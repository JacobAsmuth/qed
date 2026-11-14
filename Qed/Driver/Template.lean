import Qed.Driver.Vdom
import Std.Data.HashMap

namespace Qed

inductive VState (σ : Type) (msg : Type) where
  | text (node : Dom.Node)
  | dyn (node : Dom.Node) (last : String)
  | elem (node : Dom.Node) (kids : List (VState σ msg))
  | cond (wasYes : Bool) (inner : VState σ msg)
  | list (node : Dom.Node) (keys : Array String)
      (sigs : Array (Array (String × String))) (rows : List (Html msg))
      (marks : Array USize) (inst : String)
  | stat (node : Dom.Node)
  | dynNode (node : Dom.Node) (last : Html msg)
  | memo (node : Dom.Node) (lastKey : String) (lastHtml : Html msg)

instance : Inhabited (VState σ msg) := ⟨.text 0⟩

def keyPos (keys : Array String) : Std.HashMap String Nat :=
  (keys.foldl (init := ((∅ : Std.HashMap String Nat), 0)) fun (m, i) k =>
    (m.insert k i, i + 1)).1

structure AlignedRows (msg : Type) where
  rows  : Array (Html msg) := #[]
  marks : Array USize := #[]
  sigs  : Array (Array (String × String)) := #[]

def alignRows (keys : Array String) (oldPos : Std.HashMap String Nat)
    (oldRows : Array (Html msg)) (oldMarks : Array USize)
    (oldSigs : Array (Array (String × String)))
    (fresh : Unit → Array (Html msg)) : AlignedRows msg := Id.run do
  let mut aligned : AlignedRows msg := {}
  let mut freshRows : Option (Array (Html msg)) := none
  for key in keys do
    let (row, mark, sig) ← match oldPos[key]? with
      | some i => pure (oldRows.getD i default, oldMarks.getD i 0, oldSigs.getD i #[])
      | none => do
          let rows := match freshRows with | some rows => rows | none => fresh ()
          freshRows := some rows
          pure (rows.getD aligned.rows.size default, 0, #[])
    aligned := { rows := aligned.rows.push row, marks := aligned.marks.push mark,
                 sigs := aligned.sigs.push sig }
  return aligned

def collectChanged (inst : String) (old new : Array (String × String)) (j : Nat)
    (acc : Array (String × String)) : Array (String × String) :=
  if h : j < new.size then
    let (nm, v) := new[j]
    let acc := if old[j]?.map (·.2) == some v then acc else acc.push (inst ++ nm, v)
    collectChanged inst old new (j + 1) acc
  else acc
termination_by new.size - j

-- Pure tail recursion so the JS backend trampolines it instead of overflowing the stack on 10k-row `IO` binds.
def diffRowSigs (rowSig : Nat → Array (String × String)) (inst : String)
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String)))
    (i : Nat) (accSigs : Array (Array (String × String))) (accEmit : Array (String × String)) :
    Array (Array (String × String)) × Array (String × String) :=
  if h : i < newMarks.size then
    let m := newMarks[i]
    if m != 0 && oldMarks[i]? == some m then
      diffRowSigs rowSig inst newMarks oldMarks oldSigs (i + 1) (accSigs.push (oldSigs[i]?.getD #[])) accEmit
    else
      let rsig := rowSig i
      let accEmit := collectChanged inst (oldSigs[i]?.getD #[]) rsig 0 accEmit
      diffRowSigs rowSig inst newMarks oldMarks oldSigs (i + 1) (accSigs.push rsig) accEmit
  else (accSigs, accEmit)
termination_by newMarks.size - i

def emitSignalsM [MonadDom msg m] : List (String × String) → m Unit
  | []            => pure ()
  | (nm, v) :: rest => do
      MonadDom.setSignal nm v
      emitSignalsM rest

def seedRowsM [MonadDom msg m] (inst : String) (rowSig : Nat → Array (String × String))
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String))) :
    m (Array (Array (String × String))) := do
  let (newSigs, toEmit) := diffRowSigs rowSig inst newMarks oldMarks oldSigs 0 #[] #[]
  emitSignalsM toEmit.toList
  return newSigs

mutual
def buildViewM [MonadDom msg m] (ns : String) :
    View σ msg → σ → m (Dom.Node × VState σ msg)
  | .text s, _ => do
      let n ← MonadDom.createText s
      return (n, .text n)
  | .dyn get, s => do
      let v := get s
      let n ← MonadDom.createText v
      return (n, .dyn n v)
  | .static html, _ => do
      let n ← buildDomM ns html
      return (n, .stat n)
  | .element tag attrs kids, s => do
      let node ← MonadDom.createElement ns tag
      applyAttrsM node (attrs.map (VAttr.eval s))
      let ks ← buildViewKidsM (Dom.childNsOf ns tag) node kids s
      return (node, .elem node ks)
  | .ifElse cond yes no, s => do
      let b := cond s
      let (n, inner) ← if b then buildViewM ns yes s else buildViewM ns no s
      return (n, .cond b inner)
  | .dynNode get, s => do
      let html := get s
      let n ← buildDomM ns html
      return (n, .dynNode n html)
  | .memo sm, s => do
      let k := sm.keyOf s
      let html := sm.eval s
      let n ← buildDomM ns html
      return (n, .memo n k html)
  | .keyedList tag attrs keys marks rowSig rowsHtml, s => do
      let uKeys := disambiguateKeys (keys s)
      let node ← MonadDom.createElement ns tag
      applyAttrsM node (attrs.map (VAttr.eval s))
      let inst := s!"§{node}§"
      let nMarks := marks s
      let perRow ← seedRowsM inst (rowSig s) nMarks #[] #[]
      let rs := (rowsHtml s).map (Html.prefixSignals inst)
      buildDomListM (Dom.childNsOf ns tag) node rs
      return (node, .list node uKeys perRow rs nMarks inst)

def buildViewKidsM [MonadDom msg m] (ns : String) (parent : Dom.Node) :
    List (View σ msg) → σ → m (List (VState σ msg))
  | [], _ => return []
  | k :: rest, s => do
      let (kn, kst) ← buildViewM ns k s
      MonadDom.appendChild parent kn
      let restSt ← buildViewKidsM ns parent rest s
      return kst :: restSt
end

mutual
def patchViewM [MonadDom msg m]
    (parent : Dom.Node) (index : UInt32) :
    View σ msg → σ → VState σ msg → m (VState σ msg)
  | .dyn get, s, .dyn node last => do
      let v := get s
      if v != last then MonadDom.setText node v
      return .dyn node v
  | .element _ attrs kids, s, .elem node kstates => do
      applyDynAttrsM node attrs s
      let ks' ← patchViewKidsM node 0 kids s kstates
      return .elem node ks'
  | .ifElse cond yes no, s, .cond wasYes inner => do
      let now := cond s
      if now == wasYes then
        let inner' ← if now then patchViewM parent index yes s inner
                     else patchViewM parent index no s inner
        return .cond now inner'
      else
        let ns ← MonadDom.childNamespace parent
        let (n, st) ← if now then buildViewM ns yes s else buildViewM ns no s
        MonadDom.replaceChild parent index n
        return .cond now st
  | .dynNode get, s, .dynNode node last => do
      let newHtml := get s
      let n' ← patchHtmlSubtreeM parent index node last newHtml
      return .dynNode n' newHtml
  | .memo sm, s, .memo node lastKey lastHtml => do
      let k := sm.keyOf s
      if k == lastKey then
        return .memo node lastKey lastHtml
      else
        let newHtml := sm.eval s
        let n' ← patchHtmlSubtreeM parent index node lastHtml newHtml
        return .memo n' k newHtml
  | .keyedList tag attrs keys marks rowSig rowsHtml, s,
    .list node oldKeys oldSigs oldRowsL oldMarks inst => do
      let newKeys  := disambiguateKeys (keys s)
      let newMarks := marks s
      if newKeys == oldKeys then
        applyDynAttrsM node attrs s
        let newSigs ← seedRowsM inst (rowSig s) newMarks oldMarks oldSigs
        return .list node oldKeys newSigs oldRowsL newMarks inst
      else
        let oldPos  := keyPos oldKeys
        let oldRows := oldRowsL.toArray
        let aligned := alignRows newKeys oldPos oldRows oldMarks oldSigs
          (fun _ => ((rowsHtml s).map (Html.prefixSignals inst)).toArray)
        let newRows := aligned.rows.toList
        let newSigs ← seedRowsM inst (rowSig s) newMarks aligned.marks aligned.sigs
        if oldRowsL.isEmpty then
          applyDynAttrsM node attrs s
          let childNs ← MonadDom.childNamespace node
          let frag ← MonadDom.createFragment
          buildDomListM childNs frag newRows
          MonadDom.appendChild node frag
        else
          let evAttrs := attrs.map (VAttr.eval s)
          applyToDomM parent index node (diff (.element tag evAttrs oldRowsL) (.element tag evAttrs newRows))
        return .list node newKeys newSigs newRows newMarks inst
  | .text _,   _, st@(.text _) => return st
  | .static _, _, st@(.stat _) => return st
  | v, s, _ => do
      let (n, st) ← buildViewM (← MonadDom.childNamespace parent) v s
      MonadDom.replaceChild parent index n
      return st

def patchViewKidsM [MonadDom msg m] (node : Dom.Node) (i : UInt32) :
    List (View σ msg) → σ → List (VState σ msg) → m (List (VState σ msg))
  | [], _, _ => return []
  | k :: rest, s, kst :: restSt => do
      let kst' ← patchViewM node i k s kst
      let restSt' ← patchViewKidsM node (i + 1) rest s restSt
      return kst' :: restSt'
  | k :: rest, s, [] => do
      let kst' ← patchViewM node i k s default
      let restSt' ← patchViewKidsM node (i + 1) rest s []
      return kst' :: restSt'
end

def View.textOf? (s : σ) : View σ msg → Option String
  | .text str                   => some str
  | .dyn get                    => some (get s)
  | .ifElse cond yes no         => if cond s then View.textOf? s yes else View.textOf? s no
  | .static html                => html.textOf?
  | .dynNode get                => (get s).textOf?
  | .memo sm                    => (sm.eval s).textOf?
  | .element .. | .keyedList .. => none

def hasMoreViewText (s : σ) : List (View σ msg) → Bool
  | []      => false
  | k :: cs =>
      match k.textOf? s with
      | some "" => hasMoreViewText s cs
      | some _  => true
      | none    => false

def hydrateListRowsM [MonadDom msg m] (node : Dom.Node) (i : UInt32) : List (Html msg) → m Unit
  | []      => pure ()
  | r :: rs => do
      let child ← MonadDom.childAt node i
      hydrateDomM r child
      hydrateListRowsM node (i + 1) rs

mutual
def hydrateViewM [MonadDom msg m] :
    View σ msg → σ → Dom.Node → m (VState σ msg)
  | .text _,      _, node => return .text node
  | .dyn get,     s, node => return .dyn node (get s)
  | .static html, _, node => do hydrateDomM html node; return .stat node
  | .element _ attrs kids, s, node => do
      MonadDom.clearHandlers node
      applyAttrsM node (attrs.map (VAttr.eval s))
      let ks ← hydrateViewKidsM node s 0 false kids
      return .elem node ks
  | .ifElse cond yes no, s, node => do
      let b := cond s
      let cst ← if b then hydrateViewM yes s node else hydrateViewM no s node
      return .cond b cst
  | .dynNode get, s, node => do
      let html := get s
      hydrateDomM html node
      return .dynNode node html
  | .memo sm, s, node => do
      let k := sm.keyOf s
      let html := sm.eval s
      hydrateDomM html node
      return .memo node k html
  | .keyedList _ attrs keys marks rowSig rowsHtml, s, node => do
      let uKeys := disambiguateKeys (keys s)
      MonadDom.clearHandlers node
      applyAttrsM node (attrs.map (VAttr.eval s))
      let inst := s!"§{node}§"
      let nMarks := marks s
      let perRow ← seedRowsM inst (rowSig s) nMarks #[] #[]
      let rs := (rowsHtml s).map (Html.prefixSignals inst)
      hydrateListRowsM node 0 rs
      return .list node uKeys perRow rs nMarks inst

def hydrateViewKidsM [MonadDom msg m] (node : Dom.Node)
    (s : σ) (i : UInt32) (inTextRun : Bool) :
    List (View σ msg) → m (List (VState σ msg))
  | [] => return []
  | k :: rest => do
      let (kn, nextRun) ← match k.textOf? s with
        | some str => hydrateTextSlotM node i inTextRun str (fun () => hasMoreViewText s rest)
        | none     => do let cn ← MonadDom.childAt node i; pure (cn, false)
      let kst ← hydrateViewM k s kn
      let restSt ← hydrateViewKidsM node s (i + 1) nextRun rest
      return kst :: restSt
end

@[inline] def buildView (h : Handlers msg) (ns : String) (v : View σ msg) (s : σ) :
    IO (Dom.Node × VState σ msg) :=
  ReaderT.run (buildViewM (m := DomM msg) ns v s) h

@[inline] def patchView (h : Handlers msg) (parent : Dom.Node) (index : UInt32)
    (v : View σ msg) (s : σ) (st : VState σ msg) : IO (VState σ msg) :=
  ReaderT.run (patchViewM (m := DomM msg) parent index v s st) h

@[inline] def hydrateView (h : Handlers msg) (v : View σ msg) (s : σ) (node : Dom.Node) :
    IO (VState σ msg) :=
  ReaderT.run (hydrateViewM (m := DomM msg) v s node) h

end Qed
