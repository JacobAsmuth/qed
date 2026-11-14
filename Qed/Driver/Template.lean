import Qed.Driver.Vdom
import Std.Data.HashMap

namespace Qed

inductive VState (σ : Type) (msg : Type) where
  | text (node : Dom.Node)
  | dyn (node : Dom.Node) (last : IO.Ref String)
  | elem (node : Dom.Node) (kids : Array (VState σ msg))
  | cond (cell : Nat)
  | list (node : Dom.Node) (keys : IO.Ref (Array String))
      (sigs : IO.Ref (Array (Array (String × String)))) (rows : IO.Ref (List (Html msg)))
      (marks : IO.Ref (Array USize)) (inst : String)
  | stat (node : Dom.Node)
  | dynNode (nref : IO.Ref Dom.Node) (last : IO.Ref (Html msg))

instance : Inhabited (VState σ msg) := ⟨.text 0⟩

-- External arena: `VState` cannot hold a recursive `IO.Ref (... VState ...)`.
abbrev CondCells (σ msg : Type) := IO.Ref (Array (Bool × Option (VState σ msg)) × Array Nat)

def allocCell (cells : CondCells σ msg) : IO Nat := do
  let (cs, free) ← cells.get
  match free.back? with
  | some idx => cells.set (cs.set! idx (false, none), free.pop); return idx
  | none     => cells.set (cs.push (false, none), free); return cs.size

partial def freeCells (cells : CondCells σ msg) : VState σ msg → IO Unit
  | .cond idx => do
      match ((← cells.get).1.getD idx (false, none)).2 with
      | some ist => freeCells cells ist
      | none     => pure ()
      cells.modify (fun (cs, free) => (cs.set! idx (false, none), free.push idx))
  | .elem _ ks => ks.forM (freeCells cells)
  | _          => pure ()

def keyPos (keys : Array String) : Std.HashMap String Nat :=
  (keys.foldl (init := ((∅ : Std.HashMap String Nat), 0)) fun (m, i) k =>
    (m.insert k i, i + 1)).1

def checkRowKeys (keys : Array String) : IO Unit := do
  let mut seen : Std.HashMap String Unit := ∅
  for k in keys do
    if seen.contains k then
      throw (IO.userError s!"Qed: duplicate sibling key {k}")
    seen := seen.insert k ()

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

partial def collectChanged (inst : String) (old new : Array (String × String)) (j : Nat)
    (acc : Array (String × String)) : Array (String × String) :=
  if j ≥ new.size then acc
  else
    let (nm, v) := new[j]!
    let acc := if old[j]?.map (·.2) == some v then acc else acc.push (inst ++ nm, v)
    collectChanged inst old new (j + 1) acc

-- Pure tail recursion so the JS backend trampolines it instead of overflowing the stack on 10k-row `IO` binds.
partial def diffRowSigs (rowSig : Nat → Array (String × String)) (inst : String)
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String)))
    (i : Nat) (accSigs : Array (Array (String × String))) (accEmit : Array (String × String)) :
    Array (Array (String × String)) × Array (String × String) :=
  if i ≥ newMarks.size then (accSigs, accEmit)
  else
    let m := newMarks[i]!
    if m != 0 && oldMarks[i]? == some m then
      diffRowSigs rowSig inst newMarks oldMarks oldSigs (i + 1) (accSigs.push (oldSigs[i]?.getD #[])) accEmit
    else
      let rsig := rowSig i
      let accEmit := collectChanged inst (oldSigs[i]?.getD #[]) rsig 0 accEmit
      diffRowSigs rowSig inst newMarks oldMarks oldSigs (i + 1) (accSigs.push rsig) accEmit

def seedRows (inst : String) (rowSig : Nat → Array (String × String))
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String))) :
    IO (Array (Array (String × String))) := do
  let (newSigs, toEmit) := diffRowSigs rowSig inst newMarks oldMarks oldSigs 0 #[] #[]
  for (nm, v) in toEmit do Dom.effect "signal.set" nm v ""
  return newSigs

mutual
partial def buildView (h : Handlers msg) (cells : CondCells σ msg) (ns : String) :
    View σ msg → σ → IO (Dom.Node × VState σ msg)
  | .text s,      _ => do let n ← Dom.createText s; return (n, .text n)
  | .dyn get,     s => do
      let v := get s; let n ← Dom.createText v; let r ← IO.mkRef v
      return (n, .dyn n r)
  | .static html, _ => do let n ← buildDom h ns html; return (n, .stat n)
  | .element tag attrs kids, s => do
      let node ← Dom.createElement ns tag
      applyAttrs h node (attrs.map (VAttr.eval s))
      let childNs := Dom.childNsOf ns tag
      let mut ks : Array (VState σ msg) := #[]
      for k in kids do
        let (kn, kst) ← buildView h cells childNs k s
        Dom.appendChild node kn
        ks := ks.push kst
      return (node, .elem node ks)
  | .ifElse cond yes no, s => buildCond h cells ns cond yes no s
  | .dynNode get, s => do
      let html := get s
      let n ← buildDom h ns html
      return (n, .dynNode (← IO.mkRef n) (← IO.mkRef html))
  | .keyedList tag attrs keys marks rowSig rowsHtml, s => do
      checkRowKeys (keys s)
      let node ← Dom.createElement ns tag
      applyAttrs h node (attrs.map (VAttr.eval s))
      let inst := s!"§{node}§"
      let perRow ← seedRows inst (rowSig s) (marks s) #[] #[]
      let rs := (rowsHtml s).map (Html.prefixSignals inst)
      let childNs := Dom.childNsOf ns tag
      for r in rs do Dom.appendChild node (← buildDom h childNs r)
      return (node, .list node (← IO.mkRef (keys s)) (← IO.mkRef perRow) (← IO.mkRef rs)
        (← IO.mkRef (marks s)) inst)

partial def patchView (h : Handlers msg) (cells : CondCells σ msg)
    (parent : Dom.Node) (index : UInt32) :
    View σ msg → σ → VState σ msg → IO Unit
  | .dyn get, s, .dyn node last => do
      let v := get s
      if v != (← last.get) then Dom.setText node v; last.set v
  | .element _ attrs kids, s, .elem node kstates => do
      applyDynAttrs h node attrs s
      let mut i : UInt32 := 0
      for k in kids do
        patchView h cells node i k s (kstates.getD i.toNat default)
        i := i + 1
  | .ifElse cond yes no, s, .cond idx => patchCond h cells parent index cond yes no s idx
  | .dynNode get, s, .dynNode nref last => do
      let newHtml := get s
      let node ← nref.get
      match diff (← last.get) newHtml with
      | .replace h2 => do
          let n2 ← buildDom h (← Dom.childNamespace parent) h2
          Dom.replaceChild parent index n2
          nref.set n2
      | p => applyToDom h parent index node p
      last.set newHtml
  | .keyedList tag attrs keys marks rowSig rowsHtml, s, .list node lastKeys lastSigs lastRows lastMarks inst => do
      let newKeys  := keys s
      let oldKeys  ← lastKeys.get
      let newMarks := marks s
      if newKeys == oldKeys then
        applyDynAttrs h node attrs s
        let newSigs ← seedRows inst (rowSig s) newMarks (← lastMarks.get) (← lastSigs.get)
        lastSigs.set newSigs; lastMarks.set newMarks
      else
        checkRowKeys newKeys
        let oldPos   := keyPos oldKeys
        let oldRowsL ← lastRows.get
        let oldRows  := oldRowsL.toArray
        let oldMarks ← lastMarks.get
        let oldSigs  ← lastSigs.get
        let aligned := alignRows newKeys oldPos oldRows oldMarks oldSigs
          (fun _ => ((rowsHtml s).map (Html.prefixSignals inst)).toArray)
        let newRows := aligned.rows.toList
        let newSigs ← seedRows inst (rowSig s) newMarks aligned.marks aligned.sigs
        if oldRowsL.isEmpty then
          applyDynAttrs h node attrs s
          let childNs ← Dom.childNamespace node
          let frag ← Dom.createFragment
          for r in newRows do Dom.appendChild frag (← buildDom h childNs r)
          Dom.appendChild node frag
        else
          let evAttrs := attrs.map (VAttr.eval s)
          applyToDom h parent index node (diff (.element tag evAttrs oldRowsL) (.element tag evAttrs newRows))
        lastKeys.set newKeys; lastMarks.set newMarks; lastSigs.set newSigs; lastRows.set newRows
  | .text _,   _, _ => pure ()
  | .static _, _, _ => pure ()
  | v, s, _ => do
      let (n, _) ← buildView h cells (← Dom.childNamespace parent) v s
      Dom.replaceChild parent index n

partial def buildCond (h : Handlers msg) (cells : CondCells σ msg) (ns : String)
    (c : σ → Bool) (yes no : View σ msg) (s : σ) : IO (Dom.Node × VState σ msg) := do
  let idx ← allocCell cells
  let (n, st) ← buildView h cells ns (if c s then yes else no) s
  cells.modify (fun (cs, free) => (cs.set! idx (c s, some st), free))
  return (n, .cond idx)

partial def patchCond (h : Handlers msg) (cells : CondCells σ msg)
    (parent : Dom.Node) (index : UInt32) (c : σ → Bool) (yes no : View σ msg) (s : σ) (idx : Nat) : IO Unit := do
  let (wasYes, inner) := (← cells.get).1.getD idx (false, none)
  let now := c s
  let active := if now then yes else no
  if now == wasYes then
    match inner with | some ist => patchView h cells parent index active s ist | none => pure ()
  else do
    match inner with | some ist => freeCells cells ist | none => pure ()
    let (n, st) ← buildView h cells (← Dom.childNamespace parent) active s
    Dom.replaceChild parent index n
    cells.modify (fun (cs, free) => (cs.set! idx (now, some st), free))
end

def View.textOf? (s : σ) : View σ msg → Option String
  | .text str                 => some str
  | .dyn get                  => some (get s)
  | .ifElse cond yes no       => if cond s then View.textOf? s yes else View.textOf? s no
  | .static html              => html.textOf?
  | .dynNode get              => (get s).textOf?
  | .element .. | .keyedList .. => none

def hasMoreViewText (s : σ) : List (View σ msg) → Bool
  | []      => false
  | k :: cs =>
      match k.textOf? s with
      | some "" => hasMoreViewText s cs
      | some _  => true
      | none    => false

mutual
partial def hydrateView (h : Handlers msg) (cells : CondCells σ msg) :
    View σ msg → σ → Dom.Node → IO (VState σ msg)
  | .text _,      _, node => return .text node
  | .dyn get,     s, node => return .dyn node (← IO.mkRef (get s))
  | .static html, _, node => do hydrateDom h html node; return .stat node
  | .element _ attrs kids, s, node => do
      clearHandlerIds node
      applyAttrs h node (attrs.map (VAttr.eval s))
      let ks ← hydrateViewKids h cells node s 0 false #[] kids
      return .elem node ks
  | .ifElse cond yes no, s, node => do
      let idx ← allocCell cells
      let cst ← hydrateView h cells (if cond s then yes else no) s node
      cells.modify (fun (cs, fr) => (cs.set! idx (cond s, some cst), fr))
      return .cond idx
  | .dynNode get, s, node => do
      let html := get s
      hydrateDom h html node
      return .dynNode (← IO.mkRef node) (← IO.mkRef html)
  | .keyedList _ attrs keys marks rowSig rowsHtml, s, node => do
      checkRowKeys (keys s)
      clearHandlerIds node
      applyAttrs h node (attrs.map (VAttr.eval s))
      let inst := s!"§{node}§"
      let perRow ← seedRows inst (rowSig s) (marks s) #[] #[]
      let rs := (rowsHtml s).map (Html.prefixSignals inst)
      let mut i : UInt32 := 0
      for r in rs do
        hydrateDom h r (← Dom.childAt node i)
        i := i + 1
      return .list node (← IO.mkRef (keys s)) (← IO.mkRef perRow) (← IO.mkRef rs)
        (← IO.mkRef (marks s)) inst

partial def hydrateViewKids (h : Handlers msg) (cells : CondCells σ msg) (node : Dom.Node)
    (s : σ) (i : UInt32) (inTextRun : Bool) (acc : Array (VState σ msg)) :
    List (View σ msg) → IO (Array (VState σ msg))
  | [] => return acc
  | k :: rest => do
      let (kn, nextRun) ← match k.textOf? s with
        | some str => hydrateTextSlot node i inTextRun str (fun () => hasMoreViewText s rest)
        | none     => pure (← Dom.childAt node i, false)
      let kst ← hydrateView h cells k s kn
      hydrateViewKids h cells node s (i + 1) nextRun (acc.push kst) rest
end

end Qed
