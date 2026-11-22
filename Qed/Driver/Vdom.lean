import Qed.Render
import Qed.Diff
import Qed.Dom
import Qed.View.Core

namespace Qed

structure Handlers (msg : Type) where
  click      : IO.Ref (Array msg)
  input      : IO.Ref (Array (String → msg))
  rowEv      : IO.Ref (Array (Nat → Nat → Option msg))
  mountLocal : String → String → Option String → String → (String → Option msg) → Dom.Node → IO Unit

def rowEvBase : UInt32 := 0x80000000

def dispatchStrWithRows {msg : Type} (inputRef : IO.Ref (Array (String → msg)))
    (rowEvRef : IO.Ref (Array (Nat → Nat → Option msg)))
    (dispatchMsg : msg → IO Unit) (id : UInt32) (s : String) : IO Unit := do
  if id >= rowEvBase then
    let slot := (id - rowEvBase).toNat
    if let some fn := (← rowEvRef.get)[slot]? then
      match s.splitOn ":" with
      | [evStr, rowStr] =>
          if let (some evIdx, some rowIdx) := (evStr.toNat?, rowStr.toNat?) then
            if let some m := fn rowIdx evIdx then
              dispatchMsg m
      | _ => pure ()
  else
    match (← inputRef.get)[id.toNat]? with
    | some f => dispatchMsg (f s)
    | none   => pure ()

class MonadDom (msg : outParam Type) (m : Type → Type) extends Monad m where
  createElement    : String → String → m Dom.Node
  createText       : String → m Dom.Node
  createFragment   : m Dom.Node
  childNamespace   : Dom.Node → m String
  setAttribute     : Dom.Node → String → String → m Unit
  removeAttribute  : Dom.Node → String → m Unit
  retainAttributes : Dom.Node → List String → m Unit
  clearHandlers    : Dom.Node → m Unit
  setValue         : Dom.Node → String → m Unit
  setChecked       : Dom.Node → Bool → m Unit
  setText          : Dom.Node → String → m Unit
  appendChild      : Dom.Node → Dom.Node → m Unit
  childAt          : Dom.Node → UInt32 → m Dom.Node
  childCount       : Dom.Node → m UInt32
  removeChild      : Dom.Node → UInt32 → m Unit
  replaceChild     : Dom.Node → UInt32 → Dom.Node → m Unit
  insertBeforeNode : Dom.Node → UInt32 → Dom.Node → m Unit
  insertBeforeRef  : Dom.Node → Option Dom.Node → Dom.Node → m Unit
  removeNode       : Dom.Node → Dom.Node → m Unit
  clearChildren    : Dom.Node → m Unit
  bindSignal       : Dom.Node → String → m Unit
  bindSignalAttr   : Dom.Node → String → String → m Unit
  setSignal        : String → String → m Unit
  bindSignalOn     : Dom.Node → String → String → msg → m Unit
  setSignalOn      : String → msg → m Unit
  onEvent          : Dom.Node → String → msg → m Unit
  onValueEvent     : Dom.Node → String → (String → msg) → m Unit
  mountLocalCell   : Dom.Node → String → String → Option String → String → (String → Option msg) → m Unit
  compileRowTmpl   : String → Html msg → Array (Array UInt32) → Array String →
      Array (Array UInt32) → Array String → m UInt32
  allocRowEvSlot   : Dom.Node → (Nat → Nat → Option msg) → m UInt32
  setRowEvSlot     : UInt32 → (Nat → Nat → Option msg) → m Unit
  mountTmplRow     : UInt32 → Array String → m Dom.Node
  mountTmplRows    : Dom.Node → UInt32 → Array (Array String) → m (Array Dom.Node)
  patchTmplRow     : Dom.Node → UInt32 → Array String → Array String → m Unit
  hydrateTmplRow   : Dom.Node → UInt32 → m Unit

private def buildStaticProtoDom {msg : Type} (ns : String) : Html msg → IO Dom.Node
  | .text s => Dom.createText s
  | .element tag attrs children => do
      let node ← Dom.createElement ns tag
      for a in normalizeAttrs attrs do
        match a with
        | .cls c                  => Dom.setAttribute node "class" c
        | .attr "value" v         => Dom.setValue node v
        | .attr k v               => Dom.setAttribute node k v
        | .flag "checked" present => Dom.setChecked node present
        | .flag k present         => if present then Dom.setAttribute node k k else Dom.removeAttribute node k
        | _                       => pure ()
      let childNs := Dom.childNsOf ns tag
      for c in children do
        Dom.appendChild node (← buildStaticProtoDom childNs c)
      return node

private def listenEvNames (evNames : Array String) (i : Nat) : IO Unit := do
  if hi : i < evNames.size then
    Dom.effect "event.listen" evNames[i] "" ""
    listenEvNames evNames (i + 1)
termination_by evNames.size - i

def registerHandler {α : Type} (tbl : IO.Ref (Array α)) (node : Dom.Node)
    (key : String) (v : α) : IO Unit := do
  let ts ← tbl.get
  -- Capture `ts.size` before `push`: the JS runtime mutates pushed arrays in place.
  let next := toString ts.size
  match (← Dom.getAttribute node key).toNat? with
  | some i => if i < ts.size then tbl.set (ts.set! i v)
              else do tbl.set (ts.push v); Dom.setAttribute node key next
  | none   => do tbl.set (ts.push v); Dom.setAttribute node key next

private def allocSigSlot (h : Handlers msg) (name : String) (m : msg) : IO Nat := do
  let ts ← h.click.get
  let i := ts.size
  h.click.set (ts.push m)
  Dom.setSigSlot name (UInt32.ofNat (i + 1))
  pure i

abbrev DomM (msg : Type) := ReaderT (Handlers msg) IO

instance : MonadDom msg (DomM msg) where
  createElement ns tag       := Dom.createElement ns tag
  createText s               := Dom.createText s
  createFragment             := Dom.createFragment
  childNamespace n           := Dom.childNamespace n
  setAttribute n k v         := Dom.setAttribute n k v
  removeAttribute n k        := Dom.removeAttribute n k
  retainAttributes n names   := Dom.retainAttributes n names
  clearHandlers n            := Dom.clearHandlers n
  setValue n v               := Dom.setValue n v
  setChecked n on            := Dom.setChecked n on
  setText n s                := Dom.setText n s
  appendChild p c            := Dom.appendChild p c
  childAt p i                := Dom.childAt p i
  childCount p               := Dom.childCount p
  removeChild p i            := Dom.removeChild p i
  replaceChild p i c         := Dom.replaceChild p i c
  insertBeforeNode p i c     := Dom.insertBefore p i c
  insertBeforeRef p r c      := Dom.insertBeforeRef p (r.getD 0) c
  removeNode p c             := Dom.removeNode p c
  clearChildren p            := Dom.clearChildren p
  bindSignal n name          := Dom.bindSignal n name
  bindSignalAttr n name attr := Dom.bindSignalAttr n name attr
  setSignal name val         := Dom.effect "signal.set" name val ""
  bindSignalOn n name event m := fun h => do
    Dom.effect "event.listen" event "" ""
    let slot ← Dom.getSigSlot name
    let idx ← if slot > 0 then pure (slot.toNat - 1) else allocSigSlot h name m
    Dom.setAttribute n s!"data-qed-on-{event}" (toString idx)
  setSignalOn name m := fun h => do
    let slot ← Dom.getSigSlot name
    if slot > 0 then
      let i := slot.toNat - 1
      let ts ← h.click.get
      if i < ts.size then h.click.set (ts.set! i m)
    else
      discard <| allocSigSlot h name m
  onEvent n event m          := fun h => do
    Dom.effect "event.listen" event "" ""
    registerHandler h.click n s!"data-qed-on-{event}" m
  onValueEvent n event f     := fun h => do
    Dom.effect "event.listen" event "" ""
    registerHandler h.input n s!"data-qed-onv-{event}" f
  mountLocalCell n key comp init props bubble := fun h => do
    Dom.setAttribute n "data-qed-local" (localKey comp key)
    h.mountLocal key comp init props bubble n
  compileRowTmpl ns proto slotPaths slotAttrs evPaths evNames := fun _ => do
    listenEvNames evNames 0
    let pNode ← buildStaticProtoDom ns proto
    Dom.compileRowTmpl pNode slotPaths slotAttrs evPaths evNames
  allocRowEvSlot node fn := fun h => do
    let ts ← h.rowEv.get
    let slot := ts.size
    h.rowEv.set (ts.push fn)
    Dom.setAttribute node "data-qed-list" (toString (rowEvBase.toNat + slot))
    return UInt32.ofNat slot
  setRowEvSlot slot fn := fun h => do
    let ts ← h.rowEv.get
    let i := slot.toNat
    if i < ts.size then h.rowEv.set (ts.set! i fn)
  mountTmplRow tmplId vals := Dom.mountTmplRow tmplId vals
  mountTmplRows parent tmplId valsPerRow := Dom.mountTmplRows parent tmplId valsPerRow
  patchTmplRow node tmplId newVals oldVals := Dom.patchTmplRow node tmplId newVals oldVals
  hydrateTmplRow node tmplId := Dom.hydrateTmplRow node tmplId

def applyAttrM [MonadDom msg m] (node : Dom.Node) : Attr msg → m Unit
  | .cls c                  => MonadDom.setAttribute node "class" c
  | .attr "value" v         => MonadDom.setValue node v
  | .attr k v               => MonadDom.setAttribute node k v
  | .flag "checked" present => MonadDom.setChecked node present
  | .flag k present         => if present then MonadDom.setAttribute node k k else MonadDom.removeAttribute node k
  | .key _                  => pure ()
  | .on event evMsg         => MonadDom.onEvent node event evMsg
  | .onValue event f        => MonadDom.onValueEvent node event f
  | .localCell key comp init props bubble =>
      MonadDom.mountLocalCell node key comp init props bubble
  | .signalBind name        => MonadDom.bindSignal node name
  | .signalAttr name attr _ => MonadDom.bindSignalAttr node name attr
  | .signalOn name event m  => MonadDom.bindSignalOn node name event m

def applyAttrListM [MonadDom msg m] (node : Dom.Node) : List (Attr msg) → m Unit
  | []      => pure ()
  | a :: as => do applyAttrM node a; applyAttrListM node as

def managedAttrName : Attr msg → Option String
  | .cls _             => some "class"
  | .attr k _          => some k
  | .flag k _          => some k
  | .on e _            => some s!"data-qed-on-{e}"
  | .onValue e _       => some s!"data-qed-onv-{e}"
  | .localCell ..      => some "data-qed-local"
  | .signalAttr _ a _  => some a
  | .signalOn _ e _    => some s!"data-qed-on-{e}"
  | .signalBind _      => some "data-qed-signal"
  | .key _             => none

def applyAttrsM [MonadDom msg m] (node : Dom.Node) (attrs : List (Attr msg)) : m Unit := do
  let norm := normalizeAttrs attrs
  MonadDom.retainAttributes node (norm.filterMap managedAttrName)
  applyAttrListM node norm

def applyDynAttrListM [MonadDom msg m] (node : Dom.Node) (s : σ) : List (VAttr σ msg) → m Unit
  | []        => pure ()
  | va :: vas => do
      (match va with
       | .bind f          => applyAttrM node (f s)
       | .dynVal attr get => applyAttrM node (.attr attr (get s))
       | .dynOn ev get    => applyAttrM node (.on ev (get s))
       | .stat _          => pure ())
      applyDynAttrListM node s vas

def applyDynAttrsM [MonadDom msg m] (node : Dom.Node) (attrs : List (VAttr σ msg)) (s : σ) : m Unit := do
  if attrs.any (fun | .bind _ | .dynOn _ _ => true | _ => false) then
    applyAttrsM node (attrs.map (VAttr.eval s))
  else
    applyDynAttrListM node s attrs

def ownsChildren (attrs : List (Attr msg)) : Bool :=
  attrs.any (fun | .localCell .. => true | .signalBind .. => true | _ => false)

def allCreates : List (KeyedStep msg) → Bool
  | []                => true
  | .create _ :: rest => allCreates rest
  | .reuse _ _ :: _   => false

def positional : Nat → List (KeyedStep msg) → Bool
  | _, []                        => true
  | i, .reuse oldIndex _ :: rest => oldIndex == i && positional (i + 1) rest
  | _, .create _ :: rest         => allCreates rest

mutual
def buildDomM [MonadDom msg m] (ns : String) : Html msg → m Dom.Node
  | .text s => MonadDom.createText s
  | .element tag attrs children => do
      let node ← MonadDom.createElement ns tag
      applyAttrsM node attrs
      if !ownsChildren attrs then
        buildDomListM (Dom.childNsOf ns tag) node children
      return node

def buildDomListM [MonadDom msg m] (ns : String) (parent : Dom.Node) : List (Html msg) → m Unit
  | []      => pure ()
  | c :: cs => do
      let cn ← buildDomM ns c
      MonadDom.appendChild parent cn
      buildDomListM ns parent cs
end

def hydrateTextSlotM [MonadDom msg m] (parent : Dom.Node) (index : UInt32) (inTextRun : Bool)
    (s : String) (moreInRun : Unit → Bool) : m (Dom.Node × Bool) := do
  if s == "" then
    let ph ← MonadDom.createText ""
    MonadDom.insertBeforeNode parent index ph
    return (ph, inTextRun)
  else if inTextRun then
    let tn ← MonadDom.createText s
    MonadDom.insertBeforeNode parent index tn
    return (tn, true)
  else
    let tn ← MonadDom.childAt parent index
    if moreInRun () then MonadDom.setText tn s
    return (tn, true)

mutual
def hydrateDomM [MonadDom msg m] : Html msg → Dom.Node → m Unit
  | .text _, _ => pure ()
  | .element _ attrs children, node => do
      MonadDom.clearHandlers node
      applyAttrsM node attrs
      if !ownsChildren attrs then
        hydrateDomKidsM node 0 false children

def hydrateDomKidsM [MonadDom msg m] (node : Dom.Node) (i : UInt32) (inTextRun : Bool) :
    List (Html msg) → m Unit
  | [] => pure ()
  | c :: rest => do
      match c.textOf? with
      | some s =>
          let (_, nextRun) ← hydrateTextSlotM node i inTextRun s (fun () => hasMoreText rest)
          hydrateDomKidsM node (i + 1) nextRun rest
      | none =>
          let child ← MonadDom.childAt node i
          hydrateDomM c child
          hydrateDomKidsM node (i + 1) false rest
end

def removeTailM [MonadDom msg m] (node : Dom.Node) (atIdx : UInt32) : Nat → m Unit
  | 0     => pure ()
  | k + 1 => do
      MonadDom.removeChild node atIdx
      removeTailM node atIdx k

def snapshotChildrenM [MonadDom msg m] (node : Dom.Node) (i : Nat) (acc : Array Dom.Node) :
    Nat → m (Array Dom.Node)
  | 0       => return acc
  | rem + 1 => do
      let child ← MonadDom.childAt node (UInt32.ofNat i)
      snapshotChildrenM node (i + 1) (acc.push child) rem

mutual
def applyToDomM [MonadDom msg m]
    (parent : Dom.Node) (index : UInt32) (node : Dom.Node) : Patch msg → m Unit
  | .replace new => do
      let ns ← MonadDom.childNamespace parent
      let n2 ← buildDomM ns new
      MonadDom.replaceChild parent index n2
  | .setText s => MonadDom.setText node s
  | .patchElement attrs steps => do
      applyAttrsM node attrs
      if ownsChildren attrs then
        pure ()
      else
        let oldCount ← MonadDom.childCount node
        if positional 0 steps then
          applyPositionalStepsM node 0 steps
          let count ← MonadDom.childCount node
          removeTailM node (UInt32.ofNat steps.length) (count.toNat - steps.length)
        else
          let live ← snapshotChildrenM node 0 #[] oldCount.toNat
          let finalJ ← applyKeyedStepsM node live 0 steps
          let count ← MonadDom.childCount node
          removeTailM node finalJ (count.toNat - finalJ.toNat)

def applyPositionalStepsM [MonadDom msg m] (node : Dom.Node) (j : UInt32) :
    List (KeyedStep msg) → m Unit
  | [] => pure ()
  | .reuse _ p :: rest => do
      let child ← MonadDom.childAt node j
      applyToDomM node j child p
      applyPositionalStepsM node (j + 1) rest
  | .create newH :: rest => do
      let ns ← MonadDom.childNamespace node
      let cn ← buildDomM ns newH
      MonadDom.insertBeforeNode node j cn
      applyPositionalStepsM node (j + 1) rest

def applyKeyedStepsM [MonadDom msg m] (node : Dom.Node) (live : Array Dom.Node) (j : UInt32) :
    List (KeyedStep msg) → m UInt32
  | [] => return j
  | .reuse oldIndex p :: rest => do
      let child := live.getD oldIndex 0
      MonadDom.insertBeforeNode node j child
      applyToDomM node j child p
      applyKeyedStepsM node live (j + 1) rest
  | .create newH :: rest => do
      let ns ← MonadDom.childNamespace node
      let cn ← buildDomM ns newH
      MonadDom.insertBeforeNode node j cn
      applyKeyedStepsM node live (j + 1) rest
end

def patchHtmlSubtreeM [MonadDom msg m] (parent : Dom.Node) (index : UInt32) (node : Dom.Node)
    (oldHtml newHtml : Html msg) : m Dom.Node :=
  match diff oldHtml newHtml with
  | .replace h2 => do
      let n2 ← buildDomM (← MonadDom.childNamespace parent) h2
      MonadDom.replaceChild parent index n2
      return n2
  | p => do
      applyToDomM parent index node p
      return node

@[inline] def buildDom (h : Handlers msg) (ns : String) (tree : Html msg) : IO Dom.Node :=
  ReaderT.run (buildDomM (m := DomM msg) ns tree) h

@[inline] def hydrateDom (h : Handlers msg) (tree : Html msg) (node : Dom.Node) : IO Unit :=
  ReaderT.run (hydrateDomM (m := DomM msg) tree node) h

end Qed
