import Qed.Render
import Qed.Diff
import Qed.Dom
import Qed.View.Core

namespace Qed

structure Handlers (msg : Type) where
  click      : IO.Ref (Array msg)
  input      : IO.Ref (Array (String → msg))
  mountLocal : String → String → Option String → String → (String → Option msg) → Dom.Node → IO Unit

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
  bindSignal       : Dom.Node → String → m Unit
  bindSignalAttr   : Dom.Node → String → String → m Unit
  setSignal        : String → String → m Unit
  onEvent          : Dom.Node → String → msg → m Unit
  onValueEvent     : Dom.Node → String → (String → msg) → m Unit
  mountLocalCell   : Dom.Node → String → String → Option String → String → (String → Option msg) → m Unit

def registerHandler {α : Type} (tbl : IO.Ref (Array α)) (node : Dom.Node)
    (key : String) (v : α) : IO Unit := do
  let ts ← tbl.get
  -- Capture `ts.size` before `push`: the JS runtime mutates pushed arrays in place.
  let next := toString ts.size
  match (← Dom.getAttribute node key).toNat? with
  | some i => if i < ts.size then tbl.set (ts.set! i v)
              else do tbl.set (ts.push v); Dom.setAttribute node key next
  | none   => do tbl.set (ts.push v); Dom.setAttribute node key next

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
  bindSignal n name          := Dom.bindSignal n name
  bindSignalAttr n name attr := Dom.bindSignalAttr n name attr
  setSignal name val         := Dom.effect "signal.set" name val ""
  onEvent n event m          := fun h => do
    Dom.effect "event.listen" event "" ""
    registerHandler h.click n s!"data-qed-on-{event}" m
  onValueEvent n event f     := fun h => do
    Dom.effect "event.listen" event "" ""
    registerHandler h.input n s!"data-qed-onv-{event}" f
  mountLocalCell n key comp init props bubble := fun h => do
    Dom.setAttribute n "data-qed-local" (localKey comp key)
    h.mountLocal key comp init props bubble n

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
       | .stat _          => pure ())
      applyDynAttrListM node s vas

def applyDynAttrsM [MonadDom msg m] (node : Dom.Node) (attrs : List (VAttr σ msg)) (s : σ) : m Unit := do
  if attrs.any (fun | .bind _ => true | _ => false) then
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

@[inline] def applyToDom (h : Handlers msg) (parent : Dom.Node) (index : UInt32) (node : Dom.Node)
    (patch : Patch msg) : IO Unit :=
  ReaderT.run (applyToDomM (m := DomM msg) parent index node patch) h

end Qed
