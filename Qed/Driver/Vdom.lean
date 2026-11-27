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
  reuseSlots : Bool := true

def Handlers.mkNew {msg : Type} (mountLocal : String → String → Option String → String → (String → Option msg) → Dom.Node → IO Unit)
    (reuseSlots : Bool := true) : IO (Handlers msg) := do
  return { click := ← IO.mkRef #[], input := ← IO.mkRef #[], rowEv := ← IO.mkRef #[], mountLocal, reuseSlots }
def rowEvBase : UInt32 := 0x80000000
def dispatchStrWithRows {msg : Type} (inputRef : IO.Ref (Array (String → msg)))
    (rowEvRef : IO.Ref (Array (Nat → Nat → Option msg))) (dispatchMsg : msg → IO Unit) (id : UInt32) (s : String) : IO Unit := do
  if id >= rowEvBase then
    if let some fn := (← rowEvRef.get)[(id - rowEvBase).toNat]? then
      if let [evStr, rowStr] := s.splitOn ":" then
        if let (some evIdx, some rowIdx) := (evStr.toNat?, rowStr.toNat?) then
          if let some m := fn rowIdx evIdx then dispatchMsg m
  else if let some f := (← inputRef.get)[id.toNat]? then dispatchMsg (f s)

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
  compileRowTmpl   : String → Html msg → Array (Array UInt32) → Array String → Array (Array UInt32) → Array String → m UInt32
  allocRowEvSlot   : Dom.Node → (Nat → Nat → Option msg) → m UInt32
  setRowEvSlot     : UInt32 → (Nat → Nat → Option msg) → m Unit
  mountTmplRow     : UInt32 → Array String → m Dom.Node
  mountTmplRows    : Dom.Node → UInt32 → Array (Array String) → m (Array Dom.Node)
  patchTmplRow     : Dom.Node → UInt32 → Array String → Array String → m Unit
  hydrateTmplRow   : Dom.Node → UInt32 → m Unit

def applyAttrM [MonadDom msg m] (node : Dom.Node) : Attr msg → m Unit
  | .cls c => MonadDom.setAttribute node "class" c | .attr "value" v => MonadDom.setValue node v
  | .attr k v => MonadDom.setAttribute node k v | .flag "checked" p => MonadDom.setChecked node p
  | .flag k p => if p then MonadDom.setAttribute node k k else MonadDom.removeAttribute node k
  | .key _ => pure () | .on ev evMsg => MonadDom.onEvent node ev evMsg | .onValue ev f => MonadDom.onValueEvent node ev f
  | .localCell key comp init props bubble => MonadDom.mountLocalCell node key comp init props bubble
  | .signalBind name => MonadDom.bindSignal node name | .signalAttr name attr _ => MonadDom.bindSignalAttr node name attr
  | .signalOn name ev m => MonadDom.bindSignalOn node name ev m
def applyAttrListM [MonadDom msg m] (node : Dom.Node) : List (Attr msg) → m Unit
  | [] => pure () | a :: as => do applyAttrM node a; applyAttrListM node as
def managedAttrName : Attr msg → Option String
  | .cls _ => some "class" | .attr k _ | .flag k _ => some k
  | .on e _ | .signalOn _ e _ => some s!"data-qed-on-{e}" | .onValue e _ => some s!"data-qed-onv-{e}"
  | .localCell .. => some "data-qed-local" | .signalAttr _ a _ => some a | .signalBind _ => some "data-qed-signal" | .key _ => none
def applyAttrsM [MonadDom msg m] (node : Dom.Node) (attrs : List (Attr msg)) : m Unit := do
  let norm := normalizeAttrs attrs; MonadDom.retainAttributes node (norm.filterMap managedAttrName); applyAttrListM node norm
def applyDynAttrListM [MonadDom msg m] (node : Dom.Node) (s : σ) : List (VAttr σ msg) → m Unit
  | [] => pure ()
  | va :: vas => do
      (match va with | .bind f => applyAttrM node (f s) | .dynVal a g => applyAttrM node (.attr a (g s)) | .dynOn e g => applyAttrM node (.on e (g s)) | .stat _ => pure ())
      applyDynAttrListM node s vas
def applyDynAttrsM [MonadDom msg m] (node : Dom.Node) (attrs : List (VAttr σ msg)) (s : σ) : m Unit :=
  if attrs.any (fun | .bind _ | .dynOn _ _ => true | _ => false) then applyAttrsM node (attrs.map (VAttr.eval s)) else applyDynAttrListM node s attrs
def ownsChildren (attrs : List (Attr msg)) : Bool := attrs.any fun | .localCell .. | .signalBind .. => true | _ => false
def allCreates : List (KeyedStep msg) → Bool | [] => true | .create _ :: rest => allCreates rest | .reuse _ _ :: _ => false
def positional : Nat → List (KeyedStep msg) → Bool
  | _, [] => true | i, .reuse oldIndex _ :: rest => oldIndex == i && positional (i + 1) rest | _, .create _ :: rest => allCreates rest

mutual
def buildDomM [MonadDom msg m] (ns : String) : Html msg → m Dom.Node
  | .text s => MonadDom.createText s
  | .element tag attrs children => do
      let node ← MonadDom.createElement ns tag; applyAttrsM node attrs
      if !ownsChildren attrs then buildDomListM (Dom.childNsOf ns tag) node children
      return node
def buildDomListM [MonadDom msg m] (ns : String) (parent : Dom.Node) : List (Html msg) → m Unit
  | [] => pure () | c :: cs => do MonadDom.appendChild parent (← buildDomM ns c); buildDomListM ns parent cs
end

def registerHandler {α : Type} (tbl : IO.Ref (Array α)) (node : Dom.Node) (key : String) (v : α) (reuse : Bool := true) : IO Unit := do
  let ts ← tbl.get; let next := toString ts.size -- capture `ts.size` before `push` (JS mutates in place)
  if reuse then
    if let some i := (← Dom.getAttribute node key).toNat? then
      if i < ts.size then tbl.set (ts.set! i v); return
  tbl.set (ts.push v); Dom.setAttribute node key next

@[inline] private def listenEv (e : String) : IO Unit := Dom.effect "event.listen" e "" ""
private def allocSigSlot (h : Handlers msg) (name : String) (m : msg) : IO Nat := do
  let ts ← h.click.get; let i := ts.size; h.click.set (ts.push m); Dom.setSigSlot name (UInt32.ofNat (i + 1)); pure i

abbrev DomM (msg : Type) := ReaderT (Handlers msg) IO

@[instance_reducible] private def domMBase : MonadDom msg (DomM msg) where
  createElement a b := Dom.createElement a b
  createText a := Dom.createText a
  createFragment := Dom.createFragment
  childNamespace a := Dom.childNamespace a
  setAttribute a b c := Dom.setAttribute a b c
  removeAttribute a b := Dom.removeAttribute a b
  retainAttributes a b := Dom.retainAttributes a b
  clearHandlers a := Dom.clearHandlers a
  setValue a b := Dom.setValue a b
  setChecked a b := Dom.setChecked a b
  setText a b := Dom.setText a b
  appendChild a b := Dom.appendChild a b
  childAt a b := Dom.childAt a b
  childCount a := Dom.childCount a
  removeChild a b := Dom.removeChild a b
  replaceChild a b c := Dom.replaceChild a b c
  insertBeforeNode a b c := Dom.insertBefore a b c
  insertBeforeRef p r c := Dom.insertBeforeRef p (r.getD 0) c
  removeNode a b := Dom.removeNode a b
  clearChildren a := Dom.clearChildren a
  bindSignal a b := Dom.bindSignal a b
  bindSignalAttr a b c := Dom.bindSignalAttr a b c
  setSignal name val := Dom.effect "signal.set" name val ""
  bindSignalOn n name ev m := fun h => do
    listenEv ev; let slot ← Dom.getSigSlot name
    Dom.setAttribute n s!"data-qed-on-{ev}" (toString (← if slot > 0 then pure (slot.toNat - 1) else allocSigSlot h name m))
  setSignalOn name m := fun h => do
    let slot ← Dom.getSigSlot name
    if slot > 0 then let i := slot.toNat - 1; let ts ← h.click.get; if i < ts.size then h.click.set (ts.set! i m)
    else discard <| allocSigSlot h name m
  onEvent n ev m := fun h => do listenEv ev; registerHandler h.click n s!"data-qed-on-{ev}" m h.reuseSlots
  onValueEvent n ev f := fun h => do listenEv ev; registerHandler h.input n s!"data-qed-onv-{ev}" f h.reuseSlots
  mountLocalCell n key comp init props bubble := fun h => do
    let fk := localKey comp key
    if (← Dom.getAttribute n "data-qed-local") != fk then
      if (← Dom.childCount n) > 0 then Dom.clearChildren n
      Dom.setAttribute n "data-qed-local" fk
    h.mountLocal key comp init props bubble n
  compileRowTmpl _ _ _ _ _ _ := pure 0
  allocRowEvSlot node fn := fun h => do
    let ts ← h.rowEv.get; let slot := ts.size; h.rowEv.set (ts.push fn)
    Dom.setAttribute node "data-qed-list" (toString (rowEvBase.toNat + slot)); return UInt32.ofNat slot
  setRowEvSlot slot fn := fun h => do let ts ← h.rowEv.get; if slot.toNat < ts.size then h.rowEv.set (ts.set! slot.toNat fn)
  mountTmplRow a b := Dom.mountTmplRow a b
  mountTmplRows a b c := Dom.mountTmplRows a b c
  patchTmplRow a b c d := Dom.patchTmplRow a b c d
  hydrateTmplRow a b := Dom.hydrateTmplRow a b

instance : MonadDom msg (DomM msg) :=
  { domMBase with
    compileRowTmpl := fun ns proto slotPaths slotAttrs evPaths evNames h => do
      evNames.forM listenEv
      Dom.compileRowTmpl (← @buildDomM msg (DomM msg) domMBase ns proto h) slotPaths slotAttrs evPaths evNames }

def hydrateTextSlotM [MonadDom msg m] (parent : Dom.Node) (index : UInt32) (inTextRun : Bool)
    (s : String) (moreInRun : Unit → Bool) : m (Dom.Node × Bool) := do
  if s == "" then let ph ← MonadDom.createText ""; MonadDom.insertBeforeNode parent index ph; return (ph, inTextRun)
  else if inTextRun then let tn ← MonadDom.createText s; MonadDom.insertBeforeNode parent index tn; return (tn, true)
  else
    let tn ← MonadDom.childAt parent index
    if moreInRun () then MonadDom.setText tn s
    return (tn, true)

mutual
def hydrateDomM [MonadDom msg m] : Html msg → Dom.Node → m Unit
  | .text _, _ => pure ()
  | .element _ attrs children, node => do
      MonadDom.clearHandlers node; applyAttrsM node attrs
      if !ownsChildren attrs then hydrateDomKidsM node 0 false children
def hydrateDomKidsM [MonadDom msg m] (node : Dom.Node) (i : UInt32) (inTextRun : Bool) : List (Html msg) → m Unit
  | [] => pure ()
  | c :: rest => do
      match c.textOf? with
      | some s => let (_, nextRun) ← hydrateTextSlotM node i inTextRun s (fun () => hasMoreText rest); hydrateDomKidsM node (i + 1) nextRun rest
      | none   => hydrateDomM c (← MonadDom.childAt node i); hydrateDomKidsM node (i + 1) false rest
end

def removeTailM [MonadDom msg m] (node : Dom.Node) (atIdx : UInt32) : Nat → m Unit
  | 0 => pure () | k + 1 => do MonadDom.removeChild node atIdx; removeTailM node atIdx k
def snapshotChildrenM [MonadDom msg m] (node : Dom.Node) (i : Nat) (acc : Array Dom.Node) : Nat → m (Array Dom.Node)
  | 0 => return acc | rem + 1 => do snapshotChildrenM node (i + 1) (acc.push (← MonadDom.childAt node (UInt32.ofNat i))) rem

mutual
def applyToDomM [MonadDom msg m] (parent : Dom.Node) (index : UInt32) (node : Dom.Node) : Patch msg → m Unit
  | .replace new => do MonadDom.replaceChild parent index (← buildDomM (← MonadDom.childNamespace parent) new)
  | .setText s => MonadDom.setText node s
  | .patchElement attrs steps => do
      applyAttrsM node attrs
      if ownsChildren attrs then pure ()
      else
        let oldCount ← MonadDom.childCount node
        if positional 0 steps then
          applyPositionalStepsM node 0 steps
          let count ← MonadDom.childCount node; removeTailM node (UInt32.ofNat steps.length) (count.toNat - steps.length)
        else
          let live ← snapshotChildrenM node 0 #[] oldCount.toNat
          let finalJ ← applyKeyedStepsM node live 0 steps
          let count ← MonadDom.childCount node; removeTailM node finalJ (count.toNat - finalJ.toNat)
def applyPositionalStepsM [MonadDom msg m] (node : Dom.Node) (j : UInt32) : List (KeyedStep msg) → m Unit
  | [] => pure ()
  | .reuse _ p :: rest => do applyToDomM node j (← MonadDom.childAt node j) p; applyPositionalStepsM node (j + 1) rest
  | .create newH :: rest => do MonadDom.insertBeforeNode node j (← buildDomM (← MonadDom.childNamespace node) newH); applyPositionalStepsM node (j + 1) rest
def applyKeyedStepsM [MonadDom msg m] (node : Dom.Node) (live : Array Dom.Node) (j : UInt32) : List (KeyedStep msg) → m UInt32
  | [] => return j
  | .reuse oldIndex p :: rest => do let child := live.getD oldIndex 0; MonadDom.insertBeforeNode node j child; applyToDomM node j child p; applyKeyedStepsM node live (j + 1) rest
  | .create newH :: rest => do MonadDom.insertBeforeNode node j (← buildDomM (← MonadDom.childNamespace node) newH); applyKeyedStepsM node live (j + 1) rest
end

def patchHtmlSubtreeM [MonadDom msg m] (parent : Dom.Node) (index : UInt32) (node : Dom.Node) (oldHtml newHtml : Html msg) : m Dom.Node :=
  match diff oldHtml newHtml with
  | .replace h2 => do let n2 ← buildDomM (← MonadDom.childNamespace parent) h2; MonadDom.replaceChild parent index n2; return n2
  | p => do applyToDomM parent index node p; return node
@[inline] def buildDom (h : Handlers msg) (ns : String) (tree : Html msg) : IO Dom.Node := ReaderT.run (buildDomM (m := DomM msg) ns tree) h
@[inline] def hydrateDom (h : Handlers msg) (tree : Html msg) (node : Dom.Node) : IO Unit := ReaderT.run (hydrateDomM (m := DomM msg) tree node) h
end Qed
