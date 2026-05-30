/-
  Qed.Driver — the impure browser driver.

  This is the trusted mirror of the verified core. `buildDom` realises an `Html`
  tree as real DOM nodes; `applyToDom` executes a `Patch` (the same `Patch` proven
  correct in `Qed.Diff`) against the live DOM, **reusing existing nodes** rather
  than rebuilding — so focus, cursor, scroll, and selection survive an update.

  Two handler tables (click ↦ message, input ↦ value-to-message) are rebuilt on
  every render in the same walk that tags nodes with `data-qed-click` /
  `data-qed-input`, so the JS delegation stays in sync. Effects requested by
  `update` (a `Cmd`) are interpreted here: a `stream` registers its callbacks and
  starts a streaming fetch whose chunks dispatch back through the same loop.

  Imported by WASM entry points only; pure app code never references it.
-/
import Qed.Runtime
import Qed.Diff
import Qed.Dom

namespace Qed

/-- The two event-handler tables, rebuilt each render. -/
structure Handlers (msg : Type) where
  click : IO.Ref (Array msg)
  input : IO.Ref (Array (String → msg))

/-- Install one attribute on a DOM node, registering event handlers as it goes.
    `value` is set as the live property (controlled input); a `flag` is set only
    when on (the patch path clears first, so off needs no work). -/
def applyAttr (h : Handlers msg) (node : Dom.Node) : Attr msg → IO Unit
  | .cls c          => Dom.setAttribute node "class" c
  | .attr "value" v => Dom.setValue node v
  | .attr k v       => Dom.setAttribute node k v
  | .flag k on      => if on then Dom.setAttribute node k k else Dom.removeAttribute node k
  | .key _          => pure ()   -- a reconciliation key never touches the DOM
  | .onClick m      => do
      let cs ← h.click.get
      h.click.set (cs.push m)
      Dom.setAttribute node "data-qed-click" (toString cs.size)
  | .onInput f      => do
      let is ← h.input.get
      h.input.set (is.push f)
      Dom.setAttribute node "data-qed-input" (toString is.size)
  | .onCheck f      => do
      -- shares the string-handler table; the host sends "true"/"false" for a check
      let is ← h.input.get
      h.input.set (is.push (fun s => f (s == "true")))
      Dom.setAttribute node "data-qed-check" (toString is.size)

/-- Apply a (normalized) attribute list, so the live DOM matches what `render`
    would produce — classes merged, duplicate keys collapsed. -/
def applyAttrs (h : Handlers msg) (node : Dom.Node) (attrs : List (Attr msg)) : IO Unit := do
  for a in normalizeAttrs attrs do applyAttr h node a

/-- Build a fresh DOM subtree from an `Html` node, returning its handle. -/
partial def buildDom (h : Handlers msg) : Html msg → IO Dom.Node
  | .text s => Dom.createText s
  | .element tag attrs children => do
      let node ← Dom.createElement tag
      applyAttrs h node attrs
      for c in children do
        Dom.appendChild node (← buildDom h c)
      return node

mutual
/-- Execute a patch against the live DOM, reusing nodes where possible. `parent`
    and `index` locate `node` within its parent, needed only for `replace`. -/
partial def applyToDom (h : Handlers msg)
    (parent : Dom.Node) (index : UInt32) (node : Dom.Node) : Patch msg → IO Unit
  | .replace new => do
      Dom.replaceChild parent index (← buildDom h new)
  | .setText s => Dom.setText node s
  | .patchElement attrs kids => do
      -- reconcile attributes in place: `setAttribute` is guarded (unchanged keys are
      -- not touched, so a typed input keeps its caret) and a toggled-off `flag`
      -- removes its key. node identity — hence focus/cursor — is preserved.
      applyAttrs h node attrs
      applyChildrenToDom h node 0 kids
  | .patchKeyed attrs steps => do
      applyAttrs h node attrs
      -- Snapshot the current child handles by their original index. Handles stay
      -- valid as the nodes move, so a `reuse i` always resolves to the same node.
      let oldCount ← Dom.childCount node
      let mut live : Array Dom.Node := #[]
      for i in [0:oldCount.toNat] do
        live := live.push (← Dom.childAt node (UInt32.ofNat i))
      -- Walk the steps in new order, placing the right node at each position `j`.
      -- `insertBefore` moves a reused node (keeping its identity) or inserts a new
      -- one; reused nodes are then patched in place.
      let mut j : UInt32 := 0
      for step in steps do
        match step with
        | .reuse oldIndex p => do
            let child := live.getD oldIndex 0
            Dom.insertBefore node j child
            applyToDom h node j child p
        | .create newH => do
            Dom.insertBefore node j (← buildDom h newH)
        j := j + 1
      -- Old nodes whose key wasn't reused are now past `j`; drop them.
      let count ← Dom.childCount node
      for _ in [j.toNat:count.toNat] do Dom.removeChild node j

/-- Mirror a `ChildPatch` onto `node`'s children: patch the prefix in place (so each
    reused child keeps its identity), then append freshly-built nodes for the surplus
    new children, or remove the surplus old ones. `i` is the next child index. -/
partial def applyChildrenToDom (h : Handlers msg) (node : Dom.Node) (i : UInt32) :
    ChildPatch msg → IO Unit
  | .patch p rest => do
      applyToDom h node i (← Dom.childAt node i) p
      applyChildrenToDom h node (i + 1) rest
  | .append news => do
      for nh in news do Dom.appendChild node (← buildDom h nh)
  | .drop => do
      -- children at indices [i, count) are gone; removing at `i` repeatedly works
      -- because each removal shifts the next child down into index `i`.
      let count ← Dom.childCount node
      for _ in [i.toNat:count.toNat] do Dom.removeChild node i
end

/-- A type-erased running application — the monomorphic closures seal the
    polymorphic `Model`/`Msg` so the export wrappers below stay first-order. -/
structure Runtime where
  mount       : IO Unit
  dispatch    : UInt32 → IO Unit
  dispatchStr : UInt32 → String → IO Unit
  streamChunk : UInt32 → String → IO Unit
  streamDone  : UInt32 → IO Unit

initialize runtimeRef : IO.Ref (Option Runtime) ← IO.mkRef none

@[export qed_init]
def qedInit : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.mount
  | none    => IO.eprintln "qed: no application registered"

@[export qed_dispatch]
def qedDispatch (id : UInt32) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.dispatch id
  | none    => pure ()

@[export qed_dispatch_str]
def qedDispatchStr (id : UInt32) (s : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.dispatchStr id s
  | none    => pure ()

@[export qed_stream_chunk]
def qedStreamChunk (cid : UInt32) (chunk : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.streamChunk cid chunk
  | none    => pure ()

@[export qed_stream_done]
def qedStreamDone (did : UInt32) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.streamDone did
  | none    => pure ()

/-- Register `app` as the running application. The initial `mount` builds the DOM
    and runs the startup effect; thereafter each message updates the model, diffs
    the new view against the previous one, patches the difference, and interprets
    the requested effect (which may dispatch further messages over time). -/
def run (app : App Model Msg) : IO Unit := do
  let modelRef ← IO.mkRef app.init.1
  let treeRef  ← IO.mkRef (none : Option (Html Msg))
  let rootRef  ← IO.mkRef (0 : Dom.Node)
  let clickRef ← IO.mkRef (#[] : Array Msg)
  let inputRef ← IO.mkRef (#[] : Array (String → Msg))
  let h : Handlers Msg := { click := clickRef, input := inputRef }
  -- Stream callbacks persist across renders (a stream outlives many of them).
  let chunkCbRef ← IO.mkRef (#[] : Array (String → Msg))
  let doneCbRef  ← IO.mkRef (#[] : Array Msg)
  -- Forward reference to the dispatcher, so an effect (`Cmd.now`) can feed a
  -- message back through the loop (set to the real dispatcher just below).
  let dispatchRef ← IO.mkRef (fun (_ : Msg) => (pure () : IO Unit))
  let renderModel : IO Unit := do
    clickRef.set #[]; inputRef.set #[]
    let newTree := app.view (← modelRef.get)
    (match ← treeRef.get with
     | none => do
         let node ← buildDom h newTree
         Dom.mountRoot node; rootRef.set node
     | some oldTree => do
         let root ← rootRef.get
         match diff oldTree newTree with
         | .replace newH => do
             let node ← buildDom h newH
             Dom.mountRoot node; rootRef.set node
         | patch => applyToDom h root 0 root patch)
    treeRef.set (some newTree)
  let perform : Cmd Msg → IO Unit := fun
    | .none => pure ()
    | .stream url body onChunk onDone => do
        let cs ← chunkCbRef.get; chunkCbRef.set (cs.push onChunk)
        let ds ← doneCbRef.get;  doneCbRef.set (ds.push onDone)
        Dom.fetchStream url body (UInt32.ofNat cs.size) (UInt32.ofNat ds.size)
    | .now onNow => do
        -- reading the clock is instant; parse it and feed `onNow today` back in
        match Qed.Date.parse? (← Dom.today) with
        | some d => (← dispatchRef.get) (onNow d)
        | none   => pure ()
  let dispatchMsg : Msg → IO Unit := fun msg => do
    let (m', cmd) := app.update (← modelRef.get) msg
    modelRef.set m'
    renderModel
    perform cmd
  dispatchRef.set dispatchMsg
  runtimeRef.set (some {
    mount := do renderModel; perform app.init.2
    dispatch := fun id => do
      match (← clickRef.get)[id.toNat]? with
      | some msg => dispatchMsg msg
      | none     => IO.eprintln s!"qed: unknown click id {id}"
    dispatchStr := fun id s => do
      match (← inputRef.get)[id.toNat]? with
      | some f => dispatchMsg (f s)
      | none   => pure ()
    streamChunk := fun cid c => do
      match (← chunkCbRef.get)[cid.toNat]? with
      | some f => dispatchMsg (f c)
      | none   => pure ()
    streamDone := fun did => do
      match (← doneCbRef.get)[did.toNat]? with
      | some msg => dispatchMsg msg
      | none     => pure ()
  })

end Qed
