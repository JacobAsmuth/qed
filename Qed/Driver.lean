/-
  Qed.Driver — the impure browser driver.

  This is the trusted mirror of the verified core. `buildDom` realises an `Html`
  tree as real DOM nodes; `applyToDom` executes a `Patch` (the same `Patch` proven
  correct in `Qed.Diff`) against the live DOM, **reusing existing nodes** rather
  than rebuilding — so focus, cursor, scroll, and selection survive an update.

  Because `diff` only emits `setText`/`patchElement` for unchanged structure, an
  update touches just the nodes that differ; the input the user is typing in is
  never recreated. The handler table (event id ↦ message) is rebuilt on each
  render, in the same walk that sets the matching `data-qed-click` attributes,
  so delegation stays consistent.

  Imported by WASM entry points only; pure app code never references it.
-/
import Qed.Runtime
import Qed.Diff
import Qed.Dom

namespace Qed

/-- Install one attribute on a DOM node. An `onClick` is registered by appending
    its message to the handler table and tagging the node with the index. -/
def applyAttr (handlers : IO.Ref (Array msg)) (node : Dom.Node) : Attr msg → IO Unit
  | .cls c     => Dom.setAttribute node "class" c
  | .attr k v  => Dom.setAttribute node k v
  | .onClick m => do
      let hs ← handlers.get
      handlers.set (hs.push m)
      Dom.setAttribute node "data-qed-click" (toString hs.size)

/-- Build a fresh DOM subtree from an `Html` node, returning its handle. -/
partial def buildDom (handlers : IO.Ref (Array msg)) : Html msg → IO Dom.Node
  | .text s => Dom.createText s
  | .element tag attrs children => do
      let node ← Dom.createElement tag
      for a in attrs do applyAttr handlers node a
      for c in children do
        Dom.appendChild node (← buildDom handlers c)
      return node

/-- Execute a patch against the live DOM, reusing nodes where possible. `parent`
    and `index` locate `node` within its parent, needed only for `replace`. -/
partial def applyToDom (handlers : IO.Ref (Array msg))
    (parent : Dom.Node) (index : UInt32) (node : Dom.Node) : Patch msg → IO Unit
  | .replace new => do
      Dom.replaceChild parent index (← buildDom handlers new)
  | .setText s => Dom.setText node s
  | .patchElement attrs kids => do
      for a in attrs do applyAttr handlers node a
      let mut i : UInt32 := 0
      for kid in kids do
        applyToDom handlers node i (← Dom.childAt node i) kid
        i := i + 1

/-- A type-erased running application — see `Qed.Runtime` discussion. The
    monomorphic closures seal the polymorphic `Model`/`Msg`. -/
structure Runtime where
  mount    : IO Unit
  dispatch : UInt32 → IO Unit

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

/-- Register `app` as the running application. The initial `mount` builds the DOM
    once; thereafter each event diffs the new view against the previous one and
    applies only the resulting patch. -/
def run (app : App Model Msg) : IO Unit := do
  let modelRef ← IO.mkRef app.init
  let treeRef  ← IO.mkRef (none : Option (Html Msg))
  let rootRef  ← IO.mkRef (0 : Dom.Node)
  let handlers ← IO.mkRef (#[] : Array Msg)
  let mount : IO Unit := do
    handlers.set #[]
    let tree := app.view (← modelRef.get)
    let node ← buildDom handlers tree
    Dom.mountRoot node
    rootRef.set node
    treeRef.set (some tree)
  let dispatch : UInt32 → IO Unit := fun id => do
    let hs ← handlers.get
    match hs[id.toNat]? with
    | none => IO.eprintln s!"qed: unknown event id {id}"
    | some msg => do
        modelRef.modify (app.update · msg)
        let newTree := app.view (← modelRef.get)
        match ← treeRef.get with
        | none => mount
        | some oldTree => do
            handlers.set #[]
            let root ← rootRef.get
            match diff oldTree newTree with
            | .replace newH => do
                let newNode ← buildDom handlers newH
                Dom.mountRoot newNode
                rootRef.set newNode
            | patch => applyToDom handlers root 0 root patch
            treeRef.set (some newTree)
  runtimeRef.set (some { mount := mount, dispatch := dispatch })

end Qed
