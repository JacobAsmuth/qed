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
import Qed.View
import Std.Data.HashMap

namespace Qed

/-- The two event-handler tables, rebuilt each render. -/
structure Handlers (msg : Type) where
  click : IO.Ref (Array msg)
  input : IO.Ref (Array (String → msg))
  /-- Mount the local component `component` at instance `key` into `host`, optionally
      seeding state with `init?`, and wiring its serialized output through `bubble`.
      Supplied by `run`; idempotent per key, so a re-render of the parent leaves an
      already-mounted instance (and its state and focus) untouched. An instance's own
      tables carry a real `mountLocal` too, so local components nest. -/
  mountLocal : String → String → Option String → (String → Option msg) → Dom.Node → IO Unit

/-- A live local-component instance: its own event tables, the last child tree it
    rendered (to diff against), its host node, its view, and an output sink already
    wired to bubble through the root dispatcher. -/
structure LocalInstance where
  handlers : Handlers LocalMsg
  treeRef  : IO.Ref (Html LocalMsg)
  host     : Dom.Node
  view     : String → Html LocalMsg
  onOutput : String → IO Unit

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
  | .onKeydown f    => do
      let is ← h.input.get
      h.input.set (is.push f)         -- host sends the key name into the string table
      Dom.setAttribute node "data-qed-keydown" (toString is.size)
  | .onKeyup f      => do
      let is ← h.input.get
      h.input.set (is.push f)
      Dom.setAttribute node "data-qed-keyup" (toString is.size)
  | .onSubmit m     => do
      let cs ← h.click.get            -- no-arg messages share the click table
      h.click.set (cs.push m)
      Dom.setAttribute node "data-qed-submit" (toString cs.size)
  | .onBlur m       => do
      let cs ← h.click.get
      h.click.set (cs.push m)
      Dom.setAttribute node "data-qed-blur" (toString cs.size)
  | .onFocus m      => do
      let cs ← h.click.get
      h.click.set (cs.push m)
      Dom.setAttribute node "data-qed-focus" (toString cs.size)
  | .localCell key comp init bubble => do
      -- Mark the host (namespaced by component, so keys can't collide) so the JS
      -- delegation routes events inside it to this instance, then mount the local
      -- component (idempotent — a re-render won't remount it).
      Dom.setAttribute node "data-qed-local" (localKey comp key)
      h.mountLocal key comp init bubble node
  | .signalBind name => Dom.bindSignal node name   -- bind text to the signal; setSignal updates it
  | .signalAttr name attr _ => Dom.bindSignalAttr node name attr   -- bind an attribute to the signal

/-- Apply a (normalized) attribute list, so the live DOM matches what `render`
    would produce — classes merged, duplicate keys collapsed. -/
def applyAttrs (h : Handlers msg) (node : Dom.Node) (attrs : List (Attr msg)) : IO Unit := do
  for a in normalizeAttrs attrs do applyAttr h node a

/-- Are this element's children owned by the driver — a local component (filled from
    local state) or a signal (its text)? Then the parent's diff must not reconcile them:
    an empty `Html` child list is vacuously "keyed", and the keyed applier would treat the
    driver-managed child as surplus and drop it. -/
def ownsChildren (attrs : List (Attr msg)) : Bool :=
  attrs.any (fun | .localCell .. => true | .signalBind .. => true | _ => false)

/-- Are the keyed steps a pure in-place update — every step a `reuse` whose old index
    equals its position (nothing moved, nothing created)? Then the children stay put, so
    the applier can patch them where they sit and skip the snapshot + per-child move. -/
def identityReuse : Nat → List (KeyedStep msg) → Bool
  | _, []                        => true
  | i, .reuse oldIndex _ :: rest => oldIndex == i && identityReuse (i + 1) rest
  | _, .create _ :: _            => false

/-- Build a fresh DOM subtree from an `Html` node, returning its handle. -/
partial def buildDom (h : Handlers msg) : Html msg → IO Dom.Node
  | .text s => Dom.createText s
  | .lazy _ sub => buildDom h sub   -- a lazy node is its content; build it
  | .element tag attrs children => do
      let node ← Dom.createElement tag
      applyAttrs h node attrs          -- a local host's children are added here, by mountLocal
      unless ownsChildren attrs do
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
  | .lazyReuse _ _ =>
      -- the key was unchanged, so the existing DOM is already correct: skip it. This is
      -- the one place the driver trusts the developer's "equal key ⇒ equal subtree"
      -- promise rather than mirroring `applyPatch` (which would rebuild `sub`).
      pure ()
  | .lazyPatch _ p =>
      -- the key changed: the lazy node's DOM *is* its content's, so patch it in place
      applyToDom h parent index node p
  | .patchElement attrs kids => do
      -- reconcile attributes in place: `setAttribute` is guarded (unchanged keys are
      -- not touched, so a typed input keeps its caret) and a toggled-off `flag`
      -- removes its key. node identity — hence focus/cursor — is preserved.
      applyAttrs h node attrs
      unless ownsChildren attrs do applyChildrenToDom h node 0 kids
  | .patchKeyed attrs steps => do
      applyAttrs h node attrs
      if ownsChildren attrs then return    -- driver owns this host's children; leave them
      let oldCount ← Dom.childCount node
      -- Fast path: nothing moved or was added/removed (an `update`, not a reorder). Patch
      -- each child where it sits — no snapshot, no insertBefore — and skip those whose
      -- subtree didn't change (`lazyReuse`). This makes such an update O(changed) DOM ops.
      if identityReuse 0 steps && oldCount == UInt32.ofNat steps.length then
        let mut j : UInt32 := 0
        for step in steps do
          match step with
          | .reuse _ (.lazyReuse _ _) => pure ()
          | .reuse _ p                => applyToDom h node j (← Dom.childAt node j) p
          | .create _                 => pure ()
          j := j + 1
        return
      -- General path: snapshot the current child handles by their original index. Handles
      -- stay valid as the nodes move, so a `reuse i` always resolves to the same node.
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

/-! ### Fine-grained template runtime

    A `View` template is built into DOM *once*; thereafter only the dynamic projections
    re-run. `VState` is the runtime mirror of a rendered template — it holds the DOM
    handle of each node plus the last value of each dynamic binding, so an update walks
    the *template* (constant size — the view code, not the data) and touches only the DOM
    nodes whose projection changed. No new `Html` tree is built and no tree is diffed for
    the scalar parts; that is the fine-grained win. Structure that changes shape
    (`showIf`, `keyedList`) reconciles through the **verified** `diff`/`applyToDom`, so
    the trusted surface does not grow. -/

/-- Does this attribute carry an event handler (so it must be re-registered each update
    to keep the handler table in sync), as opposed to a value/class/flag that is set
    once and only re-touched when it changes? -/
def Attr.isEvent : Attr msg → Bool
  | .onClick _ | .onInput _ | .onCheck _ | .onKeydown _ | .onKeyup _
  | .onSubmit _ | .onBlur _ | .onFocus _ => true
  | _ => false

/-- The runtime mirror of a rendered `View` node: built *once*, then mutated in place
    through `IO.Ref`s so an update allocates nothing for the scalar skeleton (the whole
    point — a functional rebuild would re-allocate an O(n) tree every update, exactly the
    cost the template is meant to avoid). It holds each node's DOM handle plus whatever
    the update must remember: a dynamic text's last value, a conditional's current branch,
    a keyed list's last rows for the next diff. -/
inductive VState (σ : Type) (msg : Type) where
  /-- A static text node — never updated. -/
  | text (node : Dom.Node)
  /-- A dynamic text node and a cell holding the last value written to it. -/
  | dyn (node : Dom.Node) (last : IO.Ref String)
  /-- An element and the (fixed) states of its children, walked in lockstep. -/
  | elem (node : Dom.Node) (kids : Array (VState σ msg))
  /-- A conditional slot, identified by its index into the driver's external `condCells`
      array (which holds the mutable `shown?`/inner state — kept off this inductive
      because a recursive `IO.Ref (… VState …)` field is not a legal occurrence). -/
  | cond (cell : Nat)
  /-- A keyed-list container and cells of the last render: the row keys (to decide
      value-only vs structural), the per-row signal values (to push only what changed),
      and the last `Html` rows (to diff on a shape change). -/
  | list (node : Dom.Node) (keys : IO.Ref (Array String))
      (sigs : IO.Ref (Array (String × String))) (rows : IO.Ref (List (Html msg)))
  /-- An opaque embedded `Html` subtree (`View.static`) — not fine-grained-updated. -/
  | stat (node : Dom.Node)
  /-- A scope-bound `Html` subtree (`View.dynNode`): the diff escape hatch. Holds a *mutable*
      node handle (a shape change can replace it) and the last rendered `Html`, so each update
      reconciles through the verified `diff` — never a value patch. -/
  | dynNode (nref : IO.Ref Dom.Node) (last : IO.Ref (Html msg))

instance : Inhabited (VState σ msg) := ⟨.text 0⟩

/-- The mutable state of every `showIf` slot, external to `VState` (so the inductive has
    no recursive-ref field): `(shown?, inner state when shown)`, indexed by `VState.cond`. -/
abbrev CondCells (σ msg : Type) := IO.Ref (Array (Bool × Option (VState σ msg)))

mutual
/-- Build a template into DOM once, returning the root node and its `VState` mirror.
    Events register into the handler tables exactly as `buildDom` does, so the JS
    delegation works identically. `cells` accumulates one entry per `showIf`. -/
partial def buildView (h : Handlers msg) (cells : CondCells σ msg) :
    View σ msg → σ → IO (Dom.Node × VState σ msg)
  | .text s,          _ => do let n ← Dom.createText s; return (n, .text n)
  | .dyn get,         s => do
      let v := get s; let n ← Dom.createText v; let r ← IO.mkRef v
      return (n, .dyn n r)
  | .static html,     _ => do let n ← buildDom h html; return (n, .stat n)
  | .element tag attrs kids, s => do
      let node ← Dom.createElement tag
      applyAttrs h node (attrs.map (VAttr.eval s))
      let mut ks : Array (VState σ msg) := #[]
      for k in kids do
        let (kn, kst) ← buildView h cells k s
        Dom.appendChild node kn
        ks := ks.push kst
      return (node, .elem node ks)
  | .showIf cond child, s => do
      -- reserve this slot's cell first, so the child's own slots get later indices
      let idx := (← cells.get).size
      cells.modify (·.push (false, none))
      if cond s then
        let (cn, cst) ← buildView h cells child s
        cells.modify (·.set! idx (true, some cst))
        return (cn, .cond idx)
      else
        let n ← Dom.createText ""
        return (n, .cond idx)
  | .ifElse cond yes no, s => do
      -- one slot showing the active branch; reserve this cell before building it so the
      -- branch's own conditional slots get later indices. The cell's `Bool` is "is `yes`".
      let idx := (← cells.get).size
      cells.modify (·.push (false, none))
      let (cn, cst) ← buildView h cells (if cond s then yes else no) s
      cells.modify (·.set! idx (cond s, some cst))
      return (cn, .cond idx)
  | .dynNode get, s => do
      let html := get s
      let n ← buildDom h html
      return (n, .dynNode (← IO.mkRef n) (← IO.mkRef html))
  | .keyedList tag attrs keys sigs rowsHtml, s => do
      let node ← Dom.createElement tag
      applyAttrs h node (attrs.map (VAttr.eval s))
      let sg := sigs s
      for (nm, v) in sg do Dom.effect "signal.set" nm v ""   -- seed signal values first…
      let rs := rowsHtml s
      for r in rs do Dom.appendChild node (← buildDom h r)   -- …so bindSignal reads them
      return (node, .list node (← IO.mkRef (keys s)) (← IO.mkRef sg) (← IO.mkRef rs))

/-- Walk the template against the new scope, mutating leaf cells and patching only what
    changed. `parent`/`index` locate the current node for the one case that replaces it (a
    `showIf` flip). Events are re-registered in pre-order (matching how the DOM ids were
    assigned at build), so the handler tables stay consistent without rebuilding the tree. -/
partial def patchView (h : Handlers msg) (cells : CondCells σ msg)
    (parent : Dom.Node) (index : UInt32) :
    View σ msg → σ → VState σ msg → IO Unit
  | .dyn get, s, .dyn node last => do
      let v := get s
      if v != (← last.get) then Dom.setText node v; last.set v
  | .element _ attrs kids, s, .elem node kstates => do
      -- re-apply dynamic *value* attributes; leave static attrs and all events alone (set
      -- once at build — the tables are not reset, so re-registering would grow them)
      for va in attrs do
        match va with
        | .bind f          => let a := f s; unless a.isEvent do applyAttr h node a
        | .dynVal attr get => applyAttr h node (.attr attr (get s))
        | .stat _          => pure ()
      let mut i : UInt32 := 0
      for k in kids do
        patchView h cells node i k s (kstates.getD i.toNat default)
        i := i + 1
  | .showIf cond child, s, .cond idx => do
      let (shown, inner) := (← cells.get).getD idx (false, none)
      let now := cond s
      if now == shown then
        match inner with
        | some ist => patchView h cells parent index child s ist
        | none     => pure ()
      else if now then do
        let (cn, cst) ← buildView h cells child s   -- hidden → shown: install the child
        Dom.replaceChild parent index cn
        cells.modify (·.set! idx (true, some cst))
      else do
        let n ← Dom.createText ""                   -- shown → hidden: empty the slot
        Dom.replaceChild parent index n
        cells.modify (·.set! idx (false, none))
  | .ifElse cond yes no, s, .cond idx => do
      let (wasYes, inner) := (← cells.get).getD idx (false, none)
      let now := cond s
      let active := if now then yes else no
      if now == wasYes then
        match inner with                            -- same branch: value-patch it in place
        | some ist => patchView h cells parent index active s ist
        | none     => pure ()
      else do
        let (cn, cst) ← buildView h cells active s   -- flipped: install the other branch
        Dom.replaceChild parent index cn
        cells.modify (·.set! idx (now, some cst))
  | .dynNode get, s, .dynNode nref last => do
      let newHtml := get s
      let node ← nref.get
      match diff (← last.get) newHtml with
      | .replace h2 => do                            -- root shape changed: rebuild the subtree
          let n2 ← buildDom h h2
          Dom.replaceChild parent index n2
          nref.set n2
      | p => applyToDom h parent index node p        -- otherwise patch in place (verified diff)
      last.set newHtml
  | .keyedList tag attrs keys sigs rowsHtml, s, .list node lastKeys lastSigs lastRows => do
      if (keys s) == (← lastKeys.get) then
        -- value-only update: the key set/order is unchanged, so no row was added, removed,
        -- or moved. Push only the rows whose signal value changed — a direct `setSignal`
        -- (JS Map write), no `Html` built, no diff, no `childAt`. This is the list win.
        let newSigs := sigs s
        let oldSigs ← lastSigs.get
        for i in [0:newSigs.size] do
          let (nm, v) := newSigs[i]!
          if v != (oldSigs.getD i ("", "")).2 then Dom.effect "signal.set" nm v ""
        lastSigs.set newSigs
      else
        -- the keys changed (add/remove/reorder): seed signal values first (so freshly built
        -- rows bind to them), then reconcile structure through the verified diff.
        let newSigs := sigs s
        for (nm, v) in newSigs do Dom.effect "signal.set" nm v ""
        let evAttrs := attrs.map (VAttr.eval s)
        let newRows := rowsHtml s
        applyToDom h parent index node
          (diff (.element tag evAttrs (← lastRows.get)) (.element tag evAttrs newRows))
        lastKeys.set (keys s); lastSigs.set newSigs; lastRows.set newRows
  | .text _,   _, _ => pure ()
  | .static _, _, _ => pure ()
  | v, s, _ => do
      -- template/state shape disagree (should not happen): rebuild this node
      let (n, _) ← buildView h cells v s
      Dom.replaceChild parent index n
end

/-- Everything the local-component runtime threads around: the registry of declared
    components, the keyed store of serialized state, and the live instances. Shared by
    every nesting level (one flat store, keyed by `localKey component key`). -/
structure LocalCtx where
  registry  : Std.HashMap String LocalDef
  store     : IO.Ref (Std.HashMap String String)
  instances : IO.Ref (Std.HashMap String LocalInstance)

mutual
/-- Create and register an instance: its own event tables, its child subtree built
    into `host`, and a `mountLocal` for ITS children (so locals nest). `onOut` is how
    its output reaches its parent (root dispatch, or a parent instance's transition). -/
partial def spawnInstance (ctx : LocalCtx) (fk : String) (ldef : LocalDef) (s0 : String)
    (onOut : String → IO Unit) (host : Dom.Node) : IO Unit := do
  ctx.store.modify (·.insert fk s0)
  let cRef ← IO.mkRef (#[] : Array LocalMsg)
  let iRef ← IO.mkRef (#[] : Array (String → LocalMsg))
  -- a nested local's output runs as a message on THIS instance (looked up at fire
  -- time, since this instance isn't in the map yet while we build its tables).
  let lh : Handlers LocalMsg :=
    { click := cRef, input := iRef,
      mountLocal := fun k c i b hn =>
        localMountInstance ctx (fun lm => do
          match (← ctx.instances.get)[fk]? with
          | some self => localRun ctx fk self lm
          | none      => pure ()) k c i b hn }
  let tree := ldef.view s0
  Dom.appendChild host (← buildDom lh tree)
  let tRef ← IO.mkRef tree
  ctx.instances.modify (·.insert fk
    { handlers := lh, treeRef := tRef, host := host, view := ldef.view, onOutput := onOut })

/-- Re-render an instance's subtree from new serialized state, reusing the verified
    `diff`/`applyToDom` at the child's own message type — so focus inside it survives. -/
partial def localRerender (inst : LocalInstance) (s' : String) : IO Unit := do
  inst.handlers.click.set #[]; inst.handlers.input.set #[]
  let newTree := inst.view s'
  match diff (← inst.treeRef.get) newTree with
  | .replace newH => Dom.replaceChild inst.host 0 (← buildDom inst.handlers newH)
  | patch         => applyToDom inst.handlers inst.host 0 (← Dom.childAt inst.host 0) patch
  inst.treeRef.set newTree

/-- Run one local message: update the stored state, re-render the subtree, then let
    any emitted output flow to the parent via `onOutput`. -/
partial def localRun (ctx : LocalCtx) (fk : String) (inst : LocalInstance) (lm : LocalMsg) : IO Unit := do
  let (s', o) := lm.run ((← ctx.store.get).getD fk "")
  ctx.store.modify (·.insert fk s')
  localRerender inst s'
  match o with | some out => inst.onOutput out | none => pure ()

/-- Mount a local component nested inside another. Its output is a `LocalMsg` for the
    parent instance (`parentBubble`). Idempotent per namespaced key. -/
partial def localMountInstance (ctx : LocalCtx) (parentBubble : LocalMsg → IO Unit)
    (key component : String) (init? : Option String) (bubble : String → Option LocalMsg)
    (host : Dom.Node) : IO Unit := do
  let fk := localKey component key
  if (← ctx.instances.get).contains fk then return
  match ctx.registry[component]? with
  | none      => IO.eprintln s!"qed: unknown local component '{component}'"
  | some ldef =>
      let onOut : String → IO Unit := fun out => match bubble out with
        | some lm => parentBubble lm
        | none    => pure ()
      spawnInstance ctx fk ldef ((← ctx.store.get).getD fk (init?.getD ldef.init)) onOut host
end

/-- Mount a top-level local component (its host sits in the root view). Its output
    becomes a root message via `dispatchMsg`. Idempotent per namespaced key. -/
partial def localMountRoot {Msg : Type} (ctx : LocalCtx) (dispatchMsg : Msg → IO Unit)
    (key component : String) (init? : Option String) (bubble : String → Option Msg)
    (host : Dom.Node) : IO Unit := do
  let fk := localKey component key
  if (← ctx.instances.get).contains fk then return
  match ctx.registry[component]? with
  | none      => IO.eprintln s!"qed: unknown local component '{component}'"
  | some ldef =>
      let onOut : String → IO Unit := fun out => match bubble out with
        | some m => dispatchMsg m
        | none   => pure ()
      spawnInstance ctx fk ldef ((← ctx.store.get).getD fk (init?.getD ldef.init)) onOut host

/-- A type-erased running application — the monomorphic closures seal the
    polymorphic `Model`/`Msg` so the export wrappers below stay first-order. -/
structure Runtime where
  mount       : IO Unit
  dispatch    : UInt32 → IO Unit
  dispatchStr : UInt32 → String → IO Unit
  streamChunk : UInt32 → String → IO Unit
  streamDone  : UInt32 → IO Unit
  httpDone    : UInt32 → Bool → String → IO Unit
  urlChanged  : String → IO Unit
  /-- A no-arg event (click/submit/focus/blur) inside the local instance `key`. -/
  localDispatch    : String → UInt32 → IO Unit
  /-- A value event (input/check/key) inside the local instance `key`. -/
  localDispatchStr : String → UInt32 → String → IO Unit
  /-- Serialize the whole local-state store to a JSON object (key ↦ state), for
      persistence, devtools, or time-travel. -/
  snapshot : IO String
  /-- Replace local state from a `snapshot` string and re-render every live instance. -/
  restore  : String → IO Unit
  /-- A native `fxResult` effect (id) resolved with `result`. -/
  effectDone : UInt32 → String → IO Unit
  /-- An inbound port message `(name, payload)` from the app's JS. -/
  portRecv   : String → String → IO Unit

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

@[export qed_http_done]
def qedHttpDone (id : UInt32) (ok : UInt32) (text : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.httpDone id (ok != 0) text
  | none    => pure ()

@[export qed_url_changed]
def qedUrlChanged (path : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.urlChanged path
  | none    => pure ()

@[export qed_local_dispatch]
def qedLocalDispatch (key : String) (id : UInt32) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.localDispatch key id
  | none    => pure ()

@[export qed_local_dispatch_str]
def qedLocalDispatchStr (key : String) (id : UInt32) (s : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.localDispatchStr key id s
  | none    => pure ()

@[export qed_local_snapshot]
def qedLocalSnapshot : IO String := do
  match ← runtimeRef.get with
  | some rt => rt.snapshot
  | none    => return "{}"

@[export qed_local_restore]
def qedLocalRestore (s : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.restore s
  | none    => pure ()

@[export qed_effect_done]
def qedEffectDone (id : UInt32) (result : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.effectDone id result
  | none    => pure ()

@[export qed_port_recv]
def qedPortRecv (name payload : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.portRecv name payload
  | none    => pure ()

/-- Register `app` as the running application. The initial `mount` builds the DOM
    and runs the startup effect; thereafter each message updates the model, diffs
    the new view against the previous one, patches the difference, and interprets
    the requested effect (which may dispatch further messages over time). -/
def run (app : App Model Msg) (template : Option (View Model Msg) := none) : IO Unit := do
  let modelRef ← IO.mkRef app.init.1
  let treeRef  ← IO.mkRef (none : Option (Html Msg))
  let vstateRef ← IO.mkRef (none : Option (VState Model Msg))
  let condCells ← IO.mkRef (#[] : Array (Bool × Option (VState Model Msg)))
  let rootRef  ← IO.mkRef (0 : Dom.Node)
  let clickRef ← IO.mkRef (#[] : Array Msg)
  let inputRef ← IO.mkRef (#[] : Array (String → Msg))
  -- Stream callbacks persist across renders (a stream outlives many of them).
  let chunkCbRef ← IO.mkRef (#[] : Array (String → Msg))
  let doneCbRef  ← IO.mkRef (#[] : Array Msg)
  -- HTTP response callbacks (each request's result arrives later), persistent.
  let respCbRef  ← IO.mkRef (#[] : Array (Except String String → Msg))
  -- Native `fxResult` callbacks (storageGet/after/randomInt/paste/pickFile …), persistent.
  let effectCbRef ← IO.mkRef (#[] : Array (String → Msg))
  -- Forward reference to the dispatcher, so an effect (`Cmd.now`) — or a local
  -- component bubbling an output — can feed a message back through the loop.
  let dispatchRef ← IO.mkRef (fun (_ : Msg) => (pure () : IO Unit))
  -- Local-component runtime: a registry of declared components, a keyed store of
  -- serialized state, and the live instances (each with its own event tables).
  let registry : Std.HashMap String LocalDef :=
    app.locals.foldl (fun m d => m.insert d.id d) ∅
  let storeRef     ← IO.mkRef (∅ : Std.HashMap String String)
  let instancesRef ← IO.mkRef (∅ : Std.HashMap String LocalInstance)
  let ctx : LocalCtx := { registry, store := storeRef, instances := instancesRef }
  -- The root view mounts top-level locals; a bubbled output becomes a root message.
  let h : Handlers Msg :=
    { click := clickRef, input := inputRef,
      mountLocal := fun k c i b hn => localMountRoot ctx (fun m => do (← dispatchRef.get) m) k c i b hn }
  -- Drop instances (and their state) whose host left the DOM, so an unmounted cell
  -- doesn't leak and re-mounting starts fresh (React's unmount-loses-state).
  let gcLocals : IO Unit := do
    let mut dead : Array String := #[]
    for (k, inst) in (← instancesRef.get).toList do
      unless (← Dom.isConnected inst.host) do dead := dead.push k
    for k in dead do
      instancesRef.modify (·.erase k); storeRef.modify (·.erase k)
  let renderModel : IO Unit := do
    match template with
    | some t => do
        -- Fine-grained path: build once, thereafter walk the template and patch only the
        -- bindings whose projection changed (no new tree, no diff for the scalars). The
        -- handler tables are NOT reset here: static events are registered once at build and
        -- persist, so a value-only update touches no events (and a row click survives it).
        match ← vstateRef.get with
        | none => do
            let (node, vst) ← buildView h condCells t (← modelRef.get)
            Dom.mountRoot node; rootRef.set node; vstateRef.set (some vst)
        | some vst => patchView h condCells (← rootRef.get) 0 t (← modelRef.get) vst
    | none => do
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
    gcLocals
  -- Interpret one leaf effect. `batch` is flattened away by `Cmd.flatten` first, so
  -- this stays non-recursive (no termination obligation through `List.forM`).
  let performLeaf : Cmd Msg → IO Unit := fun
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
    | .request method url body onResult => do
        let rs ← respCbRef.get; respCbRef.set (rs.push onResult)
        Dom.httpSend method url body (UInt32.ofNat rs.size)
    | .pushUrl path => do
        Dom.pushPath path
        match app.onUrlChange with
        | some f => (← dispatchRef.get) (f path)
        | none   => pure ()
    | .port name payload => Dom.portSend name payload
    | .fx kind a b c => Dom.effect kind a b c
    | .fxResult kind a b onResult => do
        let cs ← effectCbRef.get; effectCbRef.set (cs.push onResult)
        Dom.effectResult kind a b (UInt32.ofNat cs.size)
    | .batch _ => pure ()   -- unreachable: flattened away below
  let perform : Cmd Msg → IO Unit := fun cmd => (Cmd.flatten cmd).forM performLeaf
  let dispatchMsg : Msg → IO Unit := fun msg => do
    let (m', cmd) := app.update (← modelRef.get) msg
    modelRef.set m'
    renderModel
    perform cmd
  dispatchRef.set dispatchMsg
  -- A local event (routed by the JS host to the nearest local host, which is namespaced
  -- by component): look up the instance and run the handler's message on its state.
  let localDispatch : String → UInt32 → IO Unit := fun fullKey id => do
    match (← instancesRef.get)[fullKey]? with
    | some inst => match (← inst.handlers.click.get)[id.toNat]? with
                   | some lm => localRun ctx fullKey inst lm
                   | none    => pure ()
    | none      => pure ()
  let localDispatchStr : String → UInt32 → String → IO Unit := fun fullKey id s => do
    match (← instancesRef.get)[fullKey]? with
    | some inst => match (← inst.handlers.input.get)[id.toNat]? with
                   | some f => localRun ctx fullKey inst (f s)
                   | none   => pure ()
    | none      => pure ()
  -- A native `fxResult` effect resolved: dispatch its callback with the result string.
  let effectDone : UInt32 → String → IO Unit := fun id result => do
    match (← effectCbRef.get)[id.toNat]? with
    | some onResult => dispatchMsg (onResult result)
    | none          => pure ()
  -- An inbound port message (app JS called `__qed.send`): route it through `onPort`.
  let portRecv : String → String → IO Unit := fun name payload => do
    match app.onPort with
    | some f => match f name payload with | some m => dispatchMsg m | none => pure ()
    | none   => pure ()
  -- Serialize the keyed store to a JSON object {fullKey: <state>} (states are already
  -- JSON, kept here as string values), and restore it, re-rendering every instance.
  let snapshotLocals : IO String := do
    let members := (← storeRef.get).toList.map (fun (k, v) => (k, Json.str v))
    return Json.render (Json.obj members)
  let restoreLocals : String → IO Unit := fun s => do
    match Json.parse s with
    | .ok (.obj members) => do
        for (k, v) in members do
          match v with | .str st => storeRef.modify (·.insert k st) | _ => pure ()
        for (k, inst) in (← instancesRef.get).toList do
          localRerender inst ((← storeRef.get).getD k "")
    | _ => pure ()
  runtimeRef.set (some {
    mount := do
      -- If routed, derive the initial model from the current URL before the first
      -- render (so it reflects the route); otherwise just render.
      match app.onUrlChange with
      | some f => do let p ← Dom.currentPath; dispatchMsg (f p)
      | none   => renderModel
      perform app.init.2
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
    httpDone := fun id ok text => do
      match (← respCbRef.get)[id.toNat]? with
      | some f => dispatchMsg (f (if ok then .ok text else .error text))
      | none   => pure ()
    urlChanged := fun path => do
      match app.onUrlChange with
      | some f => dispatchMsg (f path)
      | none   => pure ()
    localDispatch
    localDispatchStr
    snapshot := snapshotLocals
    restore  := restoreLocals
    effectDone
    portRecv
  })

end Qed
