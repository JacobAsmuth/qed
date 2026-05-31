/-
  Qed.Dom — the FFI boundary to the browser DOM.

  This is the only impure, unverified surface in the framework: `@[extern]`
  declarations whose C implementations (in `runtime/qed_dom.c`) call real
  JavaScript via emscripten's `EM_JS`. Everything above this line is pure, total
  Lean.

  DOM nodes are referenced by integer handles into a JS-side table. These
  primitives are deliberately minimal — create/append/set-attr/set-text/replace —
  so the trusted mirror of `Qed.Diff.applyPatch` onto the real DOM (in
  `Qed.Driver`) is as small as possible.
-/
namespace Qed.Dom

/-- A handle to a live DOM node (an index into the JS-side node table). -/
abbrev Node := UInt32

/-- Create a detached element with the given tag. -/
@[extern "qed_dom_create_element"]
opaque createElement (tag : String) : IO Node

/-- Create a detached text node. -/
@[extern "qed_dom_create_text"]
opaque createText (content : String) : IO Node

/-- Set an attribute on an element. -/
@[extern "qed_dom_set_attribute"]
opaque setAttribute (node : Node) (key value : String) : IO Unit

/-- Remove a single attribute from an element. The driver uses this to drop a
    toggled-off boolean attribute, while leaving unchanged attributes untouched (so
    a typed input keeps its caret). -/
@[extern "qed_dom_remove_attribute"]
opaque removeAttribute (node : Node) (key : String) : IO Unit

/-- Set an input's live `value` *property* (not just the attribute), so a
    controlled field reflects the model. A no-op when already equal, which keeps
    the caret where the user left it. -/
@[extern "qed_dom_set_value"]
opaque setValue (node : Node) (value : String) : IO Unit

/-- The current local date as an ISO `YYYY-MM-DD` string (the browser's `new Date()`),
    for `Cmd.now` to parse into a `Qed.Date` and thread into the model. -/
@[extern "qed_dom_today"]
opaque today : IO String

/-- POST `body` to `url` and stream the response. The JS host reads the response
    as Server-Sent Events and calls back into Lean per data chunk (tagged
    `chunkId`) and once at end of stream (tagged `doneId`). Fire-and-forget. -/
@[extern "qed_dom_fetch_stream"]
opaque fetchStream (url body : String) (chunkId doneId : UInt32) : IO Unit

/-- Send an HTTP request (`method url` with `body`). The JS host calls back into
    Lean once the response resolves, tagged `id`, with the response text and whether
    the status was ok. Fire-and-forget. -/
@[extern "qed_dom_http_send"]
opaque httpSend (method url body : String) (id : UInt32) : IO Unit

/-- The current URL path (`window.location.pathname`), for the router to parse into
    a route at startup and on navigation. -/
@[extern "qed_dom_current_path"]
opaque currentPath : IO String

/-- Push `path` onto the browser history (`history.pushState`) without a reload. -/
@[extern "qed_dom_push_path"]
opaque pushPath (path : String) : IO Unit

/-- Append `child` as the last child of `parent`. -/
@[extern "qed_dom_append_child"]
opaque appendChild (parent child : Node) : IO Unit

/-- Replace the text content of a text node. -/
@[extern "qed_dom_set_text"]
opaque setText (node : Node) (content : String) : IO Unit

/-- Get a handle to the `index`-th child of `parent`. -/
@[extern "qed_dom_child_at"]
opaque childAt (parent : Node) (index : UInt32) : IO Node

/-- How many children `parent` currently has. The driver uses it to know how many
    trailing nodes a `drop` must remove. -/
@[extern "qed_dom_child_count"]
opaque childCount (parent : Node) : IO UInt32

/-- Remove the `index`-th child of `parent`. Removing repeatedly at the same index
    deletes a run of trailing children (each removal shifts the rest down). -/
@[extern "qed_dom_remove_child"]
opaque removeChild (parent : Node) (index : UInt32) : IO Unit

/-- Replace the `index`-th child of `parent` with `newChild`. -/
@[extern "qed_dom_replace_child"]
opaque replaceChild (parent : Node) (index : UInt32) (newChild : Node) : IO Unit

/-- Insert `child` so it becomes the `index`-th child of `parent` (before whatever
    is currently there; appended if `index` is past the end). If `child` is already
    in `parent`, the DOM moves it — preserving its identity, focus, and selection.
    Keyed reconciliation uses this to reorder reused rows. -/
@[extern "qed_dom_insert_before"]
opaque insertBefore (parent : Node) (index : UInt32) (child : Node) : IO Unit

/-- Mount `node` as the sole child of the `#app` element. -/
@[extern "qed_dom_mount_root"]
opaque mountRoot (node : Node) : IO Unit

/-- Is `node` still attached to the live document? The driver sweeps this after each
    root render to garbage-collect the state of local components whose host element
    was removed (so an unmounted `useState` cell doesn't leak, and re-mounting starts
    fresh — React's unmount-loses-state). -/
@[extern "qed_dom_is_connected"]
opaque isConnected (node : Node) : IO Bool

end Qed.Dom
