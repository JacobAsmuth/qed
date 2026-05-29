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

/-- Remove every attribute from an element. The driver clears then re-applies on
    each patch, so a dropped or toggled-off attribute actually leaves the DOM. -/
@[extern "qed_dom_clear_attributes"]
opaque clearAttributes (node : Node) : IO Unit

/-- Append `child` as the last child of `parent`. -/
@[extern "qed_dom_append_child"]
opaque appendChild (parent child : Node) : IO Unit

/-- Replace the text content of a text node. -/
@[extern "qed_dom_set_text"]
opaque setText (node : Node) (content : String) : IO Unit

/-- Get a handle to the `index`-th child of `parent`. -/
@[extern "qed_dom_child_at"]
opaque childAt (parent : Node) (index : UInt32) : IO Node

/-- Replace the `index`-th child of `parent` with `newChild`. -/
@[extern "qed_dom_replace_child"]
opaque replaceChild (parent : Node) (index : UInt32) (newChild : Node) : IO Unit

/-- Mount `node` as the sole child of the `#app` element. -/
@[extern "qed_dom_mount_root"]
opaque mountRoot (node : Node) : IO Unit

end Qed.Dom
