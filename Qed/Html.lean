/-
  Qed.Html — the core typed virtual DOM.

  This is the *elaboration target*: every nice surface syntax (combinators in
  `Qed.Notation`, the `jsonStruct`/`form` macros, …) ultimately produces a value of
  this type, so guarantees proven about `Html` hold no matter how prettily the app
  is written. `msg` is the application's message type; event handlers carry a `msg`
  value, so an event wired to the wrong message simply does not type-check.

  There is exactly one renderer (`Html.render`, in `Qed.Runtime`); it escapes model
  data. Rendering lives there because it shares the event-id table the driver needs.
-/
namespace Qed

/-- A typed attribute on a DOM node. Event handlers carry the app's `msg`. -/
inductive Attr (msg : Type) where
  /-- A CSS class. Multiple classes on one node are merged into one `class`. -/
  | cls (name : String)
  /-- A raw `key="value"` attribute. -/
  | attr (key value : String)
  /-- A boolean attribute (`disabled`, `checked`, …): present on the node *iff*
      `on`, so there is no `disabled="false"`-still-disables footgun. -/
  | flag (key : String) (on : Bool)
  /-- A reconciliation key (React/Vue `key`): identifies a child across renders so
      the diff can match a moved/reordered element to its previous node instead of
      patching positionally. Virtual-DOM-only — it never renders or touches the DOM. -/
  | key (k : String)
  /-- A click handler producing the message `m`. -/
  | onClick (m : msg)
  /-- An input handler: produces a message from the field's current value, fired
      on every edit. Also serves `<select>`/radio change (both fire `input`). -/
  | onInput (handler : String → msg)
  /-- A checkbox handler: produces a message from the box's checked state. -/
  | onCheck (handler : Bool → msg)
  /-- A key handler: produces a message from the pressed key's name (`"Enter"`,
      `"Escape"`, `"a"`, …), fired on `keydown`. -/
  | onKeydown (handler : String → msg)
  /-- A key handler fired on `keyup`. -/
  | onKeyup (handler : String → msg)
  /-- A form-submit handler. The default page reload is always suppressed
      (`preventDefault`), so a `<form>` becomes an ordinary message source. -/
  | onSubmit (m : msg)
  /-- A focus-lost handler (`blur`). -/
  | onBlur (m : msg)
  /-- A focus-gained handler (`focus`). -/
  | onFocus (m : msg)
  /-- Mark this element as a locally-stateful child instance (React `useState`, but
      the cell is addressed by an explicit key rather than call order). `key` is the
      instance's identity in the driver's state store; `component` names a registered
      local component whose `view`/`update` live in the driver — deliberately *off*
      the pure virtual DOM, so `Html.map`/`diff` never recurse into it and stay total
      and proof-free. `init?` optionally seeds *this* instance's state from parent data
      (the `useState(propValue)` case), overriding the component's registered default.
      `bubble` maps the child's serialized *output* to an optional parent message: the
      type-safe channel by which a self-contained child event can still reach the root
      `update`. The host renders empty; the driver fills its children from local state. -/
  | localCell (key component : String) (init? : Option String) (bubble : String → Option msg)
  /-- Bind this element's text content to a named *signal* (fine-grained reactivity). The
      signal's value lives in the driver, not the model; `Cmd.setSignal name v` (or
      `window.qed.setSignal(name, v)` from JS) updates *only* the bound elements — no
      `update`, no diff, no tree walk — so a high-frequency or external value (a clock, a
      socket feed) updates in O(bindings). The element's `Html` children are owned by the
      signal, so leave them empty. -/
  | signalBind (name : String)
  /-- Bind this element's `attr` attribute to a named signal (the attribute counterpart of
      `signalBind`): `setSignal name v` sets `attr="v"` on the bound element directly. The
      `value` is the current value, rendered into the static markup so SSR matches; the
      live driver ignores it and reads the signal store. Used by `forEach` so a row's
      dynamic class/value updates fine-grained, no diff. -/
  | signalAttr (name attr value : String)

/-- A typed virtual-DOM node. Note this inductive is *total*: there is no
    constructor for "failed render", so a well-typed `view` cannot crash. -/
inductive Html (msg : Type) where
  /-- A text node. -/
  | text (content : String)
  /-- An element: a tag, its attributes, and its children. -/
  | element (tag : String) (attrs : List (Attr msg)) (children : List (Html msg))
  /-- A memoized subtree (`shouldComponentUpdate`/`useMemo` as data): `sub` is the
      content, `key` summarizes the inputs it was built from. When the key is unchanged
      since the last render the diff skips it — neither re-diffing `sub` nor touching its
      DOM — on the promise that *equal key ⇒ equal subtree*. The view still builds `sub`
      (that cost is the cheap part); the saving is the diff and the DOM patch. -/
  | lazy (key : String) (sub : Html msg)

instance : Inhabited (Attr msg) := ⟨.cls ""⟩
instance : Inhabited (Html msg) := ⟨.text ""⟩

/-- A bare string is a text node, so children can be written `["hi", node, …]`. -/
instance : Coe String (Html msg) := ⟨.text⟩
/-- …and a lone string is a one-element child list, so `button [..] "Save"` works. -/
instance : Coe String (List (Html msg)) := ⟨([·])⟩
/-- Numbers render as their decimal text, so a model field goes straight into a
    child list — `span [..] [count]`, no `toString`. -/
instance : Coe Nat (Html msg) := ⟨fun n => .text (toString n)⟩
instance : Coe Int (Html msg) := ⟨fun n => .text (toString n)⟩

/-- Remap the message type of an attribute (functoriality in `msg`). -/
def Attr.map (f : α → β) : Attr α → Attr β
  | .cls n        => .cls n
  | .attr k v     => .attr k v
  | .flag k on    => .flag k on
  | .key k        => .key k
  | .onClick m    => .onClick (f m)
  | .onInput h    => .onInput (fun s => f (h s))
  | .onCheck h    => .onCheck (fun b => f (h b))
  | .onKeydown h  => .onKeydown (fun k => f (h k))
  | .onKeyup h    => .onKeyup (fun k => f (h k))
  | .onSubmit m   => .onSubmit (f m)
  | .onBlur m     => .onBlur (f m)
  | .onFocus m    => .onFocus (f m)
  -- Only the bubble carries `msg`; the child's own view/messages live in the driver,
  -- so relabelling the parent never has to recurse into the local subtree (total).
  | .localCell k c i b => .localCell k c i (fun s => (b s).map f)
  | .signalBind name   => .signalBind name
  | .signalAttr n a v  => .signalAttr n a v

mutual
  /-- Remap the message type of a whole tree — the basis of component
      composition: a child component emitting `α` is lifted into a parent's `β`. -/
  def Html.map (f : α → β) : Html α → Html β
    | .text s                    => .text s
    | .element tag attrs children =>
        .element tag (attrs.map (Attr.map f)) (Html.mapChildren f children)
    | .lazy key sub              => .lazy key (Html.map f sub)
  /-- Helper: map over a list of children (mutual recursion gives termination). -/
  def Html.mapChildren (f : α → β) : List (Html α) → List (Html β)
    | []      => []
    | c :: cs => Html.map f c :: Html.mapChildren f cs
end

end Qed
