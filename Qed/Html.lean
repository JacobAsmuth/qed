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

/-- Trim leading/trailing whitespace, returning a `String`. A drop-in for `String.trim`, which is
    deprecated in Lean ≥ 4.30 in favour of the `String.Slice`-returning `trimAscii`; this keeps the
    `String → String` shape and the original Unicode-whitespace semantics, built only from
    primitives the IR→JS transpiler already handles (no `String.Slice` in app bundles). -/
def String.trimmed (s : String) : String :=
  String.ofList (((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)

namespace Qed

/-- A typed attribute on a DOM node. Event handlers carry the app's `msg`. -/
inductive Attr (msg : Type) where
  /-- A CSS class. Multiple classes on one node are merged into one `class`. -/
  | cls (name : String)
  /-- A raw `key="value"` attribute. -/
  | attr (key value : String)
  /-- A boolean attribute (`disabled`, `checked`, …): present on the node *iff*
      `present`, so there is no `disabled="false"`-still-disables footgun. -/
  | flag (key : String) (present : Bool)
  /-- A reconciliation key (React/Vue `key`): identifies a child across renders so
      the diff can match a moved/reordered element to its previous node instead of
      patching positionally. Virtual-DOM-only — it never renders or touches the DOM. -/
  | key (k : String)
  /-- Listen for DOM `event`, dispatching the constant message `m`. This is the single,
      open event mechanism — `onClick`/`onSubmit`/`onBlur`/`onFocus`, and `on "mousedown"`,
      `on "wheel"`, `on "dragstart"`, … are all this; the named helpers in `Qed.Notation` are
      thin wrappers. The driver delegates by event name, so any DOM event is reachable. A
      `submit` event always `preventDefault`s, so a `<form>` is just a message source. -/
  | on (event : String) (m : msg)
  /-- Listen for DOM `event`, dispatching `decode payload`, where the host supplies the event's
      natural string payload: an input/select `value`, a checkbox's checked state as
      `"true"`/`"false"` (on `change`), or a key's name (on `keydown`/`keyup`). Backs
      `onInput`/`onCheck`/`onKeydown`/`onKeyup`, and `onValue "input"` etc. directly. -/
  | onValue (event : String) (decode : String → msg)
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
  /-- INTERNAL — the engine's value-update mechanism, never written by hand. When the `ui`
      lift decides a binding can update without a diff (a list row's text derived from the
      model), it emits this; the driver binds the node to a named slot and a value-only
      update writes it directly, no `update` re-render, no diff, no tree walk — O(bindings).
      The value is still *derived from the model*; this is just how the engine delivers it. -/
  | signalBind (name : String)
  /-- INTERNAL — the attribute counterpart of `signalBind` (emitted by the `ui` lift for a
      row's derived attribute/value). `value` is the current value, rendered into the static
      markup so SSR matches; the live driver reads the slot. Never written by hand. -/
  | signalAttr (name attr value : String)
  /-- Set the element's inner HTML *verbatim* (React's `dangerouslySetInnerHTML`): the `markup`
      string becomes the node's content, parsed by the browser, and the element's child list is
      ignored. The escape hatch for raw markup you already have as a string — an inline SVG icon,
      a sanitized rich-text snippet. Unescaped by design, so only pass markup you trust. -/
  | rawHtml (markup : String)

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
  | .flag k present => .flag k present
  | .key k        => .key k
  | .on e m       => .on e (f m)
  | .onValue e h  => .onValue e (fun s => f (h s))
  -- Only the bubble carries `msg`; the child's own view/messages live in the driver,
  -- so relabelling the parent never has to recurse into the local subtree (total).
  | .localCell k c i b => .localCell k c i (fun s => (b s).map f)
  | .signalBind name   => .signalBind name
  | .signalAttr n a v  => .signalAttr n a v
  | .rawHtml markup    => .rawHtml markup

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

/-- Prefix every signal name (`signalBind`/`signalAttr`) in a subtree. Signals are a
    process-wide name→node map, so two renders of the same template would share names and
    overwrite each other; the driver gives each fine-grained list a per-instance prefix
    (its container's node id) and applies this to its rows so instances stay disjoint. -/
def Attr.prefixSignal (pfx : String) : Attr msg → Attr msg
  | .signalBind n     => .signalBind (pfx ++ n)
  | .signalAttr n a v => .signalAttr (pfx ++ n) a v
  | other             => other

mutual
  partial def Html.prefixSignals (pfx : String) : Html msg → Html msg
    | .text s                     => .text s
    | .element tag attrs children =>
        .element tag (attrs.map (Attr.prefixSignal pfx)) (Html.prefixSignalsList pfx children)
    | .lazy key sub               => .lazy key (Html.prefixSignals pfx sub)
  partial def Html.prefixSignalsList (pfx : String) : List (Html msg) → List (Html msg)
    | []      => []
    | c :: cs => Html.prefixSignals pfx c :: Html.prefixSignalsList pfx cs
end

end Qed
