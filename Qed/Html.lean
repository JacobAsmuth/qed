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
  /-- A click handler producing the message `m`. -/
  | onClick (m : msg)
  /-- An input handler: produces a message from the field's current value, fired
      on every edit. Also serves `<select>`/radio change (both fire `input`). -/
  | onInput (handler : String → msg)
  /-- A checkbox handler: produces a message from the box's checked state. -/
  | onCheck (handler : Bool → msg)

/-- A typed virtual-DOM node. Note this inductive is *total*: there is no
    constructor for "failed render", so a well-typed `view` cannot crash. -/
inductive Html (msg : Type) where
  /-- A text node. -/
  | text (content : String)
  /-- An element: a tag, its attributes, and its children. -/
  | element (tag : String) (attrs : List (Attr msg)) (children : List (Html msg))

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
  | .onClick m    => .onClick (f m)
  | .onInput h    => .onInput (fun s => f (h s))
  | .onCheck h    => .onCheck (fun b => f (h b))

mutual
  /-- Remap the message type of a whole tree — the basis of component
      composition: a child component emitting `α` is lifted into a parent's `β`. -/
  def Html.map (f : α → β) : Html α → Html β
    | .text s                    => .text s
    | .element tag attrs children =>
        .element tag (attrs.map (Attr.map f)) (Html.mapChildren f children)
  /-- Helper: map over a list of children (mutual recursion gives termination). -/
  def Html.mapChildren (f : α → β) : List (Html α) → List (Html β)
    | []      => []
    | c :: cs => Html.map f c :: Html.mapChildren f cs
end

end Qed
