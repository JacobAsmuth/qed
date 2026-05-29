/-
  Qed.Html — the core typed virtual DOM.

  This is the *elaboration target*: every nice surface syntax (combinators in
  `Qed.Notation`, future `deriving`/macros) ultimately produces a value of this
  type, so guarantees proven about `Html` hold no matter how prettily the app is
  written. `msg` is the application's message type; event handlers carry a `msg`
  value, so an event wired to the wrong message simply does not type-check.
-/
namespace Qed

/-- A typed attribute on a DOM node. Event handlers carry the app's `msg`. -/
inductive Attr (msg : Type) where
  /-- A CSS class. -/
  | cls (name : String)
  /-- A raw `key="value"` attribute. -/
  | attr (key value : String)
  /-- A click handler producing the message `m`. -/
  | onClick (m : msg)

/-- A typed virtual-DOM node. Note this inductive is *total*: there is no
    constructor for "failed render", so a well-typed `view` cannot crash. -/
inductive Html (msg : Type) where
  /-- A text node. -/
  | text (content : String)
  /-- An element: a tag, its attributes, and its children. -/
  | element (tag : String) (attrs : List (Attr msg)) (children : List (Html msg))

instance : Inhabited (Attr msg) := ⟨.cls ""⟩
instance : Inhabited (Html msg) := ⟨.text ""⟩

/-- Remap the message type of an attribute (functoriality in `msg`). -/
def Attr.map (f : α → β) : Attr α → Attr β
  | .cls n       => .cls n
  | .attr k v    => .attr k v
  | .onClick m   => .onClick (f m)

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

/-- Render an attribute to static HTML. Event handlers have no static form. -/
def Attr.renderToString : Attr msg → String
  | .cls n     => s!" class=\"{n}\""
  | .attr k v  => s!" {k}=\"{v}\""
  | .onClick _ => ""

mutual
  /-- Render a node to a static HTML string. Used for native-side sanity checks
      (and server-side rendering later) without a browser. Total by construction. -/
  def Html.renderToString : Html msg → String
    | .text s => s
    | .element tag attrs children =>
        let a := String.join (attrs.map Attr.renderToString)
        s!"<{tag}{a}>{Html.renderChildren children}</{tag}>"
  /-- Helper: concatenate rendered children. -/
  def Html.renderChildren : List (Html msg) → String
    | []      => ""
    | c :: cs => Html.renderToString c ++ Html.renderChildren cs
end

end Qed
