/-
  Qed.Style — scoped, collision-free styles co-located with the code that uses them.

  A `Style` is a hashed class name plus a CSS body. You define it next to the component,
  reference it on an element like any attribute, and emit one stylesheet:

      def card : Style := css [
        padding (rem 1), border "1px solid #ddd", radius (px 8),
        nest "&:hover" [ transform "translateY(-2px)" ] ]

      div [card] [ … ]                 -- `card` coerces to its class attribute
      styleSheet [card, button, …]      -- once in your view: emits one <style>

  The class name is a hash of the CSS, so identical styles dedup and names can never
  collide across modules. A `&` in the body refers to the class via native CSS nesting
  (`.qed-… { &:hover { … } }`). Because a style is referenced by its Lean *binding*
  (`card`), a typo is a compile error — not a silently-dead class string.

  The body is a `List Item`: each property (`padding`, `color`, `display`, …) is a typed
  function, so a misspelled property name does not compile. Values carry a small typed
  vocabulary (`px`/`rem`/`pct`, `hex`/`rgb`, the `Display`/`Position`/… enums), and a raw
  `String` coerces in anywhere for compound values (`"1px solid #ddd"`, `calc(…)`). `css`
  also still accepts a raw `String` body, unchanged.
-/
import Qed.Notation

namespace Qed

/-- A scoped style: a generated class name and the CSS declaration body it stands for. -/
structure Style where
  className : String
  raw       : String
deriving Inhabited

/-- A style is usable wherever an attribute is — it applies its class. -/
instance : Coe Style (Attr msg) := ⟨fun s => .cls s.className⟩

/-! ### The typed declaration body

One CSS body is a `List Item`. An `Item` is either a declaration (`property: value`) or a
nested rule (`&:hover { … }`, via `on`). Typed property functions build the declarations, so
a misspelled property is an unknown identifier. -/

/-- One entry in a style body: a `property: value` declaration, or a nested rule. -/
inductive Item where
  | decl (property value : String)
  | nest (selector : String) (body : List Item)
deriving Inhabited

mutual
  /-- Render one item: `prop: value;`, or `selector { … }` for a nested rule. -/
  def Item.render : Item → String
    | .decl p v   => p ++ ": " ++ v ++ ";"
    | .nest sel b => sel ++ " { " ++ Item.renderList b ++ " }"
  /-- Render a body (space-joined; declarations already carry their `;`). -/
  def Item.renderList : List Item → String
    | []      => ""
    | [i]     => Item.render i
    | i :: is => Item.render i ++ " " ++ Item.renderList is
end

/-! ### Typed values

`Len` and `Color` wrap a CSS value string with typed constructors; a raw `String` coerces in
for anything not modelled (compound values, `calc(…)`, custom properties, named colors). -/

/-- A length / numeric CSS value: `px 8`, `rem 1`, `pct 50`, or a coerced raw `String`. -/
structure Len where raw : String
deriving Inhabited
instance : Coe String Len := ⟨Len.mk⟩

def px  (n : Int) : Len := ⟨toString n ++ "px"⟩
def rem (n : Int) : Len := ⟨toString n ++ "rem"⟩
def em  (n : Int) : Len := ⟨toString n ++ "em"⟩
def pct (n : Int) : Len := ⟨toString n ++ "%"⟩
def vh  (n : Int) : Len := ⟨toString n ++ "vh"⟩
def vw  (n : Int) : Len := ⟨toString n ++ "vw"⟩
def fr  (n : Int) : Len := ⟨toString n ++ "fr"⟩

/-- A CSS color: `hex "06c"`, `rgb 0 102 204`, or a coerced raw `String` (e.g. `"red"`). -/
structure Color where raw : String
deriving Inhabited
instance : Coe String Color := ⟨Color.mk⟩

def hex  (s : String) : Color := ⟨"#" ++ s⟩
def rgb  (r g b : Nat) : Color := ⟨s!"rgb({r}, {g}, {b})"⟩
def rgba (r g b : Nat) (a : String) : Color := ⟨s!"rgba({r}, {g}, {b}, {a})"⟩

/-- A design token: a typed handle to a CSS custom property (`--name`). Define it once as a Lean
    binding (`def surface := token "surface"`) so a misspelled reference is a compile error; it
    coerces into a `Len` or a `Color` as `var(--name)`. Set its value with `Token.set` inside
    `theme`. -/
structure Token where name : String
deriving Inhabited
def token (name : String) : Token := ⟨name⟩
instance : Coe Token Len   := ⟨fun t => ⟨s!"var(--{t.name})"⟩⟩
instance : Coe Token Color := ⟨fun t => ⟨s!"var(--{t.name})"⟩⟩

/-! ### Keyword enums — for the properties whose values are a fixed vocabulary. -/

inductive Display | flex | grid | block | inline | inlineBlock | none | contents deriving Inhabited
def Display.css : Display → String
  | .flex => "flex" | .grid => "grid" | .block => "block" | .inline => "inline"
  | .inlineBlock => "inline-block" | .none => "none" | .contents => "contents"

inductive Position | static | relative | absolute | fixed | sticky deriving Inhabited
def Position.css : Position → String
  | .static => "static" | .relative => "relative" | .absolute => "absolute"
  | .fixed => "fixed" | .sticky => "sticky"

inductive TextAlign | left | right | center | justify deriving Inhabited
def TextAlign.css : TextAlign → String
  | .left => "left" | .right => "right" | .center => "center" | .justify => "justify"

inductive FlexDirection | row | column | rowReverse | columnReverse deriving Inhabited
def FlexDirection.css : FlexDirection → String
  | .row => "row" | .column => "column" | .rowReverse => "row-reverse" | .columnReverse => "column-reverse"

inductive Justify | start | «end» | center | spaceBetween | spaceAround | spaceEvenly deriving Inhabited
def Justify.css : Justify → String
  | .start => "flex-start" | .«end» => "flex-end" | .center => "center"
  | .spaceBetween => "space-between" | .spaceAround => "space-around" | .spaceEvenly => "space-evenly"

inductive Align | start | «end» | center | stretch | baseline deriving Inhabited
def Align.css : Align → String
  | .start => "flex-start" | .«end» => "flex-end" | .center => "center"
  | .stretch => "stretch" | .baseline => "baseline"

/-! ### Properties — each one a typed function, so a typo will not compile. -/

-- Box & sizing (lengths)
def width     (l : Len) : Item := .decl "width" l.raw
def height    (l : Len) : Item := .decl "height" l.raw
def minWidth  (l : Len) : Item := .decl "min-width" l.raw
def maxWidth  (l : Len) : Item := .decl "max-width" l.raw
def minHeight (l : Len) : Item := .decl "min-height" l.raw
def maxHeight (l : Len) : Item := .decl "max-height" l.raw
def padding   (l : Len) : Item := .decl "padding" l.raw
def margin    (l : Len) : Item := .decl "margin" l.raw
def top       (l : Len) : Item := .decl "top" l.raw
def right     (l : Len) : Item := .decl "right" l.raw
def bottom    (l : Len) : Item := .decl "bottom" l.raw
def left      (l : Len) : Item := .decl "left" l.raw
def gap       (l : Len) : Item := .decl "gap" l.raw
def fontSize  (l : Len) : Item := .decl "font-size" l.raw
def radius    (l : Len) : Item := .decl "border-radius" l.raw
def borderRadius (l : Len) : Item := .decl "border-radius" l.raw
def borderWidth  (l : Len) : Item := .decl "border-width" l.raw
def letterSpacing (l : Len) : Item := .decl "letter-spacing" l.raw

-- Color (incl. the SVG presentation properties `fill`/`stroke`)
def color           (c : Color) : Item := .decl "color" c.raw
def backgroundColor (c : Color) : Item := .decl "background-color" c.raw
def borderColor     (c : Color) : Item := .decl "border-color" c.raw
def fill            (c : Color) : Item := .decl "fill" c.raw
def stroke          (c : Color) : Item := .decl "stroke" c.raw

-- Keyword properties (enums)
def display        (d : Display)       : Item := .decl "display" d.css
def position       (p : Position)      : Item := .decl "position" p.css
def textAlign      (t : TextAlign)     : Item := .decl "text-align" t.css
def flexDirection  (f : FlexDirection) : Item := .decl "flex-direction" f.css
def justifyContent (j : Justify)       : Item := .decl "justify-content" j.css
def alignItems     (a : Align)         : Item := .decl "align-items" a.css

-- Freeform (compound / open-ended values: keep the String)
def background    (v : String) : Item := .decl "background" v
def border        (v : String) : Item := .decl "border" v
def boxShadow     (v : String) : Item := .decl "box-shadow" v
def transform     (v : String) : Item := .decl "transform" v
def transition    (v : String) : Item := .decl "transition" v
def font          (v : String) : Item := .decl "font" v
def fontFamily    (v : String) : Item := .decl "font-family" v
def fontWeight    (v : String) : Item := .decl "font-weight" v
def lineHeight    (v : String) : Item := .decl "line-height" v
def textDecoration (v : String) : Item := .decl "text-decoration" v
def cursor        (v : String) : Item := .decl "cursor" v
def overflow      (v : String) : Item := .decl "overflow" v
def opacity       (v : String) : Item := .decl "opacity" v
def zIndex        (v : String) : Item := .decl "z-index" v
def flex          (v : String) : Item := .decl "flex" v
def gridTemplateColumns (v : String) : Item := .decl "grid-template-columns" v
def whiteSpace    (v : String) : Item := .decl "white-space" v

/-- An escape hatch for any property not given a typed helper: `prop "aspect-ratio" "16 / 9"`. -/
def prop (name value : String) : Item := .decl name value

/-- A nested rule inside a style — pseudo-classes, descendants, media-ish selectors:
    `nest "&:hover" [ … ]`, `nest "& > li" [ … ]`. The `&` is the style's own class. -/
def nest (selector : String) (body : List Item) : Item := .nest selector body

/-- A responsive block, via native CSS nesting: `media "(max-width: 768px)" [ … ]` renders
    `@media (max-width: 768px) { … }` scoped to the class. Use `screenMax`/`screenMin` for the
    common width breakpoints. -/
def media (query : String) (body : List Item) : Item := .nest ("@media " ++ query) body
def screenMax (w : Len) (body : List Item) : Item := media s!"(max-width: {w.raw})" body
def screenMin (w : Len) (body : List Item) : Item := media s!"(min-width: {w.raw})" body

/-- Bind a token to a value inside a `theme` block: `surface.set "#0b0b0b"`, `space.set "1rem"`. -/
def Token.set (t : Token) (value : String) : Item := .decl ("--" ++ t.name) value

/-! ### Building a `Style` -/

/-- A CSS body `css` accepts: a typed `List Item` (the front door) or a raw `String` (the
    original, unchanged — same hash, so existing styles are untouched). -/
class CssBody (α : Type) where toRaw : α → String
instance : CssBody String := ⟨id⟩
instance : CssBody (List Item) := ⟨Item.renderList⟩

/-- Define a scoped style from a CSS body. (Named `css` since `style` is the inline-`style`
    attribute helper in `Qed.Notation`.) The class name is a hash of the rendered CSS. -/
def css {α : Type} [CssBody α] (body : α) : Style :=
  let raw := CssBody.toRaw body
  { className := s!"qed-{String.hash raw}", raw := raw }

/-- One CSS rule: `.qed-… { <body> }` (the body keeps any `&`-nesting). -/
private def Style.rule (s : Style) : String := "." ++ s.className ++ " { " ++ s.raw ++ " }"

/-- Emit design tokens as a `:root { … }` stylesheet from a list of `Token.set`s. Drop this once
    near your view root (alongside `styleSheet`); the tokens are then visible to every style. -/
def theme (tokens : List Item) : Html msg :=
  el "style" [] [Html.text (":root { " ++ Item.renderList tokens ++ " }")]

/-- Collect styles into one `<style>` element, deduping by class name. Drop this once in
    your view (e.g. at the top of the root element's children). -/
def styleSheet (styles : List Style) : Html msg :=
  let seen := styles.foldl
    (fun acc s => if acc.any (·.className == s.className) then acc else acc ++ [s]) []
  el "style" [] [Html.text (String.intercalate "\n" (seen.map Style.rule))]

end Qed
