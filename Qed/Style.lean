import Qed.Notation

namespace Qed

structure Style where
  className : String
  raw       : String
deriving Inhabited

instance : Coe Style (Attr msg) := ⟨fun s => .cls s.className⟩

inductive Item where
  | decl (property value : String)
  | nest (selector : String) (body : List Item)
deriving Inhabited

mutual
  def Item.render : Item → String
    | .decl p v   => p ++ ": " ++ v ++ ";"
    | .nest sel b => sel ++ " { " ++ Item.renderList b ++ " }"
  def Item.renderList : List Item → String
    | []      => ""
    | [i]     => Item.render i
    | i :: is => Item.render i ++ " " ++ Item.renderList is
end

structure Len where raw : String
deriving Inhabited
instance : Coe String Len := ⟨Len.mk⟩
instance : ToString Len := ⟨Len.raw⟩

def px  (n : Int) : Len := ⟨toString n ++ "px"⟩
def rem (n : Int) : Len := ⟨toString n ++ "rem"⟩
def em  (n : Int) : Len := ⟨toString n ++ "em"⟩
def pct (n : Int) : Len := ⟨toString n ++ "%"⟩
def vh  (n : Int) : Len := ⟨toString n ++ "vh"⟩
def vw  (n : Int) : Len := ⟨toString n ++ "vw"⟩
def fr  (n : Int) : Len := ⟨toString n ++ "fr"⟩

structure Color where raw : String
deriving Inhabited
instance : Coe String Color := ⟨Color.mk⟩
instance : ToString Color := ⟨Color.raw⟩

def hex  (s : String) : Color := ⟨"#" ++ s⟩
def rgb  (r g b : Nat) : Color := ⟨s!"rgb({r}, {g}, {b})"⟩
def rgba (r g b : Nat) (a : String) : Color := ⟨s!"rgba({r}, {g}, {b}, {a})"⟩

structure Token where name : String
deriving Inhabited
def token (name : String) : Token := ⟨name⟩
instance : ToString Token := ⟨fun t => s!"var(--{t.name})"⟩
instance : Coe Token Len   := ⟨fun t => ⟨s!"var(--{t.name})"⟩⟩
instance : Coe Token Color := ⟨fun t => ⟨s!"var(--{t.name})"⟩⟩

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

inductive BorderStyle | solid | dashed | dotted | double | none deriving Inhabited
def BorderStyle.css : BorderStyle → String
  | .solid => "solid" | .dashed => "dashed" | .dotted => "dotted" | .double => "double" | .none => "none"

def width         (l : Len) : Item := .decl "width" l.raw
def height        (l : Len) : Item := .decl "height" l.raw
def minWidth      (l : Len) : Item := .decl "min-width" l.raw
def maxWidth      (l : Len) : Item := .decl "max-width" l.raw
def minHeight     (l : Len) : Item := .decl "min-height" l.raw
def maxHeight     (l : Len) : Item := .decl "max-height" l.raw
def padding       (l : Len) : Item := .decl "padding" l.raw
def paddingX      (l : Len) : Item := .decl "padding-inline" l.raw
def paddingY      (l : Len) : Item := .decl "padding-block" l.raw
def paddingTop    (l : Len) : Item := .decl "padding-top" l.raw
def paddingRight  (l : Len) : Item := .decl "padding-right" l.raw
def paddingBottom (l : Len) : Item := .decl "padding-bottom" l.raw
def paddingLeft   (l : Len) : Item := .decl "padding-left" l.raw
def margin        (l : Len) : Item := .decl "margin" l.raw
def marginX       (l : Len) : Item := .decl "margin-inline" l.raw
def marginY       (l : Len) : Item := .decl "margin-block" l.raw
def marginTop     (l : Len) : Item := .decl "margin-top" l.raw
def marginRight   (l : Len) : Item := .decl "margin-right" l.raw
def marginBottom  (l : Len) : Item := .decl "margin-bottom" l.raw
def marginLeft    (l : Len) : Item := .decl "margin-left" l.raw
def top           (l : Len) : Item := .decl "top" l.raw
def right         (l : Len) : Item := .decl "right" l.raw
def bottom        (l : Len) : Item := .decl "bottom" l.raw
def left          (l : Len) : Item := .decl "left" l.raw
def gap           (l : Len) : Item := .decl "gap" l.raw
def fontSize      (l : Len) : Item := .decl "font-size" l.raw
def radius        (l : Len) : Item := .decl "border-radius" l.raw
def borderRadius  (l : Len) : Item := .decl "border-radius" l.raw
def borderWidth   (l : Len) : Item := .decl "border-width" l.raw
def letterSpacing (l : Len) : Item := .decl "letter-spacing" l.raw

def color           (c : Color) : Item := .decl "color" c.raw
def backgroundColor (c : Color) : Item := .decl "background-color" c.raw
def borderColor     (c : Color) : Item := .decl "border-color" c.raw
def fill            (c : Color) : Item := .decl "fill" c.raw
def stroke          (c : Color) : Item := .decl "stroke" c.raw

def display        (d : Display)       : Item := .decl "display" d.css
def position       (p : Position)      : Item := .decl "position" p.css
def textAlign      (t : TextAlign)     : Item := .decl "text-align" t.css
def flexDirection  (f : FlexDirection) : Item := .decl "flex-direction" f.css
def justifyContent (j : Justify)       : Item := .decl "justify-content" j.css
def alignItems     (a : Align)         : Item := .decl "align-items" a.css

-- Coercing `BorderStyle → Color → Item` with an empty color sentinel allows `border "1px solid #ddd"` alongside `border (px 1) .solid c`.
private def mkBorder (prop : String) (w : Len) (s : BorderStyle) (c : Color) : Item :=
  .decl prop (if c.raw.isEmpty then w.raw else s!"{w.raw} {s.css} {c.raw}")
instance : Coe (BorderStyle → Color → Item) Item := ⟨fun f => f .solid ⟨""⟩⟩
def border       := mkBorder "border"
def borderTop    := mkBorder "border-top"
def borderRight  := mkBorder "border-right"
def borderBottom := mkBorder "border-bottom"
def borderLeft   := mkBorder "border-left"

def background          (v : String) : Item := .decl "background" v
def boxShadow           (v : String) : Item := .decl "box-shadow" v
def transform           (v : String) : Item := .decl "transform" v
def transition          (v : String) : Item := .decl "transition" v
def font                (v : String) : Item := .decl "font" v
def fontFamily          (v : String) : Item := .decl "font-family" v
def fontWeight          (v : String) : Item := .decl "font-weight" v
def lineHeight          (v : String) : Item := .decl "line-height" v
def textDecoration      (v : String) : Item := .decl "text-decoration" v
def cursor              (v : String) : Item := .decl "cursor" v
def overflow            (v : String) : Item := .decl "overflow" v
def opacity             (v : String) : Item := .decl "opacity" v
def zIndex              (v : String) : Item := .decl "z-index" v
def flex                (v : String) : Item := .decl "flex" v
def gridTemplateColumns (v : String) : Item := .decl "grid-template-columns" v
def whiteSpace          (v : String) : Item := .decl "white-space" v

def prop (name value : String) : Item := .decl name value
def nest (selector : String) (body : List Item) : Item := .nest selector body
def media (query : String) (body : List Item) : Item := .nest ("@media " ++ query) body
def screenMax (w : Len) (body : List Item) : Item := media s!"(max-width: {w.raw})" body
def screenMin (w : Len) (body : List Item) : Item := media s!"(min-width: {w.raw})" body
def Token.set (t : Token) (value : String) : Item := .decl ("--" ++ t.name) value

class CssBody (α : Type) where toRaw : α → String
instance : CssBody String := ⟨id⟩
instance : CssBody (List Item) := ⟨Item.renderList⟩

def css {α : Type} [CssBody α] (body : α) : Style :=
  let raw := CssBody.toRaw body
  { className := s!"qed-{String.hash raw}", raw := raw }

private def Style.rule (s : Style) : String := "." ++ s.className ++ " { " ++ s.raw ++ " }"

def renderTheme (tokens : List Item) : String :=
  let (decls, rules) := tokens.partition (fun | .decl _ _ => true | .nest _ _ => false)
  let root := if decls.isEmpty then [] else [":root { " ++ Item.renderList decls ++ " }"]
  let resets := rules.map fun | .nest s b => s!":where({s}) \{ {Item.renderList b} }" | i => i.render
  String.intercalate "\n" (root ++ resets)

@[inline] def theme (tokens : List Item) : Html msg :=
  el "style" [] [Html.text (renderTheme tokens)]

def renderStyleSheet (styles : List Style) : String :=
  let seen := (styles.foldl
    (fun acc s => if acc.any (·.className == s.className) then acc else s :: acc) []).reverse
  String.intercalate "\n" (seen.map Style.rule)

@[inline] def styleSheet (styles : List Style) : Html msg :=
  el "style" [] [Html.text (renderStyleSheet styles)]

end Qed
