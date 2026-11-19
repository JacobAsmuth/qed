import Qed.Html

namespace Qed

/-! ## CSS Sanitization Helpers -/

@[inline] def isSafeCssAtomChar (c : Char) : Bool :=
  c.toNat ≥ 32 && c.toNat != 127 &&
  c != '{' && c != '}' && c != ';' && c != '<' && c != '>' && c != '\\'

@[inline] def isSafeCssSelectorChar (c : Char) : Bool :=
  c.toNat ≥ 32 && c.toNat != 127 &&
  c != '{' && c != '}' && c != ';' && c != '<' && c != '\\'

@[inline] def isSafeInlineCssChar (c : Char) : Bool :=
  isSafeCssAtomChar c && c != '"' && c != '\''

@[inline] def isSafeCssIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_'

def hasCommentOpenLoop (afterSlash : Bool) : List Char → Bool
  | []      => false
  | c :: cs => (afterSlash && c == '*') || hasCommentOpenLoop (c == '/') cs

def hasCommentOpen (cs : List Char) : Bool := hasCommentOpenLoop false cs

def stripCommentOpenLoop (afterSlash : Bool) : List Char → List Char
  | []      => []
  | c :: cs =>
      if afterSlash && c == '*' then stripCommentOpenLoop true cs
      else c :: stripCommentOpenLoop (c == '/') cs

def stripCommentOpen (cs : List Char) : List Char := stripCommentOpenLoop false cs

def sanitizeWith (p : Char → Bool) (s : String) : String :=
  let cs := s.toList
  if cs.all p then s
  else String.ofList (cs.filter p)

def sanitizeCssWith (p : Char → Bool) (s : String) : String :=
  let s1 := sanitizeWith p s
  let cs := s1.toList
  if hasCommentOpen cs then String.ofList (stripCommentOpen cs) else s1

def sanitizeCssAtom (s : String) : String := sanitizeCssWith isSafeCssAtomChar s

def sanitizeCssSelector (s : String) : String := sanitizeCssWith isSafeCssSelectorChar s

def sanitizeInlineCssAtom (s : String) : String := sanitizeCssWith isSafeInlineCssChar s

def sanitizeCssIdent (s : String) : String := sanitizeWith isSafeCssIdentChar s

/-! ## CSS AST (`Item`) & Rendering -/

inductive Item where
  | decl (property value : String)
  | nest (selector : String) (body : List Item)
deriving Inhabited

mutual
  def Item.render : Item → String
    | .decl p v   => sanitizeCssAtom p ++ ": " ++ sanitizeCssAtom v ++ ";"
    | .nest sel b => sanitizeCssSelector sel ++ " { " ++ Item.renderList b ++ " }"
  def Item.renderList : List Item → String
    | []      => ""
    | [i]     => Item.render i
    | i :: is => Item.render i ++ " " ++ Item.renderList is
end

/-! ## Token Reference Extraction & Deterministic Merging (Option A `extends`) -/

private def takeVarName : List Char → List Char → List String
  | acc, [] => if acc.isEmpty then [] else [String.ofList acc.reverse]
  | acc, c :: cs =>
      if c == ')' || c == ',' || c.isWhitespace then
        if acc.isEmpty then extractVarNamesLoop cs
        else String.ofList acc.reverse :: extractVarNamesLoop cs
      else
        takeVarName (c :: acc) cs
where
  extractVarNamesLoop : List Char → List String
    | [] => []
    | 'v' :: 'a' :: 'r' :: '(' :: '-' :: '-' :: rest => takeVarName [] rest
    | _ :: rest => extractVarNamesLoop rest

def extractVarNames (s : String) : List String :=
  takeVarName.extractVarNamesLoop s.toList

private def dedupStrings (xs : List String) : List String :=
  (xs.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).reverse

mutual
  def Item.collectTokens : Item → List String
    | .decl _ v   => extractVarNames v
    | .nest _ b   => Item.collectTokensList b
  def Item.collectTokensList : List Item → List String
    | []      => []
    | i :: is => Item.collectTokens i ++ Item.collectTokensList is
end

def collectItemTokens (items : List Item) : List String :=
  dedupStrings (Item.collectTokensList items)

private def isAtRuleSelector (sel : String) : Bool :=
  let t := sel.trimmed
  t.startsWith "@"

private def insertOrReplaceDecl (prop val : String) : List Item → List Item
  | [] => [.decl prop val]
  | .decl p v :: rest =>
      if p == prop then insertOrReplaceDecl prop val rest
      else .decl p v :: insertOrReplaceDecl prop val rest
  | other :: rest => other :: insertOrReplaceDecl prop val rest

mutual
  def Item.mergeOne (base : List Item) : Item → List Item
    | .decl p v => insertOrReplaceDecl p v base
    | .nest sel body => Item.mergeNest sel body base

  def Item.mergeNest (sel : String) (body : List Item) : List Item → List Item
    | [] => [.nest sel body]
    | .nest s b :: rest =>
        if s == sel then .nest s (Item.mergeItems b body) :: rest
        else .nest s b :: Item.mergeNest sel body rest
    | other :: rest => other :: Item.mergeNest sel body rest

  def Item.mergeItems : List Item → List Item → List Item
    | base, []      => base
    | base, i :: is => Item.mergeItems (Item.mergeOne base i) is
end

/-! ## Typed CSS Values: Numbers, Lengths, Time, Angle, Colors -/

structure CssNum where raw : String deriving Inhabited, BEq, Repr

namespace CssNum
private def ofMantissaExp (m e : Nat) : String :=
  if e == 0 then toString m else
  let ds := (toString m).toList
  let ps := List.replicate (e + 1 - ds.length) '0' ++ ds
  let fp := ((ps.drop (ps.length - e)).reverse.dropWhile (· == '0')).reverse
  String.ofList (ps.take (ps.length - e)) ++ if fp.isEmpty then "" else "." ++ String.ofList fp

instance (n : Nat) : OfNat CssNum n := ⟨⟨toString n⟩⟩
instance : Coe Nat CssNum    := ⟨(⟨toString ·⟩)⟩
instance : Coe Int CssNum    := ⟨(⟨toString ·⟩)⟩
instance : ToString CssNum   := ⟨CssNum.raw⟩
instance : Neg CssNum        := ⟨fun x => ⟨if x.raw.startsWith "-" || x.raw == "0" then x.raw else "-" ++ x.raw⟩⟩
instance : OfScientific CssNum := ⟨fun m neg e => ⟨if neg then ofMantissaExp m e else toString (m * 10 ^ e)⟩⟩
end CssNum

structure Len where raw : String
deriving Inhabited, BEq, Repr
instance : OfNat Len 0 := ⟨⟨"0"⟩⟩
instance : ToString Len := ⟨Len.raw⟩
def Len.auto       : Len := ⟨"auto"⟩
def Len.none       : Len := ⟨"none"⟩
def Len.fitContent : Len := ⟨"fit-content"⟩
def Len.minContent : Len := ⟨"min-content"⟩
def Len.maxContent : Len := ⟨"max-content"⟩

def px   (n : CssNum) : Len := ⟨n.raw ++ "px"⟩
def rem  (n : CssNum) : Len := ⟨n.raw ++ "rem"⟩
def em   (n : CssNum) : Len := ⟨n.raw ++ "em"⟩
def pct  (n : CssNum) : Len := ⟨n.raw ++ "%"⟩
def vh   (n : CssNum) : Len := ⟨n.raw ++ "vh"⟩
def vw   (n : CssNum) : Len := ⟨n.raw ++ "vw"⟩
def dvh  (n : CssNum) : Len := ⟨n.raw ++ "dvh"⟩
def svh  (n : CssNum) : Len := ⟨n.raw ++ "svh"⟩
def lvh  (n : CssNum) : Len := ⟨n.raw ++ "lvh"⟩
def dvw  (n : CssNum) : Len := ⟨n.raw ++ "dvw"⟩
def fr   (n : CssNum) : Len := ⟨n.raw ++ "fr"⟩
def ch   (n : CssNum) : Len := ⟨n.raw ++ "ch"⟩
def ex   (n : CssNum) : Len := ⟨n.raw ++ "ex"⟩
def vmin (n : CssNum) : Len := ⟨n.raw ++ "vmin"⟩
def vmax (n : CssNum) : Len := ⟨n.raw ++ "vmax"⟩

def cssCalc (expr : String) : Len := ⟨s!"calc({expr})"⟩
def clamp   (lo pref hi : Len) : Len := ⟨s!"clamp({lo.raw}, {pref.raw}, {hi.raw})"⟩
def minLen (a b : Len) : Len := ⟨s!"min({a.raw}, {b.raw})"⟩
def maxLen (a b : Len) : Len := ⟨s!"max({a.raw}, {b.raw})"⟩

structure Time where raw : String
deriving Inhabited, BEq, Repr
instance : ToString Time := ⟨Time.raw⟩
def ms  (n : CssNum) : Time := ⟨n.raw ++ "ms"⟩
def sec (n : CssNum) : Time := ⟨n.raw ++ "s"⟩

structure Angle where raw : String
deriving Inhabited, BEq, Repr
instance : ToString Angle := ⟨Angle.raw⟩
def deg  (n : CssNum) : Angle := ⟨n.raw ++ "deg"⟩
def turn (n : CssNum) : Angle := ⟨n.raw ++ "turn"⟩
def rad  (n : CssNum) : Angle := ⟨n.raw ++ "rad"⟩

/-! ## Colors & Hex Parsing -/

def hexDigitVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def stripHashChars (raw : String) : List Char :=
  match raw.toList with
  | '#' :: cs => cs
  | cs        => cs

def isValidHexColor (raw : String) : Bool :=
  let cs := stripHashChars raw
  (cs.length == 3 || cs.length == 4 || cs.length == 6 || cs.length == 8) &&
  cs.all (fun c => (hexDigitVal? c).isSome)

def parseHexRgb? (raw : String) : Option (Nat × Nat × Nat) :=
  match stripHashChars raw with
  | [r, g, b] => do
      let rv ← hexDigitVal? r; let gv ← hexDigitVal? g; let bv ← hexDigitVal? b
      some (rv * 17, gv * 17, bv * 17)
  | [r, g, b, a] => do
      let rv ← hexDigitVal? r; let gv ← hexDigitVal? g; let bv ← hexDigitVal? b
      let av ← hexDigitVal? a
      if av == 15 then some (rv * 17, gv * 17, bv * 17) else none
  | [r1, r2, g1, g2, b1, b2] => do
      let rv1 ← hexDigitVal? r1; let rv2 ← hexDigitVal? r2
      let gv1 ← hexDigitVal? g1; let gv2 ← hexDigitVal? g2
      let bv1 ← hexDigitVal? b1; let bv2 ← hexDigitVal? b2
      some (rv1 * 16 + rv2, gv1 * 16 + gv2, bv1 * 16 + bv2)
  | [r1, r2, g1, g2, b1, b2, a1, a2] => do
      let rv1 ← hexDigitVal? r1; let rv2 ← hexDigitVal? r2
      let gv1 ← hexDigitVal? g1; let gv2 ← hexDigitVal? g2
      let bv1 ← hexDigitVal? b1; let bv2 ← hexDigitVal? b2
      let av1 ← hexDigitVal? a1; let av2 ← hexDigitVal? a2
      if av1 == 15 && av2 == 15 then some (rv1 * 16 + rv2, gv1 * 16 + gv2, bv1 * 16 + bv2) else none
  | _ => none

structure Color where
  raw  : String
  rgb? : Option (Nat × Nat × Nat) := none
deriving Inhabited, BEq, Repr

instance : ToString Color := ⟨Color.raw⟩
def Color.transparent  : Color := ⟨"transparent", none⟩
def Color.currentColor : Color := ⟨"currentColor", none⟩
def Color.inherit      : Color := ⟨"inherit", none⟩
def Color.white        : Color := ⟨"#ffffff", some (255, 255, 255)⟩
def Color.black        : Color := ⟨"#000000", some (0, 0, 0)⟩

def hex  (s : String) : Color :=
  let clean := String.ofList (stripHashChars s)
  ⟨"#" ++ clean, parseHexRgb? clean⟩

def rgb (r g b : Nat) : Color :=
  ⟨s!"rgb({r}, {g}, {b})", if r ≤ 255 && g ≤ 255 && b ≤ 255 then some (r, g, b) else none⟩

def rgb8 (r g b : UInt8) : Color :=
  ⟨s!"rgb({r.toNat}, {g.toNat}, {b.toNat})", some (r.toNat, g.toNat, b.toNat)⟩

def rgba (r g b : Nat) (a : CssNum) : Color :=
  ⟨s!"rgba({r}, {g}, {b}, {a.raw})",
    if r ≤ 255 && g ≤ 255 && b ≤ 255 && (a.raw == "1" || a.raw == "1.0") then some (r, g, b) else none⟩

def hsl (h : CssNum) (s l : CssNum) : Color :=
  ⟨s!"hsl({h.raw}, {s.raw}%, {l.raw}%)", none⟩

def hsla (h s l a : CssNum) : Color :=
  ⟨s!"hsla({h.raw}, {s.raw}%, {l.raw}%, {a.raw})", none⟩

def oklch (l c h : CssNum) : Color :=
  ⟨s!"oklch({l.raw} {c.raw} {h.raw})", none⟩

def colorMix (space : String) (c1 : Color) (p1 : CssNum) (c2 : Color) : Color :=
  ⟨s!"color-mix(in {space}, {c1.raw} {p1.raw}%, {c2.raw})", none⟩

/-! ## `CssValue` Typeclass & Typed Design Tokens (`TypedToken α`) -/

class CssValue (α : Type) where
  toCss : α → String

instance : CssValue Color  := ⟨Color.raw⟩
instance : CssValue Len    := ⟨Len.raw⟩
instance : CssValue CssNum := ⟨CssNum.raw⟩
instance : CssValue Time   := ⟨Time.raw⟩
instance : CssValue Angle  := ⟨Angle.raw⟩
instance : CssValue String := ⟨id⟩

/-- Type-safe design token parameterized by its CSS value type `α`.
    A `TypedToken Color` can only be used where a `Color` is expected, and a `TypedToken Len`
    only where a `Len` is expected. Carries optional light/dark values for compile-time proofs. -/
structure TypedToken (α : Type) where
  name     : String
  lightVal : Option α := none
  darkVal  : Option α := none
deriving Inhabited, BEq, Repr

def colorToken (name : String) (light? : Option Color := none) (dark? : Option Color := none) : TypedToken Color :=
  ⟨name, light?, dark?⟩

def lenToken (name : String) (light? : Option Len := none) (dark? : Option Len := none) : TypedToken Len :=
  ⟨name, light?, dark?⟩

def numToken (name : String) (light? : Option CssNum := none) (dark? : Option CssNum := none) : TypedToken CssNum :=
  ⟨name, light?, dark?⟩

def fontToken (name : String) (light? : Option String := none) (dark? : Option String := none) : TypedToken String :=
  ⟨name, light?, dark?⟩

instance {α : Type} : ToString (TypedToken α) := ⟨fun t => s!"var(--{t.name})"⟩
instance : Coe (TypedToken Color)  Color  := ⟨fun t => ⟨s!"var(--{t.name})", t.lightVal.bind Color.rgb?⟩⟩
instance : Coe (TypedToken Len)    Len    := ⟨fun t => ⟨s!"var(--{t.name})"⟩⟩
instance : Coe (TypedToken CssNum) CssNum := ⟨fun t => ⟨s!"var(--{t.name})"⟩⟩
instance : Coe (TypedToken Time)   Time   := ⟨fun t => ⟨s!"var(--{t.name})"⟩⟩
instance : Coe (TypedToken String) String := ⟨fun t => s!"var(--{t.name})"⟩

def TypedToken.set {α : Type} [CssValue α] (t : TypedToken α) (value : α) : Item :=
  .decl ("--" ++ t.name) (CssValue.toCss value)

def cssVar {α : Type} [CssValue α] (t : TypedToken α) (value : α) : Item :=
  t.set value

/-! ## Typed CSS Keyword Enums -/

inductive Display | flex | inlineFlex | grid | inlineGrid | block | inline | inlineBlock | table | flowRoot | none | contents
deriving Inhabited, BEq, Repr
def Display.css : Display → String
  | .flex => "flex" | .inlineFlex => "inline-flex" | .grid => "grid" | .inlineGrid => "inline-grid"
  | .block => "block" | .inline => "inline" | .inlineBlock => "inline-block"
  | .table => "table" | .flowRoot => "flow-root" | .none => "none" | .contents => "contents"

inductive Position | static | relative | absolute | fixed | sticky
deriving Inhabited, BEq, Repr
def Position.css : Position → String
  | .static => "static" | .relative => "relative" | .absolute => "absolute"
  | .fixed => "fixed" | .sticky => "sticky"

inductive TextAlign | left | right | center | justify | start | «end»
deriving Inhabited, BEq, Repr
def TextAlign.css : TextAlign → String
  | .left => "left" | .right => "right" | .center => "center" | .justify => "justify"
  | .start => "start" | .«end» => "end"

inductive FlexDirection | row | column | rowReverse | columnReverse
deriving Inhabited, BEq, Repr
def FlexDirection.css : FlexDirection → String
  | .row => "row" | .column => "column" | .rowReverse => "row-reverse" | .columnReverse => "column-reverse"

inductive Justify | start | «end» | center | spaceBetween | spaceAround | spaceEvenly
deriving Inhabited, BEq, Repr
def Justify.css : Justify → String
  | .start => "flex-start" | .«end» => "flex-end" | .center => "center"
  | .spaceBetween => "space-between" | .spaceAround => "space-around" | .spaceEvenly => "space-evenly"

inductive Align | start | «end» | center | stretch | baseline
deriving Inhabited, BEq, Repr
def Align.css : Align → String
  | .start => "flex-start" | .«end» => "flex-end" | .center => "center"
  | .stretch => "stretch" | .baseline => "baseline"

inductive BorderStyle | solid | dashed | dotted | double | none
deriving Inhabited, BEq, Repr
def BorderStyle.css : BorderStyle → String
  | .solid => "solid" | .dashed => "dashed" | .dotted => "dotted" | .double => "double" | .none => "none"

inductive Cursor
  | auto | default | pointer | notAllowed | text | move | grab | grabbing
  | wait | progress | help | crosshair | zoomIn | zoomOut | colResize | rowResize | none
  | custom (raw : String)
deriving Inhabited, BEq, Repr
def Cursor.css : Cursor → String
  | .auto => "auto" | .default => "default" | .pointer => "pointer" | .notAllowed => "not-allowed"
  | .text => "text" | .move => "move" | .grab => "grab" | .grabbing => "grabbing"
  | .wait => "wait" | .progress => "progress" | .help => "help" | .crosshair => "crosshair"
  | .zoomIn => "zoom-in" | .zoomOut => "zoom-out" | .colResize => "col-resize" | .rowResize => "row-resize"
  | .none => "none" | .custom s => s
instance : Coe String Cursor := ⟨Cursor.custom⟩

inductive Overflow | visible | hidden | clip | scroll | auto | custom (raw : String)
deriving Inhabited, BEq, Repr
def Overflow.css : Overflow → String
  | .visible => "visible" | .hidden => "hidden" | .clip => "clip" | .scroll => "scroll"
  | .auto => "auto" | .custom s => s
instance : Coe String Overflow := ⟨Overflow.custom⟩

inductive TextDecoration | none | underline | overline | lineThrough | custom (raw : String)
deriving Inhabited, BEq, Repr
def TextDecoration.css : TextDecoration → String
  | .none => "none" | .underline => "underline" | .overline => "overline"
  | .lineThrough => "line-through" | .custom s => s
instance : Coe String TextDecoration := ⟨TextDecoration.custom⟩

inductive WhiteSpace | normal | nowrap | pre | preWrap | preLine | breakSpaces | custom (raw : String)
deriving Inhabited, BEq, Repr
def WhiteSpace.css : WhiteSpace → String
  | .normal => "normal" | .nowrap => "nowrap" | .pre => "pre" | .preWrap => "pre-wrap"
  | .preLine => "pre-line" | .breakSpaces => "break-spaces" | .custom s => s
instance : Coe String WhiteSpace := ⟨WhiteSpace.custom⟩

inductive BoxSizing | contentBox | borderBox
deriving Inhabited, BEq, Repr
def BoxSizing.css : BoxSizing → String
  | .contentBox => "content-box" | .borderBox => "border-box"

inductive FlexWrap | nowrap | wrap | wrapReverse
deriving Inhabited, BEq, Repr
def FlexWrap.css : FlexWrap → String
  | .nowrap => "nowrap" | .wrap => "wrap" | .wrapReverse => "wrap-reverse"

inductive AlignSelf | auto | start | «end» | center | stretch | baseline
deriving Inhabited, BEq, Repr
def AlignSelf.css : AlignSelf → String
  | .auto => "auto" | .start => "flex-start" | .«end» => "flex-end"
  | .center => "center" | .stretch => "stretch" | .baseline => "baseline"

inductive JustifySelf | auto | start | «end» | center | stretch
deriving Inhabited, BEq, Repr
def JustifySelf.css : JustifySelf → String
  | .auto => "auto" | .start => "start" | .«end» => "end" | .center => "center" | .stretch => "stretch"

inductive ObjectFit | fill | contain | cover | none | scaleDown
deriving Inhabited, BEq, Repr
def ObjectFit.css : ObjectFit → String
  | .fill => "fill" | .contain => "contain" | .cover => "cover" | .none => "none" | .scaleDown => "scale-down"

inductive PointerEvents | auto | none
deriving Inhabited, BEq, Repr
def PointerEvents.css : PointerEvents → String
  | .auto => "auto" | .none => "none"

inductive UserSelect | auto | none | text | all
deriving Inhabited, BEq, Repr
def UserSelect.css : UserSelect → String
  | .auto => "auto" | .none => "none" | .text => "text" | .all => "all"

inductive Visibility | visible | hidden | collapse
deriving Inhabited, BEq, Repr
def Visibility.css : Visibility → String
  | .visible => "visible" | .hidden => "hidden" | .collapse => "collapse"

inductive FontStyle | normal | italic | oblique
deriving Inhabited, BEq, Repr
def FontStyle.css : FontStyle → String
  | .normal => "normal" | .italic => "italic" | .oblique => "oblique"

inductive TextTransform | none | capitalize | uppercase | lowercase
deriving Inhabited, BEq, Repr
def TextTransform.css : TextTransform → String
  | .none => "none" | .capitalize => "capitalize" | .uppercase => "uppercase" | .lowercase => "lowercase"

inductive TextOverflow | clip | ellipsis
deriving Inhabited, BEq, Repr
def TextOverflow.css : TextOverflow → String
  | .clip => "clip" | .ellipsis => "ellipsis"

inductive WordBreak | normal | breakAll | keepAll | breakWord
deriving Inhabited, BEq, Repr
def WordBreak.css : WordBreak → String
  | .normal => "normal" | .breakAll => "break-all" | .keepAll => "keep-all" | .breakWord => "break-word"

inductive ScrollBehavior | auto | smooth
deriving Inhabited, BEq, Repr
def ScrollBehavior.css : ScrollBehavior → String
  | .auto => "auto" | .smooth => "smooth"

/-! ## CSS Property Builders -/

instance : CoeFun Item (fun _ => Len → Item) where
  coe
    | .decl p v, l => .decl p (if l.raw.isEmpty then v else v ++ " " ++ l.raw)
    | other,     _ => other

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
def inset         (l : Len) : Item := .decl "inset" l.raw
def top           (l : Len) : Item := .decl "top" l.raw
def right         (l : Len) : Item := .decl "right" l.raw
def bottom        (l : Len) : Item := .decl "bottom" l.raw
def left          (l : Len) : Item := .decl "left" l.raw
def gap           (l : Len) : Item := .decl "gap" l.raw
def rowGap        (l : Len) : Item := .decl "row-gap" l.raw
def columnGap     (l : Len) : Item := .decl "column-gap" l.raw
def fontSize      (l : Len) : Item := .decl "font-size" l.raw
def borderRadius  (l : Len) : Item := .decl "border-radius" l.raw
def borderWidth   (l : Len) : Item := .decl "border-width" l.raw
def outlineOffset (l : Len) : Item := .decl "outline-offset" l.raw
def letterSpacing (l : Len) : Item := .decl "letter-spacing" l.raw
def flexBasis     (l : Len) : Item := .decl "flex-basis" l.raw

def color           (c : Color) : Item := .decl "color" c.raw
def backgroundColor (c : Color) : Item := .decl "background-color" c.raw
def borderColor     (c : Color) : Item := .decl "border-color" c.raw
def fill            (c : Color) : Item := .decl "fill" c.raw
def stroke          (c : Color) : Item := .decl "stroke" c.raw
def accentColor     (c : Color) : Item := .decl "accent-color" c.raw
def caretColor      (c : Color) : Item := .decl "caret-color" c.raw

def display        (d : Display)        : Item := .decl "display" d.css
def position       (p : Position)       : Item := .decl "position" p.css
def textAlign      (t : TextAlign)      : Item := .decl "text-align" t.css
def flexDirection  (f : FlexDirection)  : Item := .decl "flex-direction" f.css
def justifyContent (j : Justify)        : Item := .decl "justify-content" j.css
def alignItems     (a : Align)          : Item := .decl "align-items" a.css
def cursor         (c : Cursor)         : Item := .decl "cursor" c.css
def overflow       (o : Overflow)       : Item := .decl "overflow" o.css
def overflowX      (o : Overflow)       : Item := .decl "overflow-x" o.css
def overflowY      (o : Overflow)       : Item := .decl "overflow-y" o.css
def textDecoration (t : TextDecoration) : Item := .decl "text-decoration" t.css
def whiteSpace     (w : WhiteSpace)     : Item := .decl "white-space" w.css
def boxSizing      (b : BoxSizing)      : Item := .decl "box-sizing" b.css
def flexWrap       (w : FlexWrap)       : Item := .decl "flex-wrap" w.css
def alignSelf      (a : AlignSelf)      : Item := .decl "align-self" a.css
def justifySelf    (j : JustifySelf)    : Item := .decl "justify-self" j.css
def objectFit      (o : ObjectFit)      : Item := .decl "object-fit" o.css
def pointerEvents  (p : PointerEvents)  : Item := .decl "pointer-events" p.css
def userSelect     (u : UserSelect)     : Item := .decl "user-select" u.css
def visibility     (v : Visibility)     : Item := .decl "visibility" v.css
def fontStyle      (f : FontStyle)      : Item := .decl "font-style" f.css
def textTransform  (t : TextTransform)  : Item := .decl "text-transform" t.css
def textOverflow   (t : TextOverflow)   : Item := .decl "text-overflow" t.css
def wordBreak      (w : WordBreak)      : Item := .decl "word-break" w.css
def scrollBehavior (s : ScrollBehavior) : Item := .decl "scroll-behavior" s.css

-- Coercing `BorderStyle → Color → Item` with an empty color sentinel allows `borderTop .none` / `border 0` alongside `border (px 1) .solid c`.
private def mkBorder (prop : String) (w : Len) (s : BorderStyle) (c : Color) : Item :=
  .decl prop (if c.raw.isEmpty then w.raw else s!"{w.raw} {s.css} {c.raw}")
instance : Coe (BorderStyle → Color → Item) Item := ⟨fun f => f .solid ⟨"", none⟩⟩
def border       := mkBorder "border"
def borderTop    := mkBorder "border-top"
def borderRight  := mkBorder "border-right"
def borderBottom := mkBorder "border-bottom"
def borderLeft   := mkBorder "border-left"
def outline      := mkBorder "outline"

def background          (v : String) : Item := .decl "background" v
def boxShadow           (v : String) : Item := .decl "box-shadow" v
def transform           (v : String) : Item := .decl "transform" v
def transition          (v : String) : Item := .decl "transition" v
def font                (v : String) : Item := .decl "font" v
def fontFamily          (v : String) : Item := .decl "font-family" v
def fontWeight          (v : CssNum) : Item := .decl "font-weight" v.raw
def lineHeight          (v : CssNum) : Item := .decl "line-height" v.raw
def opacity             (v : CssNum) : Item := .decl "opacity" v.raw
def zIndex              (v : CssNum) : Item := .decl "z-index" v.raw
def flex                (v : CssNum) : Item := .decl "flex" v.raw
def flexGrow            (v : CssNum) : Item := .decl "flex-grow" v.raw
def flexShrink          (v : CssNum) : Item := .decl "flex-shrink" v.raw
def gridTemplateColumns (v : String) : Item := .decl "grid-template-columns" v
def gridTemplateRows    (v : String) : Item := .decl "grid-template-rows" v
def gridColumn          (v : String) : Item := .decl "grid-column" v
def gridRow             (v : String) : Item := .decl "grid-row" v
def gridArea            (v : String) : Item := .decl "grid-area" v
def placeItems          (v : String) : Item := .decl "place-items" v
def placeContent        (v : String) : Item := .decl "place-content" v
def justifyItems        (v : String) : Item := .decl "justify-items" v
def aspectRatio         (v : String) : Item := .decl "aspect-ratio" v
def animation           (v : String) : Item := .decl "animation" v
def animationDuration   (t : Time)   : Item := .decl "animation-duration" t.raw
def willChange          (v : String) : Item := .decl "will-change" v
def backdropFilter      (v : String) : Item := .decl "backdrop-filter" v
def filter              (v : String) : Item := .decl "filter" v
def clipPath            (v : String) : Item := .decl "clip-path" v
def listStyle           (v : String) : Item := .decl "list-style" v
def resize              (v : String) : Item := .decl "resize" v
def appearance          (v : String) : Item := .decl "appearance" v
def verticalAlign       (v : String) : Item := .decl "vertical-align" v
def content             (v : String) : Item := .decl "content" v

/-! ## Hashing & Scoped `Style` Structure -/

def cssHashLoop : List UInt8 → UInt64 → UInt64
  | [], h      => h
  | b :: bs, h =>
      let h' := (h ^^^ UInt64.ofNat b.toNat) * 1099511628211
      if h' == 0 then cssHashLoop bs 0 else cssHashLoop bs h'

def cssHash (s : String) : UInt64 :=
  cssHashLoop s.toUTF8.data.toList 1469598103934665603

private def hexChar (n : Nat) : Char :=
  match n % 16 with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b'
  | 12 => 'c' | 13 => 'd' | 14 => 'e' | _ => 'f'

def shortHexHash (h : UInt64) : String :=
  let v := h.toNat
  String.ofList [
    hexChar (v / 268435456), hexChar (v / 16777216), hexChar (v / 1048576), hexChar (v / 65536),
    hexChar (v / 4096),      hexChar (v / 256),      hexChar (v / 16),      hexChar v
  ]

structure Style where
  className  : String
  raw        : String
  items      : List Item := []
  usedTokens : List String := []
  extraRules : List String := []
  isGlobal   : Bool := false
deriving Inhabited

instance : Coe Style (Attr msg) := ⟨fun s => .cls s.className⟩

/-! ## Keyframes -/

structure Keyframes where
  name  : String
  steps : List (String × List Item)
deriving Inhabited

def keyframes (name : String) (steps : List (String × List Item)) : Keyframes :=
  { name := sanitizeCssIdent name, steps }

def Keyframes.renderSteps : List (String × List Item) → String
  | [] => ""
  | [(sel, body)] => sanitizeCssSelector sel ++ " { " ++ Item.renderList body ++ " }"
  | (sel, body) :: rest =>
      sanitizeCssSelector sel ++ " { " ++ Item.renderList body ++ " } " ++ Keyframes.renderSteps rest

def Keyframes.rule (kf : Keyframes) : String :=
  "@keyframes " ++ sanitizeCssIdent kf.name ++ " { " ++ Keyframes.renderSteps kf.steps ++ " }"

def Keyframes.asStyle (kf : Keyframes) : Style :=
  { className := s!"__qed_kf_{sanitizeCssIdent kf.name}"
    raw       := kf.rule
    isGlobal  := true }

/-! ## Themes & Stylesheet Rendering -/

def cssJoinLines : List String → String
  | []      => ""
  | [s]     => s
  | s :: ss => s ++ "\n" ++ cssJoinLines ss

def renderThemeRule : Item → String
  | .nest s b =>
      let clean := sanitizeCssSelector s
      if isAtRuleSelector clean then clean ++ " { " ++ Item.renderList b ++ " }"
      else ":where(" ++ clean ++ ") { " ++ Item.renderList b ++ " }"
  | i => i.render

structure Theme where
  name          : String
  lightDecls    : List Item := []
  darkDecls     : List Item := []
  resets        : List Item := []
  definedTokens : List String := []
  darkTokens    : List String := []
deriving Inhabited

def Theme.render (th : Theme) : String :=
  let lightPart :=
    if th.lightDecls.isEmpty then []
    else [":root { " ++ Item.renderList th.lightDecls ++ " }"]
  let darkPart :=
    if th.darkDecls.isEmpty then []
    else [
      "@media (prefers-color-scheme: dark) { :root { " ++ Item.renderList th.darkDecls ++ " } }",
      "[data-theme=\"dark\"] { " ++ Item.renderList th.darkDecls ++ " }"
    ]
  let resetPart := th.resets.map renderThemeRule
  cssJoinLines (lightPart ++ darkPart ++ resetPart)

def Theme.asStyle (th : Theme) : Style :=
  { className := s!"__qed_theme_{sanitizeCssIdent th.name}"
    raw       := th.render
    isGlobal  := true }

def Theme.coversStyle (th : Theme) (s : Style) : Bool :=
  s.usedTokens.all (fun t => th.definedTokens.contains t)

def Theme.missingTokensForStyle (th : Theme) (s : Style) : List String :=
  s.usedTokens.filter (fun t => !th.definedTokens.contains t)

def Theme.coversAll (th : Theme) (styles : List Style) : Bool :=
  styles.all (th.coversStyle ·)

def Theme.missingTokens (th : Theme) (styles : List Style) : List String :=
  dedupStrings (styles.foldl (fun acc s => acc ++ th.missingTokensForStyle s) [])

def Theme.darkComplete (th : Theme) : Bool :=
  th.darkTokens.all (fun t => th.definedTokens.contains t)

def Style.rule (s : Style) : String :=
  if s.isGlobal then sanitizeWith (· != '<') s.raw
  else "." ++ sanitizeWith (· != '<') s.className ++ " { " ++ sanitizeWith (· != '<') s.raw ++ " }"

def renderStyleSheet (styles : List Style) : String :=
  let seen := (styles.foldl
    (fun acc s => if acc.any (·.className == s.className) then acc else s :: acc) []).reverse
  let (globals, localStyles) := seen.partition (·.isGlobal)
  let extras := dedupStrings (localStyles.foldl (fun acc s => acc ++ s.extraRules) [])
  let globalLines := globals.map Style.rule
  let extraLines  := extras.map (sanitizeWith (· != '<'))
  let localLines  := localStyles.map Style.rule
  cssJoinLines (globalLines ++ extraLines ++ localLines)

/-! ## Safe Dynamic Inline Styles & CSS Custom Properties -/

def inlineStyleItem : Item → String
  | .decl p v => sanitizeInlineCssAtom p ++ ": " ++ sanitizeInlineCssAtom v ++ ";"
  | .nest _ _ => ""

def inlineStyleStr : List Item → String
  | []      => ""
  | [i]     => inlineStyleItem i
  | i :: is =>
      let head := inlineStyleItem i
      let tail := inlineStyleStr is
      if head.isEmpty then tail
      else if tail.isEmpty then head
      else head ++ " " ++ tail

def inlineStyle (items : List Item) : Attr msg :=
  .attr "style" (inlineStyleStr items)

def styleVars (vars : List Item) : Attr msg :=
  inlineStyle vars

end Qed
