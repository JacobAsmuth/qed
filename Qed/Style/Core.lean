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

def dedupStrings (xs : List String) : List String :=
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
def Len.auto : Len := ⟨"auto"⟩

def px  (n : CssNum) : Len := ⟨n.raw ++ "px"⟩
def rem (n : CssNum) : Len := ⟨n.raw ++ "rem"⟩
def em  (n : CssNum) : Len := ⟨n.raw ++ "em"⟩
def pct (n : CssNum) : Len := ⟨n.raw ++ "%"⟩

structure Time where raw : String
deriving Inhabited, BEq, Repr
instance : ToString Time := ⟨Time.raw⟩

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

private def hexPair? (c1 c2 : Char) : Option Nat := do
  pure ((← hexDigitVal? c1) * 16 + (← hexDigitVal? c2))

def parseHexRgb? (raw : String) : Option (Nat × Nat × Nat) :=
  let rgb (r1 r2 g1 g2 b1 b2 : Char) : Option (Nat × Nat × Nat) := do
    pure ((← hexPair? r1 r2), (← hexPair? g1 g2), (← hexPair? b1 b2))
  match stripHashChars raw with
  | [r, g, b] => rgb r r g g b b
  | [r, g, b, a] => do let c ← rgb r r g g b b; if (← hexDigitVal? a) == 15 then some c else none
  | [r1, r2, g1, g2, b1, b2] => rgb r1 r2 g1 g2 b1 b2
  | [r1, r2, g1, g2, b1, b2, a1, a2] => do let c ← rgb r1 r2 g1 g2 b1 b2; if (← hexPair? a1 a2) == 255 then some c else none
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

def hex (s : String) : Color :=
  let clean := String.ofList (stripHashChars s)
  ⟨"#" ++ clean, parseHexRgb? clean⟩

def rgb (r g b : Nat) : Color :=
  ⟨s!"rgb({r}, {g}, {b})", if r ≤ 255 && g ≤ 255 && b ≤ 255 then some (r, g, b) else none⟩

/-! ## `CssValue` Typeclass & Typed Design Tokens (`TypedToken α`) -/

class CssValue (α : Type) where
  toCss : α → String

instance : CssValue Color  := ⟨Color.raw⟩
instance : CssValue Len    := ⟨Len.raw⟩
instance : CssValue CssNum := ⟨CssNum.raw⟩
instance : CssValue Time   := ⟨Time.raw⟩
instance : CssValue String := ⟨id⟩

/-- Type-safe design token parameterized by its CSS value type `α`.
    A `TypedToken Color` can only be used where a `Color` is expected, and a `TypedToken Len`
    only where a `Len` is expected. Carries optional light/dark values for compile-time proofs. -/
structure TypedToken (α : Type) where
  name     : String
  lightVal : Option α := none
  darkVal  : Option α := none
deriving Inhabited, BEq, Repr

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

/-! ## Dynamic Inline CSS Property Builders -/

def width           (l : Len)    : Item := .decl "width" l.raw
def height          (l : Len)    : Item := .decl "height" l.raw
def padding         (l : Len)    : Item := .decl "padding" l.raw
def paddingX        (l : Len)    : Item := .decl "padding-inline" l.raw
def paddingY        (l : Len)    : Item := .decl "padding-block" l.raw
def paddingTop      (l : Len)    : Item := .decl "padding-top" l.raw
def paddingRight    (l : Len)    : Item := .decl "padding-right" l.raw
def paddingBottom   (l : Len)    : Item := .decl "padding-bottom" l.raw
def paddingLeft     (l : Len)    : Item := .decl "padding-left" l.raw
def margin          (l : Len)    : Item := .decl "margin" l.raw
def marginX         (l : Len)    : Item := .decl "margin-inline" l.raw
def marginY         (l : Len)    : Item := .decl "margin-block" l.raw
def marginTop       (l : Len)    : Item := .decl "margin-top" l.raw
def marginRight     (l : Len)    : Item := .decl "margin-right" l.raw
def marginBottom    (l : Len)    : Item := .decl "margin-bottom" l.raw
def marginLeft      (l : Len)    : Item := .decl "margin-left" l.raw
def letterSpacing   (l : Len)    : Item := .decl "letter-spacing" l.raw
def color           (c : Color)  : Item := .decl "color" c.raw
def backgroundColor (c : Color)  : Item := .decl "background-color" c.raw
def background      (v : String) : Item := .decl "background" v
def transform       (v : String) : Item := .decl "transform" v
def opacity         (v : CssNum) : Item := .decl "opacity" v.raw
def zIndex          (v : CssNum) : Item := .decl "z-index" v.raw

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

def Keyframes.renderSteps (steps : List (String × List Item)) : String :=
  Item.renderList (steps.map fun (sel, body) => .nest sel body)

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
