import Qed.Html

namespace Qed

/-! ## CSS Sanitization Helpers -/

@[inline] def isSafeCssAtomChar (c : Char) : Bool :=
  c.toNat ≥ 32 && c.toNat != 127 && c != '{' && c != '}' && c != ';' && c != '<' && c != '>' && c != '\\'
@[inline] def isSafeCssSelectorChar (c : Char) : Bool := isSafeCssAtomChar c
@[inline] def isSafeInlineCssChar (c : Char) : Bool := isSafeCssAtomChar c && c != '"' && c != '\''
@[inline] def isSafeCssIdentChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_'

def hasCommentOpenLoop (afterSlash : Bool) : List Char → Bool
  | [] => false | c :: cs => (afterSlash && c == '*') || hasCommentOpenLoop (c == '/') cs
def hasCommentOpen (cs : List Char) : Bool := hasCommentOpenLoop false cs

def stripCommentOpenLoop (afterSlash : Bool) : List Char → List Char
  | [] => [] | c :: cs => if afterSlash && c == '*' then stripCommentOpenLoop true cs else c :: stripCommentOpenLoop (c == '/') cs
def stripCommentOpen (cs : List Char) : List Char := stripCommentOpenLoop false cs

def sanitizeWith (p : Char → Bool) (s : String) : String :=
  let cs := s.toList; if cs.all p then s else String.ofList (cs.filter p)

def sanitizeCssWith (p : Char → Bool) (s : String) : String :=
  let s1 := sanitizeWith p s; let cs := s1.toList
  if hasCommentOpen cs then String.ofList (stripCommentOpen cs) else s1

def sanitizeCssAtom (s : String) : String := sanitizeCssWith isSafeCssAtomChar s
def sanitizeCssSelector (s : String) : String := sanitizeCssAtom s
def sanitizeInlineCssAtom (s : String) : String := sanitizeCssWith isSafeInlineCssChar s
def sanitizeCssIdent (s : String) : String := sanitizeWith isSafeCssIdentChar s

/-! ## CSS AST (`Item`), Token Extraction & Deterministic Merging -/

inductive Item where
  | decl (property value : String)
  | nest (selector : String) (body : List Item)
deriving Inhabited

mutual
  def Item.render : Item → String
    | .decl p v   => sanitizeCssAtom p ++ ": " ++ sanitizeCssAtom v ++ ";"
    | .nest sel b => sanitizeCssSelector sel ++ " { " ++ Item.renderList b ++ " }"
  def Item.renderList : List Item → String
    | [] => "" | [i] => Item.render i | i :: is => Item.render i ++ " " ++ Item.renderList is
end

private def takeVarName : List Char → List Char → List String
  | acc, [] => if acc.isEmpty then [] else [String.ofList acc.reverse]
  | acc, c :: cs =>
      if c == ')' || c == ',' || c.isWhitespace then
        (if acc.isEmpty then [] else [String.ofList acc.reverse]) ++ extractVarNamesLoop cs
      else takeVarName (c :: acc) cs
where
  extractVarNamesLoop : List Char → List String
    | [] => []
    | 'v' :: 'a' :: 'r' :: '(' :: '-' :: '-' :: rest => takeVarName [] rest
    | _ :: rest => extractVarNamesLoop rest

def extractVarNames (s : String) : List String := takeVarName.extractVarNamesLoop s.toList
def dedupStrings (xs : List String) : List String := xs.eraseDups

mutual
  def Item.collectTokens : Item → List String
    | .decl _ v => extractVarNames v | .nest _ b => Item.collectTokensList b
  def Item.collectTokensList : List Item → List String
    | [] => [] | i :: is => Item.collectTokens i ++ Item.collectTokensList is
end

def collectItemTokens (items : List Item) : List String := dedupStrings (Item.collectTokensList items)

mutual
  def Item.mergeOne (base : List Item) : Item → List Item
    | .decl p v      => (base.filter fun | .decl p' _ => p' != p | _ => true) ++ [.decl p v]
    | .nest sel body => Item.mergeNest sel body base
  termination_by i => (sizeOf i, 0)
  decreasing_by simp_wf; omega
  def Item.mergeNest (sel : String) (body : List Item) : List Item → List Item
    | []              => [.nest sel body]
    | .nest s b :: rs => if s == sel then .nest s (Item.mergeItems b body) :: rs else .nest s b :: Item.mergeNest sel body rs
    | o :: rs         => o :: Item.mergeNest sel body rs
  termination_by rs => (sizeOf body, rs.length)
  decreasing_by all_goals (simp_wf; omega)
  def Item.mergeItems : List Item → List Item → List Item
    | base, [] => base | base, i :: is => Item.mergeItems (Item.mergeOne base i) is
  termination_by _ xs => (sizeOf xs, 0)
  decreasing_by all_goals (simp_wf; omega)
end

/-! ## Typed CSS Values: Numbers, Lengths, Time, Colors & Design Tokens -/

structure CssNum where raw : String deriving Inhabited, BEq, Repr
namespace CssNum
private def ofMantissaExp (m e : Nat) : String :=
  if e == 0 then toString m else
  let ds := (toString m).toList; let ps := List.replicate (e + 1 - ds.length) '0' ++ ds
  let fp := ((ps.drop (ps.length - e)).reverse.dropWhile (· == '0')).reverse
  String.ofList (ps.take (ps.length - e)) ++ if fp.isEmpty then "" else "." ++ String.ofList fp
instance (n : Nat) : OfNat CssNum n := ⟨⟨toString n⟩⟩
instance : Coe Nat CssNum := ⟨(⟨toString ·⟩)⟩
instance : Coe Int CssNum := ⟨(⟨toString ·⟩)⟩
instance : ToString CssNum := ⟨CssNum.raw⟩
instance : Neg CssNum := ⟨fun x => ⟨if x.raw.startsWith "-" || x.raw == "0" then x.raw else "-" ++ x.raw⟩⟩
instance : OfScientific CssNum := ⟨fun m neg e => ⟨if neg then ofMantissaExp m e else toString (m * 10 ^ e)⟩⟩
end CssNum

structure Len where raw : String deriving Inhabited, BEq, Repr
instance : OfNat Len 0 := ⟨⟨"0"⟩⟩
instance : ToString Len := ⟨Len.raw⟩
def Len.auto : Len := ⟨"auto"⟩
def px  (n : CssNum) : Len := ⟨n.raw ++ "px"⟩
def rem (n : CssNum) : Len := ⟨n.raw ++ "rem"⟩
def em  (n : CssNum) : Len := ⟨n.raw ++ "em"⟩
def pct (n : CssNum) : Len := ⟨n.raw ++ "%"⟩

structure Time where raw : String deriving Inhabited, BEq, Repr
instance : ToString Time := ⟨Time.raw⟩

abbrev hexDigitVal? : Char → Option Nat := unhexNat?
private def stripHashChars (raw : String) : List Char := match raw.toList with | '#' :: cs => cs | cs => cs

def isValidHexColor (raw : String) : Bool :=
  let cs := stripHashChars raw
  [3, 4, 6, 8].contains cs.length && cs.all fun c => (hexDigitVal? c).isSome

private def hexPair? (c1 c2 : Char) : Option Nat := do pure ((← hexDigitVal? c1) * 16 + (← hexDigitVal? c2))

def parseHexRgb? (raw : String) : Option (Nat × Nat × Nat) :=
  let rgb r1 r2 g1 g2 b1 b2 : Option (Nat × Nat × Nat) := do
    pure ((← hexPair? r1 r2), (← hexPair? g1 g2), (← hexPair? b1 b2))
  match stripHashChars raw with
  | [r, g, b] => rgb r r g g b b
  | [r, g, b, a] => do let c ← rgb r r g g b b; guard ((← hexDigitVal? a) == 15); pure c
  | [r1, r2, g1, g2, b1, b2] => rgb r1 r2 g1 g2 b1 b2
  | [r1, r2, g1, g2, b1, b2, a1, a2] => do let c ← rgb r1 r2 g1 g2 b1 b2; guard ((← hexPair? a1 a2) == 255); pure c
  | _ => none

structure Color where mk :: (raw : String) (rgb? : Option (Nat × Nat × Nat) := none) deriving Inhabited, BEq, Repr
instance : ToString Color := ⟨Color.raw⟩
def Color.transparent  : Color := ⟨"transparent", none⟩
def Color.currentColor : Color := ⟨"currentColor", none⟩
def Color.inherit      : Color := ⟨"inherit", none⟩
def Color.white        : Color := ⟨"#ffffff", some (255, 255, 255)⟩
def Color.black        : Color := ⟨"#000000", some (0, 0, 0)⟩
def hex (s : String) : Color := let clean := String.ofList (stripHashChars s); ⟨"#" ++ clean, parseHexRgb? clean⟩
def rgb (r g b : Nat) : Color := ⟨s!"rgb({r}, {g}, {b})", if r ≤ 255 && g ≤ 255 && b ≤ 255 then some (r, g, b) else none⟩

class CssValue (α : Type) where toCss : α → String
instance : CssValue Color  := ⟨Color.raw⟩
instance : CssValue Len    := ⟨Len.raw⟩
instance : CssValue CssNum := ⟨CssNum.raw⟩
instance : CssValue Time   := ⟨Time.raw⟩
instance : CssValue String := ⟨id⟩

structure TypedToken (α : Type) where mk :: (name : String) (lightVal : Option α := none) (darkVal : Option α := none) deriving Inhabited, BEq, Repr
instance {α : Type} : ToString (TypedToken α) := ⟨fun t => s!"var(--{t.name})"⟩
instance : Coe (TypedToken Color)  Color  := ⟨fun t => ⟨s!"var(--{t.name})", t.lightVal.bind Color.rgb?⟩⟩
instance : Coe (TypedToken Len)    Len    := ⟨fun t => ⟨s!"var(--{t.name})"⟩⟩
instance : Coe (TypedToken CssNum) CssNum := ⟨fun t => ⟨s!"var(--{t.name})"⟩⟩
instance : Coe (TypedToken Time)   Time   := ⟨fun t => ⟨s!"var(--{t.name})"⟩⟩
instance : Coe (TypedToken String) String := ⟨fun t => s!"var(--{t.name})"⟩
def TypedToken.set {α : Type} [CssValue α] (t : TypedToken α) (value : α) : Item := .decl ("--" ++ t.name) (CssValue.toCss value)
def cssVar {α : Type} [CssValue α] (t : TypedToken α) (value : α) : Item := t.set value

/-! ## Dynamic Inline CSS Property Builders -/

local macro "def_css_props" ty:ident "[" items:("(" ident "," str ")"),* "]" : command => do
  return ⟨Lean.mkNullNode (← items.getElems.mapM fun it => `(def $(⟨it.raw[1]⟩) (v : $ty) : Item := .decl $(⟨it.raw[3]⟩) (CssValue.toCss v)))⟩

def_css_props Len    [(width, "width"), (height, "height"), (padding, "padding"), (paddingX, "padding-inline"),
                      (paddingY, "padding-block"), (paddingTop, "padding-top"), (paddingRight, "padding-right"),
                      (paddingBottom, "padding-bottom"), (paddingLeft, "padding-left"), (margin, "margin"),
                      (marginX, "margin-inline"), (marginY, "margin-block"), (marginTop, "margin-top"),
                      (marginRight, "margin-right"), (marginBottom, "margin-bottom"), (marginLeft, "margin-left"),
                      (letterSpacing, "letter-spacing")]
def_css_props Color  [(color, "color"), (backgroundColor, "background-color")]
def_css_props String [(background, "background"), (transform, "transform")]
def_css_props CssNum [(opacity, "opacity"), (zIndex, "z-index")]

/-! ## Hashing, Scoped `Style`, `Keyframes`, `Theme` & Inline Styles -/

def cssHashLoop : List UInt8 → UInt64 → UInt64
  | [], h => h | b :: bs, h => cssHashLoop bs ((h ^^^ UInt64.ofNat b.toNat) * 1099511628211)
def cssHash (s : String) : UInt64 := cssHashLoop s.toUTF8.data.toList 1469598103934665603
def shortHexHash (h : UInt64) : String :=
  String.ofList ([28, 24, 20, 16, 12, 8, 4, 0].map fun sh => hexDigitLower (h.toNat >>> sh))

structure ThemeColorEntry where mk ::
  (cssName : String) (lightRgb : Nat × Nat × Nat) (darkRgb? : Option (Nat × Nat × Nat) := none)
deriving Inhabited, BEq, Repr

structure StyleColorCheck where mk ::
  (scope fgCss bgCss : String)
  (fgRgb? bgRgb? : Option (Nat × Nat × Nat) := none)
  (fgTok? bgTok? : Option String := none)
  (forcedDark : Bool := false)
deriving Inhabited, BEq, Repr

structure Style where mk ::
  (className raw : String) (items : List Item := []) (usedTokens extraRules : List String := []) (isGlobal : Bool := false)
  (colorChecks : List StyleColorCheck := []) (themePalette : List ThemeColorEntry := [])
deriving Inhabited
instance : Coe Style (Attr msg) := ⟨fun s => .cls s.className⟩

structure Keyframes where mk :: (name : String) (steps : List (String × List Item)) deriving Inhabited
def keyframes (name : String) (steps : List (String × List Item)) : Keyframes := { name := sanitizeCssIdent name, steps }
def Keyframes.renderSteps (steps : List (String × List Item)) : String := Item.renderList (steps.map fun (s, b) => .nest s b)
def Keyframes.rule (kf : Keyframes) : String := "@keyframes " ++ sanitizeCssIdent kf.name ++ " { " ++ Keyframes.renderSteps kf.steps ++ " }"
def Keyframes.asStyle (kf : Keyframes) : Style := { className := s!"__qed_kf_{sanitizeCssIdent kf.name}", raw := kf.rule, isGlobal := true }

def cssJoinLines : List String → String
  | [] => "" | [s] => s | s :: ss => s ++ "\n" ++ cssJoinLines ss

def renderThemeRule : Item → String
  | .nest s b =>
      let clean := sanitizeCssSelector s
      if clean.trimmed.startsWith "@" then clean ++ " { " ++ Item.renderList b ++ " }" else ":where(" ++ clean ++ ") { " ++ Item.renderList b ++ " }"
  | i => i.render

structure Theme where mk ::
  (name : String) (lightDecls darkDecls resets : List Item := []) (definedTokens darkTokens : List String := [])
  (colorPalette : List ThemeColorEntry := [])
deriving Inhabited

def Theme.render (th : Theme) : String :=
  let lightPart := if th.lightDecls.isEmpty then [] else [":root { " ++ Item.renderList th.lightDecls ++ " }"]
  let darkPart := if th.darkDecls.isEmpty then [] else [
    "@media (prefers-color-scheme: dark) { :root { " ++ Item.renderList th.darkDecls ++ " } }",
    "[data-theme=\"dark\"] { " ++ Item.renderList th.darkDecls ++ " }"]
  cssJoinLines (lightPart ++ darkPart ++ th.resets.map renderThemeRule)

def Theme.asStyle (th : Theme) : Style :=
  { className := s!"__qed_theme_{sanitizeCssIdent th.name}", raw := th.render, isGlobal := true, themePalette := th.colorPalette }
def Theme.coversStyle (th : Theme) (s : Style) : Bool := s.usedTokens.all th.definedTokens.contains
def Theme.missingTokensForStyle (th : Theme) (s : Style) : List String := s.usedTokens.filter (!th.definedTokens.contains ·)
def Theme.coversAll (th : Theme) (styles : List Style) : Bool := styles.all th.coversStyle
def Theme.missingTokens (th : Theme) (styles : List Style) : List String := dedupStrings (styles.flatMap th.missingTokensForStyle)
def Theme.darkComplete (th : Theme) : Bool := th.darkTokens.all th.definedTokens.contains

def Style.rule (s : Style) : String :=
  if s.isGlobal then sanitizeWith (· != '<') s.raw
  else "." ++ sanitizeWith (· != '<') s.className ++ " { " ++ sanitizeWith (· != '<') s.raw ++ " }"

def renderStyleSheet (styles : List Style) : String :=
  let seen := (styles.foldl (fun acc s => if acc.any (·.className == s.className) then acc else s :: acc) []).reverse
  let (globals, localStyles) := seen.partition (·.isGlobal)
  cssJoinLines (globals.map Style.rule ++ (dedupStrings (localStyles.flatMap (·.extraRules))).map (sanitizeWith (· != '<')) ++ localStyles.map Style.rule)

def inlineStyleItem : Item → String
  | .decl p v => sanitizeInlineCssAtom p ++ ": " ++ sanitizeInlineCssAtom v ++ ";" | .nest _ _ => ""

def inlineStyleStr : List Item → String
  | [] => "" | [i] => inlineStyleItem i
  | i :: is => let h := inlineStyleItem i; let t := inlineStyleStr is; if h.isEmpty then t else if t.isEmpty then h else h ++ " " ++ t

def inlineStyle (items : List Item) : Attr msg := .attr "style" (inlineStyleStr items)
def styleVars (vars : List Item) : Attr msg := inlineStyle vars

end Qed
