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

@[inline] def isSafeCssAtomChar (c : Char) : Bool :=
  c != '{' && c != '}' && c != ';' && c != '<' && c != '>'

@[inline] def isSafeCssSelectorChar (c : Char) : Bool :=
  c != '{' && c != '}' && c != ';' && c != '<'

def sanitizeCssAtom (s : String) : String :=
  let cs := s.toList
  if cs.all isSafeCssAtomChar then s
  else String.ofList (cs.filter isSafeCssAtomChar)

def sanitizeCssSelector (s : String) : String :=
  let cs := s.toList
  if cs.all isSafeCssSelectorChar then s
  else String.ofList (cs.filter isSafeCssSelectorChar)

mutual
  def Item.render : Item → String
    | .decl p v   => sanitizeCssAtom p ++ ": " ++ sanitizeCssAtom v ++ ";"
    | .nest sel b => sanitizeCssSelector sel ++ " { " ++ Item.renderList b ++ " }"
  def Item.renderList : List Item → String
    | []      => ""
    | [i]     => Item.render i
    | i :: is => Item.render i ++ " " ++ Item.renderList is
end

structure CssNum where raw : String deriving Inhabited

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
deriving Inhabited
instance : OfNat Len 0 := ⟨⟨"0"⟩⟩
instance : ToString Len := ⟨Len.raw⟩
def Len.auto : Len := ⟨"auto"⟩
def Len.none : Len := ⟨"none"⟩

def px  (n : CssNum) : Len := ⟨n.raw ++ "px"⟩
def rem (n : CssNum) : Len := ⟨n.raw ++ "rem"⟩
def em  (n : CssNum) : Len := ⟨n.raw ++ "em"⟩
def pct (n : CssNum) : Len := ⟨n.raw ++ "%"⟩
def vh  (n : CssNum) : Len := ⟨n.raw ++ "vh"⟩
def vw  (n : CssNum) : Len := ⟨n.raw ++ "vw"⟩
def fr  (n : CssNum) : Len := ⟨n.raw ++ "fr"⟩

structure Color where raw : String
deriving Inhabited
instance : ToString Color := ⟨Color.raw⟩
def Color.transparent  : Color := ⟨"transparent"⟩
def Color.currentColor : Color := ⟨"currentColor"⟩
def Color.inherit      : Color := ⟨"inherit"⟩

def hex  (s : String) : Color := ⟨"#" ++ s⟩
def rgb  (r g b : Nat) : Color := ⟨s!"rgb({r}, {g}, {b})"⟩
def rgba (r g b : Nat) (a : CssNum) : Color := ⟨s!"rgba({r}, {g}, {b}, {a.raw})"⟩

structure Token where name : String
deriving Inhabited
def token (name : String) : Token := ⟨name⟩
instance : ToString Token   := ⟨fun t => s!"var(--{t.name})"⟩
instance : Coe Token CssNum := ⟨fun t => ⟨s!"var(--{t.name})"⟩⟩
instance : Coe Token Len    := ⟨fun t => ⟨s!"var(--{t.name})"⟩⟩
instance : Coe Token Color  := ⟨fun t => ⟨s!"var(--{t.name})"⟩⟩

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
def top           (l : Len) : Item := .decl "top" l.raw
def right         (l : Len) : Item := .decl "right" l.raw
def bottom        (l : Len) : Item := .decl "bottom" l.raw
def left          (l : Len) : Item := .decl "left" l.raw
def gap           (l : Len) : Item := .decl "gap" l.raw
def fontSize      (l : Len) : Item := .decl "font-size" l.raw
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

-- Coercing `BorderStyle → Color → Item` with an empty color sentinel allows `borderTop .none` / `border 0` alongside `border (px 1) .solid c`.
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
def fontWeight          (v : CssNum) : Item := .decl "font-weight" v.raw
def lineHeight          (v : CssNum) : Item := .decl "line-height" v.raw
def textDecoration      (v : String) : Item := .decl "text-decoration" v
def cursor              (v : String) : Item := .decl "cursor" v
def overflow            (v : String) : Item := .decl "overflow" v
def opacity             (v : CssNum) : Item := .decl "opacity" v.raw
def zIndex              (v : CssNum) : Item := .decl "z-index" v.raw
def flex                (v : CssNum) : Item := .decl "flex" v.raw
def gridTemplateColumns (v : String) : Item := .decl "grid-template-columns" v
def whiteSpace          (v : String) : Item := .decl "white-space" v

def nest (selector : String) (body : List Item) : Item := .nest selector body
def media (query : String) (body : List Item) : Item := .nest ("@media " ++ query) body
def screenMax (w : Len) (body : List Item) : Item := media s!"(max-width: {w.raw})" body
def screenMin (w : Len) (body : List Item) : Item := media s!"(min-width: {w.raw})" body
def Token.set (t : Token) (value : String) : Item := .decl ("--" ++ t.name) value

def css (body : List Item) : Style :=
  let raw := Item.renderList body
  { className := s!"qed-{String.hash raw}", raw := raw }

private def Style.rule (s : Style) : String := "." ++ s.className ++ " { " ++ s.raw ++ " }"

private def joinLines : List String → String
  | []      => ""
  | [s]     => s
  | s :: ss => s ++ "\n" ++ joinLines ss

def renderTheme (tokens : List Item) : String :=
  let (decls, rules) := tokens.partition (fun | .decl _ _ => true | .nest _ _ => false)
  let root := if decls.isEmpty then [] else [":root { " ++ Item.renderList decls ++ " }"]
  let resets := rules.map fun | .nest s b => s!":where({sanitizeCssSelector s}) \{ {Item.renderList b} }" | i => i.render
  joinLines (root ++ resets)

@[inline] def theme (tokens : List Item) : Html msg :=
  el "style" [] [Html.text (escapeRawText (renderTheme tokens))]

def renderStyleSheet (styles : List Style) : String :=
  let seen := (styles.foldl
    (fun acc s => if acc.any (·.className == s.className) then acc else s :: acc) []).reverse
  joinLines (seen.map Style.rule)

/-! ## CSS Injection & `<style>` Breakout Safety Proofs -/

theorem sanitizeCssAtom_safe (s : String) :
    ∀ c ∈ (sanitizeCssAtom s).toList, isSafeCssAtomChar c = true := by
  unfold sanitizeCssAtom
  dsimp only
  by_cases h : s.toList.all isSafeCssAtomChar = true
  · simp only [h, ↓reduceIte]
    rw [List.all_eq_true] at h
    exact h
  · simp only [h, Bool.false_eq_true, ↓reduceIte, String.toList_ofList]
    intro c hc
    exact (List.mem_filter.1 hc).2

theorem sanitizeCssSelector_safe (s : String) :
    ∀ c ∈ (sanitizeCssSelector s).toList, isSafeCssSelectorChar c = true := by
  unfold sanitizeCssSelector
  dsimp only
  by_cases h : s.toList.all isSafeCssSelectorChar = true
  · simp only [h, ↓reduceIte]
    rw [List.all_eq_true] at h
    exact h
  · simp only [h, Bool.false_eq_true, ↓reduceIte, String.toList_ofList]
    intro c hc
    exact (List.mem_filter.1 hc).2

private theorem no_lt_implies_no_closeSeq :
    ∀ (cs : List Char), (∀ c ∈ cs, c ≠ '<') → containsCloseSeqLoop false cs = false
  | [], _ => rfl
  | c :: rest, hno => by
      have hc : c ≠ '<' := hno c (List.mem_cons_self ..)
      have hcb : (c == '<') = false := beq_eq_false_iff_ne.2 hc
      simpa [containsCloseSeqLoop, hcb] using
        no_lt_implies_no_closeSeq rest (fun x hx => hno x (List.mem_cons_of_mem c hx))

theorem containsCloseSeq_of_no_lt {s : String} (hno : ∀ c ∈ s.toList, c ≠ '<') :
    containsCloseSeq s.toList = false :=
  no_lt_implies_no_closeSeq s.toList hno

private theorem str_append_no_lt {a b : String}
    (ha : ∀ c ∈ a.toList, c ≠ '<') (hb : ∀ c ∈ b.toList, c ≠ '<') :
    ∀ c ∈ (a ++ b).toList, c ≠ '<' := by
  intro c hc
  rw [String.toList_append, List.mem_append] at hc
  exact hc.elim (ha c) (hb c)

private theorem lit_no_lt (s : String) (h : s.toList.all (· != '<') = true) :
    ∀ c ∈ s.toList, c ≠ '<' := by
  rw [List.all_eq_true] at h
  intro c hc
  exact bne_iff_ne.1 (h c hc)

private theorem sanitizeCssAtom_no_lt (s : String) :
    ∀ c ∈ (sanitizeCssAtom s).toList, c ≠ '<' := by
  intro c hc
  have hs := sanitizeCssAtom_safe s c hc
  simp only [isSafeCssAtomChar, Bool.and_eq_true, bne_iff_ne] at hs
  exact hs.1.2

private theorem sanitizeCssSelector_no_lt (s : String) :
    ∀ c ∈ (sanitizeCssSelector s).toList, c ≠ '<' := by
  intro c hc
  have hs := sanitizeCssSelector_safe s c hc
  simp only [isSafeCssSelectorChar, Bool.and_eq_true, bne_iff_ne] at hs
  exact hs.2

mutual
  theorem Item.render_no_lt : ∀ (i : Item), ∀ c ∈ (Item.render i).toList, c ≠ '<'
    | .decl p v => by
        simp only [Item.render]
        exact str_append_no_lt
          (str_append_no_lt
            (str_append_no_lt (sanitizeCssAtom_no_lt p) (lit_no_lt ": " rfl))
            (sanitizeCssAtom_no_lt v))
          (lit_no_lt ";" rfl)
    | .nest sel b => by
        simp only [Item.render]
        exact str_append_no_lt
          (str_append_no_lt
            (str_append_no_lt (sanitizeCssSelector_no_lt sel) (lit_no_lt " { " rfl))
            (Item.renderList_no_lt b))
          (lit_no_lt " }" rfl)

  theorem Item.renderList_no_lt : ∀ (is : List Item), ∀ c ∈ (Item.renderList is).toList, c ≠ '<'
    | [] => lit_no_lt "" rfl
    | [i] => Item.render_no_lt i
    | i :: j :: rest => by
        simp only [Item.renderList]
        exact str_append_no_lt
          (str_append_no_lt (Item.render_no_lt i) (lit_no_lt " " rfl))
          (Item.renderList_no_lt (j :: rest))
end

theorem Item.render_no_closeSeq (i : Item) :
    containsCloseSeq (Item.render i).toList = false :=
  containsCloseSeq_of_no_lt (Item.render_no_lt i)

theorem Item.renderList_no_closeSeq (is : List Item) :
    containsCloseSeq (Item.renderList is).toList = false :=
  containsCloseSeq_of_no_lt (Item.renderList_no_lt is)

private theorem joinLines_no_lt :
    ∀ (xs : List String), (∀ s ∈ xs, ∀ c ∈ s.toList, c ≠ '<') →
      ∀ c ∈ (joinLines xs).toList, c ≠ '<'
  | [], _ => lit_no_lt "" rfl
  | [s], hs => hs s (by simp)
  | s₁ :: s₂ :: rest, hs => by
      have h1 := hs s₁ (by simp)
      have h2 := joinLines_no_lt (s₂ :: rest) (fun x hx => hs x (by simp [hx]))
      simp only [joinLines]
      exact str_append_no_lt (str_append_no_lt h1 (lit_no_lt "\n" rfl)) h2

theorem renderTheme_no_lt (tokens : List Item) :
    ∀ c ∈ (renderTheme tokens).toList, c ≠ '<' := by
  unfold renderTheme
  dsimp only
  apply joinLines_no_lt
  intro s hs
  rw [List.mem_append] at hs
  rcases hs with hroot | hreset
  · split at hroot
    · nomatch hroot
    · simp only [List.mem_singleton] at hroot
      subst hroot
      exact str_append_no_lt
        (str_append_no_lt (lit_no_lt ":root { " rfl) (Item.renderList_no_lt _))
        (lit_no_lt " }" rfl)
  · rcases List.mem_map.1 hreset with ⟨item, _, rfl⟩
    cases item with
    | decl p v => exact Item.render_no_lt (.decl p v)
    | nest sel b =>
        change ∀ c ∈ (":where(" ++ sanitizeCssSelector sel ++ ") { " ++ Item.renderList b ++ " }").toList, c ≠ '<'
        exact str_append_no_lt
          (str_append_no_lt
            (str_append_no_lt
              (str_append_no_lt (lit_no_lt ":where(" rfl) (sanitizeCssSelector_no_lt sel))
              (lit_no_lt ") { " rfl))
            (Item.renderList_no_lt b))
          (lit_no_lt " }" rfl)

theorem renderTheme_no_closeSeq (tokens : List Item) :
    containsCloseSeq (renderTheme tokens).toList = false :=
  containsCloseSeq_of_no_lt (renderTheme_no_lt tokens)

theorem css_raw_no_lt (body : List Item) :
    ∀ c ∈ (css body).raw.toList, c ≠ '<' :=
  Item.renderList_no_lt body

theorem css_raw_no_closeSeq (body : List Item) :
    containsCloseSeq (css body).raw.toList = false :=
  containsCloseSeq_of_no_lt (css_raw_no_lt body)

end Qed
