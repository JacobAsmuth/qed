import Qed.View.Core
import Lean

/-! ## Pre-proved O(1) HTML Validity Lemmas
Eliminates per-component UTF-8 `String` kernel reduction for common HTML5 tags and attributes. -/

namespace Qed.ValidLemmas

theorem not_isVoidTag_or (tag : String) (b : Bool) (h : isVoidTag tag = false) :
    (!isVoidTag tag || b) = true := by rw [h]; rfl

theorem attr_nonUrl {msg : Type} (k v : String)
    (h : isSafeAttrName k = true ∧ isUrlAttrName k = false) :
    (Attr.attr k v : Attr msg).valid = true := by
  simp [Attr.valid, Attr.validKeyValue, h.1, h.2]

theorem signalAttr_nonUrl {msg : Type} (n k v : String)
    (h : isSafeAttrName k = true ∧ isUrlAttrName k = false) :
    (Attr.signalAttr n k v : Attr msg).valid = true := by
  simp [Attr.valid, Attr.validKeyValue, h.1, h.2]

theorem flag_safe {msg : Type} (k : String) (p : Bool) (h : isSafeAttrName k = true) :
    (Attr.flag k p : Attr msg).valid = true := h

theorem on_safe {msg : Type} (e : String) (m : msg) (h : isSafeAttrName e = true) :
    (Attr.on e m).valid = true := h

theorem signalOn_safe {msg : Type} (n e : String) (m : msg) (h : isSafeAttrName e = true) :
    (Attr.signalOn n e m).valid = true := h

theorem onValue_safe {msg : Type} (e : String) (f : String → msg) (h : isSafeAttrName e = true) :
    (Attr.onValue e f).valid = true := h

theorem valid_value {msg α : Type} [ToString α] (v : α) :
    (Qed.value v : Attr msg).valid = true :=
  attr_nonUrl "value" (toString v) ⟨rfl, rfl⟩

theorem valid_attr_nonUrl {msg α : Type} [ToString α] (k : String) (v : α)
    (h : isSafeAttrName k = true ∧ isUrlAttrName k = false) :
    (Qed.attr k v : Attr msg).valid = true :=
  attr_nonUrl k (toString v) h

theorem valid_onCheck {msg : Type} (f : Bool → msg) :
    (Qed.onCheck f).valid = true := (rfl : isSafeAttrName "change" = true)

theorem valid_vOnCheck {σ msg : Type} (s : σ) (f : σ → Bool → msg) :
    (VAttr.eval s (V.onCheck' f)).valid = true := (rfl : isSafeAttrName "change" = true)

theorem attr_valid_dite_intro {msg : Type} (c : Prop) [Decidable c]
    (a : c → Attr msg) (b : ¬c → Attr msg)
    (ha : ∀ h, (a h).valid = true) (hb : ∀ h, (b h).valid = true) :
    (dite c a b).valid = true := by
  by_cases h : c <;> simp [h, ha, hb]

theorem attr_isLocalCell_dite_eq_false {msg : Type} (c : Prop) [Decidable c]
    (a : c → Attr msg) (b : ¬c → Attr msg)
    (ha : ∀ h, (a h).isLocalCell = false) (hb : ∀ h, (b h).isLocalCell = false) :
    (dite c a b).isLocalCell = false := by
  by_cases h : c <;> simp [h, ha, hb]

theorem validListIn_dite_intro {msg : Type} (ctx : HtmlCtx) (c : Prop) [Decidable c]
    (a : c → List (Html msg)) (b : ¬c → List (Html msg))
    (ha : ∀ h, Html.validListIn ctx (a h) = true) (hb : ∀ h, Html.validListIn ctx (b h) = true) :
    Html.validListIn ctx (dite c a b) = true := by
  by_cases h : c <;> simp [h, ha, hb]

local macro "qed_snu " id:ident k:str : command =>
  `(theorem $id : isSafeAttrName $k = true ∧ isUrlAttrName $k = false := ⟨rfl, rfl⟩)
local macro "qed_sa " id:ident k:str : command =>
  `(theorem $id : isSafeAttrName $k = true := rfl)
local macro "qed_nv " id:ident tag:str : command =>
  `(theorem $id : isVoidTag $tag = false := rfl)

qed_snu snu_dataRole     "data-role"
qed_snu snu_dataQedLink  "data-qed-link"
qed_snu snu_value        "value"
qed_snu snu_placeholder  "placeholder"
qed_snu snu_name         "name"
qed_snu snu_alt          "alt"
qed_snu snu_title        "title"
qed_snu snu_style        "style"
qed_snu snu_type         "type"
qed_snu snu_class        "class"
qed_snu snu_id           "id"
qed_snu snu_for          "for"
qed_snu snu_role         "role"
qed_snu snu_ariaLabel    "aria-label"
qed_snu snu_ariaInvalid  "aria-invalid"
qed_snu snu_ariaLive     "aria-live"
qed_snu snu_rows         "rows"
qed_snu snu_cols         "cols"
qed_snu snu_min          "min"
qed_snu snu_max          "max"
qed_snu snu_step         "step"
qed_snu snu_tabindex     "tabindex"
qed_snu snu_target       "target"
qed_snu snu_rel          "rel"
qed_snu snu_accept       "accept"
qed_snu snu_autocomplete "autocomplete"

qed_sa sa_click     "click"
qed_sa sa_input     "input"
qed_sa sa_change    "change"
qed_sa sa_keydown   "keydown"
qed_sa sa_keyup     "keyup"
qed_sa sa_submit    "submit"
qed_sa sa_blur      "blur"
qed_sa sa_focus     "focus"
qed_sa sa_dblclick  "dblclick"
qed_sa sa_mousedown "mousedown"
qed_sa sa_mouseup   "mouseup"
qed_sa sa_disabled  "disabled"
qed_sa sa_required  "required"
qed_sa sa_checked   "checked"
qed_sa sa_readonly  "readonly"
qed_sa sa_selected  "selected"
qed_sa sa_multiple  "multiple"
qed_sa sa_hidden    "hidden"

private theorem mk_plainBlock (tag : String)
    (hs : isSafeTagName tag = true) (hf : isForbiddenTag tag = false)
    (hc : isContextOnlyTag tag = false) (hi : isInteractiveTag tag = false) (hh : isHeadingTag tag = false)
    (ho : (tag == "svg" || tag == "style" || tag == "textarea" || tag == "select" ||
           tag == "ul" || tag == "ol" || tag == "dl" || tag == "table" ||
           tag == "p" || tag == "a" || tag == "button" || tag == "details" ||
           tag == "summary" || tag == "label" || tag == "form") = false)
    (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } tag =
      some { mode := .normal, inP := false, interactive, inForm } := by
  simp only [Bool.or_eq_false_iff] at ho
  rcases ho with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩,h7⟩,h8⟩,h9⟩,h10⟩,h11⟩,h12⟩,h13⟩,h14⟩,h15⟩
  cases interactive <;> cases inForm <;>
    simp [stepHtmlCtx, hs, hf, hc, hi, hh, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

private theorem mk_plainInline (tag : String)
    (hs : isSafeTagName tag = true) (hf : isForbiddenTag tag = false)
    (hc : isContextOnlyTag tag = false) (hcp : closesPTag tag = false)
    (hi : isInteractiveTag tag = false) (hh : isHeadingTag tag = false)
    (ho : (tag == "svg" || tag == "style" || tag == "textarea" || tag == "select" ||
           tag == "ul" || tag == "ol" || tag == "dl" || tag == "table" ||
           tag == "p" || tag == "a" || tag == "button" || tag == "details" ||
           tag == "summary" || tag == "label" || tag == "form") = false)
    (inP interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive, inForm } tag =
      some { mode := .normal, inP, interactive, inForm } := by
  simp only [Bool.or_eq_false_iff] at ho
  rcases ho with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩,h7⟩,h8⟩,h9⟩,h10⟩,h11⟩,h12⟩,h13⟩,h14⟩,h15⟩
  cases inP <;> cases interactive <;> cases inForm <;>
    simp [stepHtmlCtx, hs, hf, hc, hcp, hi, hh, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

private theorem mk_heading (tag : String)
    (hs : isSafeTagName tag = true) (hf : isForbiddenTag tag = false)
    (hc : isContextOnlyTag tag = false) (hi : isInteractiveTag tag = false)
    (hp : (tag == "p" || isHeadingTag tag) = true)
    (ho : (tag == "svg" || tag == "style" || tag == "textarea" || tag == "select" ||
           tag == "ul" || tag == "ol" || tag == "dl" || tag == "table" ||
           tag == "a" || tag == "button" || tag == "details" ||
           tag == "summary" || tag == "label" || tag == "form") = false)
    (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } tag =
      some { mode := .normal, inP := true, interactive, inForm } := by
  simp only [Bool.or_eq_false_iff] at ho
  rcases ho with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩,h7⟩,h8⟩,h9⟩,h10⟩,h11⟩,h12⟩,h13⟩,h14⟩
  cases interactive <;> cases inForm <;>
    simp [stepHtmlCtx, hs, hf, hc, hi, hp, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]

private theorem mk_interactive (tag : String)
    (hs : isSafeTagName tag = true) (hf : isForbiddenTag tag = false)
    (hc : isContextOnlyTag tag = false) (hcp : closesPTag tag = false) (hh : isHeadingTag tag = false)
    (hint : (tag == "a" || tag == "button" || tag == "details" || tag == "summary") = true)
    (ho : (tag == "svg" || tag == "style" || tag == "textarea" || tag == "select" ||
           tag == "ul" || tag == "ol" || tag == "dl" || tag == "table" ||
           tag == "p" || tag == "form") = false)
    (inP inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive := false, inForm } tag =
      some { mode := .normal, inP, interactive := true, inForm } := by
  simp only [Bool.or_eq_false_iff] at ho
  rcases ho with ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩,h7⟩,h8⟩,h9⟩,h10⟩
  cases inP <;> cases inForm <;>
    simpa [stepHtmlCtx, hs, hf, hc, hcp, hh, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] using hint

private theorem mk_inputLike (tag : String)
    (hs : isSafeTagName tag = true) (hf : isForbiddenTag tag = false)
    (hc : isContextOnlyTag tag = false) (hcp : closesPTag tag = false) (hh : isHeadingTag tag = false)
    (ho : (tag == "svg" || tag == "style" || tag == "textarea" || tag == "select" ||
           tag == "ul" || tag == "ol" || tag == "dl" || tag == "table" ||
           tag == "p" || tag == "a" || tag == "button" || tag == "details" ||
           tag == "summary" || tag == "form") = false)
    (inP inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive := false, inForm } tag =
      some { mode := .normal, inP, interactive := false, inForm } := by
  simp only [Bool.or_eq_false_iff] at ho
  rcases ho with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩,h7⟩,h8⟩,h9⟩,h10⟩,h11⟩,h12⟩,h13⟩,h14⟩
  cases inP <;> cases inForm <;>
    simp [stepHtmlCtx, hs, hf, hc, hcp, hh, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14]

local macro "qed_step_block " id:ident tag:str : command =>
  `(theorem $id (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } $tag =
      some { mode := .normal, inP := false, interactive := i, inForm := f } :=
    mk_plainBlock $tag rfl rfl rfl rfl rfl rfl i f)
local macro "qed_step_inline " id:ident tag:str : command =>
  `(theorem $id (p i f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } $tag =
      some { mode := .normal, inP := p, interactive := i, inForm := f } :=
    mk_plainInline $tag rfl rfl rfl rfl rfl rfl rfl p i f)
local macro "qed_step_heading " id:ident tag:str : command =>
  `(theorem $id (i f : Bool) : stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } $tag =
      some { mode := .normal, inP := true, interactive := i, inForm := f } :=
    mk_heading $tag rfl rfl rfl rfl rfl rfl i f)
local macro "qed_step_inter " id:ident tag:str : command =>
  `(theorem $id (p f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := false, inForm := f } $tag =
      some { mode := .normal, inP := p, interactive := true, inForm := f } :=
    mk_interactive $tag rfl rfl rfl rfl rfl rfl rfl p f)
local macro "qed_step_input " id:ident tag:str : command =>
  `(theorem $id (p f : Bool) : stepHtmlCtx { mode := .normal, inP := p, interactive := false, inForm := f } $tag =
      some { mode := .normal, inP := p, interactive := false, inForm := f } :=
    mk_inputLike $tag rfl rfl rfl rfl rfl rfl p f)
local macro "qed_step_mode " id:ident m1:ident m2:ident tag:str : command =>
  `(theorem $id (p i f : Bool) : stepHtmlCtx { mode := .$m1, inP := p, interactive := i, inForm := f } $tag =
      some { mode := .$m2, inP := false, interactive := i, inForm := f } := by
    have h1 : isSafeTagName $tag = true := rfl; have h2 : isForbiddenTag $tag = false := rfl
    simp [stepHtmlCtx, h1, h2])

qed_step_block step_div "div"
qed_step_block step_section "section"
qed_step_block step_article "article"
qed_step_block step_aside "aside"
qed_step_block step_header "header"
qed_step_block step_footer "footer"
qed_step_block step_main "main"
qed_step_block step_nav "nav"
qed_step_block step_blockquote "blockquote"
qed_step_block step_pre "pre"
qed_step_block step_fieldset "fieldset"
qed_step_block step_figure "figure"
qed_step_block step_figcaption "figcaption"
qed_step_block step_hr "hr"

qed_step_inline step_span "span"
qed_step_inline step_strong "strong"
qed_step_inline step_em "em"
qed_step_inline step_code "code"
qed_step_inline step_small "small"
qed_step_inline step_b "b"
qed_step_inline step_i "i"
qed_step_inline step_u "u"
qed_step_inline step_s "s"
qed_step_inline step_mark "mark"
qed_step_inline step_time "time"
qed_step_inline step_kbd "kbd"
qed_step_inline step_img "img"
qed_step_inline step_br "br"
qed_step_inline step_legend "legend"

qed_step_heading step_p "p"
qed_step_heading step_h1 "h1"
qed_step_heading step_h2 "h2"
qed_step_heading step_h3 "h3"
qed_step_heading step_h4 "h4"
qed_step_heading step_h5 "h5"
qed_step_heading step_h6 "h6"

qed_step_inter step_button "button"
qed_step_inter step_a "a"
qed_step_inter step_summary "summary"
qed_step_input step_input "input"
qed_step_input step_label "label"

theorem step_form :
    stepHtmlCtx { mode := .normal, inP := false, interactive := false, inForm := false } "form" =
      some { mode := .normal, inP := false, interactive := false, inForm := true } := rfl

theorem step_textarea (inP inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive := false, inForm } "textarea" =
      some { mode := .textarea, inP, interactive := true, inForm } := by
  have h1 : isSafeTagName "textarea" = true := rfl; have h2 : isForbiddenTag "textarea" = false := rfl
  have h3 : isContextOnlyTag "textarea" = false := rfl; have h4 : closesPTag "textarea" = false := rfl
  cases inP <;> cases inForm <;> simp [stepHtmlCtx, h1, h2, h3, h4]

theorem step_select (inP inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive := false, inForm } "select" =
      some { mode := .select, inP, interactive := true, inForm } := by
  have h1 : isSafeTagName "select" = true := rfl; have h2 : isForbiddenTag "select" = false := rfl
  have h3 : isContextOnlyTag "select" = false := rfl; have h4 : closesPTag "select" = false := rfl
  cases inP <;> cases inForm <;> simp [stepHtmlCtx, h1, h2, h3, h4]

theorem step_ul (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } "ul" =
      some { mode := .ulOl, inP := false, interactive, inForm } := by
  have h1 : isSafeTagName "ul" = true := rfl; have h2 : isForbiddenTag "ul" = false := rfl
  have h3 : isContextOnlyTag "ul" = false := rfl; have h4 : isInteractiveTag "ul" = false := rfl
  cases interactive <;> cases inForm <;> simp [stepHtmlCtx, h1, h2, h3, h4]

theorem step_ol (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } "ol" =
      some { mode := .ulOl, inP := false, interactive, inForm } := by
  have h1 : isSafeTagName "ol" = true := rfl; have h2 : isForbiddenTag "ol" = false := rfl
  have h3 : isContextOnlyTag "ol" = false := rfl; have h4 : isInteractiveTag "ol" = false := rfl
  cases interactive <;> cases inForm <;> simp [stepHtmlCtx, h1, h2, h3, h4]

theorem step_table (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } "table" =
      some { mode := .table, inP := false, interactive, inForm } := by
  have h1 : isSafeTagName "table" = true := rfl; have h2 : isForbiddenTag "table" = false := rfl
  have h3 : isContextOnlyTag "table" = false := rfl; have h4 : isInteractiveTag "table" = false := rfl
  cases interactive <;> cases inForm <;> simp [stepHtmlCtx, h1, h2, h3, h4]

qed_step_mode step_li ulOl normal "li"
qed_step_mode step_thead table tableSection "thead"
qed_step_mode step_tbody table tableSection "tbody"
qed_step_mode step_tr tableSection tableRow "tr"
qed_step_mode step_td tableRow normal "td"
qed_step_mode step_th tableRow normal "th"

theorem step_option (inP interactive inForm : Bool) :
    stepHtmlCtx { mode := .select, inP, interactive, inForm } "option" =
      some { mode := .option, inP, interactive, inForm } := by
  have h1 : isSafeTagName "option" = true := rfl; have h2 : isForbiddenTag "option" = false := rfl
  simp [stepHtmlCtx, h1, h2]

qed_nv nv_div "div"
qed_nv nv_span "span"
qed_nv nv_p "p"
qed_nv nv_a "a"
qed_nv nv_button "button"
qed_nv nv_form "form"
qed_nv nv_label "label"
qed_nv nv_ul "ul"
qed_nv nv_ol "ol"
qed_nv nv_li "li"
qed_nv nv_h1 "h1"
qed_nv nv_h2 "h2"
qed_nv nv_h3 "h3"
qed_nv nv_h4 "h4"
qed_nv nv_h5 "h5"
qed_nv nv_h6 "h6"
qed_nv nv_section "section"
qed_nv nv_article "article"
qed_nv nv_aside "aside"
qed_nv nv_header "header"
qed_nv nv_footer "footer"
qed_nv nv_main "main"
qed_nv nv_nav "nav"
qed_nv nv_blockquote "blockquote"
qed_nv nv_pre "pre"
qed_nv nv_code "code"
qed_nv nv_strong "strong"
qed_nv nv_em "em"
qed_nv nv_small "small"
qed_nv nv_b "b"
qed_nv nv_i "i"
qed_nv nv_u "u"
qed_nv nv_s "s"
qed_nv nv_mark "mark"
qed_nv nv_time "time"
qed_nv nv_kbd "kbd"
qed_nv nv_table "table"
qed_nv nv_thead "thead"
qed_nv nv_tbody "tbody"
qed_nv nv_tr "tr"
qed_nv nv_td "td"
qed_nv nv_th "th"
qed_nv nv_select "select"
qed_nv nv_option "option"
qed_nv nv_textarea "textarea"
qed_nv nv_fieldset "fieldset"
qed_nv nv_legend "legend"
qed_nv nv_figure "figure"
qed_nv nv_figcaption "figcaption"
qed_nv nv_summary "summary"

open Lean

private def mkStrMap (entries : Array (String × Name)) : Std.HashMap String Name :=
  entries.foldl (fun m (k, v) => m.insert k v) {}

def safeNonUrlAttrMap : Std.HashMap String Name := mkStrMap #[
  ("data-role", ``snu_dataRole), ("data-qed-link", ``snu_dataQedLink), ("value", ``snu_value),
  ("placeholder", ``snu_placeholder), ("name", ``snu_name), ("alt", ``snu_alt), ("title", ``snu_title),
  ("style", ``snu_style), ("type", ``snu_type), ("class", ``snu_class), ("id", ``snu_id), ("for", ``snu_for),
  ("role", ``snu_role), ("aria-label", ``snu_ariaLabel), ("aria-invalid", ``snu_ariaInvalid),
  ("aria-live", ``snu_ariaLive), ("rows", ``snu_rows), ("cols", ``snu_cols), ("min", ``snu_min),
  ("max", ``snu_max), ("step", ``snu_step), ("tabindex", ``snu_tabindex), ("target", ``snu_target),
  ("rel", ``snu_rel), ("accept", ``snu_accept), ("autocomplete", ``snu_autocomplete)]

def safeAttrMap : Std.HashMap String Name := mkStrMap #[
  ("click", ``sa_click), ("input", ``sa_input), ("change", ``sa_change), ("keydown", ``sa_keydown),
  ("keyup", ``sa_keyup), ("submit", ``sa_submit), ("blur", ``sa_blur), ("focus", ``sa_focus),
  ("dblclick", ``sa_dblclick), ("mousedown", ``sa_mousedown), ("mouseup", ``sa_mouseup),
  ("disabled", ``sa_disabled), ("required", ``sa_required), ("checked", ``sa_checked),
  ("readonly", ``sa_readonly), ("selected", ``sa_selected), ("multiple", ``sa_multiple), ("hidden", ``sa_hidden)]

def nonVoidTagMap : Std.HashMap String Name := mkStrMap #[
  ("div", ``nv_div), ("span", ``nv_span), ("p", ``nv_p), ("a", ``nv_a), ("button", ``nv_button),
  ("form", ``nv_form), ("label", ``nv_label), ("ul", ``nv_ul), ("ol", ``nv_ol), ("li", ``nv_li),
  ("h1", ``nv_h1), ("h2", ``nv_h2), ("h3", ``nv_h3), ("h4", ``nv_h4), ("h5", ``nv_h5), ("h6", ``nv_h6),
  ("section", ``nv_section), ("article", ``nv_article), ("aside", ``nv_aside), ("header", ``nv_header),
  ("footer", ``nv_footer), ("main", ``nv_main), ("nav", ``nv_nav), ("blockquote", ``nv_blockquote),
  ("pre", ``nv_pre), ("code", ``nv_code), ("strong", ``nv_strong), ("em", ``nv_em), ("small", ``nv_small),
  ("b", ``nv_b), ("i", ``nv_i), ("u", ``nv_u), ("s", ``nv_s), ("mark", ``nv_mark), ("time", ``nv_time),
  ("kbd", ``nv_kbd), ("table", ``nv_table), ("thead", ``nv_thead), ("tbody", ``nv_tbody), ("tr", ``nv_tr),
  ("td", ``nv_td), ("th", ``nv_th), ("select", ``nv_select), ("option", ``nv_option), ("textarea", ``nv_textarea),
  ("fieldset", ``nv_fieldset), ("legend", ``nv_legend), ("figure", ``nv_figure), ("figcaption", ``nv_figcaption),
  ("summary", ``nv_summary)]

private def stepBlockMap : Std.HashMap String Name := mkStrMap #[
  ("div", ``step_div), ("section", ``step_section), ("article", ``step_article), ("aside", ``step_aside),
  ("header", ``step_header), ("footer", ``step_footer), ("main", ``step_main), ("nav", ``step_nav),
  ("blockquote", ``step_blockquote), ("pre", ``step_pre), ("fieldset", ``step_fieldset),
  ("figure", ``step_figure), ("figcaption", ``step_figcaption), ("hr", ``step_hr),
  ("p", ``step_p), ("h1", ``step_h1), ("h2", ``step_h2), ("h3", ``step_h3), ("h4", ``step_h4),
  ("h5", ``step_h5), ("h6", ``step_h6), ("ul", ``step_ul), ("ol", ``step_ol), ("table", ``step_table)]

private def stepInlineMap : Std.HashMap String Name := mkStrMap #[
  ("span", ``step_span), ("strong", ``step_strong), ("em", ``step_em), ("code", ``step_code),
  ("small", ``step_small), ("b", ``step_b), ("i", ``step_i), ("u", ``step_u), ("s", ``step_s),
  ("mark", ``step_mark), ("time", ``step_time), ("kbd", ``step_kbd), ("img", ``step_img),
  ("br", ``step_br), ("legend", ``step_legend)]

private def stepNonInterMap : Std.HashMap String Name := mkStrMap #[
  ("button", ``step_button), ("a", ``step_a), ("summary", ``step_summary),
  ("input", ``step_input), ("label", ``step_label), ("textarea", ``step_textarea), ("select", ``step_select)]

def proveStepHtmlCtx (ctxV : HtmlCtx) (tagS : String) (childCtxE : Expr) : Expr :=
  let bP := toExpr ctxV.inP
  let bI := toExpr ctxV.interactive
  let bF := toExpr ctxV.inForm
  match ctxV.mode with
  | .normal =>
      if !ctxV.inP then
        if let some lm := stepBlockMap[tagS]? then mkApp2 (mkConst lm) bI bF
        else if !ctxV.interactive && !ctxV.inForm && tagS == "form" then mkConst ``step_form
        else if !ctxV.interactive then
          if let some lm := stepNonInterMap[tagS]? then mkApp2 (mkConst lm) bP bF
          else if let some lm := stepInlineMap[tagS]? then mkApp3 (mkConst lm) bP bI bF
          else rflStep childCtxE
        else if let some lm := stepInlineMap[tagS]? then mkApp3 (mkConst lm) bP bI bF
        else rflStep childCtxE
      else if !ctxV.interactive then
        if let some lm := stepNonInterMap[tagS]? then mkApp2 (mkConst lm) bP bF
        else if let some lm := stepInlineMap[tagS]? then mkApp3 (mkConst lm) bP bI bF
        else rflStep childCtxE
      else if let some lm := stepInlineMap[tagS]? then mkApp3 (mkConst lm) bP bI bF
      else rflStep childCtxE
  | .ulOl         => if tagS == "li"     then mkApp3 (mkConst ``step_li) bP bI bF     else rflStep childCtxE
  | .table        => if tagS == "thead"  then mkApp3 (mkConst ``step_thead) bP bI bF
                     else if tagS == "tbody" then mkApp3 (mkConst ``step_tbody) bP bI bF else rflStep childCtxE
  | .tableSection => if tagS == "tr"     then mkApp3 (mkConst ``step_tr) bP bI bF     else rflStep childCtxE
  | .tableRow     => if tagS == "td"     then mkApp3 (mkConst ``step_td) bP bI bF
                     else if tagS == "th" then mkApp3 (mkConst ``step_th) bP bI bF    else rflStep childCtxE
  | .select       => if tagS == "option" then mkApp3 (mkConst ``step_option) bP bI bF else rflStep childCtxE
  | _             => rflStep childCtxE
where
  rflStep (childCtxE : Expr) : Expr :=
    mkApp2 (mkConst ``Eq.refl [Level.one])
      (mkApp (mkConst ``Option [Level.zero]) (mkConst ``HtmlCtx))
      (mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``HtmlCtx) childCtxE)

private def qedAttrWrapperMap : Std.HashMap Name (Name × String × Name) :=
  #[
    (``Qed.role,          (``attr_nonUrl,  "data-role",   ``snu_dataRole)),
    (``Qed.placeholder,   (``attr_nonUrl,  "placeholder", ``snu_placeholder)),
    (``Qed.name,          (``attr_nonUrl,  "name",        ``snu_name)),
    (``Qed.alt,           (``attr_nonUrl,  "alt",         ``snu_alt)),
    (``Qed.title,         (``attr_nonUrl,  "title",       ``snu_title)),
    (``Qed.style,         (``attr_nonUrl,  "style",       ``snu_style)),
    (``Qed.type',         (``attr_nonUrl,  "type",        ``snu_type)),
    (``Qed.onClick,       (``on_safe,      "click",       ``sa_click)),
    (``Qed.onSubmit,      (``on_safe,      "submit",      ``sa_submit)),
    (``Qed.onBlur,        (``on_safe,      "blur",        ``sa_blur)),
    (``Qed.onFocus,       (``on_safe,      "focus",       ``sa_focus)),
    (``Qed.onDoubleClick, (``on_safe,      "dblclick",    ``sa_dblclick)),
    (``Qed.onMouseDown,   (``on_safe,      "mousedown",   ``sa_mousedown)),
    (``Qed.onMouseUp,     (``on_safe,      "mouseup",     ``sa_mouseup)),
    (``Qed.onInput,       (``onValue_safe, "input",       ``sa_input)),
    (``Qed.onChange,      (``onValue_safe, "input",       ``sa_input)),
    (``Qed.onKeydown,     (``onValue_safe, "keydown",     ``sa_keydown)),
    (``Qed.onKeyup,       (``onValue_safe, "keyup",       ``sa_keyup)),
    (``Qed.disabled,      (``flag_safe,    "disabled",    ``sa_disabled)),
    (``Qed.required,      (``flag_safe,    "required",    ``sa_required)),
    (``Qed.checked,       (``flag_safe,    "checked",     ``sa_checked)),
    (``Qed.readOnly,      (``flag_safe,    "readonly",    ``sa_readonly))
  ].foldl (fun m (k, v) => m.insert k v) {}

def fastAttrValidProof? (msgTy a : Expr) : Option Expr :=
  let a := a.consumeMData
  let args := a.getAppArgs
  let strLit? (e : Expr) : Option String := match e.consumeMData with | .lit (.strVal s) => some s | _ => none
  match a.getAppFn.constName? with
  | some fn =>
      if fn == ``VAttr.eval && args.size == 4 &&
          (args[3]!).consumeMData.getAppFn.constName? == some ``V.onCheck' then
        let vaArgs := args[3]!.consumeMData.getAppArgs
        if vaArgs.size == 3 then some (mkApp4 (mkConst ``valid_vOnCheck) args[0]! args[1]! args[2]! vaArgs[2]!)
        else none
      else if fn == ``Qed.value && args.size == 4 then
        some (mkApp4 (mkConst ``valid_value) args[0]! args[1]! args[2]! args[3]!)
      else if fn == ``Qed.onCheck && args.size == 2 then
        some (mkApp2 (mkConst ``valid_onCheck) args[0]! args[1]!)
      else if args.size == 2 then
        qedAttrWrapperMap[fn]?.map fun (comb, key, lem) =>
          mkApp4 (mkConst comb) msgTy (toExpr key) args[1]! (mkConst lem)
      else if fn == ``Attr.attr && args.size == 3 then
        (strLit? args[1]! >>= (safeNonUrlAttrMap[·]?)).map fun lem =>
          mkApp4 (mkConst ``attr_nonUrl) msgTy args[1]! args[2]! (mkConst lem)
      else if fn == ``Attr.signalAttr && args.size == 4 then
        (strLit? args[2]! >>= (safeNonUrlAttrMap[·]?)).map fun lem =>
          mkAppN (mkConst ``signalAttr_nonUrl) #[msgTy, args[1]!, args[2]!, args[3]!, mkConst lem]
      else if fn == ``Qed.attr && args.size == 5 then
        (strLit? args[3]! >>= (safeNonUrlAttrMap[·]?)).map fun lem =>
          mkAppN (mkConst ``valid_attr_nonUrl) #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, mkConst lem]
      else if fn == ``Attr.flag && args.size == 3 then
        (strLit? args[1]! >>= (safeAttrMap[·]?)).map fun lem =>
          mkApp4 (mkConst ``flag_safe) msgTy args[1]! args[2]! (mkConst lem)
      else if fn == ``Attr.on && args.size == 3 then
        (strLit? args[1]! >>= (safeAttrMap[·]?)).map fun lem =>
          mkApp4 (mkConst ``on_safe) msgTy args[1]! args[2]! (mkConst lem)
      else if fn == ``Attr.signalOn && args.size == 4 then
        (strLit? args[2]! >>= (safeAttrMap[·]?)).map fun lem =>
          mkAppN (mkConst ``signalOn_safe) #[msgTy, args[1]!, args[2]!, args[3]!, mkConst lem]
      else if fn == ``Attr.onValue && args.size == 3 then
        (strLit? args[1]! >>= (safeAttrMap[·]?)).map fun lem =>
          mkApp4 (mkConst ``onValue_safe) msgTy args[1]! args[2]! (mkConst lem)
      else none
  | none => none

end Qed.ValidLemmas
