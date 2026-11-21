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

theorem valid_attr_nonUrl {msg α : Type} [ToString α] (k : String) (v : α)
    (h : isSafeAttrName k = true ∧ isUrlAttrName k = false) :
    (Qed.attr k v : Attr msg).valid = true :=
  attr_nonUrl k (toString v) h

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

private def mkStrMap (entries : Array (String × Lean.Name)) : Std.HashMap String Lean.Name :=
  entries.foldl (fun m (k, v) => m.insert k v) {}

private theorem mk_nv (t : String) (h : isVoidTagFast t = false) : isVoidTag t = false := by
  rw [isVoidTag_eq_fast]; exact h

private def tagNormalOk (t : String) (reqNoCloseP reqNonInter wantHead wantInter : Bool) : Bool :=
  isSafeTagName t && !isForbiddenTag t && !isContextOnlyTag t &&
  !(t == "svg" || t == "style" || t == "textarea" || t == "select" ||
    t == "ul" || t == "ol" || t == "dl" || t == "table") && !(t == "form") &&
  (!reqNoCloseP || !closesPTag t) &&
  (!reqNonInter || !(isInteractiveTag t || t == "label")) &&
  ((t == "p" || isHeadingTag t) == wantHead) &&
  ((t == "a" || t == "button" || t == "details" || t == "summary") == wantInter)

private theorem mk_stepNormal (t : String) (reqNoCloseP reqNonInter wantHead wantInter : Bool)
    (h : tagNormalOk t reqNoCloseP reqNonInter wantHead wantInter = true)
    (p i f p' i' : Bool)
    (hp : (p && !reqNoCloseP) = false) (hi : (i && !reqNonInter) = false)
    (hp' : (p || wantHead) = p') (hi' : (i || wantInter) = i') :
    stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } t =
      some { mode := .normal, inP := p', interactive := i', inForm := f } := by
  simp only [tagNormalOk, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hs, hfb⟩, hc⟩, hm⟩, hfrm⟩, hcp⟩, hni⟩, hhd⟩, hint⟩
  simp only [Bool.or_eq_false_iff] at hm
  rcases hm with ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
  have hp0 : (p && closesPTag t) = false := by cases p <;> cases reqNoCloseP <;> simp_all
  have hi0 : (i && (isInteractiveTag t || t == "label")) = false := by
    cases i <;> cases reqNonInter <;> simp_all
  have hP : (p || t == "p" || isHeadingTag t) = p' := by rw [Bool.or_assoc, hhd, hp']
  have hI : (i || t == "a" || t == "button" || t == "details" || t == "summary") = i' := by
    simp only [Bool.or_assoc] at hint ⊢; rw [hint, hi']
  simp only [stepHtmlCtx, hs, hfb, hc, hp0, hfrm, Bool.or_false, hi0, h1, h2, h3, h4, h5, h6, h7, h8, hP, hI,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

private theorem mk_modeNormal (t : String) (m2 : TagMode) (interOut : Bool)
    (h : (isSafeTagName t && !isForbiddenTag t && !isContextOnlyTag t &&
      !(t == "svg" || t == "style" || t == "dl" || t == "form") &&
      (if interOut then !closesPTag t else !(isInteractiveTag t || t == "label"))) = true)
    (hstep : (if interOut then
                if t == "textarea" then some TagMode.textarea
                else if t == "select" then some TagMode.select else none
              else
                if t == "ul" || t == "ol" then some TagMode.ulOl
                else if t == "table" then some TagMode.table else none) = some m2)
    (p i f : Bool) (hp : (p && !interOut) = false) (hi : (i && interOut) = false) :
    stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } t =
      some { mode := m2, inP := p, interactive := i || interOut, inForm := f } := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at h
  rcases h with ⟨⟨⟨⟨hs, hfb⟩, hc⟩, ⟨⟨⟨hsvg, hsty⟩, hdl⟩, hfrm⟩⟩, hguard⟩
  have hp0 : (p && closesPTag t) = false := by cases p <;> cases interOut <;> simp_all
  have hi0 : (i && (isInteractiveTag t || t == "label")) = false := by
    cases i <;> cases interOut <;> simp_all
  simp only [stepHtmlCtx, hs, hfb, hc, hp0, hfrm, Bool.or_false, hi0, hsvg, hsty, hdl,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  cases interOut with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true', Bool.or_eq_false_iff, isInteractiveTag] at hguard hstep
      have hta := hguard.1.1.1.2
      have hsel := hguard.1.1.1.1.2
      simp only [hta, hsel, Bool.false_eq_true, ↓reduceIte, Bool.or_false]
      repeat (first | (cases hstep; done) | (split at hstep <;> simp only [*, ↓reduceIte] <;> try (cases hstep; rfl)))
  | true =>
      have hiF : i = false := by cases i <;> simp_all
      subst hiF
      simp only [↓reduceIte, Bool.false_or] at hstep ⊢
      repeat (first | (cases hstep; done) | (split at hstep <;> simp only [*, ↓reduceIte] <;> try (cases hstep; rfl)))

private theorem mk_modeStep (m1 m2 : TagMode) (tag : String) (resetP : Bool)
    (hs : isSafeTagName tag = true) (hf : isForbiddenTag tag = false)
    (hstep : (match m1 with
      | .ulOl => if tag == "li" then some (TagMode.normal, true) else none
      | .table => if tag == "caption" then some (TagMode.normal, true)
                  else if tag == "colgroup" then some (TagMode.colgroup, true)
                  else if tag == "thead" || tag == "tbody" || tag == "tfoot" then some (TagMode.tableSection, true)
                  else none
      | .tableSection => if tag == "tr" then some (TagMode.tableRow, true) else none
      | .tableRow => if tag == "td" || tag == "th" then some (TagMode.normal, true) else none
      | .select => if tag == "option" then some (TagMode.option, false) else none
      | _ => none) = some (m2, resetP))
    (p i f : Bool) :
    stepHtmlCtx { mode := m1, inP := p, interactive := i, inForm := f } tag =
      some { mode := m2, inP := if resetP then false else p, interactive := i, inForm := f } := by
  cases m1 <;>
    simp only [stepHtmlCtx, hs, hf, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte] at hstep ⊢ <;>
    repeat (first | (cases hstep; done) | (split at hstep <;> simp only [*, ↓reduceIte] <;> try (cases hstep; rfl)))

local macro "genValidTable " kind:ident mapDef:ident " [" keys:str,* "]" : command => do
  let camel (pfx s : String) : String :=
    match s.splitOn "-" with
    | [] => pfx
    | h :: t => pfx ++ h ++ String.join (t.map fun p =>
        match p.toList with | [] => "" | c :: cs => String.ofList (c.toUpper :: cs))
  let mut cmds := #[]
  let mut entries : Array (Lean.TSyntax `term) := #[]
  let k := kind.getId.eraseMacroScopes.toString
  let mkRef (n : String) := Lean.mkIdentFrom kind (Lean.Name.mkSimple n)
  for sLit in keys.getElems do
    let s := sLit.getString
    let pfx := match k with
      | "snu" => "snu_" | "sa" => "sa_" | "nv" => "nv_" | _ => "step_"
    let thmStr := camel pfx s
    let thm := Lean.mkIdentFrom sLit (Lean.Name.mkSimple thmStr)
    let fullName := Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkSimple "Qed") "ValidLemmas") thmStr
    entries := entries.push (← `(($sLit, $(Lean.quote fullName))))
    let cmd ← match k with
      | "snu" => `(command| theorem $thm : isSafeAttrName $sLit = true ∧ isUrlAttrName $sLit = false := ⟨rfl, rfl⟩)
      | "sa"  => `(command| theorem $thm : isSafeAttrName $sLit = true := rfl)
      | "nv"  => `(command| theorem $thm : isVoidTag $sLit = false := $(mkRef "mk_nv") $sLit rfl)
      | "block" =>
          `(command| theorem $thm (i f : Bool) :
              stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } $sLit =
                some { mode := .normal, inP := false, interactive := i, inForm := f } :=
              $(mkRef "mk_stepNormal") $sLit false true false false rfl false i f false i rfl (Bool.and_false i) rfl (Bool.or_false i))
      | "inline" =>
          `(command| theorem $thm (p i f : Bool) :
              stepHtmlCtx { mode := .normal, inP := p, interactive := i, inForm := f } $sLit =
                some { mode := .normal, inP := p, interactive := i, inForm := f } :=
              $(mkRef "mk_stepNormal") $sLit true true false false rfl p i f p i (Bool.and_false p) (Bool.and_false i) (Bool.or_false p) (Bool.or_false i))
      | "heading" =>
          `(command| theorem $thm (i f : Bool) :
              stepHtmlCtx { mode := .normal, inP := false, interactive := i, inForm := f } $sLit =
                some { mode := .normal, inP := true, interactive := i, inForm := f } :=
              $(mkRef "mk_stepNormal") $sLit false true true false rfl false i f true i rfl (Bool.and_false i) rfl (Bool.or_false i))
      | "inter" =>
          `(command| theorem $thm (p f : Bool) :
              stepHtmlCtx { mode := .normal, inP := p, interactive := false, inForm := f } $sLit =
                some { mode := .normal, inP := p, interactive := true, inForm := f } :=
              $(mkRef "mk_stepNormal") $sLit true false false true rfl p false f p true (Bool.and_false p) rfl (Bool.or_false p) rfl)
      | "input" =>
          `(command| theorem $thm (p f : Bool) :
              stepHtmlCtx { mode := .normal, inP := p, interactive := false, inForm := f } $sLit =
                some { mode := .normal, inP := p, interactive := false, inForm := f } :=
              $(mkRef "mk_stepNormal") $sLit true false false false rfl p false f p false (Bool.and_false p) rfl (Bool.or_false p) rfl)
      | _ => Lean.Macro.throwUnsupported
    cmds := cmds.push cmd
  if k == "snu" || k == "sa" || k == "nv" || k == "inline" then
    cmds := cmds.push (← `(command| def $mapDef : Std.HashMap String Lean.Name := mkStrMap #[$entries,*]))
  else
    cmds := cmds.push (← `(command| private def $mapDef : Array (String × Lean.Name) := #[$entries,*]))
  return ⟨Lean.mkNullNode cmds⟩

genValidTable snu safeNonUrlAttrMap [
  "data-role", "data-qed-link", "value", "placeholder", "name", "alt", "title", "style", "type",
  "class", "id", "for", "role", "aria-label", "aria-invalid", "aria-live", "rows", "cols",
  "min", "max", "step", "tabindex", "target", "rel", "accept", "autocomplete"]

genValidTable sa safeAttrMap [
  "click", "input", "change", "keydown", "keyup", "submit", "blur", "focus", "dblclick",
  "mousedown", "mouseup", "disabled", "required", "checked", "readonly", "selected", "multiple", "hidden"]

theorem valid_value {msg α : Type} [ToString α] (v : α) : (Qed.value v : Attr msg).valid = true :=
  attr_nonUrl "value" (toString v) snu_value
theorem valid_onCheck {msg : Type} (f : Bool → msg) : (Qed.onCheck f).valid = true := sa_change
theorem valid_vOnCheck {σ msg : Type} (s : σ) (f : σ → Bool → msg) :
    (VAttr.eval s (V.onCheck' f)).valid = true := sa_change

genValidTable block stepPlainBlockEntries [
  "div", "section", "article", "aside", "header", "footer", "main", "nav",
  "blockquote", "pre", "fieldset", "figure", "figcaption", "hr"]

genValidTable inline stepInlineMap [
  "span", "strong", "em", "code", "small", "b", "i", "u", "s", "mark", "time", "kbd", "img", "br", "legend"]

genValidTable heading stepHeadingEntries ["p", "h1", "h2", "h3", "h4", "h5", "h6"]
genValidTable inter stepInterEntries ["button", "a", "summary"]
genValidTable input stepInputEntries ["input", "label"]

theorem step_form :
    stepHtmlCtx { mode := .normal, inP := false, interactive := false, inForm := false } "form" =
      some { mode := .normal, inP := false, interactive := false, inForm := true } := rfl
theorem step_textarea (inP inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive := false, inForm } "textarea" =
      some { mode := .textarea, inP, interactive := true, inForm } :=
  mk_modeNormal "textarea" .textarea true rfl rfl inP false inForm (by simp) rfl
theorem step_select (inP inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP, interactive := false, inForm } "select" =
      some { mode := .select, inP, interactive := true, inForm } :=
  mk_modeNormal "select" .select true rfl rfl inP false inForm (by simp) rfl
theorem step_ul (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } "ul" =
      some { mode := .ulOl, inP := false, interactive, inForm } := by
  simpa using mk_modeNormal "ul" .ulOl false rfl rfl false interactive inForm rfl (by simp)
theorem step_ol (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } "ol" =
      some { mode := .ulOl, inP := false, interactive, inForm } := by
  simpa using mk_modeNormal "ol" .ulOl false rfl rfl false interactive inForm rfl (by simp)
theorem step_table (interactive inForm : Bool) :
    stepHtmlCtx { mode := .normal, inP := false, interactive, inForm } "table" =
      some { mode := .table, inP := false, interactive, inForm } := by
  simpa using mk_modeNormal "table" .table false rfl rfl false interactive inForm rfl (by simp)

theorem step_li (p i f : Bool) : stepHtmlCtx { mode := .ulOl, inP := p, interactive := i, inForm := f } "li" = some { mode := .normal, inP := false, interactive := i, inForm := f } :=
  mk_modeStep .ulOl .normal "li" true rfl rfl rfl p i f
theorem step_thead (p i f : Bool) : stepHtmlCtx { mode := .table, inP := p, interactive := i, inForm := f } "thead" = some { mode := .tableSection, inP := false, interactive := i, inForm := f } :=
  mk_modeStep .table .tableSection "thead" true rfl rfl rfl p i f
theorem step_tbody (p i f : Bool) : stepHtmlCtx { mode := .table, inP := p, interactive := i, inForm := f } "tbody" = some { mode := .tableSection, inP := false, interactive := i, inForm := f } :=
  mk_modeStep .table .tableSection "tbody" true rfl rfl rfl p i f
theorem step_tr (p i f : Bool) : stepHtmlCtx { mode := .tableSection, inP := p, interactive := i, inForm := f } "tr" = some { mode := .tableRow, inP := false, interactive := i, inForm := f } :=
  mk_modeStep .tableSection .tableRow "tr" true rfl rfl rfl p i f
theorem step_td (p i f : Bool) : stepHtmlCtx { mode := .tableRow, inP := p, interactive := i, inForm := f } "td" = some { mode := .normal, inP := false, interactive := i, inForm := f } :=
  mk_modeStep .tableRow .normal "td" true rfl rfl rfl p i f
theorem step_th (p i f : Bool) : stepHtmlCtx { mode := .tableRow, inP := p, interactive := i, inForm := f } "th" = some { mode := .normal, inP := false, interactive := i, inForm := f } :=
  mk_modeStep .tableRow .normal "th" true rfl rfl rfl p i f
theorem step_option (inP interactive inForm : Bool) :
    stepHtmlCtx { mode := .select, inP, interactive, inForm } "option" =
      some { mode := .option, inP, interactive, inForm } :=
  mk_modeStep .select .option "option" false rfl rfl rfl inP interactive inForm

genValidTable nv nonVoidTagMap [
  "div", "span", "p", "a", "button", "form", "label", "ul", "ol", "li",
  "h1", "h2", "h3", "h4", "h5", "h6", "section", "article", "aside", "header", "footer", "main", "nav",
  "blockquote", "pre", "code", "strong", "em", "small", "b", "i", "u", "s", "mark", "time", "kbd",
  "table", "thead", "tbody", "tr", "td", "th", "select", "option", "textarea", "fieldset", "legend",
  "figure", "figcaption", "summary"]

open Lean

private def stepBlockMap : Std.HashMap String Name :=
  mkStrMap (stepPlainBlockEntries ++ stepHeadingEntries ++ #[("ul", ``step_ul), ("ol", ``step_ol), ("table", ``step_table)])

private def stepNonInterMap : Std.HashMap String Name :=
  mkStrMap (stepInterEntries ++ stepInputEntries ++ #[("textarea", ``step_textarea), ("select", ``step_select)])

def proveStepHtmlCtx (ctxV : HtmlCtx) (tagS : String) (childCtxE : Expr) : Expr :=
  let bP := toExpr ctxV.inP
  let bI := toExpr ctxV.interactive
  let bF := toExpr ctxV.inForm
  match ctxV.mode with
  | .normal =>
      if !ctxV.inP then
        if let some lm := stepBlockMap[tagS]? then mkApp2 (mkConst lm) bI bF
        else if !ctxV.interactive && !ctxV.inForm && tagS == "form" then mkConst ``step_form
        else normalInlineOrInter bP bI bF
      else normalInlineOrInter bP bI bF
  | .ulOl         => if tagS == "li"     then mkApp3 (mkConst ``step_li) bP bI bF     else rflStep childCtxE
  | .table        => if tagS == "thead"  then mkApp3 (mkConst ``step_thead) bP bI bF
                     else if tagS == "tbody" then mkApp3 (mkConst ``step_tbody) bP bI bF else rflStep childCtxE
  | .tableSection => if tagS == "tr"     then mkApp3 (mkConst ``step_tr) bP bI bF     else rflStep childCtxE
  | .tableRow     => if tagS == "td"     then mkApp3 (mkConst ``step_td) bP bI bF
                     else if tagS == "th" then mkApp3 (mkConst ``step_th) bP bI bF    else rflStep childCtxE
  | .select       => if tagS == "option" then mkApp3 (mkConst ``step_option) bP bI bF else rflStep childCtxE
  | _             => rflStep childCtxE
where
  normalInlineOrInter (bP bI bF : Expr) : Expr :=
    if let some lm := if !ctxV.interactive then stepNonInterMap[tagS]? else none then mkApp2 (mkConst lm) bP bF
    else if let some lm := stepInlineMap[tagS]? then mkApp3 (mkConst lm) bP bI bF
    else rflStep childCtxE
  rflStep (childCtxE : Expr) : Expr :=
    mkApp2 (mkConst ``Eq.refl [Level.one])
      (mkApp (mkConst ``Option [Level.zero]) (mkConst ``HtmlCtx))
      (mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``HtmlCtx) childCtxE)

def qedAttrWrapperMap : Std.HashMap Name (Name × String × Name) :=
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

private def fastAttrCtorMap : Std.HashMap Name (Nat × Nat × Bool × Name) :=
  #[
    (``Attr.attr,       (3, 1, true,  ``attr_nonUrl)),
    (``Attr.signalAttr, (4, 2, true,  ``signalAttr_nonUrl)),
    (``Attr.flag,       (3, 1, false, ``flag_safe)),
    (``Attr.on,         (3, 1, false, ``on_safe)),
    (``Attr.signalOn,   (4, 2, false, ``signalOn_safe)),
    (``Attr.onValue,    (3, 1, false, ``onValue_safe))
  ].foldl (fun m (k, v) => m.insert k v) {}

def fastAttrValidProof? (msgTy a : Expr) : Option Expr :=
  let a := a.consumeMData
  let args := a.getAppArgs
  let strLit? (e : Expr) : Option String := match e.consumeMData with | .lit (.strVal s) => some s | _ => none
  a.getAppFn.constName?.bind fun fn =>
    match fn, args.size with
    | ``VAttr.eval, 4 =>
        let va := args[3]!.consumeMData
        if va.getAppFn.constName? == some ``V.onCheck' && va.getAppArgs.size == 3 then
          some (mkApp4 (mkConst ``valid_vOnCheck) args[0]! args[1]! args[2]! va.getAppArgs[2]!)
        else none
    | ``Qed.value, 4 => some (mkApp4 (mkConst ``valid_value) args[0]! args[1]! args[2]! args[3]!)
    | ``Qed.onCheck, 2 => some (mkApp2 (mkConst ``valid_onCheck) args[0]! args[1]!)
    | ``Qed.attr, 5 =>
        (strLit? args[3]! >>= (safeNonUrlAttrMap[·]?)).map fun lem =>
          mkAppN (mkConst ``valid_attr_nonUrl) #[args[0]!, args[1]!, args[2]!, args[3]!, args[4]!, mkConst lem]
    | _, 2 =>
        qedAttrWrapperMap[fn]?.map fun (comb, key, lem) =>
          mkApp4 (mkConst comb) msgTy (toExpr key) args[1]! (mkConst lem)
    | _, sz =>
        fastAttrCtorMap[fn]?.bind fun (arity, keyIdx, nonUrl, thm) =>
          if sz != arity then none
          else
            let tbl := if nonUrl then safeNonUrlAttrMap else safeAttrMap
            (strLit? args[keyIdx]! >>= (tbl[·]?)).map fun lem =>
              mkAppN (mkConst thm) (#[msgTy] ++ args.extract 1 arity ++ #[mkConst lem])

end Qed.ValidLemmas
