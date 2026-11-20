import Qed.Notation
import Qed.Lang
import Qed.Field
import Qed.Json
import Qed.Proto
import Qed.Date
import Qed.Schema.Registry
import Lean

namespace Qed

structure Codec (α : Type) where
  parse        : String → Option α
  render       : {msg : Type} → (raw : String) → (set : String → msg) → Html msg
  valid        : α → Prop
  dec          : DecidablePred valid
  inForm       : Bool := true
  wrapLabel    : Bool := true
  render_valid : ∀ {msg : Type} (inForm : Bool) (raw : String) (set : String → msg),
                   Html.validIn ⟨.normal, false, false, inForm⟩ (render raw set) = true

@[reducible] def Codec.Val {α : Type} (_ : Codec α) : Type := α

namespace Codec

def refine (c : Codec α) (p : α → Prop) [DecidablePred p] : Codec α :=
  { c with valid := p, dec := inferInstance }

def jsonOnly (c : Codec α) : Codec α := { c with inForm := false }

def run (c : Codec α) (raw : String) : Option (Field c.valid) :=
  haveI := c.dec
  match c.parse raw with
  | some a => if h : c.valid a then some ⟨a, h⟩ else none
  | none   => none

theorem isSome_run (c : Codec α) (raw : String) :
    (c.run raw).isSome = true ↔ ∃ a, c.parse raw = some a ∧ c.valid a := by
  haveI := c.dec
  unfold Codec.run
  cases hp : c.parse raw with
  | none   => simp
  | some a => by_cases hv : c.valid a <;> simp [hv]

def fromJsonField {α} (c : Codec α) [FromJsonField α] (j : Json) (key : String) :
    Except String (Field c.valid) :=
  haveI := c.dec
  match (FromJsonField.fromField j key : Except String α) with
  | .error e => .error e
  | .ok a    => if h : c.valid a then .ok ⟨a, h⟩ else .error s!"{key}: failed validation"

@[simp] theorem fromJsonField_of_field {α : Type} (c : Codec α) [LawfulJson α]
    (j : Json) (k : String) (f : Field c.valid)
    (h : j.field k = .ok (toJson f.val)) :
    c.fromJsonField j k = .ok f := by
  rcases f with ⟨val, hok⟩
  simp [Codec.fromJsonField, LawfulJson.fromField_of_field j k val h, hok]

def fromProtoField {α} (c : Codec α) [FromProtoField α] (k : Nat) (fs : List (Nat × Proto.WireVal)) :
    Except String (Field c.valid) :=
  haveI := c.dec
  match (FromProtoField.decodeProtoField k fs : Except String α) with
  | .error e => .error e
  | .ok a    => if h : c.valid a then .ok ⟨a, h⟩ else .error s!"field {k}: failed validation"

theorem fromProtoField_of_field {α : Type} (c : Codec α) [FromProtoField α]
    (k : Nat) (fs : List (Nat × Proto.WireVal)) (f : Field c.valid)
    (h : FromProtoField.decodeProtoField k fs = .ok f.val) :
    c.fromProtoField k fs = .ok f := by
  rcases f with ⟨val, hok⟩
  simp [Codec.fromProtoField, h, hok]

theorem max_le_max {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : Nat.max a b ≤ Nat.max c d :=
  Nat.max_le.2 ⟨Nat.le_trans h1 (Nat.le_max_left c d), Nat.le_trans h2 (Nat.le_max_right c d)⟩

private def toInt? (s : String) : Option Int :=
  match s.toList with
  | '-' :: ds => (String.ofList ds).toNat?.map fun n => -(Int.ofNat n)
  | _         => s.toNat?.map Int.ofNat

private theorem step_input (inForm : Bool) :
    stepHtmlCtx ⟨.normal, false, false, inForm⟩ "input" = some ⟨.normal, false, false, inForm⟩ := by
  cases inForm <;> rfl
private theorem step_textarea (inForm : Bool) :
    stepHtmlCtx ⟨.normal, false, false, inForm⟩ "textarea" = some ⟨.textarea, false, true, inForm⟩ := by
  cases inForm <;> rfl
private theorem step_select (inForm : Bool) :
    stepHtmlCtx ⟨.normal, false, false, inForm⟩ "select" = some ⟨.select, false, true, inForm⟩ := by
  cases inForm <;> rfl
private theorem step_option (inForm : Bool) :
    stepHtmlCtx ⟨.select, false, true, inForm⟩ "option" = some ⟨.option, false, true, inForm⟩ := rfl
private theorem step_div (inForm : Bool) :
    stepHtmlCtx ⟨.normal, false, false, inForm⟩ "div" = some ⟨.normal, false, false, inForm⟩ := by
  cases inForm <;> rfl
private theorem step_label (inForm : Bool) :
    stepHtmlCtx ⟨.normal, false, false, inForm⟩ "label" = some ⟨.normal, false, false, inForm⟩ := by
  cases inForm <;> rfl
private theorem step_span (inForm : Bool) :
    stepHtmlCtx ⟨.normal, false, false, inForm⟩ "span" = some ⟨.normal, false, false, inForm⟩ := by
  cases inForm <;> rfl
private theorem step_fieldset (inForm : Bool) :
    stepHtmlCtx ⟨.normal, false, false, inForm⟩ "fieldset" = some ⟨.normal, false, false, inForm⟩ := by
  cases inForm <;> rfl
private theorem step_legend (inForm : Bool) :
    stepHtmlCtx ⟨.normal, false, false, inForm⟩ "legend" = some ⟨.normal, false, false, inForm⟩ := by
  cases inForm <;> rfl
private theorem step_button (inForm : Bool) :
    stepHtmlCtx ⟨.normal, false, false, inForm⟩ "button" = some ⟨.normal, false, true, inForm⟩ := by
  cases inForm <;> rfl

private theorem isVoid_input    : isVoidTag "input" = true := rfl
private theorem isVoid_textarea : isVoidTag "textarea" = false := rfl
private theorem isVoid_select   : isVoidTag "select" = false := rfl
private theorem isVoid_option   : isVoidTag "option" = false := rfl
private theorem isVoid_div      : isVoidTag "div" = false := rfl
private theorem isVoid_label    : isVoidTag "label" = false := rfl
private theorem isVoid_span     : isVoidTag "span" = false := rfl
private theorem isVoid_fieldset : isVoidTag "fieldset" = false := rfl
private theorem isVoid_legend   : isVoidTag "legend" = false := rfl
private theorem isVoid_button   : isVoidTag "button" = false := rfl

private theorem safe_value   : isSafeAttrName "value" = true := rfl
private theorem url_value    : isUrlAttrName "value" = false := rfl
private theorem safe_type    : isSafeAttrName "type" = true := rfl
private theorem url_type     : isUrlAttrName "type" = false := rfl
private theorem safe_min     : isSafeAttrName "min" = true := rfl
private theorem url_min      : isUrlAttrName "min" = false := rfl
private theorem safe_name    : isSafeAttrName "name" = true := rfl
private theorem url_name     : isUrlAttrName "name" = false := rfl
private theorem safe_checked : isSafeAttrName "checked" = true := rfl
private theorem safe_inputEv : isSafeAttrName "input" = true := rfl
private theorem safe_changeEv : isSafeAttrName "change" = true := rfl
private theorem safe_clickEv : isSafeAttrName "click" = true := rfl
private theorem safe_dis     : isSafeAttrName "disabled" = true := rfl
private theorem safe_ariaInv : isSafeAttrName "aria-invalid" = true := rfl
private theorem url_ariaInv  : isUrlAttrName "aria-invalid" = false := rfl

private theorem attr_valid_value {msg : Type} (v : String) :
    Attr.valid (msg := msg) (value v) = true := by
  simp only [value, Attr.valid, Attr.validKeyValue, safe_value, url_value, Bool.not_false, Bool.true_or, Bool.and_self]
private theorem attr_valid_onInput {msg : Type} (f : String → msg) :
    Attr.valid (onInput f) = true := by
  simp only [onInput, Attr.valid, safe_inputEv]
private theorem attr_valid_onChange {msg : Type} (f : String → msg) :
    Attr.valid (onChange f) = true := by
  simp only [onChange, Attr.valid, safe_inputEv]
private theorem attr_valid_onCheck {msg : Type} (f : Bool → msg) :
    Attr.valid (onCheck f) = true := by
  simp only [onCheck, Attr.valid, safe_changeEv]
private theorem attr_valid_onClick {msg : Type} (m : msg) :
    Attr.valid (onClick m) = true := by
  simp only [onClick, Attr.valid, safe_clickEv]
private theorem attr_valid_type {msg : Type} (v : String) :
    Attr.valid (msg := msg) (type' v) = true := by
  simp only [type', Attr.valid, Attr.validKeyValue, safe_type, url_type, Bool.not_false, Bool.true_or, Bool.and_self]
private theorem attr_valid_name {msg : Type} (v : String) :
    Attr.valid (msg := msg) (Qed.name v) = true := by
  simp only [Qed.name, Attr.valid, Attr.validKeyValue, safe_name, url_name, Bool.not_false, Bool.true_or, Bool.and_self]
private theorem attr_valid_min {msg : Type} (v : String) :
    Attr.valid (msg := msg) (attr "min" v) = true := by
  simp only [attr, Attr.valid, Attr.validKeyValue, safe_min, url_min, Bool.not_false, Bool.true_or, Bool.and_self]
private theorem attr_valid_checked {msg : Type} (b : Bool) :
    Attr.valid (msg := msg) (checked b) = true := by
  simp only [checked, Attr.valid, safe_checked]
private theorem attr_valid_disabled {msg : Type} (b : Bool) :
    Attr.valid (msg := msg) (disabled b) = true := by
  simp only [disabled, Attr.valid, safe_dis]
private theorem attr_valid_ariaInvalid {msg : Type} (v : String) :
    Attr.valid (msg := msg) (attr "aria-invalid" v) = true := by
  simp only [attr, Attr.valid, Attr.validKeyValue, safe_ariaInv, url_ariaInv, Bool.not_false, Bool.true_or, Bool.and_self]

private theorem attr_valid_cls {msg : Type} (v : String) :
    Attr.valid (msg := msg) (cls v) = true := rfl

private theorem validIn_input {msg : Type} (inForm : Bool) (attrs : List (Attr msg))
    (hv : Attr.validList attrs = true) (hl : Attr.hasLocalCell attrs = false) :
    Html.validIn ⟨.normal, false, false, inForm⟩ (el "input" attrs) = true := by
  simp only [el, Html.validIn, Html.validListIn, step_input, isVoid_input, hv, hl,
    Bool.not_false, Bool.or_true, Bool.and_self, List.isEmpty_nil]

def text : Codec String where
  parse := some; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [value raw, onInput set]
  render_valid := fun inForm raw set => validIn_input inForm _
    (by simp only [Attr.validList, attr_valid_value, attr_valid_onInput, Bool.and_self]) rfl

def textarea : Codec String where
  parse := some; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "textarea" [value raw, onInput set]
  render_valid := fun inForm raw set => by
    have hv : Attr.validList [value (msg := _) raw, onInput set] = true := by
      simp only [Attr.validList, attr_valid_value, attr_valid_onInput, Bool.and_self]
    have hl : Attr.hasLocalCell [value (msg := _) raw, onInput set] = false := rfl
    simp only [el, Html.validIn, Html.validListIn, step_textarea, isVoid_textarea, hv, hl,
      Bool.not_false, Bool.true_or, Bool.and_self]

def nat : Codec Nat where
  parse := fun s => s.toNat?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [type' "number", attr "min" "0", value raw, onInput set]
  render_valid := fun inForm raw set => validIn_input inForm _
    (by simp only [Attr.validList, attr_valid_type, attr_valid_min, attr_valid_value, attr_valid_onInput, Bool.and_self]) rfl

def int : Codec Int where
  parse := toInt?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [type' "number", value raw, onInput set]
  render_valid := fun inForm raw set => validIn_input inForm _
    (by simp only [Attr.validList, attr_valid_type, attr_valid_value, attr_valid_onInput, Bool.and_self]) rfl

def checkbox : Codec Bool where
  parse := fun s => some (s == "true"); valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set =>
    el "input" [type' "checkbox", checked (raw == "true"), onCheck (fun b => set (toString b))]
  render_valid := fun inForm raw set => validIn_input inForm _
    (by simp only [Attr.validList, attr_valid_type, attr_valid_checked, attr_valid_onCheck, Bool.and_self]) rfl

def date : Codec Date where
  parse := Date.parse?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [type' "date", value raw, onInput set]
  render_valid := fun inForm raw set => validIn_input inForm _
    (by simp only [Attr.validList, attr_valid_type, attr_valid_value, attr_valid_onInput, Bool.and_self]) rfl

def select (options : List (String × String)) : Codec String where
  parse := fun s => if options.any (fun o => o.1 == s) then some s else none
  valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set =>
    el "select" [value raw, onChange set]
      (options.map fun (v, lbl) => el "option" [value v] [lbl])
  render_valid := fun {msg} inForm raw set => by
    have hvSel : Attr.validList [value (msg := msg) raw, onChange set] = true := by
      simp only [Attr.validList, attr_valid_value, attr_valid_onChange, Bool.and_self]
    have hlSel : Attr.hasLocalCell [value (msg := msg) raw, onChange set] = false := rfl
    have hvOpt : ∀ v : String, Attr.validList [value (msg := msg) v] = true := fun v => by
      simp only [Attr.validList, attr_valid_value, Bool.and_self]
    have hlOpt : ∀ v : String, Attr.hasLocalCell [value (msg := msg) v] = false := fun _ => rfl
    simp only [el, Html.validIn, Html.validListIn, Html.validListIn_map,
      step_select, step_option, isVoid_select, isVoid_option, validTextIn,
      hvSel, hlSel, hvOpt, hlOpt, Bool.not_false, Bool.true_or, Bool.and_self,
      Qed.List.all_const_true]

def radios (group : String) (options : List (String × String)) : Codec String where
  parse := fun s => if options.any (fun o => o.1 == s) then some s else none
  valid := fun _ => True; dec := fun _ => inferInstance
  wrapLabel := false
  render := fun raw set =>
    el "div" [cls "qed-radios"]
      (options.map fun (v, lbl) =>
        el "label" [] [el "input" [type' "radio", Qed.name group, value v, checked (raw == v), onChange set], lbl])
  render_valid := fun {msg} inForm raw set => by
    have hvDiv : Attr.validList [cls (msg := msg) "qed-radios"] = true := rfl
    have hlDiv : Attr.hasLocalCell [cls (msg := msg) "qed-radios"] = false := rfl
    have hvNil : Attr.validList ([] : List (Attr msg)) = true := rfl
    have hlNil : Attr.hasLocalCell ([] : List (Attr msg)) = false := rfl
    have hInp : ∀ v : String, Html.validIn ⟨.normal, false, false, inForm⟩
        (el "input" [type' "radio", Qed.name group, value v, checked (raw == v), onChange set]) = true := fun v =>
      validIn_input inForm _
        (by simp only [Attr.validList, attr_valid_type, attr_valid_name, attr_valid_value, attr_valid_checked, attr_valid_onChange, Bool.and_self])
        rfl
    have hLbl : ∀ p : String × String, Html.validIn ⟨.normal, false, false, inForm⟩
        (el "label" [] [el "input" [type' "radio", Qed.name group, value p.1, checked (raw == p.1), onChange set], p.2]) = true := fun (v, lbl) => by
      simp only [el, Html.validIn, Html.validListIn, step_label, isVoid_label, validTextIn,
        hvNil, hlNil, Bool.not_false, Bool.true_or, Bool.and_self, Bool.and_true, Bool.true_and]
      exact hInp v
    change Html.validIn ⟨.normal, false, false, inForm⟩
      (Html.element "div" [cls "qed-radios"] (options.map fun p =>
        el "label" [] [el "input" [type' "radio", Qed.name group, value p.1, checked (raw == p.1), onChange set], p.2])) = true
    rw [Html.validIn]
    simp only [step_div, isVoid_div, hvDiv, hlDiv, Html.validListIn_map, hLbl,
      Bool.not_false, Bool.true_or, Bool.and_self, Qed.List.all_const_true]

def json (α : Type) [ToJson α] [FromJson α] : Codec α where
  parse := fun _ => none
  valid := fun _ => True; dec := fun _ => inferInstance
  render := fun _ _ => el "span" [] []
  inForm := false
  render_valid := fun inForm _ _ => by
    simp only [el, Html.validIn, Html.validListIn, step_span, isVoid_span,
      Attr.validList, Attr.hasLocalCell, Bool.not_false, Bool.true_or, Bool.and_self]

@[simp] theorem render_valid_simp {α msg : Type} (c : Codec α) (inForm : Bool) (raw : String) (set : String → msg) :
    Html.validIn ⟨.normal, false, false, inForm⟩ (c.render raw set) = true :=
  c.render_valid inForm raw set

def formFieldRow {msg : Type} (inForm wrapLabel bad : Bool) (label err : String) (ctrl : Html msg) :
    List (Html msg) :=
  if inForm then
    let tag    := if wrapLabel then "label" else "fieldset"
    let lblTag := if wrapLabel then "span" else "legend"
    [el tag [cls "qed-field", attr "aria-invalid" (if bad then "true" else "false")]
      ([el lblTag [cls "qed-label"] [label], ctrl] ++
       (if bad then [el "span" [cls "qed-error"] [err]] else []))]
  else []

@[simp] theorem formFieldRow_validListIn {msg : Type} (ctxInForm inForm wrapLabel bad : Bool)
    (label err : String) (ctrl : Html msg)
    (hctrl : Html.validIn ⟨.normal, false, false, ctxInForm⟩ ctrl = true) :
    Html.validListIn ⟨.normal, false, false, ctxInForm⟩
      (formFieldRow inForm wrapLabel bad label err ctrl) = true := by
  have hvRow : ∀ v : String, Attr.validList [cls (msg := msg) "qed-field", attr "aria-invalid" v] = true := fun v => by
    simp only [Attr.validList, attr_valid_cls, attr_valid_ariaInvalid, Bool.and_self]
  have hlRow : ∀ v : String, Attr.hasLocalCell [cls (msg := msg) "qed-field", attr "aria-invalid" v] = false := fun _ => rfl
  have hvCls : ∀ s : String, Attr.validList [cls (msg := msg) s] = true := fun _ => rfl
  have hlCls : ∀ s : String, Attr.hasLocalCell [cls (msg := msg) s] = false := fun _ => rfl
  cases inForm with
  | false => rfl
  | true =>
    cases wrapLabel with
    | true =>
      cases bad with
      | true =>
        dsimp only [formFieldRow]
        simp only [ite_true, List.cons_append, List.nil_append,
          el, Html.validListIn, Html.validIn, step_label, step_span, isVoid_label, isVoid_span,
          hvRow, hlRow, hvCls, hlCls, validTextIn, hctrl, Bool.not_false, Bool.true_or, Bool.and_self]
      | false =>
        dsimp only [formFieldRow]
        simp only [Bool.false_eq_true, ite_true, ite_false, List.cons_append, List.nil_append,
          el, Html.validListIn, Html.validIn, step_label, step_span, isVoid_label, isVoid_span,
          hvRow, hlRow, hvCls, hlCls, validTextIn, hctrl, Bool.not_false, Bool.true_or, Bool.and_self]
    | false =>
      cases bad with
      | true =>
        dsimp only [formFieldRow]
        simp only [Bool.false_eq_true, ite_true, ite_false, List.cons_append, List.nil_append,
          el, Html.validListIn, Html.validIn, step_fieldset, step_legend, step_span,
          isVoid_fieldset, isVoid_legend, isVoid_span,
          hvRow, hlRow, hvCls, hlCls, validTextIn, hctrl, Bool.not_false, Bool.true_or, Bool.and_self]
      | false =>
        dsimp only [formFieldRow]
        simp only [Bool.false_eq_true, ite_true, ite_false, List.cons_append, List.nil_append,
          el, Html.validListIn, Html.validIn, step_fieldset, step_legend,
          isVoid_fieldset, isVoid_legend,
          hvRow, hlRow, hvCls, hlCls, validTextIn, hctrl, Bool.not_false, Bool.true_or, Bool.and_self]

theorem formDiv_validIn {msg : Type} (inForm : Bool) (kids : List (Html msg))
    (hk : Html.validListIn ⟨.normal, false, false, inForm⟩ kids = true) :
    Html.validIn ⟨.normal, false, false, inForm⟩ (el "div" [cls "qed-form"] kids) = true := by
  have hv : Attr.validList [cls (msg := msg) "qed-form"] = true := rfl
  have hl : Attr.hasLocalCell [cls (msg := msg) "qed-form"] = false := rfl
  simp only [el, Html.validIn, step_div, isVoid_div, hv, hl, hk, Bool.not_false, Bool.true_or, Bool.and_self]

theorem formRowCons_validIn {msg : Type} (ctxInForm inForm wrapLabel bad : Bool)
    (label err : String) (ctrl : Html msg) (rest : List (Html msg))
    (hctrl : Html.validIn ⟨.normal, false, false, ctxInForm⟩ ctrl = true)
    (hrest : Html.validListIn ⟨.normal, false, false, ctxInForm⟩ rest = true) :
    Html.validListIn ⟨.normal, false, false, ctxInForm⟩
      (formFieldRow inForm wrapLabel bad label err ctrl ++ rest) = true := by
  rw [Html.validListIn_append, formFieldRow_validListIn ctxInForm inForm wrapLabel bad label err ctrl hctrl, hrest]; rfl

def submitBtn {msg α : Type} (o : Option α) (submit : α → msg) : Html msg :=
  match o with
  | some p => el "button" [onClick (submit p)] "Submit"
  | none   => el "button" [disabled true] "Submit"

theorem submitBtn_validIn {msg α : Type} (inForm : Bool) (o : Option α) (submit : α → msg) :
    Html.validListIn ⟨.normal, false, false, inForm⟩ [submitBtn o submit] = true := by
  cases o with
  | some p =>
    have hv : Attr.validList [onClick (submit p)] = true := by
      simp only [Attr.validList, attr_valid_onClick, Bool.and_self]
    have hl : Attr.hasLocalCell [onClick (submit p)] = false := rfl
    simp only [submitBtn, el, Html.validListIn, Html.validIn, step_button, isVoid_button,
      hv, hl, validTextIn, Bool.not_false, Bool.true_or, Bool.and_self]
  | none =>
    have hv : Attr.validList [disabled (msg := msg) true] = true := by
      simp only [Attr.validList, attr_valid_disabled, Bool.and_self]
    have hl : Attr.hasLocalCell [disabled (msg := msg) true] = false := rfl
    simp only [submitBtn, el, Html.validListIn, Html.validIn, step_button, isVoid_button,
      hv, hl, validTextIn, Bool.not_false, Bool.true_or, Bool.and_self]

end Codec

class DefaultCodec (α : Type) where
  codec : Codec α

@[reducible] instance : DefaultCodec String := ⟨Codec.text⟩
@[reducible] instance : DefaultCodec Nat    := ⟨Codec.nat⟩
@[reducible] instance : DefaultCodec Int    := ⟨Codec.int⟩
@[reducible] instance : DefaultCodec Bool   := ⟨Codec.checkbox⟩
@[reducible] instance : DefaultCodec Date   := ⟨Codec.date⟩
@[reducible] instance (priority := low) {α : Type} [ToJson α] [FromJson α] : DefaultCodec α :=
  ⟨Codec.json α⟩


section SchemaParsers
open Lean Parser
def schemaCtxParamP : Parser := node `Qed.schemaCtxParam (ident >> ":" >> categoryParser `qedType 0)
def schemaFieldJsonOnly : Parser := node `Qed.schemaFieldJsonOnly
  (atomic (identEq `jsonOnly >> checkNoWsBefore "" >> "(") >> categoryParser `qedType 0 >> ")")
def schemaFieldCall : Parser := node `Qed.schemaFieldCall
  (atomic (ident >> checkNoWsBefore "" >> "(") >> sepBy (categoryParser `qedCallArg 0) "," >> ")")
def schemaFieldSpec : Parser := schemaFieldJsonOnly <|> schemaFieldCall <|> categoryParser `qedType 0
def schemaFieldP : Parser := node `Qed.schemaField (withPosition
  (ident >> ":" >> schemaFieldSpec >> optional (checkColGt >> " where " >> sepBy1 (categoryParser `qedExpr 0) ",")))
@[command_parser] def schemaCmd : Parser := leading_parser withPosition
  ("schema " >> ident >> optional (checkLineEq >> "(" >> sepBy1 schemaCtxParamP "," >> ")") >> ":" >>
    checkColGt "expected indented `schema` fields" >> many1Indent schemaFieldP)
end SchemaParsers

open Lean in
private def lowerSchemaFieldSpec (stx : Syntax) : MacroM Term := do
  let k := stx.getKind
  if k == `Qed.schemaFieldJsonOnly then
    let (innerTy, _) ← Qed.Lang.lowerQedType (stx.getArg 2) false
    `(jsonOnly $innerTy)
  else if k == `Qed.schemaFieldCall then
    let callee : Term := ⟨(stx.getArg 0)⟩
    let args := (stx.getArg 2).getSepArgs
    args.foldlM (init := callee) fun acc a => do
      let aT ← Qed.Lang.lowerSimpleQedExpr .val (a.getArg 0)
      `($acc $aT)
  else
    return (← Qed.Lang.lowerQedType stx false).1

open Lean Elab Term Meta in
private partial def resolveCodecBase (fieldName : Name) (rawSpec : Term) : TermElabM Term := do
  match rawSpec with
  | `($fn:ident $arg:term) =>
      if fn.getId.eraseMacroScopes == `jsonOnly then
        let inner ← resolveCodecBase fieldName arg
        return ← `(Qed.Codec.jsonOnly $inner)
  | _ => pure ()
  let scopedSpec ← `(open Qed.Codec in $rawSpec)
  let e ← elabTermAndSynthesize scopedSpec none
  let ety ← whnf (← instantiateMVars (← inferType e))
  if ety.isAppOfArity ``Qed.Codec 1 then
    return scopedSpec
  else if ety.isSort then
    let eWhnf ← whnf (← instantiateMVars e)
    if eWhnf.isConstOf ``String then return ← `(Qed.Codec.text)
    else if eWhnf.isConstOf ``Nat then return ← `(Qed.Codec.nat)
    else if eWhnf.isConstOf ``Int then return ← `(Qed.Codec.int)
    else if eWhnf.isConstOf ``Bool then return ← `(Qed.Codec.checkbox)
    else if eWhnf.isConstOf ``Qed.Date then return ← `(Qed.Codec.date)
    else
      if (← trySynthInstance (← mkAppM ``Qed.DefaultCodec #[e])) matches .some _ then
        return ← `((Qed.DefaultCodec.codec : Qed.Codec $rawSpec))
      else
        throwErrorAt rawSpec m!"schema field `{fieldName}` has type `{rawSpec}`, which has no default `Codec` or JSON (`ToJson`/`FromJson`) instances.\nProvide a `DefaultCodec` or JSON instances for `{rawSpec}`, or use a supported field type (`String`, `Nat`, `Int`, `Bool`, `Date`, `select([...])`, `textarea`, `jsonOnly(...)`)."
  else
    throwErrorAt rawSpec m!"schema field `{fieldName}` must be a type (`String`, `Nat`, `Int`, `Bool`, `Date`, …) \
      or a `Codec` (e.g. `select([...])`, `textarea`, `jsonOnly(String)`), but this has \
      type{indentExpr ety}"

open Lean Elab Term Meta in
private partial def elabSchemaFieldsAux (cbns : Array Ident) (cbts : Array Term)
    (fs : Array Ident) (rawSpecs : Array Term) (whereClauses : Array (Array Term)) (i : Nat) :
    TermElabM (Array (Term × Bool × Bool × Bool × Bool × Bool)) := do
  if i < cbns.size then
    let bt ← elabType cbts[i]!
    withLocalDeclD cbns[i]!.getId bt fun _ =>
      elabSchemaFieldsAux cbns cbts fs rawSpecs whereClauses (i + 1)
  else
    ((fs.zip rawSpecs).zip whereClauses).mapM fun ((f, rawSpec), preds) => do
      let base ← resolveCodecBase f.getId rawSpec
      let inp : Term ←
        if preds.isEmpty then
          pure base
        else do
          let propTerms ← preds.mapM fun p => `(($p : Prop))
          let combined ← match propTerms.toList with
            | []      => `(True)
            | c :: cs => cs.foldlM (init := c) fun acc x => `($acc ∧ $x)
          `(Qed.Codec.refine $base (fun $f:ident => $combined))
      let c ← elabTermAndSynthesize inp none
      let cty ← instantiateMVars (← inferType c)
      match cty.getAppFnArgs with
      | (``Qed.Codec, #[α]) =>
          let validExpr := mkApp2 (mkConst ``Qed.Codec.valid) α c
          let trueFn := Expr.lam `x α (mkConst ``True) BinderInfo.default
          let isRef ← pure (! (← isDefEq validExpr trueFn))
          let isLaw ← pure ((← trySynthInstance (mkApp (mkConst ``Qed.LawfulJson) α)) matches .some _)
          let hasToP ← pure ((← trySynthInstance (mkApp (mkConst ``Qed.ToProtoField) α)) matches .some _)
          let hasFromP ← pure ((← trySynthInstance (mkApp (mkConst ``Qed.FromProtoField) α)) matches .some _)
          let isLawP ← pure ((← trySynthInstance (mkApp (mkConst ``Qed.LawfulProtoField) α)) matches .some _)
          let isLawBEq ←
            match ← trySynthInstance (mkApp (mkConst ``BEq [Level.zero]) α) with
            | .some beqInst =>
                pure ((← trySynthInstance (mkApp2 (mkConst ``LawfulBEq [Level.zero]) α beqInst)) matches .some _)
            | _ => pure false
          pure (inp, isRef, isLaw, hasToP && hasFromP, isLawP, isLawBEq)
      | _ =>
          throwErrorAt rawSpec m!"failed to resolve schema field `{f.getId}` to a `Codec`"

open Lean Elab Command in
private def resolveSchemaFields (cbns : Array Ident) (cbts : Array Term)
    (fs : Array Ident) (rawSpecs : Array Term) (whereClauses : Array (Array Term)) :
    CommandElabM (Array Term × Array Bool × Bool × Bool × Bool × Bool) := do
  let res ← liftTermElabM (elabSchemaFieldsAux cbns cbts fs rawSpecs whereClauses 0)
  return (res.map (·.1), res.map (·.2.1), res.all (·.2.2.1), res.all (·.2.2.2.1),
    res.all (·.2.2.2.2.1), res.all (·.2.2.2.2.2))

open Lean Elab Command Term Meta in
private partial def elabPredProbe (cbns : Array Ident) (cbts : Array Term) (inp : Term) (i : Nat) :
    TermElabM Unit := do
  if i < cbns.size then
    let bt ← elabType cbts[i]!
    withLocalDeclD cbns[i]!.getId bt fun _ => elabPredProbe cbns cbts inp (i + 1)
  else
    discard <| elabTermAndSynthesize inp none

open Lean Elab Command Term in
private def mkProtoFieldSkeleton
    (reads : Array (TSyntax `term))
    (fieldValTy : Nat → CommandElabM (TSyntax `term))
    (wrapFieldEq : Nat → TSyntax `term → TSyntax `term → CommandElabM (TSyntax `term)) :
    CommandElabM (TSyntax `term × TSyntax `term × Array Ident × Array (TSyntax `tactic)) := do
  let nFields := reads.size
  let emptyList ← `(term| ([] : List (Nat × Proto.WireVal)))
  let mut tails : Array (TSyntax `term) := Array.replicate (nFields + 1) emptyList
  let mut tagsPosPf ← `(term| (fun (_ : Nat × Proto.WireVal) h => False.elim (List.not_mem_nil h)))
  for revIdx in [0:nFields] do
    let i := nFields - 1 - revIdx
    let iLit := Syntax.mkNumLit (toString i)
    let kLit := Syntax.mkNumLit (toString (i + 1))
    tails := tails.set! i (← `(term| ToProtoField.encodeProtoField $kLit $(reads[i]!) ++ $(tails[i + 1]!)))
    tagsPosPf ← `(term| Proto.msg_tags_pos_encodeAppend (Nat.zero_lt_succ $iLit) $(reads[i]!) $tagsPosPf)
  let body := tails[0]!
  let mut pIdents : Array Ident := #[]
  let mut pHaveTacs : Array (TSyntax `tactic) := #[]
  for i in [0:nFields] do
    let kLit := Syntax.mkNumLit (toString (i + 1))
    let valTy ← fieldValTy i
    let mut gtPf ← `(term| Proto.allTagsGt_nil $kLit)
    for revAfter in [0 : nFields - 1 - i] do
      let j := nFields - 1 - revAfter
      let jLit := Syntax.mkNumLit (toString (j + 1))
      let diffPredLit := Syntax.mkNumLit (toString (j - i - 1))
      gtPf ← `(term| Proto.allTagsGt_encodeAppend (Nat.lt_of_sub_eq_succ (rfl : $jLit - $kLit = Nat.succ $diffPredLit)) $(reads[j]!) $gtPf)
    let mut rawEq ← `(term| Proto.decodeProtoField_hit $kLit $(reads[i]!) $(tails[i + 1]!) $gtPf)
    for revBefore in [0:i] do
      let j := i - 1 - revBefore
      let jLit := Syntax.mkNumLit (toString (j + 1))
      let diffPredLit := Syntax.mkNumLit (toString (i - j - 1))
      rawEq ← `(term| Eq.trans (Proto.decodeProtoField_skip (α := $valTy) (Nat.ne_of_lt (Nat.lt_of_sub_eq_succ (rfl : $kLit - $jLit = Nat.succ $diffPredLit))) $(reads[j]!) $(tails[j + 1]!)) $rawEq)
    let fullEq ← wrapFieldEq i body rawEq
    let hId := mkIdent (Name.mkSimple s!"_hp{i}")
    pIdents := pIdents.push hId
    pHaveTacs := pHaveTacs.push (← `(tactic| have $hId:ident := $fullEq))
  return (body, tagsPosPf, pIdents, pHaveTacs)

open Lean Elab Command Term in
private def mkSchemaProtoInsts (t : Ident) (toId fromId : Ident)
    (tagsPosPf : TSyntax `term) (pIdents : Array Ident) (pHaveTacs : Array (TSyntax `tactic))
    (allLawfulProto : Bool) : CommandElabM (Array (TSyntax `command)) := do
  let tId := t.getId
  let instBase : Array (TSyntax `command) := #[
    ← `(command| instance $(mkIdent (tId ++ `instToProto)):ident : ToProto $t := .ofFields $toId),
    ← `(command| instance $(mkIdent (tId ++ `instFromProto)):ident : FromProto $t := .ofFields $fromId) ]
  if !allLawfulProto then return instBase
  let fromProtoThmId := mkIdent (tId ++ `_fromProto_toProto)
  let lawCmds : Array (TSyntax `command) := #[
    ← `(command| private theorem $fromProtoThmId (x : $t) : $fromId ($toId x) = Except.ok x := by
          $[$pHaveTacs:tactic]*
          unfold $fromId $toId
          simp only [$[$pIdents:term],*, bind, Except.bind, pure, Except.pure]),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulProto)):ident : LawfulProto $t :=
          .ofFields $toId $fromId (fun x => $tagsPosPf) $fromProtoThmId) ]
  return instBase ++ lawCmds

open Lean Elab Command Term in
private def mkSchemaProtoCmds (t : Ident) (cbns : Array Ident) (cbts : Array Term)
    (tApp : TSyntax `term) (appTo : TSyntax `term → CommandElabM (TSyntax `term))
    (fs : Array Ident) (inputs : Array Term) (refined : Array Bool)
    (jsonReads : Array (TSyntax `term)) (allProto allLawfulProto : Bool) :
    CommandElabM (Array (TSyntax `command)) := do
  if !allProto then return #[]
  let tId := t.getId
  let toId          := mkIdent (tId ++ `toProtoFields)
  let fromId        := mkIdent (tId ++ `fromProtoFields)
  let encodeBytesId := mkIdent (tId ++ `encodeBytes)
  let decodeBytesId := mkIdent (tId ++ `decodeBytes)
  let toApp   ← appTo ⟨toId.raw⟩
  let fromApp ← appTo ⟨fromId.raw⟩
  let protoDecodes ← (List.range fs.size).toArray.mapM fun i => do
    let kLit := Syntax.mkNumLit (toString (i + 1))
    let inp := inputs[i]!
    if refined[i]! then `(term| ($inp).fromProtoField $kLit fs)
    else `(term| (FromProtoField.decodeProtoField $kLit fs : Except String (Codec.Val $inp)))
  let (protoBody, tagsPosPf, pIdents, pHaveTacs) ← mkProtoFieldSkeleton jsonReads
    (fun i => `(term| Codec.Val $(inputs[i]!)))
    (fun i body rawEq =>
      if refined[i]! then do
        let kLit := Syntax.mkNumLit (toString (i + 1))
        let f := fs[i]!
        `(term| Codec.fromProtoField_of_field $(inputs[i]!) $kLit $body (x.$f:ident) $rawEq)
      else pure rawEq)
  let baseCmds : Array (TSyntax `command) := #[
    ← `(command| def $toId $[($cbns:ident : $cbts:term)]* (x : $tApp) : List (Nat × Proto.WireVal) := $protoBody),
    ← `(command| def $fromId $[($cbns:ident : $cbts:term)]* (fs : List (Nat × Proto.WireVal)) : Except String $tApp := do
          $[let $fs:ident ← $protoDecodes:term]*
          return { $[$fs:ident],* }),
    ← `(command| def $encodeBytesId $[($cbns:ident : $cbts:term)]* (x : $tApp) : Bytes :=
          Proto.encodeFieldsSpec ($toApp x)),
    ← `(command| def $decodeBytesId $[($cbns:ident : $cbts:term)]* (b : Bytes) : Except String $tApp :=
          (Proto.decodeFieldsSpec b).bind ($fromApp)) ]
  if !cbns.isEmpty then return baseCmds
  let instCmds ← mkSchemaProtoInsts t toId fromId tagsPosPf pIdents pHaveTacs allLawfulProto
  return baseCmds ++ instCmds

open Lean Elab Command Term in
private def checkSchemaFieldsDecidable (cbns : Array Ident) (cbts : Array Term)
    (pairs : Array (Ident × Term)) (refined : Array Bool) : CommandElabM Unit := do
  -- Lean logs failed instance synthesis to `messages` rather than throwing; probe in isolation to catch missing `DecidablePred` cleanly.
  for ((f, inp), r) in pairs.zip refined do
    unless r do continue
    let before := (← get).messages
    try liftTermElabM (elabPredProbe cbns cbts inp 0) catch _ => pure ()
    let probeMsgs := (← get).messages.toList.drop before.toList.length
    modify fun st => { st with messages := before }
    let mut undecidable := false
    for msg in probeMsgs do
      if ((← msg.data.toString).splitOn "DecidablePred").length > 1 then undecidable := true
    if undecidable then
      throwErrorAt inp m!"schema field `{f.getId}` has a refinement that isn't decidable, so \
        validity can't be computed (no `DecidablePred` for it).\n\nThe usual cause is a \
        predicate written with `def`. Write it inline with `where …` or as an `abbrev`, so Lean \
        sees it reduces to a decidable check:\n    abbrev MyPredicate (x : …) : Prop := …\n\
        If it genuinely can't be decided, give it a `DecidablePred` instance."

open Lean Elab Command Term in
private def mkDraftInstCmds (tId : Name) (draftId draftToJsonId draftFromId : Ident)
    (fs : Array Ident) : CommandElabM (Array (TSyntax `command)) := do
  let draftFromThmId := mkIdent (tId ++ `Draft ++ `_fromJson_toJson)
  let draftFieldEqs ← fs.mapM fun f =>
    let keyLit := Syntax.mkStrLit (toString f.getId)
    `(term| LawfulJson.fromField_of_field ($draftToJsonId x) $keyLit (x.$f:ident) rfl)
  let draftDepthProof ← fs.foldrM (init := ← `(term| Nat.le_refl 0)) fun f acc =>
    `(term| Codec.max_le_max (LawfulJson.depth_toJson (x.$f:ident)) $acc)
  pure #[
    ← `(command| instance $(mkIdent (tId ++ `Draft ++ `instToJson)):ident : ToJson $draftId := ⟨$draftToJsonId⟩),
    ← `(command| instance $(mkIdent (tId ++ `Draft ++ `instFromJson)):ident : FromJson $draftId := ⟨$draftFromId⟩),
    ← `(command| instance $(mkIdent (tId ++ `Draft ++ `instNonNullJson)):ident : NonNullJson $draftId := ⟨fun _ => nofun⟩),
    ← `(command| private theorem $draftFromThmId (x : $draftId) :
          $draftFromId ($draftToJsonId x) = .ok x := by
          unfold $draftFromId
          simp only [$[$draftFieldEqs:term],*, bind, Except.bind, pure, Except.pure]),
    ← `(command| instance $(mkIdent (tId ++ `Draft ++ `instLawfulJson)):ident : LawfulJson $draftId where
          depthBound := 1
          depth_toJson x := Nat.add_le_add_left $draftDepthProof 1
          fromJson_toJson := $draftFromThmId) ]

open Lean Elab Command Term in
private def mkDraftCmds (tId : Name) (draftId : Ident) (fs : Array Ident) :
    CommandElabM (TSyntax `command × Array (TSyntax `command)) := do
  let emptyId       := mkIdent (tId ++ `Draft ++ `empty)
  let draftToJsonId := mkIdent (tId ++ `Draft ++ `toJson)
  let draftFromId   := mkIdent (tId ++ `Draft ++ `fromJson)
  let emptyVals ← fs.mapM fun _ => `(term| "")
  let draftJsonPairs ← fs.mapM fun f =>
    let keyLit := Syntax.mkStrLit (toString f.getId); `(($keyLit, toJson (x.$f:ident)))
  let draftJsonDecodes ← fs.mapM fun f =>
    let keyLit := Syntax.mkStrLit (toString f.getId)
    `((FromJsonField.fromField j $keyLit : Except String String))
  let structCmd ← `(command| structure $draftId where
          $[$fs:ident : String := ""]*
        deriving Inhabited, DecidableEq, Repr)
  let fnCmds : Array (TSyntax `command) := #[
    ← `(command| def $emptyId : $draftId := { $[$fs:ident := $emptyVals],* }),
    ← `(command| def $draftToJsonId (x : $draftId) : Json := Json.obj [$[$draftJsonPairs],*]),
    ← `(command| def $draftFromId (j : Json) : Except String $draftId := do
          $[let $fs:ident ← $draftJsonDecodes:term]*
          return { $[$fs:ident],* }) ]
  let instCmds ← mkDraftInstCmds tId draftId draftToJsonId draftFromId fs
  pure (structCmd, fnCmds ++ instCmds)

open Lean Elab Command Term in
private def mkSchemaBeqCmds (tId : Name) (cbns : Array Ident) (cbts : Array Term)
    (tApp beqApp : TSyntax `term) (fs : Array Ident) (allLawfulBEq : Bool) :
    CommandElabM (Array (TSyntax `command)) := do
  let beqFnId := mkIdent (tId ++ `beq)
  let beqExpr ← match fs.toList with
    | []      => `(true)
    | f :: rest =>
        rest.foldlM (init := ← `(a.$f:ident == b.$f:ident)) fun acc fi => `($acc && (a.$fi:ident == b.$fi:ident))
  let base : Array (TSyntax `command) := #[
    ← `(command| def $beqFnId $[($cbns:ident : $cbts:term)]* (a b : $tApp) : Bool := $beqExpr),
    ← `(command| instance $(mkIdent (tId ++ `instBEq)):ident $[($cbns:ident : $cbts:term)]* : BEq $tApp :=
          ⟨$beqApp⟩) ]
  if !allLawfulBEq then return base
  let beqEqThmId := mkIdent (tId ++ `_eq_of_beq)
  let beqRflThmId := mkIdent (tId ++ `_beq_rfl)
  return base ++ #[
    ← `(command|
      private theorem $beqEqThmId $[($cbns:ident : $cbts:term)]* {a b : $tApp}
          (h : $beqApp a b = true) : a = b := by
        cases a; cases b
        dsimp only [$beqFnId:ident] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        simp_all only),
    ← `(command|
      private theorem $beqRflThmId $[($cbns:ident : $cbts:term)]* {a : $tApp} :
          $beqApp a a = true := by
        cases a
        dsimp only [$beqFnId:ident]
        simp only [beq_self_eq_true, Bool.and_self]),
    ← `(command|
      instance $(mkIdent (tId ++ `instLawfulBEq)):ident $[($cbns:ident : $cbts:term)]* : LawfulBEq $tApp where
        eq_of_beq := $beqEqThmId
        rfl := $beqRflThmId) ]

open Lean Elab Command Term in
private def mkSchemaParseCmds (tId : Name) (cbns : Array Ident) (cbts : Array Term)
    (tApp parseApp canApp : TSyntax `term) (draftId : Ident)
    (fs : Array Ident) (runCalls : Array (TSyntax `term)) :
    CommandElabM (Array (TSyntax `command)) := do
  let parseId := mkIdent (tId ++ `parse)
  let canId   := mkIdent (tId ++ `canSubmit)
  let iffId   := mkIdent (tId ++ `canSubmit_iff)
  let isSomes ← runCalls.mapM fun rc => `(($rc).isSome)
  let rhs ← match isSomes.toList with
    | []      => `(True)
    | c :: cs => cs.foldlM (init := c) fun acc x => `($acc ∧ $x)
  let casesTac ← runCalls.foldrM (init := ← `(tactic|
    simp only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true,
      and_true, true_and, and_false, false_and, iff_self, bind, Option.bind, pure, Pure.pure]))
    fun rc acc => `(tactic|
      cases $rc:term with
      | none => simp only [Option.isSome_none, Bool.false_eq_true, false_and, and_false, iff_self, bind, Option.bind]
      | some _ => ($acc:tactic))
  pure #[
    ← `(command| def $parseId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Option $tApp := do
          $[let $fs:ident ← $runCalls:term]*
          return { $[$fs:ident],* }),
    ← `(command| def $canId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Bool :=
          ($parseApp d).isSome),
    ← `(command| theorem $iffId $[($cbns:ident : $cbts:term)]* (d : $draftId) :
          $canApp d = true ↔ $rhs := by unfold $canId $parseId; $casesTac) ]

open Lean Elab Command Term in
private def mkSchemaFormViewCmds (tId : Name) (cbns : Array Ident) (cbts : Array Term)
    (tApp parseApp viewApp : TSyntax `term) (draftId : Ident)
    (fs : Array Ident) (inputs : Array Term) (runCalls : Array (TSyntax `term)) :
    CommandElabM (Array (TSyntax `command)) := do
  let viewId      := mkIdent (tId ++ `formView)
  let formValidId := mkIdent (tId ++ `formView_validIn)
  let rowGroups ← ((fs.zip inputs).zip runCalls).mapM fun ((f, inp), rc) => do
    let nameLit := Syntax.mkStrLit (toString f.getId)
    let errLit  := Syntax.mkStrLit ("Please enter a valid " ++ toString f.getId)
    `(term| Codec.formFieldRow ($inp).inForm ($inp).wrapLabel
              (d.$f:ident != "" && ($rc).isNone) $nameLit $errLit
              (($inp).render (d.$f:ident) (fun v => onEdit { d with $f:ident := v })))
  let viewBody ← rowGroups.foldrM (init := ← `(term| [Codec.submitBtn ($parseApp d) submit])) fun g acc => `(term| $g ++ $acc)
  let validBodyPf ← inputs.foldrM (init := ← `(term| Codec.submitBtn_validIn inForm ($parseApp d) submit))
    fun inp acc => `(term| Codec.formRowCons_validIn inForm _ _ _ _ _ _ _ (($inp).render_valid inForm _ _) $acc)
  pure #[
    ← `(command| def $viewId {msg : Type} $[($cbns:ident : $cbts:term)]* (d : $draftId)
          (onEdit : $draftId → msg) (submit : $tApp → msg) : Html msg :=
          el "div" [cls "qed-form"] $viewBody),
    ← `(command| @[simp] theorem $formValidId {msg : Type} $[($cbns:ident : $cbts:term)]*
          (inForm : Bool) (d : $draftId) (onEdit : $draftId → msg) (submit : $tApp → msg) :
          Html.validIn ⟨.normal, false, false, inForm⟩ ($viewApp d onEdit submit) = true :=
          Codec.formDiv_validIn inForm _ $validBodyPf) ]

open Lean Elab Command Term in
private def mkSchemaCoreCmds (t : Ident) (cbns : Array Ident) (cbts : Array Term)
    (tApp beqApp parseApp canApp viewApp : TSyntax `term) (draftId : Ident)
    (fs : Array Ident) (inputs : Array Term) (refined : Array Bool) (allLawfulBEq : Bool) :
    CommandElabM (TSyntax `command × Array (TSyntax `command)) := do
  let tId := t.getId
  let pairs := fs.zip inputs
  let structTys ← (pairs.zip refined).mapM fun ((_, inp), r) =>
    if r then `(Field ($inp).valid) else `(Codec.Val $inp)
  let runCalls ← (pairs.zip refined).mapM fun ((f, inp), r) =>
    if r then `(($inp).run (d.$f:ident)) else `(($inp).parse (d.$f:ident))
  let structCmd ← `(command| structure $t $[($cbns:ident : $cbts:term)]* where
          $[$fs:ident : $structTys]*)
  let beqCmds   ← mkSchemaBeqCmds tId cbns cbts tApp beqApp fs allLawfulBEq
  let parseCmds ← mkSchemaParseCmds tId cbns cbts tApp parseApp canApp draftId fs runCalls
  let viewCmds  ← mkSchemaFormViewCmds tId cbns cbts tApp parseApp viewApp draftId fs inputs runCalls
  pure (structCmd, beqCmds ++ parseCmds ++ viewCmds)

open Lean Elab Command Term in
private def mkSchemaJsonInstCmds (t : Ident) (toJsonId fromJsonId : Ident)
    (fs : Array Ident) (inputs : Array Term) (refined : Array Bool)
    (jsonReads : Array (TSyntax `term)) (allLawful : Bool) :
    CommandElabM (Array (TSyntax `command)) := do
  let tId := t.getId
  let base : Array (TSyntax `command) := #[
    ← `(command| instance $(mkIdent (tId ++ `instToJson)):ident : ToJson $t := ⟨$toJsonId⟩),
    ← `(command| instance $(mkIdent (tId ++ `instFromJson)):ident : FromJson $t := ⟨$fromJsonId⟩),
    ← `(command| instance $(mkIdent (tId ++ `instNonNullJson)):ident : NonNullJson $t := ⟨fun _ => nofun⟩) ]
  if !allLawful then return base
  let depthBoundExpr ← inputs.foldrM (init := ← `(term| (0 : Nat))) fun inp acc =>
    `(term| Nat.max (LawfulJson.depthBound (Codec.Val $inp)) $acc)
  let depthProofExpr ← jsonReads.foldrM (init := ← `(term| Nat.le_refl 0)) fun rd acc =>
    `(term| Codec.max_le_max (LawfulJson.depth_toJson $rd) $acc)
  let fieldEqs ← ((fs.zip inputs).zip refined).mapM fun ((f, inp), r) => do
    let keyLit := Syntax.mkStrLit (toString f.getId)
    if r then `(term| Codec.fromJsonField_of_field $inp ($toJsonId x) $keyLit (x.$f) rfl)
    else `(term| LawfulJson.fromField_of_field ($toJsonId x) $keyLit (x.$f) rfl)
  let fromJsonThmId := mkIdent (tId ++ `_fromJson_toJson)
  return base ++ #[
    ← `(command|
      private theorem $fromJsonThmId (x : $t) : $fromJsonId ($toJsonId x) = .ok x := by
        unfold $fromJsonId
        simp only [$[$fieldEqs:term],*, bind, Except.bind, pure, Except.pure]),
    ← `(command|
      instance $(mkIdent (tId ++ `instLawfulJson)):ident : LawfulJson $t where
        depthBound := 1 + $depthBoundExpr
        depth_toJson x := Nat.add_le_add_left $depthProofExpr 1
        fromJson_toJson := $fromJsonThmId) ]

open Lean Elab Command Term in
private def mkSchemaJsonCmds (t : Ident) (cbns : Array Ident) (cbts : Array Term)
    (tApp toJsonApp fromJsonApp : TSyntax `term)
    (fs : Array Ident) (inputs : Array Term) (refined : Array Bool)
    (jsonReads : Array (TSyntax `term)) (allLawful : Bool) :
    CommandElabM (Array (TSyntax `command)) := do
  let tId        := t.getId
  let decodeId   := mkIdent (tId ++ `decode)
  let encodeId   := mkIdent (tId ++ `encode)
  let toJsonId   := mkIdent (tId ++ `toJson)
  let fromJsonId := mkIdent (tId ++ `fromJson)
  let jsonDecodes ← ((fs.zip inputs).zip refined).mapM fun ((f, inp), r) => do
    let keyLit := Syntax.mkStrLit (toString f.getId)
    if r then `(($inp).fromJsonField j $keyLit)
    else `((FromJsonField.fromField j $keyLit : Except String (Codec.Val $inp)))
  let jsonPairs ← (fs.zip jsonReads).mapM fun (f, rd) =>
    let keyLit := Syntax.mkStrLit (toString f.getId); `(($keyLit, toJson $rd))
  let jsonFnCmds : Array (TSyntax `command) := #[
    ← `(command| def $toJsonId $[($cbns:ident : $cbts:term)]* (x : $tApp) : Json :=
          Json.obj [$[$jsonPairs],*]),
    ← `(command| def $fromJsonId $[($cbns:ident : $cbts:term)]* (j : Json) : Except String $tApp := do
          $[let $fs:ident ← $jsonDecodes:term]*
          return { $[$fs:ident],* }),
    ← `(command| def $decodeId $[($cbns:ident : $cbts:term)]* (s : String) (maxDepth : Nat := 64) :
          Except String $tApp := (Json.parse s maxDepth).bind ($fromJsonApp)),
    ← `(command| def $encodeId $[($cbns:ident : $cbts:term)]* (x : $tApp) : String :=
          Json.render ($toJsonApp x)) ]
  if !cbns.isEmpty then return jsonFnCmds
  let instCmds ← mkSchemaJsonInstCmds t toJsonId fromJsonId fs inputs refined jsonReads allLawful
  return jsonFnCmds ++ instCmds

open Lean Elab Command Term in
@[command_elab schemaCmd] def elabSchemaCmd : CommandElab
  | stx => do
      let t : Ident := ⟨(stx.getArg 1)⟩
      let rawCtx := if (stx.getArg 2).getNumArgs == 3 then ((stx.getArg 2).getArg 1).getSepArgs else #[]
      let cbns : Array Ident := rawCtx.map (⟨·.getArg 0⟩)
      let cbts ← rawCtx.mapM fun cp => liftMacroM (return (← Qed.Lang.lowerQedType (cp.getArg 2) false).1)
      let fStxs := (stx.getArg 4).getArgs
      let fs : Array Ident := fStxs.map (⟨·[0]⟩)
      let rawSpecs ← fStxs.mapM fun f => liftMacroM (lowerSchemaFieldSpec (f.getArg 2))
      let whereClauses : Array (Array Term) ← fStxs.mapM fun f => do
        if (f.getArg 3).getNumArgs == 2 then
          ((f.getArg 3).getArg 1).getSepArgs.mapM fun w => liftMacroM (Qed.Lang.lowerSimpleQedExpr .propInv w)
        else pure #[]
      let tId        := t.getId
      let draftId    := mkIdent (tId ++ `Draft)
      let beqFnId    := mkIdent (tId ++ `beq)
      let parseId    := mkIdent (tId ++ `parse)
      let canId      := mkIdent (tId ++ `canSubmit)
      let viewId     := mkIdent (tId ++ `formView)
      let toJsonId   := mkIdent (tId ++ `toJson)
      let fromJsonId := mkIdent (tId ++ `fromJson)
      let (inputs, refined, allLawful, allProto, allLawfulProto, allLawfulBEq) ←
        resolveSchemaFields cbns cbts fs rawSpecs whereClauses
      let pairs := fs.zip inputs
      checkSchemaFieldsDecidable cbns cbts pairs refined
      let cbnsT : Array (TSyntax `term) := cbns.map fun c => ⟨c.raw⟩
      let appTo : TSyntax `term → CommandElabM (TSyntax `term) := fun head =>
        cbnsT.foldlM (init := head) fun acc c => `($acc $c)
      let tApp        ← appTo ⟨t.raw⟩
      let beqApp      ← appTo ⟨beqFnId.raw⟩
      let parseApp    ← appTo ⟨parseId.raw⟩
      let canApp      ← appTo ⟨canId.raw⟩
      let viewApp     ← appTo ⟨viewId.raw⟩
      let toJsonApp   ← appTo ⟨toJsonId.raw⟩
      let fromJsonApp ← appTo ⟨fromJsonId.raw⟩
      let jsonReads ← (pairs.zip refined).mapM fun ((f, _), r) =>
        if r then `((x.$f:ident).val) else `(x.$f:ident)
      let (draftStructCmd, draftCmds) ← mkDraftCmds tId draftId fs
      let (coreStructCmd, coreCmds) ← mkSchemaCoreCmds t cbns cbts tApp beqApp parseApp canApp viewApp draftId fs inputs refined allLawfulBEq
      let jsonCmds ← mkSchemaJsonCmds t cbns cbts tApp toJsonApp fromJsonApp fs inputs refined jsonReads allLawful
      let protoCmds ← mkSchemaProtoCmds t cbns cbts tApp appTo fs inputs refined jsonReads allProto allLawfulProto
      for c in #[draftStructCmd, coreStructCmd] ++ draftCmds ++ coreCmds ++ jsonCmds ++ protoCmds do
        elabCommand c
      let ns ← getCurrNamespace
      let fullSchema := ns ++ tId
      let info : SchemaFormInfo := {
        fullName := fullSchema ++ `Form
        formViewName := fullSchema ++ `formView
        ctxBinders := cbns.map (·.getId.eraseMacroScopes)
      }
      modifyEnv fun env => schemaFormRegistry.addEntry env info

end Qed
