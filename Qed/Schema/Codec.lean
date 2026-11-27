import Qed.Notation
import Qed.Field
import Qed.Date

namespace Qed

structure Codec (α : Type) where mk ::
  (parse : String → Option α) (render : {msg : Type} → (raw : String) → (set : String → msg) → Html msg)
  (valid : α → Prop) (dec : DecidablePred valid) (inForm wrapLabel : Bool := true)
  (render_valid : ∀ {msg : Type} (inForm : Bool) (raw : String) (set : String → msg), Html.validIn ⟨.normal, false, false, inForm⟩ (render raw set) = true)

@[reducible] def Codec.Val {α : Type} (_ : Codec α) : Type := α

class DefaultCodec (α : Type) where codec : Codec α

namespace Codec

def refine (c : Codec α) (p : α → Prop) [DecidablePred p] : Codec α := { c with valid := p, dec := inferInstance }
def jsonOnly (c : Codec α) : Codec α := { c with inForm := false }

def run (c : Codec α) (raw : String) : Option (Field c.valid) :=
  haveI := c.dec
  match c.parse raw with | some a => if h : c.valid a then some ⟨a, h⟩ else none | none => none

theorem run_field_of_parse {α : Type} (c : Codec α) (raw : String) (f : Field c.valid)
    (h : c.parse raw = some f.val) : c.run raw = some f := by
  rcases f with ⟨v, hok⟩; simp [run, h, hok]

def validateField {α} (c : Codec α) (label : String) : Except String α → Except String (Field c.valid)
  | .error e => .error e
  | .ok a    => haveI := c.dec; if h : c.valid a then .ok ⟨a, h⟩ else .error s!"{label}: failed validation"

private theorem validateField_ok {α} (c : Codec α) (label : String) (f : Field c.valid)
    (e : Except String α) (h : e = .ok f.val) : c.validateField label e = .ok f := by
  rcases f with ⟨val, hok⟩; subst h; simp [validateField, hok]

def fromJsonField {α} (c : Codec α) [FromJsonField α] (j : Json) (key : String) : Except String (Field c.valid) :=
  c.validateField key (FromJsonField.fromField j key)

@[simp] theorem fromJsonField_of_field {α : Type} (c : Codec α) [ToJson α] [FromJsonField α] [LawfulFromJsonField α]
    (j : Json) (k : String) (f : Field c.valid) (h : j.field k = .ok (toJson f.val)) :
    c.fromJsonField j k = .ok f := c.validateField_ok k f _ (LawfulJson.fromField_of_field j k f.val h)

def fromProtoField {α} (c : Codec α) [FromProtoField α] (k : Nat) (fs : List (Nat × Proto.WireVal)) :
    Except String (Field c.valid) := c.validateField s!"field {k}" (FromProtoField.decodeProtoField k fs)

theorem fromProtoField_of_field {α : Type} (c : Codec α) [FromProtoField α]
    (k : Nat) (fs : List (Nat × Proto.WireVal)) (f : Field c.valid) (h : FromProtoField.decodeProtoField k fs = .ok f.val) :
    c.fromProtoField k fs = .ok f := c.validateField_ok s!"field {k}" f _ h

private theorem av_kv {msg : Type} (k v : String) (hs : isSafeAttrName k = true) (hu : isUrlAttrName k = false) :
    Attr.valid (msg := msg) (.attr k v) = true := by
  simp only [Attr.valid, Attr.validKeyValue, hs, hu, Bool.not_false, Bool.true_or, Bool.and_self]
private theorem av_value   {msg : Type} (v : String)       : (value v : Attr msg).valid = true := av_kv "value" v rfl rfl
private theorem av_type    {msg : Type} (v : String)       : (type' v : Attr msg).valid = true := av_kv "type" v rfl rfl
private theorem av_onInput {msg : Type} (f : String → msg) : (onInput f : Attr msg).valid = true := rfl
private theorem av_onChg   {msg : Type} (f : String → msg) : (onChange f : Attr msg).valid = true := av_onInput f
private theorem av_checked {msg : Type} (b : Bool)         : (checked b : Attr msg).valid = true := rfl

local macro "solve_attrs" : tactic =>
  `(tactic| (dsimp only [Attr.validList]; simp only [Attr.valid_cls, cls, av_value, av_type, av_onInput, av_onChg, av_checked,
      Bool.and_true, Bool.true_and, Bool.and_eq_true]; repeat any_goals constructor) <;> first | exact av_kv _ _ rfl rfl | rfl)

private theorem validIn_el {msg : Type} {ctx next : HtmlCtx} {tag : String} {attrs : List (Attr msg)} {kids : List (Html msg)}
    (hstep : stepHtmlCtx ctx tag = some next) (hvoid : isVoidTag tag = false ∨ kids = [])
    (hv : Attr.validList attrs = true) (hl : Attr.hasLocalCell attrs = false := by rfl)
    (hk : Html.validListIn next kids = true := by rfl) : Html.validIn ctx (el tag attrs kids) = true := by
  rcases hvoid with hnv | rfl
  · simp only [el, Html.validIn, hstep, hnv, hv, hl, hk, Bool.not_false, Bool.true_or, Bool.and_self]
  · simp only [el, Html.validIn, hstep, hv, hl, hk, List.isEmpty_nil, Bool.not_false, Bool.or_true, Bool.and_self]

private theorem step_inForm {tag : String} {m : TagMode} {p inter : Bool} (inForm : Bool) (hnf : (tag == "form") = false := by rfl)
    (h : stepHtmlCtx ⟨.normal, false, false, false⟩ tag = some ⟨m, p, inter, false⟩) :
    stepHtmlCtx ⟨.normal, false, false, inForm⟩ tag = some ⟨m, p, inter, inForm⟩ := by
  cases inForm with | false => exact h | true =>
    have hite : ∀ {c : Prop} [Decidable c] {a b : Option HtmlCtx},
        (if c then a else b).map ({ · with inForm := true }) = if c then a.map ({ · with inForm := true }) else b.map ({ · with inForm := true }) := by
      intros; split <;> rfl
    have heq : (stepHtmlCtx ⟨.normal, false, false, false⟩ tag).map ({ · with inForm := true }) = stepHtmlCtx ⟨.normal, false, false, true⟩ tag := by
      unfold stepHtmlCtx; simp only [hnf, Bool.and_false, Bool.or_false, Bool.false_and, Bool.false_or, hite, Option.map_none, Option.map_some]
    rw [← heq, h]; rfl

private theorem validIn_nf {msg : Type} (inForm : Bool) {tag : String} {m : TagMode} {p inter : Bool}
    {attrs : List (Attr msg)} {kids : List (Html msg)}
    (hstep : stepHtmlCtx ⟨.normal, false, false, false⟩ tag = some ⟨m, p, inter, false⟩)
    (hv : Attr.validList attrs = true := by rfl) (hk : Html.validListIn ⟨m, p, inter, inForm⟩ kids = true := by rfl)
    (hvoid : isVoidTag tag = false := by rfl) (hnf : (tag == "form") = false := by rfl)
    (hl : Attr.hasLocalCell attrs = false := by rfl) : Html.validIn ⟨.normal, false, false, inForm⟩ (el tag attrs kids) = true :=
  validIn_el (step_inForm inForm hnf hstep) (.inl hvoid) hv hl hk

private abbrev mkSimpleCodec {α : Type} (parse : String → Option α) (render : {msg : Type} → String → (String → msg) → Html msg)
    (render_valid : ∀ {msg : Type} (inForm : Bool) (raw : String) (set : String → msg), Html.validIn ⟨.normal, false, false, inForm⟩ (render raw set) = true)
    (inForm : Bool := true) (wrapLabel : Bool := true) : Codec α :=
  { parse, render, valid := fun _ => True, dec := fun _ => inferInstance, inForm, wrapLabel, render_valid }

private theorem step_input (inForm : Bool) : stepHtmlCtx ⟨.normal, false, false, inForm⟩ "input" = some ⟨.normal, false, false, inForm⟩ := step_inForm inForm rfl rfl

private abbrev mkInputCodec {α : Type} (parse : String → Option α) (attrs : {msg : Type} → String → (String → msg) → List (Attr msg))
    (hv : ∀ {msg : Type} (raw : String) (set : String → msg), Attr.validList (attrs raw set) = true)
    (hl : ∀ {msg : Type} (raw : String) (set : String → msg), Attr.hasLocalCell (attrs raw set) = false := by intros; rfl) : Codec α :=
  mkSimpleCodec parse (fun raw set => el "input" (attrs raw set)) (fun inForm raw set => validIn_el (step_input inForm) (.inr rfl) (hv raw set) (hl raw set))

def text     : Codec String := mkInputCodec some (fun raw set => [value raw, onInput set]) (fun _ _ => by solve_attrs)
def textarea : Codec String := mkSimpleCodec some (fun raw set => el "textarea" [value raw, onInput set]) (fun inForm _ _ => validIn_nf inForm rfl (by solve_attrs))

@[simp] theorem run_refine_text (p : String → Prop) [DecidablePred p]
    (f : Field (refine text p).valid) : (refine text p).run f.val = some f := run_field_of_parse _ _ f rfl
@[simp] theorem run_refine_textarea (p : String → Prop) [DecidablePred p]
    (f : Field (refine textarea p).valid) : (refine textarea p).run f.val = some f := run_field_of_parse _ _ f rfl
def nat      : Codec Nat    := mkInputCodec Qed.Str.parseNat? (fun raw set => [type' "number", attr "min" "0", value raw, onInput set]) (fun _ _ => by solve_attrs)
def int      : Codec Int    := mkInputCodec Qed.Str.parseInt? (fun raw set => [type' "number", value raw, onInput set]) (fun _ _ => by solve_attrs)
def checkbox : Codec Bool   := mkInputCodec (fun s => some (s == "true")) (fun raw set => [type' "checkbox", checked (raw == "true"), onCheck (fun b => set (toString b))]) (fun _ _ => by solve_attrs)
def date     : Codec Date   := mkInputCodec Date.parse? (fun raw set => [type' "date", value raw, onInput set]) (fun _ _ => by solve_attrs)

def select (options : List (String × String)) : Codec String :=
  mkSimpleCodec (fun s => if options.any (·.1 == s) then some s else none)
    (fun raw set => el "select" [value raw, onChange set] (options.map fun (v, lbl) => el "option" [value v] [lbl]))
    (fun inForm _ _ => validIn_nf inForm rfl (by solve_attrs)
      (Html.validListIn_map_intro _ _ _ fun _ => validIn_el (next := ⟨.option, false, true, inForm⟩) rfl (.inl rfl) (by solve_attrs)))

def radios (group : String) (options : List (String × String)) : Codec String :=
  mkSimpleCodec (fun s => if options.any (·.1 == s) then some s else none)
    (fun raw set => el "div" [cls "qed-radios"] (options.map fun (v, lbl) =>
      el "label" [] [el "input" [type' "radio", Qed.name group, value v, checked (raw == v), onChange set], lbl]))
    (fun inForm _ _ => validIn_nf (m := .normal) (p := false) (inter := false) inForm rfl (hk := Html.validListIn_map_intro _ _ _ fun _ =>
      validIn_nf (m := .normal) (p := false) (inter := false) inForm rfl (hk := by
        simp only [Html.validListIn, Bool.and_true, Bool.and_eq_true]
        exact ⟨validIn_el (step_input inForm) (.inr rfl) (by solve_attrs), rfl⟩))) (wrapLabel := false)

def json (α : Type) [ToJson α] [FromJson α] : Codec α :=
  mkSimpleCodec (fun _ => none) (fun _ _ => el "span" [] []) (fun inForm _ _ => validIn_nf inForm rfl) (inForm := false)

@[simp] theorem render_valid_simp {α msg : Type} (c : Codec α) (inForm : Bool) (raw : String) (set : String → msg) :
    Html.validIn ⟨.normal, false, false, inForm⟩ (c.render raw set) = true := c.render_valid inForm raw set

def formFieldRow {msg : Type} (inForm wrapLabel bad : Bool) (label err : String) (ctrl : Html msg) : List (Html msg) :=
  if inForm then
    [el (if wrapLabel then "label" else "fieldset") [cls "qed-field", attr "aria-invalid" (if bad then "true" else "false")]
      ([el (if wrapLabel then "span" else "legend") [cls "qed-label"] [label], ctrl] ++ if bad then [el "span" [cls "qed-error"] [err]] else [])]
  else []

@[simp] theorem formFieldRow_validListIn {msg : Type} (ctxInForm inForm wrapLabel bad : Bool)
    (label err : String) (ctrl : Html msg) (hctrl : Html.validIn ⟨.normal, false, false, ctxInForm⟩ ctrl = true) :
    Html.validListIn ⟨.normal, false, false, ctxInForm⟩ (formFieldRow inForm wrapLabel bad label err ctrl) = true := by
  cases inForm with | false => rfl | true =>
    have hSpan (c s : String) : Html.validIn (msg := msg) ⟨.normal, false, false, ctxInForm⟩ (el "span" [cls c] [s]) = true := validIn_nf ctxInForm rfl
    have hLbl : Html.validIn (msg := msg) ⟨.normal, false, false, ctxInForm⟩ (el (if wrapLabel then "span" else "legend") [cls "qed-label"] [label]) = true := by
      cases wrapLabel; exact validIn_nf ctxInForm rfl; exact hSpan _ _
    have hTail : Html.validListIn (msg := msg) ⟨.normal, false, false, ctxInForm⟩ (if bad then [el "span" [cls "qed-error"] [err]] else []) = true := by
      cases bad with | false => rfl | true => simp only [ite_true, Html.validListIn, hSpan, Bool.and_true]
    have hStep : stepHtmlCtx ⟨.normal, false, false, ctxInForm⟩ (if wrapLabel then "label" else "fieldset") = some ⟨.normal, false, false, ctxInForm⟩ := by
      cases wrapLabel <;> exact step_inForm ctxInForm rfl rfl
    have hVoid : isVoidTag (if wrapLabel then "label" else "fieldset") = false := by cases wrapLabel <;> rfl
    dsimp only [formFieldRow]; simp only [ite_true, Html.validListIn, Bool.and_true]
    exact validIn_el hStep (.inl hVoid) (by solve_attrs) rfl (by simp only [List.cons_append, List.nil_append, Html.validListIn, hLbl, hctrl, hTail, Bool.and_self])

theorem formDiv_validIn {msg : Type} (inForm : Bool) (kids : List (Html msg)) (hk : Html.validListIn ⟨.normal, false, false, inForm⟩ kids = true) :
    Html.validIn ⟨.normal, false, false, inForm⟩ (el "div" [cls "qed-form"] kids) = true := validIn_nf inForm rfl (hk := hk)

theorem formRowCons_validIn {msg : Type} (ctxInForm inForm wrapLabel bad : Bool) (label err : String) (ctrl : Html msg) (rest : List (Html msg))
    (hctrl : Html.validIn ⟨.normal, false, false, ctxInForm⟩ ctrl = true) (hrest : Html.validListIn ⟨.normal, false, false, ctxInForm⟩ rest = true) :
    Html.validListIn ⟨.normal, false, false, ctxInForm⟩ (formFieldRow inForm wrapLabel bad label err ctrl ++ rest) = true := by
  rw [Html.validListIn_append, formFieldRow_validListIn ctxInForm inForm wrapLabel bad label err ctrl hctrl, hrest]; rfl

def submitBtn {msg α : Type} (o : Option α) (submit : α → msg) : Html msg :=
  match o with | some p => el "button" [onClick (submit p)] "Submit" | none => el "button" [disabled true] "Submit"

theorem submitBtn_validIn {msg α : Type} (inForm : Bool) (o : Option α) (submit : α → msg) :
    Html.validListIn ⟨.normal, false, false, inForm⟩ [submitBtn o submit] = true := by
  have hb := step_inForm inForm (tag := "button") rfl rfl
  cases o <;> (simp only [submitBtn, Html.validListIn, Bool.and_true]; exact validIn_el hb (.inl rfl) (by solve_attrs))

def ofField {α : Type} (c : Codec α) (p : α → Prop) [DecidablePred p] : Codec (Field p) where
  parse s := (c.parse s).bind (Field.parse? p)
  render := c.render
  valid _ := True
  dec _ := inferInstance
  inForm := c.inForm
  wrapLabel := c.wrapLabel
  render_valid := c.render_valid

end Codec

@[reducible] instance : DefaultCodec String := ⟨Codec.text⟩
@[reducible] instance : DefaultCodec Nat    := ⟨Codec.nat⟩
@[reducible] instance : DefaultCodec Int    := ⟨Codec.int⟩
@[reducible] instance : DefaultCodec Bool   := ⟨Codec.checkbox⟩
@[reducible] instance : DefaultCodec Date   := ⟨Codec.date⟩
@[reducible] instance {α : Type} {p : α → Prop} [DefaultCodec α] [DecidablePred p] : DefaultCodec (Field p) :=
  ⟨Codec.ofField DefaultCodec.codec p⟩
@[reducible] instance (priority := low) {α : Type} [ToJson α] [FromJson α] : DefaultCodec α := ⟨Codec.json α⟩

end Qed
