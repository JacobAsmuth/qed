import Qed.Notation
import Qed.Lang
import Qed.Field
import Qed.Json
import Qed.Proto
import Qed.Date
import Qed.Schema.Registry
import Lean

namespace Qed

structure Codec (α : Type) where mk ::
  (parse : String → Option α) (render : {msg : Type} → (raw : String) → (set : String → msg) → Html msg)
  (valid : α → Prop) (dec : DecidablePred valid) (inForm wrapLabel : Bool := true)
  (render_valid : ∀ {msg : Type} (inForm : Bool) (raw : String) (set : String → msg), Html.validIn ⟨.normal, false, false, inForm⟩ (render raw set) = true)

@[reducible] def Codec.Val {α : Type} (_ : Codec α) : Type := α

namespace Codec

def refine (c : Codec α) (p : α → Prop) [DecidablePred p] : Codec α := { c with valid := p, dec := inferInstance }
def jsonOnly (c : Codec α) : Codec α := { c with inForm := false }

def run (c : Codec α) (raw : String) : Option (Field c.valid) :=
  haveI := c.dec
  match c.parse raw with | some a => if h : c.valid a then some ⟨a, h⟩ else none | none => none

def validateField {α} (c : Codec α) (label : String) : Except String α → Except String (Field c.valid)
  | .error e => .error e
  | .ok a    => haveI := c.dec; if h : c.valid a then .ok ⟨a, h⟩ else .error s!"{label}: failed validation"

private theorem validateField_ok {α} (c : Codec α) (label : String) (f : Field c.valid)
    (e : Except String α) (h : e = .ok f.val) : c.validateField label e = .ok f := by
  rcases f with ⟨val, hok⟩; subst h; simp [validateField, hok]

def fromJsonField {α} (c : Codec α) [FromJsonField α] (j : Json) (key : String) : Except String (Field c.valid) :=
  c.validateField key (FromJsonField.fromField j key)

@[simp] theorem fromJsonField_of_field {α : Type} (c : Codec α) [LawfulJson α]
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
def nat      : Codec Nat    := mkInputCodec String.toNat? (fun raw set => [type' "number", attr "min" "0", value raw, onInput set]) (fun _ _ => by solve_attrs)
def int      : Codec Int    := mkInputCodec String.toInt? (fun raw set => [type' "number", value raw, onInput set]) (fun _ _ => by solve_attrs)
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

end Codec

class DefaultCodec (α : Type) where codec : Codec α
@[reducible] instance : DefaultCodec String := ⟨Codec.text⟩
@[reducible] instance : DefaultCodec Nat    := ⟨Codec.nat⟩
@[reducible] instance : DefaultCodec Int    := ⟨Codec.int⟩
@[reducible] instance : DefaultCodec Bool   := ⟨Codec.checkbox⟩
@[reducible] instance : DefaultCodec Date   := ⟨Codec.date⟩
@[reducible] instance (priority := low) {α : Type} [ToJson α] [FromJson α] : DefaultCodec α := ⟨Codec.json α⟩

section SchemaParsers
open Lean Parser
private abbrev pType : Parser := categoryParser `qedType 0
private abbrev pExpr : Parser := categoryParser `qedExpr 0
def schemaCtxParamP     : Parser := node `Qed.schemaCtxParam (ident >> ":" >> pType)
def schemaFieldJsonOnly : Parser := node `Qed.schemaFieldJsonOnly (atomic (identEq `jsonOnly >> checkNoWsBefore "" >> "(") >> pType >> ")")
def schemaFieldCall     : Parser := node `Qed.schemaFieldCall (atomic (ident >> checkNoWsBefore "" >> "(") >> sepBy (categoryParser `qedCallArg 0) "," >> ")")
def schemaFieldSpec     : Parser := schemaFieldJsonOnly <|> schemaFieldCall <|> pType
def schemaFieldP        : Parser := node `Qed.schemaField (withPosition (ident >> ":" >> schemaFieldSpec >> optional (checkColGt >> " where " >> sepBy1 pExpr ",")))
def schemaExampleFieldP : Parser := node `Qed.schemaExampleField (checkColGt >> ident >> "=" >> pExpr)
def schemaExampleP      : Parser := node `Qed.schemaExample (withPosition (atomic (symbol "example" >> ident >> ":") >> sepBy1 schemaExampleFieldP ","))
def schemaItemP         : Parser := schemaExampleP <|> schemaFieldP
@[command_parser] def schemaCmd : Parser := leading_parser withPosition
  ("schema " >> ident >> optional (checkLineEq >> "(" >> sepBy1 schemaCtxParamP "," >> ")") >> ":" >> checkColGt "expected indented `schema` fields" >> many1Indent schemaItemP)
end SchemaParsers

section SchemaElab
open Lean Elab Command Term Meta

private def lowerSchemaFieldSpec (stx : Syntax) : MacroM Term := match stx.getKind with
  | `Qed.schemaFieldJsonOnly => do `(jsonOnly $((← Qed.Lang.lowerQedType (stx.getArg 2) false).1))
  | `Qed.schemaFieldCall     => do Qed.Lang.mkAppTerms ⟨stx.getArg 0⟩ (← (stx.getArg 2).getSepArgs.mapM fun a => Qed.Lang.lowerSimpleQedExpr .val (a.getArg 0))
  | _                        => do return (← Qed.Lang.lowerQedType stx false).1

private def primSchemaTypes : Array (Name × Name) :=
  #[(``String, ``Qed.Codec.text), (``Nat, ``Qed.Codec.nat), (``Int, ``Qed.Codec.int), (``Bool, ``Qed.Codec.checkbox), (``Qed.Date, ``Qed.Codec.date)]

private partial def resolveCodecBase (fieldName : Name) (rawSpec : Term) : TermElabM Term := do
  if let `($fn:ident $arg:term) := rawSpec then
    if fn.getId.eraseMacroScopes == `jsonOnly then return ← `(Qed.Codec.jsonOnly $(← resolveCodecBase fieldName arg))
  let scopedSpec ← `(open Qed.Codec in $rawSpec)
  let e ← elabTermAndSynthesize scopedSpec none; let ety ← whnf (← instantiateMVars (← inferType e))
  if ety.isAppOfArity ``Qed.Codec 1 then return scopedSpec
  else if ety.isSort then
    let eWhnf ← whnf (← instantiateMVars e)
    if let some (_, codecNm) := primSchemaTypes.find? (eWhnf.isConstOf ·.1) then return mkCIdent codecNm
    if (← trySynthInstance (← mkAppM ``Qed.DefaultCodec #[e])) matches .some _ then return ← `((Qed.DefaultCodec.codec : Qed.Codec $rawSpec))
    throwErrorAt rawSpec m!"schema field `{fieldName}` has type `{rawSpec}`, which has no default `Codec` or JSON (`ToJson`/`FromJson`) instances.\nProvide a `DefaultCodec` or JSON instances for `{rawSpec}`, or use a supported field type (`String`, `Nat`, `Int`, `Bool`, `Date`, `select([...])`, `textarea`, `jsonOnly(...)`)."
  else throwErrorAt rawSpec m!"schema field `{fieldName}` must be a type (`String`, `Nat`, `Int`, `Bool`, `Date`, …) or a `Codec` (e.g. `select([...])`, `textarea`, `jsonOnly(String)`), but this has type{indentExpr ety}"

private structure ResolvedSchemaField where mk ::
  (input : Term) (isRefined isLawful isProto isLawfulP isLawfulBEq : Bool) (tyName : Name) (hasInhab : Bool)
deriving Inhabited

private structure SchemaCtx where mk ::
  (t : Ident) (cbns : Array Ident) (cbts : Array Term) (tApp : Term)
  (fs : Array Ident) (inputs : Array Term) (refined : Array Bool) (whereLabels : Array String)

private def SchemaCtx.appTo (sc : SchemaCtx) (head : Term) : CommandElabM Term := Qed.Lang.mkAppTerms head (sc.cbns.map (⟨·.raw⟩))

private partial def withCtxDecls {α : Type} (cbns : Array Ident) (cbts : Array Term) (k : TermElabM α) (i : Nat := 0) : TermElabM α := do
  if i < cbns.size then withLocalDeclD cbns[i]!.getId (← elabType cbts[i]!) fun _ => withCtxDecls cbns cbts k (i + 1) else k

private def elabSchemaFieldsAux (cbns : Array Ident) (cbts : Array Term)
    (fs : Array Ident) (rawSpecs : Array Term) (whereClauses : Array (Array Term)) : TermElabM (Array ResolvedSchemaField) :=
  withCtxDecls cbns cbts do
    ((fs.zip rawSpecs).zip whereClauses).mapM fun ((f, rawSpec), preds) => do
      let base ← resolveCodecBase f.getId rawSpec
      let inp : Term ← if preds.isEmpty then pure base else `(Qed.Codec.refine $base (fun $f:ident => $(← mkConjBody preds)))
      let savedLog ← Core.getMessageLog; let preCount := savedLog.toList.length
      let c ← elabTermAndSynthesize inp none
      if ← ((← Core.getMessageLog).toList.drop preCount).anyM fun msg => return ((← msg.data.toString).splitOn "DecidablePred").length > 1 then
        Core.setMessageLog savedLog
        throwErrorAt inp m!"schema field `{f.getId}` has a refinement that isn't decidable, so validity can't be computed (no `DecidablePred` for it).\n\nThe usual cause is a predicate written with `def`. Write it inline with `where …` or as an `abbrev`, so Lean sees it reduces to a decidable check:\n    abbrev MyPredicate (x : …) : Prop := …\nIf it genuinely can't be decided, give it a `DecidablePred` instance."
      match (← instantiateMVars (← inferType c)).getAppFnArgs with
      | (``Qed.Codec, #[α]) =>
          let isRefined := !(← isDefEq (mkApp2 (mkConst ``Qed.Codec.valid) α c) (Expr.lam `x α (mkConst ``True) .default))
          let hasInst (cls : Name) (lvls : List Level := []) : MetaM Bool := return (← trySynthInstance (mkApp (mkConst cls lvls) α)) matches .some _
          let isLawfulBEq ← match ← trySynthInstance (mkApp (mkConst ``BEq [Level.zero]) α) with
            | .some beqInst => pure ((← trySynthInstance (mkApp2 (mkConst ``LawfulBEq [Level.zero]) α beqInst)) matches .some _) | _ => pure false
          let isProto ← if ← hasInst ``Qed.ToProtoField then hasInst ``Qed.FromProtoField else pure false
          let isLawfulP ← if isProto then hasInst ``Qed.LawfulProtoField else pure false
          return .mk inp isRefined (← hasInst ``Qed.LawfulJson) isProto isLawfulP isLawfulBEq
            ((← whnf α).constName?.getD .anonymous) (← hasInst ``Inhabited [Level.zero])
      | _ => throwErrorAt rawSpec m!"failed to resolve schema field `{f.getId}` to a `Codec`"

private def mkSchemaBeqCmds (sc : SchemaCtx) (allLawfulBEq : Bool) : CommandElabM (Array (TSyntax `command)) := do
  let (tId, cbns, cbts, tApp, fs) := (sc.t.getId, sc.cbns, sc.cbts, sc.tApp, sc.fs)
  let beqFnId := mkIdent (tId ++ `beq); let beqApp ← sc.appTo ⟨beqFnId.raw⟩
  let beqExpr ← match fs.toList with
    | [] => `(true) | f :: rest => rest.foldlM (init := ← `(a.$f:ident == b.$f:ident)) fun acc fi => `($acc && (a.$fi:ident == b.$fi:ident))
  let base : Array (TSyntax `command) := #[
    ← `(command| def $beqFnId $[($cbns:ident : $cbts:term)]* (a b : $tApp) : Bool := $beqExpr),
    ← `(command| instance $(mkIdent (tId ++ `instBEq)):ident $[($cbns:ident : $cbts:term)]* : BEq $tApp := ⟨$beqApp⟩) ]
  if !allLawfulBEq then return base
  let (eqId, rflId) := (mkIdent (tId ++ `_eq_of_beq), mkIdent (tId ++ `_beq_rfl))
  return base ++ #[
    ← `(command| private theorem $eqId $[($cbns:ident : $cbts:term)]* {a b : $tApp} (h : $beqApp a b = true) : a = b := by
          cases a; cases b; dsimp only [$beqFnId:ident] at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; simp_all only),
    ← `(command| private theorem $rflId $[($cbns:ident : $cbts:term)]* {a : $tApp} : $beqApp a a = true := by
          cases a; dsimp only [$beqFnId:ident]; simp only [beq_self_eq_true, Bool.and_self]),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulBEq)):ident $[($cbns:ident : $cbts:term)]* : LawfulBEq $tApp where eq_of_beq := $eqId; rfl := $rflId) ]

private def mkSchemaCoreCmds (sc : SchemaCtx) (draftId : Ident) : CommandElabM (Array (TSyntax `command)) := do
  let (t, tId, cbns, cbts, tApp, fs) := (sc.t, sc.t.getId, sc.cbns, sc.cbts, sc.tApp, sc.fs); let pairs := fs.zip sc.inputs
  let structTys ← (pairs.zip sc.refined).mapM fun ((_, inp), r) => if r then `(Field ($inp).valid) else `(Codec.Val $inp)
  let runCalls ← (pairs.zip sc.refined).mapM fun ((f, inp), r) => if r then `(($inp).run (d.$f:ident)) else `(($inp).parse (d.$f:ident))
  let (parseId, canId, viewId) := (mkIdent (tId ++ `parse), mkIdent (tId ++ `canSubmit), mkIdent (tId ++ `formView))
  let (parseApp, canApp, viewApp) := (← sc.appTo ⟨parseId.raw⟩, ← sc.appTo ⟨canId.raw⟩, ← sc.appTo ⟨viewId.raw⟩)
  let rhs ← mkConjBody (← runCalls.mapM fun rc => `(($rc).isSome)) (ascribeProp := false)
  let casesTac ← runCalls.foldrM
    (init := ← `(tactic| simp only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true, and_true, true_and, and_false, false_and, iff_self, bind, Option.bind, pure, Pure.pure]))
    fun rc acc => `(tactic| cases $rc:term with
      | none => simp only [Option.isSome_none, Bool.false_eq_true, false_and, and_false, iff_self, bind, Option.bind] | some _ => ($acc:tactic))
  let rowGroups ← (pairs.zip runCalls).mapM fun ((f, inp), rc) =>
    `(term| Codec.formFieldRow ($inp).inForm ($inp).wrapLabel (d.$f:ident != "" && ($rc).isNone)
              $(Syntax.mkStrLit (toString f.getId)) $(Syntax.mkStrLit ("Please enter a valid " ++ toString f.getId))
              (($inp).render (d.$f:ident) (fun v => onEdit { d with $f:ident := v })))
  let viewBody ← rowGroups.foldrM (init := ← `(term| [Codec.submitBtn ($parseApp d) submit])) fun g acc => `(term| $g ++ $acc)
  let validBodyPf ← sc.inputs.foldrM (init := ← `(term| Codec.submitBtn_validIn inForm ($parseApp d) submit))
    fun inp acc => `(term| Codec.formRowCons_validIn inForm _ _ _ _ _ _ _ (($inp).render_valid inForm _ _) $acc)
  pure #[
    ← `(command| structure $t $[($cbns:ident : $cbts:term)]* where $[$fs:ident : $structTys]*),
    ← `(command| def $parseId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Option $tApp := do
          $[let $fs:ident ← $runCalls:term]*
          return { $[$fs:ident],* }),
    ← `(command| def $canId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Bool := ($parseApp d).isSome),
    ← `(command| theorem $(mkIdent (tId ++ `canSubmit_iff)) $[($cbns:ident : $cbts:term)]* (d : $draftId) : $canApp d = true ↔ $rhs := by unfold $canId $parseId; $casesTac),
    ← `(command| def $viewId {msg : Type} $[($cbns:ident : $cbts:term)]* (d : $draftId) (onEdit : $draftId → msg) (submit : $tApp → msg) : Html msg := el "div" [cls "qed-form"] $viewBody),
    ← `(command| @[simp] theorem $(mkIdent (tId ++ `formView_validIn)) {msg : Type} $[($cbns:ident : $cbts:term)]* (inForm : Bool) (d : $draftId) (onEdit : $draftId → msg) (submit : $tApp → msg) :
          Html.validIn ⟨.normal, false, false, inForm⟩ ($viewApp d onEdit submit) = true := Codec.formDiv_validIn inForm _ $validBodyPf) ]

private partial def collectStxLits {α : Type} [BEq α] (extract : Syntax → Option α) (stx : Syntax) (acc : Array α) : Array α :=
  stx.getArgs.foldl (fun a ch => collectStxLits extract ch a) (match extract stx with | some v => Qed.Lang.pushUnique acc v | none => acc)

private def tryCheckPropWithTactic (goalTerm : Term) (tacStx : TSyntax `tactic) : CommandElabM Bool :=
  Qed.Diag.probeTermElabOk do
    discard <| elabTermEnsuringType (← `(by $tacStx:tactic)) (← elabType goalTerm); synthesizeSyntheticMVarsNoPostponing; return true

private def synthesizeFieldWitness? (pfTac : TSyntax `tactic) (rf : ResolvedSchemaField) (rawWheres : Array Syntax) : CommandElabM (Option Term) := do
  let inp := rf.input
  if !rf.isRefined then if rf.hasInhab then return some (← `((default : Qed.Codec.Val $inp))) else return none
  let nats := (rawWheres.foldl (fun acc w => collectStxLits (fun s => if s.getKind == ``Qed.Lang.qedLitNum then some (⟨s.getArg 0⟩ : TSyntax `num).getNat else none) w acc) #[]).toList
  let cands : Array Term ← match rf.tyName with
    | ``Bool => pure #[← `((Bool.true : Bool)), ← `((Bool.false : Bool))]
    | ``Nat  => ((nats.flatMap fun n => [n, n + 1, n - 1]) ++ [0, 1, 2, 3, 5, 10, 18, 21, 50, 100]).eraseDups.toArray.mapM fun k => `(($(quote k) : Nat))
    | ``Int  => ((nats.flatMap fun n => let z : Int := Int.ofNat n; [z, z + 1, z - 1, -z, -z - 1, -z + 1]) ++ [(0 : Int), 1, -1, 2, 10, 100]).eraseDups.toArray.mapM fun k =>
        if k >= 0 then `(($(quote k.toNat) : Int)) else `((-($(quote (-k).toNat) : Int)))
    | ``String =>
        let strs := (rawWheres.foldl (fun acc w => collectStxLits (fun s => if s.getKind == ``Qed.Lang.qedLitStr then some (⟨s.getArg 0⟩ : TSyntax `str).getString else none) w acc) #[]).toList
        let lens := nats.flatMap fun n => (if n > 0 && n ≤ 64 then [String.ofList (List.replicate n 'a')] else []) ++ (if n + 1 ≤ 64 then [String.ofList (List.replicate (n + 1) 'a')] else [])
        (strs ++ ["", "a", "alice", "a@b.com", "https://example.com", "12345678", "aaaaaaaaaa"] ++ lens).eraseDups.toArray.mapM fun s => `(($(quote s) : String))
    | ``Qed.Date => pure #[← `(({ year := 2026, month := 1, day := 1 } : Qed.Date))]
    | _          => if rf.hasInhab then pure #[← `((default : Qed.Codec.Val $inp))] else pure #[]
  for cand in cands do
    if ← tryCheckPropWithTactic (← `(($inp).valid $cand)) pfTac then return some (← `(Qed.Field.mk (p := ($inp).valid) $cand (by $pfTac:tactic)))
  return none

private def emitSatisfiableCmds (sc : SchemaCtx) (ref : Syntax) (witness : Term) : CommandElabM Unit := do
  let (t, cbns, cbts, tApp) := (sc.t, sc.cbns, sc.cbts, sc.tApp)
  elabCommand (← `(command| theorem $(mkIdentFrom ref (t.getId ++ `satisfiable)) $[($cbns:ident : $cbts:term)]* : ∃ _x : $tApp, True := ⟨$witness, trivial⟩))
  if cbns.isEmpty then elabCommand (← `(command| instance $(mkIdentFrom ref (t.getId ++ `instNonempty)):ident : Nonempty $t := ⟨$witness⟩))

private def elabSchemaExampleClause (sc : SchemaCtx) (pfTac : TSyntax `tactic) (exStx : Syntax) (emitSatisfiable : Bool) : CommandElabM Unit := do
  let (tId, cbns, cbts, tApp, fs) := (sc.t.getId, sc.cbns, sc.cbts, sc.tApp, sc.fs)
  let exName : Ident := ⟨exStx.getArg 1⟩; let exId := exName.getId; let validNames := fs.toList.map (·.getId.toString)
  let mut provided : Std.HashMap String Syntax := {}
  for entry in (exStx.getArg 3).getSepArgs do
    let fid : Ident := ⟨entry.getArg 0⟩; let fName := fid.getId.toString
    unless validNames.contains fName do
      throwErrorAt fid s!"Schema `{tId}` example `{exId}`: unknown field `{fName}`{Qed.Diag.didYouMean fName validNames} (expected: {String.intercalate ", " validNames})"
    if provided.contains fName then throwErrorAt fid s!"Schema `{tId}` example `{exId}`: duplicate field `{fName}`"
    provided := provided.insert fName (entry.getArg 2)
  let fieldTerms ← fs.zipIdx.mapM fun (f, i) => do
    let fName := f.getId.toString
    let some valStx := provided[fName]? | throwErrorAt exStx s!"Schema `{tId}` example `{exId}`: missing required field `{fName}`"
    let valTerm ← liftMacroM (Qed.Lang.lowerSimpleQedExpr .val valStx)
    if !sc.refined[i]! then return valTerm
    if sc.cbns.isEmpty then
      unless ← tryCheckPropWithTactic (← `(($(sc.inputs[i]!)).valid $valTerm)) pfTac do
        let valStr := let s := Qed.Lang.stxSnippet valStx; if s.isEmpty then "<value>" else s
        throwErrorAt valStx m!"Schema `{tId}` example `{exId}` failed `where` constraint on field `{fName}`:\n  • value `{valStr}` does not satisfy `{sc.whereLabels[i]!}`\n\nHint: Update `{fName}` in example `{exId}` so it satisfies `{sc.whereLabels[i]!}`, or weaken the `where` rule."
    `(Qed.Field.mk (p := ($(sc.inputs[i]!)).valid) $valTerm (by $pfTac:tactic))
  let sampleId := mkIdentFrom exName (tId ++ exId)
  elabCommand (← `(command| def $sampleId $[($cbns:ident : $cbts:term)]* : $tApp := { $[$fs:ident := $fieldTerms:term],* }))
  if emitSatisfiable then emitSatisfiableCmds sc exStx (← sc.appTo ⟨sampleId.raw⟩)

private def checkSchemaSatAndExamples (sc : SchemaCtx) (resolved : Array ResolvedSchemaField)
    (whereRawExprs : Array (Array Syntax)) (exampleStxs : Array Syntax) : CommandElabM Unit := do
  let simpTac ← `(tactic| simp only [Qed.Codec.valid, Qed.Codec.refine, Qed.Codec.jsonOnly, Qed.Codec.text, Qed.Codec.textarea,
      Qed.Codec.nat, Qed.Codec.int, Qed.Codec.checkbox, Qed.Codec.date, Qed.Codec.select, Qed.Codec.radios, Qed.Codec.json, Qed.Lang.QedVal.val_id])
  let pfTac ← `(tactic| ($simpTac:tactic <;> first | rfl | decide | omega | trivial | (simp_all; try rfl; try decide; try omega)))
  if !exampleStxs.isEmpty then
    for (exStx, idx) in exampleStxs.zipIdx do elabSchemaExampleClause sc pfTac exStx (idx == 0)
  else if sc.cbns.isEmpty then
    for (rf, i) in resolved.zipIdx do
      if rf.isRefined then
        if ← tryCheckPropWithTactic (← `(∀ _qed_x : Qed.Codec.Val $(rf.input), ¬ ($(rf.input)).valid _qed_x))
            (← `(tactic| (intro _qed_x; $simpTac:tactic; first | omega | decide | (cases _qed_x <;> decide)))) then
          throwErrorAt sc.fs[i]! m!"Schema `{sc.t.getId}` is unsatisfiable: field `{sc.fs[i]!.getId}` has contradictory `where` constraints (`{sc.whereLabels[i]!}`) — no value can ever satisfy it.\n\nHint: Fix or remove the conflicting `where` conditions on `{sc.fs[i]!.getId}`."
    if let some synthTerms ← resolved.zipIdx.foldlM (init := some #[]) fun acc? (rf, i) => do
        let some arr := acc? | return none
        return (← synthesizeFieldWitness? pfTac rf whereRawExprs[i]!).map arr.push then
      let fs := sc.fs; emitSatisfiableCmds sc sc.t (← `({ $[$fs:ident := $synthTerms:term],* }))

@[command_elab schemaCmd] def elabSchemaCmd : CommandElab := fun stx => do
  let t : Ident := ⟨stx.getArg 1⟩; let tId := t.getId
  let rawCtx := if (stx.getArg 2).getNumArgs == 3 then ((stx.getArg 2).getArg 1).getSepArgs else #[]
  let cbns : Array Ident := rawCtx.map (⟨·.getArg 0⟩)
  let cbts ← rawCtx.mapM fun cp => liftMacroM (return (← Qed.Lang.lowerQedType (cp.getArg 2) false).1)
  let mut fStxs : Array Syntax := #[]; let mut exampleStxs : Array Syntax := #[]; let mut seenEx : Std.HashSet Name := {}
  for item in (stx.getArg 4).getArgs do
    if item.getKind == `Qed.schemaExample then
      let exName : Ident := ⟨item.getArg 1⟩
      if seenEx.contains exName.getId then throwErrorAt exName s!"duplicate example `{exName.getId}` in `schema {tId}`"
      seenEx := seenEx.insert exName.getId; exampleStxs := exampleStxs.push item
    else fStxs := fStxs.push item
  if fStxs.isEmpty then throwErrorAt t s!"`schema {tId}` must declare at least one field"
  let fs : Array Ident := fStxs.map (⟨·[0]⟩)
  let rawSpecs ← fStxs.mapM fun f => liftMacroM (lowerSchemaFieldSpec (f.getArg 2))
  let whereRawExprs := fStxs.map fun f => if (f.getArg 3).getNumArgs == 2 then ((f.getArg 3).getArg 1).getSepArgs else #[]
  let whereLabels := whereRawExprs.map fun ws => String.intercalate ", " (ws.toList.map fun w => let s := Qed.Lang.stxSnippet w; if s.isEmpty then "constraint" else s)
  let whereClauses ← whereRawExprs.mapM fun ws => ws.mapM fun w => liftMacroM (Qed.Lang.lowerSimpleQedExpr .propInv w)
  let resolved ← liftTermElabM (elabSchemaFieldsAux cbns cbts fs rawSpecs whereClauses)
  let (inputs, refined) := (resolved.map (·.input), resolved.map (·.isRefined))
  let sc : SchemaCtx := { t, cbns, cbts, tApp := ← Qed.Lang.mkAppTerms ⟨t.raw⟩ (cbns.map (⟨·.raw⟩)), fs, inputs, refined, whereLabels }
  let draftId := mkIdent (tId ++ `Draft)
  let draftFields ← fs.mapM fun f => return ({ ident := f, wireKey := f.getId.toString, valTy := ← `(String) } : StructFieldSpec)
  let schemaFields ← ((fs.zip inputs).zip refined).mapM fun ((f, inp), r) =>
    return ({ ident := f, wireKey := f.getId.toString, valTy := ← `(Codec.Val $inp), codecTerm? := if r then some inp else none } : StructFieldSpec)
  let ctxBinders := cbns.zip cbts
  let cmds : Array (TSyntax `command) := #[
    ← `(command| structure $draftId where $[$fs:ident : String := ""]* deriving Inhabited, DecidableEq, Repr),
    ← `(command| def $(mkIdent (tId ++ `Draft ++ `empty)) : $draftId := {})] ++
    (← mkStructJsonCmds draftId draftFields { fixedDepthBound := some 1 }) ++ (← mkSchemaCoreCmds sc draftId) ++
    (← mkSchemaBeqCmds sc (resolved.all (·.isLawfulBEq))) ++
    (← mkStructJsonCmds t schemaFields { ctxBinders, emitStringCodec := true, emitLawful := resolved.all (·.isLawful) }) ++
    (← if resolved.all (·.isProto) then mkStructProtoCmds t schemaFields { ctxBinders, emitBytesCodec := true, emitLawful := resolved.all (·.isLawfulP) } else pure #[])
  cmds.forM elabCommand
  checkSchemaSatAndExamples sc resolved whereRawExprs exampleStxs
  let fullSchema := (← getCurrNamespace) ++ tId
  modifyEnv fun env => schemaFormRegistry.addEntry env {
    fullName := fullSchema ++ `Form, formViewName := fullSchema ++ `formView, ctxBinders := cbns.map (·.getId.eraseMacroScopes) }

end SchemaElab
end Qed
