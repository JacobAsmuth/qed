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

def validateField {α} (c : Codec α) (label : String) : Except String α → Except String (Field c.valid)
  | .error e => .error e
  | .ok a    => haveI := c.dec; if h : c.valid a then .ok ⟨a, h⟩ else .error s!"{label}: failed validation"

private theorem validateField_ok {α} (c : Codec α) (label : String) (f : Field c.valid)
    (e : Except String α) (h : e = .ok f.val) : c.validateField label e = .ok f := by
  rcases f with ⟨val, hok⟩; subst h; simp [validateField, hok]

def fromJsonField {α} (c : Codec α) [FromJsonField α] (j : Json) (key : String) :
    Except String (Field c.valid) :=
  c.validateField key (FromJsonField.fromField j key)

@[simp] theorem fromJsonField_of_field {α : Type} (c : Codec α) [LawfulJson α]
    (j : Json) (k : String) (f : Field c.valid) (h : j.field k = .ok (toJson f.val)) :
    c.fromJsonField j k = .ok f :=
  c.validateField_ok k f _ (LawfulJson.fromField_of_field j k f.val h)

def fromProtoField {α} (c : Codec α) [FromProtoField α] (k : Nat) (fs : List (Nat × Proto.WireVal)) :
    Except String (Field c.valid) :=
  c.validateField s!"field {k}" (FromProtoField.decodeProtoField k fs)

theorem fromProtoField_of_field {α : Type} (c : Codec α) [FromProtoField α]
    (k : Nat) (fs : List (Nat × Proto.WireVal)) (f : Field c.valid)
    (h : FromProtoField.decodeProtoField k fs = .ok f.val) :
    c.fromProtoField k fs = .ok f :=
  c.validateField_ok s!"field {k}" f _ h

private def toInt? (s : String) : Option Int :=
  match s.toList with
  | '-' :: ds => (String.ofList ds).toNat?.map fun n => -(Int.ofNat n)
  | _         => s.toNat?.map Int.ofNat

private theorem attr_valid_kv {msg : Type} (k v : String)
    (hs : isSafeAttrName k = true) (hu : isUrlAttrName k = false) :
    Attr.valid (msg := msg) (.attr k v) = true := by
  simp only [Attr.valid, Attr.validKeyValue, hs, hu, Bool.not_false, Bool.true_or, Bool.and_self]

private theorem attr_valid_flag {msg : Type} (k : String) (b : Bool)
    (hs : isSafeAttrName k = true) : Attr.valid (msg := msg) (.flag k b) = true := hs

private theorem attr_valid_on {msg : Type} (k : String) (m : msg)
    (hs : isSafeAttrName k = true) : Attr.valid (.on k m) = true := hs

private theorem attr_valid_onVal {msg : Type} (k : String) (f : String → msg)
    (hs : isSafeAttrName k = true) : Attr.valid (.onValue k f) = true := hs

private theorem validIn_el {msg : Type} {ctx next : HtmlCtx} {tag : String}
    {attrs : List (Attr msg)} {kids : List (Html msg)}
    (hstep : stepHtmlCtx ctx tag = some next)
    (hvoid : isVoidTag tag = false ∨ kids = [])
    (hv : Attr.validList attrs = true)
    (hl : Attr.hasLocalCell attrs = false := by rfl)
    (hk : Html.validListIn next kids = true := by rfl) :
    Html.validIn ctx (el tag attrs kids) = true := by
  rcases hvoid with hnv | rfl
  · simp only [el, Html.validIn, hstep, hnv, hv, hl, hk, Bool.not_false, Bool.true_or, Bool.and_self]
  · simp only [el, Html.validIn, hstep, hv, hl, hk, List.isEmpty_nil, Bool.not_false, Bool.or_true, Bool.and_self]

local macro "solve_attrs" : tactic =>
  `(tactic| (dsimp only [Attr.validList, value, type', Qed.name, attr, checked, disabled, cls, onInput, onChange, onCheck, onClick]; simp only [Bool.and_eq_true]; repeat any_goals constructor) <;>
    first
    | exact attr_valid_kv _ _ rfl rfl
    | exact attr_valid_flag _ _ rfl
    | exact attr_valid_on _ _ rfl
    | exact attr_valid_onVal _ _ rfl
    | rfl)

private abbrev mkSimpleCodec {α : Type} (parse : String → Option α)
    (render : {msg : Type} → String → (String → msg) → Html msg)
    (render_valid : ∀ {msg : Type} (inForm : Bool) (raw : String) (set : String → msg),
      Html.validIn ⟨.normal, false, false, inForm⟩ (render raw set) = true)
    (inForm : Bool := true) (wrapLabel : Bool := true) : Codec α :=
  { parse, render, valid := fun _ => True, dec := fun _ => inferInstance, inForm, wrapLabel, render_valid }

private abbrev mkInputCodec {α : Type} (parse : String → Option α)
    (attrs : {msg : Type} → String → (String → msg) → List (Attr msg))
    (hv : ∀ {msg : Type} (raw : String) (set : String → msg), Attr.validList (attrs raw set) = true)
    (hl : ∀ {msg : Type} (raw : String) (set : String → msg), Attr.hasLocalCell (attrs raw set) = false := by intros; rfl) :
    Codec α :=
  mkSimpleCodec parse (fun raw set => el "input" (attrs raw set))
    (fun inForm raw set => by cases inForm <;> exact validIn_el rfl (.inr rfl) (hv raw set) (hl raw set))

def text : Codec String :=
  mkInputCodec some (fun raw set => [value raw, onInput set]) (fun _ _ => by solve_attrs)

def textarea : Codec String :=
  mkSimpleCodec some (fun raw set => el "textarea" [value raw, onInput set])
    (fun inForm _ _ => by cases inForm <;> exact validIn_el rfl (.inl rfl) (by solve_attrs))

def nat : Codec Nat :=
  mkInputCodec String.toNat? (fun raw set => [type' "number", attr "min" "0", value raw, onInput set]) (fun _ _ => by solve_attrs)

def int : Codec Int :=
  mkInputCodec toInt? (fun raw set => [type' "number", value raw, onInput set]) (fun _ _ => by solve_attrs)

def checkbox : Codec Bool :=
  mkInputCodec (fun s => some (s == "true"))
    (fun raw set => [type' "checkbox", checked (raw == "true"), onCheck (fun b => set (toString b))])
    (fun _ _ => by solve_attrs)

def date : Codec Date :=
  mkInputCodec Date.parse? (fun raw set => [type' "date", value raw, onInput set]) (fun _ _ => by solve_attrs)

def select (options : List (String × String)) : Codec String :=
  mkSimpleCodec (fun s => if options.any (fun o => o.1 == s) then some s else none)
    (fun raw set => el "select" [value raw, onChange set] (options.map fun (v, lbl) => el "option" [value v] [lbl]))
    (fun inForm _ _ => by
      cases inForm <;> exact validIn_el rfl (.inl rfl) (by solve_attrs) rfl (by
        rw [Html.validListIn_map, List.all_eq_true]; intro p _
        exact validIn_el (next := ⟨.option, false, true, _⟩) rfl (.inl rfl) (by solve_attrs)))

def radios (group : String) (options : List (String × String)) : Codec String :=
  mkSimpleCodec (fun s => if options.any (fun o => o.1 == s) then some s else none)
    (fun raw set => el "div" [cls "qed-radios"]
      (options.map fun (v, lbl) =>
        el "label" [] [el "input" [type' "radio", Qed.name group, value v, checked (raw == v), onChange set], lbl]))
    (fun inForm _ _ => by
      cases inForm <;> exact validIn_el (next := ⟨.normal, false, false, _⟩) rfl (.inl rfl) rfl rfl (by
        rw [Html.validListIn_map, List.all_eq_true]; intro p _
        exact validIn_el (next := ⟨.normal, false, false, _⟩) rfl (.inl rfl) rfl rfl (by
          simp only [Html.validListIn, Bool.and_true, Bool.and_eq_true]
          exact ⟨validIn_el rfl (.inr rfl) (by solve_attrs), rfl⟩)))
    (wrapLabel := false)

def json (α : Type) [ToJson α] [FromJson α] : Codec α :=
  mkSimpleCodec (fun _ => none) (fun _ _ => el "span" [] [])
    (fun inForm _ _ => by cases inForm <;> exact validIn_el rfl (.inl rfl) rfl)
    (inForm := false)

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
  cases inForm with
  | false => rfl
  | true =>
    cases wrapLabel <;> cases bad <;> cases ctxInForm
    all_goals
      dsimp only [formFieldRow]
      simp only [Bool.false_eq_true, ite_true, ite_false, List.cons_append, List.nil_append,
        Html.validListIn, Bool.and_true]
      refine validIn_el (next := ⟨.normal, false, false, _⟩) rfl (.inl rfl) (by solve_attrs) rfl ?_
      simp only [Html.validListIn, Bool.and_true, Bool.and_eq_true]
      repeat any_goals constructor
      all_goals first | exact hctrl | exact validIn_el rfl (.inl rfl) rfl rfl rfl

theorem formDiv_validIn {msg : Type} (inForm : Bool) (kids : List (Html msg))
    (hk : Html.validListIn ⟨.normal, false, false, inForm⟩ kids = true) :
    Html.validIn ⟨.normal, false, false, inForm⟩ (el "div" [cls "qed-form"] kids) = true := by
  cases inForm <;> exact validIn_el rfl (.inl rfl) rfl rfl hk

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
  cases o <;> cases inForm
  all_goals
    simp only [submitBtn, Html.validListIn, Bool.and_true]
    exact validIn_el rfl (.inl rfl) (by solve_attrs) rfl rfl

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
def schemaExampleFieldP : Parser := node `Qed.schemaExampleField
  (checkColGt >> ident >> "=" >> categoryParser `qedExpr 0)
def schemaExampleP : Parser := node `Qed.schemaExample (withPosition
  (atomic (symbol "example" >> ident >> ":") >> sepBy1 schemaExampleFieldP ","))
def schemaItemP : Parser := schemaExampleP <|> schemaFieldP
@[command_parser] def schemaCmd : Parser := leading_parser withPosition
  ("schema " >> ident >> optional (checkLineEq >> "(" >> sepBy1 schemaCtxParamP "," >> ")") >> ":" >>
    checkColGt "expected indented `schema` fields" >> many1Indent schemaItemP)
end SchemaParsers

open Lean in
private def lowerSchemaFieldSpec (stx : Syntax) : MacroM Term := do
  let k := stx.getKind
  if k == `Qed.schemaFieldJsonOnly then
    let (innerTy, _) ← Qed.Lang.lowerQedType (stx.getArg 2) false
    `(jsonOnly $innerTy)
  else if k == `Qed.schemaFieldCall then
    let argTs ← (stx.getArg 2).getSepArgs.mapM fun a => Qed.Lang.lowerSimpleQedExpr .val (a.getArg 0)
    Qed.Lang.mkAppTerms ⟨(stx.getArg 0)⟩ argTs
  else
    return (← Qed.Lang.lowerQedType stx false).1

private def primSchemaTypes : Array (Lean.Name × Lean.Name × String) := #[
  (``String,   ``Qed.Codec.text,     "String"),
  (``Nat,      ``Qed.Codec.nat,      "Nat"),
  (``Int,      ``Qed.Codec.int,      "Int"),
  (``Bool,     ``Qed.Codec.checkbox, "Bool"),
  (``Qed.Date, ``Qed.Codec.date,     "Date")
]

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
    if let some (_, codecNm, _) := primSchemaTypes.find? fun (tyNm, _, _) => eWhnf.isConstOf tyNm then
      return mkCIdent codecNm
    else
      if (← trySynthInstance (← mkAppM ``Qed.DefaultCodec #[e])) matches .some _ then
        return ← `((Qed.DefaultCodec.codec : Qed.Codec $rawSpec))
      else
        throwErrorAt rawSpec m!"schema field `{fieldName}` has type `{rawSpec}`, which has no default `Codec` or JSON (`ToJson`/`FromJson`) instances.\nProvide a `DefaultCodec` or JSON instances for `{rawSpec}`, or use a supported field type (`String`, `Nat`, `Int`, `Bool`, `Date`, `select([...])`, `textarea`, `jsonOnly(...)`)."
  else
    throwErrorAt rawSpec m!"schema field `{fieldName}` must be a type (`String`, `Nat`, `Int`, `Bool`, `Date`, …) \
      or a `Codec` (e.g. `select([...])`, `textarea`, `jsonOnly(String)`), but this has \
      type{indentExpr ety}"

private structure ResolvedSchemaField where
  input       : Lean.Term
  isRefined   : Bool
  isLawful    : Bool
  isProto     : Bool
  isLawfulP   : Bool
  isLawfulBEq : Bool
  tyKind      : String
  hasInhab    : Bool
deriving Inhabited

open Lean Elab Term Meta in
private partial def withCtxDecls {α : Type} (cbns : Array Ident) (cbts : Array Term)
    (k : TermElabM α) (i : Nat := 0) : TermElabM α := do
  if i < cbns.size then
    let bt ← elabType cbts[i]!
    withLocalDeclD cbns[i]!.getId bt fun _ => withCtxDecls cbns cbts k (i + 1)
  else k

open Lean Elab Term Meta in
private def elabSchemaFieldsAux (cbns : Array Ident) (cbts : Array Term)
    (fs : Array Ident) (rawSpecs : Array Term) (whereClauses : Array (Array Term)) :
    TermElabM (Array ResolvedSchemaField) :=
  withCtxDecls cbns cbts do
    ((fs.zip rawSpecs).zip whereClauses).mapM fun ((f, rawSpec), preds) => do
      let base ← resolveCodecBase f.getId rawSpec
      let inp : Term ←
        if preds.isEmpty then pure base
        else `(Qed.Codec.refine $base (fun $f:ident => $(← mkConjBody preds)))
      let c ← elabTermAndSynthesize inp none
      let cty ← instantiateMVars (← inferType c)
      match cty.getAppFnArgs with
      | (``Qed.Codec, #[α]) =>
          let validExpr := mkApp2 (mkConst ``Qed.Codec.valid) α c
          let trueFn := Expr.lam `x α (mkConst ``True) BinderInfo.default
          let isRefined := !(← isDefEq validExpr trueFn)
          let hasInst (cls : Name) (lvls : List Level := []) : MetaM Bool := do
            return (← trySynthInstance (mkApp (mkConst cls lvls) α)) matches .some _
          let isLawful ← hasInst ``Qed.LawfulJson
          let isProto := (← hasInst ``Qed.ToProtoField) && (← hasInst ``Qed.FromProtoField)
          let isLawfulP ← hasInst ``Qed.LawfulProtoField
          let isLawfulBEq ← match ← trySynthInstance (mkApp (mkConst ``BEq [Level.zero]) α) with
            | .some beqInst => pure ((← trySynthInstance (mkApp2 (mkConst ``LawfulBEq [Level.zero]) α beqInst)) matches .some _)
            | _ => pure false
          let hasInhab ← hasInst ``Inhabited [Level.zero]
          let αw ← whnf α
          let tyKind := (primSchemaTypes.find? fun (tyNm, _, _) => αw.isConstOf tyNm).map (·.2.2) |>.getD "Other"
          return { input := inp, isRefined, isLawful, isProto, isLawfulP, isLawfulBEq, tyKind, hasInhab }
      | _ =>
          throwErrorAt rawSpec m!"failed to resolve schema field `{f.getId}` to a `Codec`"

open Lean Elab Command Term in
private def checkSchemaFieldsDecidable (cbns : Array Ident) (cbts : Array Term)
    (pairs : Array (Ident × Term)) (refined : Array Bool) : CommandElabM Unit := do
  -- Lean logs failed instance synthesis to `messages` rather than throwing; probe in isolation to catch missing `DecidablePred` cleanly.
  for ((f, inp), r) in pairs.zip refined do
    unless r do continue
    let (_, probeMsgs) ← Qed.Diag.probeTermElabMsgs (withCtxDecls cbns cbts (discard <| elabTermAndSynthesize inp none))
    if ← probeMsgs.anyM fun msg => return ((← msg.data.toString).splitOn "DecidablePred").length > 1 then
      throwErrorAt inp m!"schema field `{f.getId}` has a refinement that isn't decidable, so \
        validity can't be computed (no `DecidablePred` for it).\n\nThe usual cause is a \
        predicate written with `def`. Write it inline with `where …` or as an `abbrev`, so Lean \
        sees it reduces to a decidable check:\n    abbrev MyPredicate (x : …) : Prop := …\n\
        If it genuinely can't be decided, give it a `DecidablePred` instance."

open Lean Elab Command Term in
private def mkDraftCmds (tId : Name) (draftId : Ident) (fs : Array Ident) :
    CommandElabM (TSyntax `command × Array (TSyntax `command)) := do
  let emptyId := mkIdent (tId ++ `Draft ++ `empty)
  let emptyVals ← fs.mapM fun _ => `(term| "")
  let structCmd ← `(command| structure $draftId where
          $[$fs:ident : String := ""]*
        deriving Inhabited, DecidableEq, Repr)
  let emptyCmd ← `(command| def $emptyId : $draftId := { $[$fs:ident := $emptyVals],* })
  let draftFields ← fs.mapM fun f =>
    return ({ ident := f, wireKey := f.getId.toString, valTy := ← `(String) } : StructFieldSpec)
  let jsonCmds ← mkStructJsonCmds draftId draftFields { fixedDepthBound := some 1 }
  pure (structCmd, #[emptyCmd] ++ jsonCmds)

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
  let rhs ← mkConjBody isSomes (ascribeProp := false)
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

private partial def collectStxLits {α : Type} [BEq α] (extract : Lean.Syntax → Option α)
    (stx : Lean.Syntax) (acc : Array α) : Array α :=
  let acc := match extract stx with
    | some v => if acc.contains v then acc else acc.push v
    | none   => acc
  stx.getArgs.foldl (fun a ch => collectStxLits extract ch a) acc

open Lean Elab Command Term Meta in
private def tryCheckPropWithTactic (goalTerm : Term) (tacStx : TSyntax `tactic) : CommandElabM Bool :=
  Qed.Diag.probeTermElabOk do
    let _ ← elabTermEnsuringType (← `(by $tacStx:tactic)) (← elabType goalTerm)
    synthesizeSyntheticMVarsNoPostponing
    return true

open Lean Elab Command Term Meta in
private def schemaCodecSimp : CommandElabM (TSyntax `tactic) :=
  `(tactic| simp only [Qed.Codec.valid, Qed.Codec.refine, Qed.Codec.jsonOnly,
      Qed.Codec.text, Qed.Codec.textarea, Qed.Codec.nat, Qed.Codec.int,
      Qed.Codec.checkbox, Qed.Codec.date, Qed.Codec.select, Qed.Codec.radios,
      Qed.Codec.json, Qed.Lang.QedVal.val_id])

open Lean Elab Command Term Meta in
private def mkSchemaWhereProofTac : CommandElabM (TSyntax `tactic) := do
  let simpTac ← schemaCodecSimp
  `(tactic| ($simpTac:tactic <;> first | rfl | decide | omega | trivial | (simp_all; try rfl; try decide; try omega)))

open Lean Elab Command Term Meta in
private def isFieldProvablyUnsat (inp : Term) : CommandElabM Bool := do
  let simpTac ← schemaCodecSimp
  let unsatGoal ← `(∀ _qed_x : Qed.Codec.Val $inp, ¬ ($inp).valid _qed_x)
  let unsatTac ← `(tactic| (intro _qed_x; $simpTac:tactic; first | omega | decide | (cases _qed_x <;> decide)))
  tryCheckPropWithTactic unsatGoal unsatTac

open Lean Elab Command Term Meta in
private def synthesizeFieldWitness? (rf : ResolvedSchemaField) (rawWheres : Array Syntax) :
    CommandElabM (Option Term) := do
  let inp := rf.input
  if !rf.isRefined then
    if rf.hasInhab then return some (← `((default : Qed.Codec.Val $inp))) else return none
  let natLits := rawWheres.foldl (fun acc w =>
    collectStxLits (fun s => if s.getKind == ``Qed.Lang.qedLitNum then some (⟨s.getArg 0⟩ : TSyntax `num).getNat else none) w acc) #[]
  let strLits := rawWheres.foldl (fun acc w =>
    collectStxLits (fun s => if s.getKind == ``Qed.Lang.qedLitStr then some (⟨s.getArg 0⟩ : TSyntax `str).getString else none) w acc) #[]
  let cands : Array Term ← match rf.tyKind with
    | "Bool" => pure #[← `((Bool.true : Bool)), ← `((Bool.false : Bool))]
    | "Nat"  =>
        let ns := ((natLits.toList.flatMap fun n => [n, n + 1, n - 1]) ++ [0, 1, 2, 3, 5, 10, 18, 21, 50, 100]).eraseDups
        ns.toArray.mapM fun k => `(($(Syntax.mkNumLit (toString k)) : Nat))
    | "Int"  =>
        let zs := ((natLits.toList.flatMap fun n => let z : Int := Int.ofNat n; [z, z + 1, z - 1, -z, -z - 1, -z + 1]) ++
                   [(0 : Int), 1, -1, 2, 10, 100]).eraseDups
        zs.toArray.mapM fun k =>
          if k >= 0 then `(($(Syntax.mkNumLit (toString k.toNat)) : Int))
          else `((-($(Syntax.mkNumLit (toString (-k).toNat)) : Int)))
    | "String" =>
        let lenStrs := natLits.toList.flatMap fun n =>
          (if n > 0 && n ≤ 64 then [String.ofList (List.replicate n 'a')] else []) ++
          (if n + 1 ≤ 64 then [String.ofList (List.replicate (n + 1) 'a')] else [])
        let ss := (strLits.toList ++ ["", "a", "alice", "a@b.com", "https://example.com", "12345678", "aaaaaaaaaa"] ++ lenStrs).eraseDups
        ss.toArray.mapM fun s => `(($(Syntax.mkStrLit s) : String))
    | "Date" => pure #[← `(({ year := 2026, month := 1, day := 1 } : Qed.Date))]
    | _      => if rf.hasInhab then do pure #[← `((default : Qed.Codec.Val $inp))] else pure #[]
  let pfTac ← mkSchemaWhereProofTac
  for cand in cands do
    if ← tryCheckPropWithTactic (← `(($inp).valid $cand)) pfTac then
      return some (← `(Qed.Field.mk (p := ($inp).valid) $cand (by $pfTac:tactic)))
  return none

open Lean Elab Command Term in
private def emitSatisfiableCmds (ref : Syntax) (t : Ident) (cbns : Array Ident) (cbts : Array Term)
    (tApp witness : Term) : CommandElabM Unit := do
  let tId := t.getId
  let satId := mkIdentFrom ref (tId ++ `satisfiable)
  elabCommand (← `(command|
    theorem $satId $[($cbns:ident : $cbts:term)]* : ∃ _x : $tApp, True := ⟨$witness, trivial⟩))
  if cbns.isEmpty then
    let nonEmptyId := mkIdentFrom ref (tId ++ `instNonempty)
    elabCommand (← `(command| instance $nonEmptyId:ident : Nonempty $t := ⟨$witness⟩))

open Lean Elab Command Term Meta in
private def elabSchemaExampleClause (t : Ident) (cbns : Array Ident) (cbts : Array Term)
    (tApp : TSyntax `term) (appTo : TSyntax `term → CommandElabM (TSyntax `term))
    (fs : Array Ident) (inputs : Array Term) (refined : Array Bool)
    (whereLabels : Array String) (exStx : Syntax) (emitSatisfiable : Bool) : CommandElabM Unit := do
  let tId := t.getId
  let exName : Ident := ⟨exStx.getArg 1⟩
  let exId := exName.getId
  let validNames := fs.toList.map (·.getId.toString)
  let rawEntries := (exStx.getArg 3).getSepArgs
  let mut provided : Std.HashMap String (Syntax × Syntax) := {}
  for entry in rawEntries do
    let fid : Ident := ⟨entry.getArg 0⟩
    let fName := fid.getId.toString
    unless validNames.contains fName do
      let hint := Qed.Diag.didYouMean fName validNames
      throwErrorAt fid s!"Schema `{tId}` example `{exId}`: unknown field `{fName}`{hint} (expected: {String.intercalate ", " validNames})"
    if provided.contains fName then
      throwErrorAt fid s!"Schema `{tId}` example `{exId}`: duplicate field `{fName}`"
    provided := provided.insert fName (fid.raw, entry.getArg 2)
  for f in fs do
    let fName := f.getId.toString
    unless provided.contains fName do
      throwErrorAt exStx s!"Schema `{tId}` example `{exId}`: missing required field `{fName}`"
  let pfTac ← mkSchemaWhereProofTac
  let mut fieldTerms : Array Term := #[]
  for i in [0:fs.size] do
    let f := fs[i]!
    let fName := f.getId.toString
    let (_, valStx) := provided[fName]!
    let valTerm ← liftMacroM (Qed.Lang.lowerSimpleQedExpr .val valStx)
    if refined[i]! then
      if cbns.isEmpty then
        let goal ← `(($(inputs[i]!)).valid $valTerm)
        unless ← tryCheckPropWithTactic goal pfTac do
          let valStr := (valStx.unsetTrailing.reprint.getD "<value>").trimAscii.toString
          let ruleStr := whereLabels[i]!
          throwErrorAt valStx m!"Schema `{tId}` example `{exId}` failed `where` constraint on field `{fName}`:\n  • value `{valStr}` does not satisfy `{ruleStr}`\n\nHint: Update `{fName}` in example `{exId}` so it satisfies `{ruleStr}`, or weaken the `where` rule."
      fieldTerms := fieldTerms.push (← `(Qed.Field.mk (p := ($(inputs[i]!)).valid) $valTerm (by $pfTac:tactic)))
    else
      fieldTerms := fieldTerms.push valTerm
  let sampleId := mkIdentFrom exName (tId ++ exId)
  let sampleApp ← appTo ⟨sampleId.raw⟩
  elabCommand (← `(command|
    def $sampleId $[($cbns:ident : $cbts:term)]* : $tApp := { $[$fs:ident := $fieldTerms:term],* }))
  if emitSatisfiable then
    emitSatisfiableCmds exStx t cbns cbts tApp sampleApp

open Lean Elab Command Term Meta in
private def elabSchemaAutoSatisfiability (t : Ident) (cbns : Array Ident)
    (fs : Array Ident) (resolved : Array ResolvedSchemaField)
    (whereRawExprs : Array (Array Syntax)) (whereLabels : Array String) : CommandElabM Unit := do
  let tId := t.getId
  if !cbns.isEmpty then return
  for i in [0:fs.size] do
    if resolved[i]!.isRefined then
      if ← isFieldProvablyUnsat resolved[i]!.input then
        let f := fs[i]!
        throwErrorAt f m!"Schema `{tId}` is unsatisfiable: field `{f.getId}` has contradictory `where` constraints (`{whereLabels[i]!}`) — no value can ever satisfy it.\n\nHint: Fix or remove the conflicting `where` conditions on `{f.getId}`."
  let mut synthTerms : Array Term := #[]
  for i in [0:fs.size] do
    match ← synthesizeFieldWitness? resolved[i]! whereRawExprs[i]! with
    | some ft => synthTerms := synthTerms.push ft
    | none    => return
  emitSatisfiableCmds t t #[] #[] ⟨t.raw⟩ (← `({ $[$fs:ident := $synthTerms:term],* }))

open Lean Elab Command Term in
@[command_elab schemaCmd] def elabSchemaCmd : CommandElab
  | stx => do
      let t : Ident := ⟨(stx.getArg 1)⟩
      let rawCtx := if (stx.getArg 2).getNumArgs == 3 then ((stx.getArg 2).getArg 1).getSepArgs else #[]
      let cbns : Array Ident := rawCtx.map (⟨·.getArg 0⟩)
      let cbts ← rawCtx.mapM fun cp => liftMacroM (return (← Qed.Lang.lowerQedType (cp.getArg 2) false).1)
      let itemStxs := (stx.getArg 4).getArgs
      let mut fStxs : Array Syntax := #[]
      let mut exampleStxs : Array Syntax := #[]
      let mut seenExNames : Std.HashSet Name := {}
      for item in itemStxs do
        let k := item.getKind
        if k == `Qed.schemaExample then
          let exName : Ident := ⟨item.getArg 1⟩
          if seenExNames.contains exName.getId then
            throwErrorAt exName s!"duplicate example `{exName.getId}` in `schema {t.getId}`"
          seenExNames := seenExNames.insert exName.getId
          exampleStxs := exampleStxs.push item
        else
          fStxs := fStxs.push item
      if fStxs.isEmpty then
        throwErrorAt t s!"`schema {t.getId}` must declare at least one field"
      let fs : Array Ident := fStxs.map (⟨·[0]⟩)
      let rawSpecs ← fStxs.mapM fun f => liftMacroM (lowerSchemaFieldSpec (f.getArg 2))
      let whereRawExprs : Array (Array Syntax) := fStxs.map fun f =>
        if (f.getArg 3).getNumArgs == 2 then ((f.getArg 3).getArg 1).getSepArgs else #[]
      let whereLabels : Array String := whereRawExprs.map fun ws =>
        String.intercalate ", " (ws.toList.map fun w =>
          (((w.reprint.getD "constraint").splitOn "\n").headD "constraint").trimAscii.toString)
      let whereClauses : Array (Array Term) ← whereRawExprs.mapM fun ws =>
        ws.mapM fun w => liftMacroM (Qed.Lang.lowerSimpleQedExpr .propInv w)
      let tId     := t.getId
      let draftId := mkIdent (tId ++ `Draft)
      let beqFnId := mkIdent (tId ++ `beq)
      let parseId := mkIdent (tId ++ `parse)
      let canId   := mkIdent (tId ++ `canSubmit)
      let viewId  := mkIdent (tId ++ `formView)
      let resolved ← liftTermElabM (elabSchemaFieldsAux cbns cbts fs rawSpecs whereClauses)
      let inputs := resolved.map (·.input)
      let refined := resolved.map (·.isRefined)
      let allLawful := resolved.all (·.isLawful)
      let allProto := resolved.all (·.isProto)
      let allLawfulProto := resolved.all (·.isLawfulP)
      let allLawfulBEq := resolved.all (·.isLawfulBEq)
      let pairs := fs.zip inputs
      checkSchemaFieldsDecidable cbns cbts pairs refined
      let appTo (head : TSyntax `term) : CommandElabM (TSyntax `term) :=
        Qed.Lang.mkAppTerms head (cbns.map (⟨·.raw⟩))
      let tApp     ← appTo ⟨t.raw⟩
      let beqApp   ← appTo ⟨beqFnId.raw⟩
      let parseApp ← appTo ⟨parseId.raw⟩
      let canApp   ← appTo ⟨canId.raw⟩
      let viewApp  ← appTo ⟨viewId.raw⟩
      let (draftStructCmd, draftCmds) ← mkDraftCmds tId draftId fs
      let (coreStructCmd, coreCmds) ← mkSchemaCoreCmds t cbns cbts tApp beqApp parseApp canApp viewApp draftId fs inputs refined allLawfulBEq
      let schemaFields ← (pairs.zip refined).mapM fun ((f, inp), r) =>
        return ({ ident := f, wireKey := f.getId.toString, valTy := ← `(Codec.Val $inp),
                  isRefinedField := r, codecTerm? := if r then some inp else none } : StructFieldSpec)
      let ctxBinders := cbns.zip cbts
      let jsonCmds ← mkStructJsonCmds t schemaFields
        { ctxBinders, emitStringCodec := true, emitLawful := allLawful }
      let protoCmds ← if allProto then
          mkStructProtoCmds t schemaFields { ctxBinders, emitBytesCodec := true, emitLawful := allLawfulProto }
        else pure #[]
      for c in #[draftStructCmd, coreStructCmd] ++ draftCmds ++ coreCmds ++ jsonCmds ++ protoCmds do
        elabCommand c
      if exampleStxs.isEmpty then
        elabSchemaAutoSatisfiability t cbns fs resolved whereRawExprs whereLabels
      else
        for idx in [0:exampleStxs.size] do
          elabSchemaExampleClause t cbns cbts tApp appTo fs inputs refined whereLabels exampleStxs[idx]! (idx == 0)
      let ns ← getCurrNamespace
      let fullSchema := ns ++ tId
      let info : SchemaFormInfo := {
        fullName := fullSchema ++ `Form
        formViewName := fullSchema ++ `formView
        ctxBinders := cbns.map (·.getId.eraseMacroScopes)
      }
      modifyEnv fun env => schemaFormRegistry.addEntry env info

end Qed
