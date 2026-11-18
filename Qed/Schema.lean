import Qed.Notation
import Qed.Json
import Qed.Proto
import Qed.Date
import Qed.Runtime.Verify
import Lean

namespace Qed

structure Field {α : Type} (p : α → Prop) where
  val : α
  ok  : p val

@[reducible, inline] instance {α : Type} {p : α → Prop} : Qed.Lang.QedVal (Field p) α := ⟨Field.val⟩
@[simp] theorem QedVal.val_field {α : Type} {p : α → Prop} (f : Field p) :
    Qed.Lang.QedVal.val f = f.val := rfl

@[reducible] instance {msg : Type} : Coe Date (Html msg) := ⟨fun d => .text (toString d)⟩
@[reducible] instance {α : Type} {p : α → Prop} : CoeOut (Field p) α := ⟨Field.val⟩
@[reducible] instance {α msg : Type} {p : α → Prop} [Coe α (Html msg)] : CoeHTCT (Field p) (Html msg) := ⟨fun f => (f.val : Html msg)⟩
@[reducible] instance {α : Type} {p : α → Prop} : CoeHTCT (Option (Field p)) (Option α) := ⟨Option.map Field.val⟩
instance {α : Type} {p : α → Prop} [ToString α] : ToString (Field p) := ⟨fun f => toString f.val⟩
instance {α : Type} {p : α → Prop} [BEq α] : BEq (Field p) := ⟨fun a b => a.val == b.val⟩
instance {α : Type} {p : α → Prop} [DecidableEq α] : DecidableEq (Field p) :=
  fun ⟨a, _⟩ ⟨b, _⟩ => if h : a = b then isTrue (by cases h; rfl) else isFalse (by intro heq; injection heq; exact h ‹_›)

instance {α : Type} {p : α → Prop} [ToJson α] : ToJson (Field p) := ⟨fun f => toJson f.val⟩
instance {α : Type} {p : α → Prop} [DecidablePred p] [FromJson α] : FromJson (Field p) :=
  ⟨fun j => do let a ← (fromJson j : Except String α); if h : p a then .ok ⟨a, h⟩ else .error "failed field refinement"⟩
instance {α : Type} {p : α → Prop} [DecidablePred p] [LawfulJson α] : LawfulJson (Field p) where
  depthBound := LawfulJson.depthBound α
  depth_toJson f := LawfulJson.depth_toJson f.val
  fromJson_toJson f := by
    rcases f with ⟨val, hok⟩
    change (fromJson (toJson val) : Except String α).bind
      (fun a => if h : p a then Except.ok (Field.mk a h) else Except.error _) = Except.ok (Field.mk val hok)
    rw [LawfulJson.fromJson_toJson val]; dsimp only [bind, Except.bind]; rw [dif_pos hok]
instance {α : Type} {p : α → Prop} [ToJson α] [NonNullJson α] : NonNullJson (Field p) :=
  ⟨fun f => NonNullJson.toJson_ne_null f.val⟩

instance {α : Type} {p : α → Prop} [ToProto α] : ToProto (Field p) where
  toProtoVal f := ToProto.toProtoVal f.val

instance {α : Type} {p : α → Prop} [DecidablePred p] [FromProto α] : FromProto (Field p) where
  fromProtoVal w := do
    let a ← FromProto.fromProtoVal (α := α) w
    if h : p a then .ok ⟨a, h⟩ else .error "protobuf: failed field refinement"

instance {α : Type} {p : α → Prop} [DecidablePred p] [LawfulProto α] : LawfulProto (Field p) :=
  .ofScalar fun ⟨val, hok⟩ => by
    dsimp only [ToProto.toProtoVal, FromProto.fromProtoVal, bind, Except.bind]
    rw [LawfulProto.fromProtoVal_toProtoVal val]
    dsimp only
    rw [dif_pos hok]

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

def text : Codec String where
  parse := some; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [value raw, onInput set]
  render_valid := fun inForm _ _ => by cases inForm <;> rfl

def textarea : Codec String where
  parse := some; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "textarea" [value raw, onInput set]
  render_valid := fun inForm _ _ => by cases inForm <;> rfl

def nat : Codec Nat where
  parse := fun s => s.toNat?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [type' "number", attr "min" "0", value raw, onInput set]
  render_valid := fun inForm _ _ => by cases inForm <;> rfl

def int : Codec Int where
  parse := toInt?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [type' "number", value raw, onInput set]
  render_valid := fun inForm _ _ => by cases inForm <;> rfl

def checkbox : Codec Bool where
  parse := fun s => some (s == "true"); valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set =>
    el "input" [type' "checkbox", checked (raw == "true"), onCheck (fun b => set (toString b))]
  render_valid := fun inForm _ _ => by cases inForm <;> rfl

def date : Codec Date where
  parse := Date.parse?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [type' "date", value raw, onInput set]
  render_valid := fun inForm _ _ => by cases inForm <;> rfl

def select (options : List (String × String)) : Codec String where
  parse := fun s => if options.any (fun o => o.1 == s) then some s else none
  valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set =>
    el "select" [value raw, onChange set]
      (options.map fun (v, lbl) => el "option" [value v] [lbl])
  render_valid := fun {msg} inForm raw set => by
    cases inForm <;>
      simp [el, value, onChange, Html.validIn, Attr.valid, Attr.validKeyValue, Html.validListIn_map]

def radios (group : String) (options : List (String × String)) : Codec String where
  parse := fun s => if options.any (fun o => o.1 == s) then some s else none
  valid := fun _ => True; dec := fun _ => inferInstance
  wrapLabel := false
  render := fun raw set =>
    el "div" [cls "qed-radios"]
      (options.map fun (v, lbl) =>
        el "label" [] [el "input" [type' "radio", Qed.name group, value v, checked (raw == v), onChange set], lbl])
  render_valid := fun {msg} inForm raw set => by
    cases inForm <;>
      simp [el, cls, type', Qed.name, value, checked, onChange,
            Html.validIn, Attr.valid, Attr.validKeyValue, Html.validListIn_map]

def json (α : Type) [ToJson α] [FromJson α] : Codec α where
  parse := fun _ => none
  valid := fun _ => True; dec := fun _ => inferInstance
  render := fun _ _ => el "span" [] []
  inForm := false
  render_valid := fun inForm _ _ => by cases inForm <;> rfl

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
  cases ctxInForm <;> cases inForm <;> cases wrapLabel <;> cases bad <;>
    simp [formFieldRow, el, cls, attr, Html.validListIn, Html.validIn, Attr.valid, Attr.validKeyValue, hctrl]

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
    let (innerTy, _) ← Qed.Lang.lowerQedType stx[2] false
    `(jsonOnly $innerTy)
  else if k == `Qed.schemaFieldCall then
    let callee : Term := ⟨stx[0]⟩
    let args := stx[2].getSepArgs
    args.foldlM (init := callee) fun acc a => do
      let aT ← Qed.Lang.lowerSimpleQedExpr .val a[0]
      `($acc $aT)
  else
    return (← Qed.Lang.lowerQedType stx false).1

open Lean Elab Term Meta in
private partial def resolveCodecBase (rawSpec : Term) : TermElabM Term := do
  match rawSpec with
  | `($fn:ident $arg:term) =>
      if fn.getId.eraseMacroScopes == `jsonOnly then
        let inner ← resolveCodecBase arg
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
        throwErrorAt rawSpec m!"schema field type `{rawSpec}` has no default `Codec` or JSON instances"
  else
    throwErrorAt rawSpec m!"a schema field must be a type (`String`, `Nat`, `Bool`, `Date`, …) \
      or a `Codec` (e.g. `select […]`, `textarea`, `jsonOnly String`), but this has \
      type{indentExpr ety}"

open Lean Elab Term Meta in
private partial def elabSchemaFieldsAux (cbns : Array Ident) (cbts : Array Term)
    (fs : Array Ident) (rawSpecs : Array Term) (whereClauses : Array (Array Term)) (i : Nat) :
    TermElabM (Array (Term × Bool × Bool × Bool × Bool)) := do
  if i < cbns.size then
    let bt ← elabType cbts[i]!
    withLocalDeclD cbns[i]!.getId bt fun _ =>
      elabSchemaFieldsAux cbns cbts fs rawSpecs whereClauses (i + 1)
  else
    ((fs.zip rawSpecs).zip whereClauses).mapM fun ((f, rawSpec), preds) => do
      let base ← resolveCodecBase rawSpec
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
          pure (inp, isRef, isLaw, hasToP && hasFromP, isLawP)
      | _ =>
          throwErrorAt rawSpec m!"failed to resolve schema field `{f.getId}` to a `Codec`"

open Lean Elab Command in
private def resolveSchemaFields (cbns : Array Ident) (cbts : Array Term)
    (fs : Array Ident) (rawSpecs : Array Term) (whereClauses : Array (Array Term)) :
    CommandElabM (Array Term × Array Bool × Bool × Bool × Bool) := do
  let res ← liftTermElabM (elabSchemaFieldsAux cbns cbts fs rawSpecs whereClauses 0)
  return (res.map (·.1), res.map (·.2.1), res.all (·.2.2.1), res.all (·.2.2.2.1), res.all (·.2.2.2.2))

open Lean Elab Command Term Meta in
private def elabPredProbe (cbns : Array Ident) (cbts : Array Term) (inp : Term) (i : Nat) :
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
    let kLit := Syntax.mkNumLit (toString (i + 1))
    tails := tails.set! i (← `(term| ToProtoField.encodeProtoField $kLit $(reads[i]!) ++ $(tails[i + 1]!)))
    tagsPosPf ← `(term| Proto.msg_tags_pos_encodeAppend (by decide : 0 < $kLit) $(reads[i]!) $tagsPosPf)
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
      gtPf ← `(term| Proto.allTagsGt_encodeAppend (by decide : $kLit < $jLit) $(reads[j]!) $gtPf)
    let mut rawEq ← `(term| Proto.decodeProtoField_hit $kLit $(reads[i]!) $(tails[i + 1]!) $gtPf)
    for revBefore in [0:i] do
      let j := i - 1 - revBefore
      let jLit := Syntax.mkNumLit (toString (j + 1))
      rawEq ← `(term| Eq.trans (Proto.decodeProtoField_skip (α := $valTy) (by decide : $jLit ≠ $kLit) $(reads[j]!) $(tails[j + 1]!)) $rawEq)
    let fullEq ← wrapFieldEq i body rawEq
    let hId := mkIdent (Name.mkSimple s!"_hp{i}")
    pIdents := pIdents.push hId
    pHaveTacs := pHaveTacs.push (← `(tactic| have $hId:ident := $fullEq))
  return (body, tagsPosPf, pIdents, pHaveTacs)

open Lean Elab Command Term in
private def mkDraftProtoCmds (tId : Name) (draftId : Ident) (fs : Array Ident) :
    CommandElabM (Array (TSyntax `command)) := do
  let toId   := mkIdent (tId ++ `Draft ++ `toProtoFields)
  let fromId := mkIdent (tId ++ `Draft ++ `fromProtoFields)
  let reads ← fs.mapM fun f => `(term| x.$f:ident)
  let decodes ← (List.range fs.size).toArray.mapM fun i => do
    let kLit := Syntax.mkNumLit (toString (i + 1))
    `(term| (FromProtoField.decodeProtoField $kLit fs : Except String String))
  let (body, tagsPosPf, pIdents, pHaveTacs) ← mkProtoFieldSkeleton reads
    (fun _ => `(term| String)) (fun _ _ eq => pure eq)
  return #[
    ← `(command| def $toId (x : $draftId) : List (Nat × Proto.WireVal) := $body),
    ← `(command| def $fromId (fs : List (Nat × Proto.WireVal)) : Except String $draftId := do
          $[let $fs:ident ← $decodes:term]*
          return { $[$fs:ident],* }),
    ← `(command| instance $(mkIdent (tId ++ `Draft ++ `instToProto)):ident : ToProto $draftId := .ofFields $toId),
    ← `(command| instance $(mkIdent (tId ++ `Draft ++ `instFromProto)):ident : FromProto $draftId := .ofFields $fromId),
    ← `(command| instance $(mkIdent (tId ++ `Draft ++ `instLawfulProto)):ident : LawfulProto $draftId :=
          .ofFields $toId $fromId (fun x => $tagsPosPf) fun x => by
            $[$pHaveTacs:tactic]*
            unfold $fromId $toId
            simp only [$[$pIdents:term],*, bind, Except.bind, pure, Except.pure]) ]

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
  let instBase : Array (TSyntax `command) := #[
    ← `(command| instance $(mkIdent (tId ++ `instToProto)):ident : ToProto $t := .ofFields $toId),
    ← `(command| instance $(mkIdent (tId ++ `instFromProto)):ident : FromProto $t := .ofFields $fromId) ]
  if !allLawfulProto then return baseCmds ++ instBase
  let lawCmds : Array (TSyntax `command) := #[
    ← `(command| instance $(mkIdent (tId ++ `instLawfulProto)):ident : LawfulProto $t :=
          .ofFields $toId $fromId (fun x => $tagsPosPf) fun x => by
            $[$pHaveTacs:tactic]*
            unfold $fromId $toId
            simp only [$[$pIdents:term],*, bind, Except.bind, pure, Except.pure]) ]
  return baseCmds ++ instBase ++ lawCmds

open Lean Elab Command Term in
private def checkSchemaFieldsDecidable (cbns : Array Ident) (cbts : Array Term)
    (pairs : Array (Ident × Term)) : CommandElabM Unit := do
  -- Lean logs failed instance synthesis to `messages` rather than throwing; probe in isolation to catch missing `DecidablePred` cleanly.
  for (f, inp) in pairs do
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
private def mkDraftCmds (tId : Name) (draftId : Ident) (fs : Array Ident) :
    CommandElabM (Array (TSyntax `command)) := do
  let emptyId       := mkIdent (tId ++ `Draft ++ `empty)
  let draftToJsonId := mkIdent (tId ++ `Draft ++ `toJson)
  let draftFromId   := mkIdent (tId ++ `Draft ++ `fromJson)
  let emptyVals ← fs.mapM fun _ => `(term| "")
  let draftJsonPairs ← fs.mapM fun f =>
    let keyLit := Syntax.mkStrLit (toString f.getId); `(($keyLit, toJson (x.$f:ident)))
  let draftJsonDecodes ← fs.mapM fun f =>
    let keyLit := Syntax.mkStrLit (toString f.getId)
    `((FromJsonField.fromField j $keyLit : Except String String))
  let draftFieldEqs ← fs.mapM fun f =>
    let keyLit := Syntax.mkStrLit (toString f.getId)
    `(term| LawfulJson.fromField_of_field ($draftToJsonId x) $keyLit (x.$f:ident) rfl)
  let draftDepthProof ← fs.foldrM (init := ← `(term| Nat.le_refl 0)) fun f acc =>
    `(term| Codec.max_le_max (LawfulJson.depth_toJson (x.$f:ident)) $acc)
  pure #[
    ← `(command| structure $draftId where
          $[$fs:ident : String := ""]*
        deriving Inhabited, DecidableEq, Repr),
    ← `(command| def $emptyId : $draftId := { $[$fs:ident := $emptyVals],* }),
    ← `(command| def $draftToJsonId (x : $draftId) : Json := Json.obj [$[$draftJsonPairs],*]),
    ← `(command| def $draftFromId (j : Json) : Except String $draftId := do
          $[let $fs:ident ← $draftJsonDecodes:term]*
          return { $[$fs:ident],* }),
    ← `(command| instance $(mkIdent (tId ++ `Draft ++ `instToJson)):ident : ToJson $draftId := ⟨$draftToJsonId⟩),
    ← `(command| instance $(mkIdent (tId ++ `Draft ++ `instFromJson)):ident : FromJson $draftId := ⟨$draftFromId⟩),
    ← `(command| instance $(mkIdent (tId ++ `Draft ++ `instNonNullJson)):ident : NonNullJson $draftId := ⟨fun _ => nofun⟩),
    ← `(command| instance $(mkIdent (tId ++ `Draft ++ `instLawfulJson)):ident : LawfulJson $draftId where
          depthBound := 1
          depth_toJson x := Nat.add_le_add_left $draftDepthProof 1
          fromJson_toJson x := by
            have h : $draftFromId ($draftToJsonId x) = .ok x := by
              unfold $draftFromId
              simp only [$[$draftFieldEqs:term],*, bind, Except.bind, pure, Except.pure]
            exact h) ]

open Lean Elab Command Term in
private def mkSchemaCoreCmds (t : Ident) (cbns : Array Ident) (cbts : Array Term)
    (tApp parseApp canApp viewApp : TSyntax `term) (draftId : Ident)
    (fs : Array Ident) (inputs : Array Term) (refined : Array Bool) :
    CommandElabM (Array (TSyntax `command)) := do
  let tId         := t.getId
  let parseId     := mkIdent (tId ++ `parse)
  let canId       := mkIdent (tId ++ `canSubmit)
  let iffId       := mkIdent (tId ++ `canSubmit_iff)
  let viewId      := mkIdent (tId ++ `formView)
  let formValidId := mkIdent (tId ++ `formView_validIn)
  let pairs := fs.zip inputs
  let structTys ← (pairs.zip refined).mapM fun ((_, inp), r) =>
    if r then `(Field ($inp).valid) else `(Codec.Val $inp)
  let runCalls ← (pairs.zip refined).mapM fun ((f, inp), r) =>
    if r then `(($inp).run (d.$f:ident)) else `(($inp).parse (d.$f:ident))
  let isSomes ← runCalls.mapM fun rc => `(($rc).isSome)
  let rhs ← match isSomes.toList with
    | []      => `(True)
    | c :: cs => cs.foldlM (init := c) fun acc x => `($acc ∧ $x)
  let casesTac ← runCalls.foldrM (init := ← `(tactic|
    simp only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true,
      and_true, true_and, and_false, false_and, iff_self, bind, Option.bind, pure, Pure.pure]))
    fun rc acc => `(tactic| cases $rc:term <;> $acc)
  let rowGroups ← (pairs.zip runCalls).mapM fun ((f, inp), rc) => do
    let nameLit := Syntax.mkStrLit (toString f.getId)
    let errLit  := Syntax.mkStrLit ("Please enter a valid " ++ toString f.getId)
    `(term| Codec.formFieldRow ($inp).inForm ($inp).wrapLabel
              (d.$f:ident != "" && ($rc).isNone) $nameLit $errLit
              (($inp).render (d.$f:ident) (fun v => onEdit { d with $f:ident := v })))
  let submitBtn ← `(term|
    match ($parseApp d) with
    | some _qedParsed => el "button" [onClick (submit _qedParsed)] "Submit"
    | none            => el "button" [disabled true] "Submit")
  let viewBody ← rowGroups.foldrM (init := ← `(term| [$submitBtn])) fun g acc => `(term| $g ++ $acc)
  pure #[
    ← `(command| structure $t $[($cbns:ident : $cbts:term)]* where
          $[$fs:ident : $structTys]*),
    ← `(command| def $parseId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Option $tApp := do
          $[let $fs:ident ← $runCalls:term]*
          return { $[$fs:ident],* }),
    ← `(command| def $canId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Bool :=
          ($parseApp d).isSome),
    ← `(command| theorem $iffId $[($cbns:ident : $cbts:term)]* (d : $draftId) :
          $canApp d = true ↔ $rhs := by unfold $canId $parseId; $casesTac),
    ← `(command| def $viewId {msg : Type} $[($cbns:ident : $cbts:term)]* (d : $draftId)
          (onEdit : $draftId → msg) (submit : $tApp → msg) : Html msg :=
          el "div" [cls "qed-form"] $viewBody),
    ← `(command| @[simp] theorem $formValidId {msg : Type} $[($cbns:ident : $cbts:term)]*
          (inForm : Bool) (d : $draftId) (onEdit : $draftId → msg) (submit : $tApp → msg) :
          Html.validIn ⟨.normal, false, false, inForm⟩ ($viewApp d onEdit submit) = true := by
          unfold $viewId
          cases _hp : ($parseApp d) <;> cases inForm <;> dsimp only <;>
            simp only [el, cls, disabled, onClick, Html.validIn, Html.validListIn,
              Attr.valid, Attr.validKeyValue, Attr.valid_cls, Attr.valid_flag, Attr.valid_on,
              Attr.validList_cons, Attr.validList_nil, Attr.validList_append,
              Attr.isLocalCell_cls, Attr.isLocalCell_flag, Attr.isLocalCell_on,
              Attr.hasLocalCell_cons, Attr.hasLocalCell_nil, Attr.hasLocalCell_append,
              Html.validListIn_append, Html.validListIn_cons, Html.validListIn_nil,
              Codec.formFieldRow_validListIn, Codec.render_valid_simp, validTextIn_normal,
              Qed.reduceStepHtmlCtx, Qed.reduceIsVoidTag, Qed.reduceIsSafeAttrName, Qed.reduceIsUrlAttrName,
              Bool.true_and, Bool.and_true, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, Bool.not_false,
              List.isEmpty_cons, List.isEmpty_nil]) ]

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
  let pairs := fs.zip inputs
  let jsonDecodes ← (pairs.zip refined).mapM fun ((f, inp), r) => do
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
  let depthBoundExpr ← inputs.foldrM (init := ← `(term| (0 : Nat))) fun inp acc =>
    `(term| Nat.max (LawfulJson.depthBound (Codec.Val $inp)) $acc)
  let depthProofExpr ← jsonReads.foldrM (init := ← `(term| Nat.le_refl 0)) fun rd acc =>
    `(term| Codec.max_le_max (LawfulJson.depth_toJson $rd) $acc)
  let fieldEqs ← (pairs.zip refined).mapM fun ((f, inp), r) => do
    let keyLit := Syntax.mkStrLit (toString f.getId)
    if r then `(term| Codec.fromJsonField_of_field $inp ($toJsonId x) $keyLit (x.$f) rfl)
    else `(term| LawfulJson.fromField_of_field ($toJsonId x) $keyLit (x.$f) rfl)
  let lawfulCmds : Array (TSyntax `command) ← if allLawful then
    pure #[← `(command|
      instance $(mkIdent (tId ++ `instLawfulJson)):ident : LawfulJson $t where
        depthBound := 1 + $depthBoundExpr
        depth_toJson x := Nat.add_le_add_left $depthProofExpr 1
        fromJson_toJson x := by
          have h : $fromJsonId ($toJsonId x) = .ok x := by
            unfold $fromJsonId
            simp only [$[$fieldEqs:term],*, bind, Except.bind, pure, Except.pure]
          exact h)]
  else pure #[]
  let jsonInstCmds : Array (TSyntax `command) := #[
    ← `(command| instance $(mkIdent (tId ++ `instToJson)):ident : ToJson $t := ⟨$toJsonId⟩),
    ← `(command| instance $(mkIdent (tId ++ `instFromJson)):ident : FromJson $t := ⟨$fromJsonId⟩),
    ← `(command| instance $(mkIdent (tId ++ `instNonNullJson)):ident : NonNullJson $t := ⟨fun _ => nofun⟩) ] ++ lawfulCmds
  return jsonFnCmds ++ jsonInstCmds

def resolveSchemaCtxArgs (ref : Lean.Syntax) (tag : String) (ctxBinders : Array Lean.Name)
    (props : Array (Lean.Syntax × String × Lean.Term)) (checkUnknown := true) : Lean.MacroM (Array Lean.Term) := do
  let mut ctxVals : Std.HashMap Lean.Name Lean.Term := {}
  let mut ctxArg? : Option Lean.Term := none
  for (attrRef, nm, v) in props do
    if nm == "ctx" && ctxBinders.size == 1 then ctxArg? := some v
    else if ctxBinders.contains (.mkSimple nm) then ctxVals := ctxVals.insert (.mkSimple nm) v
    else if checkUnknown then Lean.Macro.throwErrorAt attrRef s!"<{tag}>: unknown attribute `{nm}`"
  ctxBinders.mapM fun b => do
    if let some v := ctxVals[b]? <|> ctxArg? then pure v
    else Lean.Macro.throwErrorAt ref s!"<{tag}> requires context attribute `{b}=\{…}`{if ctxBinders.size == 1 then " (or `ctx={…}`)" else ""}"

open Lean Elab Command Term in
@[command_elab schemaCmd] def elabSchemaCmd : CommandElab
  | stx => do
      let t : Ident := ⟨stx[1]⟩
      let rawCtx := if stx[2].getNumArgs == 3 then stx[2][1].getSepArgs else #[]
      let cbns : Array Ident := rawCtx.map (⟨·[0]⟩)
      let cbts ← rawCtx.mapM fun cp => liftMacroM (return (← Qed.Lang.lowerQedType cp[2] false).1)
      let fStxs := stx[4].getArgs
      let fs : Array Ident := fStxs.map (⟨·[0]⟩)
      let rawSpecs ← fStxs.mapM fun f => liftMacroM (lowerSchemaFieldSpec f[2])
      let whereClauses : Array (Array Term) ← fStxs.mapM fun f => do
        if f[3].getNumArgs == 2 then
          f[3][1].getSepArgs.mapM fun w => liftMacroM (Qed.Lang.lowerSimpleQedExpr .propInv w)
        else pure #[]
      let tId        := t.getId
      let draftId    := mkIdent (tId ++ `Draft)
      let parseId    := mkIdent (tId ++ `parse)
      let canId      := mkIdent (tId ++ `canSubmit)
      let viewId     := mkIdent (tId ++ `formView)
      let toJsonId   := mkIdent (tId ++ `toJson)
      let fromJsonId := mkIdent (tId ++ `fromJson)
      let (inputs, refined, allLawful, allProto, allLawfulProto) ←
        resolveSchemaFields cbns cbts fs rawSpecs whereClauses
      let pairs := fs.zip inputs
      checkSchemaFieldsDecidable cbns cbts pairs
      let cbnsT : Array (TSyntax `term) := cbns.map fun c => ⟨c.raw⟩
      let appTo : TSyntax `term → CommandElabM (TSyntax `term) := fun head =>
        cbnsT.foldlM (init := head) fun acc c => `($acc $c)
      let tApp        ← appTo ⟨t.raw⟩
      let parseApp    ← appTo ⟨parseId.raw⟩
      let canApp      ← appTo ⟨canId.raw⟩
      let viewApp     ← appTo ⟨viewId.raw⟩
      let toJsonApp   ← appTo ⟨toJsonId.raw⟩
      let fromJsonApp ← appTo ⟨fromJsonId.raw⟩
      let jsonReads ← (pairs.zip refined).mapM fun ((f, _), r) =>
        if r then `((x.$f:ident).val) else `(x.$f:ident)
      let draftCmds ← mkDraftCmds tId draftId fs
      let coreCmds ← mkSchemaCoreCmds t cbns cbts tApp parseApp canApp viewApp draftId fs inputs refined
      let jsonCmds ← mkSchemaJsonCmds t cbns cbts tApp toJsonApp fromJsonApp fs inputs refined jsonReads allLawful
      let draftProtoCmds ← mkDraftProtoCmds tId draftId fs
      let protoCmds ← mkSchemaProtoCmds t cbns cbts tApp appTo fs inputs refined jsonReads allProto allLawfulProto
      for c in draftCmds ++ coreCmds ++ jsonCmds ++ draftProtoCmds ++ protoCmds do elabCommand c
      let ns ← getCurrNamespace
      let fullSchema := ns ++ tId
      let info : SchemaFormInfo := {
        fullName := fullSchema ++ `Form
        formViewName := fullSchema ++ `formView
        ctxBinders := cbns.map (·.getId.eraseMacroScopes)
      }
      modifyEnv fun env => schemaFormRegistry.addEntry env info

namespace Demo

schema Signup:
  email : String where '@' in email, email.length >= 3
  age   : Nat    where age >= 18
  agree : Bool   where agree

end Demo

end Qed
