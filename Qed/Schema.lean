import Qed.Notation
import Qed.Json
import Qed.Date
import Lean

namespace Qed

structure Field {α : Type} (p : α → Prop) where
  val : α
  ok  : p val

instance {α : Type} {p : α → Prop} : CoeOut (Field p) α := ⟨Field.val⟩
instance {α : Type} {p : α → Prop} [ToString α] : ToString (Field p) := ⟨fun f => toString f.val⟩

structure Codec (α : Type) where
  parse  : String → Option α
  render : {msg : Type} → (raw : String) → (set : String → msg) → Html msg
  valid  : α → Prop
  dec    : DecidablePred valid
  inForm : Bool := true

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

theorem max_le_max {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : Nat.max a b ≤ Nat.max c d :=
  Nat.max_le.2 ⟨Nat.le_trans h1 (Nat.le_max_left c d), Nat.le_trans h2 (Nat.le_max_right c d)⟩

private def toInt? (s : String) : Option Int :=
  match s.toList with
  | '-' :: ds => (String.ofList ds).toNat?.map fun n => -(Int.ofNat n)
  | _         => s.toNat?.map Int.ofNat

def text : Codec String where
  parse := some; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [value raw, onInput set]

def textarea : Codec String where
  parse := some; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "textarea" [value raw, onInput set]

def nat : Codec Nat where
  parse := fun s => s.toNat?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [type' "number", attr "min" "0", value raw, onInput set]

def int : Codec Int where
  parse := toInt?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [type' "number", value raw, onInput set]

def checkbox : Codec Bool where
  parse := fun s => some (s == "true"); valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set =>
    el "input" [type' "checkbox", checked (raw == "true"), onCheck (fun b => set (toString b))]

def date : Codec Date where
  parse := Date.parse?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [type' "date", value raw, onInput set]

def select (options : List (String × String)) : Codec String where
  parse := fun s => if options.any (fun o => o.1 == s) then some s else none
  valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set =>
    el "select" [value raw, onChange set]
      (options.map fun (v, lbl) => el "option" [value v] [lbl])

def radios (group : String) (options : List (String × String)) : Codec String where
  parse := fun s => if options.any (fun o => o.1 == s) then some s else none
  valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set =>
    el "div" [cls "qed-radios"]
      (options.map fun (v, lbl) =>
        el "label" [] [el "input" [type' "radio", Qed.name group, value v, checked (raw == v), onChange set], lbl])

def json (α : Type) [ToJson α] [FromJson α] : Codec α where
  parse := fun _ => none
  valid := fun _ => True; dec := fun _ => inferInstance
  render := fun _ _ => el "span" [] []
  inForm := false

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

open Lean in
syntax schemaField := ident " : " term (" where " sepBy1(term, ","))?

open Lean in
syntax (name := schemaCmd) "schema " ident ("(" ident " : " term ")")* " where "
  sepBy1IndentSemicolon(schemaField) : command

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
    TermElabM (Array (Term × Bool × Bool)) := do
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
          pure (inp, isRef, isLaw)
      | _ =>
          throwErrorAt rawSpec m!"failed to resolve schema field `{f.getId}` to a `Codec`"

open Lean Elab Command in
private def resolveSchemaFields (cbns : Array Ident) (cbts : Array Term)
    (fs : Array Ident) (rawSpecs : Array Term) (whereClauses : Array (Array Term)) :
    CommandElabM (Array Term × Array Bool × Bool) := do
  let res ← liftTermElabM (elabSchemaFieldsAux cbns cbts fs rawSpecs whereClauses 0)
  return (res.map (·.1), res.map (·.2.1), res.all (·.2.2))

open Lean Elab Command Term Meta in
private def elabPredProbe (cbns : Array Ident) (cbts : Array Term) (inp : Term) (i : Nat) :
    TermElabM Unit := do
  if i < cbns.size then
    let bt ← elabType cbts[i]!
    withLocalDeclD cbns[i]!.getId bt fun _ => elabPredProbe cbns cbts inp (i + 1)
  else
    discard <| elabTermAndSynthesize inp none

open Lean Elab Command Term in
elab_rules : command
  | `(schema $t:ident $[($cbns:ident : $cbts:term)]* where $[$fieldStxs:schemaField]*) => do
      let mut fs : Array Ident := #[]
      let mut rawSpecs : Array Term := #[]
      let mut whereClauses : Array (Array Term) := #[]
      for fstx in fieldStxs do
        match fstx with
        | `(schemaField| $f:ident : $spec:term $[where $[$ps:term],*]?) =>
            fs := fs.push f
            rawSpecs := rawSpecs.push spec
            whereClauses := whereClauses.push (ps.getD #[])
        | _ => throwUnsupportedSyntax
      let draftId       := mkIdent (t.getId ++ `Draft)
      let emptyId       := mkIdent (t.getId ++ `Draft ++ `empty)
      let draftToJsonId := mkIdent (t.getId ++ `Draft ++ `toJson)
      let draftFromId   := mkIdent (t.getId ++ `Draft ++ `fromJson)
      let parseId       := mkIdent (t.getId ++ `parse)
      let canId         := mkIdent (t.getId ++ `canSubmit)
      let iffId         := mkIdent (t.getId ++ `canSubmit_iff)
      let viewId        := mkIdent (t.getId ++ `formView)
      let decodeId      := mkIdent (t.getId ++ `decode)
      let encodeId      := mkIdent (t.getId ++ `encode)
      let toJsonId      := mkIdent (t.getId ++ `toJson)
      let fromJsonId    := mkIdent (t.getId ++ `fromJson)
      let (inputs, refined, allLawful) ← resolveSchemaFields cbns cbts fs rawSpecs whereClauses
      let pairs := fs.zip inputs
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
      let cbnsT : Array (TSyntax `term) := cbns.map fun c => ⟨c.raw⟩
      let appTo : TSyntax `term → CommandElabM (TSyntax `term) := fun head =>
        cbnsT.foldlM (init := head) fun acc c => `($acc $c)
      let tApp        ← appTo ⟨t.raw⟩
      let parseApp    ← appTo ⟨parseId.raw⟩
      let canApp      ← appTo ⟨canId.raw⟩
      let toJsonApp   ← appTo ⟨toJsonId.raw⟩
      let fromJsonApp ← appTo ⟨fromJsonId.raw⟩
      let emptyVals ← fs.mapM fun _ => `(term| "")
      let structTys ← (pairs.zip refined).mapM fun ((_, inp), r) =>
        if r then `(Field ($inp).valid) else `(Codec.Val $inp)
      let runCalls ← (pairs.zip refined).mapM fun ((f, inp), r) =>
        if r then `(($inp).run (d.$f:ident)) else `(($inp).parse (d.$f:ident))
      let jsonDecodes ← (pairs.zip refined).mapM fun ((f, inp), r) => do
        let keyLit := Syntax.mkStrLit (toString f.getId)
        if r then `(($inp).fromJsonField j $keyLit)
        else `((FromJsonField.fromField j $keyLit : Except String (Codec.Val $inp)))
      let jsonReads ← (pairs.zip refined).mapM fun ((f, _), r) =>
        if r then `((x.$f:ident).val) else `(x.$f:ident)
      let jsonPairs ← (fs.zip jsonReads).mapM fun (f, rd) =>
        let keyLit := Syntax.mkStrLit (toString f.getId); `(($keyLit, toJson $rd))
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
      let isSomes ← runCalls.mapM fun rc => `(($rc).isSome)
      let rhs ← match isSomes.toList with
        | []      => `(True)
        | c :: cs => cs.foldlM (init := c) fun acc x => `($acc ∧ $x)
      let casesTac ← runCalls.foldrM (init := ← `(tactic| simp)) fun rc acc =>
        `(tactic| cases $rc:term <;> $acc)
      let rowGroups ← (pairs.zip runCalls).mapM fun ((f, inp), rc) => do
        let nameLit := Syntax.mkStrLit (toString f.getId)
        let errLit  := Syntax.mkStrLit ("Please enter a valid " ++ toString f.getId)
        `(term|
            (if ($inp).inForm then
              [(let bad := d.$f:ident != "" && ($rc).isNone
                el "label" [cls "qed-field", attr "aria-invalid" (if bad then "true" else "false")]
                  ([ el "span" [cls "qed-label"] [$nameLit],
                     ($inp).render (d.$f:ident) (fun v => onEdit { d with $f:ident := v }) ]
                   ++ (if bad then [el "span" [cls "qed-error"] [$errLit]] else [])))]
             else []))
      let submitBtn ← `(term| el "button" [disabled (!($parseApp d).isSome), onClick submit] "Submit")
      let viewBody ← rowGroups.foldrM (init := ← `(term| [$submitBtn])) fun g acc => `(term| $g ++ $acc)
      let formCmds : Array (TSyntax `command) := #[
        ← `(command| structure $draftId where
              $[$fs:ident : String := ""]*
            deriving Inhabited, DecidableEq, Repr),
        ← `(command| def $emptyId : $draftId := { $[$fs:ident := $emptyVals],* }),
        ← `(command| def $draftToJsonId (x : $draftId) : Json := Json.obj [$[$draftJsonPairs],*]),
        ← `(command| def $draftFromId (j : Json) : Except String $draftId := do
              $[let $fs:ident ← $draftJsonDecodes:term]*
              return { $[$fs:ident],* }),
        ← `(command| instance : ToJson $draftId := ⟨$draftToJsonId⟩),
        ← `(command| instance : FromJson $draftId := ⟨$draftFromId⟩),
        ← `(command| instance : LawfulJson $draftId where
              depthBound := 1
              depth_toJson x := Nat.add_le_add_left $draftDepthProof 1
              fromJson_toJson x := by
                have h : $draftFromId ($draftToJsonId x) = .ok x := by
                  unfold $draftFromId
                  simp only [$[$draftFieldEqs:term],*, bind, Except.bind, pure, Except.pure]
                exact h),
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
              (onEdit : $draftId → msg) (submit : msg) : Html msg :=
              el "div" [cls "qed-form"] $viewBody) ]
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
      let depthBoundExpr ← inputs.foldrM (init := ← `(term| (0 : Nat))) fun inp acc =>
        `(term| Nat.max (LawfulJson.depthBound (Codec.Val $inp)) $acc)
      let depthProofExpr ← jsonReads.foldrM (init := ← `(term| Nat.le_refl 0)) fun rd acc =>
        `(term| Codec.max_le_max (LawfulJson.depth_toJson $rd) $acc)
      let fieldEqs ← (pairs.zip refined).mapM fun ((f, inp), r) => do
        let keyLit := Syntax.mkStrLit (toString f.getId)
        if r then `(term| Codec.fromJsonField_of_field $inp ($toJsonId x) $keyLit (x.$f) rfl)
        else `(term| LawfulJson.fromField_of_field ($toJsonId x) $keyLit (x.$f) rfl)
      let lawfulCmds : Array (TSyntax `command) ← if cbns.isEmpty && allLawful then
        pure #[← `(command|
          instance : LawfulJson $t where
            depthBound := 1 + $depthBoundExpr
            depth_toJson x := Nat.add_le_add_left $depthProofExpr 1
            fromJson_toJson x := by
              have h : $fromJsonId ($toJsonId x) = .ok x := by
                unfold $fromJsonId
                simp only [$[$fieldEqs:term],*, bind, Except.bind, pure, Except.pure]
              exact h)]
      else pure #[]
      let jsonInstCmds : Array (TSyntax `command) := #[
        ← `(command| instance : ToJson $t := ⟨$toJsonId⟩),
        ← `(command| instance : FromJson $t := ⟨$fromJsonId⟩) ] ++ lawfulCmds
      let cmds := formCmds ++ jsonFnCmds ++ (if cbns.isEmpty then jsonInstCmds else #[])
      for c in cmds do elabCommand c

namespace Demo

schema Signup where
  email : String where email.contains '@', email.length >= 3
  age   : Nat    where age >= 18
  agree : Bool   where agree

end Demo

end Qed
