import Qed.Schema.Codec
import Qed.Schema.Registry
import Qed.Verify.Core

namespace Qed

section SchemaParsers
open Lean Parser
private abbrev pType : Parser := withPosition (categoryParser `qedType 0)
private abbrev pExpr : Parser := categoryParser `qedExpr 0
def schemaFieldJsonOnly : Parser := node `Qed.schemaFieldJsonOnly (atomic (identEq `jsonOnly >> checkNoWsBefore "" >> "(") >> pType >> ")")
def schemaFieldCall     : Parser := node `Qed.schemaFieldCall (atomic (ident >> checkNoWsBefore "" >> "(") >> sepBy (categoryParser `qedCallArg 0) "," >> ")")
def schemaFieldSpec     : Parser := schemaFieldJsonOnly <|> schemaFieldCall <|> pType
def schemaFieldP        : Parser := node `Qed.schemaField (withPosition (ident >> ":" >> schemaFieldSpec >> optional (checkColGt >> " where " >> sepBy1 pExpr ",")))
def schemaExampleFieldP : Parser := node `Qed.schemaExampleField (checkColGt >> ident >> "=" >> pExpr)
def schemaExampleP      : Parser := node `Qed.schemaExample (withPosition (atomic (symbol "example" >> ident >> ":") >> sepBy1 schemaExampleFieldP ","))
def schemaRejectsP      : Parser := node `Qed.schemaRejects (withPosition (atomic (identEq `rejects >> ident >> ":") >> sepBy1 schemaExampleFieldP ","))
def schemaInvP          : Parser := node `Qed.schemaInv (withPosition (atomic (symbol "invariant" >> ident >> ":") >> sepBy1 pExpr ","))
def schemaItemP         : Parser := schemaExampleP <|> schemaRejectsP <|> schemaInvP <|> schemaFieldP
@[command_parser] def schemaCmd : Parser := leading_parser withPosition
  ("schema " >> ident >> optional (checkLineEq >> "(" >> sepBy1 schemaCtxParamP "," >> ")") >> ":" >> checkColGt "expected indented `schema` fields" >> many1Indent schemaItemP)
def recordFieldP : Parser := node `Qed.recordField (withPosition (
  ident >> ":" >> pType >> optional (checkLineEq >> "=" >> pExpr) >> optional (checkColGt >> " where " >> sepBy1 pExpr ",")))
def recordItemP : Parser := schemaExampleP <|> schemaRejectsP <|> schemaInvP <|> recordFieldP
@[command_parser] def recordCmd : Parser := leading_parser
  optional Command.docComment >> withPosition (
    atomic (optional (symbol "private") >> identEq `record) >> ident >> optional (checkLineEq >> "(" >> sepBy1 schemaCtxParamP "," >> ")") >> ":" >>
    checkColGt "expected indented `record` fields" >> many1Indent recordItemP)
def enumParamP   : Parser := node `Qed.enumParam (ident >> ":" >> pType)
def enumVariantP : Parser := node `Qed.enumVariant (withPosition (
  ident >> optional (checkNoWsBefore "" >> "(" >> sepBy1 enumParamP "," >> ")") >> optional (checkLineEq >> "=" >> strLit)))
@[command_parser] def enumCmd : Parser := leading_parser
  optional Command.docComment >> withPosition (
    atomic (optional (symbol "private") >> identEq `enum) >> ident >> ":" >> checkColGt "expected indented `enum` variants" >> many1Indent enumVariantP)
@[command_parser] def constCmd : Parser := leading_parser
  optional Command.docComment >>
  atomic (optional (symbol "private") >> identEq `const >> ident) >> optional (":" >> pType) >> "=" >> pExpr
@[command_parser] def fieldCmd : Parser := leading_parser
  optional Command.docComment >> withPosition (
    atomic (identEq `field) >> ident >> optional (checkLineEq >> "(" >> sepBy1 schemaCtxParamP "," >> ")") >>
    ":" >> pType >> checkColGt >> symbol "where" >> ident >> "=>" >> sepBy1 pExpr ",")
end SchemaParsers

section SchemaElab
open Lean Elab Command Term Meta

private def lowerSchemaFieldSpec (stx : Syntax) : MacroM Term := match stx.getKind with
  | `Qed.schemaFieldJsonOnly => do `(jsonOnly $((← Qed.Lang.lowerQedType (stx.getArg 2) false).1))
  | `Qed.schemaFieldCall     => do Qed.Lang.mkAppTerms ⟨stx.getArg 0⟩ (← (stx.getArg 2).getSepArgs.mapM fun a => Qed.Lang.lowerSimpleQedExpr .val (a.getArg 0))
  | _                        => do return (← Qed.Lang.lowerQedType stx false).1

private def primSchemaTypes : Array (Name × Name) :=
  #[(``String, ``Qed.Codec.text), (``Nat, ``Qed.Codec.nat), (``Int, ``Qed.Codec.int), (``Bool, ``Qed.Codec.checkbox), (``Qed.Date, ``Qed.Codec.date)]

private def extractOptDoc (optDoc : Syntax) : Option (TSyntax ``Lean.Parser.Command.docComment) :=
  if optDoc.getNumArgs == 1 then some ⟨optDoc.getArg 0⟩ else none

@[noinline]
private partial def resolveCodecBase (fieldName : Name) (rawSpec : Term) : TermElabM (Term × Option Term) := do
  if let `($fn:ident $arg:term) := rawSpec then
    if fn.getId.eraseMacroScopes == `jsonOnly then
      let (base, ty?) ← resolveCodecBase fieldName arg
      return (← `(Qed.Codec.jsonOnly $base), ty?)
  let scopedSpec ← `(open Qed.Codec in $rawSpec)
  let e ← elabTermAndSynthesize scopedSpec none; let ety ← whnf (← instantiateMVars (← inferType e))
  if ety.isAppOfArity ``Qed.Codec 1 then return (scopedSpec, none)
  else if ety.isSort then
    let eWhnf ← whnf (← instantiateMVars e)
    if let some (_, codecNm) := primSchemaTypes.find? (eWhnf.isConstOf ·.1) then return (mkCIdent codecNm, some rawSpec)
    if (← trySynthInstance (← mkAppM ``Qed.DefaultCodec #[e])) matches .some _ then return (← `((Qed.DefaultCodec.codec : Qed.Codec $rawSpec)), some rawSpec)
    throwErrorAt rawSpec m!"schema field `{fieldName}` has type `{rawSpec}`, which has no default `Codec` or JSON (`ToJson`/`FromJson`) instances.\nProvide a `DefaultCodec` or JSON instances for `{rawSpec}`, or use a supported field type (`String`, `Nat`, `Int`, `Bool`, `Date`, `select([...])`, `textarea`, `jsonOnly(...)`)."
  else throwErrorAt rawSpec m!"schema field `{fieldName}` must be a type (`String`, `Nat`, `Int`, `Bool`, `Date`, …) or a `Codec` (e.g. `select([...])`, `textarea`, `jsonOnly(String)`), but this has type{indentExpr ety}"

private structure ResolvedField where mk ::
  (input : Term) (valTy : Term) (predTerm : Term)
  (isRefined isJson isLawful isProto isLawfulP isBEq isLawfulBEq : Bool)
  (tyName : Name) (hasInhab hasRepr : Bool)
deriving Inhabited

private structure SchemaInvInfo where mk ::
  (invId : Ident) (invAppInFs : Term) (invLabel : String)

private structure SchemaCtx where mk ::
  (kindName : String) (t : Ident) (cbns : Array Ident) (cbts : Array Term) (tApp : Term)
  (fs : Array Ident) (inputs : Array Term) (valTys : Array Term) (preds : Array Term)
  (refined : Array Bool) (whereLabels : Array String)
  (invInfo? : Option SchemaInvInfo := none)
  (isPrivate : Bool := false)

private structure ParsedDataHeader where
  cbns          : Array Ident
  cbts          : Array Term
  fStxs         : Array Syntax
  exampleStxs   : Array Syntax
  rejectStxs    : Array Syntax
  invStxs       : Array Syntax
  fs            : Array Ident
  whereRawExprs : Array (Array Syntax)
  whereLabels   : Array String
  whereClauses  : Array (Array Term)

private structure ParsedEnumVariant where
  ident    : Ident
  params   : Array (Ident × Term)
  wireName : String
deriving Inhabited

private def SchemaCtx.appTo (sc : SchemaCtx) (head : Term) : CommandElabM Term := Qed.Lang.mkAppTerms head (sc.cbns.map (⟨·.raw⟩))

private partial def withCtxDecls {α : Type} (cbns : Array Ident) (cbts : Array Term) (k : TermElabM α) (i : Nat := 0) : TermElabM α := do
  if i < cbns.size then withLocalDeclD cbns[i]!.getId (← elabType cbts[i]!) fun _ => withCtxDecls cbns cbts k (i + 1) else k

private def probeInst (cls : Name) (ty : Expr) : MetaM Bool := do
  if let some goal ← try some <$> mkAppM cls #[ty] catch _ => pure none then
    return (← trySynthInstance goal) matches .some _
  else return false

private def probeTypeTraits (ty : Expr) : MetaM (Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool) := do
  let hasBEq ← match ← trySynthInstance (← mkAppM ``BEq #[ty]) with
    | .some beqInst => pure (true, (← trySynthInstance (← mkAppOptM ``LawfulBEq #[some ty, some beqInst])) matches .some _)
    | _ => pure (false, false)
  let isJson ← if ← probeInst ``Qed.ToJson ty then probeInst ``Qed.FromJsonField ty else pure false
  let isLawful ← if isJson then
      if ← probeInst ``Qed.LawfulJson ty then
        match ← trySynthInstance (← mkAppM ``Qed.ToJson #[ty]), ← trySynthInstance (← mkAppM ``Qed.FromJsonField #[ty]) with
        | .some tj, .some fj => pure ((← trySynthInstance (← mkAppOptM ``Qed.LawfulFromJsonField #[some ty, some tj, some fj])) matches .some _)
        | _, _ => pure false
      else pure false
    else pure false
  let isProto ← if ← probeInst ``Qed.ToProtoField ty then probeInst ``Qed.FromProtoField ty else pure false
  let isLawfulP ← if isProto then probeInst ``Qed.LawfulProtoField ty else pure false
  let hasInhab ← probeInst ``Inhabited ty
  let hasRepr ← probeInst ``Repr ty
  return (isJson, isLawful, isProto, isLawfulP, hasBEq.1, hasBEq.2, hasInhab, hasRepr)

private def checkDecPredErrors (kindName : String) (f : Ident) (inp : Term) (savedLog : MessageLog) (preCount : Nat) : TermElabM Unit := do
  if ← ((← Core.getMessageLog).toList.drop preCount).anyM fun msg => return ((← msg.data.toString).splitOn "DecidablePred").length > 1 then
    Core.setMessageLog savedLog
    throwErrorAt inp m!"{kindName} field `{f.getId}` has a refinement that isn't decidable, so validity can't be computed (no `DecidablePred` for it).\n\nThe usual cause is a predicate written with `def`. Write it inline with `where …` or as an `abbrev`, so Lean sees it reduces to a decidable check:\n    abbrev MyPredicate (x : …) : Prop := …\nIf it genuinely can't be decided, give it a `DecidablePred` instance."

private def checkRefinementDecidable (kindName : String) (ref : Ident) (α : Expr) (predTerm : Term) : TermElabM Expr := do
  let savedLog ← Core.getMessageLog; let preCount := savedLog.toList.length
  let predE ← elabTermEnsuringType predTerm (some (← mkArrow α (mkSort Level.zero)))
  let decInst? ← trySynthInstance (← mkAppM ``DecidablePred #[predE])
  unless decInst? matches .some _ do
    checkDecPredErrors kindName ref predTerm savedLog preCount
    let subject := if kindName == "field" then s!"field `{ref.getId}`" else s!"{kindName} field `{ref.getId}`"
    throwErrorAt predTerm m!"{subject} has a refinement that isn't decidable (no `DecidablePred` for it).\n\nWrite it inline with `where ...` or as an `abbrev`, or provide a `DecidablePred` instance."
  return predE

private def mkResolvedField (input valTy predTerm : Term) (isRefined : Bool) (α fieldTy : Expr) (checkBaseInhab : Bool := false) : TermElabM ResolvedField := do
  let (isJson, isLawful, isProto, isLawfulP, isBEq, isLawfulBEq, hasInhab0, hasRepr) ← probeTypeTraits fieldTy
  let hasInhab ← if checkBaseInhab && isRefined then probeInst ``Inhabited α else pure hasInhab0
  return .mk input valTy predTerm isRefined isJson isLawful isProto isLawfulP isBEq isLawfulBEq
    ((← whnf α).constName?.getD .anonymous) hasInhab hasRepr

private def elabSchemaFieldsAux (cbns : Array Ident) (cbts : Array Term)
    (fs : Array Ident) (rawSpecs : Array Term) (whereClauses : Array (Array Term)) : TermElabM (Array ResolvedField) :=
  withCtxDecls cbns cbts do
    ((fs.zip rawSpecs).zip whereClauses).mapM fun ((f, rawSpec), preds) => do
      let (base, directTy?) ← resolveCodecBase f.getId rawSpec
      let inp : Term ← if preds.isEmpty then pure base else `(Qed.Codec.refine $base (fun $f:ident => $(← mkConjBody preds)))
      let savedLog ← Core.getMessageLog; let preCount := savedLog.toList.length
      let c ← elabTermAndSynthesize inp none
      checkDecPredErrors "schema" f inp savedLog preCount
      match (← instantiateMVars (← inferType c)).getAppFnArgs with
      | (``Qed.Codec, #[α]) =>
          let isRefined := !(← isDefEq (mkApp2 (mkConst ``Qed.Codec.valid) α c) (Expr.lam `x α (mkConst ``True) .default))
          let valTy : Term ← match directTy? with
            | some dt => pure dt
            | none => try PrettyPrinter.delab α catch _ => `(Qed.Codec.Val $inp)
          mkResolvedField inp valTy (← `(($inp).valid)) isRefined α α
      | _ => throwErrorAt rawSpec m!"failed to resolve schema field `{f.getId}` to a `Codec`"

private def elabRecordFieldsAux (cbns : Array Ident) (cbts : Array Term)
    (fs : Array Ident) (rawTys : Array Term) (whereClauses : Array (Array Term)) : TermElabM (Array ResolvedField) :=
  withCtxDecls cbns cbts do
    ((fs.zip rawTys).zip whereClauses).mapM fun ((f, rawTy), preds) => do
      let α ← elabType rawTy
      let isRefined := !preds.isEmpty
      let predTerm : Term ← if isRefined then `(fun $f:ident : $rawTy => $(← mkConjBody preds)) else `(fun (_ : $rawTy) => True)
      let fieldTy : Expr ← if isRefined then Meta.mkAppM ``Qed.Field #[← checkRefinementDecidable "record" f α predTerm] else pure α
      mkResolvedField rawTy rawTy predTerm isRefined α fieldTy (checkBaseInhab := true)

@[noinline]
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
    ← `(command| instance $(mkIdent (tId ++ `instLawfulBEq)):ident $[($cbns:ident : $cbts:term)]* : LawfulBEq $tApp where eq_of_beq := $eqId; rfl := $rflId),
    ← `(command| instance (priority := low) $(mkIdent (tId ++ `instDecidableEq)):ident $[($cbns:ident : $cbts:term)]* : DecidableEq $tApp := Qed.decidableEqOfLawfulBEq) ]

@[noinline]
private def mkAutoDeriveCmds (sc : SchemaCtx) (resolved : Array ResolvedField) (defaultMasks : Array Bool) : CommandElabM (Array (TSyntax `command)) := do
  let mut out : Array (TSyntax `command) := #[]
  if sc.cbns.isEmpty && resolved.all (·.hasRepr) then
    out := out.push (← `(command| deriving instance Repr for $(sc.t)))
  let allInhab := sc.invInfo?.isNone && (resolved.zip defaultMasks).all fun (rf, hasDef) => hasDef || (!rf.isRefined && rf.hasInhab)
  if sc.cbns.isEmpty && allInhab then
    let mut inits : Array (TSyntax ``Lean.Parser.Term.structInstField) := #[]
    for ((f, rf), hasDef) in (sc.fs.zip resolved).zip defaultMasks do
      if !hasDef then
        inits := inits.push (← `(Lean.Parser.Term.structInstField| $f:ident := (default : $(rf.valTy))))
    out := out.push (← `(command| instance (priority := low) $(mkIdent (sc.t.getId ++ `instInhabited)):ident : Inhabited $(sc.t) := ⟨{ $[$inits:structInstField],* }⟩))
  return out

@[noinline]
private def mkSchemaCoreCmds (sc : SchemaCtx) (draftId : Ident) : CommandElabM (Array (TSyntax `command)) := do
  let (t, tId, cbns, cbts, tApp, fs) := (sc.t, sc.t.getId, sc.cbns, sc.cbts, sc.tApp, sc.fs); let pairs := fs.zip sc.inputs
  let structTys ← ((sc.valTys.zip sc.preds).zip sc.refined).mapM fun ((vt, pr), r) => if r then `(Field $pr) else pure vt
  let runCalls ← (pairs.zip sc.refined).mapM fun ((f, inp), r) => if r then `(($inp).run (d.$f:ident)) else `(($inp).parse (d.$f:ident))
  let (parseId, canId, viewId) := (mkIdent (tId ++ `parse), mkIdent (tId ++ `canSubmit), mkIdent (tId ++ `formView))
  let (parseApp, canApp, viewApp) := (← sc.appTo ⟨parseId.raw⟩, ← sc.appTo ⟨canId.raw⟩, ← sc.appTo ⟨viewId.raw⟩)
  let rhs ← mkConjBody (← runCalls.mapM fun rc => `(($rc).isSome)) (ascribeProp := false)
  let canSubmitPf : Term ← do
    let n := runCalls.size
    let mut pf ← `(term| Qed.optionBind_pure_isSome_iff $(runCalls[n - 1]!) _)
    for i in (Array.range (n - 1)).reverse do
      pf ← `(term| Qed.optionBind_isSome_iff $(runCalls[i]!) _ (fun _ => $pf))
    if n ≤ 2 then pure pf
    else
      let mut reassoc ← `(term| Iff.rfl)
      for _ in [0 : n - 2] do reassoc ← `(term| and_assoc.symm.trans $reassoc)
      `(term| Iff.trans $pf $reassoc)
  let rowGroups ← (pairs.zip runCalls).mapM fun ((f, inp), rc) =>
    `(term| Codec.formFieldRow ($inp).inForm ($inp).wrapLabel (d.$f:ident != "" && ($rc).isNone)
              $(Syntax.mkStrLit (toString f.getId)) $(Syntax.mkStrLit ("Please enter a valid " ++ toString f.getId))
              (($inp).render (d.$f:ident) (fun v => onEdit { d with $f:ident := v })))
  let viewBody ← rowGroups.foldrM (init := ← `(term| [Codec.submitBtn ($parseApp d) submit])) fun g acc => `(term| $g ++ $acc)
  let validBodyPf ← sc.inputs.foldrM (init := ← `(term| Codec.submitBtn_validIn inForm ($parseApp d) submit))
    fun inp acc => `(term| Codec.formRowCons_validIn inForm _ _ _ _ _ _ _ (($inp).render_valid inForm _ _) $acc)
  let structCmd ← match sc.invInfo? with
    | none => `(command| structure $t $[($cbns:ident : $cbts:term)]* where $[$fs:ident : $structTys]*)
    | some info => `(command| structure $t $[($cbns:ident : $cbts:term)]* where $[$fs:ident : $structTys]* (_inv : $(info.invAppInFs)))
  let parseBody ← match sc.invInfo? with
    | none => `(do $[let $fs:ident ← $runCalls:term]* return { $[$fs:ident],* })
    | some info => `(do $[let $fs:ident ← $runCalls:term]* if _hInv : $(info.invAppInFs) then return { $[$fs:ident],*, _inv := _hInv } else none)
  let canSubmitCmd ← match sc.invInfo? with
    | none => `(command| theorem $(mkIdent (tId ++ `canSubmit_iff)) $[($cbns:ident : $cbts:term)]* (d : $draftId) : $canApp d = true ↔ $rhs := by unfold $canId $parseId; exact $canSubmitPf)
    | some _ => `(command| theorem $(mkIdent (tId ++ `canSubmit_iff)) $[($cbns:ident : $cbts:term)]* (d : $draftId) : $canApp d = true ↔ ∃ _x : $tApp, $parseApp d = some _x := Option.isSome_iff_exists)
  pure #[
    structCmd,
    ← `(command| def $parseId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Option $tApp := $parseBody),
    ← `(command| def $canId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Bool := ($parseApp d).isSome),
    canSubmitCmd,
    ← `(command| def $viewId {msg : Type} $[($cbns:ident : $cbts:term)]* (d : $draftId) (onEdit : $draftId → msg) (submit : $tApp → msg) : Html msg := el "div" [cls "qed-form"] $viewBody),
    ← `(command| @[simp] theorem $(mkIdent (tId ++ `formView_validIn)) {msg : Type} $[($cbns:ident : $cbts:term)]* (inForm : Bool) (d : $draftId) (onEdit : $draftId → msg) (submit : $tApp → msg) :
          Html.validIn ⟨.normal, false, false, inForm⟩ ($viewApp d onEdit submit) = true := Codec.formDiv_validIn inForm _ $validBodyPf) ]

private partial def collectStxLits {α : Type} [BEq α] (extract : Syntax → Option α) (stx : Syntax) (acc : Array α) : Array α :=
  stx.getArgs.foldl (fun a ch => collectStxLits extract ch a) (match extract stx with | some v => Qed.Lang.pushUnique acc v | none => acc)

private def tryCheckPropWithTactic (goalTerm : Term) (tacStx : TSyntax `tactic) : CommandElabM Bool :=
  Qed.Diag.probeTermElabOk do
    discard <| elabTermEnsuringType (← `(by $tacStx:tactic)) (← elabType goalTerm); synthesizeSyntheticMVarsNoPostponing; return true

private def mkSchemaRefinementTacs : CommandElabM (TSyntax `tactic × TSyntax `tactic) := do
  let simpTac ← `(tactic| simp only [Qed.Codec.valid, Qed.Codec.refine, Qed.Codec.jsonOnly, Qed.Codec.text, Qed.Codec.textarea,
      Qed.Codec.nat, Qed.Codec.int, Qed.Codec.checkbox, Qed.Codec.date, Qed.Codec.select, Qed.Codec.radios, Qed.Codec.json, Qed.Lang.QedVal.val_id])
  let pfTac ← `(tactic| ((try $simpTac:tactic) <;> first | qedCloseGround | rfl | decide | omega | trivial | (simp_all; try qedCloseGround; try rfl; try decide; try omega)))
  return (simpTac, pfTac)

@[noinline]
private def synthesizeFieldWitness? (pfTac : TSyntax `tactic) (rf : ResolvedField) (rawWheres : Array Syntax) : CommandElabM (Option Term) := do
  if !rf.isRefined then if rf.hasInhab then return some (← `((default : $(rf.valTy)))) else return none
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
    | _          => if rf.hasInhab then pure #[← `((default : $(rf.valTy)))] else pure #[]
  for cand in cands do
    if ← tryCheckPropWithTactic (← `($(rf.predTerm) $cand)) pfTac then return some (← `(Qed.Field.mk (p := $(rf.predTerm)) $cand (by $pfTac:tactic)))
  return none

private def emitSatisfiableCmdsRaw (isPrivate : Bool) (t : Ident) (cbns : Array Ident) (cbts : Array Term) (tApp : Term)
    (ref : Syntax) (witness : Term) : CommandElabM Unit := do
  Qed.Lang.elabCmdWithVis isPrivate (← `(command| theorem $(mkIdentFrom ref (t.getId ++ `satisfiable)) $[($cbns:ident : $cbts:term)]* : ∃ _x : $tApp, True := ⟨$witness, trivial⟩))
  if cbns.isEmpty then Qed.Lang.elabCmdWithVis isPrivate (← `(command| instance $(mkIdentFrom ref (t.getId ++ `instNonempty)):ident : Nonempty $t := ⟨$witness⟩))

private def emitSatisfiableCmds (sc : SchemaCtx) (ref : Syntax) (witness : Term) : CommandElabM Unit :=
  emitSatisfiableCmdsRaw sc.isPrivate sc.t sc.cbns sc.cbts sc.tApp ref witness

private def parseSchemaFieldAssigns (sc : SchemaCtx) (clauseKind : String) (stx : Syntax) :
    CommandElabM (Ident × Array (Syntax × Term)) := do
  let (tId, fs) := (sc.t.getId, sc.fs)
  let nameId : Ident := ⟨stx.getArg 1⟩; let nm := nameId.getId; let validNames := fs.toList.map (·.getId.toString)
  let mut provided : Std.HashMap String Syntax := {}
  for entry in (stx.getArg 3).getSepArgs do
    let fid : Ident := ⟨entry.getArg 0⟩; let fName := fid.getId.toString
    unless validNames.contains fName do
      throwErrorAt fid s!"{sc.kindName} `{tId}` {clauseKind} `{nm}`: unknown field `{fName}`{Qed.Diag.didYouMean fName validNames} (expected: {String.intercalate ", " validNames})"
    if provided.contains fName then throwErrorAt fid s!"{sc.kindName} `{tId}` {clauseKind} `{nm}`: duplicate field `{fName}`"
    provided := provided.insert fName (entry.getArg 2)
  let vals ← fs.mapM fun f => do
    let fName := f.getId.toString
    let some valStx := provided[fName]? | throwErrorAt stx s!"{sc.kindName} `{tId}` {clauseKind} `{nm}`: missing required field `{fName}`"
    return (valStx, ← liftMacroM (Qed.Lang.lowerSimpleQedExpr .val valStx))
  return (nameId, vals)

@[noinline]
private def elabSchemaExampleClause (sc : SchemaCtx) (pfTac : TSyntax `tactic) (exStx : Syntax) (emitSatisfiable : Bool) : CommandElabM Unit := do
  let (tId, cbns, cbts, tApp, fs) := (sc.t.getId, sc.cbns, sc.cbts, sc.tApp, sc.fs)
  let (exName, rawVals) ← parseSchemaFieldAssigns sc "example" exStx
  let exId := exName.getId
  let fieldTerms ← (fs.zip rawVals).zipIdx.mapM fun ((f, (valStx, valTerm)), i) => do
    let fName := f.getId.toString
    if !sc.refined[i]! then return valTerm
    if sc.cbns.isEmpty then
      unless ← tryCheckPropWithTactic (← `($(sc.preds[i]!) $valTerm)) pfTac do
        let valStr := let s := Qed.Lang.stxSnippet valStx; if s.isEmpty then "<value>" else s
        throwErrorAt valStx m!"{sc.kindName} `{tId}` example `{exId}` failed `where` constraint on field `{fName}`:\n  • value `{valStr}` does not satisfy `{sc.whereLabels[i]!}`\n\nHint: Update `{fName}` in example `{exId}` so it satisfies `{sc.whereLabels[i]!}`, or weaken the `where` rule."
    `(Qed.Field.mk (p := $(sc.preds[i]!)) $valTerm (by $pfTac:tactic))
  let sampleId := mkIdentFrom exName (tId ++ exId)
  match sc.invInfo? with
  | none =>
      Qed.Lang.elabCmdWithVis sc.isPrivate (← `(command| def $sampleId $[($cbns:ident : $cbts:term)]* : $tApp := { $[$fs:ident := $fieldTerms:term],* }))
  | some info =>
      let invGoal ← Qed.Lang.mkAppTerms ⟨info.invId.raw⟩ (cbns.map (⟨·.raw⟩) ++ rawVals.map (·.2))
      if cbns.isEmpty then
        unless ← tryCheckPropWithTactic invGoal pfTac do
          throwErrorAt exStx m!"{sc.kindName} `{tId}` example `{exId}` failed `invariant`:\n  • values do not satisfy `{info.invLabel}`\n\nHint: Update example `{exId}` so it satisfies `{info.invLabel}`, or weaken the `invariant`."
      Qed.Lang.elabCmdWithVis sc.isPrivate (← `(command| def $sampleId $[($cbns:ident : $cbts:term)]* : $tApp := { $[$fs:ident := $fieldTerms:term],*, _inv := by $pfTac:tactic }))
  if emitSatisfiable then emitSatisfiableCmds sc exStx (← sc.appTo ⟨sampleId.raw⟩)

@[noinline]
private def elabSchemaRejectsClause (sc : SchemaCtx) (simpTac : TSyntax `tactic) (rejStx : Syntax) : CommandElabM Unit := do
  let (tId, cbns, cbts) := (sc.t.getId, sc.cbns, sc.cbts)
  let (rejName, rawVals) ← parseSchemaFieldAssigns sc "rejects" rejStx
  let rejId := rejName.getId
  let mut checks : Array Term := #[]
  for i in [0:sc.fs.size] do
    if sc.refined[i]! then
      checks := checks.push (← `($(sc.preds[i]!) $(rawVals[i]!.2)))
  if let some info := sc.invInfo? then
    checks := checks.push (← Qed.Lang.mkAppTerms ⟨info.invId.raw⟩ (cbns.map (⟨·.raw⟩) ++ rawVals.map (·.2)))
  if checks.isEmpty then
    throwErrorAt rejStx s!"{sc.kindName} `{tId}` `rejects {rejId}` requires at least one `where` or `invariant` constraint"
  let validConj ← Qed.mkConjBody checks (ascribeProp := false)
  let negGoal ← `(¬ ($validConj))
  let negTac ← `(tactic| ((try $simpTac:tactic) <;> first | qedCloseGround | decide | omega | (intro _h; simp_all; try omega; try qedCloseGround; try decide)))
  if cbns.isEmpty then
    unless ← tryCheckPropWithTactic negGoal negTac do
      throwErrorAt rejStx m!"{sc.kindName} `{tId}` `rejects {rejId}` failed: the provided values unexpectedly satisfy all `where` and `invariant` constraints.\n\nHint: Strengthen the `where`/`invariant` rules or fix the negative test case `{rejId}`."
  let thmId := mkIdentFrom rejName (tId ++ (Name.mkSimple s!"rejects_{rejId}"))
  Qed.Lang.elabCmdWithVis sc.isPrivate (← `(command| theorem $thmId $[($cbns:ident : $cbts:term)]* : $negGoal := by $negTac:tactic))

private def checkFieldUnsat (ref : Syntax) (valTy predTerm : Term) (simpTac : TSyntax `tactic) (errMsg : MessageData) : CommandElabM Unit := do
  if ← tryCheckPropWithTactic (← `(∀ _qed_x : $valTy, ¬ $predTerm _qed_x))
      (← `(tactic| (intro _qed_x; (try $simpTac:tactic) <;> first | omega | decide | (cases _qed_x <;> decide)))) then
    throwErrorAt ref errMsg

@[noinline]
private def checkSchemaSatAndExamples (sc : SchemaCtx) (resolved : Array ResolvedField)
    (whereRawExprs : Array (Array Syntax)) (exampleStxs rejectStxs : Array Syntax) : CommandElabM Unit := do
  let (simpTac, pfTac) ← mkSchemaRefinementTacs
  if !exampleStxs.isEmpty then
    for (exStx, idx) in exampleStxs.zipIdx do elabSchemaExampleClause sc pfTac exStx (idx == 0)
  else if sc.cbns.isEmpty && sc.invInfo?.isNone then
    for (rf, i) in resolved.zipIdx do
      if rf.isRefined then
        checkFieldUnsat sc.fs[i]! rf.valTy rf.predTerm simpTac
          m!"{sc.kindName} `{sc.t.getId}` is unsatisfiable: field `{sc.fs[i]!.getId}` has contradictory `where` constraints (`{sc.whereLabels[i]!}`) -- no value can ever satisfy it.\n\nHint: Fix or remove the conflicting `where` conditions on `{sc.fs[i]!.getId}`."
    if let some synthTerms ← resolved.zipIdx.foldlM (init := some #[]) fun acc? (rf, i) => do
        let some arr := acc? | return none
        return (← synthesizeFieldWitness? pfTac rf whereRawExprs[i]!).map arr.push then
      let fs := sc.fs
      let witId := mkIdentFrom sc.t (sc.t.getId ++ `_witness)
      elabCommand (← `(command| private def $witId : $(sc.t) := { $[$fs:ident := $synthTerms:term],* }))
      emitSatisfiableCmds sc sc.t witId
  for rejStx in rejectStxs do elabSchemaRejectsClause sc simpTac rejStx

private def splitDataItems (kindLow : String) (t : Ident) (items : Array Syntax) :
    CommandElabM (Array Syntax × Array Syntax × Array Syntax × Array Syntax) := do
  let tId := t.getId
  let mut fStxs : Array Syntax := #[]; let mut exampleStxs : Array Syntax := #[]; let mut rejectStxs : Array Syntax := #[]; let mut invStxs : Array Syntax := #[]
  let mut seenEx : Std.HashSet Name := {}; let mut seenRej : Std.HashSet Name := {}; let mut seenInv : Std.HashSet Name := {}
  for item in items do
    let k := item.getKind
    if k == `Qed.schemaExample then
      let exName : Ident := ⟨item.getArg 1⟩
      if seenEx.contains exName.getId then throwErrorAt exName s!"duplicate example `{exName.getId}` in `{kindLow} {tId}`"
      seenEx := seenEx.insert exName.getId; exampleStxs := exampleStxs.push item
    else if k == `Qed.schemaRejects then
      let rName : Ident := ⟨item.getArg 1⟩
      if seenRej.contains rName.getId then throwErrorAt rName s!"duplicate rejects `{rName.getId}` in `{kindLow} {tId}`"
      seenRej := seenRej.insert rName.getId; rejectStxs := rejectStxs.push item
    else if k == `Qed.schemaInv then
      let iName : Ident := ⟨item.getArg 1⟩
      if seenInv.contains iName.getId then throwErrorAt iName s!"duplicate invariant `{iName.getId}` in `{kindLow} {tId}`"
      seenInv := seenInv.insert iName.getId; invStxs := invStxs.push item
    else fStxs := fStxs.push item
  if fStxs.isEmpty then throwErrorAt t s!"`{kindLow} {tId}` must declare at least one field"
  return (fStxs, exampleStxs, rejectStxs, invStxs)

private def parseDataHeader (kindLow : String) (t : Ident) (ctxStx itemsStx : Syntax) (whereArgIdx : Nat) :
    CommandElabM ParsedDataHeader := do
  let (cbns, cbts) ← parseCtxBinders ctxStx
  let (fStxs, exampleStxs, rejectStxs, invStxs) ← splitDataItems kindLow t itemsStx.getArgs
  let fs : Array Ident := fStxs.map (⟨·[0]⟩)
  let whereRawExprs := fStxs.map fun f => if (f.getArg whereArgIdx).getNumArgs == 2 then ((f.getArg whereArgIdx).getArg 1).getSepArgs else #[]
  let whereLabels := whereRawExprs.map (fmtWhereLabel · "constraint")
  let whereClauses ← whereRawExprs.mapM fun ws => ws.mapM fun w => liftMacroM (Qed.Lang.lowerSimpleQedExpr .propInv w)
  return { cbns, cbts, fStxs, exampleStxs, rejectStxs, invStxs, fs, whereRawExprs, whereLabels, whereClauses }

@[noinline]
private def elabSchemaInvDef? (t : Ident) (hdr : ParsedDataHeader) (resolved : Array ResolvedField) (isPrivate : Bool := false) :
    CommandElabM (Option SchemaInvInfo) := do
  if hdr.invStxs.isEmpty then return none
  let mut rawPreds : Array Syntax := #[]
  for ist in hdr.invStxs do rawPreds := rawPreds ++ (ist.getArg 3).getSepArgs
  let invLabel := fmtWhereLabel rawPreds "invariant"
  let lowered ← rawPreds.mapM fun w => liftMacroM (Qed.Lang.lowerSimpleQedExpr .propInv w)
  let invBody ← Qed.mkConjBody lowered (ascribeProp := false)
  let invId := mkIdentFrom t (t.getId ++ `Inv)
  let (cbns, cbts, fs, valTys) := (hdr.cbns, hdr.cbts, hdr.fs, resolved.map (·.valTy))
  Qed.Lang.elabCmdWithVis isPrivate (← `(command|
    set_option linter.unusedVariables false in
    @[simp] abbrev $invId $[($cbns:ident : $cbts:term)]* $[($fs:ident : $valTys:term)]* : Prop := $invBody))
  let fieldArgs ← (fs.zip resolved).mapM fun (f, rf) =>
    if rf.isRefined then `(($f:ident).val) else `($f:ident)
  let invAppInFs ← Qed.Lang.mkAppTerms ⟨invId.raw⟩ (cbns.map (⟨·.raw⟩) ++ fieldArgs)
  return some { invId, invAppInFs, invLabel }

private def mkSchemaCtx (kindName : String) (t : Ident) (hdr : ParsedDataHeader) (resolved : Array ResolvedField)
    (invInfo? : Option SchemaInvInfo := none) (isPrivate : Bool := false) : CommandElabM SchemaCtx := do
  return {
    kindName, t, cbns := hdr.cbns, cbts := hdr.cbts,
    tApp := ← Qed.Lang.mkAppTerms ⟨t.raw⟩ (hdr.cbns.map (⟨·.raw⟩)),
    fs := hdr.fs, inputs := resolved.map (·.input), valTys := resolved.map (·.valTy),
    preds := resolved.map (·.predTerm), refined := resolved.map (·.isRefined), whereLabels := hdr.whereLabels, invInfo?, isPrivate }

@[noinline]
private def mkDataCodecCmds (sc : SchemaCtx) (resolved : Array ResolvedField) (defaultMasks : Array Bool)
    (fieldSpecs : Array StructFieldSpec) : CommandElabM (Array (TSyntax `command)) := do
  let ctxBinders := sc.cbns.zip sc.cbts
  let invCheck? := sc.invInfo?.map fun info => (info.invAppInFs, s!"{sc.t.getId}: failed invariant ({info.invLabel})")
  let mut cmds := ← mkAutoDeriveCmds sc resolved defaultMasks
  if resolved.all (·.isBEq) then cmds := cmds ++ (← mkSchemaBeqCmds sc (resolved.all (·.isLawfulBEq)))
  if resolved.all (·.isJson) then
    cmds := cmds ++ (← mkStructJsonCmds sc.t fieldSpecs { ctxBinders, emitStringCodec := true, emitLawful := resolved.all (·.isLawful), invCheck? })
  if resolved.all (·.isProto) then
    cmds := cmds ++ (← mkStructProtoCmds sc.t fieldSpecs { ctxBinders, emitBytesCodec := true, emitLawful := resolved.all (·.isLawfulP), invCheck? })
  return cmds

@[noinline, command_elab schemaCmd] def elabSchemaCmd : CommandElab := fun stx => do
  let t : Ident := ⟨stx.getArg 1⟩; let tId := t.getId
  let hdr ← parseDataHeader "schema" t (stx.getArg 2) (stx.getArg 4) 3
  let rawSpecs ← hdr.fStxs.mapM fun f => liftMacroM (lowerSchemaFieldSpec (f.getArg 2))
  let resolved ← liftTermElabM (elabSchemaFieldsAux hdr.cbns hdr.cbts hdr.fs rawSpecs hdr.whereClauses)
  let invInfo? ← elabSchemaInvDef? t hdr resolved
  let sc ← mkSchemaCtx "Schema" t hdr resolved invInfo?
  let draftId := mkIdent (tId ++ `Draft)
  let draftFields ← hdr.fs.mapM fun f => return ({ ident := f, wireKey := f.getId.toString, valTy := ← `(String) } : StructFieldSpec)
  let schemaFields := (hdr.fs.zip resolved).map fun (f, rf) =>
    ({ ident := f, wireKey := f.getId.toString, valTy := rf.valTy, codecTerm? := if rf.isRefined then some rf.input else none } : StructFieldSpec)
  let fs := hdr.fs
  let cmds : Array (TSyntax `command) := #[
    ← `(command| structure $draftId where $[$fs:ident : String := ""]* deriving Inhabited, DecidableEq, Repr),
    ← `(command| def $(mkIdent (tId ++ `Draft ++ `empty)) : $draftId := {})] ++
    (← mkStructJsonCmds draftId draftFields { fixedDepthBound := some 1 }) ++ (← mkSchemaCoreCmds sc draftId) ++
    (← mkDataCodecCmds sc resolved (Array.replicate fs.size false) schemaFields)
  cmds.forM elabCommand
  checkSchemaSatAndExamples sc resolved hdr.whereRawExprs hdr.exampleStxs hdr.rejectStxs
  let fullSchema := (← getCurrNamespace) ++ tId
  modifyEnv fun env => schemaFormRegistry.addEntry env {
    fullName := fullSchema ++ `Form, formViewName := fullSchema ++ `formView, ctxBinders := hdr.cbns.map (·.getId.eraseMacroScopes) }

@[noinline, command_elab recordCmd] def elabRecordCmd : CommandElab := fun stx => do
  let doc? := extractOptDoc (stx.getArg 0)
  let isPrivate := (stx.getArg 1).getNumArgs == 1
  let t : Ident := ⟨stx.getArg 3⟩; let tId := t.getId
  let hdr ← parseDataHeader "record" t (stx.getArg 4) (stx.getArg 6) 4
  let rawTys ← hdr.fStxs.mapM fun f => liftMacroM (return (← Qed.Lang.lowerQedType (f.getArg 2) false).1)
  let rawDefStxs : Array (Option Syntax) := hdr.fStxs.map fun f => if (f.getArg 3).getNumArgs == 2 then some ((f.getArg 3).getArg 1) else none
  let resolved ← liftTermElabM (elabRecordFieldsAux hdr.cbns hdr.cbts hdr.fs rawTys hdr.whereClauses)
  let invInfo? ← elabSchemaInvDef? t hdr resolved isPrivate
  let sc ← mkSchemaCtx "Record" t hdr resolved invInfo? isPrivate
  let (_, pfTac) ← mkSchemaRefinementTacs
  let mut binders : Array (TSyntax ``Lean.Parser.Command.structExplicitBinder) := #[]
  let mut fieldSpecs : Array StructFieldSpec := #[]
  let mut rawDefTerms : Array (Option Term) := #[]
  for i in [0:hdr.fs.size] do
    let f := hdr.fs[i]!; let rf := resolved[i]!; let fieldTy ← if rf.isRefined then `(Qed.Field $(rf.predTerm)) else pure rf.valTy
    fieldSpecs := fieldSpecs.push { ident := f, wireKey := f.getId.toString, valTy := fieldTy }
    match rawDefStxs[i]! with
    | none =>
        rawDefTerms := rawDefTerms.push none
        binders := binders.push (← `(Lean.Parser.Command.structExplicitBinder| ($f:ident : $fieldTy)))
    | some dStx =>
        let defT ← liftMacroM (Qed.Lang.lowerSimpleQedExpr .val dStx)
        rawDefTerms := rawDefTerms.push (some defT)
        let finalDef ← if !rf.isRefined then pure defT else do
          if hdr.cbns.isEmpty then
            unless ← tryCheckPropWithTactic (← `($(rf.predTerm) $defT)) pfTac do
              let valStr := let s := Qed.Lang.stxSnippet dStx; if s.isEmpty then "<default>" else s
              throwErrorAt dStx m!"Record `{tId}` default for field `{f.getId}` failed `where` constraint:\n  • value `{valStr}` does not satisfy `{hdr.whereLabels[i]!}`"
          `(Qed.Field.mk (p := $(rf.predTerm)) $defT (by $pfTac:tactic))
        binders := binders.push (← `(Lean.Parser.Command.structExplicitBinder| ($f:ident : $fieldTy := $finalDef)))
  if let some info := invInfo? then
    let allDefs := rawDefTerms.filterMap id
    if allDefs.size == hdr.fs.size && hdr.cbns.isEmpty then
      let invGoal ← Qed.Lang.mkAppTerms ⟨info.invId.raw⟩ allDefs
      if ← tryCheckPropWithTactic invGoal pfTac then
        binders := binders.push (← `(Lean.Parser.Command.structExplicitBinder| (_inv : $(info.invAppInFs) := by $pfTac:tactic)))
      else
        binders := binders.push (← `(Lean.Parser.Command.structExplicitBinder| (_inv : $(info.invAppInFs))))
    else
      binders := binders.push (← `(Lean.Parser.Command.structExplicitBinder| (_inv : $(info.invAppInFs))))
  let (cbns, cbts) := (hdr.cbns, hdr.cbts)
  let cmds := #[← `(command| $[$doc?:docComment]? structure $t $[($cbns:ident : $cbts:term)]* where $[$binders:structExplicitBinder]*)] ++
    (← mkDataCodecCmds sc resolved (rawDefStxs.map Option.isSome) fieldSpecs)
  cmds.forM (Qed.Lang.elabCmdWithVis isPrivate)
  if sc.refined.any id || !hdr.exampleStxs.isEmpty || !hdr.rejectStxs.isEmpty || invInfo?.isSome then
    checkSchemaSatAndExamples sc resolved hdr.whereRawExprs hdr.exampleStxs hdr.rejectStxs

@[noinline]
private def mkUnitEnumCmds (t : Ident) (variants : Array ParsedEnumVariant) : CommandElabM (Array (TSyntax `command)) := do
  let tId := t.getId
  let toStrAlts ← variants.mapM fun v =>
    `(Lean.Parser.Term.matchAltExpr| | $(mkIdent (tId ++ v.ident.getId)) => $(Syntax.mkStrLit v.wireName))
  let ofStrAlts ← variants.mapM fun v =>
    `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkStrLit v.wireName) => Except.ok $(mkIdent (tId ++ v.ident.getId)))
  let ofStrAlts := ofStrAlts.push (← `(Lean.Parser.Term.matchAltExpr| | other => Except.error ($(Syntax.mkStrLit s!"invalid {tId} '") ++ other ++ "'")))
  let toProtoAlts ← variants.zipIdx.mapM fun (v, i) =>
    `(Lean.Parser.Term.matchAltExpr| | $(mkIdent (tId ++ v.ident.getId)) => Qed.Proto.WireVal.varint $(Syntax.mkNumLit (toString i)))
  let fromProtoAlts ← variants.zipIdx.mapM fun (v, i) =>
    `(Lean.Parser.Term.matchAltExpr| | Qed.Proto.WireVal.varint $(Syntax.mkNumLit (toString i)) => Except.ok $(mkIdent (tId ++ v.ident.getId)))
  let fromProtoAlts := fromProtoAlts ++ #[
    ← `(Lean.Parser.Term.matchAltExpr| | Qed.Proto.WireVal.varint n => Except.error ($(Syntax.mkStrLit s!"protobuf: invalid {tId} tag ") ++ toString n)),
    ← `(Lean.Parser.Term.matchAltExpr| | _ => Except.error $(Syntax.mkStrLit s!"protobuf: expected varint for {tId}"))]
  let (toStrId, ofStrId, rtId) := (mkIdent (tId ++ `toString), mkIdent (tId ++ `ofString), mkIdent (tId ++ `ofString_toString))
  let (toJsonId, fromJsonId) := (mkIdent (tId ++ `toJson), mkIdent (tId ++ `fromJson))
  pure #[
    ← `(command| def $toStrId : $t → String $[$toStrAlts:matchAlt]*),
    ← `(command| def $ofStrId : String → Except String $t $[$ofStrAlts:matchAlt]*),
    ← `(command| instance $(mkIdent (tId ++ `instToString)):ident : ToString $t := ⟨$toStrId⟩),
    ← `(command| instance $(mkIdent (tId ++ `instStringEnum)):ident : Qed.StringEnum $t := ⟨$toStrId, $ofStrId⟩),
    ← `(command| @[simp] theorem $rtId (x : $t) : $ofStrId ($toStrId x) = Except.ok x := by cases x <;> rfl),
    ← `(command| instance $(mkIdent (tId ++ `instRouteParam)):ident : Qed.RouteParam $t where
          toSeg := $toStrId
          fromSeg s := ($ofStrId s).toOption
          round_trip x := by simp only [$rtId:ident, Except.toOption]),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulKey)):ident : Qed.LawfulKey $t := .ofRouteParam),
    ← `(command| def $toJsonId (x : $t) : Qed.Json := Qed.Json.str ($toStrId x)),
    ← `(command| def $fromJsonId : Qed.Json → Except String $t | Qed.Json.str s => $ofStrId s | _ => Except.error $(Syntax.mkStrLit s!"expected {tId} string")),
    ← `(command| def $(mkIdent (tId ++ `encode)) (x : $t) : String := Qed.Json.render ($toJsonId x)),
    ← `(command| def $(mkIdent (tId ++ `decode)) (s : String) (maxDepth : Nat := 64) : Except String $t := (Qed.Json.parse s maxDepth).bind $fromJsonId),
    ← `(command| instance $(mkIdent (tId ++ `instToJson)):ident : Qed.ToJson $t := ⟨$toJsonId⟩),
    ← `(command| instance $(mkIdent (tId ++ `instFromJson)):ident : Qed.FromJson $t := ⟨$fromJsonId⟩),
    ← `(command| instance $(mkIdent (tId ++ `instNonNullJson)):ident : Qed.NonNullJson $t := ⟨fun _ => nofun⟩),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulJson)):ident : Qed.LawfulJson $t where fromJson_toJson x := by cases x <;> rfl),
    ← `(command| instance $(mkIdent (tId ++ `instToProto)):ident : Qed.ToProto $t where toProtoVal $[$toProtoAlts:matchAlt]*),
    ← `(command| instance $(mkIdent (tId ++ `instFromProto)):ident : Qed.FromProto $t where fromProtoVal $[$fromProtoAlts:matchAlt]*),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulProto)):ident : Qed.LawfulProto $t := .ofScalar (by intro x; cases x <;> rfl)),
    ← `(command| def $(mkIdent (tId ++ `encodeBytes)) (x : $t) : Qed.Bytes := Qed.Proto.encode x),
    ← `(command| def $(mkIdent (tId ++ `decodeBytes)) (b : Qed.Bytes) : Except String $t := Qed.Proto.decode b)]

private def mkPayloadEnumJsonCmds (t : Ident) (variants : Array ParsedEnumVariant) (emitLawful : Bool) : CommandElabM (Array (TSyntax `command)) :=
  let allPNames := variants.flatMap fun v => v.params.map (·.1.getId.toString)
  Qed.mkTaggedUnionJsonCmds t
    (variants.map fun v => { ctorName := v.ident.getId, wireTag := v.wireName, fields := v.params.map fun (pId, pTy) => (pId, pId.getId.toString, pTy) })
    { tagKey := if allPNames.contains "t" then "_qed_tag" else "t", emitStringCodec := true, emitNonNull := true, emitLawful }

@[noinline]
private def mkPayloadEnumProtoCmds (t : Ident) (variants : Array ParsedEnumVariant) (emitLawful : Bool) : CommandElabM (Array (TSyntax `command)) := do
  let tId := t.getId; let (toId, fromId, fsId, tagId) := (mkIdent (tId ++ `toProtoFields), mkIdent (tId ++ `fromProtoFields), mkIdent `fs, mkIdent `_tag)
  let mut toAlts : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
  let mut fromAlts : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
  let mut tagPosCases : Array (TSyntax ``Lean.Parser.Tactic.inductionAlt) := #[]
  let mut rtCases : Array (TSyntax ``Lean.Parser.Tactic.inductionAlt) := #[]
  for (v, vi) in variants.zipIdx do
    let vName := v.ident.getId; let ctorId := mkIdent (tId ++ vName); let pIds := v.params.map (·.1)
    let pTerms : Array Term := pIds.map (⟨·.raw⟩)
    let viLit := Syntax.mkNumLit (toString vi)
    let allReads : Array Term := #[← `(($viLit : Nat))] ++ pTerms
    let allSpecs : Array StructFieldSpec := #[{ ident := tagId, wireKey := "t", valTy := ← `(Nat) }] ++
      v.params.map fun (pId, pTy) => { ident := pId, wireKey := pId.getId.toString, valTy := pTy }
    let (tails, tagsPosPf) ← mkProtoFieldTailsAndTags allReads emitLawful
    toAlts := toAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $ctorId $pTerms* => $(tails[0]!)))
    let decs ← v.params.zipIdx.mapM fun ((_, pTy), pi) =>
      `(Qed.FromProtoField.decodeProtoField (α := $pTy) $(Syntax.mkNumLit (toString (pi + 2))) $fsId)
    let ctorApp ← Qed.Lang.mkAppTerms ctorId pTerms
    let armDo ← if pIds.isEmpty then `(Except.ok $ctorApp) else `(do
      $[let $pIds:ident ← $decs:term]*
      return $ctorApp)
    fromAlts := fromAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $viLit => $armDo))
    if emitLawful then
      let (pIdents, pHaveTacs) ← mkProtoFieldRoundtripTacs allSpecs allReads tails none
      let roundtripPf ← pIdents.foldrM (init := ← `(term| rfl)) fun hp acc => `(term| Qed.exceptBind_eq $hp $acc)
      tagPosCases := tagPosCases.push (← `(Lean.Parser.Tactic.inductionAlt| | $(mkIdent vName):ident $[$pIds:ident]* => exact $tagsPosPf))
      rtCases := rtCases.push (← `(Lean.Parser.Tactic.inductionAlt| | $(mkIdent vName):ident $[$pIds:ident]* =>
        $[$pHaveTacs:tactic]*; unfold $fromId $toId; exact $roundtripPf))
  fromAlts := fromAlts.push (← `(Lean.Parser.Term.matchAltExpr| | n => Except.error ($(Syntax.mkStrLit s!"protobuf: invalid {tId} tag ") ++ toString n)))
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| def $toId : $t → List (Nat × Qed.Proto.WireVal) $[$toAlts:matchAlt]*),
    ← `(command| def $fromId ($fsId:ident : List (Nat × Qed.Proto.WireVal)) : Except String $t :=
          (Qed.FromProtoField.decodeProtoField (α := Nat) 1 $fsId).bind fun $tagId:ident => match $tagId:ident with $[$fromAlts:matchAlt]*),
    ← `(command| def $(mkIdent (tId ++ `encodeBytes)) (x : $t) : Qed.Bytes := Qed.Proto.encodeFieldsSpec ($toId x)),
    ← `(command| def $(mkIdent (tId ++ `decodeBytes)) (b : Qed.Bytes) : Except String $t := (Qed.Proto.decodeFieldsSpec b).bind $fromId),
    ← `(command| instance $(mkIdent (tId ++ `instToProto)):ident : Qed.ToProto $t := .ofFields $toId),
    ← `(command| instance $(mkIdent (tId ++ `instFromProto)):ident : Qed.FromProto $t := .ofFields $fromId)]
  if !emitLawful then return cmds
  let (tagsId, rtId) := (mkIdent (tId ++ `_proto_tags_pos), mkIdent (tId ++ `_fromProto_toProto))
  return cmds ++ #[
    ← `(command| private theorem $tagsId (x : $t) : ∀ kw ∈ $toId x, 0 < kw.1 := by cases x with $[$tagPosCases:inductionAlt]*),
    ← `(command| private theorem $rtId (x : $t) : $fromId ($toId x) = Except.ok x := by cases x with $[$rtCases:inductionAlt]*),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulProto)):ident : Qed.LawfulProto $t := .ofFields $toId $fromId $tagsId $rtId)]

@[noinline, command_elab enumCmd] def elabEnumCmd : CommandElab := fun stx => do
  let doc? := extractOptDoc (stx.getArg 0)
  let isPrivate := (stx.getArg 1).getNumArgs == 1
  let t : Ident := ⟨stx.getArg 3⟩; let tId := t.getId
  let rawVariants := (stx.getArg 5).getArgs
  if rawVariants.isEmpty then throwErrorAt t s!"`enum {tId}` must declare at least one variant"
  let mut variants : Array ParsedEnumVariant := #[]; let mut seenV : Std.HashSet Name := {}; let mut seenWire : Std.HashSet String := {}
  for vStx in rawVariants do
    let vId : Ident := ⟨vStx.getArg 0⟩; let vNm := vId.getId.eraseMacroScopes
    if seenV.contains vNm then throwErrorAt vId s!"duplicate variant `{vNm}` in `enum {tId}`"
    seenV := seenV.insert vNm
    let optP := vStx.getArg 1
    let mut params : Array (Ident × Term) := #[]; let mut seenP : Std.HashSet Name := {}
    if optP.getNumArgs == 3 then
      for pStx in (optP.getArg 1).getSepArgs do
        let pId : Ident := ⟨pStx.getArg 0⟩; let pNm := pId.getId.eraseMacroScopes
        if seenP.contains pNm then throwErrorAt pId s!"duplicate field `{pNm}` in variant `{vNm}` of `enum {tId}`"
        seenP := seenP.insert pNm
        params := params.push (pId, ← liftMacroM (return (← Qed.Lang.lowerQedType (pStx.getArg 2) false).1))
    let optWire := vStx.getArg 2
    let wireName := if optWire.getNumArgs == 2 then (⟨optWire.getArg 1⟩ : TSyntax `str).getString else vNm.toString
    if seenWire.contains wireName then
      throwErrorAt (if optWire.getNumArgs == 2 then optWire.getArg 1 else vId.raw) s!"duplicate wire name `{wireName}` in `enum {tId}`"
    seenWire := seenWire.insert wireName
    variants := variants.push { ident := vId, params, wireName }
  let isUnit := variants.all (·.params.isEmpty)
  let ctors ← variants.mapM fun v => do
    let pIds := v.params.map (·.1); let pTys := v.params.map (·.2)
    `(Lean.Parser.Command.ctor| | $(v.ident):ident $[($pIds:ident : $pTys:term)]*)
  Qed.Lang.elabCmdWithVis isPrivate (← `(command| $[$doc?:docComment]? inductive $t where $[$ctors:ctor]*))
  let (allJson, allLawfulJ, allProto, allLawfulP, allDecEq, allRepr, firstInhab) ← liftTermElabM do
    let mut (aJ, aLJ, aP, aLP, aDE, aR, fI) := (true, true, true, true, true, true, true)
    for (v, vi) in variants.zipIdx do
      for (_, pTy) in v.params do
        let ty ← elabType pTy
        let (isJ, isLJ, isP, isLP, _, _, hI, hR) ← probeTypeTraits ty
        let hDE ← probeInst ``DecidableEq ty
        aJ := aJ && isJ; aLJ := aLJ && isLJ; aP := aP && isP; aLP := aLP && isLP
        aDE := aDE && hDE; aR := aR && hR
        if vi == 0 then fI := fI && hI
    return (aJ, aLJ, aP, aLP, aDE, aR, fI)
  let mut cmds : Array (TSyntax `command) := #[]
  if allRepr then cmds := cmds.push (← `(command| deriving instance Repr for $t))
  if allDecEq then
    cmds := cmds ++ #[
      ← `(command| deriving instance DecidableEq for $t),
      ← `(command| instance $(mkIdent (tId ++ `instBEq)):ident : BEq $t := ⟨fun a b => decide (a = b)⟩),
      ← `(command| instance $(mkIdent (tId ++ `instLawfulBEq)):ident : LawfulBEq $t where eq_of_beq h := of_decide_eq_true h; rfl := decide_eq_true rfl)]
  if firstInhab then
    let v0 := variants[0]!
    let defArgs ← v0.params.mapM fun (_, pTy) => `((default : $pTy))
    let defVal ← Qed.Lang.mkAppTerms (mkIdent (tId ++ v0.ident.getId)) defArgs
    cmds := cmds.push (← `(command| instance (priority := low) $(mkIdent (tId ++ `instInhabited)):ident : Inhabited $t := ⟨$defVal⟩))
  if isUnit then
    cmds := cmds ++ (← mkUnitEnumCmds t variants)
  else
    if allJson then cmds := cmds ++ (← mkPayloadEnumJsonCmds t variants allLawfulJ)
    if allProto then cmds := cmds ++ (← mkPayloadEnumProtoCmds t variants allLawfulP)
  cmds.forM (Qed.Lang.elabCmdWithVis isPrivate)
  if isUnit then
    let baseNm := (← getCurrNamespace) ++ tId
    let env ← getEnv
    let fullEnum := if isPrivate then mkPrivateName env baseNm else baseNm
    modifyEnv fun env => unitEnumRegistry.addEntry env { fullName := fullEnum, variants := variants.map (·.wireName) }

@[noinline, command_elab constCmd] def elabConstCmd : CommandElab := fun stx => do
  let doc? := extractOptDoc (stx.getArg 0)
  let isPrivate := (stx.getArg 1).getNumArgs == 1
  let cId : Ident := ⟨stx.getArg 3⟩
  let tyOpt := stx.getArg 4
  let rhsT ← liftMacroM (Qed.Lang.lowerSimpleQedExpr .val (stx.getArg 6))
  let cmd ← if tyOpt.getNumArgs == 2 then
      let tyT ← liftMacroM (return (← Qed.Lang.lowerQedType (tyOpt.getArg 1) false).1)
      `(command| $[$doc?:docComment]? def $cId : $tyT := $rhsT)
    else
      `(command| $[$doc?:docComment]? def $cId := $rhsT)
  Qed.Lang.elabCmdWithVis isPrivate cmd

@[noinline, command_elab fieldCmd] def elabFieldCmd : CommandElab := fun stx => do
  let doc? := extractOptDoc (stx.getArg 0)
  let t : Ident := ⟨stx.getArg 2⟩; let tId := t.getId
  let (cbns, cbts) ← parseCtxBinders (stx.getArg 3)
  let rawTy ← liftMacroM (return (← Qed.Lang.lowerQedType (stx.getArg 5) false).1)
  let vId : Ident := ⟨stx.getArg 7⟩
  let rawWheres := (stx.getArg 9).getSepArgs
  let whereLabel := fmtWhereLabel rawWheres "constraint"
  let wherePreds ← rawWheres.mapM fun w => liftMacroM (Qed.Lang.lowerSimpleQedExpr .propInv w)
  let predBody ← mkConjBody wherePreds
  let predTerm : Term ← `(fun $vId:ident : $rawTy => $predBody)
  let (tyName, hasInhab) ← liftTermElabM <| withCtxDecls cbns cbts do
    let α ← elabType rawTy
    discard <| checkRefinementDecidable "field" t α predTerm
    return (((← whnf α).constName?.getD .anonymous), ← probeInst ``Inhabited α)
  let validId := mkIdentFrom t (tId ++ `Valid)
  let tApp ← Qed.Lang.mkAppTerms ⟨t.raw⟩ (cbns.map (⟨·.raw⟩))
  let validApp ← Qed.Lang.mkAppTerms ⟨validId.raw⟩ (cbns.map (⟨·.raw⟩))
  elabCommand (← `(command| abbrev $validId $[($cbns:ident : $cbts:term)]* ($vId:ident : $rawTy) : Prop := $predBody))
  let validCId := mkCIdent ((← getCurrNamespace) ++ tId ++ `Valid)
  let parseErrLit := Syntax.mkStrLit s!"invalid {tId}: failed constraint `{whereLabel}`"
  let cmds : Array (TSyntax `command) := #[
    ← `(command| $[$doc?:docComment]? abbrev $t $[($cbns:ident : $cbts:term)]* : Type := Qed.Field ($validApp)),
    ← `(command| @[inline] abbrev $(mkIdentFrom t (tId ++ `make)) $[($cbns:ident : $cbts:term)]* ($vId:ident : $rawTy)
          (ok : $validApp $vId := by (try dsimp only [$validCId:ident]) <;> first | rfl | decide | omega | (simp_all; try rfl; try decide; try omega)) : $tApp :=
          Qed.Field.mk $vId ok),
    ← `(command| @[inline] def $(mkIdentFrom t (tId ++ `parse?)) $[($cbns:ident : $cbts:term)]* ($vId:ident : $rawTy) : Option ($tApp) :=
          Qed.Field.parse? ($validApp) $vId),
    ← `(command| @[inline] def $(mkIdentFrom t (tId ++ `parse)) $[($cbns:ident : $cbts:term)]* ($vId:ident : $rawTy) : Except String ($tApp) :=
          Qed.Field.parse ($validApp) $parseErrLit $vId)
  ]
  cmds.forM elabCommand
  if cbns.isEmpty then
    let (simpTac, pfTac) ← mkSchemaRefinementTacs
    checkFieldUnsat t rawTy predTerm simpTac
      m!"Field `{tId}` is unsatisfiable: contradictory `where` constraints (`{whereLabel}`) -- no value can ever satisfy it.\n\nHint: Fix or remove the conflicting `where` conditions on `{tId}`."
    let rf : ResolvedField := .mk rawTy rawTy predTerm true false false false false false false tyName hasInhab false
    if let some witness ← synthesizeFieldWitness? pfTac rf rawWheres then
      emitSatisfiableCmdsRaw false t cbns cbts tApp t witness

end SchemaElab

end Qed
