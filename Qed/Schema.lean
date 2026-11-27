import Qed.Schema.Codec
import Qed.Schema.Registry
import Qed.Verify.Core

namespace Qed

section SchemaParsers
open Lean Parser Qed.Lang
private abbrev pType : Parser := withPosition (categoryParser `qedType 0)
private abbrev pExpr : Parser := categoryParser `qedExpr 0
private def schemaCtxOpt : Parser := optional (checkLineEq >> "(" >> sepBy1 schemaCtxParamP "," >> ")")
private def schemaFieldJsonOnly : Parser := node `Qed.schemaFieldJsonOnly (atomic (identEq `jsonOnly >> checkNoWsBefore "" >> "(") >> pType >> ")")
private def schemaFieldCall     : Parser := node `Qed.schemaFieldCall (atomic (ident >> checkNoWsBefore "" >> "(") >> sepBy (categoryParser `qedCallArg 0) "," >> ")")
private def schemaFieldSpec     : Parser := schemaFieldJsonOnly <|> schemaFieldCall <|> pType
private def schemaFieldP        : Parser := node `Qed.schemaField (withPosition (ident >> ":" >> schemaFieldSpec >> optional (checkColGt >> " where " >> sepBy1 pExpr ",")))
private def schemaExampleFieldP : Parser := node `Qed.schemaExampleField (checkColGt >> ident >> "=" >> pExpr)
private def schemaExampleP      : Parser := node `Qed.schemaExample (withPosition (atomic (symbol "example" >> ident >> ":") >> sepBy1 schemaExampleFieldP ","))
private def schemaRejectsP      : Parser := node `Qed.schemaRejects (withPosition (atomic (identEq `rejects >> ident >> ":") >> sepBy1 schemaExampleFieldP ","))
private def schemaInvP          : Parser := node `Qed.schemaInv (withPosition (atomic (symbol "invariant" >> ident >> ":") >> sepBy1 pExpr ","))
private def schemaItemP         : Parser := schemaExampleP <|> schemaRejectsP <|> schemaInvP <|> schemaFieldP
@[command_parser] def schemaCmd : Parser := opaqueP (node `Qed.schemaCmd (withPosition
  ("schema " >> ident >> schemaCtxOpt >> ":" >> checkColGt "expected indented `schema` fields" >> many1Indent schemaItemP)))
private def recordFieldP : Parser := node `Qed.recordField (withPosition (
  ident >> ":" >> pType >> optional (checkLineEq >> "=" >> pExpr) >> optional (checkColGt >> " where " >> sepBy1 pExpr ",")))
private def recordItemP : Parser := schemaExampleP <|> schemaRejectsP <|> schemaInvP <|> recordFieldP
@[command_parser] def recordCmd : Parser := opaqueP (node `Qed.recordCmd (
  optional Command.docComment >> withPosition (
    atomic (optional (symbol "private") >> identEq `record) >> ident >> schemaCtxOpt >> ":" >>
    checkColGt "expected indented `record` fields" >> many1Indent recordItemP)))
private def enumParamP   : Parser := node `Qed.enumParam (ident >> ":" >> pType)
private def enumVariantP : Parser := node `Qed.enumVariant (withPosition (
  ident >> optional (checkNoWsBefore "" >> "(" >> sepBy1 enumParamP "," >> ")") >> optional (checkLineEq >> "=" >> strLit)))
@[command_parser] def enumCmd : Parser := opaqueP (node `Qed.enumCmd (
  optional Command.docComment >> withPosition (
    atomic (optional (symbol "private") >> identEq `enum) >> ident >> ":" >> checkColGt "expected indented `enum` variants" >> many1Indent enumVariantP)))
@[command_parser] def constCmd : Parser := opaqueP (node `Qed.constCmd (
  optional Command.docComment >>
  atomic (optional (symbol "private") >> identEq `const >> ident) >> optional (":" >> pType) >> "=" >> pExpr))
@[command_parser] def fieldCmd : Parser := opaqueP (node `Qed.fieldCmd (
  optional Command.docComment >> withPosition (
    atomic (identEq `field) >> ident >> schemaCtxOpt >>
    ":" >> pType >> checkColGt >> symbol "where" >> ident >> "=>" >> sepBy1 pExpr ",")))
macro "qedProveField " id:ident : tactic =>
  `(tactic| (try dsimp only [$id:ident]) <;> first | rfl | decide | omega | (simp_all; try rfl; try decide; try omega))
end SchemaParsers

section SchemaElab
open Lean Elab Command Term Meta Qed.Lang

private def lowerSchemaFieldSpec (stx : Syntax) : MacroM Term := match stx.getKind with
  | `Qed.schemaFieldJsonOnly => do let t := (← lowerQedType (stx.getArg 2) false).1; runPQMacro `(jsonOnly $t)
  | `Qed.schemaFieldCall     => do let args ← (stx.getArg 2).getSepArgs.mapM fun a => lowerSimpleQedExpr .val (a.getArg 0); runPQMacro (mkAppTermsPure ⟨stx.getArg 0⟩ args)
  | _                        => do return (← lowerQedType stx false).1

private def primSchemaTypes : Array (Name × Name) :=
  #[(``String, ``Qed.Codec.text), (``Nat, ``Qed.Codec.nat), (``Int, ``Qed.Codec.int), (``Bool, ``Qed.Codec.checkbox), (``Qed.Date, ``Qed.Codec.date)]

private def extractOptDoc (optDoc : Syntax) : Option (TSyntax ``Lean.Parser.Command.docComment) :=
  if optDoc.getNumArgs == 1 then some ⟨optDoc.getArg 0⟩ else none

@[noinline] private partial def resolveCodecBase (qctx : PureQuotCtx) (fieldName : Name) (rawSpec : Term) : TermElabM (Term × Option Term) := do
  if let `($fn:ident $arg:term) := rawSpec then
    if fn.getId.eraseMacroScopes == `jsonOnly then
      let (base, ty?) ← resolveCodecBase qctx fieldName arg
      return (qctx.runPure `(Qed.Codec.jsonOnly $base), ty?)
  let scopedSpec := qctx.runPure `(open Qed.Codec in $rawSpec)
  let e ← elabTermAndSynthesize scopedSpec none; let ety ← whnf (← instantiateMVars (← inferType e))
  if ety.isAppOfArity ``Qed.Codec 1 then return (scopedSpec, none)
  else if ety.isSort then
    let eWhnf ← whnf (← instantiateMVars e)
    if let some (_, codecNm) := primSchemaTypes.find? (eWhnf.isConstOf ·.1) then return (mkCIdent codecNm, some rawSpec)
    if (← trySynthInstance (← mkAppM ``Qed.DefaultCodec #[e])) matches .some _ then return (qctx.runPure `((Qed.DefaultCodec.codec : Qed.Codec $rawSpec)), some rawSpec)
    throwErrorAt rawSpec m!"schema field `{fieldName}` has type `{rawSpec}`, which has no default `Codec` or JSON (`ToJson`/`FromJson`) instances.\nProvide a `DefaultCodec` or JSON instances for `{rawSpec}`, or use a supported field type (`String`, `Nat`, `Int`, `Bool`, `Date`, `select([...])`, `textarea`, `jsonOnly(...)`)."
  else throwErrorAt rawSpec m!"schema field `{fieldName}` must be a type (`String`, `Nat`, `Int`, `Bool`, `Date`, …) or a `Codec` (e.g. `select([...])`, `textarea`, `jsonOnly(String)`), but this has type{indentExpr ety}"

private structure ResolvedField where mk ::
  (input valTy predTerm : Term)
  (isRefined isJson isLawful isProto isLawfulP isBEq isLawfulBEq : Bool)
  (tyName : Name) (hasInhab hasRepr : Bool)
deriving Inhabited

private structure SchemaInvInfo where mk :: (invId : Ident) (invAppInFs : Term) (invLabel : String)

private structure SchemaCtx where mk ::
  (kindName : String) (t : Ident) (cbns : Array Ident) (cbts : Array Term) (tApp : Term)
  (fs : Array Ident) (inputs valTys preds : Array Term)
  (refined : Array Bool) (whereLabels : Array String)
  (invInfo? : Option SchemaInvInfo := none) (isPrivate : Bool := false)

private structure ParsedDataHeader where mk ::
  (cbns : Array Ident) (cbts : Array Term) (fStxs exampleStxs rejectStxs invStxs : Array Syntax)
  (fs : Array Ident) (whereRawExprs : Array (Array Syntax)) (whereLabels : Array String) (whereClauses : Array (Array Term))

private structure ParsedEnumVariant where mk :: (ident : Ident) (params : Array (Ident × Term)) (wireName : String) deriving Inhabited

private def SchemaCtx.appToPure (sc : SchemaCtx) (head : Term) : PureQuotM Term := mkAppTermsPure head (sc.cbns.map (⟨·.raw⟩))

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
  return (isJson, isLawful, isProto, isLawfulP, hasBEq.1, hasBEq.2, ← probeInst ``Inhabited ty, ← probeInst ``Repr ty)

private def checkDecPredErrors (kindName : String) (f : Ident) (inp : Term) (savedLog : MessageLog) (preCount : Nat) : TermElabM Unit := do
  if ← ((← Core.getMessageLog).toList.drop preCount).anyM fun msg => return ((← msg.data.toString).splitOn "DecidablePred").length > 1 then
    Core.setMessageLog savedLog
    throwErrorAt inp m!"{kindName} field `{f.getId}` has a refinement that isn't decidable, so validity can't be computed (no `DecidablePred` for it).\n\nThe usual cause is a predicate written with `def`. Write it inline with `where …` or as an `abbrev`, so Lean sees it reduces to a decidable check:\n    abbrev MyPredicate (x : …) : Prop := …\nIf it genuinely can't be decided, give it a `DecidablePred` instance."

private def checkRefinementDecidable (kindName : String) (ref : Ident) (α : Expr) (predTerm : Term) : TermElabM Expr := do
  let savedLog ← Core.getMessageLog; let preCount := savedLog.toList.length
  let predE ← elabTermEnsuringType predTerm (some (← mkArrow α (mkSort Level.zero)))
  unless (← trySynthInstance (← mkAppM ``DecidablePred #[predE])) matches .some _ do
    checkDecPredErrors kindName ref predTerm savedLog preCount
    let subject := if kindName == "field" then s!"field `{ref.getId}`" else s!"{kindName} field `{ref.getId}`"
    throwErrorAt predTerm m!"{subject} has a refinement that isn't decidable (no `DecidablePred` for it).\n\nWrite it inline with `where ...` or as an `abbrev`, or provide a `DecidablePred` instance."
  return predE

private def mkResolvedField (input valTy predTerm : Term) (isRefined : Bool) (α fieldTy : Expr) (checkBaseInhab : Bool := false) : TermElabM ResolvedField := do
  let (isJson, isLawful, isProto, isLawfulP, isBEq, isLawfulBEq, hasInhab0, hasRepr) ← probeTypeTraits fieldTy
  let hasInhab ← if checkBaseInhab && isRefined then probeInst ``Inhabited α else pure hasInhab0
  return .mk input valTy predTerm isRefined isJson isLawful isProto isLawfulP isBEq isLawfulBEq ((← whnf α).constName?.getD .anonymous) hasInhab hasRepr

@[noinline] private def elabDataFieldsAux (qctx : PureQuotCtx) (isSchema : Bool) (cbns : Array Ident) (cbts : Array Term)
    (fs : Array Ident) (rawSpecs : Array Term) (whereClauses : Array (Array Term)) : TermElabM (Array ResolvedField) :=
  withCtxDecls cbns cbts do
    mapArrM ((fs.zip rawSpecs).zip whereClauses) fun ((f, rawSpec), preds) => do
      if isSchema then
        let (base, directTy?) ← resolveCodecBase qctx f.getId rawSpec
        let inp : Term := if preds.isEmpty then base else qctx.runPure do `(Qed.Codec.refine $base (fun $f:ident => $(← mkConjBody preds)))
        let savedLog ← Core.getMessageLog; let preCount := savedLog.toList.length
        let c ← elabTermAndSynthesize inp none
        checkDecPredErrors "schema" f inp savedLog preCount
        match (← instantiateMVars (← inferType c)).getAppFnArgs with
        | (``Qed.Codec, #[α]) =>
            let isRefined := !(← isDefEq (mkApp2 (mkConst ``Qed.Codec.valid) α c) (Expr.lam `x α (mkConst ``True) .default))
            let valTy ← match directTy? with | some dt => pure dt | none => try PrettyPrinter.delab α catch _ => pure (qctx.runPure `(Qed.Codec.Val $inp))
            mkResolvedField inp valTy (qctx.runPure `(($inp).valid)) isRefined α α
        | _ => throwErrorAt rawSpec m!"failed to resolve schema field `{f.getId}` to a `Codec`"
      else
        let α ← elabType rawSpec; let isRefined := !preds.isEmpty
        let predTerm := qctx.runPure do if isRefined then `(fun $f:ident : $rawSpec => $(← mkConjBody preds)) else `(fun (_ : $rawSpec) => True)
        let fieldTy ← if isRefined then mkAppM ``Qed.Field #[← checkRefinementDecidable "record" f α predTerm] else pure α
        mkResolvedField rawSpec rawSpec predTerm isRefined α fieldTy (checkBaseInhab := true)

@[noinline] private def mkSchemaBeqCmdsPure (sc : SchemaCtx) (allLawfulBEq : Bool) : PureQuotM (Array (TSyntax `command)) := do
  let (tId, cbns, cbts, tApp, fs) := (sc.t.getId, sc.cbns, sc.cbts, sc.tApp, sc.fs)
  let beqFnId := mkIdent (tId ++ `beq); let beqApp ← sc.appToPure ⟨beqFnId.raw⟩
  let beqExpr ← if fs.isEmpty then `(true) else
    Lang.foldlPQ (fs.extract 1 fs.size) (← `(a.$(fs[0]!):ident == b.$(fs[0]!):ident)) fun acc fi => `($acc && (a.$fi:ident == b.$fi:ident))
  let defCmd ← `(command| def $beqFnId $[($cbns:ident : $cbts:term)]* (a b : $tApp) : Bool := $beqExpr)
  if !allLawfulBEq then return #[defCmd, ← `(command| instance $(mkIdent (tId ++ `instBEq)):ident $[($cbns:ident : $cbts:term)]* : BEq $tApp := ⟨$beqApp⟩)]
  let bcId := mkIdent (tId ++ `_beqCodec); let bcApp ← sc.appToPure ⟨bcId.raw⟩
  return #[defCmd,
    ← `(command| private def $bcId $[($cbns:ident : $cbts:term)]* : Qed.StructBeqCodec $tApp where
          beq := $beqApp
          eq_of_beq {a b} h := by cases a; cases b; dsimp only [$beqFnId:ident] at h; simp only [Bool.and_eq_true, beq_iff_eq] at h; simp_all only
          beq_rfl {a} := by cases a; dsimp only [$beqFnId:ident]; simp only [beq_self_eq_true, Bool.and_self]),
    ← `(command| instance $(mkIdent (tId ++ `instBEq)):ident $[($cbns:ident : $cbts:term)]* : BEq $tApp := ($bcApp).instBEq),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulBEq)):ident $[($cbns:ident : $cbts:term)]* : LawfulBEq $tApp := ($bcApp).instLawfulBEq),
    ← `(command| instance (priority := low) $(mkIdent (tId ++ `instDecidableEq)):ident $[($cbns:ident : $cbts:term)]* : DecidableEq $tApp := ($bcApp).instDecidableEq)]

@[noinline] private def mkAutoDeriveCmdsPure (sc : SchemaCtx) (resolved : Array ResolvedField) (defaultMasks : Array Bool) : PureQuotM (Array (TSyntax `command)) := do
  let mut out : Array (TSyntax `command) := #[]
  if sc.cbns.isEmpty && resolved.all (·.hasRepr) then out := out.push (← `(command| deriving instance Repr for $(sc.t)))
  if sc.cbns.isEmpty && sc.invInfo?.isNone && (resolved.zip defaultMasks).all fun (rf, hasDef) => hasDef || (!rf.isRefined && rf.hasInhab) then
    let inits ← Lang.foldlPQ ((sc.fs.zip resolved).zip defaultMasks) (#[] : Array (TSyntax ``Lean.Parser.Term.structInstField)) fun acc ((f, rf), hasDef) =>
      if hasDef then pure acc else do return acc.push (← `(Lean.Parser.Term.structInstField| $f:ident := (default : $(rf.valTy))))
    out := out.push (← `(command| instance (priority := low) $(mkIdent (sc.t.getId ++ `instInhabited)):ident : Inhabited $(sc.t) := ⟨{ $[$inits:structInstField],* }⟩))
  return out

@[noinline] private def mkSchemaCoreCmdsPure (sc : SchemaCtx) (draftId : Ident) : PureQuotM (Array (TSyntax `command)) := do
  let (t, tId, cbns, cbts, tApp, fs) := (sc.t, sc.t.getId, sc.cbns, sc.cbts, sc.tApp, sc.fs); let pairs := fs.zip sc.inputs
  let structTys ← Lang.mapPQ ((sc.valTys.zip sc.preds).zip sc.refined) fun ((vt, pr), r) => if r then `(Field $pr) else pure vt
  let runCalls ← Lang.mapPQ (pairs.zip sc.refined) fun ((f, inp), r) => if r then `(($inp).run (d.$f:ident)) else `(($inp).parse (d.$f:ident))
  let (parseId, canId, viewId) := (mkIdent (tId ++ `parse), mkIdent (tId ++ `canSubmit), mkIdent (tId ++ `formView))
  let (parseApp, canApp, viewApp) := (← sc.appToPure ⟨parseId.raw⟩, ← sc.appToPure ⟨canId.raw⟩, ← sc.appToPure ⟨viewId.raw⟩)
  let rhs ← mkConjBody (← Lang.mapPQ runCalls fun rc => `(($rc).isSome)) (ascribeProp := false)
  let n := runCalls.size
  let pf ← Lang.foldrPQ (runCalls.extract 0 (n - 1)) (← `(term| Qed.optionBind_pure_isSome_iff $(runCalls[n - 1]!) _)) fun rc acc =>
    `(term| Qed.optionBind_isSome_iff $rc _ (fun _ => $acc))
  let canSubmitPf ← if n ≤ 2 then pure pf else do
    let reassoc ← Lang.foldlPQ (Array.range (n - 2)) (← `(term| Iff.rfl)) fun acc _ => `(term| and_assoc.symm.trans $acc)
    `(term| Iff.trans $pf $reassoc)
  let rowGroups ← Lang.mapPQ (pairs.zip runCalls) fun ((f, inp), rc) =>
    `(term| ($inp).renderFieldRow (d.$f:ident) ($rc).isNone $(Syntax.mkStrLit (toString f.getId))
              $(Syntax.mkStrLit ("Please enter a valid " ++ toString f.getId)) (fun v => onEdit { d with $f:ident := v }))
  let viewBody ← Lang.foldrPQ rowGroups (← `(term| [Codec.submitBtn ($parseApp d) submit])) fun g acc => `(term| $g ++ $acc)
  let validBodyPf ← Lang.foldrPQ sc.inputs (← `(term| Codec.submitBtn_validIn inForm ($parseApp d) submit)) fun _ acc => `(term| Codec.renderFieldRowCons_validIn inForm _ _ _ _ _ _ _ $acc)
  let (structCmd, parseBody, canSubmitCmd) ← match sc.invInfo? with
    | none => pure (
        ← `(command| structure $t $[($cbns:ident : $cbts:term)]* where $[$fs:ident : $structTys]*),
        ← `(do $[let $fs:ident ← $runCalls:term]* return { $[$fs:ident],* }),
        ← `(command| theorem $(mkIdent (tId ++ `canSubmit_iff)) $[($cbns:ident : $cbts:term)]* (d : $draftId) : $canApp d = true ↔ $rhs := by unfold $canId $parseId; exact $canSubmitPf))
    | some info => pure (
        ← `(command| structure $t $[($cbns:ident : $cbts:term)]* where $[$fs:ident : $structTys]* (_inv : $(info.invAppInFs))),
        ← `(do $[let $fs:ident ← $runCalls:term]* if _hInv : $(info.invAppInFs) then return { $[$fs:ident],*, _inv := _hInv } else none),
        ← `(command| theorem $(mkIdent (tId ++ `canSubmit_iff)) $[($cbns:ident : $cbts:term)]* (d : $draftId) : $canApp d = true ↔ ∃ _x : $tApp, $parseApp d = some _x := Option.isSome_iff_exists))
  return #[structCmd,
    ← `(command| def $parseId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Option $tApp := $parseBody),
    ← `(command| def $canId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Bool := ($parseApp d).isSome),
    canSubmitCmd,
    ← `(command| def $viewId {msg : Type} $[($cbns:ident : $cbts:term)]* (d : $draftId) (onEdit : $draftId → msg) (submit : $tApp → msg) : Html msg := el "div" [cls "qed-form"] $viewBody),
    ← `(command| @[simp] theorem $(mkIdent (tId ++ `formView_validIn)) {msg : Type} $[($cbns:ident : $cbts:term)]* (inForm : Bool) (d : $draftId) (onEdit : $draftId → msg) (submit : $tApp → msg) :
          Html.validIn ⟨.normal, false, false, inForm⟩ ($viewApp d onEdit submit) = true := Codec.formDiv_validIn inForm _ $validBodyPf)]

private partial def collectStxLits {α : Type} [BEq α] (extract : Syntax → Option α) (stx : Syntax) (acc : Array α) : Array α :=
  stx.getArgs.foldl (fun a ch => collectStxLits extract ch a) (match extract stx with | some v => pushUnique acc v | none => acc)

private def tryCheckPropWithTactic (goalTerm : Term) (tacStx : TSyntax `tactic) : CommandElabM Bool :=
  Qed.Diag.probeTermElabOk do
    discard <| elabTermEnsuringType (← `(by $tacStx:tactic)) (← elabType goalTerm); synthesizeSyntheticMVarsNoPostponing; return true

@[noinline] private def mkSchemaRefinementTacsPure : PureQuotM (TSyntax `tactic × TSyntax `tactic) := do
  let simpTac ← `(tactic| simp only [Qed.Codec.valid, Qed.Codec.refine, Qed.Codec.jsonOnly, Qed.Codec.text, Qed.Codec.textarea,
      Qed.Codec.nat, Qed.Codec.int, Qed.Codec.checkbox, Qed.Codec.date, Qed.Codec.select, Qed.Codec.radios, Qed.Codec.json, Qed.Lang.QedVal.val_id])
  let pfTac ← `(tactic| ((try $simpTac:tactic) <;> first | qedCloseGround | rfl | decide | omega | trivial | (simp_all; try qedCloseGround; try rfl; try decide; try omega)))
  return (simpTac, pfTac)

@[noinline] private def mkWitnessCandsPure (rf : ResolvedField) (rawWheres : Array Syntax) : PureQuotM (Array Term) := do
  let nats := (rawWheres.foldl (fun acc w => collectStxLits (fun s => if s.getKind == ``qedLitNum then some (⟨s.getArg 0⟩ : TSyntax `num).getNat else none) w acc) #[]).toList
  match rf.tyName with
  | ``Bool => return #[← `((Bool.true : Bool)), ← `((Bool.false : Bool))]
  | ``Nat  => Lang.mapPQ ((nats.flatMap fun n => [n, n + 1, n - 1]) ++ [0, 1, 2, 3, 5, 10, 18, 21, 50, 100]).eraseDups.toArray fun k => `(($(quote k) : Nat))
  | ``Int  => Lang.mapPQ ((nats.flatMap fun n => let z : Int := Int.ofNat n; [z, z + 1, z - 1, -z, -z - 1, -z + 1]) ++ [(0 : Int), 1, -1, 2, 10, 100]).eraseDups.toArray fun k =>
      if k >= 0 then `(($(quote k.toNat) : Int)) else `((-($(quote (-k).toNat) : Int)))
  | ``String =>
      let strs := (rawWheres.foldl (fun acc w => collectStxLits (fun s => if s.getKind == ``qedLitStr then some (⟨s.getArg 0⟩ : TSyntax `str).getString else none) w acc) #[]).toList
      let lens := nats.flatMap fun n => (if n > 0 && n ≤ 64 then [String.ofList (List.replicate n 'a')] else []) ++ (if n + 1 ≤ 64 then [String.ofList (List.replicate (n + 1) 'a')] else [])
      Lang.mapPQ (strs ++ ["", "a", "alice", "a@b.com", "https://example.com", "12345678", "aaaaaaaaaa"] ++ lens).eraseDups.toArray fun s => `(($(quote s) : String))
  | ``Qed.Date => return #[← `(({ year := 2026, month := 1, day := 1 } : Qed.Date))]
  | _          => if rf.hasInhab then return #[← `((default : $(rf.valTy)))] else return #[]

@[noinline] private def synthesizeFieldWitness? (pfTac : TSyntax `tactic) (rf : ResolvedField) (rawWheres : Array Syntax) : CommandElabM (Option Term) := do
  if !rf.isRefined then if rf.hasInhab then return some (← Lang.runPQ `((default : $(rf.valTy)))) else return none
  for cand in (← Lang.runPQ (mkWitnessCandsPure rf rawWheres)) do
    if ← tryCheckPropWithTactic (← Lang.runPQ `($(rf.predTerm) $cand)) pfTac then
      return some (← Lang.runPQ `(Qed.Field.mk (p := $(rf.predTerm)) $cand (by $pfTac:tactic)))
  return none

@[noinline] private def emitSatisfiableCmdsRaw (isPrivate : Bool) (t : Ident) (cbns : Array Ident) (cbts : Array Term) (tApp : Term)
    (ref : Syntax) (witness : Term) : CommandElabM Unit := do
  let cmds ← Lang.runPQ do
    let mut cs := #[← `(command| theorem $(mkIdentFrom ref (t.getId ++ `satisfiable)) $[($cbns:ident : $cbts:term)]* : ∃ _x : $tApp, True := ⟨$witness, trivial⟩)]
    if cbns.isEmpty then cs := cs.push (← `(command| instance $(mkIdentFrom ref (t.getId ++ `instNonempty)):ident : Nonempty $t := ⟨$witness⟩))
    return cs
  Lang.foldlCmd cmds () fun _ c => elabCmdWithVis isPrivate c

private def checkFieldUnsat (ref : Syntax) (valTy predTerm : Term) (simpTac : TSyntax `tactic) (errMsg : MessageData) : CommandElabM Unit := do
  let (goalT, tac) ← Lang.runPQ do
    return (← `(∀ _qed_x : $valTy, ¬ $predTerm _qed_x),
            ← `(tactic| (intro _qed_x; (try $simpTac:tactic) <;> first | omega | decide | (cases _qed_x <;> decide))))
  if ← tryCheckPropWithTactic goalT tac then throwErrorAt ref errMsg

private def mkCheckedFieldVal (isRefined checkNow : Bool) (predTerm valTerm : Term) (valStx : Syntax) (pfTac : TSyntax `tactic)
    (errMsg : String → MessageData) : CommandElabM Term := do
  if !isRefined then return valTerm
  if checkNow then
    unless ← tryCheckPropWithTactic (← Lang.runPQ `($predTerm $valTerm)) pfTac do
      throwErrorAt valStx (errMsg (stxSnippet valStx))
  Lang.runPQ `(Qed.Field.mk (p := $predTerm) $valTerm (by $pfTac:tactic))

private def parseSchemaFieldAssigns (sc : SchemaCtx) (clauseKind : String) (stx : Syntax) : CommandElabM (Ident × Array (Syntax × Term)) := do
  let (tId, fs) := (sc.t.getId, sc.fs); let nameId : Ident := ⟨stx.getArg 1⟩; let nm := nameId.getId
  let validNames := fs.toList.map (·.getId.toString); let mut provided : Std.HashMap String Syntax := {}
  for entry in (stx.getArg 3).getSepArgs do
    let fid : Ident := ⟨entry.getArg 0⟩; let fName := fid.getId.toString
    unless validNames.contains fName do
      throwErrorAt fid s!"{sc.kindName} `{tId}` {clauseKind} `{nm}`: unknown field `{fName}`{Qed.Diag.didYouMean fName validNames} (expected: {String.intercalate ", " validNames})"
    if provided.contains fName then throwErrorAt fid s!"{sc.kindName} `{tId}` {clauseKind} `{nm}`: duplicate field `{fName}`"
    provided := provided.insert fName (entry.getArg 2)
  let vals ← Lang.mapCmd fs fun f => do
    let fName := f.getId.toString
    let some valStx := provided[fName]? | throwErrorAt stx s!"{sc.kindName} `{tId}` {clauseKind} `{nm}`: missing required field `{fName}`"
    return (valStx, ← liftMacroM (lowerSimpleQedExpr .val valStx))
  return (nameId, vals)

@[noinline] private def elabSchemaExampleClause (sc : SchemaCtx) (pfTac : TSyntax `tactic) (exStx : Syntax) (emitSatisfiable : Bool) : CommandElabM Unit := do
  let (tId, cbns, cbts, tApp, fs) := (sc.t.getId, sc.cbns, sc.cbts, sc.tApp, sc.fs)
  let (exName, rawVals) ← parseSchemaFieldAssigns sc "example" exStx; let exId := exName.getId
  let fieldTerms ← Lang.mapCmd (fs.zip rawVals).zipIdx fun ((f, (valStx, valTerm)), i) =>
    mkCheckedFieldVal sc.refined[i]! cbns.isEmpty sc.preds[i]! valTerm valStx pfTac fun s =>
      let valStr := if s.isEmpty then "<value>" else s
      m!"{sc.kindName} `{tId}` example `{exId}` failed `where` constraint on field `{f.getId}`:\n  • value `{valStr}` does not satisfy `{sc.whereLabels[i]!}`\n\nHint: Update `{f.getId}` in example `{exId}` so it satisfies `{sc.whereLabels[i]!}`, or weaken the `where` rule."
  let sampleId := mkIdentFrom exName (tId ++ exId)
  if let some info := sc.invInfo? then
    if cbns.isEmpty then
      let invGoal ← Lang.runPQ (mkAppTermsPure ⟨info.invId.raw⟩ (cbns.map (⟨·.raw⟩) ++ rawVals.map (·.2)))
      unless ← tryCheckPropWithTactic invGoal pfTac do
        throwErrorAt exStx m!"{sc.kindName} `{tId}` example `{exId}` failed `invariant`:\n  • values do not satisfy `{info.invLabel}`\n\nHint: Update example `{exId}` so it satisfies `{info.invLabel}`, or weaken the `invariant`."
  let sampleCmd ← Lang.runPQ do
    match sc.invInfo? with
    | none   => `(command| def $sampleId $[($cbns:ident : $cbts:term)]* : $tApp := { $[$fs:ident := $fieldTerms:term],* })
    | some _ => `(command| def $sampleId $[($cbns:ident : $cbts:term)]* : $tApp := { $[$fs:ident := $fieldTerms:term],*, _inv := by $pfTac:tactic })
  elabCmdWithVis sc.isPrivate sampleCmd
  if emitSatisfiable then emitSatisfiableCmdsRaw sc.isPrivate sc.t sc.cbns sc.cbts sc.tApp exStx (← Lang.runPQ (sc.appToPure ⟨sampleId.raw⟩))

@[noinline] private def elabSchemaRejectsClause (sc : SchemaCtx) (simpTac : TSyntax `tactic) (rejStx : Syntax) : CommandElabM Unit := do
  let (tId, cbns, cbts) := (sc.t.getId, sc.cbns, sc.cbts)
  let (rejName, rawVals) ← parseSchemaFieldAssigns sc "rejects" rejStx; let rejId := rejName.getId
  let (negGoal, negTac, hasChecks) ← Lang.runPQ do
    let mut checks ← Lang.foldlPQ (Array.range sc.fs.size) (#[] : Array Term) fun acc i =>
      if sc.refined[i]! then do return acc.push (← `($(sc.preds[i]!) $(rawVals[i]!.2))) else pure acc
    if let some info := sc.invInfo? then checks := checks.push (← mkAppTermsPure ⟨info.invId.raw⟩ (cbns.map (⟨·.raw⟩) ++ rawVals.map (·.2)))
    if checks.isEmpty then return (← `(False), ← `(tactic| trivial), false)
    let negGoal ← `(¬ ($(← mkConjBody checks (ascribeProp := false))))
    let negTac ← `(tactic| ((try $simpTac:tactic) <;> first | qedCloseGround | decide | omega | (intro _h; simp_all; try omega; try qedCloseGround; try decide)))
    return (negGoal, negTac, true)
  unless hasChecks do throwErrorAt rejStx s!"{sc.kindName} `{tId}` `rejects {rejId}` requires at least one `where` or `invariant` constraint"
  if cbns.isEmpty then
    unless ← tryCheckPropWithTactic negGoal negTac do
      throwErrorAt rejStx m!"{sc.kindName} `{tId}` `rejects {rejId}` failed: the provided values unexpectedly satisfy all `where` and `invariant` constraints.\n\nHint: Strengthen the `where`/`invariant` rules or fix the negative test case `{rejId}`."
  let thmId := mkIdentFrom rejName (tId ++ (Name.mkSimple s!"rejects_{rejId}"))
  elabCmdWithVis sc.isPrivate (← Lang.runPQ `(command| theorem $thmId $[($cbns:ident : $cbts:term)]* : $negGoal := by $negTac:tactic))

@[noinline] private def checkSchemaSatAndExamples (sc : SchemaCtx) (resolved : Array ResolvedField)
    (whereRawExprs : Array (Array Syntax)) (exampleStxs rejectStxs : Array Syntax) : CommandElabM Unit := do
  let (simpTac, pfTac) ← Lang.runPQ mkSchemaRefinementTacsPure
  if !exampleStxs.isEmpty then
    Lang.foldlCmd exampleStxs.zipIdx () fun _ (exStx, idx) => elabSchemaExampleClause sc pfTac exStx (idx == 0)
  else if sc.cbns.isEmpty && sc.invInfo?.isNone then
    Lang.foldlCmd resolved.zipIdx () fun _ (rf, i) => do
      if rf.isRefined then
        checkFieldUnsat sc.fs[i]! rf.valTy rf.predTerm simpTac
          m!"{sc.kindName} `{sc.t.getId}` is unsatisfiable: field `{sc.fs[i]!.getId}` has contradictory `where` constraints (`{sc.whereLabels[i]!}`) -- no value can ever satisfy it.\n\nHint: Fix or remove the conflicting `where` conditions on `{sc.fs[i]!.getId}`."
    if let some synthTerms ← Lang.foldlCmd resolved.zipIdx (some #[]) fun acc? (rf, i) => do
        let some arr := acc? | return none
        return (← synthesizeFieldWitness? pfTac rf whereRawExprs[i]!).map arr.push then
      let (fs, witId) := (sc.fs, mkIdentFrom sc.t (sc.t.getId ++ `_witness))
      Lang.elabPureCmd `(command| private def $witId : $(sc.t) := { $[$fs:ident := $synthTerms:term],* })
      emitSatisfiableCmdsRaw sc.isPrivate sc.t sc.cbns sc.cbts sc.tApp sc.t witId
  Lang.foldlCmd rejectStxs () fun _ rejStx => elabSchemaRejectsClause sc simpTac rejStx

private def parseDataHeader (kindLow : String) (t : Ident) (ctxStx itemsStx : Syntax) (whereArgIdx : Nat) : CommandElabM ParsedDataHeader := do
  let (cbns, cbts) ← parseCtxBinders ctxStx; let tId := t.getId
  let addUniq (label : String) (item : Syntax) (seen : Std.HashSet Name) (arr : Array Syntax) : CommandElabM (Std.HashSet Name × Array Syntax) := do
    let nm : Ident := ⟨item.getArg 1⟩
    if seen.contains nm.getId then throwErrorAt nm s!"duplicate {label} `{nm.getId}` in `{kindLow} {tId}`"
    return (seen.insert nm.getId, arr.push item)
  let mut (fStxs, exampleStxs, rejectStxs, invStxs) : Array Syntax × Array Syntax × Array Syntax × Array Syntax := (#[], #[], #[], #[])
  let mut (seenEx, seenRej, seenInv) : Std.HashSet Name × Std.HashSet Name × Std.HashSet Name := ({}, {}, {})
  for item in itemsStx.getArgs do
    match item.getKind with
    | `Qed.schemaExample => let (s, a) ← addUniq "example" item seenEx exampleStxs; seenEx := s; exampleStxs := a
    | `Qed.schemaRejects => let (s, a) ← addUniq "rejects" item seenRej rejectStxs; seenRej := s; rejectStxs := a
    | `Qed.schemaInv     => let (s, a) ← addUniq "invariant" item seenInv invStxs; seenInv := s; invStxs := a
    | _ => fStxs := fStxs.push item
  if fStxs.isEmpty then throwErrorAt t s!"`{kindLow} {tId}` must declare at least one field"
  let fs : Array Ident := fStxs.map (⟨·[0]⟩)
  let whereRawExprs := fStxs.map fun f => if (f.getArg whereArgIdx).getNumArgs == 2 then ((f.getArg whereArgIdx).getArg 1).getSepArgs else #[]
  let whereClauses ← Lang.mapCmd whereRawExprs fun ws => Lang.mapCmd ws fun w => liftMacroM (lowerSimpleQedExpr .propInv w)
  return { cbns, cbts, fStxs, exampleStxs, rejectStxs, invStxs, fs, whereRawExprs, whereLabels := whereRawExprs.map (fmtWhereLabel · "constraint"), whereClauses }

@[noinline] private def elabSchemaInvDef? (t : Ident) (hdr : ParsedDataHeader) (resolved : Array ResolvedField) (isPrivate : Bool := false) : CommandElabM (Option SchemaInvInfo) := do
  if hdr.invStxs.isEmpty then return none
  let rawPreds := hdr.invStxs.foldl (init := #[]) fun acc ist => acc ++ (ist.getArg 3).getSepArgs
  let lowered ← Lang.mapCmd rawPreds fun w => liftMacroM (lowerSimpleQedExpr .propInv w)
  let invId := mkIdentFrom t (t.getId ++ `Inv)
  let (cmd, invAppInFs) ← Lang.runPQ do
    let (cbns, cbts, fs, valTys) := (hdr.cbns, hdr.cbts, hdr.fs, resolved.map (·.valTy))
    let invBody ← mkConjBody lowered (ascribeProp := false)
    let cmd ← `(command| set_option linter.unusedVariables false in @[simp] abbrev $invId $[($cbns:ident : $cbts:term)]* $[($fs:ident : $valTys:term)]* : Prop := $invBody)
    let fieldArgs ← Lang.mapPQ (fs.zip resolved) fun (f, rf) => if rf.isRefined then `(($f:ident).val) else `($f:ident)
    return (cmd, ← mkAppTermsPure ⟨invId.raw⟩ (cbns.map (⟨·.raw⟩) ++ fieldArgs))
  elabCmdWithVis isPrivate cmd
  return some { invId, invAppInFs, invLabel := fmtWhereLabel rawPreds "invariant" }

@[noinline] private def mkDataCodecCmdsPure (sc : SchemaCtx) (resolved : Array ResolvedField) (defaultMasks : Array Bool)
    (fieldSpecs : Array StructFieldSpec) : PureQuotM (Array (TSyntax `command)) := do
  let ctxBinders := sc.cbns.zip sc.cbts
  let invCheck? := sc.invInfo?.map fun info => (info.invAppInFs, s!"{sc.t.getId}: failed invariant ({info.invLabel})")
  let mut cmds ← mkAutoDeriveCmdsPure sc resolved defaultMasks
  if resolved.all (·.isBEq) then cmds := cmds ++ (← mkSchemaBeqCmdsPure sc (resolved.all (·.isLawfulBEq)))
  if resolved.all (·.isJson) then cmds := cmds ++ (← mkStructJsonCmdsPure sc.t fieldSpecs { ctxBinders, emitStringCodec := true, emitLawful := resolved.all (·.isLawful), invCheck? })
  if resolved.all (·.isProto) then cmds := cmds ++ (← mkStructProtoCmdsPure sc.t fieldSpecs { ctxBinders, emitBytesCodec := true, emitLawful := resolved.all (·.isLawfulP), invCheck? })
  return cmds

@[noinline] private def elabDataCmd (isSchema : Bool) (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (isPrivate : Bool)
    (t : Ident) (ctxStx itemsStx : Syntax) : CommandElabM Unit := do
  let (tId, kindLow, kindName, whereIdx) := (t.getId, if isSchema then "schema" else "record", if isSchema then "Schema" else "Record", if isSchema then 3 else 4)
  let hdr ← parseDataHeader kindLow t ctxStx itemsStx whereIdx
  let qctx ← getPureQuotCtxCmd
  let rawSpecs ← Lang.mapCmd hdr.fStxs fun f =>
    if isSchema then liftMacroM (lowerSchemaFieldSpec (f.getArg 2)) else do return (← liftPureErr (lowerQedTypeInfoPure qctx (f.getArg 2) false)).term
  let resolved ← liftTermElabM (elabDataFieldsAux qctx isSchema hdr.cbns hdr.cbts hdr.fs rawSpecs hdr.whereClauses)
  let invInfo? ← elabSchemaInvDef? t hdr resolved isPrivate
  let sc : SchemaCtx := {
    kindName, t, cbns := hdr.cbns, cbts := hdr.cbts, tApp := qctx.runPure (mkAppTermsPure ⟨t.raw⟩ (hdr.cbns.map (⟨·.raw⟩))),
    fs := hdr.fs, inputs := resolved.map (·.input), valTys := resolved.map (·.valTy),
    preds := resolved.map (·.predTerm), refined := resolved.map (·.isRefined), whereLabels := hdr.whereLabels, invInfo?, isPrivate }
  let cmds ← if isSchema then Lang.runPQ do
    let (draftId, fs) := (mkIdent (tId ++ `Draft), hdr.fs)
    let draftFields ← Lang.mapPQ fs fun f => return ({ ident := f, wireKey := f.getId.toString, valTy := ← `(String) } : StructFieldSpec)
    let schemaFields := (fs.zip resolved).map fun (f, rf) =>
      ({ ident := f, wireKey := f.getId.toString, valTy := rf.valTy, codecTerm? := if rf.isRefined then some rf.input else none } : StructFieldSpec)
    return #[← `(command| structure $draftId where $[$fs:ident : String := ""]* deriving Inhabited, DecidableEq, Repr),
             ← `(command| def $(mkIdent (tId ++ `Draft ++ `empty)) : $draftId := {})] ++
      (← mkStructJsonCmdsPure draftId draftFields { fixedDepthBound := some 1 }) ++ (← mkSchemaCoreCmdsPure sc draftId) ++
      (← mkDataCodecCmdsPure sc resolved (Array.replicate fs.size false) schemaFields)
  else do
    let rawDefStxs := hdr.fStxs.map fun f => if (f.getArg 3).getNumArgs == 2 then some ((f.getArg 3).getArg 1) else none
    let (_, pfTac) := qctx.runPure mkSchemaRefinementTacsPure
    let (defTerms, finalDefs) ← Lang.foldlCmd (Array.range hdr.fs.size) (#[], #[]) fun (dts, fds) i => do
      let (f, rf) := (hdr.fs[i]!, resolved[i]!)
      match rawDefStxs[i]! with
      | none => return (dts.push none, fds.push none)
      | some dStx =>
          let defT ← liftMacroM (lowerSimpleQedExpr .val dStx)
          let checked ← mkCheckedFieldVal rf.isRefined hdr.cbns.isEmpty rf.predTerm defT dStx pfTac fun s =>
            m!"Record `{tId}` default for field `{f.getId}` failed `where` constraint:\n  • value `{if s.isEmpty then "<default>" else s}` does not satisfy `{hdr.whereLabels[i]!}`"
          return (dts.push (some defT), fds.push (some checked))
    let invHasDefault ← match sc.invInfo? with
      | some info =>
          let allDefs := defTerms.filterMap id
          if allDefs.size == hdr.fs.size && hdr.cbns.isEmpty then tryCheckPropWithTactic (qctx.runPure (mkAppTermsPure ⟨info.invId.raw⟩ allDefs)) pfTac else pure false
      | none => pure false
    Lang.runPQ do
      let (binders, fieldSpecs) ← Lang.foldlPQ (Array.range hdr.fs.size) ((#[] : Array (TSyntax ``Lean.Parser.Command.structExplicitBinder)), (#[] : Array StructFieldSpec)) fun (bs, sps) i => do
        let (f, rf) := (hdr.fs[i]!, resolved[i]!)
        let fieldTy ← if rf.isRefined then `(Qed.Field $(rf.predTerm)) else pure rf.valTy
        let b ← match finalDefs[i]! with
          | none => `(Lean.Parser.Command.structExplicitBinder| ($f:ident : $fieldTy))
          | some d => `(Lean.Parser.Command.structExplicitBinder| ($f:ident : $fieldTy := $d))
        return (bs.push b, sps.push { ident := f, wireKey := f.getId.toString, valTy := fieldTy })
      let binders ← match sc.invInfo? with
        | none => pure binders
        | some info => do
            let invB ← if invHasDefault then `(Lean.Parser.Command.structExplicitBinder| (_inv : $(info.invAppInFs) := by $pfTac:tactic))
              else `(Lean.Parser.Command.structExplicitBinder| (_inv : $(info.invAppInFs)))
            pure (binders.push invB)
      let (cbns, cbts) := (hdr.cbns, hdr.cbts)
      return #[← `(command| $[$doc?:docComment]? structure $t $[($cbns:ident : $cbts:term)]* where $[$binders:structExplicitBinder]*)] ++
        (← mkDataCodecCmdsPure sc resolved (rawDefStxs.map Option.isSome) fieldSpecs)
  Lang.foldlCmd cmds () fun _ c => elabCmdWithVis isPrivate c
  if isSchema || sc.refined.any id || !hdr.exampleStxs.isEmpty || !hdr.rejectStxs.isEmpty || sc.invInfo?.isSome then
    checkSchemaSatAndExamples sc resolved hdr.whereRawExprs hdr.exampleStxs hdr.rejectStxs
  if isSchema then
    let fullSchema := (← getCurrNamespace) ++ tId
    modifyEnv fun env => schemaFormRegistry.addEntry env {
      fullName := fullSchema ++ `Form, formViewName := fullSchema ++ `formView, ctxBinders := hdr.cbns.map (·.getId.eraseMacroScopes) }

@[noinline, command_elab schemaCmd] def elabSchemaCmd : CommandElab := fun stx =>
  elabDataCmd true none false ⟨stx.getArg 1⟩ (stx.getArg 2) (stx.getArg 4)
@[noinline, command_elab recordCmd] def elabRecordCmd : CommandElab := fun stx =>
  elabDataCmd false (extractOptDoc (stx.getArg 0)) ((stx.getArg 1).getNumArgs == 1) ⟨stx.getArg 3⟩ (stx.getArg 4) (stx.getArg 6)

@[noinline] private def mkPayloadVariantProtoPure (tId : Name) (toId fromId fsId tagId : Ident) (emitLawful : Bool) (v : ParsedEnumVariant) (vi : Nat) :
    PureQuotM (TSyntax ``Lean.Parser.Term.matchAltExpr × TSyntax ``Lean.Parser.Term.matchAltExpr × Option (TSyntax ``Lean.Parser.Tactic.inductionAlt × TSyntax ``Lean.Parser.Tactic.inductionAlt)) := do
  let vName := v.ident.getId; let ctorId := mkIdent (tId ++ vName); let pIds := v.params.map (·.1)
  let pTerms : Array Term := pIds.map (⟨·.raw⟩); let viLit := Syntax.mkNumLit (toString vi)
  let allReads : Array Term := #[← `(($viLit : Nat))] ++ pTerms
  let (tails, tagsPosPf) ← mkProtoFieldTailsAndTagsPure allReads emitLawful
  let toAlt ← `(Lean.Parser.Term.matchAltExpr| | $ctorId $pTerms* => $(tails[0]!))
  let decs ← Lang.mapIdxPQ v.params fun (_, pTy) pi => `(Qed.FromProtoField.decodeProtoField (α := $pTy) $(Syntax.mkNumLit (toString (pi + 2))) $fsId)
  let ctorApp ← mkAppTermsPure ctorId pTerms
  let armDo ← if pIds.isEmpty then `(Except.ok $ctorApp) else `(do $[let $pIds:ident ← $decs:term]* return $ctorApp)
  let fromAlt ← `(Lean.Parser.Term.matchAltExpr| | $viLit => $armDo)
  if !emitLawful then return (toAlt, fromAlt, none)
  let allSpecs : Array StructFieldSpec := #[{ ident := tagId, wireKey := "t", valTy := ← `(Nat) }] ++
    v.params.map fun (pId, pTy) => { ident := pId, wireKey := pId.getId.toString, valTy := pTy }
  let (pIdents, pHaveTacs) ← mkProtoFieldRoundtripTacsPure allSpecs allReads tails none
  let roundtripPf ← Lang.foldrPQ pIdents (← `(term| rfl)) fun hp acc => `(term| Qed.exceptBind_eq $hp $acc)
  let tagPosCase ← `(Lean.Parser.Tactic.inductionAlt| | $(mkIdent vName):ident $[$pIds:ident]* => exact $tagsPosPf)
  let rtCase ← `(Lean.Parser.Tactic.inductionAlt| | $(mkIdent vName):ident $[$pIds:ident]* => $[$pHaveTacs:tactic]*; unfold $fromId $toId; exact $roundtripPf)
  return (toAlt, fromAlt, some (tagPosCase, rtCase))

@[noinline] private def mkPayloadEnumProtoCmdsPure (t : Ident) (variants : Array ParsedEnumVariant) (emitLawful : Bool) : PureQuotM (Array (TSyntax `command)) := do
  let tId := t.getId; let (toId, fromId, fsId, tagId) := (mkIdent (tId ++ `toProtoFields), mkIdent (tId ++ `fromProtoFields), mkIdent `fs, mkIdent `_tag)
  let (toAlts, fromAlts0, tagPosCases, rtCases) ← Lang.foldlPQ variants.zipIdx (#[], #[], #[], #[]) fun (ts, fs, tps, rts) (v, vi) => do
    let (ta, fa, law?) ← mkPayloadVariantProtoPure tId toId fromId fsId tagId emitLawful v vi
    let (tps', rts') := match law? with | some (tp, rt) => (tps.push tp, rts.push rt) | none => (tps, rts)
    return (ts.push ta, fs.push fa, tps', rts')
  let fromAlts := fromAlts0.push (← `(Lean.Parser.Term.matchAltExpr| | n => Except.error ($(Syntax.mkStrLit s!"protobuf: invalid {tId} tag ") ++ toString n)))
  let cmds : Array (TSyntax `command) := #[
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

@[noinline] private def mkEnumPostCmdsPure (t : Ident) (variants : Array ParsedEnumVariant) (isUnit allJson allLawfulJ allProto allLawfulP allDecEq allRepr firstInhab : Bool) : PureQuotM (Array (TSyntax `command)) := do
  let tId := t.getId; let mut cmds : Array (TSyntax `command) := #[]
  if allRepr then cmds := cmds.push (← `(command| deriving instance Repr for $t))
  if allDecEq then cmds := cmds ++ #[
    ← `(command| deriving instance DecidableEq for $t),
    ← `(command| instance $(mkIdent (tId ++ `instBEq)):ident : BEq $t := ⟨fun a b => decide (a = b)⟩),
    ← `(command| instance $(mkIdent (tId ++ `instLawfulBEq)):ident : LawfulBEq $t where eq_of_beq h := of_decide_eq_true h; rfl := decide_eq_true rfl)]
  if firstInhab then
    let v0 := variants[0]!
    let defVal ← mkAppTermsPure (mkIdent (tId ++ v0.ident.getId)) (← Lang.mapPQ v0.params fun (_, pTy) => `((default : $pTy)))
    cmds := cmds.push (← `(command| instance (priority := low) $(mkIdent (tId ++ `instInhabited)):ident : Inhabited $t := ⟨$defVal⟩))
  if isUnit then
    cmds := cmds ++ (← mkUnitEnumCodecCmdsPure t (variants.map fun v => (v.ident.getId, v.wireName)))
  else
    if allJson then
      let allPNames := variants.flatMap fun v => v.params.map (·.1.getId.toString)
      cmds := cmds ++ (← mkTaggedUnionJsonCmdsPure t
        (variants.map fun v => { ctorName := v.ident.getId, wireTag := v.wireName, fields := v.params.map fun (pId, pTy) => (pId, pId.getId.toString, pTy) })
        { tagKey := if allPNames.contains "t" then "_qed_tag" else "t", emitStringCodec := true, emitNonNull := true, emitLawful := allLawfulJ })
    if allProto then cmds := cmds ++ (← mkPayloadEnumProtoCmdsPure t variants allLawfulP)
  return cmds

@[noinline, command_elab enumCmd] def elabEnumCmd : CommandElab := fun stx => do
  let doc? := extractOptDoc (stx.getArg 0); let isPrivate := (stx.getArg 1).getNumArgs == 1
  let t : Ident := ⟨stx.getArg 3⟩; let tId := t.getId; let rawVariants := (stx.getArg 5).getArgs
  if rawVariants.isEmpty then throwErrorAt t s!"`enum {tId}` must declare at least one variant"
  let qctx ← getPureQuotCtxCmd
  let (variants, _, _) ← Lang.foldlCmd rawVariants (#[], ({} : Std.HashSet Name), ({} : Std.HashSet String)) fun (vs, seenV, seenW) vStx => do
    let vId : Ident := ⟨vStx.getArg 0⟩; let vNm := vId.getId.eraseMacroScopes
    if seenV.contains vNm then throwErrorAt vId s!"duplicate variant `{vNm}` in `enum {tId}`"
    let rawPs := if (vStx.getArg 1).getNumArgs == 3 then ((vStx.getArg 1).getArg 1).getSepArgs else #[]
    let (params, _) ← Lang.foldlCmd rawPs (#[], ({} : Std.HashSet Name)) fun (ps, seenP) pStx => do
      let pId : Ident := ⟨pStx.getArg 0⟩; let pNm := pId.getId.eraseMacroScopes
      if seenP.contains pNm then throwErrorAt pId s!"duplicate field `{pNm}` in variant `{vNm}` of `enum {tId}`"
      return (ps.push (pId, (← liftPureErr (lowerQedTypeInfoPure qctx (pStx.getArg 2) false)).term), seenP.insert pNm)
    let optWire := vStx.getArg 2
    let wireName := if optWire.getNumArgs == 2 then (⟨optWire.getArg 1⟩ : TSyntax `str).getString else vNm.toString
    if seenW.contains wireName then
      throwErrorAt (if optWire.getNumArgs == 2 then optWire.getArg 1 else vId.raw) s!"duplicate wire name `{wireName}` in `enum {tId}`"
    return (vs.push { ident := vId, params, wireName }, seenV.insert vNm, seenW.insert wireName)
  let isUnit := variants.all (·.params.isEmpty)
  let indCmd ← Lang.runPQ do
    let ctors ← Lang.mapPQ variants fun v => let (pIds, pTys) := (v.params.map (·.1), v.params.map (·.2)); `(Lean.Parser.Command.ctor| | $(v.ident):ident $[($pIds:ident : $pTys:term)]*)
    `(command| $[$doc?:docComment]? inductive $t where $[$ctors:ctor]*)
  elabCmdWithVis isPrivate indCmd
  let (allJson, allLawfulJ, allProto, allLawfulP, allDecEq, allRepr, firstInhab) ← liftTermElabM do
    let mut (aJ, aLJ, aP, aLP, aDE, aR, fI) := (true, true, true, true, true, true, true)
    for (v, vi) in variants.zipIdx do
      for (_, pTy) in v.params do
        let ty ← elabType pTy; let (isJ, isLJ, isP, isLP, _, _, hI, hR) ← probeTypeTraits ty
        aJ := aJ && isJ; aLJ := aLJ && isLJ; aP := aP && isP; aLP := aLP && isLP
        if aDE then aDE ← probeInst ``DecidableEq ty
        aR := aR && hR
        if vi == 0 then fI := fI && hI
    return (aJ, aLJ, aP, aLP, aDE, aR, fI)
  Lang.foldlCmd (← Lang.runPQ (mkEnumPostCmdsPure t variants isUnit allJson allLawfulJ allProto allLawfulP allDecEq allRepr firstInhab)) () fun _ c => elabCmdWithVis isPrivate c
  if isUnit then
    let baseNm := (← getCurrNamespace) ++ tId
    modifyEnv fun env => unitEnumRegistry.addEntry env { fullName := if isPrivate then mkPrivateName env baseNm else baseNm, variants := variants.map (·.wireName) }

@[noinline, command_elab constCmd] def elabConstCmd : CommandElab := fun stx => do
  let doc? := extractOptDoc (stx.getArg 0); let isPrivate := (stx.getArg 1).getNumArgs == 1
  let cId : Ident := ⟨stx.getArg 3⟩; let tyOpt := stx.getArg 4
  let rhsT ← liftMacroM (lowerSimpleQedExpr .val (stx.getArg 6))
  let qctx ← getPureQuotCtxCmd
  let tyT? ← if tyOpt.getNumArgs == 2 then pure (some (← liftPureErr (lowerQedTypeInfoPure qctx (tyOpt.getArg 1) false)).term) else pure none
  elabCmdWithVis isPrivate (qctx.runPure do match tyT? with
    | some tyT => `(command| $[$doc?:docComment]? def $cId : $tyT := $rhsT)
    | none     => `(command| $[$doc?:docComment]? def $cId := $rhsT))

@[noinline] private def mkFieldCmdsPure (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (t vId : Ident)
    (cbns : Array Ident) (cbts : Array Term) (rawTy predBody : Term) (currNs : Name) (whereLabel : String) : PureQuotM (Term × TSyntax `command × Array (TSyntax `command)) := do
  let tId := t.getId; let validId := mkIdentFrom t (tId ++ `Valid)
  let (tApp, validApp) := (← mkAppTermsPure ⟨t.raw⟩ (cbns.map (⟨·.raw⟩)), ← mkAppTermsPure ⟨validId.raw⟩ (cbns.map (⟨·.raw⟩)))
  let validCmd ← `(command| abbrev $validId $[($cbns:ident : $cbts:term)]* ($vId:ident : $rawTy) : Prop := $predBody)
  let (validCId, parseErrLit) := (mkCIdent (currNs ++ tId ++ `Valid), Syntax.mkStrLit s!"invalid {tId}: failed constraint `{whereLabel}`")
  return (tApp, validCmd, #[
    ← `(command| $[$doc?:docComment]? abbrev $t $[($cbns:ident : $cbts:term)]* : Type := Qed.Field ($validApp)),
    ← `(command| @[inline] abbrev $(mkIdentFrom t (tId ++ `make)) $[($cbns:ident : $cbts:term)]* ($vId:ident : $rawTy)
          (ok : $validApp $vId := by qedProveField $validCId) : $tApp := Qed.Field.mk $vId ok),
    ← `(command| @[inline] def $(mkIdentFrom t (tId ++ `parse?)) $[($cbns:ident : $cbts:term)]* ($vId:ident : $rawTy) : Option ($tApp) := Qed.Field.parse? ($validApp) $vId),
    ← `(command| @[inline] def $(mkIdentFrom t (tId ++ `parse)) $[($cbns:ident : $cbts:term)]* ($vId:ident : $rawTy) : Except String ($tApp) := Qed.Field.parse ($validApp) $parseErrLit $vId)])

@[noinline, command_elab fieldCmd] def elabFieldCmd : CommandElab := fun stx => do
  let doc? := extractOptDoc (stx.getArg 0); let t : Ident := ⟨stx.getArg 2⟩; let tId := t.getId
  let (cbns, cbts) ← parseCtxBinders (stx.getArg 3)
  let qctx ← getPureQuotCtxCmd
  let rawTy := (← liftPureErr (lowerQedTypeInfoPure qctx (stx.getArg 5) false)).term
  let vId : Ident := ⟨stx.getArg 7⟩; let rawWheres := (stx.getArg 9).getSepArgs
  let whereLabel := fmtWhereLabel rawWheres "constraint"
  let wherePreds ← Lang.mapCmd rawWheres fun w => liftMacroM (lowerSimpleQedExpr .propInv w)
  let (predBody, predTerm) := qctx.runPure do let b ← mkConjBody wherePreds; return (b, ← `(fun $vId:ident : $rawTy => $b))
  let (tyName, hasInhab) ← liftTermElabM <| withCtxDecls cbns cbts do
    let α ← elabType rawTy; discard <| checkRefinementDecidable "field" t α predTerm
    return (((← whnf α).constName?.getD .anonymous), ← probeInst ``Inhabited α)
  let (tApp, validCmd, cmds) := qctx.runPure (mkFieldCmdsPure doc? t vId cbns cbts rawTy predBody (← getCurrNamespace) whereLabel)
  elabCommand validCmd; Lang.foldlCmd cmds () fun _ c => elabCommand c
  if cbns.isEmpty then
    let (simpTac, pfTac) := qctx.runPure mkSchemaRefinementTacsPure
    checkFieldUnsat t rawTy predTerm simpTac
      m!"Field `{tId}` is unsatisfiable: contradictory `where` constraints (`{whereLabel}`) -- no value can ever satisfy it.\n\nHint: Fix or remove the conflicting `where` conditions on `{tId}`."
    let rf : ResolvedField := .mk rawTy rawTy predTerm true false false false false false false tyName hasInhab false
    if let some witness ← synthesizeFieldWitness? pfTac rf rawWheres then emitSatisfiableCmdsRaw false t cbns cbts tApp t witness

end SchemaElab
end Qed
