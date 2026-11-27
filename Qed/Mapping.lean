import Qed.Schema.Codec
import Qed.Schema.Registry
import Qed.Base64
import Qed.Verify.Core

namespace Qed

/-! ## Verified Bidirectional `mapping` Command (`Mapping` Surface DSL) -/

section MappingParsers
open Lean Parser Qed.Lang

declare_syntax_cat mapClause
private abbrev mpType : Parser := withPosition (categoryParser `qedType 0)
private abbrev mpExpr : Parser := categoryParser `qedExpr 0

def mapUsingListP : Parser := node `Qed.mapUsingList (atomic (symbol "using") >> "[" >> sepBy1 termParser "," >> "]")
def mapSideSpecP : Parser :=
  node `Qed.mapSideNamed (atomic (ident >> ":") >> mpType >> optional (checkLineEq >> symbol "where" >> sepBy1 mpExpr ",")) <|>
  node `Qed.mapSidePlain mpType
@[mapClause_parser] def mapFromClause : Parser := leading_parser withPosition (atomic (symbol "from") >> mapSideSpecP)
@[mapClause_parser] def mapToClause   : Parser := leading_parser withPosition (atomic (identEq `to) >> mapSideSpecP)
@[mapClause_parser] def mapUsingClause : Parser := leading_parser withPosition mapUsingListP
@[mapClause_parser] def mapEncodeClause : Parser := leading_parser withPosition
  (atomic (identEq `encode >> checkNoWsBefore "" >> "(") >> ident >> ")" >> ":" >> qedSuite)
@[mapClause_parser] def mapDecodeClause : Parser := leading_parser withPosition
  (atomic (identEq `decode >> checkNoWsBefore "" >> "(") >> ident >> ")" >> ":" >> qedSuite)
@[mapClause_parser] def mapProveUsingClause : Parser := leading_parser withPosition
  (atomic (identEq `prove >> (identEq `encode_ok <|> identEq `roundtrip)) >> mapUsingListP)
@[mapClause_parser] def mapProveByClause : Parser := leading_parser withPosition
  (atomic (identEq `prove >> (identEq `encode_ok <|> identEq `roundtrip)) >> ":=" >> "by" >> Parser.Tactic.tacticSeq)
@[command_parser] def mappingCmd : Parser := leading_parser withPosition
  (atomic (identEq `mapping) >> ident >> optional (checkLineEq >> "(" >> sepBy1 schemaCtxParamP "," >> ")") >> ":" >>
    checkColGt "expected indented `mapping` clauses (`from`, `to`, `encode`, `decode`)" >> many1Indent (categoryParser `mapClause 0))

syntax (name := qedMapProveTac) "qedMapProve" "[" ident,* "]" "[" term,* "]" str str str : tactic
end MappingParsers

section MappingElab
open Lean Meta Elab Command Tactic Qed.Lang Qed.Verify.Core

private def mapBaseSimpNames : Array Name :=
  boolSimpNames ++ boolConstSimpNames ++ valUnwrapBaseNames ++ #[
    ``Qed.Codec.run_refine_text, ``Qed.Codec.run_refine_textarea,
    ``Qed.Field.toUTF8, ``Qed.Field.length, ``Qed.Field.utf8ByteSize, ``Qed.Field.size,
    ``Qed.Base64.encode_length, ``Qed.Base64.encodeUrl_length,
    ``Qed.Base64.encodedLength, ``Qed.Base64.encodedUrlLength, ``Qed.Base64.decode_encode,
    ``Qed.Proto.decode_encode, ``Qed.Proto.decodeHex_encodeHex,
    ``Qed.toUTF8_size, ``Qed.fromUTF8?_toUTF8,
    ``Qed.MappingUnwrap.unwrap_ok, ``Qed.MappingUnwrap.unwrap_error,
    ``Qed.MappingUnwrap.unwrap_some, ``Qed.MappingUnwrap.unwrap_none,
    ``Bind.bind, ``Except.bind, ``Option.bind, ``Pure.pure, ``Except.pure,
    ``dite_eq_left, ``Option.some.injEq, ``Except.ok.injEq, ``id_eq, ``and_self, ``true_and, ``and_true]

@[noinline, tactic qedMapProveTac] def elabQedMapProve : Tactic := fun stx => do
  let unfoldNames ← (stx.getArg 2).getSepArgs.mapM resolveGlobalConstNoOverload
  let extraTerms : Array Term := (stx.getArg 5).getSepArgs.map (⟨·⟩)
  let (kindStr, nameStr, hintStr) := ((⟨stx.getArg 7⟩ : TSyntax `str).getString, (⟨stx.getArg 8⟩ : TSyntax `str).getString, (⟨stx.getArg 9⟩ : TSyntax `str).getString)
  let ok ← tryRestoreM false id do
    let (_, g1) ← (← getMainGoal).intros; setGoals [g1]
    let uOnly ← namesToSimpLemmas unfoldNames
    let _ ← tryTac `(tactic| simp only [$[$uOnly],*] at *)
    forEachGoal fun g => do
      let (g', _) ← collectAndAssertFacts g "_mapFact" { scanLCtx := true, scanLCtxValues := true, includeFin := true }
      setGoals [(← splitAndHypsGoal g').1]
    let codecArgs ← namesToSimpLemmas optCodecSimpNames
    let baseSimp := (← namesToSimpLemmas (unfoldNames ++ mapBaseSimpNames)) ++ (← termsToSimpLemmas extraTerms)
    let _ ← tryTac `(tactic| simp only [$[$baseSimp],*] at *)
    let extraParseNames ← match ← getGoals with
      | g :: _ => g.withContext do return (← instantiateMVars (← g.getType)).getUsedConstants.filter fun | .str _ "parse" => true | _ => false
      | [] => pure #[]
    let allSimp ← if extraParseNames.isEmpty then pure baseSimp else do
      let s := baseSimp ++ (← namesToSimpLemmas extraParseNames)
      let _ ← tryTac `(tactic| simp only [$[$s],*] at *); pure s
    let _ ← tryTac `(tactic| simp only [$[$codecArgs],*] at *)
    let _ ← tryTac `(tactic| repeat' (first | (split; try simp only [$[$allSimp],*] at *) | (cases ‹_ ∧ _›)))
    forEachGoal fun g => do
      if ← tryCloseBasic g then setGoals []
      else
        setGoals [g]
        unless ← tryTac (requireClosed := true) `(tactic| first | (simp_all [$[$allSimp],*] <;> first | omega | decide | rfl) | grind) do setGoals [g]
    return (← getGoals).isEmpty
  unless ok do
    let _ ← tryTac do let uArgs ← namesToSimpLemmas unfoldNames; `(tactic| (intros; try simp only [$[$uArgs],*]))
    Qed.Diag.throwUnsolvedGoals m!"Mapping `{nameStr}` failed {kindStr}:" m!"\n\nHint: {hintStr}"
      (ref? := some stx) (stripPrefixes := ["_a", "a"]) (bulletPrefix := "  • must prove: ")

private abbrev MapLowerM := StateRefT (Nat × Array (Ident × Term)) CommandElabM

private def mapFreshId (pfx : String) : MapLowerM Ident := do
  let (n, hs) ← get; set (n + 1, hs); return mkIdent (Name.mkSimple s!"{pfx}{n}")

@[noinline] private def liftMapMacro {α : Type} (k : MacroM α) : MapLowerM α := liftM (liftMacroM (m := CommandElabM) k)

private def isMapFailCallee (callee : Syntax) : Bool :=
  callee.getKind == ``qedIdent && (callee.getArg 0).getId.eraseMacroScopes == `fail

@[noinline] private partial def lowerMapExpr (isDecode : Bool) (locals : Array String) (mode : ExprMode) (stx : Syntax) : MapLowerM Term :=
  let hoistUnw (ref : Syntax) (innerT : Term) (m' : ExprMode) : MapLowerM Term := do
    unless isDecode do throwErrorAt ref "operator `?` is only supported inside `decode(...)`"
    let tmp ← mapFreshId "_mapUnw"; modify fun (n, hs) => (n, hs.push (tmp, innerT))
    liftMapMacro (finishTermMode m' ⟨tmp⟩)
  let hooks : LowerHooks MapLowerM := { LowerHooks.mkDefault (fun ref msg => throwErrorAt ref msg) with
    lowerIdent := fun ref id m' => do
      let sId := id.getId.eraseMacroScopes.toString
      if isDecode && sId.endsWith "?" then
        let base := (sId.dropEnd 1).toString
        if locals.contains base then return ← hoistUnw ref (mkIdentFrom ref (Name.mkSimple base)) m'
      liftMapMacro (finishTermMode m' ⟨id.raw⟩)
    lowerUnwrap := fun ref innerRaw m' => do hoistUnw ref (← lowerMapExpr isDecode locals .val innerRaw) m'
    lowerCall := fun ref callee rawArgs _ goRec => do
      if isDecode && isMapFailCallee callee then
        if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then throwErrorAt ref "`fail(...)` expects a single error message string"
        return some (← `(Except.error $(← goRec .val rawArgs[0]![0])))
      return none
    lowerType := fun t => liftMapMacro (return (← lowerQedType t false).1)
    lowerPat := fun p => liftMapMacro (lowerQedPat p)
    freshIdent := mapFreshId }
  lowerQedExpr hooks mode stx

private def lowerMapExprWithHoists (isDecode : Bool) (locals : Array String) (mode : ExprMode) (stx : Syntax) : MapLowerM (Term × Array (Ident × Term)) := do
  let (n0, saved) ← get; set (n0, (#[] : Array (Ident × Term)))
  let t ← lowerMapExpr isDecode locals mode stx
  let (n1, hs) ← get; set (n1, saved); return (t, hs)

@[noinline] private def wrapMapHoistsPure (hs : Array (Ident × Term)) (body : Term) : PureQuotM Term :=
  hs.foldrM (init := body) fun (tmp, inner) acc => `(Except.bind (Qed.MappingUnwrap.unwrap $inner) fun $tmp:ident => $acc)

@[noinline] private def lowerMapStmts (isDecode : Bool) (locals : Array String) (stmts : Array Syntax) : MapLowerM Term :=
  let withHoist (locs : Array String) (mode : ExprMode) (s : Syntax) (k : Term → MapLowerM Term) : MapLowerM Term := do
    let (t, hs) ← lowerMapExprWithHoists isDecode locs mode s
    let res ← k t
    runPureQuot (wrapMapHoistsPure hs res)
  let badStmt (st : Syntax) : MapLowerM Term :=
    throwErrorAt st "unsupported statement in `mapping` body (use `let`, `if`, `if let`, `match`, or `return`)"
  lowerPureStmtsM {
    withVal := fun locs s k => withHoist locs .val s k
    withGuard := fun locs s k => withHoist locs .propGuard s k
    extendLocals := fun locs names => locs ++ names.map (·.toString)
    onEmpty := fun _ => throwError "`mapping` `encode`/`decode` block must end with `return <expr>`"
    onReturn := fun locs st _ => do
      let opt := st.getArg 1
      unless opt.getNumArgs == 1 do throwErrorAt st "`return` inside `mapping` requires a value"
      withHoist locs .val (opt.getArg 0) fun valT => if isDecode then `(Except.ok $valT) else pure valT
    onExpr := fun locs st rest => do
      unless rest.isEmpty do return ← badStmt st
      let eStx := unwrapParens1 (st.getArg 0)
      withHoist locs .val (st.getArg 0) fun valT =>
        if isDecode && !(eStx.getKind == ``qedCall && isMapFailCallee (eStx.getArg 0)) then `(Except.ok $valT) else pure valT
    onMissingElse := fun st kindName => throwErrorAt st s!"`{kindName}` inside `mapping` requires an `else:` branch or following `return`"
    onUnsupported := badStmt
    freshIfId? := some (mapFreshId "_mapIf")
    depIfLet := false
    appendRest := false
    letClauseErr := "`predict`/`catch` clauses are not supported in `mapping`"
  } locals stmts.toList

private def lowerMapWhere (preds : Array Syntax) : CommandElabM Term := do
  if preds.isEmpty then return ← runPureQuot `(True)
  let ts ← preds.mapM fun p => liftMacroM (lowerSimpleQedExpr .propInv p)
  runPureQuot (mkConjBody ts (ascribeProp := false))

private def parseMapSideSpec (ref : Ident) (fallbackName : Name) (spec : Syntax) : CommandElabM (Ident × Term × Array Syntax) := do
  if spec.getKind == `Qed.mapSideNamed then
    let tyT ← liftMacroM (return (← lowerQedType (spec.getArg 2) false).1)
    return (⟨spec.getArg 0⟩, tyT, if (spec.getArg 3).getNumArgs == 2 then ((spec.getArg 3).getArg 1).getSepArgs else #[])
  return (mkIdentFrom ref fallbackName, ← liftMacroM (return (← lowerQedType (spec.getArg 0) false).1), #[])

@[noinline] private def mkMappingCmdsPure (mId : Ident) (cbns : Array Ident) (cbts : Array Term)
    (srcVar tgtVar encParam decParam : Ident) (srcTy tgtTy srcInvBody tgtInvBody encBody decBody : Term)
    (hasSrcWhere : Bool) (tgtLabel : String) (encOkUsing rtUsing : Array Term) (encOkBy? rtBy? : Option Syntax) :
    PureQuotM (Array (TSyntax `command)) := do
  let mName := mId.getId; let sub (s : Name) := mkIdentFrom mId (mName ++ s)
  let appCtx (id : Ident) : PureQuotM Term := mkAppTerms ⟨id.raw⟩ (cbns.map (⟨·.raw⟩))
  let (srcId, tgtId, srcInvId, tgtInvId) := (sub `Source, sub `Target, sub `SourceInv, sub `TargetInv)
  let (toTgtId, rawDecId, toSrcId) := (sub `toTarget, sub `rawDecode, sub `toSource)
  let (decOkId, encOkId, rtId, mapId, encId, decId, decEncId) := (sub `decode_ok, sub `encode_ok, sub `roundtrip, sub `mapping, sub `encode, sub `decode, sub `decode_encode)
  let (srcInvApp, tgtInvApp, toTgtApp, rawDecApp, toSrcApp) := (← appCtx srcInvId, ← appCtx tgtInvId, ← appCtx toTgtId, ← appCtx rawDecId, ← appCtx toSrcId)
  let (mapApp, encApp, decApp, encOkApp, decOkApp, rtApp) := (← appCtx mapId, ← appCtx encId, ← appCtx decId, ← appCtx encOkId, ← appCtx decOkId, ← appCtx rtId)
  let encOkPfTac : TSyntax ``Lean.Parser.Tactic.tacticSeq ← match encOkBy? with
    | some seq => pure ⟨seq⟩
    | none => `(Lean.Parser.Tactic.tacticSeq| qedMapProve [$toTgtId:ident, $srcInvId:ident, $tgtInvId:ident] [$[$encOkUsing:term],*] $(Syntax.mkStrLit tgtLabel) $(Syntax.mkStrLit mName.toString) "Align `from` and `to` `where` constraints, add `using [lemma]`, or supply `prove encode_ok := by ...`.")
  let rtPfTac : TSyntax ``Lean.Parser.Tactic.tacticSeq ← match rtBy? with
    | some seq => pure ⟨seq⟩
    | none => `(Lean.Parser.Tactic.tacticSeq| qedMapProve [$toSrcId:ident, $rawDecId:ident, $toTgtId:ident, $srcInvId:ident] [$[$rtUsing:term],*] "round-trip `decode(encode(x)) == ok(x)`" $(Syntax.mkStrLit mName.toString) "Ensure `decode` inverts `encode`, add `using [lemma]`, or supply `prove roundtrip := by ...`.")
  let (toSrcBody, decOkBody, encInTy, encBody2, decBody2, decEncBody) ←
    if hasSrcWhere then pure (
      ← `(($rawDecApp b).bind fun _a => if _h : $srcInvApp _a then Except.ok _a else Except.error "mapping decode violated source constraint"),
      ← `(Qed.Mapping.decode_ok_of_guard (pA := $srcInvApp) h),
      ← `(Qed.Field ($srcInvApp)), ← `(($mapApp).encodeField a), ← `(($mapApp).decode b), ← `(($mapApp).decode_encode a.val a.ok))
    else pure (← `($rawDecApp b), ← `(trivial), (srcId : Term), ← `(($mapApp).encode a trivial), ← `($toSrcApp b), ← `($rtApp a trivial))
  return #[
    ← `(command| abbrev $srcId : Type := $srcTy),
    ← `(command| abbrev $tgtId : Type := $tgtTy),
    ← `(command| set_option linter.unusedVariables false in abbrev $srcInvId $[($cbns:ident : $cbts:term)]* ($srcVar:ident : $srcId) : Prop := $srcInvBody),
    ← `(command| set_option linter.unusedVariables false in abbrev $tgtInvId $[($cbns:ident : $cbts:term)]* ($tgtVar:ident : $tgtId) : Prop := $tgtInvBody),
    ← `(command| set_option linter.unusedVariables false in def $toTgtId $[($cbns:ident : $cbts:term)]* ($encParam:ident : $srcId) : $tgtId := $encBody),
    ← `(command| set_option linter.unusedVariables false in def $rawDecId $[($cbns:ident : $cbts:term)]* ($decParam:ident : $tgtId) : Except String $srcId := $decBody),
    ← `(command| def $toSrcId $[($cbns:ident : $cbts:term)]* (b : $tgtId) : Except String $srcId := $toSrcBody),
    ← `(command| set_option linter.unusedVariables false in theorem $decOkId $[($cbns:ident : $cbts:term)]* (b : $tgtId) (a : $srcId) (h : $toSrcApp b = Except.ok a) : $srcInvApp a := $decOkBody),
    ← `(command| set_option linter.unusedVariables false in theorem $encOkId $[($cbns:ident : $cbts:term)]* (a : $srcId) (ha : $srcInvApp a) : $tgtInvApp ($toTgtApp a) := by $encOkPfTac),
    ← `(command| set_option linter.unusedVariables false in theorem $rtId $[($cbns:ident : $cbts:term)]* (a : $srcId) (ha : $srcInvApp a) : $toSrcApp ($toTgtApp a) = Except.ok a := by $rtPfTac),
    ← `(command| def $mapId $[($cbns:ident : $cbts:term)]* : Qed.Mapping ($srcInvApp) ($tgtInvApp) := ⟨$toTgtApp, $toSrcApp, $encOkApp, $decOkApp, $rtApp⟩),
    ← `(command| def $encId $[($cbns:ident : $cbts:term)]* (a : $encInTy) : Qed.Field ($tgtInvApp) := $encBody2),
    ← `(command| def $decId $[($cbns:ident : $cbts:term)]* (b : $tgtId) : Except String $encInTy := $decBody2),
    ← `(command| theorem $decEncId $[($cbns:ident : $cbts:term)]* (a : $encInTy) : $decApp ($encApp a).val = Except.ok a := $decEncBody)]

@[noinline, command_elab mappingCmd] def elabMappingCmd : CommandElab := fun stx => do
  let mId : Ident := ⟨stx.getArg 1⟩; let mName := mId.getId
  let (cbns, cbts) ← parseCtxBinders (stx.getArg 2)
  let mut src? : Option (Ident × Term × Array Syntax) := none; let mut tgt? : Option (Ident × Term × Array Syntax) := none
  let mut enc? : Option (Ident × Array Syntax) := none; let mut dec? : Option (Ident × Array Syntax) := none
  let mut (sharedUsing, encOkUsing, rtUsing) : Array Term × Array Term × Array Term := (#[], #[], #[])
  let mut (encOkBy?, rtBy?) : Option Syntax × Option Syntax := (none, none)
  for c in (stx.getArg 4).getArgs do
    match c.getKind with
    | ``mapFromClause =>
        if src?.isSome then throwErrorAt c s!"duplicate `from` clause in `mapping {mName}`"
        src? := some (← parseMapSideSpec mId `source (c.getArg 1))
    | ``mapToClause =>
        if tgt?.isSome then throwErrorAt c s!"duplicate `to` clause in `mapping {mName}`"
        tgt? := some (← parseMapSideSpec mId `target (c.getArg 1))
    | ``mapUsingClause => sharedUsing := sharedUsing ++ ((c.getArg 0).getArg 2).getSepArgs.map (⟨·⟩)
    | ``mapEncodeClause =>
        if enc?.isSome then throwErrorAt c s!"duplicate `encode` clause in `mapping {mName}`"
        enc? := some (⟨c.getArg 2⟩, suiteStmts (c.getArg 5))
    | ``mapDecodeClause =>
        if dec?.isSome then throwErrorAt c s!"duplicate `decode` clause in `mapping {mName}`"
        dec? := some (⟨c.getArg 2⟩, suiteStmts (c.getArg 5))
    | ``mapProveUsingClause =>
        let ts := ((c.getArg 2).getArg 2).getSepArgs.map (⟨·⟩)
        if (c.getArg 1).getId.eraseMacroScopes == `encode_ok then encOkUsing := encOkUsing ++ ts else rtUsing := rtUsing ++ ts
    | ``mapProveByClause =>
        if (c.getArg 1).getId.eraseMacroScopes == `encode_ok then encOkBy? := some (c.getArg 4) else rtBy? := some (c.getArg 4)
    | _ => throwErrorAt c s!"unexpected clause in `mapping {mName}`"
  let some (srcVar, srcTy, srcWheres) := src? | throwErrorAt mId s!"`mapping {mName}` requires a `from <x : Type>` (or `from <Type>`) clause"
  let some (tgtVar, tgtTy, tgtWheres) := tgt? | throwErrorAt mId s!"`mapping {mName}` requires a `to <y : Type>` (or `to <Type>`) clause"
  let some (encParam, encStmts) := enc?       | throwErrorAt mId s!"`mapping {mName}` requires an `encode(x): ...` clause"
  let some (decParam, decStmts) := dec?       | throwErrorAt mId s!"`mapping {mName}` requires a `decode(y): ...` clause"
  let (srcInvBody, tgtInvBody) := (← lowerMapWhere srcWheres, ← lowerMapWhere tgtWheres)
  let ctxNames := cbns.map (·.getId.eraseMacroScopes.toString)
  let encBody ← (lowerMapStmts false (ctxNames.push encParam.getId.eraseMacroScopes.toString) encStmts).run' (0, #[])
  let decBody ← (lowerMapStmts true (ctxNames.push decParam.getId.eraseMacroScopes.toString) decStmts).run' (0, #[])
  let tgtLabel := if tgtWheres.isEmpty then "target invariant" else s!"target constraint `{fmtWhereLabel tgtWheres}`"
  let cmds ← runPureQuot (mkMappingCmdsPure mId cbns cbts srcVar tgtVar encParam decParam srcTy tgtTy srcInvBody tgtInvBody encBody decBody
    (!srcWheres.isEmpty) tgtLabel (sharedUsing ++ encOkUsing) (sharedUsing ++ rtUsing) encOkBy? rtBy?)
  cmds.forM elabCommand

end MappingElab
end Qed
