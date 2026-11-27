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

@[noinline, tactic qedMapProveTac]
def elabQedMapProve : Tactic := fun stx => do
  let unfoldNames ← (stx.getArg 2).getSepArgs.mapM resolveGlobalConstNoOverload
  let extraTerms : Array Term := (stx.getArg 5).getSepArgs.map (⟨·⟩)
  let kindStr := (⟨stx.getArg 7⟩ : TSyntax `str).getString
  let nameStr := (⟨stx.getArg 8⟩ : TSyntax `str).getString
  let hintStr := (⟨stx.getArg 9⟩ : TSyntax `str).getString
  let ok ← tryRestoreM false id do
    let g0 ← getMainGoal
    let (_, g1) ← g0.intros
    setGoals [g1]
    let uOnly ← namesToSimpLemmas unfoldNames
    let _ ← tryTac `(tactic| simp only [$[$uOnly],*] at *)
    forEachGoal fun g => do
      let (g', _) ← collectAndAssertFacts g "_mapFact" { scanLCtx := true, scanLCtxValues := true, includeFin := true }
      setGoals [(← splitAndHypsGoal g').1]
    let codecArgs ← namesToSimpLemmas optCodecSimpNames
    let uArgs ← namesToSimpLemmas (unfoldNames ++ mapBaseSimpNames)
    let eArgs ← termsToSimpLemmas extraTerms
    let baseSimp := uArgs ++ eArgs
    let _ ← tryTac `(tactic| simp only [$[$baseSimp],*] at *)
    -- Unfold any `Schema.parse` exposed after unfolding `rawDecode`
    let extraParseNames ← match ← getGoals with
      | g :: _ => g.withContext do
          let mut ps : Array Name := #[]
          for c in (← instantiateMVars (← g.getType)).getUsedConstants do
            if let .str _ "parse" := c then ps := ps.push c
          pure ps
      | [] => pure #[]
    let allSimp ← if extraParseNames.isEmpty then pure baseSimp else do
      let pArgs ← namesToSimpLemmas extraParseNames
      let s := baseSimp ++ pArgs
      let _ ← tryTac `(tactic| simp only [$[$s],*] at *)
      pure s
    -- Simplify `Codec.valid`/`Codec.refine` after `Schema.parse` reduces (preserves `Field` types in goal)
    let _ ← tryTac `(tactic| simp only [$[$codecArgs],*] at *)
    let _ ← tryTac `(tactic| repeat' (first | (split; try simp only [$[$allSimp],*] at *) | (cases ‹_ ∧ _›)))
    forEachGoal fun g => do
      if ← tryCloseBasic g then setGoals []
      else
        setGoals [g]
        let closed ← tryTac (requireClosed := true) `(tactic| first
          | (simp_all [$[$allSimp],*] <;> first | omega | decide | rfl)
          | grind)
        unless closed do setGoals [g]
    return (← getGoals).isEmpty
  unless ok do
    -- Simplify once for a clean diagnostic target before failing
    let _ ← tryTac do
      let uArgs ← namesToSimpLemmas unfoldNames
      `(tactic| (intros; try simp only [$[$uArgs],*]))
    Qed.Diag.throwUnsolvedGoals m!"Mapping `{nameStr}` failed {kindStr}:" m!"\n\nHint: {hintStr}"
      (ref? := some stx) (stripPrefixes := ["_a", "a"]) (bulletPrefix := "  • must prove: ")

private abbrev MapLowerM := StateRefT (Nat × Array (Ident × Term)) CommandElabM

private def mapFreshId (pfx : String) : MapLowerM Ident := do
  let (n, hs) ← get; set (n + 1, hs); return mkIdent (Name.mkSimple s!"{pfx}{n}")

private def isMapFailCallee (callee : Syntax) : Bool :=
  callee.getKind == ``qedIdent && (callee.getArg 0).getId.eraseMacroScopes == `fail

@[noinline]
private partial def lowerMapExpr (isDecode : Bool) (locals : Array String) (mode : ExprMode) (stx : Syntax) : MapLowerM Term :=
  let hoistUnw (ref : Syntax) (innerT : Term) (m' : ExprMode) : MapLowerM Term := do
    unless isDecode do throwErrorAt ref "operator `?` is only supported inside `decode(...)`"
    let tmp ← mapFreshId "_mapUnw"
    modify fun (n, hs) => (n, hs.push (tmp, innerT))
    liftMacroM (finishTermMode m' ⟨tmp⟩)
  let hooks : LowerHooks MapLowerM := { LowerHooks.mkDefault (fun ref msg => throwErrorAt ref msg) with
    lowerIdent := fun ref id m' => do
      let sId := id.getId.eraseMacroScopes.toString
      if isDecode && sId.endsWith "?" then
        let base := (sId.dropEnd 1).toString
        if locals.contains base then return ← hoistUnw ref (mkIdentFrom ref (Name.mkSimple base)) m'
      liftMacroM (finishTermMode m' ⟨id.raw⟩)
    lowerUnwrap := fun ref innerRaw m' => do hoistUnw ref (← lowerMapExpr isDecode locals .val innerRaw) m'
    lowerCall := fun ref callee rawArgs _ goRec => do
      if isDecode && isMapFailCallee callee then
        if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then throwErrorAt ref "`fail(...)` expects a single error message string"
        return some (← `(Except.error $(← goRec .val rawArgs[0]![0])))
      return none
    lowerType := fun t => liftMacroM (return (← lowerQedType t false).1)
    lowerPat := fun p => liftMacroM (lowerQedPat p)
    freshIdent := mapFreshId }
  lowerQedExpr hooks mode stx

private def lowerMapExprWithHoists (isDecode : Bool) (locals : Array String) (mode : ExprMode) (stx : Syntax) :
    MapLowerM (Term × Array (Ident × Term)) := do
  let (n0, saved) ← get; set (n0, (#[] : Array (Ident × Term)))
  let t ← lowerMapExpr isDecode locals mode stx
  let (n1, hs) ← get; set (n1, saved); return (t, hs)

private def wrapMapHoists (hs : Array (Ident × Term)) (body : Term) : CommandElabM Term :=
  hs.foldrM (init := body) fun (tmp, inner) acc => `(Except.bind (Qed.MappingUnwrap.unwrap $inner) fun $tmp:ident => $acc)

@[noinline]
private def lowerMapStmts (isDecode : Bool) (locals : Array String) (stmts : Array Syntax) : MapLowerM Term :=
  let withHoist (locs : Array String) (mode : ExprMode) (s : Syntax) (k : Term → MapLowerM Term) : MapLowerM Term := do
    let (t, hs) ← lowerMapExprWithHoists isDecode locs mode s
    liftM <| wrapMapHoists hs (← k t)
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
  if preds.isEmpty then return ← `(True)
  mkConjBody (← preds.mapM fun p => liftMacroM (lowerSimpleQedExpr .propInv p)) (ascribeProp := false)

private def parseMapSideSpec (ref : Ident) (fallbackName : Name) (spec : Syntax) : CommandElabM (Ident × Term × Array Syntax) := do
  if spec.getKind == `Qed.mapSideNamed then
    let tyT ← liftMacroM (return (← lowerQedType (spec.getArg 2) false).1)
    let ws := if (spec.getArg 3).getNumArgs == 2 then ((spec.getArg 3).getArg 1).getSepArgs else #[]
    return (⟨spec.getArg 0⟩, tyT, ws)
  else
    let tyT ← liftMacroM (return (← lowerQedType (spec.getArg 0) false).1)
    return (mkIdentFrom ref fallbackName, tyT, #[])

@[noinline, command_elab mappingCmd]
def elabMappingCmd : CommandElab := fun stx => do
  let mId : Ident := ⟨stx.getArg 1⟩; let mName := mId.getId
  let (cbns, cbts) ← parseCtxBinders (stx.getArg 2)
  let mut src? : Option (Ident × Term × Array Syntax) := none
  let mut tgt? : Option (Ident × Term × Array Syntax) := none
  let mut enc? : Option (Ident × Array Syntax) := none
  let mut dec? : Option (Ident × Array Syntax) := none
  let mut sharedUsing : Array Term := #[]
  let mut encOkUsing : Array Term := #[]; let mut rtUsing : Array Term := #[]
  let mut encOkBy? : Option Syntax := none; let mut rtBy? : Option Syntax := none
  for c in (stx.getArg 4).getArgs do
    let k := c.getKind
    if k == ``mapFromClause then
      if src?.isSome then throwErrorAt c s!"duplicate `from` clause in `mapping {mName}`"
      src? := some (← parseMapSideSpec mId `source (c.getArg 1))
    else if k == ``mapToClause then
      if tgt?.isSome then throwErrorAt c s!"duplicate `to` clause in `mapping {mName}`"
      tgt? := some (← parseMapSideSpec mId `target (c.getArg 1))
    else if k == ``mapUsingClause then
      sharedUsing := sharedUsing ++ ((c.getArg 0).getArg 2).getSepArgs.map (⟨·⟩)
    else if k == ``mapEncodeClause then
      if enc?.isSome then throwErrorAt c s!"duplicate `encode` clause in `mapping {mName}`"
      enc? := some (⟨c.getArg 2⟩, suiteStmts (c.getArg 5))
    else if k == ``mapDecodeClause then
      if dec?.isSome then throwErrorAt c s!"duplicate `decode` clause in `mapping {mName}`"
      dec? := some (⟨c.getArg 2⟩, suiteStmts (c.getArg 5))
    else if k == ``mapProveUsingClause then
      let tgt := (c.getArg 1).getId.eraseMacroScopes; let ts := ((c.getArg 2).getArg 2).getSepArgs.map (⟨·⟩)
      if tgt == `encode_ok then encOkUsing := encOkUsing ++ ts else rtUsing := rtUsing ++ ts
    else if k == ``mapProveByClause then
      let tgt := (c.getArg 1).getId.eraseMacroScopes
      if tgt == `encode_ok then encOkBy? := some (c.getArg 4) else rtBy? := some (c.getArg 4)
    else throwErrorAt c s!"unexpected clause in `mapping {mName}`"
  let some (srcVar, srcTy, srcWheres) := src? | throwErrorAt mId s!"`mapping {mName}` requires a `from <x : Type>` (or `from <Type>`) clause"
  let some (tgtVar, tgtTy, tgtWheres) := tgt? | throwErrorAt mId s!"`mapping {mName}` requires a `to <y : Type>` (or `to <Type>`) clause"
  let some (encParam, encStmts) := enc?       | throwErrorAt mId s!"`mapping {mName}` requires an `encode(x): ...` clause"
  let some (decParam, decStmts) := dec?       | throwErrorAt mId s!"`mapping {mName}` requires a `decode(y): ...` clause"
  let hasSrcWhere := !srcWheres.isEmpty
  let srcInvBody ← lowerMapWhere srcWheres
  let tgtInvBody ← lowerMapWhere tgtWheres
  let ctxNames := cbns.map (·.getId.eraseMacroScopes.toString)
  let encBody ← (lowerMapStmts false (ctxNames.push encParam.getId.eraseMacroScopes.toString) encStmts).run' (0, #[])
  let decBody ← (lowerMapStmts true (ctxNames.push decParam.getId.eraseMacroScopes.toString) decStmts).run' (0, #[])
  let sub (s : Name) := mkIdentFrom mId (mName ++ s)
  let appCtx (id : Ident) : CommandElabM Term := mkAppTerms ⟨id.raw⟩ (cbns.map (⟨·.raw⟩))
  let (srcId, tgtId, srcInvId, tgtInvId) := (sub `Source, sub `Target, sub `SourceInv, sub `TargetInv)
  let (toTgtId, rawDecId, toSrcId) := (sub `toTarget, sub `rawDecode, sub `toSource)
  let (decOkId, encOkId, rtId, mapId, encId, decId, decEncId) :=
    (sub `decode_ok, sub `encode_ok, sub `roundtrip, sub `mapping, sub `encode, sub `decode, sub `decode_encode)
  let srcInvApp ← appCtx srcInvId; let tgtInvApp ← appCtx tgtInvId
  let toTgtApp ← appCtx toTgtId; let rawDecApp ← appCtx rawDecId; let toSrcApp ← appCtx toSrcId
  let mapApp ← appCtx mapId; let encApp ← appCtx encId; let decApp ← appCtx decId
  let encOkAllUsing := sharedUsing ++ encOkUsing; let rtAllUsing := sharedUsing ++ rtUsing
  let tgtLabel := if tgtWheres.isEmpty then "target invariant" else s!"target constraint `{fmtWhereLabel tgtWheres}`"
  let encOkPfTac : TSyntax ``Lean.Parser.Tactic.tacticSeq ← match encOkBy? with
    | some seq => pure ⟨seq⟩
    | none => `(Lean.Parser.Tactic.tacticSeq| qedMapProve [$toTgtId:ident, $srcInvId:ident, $tgtInvId:ident] [$[$encOkAllUsing:term],*] $(Syntax.mkStrLit tgtLabel) $(Syntax.mkStrLit mName.toString) "Align `from` and `to` `where` constraints, add `using [lemma]`, or supply `prove encode_ok := by ...`.")
  let rtPfTac : TSyntax ``Lean.Parser.Tactic.tacticSeq ← match rtBy? with
    | some seq => pure ⟨seq⟩
    | none => `(Lean.Parser.Tactic.tacticSeq| qedMapProve [$toSrcId:ident, $rawDecId:ident, $toTgtId:ident, $srcInvId:ident] [$[$rtAllUsing:term],*] "round-trip `decode(encode(x)) == ok(x)`" $(Syntax.mkStrLit mName.toString) "Ensure `decode` inverts `encode`, add `using [lemma]`, or supply `prove roundtrip := by ...`.")
  let toSrcCmd ← if hasSrcWhere then
      `(command| def $toSrcId $[($cbns:ident : $cbts:term)]* (b : $tgtId) : Except String $srcId :=
          ($rawDecApp b).bind fun _a => if _h : $srcInvApp _a then Except.ok _a else Except.error "mapping decode violated source constraint")
    else `(command| def $toSrcId $[($cbns:ident : $cbts:term)]* (b : $tgtId) : Except String $srcId := $rawDecApp b)
  let decOkCmd ← if hasSrcWhere then
      `(command| theorem $decOkId $[($cbns:ident : $cbts:term)]* (b : $tgtId) (a : $srcId) (h : $toSrcApp b = Except.ok a) : $srcInvApp a :=
          Qed.Mapping.decode_ok_of_guard (pA := $srcInvApp) h)
    else `(command| theorem $decOkId $[($cbns:ident : $cbts:term)]* (_b : $tgtId) (_a : $srcId) (_h : $toSrcApp _b = Except.ok _a) : $srcInvApp _a := trivial)
  let encDecCmds ← if hasSrcWhere then pure #[
      ← `(command| def $encId $[($cbns:ident : $cbts:term)]* (a : Qed.Field ($srcInvApp)) : Qed.Field ($tgtInvApp) := ($mapApp).encodeField a),
      ← `(command| def $decId $[($cbns:ident : $cbts:term)]* (b : $tgtId) : Except String (Qed.Field ($srcInvApp)) := ($mapApp).decode b),
      ← `(command| theorem $decEncId $[($cbns:ident : $cbts:term)]* (a : Qed.Field ($srcInvApp)) : $decApp ($encApp a).val = Except.ok a := ($mapApp).decode_encode a.val a.ok)]
    else pure #[
      ← `(command| def $encId $[($cbns:ident : $cbts:term)]* (a : $srcId) : Qed.Field ($tgtInvApp) := ($mapApp).encode a trivial),
      ← `(command| def $decId $[($cbns:ident : $cbts:term)]* (b : $tgtId) : Except String $srcId := $toSrcApp b),
      ← `(command| theorem $decEncId $[($cbns:ident : $cbts:term)]* (a : $srcId) : $decApp ($encApp a).val = Except.ok a := $(← appCtx rtId) a trivial)]
  let cmds : Array (TSyntax `command) := #[
    ← `(command| abbrev $srcId : Type := $srcTy),
    ← `(command| abbrev $tgtId : Type := $tgtTy),
    ← `(command| set_option linter.unusedVariables false in abbrev $srcInvId $[($cbns:ident : $cbts:term)]* ($srcVar:ident : $srcId) : Prop := $srcInvBody),
    ← `(command| set_option linter.unusedVariables false in abbrev $tgtInvId $[($cbns:ident : $cbts:term)]* ($tgtVar:ident : $tgtId) : Prop := $tgtInvBody),
    ← `(command| set_option linter.unusedVariables false in def $toTgtId $[($cbns:ident : $cbts:term)]* ($encParam:ident : $srcId) : $tgtId := $encBody),
    ← `(command| set_option linter.unusedVariables false in def $rawDecId $[($cbns:ident : $cbts:term)]* ($decParam:ident : $tgtId) : Except String $srcId := $decBody),
    toSrcCmd, decOkCmd,
    ← `(command| set_option linter.unusedVariables false in theorem $encOkId $[($cbns:ident : $cbts:term)]* (a : $srcId) (ha : $srcInvApp a) : $tgtInvApp ($toTgtApp a) := by $encOkPfTac),
    ← `(command| set_option linter.unusedVariables false in theorem $rtId $[($cbns:ident : $cbts:term)]* (a : $srcId) (ha : $srcInvApp a) : $toSrcApp ($toTgtApp a) = Except.ok a := by $rtPfTac),
    ← `(command| def $mapId $[($cbns:ident : $cbts:term)]* : Qed.Mapping ($srcInvApp) ($tgtInvApp) :=
          ⟨$toTgtApp, $toSrcApp, $(← appCtx encOkId), $(← appCtx decOkId), $(← appCtx rtId)⟩)
  ] ++ encDecCmds
  cmds.forM elabCommand

end MappingElab
end Qed
