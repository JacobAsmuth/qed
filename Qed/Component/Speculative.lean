import Qed.Component.AwaitLift
import Qed.Speculative.Core
import Qed.Server.Invariant

namespace Qed
section CompElab
open Lean Elab Command Term Meta Qed.Lang

structure CheckOrigin where mk ::
  (callRef : Syntax) (srvShort methodName : String) (argExprs : Array Expr)
  (lctx : LocalContext) (localInsts : LocalInstances) (mctx : MetavarContext)

structure PendingRpcCheck extends CheckOrigin where mk ::
  (reqConst? : Option Name) (reqLabel : String) (requiresAuth : Bool) (sessionVar? : Option Name)

structure PendingPredictCheck extends CheckOrigin where mk ::
  (ensConst : Name) (isOptWrap : Bool) (predExpr : Expr)

initialize pendingRpcChecks      : IO.Ref (Array PendingRpcCheck)     ← IO.mkRef #[]
initialize pendingPredictChecks  : IO.Ref (Array PendingPredictCheck) ← IO.mkRef #[]
initialize currentCompSessionRef : IO.Ref (Option Ident)              ← IO.mkRef none

/-! ## Speculative Prediction Lowering & `_specClassify` Codegen -/

@[noinline]
private def lowerPredictExpr (stx : Syntax) : CommandElabM Term :=
  liftMacroM <| Qed.Lang.lowerSimpleQedExpr .val stx
    (wrapNamedField := fun t => pure ⟨Syntax.node .none ``Qed.Server.srvAutoFieldStx #[Syntax.atom .none "srvAutoField(", t.raw, Syntax.atom .none ")"]⟩)
    (lowerIndex? := some fun _ arrT idxT mode =>
      Qed.Lang.finishTermMode mode ⟨Syntax.node .none ``Qed.Server.srvGetElemStx #[Syntax.atom .none "srvGetElem(", arrT.raw, Syntax.atom .none ", ", idxT.raw, Syntax.atom .none ")"]⟩)

@[noinline]
private def lowerPredictStmts (wrapVal : Term → CommandElabM Term) (stmts : List Syntax) : CommandElabM Term :=
  let badStmt (st : Syntax) : CommandElabM Term :=
    throwErrorAt st "`predict:` only supports pure `let`, `if`, `if let`, `match`, `pass`, and `return`"
  lowerPureStmtsM {
    withVal := fun _ s k => do k (← lowerPredictExpr s)
    withGuard := fun _ s k => do k (← lowerCompExpr .propGuard s)
    extendLocals := fun _ _ => ()
    onEmpty := fun _ => `(Option.none)
    onReturn := fun _ st _ => do
      if (st.getArg 1).getNumArgs == 0 then `(Option.none)
      else `(Option.some ($(← wrapVal (← lowerPredictExpr ((st.getArg 1).getArg 0)))))
    onExpr := fun _ st _ => badStmt st
    onMissingElse := fun _ _ => `(Option.none)
    onUnsupported := badStmt
    letClauseErr := "`predict`/`catch` clauses are not supported inside `predict:`"
  } () stmts

@[noinline]
private def compileSpecDispatchNode (spec : ComponentSpec) (node : SpecDispatchNode) : CommandElabM Term := do
  let (tId, srvId, methId, rpcArgs) := (spec.t.getId, mkIdentFrom node.ref node.srvInfo.serverName, mkIdentFrom node.ref (Name.mkSimple node.mInfo.name), node.rpcArgs)
  let wrapVal (valT : Term) : CommandElabM Term :=
    if node.mInfo.hasEnsures then withRef node.ref `(qedCheckPredict% $srvId:ident $methId:ident [$[$rpcArgs:term],*] ($valT : $(node.predValTy))) else `(($valT : $(node.predValTy)))
  let predOptTerm ← match node.predBody with
    | .expr eStx => `(Option.some ($(← wrapVal (← lowerPredictExpr eStx))))
    | .block pStmts => lowerPredictStmts wrapVal pStmts.toList
  let preMsgOpt : Term ← match node.preCtor? with
    | none => `(Option.none)
    | some preCtor => `(Option.some ($(← Qed.Lang.mkAppTerms (mkIdentFrom node.ref (tId ++ `Msg ++ preCtor)) node.preArgs)))
  let contBase ← Qed.Lang.mkAppTerms (mkIdentFrom node.ref (tId ++ `Msg ++ node.contCtor)) node.capturedArgs
  let (txVar, predVar) := (mkIdent `_specTxId, mkIdent `_specPredVal)
  let resCb ← Qed.Lang.mkAppTerms (← `($(mkIdentFrom node.ref (tId ++ `Msg ++ node.resCtor)) $txVar)) (node.capturedArgs.push predVar)
  let rpcCall ← withRef node.ref `(qedCheckRpcCall% $srvId:ident $methId:ident [$[$rpcArgs:term],*] $resCb)
  let mkDisp (arg : Term) := `(Qed.SpecAction.dispatch $preMsgOpt Qed.Cmd.none ($contBase $arg) (fun $txVar:ident => $rpcCall))
  let dispatchBody ← match ensuredWrapKind node.mInfo node.catchHasNone with
    | .plain => mkDisp predVar
    | wrap =>
        let some ensConst := node.mInfo.ensPredConst | throwErrorAt node.ref "internal: missing server `ensures` predicate in `predict`"
        let ensApp ← Qed.Lang.mkAppTerms (mkIdent ensConst) rpcArgs
        if wrap == .optEnsured then
          let dNone ← mkDisp (← `((Option.none : Option (Qed.Ensured $(node.innerEnsTy?.getD node.predValTy) ($ensApp)))))
          let dSome ← mkDisp (← `(Option.some (Qed.Ensured.mk _pv _hSpecEns)))
          `(match $predVar:ident with | Option.none => $dNone | Option.some _pv => if _hSpecEns : ($ensApp) _pv then $dSome else Qed.SpecAction.normal)
        else do
          let dVal ← mkDisp (← `(Qed.Ensured.mk $predVar:ident _hSpecEns))
          `(if _hSpecEns : ($ensApp) $predVar:ident then $dVal else Qed.SpecAction.normal)
  let matched ← `(match ($predOptTerm : Option $(node.predValTy)) with | Option.none => Qed.SpecAction.normal | Option.some $predVar:ident => $dispatchBody)
  node.hoistDefs.foldrM (init := matched) fun (tmpId, pTy, argT) acc => `(let $tmpId:ident : $pTy := $argT; $acc)

@[noinline]
private partial def compileClassifyStmts (spec : ComponentSpec) : List Syntax → CommandElabM Term
  | [] => `(Qed.SpecAction.normal)
  | st :: rest => do
      if let some idx := matchSpecDispatchMarker? st then return ← compileSpecDispatchNode spec spec.specNodes[idx]!
      let k := st.getKind
      if k == ``qedStmtPass then compileClassifyStmts spec rest
      else if k == ``qedStmtLet then lowerLetStmt st (lowerCompExpr .val) (← compileClassifyStmts spec rest)
      else if k == ``qedStmtIf || k == ``qedStmtIfLet || k == ``qedStmtMatch then lowerControlFlowStmt st (lowerCompExpr .val) fun seq => compileClassifyStmts spec seq.toList
      else if let some (_, wrap) ← lowerMutStmt? spec st false then wrap (← compileClassifyStmts spec rest)
      else compileClassifyStmts spec rest

@[noinline]
def mkSpecClassifyCmds (spec : ComponentSpec) : CommandElabM (Array CmdStx) := do
  if !spec.hasSpeculative then return #[]
  let clsId := spec.id `_specClassify; let mut arms : Array MatchAltStx := #[]
  for da in spec.specDispatches do
    let (paramNames, ids) := (da.params.map (·.1.getId.eraseMacroScopes), (da.params.map (⟨·.1.raw⟩) : Array Term))
    let rhs0 ← compileClassifyStmts spec da.stmts.toList
    let rhs ← bindMentionedFields spec (fun g => !paramNames.contains g && mentionsIdent rhs0.raw g) rhs0
    arms := arms.push (← if ids.isEmpty then `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor da.ctor):ident => $rhs)
                         else `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor da.ctor):ident $ids* => $rhs))
  for rs in spec.specResolves do
    let (txId, predId, outId, vId) := (rs.txIdParam, rs.predParam, rs.outParam, mkIdent `_specOkVal)
    let capIds : Array Term := rs.capturedParams.map (⟨·.1.raw⟩)
    let allPatIds : Array Term := #[⟨txId.raw⟩] ++ capIds ++ #[⟨predId.raw⟩, ⟨outId.raw⟩]
    let okCtorId := mkIdent ((if rs.mInfo.domainErrTags.isEmpty then `Qed.RpcSimpleOutcome else `Qed.RpcOutcome) ++ `ok)
    let mkCtorApp (ctorNm : Name) (arg : Term) := Qed.Lang.mkAppTerms (spec.msgCtor ctorNm) (capIds.push arg)
    let (contMsg, confirmMsg?, rollbackMsg?, catchMsg?) := (← mkCtorApp rs.contCtor vId, ← rs.confirmCtor?.mapM (mkCtorApp · vId), ← rs.rollbackCtor?.mapM (mkCtorApp · vId), ← rs.catchCtor?.mapM (mkCtorApp · outId))
    let optList : Option Term → CommandElabM Term | some m => `([$m]) | none => `(([] : List $(spec.msgId)))
    let okReplList ← match confirmMsg? with | some cm => `([$contMsg, $cm]) | none => `([$contMsg])
    let rawValTerm ← match ensuredWrapKind rs.mInfo rs.catchHasNone with | .optEnsured => `(($vId).map Qed.Ensured.val) | .ensured => `(($vId).val) | .plain => `($vId)
    let (confHit, missRepl) := (← optList confirmMsg?, ← match rollbackMsg? with | some rm => `([$rm]) | none => pure okReplList)
    let okBranchBody ← `(if (Qed.SpecEq.eq $rawValTerm $predId) then Qed.SpecAction.resolve $txId true $okReplList $confHit
      else Qed.SpecAction.resolve $txId false $missRepl ([] : List $(spec.msgId)))
    let okPat ← if rs.mInfo.isOption && rs.catchHasNone then `($okCtorId (Option.some $vId:ident)) else `($okCtorId $vId:ident)
    let matchTerm ← `(match $outId:ident with | $okPat => $okBranchBody | _ => Qed.SpecAction.resolve $txId false $(← optList catchMsg?) ([] : List $(spec.msgId)))
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $(spec.msgCtor rs.resCtor):ident $allPatIds* => $matchTerm))
  arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | _ => Qed.SpecAction.normal))
  return #[
    ← `(command| set_option linter.unusedVariables false in def $clsId (s : $(spec.stateId)) : $(spec.msgId) → Qed.SpecAction $(spec.msgId) := fun m => match m with $[$arms:matchAlt]*),
    ← `(command| set_option linter.unusedVariables false in
        theorem $(spec.id `specClassify_pure) (s : $(spec.stateId)) (m : $(spec.msgId)) (preMsg? : Option $(spec.msgId))
            (preCmd : Qed.Cmd $(spec.msgId)) (specMsg : $(spec.msgId)) (rpcCmd : Nat → Qed.Cmd $(spec.msgId))
            (h : $clsId s m = Qed.SpecAction.dispatch preMsg? preCmd specMsg rpcCmd) : ∀ s', ($(spec.updateId) s' specMsg).2 = Qed.Cmd.none := by
          intro s'; unfold $clsId at h; cases m <;> dsimp only at h
          all_goals repeat (first | (injection h with _ _ _hspec _; subst _hspec; dsimp only [$(spec.updateId):ident]; repeat (first | rfl | (split <;> try dsimp only))) | (cases h) | (split at h <;> try dsimp only at h))) ]

/-! ## Deferred RPC, Predict & Channel Contract Verification -/

private def elabArgExprs (argTerms : Array Term) (paramTypeConsts : Array Name) : TermElabM (Array Expr) :=
  argTerms.zipIdx.mapM fun (aT, i) => do instantiateMVars (← elabTermEnsuringType aT (Lean.mkConst paramTypeConsts[i]!))

private def captureOrigin (callRef : Syntax) (srvShort methodName : String) (argExprs : Array Expr) : TermElabM CheckOrigin :=
  return .mk callRef srvShort methodName argExprs (← getLCtx) (← getLocalInstances) (← getMCtx)

@[noinline]
private def elabAndRecordRpcLikeCheck (stx : Syntax) (expectedType? : Option Expr) (fullCall : Term)
    (fnConst : Name) (argTerms : Array Term) (paramCount : Nat) (paramTypeConsts : Array Name)
    (srvShort methodName : String) (reqConst? : Option Name) (reqLabel : String) (requiresAuth shouldRecord : Bool) : TermElabM Expr := do
  let resExpr ← instantiateMVars (← elabTerm fullCall expectedType?)
  let fnArgs := resExpr.getAppArgs
  let argExprs ← if resExpr.isAppOf fnConst && fnArgs.size ≥ 2 + paramCount then
    (Array.range paramCount).mapM fun i => instantiateMVars fnArgs[2 + i]! else elabArgExprs argTerms paramTypeConsts
  if shouldRecord then
    let origin ← captureOrigin stx srvShort methodName argExprs
    let sessionVar? := (← currentCompSessionRef.get).map (·.getId)
    pendingRpcChecks.modify (·.push (.mk origin reqConst? reqLabel requiresAuth sessionVar?))
  return resExpr

private def lookupCheckedMethod (stx : Syntax) (srvId methId : Ident) (label : String) : TermElabM (ServerInfo × ServerMethodInfo) := do
  let (srvName, methStr) := (srvId.getId, methId.getId.toString)
  let some srvInfo := (serverRegistry.getState (← getEnv)).find? srvName | throwErrorAt stx s!"internal: unknown server `{srvName}` in {label}"
  let some mInfo := srvInfo.methods.find? (·.name == methStr) | throwErrorAt stx s!"internal: unknown method `{methStr}` on `{srvName}` in {label}"
  return (srvInfo, mInfo)

@[noinline, term_elab qedCheckRpcCallTerm] def elabQedCheckRpcCall : TermElab := fun stx expectedType? => do
  let argTerms : Array Term := (stx.getArg 4).getSepArgs.map (⟨·⟩)
  let (srvInfo, mInfo) ← lookupCheckedMethod stx ⟨stx.getArg 1⟩ ⟨stx.getArg 2⟩ "RPC check"
  let fullCall ← Qed.Lang.mkAppTerms (mkIdentFrom stx mInfo.rawRpcConst) (argTerms.push ⟨stx.getArg 6⟩)
  elabAndRecordRpcLikeCheck stx expectedType? fullCall mInfo.rawRpcConst argTerms mInfo.paramCount mInfo.paramTypeConsts
    srvInfo.shortName mInfo.name mInfo.clientReqConst mInfo.clientReqLabel mInfo.requiresAuth (mInfo.hasClientReq || mInfo.requiresAuth)

@[noinline, term_elab qedCheckPredictTerm] def elabQedCheckPredict : TermElab := fun stx expectedType? => do
  let argTerms : Array Term := (stx.getArg 4).getSepArgs.map (⟨·⟩)
  let (srvInfo, mInfo) ← lookupCheckedMethod stx ⟨stx.getArg 1⟩ ⟨stx.getArg 2⟩ "predict check"
  let predExpr ← elabTerm (stx.getArg 6) expectedType?; synthesizeSyntheticMVarsNoPostponing
  let predExpr ← instantiateMVars predExpr
  if mInfo.hasEnsures then if let some ensConst := mInfo.ensPredConst then
    let origin ← captureOrigin stx srvInfo.shortName mInfo.name (← elabArgExprs argTerms mInfo.paramTypeConsts)
    let predTy ← Meta.whnf (← Meta.inferType predExpr)
    pendingPredictChecks.modify (·.push (.mk origin ensConst (mInfo.isOption && predTy.isAppOfArity ``Option 1) predExpr))
  return predExpr

@[noinline]
def verifyPendingRpcChecks (spec : ComponentSpec) (invPreds : Array Term) : CommandElabM Unit := do
  let (checks, predChecks) := (← pendingRpcChecks.get, ← pendingPredictChecks.get)
  if checks.isEmpty && predChecks.isEmpty then return
  let stateConstName ← liftCoreM <| realizeGlobalConstNoOverload spec.stateId
  let mkProofLctx (lctx : LocalContext) : LocalContext := lctx.foldl (init := {}) fun acc decl =>
    if decl.isAuxDecl then acc else match decl with
    | .ldecl _ fv nm ty val _ k => acc.mkLetDecl fv nm ty val (nondep := false) (kind := k)
    | .cdecl _ fv nm ty bi k    => acc.mkLocalDecl fv nm ty bi (kind := k)
  let buildInvProps (lctx : LocalContext) : TermElabM (Array Expr × Option Expr) := do
    let mut invProps : Array Expr := #[]; let mut stateFVar? : Option Expr := none
    let fnTy := Expr.forallE `_ (Lean.mkConst stateConstName) (Expr.sort Level.zero) .default
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isLet then
        if (← Meta.whnf decl.type).isConstOf stateConstName then
          if stateFVar?.isNone then stateFVar? := some decl.toExpr
          for predT in invPreds do
            let predExpr ← Term.elabTermEnsuringType predT fnTy; Term.synthesizeSyntheticMVarsNoPostponing
            invProps := invProps.push ((Expr.app (← instantiateMVars predExpr) decl.toExpr).headBeta)
    return (invProps, stateFVar?)
  let cleanGoalExpr (e : Expr) : MetaM String := do Qed.Diag.ppQedExpr (← Meta.zetaReduce (← instantiateMVars e)) ["m"]
  let tryDischargeWith (invProps : Array Expr) (goalBody : Expr) (tac : Tactic.TacticM Unit) (fallbackUnfold : Expr → MetaM Expr) : TermElabM (Except String (Expr × Expr)) := do
    let fullGoal ← instantiateMVars (invProps.foldr (init := goalBody) fun hyp acc => Expr.forallE `_ hyp acc .default)
    let mv ← Meta.mkFreshExprSyntheticOpaqueMVar fullGoal
    try
      let unsolved ← Tactic.run mv.mvarId! tac
      if unsolved.isEmpty then return .ok (fullGoal, mv)
      return .error (← unsolved[0]!.withContext do cleanGoalExpr (← unsolved[0]!.getType))
    catch _ => return .error (← cleanGoalExpr (← fallbackUnfold goalBody))
  let withOrigin (o : CheckOrigin) (k : LocalContext → Array Expr → Option Expr → TermElabM Unit) : CommandElabM Unit :=
    liftTermElabM do
      let proofLctx := mkProofLctx o.lctx
      Meta.withMCtx o.mctx <| withLCtx proofLctx o.localInsts do let (invProps, stateFVar?) ← buildInvProps o.lctx; k proofLctx invProps stateFVar?
  let fmtObl (obl : String) : String := if obl.isEmpty then "" else s!"\n  • must satisfy:  {obl}"
  for chk in checks do
    withOrigin chk.toCheckOrigin fun _ invProps stateFVar? => do
      let tryDischarge (g : Expr) := tryDischargeWith invProps g (do Tactic.evalTactic (← `(tactic| intros; qedProveRpcReq))) (fun e => return (← Meta.unfoldDefinition? e).getD e)
      if chk.requiresAuth then
        let some sfName := chk.sessionVar?
          | throwErrorAt chk.callRef m!"RPC `{chk.srvShort}.{chk.methodName}` requires an authenticated session (`ctx.userId != none`), but `{spec.t.getId}` has no `session` field.\n\nHint: Add `session user` to `{spec.t.getId}` and guard the call with `if user.isSome:`."
        let sfExpr : Expr ← match chk.lctx.findDecl? fun d => if !d.isImplementationDetail && d.userName.eraseMacroScopes == sfName then some d.toExpr else none with
          | some e => pure e
          | none   => let some sFVar := stateFVar? | throwErrorAt chk.callRef m!"internal: could not locate component state while checking session auth for `{chk.srvShort}.{chk.methodName}`"
                      Meta.mkProjection sFVar sfName
        let sfTy ← Meta.whnf (← Meta.inferType sfExpr)
        let elemTy := if sfTy.isAppOfArity ``Option 1 then sfTy.appArg! else Lean.mkConst ``String
        if (← tryDischarge (← Meta.mkAppM ``Ne #[sfExpr, ← Meta.mkAppOptM ``Option.none #[some elemTy]])) matches .error _ then
          throwErrorAt chk.callRef m!"RPC `{chk.srvShort}.{chk.methodName}` requires an authenticated session (`{sfName} != none`), which could not be proved here.\n\nHint: Guard this call with `if {sfName}.isSome:` or `invariant ...: {sfName}.isSome`."
      if let some reqConst := chk.reqConst? then
        if let .error obl ← tryDischarge (mkAppN (Lean.mkConst reqConst) chk.argExprs) then
          throwErrorAt chk.callRef m!"RPC `{chk.srvShort}.{chk.methodName}` precondition `{chk.reqLabel}` could not be proved here:{fmtObl obl}\n\nHint: Pass valid arguments, guard with `if ...:`, or add a component `invariant`."
  let currNs ← getCurrNamespace
  for (chk, idx) in predChecks.zipIdx do
    withOrigin chk.toCheckOrigin fun proofLctx invProps _ => do
      let ensGoal : Expr ← if chk.isOptWrap then
        let innerTy := (← Meta.whnf (← Meta.inferType chk.predExpr)).appArg!
        Meta.withLocalDeclD `_predInner innerTy fun vFVar => do
          let eqHyp ← Meta.mkEq chk.predExpr (← Meta.mkAppOptM ``Option.some #[some innerTy, some vFVar])
          Meta.mkForallFVars #[vFVar] (Expr.forallE `_hPredSome eqHyp (mkAppN (Lean.mkConst chk.ensConst) (chk.argExprs.push vFVar)) .default)
      else pure (mkAppN (Lean.mkConst chk.ensConst) (chk.argExprs.push chk.predExpr))
      let ensId := mkIdent (`_root_ ++ chk.ensConst)
      match ← tryDischargeWith invProps ensGoal (do Tactic.evalTactic (← `(tactic| intros; try simp only [$ensId:ident]; try qedProveRpcReq))) (fun e => return (← Meta.unfold e chk.ensConst).expr) with
      | .ok (fullGoal, mv) =>
          let fvars := proofLctx.foldl (init := #[]) fun acc d => if d.isAuxDecl then acc else acc.push d.toExpr
          let closedType ← instantiateMVars (← Meta.mkForallFVars (usedOnly := false) (usedLetOnly := false) fvars fullGoal)
          let closedVal ← instantiateMVars (← Meta.mkLambdaFVars (usedOnly := false) (usedLetOnly := false) fvars (← instantiateMVars mv))
          let levelParams := (collectLevelParams (collectLevelParams {} closedType) closedVal).params.toList
          Lean.addDecl (.thmDecl { name := currNs ++ spec.t.getId ++ Name.mkSimple s!"_specPredict_ens_{idx}", levelParams, type := closedType, value := closedVal })
      | .error obl =>
          throwErrorAt chk.callRef m!"Predicted response for `{chk.srvShort}.{chk.methodName}` does not satisfy server `ensures` postcondition:{fmtObl obl}\n\nHint: Ensure the predicted value satisfies the server method's `ensures` clause (or guard it inside a `predict:` block)."

@[noinline]
private def elabAndRecordChanCheck (stx : Syntax) (expectedType? : Option Expr) (label : String)
    (argTerms : Array Term) (slotTerm : Term) (trailingArgs : Array Term) (isSub : Bool) : TermElabM Expr := do
  let chFullName := (stx.getArg 1).getId
  let some chInfo := (Qed.channelRegistry.getState (← getEnv)).find? chFullName | throwErrorAt stx s!"internal: unknown channel `{chFullName}` in {label}"
  let (helperConst, paramCount, paramTypeConsts, methodName, reqConst?, reqLabel, requiresAuth) :=
    if isSub then (chInfo.subHelperConst, chInfo.paramCount, chInfo.paramTypeConsts, chInfo.channelName, chInfo.clientReqConst, chInfo.clientReqLabel, chInfo.requiresAuth)
    else (chInfo.sendHelperConst, chInfo.sendParamCount, chInfo.sendParamTypeConsts, s!"{chInfo.channelName}.send", chInfo.sendReqConst, chInfo.sendReqLabel, false)
  let fullCall ← (argTerms ++ trailingArgs).foldlM (init := ← `($(mkIdentFrom stx helperConst) $slotTerm)) fun acc a => `($acc ($a))
  elabAndRecordRpcLikeCheck stx expectedType? fullCall helperConst argTerms paramCount paramTypeConsts chInfo.ownerShort methodName reqConst? reqLabel requiresAuth (reqConst?.isSome || requiresAuth)

@[noinline, term_elab qedCheckChanSubTerm] def elabCheckChanSub : TermElab := fun stx expectedType? =>
  elabAndRecordChanCheck stx expectedType? "subscription check" ((stx.getArg 3).getSepArgs.map (⟨·⟩)) ⟨stx.getArg 5⟩ #[⟨stx.getArg 7⟩, ⟨stx.getArg 9⟩, ⟨stx.getArg 11⟩, ⟨stx.getArg 13⟩] true

@[noinline, term_elab qedCheckChanSendTerm] def elabCheckChanSend : TermElab := fun stx expectedType? =>
  elabAndRecordChanCheck stx expectedType? "send check" ((stx.getArg 3).getSepArgs.map (⟨·⟩)) ⟨stx.getArg 5⟩ #[] false

end CompElab
end Qed
