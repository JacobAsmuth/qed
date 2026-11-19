import Qed.Server.ChannelElab
import Qed.Resource.Basic

namespace Qed.Server
open Qed.Lang

open Lean Elab Command in
private def emitClientRpcStubs (srvName fullSrvName : Name) (srvShort fnStr : String)
    (fnIdent : Ident) (pIdents : Array Ident) (pTyTerms : Array Term)
    (payloadTerm reqTupleTy : Term) (innerOpt? : Option Term)
    (errTypeId? : Option Ident) (clientReqId? : Option Ident) (ensSpec? : Option FnEnsSpec) :
    CommandElabM (Array Name) := do
  let mut paramTypeConsts : Array Name := #[]
  for (pTy, i) in pTyTerms.zipIdx do
    let pTyId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter s!"_Param_{i}")
    elabCommand (← `(command| abbrev $pTyId : Type := $pTy))
    paramTypeConsts := paramTypeConsts.push (fullSrvName ++ fnIdent.getId.appendAfter s!"_Param_{i}")

  let ensPayloadTerm : Term ← match ensSpec?, innerOpt? with
    | some ensSpec, some innerTy =>
        let ensApp ← pIdents.foldlM (init := ← `($(ensSpec.ensId))) fun acc p => `($acc $p)
        `(Option (Qed.Ensured $innerTy ($ensApp)))
    | some ensSpec, none         =>
        let ensApp ← pIdents.foldlM (init := ← `($(ensSpec.ensId))) fun acc p => `($acc $p)
        `(Qed.Ensured $payloadTerm ($ensApp))
    | none, _                    => pure payloadTerm
  let clientWireRespTerm : Term ← match errTypeId? with
    | some errId => `(Except (Qed.RpcDomainError $errId) $ensPayloadTerm)
    | none       => pure ensPayloadTerm

  let outcomeId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_Outcome")
  let outcomeRhs : Term ← match errTypeId? with
    | some errId => `(Qed.RpcOutcome $errId $ensPayloadTerm)
    | none       => `(Qed.RpcSimpleOutcome $ensPayloadTerm)
  if ensSpec?.isSome then
    elabCommand (← `(command|
      set_option linter.unusedVariables false in
      abbrev $outcomeId $[($pIdents:ident : $pTyTerms:term)]* : Type := $outcomeRhs))
  else
    elabCommand (← `(command|
      abbrev $outcomeId : Type := $outcomeRhs))

  let rawRpcId := mkIdentFrom fnIdent (srvName ++ Name.mkSimple s!"_rpc_{fnStr}")
  let clientFnId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId)
  let rpcUrlLit := Syntax.mkStrLit s!"/_qed/rpc/{srvShort}/{fnStr}"
  let reqTupleVal ← liftMacroM <| buildTupleVal (pIdents.map (⟨·.raw⟩))
  elabCommand (← `(command|
    def $rawRpcId {msg cb : Type} $[($pIdents:ident : $pTyTerms:term)]*
        (onDone : cb) [Qed.RpcCallback $clientWireRespTerm msg cb] : Qed.Cmd msg :=
      Qed.Cmd.rpc (req := $reqTupleTy) (resp := $clientWireRespTerm)
        $rpcUrlLit $reqTupleVal (Qed.RpcCallback.adapt (α := $clientWireRespTerm) onDone)))

  let rawApp ← pIdents.foldlM (init := ← `($rawRpcId)) fun acc p => `($acc $p)
  let clientFnBody ← `($rawApp onDone)
  let reqBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ← match clientReqId? with
    | some reqId =>
        let reqApp ← pIdents.foldlM (init := ← `($reqId)) fun acc p => `($acc $p)
        let b ← `(bracketedBinder| (_hReq : $reqApp := by qedProveRpcReq))
        pure #[b]
    | none => pure #[]
  elabCommand (← `(command|
    set_option linter.unusedVariables false in
    def $clientFnId {msg cb : Type} $[($pIdents:ident : $pTyTerms:term)]*
        (onDone : cb) [Qed.RpcCallback $clientWireRespTerm msg cb]
        $[$reqBinders]* : Qed.Cmd msg :=
      $clientFnBody))
  return paramTypeConsts

open Lean Elab Command in
private def mkFnDispatchArm (fnStr : String) (reqBytesId reqVar : Ident)
    (reqTupleTy : Term) (pIdents : Array Ident) (projs : Array Term)
    (reqPropTerms : Array Term) (reqHypIds : Array Ident) (reqLabels : Array String)
    (hasDomainErr : Bool) (runExpr : Term) : CommandElabM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
  let fnLit := Syntax.mkStrLit fnStr
  let initGuarded ←
    if hasDomainErr then
      `($runExpr >>= fun _fnRes => Pure.pure ((Qed.Server.SrvFailure.toWire _fnRes).map Qed.Proto.encode))
    else
      `($runExpr >>= fun _fnRes => Pure.pure (_fnRes.map Qed.Proto.encode))
  let mut guardedRun := initGuarded
  for revIdx in [0:reqPropTerms.size] do
    let ri := reqPropTerms.size - 1 - revIdx
    let rCond := reqPropTerms[ri]!
    let rHyp := reqHypIds[ri]!
    let rLbl := reqLabels[ri]!
    let rMsg := Syntax.mkStrLit s!"precondition failed: {rLbl}"
    let errCtor : Term ←
      if rLbl.contains "ctx.userId" || rLbl.contains "ctx.bearerToken" || rLbl.contains "ctx.isAuthenticated" then
        `(Qed.Server.ApiError.unauthorized $rMsg)
      else
        `(Qed.Server.ApiError.badRequest $rMsg)
    guardedRun ← `(if $rHyp:ident : $rCond then $guardedRun else Pure.pure (Except.error $errCtor))
  let bindProjBody ← (pIdents.zip projs).foldrM (init := guardedRun) fun (pid, prj) acc =>
    `(let $pid:ident := $prj; $acc)
  `(Lean.Parser.Term.matchAltExpr|
    | $fnLit =>
        match Qed.Proto.decode (α := $reqTupleTy) $reqBytesId with
        | Except.error _decErr => Pure.pure (Except.error (Qed.Server.ApiError.badRequest _decErr))
        | Except.ok $reqVar:ident => $bindProjBody)

open Lean Elab Command in
private def elabServerFnClause (priorRep priorUnrep : Nat)
    (srvName fullSrvName : Name) (srvShort : String) (hasState : Bool)
    (stateId stateInvId ctxId reqBytesId : Ident)
    (envIdents : Array Ident) (envTypes : Array Term)
    (stateFieldNames envVarNames : Array String)
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (chanSigs : Array SrvChanSig) (existingMethods : Array ServerMethodInfo)
    (fc : Syntax) :
    CommandElabM (Option (ServerMethodInfo × TSyntax ``Lean.Parser.Term.matchAltExpr × Array Name)) := do
  let fnIdent : Ident := ⟨(fc.getArg 1)⟩
  let fnStr := fnIdent.getId.toString
  if existingMethods.any (·.name == fnStr) then
    throwErrorAt fnIdent s!"duplicate function `{fnStr}` in `server {srvName}`"

  let mut reqExprs : Array Syntax := #[]
  let mut ensExprs : Array Syntax := #[]
  for cl in (fc.getArg 8).getArgs do
    if cl.getKind == ``srvRequiresLine then reqExprs := reqExprs ++ (cl.getArg 1).getSepArgs
    else if cl.getKind == ``srvEnsuresLine then ensExprs := ensExprs ++ (cl.getArg 1).getSepArgs
    else throwErrorAt cl "unexpected contract clause in `def`"

  let mut fnParams : Array ParsedFnParam := #[]
  let mut paramNames : Array String := #[]
  for rp in (fc.getArg 3).getSepArgs do
    let pid : Ident := ⟨(rp.getArg 0)⟩
    let pstr := pid.getId.toString
    if pstr == "ctx" then
      throwErrorAt pid "`ctx` is already implicitly available as `RequestCtx` in every server function"
    if !ensExprs.isEmpty && pstr == "result" then
      throwErrorAt pid "`result` is reserved inside `ensures` postconditions; rename this parameter"
    if paramNames.contains pstr then
      throwErrorAt pid s!"duplicate parameter `{pstr}` in server function `{fnStr}`"
    if envVarNames.contains pstr then
      throwErrorAt pid s!"parameter `{pstr}` in `{fnStr}` shadows server `env` binding `{pstr}`; rename the parameter"
    if stateFieldNames.contains pstr then
      throwErrorAt pid s!"parameter `{pstr}` in `{fnStr}` shadows server `state` field `{pstr}`; rename the parameter"
    let pty ← liftMacroM <| ParsedSrvType.parse (rp.getArg 2)
    liftMacroM <| pty.validate (allowFallible := false) s!"parameter `{pstr}`"
    let ptyTerm ← liftMacroM pty.toPayloadTerm
    paramNames := paramNames.push pstr
    fnParams := fnParams.push { ident := pid, ty := pty, tyTerm := ptyTerm }

  let retTy ← liftMacroM <| ParsedSrvType.parse (fc.getArg 6)
  liftMacroM <| retTy.validate (allowFallible := true) s!"return type of `{fnStr}`"
  let payloadTerm ← liftMacroM retTy.toPayloadTerm
  let innerOpt? ← computeInnerOptTerm? retTy
  let isUnitPayload := (retTy.mods.filter (· != .fallible)).isEmpty && retTy.baseIdent.getId == `Unit

  let bodyStmts := if isUnitPayload then ensureUnitReturn fnIdent (fc.getArg 9).getArgs else (fc.getArg 9).getArgs
  if !isUnitPayload && !blockAlwaysReturns bodyStmts then
    throwErrorAt fnIdent s!"missing `return` on fallthrough path of `{fnStr}`"

  let (domainTagIdents, hasPlainFail) ← scanBodyFailTags bodyStmts
  if !domainTagIdents.isEmpty && hasPlainFail then
    throwErrorAt fnIdent s!"cannot mix typed `fail(.tag)` and untyped `fail(\"...\")` inside `{fnStr}`; use `fail(.tag, msg)` for all domain failures"
  if !domainTagIdents.isEmpty && !retTy.hasFallible then
    throwErrorAt fnIdent s!"`fail(.tag)` can only be returned from a fallible `T!` function (`{fnStr}` is not declared `-> ...!`)"

  let errTypeId? : Option Ident ←
    if domainTagIdents.isEmpty then pure none
    else some <$> elabDomainErrorType srvName fnIdent domainTagIdents
  if hasNewErrors (← get).messages priorRep priorUnrep then return none

  let domainErrTyTerm? : Option Term := errTypeId?.map (⟨·.raw⟩)
  let errTyTerm : Term ← match domainErrTyTerm? with
    | some et => `(Qed.Server.SrvFailure $et)
    | none    => `(Qed.Server.ApiError)

  let pIdents := fnParams.map (·.ident)
  let pTyTerms := fnParams.map (·.tyTerm)

  let mut extRoots : Array Name := #[]
  let mut reqPropTerms : Array Term := #[]
  let mut reqHypIds    : Array Ident := #[]
  let mut reqHypTys    : Array Term := #[]
  let mut reqLabels    : Array String := #[]
  let mut clientReqProps : Array Term := #[]
  let mut clientReqLabels : Array String := #[]
  let mut requiresAuth : Bool := false
  for idx in [0:reqExprs.size] do
    let rExpr := reqExprs[idx]!
    if exprHasAwait rExpr then
      throwErrorAt rExpr "`requires` precondition cannot contain `await`"
    let reqCtx : LowerCtx := {
      fnName := fnStr, stateFields := stateFieldNames, envVars := envVarNames, locals := paramNames
      stateRule := .forbidInRequires, allowAwait := false, allowUnwrap := false
      hasFallible := false, isOption := false, innerOptTy? := none
    }
    let (pTerm, rSt) ← (lowerExpr reqCtx .propGuard rExpr).run {}
    extRoots := extRoots ++ rSt.extRoots.filter (!extRoots.contains ·)
    let hId := mkIdent (Name.mkSimple s!"_hReq{idx}")
    reqPropTerms := reqPropTerms.push pTerm
    reqHypIds := reqHypIds.push hId
    reqHypTys := reqHypTys.push pTerm
    reqLabels := reqLabels.push ((rExpr.reprint.getD "requires").trimAscii.toString)

    for conj in splitSrvAnd rExpr do
      let (mentionsCtx, mentionsEnv) := scanCtxEnv envVarNames paramNames conj
      if mentionsCtx && !mentionsEnv && isAuthReqExpr conj then
        requiresAuth := true
      else if !mentionsCtx && !mentionsEnv then
        let cliReqCtx : LowerCtx := {
          fnName := fnStr, stateFields := stateFieldNames, envVars := #[], locals := paramNames
          stateRule := .forbidInRequires, allowAwait := false, allowUnwrap := false
          hasFallible := false, isOption := false, innerOptTy? := none, forbidCtxEnv := true
        }
        let (pTerm, _) ← (lowerExpr cliReqCtx .propInv conj).run {}
        clientReqProps := clientReqProps.push pTerm
        clientReqLabels := clientReqLabels.push ((conj.reprint.getD "requires").trimAscii.toString)

  let clientReqId? : Option Ident ←
    if clientReqProps.isEmpty then pure none
    else
      let cid := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_req")
      let reqConj ← buildPropConj clientReqProps
      elabCommand (← `(command|
        set_option linter.unusedVariables false in
        @[simp] abbrev $cid $[($pIdents:ident : $pTyTerms:term)]* : Prop := $reqConj))
      pure (some cid)

  let mut ensProps : Array Term := #[]
  let mut ensLabels : Array String := #[]
  for eExpr in ensExprs do
    if exprHasAwait eExpr then
      throwErrorAt eExpr "`ensures` postcondition cannot contain `await`"
    let ensCtx : LowerCtx := {
      fnName := fnStr, stateFields := stateFieldNames, envVars := envVarNames,
      locals := paramNames.push "result", stateRule := .forbidInEnsures,
      allowAwait := false, allowUnwrap := false, hasFallible := false,
      isOption := false, innerOptTy? := none, forbidCtxEnv := true
    }
    let (pTerm, _) ← (lowerExpr ensCtx .propInv eExpr).run {}
    ensProps := ensProps.push pTerm
    ensLabels := ensLabels.push ((eExpr.reprint.getD "ensures").trimAscii.toString)

  let ensSpec? : Option FnEnsSpec ←
    if ensProps.isEmpty then pure none
    else
      let ensId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_ens")
      let resTyTerm := innerOpt?.getD payloadTerm
      let resIdent := mkIdent `result
      let ensConj ← buildPropConj ensProps
      elabCommand (← `(command|
        set_option linter.unusedVariables false in
        @[simp] abbrev $ensId $[($pIdents:ident : $pTyTerms:term)]* ($resIdent:ident : $resTyTerm) : Prop :=
          $ensConj))
      if hasNewErrors (← get).messages priorRep priorUnrep then return none
      let postFn : Term → CommandElabM Term := fun outTerm => do
        let ensApp ← pIdents.foldlM (init := ← `($ensId)) fun acc p => `($acc $p)
        if innerOpt?.isSome then `(Qed.Server.srvEnsPostOpt ($ensApp) $outTerm)
        else `(Qed.Server.srvEnsPost ($ensApp) $outTerm)
      pure (some { ensId, postFn, labelStr := String.intercalate " && " ensLabels.toList })

  let hasAwait := blockHasAwait bodyStmts
  let baseCtx : LowerCtx := {
    fnName := fnStr, stateFields := stateFieldNames, envVars := envVarNames, locals := paramNames
    stateRule := if hasState then .pureStep (mkIdent `_s0) else .statelessServer
    allowAwait := hasAwait, allowUnwrap := retTy.hasFallible || innerOpt?.isSome
    hasFallible := retTy.hasFallible, isOption := innerOpt?.isSome, innerOptTy? := innerOpt?
    domainErrTy? := domainErrTyTerm?, channels := chanSigs
  }
  let allBinderIds := envIdents ++ #[ctxId] ++ pIdents ++ reqHypIds
  let allBinderTys := envTypes ++ #[← `(Qed.Server.RequestCtx)] ++ pTyTerms ++ reqHypTys
  let reqTupleTy ← buildTupleType pTyTerms
  let reqVar := mkIdent `_reqVal
  let projs ← extractTupleProjections reqVar pTyTerms.size
  let callArgs : Array Term := envIdents.map (⟨·.raw⟩) ++ #[⟨ctxId.raw⟩] ++ projs ++ reqHypIds.map (⟨·.raw⟩)

  let (runExpr, isReadOnly, bodyExtRoots) ←
    if hasState && !hasAwait then
      let some r ← elabServerPureFn priorRep priorUnrep srvName fnStr fnIdent stateId stateInvId
          allBinderIds allBinderTys callArgs payloadTerm errTyTerm baseCtx bodyStmts
          invs mutInvs stateFieldNames envVarNames ensSpec? | return none
      pure r
    else if hasState && hasAwait then
      let some r ← elabServerAsyncFn priorRep priorUnrep srvName fnStr fnIdent stateId stateInvId
          allBinderIds allBinderTys callArgs payloadTerm errTyTerm baseCtx bodyStmts
          invs mutInvs stateFieldNames envVarNames ensSpec? | return none
      pure r
    else
      let (statelessBody, lSt) ← (lowerAsyncBlock baseCtx none bodyStmts).run {}
      let handlerId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_handler")
      elabCommand (← `(command|
        def $handlerId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m]
            $[($allBinderIds:ident : $allBinderTys:term)]* :
            m (Except $errTyTerm $payloadTerm) :=
          Qed.Server.srvFinishM $statelessBody))
      if hasNewErrors (← get).messages priorRep priorUnrep then return none
      let hCall ← allBinderIds.foldlM (init := ← `($handlerId)) fun acc a => `($acc $a)
      if let some ensSpec := ensSpec? then
        unless (← elabAsyncEnsuresThm priorRep priorUnrep srvName fnStr fnIdent handlerId
            (← `(fun _ : Unit => True)) (← `(Unit)) payloadTerm errTyTerm
            allBinderIds allBinderTys hCall #[] ensSpec) do
          return none
      let hApp ← callArgs.foldlM (init := ← `($handlerId)) fun acc a => `($acc $a)
      pure (hApp, true, lSt.extRoots)

  extRoots := extRoots ++ bodyExtRoots.filter (!extRoots.contains ·)
  let arm ← mkFnDispatchArm fnStr reqBytesId reqVar reqTupleTy pIdents projs
    reqPropTerms reqHypIds reqLabels domainErrTyTerm?.isSome runExpr
  let paramTypeConsts ← emitClientRpcStubs srvName fullSrvName srvShort fnStr fnIdent
    pIdents pTyTerms payloadTerm reqTupleTy innerOpt? errTypeId? clientReqId? ensSpec?

  let info : ServerMethodInfo := {
    name := fnStr
    paramNames := fnParams.map (·.ident.getId)
    paramCount := fnParams.size
    isReadOnly, isAsync := hasAwait, isFallible := retTy.hasFallible, isOption := innerOpt?.isSome
    hasClientReq := clientReqId?.isSome, requiresAuth
    clientReqConst := clientReqId?.map fun _ => fullSrvName ++ fnIdent.getId.appendAfter "_req"
    clientReqLabel := String.intercalate " && " clientReqLabels.toList
    hasEnsures := ensSpec?.isSome
    ensPredConst := ensSpec?.map fun _ => fullSrvName ++ fnIdent.getId.appendAfter "_ens"
    domainErrTags := domainTagIdents.map (·.getId.toString)
    errTypeConst := errTypeId?.map fun _ => fullSrvName ++ fnIdent.getId ++ `Error
    rawRpcConst := fullSrvName ++ Name.mkSimple s!"_rpc_{fnStr}"
    outcomeConst := fullSrvName ++ fnIdent.getId.appendAfter "_Outcome"
    paramTypeConsts
  }
  return some (info, arm, extRoots)

open Lean Elab Command in
private def elabServerCmdCore (priorRep priorUnrep : Nat) : CommandElab := fun stx => do
  let srvIdent : Ident := ⟨(stx.getArg 1)⟩
  let srvName := srvIdent.getId
  let srvShort := srvName.toString
  let fullSrvName := (← getCurrNamespace) ++ srvName
  let parsed ← parseServerClauses srvIdent srvName (stx.getArg 3).getArgs
  let hasState := !parsed.stateDecls.isEmpty
  let stateFieldNames := parsed.stateDecls.map (·.ident.getId.toString)
  let envVarNames := parsed.envDecls.map (·.ident.getId.toString)
  let envIdents := parsed.envDecls.map (·.ident)
  let envStrType ← `(String)
  let envTypes := parsed.envDecls.map fun _ => envStrType
  let stateId := mkIdentFrom srvIdent (srvName ++ `State)
  let initStateId := mkIdentFrom srvIdent (srvName ++ `initState)
  let stateInvId := mkIdentFrom srvIdent (srvName ++ `StateInv)
  let invInitId := mkIdentFrom srvIdent (srvName ++ `inv_init)

  if hasState then
    unless (← elabServerStateCmds priorRep priorUnrep stateId initStateId stateInvId invInitId
        parsed.stateDecls parsed.invs stateFieldNames envVarNames) do
      return

  let mut chanHeaders : Array ParsedChanHeader := #[]
  let mut chanSigs : Array SrvChanSig := #[]
  let mut chanNames : Array String := #[]
  let mut allExtRoots : Array Name := #[]
  for cc in parsed.chanClauses do
    let some (hdr, er) ← elabServerChannelHeader priorRep priorUnrep srvName fullSrvName
        stateFieldNames envVarNames chanNames cc | return
    chanHeaders := chanHeaders.push hdr
    chanSigs := chanSigs.push hdr.sig
    chanNames := chanNames.push hdr.chStr
    allExtRoots := allExtRoots ++ er.filter (!allExtRoots.contains ·)

  let mut methodInfos : Array ServerMethodInfo := #[]
  let mut dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
  let ctxId := mkIdent `ctx
  let reqBytesId := mkIdent `reqBytes

  for fc in parsed.fnClauses do
    let some (info, arm, er) ← elabServerFnClause priorRep priorUnrep srvName fullSrvName srvShort
        hasState stateId stateInvId ctxId reqBytesId envIdents envTypes stateFieldNames envVarNames
        parsed.invs parsed.mutInvs chanSigs methodInfos fc | return
    methodInfos := methodInfos.push info
    dispatchArms := dispatchArms.push arm
    allExtRoots := allExtRoots ++ er.filter (!allExtRoots.contains ·)

  let mut wsDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
  for hdr in chanHeaders do
    let some (chArms, er) ← elabServerChannelBody priorRep priorUnrep
        srvName fullSrvName srvShort hasState stateId stateInvId ctxId
        envIdents envTypes stateFieldNames envVarNames parsed.invs parsed.mutInvs chanSigs hdr | return
    wsDispatchArms := wsDispatchArms ++ chArms
    allExtRoots := allExtRoots ++ er.filter (!allExtRoots.contains ·)

  elabServerDispatchCmds srvIdent stateId initStateId stateInvId invInitId
    srvName fullSrvName srvShort hasState parsed.envDecls allExtRoots methodInfos dispatchArms
    chanNames wsDispatchArms ctxId reqBytesId

open Lean Elab Command in
private def rollbackFailedServer (savedEnv : Environment)
    (priorRep priorUnrep : Nat) (priorKinds : Lean.NameSet) : CommandElabM Unit := do
  setEnv savedEnv
  modify fun s =>
    let m := s.messages
    { s with messages := {
        reported    := filterNewWarnings m.reported priorRep
        unreported  := filterNewWarnings m.unreported priorUnrep
        loggedKinds := priorKinds
      } }

open Lean Elab Command in
@[command_elab serverCmd]
def elabServerCmd : CommandElab := fun stx => do
  let savedEnv ← getEnv
  let priorLog := (← get).messages
  let priorRep := priorLog.reported.size
  let priorUnrep := priorLog.unreported.size
  let priorKinds := priorLog.loggedKinds
  try
    withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) do
      elabServerCmdCore priorRep priorUnrep stx
  catch ex =>
    rollbackFailedServer savedEnv priorRep priorUnrep priorKinds
    throw ex
  if hasNewErrors (← get).messages priorRep priorUnrep then
    rollbackFailedServer savedEnv priorRep priorUnrep priorKinds


end Qed.Server
