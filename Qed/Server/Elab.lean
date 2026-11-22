import Qed.Server.ChannelElab
import Qed.Server.JobElab
import Qed.Server.Invariant
import Qed.Resource.Basic

namespace Qed.Server
open Qed.Lang

section ServerElab
open Lean Elab Command

private def emitClientRpcStubs (fnStr : String) (fnIdent : Ident)
    (pIdents : Array Ident) (pTyTerms : Array Term) (payloadTerm reqTupleTy : Term)
    (innerOpt? : Option Term) (errTypeId? : Option Ident)
    (clientReqId? : Option Ident) (ensSpec? : Option FnEnsSpec) : SrvElabM (Array Name) := do
  let c ← read
  let paramTypeConsts ← liftM <| elabParamTypeAbbrevs fnIdent c.srvName c.fullSrvName fnIdent.getId "_Param_" pTyTerms

  let pTerms : Array Term := pIdents.map (⟨·.raw⟩)
  let ensPayloadTerm : Term ← match ensSpec? with
    | some ensSpec =>
        let ensApp ← mkAppTerms ensSpec.ensId pTerms
        match innerOpt? with
        | some innerTy => `(Option (Qed.Ensured $innerTy ($ensApp)))
        | none         => `(Qed.Ensured $payloadTerm ($ensApp))
    | none => pure payloadTerm
  let clientWireRespTerm : Term ← match errTypeId? with
    | some errId => `(Except (Qed.RpcDomainError $errId) $ensPayloadTerm)
    | none       => pure ensPayloadTerm

  let outcomeId := mkIdentFrom fnIdent (c.srvName ++ fnIdent.getId.appendAfter "_Outcome")
  let outcomeRhs : Term ← match errTypeId? with
    | some errId => `(Qed.RpcOutcome $errId $ensPayloadTerm)
    | none       => `(Qed.RpcSimpleOutcome $ensPayloadTerm)
  if ensSpec?.isSome then
    liftM <| elabCommand (← `(command|
      set_option linter.unusedVariables false in
      abbrev $outcomeId $[($pIdents:ident : $pTyTerms:term)]* : Type := $outcomeRhs))
  else
    liftM <| elabCommand (← `(command| abbrev $outcomeId : Type := $outcomeRhs))

  let rawRpcId := mkIdentFrom fnIdent (c.srvName ++ Name.mkSimple s!"_rpc_{fnStr}")
  let clientFnId := mkIdentFrom fnIdent (c.srvName ++ fnIdent.getId)
  let rpcUrlLit := Syntax.mkStrLit s!"/_qed/rpc/{c.srvShort}/{fnStr}"
  let reqTupleVal ← liftMacroM <| buildTupleVal pTerms
  liftM <| elabCommand (← `(command|
    def $rawRpcId {msg cb : Type} $[($pIdents:ident : $pTyTerms:term)]*
        (onDone : cb) [Qed.RpcCallback $clientWireRespTerm msg cb] : Qed.Cmd msg :=
      Qed.Cmd.rpc (req := $reqTupleTy) (resp := $clientWireRespTerm)
        $rpcUrlLit $reqTupleVal (Qed.RpcCallback.adapt (α := $clientWireRespTerm) onDone)))

  let rawApp ← mkAppTerms rawRpcId pTerms
  let reqBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ← match clientReqId? with
    | some reqId =>
        let reqApp ← mkAppTerms reqId pTerms
        pure #[← `(bracketedBinder| (_hReq : $reqApp := by qedProveRpcReq))]
    | none => pure #[]
  liftM <| elabCommand (← `(command|
    set_option linter.unusedVariables false in
    def $clientFnId {msg cb : Type} $[($pIdents:ident : $pTyTerms:term)]*
        (onDone : cb) [Qed.RpcCallback $clientWireRespTerm msg cb]
        $[$reqBinders]* : Qed.Cmd msg :=
      $rawApp onDone))
  return paramTypeConsts

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
  let guardedRun ← wrapReqs reqPropTerms reqHypIds reqLabels initGuarded
  let decoded ← mkProtoDecodeBind reqBytesId reqVar reqTupleTy pIdents projs guardedRun
  `(Lean.Parser.Term.matchAltExpr| | $fnLit => $decoded)

private def elabServerFnClause (existingMethods : Array ServerMethodInfo) (fc : Syntax) :
    SrvElabM (Option (ServerMethodInfo × TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let c ← read
  let fnIdent : Ident := ⟨(fc.getArg 1)⟩
  let fnStr := fnIdent.getId.toString
  if existingMethods.any (·.name == fnStr) then
    throwErrorAt fnIdent s!"duplicate function `{fnStr}` in `server {c.srvName}`"

  let mut reqExprs : Array Syntax := #[]
  let mut ensExprs : Array Syntax := #[]
  for cl in (fc.getArg 8).getArgs do
    if cl.getKind == ``srvRequiresLine then reqExprs := reqExprs ++ (cl.getArg 1).getSepArgs
    else if cl.getKind == ``srvEnsuresLine then ensExprs := ensExprs ++ (cl.getArg 1).getSepArgs
    else throwErrorAt cl "unexpected contract clause in `def`"

  let (pIdents, pTyTerms, paramNames) ←
    parseSrvParams s!"server function `{fnStr}`" "parameter" (fc.getArg 3).getSepArgs
      (reserved := if ensExprs.isEmpty then #[] else #["result"])

  let retTy ← liftMacroM <| lowerSrvType (fc.getArg 6) (allowFallible := true) s!"return type of `{fnStr}`"
  let payloadTerm := retTy.term
  let innerOpt? := retTy.innerOpt?
  let isUnitPayload := (retTy.mods.filter (· != .fallible)).isEmpty && retTy.baseName == `Unit

  let bodyStmts := if isUnitPayload then ensureUnitReturn fnIdent (fc.getArg 9).getArgs else (fc.getArg 9).getArgs
  if !isUnitPayload && !blockAlwaysReturns bodyStmts then
    throwErrorAt fnIdent s!"missing `return` on fallthrough path of `{fnStr}`"

  let (domainTagIdents, hasPlainFail) ← liftM <| scanBodyFailTags bodyStmts
  if !domainTagIdents.isEmpty && hasPlainFail then
    throwErrorAt fnIdent s!"cannot mix typed `fail(.tag)` and untyped `fail(\"...\")` inside `{fnStr}`; use `fail(.tag, msg)` for all domain failures"
  if !domainTagIdents.isEmpty && !retTy.isFallible then
    throwErrorAt fnIdent s!"`fail(.tag)` can only be returned from a fallible `T!` function (`{fnStr}` is not declared `-> ...!`)"

  let errTypeId? : Option Ident ←
    if domainTagIdents.isEmpty then pure none
    else some <$> elabDomainErrorType fnIdent domainTagIdents
  if (← hasSrvErrors) then return none

  let domainErrTyTerm? : Option Term := errTypeId?.map (⟨·.raw⟩)
  let errTyTerm : Term ← match domainErrTyTerm? with
    | some et => `(Qed.Server.SrvFailure $et)
    | none    => `(Qed.Server.ApiError)

  let reqs ← elabRequiresClauses fnIdent fnIdent.getId fnStr "_hReq" "_req"
    paramNames paramNames pIdents pTyTerms reqExprs
  let some ensRes? ← elabEnsuresAbbrev fnIdent fnStr `result paramNames pIdents pTyTerms
      (innerOpt?.getD payloadTerm) ensExprs | return none
  let ensSpec? : Option FnEnsSpec := ensRes?.map fun (ensId, _, labelStr) => {
    ensId, labelStr
    postFn := fun outTerm => do
      let ensApp ← mkAppTerms ensId (pIdents.map (⟨·.raw⟩))
      if innerOpt?.isSome then `(Qed.Server.srvEnsPostOpt ($ensApp) $outTerm)
      else `(Qed.Server.srvEnsPost ($ensApp) $outTerm)
  }

  let hasAwait := blockHasAwait bodyStmts
  let baseCtx ← mkBaseLowerCtx fnStr paramNames hasAwait (retTy.isFallible || innerOpt?.isSome)
    retTy.isFallible innerOpt? domainErrTyTerm?
  let reqTupleTy ← liftMacroM <| buildProdType pTyTerms
  let reqVar := mkIdent `_reqVal
  let projs ← extractTupleProjections reqVar pTyTerms.size
  let some (runExpr, isReadOnly, _) ← elabServerHandler hasAwait fnStr fnIdent
      (pIdents ++ reqs.reqHypIds) (pTyTerms ++ reqs.reqHypTys) (projs ++ reqs.reqHypIds.map (⟨·.raw⟩))
      payloadTerm errTyTerm baseCtx bodyStmts ensSpec? | return none

  let arm ← liftM <| mkFnDispatchArm fnStr c.reqBytesId reqVar reqTupleTy pIdents projs
    reqs.reqPropTerms reqs.reqHypIds reqs.reqLabels domainErrTyTerm?.isSome runExpr
  let paramTypeConsts ← emitClientRpcStubs fnStr fnIdent
    pIdents pTyTerms payloadTerm reqTupleTy innerOpt? errTypeId? reqs.clientReqId? ensSpec?

  let info : ServerMethodInfo := {
    name := fnStr, paramNames := pIdents.map (·.getId), paramCount := pIdents.size
    isReadOnly, isAsync := hasAwait, isFallible := retTy.isFallible, isOption := innerOpt?.isSome
    hasClientReq := reqs.clientReqId?.isSome, requiresAuth := reqs.requiresAuth
    clientReqConst := reqs.clientReqConst?, clientReqLabel := reqs.clientReqLabel
    hasEnsures := ensSpec?.isSome
    ensPredConst := ensRes?.map (·.2.1)
    domainErrTags := domainTagIdents.map (·.getId.toString)
    rawRpcConst := c.fullSrvName ++ Name.mkSimple s!"_rpc_{fnStr}"
    outcomeConst := c.fullSrvName ++ fnIdent.getId.appendAfter "_Outcome"
    paramTypeConsts
  }
  return some (info, arm)

private def elabServerHttpRouteClause (routeIdx : Nat) (existingRoutes : Array (String × String)) (hc : Syntax) :
    SrvElabM (Option ((String × String) × TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let c ← read
  let isStream := hc.getKind == ``srvStreamClause
  let methodStr := if isStream then "GET" else (hc.getArg 0).getId.toString.toUpper
  let pathStx := hc.getArg 1
  let pathStr := (⟨pathStx⟩ : TSyntax `str).getString
  if !pathStr.startsWith "/" then
    throwErrorAt pathStx s!"custom HTTP route path `{pathStr}` must start with `/`"
  if pathStr.startsWith "/_qed/" then
    throwErrorAt pathStx s!"custom HTTP route path `{pathStr}` cannot use reserved `/_qed/` prefix"
  if existingRoutes.any (fun (m, p) => m == methodStr && p == pathStr) then
    throwErrorAt pathStx s!"duplicate custom HTTP route `{methodStr} {pathStr}` in `server {c.srvName}`"

  let mut reqExprs : Array Syntax := #[]
  for cl in (hc.getArg 3).getArgs do
    if cl.getKind == ``srvRequiresLine then reqExprs := reqExprs ++ (cl.getArg 1).getSepArgs
    else throwErrorAt cl "only `requires` contracts are supported on HTTP / `stream` routes"

  let routeLeaf := Name.mkSimple s!"_http_{routeIdx}"
  let routeIdent := mkIdentFrom pathStx routeLeaf
  let routeLabel := if isStream then s!"stream {pathStr}" else s!"{methodStr} {pathStr}"
  let rawBodyStmts := (hc.getArg 4).getArgs
  let bodyStmts := if isStream then ensureUnitReturn routeIdent rawBodyStmts else rawBodyStmts
  if !isStream && !blockAlwaysReturns bodyStmts then
    throwErrorAt pathStx s!"missing `return` on fallthrough path of `{routeLabel}`"

  let reqs ← elabRequiresClauses routeIdent routeLeaf routeLabel "_hHttpReq" "_req"
    #[] #[] #[] #[] reqExprs (trackAuth := true)

  let payloadTerm : Term ← if isStream then `(Unit) else `(Qed.Server.HttpResponse)
  let errTyTerm : Term ← `(Qed.Server.ApiError)
  let hasAwait := blockHasAwait bodyStmts
  let baseCtx ← mkBaseLowerCtx routeLabel #[] hasAwait true true (isHttpRoute := !isStream) (isStreamRoute := isStream)
  let some (runExpr, _, _) ← elabServerHandler hasAwait routeLabel routeIdent
      reqs.reqHypIds reqs.reqHypTys (reqs.reqHypIds.map (⟨·.raw⟩))
      payloadTerm errTyTerm baseCtx bodyStmts none | return none

  let wrappedRun ← if isStream then
      `($runExpr >>= fun _httpRes => Pure.pure (_httpRes.map (fun _ => Option.some (Qed.Server.HttpResponse.sse []))))
    else
      `($runExpr >>= fun _httpRes => Pure.pure (_httpRes.map Option.some))
  let guardedRun ← liftM <| wrapReqs reqs.reqPropTerms reqs.reqHypIds reqs.reqLabels wrappedRun
  let arm ← `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkStrLit methodStr), $(Syntax.mkStrLit pathStr) => $guardedRun)
  return some ((methodStr, pathStr), arm)

private def elabServerAuthHook (hookLabel : String) (hookLeaf : Name)
    (authDecl : ParsedAuthDecl) (hc : Syntax) : SrvElabM (Option Term) := do
  let c ← read
  let paramIdent : Ident := ⟨hc.getArg 2⟩
  let paramStr ← checkSrvParamName s!"`{hookLabel}`" paramIdent
  let hookIdent := mkIdentFrom hc hookLeaf
  let bodyStmts := ensureUnitReturn hookIdent (suiteStmts (hc.getArg 5))
  let hasAwait := blockHasAwait bodyStmts
  let isAsync := c.hasState && (hasAwait || blockHasAtomic bodyStmts)
  let userTyId := mkIdentFrom paramIdent (authDecl.info.authName ++ `User)
  let (authUserVar, hAuthId, hAuthEqId) := (mkIdent `_authUser, mkIdent `_hAuth, mkIdent `_hAuthEq)
  let baseCtx ← mkBaseLowerCtx hookLabel #[paramStr] (if c.hasState then isAsync else hasAwait) true true
  let extraBinderTys : Array Term := #[
    ← `($userTyId), ← `(($(c.ctxId)).userId ≠ Option.none),
    ← `(Option.some (($paramIdent).id) = ($(c.ctxId)).userId)
  ]
  let some (re, _, _) ← elabServerHandler isAsync hookLabel hookIdent
      #[paramIdent, hAuthId, hAuthEqId] extraBinderTys #[⟨authUserVar.raw⟩, ⟨hAuthId.raw⟩, ⟨hAuthEqId.raw⟩]
      (← `(Unit)) (← `(Qed.Server.ApiError)) baseCtx bodyStmts none | return none
  return some re

private def elabServerCmdCore (priorRep priorUnrep : Nat) : CommandElab := fun stx => do
  let srvIdent : Ident := ⟨(stx.getArg 1)⟩
  let srvName := srvIdent.getId
  let parsed ← parseServerClauses srvIdent srvName (stx.getArg 3).getArgs
  let envStrType ← `(String)
  let initCtx : SrvElabCtx := {
    priorRep, priorUnrep, srvIdent, srvName
    fullSrvName := (← getCurrNamespace) ++ srvName
    srvShort := srvName.toString
    hasState := !parsed.stateDecls.isEmpty
    stateId := mkIdentFrom srvIdent (srvName ++ `State)
    initStateId := mkIdentFrom srvIdent (srvName ++ `initState)
    stateInvId := mkIdentFrom srvIdent (srvName ++ `StateInv)
    invInitId := mkIdentFrom srvIdent (srvName ++ `inv_init)
    ctxId := mkIdent `ctx, reqBytesId := mkIdent `reqBytes
    dbDecls := parsed.dbDecls
    dbBindings := parsed.dbDecls.map fun d => (d.aliasIdent.getId.toString, d.info)
    authDecl? := parsed.authDecl?
    envDecls := parsed.envDecls
    envIdents := parsed.envDecls.map (·.ident)
    envTypes := parsed.envDecls.map fun _ => envStrType
    stateFieldNames := parsed.stateDecls.map (·.ident.getId.toString)
    envVarNames := parsed.envDecls.map (·.ident.getId.toString)
    invs := parsed.invs, mutInvs := parsed.mutInvs
    deferredProofs := ← IO.mkRef #[]
    extRootsRef := ← IO.mkRef #[]
  }
  (do
    if initCtx.hasState then
      unless (← elabServerStateCmds parsed.stateDecls) do return

    let mut chanHeaders : Array ParsedChanHeader := #[]
    let mut chanSigs : Array SrvChanSig := #[]
    let mut chanNames : Array String := #[]
    for cc in parsed.chanClauses do
      let some hdr ← elabServerChannelHeader chanNames cc | return
      chanHeaders := chanHeaders.push hdr
      chanSigs := chanSigs.push hdr.sig
      chanNames := chanNames.push hdr.chStr

    withReader (fun (c : SrvElabCtx) => { c with chanSigs }) do
      let mut methodInfos : Array ServerMethodInfo := #[]
      let mut dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
      for fc in parsed.fnClauses do
        let some (info, arm) ← elabServerFnClause methodInfos fc | return
        methodInfos := methodInfos.push info
        dispatchArms := dispatchArms.push arm

      let mut wsDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
      for hdr in chanHeaders do
        let some chArms ← elabServerChannelBody hdr | return
        wsDispatchArms := wsDispatchArms ++ chArms

      let mut httpRoutes : Array (String × String) := #[]
      let mut httpDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
      for (hc, idx) in parsed.httpClauses.zipIdx do
        let some (rt, arm) ← elabServerHttpRouteClause idx httpRoutes hc | return
        httpRoutes := httpRoutes.push rt
        httpDispatchArms := httpDispatchArms.push arm

      let some jobNames ← elabServerJobs methodInfos parsed.jobClauses | return

      let mut onCreateRun? : Option Term := none
      let mut onSignInRun? : Option Term := none
      if let some authDecl := parsed.authDecl? then
        if let some cc := parsed.onCreateAccountClause? then
          let some re ← elabServerAuthHook "onCreateAccount" `_onCreateAccount authDecl cc | return
          onCreateRun? := some re
        if let some sc := parsed.onSignInClause? then
          let some re ← elabServerAuthHook "onSignIn" `_onSignIn authDecl sc | return
          onSignInRun? := some re

      elabServerDispatchCmds methodInfos dispatchArms chanNames wsDispatchArms
        httpDispatchArms jobNames onCreateRun? onSignInRun?
  ).run initCtx

  -- Launch all method & channel proof theorems together in one parallel wave after all inductives/defs.
  for runProof in (← initCtx.deferredProofs.get) do
    unless (← runProof) do return

private def rollbackFailedServer (savedEnv : Environment)
    (priorRep priorUnrep : Nat) (priorKinds : NameSet) : CommandElabM Unit := do
  setEnv savedEnv
  modify fun s =>
    let m := s.messages
    { s with messages := {
        reported    := filterNewWarnings m.reported priorRep
        unreported  := filterNewWarnings m.unreported priorUnrep
        loggedKinds := priorKinds
      } }

@[command_elab serverCmd]
def elabServerCmd : CommandElab := fun stx => do
  let savedEnv ← getEnv
  let priorLog := (← get).messages
  let (priorRep, priorUnrep, priorKinds) := (priorLog.reported.size, priorLog.unreported.size, priorLog.loggedKinds)
  let priorTasks := (← get).snapshotTasks.size
  try
    elabServerCmdCore priorRep priorUnrep stx
  catch ex =>
    rollbackFailedServer savedEnv priorRep priorUnrep priorKinds
    throw ex
  let newTasks := (← get).snapshotTasks.extract priorTasks (← get).snapshotTasks.size
  let asyncErr := newTasks.any fun t => Qed.Diag.snapshotTreeHasErrors 64 t.get
  if hasNewErrors (← get).messages priorRep priorUnrep || asyncErr then
    rollbackFailedServer savedEnv priorRep priorUnrep priorKinds

end ServerElab

end Qed.Server
