import Qed.Server.ChannelElab
import Qed.Server.JobElab
import Qed.Server.Invariant
import Qed.Resource.Basic

namespace Qed.Server
open Qed.Lang

open Lean Elab Command in
private def emitClientRpcStubs (srvName fullSrvName : Name) (srvShort fnStr : String)
    (fnIdent : Ident) (pIdents : Array Ident) (pTyTerms : Array Term)
    (payloadTerm reqTupleTy : Term) (innerOpt? : Option Term)
    (errTypeId? : Option Ident) (clientReqId? : Option Ident) (ensSpec? : Option FnEnsSpec) :
    CommandElabM (Array Name) := do
  let paramTypeConsts ← elabParamTypeAbbrevs fnIdent srvName fullSrvName fnIdent.getId "_Param_" pTyTerms

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
  let guardedRun ← wrapReqs reqPropTerms reqHypIds reqLabels initGuarded
  let bindProjBody ← (pIdents.zip projs).foldrM (init := guardedRun) fun (pid, prj) acc =>
    `(let $pid:ident := $prj; $acc)
  `(Lean.Parser.Term.matchAltExpr|
    | $fnLit =>
        match Qed.Proto.decode (α := $reqTupleTy) $reqBytesId with
        | Except.error _decErr => Pure.pure (Except.error (Qed.Server.ApiError.badRequest _decErr))
        | Except.ok $reqVar:ident => $bindProjBody)

open Lean Elab Command in
private def parseServerFnParams (fnStr : String) (hasEnsures : Bool)
    (stateFieldNames envVarNames : Array String) (rawParams : Array Syntax) :
    CommandElabM (Array ParsedFnParam × Array String) := do
  let mut fnParams : Array ParsedFnParam := #[]
  let mut paramNames : Array String := #[]
  for rp in rawParams do
    let pid : Ident := ⟨(rp.getArg 0)⟩
    let pstr := pid.getId.toString
    if pstr == "ctx" then
      throwErrorAt pid "`ctx` is already implicitly available as `RequestCtx` in every server function"
    if hasEnsures && pstr == "result" then
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
  return (fnParams, paramNames)

open Lean Elab Command in
private def elabServerFnEnsures (priorRep priorUnrep : Nat) (srvName : Name) (fnStr : String)
    (fnIdent : Ident) (stateFieldNames envVarNames paramNames : Array String)
    (pIdents : Array Ident) (pTyTerms : Array Term) (payloadTerm : Term) (innerOpt? : Option Term)
    (ensExprs : Array Syntax) : CommandElabM (Option (Option FnEnsSpec)) := do
  if ensExprs.isEmpty then return some none
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
  return some (some { ensId, postFn, labelStr := String.intercalate " && " ensLabels.toList })

open Lean Elab Command in
private def elabServerFnClause (priorRep priorUnrep : Nat)
    (srvName fullSrvName : Name) (srvShort : String) (hasState : Bool)
    (stateId stateInvId ctxId reqBytesId : Ident)
    (envIdents : Array Ident) (envTypes : Array Term)
    (stateFieldNames envVarNames : Array String)
    (dbBindings : Array (String × DatabaseInfo))
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (chanSigs : Array SrvChanSig) (existingMethods : Array ServerMethodInfo)
    (deferredProofs : IO.Ref (Array (CommandElabM Bool)))
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

  let (fnParams, paramNames) ← parseServerFnParams fnStr (!ensExprs.isEmpty) stateFieldNames envVarNames (fc.getArg 3).getSepArgs

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

  let reqs ← elabRequiresClauses fnIdent srvName fullSrvName fnIdent.getId fnStr "_hReq" "_req"
    stateFieldNames envVarNames paramNames paramNames pIdents pTyTerms reqExprs
  let some ensSpec? ← elabServerFnEnsures priorRep priorUnrep srvName fnStr fnIdent
    stateFieldNames envVarNames paramNames pIdents pTyTerms payloadTerm innerOpt? ensExprs | return none

  let hasAwait := blockHasAwait bodyStmts
  let baseCtx : LowerCtx := {
    fnName := fnStr, stateFields := stateFieldNames, envVars := envVarNames, locals := paramNames
    stateRule := if hasState then .pureStep (mkIdent `_s0) else .statelessServer
    allowAwait := hasAwait, allowUnwrap := retTy.hasFallible || innerOpt?.isSome
    hasFallible := retTy.hasFallible, isOption := innerOpt?.isSome, innerOptTy? := innerOpt?
    domainErrTy? := domainErrTyTerm?, channels := chanSigs, dbs := dbBindings
  }
  let allBinderIds := envIdents ++ #[ctxId] ++ pIdents ++ reqs.reqHypIds
  let allBinderTys := envTypes ++ #[← `(Qed.Server.RequestCtx)] ++ pTyTerms ++ reqs.reqHypTys
  let reqTupleTy ← buildTupleType pTyTerms
  let reqVar := mkIdent `_reqVal
  let projs ← extractTupleProjections reqVar pTyTerms.size
  let callArgs : Array Term := envIdents.map (⟨·.raw⟩) ++ #[⟨ctxId.raw⟩] ++ projs ++ reqs.reqHypIds.map (⟨·.raw⟩)

  let some (runExpr, isReadOnly, bodyExtRoots) ← elabServerHandler priorRep priorUnrep hasState hasAwait
      srvName fnStr fnIdent stateId stateInvId allBinderIds allBinderTys callArgs
      payloadTerm errTyTerm baseCtx bodyStmts invs mutInvs stateFieldNames envVarNames
      ensSpec? deferredProofs | return none

  let extRoots := reqs.extRoots ++ bodyExtRoots.filter (!reqs.extRoots.contains ·)
  let arm ← mkFnDispatchArm fnStr reqBytesId reqVar reqTupleTy pIdents projs
    reqs.reqPropTerms reqs.reqHypIds reqs.reqLabels domainErrTyTerm?.isSome runExpr
  let paramTypeConsts ← emitClientRpcStubs srvName fullSrvName srvShort fnStr fnIdent
    pIdents pTyTerms payloadTerm reqTupleTy innerOpt? errTypeId? reqs.clientReqId? ensSpec?

  let info : ServerMethodInfo := {
    name := fnStr
    paramNames := fnParams.map (·.ident.getId)
    paramCount := fnParams.size
    isReadOnly, isAsync := hasAwait, isFallible := retTy.hasFallible, isOption := innerOpt?.isSome
    hasClientReq := reqs.clientReqId?.isSome, requiresAuth := reqs.requiresAuth
    clientReqConst := reqs.clientReqConst?
    clientReqLabel := reqs.clientReqLabel
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
private def elabServerHttpRouteClause (priorRep priorUnrep : Nat)
    (srvName fullSrvName : Name) (hasState : Bool)
    (stateId stateInvId ctxId : Ident)
    (envIdents : Array Ident) (envTypes : Array Term)
    (stateFieldNames envVarNames : Array String)
    (dbBindings : Array (String × DatabaseInfo))
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (chanSigs : Array SrvChanSig) (routeIdx : Nat) (existingRoutes : Array (String × String))
    (deferredProofs : IO.Ref (Array (CommandElabM Bool)))
    (hc : Syntax) :
    CommandElabM (Option ((String × String) × TSyntax ``Lean.Parser.Term.matchAltExpr × Array Name)) := do
  let isStream := hc.getKind == ``srvStreamClause
  let methodStr := if isStream then "GET" else (hc.getArg 0).getId.toString.toUpper
  let pathStx := hc.getArg 1
  let pathStr := (⟨pathStx⟩ : TSyntax `str).getString
  if !pathStr.startsWith "/" then
    throwErrorAt pathStx s!"custom HTTP route path `{pathStr}` must start with `/`"
  if pathStr.startsWith "/_qed/" then
    throwErrorAt pathStx s!"custom HTTP route path `{pathStr}` cannot use reserved `/_qed/` prefix"
  if existingRoutes.any (fun (m, p) => m == methodStr && p == pathStr) then
    throwErrorAt pathStx s!"duplicate custom HTTP route `{methodStr} {pathStr}` in `server {srvName}`"

  let contractStx := hc.getArg 3
  let rawBodyStmts := (hc.getArg 4).getArgs
  let mut reqExprs : Array Syntax := #[]
  for cl in contractStx.getArgs do
    if cl.getKind == ``srvRequiresLine then
      reqExprs := reqExprs ++ (cl.getArg 1).getSepArgs
    else
      throwErrorAt cl "only `requires` contracts are supported on HTTP / `stream` routes"

  let routeLeaf := Name.mkSimple s!"_http_{routeIdx}"
  let routeIdent := mkIdentFrom pathStx routeLeaf
  let routeLabel := if isStream then s!"stream {pathStr}" else s!"{methodStr} {pathStr}"
  let bodyStmts := if isStream then ensureUnitReturn routeIdent rawBodyStmts else rawBodyStmts
  if !isStream && !blockAlwaysReturns bodyStmts then
    throwErrorAt pathStx s!"missing `return` on fallthrough path of `{routeLabel}`"

  let reqs ← elabRequiresClauses routeIdent srvName fullSrvName routeLeaf routeLabel "_hHttpReq" "_req"
    stateFieldNames envVarNames #[] #[] #[] #[] reqExprs (trackAuth := true)

  let payloadTerm : Term ←
    if isStream then `(Unit) else `(Qed.Server.HttpResponse)
  let errTyTerm : Term ← `(Qed.Server.ApiError)

  let hasAwait := blockHasAwait bodyStmts
  let baseCtx : LowerCtx := {
    fnName := routeLabel, stateFields := stateFieldNames, envVars := envVarNames, locals := #[]
    stateRule := if hasState then .pureStep (mkIdent `_s0) else .statelessServer
    allowAwait := hasAwait, allowUnwrap := true
    hasFallible := true, isOption := false, innerOptTy? := none
    domainErrTy? := none, channels := chanSigs, dbs := dbBindings
    isHttpRoute := !isStream, isStreamRoute := isStream
  }
  let allBinderIds := envIdents ++ #[ctxId] ++ reqs.reqHypIds
  let allBinderTys := envTypes ++ #[← `(Qed.Server.RequestCtx)] ++ reqs.reqHypTys
  let callArgs : Array Term := envIdents.map (⟨·.raw⟩) ++ #[⟨ctxId.raw⟩] ++ reqs.reqHypIds.map (⟨·.raw⟩)

  let some (runExpr, _, bodyExtRoots) ← elabServerHandler priorRep priorUnrep hasState hasAwait
      srvName routeLabel routeIdent stateId stateInvId allBinderIds allBinderTys callArgs
      payloadTerm errTyTerm baseCtx bodyStmts invs mutInvs stateFieldNames envVarNames
      none deferredProofs | return none

  let extRoots := reqs.extRoots ++ bodyExtRoots.filter (!reqs.extRoots.contains ·)
  let wrappedRun ←
    if isStream then
      `($runExpr >>= fun _httpRes => Pure.pure (_httpRes.map (fun _ => Option.some (Qed.Server.HttpResponse.sse []))))
    else
      `($runExpr >>= fun _httpRes => Pure.pure (_httpRes.map Option.some))
  let guardedRun ← wrapReqs reqs.reqPropTerms reqs.reqHypIds reqs.reqLabels wrappedRun
  let methodLit := Syntax.mkStrLit methodStr
  let pathLit := Syntax.mkStrLit pathStr
  let arm ← `(Lean.Parser.Term.matchAltExpr|
    | $methodLit, $pathLit => $guardedRun)
  return some ((methodStr, pathStr), arm, extRoots)

open Lean Elab Command in
private def elabServerAuthHook (priorRep priorUnrep : Nat)
    (srvName : Name) (hookLabel : String) (hookLeaf : Name) (hasState : Bool)
    (stateId stateInvId ctxId : Ident)
    (envIdents : Array Ident) (envTypes : Array Term)
    (stateFieldNames envVarNames : Array String)
    (dbBindings : Array (String × DatabaseInfo))
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (chanSigs : Array SrvChanSig) (authDecl : ParsedAuthDecl)
    (deferredProofs : IO.Ref (Array (CommandElabM Bool)))
    (hc : Syntax) :
    CommandElabM (Option (Term × Array Name)) := do
  let paramIdent : Ident := ⟨hc.getArg 2⟩
  let paramStr := paramIdent.getId.toString
  if paramStr == "ctx" then
    throwErrorAt paramIdent s!"`ctx` is already implicitly available as `RequestCtx` in `{hookLabel}`"
  if envVarNames.contains paramStr then
    throwErrorAt paramIdent s!"parameter `{paramStr}` in `{hookLabel}` shadows server `env` binding `{paramStr}`; rename the parameter"
  if stateFieldNames.contains paramStr then
    throwErrorAt paramIdent s!"parameter `{paramStr}` in `{hookLabel}` shadows server `state` field `{paramStr}`; rename the parameter"
  let hookIdent := mkIdentFrom hc hookLeaf
  let bodyStmts := ensureUnitReturn hookIdent (suiteStmts (hc.getArg 5))
  let hasAwait := blockHasAwait bodyStmts
  let isAsync := hasState && (hasAwait || blockHasAtomic bodyStmts)
  let payloadTerm : Term ← `(Unit)
  let errTyTerm : Term ← `(Qed.Server.ApiError)
  let userTyId := mkIdentFrom paramIdent (authDecl.info.authName ++ `User)
  let authUserVar := mkIdent `_authUser
  let hAuthId := mkIdent `_hAuth
  let hAuthEqId := mkIdent `_hAuthEq
  let baseCtx : LowerCtx := {
    fnName := hookLabel, stateFields := stateFieldNames, envVars := envVarNames, locals := #[paramStr]
    stateRule := if hasState then .pureStep (mkIdent `_s0) else .statelessServer
    allowAwait := if hasState then isAsync else hasAwait, allowUnwrap := true
    hasFallible := true, isOption := false, innerOptTy? := none
    domainErrTy? := none, channels := chanSigs, dbs := dbBindings
  }
  let allBinderIds := envIdents ++ #[ctxId, paramIdent, hAuthId, hAuthEqId]
  let allBinderTys := envTypes ++ #[
    ← `(Qed.Server.RequestCtx),
    ← `($userTyId),
    ← `(($ctxId).userId ≠ Option.none),
    ← `(Option.some (($paramIdent).id) = ($ctxId).userId)
  ]
  let callArgs : Array Term :=
    envIdents.map (⟨·.raw⟩) ++ #[⟨ctxId.raw⟩, ⟨authUserVar.raw⟩, ⟨hAuthId.raw⟩, ⟨hAuthEqId.raw⟩]
  let some (re, _, er) ← elabServerHandler priorRep priorUnrep hasState isAsync
      srvName hookLabel hookIdent stateId stateInvId allBinderIds allBinderTys callArgs
      payloadTerm errTyTerm baseCtx bodyStmts invs mutInvs stateFieldNames envVarNames
      none deferredProofs | return none
  return some (re, er)

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

  let deferredProofs ← IO.mkRef (#[] : Array (CommandElabM Bool))
  let mut methodInfos : Array ServerMethodInfo := #[]
  let mut dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
  let ctxId := mkIdent `ctx
  let reqBytesId := mkIdent `reqBytes

  let dbBindings : Array (String × DatabaseInfo) :=
    parsed.dbDecls.map fun d => (d.aliasIdent.getId.toString, d.info)
  for fc in parsed.fnClauses do
    let some (info, arm, er) ← elabServerFnClause priorRep priorUnrep srvName fullSrvName srvShort
        hasState stateId stateInvId ctxId reqBytesId envIdents envTypes stateFieldNames envVarNames
        dbBindings parsed.invs parsed.mutInvs chanSigs methodInfos deferredProofs fc | return
    methodInfos := methodInfos.push info
    dispatchArms := dispatchArms.push arm
    allExtRoots := allExtRoots ++ er.filter (!allExtRoots.contains ·)

  let mut wsDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
  for hdr in chanHeaders do
    let some (chArms, er) ← elabServerChannelBody priorRep priorUnrep
        srvName fullSrvName srvShort hasState stateId stateInvId ctxId
        envIdents envTypes stateFieldNames envVarNames parsed.invs parsed.mutInvs chanSigs hdr deferredProofs | return
    wsDispatchArms := wsDispatchArms ++ chArms
    allExtRoots := allExtRoots ++ er.filter (!allExtRoots.contains ·)

  let mut httpRoutes : Array (String × String) := #[]
  let mut httpDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
  for (hc, idx) in parsed.httpClauses.zipIdx do
    let some (rt, arm, er) ← elabServerHttpRouteClause priorRep priorUnrep
        srvName fullSrvName hasState stateId stateInvId ctxId
        envIdents envTypes stateFieldNames envVarNames dbBindings parsed.invs parsed.mutInvs chanSigs
        idx httpRoutes deferredProofs hc | return
    httpRoutes := httpRoutes.push rt
    httpDispatchArms := httpDispatchArms.push arm
    allExtRoots := allExtRoots ++ er.filter (!allExtRoots.contains ·)

  let some (jobNames, jobExtRoots) ← elabServerJobs priorRep priorUnrep
      srvIdent srvName hasState stateId stateInvId ctxId parsed.envDecls envIdents envTypes
      stateFieldNames envVarNames dbBindings parsed.invs parsed.mutInvs chanSigs methodInfos
      parsed.jobClauses deferredProofs | return
  allExtRoots := allExtRoots ++ jobExtRoots.filter (!allExtRoots.contains ·)

  let mut onCreateRun? : Option Term := none
  let mut onSignInRun? : Option Term := none
  if let some authDecl := parsed.authDecl? then
    if let some cc := parsed.onCreateAccountClause? then
      let some (re, er) ← elabServerAuthHook priorRep priorUnrep srvName "onCreateAccount" `_onCreateAccount
          hasState stateId stateInvId ctxId envIdents envTypes stateFieldNames envVarNames
          dbBindings parsed.invs parsed.mutInvs chanSigs authDecl deferredProofs cc | return
      onCreateRun? := some re
      allExtRoots := allExtRoots ++ er.filter (!allExtRoots.contains ·)
    if let some sc := parsed.onSignInClause? then
      let some (re, er) ← elabServerAuthHook priorRep priorUnrep srvName "onSignIn" `_onSignIn
          hasState stateId stateInvId ctxId envIdents envTypes stateFieldNames envVarNames
          dbBindings parsed.invs parsed.mutInvs chanSigs authDecl deferredProofs sc | return
      onSignInRun? := some re
      allExtRoots := allExtRoots ++ er.filter (!allExtRoots.contains ·)

  elabServerDispatchCmds srvIdent stateId initStateId stateInvId invInitId
    srvName fullSrvName srvShort hasState parsed.dbDecls parsed.envDecls allExtRoots methodInfos dispatchArms
    chanNames wsDispatchArms ctxId reqBytesId httpDispatchArms jobNames parsed.authDecl?
    onCreateRun? onSignInRun?

  -- Launch all method & channel proof theorems together in one parallel wave after all inductives/defs.
  for runProof in (← deferredProofs.get) do
    unless (← runProof) do return

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
private def snapshotTreeHasErrors : Nat → Language.SnapshotTree → Bool
  | 0, tree => tree.element.diagnostics.msgLog.hasErrors
  | fuel + 1, tree =>
      tree.element.diagnostics.msgLog.hasErrors ||
      tree.children.any fun t => snapshotTreeHasErrors fuel t.get

open Lean Elab Command in
@[command_elab serverCmd]
def elabServerCmd : CommandElab := fun stx => do
  let savedEnv ← getEnv
  let priorLog := (← get).messages
  let priorRep := priorLog.reported.size
  let priorUnrep := priorLog.unreported.size
  let priorKinds := priorLog.loggedKinds
  let priorTasks := (← get).snapshotTasks.size
  try
    elabServerCmdCore priorRep priorUnrep stx
  catch ex =>
    rollbackFailedServer savedEnv priorRep priorUnrep priorKinds
    throw ex
  let newTasks := (← get).snapshotTasks.extract priorTasks (← get).snapshotTasks.size
  let asyncErr := newTasks.any fun t => snapshotTreeHasErrors 64 t.get
  if hasNewErrors (← get).messages priorRep priorUnrep || asyncErr then
    rollbackFailedServer savedEnv priorRep priorUnrep priorKinds


end Qed.Server
