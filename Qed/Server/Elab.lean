import Qed.Server.FnElab
import Qed.Server.Invariant
import Qed.Runtime.Cmd
import Qed.Resource.Basic
import Qed.Ssr
import Qed.Socket
import Qed.Component.Syntax

namespace Qed.Server
open Qed.Lang

/-! ## WebSocket `channel` Elaborator -/

private structure ParsedChanHeader where
  chIdent         : Lean.Ident
  chName          : Lean.Name
  chStr           : String
  pIdents         : Array Lean.Ident
  pTyTerms        : Array Lean.Term
  paramNames      : Array String
  paramTypeConsts : Array Lean.Name
  evTyTerm        : Lean.Term
  reqs            : LoweredRequires
  ensId?          : Option Lean.Ident
  ensConst?       : Option Lean.Name
  recPolicy       : Qed.Reconnect
  onJoin?         : Option (Option Lean.Syntax × Array Lean.Syntax)
  onSend?         : Option (Array Lean.Syntax × Array Lean.Syntax × Array Lean.Syntax)
  onLeave?        : Option (Array Lean.Syntax)
  sig             : SrvChanSig

section ServerFullElab
open Lean Elab Command

@[noinline]
private def elabServerChannelHeader (existingChanNames : Array String) (chStx : Syntax) : SrvElabM (Option ParsedChanHeader) := do
  let c ← read; let chIdent : Ident := ⟨chStx.getArg 1⟩; let chName := chIdent.getId; let chStr := chName.toString
  if existingChanNames.contains chStr then throwErrorAt chIdent s!"duplicate `channel {chStr}` in `server {c.srvName}`"
  let (pIdents, pTyTerms, paramNames) ← parseSrvParams s!"`channel {chStr}`" "channel parameter" (chStx.getArg 3).getSepArgs (reserved := #["event"])
  let evTyTerm := (← liftMacroM <| lowerSrvType (chStx.getArg 6) false s!"event type of `channel {chStr}`").term
  let mut reqExprs : Array Syntax := #[]; let mut ensExprs : Array Syntax := #[]; let mut recPolicy : Qed.Reconnect := .defaultPolicy
  let mut hasRec := false; let mut onJoin? : Option (Option Syntax × Array Syntax) := none
  let mut onSend? : Option (Array Syntax × Array Syntax × Array Syntax) := none; let mut onLeave? : Option (Array Syntax) := none
  if (chStx.getArg 7).getNumArgs == 2 then
    for sub in ((chStx.getArg 7).getArg 1).getArgs do
      let sk := sub.getKind
      if sk == ``srvChanReqClause then reqExprs := reqExprs ++ ((sub.getArg 0).getArg 1).getSepArgs
      else if sk == ``srvChanEnsClause then ensExprs := ensExprs ++ ((sub.getArg 0).getArg 1).getSepArgs
      else if sk == ``srvChanReconnectClause then
        if hasRec then throwErrorAt sub s!"duplicate `reconnect` clause in `channel {chStr}`"
        hasRec := true; recPolicy ← liftMacroM <| Qed.parseReconnectExpr (sub.getArg 1)
      else if sk == ``srvChanOnJoinClause then
        if onJoin?.isSome then throwErrorAt sub s!"duplicate `on_join` in `channel {chStr}`"
        onJoin? := some (if (sub.getArg 1).getNumArgs == 2 then some ((sub.getArg 1).getArg 1) else none, suiteStmts (sub.getArg 3))
      else if sk == ``srvChanOnSendClause then
        if onSend?.isSome then throwErrorAt sub s!"duplicate `on_send` in `channel {chStr}`"
        onSend? := some ((sub.getArg 2).getSepArgs, (sub.getArg 5).getArgs.flatMap fun rl => (rl.getArg 1).getSepArgs, (sub.getArg 6).getArgs)
      else if sk == ``srvChanOnLeaveClause then
        if onLeave?.isSome then throwErrorAt sub s!"duplicate `on_leave` in `channel {chStr}`"
        onLeave? := some (suiteStmts (sub.getArg 2))
      else throwErrorAt sub s!"unexpected clause in `channel {chStr}`"
  let evId := c.fnSubId chIdent "_Event"
  elabSrvCmd (← `(command| abbrev $evId : Type := $evTyTerm))
  let paramTypeConsts ← liftM <| elabParamTypeAbbrevs chIdent c.srvName c.fullSrvName chName "_Param_" pTyTerms
  let reqs ← elabRequiresClauses chIdent chName chStr "_hChReq" "_req" paramNames paramNames pIdents pTyTerms reqExprs
  let some ensRes? ← elabEnsuresAbbrev chIdent chStr `event paramNames pIdents pTyTerms evTyTerm ensExprs | return none
  let (ensId?, ensConst?) : Option Ident × Option Name := (ensRes?.map (·.1), ensRes?.map (·.2.1))
  let mkEmitId := c.fnSubId chIdent "_mkEmit"; let evVar := mkIdent `_ev
  let paramTupleVal ← liftMacroM <| buildTupleVal (pIdents.map (⟨·.raw⟩))
  let extraBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ← match ensId? with
    | some eid => pure #[← `(bracketedBinder| (_hEns : $(← mkAppTerms eid ((pIdents.push evVar).map (⟨·.raw⟩)))))] | none => pure #[]
  elabSrvCmd (← `(command|
    set_option linter.unusedVariables false in
    @[inline] def $mkEmitId $[($pIdents:ident : $pTyTerms:term)]* ($evVar:ident : $evTyTerm) $[$extraBinders:bracketedBinder]* : Qed.Server.WsEmit :=
      { topic := Qed.wsTopicKey $(Syntax.mkStrLit chStr) $paramTupleVal, payload := Qed.Proto.encode $evVar }))
  if (← hasSrvErrors) then return none
  return some {
    chIdent, chName, chStr, pIdents, pTyTerms, paramNames, paramTypeConsts, evTyTerm, reqs, ensId?, ensConst?, recPolicy, onJoin?, onSend?, onLeave?,
    sig := { name := chStr, mkEmitId, paramCount := pIdents.size, hasEnsures := ensId?.isSome } }

@[noinline]
private def elabChanClientHelpers (hdr : ParsedChanHeader) (hasJoinSnapshot hasSend : Bool)
    (joinTyTerm : Term) (spIdents : Array Ident) (spTyTerms : Array Term) : SrvElabM (String × Name) := do
  let c ← read; let (pIdents, pTyTerms) := (hdr.pIdents, hdr.pTyTerms); let chLit := Syntax.mkStrLit hdr.chStr
  let paramTupleVal ← liftMacroM <| buildTupleVal (pIdents.map (⟨·.raw⟩))
  let wireEvTerm : Term ← match hdr.ensId? with | some eid => `(Qed.Ensured $(hdr.evTyTerm) ($(← mkAppTerms eid (pIdents.map (⟨·.raw⟩))))) | none => pure hdr.evTyTerm
  let (slotId, recId, onJoinId, onMsgId, onStatusId) := (mkIdent `slot, mkIdent `rec, mkIdent `onJoin, mkIdent `onMsg, mkIdent `onStatus)
  let wsPathStr := s!"/_qed/ws/{c.srvName.toString}"
  let mkProtoCb (ty : Term) (onOk : Ident) : CommandElabM Term := mkWsDecodeCb onOk onStatusId fun bs => `(Qed.Proto.decode (α := $ty) $bs)
  let onJoinDec ← if hasJoinSnapshot then liftM (mkProtoCb joinTyTerm onJoinId) else `(fun _ => $onJoinId ())
  let onEvDec ← liftM (mkProtoCb wireEvTerm onMsgId)
  let (joinId, keyId, subId, unsubId) := (c.fnSubId hdr.chIdent "_Join", c.fnSubId hdr.chIdent "_key", c.fnSubId hdr.chIdent "_sub", c.fnSubId hdr.chIdent "_unsub")
  elabSrvCmds #[
    ← `(command| abbrev $joinId : Type := $joinTyTerm),
    ← `(command| def $keyId $[($pIdents:ident : $pTyTerms:term)]* : String := Qed.wsTopicKey $chLit $paramTupleVal),
    ← `(command| set_option linter.unusedVariables false in
        def $subId {msg : Type} ($slotId:ident : String) $[($pIdents:ident : $pTyTerms:term)]*
            ($recId:ident : Qed.Reconnect) ($onJoinId:ident : $joinTyTerm → msg) ($onMsgId:ident : $wireEvTerm → msg) ($onStatusId:ident : Qed.SocketStatus → msg) : Qed.Cmd msg :=
          Qed.Cmd.wsMuxSub $slotId $(Syntax.mkStrLit wsPathStr) $chLit (Qed.Proto.encode $paramTupleVal) $recId $onJoinDec $onEvDec $onStatusId),
    ← `(command| def $unsubId {msg : Type} ($slotId:ident : String) : Qed.Cmd msg := Qed.Cmd.wsMuxUnsub $slotId)]
  let sendHelperConst ← if hasSend then
      let sendTupleVal ← liftMacroM <| buildTupleVal (spIdents.map (⟨·.raw⟩)); let sendId := c.fnSubId hdr.chIdent "_send"
      elabSrvCmd (← `(command| def $sendId {msg : Type} ($slotId:ident : String) $[($spIdents:ident : $spTyTerms:term)]* : Qed.Cmd msg := Qed.Cmd.wsMuxSend $slotId (Qed.Proto.encode $sendTupleVal)))
      pure (c.fullSrvName ++ hdr.chName.appendAfter "_send")
    else pure .anonymous
  return (wsPathStr, sendHelperConst)

@[noinline]
private def elabServerChannelBody (hdr : ParsedChanHeader) : SrvElabM (Option (Array (TSyntax ``Lean.Parser.Term.matchAltExpr))) := do
  let c ← read; let errTyTerm ← `(Qed.Server.ApiError); let chLit := Syntax.mkStrLit hdr.chStr
  let paramTupleTy ← liftMacroM <| buildProdType hdr.pTyTerms; let pProjs ← extractTupleProjections (mkIdent `_chParams) hdr.pTyTerms.size
  let wrapEmpty (r : Term) : CommandElabM Term := `($r >>= fun _wsRes => Pure.pure (_wsRes.map fun _ => ByteArray.empty))
  let mkArm (kindStr : String) (bodyInParams : Term) : CommandElabM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
    `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkNumLit kindStr):num, $chLit => $(← mkProtoDecodeBind (mkIdent `wsParams) (mkIdent `_chParams) paramTupleTy hdr.pIdents pProjs bodyInParams))
  let runSub (suf : String) (eIds : Array Ident) (eTys eProjs : Array Term) (eReqIds : Array Ident) (eReqTys : Array Term)
      (retTy : Term) (isUnit : Bool) (rawStmts : Array Syntax) : SrvElabM (Option Term) := do
    let norm := if !blockHasAwait rawStmts && rawStmts.size == 1 && rawStmts[0]!.getKind == ``qedStmtAtomic then suiteStmts rawStmts[0]![2] else rawStmts
    let body := if isUnit then ensureUnitReturn hdr.chIdent norm else norm
    if !isUnit && !blockAlwaysReturns body then throwErrorAt hdr.chIdent s!"missing `return` on fallthrough path of `{hdr.chStr}.{suf}`"
    let subStr := s!"{hdr.chStr}_{suf}"; let hasAw := blockHasAwait body
    let baseCtx ← mkBaseLowerCtx subStr (hdr.paramNames ++ eIds.map (·.getId.toString)) hasAw true true (includeDbs := false)
    let some (r, _, _) ← elabServerHandler hasAw subStr (mkIdentFrom hdr.chIdent (hdr.chName.appendAfter s!"_{suf}"))
        (hdr.pIdents ++ eIds ++ hdr.reqs.reqHypIds ++ eReqIds) (hdr.pTyTerms ++ eTys ++ hdr.reqs.reqPropTerms ++ eReqTys)
        (pProjs ++ eProjs ++ hdr.reqs.reqHypIds.map (⟨·.raw⟩) ++ eReqIds.map (⟨·.raw⟩)) retTy errTyTerm baseCtx body none | return none
    return some r
  let (hasJoinSnapshot, joinTyTerm, joinRunTerm) ← match hdr.onJoin? with
    | some (some snapTyStx, stmts) =>
        let jt := (← liftMacroM <| lowerSrvType snapTyStx false s!"`on_join` return type of `channel {hdr.chStr}`").term
        let some r ← runSub "onJoin" #[] #[] #[] #[] #[] jt false stmts | return none
        pure (true, jt, ← `($r >>= fun _jRes => Pure.pure (_jRes.map Qed.Proto.encode)))
    | some (none, stmts) =>
        let jt ← `(Unit)
        let some r ← runSub "onJoin" #[] #[] #[] #[] #[] jt true stmts | return none
        pure (false, jt, ← liftM (wrapEmpty r))
    | none => pure (false, ← `(Unit), ← `(Pure.pure (Except.ok ByteArray.empty)))
  let joinArm ← liftM <| mkArm "1" (← liftM <| wrapReqs hdr.reqs.reqPropTerms hdr.reqs.reqHypIds hdr.reqs.reqLabels joinRunTerm)
  let mut hasSend := false; let mut spIdents : Array Ident := #[]; let mut spTyTerms : Array Term := #[]
  let mut sendParamTypeConsts : Array Name := #[]; let mut sendReqConst? : Option Name := none; let mut sendReqLabel := ""
  let mut sendArm? : Option (TSyntax ``Lean.Parser.Term.matchAltExpr) := none
  if let some (rawSParams, rawSReqs, sBody) := hdr.onSend? then
    let (spIds, spTys, spNames) ← parseSrvParams s!"`channel {hdr.chStr}`" "`on_send` parameter" rawSParams (extraShadow := hdr.paramNames)
    hasSend := true; spIdents := spIds; spTyTerms := spTys
    sendParamTypeConsts ← liftM <| elabParamTypeAbbrevs hdr.chIdent c.srvName c.fullSrvName hdr.chName "_SendParam_" spTys
    let sReqs ← elabRequiresClauses hdr.chIdent hdr.chName s!"{hdr.chStr}.on_send" "_hSReq" "_send_req"
      (hdr.paramNames ++ spNames) spNames spIds spTys rawSReqs (excludedClientVars := hdr.paramNames) (trackAuth := false)
    sendReqConst? := sReqs.clientReqConst?; sendReqLabel := sReqs.clientReqLabel
    let sendTupleTy ← liftMacroM <| buildProdType spTys; let sTupleVar := mkIdent `_chSendVal; let sProjs ← extractTupleProjections sTupleVar spTys.size
    let some sr ← runSub "onSend" spIds spTys sProjs sReqs.reqHypIds sReqs.reqPropTerms (← `(Unit)) true sBody | return none
    let sGuarded ← liftM <| wrapReqs (hdr.reqs.reqPropTerms ++ sReqs.reqPropTerms) (hdr.reqs.reqHypIds ++ sReqs.reqHypIds) (hdr.reqs.reqLabels ++ sReqs.reqLabels) (← liftM (wrapEmpty sr))
    sendArm? := some (← liftM <| mkArm "2" (← liftM <| mkProtoDecodeBind (mkIdent `wsPayload) sTupleVar sendTupleTy spIds sProjs sGuarded))
  let leaveRunTerm ← match hdr.onLeave? with
    | some stmts =>
        let some r ← runSub "onLeave" #[] #[] #[] #[] #[] (← `(Unit)) true stmts | return none
        liftM (wrapEmpty r)
    | none => `(Pure.pure (Except.ok ByteArray.empty))
  let leaveArm ← liftM <| mkArm "3" (← liftM <| wrapReqs hdr.reqs.reqPropTerms hdr.reqs.reqHypIds hdr.reqs.reqLabels leaveRunTerm)
  let (wsPathStr, sendHelperConst) ← elabChanClientHelpers hdr hasJoinSnapshot hasSend joinTyTerm spIdents spTyTerms
  if (← hasSrvErrors) then return none
  modifyEnv fun env => Qed.channelRegistry.addEntry env {
    ChannelInfo.mkDefault c.fullSrvName c.srvName.toString hdr.chName (.fullstack c.fullSrvName c.srvName.toString wsPathStr) (hdr.pIdents.map (·.getId)) hdr.paramTypeConsts hdr.recPolicy with
    hasJoinSnapshot, joinTypeConst := c.fullSrvName ++ hdr.chName.appendAfter "_Join", hasSend, sendParamCount := spIdents.size, sendParamTypeConsts,
    sendReqConst := sendReqConst?, sendReqLabel, requiresAuth := hdr.reqs.requiresAuth, clientReqConst := hdr.reqs.clientReqConst?,
    clientReqLabel := hdr.reqs.clientReqLabel, hasEnsures := hdr.ensConst?.isSome, ensPredConst := hdr.ensConst?, sendHelperConst }
  return some (#[joinArm] ++ sendArm?.toArray ++ #[leaveArm])

/-! ## Background `every` Job Elaborator -/

@[noinline]
private def elabOneServerJob (existingMethods : Array ServerMethodInfo) (seenJobs : Array String)
    (payloadTerm errTyTerm emptyCtx : Term) (callArgs : Array Term) (jc : Syntax) : SrvElabM (Option (String × Term × Option Term)) := do
  let c ← read; let jobIdent : Ident := ⟨jc.getArg 3⟩; let jobStr := jobIdent.getId.toString
  if existingMethods.any (·.name == jobStr) || seenJobs.contains jobStr then throwErrorAt jobIdent s!"duplicate job or method name `{jobStr}` in `server {c.srvName}`"
  let n := (⟨jc.getArg 1⟩ : TSyntax `num).getNat; let unitStr := (jc.getArg 2).getId.eraseMacroScopes.toString
  let unit ← match unitStr with
    | "ms" => pure DurationUnit.ms | "s" => pure DurationUnit.s | "m" => pure DurationUnit.m | "h" => pure DurationUnit.h
    | _ => throwErrorAt (jc.getArg 2) s!"unknown duration unit `{unitStr}` in `every {n}{unitStr} {jobStr}`; supported units are `ms`, `s`, `m`, `h`"
  let intervalMs := durationToMs n unit
  if intervalMs == 0 then throwErrorAt (jc.getArg 1) s!"background job `{jobStr}` interval must be positive (got `{n}{unitStr}`)"
  let bodyStmts := ensureUnitReturn jobIdent (suiteStmts (jc.getArg 5))
  let isAsyncJob := c.hasState && (blockHasAwait bodyStmts || blockHasAtomic bodyStmts)
  let some (runExpr, isRO, hasEmit) ← elabServerHandler isAsyncJob jobStr jobIdent #[] #[] #[] payloadTerm errTyTerm
      (← mkBaseLowerCtx jobStr #[] isAsyncJob true true) bodyStmts none (ctxArg? := some emptyCtx) | return none
  let proofExpr? : Option Term ← if !c.hasState then pure none else do
    let invThmId := c.fnSubId jobIdent "_inv"
    if isAsyncJob then some <$> mkAppTerms invThmId callArgs
    else
      let emitCont ← `(fun _ => Qed.Server.ProgSpec.safeIO_bind _ fun _ => Qed.Server.ProgSpec.pure_class _ trivial)
      if isRO then some <$> if hasEmit then `(Qed.Server.ProgSpec.runAtomicRead_bind_val _ $emitCont fun _ _h => _h) else `(Qed.Server.ProgSpec.runAtomicRead _ (fun _ _h => _h) fun _ _ => trivial)
      else let invApp ← mkAppTerms (← `($invThmId _s)) callArgs
           some <$> if hasEmit then `(Qed.Server.ProgSpec.runAtomic_bind_val _ $emitCont fun _s _h => $invApp _h) else `(Qed.Server.ProgSpec.runAtomic _ (fun _s _h => $invApp _h) fun _ _ => trivial)
  let (wrappedRun, wrappedPf?) ← liftM <| wrapWithEnvDecls c.envDecls runExpr proofExpr?
  let (nameLit, msLit, posPf) := (Syntax.mkStrLit jobStr, Syntax.mkNumLit (toString intervalMs), ← `(by decide))
  if c.hasState then
    let runMTerm ← `(fun {m} [Monad m] [Qed.Server.MonadServer m] [Qed.Server.MonadAtomic $(c.stateId) m] => $wrappedRun)
    let jobTerm ← `({ name := $nameLit, intervalMs := $msLit, intervalPos := $posPf, runM := $runMTerm : Qed.Server.ServerJob $(c.stateId) })
    return some (jobStr, jobTerm, ← wrappedPf?.mapM fun pf => `(Qed.Server.VerifiedJob.mk (σ := $(c.stateId)) (Inv := $(c.stateInvId)) $jobTerm $pf))
  else return some (jobStr, ← `({ name := $nameLit, intervalMs := $msLit, intervalPos := $posPf, runM := fun {m} [Monad m] [Qed.Server.MonadServer m] => $wrappedRun : Qed.Server.StatelessJob }), none)

@[noinline]
private def elabServerJobs (existingMethods : Array ServerMethodInfo) (jobClauses : Array Syntax) : SrvElabM (Option (Array String)) := do
  if jobClauses.isEmpty then return some #[]
  let c ← read; let mut jobNames : Array String := #[]; let mut runtimeJobTerms : Array Term := #[]; let mut verifiedJobTerms : Array Term := #[]
  let (payloadTerm, errTyTerm, emptyCtx) := (← `(Unit), ← `(Qed.Server.ApiError), ← `(({} : Qed.Server.RequestCtx)))
  let callArgs : Array Term := c.envIdents.map (⟨·.raw⟩) ++ #[emptyCtx]
  for jc in jobClauses do
    let some (nm, jt, vjt?) ← elabOneServerJob existingMethods jobNames payloadTerm errTyTerm emptyCtx callArgs jc | return none
    jobNames := jobNames.push nm; runtimeJobTerms := runtimeJobTerms.push jt
    if let some vjt := vjt? then verifiedJobTerms := verifiedJobTerms.push vjt
  let (jobsId, jobNamesId, verJobsId) := (c.subId `jobs, c.subId `jobNames, c.subId `verifiedJobs)
  let nameLits : Array Term := jobNames.map (Syntax.mkStrLit ·)
  elabSrvCmd (← `(command| @[noinline] def $jobNamesId : List String := [$[$nameLits:term],*]))
  if c.hasState then
    elabSrvCmd (← `(command| @[noinline] def $jobsId : Array (Qed.Server.ServerJob $(c.stateId)) := #[$[$runtimeJobTerms:term],*]))
    deferSrvCmd (← `(command| @[noinline] def $verJobsId : Array (Qed.Server.VerifiedJob $(c.stateId) $(c.stateInvId)) := #[$[$verifiedJobTerms:term],*]))
  else elabSrvCmd (← `(command| @[noinline] def $jobsId : Array Qed.Server.StatelessJob := #[$[$runtimeJobTerms:term],*]))
  return some jobNames

/-! ## `server` RPC / HTTP / Auth Hook & Command Elaborator -/

@[noinline]
private def elabFnClientStubs (fnIdent : Ident) (fnStr : String) (pIdents : Array Ident) (pTyTerms : Array Term)
    (reqTupleTy payloadTerm : Term) (innerOpt? : Option Term) (errTypeId? : Option Ident) (ensSpec? : Option FnEnsSpec)
    (reqs : LoweredRequires) : SrvElabM (Array Name) := do
  let c ← read; let pTerms : Array Term := pIdents.map (⟨·.raw⟩)
  let paramTypeConsts ← liftM <| elabParamTypeAbbrevs fnIdent c.srvName c.fullSrvName fnIdent.getId "_Param_" pTyTerms
  let ensPayloadTerm : Term ← match ensSpec? with
    | some (ensId, _, _) => let a ← mkAppTerms ensId pTerms; match innerOpt? with | some it => `(Option (Qed.Ensured $it ($a))) | none => `(Qed.Ensured $payloadTerm ($a))
    | none => pure payloadTerm
  let wireRespT : Term ← match errTypeId? with | some e => `(Except (Qed.RpcDomainError $e) $ensPayloadTerm) | none => pure ensPayloadTerm
  let outcomeT : Term ← match errTypeId? with | some e => `(Qed.RpcOutcome $e $ensPayloadTerm) | none => `(Qed.RpcSimpleOutcome $ensPayloadTerm)
  let outBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ← if ensSpec?.isSome then (pIdents.zip pTyTerms).mapM fun (p, t) => `(bracketedBinder| ($p:ident : $t:term)) else pure #[]
  let (rawRpcId, outcomeId, pubFnId) := (c.subId (Name.mkSimple s!"_rpc_{fnStr}") fnIdent, c.fnSubId fnIdent "_Outcome", c.subId fnIdent.getId fnIdent)
  let reqBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ← match reqs.clientReqId? with
    | some reqId => pure #[← `(bracketedBinder| (_hReq : $(← mkAppTerms reqId pTerms) := by qedProveRpcReq))] | none => pure #[]
  let pTupleVal ← liftMacroM <| buildTupleVal pTerms; let rawCall ← mkAppTerms rawRpcId pTerms
  elabSrvCmds #[
    ← `(command| set_option linter.unusedVariables false in abbrev $outcomeId $[$outBinders:bracketedBinder]* : Type := $outcomeT),
    ← `(command| def $rawRpcId {msg cb : Type} $[($pIdents:ident : $pTyTerms:term)]* (onDone : cb) [Qed.RpcCallback $wireRespT msg cb] : Qed.Cmd msg :=
        Qed.Cmd.rpc (req := $reqTupleTy) (resp := $wireRespT) $(Syntax.mkStrLit s!"/_qed/rpc/{c.srvName.toString}/{fnStr}") $pTupleVal (Qed.RpcCallback.adapt (α := $wireRespT) onDone)),
    ← `(command| set_option linter.unusedVariables false in def $pubFnId {msg cb : Type} $[($pIdents:ident : $pTyTerms:term)]* (onDone : cb) [Qed.RpcCallback $wireRespT msg cb] $[$reqBinders]* : Qed.Cmd msg :=
        $rawCall onDone)]
  return paramTypeConsts

@[noinline]
private def elabServerFnClause (existingMethods : Array ServerMethodInfo) (fc : Syntax) :
    SrvElabM (Option (ServerMethodInfo × TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let c ← read; let fnIdent : Ident := ⟨fc.getArg 1⟩; let fnStr := fnIdent.getId.toString
  if existingMethods.any (·.name == fnStr) then throwErrorAt fnIdent s!"duplicate function `{fnStr}` in `server {c.srvName}`"
  let mut reqExprs : Array Syntax := #[]; let mut ensExprs : Array Syntax := #[]
  for cl in (fc.getArg 8).getArgs do
    if cl.getKind == ``srvRequiresLine then reqExprs := reqExprs ++ (cl.getArg 1).getSepArgs
    else if cl.getKind == ``srvEnsuresLine then ensExprs := ensExprs ++ (cl.getArg 1).getSepArgs
    else throwErrorAt cl "unexpected contract clause in `def`"
  let (pIdents, pTyTerms, paramNames) ← parseSrvParams s!"server function `{fnStr}`" "parameter" (fc.getArg 3).getSepArgs (reserved := if ensExprs.isEmpty then #[] else #["result"])
  let retTy ← liftMacroM <| lowerSrvType (fc.getArg 6) true s!"return type of `{fnStr}`"
  let (payloadTerm, innerOpt?) := (retTy.term, retTy.innerOpt?)
  let isUnitPayload := (retTy.mods.filter (· != .fallible)).isEmpty && retTy.baseName == `Unit
  let bodyStmts := if isUnitPayload then ensureUnitReturn fnIdent (fc.getArg 9).getArgs else (fc.getArg 9).getArgs
  if !isUnitPayload && !blockAlwaysReturns bodyStmts then throwErrorAt fnIdent s!"missing `return` on fallthrough path of `{fnStr}`"
  let (domainTagIdents, hasPlainFail) ← liftM <| scanBodyFailTags bodyStmts
  if !domainTagIdents.isEmpty && hasPlainFail then throwErrorAt fnIdent s!"cannot mix typed `fail(.tag)` and untyped `fail(\"...\")` inside `{fnStr}`; use `fail(.tag, msg)` for all domain failures"
  if !domainTagIdents.isEmpty && !retTy.isFallible then throwErrorAt fnIdent s!"`fail(.tag)` can only be returned from a fallible `T!` function (`{fnStr}` is not declared `-> ...!`)"
  let errTypeId? ← if domainTagIdents.isEmpty then pure none else some <$> elabDomainErrorType fnIdent domainTagIdents
  if (← hasSrvErrors) then return none
  let domainErrTyTerm? : Option Term := errTypeId?.map (⟨·.raw⟩)
  let errTyTerm : Term ← match domainErrTyTerm? with | some et => `(Qed.Server.SrvFailure $et) | none => `(Qed.Server.ApiError)
  let reqs ← elabRequiresClauses fnIdent fnIdent.getId fnStr "_hReq" "_req" paramNames paramNames pIdents pTyTerms reqExprs
  let some ensRes? ← elabEnsuresAbbrev fnIdent fnStr `result paramNames pIdents pTyTerms (innerOpt?.getD payloadTerm) ensExprs | return none
  let pTerms : Array Term := pIdents.map (⟨·.raw⟩)
  let ensSpec? : Option FnEnsSpec := ensRes?.map fun (ensId, _, labelStr) => (ensId, fun outT => do
    let ensApp ← mkAppTerms ensId pTerms; if innerOpt?.isSome then `(Qed.Server.srvEnsPostOpt ($ensApp) $outT) else `(Qed.Server.srvEnsPost ($ensApp) $outT), labelStr)
  let hasAwait := blockHasAwait bodyStmts; let reqTupleTy ← liftMacroM <| buildProdType pTyTerms; let reqVar := mkIdent `_reqVal
  let projs ← extractTupleProjections reqVar pTyTerms.size
  let some (runExpr, isReadOnly, _) ← elabServerHandler hasAwait fnStr fnIdent (pIdents ++ reqs.reqHypIds) (pTyTerms ++ reqs.reqPropTerms)
      (projs ++ reqs.reqHypIds.map (⟨·.raw⟩)) payloadTerm errTyTerm
      (← mkBaseLowerCtx fnStr paramNames hasAwait (retTy.isFallible || innerOpt?.isSome) retTy.isFallible innerOpt? domainErrTyTerm?) bodyStmts ensSpec? | return none
  let resExpr ← if domainErrTyTerm?.isSome then `(Qed.Server.SrvFailure.toWire _fnRes) else `(_fnRes)
  let arm : TSyntax ``Lean.Parser.Term.matchAltExpr ← liftM <| do
    let dec ← mkProtoDecodeBind (mkIdent `reqBytes) reqVar reqTupleTy pIdents projs (← wrapReqs reqs.reqPropTerms reqs.reqHypIds reqs.reqLabels (← `($runExpr >>= fun _fnRes => Pure.pure (($resExpr).map Qed.Proto.encode))))
    `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkStrLit fnStr) => $dec)
  let paramTypeConsts ← elabFnClientStubs fnIdent fnStr pIdents pTyTerms reqTupleTy payloadTerm innerOpt? errTypeId? ensSpec? reqs
  return some ({
    name := fnStr, paramNames := pIdents.map (·.getId), paramCount := pIdents.size, isReadOnly, isAsync := hasAwait,
    isFallible := retTy.isFallible, isOption := innerOpt?.isSome, hasClientReq := reqs.clientReqId?.isSome, requiresAuth := reqs.requiresAuth,
    clientReqConst := reqs.clientReqConst?, clientReqLabel := reqs.clientReqLabel, hasEnsures := ensSpec?.isSome, ensPredConst := ensRes?.map (·.2.1),
    domainErrTags := domainTagIdents.map (·.getId.toString), rawRpcConst := c.fullSrvName ++ Name.mkSimple s!"_rpc_{fnStr}",
    outcomeConst := c.fullSrvName ++ fnIdent.getId.appendAfter "_Outcome", paramTypeConsts }, arm)

@[noinline]
private def elabServerHttpRouteClause (routeIdx : Nat) (existingRoutes : Array (String × String)) (hc : Syntax) :
    SrvElabM (Option ((String × String) × TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let c ← read; let isStream := hc.getKind == ``srvStreamClause
  let methodStr := if isStream then "GET" else (hc.getArg 0).getId.toString.toUpper
  let pathStx := hc.getArg 1; let pathStr := (⟨pathStx⟩ : TSyntax `str).getString
  if !pathStr.startsWith "/" then throwErrorAt pathStx s!"custom HTTP route path `{pathStr}` must start with `/`"
  if pathStr.startsWith "/_qed/" then throwErrorAt pathStx s!"custom HTTP route path `{pathStr}` cannot use reserved `/_qed/` prefix"
  if existingRoutes.any fun (m, p) => m == methodStr && p == pathStr then throwErrorAt pathStx s!"duplicate custom HTTP route `{methodStr} {pathStr}` in `server {c.srvName}`"
  let mut reqExprs : Array Syntax := #[]
  for cl in (hc.getArg 3).getArgs do
    if cl.getKind == ``srvRequiresLine then reqExprs := reqExprs ++ (cl.getArg 1).getSepArgs
    else throwErrorAt cl "only `requires` contracts are supported on HTTP / `stream` routes"
  let routeLeaf := Name.mkSimple s!"_http_{routeIdx}"; let routeIdent := mkIdentFrom pathStx routeLeaf
  let routeLabel := if isStream then s!"stream {pathStr}" else s!"{methodStr} {pathStr}"
  let bodyStmts := if isStream then ensureUnitReturn routeIdent (hc.getArg 4).getArgs else (hc.getArg 4).getArgs
  if !isStream && !blockAlwaysReturns bodyStmts then throwErrorAt pathStx s!"missing `return` on fallthrough path of `{routeLabel}`"
  let reqs ← elabRequiresClauses routeIdent routeLeaf routeLabel "_hHttpReq" "_req" #[] #[] #[] #[] reqExprs (trackAuth := true)
  let hasAwait := blockHasAwait bodyStmts
  let some (runExpr, _, _) ← elabServerHandler hasAwait routeLabel routeIdent reqs.reqHypIds reqs.reqPropTerms (reqs.reqHypIds.map (⟨·.raw⟩))
      (← if isStream then `(Unit) else `(Qed.Server.HttpResponse)) (← `(Qed.Server.ApiError))
      (← mkBaseLowerCtx routeLabel #[] hasAwait true true (isHttpRoute := !isStream) (isStreamRoute := isStream)) bodyStmts none | return none
  let mapFn ← if isStream then `(fun _ => Option.some (Qed.Server.HttpResponse.sse [])) else `(Option.some)
  let guardedRun ← liftM <| wrapReqs reqs.reqPropTerms reqs.reqHypIds reqs.reqLabels (← `($runExpr >>= fun _httpRes => Pure.pure (_httpRes.map $mapFn)))
  return some ((methodStr, pathStr), ← `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkStrLit methodStr), $(Syntax.mkStrLit pathStr) => $guardedRun))

@[noinline]
private def elabServerAuthHook (hookLabel : String) (hookLeaf : Name) (authInfo : AuthInfo) (hc : Syntax) : SrvElabM (Option Term) := do
  let c ← read; let paramIdent : Ident := ⟨hc.getArg 2⟩; let paramStr ← checkSrvParamName s!"`{hookLabel}`" paramIdent
  let hookIdent := mkIdentFrom hc hookLeaf; let bodyStmts := ensureUnitReturn hookIdent (suiteStmts (hc.getArg 5))
  let hasAwait := blockHasAwait bodyStmts; let isAsync := c.hasState && (hasAwait || blockHasAtomic bodyStmts)
  let (authUserVar, hAuthId, hAuthEqId) := (mkIdent `_authUser, mkIdent `_hAuth, mkIdent `_hAuthEq)
  let extraTys : Array Term := #[← `($(mkIdentFrom paramIdent (authInfo.authName ++ `User))), ← `(($(c.ctxId)).userId ≠ Option.none), ← `(Option.some (($paramIdent).id) = ($(c.ctxId)).userId)]
  let some (re, _, _) ← elabServerHandler isAsync hookLabel hookIdent #[paramIdent, hAuthId, hAuthEqId] extraTys
      #[⟨authUserVar.raw⟩, ⟨hAuthId.raw⟩, ⟨hAuthEqId.raw⟩] (← `(Unit)) (← `(Qed.Server.ApiError))
      (← mkBaseLowerCtx hookLabel #[paramStr] (if c.hasState then isAsync else hasAwait) true true) bodyStmts none | return none
  return some re

@[noinline]
private def elabServerCmdCore (priorRep priorUnrep : Nat) : CommandElab := fun stx => do
  let srvIdent : Ident := ⟨stx.getArg 1⟩; let srvName := srvIdent.getId
  let parsed ← parseServerClauses srvIdent srvName (stx.getArg 3).getArgs
  let initCtx : SrvElabCtx := {
    priorRep, priorUnrep, srvIdent, srvName, fullSrvName := (← getCurrNamespace) ++ srvName, hasState := !parsed.stateDecls.isEmpty,
    dbDecls := parsed.dbDecls, authDecl? := parsed.authDecl?, envDecls := parsed.envDecls,
    stateFieldNames := parsed.stateDecls.map (·.1.getId.toString), envVarNames := parsed.envDecls.map (·.1.getId.toString),
    invs := parsed.invs, mutInvs := parsed.mutInvs, deferredProofs := ← IO.mkRef #[], extRootsRef := ← IO.mkRef #[] }
  (do
    if initCtx.hasState then unless (← elabServerStateCmds parsed.stateDecls) do return
    let mut chanHeaders : Array ParsedChanHeader := #[]
    for cc in parsed.chanClauses do
      let some hdr ← elabServerChannelHeader (chanHeaders.map ParsedChanHeader.chStr) cc | return
      chanHeaders := chanHeaders.push hdr
    withReader (fun (c : SrvElabCtx) => { c with chanSigs := chanHeaders.map ParsedChanHeader.sig }) do
      let mut methodInfos : Array ServerMethodInfo := #[]; let mut dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
      for fc in parsed.fnClauses do
        let some (info, arm) ← elabServerFnClause methodInfos fc | return
        methodInfos := methodInfos.push info; dispatchArms := dispatchArms.push arm
      let mut wsDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
      for hdr in chanHeaders do
        let some chArms ← elabServerChannelBody hdr | return
        wsDispatchArms := wsDispatchArms ++ chArms
      let mut httpRoutes : Array (String × String) := #[]; let mut httpDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
      for (hc, idx) in parsed.httpClauses.zipIdx do
        let some (rt, arm) ← elabServerHttpRouteClause idx httpRoutes hc | return
        httpRoutes := httpRoutes.push rt; httpDispatchArms := httpDispatchArms.push arm
      let some jobNames ← elabServerJobs methodInfos parsed.jobClauses | return
      let elabHook? (lbl : String) (leaf : Name) (cl? : Option Syntax) : SrvElabM (Option (Option Term)) :=
        match parsed.authDecl?, cl? with | some (_, ai), some hc => Option.map some <$> elabServerAuthHook lbl leaf ai hc | _, _ => pure (some none)
      let some onCreateRun? ← elabHook? "onCreateAccount" `_onCreateAccount parsed.onCreateAccountClause? | return
      let some onSignInRun? ← elabHook? "onSignIn" `_onSignIn parsed.onSignInClause? | return
      elabServerDispatchCmds methodInfos dispatchArms (chanHeaders.map ParsedChanHeader.chStr) wsDispatchArms httpDispatchArms jobNames onCreateRun? onSignInRun?
  ).run initCtx
  for runProof in ← initCtx.deferredProofs.get do unless (← runProof) do return

@[command_elab serverCmd]
def elabServerCmd : CommandElab := fun stx => do
  let savedEnv ← getEnv; let priorLog := (← get).messages
  let (priorRep, priorUnrep, priorKinds, priorTasks) := (priorLog.reported.size, priorLog.unreported.size, priorLog.loggedKinds, (← get).snapshotTasks.size)
  let rollback : CommandElabM Unit := do
    setEnv savedEnv
    modify fun s => let m := s.messages; { s with messages := { reported := filterNewWarnings m.reported priorRep, unreported := filterNewWarnings m.unreported priorUnrep, loggedKinds := priorKinds } }
  try elabServerCmdCore priorRep priorUnrep stx catch ex => rollback; throw ex
  let asyncErr := ((← get).snapshotTasks.extract priorTasks (← get).snapshotTasks.size).any fun t => Qed.Diag.snapshotTreeHasErrors 64 t.get
  if hasNewErrors (← get).messages priorRep priorUnrep || asyncErr then rollback

/-! ## `fullstack` Command Elaborator & `qedServerMain` -/

private def collectReachableDefns (env : Environment) : Nat → List Name → Std.HashSet Name → Except Name (Std.HashSet Name)
  | _, [], seen => .ok seen | 0, n :: _, _ => .error n
  | fuel + 1, n :: rest, seen =>
      if seen.contains n then collectReachableDefns env fuel rest seen
      else let seen' := seen.insert n
           if Qed.Diag.isToolchainRoot (Qed.Diag.modRootOf env n) then collectReachableDefns env fuel rest seen'
           else match env.find? n with
             | some (.defnInfo d) => collectReachableDefns env fuel (d.value.getUsedConstants.toList ++ rest) seen'
             | _ => collectReachableDefns env fuel rest seen'

@[noinline]
private def verifyFullstackRpcClosure (env : Environment) (fsName : Name) (srvInfo : ServerInfo) (cliIdent : Ident) (resolvedCli : Name) : CommandElabM Unit := do
  let mut rpcMap : NameMap (ServerInfo × ServerMethodInfo) := {}
  for (_, s) in serverRegistry.getState env do for m in s.methods do
    if m.rawRpcConst != .anonymous then rpcMap := rpcMap.insert m.rawRpcConst (s, m)
    rpcMap := rpcMap.insert (s.serverName ++ Name.mkSimple m.name) (s, m)
  let visited ← match collectReachableDefns env 300000 [resolvedCli] {} with
    | .ok s => pure s | .error p => throwErrorAt cliIdent s!"`fullstack {fsName}`: RPC endpoint closure analysis exceeded fuel limit while inspecting `{p}`"
  let mut fsChanMap : NameMap Qed.ChannelInfo := {}
  for (_, ch) in Qed.channelRegistry.getState env do
    if let .fullstack _ _ _ := ch.kind then
      if ch.subHelperConst != .anonymous then fsChanMap := fsChanMap.insert ch.subHelperConst ch
      if ch.sendHelperConst != .anonymous then fsChanMap := fsChanMap.insert ch.sendHelperConst ch
  for n in visited do
    if let some ch := fsChanMap.find? n then
      if ch.ownerName != srvInfo.serverName then throwErrorAt cliIdent s!"`fullstack {fsName}` mounts `server {srvInfo.shortName}`, but client `{cliIdent.getId}` subscribes to WebSocket channel `{ch.ownerShort}.{ch.channelName}` on unmounted server `{ch.ownerShort}`"
    if let some (otherSrv, mInfo) := rpcMap.find? n then
      if otherSrv.serverName != srvInfo.serverName then throwErrorAt cliIdent s!"`fullstack {fsName}` mounts `server {srvInfo.shortName}`, but client `{cliIdent.getId}` calls RPC `{otherSrv.shortName}.{mInfo.name}` on unmounted server `{otherSrv.shortName}`"
    let root := Qed.Diag.modRootOf env n
    if root != `Qed && root != `Js && root != `Cli then
      if let some (.defnInfo d) := env.find? n then
        let badRef ← IO.mkRef (none : Option String)
        d.value.forEach fun sub => do
          if (← badRef.get).isNone then
            if let .lit (.strVal s) := sub then
              if s.startsWith "/_qed/rpc/" then
                match (s.drop 10).toString.splitOn "/" with
                | [sp, mp] => if sp != srvInfo.shortName || !(srvInfo.methods.any (·.name == mp)) then badRef.set (some s)
                | _ => badRef.set (some s)
        if let some url ← badRef.get then
          throwErrorAt cliIdent s!"`fullstack {fsName}` mounts `server {srvInfo.shortName}` (methods: [{String.intercalate ", " (srvInfo.methods.toList.map (·.name))}]), but client `{cliIdent.getId}` targets invalid RPC endpoint `{url}`"

@[noinline, command_elab fullstackCmd]
def elabFullstackCmd : CommandElab := fun stx => do
  let fsIdent : Ident := ⟨stx.getArg 1⟩; let fsName := fsIdent.getId; let currNs ← getCurrNamespace
  let mut srvIdent? : Option Ident := none; let mut cliIdent? : Option Ident := none; let mut title? : Option String := none
  for c in (stx.getArg 3).getArgs do
    let k := c.getKind
    if k == ``fsServerClause then
      if srvIdent?.isSome then throwErrorAt c "duplicate `server` clause in `fullstack`"
      srvIdent? := some ⟨c.getArg 1⟩
    else if k == ``fsClientClause then
      if cliIdent?.isSome then throwErrorAt c "duplicate `client` clause in `fullstack`"
      cliIdent? := some ⟨c.getArg 1⟩
    else if k == ``fsTitleClause then
      if title?.isSome then throwErrorAt c "duplicate `title` clause in `fullstack`"
      title? := some (⟨c.getArg 1⟩ : TSyntax `str).getString
    else throwErrorAt c "unexpected clause in `fullstack` block"
  let some srvIdent := srvIdent? | throwErrorAt fsIdent s!"`fullstack {fsName}` must specify `server <ServerName>`"
  let some cliIdent := cliIdent? | throwErrorAt fsIdent s!"`fullstack {fsName}` must specify `client <AppName>`"
  let env ← getEnv
  let some srvInfo := Qed.Diag.lookupNameMapExt? serverRegistry env currNs (← getOpenDecls) srvIdent.getId
    | throwErrorAt srvIdent s!"unknown `server` `{srvIdent.getId}` in `fullstack {fsName}`"
  let cliTarget := resolveAppTargetIdent env currNs cliIdent
  let resolvedCli ← try liftCoreM <| realizeGlobalConstNoOverloadWithInfo cliTarget catch _ =>
    if (← liftCoreM (Qed.lookupComponent? cliIdent.getId)).isSome then
      throwErrorAt cliIdent s!"component `{cliIdent.getId}` in `fullstack {fsName}` is not a top-level mountable app (remove `prop`, `bind`, `children`, `event`, and uninitialized `state` fields)"
    else throwErrorAt cliIdent s!"unknown `client` `{cliIdent.getId}` in `fullstack {fsName}`; specify a top-level `component` or `Qed.App` value"
  let cliAppId := mkIdentFrom fsIdent (fsName ++ `clientApp)
  elabCommand (← `(command| abbrev $cliAppId := $cliTarget))
  let cliCompName := if resolvedCli.getString! == "app" then resolvedCli.getPrefix else resolvedCli
  verifyFullstackRpcClosure env fsName srvInfo cliIdent resolvedCli
  let srvShortLit := Syntax.mkStrLit srvInfo.shortName
  if env.contains (cliCompName ++ `usedRpcs) then
    let (usedRpcsId, srvMethodsId, epThmId, ssrThmId) := (mkIdentFrom cliIdent (cliCompName ++ `usedRpcs), mkIdentFrom srvIdent (srvInfo.serverName ++ `methods), mkIdentFrom fsIdent (fsName ++ `rpc_endpoints_valid), mkIdentFrom fsIdent (fsName ++ `ssr_rpc_closure_complete))
    elabCommand (← `(command| theorem $epThmId : ∀ ep ∈ $usedRpcsId, ep.1 = $srvShortLit ∧ ep.2 ∈ $srvMethodsId := by decide))
    elabCommand (← `(command|
      theorem $ssrThmId (dispatchMethod : String → ByteArray → Except String ByteArray) (ep : String × String) (hep : ep ∈ $usedRpcsId) (reqBody : ByteArray) :
          Qed.ssrDispatchRpc $srvShortLit $srvMethodsId dispatchMethod "POST" ("/_qed/rpc/" ++ ep.1 ++ "/" ++ ep.2) reqBody = dispatchMethod ep.2 reqBody :=
        Qed.ssr_rpc_closure_complete $srvShortLit $srvMethodsId $usedRpcsId $epThmId dispatchMethod (by decide) (by decide) ep hep reqBody))
  if env.contains (cliCompName ++ `usedChannels) then
    let (wsThmId, usedChsId, srvChsId) := (mkIdentFrom fsIdent (fsName ++ `ws_endpoints_valid), mkIdentFrom cliIdent (cliCompName ++ `usedChannels), mkIdentFrom srvIdent (srvInfo.serverName ++ `channels))
    elabCommand (← `(command| theorem $wsThmId : ∀ ch ∈ $usedChsId, ch.1 = $srvShortLit ∧ ch.2 ∈ $srvChsId := by decide))
  let pageTitle := title?.getD fsName.toString; let titleId := mkIdentFrom fsIdent (fsName ++ `title)
  elabCommand (← `(command| def $titleId : String := $(Syntax.mkStrLit pageTitle)))
  modifyEnv fun e => fullstackRegistry.addEntry e { fullstackName := currNs ++ fsName, serverName := srvInfo.serverName, title := pageTitle }

syntax (name := qedServerMainCmd) "qedServerMain " ident : command

@[noinline, command_elab qedServerMainCmd]
def elabQedServerMain : CommandElab := fun stx => do
  let fsIdent : Ident := ⟨stx[1]⟩; let env ← getEnv; let currNs ← getCurrNamespace
  let some fsInfo := (Qed.Diag.lookupNameMapExt? fullstackRegistry env currNs (← getOpenDecls) fsIdent.getId).orElse (fun _ =>
      (fullstackRegistry.getState env).toList.findSome? fun (k, v) => if k.getString! == fsIdent.getId.toString then some v else none)
    | throwErrorAt fsIdent s!"unknown `fullstack` declaration `{fsIdent.getId}`"
  let some srvInfo := (serverRegistry.getState env).find? fsInfo.serverName
    | throwErrorAt fsIdent s!"internal error: `server` `{fsInfo.serverName}` not found in registry"
  let srvId (leaf : Name) := mkIdentFrom fsIdent (srvInfo.serverName ++ leaf)
  let dbCfgIds := srvInfo.databases.map (mkIdentFrom fsIdent ·)
  let optId (id? : Option Ident) : CommandElabM Term := match id? with | some id => `(Option.some $id:ident) | none => `(Option.none)
  let wrapHandler (id : Ident) : CommandElabM Term := `(fun {m} [Monad m] [Qed.Server.MonadServer m] [Qed.Server.MonadAtomic _ m] => $id)
  let optHandler (on : Bool) (id : Ident) : CommandElabM Term := if on then do `(some $(← wrapHandler id)) else `(none)
  let asyncNames : Array Term := srvInfo.methods.filterMap fun m => if m.isAsync then some (Syntax.mkStrLit m.name) else none
  let initStateArg : Term ← if srvInfo.hasState then pure (srvId `initState : Term) else `((() : Unit))
  let jobsArg : Term ← if srvInfo.jobs.isEmpty then `(#[]) else if srvInfo.hasState then pure (srvId `jobs : Term) else `(($(srvId `jobs)).map Qed.Server.StatelessJob.toUnitJob)
  let runnerCall ← `($(mkIdent `Qed.Server.Native.runStatefulFullstack) $(mkIdentFrom fsIdent (fsInfo.fullstackName ++ `clientApp))
      $(quote fsInfo.title) $(quote srvInfo.shortName) $initStateArg $(srvId `secrets) $(← wrapHandler (srvId `dispatchM))
      port staticDir devMode numWorkers $(← optHandler (!srvInfo.channels.isEmpty) (srvId `wsDispatchM)) (some #[$asyncNames,*])
      $(← optHandler srvInfo.hasHttpRoutes (srvId `httpDispatchM)) $jobsArg $(← optId (srvInfo.authConfig?.map (mkIdentFrom fsIdent ·)))
      $(← optHandler (srvInfo.hasOnCreateAccount || srvInfo.hasOnSignIn) (srvId `authHookM))
      ($(quote srvInfo.hasOnCreateAccount), $(quote srvInfo.hasOnSignIn)) $(← optId dbCfgIds[0]?))
  let initDbCheck ← if dbCfgIds.isEmpty then `(pure true) else `($(mkIdent `Qed.Server.Native.initDatabases) #[$[$dbCfgIds:ident],*])
  let parseCliCall ← `($(mkIdent `Qed.Server.Native.parseServerCliArgs) args)
  elabCommand (← `(command|
    def $(mkIdent `main):ident (args : List String) : IO UInt32 := do
      let (staticDir, port, devMode, numWorkers) ← $parseCliCall:term
      if !(← $initDbCheck:term) then return 1
      $runnerCall:term))

end ServerFullElab
end Qed.Server
