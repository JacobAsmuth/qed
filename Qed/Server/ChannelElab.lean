import Qed.Server.FnElab
import Qed.Runtime.Cmd

namespace Qed.Server
open Qed.Lang

structure ParsedChanHeader where
  chIdent        : Lean.Ident
  chName         : Lean.Name
  chStr          : String
  pIdents        : Array Lean.Ident
  pTyTerms       : Array Lean.Term
  paramNames     : Array String
  paramTypeConsts: Array Lean.Name
  evTyTerm       : Lean.Term
  reqs           : LoweredRequires
  ensId?         : Option Lean.Ident
  ensConst?      : Option Lean.Name
  recPolicy      : Qed.Reconnect
  onJoin?        : Option (Option Lean.Syntax × Array Lean.Syntax)
  onSend?        : Option (Array Lean.Syntax × Array Lean.Syntax × Array Lean.Syntax)
  onLeave?       : Option (Array Lean.Syntax)
  sig            : SrvChanSig

section ChannelElab
open Lean Elab Command

def elabServerChannelHeader (existingChanNames : Array String) (chStx : Syntax) :
    SrvElabM (Option ParsedChanHeader) := do
  let c ← read
  let chIdent : Ident := ⟨(chStx.getArg 1)⟩
  let chName := chIdent.getId
  let chStr := chName.toString
  if existingChanNames.contains chStr then
    throwErrorAt chIdent s!"duplicate `channel {chStr}` in `server {c.srvName}`"

  let (pIdents, pTyTerms, paramNames) ←
    parseSrvParams s!"`channel {chStr}`" "channel parameter" (chStx.getArg 3).getSepArgs (reserved := #["event"])

  let evTy ← liftMacroM <| lowerSrvType (chStx.getArg 6) (allowFallible := false) s!"event type of `channel {chStr}`"
  let evTyTerm := evTy.term

  let mut reqExprs : Array Syntax := #[]
  let mut ensExprs : Array Syntax := #[]
  let mut recPolicy : Qed.Reconnect := .defaultPolicy
  let mut hasRec := false
  let mut onJoin? : Option (Option Syntax × Array Syntax) := none
  let mut onSend? : Option (Array Syntax × Array Syntax × Array Syntax) := none
  let mut onLeave? : Option (Array Syntax) := none

  if (chStx.getArg 7).getNumArgs == 2 then
    for sub in ((chStx.getArg 7).getArg 1).getArgs do
      let sk := sub.getKind
      if sk == ``srvChanReqClause then reqExprs := reqExprs ++ ((sub.getArg 0).getArg 1).getSepArgs
      else if sk == ``srvChanEnsClause then ensExprs := ensExprs ++ ((sub.getArg 0).getArg 1).getSepArgs
      else if sk == ``srvChanReconnectClause then
        if hasRec then throwErrorAt sub s!"duplicate `reconnect` clause in `channel {chStr}`"
        hasRec := true
        recPolicy ← liftMacroM <| Qed.parseReconnectExpr (sub.getArg 1)
      else if sk == ``srvChanOnJoinClause then
        if onJoin?.isSome then throwErrorAt sub s!"duplicate `on_join` in `channel {chStr}`"
        let snapTy? := if (sub.getArg 1).getNumArgs == 2 then some ((sub.getArg 1).getArg 1) else none
        onJoin? := some (snapTy?, suiteStmts (sub.getArg 3))
      else if sk == ``srvChanOnSendClause then
        if onSend?.isSome then throwErrorAt sub s!"duplicate `on_send` in `channel {chStr}`"
        let sReqs := (sub.getArg 5).getArgs.flatMap fun rl => (rl.getArg 1).getSepArgs
        onSend? := some ((sub.getArg 2).getSepArgs, sReqs, (sub.getArg 6).getArgs)
      else if sk == ``srvChanOnLeaveClause then
        if onLeave?.isSome then throwErrorAt sub s!"duplicate `on_leave` in `channel {chStr}`"
        onLeave? := some (suiteStmts (sub.getArg 2))
      else
        throwErrorAt sub s!"unexpected clause in `channel {chStr}`"

  let evAbbrevId := mkIdentFrom chIdent (c.srvName ++ chName.appendAfter "_Event")
  liftM <| elabCommand (← `(command| abbrev $evAbbrevId : Type := $evTyTerm))
  let paramTypeConsts ← liftM <| elabParamTypeAbbrevs chIdent c.srvName c.fullSrvName chName "_Param_" pTyTerms

  let reqs ← elabRequiresClauses chIdent chName chStr "_hChReq" "_req"
    paramNames paramNames pIdents pTyTerms reqExprs

  let some ensRes? ← elabEnsuresAbbrev chIdent chStr `event paramNames pIdents pTyTerms evTyTerm ensExprs
    | return none
  let (ensId?, ensConst?) := match ensRes? with
    | some (eid, econst, _) => (some eid, some econst)
    | none                  => (none, none)

  -- Emit `<S>.<ch>_mkEmit` (checked at every `emit <ch>(...)` site!)
  let mkEmitId := mkIdentFrom chIdent (c.srvName ++ chName.appendAfter "_mkEmit")
  let evVar := mkIdent `_ev
  let chLit := Syntax.mkStrLit chStr
  let paramTupleVal ← liftMacroM <| buildTupleVal (pIdents.map (⟨·.raw⟩))
  let extraBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ← match ensId? with
    | some eid =>
        let ensApp ← mkAppTerms eid ((pIdents.push evVar).map (⟨·.raw⟩))
        pure #[← `(bracketedBinder| (_hEns : $ensApp))]
    | none => pure #[]
  liftM <| elabCommand (← `(command|
    set_option linter.unusedVariables false in
    @[inline] def $mkEmitId $[($pIdents:ident : $pTyTerms:term)]* ($evVar:ident : $evTyTerm)
        $[$extraBinders:bracketedBinder]* : Qed.Server.WsEmit :=
      { topic := Qed.wsTopicKey $chLit $paramTupleVal, payload := Qed.Proto.encode $evVar }))
  if (← hasSrvErrors) then return none

  let sig : SrvChanSig := { name := chStr, mkEmitId, paramCount := pIdents.size, hasEnsures := ensId?.isSome }
  return some {
    chIdent, chName, chStr, pIdents, pTyTerms, paramNames, paramTypeConsts, evTyTerm,
    reqs, ensId?, ensConst?, recPolicy, onJoin?, onSend?, onLeave?, sig
  }

private def unwrapOptionalOuterAtomic (stmts : Array Syntax) : Array Syntax :=
  if !blockHasAwait stmts && stmts.size == 1 && stmts[0]!.getKind == ``qedStmtAtomic then
    suiteStmts stmts[0]![2]
  else stmts

private def wrapEmptyWs (r : Term) : CommandElabM Term :=
  `($r >>= fun _wsRes => Pure.pure (_wsRes.map fun _ => ByteArray.empty))

private structure ChanBodyCtx where
  hdr          : ParsedChanHeader
  errTyTerm    : Term
  paramTupleTy : Term
  pProjs       : Array Term

private def runChanSubHandler (cb : ChanBodyCtx) (subSuffix : String)
    (extraIds : Array Ident) (extraTys : Array Term) (extraProjs : Array Term)
    (extraReqIds : Array Ident) (extraReqTys : Array Term)
    (retTyTerm : Term) (isUnitRet : Bool) (rawStmts : Array Syntax) :
    SrvElabM (Option Term) := do
  let hdr := cb.hdr
  let normStmts := unwrapOptionalOuterAtomic rawStmts
  let bodyStmts := if isUnitRet then ensureUnitReturn hdr.chIdent normStmts else normStmts
  if !isUnitRet && !blockAlwaysReturns bodyStmts then
    throwErrorAt hdr.chIdent s!"missing `return` on fallthrough path of `{hdr.chStr}.{subSuffix}`"
  let subFnStr := s!"{hdr.chStr}_{subSuffix}"
  let subFnIdent := mkIdentFrom hdr.chIdent (hdr.chName.appendAfter s!"_{subSuffix}")
  let hasAwait := blockHasAwait bodyStmts
  let extraBinderIds := hdr.pIdents ++ extraIds ++ hdr.reqs.reqHypIds ++ extraReqIds
  let extraBinderTys := hdr.pTyTerms ++ extraTys ++ hdr.reqs.reqHypTys ++ extraReqTys
  let extraCallArgs : Array Term :=
    cb.pProjs ++ extraProjs ++ hdr.reqs.reqHypIds.map (⟨·.raw⟩) ++ extraReqIds.map (⟨·.raw⟩)
  let baseCtx ← mkBaseLowerCtx subFnStr (hdr.paramNames ++ extraIds.map (·.getId.toString))
    hasAwait true true (includeDbs := false)
  let some (runExpr, _, _) ← elabServerHandler hasAwait subFnStr subFnIdent
      extraBinderIds extraBinderTys extraCallArgs retTyTerm cb.errTyTerm baseCtx bodyStmts none | return none
  return some runExpr

private def mkChanDispatchArm (cb : ChanBodyCtx) (kindLit : TSyntax `num) (bodyInParams : Term) :
    CommandElabM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
  let chLit := Syntax.mkStrLit cb.hdr.chStr
  let decoded ← mkProtoDecodeBind (mkIdent `wsParams) (mkIdent `_chParams) cb.paramTupleTy cb.hdr.pIdents cb.pProjs bodyInParams
  `(Lean.Parser.Term.matchAltExpr| | $kindLit:num, $chLit => $decoded)

private def elabChanOnJoin (cb : ChanBodyCtx) :
    SrvElabM (Option (Bool × Term × TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let hdr := cb.hdr
  let (hasJoinSnapshot, joinTyTerm, joinRunTerm) ← match hdr.onJoin? with
    | some (some snapTyStx, stmts) =>
        let jty ← liftMacroM <| lowerSrvType snapTyStx (allowFallible := false) s!"`on_join` return type of `channel {hdr.chStr}`"
        let some r ← runChanSubHandler cb "onJoin" #[] #[] #[] #[] #[] jty.term false stmts | return none
        pure (true, jty.term, ← `($r >>= fun _jRes => Pure.pure (_jRes.map Qed.Proto.encode)))
    | some (none, stmts) =>
        let jt ← `(Unit)
        let some r ← runChanSubHandler cb "onJoin" #[] #[] #[] #[] #[] jt true stmts | return none
        pure (false, jt, ← liftM (wrapEmptyWs r))
    | none =>
        pure (false, ← `(Unit), ← `(Pure.pure (Except.ok ByteArray.empty)))
  let arm ← liftM <| mkChanDispatchArm cb (Syntax.mkNumLit "1")
    (← liftM <| wrapReqs hdr.reqs.reqPropTerms hdr.reqs.reqHypIds hdr.reqs.reqLabels joinRunTerm)
  return some (hasJoinSnapshot, joinTyTerm, arm)

private structure ChanSendInfo where
  hasSend             : Bool := false
  spIdents            : Array Ident := #[]
  spTyTerms           : Array Term := #[]
  sendParamTypeConsts : Array Name := #[]
  sendReqConst?       : Option Name := none
  sendReqLabel        : String := ""
  arm?                : Option (TSyntax ``Lean.Parser.Term.matchAltExpr) := none

private def elabChanOnSend (cb : ChanBodyCtx) : SrvElabM (Option ChanSendInfo) := do
  let c ← read
  let hdr := cb.hdr
  let some (rawSParams, rawSReqs, sBody) := hdr.onSend? | return some {}
  let (spIdents, spTyTerms, spNames) ←
    parseSrvParams s!"`channel {hdr.chStr}`" "`on_send` parameter" rawSParams (extraShadow := hdr.paramNames)
  let sendParamTypeConsts ← liftM <| elabParamTypeAbbrevs hdr.chIdent c.srvName c.fullSrvName hdr.chName "_SendParam_" spTyTerms
  let sReqs ← elabRequiresClauses hdr.chIdent hdr.chName s!"{hdr.chStr}.on_send" "_hSReq" "_send_req"
    (hdr.paramNames ++ spNames) spNames spIdents spTyTerms rawSReqs
    (excludedClientVars := hdr.paramNames) (trackAuth := false)
  let sendTupleTy ← liftMacroM <| buildProdType spTyTerms
  let sTupleVar := mkIdent `_chSendVal
  let sProjs ← extractTupleProjections sTupleVar spTyTerms.size
  let some sendRun ← runChanSubHandler cb "onSend" spIdents spTyTerms sProjs sReqs.reqHypIds sReqs.reqHypTys (← `(Unit)) true sBody | return none
  let sendOut ← liftM (wrapEmptyWs sendRun)
  let sendGuarded ← liftM <| wrapReqs (hdr.reqs.reqPropTerms ++ sReqs.reqPropTerms)
    (hdr.reqs.reqHypIds ++ sReqs.reqHypIds) (hdr.reqs.reqLabels ++ sReqs.reqLabels) sendOut
  let sendDecode ← liftM <| mkProtoDecodeBind (mkIdent `wsPayload) sTupleVar sendTupleTy spIdents sProjs sendGuarded
  let arm ← liftM <| mkChanDispatchArm cb (Syntax.mkNumLit "2") sendDecode
  return some {
    hasSend := true, spIdents, spTyTerms, sendParamTypeConsts,
    sendReqConst? := sReqs.clientReqConst?, sendReqLabel := sReqs.clientReqLabel,
    arm? := some arm
  }

private def emitChanClientHelpers (cb : ChanBodyCtx) (hasJoinSnapshot : Bool) (joinTyTerm : Term)
    (sendInfo : ChanSendInfo) : SrvElabM (String × Name) := do
  let c ← read
  let hdr := cb.hdr
  let (pIdents, pTyTerms) := (hdr.pIdents, hdr.pTyTerms)
  let chLit := Syntax.mkStrLit hdr.chStr
  let joinAbbrevId := mkIdentFrom hdr.chIdent (c.srvName ++ hdr.chName.appendAfter "_Join")
  liftM <| elabCommand (← `(command| abbrev $joinAbbrevId : Type := $joinTyTerm))
  let keyId := mkIdentFrom hdr.chIdent (c.srvName ++ hdr.chName.appendAfter "_key")
  let paramTupleVal ← liftMacroM <| buildTupleVal (pIdents.map (⟨·.raw⟩))
  liftM <| elabCommand (← `(command|
    def $keyId $[($pIdents:ident : $pTyTerms:term)]* : String := Qed.wsTopicKey $chLit $paramTupleVal))
  let wireEvTerm : Term ← match hdr.ensId? with
    | some eid =>
        let ensApp ← mkAppTerms eid (pIdents.map (⟨·.raw⟩))
        `(Qed.Ensured $(hdr.evTyTerm) ($ensApp))
    | none => pure hdr.evTyTerm
  let (subId, slotId, recId, onJoinId, onMsgId, onStatusId) :=
    (mkIdentFrom hdr.chIdent (c.srvName ++ hdr.chName.appendAfter "_sub"),
     mkIdent `slot, mkIdent `rec, mkIdent `onJoin, mkIdent `onMsg, mkIdent `onStatus)
  let wsPathStr := s!"/_qed/ws/{c.srvShort}"
  let wsPathLit := Syntax.mkStrLit wsPathStr
  let mkProtoCb (ty : Term) (onOk : Ident) : CommandElabM Term :=
    `(fun bs => match Qed.Proto.decode (α := $ty) bs with
      | Except.ok v    => $onOk v
      | Except.error e => $onStatusId (Qed.SocketStatus.failed e))
  let onJoinDecTerm ← if hasJoinSnapshot then liftM (mkProtoCb joinTyTerm onJoinId) else `(fun _ => $onJoinId ())
  let onEvDecTerm ← liftM (mkProtoCb wireEvTerm onMsgId)
  liftM <| elabCommand (← `(command|
    set_option linter.unusedVariables false in
    def $subId {msg : Type} ($slotId:ident : String) $[($pIdents:ident : $pTyTerms:term)]*
        ($recId:ident : Qed.Reconnect) ($onJoinId:ident : $joinTyTerm → msg)
        ($onMsgId:ident : $wireEvTerm → msg) ($onStatusId:ident : Qed.SocketStatus → msg) : Qed.Cmd msg :=
      Qed.Cmd.wsMuxSub $slotId $wsPathLit $chLit (Qed.Proto.encode $paramTupleVal) $recId
        $onJoinDecTerm $onEvDecTerm $onStatusId))
  let unsubId := mkIdentFrom hdr.chIdent (c.srvName ++ hdr.chName.appendAfter "_unsub")
  liftM <| elabCommand (← `(command|
    def $unsubId {msg : Type} ($slotId:ident : String) : Qed.Cmd msg := Qed.Cmd.wsMuxUnsub $slotId))
  let sendHelperConst ←
    if sendInfo.hasSend then
      let sendId := mkIdentFrom hdr.chIdent (c.srvName ++ hdr.chName.appendAfter "_send")
      let (spIdents, spTyTerms) := (sendInfo.spIdents, sendInfo.spTyTerms)
      let sendTupleVal ← liftMacroM <| buildTupleVal (spIdents.map (⟨·.raw⟩))
      liftM <| elabCommand (← `(command|
        def $sendId {msg : Type} ($slotId:ident : String) $[($spIdents:ident : $spTyTerms:term)]* : Qed.Cmd msg :=
          Qed.Cmd.wsMuxSend $slotId (Qed.Proto.encode $sendTupleVal)))
      pure (c.fullSrvName ++ hdr.chName.appendAfter "_send")
    else pure .anonymous
  return (wsPathStr, sendHelperConst)

def elabServerChannelBody (hdr : ParsedChanHeader) :
    SrvElabM (Option (Array (TSyntax ``Lean.Parser.Term.matchAltExpr))) := do
  let c ← read
  let cb : ChanBodyCtx := {
    hdr, errTyTerm := ← `(Qed.Server.ApiError),
    paramTupleTy := ← liftMacroM <| buildProdType hdr.pTyTerms,
    pProjs := ← extractTupleProjections (mkIdent `_chParams) hdr.pTyTerms.size
  }
  let some (hasJoinSnapshot, joinTyTerm, joinArm) ← elabChanOnJoin cb | return none
  let some sendInfo ← elabChanOnSend cb | return none
  let leaveRunTerm ← match hdr.onLeave? with
    | some stmts =>
        let some r ← runChanSubHandler cb "onLeave" #[] #[] #[] #[] #[] (← `(Unit)) true stmts | return none
        liftM (wrapEmptyWs r)
    | none => `(Pure.pure (Except.ok ByteArray.empty))
  let leaveArm ← liftM <| mkChanDispatchArm cb (Syntax.mkNumLit "3")
    (← liftM <| wrapReqs hdr.reqs.reqPropTerms hdr.reqs.reqHypIds hdr.reqs.reqLabels leaveRunTerm)
  let arms := #[joinArm] ++ (match sendInfo.arm? with | some a => #[a] | none => #[]) ++ #[leaveArm]
  let (wsPathStr, sendHelperConst) ← emitChanClientHelpers cb hasJoinSnapshot joinTyTerm sendInfo
  if (← hasSrvErrors) then return none
  modifyEnv fun env => Qed.channelRegistry.addEntry env {
    fullName := c.fullSrvName ++ hdr.chName, ownerName := c.fullSrvName, ownerShort := c.srvShort
    channelName := hdr.chStr, kind := .fullstack c.fullSrvName c.srvShort wsPathStr
    paramNames := hdr.pIdents.map (·.getId), paramCount := hdr.pIdents.size
    paramTypeConsts := hdr.paramTypeConsts
    eventTypeConst := c.fullSrvName ++ hdr.chName.appendAfter "_Event"
    hasJoinSnapshot, joinTypeConst := c.fullSrvName ++ hdr.chName.appendAfter "_Join"
    hasSend := sendInfo.hasSend
    sendParamCount := sendInfo.spIdents.size, sendParamTypeConsts := sendInfo.sendParamTypeConsts
    sendReqConst := sendInfo.sendReqConst?, sendReqLabel := sendInfo.sendReqLabel
    requiresAuth := hdr.reqs.requiresAuth, clientReqConst := hdr.reqs.clientReqConst?
    clientReqLabel := hdr.reqs.clientReqLabel, hasEnsures := hdr.ensConst?.isSome
    ensPredConst := hdr.ensConst?, defaultReconnect := hdr.recPolicy
    keyHelperConst := c.fullSrvName ++ hdr.chName.appendAfter "_key"
    subHelperConst := c.fullSrvName ++ hdr.chName.appendAfter "_sub"
    sendHelperConst
    unsubHelperConst := c.fullSrvName ++ hdr.chName.appendAfter "_unsub"
  }
  return some arms

end ChannelElab

end Qed.Server
