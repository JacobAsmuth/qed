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
  reqPropTerms   : Array Lean.Term
  reqHypIds      : Array Lean.Ident
  reqHypTys      : Array Lean.Term
  reqLabels      : Array String
  requiresAuth   : Bool
  clientReqConst : Option Lean.Name
  clientReqLabel : String
  ensId?         : Option Lean.Ident
  ensConst?      : Option Lean.Name
  recPolicy      : Qed.Reconnect
  onJoin?        : Option (Option Lean.Syntax × Array Lean.Syntax)
  onSend?        : Option (Array Lean.Syntax × Array Lean.Syntax × Array Lean.Syntax)
  onLeave?       : Option (Array Lean.Syntax)
  sig            : SrvChanSig

open Lean Elab Command in
def elabServerChannelHeader (priorRep priorUnrep : Nat)
    (srvName fullSrvName : Name) (stateFieldNames envVarNames : Array String)
    (existingChanNames : Array String) (chStx : Syntax) :
    CommandElabM (Option (ParsedChanHeader × Array Name)) := do
  let chIdent : Ident := ⟨(chStx.getArg 1)⟩
  let chName := chIdent.getId
  let chStr := chName.toString
  if existingChanNames.contains chStr then
    throwErrorAt chIdent s!"duplicate `channel {chStr}` in `server {srvName}`"

  let rawParams := (chStx.getArg 3).getSepArgs
  let mut pIdents : Array Ident := #[]
  let mut pTyTerms : Array Term := #[]
  let mut paramNames : Array String := #[]
  for rp in rawParams do
    let pid : Ident := ⟨(rp.getArg 0)⟩
    let pstr := pid.getId.toString
    if pstr == "ctx" || pstr == "event" then
      throwErrorAt pid s!"`{pstr}` is reserved inside `channel {chStr}`; rename this parameter"
    if paramNames.contains pstr || envVarNames.contains pstr || stateFieldNames.contains pstr then
      throwErrorAt pid s!"parameter `{pstr}` shadows an existing parameter, `env`, or `state` binding"
    let pty ← liftMacroM <| ParsedSrvType.parse (rp.getArg 2)
    liftMacroM <| pty.validate (allowFallible := false) s!"channel parameter `{pstr}`"
    pIdents := pIdents.push pid
    pTyTerms := pTyTerms.push (← liftMacroM pty.toPayloadTerm)
    paramNames := paramNames.push pstr

  let evTy ← liftMacroM <| ParsedSrvType.parse (chStx.getArg 6)
  liftMacroM <| evTy.validate (allowFallible := false) s!"event type of `channel {chStr}`"
  let evTyTerm ← liftMacroM evTy.toPayloadTerm

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
      if sk == ``srvChanReqClause then
        reqExprs := reqExprs ++ ((sub.getArg 0).getArg 1).getSepArgs
      else if sk == ``srvChanEnsClause then
        ensExprs := ensExprs ++ ((sub.getArg 0).getArg 1).getSepArgs
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
        let sParams := (sub.getArg 2).getSepArgs
        let sReqs := (sub.getArg 5).getArgs.flatMap fun rl => (rl.getArg 1).getSepArgs
        let sBody := (sub.getArg 6).getArgs
        onSend? := some (sParams, sReqs, sBody)
      else if sk == ``srvChanOnLeaveClause then
        if onLeave?.isSome then throwErrorAt sub s!"duplicate `on_leave` in `channel {chStr}`"
        onLeave? := some (suiteStmts (sub.getArg 2))
      else
        throwErrorAt sub s!"unexpected clause in `channel {chStr}`"

  let evAbbrevId := mkIdentFrom chIdent (srvName ++ chName.appendAfter "_Event")
  elabCommand (← `(command| abbrev $evAbbrevId : Type := $evTyTerm))
  let paramTypeConsts ← elabParamTypeAbbrevs chIdent srvName fullSrvName chName "_Param_" pTyTerms

  let reqs ← elabRequiresClauses chIdent srvName fullSrvName chName chStr "_hChReq" "_req"
    stateFieldNames envVarNames paramNames paramNames pIdents pTyTerms reqExprs

  let mut ensProps : Array Term := #[]
  for eExpr in ensExprs do
    if exprHasAwait eExpr then
      throwErrorAt eExpr "`ensures` postcondition cannot contain `await`"
    let ensCtx : LowerCtx := {
      fnName := chStr, stateFields := stateFieldNames, envVars := envVarNames,
      locals := paramNames.push "event", stateRule := .forbidInEnsures,
      allowAwait := false, allowUnwrap := false, hasFallible := false,
      isOption := false, innerOptTy? := none, forbidCtxEnv := true
    }
    let (pTerm, _) ← (lowerExpr ensCtx .propInv eExpr).run {}
    ensProps := ensProps.push pTerm

  let (ensId?, ensConst?) : Option Ident × Option Name ←
    if ensProps.isEmpty then pure (none, none)
    else
      let ensId := mkIdentFrom chIdent (srvName ++ chName.appendAfter "_ens")
      let evId := mkIdent `event
      let ensConj ← buildPropConj ensProps
      elabCommand (← `(command|
        set_option linter.unusedVariables false in
        @[simp] abbrev $ensId $[($pIdents:ident : $pTyTerms:term)]* ($evId:ident : $evTyTerm) : Prop := $ensConj))
      pure (some ensId, some (fullSrvName ++ chName.appendAfter "_ens"))

  if hasNewErrors (← get).messages priorRep priorUnrep then return none

  -- Emit `<S>.<ch>_mkEmit` (checked at every `emit <ch>(...)` site!)
  let mkEmitId := mkIdentFrom chIdent (srvName ++ chName.appendAfter "_mkEmit")
  let evVar := mkIdent `_ev
  let chLit := Syntax.mkStrLit chStr
  let paramTupleVal ← liftMacroM <| buildTupleVal (pIdents.map (⟨·.raw⟩))
  let extraBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ← match ensId? with
    | some eid =>
        let ensApp ← (pIdents.push evVar).foldlM (init := (eid : Term)) fun acc x => `($acc $x)
        pure #[← `(bracketedBinder| (_hEns : $ensApp))]
    | none => pure #[]
  elabCommand (← `(command|
    set_option linter.unusedVariables false in
    @[inline] def $mkEmitId $[($pIdents:ident : $pTyTerms:term)]* ($evVar:ident : $evTyTerm)
        $[$extraBinders:bracketedBinder]* : Qed.Server.WsEmit :=
      { topic := Qed.wsTopicKey $chLit $paramTupleVal, payload := Qed.Proto.encode $evVar }))

  if hasNewErrors (← get).messages priorRep priorUnrep then return none

  let sig : SrvChanSig := { name := chStr, mkEmitId, paramCount := pIdents.size, hasEnsures := ensId?.isSome }
  return some ({
    chIdent, chName, chStr, pIdents, pTyTerms, paramNames, paramTypeConsts, evTyTerm,
    reqPropTerms := reqs.reqPropTerms, reqHypIds := reqs.reqHypIds, reqHypTys := reqs.reqHypTys,
    reqLabels := reqs.reqLabels, requiresAuth := reqs.requiresAuth,
    clientReqConst := reqs.clientReqConst?, clientReqLabel := reqs.clientReqLabel,
    ensId?, ensConst?, recPolicy, onJoin?, onSend?, onLeave?, sig
  }, reqs.extRoots)

open Lean Elab Command in
private def unwrapOptionalOuterAtomic (stmts : Array Syntax) : Array Syntax :=
  if !blockHasAwait stmts && stmts.size == 1 && stmts[0]!.getKind == ``qedStmtAtomic then
    suiteStmts stmts[0]![2]
  else stmts

open Lean Elab Command in
def ensureUnitReturn (ref : Syntax) (stmts : Array Syntax) : Array Syntax :=
  if blockAlwaysReturns stmts then stmts
  else
    let info := SourceInfo.fromRef ref
    stmts.push (Syntax.node info ``qedStmtReturn #[Syntax.atom info "return", Syntax.node info nullKind #[]])

private structure ChanBodyCtx where
  priorRep        : Nat
  priorUnrep      : Nat
  srvName         : Lean.Name
  fullSrvName     : Lean.Name
  srvShort        : String
  hasState        : Bool
  stateId         : Lean.Ident
  stateInvId      : Lean.Ident
  ctxId           : Lean.Ident
  envIdents       : Array Lean.Ident
  envTypes        : Array Lean.Term
  stateFieldNames : Array String
  envVarNames     : Array String
  invs            : Array ParsedInv
  mutInvs         : Array ParsedMutInv
  chanSigs        : Array SrvChanSig
  hdr             : ParsedChanHeader
  ctxTyTerm       : Lean.Term
  errTyTerm       : Lean.Term
  paramTupleTy    : Lean.Term
  pProjs          : Array Lean.Term
  extRootsRef     : IO.Ref (Array Lean.Name)
  deferredProofs  : IO.Ref (Array (Lean.Elab.Command.CommandElabM Bool))

open Lean Elab Command in
private def runChanSubHandler (c : ChanBodyCtx) (subSuffix : String)
    (extraIds : Array Ident) (extraTys : Array Term) (extraProjs : Array Term)
    (extraReqIds : Array Ident) (extraReqTys : Array Term)
    (retTyTerm : Term) (isUnitRet : Bool) (rawStmts : Array Syntax) :
    CommandElabM (Option Term) := do
  let hdr := c.hdr
  let normStmts := unwrapOptionalOuterAtomic rawStmts
  let bodyStmts := if isUnitRet then ensureUnitReturn hdr.chIdent normStmts else normStmts
  if !isUnitRet && !blockAlwaysReturns bodyStmts then
    throwErrorAt hdr.chIdent s!"missing `return` on fallthrough path of `{hdr.chStr}.{subSuffix}`"
  let subFnStr := s!"{hdr.chStr}_{subSuffix}"
  let subFnIdent := mkIdentFrom hdr.chIdent (hdr.chName.appendAfter s!"_{subSuffix}")
  let hasAwait := blockHasAwait bodyStmts
  let allBinderIds := c.envIdents ++ #[c.ctxId] ++ hdr.pIdents ++ extraIds ++ hdr.reqHypIds ++ extraReqIds
  let allBinderTys := c.envTypes ++ #[c.ctxTyTerm] ++ hdr.pTyTerms ++ extraTys ++ hdr.reqHypTys ++ extraReqTys
  let callArgs : Array Term :=
    c.envIdents.map (⟨·.raw⟩) ++ #[⟨c.ctxId.raw⟩] ++ c.pProjs ++ extraProjs ++
    hdr.reqHypIds.map (⟨·.raw⟩) ++ extraReqIds.map (⟨·.raw⟩)
  let baseCtx : LowerCtx := {
    fnName := subFnStr, stateFields := c.stateFieldNames, envVars := c.envVarNames,
    locals := hdr.paramNames ++ extraIds.map (·.getId.toString),
    stateRule := if c.hasState then .pureStep (mkIdent `_s0) else .statelessServer,
    allowAwait := hasAwait, allowUnwrap := true, hasFallible := true,
    isOption := false, innerOptTy? := none, channels := c.chanSigs
  }
  if c.hasState && !hasAwait then
    let some (runExpr, _, er) ← elabServerPureFn c.priorRep c.priorUnrep
        c.srvName subFnStr subFnIdent c.stateId c.stateInvId
        allBinderIds allBinderTys callArgs retTyTerm c.errTyTerm baseCtx bodyStmts
        c.invs c.mutInvs c.stateFieldNames c.envVarNames none c.deferredProofs | return none
    c.extRootsRef.modify fun acc => acc ++ er.filter (!acc.contains ·)
    return some runExpr
  else if c.hasState && hasAwait then
    let some (hApp, _, er) ← elabServerAsyncFn c.priorRep c.priorUnrep
        c.srvName subFnStr subFnIdent c.stateId c.stateInvId
        allBinderIds allBinderTys callArgs retTyTerm c.errTyTerm baseCtx bodyStmts
        c.invs c.mutInvs c.stateFieldNames c.envVarNames none c.deferredProofs | return none
    c.extRootsRef.modify fun acc => acc ++ er.filter (!acc.contains ·)
    return some hApp
  else
    let some (_, _, hApp, er, _) ← elabStatelessHandler c.priorRep c.priorUnrep hdr.chIdent c.srvName subFnIdent.getId
        allBinderIds allBinderTys callArgs retTyTerm c.errTyTerm baseCtx bodyStmts | return none
    c.extRootsRef.modify fun acc => acc ++ er.filter (!acc.contains ·)
    return some hApp

open Lean Elab Command in
private def mkChanDispatchArm (c : ChanBodyCtx) (kindLit : TSyntax `num) (bodyInParams : Term) :
    CommandElabM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
  let chLit := Syntax.mkStrLit c.hdr.chStr
  let paramsBytesVar := mkIdent `wsParams
  let pTupleVar := mkIdent `_chParams
  let bound ← (c.hdr.pIdents.zip c.pProjs).foldrM (init := bodyInParams) fun (pid, prj) acc =>
    `(let $pid:ident := $prj; $acc)
  `(Lean.Parser.Term.matchAltExpr|
    | $kindLit:num, $chLit =>
        match Qed.Proto.decode (α := $(c.paramTupleTy)) $paramsBytesVar with
        | Except.error _e => Pure.pure (Except.error (Qed.Server.ApiError.badRequest _e))
        | Except.ok $pTupleVar:ident => $bound)

open Lean Elab Command in
private def elabChanOnJoin (c : ChanBodyCtx) :
    CommandElabM (Option (Bool × Term × TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let hdr := c.hdr
  let (hasJoinSnapshot, joinTyTerm, joinRunTerm) ← match hdr.onJoin? with
    | some (some snapTyStx, stmts) =>
        let jty ← liftMacroM <| ParsedSrvType.parse snapTyStx
        liftMacroM <| jty.validate (allowFallible := false) s!"`on_join` return type of `channel {hdr.chStr}`"
        let jt ← liftMacroM jty.toPayloadTerm
        let some r ← runChanSubHandler c "onJoin" #[] #[] #[] #[] #[] jt false stmts | return none
        pure (true, jt, ← `($r >>= fun _jRes => Pure.pure (_jRes.map Qed.Proto.encode)))
    | some (none, stmts) =>
        let jt ← `(Unit)
        let some r ← runChanSubHandler c "onJoin" #[] #[] #[] #[] #[] jt true stmts | return none
        pure (false, jt, ← `($r >>= fun _jRes => Pure.pure (_jRes.map fun _ => ByteArray.empty)))
    | none =>
        pure (false, ← `(Unit), ← `(Pure.pure (Except.ok ByteArray.empty)))
  let arm ← mkChanDispatchArm c (Syntax.mkNumLit "1")
    (← wrapReqs hdr.reqPropTerms hdr.reqHypIds hdr.reqLabels joinRunTerm)
  return some (hasJoinSnapshot, joinTyTerm, arm)

private structure ChanSendInfo where
  hasSend             : Bool := false
  spIdents            : Array Lean.Ident := #[]
  spTyTerms           : Array Lean.Term := #[]
  sendParamTypeConsts : Array Lean.Name := #[]
  sendReqConst?       : Option Lean.Name := none
  sendReqLabel        : String := ""
  arm?                : Option (Lean.TSyntax ``Lean.Parser.Term.matchAltExpr) := none

open Lean Elab Command in
private def elabChanOnSend (c : ChanBodyCtx) : CommandElabM (Option ChanSendInfo) := do
  let hdr := c.hdr
  let some (rawSParams, rawSReqs, sBody) := hdr.onSend? | return some {}
  let mut spIdents : Array Ident := #[]
  let mut spTyTerms : Array Term := #[]
  let mut spNames : Array String := #[]
  for srp in rawSParams do
    let spid : Ident := ⟨(srp.getArg 0)⟩
    let spstr := spid.getId.toString
    if spstr == "ctx" || hdr.paramNames.contains spstr || spNames.contains spstr ||
       c.envVarNames.contains spstr || c.stateFieldNames.contains spstr then
      throwErrorAt spid s!"`on_send` parameter `{spstr}` shadows an existing binding in `channel {hdr.chStr}`"
    let spty ← liftMacroM <| ParsedSrvType.parse (srp.getArg 2)
    liftMacroM <| spty.validate (allowFallible := false) s!"`on_send` parameter `{spstr}`"
    spIdents := spIdents.push spid
    spTyTerms := spTyTerms.push (← liftMacroM spty.toPayloadTerm)
    spNames := spNames.push spstr
  let sendParamTypeConsts ← elabParamTypeAbbrevs hdr.chIdent c.srvName c.fullSrvName hdr.chName "_SendParam_" spTyTerms
  let sReqs ← elabRequiresClauses hdr.chIdent c.srvName c.fullSrvName hdr.chName s!"{hdr.chStr}.on_send" "_hSReq" "_send_req"
    c.stateFieldNames c.envVarNames (hdr.paramNames ++ spNames) spNames spIdents spTyTerms rawSReqs
    (excludedClientVars := hdr.paramNames) (trackAuth := false)
  c.extRootsRef.modify fun acc => acc ++ sReqs.extRoots.filter (!acc.contains ·)
  let sendTupleTy ← buildTupleType spTyTerms
  let sTupleVar := mkIdent `_chSendVal
  let payloadBytesVar := mkIdent `wsPayload
  let sProjs ← extractTupleProjections sTupleVar spTyTerms.size
  let unitTy ← `(Unit)
  let some sendRun ← runChanSubHandler c "onSend" spIdents spTyTerms sProjs sReqs.reqHypIds sReqs.reqHypTys unitTy true sBody | return none
  let sendOut ← `($sendRun >>= fun _sRes => Pure.pure (_sRes.map fun _ => ByteArray.empty))
  let sendGuarded ← wrapReqs (hdr.reqPropTerms ++ sReqs.reqPropTerms) (hdr.reqHypIds ++ sReqs.reqHypIds) (hdr.reqLabels ++ sReqs.reqLabels) sendOut
  let sendBound ← (spIdents.zip sProjs).foldrM (init := sendGuarded) fun (spid, sprj) acc =>
    `(let $spid:ident := $sprj; $acc)
  let sendDecode ← `(match Qed.Proto.decode (α := $sendTupleTy) $payloadBytesVar with
    | Except.error _e2 => Pure.pure (Except.error (Qed.Server.ApiError.badRequest _e2))
    | Except.ok $sTupleVar:ident => $sendBound)
  let arm ← mkChanDispatchArm c (Syntax.mkNumLit "2") sendDecode
  return some {
    hasSend := true, spIdents, spTyTerms, sendParamTypeConsts,
    sendReqConst? := sReqs.clientReqConst?, sendReqLabel := sReqs.clientReqLabel,
    arm? := some arm
  }

open Lean Elab Command in
private def emitChanClientHelpers (c : ChanBodyCtx) (hasJoinSnapshot : Bool) (joinTyTerm : Term)
    (sendInfo : ChanSendInfo) : CommandElabM (String × Name) := do
  let hdr := c.hdr
  let pIdents := hdr.pIdents
  let pTyTerms := hdr.pTyTerms
  let chLit := Syntax.mkStrLit hdr.chStr
  let joinAbbrevId := mkIdentFrom hdr.chIdent (c.srvName ++ hdr.chName.appendAfter "_Join")
  elabCommand (← `(command| abbrev $joinAbbrevId : Type := $joinTyTerm))
  let keyId := mkIdentFrom hdr.chIdent (c.srvName ++ hdr.chName.appendAfter "_key")
  let paramTupleVal ← liftMacroM <| buildTupleVal (pIdents.map (⟨·.raw⟩))
  elabCommand (← `(command|
    def $keyId $[($pIdents:ident : $pTyTerms:term)]* : String :=
      Qed.wsTopicKey $chLit $paramTupleVal))
  let wireEvTerm : Term ← match hdr.ensId? with
    | some eid =>
        let ensApp ← pIdents.foldlM (init := (eid : Term)) fun acc p => `($acc $p)
        `(Qed.Ensured $(hdr.evTyTerm) ($ensApp))
    | none => pure hdr.evTyTerm
  let subId := mkIdentFrom hdr.chIdent (c.srvName ++ hdr.chName.appendAfter "_sub")
  let slotId := mkIdent `slot
  let recId := mkIdent `rec
  let onJoinId := mkIdent `onJoin
  let onMsgId := mkIdent `onMsg
  let onStatusId := mkIdent `onStatus
  let wsPathStr := s!"/_qed/ws/{c.srvShort}"
  let wsPathLit := Syntax.mkStrLit wsPathStr
  let onJoinDecTerm : Term ←
    if hasJoinSnapshot then
      `(fun bs =>
          match Qed.Proto.decode (α := $joinTyTerm) bs with
          | Except.ok v    => $onJoinId v
          | Except.error e => $onStatusId (Qed.SocketStatus.failed e))
    else
      `(fun _ => $onJoinId ())
  elabCommand (← `(command|
    set_option linter.unusedVariables false in
    def $subId {msg : Type} ($slotId:ident : String) $[($pIdents:ident : $pTyTerms:term)]*
        ($recId:ident : Qed.Reconnect) ($onJoinId:ident : $joinTyTerm → msg)
        ($onMsgId:ident : $wireEvTerm → msg) ($onStatusId:ident : Qed.SocketStatus → msg) : Qed.Cmd msg :=
      Qed.Cmd.wsMuxSub $slotId $wsPathLit $chLit (Qed.Proto.encode $paramTupleVal) $recId
        $onJoinDecTerm
        (fun bs =>
          match Qed.Proto.decode (α := $wireEvTerm) bs with
          | Except.ok v    => $onMsgId v
          | Except.error e => $onStatusId (Qed.SocketStatus.failed e))
        $onStatusId))
  let unsubId := mkIdentFrom hdr.chIdent (c.srvName ++ hdr.chName.appendAfter "_unsub")
  elabCommand (← `(command|
    def $unsubId {msg : Type} ($slotId:ident : String) : Qed.Cmd msg :=
      Qed.Cmd.wsMuxUnsub $slotId))
  let sendHelperConst ←
    if sendInfo.hasSend then
      let sendId := mkIdentFrom hdr.chIdent (c.srvName ++ hdr.chName.appendAfter "_send")
      let spIdents := sendInfo.spIdents
      let spTyTerms := sendInfo.spTyTerms
      let sendTupleVal ← liftMacroM <| buildTupleVal (spIdents.map (⟨·.raw⟩))
      elabCommand (← `(command|
        def $sendId {msg : Type} ($slotId:ident : String) $[($spIdents:ident : $spTyTerms:term)]* : Qed.Cmd msg :=
          Qed.Cmd.wsMuxSend $slotId (Qed.Proto.encode $sendTupleVal)))
      pure (c.fullSrvName ++ hdr.chName.appendAfter "_send")
    else pure .anonymous
  return (wsPathStr, sendHelperConst)

open Lean Elab Command in
def elabServerChannelBody (priorRep priorUnrep : Nat)
    (srvName fullSrvName : Name) (srvShort : String) (hasState : Bool)
    (stateId stateInvId ctxId : Ident)
    (envIdents : Array Ident) (envTypes : Array Term)
    (stateFieldNames envVarNames : Array String)
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (chanSigs : Array SrvChanSig) (hdr : ParsedChanHeader)
    (deferredProofs : IO.Ref (Array (CommandElabM Bool))) :
    CommandElabM (Option (Array (TSyntax ``Lean.Parser.Term.matchAltExpr) × Array Name)) := do
  let ctxTyTerm ← `(Qed.Server.RequestCtx)
  let errTyTerm ← `(Qed.Server.ApiError)
  let paramTupleTy ← buildTupleType hdr.pTyTerms
  let pProjs ← extractTupleProjections (mkIdent `_chParams) hdr.pTyTerms.size
  let extRootsRef ← IO.mkRef (#[] : Array Name)
  let c : ChanBodyCtx := {
    priorRep, priorUnrep, srvName, fullSrvName, srvShort, hasState,
    stateId, stateInvId, ctxId, envIdents, envTypes, stateFieldNames, envVarNames,
    invs, mutInvs, chanSigs, hdr, ctxTyTerm, errTyTerm, paramTupleTy, pProjs,
    extRootsRef, deferredProofs
  }
  let some (hasJoinSnapshot, joinTyTerm, joinArm) ← elabChanOnJoin c | return none
  let some sendInfo ← elabChanOnSend c | return none
  let leaveRunTerm ← match hdr.onLeave? with
    | some stmts =>
        let unitTy ← `(Unit)
        let some r ← runChanSubHandler c "onLeave" #[] #[] #[] #[] #[] unitTy true stmts | return none
        `($r >>= fun _lRes => Pure.pure (_lRes.map fun _ => ByteArray.empty))
    | none =>
        `(Pure.pure (Except.ok ByteArray.empty))
  let leaveArm ← mkChanDispatchArm c (Syntax.mkNumLit "3")
    (← wrapReqs hdr.reqPropTerms hdr.reqHypIds hdr.reqLabels leaveRunTerm)
  let arms := #[joinArm] ++ (match sendInfo.arm? with | some a => #[a] | none => #[]) ++ #[leaveArm]
  let (wsPathStr, sendHelperConst) ← emitChanClientHelpers c hasJoinSnapshot joinTyTerm sendInfo
  if hasNewErrors (← get).messages priorRep priorUnrep then return none
  modifyEnv fun env => Qed.channelRegistry.addEntry env {
    fullName := fullSrvName ++ hdr.chName
    ownerName := fullSrvName
    ownerShort := srvShort
    channelName := hdr.chStr
    kind := .fullstack fullSrvName srvShort wsPathStr
    paramNames := hdr.pIdents.map (·.getId)
    paramCount := hdr.pIdents.size
    paramTypeConsts := hdr.paramTypeConsts
    eventTypeConst := fullSrvName ++ hdr.chName.appendAfter "_Event"
    hasJoinSnapshot
    joinTypeConst := fullSrvName ++ hdr.chName.appendAfter "_Join"
    hasSend := sendInfo.hasSend
    sendParamNames := sendInfo.spIdents.map (·.getId)
    sendParamCount := sendInfo.spIdents.size
    sendParamTypeConsts := sendInfo.sendParamTypeConsts
    sendReqConst := sendInfo.sendReqConst?
    sendReqLabel := sendInfo.sendReqLabel
    requiresAuth := hdr.requiresAuth
    clientReqConst := hdr.clientReqConst
    clientReqLabel := hdr.clientReqLabel
    hasEnsures := hdr.ensConst?.isSome
    ensPredConst := hdr.ensConst?
    defaultReconnect := hdr.recPolicy
    keyHelperConst := fullSrvName ++ hdr.chName.appendAfter "_key"
    subHelperConst := fullSrvName ++ hdr.chName.appendAfter "_sub"
    sendHelperConst
    unsubHelperConst := fullSrvName ++ hdr.chName.appendAfter "_unsub"
  }
  return some (arms, ← extRootsRef.get)


end Qed.Server
