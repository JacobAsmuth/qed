import Qed.Server.FnElab
import Qed.Server.Invariant
import Qed.Server.Eval
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
  project?        : Option (Lean.Ident × Lean.Term × Lean.Ident) := none
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
  let mut rawProject? : Option (Syntax × Option Syntax × Array Syntax × Array Syntax) := none
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
        onSend? := some ((sub.getArg 2).getSepArgs, (sub.getArg 5).getArgs.flatMap fun rl => (rl.getArg 1).getSepArgs, suiteStmts (sub.getArg 6))
      else if sk == ``srvChanOnLeaveClause then
        if onLeave?.isSome then throwErrorAt sub s!"duplicate `on_leave` in `channel {chStr}`"
        onLeave? := some (suiteStmts (sub.getArg 2))
      else if sk == ``srvChanProjectClause then
        if rawProject?.isSome then throwErrorAt sub s!"duplicate `project` in `channel {chStr}`"
        let optRet? := if (sub.getArg 4).getNumArgs == 2 then some ((sub.getArg 4).getArg 1) else none
        rawProject? := some (sub.getArg 2, optRet?, (sub.getArg 6).getArgs, (sub.getArg 7).getArgs)
      else throwErrorAt sub s!"unexpected clause in `channel {chStr}`"
  let evId := c.fnSubId chIdent "_Event"
  elabSrvCmd (← `(command| abbrev $evId : Type := $evTyTerm))
  let paramTypeConsts ← liftM <| elabParamTypeAbbrevs chIdent c.srvName c.fullSrvName chName "_Param_" pTyTerms
  let reqs ← elabRequiresClauses chIdent chName chStr "_hChReq" "_req" paramNames paramNames pIdents pTyTerms reqExprs
  let some ensRes? ← elabEnsuresAbbrev chIdent chStr `event paramNames pIdents pTyTerms evTyTerm ensExprs | return none
  let (ensId?, ensConst?) : Option Ident × Option Name := (ensRes?.map (·.1), ensRes?.map (·.2.1))
  let mut projectInfo? : Option (Ident × Term × Ident) := none
  if let some (rawParamStx, optRet?, projContracts, projStmts) := rawProject? then
    let (rIds, rTys, _) ← parseSrvParams s!"`channel {chStr}.project`" "`project` parameter" #[rawParamStx] (reserved := #["result"]) (extraShadow := paramNames)
    let (rawId, rawTyTerm) := (rIds[0]!, rTys[0]!)
    let projRetTy : Term ← match optRet? with
      | some rt => pure (← liftMacroM <| lowerSrvType rt false s!"return type of `channel {chStr}.project`").term
      | none    => pure evTyTerm
    let projFnId := c.fnSubId chIdent "_project"
    let ctxTy ← `(Qed.Server.RequestCtx)
    let bodyTerm ← liftM <| Qed.lowerPureFnStmts s!"channel {chStr}.project" projStmts.toList
    elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      def $projFnId ($(c.ctxId):ident : $ctxTy) $[($pIdents:ident : $pTyTerms:term)]* ($rawId:ident : $rawTyTerm) : $evTyTerm := ($bodyTerm : $projRetTy)))
    if (← hasSrvErrors) then return none
    let allPIds := #[c.ctxId] ++ pIdents ++ #[rawId]
    let allPTys := #[ctxTy] ++ pTyTerms ++ #[rawTyTerm]
    let preHyps := reqs.reqHypIds.zip reqs.reqPropTerms
    liftM <| Qed.elabPureFnContracts projFnId projFnId allPIds allPTys evTyTerm projContracts preHyps
    if let some eid := ensId? then
      let ensApp ← mkAppTerms eid (pIdents.map (⟨·.raw⟩))
      let callT ← mkAppTerms projFnId (allPIds.map (⟨·.raw⟩))
      let reqBs : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ← preHyps.mapM fun (hid, hty) => `(bracketedBinder| ($hid:ident : $hty))
      let chEnsThmId := c.fnSubId chIdent "_project_channel_ensures"
      elabSrvCmd (← `(command|
        set_option linter.unusedVariables false in
        theorem $chEnsThmId ($(c.ctxId):ident : $ctxTy) $[($pIdents:ident : $pTyTerms:term)]* ($rawId:ident : $rawTyTerm) $[$reqBs:bracketedBinder]* :
            $ensApp ($callT) := by qedProveFnEnsures $projFnId $chEnsThmId))
    if (← hasSrvErrors) then return none
    projectInfo? := some (rawId, rawTyTerm, projFnId)
  let mkEmitId := c.fnSubId chIdent "_mkEmit"; let evVar := mkIdent `_ev
  let paramTupleVal ← liftMacroM <| buildTupleVal (pIdents.map (⟨·.raw⟩))
  let (emitPayloadTy, needEmitEns) := match projectInfo? with
    | some (_, rawTy, _) => (rawTy, false)
    | none               => (evTyTerm, ensId?.isSome)
  let extraBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ← match ensId?, needEmitEns with
    | some eid, true => pure #[← `(bracketedBinder| (_hEns : $(← mkAppTerms eid ((pIdents.push evVar).map (⟨·.raw⟩)))))]
    | _, _ => pure #[]
  elabSrvCmd (← `(command|
    set_option linter.unusedVariables false in
    @[inline] def $mkEmitId $[($pIdents:ident : $pTyTerms:term)]* ($evVar:ident : $emitPayloadTy) $[$extraBinders:bracketedBinder]* : Qed.Server.WsEmit :=
      { topic := Qed.wsTopicKey $(Syntax.mkStrLit chStr) $paramTupleVal, payload := Qed.Proto.encode $evVar }))
  if (← hasSrvErrors) then return none
  return some {
    chIdent, chName, chStr, pIdents, pTyTerms, paramNames, paramTypeConsts, evTyTerm, reqs, ensId?, ensConst?, recPolicy, onJoin?, onSend?, onLeave?,
    project? := projectInfo?,
    sig := { name := chStr, mkEmitId, paramCount := pIdents.size, hasEnsures := needEmitEns } }

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
private def wrapWithBefore? (beforeRun? : Option Term) (body : Term) : CommandElabM Term :=
  match beforeRun? with
  | none => pure body
  | some br => `($br >>= fun | Except.error _beforeErr => Pure.pure (Except.error _beforeErr) | Except.ok () => $body)

@[noinline]
private def elabServerChannelBody (hdr : ParsedChanHeader) (beforeRun? : Option Term := none) :
    SrvElabM (Option (Array (TSyntax ``Lean.Parser.Term.matchAltExpr) × Option (TSyntax ``Lean.Parser.Term.matchAltExpr))) := do
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
    let baseCtx ← mkBaseLowerCtx subStr (hdr.paramNames ++ hdr.reqs.extraLocals ++ eIds.map (·.getId.toString)) hasAw true true (includeDbs := false)
    let some hRes ← elabServerHandler hasAw subStr (mkIdentFrom hdr.chIdent (hdr.chName.appendAfter s!"_{suf}"))
        (hdr.pIdents ++ eIds ++ hdr.reqs.allBinderIds ++ eReqIds) (hdr.pTyTerms ++ eTys ++ hdr.reqs.allBinderTys ++ eReqTys)
        (pProjs ++ eProjs ++ hdr.reqs.allBinderArgs ++ eReqIds.map (⟨·.raw⟩)) retTy errTyTerm baseCtx body none | return none
    return some hRes.runExpr
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
  let joinArm ← liftM <| mkArm "1" (← liftM <| wrapWithBefore? beforeRun? (← liftM <| wrapAuthAndReqs hdr.reqs joinRunTerm))
  let mut hasSend := false; let mut spIdents : Array Ident := #[]; let mut spTyTerms : Array Term := #[]
  let mut sendParamTypeConsts : Array Name := #[]; let mut sendReqConst? : Option Name := none; let mut sendReqLabel := ""
  let mut sendArm? : Option (TSyntax ``Lean.Parser.Term.matchAltExpr) := none
  if let some (rawSParams, rawSReqs, sBody) := hdr.onSend? then
    let (spIds, spTys, spNames) ← parseSrvParams s!"`channel {hdr.chStr}`" "`on_send` parameter" rawSParams (extraShadow := hdr.paramNames ++ hdr.reqs.extraLocals)
    hasSend := true; spIdents := spIds; spTyTerms := spTys
    sendParamTypeConsts ← liftM <| elabParamTypeAbbrevs hdr.chIdent c.srvName c.fullSrvName hdr.chName "_SendParam_" spTys
    let sReqs ← elabRequiresClauses hdr.chIdent hdr.chName s!"{hdr.chStr}.on_send" "_hSReq" "_send_req"
      (hdr.paramNames ++ hdr.reqs.extraLocals ++ spNames) spNames spIds spTys rawSReqs (excludedClientVars := hdr.paramNames ++ hdr.reqs.extraLocals) (trackAuth := false)
    sendReqConst? := sReqs.clientReqConst?; sendReqLabel := sReqs.clientReqLabel
    let sendTupleTy ← liftMacroM <| buildProdType spTys; let sTupleVar := mkIdent `_chSendVal; let sProjs ← extractTupleProjections sTupleVar spTys.size
    let some sr ← runSub "onSend" spIds spTys sProjs sReqs.reqHypIds sReqs.reqPropTerms (← `(Unit)) true sBody | return none
    let sGuarded ← liftM <| wrapWithBefore? beforeRun? (← liftM <| wrapAuthAndReqs hdr.reqs (← liftM <| wrapReqs sReqs.reqPropTerms sReqs.reqHypIds sReqs.reqLabels (← liftM (wrapEmpty sr))))
    sendArm? := some (← liftM <| mkArm "2" (← liftM <| mkProtoDecodeBind (mkIdent `wsPayload) sTupleVar sendTupleTy spIds sProjs sGuarded))
  let leaveRunTerm ← match hdr.onLeave? with
    | some stmts =>
        let some r ← runSub "onLeave" #[] #[] #[] #[] #[] (← `(Unit)) true stmts | return none
        liftM (wrapEmpty r)
    | none => `(Pure.pure (Except.ok ByteArray.empty))
  let leaveArm ← liftM <| mkArm "3" (← liftM <| wrapAuthAndReqs hdr.reqs leaveRunTerm)
  let (wsPathStr, sendHelperConst) ← elabChanClientHelpers hdr hasJoinSnapshot hasSend joinTyTerm spIdents spTyTerms
  let projArm? : Option (TSyntax ``Lean.Parser.Term.matchAltExpr) ← match hdr.project? with
    | none => pure none
    | some (_, rawTyTerm, projFnId) =>
        let (wsPId, wsPayId, chPId, rawVar) := (mkIdent `wsParams, mkIdent `wsPayload, mkIdent `_chParams, mkIdent `_rawVal)
        let projCall ← mkAppTerms projFnId (#[⟨c.ctxId.raw⟩] ++ pProjs ++ #[⟨rawVar.raw⟩])
        some <$> `(Lean.Parser.Term.matchAltExpr| | $chLit =>
          match Qed.Proto.decode (α := $paramTupleTy) $wsPId:ident, Qed.Proto.decode (α := $rawTyTerm) $wsPayId:ident with
          | Except.ok $chPId:ident, Except.ok $rawVar:ident => Qed.Server.WsProjectOut.send (Qed.Proto.encode ($projCall))
          | _, _ => Qed.Server.WsProjectOut.drop)
  if (← hasSrvErrors) then return none
  modifyEnv fun env => Qed.channelRegistry.addEntry env {
    ChannelInfo.mkDefault c.fullSrvName c.srvName.toString hdr.chName (.fullstack c.fullSrvName c.srvName.toString wsPathStr) (hdr.pIdents.map (·.getId)) hdr.paramTypeConsts hdr.recPolicy with
    hasJoinSnapshot, joinTypeConst := c.fullSrvName ++ hdr.chName.appendAfter "_Join", hasSend, sendParamCount := spIdents.size, sendParamTypeConsts,
    sendReqConst := sendReqConst?, sendReqLabel, requiresAuth := hdr.reqs.requiresAuth, clientReqConst := hdr.reqs.clientReqConst?,
    clientReqLabel := hdr.reqs.clientReqLabel, hasEnsures := hdr.ensConst?.isSome, ensPredConst := hdr.ensConst?, sendHelperConst }
  return some (#[joinArm] ++ sendArm?.toArray ++ #[leaveArm], projArm?)

/-! ## `server` RPC / HTTP / Auth Hook & Command Elaborator -/

@[noinline]
private def elabFnClientStubs (fnIdent : Ident) (fnStr : String) (pIdents : Array Ident) (pTyTerms : Array Term)
    (reqTupleTy payloadTerm : Term) (innerOpt? : Option Term) (errTypeId? : Option Ident) (ensSpec? : Option FnEnsSpec)
    (reqs : LoweredRequires) : SrvElabM (Array Name) := do
  let c ← read; let pTerms : Array Term := pIdents.map (⟨·.raw⟩)
  let paramTypeConsts ← liftM <| elabParamTypeAbbrevs fnIdent c.srvName c.fullSrvName fnIdent.getId "_Param_" pTyTerms
  let ensPayloadTerm : Term ← match ensSpec? with
    | some ens => let a ← mkAppTerms ens.ensId pTerms; match innerOpt? with | some it => `(Option (Qed.Ensured $it ($a))) | none => `(Qed.Ensured $payloadTerm ($a))
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

private structure ParsedSrvEffContract where
  ref      : Syntax
  guards   : Array Syntax := #[]
  effTags  : Array Name := #[]
  ensPreds : Array Syntax := #[]
  errPreds : Array Syntax := #[]
  fails?   : Option (Option Nat) := none
  tac?     : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none

private structure ParsedSrvBlind where
  ref     : Syntax
  guards  : Array Syntax := #[]
  targets : Array Syntax := #[]
  tac?    : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none

private structure ParsedSrvContracts where
  requires   : Array Syntax := #[]
  topEnsures : Array Syntax := #[]
  topEnsTac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none
  effSpecs   : Array ParsedSrvEffContract := #[]
  blinds     : Array ParsedSrvBlind := #[]

private partial def collectSrvContracts (kindLabel : String) (guards : Array Syntax) (clauses : Array Syntax)
    (acc : ParsedSrvContracts) : CommandElabM ParsedSrvContracts := do
  let mut acc := acc
  let mut grpEffTags : Array Name := #[]
  let mut grpEns : Array Syntax := #[]
  let mut grpErr : Array Syntax := #[]
  let mut grpFails? : Option (Option Nat) := none
  let mut grpTac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none
  let mut grpRef? : Option Syntax := none
  let flushGroup (a : ParsedSrvContracts) (ref? : Option Syntax) (tags : Array Name)
      (ens err : Array Syntax) (fails? : Option (Option Nat)) (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : ParsedSrvContracts :=
    if tags.isEmpty && ens.isEmpty && err.isEmpty && fails?.isNone then a
    else { a with effSpecs := a.effSpecs.push { ref := ref?.getD Syntax.missing, guards, effTags := tags, ensPreds := ens, errPreds := err, fails?, tac? } }
  for cl0 in clauses do
    let k0 := cl0.getKind
    let cl := if k0 == ``srvCIReq || k0 == ``srvCIEns || k0 == ``srvCIEnsErr || k0 == ``srvCIEnsFails || k0 == ``srvCIEff || k0 == ``srvCIBlind then cl0.getArg 0 else cl0
    let k := cl.getKind
    if k == ``srvRequiresLine then
      unless guards.isEmpty do throwErrorAt cl s!"`requires` must appear at the top level of {kindLabel}"
      acc := { acc with requires := acc.requires ++ (cl.getArg 1).getSepArgs }
    else if k == ``srvEnsuresLine then
      let ps := (cl.getArg 1).getSepArgs; let t? := Qed.parseOptTacSeq (cl.getArg 2)
      if guards.isEmpty then
        if t?.isSome && acc.topEnsTac?.isSome then throwErrorAt cl s!"at most one `prove:` / `:= by` block is allowed per {kindLabel}"
        acc := { acc with topEnsures := acc.topEnsures ++ ps, topEnsTac? := acc.topEnsTac?.orElse fun _ => t? }
      else
        grpRef? := grpRef?.orElse fun _ => some cl; grpEns := grpEns ++ ps; grpTac? := grpTac?.orElse fun _ => t?
    else if k == ``srvEnsuresErrLine then
      grpRef? := grpRef?.orElse fun _ => some cl
      grpErr := grpErr ++ (cl.getArg 1).getSepArgs
      grpTac? := grpTac?.orElse fun _ => Qed.parseOptTacSeq (cl.getArg 2)
    else if k == ``srvEnsuresFailsLine then
      grpRef? := grpRef?.orElse fun _ => some cl
      let codeOpt := cl.getArg 1
      let code? := if codeOpt.getNumArgs == 1 then some (⟨codeOpt.getArg 0⟩ : TSyntax `num).getNat else none
      grpFails? := some code?
      grpTac? := grpTac?.orElse fun _ => Qed.parseOptTacSeq (cl.getArg 2)
    else if k == ``srvEffectLine then
      grpRef? := grpRef?.orElse fun _ => some cl
      for tag in (cl.getArg 0).getSepArgs do
        let tn := (tag.getArg 0).getId.eraseMacroScopes
        if !grpEffTags.contains tn then grpEffTags := grpEffTags.push tn
      grpTac? := grpTac?.orElse fun _ => Qed.parseOptTacSeq (cl.getArg 1)
    else if k == ``srvBlindToLine then
      acc := { acc with blinds := acc.blinds.push { ref := cl, guards, targets := (cl.getArg 1).getSepArgs, tac? := Qed.parseOptTacSeq (cl.getArg 2) } }
    else if k == ``srvCIIf then
      acc := flushGroup acc grpRef? grpEffTags grpEns grpErr grpFails? grpTac?
      grpEffTags := #[]; grpEns := #[]; grpErr := #[]; grpFails? := none; grpTac? := none; grpRef? := none
      acc ← collectSrvContracts kindLabel (guards ++ (cl.getArg 1).getSepArgs) (cl.getArg 3).getArgs acc
    else throwErrorAt cl s!"unexpected contract clause in {kindLabel}"
  return flushGroup acc grpRef? grpEffTags grpEns grpErr grpFails? grpTac?

private def parseSrvContracts (kindLabel : String) (clauses : Array Syntax) : CommandElabM ParsedSrvContracts :=
  collectSrvContracts kindLabel #[] clauses {}

private def effTagToTerm (effVar : Ident) (tag : Name) : CommandElabM Term := match tag with
  | `no_http     => `(($effVar:ident).isHttp = false)
  | `no_decrypt  => `(($effVar:ident).isDecrypt = false)
  | `no_crypto   => `(($effVar:ident).isCrypto = false)
  | `no_db_write => `(($effVar:ident).isDbWrite = false)
  | other        => throwError s!"unknown effect constraint `{other}`"

@[noinline]
private def elabSrvExtraContracts (fnIdent targetId : Ident) (thmBaseLeaf : Name) (fnStr : String)
    (isMonadic isFallible : Bool) (hasState : Bool) (paramIds : Array Ident)
    (binderIds : Array Ident) (binderTys : Array Term) (callT : Term)
    (payloadTerm errTyTerm : Term) (innerOpt? : Option Term)
    (contracts : ParsedSrvContracts) (unfoldIds : Array Ident := #[]) (defer : Bool := true)
    (isStepPair : Bool := false) (hasEmit : Bool := false) : SrvElabM Unit := do
  let c ← read
  let fnLit := Syntax.mkStrLit fnStr
  let emitCmd (cmd : Command) : SrvElabM Unit := if defer then deferSrvCmd cmd else elabSrvCmd cmd
  let lowerGuard (s : Syntax) : CommandElabM Term := liftMacroM (lowerSimpleQedExpr .propInv s)
  let mkGuardBinders (guards : Array Syntax) : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
    let mut bs : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
    for (g, i) in guards.zipIdx do
      bs := bs.push (← `(bracketedBinder| ($(mkIdent (Name.mkSimple s!"_hIf_{i}")):ident : $(← lowerGuard g))))
    return bs
  for (ec, idx) in contracts.effSpecs.zipIdx do
    let guardBinders ← liftM <| mkGuardBinders ec.guards
    let effVar := mkIdent `_eff
    let effPredBody ← if ec.effTags.isEmpty then `(True)
      else Qed.mkConjBody (← liftM <| ec.effTags.mapM (effTagToTerm effVar)) (ascribeProp := false)
    let effOkTerm ← `(fun ($effVar:ident : Qed.Server.ServerEffect) => $effPredBody)
    let outVar := mkIdent `_srvOut
    let mut postConjParts : Array Term := #[]
    if !ec.ensPreds.isEmpty then
      let resId := mkIdent `result
      let ensBody ← Qed.mkConjBody (← liftM <| ec.ensPreds.mapM lowerGuard) (ascribeProp := false)
      let resTy := innerOpt?.getD payloadTerm
      let pLam ← `(fun ($resId:ident : $resTy) => $ensBody)
      let pPart ← if !isFallible then
          if innerOpt?.isSome then `(∀ _r, $outVar = Option.some _r → $pLam _r) else `($pLam $outVar)
        else if innerOpt?.isSome then `(Qed.Server.srvEnsPostOpt ($pLam) $outVar)
        else `(Qed.Server.srvEnsPost ($pLam) $outVar)
      postConjParts := postConjParts.push pPart
    if !ec.errPreds.isEmpty then
      unless isFallible do throwErrorAt ec.ref s!"`ensures_error` requires a fallible (`T!`) {fnStr}"
      let errId := mkIdent `err
      let errBody ← Qed.mkConjBody (← liftM <| ec.errPreds.mapM lowerGuard) (ascribeProp := false)
      let errLam ← `(fun ($errId:ident : $errTyTerm) => let code := ($errId).code; let status := ($errId).code; let message := ($errId).message; $errBody)
      postConjParts := postConjParts.push (← `(Qed.Server.srvEnsErrPost ($errLam) $outVar))
    if let some code? := ec.fails? then
      unless isFallible do throwErrorAt ec.ref s!"`ensures_fails` requires a fallible (`T!`) {fnStr}"
      match code? with
      | none => postConjParts := postConjParts.push (← `(Qed.Server.srvEnsFails $outVar))
      | some code => postConjParts := postConjParts.push (← `(Qed.Server.srvEnsFailsCode $(Syntax.mkNumLit (toString code)) $outVar))
    let postBody : Term ← if postConjParts.isEmpty then `(True) else Qed.mkConjBody postConjParts (ascribeProp := false)
    let lblParts := (ec.effTags.map (·.toString)) ++
      (if ec.ensPreds.isEmpty then #[] else #["ensures"]) ++
      (if ec.errPreds.isEmpty then #[] else #["ensures_error"]) ++
      (match ec.fails? with | some none => #["ensures_fails"] | some (some code) => #[s!"ensures_fails {code}"] | none => #[])
    let lblLit := Syntax.mkStrLit (String.intercalate ", " lblParts.toList)
    let thmId := c.subId (thmBaseLeaf.appendAfter s!"_contract_{idx + 1}") fnIdent
    let retTy ← if isFallible then `(Except $errTyTerm $payloadTerm) else pure payloadTerm
    if isMonadic then
      let allUnfolds := unfoldIds ++ c.statefulHelperIds
      let tac ← match ec.tac? with
        | some ts => `(Lean.Parser.Tactic.tacticSeq| qedSrvPrepEffSpec $targetId [$[$allUnfolds],*]; first | done | ($ts))
        | none    => `(Lean.Parser.Tactic.tacticSeq| qedSrvProveEffSpec $targetId [$[$allUnfolds],*] $fnLit $lblLit)
      if hasState then
        emitCmd (← `(command|
          set_option linter.unusedVariables false in
          theorem $thmId $[($binderIds:ident : $binderTys:term)]* $[$guardBinders:bracketedBinder]* :
              Qed.Server.ProgEffSpec $(c.stateInvId) True (fun _ _ => True) $effOkTerm
                (fun ($outVar:ident : $retTy) => $postBody) ($callT : Qed.Server.ThreadProg $(c.stateId) _) := by $tac))
      else
        emitCmd (← `(command|
          set_option linter.unusedVariables false in
          theorem $thmId {_σ : Type} {_Inv : _σ → Prop} $[($binderIds:ident : $binderTys:term)]* $[$guardBinders:bracketedBinder]* :
              Qed.Server.ProgEffSpec _Inv True (fun _ _ => True) $effOkTerm
                (fun ($outVar:ident : $retTy) => $postBody) ($callT : Qed.Server.ThreadProg _σ _) := by $tac))
    else
      if postConjParts.isEmpty then
        -- Pure/sync functions perform zero ServerEffect operations by construction.
        emitCmd (← `(command|
          set_option linter.unusedVariables false in
          theorem $thmId $[($binderIds:ident : $binderTys:term)]* $[$guardBinders:bracketedBinder]* : True := True.intro))
      else
        let targetOut ← if isStepPair then (if hasEmit then `(($callT).2.1) else `(($callT).2)) else pure callT
        let stepUnfolds := #[targetId] ++ unfoldIds ++ (if hasState then #[c.stateInvId] else #[])
        let tac ← liftM <| mkStepEnsProofTac stepUnfolds fnLit (String.intercalate ", " lblParts.toList) ec.tac?
        if isStepPair then
          let s0Id := mkIdent `_s0
          emitCmd (← `(command|
            set_option linter.unusedVariables false in
            theorem $thmId ($s0Id:ident : $(c.stateId)) $[($binderIds:ident : $binderTys:term)]* (_hInv : $(c.stateInvId) $s0Id) $[$guardBinders:bracketedBinder]* :
                let $outVar:ident : $retTy := $targetOut; $postBody := by $tac))
        else
          emitCmd (← `(command|
            set_option linter.unusedVariables false in
            theorem $thmId $[($binderIds:ident : $binderTys:term)]* $[$guardBinders:bracketedBinder]* :
                let $outVar:ident : $retTy := $targetOut; $postBody := by $tac))
  let paramNames := paramIds.map (·.getId.eraseMacroScopes)
  for (bl, idx) in contracts.blinds.zipIdx do
    let thmId := c.subId (thmBaseLeaf.appendAfter s!"_blindTo_{idx + 1}") fnIdent
    let guardBinders ← liftM <| mkGuardBinders bl.guards
    let mut paramBlinds : Array (Name × Bool × Array Ident) := #[]
    for rawT in bl.targets do
      let rawId : Ident := ⟨rawT.getArg 0⟩; let optB := rawT.getArg 1
      let (pId, flds) ← if optB.getNumArgs == 3 then pure (rawId, (optB.getArg 1).getSepArgs.map (⟨·⟩))
        else match rawId.getId.eraseMacroScopes with
          | .str .anonymous _ => pure (rawId, #[])
          | .str (.str .anonymous p) f => pure (mkIdentFrom rawId (Name.mkSimple p), #[mkIdentFrom rawId (Name.mkSimple f)])
          | _ => throwErrorAt rawId s!"`blindTo` expects `<param>`, `<param>.<field>`, or `<param>.\{f1, f2}`"
      let pn := pId.getId.eraseMacroScopes
      unless paramNames.contains pn do
        throwErrorAt pId s!"unknown parameter `{pn}` in `blindTo` of `{fnStr}`"
      if let some pos := paramBlinds.findIdx? (·.1 == pn) then
        let (_, w, fs) := paramBlinds[pos]!; let w' := w || flds.isEmpty
        let fs' := if w' then #[] else flds.foldl (fun a f => if a.any (·.getId.eraseMacroScopes == f.getId.eraseMacroScopes) then a else a.push f) fs
        paramBlinds := paramBlinds.set! pos (pn, w', fs')
      else paramBlinds := paramBlinds.push (pn, flds.isEmpty, flds)
    let mut freshVars : Array (Ident × Option Term) := #[]
    let mut lhsArgs : Array Term := #[]
    let mut rhsArgs : Array Term := #[]
    for (bId, bTy) in binderIds.zip binderTys do
      let bn := bId.getId.eraseMacroScopes
      rhsArgs := rhsArgs.push ⟨bId.raw⟩
      match paramBlinds.find? (·.1 == bn) with
      | none => lhsArgs := lhsArgs.push ⟨bId.raw⟩
      | some (_, true, _) =>
          let fv := mkIdent (Name.mkSimple s!"_qed_blind_{bn}")
          freshVars := freshVars.push (fv, some bTy); lhsArgs := lhsArgs.push ⟨fv.raw⟩
      | some (_, false, flds) =>
          let mut updIds : Array Ident := #[]; let mut updVals : Array Term := #[]
          for f in flds do
            let fv := mkIdent (Name.mkSimple s!"_qed_blind_{bn}_{f.getId.eraseMacroScopes}")
            freshVars := freshVars.push (fv, none); updIds := updIds.push f; updVals := updVals.push ⟨fv.raw⟩
          lhsArgs := lhsArgs.push (← `({ $bId with $[$updIds:ident := $updVals:term],* }))
    let (lhsCall, rhsCall) ← if isMonadic && !hasState then
        let l ← mkAppTerms targetId lhsArgs; let r ← mkAppTerms targetId rhsArgs
        pure (← `(($l : Qed.Server.ThreadProg _σ _)), ← `(($r : Qed.Server.ThreadProg _σ _)))
      else if isStepPair then
        let s0Id := mkIdent `_s0
        pure (← `($targetId $s0Id $lhsArgs*), ← `($targetId $s0Id $rhsArgs*))
      else
        pure (← mkAppTerms targetId lhsArgs, ← mkAppTerms targetId rhsArgs)
    let eqProp ← freshVars.foldrM (init := ← `($lhsCall = $rhsCall)) fun (fv, ty?) acc => match ty? with
      | some ty => `(∀ ($fv:ident : $ty), $acc) | none => `(∀ $fv:ident, $acc)
    let proofTac : TSyntax ``Lean.Parser.Tactic.tacticSeq ← match bl.tac? with
      | some ts => pure ts
      | none => `(Lean.Parser.Tactic.tacticSeq| qedProveBlindTo $targetId $thmId $(Syntax.mkStrLit fnStr))
    if isMonadic && !hasState then
      emitCmd (← `(command|
        set_option linter.unusedVariables false in
        theorem $thmId {_σ : Type} $[($binderIds:ident : $binderTys:term)]* $[$guardBinders:bracketedBinder]* : $eqProp := by $proofTac))
    else if isStepPair then
      let s0Id := mkIdent `_s0
      emitCmd (← `(command|
        set_option linter.unusedVariables false in
        theorem $thmId ($s0Id:ident : $(c.stateId)) $[($binderIds:ident : $binderTys:term)]* $[$guardBinders:bracketedBinder]* : $eqProp := by $proofTac))
    else
      emitCmd (← `(command|
        set_option linter.unusedVariables false in
        theorem $thmId $[($binderIds:ident : $binderTys:term)]* $[$guardBinders:bracketedBinder]* : $eqProp := by $proofTac))

private def mkFnEnsSpec? (ensRes? : Option (Ident × Name × String)) (pTerms : Array Term) (isOpt : Bool)
    (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none) : Option FnEnsSpec :=
  ensRes?.map fun (ensId, _, labelStr) =>
    { ensId, labelStr, tac?, postFn := fun outT => do
        let ensApp ← mkAppTerms ensId pTerms
        if isOpt then `(Qed.Server.srvEnsPostOpt ($ensApp) $outT) else `(Qed.Server.srvEnsPost ($ensApp) $outT) }

private def checkReadOnlyDecl (ref : Ident) (kindLabel fnStr : String) (declaredReadOnly : Bool)
    (mutatesState dbWrite hasEmit hasCookieOp : Bool) : SrvElabM Unit := do
  if !declaredReadOnly then return
  let mut reasons : Array String := #[]
  if mutatesState then reasons := reasons.push "mutates server state"
  if dbWrite then reasons := reasons.push "performs a database write"
  if hasEmit then reasons := reasons.push "emits on a WebSocket channel"
  if hasCookieOp then reasons := reasons.push "sets or clears cookies"
  unless reasons.isEmpty do
    throwErrorAt ref s!"`read_only {kindLabel} {fnStr}` is not read-only: it {String.intercalate ", " reasons.toList}"

/-! ## Background `every` Job Elaborator -/

@[noinline]
private def elabOneServerJob (existingMethods : Array ServerMethodInfo) (seenJobs : Array String)
    (errTyTerm emptyCtx : Term) (callArgs : Array Term) (jc : Syntax) : SrvElabM (Option (String × Term × Option Term)) := do
  let c ← read; let jobIdent : Ident := ⟨jc.getArg 3⟩; let jobStr := jobIdent.getId.toString
  if existingMethods.any (·.name == jobStr) || seenJobs.contains jobStr then throwErrorAt jobIdent s!"duplicate job or method name `{jobStr}` in `server {c.srvName}`"
  let n := (⟨jc.getArg 1⟩ : TSyntax `num).getNat; let unitStr := (jc.getArg 2).getId.eraseMacroScopes.toString
  let unit ← match unitStr with
    | "ms" => pure DurationUnit.ms | "s" => pure DurationUnit.s | "m" => pure DurationUnit.m | "h" => pure DurationUnit.h
    | _ => throwErrorAt (jc.getArg 2) s!"unknown duration unit `{unitStr}` in `every {n}{unitStr} {jobStr}`; supported units are `ms`, `s`, `m`, `h`"
  let intervalMs := durationToMs n unit
  if intervalMs == 0 then throwErrorAt (jc.getArg 1) s!"background job `{jobStr}` interval must be positive (got `{n}{unitStr}`)"
  let optRet := jc.getArg 4
  let returnsBool ← if optRet.getNumArgs == 2 then do
      let retTy ← liftMacroM <| lowerSrvType (optRet.getArg 1) true s!"return type of job `{jobStr}`"
      unless (retTy.mods.filter (· != .fallible)).isEmpty && (retTy.baseName == `Bool || retTy.baseName == `Unit) do
        throwErrorAt (optRet.getArg 1) s!"`every` job `{jobStr}` return type must be `Bool` (or omitted for `Unit`)"
      pure (retTy.baseName == `Bool)
    else pure false
  let contracts ← liftM <| parseSrvContracts s!"job `{jobStr}`" (jc.getArg 6).getArgs
  unless contracts.requires.isEmpty do throwErrorAt jobIdent s!"`requires` is not supported on background job `{jobStr}`"
  unless contracts.blinds.isEmpty do throwErrorAt jobIdent s!"`blindTo` is not supported on background job `{jobStr}`"
  let rawBodyStmts := suiteStmts (jc.getArg 7)
  let payloadTerm ← if returnsBool then `(Bool) else `(Unit)
  let bodyStmts ← if returnsBool then do
      unless blockAlwaysReturns rawBodyStmts do throwErrorAt jobIdent s!"missing `return` on fallthrough path of `-> Bool` job `{jobStr}`"
      pure rawBodyStmts
    else pure (ensureUnitReturn jobIdent rawBodyStmts)
  let ensRes? ← if contracts.topEnsures.isEmpty then pure none else do
    let some r ← elabEnsuresAbbrev jobIdent s!"job `{jobStr}`" `result #[] #[] #[] payloadTerm contracts.topEnsures | return none
    pure r
  let ensSpec? := mkFnEnsSpec? ensRes? #[] false contracts.topEnsTac?
  let isAsyncJob := c.hasState && (blockHasAwait bodyStmts || blockHasAtomic bodyStmts)
  let some hRes ← elabServerHandler isAsyncJob jobStr jobIdent #[] #[] #[] payloadTerm errTyTerm
      (← mkBaseLowerCtx jobStr #[] isAsyncJob true true) bodyStmts ensSpec? (ctxArg? := some emptyCtx) | return none
  let innerCall ← if hRes.isAsync then mkAppTerms hRes.targetId (hRes.allBinderIds.map (⟨·.raw⟩))
    else mkAppTerms (← `($(hRes.targetId) _s0)) (hRes.allBinderIds.map (⟨·.raw⟩))
  elabSrvExtraContracts jobIdent hRes.targetId jobIdent.getId jobStr hRes.isAsync true c.hasState #[]
    hRes.allBinderIds hRes.allBinderTys innerCall payloadTerm errTyTerm none contracts (isStepPair := !hRes.isAsync) (hasEmit := hRes.hasEmit)
  let (runExpr, isRO, hasEmit) := (hRes.runExpr, !hRes.mutatesState, hRes.hasEmit)
  let proofExpr? : Option Term ← if !c.hasState then pure none else do
    let invThmId := c.fnSubId jobIdent "_inv"
    if isAsyncJob then some <$> mkAppTerms invThmId callArgs
    else
      let emitCont ← `(fun _ => Qed.Server.ProgSpec.safeIO_bind _ fun _ => Qed.Server.ProgSpec.pure_class _ trivial)
      if isRO then some <$> if hasEmit then `(Qed.Server.ProgSpec.runAtomicRead_bind_val _ $emitCont fun _ _h => _h) else `(Qed.Server.ProgSpec.runAtomicRead _ (fun _ _h => _h) fun _ _ => trivial)
      else let invApp ← mkAppTerms (← `($invThmId _s)) callArgs
           some <$> if hasEmit then `(Qed.Server.ProgSpec.runAtomic_bind_val _ $emitCont fun _s _h => $invApp _h) else `(Qed.Server.ProgSpec.runAtomic _ (fun _s _h => $invApp _h) fun _ _ => trivial)
  let (unitRunExpr, unitProofExpr?) ← if returnsBool then do
      let uRun ← `(($runExpr) >>= fun _jr => Pure.pure (_jr.map fun _ => ()))
      let uPf? ← proofExpr?.mapM fun pf => `(Qed.Server.ProgSpec.bind $pf fun _ _ => Qed.Server.ProgSpec.pure_class _ trivial)
      pure (uRun, uPf?)
    else pure (runExpr, proofExpr?)
  let (wrappedRun, wrappedPf?) ← liftM <| wrapWithEnvDecls c.envDecls unitRunExpr unitProofExpr?
  let wrappedWorkRun? ← if returnsBool then some <$> (return (← liftM <| wrapWithEnvDecls c.envDecls runExpr none).1) else pure none
  let (nameLit, msLit, posPf) := (Syntax.mkStrLit jobStr, Syntax.mkNumLit (toString intervalMs), ← `(by decide))
  if c.hasState then
    let runMTerm ← `(fun {m} [Monad m] [Qed.Server.MonadServer m] [Qed.Server.MonadAtomic $(c.stateId) m] => $wrappedRun)
    let workOptTerm ← match wrappedWorkRun? with
      | some wRun => `(Option.some (fun {m} [Monad m] [Qed.Server.MonadServer m] [Qed.Server.MonadAtomic $(c.stateId) m] => $wRun))
      | none => `(Option.none)
    let jobTerm ← `({ name := $nameLit, intervalMs := $msLit, intervalPos := $posPf, runM := $runMTerm, runWorkM? := $workOptTerm : Qed.Server.ServerJob $(c.stateId) })
    return some (jobStr, jobTerm, ← wrappedPf?.mapM fun pf => `(Qed.Server.VerifiedJob.mk (σ := $(c.stateId)) (Inv := $(c.stateInvId)) $jobTerm $pf))
  else
    let workOptTerm ← match wrappedWorkRun? with
      | some wRun => `(Option.some (fun {m} [Monad m] [Qed.Server.MonadServer m] => $wRun))
      | none => `(Option.none)
    return some (jobStr, ← `({ name := $nameLit, intervalMs := $msLit, intervalPos := $posPf, runM := fun {m} [Monad m] [Qed.Server.MonadServer m] => $wrappedRun, runWorkM? := $workOptTerm : Qed.Server.StatelessJob }), none)

@[noinline]
private def elabServerJobs (existingMethods : Array ServerMethodInfo) (jobClauses : Array Syntax) : SrvElabM (Option (Array String)) := do
  if jobClauses.isEmpty then return some #[]
  let c ← read; let mut jobNames : Array String := #[]; let mut runtimeJobTerms : Array Term := #[]; let mut verifiedJobTerms : Array Term := #[]
  let (errTyTerm, emptyCtx) := (← `(Qed.Server.ApiError), ← `(({} : Qed.Server.RequestCtx)))
  let callArgs : Array Term := c.envIdents.map (⟨·.raw⟩) ++ #[emptyCtx]
  for jc in jobClauses do
    let some (nm, jt, vjt?) ← elabOneServerJob existingMethods jobNames errTyTerm emptyCtx callArgs jc | return none
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

private def parseSrvFnMods (modsNode : Syntax) : CommandElabM (Bool × Bool) := do
  let mut isRO := false; let mut isSys := false
  for m in modsNode.getArgs do
    let nm := (m.getArg 0).getId.eraseMacroScopes
    if nm == `read_only then
      if isRO then throwErrorAt m "duplicate `read_only` modifier on `fn`"
      isRO := true
    else if nm == `system then
      if isSys then throwErrorAt m "duplicate `system` modifier on `fn`"
      isSys := true
    else throwErrorAt m s!"unexpected `fn` modifier `{nm}`"
  return (isRO, isSys)

@[noinline]
private def elabServerHelperClause (hc : Syntax) : SrvElabM (Option (SrvHelperSig × Array Ident)) := do
  let c ← read; let (declaredReadOnly, isSystem) ← liftM <| parseSrvFnMods (hc.getArg 0)
  let fnIdent : Ident := ⟨hc.getArg 2⟩; let fnStr := fnIdent.getId.toString
  if c.helpers.any (·.name == fnStr) then throwErrorAt fnIdent s!"duplicate helper `fn {fnStr}` in `server {c.srvName}`"
  let contracts ← liftM <| parseSrvContracts "server `fn`" (hc.getArg 8).getArgs
  let (reqExprs, ensExprs, ensTac?) := (contracts.requires, contracts.topEnsures, contracts.topEnsTac?)
  let pp ← parseSrvFnParams s!"server helper `fn {fnStr}`" "parameter" (hc.getArg 4).getSepArgs (reserved := if ensExprs.isEmpty then #[] else #["result"])
  let (pIdents, pTyTerms, pDefBinders, paramNames, minParamCount) := (pp.idents, pp.tyTerms, pp.defBinders, pp.names, pp.minParamCount)
  let sysCtxTerm? : Option Term ← if isSystem then some <$> `({ $(c.ctxId) with isSystem := true }) else pure none
  let wrapSysCtx (body : Term) : CommandElabM Term := match sysCtxTerm? with
    | some sc => `(let $(c.ctxId):ident : Qed.Server.RequestCtx := $sc; $body)
    | none => pure body
  let hasExplicitRet := (hc.getArg 6).getNumArgs == 2
  let (payloadTerm, innerOpt?, isFallible, isUnitPayload) ←
    if hasExplicitRet then
      let rt ← liftMacroM <| lowerSrvType ((hc.getArg 6).getArg 1) true s!"return type of helper `fn {fnStr}`"
      pure (rt.term, rt.innerOpt?, rt.isFallible, (rt.mods.filter (· != .fallible)).isEmpty && rt.baseName == `Unit)
    else pure (← `(Unit), none, true, true)
  let bodyStmts := if isUnitPayload then ensureUnitReturn fnIdent (suiteStmts (hc.getArg 9)) else suiteStmts (hc.getArg 9)
  if !isUnitPayload && !blockAlwaysReturns bodyStmts then throwErrorAt fnIdent s!"missing `return` on fallthrough path of helper `fn {fnStr}`"
  let (domainTagIdents, hasPlainFail) ← liftM <| scanBodyFailTags bodyStmts
  if !domainTagIdents.isEmpty then throwErrorAt fnIdent s!"typed `fail(.tag)` is only supported in `rpc` endpoints; use `fail(code, msg)` or `fail(msg)` in private helper `fn {fnStr}`"
  if hasPlainFail && !isFallible then throwErrorAt fnIdent s!"`fail(...)` can only be returned from a fallible `T!` helper (`fn {fnStr}` is not declared `-> ...!`)"
  let errTyTerm ← `(Qed.Server.ApiError); let defLeaf := Name.mkSimple s!"_fn_{fnStr}"; let defId := c.subId defLeaf fnIdent
  let envTys ← liftM c.envBinderTys; let ctxTy ← `(Qed.Server.RequestCtx)
  let baseBinderIds := c.envIdents ++ #[c.ctxId] ++ pIdents
  let baseBinderTys := envTys ++ #[ctxTy] ++ pTyTerms
  let preDefBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ←
    (c.envIdents.zip envTys |>.push (c.ctxId, ctxTy)).mapM fun (i, t) => `(bracketedBinder| ($i:ident : $t:term))
  let allDefBinders := preDefBinders ++ pDefBinders
  let reqs ← elabRequiresClauses fnIdent defLeaf fnStr "_hFnReq" "_req" paramNames paramNames pIdents pTyTerms reqExprs (trackAuth := false)
  let some ensRes? ← elabEnsuresAbbrev (mkIdentFrom fnIdent defLeaf) fnStr `result paramNames pIdents pTyTerms (innerOpt?.getD payloadTerm) ensExprs | return none
  let pTerms : Array Term := pIdents.map (⟨·.raw⟩)
  let ensSpec? := mkFnEnsSpec? ensRes? pTerms innerOpt?.isSome ensTac?
  let hasAwait := blockHasAwait bodyStmts; let hasEmit := blockHasEmit bodyStmts
  let touchesState := c.hasState && (blockHasAtomic bodyStmts ||
    c.stateFieldNames.any (fun sf => bodyStmts.any (stxMentionsVar sf)) ||
    c.helpers.any (fun h => h.takesAtomic && bodyStmts.any (stxMentionsVar h.name)))
  let callsMonadicHelper := c.helpers.any fun h => h.isMonadic && bodyStmts.any (stxMentionsVar h.name)
  let isMonadic := hasAwait || hasEmit || touchesState || callsMonadicHelper
  let bodyHasUnwrap := bodyStmts.any (stxAny exprHasUnwrap)
  let bodyHasCatch := bodyStmts.any (stxAny fun s => s.getKind == ``qedStmtLet && (s.getArg 5).getNumArgs > 0)
  let isPureSync := !isMonadic && !isFallible && reqExprs.isEmpty && !bodyHasUnwrap && !bodyHasCatch && !hasPlainFail && hasExplicitRet
  let fnLit := Syntax.mkStrLit fnStr
  if isPureSync then
    let lCtx : LowerCtx := {
      fnName := fnStr, envVars := c.envVarNames, envIdents := c.envIdents, locals := paramNames,
      stateRule := .statelessServer, helpers := c.helpers, dbs := #[],
      services := c.serviceDecls.map fun (a, i) => (a.getId.toString, i),
      ctxTerm? := sysCtxTerm? }
    let bodyTerm ← liftM <| Qed.lowerPureFnStmts s!"fn {fnStr}" bodyStmts.toList
      (fun s => do let (t, st) ← (lowerExpr lCtx .val s).run {}; (recordSrvExtRoots st.extRoots).run c; pure t)
      (fun s => do let (t, st) ← (lowerExpr lCtx .propGuard s).run {}; (recordSrvExtRoots st.extRoots).run c; pure t)
    let fullBody ← liftM <| wrapSysCtx (← `(srvAutoField($bodyTerm)))
    elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      @[noinline] def $defId $[$allDefBinders:bracketedBinder]* : $payloadTerm := $fullBody))
    if (← hasSrvErrors) then return none
    if let some (ensId, _, labelStr) := ensRes? then
      let callT ← mkAppTerms defId (baseBinderIds.map (⟨·.raw⟩))
      let ensApp ← mkAppTerms ensId pTerms
      let goal ← if innerOpt?.isSome then `(∀ _r, $callT = some _r → $ensApp _r) else `($ensApp ($callT))
      let ensTac ← liftM <| mkStepEnsProofTac #[defId, ensId] fnLit labelStr ensTac?
      deferSrvCmd (← `(command| theorem $(c.subId (defLeaf.appendAfter "_ensures") fnIdent) $[($baseBinderIds:ident : $baseBinderTys:term)]* :
          $goal := by $ensTac))
    let callT ← mkAppTerms defId (baseBinderIds.map (⟨·.raw⟩))
    elabSrvExtraContracts fnIdent defId defLeaf fnStr false false false pIdents baseBinderIds baseBinderTys callT payloadTerm errTyTerm innerOpt? contracts
    return some ({ name := fnStr, defId, minParamCount, paramCount := pIdents.size, isMonadic := false, isFallible := false, takesAtomic := false, mutatesState := false, dbWrite := false }, #[])
  else if !isMonadic then
    let sUnitId := mkIdent `_sUnit
    let lCtx : LowerCtx := {
      fnName := fnStr, envVars := c.envVarNames, envIdents := c.envIdents, locals := paramNames ++ reqs.extraLocals,
      stateRule := .statelessServer, allowAwait := false, allowUnwrap := isFallible || innerOpt?.isSome,
      hasFallible := isFallible, innerOptTy? := innerOpt?, helpers := c.helpers, dbs := #[],
      services := c.serviceDecls.map fun (a, i) => (a.getId.toString, i),
      ctxTerm? := sysCtxTerm? }
    let (pureBody, lSt) ← liftM <| (lowerPureBlock lCtx false sUnitId sUnitId bodyStmts).run {}
    recordSrvExtRoots lSt.extRoots
    let inner ← liftM <| wrapSysCtx (← `(let $sUnitId:ident : Unit := (); (Qed.Server.srvFinish $sUnitId $pureBody).2))
    let wrapped ← liftM <| wrapAuthAndReqs reqs inner (pureWrap := false)
    elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      @[noinline] def $defId $[$allDefBinders:bracketedBinder]* : Except $errTyTerm $payloadTerm := $wrapped))
    if (← hasSrvErrors) then return none
    if let some ens := ensSpec? then
      let callT ← mkAppTerms defId (baseBinderIds.map (⟨·.raw⟩))
      let postGoal ← liftM <| ens.postFn callT
      let ensTac ← liftM <| mkStepEnsProofTac #[defId, ens.ensId] fnLit ens.labelStr ens.tac?
      deferSrvCmd (← `(command| theorem $(c.subId (defLeaf.appendAfter "_ensures") fnIdent) $[($baseBinderIds:ident : $baseBinderTys:term)]* :
          $postGoal := by $ensTac))
    let callT ← mkAppTerms defId (baseBinderIds.map (⟨·.raw⟩))
    elabSrvExtraContracts fnIdent defId defLeaf fnStr false true false pIdents baseBinderIds baseBinderTys callT payloadTerm errTyTerm innerOpt? contracts
    return some ({ name := fnStr, defId, minParamCount, paramCount := pIdents.size, isMonadic := false, takesAtomic := false, mutatesState := false, dbWrite := lSt.dbWrite }, #[])
  else if touchesState then
    let isAsync := hasAwait || blockHasAtomic bodyStmts || callsMonadicHelper
    let fnInnerIdent := mkIdentFrom fnIdent defLeaf
    let some hRes ← elabServerHandler isAsync fnStr fnInnerIdent (pIdents ++ reqs.allBinderIds) (pTyTerms ++ reqs.allBinderTys)
        (pTerms ++ reqs.allBinderArgs) payloadTerm errTyTerm
        (← mkBaseLowerCtx fnStr (paramNames ++ reqs.extraLocals) isAsync (isFallible || innerOpt?.isSome) isFallible innerOpt? (ctxTerm? := sysCtxTerm?) (txParams := pp.txParams)) bodyStmts ensSpec? (ctxArg? := sysCtxTerm?) | return none
    checkReadOnlyDecl fnIdent "fn" fnStr declaredReadOnly hRes.mutatesState hRes.dbWrite hRes.hasEmit hRes.hasCookieOp
    let guarded ← liftM <| wrapAuthAndReqs reqs (← liftM <| wrapSysCtx hRes.runExpr)
    let atomicBinders ← liftM c.atomicBinders
    elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      @[noinline] def $defId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m] $[$atomicBinders:bracketedBinder]* $[$allDefBinders:bracketedBinder]* :
          m (Except $errTyTerm $payloadTerm) := $guarded))
    if (← hasSrvErrors) then return none
    let innerId := c.fnSubId fnInnerIdent (if isAsync then "_handler" else "_step")
    let innerCall ← if hRes.isAsync then mkAppTerms hRes.targetId (hRes.allBinderIds.map (⟨·.raw⟩))
      else mkAppTerms (← `($(hRes.targetId) $(mkIdent `_s0))) (hRes.allBinderIds.map (⟨·.raw⟩))
    elabSrvExtraContracts fnIdent hRes.targetId defLeaf fnStr hRes.isAsync true c.hasState pIdents hRes.allBinderIds hRes.allBinderTys innerCall payloadTerm errTyTerm innerOpt? contracts (isStepPair := !hRes.isAsync) (hasEmit := hRes.hasEmit)
    return some ({ name := fnStr, defId, minParamCount, paramCount := pIdents.size, isMonadic := true, takesAtomic := true, mutatesState := hRes.mutatesState, dbWrite := hRes.dbWrite, hasCookieOp := hRes.hasCookieOp }, #[defId, innerId])
  else
    let baseCtx ← mkBaseLowerCtx fnStr (paramNames ++ reqs.extraLocals) true (isFallible || innerOpt?.isSome) isFallible innerOpt? (ctxTerm? := sysCtxTerm?) (txParams := pp.txParams)
    let (asyncBody, lSt) ← liftM <| (lowerAsyncBlock { baseCtx with stateFields := #[] } none bodyStmts).run {}
    recordSrvExtRoots lSt.extRoots
    checkReadOnlyDecl fnIdent "fn" fnStr declaredReadOnly false lSt.dbWrite hasEmit lSt.hasCookieOp
    let guarded ← liftM <| wrapAuthAndReqs reqs (← liftM <| wrapSysCtx (← `(Qed.Server.srvFinishM $asyncBody)))
    let mId := mkIdent `m
    elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      @[noinline] def $defId {$mId:ident : Type → Type} [Monad $mId] [Qed.Server.MonadServer $mId] $[$allDefBinders:bracketedBinder]* :
          $mId (Except $errTyTerm $payloadTerm) := $guarded))
    if (← hasSrvErrors) then return none
    let baseArgTerms : Array Term := baseBinderIds.map (⟨·.raw⟩)
    let callT ← `($defId ($mId := Qed.Server.ThreadProg _σ) $baseArgTerms*)
    let noAtomId := c.subId (defLeaf.appendAfter "_noAtomic") fnIdent
    let noAtomApp ← mkAppTerms noAtomId (baseBinderIds.map (⟨·.raw⟩))
    elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      theorem $noAtomId {_σ : Type} $[($baseBinderIds:ident : $baseBinderTys:term)]* :
          Qed.Server.NoAtomic $callT := by qedSrvProveSafeIO $defId))
    elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      instance {_σ : Type} $[($baseBinderIds:ident : $baseBinderTys:term)]* :
          Qed.Server.SafeIO $callT := ⟨$noAtomApp⟩))
    if let some ens := ensSpec? then
      let outVar := mkIdent `_srvOut; let postBody ← liftM <| ens.postFn ⟨outVar.raw⟩
      let ensThmId := c.subId (defLeaf.appendAfter "_ensures") fnIdent
      let ensThmApp ← mkAppTerms ensThmId (baseBinderIds.map (⟨·.raw⟩))
      let ensTac ← liftM <| mkAsyncEnsProofTac defId #[ens.ensId] fnLit ens.labelStr ens.tac?
      elabSrvCmd (← `(command|
        set_option linter.unusedVariables false in
        theorem $ensThmId {_σ : Type} {_Inv : _σ → Prop} $[($baseBinderIds:ident : $baseBinderTys:term)]* :
            Qed.Server.ProgEnsures _Inv (fun ($outVar:ident : Except $errTyTerm $payloadTerm) => $postBody) $callT := by $ensTac))
      elabSrvCmd (← `(command|
        set_option linter.unusedVariables false in
        instance {_σ : Type} $[($baseBinderIds:ident : $baseBinderTys:term)]* :
            Qed.Server.SafeIOEnsures $callT (fun ($outVar:ident : Except $errTyTerm $payloadTerm) => $postBody) :=
          ⟨$noAtomApp, fun {_Inv} => $ensThmApp⟩))
    elabSrvExtraContracts fnIdent defId defLeaf fnStr true true false pIdents baseBinderIds baseBinderTys callT payloadTerm errTyTerm innerOpt? contracts (defer := false)
    if (← hasSrvErrors) then return none
    return some ({ name := fnStr, defId, minParamCount, paramCount := pIdents.size, isMonadic := true, takesAtomic := false, mutatesState := false, dbWrite := lSt.dbWrite, hasCookieOp := lSt.hasCookieOp }, #[])

@[noinline]
private def elabServerBeforeClause (bc : Syntax) : SrvElabM (Option Term) := do
  let c ← read; let beforeIdent := mkIdentFrom bc `_before
  let bodyStmts := ensureUnitReturn beforeIdent (suiteStmts (bc.getArg 2))
  let hasAwait := blockHasAwait bodyStmts; let isAsync := if c.hasState then hasAwait || blockHasAtomic bodyStmts else true
  let some hRes ← elabServerHandler isAsync "before" beforeIdent #[] #[] #[] (← `(Unit)) (← `(Qed.Server.ApiError))
      (← mkBaseLowerCtx "before" #[] (if c.hasState then isAsync else hasAwait) true true) bodyStmts none | return none
  return some hRes.runExpr

@[noinline]
private def elabServerFnClause (existingMethods : Array ServerMethodInfo) (fc : Syntax) (beforeRun? : Option Term := none) :
    SrvElabM (Option (ServerMethodInfo × (Term × Term) × TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let c ← read; let declaredReadOnly := (fc.getArg 0).getNumArgs == 1
  let fnIdent : Ident := ⟨fc.getArg 2⟩; let fnStr := fnIdent.getId.toString
  if existingMethods.any (·.name == fnStr) || c.helpers.any (·.name == fnStr) then throwErrorAt fnIdent s!"duplicate function `{fnStr}` in `server {c.srvName}`"
  let contracts ← liftM <| parseSrvContracts "`rpc`" (fc.getArg 9).getArgs
  let (reqExprs, ensExprs, ensTac?) := (contracts.requires, contracts.topEnsures, contracts.topEnsTac?)
  let (pIdents, pTyTerms, paramNames) ← parseSrvParams s!"server RPC `{fnStr}`" "parameter" (fc.getArg 4).getSepArgs (reserved := if ensExprs.isEmpty then #[] else #["result"])
  let retTy ← liftMacroM <| lowerSrvType (fc.getArg 7) true s!"return type of `{fnStr}`"
  let (payloadTerm, innerOpt?) := (retTy.term, retTy.innerOpt?)
  let isUnitPayload := (retTy.mods.filter (· != .fallible)).isEmpty && retTy.baseName == `Unit
  let bodyStmts := if isUnitPayload then ensureUnitReturn fnIdent (suiteStmts (fc.getArg 10)) else suiteStmts (fc.getArg 10)
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
  let ensSpec? := mkFnEnsSpec? ensRes? pTerms innerOpt?.isSome ensTac?
  let hasAwait := blockHasAwait bodyStmts; let reqTupleTy ← liftMacroM <| buildProdType pTyTerms; let reqVar := mkIdent `_reqVal
  let projs ← extractTupleProjections reqVar pTyTerms.size
  let some hRes ← elabServerHandler hasAwait fnStr fnIdent (pIdents ++ reqs.allBinderIds) (pTyTerms ++ reqs.allBinderTys)
      (projs ++ reqs.allBinderArgs) payloadTerm errTyTerm
      (← mkBaseLowerCtx fnStr (paramNames ++ reqs.extraLocals) hasAwait (retTy.isFallible || innerOpt?.isSome) retTy.isFallible innerOpt? domainErrTyTerm?) bodyStmts ensSpec? | return none
  checkReadOnlyDecl fnIdent "rpc" fnStr declaredReadOnly hRes.mutatesState hRes.dbWrite hRes.hasEmit hRes.hasCookieOp
  let extraCall ← if hRes.isAsync then mkAppTerms hRes.targetId (hRes.allBinderIds.map (⟨·.raw⟩))
    else mkAppTerms (← `($(hRes.targetId) $(mkIdent `_s0))) (hRes.allBinderIds.map (⟨·.raw⟩))
  elabSrvExtraContracts fnIdent hRes.targetId fnIdent.getId fnStr hRes.isAsync true c.hasState pIdents hRes.allBinderIds hRes.allBinderTys extraCall payloadTerm errTyTerm innerOpt? contracts (isStepPair := !hRes.isAsync) (hasEmit := hRes.hasEmit)
  let (runExpr, isReadOnly) := (hRes.runExpr, hRes.isReadOnly)
  let resExpr ← if domainErrTyTerm?.isSome then `(Qed.Server.SrvFailure.toWire _fnRes) else `(_fnRes)
  let arm : TSyntax ``Lean.Parser.Term.matchAltExpr ← liftM <| do
    let dec ← mkProtoDecodeBind (mkIdent `reqBytes) reqVar reqTupleTy pIdents projs (← wrapAuthAndReqs reqs (← `($runExpr >>= fun _fnRes => Pure.pure (($resExpr).map Qed.Proto.encode))))
    let guardedDec ← wrapWithBefore? beforeRun? dec
    `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkStrLit fnStr) => $guardedDec)
  let paramTypeConsts ← elabFnClientStubs fnIdent fnStr pIdents pTyTerms reqTupleTy payloadTerm innerOpt? errTypeId? ensSpec? reqs
  let wireRespTy ← match errTypeId? with | some e => `(Except (Qed.RpcDomainError $e) $payloadTerm) | none => pure payloadTerm
  return some ({
    name := fnStr, paramNames := pIdents.map (·.getId), paramCount := pIdents.size, isReadOnly, isAsync := hasAwait || beforeRun?.isSome,
    isFallible := retTy.isFallible, isOption := innerOpt?.isSome, hasClientReq := reqs.clientReqId?.isSome, requiresAuth := reqs.requiresAuth,
    clientReqConst := reqs.clientReqConst?, clientReqLabel := reqs.clientReqLabel, hasEnsures := ensSpec?.isSome, ensPredConst := ensRes?.map (·.2.1),
    domainErrTags := domainTagIdents.map (·.getId.toString), rawRpcConst := c.fullSrvName ++ Name.mkSimple s!"_rpc_{fnStr}",
    outcomeConst := c.fullSrvName ++ fnIdent.getId.appendAfter "_Outcome", paramTypeConsts }, (reqTupleTy, wireRespTy), arm)

@[noinline]
private def elabServerHttpRouteClause (routeIdx : Nat) (existingRoutes : Array (String × String × Bool)) (hc : Syntax) (beforeRun? : Option Term := none) :
    SrvElabM (Option ((String × String × Bool) × TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let c ← read; let isStream := hc.getKind == ``srvStreamClause
  let methodStr := if isStream then "GET" else (hc.getArg 0).getId.toString.toUpper
  let pathStx := hc.getArg 1; let pathStr := (⟨pathStx⟩ : TSyntax `str).getString
  if !pathStr.startsWith "/" then throwErrorAt pathStx s!"custom HTTP route path `{pathStr}` must start with `/`"
  if pathStr.startsWith "/_qed/" then throwErrorAt pathStx s!"custom HTTP route path `{pathStr}` cannot use reserved `/_qed/` prefix"
  if existingRoutes.any fun (m, p, _) => m == methodStr && p == pathStr then throwErrorAt pathStx s!"duplicate custom HTTP route `{methodStr} {pathStr}` in `server {c.srvName}`"
  let routeLeaf := Name.mkSimple s!"_http_{routeIdx}"; let routeIdent := mkIdentFrom pathStx routeLeaf
  let routeLabel := if isStream then s!"stream {pathStr}" else s!"{methodStr} {pathStr}"
  let contracts ← liftM <| parseSrvContracts s!"HTTP route `{routeLabel}`" (hc.getArg 3).getArgs
  let (reqExprs, ensExprs, ensTac?) := (contracts.requires, contracts.topEnsures, contracts.topEnsTac?)
  let bodyStmts := if isStream then ensureUnitReturn routeIdent (suiteStmts (hc.getArg 4)) else suiteStmts (hc.getArg 4)
  if !isStream && !blockAlwaysReturns bodyStmts then throwErrorAt pathStx s!"missing `return` on fallthrough path of `{routeLabel}`"
  let reqs ← elabRequiresClauses routeIdent routeLeaf routeLabel "_hHttpReq" "_req" #[] #[] #[] #[] reqExprs (trackAuth := true)
  let payloadTerm ← if isStream then `(Unit) else `(Qed.Server.HttpResponse)
  let errTyTerm ← `(Qed.Server.ApiError)
  let some ensRes? ← elabEnsuresAbbrev routeIdent routeLabel `result #[] #[] #[] payloadTerm ensExprs | return none
  let ensSpec? := mkFnEnsSpec? ensRes? #[] false ensTac?
  let hasAwait := blockHasAwait bodyStmts
  let some hRes ← elabServerHandler hasAwait routeLabel routeIdent reqs.allBinderIds reqs.allBinderTys reqs.allBinderArgs
      payloadTerm errTyTerm
      (← mkBaseLowerCtx routeLabel reqs.extraLocals hasAwait true true (isHttpRoute := !isStream) (isStreamRoute := isStream)) bodyStmts ensSpec? | return none
  let extraCall ← if hRes.isAsync then mkAppTerms hRes.targetId (hRes.allBinderIds.map (⟨·.raw⟩))
    else mkAppTerms (← `($(hRes.targetId) $(mkIdent `_s0))) (hRes.allBinderIds.map (⟨·.raw⟩))
  elabSrvExtraContracts routeIdent hRes.targetId routeLeaf routeLabel hRes.isAsync true c.hasState #[] hRes.allBinderIds hRes.allBinderTys extraCall payloadTerm errTyTerm none contracts (isStepPair := !hRes.isAsync) (hasEmit := hRes.hasEmit)
  let runExpr := hRes.runExpr
  let mapFn ← if isStream then `(fun _ => Option.some (Qed.Server.HttpResponse.sse [])) else `(Option.some)
  let guardedRun ← liftM <| wrapWithBefore? beforeRun? (← liftM <| wrapAuthAndReqs reqs (← `($runExpr >>= fun _httpRes => Pure.pure (_httpRes.map $mapFn))))
  return some ((methodStr, pathStr, reqs.requiresAuth), ← `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkStrLit methodStr), $(Syntax.mkStrLit pathStr) => $guardedRun))

@[noinline]
private def elabServerAuthHook (hookLabel : String) (hookLeaf : Name) (authInfo : AuthInfo) (hc : Syntax) : SrvElabM (Option Term) := do
  let c ← read; let paramIdent : Ident := ⟨hc.getArg 2⟩; let paramStr ← checkSrvParamName s!"`{hookLabel}`" paramIdent
  let hookIdent := mkIdentFrom hc hookLeaf; let bodyStmts := ensureUnitReturn hookIdent (suiteStmts (hc.getArg 5))
  let hasAwait := blockHasAwait bodyStmts; let isAsync := c.hasState && (hasAwait || blockHasAtomic bodyStmts)
  let (authUserVar, hAuthId, hAuthEqId) := (mkIdent `_authUser, mkIdent `_hAuth, mkIdent `_hAuthEq)
  let extraTys : Array Term := #[← `($(mkIdentFrom paramIdent (authInfo.authName ++ `User))), ← `(($(c.ctxId)).userId ≠ Option.none), ← `(Option.some (($paramIdent).id) = ($(c.ctxId)).userId)]
  let some hRes ← elabServerHandler isAsync hookLabel hookIdent #[paramIdent, hAuthId, hAuthEqId] extraTys
      #[⟨authUserVar.raw⟩, ⟨hAuthId.raw⟩, ⟨hAuthEqId.raw⟩] (← `(Unit)) (← `(Qed.Server.ApiError))
      (← mkBaseLowerCtx hookLabel #[paramStr] (if c.hasState then isAsync else hasAwait) true true) bodyStmts none | return none
  return some hRes.runExpr

@[noinline]
private def resolveSrvExDbTable (c : SrvElabCtx) (tblRef : Ident) : CommandElabM (Ident × String) := do
  match tblRef.getId.eraseMacroScopes with
  | .str (.str .anonymous aliasStr) tblStr =>
      if let some (_, dbInfo) := c.dbDecls.find? (·.1.getId.toString == aliasStr) then
        if dbInfo.tables.any (·.tableName == tblStr) then
          return (mkIdentFrom tblRef (dbInfo.dbName ++ Name.mkSimple tblStr), tblStr)
        throwErrorAt tblRef s!"unknown table `{tblStr}` in database `{aliasStr}`"
      return (tblRef, tblStr)
  | .str .anonymous tblStr =>
      let matchesDb := c.dbDecls.filter fun (_, dbInfo) => dbInfo.tables.any (·.tableName == tblStr)
      if matchesDb.size == 1 then
        let (_, dbInfo) := matchesDb[0]!
        return (mkIdentFrom tblRef (dbInfo.dbName ++ Name.mkSimple tblStr), tblStr)
      else if matchesDb.size > 1 then
        throwErrorAt tblRef s!"ambiguous table `{tblStr}` in `with db`; qualify it as `<db>.{tblStr}`"
      throwErrorAt tblRef s!"unknown table `{tblStr}` in `with db`; expected `<db>.<table>` from a `use <db> : ...` database"
  | .str _ tblStr => return (tblRef, tblStr)
  | _ => throwErrorAt tblRef s!"`with db` expects `<db>.<table>` (e.g. `db.items`), got `{tblRef.getId}`"

@[noinline]
private def elabSrvExamples (isService : Bool) (exampleClauses : Array Syntax)
    (serviceMethods : Array ServiceMethodInfo := #[])
    (rpcWireMap : Std.HashMap String (Term × Term) := {}) : SrvElabM Unit := do
  let c ← read
  if exampleClauses.isEmpty then return
  let mut seenNames : Std.HashSet Name := {}
  let bangIdx : Syntax → Term → Term → ExprMode → MacroM Term := fun _ arr idx _ => `($arr[$idx]!)
  let lowerVal (s : Syntax) : CommandElabM Term := liftMacroM (lowerSimpleQedExpr .val s (lowerIndex? := some bangIdx))
  let lowerProp (s : Syntax) : CommandElabM Term := liftMacroM (lowerSimpleQedExpr .propInv s (lowerIndex? := some bangIdx))
  let stateTy ← if c.hasState then pure ⟨c.stateId.raw⟩ else `(Unit)
  let initShared ← if c.hasState then pure ⟨(c.subId `initState).raw⟩ else `(())
  let envId := mkIdent `_env; let stId := mkIdent `_st; let ctxId := mkIdent `_ctx
  let resId := mkIdent `result; let statusId := mkIdent `status; let bodyId := mkIdent `body
  let httpCallsId := mkIdent `http_calls; let httpId := mkIdent `http
  let decryptCallsId := mkIdent `decrypt_calls; let encryptCallsId := mkIdent `encrypt_calls
  let dbQueriesId := mkIdent `db_queries; let cookiesId := mkIdent `cookies
  let dbCountId := mkIdent `db_count; let stateId := mkIdent `state
  for exStx in exampleClauses do
    let exId : Ident := ⟨exStx.getArg 1⟩; let exNm := exId.getId.eraseMacroScopes
    if seenNames.contains exNm then throwErrorAt exId s!"duplicate `example {exNm}` in `{c.srvName}`"
    seenNames := seenNames.insert exNm
    let items := (exStx.getArg 3).getArgs
    let rec foldItems (idx : Nat) (lastResKind : Nat) : CommandElabM Term := do
      if h : idx < items.size then
        let it := items[idx]; let ik := it.getKind
        if ik == ``srvExEnv then
          let kLit := Syntax.mkStrLit (⟨it.getArg 2⟩ : TSyntax `str).getString
          let vT ← lowerVal (it.getArg 4)
          let rest ← foldItems (idx + 1) lastResKind
          `(let $envId:ident := { $envId with envVars := ($kLit, $vT) :: ($envId).envVars }; $rest)
        else if ik == ``srvExNow then
          let vT ← lowerVal (it.getArg 3)
          let rest ← foldItems (idx + 1) lastResKind
          `(let $envId:ident := { $envId with nowMs := ($vT : UInt64) }; $rest)
        else if ik == ``srvExUser then
          let uStx := it.getArg 2; let uu := unwrapParens1 uStx
          let rest ← foldItems (idx + 1) lastResKind
          if uu.getKind == ``qedIdent && (uu.getArg 0).getId.eraseMacroScopes == `none then
            `(let $ctxId:ident := { $ctxId with userId := Option.none, authMethod := Qed.Server.AuthMethod.none }; $rest)
          else
            let uT ← lowerVal uStx
            `(let $ctxId:ident := { $ctxId with userId := Option.some $uT, authMethod := if ($ctxId).authMethod == Qed.Server.AuthMethod.none then Qed.Server.AuthMethod.bearer else ($ctxId).authMethod }; $rest)
        else if ik == ``srvExRole then
          let rT ← lowerVal (it.getArg 2)
          let rest ← foldItems (idx + 1) lastResKind
          `(let $ctxId:ident := { $ctxId with claims := ("role", $rT) :: ($ctxId).claims }; $rest)
        else if ik == ``srvExSession then
          let sT ← lowerVal (it.getArg 3)
          let rest ← foldItems (idx + 1) lastResKind
          `(let $ctxId:ident := { $ctxId with authMethod := if $sT then Qed.Server.AuthMethod.session else Qed.Server.AuthMethod.bearer }; $rest)
        else if ik == ``srvExSystem then
          let sysT ← if (it.getArg 2).getNumArgs == 2 then lowerVal ((it.getArg 2).getArg 1) else `(true)
          let rest ← foldItems (idx + 1) lastResKind
          `(let $ctxId:ident := { $ctxId with isSystem := $sysT }; $rest)
        else if ik == ``srvExHeader then
          let kLit := Syntax.mkStrLit (⟨it.getArg 2⟩ : TSyntax `str).getString
          let vT ← lowerVal (it.getArg 4)
          let rest ← foldItems (idx + 1) lastResKind
          `(let $ctxId:ident := { $ctxId with headers := ($kLit, $vT) :: ($ctxId).headers }; $rest)
        else if ik == ``srvExQuery then
          let qT ← lowerVal (it.getArg 3)
          let rest ← foldItems (idx + 1) lastResKind
          `(let $ctxId:ident := { $ctxId with query := $qT }; $rest)
        else if ik == ``srvExBody then
          let bT ← lowerVal (it.getArg 3)
          let rest ← foldItems (idx + 1) lastResKind
          `(let $ctxId:ident := { $ctxId with body := $bT }; $rest)
        else if ik == ``srvExCtx then
          let cT ← lowerVal (it.getArg 3)
          let rest ← foldItems (idx + 1) lastResKind
          `(let $ctxId:ident := ($cT : Qed.Server.RequestCtx); $rest)
        else if ik == ``srvExState then
          let sT ← lowerVal (it.getArg 3)
          let rest ← foldItems (idx + 1) lastResKind
          `(let $stId:ident := { $stId with shared := ($sT : $stateTy) }; $rest)
        else if ik == ``srvExHttp || ik == ``srvExHttpErr then
          let isOk := ik == ``srvExHttp
          let mLit := Syntax.mkStrLit (it.getArg 2).getId.eraseMacroScopes.toString.toUpper
          let urlLit := Syntax.mkStrLit (⟨it.getArg 3⟩ : TSyntax `str).getString
          let codeNum : TSyntax `num := ⟨it.getArg 5⟩
          let payloadT ← if (it.getArg 6).getNumArgs == 1 then lowerVal ((it.getArg 6).getArg 0) else if isOk then `("") else `("upstream error")
          let stubT ← if isOk then `(Qed.Server.Eval.HttpStub.ok $mLit $urlLit ($codeNum : UInt32) $payloadT)
                      else `(Qed.Server.Eval.HttpStub.err $mLit $urlLit $codeNum $payloadT)
          let rest ← foldItems (idx + 1) lastResKind
          `(let $stId:ident := { $stId with httpStubs := ($stId).httpStubs ++ [$stubT] }; $rest)
        else if ik == ``srvExDb then
          let (tblRowId, tblStr) ← resolveSrvExDbTable c ⟨it.getArg 2⟩
          let rawRows := it.getArg 4
          let rowsListT ← if rawRows.getKind == ``qedArrLit then
              let elems ← (rawRows.getArg 1).getSepArgs.mapM fun el => do
                let eT ← lowerVal el
                `(($eT : $tblRowId))
              `([$[$elems:term],*])
            else
              let rT ← lowerVal rawRows
              `(($rT : List $tblRowId))
          let schemaId := mkIdentFrom tblRowId (tblRowId.getId ++ `schema)
          let encId := mkIdentFrom tblRowId (tblRowId.getId ++ `encodeRow)
          let rest ← foldItems (idx + 1) lastResKind
          `(let $stId:ident := { $stId with db := ($stId).db.seedEncoded $(Syntax.mkStrLit tblStr) (($schemaId).columns.map fun _c => _c.name.raw) (($rowsListT : List $tblRowId).map $encId) }; $rest)
        else if ik == ``srvExCall then
          let fnId : Ident := ⟨it.getArg 1⟩; let fnStr := fnId.getId.eraseMacroScopes.toString
          let argTerms ← (it.getArg 3).getSepArgs.mapM lowerVal
          if isService then
            let some mi := serviceMethods.find? (·.name == fnStr)
              | throwErrorAt fnId s!"unknown service function `{fnStr}` in `example {exNm}`"
            let fullArgs := (if mi.takesCtx then #[⟨ctxId.raw⟩] else #[]) ++ argTerms
            let fnRef := c.subId (Name.mkSimple fnStr) fnId
            let callExpr ← mkAppTerms fnRef fullArgs
            if mi.isMonadic then
              let rest ← foldItems (idx + 1) 0
              `(let _ev := Qed.Server.Eval.evalProg $envId $stId ($callExpr : Qed.Server.ThreadProg Unit _)
                let $stId:ident := _ev.state
                let $resId:ident := _ev.value
                $rest)
            else
              let rest ← foldItems (idx + 1) (if mi.isFallible then 0 else 2)
              `(let $resId:ident := $callExpr
                $rest)
          else if let some (reqTupleTy, wireRespTy) := rpcWireMap[fnStr]? then
            let tupleVal ← liftMacroM <| buildTupleVal argTerms
            let dispId := c.subId `dispatchM fnId
            let rest ← foldItems (idx + 1) 0
            `(let _ev := Qed.Server.Eval.evalProg $envId $stId ($dispId $ctxId $(Syntax.mkStrLit fnStr) (Qed.Proto.encode ($tupleVal : $reqTupleTy)) : Qed.Server.ThreadProg $stateTy _)
              let $stId:ident := _ev.state
              let $resId:ident : Except Qed.Server.ApiError $wireRespTy :=
                _ev.value.bind fun _bs => (Qed.Proto.decode (α := $wireRespTy) _bs).mapError Qed.Server.ApiError.internal
              $rest)
          else if let some hs := c.helpers.find? (·.name == fnStr) then
            let fullArgs := (if hs.takesEnvs then c.envIdents.map (⟨·.raw⟩) else #[]) ++ (if hs.takesCtx then #[⟨ctxId.raw⟩] else #[]) ++ argTerms
            let callExpr ← mkAppTerms hs.defId fullArgs
            if hs.isMonadic || !c.envDecls.isEmpty then
              let monExpr ← if hs.isMonadic then pure callExpr
                else if hs.isFallible then `(Pure.pure $callExpr)
                else `(Pure.pure (Except.ok (α := Qed.Server.ApiError) $callExpr))
              let (wrappedCall, _) ← wrapWithEnvDecls c.envDecls monExpr none
              let rest ← foldItems (idx + 1) 0
              `(let _ev := Qed.Server.Eval.evalProg $envId $stId ($wrappedCall : Qed.Server.ThreadProg $stateTy _)
                let $stId:ident := _ev.state
                let $resId:ident := _ev.value
                $rest)
            else
              let rest ← foldItems (idx + 1) (if hs.isFallible then 0 else 2)
              `(let $resId:ident := $callExpr
                $rest)
          else
            throwErrorAt fnId s!"unknown RPC or helper `fn` `{fnStr}` in `example {exNm}`"
        else if ik == ``srvExReq then
          if isService then throwErrorAt it s!"HTTP requests are only available in `server` examples, not `service {c.srvName}`"
          let mStr := (it.getArg 0).getId.eraseMacroScopes.toString.toUpper
          let pStr := (⟨it.getArg 1⟩ : TSyntax `str).getString
          let dispId := c.subId `httpDispatchM ⟨it.getArg 0⟩
          let rest ← foldItems (idx + 1) 1
          `(let _ev := Qed.Server.Eval.evalProg $envId $stId ($dispId $ctxId $(Syntax.mkStrLit mStr) $(Syntax.mkStrLit pStr) : Qed.Server.ThreadProg $stateTy _)
            let $stId:ident := _ev.state
            let $resId:ident := _ev.value
            let $statusId:ident : Nat := (match ($resId:ident) with | Except.ok (Option.some _r) => _r.status | Except.ok Option.none => 404 | Except.error _e => _e.code)
            let $bodyId:ident : String := (match ($resId:ident) with | Except.ok (Option.some _r) => (String.fromUTF8? _r.body).getD "" | Except.ok Option.none => "" | Except.error _e => _e.message)
            $rest)
        else
          let rest ← foldItems (idx + 1) lastResKind
          let wrapEnv (checkT : Term) : CommandElabM Term :=
            `(let $httpCallsId:ident : Nat := ($stId).trace.httpCalls.length
              let $httpId:ident : Array Qed.Server.OutboundReq := ($stId).trace.httpCalls.toArray
              let $decryptCallsId:ident : Nat := ($stId).trace.decryptCount
              let $encryptCallsId:ident : Nat := ($stId).trace.encryptCount
              let $dbQueriesId:ident : Nat := ($stId).trace.dbQueries.length
              let $cookiesId:ident : Array Qed.Server.SetCookie := ($stId).trace.cookies.toArray
              let $dbCountId:ident : String → Nat := ($stId).db.countRows
              let $stateId:ident := ($stId).shared
              ($checkT) ∧ ($rest))
          if ik == ``srvExExpectOk then
            let valOpt := it.getArg 2
            let chk ← if valOpt.getNumArgs == 3 then
                let vT ← lowerVal (valOpt.getArg 1)
                if lastResKind == 1 then `((match ($resId:ident) with | Except.ok (Option.some _r) => decide (_r = $vT) | _ => false) = true)
                else if lastResKind == 2 then `($resId:ident = $vT)
                else `((match ($resId:ident) with | Except.ok _v => decide (_v = $vT) | Except.error _ => false) = true)
              else
                if lastResKind == 1 then `((match ($resId:ident) with | Except.ok (Option.some _) => true | _ => false) = true)
                else if lastResKind == 2 then `(True)
                else `((match ($resId:ident) with | Except.ok _ => true | Except.error _ => false) = true)
            wrapEnv chk
          else if ik == ``srvExExpectErr then
            if lastResKind == 2 then throwErrorAt it s!"`expect error` cannot be used after a pure (non-fallible) call in `example {exNm}`"
            let codeOpt := it.getArg 2
            let chk ← if codeOpt.getNumArgs == 3 then
                let cNum : TSyntax `num := ⟨codeOpt.getArg 1⟩
                `((match ($resId:ident) with | Except.error _e => _e.code == $cNum | _ => false) = true)
              else `((match ($resId:ident) with | Except.error _ => true | _ => false) = true)
            wrapEnv chk
          else if ik == ``srvExExpectStatus then
            let sT ← lowerVal (it.getArg 3)
            wrapEnv (← `($statusId = $sT))
          else if ik == ``srvExExpectExpr then
            let pT ← lowerProp (it.getArg 1)
            wrapEnv pT
          else throwErrorAt it s!"unexpected item in `example {exNm}`"
      else `(True)
    let bodyProp ← liftM <| foldItems 0 0
    let fullProp ← `(
      let $envId:ident : Qed.Server.Eval.EvalEnv := {}
      let $stId:ident : Qed.Server.Eval.EvalState $stateTy := { shared := $initShared }
      let $ctxId:ident : Qed.Server.RequestCtx := {}
      $bodyProp)
    let thmId := c.subId (Name.mkSimple s!"example_{exNm}") exId
    withRef exId <| elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      theorem $thmId:ident : $fullProp:term := by decide +kernel))

@[noinline]
private def elabServerCmdCore (priorRep priorUnrep : Nat) : CommandElab := fun stx => do
  let isStateless := (stx.getArg 1).getNumArgs == 1
  let srvIdent : Ident := ⟨stx.getArg 2⟩; let srvName := srvIdent.getId
  let parsed ← parseServerClauses srvIdent srvName (stx.getArg 4).getArgs
  if isStateless then
    if let some (stId, _, _, _) := parsed.stateDecls[0]? then
      throwErrorAt stId s!"`server stateless {srvName}` forbids in-memory `state` field `{stId.getId}`; persist state in a `database` (`use db : ...`) or remove `stateless`"
  let initCtx : SrvElabCtx := {
    priorRep, priorUnrep, srvIdent, srvName, fullSrvName := (← getCurrNamespace) ++ srvName, hasState := !parsed.stateDecls.isEmpty,
    dbDecls := parsed.dbDecls, serviceDecls := parsed.serviceDecls, authDecl? := parsed.authDecl?, envDecls := parsed.envDecls,
    stateFieldNames := parsed.stateDecls.map (·.1.getId.toString), envVarNames := parsed.envDecls.map (·.ident.getId.toString),
    invs := parsed.invs, mutInvs := parsed.mutInvs, deferredProofs := ← IO.mkRef #[], extRootsRef := ← IO.mkRef #[] }
  (do
    if initCtx.hasState then unless (← elabServerStateCmds parsed.stateDecls) do return
    if isStateless then elabSrvCmd (← `(command| theorem $(initCtx.subId `is_stateless) : True := True.intro))
    let mut chanHeaders : Array ParsedChanHeader := #[]
    for cc in parsed.chanClauses do
      let some hdr ← elabServerChannelHeader (chanHeaders.map ParsedChanHeader.chStr) cc | return
      chanHeaders := chanHeaders.push hdr
    withReader (fun (c : SrvElabCtx) => { c with chanSigs := chanHeaders.map ParsedChanHeader.sig }) do
      let mut helperSigs : Array SrvHelperSig := #[]; let mut statefulHelperIds : Array Ident := #[]
      for hlc in parsed.helperClauses do
        let some (hs, shIds) ← withReader (fun (c : SrvElabCtx) => { c with helpers := helperSigs, statefulHelperIds }) (elabServerHelperClause hlc) | return
        helperSigs := helperSigs.push hs; statefulHelperIds := statefulHelperIds ++ shIds
      withReader (fun (c : SrvElabCtx) => { c with helpers := helperSigs, statefulHelperIds }) do
        let beforeRun? : Option Term ← match parsed.beforeClause? with
          | none => pure none
          | some bc => match ← elabServerBeforeClause bc with | some br => pure (some br) | none => return
        let mut methodInfos : Array ServerMethodInfo := #[]; let mut dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
        let mut rpcWireMap : Std.HashMap String (Term × Term) := {}
        for fc in parsed.fnClauses do
          let some (info, wireTys, arm) ← elabServerFnClause methodInfos fc beforeRun? | return
          methodInfos := methodInfos.push info; rpcWireMap := rpcWireMap.insert info.name wireTys; dispatchArms := dispatchArms.push arm
        let mut wsDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
        let mut wsProjectArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
        for hdr in chanHeaders do
          let some (chArms, projArm?) ← elabServerChannelBody hdr beforeRun? | return
          wsDispatchArms := wsDispatchArms ++ chArms
          if let some pa := projArm? then wsProjectArms := wsProjectArms.push pa
        let mut httpRoutes : Array (String × String × Bool) := #[]; let mut httpDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
        for (hc, idx) in parsed.httpClauses.zipIdx do
          let some (rt, arm) ← elabServerHttpRouteClause idx httpRoutes hc beforeRun? | return
          httpRoutes := httpRoutes.push rt; httpDispatchArms := httpDispatchArms.push arm
        let some jobNames ← elabServerJobs methodInfos parsed.jobClauses | return
        let elabHook? (lbl : String) (leaf : Name) (cl? : Option Syntax) : SrvElabM (Option (Option Term)) :=
          match parsed.authDecl?, cl? with | some (_, ai), some hc => Option.map some <$> elabServerAuthHook lbl leaf ai hc | _, _ => pure (some none)
        let some onCreateRun? ← elabHook? "onCreateAccount" `_onCreateAccount parsed.onCreateAccountClause? | return
        let some onSignInRun? ← elabHook? "onSignIn" `_onSignIn parsed.onSignInClause? | return
        elabServerDispatchCmds methodInfos dispatchArms (chanHeaders.map ParsedChanHeader.chStr) wsDispatchArms wsProjectArms httpDispatchArms jobNames onCreateRun? onSignInRun?
        for (invId, pfxStr, excs) in parsed.routesAuthInvs do
          let missing : Array (String × String × Bool) := httpRoutes.filter fun r => r.2.1.startsWith pfxStr && !excs.contains r.2.1 && !r.2.2
          unless missing.isEmpty do
            let list := String.intercalate ", " (missing.toList.map fun (r : String × String × Bool) => s!"`{r.1} {r.2.1}`")
            throwErrorAt invId s!"server invariant `{invId.getId}` violated: routes matching \"{pfxStr}\" without `requires auth`: {list}"
          elabSrvCmd (← `(command| theorem $(initCtx.subId invId.getId invId) : True := True.intro))
        for (invId, excs) in parsed.rpcsAuthInvs do
          let missing := methodInfos.filter fun (m : ServerMethodInfo) => !excs.contains m.name && !m.requiresAuth
          unless missing.isEmpty do
            let list := String.intercalate ", " (missing.toList.map fun (m : ServerMethodInfo) => s!"`{m.name}`")
            throwErrorAt invId s!"server invariant `{invId.getId}` violated: RPCs without `requires auth`: {list}"
          elabSrvCmd (← `(command| theorem $(initCtx.subId invId.getId invId) : True := True.intro))
        for invId in parsed.noSecretsInvs do
          elabSrvCmd (← `(command| theorem $(initCtx.subId invId.getId invId) : $(initCtx.subId `secrets) = #[] := rfl))
        elabSrvExamples false parsed.exampleClauses #[] rpcWireMap
  ).run initCtx
  for runProof in ← initCtx.deferredProofs.get do unless (← runProof) do return

@[command_elab serverCmd]
def elabServerCmd : CommandElab := fun stx => do
  let savedEnv ← getEnv; let priorLog := (← get).messages
  let fullSrvName := (← getCurrNamespace) ++ (stx.getArg 2).getId
  let (priorRep, priorUnrep, priorKinds, priorTasks) := (priorLog.reported.size, priorLog.unreported.size, priorLog.loggedKinds, (← get).snapshotTasks.size)
  let rollback : CommandElabM Unit := do
    setEnv (Qed.failedServerRegistry.addEntry savedEnv fullSrvName)
    modify fun s => let m := s.messages; { s with messages := { reported := filterNewWarnings m.reported priorRep, unreported := filterNewWarnings m.unreported priorUnrep, loggedKinds := priorKinds } }
  try elabServerCmdCore priorRep priorUnrep stx catch ex => rollback; throw ex
  let asyncErr := ((← get).snapshotTasks.extract priorTasks (← get).snapshotTasks.size).any fun t => Qed.Diag.snapshotTreeHasErrors 64 t.get
  if hasNewErrors (← get).messages priorRep priorUnrep || asyncErr then rollback

/-! ## Stateless `service` Command Elaborator -/

@[noinline]
private def elabServiceFnClause (hc : Syntax) : SrvElabM (Option (ServiceMethodInfo × SrvHelperSig)) := do
  let c ← read; let (declaredReadOnly, isSystem) ← liftM <| parseSrvFnMods (hc.getArg 0)
  let fnIdent : Ident := ⟨hc.getArg 2⟩; let fnStr := fnIdent.getId.toString
  if c.helpers.any (·.name == fnStr) then throwErrorAt fnIdent s!"duplicate `fn {fnStr}` in `service {c.srvName}`"
  let contracts ← liftM <| parseSrvContracts "`service` `fn`" (hc.getArg 8).getArgs
  let (reqExprs, ensExprs, ensTac?) := (contracts.requires, contracts.topEnsures, contracts.topEnsTac?)
  let pp ← parseSrvFnParams s!"service `fn {fnStr}`" "parameter" (hc.getArg 4).getSepArgs
    (reserved := if ensExprs.isEmpty then #[] else #["result"]) (allowExplicitCtx := true)
  let (pIdents, pTyTerms, pDefBinders, paramNames, minParamCount, hasExplicitCtx) :=
    (pp.idents, pp.tyTerms, pp.defBinders, pp.names, pp.minParamCount, pp.hasExplicitCtx)
  let hasExplicitRet := (hc.getArg 6).getNumArgs == 2
  let (payloadTerm, innerOpt?, isFallible, isUnitPayload) ←
    if hasExplicitRet then
      let rt ← liftMacroM <| lowerSrvType ((hc.getArg 6).getArg 1) true s!"return type of service `fn {fnStr}`"
      pure (rt.term, rt.innerOpt?, rt.isFallible, (rt.mods.filter (· != .fallible)).isEmpty && rt.baseName == `Unit)
    else pure (← `(Unit), none, true, true)
  let bodyStmts := if isUnitPayload then ensureUnitReturn fnIdent (suiteStmts (hc.getArg 9)) else suiteStmts (hc.getArg 9)
  if !isUnitPayload && !blockAlwaysReturns bodyStmts then throwErrorAt fnIdent s!"missing `return` on fallthrough path of service `fn {fnStr}`"
  let (domainTagIdents, hasPlainFail) ← liftM <| scanBodyFailTags bodyStmts
  if !domainTagIdents.isEmpty then throwErrorAt fnIdent s!"typed `fail(.tag)` is only supported in `rpc` endpoints; use `fail(code, msg)` or `fail(msg)` in `service` `fn {fnStr}`"
  if hasPlainFail && !isFallible then throwErrorAt fnIdent s!"`fail(...)` can only be returned from a fallible `T!` function (`fn {fnStr}` is not declared `-> ...!`)"
  let allStx := bodyStmts ++ reqExprs ++ pp.defaultExprs
  let usedEnvs := c.envDecls.filter fun e => allStx.any (stxMentionsVar e.ident.getId.toString)
  let hasReqEnv := usedEnvs.any (·.default?.isNone)
  let hasTx := bodyStmts.any (stxAny (·.getKind == ``qedStmtDbTransaction))
  let mentionsCtx := allStx.any (stxMentionsVar "ctx")
  let callsTakesCtxHelper := c.helpers.any fun h => h.takesCtx && bodyStmts.any (stxMentionsVar h.name)
  let callsTakesCtxSvc := c.serviceDecls.any fun (al, si) =>
    let alStr := al.getId.toString
    si.methods.any fun m => m.takesCtx && bodyStmts.any (stxMentionsVar alStr) && bodyStmts.any (stxAny fun s =>
      (extractDottedChain? s).any fun ch => ch == [alStr, m.name])
  let reqs ← elabRequiresClauses fnIdent fnIdent.getId fnStr "_hSvcReq" "_req" paramNames paramNames pIdents pTyTerms reqExprs (trackAuth := true)
  let needsImplicitCtx := !hasExplicitCtx && (mentionsCtx || reqs.authBind?.isSome || callsTakesCtxHelper || callsTakesCtxSvc)
  let ctxTy ← `(Qed.Server.RequestCtx)
  let hasCtxInScope := hasExplicitCtx || needsImplicitCtx
  let ctxTerm? : Option Term ←
    if isSystem then
      if hasCtxInScope then some <$> `({ $(c.ctxId) with isSystem := true })
      else some <$> `({ isSystem := true : Qed.Server.RequestCtx })
    else if hasCtxInScope then pure none
    else some <$> `(({} : Qed.Server.RequestCtx))
  let wrapSysCtx (body : Term) : CommandElabM Term :=
    if isSystem && hasCtxInScope then `(let $(c.ctxId):ident : Qed.Server.RequestCtx := { $(c.ctxId) with isSystem := true }; $body)
    else pure body
  let hasAwait := blockHasAwait bodyStmts
  let callsMonadicHelper := c.helpers.any fun h => h.isMonadic && bodyStmts.any (stxMentionsVar h.name)
  let isMonadic := hasAwait || callsMonadicHelper || !usedEnvs.isEmpty
  let bodyHasUnwrap := bodyStmts.any (stxAny exprHasUnwrap)
  if !isFallible && (hasReqEnv || !reqExprs.isEmpty || hasTx || hasPlainFail || (bodyHasUnwrap && innerOpt?.isNone)) then
    throwErrorAt fnIdent s!"service `fn {fnStr}` can fail (uses required `secret`/`env`, `requires`, `transaction`, `fail`, or `?`); declare its return type as `-> ...!`"
  let defId := c.subId fnIdent.getId fnIdent
  let defConst := c.fullSrvName ++ fnIdent.getId
  let errTyTerm ← `(Qed.Server.ApiError); let fnLit := Syntax.mkStrLit fnStr
  let some ensRes? ← elabEnsuresAbbrev fnIdent fnStr `result paramNames pIdents pTyTerms (innerOpt?.getD payloadTerm) ensExprs | return none
  let pTerms : Array Term := pIdents.map (⟨·.raw⟩)
  let ensSpec? := mkFnEnsSpec? ensRes? pTerms innerOpt?.isSome ensTac?
  let ctxBinderArr : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ←
    if needsImplicitCtx then pure #[← `(bracketedBinder| ($(c.ctxId):ident : $ctxTy))] else pure #[]
  let allDefBinders := ctxBinderArr ++ pDefBinders
  let thmBinderIds := (if needsImplicitCtx then #[c.ctxId] else #[]) ++ pIdents
  let thmBinderTys := (if needsImplicitCtx then #[ctxTy] else #[]) ++ pTyTerms
  let baseCtx ← mkBaseLowerCtx fnStr (paramNames ++ reqs.extraLocals) isMonadic (isFallible || (innerOpt?.isSome && isMonadic)) isFallible innerOpt? (ctxTerm? := ctxTerm?) (txParams := pp.txParams)
  let mId := mkIdent `m
  if !isMonadic && !isFallible then
    let pureCtx := { baseCtx with allowUnwrap := false }
    let bodyTerm ← liftM <| Qed.lowerPureFnStmts s!"service fn {fnStr}" bodyStmts.toList
      (fun s => do let (t, st) ← (lowerExpr pureCtx .val s).run {}; (recordSrvExtRoots st.extRoots).run c; pure t)
      (fun s => do let (t, st) ← (lowerExpr pureCtx .propGuard s).run {}; (recordSrvExtRoots st.extRoots).run c; pure t)
    let fullBody ← liftM <| wrapSysCtx (← `(srvAutoField($bodyTerm)))
    elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      @[noinline] def $defId $[$allDefBinders:bracketedBinder]* : $payloadTerm := $fullBody))
    if (← hasSrvErrors) then return none
    if let some (ensId, _, labelStr) := ensRes? then
      let callT ← mkAppTerms defId (thmBinderIds.map (⟨·.raw⟩))
      let ensApp ← mkAppTerms ensId pTerms
      let goal ← if innerOpt?.isSome then `(∀ _r, $callT = some _r → $ensApp _r) else `($ensApp ($callT))
      let ensTac ← liftM <| mkStepEnsProofTac #[defId, ensId] fnLit labelStr ensTac?
      deferSrvCmd (← `(command| theorem $(c.fnSubId fnIdent "_ensures") $[($thmBinderIds:ident : $thmBinderTys:term)]* : $goal := by $ensTac))
    let callT ← mkAppTerms defId (thmBinderIds.map (⟨·.raw⟩))
    elabSrvExtraContracts fnIdent defId fnIdent.getId fnStr false false false pIdents thmBinderIds thmBinderTys callT payloadTerm errTyTerm innerOpt? contracts
    let mInfo : ServiceMethodInfo := { name := fnStr, defConst, minParamCount, paramCount := pIdents.size, isMonadic := false, isFallible := false, takesCtx := needsImplicitCtx, hasEnsures := ensRes?.isSome }
    let hSig : SrvHelperSig := { name := fnStr, defId, minParamCount, paramCount := pIdents.size, isMonadic := false, takesAtomic := false, takesEnvs := false, takesCtx := needsImplicitCtx, mutatesState := false, dbWrite := false }
    return some (mInfo, hSig)
  else if !isMonadic then
    let sUnitId := mkIdent `_sUnit
    let (pureBody, lSt) ← liftM <| (lowerPureBlock baseCtx false sUnitId sUnitId bodyStmts).run {}
    recordSrvExtRoots lSt.extRoots
    checkReadOnlyDecl fnIdent "fn" fnStr declaredReadOnly false lSt.dbWrite false lSt.hasCookieOp
    let inner ← liftM <| wrapSysCtx (← `(let $sUnitId:ident : Unit := (); (Qed.Server.srvFinish $sUnitId $pureBody).2))
    let wrapped ← liftM <| wrapAuthAndReqs reqs inner (pureWrap := false)
    elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      @[noinline] def $defId $[$allDefBinders:bracketedBinder]* : Except $errTyTerm $payloadTerm := $wrapped))
    if (← hasSrvErrors) then return none
    if let some ens := ensSpec? then
      let callT ← mkAppTerms defId (thmBinderIds.map (⟨·.raw⟩))
      let postGoal ← liftM <| ens.postFn callT
      let ensTac ← liftM <| mkStepEnsProofTac #[defId, ens.ensId] fnLit ens.labelStr ens.tac?
      deferSrvCmd (← `(command| theorem $(c.fnSubId fnIdent "_ensures") $[($thmBinderIds:ident : $thmBinderTys:term)]* : $postGoal := by $ensTac))
    let callT ← mkAppTerms defId (thmBinderIds.map (⟨·.raw⟩))
    elabSrvExtraContracts fnIdent defId fnIdent.getId fnStr false true false pIdents thmBinderIds thmBinderTys callT payloadTerm errTyTerm innerOpt? contracts
    let mInfo : ServiceMethodInfo := { name := fnStr, defConst, minParamCount, paramCount := pIdents.size, isMonadic := false, isFallible := true, takesCtx := needsImplicitCtx, dbWrite := lSt.dbWrite, hasCookieOp := lSt.hasCookieOp, hasEnsures := ensRes?.isSome }
    let hSig : SrvHelperSig := { name := fnStr, defId, minParamCount, paramCount := pIdents.size, isMonadic := false, takesAtomic := false, takesEnvs := false, takesCtx := needsImplicitCtx, mutatesState := false, dbWrite := lSt.dbWrite, hasCookieOp := lSt.hasCookieOp }
    return some (mInfo, hSig)
  else
    let (fullBody, lSt, retTy, ensPost?) ←
      if !isFallible then
        let (infBody, st) ← liftM <| (lowerInfallibleAsyncBlock baseCtx bodyStmts).run {}
        let fb := (← liftM <| wrapWithEnvDecls usedEnvs (← liftM <| wrapSysCtx infBody)).1
        let ep? ← match ensRes? with
          | some (ensId, _, labelStr) =>
              let outVar := mkIdent `_srvOut; let ensApp ← mkAppTerms ensId pTerms
              let postBody ← if innerOpt?.isSome then `(∀ _r, $outVar = some _r → $ensApp _r) else `($ensApp $outVar)
              pure (some (ensId, labelStr, ensTac?, outVar, postBody))
          | none => pure none
        pure (fb, st, payloadTerm, ep?)
      else
        let (asyncBody, st) ← liftM <| (lowerAsyncBlock baseCtx none bodyStmts).run {}
        let guarded ← liftM <| wrapAuthAndReqs reqs (← liftM <| wrapSysCtx (← `(Qed.Server.srvFinishM $asyncBody)))
        let fb := (← liftM <| wrapWithEnvDecls usedEnvs guarded).1
        let rTy ← `(Except $errTyTerm $payloadTerm)
        let ep? ← match ensSpec? with
          | some ens =>
              let outVar := mkIdent `_srvOut; let postBody ← liftM <| ens.postFn ⟨outVar.raw⟩
              pure (some (ens.ensId, ens.labelStr, ens.tac?, outVar, postBody))
          | none => pure none
        pure (fb, st, rTy, ep?)
    recordSrvExtRoots lSt.extRoots
    checkReadOnlyDecl fnIdent "fn" fnStr declaredReadOnly false lSt.dbWrite false lSt.hasCookieOp
    elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      @[noinline] def $defId {$mId:ident : Type → Type} [Monad $mId] [Qed.Server.MonadServer $mId] $[$allDefBinders:bracketedBinder]* :
          $mId $retTy := $fullBody))
    if (← hasSrvErrors) then return none
    let thmArgTerms : Array Term := thmBinderIds.map (⟨·.raw⟩)
    let callT ← `($defId ($mId := Qed.Server.ThreadProg _σ) $thmArgTerms*)
    let noAtomId := c.fnSubId fnIdent "_noAtomic"
    let noAtomApp ← mkAppTerms noAtomId (thmBinderIds.map (⟨·.raw⟩))
    elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      theorem $noAtomId {_σ : Type} $[($thmBinderIds:ident : $thmBinderTys:term)]* :
          Qed.Server.NoAtomic $callT := by qedSrvProveSafeIO $defId))
    elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      instance {_σ : Type} $[($thmBinderIds:ident : $thmBinderTys:term)]* :
          Qed.Server.SafeIO $callT := ⟨$noAtomApp⟩))
    if let some (ensId, labelStr, tac?, outVar, postBody) := ensPost? then
      let ensThmId := c.fnSubId fnIdent "_ensures"
      let ensThmApp ← mkAppTerms ensThmId (thmBinderIds.map (⟨·.raw⟩))
      let ensTac ← liftM <| mkAsyncEnsProofTac defId #[ensId] fnLit labelStr tac?
      elabSrvCmd (← `(command|
        set_option linter.unusedVariables false in
        theorem $ensThmId {_σ : Type} {_Inv : _σ → Prop} $[($thmBinderIds:ident : $thmBinderTys:term)]* :
            Qed.Server.ProgEnsures _Inv (fun ($outVar:ident : $retTy) => $postBody) $callT := by $ensTac))
      elabSrvCmd (← `(command|
        set_option linter.unusedVariables false in
        instance {_σ : Type} $[($thmBinderIds:ident : $thmBinderTys:term)]* :
            Qed.Server.SafeIOEnsures $callT (fun ($outVar:ident : $retTy) => $postBody) :=
          ⟨$noAtomApp, fun {_Inv} => $ensThmApp⟩))
    elabSrvExtraContracts fnIdent defId fnIdent.getId fnStr true isFallible false pIdents thmBinderIds thmBinderTys callT payloadTerm errTyTerm innerOpt? contracts (defer := false)
    if (← hasSrvErrors) then return none
    let mInfo : ServiceMethodInfo := { name := fnStr, defConst, minParamCount, paramCount := pIdents.size, isMonadic := true, isFallible, takesCtx := needsImplicitCtx, dbWrite := lSt.dbWrite, hasCookieOp := lSt.hasCookieOp, hasEnsures := ensRes?.isSome }
    let hSig : SrvHelperSig := { name := fnStr, defId, minParamCount, paramCount := pIdents.size, isMonadic := true, takesAtomic := false, takesEnvs := false, takesCtx := needsImplicitCtx, mutatesState := false, dbWrite := lSt.dbWrite, hasCookieOp := lSt.hasCookieOp }
    return some (mInfo, hSig)

@[noinline]
private def elabServiceCmdCore (priorRep priorUnrep : Nat) : CommandElab := fun stx => do
  let svcIdent : Ident := ⟨stx.getArg 1⟩; let svcName := svcIdent.getId
  let parsed ← parseServerClauses svcIdent svcName (stx.getArg 3).getArgs (isService := true)
  let initCtx : SrvElabCtx := {
    priorRep, priorUnrep, srvIdent := svcIdent, srvName := svcName, fullSrvName := (← getCurrNamespace) ++ svcName, hasState := false,
    dbDecls := parsed.dbDecls, serviceDecls := parsed.serviceDecls, authDecl? := none, envDecls := parsed.envDecls,
    stateFieldNames := #[], envVarNames := parsed.envDecls.map (·.ident.getId.toString),
    invs := #[], mutInvs := #[], deferredProofs := ← IO.mkRef #[], extRootsRef := ← IO.mkRef #[] }
  (do
    let mut methodInfos : Array ServiceMethodInfo := #[]; let mut helperSigs : Array SrvHelperSig := #[]
    for hlc in parsed.helperClauses do
      let some (mi, hs) ← withReader (fun (c : SrvElabCtx) => { c with helpers := helperSigs }) (elabServiceFnClause hlc) | return
      methodInfos := methodInfos.push mi; helperSigs := helperSigs.push hs
    let (reqSecrets, ownSecrets, usedExts, allDbs, allEnvs) ← collectServerSecretsAndExts
    let mkLits (ss : Array String) : Array Term := ss.map (Syntax.mkStrLit ·)
    elabSrvCmds #[
      ← `(command| @[noinline] def $(initCtx.subId `secrets) : Array String := #[$(mkLits reqSecrets),*]),
      ← `(command| theorem $(initCtx.subId `_qed_service_marker) : True := True.intro)]
    for invId in parsed.noSecretsInvs do
      elabSrvCmd (← `(command| theorem $(initCtx.subId invId.getId invId) : $(initCtx.subId `secrets) = #[] := rfl))
    elabSrvExamples true parsed.exampleClauses methodInfos
    modifyEnv fun env => serviceRegistry.addEntry env {
      serviceName := initCtx.fullSrvName, shortName := svcName.toString,
      secrets := reqSecrets, ownSecrets, envVars := allEnvs, externalServices := usedExts,
      databases := allDbs, methods := methodInfos }
  ).run initCtx
  for runProof in ← initCtx.deferredProofs.get do unless (← runProof) do return

@[command_elab serviceCmd]
def elabServiceCmd : CommandElab := fun stx => do
  let savedEnv ← getEnv; let priorLog := (← get).messages
  let fullSvcName := (← getCurrNamespace) ++ (stx.getArg 1).getId
  let (priorRep, priorUnrep, priorKinds, priorTasks) := (priorLog.reported.size, priorLog.unreported.size, priorLog.loggedKinds, (← get).snapshotTasks.size)
  let rollback : CommandElabM Unit := do
    setEnv (Qed.Server.failedServiceRegistry.addEntry savedEnv fullSvcName)
    modify fun s => let m := s.messages; { s with messages := { reported := filterNewWarnings m.reported priorRep, unreported := filterNewWarnings m.unreported priorUnrep, loggedKinds := priorKinds } }
  try elabServiceCmdCore priorRep priorUnrep stx catch ex => rollback; throw ex
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
  let env ← getEnv; let openDecls ← getOpenDecls
  let some srvInfo := Qed.Diag.lookupNameMapExt? serverRegistry env currNs openDecls srvIdent.getId
    | if (Qed.Diag.lookupNameMapExt? Qed.failedServerRegistry env currNs openDecls srvIdent.getId).isSome then return
      throwErrorAt srvIdent s!"unknown `server` `{srvIdent.getId}` in `fullstack {fsName}`"
  let cliTarget := resolveAppTargetIdent env currNs cliIdent
  let resolvedCli ← try liftCoreM <| realizeGlobalConstNoOverloadWithInfo cliTarget catch _ =>
    if ← liftCoreM (Qed.isFailedComponent cliIdent.getId) then return
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
  let wsProjArg : Term ← if srvInfo.hasWsProject then `(Option.some $(srvId `wsProject)) else `(Option.none)
  let runnerCall ← `($(mkIdent `Qed.Server.Native.runStatefulFullstack) $(mkIdentFrom fsIdent (fsInfo.fullstackName ++ `clientApp))
      $(quote fsInfo.title) $(quote srvInfo.shortName) $initStateArg $(srvId `secrets) $(← wrapHandler (srvId `dispatchM))
      port staticDir devMode numWorkers $(← optHandler (!srvInfo.channels.isEmpty) (srvId `wsDispatchM)) (some #[$asyncNames,*])
      $(← optHandler srvInfo.hasHttpRoutes (srvId `httpDispatchM)) $jobsArg $(← optId (srvInfo.authConfig?.map (mkIdentFrom fsIdent ·)))
      $(← optHandler (srvInfo.hasOnCreateAccount || srvInfo.hasOnSignIn) (srvId `authHookM))
      ($(quote srvInfo.hasOnCreateAccount), $(quote srvInfo.hasOnSignIn)) $(← optId dbCfgIds[0]?) $wsProjArg)
  let initDbCheck ← if dbCfgIds.isEmpty then `(pure true) else `($(mkIdent `Qed.Server.Native.initDatabases) #[$[$dbCfgIds:ident],*])
  let parseCliCall ← `($(mkIdent `Qed.Server.Native.parseServerCliArgs) args)
  elabCommand (← `(command|
    def $(mkIdent `main):ident (args : List String) : IO UInt32 := do
      let (staticDir, port, devMode, numWorkers) ← $parseCliCall:term
      if !(← $initDbCheck:term) then return 1
      $runnerCall:term))

end ServerFullElab
end Qed.Server
