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

  let mut reqPropTerms : Array Term := #[]
  let mut reqHypIds : Array Ident := #[]
  let mut reqHypTys : Array Term := #[]
  let mut reqLabels : Array String := #[]
  let mut clientReqProps : Array Term := #[]
  let mut clientReqLabels : Array String := #[]
  let mut requiresAuth := false
  let mut extRoots : Array Name := #[]

  for idx in [0:reqExprs.size] do
    let rExpr := reqExprs[idx]!
    if exprHasAwait rExpr then
      throwErrorAt rExpr "`requires` precondition cannot contain `await`"
    let reqCtx : LowerCtx := {
      fnName := chStr, stateFields := stateFieldNames, envVars := envVarNames, locals := paramNames
      stateRule := .forbidInRequires, allowAwait := false, allowUnwrap := false
      hasFallible := false, isOption := false, innerOptTy? := none
    }
    let (pTerm, rSt) ← (lowerExpr reqCtx .propGuard rExpr).run {}
    extRoots := extRoots ++ rSt.extRoots.filter (!extRoots.contains ·)
    let hId := mkIdent (Name.mkSimple s!"_hChReq{idx}")
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
          fnName := chStr, stateFields := stateFieldNames, envVars := #[], locals := paramNames
          stateRule := .forbidInRequires, allowAwait := false, allowUnwrap := false
          hasFallible := false, isOption := false, innerOptTy? := none, forbidCtxEnv := true
        }
        let (cpTerm, _) ← (lowerExpr cliReqCtx .propInv conj).run {}
        clientReqProps := clientReqProps.push cpTerm
        clientReqLabels := clientReqLabels.push ((conj.reprint.getD "requires").trimAscii.toString)

  let evAbbrevId := mkIdentFrom chIdent (srvName ++ chName.appendAfter "_Event")
  elabCommand (← `(command| abbrev $evAbbrevId : Type := $evTyTerm))
  let mut paramTypeConsts : Array Name := #[]
  for (pTy, i) in pTyTerms.zipIdx do
    let pTyId := mkIdentFrom chIdent (srvName ++ chName.appendAfter s!"_Param_{i}")
    elabCommand (← `(command| abbrev $pTyId : Type := $pTy))
    paramTypeConsts := paramTypeConsts.push (fullSrvName ++ chName.appendAfter s!"_Param_{i}")

  let clientReqConst : Option Name ←
    if clientReqProps.isEmpty then pure none
    else
      let cid := mkIdentFrom chIdent (srvName ++ chName.appendAfter "_req")
      let reqConj ← buildPropConj clientReqProps
      elabCommand (← `(command|
        set_option linter.unusedVariables false in
        @[simp] abbrev $cid $[($pIdents:ident : $pTyTerms:term)]* : Prop := $reqConj))
      pure (some (fullSrvName ++ chName.appendAfter "_req"))

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
    reqPropTerms, reqHypIds, reqHypTys, reqLabels, requiresAuth,
    clientReqConst, clientReqLabel := String.intercalate " && " clientReqLabels.toList,
    ensId?, ensConst?, recPolicy, onJoin?, onSend?, onLeave?, sig
  }, extRoots)

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

open Lean Elab Command in
def elabServerChannelBody (priorRep priorUnrep : Nat)
    (srvName fullSrvName : Name) (srvShort : String) (hasState : Bool)
    (stateId stateInvId ctxId : Ident)
    (envIdents : Array Ident) (envTypes : Array Term)
    (stateFieldNames envVarNames : Array String)
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (chanSigs : Array SrvChanSig) (hdr : ParsedChanHeader) :
    CommandElabM (Option (Array (TSyntax ``Lean.Parser.Term.matchAltExpr) × Array Name)) := do
  let chIdent := hdr.chIdent
  let chName := hdr.chName
  let chStr := hdr.chStr
  let chLit := Syntax.mkStrLit chStr
  let pIdents := hdr.pIdents
  let pTyTerms := hdr.pTyTerms
  let ctxTyTerm ← `(Qed.Server.RequestCtx)
  let errTyTerm ← `(Qed.Server.ApiError)
  let paramTupleTy ← buildTupleType pTyTerms
  let paramsBytesVar := mkIdent `wsParams
  let payloadBytesVar := mkIdent `wsPayload
  let pTupleVar := mkIdent `_chParams
  let pProjs ← extractTupleProjections pTupleVar pTyTerms.size
  let extRootsRef ← IO.mkRef (#[] : Array Name)
  let mut arms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]

  let wrapReqs (reqProps : Array Term) (reqHIds : Array Ident) (reqLbls : Array String) (inner : Term) : CommandElabM Term := do
    let mut g := inner
    for revIdx in [0:reqProps.size] do
      let ri := reqProps.size - 1 - revIdx
      let rCond := reqProps[ri]!
      let rHyp := reqHIds[ri]!
      let rLbl := reqLbls[ri]!
      let rMsg := Syntax.mkStrLit s!"precondition failed: {rLbl}"
      let errCtor : Term ←
        if rLbl.contains "ctx.userId" || rLbl.contains "ctx.bearerToken" || rLbl.contains "ctx.isAuthenticated" then
          `(Qed.Server.ApiError.unauthorized $rMsg)
        else
          `(Qed.Server.ApiError.badRequest $rMsg)
      g ← `(if $rHyp:ident : $rCond then $g else Pure.pure (Except.error $errCtor))
    return g

  let runSubHandler (subSuffix : String) (extraIds : Array Ident) (extraTys : Array Term)
      (extraProjs : Array Term) (_extraReqProps : Array Term) (extraReqIds : Array Ident)
      (extraReqTys : Array Term) (retTyTerm : Term) (isUnitRet : Bool) (rawStmts : Array Syntax) :
      CommandElabM (Option Term) := do
    let normStmts := unwrapOptionalOuterAtomic rawStmts
    let bodyStmts := if isUnitRet then ensureUnitReturn chIdent normStmts else normStmts
    if !isUnitRet && !blockAlwaysReturns bodyStmts then
      throwErrorAt chIdent s!"missing `return` on fallthrough path of `{chStr}.{subSuffix}`"
    let subFnStr := s!"{chStr}_{subSuffix}"
    let subFnIdent := mkIdentFrom chIdent (chName.appendAfter s!"_{subSuffix}")
    let hasAwait := blockHasAwait bodyStmts
    let allBinderIds := envIdents ++ #[ctxId] ++ pIdents ++ extraIds ++ hdr.reqHypIds ++ extraReqIds
    let allBinderTys := envTypes ++ #[ctxTyTerm] ++ pTyTerms ++ extraTys ++ hdr.reqHypTys ++ extraReqTys
    let callArgs : Array Term :=
      envIdents.map (⟨·.raw⟩) ++ #[⟨ctxId.raw⟩] ++ pProjs ++ extraProjs ++
      hdr.reqHypIds.map (⟨·.raw⟩) ++ extraReqIds.map (⟨·.raw⟩)
    let baseCtx : LowerCtx := {
      fnName := subFnStr, stateFields := stateFieldNames, envVars := envVarNames,
      locals := hdr.paramNames ++ extraIds.map (·.getId.toString),
      stateRule := if hasState then .pureStep (mkIdent `_s0) else .statelessServer,
      allowAwait := hasAwait, allowUnwrap := true, hasFallible := true,
      isOption := false, innerOptTy? := none, channels := chanSigs
    }
    if hasState && !hasAwait then
      let some (runExpr, _, er) ← elabServerPureFn priorRep priorUnrep
          srvName subFnStr subFnIdent stateId stateInvId
          allBinderIds allBinderTys callArgs retTyTerm errTyTerm baseCtx bodyStmts
          invs mutInvs stateFieldNames envVarNames none | return none
      extRootsRef.modify fun acc => acc ++ er.filter (!acc.contains ·)
      return some runExpr
    else if hasState && hasAwait then
      let some (hApp, _, er) ← elabServerAsyncFn priorRep priorUnrep
          srvName subFnStr subFnIdent stateId stateInvId
          allBinderIds allBinderTys callArgs retTyTerm errTyTerm baseCtx bodyStmts
          invs mutInvs stateFieldNames envVarNames none | return none
      extRootsRef.modify fun acc => acc ++ er.filter (!acc.contains ·)
      return some hApp
    else
      let (statelessBody, lSt) ← (lowerAsyncBlock baseCtx none bodyStmts).run {}
      extRootsRef.modify fun acc => acc ++ lSt.extRoots.filter (!acc.contains ·)
      let handlerId := mkIdentFrom chIdent (srvName ++ subFnIdent.getId.appendAfter "_handler")
      elabCommand (← `(command|
        def $handlerId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m]
            $[($allBinderIds:ident : $allBinderTys:term)]* :
            m (Except $errTyTerm $retTyTerm) :=
          Qed.Server.srvFinishM $statelessBody))
      if hasNewErrors (← get).messages priorRep priorUnrep then return none
      let hApp ← callArgs.foldlM (init := ← `($handlerId)) fun acc a => `($acc $a)
      return some hApp

  let mkChanArm (kindLit : TSyntax `num) (bodyInParams : Term) :
      CommandElabM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
    let bound ← (pIdents.zip pProjs).foldrM (init := bodyInParams) fun (pid, prj) acc =>
      `(let $pid:ident := $prj; $acc)
    `(Lean.Parser.Term.matchAltExpr|
      | $kindLit:num, $chLit =>
          match Qed.Proto.decode (α := $paramTupleTy) $paramsBytesVar with
          | Except.error _e => Pure.pure (Except.error (Qed.Server.ApiError.badRequest _e))
          | Except.ok $pTupleVar:ident => $bound)

  -- 1. `on_join` (kind = 1)
  let mut hasJoinSnapshot := false
  let mut joinTyTerm : Term ← `(Unit)
  let joinRunTerm ← match hdr.onJoin? with
    | some (some snapTyStx, stmts) =>
        hasJoinSnapshot := true
        let jty ← liftMacroM <| ParsedSrvType.parse snapTyStx
        liftMacroM <| jty.validate (allowFallible := false) s!"`on_join` return type of `channel {chStr}`"
        joinTyTerm ← liftMacroM jty.toPayloadTerm
        let some r ← runSubHandler "onJoin" #[] #[] #[] #[] #[] #[] joinTyTerm false stmts | return none
        `($r >>= fun _jRes => Pure.pure (_jRes.map Qed.Proto.encode))
    | some (none, stmts) =>
        let some r ← runSubHandler "onJoin" #[] #[] #[] #[] #[] #[] joinTyTerm true stmts | return none
        `($r >>= fun _jRes => Pure.pure (_jRes.map fun _ => ByteArray.empty))
    | none =>
        `(Pure.pure (Except.ok ByteArray.empty))

  arms := arms.push (← mkChanArm (Syntax.mkNumLit "1")
    (← wrapReqs hdr.reqPropTerms hdr.reqHypIds hdr.reqLabels joinRunTerm))

  -- 2. `on_send` (kind = 2)
  let mut hasSend := false
  let mut spIdents : Array Ident := #[]
  let mut spTyTerms : Array Term := #[]
  let mut sendParamTypeConsts : Array Name := #[]
  let mut sendReqConst? : Option Name := none
  let mut sendReqLabel := ""
  if let some (rawSParams, rawSReqs, sBody) := hdr.onSend? then
    hasSend := true
    let mut spNames : Array String := #[]
    for srp in rawSParams do
      let spid : Ident := ⟨(srp.getArg 0)⟩
      let spstr := spid.getId.toString
      if spstr == "ctx" || hdr.paramNames.contains spstr || spNames.contains spstr ||
         envVarNames.contains spstr || stateFieldNames.contains spstr then
        throwErrorAt spid s!"`on_send` parameter `{spstr}` shadows an existing binding in `channel {chStr}`"
      let spty ← liftMacroM <| ParsedSrvType.parse (srp.getArg 2)
      liftMacroM <| spty.validate (allowFallible := false) s!"`on_send` parameter `{spstr}`"
      spIdents := spIdents.push spid
      spTyTerms := spTyTerms.push (← liftMacroM spty.toPayloadTerm)
      spNames := spNames.push spstr
    for (sTy, i) in spTyTerms.zipIdx do
      let sTyId := mkIdentFrom chIdent (srvName ++ chName.appendAfter s!"_SendParam_{i}")
      elabCommand (← `(command| abbrev $sTyId : Type := $sTy))
      sendParamTypeConsts := sendParamTypeConsts.push (fullSrvName ++ chName.appendAfter s!"_SendParam_{i}")

    let mut sReqProps : Array Term := #[]
    let mut sReqIds : Array Ident := #[]
    let mut sReqTys : Array Term := #[]
    let mut sReqLbls : Array String := #[]
    let mut sCliReqProps : Array Term := #[]
    let mut sCliReqLbls : Array String := #[]
    for idx in [0:rawSReqs.size] do
      let re := rawSReqs[idx]!
      let rCtx : LowerCtx := {
        fnName := s!"{chStr}.on_send", stateFields := stateFieldNames, envVars := envVarNames,
        locals := hdr.paramNames ++ spNames, stateRule := .forbidInRequires,
        allowAwait := false, allowUnwrap := false, hasFallible := false, isOption := false, innerOptTy? := none
      }
      let (pt, rSt) ← (lowerExpr rCtx .propGuard re).run {}
      extRootsRef.modify fun acc => acc ++ rSt.extRoots.filter (!acc.contains ·)
      let hid := mkIdent (Name.mkSimple s!"_hSReq{idx}")
      sReqProps := sReqProps.push pt
      sReqIds := sReqIds.push hid
      sReqTys := sReqTys.push pt
      sReqLbls := sReqLbls.push ((re.reprint.getD "requires").trimAscii.toString)
      for conj in splitSrvAnd re do
        let (mCtx, mEnv) := scanCtxEnv envVarNames (hdr.paramNames ++ spNames) conj
        -- Client send `requires` checks expressions referencing only `on_send` parameters
        let (_, mChP) := scanCtxEnv hdr.paramNames spNames conj
        if !mCtx && !mEnv && !mChP then
          let cCtx : LowerCtx := {
            fnName := s!"{chStr}.on_send", stateFields := stateFieldNames, envVars := #[],
            locals := spNames, stateRule := .forbidInRequires, allowAwait := false, allowUnwrap := false,
            hasFallible := false, isOption := false, innerOptTy? := none, forbidCtxEnv := true
          }
          let (cpt, _) ← (lowerExpr cCtx .propInv conj).run {}
          sCliReqProps := sCliReqProps.push cpt
          sCliReqLbls := sCliReqLbls.push ((conj.reprint.getD "requires").trimAscii.toString)

    if !sCliReqProps.isEmpty then
      let srId := mkIdentFrom chIdent (srvName ++ chName.appendAfter "_send_req")
      let srConj ← buildPropConj sCliReqProps
      elabCommand (← `(command|
        set_option linter.unusedVariables false in
        @[simp] abbrev $srId $[($spIdents:ident : $spTyTerms:term)]* : Prop := $srConj))
      sendReqConst? := some (fullSrvName ++ chName.appendAfter "_send_req")
      sendReqLabel := String.intercalate " && " sCliReqLbls.toList

    let sendTupleTy ← buildTupleType spTyTerms
    let sTupleVar := mkIdent `_chSendVal
    let sProjs ← extractTupleProjections sTupleVar spTyTerms.size
    let unitTy ← `(Unit)
    let some sendRun ← runSubHandler "onSend" spIdents spTyTerms sProjs sReqProps sReqIds sReqTys unitTy true sBody | return none
    let sendOut ← `($sendRun >>= fun _sRes => Pure.pure (_sRes.map fun _ => ByteArray.empty))
    let sendGuarded ← wrapReqs (hdr.reqPropTerms ++ sReqProps) (hdr.reqHypIds ++ sReqIds) (hdr.reqLabels ++ sReqLbls) sendOut
    let sendBound ← (spIdents.zip sProjs).foldrM (init := sendGuarded) fun (spid, sprj) acc =>
      `(let $spid:ident := $sprj; $acc)
    let sendDecode ← `(match Qed.Proto.decode (α := $sendTupleTy) $payloadBytesVar with
      | Except.error _e2 => Pure.pure (Except.error (Qed.Server.ApiError.badRequest _e2))
      | Except.ok $sTupleVar:ident => $sendBound)
    arms := arms.push (← mkChanArm (Syntax.mkNumLit "2") sendDecode)

  -- 3. `on_leave` (kind = 3)
  let leaveRunTerm ← match hdr.onLeave? with
    | some stmts =>
        let unitTy ← `(Unit)
        let some r ← runSubHandler "onLeave" #[] #[] #[] #[] #[] #[] unitTy true stmts | return none
        `($r >>= fun _lRes => Pure.pure (_lRes.map fun _ => ByteArray.empty))
    | none =>
        `(Pure.pure (Except.ok ByteArray.empty))
  arms := arms.push (← mkChanArm (Syntax.mkNumLit "3")
    (← wrapReqs hdr.reqPropTerms hdr.reqHypIds hdr.reqLabels leaveRunTerm))

  -- 4. Emit client-safe channel helpers (`_Join`, `_key`, `_sub`, `_send`, `_unsub`) & register in `channelRegistry`
  let joinAbbrevId := mkIdentFrom chIdent (srvName ++ chName.appendAfter "_Join")
  elabCommand (← `(command| abbrev $joinAbbrevId : Type := $joinTyTerm))

  let keyId := mkIdentFrom chIdent (srvName ++ chName.appendAfter "_key")
  let paramTupleVal ← liftMacroM <| buildTupleVal (pIdents.map (⟨·.raw⟩))
  elabCommand (← `(command|
    def $keyId $[($pIdents:ident : $pTyTerms:term)]* : String :=
      Qed.wsTopicKey $chLit $paramTupleVal))

  let wireEvTerm : Term ← match hdr.ensId? with
    | some eid =>
        let ensApp ← pIdents.foldlM (init := (eid : Term)) fun acc p => `($acc $p)
        `(Qed.Ensured $(hdr.evTyTerm) ($ensApp))
    | none => pure hdr.evTyTerm

  let subId := mkIdentFrom chIdent (srvName ++ chName.appendAfter "_sub")
  let slotId := mkIdent `slot
  let recId := mkIdent `rec
  let onJoinId := mkIdent `onJoin
  let onMsgId := mkIdent `onMsg
  let onStatusId := mkIdent `onStatus
  let wsPathStr := s!"/_qed/ws/{srvShort}"
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

  let unsubId := mkIdentFrom chIdent (srvName ++ chName.appendAfter "_unsub")
  elabCommand (← `(command|
    def $unsubId {msg : Type} ($slotId:ident : String) : Qed.Cmd msg :=
      Qed.Cmd.wsMuxUnsub $slotId))

  let mut sendHelperConst : Name := .anonymous
  if hasSend then
    let sendId := mkIdentFrom chIdent (srvName ++ chName.appendAfter "_send")
    let sendTupleVal ← liftMacroM <| buildTupleVal (spIdents.map (⟨·.raw⟩))
    elabCommand (← `(command|
      def $sendId {msg : Type} ($slotId:ident : String) $[($spIdents:ident : $spTyTerms:term)]* : Qed.Cmd msg :=
        Qed.Cmd.wsMuxSend $slotId (Qed.Proto.encode $sendTupleVal)))
    sendHelperConst := fullSrvName ++ chName.appendAfter "_send"

  if hasNewErrors (← get).messages priorRep priorUnrep then return none

  modifyEnv fun env => Qed.channelRegistry.addEntry env {
    fullName := fullSrvName ++ chName
    ownerName := fullSrvName
    ownerShort := srvShort
    channelName := chStr
    kind := .fullstack fullSrvName srvShort wsPathStr
    paramNames := pIdents.map (·.getId)
    paramCount := pIdents.size
    paramTypeConsts := hdr.paramTypeConsts
    eventTypeConst := fullSrvName ++ chName.appendAfter "_Event"
    hasJoinSnapshot
    joinTypeConst := fullSrvName ++ chName.appendAfter "_Join"
    hasSend
    sendParamNames := spIdents.map (·.getId)
    sendParamCount := spIdents.size
    sendParamTypeConsts
    sendReqConst := sendReqConst?
    sendReqLabel
    requiresAuth := hdr.requiresAuth
    clientReqConst := hdr.clientReqConst
    clientReqLabel := hdr.clientReqLabel
    hasEnsures := hdr.ensConst?.isSome
    ensPredConst := hdr.ensConst?
    defaultReconnect := hdr.recPolicy
    keyHelperConst := fullSrvName ++ chName.appendAfter "_key"
    subHelperConst := fullSrvName ++ chName.appendAfter "_sub"
    sendHelperConst
    unsubHelperConst := fullSrvName ++ chName.appendAfter "_unsub"
  }
  return some (arms, ← extRootsRef.get)


end Qed.Server
