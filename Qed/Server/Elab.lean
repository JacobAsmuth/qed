import Qed.Server.FnElab
import Qed.Server.Invariant
import Qed.Server.Eval
import Qed.Invariant.State
import Qed.Runtime.Cmd
import Qed.Resource.Basic
import Qed.Ssr
import Qed.Component.Syntax

namespace Qed.Server
open Qed.Lang

syntax (name := qedServerMainCmd) "qedServerMain " ident : command

private structure ParsedChanHeader where
  (chIdent : Lean.Ident) (chName : Lean.Name) (chStr : String)
  (pIdents : Array Lean.Ident) (pTyTerms : Array Lean.Term) (paramNames : Array String) (paramTypeConsts : Array Lean.Name)
  (evTyTerm : Lean.Term) (reqs : LoweredRequires) (ensId? : Option Lean.Ident) (ensConst? : Option Lean.Name) (recPolicy : Qed.Reconnect)
  (onJoin? : Option (Option Lean.Syntax × Array Lean.Syntax))
  (onSend? : Option (Array Lean.Syntax × Array Lean.Syntax × Array Lean.Syntax))
  (onLeave? : Option (Array Lean.Syntax))
  (project? : Option (Lean.Ident × Lean.Term × Lean.Ident) := none) (sig : SrvChanSig)

private structure ParsedSrvEffContract where
  (ref : Lean.Syntax) (guards ensPreds errPreds : Array Lean.Syntax := #[]) (effTags : Array Lean.Name := #[])
  (fails? : Option (Option Nat) := none) (tac? : Option (Lean.TSyntax ``Lean.Parser.Tactic.tacticSeq) := none)

private structure ParsedSrvBlind where
  (ref : Lean.Syntax) (guards targets : Array Lean.Syntax := #[]) (tac? : Option (Lean.TSyntax ``Lean.Parser.Tactic.tacticSeq) := none)

private structure ParsedSrvContracts where
  (requires topEnsures : Array Lean.Syntax := #[]) (topEnsTac? : Option (Lean.TSyntax ``Lean.Parser.Tactic.tacticSeq) := none)
  (effSpecs : Array ParsedSrvEffContract := #[]) (blinds : Array ParsedSrvBlind := #[])

private structure SrvExCtx where
  (c : SrvElabCtx) (isService : Bool) (serviceMethods : Array ServiceMethodInfo)
  (rpcWireMap : Std.HashMap String (Lean.Term × Lean.Term)) (stateTy : Lean.Term) (exNm : Lean.Name)

section ServerFullElab
open Lean Elab Command

/-! ## WebSocket `channel` Header & Body Elaborators -/

@[noinline] private def elabChanProject (chIdent : Ident) (chStr : String) (pIdents : Array Ident) (pTyTerms : Array Term)
    (paramNames : Array String) (evTyTerm : Term) (reqs : LoweredRequires) (ensId? : Option Ident)
    (rawParamStx : Syntax) (optRet? : Option Syntax) (projContracts projStmts : Array Syntax) : SrvElabM (Option (Ident × Term × Ident)) := do
  let c ← read
  let (rIds, rTys, _) ← parseSrvParams s!"`channel {chStr}.project`" "`project` parameter" #[rawParamStx] (reserved := #["result"]) (extraShadow := paramNames)
  let (rawId, rawTyTerm) := (rIds[0]!, rTys[0]!)
  let projRetTy : Term ← match optRet? with | some rt => pure (← liftSrvMacro (lowerSrvType rt false s!"return type of `channel {chStr}.project`")).term | none => pure evTyTerm
  let (projFnId, ctxTy) := (c.fnSubId chIdent "_project", ← runSrvPQ `(Qed.Server.RequestCtx))
  let bodyTerm ← liftM <| Qed.lowerPureFnStmts s!"channel {chStr}.project" projStmts.toList
  elabSrvPure do noUnusedVarsPure (← `(command| def $projFnId ($(c.ctxId):ident : $ctxTy) $[($pIdents:ident : $pTyTerms:term)]* ($rawId:ident : $rawTyTerm) : $evTyTerm := ($bodyTerm : $projRetTy)))
  if (← hasSrvErrors) then return none
  let (allPIds, allPTys, preHyps) := (#[c.ctxId] ++ pIdents ++ #[rawId], #[ctxTy] ++ pTyTerms ++ #[rawTyTerm], reqs.reqHypIds.zip reqs.reqPropTerms)
  liftM <| Qed.elabPureFnContracts projFnId projFnId allPIds allPTys evTyTerm projContracts preHyps
  if let some eid := ensId? then
    let chEnsThmId := c.fnSubId chIdent "_project_channel_ensures"
    elabSrvPure do
      let (ensApp, callT) := (← mkAppTerms eid (pIdents.map (⟨·.raw⟩)), ← mkAppTerms projFnId (allPIds.map (⟨·.raw⟩)))
      let reqBs ← mapPQ preHyps fun (hid, hty) => `(bracketedBinder| ($hid:ident : $hty))
      noUnusedVarsPure (← `(command| theorem $chEnsThmId ($(c.ctxId):ident : $ctxTy) $[($pIdents:ident : $pTyTerms:term)]* ($rawId:ident : $rawTyTerm) $[$reqBs:bracketedBinder]* : $ensApp ($callT) := by qedProveFnEnsures $projFnId $chEnsThmId))
  if (← hasSrvErrors) then return none
  return some (rawId, rawTyTerm, projFnId)

private structure ChanSubAcc where
  (reqExprs ensExprs : Array Syntax := #[]) (recPolicy? : Option Qed.Reconnect := none)
  (onJoin? : Option (Option Syntax × Array Syntax) := none) (onSend? : Option (Array Syntax × Array Syntax × Array Syntax) := none)
  (onLeave? : Option (Array Syntax) := none) (rawProject? : Option (Syntax × Option Syntax × Array Syntax × Array Syntax) := none)

@[noinline] private def parseChanSub (chStr : String) (acc : ChanSubAcc) (sub : Syntax) : SrvElabM ChanSubAcc := do
  match sub.getKind with
  | ``srvRequiresLine => return { acc with reqExprs := acc.reqExprs ++ (sub.getArg 1).getSepArgs }
  | ``srvEnsuresLine  => return { acc with ensExprs := acc.ensExprs ++ (sub.getArg 1).getSepArgs }
  | ``srvChanReconnectClause => return { acc with recPolicy? := ← setOptOnce acc.recPolicy? sub s!"`reconnect` clause in `channel {chStr}`" (liftSrvMacro (Qed.parseReconnectExpr (sub.getArg 1))) }
  | ``srvChanOnJoinClause => return { acc with onJoin? := ← setOptOnce acc.onJoin? sub s!"`on_join` in `channel {chStr}`" (pure (if (sub.getArg 1).getNumArgs == 2 then some ((sub.getArg 1).getArg 1) else none, suiteStmts (sub.getArg 3))) }
  | ``srvChanOnSendClause => return { acc with onSend? := ← setOptOnce acc.onSend? sub s!"`on_send` in `channel {chStr}`" (pure ((sub.getArg 2).getSepArgs, (sub.getArg 5).getArgs.flatMap fun rl => (rl.getArg 1).getSepArgs, suiteStmts (sub.getArg 6))) }
  | ``srvChanOnLeaveClause => return { acc with onLeave? := ← setOptOnce acc.onLeave? sub s!"`on_leave` in `channel {chStr}`" (pure (suiteStmts (sub.getArg 2))) }
  | ``srvChanProjectClause => return { acc with rawProject? := ← setOptOnce acc.rawProject? sub s!"`project` in `channel {chStr}`" (pure (sub.getArg 2, if (sub.getArg 4).getNumArgs == 2 then some ((sub.getArg 4).getArg 1) else none, (sub.getArg 6).getArgs, (sub.getArg 7).getArgs)) }
  | _ => srvErrAt sub s!"unexpected clause in `channel {chStr}`"

@[noinline] private def elabServerChannelHeader (existingChanNames : Array String) (chStx : Syntax) : SrvElabM (Option ParsedChanHeader) := do
  let c ← read; let chIdent : Ident := ⟨chStx.getArg 1⟩; let (chName, chStr) := (chIdent.getId, chIdent.getId.toString)
  if existingChanNames.contains chStr then srvErrAt chIdent s!"duplicate `channel {chStr}` in `server {c.srvName}`"
  let (pIdents, pTyTerms, paramNames) ← parseSrvParams s!"`channel {chStr}`" "channel parameter" (chStx.getArg 3).getSepArgs (reserved := #["event"])
  let evTyTerm := (← liftSrvMacro (lowerSrvType (chStx.getArg 6) false s!"event type of `channel {chStr}`")).term
  let acc ← foldlSrv (if (chStx.getArg 7).getNumArgs == 2 then ((chStx.getArg 7).getArg 1).getArgs else #[]) {} (parseChanSub chStr)
  let paramTypeConsts ← liftM <| elabParamTypeAbbrevs chIdent c.srvName c.fullSrvName chName "_Param_" pTyTerms
  let reqs ← elabRequiresClauses chIdent chName chStr "_hChReq" "_req" paramNames paramNames pIdents pTyTerms acc.reqExprs
  let some ensRes? ← elabEnsuresAbbrev chIdent chStr `event paramNames pIdents pTyTerms evTyTerm acc.ensExprs | return none
  let (ensId?, ensConst?) : Option Ident × Option Name := (ensRes?.map (·.1), ensRes?.map (·.2.1))
  let projectInfo? ← match acc.rawProject? with
    | none => pure none
    | some (rp, oR, pC, pS) => match ← elabChanProject chIdent chStr pIdents pTyTerms paramNames evTyTerm reqs ensId? rp oR pC pS with | some p => pure (some p) | none => return none
  let mkEmitId := c.fnSubId chIdent "_mkEmit"
  let (emitPayloadTy, needEmitEns) := match projectInfo? with | some (_, rawTy, _) => (rawTy, false) | none => (evTyTerm, ensId?.isSome)
  elabSrvPureCmds do
    let evVar := mkIdent `_ev; let paramTupleVal ← buildTupleVal (pIdents.map (⟨·.raw⟩))
    let extraBs ← match ensId?, needEmitEns with
      | some eid, true => pure #[← `(bracketedBinder| (_hEns : $(← mkAppTerms eid ((pIdents.push evVar).map (⟨·.raw⟩)))))] | _, _ => pure #[]
    return #[
      ← `(command| abbrev $(c.fnSubId chIdent "_Event") : Type := $evTyTerm),
      ← noUnusedVarsPure (← `(command| @[inline] def $mkEmitId $[($pIdents:ident : $pTyTerms:term)]* ($evVar:ident : $emitPayloadTy) $[$extraBs:bracketedBinder]* : Qed.Server.WsEmit :=
        { topic := Qed.wsTopicKey $(Syntax.mkStrLit chStr) $paramTupleVal, payload := Qed.Proto.encode $evVar }))]
  if (← hasSrvErrors) then return none
  return some { chIdent, chName, chStr, pIdents, pTyTerms, paramNames, paramTypeConsts, evTyTerm, reqs, ensId?, ensConst?,
                recPolicy := acc.recPolicy?.getD .defaultPolicy, onJoin? := acc.onJoin?, onSend? := acc.onSend?, onLeave? := acc.onLeave?,
                project? := projectInfo?, sig := { name := chStr, mkEmitId, paramCount := pIdents.size, hasEnsures := needEmitEns } }

@[noinline] private def mkChanWsClientSpecPure (c : SrvElabCtx) (hdr : ParsedChanHeader) (hasJoinSnapshot hasSend : Bool)
    (joinTyTerm : Term) (spIdents : Array Ident) (spTyTerms : Array Term) (wsPathStr : String) : PureQuotM WsClientSpec := do
  let (pIdents, pTyTerms, chLit) := (hdr.pIdents, hdr.pTyTerms, Syntax.mkStrLit hdr.chStr)
  let paramTupleVal ← buildTupleVal (pIdents.map (⟨·.raw⟩))
  let wireEvTy : Term ← match hdr.ensId? with | some eid => `(Qed.Ensured $(hdr.evTyTerm) ($(← mkAppTerms eid (pIdents.map (⟨·.raw⟩))))) | none => pure hdr.evTyTerm
  let (slotId, recId, onJoinId, onMsgId, onStatusId) := (mkIdent `slot, mkIdent `rec, mkIdent `onJoin, mkIdent `onMsg, mkIdent `onStatus)
  let mkProtoCb (ty : Term) (onOk : Ident) : PureQuotM Term := mkWsDecodeCb onOk onStatusId fun bs => `(Qed.Proto.decode (α := $ty) $bs)
  let onJoinDec ← if hasJoinSnapshot then mkProtoCb joinTyTerm onJoinId else `(fun _ => $onJoinId ())
  let sendSpec? ← if hasSend then pure (some (spIdents, spTyTerms, ← `(Qed.Cmd.wsMuxSend $slotId (Qed.Proto.encode $(← buildTupleVal (spIdents.map (⟨·.raw⟩))))))) else pure none
  return { refIdent := hdr.chIdent, ownerName := c.srvName, chName := hdr.chName, pIdents, pTyTerms, joinAbbrev? := some joinTyTerm, joinCbTy := joinTyTerm, wireEvTy,
           keyBody := ← `(Qed.wsTopicKey $chLit $paramTupleVal),
           subBody := ← `(Qed.Cmd.wsMuxSub $slotId $(Syntax.mkStrLit wsPathStr) $chLit (Qed.Proto.encode $paramTupleVal) $recId $onJoinDec $(← mkProtoCb wireEvTy onMsgId) $onStatusId),
           unsubBody := ← `(Qed.Cmd.wsMuxUnsub $slotId), sendSpec? }

@[noinline] private def mapRunPure (runT mapFn : Term) : PureQuotM Term := `($runT >>= fun _r => Pure.pure (_r.map $mapFn))
private def wrapWithBeforePure (beforeRun? : Option Term) (body : Term) : PureQuotM Term :=
  match beforeRun? with | none => pure body | some br => `($br >>= fun | Except.error _beforeErr => Pure.pure (Except.error _beforeErr) | Except.ok () => $body)

/-! ## Shared Contract Parser, Extra Contracts & Unified Callable Pipeline -/

private structure ContractGrpAcc where
  (acc : ParsedSrvContracts) (ref? : Option Syntax := none) (tags : Array Name := #[])
  (ens err : Array Syntax := #[]) (fails? : Option (Option Nat) := none) (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none)

private def ContractGrpAcc.flush (g : ContractGrpAcc) (guards : Array Syntax) : ContractGrpAcc :=
  if g.tags.isEmpty && g.ens.isEmpty && g.err.isEmpty && g.fails?.isNone then g
  else { acc := { g.acc with effSpecs := g.acc.effSpecs.push { ref := g.ref?.getD Syntax.missing, guards, effTags := g.tags, ensPreds := g.ens, errPreds := g.err, fails? := g.fails?, tac? := g.tac? } } }

@[noinline] private partial def collectSrvContracts (kindLabel : String) (guards : Array Syntax) (clauses : Array Syntax) (acc0 : ParsedSrvContracts) : CommandElabM ParsedSrvContracts := do
  let gFinal ← foldlCmd clauses ({ acc := acc0 } : ContractGrpAcc) fun g cl => do
    let ref? := g.ref?.orElse fun _ => some cl
    match cl.getKind with
    | ``srvRequiresLine =>
        unless guards.isEmpty do errAt cl s!"`requires` must appear at the top level of {kindLabel}"
        return { g with acc := { g.acc with requires := g.acc.requires ++ (cl.getArg 1).getSepArgs } }
    | ``srvEnsuresLine =>
        let (ps, t?) := ((cl.getArg 1).getSepArgs, Qed.parseOptTacSeq (cl.getArg 2))
        if guards.isEmpty then
          if t?.isSome && g.acc.topEnsTac?.isSome then errAt cl s!"at most one `prove:` / `:= by` block is allowed per {kindLabel}"
          return { g with acc := { g.acc with topEnsures := g.acc.topEnsures ++ ps, topEnsTac? := g.acc.topEnsTac?.orElse fun _ => t? } }
        return { g with ref?, ens := g.ens ++ ps, tac? := g.tac?.orElse fun _ => t? }
    | ``srvEnsuresErrLine => return { g with ref?, err := g.err ++ (cl.getArg 1).getSepArgs, tac? := g.tac?.orElse fun _ => Qed.parseOptTacSeq (cl.getArg 2) }
    | ``srvEnsuresFailsLine =>
        let cOpt := cl.getArg 1
        return { g with ref?, fails? := some (if cOpt.getNumArgs == 1 then some (⟨cOpt.getArg 0⟩ : TSyntax `num).getNat else none), tac? := g.tac?.orElse fun _ => Qed.parseOptTacSeq (cl.getArg 2) }
    | ``srvEffectLine =>
        let tags := (cl.getArg 0).getSepArgs.foldl (init := g.tags) fun ts tag => pushUnique ts (tag.getArg 0).getId.eraseMacroScopes
        return { g with ref?, tags, tac? := g.tac?.orElse fun _ => Qed.parseOptTacSeq (cl.getArg 1) }
    | ``srvBlindToLine => return { g with acc := { g.acc with blinds := g.acc.blinds.push { ref := cl, guards, targets := (cl.getArg 1).getSepArgs, tac? := Qed.parseOptTacSeq (cl.getArg 2) } } }
    | `Qed.Server.srvCIIf => return { acc := ← collectSrvContracts kindLabel (guards ++ (cl.getArg 1).getSepArgs) (cl.getArg 3).getArgs (g.flush guards).acc }
    | _ => errAt cl s!"unexpected contract clause in {kindLabel}"
  return (gFinal.flush guards).acc

private structure EffContractCtx where
  (fnIdent targetId : Ident) (thmBaseLeaf : Name) (fnStr : String)
  (isMonadic isFallible hasState : Bool) (isStepPair hasEmit : Bool := false) (defer : Bool := true)
  (paramIds binderIds : Array Ident) (binderTys : Array Term)
  (callT payloadTerm errTyTerm : Term) (innerOpt? : Option Term) (unfoldIds : Array Ident := #[])

private def effTagField? : Name → Option Name
  | `no_http => some `isHttp | `no_decrypt => some `isDecrypt | `no_crypto => some `isCrypto | `no_db_write => some `isDbWrite | _ => none

private def mkGuardBindersPure (guardTerms : Array Term) : PureQuotM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) :=
  mapIdxPQ guardTerms fun g i => `(bracketedBinder| ($(mkIdent (Name.mkSimple s!"_hIf_{i}")):ident : $g))

@[noinline] private def mkEffPostBodyPure (outVar : Ident) (x : EffContractCtx) (ensTms errTms : Array Term) (fails? : Option (Option Nat)) : PureQuotM (Bool × Term) := do
  let mut parts : Array Term := #[]
  if !ensTms.isEmpty then
    let resId := mkIdent `result; let pLam ← `(fun ($resId:ident : $(x.innerOpt?.getD x.payloadTerm)) => $(← Qed.mkConjBody ensTms (ascribeProp := false)))
    parts := parts.push (← if !x.isFallible then (if x.innerOpt?.isSome then `(∀ _r, $outVar = Option.some _r → $pLam _r) else `($pLam $outVar))
      else mkAppC (if x.innerOpt?.isSome then ``Qed.Server.srvEnsPostOpt else ``Qed.Server.srvEnsPost) #[pLam, outVar])
  if !errTms.isEmpty then
    let errId := mkIdent `err; let errBody ← Qed.mkConjBody errTms (ascribeProp := false)
    parts := parts.push (← mkAppC ``Qed.Server.srvEnsErrPost #[← `(fun ($errId:ident : $(x.errTyTerm)) => let code := ($errId).code; let status := ($errId).code; let message := ($errId).message; $errBody), outVar])
  if let some code? := fails? then
    parts := parts.push (← match code? with | none => mkAppC ``Qed.Server.srvEnsFails #[outVar] | some code => mkAppC ``Qed.Server.srvEnsFailsCode #[Syntax.mkNumLit (toString code), outVar])
  return (parts.isEmpty, ← if parts.isEmpty then pure (mkCIdent ``True : Term) else Qed.mkConjBody parts (ascribeProp := false))

@[noinline] private def mkEffContractCmdPure (c : SrvElabCtx) (x : EffContractCtx) (ec : ParsedSrvEffContract) (idx : Nat)
    (guardTms ensTms errTms : Array Term) : PureQuotM (TSyntax `command) := do
  let (bBs, guardBs, effVar, outVar, fnLit) := (← mkTypedBindersPure x.binderIds x.binderTys, ← mkGuardBindersPure guardTms, mkIdent `_eff, mkIdent `_srvOut, Syntax.mkStrLit x.fnStr)
  let effPred : Term ← if ec.effTags.isEmpty then pure (mkCIdent ``True : Term) else Qed.mkConjBody (← mapPQ ec.effTags fun tn => `(($effVar:ident).$(mkIdent (effTagField? tn |>.getD `isHttp)) = false)) (ascribeProp := false)
  let (noPost, postBody) ← mkEffPostBodyPure outVar x ensTms errTms ec.fails?
  let lblStr := String.intercalate ", " ((ec.effTags.map (·.toString)) ++ (if ensTms.isEmpty then #[] else #["ensures"]) ++
    (if errTms.isEmpty then #[] else #["ensures_error"]) ++ (match ec.fails? with | some none => #["ensures_fails"] | some (some code) => #[s!"ensures_fails {code}"] | none => #[])).toList
  let (thmId, retTy) := (c.subId (x.thmBaseLeaf.appendAfter s!"_contract_{idx + 1}") x.fnIdent, ← if x.isFallible then mkAppC ``Except #[x.errTyTerm, x.payloadTerm] else pure x.payloadTerm)
  if x.isMonadic then
    let allUnfolds := x.unfoldIds ++ c.statefulHelperIds
    let tac ← match ec.tac? with
      | some ts => `(Lean.Parser.Tactic.tacticSeq| qedSrvPrepEffSpec $(x.targetId) [$[$allUnfolds],*]; first | done | ($ts))
      | none    => `(Lean.Parser.Tactic.tacticSeq| qedSrvProveEffSpec $(x.targetId) [$[$allUnfolds],*] $fnLit $(Syntax.mkStrLit lblStr))
    let (sigId, invId) := (mkIdent `_σ, mkIdent `_Inv)
    let (leadBs, invT, stT) ← if x.hasState then pure (#[], (c.stateInvId : Term), (c.stateId : Term))
      else pure (#[← `(bracketedBinder| {$sigId:ident : Type}), ← `(bracketedBinder| {$invId:ident : $sigId → Prop})], (invId : Term), (sigId : Term))
    let goal ← mkAppC ``Qed.Server.ProgEffSpec #[invT, mkCIdent ``True, ← `(fun _ _ => True),
      ← `(fun ($effVar:ident : Qed.Server.ServerEffect) => $effPred), ← `(fun ($outVar:ident : $retTy) => $postBody),
      ← mkAscribePure x.callT (← mkAppC ``Qed.Server.ThreadProg #[stT, ← `(_)])]
    mkSrvThmPure thmId (leadBs ++ bBs ++ guardBs) goal tac true
  else if noPost then
    noUnusedVarsPure (← `(command| theorem $thmId $[$bBs:bracketedBinder]* $[$guardBs:bracketedBinder]* : True := True.intro))
  else
    let targetOut ← if x.isStepPair then (if x.hasEmit then `(($(x.callT)).2.1) else `(($(x.callT)).2)) else pure x.callT
    let tac ← mkEnsProofTacPure none (#[x.targetId] ++ x.unfoldIds ++ (if x.hasState then #[c.stateInvId] else #[])) fnLit lblStr ec.tac?
    let (preBs, postBs) ← if x.isStepPair then let s0Id := mkIdent `_s0; pure (#[← `(bracketedBinder| ($s0Id:ident : $(c.stateId)))], #[← `(bracketedBinder| (_hInv : $(c.stateInvId) $s0Id))]) else pure (#[], #[])
    mkSrvThmPure thmId (preBs ++ bBs ++ postBs ++ guardBs) (← mkLetBindTerm outVar.raw (some retTy) targetOut postBody) tac true

@[noinline] private def elabSrvExtraContracts (x : EffContractCtx) (contracts : ParsedSrvContracts) : SrvElabM Unit := do
  let c ← read; let emit (cmd : Command) := if x.defer then deferSrvCmd cmd else elabSrvCmd cmd
  let lowerG (s : Syntax) : CommandElabM Term := liftMacroCmd (lowerSimpleQedExpr .propInv s)
  foldlSrv contracts.effSpecs.zipIdx () fun _ (ec, idx) => do
    if let some tn := ec.effTags.find? fun t => (effTagField? t).isNone then srvErrAt ec.ref s!"unknown effect constraint `{tn}`"
    if !ec.errPreds.isEmpty && !x.isFallible then srvErrAt ec.ref s!"`ensures_error` requires a fallible (`T!`) {x.fnStr}"
    if ec.fails?.isSome && !x.isFallible then srvErrAt ec.ref s!"`ensures_fails` requires a fallible (`T!`) {x.fnStr}"
    let (gTms, eTms, erTms) ← liftM do return (← mapCmd ec.guards lowerG, ← mapCmd ec.ensPreds lowerG, ← mapCmd ec.errPreds lowerG)
    emit (← runSrvPQ (mkEffContractCmdPure c x ec idx gTms eTms erTms))
  let paramNames := x.paramIds.map (·.getId.eraseMacroScopes)
  foldlSrv contracts.blinds.zipIdx () fun _ (bl, idx) => do
    let thmId := c.subId (x.thmBaseLeaf.appendAfter s!"_blindTo_{idx + 1}") x.fnIdent
    let (guardTms, parsedTgts) ← liftM do return (← mapCmd bl.guards lowerG, ← mapCmd bl.targets (Qed.Verify.Core.parseBlindTarget · (includeGot := false)))
    let (freshVars, lhsArgs, rhsArgs) ← liftM <| Qed.Verify.Core.buildBlindToArgs parsedTgts paramNames x.binderIds x.binderTys (some x.fnStr)
    let sigId := mkIdent `_σ
    let (lhsCall, rhsCall) ← runSrvPQ do
      if x.isMonadic && !x.hasState then
        let tpTy ← mkAppC ``Qed.Server.ThreadProg #[sigId, ← `(_)]
        return (← mkAscribePure (← mkAppTermsPure x.targetId lhsArgs) tpTy, ← mkAscribePure (← mkAppTermsPure x.targetId rhsArgs) tpTy)
      else if x.isStepPair then let s0Id := mkIdent `_s0; return (← `($(x.targetId) $s0Id $lhsArgs*), ← `($(x.targetId) $s0Id $rhsArgs*))
      else return (← mkAppTermsPure x.targetId lhsArgs, ← mkAppTermsPure x.targetId rhsArgs)
    let eqProp ← liftM <| Qed.Verify.Core.mkBlindToEqProp freshVars lhsCall rhsCall
    emit (← runSrvPQ do
      let proofTac ← match bl.tac? with | some ts => pure ts | none => `(Lean.Parser.Tactic.tacticSeq| qedProveBlindTo $(x.targetId) $thmId $(Syntax.mkStrLit x.fnStr))
      let leadBs ← if x.isMonadic && !x.hasState then pure #[← `(bracketedBinder| {$sigId:ident : Type})]
        else if x.isStepPair then pure #[← `(bracketedBinder| ($(mkIdent `_s0):ident : $(c.stateId)))] else pure #[]
      mkSrvThmPure thmId (leadBs ++ (← mkTypedBindersPure x.binderIds x.binderTys) ++ (← mkGuardBindersPure guardTms)) eqProp proofTac true)

private def mkEnsPostGoalPure (ensId : Ident) (pTerms : Array Term) (outT : Term) (isFallible isOpt : Bool) : PureQuotM Term := do
  let a ← mkAppTermsPure ensId pTerms
  if isFallible then mkAppC (if isOpt then ``Qed.Server.srvEnsPostOpt else ``Qed.Server.srvEnsPost) #[a, outT]
  else if isOpt then `(∀ _r, $outT = Option.some _r → $a _r) else `($a ($outT))

private def mkFnEnsSpec? (ensRes? : Option (Ident × Name × String)) (pTerms : Array Term) (isOpt : Bool)
    (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none) : Option FnEnsSpec :=
  ensRes?.map fun (ensId, _, labelStr) => { ensId, labelStr, tac?, postFn := fun outT => mkEnsPostGoalPure ensId pTerms outT true isOpt }

private def checkReadOnlyDecl (ref : Ident) (kindLabel fnStr : String) (declaredReadOnly mutatesState dbWrite hasEmit hasCookieOp : Bool) : SrvElabM Unit := do
  if !declaredReadOnly then return
  let reasons := (#[(mutatesState, "mutates server state"), (dbWrite, "performs a database write"), (hasEmit, "emits on a WebSocket channel"), (hasCookieOp, "sets or clears cookies")].filter (·.1)).map (·.2)
  unless reasons.isEmpty do srvErrAt ref s!"`read_only {kindLabel} {fnStr}` is not read-only: it {String.intercalate ", " reasons.toList}"

private structure CallableOpts where
  (thmBaseLeaf : Name := .anonymous) (errRef? : Option Syntax := none) (missingRetLabel : String := "")
  (isUnit normalizeAtomic isHttpRoute isStreamRoute declaredReadOnly : Bool := false)
  (allowUnwrap hasFallible includeDbs : Bool := true)
  (forceAsync? allowAwait? : Option Bool := none) (innerOpt? domainErrTy? ctxArg? : Option Term := none)
  (locals : Array String := #[]) (paramIds extraBinderIds : Array Ident := #[]) (extraBinderTys extraCallArgs : Array Term := #[])
  (reqs? : Option LoweredRequires := none) (ensSpec? : Option FnEnsSpec := none) (contracts? : Option ParsedSrvContracts := none)
  (roKindLabel : String := "rpc") (txParams : Array (Ident × DatabaseInfo) := #[])

@[noinline] private def elabSrvCallable (fnIdent : Ident) (fnStr : String) (rawStmts : Array Syntax) (payloadTerm errTyTerm : Term) (o : CallableOpts := {}) : SrvElabM (Option ElabHandlerRes) := do
  let c ← read
  let norm := if o.normalizeAtomic && !blockHasAwait rawStmts && rawStmts.size == 1 && rawStmts[0]!.getKind == ``qedStmtAtomic then suiteStmts rawStmts[0]![2] else rawStmts
  let body := if o.isUnit then ensureUnitReturn fnIdent norm else norm
  if !o.isUnit && !blockAlwaysReturns body then srvErrAt (o.errRef?.getD fnIdent.raw) s!"missing `return` on fallthrough path of {if o.missingRetLabel.isEmpty then s!"`{fnStr}`" else o.missingRetLabel}"
  let isAsync := o.forceAsync?.getD (blockHasAwait body)
  let (locs, bIds, bTys, cArgs) := match o.reqs? with
    | none => (o.locals, o.extraBinderIds, o.extraBinderTys, o.extraCallArgs)
    | some r => (o.locals ++ r.extraLocals, o.extraBinderIds ++ r.allBinderIds, o.extraBinderTys ++ r.allBinderTys, o.extraCallArgs ++ r.allBinderArgs)
  let baseCtx ← mkBaseLowerCtx fnStr locs (o.allowAwait?.getD isAsync) o.allowUnwrap o.hasFallible o.innerOpt? o.domainErrTy? o.isHttpRoute o.isStreamRoute o.includeDbs (txParams := o.txParams)
  let some hRes ← elabServerHandler isAsync fnStr fnIdent bIds bTys cArgs payloadTerm errTyTerm baseCtx body o.ensSpec? o.ctxArg? | return none
  checkReadOnlyDecl fnIdent o.roKindLabel fnStr o.declaredReadOnly hRes.mutatesState hRes.dbWrite hRes.hasEmit hRes.hasCookieOp
  if let some cs := o.contracts? then
    let callT ← runSrvPQ do
      let head : Term ← if hRes.isAsync then pure (hRes.targetId : Term) else `($(hRes.targetId) $(mkIdent `_s0))
      mkAppTermsPure head (hRes.allBinderIds.map (⟨·.raw⟩))
    let ecCtx : EffContractCtx := {
      fnIdent, targetId := hRes.targetId, thmBaseLeaf := if o.thmBaseLeaf == .anonymous then fnIdent.getId else o.thmBaseLeaf, fnStr,
      isMonadic := hRes.isAsync, isFallible := true, hasState := c.hasState, isStepPair := !hRes.isAsync, hasEmit := hRes.hasEmit,
      paramIds := o.paramIds, binderIds := hRes.allBinderIds, binderTys := hRes.allBinderTys, callT, payloadTerm, errTyTerm, innerOpt? := o.innerOpt? }
    elabSrvExtraContracts ecCtx cs
  return some hRes

/-! ## Channel Body, RPC, HTTP Route, Job, Before & Auth Hook Elaborators -/

@[noinline] private def mkChanArmsPure (c : SrvElabCtx) (hdr : ParsedChanHeader) (paramTupleTy : Term) (pProjs : Array Term)
    (beforeRun? : Option Term) (joinSpec : Option (Term × Bool)) (sendSpec? : Option (Ident × Term × Array Ident × Array Term × LoweredRequires × Term))
    (leaveRun? : Option Term) : PureQuotM (Array (TSyntax ``Lean.Parser.Term.matchAltExpr) × Option (TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let chLit := Syntax.mkStrLit hdr.chStr
  let mkArm (kindStr : String) (bodyInParams : Term) : PureQuotM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
    `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkNumLit kindStr):num, $chLit => $(← mkProtoDecodeBindPure (mkIdent `wsParams) (mkIdent `_chParams) paramTupleTy hdr.pIdents pProjs bodyInParams))
  let (emptyFn, okEmpty) := (← `(fun _ => ByteArray.empty), ← mkPureOk (mkCIdent ``ByteArray.empty))
  let joinRun ← match joinSpec with | some (r, true) => mapRunPure r (mkCIdent ``Qed.Proto.encode) | some (r, false) => mapRunPure r emptyFn | none => pure okEmpty
  let joinArm ← mkArm "1" (← wrapWithBeforePure beforeRun? (← wrapAuthAndReqsPure hdr.reqs joinRun))
  let sendArms ← match sendSpec? with
    | none => pure #[]
    | some (sTupleVar, sendTupleTy, spIds, sProjs, sReqs, sr) =>
        let sGuarded ← wrapWithBeforePure beforeRun? (← wrapAuthAndReqsPure hdr.reqs (← wrapReqsPure sReqs.reqPropTerms sReqs.reqHypIds sReqs.reqLabels (← mapRunPure sr emptyFn)))
        pure #[← mkArm "2" (← mkProtoDecodeBindPure (mkIdent `wsPayload) sTupleVar sendTupleTy spIds sProjs sGuarded)]
  let leaveArm ← mkArm "3" (← wrapAuthAndReqsPure hdr.reqs (← match leaveRun? with | some r => mapRunPure r emptyFn | none => pure okEmpty))
  let projArm? ← match hdr.project? with
    | none => pure none
    | some (_, rawTyTerm, projFnId) =>
        let (wsPId, wsPayId, chPId, rawVar) := (mkIdent `wsParams, mkIdent `wsPayload, mkIdent `_chParams, mkIdent `_rawVal)
        let projCall ← mkAppTermsPure projFnId (#[⟨c.ctxId.raw⟩] ++ pProjs ++ #[⟨rawVar.raw⟩])
        some <$> `(Lean.Parser.Term.matchAltExpr| | $chLit =>
          match Qed.Proto.decode (α := $paramTupleTy) $wsPId:ident, Qed.Proto.decode (α := $rawTyTerm) $wsPayId:ident with
          | Except.ok $chPId:ident, Except.ok $rawVar:ident => Qed.Server.WsProjectOut.send (Qed.Proto.encode ($projCall))
          | _, _ => Qed.Server.WsProjectOut.drop)
  return (#[joinArm] ++ sendArms ++ #[leaveArm], projArm?)

@[noinline] private def elabChanSub (hdr : ParsedChanHeader) (pProjs : Array Term) (errTyTerm : Term) (suf : String)
    (eIds : Array Ident) (eTys eProjs : Array Term) (eReqIds : Array Ident) (eReqTys : Array Term) (retTy : Term) (isUnit : Bool) (rawStmts : Array Syntax) : SrvElabM (Option Term) :=
  (·.map (·.runExpr)) <$> elabSrvCallable (mkIdentFrom hdr.chIdent (hdr.chName.appendAfter s!"_{suf}")) s!"{hdr.chStr}_{suf}" rawStmts retTy errTyTerm {
    thmBaseLeaf := hdr.chName, errRef? := some hdr.chIdent.raw, missingRetLabel := s!"`{hdr.chStr}.{suf}`", isUnit, normalizeAtomic := true, includeDbs := false,
    locals := hdr.paramNames ++ hdr.reqs.extraLocals ++ eIds.map (·.getId.toString),
    extraBinderIds := hdr.pIdents ++ eIds ++ hdr.reqs.allBinderIds ++ eReqIds,
    extraBinderTys := hdr.pTyTerms ++ eTys ++ hdr.reqs.allBinderTys ++ eReqTys,
    extraCallArgs := pProjs ++ eProjs ++ hdr.reqs.allBinderArgs ++ eReqIds.map (⟨·.raw⟩) }

@[noinline] private def elabServerChannelBody (hdr : ParsedChanHeader) (beforeRun? : Option Term := none) :
    SrvElabM (Option (Array (TSyntax ``Lean.Parser.Term.matchAltExpr) × Option (TSyntax ``Lean.Parser.Term.matchAltExpr))) := do
  let c ← read; let (errTyTerm, unitTy) := (mkCIdent ``Qed.Server.ApiError, mkCIdent ``Unit)
  let paramTupleTy ← liftSrvMacro (buildProdType hdr.pTyTerms); let pProjs ← runSrvPQ (extractTupleProjectionsPure (mkIdent `_chParams) hdr.pTyTerms.size)
  let (hasJoinSnapshot, joinTyTerm, joinSpec) ← match hdr.onJoin? with
    | none => pure (false, (unitTy : Term), none)
    | some (snapTyStx?, stmts) =>
        let (hasSnap, jt) : Bool × Term ← match snapTyStx? with
          | some stx => pure (true, (← liftSrvMacro (lowerSrvType stx false s!"`on_join` return type of `channel {hdr.chStr}`")).term)
          | none => pure (false, unitTy)
        let some r ← elabChanSub hdr pProjs errTyTerm "onJoin" #[] #[] #[] #[] #[] jt (!hasSnap) stmts | return none
        pure (hasSnap, jt, some (r, hasSnap))
  let (hasSend, spIds, spTys, sendParamTypeConsts, sendReqConst?, sendReqLabel, sendSpec?) ← match hdr.onSend? with
    | none => pure (false, #[], #[], #[], none, "", none)
    | some (rawSParams, rawSReqs, sBody) =>
        let (spIds, spTys, spNames) ← parseSrvParams s!"`channel {hdr.chStr}`" "`on_send` parameter" rawSParams (extraShadow := hdr.paramNames ++ hdr.reqs.extraLocals)
        let sptc ← liftM <| elabParamTypeAbbrevs hdr.chIdent c.srvName c.fullSrvName hdr.chName "_SendParam_" spTys
        let sReqs ← elabRequiresClauses hdr.chIdent hdr.chName s!"{hdr.chStr}.on_send" "_hSReq" "_send_req"
          (hdr.paramNames ++ hdr.reqs.extraLocals ++ spNames) spNames spIds spTys rawSReqs (excludedClientVars := hdr.paramNames ++ hdr.reqs.extraLocals) (trackAuth := false)
        let sendTupleTy ← liftSrvMacro (buildProdType spTys); let sTupleVar := mkIdent `_chSendVal; let sProjs ← runSrvPQ (extractTupleProjectionsPure sTupleVar spTys.size)
        let some sr ← elabChanSub hdr pProjs errTyTerm "onSend" spIds spTys sProjs sReqs.reqHypIds sReqs.reqPropTerms unitTy true sBody | return none
        pure (true, spIds, spTys, sptc, sReqs.clientReqConst?, sReqs.clientReqLabel, some (sTupleVar, sendTupleTy, spIds, sProjs, sReqs, sr))
  let leaveRun? ← match hdr.onLeave? with
    | none => pure none
    | some stmts => match ← elabChanSub hdr pProjs errTyTerm "onLeave" #[] #[] #[] #[] #[] unitTy true stmts with | some r => pure (some r) | none => return none
  let (wsArms, projArm?) ← runSrvPQ (mkChanArmsPure c hdr paramTupleTy pProjs beforeRun? joinSpec sendSpec? leaveRun?)
  let wsPathStr := s!"/_qed/ws/{c.srvName.toString}"
  liftM <| elabWsClientCommon (← runSrvPQ (mkChanWsClientSpecPure c hdr hasJoinSnapshot hasSend joinTyTerm spIds spTys wsPathStr))
  if (← hasSrvErrors) then return none
  modifyEnv fun env => Qed.channelRegistry.addEntry env {
    ChannelInfo.mkDefault c.fullSrvName c.srvName.toString hdr.chName (.fullstack c.fullSrvName c.srvName.toString wsPathStr) (hdr.pIdents.map (·.getId)) hdr.paramTypeConsts hdr.recPolicy with
    hasJoinSnapshot, joinTypeConst := c.fullSrvName ++ hdr.chName.appendAfter "_Join", hasSend, sendParamCount := spIds.size, sendParamTypeConsts,
    sendReqConst := sendReqConst?, sendReqLabel, requiresAuth := hdr.reqs.requiresAuth, clientReqConst := hdr.reqs.clientReqConst?,
    clientReqLabel := hdr.reqs.clientReqLabel, hasEnsures := hdr.ensConst?.isSome, ensPredConst := hdr.ensConst?,
    sendHelperConst := if hasSend then c.fullSrvName ++ hdr.chName.appendAfter "_send" else .anonymous }
  return some (wsArms, projArm?)

@[noinline] private def elabFnClientStubs (fnIdent : Ident) (fnStr : String) (pIdents : Array Ident) (pTyTerms : Array Term)
    (reqTupleTy payloadTerm : Term) (innerOpt? : Option Term) (errTypeId? : Option Ident) (ensSpec? : Option FnEnsSpec)
    (reqs : LoweredRequires) (doc? : Option (TSyntax ``Lean.Parser.Command.docComment) := none) : SrvElabM (Array Name) := do
  let c ← read; let paramTypeConsts ← liftM <| elabParamTypeAbbrevs fnIdent c.srvName c.fullSrvName fnIdent.getId "_Param_" pTyTerms
  elabSrvPureCmds do
    let (pTerms, pBs) := (pIdents.map (⟨·.raw⟩), ← mkTypedBindersPure pIdents pTyTerms)
    let ensPayload : Term ← match ensSpec? with
      | some ens => let a ← mkAppTermsPure ens.ensId pTerms; match innerOpt? with | some it => mkAppC ``Option #[← mkAppC ``Qed.Ensured #[it, a]] | none => mkAppC ``Qed.Ensured #[payloadTerm, a]
      | none => pure payloadTerm
    let wireRespT : Term ← match errTypeId? with | some e => mkAppC ``Except #[← mkAppC ``Qed.RpcDomainError #[e], ensPayload] | none => pure ensPayload
    let outcomeT : Term ← match errTypeId? with | some e => mkAppC ``Qed.RpcOutcome #[e, ensPayload] | none => mkAppC ``Qed.RpcSimpleOutcome #[ensPayload]
    let outBs := if ensSpec?.isSome then pBs else #[]
    let (rawRpcId, outcomeId, pubFnId) := (c.subId (Name.mkSimple s!"_rpc_{fnStr}") fnIdent, c.fnSubId fnIdent "_Outcome", c.subId fnIdent.getId fnIdent)
    let reqBs ← match reqs.clientReqId? with | some reqId => pure #[← `(bracketedBinder| (_hReq : $(← mkAppTermsPure reqId pTerms) := by qedProveRpcReq))] | none => pure #[]
    let (pTupleVal, rawCall) := (← buildTupleValPure pTerms, ← mkAppTermsPure rawRpcId pTerms)
    return #[
      ← noUnusedVarsPure (← `(command| abbrev $outcomeId $[$outBs:bracketedBinder]* : Type := $outcomeT)),
      ← `(command| def $rawRpcId {msg cb : Type} $[$pBs:bracketedBinder]* (onDone : cb) [Qed.RpcCallback $wireRespT msg cb] : Qed.Cmd msg :=
          Qed.Cmd.rpc (req := $reqTupleTy) (resp := $wireRespT) $(Syntax.mkStrLit s!"/_qed/rpc/{c.srvName.toString}/{fnStr}") $pTupleVal (Qed.RpcCallback.adapt (α := $wireRespT) onDone)),
      ← noUnusedVarsPure (← `(command| $[$doc?:docComment]? def $pubFnId {msg cb : Type} $[$pBs:bracketedBinder]* (onDone : cb) [Qed.RpcCallback $wireRespT msg cb] $[$reqBs]* : Qed.Cmd msg := $rawCall onDone))]
  return paramTypeConsts

@[noinline] private def mkJobTermsPure (c : SrvElabCtx) (jobIdent : Ident) (jobStr : String) (intervalMs : Nat)
    (returnsBool isAsyncJob : Bool) (hRes : ElabHandlerRes) (callArgs : Array Term) : PureQuotM (Term × Option Term) := do
  let (runExpr, isRO, hasEmit) := (hRes.runExpr, !hRes.mutatesState, hRes.hasEmit)
  let proofExpr? : Option Term ← if !c.hasState then pure none else do
    let invThmId := c.fnSubId jobIdent "_inv"
    if isAsyncJob then some <$> mkAppTermsPure invThmId callArgs
    else
      let (wild, emitCont) := (← `(_), ← `(fun _ => Qed.Server.ProgSpec.safeIO_bind _ fun _ => Qed.Server.ProgSpec.pure_class _ trivial))
      let presFn ← if isRO then `(fun _ _h => _h) else `(fun _s _h => $(← mkAppTermsPure (← `($invThmId _s)) callArgs) _h)
      let fnName := match isRO, hasEmit with
        | true, true => ``Qed.Server.ProgSpec.runAtomicRead_bind_val | true, false => ``Qed.Server.ProgSpec.runAtomicRead
        | false, true => ``Qed.Server.ProgSpec.runAtomic_bind_val | false, false => ``Qed.Server.ProgSpec.runAtomic
      some <$> if hasEmit then mkAppC fnName #[wild, emitCont, presFn] else do mkAppC fnName #[wild, presFn, ← `(fun _ _ => trivial)]
  let (unitRun, unitPf?) ← if returnsBool then
      pure (← mapRunPure runExpr (← `(fun _ => ())),
            ← match proofExpr? with | some pf => some <$> mkAppC ``Qed.Server.ProgSpec.bind #[pf, ← `(fun _ _ => Qed.Server.ProgSpec.pure_class _ trivial)] | none => pure none)
    else pure (runExpr, proofExpr?)
  let (wrappedRun, wrappedPf?) ← wrapWithEnvDeclsPure c.envDecls unitRun unitPf?
  let stTy : Term := if c.hasState then (c.stateId : Term) else mkCIdent ``Unit
  let mkJobLam (body : Term) : PureQuotM Term := `(fun {m} [Monad m] [Qed.Server.MonadServer m] [Qed.Server.MonadAtomic $stTy m] => $body)
  let workOpt ← mkOptTermPure (← if returnsBool then some <$> mkJobLam (← wrapWithEnvDeclsPure c.envDecls runExpr none).1 else pure none)
  let jobMeta ← mkAppC ``Qed.Server.JobMeta.mk #[Syntax.mkStrLit jobStr, Syntax.mkNumLit (toString intervalMs), ← mkAppC ``Nat.zero_lt_succ #[← `(_)]]
  let jobTerm ← mkAscribePure (← mkAppC ``Qed.Server.ServerJob.mk #[jobMeta, ← mkJobLam wrappedRun, workOpt]) (← mkAppC ``Qed.Server.ServerJob #[stTy])
  return (jobTerm, ← match wrappedPf? with | some pf => some <$> `(Qed.Server.VerifiedJob.mk (σ := $stTy) (Inv := $(c.stateInvId)) $jobTerm $pf) | none => pure none)

@[noinline] private def elabOneServerJob (existingMethods : Array ServerMethodInfo) (errTyTerm emptyCtx : Term) (callArgs : Array Term)
    (acc : Array String × Array Term × Array Term) (jc : Syntax) : SrvElabM (Option (Array String × Array Term × Array Term)) := do
  let (jobNames, rtJobs, vJobs) := acc; let c ← read; let jobIdent : Ident := ⟨jc.getArg 3⟩; let jobStr := jobIdent.getId.toString
  if existingMethods.any (·.name == jobStr) || jobNames.contains jobStr then srvErrAt jobIdent s!"duplicate job or method name `{jobStr}` in `server {c.srvName}`"
  let n := (⟨jc.getArg 1⟩ : TSyntax `num).getNat; let unitStr := (jc.getArg 2).getId.eraseMacroScopes.toString
  let unit ← match unitStr with
    | "ms" => pure DurationUnit.ms | "s" => pure DurationUnit.s | "m" => pure DurationUnit.m | "h" => pure DurationUnit.h
    | _ => srvErrAt (jc.getArg 2) s!"unknown duration unit `{unitStr}` in `every {n}{unitStr} {jobStr}`; supported units are `ms`, `s`, `m`, `h`"
  let intervalMs := durationToMs n unit
  if intervalMs == 0 then srvErrAt (jc.getArg 1) s!"background job `{jobStr}` interval must be positive (got `{n}{unitStr}`)"
  let optRet := jc.getArg 4
  let returnsBool ← if optRet.getNumArgs == 2 then do
      let retTy ← liftSrvMacro (lowerSrvType (optRet.getArg 1) true s!"return type of job `{jobStr}`")
      unless (retTy.mods.filter (· != .fallible)).isEmpty && (retTy.baseName == `Bool || retTy.baseName == `Unit) do srvErrAt (optRet.getArg 1) s!"`every` job `{jobStr}` return type must be `Bool` (or omitted for `Unit`)"
      pure (retTy.baseName == `Bool)
    else pure false
  let contracts ← liftM <| collectSrvContracts s!"job `{jobStr}`" #[] (jc.getArg 6).getArgs {}
  unless contracts.requires.isEmpty do srvErrAt jobIdent s!"`requires` is not supported on background job `{jobStr}`"
  unless contracts.blinds.isEmpty do srvErrAt jobIdent s!"`blindTo` is not supported on background job `{jobStr}`"
  let rawBodyStmts := suiteStmts (jc.getArg 7); let payloadTerm : Term := mkCIdent (if returnsBool then ``Bool else ``Unit)
  let some ensRes? ← elabEnsuresAbbrev jobIdent s!"job `{jobStr}`" `result #[] #[] #[] payloadTerm contracts.topEnsures | return none
  let isAsyncJob := c.hasState && (blockHasAwait rawBodyStmts || blockHasAtomic rawBodyStmts)
  let some hRes ← elabSrvCallable jobIdent jobStr rawBodyStmts payloadTerm errTyTerm {
    missingRetLabel := s!"`-> Bool` job `{jobStr}`", isUnit := !returnsBool, forceAsync? := some isAsyncJob,
    ensSpec? := mkFnEnsSpec? ensRes? #[] false contracts.topEnsTac?, contracts? := some contracts, ctxArg? := some emptyCtx } | return none
  let (jt, vjt?) ← runSrvPQ (mkJobTermsPure c jobIdent jobStr intervalMs returnsBool isAsyncJob hRes callArgs)
  return some (jobNames.push jobStr, rtJobs.push jt, vjt?.elim vJobs vJobs.push)

@[noinline] private def elabServerJobs (existingMethods : Array ServerMethodInfo) (jobClauses : Array Syntax) : SrvElabM (Option (Array String)) := do
  if jobClauses.isEmpty then return some #[]
  let c ← read; let (errTyTerm, emptyCtx, stTy) ← runSrvPQ do return (mkCIdent ``Qed.Server.ApiError, ← `(({} : Qed.Server.RequestCtx)), if c.hasState then (c.stateId : Term) else mkCIdent ``Unit)
  let some (jobNames, rtJobs, vJobs) ← foldOptSrv jobClauses (#[], #[], #[]) (elabOneServerJob existingMethods errTyTerm emptyCtx (c.envIdents.map (⟨·.raw⟩) ++ #[emptyCtx])) | return none
  elabSrvPureCmds do return #[
    ← mkStrListDefPure (c.subId `jobNames) jobNames,
    ← mkDefValPure (c.subId `jobs) #[] (← mkAppC ``Array #[← mkAppC ``Qed.Server.ServerJob #[stTy]]) (← mkArrLitPure rtJobs)]
  if c.hasState then deferSrvPure do mkDefValPure (c.subId `verifiedJobs) #[] (← mkAppC ``Array #[← mkAppC ``Qed.Server.VerifiedJob #[c.stateId, c.stateInvId]]) (← mkArrLitPure vJobs)
  return some jobNames

/-! ## Helper & Service `fn` Elaborator -/

private structure FnElabInfo where
  (isService declaredReadOnly isFallible takesCtx : Bool) (doc? : Option (TSyntax ``Lean.Parser.Command.docComment))
  (fnIdent : Ident) (defLeaf : Name) (pp : ParsedFnParams) (payloadTerm errTyTerm : Term) (innerOpt? : Option Term)
  (contracts : ParsedSrvContracts) (reqs : LoweredRequires) (ensRes? : Option (Ident × Name × String))
  (usedEnvs : Array ParsedEnvDecl) (thmBinderIds : Array Ident) (thmBinderTys : Array Term)
  (allDefBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (baseCtx : LowerCtx) (bodyStmts : Array Syntax)

private def FnElabInfo.fnStr (i : FnElabInfo) : String := i.fnIdent.getId.toString
private def FnElabInfo.defId (i : FnElabInfo) (c : SrvElabCtx) : Ident := c.subId i.defLeaf i.fnIdent
private def FnElabInfo.mkRes (i : FnElabInfo) (c : SrvElabCtx) (mon fal tAtom mutS dbW hasCk : Bool) (shIds : Array Ident := #[]) :
    Option ServiceMethodInfo × SrvHelperSig × Array Ident :=
  let (n, fnStr) := (i.pp.idents.size, i.fnStr)
  (if !i.isService then none else some { name := fnStr, defConst := c.fullSrvName ++ i.defLeaf, minParamCount := i.pp.minParamCount, paramCount := n, isMonadic := mon, isFallible := fal, takesCtx := i.takesCtx, dbWrite := dbW, hasCookieOp := hasCk, hasEnsures := i.ensRes?.isSome },
   { name := fnStr, defId := i.defId c, minParamCount := i.pp.minParamCount, paramCount := n, isMonadic := mon, isFallible := fal, takesAtomic := tAtom, takesEnvs := !i.isService, takesCtx := i.takesCtx, mutatesState := mutS, dbWrite := dbW, hasCookieOp := hasCk }, shIds)

@[noinline] private def emitFnDefAndProofs (info : FnElabInfo) (isMonadic outIsFallible : Bool) (retTy bodyTerm : Term) : SrvElabM Bool := do
  let c ← read; let (doc?, defId, allBs, bIds, bTys) := (info.doc?, info.defId c, info.allDefBinders, info.thmBinderIds, info.thmBinderTys)
  elabSrvPure do
    if isMonadic then let mId := mkIdent `m; noUnusedVarsPure (← `(command| $[$doc?:docComment]? @[noinline, nospecialize] def $defId {$mId:ident : Type → Type} [Monad $mId] [Qed.Server.MonadServer $mId] $[$allBs:bracketedBinder]* : $mId $retTy := $bodyTerm))
    else noUnusedVarsPure (← `(command| $[$doc?:docComment]? @[noinline] def $defId $[$allBs:bracketedBinder]* : $retTy := $bodyTerm))
  if (← hasSrvErrors) then return false
  let (callT, immCmds, defCmd?) ← runSrvPQ do
    let (thmArgs, bBs, pTerms, ensThmId) := (bIds.map (⟨·.raw⟩), ← mkTypedBindersPure bIds bTys, info.pp.idents.map (⟨·.raw⟩), c.subId (info.defLeaf.appendAfter "_ensures") info.fnIdent)
    if !isMonadic then
      let callT ← mkAppTermsPure defId thmArgs
      let ensCmd? ← match info.ensRes? with
        | none => pure none
        | some (ensId, _, lbl) => some <$> mkSrvThmPure ensThmId bBs (← mkEnsPostGoalPure ensId pTerms callT outIsFallible info.innerOpt?.isSome) (← mkEnsProofTacPure none #[defId, ensId] (Syntax.mkStrLit info.fnStr) lbl info.contracts.topEnsTac?)
      return (callT, #[], ensCmd?)
    let (mId, outVar, sigId, invId, noAtomId) := (mkIdent `m, mkIdent `_srvOut, mkIdent `_σ, mkIdent `_Inv, c.subId (info.defLeaf.appendAfter "_noAtomic") info.fnIdent)
    let (callT, sigB, noAtomApp) := (← `($defId ($mId := Qed.Server.ThreadProg $sigId) $thmArgs*), ← `(bracketedBinder| {$sigId:ident : Type}), ← mkAppTermsPure noAtomId thmArgs)
    let ensCmds ← match info.ensRes? with
      | none => pure #[]
      | some (ensId, _, lbl) =>
          let (invB, postLam) := (← `(bracketedBinder| {$invId:ident : $sigId → Prop}), ← `(fun ($outVar:ident : $retTy) => $(← mkEnsPostGoalPure ensId pTerms outVar outIsFallible info.innerOpt?.isSome)))
          pure #[
            ← mkSrvThmPure ensThmId (#[sigB, invB] ++ bBs) (← mkAppC ``Qed.Server.ProgEnsures #[invId, postLam, callT]) (← mkEnsProofTacPure (some defId) #[ensId] (Syntax.mkStrLit info.fnStr) lbl info.contracts.topEnsTac?) true,
            ← noUnusedVarsPure (← `(command| instance $sigB:bracketedBinder $[$bBs:bracketedBinder]* : Qed.Server.SafeIOEnsures $callT $postLam := ⟨$noAtomApp, fun {$invId:ident} => $(← mkAppTermsPure ensThmId thmArgs)⟩))]
    return (callT, #[
      ← mkSrvThmPure noAtomId (#[sigB] ++ bBs) (← mkAppC ``Qed.Server.NoAtomic #[callT]) (← `(Lean.Parser.Tactic.tacticSeq| qedSrvProveSafeIO $defId)) true,
      ← noUnusedVarsPure (← `(command| instance $sigB:bracketedBinder $[$bBs:bracketedBinder]* : Qed.Server.SafeIO $callT := ⟨$noAtomApp⟩))] ++ ensCmds, none)
  if !immCmds.isEmpty then elabSrvCmds immCmds
  if let some ec := defCmd? then deferSrvCmd ec
  let ecCtx : EffContractCtx := {
    fnIdent := info.fnIdent, targetId := defId, thmBaseLeaf := info.defLeaf, fnStr := info.fnStr,
    isMonadic, isFallible := outIsFallible, hasState := false, paramIds := info.pp.idents, binderIds := bIds, binderTys := bTys,
    callT, payloadTerm := info.payloadTerm, errTyTerm := info.errTyTerm, innerOpt? := info.innerOpt? }
  elabSrvExtraContracts ecCtx info.contracts
  return !(← hasSrvErrors)

@[noinline] private def elabFnMode (info : FnElabInfo) (isMonadic touchesState isPureSync hasAwait hasEmit callsMonadic : Bool) :
    SrvElabM (Option (Option ServiceMethodInfo × SrvHelperSig × Array Ident)) := do
  let c ← read; let defId := info.defId c
  if isPureSync then
    let pureCtx := { info.baseCtx with stateRule := .statelessServer, allowAwait := false, allowUnwrap := false, locals := if info.isService then info.baseCtx.locals else info.pp.names }
    let bodyTerm ← liftM <| Qed.lowerPureFnStmts (if info.isService then s!"service fn {info.fnStr}" else s!"fn {info.fnStr}") info.bodyStmts.toList
      (lowerWithLocals? := some fun extra mode s => do let (t, st) ← (lowerExpr { pureCtx with locals := pureCtx.locals ++ extra } mode s).run {}; (recordSrvExtRoots st.extRoots).run c; pure t)
    unless (← emitFnDefAndProofs info false false info.payloadTerm (← runSrvPQ `(srvAutoField($bodyTerm)))) do return none
    return some (info.mkRes c false false false false false false)
  if !isMonadic then
    let sUnitId := mkIdent `_sUnit
    let (pureBody, lSt) ← liftM <| (lowerPureBlock { info.baseCtx with stateRule := .statelessServer, allowAwait := false } false sUnitId sUnitId info.bodyStmts).run {}
    recordSrvExtRoots lSt.extRoots; checkReadOnlyDecl info.fnIdent "fn" info.fnStr info.declaredReadOnly false lSt.dbWrite false lSt.hasCookieOp
    let (retTy, wrapped) ← runSrvPQ do
      return (← mkAppC ``Except #[info.errTyTerm, info.payloadTerm], ← wrapAuthAndReqsPure info.reqs (← `(let $sUnitId:ident : Unit := (); (Qed.Server.srvFinish $sUnitId $pureBody).2)) (pureWrap := false))
    unless (← emitFnDefAndProofs info false true retTy wrapped) do return none
    return some (info.mkRes c false true false false lSt.dbWrite lSt.hasCookieOp)
  if touchesState then
    let isAsync := hasAwait || blockHasAtomic info.bodyStmts || callsMonadic
    let fnInnerIdent := mkIdentFrom info.fnIdent info.defLeaf; let pTerms : Array Term := info.pp.idents.map (⟨·.raw⟩)
    let some hRes ← elabSrvCallable fnInnerIdent info.fnStr info.bodyStmts info.payloadTerm info.errTyTerm {
      thmBaseLeaf := info.defLeaf, errRef? := some info.fnIdent.raw, missingRetLabel := info.fnStr, forceAsync? := some isAsync,
      allowUnwrap := info.isFallible || info.innerOpt?.isSome, hasFallible := info.isFallible, innerOpt? := info.innerOpt?,
      locals := info.pp.names, paramIds := info.pp.idents, extraBinderIds := info.pp.idents, extraBinderTys := info.pp.tyTerms, extraCallArgs := pTerms, reqs? := some info.reqs,
      ensSpec? := mkFnEnsSpec? info.ensRes? pTerms info.innerOpt?.isSome info.contracts.topEnsTac?, contracts? := some info.contracts,
      declaredReadOnly := info.declaredReadOnly, roKindLabel := "fn", txParams := info.pp.txParams } | return none
    elabSrvPure do
      let (guarded, atomicBs, doc?, allBs) := (← wrapAuthAndReqsPure info.reqs hRes.runExpr, ← c.atomicBindersPure, info.doc?, info.allDefBinders)
      noUnusedVarsPure (← `(command| $[$doc?:docComment]? @[noinline, nospecialize] def $defId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m] $[$atomicBs:bracketedBinder]* $[$allBs:bracketedBinder]* : m (Except $(info.errTyTerm) $(info.payloadTerm)) := $guarded))
    if (← hasSrvErrors) then return none
    return some (info.mkRes c true true true hRes.mutatesState hRes.dbWrite hRes.hasCookieOp #[defId, c.fnSubId fnInnerIdent (if isAsync then "_handler" else "_step")])
  let outIsFallible := !info.isService || info.isFallible
  let (fullBody, lSt, retTy) ← if !outIsFallible then
      let (infBody, st) ← liftM <| (lowerInfallibleAsyncBlock info.baseCtx info.bodyStmts).run {}
      pure ((← runSrvPQ (wrapWithEnvDeclsPure info.usedEnvs infBody)).1, st, info.payloadTerm)
    else
      let (asyncBody, st) ← liftM <| (lowerAsyncBlock { info.baseCtx with stateFields := #[] } none info.bodyStmts).run {}
      let (fb, rt) ← runSrvPQ do
        return ((← wrapWithEnvDeclsPure info.usedEnvs (← wrapAuthAndReqsPure info.reqs (← mkAppC ``Qed.Server.srvFinishM #[asyncBody]))).1, ← mkAppC ``Except #[info.errTyTerm, info.payloadTerm])
      pure (fb, st, rt)
  recordSrvExtRoots lSt.extRoots; checkReadOnlyDecl info.fnIdent "fn" info.fnStr info.declaredReadOnly false lSt.dbWrite hasEmit lSt.hasCookieOp
  unless (← emitFnDefAndProofs info true outIsFallible retTy fullBody) do return none
  return some (info.mkRes c true outIsFallible false false lSt.dbWrite lSt.hasCookieOp)

@[noinline] private def mkFnHeaderBindersPure (c : SrvElabCtx) (isService needsCtx hasExplicitCtx : Bool) (pp : ParsedFnParams) :
    PureQuotM (Term × Option Term × Array Ident × Array Term × Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  let (errTyTerm, ctxTy) : Term × Term := (mkCIdent ``Qed.Server.ApiError, mkCIdent ``Qed.Server.RequestCtx)
  let (preIds, preTys) : Array Ident × Array Term ← if isService then pure (if needsCtx then (#[c.ctxId], #[ctxTy]) else (#[], #[]))
    else do pure (c.envIdents.push c.ctxId, (← c.envBinderTysPure).push ctxTy)
  let ctxT? ← if isService && !hasExplicitCtx && !needsCtx then some <$> `(({} : Qed.Server.RequestCtx)) else pure none
  return (errTyTerm, ctxT?, preIds ++ pp.idents, preTys ++ pp.tyTerms, (← mkTypedBindersPure preIds preTys) ++ pp.defBinders)

@[noinline] private def elabStatelessOrHelperFn (isService : Bool) (rawHc : Syntax) : SrvElabM (Option (Option ServiceMethodInfo × SrvHelperSig × Array Ident)) := do
  let (doc?, hc) := unwrapDocClause rawHc; let c ← read; let declaredReadOnly := (hc.getArg 0).getNumArgs == 1
  let fnIdent : Ident := ⟨hc.getArg 2⟩; let fnStr := fnIdent.getId.toString; let kindDesc := if isService then "service" else "helper"
  if c.helpers.any (·.name == fnStr) then srvErrAt fnIdent (if isService then s!"duplicate `fn {fnStr}` in `service {c.srvName}`" else s!"duplicate helper `fn {fnStr}` in `server {c.srvName}`")
  let contracts ← liftM <| collectSrvContracts (if isService then "`service` `fn`" else "server `fn`") #[] (hc.getArg 8).getArgs {}
  let pp ← parseSrvFnParams (if isService then s!"service `fn {fnStr}`" else s!"server helper `fn {fnStr}`") "parameter" (hc.getArg 4).getSepArgs
    (reserved := if contracts.topEnsures.isEmpty then #[] else #["result"]) (allowExplicitCtx := isService)
  let hasExplicitRet := (hc.getArg 6).getNumArgs == 2
  let (payloadTerm, innerOpt?, isFallible, isUnitPayload) ← if hasExplicitRet then
      let rt ← liftSrvMacro (lowerSrvType ((hc.getArg 6).getArg 1) true s!"return type of {kindDesc} `fn {fnStr}`")
      pure (rt.term, rt.innerOpt?, rt.isFallible, (rt.mods.filter (· != .fallible)).isEmpty && rt.baseName == `Unit)
    else pure (mkCIdent ``Unit, none, true, true)
  let bodyStmts := if isUnitPayload then ensureUnitReturn fnIdent (suiteStmts (hc.getArg 9)) else suiteStmts (hc.getArg 9)
  if !isUnitPayload && !blockAlwaysReturns bodyStmts then srvErrAt fnIdent s!"missing `return` on fallthrough path of {kindDesc} `fn {fnStr}`"
  let (domainTagIdents, hasPlainFail) := scanBodyFailTags bodyStmts
  if !domainTagIdents.isEmpty then srvErrAt fnIdent s!"typed `fail(.tag)` is only supported in `rpc` endpoints; use `fail(code, msg)` or `fail(msg)` in {if isService then "`service`" else "private helper"} `fn {fnStr}`"
  if hasPlainFail && !isFallible then srvErrAt fnIdent s!"`fail(...)` can only be returned from a fallible `T!` {if isService then "function" else "helper"} (`fn {fnStr}` is not declared `-> ...!`)"
  let defLeaf := if isService then fnIdent.getId else Name.mkSimple s!"_fn_{fnStr}"
  let allStx := bodyStmts ++ contracts.requires ++ pp.defaultExprs
  let usedEnvs := if isService then c.envDecls.filter fun e => allStx.any (stxMentionsVar e.ident.getId.toString) else #[]
  let reqs ← elabRequiresClauses fnIdent defLeaf fnStr (if isService then "_hSvcReq" else "_hFnReq") "_req" pp.names pp.names pp.idents pp.tyTerms contracts.requires (trackAuth := isService)
  let callsCtxSvc := isService && c.serviceDecls.any fun (al, si) => let alStr := al.getId.toString
    si.methods.any fun m => m.takesCtx && bodyStmts.any (stxMentionsVar alStr) && bodyStmts.any (stxAny fun s => (extractDottedChain? s).any (· == [alStr, m.name]))
  let needsCtx := isService && !pp.hasExplicitCtx && (allStx.any (stxMentionsVar "ctx") || reqs.authBind?.isSome || c.helpers.any (fun h => h.takesCtx && bodyStmts.any (stxMentionsVar h.name)) || callsCtxSvc)
  let (errTyTerm, ctxTerm?, thmBinderIds, thmBinderTys, allDefBinders) ← runSrvPQ (mkFnHeaderBindersPure c isService needsCtx pp.hasExplicitCtx pp)
  let (hasAwait, hasEmit) := (blockHasAwait bodyStmts, !isService && blockHasEmit bodyStmts)
  let touchesState := !isService && c.hasState && (blockHasAtomic bodyStmts || c.stateFieldNames.any (fun sf => bodyStmts.any (stxMentionsVar sf)) || c.helpers.any (fun h => h.takesAtomic && bodyStmts.any (stxMentionsVar h.name)))
  let callsMonadic := c.helpers.any fun h => h.isMonadic && bodyStmts.any (stxMentionsVar h.name)
  let isMonadic := hasAwait || hasEmit || touchesState || callsMonadic || !usedEnvs.isEmpty
  let bodyHasUnwrap ← liftM <| stmtsHaveUnwrapM (pp.names ++ c.stateFieldNames ++ c.envVarNames) bodyStmts
  if isService && !isFallible && (usedEnvs.any (·.default?.isNone) || !contracts.requires.isEmpty || bodyStmts.any (stxAny (·.getKind == ``qedStmtDbTransaction)) || hasPlainFail || (bodyHasUnwrap && innerOpt?.isNone)) then
    srvErrAt fnIdent s!"service `fn {fnStr}` can fail (uses required `secret`/`env`, `requires`, `transaction`, `fail`, or `?`); declare its return type as `-> ...!`"
  let some ensRes? ← elabEnsuresAbbrev (mkIdentFrom fnIdent defLeaf) fnStr `result pp.names pp.idents pp.tyTerms (innerOpt?.getD payloadTerm) contracts.topEnsures | return none
  let baseCtx ← mkBaseLowerCtx fnStr (pp.names ++ reqs.extraLocals) isMonadic (isFallible || (innerOpt?.isSome && (!isService || isMonadic))) isFallible innerOpt? (includeDbs := isService || isMonadic) (ctxTerm? := ctxTerm?) (txParams := pp.txParams)
  let bodyHasCatch := !isService && bodyStmts.any (stxAny fun s => s.getKind == ``qedStmtLet && (s.getArg 5).getNumArgs > 0)
  let isPureSync := !isMonadic && !isFallible && (isService || (contracts.requires.isEmpty && !bodyHasUnwrap && !bodyHasCatch && !hasPlainFail && hasExplicitRet))
  elabFnMode { isService, doc?, declaredReadOnly, fnIdent, defLeaf, pp, payloadTerm, innerOpt?, isFallible, errTyTerm, contracts, reqs, ensRes?, usedEnvs, takesCtx := if isService then needsCtx else true, thmBinderIds, thmBinderTys, allDefBinders, baseCtx, bodyStmts }
    isMonadic touchesState isPureSync hasAwait hasEmit callsMonadic

@[noinline] private def elabServerBeforeClause (bc : Syntax) : SrvElabM (Option Term) := do
  let c ← read; let rawStmts := suiteStmts (bc.getArg 2); let hasAw := blockHasAwait rawStmts
  let isAsync := if c.hasState then hasAw || blockHasAtomic rawStmts else true
  (·.map (·.runExpr)) <$> elabSrvCallable (mkIdentFrom bc `_before) "before" rawStmts (mkCIdent ``Unit) (mkCIdent ``Qed.Server.ApiError) {
    errRef? := some bc, missingRetLabel := "`before`", isUnit := true, forceAsync? := some isAsync, allowAwait? := some (if c.hasState then isAsync else hasAw) }

@[noinline] private def mkRpcDispatchArmPure (fnStr : String) (reqVar : Ident) (reqTupleTy payloadTerm runExpr : Term)
    (pIdents : Array Ident) (projs : Array Term) (reqs : LoweredRequires) (beforeRun? : Option Term) (errTypeId? : Option Ident) :
    PureQuotM (TSyntax ``Lean.Parser.Term.matchAltExpr × Term) := do
  let resRun ← if errTypeId?.isSome then `($runExpr >>= fun _r => Pure.pure ((Qed.Server.SrvFailure.toWire _r).map Qed.Proto.encode))
    else mapRunPure runExpr (mkCIdent ``Qed.Proto.encode)
  let dec ← mkProtoDecodeBindPure (mkIdent `reqBytes) reqVar reqTupleTy pIdents projs (← wrapAuthAndReqsPure reqs resRun)
  return (← `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkStrLit fnStr) => $(← wrapWithBeforePure beforeRun? dec)),
          ← match errTypeId? with | some e => mkAppC ``Except #[← mkAppC ``Qed.RpcDomainError #[e], payloadTerm] | none => pure payloadTerm)

@[noinline] private def elabServerFnClause (existingMethods : Array ServerMethodInfo) (rawFc : Syntax) (beforeRun? : Option Term := none) :
    SrvElabM (Option (ServerMethodInfo × (Term × Term) × TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let (doc?, fc) := unwrapDocClause rawFc; let c ← read; let declaredReadOnly := (fc.getArg 0).getNumArgs == 1
  let fnIdent : Ident := ⟨fc.getArg 2⟩; let fnStr := fnIdent.getId.toString
  if existingMethods.any (·.name == fnStr) || c.helpers.any (·.name == fnStr) then srvErrAt fnIdent s!"duplicate function `{fnStr}` in `server {c.srvName}`"
  let contracts ← liftM <| collectSrvContracts "`rpc`" #[] (fc.getArg 9).getArgs {}
  let (pIdents, pTyTerms, paramNames) ← parseSrvParams s!"server RPC `{fnStr}`" "parameter" (fc.getArg 4).getSepArgs (reserved := if contracts.topEnsures.isEmpty then #[] else #["result"])
  let retTy ← liftSrvMacro (lowerSrvType (fc.getArg 7) true s!"return type of `{fnStr}`")
  let (payloadTerm, innerOpt?, isUnitPayload) := (retTy.term, retTy.innerOpt?, (retTy.mods.filter (· != .fallible)).isEmpty && retTy.baseName == `Unit)
  let rawStmts := suiteStmts (fc.getArg 10); let (domainTagIdents, hasPlainFail) := scanBodyFailTags rawStmts
  if !domainTagIdents.isEmpty && hasPlainFail then srvErrAt fnIdent s!"cannot mix typed `fail(.tag)` and untyped `fail(\"...\")` inside `{fnStr}`; use `fail(.tag, msg)` for all domain failures"
  if !domainTagIdents.isEmpty && !retTy.isFallible then srvErrAt fnIdent s!"`fail(.tag)` can only be returned from a fallible `T!` function (`{fnStr}` is not declared `-> ...!`)"
  let errTypeId? ← if domainTagIdents.isEmpty then pure none else some <$> elabDomainErrorType fnIdent domainTagIdents
  if (← hasSrvErrors) then return none
  let domainErrTyTerm? : Option Term := errTypeId?.map (⟨·.raw⟩)
  let errTyTerm ← runSrvPQ do match domainErrTyTerm? with | some et => mkAppC ``Qed.Server.SrvFailure #[et] | none => pure (mkCIdent ``Qed.Server.ApiError)
  let reqs ← elabRequiresClauses fnIdent fnIdent.getId fnStr "_hReq" "_req" paramNames paramNames pIdents pTyTerms contracts.requires
  let some ensRes? ← elabEnsuresAbbrev fnIdent fnStr `result paramNames pIdents pTyTerms (innerOpt?.getD payloadTerm) contracts.topEnsures | return none
  let ensSpec? := mkFnEnsSpec? ensRes? (pIdents.map (⟨·.raw⟩)) innerOpt?.isSome contracts.topEnsTac?
  let reqTupleTy ← liftSrvMacro (buildProdType pTyTerms); let reqVar := mkIdent `_reqVal; let projs ← runSrvPQ (extractTupleProjectionsPure reqVar pTyTerms.size)
  let some hRes ← elabSrvCallable fnIdent fnStr rawStmts payloadTerm errTyTerm {
    isUnit := isUnitPayload, allowUnwrap := retTy.isFallible || innerOpt?.isSome, hasFallible := retTy.isFallible, innerOpt?, domainErrTy? := domainErrTyTerm?,
    locals := paramNames, paramIds := pIdents, extraBinderIds := pIdents, extraBinderTys := pTyTerms, extraCallArgs := projs, reqs? := some reqs, ensSpec?, contracts? := some contracts, declaredReadOnly } | return none
  let (arm, wireRespTy) ← runSrvPQ (mkRpcDispatchArmPure fnStr reqVar reqTupleTy payloadTerm hRes.runExpr pIdents projs reqs beforeRun? errTypeId?)
  let paramTypeConsts ← elabFnClientStubs fnIdent fnStr pIdents pTyTerms reqTupleTy payloadTerm innerOpt? errTypeId? ensSpec? reqs doc?
  return some ({
    name := fnStr, paramNames := pIdents.map (·.getId), paramCount := pIdents.size, isReadOnly := hRes.isReadOnly,
    isAsync := blockHasAwait rawStmts || beforeRun?.isSome, isFallible := retTy.isFallible, isOption := innerOpt?.isSome,
    hasClientReq := reqs.clientReqId?.isSome, requiresAuth := reqs.requiresAuth, clientReqConst := reqs.clientReqConst?,
    clientReqLabel := reqs.clientReqLabel, hasEnsures := ensSpec?.isSome, ensPredConst := ensRes?.map (·.2.1),
    domainErrTags := domainTagIdents.map (·.getId.toString), rawRpcConst := c.fullSrvName ++ Name.mkSimple s!"_rpc_{fnStr}",
    outcomeConst := c.fullSrvName ++ fnIdent.getId.appendAfter "_Outcome", paramTypeConsts }, (reqTupleTy, wireRespTy), arm)

@[noinline] private def elabServerHttpRouteClause (routeIdx : Nat) (existingRoutes : Array (String × String × Bool)) (hc : Syntax) (beforeRun? : Option Term := none) :
    SrvElabM (Option ((String × String × Bool) × TSyntax ``Lean.Parser.Term.matchAltExpr)) := do
  let c ← read; let isStream := hc.getKind == ``srvStreamClause
  let methodStr := if isStream then "GET" else (hc.getArg 0).getId.toString.toUpper; let pathStx := hc.getArg 1; let pathStr := (⟨pathStx⟩ : TSyntax `str).getString
  if !pathStr.startsWith "/" then srvErrAt pathStx s!"custom HTTP route path `{pathStr}` must start with `/`"
  if pathStr.startsWith "/_qed/" then srvErrAt pathStx s!"custom HTTP route path `{pathStr}` cannot use reserved `/_qed/` prefix"
  if existingRoutes.any fun (m, p, _) => m == methodStr && p == pathStr then srvErrAt pathStx s!"duplicate custom HTTP route `{methodStr} {pathStr}` in `server {c.srvName}`"
  let (routeLeaf, routeLabel) := (Name.mkSimple s!"_http_{routeIdx}", if isStream then s!"stream {pathStr}" else s!"{methodStr} {pathStr}")
  let routeIdent := mkIdentFrom pathStx routeLeaf
  let contracts ← liftM <| collectSrvContracts s!"HTTP route `{routeLabel}`" #[] (hc.getArg 3).getArgs {}
  let reqs ← elabRequiresClauses routeIdent routeLeaf routeLabel "_hHttpReq" "_req" #[] #[] #[] #[] contracts.requires (trackAuth := true)
  let payloadTerm : Term := mkCIdent (if isStream then ``Unit else ``Qed.Server.HttpResponse)
  let some ensRes? ← elabEnsuresAbbrev routeIdent routeLabel `result #[] #[] #[] payloadTerm contracts.topEnsures | return none
  let some hRes ← elabSrvCallable routeIdent routeLabel (suiteStmts (hc.getArg 4)) payloadTerm (mkCIdent ``Qed.Server.ApiError) {
    thmBaseLeaf := routeLeaf, errRef? := some pathStx, isUnit := isStream, isHttpRoute := !isStream, isStreamRoute := isStream,
    reqs? := some reqs, ensSpec? := mkFnEnsSpec? ensRes? #[] false contracts.topEnsTac?, contracts? := some contracts } | return none
  let arm ← runSrvPQ do
    let mapFn ← if isStream then `(fun _ => Option.some (Qed.Server.HttpResponse.sse [])) else pure (mkCIdent ``Option.some)
    `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkStrLit methodStr), $(Syntax.mkStrLit pathStr) => $(← wrapWithBeforePure beforeRun? (← wrapAuthAndReqsPure reqs (← mapRunPure hRes.runExpr mapFn))))
  return some ((methodStr, pathStr, reqs.requiresAuth), arm)

@[noinline] private def elabServerAuthHook (hookLabel : String) (hookLeaf : Name) (authInfo : AuthInfo) (hc : Syntax) : SrvElabM (Option Term) := do
  let c ← read; let paramIdent : Ident := ⟨hc.getArg 2⟩; let paramStr ← checkSrvParamName s!"`{hookLabel}`" paramIdent
  let rawStmts := suiteStmts (hc.getArg 5); let hasAw := blockHasAwait rawStmts; let isAsync := c.hasState && (hasAw || blockHasAtomic rawStmts)
  let (authUserVar, hAuthEqId, hAuthId) := (mkIdent `_authUser, mkIdent `_hAuthEq, mkIdent `_hAuth)
  let extraTys ← runSrvPQ (mkAuthExtraTysPure c.ctxId paramIdent (some authInfo) false)
  (·.map (·.runExpr)) <$> elabSrvCallable (mkIdentFrom hc hookLeaf) hookLabel rawStmts (mkCIdent ``Unit) (mkCIdent ``Qed.Server.ApiError) {
    thmBaseLeaf := hookLeaf, errRef? := some hc, missingRetLabel := hookLabel, isUnit := true, forceAsync? := some isAsync,
    allowAwait? := some (if c.hasState then isAsync else hasAw), locals := #[paramStr],
    extraBinderIds := #[paramIdent, hAuthEqId, hAuthId], extraBinderTys := extraTys, extraCallArgs := #[⟨authUserVar.raw⟩, ⟨hAuthEqId.raw⟩, ⟨hAuthId.raw⟩] }

/-! ## Server / Service `example` Elaborator (Pure-AST -> Single `PureQuotM` Pass) -/

@[noinline] private def resolveSrvExDbTable (c : SrvElabCtx) (tblRef : Ident) : CommandElabM (Ident × String) := do
  match tblRef.getId.eraseMacroScopes with
  | .str (.str .anonymous aliasStr) tblStr =>
      if let some (_, dbInfo) := c.dbDecls.find? (·.1.getId.toString == aliasStr) then
        if dbInfo.tables.any (·.tableName == tblStr) then return (mkIdentFrom tblRef (dbInfo.dbName ++ Name.mkSimple tblStr), tblStr)
        errAt tblRef s!"unknown table `{tblStr}` in database `{aliasStr}`"
      return (tblRef, tblStr)
  | .str .anonymous tblStr =>
      let matchesDb := c.dbDecls.filter fun (_, dbInfo) => dbInfo.tables.any (·.tableName == tblStr)
      if matchesDb.size == 1 then return (mkIdentFrom tblRef (matchesDb[0]!.2.dbName ++ Name.mkSimple tblStr), tblStr)
      if matchesDb.size > 1 then errAt tblRef s!"ambiguous table `{tblStr}` in `with db`; qualify it as `<db>.{tblStr}`"
      errAt tblRef s!"unknown table `{tblStr}` in `with db`; expected `<db>.<table>` from a `use <db> : ...` database"
  | .str _ tblStr => return (tblRef, tblStr)
  | _ => errAt tblRef s!"`with db` expects `<db>.<table>` (e.g. `db.items`), got `{tblRef.getId}`"

private def srvExBangIdx : Syntax → Term → Term → ExprMode → MacroM Term := fun _ arr idx _ => `($arr[$idx]!)
private def lowerSrvExVal (s : Syntax) : CommandElabM Term := liftMacroCmd (lowerSimpleQedExpr .val s (lowerIndex? := some srvExBangIdx))
private def lowerSrvExProp (s : Syntax) : CommandElabM Term := liftMacroCmd (lowerSimpleQedExpr .propInv s (lowerIndex? := some srvExBangIdx))
private def termMentionsRoot (v : String) (t : Term) : Bool :=
  stxAny (fun s => s.isIdent && match s.getId.eraseMacroScopes.components with | root :: _ => root.toString == v | [] => false) t.raw

private inductive SrvExCheck where | ok (rk : Nat) (val? : Option Term) | err (code? : Option (TSyntax `num)) | status (val : Term) | prop (p : Term)
private inductive SrvExStep where
  | withEq (kw : Name) (val : Term) | withStrEq (isEnv : Bool) (key : String) (val : Term) | withRole (val : Term) | withUser (val? : Option Term)
  | withHttp (isOk : Bool) (method url : String) (code : TSyntax `num) (payload? : Option Term)
  | seedDb (tblRowId : Ident) (tblStr : String) (rows : Sum (Array Term) Term)
  | callSvc (fnId : Ident) (takesCtx isMonadic : Bool) (args : Array Term)
  | callRpc (dispId : Ident) (fnStr : String) (reqTy respTy : Term) (args : Array Term)
  | callHelper (defId : Ident) (takesEnvs takesCtx isMonadic isFallible : Bool) (args : Array Term)
  | reqHttp (dispId : Ident) (methodStr pathStr : String) | check (chk : SrvExCheck)

@[noinline] private def parseOneSrvExStep (ctx : SrvExCtx) (acc : Array SrvExStep × Nat) (it : Syntax) : CommandElabM (Array SrvExStep × Nat) := do
  let (steps, rk) := acc; let c := ctx.c; let push (s : SrvExStep) (nk : Nat := rk) := pure (steps.push s, nk)
  match it.getKind with
  | `Qed.Server.srvExWithEq => push (.withEq (it.getArg 1).getId.eraseMacroScopes (← lowerSrvExVal (it.getArg 3)))
  | `Qed.Server.srvExWithStrEq => push (.withStrEq ((it.getArg 1).getId.eraseMacroScopes == `env) (⟨it.getArg 2⟩ : TSyntax `str).getString (← lowerSrvExVal (it.getArg 4)))
  | `Qed.Server.srvExWithExpr =>
      let vStx := it.getArg 2
      if (it.getArg 1).getId.eraseMacroScopes == `role then push (.withRole (← lowerSrvExVal vStx))
      else let uu := unwrapParens1 vStx; if uu.getKind == ``qedIdent && (uu.getArg 0).getId.eraseMacroScopes == `none then push (.withUser none) else push (.withUser (some (← lowerSrvExVal vStx)))
  | `Qed.Server.srvExWithHttp =>
      let payload? ← if (it.getArg 6).getNumArgs == 1 then some <$> lowerSrvExVal ((it.getArg 6).getArg 0) else pure none
      push (.withHttp ((it.getArg 1).getId.eraseMacroScopes == `http) (it.getArg 2).getId.eraseMacroScopes.toString.toUpper (⟨it.getArg 3⟩ : TSyntax `str).getString ⟨it.getArg 5⟩ payload?)
  | `Qed.Server.srvExDb =>
      let (tblRowId, tblStr) ← resolveSrvExDbTable c ⟨it.getArg 2⟩; let rawRows := it.getArg 4
      let rows ← if rawRows.getKind == ``qedArrLit then Sum.inl <$> mapCmd (rawRows.getArg 1).getSepArgs lowerSrvExVal else Sum.inr <$> lowerSrvExVal rawRows
      push (.seedDb tblRowId tblStr rows)
  | `Qed.Server.srvExCall =>
      let fnId : Ident := ⟨it.getArg 1⟩; let fnStr := fnId.getId.eraseMacroScopes.toString; let args ← mapCmd (it.getArg 3).getSepArgs lowerSrvExVal
      if ctx.isService then
        let some mi := ctx.serviceMethods.find? (·.name == fnStr) | errAt fnId s!"unknown service function `{fnStr}` in `example {ctx.exNm}`"
        push (.callSvc (c.subId (Name.mkSimple fnStr) fnId) mi.takesCtx mi.isMonadic args) (if mi.isMonadic || mi.isFallible then 0 else 2)
      else if let some (reqTy, respTy) := ctx.rpcWireMap[fnStr]? then push (.callRpc (c.subId `dispatchM fnId) fnStr reqTy respTy args) 0
      else if let some hs := c.helpers.find? (·.name == fnStr) then
        push (.callHelper hs.defId hs.takesEnvs hs.takesCtx hs.isMonadic hs.isFallible args) (if hs.isMonadic || !c.envDecls.isEmpty || hs.isFallible then 0 else 2)
      else errAt fnId s!"unknown RPC or helper `fn` `{fnStr}` in `example {ctx.exNm}`"
  | `Qed.Server.srvExReq =>
      if ctx.isService then errAt it s!"HTTP requests are only available in `server` examples, not `service {c.srvName}`"
      push (.reqHttp (c.subId `httpDispatchM ⟨it.getArg 0⟩) (it.getArg 0).getId.eraseMacroScopes.toString.toUpper (⟨it.getArg 1⟩ : TSyntax `str).getString) 1
  | `Qed.Server.srvExExpectOk =>
      let valOpt := it.getArg 2; let v? ← if valOpt.getNumArgs == 3 then some <$> lowerSrvExVal (valOpt.getArg 1) else pure none
      push (.check (.ok rk v?))
  | `Qed.Server.srvExExpectErr =>
      if rk == 2 then errAt it s!"`expect error` cannot be used after a pure (non-fallible) call in `example {ctx.exNm}`"
      let codeOpt := it.getArg 2; push (.check (.err (if codeOpt.getNumArgs == 3 then some ⟨codeOpt.getArg 1⟩ else none)))
  | `Qed.Server.srvExExpectStatus => push (.check (.status (← lowerSrvExVal (it.getArg 3))))
  | `Qed.Server.srvExExpectExpr => push (.check (.prop (← lowerSrvExProp (it.getArg 1))))
  | _ => errAt it s!"unexpected item in `example {ctx.exNm}`"

private def srvExTraceSpecs : Array (Name × List Name) := #[
  (`http_calls, [`trace, `httpCalls, `length]), (`http, [`trace, `httpCalls, `toArray]),
  (`decrypt_calls, [`trace, `decryptCount]), (`encrypt_calls, [`trace, `encryptCount]),
  (`db_queries, [`trace, `dbQueries, `length]), (`cookies, [`trace, `cookies, `toArray]),
  (`db_count, [`db, `countRows]), (`state, [`shared])]

@[noinline] private def wrapSrvExCheckPure (stId : Ident) (checkT rest : Term) : PureQuotM Term := do
  foldrPQ srvExTraceSpecs (← `(($checkT) ∧ ($rest))) fun (nm, path) body => do
    if !termMentionsRoot nm.toString checkT then return body
    mkLetBindTerm (mkIdent nm).raw none (← foldProjTerms stId.raw ⟨stId.raw⟩ path) body

private def srvExEqSpecs : Array (Name × Bool × Name × Option Name) := #[
  (`now, false, ``Qed.Server.Eval.setNow, some ``UInt64), (`session, true, ``Qed.Server.Eval.setSession, none),
  (`query, true, ``Qed.Server.Eval.setQuery, none), (`body, true, ``Qed.Server.Eval.setBody, none)]

@[noinline] private def compileOneSrvExStepPure (ctx : SrvExCtx) (envId stId ctxId : Ident) (step : SrvExStep) (rest : Term) : PureQuotM Term := do
  let (resId, statusId, bodyId, evId, c) := (mkIdent `result, mkIdent `status, mkIdent `body, mkIdent `_ev, ctx.c)
  let letR (id : Ident) (rhs : Term) : PureQuotM Term := mkLetBindTerm id.raw none rhs rest
  let mkEvalStep (progT sTy : Term) (resBind : Term → PureQuotM Term) : PureQuotM Term := do
    let evCall ← mkAppC ``Qed.Server.Eval.evalProg #[envId, stId, ← mkAscribePure progT (← mkAppC ``Qed.Server.ThreadProg #[sTy, ← `(_)])]
    mkLetBindTerm evId.raw none evCall (← mkLetBindTerm stId.raw none (← `(($evId).state)) (← resBind (← `(($evId).value))))
  let mkEval (progT sTy : Term) := mkEvalStep progT sTy fun v => mkLetBindTerm resId.raw none v rest
  match step with
  | .withEq kw vT =>
      if let some (_, isCtx, fn, ty?) := srvExEqSpecs.find? (·.1 == kw) then
        let tgt := if isCtx then ctxId else envId
        letR tgt (← mkAppC fn #[tgt, ← match ty? with | some tn => mkAscribePure vT (mkCIdent tn) | none => pure vT])
      else if kw == `ctx then letR ctxId (← mkAscribePure vT (mkCIdent ``Qed.Server.RequestCtx))
      else letR stId (← mkAppC ``Qed.Server.Eval.setShared #[stId, ← mkAscribePure vT ctx.stateTy])
  | .withStrEq isEnv k vT =>
      let (tgt, fn) := if isEnv then (envId, ``Qed.Server.Eval.setEnvVar) else (ctxId, ``Qed.Server.Eval.setHeader)
      letR tgt (← mkAppC fn #[tgt, Syntax.mkStrLit k, vT])
  | .withRole vT => letR ctxId (← mkAppC ``Qed.Server.Eval.setRole #[ctxId, vT])
  | .withUser u? => letR ctxId (← mkAppC ``Qed.Server.Eval.setUser #[ctxId, ← mkOptTermPure u?])
  | .withHttp isOk m u code p? =>
      let codeT ← if isOk then mkAscribePure ⟨code.raw⟩ (mkCIdent ``UInt32) else pure ⟨code.raw⟩
      let stub ← mkAppC (if isOk then ``Qed.Server.Eval.HttpStub.ok else ``Qed.Server.Eval.HttpStub.err)
        #[Syntax.mkStrLit m, Syntax.mkStrLit u, codeT, p?.getD (Syntax.mkStrLit (if isOk then "" else "upstream error"))]
      letR stId (← mkAppC ``Qed.Server.Eval.pushHttpStub #[stId, stub])
  | .seedDb tblRowId tblStr rows =>
      let rowsT ← match rows with | .inl elems => mkListLitPure (← mapPQ elems (mkAscribePure · tblRowId)) | .inr v => mkAscribePure v (← mkAppC ``List #[tblRowId])
      letR stId (← mkAppC ``Qed.Server.Eval.seedDbRows #[stId, Syntax.mkStrLit tblStr, mkIdentFrom tblRowId (tblRowId.getId ++ `schema), mkIdentFrom tblRowId (tblRowId.getId ++ `encodeRow), rowsT])
  | .callSvc fnId takesCtx isMonadic args =>
      let callE ← mkAppTermsPure fnId ((if takesCtx then #[⟨ctxId.raw⟩] else #[]) ++ args)
      if isMonadic then mkEval callE (mkCIdent ``Unit) else letR resId callE
  | .callRpc dispId fnStr reqTy respTy args =>
      let prog ← mkAppTermsPure dispId #[ctxId, Syntax.mkStrLit fnStr, ← mkAppC ``Qed.Proto.encode #[← mkAscribePure (← buildTupleValPure args) reqTy]]
      mkEvalStep prog ctx.stateTy fun evVal => do
        let dec ← `(($evVal).bind fun _bs => (Qed.Proto.decode (α := $respTy) _bs).mapError Qed.Server.ApiError.internal)
        mkLetBindTerm resId.raw (some (← mkAppC ``Except #[mkCIdent ``Qed.Server.ApiError, respTy])) dec rest
  | .callHelper defId takesEnvs takesCtx isMonadic isFallible args =>
      let callE ← mkAppTermsPure defId ((if takesEnvs then c.envIdents.map (⟨·.raw⟩) else #[]) ++ (if takesCtx then #[⟨ctxId.raw⟩] else #[]) ++ args)
      if isMonadic || !c.envDecls.isEmpty then
        let monE ← if isMonadic then pure callE else if isFallible then mkAppC ``Pure.pure #[callE] else `(Pure.pure (Except.ok (α := Qed.Server.ApiError) $callE))
        mkEval (← wrapWithEnvDeclsPure c.envDecls monE none).1 ctx.stateTy
      else letR resId callE
  | .reqHttp dispId mStr pStr =>
      mkEvalStep (← mkAppTermsPure dispId #[ctxId, Syntax.mkStrLit mStr, Syntax.mkStrLit pStr]) ctx.stateTy fun evVal => do
        mkLetBindTerm resId.raw none evVal (← mkLetBindTerm statusId.raw (some (mkCIdent ``Nat)) (← mkAppC ``Qed.Server.Eval.httpStatus #[resId])
          (← mkLetBindTerm bodyId.raw (some (mkCIdent ``String)) (← mkAppC ``Qed.Server.Eval.httpBody #[resId]) rest))
  | .check chk =>
      let eqP (fn : Name) (arg? : Option Term) := do mkPropEqTrue (← mkAppC fn (arg?.elim #[resId] fun a => #[a, resId]))
      let chkT ← match chk with
        | .ok 2 (some vT) => `($resId:ident = $vT) | .ok 2 none => pure (mkCIdent ``True)
        | .ok 1 v? => eqP (if v?.isSome then ``Qed.Server.Eval.isHttpOkEq else ``Qed.Server.Eval.isHttpOk) v?
        | .ok _ v? => eqP (if v?.isSome then ``Qed.Server.Eval.isOkEq else ``Qed.Server.Eval.isOk) v?
        | .err c?  => eqP (if c?.isSome then ``Qed.Server.Eval.isErrCode else ``Qed.Server.Eval.isErr) (c?.map (⟨·.raw⟩))
        | .status vT => `($statusId = $vT) | .prop p => pure p
      wrapSrvExCheckPure stId chkT rest

@[noinline] private def elabSrvExamples (isService : Bool) (exampleClauses : Array Syntax)
    (serviceMethods : Array ServiceMethodInfo := #[]) (rpcWireMap : Std.HashMap String (Term × Term) := {}) : SrvElabM Unit := do
  if exampleClauses.isEmpty then return
  let c ← read
  let (stateTy, initShared) ← runSrvPQ do
    if c.hasState then return (⟨c.stateId.raw⟩, ⟨(c.subId `initState).raw⟩) else return (← `(Unit), ← `(()))
  let (envId, stId, ctxId) := (mkIdent `_env, mkIdent `_st, mkIdent `_ctx)
  let (savedLog0, savedTasks0) := ((← get).messages, (← get).snapshotTasks)
  let (_, launched) ← foldlSrv exampleClauses (({} : Std.HashSet Name), (#[] : Array (Ident × Nat × Nat × Nat × Nat × Term))) fun (seen, acc) rawExStx => do
    let (doc?, exStx) := unwrapDocClause rawExStx; let exId : Ident := ⟨exStx.getArg 1⟩; let exNm := exId.getId.eraseMacroScopes
    if seen.contains exNm then srvErrAt exId s!"duplicate `example {exNm}` in `{c.srvName}`"
    let exCtx : SrvExCtx := { c, isService, serviceMethods, rpcWireMap, stateTy, exNm }
    let (steps, _) ← liftM <| foldlCmd (exStx.getArg 3).getArgs (#[], 0) (parseOneSrvExStep exCtx)
    let thmId := c.subId (Name.mkSimple s!"example_{exNm}") exId
    let (fullProp, cmdFast) ← runSrvPQ do
      let bodyProp ← foldrPQ steps (← `(True)) (compileOneSrvExStepPure exCtx envId stId ctxId)
      let fp ← `(let $envId:ident : Qed.Server.Eval.EvalEnv := {}; let $stId:ident : Qed.Server.Eval.EvalState $stateTy := { shared := $initShared }; let $ctxId:ident : Qed.Server.RequestCtx := {}; $bodyProp)
      return (fp, ← noUnusedVarsPure (← `(command| $[$doc?:docComment]? theorem $thmId:ident : $fp:term := by first | qedCloseGroundKernel | decide +kernel)))
    let stBefore ← get; withRef exId <| elabSrvCmd cmdFast; let stAfter ← get
    return (seen.insert exNm, acc.push (exId, stBefore.messages.reported.size, stBefore.messages.unreported.size, stBefore.snapshotTasks.size, stAfter.snapshotTasks.size, fullProp))
  deferSrvProof do
    let cur ← get
    let failed := launched.filter fun (_, pR, pU, t0, t1, _) =>
      hasNewErrors cur.messages pR pU || (cur.snapshotTasks.extract t0 t1).any (Qed.Diag.snapshotTreeHasErrors 64 ·.get)
    if failed.isEmpty then return true
    modify fun s => { s with messages := savedLog0, snapshotTasks := savedTasks0 }
    foldlCmd failed () fun _ (exId, _, _, _, _, fp) =>
      withRef exId <| elabPureCmd do noUnusedVarsPure (← `(command| example : $fp:term := by decide +kernel))
    return false

/-! ## Unified `server` & `service` Command Elaborator -/

@[noinline] private def withCmdRollback (failedReg : SimplePersistentEnvExtension Name (NameMap Name)) (fullName : Name) (run : Nat → Nat → CommandElabM Unit) : CommandElabM Unit := do
  let (savedEnv, priorLog, priorTasks) := (← getEnv, (← get).messages, (← get).snapshotTasks.size)
  let (priorRep, priorUnrep, priorKinds) := (priorLog.reported.size, priorLog.unreported.size, priorLog.loggedKinds)
  let rollback : CommandElabM Unit := do
    setEnv (failedReg.addEntry savedEnv fullName)
    modify fun s => let m := s.messages; { s with messages := { reported := filterNewWarnings m.reported priorRep, unreported := filterNewWarnings m.unreported priorUnrep, loggedKinds := priorKinds } }
  try run priorRep priorUnrep catch ex => rollback; throw ex
  let asyncErr := ((← get).snapshotTasks.extract priorTasks (← get).snapshotTasks.size).any fun t => Qed.Diag.snapshotTreeHasErrors 64 t.get
  if hasNewErrors (← get).messages priorRep priorUnrep || asyncErr then rollback

@[noinline] private def elabHelpersLoop (isService : Bool) (helperClauses : Array Syntax) : SrvElabM (Option (Array ServiceMethodInfo × Array SrvHelperSig × Array Ident)) :=
  foldOptSrv helperClauses (#[], #[], #[]) fun (mInfos, hSigs, shIds) hlc => do
    let some (mi?, hs, sh) ← withReader (fun (c : SrvElabCtx) => { c with helpers := hSigs, statefulHelperIds := shIds }) (elabStatelessOrHelperFn isService hlc) | return none
    return some (mi?.elim mInfos mInfos.push, hSigs.push hs, shIds ++ sh)

private def checkAuthInvs {α β : Type} (invs : Array α) (invIdOf : α → Ident) (what : α → String) (missingOf : α → Array β) (fmtItem : β → String) : SrvElabM Unit :=
  foldlSrv invs () fun _ inv => do
    let missing := missingOf inv
    unless missing.isEmpty do
      let id := invIdOf inv
      srvErrAt id s!"server invariant `{id.getId}` violated: {what inv} without `requires auth`: {String.intercalate ", " (missing.toList.map fmtItem)}"

private def mkNoSecretsInvsPure (c : SrvElabCtx) (invIds : Array Ident) : PureQuotM (Array (TSyntax `command)) :=
  mapPQ invIds fun id => `(command| theorem $(c.subId id.getId id) : $(c.subId `secrets) = #[] := rfl)

@[noinline] private def elabServerBody (b : ParsedServerBlock) (isStateless : Bool) : SrvElabM Unit := do
  let c ← read
  if c.hasState then unless (← elabServerStateCmds b.stateDecls) do return
  if isStateless then elabSrvPure (mkMarkerThmPure (c.subId `is_stateless))
  let some chanHeaders ← foldOptSrv b.chanClauses #[] (fun hs cc => Option.map hs.push <$> elabServerChannelHeader (hs.map (·.chStr)) cc) | return
  withReader (fun (c : SrvElabCtx) => { c with chanSigs := chanHeaders.map (·.sig) }) do
    let some (_, helperSigs, statefulHelperIds) ← elabHelpersLoop false b.helperClauses | return
    withReader (fun (c : SrvElabCtx) => { c with helpers := helperSigs, statefulHelperIds }) do
      let beforeRun? ← match b.beforeClause? with | none => pure none | some bc => match ← elabServerBeforeClause bc with | some br => pure (some br) | none => return
      let some (methodInfos, rpcWireMap, dispatchArms) ← foldOptSrv b.fnClauses (#[], {}, #[]) (fun (ms, wm, arms) fc => do
        let some (info, wireTys, arm) ← elabServerFnClause ms fc beforeRun? | return none
        return some (ms.push info, wm.insert info.name wireTys, arms.push arm)) | return
      let some (wsDispatchArms, wsProjectArms) ← foldOptSrv chanHeaders (#[], #[]) (fun (da, pa) hdr => do
        let some (cArms, pArm?) ← elabServerChannelBody hdr beforeRun? | return none
        return some (da ++ cArms, pArm?.elim pa pa.push)) | return
      let some (httpRoutes, httpDispatchArms) ← foldOptSrv b.httpClauses.zipIdx (#[], #[]) (fun (rts, arms) (hc, idx) => do
        let some (rt, arm) ← elabServerHttpRouteClause idx rts hc beforeRun? | return none
        return some (rts.push rt, arms.push arm)) | return
      let some jobNames ← elabServerJobs methodInfos b.jobClauses | return
      let elabHook? (lbl : String) (leaf : Name) (c? : Option Syntax) := match b.authDecl?, c? with | some (_, ai), some hc => Option.map some <$> elabServerAuthHook lbl leaf ai hc | _, _ => pure (some none)
      let some onCreateRun? ← elabHook? "onCreateAccount" `_onCreateAccount b.onCreateAccountClause? | return
      let some onSignInRun? ← elabHook? "onSignIn" `_onSignIn b.onSignInClause? | return
      elabServerDispatchCmds methodInfos dispatchArms (chanHeaders.map (·.chStr)) wsDispatchArms wsProjectArms httpDispatchArms jobNames onCreateRun? onSignInRun?
      checkAuthInvs b.routesAuthInvs (·.1) (fun x => s!"routes matching \"{x.2.1}\"") (fun (_, pfx, excs) => httpRoutes.filter fun r => r.2.1.startsWith pfx && !excs.contains r.2.1 && !r.2.2) (fun r => s!"`{r.1} {r.2.1}`")
      checkAuthInvs b.rpcsAuthInvs (·.1) (fun _ => "RPCs") (fun (_, excs) => methodInfos.filter fun m => !excs.contains m.name && !m.requiresAuth) (fun m => s!"`{m.name}`")
      elabSrvPureCmds do return (← mapPQ (b.routesAuthInvs.map (·.1) ++ b.rpcsAuthInvs.map (·.1)) fun id => mkMarkerThmPure (c.subId id.getId id)) ++ (← mkNoSecretsInvsPure c b.noSecretsInvs)
      elabSrvExamples false b.exampleClauses #[] rpcWireMap

@[noinline] private def elabServerOrServiceCore (isService : Bool) (priorRep priorUnrep : Nat) (stx : Syntax) : CommandElabM Unit := do
  let (isStateless, srvIdent, clausesStx) := if isService then (false, (⟨stx.getArg 2⟩ : Ident), stx.getArg 4) else ((stx.getArg 2).getNumArgs == 1, (⟨stx.getArg 3⟩ : Ident), stx.getArg 5)
  let srvName := srvIdent.getId; let b ← parseServerClauses srvIdent srvName clausesStx.getArgs (isService := isService)
  if isStateless then if let some (stId, _, _, _) := b.stateDecls[0]? then
    errAt stId s!"`server stateless {srvName}` forbids in-memory `state` field `{stId.getId}`; persist state in a `database` (`use db : ...`) or remove `stateless`"
  let initCtx : SrvElabCtx := {
    priorRep, priorUnrep, srvIdent, srvName, fullSrvName := (← getCurrNamespace) ++ srvName, hasState := !b.stateDecls.isEmpty,
    dbDecls := b.dbDecls, serviceDecls := b.serviceDecls, authDecl? := b.authDecl?, envDecls := b.envDecls,
    stateFieldNames := b.stateDecls.map (·.1.getId.toString), envVarNames := b.envDecls.map (·.ident.getId.toString),
    invs := b.invs, mutInvs := b.mutInvs, deferredProofs := ← IO.mkRef #[], extRootsRef := ← IO.mkRef #[] }
  (if isService then do
      let some (methodInfos, _, _) ← elabHelpersLoop true b.helperClauses | return
      let (reqSecrets, ownSecrets, usedExts, allDbs, allEnvs) ← collectServerSecretsAndExts
      elabSrvPureCmds do
        return #[← mkStrArrDefPure (initCtx.subId `secrets) reqSecrets, ← mkMarkerThmPure (initCtx.subId `_qed_service_marker)] ++ (← mkNoSecretsInvsPure initCtx b.noSecretsInvs)
      elabSrvExamples true b.exampleClauses methodInfos
      modifyEnv fun env => serviceRegistry.addEntry env { serviceName := initCtx.fullSrvName, shortName := srvName.toString, secrets := reqSecrets, ownSecrets, envVars := allEnvs, externalServices := usedExts, databases := allDbs, methods := methodInfos }
    else elabServerBody b isStateless).run initCtx
  discard <| foldlCmd (← initCtx.deferredProofs.get) true fun ok runProof => if ok then runProof else pure false

@[noinline, command_elab serverCmd] def elabServerCmd : CommandElab := fun stx => do
  withCmdRollback Qed.failedServerRegistry ((← getCurrNamespace) ++ (stx.getArg 3).getId) (elabServerOrServiceCore false · · stx)
@[noinline, command_elab serviceCmd] def elabServiceCmd : CommandElab := fun stx => do
  withCmdRollback Qed.Server.failedServiceRegistry ((← getCurrNamespace) ++ (stx.getArg 2).getId) (elabServerOrServiceCore true · · stx)

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

@[noinline] private def verifyFullstackRpcClosure (env : Environment) (fsName : Name) (srvInfo : ServerInfo) (cliIdent : Ident) (resolvedCli : Name) : CommandElabM Unit := do
  let rpcMap := (serverRegistry.getState env).foldl (init := ({} : NameMap (ServerInfo × ServerMethodInfo))) fun acc _ s =>
    s.methods.foldl (init := acc) fun a m => let a := if m.rawRpcConst != .anonymous then a.insert m.rawRpcConst (s, m) else a; a.insert (s.serverName ++ Name.mkSimple m.name) (s, m)
  let fsChanMap := (Qed.channelRegistry.getState env).foldl (init := ({} : NameMap Qed.ChannelInfo)) fun acc _ ch =>
    match ch.kind with | .fullstack .. => let a := if ch.subHelperConst != .anonymous then acc.insert ch.subHelperConst ch else acc; if ch.sendHelperConst != .anonymous then a.insert ch.sendHelperConst ch else a | _ => acc
  let visited ← match collectReachableDefns env 300000 [resolvedCli] {} with
    | .ok s => pure s | .error p => errAt cliIdent s!"`fullstack {fsName}`: RPC endpoint closure analysis exceeded fuel limit while inspecting `{p}`"
  for n in visited do
    if let some ch := fsChanMap.find? n then
      if ch.ownerName != srvInfo.serverName then errAt cliIdent s!"`fullstack {fsName}` mounts `server {srvInfo.shortName}`, but client `{cliIdent.getId}` subscribes to WebSocket channel `{ch.ownerShort}.{ch.channelName}` on unmounted server `{ch.ownerShort}`"
    if let some (otherSrv, mInfo) := rpcMap.find? n then
      if otherSrv.serverName != srvInfo.serverName then errAt cliIdent s!"`fullstack {fsName}` mounts `server {srvInfo.shortName}`, but client `{cliIdent.getId}` calls RPC `{otherSrv.shortName}.{mInfo.name}` on unmounted server `{otherSrv.shortName}`"
    let root := Qed.Diag.modRootOf env n
    if root != `Qed && root != `Js && root != `Cli then if let some (.defnInfo d) := env.find? n then
      let badRef ← IO.mkRef (none : Option String)
      d.value.forEach fun sub => do
        if (← badRef.get).isNone then if let .lit (.strVal s) := sub then if s.startsWith "/_qed/rpc/" then
          match (s.drop 10).toString.splitOn "/" with
          | [sp, mp] => if sp != srvInfo.shortName || !(srvInfo.methods.any (·.name == mp)) then badRef.set (some s)
          | _ => badRef.set (some s)
      if let some url ← badRef.get then
        errAt cliIdent s!"`fullstack {fsName}` mounts `server {srvInfo.shortName}` (methods: [{String.intercalate ", " (srvInfo.methods.toList.map (·.name))}]), but client `{cliIdent.getId}` targets invalid RPC endpoint `{url}`"

@[noinline, command_elab fullstackCmd] def elabFullstackCmd : CommandElab := fun stx => do
  let fsIdent : Ident := ⟨stx.getArg 1⟩; let (fsName, currNs) := (fsIdent.getId, ← getCurrNamespace)
  let (srvIdent?, cliIdent?, title?) ← foldlCmd (stx.getArg 3).getArgs ((none : Option Ident), (none : Option Ident), (none : Option String)) fun (s?, c?, t?) cl => do
    match cl.getKind with
    | `Qed.Server.fsServerClause => return (← setOptOnce s? cl "`server` clause in `fullstack`" (pure ⟨cl.getArg 1⟩), c?, t?)
    | `Qed.Server.fsClientClause => return (s?, ← setOptOnce c? cl "`client` clause in `fullstack`" (pure ⟨cl.getArg 1⟩), t?)
    | `Qed.Server.fsTitleClause  => return (s?, c?, ← setOptOnce t? cl "`title` clause in `fullstack`" (pure (⟨cl.getArg 1⟩ : TSyntax `str).getString))
    | _ => errAt cl "unexpected clause in `fullstack` block"
  let some srvIdent := srvIdent? | errAt fsIdent s!"`fullstack {fsName}` must specify `server <ServerName>`"
  let some cliIdent := cliIdent? | errAt fsIdent s!"`fullstack {fsName}` must specify `client <AppName>`"
  let (env, openDecls) := (← getEnv, ← getOpenDecls)
  let some srvInfo := Qed.Diag.lookupNameMapExt? serverRegistry env currNs openDecls srvIdent.getId
    | if (Qed.Diag.lookupNameMapExt? Qed.failedServerRegistry env currNs openDecls srvIdent.getId).isSome then return
      errAt srvIdent s!"unknown `server` `{srvIdent.getId}` in `fullstack {fsName}`"
  let cliTarget := resolveAppTargetIdent env currNs cliIdent
  let resolvedCli ← try liftCoreM <| realizeGlobalConstNoOverloadWithInfo cliTarget catch _ =>
    if ← liftCoreM (Qed.isFailedComponent cliIdent.getId) then return
    if (← liftCoreM (Qed.lookupComponent? cliIdent.getId)).isSome then errAt cliIdent s!"component `{cliIdent.getId}` in `fullstack {fsName}` is not a top-level mountable app (remove `prop`, `bind`, `children`, `event`, and uninitialized `state` fields)"
    else errAt cliIdent s!"unknown `client` `{cliIdent.getId}` in `fullstack {fsName}`; specify a top-level `component` or `Qed.App` value"
  elabPureCmd `(command| abbrev $(mkIdentFrom fsIdent (fsName ++ `clientApp)) := $cliTarget)
  let cliCompName := if resolvedCli.getString! == "app" then resolvedCli.getPrefix else resolvedCli
  verifyFullstackRpcClosure env fsName srvInfo cliIdent resolvedCli
  let pageTitle := title?.getD fsName.toString; let srvShortLit := Syntax.mkStrLit srvInfo.shortName
  elabPureCmds do
    let mut cmds : Array (TSyntax `command) := #[]
    if env.contains (cliCompName ++ `usedRpcs) then
      let (usedRpcsId, srvMethodsId, epThmId) := (mkIdentFrom cliIdent (cliCompName ++ `usedRpcs), mkIdentFrom srvIdent (srvInfo.serverName ++ `methods), mkIdentFrom fsIdent (fsName ++ `rpc_endpoints_valid))
      cmds := cmds ++ #[
        ← `(command| theorem $epThmId : ∀ ep ∈ $usedRpcsId, ep.1 = $srvShortLit ∧ ep.2 ∈ $srvMethodsId := by first | qedCloseGroundKernel | decide),
        ← `(command| theorem $(mkIdentFrom fsIdent (fsName ++ `ssr_rpc_closure_complete)) (dispatchMethod : String → ByteArray → Except String ByteArray) (ep : String × String) (hep : ep ∈ $usedRpcsId) (reqBody : ByteArray) :
            Qed.ssrDispatchRpc $srvShortLit $srvMethodsId dispatchMethod "POST" ("/_qed/rpc/" ++ ep.1 ++ "/" ++ ep.2) reqBody = dispatchMethod ep.2 reqBody :=
          Qed.ssr_rpc_closure_complete $srvShortLit $srvMethodsId $usedRpcsId $epThmId dispatchMethod (by decide) (by decide) ep hep reqBody)]
    if env.contains (cliCompName ++ `usedChannels) then
      cmds := cmds.push (← `(command| theorem $(mkIdentFrom fsIdent (fsName ++ `ws_endpoints_valid)) : ∀ ch ∈ $(mkIdentFrom cliIdent (cliCompName ++ `usedChannels)), ch.1 = $srvShortLit ∧ ch.2 ∈ $(mkIdentFrom srvIdent (srvInfo.serverName ++ `channels)) := by first | qedCloseGroundKernel | decide))
    return cmds.push (← `(command| def $(mkIdentFrom fsIdent (fsName ++ `title)) : String := $(Syntax.mkStrLit pageTitle)))
  modifyEnv fun e => fullstackRegistry.addEntry e { fullstackName := currNs ++ fsName, serverName := srvInfo.serverName, title := pageTitle }

@[noinline] private def mkServerMainCmdPure (fsIdent : Ident) (fsInfo : FullstackInfo) (srvInfo : ServerInfo) : PureQuotM (TSyntax `command) := do
  let srvId (leaf : Name) : Ident := mkIdentFrom fsIdent (srvInfo.serverName ++ leaf)
  let dbCfgIds : Array Term := srvInfo.databases.map (mkIdentFrom fsIdent ·)
  let wrapHandler (id : Ident) : PureQuotM Term := `(fun {m} [Monad m] [Qed.Server.MonadServer m] [Qed.Server.MonadAtomic _ m] => $id)
  let optHandler (on : Bool) (id : Ident) : PureQuotM Term := do mkOptTermPure (← if on then some <$> wrapHandler id else pure none)
  let (stDirId, portId, devId, wrkId, argsId) := (mkIdent `staticDir, mkIdent `port, mkIdent `devMode, mkIdent `numWorkers, mkIdent `args)
  let metaTerm ← mkAppC `Qed.Server.Native.FullstackMeta.mk #[
    quote fsInfo.title, quote srvInfo.shortName, srvId `secrets, portId, stDirId, devId, wrkId,
    ← mkOptTermPure (some (← mkArrLitPure (srvInfo.methods.filterMap fun m => if m.isAsync then some (Syntax.mkStrLit m.name) else none))),
    ← mkOptTermPure (srvInfo.authConfig?.map (mkIdentFrom fsIdent ·)), ← mkPairPure (quote srvInfo.hasOnCreateAccount) (quote srvInfo.hasOnSignIn),
    ← mkOptTermPure dbCfgIds[0]?, ← mkOptTermPure (if srvInfo.hasWsProject then some (srvId `wsProject) else none)]
  let runnerCall ← mkAppC `Qed.Server.Native.runStatefulFullstack #[
    mkIdentFrom fsIdent (fsInfo.fullstackName ++ `clientApp), metaTerm,
    ← if srvInfo.hasState then pure (srvId `initState : Term) else mkAscribePure (mkCIdent ``Unit.unit) (mkCIdent ``Unit),
    ← wrapHandler (srvId `dispatchM), ← optHandler (!srvInfo.channels.isEmpty) (srvId `wsDispatchM),
    ← optHandler srvInfo.hasHttpRoutes (srvId `httpDispatchM), ← if srvInfo.jobs.isEmpty then mkArrLitPure #[] else pure (srvId `jobs : Term),
    ← optHandler (srvInfo.hasOnCreateAccount || srvInfo.hasOnSignIn) (srvId `authHookM)]
  let (initDbCheck, parseCli) := (← if dbCfgIds.isEmpty then mkAppC ``Pure.pure #[mkCIdent ``Bool.true] else mkAppC `Qed.Server.Native.initDatabases #[← mkArrLitPure dbCfgIds], ← mkAppC `Qed.Server.Native.parseServerCliArgs #[argsId])
  `(command| def $(mkIdent `main):ident ($argsId:ident : List String) : IO UInt32 := do
    let ($stDirId:ident, $portId:ident, $devId:ident, $wrkId:ident) ← $parseCli:term
    if !(← $initDbCheck:term) then return 1
    $runnerCall:term)

@[noinline, command_elab qedServerMainCmd] def elabQedServerMain : CommandElab := fun stx => do
  let fsIdent : Ident := ⟨stx[1]⟩; let (env, currNs) := (← getEnv, ← getCurrNamespace)
  let some fsInfo := (Qed.Diag.lookupNameMapExt? fullstackRegistry env currNs (← getOpenDecls) fsIdent.getId).orElse (fun _ =>
      (fullstackRegistry.getState env).toList.findSome? fun (k, v) => if k.getString! == fsIdent.getId.toString then some v else none)
    | errAt fsIdent s!"unknown `fullstack` declaration `{fsIdent.getId}`"
  let some srvInfo := (serverRegistry.getState env).find? fsInfo.serverName
    | errAt fsIdent s!"internal error: `server` `{fsInfo.serverName}` not found in registry"
  elabPureCmd (mkServerMainCmdPure fsIdent fsInfo srvInfo)

end ServerFullElab
end Qed.Server
