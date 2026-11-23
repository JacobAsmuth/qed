import Qed.Component.AwaitLift
import Qed.Speculative.Core
import Qed.Server.Invariant

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

/-! ## Speculative Prediction Lowering & `_specClassify` Codegen -/

private def lowerPredictExpr (stx : Syntax) : CommandElabM Term :=
  liftMacroM <| Qed.Lang.lowerSimpleQedExpr .val stx
    (wrapNamedField := fun t => pure ⟨Syntax.node .none ``Qed.Server.srvAutoFieldStx #[Syntax.atom .none "srvAutoField(", t.raw, Syntax.atom .none ")"]⟩)
    (lowerIndex? := some fun _ arrT idxT mode =>
      Qed.Lang.finishTermMode mode ⟨Syntax.node .none ``Qed.Server.srvGetElemStx #[Syntax.atom .none "srvGetElem(", arrT.raw, Syntax.atom .none ", ", idxT.raw, Syntax.atom .none ")"]⟩)

private partial def lowerPredictStmts (wrapVal : Term → CommandElabM Term) : List Syntax → CommandElabM Term
  | [] => `(Option.none)
  | st :: rest => do
      let k := st.getKind
      if k == ``qedStmtPass then lowerPredictStmts wrapVal rest
      else if k == ``qedStmtReturn then
        if (st.getArg 1).getNumArgs == 0 then `(Option.none) else `(Option.some ($(← wrapVal (← lowerPredictExpr ((st.getArg 1).getArg 0)))))
      else if k == ``qedStmtLet then lowerLetStmt st lowerPredictExpr (← lowerPredictStmts wrapVal rest)
      else if k == ``qedStmtIf || k == ``qedStmtIfLet || k == ``qedStmtMatch then
        let passTail := !rest.isEmpty && hasReturnStmt st
        let brTerm ← lowerControlFlowStmt st lowerPredictExpr fun seq => lowerPredictStmts wrapVal (seq.toList ++ if passTail then rest else [])
        if passTail || rest.isEmpty then return brTerm
        else `(match $brTerm:term with | Option.some _pv => Option.some _pv | Option.none => $(← lowerPredictStmts wrapVal rest))
      else throwErrorAt st "`predict:` only supports pure `let`, `if`, `if let`, `match`, `pass`, and `return`"

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

end CompElab
end Qed
