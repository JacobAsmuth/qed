import Qed.Component.AwaitLift
import Qed.Speculative.Core
import Qed.Server.Invariant

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

/-! ## Speculative Prediction Lowering & `_specClassify` Codegen -/

private def lowerPredictExpr (stx : Syntax) : CommandElabM Term :=
  liftMacroM <| Qed.Lang.lowerSimpleQedExpr .val stx
    (wrapNamedField := fun t =>
      pure ⟨Syntax.node .none ``Qed.Server.srvAutoFieldStx #[Syntax.atom .none "srvAutoField(", t.raw, Syntax.atom .none ")"]⟩)
    (lowerIndex? := some fun _ arrT idxT mode => do
      let elem : Term := ⟨Syntax.node .none ``Qed.Server.srvGetElemStx
        #[Syntax.atom .none "srvGetElem(", arrT.raw, Syntax.atom .none ", ", idxT.raw, Syntax.atom .none ")"]⟩
      Qed.Lang.finishTermMode mode elem)

private partial def lowerPredictStmts (wrapVal : Term → CommandElabM Term) :
    List Syntax → CommandElabM Term
  | [] => `(Option.none)
  | st :: rest => do
      let k := st.getKind
      if k == ``qedStmtPass then
        lowerPredictStmts wrapVal rest
      else if k == ``qedStmtReturn then
        if (st.getArg 1).getNumArgs == 0 then
          `(Option.none)
        else
          let valT ← lowerPredictExpr ((st.getArg 1).getArg 0)
          let checked ← wrapVal valT
          `(Option.some ($checked))
      else if k == ``qedStmtLet then
        lowerLetStmt st lowerPredictExpr (← lowerPredictStmts wrapVal rest)
      else if k == ``qedStmtIf || k == ``qedStmtIfLet || k == ``qedStmtMatch then
        let passTail := !rest.isEmpty && hasReturnStmt st
        let tailStmts := if passTail then rest else []
        let brTerm ← lowerControlFlowStmt st lowerPredictExpr fun seq =>
          lowerPredictStmts wrapVal (seq.toList ++ tailStmts)
        if passTail || rest.isEmpty then
          return brTerm
        else
          let restT ← lowerPredictStmts wrapVal rest
          `(match $brTerm:term with | Option.some _pv => Option.some _pv | Option.none => $restT)
      else
        throwErrorAt st "`predict:` only supports pure `let`, `if`, `if let`, `match`, `pass`, and `return`"

private def compileSpecDispatchNode (spec : ComponentSpec) (node : SpecDispatchNode) : CommandElabM Term := do
  let tId := spec.t.getId
  let srvId := mkIdentFrom node.ref node.srvInfo.serverName
  let methId := mkIdentFrom node.ref (Name.mkSimple node.mInfo.name)
  let mut hoistDefs : Array (Ident × Term × Term) := #[]
  let mut allCapturedArgs : Array Term := node.capturedArgs
  let mut rpcArgs : Array Term := #[]
  for i in [0:node.rpcArgExprs.size] do
    let argT := node.rpcArgExprs[i]!
    if node.rpcArgNeedHoist[i]! then
      let tmpId := mkIdentFrom argT.raw (Name.mkSimple s!"_rpcArg_{node.kIdx}_{i}")
      let paramTyId := mkIdentFrom argT.raw node.mInfo.paramTypeConsts[i]!
      hoistDefs := hoistDefs.push (tmpId, paramTyId, argT)
      allCapturedArgs := allCapturedArgs.push tmpId
      rpcArgs := rpcArgs.push tmpId
    else
      rpcArgs := rpcArgs.push argT

  let wrapVal (valT : Term) : CommandElabM Term := do
    if node.mInfo.hasEnsures then
      withRef node.ref `(qedCheckPredict% $srvId:ident $methId:ident [$[$rpcArgs:term],*] ($valT : $(node.predValTy)))
    else
      `(($valT : $(node.predValTy)))

  let predOptTerm ← match node.predBody with
    | .expr eStx =>
        let v ← wrapVal (← lowerPredictExpr eStx)
        `(Option.some ($v))
    | .block pStmts =>
        lowerPredictStmts wrapVal pStmts.toList

  let preMsgOpt : Term ← match node.preCtor? with
    | none => `(Option.none)
    | some preCtor =>
        let preId := mkIdentFrom node.ref (tId ++ `Msg ++ preCtor)
        let preCall ← node.preArgs.foldlM (init := (preId : Term)) fun acc a => `($acc $a)
        `(Option.some ($preCall))

  let contId := mkIdentFrom node.ref (tId ++ `Msg ++ node.contCtor)
  let contBase ← allCapturedArgs.foldlM (init := (contId : Term)) fun acc a => `($acc $a)
  let resId := mkIdentFrom node.ref (tId ++ `Msg ++ node.resCtor)
  let txVar := mkIdent `_specTxId
  let predVar := mkIdent `_specPredVal
  let resCb ← (allCapturedArgs.push (predVar : Term)).foldlM
    (init := ← `($resId $txVar)) fun acc a => `($acc $a)
  let rpcCall ← withRef node.ref `(qedCheckRpcCall% $srvId:ident $methId:ident [$[$rpcArgs:term],*] $resCb)

  let mkDisp (arg : Term) : CommandElabM Term :=
    `(Qed.SpecAction.dispatch $preMsgOpt Qed.Cmd.none ($contBase $arg) (fun $txVar:ident => $rpcCall))
  let dispatchBody ← match ensuredWrapKind node.mInfo node.catchHasNone with
    | .plain => mkDisp predVar
    | wrap =>
        let some ensConst := node.mInfo.ensPredConst
          | throwErrorAt node.ref "internal: missing server `ensures` predicate in `predict`"
        let ensApp ← rpcArgs.foldlM (init := (mkIdent ensConst : Term)) fun acc a => `($acc $a)
        if wrap == .optEnsured then
          let innerTy := node.innerEnsTy?.getD node.predValTy
          let dNone ← mkDisp (← `((Option.none : Option (Qed.Ensured $innerTy ($ensApp)))))
          let dSome ← mkDisp (← `(Option.some (Qed.Ensured.mk _pv _hSpecEns)))
          `(match $predVar:ident with
            | Option.none => $dNone
            | Option.some _pv => if _hSpecEns : ($ensApp) _pv then $dSome else Qed.SpecAction.normal)
        else
          let dVal ← mkDisp (← `(Qed.Ensured.mk $predVar:ident _hSpecEns))
          `(if _hSpecEns : ($ensApp) $predVar:ident then $dVal else Qed.SpecAction.normal)

  let matched ← `(match ($predOptTerm : Option $(node.predValTy)) with
    | Option.none => Qed.SpecAction.normal
    | Option.some $predVar:ident => $dispatchBody)

  hoistDefs.foldrM (init := matched) fun (tmpId, pTy, argT) acc =>
    `(let $tmpId:ident : $pTy := $argT; $acc)

private partial def compileClassifyStmts (spec : ComponentSpec) : List Syntax → CommandElabM Term
  | [] => `(Qed.SpecAction.normal)
  | st :: rest => do
      if let some idx := matchSpecDispatchMarker? st then
        return ← compileSpecDispatchNode spec spec.specNodes[idx]!
      let k := st.getKind
      if k == ``qedStmtPass then
        compileClassifyStmts spec rest
      else if k == ``qedStmtLet then
        lowerLetStmt st (lowerCompExpr .val) (← compileClassifyStmts spec rest)
      else if k == ``qedStmtIf || k == ``qedStmtIfLet || k == ``qedStmtMatch then
        lowerControlFlowStmt st (lowerCompExpr .val) fun seq => compileClassifyStmts spec seq.toList
      else if let some (_, wrap) ← lowerMutStmt? spec st false then
        wrap (← compileClassifyStmts spec rest)
      else
        compileClassifyStmts spec rest

def mkSpecClassifyCmds (spec : ComponentSpec) : CommandElabM (Array (TSyntax `command)) := do
  if !spec.hasSpeculative then return #[]
  let tId := spec.t.getId
  let stateId := mkIdent (tId ++ `State)
  let msgId := mkIdent (tId ++ `Msg)
  let updateId := mkIdent (tId ++ `update)
  let clsId := mkIdent (tId ++ `_specClassify)
  let pureId := mkIdent (tId ++ `specClassify_pure)
  let mut arms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]

  for da in spec.specDispatches do
    let cFull := mkIdent (tId ++ `Msg ++ da.ctor)
    let paramNames := da.params.map (·.1.getId.eraseMacroScopes)
    let mut rhs ← compileClassifyStmts spec da.stmts.toList
    rhs ← bindMentionedFields spec (fun g => !paramNames.contains g && mentionsIdent rhs.raw g) rhs
    if !da.params.isEmpty then
      let ids : Array Term := da.params.map (⟨·.1.raw⟩)
      arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $ids* => $rhs))
    else
      arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $cFull:ident => $rhs))

  for rs in spec.specResolves do
    let cFull := mkIdent (tId ++ `Msg ++ rs.resCtor)
    let txId := rs.txIdParam
    let capIds : Array Term := rs.capturedParams.map (⟨·.1.raw⟩)
    let predId := rs.predParam
    let outId := rs.outParam
    let allPatIds : Array Term := #[⟨txId.raw⟩] ++ capIds ++ #[⟨predId.raw⟩, ⟨outId.raw⟩]

    let outcomePrefix := if rs.mInfo.domainErrTags.isEmpty then `Qed.RpcSimpleOutcome else `Qed.RpcOutcome
    let okCtorId := mkIdent (outcomePrefix ++ `ok)
    let vId := mkIdent `_specOkVal

    let mkCtorApp (ctorNm : Name) (extraArg : Term) : CommandElabM Term := do
      let cid := mkIdent (tId ++ `Msg ++ ctorNm)
      let base ← capIds.foldlM (init := (cid : Term)) fun acc a => `($acc $a)
      `($base $extraArg)

    let contMsg ← mkCtorApp rs.contCtor ⟨vId.raw⟩
    let confirmMsg? ← rs.confirmCtor?.mapM fun cn => mkCtorApp cn ⟨vId.raw⟩
    let rollbackMsg? ← rs.rollbackCtor?.mapM fun rn => mkCtorApp rn ⟨vId.raw⟩
    let catchMsg? ← rs.catchCtor?.mapM fun cn => mkCtorApp cn ⟨outId.raw⟩

    let okReplList ← match confirmMsg? with
      | some cm => `([$contMsg, $cm])
      | none    => `([$contMsg])
    let confirmOnHitList ← match confirmMsg? with
      | some cm => `([$cm])
      | none    => `(([] : List $msgId))
    let missReplList ← match rollbackMsg? with
      | some rm => `([$rm])
      | none    => pure okReplList
    let errReplList ← match catchMsg? with
      | some cm => `([$cm])
      | none    => `(([] : List $msgId))

    let rawValTerm ← match ensuredWrapKind rs.mInfo rs.catchHasNone with
      | .optEnsured => `(($vId).map Qed.Ensured.val)
      | .ensured    => `(($vId).val)
      | .plain      => `($vId)

    let okBranchBody ← `(
      if (Qed.SpecEq.eq $rawValTerm $predId) then
        Qed.SpecAction.resolve $txId true $okReplList $confirmOnHitList
      else
        Qed.SpecAction.resolve $txId false $missReplList ([] : List $msgId))

    let matchTerm ←
      if rs.mInfo.isOption && rs.catchHasNone then
        `(match $outId:ident with
          | $okCtorId (Option.some $vId:ident) => $okBranchBody
          | _ => Qed.SpecAction.resolve $txId false $errReplList ([] : List $msgId))
      else
        `(match $outId:ident with
          | $okCtorId $vId:ident => $okBranchBody
          | _ => Qed.SpecAction.resolve $txId false $errReplList ([] : List $msgId))

    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $allPatIds* => $matchTerm))

  arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | _ => Qed.SpecAction.normal))
  return #[
    ← `(command|
      set_option linter.unusedVariables false in
      def $clsId (s : $stateId) : $msgId → Qed.SpecAction $msgId :=
        fun m => match m with $[$arms:matchAlt]*),
    ← `(command|
      set_option linter.unusedVariables false in
      theorem $pureId (s : $stateId) (m : $msgId)
          (preMsg? : Option $msgId) (preCmd : Qed.Cmd $msgId)
          (specMsg : $msgId) (rpcCmd : Nat → Qed.Cmd $msgId)
          (h : $clsId s m = Qed.SpecAction.dispatch preMsg? preCmd specMsg rpcCmd) :
          ∀ s', ($updateId s' specMsg).2 = Qed.Cmd.none := by
        intro s'
        unfold $clsId at h
        cases m <;> dsimp only at h
        all_goals
          repeat (first
            | (injection h with _ _ _hspec _; subst _hspec; dsimp only [$updateId:ident];
               repeat (first | rfl | (split <;> try dsimp only)))
            | (cases h)
            | (split at h <;> try dsimp only at h)))
  ]


end CompElab
end Qed
