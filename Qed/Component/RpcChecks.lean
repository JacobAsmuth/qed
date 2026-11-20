import Qed.Component.AwaitLift
import Qed.Server.Invariant

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

structure PendingRpcCheck where
  callRef      : Syntax
  srvShort     : String
  methodName   : String
  reqConst?    : Option Name
  reqLabel     : String
  requiresAuth : Bool
  argExprs     : Array Expr
  lctx         : LocalContext
  localInsts   : LocalInstances
  mctx         : MetavarContext
  sessionVar?  : Option Name

structure PendingPredictCheck where
  callRef    : Syntax
  srvShort   : String
  methodName : String
  ensConst   : Name
  isOptWrap  : Bool
  argExprs   : Array Expr
  predExpr   : Expr
  lctx       : LocalContext
  localInsts : LocalInstances
  mctx       : MetavarContext

initialize pendingRpcChecks : IO.Ref (Array PendingRpcCheck) ← IO.mkRef #[]
initialize pendingPredictChecks : IO.Ref (Array PendingPredictCheck) ← IO.mkRef #[]
initialize currentCompSessionRef : IO.Ref (Option Ident) ← IO.mkRef none



open Lean Elab Term Meta in
@[term_elab qedCheckRpcCallTerm]
def elabQedCheckRpcCall : TermElab := fun stx expectedType? => do
  let srvId : Ident := ⟨(stx.getArg 1)⟩
  let methId : Ident := ⟨(stx.getArg 2)⟩
  let argTerms : Array Term := (stx.getArg 4).getSepArgs.map (⟨·⟩)
  let cbTerm : Term := ⟨(stx.getArg 6)⟩
  let srvName := srvId.getId
  let methStr := methId.getId.toString
  let env ← getEnv
  let some srvInfo := (serverRegistry.getState env).find? srvName
    | throwErrorAt stx s!"internal: unknown server `{srvName}` in RPC check"
  let some mInfo := srvInfo.methods.find? (·.name == methStr)
    | throwErrorAt stx s!"internal: unknown method `{methStr}` on `{srvName}` in RPC check"
  let rawRpcId := mkIdentFrom stx mInfo.rawRpcConst
  let callApp ← argTerms.foldlM (init := (rawRpcId : Term)) fun acc a => `($acc $a)
  let fullCall ← `($callApp $cbTerm)
  let resExpr ← elabTerm fullCall expectedType?
  let resExpr ← instantiateMVars resExpr
  let mut argExprs : Array Expr := #[]
  let fnArgs := resExpr.getAppArgs
  if resExpr.isAppOf mInfo.rawRpcConst && fnArgs.size ≥ 2 + mInfo.paramCount then
    for i in [0:mInfo.paramCount] do
      argExprs := argExprs.push (← instantiateMVars fnArgs[2 + i]!)
  else
    for (aT, i) in argTerms.zipIdx do
      let pTy := Lean.mkConst mInfo.paramTypeConsts[i]!
      argExprs := argExprs.push (← instantiateMVars (← elabTermEnsuringType aT pTy))
  if mInfo.hasClientReq || mInfo.requiresAuth then
    let lctx ← getLCtx
    let localInsts ← getLocalInstances
    let mctx ← getMCtx
    let sessionId? ← currentCompSessionRef.get
    pendingRpcChecks.modify (·.push {
      callRef := stx
      srvShort := srvInfo.shortName
      methodName := mInfo.name
      reqConst? := mInfo.clientReqConst
      reqLabel := mInfo.clientReqLabel
      requiresAuth := mInfo.requiresAuth
      argExprs
      lctx
      localInsts
      mctx
      sessionVar? := sessionId?.map (·.getId)
    })
  return resExpr

open Lean Elab Term Meta in
@[term_elab qedCheckPredictTerm]
def elabQedCheckPredict : TermElab := fun stx expectedType? => do
  let srvId : Ident := ⟨(stx.getArg 1)⟩
  let methId : Ident := ⟨(stx.getArg 2)⟩
  let argTerms : Array Term := (stx.getArg 4).getSepArgs.map (⟨·⟩)
  let predTerm : Term := ⟨(stx.getArg 6)⟩
  let srvName := srvId.getId
  let methStr := methId.getId.toString
  let env ← getEnv
  let some srvInfo := (serverRegistry.getState env).find? srvName
    | throwErrorAt stx s!"internal: unknown server `{srvName}` in predict check"
  let some mInfo := srvInfo.methods.find? (·.name == methStr)
    | throwErrorAt stx s!"internal: unknown method `{methStr}` on `{srvName}` in predict check"
  let predExpr ← elabTerm predTerm expectedType?
  synthesizeSyntheticMVarsNoPostponing
  let predExpr ← instantiateMVars predExpr
  if mInfo.hasEnsures then
    if let some ensConst := mInfo.ensPredConst then
      let mut argExprs : Array Expr := #[]
      for (aT, i) in argTerms.zipIdx do
        let pTy := Lean.mkConst mInfo.paramTypeConsts[i]!
        argExprs := argExprs.push (← instantiateMVars (← elabTermEnsuringType aT pTy))
      let predTy ← Meta.whnf (← Meta.inferType predExpr)
      let isOptWrap := mInfo.isOption && predTy.isAppOfArity ``Option 1
      pendingPredictChecks.modify (·.push {
        callRef := stx
        srvShort := srvInfo.shortName
        methodName := mInfo.name
        ensConst
        isOptWrap
        argExprs
        predExpr
        lctx := ← getLCtx
        localInsts := ← getLocalInstances
        mctx := ← getMCtx
      })
  return predExpr

open Lean Elab Meta in
def verifyPendingRpcChecks (spec : ComponentSpec) (invPreds : Array Term) :
    CommandElabM Unit := do
  let checks ← pendingRpcChecks.get
  let predChecks ← pendingPredictChecks.get
  if checks.isEmpty && predChecks.isEmpty then return
  let stateConstName ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent (spec.t.getId ++ `State))
  let buildInvProps (lctx : LocalContext) : TermElabM (Array Expr × Option Expr) := do
    let mut invProps : Array Expr := #[]
    let mut stateFVar? : Option Expr := none
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isLet then
        if (← Meta.whnf decl.type).isConstOf stateConstName then
          if stateFVar?.isNone then stateFVar? := some decl.toExpr
          let fnTy := Expr.forallE `_ (Lean.mkConst stateConstName) (Expr.sort Level.zero) .default
          for predT in invPreds do
            let predExpr ← Term.elabTermEnsuringType predT fnTy
            Term.synthesizeSyntheticMVarsNoPostponing
            let predExpr ← instantiateMVars predExpr
            invProps := invProps.push ((Expr.app predExpr decl.toExpr).headBeta)
    return (invProps, stateFVar?)
  let cleanGoalExpr (e : Expr) : MetaM String := do
    let e ← instantiateMVars e
    let e ← Meta.zetaReduce e
    Qed.Diag.ppQedExpr e ["m"]
  let tryDischargeWith (invProps : Array Expr) (goalBody : Expr) : TermElabM (Option String) := do
    let fullGoal ← invProps.foldrM (init := goalBody) fun hyp acc =>
      pure (Expr.forallE `_ hyp acc .default)
    let fullGoal ← instantiateMVars fullGoal
    let mv ← Meta.mkFreshExprSyntheticOpaqueMVar fullGoal
    try
      let unsolved ← Tactic.run mv.mvarId! do
        Tactic.evalTactic (← `(tactic| intros; qedProveRpcReq))
      if unsolved.isEmpty then return none
      let msg ← unsolved[0]!.withContext do cleanGoalExpr (← unsolved[0]!.getType)
      return some msg
    catch _ =>
      let reduced := (← Meta.unfoldDefinition? goalBody).getD goalBody
      return some (← cleanGoalExpr reduced)
  let mkProofLctx (lctx : LocalContext) : LocalContext :=
    lctx.foldl (init := {}) fun acc decl =>
      if decl.isAuxDecl then acc
      else match decl with
      | .ldecl _ fv nm ty val _ k => acc.mkLetDecl fv nm ty val (nondep := false) (kind := k)
      | .cdecl _ fv nm ty bi k    => acc.mkLocalDecl fv nm ty bi (kind := k)
  for chk in checks do
    liftTermElabM do
      Meta.withMCtx chk.mctx <| withLCtx (mkProofLctx chk.lctx) chk.localInsts do
        let (invProps, stateFVar?) ← buildInvProps chk.lctx
        let tryDischarge := tryDischargeWith invProps
        if chk.requiresAuth then
          let some sfName := chk.sessionVar?
            | throwErrorAt chk.callRef m!"RPC `{chk.srvShort}.{chk.methodName}` requires an authenticated session (`ctx.userId != none`), but `{spec.t.getId}` has no `session` field.\n\nHint: Add `session user` to `{spec.t.getId}` and guard the call with `if user.isSome:`."
          let sfExpr : Expr ←
            match chk.lctx.findDecl? fun decl =>
                if !decl.isImplementationDetail && decl.userName.eraseMacroScopes == sfName then some decl.toExpr else none with
            | some e => pure e
            | none =>
                let some sFVar := stateFVar?
                  | throwErrorAt chk.callRef m!"internal: could not locate component state while checking session auth for `{chk.srvShort}.{chk.methodName}`"
                Meta.mkProjection sFVar sfName
          let sfTy ← Meta.whnf (← Meta.inferType sfExpr)
          let elemTy := if sfTy.isAppOfArity ``Option 1 then sfTy.appArg! else Lean.mkConst ``String
          let noneExpr ← Meta.mkAppOptM ``Option.none #[some elemTy]
          let authGoal ← Meta.mkAppM ``Ne #[sfExpr, noneExpr]
          if (← tryDischarge authGoal).isSome then
            throwErrorAt chk.callRef m!"RPC `{chk.srvShort}.{chk.methodName}` requires an authenticated session (`{sfName} != none`), which could not be proved here.\n\nHint: Guard this call with `if {sfName}.isSome:`, `ensure {sfName}.isSome else return`, or `invariant ...: {sfName}.isSome`."
        if let some reqConst := chk.reqConst? then
          let reqGoal := mkAppN (Lean.mkConst reqConst) chk.argExprs
          if let some obl ← tryDischarge reqGoal then
            let oblLine := if obl.isEmpty then "" else s!"\n  • must satisfy:  {obl}"
            throwErrorAt chk.callRef m!"RPC `{chk.srvShort}.{chk.methodName}` precondition `{chk.reqLabel}` could not be proved here:{oblLine}\n\nHint: Pass valid arguments, guard with `if`/`ensure`, or add a component `invariant`."
  let currNs ← getCurrNamespace
  for (chk, idx) in predChecks.zipIdx do
    liftTermElabM do
      let proofLctx := mkProofLctx chk.lctx
      Meta.withMCtx chk.mctx <| withLCtx proofLctx chk.localInsts do
        let (invProps, _) ← buildInvProps chk.lctx
        let ensGoal : Expr ←
          if chk.isOptWrap then
            let predTy ← Meta.whnf (← Meta.inferType chk.predExpr)
            let innerTy := predTy.appArg!
            Meta.withLocalDeclD `_predInner innerTy fun vFVar => do
              let someV ← Meta.mkAppOptM ``Option.some #[some innerTy, some vFVar]
              let eqHyp ← Meta.mkEq chk.predExpr someV
              let body := mkAppN (Lean.mkConst chk.ensConst) (chk.argExprs.push vFVar)
              Meta.mkForallFVars #[vFVar] (Expr.forallE `_hPredSome eqHyp body .default)
          else
            pure (mkAppN (Lean.mkConst chk.ensConst) (chk.argExprs.push chk.predExpr))
        let ensId := mkIdent (`_root_ ++ chk.ensConst)
        let fullGoal ← invProps.foldrM (init := ensGoal) fun hyp acc =>
          pure (Expr.forallE `_ hyp acc .default)
        let fullGoal ← instantiateMVars fullGoal
        let mv ← Meta.mkFreshExprSyntheticOpaqueMVar fullGoal
        let obl? : Option String ← try
            let unsolved ← Tactic.run mv.mvarId! do
              Tactic.evalTactic (← `(tactic| intros; try simp only [$ensId:ident]; try qedProveRpcReq))
            if unsolved.isEmpty then
              -- Submit the complete proof term directly to Lean's kernel as a verified theorem
              -- so it is typechecked by the kernel and audited by `qed check`.
              let fvars := proofLctx.foldl (init := #[]) fun acc d =>
                if d.isAuxDecl then acc else acc.push d.toExpr
              let proofVal ← instantiateMVars mv
              let closedType ← instantiateMVars (← Meta.mkForallFVars (usedOnly := false) (usedLetOnly := false) fvars fullGoal)
              let closedVal ← instantiateMVars (← Meta.mkLambdaFVars (usedOnly := false) (usedLetOnly := false) fvars proofVal)
              let levelParams := (collectLevelParams (collectLevelParams {} closedType) closedVal).params.toList
              let thmName := currNs ++ spec.t.getId ++ Name.mkSimple s!"_specPredict_ens_{idx}"
              Lean.addDecl (.thmDecl {
                name := thmName
                levelParams
                type := closedType
                value := closedVal
              })
              pure none
            else
              let msg ← unsolved[0]!.withContext do cleanGoalExpr (← unsolved[0]!.getType)
              pure (some msg)
          catch _ =>
            let reduced := (← Meta.unfold ensGoal chk.ensConst).expr
            pure (some (← cleanGoalExpr reduced))
        if let some obl := obl? then
          let oblLine := if obl.isEmpty then "" else s!"\n  • must satisfy:  {obl}"
          throwErrorAt chk.callRef m!"Predicted response for `{chk.srvShort}.{chk.methodName}` does not satisfy server `ensures` postcondition:{oblLine}\n\nHint: Ensure the predicted value satisfies the server method's `ensures` clause (or guard it inside a `predict:` block)."

open Lean Elab Term Meta in
private def elabAndRecordChanCheck (stx : Syntax) (expectedType? : Option Expr)
    (argTerms : Array Term) (slotLit : TSyntax `str)
    (helperConst : Name) (paramCount : Nat) (paramTypeConsts : Array Name)
    (trailingArgs : Array Term) (srvShort methodName : String)
    (reqConst? : Option Name) (reqLabel : String) (requiresAuth : Bool) : TermElabM Expr := do
  let fnId := mkIdentFrom stx helperConst
  let mut fullCall : Term ← `($fnId $slotLit)
  for a in argTerms do
    fullCall ← `($fullCall ($a))
  for t in trailingArgs do
    fullCall ← `($fullCall ($t))
  let resExpr ← instantiateMVars (← elabTerm fullCall expectedType?)
  let mut argExprs : Array Expr := #[]
  let fnArgs := resExpr.getAppArgs
  if resExpr.isAppOf helperConst && fnArgs.size ≥ 2 + paramCount then
    for i in [0:paramCount] do
      argExprs := argExprs.push (← instantiateMVars fnArgs[2 + i]!)
  else
    for (aT, i) in argTerms.zipIdx do
      argExprs := argExprs.push (← instantiateMVars (← elabTermEnsuringType aT (Lean.mkConst paramTypeConsts[i]!)))
  if reqConst?.isSome || requiresAuth then
    pendingRpcChecks.modify (·.push {
      callRef := stx, srvShort, methodName, reqConst?, reqLabel, requiresAuth, argExprs,
      lctx := ← getLCtx, localInsts := ← getLocalInstances, mctx := ← getMCtx,
      sessionVar? := (← currentCompSessionRef.get).map (·.getId)
    })
  return resExpr

open Lean Elab Term Meta in
@[term_elab qedCheckChanSubTerm]
def elabCheckChanSub : TermElab := fun stx expectedType? => do
  let chFullName := (stx.getArg 1).getId
  let some chInfo := (Qed.channelRegistry.getState (← getEnv)).find? chFullName
    | throwErrorAt stx s!"internal: unknown channel `{chFullName}` in subscription check"
  elabAndRecordChanCheck stx expectedType? ((stx.getArg 3).getSepArgs.map (⟨·⟩)) ⟨(stx.getArg 5)⟩
    chInfo.subHelperConst chInfo.paramCount chInfo.paramTypeConsts
    #[⟨(stx.getArg 7)⟩, ⟨(stx.getArg 9)⟩, ⟨(stx.getArg 11)⟩, ⟨(stx.getArg 13)⟩]
    chInfo.ownerShort chInfo.channelName chInfo.clientReqConst chInfo.clientReqLabel chInfo.requiresAuth

open Lean Elab Term Meta in
@[term_elab qedCheckChanSendTerm]
def elabCheckChanSend : TermElab := fun stx expectedType? => do
  let chFullName := (stx.getArg 1).getId
  let some chInfo := (Qed.channelRegistry.getState (← getEnv)).find? chFullName
    | throwErrorAt stx s!"internal: unknown channel `{chFullName}` in send check"
  elabAndRecordChanCheck stx expectedType? ((stx.getArg 3).getSepArgs.map (⟨·⟩)) ⟨(stx.getArg 5)⟩
    chInfo.sendHelperConst chInfo.sendParamCount chInfo.sendParamTypeConsts #[]
    chInfo.ownerShort s!"{chInfo.channelName}.send" chInfo.sendReqConst chInfo.sendReqLabel false


end CompElab
end Qed
