import Qed.Component.AwaitLift
import Qed.Invariant.State
import Qed.Invariant.ForEach
import Qed.Invariant.Reachability

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

def resolveInvIdent (invStx : Syntax) (compId : Name) : Ident :=
  let idStx := (invStx.getArg 1).getArg 0; mkIdentFrom idStx (compId ++ idStx.getId)

/-- Elaborate a generated component verification theorem with an isolated heartbeat budget
    so large component definitions do not starve their `invariant` or `example` clauses. -/
def elabIsolatedTheorem (cmd : CmdStx) : CommandElabM Unit := do
  let saved ← IO.getNumHeartbeats; IO.setNumHeartbeats 0
  try elabCommand cmd finally IO.setNumHeartbeats saved

/-! ## Inline Invariant Elaboration -/

def mkViewPredAndStr (invStx : Syntax) (rawClauses : Array Syntax) (clauses : Array Term) (emptyMsg : String) : CommandElabM (Term × String) := do
  let vPred ← match clauses.toList with
    | [p] => pure p
    | p :: ps => runPureQuot (ps.foldlM (init := p) fun acc q => `(Qed.both $acc $q))
    | [] => throwErrorAt invStx emptyMsg
  return (vPred, String.intercalate ", " (rawClauses.toList.map fun c => (c.reprint.getD "this rule").trimmed))

private def isViewPred (msgId : Ident) (pred : Term) : CommandElabM Bool :=
  Qed.Diag.probeTermElabOk do
    discard <| Term.elabTermEnsuringType pred (← Term.elabType (← `(Html $msgId → Bool)))
    Term.synthesizeSyntheticMVarsNoPostponing; return true

private def isForEachStyled (invStx : Syntax) : CommandElabM Bool := do
  if (invStx.getArg 5).getNumArgs > 0 then return true
  let pred ← lowerCompExpr .val (invStx.getArg 2)
  let using? : Option Ident := if (invStx.getArg 6).getNumArgs == 2 then some ⟨(invStx.getArg 6).getArg 1⟩ else none
  let some pid := using?.or (if pred.raw.isIdent then some ⟨pred.raw⟩ else none) | return false
  liftTermElabM do try Meta.forallTelescope (← getConstInfo (← realizeGlobalConstNoOverload pid)).type fun _ body => return body.eq?.isSome catch _ => return false

@[noinline] private def elabForEachInlineInv (spec : ComponentSpec) (invStx : Syntax) (isStyled : Bool) : CommandElabM (Option Term) := do
  let (invId, pred, colField) := (resolveInvIdent invStx spec.t.getId, ← lowerCompExpr .val (invStx.getArg 2), (⟨invStx.getArg 4⟩ : Ident))
  let using? : Option Ident := if (invStx.getArg 6).getNumArgs == 2 then some ⟨(invStx.getArg 6).getArg 1⟩ else none
  let pf? : Option Term := if (invStx.getArg 7).getNumArgs == 2 then some ⟨(invStx.getArg 7).getArg 1⟩ else none
  let (predToEmit, childInv) ← match using? with
    | some u => pure (pred, u)
    | none =>
        unless pred.raw.isIdent do throwErrorAt invStx (if pf?.isSome then "specify `using <ChildInvariant>` when proving a custom predicate" else "specify `using <ChildInvariant>` for an inline `for_each` predicate")
        let cid : Ident := ⟨pred.raw⟩
        pure (← liftTermElabM (if isStyled then extractViewInvPred cid else extractInvPred cid), cid)
  let cmd ← runPureQuot do
    if isStyled then
      let rhs ← pf?.getDM `(by qedDischargeStyledForEach $(spec.viewId) $colField $childInv $invId $predToEmit)
      `(command| set_option linter.unusedSimpArgs false in theorem $invId:ident : ∀ m, ($predToEmit) ($(spec.viewId) m) = true := $rhs)
    else
      let rhs ← pf?.getDM `(by qedDischargeForEach $(spec.updateId) $childInv $invId $predToEmit)
      `(command| theorem $invId:ident : ∀ m msg, (∀ c ∈ m.$colField, ($predToEmit) c) → (∀ c ∈ (InvTarget.proj ($(spec.updateId) m msg)).$colField, ($predToEmit) c) := $rhs)
  elabIsolatedTheorem cmd
  if isStyled then return none
  try return some (← liftTermElabM (extractInvPred invId)) catch _ => return none

@[noinline] private def mkViewAppInvCmdPure (spec : ComponentSpec) (invId : Ident) (compFull : Name) (vPred : Term) (assumePred? : Option Term) : PureQuotM CmdStx := do
  let stateOfM : Term ← if spec.hasSpeculative then `(m.visible) else `(m)
  let simpCan ← `(by simp (discharger := decide) [Qed.both, Qed.either, Qed.hasTag_canonical, Qed.tagHasOneOf_canonical])
  let congr ← `(Qed.canonical_congr_pred ($(mkIdent (compFull ++ `app_view_eq)) m) $simpCan $simpCan)
  let (appId, appViewFn) := (mkIdent (compFull ++ `app), mkIdent `Qed.App.view)
  let (appProp, appPf) ← match assumePred? with
    | some P => pure (← `(∀ m, ($P) $stateOfM → ($vPred) ($appViewFn $appId m) = true), ← `(fun m ha => ($congr).trans ($invId $stateOfM ha)))
    | none   => pure (← `(∀ m, ($vPred) ($appViewFn $appId m) = true), ← `(fun m => ($congr).trans ($invId $stateOfM)))
  `(command| set_option linter.unusedSimpArgs false in theorem $(mkIdentFrom invId (invId.getId.appendAfter "_app")) : $appProp := $appPf)

@[noinline] private def elabViewInlineInv (spec : ComponentSpec) (invStx : Syntax) (invId : Ident)
    (rawClauses : Array Syntax) (clauses : Array Term) (assume? pf? : Option Term) : CommandElabM Unit := do
  let (vPred, predStr) ← mkViewPredAndStr invStx rawClauses clauses "empty view styling invariant"
  if spec.hasProps then
    elabIsolatedTheorem (← runPureQuot do
      let rhs ← pf?.getDM `(by let _qed_hv := $(spec.viewId) p; change ∀ m, ($vPred) (_qed_hv m) = true; qedDischargeStyling _qed_hv $invId $(Syntax.mkStrLit predStr))
      `(command| set_option linter.unusedSimpArgs false in theorem $invId:ident (p : $(spec.propsId)) : ∀ m, ($vPred) ($(spec.viewId) p m) = true := $rhs))
  else
    let assumePred? ← assume?.mapM fun a => if a.raw.isIdent then try liftTermElabM (extractInvPred ⟨a.raw⟩) catch _ => pure a else pure a
    elabIsolatedTheorem (← runPureQuot do
      let prop ← match assumePred? with | some P => `(∀ m, ($P) m → ($vPred) ($(spec.viewId) m) = true) | none => `(∀ m, ($vPred) ($(spec.viewId) m) = true)
      let rhs ← pf?.getDM `(by qedDischargeStyling $(spec.viewId) $invId $(Syntax.mkStrLit predStr))
      `(command| set_option linter.unusedSimpArgs false in theorem $invId:ident : $prop := $rhs))
    let compFull := (← liftCoreM (resolveGlobalConstNoOverload spec.viewId)).getPrefix
    if (← getEnv).contains (compFull ++ `app_view_eq) then
      let saved ← get
      try elabIsolatedTheorem (← runPureQuot (mkViewAppInvCmdPure spec invId compFull vPred assumePred?)) catch _ => set saved

private def parseProveCases (optNode : Syntax) : CommandElabM (Option (Array (TSyntax ``Qed.qedProveCase))) := do
  if optNode.getNumArgs != 1 then return none
  some <$> runPureQuot do ((optNode.getArg 0).getArg 2).getArgs.mapM fun c => do
    let caseIds : Array Ident := (c.getArg 1).getSepArgs.map (⟨·⟩)
    let tacSeq : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨c.getArg 3⟩
    `(Qed.qedProveCase| $[$caseIds:ident],* => $tacSeq)

@[noinline] private def mkStateInlineInvCmdsPure (spec : ComponentSpec) (invId : Ident) (clauses : Array Term) (using? : Option (Array Term))
    (prove? : Option (Array (TSyntax ``Qed.qedProveCase))) (pf? : Option Term) : PureQuotM (Term × Array CmdStx) := do
  let conj ← mkConjBody clauses; let pred ← `(fun (s : $(spec.stateId)) => $(← bindMentionedFieldsPure spec (mentionsIdent conj.raw) conj))
  let usingL := using?.getD #[]
  let mkPresTac (updT : Term) (initT? : Option Term := none) : PureQuotM Term := match initT?, prove? with
    | some it, some pcs => `(by qedDischargePreserved [$[$usingL],*] $updT $invId ($pred) from $it _qedProve [$[$pcs],*])
    | some it, none     => `(by qedDischargePreserved [$[$usingL],*] $updT $invId ($pred) from $it)
    | none,    some pcs => `(by qedDischargePreserved [$[$usingL],*] $updT $invId ($pred) _qedProve [$[$pcs],*])
    | none,    none     => `(by qedDischargePreserved [$[$usingL],*] $updT $invId ($pred))
  if spec.hasProps then
    let mut cmds : Array CmdStx := #[]
    if spec.mountable then
      cmds := cmds.push (← `(command| set_option linter.unusedVariables false in theorem $(mkIdentFrom invId (invId.getId.appendAfter "_init")):ident (p : $(spec.propsId)) : ($pred) $(spec.initId) := by qedDischargeInit [$[$usingL],*] $(spec.initId) $invId ($pred)))
    let rhs ← pf?.getDM (mkPresTac (← `(($(spec.updateId) p))))
    return (pred, cmds.push (← `(command| set_option linter.unusedVariables false in theorem $invId:ident (p : $(spec.propsId)) : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($(spec.updateId) p m msg)) := $rhs)))
  let presProp ← `(∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($(spec.updateId) m msg)))
  let (prop, rhs) ← if spec.mountable then
      let r ← match pf? with
        | some pf => `(by exact ⟨by qedDischargeInit [$[$usingL],*] $(spec.initId) $invId ($pred), $pf⟩)
        | none    => mkPresTac spec.updateId (some spec.initId)
      pure (← `(($pred) ($(spec.initId)) ∧ $presProp), r)
    else pure (presProp, ← pf?.getDM (mkPresTac spec.updateId))
  return (pred, #[← `(command| theorem $invId:ident : $prop := $rhs)])

@[noinline] def elabInlineInvariantsPhase (spec : ComponentSpec) (wantView : Bool) : CommandElabM (Array (Term × Option Ident)) := do
  let mut statePreds : Array (Term × Option Ident) := #[]
  let rwCtx ← mkRewriteCtx spec false (allowHoist := false)
  let rwRawClause (c : Syntax) : CommandElabM Syntax := if spec.pureFns.isEmpty then pure c else rewriteIn rwCtx false c
  for invStx in spec.invariants do
    if invStx.getKind == ``compExampleClause then continue
    if invStx.getKind == ``compForEachInvClause then
      let isStyled ← isForEachStyled invStx
      if isStyled == wantView then if let some pred ← withRef invStx (elabForEachInlineInv spec invStx isStyled) then statePreds := statePreds.push (pred, none)
      continue
    let rawClauses ← (invStx.getArg 2).getSepArgs.mapM rwRawClause
    let hasHoldsIn := (invStx.getArg 3).getNumArgs > 0
    let assume? ← if hasHoldsIn && ((invStx.getArg 3).getArg 2).getNumArgs == 2 then some <$> lowerCompExpr .val (← rwRawClause (((invStx.getArg 3).getArg 2).getArg 1)) else pure none
    let using? : Option (Array Term) := if (invStx.getArg 4).getNumArgs == 4 then some (((invStx.getArg 4).getArg 2).getSepArgs.map (⟨·⟩)) else none
    let prove? ← parseProveCases (invStx.getArg 5)
    let pf? : Option Term := if (invStx.getArg 6).getNumArgs == 2 then some ⟨(invStx.getArg 6).getArg 1⟩ else none
    if prove?.isSome && pf?.isSome then throwErrorAt (invStx.getArg 5) "cannot combine per-action `prove:` with a manual `:= by` proof; use one or the other"
    let valClauses? ← if hasHoldsIn then some <$> rawClauses.mapM (lowerCompExpr .val)
      else if using?.isSome || prove?.isSome || rawClauses.isEmpty then pure none else try some <$> rawClauses.mapM (lowerCompExpr .val) catch _ => pure none
    let autoView ← match valClauses? with
      | some vc => if !hasHoldsIn && !vc.any (fun c => spec.allNames.any (mentionsIdent c.raw)) then vc.allM (isViewPred spec.msgId) else pure false
      | none => pure false
    if (hasHoldsIn || autoView) == wantView then
      let invId := resolveInvIdent invStx spec.t.getId
      if hasHoldsIn || autoView then
        if prove?.isSome then throwErrorAt (invStx.getArg 5) "per-action `prove:` applies to state invariants, not `view` styling invariants"
        withRef invStx <| elabViewInlineInv spec invStx invId rawClauses (← valClauses?.getDM (rawClauses.mapM (lowerCompExpr .val))) assume? pf?
      else
        let clauses ← rawClauses.mapM (lowerCompExpr .propInv)
        let (pred, cmds) ← withRef invStx <| runPureQuot (mkStateInlineInvCmdsPure spec invId clauses using? prove? pf?)
        withRef invStx <| cmds.forM elabIsolatedTheorem
        statePreds := statePreds.push (pred, if !spec.hasProps && spec.mountable then some invId else none)
  return statePreds

private def parseCompExRecord (recStx : Syntax) (validFields : Array Name) (kindLabel : String) (compId : Name) : CommandElabM (Array (Ident × Term)) :=
  (recStx.getArg 1).getSepArgs.mapM fun item => do
    let fid : Ident := ⟨item.getArg 0⟩; let fn := fid.getId.eraseMacroScopes
    unless validFields.contains fn do
      throwErrorAt fid s!"unknown {kindLabel} `{fn}` on component `{compId}` (valid: {String.intercalate ", " (validFields.toList.map toString)})"
    return (mkIdentFrom fid fn, ← lowerCompExpr .val (item.getArg 2))

@[noinline] private def lowerExampleRpcStep (spec : ComponentSpec) (st : Syntax) : CommandElabM Term := do
  if st.getKind != `Qed.compExOnReply then
    let v ← lowerCompExpr .val st; return ← runPureQuot `(Qed.TraceStep.msg ($v : $(spec.msgId)))
  let rpcId : Ident := ⟨st.getArg 1⟩
  let some (srvInfo, mInfo) := lookupServerMethod? (← getEnv) (← getCurrNamespace) (← getScope).openDecls rpcId.getId
    | throwErrorAt rpcId s!"unknown server RPC `{rpcId.getId}` in `on {rpcId.getId} => ...`"
  let urlLit := Syntax.mkStrLit s!"/_qed/rpc/{srvInfo.shortName}/{mInfo.name}"
  let rNode := st.getArg 3; let rk := rNode.getKind
  if rk == `Qed.compExReplyErr then
    let msgT ← lowerCompExpr .val (rNode.getArg 2); return ← runPureQuot `(Qed.TraceStep.rpcReply $urlLit (Except.error $msgT))
  let some (errTy?, payTy) ← extractRpcOutcomeTys? mInfo false false true | throwError s!"internal: unexpected RPC outcome type for `{mInfo.name}`"
  if rk == `Qed.compExReplyOk then
    let valT ← lowerCompExpr .val (rNode.getArg 2)
    return ← runPureQuot do match errTy? with
      | none     => `(Qed.TraceStep.rpcReply $urlLit (Except.ok (Qed.Proto.encode ($valT : $payTy))))
      | some eTy => `(Qed.TraceStep.rpcReply $urlLit (Except.ok (Qed.Proto.encode (Except.ok ($valT : $payTy) : Except (Qed.RpcDomainError $eTy) $payTy))))
  let some eTy := errTy? | throwErrorAt rNode s!"RPC `{rpcId.getId}` has no domain error tags; use `error(\"...\")` for transport errors"
  let tagId : Ident := ⟨rNode.getArg 3⟩
  let msgT ← if (rNode.getArg 4).getNumArgs == 2 then lowerCompExpr .val ((rNode.getArg 4).getArg 1) else runPureQuot `("")
  let tagDot := Syntax.node (.fromRef tagId) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef tagId) ".", tagId.raw]
  runPureQuot `(Qed.TraceStep.rpcReply $urlLit (Except.ok (Qed.Proto.encode (Except.error ({ tag := $(⟨tagDot⟩), message := $msgT } : Qed.RpcDomainError $eTy) : Except (Qed.RpcDomainError $eTy) $payTy))))

@[noinline] private def mkCompExampleCmdPure (spec : ComponentSpec) (thmId : Ident) (parsedParams : Array (Ident × Term))
    (whereTerms : Array (Syntax × Term)) (propsTerm? : Option Term) (initTerm goalTerm : Term) (emitsRaw? : Option Term)
    (hasRpcReplies : Bool) (stepTerms : Array Term) (lbl : StrLit) (manualTac? : Option (TSyntax `Lean.Parser.Tactic.tacticSeq)) : PureQuotM CmdStx := do
  let paramNames := parsedParams.map (·.1.getId.eraseMacroScopes)
  let paramBinders ← parsedParams.mapM fun (pId, pTy) => `(bracketedBinder| ($pId:ident : $pTy:term))
  let whereBinders ← whereTerms.zipIdx.mapM fun ((wStx, wT), idx) => `(bracketedBinder| ($(mkIdentFrom wStx (Name.mkSimple s!"_hWhere{idx}")):ident : $wT:term))
  let predBody0 ← bindMentionedFieldsPure spec (fun nm => !paramNames.contains nm && mentionsIdent goalTerm.raw nm) goalTerm
  let pred ← `(fun (s : $(spec.stateId)) => $(← match propsTerm? with | some pt => `(let p : $(spec.propsId) := $pt; $predBody0) | none => pure predBody0))
  let emitsTerm? ← emitsRaw?.mapM fun evVal => do
    let mut evBound ← bindMentionedFieldsPure spec (fun nm => !paramNames.contains nm && !spec.fieldNames.contains nm && mentionsIdent evVal.raw nm) evVal
    for bd in spec.binds.reverse do
      let sn := bindSetName bd.id.getId
      if mentionsIdent evBound.raw sn then evBound ← `(let $(mkIdent sn):ident := $(spec.outCtor sn); $evBound)
    let evFinal ← match propsTerm? with | some pt => `(let p : $(spec.propsId) := $pt; $evBound) | none => pure evBound
    `(($evFinal : $(spec.id `Out)))
  let updTerm ← match propsTerm? with | some pt => `(($(spec.updateId) $pt)) | none => pure spec.updateId
  let allBinders := paramBinders ++ whereBinders
  let pf ← match manualTac? with
    | some tacSeq => `(by qedWithFreshHeartbeats $tacSeq)
    | none        => `(by qedDischargeReachable $updTerm $initTerm $thmId $lbl)
  if hasRpcReplies then
    let stepsTerm ← `(([$[$stepTerms:term],*] : List (Qed.TraceStep $(spec.msgId))))
    match emitsTerm? with
    | some evT => `(command| set_option linter.unusedVariables false in theorem $thmId:ident $[$allBinders:bracketedBinder]* : Qed.optSat (Qed.runTraceAsyncEmits $updTerm $initTerm $stepsTerm) (fun _tr => ($pred) _tr.1 ∧ ($evT ∈ _tr.2)) := $pf)
    | none     => `(command| set_option linter.unusedVariables false in theorem $thmId:ident $[$allBinders:bracketedBinder]* : Qed.optSat (Qed.runTraceAsync $updTerm $initTerm $stepsTerm) ($pred) := $pf)
  else
    let traceTerm ← `(([$[$stepTerms:term],*] : List $(spec.msgId)))
    match emitsTerm? with
    | some evT => `(command| set_option linter.unusedVariables false in theorem $thmId:ident $[$allBinders:bracketedBinder]* : let _tr := Qed.runTraceEmits $updTerm $initTerm $traceTerm; ($pred) _tr.1 ∧ ($evT ∈ _tr.2) := $pf)
    | none     => `(command| set_option linter.unusedVariables false in theorem $thmId:ident $[$allBinders:bracketedBinder]* : Qed.Reachable $updTerm $initTerm ($pred) := Qed.reachable_of_trace $updTerm $initTerm ($pred) $traceTerm $pf)

@[noinline] private def elabCompExampleClause (spec : ComponentSpec) (cl : Syntax) : CommandElabM Unit := do
  let nameIdent : Ident := ⟨cl.getArg 1⟩; let thmId := mkIdentFrom nameIdent (spec.t.getId ++ nameIdent.getId.eraseMacroScopes)
  let parsedParams ← parseParamList (cl.getArg 2)
  for (pId, _) in parsedParams do
    let pName := pId.getId.eraseMacroScopes
    if spec.allNames.contains pName then throwErrorAt pId s!"`example` parameter `{pName}` shadows a field of `{spec.t.getId}`; rename the parameter"
  let optProps := cl.getArg 3
  let propsTerm? : Option Term ← if optProps.getNumArgs == 1 then
      unless spec.hasProps do throwErrorAt optProps s!"`with props` cannot be used on component `{spec.t.getId}` which has no `prop` or `bind` fields"
      let wp := optProps.getArg 0
      if wp.getNumArgs == 3 && (wp.getArg 2).getKind == `Qed.compExRecord then
        let pairs ← parseCompExRecord (wp.getArg 2) (spec.props.map (·.id.getId.eraseMacroScopes)) "prop" spec.t.getId
        let (fIds, fVals) := (pairs.map (·.1), pairs.map (·.2)); some <$> runPureQuot `(({ $[$fIds:ident := $fVals:term],* } : $(spec.propsId)))
      else let v ← lowerCompExpr .val (wp.getArg 3); some <$> runPureQuot `(($v : $(spec.propsId)))
    else if spec.hasProps then
      let reqProps := spec.props.filter (·.def?.isNone)
      if reqProps.isEmpty then some <$> runPureQuot `(({} : $(spec.propsId)))
      else throwErrorAt cl s!"`example {nameIdent.getId}` on prop-bearing component `{spec.t.getId}` requires `with props \{ ... }` for required prop(s): {String.intercalate ", " (reqProps.toList.map (·.id.getId.toString))}"
    else pure none
  let optFrom := cl.getArg 4
  let initTerm : Term ← if optFrom.getNumArgs == 1 then
      let fNode := (optFrom.getArg 0).getArg 1
      if fNode.getKind == `Qed.compExRecord then
        let pairs ← parseCompExRecord fNode (spec.states.map (·.id.getId.eraseMacroScopes)) "state field" spec.t.getId
        let (fIds, fVals) := (pairs.map (·.1), pairs.map (·.2))
        runPureQuot (if spec.mountable then `(({ $(spec.initId) with $[$fIds:ident := $fVals:term],* } : $(spec.stateId))) else `(({ $[$fIds:ident := $fVals:term],* } : $(spec.stateId))))
      else let v ← lowerCompExpr .val fNode; runPureQuot `(($v : $(spec.stateId)))
    else
      unless spec.mountable do throwErrorAt cl s!"`example {nameIdent.getId}` on non-mountable component `{spec.t.getId}` requires `from \{ ... }` to specify initial state"
      pure spec.initId
  let whereTerms ← if (cl.getArg 5).getNumArgs == 2 then ((cl.getArg 5).getArg 1).getSepArgs.mapM fun w => return (w, ← lowerCompExpr .propInv w) else pure #[]
  let rawSteps := (cl.getArg 7).getSepArgs; let hasRpcReplies := rawSteps.any (·.getKind == `Qed.compExOnReply)
  if hasRpcReplies && !spec.hasEffects then throwErrorAt cl s!"`on ... => ...` in `example {nameIdent.getId}` requires component `{spec.t.getId}` to have `await` / async effects"
  let stepTerms ← if hasRpcReplies then rawSteps.mapM (lowerExampleRpcStep spec) else rawSteps.mapM (lowerCompExpr .val)
  let rawGoal := cl.getArg 9; let goalTerm ← lowerCompExpr .propInv rawGoal
  let optEmits := cl.getArg 10
  let emitsRaw? ← if optEmits.getNumArgs == 1 then
      unless spec.outTy?.isSome do throwErrorAt optEmits s!"`emits` requires component `{spec.t.getId}` to declare at least one `event` or `bind`"
      some <$> lowerCompExpr .val ((optEmits.getArg 0).getArg 1)
    else pure none
  let lbl := Syntax.mkStrLit (let s := stxSnippet rawGoal; if s.isEmpty then "target" else s)
  let manualTac? := if (cl.getArg 11).getNumArgs == 3 then some (⟨(cl.getArg 11).getArg 2⟩ : TSyntax `Lean.Parser.Tactic.tacticSeq) else none
  elabIsolatedTheorem (← runPureQuot (mkCompExampleCmdPure spec thmId parsedParams whereTerms propsTerm? initTerm goalTerm emitsRaw? hasRpcReplies stepTerms lbl manualTac?))

@[noinline] def elabCompReachableAndWitnesses (spec : ComponentSpec) : CommandElabM Unit := do
  for cl in spec.invariants do if cl.getKind == ``compExampleClause then elabCompExampleClause spec cl

end CompElab
end Qed
