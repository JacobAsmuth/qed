import Qed.Component.AwaitLift
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
  let saved ← IO.getNumHeartbeats
  IO.setNumHeartbeats 0
  try elabCommand cmd
  finally IO.setNumHeartbeats saved

/-! ## Inline Invariant Elaboration -/

def mkViewPredAndStr (invStx : Syntax) (rawClauses : Array Syntax) (clauses : Array Term) (emptyMsg : String) : CommandElabM (Term × String) := do
  let vPred ← match clauses.toList with
    | [p] => pure p | p :: ps => ps.foldlM (init := p) fun acc q => `(Qed.both $acc $q) | [] => throwErrorAt invStx emptyMsg
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

private def elabForEachInlineInv (spec : ComponentSpec) (invStx : Syntax) (isStyled : Bool) : CommandElabM (Option Term) := do
  let (invId, pred, colField) := (resolveInvIdent invStx spec.t.getId, ← lowerCompExpr .val (invStx.getArg 2), (⟨invStx.getArg 4⟩ : Ident))
  let using? : Option Ident := if (invStx.getArg 6).getNumArgs == 2 then some ⟨(invStx.getArg 6).getArg 1⟩ else none
  let pf? : Option Term := if (invStx.getArg 7).getNumArgs == 2 then some ⟨(invStx.getArg 7).getArg 1⟩ else none
  let (predToEmit, childInv) ← match using? with
    | some u => pure (pred, u)
    | none =>
        unless pred.raw.isIdent do throwErrorAt invStx (if pf?.isSome then "specify `using <ChildInvariant>` when proving a custom predicate" else "specify `using <ChildInvariant>` for an inline `for_each` predicate")
        let cid : Ident := ⟨pred.raw⟩
        pure (← liftTermElabM (if isStyled then extractViewInvPred cid else extractInvPred cid), cid)
  if isStyled then
    let rhs ← pf?.getDM `(by qedDischargeStyledForEach $(spec.viewId) $colField $childInv $invId $predToEmit)
    elabIsolatedTheorem (← `(command| set_option linter.unusedSimpArgs false in theorem $invId:ident : ∀ m, ($predToEmit) ($(spec.viewId) m) = true := $rhs))
    return none
  let rhs ← pf?.getDM `(by qedDischargeForEach $(spec.updateId) $childInv $invId $predToEmit)
  elabIsolatedTheorem (← `(command| theorem $invId:ident : ∀ m msg, (∀ c ∈ m.$colField, ($predToEmit) c) → (∀ c ∈ (InvTarget.proj ($(spec.updateId) m msg)).$colField, ($predToEmit) c) := $rhs))
  try return some (← liftTermElabM (extractInvPred invId)) catch _ => return none

private def elabViewInlineInv (spec : ComponentSpec) (invStx : Syntax) (invId : Ident)
    (rawClauses : Array Syntax) (clauses : Array Term) (assume? pf? : Option Term) : CommandElabM Unit := do
  let (vPred, predStr) ← mkViewPredAndStr invStx rawClauses clauses "empty view styling invariant"
  if spec.hasProps then
    let rhs ← pf?.getDM `(by let _qed_hv := $(spec.viewId) p; change ∀ m, ($vPred) (_qed_hv m) = true; qedDischargeStyling _qed_hv $invId $(Syntax.mkStrLit predStr))
    elabIsolatedTheorem (← `(command| set_option linter.unusedSimpArgs false in theorem $invId:ident (p : $(spec.propsId)) : ∀ m, ($vPred) ($(spec.viewId) p m) = true := $rhs))
  else
    let assumePred? ← assume?.mapM fun a => if a.raw.isIdent then try liftTermElabM (extractInvPred ⟨a.raw⟩) catch _ => pure a else pure a
    let prop ← match assumePred? with | some P => `(∀ m, ($P) m → ($vPred) ($(spec.viewId) m) = true) | none => `(∀ m, ($vPred) ($(spec.viewId) m) = true)
    let rhs ← pf?.getDM `(by qedDischargeStyling $(spec.viewId) $invId $(Syntax.mkStrLit predStr))
    elabIsolatedTheorem (← `(command| set_option linter.unusedSimpArgs false in theorem $invId:ident : $prop := $rhs))
    let compFull := (← liftCoreM (resolveGlobalConstNoOverload spec.viewId)).getPrefix
    let appViewEqName := compFull ++ `app_view_eq
    if (← getEnv).contains appViewEqName then
      let saved ← get
      try
        let stateOfM : Term ← if spec.hasSpeculative then `(m.visible) else `(m)
        let simpCan ← `(by simp (discharger := decide) [Qed.both, Qed.either, Qed.hasTag_canonical, Qed.tagHasOneOf_canonical])
        let congr ← `(Qed.canonical_congr_pred ($(mkIdent appViewEqName) m) $simpCan $simpCan)
        let (appId, appViewFn) := (mkIdent (compFull ++ `app), mkIdent `Qed.App.view)
        let (appProp, appPf) ← match assumePred? with
          | some P => pure (← `(∀ m, ($P) $stateOfM → ($vPred) ($appViewFn $appId m) = true), ← `(fun m ha => ($congr).trans ($invId $stateOfM ha)))
          | none   => pure (← `(∀ m, ($vPred) ($appViewFn $appId m) = true), ← `(fun m => ($congr).trans ($invId $stateOfM)))
        elabIsolatedTheorem (← `(command| set_option linter.unusedSimpArgs false in theorem $(mkIdentFrom invId (invId.getId.appendAfter "_app")) : $appProp := $appPf))
      catch _ => set saved

private def parseProveCases (optNode : Syntax) : CommandElabM (Option (Array (TSyntax ``Qed.qedProveCase))) := do
  if optNode.getNumArgs != 1 then return none
  let proveNode := optNode.getArg 0
  let cases ← (proveNode.getArg 2).getArgs.mapM fun c => do
    let cIds : Array Ident := (c.getArg 1).getSepArgs.map (⟨·⟩)
    let tacSeq : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨c.getArg 3⟩
    `(Qed.qedProveCase| $[$cIds:ident],* => $tacSeq)
  return some cases

private def elabStateInlineInv (spec : ComponentSpec) (invId : Ident) (clauses : Array Term) (using? : Option (Array Term))
    (prove? : Option (Array (TSyntax ``Qed.qedProveCase))) (pf? : Option Term) : CommandElabM Term := do
  let conj ← mkConjBody clauses; let pred ← `(fun (s : $(spec.stateId)) => $(← bindMentionedFields spec (mentionsIdent conj.raw) conj))
  let usingL := using?.getD #[]
  let mkPresTac (updT : Term) (initT? : Option Term := none) : CommandElabM Term := match initT?, prove? with
    | some it, some pcs => `(by qedDischargePreserved [$[$usingL],*] $updT $invId ($pred) from $it _qedProve [$[$pcs],*])
    | some it, none     => `(by qedDischargePreserved [$[$usingL],*] $updT $invId ($pred) from $it)
    | none,    some pcs => `(by qedDischargePreserved [$[$usingL],*] $updT $invId ($pred) _qedProve [$[$pcs],*])
    | none,    none     => `(by qedDischargePreserved [$[$usingL],*] $updT $invId ($pred))
  if spec.hasProps then
    if spec.mountable then
      elabIsolatedTheorem (← `(theorem $(mkIdentFrom invId (invId.getId.appendAfter "_init")):ident : ($pred) $(spec.initId) := by qedDischargeInit [$[$usingL],*] $(spec.initId) $invId ($pred)))
    let rhs ← pf?.getDM (mkPresTac (← `(($(spec.updateId) p))))
    elabIsolatedTheorem (← `(theorem $invId:ident (p : $(spec.propsId)) : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($(spec.updateId) p m msg)) := $rhs))
  else
    let presProp ← `(∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($(spec.updateId) m msg)))
    let (prop, rhs) ← if spec.mountable then
        let r ← match pf? with
          | some pf => `(by exact ⟨by qedDischargeInit [$[$usingL],*] $(spec.initId) $invId ($pred), $pf⟩)
          | none    => mkPresTac spec.updateId (some spec.initId)
        pure (← `(($pred) ($(spec.initId)) ∧ $presProp), r)
      else pure (presProp, ← pf?.getDM (mkPresTac spec.updateId))
    elabIsolatedTheorem (← `(command| theorem $invId:ident : $prop := $rhs))
  return pred

def elabInlineInvariantsPhase (spec : ComponentSpec) (wantView : Bool) : CommandElabM (Array (Term × Option Ident)) := do
  let mut statePreds : Array (Term × Option Ident) := #[]
  let rwCtx ← mkRewriteCtx spec false (allowHoist := false)
  let rwRawClause (c : Syntax) : CommandElabM Syntax :=
    if spec.pureFns.isEmpty then pure c else rewriteIn rwCtx false c
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
    if prove?.isSome && pf?.isSome then
      throwErrorAt (invStx.getArg 5) "cannot combine per-action `prove:` with a manual `:= by` proof; use one or the other"
    let valClauses? ← if hasHoldsIn then some <$> rawClauses.mapM (lowerCompExpr .val)
      else if using?.isSome || prove?.isSome || rawClauses.isEmpty then pure none else try some <$> rawClauses.mapM (lowerCompExpr .val) catch _ => pure none
    let autoView ← match valClauses? with
      | some vc => if !hasHoldsIn && !vc.any (fun c => spec.allNames.any (mentionsIdent c.raw)) then vc.allM (isViewPred spec.msgId) else pure false
      | none => pure false
    let isView := hasHoldsIn || autoView
    if isView == wantView then
      let invId := resolveInvIdent invStx spec.t.getId
      if isView then
        if prove?.isSome then throwErrorAt (invStx.getArg 5) "per-action `prove:` applies to state invariants, not `view` styling invariants"
        withRef invStx <| elabViewInlineInv spec invStx invId rawClauses (← valClauses?.getDM (rawClauses.mapM (lowerCompExpr .val))) assume? pf?
      else
        let pred ← withRef invStx <| elabStateInlineInv spec invId (← rawClauses.mapM (lowerCompExpr .propInv)) using? prove? pf?
        statePreds := statePreds.push (pred, if !spec.hasProps && spec.mountable then some invId else none)
  return statePreds

def elabCompReachableAndWitnesses (spec : ComponentSpec) : CommandElabM Unit := do
  for cl in spec.invariants do
    if cl.getKind == ``compExampleClause then
      unless spec.mountable && !spec.hasProps do throwErrorAt cl "`example` inside a `component` requires a mountable component without `prop`s"
      let nameIdent : Ident := ⟨cl.getArg 1⟩; let thmId := mkIdentFrom nameIdent (spec.t.getId ++ nameIdent.getId.eraseMacroScopes)
      let parsedParams ← parseParamList (cl.getArg 2)
      let paramBinders : Array BinderStx ← parsedParams.mapM fun (pId, pTy) => do
        let pName := pId.getId.eraseMacroScopes
        if spec.allNames.contains pName then throwErrorAt pId s!"`example` parameter `{pName}` shadows a field of `{spec.t.getId}`; rename the parameter"
        `(bracketedBinder| ($pId:ident : $pTy:term))
      let paramNames := parsedParams.map (·.1.getId.eraseMacroScopes)
      let whereBinders ← if (cl.getArg 3).getNumArgs == 2 then
          ((cl.getArg 3).getArg 1).getSepArgs.zipIdx.mapM fun (wStx, idx) => do
            `(bracketedBinder| ($(mkIdentFrom wStx (Name.mkSimple s!"_hWhere{idx}")):ident : $(← lowerCompExpr .propInv wStx):term))
        else pure #[]
      let traceTerm ← `(([$(← (cl.getArg 5).getSepArgs.mapM (lowerCompExpr .val)):term,*] : List $(spec.msgId)))
      let rawGoal := cl.getArg 7; let goalTerm ← lowerCompExpr .propInv rawGoal
      let pred ← `(fun (s : $(spec.stateId)) => $(← bindMentionedFields spec (fun nm => !paramNames.contains nm && mentionsIdent goalTerm.raw nm) goalTerm))
      let lbl := Syntax.mkStrLit (let s := stxSnippet rawGoal; if s.isEmpty then "target" else s)
      let allBinders := paramBinders ++ whereBinders
      let pf ← if (cl.getArg 8).getNumArgs == 3 then let tacSeq : TSyntax `Lean.Parser.Tactic.tacticSeq := ⟨(cl.getArg 8).getArg 2⟩; `(by qedWithFreshHeartbeats $tacSeq)
               else `(by qedDischargeReachable $(spec.updateId) $(spec.initId) $thmId $lbl)
      elabIsolatedTheorem (← `(command| theorem $thmId:ident $[$allBinders:bracketedBinder]* : Qed.Reachable $(spec.updateId) $(spec.initId) ($pred) := Qed.reachable_of_trace $(spec.updateId) $(spec.initId) ($pred) $traceTerm $pf))

end CompElab
end Qed
