import Qed.Component.AwaitLift
import Qed.Invariant.ForEach

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

def resolveInvIdent (invStx : Syntax) (compId : Name) : Ident :=
  let idStx := (invStx.getArg 1).getArg 0
  mkIdentFrom idStx (compId ++ idStx.getId)


/-! ## Inline Invariant Elaboration -/

private def isViewPred (msgId : Ident) (pred : Term) : CommandElabM Bool := do
  let saved ← get
  try
    let ok ← liftTermElabM do
      let preCount := (← Core.getMessageLog).toList.length
      let expected ← Term.elabType (← `(Html $msgId → Bool))
      let _ ← Term.elabTermEnsuringType pred expected
      Term.synthesizeSyntheticMVarsNoPostponing
      return ((← Core.getMessageLog).toList.drop preCount).all (·.severity != .error)
    modify fun _ => saved
    return ok
  catch _ =>
    modify fun _ => saved
    return false

private def isForEachStyled (invStx : Syntax) : CommandElabM Bool := do
  let pred ← lowerCompExpr .val (invStx.getArg 2)
  let hasHoldsIn := (invStx.getArg 5).getNumArgs > 0
  let using? : Option Ident := if (invStx.getArg 6).getNumArgs == 2 then some ⟨((invStx.getArg 6).getArg 1)⟩ else none
  if hasHoldsIn then return true
  let some pid := using?.or (if pred.raw.isIdent then some ⟨pred.raw⟩ else none) | return false
  liftTermElabM do
    try
      let cn ← realizeGlobalConstNoOverload pid
      Meta.forallTelescope (← getConstInfo cn).type fun _ body => return body.eq?.isSome
    catch _ => return false

private def elabForEachInlineInv (spec : ComponentSpec) (invStx : Syntax) (isStyled : Bool) :
    CommandElabM (Option Term) := do
  let tId      := spec.t.getId
  let updateId := mkIdent (tId ++ `update)
  let viewId   := mkIdent (tId ++ `view)
  let invId := resolveInvIdent invStx tId
  let pred ← lowerCompExpr .val (invStx.getArg 2)
  let colField : Ident := ⟨(invStx.getArg 4)⟩
  let using? : Option Ident := if (invStx.getArg 6).getNumArgs == 2 then some ⟨((invStx.getArg 6).getArg 1)⟩ else none
  let pf? : Option Term := if (invStx.getArg 7).getNumArgs == 2 then some ⟨((invStx.getArg 7).getArg 1)⟩ else none
  let (predToEmit, usingToEmit?) ← match using?, pf? with
    | some u, _ => pure (pred, some u)
    | none, some _ =>
        unless pred.raw.isIdent do
          throwErrorAt invStx "specify `using <ChildInvariant>` when proving a custom predicate"
        let childInv : Ident := ⟨pred.raw⟩
        let ep ← if isStyled then
          liftTermElabM do
            let cn ← realizeGlobalConstNoOverload childInv
            Meta.forallTelescope (← getConstInfo cn).type fun _ body => do
              let some lhs := body.eq?.map (·.2.1) | throwErrorAt childInv
                "`{childInv}` doesn't look like a `… holds_in …` invariant"
              PrettyPrinter.delab lhs.appFn!
        else liftTermElabM (extractInvPred childInv)
        pure (ep, some childInv)
    | none, none =>
        unless pred.raw.isIdent do
          throwErrorAt invStx "specify `using <ChildInvariant>` for an inline `for_each` predicate"
        pure (pred, none)
  match isStyled, usingToEmit? with
  | true,  some u => elabCommand (← `(qedInternalInvariant $invId : $predToEmit for_each $colField holds_in $viewId using $u $[:= $pf?]?))
  | true,  none   =>
      let pid : Ident := ⟨predToEmit.raw⟩
      elabCommand (← `(qedInternalInvariant $invId : $pid for_each $colField holds_in $viewId))
  | false, some u => elabCommand (← `(qedInternalInvariant $invId : $predToEmit for_each $colField preserved_by $updateId using $u $[:= $pf?]?))
  | false, none   =>
      let pid : Ident := ⟨predToEmit.raw⟩
      elabCommand (← `(qedInternalInvariant $invId : $pid for_each $colField preserved_by $updateId))
  if isStyled then return none
  try
    return some (← liftTermElabM (extractInvPred invId))
  catch _ => return none

private def elabViewInlineInv (spec : ComponentSpec) (invStx : Syntax) (invId : Ident)
    (rawClauses : Array Syntax) (clauses : Array Term) (assume? pf? : Option Term) : CommandElabM Unit := do
  let tId     := spec.t.getId
  let propsId := mkIdent (tId ++ `Props)
  let viewId  := mkIdent (tId ++ `view)
  let vPred ← match clauses.toList with
    | [p] => pure p
    | p :: ps => ps.foldlM (init := p) fun acc q => `(Qed.both $acc $q)
    | [] => throwErrorAt invStx "empty view styling invariant"
  let predStr := String.intercalate ", " (rawClauses.toList.map fun c => (c.reprint.getD "this rule").trimmed)
  if spec.hasProps then
    let rhs ← pf?.getDM `(by
      let _qed_hv := $viewId p
      change ∀ m, ($vPred) (_qed_hv m) = true
      qedDischargeStyling _qed_hv $invId $(Syntax.mkStrLit predStr))
    elabCommand (← `(command| set_option linter.unusedSimpArgs false in
      theorem $invId:ident (p : $propsId) : ∀ m, ($vPred) ($viewId p m) = true := $rhs))
  else
    let prop ← match assume? with
      | some a =>
          let P ← if a.raw.isIdent then try liftTermElabM (extractInvPred ⟨a.raw⟩) catch _ => pure a else pure a
          `(∀ m, ($P) m → ($vPred) ($viewId m) = true)
      | none => `(∀ m, ($vPred) ($viewId m) = true)
    match pf? with
    | some p => elabCommand (← `(theorem $invId:ident : $prop := $p))
    | none   => elabCommand (← `(
        set_option linter.unusedSimpArgs false in
        theorem $invId:ident : $prop := by
          qedDischargeStyling $viewId $invId $(Syntax.mkStrLit predStr)))
    let fullView ← liftCoreM (resolveGlobalConstNoOverload viewId)
    let compFull := fullView.getPrefix
    let appViewEqName := compFull ++ `app_view_eq
    if (← getEnv).contains appViewEqName then
      let appId : Ident := mkIdent (compFull ++ `app)
      let appViewEqId : Ident := mkIdent appViewEqName
      let appInvId : Ident := mkIdentFrom invId (invId.getId.appendAfter "_app")
      let saved ← get
      try
        let stateOfM : Term ← if spec.hasSpeculative then `(m.visible) else `(m)
        let congr ← `(Qed.canonical_congr_pred ($appViewEqId m)
          (by simp (discharger := decide) [Qed.both, Qed.either, Qed.hasTag_canonical, Qed.tagHasOneOf_canonical])
          (by simp (discharger := decide) [Qed.both, Qed.either, Qed.hasTag_canonical, Qed.tagHasOneOf_canonical]))
        match assume? with
        | some a =>
            let P ← if a.raw.isIdent then try liftTermElabM (extractInvPred ⟨a.raw⟩) catch _ => pure a else pure a
            elabCommand (← `(command| set_option linter.unusedSimpArgs false in
              theorem $appInvId : ∀ m, ($P) $stateOfM → ($vPred) (Qed.App.view $appId m) = true :=
                fun m ha => ($congr).trans ($invId $stateOfM ha)))
        | none =>
            elabCommand (← `(command| set_option linter.unusedSimpArgs false in
              theorem $appInvId : ∀ m, ($vPred) (Qed.App.view $appId m) = true :=
                fun m => ($congr).trans ($invId $stateOfM)))
      catch _ => set saved

private def elabStateInlineInv (spec : ComponentSpec) (invId : Ident)
    (clauses : Array Term) (using? : Option (Array Term)) (pf? : Option Term) : CommandElabM Term := do
  let tId      := spec.t.getId
  let propsId  := mkIdent (tId ++ `Props)
  let stateId  := mkIdent (tId ++ `State)
  let initId   := mkIdent (tId ++ `init)
  let updateId := mkIdent (tId ++ `update)
  let conj ← mkConjBody clauses
  let pred ← `(fun (s : $stateId) => $(← bindMentionedFields spec (mentionsIdent conj.raw) conj))
  let usingL := using?.getD #[]
  if spec.hasProps then
    if spec.mountable then
      let initInvId := mkIdentFrom invId (invId.getId.appendAfter "_init")
      elabCommand (← `(theorem $initInvId:ident : ($pred) $initId := by
        qedDischargeInit [$[$usingL],*] $initId $invId ($pred)))
    let rhs ← pf?.getDM `(by qedDischargePreserved [$[$usingL],*] ($updateId p) $invId ($pred))
    elabCommand (← `(theorem $invId:ident (p : $propsId) :
      ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($updateId p m msg)) := $rhs))
  else
    let stepPf? ← pf?.mapM fun pf =>
      if spec.mountable then
        `(by exact ⟨by qedDischargeInit [$[$usingL],*] $initId $invId ($pred), $pf⟩)
      else pure pf
    let initOpt? : Option Term := if spec.mountable then some initId else none
    elabCommand (← `(qedInternalInvariant $invId : $pred $[from $initOpt?]? preserved_by $updateId using [$[$usingL],*] $[ := $stepPf?]?))
  return pred

def elabInlineInvariantsPhase (spec : ComponentSpec) (wantView : Bool) :
    CommandElabM (Array (Term × Option Ident)) := do
  let tId   := spec.t.getId
  let msgId := mkIdent (tId ++ `Msg)
  let mut statePreds : Array (Term × Option Ident) := #[]
  for invStx in spec.invariants do
    if invStx.getKind == ``compForEachInvClause then
      let isStyled ← isForEachStyled invStx
      if isStyled == wantView then
        if let some pred ← elabForEachInlineInv spec invStx isStyled then
          statePreds := statePreds.push (pred, none)
      continue
    let rawClauses := (invStx.getArg 2).getSepArgs
    let hasHoldsIn := (invStx.getArg 3).getNumArgs > 0
    let assume? : Option Term ←
      if hasHoldsIn && ((invStx.getArg 3).getArg 2).getNumArgs == 2 then some <$> lowerCompExpr .val (((invStx.getArg 3).getArg 2).getArg 1) else pure none
    let using? : Option (Array Term) :=
      if (invStx.getArg 4).getNumArgs == 4 then some (((invStx.getArg 4).getArg 2).getSepArgs.map (⟨·⟩)) else none
    let pf? : Option Term := if (invStx.getArg 5).getNumArgs == 2 then some ⟨((invStx.getArg 5).getArg 1)⟩ else none
    let valClauses? : Option (Array Term) ←
      if hasHoldsIn then
        some <$> rawClauses.mapM (lowerCompExpr .val)
      else if using?.isSome || rawClauses.isEmpty then
        pure none
      else
        try some <$> rawClauses.mapM (lowerCompExpr .val) catch _ => pure none
    let autoView ← match valClauses? with
      | some vc =>
          if !hasHoldsIn && !vc.any (fun c => spec.allNames.any (mentionsIdent c.raw)) then
            vc.allM (isViewPred msgId)
          else pure false
      | none => pure false
    let isView := hasHoldsIn || autoView
    if isView == wantView then
      let invId := resolveInvIdent invStx tId
      if isView then
        let valClauses ← match valClauses? with
          | some vc => pure vc
          | none => rawClauses.mapM (lowerCompExpr .val)
        elabViewInlineInv spec invStx invId rawClauses valClauses assume? pf?
      else
        let propClauses ← rawClauses.mapM (lowerCompExpr .propInv)
        let pred ← elabStateInlineInv spec invId propClauses using? pf?
        let id? := if !spec.hasProps && spec.mountable then some invId else none
        statePreds := statePreds.push (pred, id?)
  return statePreds


end CompElab
end Qed
