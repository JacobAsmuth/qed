import Qed.Invariant.State

namespace Qed
section
variable {State Msg Out : Type} [InvTarget Out State]

def runTrace (update : State → Msg → Out) : State → List Msg → State
  | s, [] => s | s, m :: ms => runTrace update (InvTarget.proj (update s m)) ms

@[simp] theorem runTrace_nil (update : State → Msg → Out) (s : State) : runTrace update s [] = s := rfl
@[simp] theorem runTrace_cons (update : State → Msg → Out) (s : State) (m : Msg) (ms : List Msg) :
    runTrace update s (m :: ms) = runTrace update (InvTarget.proj (update s m)) ms := rfl

def Reachable (update : State → Msg → Out) (init : State) (target : State → Prop) : Prop := ∃ trace : List Msg, target (runTrace update init trace)
theorem reachable_of_trace (update : State → Msg → Out) (init : State) (target : State → Prop) (trace : List Msg)
    (h : target (runTrace update init trace)) : Reachable update init target := ⟨trace, h⟩

theorem inv_holds_on_runTrace {update : State → Msg → Out} {init : State} {Inv : State → Prop}
    (hinit : Inv init) (hstep : ∀ s m, Inv s → Inv (InvTarget.proj (update s m))) : ∀ trace, Inv (runTrace update init trace)
  | [] => hinit | m :: ms => inv_holds_on_runTrace (hstep init m hinit) hstep ms

theorem inv_nonvacuous_of_reachable {update : State → Msg → Out} {init : State} {Inv target : State → Prop}
    (hreach : Reachable update init target) (hinit : Inv init) (hstep : ∀ s m, Inv s → Inv (InvTarget.proj (update s m))) :
    ∃ s, Inv s ∧ target s := let ⟨tr, ht⟩ := hreach; ⟨runTrace update init tr, inv_holds_on_runTrace hinit hstep tr, ht⟩
end

private def reachBaseSimpNames : Array Lean.Name := #[``Qed.runTrace, ``Qed.InvTarget.proj_id, ``Qed.InvTarget.proj_fst, ``Qed.Lang.QedVal.val_id] ++ Qed.Verify.Core.dictSimpNames
private def reachBoolSimpNames : Array Lean.Name := Qed.Verify.Core.boolSimpNames ++ #[``decide_eq_false_iff_not]

open Lean Elab Tactic Qed.Verify.Core in
elab "qedDischargeReachable" upd:term:max initT:term:max nm:ident labelLit:str : tactic => do
  let mut dynNames : Array Name := #[]
  for raw in #[upd, initT] do
    let inner := match raw with | `(($u)) => u | u => u
    if inner.raw.isIdent then if let some cn ← try some <$> resolveGlobalConstNoOverload inner.raw catch _ => pure none then dynNames := dynNames.push cn
  try
    if let g :: rest ← getGoals then
      let ctx ← mkDynamicSimpCtx dynNames (some ("reachBase", reachBaseSimpNames))
      let g1? ← simpGoalOnly g ctx (dsimpOnly := true)
      let g2? ← match g1? with | none => pure none | some g1 => simpGoalOnly g1 ctx
      setGoals (match g2? with | none => rest | some g' => g' :: rest)
    evalTactic (← `(tactic| qedUnfoldPresent []))
    let (bCtx, _) ← mkCachedSimpCtx "reachBool" reachBoolSimpNames
    setGoals <| ← (← getGoals).filterMapM (simpGoalAllHyps · bCtx)
    evalTactic (← `(tactic| try (repeat' split)))
    forEachGoal fun g => do
      if ← tryCloseBasic g then setGoals []
      else (try evalTactic (← `(tactic| first | (simp_all; first | decide | omega | rfl | qedAutoClose) | qedAutoClose)) catch _ => pure ())
  catch _ => pure ()
  let lbl := labelLit.getString
  Qed.Diag.throwUnsolvedGoals m!"Example `{nm.getId}` failed to prove `{lbl}`:"
    m!"\n\nHint: Verify the action sequence reaches a state satisfying `{lbl}` (or strengthen the `where` preconditions for parametric examples)." (ref? := some nm)

end Qed
