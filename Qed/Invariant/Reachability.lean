import Qed.Invariant.State

namespace Qed

/-! ## Invariant Non-Vacuity & Reachability Verification -/

/-- Executes a finite action trace from an initial state using `update` (supporting both pure
    `State → Msg → State` and effectful `State → Msg → State × Cmd Msg` / `State × Option Out`
    via `InvTarget.proj`). -/
def runTrace {State Msg Out : Type} [InvTarget Out State]
    (update : State → Msg → Out) : State → List Msg → State
  | s, []      => s
  | s, m :: ms => runTrace update (InvTarget.proj (update s m)) ms

@[simp] theorem runTrace_nil {State Msg Out : Type} [InvTarget Out State]
    (update : State → Msg → Out) (s : State) :
    runTrace update s [] = s := rfl

@[simp] theorem runTrace_cons {State Msg Out : Type} [InvTarget Out State]
    (update : State → Msg → Out) (s : State) (m : Msg) (ms : List Msg) :
    runTrace update s (m :: ms) = runTrace update (InvTarget.proj (update s m)) ms := rfl

/-- `Reachable update init target` holds iff some finite action trace from `init` reaches
    a state satisfying `target`. -/
def Reachable {State Msg Out : Type} [InvTarget Out State]
    (update : State → Msg → Out) (init : State) (target : State → Prop) : Prop :=
  ∃ trace : List Msg, target (runTrace update init trace)

theorem reachable_of_trace {State Msg Out : Type} [InvTarget Out State]
    (update : State → Msg → Out) (init : State) (target : State → Prop)
    (trace : List Msg) (h : target (runTrace update init trace)) :
    Reachable update init target :=
  ⟨trace, h⟩

theorem inv_holds_on_runTrace {State Msg Out : Type} [InvTarget Out State]
    {update : State → Msg → Out} {init : State} {Inv : State → Prop}
    (hinit : Inv init) (hstep : ∀ s m, Inv s → Inv (InvTarget.proj (update s m))) :
    ∀ trace, Inv (runTrace update init trace)
  | []      => hinit
  | m :: ms => inv_holds_on_runTrace (hstep init m hinit) hstep ms

/-- Non-vacuity theorem: if `Inv` is preserved from `init` and `target` is reachable via a finite
    action trace, then `Inv` is non-vacuously satisfiable alongside `target`. -/
theorem inv_nonvacuous_of_reachable {State Msg Out : Type} [InvTarget Out State]
    {update : State → Msg → Out} {init : State} {Inv target : State → Prop}
    (hreach : Reachable update init target)
    (hinit : Inv init) (hstep : ∀ s m, Inv s → Inv (InvTarget.proj (update s m))) :
    ∃ s, Inv s ∧ target s :=
  let ⟨tr, ht⟩ := hreach
  ⟨runTrace update init tr, inv_holds_on_runTrace hinit hstep tr, ht⟩

/-! ## Tactics & Standalone Commands (`reachable` / `witness`) -/

private def reachBaseSimpNames : Array Lean.Name :=
  #[``Qed.runTrace, ``Qed.InvTarget.proj_id, ``Qed.InvTarget.proj_fst, ``Qed.Lang.QedVal.val_id] ++
  Qed.Verify.Core.dictSimpNames

private def reachBoolSimpNames : Array Lean.Name :=
  Qed.Verify.Core.boolSimpNames ++ #[``decide_eq_false_iff_not]

open Lean Elab Tactic Qed.Verify.Core in
elab "qedDischargeReachable" upd:term:max initT:term:max nm:ident labelLit:str : tactic => do
  let mut dynNames : Array Name := #[]
  for raw in #[upd, initT] do
    let inner := match raw with | `(($u)) => u | u => u
    if inner.raw.isIdent then
      if let some cn ← try some <$> resolveGlobalConstNoOverload inner.raw catch _ => pure none then
        dynNames := dynNames.push cn
  try
    if let g :: rest ← getGoals then
      let sCtx ← mkDynamicSimpCtx dynNames (some ("reachBase", reachBaseSimpNames))
      setGoals (match ← simpGoalOnly g sCtx with | none => rest | some g' => g' :: rest)
    evalTactic (← `(tactic| qedUnfoldPresent []))
    let (bCtx, _) ← mkCachedSimpCtx "reachBool" reachBoolSimpNames
    setGoals <| ← (← getGoals).filterMapM fun g => simpGoalAllHyps g bCtx
    evalTactic (← `(tactic| try (repeat' split)))
    let mut rem : List MVarId := []
    for g in (← getGoals) do
      if ← tryCloseBasic g then continue
      setGoals [g]
      try evalTactic (← `(tactic| first | (simp_all; first | decide | omega | rfl | qedAutoClose) | qedAutoClose)) catch _ => pure ()
      rem := rem ++ (← getGoals)
    setGoals rem
  catch _ => pure ()
  let lbl := labelLit.getString
  Qed.Diag.throwUnsolvedGoals m!"Example `{nm.getId}` failed to prove `{lbl}`:"
    m!"\n\nHint: Verify the action sequence reaches a state satisfying `{lbl}` (or strengthen the `where` preconditions for parametric examples)."
    (ref? := some nm)

end Qed
