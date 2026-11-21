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

/-- `ReachableIn update init n target` holds iff `target` is reachable in at most `n` actions. -/
def ReachableIn {State Msg Out : Type} [InvTarget Out State]
    (update : State → Msg → Out) (init : State) (n : Nat) (target : State → Prop) : Prop :=
  ∃ trace : List Msg, trace.length ≤ n ∧ target (runTrace update init trace)

theorem reachable_of_trace {State Msg Out : Type} [InvTarget Out State]
    (update : State → Msg → Out) (init : State) (target : State → Prop)
    (trace : List Msg) (h : target (runTrace update init trace)) :
    Reachable update init target :=
  ⟨trace, h⟩

theorem reachableIn_of_trace {State Msg Out : Type} [InvTarget Out State]
    (update : State → Msg → Out) (init : State) (n : Nat) (target : State → Prop)
    (trace : List Msg) (hlen : trace.length ≤ n) (h : target (runTrace update init trace)) :
    ReachableIn update init n target :=
  ⟨trace, hlen, h⟩

theorem reachable_of_reachableIn {State Msg Out : Type} [InvTarget Out State]
    {update : State → Msg → Out} {init : State} {n : Nat} {target : State → Prop}
    (h : ReachableIn update init n target) :
    Reachable update init target :=
  let ⟨tr, _, ht⟩ := h
  ⟨tr, ht⟩

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

open Lean Elab Tactic in
elab "qedDischargeReachable" upd:term:max initT:term:max nm:ident labelLit:str : tactic => do
  let mut unfoldL : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[
    ← `(Lean.Parser.Tactic.simpLemma| Qed.runTrace),
    ← `(Lean.Parser.Tactic.simpLemma| Qed.InvTarget.proj_id),
    ← `(Lean.Parser.Tactic.simpLemma| Qed.InvTarget.proj_fst),
    ← `(Lean.Parser.Tactic.simpLemma| Qed.Lang.QedVal.val_id)
  ]
  let updInner := match upd with | `(($u)) => u | u => u
  let initInner := match initT with | `(($i)) => i | i => i
  if updInner.raw.isIdent then
    unfoldL := unfoldL.push (← `(Lean.Parser.Tactic.simpLemma| $(⟨updInner.raw⟩):term))
  if initInner.raw.isIdent then
    unfoldL := unfoldL.push (← `(Lean.Parser.Tactic.simpLemma| $(⟨initInner.raw⟩):term))
  try
    evalTactic (← `(tactic|
      (simp only [$[$unfoldL],*];
       qedUnfoldPresent [];
       try simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
         decide_eq_true_eq, decide_eq_false_iff_not, beq_iff_eq, bne_iff_ne] at *;
       try (repeat' split);
       all_goals (first | qedFastClose | decide | omega | rfl | (simp_all; first | decide | omega | rfl | qedAutoClose) | qedAutoClose))))
  catch _ => pure ()
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let mut lines : Array String := #[]
    for g in goals do
      let s ← g.withContext (Qed.Diag.ppQedExpr (← instantiateMVars (← g.getType)) [])
      unless lines.contains s do lines := lines.push s
    let body := String.intercalate "\n" (lines.toList.map fun l => s!"  • must satisfy:  {l}")
    throwErrorAt nm m!"Example `{nm.getId}` failed to prove `{labelLit.getString}`:\n{body}\n\nHint: Verify the action sequence reaches a state satisfying `{labelLit.getString}` (or strengthen the `where` preconditions for parametric examples)."

end Qed
