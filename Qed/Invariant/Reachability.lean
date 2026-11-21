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
    throwErrorAt nm m!"Reachability check `{nm.getId}` failed for `{labelLit.getString}`:\n{body}\n\nHint: Verify that the action trace reaches a state satisfying `{labelLit.getString}` (and within the step bound, if specified)."

open Lean Elab Tactic in
elab "qedDischargeWitness" nm:ident labelLit:str : tactic => do
  try
    evalTactic (← `(tactic|
      (try dsimp only at *;
       qedUnfoldPresent [];
       try (repeat' split);
       all_goals (first | qedFastClose | decide | omega | rfl | (simp_all; first | decide | omega | rfl | qedAutoClose) | qedAutoClose))))
  catch _ => pure ()
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let mut lines : Array String := #[]
    for g in goals do
      let s ← g.withContext (Qed.Diag.ppQedExpr (← instantiateMVars (← g.getType)) [])
      unless lines.contains s do lines := lines.push s
    let body := String.intercalate "\n" (lines.toList.map fun l => s!"  • unsatisfied invariant condition:  {l}")
    throwErrorAt nm m!"Witness `{nm.getId}` violates component/state invariant (`{labelLit.getString}`):\n{body}\n\nHint: Either the invariant is overly restrictive (accidentally disallowing this intended state) or the witness fields need adjustment."

section ReachParsers
open Lean Parser Qed.Lang

@[command_parser] def reachableStandaloneCmd : Parser := leading_parser
  atomic ("invariant " >> identEq `reachable) >> ident >> ":" >> termParser >>
  optional (symbol "within" >> numLit) >>
  symbol "from" >> termParser >> symbol "via" >> termParser >> symbol "by" >> termParser

@[command_parser] def witnessStandaloneCmd : Parser := leading_parser
  atomic ("invariant " >> identEq `witness) >> ident >> ":" >> termParser >> symbol "satisfies" >> termParser

end ReachParsers

open Lean Elab Command in
@[command_elab reachableStandaloneCmd]
def elabReachableStandaloneCmd : CommandElab := fun stx => do
  let name : Ident := ⟨stx.getArg 2⟩
  let pred : Term := ⟨stx.getArg 4⟩
  let bound? : Option (TSyntax `num) :=
    if (stx.getArg 5).getNumArgs == 2 then some ⟨(stx.getArg 5).getArg 1⟩ else none
  let init : Term := ⟨stx.getArg 7⟩
  let upd : Term := ⟨stx.getArg 9⟩
  let trace : Term := ⟨stx.getArg 11⟩
  let lbl := Syntax.mkStrLit ((((pred.raw.reprint.getD "target").splitOn "\n").headD "target").trimAscii.toString)
  match bound? with
  | some bound =>
      elabCommand (← `(command|
        theorem $name:ident : Qed.ReachableIn $upd $init $bound ($pred) :=
          Qed.reachableIn_of_trace $upd $init $bound ($pred) $trace
            (by simp only [List.length_cons, List.length_nil]; omega)
            (by qedDischargeReachable ($upd) ($init) $name $lbl)))
  | none =>
      elabCommand (← `(command|
        theorem $name:ident : Qed.Reachable $upd $init ($pred) :=
          Qed.reachable_of_trace $upd $init ($pred) $trace
            (by qedDischargeReachable ($upd) ($init) $name $lbl)))

open Lean Elab Command in
@[command_elab witnessStandaloneCmd]
def elabWitnessStandaloneCmd : CommandElab := fun stx => do
  let name : Ident := ⟨stx.getArg 2⟩
  let stateVal : Term := ⟨stx.getArg 4⟩
  let inv : Term := ⟨stx.getArg 6⟩
  let lbl := Syntax.mkStrLit ((((inv.raw.reprint.getD "invariant").splitOn "\n").headD "invariant").trimAscii.toString)
  elabCommand (← `(command|
    theorem $name:ident : ($inv) ($stateVal) := by
      qedDischargeWitness $name $lbl))

end Qed
