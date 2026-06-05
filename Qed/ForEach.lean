/-
  Qed.ForEach — lifting a child component's invariant over a list of children.

  A `Component` embedded with `embed` lives as a keyed array in the parent's model. Its contract
  (`invariant childSafe : Child.Safe preserved_by Child.update`) is then a fact about *one* child.
  This file adds the connective that lifts it to "*every* child in the list stays valid", across the
  parent's own transition:

      invariant feedSafe : Card.Safe for_each cards preserved_by update using cardSafe

  expands to a machine-checked

      theorem feedSafe : ∀ m msg, (∀ c ∈ m.cards, Card.Safe c) →
                                  (∀ c ∈ (update m msg).cards, Card.Safe c)

  and discharges it by *applying* the composition lemmas in `Qed.ForEach` (`Component.lean`) — one per
  list operation — rather than re-deriving the membership reasoning. The keyed arm (the one `embed`
  introduces) is closed by `updateKeyed_forall` fed the child invariant `cardSafe`; `add`/`remove`
  arms by `forall_push`/`forall_filter`. An arm with no matching lemma (a `qsort`, a hand-rolled
  rebuild, an `add` whose new element isn't provably valid) is *named* in the error with the fix.

  Because `feedSafe` is itself a `∀ c ∈ cards, …` fact, it composes: a grandparent lifts it again
  with `for_each` one level up. `import Lean` here is for the discharge elaborator + its error
  reporting; it is build-time only (tree-shaken out of the JS bundle).
-/
import Qed.Component
import Qed.Invariant
import Lean

namespace Qed
open Lean Elab Tactic

/-- `<pred> for_each <field> preserved_by <update> using <childInv>` — see the module docs. The
    optional `:= proof` hands over a proof for an arm the automation can't close on its own. -/
syntax (name := invariantForEach)
  "invariant " ident " : " term:max " for_each " ident " preserved_by " ident " using " ident
    (" := " term)? : command

/-- The discharge *core*, exposed as a tactic so a hand-written `:= by` can let it close every arm
    it can and *leave the rest as goals* to fill by `case` (it does not error). The auto path
    (`qedDischargeForEach`, below) runs this and turns whatever's left into a readable message.

    It splits the parent transition and closes each arm by applying the matching `Qed.ForEach`
    lemma — keyed child message → `updateKeyed_forall childInv`, remove → `forall_filter`, add →
    `forall_push` (then close `pred newElem`), pass-through → the hypothesis. An arm with no lemma
    (a `qsort`, an `++`, an add whose element isn't provably valid) is simply left open. -/
elab "forEachLift " upd:ident childInv:ident pred:term : tactic => do
  -- closing the residual `pred newElem` an `add` (push) leaves: unfold a named predicate, then the
  -- usual arithmetic battery. Left *open* (not failed) when it can't — that's the "added element
  -- isn't provably valid" case the auto path surfaces.
  let predI : Ident := ⟨pred.raw⟩
  let elemClose ← if pred.raw.isIdent
    then `(tactic| (try simp only [$predI:ident]) <;> (try (first | omega | simp_all | decide | trivial)))
    else `(tactic| (try (first | omega | simp | simp_all | decide | trivial)))
  -- non-hygienic binder names, so a hand proof's `case … =>` can reference the model `m` and the
  -- "all children valid before" hypothesis `h`.
  let m := mkIdent `m; let msg := mkIdent `msg; let h := mkIdent `h
  evalTactic (← `(tactic|
    (intro $m $msg $h
     cases $msg:ident <;>
       simp only [$upd:ident, InvTarget.proj_id, InvTarget.proj_fst] <;>
       (first
         | exact $h                                                       -- pass-through arm
         | exact Qed.ForEach.forall_filter $h                             -- remove (filter)
         | exact Qed.ForEach.forall_sortBy $h                             -- re-rank (verified sort)
         | exact Qed.ForEach.updateKeyed_forall _ _ $childInv $h          -- keyed child message
         | (refine Qed.ForEach.forall_push $h ?_ <;> ($elemClose:tactic)) -- add (push)
         | skip))))                                                        -- unmatched → left open

/-- The auto discharger the no-`:=` command uses: run `forEachLift`, then if any arm is left open,
    report *which* arm, *which list operation* blocked it, the remaining goal, and a paste-able
    `:= by` that finishes it — instead of a raw `unsolved goals` dump. `nm` positions the error. -/
elab "qedDischargeForEach" upd:ident childInv:ident nm:ident pred:term : tactic => do
  evalTactic (← `(tactic| forEachLift $upd $childInv $pred))
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let mut body : MessageData := m!""
    let mut firstTag : Name := `theArm
    for g in goals do
      let tag ← g.getTag
      if firstTag == `theArm then firstTag := tag
      body := body ++ (← g.withContext do
        let ty ← instantiateMVars (← g.getType)
        let s := (← Meta.ppExpr ty).pretty.replace "✝" ""
        let why :=
          if (s.splitOn "qsort").length > 1 then
            "sorts with `Array.qsort`, which has no membership lemma in the standard library — so \
             Qed can't see that reordering keeps every element valid (it does — same elements). \
             Switch this arm to Qed's verified `Array.sortBy` (a `mergeSort`) and it lifts \
             automatically; or prove this case."
          else if (s.splitOn " ++ ").length > 1 then
            "appends elements (`++`) that aren't known to satisfy the contract. Validate them on the \
             way in (decode into a type that already carries it) so invalid ones are unrepresentable, \
             or prove this case."
          else if ty.isForall then
            "reshapes the list with an operation Qed has no composition lemma for yet — add one to \
             `Qed.ForEach`, or prove this case."
          else
            "adds an element that isn't known to satisfy the contract. Build it so the property holds \
             by construction, or prove this case."
        pure m!"\n  • case `{tag}` {why}\n        still needs:  {s}")
    let predStr := (pred.raw.reprint.getD "the contract").trimmed
    throwErrorAt nm m!"invariant `{nm.getId}` doesn't lift to every {upd.getId}-arm: the contract \
      `{predStr}` holds for each child on its own, but the arm(s) below could break it for the \
      list.\n{body}\n\nEvery other arm was discharged automatically. Finish these by reusing the \
      automation, then filling only what's left:\n\n  invariant {nm.getId} : {predStr} for_each … \
      preserved_by {upd.getId} using {childInv.getId} := by\n    forEachLift {upd.getId} \
      {childInv.getId} {predStr}\n    case {firstTag} => …"

macro_rules
  | `(invariant $name:ident : $pred for_each $field:ident preserved_by $upd:ident using $_:ident := $pf:term) =>
    `(theorem $name:ident :
        ∀ m msg, (∀ c ∈ m.$field, ($pred) c) →
                 (∀ c ∈ (InvTarget.proj ($upd m msg)).$field, ($pred) c) := $pf)
  | `(invariant $name:ident : $pred for_each $field:ident preserved_by $upd:ident using $childInv:ident) =>
    `(theorem $name:ident :
        ∀ m msg, (∀ c ∈ m.$field, ($pred) c) →
                 (∀ c ∈ (InvTarget.proj ($upd m msg)).$field, ($pred) c) := by
        qedDischargeForEach $upd $childInv $name $pred)

end Qed
