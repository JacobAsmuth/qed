/-
  Qed.ForEach: lifting a child component's invariant over a list of children.

  A `Component` embedded with `embed` lives as a keyed array in the parent's model. Its contract
  (`invariant childSafe : Child.Safe preserved_by Child.update`) is then a fact about *one* child.
  This file adds the connective that lifts it to "*every* child in the list stays valid", across the
  parent's own transition:

      invariant feedSafe : Card.Safe for_each cards preserved_by update using cardSafe

  expands to a machine-checked

      theorem feedSafe : ∀ m msg, (∀ c ∈ m.cards, Card.Safe c) →
                                  (∀ c ∈ (update m msg).cards, Card.Safe c)

  and discharges it by *applying* the composition lemmas in `Qed.ForEach` (`Component.lean`), one per
  list operation, rather than re-deriving the membership reasoning. The keyed arm (the one `embed`
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

/-- `<pred> for_each <field> preserved_by <update> using <childInv>`, see the module docs. The
    optional `:= proof` hands over a proof for an arm the automation can't close on its own. -/
syntax (name := invariantForEach)
  "invariant " ident " : " term " for_each " ident " preserved_by " ident " using " ident
    (" := " term)? : command

/-- The discharge *core*, exposed as a tactic so a hand-written `:= by` can let it close every arm
    it can and *leave the rest as goals* to fill by `case` (it does not error). The auto path
    (`qedDischargeForEach`, below) runs this and turns whatever's left into a readable message.

    It splits the parent transition and closes each arm by applying the matching `Qed.ForEach`
    lemma, keyed child message → `updateKeyed_forall childInv`, remove → `forall_filter`, add →
    `forall_push` (then close `pred newElem`), pass-through → the hypothesis. An arm with no lemma
    (a `qsort`, an `++`, an add whose element isn't provably valid) is simply left open. -/
elab "forEachLift " upd:ident childInv:ident pred:term : tactic => do
  -- closing the residual `pred newElem` an `add` (push) leaves: unfold a named predicate, then the
  -- usual arithmetic battery. Left *open* (not failed) when it can't, that's the "added element
  -- isn't provably valid" case the auto path surfaces.
  let predI : Ident := ⟨pred.raw⟩
  let elemClose ← if pred.raw.isIdent
    then `(tactic| (try simp only [$predI:ident]) <;> (try (first | omega | simp_all | decide | trivial)))
    else `(tactic| (try (first | omega | simp | simp_all | decide | trivial)))
  -- non-hygienic binder names, so a hand proof's `case … =>` can reference the model `m` and the
  -- "all children valid before" hypothesis `h` (and, in a map arm, the row `y` with `hP : P y`).
  let m := mkIdent `m; let msg := mkIdent `msg; let h := mkIdent `h
  let y := mkIdent `y; let hy := mkIdent `hy; let hP := mkIdent `hP
  -- the map arm's elementwise goal `P (g y)` comes with `hP : P y` in scope; unfold a named
  -- predicate on both, then the `preserved_by` battery (`simp_all` splits the conjunctions,
  -- `omega` finishes the arithmetic a rewrite can't, e.g. a `min`-clamped field)
  let mapClose ← if pred.raw.isIdent
    then `(tactic| ((try simp only [$predI:ident] at $hP:ident ⊢) <;>
                    (try (first | omega | (simp_all <;> omega) | (simp_all <;> done)
                                | decide | trivial))))
    else `(tactic| (try (first | omega | (simp_all <;> omega) | (simp_all <;> done)
                               | decide | trivial)))
  evalTactic (← `(tactic|
    (intro $m $msg $h
     cases $msg:ident <;>
       simp only [$upd:ident, Qed.ToStep.toStep_model, Qed.ToStep.toStep_pair,
                  InvTarget.proj_id, InvTarget.proj_fst] <;>
       (first
         | exact $h                                                       -- pass-through arm
         | exact Qed.ForEach.forall_filter $h                             -- remove (filter)
         | exact Qed.ForEach.forall_sortBy $h                             -- re-rank (verified sort)
         | exact Qed.ForEach.updateKeyed_forall _ _ $childInv $h          -- keyed child message
         | (refine Qed.ForEach.forall_map ?_ <;> intro $y $hy <;>         -- parent updates rows
             have $hP:ident := $h $y $hy <;> ($mapClose:tactic))          --   (props flow, map)
         | (refine Qed.ForEach.forall_push $h ?_ <;> ($elemClose:tactic)) -- add (push)
         | skip))))                                                        -- unmatched → left open

/-- The auto discharger the no-`:=` command uses: run `forEachLift`, then if any arm is left open,
    report *which* arm, *which list operation* blocked it, the remaining goal, and a paste-able
    `:= by` that finishes it, instead of a raw `unsolved goals` dump. `nm` positions the error. -/
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
            "sorts with `Array.qsort`, which has no membership lemma in the standard library, so \
             Qed can't see that reordering keeps every element valid (it does, same elements). \
             Switch this arm to Qed's verified `Array.sortBy` (a `mergeSort`) and it lifts \
             automatically; or prove this case."
          else if (s.splitOn " ++ ").length > 1 then
            "appends elements (`++`) that aren't known to satisfy the contract. Validate them on the \
             way in (decode into a type that already carries it) so invalid ones are unrepresentable, \
             or prove this case."
          else if ty.isForall then
            "reshapes the list with an operation Qed has no composition lemma for yet, add one to \
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

/-! ### Styling lift: the same `for_each`, over the view (`holds_in`)

`<pred> for_each <field> holds_in <view> using <childStyled>` lifts a child's styling contract to
"the parent's whole rendered view is styled", chrome *and* every card. It proves the same theorem a
plain `holds_in` does (`∀ m, pred (view m) = true`); the difference is the discharger handles the
*dynamic list* of `embed`-rendered children (which plain `holds_in` can't), by closing each rendered
card with `<childStyled>`. -/

/-- The styling lift's discharge core, exposed as a tactic so a hand `:= by` can reuse it and fill
    only an unusual view shape: reduce the view to chrome + a rendered list (`qedStyleReduce`), then
    close each rendered card via the child `holds_in` contract `childStyled` (a styled child view
    stays styled after `embed`'s `Html.map`, `everyElement_through_map`). Leaves what it can't (no
    error). -/
macro "forEachStyleLift " view:ident childStyled:ident : tactic =>
  `(tactic|
    (intro m
     qedStyleReduce $view
     all_goals (try (rw [Qed.everyElementL_mapList]
                     intro c _
                     first
                       -- the list element IS the rendered child
                       | (refine Qed.everyElement_through_map _ _ ?_ ($childStyled c) <;>
                            (intro t a; simp [Qed.attrRole_map, Qed.attrClasses_map, Qed.hasOneClass]; done))
                       -- the rendered child sits inside wrapper chrome (a keyed slot, parent
                       -- controls next to it): peel the literal wrapper elements, close the
                       -- chrome leaves by evaluation and each child-view conjunct through the
                       -- child's contract
                       | (simp only [Qed.everyElement, Qed.everyElementL, Bool.and_eq_true]
                          repeat' apply And.intro
                          all_goals (first
                            | (refine Qed.everyElement_through_map _ _ ?_ ($childStyled c) <;>
                                 (intro t a; simp [Qed.attrRole_map, Qed.attrClasses_map, Qed.hasOneClass]; done))
                            | (simp [Qed.attrRole, Qed.attrClasses, Qed.hasOneClass]; done)
                            | rfl))))))

/-- The auto discharger for `for_each … holds_in`: run `forEachStyleLift`, then if anything's left,
    report it clearly with the fix, instead of a raw goal dump. -/
elab "qedDischargeStyledForEach" view:ident field:ident childStyled:ident nm:ident pred:term : tactic => do
  evalTactic (← `(tactic| forEachStyleLift $view $childStyled))
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let mut body : MessageData := m!""
    for g in goals do
      body := body ++ (← g.withContext do
        let s := (← Meta.ppExpr (← instantiateMVars (← g.getType))).pretty.replace "✝" ""
        let why :=
          if (s.splitOn "everyElementL").length > 1 then
            "a leftover rendered list, check `" ++ toString childStyled.getId ++ "`'s predicate is \
             exactly the one here (same role and the same styles)."
          else
            "an element this rule constrains that the lift couldn't place, usually the parent view \
             has its *own* element with that role (style it), or the view is shaped unusually."
        pure m!"\n  • {why}\n      still needs:  {s}")
    let predStr := (pred.raw.reprint.getD "the rule").trimmed
    throwErrorAt nm m!"styling lift `{nm.getId}`, `{predStr}` couldn't be lifted over every \
      `{field.getId}` in `{view.getId}`.\n{body}\n\n`for_each … holds_in` reduces `{view.getId}` to \
      its static chrome plus a `{field.getId}.map (the child view)` list, closing each rendered card \
      with `{childStyled.getId}`. For anything left, finish by hand, `roleHasOneOf_map` / \
      `everyElementL_mapList` are the lemmas, and `forEachStyleLift` closes the parts it can:\n\n  \
      invariant {nm.getId} : {predStr} for_each {field.getId} holds_in {view.getId} using \
      {childStyled.getId} := by\n    forEachStyleLift {view.getId} {childStyled.getId}\n    <fill the rest>"

syntax (name := invariantForEachStyled)
  "invariant " ident " : " term " for_each " ident " holds_in " ident " using " ident
    (" := " term)? : command

macro_rules
  | `(invariant $name:ident : $pred for_each $_:ident holds_in $view:ident using $_:ident := $pf:term) =>
    `(theorem $name:ident : ∀ m, ($pred) ($view m) = true := $pf)
  | `(invariant $name:ident : $pred for_each $field:ident holds_in $view:ident using $childStyled:ident) =>
    `(set_option linter.unusedSimpArgs false in
      theorem $name:ident : ∀ m, ($pred) ($view m) = true := by
        qedDischargeStyledForEach $view $field $childStyled $name $pred)

/-! ### Single-reference sugar: infer the predicate from the child invariant

`cardSafe for_each cards preserved_by update` (no explicit predicate, no `using`) recovers the
predicate from `cardSafe`'s type and expands to the explicit form above. The same over the view:
`cardStyled for_each cards holds_in view`. Both are elaborators (they read the child invariant's
type), so the child invariant must be a bare identifier. -/

syntax (name := invariantForEachSugar)
  "invariant " ident " : " ident " for_each " ident " preserved_by " ident : command
syntax (name := invariantForEachStyledSugar)
  "invariant " ident " : " ident " for_each " ident " holds_in " ident : command

open Elab Command Term Meta Lean.PrettyPrinter in
elab_rules : command
  | `(invariant $name:ident : $childInv:ident for_each $field:ident preserved_by $upd:ident) => do
      -- `childInv : ∀ m msg, pred m → pred (…)`; recover `pred` as `fun m => (type of the hypothesis)`.
      let pred ← liftTermElabM do
        let cn ← realizeGlobalConstNoOverload childInv
        forallTelescope (← getConstInfo cn).type fun args _ => do
          if args.size < 2 then throwErrorAt childInv
            "`{childInv}` doesn't look like a `… preserved_by …` invariant, so its predicate can't \
             be inferred, write it explicitly (`<pred> for_each … preserved_by … using {childInv}`)."
          -- `.eta` turns `fun m => Card.Safe m` back into the bare `Card.Safe`, so a *named*
          -- predicate stays an identifier (the discharger unfolds it); a true inline `fun …` stays
          -- a lambda (no eta), which is exactly what the discharger wants too.
          let P ← mkLambdaFVars #[args[0]!] (← inferType args[args.size - 1]!)
          delab P.eta
      elabCommand (← `(invariant $name : $pred for_each $field preserved_by $upd using $childInv))
  | `(invariant $name:ident : $childStyled:ident for_each $field:ident holds_in $view:ident) => do
      -- `childStyled : ∀ m, pred (childView m) = true`; recover `pred` from the equation's LHS head.
      let pred ← liftTermElabM do
        let cn ← realizeGlobalConstNoOverload childStyled
        forallTelescope (← getConstInfo cn).type fun _ body => do
          let some lhs := body.eq?.map (·.2.1) | throwErrorAt childStyled
            "`{childStyled}` doesn't look like a `… holds_in …` invariant, so its predicate can't be \
             inferred, write it explicitly (`<pred> for_each … holds_in … using {childStyled}`)."
          delab lhs.appFn!
      elabCommand (← `(invariant $name : $pred for_each $field holds_in $view using $childStyled))

end Qed
