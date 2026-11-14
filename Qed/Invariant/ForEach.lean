import Qed.Component.Core
import Qed.Invariant.View
import Lean

namespace Qed
open Lean Elab Tactic

syntax (name := invariantForEach)
  "invariant " ident " : " term " for_each " ident " preserved_by " ident " using " ident
    (" := " term)? : command

elab "forEachLift " upd:ident childInv:ident pred:term : tactic => do
  let predI : Ident := ⟨pred.raw⟩
  let elemClose ← if pred.raw.isIdent
    then `(tactic| (try simp only [$predI:ident]) <;> (try (first | omega | simp_all | decide | trivial)))
    else `(tactic| (try (first | omega | simp | simp_all | decide | trivial)))
  -- Unhygienic binder names so manual `case … =>` proofs can reference `m`, `h`, `y`, `hP`.
  let m := mkIdent `m; let msg := mkIdent `msg; let h := mkIdent `h
  let y := mkIdent `y; let hy := mkIdent `hy; let hP := mkIdent `hP
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
         | exact $h
         | exact Qed.ForEach.forall_filter $h
         | exact Qed.ForEach.forall_sortBy $h
         | exact Qed.ForEach.updateKeyed_forall _ _ $childInv $h
         | exact Qed.ForEach.updateKeyed_forall _ _ ($childInv).2 $h
         | (refine Qed.ForEach.forall_map ?_ <;> intro $y $hy <;>
             have $hP:ident := $h $y $hy <;> ($mapClose:tactic))
         | (refine Qed.ForEach.forall_push $h ?_ <;> ($elemClose:tactic))
         | skip))))

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

macro "forEachStyleLift " view:ident childStyled:ident : tactic =>
  `(tactic|
    (intro m
     qedStyleReduce $view
     all_goals (try (rw [Qed.everyElementL_mapList]
                     intro c _
                     first
                       | (refine Qed.everyElement_through_map _ _ ?_ ($childStyled c) <;>
                            (intro t a; simp [Qed.attrRole_map, Qed.attrClasses_map, Qed.hasOneClass]; done))
                       | (simp only [Qed.everyElement, Qed.everyElementL, Bool.and_eq_true]
                          repeat' apply And.intro
                          all_goals (first
                            | (refine Qed.everyElement_through_map _ _ ?_ ($childStyled c) <;>
                                 (intro t a; simp [Qed.attrRole_map, Qed.attrClasses_map, Qed.hasOneClass]; done))
                            | (simp [Qed.attrRole, Qed.attrClasses, Qed.hasOneClass]; done)
                            | rfl))))))

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

syntax (name := invariantForEachSugar)
  "invariant " ident " : " ident " for_each " ident " preserved_by " ident : command
syntax (name := invariantForEachStyledSugar)
  "invariant " ident " : " ident " for_each " ident " holds_in " ident : command

open Elab Command Term Meta Lean.PrettyPrinter in
elab_rules : command
  | `(invariant $name:ident : $childInv:ident for_each $field:ident preserved_by $upd:ident) => do
      let pred ← liftTermElabM (extractInvPred childInv)
      elabCommand (← `(invariant $name : $pred for_each $field preserved_by $upd using $childInv))
  | `(invariant $name:ident : $childStyled:ident for_each $field:ident holds_in $view:ident) => do
      let pred ← liftTermElabM do
        let cn ← realizeGlobalConstNoOverload childStyled
        forallTelescope (← getConstInfo cn).type fun _ body => do
          let some lhs := body.eq?.map (·.2.1) | throwErrorAt childStyled
            "`{childStyled}` doesn't look like a `… holds_in …` invariant, so its predicate can't be \
             inferred, write it explicitly (`<pred> for_each … holds_in … using {childStyled}`)."
          delab lhs.appFn!
      elabCommand (← `(invariant $name : $pred for_each $field holds_in $view using $childStyled))

end Qed
