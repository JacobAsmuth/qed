import Qed.Component.Core
import Qed.Invariant.State
import Qed.Invariant.View

namespace Qed
open Lean Elab Tactic

syntax (name := invariantForEach)
  "qedInternalInvariant " ident " : " term " for_each " ident " preserved_by " ident " using " ident
    (" := " term)? : command

/-- Extract the collection expression `xs` from a goal of shape `∀ c ∈ xs, P c`. -/
private def extractForEachColl? (tgt : Expr) : Option Expr :=
  match tgt.consumeMData with
  | .forallE _ _ (.forallE _ memTy _ _) _ =>
      let memTy := memTy.consumeMData
      if memTy.isAppOfArity ``Membership.mem 5 then
        some memTy.getAppArgs[3]!.consumeMData
      else none
  | _ => none

private def forEachDirectTable : Array (Name × Name) := #[
  (``Array.filter, ``Qed.ForEach.forall_filter),
  (``Array.sortBy, ``Qed.ForEach.forall_sortBy),
  (``Array.pop, ``Qed.ForEach.forall_pop),
  (``Array.reverse, ``Qed.ForEach.forall_reverse),
  (``Array.extract, ``Qed.ForEach.forall_extract),
  (``Array.eraseIdx, ``Qed.ForEach.forall_eraseIdx),
  (``Array.eraseIdxIfInBounds, ``Qed.ForEach.forall_eraseIdxIfInBounds),
  (``Array.swap, ``Qed.ForEach.forall_swap),
  (``Array.swapIfInBounds, ``Qed.ForEach.forall_swapIfInBounds)
]

private def forEachElemTable : Array (Name × Name) := #[
  (``Array.push, ``Qed.ForEach.forall_push),
  (``Array.set, ``Qed.ForEach.forall_set),
  (``Array.setIfInBounds, ``Qed.ForEach.forall_setIfInBounds),
  (``HAppend.hAppend, ``Qed.ForEach.forall_append),
  (``Array.append, ``Qed.ForEach.forall_append)
]

private def runForEachArm (childInv : Ident) (pred : Term)
    (elemClose mapClose : TSyntax `tactic) : TacticM Unit := do
  let _ := pred
  let h := mkIdent `h; let y := mkIdent `y; let hy := mkIdent `hy; let hP := mkIdent `hP
  let mkDirect (lem : Name) := `(tactic| exact $(mkIdent lem):ident $h)
  let mkElem (lem : Name) := `(tactic| (refine $(mkIdent lem):ident $h ?_ <;> ($elemClose:tactic)))
  let mapTac ← `(tactic| (refine Qed.ForEach.forall_map ?_ <;> intro $y $hy <;> have $hP:ident := $h $y $hy <;> ($mapClose:tactic)))
  let modTac ← `(tactic| (refine Qed.ForEach.forall_modify $h ?_ <;> intro $y $hy $hP <;> ($mapClose:tactic)))
  let ukTac1 ← `(tactic| exact Qed.ForEach.updateKeyed_forall _ _ $childInv $h)
  let ukTac2 ← `(tactic| exact Qed.ForEach.updateKeyed_forall _ _ ($childInv).2 $h)
  let tryTac (tac : TSyntax `tactic) : TacticM Bool := do
    let saved ← saveState
    try evalTactic tac; return true
    catch _ => restoreState saved; return false
  let fastTac? : Option (TSyntax `tactic) ← withMainContext do
    let tgt ← instantiateMVars (← getMainTarget)
    let some collRaw := extractForEachColl? tgt | return none
    let coll := Qed.stripLetE 16 collRaw
    let some nm := coll.getAppFn.constName? | return some (← `(tactic| exact $h))
    if let some (_, lem) := forEachDirectTable.find? (·.1 == nm) then return some (← mkDirect lem)
    if let some (_, lem) := forEachElemTable.find? (·.1 == nm) then return some (← mkElem lem)
    if nm == ``Array.map then return some mapTac
    if nm == ``Array.modify then return some modTac
    if nm == ``Qed.Component.updateKeyed || nm.getString! == "updateKeyed" then
      return some (← `(tactic| first | $ukTac1:tactic | $ukTac2:tactic))
    return some (← `(tactic| exact $h))
  if let some tac := fastTac? then
    if (← tryTac tac) then return
  let mut fallbacks : Array (TSyntax `tactic) := #[← `(tactic| exact $h)]
  for (_, lem) in forEachDirectTable do fallbacks := fallbacks.push (← mkDirect lem)
  fallbacks := fallbacks ++ #[ukTac1, ukTac2, mapTac, modTac]
  for (_, lem) in forEachElemTable.take 4 do fallbacks := fallbacks.push (← mkElem lem)
  fallbacks := fallbacks.push (← `(tactic| grind))
  for tac in fallbacks do
    if (← tryTac tac) then return

elab "forEachLift " upd:ident childInv:ident pred:term : tactic => do
  let predLem ← if pred.raw.isIdent
    then pure #[← `(Lean.Parser.Tactic.simpLemma| $(⟨pred.raw⟩):ident),
                ← `(Lean.Parser.Tactic.simpLemma| Qed.Lang.QedVal.val_id)]
    else pure #[← `(Lean.Parser.Tactic.simpLemma| Qed.Lang.QedVal.val_id)]
  let elemClose ← if pred.raw.isIdent
    then `(tactic| (try dsimp only) <;> (try simp only [$[$predLem],*]) <;>
                   (try (first | omega | decide | trivial | simp_all | qedAutoClose)))
    else `(tactic| (try dsimp only) <;> (try simp only [$[$predLem],*]) <;>
                   (try (first | omega | decide | trivial | simp | simp_all | qedAutoClose)))
  -- Unhygienic binder names so manual `case … =>` proofs can reference `m`, `h`, `y`, `hP`.
  let m := mkIdent `m; let msg := mkIdent `msg; let h := mkIdent `h
  let hP := mkIdent `hP
  let mapClose ← `(tactic|
    ((try dsimp only at $hP:ident ⊢) <;> (try simp only [$[$predLem],*] at $hP:ident ⊢) <;>
     (try (first | omega | decide | trivial | (simp_all <;> omega) | (simp_all <;> done) | qedAutoClose))))
  evalTactic (← `(tactic|
    (intro $m $msg $h
     cases $msg:ident <;>
       simp only [$upd:ident, InvTarget.proj_id, InvTarget.proj_fst])))
  let goals ← getGoals
  let mut rem : List MVarId := []
  for g in goals do
    setGoals [g]
    runForEachArm childInv pred elemClose mapClose
    rem := rem ++ (← getGoals)
  setGoals rem

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
        let s ← Qed.Diag.ppQedExpr ty ["m"]
        let tagLabel := Qed.Diag.formatCaseTag tag
        let why :=
          if (s.splitOn "qsort").length > 1 then
            "uses `Array.qsort` (no membership lemma); switch to Qed's verified `sortBy` so it lifts automatically."
          else if (s.splitOn " ++ ").length > 1 then
            "appends elements (`++`) not known to satisfy the contract; validate them first or prove this case."
          else if ty.isForall then
            "transforms the collection with an unverified operation; add a lemma or prove this case."
          else
            "inserts an element not known to satisfy the contract."
        pure m!"\n  • {tagLabel}: {why}\n    must satisfy:  {s}")
    let predStr := (pred.raw.reprint.getD "the contract").trimmed
    throwErrorAt nm m!"Invariant `{nm.getId}` failed to lift `{predStr}` across `{upd.getId}`:{body}\n\nHint: Ensure newly inserted elements satisfy `{predStr}`, or prove only the remaining branch:\n  invariant {nm.getId} : {predStr} for_each … using {childInv.getId} := by\n    forEachLift {upd.getId} {childInv.getId} {predStr}\n    case {firstTag} => …"

macro_rules
  | `(qedInternalInvariant $name:ident : $pred for_each $field:ident preserved_by $upd:ident using $_:ident := $pf:term) =>
    `(theorem $name:ident :
        ∀ m msg, (∀ c ∈ m.$field, ($pred) c) →
                 (∀ c ∈ (InvTarget.proj ($upd m msg)).$field, ($pred) c) := $pf)
  | `(qedInternalInvariant $name:ident : $pred for_each $field:ident preserved_by $upd:ident using $childInv:ident) =>
    `(theorem $name:ident :
        ∀ m msg, (∀ c ∈ m.$field, ($pred) c) →
                 (∀ c ∈ (InvTarget.proj ($upd m msg)).$field, ($pred) c) := by
        qedDischargeForEach $upd $childInv $name $pred)

syntax "forEachStyleLift " ident ident : tactic

macro_rules
  | `(tactic| forEachStyleLift $view:ident $childStyled:ident) => do
      let c := mkIdent `c
      let liftChild ← `(tactic|
        (refine Qed.everyElement_through_map _ _ ?_ ($childStyled $c) <;>
          (intro t a;
           first
             | (simp only [Qed.attrRole_map, Qed.attrClasses_map, Qed.hasOneClass]; done)
             | (simp [Qed.attrRole_map, Qed.attrClasses_map, Qed.hasOneClass]; done))))
      `(tactic|
        (intro m
         qedStyleReduce $view
         all_goals (try (first
           | (rw [Qed.everyElementL_mapList]
              intro $c _
              first
                | $liftChild:tactic
                | (simp only [Qed.everyElement, Qed.everyElementL, Bool.and_eq_true]
                   repeat' apply And.intro
                   all_goals (first
                     | $liftChild:tactic
                     | (simp only [Qed.attrRole, Qed.attrValue, Qed.attrClasses, Qed.hasOneClass,
                                   Bool.true_and, Bool.and_true, Bool.false_and, Bool.and_false,
                                   Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false,
                                   ite_true, ite_false, beq_self_eq_true, eq_self]; (try rfl); done)
                     | (simp [Qed.attrRole, Qed.attrClasses, Qed.hasOneClass]; done)
                     | rfl)))
           | (rw [Qed.Html.imgsHaveAltList_mapList]; intro $c _; simpa [Qed.Html.imgsHaveAlt_map] using $childStyled $c)
           | (rw [Qed.Html.buttonsAccessibleList_mapList]; intro $c _; simpa [Qed.Html.buttonsAccessible_map] using $childStyled $c)
           | (rw [Qed.Html.validAriaRolesList_mapList]; intro $c _; simpa [Qed.Html.validAriaRoles_map] using $childStyled $c)
           | (rw [Qed.Html.labelsAssociatedList_mapList]; intro $c _; simpa [Qed.Html.labelsAssociated_map] using $childStyled $c)
           | (rw [Qed.Html.htmlHasLangList_mapList]; intro $c _; simpa [Qed.Html.htmlHasLang_map] using $childStyled $c)))))

elab "qedDischargeStyledForEach" view:ident field:ident childStyled:ident nm:ident pred:term : tactic => do
  evalTactic (← `(tactic| forEachStyleLift $view $childStyled))
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let mut body : MessageData := m!""
    for g in goals do
      body := body ++ (← g.withContext do
        let s ← Qed.Diag.ppQedExpr (← g.getType) ["m"]
        let why :=
          if (s.splitOn "everyElementL").length > 1 then
            s!"child list didn't match `{childStyled.getId}` — check that both use the same role and styles."
          else
            "an element outside the collection wasn't covered — check if the parent view also renders that role."
        pure m!"\n  • {why}\n    must satisfy:  {s}")
    let predStr := (pred.raw.reprint.getD "the rule").trimmed
    throwErrorAt nm m!"Styling invariant `{nm.getId}` failed to lift `{predStr}` over `{field.getId}` in `{view.getId}`:{body}\n\nHint: Finish the remaining branch with `forEachStyleLift`:\n  invariant {nm.getId} : {predStr} for_each {field.getId} using {childStyled.getId} := by\n    forEachStyleLift {view.getId} {childStyled.getId}\n    …"

syntax (name := invariantForEachStyled)
  "qedInternalInvariant " ident " : " term " for_each " ident " holds_in " ident " using " ident
    (" := " term)? : command

macro_rules
  | `(qedInternalInvariant $name:ident : $pred for_each $_:ident holds_in $view:ident using $_:ident := $pf:term) =>
    `(theorem $name:ident : ∀ m, ($pred) ($view m) = true := $pf)
  | `(qedInternalInvariant $name:ident : $pred for_each $field:ident holds_in $view:ident using $childStyled:ident) =>
    `(set_option linter.unusedSimpArgs false in
      theorem $name:ident : ∀ m, ($pred) ($view m) = true := by
        qedDischargeStyledForEach $view $field $childStyled $name $pred)

syntax (name := invariantForEachSugar)
  "qedInternalInvariant " ident " : " ident " for_each " ident " preserved_by " ident : command
syntax (name := invariantForEachStyledSugar)
  "qedInternalInvariant " ident " : " ident " for_each " ident " holds_in " ident : command

open Elab Command Term Meta Lean.PrettyPrinter in
elab_rules : command
  | `(qedInternalInvariant $name:ident : $childInv:ident for_each $field:ident preserved_by $upd:ident) => do
      let pred ← liftTermElabM (extractInvPred childInv)
      elabCommand (← `(qedInternalInvariant $name : $pred for_each $field preserved_by $upd using $childInv))
  | `(qedInternalInvariant $name:ident : $childStyled:ident for_each $field:ident holds_in $view:ident) => do
      let pred ← liftTermElabM do
        let cn ← realizeGlobalConstNoOverload childStyled
        forallTelescope (← getConstInfo cn).type fun _ body => do
          let some lhs := body.eq?.map (·.2.1) | throwErrorAt childStyled
            "`{childStyled}` doesn't look like a `… holds_in …` invariant, so its predicate can't be \
             inferred, write it explicitly (`<pred> for_each … using {childStyled}`)."
          delab lhs.appFn!
      elabCommand (← `(qedInternalInvariant $name : $pred for_each $field holds_in $view using $childStyled))

end Qed
