import Qed.Component.Core
import Qed.Invariant.State
import Qed.Invariant.View

namespace Qed
open Lean Elab Tactic Qed.Verify.Core

/-- Extracts the view predicate `P` from a `∀ m, P (view m) = true` theorem. -/
def extractViewInvPred (childStyled : Ident) : Term.TermElabM Term := do
  let cn ← realizeGlobalConstNoOverload childStyled
  Meta.forallTelescope (← getConstInfo cn).type fun _ body => do
    let some lhs := body.eq?.map (·.2.1) | throwErrorAt childStyled
      "`{childStyled}` doesn't look like a `… holds_in …` invariant, so its predicate can't be \
       inferred, write it explicitly (`<pred> for_each … using {childStyled}`)."
    PrettyPrinter.delab lhs.appFn!

private def tryTac (mk : TacticM (TSyntax `tactic)) (requireClosed : Bool := false) : TacticM Bool := do
  let saved ← saveState
  try
    withoutRecover <| evalTactic (← mk)
    return !requireClosed || (← getGoals).isEmpty
  catch _ => restoreState saved; return false

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

private def runForEachArm (childInv : Ident)
    (elemClose mapClose : TSyntax `tactic) : TacticM Unit := do
  let h := mkIdent `h; let y := mkIdent `y; let hy := mkIdent `hy; let hP := mkIdent `hP
  let mkDirect (lem : Name) := `(tactic| exact $(mkIdent lem):ident $h)
  let mkElem (lem : Name) := `(tactic| (refine $(mkIdent lem):ident $h ?_ <;> ($elemClose:tactic)))
  let mkMap := `(tactic| (refine Qed.ForEach.forall_map ?_ <;> intro $y $hy <;> have $hP:ident := $h $y $hy <;> ($mapClose:tactic)))
  let mkMod := `(tactic| (refine Qed.ForEach.forall_modify $h ?_ <;> intro $y $hy $hP <;> ($mapClose:tactic)))
  let mkUk1 := `(tactic| exact Qed.ForEach.updateKeyed_forall _ _ $childInv $h)
  let mkUk2 := `(tactic| exact Qed.ForEach.updateKeyed_forall _ _ ($childInv).2 $h)
  let fastOk ← withMainContext do
    let tgt ← instantiateMVars (← getMainTarget)
    let some collRaw := extractForEachColl? tgt | return false
    let coll := Qed.stripLetE 16 collRaw
    let some nm := coll.getAppFn.constName? | return ← tryTac `(tactic| exact $h)
    if let some (_, lem) := forEachDirectTable.find? (·.1 == nm) then return ← tryTac (mkDirect lem)
    if let some (_, lem) := forEachElemTable.find? (·.1 == nm) then return ← tryTac (mkElem lem)
    if nm == ``Array.map then return ← tryTac mkMap
    if nm == ``Array.modify then return ← tryTac mkMod
    if nm == ``Qed.Component.updateKeyed || nm.getString! == "updateKeyed" then
      return (← tryTac mkUk1) || (← tryTac mkUk2)
    tryTac `(tactic| exact $h)
  if fastOk then return
  if ← tryTac `(tactic| exact $h) then return
  for (_, lem) in forEachDirectTable do if ← tryTac (mkDirect lem) then return
  for mk in #[mkUk1, mkUk2, mkMap, mkMod] do if ← tryTac mk then return
  for (_, lem) in forEachElemTable.take 4 do if ← tryTac (mkElem lem) then return
  let _ ← tryTac `(tactic| grind)

elab "forEachLift " upd:ident childInv:ident pred:term : tactic => do
  let predLem ← if pred.raw.isIdent
    then pure #[← `(Lean.Parser.Tactic.simpLemma| $(⟨pred.raw⟩):ident),
                ← `(Lean.Parser.Tactic.simpLemma| Qed.Lang.QedVal.val_id)]
    else pure #[← `(Lean.Parser.Tactic.simpLemma| Qed.Lang.QedVal.val_id)]
  let elemFallback ← if pred.raw.isIdent
    then `(tactic| first | omega | decide | trivial | simp_all | qedAutoClose)
    else `(tactic| first | omega | decide | trivial | simp | simp_all | qedAutoClose)
  let elemClose ← `(tactic| (try dsimp only) <;> (try simp only [$[$predLem],*]) <;> (try ($elemFallback:tactic)))
  -- Unhygienic binder names so manual `case … =>` proofs can reference `m`, `h`, `y`, `hP`.
  let m := mkIdent `m; let msg := mkIdent `msg; let h := mkIdent `h; let hP := mkIdent `hP
  let mapClose ← `(tactic|
    ((try dsimp only at $hP:ident ⊢) <;> (try simp only [$[$predLem],*] at $hP:ident ⊢) <;>
     (try (first | omega | decide | trivial | (simp_all <;> omega) | (simp_all <;> done) | qedAutoClose))))
  evalTactic (← `(tactic|
    (intro $m $msg $h
     cases $msg:ident <;>
       simp only [$upd:ident, InvTarget.proj_id, InvTarget.proj_fst])))
  let mut rem : List MVarId := []
  for g in (← getGoals) do
    setGoals [g]
    runForEachArm childInv elemClose mapClose
    rem := rem ++ (← getGoals)
  setGoals rem

elab "qedDischargeForEach" upd:ident childInv:ident nm:ident pred:term : tactic => do
  evalTactic (← `(tactic| forEachLift $upd $childInv $pred))
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let firstTag ← goals[0]!.getTag
    let predStr := (pred.raw.reprint.getD "the contract").trimmed
    Qed.Diag.throwUnsolvedGoals
      m!"Invariant `{nm.getId}` failed to lift `{predStr}` across `{upd.getId}`:"
      m!"\n\nHint: Ensure newly inserted elements satisfy `{predStr}`, or prove only the remaining branch:\n  invariant {nm.getId} : {predStr} for_each … using {childInv.getId} := by\n    forEachLift {upd.getId} {childInv.getId} {predStr}\n    case {firstTag} => …"
      (ref? := some nm) (goals? := some goals)
      (formatGoal? := some fun g => g.withContext do
        let ty ← instantiateMVars (← g.getType)
        let s ← Qed.Diag.ppQedExpr ty ["m"]
        let tagLabel := Qed.Diag.formatCaseTag (← g.getTag)
        let why :=
          if (s.splitOn "qsort").length > 1 then
            "uses `Array.qsort` (no membership lemma); switch to Qed's verified `sortBy` so it lifts automatically."
          else if (s.splitOn " ++ ").length > 1 then
            "appends elements (`++`) not known to satisfy the contract; validate them first or prove this case."
          else if ty.isForall then
            "transforms the collection with an unverified operation; add a lemma or prove this case."
          else
            "inserts an element not known to satisfy the contract."
        return some s!"  • {tagLabel}: {why}\n    must satisfy:  {s}")

private def a11yForEachLiftPairs : Array (Name × Name) := #[
  (``Qed.Html.imgsHaveAltList_mapList,        ``Qed.Html.imgsHaveAlt_map),
  (``Qed.Html.buttonsAccessibleList_mapList,  ``Qed.Html.buttonsAccessible_map),
  (``Qed.Html.validAriaRolesList_mapList,     ``Qed.Html.validAriaRoles_map),
  (``Qed.Html.labelsAssociatedList_mapList,   ``Qed.Html.labelsAssociated_map),
  (``Qed.Html.htmlHasLangList_mapList,        ``Qed.Html.htmlHasLang_map)
]

elab "forEachStyleLift " view:ident childStyled:ident : tactic => do
  let c := mkIdent `c
  let liftChild ← `(tactic|
    (refine Qed.everyElement_through_map _ _ ?_ ($childStyled $c) <;>
      (intro t a;
       first
         | (simp only [Qed.attrRole_map, Qed.attrClasses_map, Qed.hasOneClass]; done)
         | (simp [Qed.attrRole_map, Qed.attrClasses_map, Qed.hasOneClass]; done))))
  let everyArm ← `(tactic|
    (rw [Qed.everyElementL_mapList]
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
            | rfl))))
  evalTactic (← `(tactic| (intro m; qedStyleReduce $view)))
  let mut rem : List MVarId := []
  for g in (← getGoals) do
    setGoals [g]
    if !(← tryTac (pure everyArm) (requireClosed := true)) then
      let closed ← a11yForEachLiftPairs.anyM fun (mapListLem, mapLem) =>
        tryTac (requireClosed := true) `(tactic|
          (rw [$(mkIdent mapListLem):ident]; intro $c _; simpa [$(mkIdent mapLem):ident] using $childStyled $c))
      unless closed do rem := rem ++ (← getGoals)
  setGoals rem

elab "qedDischargeStyledForEach" view:ident field:ident childStyled:ident nm:ident pred:term : tactic => do
  evalTactic (← `(tactic| forEachStyleLift $view $childStyled))
  let predStr := (pred.raw.reprint.getD "the rule").trimmed
  Qed.Diag.throwUnsolvedGoals
    m!"Styling invariant `{nm.getId}` failed to lift `{predStr}` over `{field.getId}` in `{view.getId}`:"
    m!"\n\nHint: Finish the remaining branch with `forEachStyleLift`:\n  invariant {nm.getId} : {predStr} for_each {field.getId} using {childStyled.getId} := by\n    forEachStyleLift {view.getId} {childStyled.getId}\n    …"
    (ref? := some nm)
    (formatGoal? := some fun g => g.withContext do
      let s ← Qed.Diag.ppQedExpr (← g.getType) ["m"]
      let why :=
        if (s.splitOn "everyElementL").length > 1 then
          s!"child list didn't match `{childStyled.getId}` — check that both use the same role and styles."
        else
          "an element outside the collection wasn't covered — check if the parent view also renders that role."
      return some s!"  • {why}\n    must satisfy:  {s}")

end Qed
