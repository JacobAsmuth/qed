import Qed.Verify.Core

namespace Qed

class InvTarget (α : Type) (Model : outParam Type) where
  proj : α → Model

instance {Model : Type} : InvTarget Model Model := ⟨id⟩
instance {Model β : Type} : InvTarget (Model × β) Model := ⟨Prod.fst⟩

@[simp] theorem InvTarget.proj_id {Model : Type} (m : Model) :
    InvTarget.proj m = m := rfl
@[simp] theorem InvTarget.proj_fst {Model β : Type} (p : Model × β) :
    InvTarget.proj p = p.1 := rfl

abbrev dictSimpNames : Array Lean.Name := Qed.Verify.Core.dictSimpNames

open Lean Elab Tactic Qed.Verify.Core

private def boundaryLemmaGroups : Array (Name × Array Name) := #[
  (``Array.size, #[``Array.size_push, ``Array.size_modify, ``Array.size_set, ``Array.size_pop,
    ``Array.size_map, ``Array.size_append, ``Array.size_eraseIdx, ``Array.size_reverse,
    ``Array.size_extract, ``Array.size_swap, ``Array.size_mergeSort]),
  (``Array.sumBy, #[``Array.sumBy_empty, ``Array.sumBy_push, ``Array.sumBy_append, ``Array.sumBy_map,
    ``Array.sumBy_reverse, ``Array.sumBy_mergeSort]),
  (``Array.sumByInt, #[``Array.sumByInt_empty, ``Array.sumByInt_push, ``Array.sumByInt_append,
    ``Array.sumByInt_map, ``Array.sumByInt_mergeSort]),
  (``Array.countWhere, #[``Array.countWhere_empty, ``Array.countWhere_push, ``Array.countWhere_append,
    ``Array.countWhere_reverse, ``Array.countWhere_mergeSort]),
  (``Array.uniqueBy, #[``Array.uniqueBy_empty, ``Array.uniqueBy_push_iff]),
  (``Array.isSortedBy, #[``Array.isSortedBy_empty, ``Array.isSortedBy_singleton, ``Array.isSortedBy_push_iff]),
  (``List.length, #[``List.length_cons, ``List.length_append, ``List.length_map]),
  (``Qed.Lang.QedSeqLit.ofList, #[``Qed.Lang.QedSeqLit.ofList_array, ``Qed.Lang.QedSeqLit.ofList_list]),
  (``Qed.Lang.QedMem.mem, #[``Qed.Lang.QedMem.mem_array, ``Qed.Lang.QedMem.mem_list, ``Qed.Lang.QedMem.mem_string]),
  (``Qed.Lang.QedMemProp.memProp, #[``Qed.Lang.QedMemProp.memProp_array, ``Qed.Lang.QedMemProp.memProp_list, ``Qed.Lang.QedMemProp.memProp_string]),
  (``Qed.Lang.QedAndProp, #[``Qed.Lang.not_qedAndProp]),
  (``Qed.Lang.QedOrProp, #[``Qed.Lang.not_qedOrProp])]

private def relevantBoundaryLemmas (cs : Std.HashSet Name) : Array Name :=
  boundaryLemmaGroups.foldl (init := #[``Qed.Lang.QedVal.val_id]) fun acc (k, ns) =>
    if cs.contains k then acc ++ ns else acc

private def relevantAppLemmas (env : Environment) (cs : Std.HashSet Name) : Array Name := Id.run do
  let mut r : Array Name := #[``InvTarget.proj_id, ``InvTarget.proj_fst]
  let hasApp := #[`Qed.Internal.mkApp, `Qed.Internal.mkRoutedApp, `Qed.App.init, `Qed.App.update,
    `Qed.Internal.App.withDehydrate, `Qed.Internal.App.withQueries, `Qed.Internal.App.withSubscriptions,
    `Qed.Internal.App.withStylesheets, `Qed.Internal.App.withExtraStyles,
    `Qed.App.withHead, `Qed.App.withSsrStatus].any cs.contains
  if hasApp then
    r := r ++ appProjSimpNames env #["init", "update"] ++
      #[`Qed.Query.boot, `Qed.Query.wrap, `Qed.Resource.query, `Qed.Resource.rpcQuery,
        `Qed.Subscription.boot, `Qed.Subscription.wrap, `Qed.Subscription.boot_state_eq].filter env.contains
  if cs.contains `Qed.Cached.activate || cs.contains `Qed.Cached.all then
    r := r ++ #[`Qed.Cached.activate, `Qed.Cached.all_empty].filter env.contains
  return r

private def relevantOptResLemmas (env : Environment) (cs : Std.HashSet Name) : Array Name := Id.run do
  let mut r : Array Name := #[]
  if cs.contains `Qed.Cached.all || cs.contains `Qed.Resource.all then
    r := r ++ #[`Qed.Cached.all, `Qed.Resource.all].filter env.contains
  if cs.contains ``Qed.Lang.QedVal.val then
    r := r ++ #[`Qed.QedVal.val_field, `Qed.QedVal.val_ensured].filter env.contains
  if cs.contains `Qed.Codec.valid || cs.contains `Qed.Field || cs.contains `Qed.Ensured then
    r := r ++ optCodecSimpNames.filter env.contains
  if #[`Qed.Dict, `Qed.Dict.size, `Qed.Dict.get, `Qed.Dict.set, `Qed.Dict.remove, `Qed.Dict.contains].any cs.contains then
    r := r ++ dictSimpNames.filter env.contains
  return r

private def stripStepPrefix : Name → Name
  | .str `step s => Name.mkSimple s
  | .str p s     =>
      let p' := stripStepPrefix p
      if p' == .anonymous then Name.mkSimple s else .str p' s
  | n => n

private def runUnfoldPresent (extra : Array Term) : TacticM Unit := do
  let g :: _ ← getGoals | return
  let env0 ← getEnv
  let cs ← collectGoalConsts g true
  let fixedNames := relevantAppLemmas env0 cs ++ relevantBoundaryLemmas cs
  let fixedL := (← namesToSimpLemmas fixedNames) ++ (← termsToSimpLemmas extra)
  qedUnfoldHelperLoop 12
    (fun env n => return qedIsHelper env n && (← getProjectionFnInfo? n).isNone)
    fixedL (includeLCtx := true) (useSimpAll := true)

private def runAddFieldFacts : TacticM Unit := do
  let env ← getEnv
  unless env.contains `Qed.Field.ok || env.contains `Qed.Ensured.ok || env.contains `Qed.Dict.size_remove_le do return
  let g ← getMainGoal
  let (g', _) ← collectAndAssertFacts g "_qedFld" {
    includeFin := false
    includeDictRemove := true
    rounds := 1
  }
  replaceMainGoal [g']

private def runFastClose : TacticM Unit := do
  if ← tryCloseTrivial (← getMainGoal) (reducibleOnly := true) then
    replaceMainGoal []
  else
    throwError "qedFastClose: not trivially closed"

private def runDestructExistsHyps : TacticM Unit := do
  let g :: rem ← getGoals | return
  let (g', _) ← splitAndHypsGoal g (existsOnly := true) (maxIters := 16)
  setGoals (g' :: rem)

private def mkPredUnfold (pred : Term) : TacticM (Term × TSyntax `tactic) := do
  let pred := match pred with | `(($p)) => p | p => p
  let unfoldPred ← if pred.raw.isIdent
    then `(tactic| try simp only [$(⟨pred.raw⟩):ident] at *)
    else `(tactic| skip)
  return (pred, unfoldPred)

private def throwUnsolvedInvGoals (nm : Ident) (hdr footer : MessageData) : TacticM Unit :=
  Qed.Diag.throwUnsolvedGoals hdr m!"\n\n{footer}" (ref? := some nm) (maxShown? := some 6)
    (formatGoal? := some fun g => g.withContext do
      let tagLabel := Qed.Diag.formatCaseTag (stripStepPrefix (← g.getTag))
      let ty ← instantiateMVars (← g.getType)
      let tgt ← Qed.Diag.ppQedExpr ty ["m"]
      let env ← getEnv
      let present ← (ty.getUsedConstants.filter (qedIsHelper env)).filterM
        (fun n => return (← getProjectionFnInfo? n).isNone)
      let involves := if present.isEmpty then ""
        else s!"\n    (involves helper: {String.intercalate ", " (present.toList.map toString)})"
      return some s!"  • {tagLabel} must satisfy:  {tgt}{involves}")

elab "qedUnfoldPresent" "[" extra:term,* "]" : tactic => runUnfoldPresent extra.getElems
elab "qedAddFieldFacts" : tactic => runAddFieldFacts
elab "qedFastClose" : tactic => runFastClose
elab "qedDestructExistsHyps" : tactic => runDestructExistsHyps

/-- General single-goal closer escalating from fast linear/decidable checks to nonlinear
    monotonicity and Lean 4's `grind` (quantified collections, congruence closure, ring).
    Always fails (leaving state untouched for `first` backtracking) if any goal remains. -/
macro "qedAutoClose" : tactic => `(tactic|
  (first
    | qedFastClose
    | omega
    | decide
    | assumption
    | rfl
    | (qedNonlinearClose; done)
    | (try (repeat' (apply And.intro)); all_goals (first | qedFastClose | omega | decide | (qedNonlinearClose; done) | grind); done)))

private def runCloseStateGoal (extra : Array Term) : TacticM Unit := do
  let g0 :: rest ← getGoals | return
  let env0 ← getEnv
  let cs ← collectGoalConsts g0 true
  let relNames := relevantOptResLemmas env0 cs ++ relevantBoundaryLemmas cs
  let g ← if extra.isEmpty then
      if relNames.isEmpty then pure g0 else do
        let ctx ← mkDynamicSimpCtx relNames
        match ← trySimpAll g0 ctx with
        | none    => setGoals rest; return
        | some g' => setGoals (g' :: rest); pure g'
    else do
      let relL := (← namesToSimpLemmas relNames) ++ (← termsToSimpLemmas extra)
      if !relL.isEmpty then
        try evalTactic (← `(tactic| simp_all only [$[$relL],*])) catch _ => pure ()
      let g' :: _ ← getGoals | return
      pure g'
  if ← tryCloseTrivial g (reducibleOnly := true) then
    replaceMainGoal []; return
  if ← tryDirectOmega g then
    replaceMainGoal []; return
  if ← tryDirectDecide g then
    replaceMainGoal []; return
  let relL := (← namesToSimpLemmas relNames) ++ (← termsToSimpLemmas extra)
  evalTactic (← `(tactic|
    first
      | (qedNonlinearClose; done)
      | (qedAutoClose; done)
      | (simp_all [$[$relL],*] <;> qedAutoClose; done)
      | skip))

private def runCloseCachedPut (extraL : Array Term) : TacticM Unit := do
  unless (← getEnv).contains `Qed.Cached.all_put do return
  let gs0 ← getGoals
  let anyCached ← gs0.anyM fun g =>
    return (← g.withContext (instantiateMVars (← g.getType))).getUsedConstants.contains `Qed.Cached.all
  unless anyCached do return
  let extraSimpL ← termsToSimpLemmas extraL
  for _ in [0:8] do
    let goals ← getGoals
    if goals.isEmpty then return
    let mut progressed := false
    let mut rem : List MVarId := []
    for g in goals do
      setGoals [g]
      let tgt ← g.withContext (instantiateMVars (← g.getType))
      if tgt.isAppOfArity ``And 2 && tgt.getUsedConstants.contains `Qed.Cached.all then
        evalTactic (← `(tactic| apply And.intro))
        progressed := true
      else if tgt.isAppOfArity `Qed.Cached.all 3 then
        let cArg := tgt.getAppArgs[2]!.consumeMData
        if cArg.isAppOfArity `Qed.Cached.put 5 then
          let saved ← saveState
          let allPutId := mkIdent `Qed.Cached.all_put
          let stripImpId := mkIdent `Qed.Resource.all_stripEnsured_of_imp
          let ok ← try
              evalTactic (← `(tactic| apply $allPutId))
              match ← getGoals with
              | [gHall, gHr] =>
                  setGoals [gHall]
                  evalTactic (← `(tactic| first | assumption | simp_all))
                  unless (← getUnsolvedGoals).isEmpty do throwError "hall unsolved"
                  setGoals [gHr]
                  evalTactic (← `(tactic| (
                    try (apply $stripImpId; intro _ _hEns; try dsimp only at _hEns; qedDestructExistsHyps);
                    qedUnfoldPresent [$[$extraL],*];
                    (try simp_all [$[$extraSimpL],*]);
                    all_goals (first | rfl | decide | omega | assumption | trivial))))
                  pure (← getUnsolvedGoals).isEmpty
              | _ => pure false
            catch _ => pure false
          if ok then
            progressed := true
            setGoals []
          else
            restoreState saved
      rem := rem ++ (← getGoals)
    setGoals rem
    unless progressed do break

elab "qedCloseStateGoal" "[" extra:term,* "]" : tactic => runCloseStateGoal extra.getElems
elab "qedCloseCachedPut" "[" extra:term,* "]" : tactic => runCloseCachedPut extra.getElems

private def mkInitTac (usingL : Array Term) (pred initT : Term) : TacticM (TSyntax `tactic) := do
  let (_, unfoldPred) ← mkPredUnfold pred
  let unfoldInit ← if initT.raw.isIdent
    then `(tactic| try simp only [$(⟨initT.raw⟩):ident] at *)
    else `(tactic| skip)
  `(tactic|
    ($unfoldPred:tactic;
     try dsimp only at *;
     $unfoldInit:tactic;
     qedUnfoldPresent [$[$usingL],*];
     try ((repeat' split) <;> qedCloseStateGoal [$[$usingL],*])))

syntax "qedDischargeInit " "[" term,* "]" term:max ident term:max : tactic

elab_rules : tactic
  | `(tactic| qedDischargeInit [$[$usingL],*] $initT $nm $pred) => do
    (← getMainGoal).setTag `init
    evalTactic (← mkInitTac usingL pred initT)
    let initName := if initT.raw.isIdent then toString initT.raw.getId
      else (initT.raw.reprint.getD (toString initT.raw)).trimAscii.toString
    throwUnsolvedInvGoals nm
      m!"Invariant `{nm.getId}` failed on initial state `{initName}`:"
      m!"Hint: Update the initial `state` values so `{nm.getId}` holds, add `using [lemma]`, or supply a `:= by` proof."

syntax "qedDischargePreserved " "[" term,* "]" term:max ident term:max (" from " term)? : tactic

elab_rules : tactic
  | `(tactic| qedDischargePreserved [$[$usingL],*] $upd $nm $pred $[from $init]?) => do
    let (_, unfoldPred) ← mkPredUnfold pred
    let env0 ← getEnv
    let cs0 ← collectGoalConsts (← getMainGoal) true
    let appL ← namesToSimpLemmas (relevantAppLemmas env0 cs0)
    let updL ← if upd.raw.isIdent
      then pure (#[← `(Lean.Parser.Tactic.simpLemma| $(⟨upd.raw⟩):term)] ++ appL)
      else match upd with
        | `((($a:ident).update)) => pure (#[← `(Lean.Parser.Tactic.simpLemma| $a:term)] ++ appL)
        | `(($a:ident).update)   => pure (#[← `(Lean.Parser.Tactic.simpLemma| $a:term)] ++ appL)
        | `(($fn:ident $_:term*)) => pure (#[← `(Lean.Parser.Tactic.simpLemma| $fn:term)] ++ appL)
        | _ => pure appL
    let stepTac ← `(tactic|
      (intro m msg h;
       $unfoldPred:tactic;
       try dsimp only at *;
       cases msg <;>
         (try simp_all only [$[$updL],*]) <;>
         qedUnfoldPresent [$[$usingL],*] <;>
         (try qedCloseCachedPut [$[$usingL],*]) <;>
         (try repeat' split) <;>
         (first | qedFastClose | omega | skip) <;>
         intros <;>
         (try repeat' split) <;>
         (try dsimp only at *) <;>
         qedAddFieldFacts <;>
         (try qedDestructExistsHyps) <;>
         qedUnfoldPresent [$[$usingL],*] <;>
         qedCloseStateGoal [$[$usingL],*]))
    match init with
    | some initT =>
        let initTac ← mkInitTac usingL pred initT
        let gs ← (← getMainGoal).apply (mkConst ``And.intro)
        match gs with
        | [gInit, gStep] =>
            gInit.setTag `init
            gStep.setTag `step
            setGoals [gInit]
            evalTactic initTac
            let remInit ← getUnsolvedGoals
            setGoals [gStep]
            evalTactic stepTac
            let remStep ← getUnsolvedGoals
            setGoals (remInit ++ remStep)
        | _ => throwError "internal error splitting invariant init/step goals"
    | none =>
        evalTactic stepTac
    let updName := if upd.raw.isIdent then toString upd.raw.getId
      else (upd.raw.reprint.getD (toString upd.raw)).trimAscii.toString
    throwUnsolvedInvGoals nm
      m!"Invariant `{nm.getId}` failed in `{updName}`:"
      m!"Hint: Guard the failing branch with `if ...:`, fix the update, or weaken the invariant.\n      If the rule does hold, add `using [lemma]` or a manual `:= by` proof."

end Qed
