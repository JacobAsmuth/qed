import Qed.Verify.Core

namespace Qed

class InvTarget (α : Type) (Model : outParam Type) where proj : α → Model
instance {Model : Type} : InvTarget Model Model := ⟨id⟩
instance {Model β : Type} : InvTarget (Model × β) Model := ⟨Prod.fst⟩
@[simp] theorem InvTarget.proj_id {Model : Type} (m : Model) : InvTarget.proj m = m := rfl
@[simp] theorem InvTarget.proj_fst {Model β : Type} (p : Model × β) : InvTarget.proj p = p.1 := rfl

open Lean Elab Tactic Qed.Verify.Core

private def boundaryLemmaGroups : Array (Name × Array Name) := #[
  (``Array.size, #[``Array.size_push, ``Array.size_modify, ``Array.size_set, ``Array.size_pop, ``Array.size_map, ``Array.size_append, ``Array.size_eraseIdx, ``Array.size_reverse, ``Array.size_extract, ``Array.size_swap, ``Array.size_mergeSort]),
  (``Array.sumBy, #[``Array.sumBy_empty, ``Array.sumBy_push, ``Array.sumBy_append, ``Array.sumBy_map, ``Array.sumBy_reverse, ``Array.sumBy_mergeSort]),
  (``Array.sumByInt, #[``Array.sumByInt_empty, ``Array.sumByInt_push, ``Array.sumByInt_append, ``Array.sumByInt_map, ``Array.sumByInt_reverse, ``Array.sumByInt_mergeSort]),
  (``Array.countWhere, #[``Array.countWhere_empty, ``Array.countWhere_push, ``Array.countWhere_append, ``Array.countWhere_reverse, ``Array.countWhere_mergeSort]),
  (``Array.uniqueBy, #[``Array.uniqueBy_empty, ``Array.uniqueBy_push_iff]),
  (``Array.isSortedBy, #[``Array.isSortedBy_empty, ``Array.isSortedBy_singleton, ``Array.isSortedBy_push_iff]),
  (``List.length, #[``List.length_cons, ``List.length_append, ``List.length_map]),
  (``Qed.Lang.QedSeqLit.ofList, #[``Qed.Lang.QedSeqLit.ofList_array, ``Qed.Lang.QedSeqLit.ofList_list]),
  (``Qed.Lang.QedMem.mem, #[``Qed.Lang.QedMem.mem_array, ``Qed.Lang.QedMem.mem_list, ``Qed.Lang.QedMem.mem_string]),
  (``Qed.Lang.QedMemProp.memProp, #[``Qed.Lang.QedMemProp.memProp_array, ``Qed.Lang.QedMemProp.memProp_list, ``Qed.Lang.QedMemProp.memProp_string]),
  (``Qed.Lang.QedAndProp, #[``Qed.Lang.not_qedAndProp]), (``Qed.Lang.QedOrProp, #[``Qed.Lang.not_qedOrProp])]

private def relevantBoundaryLemmas (cs : Std.HashSet Name) : Array Name :=
  boundaryLemmaGroups.foldl (init := #[``Qed.Lang.QedVal.val_id]) fun acc (k, ns) => if cs.contains k then acc ++ ns else acc

private def collectTriggered (env : Environment) (cs : Std.HashSet Name) (init : Array Name) (groups : Array (Array Name × Array Name)) : Array Name :=
  groups.foldl (init := init) fun acc (triggers, lemmas) => if triggers.any cs.contains then acc ++ lemmas.filter env.contains else acc

private def relevantAppLemmas (env : Environment) (cs : Std.HashSet Name) : Array Name :=
  collectTriggered env cs #[``InvTarget.proj_id, ``InvTarget.proj_fst] #[
    (appWrapperBases ++ #[`Qed.App.init, `Qed.App.update], appProjSimpNames env #["init", "update"] ++
      #[`Qed.Query.boot, `Qed.Query.wrap, `Qed.Resource.query, `Qed.Resource.rpcQuery, `Qed.Subscription.boot, `Qed.Subscription.wrap, `Qed.Subscription.boot_state_eq]),
    (#[`Qed.Cached.activate, `Qed.Cached.all], #[`Qed.Cached.activate, `Qed.Cached.all_empty])]

private def relevantOptResLemmas (env : Environment) (cs : Std.HashSet Name) : Array Name :=
  collectTriggered env cs #[] #[
    (#[`Qed.Cached.all, `Qed.Resource.all], #[`Qed.Cached.all, `Qed.Resource.all]),
    (#[``Qed.Lang.QedVal.val], #[`Qed.QedVal.val_field, `Qed.QedVal.val_ensured]),
    (#[`Qed.Codec.valid, `Qed.Field, `Qed.Ensured], optCodecSimpNames),
    (#[`Qed.Dict, `Qed.Dict.size, `Qed.Dict.get, `Qed.Dict.set, `Qed.Dict.remove, `Qed.Dict.contains], dictSimpNames)]

private def stripStepPrefix : Name → Name
  | .str `step s => Name.mkSimple s
  | .str p s     => let p' := stripStepPrefix p; if p' == .anonymous then Name.mkSimple s else .str p' s
  | n => n

private def runUnfoldPresent (extra : Array Term) : TacticM Unit := do
  let g :: _ ← getGoals | return
  let cs ← collectGoalConsts g true
  let fixedL := (← namesToSimpLemmas (relevantAppLemmas (← getEnv) cs ++ relevantBoundaryLemmas cs)) ++ (← termsToSimpLemmas extra)
  qedUnfoldHelperLoop 12 (fun env n => if !qedIsHelper env n then return false else return (← getProjectionFnInfo? n).isNone)
    fixedL (includeLCtx := true) (useSimpAll := true)

private def runAddFieldFacts : TacticM Unit := do
  let env ← getEnv
  unless env.contains `Qed.Field.ok || env.contains `Qed.Ensured.ok || env.contains `Qed.Dict.size_remove_le do return
  replaceMainGoal [(← collectAndAssertFacts (← getMainGoal) "_qedFld" { includeFin := false, includeDictRemove := true }).1]

private def runFastClose : TacticM Unit := do
  if ← tryCloseTrivial (← getMainGoal) (reducibleOnly := true) then replaceMainGoal []
  else throwError "qedFastClose: not trivially closed"

elab "qedUnfoldPresent" "[" extra:term,* "]" : tactic => runUnfoldPresent extra.getElems
elab "qedFastClose" : tactic => runFastClose

macro "qedAutoClose" : tactic => `(tactic|
  (first
    | qedFastClose | omega | decide | assumption | rfl | (qedNonlinearClose; done)
    | (try (repeat' (apply And.intro)); all_goals (first | qedFastClose | omega | decide | (qedNonlinearClose; done) | grind); done)))

private def runCloseStateGoal (extra : Array Term) : TacticM Unit := do
  let g0 :: rest ← getGoals | return
  let cs ← collectGoalConsts g0 true
  let relNames := relevantOptResLemmas (← getEnv) cs ++ relevantBoundaryLemmas cs
  let g ← if extra.isEmpty then
      if relNames.isEmpty then pure g0 else do
        match ← trySimpAll g0 (← mkDynamicSimpCtx relNames) with | none => setGoals rest; return | some g' => setGoals (g' :: rest); pure g'
    else do
      let relL := (← namesToSimpLemmas relNames) ++ (← termsToSimpLemmas extra)
      if !relL.isEmpty then discard <| tryTac `(tactic| simp_all only [$[$relL],*])
      let g' :: _ ← getGoals | return
      pure g'
  if ← tryCloseBasic g (reducibleOnly := true) then replaceMainGoal []; return
  let relL := (← namesToSimpLemmas relNames) ++ (← termsToSimpLemmas extra)
  evalTactic (← `(tactic| first | (qedNonlinearClose; done) | (qedAutoClose; done) | (simp_all [$[$relL],*] <;> qedAutoClose; done) | skip))

private def runCloseCachedPut (extraL : Array Term) : TacticM Unit := do
  unless (← getEnv).contains `Qed.Cached.all_put do return
  unless ← (← getGoals).anyM fun g => return (← g.withContext (instantiateMVars (← g.getType))).getUsedConstants.contains `Qed.Cached.all do return
  let extraSimpL ← termsToSimpLemmas extraL
  for _ in [0:8] do
    if (← getGoals).isEmpty then return
    let progressedRef ← IO.mkRef false
    forEachGoal fun g => do
      let tgt ← g.withContext (instantiateMVars (← g.getType))
      if tgt.isAppOfArity ``And 2 && tgt.getUsedConstants.contains `Qed.Cached.all then
        evalTactic (← `(tactic| apply And.intro)); progressedRef.set true
      else if tgt.isAppOfArity `Qed.Cached.all 3 && tgt.getAppArgs[2]!.consumeMData.isAppOfArity `Qed.Cached.put 5 then
        let allPutId := mkIdent `Qed.Cached.all_put; let stripImpId := mkIdent `Qed.Resource.all_stripEnsured_of_imp
        if ← tryRestoreM false id do
            evalTactic (← `(tactic| apply $allPutId))
            let [gHall, gHr] ← getGoals | return false
            setGoals [gHall]; evalTactic (← `(tactic| first | assumption | simp_all))
            unless (← getUnsolvedGoals).isEmpty do return false
            setGoals [gHr]; discard <| tryTac `(tactic| (apply $stripImpId; intro _ _hEns; try dsimp only at _hEns))
            if let g1 :: r1 ← getGoals then setGoals ((← splitAndHypsGoal g1 true 16).1 :: r1)
            runUnfoldPresent extraL
            evalTactic (← `(tactic| ((try simp_all [$[$extraSimpL],*]); all_goals (first | rfl | decide | omega | assumption | trivial))))
            return (← getUnsolvedGoals).isEmpty
        then progressedRef.set true; setGoals []
    unless ← progressedRef.get do break

private def unfoldIdentTac (t : Term) : TacticM (TSyntax `tactic) :=
  let t := match t with | `(($p)) => p | p => p
  if t.raw.isIdent then `(tactic| try simp only [$(⟨t.raw⟩):ident] at *) else `(tactic| skip)

private def runInitPass (usingL : Array Term) (pred initT : Term) : TacticM Unit := do
  evalTactic (← `(tactic| ($(← unfoldIdentTac pred); try dsimp only at *; $(← unfoldIdentTac initT))))
  runUnfoldPresent usingL; discard <| tryTac `(tactic| repeat' split)
  forEachGoal fun _ => try runCloseStateGoal usingL catch _ => pure ()

private def formatTargetName (t : Term) : String :=
  if t.raw.isIdent then toString t.raw.getId else (t.raw.reprint.getD (toString t.raw)).trimAscii.toString

private def throwUnsolvedInvGoals (nm : Ident) (hdr footer : MessageData) : TacticM Unit :=
  Qed.Diag.throwUnsolvedGoals hdr m!"\n\n{footer}" (ref? := some nm) (maxShown? := some 6)
    (formatGoal? := some fun g => g.withContext do
      let tagLabel := Qed.Diag.formatCaseTag (stripStepPrefix (← g.getTag))
      let ty ← instantiateMVars (← g.getType); let tgt ← Qed.Diag.ppQedExpr ty ["m"]; let env ← getEnv
      let present ← (ty.getUsedConstants.filter (qedIsHelper env)).filterM fun n => return (← getProjectionFnInfo? n).isNone
      let involves := if present.isEmpty then "" else s!"\n    (involves helper: {String.intercalate ", " (present.toList.map toString)})"
      return some s!"  • {tagLabel} must satisfy:  {tgt}{involves}")

syntax "qedDischargeInit " "[" term,* "]" term:max ident term:max : tactic
syntax "qedDischargePreserved " "[" term,* "]" term:max ident term:max (" from " term)? : tactic

elab_rules : tactic
  | `(tactic| qedDischargeInit [$[$usingL],*] $initT $nm $pred) => do
    (← getMainGoal).setTag `init; runInitPass usingL pred initT
    throwUnsolvedInvGoals nm m!"Invariant `{nm.getId}` failed on initial state `{formatTargetName initT}`:"
      m!"Hint: Update the initial `state` values so `{nm.getId}` holds, add `using [lemma]`, or supply a `:= by` proof."

  | `(tactic| qedDischargePreserved [$[$usingL],*] $upd $nm $pred $[from $init]?) => do
    let unfoldPred ← unfoldIdentTac pred
    let appL ← namesToSimpLemmas (relevantAppLemmas (← getEnv) (← collectGoalConsts (← getMainGoal) true))
    let updL ← match upd with
      | `($a:ident) | `(($a:ident).update) | `((($a:ident).update)) | `(($a:ident $_:term*)) => pure (#[← `(Lean.Parser.Tactic.simpLemma| $a:term)] ++ appL)
      | _ => pure appL
    let runStep : TacticM Unit := do
      evalTactic (← `(tactic| (intro m msg h; $unfoldPred:tactic; try dsimp only at *; cases msg)))
      forEachGoal fun _ => do
        discard <| tryTac `(tactic| simp_all only [$[$updL],*])
        runUnfoldPresent usingL; try runCloseCachedPut usingL catch _ => pure ()
        discard <| tryTac `(tactic| repeat' split)
        forEachGoal fun g => do
          if ← tryCloseTrivial g (reducibleOnly := true) then setGoals []; return
          if ← tryDirectOmega g then setGoals []; return
          evalTactic (← `(tactic| (intros; try repeat' split; try dsimp only at *)))
          forEachGoal fun _ => do
            runAddFieldFacts
            if let g1 :: r1 ← getGoals then setGoals ((← splitAndHypsGoal g1 true 16).1 :: r1)
            runUnfoldPresent usingL; runCloseStateGoal usingL
    match init with
    | some initT =>
        let [gInit, gStep] ← (← getMainGoal).apply (mkConst ``And.intro) | throwError "internal error splitting invariant init/step goals"
        gInit.setTag `init; gStep.setTag `step
        setGoals [gInit]; runInitPass usingL pred initT; let remInit ← getUnsolvedGoals
        setGoals [gStep]; runStep; setGoals (remInit ++ (← getUnsolvedGoals))
    | none => runStep
    throwUnsolvedInvGoals nm m!"Invariant `{nm.getId}` failed in `{formatTargetName upd}`:"
      m!"Hint: Guard the failing branch with `if ...:`, fix the update, or weaken the invariant.\n      If the rule does hold, add `using [lemma]` or a manual `:= by` proof."

end Qed
