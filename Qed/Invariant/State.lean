import Qed.Runtime.App
import Qed.Diag
import Qed.Collection
import Lean

namespace Qed

class InvTarget (α : Type) (Model : outParam Type) where
  proj : α → Model

instance {Model : Type} : InvTarget Model Model := ⟨id⟩
instance {Model β : Type} : InvTarget (Model × β) Model := ⟨Prod.fst⟩

@[simp] theorem InvTarget.proj_id {Model : Type} (m : Model) :
    InvTarget.proj m = m := rfl
@[simp] theorem InvTarget.proj_fst {Model β : Type} (p : Model × β) :
    InvTarget.proj p = p.1 := rfl

syntax (name := invariantCmd)
  "qedInternalInvariant " ident " : " term (" from " term)? " preserved_by " ident
    (" using " "[" term,* "]")? (" := " term)? : command

open Lean Elab Tactic

private def qedBoundaryLemmas : Array Name :=
  #[``Array.size_push, ``Array.size_modify, ``Array.size_set, ``Array.size_pop,
    ``Array.size_map, ``Array.size_append, ``Array.size_eraseIdx, ``Array.size_reverse,
    ``Array.size_extract, ``Array.size_swap, ``Array.size_mergeSort,
    ``Array.sumBy_empty, ``Array.sumBy_push, ``Array.sumBy_append, ``Array.sumBy_map,
    ``Array.sumBy_reverse, ``Array.sumBy_mergeSort,
    ``Array.sumByInt_empty, ``Array.sumByInt_push, ``Array.sumByInt_append,
    ``Array.sumByInt_map, ``Array.sumByInt_mergeSort,
    ``Array.countWhere_empty, ``Array.countWhere_push, ``Array.countWhere_append,
    ``Array.countWhere_reverse, ``Array.countWhere_mergeSort,
    ``Array.uniqueBy_empty, ``Array.uniqueBy_push_iff,
    ``Array.isSortedBy_empty, ``Array.isSortedBy_singleton, ``Array.isSortedBy_push_iff,
    ``List.length_cons, ``List.length_append, ``List.length_map,
    ``Qed.Lang.QedVal.val_id, ``Qed.Lang.QedSeqLit.ofList_array, ``Qed.Lang.QedSeqLit.ofList_list,
    ``Qed.Lang.QedMem.mem_array, ``Qed.Lang.QedMem.mem_list, ``Qed.Lang.QedMem.mem_string,
    ``Qed.Lang.QedMemProp.memProp_array, ``Qed.Lang.QedMemProp.memProp_list, ``Qed.Lang.QedMemProp.memProp_string,
    ``Qed.Lang.not_qedAndProp, ``Qed.Lang.not_qedOrProp]

private def qedAppLemmas (env : Environment) : Array Name :=
  let base := #[``InvTarget.proj_id, ``InvTarget.proj_fst,
                ``Qed.Internal.mkApp_init, ``Qed.Internal.mkApp_update,
                ``Qed.Internal.mkRoutedApp_init, ``Qed.Internal.mkRoutedApp_update,
                ``Qed.Internal.App.withDehydrate_init, ``Qed.Internal.App.withDehydrate_update]
  let opt := #[`Qed.Internal.App.withQueries_init, `Qed.Internal.App.withQueries_update,
               `Qed.Internal.App.withSubscriptions_init, `Qed.Internal.App.withSubscriptions_update,
               `Qed.Internal.App.withStylesheets_init, `Qed.Internal.App.withStylesheets_update,
               `Qed.Internal.App.withExtraStyles_init, `Qed.Internal.App.withExtraStyles_update,
               `Qed.Query.boot, `Qed.Query.wrap, `Qed.Resource.query, `Qed.Resource.rpcQuery,
               `Qed.Subscription.boot, `Qed.Subscription.wrap, `Qed.Subscription.boot_state_eq,
               `Qed.Cached.activate, `Qed.Cached.all_empty].filter env.contains
  base ++ opt

private def stripStepPrefix : Name → Name
  | .str `step s => Name.mkSimple s
  | .str p s     =>
      let p' := stripStepPrefix p
      if p' == .anonymous then Name.mkSimple s else .str p' s
  | n => n

elab "qedUnfoldPresent" "[" extra:term,* "]" : tactic => do
  let toLemma (t : TSyntax `term) : TacticM (TSyntax `Lean.Parser.Tactic.simpLemma) :=
    `(Lean.Parser.Tactic.simpLemma| $t:term)
  let env0 ← getEnv
  let fixedNames := qedAppLemmas env0 ++ qedBoundaryLemmas
  let fixedL := (← fixedNames.mapM (fun n => toLemma ⟨(mkIdent n).raw⟩)) ++ (← extra.getElems.mapM toLemma)
  for _ in [0:12] do
    if (← getGoals).isEmpty then return
    let env ← getEnv
    let goal ← instantiateMVars (← getMainTarget)
    let mut usedConsts : Array Name := goal.getUsedConstants
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        let dTy ← instantiateMVars decl.type
        for c in dTy.getUsedConstants do
          if !usedConsts.contains c then usedConsts := usedConsts.push c
    let present ← (usedConsts.filter (qedIsHelper env)).filterM
      (fun n => return (← getProjectionFnInfo? n).isNone)
    if present.isEmpty then
      let _ ← try evalTactic (← `(tactic| simp_all only [$[$fixedL],*])) catch _ => pure ()
      return
    -- Splice a single combined array; comma-separated `$[…],*` splices fail when one is empty.
    let lemmas := (← present.mapM (fun n => toLemma ⟨(mkIdent n).raw⟩)) ++ fixedL
    let ok ← try
        evalTactic (← `(tactic| simp_all only [$[$lemmas],*]))
        pure true
      catch _ => pure false
    unless ok do return

private def toSimpLemmas (ts : Array Term) : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :=
  ts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)

private def mkOptResSimpLemmas (env : Environment) :
    TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :=
  toSimpLemmas ((#[`Qed.Cached.all, `Qed.Resource.all,
                   `Qed.QedVal.val_field, `Qed.QedVal.val_ensured,
                   `Qed.Codec.valid, `Qed.Codec.refine, `Qed.Codec.jsonOnly,
                   `Qed.Codec.text, `Qed.Codec.textarea, `Qed.Codec.nat,
                   `Qed.Codec.int, `Qed.Codec.checkbox, `Qed.Codec.date].filter env.contains).map
    fun n => ⟨(mkIdent n).raw⟩)

elab "qedAddFieldFacts" : tactic => do
  let env ← getEnv
  unless env.contains `Qed.Field.ok || env.contains `Qed.Ensured.ok do return
  let g ← getMainGoal
  let facts ← g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let mut scan : Array Expr := #[tgt]
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        scan := scan.push (← instantiateMVars decl.type)
    let factsRef ← IO.mkRef (#[] : Array Expr)
    let seenRef ← IO.mkRef (#[] : Array Expr)
    for e in scan do
      e.forEach fun sub => do
        if !sub.hasLooseBVars && (sub.isFVar || sub.isProj || sub.isApp) then
          let ty? ← try some <$> Meta.whnf (← Meta.inferType sub) catch _ => pure none
          if let some ty := ty? then
            if ty.isAppOfArity `Qed.Field 2 && env.contains `Qed.Field.ok then
              if !(← seenRef.get).contains sub then
                seenRef.modify (·.push sub)
                if let some okP ← try some <$> Meta.mkAppM `Qed.Field.ok #[sub] catch _ => pure none then
                  factsRef.modify (·.push okP)
            else if ty.isAppOfArity `Qed.Ensured 2 && env.contains `Qed.Ensured.ok then
              if !(← seenRef.get).contains sub then
                seenRef.modify (·.push sub)
                if let some okP ← try some <$> Meta.mkAppM `Qed.Ensured.ok #[sub] catch _ => pure none then
                  factsRef.modify (·.push okP)
    factsRef.get
  for idx in [0:facts.size] do
    let fPrf := facts[idx]!
    let g ← getMainGoal
    let fTy ← g.withContext (Meta.inferType fPrf)
    let (_, g') ← (← g.assert (Name.mkSimple s!"_qedFld{idx}") fTy fPrf).intro1P
    replaceMainGoal [g']

elab "qedFastClose" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  if tgt.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    replaceMainGoal []
    return
  let closed ← Meta.withTransparency .reducible do
    if let some (_, lhs, rhs) := tgt.eq? then
      if (← Meta.isDefEq lhs rhs) then
        g.assign (← Meta.mkEqRefl lhs)
        return true
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        if (← Meta.isDefEq decl.type tgt) then
          g.assign (mkFVar decl.fvarId)
          return true
    return false
  if closed then
    replaceMainGoal []
  else
    throwError "qedFastClose: not trivially closed"

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
    | qedNonlinearClose
    | (try (repeat' (apply And.intro)); all_goals (first | qedFastClose | omega | decide | qedNonlinearClose | grind); done)))

private def mkCloserLemmas (usingL : Array Term) : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let bL ← toSimpLemmas (qedBoundaryLemmas.map fun n => ⟨(mkIdent n).raw⟩)
  return bL ++ (← toSimpLemmas usingL)

private def mkPredUnfold (pred : Term) : TacticM (Term × TSyntax `tactic) := do
  let pred := match pred with | `(($p)) => p | p => p
  let unfoldPred ← if pred.raw.isIdent
    then `(tactic| try simp only [$(⟨pred.raw⟩):ident] at *)
    else `(tactic| skip)
  return (pred, unfoldPred)

private def mkInitTac (usingL : Array Term) (pred initT : Term) : TacticM (TSyntax `tactic) := do
  let (_, unfoldPred) ← mkPredUnfold pred
  let closerL ← mkCloserLemmas usingL
  let initCloserL := closerL ++ (← mkOptResSimpLemmas (← getEnv))
  let unfoldInit ← if initT.raw.isIdent
    then `(tactic| try simp only [$(⟨initT.raw⟩):ident] at *)
    else `(tactic| skip)
  `(tactic|
    ($unfoldPred:tactic;
     try dsimp only at *;
     $unfoldInit:tactic;
     qedUnfoldPresent [$[$usingL],*];
     try ((repeat' split) <;>
            (first | qedFastClose | omega | decide | qedNonlinearClose
                   | (simp_all [$[$initCloserL],*] <;> qedAutoClose; done)
                   | qedAutoClose))))

private def throwUnsolvedInvGoals (nm : Ident) (hdr footer : MessageData) : TacticM Unit := do
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let mut lines : Array String := #[]
    for g in goals do
      let line ← g.withContext do
        let tagLabel := Qed.Diag.formatCaseTag (stripStepPrefix (← g.getTag))
        let ty ← instantiateMVars (← g.getType)
        let tgt ← Qed.Diag.ppQedExpr ty ["m"]
        let env ← getEnv
        let present ← (ty.getUsedConstants.filter (qedIsHelper env)).filterM
          (fun n => return (← getProjectionFnInfo? n).isNone)
        let involves := if present.isEmpty then ""
          else s!"\n    (involves helper: {String.intercalate ", " (present.toList.map toString)})"
        pure s!"  • {tagLabel} must satisfy:  {tgt}{involves}"
      unless lines.contains line do
        lines := lines.push line
    let maxShown := 6
    let shown := lines.extract 0 (min lines.size maxShown)
    let extra := if lines.size > maxShown then s!"\n  • (+ {lines.size - maxShown} more failing branch(es))" else ""
    let body := String.intercalate "\n" shown.toList ++ extra
    throwErrorAt nm m!"{hdr}\n{body}\n\n{footer}"

syntax "qedDischargeInit " "[" term,* "]" term:max ident term:max : tactic

elab_rules : tactic
  | `(tactic| qedDischargeInit [$[$usingL],*] $initT $nm $pred) => do
    (← getMainGoal).setTag `init
    evalTactic (← mkInitTac usingL pred initT)
    let initName := if initT.raw.isIdent then toString initT.raw.getId
      else (initT.raw.reprint.getD (toString initT.raw)).trimmed
    throwUnsolvedInvGoals nm
      m!"Invariant `{nm.getId}` failed on initial state `{initName}`:"
      m!"Hint: Update the initial `state` values so `{nm.getId}` holds, add `using [lemma]`, or supply a `:= by` proof."

elab "qedDestructExistsHyps" : tactic => do
  for _ in [0:16] do
    let g :: rem ← getGoals | return
    let mut splitFv? : Option FVarId := none
    for decl in (← g.withContext getLCtx) do
      if splitFv?.isNone && !decl.isImplementationDetail && !decl.isLet then
        if (← g.withContext (Meta.whnf decl.type)).isAppOfArity ``Exists 2 then
          splitFv? := some decl.fvarId
    match splitFv? with
    | some fv =>
        let subgoals ← g.cases fv
        setGoals (subgoals.toList.map (·.mvarId) ++ rem)
    | none => break

elab "qedCloseCachedPut" "[" extra:term,* "]" : tactic => do
  unless (← getEnv).contains `Qed.Cached.all_put do return
  let gs0 ← getGoals
  let anyCached ← gs0.anyM fun g =>
    return (← g.withContext (instantiateMVars (← g.getType))).getUsedConstants.contains `Qed.Cached.all
  unless anyCached do return
  let extraL := extra.getElems
  let extraSimpL ← toSimpLemmas extraL
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

syntax "qedDischargePreserved " "[" term,* "]" term:max ident term:max (" from " term)? : tactic

elab_rules : tactic
  | `(tactic| qedDischargePreserved [$[$usingL],*] $upd $nm $pred $[from $init]?) => do
    let (_, unfoldPred) ← mkPredUnfold pred
    let env0 ← getEnv
    let appL ← toSimpLemmas ((qedAppLemmas env0).map fun n => ⟨(mkIdent n).raw⟩)
    let updL ← if upd.raw.isIdent
      then pure (#[← `(Lean.Parser.Tactic.simpLemma| $(⟨upd.raw⟩):term)] ++ appL)
      else match upd with
        | `((($a:ident).update)) => pure (#[← `(Lean.Parser.Tactic.simpLemma| $a:term)] ++ appL)
        | `(($a:ident).update)   => pure (#[← `(Lean.Parser.Tactic.simpLemma| $a:term)] ++ appL)
        | `(($fn:ident $_:term*)) => pure (#[← `(Lean.Parser.Tactic.simpLemma| $fn:term)] ++ appL)
        | _ => pure appL
    let closerL ← mkCloserLemmas usingL
    let finalCloserL := (← mkOptResSimpLemmas env0) ++ closerL
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
         (try simp_all only [$[$finalCloserL],*]) <;>
         (first | qedFastClose | omega | decide | qedNonlinearClose
                | (simp_all [$[$finalCloserL],*] <;> qedAutoClose; done)
                | qedAutoClose
                | skip)))
    match init with
    | some initT =>
        let initTac ← mkInitTac usingL pred initT
        let g0 ← getMainGoal
        let gs ← g0.apply (mkConst ``And.intro)
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
      else (upd.raw.reprint.getD (toString upd.raw)).trimmed
    throwUnsolvedInvGoals nm
      m!"Invariant `{nm.getId}` failed in `{updName}`:"
      m!"Hint: Guard the failing branch with `if ...:`, fix the update, or weaken the invariant.\n      If the rule does hold, add `using [lemma]` or a manual `:= by` proof."

macro_rules
  | `(qedInternalInvariant $name:ident : $pred from $init preserved_by $upd:ident using [$_ls,*] := $pf:term) =>
    `(theorem $name:ident : ($pred) ($init) ∧ ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(qedInternalInvariant $name:ident : $pred from $init preserved_by $upd:ident := $pf:term) =>
    `(theorem $name:ident : ($pred) ($init) ∧ ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(qedInternalInvariant $name:ident : $pred from $init preserved_by $upd:ident using [$ls,*]) =>
    `(theorem $name:ident : ($pred) ($init) ∧ ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        qedDischargePreserved [$ls,*] $upd $name ($pred) from $init)
  | `(qedInternalInvariant $name:ident : $pred from $init preserved_by $upd:ident) =>
    `(theorem $name:ident : ($pred) ($init) ∧ ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        qedDischargePreserved [] $upd $name ($pred) from $init)
  | `(qedInternalInvariant $name:ident : $pred preserved_by $upd:ident using [$_ls,*] := $pf:term) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(qedInternalInvariant $name:ident : $pred preserved_by $upd:ident := $pf:term) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(qedInternalInvariant $name:ident : $pred preserved_by $upd:ident using [$ls,*]) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        qedDischargePreserved [$ls,*] $upd $name ($pred))
  | `(qedInternalInvariant $name:ident : $pred preserved_by $upd:ident) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        qedDischargePreserved [] $upd $name ($pred))

open Lean Elab Command in
def mkConjBody (clauses : Array Term) : CommandElabM Term := do
  let props ← clauses.mapM fun c => `(($c : Prop))
  match props.toList with
  | []      => `(True)
  | p :: ps => ps.foldlM (init := p) fun acc x => `($acc ∧ $x)

open Lean Elab Command Term Meta Lean.PrettyPrinter in
def extractInvPred (id : Ident) : TermElabM (TSyntax `term) := do
  let cTy := (← getConstInfo (← realizeGlobalConstNoOverload id)).type
  let stepTy := if cTy.isAppOfArity ``And 2 then cTy.appArg! else cTy
  forallTelescope stepTy fun args _ => do
    let some hIdx ← (List.range args.size).findM? fun i => do
      return i ≥ 2 && (← isProp (← inferType args[i]!))
      | throwErrorAt id
          "`{id}` doesn't look like a state invariant, so its predicate can't be inferred; write it explicitly (`<pred> for_each … using {id}`)."
    delab (← mkLambdaFVars #[args[hIdx - 2]!] (← inferType args[hIdx]!)).eta

end Qed
