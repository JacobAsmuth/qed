import Qed.Lang
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

private def collectMainConsts (includeLCtx : Bool) : TacticM (Std.HashSet Name) :=
  withMainContext do
    let mut s : Std.HashSet Name := {}
    for c in (← instantiateMVars (← getMainTarget)).getUsedConstants do
      s := s.insert c
    if includeLCtx then
      for ldecl in (← getLCtx) do
        if !ldecl.isImplementationDetail then
          for c in (← instantiateMVars ldecl.type).getUsedConstants do
            s := s.insert c
    return s

private def pushIf (arr : Array Name) (cond : Bool) (ns : Array Name) : Array Name :=
  if cond then arr ++ ns else arr

private def relevantBoundaryLemmas (cs : Std.HashSet Name) : Array Name := Id.run do
  let mut r : Array Name := #[``Qed.Lang.QedVal.val_id]
  r := pushIf r (cs.contains ``Array.size)
    #[``Array.size_push, ``Array.size_modify, ``Array.size_set, ``Array.size_pop,
      ``Array.size_map, ``Array.size_append, ``Array.size_eraseIdx, ``Array.size_reverse,
      ``Array.size_extract, ``Array.size_swap, ``Array.size_mergeSort]
  r := pushIf r (cs.contains ``Array.sumBy)
    #[``Array.sumBy_empty, ``Array.sumBy_push, ``Array.sumBy_append, ``Array.sumBy_map,
      ``Array.sumBy_reverse, ``Array.sumBy_mergeSort]
  r := pushIf r (cs.contains ``Array.sumByInt)
    #[``Array.sumByInt_empty, ``Array.sumByInt_push, ``Array.sumByInt_append,
      ``Array.sumByInt_map, ``Array.sumByInt_mergeSort]
  r := pushIf r (cs.contains ``Array.countWhere)
    #[``Array.countWhere_empty, ``Array.countWhere_push, ``Array.countWhere_append,
      ``Array.countWhere_reverse, ``Array.countWhere_mergeSort]
  r := pushIf r (cs.contains ``Array.uniqueBy)
    #[``Array.uniqueBy_empty, ``Array.uniqueBy_push_iff]
  r := pushIf r (cs.contains ``Array.isSortedBy)
    #[``Array.isSortedBy_empty, ``Array.isSortedBy_singleton, ``Array.isSortedBy_push_iff]
  r := pushIf r (cs.contains ``List.length)
    #[``List.length_cons, ``List.length_append, ``List.length_map]
  r := pushIf r (cs.contains ``Qed.Lang.QedSeqLit.ofList)
    #[``Qed.Lang.QedSeqLit.ofList_array, ``Qed.Lang.QedSeqLit.ofList_list]
  r := pushIf r (cs.contains ``Qed.Lang.QedMem.mem)
    #[``Qed.Lang.QedMem.mem_array, ``Qed.Lang.QedMem.mem_list, ``Qed.Lang.QedMem.mem_string]
  r := pushIf r (cs.contains ``Qed.Lang.QedMemProp.memProp)
    #[``Qed.Lang.QedMemProp.memProp_array, ``Qed.Lang.QedMemProp.memProp_list, ``Qed.Lang.QedMemProp.memProp_string]
  r := pushIf r (cs.contains ``Qed.Lang.QedAndProp) #[``Qed.Lang.not_qedAndProp]
  r := pushIf r (cs.contains ``Qed.Lang.QedOrProp) #[``Qed.Lang.not_qedOrProp]
  return r

private def relevantAppLemmas (env : Environment) (cs : Std.HashSet Name) : Array Name := Id.run do
  let mut r : Array Name := #[``InvTarget.proj_id, ``InvTarget.proj_fst]
  let hasApp := cs.contains `Qed.Internal.mkApp || cs.contains `Qed.Internal.mkRoutedApp ||
    cs.contains `Qed.App.init || cs.contains `Qed.App.update ||
    cs.contains `Qed.Internal.App.withDehydrate || cs.contains `Qed.Internal.App.withQueries ||
    cs.contains `Qed.Internal.App.withSubscriptions || cs.contains `Qed.Internal.App.withStylesheets ||
    cs.contains `Qed.Internal.App.withExtraStyles || cs.contains `Qed.App.withHead ||
    cs.contains `Qed.App.withSsrStatus
  if hasApp then
    r := r ++ (#[`Qed.Internal.mkApp_init, `Qed.Internal.mkApp_update,
                 `Qed.Internal.mkRoutedApp_init, `Qed.Internal.mkRoutedApp_update,
                 `Qed.Internal.App.withDehydrate_init, `Qed.Internal.App.withDehydrate_update,
                 `Qed.Internal.App.withQueries_init, `Qed.Internal.App.withQueries_update,
                 `Qed.Internal.App.withSubscriptions_init, `Qed.Internal.App.withSubscriptions_update,
                 `Qed.Internal.App.withStylesheets_init, `Qed.Internal.App.withStylesheets_update,
                 `Qed.Internal.App.withExtraStyles_init, `Qed.Internal.App.withExtraStyles_update,
                 `Qed.App.withHead_init, `Qed.App.withHead_update,
                 `Qed.App.withSsrStatus_init, `Qed.App.withSsrStatus_update,
                 `Qed.Query.boot, `Qed.Query.wrap, `Qed.Resource.query, `Qed.Resource.rpcQuery,
                 `Qed.Subscription.boot, `Qed.Subscription.wrap, `Qed.Subscription.boot_state_eq].filter env.contains)
  if cs.contains `Qed.Cached.activate || cs.contains `Qed.Cached.all then
    r := r ++ (#[`Qed.Cached.activate, `Qed.Cached.all_empty].filter env.contains)
  return r

private def relevantOptResLemmas (env : Environment) (cs : Std.HashSet Name) : Array Name := Id.run do
  let mut r : Array Name := #[]
  if cs.contains `Qed.Cached.all || cs.contains `Qed.Resource.all then
    r := r ++ (#[`Qed.Cached.all, `Qed.Resource.all].filter env.contains)
  if cs.contains ``Qed.Lang.QedVal.val then
    r := r ++ (#[`Qed.QedVal.val_field, `Qed.QedVal.val_ensured].filter env.contains)
  if cs.contains `Qed.Codec.valid || cs.contains `Qed.Field then
    r := r ++ (#[`Qed.Codec.valid, `Qed.Codec.refine, `Qed.Codec.jsonOnly,
                 `Qed.Codec.text, `Qed.Codec.textarea, `Qed.Codec.nat,
                 `Qed.Codec.int, `Qed.Codec.checkbox, `Qed.Codec.date].filter env.contains)
  return r

private def stripStepPrefix : Name → Name
  | .str `step s => Name.mkSimple s
  | .str p s     =>
      let p' := stripStepPrefix p
      if p' == .anonymous then Name.mkSimple s else .str p' s
  | n => n

private def toSimpLemmas (ts : Array Term) : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :=
  ts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)

private def namesToSimpLemmas (ns : Array Name) : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :=
  ns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)

private def runUnfoldPresent (extra : Array Term) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  let env0 ← getEnv
  let cs ← collectMainConsts true
  let fixedNames := relevantAppLemmas env0 cs ++ relevantBoundaryLemmas cs
  let fixedL := (← namesToSimpLemmas fixedNames) ++ (← toSimpLemmas extra)
  qedUnfoldHelperLoop 12
    (fun env n => return qedIsHelper env n && (← getProjectionFnInfo? n).isNone)
    fixedL (includeLCtx := true) (useSimpAll := true)

private def isTrivialNonFieldTy (ty : Expr) : Bool :=
  ty.isSort || ty.isForall ||
  ty.isConstOf ``Nat || ty.isConstOf ``Int || ty.isConstOf ``Bool || ty.isConstOf ``String ||
  ty.isConstOf ``Unit ||
  ty.isAppOfArity ``Eq 3 || ty.isAppOfArity ``LE.le 4 || ty.isAppOfArity ``LT.lt 4 ||
  ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Or 2 ||
  ty.isAppOfArity ``Array 1 || ty.isAppOfArity ``List 1

private def runAddFieldFacts : TacticM Unit := do
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
          let rawTy? ← try some <$> Meta.inferType sub catch _ => pure none
          if let some rawTy := rawTy? then
            if isTrivialNonFieldTy rawTy then return
            let ty ←
              if rawTy.isAppOfArity `Qed.Field 2 || rawTy.isAppOfArity `Qed.Ensured 2 then pure rawTy
              else try Meta.whnf rawTy catch _ => pure rawTy
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

private def runFastClose : TacticM Unit := withMainContext do
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

private def runDestructExistsHyps : TacticM Unit := do
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

private def mkPredUnfold (pred : Term) : TacticM (Term × TSyntax `tactic) := do
  let pred := match pred with | `(($p)) => p | p => p
  let unfoldPred ← if pred.raw.isIdent
    then `(tactic| try simp only [$(⟨pred.raw⟩):ident] at *)
    else `(tactic| skip)
  return (pred, unfoldPred)

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
  if (← getGoals).isEmpty then return
  let env0 ← getEnv
  let cs ← collectMainConsts true
  let relNames := relevantOptResLemmas env0 cs ++ relevantBoundaryLemmas cs
  let relL := (← namesToSimpLemmas relNames) ++ (← toSimpLemmas extra)
  if !relL.isEmpty then
    try evalTactic (← `(tactic| simp_all only [$[$relL],*])) catch _ => pure ()
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic|
    first
      | qedFastClose
      | omega
      | decide
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
    let cs0 ← collectMainConsts true
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
      else (upd.raw.reprint.getD (toString upd.raw)).trimAscii.toString
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

end Qed
