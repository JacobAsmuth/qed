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
  (``Qed.Lang.QedMem.mem, #[``Qed.Lang.QedMem.mem_array, ``Qed.Lang.QedMem.mem_list, ``Qed.Lang.QedMem.mem_string, ``Array.contains_iff_mem, ``List.contains_iff_mem]),
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

private def impHypSimpNames : Array Name :=
  boolSimpNames ++ boolConstSimpNames ++ valUnwrapBaseNames ++
    #[``reduceCtorEq, ``Option.some.injEq, ``Prod.mk.injEq, ``Qed.Lang.QedMem.mem_array,
      ``Qed.Lang.QedMem.mem_list, ``Qed.Lang.QedMem.mem_string, ``Qed.Lang.QedMemProp.memProp_array,
      ``Qed.Lang.QedMemProp.memProp_list, ``Qed.Lang.QedMemProp.memProp_string,
      ``Array.contains_iff_mem, ``List.contains_iff_mem]

private def isPropSafe (ty : Expr) : MetaM Bool :=
  try Meta.isProp ty catch _ => pure false

/-- Forward-chain non-dependent implication hypotheses `h : P → Q` whose premise `P` already follows
    from the local context, then split any resulting conjunctions. -/
private def specializeImpHyps (g0 : MVarId) : MetaM MVarId := do
  let mut g := g0
  let mut seen : Std.HashSet Expr := {}
  for _ in [0:4] do
    let hyps ← g.withContext do
      let mut out : Array (FVarId × Expr × Expr) := #[]
      for d in (← getLCtx) do
        if !d.isImplementationDetail && !d.isLet then
          let ty ← instantiateMVars d.type
          if let .forallE _ p q _ := ty then
            if !q.hasLooseBVars && !seen.contains q then
              if ← isPropSafe p then
                if ← isPropSafe q then
                  out := out.push (d.fvarId, p, q)
      pure out
    let mut added := false
    for (hfv, p, q) in hyps do
      if seen.contains q then continue
      let pf? : Option Expr ← g.withContext do
        tryRestoreM none Option.isSome do
          let mP ← Meta.mkFreshExprSyntheticOpaqueMVar p
          let mId := mP.mvarId!
          let closed ←
            if ← tryCloseTrivial mId then pure true
            else if ← tryDirectOmega mId then pure true
            else if ← tryDirectDecide mId then pure true
            else do
              let (ctx, _) ← mkCachedSimpCtx "impHypPremise" impHypSimpNames
              match ← trySimpAll mId ctx with
              | none => pure true
              | some mId' =>
                  if ← tryCloseTrivial mId' then pure true
                  else if ← tryDirectOmega mId' then pure true
                  else tryDirectDecide mId'
          if closed then return some (← instantiateMVars mP) else return none
      if let some pfP := pf? then
        seen := seen.insert q
        let (_, g1) ← (← g.assert `_qedMp q (mkApp (mkFVar hfv) pfP)).intro1P
        g := (← splitAndHypsGoal g1 true 16).1
        added := true
    unless added do break
  return g

elab "qedUnfoldPresent" "[" extra:term,* "]" : tactic => runUnfoldPresent extra.getElems
elab "qedFastClose" : tactic => runFastClose

macro "qedAutoClose" : tactic => `(tactic|
  (first
    | qedFastClose | contradiction | omega | decide | assumption | rfl | (qedNonlinearClose; done)
    | (try (repeat' (apply And.intro)); all_goals (first | qedFastClose | contradiction | omega | decide | (qedNonlinearClose; done) | grind); done)))

private def tryCloseContradiction (g : MVarId) : MetaM Bool :=
  tryRestoreM false id (g.contradictionCore {})

private def runCloseStateGoal (extra : Array Term) : TacticM Unit := do
  let g0 :: rest ← getGoals | return
  if ← tryCloseContradiction g0 then setGoals rest; return
  let g0 ← specializeImpHyps g0
  setGoals (g0 :: rest)
  if ← tryCloseContradiction g0 then setGoals rest; return
  if ← tryCloseBasic g0 (reducibleOnly := true) then setGoals rest; return
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
  let _ :: rest2 ← getGoals | return
  if ← tryCloseContradiction g then setGoals rest2; return
  let g ← specializeImpHyps g
  setGoals (g :: rest2)
  if ← tryCloseContradiction g then setGoals rest2; return
  if ← tryCloseBasic g (reducibleOnly := true) then setGoals rest2; return
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

private def closeSplitBranch (usingL : Array Term) (reducibleOnly : Bool)
    (extraSimpL? : Option (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := none)
    (hypSplitFuel : Nat := 0) (g : MVarId) : TacticM Unit := do
  if ← tryCloseContradiction g then setGoals []; return
  if ← tryCloseTrivial g (reducibleOnly := reducibleOnly) then setGoals []; return
  if ← tryDirectOmega g then setGoals []; return
  evalTactic (← `(tactic| (intros; try repeat' split; try dsimp only at *)))
  forEachGoal fun gSub => do
    if ← tryCloseContradiction gSub then setGoals []; return
    runAddFieldFacts
    if let g1 :: r1 ← getGoals then setGoals ((← splitAndHypsGoal g1 true 16).1 :: r1)
    runUnfoldPresent usingL
    if let some simpL := extraSimpL? then
      discard <| tryTac `(tactic| simp_all only [$[$simpL],*])
      if (← getGoals).isEmpty then return
    runCloseStateGoal usingL
    if hypSplitFuel > 0 then
      if !(← getGoals).isEmpty then
        let gRem :: _ ← getGoals | return
        let splitFVar? ← gRem.withContext do
          for d in (← getLCtx) do
            if !d.isImplementationDetail && !d.isLet then
              let ty ← instantiateMVars d.type
              if ← isPropSafe ty then
                if (← trySplitLocalDecl gRem d.fvarId).isSome then return some d.fvarId
          return none
        if let some fv := splitFVar? then
          if let some subgoals ← trySplitLocalDecl gRem fv then
            setGoals subgoals
            forEachGoal (closeSplitBranch usingL reducibleOnly extraSimpL? (hypSplitFuel - 1))
termination_by hypSplitFuel

syntax qedProveCase := ident,+ " => " Lean.Parser.Tactic.tacticSeq
syntax "qedDischargeInit " "[" term,* "]" term:max ident term:max : tactic
syntax "qedDischargePreserved " "[" term,* "]" term:max ident term:max (" from " term)? (" _qedProve " "[" qedProveCase,* "]")? : tactic

elab_rules : tactic
  | `(tactic| qedDischargeInit [$[$usingL],*] $initT $nm $pred) => do
    (← getMainGoal).setTag `init; runInitPass usingL pred initT
    throwUnsolvedInvGoals nm m!"Invariant `{nm.getId}` failed on initial state `{formatTargetName initT}`:"
      m!"Hint: Update the initial `state` values so `{nm.getId}` holds, add `using [lemma]`, or supply a `:= by` proof."

  | `(tactic| qedDischargePreserved [$[$usingL],*] $upd $nm $pred $[from $init]? $[_qedProve [$[$proveCases],*]]?) => do
    let unfoldPred ← unfoldIdentTac pred
    let appL ← namesToSimpLemmas (relevantAppLemmas (← getEnv) (← collectGoalConsts (← getMainGoal) true))
    let updL ← match upd with
      | `($a:ident) | `(($a:ident).update) | `((($a:ident).update)) | `(($a:ident $_:term*)) => pure (#[← `(Lean.Parser.Tactic.simpLemma| $a:term)] ++ appL)
      | _ => pure appL
    let mut caseMap : Std.HashMap Name (Ident × TSyntax ``Lean.Parser.Tactic.tacticSeq) := {}
    let mut orderedCaseIds : Array Ident := #[]
    if let some pcs := proveCases then
      for pc in pcs do
        match pc with
        | `(qedProveCase| $[$cIds:ident],* => $tacSeq) =>
            for cid in cIds do
              let cn := cid.getId.eraseMacroScopes
              if caseMap.contains cn then throwErrorAt cid s!"duplicate `case {cn}` in `prove:` on invariant `{nm.getId}`"
              caseMap := caseMap.insert cn (cid, tacSeq)
              orderedCaseIds := orderedCaseIds.push cid
        | _ => pure ()
    let seenCasesRef ← IO.mkRef ({} : Std.HashSet Name)
    let allCtorsRef ← IO.mkRef (#[] : Array Name)
    let runStep : TacticM Unit := do
      evalTactic (← `(tactic| (intro m msg h; $unfoldPred:tactic; try dsimp only at *; cases msg)))
      forEachGoal fun g => do
        let ctorTag := stripStepPrefix (← g.getTag)
        allCtorsRef.modify (Qed.Lang.pushUnique · ctorTag)
        if let some (_, tacSeq) := caseMap[ctorTag]? then
          seenCasesRef.modify (·.insert ctorTag)
          discard <| tryTac `(tactic| simp only [$[$updL],*])
          discard <| tryTac `(tactic| dsimp only at *)
          evalTactic tacSeq
          return
        discard <| tryTac `(tactic| simp_all only [$[$updL],*])
        runUnfoldPresent usingL; try runCloseCachedPut usingL catch _ => pure ()
        discard <| tryTac `(tactic| repeat' split)
        forEachGoal (closeSplitBranch usingL true none 3)
    match init with
    | some initT =>
        let [gInit, gStep] ← (← getMainGoal).apply (mkConst ``And.intro) | throwError "internal error splitting invariant init/step goals"
        gInit.setTag `init; gStep.setTag `step
        setGoals [gInit]; runInitPass usingL pred initT; let remInit ← getUnsolvedGoals
        setGoals [gStep]; runStep; setGoals (remInit ++ (← getUnsolvedGoals))
    | none => runStep
    let seenCases ← seenCasesRef.get
    let allCtors ← allCtorsRef.get
    for cid in orderedCaseIds do
      let cn := cid.getId.eraseMacroScopes
      unless seenCases.contains cn do
        let validList := String.intercalate ", " (allCtors.toList.map toString)
        throwErrorAt cid s!"unknown action/message `{cn}` in `prove:` on invariant `{nm.getId}` (valid cases: {validList})"
    throwUnsolvedInvGoals nm m!"Invariant `{nm.getId}` failed in `{formatTargetName upd}`:"
      m!"Hint: Guard the failing branch with `if ...:`, fix the update, or weaken the invariant.\n      If the rule does hold, add `using [lemma]`, a per-action `prove:` block, or a manual `:= by` proof."

/-! ## Pure `fn` Command with Contracts (`requires`, `ensures`, `if`, `blindTo`) -/

declare_syntax_cat qedFnContract

section FnParsers
open Lean Parser Qed.Lang

private abbrev fExpr : Parser := categoryParser `qedExpr 0
private abbrev fType : Parser := categoryParser `qedType 0
private abbrev fContract : Parser := categoryParser `qedFnContract 0

def fnParam : Parser := node `Qed.fnParam (ident >> ":" >> fType)
def fnBlindTarget : Parser := node `Qed.fnBlindTarget (ident >> optional (checkNoWsBefore "" >> ".{" >> sepBy1 ident "," >> "}"))
def fnOptProof : Parser := optional (":=" >> kw "by" >> Parser.Tactic.tacticSeq)

@[qedFnContract_parser] def fnRequiresClause : Parser := leading_parser
  withPosition (atomic (identEq `requires) >> sepBy1 fExpr ",")
@[qedFnContract_parser] def fnEnsuresClause : Parser := leading_parser
  withPosition (atomic (identEq `ensures) >> sepBy1 fExpr "," >> fnOptProof)
@[qedFnContract_parser] def fnBlindToClause : Parser := leading_parser
  withPosition (atomic (identEq `blindTo) >> sepBy1 fnBlindTarget "," >> fnOptProof)
@[qedFnContract_parser] def fnContractIf : Parser := leading_parser
  withPosition (atomic (symbol "if" >> notFollowedBy (symbol "let") "let" >> sepBy1 fExpr "," >> ":" >>
    checkColGt "expected indented contract clauses" >> many1Indent fContract))

@[command_parser] def fnCmd : Parser := leading_parser
  optional Command.docComment >>
  withPosition (atomic (identEq `fn >> ident >> "(") >> sepBy fnParam "," >> ")" >> " -> " >> fType >> ":" >>
    checkColGt "expected indented `fn` body" >>
    withPosition (many (atomic (checkColEq "contract" >> fContract)) >>
                  many1 (checkColEq "statement" >> categoryParser `qedStmt 0)))

end FnParsers

/-! ## Pure `fn` Contract Proof Tactics (`qedProveFnEnsures`, `qedProveBlindTo`) -/

private def fnContractSimpNames : Array Name :=
  impHypSimpNames ++ #[``Array.size_push, ``Array.size_set, ``Array.size_map, ``Array.size_append,
    ``Array.size_reverse, ``List.length_cons, ``List.length_append, ``List.length_map,
    ``true_and, ``and_true, ``false_or, ``or_false, ``true_or, ``or_true, ``id_eq, ``ne_eq]

private def runProveFnGoal (fnId : Ident) (isBlind : Bool) : TacticM Unit := do
  if isBlind then evalTactic (← `(tactic| intros))
  else discard <| tryTac `(tactic| dsimp only)
  discard <| tryTac `(tactic| simp only [$fnId:ident])
  discard <| tryTac `(tactic| dsimp only at *)
  if (← getGoals).isEmpty then return
  if let g0 :: rest ← getGoals then
    if ← tryCloseTrivial g0 then setGoals rest; return
  let simpL ← namesToSimpLemmas fnContractSimpNames
  runUnfoldPresent #[]
  discard <| tryTac `(tactic| dsimp only at *)
  discard <| tryTac `(tactic| simp_all only [$[$simpL],*])
  if (← getGoals).isEmpty then return
  discard <| tryTac `(tactic| repeat' split)
  forEachGoal (closeSplitBranch #[] false (some simpL) 3)

syntax "qedProveFnEnsures " ident ident : tactic
syntax "qedProveBlindTo " ident ident str : tactic

elab_rules : tactic
  | `(tactic| qedProveFnEnsures $fnId $thmId) => do
      runProveFnGoal fnId false
      throwUnsolvedInvGoals thmId m!"`ensures` contract failed for `{fnId.getId}`:"
        m!"Hint: Strengthen `requires` / `if` guards, fix the return value, or supply a `:= by` proof."

  | `(tactic| qedProveBlindTo $fnId $thmId $desc) => do
      runProveFnGoal fnId true
      throwUnsolvedInvGoals thmId m!"`blindTo {desc.getString}` failed in `{fnId.getId}` (output may depend on blinded field/parameter):"
        m!"Hint: Redact every branch that reads {desc.getString} under this guard, strengthen the `if` condition, or supply a `:= by` proof."

/-! ## Shared Pure Statement Lowering & `fn` Contract Elaboration -/

section FnElab
open Lean Elab Command Qed.Lang

@[noinline]
partial def lowerPureFnStmts (fnDesc : String) (stmts : List Syntax)
    (lowerVal : Syntax → CommandElabM Term := fun s => liftMacroM (lowerSimpleQedExpr .val s))
    (lowerGuard : Syntax → CommandElabM Term := fun s => liftMacroM (lowerSimpleQedExpr .propGuard s)) : CommandElabM Term := do
  match stmts with
  | [] => throwError s!"missing `return` on fallthrough path of `{fnDesc}`"
  | s :: rest =>
      let sk := s.getKind
      if sk == ``qedStmtPass then lowerPureFnStmts fnDesc rest lowerVal lowerGuard
      else if sk == ``qedStmtReturn then
        if (s.getArg 1).getNumArgs == 1 then lowerVal ((s.getArg 1).getArg 0)
        else throwErrorAt s s!"`return` inside `{fnDesc}` must return a value"
      else if sk == ``qedStmtExpr then
        if rest.isEmpty then lowerVal (s.getArg 0)
        else throwErrorAt s s!"unexpected bare expression statement in pure `{fnDesc}`; bind it with `let _ = ...` or return it"
      else if sk == ``qedStmtLet then
        if (s.getArg 5).getNumArgs > 0 then throwErrorAt ((s.getArg 5).getArg 0) s!"`predict`/`catch` clauses are not supported in pure `{fnDesc}`"
        let rhsT ← lowerVal (s.getArg 4)
        let cont ← lowerPureFnStmts fnDesc rest lowerVal lowerGuard
        if (s.getArg 1).isIdent then
          let lId : Ident := ⟨s.getArg 1⟩
          if (s.getArg 2).getNumArgs == 2 then
            let lTy ← liftMacroM (return (← lowerQedType ((s.getArg 2).getArg 1) false).1)
            `(let $lId:ident : $lTy := $rhsT; $cont)
          else `(let $lId:ident := $rhsT; $cont)
        else `(let _ := $rhsT; $cont)
      else if sk == ``qedStmtIf then
        let cond ← lowerGuard (s.getArg 1)
        let thenT ← lowerPureFnStmts fnDesc ((suiteStmts (s.getArg 3)).toList ++ rest) lowerVal lowerGuard
        let elseStmts := (desugarElifs (s.getArg 4).getArgs (s.getArg 5)).getD #[]
        let elseT ← lowerPureFnStmts fnDesc (elseStmts.toList ++ rest) lowerVal lowerGuard
        `(if $(mkIdent `_qedIf):ident : $cond then $thenT else $elseT)
      else if sk == ``qedStmtIfLet then
        let pat ← liftMacroM (lowerQedPat (s.getArg 2))
        let scrut ← lowerVal (s.getArg 4)
        let thenT ← lowerPureFnStmts fnDesc ((suiteStmts (s.getArg 6)).toList ++ rest) lowerVal lowerGuard
        let elseStmts := (extractElseSuite (s.getArg 7)).getD #[]
        let elseT ← lowerPureFnStmts fnDesc (elseStmts.toList ++ rest) lowerVal lowerGuard
        `(match $(mkIdent `_qedIfLet):ident : $scrut:term with | $pat:term => $thenT | _ => $elseT)
      else if sk == ``qedStmtMatch then
        let scruts ← (s.getArg 1).getSepArgs.mapM lowerVal
        let alts ← (s.getArg 3).getArgs.mapM fun alt => do
          let altTerms ← liftMacroM (lowerCasePatAlts (alt.getArg 1))
          let body ← lowerPureFnStmts fnDesc ((suiteStmts (alt.getArg 3)).toList ++ rest) lowerVal lowerGuard
          mkMatchAltFromAlts altTerms body
        `(match $[$scruts:term],* with $[$alts:matchAlt]*)
      else
        let sn := stxSnippet s
        throwErrorAt s s!"unsupported statement{if sn.isEmpty then "" else s!" `{sn}`"} in pure `{fnDesc}` (pure functions cannot mutate state; use `let` or return a value)"

private structure ParsedBlindTarget where
  paramId : Ident
  fields  : Array Ident

private structure ParsedFnEnsures where
  ref    : Syntax
  guards : Array Syntax
  preds  : Array Syntax
  tac?   : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)

private structure ParsedFnBlindTo where
  ref     : Syntax
  guards  : Array Syntax
  targets : Array ParsedBlindTarget
  tac?    : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)

private structure ParsedFnContracts where
  requires : Array Syntax := #[]
  ensures  : Array ParsedFnEnsures := #[]
  blinds   : Array ParsedFnBlindTo := #[]

private def parseOptTacSeq (optNode : Syntax) : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
  if optNode.getNumArgs == 3 then some ⟨optNode.getArg 2⟩ else none

private def parseBlindTarget (stx : Syntax) : CommandElabM ParsedBlindTarget := do
  let rawId : Ident := ⟨stx.getArg 0⟩
  let optBraces := stx.getArg 1
  if optBraces.getNumArgs == 3 then
    let flds : Array Ident := (optBraces.getArg 1).getSepArgs.map (⟨·⟩)
    return { paramId := rawId, fields := flds }
  match rawId.getId.eraseMacroScopes with
  | .str .anonymous _ => return { paramId := rawId, fields := #[] }
  | .str (.str .anonymous p) f =>
      return { paramId := mkIdentFrom rawId (Name.mkSimple p), fields := #[mkIdentFrom rawId (Name.mkSimple f)] }
  | _ => throwErrorAt rawId s!"`blindTo` expects `<param>`, `<param>.<field>`, or `<param>.\{f1, f2}`, got `{rawId.getId}`"

private partial def collectFnContracts (guards : Array Syntax) (clauses : Array Syntax) (acc : ParsedFnContracts) : CommandElabM ParsedFnContracts := do
  let mut acc := acc
  for cl in clauses do
    let k := cl.getKind
    if k == ``fnRequiresClause then
      unless guards.isEmpty do throwErrorAt cl "`requires` must appear at the top level of `fn` (combine guard conditions inside `if ...:`)"
      acc := { acc with requires := acc.requires ++ (cl.getArg 1).getSepArgs }
    else if k == ``fnEnsuresClause then
      acc := { acc with ensures := acc.ensures.push { ref := cl, guards, preds := (cl.getArg 1).getSepArgs, tac? := parseOptTacSeq (cl.getArg 2) } }
    else if k == ``fnBlindToClause then
      let tgts ← (cl.getArg 1).getSepArgs.mapM parseBlindTarget
      acc := { acc with blinds := acc.blinds.push { ref := cl, guards, targets := tgts, tac? := parseOptTacSeq (cl.getArg 2) } }
    else if k == ``fnContractIf then
      let conds := (cl.getArg 1).getSepArgs
      acc ← collectFnContracts (guards ++ conds) (cl.getArg 3).getArgs acc
    else throwErrorAt cl "unexpected contract clause in `fn`"
  return acc

private def fmtBlindTarget (t : ParsedBlindTarget) : String :=
  if t.fields.isEmpty then t.paramId.getId.toString
  else if t.fields.size == 1 then s!"{t.paramId.getId}.{t.fields[0]!.getId}"
  else s!"{t.paramId.getId}.\{" ++ String.intercalate ", " (t.fields.toList.map (·.getId.toString)) ++ "}"

@[noinline]
def elabPureFnContracts (thmBaseId fnConstId : Ident) (paramIds : Array Ident) (paramTys : Array Term) (retTy : Term)
    (contracts : Array Syntax) (extraPreHyps : Array (Ident × Term) := #[]) : CommandElabM Unit := do
  if contracts.isEmpty then return
  let parsed ← collectFnContracts #[] contracts {}
  let lowerProp (s : Syntax) : CommandElabM Term := liftMacroM (lowerSimpleQedExpr .propInv s)
  let reqProp? : Option Term ← if parsed.requires.isEmpty then pure none else some <$> mkConjBody (← parsed.requires.mapM lowerProp)
  let mkPreBinders (guards : Array Syntax) : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
    let mut bs : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
    for (pId, pTy) in paramIds.zip paramTys do bs := bs.push (← `(bracketedBinder| ($pId:ident : $pTy)))
    for (hId, hTy) in extraPreHyps do bs := bs.push (← `(bracketedBinder| ($hId:ident : $hTy)))
    if let some rp := reqProp? then bs := bs.push (← `(bracketedBinder| ($(mkIdent `_hReq):ident : $rp)))
    for (g, i) in guards.zipIdx do
      let gp ← lowerProp g
      bs := bs.push (← `(bracketedBinder| ($(mkIdent (Name.mkSimple s!"_hIf_{i}")):ident : $gp)))
    return bs
  let rhsCall ← mkAppTerms fnConstId (paramIds.map (⟨·.raw⟩))
  let paramNames := paramIds.map (·.getId.eraseMacroScopes)
  for (ens, idx) in parsed.ensures.zipIdx do
    let thmName := if parsed.ensures.size == 1 then thmBaseId.getId.appendAfter "_ensures" else thmBaseId.getId.appendAfter s!"_ensures_{idx + 1}"
    let thmId := mkIdentFrom ens.ref thmName
    let binders ← mkPreBinders ens.guards
    let ensProp ← mkConjBody (← ens.preds.mapM lowerProp)
    let resId := mkIdent `result
    let proofTac : TSyntax ``Lean.Parser.Tactic.tacticSeq ← match ens.tac? with
      | some ts => pure ts
      | none    => `(Lean.Parser.Tactic.tacticSeq| qedProveFnEnsures $fnConstId $thmId)
    elabCommand (← `(command|
      set_option linter.unusedVariables false in
      theorem $thmId $[$binders:bracketedBinder]* : let $resId:ident : $retTy := $rhsCall; $ensProp := by $proofTac))
  for (bl, idx) in parsed.blinds.zipIdx do
    let thmName := if parsed.blinds.size == 1 then thmBaseId.getId.appendAfter "_blindTo" else thmBaseId.getId.appendAfter s!"_blindTo_{idx + 1}"
    let thmId := mkIdentFrom bl.ref thmName
    -- Merge targets that refer to the same parameter (e.g. `blindTo r.a, r.b`).
    let mut paramBlinds : Array (Name × Bool × Array Ident) := #[]
    for t in bl.targets do
      let pn := t.paramId.getId.eraseMacroScopes
      unless paramNames.contains pn do
        throwErrorAt t.paramId s!"unknown parameter `{pn}` in `blindTo`{Qed.Diag.didYouMean pn.toString (paramNames.toList.map toString)}"
      if let some pos := paramBlinds.findIdx? (·.1 == pn) then
        let (_, whole, flds) := paramBlinds[pos]!
        let whole' := whole || t.fields.isEmpty
        let flds' := if whole' then #[] else t.fields.foldl (fun acc f => if acc.any (·.getId.eraseMacroScopes == f.getId.eraseMacroScopes) then acc else acc.push f) flds
        paramBlinds := paramBlinds.set! pos (pn, whole', flds')
      else
        paramBlinds := paramBlinds.push (pn, t.fields.isEmpty, t.fields)
    let mut freshVars : Array (Ident × Option Term) := #[]
    let mut lhsArgs : Array Term := #[]
    for (pId, pTy) in paramIds.zip paramTys do
      let pn := pId.getId.eraseMacroScopes
      match paramBlinds.find? (·.1 == pn) with
      | none => lhsArgs := lhsArgs.push ⟨pId.raw⟩
      | some (_, true, _) =>
          let fv := mkIdent (Name.mkSimple s!"_qed_blind_{pn}")
          freshVars := freshVars.push (fv, some pTy)
          lhsArgs := lhsArgs.push ⟨fv.raw⟩
      | some (_, false, flds) =>
          let mut updFIds : Array Ident := #[]
          let mut updVals : Array Term := #[]
          for f in flds do
            let fv := mkIdent (Name.mkSimple s!"_qed_blind_{pn}_{f.getId.eraseMacroScopes}")
            freshVars := freshVars.push (fv, none)
            updFIds := updFIds.push f
            updVals := updVals.push ⟨fv.raw⟩
          lhsArgs := lhsArgs.push (← `({ $pId with $[$updFIds:ident := $updVals:term],* }))
    let lhsCall ← mkAppTerms fnConstId lhsArgs
    let eqProp ← freshVars.foldrM (init := ← `($lhsCall = $rhsCall)) fun (fv, ty?) acc => match ty? with
      | some ty => `(∀ ($fv:ident : $ty), $acc)
      | none    => `(∀ $fv:ident, $acc)
    let binders ← mkPreBinders bl.guards
    let descLit := Syntax.mkStrLit (String.intercalate ", " (bl.targets.toList.map fmtBlindTarget))
    let proofTac : TSyntax ``Lean.Parser.Tactic.tacticSeq ← match bl.tac? with
      | some ts => pure ts
      | none    => `(Lean.Parser.Tactic.tacticSeq| qedProveBlindTo $fnConstId $thmId $descLit)
    elabCommand (← `(command|
      set_option linter.unusedVariables false in
      theorem $thmId $[$binders:bracketedBinder]* : $eqProp := by $proofTac))

@[noinline, command_elab fnCmd] def elabFnCmd : CommandElab := fun stx => do
  let doc? := if (stx.getArg 0).getNumArgs == 1 then some (⟨(stx.getArg 0).getArg 0⟩ : TSyntax ``Lean.Parser.Command.docComment) else none
  let fnId : Ident := ⟨stx.getArg 2⟩
  let rawParams := (stx.getArg 4).getSepArgs
  let mut paramIds : Array Ident := #[]; let mut paramTys : Array Term := #[]
  for rp in rawParams do
    let pid : Ident := ⟨rp.getArg 0⟩
    if paramIds.any (·.getId.eraseMacroScopes == pid.getId.eraseMacroScopes) then
      throwErrorAt pid s!"duplicate parameter `{pid.getId}` in `fn {fnId.getId}`"
    let pty ← liftMacroM (return (← lowerQedType (rp.getArg 2) false).1)
    paramIds := paramIds.push pid; paramTys := paramTys.push pty
  let retTy ← liftMacroM (return (← lowerQedType (stx.getArg 7) false).1)
  let contracts := (stx.getArg 9).getArgs
  let bodyStmts := (stx.getArg 10).getArgs
  let bodyTerm ← lowerPureFnStmts s!"fn {fnId.getId}" bodyStmts.toList
  elabCommand (← `(command|
    $[$doc?:docComment]? def $fnId $[($paramIds:ident : $paramTys:term)]* : $retTy := $bodyTerm))
  elabPureFnContracts fnId fnId paramIds paramTys retTy contracts

end FnElab

end Qed
