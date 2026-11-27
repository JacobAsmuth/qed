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
    (#[`Qed.Cached.activate, `Qed.Cached.all, `Qed.Cached.markRefetch, `Qed.Cached.invalidateAll],
     #[`Qed.Cached.activate, `Qed.Cached.all_empty, `Qed.Cached.all_markRefetch, `Qed.Cached.all_invalidateAll])]

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

def runUnfoldPresent (extra : Array Term) (skip : Array Name := #[]) : TacticM Unit := do
  let g :: _ ← getGoals | return
  let cs ← collectGoalConsts g true
  let fixedL := (← namesToSimpLemmas (relevantAppLemmas (← getEnv) cs ++ relevantBoundaryLemmas cs)) ++ (← termsToSimpLemmas extra)
  qedUnfoldHelperLoop 12 (fun env n => if skip.contains n || !qedIsHelper env n then return false else return (← getProjectionFnInfo? n).isNone)
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
      else if tgt.isAppOfArity `Qed.Cached.all 3 && (tgt.getAppArgs[2]!.consumeMData.isAppOfArity `Qed.Cached.put 5 || tgt.getAppArgs[2]!.consumeMData.isAppOfArity `Qed.Cached.putRev 5) then
        let isRev := tgt.getAppArgs[2]!.consumeMData.isAppOfArity `Qed.Cached.putRev 5
        let allPutId := mkIdent (if isRev then `Qed.Cached.all_putRev else `Qed.Cached.all_put); let stripImpId := mkIdent `Qed.Resource.all_stripEnsured_of_imp
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
    (hypSplitFuel : Nat := 0) (skipUnfold : Array Name := #[]) (g : MVarId) : TacticM Unit := do
  if ← tryCloseContradiction g then setGoals []; return
  if ← tryCloseTrivial g (reducibleOnly := reducibleOnly) then setGoals []; return
  if ← tryDirectOmega g then setGoals []; return
  evalTactic (← `(tactic| (intros; try repeat' (split <;> try dsimp only); try dsimp only at *)))
  forEachGoal fun gSub => do
    if ← tryCloseContradiction gSub then setGoals []; return
    runAddFieldFacts
    if let g1 :: r1 ← getGoals then setGoals ((← splitAndHypsGoal g1 true 16).1 :: r1)
    runUnfoldPresent usingL skipUnfold
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
            forEachGoal (closeSplitBranch usingL reducibleOnly extraSimpL? (hypSplitFuel - 1) skipUnfold)
termination_by hypSplitFuel

syntax qedProveCase := ident,+ " => " Lean.Parser.Tactic.tacticSeq
syntax "qedDischargeInit " "[" term,* "]" term:max ident term:max : tactic
syntax "qedDischargePreserved " "[" term,* "]" term:max ident term:max (" from " term)? (" _qedProve " "[" qedProveCase,* "]")? : tactic

elab_rules : tactic
  | `(tactic| qedDischargeInit [$[$usingL],*] $initT $nm $pred) => Core.withCurrHeartbeats do
    (← getMainGoal).setTag `init; runInitPass usingL pred initT
    throwUnsolvedInvGoals nm m!"Invariant `{nm.getId}` failed on initial state `{formatTargetName initT}`:"
      m!"Hint: Update the initial `state` values so `{nm.getId}` holds, add `using [lemma]`, or supply a `:= by` proof."

  | `(tactic| qedDischargePreserved [$[$usingL],*] $upd $nm $pred $[from $init]? $[_qedProve [$[$proveCases],*]]?) => Core.withCurrHeartbeats do
    let unfoldPred ← unfoldIdentTac pred
    let appNames := relevantAppLemmas (← getEnv) (← collectGoalConsts (← getMainGoal) true)
    let updUnfolds ← match upd with
      | `($a:ident) | `(($a:ident).update) | `((($a:ident).update)) | `(($a:ident $_:term*)) => resolveCompUpdateUnfolds a.raw
      | _ => pure #[]
    let updNames := updUnfolds ++ appNames
    let updCtx ← mkDynamicSimpCtx updNames none (withEqns := false)
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
      forEachGoal fun g => Core.withCurrHeartbeats do
        let ctorTag := stripStepPrefix (← g.getTag)
        allCtorsRef.modify (Qed.Lang.pushUnique · ctorTag)
        if let some (_, tacSeq) := caseMap[ctorTag]? then
          seenCasesRef.modify (·.insert ctorTag)
          match ← simpGoalOnly g updCtx with
          | none => setGoals []; return
          | some g1 =>
              setGoals [g1]
              discard <| tryTac `(tactic| dsimp only at *)
              evalTactic tacSeq
              return
        match ← trySimpAll g updCtx with
        | none => setGoals []; return
        | some g1 =>
            setGoals [g1]
            if ← tryCloseBasic g1 (reducibleOnly := true) then setGoals []; return
        runUnfoldPresent usingL updNames; try runCloseCachedPut usingL catch _ => pure ()
        discard <| tryTac `(tactic| repeat' (split <;> try dsimp only))
        forEachGoal (closeSplitBranch usingL true none 3 updNames)
    match init with
    | some initT =>
        let [gInit, gStep] ← (← getMainGoal).apply (mkConst ``And.intro) | throwError "internal error splitting invariant init/step goals"
        gInit.setTag `init; gStep.setTag `step
        setGoals [gInit]; Core.withCurrHeartbeats (runInitPass usingL pred initT); let remInit ← getUnsolvedGoals
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

def fnParam : Parser := node `Qed.fnParam (ident >> ":" >> fType >> optional ("=" >> fExpr))
def fnExParam : Parser := node `Qed.fnExParam (ident >> ":" >> fType)
def fnBlindTarget : Parser := node `Qed.fnBlindTarget (ident >> optional (checkNoWsBefore "" >> ".{" >> sepBy1 ident "," >> "}"))
def fnProofBy : Parser := node `Qed.fnProofBy (":=" >> kw "by" >> Parser.Tactic.tacticSeq)
def fnProofProve : Parser := node `Qed.fnProofProve (atomic (checkColGt "expected indented `prove:` block" >> identEq `prove >> ":") >> checkColGt "expected indented proof tactics" >> Parser.Tactic.tacticSeq)
def fnOptProof : Parser := optional (fnProofBy <|> fnProofProve)

@[qedFnContract_parser] def fnRequiresClause : Parser := leading_parser
  withPosition (atomic (identEq `requires) >> sepBy1 fExpr ",")
@[qedFnContract_parser] def fnEnsuresClause : Parser := leading_parser
  withPosition (atomic (identEq `ensures) >> sepBy1 fExpr "," >> fnOptProof)
@[qedFnContract_parser] def fnBlindToClause : Parser := leading_parser
  withPosition (atomic (identEq `blindTo) >> sepBy1 fnBlindTarget "," >> fnOptProof)
@[qedFnContract_parser] def fnExampleClause : Parser := leading_parser
  withPosition (atomic (symbol "example" >> ident) >>
    optional (checkNoWsBefore "" >> "(" >> sepBy1 fnExParam "," >> ")") >>
    optional (symbol "where" >> sepBy1 fExpr ",") >> ":" >> sepBy1 fExpr "," >> fnOptProof)
@[qedFnContract_parser] def fnContractIf : Parser := leading_parser
  withPosition (atomic (symbol "if" >> notFollowedBy (symbol "let") "let" >> sepBy1 fExpr "," >> ":" >>
    checkColGt "expected indented contract clauses" >> many1Indent fContract))

@[command_parser] def fnCmd : Parser := leading_parser
  optional Command.docComment >>
  withPosition (atomic (optional (symbol "private") >> identEq `fn >> ident >> "(") >> sepBy fnParam "," >> ")" >> " -> " >> fType >> ":" >>
    checkColGt "expected indented `fn` body" >>
    withPosition (many (atomic (checkColEq "contract" >> fContract)) >>
                  many1 (checkColEq "statement" >> categoryParser `qedStmt 0)))

end FnParsers

/-! ## Pure `fn` Contract Proof Tactics (`qedProveFnEnsures`, `qedProveBlindTo`, `qedProveFnExample`) -/

private def fnContractSimpNames : Array Name :=
  impHypSimpNames ++ #[``Array.size_push, ``Array.size_set, ``Array.size_map, ``Array.size_append,
    ``Array.size_reverse, ``List.length_cons, ``List.length_append, ``List.length_map,
    ``Qed.qedCoalesce_option, ``Qed.qedIterable_toList_list, ``Qed.qedIterable_toList_array, ``Qed.qedIterable_toList_range,
    ``true_and, ``and_true, ``false_or, ``or_false, ``true_or, ``or_true, ``id_eq, ``ne_eq]

private def runProveFnGoal (fnId : Ident) (isBlind : Bool) : TacticM Unit := do
  if isBlind then evalTactic (← `(tactic| intros))
  else discard <| tryTac `(tactic| dsimp only)
  discard <| tryTac `(tactic| unfold $fnId:ident)
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
  if !(← getGoals).isEmpty then
    forEachGoal fun _ => discard <| tryTac `(tactic| first | rfl | decide | decide +kernel | omega)

private def finiteEnumCtorCount? (ty : Expr) : MetaM (Option Nat) := do
  let ty ← Meta.whnf ty
  let .const nm _ := ty | return none
  let some (.inductInfo ind) := (← getEnv).find? nm | return none
  if ind.numParams != 0 || ind.numIndices != 0 || ind.isRec then return none
  for ctorNm in ind.ctors do
    let some (.ctorInfo ci) := (← getEnv).find? ctorNm | return none
    if ci.numFields != 0 then return none
  return some ind.ctors.length

private partial def splitFiniteEnumsAndProve (fnId : Ident) (budget : Nat) (g : MVarId) : TacticM Unit := do
  setGoals [g]
  if ← tryCloseContradiction g then setGoals []; return
  if ← tryTac (requireClosed := true) `(tactic| first | rfl | decide | decide +kernel | omega) then return
  let nextEnum? : Option (FVarId × Nat) ← g.withContext do
    for d in (← getLCtx) do
      if !d.isImplementationDetail && !d.isLet then
        if let some k ← finiteEnumCtorCount? d.type then
          if k > 0 && k ≤ budget then return some (d.fvarId, k)
    return none
  match nextEnum? with
  | none =>
      runProveFnGoal fnId false
  | some (fv, k) =>
      let subgoals ← g.cases fv
      let nextBudget := budget / k
      let mut rem : List MVarId := []
      for sg in subgoals do
        setGoals [sg.mvarId]
        let pruned ← tryTac (requireClosed := true) `(tactic| (
          try simp only [$fnId:ident] at *
          first | contradiction | rfl | decide | decide +kernel))
        unless pruned do
          splitFiniteEnumsAndProve fnId nextBudget (← getMainGoal)
          rem := rem ++ (← getGoals)
      setGoals rem

syntax "qedProveFnEnsures " ident ident : tactic
syntax "qedProveBlindTo " ident ident str : tactic
syntax "qedProveFnExample " ident ident : tactic

elab_rules : tactic
  | `(tactic| qedProveFnEnsures $fnId $thmId) => do
      runProveFnGoal fnId false
      throwUnsolvedInvGoals thmId m!"`ensures` contract failed for `{fnId.getId}`:"
        m!"Hint: Strengthen `requires` / `if` guards, fix the return value, or supply a `:= by` proof."

  | `(tactic| qedProveBlindTo $fnId $thmId $desc) => do
      runProveFnGoal fnId true
      throwUnsolvedInvGoals thmId m!"`blindTo {desc.getString}` failed in `{fnId.getId}` (output may depend on blinded field/parameter):"
        m!"Hint: Redact every branch that reads {desc.getString} under this guard, strengthen the `if` condition, or supply a `:= by` proof."

  | `(tactic| qedProveFnExample $fnId $thmId) => do
      if ← tryTac (requireClosed := true) `(tactic| first | rfl | decide | decide +kernel) then return
      let saved ← saveState
      runProveFnGoal fnId false
      if !(← getGoals).isEmpty then
        restoreState saved
        forEachGoal (splitFiniteEnumsAndProve fnId 256)
      throwUnsolvedInvGoals thmId m!"`example` failed for `{fnId.getId}`:"
        m!"Hint: Check the expected output in the `example`, fix `{fnId.getId}`, or supply a `prove:` / `:= by` proof."

/-! ## Shared Pure Statement Lowering & `fn` Contract Elaboration -/

section FnElab
open Lean Elab Command Qed.Lang

@[noinline]
private partial def lowerPureFnStmtsAux (fnDesc : String)
    (lowerVal : Syntax → CommandElabM Term) (lowerGuard : Syntax → CommandElabM Term)
    (muts : Array Ident) (loopMuts? : Option (Array Ident)) (depth : Nat) (stmts : List Syntax) : CommandElabM Term := do
  let recSelf (m' : Array Ident := muts) (lm' : Option (Array Ident) := loopMuts?) (d' : Nat := depth) (ss : List Syntax) :=
    lowerPureFnStmtsAux fnDesc lowerVal lowerGuard m' lm' d' ss
  let dropShadowed (names : Array Name) (ms : Array Ident) : Array Ident :=
    ms.filter fun m => !names.contains m.getId.eraseMacroScopes
  match stmts with
  | [] =>
      match loopMuts? with
      | none => throwError s!"missing `return` on fallthrough path of `{fnDesc}`"
      | some lm => let stPack ← liftMacroM (mkMutPack lm.toList); `(Qed.QedLoopStep.next $stPack)
  | s :: rest =>
      let sk := s.getKind
      if sk == ``qedStmtPass then recSelf (ss := rest)
      else if sk == ``qedStmtBreak then
        let some lm := loopMuts? | throwErrorAt s "`break` can only be used inside a `for` loop"
        let stPack ← liftMacroM (mkMutPack lm.toList); `(Qed.QedLoopStep.breakLoop $stPack)
      else if sk == ``qedStmtContinue then
        let some lm := loopMuts? | throwErrorAt s "`continue` can only be used inside a `for` loop"
        let stPack ← liftMacroM (mkMutPack lm.toList); `(Qed.QedLoopStep.next $stPack)
      else if sk == ``qedStmtReturn then
        unless (s.getArg 1).getNumArgs == 1 do throwErrorAt s s!"`return` inside `{fnDesc}` must return a value"
        let v ← lowerVal ((s.getArg 1).getArg 0)
        match loopMuts? with
        | none => pure v
        | some lm => let stPack ← liftMacroM (mkMutPack lm.toList); `(Qed.QedLoopStep.ret $stPack $v)
      else if sk == ``qedStmtLetMut then
        let lId : Ident := ⟨s.getArg 2⟩; let nm := lId.getId.eraseMacroScopes
        if muts.any (·.getId.eraseMacroScopes == nm) then
          throwErrorAt lId s!"mutable variable `{nm}` is already declared in this scope; update it with `{nm} = ...`"
        let rhsT ← lowerVal (s.getArg 5)
        let cont ← recSelf (m' := muts.push lId) (ss := rest)
        if (s.getArg 3).getNumArgs == 2 then
          let lTy ← liftMacroM (return (← lowerQedType ((s.getArg 3).getArg 1) false).1)
          `(let $lId:ident : $lTy := $rhsT; $cont)
        else `(let $lId:ident := $rhsT; $cont)
      else if let some act := tryMatchLocalMut? muts s then
        if sk == ``qedStmtAssign && s.getNumArgs > 3 && (s.getArg 3).getNumArgs > 0 then
          throwErrorAt ((s.getArg 3).getArg 0) s!"`predict` is not supported in pure `{fnDesc}`"
        let rhsT ← lowerVal act.rhsSyntax
        let newVal ← liftMacroM (applyLocalMutRhs act rhsT)
        let lId := act.targetIdent
        let cont ← recSelf (ss := rest)
        `(let $lId:ident := $newVal; $cont)
      else if sk == ``qedStmtFor then
        let bStx := s.getArg 1; let iterStx := s.getArg 3; let bodyStmts := suiteStmts (s.getArg 5)
        if bStx.isIdent then
          let bNm := bStx.getId.eraseMacroScopes
          if muts.any (·.getId.eraseMacroScopes == bNm) then
            throwErrorAt bStx s!"`for` loop variable `{bNm}` shadows mutable variable `{bNm}`; use a different loop variable name"
        let iterTerm ← lowerVal iterStx
        let mutated := collectMutatedIds bodyStmts
        let usedMuts := muts.filter fun m => mutated.contains m.getId.eraseMacroScopes
        let initSt ← liftMacroM (mkMutPack usedMuts.toList)
        let stParam := mkIdent (Name.mkSimple s!"_qedSt{depth}")
        let resSt := mkIdent (Name.mkSimple s!"_qedLoopSt{depth}")
        let resRet := mkIdent (Name.mkSimple s!"_qedLoopRet{depth}")
        let retValId := mkIdent (Name.mkSimple s!"_qedRet{depth}")
        let bodyInner ← recSelf (lm' := some usedMuts) (d' := depth + 1) (ss := bodyStmts.toList)
        let bodyWithUnpack ← liftMacroM (wrapMutUnpack stParam usedMuts.toList bodyInner)
        let lam ← if bStx.isIdent then `(fun $stParam:ident $(⟨bStx⟩):ident => $bodyWithUnpack) else `(fun $stParam:ident _ => $bodyWithUnpack)
        let loopCall ← if isRangeCallExpr iterStx then `(Qed.qedForRange $iterTerm $initSt $lam) else `(Qed.qedForFold $iterTerm $initSt $lam)
        let restTerm ← recSelf (d' := depth + 1) (ss := rest)
        let someArm ← match loopMuts? with
          | none => pure (⟨retValId.raw⟩ : Term)
          | some outerMuts => let outerPack ← liftMacroM (mkMutPack outerMuts.toList); `(Qed.QedLoopStep.ret $outerPack $retValId)
        let afterLoop ← liftMacroM (wrapMutUnpack resSt usedMuts.toList (← `(match $resRet:ident with | Option.some $retValId:ident => $someArm | Option.none => $restTerm)))
        `(let ($resSt:ident, $resRet:ident) := $loopCall; $afterLoop)
      else if sk == ``qedStmtExpr then
        if rest.isEmpty && loopMuts?.isNone then lowerVal (s.getArg 0)
        else throwErrorAt s s!"unexpected bare expression statement in pure `{fnDesc}`; bind it with `let _ = ...` or return it"
      else if sk == ``qedStmtLet then
        if (s.getArg 5).getNumArgs > 0 then throwErrorAt ((s.getArg 5).getArg 0) s!"`predict`/`catch` clauses are not supported in pure `{fnDesc}`"
        let rhsT ← lowerVal (s.getArg 4)
        let bStx := s.getArg 1
        let muts' := if bStx.isIdent then dropShadowed #[bStx.getId.eraseMacroScopes] muts else muts
        let cont ← recSelf (m' := muts') (ss := rest)
        if bStx.isIdent then
          let lId : Ident := ⟨bStx⟩
          if (s.getArg 2).getNumArgs == 2 then
            let lTy ← liftMacroM (return (← lowerQedType ((s.getArg 2).getArg 1) false).1)
            `(let $lId:ident : $lTy := $rhsT; $cont)
          else `(let $lId:ident := $rhsT; $cont)
        else `(let _ := $rhsT; $cont)
      else if sk == ``qedStmtLetElse then
        let pat ← liftMacroM (lowerQedPat (s.getArg 1))
        let scrut ← lowerVal (s.getArg 3)
        let elseStmts := extractLetElseStmts s
        let elseT ← recSelf (ss := elseStmts.toList)
        let thenT ← recSelf (m' := dropShadowed (collectQedPatIds (s.getArg 1)) muts) (ss := rest)
        `(match $(mkIdent `_qedLetElse):ident : $scrut:term with | $pat:term => $thenT | _ => $elseT)
      else if sk == ``qedStmtIf then
        let cond ← lowerGuard (s.getArg 1)
        let thenT ← recSelf (ss := (suiteStmts (s.getArg 3)).toList ++ rest)
        let elseStmts := (desugarElifs (s.getArg 4).getArgs (s.getArg 5)).getD #[]
        let elseT ← recSelf (ss := elseStmts.toList ++ rest)
        `(if $(mkIdent `_qedIf):ident : $cond then $thenT else $elseT)
      else if sk == ``qedStmtIfLet then
        let pat ← liftMacroM (lowerQedPat (s.getArg 2))
        let scrut ← lowerVal (s.getArg 4)
        let thenT ← recSelf (m' := dropShadowed (collectQedPatIds (s.getArg 2)) muts) (ss := (suiteStmts (s.getArg 6)).toList ++ rest)
        let elseStmts := (extractElseSuite (s.getArg 7)).getD #[]
        let elseT ← recSelf (ss := elseStmts.toList ++ rest)
        `(match $(mkIdent `_qedIfLet):ident : $scrut:term with | $pat:term => $thenT | _ => $elseT)
      else if sk == ``qedStmtMatch then
        let scruts ← (s.getArg 1).getSepArgs.mapM lowerVal
        let alts ← (s.getArg 3).getArgs.mapM fun alt => do
          let altTerms ← liftMacroM (lowerCasePatAlts (alt.getArg 1))
          let patIds := collectCasePatIds (extractCasePatAlts (alt.getArg 1))
          let body ← recSelf (m' := dropShadowed patIds muts) (ss := (suiteStmts (alt.getArg 3)).toList ++ rest)
          mkMatchAltFromAlts altTerms body
        `(match $[$scruts:term],* with $[$alts:matchAlt]*)
      else if sk == ``qedStmtAssign then
        let lhsStr := stxSnippet (s.getArg 0)
        throwErrorAt s s!"cannot assign to `{lhsStr}` in pure `{fnDesc}`; declare local variables with `let mut {lhsStr} = ...` to mutate them"
      else
        let sn := stxSnippet s
        throwErrorAt s s!"unsupported statement{if sn.isEmpty then "" else s!" `{sn}`"} in pure `{fnDesc}`"

@[noinline]
def lowerPureFnStmts (fnDesc : String) (stmts : List Syntax)
    (lowerVal : Syntax → CommandElabM Term := fun s => liftMacroM (lowerSimpleQedExpr .val s))
    (lowerGuard : Syntax → CommandElabM Term := fun s => liftMacroM (lowerSimpleQedExpr .propGuard s)) : CommandElabM Term :=
  lowerPureFnStmtsAux fnDesc lowerVal lowerGuard #[] none 0 stmts

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

private structure ParsedFnExample where
  ref    : Syntax
  name   : Ident
  params : Array Syntax
  wheres : Array Syntax
  preds  : Array Syntax
  tac?   : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)

private structure ParsedFnContracts where
  requires : Array Syntax := #[]
  ensures  : Array ParsedFnEnsures := #[]
  blinds   : Array ParsedFnBlindTo := #[]
  examples : Array ParsedFnExample := #[]

def parseOptTacSeq (optNode : Syntax) : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
  if optNode.getNumArgs == 1 then
    let inner := optNode.getArg 0
    if inner.getKind == `Qed.fnProofBy || inner.getKind == `Qed.fnProofProve then some ⟨inner.getArg 2⟩ else none
  else none

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
    else if k == ``fnExampleClause then
      unless guards.isEmpty do throwErrorAt cl "`example` must appear at the top level of `fn` (use `where` on `example` for preconditions)"
      let exName : Ident := ⟨cl.getArg 1⟩
      if acc.examples.any (·.name.getId.eraseMacroScopes == exName.getId.eraseMacroScopes) then
        throwErrorAt exName s!"duplicate `example {exName.getId}` in `fn`"
      let params := if (cl.getArg 2).getNumArgs == 3 then ((cl.getArg 2).getArg 1).getSepArgs else #[]
      let wheres := if (cl.getArg 3).getNumArgs == 2 then ((cl.getArg 3).getArg 1).getSepArgs else #[]
      acc := { acc with examples := acc.examples.push { ref := cl, name := exName, params, wheres, preds := (cl.getArg 5).getSepArgs, tac? := parseOptTacSeq (cl.getArg 6) } }
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
    (contracts : Array Syntax) (extraPreHyps : Array (Ident × Term) := #[]) (isPrivate : Bool := false) : CommandElabM Unit := do
  if contracts.isEmpty then return
  let parsed ← collectFnContracts #[] contracts {}
  let lowerProp (s : Syntax) : CommandElabM Term := liftMacroM (lowerSimpleQedExpr .propInv s)
  let elabThm (thmId : Ident) (binders : Array (TSyntax `Lean.Parser.Term.bracketedBinder)) (goal : Term) (proofTac : TSyntax ``Lean.Parser.Tactic.tacticSeq) : CommandElabM Unit := do
    Qed.Lang.elabCmdWithVis isPrivate (← `(command|
      set_option linter.unusedVariables false in
      theorem $thmId $[$binders:bracketedBinder]* : $goal := by $proofTac))
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
    elabThm thmId binders (← `(let $resId:ident : $retTy := $rhsCall; $ensProp)) proofTac
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
    elabThm thmId binders eqProp proofTac
  for ex in parsed.examples do
    let thmId := mkIdentFrom ex.name (thmBaseId.getId.appendAfter s!"_example_{ex.name.getId.eraseMacroScopes}")
    let mut exBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
    for ep in ex.params do
      let pid : Ident := ⟨ep.getArg 0⟩
      let pty ← liftMacroM (return (← lowerQedType (ep.getArg 2) false).1)
      exBinders := exBinders.push (← `(bracketedBinder| ($pid:ident : $pty)))
    for (w, i) in ex.wheres.zipIdx do
      let wp ← lowerProp w
      exBinders := exBinders.push (← `(bracketedBinder| ($(mkIdent (Name.mkSimple s!"_hExWhere_{i}")):ident : $wp)))
    let exProp ← mkConjBody (← ex.preds.mapM lowerProp)
    let proofTac : TSyntax ``Lean.Parser.Tactic.tacticSeq ← match ex.tac? with
      | some ts => pure ts
      | none    => `(Lean.Parser.Tactic.tacticSeq| qedProveFnExample $fnConstId $thmId)
    elabThm thmId exBinders exProp proofTac

@[noinline, command_elab fnCmd] def elabFnCmd : CommandElab := fun stx => do
  let doc? := if (stx.getArg 0).getNumArgs == 1 then some (⟨(stx.getArg 0).getArg 0⟩ : TSyntax ``Lean.Parser.Command.docComment) else none
  let isPrivate := (stx.getArg 1).getNumArgs == 1
  let fnId : Ident := ⟨stx.getArg 3⟩
  let rawParams := (stx.getArg 5).getSepArgs
  let mut paramIds : Array Ident := #[]; let mut paramTys : Array Term := #[]
  let mut defBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]; let mut seenDefault := false
  for rp in rawParams do
    let pid : Ident := ⟨rp.getArg 0⟩
    if paramIds.any (·.getId.eraseMacroScopes == pid.getId.eraseMacroScopes) then
      throwErrorAt pid s!"duplicate parameter `{pid.getId}` in `fn {fnId.getId}`"
    let pty ← liftMacroM (return (← lowerQedType (rp.getArg 2) false).1)
    let optDef := rp.getArg 3
    if optDef.getNumArgs == 2 then
      seenDefault := true
      let defT ← liftMacroM (lowerSimpleQedExpr .val (optDef.getArg 1))
      defBinders := defBinders.push (← `(bracketedBinder| ($pid:ident : $pty := $defT)))
    else
      if seenDefault then throwErrorAt pid s!"non-default parameter `{pid.getId}` cannot follow a parameter with a default value in `fn {fnId.getId}`"
      defBinders := defBinders.push (← `(bracketedBinder| ($pid:ident : $pty)))
    paramIds := paramIds.push pid; paramTys := paramTys.push pty
  let retTy ← liftMacroM (return (← lowerQedType (stx.getArg 8) false).1)
  let contracts := (stx.getArg 10).getArgs
  let bodyStmts := (stx.getArg 11).getArgs
  let bodyTerm ← lowerPureFnStmts s!"fn {fnId.getId}" bodyStmts.toList
  Qed.Lang.elabCmdWithVis isPrivate (← `(command|
    $[$doc?:docComment]? def $fnId $[$defBinders:bracketedBinder]* : $retTy := $bodyTerm))
  elabPureFnContracts fnId fnId paramIds paramTys retTy contracts #[] isPrivate

end FnElab

end Qed
