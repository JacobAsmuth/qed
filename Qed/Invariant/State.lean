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
  tryRestoreM false id (Meta.withTransparency .reducible (g.contradictionCore {}))

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
private abbrev fType : Parser := withPosition (categoryParser `qedType 0)
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

simproc_decl fnReduceStrLen (String.length _) := fun e => do
  let some (Expr.lit (Literal.strVal s)) := e.getAppArgs[0]? | return .continue
  let charTy := mkConst ``Char
  let cs := s.toList.foldr (fun c acc => mkApp2 (mkApp (mkConst ``List.cons [0]) charTy) (mkApp (mkConst ``Char.ofNat) (mkNatLit c.toNat)) acc) (mkApp (mkConst ``List.nil [0]) charTy)
  let nExpr := mkNatLit s.length
  return .done { expr := nExpr, proof? := some (← Meta.mkEqTrans (mkApp (mkConst ``String.length_ofList) cs) (← Meta.mkEqRefl nExpr)) }

private def fnContractSimpNames : Array Name :=
  impHypSimpNames ++ #[``Array.size_push, ``Array.size_set, ``Array.size_map, ``Array.size_append,
    ``Array.size_reverse, ``List.length_cons, ``List.length_append, ``List.length_map,
    ``String.length_append, ``String.all_bool_eq, ``Qed.Str.str_toString,
    ``Qed.Lang.QedSeqLit.ofList_array, ``Qed.Lang.QedSeqLit.ofList_list, ``Array.mem_toArray,
    ``Option.isSome_none, ``Option.isSome_some, ``Option.isNone_none, ``Option.isNone_some,
    ``Decidable.not_not, ``Bool.not_eq_false, ``Bool.not_eq_true, ``not_or,
    ``Qed.qedCoalesce_option, ``Qed.qedIterable_toList_list, ``Qed.qedIterable_toList_array, ``Qed.qedIterable_toList_range,
    ``true_and, ``and_true, ``false_or, ``or_false, ``true_or, ``or_true, ``id_eq, ``ne_eq]

private def pruneSimpNames : Array Name :=
  #[``reduceCtorEq, ``Option.some.injEq, ``Option.isSome_none, ``Option.isSome_some,
    ``Option.isNone_none, ``Option.isNone_some, ``Bool.false_eq_true, ``Bool.true_eq_false,
    ``Bool.not_true, ``Bool.not_false, ``ite_true, ``ite_false, ``dite_true, ``dite_false,
    ``Qed.Lang.QedVal.val_id]

private def strGuardNormNames : Array Name :=
  boolSimpNames ++ boolConstSimpNames ++ #[``Qed.Lang.QedVal.val_id, ``Qed.Str.str_toString,
    ``Qed.Lang.QedMem.mem_array, ``Qed.Lang.QedMem.mem_list, ``Qed.Lang.QedMem.mem_string,
    ``Qed.Lang.QedMemProp.memProp_array, ``Qed.Lang.QedMemProp.memProp_list, ``Qed.Lang.QedMemProp.memProp_string,
    ``Qed.Lang.QedSeqLit.ofList_array, ``Qed.Lang.QedSeqLit.ofList_list,
    ``Array.contains_iff_mem, ``List.contains_iff_mem, ``Array.mem_toArray,
    ``Decidable.not_not, ``Bool.not_eq_false, ``Bool.not_eq_true, ``not_or, ``String.all_bool_eq]

private def strAllNormNames : Array Name :=
  #[``String.all_bool_eq, ``Qed.Lang.QedVal.val_id, ``Qed.Str.str_toString, ``String.toList_append, ``List.all_append, ``Bool.and_eq_true]

private def countBVar (idx : Nat) : Expr → Nat
  | .bvar i => if i == idx then 1 else 0
  | .app f a => countBVar idx f + countBVar idx a
  | .lam _ ty b _ | .forallE _ ty b _ => countBVar idx ty + countBVar (idx + 1) b
  | .letE _ ty v b _ => countBVar idx ty + countBVar idx v + countBVar (idx + 1) b
  | .mdata _ e | .proj _ _ e => countBVar idx e
  | _ => 0

/-- When `let result := rhs; body` references `result` multiple times, introduce `result` as a shared
    free variable with `hRes : result = rhs` so unfolding `fnId` never duplicates its body. -/
private def shareLetResult? (g0 : MVarId) : MetaM (Option (FVarId × FVarId × MVarId)) := do
  let tgt := (← g0.withContext (instantiateMVars (← g0.getType))).consumeMData
  let .letE nm ty val body _ := tgt | return none
  if countBVar 0 body < 2 then return none
  g0.withContext do
    let u ← Meta.getLevel ty
    let eqTy := mkApp3 (mkConst ``Eq [u]) ty (.bvar 0) val
    let newTy := Expr.forallE nm ty (Expr.forallE `_qedResDef eqTy (body.liftLooseBVars 0 1) .default) .default
    let m ← Meta.mkFreshExprSyntheticOpaqueMVar newTy
    g0.assign (mkApp2 m val (← Meta.mkEqRefl val))
    let (resFv, g1) ← m.mvarId!.intro1P
    let (hResFv, g2) ← g1.intro1P
    return some (resFv, hResFv, g2)

private def isEqNoneOf? (ty : Expr) : Option FVarId :=
  match ty.consumeMData.eq? with
  | some (_, lhs, rhs) =>
      let l := lhs.consumeMData; let r := rhs.consumeMData
      if l.isFVar && r.isAppOfArity ``Option.none 1 then some l.fvarId!
      else if r.isFVar && l.isAppOfArity ``Option.none 1 then some r.fvarId!
      else none
  | none => none

private def trySubstFVar (g : MVarId) (fv : FVarId) : MetaM (Option MVarId) :=
  tryRestoreM none Option.isSome do return some (← Meta.subst g fv)

private def findFVarByName? (g : MVarId) (nm : Name) : MetaM (Option FVarId) :=
  g.withContext do
    let mut found : Option FVarId := none
    for d in (← getLCtx) do
      if !d.isImplementationDetail && d.userName == nm then found := some d.fvarId
    return found

private def simpOneFVar (g : MVarId) (ctx : Meta.Simp.Context) (fv : FVarId) : MetaM (Option (FVarId × MVarId)) :=
  tryRestoreM (some (fv, g)) (fun _ => true) do
    match (← Meta.simpGoal g ctx #[] none (simplifyTarget := false) #[fv]).1 with
    | none => return none
    | some (newFvs, g') => return some (newFvs.getD 0 fv, g')

private def isDefEqFast (a b : Expr) : MetaM Bool :=
  if a == b then pure true else Meta.withTransparency .reducible (Meta.isDefEq a b)

private def stripValWrapAux (e : Expr) : Nat → Expr
  | 0 => e.consumeMData
  | fuel + 1 =>
      let e := e.consumeMData
      if e.isAppOfArity ``Qed.Lang.QedVal.val 4 then stripValWrapAux e.getAppArgs[3]! fuel
      else if e.isAppOfArity ``toString 3 && e.getAppArgs[0]!.isConstOf ``String then stripValWrapAux e.getAppArgs[2]! fuel
      else e

private def stripValWrap (e : Expr) : Expr := stripValWrapAux e 32

private def isOuterIteEq (ty : Expr) : Bool :=
  match ty.consumeMData.eq? with
  | some (_, lhs, rhs) =>
      let l := stripValWrap lhs; let r := stripValWrap rhs
      l.isAppOfArity ``dite 5 || l.isAppOfArity ``ite 5 || r.isAppOfArity ``dite 5 || r.isAppOfArity ``ite 5
  | none => false

/-- Split `(if h : c then t h else e h) = v` (or symmetric / `ite`) in strict O(1) without calling
    `simp`/`dite_congr` over inner `if` spines (avoids O(k * 2^k) `splitLocalDecl?` blowup on k guards). -/
private def tryFastSplitIteEqHyp (g : MVarId) (fv : FVarId) (fvName : Name) : MetaM (Option (List MVarId)) :=
  tryRestoreM none Option.isSome do
    let ty ← g.withContext do instantiateMVars (← fv.getType)
    let some (eqTy, lhs, rhs) := ty.consumeMData.eq? | return none
    let l := stripValWrap lhs; let r := stripValWrap rhs
    let (isLeft, isDite, ifExpr, other) ←
      if l.isAppOfArity ``dite 5 then pure (true, true, l, r)
      else if l.isAppOfArity ``ite 5 then pure (true, false, l, r)
      else if r.isAppOfArity ``dite 5 then pure (false, true, r, l)
      else if r.isAppOfArity ``ite 5 then pure (false, false, r, l)
      else return none
    let args := ifExpr.getAppArgs
    let c := args[1]!; let decInst := args[2]!; let t := args[3]!; let e := args[4]!
    let lem := match isLeft, isDite with
      | true,  true  => ``Qed.Str.dite_eq_cases
      | false, true  => ``Qed.Str.eq_dite_cases
      | true,  false => ``Qed.Str.ite_eq_cases
      | false, false => ``Qed.Str.eq_ite_cases
    g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      let u ← Meta.getLevel eqTy
      let mkBranch (isPos : Bool) (branchExpr : Expr) : MetaM MVarId := do
        let condTy := if isPos then c else mkApp (mkConst ``Not) c
        let bTy ← Meta.withLocalDeclD `_qedCond condTy fun hc => do
          let valExpr := if isDite then branchExpr.beta #[hc] else branchExpr
          let eqExpr := if isLeft then mkApp3 (mkConst ``Eq [u]) eqTy valExpr other
                        else mkApp3 (mkConst ``Eq [u]) eqTy other valExpr
          Meta.mkForallFVars #[hc] (Expr.forallE fvName eqExpr tgt .default)
        return (← Meta.mkFreshExprSyntheticOpaqueMVar bTy).mvarId!
      let mThen ← mkBranch true t
      let mElse ← mkBranch false e
      let pf := mkAppN (mkConst lem [u]) #[eqTy, c, decInst, t, e, other, tgt, mkFVar fv, mkMVar mThen, mkMVar mElse]
      g.assign pf
      let prep (m : MVarId) : MetaM MVarId := do
        let m1 ← try m.clear fv catch _ => pure m
        let (_, m2) ← m1.intro1
        let (_, m3) ← m2.intro fvName
        return m3
      return some [← prep mThen, ← prep mElse]

/-- Fast O(1) pruning of a single split branch before splitting any deeper guards. -/
private def tryPruneBranch (g0 : MVarId) (fvName? : Option Name) : MetaM (Option MVarId) := do
  if ← tryCloseContradiction g0 then return none
  if ← tryCloseTrivial g0 (reducibleOnly := true) then return none
  let (g1, curFv?) ← match fvName? with
    | some nm =>
        match ← findFVarByName? g0 nm with
        | none => pure (g0, none)
        | some fv =>
            let fvTy ← g0.withContext do instantiateMVars (← fv.getType)
            if isOuterIteEq fvTy then pure (g0, some fv)
            else do
              let (pruneCtx, _) ← mkCachedSimpCtx "fnPrune" pruneSimpNames { zetaDelta := false } #[] false false
              match ← simpOneFVar g0 pruneCtx fv with
              | none => return none
              | some (fv', g') => pure (g', some fv')
    | none =>
        let (pruneCtx, _) ← mkCachedSimpCtx "fnPrune" pruneSimpNames { zetaDelta := false } #[] false false
        match ← simpGoalOnly g0 pruneCtx #[] #[] (simplifyTarget := true) with
        | none => return none
        | some g' => pure (g', none)
  if ← tryCloseContradiction g1 then return none
  if ← tryCloseTrivial g1 (reducibleOnly := true) then return none
  if let some fv := curFv? then
    let fvTy ← g1.withContext do instantiateMVars (← fv.getType)
    if let some optFv := isEqNoneOf? fvTy then
      let conflictName? ← g1.withContext do
        for d in (← getLCtx) do
          if d.fvarId != fv && !d.isImplementationDetail && !d.isLet then
            let dt := (← instantiateMVars d.type).consumeMData
            if dt.containsFVar optFv then
              if dt.getUsedConstants.any fun c => c == ``Option.isSome || c == ``Option.some then
                return some d.userName
        return none
      if let some cNm := conflictName? then
        if let some gSub ← trySubstFVar g1 fv then
          if let some cFv ← findFVarByName? gSub cNm then
            let (pruneCtx, _) ← mkCachedSimpCtx "fnPrune" pruneSimpNames { zetaDelta := false } #[] false false
            match ← simpOneFVar gSub pruneCtx cFv with
            | none => return none
            | some (_, gSub') =>
                if ← tryCloseContradiction gSub' then return none
  return some g1

/-- Incrementally split outermost `if`/`match` in one hypothesis (tracked by name across FVarId refreshes),
    pruning dead branches at every step so `k` guards produce O(k) trivial closures instead of O(2^k) / O(k^2). -/
@[noinline]
private def linearSplitHyp (g0 : MVarId) (fvName : Name) (substTargetName? : Option Name := none)
    (maxLive : Nat := 16) (fuel : Nat := 32) : MetaM (List MVarId) := do
  let rec go (work done : List MVarId) : Nat → MetaM (List MVarId)
    | 0 => return done.reverse ++ work
    | fuel + 1 =>
        match work with
        | [] => return done.reverse
        | g :: rest => do
            if done.length + work.length > maxLive then return done.reverse ++ work
            let some fv ← findFVarByName? g fvName | go rest (g :: done) fuel
            let splitRes ← match ← tryFastSplitIteEqHyp g fv fvName with
              | some kids => pure (some kids)
              | none => trySplitLocalDecl g fv
            match splitRes with
            | none => go rest (g :: done) fuel
            | some kids =>
                let mut live : List MVarId := []
                for sg in kids do
                  if let some sg' ← tryPruneBranch sg (some fvName) then live := sg' :: live
                go (live.reverse ++ rest) done fuel
  let survived ← go [g0] [] fuel
  match substTargetName? with
  | none => return survived
  | some targetNm =>
      let mut out : List MVarId := []
      for g in survived do
        let some fv ← findFVarByName? g fvName | out := g :: out
        let some targetFv ← findFVarByName? g targetNm | out := g :: out
        let fvTy ← g.withContext do instantiateMVars (← fv.getType)
        let shouldSubst := match fvTy.consumeMData.eq? with
          | some (_, lhs, rhs) =>
              (lhs.consumeMData == mkFVar targetFv && !rhs.containsFVar targetFv) ||
              (rhs.consumeMData == mkFVar targetFv && !lhs.containsFVar targetFv)
          | none => false
        if shouldSubst then
          if let some gSub ← trySubstFVar g fv then
            if let some gPruned ← tryPruneBranch gSub none then out := gPruned :: out
          else out := g :: out
        else out := g :: out
      return out.reverse

/-- Incrementally split outermost `if`/`match` in the goal target with immediate pruning. -/
@[noinline]
private def linearSplitTarget (g0 : MVarId) (maxLive : Nat := 16) (fuel : Nat := 32) : MetaM (List MVarId) := do
  let rec go (work done : List MVarId) : Nat → MetaM (List MVarId)
    | 0 => return done.reverse ++ work
    | fuel + 1 =>
        match work with
        | [] => return done.reverse
        | g :: rest => do
            if done.length + work.length > maxLive then return done.reverse ++ work
            match ← trySplitTarget g with
            | none => go rest (g :: done) fuel
            | some kids =>
                let mut live : List MVarId := []
                for sg in kids do
                  if let some sg' ← tryPruneBranch sg none then live := sg' :: live
                go (live.reverse ++ rest) done fuel
  go [g0] [] fuel

private def unfoldConstInFVarName (g : MVarId) (fnName : Name) (fvName : Name) : MetaM (Option MVarId) := do
  let some fv ← findFVarByName? g fvName | return some g
  let fast? ← tryRestoreM none Option.isSome <| g.withContext do
    let ty ← instantiateMVars (← fv.getType)
    let ty' ← Meta.deltaExpand ty (· == fnName)
    if ty' == ty then return none
    return some (← g.replaceLocalDeclDefEq fv ty')
  if let some g' := fast? then return some g'
  let ctx ← mkDynamicSimpCtx #[fnName] none { zetaDelta := true } (dsimpOnly := false) (withEqns := true)
  return (← simpOneFVar g ctx fv).map Prod.snd

private def unfoldConstInTarget (g : MVarId) (fnName : Name) : MetaM (Option MVarId) := do
  let fast? ← tryRestoreM none Option.isSome <| g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    let tgt' ← Meta.deltaExpand tgt (· == fnName)
    if tgt' == tgt then return none
    return some (← g.replaceTargetDefEq tgt')
  if let some g' := fast? then return some g'
  let ctx ← mkDynamicSimpCtx #[fnName] none { zetaDelta := true } (dsimpOnly := false) (withEqns := true)
  simpGoalOnly g ctx #[] #[] (simplifyTarget := true)

/-! ### Linear-Time String Equality & Character-Predicate Prover -/

private def extractStrLit? (e : Expr) : Option String :=
  match (stripValWrap e).consumeMData with
  | .lit (.strVal s) => some s
  | _ => none

private def extractStrAppend? (e : Expr) : Option (Expr × Expr) :=
  let e := (stripValWrap e).consumeMData
  if e.isAppOfArity ``HAppend.hAppend 6 && e.getAppArgs[0]!.isConstOf ``String then
    some (e.getAppArgs[4]!, e.getAppArgs[5]!)
  else if e.isAppOfArity ``String.append 2 then
    some (e.getAppArgs[0]!, e.getAppArgs[1]!)
  else none

private def extractToStringOf? (tyNm reprNm : Name) (e : Expr) : Option Expr :=
  let e := (stripValWrap e).consumeMData
  if e.isAppOfArity ``toString 3 && e.getAppArgs[0]!.isConstOf tyNm then some (stripValWrap e.getAppArgs[2]!)
  else if e.isAppOfArity reprNm 1 then some (stripValWrap e.getAppArgs[0]!)
  else none

private def extractNatToString? := extractToStringOf? ``Nat ``Nat.repr
private def extractIntToString? := extractToStringOf? ``Int ``Int.repr

private def tryMkDecideProof (prop : Expr) : MetaM (Option Expr) := do
  let prop ← instantiateMVars prop
  if prop.hasFVar || prop.hasMVar then return none
  tryRestoreM none Option.isSome do
    let decInst ← Meta.synthInstance (mkApp (mkConst ``Decidable) prop)
    if ← Meta.isDefEq (mkApp2 (mkConst ``Decidable.decide) prop decInst) (mkConst ``Bool.true) then
      return some (mkApp3 (mkConst ``of_decide_eq_true) prop decInst (← Meta.mkEqRefl (mkConst ``Bool.true)))
    return none

private def tryCloseBoolFalse (lhs : Expr) : MetaM (Option Expr) := do
  let eqProp ← Meta.mkEq lhs (mkConst ``Bool.false)
  if let some pf ← tryMkDecideProof eqProp then return some pf
  tryRestoreM none Option.isSome do
    let m ← Meta.mkFreshExprSyntheticOpaqueMVar eqProp
    let (ctx, _) ← mkCachedSimpCtx "boolFalseCheck" (boolSimpNames ++ boolConstSimpNames ++ #[``Qed.Lang.QedVal.val_id])
    match ← simpGoalOnly m.mvarId! ctx with
    | none => return some (← instantiateMVars m)
    | some _ => return none

private def extractStrAll? (ty : Expr) : Option (Expr × Expr × Bool) :=
  match ty.consumeMData.eq? with
  | some (_, lhs, rhs) =>
      if !rhs.consumeMData.isConstOf ``Bool.true then none
      else
        let l := lhs.consumeMData
        if l.isAppOfArity ``List.all 3 then
          let xs := l.getAppArgs[1]!.consumeMData
          if xs.isAppOfArity ``String.toList 1 then some (stripValWrap xs.getAppArgs[0]!, l.getAppArgs[2]!, true)
          else none
        else if l.isAppOfArity ``String.all 4 then
          some (stripValWrap l.getAppArgs[1]!, l.getAppArgs[2]!, false)
        else none
  | none => none

private def extractStrContains? (ty : Expr) : Option (Expr × Expr × Bool) :=
  let t := ty.consumeMData
  if t.isAppOfArity ``Not 1 then
    match t.getAppArgs[0]!.consumeMData.eq? with
    | some (_, lhs, rhs) =>
        let l := lhs.consumeMData
        if rhs.consumeMData.isConstOf ``Bool.true && l.isAppOfArity ``String.contains 7 then
          some (stripValWrap l.getAppArgs[4]!, l.getAppArgs[5]!, true)
        else none
    | none => none
  else
    match t.eq? with
    | some (_, lhs, rhs) =>
        let l := lhs.consumeMData
        if rhs.consumeMData.isConstOf ``Bool.false && l.isAppOfArity ``String.contains 7 then
          some (stripValWrap l.getAppArgs[4]!, l.getAppArgs[5]!, false)
        else none
    | none => none

private def extractStrMemColl? (ty : Expr) : Option (Expr × Expr × Bool) :=
  let t := ty.consumeMData
  if t.isAppOfArity ``Membership.mem 5 && t.getAppArgs[0]!.isConstOf ``String then
    let collTy := t.getAppArgs[1]!.consumeMData
    let coll := t.getAppArgs[3]!.consumeMData
    let elem := stripValWrap t.getAppArgs[4]!
    if collTy.isAppOfArity ``List 1 then some (elem, coll, false)
    else if collTy.isAppOfArity ``Array 1 then some (elem, coll, true)
    else none
  else none

/-- Synthesize a direct proof of `d ∉ a.toList` in O(1) per segment without case splitting. -/
private partial def proveCharNotMem? (d : Char) (a0 : Expr) (depth : Nat := 2) : MetaM (Option Expr) := do
  let a := stripValWrap a0
  let dExpr := toExpr d
  let goalTy ← Meta.mkAppM ``Not #[← Meta.mkAppM ``Membership.mem #[← Meta.mkAppM ``String.toList #[a], dExpr]]
  -- 1. `toString (n : Nat)` / `Nat.repr n`
  if let some n := extractNatToString? a then
    if d < '0' || '9' < d then
      let hdTy ← Meta.mkAppM ``Or #[← Meta.mkAppM ``LT.lt #[dExpr, toExpr '0'], ← Meta.mkAppM ``LT.lt #[toExpr '9', dExpr]]
      if let some hd ← tryMkDecideProof hdTy then
        return some (← Meta.mkAppM ``Qed.Str.nat_toString_not_mem #[hd, n])
  -- 2. `toString (i : Int)` / `Int.repr i`
  if let some i := extractIntToString? a then
    if d != '-' && (d < '0' || '9' < d) then
      let hdTy ← Meta.mkAppM ``And #[← Meta.mkAppM ``Ne #[dExpr, toExpr '-'],
        ← Meta.mkAppM ``Or #[← Meta.mkAppM ``LT.lt #[dExpr, toExpr '0'], ← Meta.mkAppM ``LT.lt #[toExpr '9', dExpr]]]
      if let some hd ← tryMkDecideProof hdTy then
        return some (← Meta.mkAppM ``Qed.Str.int_toString_not_mem #[hd, i])
  -- 3. Concrete string literal
  if let some s := extractStrLit? a then
    if !s.contains d then
      if let some pf ← tryMkDecideProof goalTy then return some pf
  -- 4. Concatenation `x ++ y`
  if let some (x, y) := extractStrAppend? a then
    if let some hx ← proveCharNotMem? d x depth then
      if let some hy ← proveCharNotMem? d y depth then
        return some (← Meta.mkAppM ``Qed.Str.str_not_mem_append #[hx, hy])
  -- 5. Local context hypotheses constraining `a`
  let lctx ← getLCtx
  let env ← getEnv
  for decl in lctx do
    if !decl.isImplementationDetail && !decl.isLet then
      let ty := (← instantiateMVars decl.type).consumeMData
      if ← isDefEqFast ty goalTy then return some decl.toExpr
      -- `a.contains d = false` or `¬ (a.contains d = true)`
      if let some (s, ch, isNeg) := extractStrContains? ty then
        if ← isDefEqFast s a then
          if ← isDefEqFast ch dExpr then
            let lem := if isNeg then ``Qed.Str.str_not_mem_of_not_contains else ``Qed.Str.str_not_mem_of_contains_false
            return some (← Meta.mkAppM lem #[decl.toExpr])
      -- `a.all p = true` or `a.toList.all p = true`
      if let some (s, p, isToList) := extractStrAll? ty then
        if ← isDefEqFast s a then
          if let some hpd ← tryCloseBoolFalse (p.beta #[dExpr]) then
            let lem := if isToList then ``Qed.Str.str_not_mem_of_toList_all else ``Qed.Str.str_not_mem_of_all
            return some (← Meta.mkAppM lem #[decl.toExpr, hpd])
      -- `∀ c ∈ a.toList, P c`
      if let .forallE _ cTy (.forallE _ memTy body _) _ := ty then
        if cTy.isConstOf ``Char && memTy.isAppOfArity ``Membership.mem 5 && !body.hasLooseBVar 0 then
          let listArg := memTy.getAppArgs[3]!.consumeMData
          if listArg.isAppOfArity ``String.toList 1 then
            if ← isDefEqFast (stripValWrap listArg.getAppArgs[0]!) a then
              let predAtD := (body.lowerLooseBVars 1 1).instantiate1 dExpr
              if !predAtD.hasLooseBVars then
                if let some hnd ← tryMkDecideProof (← Meta.mkAppM ``Not #[predAtD]) then
                  return some (← Meta.mkAppM ``Qed.Str.str_not_mem_of_forall #[decl.toExpr, hnd])
      -- `a ∈ xs` (literal `List String` or `Array String`)
      if let some (elem, coll, isArr) := extractStrMemColl? ty then
        if ← isDefEqFast elem a then
          let listExpr ← if isArr then Meta.mkAppM ``Array.toList #[coll] else pure coll
          let pred ← Meta.withLocalDeclD `x (mkConst ``String) fun x => do
            let c ← Meta.mkAppM ``List.contains #[← Meta.mkAppM ``String.toList #[x], dExpr]
            Meta.mkLambdaFVars #[x] (mkApp (mkConst ``Bool.not) c)
          let allProp ← Meta.mkEq (← Meta.mkAppM ``List.all #[listExpr, pred]) (mkConst ``Bool.true)
          if let some hall ← tryMkDecideProof allProp then
            let lem := if isArr then ``Qed.Str.str_not_mem_of_mem_array else ``Qed.Str.str_not_mem_of_mem_list
            return some (← Meta.mkAppM lem #[decl.toExpr, hall])
      -- `userPred ... a ... = true` (unfold non-recursive user helper up to bounded depth)
      if depth > 0 then
        if let some (_, lhs, rhs) := ty.eq? then
          if rhs.consumeMData.isConstOf ``Bool.true then
            let fn := lhs.getAppFn
            if let .const fnNm _ := fn then
              if qedIsHelper env fnNm && lhs.getAppArgs.any (fun arg => stripValWrap arg == a) then
                let pf? ← tryRestoreM none Option.isSome do
                  let m ← Meta.mkFreshExprSyntheticOpaqueMVar goalTy
                  let ctx ← mkDynamicSimpCtx (strGuardNormNames.push fnNm) none { zetaDelta := true }
                  match ← simpGoalOnly m.mvarId! ctx #[] #[decl.fvarId] (simplifyTarget := false) with
                  | none => return some (← instantiateMVars m)
                  | some m1 =>
                      let (m2, _) ← splitAndHypsGoal m1 false 16
                      let res? ← m2.withContext (proveCharNotMem? d a (depth - 1))
                      match res? with
                      | some pf => m2.assign pf; return some (← instantiateMVars m)
                      | none => return none
                if pf?.isSome then return pf?
  return none

/-- Strip `QedVal.val` and `toString (s : String)` from a single string leaf in O(1), returning `(e', pf : e = e')`. -/
private partial def normStrLeaf (e0 : Expr) : MetaM (Expr × Expr) := do
  let e := e0.consumeMData
  if e.isAppOfArity ``Qed.Lang.QedVal.val 4 then
    let inner := e.getAppArgs[3]!
    let h1 ← Meta.mkAppM ``Qed.Lang.QedVal.val_id #[inner]
    let (e', h2) ← normStrLeaf inner
    return (e', ← Meta.mkEqTrans h1 h2)
  if e.isAppOfArity ``toString 3 && e.getAppArgs[0]!.isConstOf ``String then
    let inner := e.getAppArgs[2]!
    let h1 ← Meta.mkAppM ``Qed.Str.str_toString #[inner]
    let (e', h2) ← normStrLeaf inner
    return (e', ← Meta.mkEqTrans h1 h2)
  if e.isAppOfArity ``toString 3 then
    let arg := e.getAppArgs[2]!.consumeMData
    if arg.isAppOfArity ``Qed.Lang.QedVal.val 4 then
      let ty := e.getAppArgs[0]!
      let inner := arg.getAppArgs[3]!
      let hVal ← Meta.mkAppM ``Qed.Lang.QedVal.val_id #[inner]
      let toStrLam ← Meta.withLocalDeclD `x ty fun x => do
        Meta.mkLambdaFVars #[x] (mkApp3 e.getAppFn ty e.getAppArgs[1]! x)
      let h1 ← Meta.mkAppM ``congrArg #[toStrLam, hVal]
      return (mkApp3 e.getAppFn ty e.getAppArgs[1]! inner, h1)
  return (e, ← Meta.mkEqRefl e)

private def mkStrAppendExpr (x y : Expr) : MetaM Expr :=
  Meta.mkAppM ``HAppend.hAppend #[x, y]

private def congrStrAppendLeft (a h : Expr) : MetaM Expr := do
  let lam ← Meta.withLocalDeclD `z (mkConst ``String) fun z => do Meta.mkLambdaFVars #[z] (← mkStrAppendExpr a z)
  Meta.mkAppM ``congrArg #[lam, h]

private def congrStrAppendRight (b h : Expr) : MetaM Expr := do
  let lam ← Meta.withLocalDeclD `z (mkConst ``String) fun z => do Meta.mkLambdaFVars #[z] (← mkStrAppendExpr z b)
  Meta.mkAppM ``congrArg #[lam, h]

/-- Right-associate an arbitrary `String` append tree in strict O(S) using CPS accumulation
    (at most 1 `String.append_assoc` per internal `++` node, zero `simp` calls). -/
private partial def reassocStrAcc (t acc : Expr) : MetaM (Expr × Expr) := do
  let (t0, hLeaf) ← normStrLeaf t
  let hLift ← congrStrAppendRight acc hLeaf
  match extractStrAppend? t0 with
  | none =>
      if extractStrLit? t0 == some "" then
        return (acc, ← Meta.mkEqTrans hLift (← Meta.mkAppOptM ``String.empty_append #[some acc]))
      return (← mkStrAppendExpr t0 acc, hLift)
  | some (a, b) =>
      let (r1, h1) ← reassocStrAcc b acc
      let (r2, h2) ← reassocStrAcc a r1
      let hAssoc ← Meta.mkAppOptM ``String.append_assoc #[some a, some b, some acc]
      let hMid ← congrStrAppendLeft a h1
      return (r2, ← Meta.mkEqTrans hLift (← Meta.mkEqTrans hAssoc (← Meta.mkEqTrans hMid h2)))

private partial def reassocStr (t : Expr) : MetaM (Expr × Expr) := do
  let (t0, hLeaf) ← normStrLeaf t
  match extractStrAppend? t0 with
  | none => return (t0, hLeaf)
  | some (a, b) =>
      let (rb, hb) ← reassocStr b
      if extractStrLit? rb == some "" then
        let (ra, ha) ← reassocStr a
        let h1 ← congrStrAppendLeft a hb
        let h2 ← Meta.mkAppOptM ``String.append_empty #[some a]
        return (ra, ← Meta.mkEqTrans hLeaf (← Meta.mkEqTrans h1 (← Meta.mkEqTrans h2 ha)))
      let (res, hAcc) ← reassocStrAcc a rb
      let h1 ← congrStrAppendLeft a hb
      return (res, ← Meta.mkEqTrans hLeaf (← Meta.mkEqTrans h1 hAcc))

/-- Decompose a single `String` equality proof term `h : lhs = rhs` into atomic segment equalities
    (or a `False` proof on differing literal prefixes) in strict O(segments), with zero `simp` calls. -/
private def collectStringEqFacts (lhs0 rhs0 eqPf0 : Expr) (fuel0 : Nat := 32) :
    MetaM (Sum Expr (Array Expr)) := do
  let (lInit, hlInit) ← reassocStr lhs0
  let (rInit, hrInit) ← reassocStr rhs0
  let pfInit ← Meta.mkEqTrans (← Meta.mkEqTrans (← Meta.mkEqSymm hlInit) eqPf0) hrInit
  let rec go (l r eqPf' : Expr) : Nat → MetaM (Sum Expr (Array Expr))
    | 0 => return .inr #[eqPf']
    | fuel + 1 => do
      if l == r then return .inr #[]
      -- Case 1: Both sides are `p₁ ++ x` and `p₂ ++ y`
      if let (some (p₁, x), some (p₂, y)) := (extractStrAppend? l, extractStrAppend? r) then
        if p₁ == p₂ then
          let hNext ← Meta.mkAppM ``Qed.Str.str_append_left_cancel #[eqPf']
          return ← go x y hNext fuel
        if let (some s₁, some s₂) := (extractStrLit? p₁, extractStrLit? p₂) then
          if (s₁.toList.zip s₂.toList).any (fun ab => ab.1 != ab.2) then
            let diffProp ← Meta.mkEq
              (← Meta.mkAppM ``List.any #[← Meta.mkAppM ``List.zip #[← Meta.mkAppM ``String.toList #[p₁], ← Meta.mkAppM ``String.toList #[p₂]],
                ← Meta.withLocalDeclD `ab (← Meta.mkAppM ``Prod #[mkConst ``Char, mkConst ``Char]) fun ab => do
                  Meta.mkLambdaFVars #[ab] (← Meta.mkAppM ``bne #[← Meta.mkAppM ``Prod.fst #[ab], ← Meta.mkAppM ``Prod.snd #[ab]])])
              (mkConst ``Bool.true)
            if let some hdiff ← tryMkDecideProof diffProp then
              return .inl (← Meta.mkAppM ``Qed.Str.str_append_ne_of_diff_prefix #[hdiff, eqPf'])
          else if s₁.length < s₂.length then
            let rest := Expr.lit (.strVal (String.ofList (s₂.toList.drop s₁.length)))
            let p₂Split ← mkStrAppendExpr p₁ rest
            if let some hp₂ ← tryMkDecideProof (← Meta.mkEq p₂ p₂Split) then
              let hrSplit ← congrStrAppendRight y hp₂
              let hRew ← Meta.mkEqTrans eqPf' hrSplit
              let hAssoc ← Meta.mkEqTrans hRew (← Meta.mkAppOptM ``String.append_assoc #[some p₁, some rest, some y])
              let hNext ← Meta.mkAppM ``Qed.Str.str_append_left_cancel #[hAssoc]
              return ← go x (← mkStrAppendExpr rest y) hNext fuel
          else if s₂.length < s₁.length then
            let rest := Expr.lit (.strVal (String.ofList (s₁.toList.drop s₂.length)))
            let p₁Split ← mkStrAppendExpr p₂ rest
            if let some hp₁ ← tryMkDecideProof (← Meta.mkEq p₁ p₁Split) then
              let hlSplit ← congrStrAppendRight x hp₁
              let hRew ← Meta.mkEqTrans (← Meta.mkEqSymm hlSplit) eqPf'
              let hAssoc ← Meta.mkEqTrans (← Meta.mkEqSymm (← Meta.mkAppOptM ``String.append_assoc #[some p₂, some rest, some x])) hRew
              let hNext ← Meta.mkAppM ``Qed.Str.str_append_left_cancel #[hAssoc]
              return ← go (← mkStrAppendExpr rest x) y hNext fuel
        -- Case 2: Both sides are `a₁ ++ (sep₁ ++ r₁)` and `a₂ ++ (sep₂ ++ r₂)` sharing delimiter head `d`
        if let (some (sep₁, r₁), some (sep₂, r₂)) := (extractStrAppend? x, extractStrAppend? y) then
          if let (some s₁, some s₂) := (extractStrLit? sep₁, extractStrLit? sep₂) then
            if let (d₁ :: _, d₂ :: _) := (s₁.toList, s₂.toList) then
              if d₁ == d₂ then
                if let some h₁ ← proveCharNotMem? d₁ p₁ then
                  if let some h₂ ← proveCharNotMem? d₁ p₂ then
                    let splitOnSep (sepExpr rhs₁ rhs₂ eqTerm : Expr) : MetaM (Option (Sum Expr (Array Expr))) := do
                      let headEqTy ← Meta.mkEq (← Meta.mkAppM ``List.head? #[← Meta.mkAppM ``String.toList #[sepExpr]]) (mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Char) (toExpr d₁))
                      let some hsep ← tryMkDecideProof headEqTy | return none
                      let pairPf ← Meta.mkAppOptM ``Qed.Str.str_split_sep_inj #[some sepExpr, some p₁, some p₂, some rhs₁, some rhs₂, some (toExpr d₁), some hsep, some h₁, some h₂, some eqTerm]
                      match ← go p₁ p₂ (← Meta.mkAppM ``And.left #[pairPf]) fuel with
                      | .inl f => return some (.inl f)
                      | .inr fsL =>
                          match ← go rhs₁ rhs₂ (← Meta.mkAppM ``And.right #[pairPf]) fuel with
                          | .inl f => return some (.inl f)
                          | .inr fsR => return some (.inr (fsL ++ fsR))
                    if s₁ == s₂ then
                      if let some res ← splitOnSep sep₁ r₁ r₂ eqPf' then return res
                    else
                      -- Split differing separators with same first char `d₁` on single-char `d₁` in O(1)
                      let dStr := Expr.lit (.strVal (String.singleton d₁))
                      let tail₁ := Expr.lit (.strVal (String.ofList (s₁.toList.drop 1)))
                      let tail₂ := Expr.lit (.strVal (String.ofList (s₂.toList.drop 1)))
                      let mkSplitSep (a sep tail r : Expr) : MetaM (Option (Expr × Expr)) := do
                        let some hSep ← tryMkDecideProof (← Meta.mkEq sep (← mkStrAppendExpr dStr tail)) | return none
                        let h1 ← congrStrAppendRight r hSep
                        let h2 ← Meta.mkAppOptM ``String.append_assoc #[some dStr, some tail, some r]
                        return some (← mkStrAppendExpr tail r, ← congrStrAppendLeft a (← Meta.mkEqTrans h1 h2))
                      if let (some (newR₁, pL), some (newR₂, pR)) := (← mkSplitSep p₁ sep₁ tail₁ r₁, ← mkSplitSep p₂ sep₂ tail₂ r₂) then
                        let eqSplit ← Meta.mkEqTrans (← Meta.mkEqSymm pL) (← Meta.mkEqTrans eqPf' pR)
                        if let some res ← splitOnSep dStr newR₁ newR₂ eqSplit then return res
        -- Case 3: Identical right suffix `a₁ ++ s = a₂ ++ s`
        if x == y then
          let hNext ← Meta.mkAppM ``Qed.Str.str_append_right_cancel #[eqPf']
          return ← go p₁ p₂ hNext fuel
      -- Case 4: Atomic segment injectivity
      if let (some _, some _) := (extractNatToString? l, extractNatToString? r) then
        return .inr #[← Meta.mkAppM ``Qed.Str.nat_toString_injective #[eqPf']]
      if let (some _, some _) := (extractIntToString? l, extractIntToString? r) then
        return .inr #[← Meta.mkAppM ``Qed.Str.int_toString_injective #[eqPf']]
      if let (some s₁, some s₂) := (extractStrLit? l, extractStrLit? r) then
        if s₁ != s₂ then
          if let some hne ← tryMkDecideProof (← Meta.mkAppM ``Ne #[l, r]) then
            return .inl (mkApp hne eqPf')
      return .inr #[eqPf']
  go lInit rInit pfInit fuel0

/-- Run the O(segments) string equality decomposition pass ONLY if the goal has a `String = String` hyp. -/
@[noinline]
private def decomposeStringEqs (g0 : MVarId) : MetaM (Option MVarId) := do
  let hasStrEq ← g0.withContext do
    for d in (← getLCtx) do
      if !d.isImplementationDetail && !d.isLet then
        if let some (ty, _, _) := (← instantiateMVars d.type).consumeMData.eq? then
          if ty.consumeMData.isConstOf ``String then return true
    return false
  if !hasStrEq then return some g0
  -- Lightly normalize non-String-equality guard hypotheses so `env ∈ [...]` and `all` are direct.
  let guardFvs ← g0.withContext do
    let mut out : Array FVarId := #[]
    for d in (← getLCtx) do
      if !d.isImplementationDetail && !d.isLet then
        let ty ← instantiateMVars d.type
        let isStrEq := match ty.consumeMData.eq? with
          | some (eqTy, _, _) => eqTy.consumeMData.isConstOf ``String
          | none => false
        if !isStrEq then
          if ← isPropSafe ty then out := out.push d.fvarId
    return out
  let g1 ← if guardFvs.isEmpty then pure g0 else do
    let (guardCtx, _) ← mkCachedSimpCtx "strGuardNorm" strGuardNormNames { zetaDelta := false }
    match ← simpGoalOnly g0 guardCtx #[] guardFvs (simplifyTarget := false) with
    | none => return none
    | some g' => pure (← splitAndHypsGoal g' false 32).1
  let strEqs ← g1.withContext do
    let mut out : Array (Expr × Expr × Expr) := #[]
    for d in (← getLCtx) do
      if !d.isImplementationDetail && !d.isLet then
        if let some (ty, lhs, rhs) := (← instantiateMVars d.type).consumeMData.eq? then
          if ty.consumeMData.isConstOf ``String then out := out.push (lhs, rhs, d.toExpr)
    return out
  let mut newFacts : Array Expr := #[]
  for (lhs, rhs, pf) in strEqs do
    match ← g1.withContext (collectStringEqFacts lhs rhs pf) with
    | .inl falsePf =>
        let tgt ← g1.withContext (instantiateMVars (← g1.getType))
        g1.assign (← g1.withContext (Meta.mkAppOptM ``False.elim #[some tgt, some falsePf]))
        return none
    | .inr facts =>
        newFacts := newFacts ++ facts
  if newFacts.isEmpty then return some g1
  let (g2, _) ← assertFacts g1 "_qedStr" newFacts
  return some g2

private def extractStrLitListAux (e : Expr) : Nat → Option (List String)
  | 0 => none
  | fuel + 1 =>
      let e := e.consumeMData
      if e.isAppOfArity ``List.nil 1 then some []
      else if e.isAppOfArity ``List.cons 3 then
        match extractStrLit? e.getAppArgs[1]!, extractStrLitListAux e.getAppArgs[2]! fuel with
        | some s, some rest => some (s :: rest)
        | _, _ => none
      else if e.isAppOfArity ``List.toArray 2 || e.isAppOfArity ``Array.mk 2 then
        extractStrLitListAux e.getAppArgs[1]! fuel
      else if e.isAppOfArity ``Qed.Lang.QedSeqLit.ofList 4 then
        extractStrLitListAux e.getAppArgs[3]! fuel
      else none

private def extractStrLitList? (e : Expr) : Option (List String) := extractStrLitListAux e 128

/-- For concrete string membership guards `s ∈ ["a", "bb", ...]`, assert `lo ≤ s.length ∧ s.length ≤ hi`
    in O(1) branches (no case split on `s`) whenever the target mentions `String.length`. -/
@[noinline]
private def assertStrMemLenBounds (g0 : MVarId) : MetaM MVarId := do
  let tgtHasLen := (← g0.withContext (instantiateMVars (← g0.getType))).getUsedConstants.contains ``String.length
  if !tgtHasLen then return g0
  let facts ← g0.withContext do
    let mut out : Array Expr := #[]
    for d in (← getLCtx) do
      if !d.isImplementationDetail && !d.isLet then
        let dty := (← instantiateMVars d.type).consumeMData
        if let some (_, coll, isArr) := extractStrMemColl? dty then
          if let some (s0 :: ss) := extractStrLitList? coll then
            let lo := ss.foldl (fun m s => min m s.length) s0.length
            let hi := ss.foldl (fun m s => max m s.length) s0.length
            let listExpr ← if isArr then Meta.mkAppM ``Array.toList #[coll] else pure coll
            let checkLam ← Meta.withLocalDeclD `x (mkConst ``String) fun x => do
              let lenX ← Meta.mkAppM ``String.length #[x]
              let loProp ← Meta.mkAppM ``LE.le #[mkNatLit lo, lenX]
              let hiProp ← Meta.mkAppM ``LE.le #[lenX, mkNatLit hi]
              let conj ← Meta.mkAppM ``And #[loProp, hiProp]
              let decInst ← Meta.synthInstance (mkApp (mkConst ``Decidable) conj)
              let body := mkApp2 (mkConst ``Decidable.decide) conj decInst
              Meta.mkLambdaFVars #[x] body
            let allProp ← Meta.mkEq (← Meta.mkAppM ``List.all #[listExpr, checkLam]) (mkConst ``Bool.true)
            if let some hall ← tryMkDecideProof allProp then
              let lem := if isArr then ``Qed.Str.str_length_bounds_of_mem_array else ``Qed.Str.str_length_bounds_of_mem_list
              out := out.push (← Meta.mkAppM lem #[d.toExpr, hall])
    return out
  if facts.isEmpty then return g0
  let (g1, _) ← assertFacts g0 "_qedLen" facts
  return (← splitAndHypsGoal g1 false 16).1

private def goalHasStrRepr (g : MVarId) : MetaM Bool := do
  let cs ← collectGoalConsts g true
  return cs.contains ``ToString.toString || cs.contains ``Nat.repr || cs.contains ``Int.repr || cs.contains ``Nat.toDigits

/-- Close a `s.all p = true` or `s.toList.all p = true` subgoal in O(segments). -/
@[noinline]
private def tryCloseStringAllGoal (g0 : MVarId) : TacticM Bool := do
  let tgt := (← g0.withContext (instantiateMVars (← g0.getType))).consumeMData
  if (extractStrAll? tgt).isNone then return false
  let saved ← saveState
  let (allCtx, _) ← mkCachedSimpCtx "strAllNorm" strAllNormNames { zetaDelta := false }
  let some g1 ← simpGoalOnly g0 allCtx | return true
  let subgoals ← splitGoalAnds g1
  for sg in subgoals do
    if ← tryCloseBasic sg (reducibleOnly := true) then continue
    let sTgt := (← sg.withContext (instantiateMVars (← sg.getType))).consumeMData
    let some (seg, p, true) := extractStrAll? sTgt | restoreState saved; return false
    let closed ← sg.withContext do
      let closeAlphabetAll (chars : String) (lem : Name) (arg : Expr) : MetaM Bool := do
        let digProp ← Meta.mkEq (← Meta.mkAppM ``List.all #[← Meta.mkAppM ``String.toList #[Expr.lit (.strVal chars)], p]) (mkConst ``Bool.true)
        let some hp ← tryMkDecideProof digProp | return false
        sg.assign (← Meta.mkAppM lem #[hp, arg]); return true
      -- 1. `toString (n : Nat)` / `toString (i : Int)`
      if let some n := extractNatToString? seg then
        if ← closeAlphabetAll "0123456789" ``Qed.Str.nat_toString_all n then return true
      if let some i := extractIntToString? seg then
        if ← closeAlphabetAll "-0123456789" ``Qed.Str.int_toString_all i then return true
      -- 3. Local hypotheses on `seg`: `seg ∈ xs` or `seg.all p' = true`
      for d in (← getLCtx) do
        if !d.isImplementationDetail && !d.isLet then
          let dty := (← instantiateMVars d.type).consumeMData
          if let some (elem, coll, isArr) := extractStrMemColl? dty then
            if ← isDefEqFast elem seg then
              let listExpr ← if isArr then Meta.mkAppM ``Array.toList #[coll] else pure coll
              let checkLam ← Meta.withLocalDeclD `x (mkConst ``String) fun x => do
                Meta.mkLambdaFVars #[x] (← Meta.mkAppM ``List.all #[← Meta.mkAppM ``String.toList #[x], p])
              let allProp ← Meta.mkEq (← Meta.mkAppM ``List.all #[listExpr, checkLam]) (mkConst ``Bool.true)
              if let some hall ← tryMkDecideProof allProp then
                let lem := if isArr then ``Qed.Str.str_all_of_mem_array else ``Qed.Str.str_all_of_mem_list
                sg.assign (← Meta.mkAppM lem #[d.toExpr, hall]); return true
          if let some (s', p', isToList) := extractStrAll? dty then
            if ← isDefEqFast s' seg then
              let hList ← if isToList then pure d.toExpr else do
                let eqTrueLam ← Meta.withLocalDeclD `b (mkConst ``Bool) fun b => do
                  Meta.mkLambdaFVars #[b] (← Meta.mkEq b (mkConst ``Bool.true))
                Meta.mkAppM ``Eq.mp #[← Meta.mkAppM ``congrArg #[eqTrueLam, ← Meta.mkAppM ``String.all_bool_eq #[p', s']], d.toExpr]
              if ← isDefEqFast p' p then
                sg.assign hList; return true
              let impTy ← Meta.withLocalDeclD `c (mkConst ``Char) fun c => do
                let lhs ← Meta.mkEq (p'.beta #[c]) (mkConst ``Bool.true)
                let rhs ← Meta.mkEq (p.beta #[c]) (mkConst ``Bool.true)
                Meta.mkForallFVars #[c] (Expr.forallE `_h lhs rhs .default)
              let mImp ← if impTy.hasFVar then Meta.mkFreshExprSyntheticOpaqueMVar impTy
                         else Meta.withLCtx {} {} (Meta.mkFreshExprSyntheticOpaqueMVar impTy)
              let savedGoals ← getGoals; setGoals [mImp.mvarId!]
              let okImp ← tryTac (requireClosed := true) `(tactic| (
                intro _c _hc
                try dsimp only at _hc ⊢
                try simp only [Qed.Lang.QedVal.val_id, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at _hc ⊢
                first
                | grind
                | (try simp only [Char.le_def, Char.lt_def, UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt, Char.ext_iff, ← UInt32.toNat_inj] at _hc ⊢
                   try simp only [Char.toNat] at _hc ⊢
                   first | omega | grind)))
              setGoals savedGoals
              if okImp then
                sg.assign (← Meta.mkAppM ``Qed.Str.list_all_mono #[hList, ← instantiateMVars mImp]); return true
      return false
    unless closed do restoreState saved; return false
  return true

/-- Try closing a goal by splitting top-level `And`s and applying fast closers (including O(S) string `all`). -/
private def tryCloseConjuncts (g0 : MVarId) : TacticM (List MVarId) := do
  let subgoals ← splitGoalAnds g0
  let mut rem : List MVarId := []
  for sg in subgoals do
    if ← tryCloseBasic sg (reducibleOnly := true) then continue
    if ← tryCloseStringAllGoal sg then continue
    rem := sg :: rem
  return rem.reverse

/-- If `g` has an outer `match` / `if let` in the target (like `if let some id := f args then P id else True`),
    split it BEFORE unfolding `f` so `f args = some id` lands in a hypothesis and gets linearly split! -/
private def preSplitOuterMatch (g0 : MVarId) : MetaM (List MVarId) := do
  let tgt := (← g0.withContext (instantiateMVars (← g0.getType))).consumeMData
  let isMatch := match tgt.getAppFn with | .const c _ => c.toString.contains ".match_" | _ => false
  if !isMatch then return [g0]
  match ← trySplitTarget g0 with
  | none => return [g0]
  | some kids =>
      let mut live : List MVarId := []
      for sg in kids do
        if let some sg' ← tryPruneBranch sg none then live := sg' :: live
      return live.reverse

/-- Unfold `fnConst` in every hypothesis mentioning it (one by one, tracking fresh names) and in target,
    splitting incrementally with immediate dead-branch pruning. -/
private def unfoldAndLinearSplitFn (g0 : MVarId) (fnConst : Name) (skipName? : Option Name := none) :
    MetaM (List MVarId) := do
  let initGoals ← preSplitOuterMatch g0
  let rec splitHyps (work done : List MVarId) : Nat → MetaM (List MVarId)
    | 0 => return done.reverse ++ work
    | fuel + 1 =>
        match work with
        | [] => return done.reverse
        | g :: rest => do
            let nextHyp? : Option (Name × Option Name) ← g.withContext do
              for d in (← getLCtx) do
                if !d.isImplementationDetail && !d.isLet && skipName? != some d.userName then
                  let ty ← instantiateMVars d.type
                  if ty.getUsedConstants.contains fnConst then
                    -- If `heq : fnConst ... = some v` (from `if let some v := result`), substitute `v` after splitting!
                    let substNm? ← match ty.consumeMData.eq? with
                      | some (_, lhs, rhs) =>
                          let l := lhs.consumeMData; let r := rhs.consumeMData
                          if r.isAppOfArity ``Option.some 2 && r.getAppArgs[1]!.consumeMData.isFVar then
                            some <$> r.getAppArgs[1]!.consumeMData.fvarId!.getUserName
                          else if l.isAppOfArity ``Option.some 2 && l.getAppArgs[1]!.consumeMData.isFVar then
                            some <$> l.getAppArgs[1]!.consumeMData.fvarId!.getUserName
                          else pure none
                      | none => pure none
                    return some (d.userName, substNm?)
              return none
            match nextHyp? with
            | none => splitHyps rest (g :: done) fuel
            | some (hNm, substNm?) =>
                match ← unfoldConstInFVarName g fnConst hNm with
                | none => splitHyps rest done fuel
                | some gU =>
                    let kids ← linearSplitHyp gU hNm substNm?
                    splitHyps (kids ++ rest) done fuel
  let afterHyps ← splitHyps initGoals [] 8
  let mut out : List MVarId := []
  for g in afterHyps do
    let tgtHasFn := (← g.withContext (instantiateMVars (← g.getType))).getUsedConstants.contains fnConst
    if tgtHasFn then
      match ← unfoldConstInTarget g fnConst with
      | none => pure ()
      | some gU => out := out ++ (← linearSplitTarget gU)
    else out := out ++ [g]
  return out

private def runProveFnGoal (fnId : Ident) (isBlind : Bool) : TacticM Unit := do
  let fnConst? : Option Name ← try some <$> resolveGlobalConstNoOverload fnId catch _ => pure none
  -- Phase 0: Shared `result` + incremental O(k) split-and-prune + O(S) string decomposition.
  let g0 :: rest0 ← getGoals | return
  let mut phase0Goals : List MVarId := []
  let shared? ← if isBlind then pure none else shareLetResult? g0
  match shared?, fnConst? with
  | some (resFv, hResFv, g1), some fnConst =>
      let (resNm, hResNm) ← g1.withContext do return ((← resFv.getUserName), (← hResFv.getUserName))
      let (_, g2) ← g1.intros
      let g3 := (← splitAndHypsGoal g2 false 32).1
      let step1 ← match ← unfoldConstInFVarName g3 fnConst hResNm with
        | none => pure []
        | some gU => linearSplitHyp gU hResNm (some resNm)
      let mut step2 : List MVarId := []
      for g in step1 do
        step2 := step2 ++ (← unfoldAndLinearSplitFn g fnConst (some hResNm))
      for g in step2 do
        match ← decomposeStringEqs g with
        | none => pure ()
        | some g' => phase0Goals := phase0Goals ++ (← tryCloseConjuncts g')
      setGoals (phase0Goals ++ rest0)
  | _, _ =>
      if isBlind then evalTactic (← `(tactic| intros))
      else
        discard <| tryTac `(tactic| dsimp only)
        discard <| tryTac `(tactic| intros)
      if let g1 :: rest1 ← getGoals then
        let g2 := (← splitAndHypsGoal g1 false 32).1
        match fnConst? with
        | some fnConst =>
            let afterTgt ← unfoldAndLinearSplitFn g2 fnConst none
            let mut rem : List MVarId := []
            for cg in afterTgt do
              match ← decomposeStringEqs cg with
              | none => pure ()
              | some cg' => rem := rem ++ (← tryCloseConjuncts cg')
            setGoals (rem ++ rest1)
        | none =>
            setGoals (g2 :: rest1)
            discard <| tryTac `(tactic| unfold $fnId:ident)
            discard <| tryTac `(tactic| simp only [$fnId:ident])
            discard <| tryTac `(tactic| dsimp only at *)
  if (← getGoals).isEmpty then return
  -- Phase 1: General helper unfolding + bounded contract solver on remaining goals.
  let simpL ← namesToSimpLemmas fnContractSimpNames
  let (fnSimpCtx, fnSimpSP) ← mkCachedSimpCtx "fnContract" fnContractSimpNames { zetaDelta := false } #[``fnReduceStrLen]
  forEachGoal fun g => do
    setGoals [g]
    if ← tryCloseBasic g (reducibleOnly := true) then setGoals []; return
    runUnfoldPresent #[]
    if let g1 :: rest1 ← getGoals then
      match ← simpGoalAllHyps g1 fnSimpCtx fnSimpSP with
      | none => setGoals rest1
      | some g2 =>
          let g3 := (← splitAndHypsGoal g2 false 32).1
          setGoals (g3 :: rest1)
    if (← getGoals).isEmpty then return
    let mut afterStr : List MVarId := []
    for sg in (← getGoals) do
      match ← decomposeStringEqs sg with
      | none => pure ()
      | some sg' =>
          let sg'' ← assertStrMemLenBounds sg'
          afterStr := afterStr ++ (← tryCloseConjuncts sg'')
    setGoals afterStr
    if (← getGoals).isEmpty then return
    -- Avoid default-transparency `assumption`/`contradiction`/`rfl` on goals with `toString`/`Nat.repr`
    -- (unfolding `Nat.toDigits` causes `whnf` timeouts on genuine failures).
    let mut finalRem : List MVarId := []
    for sg in (← getGoals) do
      if ← goalHasStrRepr sg then
        let branches ← linearSplitTarget sg
        for bg in branches do
          if ← tryCloseContradiction bg then continue
          let bg1? ← simpGoalAllHyps bg fnSimpCtx fnSimpSP
          let some bg1 := bg1? | continue
          let bg2 := (← splitAndHypsGoal bg1 false 32).1
          let some bg3 ← decomposeStringEqs bg2 | continue
          let bg4 ← assertStrMemLenBounds bg3
          for cg in (← tryCloseConjuncts bg4) do
            setGoals [cg]
            unless ← tryTac (requireClosed := true) `(tactic| first | qedCloseGround | (with_reducible assumption) | (with_reducible rfl) | decide | omega) do
              finalRem := finalRem ++ (← getGoals)
      else
        setGoals [sg]
        discard <| tryTac `(tactic| simp_all only [$[$simpL],*])
        if (← getGoals).isEmpty then continue
        let mut afterSplit : List MVarId := []
        for s in (← getGoals) do afterSplit := afterSplit ++ (← linearSplitTarget s)
        setGoals afterSplit
        forEachGoal (closeSplitBranch #[] false (some simpL) 3)
        if !(← getGoals).isEmpty then
          forEachGoal fun s => do
            if ← tryCloseStringAllGoal s then setGoals []; return
            if ← tryCloseBasic s (reducibleOnly := true) then setGoals []; return
            discard <| tryTac `(tactic| first | qedCloseGround | decide | omega)
        finalRem := finalRem ++ (← getGoals)
    setGoals finalRem

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
  if ← tryTac (requireClosed := true) `(tactic| first | qedCloseGround | rfl | decide | omega) then return
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
          first | contradiction | qedCloseGround | rfl | decide))
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
      if ← tryTac (requireClosed := true) `(tactic| first | qedCloseGround | rfl | decide) then return
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
    (lowerVal : Array String → Syntax → CommandElabM Term) (lowerGuard : Array String → Syntax → CommandElabM Term)
    (boundLocals : Array String) (muts : Array Ident) (loopMuts? : Option (Array Ident)) (depth : Nat) (stmts : List Syntax) : CommandElabM Term := do
  let recSelf (loc' : Array String := boundLocals) (m' : Array Ident := muts) (lm' : Option (Array Ident) := loopMuts?) (d' : Nat := depth) (ss : List Syntax) :=
    lowerPureFnStmtsAux fnDesc lowerVal lowerGuard loc' m' lm' d' ss
  let dropShadowed (names : Array Name) (ms : Array Ident) : Array Ident :=
    ms.filter fun m => !names.contains m.getId.eraseMacroScopes
  let addLocs (names : Array Name) : Array String := boundLocals ++ names.map (·.toString)
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
        let v ← lowerVal boundLocals ((s.getArg 1).getArg 0)
        match loopMuts? with
        | none => pure v
        | some lm => let stPack ← liftMacroM (mkMutPack lm.toList); `(Qed.QedLoopStep.ret $stPack $v)
      else if sk == ``qedStmtLetMut then
        let lId : Ident := ⟨s.getArg 2⟩; let nm := lId.getId.eraseMacroScopes
        if muts.any (·.getId.eraseMacroScopes == nm) then
          throwErrorAt lId s!"mutable variable `{nm}` is already declared in this scope; update it with `{nm} = ...`"
        let rhsT ← lowerVal boundLocals (s.getArg 5)
        let cont ← recSelf (loc' := boundLocals.push nm.toString) (m' := muts.push lId) (ss := rest)
        if (s.getArg 3).getNumArgs == 2 then
          let lTy ← liftMacroM (return (← lowerQedType ((s.getArg 3).getArg 1) false).1)
          `(let $lId:ident : $lTy := $rhsT; $cont)
        else `(let $lId:ident := $rhsT; $cont)
      else if let some act := tryMatchLocalMut? muts s then
        if sk == ``qedStmtAssign && s.getNumArgs > 3 && (s.getArg 3).getNumArgs > 0 then
          throwErrorAt ((s.getArg 3).getArg 0) s!"`predict` is not supported in pure `{fnDesc}`"
        let rhsT ← lowerVal boundLocals act.rhsSyntax
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
        let iterTerm ← lowerVal boundLocals iterStx
        let mutated := collectMutatedIds bodyStmts
        let usedMuts := muts.filter fun m => mutated.contains m.getId.eraseMacroScopes
        let initSt ← liftMacroM (mkMutPack usedMuts.toList)
        let stParam := mkIdent (Name.mkSimple s!"_qedSt{depth}")
        let resSt := mkIdent (Name.mkSimple s!"_qedLoopSt{depth}")
        let resRet := mkIdent (Name.mkSimple s!"_qedLoopRet{depth}")
        let retValId := mkIdent (Name.mkSimple s!"_qedRet{depth}")
        let bodyLocs := if bStx.isIdent then boundLocals.push bStx.getId.eraseMacroScopes.toString else boundLocals
        let bodyInner ← recSelf (loc' := bodyLocs) (lm' := some usedMuts) (d' := depth + 1) (ss := bodyStmts.toList)
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
        if rest.isEmpty && loopMuts?.isNone then lowerVal boundLocals (s.getArg 0)
        else throwErrorAt s s!"unexpected bare expression statement in pure `{fnDesc}`; bind it with `let _ = ...` or return it"
      else if sk == ``qedStmtLet then
        if (s.getArg 5).getNumArgs > 0 then throwErrorAt ((s.getArg 5).getArg 0) s!"`predict`/`catch` clauses are not supported in pure `{fnDesc}`"
        let rhsT ← lowerVal boundLocals (s.getArg 4)
        let bStx := s.getArg 1
        let bIds := collectLetBinderIds bStx
        let cont ← recSelf (loc' := addLocs bIds) (m' := dropShadowed bIds muts) (ss := rest)
        let ty? ← if (s.getArg 2).getNumArgs == 2 then some <$> liftMacroM (return (← lowerQedType ((s.getArg 2).getArg 1) false).1) else pure none
        mkLetBindTerm bStx ty? rhsT cont
      else if sk == ``qedStmtLetElse then
        let pat ← liftMacroM (lowerQedPat (s.getArg 1))
        let scrut ← lowerVal boundLocals (s.getArg 3)
        let elseStmts := extractLetElseStmts s
        let elseT ← recSelf (ss := elseStmts.toList)
        let patIds := collectQedPatIds (s.getArg 1)
        let thenT ← recSelf (loc' := addLocs patIds) (m' := dropShadowed patIds muts) (ss := rest)
        `(match $(mkIdent `_qedLetElse):ident : $scrut:term with | $pat:term => $thenT | _ => $elseT)
      else if sk == ``qedStmtIf then
        let cond ← lowerGuard boundLocals (s.getArg 1)
        let thenT ← recSelf (ss := (suiteStmts (s.getArg 3)).toList ++ rest)
        let elseStmts := (desugarElifs (s.getArg 4).getArgs (s.getArg 5)).getD #[]
        let elseT ← recSelf (ss := elseStmts.toList ++ rest)
        `(if $(mkIdent `_qedIf):ident : $cond then $thenT else $elseT)
      else if sk == ``qedStmtIfLet then
        let pat ← liftMacroM (lowerQedPat (s.getArg 2))
        let scrut ← lowerVal boundLocals (s.getArg 4)
        let patIds := collectQedPatIds (s.getArg 2)
        let thenT ← recSelf (loc' := addLocs patIds) (m' := dropShadowed patIds muts) (ss := (suiteStmts (s.getArg 6)).toList ++ rest)
        let elseStmts := (extractElseSuite (s.getArg 7)).getD #[]
        let elseT ← recSelf (ss := elseStmts.toList ++ rest)
        `(match $(mkIdent `_qedIfLet):ident : $scrut:term with | $pat:term => $thenT | _ => $elseT)
      else if sk == ``qedStmtMatch then
        let scruts ← (s.getArg 1).getSepArgs.mapM (lowerVal boundLocals)
        let alts ← (s.getArg 3).getArgs.mapM fun alt => do
          let altTerms ← liftMacroM (lowerCasePatAlts (alt.getArg 1))
          let patIds := collectCasePatIds (extractCasePatAlts (alt.getArg 1))
          let body ← recSelf (loc' := addLocs patIds) (m' := dropShadowed patIds muts) (ss := (suiteStmts (alt.getArg 3)).toList ++ rest)
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
    (lowerGuard : Syntax → CommandElabM Term := fun s => liftMacroM (lowerSimpleQedExpr .propGuard s))
    (lowerWithLocals? : Option (Array String → ExprMode → Syntax → CommandElabM Term) := none) : CommandElabM Term :=
  match lowerWithLocals? with
  | some f => lowerPureFnStmtsAux fnDesc (fun ls s => f ls .val s) (fun ls s => f ls .propGuard s) #[] #[] none 0 stmts
  | none   => lowerPureFnStmtsAux fnDesc (fun _ s => lowerVal s) (fun _ s => lowerGuard s) #[] #[] none 0 stmts

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
  let lowerProp (s : Syntax) : CommandElabM Term :=
    liftMacroM (lowerSimpleQedExpr .propInv s (allowOptElse := true) (optElseFallback := `(True)))
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
