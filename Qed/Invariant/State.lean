import Qed.Verify.Core

namespace Qed
open Lean Elab Tactic Qed.Verify.Core

theorem str_append_congr_left (a : String) {x y : String} (h : x = y) : a ++ x = a ++ y := congrArg (a ++ ·) h
theorem str_append_congr_right (b : String) {x y : String} (h : x = y) : x ++ b = y ++ b := congrArg (· ++ b) h
theorem toString_qedVal_eq {α : Type} [ToString α] (x : α) : toString (Qed.Lang.QedVal.val x) = toString x := rfl
theorem str_all_toList_of_all {s : String} {p : Char → Bool} (h : s.all p = true) : s.toList.all p = true := String.all_bool_eq ▸ h
abbrev strDiffPrefix (a b : String) : Bool := (a.toList.zip b.toList).any fun ab => ab.1 != ab.2
abbrev strMemLenCheck (lo hi : Nat) (x : String) : Bool := decide (lo ≤ x.length ∧ x.length ≤ hi)
abbrev strNotContainsChar (d : Char) (x : String) : Bool := !x.toList.contains d

private structure ParsedFnEnsures where (ref : Syntax) (guards preds : Array Syntax) (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
private structure ParsedFnBlindTo where (ref : Syntax) (guards : Array Syntax) (targets : Array ParsedBlindTarget) (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
private structure ParsedFnExample where (ref : Syntax) (name : Ident) (params wheres preds : Array Syntax) (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
private structure ParsedFnContracts where
  (requires : Array Syntax := #[]) (ensures : Array ParsedFnEnsures := #[]) (blinds : Array ParsedFnBlindTo := #[]) (examples : Array ParsedFnExample := #[])

syntax qedProveCase := ident,+ " => " Lean.Parser.Tactic.tacticSeq
syntax qedLoopProveArg := "(" Lean.Parser.Tactic.tacticSeq ")"
syntax "qedDischargeInit " "[" term,* "]" term:max ident term:max : tactic
syntax "qedDischargePreserved " "[" term,* "]" term:max ident term:max (" from " term)? (" _qedProve " "[" qedProveCase,* "]")? : tactic
syntax "qedProveFnEnsures " ident ident (" _qedLoopProve " "[" qedLoopProveArg,* "]")? : tactic
syntax "qedProveFnLoopInvs " ident ident (" _qedLoopProve " "[" qedLoopProveArg,* "]")? : tactic
syntax "qedProveBlindTo " ident ident str : tactic
syntax "qedProveFnExample " ("ground ")? ident ident : tactic

private def relevantOptResLemmas (env : Environment) (cs : Std.HashSet Name) : Array Name :=
  collectTriggered env cs #[] #[
    (#[`Qed.Cached.all, `Qed.Resource.all], #[`Qed.Cached.all, `Qed.Resource.all]),
    (#[``Qed.Lang.QedVal.val], #[`Qed.QedVal.val_field, `Qed.QedVal.val_ensured]),
    (#[`Qed.Codec.valid, `Qed.Field, `Qed.Ensured], optCodecSimpNames),
    (#[`Qed.Dict, `Qed.Dict.size, `Qed.Dict.get, `Qed.Dict.set, `Qed.Dict.remove, `Qed.Dict.contains], dictSimpNames)]

private def stripStepPrefix : Name → Name
  | .str `step s => Name.mkSimple s
  | .str p s => let p' := stripStepPrefix p; if p' == .anonymous then Name.mkSimple s else .str p' s
  | n => n

private def runAddFieldFacts : TacticM Unit := do
  let env ← getEnv
  if env.contains `Qed.Field.ok || env.contains `Qed.Ensured.ok || env.contains `Qed.Dict.size_remove_le then
    replaceMainGoal [(← collectAndAssertFacts (← getMainGoal) "_qedFld" { includeFin := false, includeDictRemove := true }).1]

private def impHypSimpNames : Array Name :=
  boolSimpNames ++ boolConstSimpNames ++ valUnwrapBaseNames ++
    #[``reduceCtorEq, ``Option.some.injEq, ``Prod.mk.injEq, ``Qed.Lang.QedMem.mem_array,
      ``Qed.Lang.QedMem.mem_list, ``Qed.Lang.QedMem.mem_string, ``Qed.Lang.QedMemProp.memProp_array,
      ``Qed.Lang.QedMemProp.memProp_list, ``Qed.Lang.QedMemProp.memProp_string,
      ``Array.contains_iff_mem, ``List.contains_iff_mem]

private def mkStrToList (s : Expr) : Expr := mkApp (mkConst ``String.toList) s
private def mkNot (p : Expr) : Expr := mkApp (mkConst ``Not) p
private def mkListAll (ty xs p : Expr) : Expr := mkApp3 (mkConst ``List.all [0]) ty xs p
@[noinline] private def filterMapGoalsM (f : MVarId → MetaM (Option MVarId)) : List MVarId → MetaM (List MVarId)
  | [] => pure [] | g :: r => do match ← f g with | some g' => return g' :: (← filterMapGoalsM f r) | none => filterMapGoalsM f r
private def filterMapGoalsT (f : MVarId → MetaM (Option MVarId)) : TacticM Unit := do setGoals (← filterMapGoalsM f (← getGoals))
@[noinline] private def foldlT {α β : Type} (xs : Array α) (init : β) (f : β → α → TacticM β) : TacticM β :=
  let rec go : Nat → β → TacticM β | 0, acc => pure acc | r + 1, acc => do let i := xs.size - (r + 1); if h : i < xs.size then go r (← f acc xs[i]) else pure acc
  go xs.size init

private def tryCloseContradiction (g : MVarId) : MetaM Bool :=
  tryRestoreM false id (Meta.withTransparency .reducible (g.contradictionCore {}))

@[noinline] private def tryProvePremise (g : MVarId) (p : Expr) : MetaM (Option Expr) := g.withContext do
  tryRestoreM none Option.isSome do
    let mP ← Meta.mkFreshExprSyntheticOpaqueMVar p; let mId := mP.mvarId!
    let closed ← if ← tryCloseBasic mId then pure true else do
      match ← trySimpAll mId (← mkCachedSimpCtx "impHypPremise" impHypSimpNames).1 with
      | none => pure true | some mId' => tryCloseBasic mId'
    if closed then some <$> instantiateMVars mP else return none

@[noinline] private def specializeImpHyps (g0 : MVarId) : MetaM MVarId := do
  let rec rounds (g : MVarId) (seen : Std.HashSet Expr) : Nat → MetaM MVarId
    | 0 => pure g
    | n + 1 => do
        let hyps ← g.withContext <| collectLCtxDecls (includeLet := false) fun d => do
          let .forallE _ p q _ ← instantiateMVars d.type | return none
          if q.hasLooseBVars || seen.contains q then return none
          if ← isPropSafe p then if ← isPropSafe q then return some (d.fvarId, p, q)
          return none
        let (g', seen', added) ← foldlMeta hyps (g, seen, false) fun (cg, sn, add) (hfv, p, q) => do
          if sn.contains q then return (cg, sn, add)
          match ← tryProvePremise cg p with
          | none => return (cg, sn, add)
          | some pfP => return ((← splitAndHypsGoal (← (← cg.assert `_qedMp q (mkApp (mkFVar hfv) pfP)).intro1P).2 true 16).1, sn.insert q, true)
        if added then rounds g' seen' n else pure g'
  rounds g0 {} 4

private def tryCloseWithImp (g : MVarId) : MetaM (Option MVarId) := do
  if ← tryCloseContradiction g then return none
  let g ← specializeImpHyps g
  if ← tryCloseContradiction g then return none else if ← tryCloseBasic g (reducibleOnly := true) then return none else return some g

@[noinline] private def runCloseStateGoal (extra : Array Term) : TacticM Unit := do
  let g0 :: rest ← getGoals | return
  let some g0 ← tryCloseWithImp g0 | setGoals rest; return
  setGoals (g0 :: rest)
  let relNames := let cs := (← collectGoalConsts g0 true); relevantOptResLemmas (← getEnv) cs ++ relevantBoundaryLemmas cs
  let getRelL : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := (· ++ ·) <$> namesToSimpLemmas relNames <*> termsToSimpLemmas extra
  let relL? ← if extra.isEmpty then
      if !relNames.isEmpty then match ← trySimpAll g0 (← mkDynamicSimpCtx relNames) with | none => setGoals rest; return | some g' => setGoals (g' :: rest)
      pure none
    else
      let relL ← getRelL; if !relL.isEmpty then discard <| tryTac (Qed.Lang.runPQTactic `(tactic| simp_all only [$[$relL],*]))
      pure (some relL)
  let g :: rest2 ← getGoals | return
  let some g2 ← tryCloseWithImp g | setGoals rest2; return
  if ← tryCloseNonlinear g2 then setGoals rest2; return
  setGoals (g2 :: rest2)
  let relL ← match relL? with | some l => pure l | none => getRelL
  evalTactic (← Qed.Lang.runPQTactic `(tactic| first | (qedAutoClose; done) | (simp_all [$[$relL],*] <;> qedAutoClose; done) | skip))

@[noinline] private def closeCachedPutGoal (extraL : Array Term) (extraSimpL : Array (TSyntax `Lean.Parser.Tactic.simpLemma))
    (progRef : IO.Ref Bool) (g : MVarId) : TacticM Unit := do
  let tgt ← g.withContext (instantiateMVars (← g.getType))
  if tgt.isAppOfArity ``And 2 && tgt.getUsedConstants.contains `Qed.Cached.all then
    if let some gs ← tryApplyConst g ``And.intro then setGoals gs; progRef.set true
  else if tgt.isAppOfArity `Qed.Cached.all 3 then
    let arg := tgt.getAppArgs[2]!.consumeMData; let isRev := arg.isAppOfArity `Qed.Cached.putRev 5
    if arg.isAppOfArity `Qed.Cached.put 5 || isRev then
      if ← tryRestoreM false id do
          let some [gHall, gHr] ← tryApplyConst g (if isRev then `Qed.Cached.all_putRev else `Qed.Cached.all_put) | return false
          unless ← Meta.withTransparency .reducible gHall.assumptionCore do
            if (← trySimpAll gHall (← mkSimpCtxWithBase)).isSome then return false
          let gHr1 ← match ← tryApplyConst gHr `Qed.Resource.all_stripEnsured_of_imp with
            | some [gh] =>
                let (fvs, gh1) ← gh.introN 2
                match ← simpGoalOnly gh1 (← mkEmptyDsimpCtx) #[] #[fvs[1]!] (simplifyTarget := false) (dsimpOnly := true) with
                | none => setGoals []; return true | some gh2 => pure gh2
            | _ => pure gHr
          setGoals [(← splitAndHypsGoal gHr1 true 16).1]; runUnfoldPresent extraL
          if !extraSimpL.isEmpty then discard <| tryTac (Qed.Lang.runPQTactic `(tactic| simp_all [$[$extraSimpL],*]))
          else let baseCtx ← mkSimpCtxWithBase; filterMapGoalsT (trySimpAll · baseCtx)
          closeAllGoals (tryCloseBasic ·) (← getGoals)
      then progRef.set true; setGoals []

@[noinline] private def runCloseCachedPut (extraL : Array Term) : TacticM Unit := do
  unless (← getEnv).contains `Qed.Cached.all_put do return
  unless ← foldlMeta (← getGoals).toArray false fun ok g => if ok then pure true else return (← g.withContext (instantiateMVars (← g.getType))).getUsedConstants.contains `Qed.Cached.all do return
  let extraSimpL ← termsToSimpLemmas extraL
  let rec go : Nat → TacticM Unit
    | 0 => pure ()
    | n + 1 => do if !(← getGoals).isEmpty then let p ← IO.mkRef false; forEachGoal (closeCachedPutGoal extraL extraSimpL p); if ← p.get then go n
  go 8

private def simpIdentAtAll (t : Term) : TacticM Unit := do
  let t := match t with | `(($p)) => p | p => p
  if t.raw.isIdent then if let some nm ← try some <$> realizeGlobalConstNoOverload t.raw catch _ => pure none then
    let ctx ← mkDynamicSimpCtx #[nm] none (withEqns := false); filterMapGoalsT (simpGoalAllHyps · ctx)

@[noinline] private def runInitPass (usingL : Array Term) (pred initT : Term) : TacticM Unit := do
  simpIdentAtAll pred; let dCtx ← mkEmptyDsimpCtx; filterMapGoalsT (simpGoalAllHyps · dCtx (dsimpOnly := true))
  simpIdentAtAll initT; runUnfoldPresent usingL
  setGoals (← splitTargetsRec 32 (← getGoals) (some dCtx))
  forEachGoal fun _ => try runCloseStateGoal usingL catch _ => pure ()

private def formatTargetName (t : Term) : String :=
  if t.raw.isIdent then toString t.raw.getId else (t.raw.reprint.getD (toString t.raw)).trimAscii.toString

@[noinline] private def throwUnsolvedInvGoals (nm : Ident) (hdr footer : MessageData) : TacticM Unit :=
  Qed.Diag.throwUnsolvedGoals hdr m!"\n\n{footer}" (ref? := some nm) (maxShown? := some 6)
    (formatGoal? := some fun g => g.withContext do
      let tagLabel := Qed.Diag.formatCaseTag (stripStepPrefix (← g.getTag))
      let ty ← instantiateMVars (← g.getType); let tgt ← Qed.Diag.ppQedExpr ty ["m"]; let env ← getEnv
      let present ← (ty.getUsedConstants.filter (qedIsHelper env)).filterM fun n => return (← getProjectionFnInfo? n).isNone
      let involves := if present.isEmpty then "" else s!"\n    (involves helper: {String.intercalate ", " (present.toList.map toString)})"
      return some s!"  • {tagLabel} must satisfy:  {tgt}{involves}")

@[noinline] private def closeSplitBranch (usingL : Array Term) (reducibleOnly : Bool)
    (extraCtx? : Option (Meta.Simp.Context × Meta.Simp.SimprocsArray) := none)
    (hypSplitFuel : Nat := 0) (skipUnfold : Array Name := #[]) (g : MVarId) : TacticM Unit := do
  if ← tryCloseContradiction g then setGoals []; return
  if ← tryCloseBasic g (reducibleOnly := reducibleOnly) then setGoals []; return
  let dCtx ← mkEmptyDsimpCtx
  setGoals (← filterMapGoalsM (simpGoalAllHyps · dCtx (dsimpOnly := true)) (← splitTargetsRec 16 [(← g.intros).2] (some dCtx)))
  forEachGoal fun gSub => do
    if ← tryCloseContradiction gSub then setGoals []; return
    runAddFieldFacts
    if let g1 :: r1 ← getGoals then setGoals ((← splitAndHypsGoal g1 true 16).1 :: r1)
    runUnfoldPresent usingL skipUnfold
    if let some (eCtx, eSP) := extraCtx? then filterMapGoalsT (trySimpAll · eCtx eSP); if (← getGoals).isEmpty then return
    runCloseStateGoal usingL
    if hypSplitFuel > 0 then
      if let gRem :: _ ← getGoals then
        if let some subgoals ← gRem.withContext <| findLCtxDecl? (includeLet := false) fun d => do
          if ← isPropSafe (← instantiateMVars d.type) then trySplitLocalDecl gRem d.fvarId else return none
        then setGoals subgoals; forEachGoal (closeSplitBranch usingL reducibleOnly extraCtx? (hypSplitFuel - 1) skipUnfold)
termination_by hypSplitFuel

@[noinline] private def runPreservedBranchCore (usingL : Array Term) (updNames : Array Name) (ctx dCtx : Meta.Simp.Context) (isFastRecon : Bool) (g : MVarId) : TacticM Unit := do
  match ← trySimpAll g ctx with
  | none => setGoals []; return
  | some g1 =>
      setGoals [g1]
      if ← tryCloseBasic g1 (reducibleOnly := true) then setGoals []; return
      if isFastRecon then
        if ← tryRestoreM false id (do if ← closeAllGoals (tryCloseBasic · (reducibleOnly := true)) (← splitTargetsRec 16 [g1] (some dCtx)) then setGoals []; return true else return false) then return
  runUnfoldPresent usingL updNames; try runCloseCachedPut usingL catch _ => pure ()
  setGoals (← splitTargetsRec 16 (← getGoals) (some dCtx))
  forEachGoal (closeSplitBranch usingL true none 3 updNames)

@[noinline] private def parseProveCases (nm : Ident) (proveCases : Option (Array (TSyntax ``qedProveCase))) :
    TacticM (Std.HashMap Name (Ident × TSyntax ``Lean.Parser.Tactic.tacticSeq) × Array Ident) := do
  let some pcs := proveCases | return ({}, #[])
  foldlT pcs ({}, #[]) fun (m, ids) (pc : TSyntax ``qedProveCase) => match pc with
    | `(qedProveCase| $[$cIds:ident],* => $tacSeq) =>
        foldlT cIds (m, ids) fun (acc, os) (cid : Ident) => do
          let cn := cid.getId.eraseMacroScopes
          if acc.contains cn then throwErrorAt cid s!"duplicate `case {cn}` in `prove:` on invariant `{nm.getId}`"
          return (acc.insert cn (cid, tacSeq), os.push cid)
    | _ => pure (m, ids)

@[noinline] private def runDischargePreserved (usingL : Array Term) (upd : Term) (nm : Ident) (pred : Term)
    (init : Option Term) (proveCases : Option (Array (TSyntax ``qedProveCase))) : TacticM Unit := withFreshHeartbeatsT do
  let updUnfolds ← match upd with
    | `($a:ident) | `(($a:ident).update) | `((($a:ident).update)) | `(($a:ident $_:term*)) => resolveCompUpdateUnfolds a.raw
    | _ => pure #[]
  let updNames := updUnfolds ++ relevantAppLemmas (← getEnv) (← collectGoalConsts (← getMainGoal) true)
  let updCtx ← mkDynamicSimpCtx updNames none (withEqns := false); let dCtx ← mkEmptyDsimpCtx
  let (caseMap, orderedCaseIds) ← parseProveCases nm proveCases
  let seenCasesRef ← IO.mkRef ({} : Std.HashSet Name); let allCtorsRef ← IO.mkRef (#[] : Array Name)
  let step : TacticM Unit := do
    let (_, g1) ← (← getMainGoal).introN 3 [`m, `msg, `h]
    setGoals [g1]; simpIdentAtAll pred; filterMapGoalsT (simpGoalAllHyps · dCtx (dsimpOnly := true))
    if (← getGoals).isEmpty then return
    let fastUpdCtx? ← buildFastReconCtx? updNames (updUnfolds.filter (·.getString! == "_reconcileHoisted"))
    evalTactic (← Qed.Lang.runPQTactic `(tactic| cases $(mkIdent `msg):ident))
    forEachGoal fun g => withFreshHeartbeatsT do
      let ctorTag := stripStepPrefix (← g.getTag); allCtorsRef.modify (Qed.Lang.pushUnique · ctorTag)
      if let some (_, tacSeq) := caseMap[ctorTag]? then
        seenCasesRef.modify (·.insert ctorTag)
        let runUser (ctx : Meta.Simp.Context) : TacticM Bool := do
          let some g1 ← simpGoalOnly g ctx | setGoals []; return true
          let some g2 ← simpGoalAllHyps g1 dCtx (dsimpOnly := true) | setGoals []; return true
          setGoals [g2]; evalTactic tacSeq; return (← getGoals).isEmpty
        if let some fCtx := fastUpdCtx? then if ← tryRestoreM false id (runUser fCtx) then return
        discard <| runUser updCtx; return
      if let some fCtx := fastUpdCtx? then
        if ← tryRestoreM false id (do runPreservedBranchCore usingL updNames fCtx dCtx true g; return (← getGoals).isEmpty) then return
      runPreservedBranchCore usingL updNames updCtx dCtx false g
  match init with
  | some initT =>
      let [gInit, gStep] ← (← getMainGoal).apply (mkConst ``And.intro) | throwError "internal error splitting invariant init/step goals"
      gInit.setTag `init; gStep.setTag `step
      setGoals [gInit]; withFreshHeartbeatsT (runInitPass usingL pred initT); let remInit ← getUnsolvedGoals
      setGoals [gStep]; step; setGoals (remInit ++ (← getUnsolvedGoals))
  | none => step
  let (seenCases, allCtors) := (← seenCasesRef.get, ← allCtorsRef.get)
  orderedCaseIds.toList.forM fun cid => do
    let cn := cid.getId.eraseMacroScopes
    unless seenCases.contains cn do
      throwErrorAt cid s!"unknown action/message `{cn}` in `prove:` on invariant `{nm.getId}` (valid cases: {String.intercalate ", " (allCtors.toList.map toString)})"
  throwUnsolvedInvGoals nm m!"Invariant `{nm.getId}` failed in `{formatTargetName upd}`:"
    m!"Hint: Guard the failing branch with `if ...:`, fix the update, or weaken the invariant.\n      If the rule does hold, add `using [lemma]`, a per-action `prove:` block, or a manual `:= by` proof."

elab_rules : tactic
  | `(tactic| qedDischargeInit [$[$usingL],*] $initT $nm $pred) => withFreshHeartbeatsT do
      (← getMainGoal).setTag `init; runInitPass usingL pred initT
      throwUnsolvedInvGoals nm m!"Invariant `{nm.getId}` failed on initial state `{formatTargetName initT}`:"
        m!"Hint: Update the initial `state` values so `{nm.getId}` holds, add `using [lemma]`, or supply a `:= by` proof."
  | `(tactic| qedDischargePreserved [$[$usingL],*] $upd $nm $pred $[from $init]? $[_qedProve [$[$proveCases],*]]?) =>
    runDischargePreserved usingL upd nm pred init proveCases

simproc_decl fnReduceStrLen (String.length _) := fun e => do
  let some (Expr.lit (Literal.strVal s)) := e.getAppArgs[0]? | return .continue
  let charTy := mkConst ``Char
  let cs := s.toList.foldr (fun c acc => mkApp2 (mkApp (mkConst ``List.cons [0]) charTy) (mkApp (mkConst ``Char.ofNat) (mkNatLit c.toNat)) acc) (mkApp (mkConst ``List.nil [0]) charTy)
  let nExpr := mkNatLit s.length
  return .done { expr := nExpr, proof? := some (← Meta.mkEqTrans (mkApp (mkConst ``String.length_ofList) cs) (← Meta.mkEqRefl nExpr)) }

private def strGuardNormNames : Array Name :=
  impHypSimpNames ++ #[``Qed.Str.str_toString, ``Qed.Lang.QedSeqLit.ofList_array, ``Qed.Lang.QedSeqLit.ofList_list,
    ``Array.mem_toArray, ``Decidable.not_not, ``Bool.not_eq_false, ``Bool.not_eq_true, ``not_or, ``String.all_bool_eq]
private def ordDispatchSimpNames : Array Name := #[
  ``Qed.QedMin2.run_scalar, ``Qed.QedMin2.run_key, ``Qed.QedMin2.run_cmp,
  ``Qed.QedMax2.run_scalar, ``Qed.QedMax2.run_key, ``Qed.QedMax2.run_cmp,
  ``Qed.QedOrdArg.sortFn_key, ``Qed.QedOrdArg.sortFn_cmp,
  ``Qed.QedOrdArg.sortDescFn_key, ``Qed.QedOrdArg.sortDescFn_cmp,
  ``Qed.QedOrdArg.minFn_key, ``Qed.QedOrdArg.minFn_cmp,
  ``Qed.QedOrdArg.maxFn_key, ``Qed.QedOrdArg.maxFn_cmp,
  ``Qed.QedOrdArg.isSortedFn_key, ``Qed.QedOrdArg.isSortedFn_cmp,
  ``Qed.QedOrdArg.isSortedDescFn_key, ``Qed.QedOrdArg.isSortedDescFn_cmp,
  ``Qed.QedOrdArg.isSortedBFn_key, ``Qed.QedOrdArg.isSortedBFn_cmp,
  ``Qed.QedOrdArg.isSortedDescBFn_key, ``Qed.QedOrdArg.isSortedDescBFn_cmp,
  ``Qed.QedOrdArg.isMinOfFn_key, ``Qed.QedOrdArg.isMinOfFn_cmp,
  ``Qed.QedOrdArg.isMaxOfFn_key, ``Qed.QedOrdArg.isMaxOfFn_cmp]
private def fnContractSimpNames : Array Name :=
  strGuardNormNames ++ ordDispatchSimpNames ++ #[``Array.size_push, ``Array.size_set, ``Array.size_map, ``Array.size_append,
    ``Array.size_reverse, ``List.length_cons, ``List.length_append, ``List.length_map, ``String.length_append,
    ``Option.isSome_none, ``Option.isSome_some, ``Option.isNone_none, ``Option.isNone_some, ``Qed.qedCoalesce_option,
    ``Qed.qedIterable_toList_list, ``Qed.qedIterable_toList_array, ``Qed.qedIterable_toList_range,
    ``Nat.min_def, ``Nat.max_def, ``Int.min_def, ``Int.max_def,
    ``true_and, ``and_true, ``false_or, ``or_false, ``true_or, ``or_true, ``id_eq, ``ne_eq]
private def ordSimpNames : Array Name := #[
  ``Qed.QedOrd.le_nat, ``Qed.QedOrd.le_int, ``Qed.QedOrd.le_char, ``Qed.QedOrd.le_string, ``Qed.QedOrd.le_bool,
  ``Qed.QedOrd.le_desc, ``Qed.QedOrd.le_desc_mk, ``Qed.QedOrd.le_prod,
  ``Qed.QedOrd.le_option_none, ``Qed.QedOrd.le_option_some_none, ``Qed.QedOrd.le_option_some,
  ``Qed.QedOrd.leB_eq_true, ``Qed.QedOrd.leB_eq_false,
  ``Qed.QedSeq.toList_array, ``Qed.QedSeq.toList_list,
  ``Qed.qedMinKey_isSome_iff, ``Qed.qedMaxKey_isSome_iff, ``Qed.qedMinCmp_isSome_iff, ``Qed.qedMaxCmp_isSome_iff,
  ``Qed.qedIsMinOfKey_minKey, ``Qed.qedIsMaxOfKey_maxKey,
  ``Qed.qedSortKey_array_head?_isMinOf, ``Qed.qedSortKey_list_head?_isMinOf,
  ``Qed.qedIsSortedKey_sortKey, ``Qed.qedIsSortedDescKey_sortDescKey,
  ``Qed.qedIsSortedKeyB_eq_true, ``Qed.qedIsSortedDescKeyB_eq_true,
  ``Qed.qedSortKey_array_mem, ``Qed.qedSortDescKey_array_mem, ``Qed.qedSortCmp_array_mem, ``Qed.qedSortDescCmp_array_mem,
  ``Qed.qedSortKey_array_size, ``Qed.qedSortDescKey_array_size, ``Qed.qedSortCmp_array_size, ``Qed.qedSortDescCmp_array_size,
  ``Qed.qedSortKey_list_mem, ``Qed.qedSortDescKey_list_mem, ``Qed.qedSortCmp_list_mem, ``Qed.qedSortDescCmp_list_mem,
  ``Qed.qedSortKey_list_length, ``Qed.qedSortDescKey_list_length, ``Qed.qedSortCmp_list_length, ``Qed.qedSortDescCmp_list_length,
  ``Qed.qedIsSortedKey_array_empty, ``Qed.qedIsSortedKey_array_singleton, ``Qed.qedIsSortedKey_array_push_iff,
  ``Qed.qedIsSortedKey_array_filter_of_size_eq, ``Qed.qedIsSortedDescKey_array_filter_of_size_eq,
  ``Qed.qedIsSortedKey_list_nil, ``Qed.qedIsSortedKey_list_singleton,
  ``Qed.qedIsSortedKey_list_filter, ``Qed.qedIsSortedDescKey_list_filter,
  ``Qed.Array.mem_filter_of_size_eq, ``Qed.Array.toList_filter_of_size_eq,
  ``Qed.Array.forall_mem_filter_of_size_eq, ``Qed.Array.exists_mem_filter_of_size_eq,
  ``Qed.Array.forall_mem_filter, ``Qed.Array.exists_mem_filter, ``Qed.List.forall_mem_filter, ``Qed.List.exists_mem_filter,
  ``Qed.Array.forall_mem_map, ``Qed.Array.exists_mem_map, ``Qed.List.forall_mem_map, ``Qed.List.exists_mem_map,
  ``Array.mem_filter, ``List.mem_filter, ``Array.mem_map, ``List.mem_map,
  ``Array.mem_toList_iff, ``Array.toList_filter, ``Array.toList_map, ``Array.length_toList,
  ``Bool.and_eq_true, ``Bool.or_eq_true, ``decide_eq_true_eq, ``decide_eq_false_iff_not, ``beq_iff_eq, ``bne_iff_ne, ``eq_self]
private def fnMemSimpNames : Array Name :=
  fnContractSimpNames ++ ordSimpNames ++ #[``Array.mem_push, ``Array.not_mem_empty, ``Array.mem_append,
    ``List.mem_cons, ``List.not_mem_nil, ``List.mem_append, ``forall_eq, ``forall_eq', ``Option.some.injEq]
private def loopSimpNames : Array Name :=
  fnMemSimpNames ++ #[
    ``Qed.qedMatchStep_next, ``Qed.qedMatchStep_break, ``Qed.qedMatchStep_ret,
    ``Qed.qedMatchStep_dite, ``Qed.qedMatchStep_ite, ``Qed.qedMatchStep_option,
    ``Qed.qedMinListBy_nil, ``Qed.qedMinListBy_append_singleton,
    ``Qed.QedRange.start_mk1, ``Qed.QedRange.stop_mk1, ``Qed.QedRange.step_mk1,
    ``Qed.QedRange.start_mk2, ``Qed.QedRange.stop_mk2, ``Qed.QedRange.step_mk2,
    ``Qed.QedRange.start_mk3, ``Qed.QedRange.stop_mk3, ``Qed.QedRange.step_mk3,
    ``Qed.QedRange.toList_length, ``Qed.QedRange.count_mk1, ``Qed.QedRange.toList_mk1_length,
    ``Qed.forall_mem_append_singleton, ``Qed.exists_mem_append_singleton,
    ``Qed.forall_mem_nil_iff, ``Qed.exists_mem_nil_iff,
    ``Option.isNone_iff_eq_none, ``Option.isNone_eq_false_iff, ``Option.isSome_eq_false_iff,
    ``List.length_nil, ``List.isEmpty_nil, ``List.isEmpty_cons,
    ``Nat.zero_add, ``Nat.add_zero, ``Nat.mul_one, ``Nat.one_mul,
    ``eq_self, ``true_implies, ``false_implies,
    ``and_imp, ``not_and, ``imp_false, ``not_false_eq_true, ``not_true_eq_false]
private def pruneSimpNames : Array Name :=
  #[``reduceCtorEq, ``Option.some.injEq, ``Option.isSome_none, ``Option.isSome_some, ``Option.isNone_none, ``Option.isNone_some,
    ``Bool.false_eq_true, ``Bool.true_eq_false, ``Bool.not_true, ``Bool.not_false, ``ite_true, ``ite_false, ``dite_true, ``dite_false, ``Qed.Lang.QedVal.val_id]
private def strAllNormNames : Array Name :=
  #[``String.all_bool_eq, ``Qed.Lang.QedVal.val_id, ``Qed.Str.str_toString, ``String.toList_append, ``List.all_append, ``Bool.and_eq_true]
private def charImpSimpNames : Array Name := #[``Qed.Lang.QedVal.val_id] ++ boolSimpNames
private def charNatSimpNames : Array Name := #[``Char.le_def, ``Char.lt_def, ``UInt32.le_iff_toNat_le, ``UInt32.lt_iff_toNat_lt, ``Char.ext_iff, ``Char.toNat]

private def countBVar (idx : Nat) : Expr → Nat
  | .bvar i => if i == idx then 1 else 0 | .app f a => countBVar idx f + countBVar idx a
  | .lam _ ty b _ | .forallE _ ty b _ => countBVar idx ty + countBVar (idx + 1) b
  | .letE _ ty v b _ => countBVar idx ty + countBVar idx v + countBVar (idx + 1) b
  | .mdata _ e | .proj _ _ e => countBVar idx e | _ => 0

@[noinline] private def shareLetResult? (g0 : MVarId) : MetaM (Option (FVarId × FVarId × MVarId)) := do
  let .letE nm ty val body _ := (← g0.withContext (instantiateMVars (← g0.getType))).consumeMData | return none
  if countBVar 0 body < 2 then return none
  g0.withContext do
    let eqTy := mkApp3 (mkConst ``Eq [← Meta.getLevel ty]) ty (.bvar 0) val
    let m ← Meta.mkFreshExprSyntheticOpaqueMVar (Expr.forallE nm ty (Expr.forallE `_qedResDef eqTy (body.liftLooseBVars 0 1) .default) .default)
    g0.assign (mkApp2 m val (← Meta.mkEqRefl val))
    let (resFv, g1) ← m.mvarId!.intro1P; let (hResFv, g2) ← g1.intro1P
    return some (resFv, hResFv, g2)

private def trySubstFVar (g : MVarId) (fv : FVarId) : MetaM (Option MVarId) := tryRestoreM none Option.isSome do some <$> Meta.subst g fv
private def findFVarByName? (g : MVarId) (nm : Name) : MetaM (Option FVarId) := g.withContext do return (← collectLCtxDecls fun d => pure (if d.userName == nm then some d.fvarId else none)).back?
private def simpOneFVar (g : MVarId) (ctx : Meta.Simp.Context) (fv : FVarId) : MetaM (Option (FVarId × MVarId)) :=
  tryRestoreM (some (fv, g)) (fun _ => true) do
    match (← Meta.simpGoal g ctx #[] none (simplifyTarget := false) #[fv]).1 with
    | none => return none | some (newFvs, g') => return some (newFvs.getD 0 fv, g')
private def isDefEqFast (a b : Expr) : MetaM Bool := if a == b then pure true else Meta.withTransparency .reducible (Meta.isDefEq a b)

private def stripValWrap (e : Expr) (fuel : Nat := 32) : Expr := match fuel with
  | 0 => e.consumeMData
  | fuel + 1 =>
      let e := e.consumeMData
      if e.isAppOfArity ``Qed.Lang.QedVal.val 4 then stripValWrap e.getAppArgs[3]! fuel
      else if e.isAppOfArity ``toString 3 && e.getAppArgs[0]!.isConstOf ``String then stripValWrap e.getAppArgs[2]! fuel else e
private def matchIteSide? (e : Expr) : Option (Bool × Expr) :=
  if e.isAppOfArity ``dite 5 then some (true, e) else if e.isAppOfArity ``ite 5 then some (false, e) else none

@[noinline] private def tryFastSplitIteEqHyp (g : MVarId) (fv : FVarId) (fvName : Name) : MetaM (Option (List MVarId)) :=
  tryRestoreM none Option.isSome do
    let some (eqTy, lhs, rhs) := (← g.withContext do instantiateMVars (← fv.getType)).consumeMData.eq? | return none
    let (l, r) := (stripValWrap lhs, stripValWrap rhs)
    let some (isLeft, isDite, ifExpr, other) :=
      (match matchIteSide? l, matchIteSide? r with | some (d, e), _ => some (true, d, e, r) | _, some (d, e) => some (false, d, e, l) | _, _ => none)
      | return none
    let a := ifExpr.getAppArgs; let (c, decInst, t, e) := (a[1]!, a[2]!, a[3]!, a[4]!)
    let lem := match isLeft, isDite with
      | true, true => ``Qed.Str.dite_eq_cases | false, true => ``Qed.Str.eq_dite_cases
      | true, false => ``Qed.Str.ite_eq_cases | false, false => ``Qed.Str.eq_ite_cases
    g.withContext do
      let tgt ← instantiateMVars (← g.getType); let u ← Meta.getLevel eqTy
      let mkBranch (isPos : Bool) (branchExpr : Expr) : MetaM MVarId := do
        let bTy ← Meta.withLocalDeclD `_qedCond (if isPos then c else mkNot c) fun hc => do
          let v := if isDite then branchExpr.beta #[hc] else branchExpr
          let eqE := mkApp3 (mkConst ``Eq [u]) eqTy (if isLeft then v else other) (if isLeft then other else v)
          Meta.mkForallFVars #[hc] (Expr.forallE fvName eqE tgt .default)
        return (← Meta.mkFreshExprSyntheticOpaqueMVar bTy).mvarId!
      let (mThen, mElse) := (← mkBranch true t, ← mkBranch false e)
      g.assign (mkAppN (mkConst lem [u]) #[eqTy, c, decInst, t, e, other, tgt, mkFVar fv, mkMVar mThen, mkMVar mElse])
      let prep (m : MVarId) : MetaM MVarId := do return (← (← (← try m.clear fv catch _ => pure m).intro1).2.intro fvName).2
      return some [← prep mThen, ← prep mElse]

@[noinline] private def tryPruneBranch (g0 : MVarId) (fvName? : Option Name) : MetaM (Option MVarId) := do
  let isClosed (g : MVarId) : MetaM Bool := do if ← tryCloseContradiction g then pure true else tryCloseTrivial g (reducibleOnly := true)
  if ← isClosed g0 then return none
  let getPruneCtx : MetaM Meta.Simp.Context := return (← mkCachedSimpCtx "fnPrune" pruneSimpNames { zetaDelta := false } #[] false false).1
  let (g1, curFv?) ← match fvName? with
    | some nm => match ← findFVarByName? g0 nm with
        | none => pure (g0, none)
        | some fv =>
            let ty ← g0.withContext do instantiateMVars (← fv.getType)
            if ty.consumeMData.eq?.any fun (_, l, r) => (matchIteSide? (stripValWrap l)).isSome || (matchIteSide? (stripValWrap r)).isSome then pure (g0, some fv)
            else match ← simpOneFVar g0 (← getPruneCtx) fv with | none => return none | some (fv', g') => pure (g', some fv')
    | none => match ← simpGoalOnly g0 (← getPruneCtx) #[] #[] (simplifyTarget := true) with | none => return none | some g' => pure (g', none)
  if ← isClosed g1 then return none
  if let some fv := curFv? then
    let optFv? := (← g1.withContext do instantiateMVars (← fv.getType)).consumeMData.eq?.bind fun (_, l, r) =>
      let (l, r) := (l.consumeMData, r.consumeMData)
      if l.isFVar && r.isAppOfArity ``Option.none 1 then some l.fvarId! else if r.isFVar && l.isAppOfArity ``Option.none 1 then some r.fvarId! else none
    if let some optFv := optFv? then
      let conflict? ← g1.withContext <| findLCtxDecl? (includeLet := false) fun d => do
        if d.fvarId == fv then return none
        let dt := (← instantiateMVars d.type).consumeMData
        return if dt.containsFVar optFv && dt.getUsedConstants.any (fun c => c == ``Option.isSome || c == ``Option.some) then some d.userName else none
      if let some cNm := conflict? then if let some gSub ← trySubstFVar g1 fv then if let some cFv ← findFVarByName? gSub cNm then
        match ← simpOneFVar gSub (← getPruneCtx) cFv with | none => return none | some (_, gSub') => if ← tryCloseContradiction gSub' then return none
  return some g1

@[noinline] private def linearSplit (g0 : MVarId) (splitOne : MVarId → MetaM (Option (List MVarId))) (pruneName? : Option Name) : MetaM (List MVarId) := do
  let rec go (work done : List MVarId) : Nat → MetaM (List MVarId)
    | 0 => return done.reverse ++ work
    | fuel + 1 => match work with
        | [] => return done.reverse
        | g :: rest => do
            if done.length + work.length > 16 then return done.reverse ++ work
            match ← splitOne g with | none => go rest (g :: done) fuel | some kids => go ((← filterMapGoalsM (tryPruneBranch · pruneName?) kids) ++ rest) done fuel
  go [g0] [] 32

@[noinline] private def linearSplitHyp (g0 : MVarId) (fvName : Name) (substTargetName? : Option Name := none) : MetaM (List MVarId) := do
  let survived ← linearSplit g0 (fun g => do
    let some fv ← findFVarByName? g fvName | return none
    match ← tryFastSplitIteEqHyp g fv fvName with | some kids => pure (some kids) | none => trySplitLocalDecl g fv) (some fvName)
  let some targetNm := substTargetName? | return survived
  filterMapGoalsM (fun g => do
    let some fv ← findFVarByName? g fvName | return some g
    let some targetFv ← findFVarByName? g targetNm | return some g
    let shouldSubst := (← g.withContext do instantiateMVars (← fv.getType)).consumeMData.eq?.any fun (_, l, r) =>
      (l.consumeMData == mkFVar targetFv && !r.containsFVar targetFv) || (r.consumeMData == mkFVar targetFv && !l.containsFVar targetFv)
    if shouldSubst then match ← trySubstFVar g fv with | some gSub => tryPruneBranch gSub none | none => pure (some g) else pure (some g)) survived

private def linearSplitTarget (g0 : MVarId) : MetaM (List MVarId) := linearSplit g0 trySplitTarget none

@[noinline] private def unfoldConstIn (g : MVarId) (fnName : Name) (fvName? : Option Name := none) : MetaM (Option MVarId) := do
  let fv? ← match fvName? with
    | none => pure none | some fvName => match ← findFVarByName? g fvName with | some fv => pure (some fv) | none => return some g
  let fast? ← tryRestoreM none Option.isSome <| g.withContext do
    let e ← instantiateMVars (← match fv? with | some fv => fv.getType | none => g.getType)
    let e' ← Meta.deltaExpand e (· == fnName)
    if e' == e then return none
    some <$> match fv? with | some fv => g.replaceLocalDeclDefEq fv e' | none => g.replaceTargetDefEq e'
  if let some g' := fast? then return some g'
  let ctx ← mkDynamicSimpCtx #[fnName] none { zetaDelta := true } (dsimpOnly := false) (withEqns := true)
  match fv? with | some fv => return (← simpOneFVar g ctx fv).map Prod.snd | none => simpGoalOnly g ctx #[] #[] (simplifyTarget := true)

private def extractStrLit? (e : Expr) : Option String := match (stripValWrap e).consumeMData with | .lit (.strVal s) => some s | _ => none
private def extractStrAppend? (e : Expr) : Option (Expr × Expr) :=
  let e := (stripValWrap e).consumeMData
  if e.isAppOfArity ``HAppend.hAppend 6 && e.getAppArgs[0]!.isConstOf ``String then some (e.getAppArgs[4]!, e.getAppArgs[5]!)
  else if e.isAppOfArity ``String.append 2 then some (e.getAppArgs[0]!, e.getAppArgs[1]!) else none
private def extractNumToString? (e : Expr) : Option (Bool × Expr) :=
  let e := (stripValWrap e).consumeMData
  let check (tyNm reprNm : Name) (isInt : Bool) :=
    if e.isAppOfArity ``toString 3 && e.getAppArgs[0]!.isConstOf tyNm then some (isInt, stripValWrap e.getAppArgs[2]!)
    else if e.isAppOfArity reprNm 1 then some (isInt, stripValWrap e.getAppArgs[0]!) else none
  (check ``Nat ``Nat.repr false).orElse fun _ => check ``Int ``Int.repr true
private def tryMkDecideProof (prop : Expr) : MetaM (Option Expr) := do
  let m ← Meta.mkFreshExprSyntheticOpaqueMVar (← instantiateMVars prop)
  if ← tryDirectDecide m.mvarId! then some <$> instantiateMVars m else return none
private def tryCloseBoolFalse (lhs : Expr) : MetaM (Option Expr) := do
  let eqProp := mkBoolEq lhs (mkConst ``Bool.false)
  if let some pf ← tryMkDecideProof eqProp then return some pf
  tryRestoreM none Option.isSome do
    let m ← Meta.mkFreshExprSyntheticOpaqueMVar eqProp
    let (ctx, _) ← mkCachedSimpCtx "boolFalseCheck" (boolSimpNames ++ boolConstSimpNames ++ #[``Qed.Lang.QedVal.val_id])
    match ← simpGoalOnly m.mvarId! ctx with | none => some <$> instantiateMVars m | some _ => return none

private def extractStrAll? (ty : Expr) : Option (Expr × Expr × Bool) :=
  ty.consumeMData.eq?.bind fun (_, lhs, rhs) =>
    if !rhs.consumeMData.isConstOf ``Bool.true then none
    else let l := lhs.consumeMData
      if l.isAppOfArity ``List.all 3 && l.getAppArgs[1]!.consumeMData.isAppOfArity ``String.toList 1 then
        some (stripValWrap l.getAppArgs[1]!.consumeMData.getAppArgs[0]!, l.getAppArgs[2]!, true)
      else if l.isAppOfArity ``String.all 4 then some (stripValWrap l.getAppArgs[1]!, l.getAppArgs[2]!, false) else none

private def extractStrContains? (ty : Expr) : Option (Expr × Expr × Bool) :=
  let t := ty.consumeMData
  let (inner, isNeg, want) := if t.isAppOfArity ``Not 1 then (t.getAppArgs[0]!.consumeMData, true, ``Bool.true) else (t, false, ``Bool.false)
  inner.eq?.bind fun (_, lhs, rhs) =>
    let l := lhs.consumeMData
    if rhs.consumeMData.isConstOf want && l.isAppOfArity ``String.contains 7 then some (stripValWrap l.getAppArgs[4]!, l.getAppArgs[5]!, isNeg) else none

private def extractStrMemColl? (ty : Expr) : Option (Expr × Expr × Bool) :=
  let t := ty.consumeMData
  if t.isAppOfArity ``Membership.mem 5 && t.getAppArgs[0]!.isConstOf ``String then
    let collTy := t.getAppArgs[1]!.consumeMData
    if collTy.isAppOfArity ``List 1 || collTy.isAppOfArity ``Array 1 then some (stripValWrap t.getAppArgs[4]!, t.getAppArgs[3]!.consumeMData, collTy.isAppOfArity ``Array 1) else none
  else none

@[noinline] private def tryProveFromStrMemColl (hMem coll checkFn : Expr) (isArr : Bool) (arrLem listLem : Name) : MetaM (Option Expr) := do
  let listExpr := if isArr then mkApp2 (mkConst ``Array.toList [0]) (mkConst ``String) coll else coll
  let some hall ← tryMkDecideProof (mkBoolEqTrue (mkListAll (mkConst ``String) listExpr checkFn)) | return none
  some <$> Meta.mkAppM (if isArr then arrLem else listLem) #[hMem, hall]

private def mkEqTransChain : List Expr → MetaM Expr
  | [h] => pure h | h :: rest => do Meta.mkEqTrans h (← mkEqTransChain rest) | [] => throwError "mkEqTransChain: empty"

mutual
@[noinline] private partial def proveCharNotMemFromDecl? (env : Environment) (d : Char) (dExpr a goalTy : Expr) (depth : Nat) (decl : LocalDecl) : MetaM (Option Expr) := do
  let ty := (← instantiateMVars decl.type).consumeMData
  if ← isDefEqFast ty goalTy then return some decl.toExpr
  if let some (s, ch, isNeg) := extractStrContains? ty then
    if ← isDefEqFast s a then if ← isDefEqFast ch dExpr then
      return some (← Meta.mkAppM (if isNeg then ``Qed.Str.str_not_mem_of_not_contains else ``Qed.Str.str_not_mem_of_contains_false) #[decl.toExpr])
  if let some (s, p, isToList) := extractStrAll? ty then
    if ← isDefEqFast s a then if let some hpd ← tryCloseBoolFalse (p.beta #[dExpr]) then
      return some (← Meta.mkAppM (if isToList then ``Qed.Str.str_not_mem_of_toList_all else ``Qed.Str.str_not_mem_of_all) #[decl.toExpr, hpd])
  if let .forallE _ cTy (.forallE _ memTy body _) _ := ty then
    if cTy.isConstOf ``Char && memTy.isAppOfArity ``Membership.mem 5 && !body.hasLooseBVar 0 then
      let listArg := memTy.getAppArgs[3]!.consumeMData
      if listArg.isAppOfArity ``String.toList 1 then if ← isDefEqFast (stripValWrap listArg.getAppArgs[0]!) a then
        let predAtD := (body.lowerLooseBVars 1 1).instantiate1 dExpr
        if !predAtD.hasLooseBVars then if let some hnd ← tryMkDecideProof (mkNot predAtD) then
          return some (← Meta.mkAppM ``Qed.Str.str_not_mem_of_forall #[decl.toExpr, hnd])
  if let some (elem, coll, isArr) := extractStrMemColl? ty then
    if ← isDefEqFast elem a then
      if let some pf ← tryProveFromStrMemColl decl.toExpr coll (mkApp (mkConst ``strNotContainsChar) dExpr) isArr ``Qed.Str.str_not_mem_of_mem_array ``Qed.Str.str_not_mem_of_mem_list then
        return some pf
  if depth == 0 then return none
  let some (_, lhs, rhs) := ty.eq? | return none
  unless rhs.consumeMData.isConstOf ``Bool.true do return none
  let .const fnNm _ := lhs.getAppFn | return none
  unless qedIsHelper env fnNm && lhs.getAppArgs.any (stripValWrap · == a) do return none
  tryRestoreM none Option.isSome do
    let m ← Meta.mkFreshExprSyntheticOpaqueMVar goalTy
    let ctx ← mkDynamicSimpCtx (strGuardNormNames.push fnNm) none { zetaDelta := true }
    match ← simpGoalOnly m.mvarId! ctx #[] #[decl.fvarId] (simplifyTarget := false) with
    | none => some <$> instantiateMVars m
    | some m1 =>
        let m2 := (← splitAndHypsGoal m1 false 16).1
        match ← m2.withContext (proveCharNotMem? d a (depth - 1)) with
        | some pf => m2.assign pf; some <$> instantiateMVars m | none => return none

@[noinline] private partial def proveCharNotMem? (d : Char) (a0 : Expr) (depth : Nat := 2) : MetaM (Option Expr) := do
  let a := stripValWrap a0; let dExpr := toExpr d
  let goalTy := mkNot (← Meta.mkAppM ``Membership.mem #[mkStrToList a, dExpr])
  if d < '0' || '9' < d then
    if let some (isInt, arg) := extractNumToString? a then
      if !isInt || d != '-' then
        let digitOut := mkApp2 (mkConst ``Or) (← Meta.mkAppM ``LT.lt #[dExpr, toExpr '0']) (← Meta.mkAppM ``LT.lt #[toExpr '9', dExpr])
        let cond := if isInt then mkApp2 (mkConst ``And) (mkApp3 (mkConst ``Ne [1]) (mkConst ``Char) dExpr (toExpr '-')) digitOut else digitOut
        if let some hd ← tryMkDecideProof cond then
          return some (← Meta.mkAppM (if isInt then ``Qed.Str.int_toString_not_mem else ``Qed.Str.nat_toString_not_mem) #[hd, arg])
  if let some s := extractStrLit? a then
    if !s.contains d then if let some pf ← tryMkDecideProof goalTy then return some pf
  if let some (x, y) := extractStrAppend? a then
    if let some hx ← proveCharNotMem? d x depth then if let some hy ← proveCharNotMem? d y depth then
      return some (← Meta.mkAppM ``Qed.Str.str_not_mem_append #[hx, hy])
  findLCtxDecl? (includeLet := false) (proveCharNotMemFromDecl? (← getEnv) d dExpr a goalTy depth)
end

@[noinline] private partial def normStrLeaf (e0 : Expr) : MetaM (Expr × Expr) := do
  let e := e0.consumeMData; let a := e.getAppArgs
  if e.isAppOfArity ``Qed.Lang.QedVal.val 4 then
    let (e', h2) ← normStrLeaf a[3]!; return (e', ← Meta.mkEqTrans (← Meta.mkAppM ``Qed.Lang.QedVal.val_id #[a[3]!]) h2)
  if e.isAppOfArity ``toString 3 && a[0]!.isConstOf ``String then
    let (e', h2) ← normStrLeaf a[2]!; return (e', ← Meta.mkEqTrans (mkApp (mkConst ``Qed.Str.str_toString) a[2]!) h2)
  if e.isAppOfArity ``toString 3 && a[2]!.consumeMData.isAppOfArity ``Qed.Lang.QedVal.val 4 then
    let inner := a[2]!.consumeMData.getAppArgs[3]!; return (mkApp3 e.getAppFn a[0]! a[1]! inner, ← Meta.mkAppM ``toString_qedVal_eq #[inner])
  return (e, ← Meta.mkEqRefl e)

private def mkStrAppendExpr (x y : Expr) : MetaM Expr := Meta.mkAppM ``HAppend.hAppend #[x, y]

@[noinline] private partial def reassocStrAcc (t acc : Expr) : MetaM (Expr × Expr) := do
  let (t0, hLeaf) ← normStrLeaf t; let hLift ← Meta.mkAppM ``str_append_congr_right #[acc, hLeaf]
  match extractStrAppend? t0 with
  | none => if extractStrLit? t0 == some "" then return (acc, ← Meta.mkEqTrans hLift (mkApp (mkConst ``String.empty_append) acc)) else return (← mkStrAppendExpr t0 acc, hLift)
  | some (a, b) =>
      let (r1, h1) ← reassocStrAcc b acc; let (r2, h2) ← reassocStrAcc a r1
      return (r2, ← mkEqTransChain [hLift, mkApp3 (mkConst ``String.append_assoc) a b acc, ← Meta.mkAppM ``str_append_congr_left #[a, h1], h2])

@[noinline] private partial def reassocStr (t : Expr) : MetaM (Expr × Expr) := do
  let (t0, hLeaf) ← normStrLeaf t
  match extractStrAppend? t0 with
  | none => return (t0, hLeaf)
  | some (a, b) =>
      let (rb, hb) ← reassocStr b; let h1 ← Meta.mkAppM ``str_append_congr_left #[a, hb]
      if extractStrLit? rb == some "" then let (ra, ha) ← reassocStr a; return (ra, ← mkEqTransChain [hLeaf, h1, mkApp (mkConst ``String.append_empty) a, ha])
      let (res, hAcc) ← reassocStrAcc a rb; return (res, ← mkEqTransChain [hLeaf, h1, hAcc])

private def mkStrPrefixSplitPf (lit head tail rest : Expr) : MetaM (Option (Expr × Expr)) := do
  let some hSplit ← tryMkDecideProof (mkApp3 (mkConst ``Eq [1]) (mkConst ``String) lit (← mkStrAppendExpr head tail)) | return none
  return some (← mkStrAppendExpr tail rest, ← Meta.mkEqTrans (← Meta.mkAppM ``str_append_congr_right #[rest, hSplit]) (mkApp3 (mkConst ``String.append_assoc) head tail rest))

@[noinline] private def tryStrSepSplit? (p₁ p₂ x y eqPf' : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let (some (sep₁, r₁), some (sep₂, r₂)) := (extractStrAppend? x, extractStrAppend? y) | return none
  let (some s₁, some s₂) := (extractStrLit? sep₁, extractStrLit? sep₂) | return none
  let (d₁ :: _, d₂ :: _) := (s₁.toList, s₂.toList) | return none
  if d₁ != d₂ then return none
  let some h₁ ← proveCharNotMem? d₁ p₁ | return none
  let some h₂ ← proveCharNotMem? d₁ p₂ | return none
  let runSep (sepExpr rhs₁ rhs₂ eqTerm : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
    let optChar := mkApp (mkConst ``Option [0]) (mkConst ``Char)
    let some hsep ← tryMkDecideProof (mkApp3 (mkConst ``Eq [1]) optChar (mkApp2 (mkConst ``List.head? [0]) (mkConst ``Char) (mkStrToList sepExpr)) (mkApp2 (mkConst ``Option.some [0]) (mkConst ``Char) (toExpr d₁))) | return none
    let pairPf := mkAppN (mkConst ``Qed.Str.str_split_sep_inj) #[sepExpr, p₁, p₂, rhs₁, rhs₂, toExpr d₁, hsep, h₁, h₂, eqTerm]
    return some (rhs₁, rhs₂, ← Meta.mkAppM ``And.left #[pairPf], ← Meta.mkAppM ``And.right #[pairPf])
  if s₁ == s₂ then runSep sep₁ r₁ r₂ eqPf'
  else
    let dStr := Expr.lit (.strVal (String.singleton d₁))
    let some (nr₁, hL) ← mkStrPrefixSplitPf sep₁ dStr (Expr.lit (.strVal (String.ofList (s₁.toList.drop 1)))) r₁ | return none
    let some (nr₂, hR) ← mkStrPrefixSplitPf sep₂ dStr (Expr.lit (.strVal (String.ofList (s₂.toList.drop 1)))) r₂ | return none
    runSep dStr nr₁ nr₂ (← mkEqTransChain [← Meta.mkEqSymm (← Meta.mkAppM ``str_append_congr_left #[p₁, hL]), eqPf', ← Meta.mkAppM ``str_append_congr_left #[p₂, hR]])

@[noinline] private def collectStringEqFacts (lhs0 rhs0 eqPf0 : Expr) (fuel0 : Nat := 32) : MetaM (Sum Expr (Array Expr)) := do
  let (lInit, hlInit) ← reassocStr lhs0; let (rInit, hrInit) ← reassocStr rhs0
  let pfInit ← mkEqTransChain [← Meta.mkEqSymm hlInit, eqPf0, hrInit]
  let rec go (l r eqPf' : Expr) : Nat → MetaM (Sum Expr (Array Expr))
    | 0 => return .inr #[eqPf']
    | fuel + 1 => do
      if l == r then return .inr #[]
      if let (some (p₁, x), some (p₂, y)) := (extractStrAppend? l, extractStrAppend? r) then
        if p₁ == p₂ then return ← go x y (← Meta.mkAppM ``Qed.Str.str_append_left_cancel #[eqPf']) fuel
        if let (some s₁, some s₂) := (extractStrLit? p₁, extractStrLit? p₂) then
          if strDiffPrefix s₁ s₂ then
            if let some hdiff ← tryMkDecideProof (mkBoolEqTrue (mkApp2 (mkConst ``strDiffPrefix) p₁ p₂)) then
              return .inl (← Meta.mkAppM ``Qed.Str.str_append_ne_of_diff_prefix #[hdiff, eqPf'])
          else if s₁.length != s₂.length then
            let swap := s₂.length < s₁.length
            let (shorter, longP, shortLen, longS, shortRest, longRest) := if swap then (p₂, p₁, s₂.length, s₁, y, x) else (p₁, p₂, s₁.length, s₂, x, y)
            if let some (nextLong, hSplit) ← mkStrPrefixSplitPf longP shorter (Expr.lit (.strVal (String.ofList (longS.toList.drop shortLen)))) longRest then
              let hComb ← if swap then Meta.mkEqTrans (← Meta.mkEqSymm hSplit) eqPf' else Meta.mkEqTrans eqPf' hSplit
              let hNext ← Meta.mkAppM ``Qed.Str.str_append_left_cancel #[hComb]
              return ← if swap then go nextLong shortRest hNext fuel else go shortRest nextLong hNext fuel
        if let some (rhs₁, rhs₂, pfL, pfR) ← tryStrSepSplit? p₁ p₂ x y eqPf' then
          match ← go p₁ p₂ pfL fuel with
          | .inl f => return .inl f
          | .inr fsL => match ← go rhs₁ rhs₂ pfR fuel with | .inl f => return .inl f | .inr fsR => return .inr (fsL ++ fsR)
        if x == y then return ← go p₁ p₂ (← Meta.mkAppM ``Qed.Str.str_append_right_cancel #[eqPf']) fuel
      if let (some (isIntL, _), some (isIntR, _)) := (extractNumToString? l, extractNumToString? r) then
        if isIntL == isIntR then return .inr #[← Meta.mkAppM (if isIntL then ``Qed.Str.int_toString_injective else ``Qed.Str.nat_toString_injective) #[eqPf']]
      if let (some s₁, some s₂) := (extractStrLit? l, extractStrLit? r) then
        if s₁ != s₂ then if let some hne ← tryMkDecideProof (mkApp3 (mkConst ``Ne [1]) (mkConst ``String) l r) then return .inl (mkApp hne eqPf')
      return .inr #[eqPf']
  go lInit rInit pfInit fuel0

private def isStringEqTy (ty : Expr) : Option (Expr × Expr) :=
  ty.consumeMData.eq?.bind fun (eqTy, l, r) => if eqTy.consumeMData.isConstOf ``String then some (l, r) else none

@[noinline] private def decomposeStringEqs (g0 : MVarId) : MetaM (Option MVarId) := do
  let decls ← g0.withContext <| collectLCtxDecls (includeLet := false) fun d => do
    let ty ← instantiateMVars d.type
    if (isStringEqTy ty).isSome then return some (true, d.fvarId)
    else if ← isPropSafe ty then return some (false, d.fvarId) else return none
  unless decls.any (·.1) do return some g0
  let guardFvs := decls.filterMap fun (isStr, fv) => if isStr then none else some fv
  let g1 ← if guardFvs.isEmpty then pure g0 else do
    let (guardCtx, _) ← mkCachedSimpCtx "strGuardNorm" strGuardNormNames { zetaDelta := false }
    match ← simpGoalOnly g0 guardCtx #[] guardFvs (simplifyTarget := false) with
    | none => return none | some g' => pure (← splitAndHypsGoal g' false 32).1
  let strEqs ← g1.withContext <| collectLCtxDecls (includeLet := false) fun d => return (isStringEqTy (← instantiateMVars d.type)).map fun (l, r) => (l, r, d.toExpr)
  let newFacts? ← foldlMeta strEqs (some #[]) fun acc? (lhs, rhs, pf) => match acc? with
    | none => pure none
    | some acc => do
        match ← g1.withContext (collectStringEqFacts lhs rhs pf) with
        | .inl falsePf => g1.assign (mkApp2 (mkConst ``False.elim [0]) (← g1.withContext (instantiateMVars (← g1.getType))) falsePf); pure none
        | .inr facts => pure (some (acc ++ facts))
  let some newFacts := newFacts? | return none
  if newFacts.isEmpty then return some g1 else return some (← assertFacts g1 "_qedStr" newFacts).1

private def extractStrLitListAux (e : Expr) : Nat → Option (List String)
  | 0 => none
  | fuel + 1 =>
      let e := e.consumeMData; let a := e.getAppArgs
      if e.isAppOfArity ``List.nil 1 then some []
      else if e.isAppOfArity ``List.cons 3 then do return (← extractStrLit? a[1]!) :: (← extractStrLitListAux a[2]! fuel)
      else if e.isAppOfArity ``List.toArray 2 || e.isAppOfArity ``Array.mk 2 then extractStrLitListAux a[1]! fuel
      else if e.isAppOfArity ``Qed.Lang.QedSeqLit.ofList 4 then extractStrLitListAux a[3]! fuel else none

@[noinline] private def assertStrMemLenBounds (g0 : MVarId) : MetaM MVarId := do
  unless (← g0.withContext (instantiateMVars (← g0.getType))).getUsedConstants.contains ``String.length do return g0
  let facts ← g0.withContext <| collectLCtxDecls (includeLet := false) fun d => do
    let some (_, coll, isArr) := extractStrMemColl? (← instantiateMVars d.type) | return none
    let some (s0 :: ss) := extractStrLitListAux coll 128 | return none
    let (lo, hi) := (ss.foldl (fun m s => min m s.length) s0.length, ss.foldl (fun m s => max m s.length) s0.length)
    tryProveFromStrMemColl d.toExpr coll (mkApp2 (mkConst ``strMemLenCheck) (mkNatLit lo) (mkNatLit hi)) isArr ``Qed.Str.str_length_bounds_of_mem_array ``Qed.Str.str_length_bounds_of_mem_list
  if facts.isEmpty then return g0 else return (← splitAndHypsGoal (← assertFacts g0 "_qedLen" facts).1 false 16).1

private def goalHasStrRepr (g : MVarId) : MetaM Bool := do
  let cs ← collectGoalConsts g true
  return cs.contains ``ToString.toString || cs.contains ``Nat.repr || cs.contains ``Int.repr || cs.contains ``Nat.toDigits

private def isNonRecDef (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.defnInfo d) => !(d.hints matches .opaque) && !d.value.getUsedConstants.contains c
  | _ => false

private def isCharHelperDef (env : Environment) (c : Name) : Bool :=
  isNonRecDef env c &&
    (qedIsHelper env c || match env.find? c with
      | some (.defnInfo d) => match d.type with | .forallE _ dom body _ => dom.isConstOf ``Char && body.isConstOf ``Bool | _ => false
      | _ => false)

@[noinline] private def deltaUnfoldLoop (g : MVarId) (pred : Environment → Name → Bool) (hfv? : Option FVarId) : Nat → MetaM MVarId
  | 0 => pure g
  | fuel + 1 => g.withContext do
      let p := pred (← getEnv)
      let tgt ← instantiateMVars (← g.getType); let tgt' ← Meta.deltaExpand tgt p
      let (g1, changed) ← if tgt' != tgt then pure (← g.replaceTargetDefEq tgt', true) else pure (g, false)
      let (g2, changed) ← match hfv? with
        | none => pure (g1, changed)
        | some hfv =>
            let hty ← instantiateMVars (← hfv.getType); let hty' ← Meta.deltaExpand hty p
            if hty' != hty then pure (← g1.replaceLocalDeclDefEq hfv hty', true) else pure (g1, changed)
      if !changed then return g2 else deltaUnfoldLoop g2 pred hfv? fuel

@[noinline] private def tryProveCharImp (impTy : Expr) : MetaM (Option Expr) := tryRestoreM none Option.isSome do
  let mImp ← if impTy.hasFVar then Meta.mkFreshExprSyntheticOpaqueMVar impTy else Meta.withLCtx {} {} (Meta.mkFreshExprSyntheticOpaqueMVar impTy)
  let done := some <$> instantiateMVars mImp
  let (fvs, g1) ← mImp.mvarId!.introN 2
  let g1 ← deltaUnfoldLoop g1 isCharHelperDef (some fvs[1]!) 6
  let dCtx ← mkEmptyDsimpCtx
  let some g2 ← simpGoalAllHyps g1 dCtx (dsimpOnly := true) | done
  let charImpCtx := (← mkCachedSimpCtx "charImp" charImpSimpNames).1
  let charNatSt ← (← getCachedSimpThms "charNat" charNatSimpNames).addConst ``UInt32.toNat_inj (inv := true)
  let charNatCtx ← Meta.Simp.mkContext { failIfUnchanged := false } #[charNatSt] (← Meta.getSimpCongrTheorems)
  let closeBranch (g : MVarId) : MetaM Bool := do
    if ← tryCloseTrivial g (reducibleOnly := true) then return true
    let some g3 ← simpGoalAllHyps g charImpCtx | return true
    if ← g3.assumptionCore then return true
    match ← simpGoalAllHyps g3 charNatCtx with
    | none => return true | some g4 => tryDirectOmega g4
  if ← closeAllGoals closeBranch (← splitTargetsRec 8 [g2] (some dCtx)) then done else return none

@[noinline] private def tryCloseOneStringAllSubgoal (sg : MVarId) : MetaM Bool := do
  if ← tryCloseBasic sg (reducibleOnly := true) then return true
  let some (seg, p, true) := extractStrAll? (← sg.withContext (instantiateMVars (← sg.getType))) | return false
  sg.withContext do
    if let some (isInt, arg) := extractNumToString? seg then
      let chars := if isInt then "-0123456789" else "0123456789"
      if let some hp ← tryMkDecideProof (mkBoolEqTrue (mkListAll (mkConst ``Char) (mkStrToList (Expr.lit (.strVal chars))) p)) then
        sg.assign (← Meta.mkAppM (if isInt then ``Qed.Str.int_toString_all else ``Qed.Str.nat_toString_all) #[hp, arg]); return true
    return (← findLCtxDecl? (includeLet := false) fun d => do
      let (de, dty) := (d.toExpr, (← instantiateMVars d.type).consumeMData)
      if let some (elem, coll, isArr) := extractStrMemColl? dty then if ← isDefEqFast elem seg then
        let checkFn := Expr.lam `x (mkConst ``String) (mkListAll (mkConst ``Char) (mkStrToList (.bvar 0)) (p.liftLooseBVars 0 1)) .default
        if let some pf ← tryProveFromStrMemColl de coll checkFn isArr ``Qed.Str.str_all_of_mem_array ``Qed.Str.str_all_of_mem_list then sg.assign pf; return some ()
      if let some (s', p', isToList) := extractStrAll? dty then if ← isDefEqFast s' seg then
        let hList := if isToList then de else mkApp3 (mkConst ``str_all_toList_of_all) s' p' de
        if ← isDefEqFast p' p then sg.assign hList; return some ()
        let impTy ← Meta.withLocalDeclD `c (mkConst ``Char) fun c =>
          Meta.mkForallFVars #[c] (Expr.forallE `_h (mkBoolEqTrue (p'.beta #[c])) (mkBoolEqTrue (p.beta #[c])) .default)
        if let some pfImp ← tryProveCharImp impTy then sg.assign (← Meta.mkAppM ``Qed.Str.list_all_mono #[hList, pfImp]); return some ()
      return none).isSome

@[noinline] private def tryCloseStringAllGoal (g0 : MVarId) : MetaM Bool := do
  if (extractStrAll? (← g0.withContext (instantiateMVars (← g0.getType)))).isNone then return false
  tryRestoreM false id do
    let some g1 ← simpGoalOnly g0 (← mkCachedSimpCtx "strAllNorm" strAllNormNames { zetaDelta := false }).1 | return true
    closeAllGoals tryCloseOneStringAllSubgoal (← splitGoalAnds g1)

@[noinline] private def finishStringGoals (gs : List MVarId) (withLenBounds : Bool := false) : MetaM (List MVarId) := do
  let closeSub (sg : MVarId) : MetaM Bool := do if ← tryCloseBasic sg (reducibleOnly := true) then pure true else tryCloseStringAllGoal sg
  return (← foldlMeta gs.toArray #[] fun acc g => do
    match ← decomposeStringEqs g with
    | none => pure acc
    | some g1 =>
        let g2 ← if withLenBounds then assertStrMemLenBounds g1 else pure g1
        return acc ++ (← filterUnsolvedM closeSub (← splitGoalAnds g2)).toArray).toList

@[noinline] private def unfoldAndLinearSplitFn (g0 : MVarId) (fnConst : Name) (skipName? : Option Name := none) : MetaM (List MVarId) := do
  let initGs ← do
    let tgt := (← g0.withContext (instantiateMVars (← g0.getType))).consumeMData
    if match tgt.getAppFn with | .const c _ => c.toString.contains ".match_" | _ => false then
      match ← trySplitTarget g0 with | none => pure [g0] | some kids => filterMapGoalsM (tryPruneBranch · none) kids
    else pure [g0]
  let rec splitHyps (work done : List MVarId) : Nat → MetaM (List MVarId)
    | 0 => return done.reverse ++ work
    | fuel + 1 => match work with
        | [] => return done.reverse
        | g :: rest => do
            let nextHyp? ← g.withContext <| findLCtxDecl? (includeLet := false) fun d => do
              if skipName? == some d.userName then return none
              let ty ← instantiateMVars d.type; if !ty.getUsedConstants.contains fnConst then return none
              let optVar (e : Expr) := let e := e.consumeMData; if e.isAppOfArity ``Option.some 2 && e.getAppArgs[1]!.consumeMData.isFVar then some e.getAppArgs[1]!.consumeMData.fvarId! else none
              let substNm? ← match ty.consumeMData.eq?.bind fun (_, l, r) => optVar r |>.orElse fun _ => optVar l with
                | some fv => some <$> fv.getUserName | none => pure none
              return some (d.userName, substNm?)
            match nextHyp? with
            | none => splitHyps rest (g :: done) fuel
            | some (hNm, substNm?) => match ← unfoldConstIn g fnConst (some hNm) with
                | none => splitHyps rest done fuel | some gU => splitHyps ((← linearSplitHyp gU hNm substNm?) ++ rest) done fuel
  return (← foldlMeta (← splitHyps initGs [] 8).toArray #[] fun acc g => do
    if (← g.withContext (instantiateMVars (← g.getType))).getUsedConstants.contains fnConst then
      match ← unfoldConstIn g fnConst none with | none => pure acc | some gU => return acc ++ (← linearSplitTarget gU).toArray
    else pure (acc.push g)).toList

private def tryCloseFnAtom (g : MVarId) : MetaM Bool := do
  if ← tryCloseGroundKernel g (check := true) then return true
  tryCloseBasic g (reducibleOnly := true)
private def tryCloseFnOrContra (g : MVarId) : MetaM Bool := do if ← tryCloseContradiction g then pure true else tryCloseFnAtom g

@[noinline] private def tryCloseStrReprMem (memSimpCtx : Meta.Simp.Context) (memSimpSP : Meta.Simp.SimprocsArray) (g : MVarId) : MetaM Bool :=
  tryRestoreM false id do
    let rec go : Nat → List MVarId → MetaM Bool
      | 0, [] => pure true | 0, _ => pure false
      | _, [] => pure true
      | fuel + 1, g :: rest => do
          if ← tryCloseFnOrContra g then return ← go fuel rest
          match ← trySimpAll g memSimpCtx memSimpSP with
          | none => go fuel rest
          | some g1 =>
              if ← tryCloseFnOrContra g1 then return ← go fuel rest
              let orFv? ← g1.withContext <| findLCtxDecl? (includeLet := false) fun d => do
                return if (← instantiateMVars d.type).consumeMData.isAppOfArity ``Or 2 then some d.fvarId else none
              match orFv? with
              | some fv => go fuel ((← g1.cases fv).toList.map (·.mvarId) ++ rest)
              | none => return false
    go 16 [g]

@[noinline] private def instantiateMemForalls (g0 : MVarId) : MetaM MVarId := do
  let (memHyps, allHyps, existingTys) ← g0.withContext do
    let mhs ← collectLCtxDecls (includeLet := false) fun d => do
      let ty := (← instantiateMVars d.type).consumeMData
      if ty.isAppOfArity ``Membership.mem 5 then return some (d.toExpr, ty.getAppArgs[3]!.consumeMData, ty.getAppArgs[4]!.consumeMData)
      return none
    let ahs ← collectLCtxDecls (includeLet := false) fun d => do
      let ty := (← instantiateMVars d.type).consumeMData
      match ty with
      | .forallE _ _ (.forallE _ memTy _ _) _ =>
          let mC := memTy.consumeMData
          if mC.isAppOfArity ``Membership.mem 5 then return some (d.toExpr, mC.getAppArgs[3]!.consumeMData)
          return none
      | _ => return none
    let ex ← collectLCtxDecls (includeLet := false) fun d => some <$> instantiateMVars d.type
    return (mhs, ahs, ex.foldl (·.insert ·) ({} : Std.HashSet Expr))
  if memHyps.isEmpty || allHyps.isEmpty then return g0
  let (_, newFacts) ← g0.withContext <| foldlMeta allHyps (existingTys, (#[] : Array Expr)) fun (seen, acc) (hAll, allColl) =>
    foldlMeta memHyps (seen, acc) fun (sn, out) (hMem, memColl, elem) => do
      if ← isDefEqFast allColl memColl then
        let pf := mkApp2 hAll elem hMem
        if let some pfTy ← try some <$> (instantiateMVars (← Meta.inferType pf)) catch _ => pure none then
          if !sn.contains pfTy then return (sn.insert pfTy, out.push pf)
      return (sn, out)
  if newFacts.isEmpty then return g0
  return (← assertFacts g0 "_memInst" newFacts).1

@[noinline] private def splitOrHypsLoop : Nat → List MVarId → MetaM (List MVarId)
  | 0, gs => pure gs | _, [] => pure []
  | fuel + 1, g :: rest => do
      let orFv? ← g.withContext <| findLCtxDecl? (includeLet := false) fun d => do
        return if (← instantiateMVars d.type).consumeMData.isAppOfArity ``Or 2 then some d.fvarId else none
      match orFv? with
      | some fv => splitOrHypsLoop fuel ((← g.cases fv).toList.map (·.mvarId) ++ rest)
      | none => return g :: (← splitOrHypsLoop fuel rest)

@[noinline] private def splitAndOnlyHyps (g0 : MVarId) : Nat → MetaM MVarId
  | 0 => pure g0
  | fuel + 1 => do
      let nextG? ← g0.withContext <| findLCtxDecl? (includeLet := false) fun d => do
        let tC := (← instantiateMVars d.type).consumeMData
        if tC.isAppOfArity ``And 2 || tC.isAppOfArity ``Qed.Lang.QedAndProp 2 then
          tryRestoreM none Option.isSome do return ((← g0.cases d.fvarId)[0]?).map (·.mvarId)
        else return none
      match nextG? with | some g1 => splitAndOnlyHyps g1 fuel | none => pure g0

private def cmpLawSimpNames : Array Name := #[
  ``Bool.or_eq_true, ``Bool.and_eq_true, ``Bool.not_eq_true', ``Bool.not_eq_false',
  ``decide_eq_true_eq, ``decide_eq_false_iff_not, ``beq_iff_eq, ``bne_iff_ne,
  ``Qed.Lang.QedVal.val_id, ``Nat.not_le, ``Nat.not_lt, ``Int.not_le, ``Int.not_lt, ``or_assoc, ``and_assoc]

@[noinline] private def proveCmpLaw (goalTy : Expr) (leConst? : Option Name := none) : MetaM (Option Expr) := tryRestoreM none Option.isSome do
  let m ← if goalTy.hasFVar then Meta.mkFreshExprSyntheticOpaqueMVar goalTy
    else Meta.withLCtx {} {} (Meta.mkFreshExprSyntheticOpaqueMVar goalTy)
  let (_, g1) ← m.mvarId!.intros
  let some g1 ← (match leConst? with
    | some c => do
        let uCtx ← mkDynamicSimpCtx #[c] none (withEqns := false)
        simpGoalAllHyps g1 uCtx
    | none => pure (some g1))
    | return some (← instantiateMVars m)
  let dCtx ← mkEmptyDsimpCtx { zeta := true, zetaHave := true }
  let (cCtx, _) ← mkCachedSimpCtx "cmpLaw" cmpLawSimpNames { zetaDelta := false }
  let some g2 ← simpGoalAllHyps g1 dCtx (dsimpOnly := true) | return some (← instantiateMVars m)
  let some g3 ← simpGoalAllHyps g2 cCtx | return some (← instantiateMVars m)
  let orGs ← splitOrHypsLoop 8 [(← splitAndOnlyHyps g3 16)]
  let ok ← closeAllGoals (fun sg => do
    let sg ← splitAndOnlyHyps sg 16
    if ← tryCloseFnOrContra sg then return true
    if ← tryDirectOmega sg then return true
    if ← tryCloseNonlinear sg then return true
    match ← trySimpAll sg cCtx with
    | none => return true
    | some sg1 =>
        if ← tryCloseFnOrContra sg1 then return true
        if ← tryDirectOmega sg1 then return true
        tryCloseNonlinear sg1) orGs
  if ok then return some (← instantiateMVars m) else return none

@[noinline] private def tryProveCmpTransTotal (le : Expr) (cmpErrRef? : Option (IO.Ref (Option String)) := none) : MetaM (Option (Expr × Expr)) := do
  let leTy ← Meta.whnf (← Meta.inferType le)
  let .forallE _ α _ _ := leTy | return none
  let leConst? := le.consumeMData.getAppFn.consumeMData.constName?
  let transTy ← Meta.withLocalDeclD `_a α fun a => Meta.withLocalDeclD `_b α fun b => Meta.withLocalDeclD `_c α fun c => do
    let eqT (x y : Expr) := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool) (mkApp2 le x y) (mkConst ``Bool.true)
    Meta.mkForallFVars #[a, b, c] (Expr.forallE `_h1 (eqT a b) (Expr.forallE `_h2 (eqT b c) (eqT a c) .default) .default)
  let totalTy ← Meta.withLocalDeclD `_a α fun a => Meta.withLocalDeclD `_b α fun b => do
    let disj := mkApp2 (mkConst ``or) (mkApp2 le a b) (mkApp2 le b a)
    let eqT := mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool) disj (mkConst ``Bool.true)
    Meta.mkForallFVars #[a, b] eqT
  let some hTotal ← proveCmpLaw totalTy leConst? | do
    if let some r := cmpErrRef? then
      if (← r.get).isNone then
        r.set (some "custom comparator failed totality check (`cmp(a, b) || cmp(b, a)` must always be true; use `<=` instead of `<`, or pass a key function like `x => (x.a, Desc(x.b))` which is automatically a total order)")
    return none
  let some hTrans ← proveCmpLaw transTy leConst? | do
    if let some r := cmpErrRef? then
      if (← r.get).isNone then
        r.set (some "custom comparator failed transitivity check (`cmp(a, b) && cmp(b, c) -> cmp(a, c)` must always hold; consider a key function like `x => (x.a, Desc(x.b))` which is automatically transitive)")
    return none
  return some (hTrans, hTotal)

private def tryCloseOrdAntisymm (g : MVarId) : MetaM Bool := tryRestoreM false id <| g.withContext do
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  let some (_, lhs, rhs) := tgt.eq? | return false
  let leHyps ← collectLCtxDecls (includeLet := false) fun d => do
    let ty := (← instantiateMVars d.type).consumeMData
    if ty.isAppOfArity ``LE.le 4 then return some (d.toExpr, ty.getAppArgs[2]!, ty.getAppArgs[3]!)
    return none
  let mut h1? : Option Expr := none
  let mut h2? : Option Expr := none
  for (pf, a, b) in leHyps do
    if h1?.isNone then if ← isDefEqFast a lhs then if ← isDefEqFast b rhs then h1? := some pf
    if h2?.isNone then if ← isDefEqFast a rhs then if ← isDefEqFast b lhs then h2? := some pf
  if let (some h1, some h2) := (h1?, h2?) then
    if let some pf ← try some <$> Meta.mkAppM ``Std.le_antisymm #[h1, h2] catch _ => pure none then
      g.assign pf; return true
  return false

private def directCmpGoalSpecs : Array (Name × Nat × Name × Name × Bool) := #[
  (``Qed.qedIsSortedCmp, 5, ``Qed.qedSortCmp, ``Qed.qedIsSortedCmp_sortCmp, false),
  (``Qed.qedIsSortedDescCmp, 5, ``Qed.qedSortDescCmp, ``Qed.qedIsSortedDescCmp_sortDescCmp, false),
  (``Qed.qedIsMinOfCmp, 6, ``Qed.qedMinCmp, ``Qed.qedIsMinOfCmp_minCmp, true),
  (``Qed.qedIsMaxOfCmp, 6, ``Qed.qedMaxCmp, ``Qed.qedIsMaxOfCmp_maxCmp, true)]

private def extEqHarvestSpecs : Array (Name × Nat × Name × Name × Bool) := #[
  (``Qed.qedMinKey, 7, ``Qed.qedMinKey_mem, ``Qed.qedMinKey_le, false),
  (``Qed.qedMaxKey, 7, ``Qed.qedMaxKey_mem, ``Qed.qedMaxKey_ge, false),
  (``Qed.qedMinCmp, 5, ``Qed.qedMinCmp_mem, ``Qed.qedMinCmp_le, true),
  (``Qed.qedMaxCmp, 5, ``Qed.qedMaxCmp_mem, ``Qed.qedMaxCmp_ge, true)]

/-- Harvest facts from verified `min`/`max`/`sort`/`filter` expressions in local hypotheses and target,
    and directly discharge custom-comparator sortedness/extremum goals. Returns `none` if goal is closed. -/
@[noinline] private def assertCollectionOrdFacts (cmpErrRef? : Option (IO.Ref (Option String))) (g0 : MVarId) : MetaM (Option MVarId) := do
  let closedDirect ← g0.withContext do
    let tgt := (← instantiateMVars (← g0.getType)).consumeMData
    for (predNm, predAr, innerNm, lemNm, takesXs) in directCmpGoalSpecs do
      if tgt.isAppOfArity predNm predAr then
        let a := tgt.getAppArgs; let sub := a[3]!.consumeMData
        let le := if takesXs then a[5]! else a[4]!
        if sub.isAppOfArity innerNm 5 then
          let sa := sub.getAppArgs
          let xsOk ← if takesXs then isDefEqFast sa[3]! a[4]! else pure true
          if xsOk then if ← isDefEqFast sa[4]! le then
            if let some (hTr, hTo) ← tryProveCmpTransTotal le cmpErrRef? then
              g0.assign (← Meta.mkAppM lemNm #[sa[3]!, le, hTr, hTo]); return true
    return false
  if closedDirect then return none
  let newFacts ← g0.withContext do
    let existing ← collectLCtxDecls (includeLet := false) fun d => some <$> instantiateMVars d.type
    let seenInit := existing.foldl (·.insert ·) ({} : Std.HashSet Expr)
    let addPf (pf : Expr) (st : Std.HashSet Expr × Array Expr) : MetaM (Std.HashSet Expr × Array Expr) := do
      if let some ty ← try some <$> instantiateMVars (← Meta.inferType pf) catch _ => pure none then
        if !st.1.contains ty then return (st.1.insert ty, st.2.push pf)
      return st
    let mut acc : Std.HashSet Expr × Array Expr := (seenInit, #[])
    let eqHyps ← collectLCtxDecls (includeLet := false) fun d => do
      let ty := (← instantiateMVars d.type).consumeMData
      if let some (_, l, r) := ty.eq? then return some (d.toExpr, l.consumeMData, r.consumeMData)
      return none
    for (hPf, l, r) in eqHyps do
      let pair? : Option (Expr × Bool) :=
        if r.isAppOfArity ``Option.some 2 then some (l, false)
        else if l.isAppOfArity ``Option.some 2 then some (r, true)
        else none
      if let some (callE, needsSymm) := pair? then
        for (opNm, opAr, memLem, ordLem, needsCmp) in extEqHarvestSpecs do
          if callE.isAppOfArity opNm opAr then
            let orientedPf ← if needsSymm then Meta.mkEqSymm hPf else pure hPf
            if let some p1 ← try some <$> Meta.mkAppM memLem #[orientedPf] catch _ => pure none then acc ← addPf p1 acc
            if needsCmp then
              if let some (hTr, hTo) ← tryProveCmpTransTotal callE.getAppArgs[4]! cmpErrRef? then
                if let some p2 ← try some <$> Meta.mkAppM ordLem #[hTr, hTo, orientedPf] catch _ => pure none then acc ← addPf p2 acc
            else
              if let some p2 ← try some <$> Meta.mkAppM ordLem #[orientedPf] catch _ => pure none then acc ← addPf p2 acc
    let tgt ← instantiateMVars (← g0.getType)
    let filterTermsRef ← IO.mkRef (#[] : Array (Bool × Expr × Expr))
    for e in existing.push tgt do
      e.forEach fun sub => do
        let s := sub.consumeMData
        if !s.hasLooseBVars then
          if s.isAppOfArity ``Array.filter 5 then filterTermsRef.modify (·.push (true, s.getAppArgs[2]!, s.getAppArgs[1]!))
          else if s.isAppOfArity ``List.filter 3 then filterTermsRef.modify (·.push (false, s.getAppArgs[2]!, s.getAppArgs[1]!))
    for (isArr, xs, p) in (← filterTermsRef.get) do
      let lem := if isArr then ``Qed.Array.size_filter_le_self else ``Qed.List.length_filter_le_self
      if let some pf ← try some <$> Meta.mkAppM lem #[xs, p] catch _ => pure none then acc ← addPf pf acc
    return acc.2
  if newFacts.isEmpty then return some g0
  return some (← splitAndOnlyHyps (← assertFacts g0 "_ordFact" newFacts).1 16)

@[noinline] private def finishOrdBranch (memCtx : Meta.Simp.Context) (memSP : Meta.Simp.SimprocsArray)
    (cmpErrRef? : Option (IO.Ref (Option String))) (g0 : MVarId) : MetaM (List MVarId) := do
  let some g1 ← assertCollectionOrdFacts cmpErrRef? g0 | return []
  let some g2 ← simpGoalAllHyps g1 memCtx memSP | return []
  let fwd (g : MVarId) : MetaM MVarId := do splitAndOnlyHyps (← specializeImpHyps (← instantiateMemForalls g)) 16
  let rem ← foldlMeta (← splitGoalAnds g2).toArray #[] fun acc leaf => do
    let l1 ← splitAndOnlyHyps (← leaf.intros).2 16
    let some l1 ← assertCollectionOrdFacts cmpErrRef? l1 | return acc
    let some l2 ← simpGoalAllHyps l1 memCtx memSP | return acc
    let l2 ← fwd (← fwd (← splitAndOnlyHyps l2 16))
    if ← tryCloseFnOrContra l2 then return acc
    if ← tryDirectOmega l2 then return acc
    if ← tryCloseNonlinear l2 then return acc
    if ← tryCloseOrdAntisymm l2 then return acc
    return acc.push l2
  return rem.toList

@[noinline] private def finishFnSubgoal (fnSimpCtx : Meta.Simp.Context) (fnSimpSP : Meta.Simp.SimprocsArray)
    (cmpErrRef? : Option (IO.Ref (Option String)) := none) (sg : MVarId) : TacticM Unit := do
  let getMemCtx : MetaM (Meta.Simp.Context × Meta.Simp.SimprocsArray) :=
    mkCachedSimpCtx "fnMem" fnMemSimpNames { zetaDelta := false } #[``fnReduceStrLen]
  if ← goalHasStrRepr sg then
    let out ← foldlMeta (← linearSplitTarget sg).toArray #[] fun acc bg => do
      if ← tryCloseContradiction bg then return acc
      match ← simpGoalAllHyps bg fnSimpCtx fnSimpSP with
      | none => pure acc
      | some bg1 =>
          let rem ← filterUnsolvedM tryCloseFnAtom (← finishStringGoals [(← splitAndHypsGoal bg1 false 32).1] true)
          let rem' ← if rem.isEmpty then pure [] else do
            let (memCtx, memSP) ← getMemCtx
            filterUnsolvedM (tryCloseStrReprMem memCtx memSP) rem
          return acc ++ rem'.toArray
    setGoals out.toList; return
  let (memCtx, memSP) ← getMemCtx
  let some sg0 ← assertCollectionOrdFacts cmpErrRef? sg | setGoals []; return
  let some sg1 ← trySimpAll sg0 memCtx memSP | setGoals []; return
  let splitGs ← linearSplitTarget sg1
  let ordRem ← foldlMeta splitGs.toArray #[] fun acc bg => return acc ++ (← finishOrdBranch memCtx memSP cmpErrRef? bg).toArray
  setGoals ordRem.toList
  forEachGoal (closeSplitBranch #[] false (some (memCtx, memSP)) 3)
  if !(← getGoals).isEmpty then
    setGoals (← filterUnsolvedM (fun s => do if ← tryCloseStringAllGoal s then pure true else tryCloseFnAtom s) (← getGoals))

/-! ## Pure `for`-Loop Invariant Synthesis & Verification (Phase A + Phase B) -/

private structure FoundForLoop where
  rawExpr  : Expr
  elemTy   : Expr
  stateTy  : Expr
  retTy    : Expr
  xsList   : Expr
  origColl : Expr
  st0      : Expr
  body     : Expr
  isRange  : Bool
  userInv? : Option Expr

private def loopFnConstNames : Array Name :=
  #[``Qed.qedForFold, ``Qed.qedForFoldList, ``Qed.qedForFoldAnn, ``Qed.qedForRange, ``Qed.qedForRangeAnn]

private def exprHasLoopFn (e : Expr) : Bool :=
  e.getUsedConstants.any (loopFnConstNames.contains ·)

private def normalizeLoopList (elemTy xs : Expr) : Expr × Expr × Bool :=
  let x := xs.consumeMData
  if x.isAppOfArity ``Qed.QedIterable.toList 4 then
    let a := x.getAppArgs; let cTy := a[0]!.consumeMData; let coll := a[3]!.consumeMData
    if cTy.isAppOfArity ``Array 1 then (mkApp2 (mkConst ``Array.toList [0]) elemTy coll, coll, false)
    else if cTy.isAppOfArity ``List 1 then (coll, coll, false)
    else if cTy.isConstOf ``Qed.QedRange then (mkApp (mkConst ``Qed.QedRange.toList) coll, coll, true)
    else (x, coll, false)
  else if x.isAppOfArity ``Array.toList 2 then (x, x.getAppArgs[1]!.consumeMData, false)
  else if x.isAppOfArity ``Qed.QedRange.toList 1 then (x, x.getAppArgs[0]!.consumeMData, true)
  else (x, x, false)

private def matchForLoopExpr? (e : Expr) : Option FoundForLoop :=
  let eC := e.consumeMData
  if eC.hasLooseBVars then none
  else if eC.isAppOfArity ``Qed.qedForFoldAnn 7 then
    let a := eC.getAppArgs; let (xsList, origColl, isRange) := normalizeLoopList a[0]! a[3]!
    some { rawExpr := eC, elemTy := a[0]!, stateTy := a[1]!, retTy := a[2]!, xsList, origColl, st0 := a[4]!, body := a[5]!, isRange, userInv? := some a[6]! }
  else if eC.isAppOfArity ``Qed.qedForRangeAnn 6 then
    let a := eC.getAppArgs; let r := a[2]!.consumeMData
    some { rawExpr := eC, elemTy := mkConst ``Nat, stateTy := a[0]!, retTy := a[1]!, xsList := mkApp (mkConst ``Qed.QedRange.toList) r, origColl := r, st0 := a[3]!, body := a[4]!, isRange := true, userInv? := some a[5]! }
  else if eC.isAppOfArity ``Qed.qedForFold 8 then
    let a := eC.getAppArgs; let cTy := a[0]!.consumeMData; let elemTy := a[1]!; let coll := a[5]!.consumeMData
    let (xsList, isRange) :=
      if cTy.isAppOfArity ``Array 1 then (mkApp2 (mkConst ``Array.toList [0]) elemTy coll, false)
      else if cTy.isAppOfArity ``List 1 then (coll, false)
      else if cTy.isConstOf ``Qed.QedRange then (mkApp (mkConst ``Qed.QedRange.toList) coll, true)
      else (mkApp4 (mkConst ``Qed.QedIterable.toList) cTy elemTy a[4]! coll, false)
    some { rawExpr := eC, elemTy, stateTy := a[2]!, retTy := a[3]!, xsList, origColl := coll, st0 := a[6]!, body := a[7]!, isRange, userInv? := none }
  else if eC.isAppOfArity ``Qed.qedForFoldList 6 then
    let a := eC.getAppArgs; let (xsList, origColl, isRange) := normalizeLoopList a[0]! a[3]!
    some { rawExpr := eC, elemTy := a[0]!, stateTy := a[1]!, retTy := a[2]!, xsList, origColl, st0 := a[4]!, body := a[5]!, isRange, userInv? := none }
  else if eC.isAppOfArity ``Qed.qedForRange 5 then
    let a := eC.getAppArgs; let r := a[2]!.consumeMData
    some { rawExpr := eC, elemTy := mkConst ``Nat, stateTy := a[0]!, retTy := a[1]!, xsList := mkApp (mkConst ``Qed.QedRange.toList) r, origColl := r, st0 := a[3]!, body := a[4]!, isRange := true, userInv? := none }
  else none

/-- Bottom-up search over closed loop subexpressions so sequential loops prove Loop 1 before Loop 2,
    while nested loops inside a body lambda (referencing outer bvars) defer until the outer step. -/
private def findForLoopInExprAux : Nat → Expr → Option FoundForLoop
  | 0, _ => none
  | fuel + 1, e =>
      let eC := e.consumeMData
      let child? := match eC with
        | .app .. =>
            let args := eC.getAppArgs
            let rec scan : Nat → Option FoundForLoop
              | 0 => none
              | r + 1 =>
                  let i := args.size - (r + 1)
                  if h : i < args.size then (findForLoopInExprAux fuel args[i]).orElse fun _ => scan r else none
            (findForLoopInExprAux fuel eC.getAppFn).orElse fun _ => scan args.size
        | .letE _ _ v b _ => (findForLoopInExprAux fuel v).orElse fun _ => findForLoopInExprAux fuel b
        | .proj _ _ s => findForLoopInExprAux fuel s
        | .forallE _ d b _ => (findForLoopInExprAux fuel d).orElse fun _ => findForLoopInExprAux fuel b
        | .lam _ d b _ => (findForLoopInExprAux fuel d).orElse fun _ => findForLoopInExprAux fuel b
        | _ => none
      child?.orElse fun _ => matchForLoopExpr? eC

private def findForLoopInExpr? (e : Expr) : Option FoundForLoop := findForLoopInExprAux 128 e

private structure LoopFailDiag where
  kind          : Nat          -- 0 = init, 1 = step, 2 = after-loop
  hasUserInv    : Bool
  hasMultiMut   : Bool
  hasSeqLoop    : Bool
  hasNestedLoop : Bool
  usedFullColl  : Bool
  elemName      : Name
  failedGoalStr : String

private def invUsesFullCollQuantWithoutSeen (fl : FoundForLoop) (uInv : Expr) : Bool :=
  match uInv.consumeMData with
  | .lam _ _ b1 _ => match b1.consumeMData with
    | .lam _ _ body _ =>
        if countBVar 1 body > 0 then false
        else (body.find? fun sub =>
          let s := sub.consumeMData
          let isMemColl (m : Expr) :=
            let mC := m.consumeMData
            (mC.isAppOfArity ``Membership.mem 5 && mC.getAppArgs[3]!.consumeMData == fl.origColl) ||
            (mC.isAppOfArity ``Qed.Lang.QedMemProp.memProp 5 && mC.getAppArgs[4]!.consumeMData == fl.origColl)
          let isQuantColl := match s with
            | .forallE _ _ (.forallE _ memTy _ _) _ => isMemColl memTy
            | _ => s.isAppOfArity ``Exists 2 && match s.getAppArgs[1]!.consumeMData with
                | .lam _ _ b _ => (b.isAppOfArity ``And 2 || b.isAppOfArity ``Qed.Lang.QedAndProp 2) && isMemColl b.getAppArgs[0]!
                | _ => false
          isQuantColl || (s.isAppOfArity ``Array.size 2 && s.getAppArgs[1]!.consumeMData == fl.origColl) ||
            (s.isAppOfArity ``List.length 2 && s.getAppArgs[1]!.consumeMData == fl.xsList)).isSome
    | _ => false
  | _ => false

@[noinline] private def replaceIterWithSeen (fl : FoundForLoop) (seenFv : Expr) (e : Expr) (extraColls : Array Expr := #[]) : MetaM Expr :=
  let seenLen := mkApp2 (mkConst ``List.length [0]) fl.elemTy seenFv
  let mk1Stop? : Option Expr :=
    if fl.origColl.isAppOfArity ``Qed.QedRange.mk1 1 then some fl.origColl.getAppArgs[0]!.consumeMData else none
  let isTargetColl (c : Expr) : Bool := c == fl.origColl || extraColls.any (· == c)
  Meta.transform e (pre := fun sub => do
    let s := sub.consumeMData
    if s == fl.xsList then return .done seenFv
    if s == fl.origColl && fl.origColl == fl.xsList then return .done seenFv
    if s.isAppOfArity ``Membership.mem 5 && isTargetColl s.getAppArgs[3]!.consumeMData then
      return .visit (← Meta.mkAppM ``Membership.mem #[seenFv, s.getAppArgs[4]!])
    if (s.isAppOfArity ``Qed.qedMinKey 7 || s.isAppOfArity ``Qed.qedMaxKey 7) && isTargetColl s.getAppArgs[5]!.consumeMData then
      let a := s.getAppArgs; let isMax := s.isAppOfArity ``Qed.qedMaxKey 7
      let leLam ← Meta.withLocalDeclD `_a fl.elemTy fun aFv => Meta.withLocalDeclD `_b fl.elemTy fun bFv => do
        let ka := a[6]!.beta #[aFv]; let kb := a[6]!.beta #[bFv]
        let cmp := if isMax then mkApp4 (mkConst ``Qed.QedOrd.leB) a[2]! a[4]! kb ka else mkApp4 (mkConst ``Qed.QedOrd.leB) a[2]! a[4]! ka kb
        Meta.mkLambdaFVars #[aFv, bFv] cmp
      return .done (← Meta.mkAppM ``Qed.qedMinListBy #[leLam, seenFv])
    if s.isAppOfArity ``Array.size 2 && s.getAppArgs[1]!.consumeMData == fl.origColl then return .done seenLen
    if s.isAppOfArity ``List.length 2 && s.getAppArgs[1]!.consumeMData == fl.xsList then return .done seenLen
    if s.isAppOfArity ``Array.isEmpty 2 && s.getAppArgs[1]!.consumeMData == fl.origColl then
      return .done (mkApp2 (mkConst ``List.isEmpty [0]) fl.elemTy seenFv)
    if s.isAppOfArity ``Qed.QedRange.count 1 && s.getAppArgs[0]!.consumeMData == fl.origColl then return .done seenLen
    if let some stopE := mk1Stop? then if s == stopE then return .done seenLen
    return .continue)

/-- Find upstream collections `sup` linked to `fl.origColl` via a local hyp `∀ x ∈ sup, ... → x ∈ fl.origColl`. -/
@[noinline] private def findSupCollsForLoop (fl : FoundForLoop) : MetaM (Array Expr) := do
  let memTarget (e : Expr) : Bool :=
    (e.find? fun sub =>
      let s := sub.consumeMData
      s.isAppOfArity ``Membership.mem 5 &&
        (s.getAppArgs[3]!.consumeMData == fl.origColl || s.getAppArgs[3]!.consumeMData == fl.xsList)).isSome
  collectLCtxDecls (includeLet := false) fun d => do
    let ty := (← instantiateMVars d.type).consumeMData
    match ty with
    | .forallE _ _ (.forallE _ memTy body _) _ =>
        let mC := memTy.consumeMData
        if mC.isAppOfArity ``Membership.mem 5 then
          let sup := mC.getAppArgs[3]!.consumeMData
          if sup != fl.origColl && sup != fl.xsList && memTarget body then return some sup
        return none
    | _ => return none

private def findNoneOptProjAux : Nat → Expr → Expr → List (Expr × Expr × (Expr → Expr))
  | 0, _, _ => []
  | fuel + 1, st0, stExpr =>
      let s0 := st0.consumeMData
      if s0.isAppOfArity ``Option.none 1 then
        let β := s0.getAppArgs[0]!
        [(stExpr, β, fun b => mkApp2 (mkConst ``Option.some [0]) β b)]
      else if s0.isAppOfArity ``Prod.mk 4 then
        let a := s0.getAppArgs
        let fstE := mkApp3 (mkConst ``Prod.fst [0, 0]) a[0]! a[1]! stExpr
        let sndE := mkApp3 (mkConst ``Prod.snd [0, 0]) a[0]! a[1]! stExpr
        ((findNoneOptProjAux fuel a[2]! fstE).map fun (p, β, mk) => (p, β, fun b => mkApp4 (mkConst ``Prod.mk [0, 0]) a[0]! a[1]! (mk b) sndE)) ++
        ((findNoneOptProjAux fuel a[3]! sndE).map fun (p, β, mk) => (p, β, fun b => mkApp4 (mkConst ``Prod.mk [0, 0]) a[0]! a[1]! fstE (mk b)))
      else []

private def findNoneOptProj (st0 stExpr : Expr) : List (Expr × Expr × (Expr → Expr)) := findNoneOptProjAux 16 st0 stExpr

private def collectSeenForallNoneGuardsAux (seenFv bFv : Expr) : Nat → Expr → Array Expr
  | 0, _ => #[]
  | fuel + 1, e =>
      let eC := e.consumeMData
      if eC.isAppOfArity ``And 2 then
        collectSeenForallNoneGuardsAux seenFv bFv fuel eC.getAppArgs[0]! ++ collectSeenForallNoneGuardsAux seenFv bFv fuel eC.getAppArgs[1]!
      else match eC with
        | .forallE xNm xTy (.forallE hNm memTy body bi2) bi1 =>
            let mC := memTy.consumeMData
            if mC.isAppOfArity ``Membership.mem 5 && mC.getAppArgs[3]!.consumeMData == seenFv then
              match body.consumeMData with
              | .forallE _ guardTy concl _ =>
                  if !concl.hasLooseBVar 0 && !guardTy.containsFVar bFv.fvarId! then
                    #[Expr.forallE xNm xTy (Expr.forallE hNm memTy (mkNot guardTy) bi2) bi1]
                  else #[]
              | _ =>
                  if body.containsFVar bFv.fvarId! then
                    #[Expr.forallE xNm xTy (Expr.forallE hNm memTy (mkConst ``False) bi2) bi1]
                  else #[]
            else #[]
        | _ => #[]

private def collectSeenForallNoneGuards (seenFv bFv e : Expr) : Array Expr := collectSeenForallNoneGuardsAux seenFv bFv 32 e

@[noinline] private def mkInvPairFromPost (fl : FoundForLoop) (seenFv stFv postWithSeen : Expr) : MetaM (Expr × Option Expr) := do
  let baseLam ← Meta.mkLambdaFVars #[seenFv, stFv] postWithSeen
  let (someNormCtx, _) ← mkCachedSimpCtx "invSomeNorm" #[``Option.some.injEq, ``forall_eq, ``forall_eq',
    ``reduceCtorEq, ``false_implies, ``true_implies, ``true_and, ``and_true] { zetaDelta := false }
  let strExtras ← foldlMeta (findNoneOptProj fl.st0 stFv).toArray #[] fun acc (optProj, β, mkSome) => do
    Meta.withLocalDeclD `_bOpt β fun bFv => do
      let atSome0 := (postWithSeen.abstract #[stFv]).instantiate1 (mkSome bFv)
      let atSome1 := (← Meta.dsimp atSome0 (← mkEmptyDsimpCtx { zeta := true, zetaHave := true })).1
      let atSome := (← Meta.simp atSome1 someNormCtx).1.expr
      let guards := collectSeenForallNoneGuards seenFv bFv atSome
      if guards.isEmpty then return acc
      let conjG := guards.extract 1 guards.size |>.foldl (init := guards[0]!) fun a b => mkApp2 (mkConst ``And) a b
      let noneVal ← Meta.mkAppOptM ``Option.none #[some β]
      let eqNone ← Meta.mkEq optProj noneVal
      return acc.push (Expr.forallE `_hNone eqNone conjG .default)
  let strLam? ← if strExtras.isEmpty then pure none else do
    let fullBody := strExtras.foldl (init := postWithSeen) fun a b => mkApp2 (mkConst ``And) a b
    some <$> Meta.mkLambdaFVars #[seenFv, stFv] fullBody
  return (baseLam, strLam?)

@[noinline] private def synthesizeLoopInvs (fl : FoundForLoop) (predP : Expr) : MetaM (Array Expr) := do
  let mut cands : Array Expr := #[]
  if let some uInv := fl.userInv? then cands := cands.push uInv
  let supColls ← findSupCollsForLoop fl
  let autoPairs : Array (Expr × Option Expr) ← tryRestoreM #[] (fun a => !a.isEmpty) do
    Meta.withLocalDeclD `seen (mkApp (mkConst ``List [0]) fl.elemTy) fun seenFv =>
      Meta.withLocalDeclD `_loopSt fl.stateTy fun stFv => do
        let noneE ← Meta.mkAppOptM ``Option.none #[some fl.retTy]
        let pairE ← Meta.mkAppM ``Prod.mk #[stFv, noneE]
        let raw0 := predP.beta #[pairE]
        let (normCtx, _) ← mkCachedSimpCtx "loopSynNorm" (ordDispatchSimpNames ++ #[``Qed.Lang.QedMemProp.memProp_array, ``Qed.Lang.QedMemProp.memProp_list,
          ``Qed.Lang.QedVal.val_id, ``Qed.qedIterable_toList_array, ``Qed.qedIterable_toList_list, ``Qed.qedIterable_toList_range,
          ``Qed.QedSeq.toList_array, ``Qed.QedSeq.toList_list, ``Array.mem_toList_iff,
          ``Qed.Array.forall_mem_filter, ``Qed.Array.exists_mem_filter, ``Qed.List.forall_mem_filter, ``Qed.List.exists_mem_filter,
          ``Array.mem_filter, ``List.mem_filter,
          ``Qed.QedOrd.le_nat, ``Qed.QedOrd.le_int, ``Qed.QedOrd.le_char, ``Qed.QedOrd.le_string, ``Qed.QedOrd.le_bool,
          ``Qed.QedOrd.le_desc, ``Qed.QedOrd.le_desc_mk, ``Qed.QedOrd.le_prod,
          ``Bool.and_eq_true, ``Bool.or_eq_true, ``decide_eq_true_eq, ``decide_eq_false_iff_not, ``beq_iff_eq, ``bne_iff_ne,
          ``and_true, ``true_and]) { zetaDelta := false }
        let raw1 := (← Meta.simp raw0 normCtx).1.expr
        if exprHasLoopFn raw1 then return #[]
        let postWithSeen ← replaceIterWithSeen fl seenFv raw1
        let basePair ← mkInvPairFromPost fl seenFv stFv postWithSeen
        let mut pairs : Array (Expr × Option Expr) := #[]
        if !supColls.isEmpty then
          let postSup ← replaceIterWithSeen fl seenFv raw1 supColls
          if postSup != postWithSeen then
            pairs := pairs.push (← mkInvPairFromPost fl seenFv stFv postSup)
        pairs := pairs.push basePair
        return pairs
  let combineWithUser (aLam : Expr) : MetaM Expr := match fl.userInv? with
    | none => pure aLam
    | some uInv => Meta.withLocalDeclD `seen (mkApp (mkConst ``List [0]) fl.elemTy) fun seenFv =>
        Meta.withLocalDeclD `_loopSt fl.stateTy fun stFv =>
          Meta.mkLambdaFVars #[seenFv, stFv] (mkApp2 (mkConst ``And) (uInv.beta #[seenFv, stFv]) (aLam.beta #[seenFv, stFv]))
  -- Try the Option-strengthened invariant before `baseLam` when present (since `∀ x ∈ seen` under `some b`
  -- requires the `none → ∀ x ∈ seen, ¬ guard` clause on the first match).
  for (baseLam, strLam?) in autoPairs do
    if let some sLam := strLam? then cands := cands.push (← combineWithUser sLam)
    cands := cands.push (← combineWithUser baseLam)
  return cands

private def extractMutVarNames (body : Expr) : Array Name :=
  let rec goLam : Nat → Expr → Array Name → Array Name
    | 0, _, acc => acc
    | fuel + 1, e, acc => match e.consumeMData with
        | .lam nm _ rest _ => goLam fuel rest (acc.push nm.eraseMacroScopes)
        | _ => acc
  match body.consumeMData with
  | .lam stNm _ b1 _ =>
      let stClean := stNm.eraseMacroScopes
      if !stClean.toString.startsWith "_qedSt" && stClean != `_ then #[stClean]
      else match b1.consumeMData with
        | .lam _ _ b _ =>
            let bC := b.consumeMData
            match bC.getAppFn.consumeMData with
            | .const c _ =>
                let args := bC.getAppArgs
                if c == ``Prod.casesOn || c == ``Prod.rec || c.toString.contains ".match_" then
                  match args.reverse.find? (·.consumeMData.isLambda) with
                  | some lamE => goLam 16 lamE #[]
                  | none => #[]
                else #[]
            | _ => #[]
        | _ => #[]
  | _ => #[]

@[noinline] private def unpackProdFVars (g : MVarId) (fv : FVarId) (mutNames : Array Name := #[]) (idx : Nat := 0) : Nat → MetaM MVarId
  | 0 => pure g
  | fuel + 1 => do
      let ty ← g.withContext do Meta.whnf (← fv.getType)
      if ty.isAppOfArity ``Prod 2 then
        let rightIsProd ← g.withContext do return (← Meta.whnf ty.getAppArgs[1]!).isAppOfArity ``Prod 2
        let n0 := mutNames.getD idx `_st
        let n1 := if rightIsProd then `_loopSt else mutNames.getD (idx + 1) `_st
        match ← tryRestoreM none Option.isSome (do return (← g.cases fv #[{ explicit := false, varNames := [n0, n1] }])[0]?) with
        | some sub =>
            let g1 ← unpackProdFVars sub.mvarId sub.fields[0]!.fvarId! mutNames idx fuel
            unpackProdFVars g1 sub.fields[1]!.fvarId! mutNames (idx + 1) fuel
        | none => pure g
      else pure g

@[noinline] private def assertLoopStepFacts (fl : FoundForLoop) (g0 : MVarId) (hEqFv : FVarId) : MetaM MVarId := do
  let mut facts : Array Expr := #[]
  let hEqE := mkFVar hEqFv
  let (hMemList?, g) ← g0.withContext do
    if let some hm ← try some <$> Meta.mkAppM ``Qed.mem_of_append_cons #[hEqE] catch _ => pure none then
      let mut fs := #[hm]
      if fl.xsList.isAppOfArity ``Array.toList 2 then
        if let some hArr ← try some <$> Meta.mkAppM ``Qed.mem_array_of_mem_toList #[hm] catch _ => pure none then
          fs := fs.push hArr
      if let some hPfx ← try some <$> Meta.mkAppM ``Qed.mem_of_prefix_append_cons #[hEqE] catch _ => pure none then
        fs := fs.push hPfx
      if fl.isRange then
        if let some hBnd ← try some <$> Meta.mkAppM ``Qed.QedRange.mem_toList_bounds #[fl.origColl, hm] catch _ => pure none then
          fs := fs.push hBnd
        if let some hIdx ← try some <$> Meta.mkAppM ``Qed.QedRange.prefix_elem_toList #[fl.origColl, hEqE] catch _ => pure none then
          fs := fs.push hIdx
      return (some fs, g0)
    return (none, g0)
  if let some fs := hMemList? then facts := fs
  if facts.isEmpty then return g else return (← splitAndHypsGoal (← assertFacts g "_loopFact" facts).1 false 16).1

@[noinline] private def formatLoopFailDiag (fnId thmId : Ident) (isInvOnly : Bool) (d : LoopFailDiag) : TacticM Unit := do
  let hdr := if isInvOnly then s!"loop `invariant` failed in `{fnId.getId}`" else s!"`ensures` contract failed for `{fnId.getId}`"
  let phaseMsg := match d.kind with
    | 0 => "loop invariant failed before the first iteration (`seen = []`)"
    | 1 => s!"loop invariant was not preserved on an iteration step (`seen` -> `seen ++ [{d.elemName}]`)"
    | 2 => "loop invariant held, but was not strong enough to prove `ensures` after the loop"
    | _ => s!"could not automatically synthesize a loop invariant for `for {d.elemName} in ...:`"
  let mut notes : Array String := #[]
  if d.usedFullColl then
    notes := notes.push "  Note: this loop `invariant` quantifies over the full collection without referencing `seen` (elements processed so far). Mid-loop invariants usually need `seen` instead."
  if d.hasNestedLoop then
    notes := notes.push "  Note: this loop body contains an inner `for` loop; add an `invariant <expr>` inside the inner `for` loop too."
  if d.hasSeqLoop then
    notes := notes.push (if d.kind == 2 then "  Note: another `for` loop follows this one; add an `invariant <expr>` inside the next `for` loop."
      else "  Note: this function has multiple `for` loops; add an `invariant <expr>` inside the first `for` loop to describe its output state.")
  if !d.hasUserInv && d.hasMultiMut then
    notes := notes.push "  Note: this `for` loop updates multiple `let mut` variables; add an `invariant <expr>` inside the `for` loop relating them (e.g. linking auxiliary state to the returned value)."
  let hint := match d.kind, d.hasUserInv with
    | 0, true  => "Hint: Check initial `let mut` values before the loop or weaken the `invariant` when `seen` is empty."
    | 0, false => "Hint: Add an explicit `invariant <expr>` inside the `for` loop (use `seen` for elements processed so far), fix the initial state, or supply a `prove:` block."
    | 1, true  => "Hint: Strengthen or adjust the loop `invariant` (use `seen` for elements processed so far), fix the loop body, or attach a `prove:` block to the `invariant`."
    | 1, false => "Hint: Add an explicit `invariant <expr>` inside the `for` loop (use `seen` for elements processed so far), fix the loop body, or supply a `prove:` block."
    | 2, true  => "Hint: Strengthen the loop `invariant` (e.g. using `seen` so it implies `ensures` at loop exit) or supply a `prove:` block."
    | 2, false => "Hint: Add an `invariant <expr>` inside the `for` loop (use `seen` for elements processed so far) so the prover can carry facts across the loop."
    | _, _     => "Hint: Add an `invariant <expr>` inside the `for` loop (use `seen` for elements processed so far) describing what holds after each iteration."
  let goalLine := if d.failedGoalStr.isEmpty then "" else s!":\n      must satisfy:  {d.failedGoalStr}"
  let noteBlock := if notes.isEmpty then "" else "\n" ++ String.intercalate "\n" notes.toList
  throwErrorAt thmId s!"{hdr}:\n  • {phaseMsg}{goalLine}{noteBlock}\n\n{hint}"

@[noinline] private def splitLoopSafeTargets (dCtx : Meta.Simp.Context) : Nat → List MVarId → MetaM (List MVarId)
  | 0, gs => pure gs | _, [] => pure []
  | fuel + 1, g :: rest => do
      let tgt ← g.withContext do instantiateMVars (← g.getType)
      let fl? := findForLoopInExpr? tgt
      let saved ← saveState
      match ← trySplitTarget g with
      | none => return g :: (← splitLoopSafeTargets dCtx fuel rest)
      | some sub =>
          let keepSplit ← match fl? with
            | none => pure true
            | some fl => do
                let hasNeedle (e : Expr) : Bool := (e.find? (· == fl.rawExpr)).isSome
                foldlMeta sub.toArray false fun ok sg => do
                  if ok then return true
                  sg.withContext do return hasNeedle (← instantiateMVars (← sg.getType))
          if !keepSplit then
            restoreState saved
            return g :: (← splitLoopSafeTargets dCtx fuel rest)
          let sub' ← sub.filterMapM (simpGoalAllHyps · dCtx (dsimpOnly := true))
          splitLoopSafeTargets dCtx fuel (sub' ++ rest)

@[noinline] private def findUsefulOptionFVar? (g : MVarId) : MetaM (Option FVarId) :=
  g.withContext do
    let optFvs ← collectLCtxDecls (includeLet := false) fun d => do
      if (← Meta.whnf d.type).isAppOfArity ``Option 1 then return some d.fvarId
      return none
    if optFvs.isEmpty then return none
    let exprUsesOpt (fv : FVarId) (e : Expr) : Bool :=
      (e.find? fun sub =>
        let s := sub.consumeMData
        let head := s.getAppFn.consumeMData
        let args := s.getAppArgs
        match head with
        | .const c _ =>
            (c == ``Option.casesOn || c == ``Option.rec || c == ``Option.isNone || c == ``Option.isSome ||
             c == ``Eq || c.toString.contains ".match_") &&
            args.any (fun a => a.consumeMData == mkFVar fv)
        | _ => false).isSome
    let tgt ← instantiateMVars (← g.getType)
    let hyps ← collectLCtxDecls (includeLet := false) fun d => some <$> instantiateMVars d.type
    for fv in optFvs do
      if exprUsesOpt fv tgt || hyps.any (exprUsesOpt fv) then return some fv
    return none

@[noinline] private def deltaReduceMatchHyps (g0 : MVarId) : MetaM MVarId := do
  let isMatchConst (c : Name) : Bool :=
    let s := c.toString; s.contains ".match_" || s.contains "._sparseCasesOn_"
  let fvs ← g0.withContext <| collectLCtxDecls (includeLet := false) fun d => do
    let ty ← instantiateMVars d.type
    return if ty.getUsedConstants.any isMatchConst then some d.fvarId else none
  foldlMeta fvs g0 fun g fv => g.withContext do
    let ty ← instantiateMVars (← fv.getType)
    let ty' ← Meta.deltaExpand ty isMatchConst
    if ty' != ty then g.replaceLocalDeclDefEq fv ty' else pure g

private structure LoopProveCtx where
  dCtx         : Meta.Simp.Context
  loopCtx      : Meta.Simp.Context
  loopSP       : Meta.Simp.SimprocsArray
  userTacs     : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq)
  onlyInvCheck : Bool
  diagRef      : IO.Ref (Option LoopFailDiag)

private def loopElemName (body : Expr) : Name :=
  match body.consumeMData with
  | .lam _ _ b1 _ => match b1.consumeMData with | .lam nm _ _ _ => nm.eraseMacroScopes | _ => `x
  | _ => `x

private def tryCloseLoopInvCheck (g : MVarId) : MetaM Bool := do
  let tgt := (← g.withContext do instantiateMVars (← g.getType)).consumeMData
  if tgt.isAppOfArity ``Qed.QedLoopInvCheck 2 && !exprHasLoopFn tgt then
    g.assign (mkApp2 (mkConst ``Qed.qedLoopInvCheck_intro) tgt.getAppArgs[0]! tgt.getAppArgs[1]!)
    return true
  return false

private def mkLoopProveCtx (userTacs : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq)) (onlyInvCheck : Bool)
    (diagRef : IO.Ref (Option LoopFailDiag)) : MetaM LoopProveCtx := do
  let dCtx ← mkEmptyDsimpCtx { zeta := true, zetaHave := true }
  let (loopCtx, loopSP) ← mkCachedSimpCtx "fnLoop" loopSimpNames { zetaDelta := false } #[``fnReduceStrLen]
  return { dCtx, loopCtx, loopSP, userTacs, onlyInvCheck, diagRef }

mutual
@[noinline] private partial def closeLoopLeaf (ctx : LoopProveCtx) (depth optFuel : Nat)
    (allowStdFallback : Bool) (g0 : MVarId) : TacticM (Option MVarId) := do
  let checkQuick (g : MVarId) : MetaM Bool := do
    if ← tryCloseFnOrContra g then return true
    if ← tryCloseNonlinear g then return true
    if ← tryDirectOmega g then return true
    tryCloseOrdAntisymm g
  let fwdClose (g : MVarId) : MetaM (Option MVarId) := do
    let g ← instantiateMemForalls g
    let g ← specializeImpHyps g
    let g ← splitAndOnlyHyps g 16
    if ← checkQuick g then return none else return some g
  if ← checkQuick g0 then return none
  let (_, g1) ← g0.intros
  let g1 ← splitAndOnlyHyps g1 24
  let orGs ← splitOrHypsLoop 8 [g1]
  foldlT orGs.toArray (none : Option MVarId) fun firstFail? sg => do
    if firstFail?.isSome then return firstFail?
    let sg ← splitAndOnlyHyps sg 16
    if ← checkQuick sg then return none
    let some sg ← assertCollectionOrdFacts none sg | return none
    -- Run forward chaining BEFORE splitting `Exists` so `(∃ x ∈ seen, P x) → ...` matches directly.
    let sg ← splitAndOnlyHyps (← specializeImpHyps sg) 16
    if ← checkQuick sg then return none
    let some sg ← fwdClose sg | return none
    let some sg ← fwdClose (← splitAndHypsGoal sg true 16).1 | return none
    match ← trySimpAll sg ctx.loopCtx ctx.loopSP with
    | none => return none
    | some sg1 =>
        let (_, sg1) ← sg1.intros
        let some sg1 ← assertCollectionOrdFacts none sg1 | return none
        let some sg1 ← simpGoalAllHyps sg1 ctx.loopCtx ctx.loopSP | return none
        let some sg1 ← fwdClose (← splitAndOnlyHyps sg1 16) | return none
        if ctx.onlyInvCheck then if ← tryCloseLoopInvCheck sg1 then return none
        if depth > 0 then
          if ← proveForLoopsInGoal ctx (depth - 1) sg1 then return none
        let tgt1 := (← sg1.withContext do instantiateMVars (← sg1.getType)).consumeMData
        -- Case-split an unsplit `Option` state variable (e.g. `if best.isNone or sc > bestScore:`).
        if optFuel > 0 && !exprHasLoopFn tgt1 then
          if let some optFv ← findUsefulOptionFVar? sg1 then
            let optSolved ← tryRestoreM false id do
              let subs ← sg1.cases optFv
              foldlT subs true fun ok sub => do
                if !ok then return false
                let b0 ← deltaReduceMatchHyps sub.mvarId
                let some b1 ← simpGoalAllHyps b0 ctx.dCtx (dsimpOnly := true) | return true
                let some b2 ← simpGoalAllHyps b1 ctx.loopCtx ctx.loopSP | return true
                return (← closeLoopLeaf ctx depth (optFuel - 1) false b2).isNone
            if optSolved then return none
        -- Try user-supplied `prove:` tactics on this loop subgoal.
        let closedByUser ← foldlT ctx.userTacs false fun ok tacSeq => do
          if ok then return true
          tryRestoreM false id do setGoals [sg1]; withoutRecover <| evalTactic tacSeq; return (← getGoals).isEmpty
        if closedByUser then return none
        -- Final fallback through Qed's standard branch closer (only when no unproved loop remains in target).
        if allowStdFallback && !exprHasLoopFn tgt1 then
          let closedByStd ← tryRestoreM false id do
            setGoals [sg1]; closeSplitBranch #[] false (some (ctx.loopCtx, ctx.loopSP)) 2 #[] sg1; return (← getGoals).isEmpty
          if closedByStd then return none
        return some sg1

@[noinline] private partial def closeLoopVC (fl : FoundForLoop) (ctx : LoopProveCtx) (depth kind : Nat) (g0 : MVarId) : TacticM (Option MVarId) := do
  -- kind: 0 = init, 1 = step, 2 = done
  let mutNames := extractMutVarNames fl.body
  let stIntroNm := if mutNames.size == 1 then mutNames[0]! else `_loopSt
  let g1 ← match kind with
    | 1 => do
        let (fvs, gI) ← g0.introN 6 [`seen, loopElemName fl.body, `_rest, stIntroNm, `_hLoopEq, `_hLoopInv]
        let gU ← unpackProdFVars gI fvs[3]! mutNames 0 8
        assertLoopStepFacts fl gU fvs[4]!
    | 2 => do
        let (fvs, gI) ← g0.introN 2 [stIntroNm, `_hLoopInv]
        unpackProdFVars gI fvs[0]! mutNames 0 8
    | _ => pure g0
  let some g2 ← simpGoalAllHyps g1 ctx.dCtx (dsimpOnly := true) | return none
  let some g3 ← simpGoalAllHyps g2 ctx.loopCtx ctx.loopSP | return none
  let some g3 ← do
    if kind == 2 then
      let needsMinBridge ← g3.withContext do
        let tgtConsts := (← instantiateMVars (← g3.getType)).getUsedConstants
        if tgtConsts.contains ``Qed.qedMinKey || tgtConsts.contains ``Qed.qedMaxKey then
          return (← findLCtxDecl? (includeLet := false) fun d => do
            return if (← instantiateMVars d.type).getUsedConstants.contains ``Qed.qedMinListBy then some () else none).isSome
        return false
      if needsMinBridge then
        let (bCtx, _) ← mkCachedSimpCtx "loopMinDone" #[``Qed.qedMinKey_array_eq, ``Qed.qedMinKey_list_eq,
          ``Qed.qedMaxKey_array_eq, ``Qed.qedMaxKey_list_eq] { zetaDelta := false }
        simpGoalOnly g3 bCtx
      else pure (some g3)
    else pure (some g3)
    | return none
  let mut preDiag? : Option LoopFailDiag := none
  if depth > 0 then
    if exprHasLoopFn (← g3.withContext do instantiateMVars (← g3.getType)) then
      let tmpDiag ← IO.mkRef (none : Option LoopFailDiag)
      if ← proveForLoopsInGoal { ctx with diagRef := tmpDiag } (depth - 1) g3 then return none
      preDiag? ← tmpDiag.get
  let splitGs ← splitLoopSafeTargets ctx.dCtx 32 [g3]
  let flatGs ← foldlMeta splitGs.toArray (#[] : Array MVarId) fun acc sg => do
    match ← simpGoalAllHyps sg ctx.loopCtx ctx.loopSP with
    | none => return acc
    | some sg1 => return acc ++ (← splitGoalAnds sg1).toArray
  let fail? ← foldlT flatGs (none : Option MVarId) fun fail? leaf =>
    if fail?.isSome then pure fail? else closeLoopLeaf ctx depth 1 true leaf
  if fail?.isSome then
    if let some pd := preDiag? then
      if (← ctx.diagRef.get).isNone then
        ctx.diagRef.set (some { pd with hasNestedLoop := pd.hasNestedLoop || kind == 1, hasSeqLoop := pd.hasSeqLoop || kind == 2 })
  return fail?

@[noinline] private partial def proveForLoopsInGoal (ctx : LoopProveCtx) (depth : Nat) (g0 : MVarId) : TacticM Bool := do
  if depth == 0 then return false
  tryRestoreM false id do
    -- Substitute any local `h : res = <expr containing a for loop>` so the loop appears in the target.
    let gSub ← do
      let eqFv? ← g0.withContext <| findLCtxDecl? (includeLet := false) fun d => do
        let ty := (← instantiateMVars d.type).consumeMData
        if let some (_, l, r) := ty.eq? then
          if (l.consumeMData.isFVar && exprHasLoopFn r) || (r.consumeMData.isFVar && exprHasLoopFn l) then return some d.fvarId
        return none
      match eqFv? with
      | some fv => pure ((← trySubstFVar g0 fv).getD g0)
      | none => pure g0
    let some gZ ← simpGoalOnly gSub ctx.dCtx (dsimpOnly := true) | return true
    let tgt ← gZ.withContext do instantiateMVars (← gZ.getType)
    let some fl := findForLoopInExpr? tgt | return false
    let (predP, pfWrap?, hasSeqLoop, hasMultiMut, elemName, usedFullColl) ← gZ.withContext do
      let loopResTy ← Meta.mkAppM ``Prod #[fl.stateTy, ← Meta.mkAppM ``Option #[fl.retTy]]
      let bodyP ← Meta.kabstract tgt fl.rawExpr
      let p := Expr.lam `_loopRes loopResTy bodyP .default
      let hEq? ←
        if fl.rawExpr.isAppOfArity ``Qed.qedForRangeAnn 6 then
          some <$> Meta.mkAppM ``Qed.qedForRangeAnn_eq_foldList #[fl.origColl, fl.st0, fl.body, fl.userInv?.get!]
        else if fl.rawExpr.isAppOfArity ``Qed.qedForRange 5 then
          some <$> Meta.mkAppM ``Qed.qedForRange_eq_foldList #[fl.origColl, fl.st0, fl.body]
        else if fl.rawExpr.isAppOfArity ``Qed.qedForFoldAnn 7 then
          some <$> Meta.mkAppM ``Qed.qedForFoldAnn_eq_foldList #[fl.rawExpr.getAppArgs[3]!, fl.st0, fl.body, fl.userInv?.get!]
        else pure none
      let wrap? ← match hEq? with | some hEq => some <$> Meta.mkAppM ``congrArg #[p, hEq] | none => pure none
      let multiMut := (← Meta.whnf fl.stateTy).isAppOfArity ``Prod 2
      let fullColl := match fl.userInv? with | some uInv => invUsesFullCollQuantWithoutSeen fl uInv | none => false
      return (p, wrap?, exprHasLoopFn bodyP, multiMut, loopElemName fl.body, fullColl)
    let cands ← gZ.withContext do
      if ctx.onlyInvCheck then
        match fl.userInv? with
        | some uInv => pure #[uInv]
        | none => synthesizeLoopInvs fl predP
      else synthesizeLoopInvs fl predP
    let recordFail (kind : Nat) (failG : MVarId) : TacticM Unit := do
      let fTy ← failG.withContext do instantiateMVars (← failG.getType)
      let hasRawLoop := exprHasLoopFn fTy
      let nestedNow := kind == 1 && (hasRawLoop || exprHasLoopFn fl.body)
      let seqNow := hasSeqLoop || (kind == 2 && hasRawLoop)
      match ← ctx.diagRef.get with
      | some prev =>
          if nestedNow && !prev.hasNestedLoop then ctx.diagRef.set (some { prev with hasNestedLoop := true })
          else if seqNow && !prev.hasSeqLoop then ctx.diagRef.set (some { prev with hasSeqLoop := true })
      | none =>
          let fStr ← if kind == 3 || hasRawLoop then pure "" else failG.withContext do Qed.Diag.ppQedExpr fTy
          ctx.diagRef.set (some {
            kind, hasUserInv := fl.userInv?.isSome, hasMultiMut,
            hasSeqLoop := seqNow, hasNestedLoop := nestedNow,
            usedFullColl, elemName, failedGoalStr := fStr
          })
    if cands.isEmpty then
      recordFail 3 gZ
      return false
    foldlT cands false fun solved invI => do
      if solved then return true
      tryRestoreM false id do
        let (mInit, mStep, mDone, pfTerm) ← gZ.withContext do
          let specApp ← Meta.mkAppM ``Qed.qedForFoldList_spec #[fl.xsList, fl.st0, fl.body, invI, predP]
          let (mvars, _, _) ← Meta.forallMetaBoundedTelescope (← Meta.inferType specApp) 3
          if mvars.size != 3 then throwError "qedForFoldList_spec: expected 3 subgoals"
          let pf0 := mkAppN specApp mvars
          let pf ← match pfWrap? with | some hCong => Meta.mkAppM ``Eq.mpr #[hCong, pf0] | none => pure pf0
          return (mvars[0]!.mvarId!, mvars[1]!.mvarId!, mvars[2]!.mvarId!, pf)
        if let some f0 ← closeLoopVC fl ctx (depth - 1) 0 mInit then recordFail 0 f0; return false
        if let some f1 ← closeLoopVC fl ctx (depth - 1) 1 mStep then recordFail 1 f1; return false
        if let some f2 ← closeLoopVC fl ctx (depth - 1) 2 mDone then recordFail 2 f2; return false
        gZ.assign pfTerm
        return true
end

@[noinline] private def runProveFnGoal (fnId : Ident) (isBlind : Bool)
    (loopTacs : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq) := #[])
    (loopDiagRef? : Option (IO.Ref (Option LoopFailDiag)) := none)
    (cmpErrRef? : Option (IO.Ref (Option String)) := none) : TacticM Unit := do
  let fnConst? : Option Name ← try some <$> (realizeGlobalConstNoOverload fnId : CoreM Name) catch _ => pure none
  let g0 :: rest0 ← getGoals | return
  -- Fast path for pure `fn` containing `for` loops: keep `ensures` implications un-introduced so
  -- prefix generalization sees `(∃ x ∈ xs, P x) → result.isSome` as a whole before any `intros`.
  let env ← getEnv
  let fnHasLoop := match fnConst? with
    | some c => match env.find? c with | some (.defnInfo d) => exprHasLoopFn d.value | _ => false
    | none => false
  if !isBlind && fnHasLoop then
    if let some fnConst := fnConst? then
      let savedLoop ← saveState
      let loopSolved ← tryRestoreM false id do
        let diagRef ← match loopDiagRef? with | some r => pure r | none => IO.mkRef (none : Option LoopFailDiag)
        let ctx ← mkLoopProveCtx loopTacs false diagRef
        let g1 := (← splitAndHypsGoal g0 false 32).1
        let some g2 ← simpGoalOnly g1 ctx.dCtx (dsimpOnly := true) | setGoals rest0; return true
        let some g3 ← unfoldConstIn g2 fnConst none | return false
        let some g4 ← simpGoalOnly g3 ctx.dCtx (dsimpOnly := true) | setGoals rest0; return true
        let some g4 ← do
          let cs := (← g4.withContext do instantiateMVars (← g4.getType)).getUsedConstants
          if cs.any (fun c => c == ``Qed.qedIsMinOfKey || c == ``Qed.qedIsMaxOfKey || c == ``Qed.qedIsMinOfCmp || c == ``Qed.qedIsMaxOfCmp ||
              c == ``Qed.QedOrdArg.isMinOfFn || c == ``Qed.QedOrdArg.isMaxOfFn || c == ``Qed.QedMin2.run || c == ``Qed.QedMax2.run) then
            let (uCtx, _) ← mkCachedSimpCtx "loopUnfoldOrdPred" (ordDispatchSimpNames ++ #[``Qed.qedIsMinOfKey, ``Qed.qedIsMaxOfKey, ``Qed.qedIsMinOfCmp, ``Qed.qedIsMaxOfCmp]) { zetaDelta := false }
            simpGoalOnly g4 uCtx
          else pure (some g4)
          | setGoals rest0; return true
        if ← proveForLoopsInGoal ctx 8 g4 then setGoals rest0; return true
        -- If there are pre-loop `if`/`match` branches around the loop, split them and prove each branch.
        let splitGs ← linearSplitTarget g4
        if splitGs.length > 1 then
          let okAll ← foldlT splitGs.toArray true fun ok sg => do
            if !ok then return false
            if ← tryCloseFnOrContra sg then return true
            proveForLoopsInGoal ctx 8 sg
          if okAll then setGoals rest0; return true
        return false
      if loopSolved then return
      restoreState savedLoop
  match ← (if isBlind then pure none else shareLetResult? g0), fnConst? with
  | some (resFv, hResFv, g1), some fnConst =>
      let (resNm, hResNm) ← g1.withContext do return (← resFv.getUserName, ← hResFv.getUserName)
      let g3 := (← splitAndHypsGoal (← g1.intros).2 false 32).1
      let step1 ← match ← unfoldConstIn g3 fnConst (some hResNm) with | none => pure [] | some gU => linearSplitHyp gU hResNm (some resNm)
      let step2 ← foldlMeta step1.toArray #[] fun acc sg => return acc ++ (← unfoldAndLinearSplitFn sg fnConst (some hResNm)).toArray
      setGoals ((← finishStringGoals step2.toList) ++ rest0)
  | _, _ =>
      let some g0' ← (if isBlind then pure (some g0) else do simpGoalOnly g0 (← mkEmptyDsimpCtx) (dsimpOnly := true)) | setGoals rest0; return
      let g2 := (← splitAndHypsGoal (← g0'.intros).2 false 32).1
      match fnConst? with
      | some fnConst => setGoals ((← finishStringGoals (← unfoldAndLinearSplitFn g2 fnConst none)) ++ rest0)
      | none => setGoals (g2 :: rest0); discard <| tryTac (Qed.Lang.runPQTactic `(tactic| (try unfold $fnId:ident; try simp only [$fnId:ident]; try dsimp only at *)))
  if (← getGoals).isEmpty then return
  let (fnSimpCtx, fnSimpSP) ← mkCachedSimpCtx "fnContract" fnContractSimpNames { zetaDelta := false } #[``fnReduceStrLen]
  forEachGoal fun g => do
    if ← tryCloseFnAtom g then setGoals []; return
    runUnfoldPresent #[]
    if let g1 :: rest1 ← getGoals then
      match ← simpGoalAllHyps g1 fnSimpCtx fnSimpSP with | none => setGoals rest1 | some g2 => setGoals ((← splitAndHypsGoal g2 false 32).1 :: rest1)
    if (← getGoals).isEmpty then return
    setGoals (← finishStringGoals (← getGoals) (withLenBounds := true))
    forEachGoal (finishFnSubgoal fnSimpCtx fnSimpSP cmpErrRef?)

@[noinline] private def runProveFnLoopInvs (fnId thmId : Ident) (loopTacs : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : TacticM Unit := do
  let g0 :: _ ← getGoals | return
  let g1 := (← splitAndHypsGoal (← g0.intros).2 false 32).1
  let fnConst ← realizeGlobalConstNoOverload fnId
  let gs ← match ← unfoldConstIn g1 fnConst none with | none => pure [] | some gU => linearSplitTarget gU
  let diagRef ← IO.mkRef (none : Option LoopFailDiag)
  let ctx ← mkLoopProveCtx loopTacs true diagRef
  setGoals gs
  forEachGoal fun g => do
    if ← proveForLoopsInGoal ctx 8 g then setGoals []
    else if ← tryCloseLoopInvCheck g then setGoals []
  if !(← getGoals).isEmpty then
    if let some diag ← diagRef.get then formatLoopFailDiag fnId thmId true diag
  throwUnsolvedInvGoals thmId m!"loop `invariant` failed in `{fnId.getId}`:"
    m!"Hint: Strengthen the loop `invariant`, check initialization and each branch, or supply a `prove:` block."

@[noinline] private partial def splitFiniteEnumsAndProve (fnId : Ident) (fnSimpCtx? : Option Meta.Simp.Context) (budget : Nat) (g : MVarId) : TacticM Unit := do
  setGoals [g]; if ← tryCloseFnOrContra g then setGoals []; return
  let nextEnum? ← g.withContext <| findLCtxDecl? (includeLet := false) fun d => do
    if let some k := nullaryEnumCtorCount? (← getEnv) (← Meta.whnf d.type) then if k > 0 && k ≤ budget then return some (d.fvarId, k)
    return none
  let some (fv, k) := nextEnum? | runProveFnGoal fnId false
  let rem ← foldlT (← g.cases fv) [] fun acc sg => do
    match ← (match fnSimpCtx? with | some ctx => simpGoalAllHyps sg.mvarId ctx | none => pure (some sg.mvarId)) with
    | none => pure acc
    | some g1 => if ← tryCloseFnOrContra g1 then pure acc else do splitFiniteEnumsAndProve fnId fnSimpCtx? (budget / k) g1; return acc ++ (← getGoals)
  setGoals rem

private def exprHasQuantifier (e : Expr) : Bool :=
  (e.find? fun sub => sub.isForall || sub.isConstOf ``Exists ||
    sub.isConstOf ``Qed.qedIsMinOfKey || sub.isConstOf ``Qed.qedIsMaxOfKey ||
    sub.isConstOf ``Qed.qedIsMinOfCmp || sub.isConstOf ``Qed.qedIsMaxOfCmp ||
    sub.isConstOf ``Qed.qedIsSortedKey || sub.isConstOf ``Qed.qedIsSortedDescKey ||
    sub.isConstOf ``Qed.qedIsSortedCmp || sub.isConstOf ``Qed.qedIsSortedDescCmp ||
    sub.isConstOf ``Qed.QedOrdArg.isMinOfFn || sub.isConstOf ``Qed.QedOrdArg.isMaxOfFn ||
    sub.isConstOf ``Qed.QedOrdArg.isSortedFn || sub.isConstOf ``Qed.QedOrdArg.isSortedDescFn).isSome

@[noinline] private def runProveFnExample (fnId thmId : Ident) (isGround : Bool) : TacticM Unit := do
  let mut needGeneral := !isGround
  if let g0 :: _ ← getGoals then
    if isGround then
      if ← tryCloseGroundKernel g0 (check := true) then replaceMainGoal []; return
      -- Retry kernel reduction after unfolding `fnId`/helpers when non-kernel-reducible `String.all` is present.
      let savedFast ← saveState
      let fnConst? : Option Name ← try some <$> (realizeGlobalConstNoOverload fnId : CoreM Name) catch _ => pure none
      let gU ← deltaUnfoldLoop g0 (fun env c => isNonRecDef env c && (fnConst? == some c || qedIsHelper env c)) none 6
      let hasStrAll := (← gU.withContext do instantiateMVars (← gU.getType)).getUsedConstants.contains ``String.all
      let fastOk ← if hasStrAll then do
          let (strAllCtx, _) ← mkCachedSimpCtx "groundStrAll" #[``String.all_bool_eq, ``Qed.Lang.QedVal.val_id] { zetaDelta := false }
          match ← simpGoalOnly gU strAllCtx with
          | none => setGoals []; pure true
          | some g1 =>
              if ← closeAllGoals (tryCloseGroundKernel · (check := true)) (← splitGoalAnds g1) then setGoals []; pure true else pure false
        else pure false
      if fastOk then return
      restoreState savedFast
      needGeneral := exprHasQuantifier (← g0.withContext do instantiateMVars (← g0.getType))
    else if ← tryCloseFnAtom g0 then replaceMainGoal []; return
  if needGeneral then
    let saved ← saveState; runProveFnGoal fnId false
    if !isGround then
      if !(← getGoals).isEmpty then
        restoreState saved
        let fnSimpCtx? ← try some <$> mkDynamicSimpCtx #[← realizeGlobalConstNoOverload fnId] none (withEqns := false) catch _ => pure none
        forEachGoal (splitFiniteEnumsAndProve fnId fnSimpCtx? 256)
  throwUnsolvedInvGoals thmId m!"`example` failed for `{fnId.getId}`:"
    m!"Hint: Check the expected output in the `example`, fix `{fnId.getId}`, or supply a `prove:` / `:= by` proof."

private def extractLoopProveTacs (optArgs : Option (Array (TSyntax ``qedLoopProveArg))) : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
  match optArgs with
  | none => #[]
  | some xs => xs.filterMap fun a => match a with | `(qedLoopProveArg| ($ts:tacticSeq)) => some ts | _ => none

elab_rules : tactic
  | `(tactic| qedProveFnEnsures $fnId $thmId $[_qedLoopProve [$[$lpArgs:qedLoopProveArg],*]]?) => do
      let diagRef ← IO.mkRef (none : Option LoopFailDiag)
      let cmpErrRef ← IO.mkRef (none : Option String)
      runProveFnGoal fnId false (extractLoopProveTacs lpArgs) (some diagRef) (some cmpErrRef)
      if !(← getGoals).isEmpty then
        if let some diag ← diagRef.get then formatLoopFailDiag fnId thmId false diag
        if let some cmpMsg ← cmpErrRef.get then
          throwErrorAt thmId s!"`ensures` contract failed for `{fnId.getId}`:\n  • {cmpMsg}"
      throwUnsolvedInvGoals thmId m!"`ensures` contract failed for `{fnId.getId}`:" m!"Hint: Strengthen `requires` / `if` guards, fix the return value, or supply a `:= by` proof."
  | `(tactic| qedProveFnLoopInvs $fnId $thmId $[_qedLoopProve [$[$lpArgs:qedLoopProveArg],*]]?) =>
      runProveFnLoopInvs fnId thmId (extractLoopProveTacs lpArgs)
  | `(tactic| qedProveBlindTo $fnId $thmId $desc) => do
      runProveFnGoal fnId true
      throwUnsolvedInvGoals thmId m!"`blindTo {desc.getString}` failed in `{fnId.getId}` (output may depend on blinded field/parameter):" m!"Hint: Redact every branch that reads {desc.getString} under this guard, strengthen the `if` condition, or supply a `:= by` proof."
  | `(tactic| qedProveFnExample ground $fnId $thmId) => runProveFnExample fnId thmId true
  | `(tactic| qedProveFnExample $fnId $thmId) => runProveFnExample fnId thmId false

section FnElab
open Lean Elab Command Qed.Lang

@[noinline] private partial def collectFnContracts (guards clauses : Array Syntax) (acc : ParsedFnContracts) : CommandElabM ParsedFnContracts :=
  Qed.Lang.foldlCmd clauses acc fun acc cl => match cl.getKind with
    | ``fnRequiresClause => do
        unless guards.isEmpty do throwErrorAt cl "`requires` must appear at the top level of `fn` (combine guard conditions inside `if ...:`)"
        pure { acc with requires := acc.requires ++ (cl.getArg 1).getSepArgs }
    | ``fnEnsuresClause => pure { acc with ensures := acc.ensures.push { ref := cl, guards, preds := (cl.getArg 1).getSepArgs, tac? := parseOptTacSeq (cl.getArg 2) } }
    | ``fnBlindToClause => do pure { acc with blinds := acc.blinds.push { ref := cl, guards, targets := ← Qed.Lang.mapCmd (cl.getArg 1).getSepArgs (parseBlindTarget ·), tac? := parseOptTacSeq (cl.getArg 2) } }
    | ``fnExampleClause => do
        unless guards.isEmpty do throwErrorAt cl "`example` must appear at the top level of `fn` (use `where` on `example` for preconditions)"
        let exName : Ident := ⟨cl.getArg 1⟩
        if acc.examples.any (·.name.getId.eraseMacroScopes == exName.getId.eraseMacroScopes) then throwErrorAt exName s!"duplicate `example {exName.getId}` in `fn`"
        let params := if (cl.getArg 2).getNumArgs == 3 then ((cl.getArg 2).getArg 1).getSepArgs else #[]
        let wheres := if (cl.getArg 3).getNumArgs == 2 then ((cl.getArg 3).getArg 1).getSepArgs else #[]
        pure { acc with examples := acc.examples.push { ref := cl, name := exName, params, wheres, preds := (cl.getArg 5).getSepArgs, tac? := parseOptTacSeq (cl.getArg 6) } }
    | ``fnContractIf => collectFnContracts (guards ++ (cl.getArg 1).getSepArgs) (cl.getArg 3).getArgs acc
    | _ => throwErrorAt cl "unexpected contract clause in `fn`"

private def mkTypedBinder (id : Ident) (ty : Term) : PureQuotM (TSyntax `Lean.Parser.Term.bracketedBinder) := `(bracketedBinder| ($id:ident : $ty))
private def lowerContractProp (s : Syntax) : CommandElabM Term := liftMacroM (lowerSimpleQedExpr .propInv s (allowOptElse := true) (optElseFallback := `(True)))
private def lowerContractConj (xs : Array Syntax) : CommandElabM Term := do mkConjBody (← Qed.Lang.mapCmd xs lowerContractProp)
private def lowerTypeOnly (s : Syntax) : CommandElabM Term := liftMacroM (return (← lowerQedType s false).1)

@[noinline] private def elabContractThm (isPrivate : Bool) (thmId : Ident) (baseBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (guardPfx : String) (guards : Array Syntax) (goal : Term) (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
    (defaultTac : PureQuotM (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : CommandElabM Unit := do
  let gProps ← Qed.Lang.mapCmd guards lowerContractProp
  Qed.Lang.elabCmdWithVis isPrivate <| ← Qed.Lang.runPQ do
    let binders := baseBinders ++ (← Qed.Lang.mapIdxPQ gProps fun gp i => mkTypedBinder (mkIdent (Name.mkSimple s!"{guardPfx}{i}")) gp)
    let proofTac ← match tac? with | some ts => pure ts | none => defaultTac
    `(command| set_option linter.unusedVariables false in theorem $thmId $[$binders:bracketedBinder]* : $goal := by $proofTac)

@[noinline] def elabPureFnContracts (thmBaseId fnConstId : Ident) (paramIds : Array Ident) (paramTys : Array Term) (retTy : Term)
    (contracts : Array Syntax) (extraPreHyps : Array (Ident × Term) := #[]) (isPrivate : Bool := false)
    (hasLoopInv : Bool := false) (loopTacs : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq) := #[]) : CommandElabM Unit := do
  if contracts.isEmpty && !hasLoopInv then return
  let parsed ← collectFnContracts #[] contracts {}
  let reqProp? ← if parsed.requires.isEmpty then pure none else some <$> lowerContractConj parsed.requires
  let baseBinders ← Qed.Lang.runPQ (Qed.Lang.mapPQ (paramIds.zip paramTys ++ extraPreHyps ++ match reqProp? with | some rp => #[(mkIdent `_hReq, rp)] | none => #[]) fun (i, t) => mkTypedBinder i t)
  let rhsCall ← mkAppTerms fnConstId (paramIds.map (⟨·.raw⟩)); let paramNames := paramIds.map (·.getId.eraseMacroScopes)
  let mkSfx (ref : Syntax) (tag : String) (total idx : Nat) : Ident := mkIdentFrom ref (thmBaseId.getId.appendAfter (if total == 1 then tag else s!"{tag}_{idx + 1}"))
  let forIdx {α : Type} (xs : Array α) (f : Nat → α → CommandElabM Unit) : CommandElabM Unit := discard <| Qed.Lang.foldlCmd xs 0 fun i x => do f i x; return i + 1
  let mkLoopArgs : PureQuotM (Array (TSyntax ``qedLoopProveArg)) := Qed.Lang.mapPQ loopTacs fun ts => `(qedLoopProveArg| ($ts:tacticSeq))
  forIdx parsed.ensures fun i ens => do
    let thmId := mkSfx ens.ref "_ensures" parsed.ensures.size i; let ensProp ← lowerContractConj ens.preds
    let defTac : PureQuotM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
      if loopTacs.isEmpty then `(Lean.Parser.Tactic.tacticSeq| qedProveFnEnsures $fnConstId $thmId)
      else let lpArgs ← mkLoopArgs; `(Lean.Parser.Tactic.tacticSeq| qedProveFnEnsures $fnConstId $thmId _qedLoopProve [$[$lpArgs:qedLoopProveArg],*])
    elabContractThm isPrivate thmId baseBinders "_hIf_" ens.guards (← Qed.Lang.runPQ `(let $(mkIdent `result):ident : $retTy := $rhsCall; $ensProp)) ens.tac? defTac
  if parsed.ensures.isEmpty && hasLoopInv then
    let thmId := mkIdentFrom thmBaseId (thmBaseId.getId.appendAfter "_loop_invariants")
    let defTac : PureQuotM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
      if loopTacs.isEmpty then `(Lean.Parser.Tactic.tacticSeq| qedProveFnLoopInvs $fnConstId $thmId)
      else let lpArgs ← mkLoopArgs; `(Lean.Parser.Tactic.tacticSeq| qedProveFnLoopInvs $fnConstId $thmId _qedLoopProve [$[$lpArgs:qedLoopProveArg],*])
    elabContractThm isPrivate thmId baseBinders "_hIf_" #[] (← Qed.Lang.runPQ `(Qed.QedLoopInvCheck $rhsCall)) none defTac
  forIdx parsed.blinds fun i bl => do
    let thmId := mkSfx bl.ref "_blindTo" parsed.blinds.size i; let (freshVars, lhsArgs, _) ← buildBlindToArgs bl.targets paramNames paramIds paramTys
    let descLit := Syntax.mkStrLit (String.intercalate ", " (bl.targets.toList.map fmtBlindTarget))
    elabContractThm isPrivate thmId baseBinders "_hIf_" bl.guards (← mkBlindToEqProp freshVars (← mkAppTerms fnConstId lhsArgs) rhsCall) bl.tac? `(Lean.Parser.Tactic.tacticSeq| qedProveBlindTo $fnConstId $thmId $descLit)
  Qed.Lang.foldlCmd parsed.examples () fun _ ex => do
    let thmId := mkIdentFrom ex.name (thmBaseId.getId.appendAfter s!"_example_{ex.name.getId.eraseMacroScopes}")
    let pBinders ← Qed.Lang.mapCmd ex.params fun ep => do Qed.Lang.runPQ (mkTypedBinder ⟨ep.getArg 0⟩ (← lowerTypeOnly (ep.getArg 2)))
    let exTac := if ex.params.isEmpty && ex.wheres.isEmpty then `(Lean.Parser.Tactic.tacticSeq| qedProveFnExample ground $fnConstId $thmId) else `(Lean.Parser.Tactic.tacticSeq| qedProveFnExample $fnConstId $thmId)
    elabContractThm isPrivate thmId pBinders "_hExWhere_" ex.wheres (← lowerContractConj ex.preds) ex.tac? exTac

@[noinline, command_elab fnCmd] def elabFnCmd : CommandElab := fun stx => do
  let doc? := if (stx.getArg 0).getNumArgs == 1 then some (⟨(stx.getArg 0).getArg 0⟩ : TSyntax ``Lean.Parser.Command.docComment) else none
  let isPrivate := (stx.getArg 1).getNumArgs == 1; let fnId : Ident := ⟨stx.getArg 3⟩
  let (_, paramIds, paramTys, defBinders) ← Qed.Lang.foldlCmd (stx.getArg 5).getSepArgs (false, #[], #[], #[]) fun (seenDef, ids, tys, bs) rp => do
    let pid : Ident := ⟨rp.getArg 0⟩
    if ids.any (·.getId.eraseMacroScopes == pid.getId.eraseMacroScopes) then throwErrorAt pid s!"duplicate parameter `{pid.getId}` in `fn {fnId.getId}`"
    let pty ← lowerTypeOnly (rp.getArg 2)
    let (seen', b) ← if (rp.getArg 3).getNumArgs == 2 then
        let defT ← liftMacroM (lowerSimpleQedExpr .val ((rp.getArg 3).getArg 1))
        pure (true, ← Qed.Lang.runPQ `(bracketedBinder| ($pid:ident : $pty := $defT)))
      else do
        if seenDef then throwErrorAt pid s!"non-default parameter `{pid.getId}` cannot follow a parameter with a default value in `fn {fnId.getId}`"
        pure (false, ← Qed.Lang.runPQ (mkTypedBinder pid pty))
    return (seen', ids.push pid, tys.push pty, bs.push b)
  let retTy ← lowerTypeOnly (stx.getArg 8)
  let hasLoopInvRef ← IO.mkRef false
  let loopTacsRef ← IO.mkRef (#[] : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq))
  let bodyTerm ← lowerPureFnStmts s!"fn {fnId.getId}" (stx.getArg 11).getArgs.toList
    (onLoopInv? := some fun tac? => do hasLoopInvRef.set true; if let some ts := tac? then loopTacsRef.modify (·.push ts))
  Qed.Lang.elabCmdWithVis isPrivate (← Qed.Lang.runPQ `(command| $[$doc?:docComment]? def $fnId $[$defBinders:bracketedBinder]* : $retTy := $bodyTerm))
  elabPureFnContracts fnId fnId paramIds paramTys retTy (stx.getArg 10).getArgs #[] isPrivate (← hasLoopInvRef.get) (← loopTacsRef.get)

end FnElab
end Qed
