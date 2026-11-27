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
  requires : Array Syntax := #[]
  ensures  : Array ParsedFnEnsures := #[]
  blinds   : Array ParsedFnBlindTo := #[]
  examples : Array ParsedFnExample := #[]

syntax qedProveCase := ident,+ " => " Lean.Parser.Tactic.tacticSeq
syntax "qedDischargeInit " "[" term,* "]" term:max ident term:max : tactic
syntax "qedDischargePreserved " "[" term,* "]" term:max ident term:max (" from " term)? (" _qedProve " "[" qedProveCase,* "]")? : tactic
syntax "qedProveFnEnsures " ident ident : tactic
syntax "qedProveBlindTo " ident ident str : tactic
syntax "qedProveFnExample " ident ident : tactic

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

private def mkBoolEq (lhs rhs : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) lhs rhs
private def mkStrToList (s : Expr) : Expr := mkApp (mkConst ``String.toList) s
private def mkNot (p : Expr) : Expr := mkApp (mkConst ``Not) p
private def mkListAll (ty xs p : Expr) : Expr := mkApp3 (mkConst ``List.all [0]) ty xs p
private def closeAllGoals (f : MVarId → MetaM Bool) : List MVarId → MetaM Bool
  | [] => pure true | g :: r => do if ← f g then closeAllGoals f r else pure false
private def filterUnsolvedM (f : MVarId → MetaM Bool) : List MVarId → MetaM (List MVarId)
  | [] => pure [] | g :: r => do if ← f g then filterUnsolvedM f r else return g :: (← filterUnsolvedM f r)

private def tryCloseContradiction (g : MVarId) : MetaM Bool :=
  tryRestoreM false id (Meta.withTransparency .reducible (g.contradictionCore {}))

@[noinline] private def splitAndDsimpState (dCtx : Meta.Simp.Context) : Nat → List MVarId → MetaM (List MVarId)
  | 0, gs => pure gs | _, [] => pure []
  | fuel + 1, g :: rest => do
      match ← trySplitTarget g with
      | none => return g :: (← splitAndDsimpState dCtx fuel rest)
      | some sub => splitAndDsimpState dCtx fuel ((← sub.filterMapM (simpGoalOnly · dCtx (dsimpOnly := true))) ++ rest)

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
        let (g', seen', added) ← hyps.toList.foldlM (init := (g, seen, false)) fun (cg, sn, add) (hfv, p, q) => do
          if sn.contains q then return (cg, sn, add)
          match ← tryProvePremise cg p with
          | none => return (cg, sn, add)
          | some pfP => return ((← splitAndHypsGoal (← (← cg.assert `_qedMp q (mkApp (mkFVar hfv) pfP)).intro1P).2 true 16).1, sn.insert q, true)
        if added then rounds g' seen' n else pure g'
  rounds g0 {} 4

private def tryCloseWithImp (g : MVarId) : MetaM (Option MVarId) := do
  if ← tryCloseContradiction g then return none
  let g ← specializeImpHyps g
  if ← tryCloseContradiction g then return none
  if ← tryCloseBasic g (reducibleOnly := true) then return none
  return some g

@[noinline] private def runCloseStateGoal (extra : Array Term) : TacticM Unit := do
  let g0 :: rest ← getGoals | return
  let some g0 ← tryCloseWithImp g0 | setGoals rest; return
  setGoals (g0 :: rest)
  let cs ← collectGoalConsts g0 true
  let relNames := relevantOptResLemmas (← getEnv) cs ++ relevantBoundaryLemmas cs
  let relL? ← if extra.isEmpty then pure none else do pure (some ((← namesToSimpLemmas relNames) ++ (← termsToSimpLemmas extra)))
  let g ← match relL? with
    | none =>
        if relNames.isEmpty then pure g0
        else match ← trySimpAll g0 (← mkDynamicSimpCtx relNames) with | none => setGoals rest; return | some g' => setGoals (g' :: rest); pure g'
    | some relL =>
        if !relL.isEmpty then discard <| tryTac `(tactic| simp_all only [$[$relL],*])
        let g' :: _ ← getGoals | return
        pure g'
  let _ :: rest2 ← getGoals | return
  let some g2 ← tryCloseWithImp g | setGoals rest2; return
  setGoals (g2 :: rest2)
  let relL ← match relL? with | some l => pure l | none => do pure ((← namesToSimpLemmas relNames) ++ (← termsToSimpLemmas extra))
  evalTactic (← `(tactic| first | (qedNonlinearClose; done) | (qedAutoClose; done) | (simp_all [$[$relL],*] <;> qedAutoClose; done) | skip))

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
          let hallClosed ← if ← gHall.assumptionCore then pure true else return (← trySimpAll gHall (← mkSimpCtxWithBase)).isNone
          if !hallClosed then return false
          let gHr1 ← match ← tryApplyConst gHr `Qed.Resource.all_stripEnsured_of_imp with
            | some [gh] =>
                let (fvs, gh1) ← gh.introN 2
                match ← simpGoalOnly gh1 (← mkEmptyDsimpCtx) #[] #[fvs[1]!] (simplifyTarget := false) (dsimpOnly := true) with
                | none => setGoals []; return true | some gh2 => pure gh2
            | _ => pure gHr
          setGoals [(← splitAndHypsGoal gHr1 true 16).1]; runUnfoldPresent extraL
          if !extraSimpL.isEmpty then discard <| tryTac `(tactic| simp_all [$[$extraSimpL],*])
          else setGoals <| ← (← getGoals).filterMapM (trySimpAll · (← mkSimpCtxWithBase))
          closeAllGoals (tryCloseBasic ·) (← getGoals)
      then progRef.set true; setGoals []

@[noinline] private def runCloseCachedPut (extraL : Array Term) : TacticM Unit := do
  unless (← getEnv).contains `Qed.Cached.all_put do return
  unless ← (← getGoals).anyM fun g => return (← g.withContext (instantiateMVars (← g.getType))).getUsedConstants.contains `Qed.Cached.all do return
  let extraSimpL ← termsToSimpLemmas extraL
  let rec go : Nat → TacticM Unit
    | 0 => pure ()
    | n + 1 => do if !(← getGoals).isEmpty then let p ← IO.mkRef false; forEachGoal (closeCachedPutGoal extraL extraSimpL p); if ← p.get then go n
  go 8

private def simpIdentAtAll (t : Term) : TacticM Unit := do
  let t := match t with | `(($p)) => p | p => p
  if t.raw.isIdent then if let some nm ← try some <$> realizeGlobalConstNoOverload t.raw catch _ => pure none then
    setGoals <| ← (← getGoals).filterMapM (simpGoalAllHyps · (← mkDynamicSimpCtx #[nm] none (withEqns := false)))

@[noinline] private def runInitPass (usingL : Array Term) (pred initT : Term) : TacticM Unit := do
  simpIdentAtAll pred; let dCtx ← mkEmptyDsimpCtx
  setGoals <| ← (← getGoals).filterMapM (simpGoalAllHyps · dCtx (dsimpOnly := true))
  simpIdentAtAll initT; runUnfoldPresent usingL
  setGoals (← splitAndDsimpState dCtx 32 (← getGoals))
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
  if ← tryCloseTrivial g (reducibleOnly := reducibleOnly) then setGoals []; return
  if ← tryDirectOmega g then setGoals []; return
  let dCtx ← mkEmptyDsimpCtx
  setGoals <| ← (← splitAndDsimpState dCtx 16 [(← g.intros).2]).filterMapM (simpGoalAllHyps · dCtx (dsimpOnly := true))
  forEachGoal fun gSub => do
    if ← tryCloseContradiction gSub then setGoals []; return
    runAddFieldFacts
    if let g1 :: r1 ← getGoals then setGoals ((← splitAndHypsGoal g1 true 16).1 :: r1)
    runUnfoldPresent usingL skipUnfold
    if let some (eCtx, eSP) := extraCtx? then
      setGoals <| ← ((← getGoals).filterMapM (trySimpAll · eCtx eSP) : MetaM _)
      if (← getGoals).isEmpty then return
    runCloseStateGoal usingL
    if hypSplitFuel > 0 then
      if let gRem :: _ ← getGoals then
        let splitFVar? ← gRem.withContext <| findLCtxDecl? (includeLet := false) fun d => do
          if ← isPropSafe (← instantiateMVars d.type) then if (← trySplitLocalDecl gRem d.fvarId).isSome then return some d.fvarId
          return none
        if let some fv := splitFVar? then
          if let some subgoals ← trySplitLocalDecl gRem fv then
            setGoals subgoals; forEachGoal (closeSplitBranch usingL reducibleOnly extraCtx? (hypSplitFuel - 1) skipUnfold)
termination_by hypSplitFuel

@[noinline] private def runDischargeInit (usingL : Array Term) (initT : Term) (nm : Ident) (pred : Term) : TacticM Unit :=
  withFreshHeartbeatsT do
    (← getMainGoal).setTag `init; runInitPass usingL pred initT
    throwUnsolvedInvGoals nm m!"Invariant `{nm.getId}` failed on initial state `{formatTargetName initT}`:"
      m!"Hint: Update the initial `state` values so `{nm.getId}` holds, add `using [lemma]`, or supply a `:= by` proof."

@[noinline] private def runPreservedBranchCore (usingL : Array Term) (updNames : Array Name) (ctx dCtx : Meta.Simp.Context) (isFastRecon : Bool) (g : MVarId) : TacticM Unit := do
  match ← trySimpAll g ctx with
  | none => setGoals []; return
  | some g1 =>
      setGoals [g1]
      if ← tryCloseBasic g1 (reducibleOnly := true) then setGoals []; return
      if isFastRecon then
        if ← tryRestoreM false id (do
          if ← closeAllGoals (tryCloseBasic · (reducibleOnly := true)) (← splitAndDsimpState dCtx 16 [g1]) then setGoals []; return true else return false)
        then return
  runUnfoldPresent usingL updNames; try runCloseCachedPut usingL catch _ => pure ()
  setGoals (← splitAndDsimpState dCtx 16 (← getGoals))
  forEachGoal (closeSplitBranch usingL true none 3 updNames)

@[noinline] private def runPreservedBranch (usingL : Array Term) (updNames : Array Name) (updCtx dCtx : Meta.Simp.Context)
    (fastUpdCtx? : Option Meta.Simp.Context) (caseMap : Std.HashMap Name (Ident × TSyntax ``Lean.Parser.Tactic.tacticSeq))
    (seenCasesRef : IO.Ref (Std.HashSet Name)) (allCtorsRef : IO.Ref (Array Name)) (g : MVarId) : TacticM Unit := withFreshHeartbeatsT do
  let ctorTag := stripStepPrefix (← g.getTag)
  allCtorsRef.modify (Qed.Lang.pushUnique · ctorTag)
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

@[noinline] private def buildFastReconCtx? (updNames reconNames : Array Name) : TacticM (Option Meta.Simp.Context) := do
  if reconNames.isEmpty then return none
  let g0 :: _ ← getGoals | return none
  let goalConsts ← collectGoalConsts g0 true
  let projSt? ← reconNames.toList.foldlM (init := some ({} : Meta.SimpTheorems)) fun acc? rn =>
    match acc? with | none => pure none | some st => addReconcileProjLemmas st rn goalConsts
  let some projSt := projSt? | return none
  let baseCtx ← mkDynamicSimpCtx (updNames.filter (·.getString! != "_reconcileHoisted")) none (withEqns := false)
  some <$> Meta.Simp.mkContext baseCtx.config (baseCtx.simpTheorems.push projSt) baseCtx.congrTheorems

@[noinline] private def runPreservedStep (usingL : Array Term) (pred : Term) (updUnfolds updNames : Array Name)
    (updCtx dCtx : Meta.Simp.Context) (caseMap : Std.HashMap Name (Ident × TSyntax ``Lean.Parser.Tactic.tacticSeq))
    (seenCasesRef : IO.Ref (Std.HashSet Name)) (allCtorsRef : IO.Ref (Array Name)) : TacticM Unit := do
  let (_, g1) ← (← getMainGoal).introN 3 [`m, `msg, `h]
  setGoals [g1]; simpIdentAtAll pred
  setGoals <| ← (← getGoals).filterMapM (simpGoalAllHyps · dCtx (dsimpOnly := true))
  if (← getGoals).isEmpty then return
  let fastUpdCtx? ← buildFastReconCtx? updNames (updUnfolds.filter (·.getString! == "_reconcileHoisted"))
  evalTactic (← `(tactic| cases $(mkIdent `msg):ident))
  forEachGoal (runPreservedBranch usingL updNames updCtx dCtx fastUpdCtx? caseMap seenCasesRef allCtorsRef)

@[noinline] private def parseProveCases (nm : Ident) (proveCases : Option (Array (TSyntax ``qedProveCase))) :
    TacticM (Std.HashMap Name (Ident × TSyntax ``Lean.Parser.Tactic.tacticSeq) × Array Ident) := do
  let some pcs := proveCases | return ({}, #[])
  pcs.toList.foldlM (init := ({}, #[])) fun (m, ids) (pc : TSyntax ``qedProveCase) => match pc with
    | `(qedProveCase| $[$cIds:ident],* => $tacSeq) =>
        cIds.toList.foldlM (init := (m, ids)) fun (acc, os) (cid : Ident) => do
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
  let step := runPreservedStep usingL pred updUnfolds updNames updCtx dCtx caseMap seenCasesRef allCtorsRef
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
  | `(tactic| qedDischargeInit [$[$usingL],*] $initT $nm $pred) => runDischargeInit usingL initT nm pred
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
private def fnContractSimpNames : Array Name :=
  strGuardNormNames ++ #[``Array.size_push, ``Array.size_set, ``Array.size_map, ``Array.size_append,
    ``Array.size_reverse, ``List.length_cons, ``List.length_append, ``List.length_map, ``String.length_append,
    ``Option.isSome_none, ``Option.isSome_some, ``Option.isNone_none, ``Option.isNone_some, ``Qed.qedCoalesce_option,
    ``Qed.qedIterable_toList_list, ``Qed.qedIterable_toList_array, ``Qed.qedIterable_toList_range,
    ``true_and, ``and_true, ``false_or, ``or_false, ``true_or, ``or_true, ``id_eq, ``ne_eq]
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

private def stripValWrapAux (e : Expr) : Nat → Expr
  | 0 => e.consumeMData
  | fuel + 1 =>
      let e := e.consumeMData
      if e.isAppOfArity ``Qed.Lang.QedVal.val 4 then stripValWrapAux e.getAppArgs[3]! fuel
      else if e.isAppOfArity ``toString 3 && e.getAppArgs[0]!.isConstOf ``String then stripValWrapAux e.getAppArgs[2]! fuel
      else e
private def stripValWrap (e : Expr) : Expr := stripValWrapAux e 32

private def matchIteSide? (e : Expr) : Option (Bool × Expr) :=
  if e.isAppOfArity ``dite 5 then some (true, e) else if e.isAppOfArity ``ite 5 then some (false, e) else none

private def isOuterIteEq (ty : Expr) : Bool :=
  match ty.consumeMData.eq? with
  | some (_, l, r) => (matchIteSide? (stripValWrap l)).isSome || (matchIteSide? (stripValWrap r)).isSome
  | none => false

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
        let bTy ← Meta.withLocalDeclD `_qedCond (if isPos then c else mkApp (mkConst ``Not) c) fun hc => do
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
            if isOuterIteEq (← g0.withContext do instantiateMVars (← fv.getType)) then pure (g0, some fv)
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
            match ← splitOne g with | none => go rest (g :: done) fuel | some kids => go ((← kids.filterMapM (tryPruneBranch · pruneName?)) ++ rest) done fuel
  go [g0] [] 32

@[noinline] private def linearSplitHyp (g0 : MVarId) (fvName : Name) (substTargetName? : Option Name := none) : MetaM (List MVarId) := do
  let survived ← linearSplit g0 (fun g => do
    let some fv ← findFVarByName? g fvName | return none
    match ← tryFastSplitIteEqHyp g fv fvName with | some kids => pure (some kids) | none => trySplitLocalDecl g fv) (some fvName)
  let some targetNm := substTargetName? | return survived
  survived.filterMapM fun g => do
    let some fv ← findFVarByName? g fvName | return some g
    let some targetFv ← findFVarByName? g targetNm | return some g
    let shouldSubst := (← g.withContext do instantiateMVars (← fv.getType)).consumeMData.eq?.any fun (_, l, r) =>
      (l.consumeMData == mkFVar targetFv && !r.containsFVar targetFv) || (r.consumeMData == mkFVar targetFv && !l.containsFVar targetFv)
    if shouldSubst then match ← trySubstFVar g fv with | some gSub => tryPruneBranch gSub none | none => pure (some g) else pure (some g)

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
private def extractToStringOf? (tyNm reprNm : Name) (e : Expr) : Option Expr :=
  let e := (stripValWrap e).consumeMData
  if e.isAppOfArity ``toString 3 && e.getAppArgs[0]!.isConstOf tyNm then some (stripValWrap e.getAppArgs[2]!)
  else if e.isAppOfArity reprNm 1 then some (stripValWrap e.getAppArgs[0]!) else none
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
  let some hall ← tryMkDecideProof (mkBoolEq (mkListAll (mkConst ``String) listExpr checkFn) (mkConst ``Bool.true)) | return none
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
  if depth > 0 then
    if let some (_, lhs, rhs) := ty.eq? then
      if rhs.consumeMData.isConstOf ``Bool.true then
        if let .const fnNm _ := lhs.getAppFn then
          if qedIsHelper env fnNm && lhs.getAppArgs.any (stripValWrap · == a) then
            return ← tryRestoreM none Option.isSome do
              let m ← Meta.mkFreshExprSyntheticOpaqueMVar goalTy
              let ctx ← mkDynamicSimpCtx (strGuardNormNames.push fnNm) none { zetaDelta := true }
              match ← simpGoalOnly m.mvarId! ctx #[] #[decl.fvarId] (simplifyTarget := false) with
              | none => some <$> instantiateMVars m
              | some m1 =>
                  let m2 := (← splitAndHypsGoal m1 false 16).1
                  match ← m2.withContext (proveCharNotMem? d a (depth - 1)) with
                  | some pf => m2.assign pf; some <$> instantiateMVars m | none => return none
  return none

@[noinline] private partial def proveCharNotMem? (d : Char) (a0 : Expr) (depth : Nat := 2) : MetaM (Option Expr) := do
  let a := stripValWrap a0; let dExpr := toExpr d
  let goalTy := mkNot (← Meta.mkAppM ``Membership.mem #[mkStrToList a, dExpr])
  if d < '0' || '9' < d then
    let digitOut := do return mkApp2 (mkConst ``Or) (← Meta.mkAppM ``LT.lt #[dExpr, toExpr '0']) (← Meta.mkAppM ``LT.lt #[toExpr '9', dExpr])
    if let some n := extractToStringOf? ``Nat ``Nat.repr a then
      if let some hd ← tryMkDecideProof (← digitOut) then return some (← Meta.mkAppM ``Qed.Str.nat_toString_not_mem #[hd, n])
    if d != '-' then if let some i := extractToStringOf? ``Int ``Int.repr a then
      if let some hd ← tryMkDecideProof (mkApp2 (mkConst ``And) (mkApp3 (mkConst ``Ne [1]) (mkConst ``Char) dExpr (toExpr '-')) (← digitOut)) then
        return some (← Meta.mkAppM ``Qed.Str.int_toString_not_mem #[hd, i])
  if let some s := extractStrLit? a then
    if !s.contains d then if let some pf ← tryMkDecideProof goalTy then return some pf
  if let some (x, y) := extractStrAppend? a then
    if let some hx ← proveCharNotMem? d x depth then if let some hy ← proveCharNotMem? d y depth then
      return some (← Meta.mkAppM ``Qed.Str.str_not_mem_append #[hx, hy])
  findLCtxDecl? (includeLet := false) (proveCharNotMemFromDecl? (← getEnv) d dExpr a goalTy depth)
end

@[noinline] private partial def normStrLeaf (e0 : Expr) : MetaM (Expr × Expr) := do
  let e := e0.consumeMData
  if e.isAppOfArity ``Qed.Lang.QedVal.val 4 then
    let inner := e.getAppArgs[3]!; let (e', h2) ← normStrLeaf inner
    return (e', ← Meta.mkEqTrans (← Meta.mkAppM ``Qed.Lang.QedVal.val_id #[inner]) h2)
  if e.isAppOfArity ``toString 3 && e.getAppArgs[0]!.isConstOf ``String then
    let inner := e.getAppArgs[2]!; let (e', h2) ← normStrLeaf inner
    return (e', ← Meta.mkEqTrans (mkApp (mkConst ``Qed.Str.str_toString) inner) h2)
  if e.isAppOfArity ``toString 3 && e.getAppArgs[2]!.consumeMData.isAppOfArity ``Qed.Lang.QedVal.val 4 then
    let a := e.getAppArgs; let inner := a[2]!.consumeMData.getAppArgs[3]!
    return (mkApp3 e.getAppFn a[0]! a[1]! inner, ← Meta.mkAppM ``toString_qedVal_eq #[inner])
  return (e, ← Meta.mkEqRefl e)

private def mkStrAppendExpr (x y : Expr) : MetaM Expr := Meta.mkAppM ``HAppend.hAppend #[x, y]

@[noinline] private partial def reassocStrAcc (t acc : Expr) : MetaM (Expr × Expr) := do
  let (t0, hLeaf) ← normStrLeaf t; let hLift ← Meta.mkAppM ``str_append_congr_right #[acc, hLeaf]
  match extractStrAppend? t0 with
  | none =>
      if extractStrLit? t0 == some "" then return (acc, ← Meta.mkEqTrans hLift (mkApp (mkConst ``String.empty_append) acc))
      return (← mkStrAppendExpr t0 acc, hLift)
  | some (a, b) =>
      let (r1, h1) ← reassocStrAcc b acc; let (r2, h2) ← reassocStrAcc a r1
      return (r2, ← mkEqTransChain [hLift, mkApp3 (mkConst ``String.append_assoc) a b acc, ← Meta.mkAppM ``str_append_congr_left #[a, h1], h2])

@[noinline] private partial def reassocStr (t : Expr) : MetaM (Expr × Expr) := do
  let (t0, hLeaf) ← normStrLeaf t
  match extractStrAppend? t0 with
  | none => return (t0, hLeaf)
  | some (a, b) =>
      let (rb, hb) ← reassocStr b; let h1 ← Meta.mkAppM ``str_append_congr_left #[a, hb]
      if extractStrLit? rb == some "" then
        let (ra, ha) ← reassocStr a
        return (ra, ← mkEqTransChain [hLeaf, h1, mkApp (mkConst ``String.append_empty) a, ha])
      let (res, hAcc) ← reassocStrAcc a rb; return (res, ← mkEqTransChain [hLeaf, h1, hAcc])

private def mkStrPrefixSplitPf (lit head tail rest : Expr) : MetaM (Option (Expr × Expr)) := do
  let some hSplit ← tryMkDecideProof (mkApp3 (mkConst ``Eq [1]) (mkConst ``String) lit (← mkStrAppendExpr head tail)) | return none
  let h1 ← Meta.mkAppM ``str_append_congr_right #[rest, hSplit]
  return some (← mkStrAppendExpr tail rest, ← Meta.mkEqTrans h1 (mkApp3 (mkConst ``String.append_assoc) head tail rest))

@[noinline] private def tryStrSepSplit? (p₁ p₂ x y eqPf' : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let (some (sep₁, r₁), some (sep₂, r₂)) := (extractStrAppend? x, extractStrAppend? y) | return none
  let (some s₁, some s₂) := (extractStrLit? sep₁, extractStrLit? sep₂) | return none
  let (d₁ :: _, d₂ :: _) := (s₁.toList, s₂.toList) | return none
  if d₁ != d₂ then return none
  let some h₁ ← proveCharNotMem? d₁ p₁ | return none
  let some h₂ ← proveCharNotMem? d₁ p₂ | return none
  let runSep (sepExpr rhs₁ rhs₂ eqTerm : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
    let optChar := mkApp (mkConst ``Option [0]) (mkConst ``Char)
    let headEqTy := mkApp3 (mkConst ``Eq [1]) optChar (mkApp2 (mkConst ``List.head? [0]) (mkConst ``Char) (mkStrToList sepExpr)) (mkApp2 (mkConst ``Option.some [0]) (mkConst ``Char) (toExpr d₁))
    let some hsep ← tryMkDecideProof headEqTy | return none
    let pairPf := mkAppN (mkConst ``Qed.Str.str_split_sep_inj) #[sepExpr, p₁, p₂, rhs₁, rhs₂, toExpr d₁, hsep, h₁, h₂, eqTerm]
    return some (rhs₁, rhs₂, ← Meta.mkAppM ``And.left #[pairPf], ← Meta.mkAppM ``And.right #[pairPf])
  if s₁ == s₂ then runSep sep₁ r₁ r₂ eqPf'
  else
    let dStr := Expr.lit (.strVal (String.singleton d₁))
    let some (nr₁, hL) ← mkStrPrefixSplitPf sep₁ dStr (Expr.lit (.strVal (String.ofList (s₁.toList.drop 1)))) r₁ | return none
    let some (nr₂, hR) ← mkStrPrefixSplitPf sep₂ dStr (Expr.lit (.strVal (String.ofList (s₂.toList.drop 1)))) r₂ | return none
    let pL ← Meta.mkAppM ``str_append_congr_left #[p₁, hL]; let pR ← Meta.mkAppM ``str_append_congr_left #[p₂, hR]
    runSep dStr nr₁ nr₂ (← mkEqTransChain [← Meta.mkEqSymm pL, eqPf', pR])

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
            if let some hdiff ← tryMkDecideProof (mkBoolEq (mkApp2 (mkConst ``strDiffPrefix) p₁ p₂) (mkConst ``Bool.true)) then
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
      if (extractToStringOf? ``Nat ``Nat.repr l).isSome && (extractToStringOf? ``Nat ``Nat.repr r).isSome then
        return .inr #[← Meta.mkAppM ``Qed.Str.nat_toString_injective #[eqPf']]
      if (extractToStringOf? ``Int ``Int.repr l).isSome && (extractToStringOf? ``Int ``Int.repr r).isSome then
        return .inr #[← Meta.mkAppM ``Qed.Str.int_toString_injective #[eqPf']]
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
  let rec go (acc : Array Expr) : List (Expr × Expr × Expr) → MetaM (Option (Array Expr))
    | [] => pure (some acc)
    | (lhs, rhs, pf) :: rest => do
        match ← g1.withContext (collectStringEqFacts lhs rhs pf) with
        | .inl falsePf => g1.assign (mkApp2 (mkConst ``False.elim [0]) (← g1.withContext (instantiateMVars (← g1.getType))) falsePf); return none
        | .inr facts => go (acc ++ facts) rest
  let some newFacts ← go #[] strEqs.toList | return none
  if newFacts.isEmpty then return some g1
  return some (← assertFacts g1 "_qedStr" newFacts).1

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
  return #[``ToString.toString, ``Nat.repr, ``Int.repr, ``Nat.toDigits].any cs.contains

@[noinline] private def tryProveCharImp (impTy : Expr) : MetaM (Option Expr) := tryRestoreM none Option.isSome do
  let mImp ← if impTy.hasFVar then Meta.mkFreshExprSyntheticOpaqueMVar impTy else Meta.withLCtx {} {} (Meta.mkFreshExprSyntheticOpaqueMVar impTy)
  let done := some <$> instantiateMVars mImp
  let some g2 ← simpGoalAllHyps (← mImp.mvarId!.introN 2).2 (← mkEmptyDsimpCtx) (dsimpOnly := true) | done
  let some g3 ← simpGoalAllHyps g2 (← mkCachedSimpCtx "charImp" charImpSimpNames).1 | done
  if ← g3.assumptionCore then return ← done
  let charNatSt ← (← getCachedSimpThms "charNat" charNatSimpNames).addConst ``UInt32.toNat_inj (inv := true)
  match ← simpGoalAllHyps g3 (← Meta.Simp.mkContext { failIfUnchanged := false } #[charNatSt] (← Meta.getSimpCongrTheorems)) with
  | none => done | some g4 => if ← tryDirectOmega g4 then done else return none

@[noinline] private def tryCloseOneStringAllSubgoal (sg : MVarId) : MetaM Bool := do
  if ← tryCloseBasic sg (reducibleOnly := true) then return true
  let some (seg, p, true) := extractStrAll? (← sg.withContext (instantiateMVars (← sg.getType))) | return false
  sg.withContext do
    let closeAlpha (chars : String) (lem : Name) (arg : Expr) : MetaM Bool := do
      let some hp ← tryMkDecideProof (mkBoolEq (mkListAll (mkConst ``Char) (mkStrToList (Expr.lit (.strVal chars))) p) (mkConst ``Bool.true)) | return false
      sg.assign (← Meta.mkAppM lem #[hp, arg]); return true
    if let some n := extractToStringOf? ``Nat ``Nat.repr seg then if ← closeAlpha "0123456789" ``Qed.Str.nat_toString_all n then return true
    if let some i := extractToStringOf? ``Int ``Int.repr seg then if ← closeAlpha "-0123456789" ``Qed.Str.int_toString_all i then return true
    (← collectLCtxDecls (includeLet := false) fun d => return some (d.toExpr, (← instantiateMVars d.type).consumeMData)).toList.anyM fun (de, dty) => do
      if let some (elem, coll, isArr) := extractStrMemColl? dty then if ← isDefEqFast elem seg then
        let checkFn := Expr.lam `x (mkConst ``String) (mkListAll (mkConst ``Char) (mkStrToList (.bvar 0)) (p.liftLooseBVars 0 1)) .default
        if let some pf ← tryProveFromStrMemColl de coll checkFn isArr ``Qed.Str.str_all_of_mem_array ``Qed.Str.str_all_of_mem_list then sg.assign pf; return true
      if let some (s', p', isToList) := extractStrAll? dty then if ← isDefEqFast s' seg then
        let hList := if isToList then de else mkApp3 (mkConst ``str_all_toList_of_all) s' p' de
        if ← isDefEqFast p' p then sg.assign hList; return true
        let impTy ← Meta.withLocalDeclD `c (mkConst ``Char) fun c =>
          Meta.mkForallFVars #[c] (Expr.forallE `_h (mkBoolEq (p'.beta #[c]) (mkConst ``Bool.true)) (mkBoolEq (p.beta #[c]) (mkConst ``Bool.true)) .default)
        if let some pfImp ← tryProveCharImp impTy then sg.assign (← Meta.mkAppM ``Qed.Str.list_all_mono #[hList, pfImp]); return true
      return false

@[noinline] private def tryCloseStringAllGoal (g0 : MVarId) : MetaM Bool := do
  if (extractStrAll? (← g0.withContext (instantiateMVars (← g0.getType)))).isNone then return false
  tryRestoreM false id do
    let some g1 ← simpGoalOnly g0 (← mkCachedSimpCtx "strAllNorm" strAllNormNames { zetaDelta := false }).1 | return true
    closeAllGoals tryCloseOneStringAllSubgoal (← splitGoalAnds g1)

@[noinline] private def finishStringGoals (gs : List MVarId) (withLenBounds : Bool := false) : MetaM (List MVarId) := do
  let closeSub (sg : MVarId) : MetaM Bool := do if ← tryCloseBasic sg (reducibleOnly := true) then pure true else tryCloseStringAllGoal sg
  let rec go (acc : List MVarId) : List MVarId → MetaM (List MVarId)
    | [] => pure acc.reverse
    | g :: rest => do
        match ← decomposeStringEqs g with
        | none => go acc rest
        | some g1 =>
            let g2 ← if withLenBounds then assertStrMemLenBounds g1 else pure g1
            go ((← filterUnsolvedM closeSub (← splitGoalAnds g2)).reverse ++ acc) rest
  go [] gs

private def preSplitOuterMatch (g0 : MVarId) : MetaM (List MVarId) := do
  let tgt := (← g0.withContext (instantiateMVars (← g0.getType))).consumeMData
  unless match tgt.getAppFn with | .const c _ => c.toString.contains ".match_" | _ => false do return [g0]
  match ← trySplitTarget g0 with | none => return [g0] | some kids => kids.filterMapM (tryPruneBranch · none)

@[noinline] private def unfoldAndLinearSplitFn (g0 : MVarId) (fnConst : Name) (skipName? : Option Name := none) : MetaM (List MVarId) := do
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
  (← (← splitHyps (← preSplitOuterMatch g0) [] 8).mapM fun g => do
    if (← g.withContext (instantiateMVars (← g.getType))).getUsedConstants.contains fnConst then
      match ← unfoldConstIn g fnConst none with | none => pure [] | some gU => linearSplitTarget gU
    else pure [g]).flatten |> pure

private def tryCloseFnAtom (g : MVarId) : MetaM Bool := do
  if ← tryCloseGroundKernel g (check := true) then return true
  tryCloseBasic g (reducibleOnly := true)

@[noinline] private def finishFnSubgoal (fnSimpCtx : Meta.Simp.Context) (fnSimpSP : Meta.Simp.SimprocsArray) (sg : MVarId) : TacticM (List MVarId) := do
  if ← goalHasStrRepr sg then
    let rec goBranches (acc : List MVarId) : List MVarId → MetaM (List MVarId)
      | [] => pure acc.reverse
      | bg :: r => do
          if ← tryCloseContradiction bg then return ← goBranches acc r
          match ← simpGoalAllHyps bg fnSimpCtx fnSimpSP with
          | none => goBranches acc r
          | some bg1 => goBranches ((← filterUnsolvedM tryCloseFnAtom (← finishStringGoals [(← splitAndHypsGoal bg1 false 32).1] true)).reverse ++ acc) r
    return ← goBranches [] (← linearSplitTarget sg)
  let some sg1 ← trySimpAll sg fnSimpCtx fnSimpSP | return []
  setGoals (← linearSplitTarget sg1)
  forEachGoal (closeSplitBranch #[] false (some (fnSimpCtx, fnSimpSP)) 3)
  if !(← getGoals).isEmpty then
    setGoals (← filterUnsolvedM (fun s => do if ← tryCloseStringAllGoal s then pure true else tryCloseFnAtom s) (← getGoals))
  getGoals

@[noinline] private def runProveFnGoal (fnId : Ident) (isBlind : Bool) : TacticM Unit := do
  let fnConst? : Option Name ← try some <$> (realizeGlobalConstNoOverload fnId : CoreM Name) catch _ => pure none
  let g0 :: rest0 ← getGoals | return
  let shared? ← if isBlind then pure none else shareLetResult? g0
  match shared?, fnConst? with
  | some (resFv, hResFv, g1), some fnConst =>
      let (resNm, hResNm) ← g1.withContext do return (← resFv.getUserName, ← hResFv.getUserName)
      let g3 := (← splitAndHypsGoal (← g1.intros).2 false 32).1
      let step1 ← match ← unfoldConstIn g3 fnConst (some hResNm) with | none => pure [] | some gU => linearSplitHyp gU hResNm (some resNm)
      setGoals ((← finishStringGoals (← (step1.mapM (unfoldAndLinearSplitFn · fnConst (some hResNm)) : MetaM _)).flatten) ++ rest0)
  | _, _ =>
      let some g0' ← (if isBlind then pure (some g0) else do simpGoalOnly g0 (← mkEmptyDsimpCtx) (dsimpOnly := true)) | setGoals rest0; return
      let g2 := (← splitAndHypsGoal (← g0'.intros).2 false 32).1
      match fnConst? with
      | some fnConst => setGoals ((← finishStringGoals (← unfoldAndLinearSplitFn g2 fnConst none)) ++ rest0)
      | none => setGoals (g2 :: rest0); discard <| tryTac `(tactic| (try unfold $fnId:ident; try simp only [$fnId:ident]; try dsimp only at *))
  if (← getGoals).isEmpty then return
  let (fnSimpCtx, fnSimpSP) ← mkCachedSimpCtx "fnContract" fnContractSimpNames { zetaDelta := false } #[``fnReduceStrLen]
  forEachGoal fun g => do
    if ← tryCloseBasic g (reducibleOnly := true) then setGoals []; return
    setGoals [g]; runUnfoldPresent #[]
    if let g1 :: rest1 ← getGoals then
      match ← simpGoalAllHyps g1 fnSimpCtx fnSimpSP with | none => setGoals rest1 | some g2 => setGoals ((← splitAndHypsGoal g2 false 32).1 :: rest1)
    if (← getGoals).isEmpty then return
    setGoals (← finishStringGoals (← getGoals) (withLenBounds := true))
    if !(← getGoals).isEmpty then setGoals (← (← getGoals).mapM (finishFnSubgoal fnSimpCtx fnSimpSP)).flatten

@[noinline] private partial def splitFiniteEnumsAndProve (fnId : Ident) (fnSimpCtx? : Option Meta.Simp.Context) (budget : Nat) (g : MVarId) : TacticM Unit := do
  setGoals [g]
  if ← tryCloseContradiction g then setGoals []; return
  if ← tryCloseFnAtom g then setGoals []; return
  let nextEnum? ← g.withContext <| findLCtxDecl? (includeLet := false) fun d => do
    if let some k := nullaryEnumCtorCount? (← getEnv) (← Meta.whnf d.type) then if k > 0 && k ≤ budget then return some (d.fvarId, k)
    return none
  let some (fv, k) := nextEnum? | runProveFnGoal fnId false
  let rem ← (← g.cases fv).toList.foldlM (init := []) fun acc sg => do
    match ← (match fnSimpCtx? with | some ctx => simpGoalAllHyps sg.mvarId ctx | none => pure (some sg.mvarId)) with
    | none => pure acc
    | some g1 =>
        if ← tryCloseContradiction g1 then pure acc
        else if ← tryCloseFnAtom g1 then pure acc
        else do splitFiniteEnumsAndProve fnId fnSimpCtx? (budget / k) g1; return acc ++ (← getGoals)
  setGoals rem

@[noinline] private def runProveFnExample (fnId thmId : Ident) : TacticM Unit := do
  if let g0 :: _ ← getGoals then if ← tryCloseFnAtom g0 then replaceMainGoal []; return
  let saved ← saveState; runProveFnGoal fnId false
  if !(← getGoals).isEmpty then
    restoreState saved
    let fnSimpCtx? ← try some <$> mkDynamicSimpCtx #[← realizeGlobalConstNoOverload fnId] none (withEqns := false) catch _ => pure none
    forEachGoal (splitFiniteEnumsAndProve fnId fnSimpCtx? 256)
  throwUnsolvedInvGoals thmId m!"`example` failed for `{fnId.getId}`:"
    m!"Hint: Check the expected output in the `example`, fix `{fnId.getId}`, or supply a `prove:` / `:= by` proof."

@[noinline] private def runProveFnContract (fnId thmId : Ident) (blindDesc? : Option String) : TacticM Unit := do
  runProveFnGoal fnId blindDesc?.isSome
  match blindDesc? with
  | none => throwUnsolvedInvGoals thmId m!"`ensures` contract failed for `{fnId.getId}`:" m!"Hint: Strengthen `requires` / `if` guards, fix the return value, or supply a `:= by` proof."
  | some desc => throwUnsolvedInvGoals thmId m!"`blindTo {desc}` failed in `{fnId.getId}` (output may depend on blinded field/parameter):" m!"Hint: Redact every branch that reads {desc} under this guard, strengthen the `if` condition, or supply a `:= by` proof."

elab_rules : tactic
  | `(tactic| qedProveFnEnsures $fnId $thmId) => runProveFnContract fnId thmId none
  | `(tactic| qedProveBlindTo $fnId $thmId $desc) => runProveFnContract fnId thmId (some desc.getString)
  | `(tactic| qedProveFnExample $fnId $thmId) => runProveFnExample fnId thmId

section FnElab
open Lean Elab Command Qed.Lang

def parseOptTacSeq (optNode : Syntax) : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
  if optNode.getNumArgs == 1 then
    let i := optNode.getArg 0; if i.getKind == `Qed.fnProofBy || i.getKind == `Qed.fnProofProve then some ⟨i.getArg 2⟩ else none
  else none

@[noinline] private partial def collectFnContracts (guards : Array Syntax) (clauses : List Syntax) (acc : ParsedFnContracts) : CommandElabM ParsedFnContracts :=
  match clauses with
  | [] => pure acc
  | cl :: rest => do
      let acc' ← match cl.getKind with
        | ``fnRequiresClause =>
            unless guards.isEmpty do throwErrorAt cl "`requires` must appear at the top level of `fn` (combine guard conditions inside `if ...:`)"
            pure { acc with requires := acc.requires ++ (cl.getArg 1).getSepArgs }
        | ``fnEnsuresClause => pure { acc with ensures := acc.ensures.push { ref := cl, guards, preds := (cl.getArg 1).getSepArgs, tac? := parseOptTacSeq (cl.getArg 2) } }
        | ``fnBlindToClause => pure { acc with blinds := acc.blinds.push { ref := cl, guards, targets := ← (cl.getArg 1).getSepArgs.mapM (parseBlindTarget ·), tac? := parseOptTacSeq (cl.getArg 2) } }
        | ``fnExampleClause =>
            unless guards.isEmpty do throwErrorAt cl "`example` must appear at the top level of `fn` (use `where` on `example` for preconditions)"
            let exName : Ident := ⟨cl.getArg 1⟩
            if acc.examples.any (·.name.getId.eraseMacroScopes == exName.getId.eraseMacroScopes) then throwErrorAt exName s!"duplicate `example {exName.getId}` in `fn`"
            let params := if (cl.getArg 2).getNumArgs == 3 then ((cl.getArg 2).getArg 1).getSepArgs else #[]
            let wheres := if (cl.getArg 3).getNumArgs == 2 then ((cl.getArg 3).getArg 1).getSepArgs else #[]
            pure { acc with examples := acc.examples.push { ref := cl, name := exName, params, wheres, preds := (cl.getArg 5).getSepArgs, tac? := parseOptTacSeq (cl.getArg 6) } }
        | ``fnContractIf => collectFnContracts (guards ++ (cl.getArg 1).getSepArgs) (cl.getArg 3).getArgs.toList acc
        | _ => throwErrorAt cl "unexpected contract clause in `fn`"
      collectFnContracts guards rest acc'

private def mkTypedBinder (id : Ident) (ty : Term) : PureQuotM (TSyntax `Lean.Parser.Term.bracketedBinder) := `(bracketedBinder| ($id:ident : $ty))
private def lowerContractProp (s : Syntax) : CommandElabM Term := liftMacroM (lowerSimpleQedExpr .propInv s (allowOptElse := true) (optElseFallback := `(True)))
private def mkSuffixId (ref : Syntax) (base : Ident) (tag : String) (total idx : Nat) : Ident :=
  mkIdentFrom ref (base.getId.appendAfter (if total == 1 then tag else s!"{tag}_{idx + 1}"))

@[noinline] private def elabContractThm (isPrivate : Bool) (thmId : Ident) (baseBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (guardPfx : String) (guards : Array Syntax) (goal : Term) (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
    (defaultTac : PureQuotM (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : CommandElabM Unit := do
  let gProps ← guards.toList.mapM lowerContractProp
  let cmd ← runPureQuot do
    let binders := baseBinders ++ (← gProps.zipIdx.mapM fun (gp, i) => mkTypedBinder (mkIdent (Name.mkSimple s!"{guardPfx}{i}")) gp).toArray
    let proofTac ← match tac? with | some ts => pure ts | none => defaultTac
    `(command| set_option linter.unusedVariables false in theorem $thmId $[$binders:bracketedBinder]* : $goal := by $proofTac)
  Qed.Lang.elabCmdWithVis isPrivate cmd

@[noinline, nospecialize] private def forListCmd {α : Type} (f : α → CommandElabM Unit) : List α → CommandElabM Unit
  | [] => pure () | x :: xs => do f x; forListCmd f xs

@[noinline] def elabPureFnContracts (thmBaseId fnConstId : Ident) (paramIds : Array Ident) (paramTys : Array Term) (retTy : Term)
    (contracts : Array Syntax) (extraPreHyps : Array (Ident × Term) := #[]) (isPrivate : Bool := false) : CommandElabM Unit := do
  if contracts.isEmpty then return
  let parsed ← collectFnContracts #[] contracts.toList {}
  let reqProp? ← if parsed.requires.isEmpty then pure none else some <$> mkConjBody (← parsed.requires.toList.mapM lowerContractProp).toArray
  let prePairs := paramIds.zip paramTys ++ extraPreHyps ++ match reqProp? with | some rp => #[(mkIdent `_hReq, rp)] | none => #[]
  let baseBinders := (← runPureQuot (prePairs.toList.mapM fun (i, t) => mkTypedBinder i t)).toArray
  let rhsCall ← mkAppTerms fnConstId (paramIds.map (⟨·.raw⟩)); let paramNames := paramIds.map (·.getId.eraseMacroScopes)
  forListCmd (fun (ens, i) => do
    let thmId := mkSuffixId ens.ref thmBaseId "_ensures" parsed.ensures.size i
    let ensProp ← mkConjBody (← ens.preds.toList.mapM lowerContractProp).toArray
    elabContractThm isPrivate thmId baseBinders "_hIf_" ens.guards (← runPureQuot `(let $(mkIdent `result):ident : $retTy := $rhsCall; $ensProp)) ens.tac? `(Lean.Parser.Tactic.tacticSeq| qedProveFnEnsures $fnConstId $thmId)) parsed.ensures.toList.zipIdx
  forListCmd (fun (bl, i) => do
    let thmId := mkSuffixId bl.ref thmBaseId "_blindTo" parsed.blinds.size i
    let (freshVars, lhsArgs, _) ← buildBlindToArgs bl.targets paramNames paramIds paramTys
    let eqProp ← mkBlindToEqProp freshVars (← mkAppTerms fnConstId lhsArgs) rhsCall
    let descLit := Syntax.mkStrLit (String.intercalate ", " (bl.targets.toList.map fmtBlindTarget))
    elabContractThm isPrivate thmId baseBinders "_hIf_" bl.guards eqProp bl.tac? `(Lean.Parser.Tactic.tacticSeq| qedProveBlindTo $fnConstId $thmId $descLit)) parsed.blinds.toList.zipIdx
  forListCmd (fun ex => do
    let thmId := mkIdentFrom ex.name (thmBaseId.getId.appendAfter s!"_example_{ex.name.getId.eraseMacroScopes}")
    let pBinders ← ex.params.toList.mapM fun ep => do runPureQuot (mkTypedBinder ⟨ep.getArg 0⟩ (← liftMacroM (return (← lowerQedType (ep.getArg 2) false).1)))
    let exProp ← mkConjBody (← ex.preds.toList.mapM lowerContractProp).toArray
    elabContractThm isPrivate thmId pBinders.toArray "_hExWhere_" ex.wheres exProp ex.tac? `(Lean.Parser.Tactic.tacticSeq| qedProveFnExample $fnConstId $thmId)) parsed.examples.toList

@[noinline] private def parseFnParam (fnId : Ident) (seenDef : Bool) (paramIds : Array Ident) (rp : Syntax) :
    CommandElabM (Bool × Ident × Term × TSyntax `Lean.Parser.Term.bracketedBinder) := do
  let pid : Ident := ⟨rp.getArg 0⟩
  if paramIds.any (·.getId.eraseMacroScopes == pid.getId.eraseMacroScopes) then throwErrorAt pid s!"duplicate parameter `{pid.getId}` in `fn {fnId.getId}`"
  let pty ← liftMacroM (return (← lowerQedType (rp.getArg 2) false).1)
  if (rp.getArg 3).getNumArgs == 2 then
    let defT ← liftMacroM (lowerSimpleQedExpr .val ((rp.getArg 3).getArg 1))
    return (true, pid, pty, ← runPureQuot `(bracketedBinder| ($pid:ident : $pty := $defT)))
  if seenDef then throwErrorAt pid s!"non-default parameter `{pid.getId}` cannot follow a parameter with a default value in `fn {fnId.getId}`"
  return (false, pid, pty, ← runPureQuot (mkTypedBinder pid pty))

@[noinline, command_elab fnCmd] def elabFnCmd : CommandElab := fun stx => do
  let doc? := if (stx.getArg 0).getNumArgs == 1 then some (⟨(stx.getArg 0).getArg 0⟩ : TSyntax ``Lean.Parser.Command.docComment) else none
  let isPrivate := (stx.getArg 1).getNumArgs == 1; let fnId : Ident := ⟨stx.getArg 3⟩
  let (_, paramIds, paramTys, defBinders) ← (stx.getArg 5).getSepArgs.toList.foldlM (init := (false, #[], #[], #[]))
    fun (seenDef, ids, tys, bs) rp => do let (seen', pid, pty, b) ← parseFnParam fnId seenDef ids rp; return (seen', ids.push pid, tys.push pty, bs.push b)
  let retTy ← liftMacroM (return (← lowerQedType (stx.getArg 8) false).1)
  let bodyTerm ← lowerPureFnStmts s!"fn {fnId.getId}" (stx.getArg 11).getArgs.toList
  Qed.Lang.elabCmdWithVis isPrivate (← runPureQuot `(command| $[$doc?:docComment]? def $fnId $[$defBinders:bracketedBinder]* : $retTy := $bodyTerm))
  elabPureFnContracts fnId fnId paramIds paramTys retTy (stx.getArg 10).getArgs #[] isPrivate

end FnElab
end Qed
