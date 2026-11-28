import Qed.Verify.Core
import Qed.Field
import Qed.Server.Core
import Qed.Server.Syntax
import Qed.Server.Registry

namespace Qed.Server

@[inline] instance {Inner : Type} {p : Inner → Prop} : SrvLiftOpt (Qed.Field p) Inner := ⟨fun f => some f.val⟩
@[inline] instance {Inner : Type} {p : Inner → Prop} : SrvLiftOpt (Option (Qed.Field p)) Inner := ⟨Option.map Qed.Field.val⟩

theorem srvDiteFalse_eq_true {P : Prop} [Decidable P] (t : P → Bool) :
    ((if h : P then t h else false) = true) ↔ ∃ h : P, t h = true := by by_cases hP : P <;> simp [hP]
theorem srvDiteFalse_eq_false {P : Prop} [Decidable P] (t : P → Bool) :
    ((if h : P then t h else false) = false) ↔ ∀ h : P, t h = false := by by_cases hP : P <;> simp [hP]

/-! ## Cached `Simp.Context` Rule Sets & Pipeline Combinators -/

open Lean Meta Elab Term Tactic Qed.Verify.Core

private inductive ProgStepMode where | preserves | ensures | effSpec | noAtomic deriving BEq

private def mkNameSet (ns : Array Name) : NameSet := ns.foldl (·.insert ·) {}
@[noinline] private def mkNm (pfx : Name) (s : String) : Name := (s.splitOn ".").foldl Name.str pfx
@[noinline] private def srvNm (s : String) : Name := mkNm `Qed.Server s
@[noinline] private def splitNms (pfx : Name) (s : String) : Array Name :=
  (s.splitOn " ").toArray.foldl (init := #[]) fun a w => if w.isEmpty then a else a.push (mkNm pfx w)
@[noinline] private def hasAnyConst (e : Expr) (p : Name → Bool) : Bool := (e.find? fun | .const c _ => p c | _ => false).isSome
@[noinline] private def hasConst (e : Expr) (c : Name) : Bool := hasAnyConst e (· == c)

@[noinline] private def findMeta {α β : Type} (xs : Array α) (f : α → MetaM (Option β)) : MetaM (Option β) :=
  let rec go : Nat → MetaM (Option β)
    | 0 => pure none
    | r + 1 => do let i := xs.size - (r + 1); if h : i < xs.size then match ← f xs[i] with | some v => pure (some v) | none => go r else pure none
  go xs.size

@[noinline] private def foldlGoalMeta {α : Type} (xs : Array α) (g0 : MVarId) (f : MVarId → α → MetaM (Option MVarId)) : MetaM (Option MVarId) :=
  let rec go : Nat → MVarId → MetaM (Option MVarId)
    | 0, g => pure (some g)
    | r + 1, g => do let i := xs.size - (r + 1); if h : i < xs.size then match ← f g xs[i] with | none => pure none | some g' => go r g' else pure (some g)
  go xs.size g0

@[noinline] private def runGoalPipe (g0 : MVarId) : List (MVarId → MetaM (Option MVarId)) → MetaM (Option MVarId)
  | [] => pure (some g0) | f :: fs => do match ← f g0 with | none => pure none | some g' => runGoalPipe g' fs

@[noinline] private def filterMapGoalsMeta (f : MVarId → MetaM (Option MVarId)) : List MVarId → MetaM (List MVarId)
  | [] => pure [] | g :: gs => do let hd ← f g; let tl ← filterMapGoalsMeta f gs; pure (hd.elim tl (· :: tl))

@[noinline] private def flatMapGoalsTactic (f : MVarId → TacticM (List MVarId)) : List MVarId → TacticM (List MVarId)
  | [] => pure [] | g :: gs => return (← f g) ++ (← flatMapGoalsTactic f gs)

@[noinline] private def resolveIdentMeta (id : Ident) : MetaM Name := resolveGlobalConstNoOverload id
@[noinline] private def resolveIdentsMeta (ids : Array Ident) : MetaM (Array Name) := mapMeta ids resolveIdentMeta

private def strLenSP : Array Name := #[``qedReduceStrLen]
private def valUnwrapSimpNames : Array Name := splitNms `Qed.Server "srvGetAt_eq SrvIdx.toNat_nat SrvIdx.toNat_fin" ++ valUnwrapBaseNames
private def liftOptSimpNames : Array Name := splitNms `Qed.Server "SrvLiftOpt.liftOpt_opt SrvLiftOpt.liftOpt_val"
private def arrayCoreSimpNames : Array Name := splitNms .anonymous "Array.size_set Array.size_push Array.getElem_set_self Qed.Lang.QedSeqLit.ofList_array Qed.Lang.QedSeqLit.ofList_list" ++ dictSimpNames
private def unwrapOkSimpNames : Array Name := splitNms `Qed.Server "srvUnwrap_srvFailure_ok_iff srvUnwrap_str_ok_iff srvUnwrap_opt_ok_iff"
private def diteFalseSimpNames : Array Name := splitNms `Qed.Server "srvDiteFalse_eq_true srvDiteFalse_eq_false"
private def arrayAndBoolSimpNames : Array Name := #[``id_eq, ``ne_eq, ``Array.size_modify] ++ diteFalseSimpNames ++ valUnwrapSimpNames ++ arrayCoreSimpNames ++ boolSimpNames
private def stepCombSimpNames : Array Name := splitNms `Qed.Server "srvSeq_none srvSeq_some srvEmitSeq_none srvEmitSeq_some srvFinish_ok srvFinish_err srvFinish_none srvFinishEmit_ok srvFinishEmit_err srvFinishEmit_none srvAtomicCommit_none srvAtomicCommit_ok srvAtomicCommit_err srvAtomicCommitEmit_none srvAtomicCommitEmit_ok srvAtomicCommitEmit_err"
private def stepLetEqSimpNames : Array Name := splitNms `Qed.Server "srvSeq_srvLetEq srvEmitSeq_srvLetEq srvFinish_srvLetEq srvFinishEmit_srvLetEq srvAtomicCommit_srvLetEq srvAtomicCommitEmit_srvLetEq srvWithNewState_srvLetEq prod_fst_srvLetEq prod_snd_srvLetEq"
private def ensPostSimpNames : Array Name := splitNms `Qed.Server "srvEnsPost_ok srvEnsPost_err srvEnsPost_srvLetEq srvEnsPostOpt_some srvEnsPostOpt_none srvEnsPostOpt_err srvEnsPostOpt_srvLetEq srvEnsPostOpt_ok_iff srvEnsFails_ok srvEnsFails_err srvEnsFails_srvLetEq srvEnsFailsCode_ok srvEnsFailsCode_err srvEnsFailsCode_srvLetEq"

private def isSrvEqDecl (decl : LocalDecl) : Bool := !decl.userName.hasMacroScopes && let u := decl.userName.toString; u.startsWith "_srvEq" || u.startsWith "_hLet"
def collectProofFacts (extraExprs : Array Expr) : TermElabM (Array Expr) :=
  liftMetaM <| collectFacts { scanLCtx := true, scanLCtxValues := true, includeMacroPropHyps := true, includeFin := true, skipDecl := fun d _ => isSrvEqDecl d } extraExprs

private def unsteppedCtrlSet : NameSet := mkNameSet (splitNms `Qed.Server "srvLetEq srvFinish srvFinishEmit srvSeq srvEmitSeq srvAtomicCommit srvAtomicCommitEmit srvEnsPost srvEnsPostOpt srvEnsFails srvEnsFailsCode" ++ #[``ite, ``dite])
private def hasUnsteppedCtrlFlow (e : Expr) : Bool := hasAnyConst e unsteppedCtrlSet.contains

private def tryCloseSrvTrivial (g : MVarId) : MetaM Bool := tryCloseTrivial g hasUnsteppedCtrlFlow
private def tryCloseSrvBasic (g : MVarId) : MetaM Bool := tryCloseBasic g hasUnsteppedCtrlFlow
private def goalType (g : MVarId) : MetaM Expr := g.withContext do instantiateMVars (← g.getType)
private def dsimpTargetOnly (g : MVarId) : MetaM (Option MVarId) := do simpGoalOnly g (← mkEmptyDsimpCtx) #[] #[] true true
private def maybeEnsureType (expectedType? : Option Expr) (e : Expr) : TermElabM Expr := expectedType?.elim (pure e) (ensureHasType · e)
private def closeIf (p : MVarId → MetaM Bool) (g : MVarId) : MetaM (Option MVarId) := do if ← p g then return none else return some g
private def liftStep (f : MVarId → MetaM MVarId) (g : MVarId) : MetaM (Option MVarId) := some <$> f g
private def userDecls (g : MVarId) : MetaM (Array (LocalDecl × Expr)) :=
  g.withContext <| collectLCtxDecls (includeLet := false) fun d => return some (d, ← instantiateMVars d.type)
private abbrev trySaveOpt {α : Type} (act : MetaM (Option α)) : MetaM (Option α) := tryRestoreMeta none Option.isSome act

private def simpCached (g : MVarId) (key : String) (ns : Array Name) (cfg : Simp.Config := {}) (sp : Array Name := #[])
    (fvs : Array FVarId := #[]) (simpTgt := true) (dsimpOnly := false) (allHyps := false) : MetaM (Option MVarId) := do
  let (ctx, sps) ← mkCachedSimpCtx key ns cfg sp dsimpOnly
  if allHyps then simpGoalAllHyps g ctx sps dsimpOnly else simpGoalOnly g ctx sps fvs simpTgt dsimpOnly

private def dsimpCodecGoal (g : MVarId) : MetaM (Option MVarId) :=
  simpCached g "dsimpCodec" (#[``Qed.Lang.QedVal.val, ``Qed.Server.SrvIdx.toNat, ``Qed.Server.SrvLiftOpt.liftOpt, ``Qed.Server.srvGetAt] ++ optCodecSimpNames)
    { zetaDelta := false } #[] #[] true true

private def dsimpCodecAndStrLen (g0 : MVarId) : MetaM (Option MVarId) :=
  runGoalPipe g0 [dsimpCodecGoal, fun g => simpCached g "strLenOnly" #[] { zetaDelta := false } strLenSP]

private def srvHelperSet : NameSet := mkNameSet #[``srvGetAt, ``Qed.Lang.QedVal.val, ``SrvIdx.toNat, ``SrvLiftOpt.liftOpt]
private def hasSrvHelperConst (e : Expr) : Bool := hasAnyConst e fun c => srvHelperSet.contains c || c == ``id

private def unfoldSrvHelpersExpr (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun sub => do
    if sub.isAppOfArity ``id 2 then return .visit sub.getAppArgs[1]!
    if let some cn := sub.getAppFn.constName? then if srvHelperSet.contains cn then
      let u? ← match ← unfoldProjInst? sub with | some x => pure (some x) | none => unfoldDefinition? sub
      if let some u := u? then return .visit (if u.isAppOfArity ``id 2 then u.getAppArgs[1]! else u)
    return .continue)

private def nextFreshSrvName (g : MVarId) (pfx : String) (startIdx : Nat) : MetaM (Name × Nat) := do
  let lctx ← g.withContext getLCtx
  let rec go : Nat → Nat → Name × Nat
    | 0, i => (Name.mkSimple s!"{pfx}{i}", i + 1)
    | fuel + 1, i => let cand := Name.mkSimple s!"{pfx}{i}"; if lctx.any (·.userName == cand) then go fuel (i + 1) else (cand, i + 1)
  return go (lctx.size + 1) startIdx

private def maybeRenameMacro (g : MVarId) (decl : LocalDecl) (pfx : String) (idx : Nat) : MetaM (MVarId × Nat) := do
  if !decl.userName.hasMacroScopes then return (g, idx)
  let (cand, nxt) ← nextFreshSrvName g pfx idx; return (← g.rename decl.fvarId cand, nxt)

@[noinline] private def unfoldSrvHelpersGoal (g0 : MVarId) : MetaM MVarId := do
  let (g, hIdx, propFVars) ← foldlMeta (← userDecls g0) (g0, (← g0.withContext getLCtx).size, (#[] : Array FVarId)) fun (g, hIdx, pfs) (decl, ty) => do
    if isSrvEqDecl decl then return (g, hIdx, pfs)
    if !(← g.withContext (isPropSafe ty)) then return (g, hIdx, pfs)
    let (g', nxt) ← maybeRenameMacro g decl "_srvSplitH" hIdx
    return (g', nxt, if hasSrvHelperConst ty then pfs.push decl.fvarId else pfs)
  let (g, _) ← foldlMeta propFVars.reverse (g, hIdx) fun (g, hIdx) fv => do
    let some decl := (← g.withContext getLCtx).find? fv | return (g, hIdx)
    let ty ← g.withContext (instantiateMVars decl.type)
    if !hasSrvHelperConst ty then return (g, hIdx)
    let ty' ← g.withContext (unfoldSrvHelpersExpr ty)
    if ty' == ty then return (g, hIdx)
    let (g, hIdx) ← if (← goalType g).containsFVar fv then
        let (cand, nxt) ← nextFreshSrvName g "_srvFreeH" hIdx
        pure ((← (← g.assert cand ty' (mkFVar fv)).intro1P).2, nxt)
      else pure (g, hIdx)
    return (← tryGoalM g (·.changeLocalDecl fv ty'), hIdx)
  let tgt ← goalType g
  if hasSrvHelperConst tgt then
    let tgt' ← g.withContext (unfoldSrvHelpersExpr tgt)
    if tgt' != tgt then return ← tryGoalM g (·.change tgt')
  return g

@[noinline] private def simpHypsEachGoal (g0 : MVarId) : MetaM (Option MVarId) := do
  let hFVars ← g0.withContext <| collectLCtxDecls (includeLet := false) fun d => do
    if d.userName.hasMacroScopes || isSrvEqDecl d then return none
    if ← isPropSafe (← instantiateMVars d.type) then return some d.fvarId else return none
  let some g ← (if hFVars.isEmpty then pure (some g0) else do
    let (hypCtx, _) ← mkCachedSimpCtx "hypSimpEach"
      (#[``id_eq, ``ne_eq, ``Prod.mk.injEq, ``Option.some.injEq, ``Except.ok.injEq, ``Except.error.injEq, ``reduceCtorEq,
         ``Qed.Lang.not_qedAndProp, ``Qed.Lang.not_qedOrProp] ++ ensPostSimpNames ++ diteFalseSimpNames ++ unwrapOkSimpNames ++
       valUnwrapSimpNames ++ liftOptSimpNames ++ optCodecSimpNames ++ arrayCoreSimpNames ++ boolSimpNames)
    match ← trySaveOpt (some <$> (match (← simpGoal g0 hypCtx #[] none false hFVars).1 with | none => pure none | some (_, g') => pure (some g'))) with
    | some r => pure r
    | none => foldlGoalMeta hFVars g0 fun g fv => simpGoalOnly g hypCtx #[] #[fv] false false) | return none
  simpCached g "tgtSimpEach" (#[``id_eq, ``ne_eq, ``Array.forall_push, ``Array.sumBy_empty, ``Array.sumBy_push] ++
    stepCombSimpNames ++ valUnwrapSimpNames ++ liftOptSimpNames ++ arrayCoreSimpNames ++ boolSimpNames)

/-! ## Custom Term Elaborators (`srvAutoField`, `srvAutoEmit`, `srvTypedAs`, `srvGetElem`, `srvSetElem`) -/

private def isTinyProofExpr (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isFVar || e.isConst || match e.getAppFn.constName?, e.getAppNumArgs with
    | some ``Eq.refl, 2 | some ``of_decide_eq_true, 3 | some ``Nat.le_refl, 1
    | some `Qed.Field.ok, 3 | some `Qed.Ensured.ok, 3 | some ``Fin.isLt, 2 => true | _, _ => false

private def wrapAuxProof (goalProp prf : Expr) : TermElabM Expr := do
  let prf ← instantiateMVars prf; let goalProp ← instantiateMVars goalProp
  if prf.hasMVar || goalProp.hasMVar || isTinyProofExpr prf then return prf
  let lctx ← getLCtx; let hasLet (e : Expr) := e.hasAnyFVar fun fv => (lctx.find? fv).any (·.isLet)
  if hasLet goalProp || hasLet prf then return prf
  liftMetaM <| Meta.mkAuxTheorem goalProp prf (zetaDelta := false)

private def proveGoalWithMeta (facts : Array Expr) (goalProp : Expr) (solver : MVarId → Array FVarId → MetaM Bool) : TermElabM (Option Expr) := do
  let s ← saveState
  try
    let mvar ← mkFreshExprMVar goalProp
    let (g, factFVars) ← assertFacts mvar.mvarId! "_srvFact" facts
    if ← solver g factFVars then
      let prf ← instantiateMVars mvar
      unless prf.hasMVar do return some prf
  catch _ => pure ()
  restoreState s; return none

private def solveRefinementSlow (g0 : MVarId) : MetaM Bool := do
  return (← runGoalPipe g0 [
    liftStep (tryGoalM · unfoldSrvHelpersGoal), (tryGoalOptM · simpHypsEachGoal),
    (simpCached · "slowRefinement" (#[``id_eq, ``ne_eq] ++ valUnwrapSimpNames ++ arrayCoreSimpNames ++ boolSimpNames) { zetaDelta := false } strLenSP),
    dsimpCodecAndStrLen, closeIf tryCloseSrvBasic,
    fun g => do let (_, sp) ← mkCachedSimpCtx "strLenOnly" #[] { zetaDelta := false } strLenSP; trySimpAll g (← mkSimpCtxWithBase valUnwrapBaseNames) sp,
    closeIf tryCloseSrvBasic]).isNone

private def solveAutoFieldFast (isLit : Bool) (g0 : MVarId) (factFVars : Array FVarId) : MetaM Bool := do
  if isLit && factFVars.isEmpty then
    return (← runGoalPipe g0 [(simpCached · "litField" (#[``id_eq, ``Qed.Lang.QedVal.val_id] ++ optCodecSimpNames) { zetaDelta := false } strLenSP), closeIf tryCloseSrvBasic]).isNone
  return (← runGoalPipe g0 [
    (simpCached · "fastField" (#[``id_eq] ++ valUnwrapSimpNames ++ optCodecSimpNames) { zetaDelta := false } strLenSP factFVars),
    closeIf tryCloseSrvBasic, dsimpCodecAndStrLen, closeIf tryCloseSrvBasic]).isNone

private def throwFieldRuleFailed (stx : Syntax) (predFn valExpr : Expr) : TermElabM α := do
  let mut p := predFn.consumeMData
  if p.isAppOfArity `Qed.Codec.valid 2 then
    let mut c := (p.getArg! 1).consumeMData
    while c.isAppOfArity `Qed.Codec.jsonOnly 2 do c := (c.getArg! 1).consumeMData
    if c.isAppOfArity `Qed.Codec.refine 4 then p := c.getArg! 2
  throwErrorAt stx m!"Schema field rule `{← Qed.Diag.ppQedExpr ((Expr.app p valExpr).headBeta)}` failed for `{← Qed.Diag.ppQedExpr valExpr}`.\n\n\
    Hint: Guard this value with `if ...:` or a `requires` precondition so it satisfies the schema's `where` rule."

@[noinline] private def elabAutoFieldTerm (stx : Syntax) (valStx : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  if let some expTy := expectedType? then
    let expTy ← instantiateMVars expTy
    if !expTy.getAppFn.isMVar then
      let expWhnf ← whnf expTy
      if expWhnf.isAppOfArity ``Qed.Field 2 then
        let saved ← saveState; let preMsgs := (← Core.getMessageLog).toList.length
        let direct? ← try
          let e ← Term.withoutErrToSorry <| elabTermEnsuringType valStx (some expTy); synthesizeSyntheticMVarsNoPostponing
          let e ← instantiateMVars e
          pure (if (← Core.getMessageLog).toList.length == preMsgs && !e.hasMVar then some e else none)
        catch _ => pure none
        if let some direct := direct? then return direct
        restoreState saved
        let (innerTy, predFn) := (expWhnf.getAppArgs[0]!, expWhnf.getAppArgs[1]!)
        let valExpr ← elabTermEnsuringType valStx (some innerTy); synthesizeSyntheticMVarsNoPostponing
        let valExpr ← instantiateMVars valExpr; let goalProp := mkApp predFn valExpr
        let isLit := valExpr.isLit || (valExpr.getAppFn.isConstOf ``OfNat.ofNat && !valExpr.hasFVar)
        let localFacts ← if isLit then pure #[] else liftMetaM <| collectFacts { scanLCtx := false, includeFin := true } #[valExpr]
        let prf? ← match ← proveGoalWithMeta localFacts goalProp (solveAutoFieldFast isLit) with
          | some p => pure (some p)
          | none => proveGoalWithMeta (← collectProofFacts #[valExpr]) goalProp (fun g _ => solveRefinementSlow g)
        let some prfExpr := prf? | throwFieldRuleFailed stx predFn valExpr
        return ← mkAppOptM ``Qed.Field.mk #[some innerTy, some predFn, some valExpr, some (← wrapAuxProof goalProp prfExpr)]
      else return ← try elabTermEnsuringType valStx (some expTy)
        catch _ => do let raw ← elabTerm valStx none; ensureHasType expTy (← mkAppM ``Qed.Lang.QedVal.val #[raw])
  let e ← elabTerm valStx none; synthesizeSyntheticMVars (postpone := .yes)
  let ty ← whnf (← instantiateMVars (← inferType e))
  maybeEnsureType expectedType? (← if ty.isAppOfArity ``Qed.Field 2 then mkAppM ``Qed.Field.val #[e] else pure e)

@[term_elab srvAutoFieldStx] def elabSrvAutoField : TermElab := fun stx expectedType? =>
  elabAutoFieldTerm stx ⟨stx.getArg 1⟩ expectedType?

@[noinline, term_elab srvAutoEmitStx] def elabSrvAutoEmit : TermElab := fun stx expectedType? => do
  let propExpr ← match expectedType? with | some expTy => instantiateMVars expTy | none => elabTerm (stx.getArg 1) (some (mkSort Level.zero))
  let some prfExpr ← proveGoalWithMeta (← collectProofFacts #[propExpr]) propExpr (fun g _ => solveRefinementSlow g)
    | throwErrorAt stx m!"Channel `ensures` postcondition failed at `emit`:\n  • must satisfy:  {← Qed.Diag.ppQedExpr ((← unfoldDefinition? propExpr).getD propExpr)}\n\n\
        Hint: Ensure the emitted event satisfies the channel's `ensures` clause."
  wrapAuxProof propExpr prfExpr

@[term_elab srvTypedAsStx] def elabSrvTypedAs : TermElab := fun stx expectedType? => do
  let tplExpr ← elabTerm (stx.getArg 1) none; synthesizeSyntheticMVarsNoPostponing
  maybeEnsureType expectedType? (← elabTermEnsuringType (stx.getArg 3) (some (← instantiateMVars (← inferType tplExpr))))

/-! ## Bounds Checking (`srvGetElem`, `srvSetElem`): O(N) Size-Chain Fast Path -/

private def unwrapSizeSet? (e : Expr) : Nat → MetaM (Option (Expr × Expr))
  | 0 => return none
  | fuel + 1 => do
      let eC := e.consumeMData
      if eC.isAppOfArity ``Array.set 5 then
        let a := eC.getAppArgs; return some (a[1]!, ← mkAppOptM ``Array.size_set #[some a[0]!, some a[1]!, some a[2]!, some a[3]!, some a[4]!])
      else if eC.isAppOfArity ``srvLetEq 4 then
        let a := eC.getAppArgs; unwrapSizeSet? (mkApp2 a[3]! a[2]! (← mkEqRefl a[2]!)).headBeta fuel
      else return none

@[noinline] private def proveSizeEqChain (startArr : Expr) : MetaM (Expr × Option Expr) := do
  let rec go : Nat → Expr → Option Expr → Array FVarId → MetaM (Expr × Option Expr)
    | 0, cur, eqOpt?, _ => return (cur, eqOpt?)
    | fuel + 1, cur, eqOpt?, seen => do
        let .fvar fv := cur.consumeMData | return (cur, eqOpt?)
        if seen.contains fv then return (cur, eqOpt?)
        let next? ← findLCtxDecl? (includeLet := false) fun decl => do
          let some (_, lhs, rhs) := (← instantiateMVars decl.type).eq? | return none
          if lhs.consumeMData != Expr.fvar fv then return none
          let rhsC := rhs.consumeMData; let arrTy ← whnf (← inferType cur)
          let elemTy := if arrTy.isAppOfArity ``Array 1 then arrTy.getAppArgs[0]! else mkConst ``Unit
          let mkSizeCongr := do mkAppM ``congrArg #[← mkAppOptM ``Array.size #[some elemTy], decl.toExpr]
          if let some (prevArr, eqSet) ← try unwrapSizeSet? rhsC 8 catch _ => pure none then
            return some (prevArr, ← mkEqSymm (← mkEqTrans (← mkSizeCongr) eqSet))
          else if !rhsC.containsFVar fv && !hasConst rhsC ``srvLetEq then
            return some (rhsC, ← mkEqSymm (← mkSizeCongr))
          else return none
        match next? with
        | some (prevArr, prevEqCur) => go fuel prevArr (some (← eqOpt?.elim (pure prevEqCur) (mkEqTrans prevEqCur ·))) (seen.push fv)
        | none => return (cur, eqOpt?)
  go (← getLCtx).size startArr none #[]

private def boundsKeepSet : NameSet := mkNameSet #[``Array.size, ``LT.lt, ``LE.le, ``GE.ge, ``GT.gt]
private def boundsSkipSet : NameSet := mkNameSet #[``srvGetAt, ``RequestCtx, ``Array.set]

private def solveBoundsFast (g0 : MVarId) : MetaM Bool := do
  let some g1 ← runGoalPipe g0 [closeIf tryCloseSrvTrivial, (tryGoalOptM · (simpCached · "boundsTgt" (#[``id_eq, ``Array.size_set, ``Array.size_push, ``Array.size_modify] ++ valUnwrapSimpNames) { zetaDelta := true }))] | return true
  let sizeFVars ← g1.withContext <| collectLCtxDecls (includeLet := false) fun d => do
    if d.userName.hasMacroScopes then return none
    let ty ← instantiateMVars d.type
    if ← isPropSafe ty then
      if hasAnyConst ty boundsKeepSet.contains && !hasAnyConst ty boundsSkipSet.contains then return some d.fvarId
    return none
  return (← runGoalPipe g1 [
    fun g => if sizeFVars.isEmpty then pure (some g) else tryGoalOptM g (simpCached · "boundsHyp" (#[``id_eq, ``ne_eq, ``Qed.Lang.not_qedAndProp, ``Qed.Lang.not_qedOrProp] ++ valUnwrapSimpNames ++ boolSimpNames) {} #[] sizeFVars false),
    closeIf tryCloseSrvTrivial, closeIf tryDirectOmega]).isNone

private def solveBoundsSlow (g0 : MVarId) : MetaM Bool := do
  let some g' ← runGoalPipe g0 [
    liftStep (tryGoalM · unfoldSrvHelpersGoal),
    fun g => do tryGoalOptM g (simpGoalAllHyps · (← mkEmptyDsimpCtx { zetaDelta := true }) #[] true),
    (simpCached · "arrayAndBool" arrayAndBoolSimpNames { zetaDelta := true } (allHyps := true)),
    liftStep fun g => try Prod.fst <$> splitAndHypsGoal g catch _ => pure g,
    closeIf tryCloseSrvTrivial, closeIf tryDirectOmega,
    fun g => do trySimpAll g (← mkSimpCtxWithBase #[] { zetaDelta := true }),
    closeIf tryDirectOmega] | return true
  let (spCtx, _) ← mkCachedSimpCtx "boundsSplitSize" #[``Array.size_set, ``Array.size_push] { zetaDelta := true }
  let rec splitLoop : Nat → List MVarId → MetaM Bool
    | _, [] => return true | 0, _ => return false
    | f + 1, cur :: rest => do
        if let some sgs ← trySplitTarget cur then splitLoop f (sgs ++ rest)
        else match ← simpGoalAllHyps cur spCtx with
          | none => splitLoop f rest
          | some c' => if ← tryDirectOmega c' then splitLoop f rest else return false
  splitLoop 16 [g']

@[noinline] private def elabSrvArrOrDictOp (stx : Syntax) (arrStx idxStx : Term) (valStx? : Option Term) (expectedType? : Option Expr) : TermElabM Expr := do
  let arrExpr ← elabTerm arrStx none; synthesizeSyntheticMVarsNoPostponing
  let arrExpr ← instantiateMVars arrExpr; let arrTy ← whnf (← inferType arrExpr)
  if arrTy.isAppOfArity `Qed.Dict 2 then
    let keyExpr ← elabTermEnsuringType idxStx (some arrTy.getAppArgs[0]!)
    let res ← match valStx? with
      | none => mkAppM `Qed.Dict.get #[arrExpr, keyExpr]
      | some v => do
          let valExpr ← elabAutoFieldTerm v v (some arrTy.getAppArgs[1]!)
          mkAppM `Qed.Dict.set #[arrExpr, keyExpr, valExpr]
    return ← maybeEnsureType expectedType? res
  unless arrTy.isAppOfArity ``Array 1 do
    throwErrorAt arrStx m!"expected an array (`T[]`) for {if valStx?.isSome then "indexed assignment" else "indexing"}, got `{← ppExpr arrTy}`"
  let elemTy := arrTy.getAppArgs[0]!
  let idxNatExpr ← elabTermEnsuringType (← `(Qed.Server.SrvIdx.toNat $idxStx)) (some (mkConst ``Nat))
  let valExpr? ← match valStx? with | none => pure none | some v => some <$> elabAutoFieldTerm v v (some elemTy)
  synthesizeSyntheticMVarsNoPostponing
  let arrExpr ← instantiateMVars arrExpr; let idxNatExpr ← instantiateMVars idxNatExpr
  let valExpr? ← match valExpr? with | none => pure none | some v => some <$> instantiateMVars v
  let goalProp ← mkAppM ``LT.lt #[idxNatExpr, ← mkAppM ``Array.size #[arrExpr]]
  let (baseArr, sizeEqOpt?) ← proveSizeEqChain arrExpr
  let ltPrf ← if let some basePrf ← proveGoalWithMeta #[] (← mkAppM ``LT.lt #[idxNatExpr, ← mkAppM ``Array.size #[baseArr]]) (fun g _ => solveBoundsFast g) then
      wrapAuxProof goalProp (← sizeEqOpt?.elim (pure basePrf) fun eqPrf => mkAppM ``Nat.lt_of_lt_of_eq #[basePrf, eqPrf])
    else
      let some prfExpr ← proveGoalWithMeta (← collectProofFacts #[arrExpr, idxNatExpr]) goalProp (fun g _ => solveBoundsSlow g)
        | do let (pArr, pIdx) := (← Qed.Diag.ppQedExpr arrExpr, ← Qed.Diag.ppQedExpr idxNatExpr)
             throwErrorAt stx m!"Array index `{pIdx}` could be out of bounds for `{pArr}`:\n  • must satisfy:  {pIdx} < {pArr}.size\n\nHint: Guard this access with `if {pIdx} < {pArr}.size:`."
      wrapAuxProof goalProp prfExpr
  maybeEnsureType expectedType? (← match valExpr? with
    | none => mkAppOptM ``srvGetAt #[some elemTy, some arrExpr, some idxNatExpr, some ltPrf]
    | some v => mkAppOptM ``Array.set #[some elemTy, some arrExpr, some idxNatExpr, some v, some ltPrf])

@[term_elab srvGetElemStx] def elabSrvGetElem : TermElab := fun stx => elabSrvArrOrDictOp stx ⟨stx.getArg 1⟩ ⟨stx.getArg 3⟩ none
@[term_elab srvSetElemStx] def elabSrvSetElem : TermElab := fun stx => elabSrvArrOrDictOp stx ⟨stx.getArg 1⟩ ⟨stx.getArg 3⟩ (some ⟨stx.getArg 5⟩)

/-! ## Automated Server Invariant Prover (`qedSrvProveStep`, `qedSrvProveAsync`) -/

@[noinline] private def finishAtomGoal (g0 : MVarId) (allowDeepFallback : Bool := true) : TacticM (Option MVarId) := do
  let some g ← runGoalPipe g0 [
    closeIf tryCloseSrvTrivial, liftStep unfoldSrvHelpersGoal,
    (simpCached · "finishAtomPre" (valUnwrapSimpNames ++ liftOptSimpNames ++ #[``Array.getElem_set_self] ++ dictSimpNames)),
    dsimpCodecGoal, closeIf tryCloseSrvTrivial, closeIf tryDirectOmega] | return none
  let (g, invFactFVars) ← collectAndAssertFacts g "_invFact" {
    includeFin := true, includeCollectionRules := true, rounds := 4,
    skipDecl := fun d dty => isSrvEqDecl d && match dty.eq? with | some (_, _, rhs) => hasAnyConst rhs fun c => c == ``Array.set || c == ``Array.push | none => true }
  let some g ← runGoalPipe g [
    fun g => if invFactFVars.isEmpty then pure (some g) else simpCached g "optCodecDsimp" optCodecSimpNames { zetaDelta := false } #[] invFactFVars false true,
    dsimpCodecGoal, closeIf tryCloseSrvBasic,
    (simpCached · "finishAtomFb" (valUnwrapSimpNames ++ arrayCoreSimpNames)), closeIf tryCloseSrvBasic] | return none
  if allowDeepFallback then
    if ← closeWithFallback g { skipTarget := hasUnsteppedCtrlFlow, trySimpStarOmega := true, deepExtraSimpAll := #[``Qed.Server.srvLetEq] } then return none
  return some g

/-! ### Dedicated O(N) Linear Passes -/

private def collectReadySrvLetEqs (e : Expr) : Nat → MetaM (Array Expr)
  | 0 => return #[]
  | fuel + 1 => do
      let e := e.consumeMData
      if e.isAppOfArity ``Qed.Server.srvLetEq 4 then return (if !e.hasLooseBVars then #[e] else #[]) ++ (← collectReadySrvLetEqs e.getAppArgs[2]! fuel)
      else if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then collectReadySrvLetEqs e.getAppArgs[1]! fuel
      else match e with
        | .app f a | .forallE _ f a _ => return (← collectReadySrvLetEqs f fuel) ++ (← collectReadySrvLetEqs a fuel)
        | .proj _ _ b | .letE _ _ b _ _ => collectReadySrvLetEqs b fuel | _ => return #[]

private def tryPickSrvLetEq (gGoal : MVarId) (cands : Array Expr) (revCount : Nat) : MetaM (Option (Expr × Expr × MVarId × Nat)) := do
  let tgtNow ← goalType gGoal
  findMeta cands fun letApp => trySaveOpt <| gGoal.withContext do
    let a := letApp.getAppArgs; let absBody ← Meta.kabstract tgtNow letApp
    unless absBody.hasLooseBVar 0 do return none
    let pred := Lean.mkLambda `_ BinderInfo.default a[1]! absBody
    unless (← Meta.isTypeCorrect pred) do return none
    let elimPrf ← Meta.mkAppOptM ``Qed.Server.srvLetEq_elim #[some a[0]!, some a[1]!, some pred, some a[2]!, some a[3]!]
    match ← try some <$> gGoal.apply elimPrf catch _ => pure none with | some [sg] => return some (a[3]!, absBody, sg, revCount) | _ => return none

@[noinline] private def elimSrvLetEqGoal (g : MVarId) (allowHyps : Bool := true) : MetaM (Option MVarId) := do
  let tgt ← goalType g
  let mut picked? ← if hasConst tgt ``Qed.Server.srvLetEq then tryPickSrvLetEq g (← collectReadySrvLetEqs tgt 1024) 0 else pure none
  if picked?.isNone && allowHyps then
    picked? ← findMeta (← userDecls g) fun (d, dty) => do
      if !hasConst dty ``Qed.Server.srvLetEq then return none
      let cands ← collectReadySrvLetEqs dty 1024
      if cands.isEmpty then return none
      trySaveOpt do let (rev, gRev) ← g.revert #[d.fvarId]; tryPickSrvLetEq gRev cands rev.size
  let some (kFun, absBody, newGoal, revCount) := picked? | return none
  let (valName, idx1) ← nextFreshSrvName newGoal "_srvVal" (← newGoal.withContext getLCtx).size
  let (eqName, _) ← nextFreshSrvName newGoal "_srvEq" idx1
  let (valFVar, g1) ← newGoal.intro valName; let (eqFVar, g2) ← g1.intro eqName
  let g3 ← tryGoalM g2 (·.change (absBody.instantiate1 (mkApp2 kFun (mkFVar valFVar) (mkFVar eqFVar)).headBeta))
  some <$> if revCount > 0 then tryGoalM g3 (Prod.snd <$> ·.introN revCount) else pure g3

private def elimAllSrvLetEqTarget (g0 : MVarId) : MetaM (MVarId × Bool) :=
  let rec go : Nat → MVarId → Bool → MetaM (MVarId × Bool)
    | 0, g, did => return (g, did)
    | fuel + 1, g, did => do match ← elimSrvLetEqGoal g false with | some g' => go fuel g' true | none => return (g, did)
  go 128 g0 false

private def rewriteTargetByFVar (g : MVarId) (eqFVar : FVarId) : MetaM (Option MVarId) :=
  trySaveOpt do let r ← g.withContext (g.rewrite (← goalType g) (mkFVar eqFVar)); some <$> g.replaceTargetEq r.eNew r.eqProof

@[noinline] private def mkArrCongrSimp? (g : MVarId) (elemTy lhs rhs : Expr) (eqFv : FVarId) : MetaM (Option (Simp.Context × Simp.SimprocsArray)) :=
  g.withContext do try
    let base ← getCachedSimpThms "arrSetSimp" #[``Array.getElem_set_self, ``Array.getElem_set]
    let sizeLhs ← mkAppM ``Array.size #[lhs]
    let (c1, c2) ← withLocalDecl `j .implicit (mkConst ``Nat) fun j => do withLocalDeclD `hj (← mkAppM ``LT.lt #[j, sizeLhs]) fun hj => do
      let mk (c : Name) := do mkLambdaFVars #[j, hj] (← mkAppOptM c #[some elemTy, some rhs, some lhs, some j, some (mkFVar eqFv), some hj])
      return (← mk ``Qed.Server.getElem_congr_arr, ← mk ``Qed.Server.srvGetAt_congr_arr)
    let st ← (← base.add (.other `arrCongr1) #[] c1).add (.other `arrCongr2) #[] c2
    return some (← Simp.mkContext { zetaDelta := false, failIfUnchanged := false } #[st] (← getSimpCongrTheorems), ← getCachedSimprocs #[`reduceIte] false)
  catch _ => return none

@[noinline] private def rewriteTargetEqsLinearGoal (g0 : MVarId) : MetaM (Option MVarId) := do
  let eqDecls ← g0.withContext <| collectLCtxDecls (includeLet := false) fun d => do
    unless isSrvEqDecl d do return none
    let some (eqTy, lhs, rhs) := (← instantiateMVars d.type).eq? | return none
    let .fvar fv := lhs.consumeMData | return none
    if rhs.containsFVar fv then return none
    let w ← whnf eqTy
    return some (fv, if w.isAppOfArity ``Array 1 then some (w.getAppArgs[0]!, lhs.consumeMData, rhs) else none, d.fvarId)
  if eqDecls.isEmpty then return some g0
  let (postRwCtx, _) ← mkCachedSimpCtx "postRw" (#[``Array.sumBy_empty, ``Array.sumBy_push] ++ arrayCoreSimpNames ++ valUnwrapSimpNames ++ liftOptSimpNames)
  foldlGoalMeta eqDecls.reverse g0 fun g (fv, arrInfo?, eqFv) => do
    if !(← goalType g).containsFVar fv then return some g
    let (g?, prog1) ← match arrInfo? with
      | some (elemTy, lhs, rhs) =>
          match ← mkArrCongrSimp? g elemTy lhs rhs eqFv with
          | some (ctx, sp) => pure (← simpGoalOnly g ctx sp, true)
          | none => pure (some g, false)
      | none => pure (some g, false)
    let some g := g? | return none
    let (g, prog2) ← if (← goalType g).containsFVar fv then
        match ← rewriteTargetByFVar g eqFv with | some g' => pure (g', true) | none => pure (g, false)
      else pure (g, false)
    if prog1 || prog2 then simpGoalOnly g postRwCtx else return some g

private theorem srv_forall_push {α : Type} {P : α → Prop} {xs : Array α} {v : α}
    (hxs : ∀ x ∈ xs, P x) (hv : P v) : ∀ x ∈ xs.push v, P x := (Array.forall_push (P := P) (xs := xs) (v := v)).2 ⟨hxs, hv⟩

@[noinline] private def peelArrayForallGoal (g0 : MVarId) (allowDeepFallback : Bool := true) : TacticM (List MVarId) := do
  let rec loop : Nat → MVarId → TacticM (List MVarId)
    | 0, g => return [g]
    | fuel + 1, g => do
        let some g ← runGoalPipe g [dsimpTargetOnly, closeIf tryCloseSrvTrivial] | return []
        let some arrExpr := extractForEachColl? (← goalType g) | return [g]
        let lem? := if arrExpr.isAppOfArity ``Array.set 5 then some ``Array.forall_set else if arrExpr.isAppOfArity ``Array.push 3 then some ``srv_forall_push else none
        if let some lem := lem? then if let some [gPrev, gElem] ← tryApplyConst g lem then
          let elemRem ← match ← runGoalPipe gElem [dsimpTargetOnly, rewriteTargetEqsLinearGoal] with
            | none => pure [] | some ge => pure (← finishAtomGoal ge allowDeepFallback).toList
          return (← loop fuel gPrev) ++ elemRem
        if let .fvar fv := arrExpr then
          if let some (d, _) := (← userDecls g).find? fun (d, ty) =>
              !d.userName.hasMacroScopes && match ty.eq? with | some (_, lhs, _) => lhs.consumeMData == .fvar fv | none => false then
            if let some g' ← rewriteTargetByFVar g d.fvarId then return ← loop fuel g'
        if ← g.assumptionCore then return []
        return [g]
  loop 128 g0

@[noinline] private def substMatchEqHypsGoal (g0 : MVarId) : MetaM (MVarId × Bool) := do
  let rec go : Nat → MVarId → Bool → MetaM (MVarId × Bool)
    | 0, g, did => return (g, did)
    | fuel + 1, g, did => do
        let lctx ← g.withContext getLCtx
        let trySide (declFv : FVarId) (varSide otherSide : Expr) (allowNonMacro symm : Bool) : MetaM (Option MVarId) := do
          let .fvar fv := varSide.consumeMData | return none
          unless fv != declFv && !otherSide.containsFVar fv && (((lctx.find? fv).any (·.userName.hasMacroScopes)) || allowNonMacro) do return none
          trySaveOpt <| g.withContext do some <$> (Prod.snd <$> Meta.substCore g declFv (symm := symm))
        match ← findMeta (← userDecls g) fun (d, ty) => do
          let u := d.userName.toString
          if !(u.startsWith "_srvMatchEq" || u.startsWith "_srvSplitH") then return none
          let some (_, lhs, rhs) := ty.eq? | return none
          match ← trySide d.fvarId rhs lhs (u.startsWith "_srvMatchEq") true with
          | some g' => pure (some g')
          | none => trySide d.fvarId lhs rhs false false
        with | some g' => go fuel g' true | none => return (g, did)
  go 16 g0 false

@[noinline] private def closeLeafGoal (g0 : MVarId) (allowDeepFallback : Bool := true) : TacticM (List MVarId) := do
  let simpWNS (g : MVarId) : MetaM (Option MVarId) := do
    if (← goalType g).consumeMData.isAppOf ``Qed.Server.srvWithNewState then simpCached g "withNewState" #[``Qed.Server.srvWithNewState_apply] else pure (some g)
  let some g ← runGoalPipe g0 [
    simpWNS, closeIf tryCloseSrvTrivial, dsimpTargetOnly, closeIf tryCloseSrvTrivial,
    liftStep fun g => do Prod.fst <$> splitAndHypsGoal (← tryGoalM g unfoldSrvHelpersGoal), (tryGoalOptM · simpHypsEachGoal)] | return []
  let (g, didSubst) ← substMatchEqHypsGoal g
  let some g ← runGoalPipe g [simpWNS, dsimpTargetOnly, dsimpCodecGoal, closeIf tryCloseSrvTrivial] | return []
  let (g, didSplit2) ← splitAndHypsGoal g
  let g ← if !didSubst && !didSplit2 then pure g else do
    let some g' ← tryGoalOptM g simpHypsEachGoal | return []
    Prod.fst <$> substMatchEqHypsGoal (← splitAndHypsGoal g').1
  flatMapGoalsTactic (fun cg => do
    if ← tryCloseSrvTrivial cg then return []
    flatMapGoalsTactic (fun pg => do
      if ← tryCloseSrvTrivial pg then return []
      match ← rewriteTargetEqsLinearGoal pg with
      | none => return []
      | some rg => return (← finishAtomGoal rg allowDeepFallback).toList) (← peelArrayForallGoal cg allowDeepFallback)) (← splitGoalAnds g)

private def exprHasSplittable (e : Expr) : Bool := hasAnyConst e fun c => c == ``ite || c == ``dite || c.toString.contains ".match_"

private def splitEqHypGoal (g0 : MVarId) : MetaM (Option (List MVarId)) := do
  let (gCur, _, eqFVars) ← foldlMeta (← userDecls g0) (g0, (← g0.withContext getLCtx).size, (#[] : Array FVarId)) fun (gCur, idx, eqFVars) (d, ty) => do
    if ty.isEq && exprHasSplittable ty then
      let (g', nxt) ← maybeRenameMacro gCur d "_srvMatchEq" idx
      return (g', nxt, eqFVars.push d.fvarId)
    else return (gCur, idx, eqFVars)
  findMeta eqFVars (trySplitLocalDecl gCur)

private def goalHasSplittableHyp (g : MVarId) : MetaM Bool := do
  return (← userDecls g).any fun (_, ty) => hasConst ty ``Qed.Server.srvLetEq || (ty.isEq && exprHasSplittable ty)

@[noinline] private def proveStepSingleGoal (g0 : MVarId) (allStepCtx : Simp.Context) : TacticM (List MVarId) := do
  let some g2 ← simpGoalAllHyps (← g0.intros).2 allStepCtx | return []
  let rec stepTargetLoop : Nat → List MVarId → TacticM (List MVarId)
    | 0, gs => return gs | _, [] => return []
    | fuel + 1, g :: rest => do
        if ← tryCloseSrvTrivial g then return ← stepTargetLoop fuel rest
        let (gLet, didLet) ← elimAllSrvLetEqTarget g
        if didLet then return ← stepTargetLoop fuel ((← simpGoalOnly gLet allStepCtx).toList ++ rest)
        match ← trySplitTarget g with
        | some sgs => return ← stepTargetLoop fuel ((← filterMapGoalsMeta (simpGoalOnly · allStepCtx) sgs) ++ rest)
        | none =>
            if ← goalHasSplittableHyp g then
              let s ← saveState
              if (← closeLeafGoal g false).isEmpty then return ← stepTargetLoop fuel rest
              restoreState s
              if let some gHypLet ← elimSrvLetEqGoal g true then return ← stepTargetLoop fuel ((← simpGoalOnly gHypLet allStepCtx).toList ++ rest)
              if let some eqSgs ← splitEqHypGoal g then return ← stepTargetLoop fuel ((← filterMapGoalsMeta (simpGoalAllHyps · allStepCtx) eqSgs) ++ rest)
            return (← closeLeafGoal g true) ++ (← stepTargetLoop fuel rest)
  stepTargetLoop 256 [g2]

private def runProveStepOnGoals (gs : List MVarId) (userNames : Array Name) (fnStr lbl : String) (throwOnRem : Bool := true) : TacticM Unit := do
  let allStepCtx ← mkDynamicSimpCtx userNames (some ("stepFixed", unwrapOkSimpNames ++ stepCombSimpNames ++ stepLetEqSimpNames ++ ensPostSimpNames ++ valUnwrapSimpNames ++ liftOptSimpNames))
  let rem ← flatMapGoalsTactic (proveStepSingleGoal · allStepCtx) gs
  setGoals rem
  if throwOnRem && !rem.isEmpty then
    let (hdr, hint) : MessageData × String :=
      if lbl.startsWith "ensures:" then let p := (lbl.drop 8).toString.trimAscii.toString; (m!"Server postcondition `ensures {p}` failed in `{fnStr}`:", s!"Ensure every successful return path establishes `{p}`.")
      else if lbl.startsWith "init:" then let i := (lbl.drop 5).toString.trimAscii.toString; (m!"Server invariant `{i}` failed on initial state:", s!"Update the initial `state` values so they satisfy `{i}`.")
      else if lbl.startsWith "mutating:" then (m!"Server invariant `{(lbl.drop 9).toString.trimAscii.toString}` failed in `{fnStr}`:", "Add a matching `requires` clause or guard mutations of that field with `if ...:`.")
      else (m!"Server invariant `{lbl}` failed in `{fnStr}`:", "Guard state mutations with `if ...:` or `requires ...` so this invariant holds across every branch.")
    Qed.Diag.throwUnsolvedGoals hdr m!"\n\nHint: {hint}" (maxShown? := some 1) (moreLabel := "obligation(s)") (goals? := some rem)

elab_rules : tactic
  | `(tactic| qedSrvProveStep [$[$unfoldIds:ident],*] $fnLabel:str $invLabel:str) => do
      runProveStepOnGoals (← getGoals) (← resolveIdentsMeta unfoldIds) fnLabel.getString invLabel.getString
  | `(tactic| qedSrvPrepStep [$[$unfoldIds:ident],*]) => do
      runProveStepOnGoals (← getGoals) (← resolveIdentsMeta unfoldIds) "" "" (throwOnRem := false)

/-! ## Unified AST-Directed Async Prover Directly over `ProgSpec` -/

private def dropTrivialGoals (gs : List MVarId) : MetaM (List MVarId) :=
  filterUnsolvedM (fun g => do
    let s ← saveState; let (_, g') ← g.intros
    if (← goalType g').isConstOf ``True then do g'.assign (mkConst ``True.intro); return true
    restoreState s; return false) gs

private def normAsyncContGoal (g0 : MVarId) (dCtx sCtx : Simp.Context) : MetaM (Option MVarId) :=
  runGoalPipe g0 [(tryGoalOptM · (simpGoalOnly · dCtx #[] #[] true true)), (tryGoalOptM · (simpGoalOnly · sCtx))]

private def tryCloseConstMutInv (g0 : MVarId) : TacticM (Option MVarId) := do
  let (_, g1) ← g0.intros; let tgtC := (← goalType g1).consumeMData
  if tgtC.isAppOfArity ``Qed.Server.ProgPreservesStepRel 5 then
    if let .lam _ _ (.lam _ _ body _) _ := tgtC.getAppArgs[3]!.consumeMData then
      if body.isAppOfArity ``Or 2 && !body.getAppArgs[1]!.hasLooseBVars then
        return ← tryRestoreM (some g1) Option.isNone do
          let [gH] ← g1.applyConst ``Qed.Server.progPreservesStepRel_of_const | return some g1
          let [gR] ← (← gH.introN 2).2.applyConst ``Or.inr | return some g1
          return if (← closeLeafGoal gR).isEmpty then none else some g1
  return some g1

private def effWrapperUnfoldNames : Array Name :=
  splitNms `Qed.Server "newId hashBearerToken mintBearerToken flushWsEmits" ++
  splitNms `Qed.Time "nowMs nowSec sleepMs sleepSec" ++
  splitNms `Qed.Http "requestOidcRaw getOidc getOidcString getOidcJson postOidcJson" ++
  splitNms `Qed.Proc "exec execOk" ++
  splitNms `Qed.Fs "readBytes readText writeBytes writeText mkdirAll removeAll pathExists mktempDir" ++
  splitNms `Qed.Server.Db "dbRunRows dbRunOneRow dbSelectProj dbFindOneProj dbCount dbSumNat dbSumInt dbAggOpt dbDelete dbInsert dbInsertOrIgnore dbUpsert dbJoinSelect dbRun pgSchemasQuery pgTablesQuery pgColumnsQuery pgIndexesQuery pgKeyColumnsQuery pgTableStatsQuery" ++
  splitNms `Qed.Server.Db.PgHandle "runReadOnly queryReadOnly listSchemas listTables listColumns listIndexes listKeyColumns listTableStats countRows countRowsInSchema selectRows selectCols selectSchema"

private def effHypContraSimpNames : Array Name :=
  splitNms .anonymous "Bool.not_eq_true' Bool.not_eq_false' not_true_eq_false not_false_eq_true decide_eq_true_eq decide_eq_false_iff_not beq_iff_eq bne_iff_ne Qed.Lang.QedVal.val_id Qed.qedIterable_toList_array Qed.qedIterable_toList_list Qed.qedIterable_toList_range Qed.Lang.QedSeqLit.ofList Array.toList_empty List.mem_nil_iff List.not_mem_nil"

private def effSideSimpNames : Array Name :=
  splitNms `Qed.Server "ServerEffect.isHttp ServerEffect.isDecrypt ServerEffect.isCrypto ServerEffect.isDbWrite Db.SqlQuery.isWrite Db.dbExecEff" ++ boolSimpNames ++ boolConstSimpNames

private def tryCloseHypContradiction (contraCtx : Simp.Context) (g : MVarId) : MetaM Bool := do
  if ← tryRestoreMeta false id (g.contradictionCore {}) then return true
  tryRestoreMeta false id do
    match ← trySimpAll g contraCtx with
    | none => return true
    | some g' => if ← tryRestoreMeta false id (g'.contradictionCore {}) then return true else tryDirectOmega g'

private def closeEffLeaf (effCtx : Simp.Context) (g : MVarId) : MetaM Bool := do
  let (_, g1) ← g.intros
  if ← tryCloseBasic g1 then return true
  match ← trySimpAll g1 effCtx with | none => return true | some g2 => tryCloseBasic g2

private def tryApply1 (g : MVarId) (c : Name) (k : MVarId → MetaM Bool) : MetaM Bool :=
  tryRestoreMeta false id do match ← tryApplyConst g c with | some [g'] => k g' | _ => pure false

@[noinline] private def tryCloseEffSideGoal (effCtx : Simp.Context) (g0 : MVarId) : MetaM Bool :=
  tryRestoreMeta false id do
    let (_, g) ← g0.intros
    if ← tryApply1 g ``Or.inl tryReflGoal then return true
    if ← tryApply1 g ``Or.inr fun gR => do
      if ← tryApply1 gR ``Or.inl tryReflGoal then return true
      if ← tryApply1 gR ``Or.inr (closeEffLeaf effCtx) then return true
      let some [gA, gB] ← tryApplyConst gR ``And.intro | return false
      if ← closeEffLeaf effCtx gA then closeEffLeaf effCtx gB else return false
    then return true
    let some g2 ← simpGoalAllHyps g effCtx | return true
    match ← trySplitTarget g2 with | some sgs => closeAllGoals (closeEffLeaf effCtx) sgs | none => closeEffLeaf effCtx g2

private def commonProgHeadSet : NameSet := mkNameSet (splitNms `Qed.Server "ThreadProg.pure ThreadProg.bind srvFinishM srvSeqM dbRunTx srvForFoldM srvForRangeM" ++ #[``Pure.pure, ``Bind.bind, ``ite, ``dite])
private def effSkipExtraSet : NameSet := mkNameSet (splitNms `Qed.Server "MonadServer.exec Db.dbRunChecked MonadAtomic.runAtomic MonadAtomic.runAtomicRead")

private def isEffSkipUnfold (env : Environment) (c : Name) : Bool :=
  commonProgHeadSet.contains c || effSkipExtraSet.contains c ||
  (c == `Qed.Server.execExternalRaw && env.contains `Qed.Server.progEffSpec_execExternalRaw_bind) ||
  (c == `Qed.Server.Webhook.postRaw && env.contains `Qed.Server.Webhook.progEffSpec_postRaw_bind)

private def isNoAtomicStructuralHead (p : Expr) : Bool :=
  match p.getAppFn.constName? with
  | some c => commonProgHeadSet.contains c || c == ``Qed.Server.srvLetEq || c.toString.contains ".match_"
  | none => false

private structure StepCtx where
  env : Environment
  mode : ProgStepMode
  dCtx : Simp.Context
  sCtx : Simp.Context
  contraCtx? : Option Simp.Context
  effCtx? : Option Simp.Context

private def StepCtx.normCont (c : StepCtx) (g : MVarId) (n : Nat) : MetaM (List MVarId) := do
  let g1 ← if n == 0 then pure g else Prod.snd <$> g.introN n
  if (← goalType g1).isConstOf ``True then g1.assign (mkConst ``True.intro); return []
  return (← normAsyncContGoal g1 c.dCtx c.sCtx).toList

private def StepCtx.normSplits (c : StepCtx) (sgs : List MVarId) : MetaM (List MVarId) :=
  filterMapGoalsMeta (fun sg => do normAsyncContGoal (← sg.intros).2 c.dCtx c.sCtx) sgs

private def StepCtx.filterEffSides (c : StepCtx) (sgs : List MVarId) : MetaM (List MVarId) :=
  match c.effCtx? with | none => dropTrivialGoals sgs | some eCtx => filterUnsolvedM (tryCloseEffSideGoal eCtx) sgs

private def StepCtx.tryUnfoldHead (c : StepCtx) (g : MVarId) (tgtC expr : Expr) : MetaM (Option MVarId) := do
  let some fnNm := expr.getAppFn.constName? | return none
  if isEffSkipUnfold c.env fnNm then return none
  let some (.defnInfo _) := c.env.find? fnNm | return none
  let some g' ← tryGoalOptM g (simpGoalOnly · (← mkDynamicSimpCtx #[fnNm])) | return none
  let some g'' ← normAsyncContGoal g' c.dCtx c.sCtx | return none
  return if (← goalType g'') != tgtC then some g'' else none

private inductive SubAct where | eff | dropDone | dropLoop | norm (n : Nat) (contra : Bool := false)
private def tagGoals (b : Bool) (gs : List MVarId) : List (MVarId × Bool) := gs.map (·, b)
private def tryCloseConst (g : MVarId) (lem : Name) : MetaM Bool := do return (← tryApplyConst g lem) == some []

@[noinline] private def applySubActs (c : StepCtx) (g : MVarId) (lem : Name) (acts : List SubAct) :
    MetaM (Option (List MVarId × List (MVarId × Bool))) := do
  if !c.env.contains lem then return none
  let some sgs ← tryApplyConst g lem | return none
  if sgs.length != acts.length then return none
  let rec go : List MVarId → List SubAct → List MVarId → List (MVarId × Bool) → MetaM (List MVarId × List (MVarId × Bool))
    | sg :: sgs, act :: acts, done, next => do
        match act with
        | .eff => go sgs acts (done ++ (← c.filterEffSides [sg])) next
        | .dropDone => go sgs acts (done ++ (← dropTrivialGoals [sg])) next
        | .dropLoop => go sgs acts done (next ++ tagGoals false (← dropTrivialGoals [sg]))
        | .norm n b => go sgs acts done (next ++ tagGoals b (← c.normCont sg n))
    | _, _, done, next => pure (done, next)
  some <$> go sgs acts [] []

@[noinline] private def applyFirstActs (c : StepCtx) (g : MVarId) : List (Name × List SubAct) →
    MetaM (Option (List MVarId × List (MVarId × Bool)))
  | [] => pure none
  | (lem, acts) :: rest => do
      match ← applySubActs c g lem acts with | some res => pure (some res) | none => applyFirstActs c g rest

private structure RuleRow where
  isBind : Bool
  effOnly : Bool := false
  presOnly? : Option Bool := none
  cands : List (Name × List SubAct)

private def mkNameMap {α : Type} (entries : Array (Name × α)) : NameMap α := entries.foldl (init := {}) fun m (k, v) => m.insert k v
private def srvRow (isBind : Bool) (cands : List (String × List SubAct)) (effOnly := false) (presOnly? : Option Bool := none) : RuleRow :=
  { isBind, effOnly, presOnly?, cands := cands.map fun (s, a) => (srvNm s, a) }
private def effRuleRows (d b : String) : List RuleRow := [srvRow false [(d, [.eff, .dropDone])] true, srvRow true [(b, [.eff, .norm 1])] true]
private def atomicBindRows (v n : String) : List RuleRow := [srvRow true [(v, [.norm 1, .dropLoop])] false (some true), srvRow true [(n, [.norm 2, .dropLoop])] false (some false)]

private def structuralRulesMap : NameMap (List RuleRow) := mkNameMap #[
  (srvNm "srvFinishM", [srvRow false [("progEffSpec_srvFinishM_triv", [.norm 0]), ("progEffSpec_srvFinishM", [.norm 0])], srvRow true [("progEffSpec_srvFinishM_bind", [.norm 0])]]),
  (srvNm "srvSeqM", [srvRow false [("progEffSpec_srvSeqM_triv", [.norm 0, .norm 0]), ("progEffSpec_srvSeqM", [.norm 0, .norm 0])], srvRow true [("progEffSpec_srvSeqM_bind", [.norm 0, .norm 0])]]),
  (srvNm "dbRunTx", [srvRow false [("progEffSpec_dbRunTx", [.eff, .eff, .eff, .norm 1, .norm 1])], srvRow true [("progEffSpec_dbRunTx_bind", [.eff, .eff, .eff, .norm 1, .norm 0, .norm 1])]]),
  (srvNm "srvForFoldM", [srvRow false [("progEffSpec_srvForFoldM", [.norm 1, .norm 3 true])], srvRow true [("progEffSpec_srvForFoldM_bind", [.norm 1, .norm 3 true])]]),
  (srvNm "srvForRangeM", [srvRow false [("progEffSpec_srvForRangeM", [.norm 1, .norm 4 true])], srvRow true [("progEffSpec_srvForRangeM_bind", [.norm 1, .norm 4 true])]]),
  (srvNm "MonadAtomic.runAtomic", atomicBindRows "ProgEffSpec.runAtomic_bind_val" "ProgEffSpec.runAtomic_bind"),
  (srvNm "MonadAtomic.runAtomicRead", atomicBindRows "ProgEffSpec.runAtomicRead_bind_val" "ProgEffSpec.runAtomicRead_bind"),
  (srvNm "MonadServer.exec", effRuleRows "ProgEffSpec.exec" "ProgEffSpec.exec_bind"),
  (srvNm "execExternalRaw", effRuleRows "progEffSpec_execExternalRaw" "progEffSpec_execExternalRaw_bind"),
  (srvNm "Webhook.postRaw", effRuleRows "Webhook.progEffSpec_postRaw" "Webhook.progEffSpec_postRaw_bind"),
  (srvNm "Db.dbRunChecked", [srvRow false [("Db.progEffSpec_dbRunChecked", [.eff, .eff, .eff, .dropDone])] true, srvRow true [("Db.progEffSpec_dbRunChecked_bind", [.eff, .eff, .eff, .norm 2])] true])]

private def structuralRule? (isEff isPreserves isBind : Bool) (head : Name) : List (Name × List SubAct) :=
  match structuralRulesMap.get? head with
  | none => []
  | some rows => match rows.find? fun r => r.isBind == isBind && (!r.effOnly || isEff) && (r.presOnly?.elim true (· == isPreserves)) with | some r => r.cands | none => []

private def noAtomicRulesMap : NameMap (Name × List SubAct) := mkNameMap #[
  (srvNm "ThreadProg.pure", (srvNm "NoAtomic.pure", [])), (``Pure.pure, (srvNm "SafeIO.noAtomic", [])),
  (srvNm "srvFinishM", (srvNm "noAtomic_srvFinishM", [.norm 0])), (srvNm "srvSeqM", (srvNm "noAtomic_srvSeqM", [.norm 0, .norm 0])),
  (srvNm "dbRunTx", (srvNm "noAtomic_dbRunTx", [.norm 1])), (srvNm "srvForFoldM", (srvNm "noAtomic_srvForFoldM", [.norm 2])),
  (srvNm "srvForRangeM", (srvNm "noAtomic_srvForRangeM", [.norm 2]))]

private def leafRuleMap : NameMap Name := mkNameMap #[
  (srvNm "ThreadProg.pure", srvNm "ProgEffSpec.pure"), (``Pure.pure, srvNm "ProgEffSpec.pure_class"),
  (srvNm "MonadAtomic.runAtomic", srvNm "ProgEffSpec.runAtomic"), (srvNm "MonadAtomic.runAtomicRead", srvNm "ProgEffSpec.runAtomicRead")]

@[noinline] private def stepProgOne (c : StepCtx) (g : MVarId) (tgtC prog : Expr) : MetaM (List MVarId × List (MVarId × Bool)) := do
  let head? := prog.getAppFn.constName?
  if head? == some ``Qed.Server.srvLetEq then
    if let some gLet ← elimSrvLetEqGoal g false then return ([], tagGoals false (← c.normCont gLet 0))
  let (isNoAtomic, isEff, isPreserves) := (c.mode == .noAtomic, c.mode == .effSpec, c.mode == .preserves)
  if let some head := head? then
    if isNoAtomic then
      if let some (lem, acts) := noAtomicRulesMap.get? head then if let some res ← applySubActs c g lem acts then return res
    else
      if let some lem := leafRuleMap.get? head then
        if let some sgs ← tryApplyConst g lem then return ([], tagGoals false (← c.normSplits (← dropTrivialGoals sgs)))
      if let some res ← applyFirstActs c g (structuralRule? isEff isPreserves false head) then return res
    if head == ``Bind.bind || head == ``Qed.Server.ThreadProg.bind then
      let pArg := (if head == ``Bind.bind then prog.getAppArgs[4]! else prog.getAppArgs[3]!).consumeMData
      if isNoAtomic then
        if let some [gLeft, gRight] ← tryApplyConst g ``Qed.Server.noAtomic_bind then
          let leftRem ← if !isNoAtomicStructuralHead pArg then
              if ← tryCloseConst gLeft ``Qed.Server.SafeIO.noAtomic then pure [] else pure [gLeft]
            else pure [gLeft]
          return ([], tagGoals false (leftRem ++ (← c.normCont gRight 1)))
      else
        if let some pHead := pArg.getAppFn.constName? then
          if let some res ← applyFirstActs c g (structuralRule? isEff isPreserves true pHead) then return res
        if isEff then
          if exprHasSplittable pArg then if let some sgs ← trySplitTarget g then return ([], tagGoals true (← c.normSplits sgs))
          if let some g'' ← c.tryUnfoldHead g tgtC pArg then return ([], [(g'', false)])
        else
          if c.mode == .ensures then
            if let some res ← applySubActs c g ``Qed.Server.safeIOEnsures_bind [.norm 2] then return res
            if exprHasSplittable pArg then if let some sgs ← trySplitTarget g then return ([], tagGoals true (← c.normSplits sgs))
          if let some res ← applySubActs c g ``Qed.Server.ProgSpec.safeIO_bind [.norm 1] then return res
  if isNoAtomic then
    if !isNoAtomicStructuralHead prog then if ← tryCloseConst g ``Qed.Server.SafeIO.noAtomic then return ([], [])
  else if c.mode == .ensures then
    if let some [gImp] ← tryApplyConst g ``Qed.Server.safeIOEnsures_final then return ([gImp], [])
  else if isPreserves && !hasAnyConst prog fun cn => cn == ``Qed.Server.MonadAtomic.runAtomic || cn == ``Qed.Server.MonadAtomic.runAtomicRead then
    if ← tryCloseConst g ``Qed.Server.ProgSpec.of_safeIO then return ([], [])
  else if isEff then
    if let some g'' ← c.tryUnfoldHead g tgtC prog then return ([], [(g'', false)])
  match ← trySplitTarget g with
  | some sgs => return ([], tagGoals (!isNoAtomic) (← c.normSplits sgs))
  | none =>
      let fbLem? := if isNoAtomic then some ``Qed.Server.SafeIO.noAtomic else if isPreserves then some ``Qed.Server.ProgSpec.of_safeIO else none
      if let some fbLem := fbLem? then if ← tryCloseConst g fbLem then return ([], [])
      return ([g], [])

@[noinline] private def stepProgLoop (mode : ProgStepMode) (dCtx sCtx : Simp.Context) (gInit : MVarId) : MetaM (List MVarId) := do
  let env ← getEnv
  let (contraCtx?, effCtx?) ← if mode == .effSpec then
      pure (some (← mkCachedSimpCtx "effHypContra" effHypContraSimpNames {}).1, some (← mkCachedSimpCtx "effSide" effSideSimpNames {}).1)
    else pure (none, none)
  let c : StepCtx := { env, mode, dCtx, sCtx, contraCtx?, effCtx? }
  let extractProg? (e : Expr) : Option Expr := match e.getAppFn.constName?, e.getAppNumArgs with
    | some ``Qed.Server.ProgEffSpec, 8 => some e.getAppArgs[7]!
    | some ``Qed.Server.ProgSpec, 7 => some e.getAppArgs[6]!
    | some ``Qed.Server.ProgPreservesStepRel, 5 | some ``Qed.Server.ProgEnsures, 5 => some e.getAppArgs[4]!
    | some ``Qed.Server.ProgPreservesInv, 4 => some e.getAppArgs[3]!
    | some ``Qed.Server.NoAtomic, 3 => some e.getAppArgs[2]! | _, _ => none
  let rec loop : Nat → List (MVarId × Bool) → MetaM (List MVarId)
    | 0, gs => return gs.map Prod.fst | _, [] => return []
    | fuel + 1, (g, checkContra) :: rest => do
        if checkContra then if let some cCtx := c.contraCtx? then if ← tryCloseHypContradiction cCtx g then return ← loop fuel rest
        let tgtC := (← goalType g).consumeMData
        let some progRaw := extractProg? tgtC | return g :: (← loop fuel rest)
        let (done, next) ← stepProgOne c g tgtC progRaw.consumeMData
        return done ++ (← loop fuel (next ++ rest))
  loop 256 [(gInit, true)]

private def initAsyncSimpAndNorm (g : MVarId) (unfoldConsts : Array Name) : TacticM (Simp.Context × Simp.Context × Option MVarId) := do
  let (dCtx, _) ← mkCachedSimpCtx "asyncDsimp" #[``Qed.Server.SrvUnwrap.unwrap, ``Qed.Server.SrvErr.ofApi, ``Qed.Server.SrvUnwrapOpt.unwrapOpt] { zetaDelta := false } #[] true
  let (sCtx, _) ← mkCachedSimpCtx "asyncNorm" (stepCombSimpNames ++ stepLetEqSimpNames ++ ensPostSimpNames ++ #[``Qed.Server.threadProg_pure_bind, ``Qed.Server.threadProg_pure_bind', ``Qed.Server.threadProg_bind_pure_left, ``Qed.Server.threadProg_bind_pure_left', ``Qed.Server.threadProg_bind_assoc, ``Qed.Server.threadProg_bind_assoc_inner, ``Qed.Server.threadProg_bind_assoc'])
  let gInit? ← runGoalPipe (← g.intros).2 [fun g => do tryGoalOptM g (simpGoalOnly · (← mkDynamicSimpCtx unfoldConsts)), (normAsyncContGoal · dCtx sCtx)]
  return (dCtx, sCtx, gInit?)

@[noinline] private def elabProgProve (mode : ProgStepMode) (handlerId : Ident) (invUnfoldIds : Array Ident)
    (fnLabel invLabel : String) (throwOnRem : Bool := true) : TacticM Unit := do
  let g0 ← getMainGoal
  let g1 ← if mode == .preserves then
      let some g' ← tryCloseConstMutInv g0 | replaceMainGoal []; return
      pure g'
    else pure g0
  let handlerConst ← resolveIdentMeta handlerId; let userNames ← resolveIdentsMeta invUnfoldIds
  let (helperConsts, invConsts) := userNames.partition fun n => n.getString!.startsWith "_fn_"
  let extraUnfolds ← if mode == .effSpec then do let env ← getEnv; pure (effWrapperUnfoldNames.filter env.contains) else pure #[]
  let (dCtx, sCtx, some gInit) ← initAsyncSimpAndNorm g1 (#[handlerConst] ++ helperConsts ++ extraUnfolds) | replaceMainGoal []; return
  let rem ← stepProgLoop mode dCtx sCtx gInit
  if mode == .noAtomic then
    setGoals rem
    unless rem.isEmpty do Qed.Diag.throwUnsolvedGoals m!"Server helper `{handlerConst}` could not be proved `SafeIO` (no atomic state mutation):" m!"" (maxShown? := some 1) (goals? := some rem)
  else runProveStepOnGoals rem invConsts fnLabel invLabel throwOnRem

elab_rules : tactic
  | `(tactic| qedSrvProveAsync $handlerId:ident [$[$invUnfoldIds:ident],*] $fnLabel:str $invLabel:str) => elabProgProve .preserves handlerId invUnfoldIds fnLabel.getString invLabel.getString
  | `(tactic| qedSrvProveAsyncEnsures $handlerId:ident [$[$invUnfoldIds:ident],*] $fnLabel:str $invLabel:str) => elabProgProve .ensures handlerId invUnfoldIds fnLabel.getString invLabel.getString
  | `(tactic| qedSrvPrepAsyncEnsures $handlerId:ident [$[$invUnfoldIds:ident],*]) => elabProgProve .ensures handlerId invUnfoldIds "" "" (throwOnRem := false)
  | `(tactic| qedSrvProveEffSpec $handlerId:ident [$[$invUnfoldIds:ident],*] $fnLabel:str $invLabel:str) => elabProgProve .effSpec handlerId invUnfoldIds fnLabel.getString invLabel.getString
  | `(tactic| qedSrvPrepEffSpec $handlerId:ident [$[$invUnfoldIds:ident],*]) => elabProgProve .effSpec handlerId invUnfoldIds "" "" (throwOnRem := false)
  | `(tactic| qedSrvProveSafeIO $fnId:ident) => elabProgProve .noAtomic fnId #[] "" ""

/-! ## Client RPC Precondition Prover (`qedProveRpcReq`) -/

@[noinline] private def elabProveRpcReq : TacticM Unit := do
  let some g ← runGoalPipe (← getMainGoal) [
    closeIf tryCloseSrvBasic, liftStep fun g => try Prod.fst <$> splitAndHypsGoal g catch _ => pure g,
    liftStep (tryGoalM · unfoldSrvHelpersGoal), fun g => do simpGoalAllHyps g (← mkEmptyDsimpCtx) #[] true] | replaceMainGoal []; return
  let (g, _) ← assertFacts g "_reqFact" (← g.withContext do collectProofFacts #[← instantiateMVars (← g.getType)])
  let some g ← runGoalPipe g [
    liftStep (tryGoalM · unfoldSrvHelpersGoal),
    (simpCached · "arrayAndBool" arrayAndBoolSimpNames { zetaDelta := true } (allHyps := true)),
    (simpCached · "rpcReq" (#[``Option.isSome_iff_ne_none, ``ne_eq, `Qed.Cached.all, `Qed.Resource.all] ++ boolSimpNames ++ valUnwrapSimpNames ++ optCodecSimpNames) { zetaDelta := true, zetaHave := true } (allHyps := true)),
    dsimpCodecGoal] | replaceMainGoal []; return
  let rem ← flatMapGoalsTactic (fun cg => do
    let (cg, _) ← try splitAndHypsGoal cg catch _ => pure (cg, false)
    if ← tryCloseSrvBasic cg then return []
    if ← closeWithFallback cg { skipTarget := hasUnsteppedCtrlFlow, simpAllCfg := { zetaDelta := true, zetaHave := true }, deepExtraSimpAll := #[``Qed.Server.srvLetEq] } then return []
    return [cg]) (← splitGoalAnds g)
  setGoals rem
  unless rem.isEmpty do
    Qed.Diag.throwUnsolvedGoals m!"Server `requires` precondition could not be proved:"
      m!"\n\nHint: Guard this RPC call with `if ...:` so the precondition holds." (goals? := some (rem.take 1))

elab_rules : tactic
  | `(tactic| qedProveRpcReq) => elabProveRpcReq

end Qed.Server
