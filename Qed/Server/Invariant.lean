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

private def strLenSP : Array Name := #[``qedReduceStrLen]
private def valUnwrapSimpNames : Array Name := #[``Qed.Server.srvGetAt_eq, ``Qed.Server.SrvIdx.toNat_nat, ``Qed.Server.SrvIdx.toNat_fin] ++ valUnwrapBaseNames
private def liftOptSimpNames : Array Name := #[``Qed.Server.SrvLiftOpt.liftOpt_opt, ``Qed.Server.SrvLiftOpt.liftOpt_val]
private def arrayCoreSimpNames : Array Name := #[``Array.size_set, ``Array.size_push, ``Array.getElem_set_self, ``Qed.Lang.QedSeqLit.ofList_array, ``Qed.Lang.QedSeqLit.ofList_list] ++ dictSimpNames
private def unwrapOkSimpNames : Array Name := #[``Qed.Server.srvUnwrap_srvFailure_ok_iff, ``Qed.Server.srvUnwrap_str_ok_iff, ``Qed.Server.srvUnwrap_opt_ok_iff]
private def diteFalseSimpNames : Array Name := #[``Qed.Server.srvDiteFalse_eq_true, ``Qed.Server.srvDiteFalse_eq_false]
private def arrayAndBoolSimpNames : Array Name := #[``id_eq, ``ne_eq, ``Array.size_modify] ++ diteFalseSimpNames ++ valUnwrapSimpNames ++ arrayCoreSimpNames ++ boolSimpNames
private def stepCombSimpNames : Array Name := #[
  ``Qed.Server.srvSeq_none, ``Qed.Server.srvSeq_some, ``Qed.Server.srvEmitSeq_none, ``Qed.Server.srvEmitSeq_some,
  ``Qed.Server.srvFinish_ok, ``Qed.Server.srvFinish_err, ``Qed.Server.srvFinish_none,
  ``Qed.Server.srvFinishEmit_ok, ``Qed.Server.srvFinishEmit_err, ``Qed.Server.srvFinishEmit_none,
  ``Qed.Server.srvAtomicCommit_none, ``Qed.Server.srvAtomicCommit_ok, ``Qed.Server.srvAtomicCommit_err,
  ``Qed.Server.srvAtomicCommitEmit_none, ``Qed.Server.srvAtomicCommitEmit_ok, ``Qed.Server.srvAtomicCommitEmit_err]
private def stepLetEqSimpNames : Array Name := #[
  ``Qed.Server.srvSeq_srvLetEq, ``Qed.Server.srvEmitSeq_srvLetEq, ``Qed.Server.srvFinish_srvLetEq, ``Qed.Server.srvFinishEmit_srvLetEq,
  ``Qed.Server.srvAtomicCommit_srvLetEq, ``Qed.Server.srvAtomicCommitEmit_srvLetEq, ``Qed.Server.srvWithNewState_srvLetEq,
  ``Qed.Server.prod_fst_srvLetEq, ``Qed.Server.prod_snd_srvLetEq]
private def ensPostSimpNames : Array Name := #[
  ``Qed.Server.srvEnsPost_ok, ``Qed.Server.srvEnsPost_err, ``Qed.Server.srvEnsPost_srvLetEq,
  ``Qed.Server.srvEnsPostOpt_some, ``Qed.Server.srvEnsPostOpt_none, ``Qed.Server.srvEnsPostOpt_err,
  ``Qed.Server.srvEnsPostOpt_srvLetEq, ``Qed.Server.srvEnsPostOpt_ok_iff,
  ``Qed.Server.srvEnsErrPost_ok, ``Qed.Server.srvEnsErrPost_err, ``Qed.Server.srvEnsErrPost_srvLetEq,
  ``Qed.Server.srvEnsFails_ok, ``Qed.Server.srvEnsFails_err, ``Qed.Server.srvEnsFails_srvLetEq,
  ``Qed.Server.srvEnsFailsCode_ok, ``Qed.Server.srvEnsFailsCode_err, ``Qed.Server.srvEnsFailsCode_srvLetEq]

private def isSrvEqDecl (decl : LocalDecl) : Bool := !decl.userName.hasMacroScopes && let u := decl.userName.toString; u.startsWith "_srvEq" || u.startsWith "_hLet"
def collectProofFacts (extraExprs : Array Expr) : TermElabM (Array Expr) :=
  liftMetaM <| collectFacts { scanLCtx := true, scanLCtxValues := true, includeMacroPropHyps := true, includeFin := true, skipDecl := fun d _ => isSrvEqDecl d } extraExprs

private def hasUnsteppedCtrlFlow (e : Expr) : Bool :=
  let hasUnstepped :=
    e.getUsedConstants.any fun c =>
      c == ``Qed.Server.srvLetEq || c == ``Qed.Server.srvFinish || c == ``Qed.Server.srvFinishEmit || c == ``Qed.Server.srvSeq ||
      c == ``Qed.Server.srvEmitSeq || c == ``Qed.Server.srvAtomicCommit || c == ``Qed.Server.srvAtomicCommitEmit ||
      c == ``Qed.Server.srvEnsPost || c == ``Qed.Server.srvEnsPostOpt || c == ``Qed.Server.srvEnsErrPost ||
      c == ``Qed.Server.srvEnsFails || c == ``Qed.Server.srvEnsFailsCode || c == ``ite || c == ``dite
  hasUnstepped

private def tryCloseSrvTrivial (g : MVarId) : MetaM Bool := tryCloseTrivial g hasUnsteppedCtrlFlow
private def tryCloseSrvBasic (g : MVarId) : MetaM Bool := tryCloseBasic g hasUnsteppedCtrlFlow
private def isUserDecl (d : LocalDecl) : Bool := !d.isImplementationDetail && !d.isLet
private def isPropSafe (ty : Expr) : MetaM Bool := try isProp ty catch _ => pure false
private def goalType (g : MVarId) : MetaM Expr := g.withContext do instantiateMVars (← g.getType)
private def dsimpTargetOnly (g : MVarId) : MetaM (Option MVarId) := do simpGoalOnly g (← mkEmptyDsimpCtx) #[] #[] true true
private def maybeEnsureType (expectedType? : Option Expr) (e : Expr) : TermElabM Expr := expectedType?.elim (pure e) (ensureHasType · e)
private def closeIf (p : MVarId → MetaM Bool) (g : MVarId) : MetaM (Option MVarId) := do if ← p g then return none else return some g
private def liftStep (f : MVarId → MetaM MVarId) (g : MVarId) : MetaM (Option MVarId) := some <$> f g
private def runGoalPipe (g0 : MVarId) (steps : List (MVarId → MetaM (Option MVarId))) : MetaM (Option MVarId) :=
  steps.foldlM (init := some g0) fun acc f => match acc with | none => pure none | some g => f g

private def userDecls (g : MVarId) : MetaM (Array (LocalDecl × Expr)) := g.withContext do
  let mut out := #[]
  for d in ← getLCtx do if isUserDecl d then out := out.push (d, ← instantiateMVars d.type)
  return out

private def simpCached (g : MVarId) (key : String) (ns : Array Name) (cfg : Simp.Config := {}) (sp : Array Name := #[])
    (fvs : Array FVarId := #[]) (simpTgt := true) (dsimpOnly := false) (allHyps := false) : MetaM (Option MVarId) := do
  let (ctx, sps) ← mkCachedSimpCtx key ns cfg sp dsimpOnly
  if allHyps then simpGoalAllHyps g ctx sps dsimpOnly else simpGoalOnly g ctx sps fvs simpTgt dsimpOnly

private def dsimpCodecGoal (g : MVarId) : MetaM (Option MVarId) :=
  simpCached g "dsimpCodec" (#[``Qed.Lang.QedVal.val, ``Qed.Server.SrvIdx.toNat, ``Qed.Server.SrvLiftOpt.liftOpt, ``Qed.Server.srvGetAt] ++ optCodecSimpNames)
    { zetaDelta := false } #[] #[] true true

private def dsimpCodecAndStrLen (g0 : MVarId) : MetaM (Option MVarId) :=
  runGoalPipe g0 [dsimpCodecGoal, fun g => simpCached g "strLenOnly" #[] { zetaDelta := false } strLenSP]

private def trySaveOpt {α : Type} (act : MetaM (Option α)) : MetaM (Option α) := do
  let s ← saveState
  let res? ← try act catch _ => pure none
  if res?.isNone then restoreState s
  return res?

private def isSrvHelperConst (c : Name) : Bool :=
  c == ``srvGetAt || c == ``Qed.Lang.QedVal.val || c == ``SrvIdx.toNat || c == ``SrvLiftOpt.liftOpt

private def hasSrvHelperConst (e : Expr) : Bool := e.getUsedConstants.any fun c => isSrvHelperConst c || c == ``id

private def unfoldSrvHelpersExpr (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun sub => do
    if sub.isAppOfArity ``id 2 then return .visit sub.getAppArgs[1]!
    if let some cn := sub.getAppFn.constName? then
      if isSrvHelperConst cn then
        let u? ← match ← unfoldProjInst? sub with | some x => pure (some x) | none => unfoldDefinition? sub
        if let some u := u? then return .visit (if u.isAppOfArity ``id 2 then u.getAppArgs[1]! else u)
    return .continue)

private def nextFreshSrvName (g : MVarId) (pfx : String) (startIdx : Nat) : MetaM (Name × Nat) := do
  let lctx ← g.withContext getLCtx; let mut i := startIdx; let mut cand := Name.mkSimple s!"{pfx}{i}"
  while lctx.any (·.userName == cand) do i := i + 1; cand := Name.mkSimple s!"{pfx}{i}"
  return (cand, i + 1)

private def maybeRenameMacro (g : MVarId) (decl : LocalDecl) (pfx : String) (idx : Nat) : MetaM (MVarId × Nat) := do
  if !decl.userName.hasMacroScopes then return (g, idx)
  let (cand, nxt) ← nextFreshSrvName g pfx idx; return (← g.rename decl.fvarId cand, nxt)

private def unfoldSrvHelpersGoal (g0 : MVarId) : MetaM MVarId := do
  let decls ← userDecls g0; let mut g := g0; let mut hIdx := (← g0.withContext getLCtx).size; let mut propFVars : Array FVarId := #[]
  for (decl, ty) in decls do
    if !isSrvEqDecl decl then
      if ← g.withContext (isPropSafe ty) then
        let (g', nxt) ← maybeRenameMacro g decl "_srvSplitH" hIdx; g := g'; hIdx := nxt
        if hasSrvHelperConst ty then propFVars := propFVars.push decl.fvarId
  for fv in propFVars.reverse do
    if let some decl := (← g.withContext getLCtx).find? fv then
      let ty ← g.withContext (instantiateMVars decl.type)
      if hasSrvHelperConst ty then
        let ty' ← g.withContext (unfoldSrvHelpersExpr ty)
        if ty' != ty then
          if (← goalType g).containsFVar fv then
            let (cand, nxt) ← nextFreshSrvName g "_srvFreeH" hIdx; hIdx := nxt
            g := (← (← g.assert cand ty' (mkFVar fv)).intro1P).2
          g ← tryGoalM g (·.changeLocalDecl fv ty')
  let tgt ← goalType g
  if hasSrvHelperConst tgt then
    let tgt' ← g.withContext (unfoldSrvHelpersExpr tgt)
    if tgt' != tgt then g ← tryGoalM g (·.change tgt')
  return g

private def simpHypsEachGoal (g0 : MVarId) : MetaM (Option MVarId) := do
  let mut hFVars : Array FVarId := #[]
  for (d, ty) in ← userDecls g0 do
    if !d.userName.hasMacroScopes && !isSrvEqDecl d then
      if ← g0.withContext (isPropSafe ty) then hFVars := hFVars.push d.fvarId
  let mut g := g0
  if !hFVars.isEmpty then
    let (hypCtx, _) ← mkCachedSimpCtx "hypSimpEach"
      (#[``id_eq, ``ne_eq, ``Prod.mk.injEq, ``Option.some.injEq, ``Except.ok.injEq, ``Except.error.injEq, ``reduceCtorEq,
         ``Qed.Lang.not_qedAndProp, ``Qed.Lang.not_qedOrProp] ++ diteFalseSimpNames ++ unwrapOkSimpNames ++
       valUnwrapSimpNames ++ liftOptSimpNames ++ optCodecSimpNames ++ arrayCoreSimpNames ++ boolSimpNames)
    match ← trySaveOpt (some <$> (match (← simpGoal g hypCtx #[] none false hFVars).1 with | none => pure none | some (_, g') => pure (some g'))) with
    | some none => return none
    | some (some g') => g := g'
    | none => for fv in hFVars do match ← simpGoalOnly g hypCtx #[] #[fv] false false with | none => return none | some g' => g := g'
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

@[term_elab srvAutoFieldStx]
def elabSrvAutoField : TermElab := fun stx expectedType? => do
  let valStx : Term := ⟨stx.getArg 1⟩
  if let some expTy := expectedType? then
    let expTy ← instantiateMVars expTy
    if !expTy.getAppFn.isMVar then
      let expWhnf ← whnf expTy
      if expWhnf.isAppOfArity ``Qed.Field 2 then
        let saved ← saveState; let preMsgs := (← Core.getMessageLog).toList.length
        let direct? ← try
          let e ← Term.withoutErrToSorry <| elabTermEnsuringType valStx (some expTy)
          synthesizeSyntheticMVarsNoPostponing
          let e ← instantiateMVars e
          if (← Core.getMessageLog).toList.length == preMsgs && !e.hasMVar then pure (some e) else pure none
        catch _ => pure none
        if let some direct := direct? then return direct
        restoreState saved
        let innerTy := expWhnf.getAppArgs[0]!; let predFn := expWhnf.getAppArgs[1]!
        let valExpr ← elabTermEnsuringType valStx (some innerTy); synthesizeSyntheticMVarsNoPostponing
        let valExpr ← instantiateMVars valExpr; let goalProp := mkApp predFn valExpr
        let isLit := valExpr.isLit || (valExpr.getAppFn.isConstOf ``OfNat.ofNat && !valExpr.hasFVar)
        let localFacts ← if isLit then pure #[] else liftMetaM <| collectFacts { scanLCtx := false, includeFin := true } #[valExpr]
        let mut prf? ← proveGoalWithMeta localFacts goalProp (solveAutoFieldFast isLit)
        if prf?.isNone then prf? ← proveGoalWithMeta (← collectProofFacts #[valExpr]) goalProp (fun g _ => solveRefinementSlow g)
        let some prfExpr := prf? | throwFieldRuleFailed stx predFn valExpr
        return ← mkAppOptM ``Qed.Field.mk #[some innerTy, some predFn, some valExpr, some (← wrapAuxProof goalProp prfExpr)]
      else return ← try elabTermEnsuringType valStx (some expTy) catch _ => elabTermEnsuringType (← `(Qed.Lang.QedVal.val $valStx)) (some expTy)
  let e ← elabTerm valStx none; synthesizeSyntheticMVars (postpone := .yes)
  let ty ← whnf (← instantiateMVars (← inferType e))
  let e ← if ty.isAppOfArity ``Qed.Field 2 then mkAppM ``Qed.Field.val #[e] else pure e
  maybeEnsureType expectedType? e

@[term_elab srvAutoEmitStx]
def elabSrvAutoEmit : TermElab := fun stx expectedType? => do
  let propExpr ← match expectedType? with | some expTy => instantiateMVars expTy | none => elabTerm (stx.getArg 1) (some (mkSort Level.zero))
  let some prfExpr ← proveGoalWithMeta (← collectProofFacts #[propExpr]) propExpr (fun g _ => solveRefinementSlow g)
    | throwErrorAt stx m!"Channel `ensures` postcondition failed at `emit`:\n  • must satisfy:  {← Qed.Diag.ppQedExpr ((← unfoldDefinition? propExpr).getD propExpr)}\n\n\
        Hint: Ensure the emitted event satisfies the channel's `ensures` clause."
  wrapAuxProof propExpr prfExpr

@[term_elab srvTypedAsStx]
def elabSrvTypedAs : TermElab := fun stx expectedType? => do
  let tplExpr ← elabTerm (stx.getArg 1) none; synthesizeSyntheticMVarsNoPostponing
  maybeEnsureType expectedType? (← elabTermEnsuringType (stx.getArg 3) (some (← instantiateMVars (← inferType tplExpr))))

/-! ## Bounds Checking (`srvGetElem`, `srvSetElem`) — O(N) Size-Chain Fast Path -/

private def unwrapSizeSet? (e : Expr) : Nat → MetaM (Option (Expr × Expr))
  | 0 => return none
  | fuel + 1 => do
      let eC := e.consumeMData
      if eC.isAppOfArity ``Array.set 5 then
        let a := eC.getAppArgs; return some (a[1]!, ← mkAppOptM ``Array.size_set #[some a[0]!, some a[1]!, some a[2]!, some a[3]!, some a[4]!])
      else if eC.isAppOfArity ``srvLetEq 4 then
        let a := eC.getAppArgs; unwrapSizeSet? (mkApp2 a[3]! a[2]! (← mkEqRefl a[2]!)).headBeta fuel
      else return none

private def proveSizeEqChain (lctx : LocalContext) (startArr : Expr) : MetaM (Expr × Option Expr) := do
  let mut cur := startArr; let mut eqOpt? : Option Expr := none; let mut seen : Array FVarId := #[]
  for _ in [0:lctx.size] do
    let Expr.fvar fv := cur.consumeMData | break
    if seen.contains fv then break else seen := seen.push fv
    let mut next? : Option (Expr × Expr) := none
    for decl in lctx do
      if isUserDecl decl then
        if let some (_, lhs, rhs) := (← instantiateMVars decl.type).eq? then
          if lhs.consumeMData == Expr.fvar fv then
            let rhsC := rhs.consumeMData; let arrTy ← whnf (← inferType cur)
            let elemTy := if arrTy.isAppOfArity ``Array 1 then arrTy.getAppArgs[0]! else mkConst ``Unit
            let mkSizeCongr := do mkAppM ``congrArg #[← mkAppOptM ``Array.size #[some elemTy], decl.toExpr]
            if let some (prevArr, eqSet) ← try unwrapSizeSet? rhsC 8 catch _ => pure none then
              next? := some (prevArr, ← mkEqSymm (← mkEqTrans (← mkSizeCongr) eqSet)); break
            else if !rhsC.containsFVar fv && !(rhsC.getUsedConstants.any (· == ``srvLetEq)) then
              next? := some (rhsC, ← mkEqSymm (← mkSizeCongr)); break
    match next? with
    | some (prevArr, prevEqCur) => eqOpt? := some (← eqOpt?.elim (pure prevEqCur) (mkEqTrans prevEqCur ·)); cur := prevArr
    | none => break
  return (cur, eqOpt?)

private def solveBoundsFast (g0 : MVarId) : MetaM Bool := do
  let some g1 ← runGoalPipe g0 [closeIf tryCloseSrvTrivial, (tryGoalOptM · (simpCached · "boundsTgt" (#[``id_eq, ``Array.size_set, ``Array.size_push, ``Array.size_modify] ++ valUnwrapSimpNames) { zetaDelta := true }))] | return true
  let mut sizeFVars : Array FVarId := #[]
  for (d, ty) in ← userDecls g1 do
    if !d.userName.hasMacroScopes then
      if ← g1.withContext (isPropSafe ty) then
        let cs := ty.getUsedConstants
        if (cs.any fun c => c == ``Array.size || c == ``LT.lt || c == ``LE.le || c == ``GE.ge || c == ``GT.gt) &&
           !(cs.any fun c => c == ``srvGetAt || c == ``RequestCtx || c == ``Array.set) then sizeFVars := sizeFVars.push d.fvarId
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

private def proveBoundsFor (ref : Syntax) (arrExpr idxNatExpr : Expr) : TermElabM Expr := do
  let goalProp ← mkAppM ``LT.lt #[idxNatExpr, ← mkAppM ``Array.size #[arrExpr]]
  let (baseArr, sizeEqOpt?) ← proveSizeEqChain (← getLCtx) arrExpr
  if let some basePrf ← proveGoalWithMeta #[] (← mkAppM ``LT.lt #[idxNatExpr, ← mkAppM ``Array.size #[baseArr]]) (fun g _ => solveBoundsFast g) then
    return ← wrapAuxProof goalProp (← sizeEqOpt?.elim (pure basePrf) fun eqPrf => mkAppM ``Nat.lt_of_lt_of_eq #[basePrf, eqPrf])
  let some prfExpr ← proveGoalWithMeta (← collectProofFacts #[arrExpr, idxNatExpr]) goalProp (fun g _ => solveBoundsSlow g)
    | do let (pArr, pIdx) := (← Qed.Diag.ppQedExpr arrExpr, ← Qed.Diag.ppQedExpr idxNatExpr)
         throwErrorAt ref m!"Array index `{pIdx}` could be out of bounds for `{pArr}`:\n  • must satisfy:  {pIdx} < {pArr}.size\n\n\
           Hint: Guard this access with `if {pIdx} < {pArr}.size:`."
  wrapAuxProof goalProp prfExpr

private def elabSrvArrOrDictOp (stx : Syntax) (arrStx idxStx : Term) (valStx? : Option Term) (expectedType? : Option Expr) : TermElabM Expr := do
  let arrExpr ← elabTerm arrStx none; synthesizeSyntheticMVarsNoPostponing
  let arrExpr ← instantiateMVars arrExpr; let arrTy ← whnf (← inferType arrExpr)
  if arrTy.isAppOfArity `Qed.Dict 2 then
    return ← elabTerm (← valStx?.elim `(Qed.Dict.get $arrStx $idxStx) fun v => `(Qed.Dict.set $arrStx $idxStx (srvAutoField($v)))) expectedType?
  unless arrTy.isAppOfArity ``Array 1 do
    throwErrorAt arrStx m!"expected an array (`T[]`) for {if valStx?.isSome then "indexed assignment" else "indexing"}, got `{← ppExpr arrTy}`"
  let elemTy := arrTy.getAppArgs[0]!
  let idxNatExpr ← elabTermEnsuringType (← `(Qed.Server.SrvIdx.toNat $idxStx)) (some (mkConst ``Nat))
  let valExpr? ← valStx?.mapM fun v => do elabTermEnsuringType (← `(srvAutoField($v))) (some elemTy)
  synthesizeSyntheticMVarsNoPostponing
  let arrExpr ← instantiateMVars arrExpr; let idxNatExpr ← instantiateMVars idxNatExpr; let valExpr? ← valExpr?.mapM instantiateMVars
  let ltPrf ← proveBoundsFor stx arrExpr idxNatExpr
  maybeEnsureType expectedType? (← valExpr?.elim
    (mkAppOptM ``srvGetAt #[some elemTy, some arrExpr, some idxNatExpr, some ltPrf])
    (fun v => mkAppOptM ``Array.set #[some elemTy, some arrExpr, some idxNatExpr, some v, some ltPrf]))

@[term_elab srvGetElemStx] def elabSrvGetElem : TermElab := fun stx => elabSrvArrOrDictOp stx ⟨stx.getArg 1⟩ ⟨stx.getArg 3⟩ none
@[term_elab srvSetElemStx] def elabSrvSetElem : TermElab := fun stx => elabSrvArrOrDictOp stx ⟨stx.getArg 1⟩ ⟨stx.getArg 3⟩ (some ⟨stx.getArg 5⟩)

/-! ## Automated Server Invariant Prover (`qedSrvProveStep`, `qedSrvProveAsync`) -/

private def finishAtomGoal (g0 : MVarId) (allowDeepFallback : Bool := true) : TacticM (Option MVarId) := do
  let some g ← runGoalPipe g0 [
    closeIf tryCloseSrvTrivial, liftStep unfoldSrvHelpersGoal,
    (simpCached · "finishAtomPre" (valUnwrapSimpNames ++ liftOptSimpNames ++ #[``Array.getElem_set_self] ++ dictSimpNames)),
    dsimpCodecGoal, closeIf tryCloseSrvTrivial, closeIf tryDirectOmega] | return none
  let (g, invFactFVars) ← collectAndAssertFacts g "_invFact" {
    includeFin := true, includeCollectionRules := true, rounds := 4,
    skipDecl := fun d dty => isSrvEqDecl d && match dty.eq? with | some (_, _, rhs) => rhs.getUsedConstants.any fun c => c == ``Array.set || c == ``Array.push | none => true }
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
        | .proj _ _ b | .letE _ _ b _ _ => collectReadySrvLetEqs b fuel
        | _ => return #[]

private def tryPickSrvLetEq (gGoal : MVarId) (cands : Array Expr) (revCount : Nat) : MetaM (Option (Expr × Expr × MVarId × Nat)) := do
  let tgtNow ← goalType gGoal
  for letApp in cands do
    if let some hit ← trySaveOpt <| gGoal.withContext do
      let a := letApp.getAppArgs; let absBody ← Meta.kabstract tgtNow letApp
      unless absBody.hasLooseBVar 0 do return none
      let pred := Lean.mkLambda `_ BinderInfo.default a[1]! absBody
      unless (← Meta.isTypeCorrect pred) do return none
      let elimPrf ← Meta.mkAppOptM ``Qed.Server.srvLetEq_elim #[some a[0]!, some a[1]!, some pred, some a[2]!, some a[3]!]
      match ← try some <$> gGoal.apply elimPrf catch _ => pure none with | some [sg] => return some (a[3]!, absBody, sg, revCount) | _ => return none
    then return some hit
  return none

private def elimSrvLetEqGoal (g : MVarId) (allowHyps : Bool := true) : MetaM (Option MVarId) := do
  let tgt ← goalType g; let mut picked? : Option (Expr × Expr × MVarId × Nat) := none
  if tgt.getUsedConstants.any (· == ``Qed.Server.srvLetEq) then picked? ← tryPickSrvLetEq g (← collectReadySrvLetEqs tgt 1024) 0
  if picked?.isNone && allowHyps then
    for (d, dty) in ← userDecls g do
      if dty.getUsedConstants.any (· == ``Qed.Server.srvLetEq) then
        let cands ← collectReadySrvLetEqs dty 1024
        unless cands.isEmpty do
          if let some hit ← trySaveOpt (do let (rev, gRev) ← g.revert #[d.fvarId]; tryPickSrvLetEq gRev cands rev.size) then
            picked? := some hit; break
  let some (kFun, absBody, newGoal, revCount) := picked? | return none
  let (valName, idx1) ← nextFreshSrvName newGoal "_srvVal" (← newGoal.withContext getLCtx).size
  let (eqName, _) ← nextFreshSrvName newGoal "_srvEq" idx1
  let (valFVar, g1) ← newGoal.intro valName; let (eqFVar, g2) ← g1.intro eqName
  let g3 ← tryGoalM g2 (·.change (absBody.instantiate1 (mkApp2 kFun (mkFVar valFVar) (mkFVar eqFVar)).headBeta))
  some <$> if revCount > 0 then tryGoalM g3 (Prod.snd <$> ·.introN revCount) else pure g3

private def elimAllSrvLetEqTarget (g0 : MVarId) : MetaM (MVarId × Bool) := do
  let mut g := g0; let mut did := false
  for _ in [0:128] do match ← elimSrvLetEqGoal g false with | some g' => g := g'; did := true | none => break
  return (g, did)

private def rewriteTargetByFVar (g : MVarId) (eqFVar : FVarId) : MetaM (Option MVarId) :=
  trySaveOpt do let r ← g.withContext (g.rewrite (← goalType g) (mkFVar eqFVar)); some <$> g.replaceTargetEq r.eNew r.eqProof

private def mkArrCongrLemmas (elemTy lhs rhs hE : Expr) : MetaM (Expr × Expr) := do
  let sizeLhs ← mkAppM ``Array.size #[lhs]
  withLocalDecl `j .implicit (mkConst ``Nat) fun j => do
    withLocalDeclD `hj (← mkAppM ``LT.lt #[j, sizeLhs]) fun hj => do
      let mk (c : Name) := do mkLambdaFVars #[j, hj] (← mkAppOptM c #[some elemTy, some rhs, some lhs, some j, some hE, some hj])
      return (← mk ``Qed.Server.getElem_congr_arr, ← mk ``Qed.Server.srvGetAt_congr_arr)

private def rewriteTargetEqsLinearGoal (g0 : MVarId) : MetaM (Option MVarId) := do
  let mut eqDecls : Array (FVarId × Option (Expr × Expr × Expr) × FVarId) := #[]
  for (d, dty) in ← userDecls g0 do
    if isSrvEqDecl d then
      if let some (eqTy, lhs, rhs) := dty.eq? then
        if let .fvar fv := lhs.consumeMData then
          if !rhs.containsFVar fv then
            let arrInfo? ← g0.withContext do
              let w ← whnf eqTy; return if w.isAppOfArity ``Array 1 then some (w.getAppArgs[0]!, lhs.consumeMData, rhs) else none
            eqDecls := eqDecls.push (fv, arrInfo?, d.fvarId)
  if eqDecls.isEmpty then return some g0
  let (postRwCtx, _) ← mkCachedSimpCtx "postRw" (#[``Array.sumBy_empty, ``Array.sumBy_push] ++ arrayCoreSimpNames ++ valUnwrapSimpNames ++ liftOptSimpNames)
  let mut g := g0
  for (fv, arrInfo?, eqFv) in eqDecls.reverse do
    if (← goalType g).containsFVar fv then
      let mut progressed := false
      if let some (elemTy, lhs, rhs) := arrInfo? then
        let arrCongrRes ← g.withContext do
          try
            let base ← getCachedSimpThms "arrSetSimp" #[``Array.getElem_set_self, ``Array.getElem_set]
            let (c1, c2) ← mkArrCongrLemmas elemTy lhs rhs (mkFVar eqFv)
            let st ← (← base.add (.other `arrCongr1) #[] c1).add (.other `arrCongr2) #[] c2
            return some (← Simp.mkContext { zetaDelta := false, failIfUnchanged := false } #[st] (← getSimpCongrTheorems), ← getCachedSimprocs #[`reduceIte] false)
          catch _ => return none
        if let some (ctx, sp) := arrCongrRes then
          match ← simpGoalOnly g ctx sp with | none => return none | some g' => g := g'; progressed := true
      if (← goalType g).containsFVar fv then
        if let some g' ← rewriteTargetByFVar g eqFv then g := g'; progressed := true
      if progressed then match ← simpGoalOnly g postRwCtx with | none => return none | some g' => g := g'
  return some g

private theorem srv_forall_push {α : Type} {P : α → Prop} {xs : Array α} {v : α}
    (hxs : ∀ x ∈ xs, P x) (hv : P v) : ∀ x ∈ xs.push v, P x := (Array.forall_push (P := P) (xs := xs) (v := v)).2 ⟨hxs, hv⟩

private def peelArrayForallGoal (g0 : MVarId) (allowDeepFallback : Bool := true) : TacticM (List MVarId) := do
  let rec loop : Nat → MVarId → TacticM (List MVarId)
    | 0, g => return [g]
    | fuel + 1, g => do
        let some g ← runGoalPipe g [dsimpTargetOnly, closeIf tryCloseSrvTrivial] | return []
        let some arrExpr := extractForEachColl? (← goalType g) | return [g]
        for (ctor, arity, lem) in #[(``Array.set, 5, ``Array.forall_set), (``Array.push, 3, ``srv_forall_push)] do
          if arrExpr.isAppOfArity ctor arity then
            if let some [gPrev, gElem] ← tryApplyConst g lem then
              let elemRem ← match ← runGoalPipe gElem [dsimpTargetOnly, rewriteTargetEqsLinearGoal] with
                | none => pure [] | some ge => pure (← finishAtomGoal ge allowDeepFallback).toList
              return (← loop fuel gPrev) ++ elemRem
        if let .fvar fv := arrExpr then
          for (d, ty) in ← userDecls g do
            if !d.userName.hasMacroScopes then
              if let some (_, lhs, _) := ty.eq? then
                if lhs.consumeMData == .fvar fv then
                  if let some g' ← rewriteTargetByFVar g d.fvarId then return ← loop fuel g'
                  break
        if ← g.assumptionCore then return []
        return [g]
  loop 128 g0

private def substMatchEqHypsGoal (g0 : MVarId) : MetaM MVarId := do
  let mut g := g0
  for _ in [0:16] do
    let lctx ← g.withContext getLCtx; let mut substGoal? : Option MVarId := none
    let trySubstSide (declFv : FVarId) (varSide otherSide : Expr) (allowNonMacro symm : Bool) : MetaM (Option MVarId) := do
      let .fvar fv := varSide.consumeMData | return none
      unless fv != declFv && !otherSide.containsFVar fv && (((lctx.find? fv).any (·.userName.hasMacroScopes)) || allowNonMacro) do return none
      trySaveOpt <| g.withContext do some <$> (Prod.snd <$> Meta.substCore g declFv (symm := symm))
    for (d, ty) in ← userDecls g do
      if substGoal?.isNone then
        let u := d.userName.toString
        if u.startsWith "_srvMatchEq" || u.startsWith "_srvSplitH" then
          if let some (_, lhs, rhs) := ty.eq? then
            substGoal? ← trySubstSide d.fvarId rhs lhs (u.startsWith "_srvMatchEq") true
            if substGoal?.isNone then substGoal? ← trySubstSide d.fvarId lhs rhs false false
    match substGoal? with | some g' => g := g' | none => break
  return g

private def closeLeafGoal (g0 : MVarId) (allowDeepFallback : Bool := true) : TacticM (List MVarId) := do
  let simpWNS (g : MVarId) : MetaM (Option MVarId) := do
    if (← goalType g).consumeMData.isAppOf ``Qed.Server.srvWithNewState then simpCached g "withNewState" #[``Qed.Server.srvWithNewState_apply]
    else pure (some g)
  let some g ← runGoalPipe g0 [
    simpWNS, closeIf tryCloseSrvTrivial, dsimpTargetOnly, closeIf tryCloseSrvTrivial,
    liftStep fun g => do Prod.fst <$> splitAndHypsGoal (← tryGoalM g unfoldSrvHelpersGoal),
    (tryGoalOptM · simpHypsEachGoal), liftStep substMatchEqHypsGoal,
    simpWNS, dsimpTargetOnly, dsimpCodecGoal, closeIf tryCloseSrvTrivial] | return []
  let (g, didSplit2) ← splitAndHypsGoal g
  let g ← if !didSplit2 then pure g else do
    let some g' ← tryGoalOptM g simpHypsEachGoal | return []
    substMatchEqHypsGoal g'
  let mut rem : List MVarId := []
  for cg in ← splitGoalAnds g do
    if ← tryCloseSrvTrivial cg then continue
    for pg in ← peelArrayForallGoal cg allowDeepFallback do
      if ← tryCloseSrvTrivial pg then continue
      if let some rg ← rewriteTargetEqsLinearGoal pg then
        if let some fg ← finishAtomGoal rg allowDeepFallback then rem := rem ++ [fg]
  return rem

private def exprHasSplittable (e : Expr) : Bool := e.getUsedConstants.any fun c => c == ``ite || c == ``dite || c.toString.contains ".match_"

private def splitEqHypGoal (g0 : MVarId) : MetaM (Option (List MVarId)) := do
  let mut idx := (← g0.withContext getLCtx).size; let mut gCur := g0; let mut eqFVars : Array FVarId := #[]
  for (d, ty) in ← userDecls g0 do
    if ty.isEq && exprHasSplittable ty then
      let (g', nxt) ← maybeRenameMacro gCur d "_srvMatchEq" idx; gCur := g'; idx := nxt; eqFVars := eqFVars.push d.fvarId
  for fv in eqFVars do if let some sgs ← trySplitLocalDecl gCur fv then return some sgs
  return none

private def goalHasSplittableHyp (g : MVarId) : MetaM Bool := do
  return (← userDecls g).any fun (_, ty) => ty.getUsedConstants.any (· == ``Qed.Server.srvLetEq) || (ty.isEq && exprHasSplittable ty)

private def proveStepSingleGoal (g0 : MVarId) (allStepCtx : Simp.Context) : TacticM (List MVarId) := do
  let some g2 ← simpGoalAllHyps (← g0.intros).2 allStepCtx | return []
  let rec stepTargetLoop : Nat → List MVarId → TacticM (List MVarId)
    | 0, gs => return gs | _, [] => return []
    | fuel + 1, g :: rest => do
        if ← tryCloseSrvTrivial g then return ← stepTargetLoop fuel rest
        let pushSimp (g' : MVarId) := do stepTargetLoop fuel ((← simpGoalOnly g' allStepCtx).toList ++ rest)
        let (gLet, didLet) ← elimAllSrvLetEqTarget g
        if didLet then return ← pushSimp gLet
        match ← trySplitTarget g with
        | some sgs => return ← stepTargetLoop fuel ((← sgs.filterMapM (simpGoalOnly · allStepCtx)) ++ rest)
        | none =>
            if ← goalHasSplittableHyp g then
              let s ← saveState
              if (← closeLeafGoal g false).isEmpty then return ← stepTargetLoop fuel rest
              restoreState s
              if let some gHypLet ← elimSrvLetEqGoal g true then return ← pushSimp gHypLet
              if let some eqSgs ← splitEqHypGoal g then return ← stepTargetLoop fuel ((← eqSgs.filterMapM (simpGoalAllHyps · allStepCtx)) ++ rest)
            return (← closeLeafGoal g true) ++ (← stepTargetLoop fuel rest)
  stepTargetLoop 256 [g2]

private def runProveStepOnGoals (gs : List MVarId) (userNames : Array Name) (fnStr lbl : String) (throwOnRem : Bool := true) : TacticM Unit := do
  let allStepCtx ← mkDynamicSimpCtx userNames (some ("stepFixed", unwrapOkSimpNames ++ stepCombSimpNames ++ stepLetEqSimpNames ++ ensPostSimpNames ++ valUnwrapSimpNames ++ liftOptSimpNames))
  let mut rem : List MVarId := []
  for g in gs do rem := rem ++ (← proveStepSingleGoal g allStepCtx)
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
      runProveStepOnGoals (← getGoals) (← unfoldIds.mapM resolveGlobalConstNoOverload) fnLabel.getString invLabel.getString
  | `(tactic| qedSrvPrepStep [$[$unfoldIds:ident],*]) => do
      runProveStepOnGoals (← getGoals) (← unfoldIds.mapM resolveGlobalConstNoOverload) "" "" (throwOnRem := false)

/-! ## Unified AST-Directed Async Prover Directly over `ProgSpec` -/

private def dropTrivialGoals (gs : List MVarId) : MetaM (List MVarId) :=
  gs.filterM fun g => do
    let s ← saveState; let (_, g') ← g.intros
    if (← goalType g').isConstOf ``True then g'.assign (mkConst ``True.intro); return false
    restoreState s; return true

private def normAsyncContGoal (g0 : MVarId) (dCtx sCtx : Simp.Context) : MetaM (Option MVarId) :=
  runGoalPipe g0 [(tryGoalOptM · (simpGoalOnly · dCtx #[] #[] true true)), (tryGoalOptM · (simpGoalOnly · sCtx))]

private def tryCloseConstMutInv (g0 : MVarId) : TacticM (Option MVarId) := do
  let (_, g1) ← g0.intros; let tgtC := (← goalType g1).consumeMData
  if tgtC.isAppOfArity ``Qed.Server.ProgPreservesStepRel 5 then
    if let .lam _ _ (.lam _ _ body _) _ := tgtC.getAppArgs[3]!.consumeMData then
      if body.isAppOfArity ``Or 2 && !body.getAppArgs[1]!.hasLooseBVars then
        let s ← saveState
        try
          let [gH] ← g1.applyConst ``Qed.Server.progPreservesStepRel_of_const | restoreState s; return some g1
          let [gR] ← (← gH.introN 2).2.applyConst ``Or.inr | restoreState s; return some g1
          if (← closeLeafGoal gR).isEmpty then return none
          restoreState s
        catch _ => restoreState s
  return some g1

private def stepAsyncLoop (isPreserves : Bool) (dCtx sCtx : Simp.Context) (gInit : MVarId) : MetaM (List MVarId) := do
  let normCont (g : MVarId) (n : Nat) : MetaM (List MVarId) := do
    let g1 ← if n == 0 then pure g else Prod.snd <$> g.introN n
    return (← normAsyncContGoal g1 dCtx sCtx).toList
  let normSplits (sgs : List MVarId) := sgs.filterMapM (normAsyncContGoal · dCtx sCtx)
  let rec loop : Nat → List MVarId → MetaM (List MVarId)
    | 0, gs => return gs | _, [] => return []
    | fuel + 1, g :: rest => do
        let tgtC := (← goalType g).consumeMData
        let prog? := #[(``Qed.Server.ProgSpec, 7, 6), (``Qed.Server.ProgPreservesStepRel, 5, 4),
          (``Qed.Server.ProgPreservesInv, 4, 3), (``Qed.Server.ProgEnsures, 5, 4)].findSome? fun (c, a, i) =>
            if tgtC.isAppOfArity c a then some tgtC.getAppArgs[i]! else none
        let some progRaw := prog? | return g :: (← loop fuel rest)
        let prog := progRaw.consumeMData
        for (head, lem) in #[(``Qed.Server.ThreadProg.pure, ``Qed.Server.ProgSpec.pure), (``Pure.pure, ``Qed.Server.ProgSpec.pure_class),
                             (``Qed.Server.MonadAtomic.runAtomic, ``Qed.Server.ProgSpec.runAtomic), (``Qed.Server.MonadAtomic.runAtomicRead, ``Qed.Server.ProgSpec.runAtomicRead)] do
          if prog.isAppOf head then if let some sgs ← tryApplyConst g lem then return (← dropTrivialGoals sgs) ++ (← loop fuel rest)
        for (head, lem, nDone, nBody) in #[
            (``Qed.Server.srvForEachM, ``Qed.Server.progSpec_srvForEachM, 0, 2),
            (``Qed.Server.srvForFoldM, ``Qed.Server.progSpec_srvForFoldM, 1, 3),
            (``Qed.Server.srvForRangeM, ``Qed.Server.progSpec_srvForRangeM, 1, 4)] do
          if prog.isAppOf head then
            if let some [gDone, gBody] ← tryApplyConst g lem then
              let dRem ← if nDone == 0 then dropTrivialGoals [gDone] else normCont gDone nDone
              return ← loop fuel (dRem ++ (← normCont gBody nBody) ++ rest)
        if prog.isAppOf ``Bind.bind || prog.isAppOf ``Qed.Server.ThreadProg.bind then
          let pArg := (if prog.isAppOf ``Bind.bind then prog.getAppArgs[4]! else prog.getAppArgs[3]!).consumeMData
          for (head, lem, nDone, nBody) in #[
              (``Qed.Server.srvForEachM, ``Qed.Server.progSpec_srvForEachM_bind, 0, 2),
              (``Qed.Server.srvForFoldM, ``Qed.Server.progSpec_srvForFoldM_bind, 1, 3),
              (``Qed.Server.srvForRangeM, ``Qed.Server.progSpec_srvForRangeM_bind, 1, 4)] do
            if pArg.isAppOf head then
              if let some [gDone, gBody] ← tryApplyConst g lem then
                return ← loop fuel ((← normCont gDone nDone) ++ (← normCont gBody nBody) ++ rest)
          let atomicLem? :=
            if pArg.isAppOf ``Qed.Server.MonadAtomic.runAtomic then some (if isPreserves then ``Qed.Server.ProgSpec.runAtomic_bind_val else ``Qed.Server.ProgSpec.runAtomic_bind)
            else if pArg.isAppOf ``Qed.Server.MonadAtomic.runAtomicRead then some (if isPreserves then ``Qed.Server.ProgSpec.runAtomicRead_bind_val else ``Qed.Server.ProgSpec.runAtomicRead_bind)
            else none
          if let some lem := atomicLem? then
            if let some (gCont :: gExtra) ← tryApplyConst g lem then
              return ← loop fuel ((← normCont gCont (if isPreserves then 1 else 2)) ++ (← dropTrivialGoals gExtra) ++ rest)
          else
            if !isPreserves then
              if let some [gCont] ← tryApplyConst g ``Qed.Server.safeIOEnsures_bind then return ← loop fuel ((← normCont gCont 2) ++ rest)
              if exprHasSplittable pArg then if let some sgs ← trySplitTarget g then return ← loop fuel ((← normSplits sgs) ++ rest)
            if let some [gCont] ← tryApplyConst g ``Qed.Server.ProgSpec.safeIO_bind then return ← loop fuel ((← normCont gCont 1) ++ rest)
        if !isPreserves then if let some [gImp] ← tryApplyConst g ``Qed.Server.safeIOEnsures_final then return gImp :: (← loop fuel rest)
        if prog.isAppOf ``Qed.Server.srvLetEq then
          if let some gLet ← elimSrvLetEqGoal g false then return ← loop fuel ((← normCont gLet 0) ++ rest)
        if isPreserves && !(prog.getUsedConstants.any fun c => c == ``Qed.Server.MonadAtomic.runAtomic || c == ``Qed.Server.MonadAtomic.runAtomicRead) then
          if let some [] ← tryApplyConst g ``Qed.Server.ProgSpec.of_safeIO then return ← loop fuel rest
        match ← trySplitTarget g with
        | some sgs => return ← loop fuel ((← normSplits sgs) ++ rest)
        | none =>
            if isPreserves then if let some [] ← tryApplyConst g ``Qed.Server.ProgSpec.of_safeIO then return ← loop fuel rest
            return g :: (← loop fuel rest)
  loop 256 [gInit]

private def initAsyncSimpAndNorm (g : MVarId) (unfoldConsts : Array Name) :
    TacticM (Simp.Context × Simp.Context × Option MVarId) := do
  let (dCtx, _) ← mkCachedSimpCtx "asyncDsimp" #[``Qed.Server.srvSeqM, ``Qed.Server.dbRunTx, ``Qed.Server.SrvUnwrap.unwrap, ``Qed.Server.SrvErr.ofApi, ``Qed.Server.SrvUnwrapOpt.unwrapOpt] { zetaDelta := false } #[] true
  let (sCtx, _) ← mkCachedSimpCtx "asyncNorm" (stepCombSimpNames ++ stepLetEqSimpNames ++ ensPostSimpNames ++ #[``Qed.Server.threadProg_pure_bind, ``Qed.Server.threadProg_pure_bind', ``Qed.Server.threadProg_bind_pure_left, ``Qed.Server.threadProg_bind_pure_left', ``Qed.Server.threadProg_bind_assoc, ``Qed.Server.threadProg_bind_assoc_inner, ``Qed.Server.threadProg_bind_assoc'])
  let gInit? ← runGoalPipe (← g.intros).2 [
    fun g => do tryGoalOptM g (simpGoalOnly · (← mkDynamicSimpCtx unfoldConsts (some ("asyncInit", #[``Qed.Server.srvFinishM, ``Qed.Server.srvSeqM, ``Qed.Server.dbRunTx])))),
    (normAsyncContGoal · dCtx sCtx)]
  return (dCtx, sCtx, gInit?)

private def elabAsyncProve (isPreserves : Bool) (handlerId : Ident) (invUnfoldIds : Array Ident) (fnLabel invLabel : String) (throwOnRem : Bool := true) : TacticM Unit := do
  let g0 ← getMainGoal
  let g1 ← if isPreserves then
      let some g' ← tryCloseConstMutInv g0 | replaceMainGoal []; return
      pure g'
    else pure g0
  let handlerConst ← resolveGlobalConstNoOverload handlerId; let userNames ← invUnfoldIds.mapM resolveGlobalConstNoOverload
  let (helperConsts, invConsts) := userNames.partition fun n => n.getString!.startsWith "_fn_"
  let (dCtx, sCtx, some gInit) ← initAsyncSimpAndNorm g1 (#[handlerConst] ++ helperConsts) | replaceMainGoal []; return
  runProveStepOnGoals (← stepAsyncLoop isPreserves dCtx sCtx gInit) invConsts fnLabel invLabel throwOnRem

private def stepSafeIOLoop (dCtx sCtx : Simp.Context) (gInit : MVarId) : TacticM (List MVarId) :=
  let norm1 (g' : MVarId) : TacticM (List MVarId) := return (← normAsyncContGoal g' dCtx sCtx).toList
  let rec loop : Nat → List MVarId → TacticM (List MVarId)
    | _, [] => return []
    | 0, gs => return gs
    | fuel + 1, g :: rest => do
        if let some [] ← tryApplyConst g ``Qed.Server.NoAtomic.pure then return ← loop fuel rest
        if let some [] ← tryApplyConst g ``Qed.Server.SafeIO.noAtomic then return ← loop fuel rest
        let tgtC := (← g.withContext do instantiateMVars (← g.getType)).consumeMData
        if tgtC.isAppOfArity ``Qed.Server.NoAtomic 3 then
          let prog := tgtC.getAppArgs[2]!.consumeMData
          if prog.isAppOf ``Bind.bind || prog.isAppOf ``Qed.Server.ThreadProg.bind then
            if let some [gLeft, gRight] ← tryApplyConst g ``Qed.Server.noAtomic_bind then
              let gLeftRem ← match ← tryApplyConst gLeft ``Qed.Server.SafeIO.noAtomic with | some [] => pure [] | _ => pure [gLeft]
              let (_, gR1) ← gRight.intro1P
              return ← loop fuel (gLeftRem ++ (← norm1 gR1) ++ rest)
          for (head, lem, nIntro) in #[
              (``Qed.Server.srvForEachM, ``Qed.Server.noAtomic_srvForEachM, 1),
              (``Qed.Server.srvForFoldM, ``Qed.Server.noAtomic_srvForFoldM, 2),
              (``Qed.Server.srvForRangeM, ``Qed.Server.noAtomic_srvForRangeM, 2)] do
            if prog.isAppOf head then
              if let some [gBody] ← tryApplyConst g lem then
                let (_, gB1) ← gBody.introN nIntro
                return ← loop fuel ((← norm1 gB1) ++ rest)
          if prog.isAppOf ``Qed.Server.srvLetEq then
            if let some gLet ← elimSrvLetEqGoal g false then return ← loop fuel ((← norm1 gLet) ++ rest)
        match ← trySplitTarget g with
        | some sgs => return ← loop fuel ((← sgs.filterMapM (normAsyncContGoal · dCtx sCtx)) ++ rest)
        | none => return g :: (← loop fuel rest)
  loop 256 [gInit]

@[noinline]
private def elabSafeIOProve (fnId : Ident) : TacticM Unit := do
  let g0 ← getMainGoal; let fnConst ← resolveGlobalConstNoOverload fnId
  let (dCtx, sCtx, some gInit) ← initAsyncSimpAndNorm g0 #[fnConst] | replaceMainGoal []; return
  let rem ← stepSafeIOLoop dCtx sCtx gInit
  setGoals rem
  unless rem.isEmpty do
    Qed.Diag.throwUnsolvedGoals m!"Server helper `{fnConst}` could not be proved `SafeIO` (no atomic state mutation):" m!"" (maxShown? := some 1) (goals? := some rem)

private def effWrapperUnfoldNames : Array Name := #[
  ``Qed.Server.srvFinishM, ``Qed.Server.srvSeqM, ``Qed.Server.dbRunTx, ``Qed.Server.newId,
  ``Qed.Server.hashBearerToken, ``Qed.Server.mintBearerToken, ``Qed.Server.flushWsEmits,
  `Qed.Server.Db.dbSelect, `Qed.Server.Db.dbSelectMeta, `Qed.Server.Db.dbSelectOne, `Qed.Server.Db.dbSelectJoin,
  `Qed.Server.Db.dbCount, `Qed.Server.Db.dbAggregate, `Qed.Server.Db.dbInsert, `Qed.Server.Db.dbInsertOrIgnore,
  `Qed.Server.Db.dbUpsert, `Qed.Server.Db.dbUpdateRun, `Qed.Server.Db.dbDeleteRun, `Qed.Server.Db.dbRun,
  `Qed.Server.Db.withTransaction]

private def tryCloseHypContradiction (g : MVarId) : TacticM Bool := do
  if ← tryRestoreM false id (g.contradictionCore {}) then return true
  let saved ← getGoals
  setGoals [g]
  let ok ← tryTac (requireClosed := true) `(tactic| (
    try simp_all only [Bool.not_eq_true', Bool.not_eq_false', not_true_eq_false, not_false_eq_true,
      decide_eq_true_eq, decide_eq_false_iff_not, beq_iff_eq, bne_iff_ne, Qed.Lang.QedVal.val_id,
      Qed.qedIterable_toList_array, Qed.qedIterable_toList_list, Qed.qedIterable_toList_range,
      Qed.Lang.QedSeqLit.ofList, Array.toList_empty, Array.toList_mk, List.mem_nil_iff, List.not_mem_nil]
    first | contradiction | omega))
  setGoals saved
  return ok

private def tryCloseEffSideGoal (g : MVarId) : TacticM Bool := do
  let saved ← getGoals
  setGoals [g]
  let ok ← tryTac (requireClosed := true) `(tactic| (
    first
    | (left; rfl)
    | (right; left; rfl)
    | (right; right; intros; first | rfl | trivial | decide | simp_all)
    | (right; constructor <;> (intros; first | rfl | trivial | decide | simp_all))
    | (intros
       try simp only [Qed.Server.ServerEffect.isHttp, Qed.Server.ServerEffect.isDecrypt,
         Qed.Server.ServerEffect.isCrypto, Qed.Server.ServerEffect.isDbWrite,
         Qed.Server.Db.SqlQuery.isWrite, Qed.Server.Db.dbExecEff] at *
       try split
       all_goals (try simp_all only [Qed.Server.ServerEffect.isHttp, Qed.Server.ServerEffect.isDecrypt,
         Qed.Server.ServerEffect.isCrypto, Qed.Server.ServerEffect.isDbWrite,
         Qed.Server.Db.SqlQuery.isWrite]; first | rfl | trivial | decide | omega))))
  setGoals saved
  return ok

private def stepEffSpecLoop (dCtx sCtx : Simp.Context) (gInit : MVarId) : TacticM (List MVarId) := do
  let env ← getEnv
  let hasDbLem := env.contains `Qed.Server.Db.progEffSpec_dbRunChecked_bind
  let normCont (g : MVarId) (n : Nat) : MetaM (List MVarId) := do
    let g1 ← if n == 0 then pure g else Prod.snd <$> g.introN n
    return (← normAsyncContGoal g1 dCtx sCtx).toList
  let normSplits (sgs : List MVarId) := sgs.filterMapM (normAsyncContGoal · dCtx sCtx)
  let rec loop : Nat → List MVarId → TacticM (List MVarId)
    | 0, gs => return gs | _, [] => return []
    | fuel + 1, g :: rest => do
        if ← tryCloseHypContradiction g then return ← loop fuel rest
        let tgtC := (← goalType g).consumeMData
        let prog? := #[(``Qed.Server.ProgEffSpec, 8, 7), (``Qed.Server.ProgEnsuresEff, 6, 5),
          (``Qed.Server.ProgAllowsEff, 4, 3), (``Qed.Server.ProgNoHttp, 3, 2),
          (``Qed.Server.ProgNoDecrypt, 3, 2), (``Qed.Server.ProgNoCrypto, 3, 2),
          (``Qed.Server.ProgNoDbWrite, 3, 2)].findSome? fun (c, a, i) =>
            if tgtC.isAppOfArity c a then some tgtC.getAppArgs[i]! else none
        let some progRaw := prog? | return g :: (← loop fuel rest)
        let prog := progRaw.consumeMData
        for (head, lem) in #[(``Qed.Server.ThreadProg.pure, ``Qed.Server.ProgEffSpec.pure),
                             (``Pure.pure, ``Qed.Server.ProgEffSpec.pure_class),
                             (``Qed.Server.MonadAtomic.runAtomic, ``Qed.Server.ProgEffSpec.runAtomic),
                             (``Qed.Server.MonadAtomic.runAtomicRead, ``Qed.Server.ProgEffSpec.runAtomicRead)] do
          if prog.isAppOf head then
            if let some sgs ← tryApplyConst g lem then
              let sgs' ← normSplits (← dropTrivialGoals sgs)
              return ← loop fuel (sgs' ++ rest)
        for (head, lem, nDone, nBody) in #[
            (``Qed.Server.srvForEachM, ``Qed.Server.progEffSpec_srvForEachM, 0, 2),
            (``Qed.Server.srvForFoldM, ``Qed.Server.progEffSpec_srvForFoldM, 1, 3),
            (``Qed.Server.srvForRangeM, ``Qed.Server.progEffSpec_srvForRangeM, 1, 4)] do
          if prog.isAppOf head then
            if let some [gDone, gBody] ← tryApplyConst g lem then
              let dRem ← if nDone == 0 then dropTrivialGoals [gDone] else normCont gDone nDone
              return ← loop fuel (dRem ++ (← normCont gBody nBody) ++ rest)
        if prog.isAppOf ``Qed.Server.MonadServer.exec then
          if let some [gEff, gPost] ← tryApplyConst g ``Qed.Server.ProgEffSpec.exec then
            let effRem ← if ← tryCloseEffSideGoal gEff then pure [] else pure [gEff]
            return effRem ++ (← dropTrivialGoals [gPost]) ++ (← loop fuel rest)
        if hasDbLem && prog.isAppOf `Qed.Server.Db.dbRunChecked then
          if let some [gEnc, gDb, gDec, gPost] ← tryApplyConst g `Qed.Server.Db.progEffSpec_dbRunChecked then
            let mut sideRem : List MVarId := []
            for sg in [gEnc, gDb, gDec] do if !(← tryCloseEffSideGoal sg) then sideRem := sideRem ++ [sg]
            return sideRem ++ (← dropTrivialGoals [gPost]) ++ (← loop fuel rest)
        if prog.isAppOf ``Bind.bind || prog.isAppOf ``Qed.Server.ThreadProg.bind then
          let pArg := (if prog.isAppOf ``Bind.bind then prog.getAppArgs[4]! else prog.getAppArgs[3]!).consumeMData
          if pArg.isAppOf ``Qed.Server.MonadAtomic.runAtomic then
            if let some (gCont :: gExtra) ← tryApplyConst g ``Qed.Server.ProgEffSpec.runAtomic_bind then
              return ← loop fuel ((← normCont gCont 2) ++ (← dropTrivialGoals gExtra) ++ rest)
          if pArg.isAppOf ``Qed.Server.MonadAtomic.runAtomicRead then
            if let some (gCont :: gExtra) ← tryApplyConst g ``Qed.Server.ProgEffSpec.runAtomicRead_bind then
              return ← loop fuel ((← normCont gCont 2) ++ (← dropTrivialGoals gExtra) ++ rest)
          if pArg.isAppOf ``Qed.Server.MonadServer.exec then
            if let some [gEff, gCont] ← tryApplyConst g ``Qed.Server.ProgEffSpec.exec_bind then
              let effRem ← if ← tryCloseEffSideGoal gEff then pure [] else pure [gEff]
              return effRem ++ (← loop fuel ((← normCont gCont 1) ++ rest))
          if hasDbLem && pArg.isAppOf `Qed.Server.Db.dbRunChecked then
            if let some [gEnc, gDb, gDec, gCont] ← tryApplyConst g `Qed.Server.Db.progEffSpec_dbRunChecked_bind then
              let mut sideRem : List MVarId := []
              for sg in [gEnc, gDb, gDec] do if !(← tryCloseEffSideGoal sg) then sideRem := sideRem ++ [sg]
              return sideRem ++ (← loop fuel ((← normCont gCont 2) ++ rest))
          for (head, lem, nDone, nBody) in #[
              (``Qed.Server.srvForEachM, ``Qed.Server.progEffSpec_srvForEachM_bind, 0, 2),
              (``Qed.Server.srvForFoldM, ``Qed.Server.progEffSpec_srvForFoldM_bind, 1, 3),
              (``Qed.Server.srvForRangeM, ``Qed.Server.progEffSpec_srvForRangeM_bind, 1, 4)] do
            if pArg.isAppOf head then
              if let some [gDone, gBody] ← tryApplyConst g lem then
                return ← loop fuel ((← normCont gDone nDone) ++ (← normCont gBody nBody) ++ rest)
          if exprHasSplittable pArg then
            if let some sgs ← trySplitTarget g then return ← loop fuel ((← normSplits sgs) ++ rest)
          if let some fnNm := pArg.getAppFn.constName? then
            if fnNm != ``Qed.Server.MonadServer.exec && fnNm != `Qed.Server.Db.dbRunChecked &&
               fnNm != ``Qed.Server.MonadAtomic.runAtomic && fnNm != ``Qed.Server.MonadAtomic.runAtomicRead &&
               fnNm != ``Qed.Server.srvForEachM && fnNm != ``Qed.Server.srvForFoldM && fnNm != ``Qed.Server.srvForRangeM then
              if let some (.defnInfo _) := env.find? fnNm then
                if let some g' ← tryGoalOptM g (simpGoalOnly · (← mkDynamicSimpCtx #[fnNm])) then
                  if let some g'' ← normAsyncContGoal g' dCtx sCtx then
                    if (← goalType g'') != tgtC then return ← loop fuel (g'' :: rest)
        if prog.isAppOf ``Qed.Server.srvLetEq then
          if let some gLet ← elimSrvLetEqGoal g false then return ← loop fuel ((← normCont gLet 0) ++ rest)
        if let some fnNm := prog.getAppFn.constName? then
          if fnNm != ``Qed.Server.ThreadProg.pure && fnNm != ``Pure.pure && fnNm != ``Bind.bind &&
             fnNm != ``Qed.Server.ThreadProg.bind && fnNm != ``Qed.Server.MonadServer.exec &&
             fnNm != `Qed.Server.Db.dbRunChecked && fnNm != ``ite && fnNm != ``dite &&
             fnNm != ``Qed.Server.srvForEachM && fnNm != ``Qed.Server.srvForFoldM && fnNm != ``Qed.Server.srvForRangeM then
            if let some (.defnInfo _) := env.find? fnNm then
              if let some g' ← tryGoalOptM g (simpGoalOnly · (← mkDynamicSimpCtx #[fnNm])) then
                if let some g'' ← normAsyncContGoal g' dCtx sCtx then
                  if (← goalType g'') != tgtC then return ← loop fuel (g'' :: rest)
        match ← trySplitTarget g with
        | some sgs => return ← loop fuel ((← normSplits sgs) ++ rest)
        | none => return g :: (← loop fuel rest)
  loop 256 [gInit]

@[noinline]
private def elabEffSpecProve (handlerId : Ident) (invUnfoldIds : Array Ident) (fnLabel invLabel : String) (throwOnRem : Bool := true) : TacticM Unit := do
  let g0 ← getMainGoal
  let handlerConst ← resolveGlobalConstNoOverload handlerId; let userNames ← invUnfoldIds.mapM resolveGlobalConstNoOverload
  let (helperConsts, invConsts) := userNames.partition fun n => n.getString!.startsWith "_fn_"
  let env ← getEnv
  let presentWrappers := effWrapperUnfoldNames.filter env.contains
  let (dCtx, sCtx, some gInit) ← initAsyncSimpAndNorm g0 (#[handlerConst] ++ helperConsts ++ presentWrappers) | replaceMainGoal []; return
  runProveStepOnGoals (← stepEffSpecLoop dCtx sCtx gInit) invConsts fnLabel invLabel throwOnRem

elab_rules : tactic
  | `(tactic| qedSrvProveAsync $handlerId:ident [$[$invUnfoldIds:ident],*] $fnLabel:str $invLabel:str) => elabAsyncProve true handlerId invUnfoldIds fnLabel.getString invLabel.getString
  | `(tactic| qedSrvProveAsyncEnsures $handlerId:ident [$[$invUnfoldIds:ident],*] $fnLabel:str $invLabel:str) => elabAsyncProve false handlerId invUnfoldIds fnLabel.getString invLabel.getString
  | `(tactic| qedSrvPrepAsyncEnsures $handlerId:ident [$[$invUnfoldIds:ident],*]) => elabAsyncProve false handlerId invUnfoldIds "" "" (throwOnRem := false)
  | `(tactic| qedSrvProveEffSpec $handlerId:ident [$[$invUnfoldIds:ident],*] $fnLabel:str $invLabel:str) => elabEffSpecProve handlerId invUnfoldIds fnLabel.getString invLabel.getString
  | `(tactic| qedSrvPrepEffSpec $handlerId:ident [$[$invUnfoldIds:ident],*]) => elabEffSpecProve handlerId invUnfoldIds "" "" (throwOnRem := false)
  | `(tactic| qedSrvProveSafeIO $fnId:ident) => elabSafeIOProve fnId

/-! ## Client RPC Precondition Prover (`qedProveRpcReq`) -/

elab_rules : tactic
  | `(tactic| qedProveRpcReq) => do
      let g0 ← getMainGoal
      let some g ← runGoalPipe g0 [
        closeIf tryCloseSrvBasic, liftStep fun g => try Prod.fst <$> splitAndHypsGoal g catch _ => pure g,
        liftStep (tryGoalM · unfoldSrvHelpersGoal),
        fun g => do simpGoalAllHyps g (← mkEmptyDsimpCtx) #[] true] | replaceMainGoal []; return
      let (g, _) ← assertFacts g "_reqFact" (← g.withContext do collectProofFacts #[← instantiateMVars (← g.getType)])
      let some g ← runGoalPipe g [
        liftStep (tryGoalM · unfoldSrvHelpersGoal),
        (simpCached · "arrayAndBool" arrayAndBoolSimpNames { zetaDelta := true } (allHyps := true)),
        (simpCached · "rpcReq" (#[``Option.isSome_iff_ne_none, ``ne_eq, `Qed.Cached.all, `Qed.Resource.all] ++ boolSimpNames ++ valUnwrapSimpNames ++ optCodecSimpNames) { zetaDelta := true, zetaHave := true } (allHyps := true)),
        dsimpCodecGoal] | replaceMainGoal []; return
      let rem ← (← splitGoalAnds g).filterMapM fun cg => do
        let (cg, _) ← try splitAndHypsGoal cg catch _ => pure (cg, false)
        if ← tryCloseSrvBasic cg then return none
        if ← closeWithFallback cg { skipTarget := hasUnsteppedCtrlFlow, simpAllCfg := { zetaDelta := true, zetaHave := true }, deepExtraSimpAll := #[``Qed.Server.srvLetEq] } then return none
        return some cg
      setGoals rem
      unless rem.isEmpty do
        Qed.Diag.throwUnsolvedGoals m!"Server `requires` precondition could not be proved:"
          m!"\n\nHint: Guard this RPC call with `if ...:` so the precondition holds." (goals? := some (rem.take 1))

end Qed.Server
