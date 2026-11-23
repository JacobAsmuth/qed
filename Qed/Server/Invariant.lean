import Qed.Verify.Core
import Qed.Field
import Qed.Server.Core
import Qed.Server.Syntax
import Qed.Server.Registry

namespace Qed.Server

@[inline] instance {Inner : Type} {p : Inner → Prop} : SrvLiftOpt (Qed.Field p) Inner := ⟨fun f => some f.val⟩
@[inline] instance {Inner : Type} {p : Inner → Prop} : SrvLiftOpt (Option (Qed.Field p)) Inner := ⟨Option.map Qed.Field.val⟩

/-! ## Cached `Simp.Context` Rule Sets -/

theorem srvDiteFalse_eq_true {P : Prop} [Decidable P] (t : P → Bool) :
    ((if h : P then t h else false) = true) ↔ ∃ h : P, t h = true := by
  by_cases hP : P <;> simp [hP]

theorem srvDiteFalse_eq_false {P : Prop} [Decidable P] (t : P → Bool) :
    ((if h : P then t h else false) = false) ↔ ∀ h : P, t h = false := by
  by_cases hP : P <;> simp [hP]

open Lean Meta Elab Term Tactic Qed.Verify.Core

private def strLenSP : Array Name := #[``qedReduceStrLen]

private def valUnwrapSimpNames : Array Name :=
  #[``Qed.Server.srvGetAt_eq, ``Qed.Server.SrvIdx.toNat_nat, ``Qed.Server.SrvIdx.toNat_fin] ++
  valUnwrapBaseNames

private def liftOptSimpNames : Array Name := #[
  ``Qed.Server.SrvLiftOpt.liftOpt_opt, ``Qed.Server.SrvLiftOpt.liftOpt_val]

private def arrayCoreSimpNames : Array Name :=
  #[``Array.size_set, ``Array.size_push, ``Array.getElem_set_self] ++ dictSimpNames

private def stepCombSimpNames : Array Name := #[
  ``Qed.Server.srvSeq_none, ``Qed.Server.srvSeq_some,
  ``Qed.Server.srvEmitSeq_none, ``Qed.Server.srvEmitSeq_some,
  ``Qed.Server.srvFinish_ok, ``Qed.Server.srvFinish_err, ``Qed.Server.srvFinish_none,
  ``Qed.Server.srvFinishEmit_ok, ``Qed.Server.srvFinishEmit_err, ``Qed.Server.srvFinishEmit_none,
  ``Qed.Server.srvAtomicCommit_none, ``Qed.Server.srvAtomicCommit_ok, ``Qed.Server.srvAtomicCommit_err,
  ``Qed.Server.srvAtomicCommitEmit_none, ``Qed.Server.srvAtomicCommitEmit_ok, ``Qed.Server.srvAtomicCommitEmit_err]

private def stepLetEqSimpNames : Array Name := #[
  ``Qed.Server.srvSeq_srvLetEq, ``Qed.Server.srvEmitSeq_srvLetEq,
  ``Qed.Server.srvFinish_srvLetEq, ``Qed.Server.srvFinishEmit_srvLetEq,
  ``Qed.Server.srvAtomicCommit_srvLetEq, ``Qed.Server.srvAtomicCommitEmit_srvLetEq,
  ``Qed.Server.srvWithNewState_srvLetEq,
  ``Qed.Server.prod_fst_srvLetEq, ``Qed.Server.prod_snd_srvLetEq]

private def ensPostSimpNames : Array Name := #[
  ``Qed.Server.srvEnsPost_ok, ``Qed.Server.srvEnsPost_err, ``Qed.Server.srvEnsPost_srvLetEq,
  ``Qed.Server.srvEnsPostOpt_some, ``Qed.Server.srvEnsPostOpt_none, ``Qed.Server.srvEnsPostOpt_err,
  ``Qed.Server.srvEnsPostOpt_srvLetEq, ``Qed.Server.srvEnsPostOpt_ok_iff]

private def threadProgBindSimpNames : Array Name := #[
  ``Qed.Server.threadProg_pure_bind, ``Qed.Server.threadProg_pure_bind', ``Qed.Server.threadProg_bind_assoc]

private def dsimpCodecUnfoldNames : Array Name :=
  #[``Qed.Lang.QedVal.val, ``Qed.Server.SrvIdx.toNat,
    ``Qed.Server.SrvLiftOpt.liftOpt, ``Qed.Server.srvGetAt] ++ optCodecSimpNames

private def arrayAndBoolSimpNames : Array Name :=
  #[``id_eq, ``ne_eq, ``Array.size_modify, ``Qed.Server.srvDiteFalse_eq_true, ``Qed.Server.srvDiteFalse_eq_false] ++
  valUnwrapSimpNames ++ arrayCoreSimpNames ++ boolSimpNames

private def boundsTgtSimpNames : Array Name :=
  #[``id_eq, ``Array.size_set, ``Array.size_push, ``Array.size_modify] ++ valUnwrapSimpNames

private def boundsHypSimpNames : Array Name :=
  #[``id_eq, ``ne_eq, ``Qed.Lang.not_qedAndProp, ``Qed.Lang.not_qedOrProp] ++ valUnwrapSimpNames ++ boolSimpNames

private def hypSimpEachNames : Array Name :=
  #[``id_eq, ``ne_eq, ``Prod.mk.injEq, ``Option.some.injEq, ``Except.ok.injEq, ``Except.error.injEq,
    ``reduceCtorEq, ``Qed.Lang.not_qedAndProp, ``Qed.Lang.not_qedOrProp,
    ``Qed.Server.srvDiteFalse_eq_true, ``Qed.Server.srvDiteFalse_eq_false,
    ``Qed.Server.srvUnwrap_srvFailure_ok_iff, ``Qed.Server.srvUnwrap_str_ok_iff, ``Qed.Server.srvUnwrap_opt_ok_iff] ++
  valUnwrapSimpNames ++ liftOptSimpNames ++ optCodecSimpNames ++ arrayCoreSimpNames ++ boolSimpNames

private def tgtSimpEachNames : Array Name :=
  #[``id_eq, ``ne_eq, ``Array.forall_push, ``Array.sumBy_empty, ``Array.sumBy_push] ++
  stepCombSimpNames ++ valUnwrapSimpNames ++ liftOptSimpNames ++ arrayCoreSimpNames ++ boolSimpNames

private def postRwSimpNames : Array Name :=
  #[``Array.sumBy_empty, ``Array.sumBy_push] ++ arrayCoreSimpNames ++ valUnwrapSimpNames ++ liftOptSimpNames

private def stepFixedSimpNames : Array Name :=
  #[``Qed.Server.srvUnwrap_srvFailure_ok_iff, ``Qed.Server.srvUnwrap_str_ok_iff, ``Qed.Server.srvUnwrap_opt_ok_iff] ++
  stepCombSimpNames ++ stepLetEqSimpNames ++ ensPostSimpNames ++ valUnwrapSimpNames ++ liftOptSimpNames

private def asyncInitSimpNames : Array Name :=
  #[``Qed.Server.srvFinishM, ``Qed.Server.srvSeqM, ``Qed.Server.dbRunTx]

private def asyncDsimpNames : Array Name :=
  #[``Qed.Server.srvSeqM, ``Qed.Server.dbRunTx, ``Qed.Server.SrvUnwrap.unwrap,
    ``Qed.Server.SrvErr.ofApi, ``Qed.Server.SrvUnwrapOpt.unwrapOpt]

private def asyncNormSimpNames : Array Name :=
  stepCombSimpNames ++ stepLetEqSimpNames ++ ensPostSimpNames ++ threadProgBindSimpNames

private def rpcReqSimpNames : Array Name :=
  #[``Option.isSome_iff_ne_none, ``ne_eq, `Qed.Cached.all, `Qed.Resource.all] ++
  boolSimpNames ++ valUnwrapSimpNames ++ optCodecSimpNames

/-! ## Server-Specific Control-Flow Guard & Proof-Fact Collection -/

private def isSrvEqDecl (decl : LocalDecl) : Bool :=
  !decl.userName.hasMacroScopes &&
    let u := decl.userName.toString
    u.startsWith "_srvEq" || u.startsWith "_hLet"

/-- Collects all closed subterms of type `Qed.Field _`, `Qed.Ensured _`, or `Fin _` from `extraExprs`
    and local hypotheses so `omega` automatically sees `.ok` field refinements and `.isLt` index bounds. -/
def collectProofFacts (extraExprs : Array Expr) : TermElabM (Array Expr) :=
  liftMetaM <| collectFacts {
    scanLCtx := true
    scanLCtxValues := true
    includeMacroPropHyps := true
    includeFin := true
    skipDecl := fun d _ => isSrvEqDecl d
  } extraExprs

private def hasUnsteppedCtrlFlow (e : Expr) : Bool :=
  e.getUsedConstants.any fun c =>
    c == ``Qed.Server.srvLetEq || c == ``Qed.Server.srvFinish ||
    c == ``Qed.Server.srvFinishEmit || c == ``Qed.Server.srvSeq ||
    c == ``Qed.Server.srvEmitSeq || c == ``Qed.Server.srvAtomicCommit ||
    c == ``Qed.Server.srvAtomicCommitEmit || c == ``Qed.Server.srvEnsPost ||
    c == ``Qed.Server.srvEnsPostOpt || c == ``ite || c == ``dite

private def tryCloseSrvTrivial (g : MVarId) : MetaM Bool :=
  tryCloseTrivial g hasUnsteppedCtrlFlow

private def tryCloseSrvBasic (g : MVarId) : MetaM Bool :=
  tryCloseBasic g hasUnsteppedCtrlFlow

/-! ## Helper Unfolding & Hypothesis Simplification -/

private def unfoldSrvHelpersExpr (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun sub => do
    let fn := sub.getAppFn
    if sub.isAppOfArity ``id 2 then
      return .visit (sub.getAppArgs[1]!)
    if fn.isConstOf ``srvGetAt || fn.isConstOf ``Qed.Lang.QedVal.val ||
       fn.isConstOf ``SrvIdx.toNat || fn.isConstOf ``SrvLiftOpt.liftOpt then
      if let some u ← (do if let some x ← unfoldProjInst? sub then pure (some x) else unfoldDefinition? sub) then
        return .visit (if u.isAppOfArity ``id 2 then u.getAppArgs[1]! else u)
    return .continue)

private def hasSrvHelperConst (e : Expr) : Bool :=
  e.getUsedConstants.any fun c =>
    c == ``srvGetAt || c == ``Qed.Lang.QedVal.val || c == ``SrvIdx.toNat ||
    c == ``SrvLiftOpt.liftOpt || c == ``id

private def isUserDecl (decl : LocalDecl) : Bool :=
  !decl.isImplementationDetail && !decl.isLet

private def goalType (g : MVarId) : MetaM Expr :=
  g.withContext do instantiateMVars (← g.getType)

private def dsimpTargetOnly (g : MVarId) : MetaM (Option MVarId) := do
  simpGoalOnly g (← mkEmptyDsimpCtx) #[] #[] true true

private def maybeEnsureType (expectedType? : Option Expr) (e : Expr) : TermElabM Expr :=
  match expectedType? with
  | some expTy => ensureHasType expTy e
  | none       => return e

private def nextFreshSrvName (g : MVarId) (pfx : String) (startIdx : Nat) : MetaM (Name × Nat) := do
  let lctx ← g.withContext getLCtx
  let mut i := startIdx
  let mut cand := Name.mkSimple s!"{pfx}{i}"
  while lctx.any (·.userName == cand) do
    i := i + 1
    cand := Name.mkSimple s!"{pfx}{i}"
  return (cand, i + 1)

private def maybeRenameMacro (g : MVarId) (decl : LocalDecl) (pfx : String) (idx : Nat) :
    MetaM (MVarId × Nat) := do
  if !decl.userName.hasMacroScopes then return (g, idx)
  let (cand, nxt) ← nextFreshSrvName g pfx idx
  return (← g.rename decl.fvarId cand, nxt)

private def unfoldSrvHelpersGoal (g0 : MVarId) : MetaM MVarId := do
  let mut g := g0
  let lctx0 ← g.withContext getLCtx
  let mut hIdx : Nat := lctx0.size
  let mut propFVars : Array FVarId := #[]
  for decl in lctx0 do
    if isUserDecl decl && !isSrvEqDecl decl then
      let ty ← g.withContext (instantiateMVars decl.type)
      if (← g.withContext (try isProp ty catch _ => pure false)) then
        let (g', nxt) ← maybeRenameMacro g decl "_srvSplitH" hIdx
        g := g'; hIdx := nxt
        if hasSrvHelperConst ty then propFVars := propFVars.push decl.fvarId
  for revIdx in [0:propFVars.size] do
    let fv := propFVars[propFVars.size - 1 - revIdx]!
    if let some decl := (← g.withContext getLCtx).find? fv then
      let ty ← g.withContext (instantiateMVars decl.type)
      if hasSrvHelperConst ty then
        let ty' ← g.withContext (unfoldSrvHelpersExpr ty)
        if ty' != ty then
          if (← goalType g).containsFVar fv then
            let (cand, nxt) ← nextFreshSrvName g "_srvFreeH" hIdx
            hIdx := nxt
            g := (← (← g.assert cand ty' (mkFVar fv)).intro1P).2
          g ← tryGoalM g (·.changeLocalDecl fv ty')
  let tgt ← goalType g
  if hasSrvHelperConst tgt then
    let tgt' ← g.withContext (unfoldSrvHelpersExpr tgt)
    if tgt' != tgt then g ← tryGoalM g (·.change tgt')
  return g

private def filterUserDecls (g : MVarId) (p : LocalDecl → MetaM Bool) : MetaM (Array FVarId) := do
  let mut fvs : Array FVarId := #[]
  for decl in (← g.withContext getLCtx) do
    if isUserDecl decl && (← g.withContext (p decl)) then
      fvs := fvs.push decl.fvarId
  return fvs

private def simpHypsEachGoal (g0 : MVarId) : MetaM (Option MVarId) := do
  let hFVars ← filterUserDecls g0 fun decl => do
    if decl.userName.hasMacroScopes || isSrvEqDecl decl then return false
    try isProp decl.type catch _ => pure false
  let mut g := g0
  if !hFVars.isEmpty then
    let (hypCtx, _) ← mkCachedSimpCtx "hypSimpEach" hypSimpEachNames
    let s ← saveState
    let batchRes ← try
        some <$> (match (← simpGoal g hypCtx #[] none false hFVars).1 with
          | none => pure none
          | some (_, g') => pure (some g'))
      catch _ => restoreState s; pure none
    match batchRes with
    | some none      => return none
    | some (some g') => g := g'
    | none =>
        for fv in hFVars do
          match ← simpGoalOnly g hypCtx #[] #[fv] false false with
          | none    => return none
          | some g' => g := g'
  let (tgtCtx, _) ← mkCachedSimpCtx "tgtSimpEach" tgtSimpEachNames
  simpGoalOnly g tgtCtx

/-! ## Custom Term Elaborators (`srvAutoField`, `srvAutoEmit`, `srvTypedAs`, `srvGetElem`, `srvSetElem`) -/

private def exprHasLetFVar (lctx : LocalContext) (e : Expr) : Bool :=
  e.hasAnyFVar fun fvid => (lctx.find? fvid).any (·.isLet)

private def isTinyProofExpr (e : Expr) : Bool :=
  let e := e.consumeMData
  if e.isFVar || e.isConst then true
  else match e.getAppFn.constName?, e.getAppNumArgs with
  | some ``Eq.refl, 2 | some ``of_decide_eq_true, 3 | some ``Nat.le_refl, 1
  | some `Qed.Field.ok, 3 | some `Qed.Ensured.ok, 3 | some ``Fin.isLt, 2 => true
  | _, _ => false

private def wrapAuxProof (goalProp prf : Expr) : TermElabM Expr := do
  let prf ← instantiateMVars prf
  let goalProp ← instantiateMVars goalProp
  if prf.hasMVar || goalProp.hasMVar || isTinyProofExpr prf then return prf
  let lctx ← getLCtx
  if exprHasLetFVar lctx goalProp || exprHasLetFVar lctx prf then return prf
  liftMetaM <| Meta.mkAuxTheorem goalProp prf (zetaDelta := false)

private def proveGoalWithMeta (facts : Array Expr) (goalProp : Expr)
    (solver : MVarId → Array FVarId → MetaM Bool) : TermElabM (Option Expr) := do
  let s ← saveState
  try
    let mvar ← mkFreshExprMVar goalProp
    let (g, factFVars) ← assertFacts mvar.mvarId! "_srvFact" facts
    if ← solver g factFVars then
      let prf ← instantiateMVars mvar
      unless prf.hasMVar do return some prf
    restoreState s
    return none
  catch _ =>
    restoreState s
    return none

private def dsimpCodecGoal (g : MVarId) : MetaM (Option MVarId) := do
  let (dcCtx, _) ← mkCachedSimpCtx "dsimpCodec" dsimpCodecUnfoldNames { zetaDelta := false } #[] true
  simpGoalOnly g dcCtx #[] #[] true true

private def dsimpCodecAndStrLen (g0 : MVarId) : MetaM (Option MVarId) := do
  let some g1 ← dsimpCodecGoal g0 | return none
  let (strCtx, strSp) ← mkCachedSimpCtx "strLenOnly" #[] { zetaDelta := false } strLenSP
  simpGoalOnly g1 strCtx strSp

private def solveRefinementSlow (g0 : MVarId) : MetaM Bool := do
  let g ← tryGoalM g0 unfoldSrvHelpersGoal
  let some g ← tryGoalOptM g simpHypsEachGoal | return true
  let (refCtx, sp) ← mkCachedSimpCtx "slowRefinement"
    (#[``id_eq, ``ne_eq] ++ valUnwrapSimpNames ++ arrayCoreSimpNames ++ boolSimpNames)
    { zetaDelta := false } strLenSP
  let some g ← simpGoalOnly g refCtx sp | return true
  let some g ← dsimpCodecAndStrLen g | return true
  if ← tryCloseSrvBasic g then return true
  let saCtx ← mkSimpCtxWithBase valUnwrapBaseNames
  let some g' ← trySimpAll g saCtx sp | return true
  tryCloseSrvBasic g'

private def solveAutoFieldFast (isLit : Bool) (g0 : MVarId) (factFVars : Array FVarId) : MetaM Bool := do
  if isLit && factFVars.isEmpty then
    let (litCtx, sp) ← mkCachedSimpCtx "litField" (#[``id_eq, ``Qed.Lang.QedVal.val_id] ++ optCodecSimpNames)
      { zetaDelta := false } strLenSP
    let some g ← simpGoalOnly g0 litCtx sp | return true
    return ← tryCloseSrvBasic g
  let (ffCtx, sp) ← mkCachedSimpCtx "fastField" (#[``id_eq] ++ valUnwrapSimpNames ++ optCodecSimpNames)
    { zetaDelta := false } strLenSP
  let some g ← simpGoalOnly g0 ffCtx sp factFVars true false | return true
  if ← tryCloseSrvBasic g then return true
  let some g ← dsimpCodecAndStrLen g | return true
  tryCloseSrvBasic g

private def throwFieldRuleFailed (stx : Syntax) (predFn valExpr : Expr) : TermElabM α := do
  let mut p := predFn.consumeMData
  if p.isAppOfArity `Qed.Codec.valid 2 then
    let mut c := (p.getArg! 1).consumeMData
    while c.isAppOfArity `Qed.Codec.jsonOnly 2 do c := (c.getArg! 1).consumeMData
    if c.isAppOfArity `Qed.Codec.refine 4 then p := c.getArg! 2
  let prettyGoal ← Qed.Diag.ppQedExpr ((Expr.app p valExpr).headBeta)
  let prettyVal ← Qed.Diag.ppQedExpr valExpr
  throwErrorAt stx m!"Schema field rule `{prettyGoal}` failed for `{prettyVal}`.\n\n\
    Hint: Guard this value with `if ...:` or a `requires` precondition so it satisfies the schema's `where` rule."

@[term_elab srvAutoFieldStx]
def elabSrvAutoField : TermElab := fun stx expectedType? => do
  let valStx : Term := ⟨(stx.getArg 1)⟩
  if let some expTy := expectedType? then
    let expTy ← instantiateMVars expTy
    if !expTy.getAppFn.isMVar then
      let expWhnf ← whnf expTy
      if expWhnf.isAppOfArity ``Qed.Field 2 then
        let args := expWhnf.getAppArgs
        let innerTy := args[0]!; let predFn := args[1]!
        let valExpr ← elabTermEnsuringType valStx (some innerTy)
        synthesizeSyntheticMVarsNoPostponing
        let valExpr ← instantiateMVars valExpr
        let goalProp := mkApp predFn valExpr
        let isLit := valExpr.isLit || (valExpr.getAppFn.isConstOf ``OfNat.ofNat && !valExpr.hasFVar)
        let localFacts ← if isLit then pure #[] else
          liftMetaM <| collectFacts { scanLCtx := false, includeFin := true } #[valExpr]
        let mut prf? ← proveGoalWithMeta localFacts goalProp (solveAutoFieldFast isLit)
        if prf?.isNone then
          prf? ← proveGoalWithMeta (← collectProofFacts #[valExpr]) goalProp (fun g _ => solveRefinementSlow g)
        let some prfExpr := prf? | throwFieldRuleFailed stx predFn valExpr
        return ← mkAppOptM ``Qed.Field.mk #[some innerTy, some predFn, some valExpr, some (← wrapAuxProof goalProp prfExpr)]
      else
        return ← try elabTermEnsuringType valStx (some expTy)
                 catch _ => elabTermEnsuringType (← `(Qed.Lang.QedVal.val $valStx)) (some expTy)
  let e ← elabTerm valStx none
  synthesizeSyntheticMVars (postpone := .yes)
  let ty ← whnf (← instantiateMVars (← inferType e))
  let e ← if ty.isAppOfArity ``Qed.Field 2 then mkAppM ``Qed.Field.val #[e] else pure e
  maybeEnsureType expectedType? e

@[term_elab srvAutoEmitStx]
def elabSrvAutoEmit : TermElab := fun stx expectedType? => do
  let propExpr ← match expectedType? with
    | some expTy => instantiateMVars expTy
    | none       => elabTerm (stx.getArg 1) (some (mkSort Level.zero))
  let facts ← collectProofFacts #[propExpr]
  let some prfExpr ← proveGoalWithMeta facts propExpr (fun g _ => solveRefinementSlow g)
    | do
        let prettyGoal ← Qed.Diag.ppQedExpr ((← unfoldDefinition? propExpr).getD propExpr)
        throwErrorAt stx m!"Channel `ensures` postcondition failed at `emit`:\n  • must satisfy:  {prettyGoal}\n\n\
          Hint: Ensure the emitted event satisfies the channel's `ensures` clause."
  wrapAuxProof propExpr prfExpr

@[term_elab srvTypedAsStx]
def elabSrvTypedAs : TermElab := fun stx expectedType? => do
  let tplExpr ← elabTerm (stx.getArg 1) none
  synthesizeSyntheticMVarsNoPostponing
  let valExpr ← elabTermEnsuringType (stx.getArg 3) (some (← instantiateMVars (← inferType tplExpr)))
  maybeEnsureType expectedType? valExpr

/-! ## Bounds Checking (`srvGetElem`, `srvSetElem`) — O(N) Size-Chain Fast Path -/

private def unwrapSizeSet? (e : Expr) : Nat → MetaM (Option (Expr × Expr))
  | 0 => return none
  | fuel + 1 => do
      let eC := e.consumeMData
      if eC.isAppOfArity ``Array.set 5 then
        let setArgs := eC.getAppArgs
        let eqSet ← mkAppOptM ``Array.size_set
          #[some setArgs[0]!, some setArgs[1]!, some setArgs[2]!, some setArgs[3]!, some setArgs[4]!]
        return some (setArgs[1]!, eqSet)
      else if eC.isAppOfArity ``srvLetEq 4 then
        let lArgs := eC.getAppArgs
        unwrapSizeSet? (mkApp2 lArgs[3]! lArgs[2]! (← mkEqRefl lArgs[2]!)).headBeta fuel
      else return none

private def proveSizeEqChain (lctx : LocalContext) (startArr : Expr) : MetaM (Expr × Option Expr) := do
  let mut cur := startArr
  let mut eqOpt? : Option Expr := none
  let mut seen : Array FVarId := #[]
  for _ in [0:lctx.size] do
    let Expr.fvar fv := cur.consumeMData | break
    if seen.contains fv then break
    seen := seen.push fv
    let mut next? : Option (Expr × Expr) := none
    for decl in lctx do
      if isUserDecl decl then
        if let some (_, lhs, rhs) := (← instantiateMVars decl.type).eq? then
          if lhs.consumeMData == Expr.fvar fv then
            let rhsC := rhs.consumeMData
            let arrTy ← whnf (← inferType cur)
            let elemTy := if arrTy.isAppOfArity ``Array 1 then arrTy.getAppArgs[0]! else mkConst ``Unit
            let mkSizeCongr := do mkAppM ``congrArg #[← mkAppOptM ``Array.size #[some elemTy], decl.toExpr]
            if let some (prevArr, eqSet) ← try unwrapSizeSet? rhsC 8 catch _ => pure none then
              next? := some (prevArr, ← mkEqSymm (← mkEqTrans (← mkSizeCongr) eqSet))
              break
            else if !rhsC.containsFVar fv && !(rhsC.getUsedConstants.any (· == ``srvLetEq)) then
              next? := some (rhsC, ← mkEqSymm (← mkSizeCongr))
              break
    match next? with
    | some (prevArr, prevEqCur) =>
        eqOpt? := some (← match eqOpt? with | none => pure prevEqCur | some eq => mkEqTrans prevEqCur eq)
        cur := prevArr
    | none => break
  return (cur, eqOpt?)

private def collectSizeBoundHypFVars (g : MVarId) : MetaM (Array FVarId) :=
  filterUserDecls g fun decl => do
    if decl.userName.hasMacroScopes then return false
    let ty ← instantiateMVars decl.type
    if !(← try isProp ty catch _ => pure false) then return false
    let cs := ty.getUsedConstants
    return (cs.any fun c => c == ``Array.size || c == ``LT.lt || c == ``LE.le || c == ``GE.ge || c == ``GT.gt) &&
      !(cs.any fun c => c == ``srvGetAt || c == ``RequestCtx || c == ``Array.set)

private def solveBoundsFast (g0 : MVarId) : MetaM Bool := do
  if ← tryCloseSrvTrivial g0 then return true
  let (tgtCtx, _) ← mkCachedSimpCtx "boundsTgt" boundsTgtSimpNames { zetaDelta := true }
  let some g1 ← tryGoalOptM g0 (simpGoalOnly · tgtCtx) | return true
  let mut g := g1
  let sizeFVars ← collectSizeBoundHypFVars g
  unless sizeFVars.isEmpty do
    let (hypCtx, _) ← mkCachedSimpCtx "boundsHyp" boundsHypSimpNames
    match ← tryGoalOptM g (simpGoalOnly · hypCtx #[] sizeFVars false false) with
    | none    => return true
    | some g' => g := g'
  if ← tryCloseSrvTrivial g then return true
  tryDirectOmega g

private def solveBoundsSlow (g0 : MVarId) : MetaM Bool := do
  let g ← tryGoalM g0 unfoldSrvHelpersGoal
  let dsimpAllCtx ← mkEmptyDsimpCtx { zetaDelta := true }
  let some g ← tryGoalOptM g (simpGoalAllHyps · dsimpAllCtx #[] true) | return true
  let (abCtx, _) ← mkCachedSimpCtx "arrayAndBool" arrayAndBoolSimpNames { zetaDelta := true }
  let some g ← simpGoalAllHyps g abCtx | return true
  let (g, _) ← try splitAndHypsGoal g catch _ => pure (g, false)
  if ← tryCloseSrvTrivial g then return true
  if ← tryDirectOmega g then return true
  let saCtx ← mkSimpCtxWithBase #[] { zetaDelta := true }
  let some g' ← trySimpAll g saCtx | return true
  if ← tryDirectOmega g' then return true
  let (spCtx, _) ← mkCachedSimpCtx "boundsSplitSize" #[``Array.size_set, ``Array.size_push] { zetaDelta := true }
  let rec splitLoop (fuel : Nat) (gs : List MVarId) : MetaM Bool := do
    match fuel, gs with
    | _, [] => return true
    | 0, _  => return false
    | f + 1, cur :: rest =>
        match ← trySplitTarget cur with
        | some sgs => splitLoop f (sgs ++ rest)
        | none =>
            match ← simpGoalAllHyps cur spCtx with
            | none => splitLoop f rest
            | some c' => if ← tryDirectOmega c' then splitLoop f rest else return false
  splitLoop 16 [g']

private def proveBoundsFor (ref : Syntax) (arrExpr idxNatExpr : Expr) : TermElabM Expr := do
  let goalProp ← mkAppM ``LT.lt #[idxNatExpr, ← mkAppM ``Array.size #[arrExpr]]
  let (baseArr, sizeEqOpt?) ← proveSizeEqChain (← getLCtx) arrExpr
  let baseGoalProp ← mkAppM ``LT.lt #[idxNatExpr, ← mkAppM ``Array.size #[baseArr]]
  if let some basePrf ← proveGoalWithMeta #[] baseGoalProp (fun g _ => solveBoundsFast g) then
    let prfExpr ← match sizeEqOpt? with
      | none       => pure basePrf
      | some eqPrf => mkAppM ``Nat.lt_of_lt_of_eq #[basePrf, eqPrf]
    return ← wrapAuxProof goalProp prfExpr
  let facts ← collectProofFacts #[arrExpr, idxNatExpr]
  let some prfExpr ← proveGoalWithMeta facts goalProp (fun g _ => solveBoundsSlow g)
    | do
        let prettyArr ← Qed.Diag.ppQedExpr arrExpr
        let prettyIdx ← Qed.Diag.ppQedExpr idxNatExpr
        throwErrorAt ref m!"Array index `{prettyIdx}` could be out of bounds for `{prettyArr}`:\n  • must satisfy:  {prettyIdx} < {prettyArr}.size\n\n\
          Hint: Guard this access with `if {prettyIdx} < {prettyArr}.size:`."
  wrapAuxProof goalProp prfExpr

/-- Unified elaborator for `srvGetElem` (`valStx? = none`) and `srvSetElem` (`valStx? = some v`),
    elaborating `arrStx` only once and dispatching cleanly between `Qed.Dict` and `Array`. -/
private def elabSrvArrOrDictOp (stx : Syntax) (arrStx idxStx : Term) (valStx? : Option Term)
    (expectedType? : Option Expr) : TermElabM Expr := do
  let arrExpr ← elabTerm arrStx none
  synthesizeSyntheticMVarsNoPostponing
  let arrExpr ← instantiateMVars arrExpr
  let arrTy ← whnf (← inferType arrExpr)
  if arrTy.isAppOfArity `Qed.Dict 2 then
    let dictStx ← match valStx? with
      | none        => `(Qed.Dict.get $arrStx $idxStx)
      | some valStx => `(Qed.Dict.set $arrStx $idxStx (srvAutoField($valStx)))
    return ← elabTerm dictStx expectedType?
  let opDesc := if valStx?.isSome then "indexed assignment" else "indexing"
  unless arrTy.isAppOfArity ``Array 1 do
    throwErrorAt arrStx m!"expected an array (`T[]`) for {opDesc}, got `{← ppExpr arrTy}`"
  let elemTy := arrTy.getAppArgs[0]!
  let idxNatExpr ← elabTermEnsuringType (← `(Qed.Server.SrvIdx.toNat $idxStx)) (some (mkConst ``Nat))
  let valExpr? ← valStx?.mapM fun valStx => do elabTermEnsuringType (← `(srvAutoField($valStx))) (some elemTy)
  synthesizeSyntheticMVarsNoPostponing
  let arrExpr ← instantiateMVars arrExpr
  let idxNatExpr ← instantiateMVars idxNatExpr
  let valExpr? ← valExpr?.mapM instantiateMVars
  let ltPrf ← proveBoundsFor stx arrExpr idxNatExpr
  let resExpr ← match valExpr? with
    | none         => mkAppOptM ``srvGetAt #[some elemTy, some arrExpr, some idxNatExpr, some ltPrf]
    | some valExpr => mkAppOptM ``Array.set #[some elemTy, some arrExpr, some idxNatExpr, some valExpr, some ltPrf]
  maybeEnsureType expectedType? resExpr

@[term_elab srvGetElemStx]
def elabSrvGetElem : TermElab := fun stx expectedType? =>
  elabSrvArrOrDictOp stx ⟨stx.getArg 1⟩ ⟨stx.getArg 3⟩ none expectedType?

@[term_elab srvSetElemStx]
def elabSrvSetElem : TermElab := fun stx expectedType? =>
  elabSrvArrOrDictOp stx ⟨stx.getArg 1⟩ ⟨stx.getArg 3⟩ (some ⟨stx.getArg 5⟩) expectedType?

/-! ## Automated Server Invariant Prover (`qedSrvProveStep`, `qedSrvProveAsync`) -/

private def poseInvFactsOnGoal (g0 : MVarId) : MetaM (MVarId × Array FVarId) :=
  collectAndAssertFacts g0 "_invFact" {
    includeFin := true
    includeCollectionRules := true
    rounds := 4
    skipDecl := fun decl dty =>
      isSrvEqDecl decl &&
        match dty.eq? with
        | some (_, _, rhs) => rhs.getUsedConstants.any fun c => c == ``Array.set || c == ``Array.push
        | none             => true
  }

private def finishAtomGoal (g0 : MVarId) (allowDeepFallback : Bool := true) : TacticM (Option MVarId) := do
  if ← tryCloseSrvTrivial g0 then return none
  let g ← unfoldSrvHelpersGoal g0
  let (preCtx, _) ← mkCachedSimpCtx "finishAtomPre"
    (valUnwrapSimpNames ++ liftOptSimpNames ++ #[``Array.getElem_set_self] ++ dictSimpNames)
  let some g ← simpGoalOnly g preCtx | return none
  let some g ← dsimpCodecGoal g | return none
  if ← tryCloseSrvTrivial g then return none
  if ← tryDirectOmega g then return none
  let (g, invFactFVars) ← poseInvFactsOnGoal g
  let g ← if invFactFVars.isEmpty then pure g else do
    let (codecCtx, _) ← mkCachedSimpCtx "optCodecDsimp" optCodecSimpNames { zetaDelta := false } #[] true
    let some g' ← simpGoalOnly g codecCtx #[] invFactFVars false true | return none
    pure g'
  let some g ← dsimpCodecGoal g | return none
  if ← tryCloseSrvBasic g then return none
  let (fbCtx, _) ← mkCachedSimpCtx "finishAtomFb" (valUnwrapSimpNames ++ arrayCoreSimpNames)
  let some g ← simpGoalOnly g fbCtx | return none
  if ← tryCloseSrvBasic g then return none
  if allowDeepFallback then
    if ← closeWithFallback g {
        skipTarget := hasUnsteppedCtrlFlow
        trySimpStarOmega := true
        deepExtraSimpAll := #[``Qed.Server.srvLetEq]
      } then return none
  return some g

/-! ### Dedicated O(N) Linear Passes (`elimSrvLetEqGoal`, `rewriteTargetEqsLinearGoal`, `peelArrayForallGoal`) -/

private def collectReadySrvLetEqs (e : Expr) : Nat → MetaM (Array Expr)
  | 0 => return #[]
  | fuel + 1 => do
      let e := e.consumeMData
      if e.isAppOfArity ``Qed.Server.srvLetEq 4 then
        return (if !e.hasLooseBVars then #[e] else #[]) ++ (← collectReadySrvLetEqs (e.getAppArgs[2]!) fuel)
      else if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
        collectReadySrvLetEqs (e.getAppArgs[1]!) fuel
      else match e with
        | .app f a => return (← collectReadySrvLetEqs f fuel) ++ (← collectReadySrvLetEqs a fuel)
        | .proj _ _ b => collectReadySrvLetEqs b fuel
        | .letE _ _ v _ _ => collectReadySrvLetEqs v fuel
        | .forallE _ d b _ => return (← collectReadySrvLetEqs d fuel) ++ (← collectReadySrvLetEqs b fuel)
        | _ => return #[]

private def tryPickSrvLetEq (gGoal : MVarId) (cands : Array Expr) (revCount : Nat) :
    MetaM (Option (Expr × Expr × MVarId × Nat)) := do
  let tgtNow ← goalType gGoal
  for letApp in cands do
    let s ← saveState
    let res? ← try
        gGoal.withContext do
          let args := letApp.getAppArgs
          let absBody ← Meta.kabstract tgtNow letApp
          unless absBody.hasLooseBVar 0 do return none
          let pred := Lean.mkLambda `_ BinderInfo.default args[1]! absBody
          unless (← Meta.isTypeCorrect pred) do return none
          let elimPrf ← Meta.mkAppOptM ``Qed.Server.srvLetEq_elim
            #[some args[0]!, some args[1]!, some pred, some args[2]!, some args[3]!]
          match ← try some <$> gGoal.apply elimPrf catch _ => pure none with
          | some [sg] => return some (args[3]!, absBody, sg, revCount)
          | _ => return none
      catch _ => pure none
    if res?.isSome then return res?
    restoreState s
  return none

private def finishElimSrvLetEq (kFun absBody : Expr) (newGoal : MVarId) (revertedCount : Nat) :
    MetaM MVarId := do
  let idx0 := (← newGoal.withContext getLCtx).size
  let (valName, idx1) ← nextFreshSrvName newGoal "_srvVal" idx0
  let (eqName, _) ← nextFreshSrvName newGoal "_srvEq" idx1
  let (valFVar, g1) ← newGoal.intro valName
  let (eqFVar, g2) ← g1.intro eqName
  let reducedGoal := absBody.instantiate1 (mkApp2 kFun (mkFVar valFVar) (mkFVar eqFVar)).headBeta
  let g3 ← tryGoalM g2 (·.change reducedGoal)
  if revertedCount > 0 then tryGoalM g3 fun x => Prod.snd <$> x.introN revertedCount else pure g3

private def elimSrvLetEqGoal (g : MVarId) (allowHyps : Bool := true) : MetaM (Option MVarId) := do
  let tgt ← goalType g
  let mut picked? : Option (Expr × Expr × MVarId × Nat) := none
  if tgt.getUsedConstants.any (· == ``Qed.Server.srvLetEq) then
    picked? ← tryPickSrvLetEq g (← collectReadySrvLetEqs tgt 1024) 0
  if picked?.isNone && allowHyps then
    for decl in (← g.withContext getLCtx) do
      if isUserDecl decl then
        let dty ← g.withContext (instantiateMVars decl.type)
        if dty.getUsedConstants.any (· == ``Qed.Server.srvLetEq) then
          let cands ← collectReadySrvLetEqs dty 1024
          unless cands.isEmpty do
            let s ← saveState
            let attempt? ← try
                let (reverted, gRev) ← g.revert #[decl.fvarId]
                tryPickSrvLetEq gRev cands reverted.size
              catch _ => pure none
            if attempt?.isSome then picked? := attempt?; break
            restoreState s
  let some (kFun, absBody, newGoal, revCount) := picked? | return none
  some <$> finishElimSrvLetEq kFun absBody newGoal revCount

private def elimAllSrvLetEqTarget (g0 : MVarId) : MetaM (MVarId × Bool) := do
  let mut g := g0; let mut did := false
  for _ in [0:128] do
    match ← elimSrvLetEqGoal g (allowHyps := false) with
    | some g' => g := g'; did := true
    | none    => break
  return (g, did)

private def rewriteTargetByFVar (g : MVarId) (eqFVar : FVarId) : MetaM (Option MVarId) := do
  let s ← saveState
  try
    let tgt ← goalType g
    let rwRes ← g.withContext (g.rewrite tgt (mkFVar eqFVar))
    return some (← g.replaceTargetEq rwRes.eNew rwRes.eqProof)
  catch _ => restoreState s; return none

private def mkArrCongrLemmas (elemTy lhs rhs hE : Expr) : MetaM (Expr × Expr) := do
  let sizeLhs ← mkAppM ``Array.size #[lhs]
  withLocalDecl `j .implicit (mkConst ``Nat) fun j => do
    withLocalDeclD `hj (← mkAppM ``LT.lt #[j, sizeLhs]) fun hj => do
      let p1 ← mkAppOptM ``Qed.Server.getElem_congr_arr #[some elemTy, some rhs, some lhs, some j, some hE, some hj]
      let p2 ← mkAppOptM ``Qed.Server.srvGetAt_congr_arr #[some elemTy, some rhs, some lhs, some j, some hE, some hj]
      return (← mkLambdaFVars #[j, hj] p1, ← mkLambdaFVars #[j, hj] p2)

private def rewriteTargetEqsLinearGoal (g0 : MVarId) : MetaM (Option MVarId) := do
  let mut eqDecls : Array (FVarId × Option (Expr × Expr × Expr) × FVarId) := #[]
  for decl in (← g0.withContext getLCtx) do
    if isUserDecl decl && isSrvEqDecl decl then
      if let some (eqTy, lhs, rhs) := (← g0.withContext (instantiateMVars decl.type)).eq? then
        if let .fvar fv := lhs.consumeMData then
          if !rhs.containsFVar fv then
            let arrInfo? ← g0.withContext do
              let w ← whnf eqTy
              if w.isAppOfArity ``Array 1 then return some (w.getAppArgs[0]!, lhs.consumeMData, rhs)
              else return none
            eqDecls := eqDecls.push (fv, arrInfo?, decl.fvarId)
  if eqDecls.isEmpty then return some g0
  let (postRwCtx, _) ← mkCachedSimpCtx "postRw" postRwSimpNames
  let mut g := g0
  for revIdx in [0:eqDecls.size] do
    let (fv, arrInfo?, eqFv) := eqDecls[eqDecls.size - 1 - revIdx]!
    if (← goalType g).containsFVar fv then
      let mut progressed := false
      if let some (elemTy, lhs, rhs) := arrInfo? then
        let arrCongrRes ← g.withContext do
          try
            let base ← getCachedSimpThms "arrSetSimp" #[``Array.getElem_set_self, ``Array.getElem_set]
            let (c1, c2) ← mkArrCongrLemmas elemTy lhs rhs (mkFVar eqFv)
            let st ← (← base.add (.other `arrCongr1) #[] c1).add (.other `arrCongr2) #[] c2
            let ctx ← Simp.mkContext { zetaDelta := false, failIfUnchanged := false } #[st] (← getSimpCongrTheorems)
            let sp ← getCachedSimprocs #[`reduceIte] (post := false)
            return some (ctx, sp)
          catch _ => return none
        if let some (ctx, sp) := arrCongrRes then
          match ← simpGoalOnly g ctx sp with
          | none    => return none
          | some g' => g := g'; progressed := true
        if (← goalType g).containsFVar fv then
          if let some g' ← rewriteTargetByFVar g eqFv then g := g'; progressed := true
      else if let some g' ← rewriteTargetByFVar g eqFv then g := g'; progressed := true
      if progressed then
        match ← simpGoalOnly g postRwCtx with
        | none    => return none
        | some g' => g := g'
  return some g

private theorem srv_forall_push {α : Type} {P : α → Prop} {xs : Array α} {v : α}
    (hxs : ∀ x ∈ xs, P x) (hv : P v) : ∀ x ∈ xs.push v, P x :=
  (Array.forall_push (P := P) (xs := xs) (v := v)).2 ⟨hxs, hv⟩

private def peelArrayForallGoal (g0 : MVarId) (allowDeepFallback : Bool := true) : TacticM (List MVarId) := do
  let rec loop : Nat → MVarId → TacticM (List MVarId)
    | 0, g => return [g]
    | fuel + 1, g => do
        let some g ← dsimpTargetOnly g | return []
        if ← tryCloseSrvTrivial g then return []
        let some arrExpr := extractForEachColl? (← goalType g) | return [g]
        for (ctor, arity, lem) in #[(``Array.set, 5, ``Array.forall_set), (``Array.push, 3, ``srv_forall_push)] do
          if arrExpr.isAppOfArity ctor arity then
            if let some [gPrev, gElem] ← tryApplyConst g lem then
              let elemRem : List MVarId ← do
                let some ge1 ← dsimpTargetOnly gElem | pure []
                let some ge2 ← rewriteTargetEqsLinearGoal ge1 | pure []
                pure (← finishAtomGoal ge2 allowDeepFallback).toList
              return (← loop fuel gPrev) ++ elemRem
        if let .fvar fv := arrExpr then
          let lctx ← g.withContext getLCtx
          let eqFv? := (← lctx.foldlM (init := none) fun acc decl => do
            if acc.isSome || !isUserDecl decl || decl.userName.hasMacroScopes then return acc
            if let some (_, lhs, _) := (← g.withContext (instantiateMVars decl.type)).eq? then
              if lhs.consumeMData == .fvar fv then return some decl.fvarId
            return none)
          if let some eqFv := eqFv? then
            if let some g' ← rewriteTargetByFVar g eqFv then
              return ← loop fuel g'
        if ← g.assumptionCore then return []
        return [g]
  loop 128 g0

private def substMatchEqHypsGoal (g0 : MVarId) : MetaM MVarId := do
  let mut g := g0
  for _ in [0:16] do
    let lctx ← g.withContext getLCtx
    let mut substGoal? : Option MVarId := none
    let trySubstSide (declFv : FVarId) (varSide otherSide : Expr) (allowNonMacro symm : Bool) :
        MetaM (Option MVarId) := do
      let .fvar fv := varSide.consumeMData | return none
      let fvMacro := (lctx.find? fv).map (·.userName.hasMacroScopes) |>.getD false
      unless fv != declFv && !otherSide.containsFVar fv && (fvMacro || allowNonMacro) do return none
      let sSub ← saveState
      g.withContext do
        try some <$> (Prod.snd <$> Meta.substCore g declFv (symm := symm))
        catch _ => restoreState sSub; pure none
    for decl in lctx do
      if substGoal?.isNone && isUserDecl decl then
        let uname := decl.userName.toString
        if uname.startsWith "_srvMatchEq" || uname.startsWith "_srvSplitH" then
          if let some (_, lhs, rhs) := (← g.withContext (instantiateMVars decl.type)).eq? then
            substGoal? ← trySubstSide decl.fvarId rhs lhs (uname.startsWith "_srvMatchEq") true
            if substGoal?.isNone then
              substGoal? ← trySubstSide decl.fvarId lhs rhs false false
    match substGoal? with
    | some g' => g := g'
    | none    => break
  return g

private def closeLeafGoal (g0 : MVarId) (allowDeepFallback : Bool := true) : TacticM (List MVarId) := do
  let simpWithNewState (g : MVarId) : MetaM (Option MVarId) := do
    if (← goalType g).consumeMData.isAppOf ``Qed.Server.srvWithNewState then
      let (wCtx, _) ← mkCachedSimpCtx "withNewState" #[``Qed.Server.srvWithNewState_apply]
      simpGoalOnly g wCtx
    else pure (some g)
  let some g ← simpWithNewState g0 | return []
  if ← tryCloseSrvTrivial g then return []
  let some g ← dsimpTargetOnly g | return []
  if ← tryCloseSrvTrivial g then return []
  let g ← tryGoalM g unfoldSrvHelpersGoal
  let (g, _) ← splitAndHypsGoal g
  let some g ← tryGoalOptM g simpHypsEachGoal | return []
  let g ← substMatchEqHypsGoal g
  let some g ← simpWithNewState g | return []
  let some g ← dsimpTargetOnly g | return []
  let some g ← dsimpCodecGoal g | return []
  if ← tryCloseSrvTrivial g then return []
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
        if let some fg ← finishAtomGoal rg allowDeepFallback then
          rem := rem ++ [fg]
  return rem

private def exprHasSplittable (e : Expr) : Bool :=
  e.getUsedConstants.any fun c => c == ``ite || c == ``dite || c.toString.contains ".match_"

private def splitEqHypGoal (g0 : MVarId) : MetaM (Option (List MVarId)) := do
  let lctx ← g0.withContext getLCtx
  let mut idx := lctx.size
  let mut gCur := g0
  let mut eqFVars : Array FVarId := #[]
  for decl in lctx do
    if isUserDecl decl then
      let ty ← gCur.withContext (instantiateMVars decl.type)
      if ty.isEq && exprHasSplittable ty then
        let (g', nxt) ← maybeRenameMacro gCur decl "_srvMatchEq" idx
        gCur := g'; idx := nxt
        eqFVars := eqFVars.push decl.fvarId
  for fv in eqFVars do
    if let some sgs ← trySplitLocalDecl gCur fv then return some sgs
  return none

private def goalHasSplittableHyp (g : MVarId) : MetaM Bool := do
  for decl in (← g.withContext getLCtx) do
    if isUserDecl decl then
      let ty ← g.withContext (instantiateMVars decl.type)
      if ty.getUsedConstants.any (· == ``Qed.Server.srvLetEq) || (ty.isEq && exprHasSplittable ty) then
        return true
  return false

private def proveStepSingleGoal (g0 : MVarId) (allStepCtx stepFloatCtx : Simp.Context) :
    TacticM (List MVarId) := do
  let (_, g1) ← g0.intros
  let some g2 ← simpGoalAllHyps g1 allStepCtx | return []
  let rec stepTargetLoop : Nat → List MVarId → TacticM (List MVarId)
    | 0, gs => return gs
    | _, [] => return []
    | fuel + 1, g :: rest => do
        if ← tryCloseSrvTrivial g then return ← stepTargetLoop fuel rest
        let pushSimp (g' : MVarId) := do stepTargetLoop fuel ((← simpGoalOnly g' stepFloatCtx).toList ++ rest)
        let (gLet, didLet) ← elimAllSrvLetEqTarget g
        if didLet then return ← pushSimp gLet
        match ← trySplitTarget g with
        | some sgs =>
            return ← stepTargetLoop fuel ((← sgs.filterMapM (simpGoalOnly · stepFloatCtx)) ++ rest)
        | none =>
            if ← goalHasSplittableHyp g then
              let s ← saveState
              if (← closeLeafGoal g (allowDeepFallback := false)).isEmpty then
                return ← stepTargetLoop fuel rest
              restoreState s
              if let some gHypLet ← elimSrvLetEqGoal g (allowHyps := true) then
                return ← pushSimp gHypLet
              if let some eqSgs ← splitEqHypGoal g then
                return ← stepTargetLoop fuel ((← eqSgs.filterMapM (simpGoalAllHyps · stepFloatCtx)) ++ rest)
            return (← closeLeafGoal g (allowDeepFallback := true)) ++ (← stepTargetLoop fuel rest)
  stepTargetLoop 256 [g2]

private def throwStepFailure (rem : List MVarId) (fnStr lbl : String) : TacticM Unit := do
  let (hdr, hint) : MessageData × String :=
    if lbl.startsWith "ensures:" then
      let postStr := (lbl.drop 8).toString.trimAscii.toString
      (m!"Server postcondition `ensures {postStr}` failed in `{fnStr}`:",
       s!"Ensure every successful return path establishes `{postStr}`.")
    else if lbl.startsWith "init:" then
      let invStr := (lbl.drop 5).toString.trimAscii.toString
      (m!"Server invariant `{invStr}` failed on initial state:",
       s!"Update the initial `state` values so they satisfy `{invStr}`.")
    else if lbl.startsWith "mutating:" then
      let invName := (lbl.drop 9).toString.trimAscii.toString
      (m!"Server invariant `{invName}` failed in `{fnStr}`:",
       "Add a matching `requires` clause or guard mutations of that field with `if ...:`.")
    else
      (m!"Server invariant `{lbl}` failed in `{fnStr}`:",
       "Guard state mutations with `if ...:` or `requires ...` so this invariant holds across every branch.")
  Qed.Diag.throwUnsolvedGoals hdr m!"\n\nHint: {hint}"
    (maxShown? := some 1) (moreLabel := "obligation(s)") (goals? := some rem)

private def runProveStepOnGoals (gs : List MVarId) (userNames : Array Name) (fnStr lbl : String) :
    TacticM Unit := do
  let allStepCtx ← mkDynamicSimpCtx userNames (some ("stepFixed", stepFixedSimpNames))
  let mut rem : List MVarId := []
  for g in gs do
    rem := rem ++ (← proveStepSingleGoal g allStepCtx allStepCtx)
  setGoals rem
  unless rem.isEmpty do
    throwStepFailure rem fnStr lbl

elab_rules : tactic
  | `(tactic| qedSrvProveStep [$[$unfoldIds:ident],*] $fnLabel:str $invLabel:str) => do
      let userNames ← unfoldIds.mapM fun id => resolveGlobalConstNoOverload id
      runProveStepOnGoals (← getGoals) userNames fnLabel.getString invLabel.getString

/-! ## Unified AST-Directed Async Prover (`qedSrvProveAsync`, `qedSrvProveAsyncEnsures`) -/

private def normAsyncContGoal (g0 : MVarId) (dCtx sCtx : Simp.Context) : MetaM (Option MVarId) := do
  let some g1 ← tryGoalOptM g0 (simpGoalOnly · dCtx #[] #[] true true) | return none
  tryGoalOptM g1 (simpGoalOnly · sCtx)

private def initAsyncGoal (g0 : MVarId) (handlerConst : Name) (dCtx sCtx : Simp.Context) :
    MetaM (Option MVarId) := do
  let (_, g1) ← g0.intros
  let unfoldCtx ← mkDynamicSimpCtx #[handlerConst] (some ("asyncInit", asyncInitSimpNames))
  let some g2 ← tryGoalOptM g1 (simpGoalOnly · unfoldCtx) | return none
  normAsyncContGoal g2 dCtx sCtx

private def tryCloseConstMutInv (g0 : MVarId) : TacticM (Option MVarId) := do
  let (_, g1) ← g0.intros
  let tgtC := (← goalType g1).consumeMData
  if tgtC.isAppOfArity ``Qed.Server.ProgPreservesStepRel 5 then
    if let .lam _ _ (.lam _ _ body _) _ := tgtC.getAppArgs[3]!.consumeMData then
      if body.isAppOfArity ``Or 2 && !body.getAppArgs[1]!.hasLooseBVars then
        let s ← saveState
        try
          let [gH] ← g1.applyConst ``Qed.Server.progPreservesStepRel_of_const | restoreState s; return some g1
          let (_, gH2) ← gH.introN 2
          let [gR] ← gH2.applyConst ``Or.inr | restoreState s; return some g1
          if (← closeLeafGoal gR).isEmpty then return none
          restoreState s
        catch _ => restoreState s
  return some g1

private def normAndPushCont (g : MVarId) (introN : Nat) (dCtx sCtx : Simp.Context) :
    MetaM (List MVarId) := do
  let (_, g1) ← if introN == 0 then pure (#[], g) else g.introN introN
  return match ← normAsyncContGoal g1 dCtx sCtx with | none => [] | some c => [c]

private def normSplitGoals (sgs : List MVarId) (dCtx sCtx : Simp.Context) : MetaM (List MVarId) :=
  sgs.filterMapM (normAsyncContGoal · dCtx sCtx)

/-- Parameterization unifying `ProgPreservesStepRel`/`ProgPreservesInv` and `ProgEnsures` AST stepping. -/
private structure AsyncStepSpec where
  isPreserves : Bool
  pureThreadLem : Name
  pureClassLem : Name
  bindAtomicLem : Name
  bindAtomicReadLem : Name
  bindSafeIOLem : Name
  atomicContIntros : Nat
  singleAtomicLem : Name
  singleAtomicReadLem : Name

private def preservesAsyncSpec : AsyncStepSpec := {
  isPreserves := true
  pureThreadLem := ``Qed.Server.ProgPreservesStepRel.pure
  pureClassLem := ``Qed.Server.ProgPreservesStepRel.pure
  bindAtomicLem := ``Qed.Server.runAtomic_bind_preservesStepRel
  bindAtomicReadLem := ``Qed.Server.runAtomicRead_bind_preservesStepRel
  bindSafeIOLem := ``Qed.Server.safeIO_bind_preservesStepRel
  atomicContIntros := 1
  singleAtomicLem := ``Qed.Server.progPreservesStepRel_runAtomic
  singleAtomicReadLem := ``Qed.Server.progPreservesStepRel_runAtomicRead
}

private def ensuresAsyncSpec : AsyncStepSpec := {
  isPreserves := false
  pureThreadLem := ``Qed.Server.ProgEnsures.pure
  pureClassLem := ``Qed.Server.progEnsures_pure
  bindAtomicLem := ``Qed.Server.runAtomic_bind_ensures
  bindAtomicReadLem := ``Qed.Server.runAtomicRead_bind_ensures
  bindSafeIOLem := ``Qed.Server.safeIO_bind_ensures
  atomicContIntros := 2
  singleAtomicLem := ``Qed.Server.progEnsures_runAtomic
  singleAtomicReadLem := ``Qed.Server.progEnsures_runAtomicRead
}

private def stepAsyncLoop (spec : AsyncStepSpec) (dCtx sCtx : Simp.Context) (gInit : MVarId) :
    MetaM (List MVarId) := do
  let rec loop : Nat → List MVarId → MetaM (List MVarId)
    | 0, gs => return gs
    | _, [] => return []
    | fuel + 1, g :: rest => do
        let tgtC := (← goalType g).consumeMData
        let prog? : Option Expr :=
          if spec.isPreserves then
            if tgtC.isAppOfArity ``Qed.Server.ProgPreservesStepRel 5 then some tgtC.getAppArgs[4]!
            else if tgtC.isAppOfArity ``Qed.Server.ProgPreservesInv 4 then some tgtC.getAppArgs[3]!
            else none
          else if tgtC.isAppOfArity ``Qed.Server.ProgEnsures 5 then some tgtC.getAppArgs[4]!
          else none
        let some progRaw := prog? | return g :: (← loop fuel rest)
        let prog := progRaw.consumeMData
        -- 1. Pure
        for (head, lem) in #[(``Qed.Server.ThreadProg.pure, spec.pureThreadLem), (``Pure.pure, spec.pureClassLem)] do
          if prog.isAppOf head then
            if let some sgs ← tryApplyConst g lem then return sgs ++ (← loop fuel rest)
        -- 2. Bind
        if prog.isAppOf ``Bind.bind || prog.isAppOf ``Qed.Server.ThreadProg.bind then
          let pArg := (if prog.isAppOf ``Bind.bind then prog.getAppArgs[4]! else prog.getAppArgs[3]!).consumeMData
          let atomicLem? :=
            if pArg.isAppOf ``Qed.Server.MonadAtomic.runAtomic then some spec.bindAtomicLem
            else if pArg.isAppOf ``Qed.Server.MonadAtomic.runAtomicRead then some spec.bindAtomicReadLem
            else none
          if let some lem := atomicLem? then
            if let some (gCont :: gExtra) ← tryApplyConst g lem then
              return ← loop fuel ((← normAndPushCont gCont spec.atomicContIntros dCtx sCtx) ++ gExtra ++ rest)
          else
            if !spec.isPreserves then
              if let some [gCont] ← tryApplyConst g ``Qed.Server.safeIOEnsures_bind then
                return ← loop fuel ((← normAndPushCont gCont 2 dCtx sCtx) ++ rest)
              if exprHasSplittable pArg then
                if let some sgs ← trySplitTarget g then
                  return ← loop fuel ((← normSplitGoals sgs dCtx sCtx) ++ rest)
            if let some [gCont] ← tryApplyConst g spec.bindSafeIOLem then
              return ← loop fuel ((← normAndPushCont gCont 1 dCtx sCtx) ++ rest)
        -- 3. Single runAtomic / runAtomicRead / SafeIO
        for (head, lem) in #[(``Qed.Server.MonadAtomic.runAtomic, spec.singleAtomicLem),
                             (``Qed.Server.MonadAtomic.runAtomicRead, spec.singleAtomicReadLem)] do
          if prog.isAppOf head then
            if let some [gStep] ← tryApplyConst g lem then return gStep :: (← loop fuel rest)
        if !spec.isPreserves then
          if let some [gImp] ← tryApplyConst g ``Qed.Server.safeIOEnsures_final then
            return gImp :: (← loop fuel rest)
        -- 4. `srvLetEq`
        if prog.isAppOf ``Qed.Server.srvLetEq then
          if let some gLet ← elimSrvLetEqGoal g (allowHyps := false) then
            return ← loop fuel ((← normAndPushCont gLet 0 dCtx sCtx) ++ rest)
        -- 5. SafeIO whole program (preserves mode only)
        if spec.isPreserves && !(prog.getUsedConstants.any fun c =>
            c == ``Qed.Server.MonadAtomic.runAtomic || c == ``Qed.Server.MonadAtomic.runAtomicRead) then
          if let some [] ← tryApplyConst g ``Qed.Server.safeIO_preservesStepRel then
            return ← loop fuel rest
        -- 6. Split `ite` / `dite` / `match`
        match ← trySplitTarget g with
        | some sgs => return ← loop fuel ((← normSplitGoals sgs dCtx sCtx) ++ rest)
        | none =>
            if spec.isPreserves then
              if let some [] ← tryApplyConst g ``Qed.Server.safeIO_preservesStepRel then
                return ← loop fuel rest
            return g :: (← loop fuel rest)
  loop 256 [gInit]

private def elabAsyncProve (spec : AsyncStepSpec)
    (handlerId : Ident) (invUnfoldIds : Array Ident) (fnLabel invLabel : String) : TacticM Unit := do
  let g0 ← getMainGoal
  let g1 ← if spec.isPreserves then
    let some g' ← tryCloseConstMutInv g0 | replaceMainGoal []; return
    pure g'
  else pure g0
  let handlerConst ← resolveGlobalConstNoOverload handlerId
  let userNames ← invUnfoldIds.mapM resolveGlobalConstNoOverload
  let (dCtx, _) ← mkCachedSimpCtx "asyncDsimp" asyncDsimpNames { zetaDelta := false } #[] true
  let (sCtx, _) ← mkCachedSimpCtx "asyncNorm" asyncNormSimpNames
  let some gInit ← initAsyncGoal g1 handlerConst dCtx sCtx | replaceMainGoal []; return
  runProveStepOnGoals (← stepAsyncLoop spec dCtx sCtx gInit) userNames fnLabel invLabel

elab_rules : tactic
  | `(tactic| qedSrvProveAsync $handlerId:ident [$[$invUnfoldIds:ident],*] $fnLabel:str $invLabel:str) =>
      elabAsyncProve preservesAsyncSpec handlerId invUnfoldIds fnLabel.getString invLabel.getString
  | `(tactic| qedSrvProveAsyncEnsures $handlerId:ident [$[$invUnfoldIds:ident],*] $fnLabel:str $invLabel:str) =>
      elabAsyncProve ensuresAsyncSpec handlerId invUnfoldIds fnLabel.getString invLabel.getString

/-! ## Client RPC Precondition Prover (`qedProveRpcReq`) -/

private def closeRpcReqLeaf (g0 : MVarId) : TacticM (Option MVarId) := do
  let (g, _) ← try splitAndHypsGoal g0 catch _ => pure (g0, false)
  if ← tryCloseSrvBasic g then return none
  let closed ← closeWithFallback g {
    skipTarget := hasUnsteppedCtrlFlow
    simpAllCfg := { zetaDelta := true, zetaHave := true }
    deepExtraSimpAll := #[``Qed.Server.srvLetEq]
  }
  return if closed then none else some g

elab_rules : tactic
  | `(tactic| qedProveRpcReq) => do
      let g0 ← getMainGoal
      if ← tryCloseSrvBasic g0 then replaceMainGoal []; return
      let (g, _) ← try splitAndHypsGoal g0 catch _ => pure (g0, false)
      let g ← tryGoalM g unfoldSrvHelpersGoal
      let some g ← simpGoalAllHyps g (← mkEmptyDsimpCtx) #[] true | replaceMainGoal []; return
      let facts ← g.withContext do collectProofFacts #[← instantiateMVars (← g.getType)]
      let (g, _) ← assertFacts g "_reqFact" facts
      let g ← tryGoalM g unfoldSrvHelpersGoal
      let (abCtx, _) ← mkCachedSimpCtx "arrayAndBool" arrayAndBoolSimpNames { zetaDelta := true }
      let some g ← simpGoalAllHyps g abCtx | replaceMainGoal []; return
      let (reqCtx, _) ← mkCachedSimpCtx "rpcReq" rpcReqSimpNames { zetaDelta := true, zetaHave := true }
      let some g ← simpGoalAllHyps g reqCtx | replaceMainGoal []; return
      let some g ← dsimpCodecGoal g | replaceMainGoal []; return
      let rem ← (← splitGoalAnds g).filterMapM closeRpcReqLeaf
      setGoals rem
      unless rem.isEmpty do
        Qed.Diag.throwUnsolvedGoals
          m!"Server `requires` precondition could not be proved:"
          m!"\n\nHint: Guard this RPC call with `if ...:` so the precondition holds."
          (goals? := some (rem.take 1))

end Qed.Server
