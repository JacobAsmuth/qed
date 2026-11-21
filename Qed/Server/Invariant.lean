import Lean
import Qed.Field
import Qed.Diag
import Qed.Server.Core
import Qed.Server.Syntax
import Qed.Server.Registry

namespace Qed.Server

@[inline] instance {Inner : Type} {p : Inner → Prop} : SrvLiftOpt (Qed.Field p) Inner := ⟨fun f => some f.val⟩
@[inline] instance {Inner : Type} {p : Inner → Prop} : SrvLiftOpt (Option (Qed.Field p)) Inner := ⟨Option.map Qed.Field.val⟩

/-! ## String-Length Simproc & Cached `Simp.Context` Builders -/

open Lean Meta Simp in
private def mkCharListExpr (s : String) : Expr :=
  let charTy := mkConst ``Char
  let nilE := mkApp (mkConst ``List.nil [Level.zero]) charTy
  let consC := mkApp (mkConst ``List.cons [Level.zero]) charTy
  s.toList.foldr (init := nilE) fun c acc =>
    mkApp2 consC (mkApp (mkConst ``Char.ofNat) (mkNatLit c.toNat)) acc

open Lean Meta Simp in
simproc_decl qedReduceStrLen (String.length _) := fun e => do
  let some (Expr.lit (Literal.strVal s)) := e.getAppArgs[0]? | return .continue
  let cs := mkCharListExpr s
  let nExpr := mkNatLit s.length
  let prf ← mkEqTrans (mkApp (mkConst ``String.length_ofList) cs) (← mkEqRefl nExpr)
  return .done { expr := nExpr, proof? := some prf }

theorem srvDiteFalse_eq_true {P : Prop} [Decidable P] (t : P → Bool) :
    ((if h : P then t h else false) = true) ↔ ∃ h : P, t h = true := by
  by_cases hP : P <;> simp [hP]

theorem srvDiteFalse_eq_false {P : Prop} [Decidable P] (t : P → Bool) :
    ((if h : P then t h else false) = false) ↔ ∀ h : P, t h = false := by
  by_cases hP : P <;> simp [hP]

private def optCodecSimpNames : Array Lean.Name := #[
  `Qed.Codec.valid, `Qed.Codec.refine, `Qed.Codec.jsonOnly,
  `Qed.Codec.text, `Qed.Codec.textarea, `Qed.Codec.nat,
  `Qed.Codec.int, `Qed.Codec.checkbox, `Qed.Codec.date]

private def valUnwrapSimpNames : Array Lean.Name := #[
  ``Qed.Server.srvGetAt_eq, ``Qed.QedVal.val_field,
  ``Qed.QedVal.val_ensured, ``Qed.Lang.QedVal.val_id,
  ``Qed.Server.SrvIdx.toNat_nat, ``Qed.Server.SrvIdx.toNat_fin]

private def liftOptSimpNames : Array Lean.Name := #[
  ``Qed.Server.SrvLiftOpt.liftOpt_opt, ``Qed.Server.SrvLiftOpt.liftOpt_val]

private def boolSimpNames : Array Lean.Name := #[
  ``Bool.and_eq_true, ``Bool.or_eq_true, ``Bool.not_eq_true',
  ``beq_iff_eq, ``bne_iff_ne, ``decide_eq_true_eq]

private def arrayCoreSimpNames : Array Lean.Name := #[
  ``Array.size_set, ``Array.size_push, ``Array.getElem_set_self]

private def stepCombSimpNames : Array Lean.Name := #[
  ``Qed.Server.srvSeq_none, ``Qed.Server.srvSeq_some,
  ``Qed.Server.srvEmitSeq_none, ``Qed.Server.srvEmitSeq_some,
  ``Qed.Server.srvFinish_ok, ``Qed.Server.srvFinish_err, ``Qed.Server.srvFinish_none,
  ``Qed.Server.srvFinishEmit_ok, ``Qed.Server.srvFinishEmit_err, ``Qed.Server.srvFinishEmit_none,
  ``Qed.Server.srvAtomicCommit_none, ``Qed.Server.srvAtomicCommit_ok, ``Qed.Server.srvAtomicCommit_err,
  ``Qed.Server.srvAtomicCommitEmit_none, ``Qed.Server.srvAtomicCommitEmit_ok, ``Qed.Server.srvAtomicCommitEmit_err]

private def stepLetEqSimpNames : Array Lean.Name := #[
  ``Qed.Server.srvSeq_srvLetEq, ``Qed.Server.srvEmitSeq_srvLetEq,
  ``Qed.Server.srvFinish_srvLetEq, ``Qed.Server.srvFinishEmit_srvLetEq,
  ``Qed.Server.srvAtomicCommit_srvLetEq, ``Qed.Server.srvAtomicCommitEmit_srvLetEq,
  ``Qed.Server.srvWithNewState_srvLetEq,
  ``Qed.Server.prod_fst_srvLetEq, ``Qed.Server.prod_snd_srvLetEq]

private def ensPostSimpNames : Array Lean.Name := #[
  ``Qed.Server.srvEnsPost_ok, ``Qed.Server.srvEnsPost_err, ``Qed.Server.srvEnsPost_srvLetEq,
  ``Qed.Server.srvEnsPostOpt_some, ``Qed.Server.srvEnsPostOpt_none, ``Qed.Server.srvEnsPostOpt_err,
  ``Qed.Server.srvEnsPostOpt_srvLetEq, ``Qed.Server.srvEnsPostOpt_ok_iff]

private def threadProgBindSimpNames : Array Lean.Name := #[
  ``Qed.Server.threadProg_pure_bind, ``Qed.Server.threadProg_pure_bind', ``Qed.Server.threadProg_bind_assoc]

private def dsimpCodecUnfoldNames : Array Lean.Name :=
  #[``Qed.Lang.QedVal.val, ``Qed.Server.SrvIdx.toNat,
    ``Qed.Server.SrvLiftOpt.liftOpt, ``Qed.Server.srvGetAt] ++ optCodecSimpNames

private def arrayAndBoolSimpNames : Array Lean.Name :=
  #[``id_eq, ``ne_eq, ``Array.size_modify, ``Qed.Server.srvDiteFalse_eq_true, ``Qed.Server.srvDiteFalse_eq_false] ++
  valUnwrapSimpNames ++ arrayCoreSimpNames ++ boolSimpNames

private def litFieldSimpNames : Array Lean.Name :=
  #[``id_eq, ``Qed.Lang.QedVal.val_id] ++ optCodecSimpNames

private def fastFieldSimpNames : Array Lean.Name :=
  #[``id_eq] ++ valUnwrapSimpNames ++ optCodecSimpNames

private def slowRefinementSimpNames : Array Lean.Name :=
  #[``id_eq, ``ne_eq] ++ valUnwrapSimpNames ++ arrayCoreSimpNames ++ boolSimpNames

private def boundsTgtSimpNames : Array Lean.Name :=
  #[``id_eq, ``Qed.Server.srvGetAt_eq, ``Qed.QedVal.val_field, ``Qed.Lang.QedVal.val_id,
    ``Qed.Server.SrvIdx.toNat_nat, ``Qed.Server.SrvIdx.toNat_fin,
    ``Array.size_set, ``Array.size_push, ``Array.size_modify]

private def boundsHypSimpNames : Array Lean.Name :=
  #[``id_eq, ``ne_eq, ``Qed.Lang.not_qedAndProp, ``Qed.Lang.not_qedOrProp,
    ``Qed.QedVal.val_field, ``Qed.Lang.QedVal.val_id,
    ``Qed.Server.SrvIdx.toNat_nat, ``Qed.Server.SrvIdx.toNat_fin] ++ boolSimpNames

private def finishAtomPreSimpNames : Array Lean.Name :=
  valUnwrapSimpNames ++ liftOptSimpNames ++ #[``Array.getElem_set_self]

private def finishAtomFallbackSimpNames : Array Lean.Name :=
  valUnwrapSimpNames ++ arrayCoreSimpNames

private def hypSimpEachNames : Array Lean.Name :=
  #[``id_eq, ``ne_eq, ``Prod.mk.injEq, ``Option.some.injEq, ``Except.ok.injEq, ``Except.error.injEq,
    ``reduceCtorEq, ``Qed.Lang.not_qedAndProp, ``Qed.Lang.not_qedOrProp,
    ``Qed.Server.srvDiteFalse_eq_true, ``Qed.Server.srvDiteFalse_eq_false,
    ``Qed.Server.srvUnwrap_srvFailure_ok_iff, ``Qed.Server.srvUnwrap_str_ok_iff, ``Qed.Server.srvUnwrap_opt_ok_iff] ++
  valUnwrapSimpNames ++ liftOptSimpNames ++ optCodecSimpNames ++ arrayCoreSimpNames ++ boolSimpNames

private def tgtSimpEachNames : Array Lean.Name :=
  #[``id_eq, ``ne_eq, ``Array.forall_push, ``Array.sumBy_empty, ``Array.sumBy_push] ++
  stepCombSimpNames ++ valUnwrapSimpNames ++ liftOptSimpNames ++ arrayCoreSimpNames ++ boolSimpNames

private def postRwSimpNames : Array Lean.Name :=
  #[``Array.sumBy_empty, ``Array.sumBy_push] ++ arrayCoreSimpNames ++ valUnwrapSimpNames ++ liftOptSimpNames

private def stepFixedSimpNames : Array Lean.Name :=
  #[``Qed.Server.srvUnwrap_srvFailure_ok_iff, ``Qed.Server.srvUnwrap_str_ok_iff, ``Qed.Server.srvUnwrap_opt_ok_iff] ++
  stepCombSimpNames ++ stepLetEqSimpNames ++ ensPostSimpNames ++ valUnwrapSimpNames ++ liftOptSimpNames

private def asyncInitSimpNames : Array Lean.Name :=
  #[``Qed.Server.srvFinishM, ``Qed.Server.srvSeqM, ``Qed.Server.dbRunTx]

private def asyncDsimpNames : Array Lean.Name :=
  #[``Qed.Server.srvSeqM, ``Qed.Server.dbRunTx, ``Qed.Server.SrvUnwrap.unwrap, ``Qed.Server.SrvErr.ofApi, ``Qed.Server.SrvUnwrapOpt.unwrapOpt]

private def asyncNormSimpNames : Array Lean.Name :=
  stepCombSimpNames ++ stepLetEqSimpNames ++ ensPostSimpNames ++ threadProgBindSimpNames

private def rpcReqSimpNames : Array Lean.Name :=
  #[``Option.isSome_iff_ne_none, ``ne_eq, `Qed.Cached.all, `Qed.Resource.all] ++
  boolSimpNames ++ valUnwrapSimpNames ++ optCodecSimpNames

open Lean Meta in
private def addSimpNamesWithEqns (st : SimpTheorems) (names : Array Name) (dsimpOnly : Bool := false) :
    MetaM (SimpTheorems × Array Name) := do
  let env ← getEnv
  let mut st := st
  let mut eqnsAdded : Array Name := #[]
  for n in names do
    if let some ci := env.find? n then
      match ci with
      | .thmInfo _ =>
          unless dsimpOnly do
            st ← st.addConst n
      | _ =>
          st ← st.addDeclToUnfold n
          unless dsimpOnly do
            if let some eqns ← getEqnsFor? n then
              for eq in eqns do
                st ← st.addConst eq
                eqnsAdded := eqnsAdded.push eq
  return (st, eqnsAdded)

open Lean Meta in
private def addSimpNames (st : SimpTheorems) (names : Array Name) (dsimpOnly : Bool := false) :
    MetaM SimpTheorems :=
  Prod.fst <$> addSimpNamesWithEqns st names dsimpOnly

initialize srvSimpThmsCache : IO.Ref (Std.HashMap (String × Lean.Name × Bool) (Lean.Meta.SimpTheorems × Array Lean.Name)) ←
  IO.mkRef {}

initialize srvStrLenSimprocsCache : IO.Ref (Option Lean.Meta.Simp.SimprocsArray) ←
  IO.mkRef none

open Lean Meta in
private def getStrLenSimprocs : MetaM Simp.SimprocsArray := do
  if let some sp ← srvStrLenSimprocsCache.get then
    return sp
  let mut sp : Simp.Simprocs := {}
  sp ← sp.add ``qedReduceStrLen true
  let arr := #[sp]
  srvStrLenSimprocsCache.set (some arr)
  return arr

open Lean Meta in
private def getCachedSimpThms (key : String) (names : Array Name) (dsimpOnly : Bool := false) :
    MetaM SimpTheorems := do
  let envBefore ← getEnv
  let cacheKey := (key, envBefore.header.mainModule, envBefore.contains `Qed.Codec.valid)
  if let some (st, needed) := (← srvSimpThmsCache.get).get? cacheKey then
    if needed.all envBefore.contains then
      return st
  let (st, eqns) ← addSimpNamesWithEqns {} names dsimpOnly
  let envAfter ← getEnv
  let mut needed := eqns
  for (c, _) in envAfter.constants.map₂.toList do
    if !envBefore.contains c then
      needed := needed.push c
  srvSimpThmsCache.modify (·.insert cacheKey (st, needed))
  return st

open Lean Meta in
private def mkCachedSimpCtx (key : String) (names : Array Name)
    (cfg : Simp.Config := { zetaDelta := false }) (withStrLen : Bool := false) (dsimpOnly : Bool := false) :
    MetaM (Simp.Context × Simp.SimprocsArray) := do
  let st ← getCachedSimpThms key names dsimpOnly
  let ctx ← Simp.mkContext { cfg with failIfUnchanged := false } #[st] (← getSimpCongrTheorems)
  let simprocs ← if withStrLen then getStrLenSimprocs else pure #[]
  return (ctx, simprocs)

open Lean Meta in
private def mkDynamicSimpCtx (extraNames : Array Name) (baseKey? : Option (String × Array Name) := none)
    (cfg : Simp.Config := { zetaDelta := false }) (dsimpOnly : Bool := false) : MetaM Simp.Context := do
  let baseSt ← match baseKey? with
    | some (k, ns) => getCachedSimpThms k ns dsimpOnly
    | none         => pure {}
  let st ← addSimpNames baseSt extraNames dsimpOnly
  Simp.mkContext { cfg with failIfUnchanged := false } #[st] (← getSimpCongrTheorems)

open Lean Meta in
private def tryGoalM (g : MVarId) (k : MVarId → MetaM MVarId) : MetaM MVarId := do
  let s ← saveState
  try k g catch _ => restoreState s; return g

open Lean Meta in
private def tryGoalOptM (g : MVarId) (k : MVarId → MetaM (Option MVarId)) : MetaM (Option MVarId) := do
  let s ← saveState
  try k g catch _ => restoreState s; return some g

open Lean Meta in
private def simpGoalOnly (g : MVarId) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray := #[])
    (fvarIds : Array FVarId := #[]) (simplifyTarget : Bool := true) (dsimpOnly : Bool := false) :
    MetaM (Option MVarId) := do
  let s ← saveState
  try
    if dsimpOnly then
      return (← dsimpGoal g ctx simprocs simplifyTarget fvarIds).1
    else
      match (← simpGoal g ctx simprocs none simplifyTarget fvarIds).1 with
      | none         => return none
      | some (_, g') => return some g'
  catch _ =>
    restoreState s
    return some g

open Lean Meta in
private def trySimpAll (g : MVarId) (ctx : Simp.Context) (sp : Simp.SimprocsArray := #[]) :
    MetaM (Option MVarId) := do
  let s ← saveState
  try return (← simpAll g ctx sp).1 catch _ => restoreState s; return some g

open Lean Meta in
private def trySplitTarget (g : MVarId) : MetaM (Option (List MVarId)) := do
  let s ← saveState
  try
    let res? ← g.withContext (Meta.splitTarget? g)
    if res?.isNone then restoreState s
    return res?
  catch _ => restoreState s; return none

open Lean Meta in
private def trySplitLocalDecl (g : MVarId) (fv : FVarId) : MetaM (Option (List MVarId)) := do
  let s ← saveState
  try
    let res? ← g.withContext (Meta.splitLocalDecl? g fv)
    if res?.isNone then restoreState s
    return res?
  catch _ => restoreState s; return none

open Lean Meta in
private def simpGoalAllHyps (g : MVarId) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray := #[]) :
    MetaM (Option MVarId) := do
  let fvs ← g.withContext do
    let mut arr : Array FVarId := #[]
    for d in (← getLCtx) do
      if !d.isImplementationDetail then arr := arr.push d.fvarId
    return arr
  simpGoalOnly g ctx simprocs fvs true false

/-! ## Fast Direct MetaM Closers & Proof-Fact Collection -/

open Lean in
private def isSrvEqDecl (decl : LocalDecl) : Bool :=
  !decl.userName.hasMacroScopes &&
    let u := decl.userName.toString
    u.startsWith "_srvEq" || u.startsWith "_hLet"

open Lean in
private def isKnownNonRefinedHead (c : Name) : Bool :=
  c == ``Nat || c == ``Int || c == ``String || c == ``Bool || c == ``Unit ||
  c == ``ByteArray || c == ``Char || c == ``UInt8 || c == ``UInt16 ||
  c == ``UInt32 || c == ``UInt64 || c == ``USize || c == ``Array || c == ``List ||
  c == ``Option || c == ``Except || c == ``Prod || c == ``Eq || c == ``And ||
  c == ``Or || c == ``Not || c == ``LT.lt || c == ``LE.le || c == ``True ||
  c == ``False || c == ``RequestCtx || c == ``ApiError || c == ``WsEmit

open Lean Meta in
private def inspectFieldOrFin (sub : Expr) (addFact : Expr → MetaM Unit) : MetaM Unit := do
  if sub.hasLooseBVars then return
  match sub with
  | .sort _ | .lit _ | .mvar _ | .bvar _ | .forallE .. | .lam .. => return
  | _ => pure ()
  let some t ← try some <$> inferType sub catch _ => pure none | return
  let tC := t.consumeMData
  if tC.isAppOfArity ``Qed.Field 2 then
    if let some p ← try some <$> mkAppM ``Qed.Field.ok #[sub] catch _ => pure none then addFact p
    return
  if tC.isAppOfArity ``Qed.Ensured 2 then
    if let some p ← try some <$> mkAppM ``Qed.Ensured.ok #[sub] catch _ => pure none then addFact p
    return
  if tC.isAppOfArity ``Fin 1 then
    if let some p ← try some <$> mkAppM ``Fin.isLt #[sub] catch _ => pure none then addFact p
    return
  match tC.getAppFn with
  | .sort _ | .forallE .. => return
  | .const c _ => if isKnownNonRefinedHead c then return
  | _ => pure ()
  let some ty ← try some <$> whnf tC catch _ => pure none | return
  if ty.isAppOfArity ``Qed.Field 2 then
    if let some p ← try some <$> mkAppM ``Qed.Field.ok #[sub] catch _ => pure none then addFact p
  else if ty.isAppOfArity ``Qed.Ensured 2 then
    if let some p ← try some <$> mkAppM ``Qed.Ensured.ok #[sub] catch _ => pure none then addFact p
  else if ty.isAppOfArity ``Fin 1 then
    if let some p ← try some <$> mkAppM ``Fin.isLt #[sub] catch _ => pure none then addFact p

open Lean Meta in
private def scanExprForFacts (e : Expr) (seenRef : IO.Ref (Std.HashSet Expr))
    (addFact : Expr → MetaM Unit) : MetaM Unit := do
  e.forEach fun sub => do
    unless sub.hasLooseBVars do
      let seen ← seenRef.get
      unless seen.contains sub do
        seenRef.set (seen.insert sub)
        inspectFieldOrFin sub addFact

open Lean Meta Elab Term in
/-- Collects all closed subterms of type `Qed.Field _`, `Qed.Ensured _`, or `Fin _` from `extraExprs`
    and local hypotheses so `omega` automatically sees `.ok` field refinements and `.isLt` index bounds. -/
def collectProofFacts (extraExprs : Array Expr) : TermElabM (Array Expr) := do
  let factsRef ← IO.mkRef (#[] : Array Expr)
  let factSetRef ← IO.mkRef (({} : Std.HashSet Expr))
  let seenRef ← IO.mkRef (({} : Std.HashSet Expr))
  let addFact (fact : Expr) : MetaM Unit := do
    let s ← factSetRef.get
    unless s.contains fact do
      factSetRef.set (s.insert fact)
      factsRef.modify (·.push fact)
  let lctx ← getLCtx
  for decl in lctx do
    if !decl.isImplementationDetail then
      if !decl.isLet && decl.userName.hasMacroScopes then
        if (← try isProp decl.type catch _ => pure false) then
          liftMetaM <| addFact decl.toExpr
      unless isSrvEqDecl decl do
        liftMetaM <| scanExprForFacts decl.toExpr seenRef addFact
        if let some val := decl.value? then
          liftMetaM <| scanExprForFacts val seenRef addFact
  for e in extraExprs do
    liftMetaM <| scanExprForFacts (← instantiateMVars e) seenRef addFact
  factsRef.get

open Lean Meta Elab Term in
def withPosedFacts (facts : Array Expr) (k : TermElabM Expr) : TermElabM Expr := do
  let rec loop (idx : Nat) : TermElabM Expr := do
    if h : idx < facts.size then
      let fPrf := facts[idx]
      let fTy ← inferType fPrf
      withLocalDeclD (Name.mkSimple s!"_srvFact{idx}") fTy fun fvar => do
        let inner ← loop (idx + 1)
        return mkApp (← mkLambdaFVars #[fvar] inner) fPrf
    else
      k
  loop 0

open Lean in
private def hasUnsteppedCtrlFlow (e : Expr) : Bool :=
  e.getUsedConstants.any fun c =>
    c == ``Qed.Server.srvLetEq || c == ``Qed.Server.srvFinish ||
    c == ``Qed.Server.srvFinishEmit || c == ``Qed.Server.srvSeq ||
    c == ``Qed.Server.srvEmitSeq || c == ``Qed.Server.srvAtomicCommit ||
    c == ``Qed.Server.srvAtomicCommitEmit || c == ``Qed.Server.srvEnsPost ||
    c == ``Qed.Server.srvEnsPostOpt || c == ``ite || c == ``dite

open Lean Meta in
private def tryCloseTrivial (g : MVarId) : MetaM Bool := do
  let tgt ← g.withContext do instantiateMVars (← g.getType)
  let tgtC := tgt.consumeMData
  if tgtC.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    return true
  if hasUnsteppedCtrlFlow tgtC then
    return false
  if tgtC.isAppOfArity ``Eq 3 then
    let s ← saveState
    try g.refl; return true catch _ => restoreState s
  if tgtC.isAppOfArity ``LE.le 4 || tgtC.isAppOfArity ``GE.ge 4 then
    let args := tgtC.getAppArgs
    if args[2]! == args[3]! then
      let s ← saveState
      try
        let gs ← g.applyConst ``Nat.le_refl
        if gs.isEmpty then return true
        restoreState s
      catch _ => restoreState s
  if ← g.assumptionCore then return true
  if tgtC.isAppOfArity ``Or 2 then
    let s ← saveState
    try
      let [gL] ← g.applyConst ``Or.inl | restoreState s
      gL.refl
      return true
    catch _ => restoreState s
    let s ← saveState
    try
      let [gR] ← g.applyConst ``Or.inr | restoreState s
      if ← gR.assumptionCore then return true
      restoreState s
    catch _ => restoreState s
  return false

open Lean Meta in
private def tryDirectDecide (g : MVarId) : MetaM Bool := do
  let tgt ← g.withContext do instantiateMVars (← g.getType)
  if tgt.hasFVar || tgt.hasMVar then return false
  let s ← saveState
  try
    let ok ← g.withContext do
      let decInst ← synthInstance (mkApp (mkConst ``Decidable) tgt)
      let decApp := mkApp2 (mkConst ``Decidable.decide) tgt decInst
      if ← isDefEq decApp (mkConst ``Bool.true) then
        let prf := mkApp3 (mkConst ``of_decide_eq_true) tgt decInst (← mkEqRefl (mkConst ``Bool.true))
        g.assign prf
        return true
      return false
    unless ok do restoreState s
    return ok
  catch _ =>
    restoreState s
    return false

open Lean Meta Elab Tactic in
private def tryDirectOmega (g : MVarId) : MetaM Bool := do
  let s ← saveState
  try
    let some g' ← g.falseOrByContra | return true
    g'.withContext do
      let hyps ← getPropHyps
      Omega.omega (hyps.toList.map mkFVar) g' {}
    return true
  catch _ =>
    restoreState s
    return false

open Lean Meta Elab Tactic in
private def tryCloseBasic (g : MVarId) : MetaM Bool := do
  if ← tryCloseTrivial g then return true
  if ← tryDirectDecide g then return true
  tryDirectOmega g

/-! ## Helper Unfolding & Hypothesis Splitting -/

open Lean Meta in
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

open Lean in
private def hasSrvHelperConst (e : Expr) : Bool :=
  e.getUsedConstants.any fun c =>
    c == ``srvGetAt || c == ``Qed.Lang.QedVal.val || c == ``SrvIdx.toNat ||
    c == ``SrvLiftOpt.liftOpt || c == ``id

open Lean Meta in
private def nextFreshSrvName (g : MVarId) (pfx : String) (startIdx : Nat) : MetaM (Name × Nat) := do
  let lctx ← g.withContext getLCtx
  let mut i := startIdx
  let mut cand := Name.mkSimple s!"{pfx}{i}"
  while lctx.any (·.userName == cand) do
    i := i + 1
    cand := Name.mkSimple s!"{pfx}{i}"
  return (cand, i + 1)

open Lean Meta in
private def unfoldSrvHelpersGoal (g0 : MVarId) : MetaM MVarId := do
  let mut g := g0
  let lctx0 ← g.withContext getLCtx
  let mut hIdx : Nat := lctx0.size
  let mut propFVars : Array FVarId := #[]
  for decl in lctx0 do
    if !decl.isImplementationDetail && !decl.isLet then
      unless isSrvEqDecl decl do
        let ty ← g.withContext (instantiateMVars decl.type)
        if (← g.withContext (try isProp ty catch _ => pure false)) then
          if decl.userName.hasMacroScopes then
            let (cand, nxt) ← nextFreshSrvName g "_srvSplitH" hIdx
            hIdx := nxt
            g ← g.rename decl.fvarId cand
          if hasSrvHelperConst ty then
            propFVars := propFVars.push decl.fvarId
  for revIdx in [0:propFVars.size] do
    let fv := propFVars[propFVars.size - 1 - revIdx]!
    if let some decl := (← g.withContext getLCtx).find? fv then
      let ty ← g.withContext (instantiateMVars decl.type)
      if hasSrvHelperConst ty then
        let ty' ← g.withContext (unfoldSrvHelpersExpr ty)
        if ty' != ty then
          let curTgt ← g.withContext (instantiateMVars (← g.getType))
          if curTgt.containsFVar fv then
            let (cand, nxt) ← nextFreshSrvName g "_srvFreeH" hIdx
            hIdx := nxt
            let (_, gFree) ← (← g.assert cand ty' (mkFVar fv)).intro1P
            g := gFree
          let sCh ← saveState
          if let some g' ← try some <$> g.changeLocalDecl fv ty' catch _ => restoreState sCh; pure none then
            g := g'
  let tgt ← g.withContext (instantiateMVars (← g.getType))
  if hasSrvHelperConst tgt then
    let tgt' ← g.withContext (unfoldSrvHelpersExpr tgt)
    if tgt' != tgt then
      let sCh ← saveState
      try g ← g.change tgt' catch _ => restoreState sCh
  return g

open Lean Meta in
private def splitAndHypsGoal (g0 : MVarId) : MetaM (MVarId × Bool) := do
  let mut g := g0
  let mut didSplit := false
  for _ in [0:32] do
    let lctx ← g.withContext getLCtx
    let mut nextG? : Option MVarId := none
    for decl in lctx do
      if nextG?.isNone && !decl.isImplementationDetail && !decl.isLet then
        let tC := decl.type.consumeMData
        let maybeSplittable :=
          tC.isAppOfArity ``And 2 || tC.isAppOfArity ``Exists 2 ||
          tC.isAppOfArity ``Qed.Lang.QedAndProp 2 ||
          match tC.getAppFn with
          | .const c _ => !isKnownNonRefinedHead c
          | _ => true
        if maybeSplittable then
          let s ← saveState
          try
            let ty ← g.withContext (whnf tC)
            if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``Qed.Lang.QedAndProp 2 then
              let subgoals ← g.cases decl.fvarId
              if let some sg := subgoals[0]? then
                nextG? := some sg.mvarId
                didSplit := true
              else
                restoreState s
          catch _ => restoreState s
    match nextG? with
    | some g' => g := g'
    | none    => break
  return (g, didSplit)

open Lean Meta in
private def simpHypsEachGoal (g0 : MVarId) : MetaM (Option MVarId) := do
  let lctx ← g0.withContext getLCtx
  let mut hFVars : Array FVarId := #[]
  for decl in lctx do
    if !decl.isImplementationDetail && !decl.isLet && !decl.userName.hasMacroScopes then
      unless isSrvEqDecl decl do
        if (← g0.withContext (try isProp decl.type catch _ => pure false)) then
          hFVars := hFVars.push decl.fvarId
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

open Lean Meta Elab Term in
private def exprHasLetFVar (lctx : LocalContext) (e : Expr) : Bool :=
  e.hasAnyFVar fun fvid => match lctx.find? fvid with
    | some d => d.isLet
    | none   => false

open Lean in
private def isTinyProofExpr (e : Expr) : Bool :=
  match e.consumeMData with
  | .fvar _ | .const _ _ => true
  | .app (.const ``Eq.refl _) _ => true
  | .app (.app (.const ``of_decide_eq_true _) _) _ => true
  | .app (.app (.const ``Nat.le_refl _) _) _ => true
  | .app (.app (.app (.const ``Qed.Field.ok _) _) _) _ => true
  | .app (.app (.app (.const ``Qed.Ensured.ok _) _) _) _ => true
  | .app (.app (.const ``Fin.isLt _) _) _ => true
  | _ => false

open Lean Meta Elab Term in
private def wrapAuxProof (goalProp prf : Expr) : TermElabM Expr := do
  let prf ← instantiateMVars prf
  let goalProp ← instantiateMVars goalProp
  if prf.hasMVar || goalProp.hasMVar || isTinyProofExpr prf then
    return prf
  let lctx ← getLCtx
  if exprHasLetFVar lctx goalProp || exprHasLetFVar lctx prf then
    return prf
  liftMetaM <| Meta.mkAuxTheorem goalProp prf (zetaDelta := false)

open Lean Meta Elab Term in
private def proveGoalWithMeta (facts : Array Expr) (goalProp : Expr)
    (solver : MVarId → Array FVarId → MetaM Bool) : TermElabM (Option Expr) := do
  let s ← saveState
  try
    let mvar ← mkFreshExprMVar goalProp
    let mut g := mvar.mvarId!
    let mut factFVars : Array FVarId := #[]
    for idx in [0:facts.size] do
      let fPrf := facts[idx]!
      let fTy ← g.withContext (inferType fPrf)
      let (fv, g') ← (← g.assert (Name.mkSimple s!"_srvFact{idx}") fTy fPrf).intro1P
      g := g'
      factFVars := factFVars.push fv
    if ← solver g factFVars then
      let prf ← instantiateMVars mvar
      unless prf.hasMVar do
        return some prf
    restoreState s
    return none
  catch _ =>
    restoreState s
    return none

open Lean Meta Elab Term Tactic in
private def solveRefinementSlow (g0 : MVarId) : MetaM Bool := do
  let mut g := g0
  g ← try unfoldSrvHelpersGoal g catch _ => pure g
  match ← try simpHypsEachGoal g catch _ => pure (some g) with
  | none    => return true
  | some g' => g := g'
  let (refCtx, sp) ← mkCachedSimpCtx "slowRefinement" slowRefinementSimpNames { zetaDelta := false } true
  match ← try simpGoalOnly g refCtx sp catch _ => pure (some g) with
  | none    => return true
  | some g' => g := g'
  let (dcCtx, _) ← mkCachedSimpCtx "dsimpCodec" dsimpCodecUnfoldNames { zetaDelta := false } false true
  match ← try simpGoalOnly g dcCtx #[] #[] true true catch _ => pure (some g) with
  | none    => return true
  | some g' => g := g'
  let (strCtx, strSp) ← mkCachedSimpCtx "strLenOnly" #[] { zetaDelta := false } true
  match ← try simpGoalOnly g strCtx strSp catch _ => pure (some g) with
  | none    => return true
  | some g' => g := g'
  if ← tryCloseBasic g then return true
  -- Final fallback: `simp_all` with field unwrappers + `qedReduceStrLen`
  let baseSimp ← getSimpTheorems
  let extra ← addSimpNames baseSimp #[``Qed.QedVal.val_field, ``Qed.QedVal.val_ensured, ``Qed.Lang.QedVal.val_id]
  let saCtx ← Simp.mkContext { failIfUnchanged := false } #[extra] (← getSimpCongrTheorems)
  match ← trySimpAll g saCtx strSp with
  | none    => return true
  | some g' => tryCloseBasic g'

open Lean Meta Elab Term Tactic in
private def solveAutoFieldFast (isLit : Bool) (g0 : MVarId) (factFVars : Array FVarId) : MetaM Bool := do
  let mut g := g0
  if isLit && factFVars.isEmpty then
    let (litCtx, sp) ← mkCachedSimpCtx "litField" litFieldSimpNames { zetaDelta := false } true
    match ← try simpGoalOnly g litCtx sp catch _ => pure (some g) with
    | none    => return true
    | some g' => g := g'
    return ← tryCloseBasic g
  else
    let (ffCtx, sp) ← mkCachedSimpCtx "fastField" fastFieldSimpNames { zetaDelta := false } true
    match ← try simpGoalOnly g ffCtx sp factFVars true false catch _ => pure (some g) with
    | none    => return true
    | some g' => g := g'
    if ← tryCloseBasic g then return true
    let (dcCtx, _) ← mkCachedSimpCtx "dsimpCodec" dsimpCodecUnfoldNames { zetaDelta := false } false true
    match ← try simpGoalOnly g dcCtx #[] #[] true true catch _ => pure (some g) with
    | none    => return true
    | some g' => g := g'
    let (strCtx, strSp) ← mkCachedSimpCtx "strLenOnly" #[] { zetaDelta := false } true
    match ← try simpGoalOnly g strCtx strSp catch _ => pure (some g) with
    | none    => return true
    | some g' => g := g'
    return ← tryCloseBasic g

open Lean Meta Elab Term in
private def throwFieldRuleFailed (stx : Syntax) (predFn valExpr : Expr) : TermElabM α := do
  let mut p := predFn.consumeMData
  if p.isAppOfArity `Qed.Codec.valid 2 then
    let mut c := (p.getArg! 1).consumeMData
    while c.isAppOfArity `Qed.Codec.jsonOnly 2 do
      c := (c.getArg! 1).consumeMData
    if c.isAppOfArity `Qed.Codec.refine 4 then
      p := c.getArg! 2
  let prettyGoal ← Qed.Diag.ppQedExpr ((Expr.app p valExpr).headBeta)
  let prettyVal ← Qed.Diag.ppQedExpr valExpr
  throwErrorAt stx m!"Schema field rule `{prettyGoal}` failed for `{prettyVal}`.\n\n\
    Hint: Guard this value with `if ...:` or a `requires` precondition so it satisfies the schema's `where` rule."

open Lean Meta Elab Term Tactic in
@[term_elab srvAutoFieldStx]
def elabSrvAutoField : TermElab := fun stx expectedType? => do
  let valStx : Term := ⟨(stx.getArg 1)⟩
  if let some expTy := expectedType? then
    let expTy ← instantiateMVars expTy
    if !expTy.getAppFn.isMVar then
      let expWhnf ← whnf expTy
      if expWhnf.isAppOfArity ``Qed.Field 2 then
        let args := expWhnf.getAppArgs
        let innerTy := args[0]!
        let predFn := args[1]!
        let valExpr ← elabTermEnsuringType valStx (some innerTy)
        synthesizeSyntheticMVarsNoPostponing
        let valExpr ← instantiateMVars valExpr
        let goalProp := mkApp predFn valExpr
        let isLit := valExpr.isLit || (valExpr.getAppFn.isConstOf ``OfNat.ofNat && !valExpr.hasFVar)
        let localFacts ← if isLit then pure #[] else do
          let factsRef ← IO.mkRef (#[] : Array Expr)
          let factSetRef ← IO.mkRef (({} : Std.HashSet Expr))
          let seenRef ← IO.mkRef (({} : Std.HashSet Expr))
          liftMetaM <| scanExprForFacts valExpr seenRef fun p => do
            let s ← factSetRef.get
            unless s.contains p do
              factSetRef.set (s.insert p)
              factsRef.modify (·.push p)
          factsRef.get
        if let some fastPrf ← proveGoalWithMeta localFacts goalProp (solveAutoFieldFast isLit) then
          let fastPrf ← wrapAuxProof goalProp fastPrf
          return ← mkAppOptM ``Qed.Field.mk #[some innerTy, some predFn, some valExpr, some fastPrf]
        let facts ← collectProofFacts #[valExpr]
        let some prfExpr ← proveGoalWithMeta facts goalProp (fun g _ => solveRefinementSlow g)
          | throwFieldRuleFailed stx predFn valExpr
        let prfExpr ← wrapAuxProof goalProp prfExpr
        return ← mkAppOptM ``Qed.Field.mk #[some innerTy, some predFn, some valExpr, some prfExpr]
      else
        return ← try elabTermEnsuringType valStx (some expTy)
                 catch _ => elabTermEnsuringType (← `(Qed.Lang.QedVal.val $valStx)) (some expTy)
  let e ← elabTerm valStx none
  synthesizeSyntheticMVars (postpone := .yes)
  let ty ← whnf (← instantiateMVars (← inferType e))
  let e ← if ty.isAppOfArity ``Qed.Field 2 then mkAppM ``Qed.Field.val #[e] else pure e
  match expectedType? with
  | some expTy => ensureHasType expTy e
  | none       => return e

open Lean Meta Elab Term in
@[term_elab srvAutoEmitStx]
def elabSrvAutoEmit : TermElab := fun stx expectedType? => do
  let propExpr ← match expectedType? with
    | some expTy => instantiateMVars expTy
    | none       => elabTerm (stx.getArg 1) (some (mkSort Level.zero))
  let facts ← collectProofFacts #[propExpr]
  let some prfExpr ← proveGoalWithMeta facts propExpr (fun g _ => solveRefinementSlow g)
    | do
        let unfolded := (← unfoldDefinition? propExpr).getD propExpr
        let prettyGoal ← Qed.Diag.ppQedExpr unfolded
        throwErrorAt stx m!"Channel `ensures` postcondition failed at `emit`:\n  • must satisfy:  {prettyGoal}\n\n\
          Hint: Ensure the emitted event satisfies the channel's `ensures` clause."
  wrapAuxProof propExpr prfExpr

open Lean Meta Elab Term in
@[term_elab srvTypedAsStx]
def elabSrvTypedAs : TermElab := fun stx expectedType? => do
  let tplExpr ← elabTerm (stx.getArg 1) none
  synthesizeSyntheticMVarsNoPostponing
  let tplTy ← instantiateMVars (← inferType tplExpr)
  let valExpr ← elabTermEnsuringType (stx.getArg 3) (some tplTy)
  match expectedType? with
  | some expTy => ensureHasType expTy valExpr
  | none       => return valExpr

/-! ## Bounds Checking (`srvGetElem`, `srvSetElem`) -/

open Lean Meta in
private def unwrapSizeSet? (e : Expr) : Nat → MetaM (Option (Expr × Expr))
  | 0 => return none
  | fuel + 1 => do
      let eC := e.consumeMData
      if eC.isAppOfArity ``Array.set 5 then
        let setArgs := eC.getAppArgs
        let prevArr := setArgs[1]!
        let eqSet ← mkAppOptM ``Array.size_set
          #[some setArgs[0]!, some prevArr, some setArgs[2]!, some setArgs[3]!, some setArgs[4]!]
        return some (prevArr, eqSet)
      else if eC.isAppOfArity ``srvLetEq 4 then
        let lArgs := eC.getAppArgs
        let eqRefl ← mkEqRefl lArgs[2]!
        let nextBody := (mkApp2 lArgs[3]! lArgs[2]! eqRefl).headBeta
        unwrapSizeSet? nextBody fuel
      else
        return none

open Lean Meta in
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
      if !decl.isImplementationDetail && !decl.isLet then
        let ty ← instantiateMVars decl.type
        if let some (_, lhs, rhs) := ty.eq? then
          if lhs.consumeMData == Expr.fvar fv then
            let rhsC := rhs.consumeMData
            if let some (prevArr, eqSet) ← try unwrapSizeSet? rhsC 8 catch _ => pure none then
              let arrTy ← whnf (← inferType cur)
              let elemTy := if arrTy.isAppOfArity ``Array 1 then arrTy.getAppArgs[0]! else mkConst ``Unit
              let eqCur ← mkAppM ``congrArg #[← mkAppOptM ``Array.size #[some elemTy], decl.toExpr]
              let prevEqCur ← mkEqSymm (← mkEqTrans eqCur eqSet)
              next? := some (prevArr, prevEqCur)
              break
            else if !rhsC.containsFVar fv && !(rhsC.getUsedConstants.any (· == ``srvLetEq)) then
              let arrTy ← whnf (← inferType cur)
              let elemTy := if arrTy.isAppOfArity ``Array 1 then arrTy.getAppArgs[0]! else mkConst ``Unit
              let curEqRhs ← mkAppM ``congrArg #[← mkAppOptM ``Array.size #[some elemTy], decl.toExpr]
              next? := some (rhsC, ← mkEqSymm curEqRhs)
              break
    match next? with
    | some (prevArr, prevEqCur) =>
        let combined ← match eqOpt? with
          | none    => pure prevEqCur
          | some eq => mkEqTrans prevEqCur eq
        cur := prevArr
        eqOpt? := some combined
    | none => break
  return (cur, eqOpt?)

open Lean Meta in
private def collectSizeBoundHypFVars (lctx : LocalContext) : MetaM (Array FVarId) := do
  let mut fvs : Array FVarId := #[]
  for decl in lctx do
    if !decl.isImplementationDetail && !decl.isLet && !decl.userName.hasMacroScopes then
      let ty ← instantiateMVars decl.type
      if (← try isProp ty catch _ => pure false) then
        let cs := ty.getUsedConstants
        let hasRel := cs.any fun c =>
          c == ``Array.size || c == ``LT.lt || c == ``LE.le || c == ``GE.ge || c == ``GT.gt
        let hasHeavy := cs.any fun c =>
          c == ``srvGetAt || c == ``RequestCtx || c == ``Array.set
        if hasRel && !hasHeavy then
          fvs := fvs.push decl.fvarId
  return fvs

open Lean Meta Elab Tactic in
private def solveBoundsFast (g0 : MVarId) : MetaM Bool := do
  if ← tryCloseTrivial g0 then return true
  let (tgtCtx, _) ← mkCachedSimpCtx "boundsTgt" boundsTgtSimpNames { zetaDelta := true }
  let g1 ← match ← try simpGoalOnly g0 tgtCtx catch _ => pure (some g0) with
    | none    => return true
    | some g' => pure g'
  let mut g := g1
  let sizeFVars ← g.withContext do collectSizeBoundHypFVars (← getLCtx)
  unless sizeFVars.isEmpty do
    let (hypCtx, _) ← mkCachedSimpCtx "boundsHyp" boundsHypSimpNames
    match ← try simpGoalOnly g hypCtx #[] sizeFVars false false catch _ => pure (some g) with
    | none    => return true
    | some g' => g := g'
  if ← tryCloseTrivial g then return true
  tryDirectOmega g

open Lean Meta Elab Tactic in
private def solveBoundsSlow (g0 : MVarId) : MetaM Bool := do
  let mut g := g0
  g ← try unfoldSrvHelpersGoal g catch _ => pure g
  let dsimpAllCtx ← Simp.mkContext { zetaDelta := true, failIfUnchanged := false } #[] (← getSimpCongrTheorems)
  let allFVars ← g.withContext do
    let mut arr : Array FVarId := #[]
    for d in (← getLCtx) do
      if !d.isImplementationDetail then arr := arr.push d.fvarId
    return arr
  match ← try simpGoalOnly g dsimpAllCtx #[] allFVars true true catch _ => pure (some g) with
  | none    => return true
  | some g' => g := g'
  let (abCtx, _) ← mkCachedSimpCtx "arrayAndBool" arrayAndBoolSimpNames { zetaDelta := true }
  match ← simpGoalAllHyps g abCtx with
  | none    => return true
  | some g' => g := g'
  let (g', _) ← try splitAndHypsGoal g catch _ => pure (g, false)
  g := g'
  if ← tryCloseTrivial g then return true
  if ← tryDirectOmega g then return true
  let baseSimp ← getSimpTheorems
  let saCtx ← Simp.mkContext { zetaDelta := true, failIfUnchanged := false } #[baseSimp] (← getSimpCongrTheorems)
  match ← trySimpAll g saCtx #[] with
  | none    => return true
  | some g' =>
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
                | some c' =>
                    if ← tryDirectOmega c' then splitLoop f rest else return false
      splitLoop 16 [g']

open Lean Meta Elab Term in
private def proveBoundsFor (ref : Syntax) (arrExpr idxNatExpr : Expr) : TermElabM Expr := do
  let sizeExpr ← mkAppM ``Array.size #[arrExpr]
  let goalProp ← mkAppM ``LT.lt #[idxNatExpr, sizeExpr]
  let lctx ← getLCtx
  let (baseArr, sizeEqOpt?) ← proveSizeEqChain lctx arrExpr
  let targetSizeExpr ← mkAppM ``Array.size #[baseArr]
  let baseGoalProp ← mkAppM ``LT.lt #[idxNatExpr, targetSizeExpr]
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

open Lean Meta Elab Term in
private def elabArrAndIdx (arrStx idxStx : Term) (opDesc : String) : TermElabM (Expr × Expr × Expr) := do
  let arrExpr ← elabTerm arrStx none
  let idxNatExpr ← elabTermEnsuringType (← `(Qed.Server.SrvIdx.toNat $idxStx)) (some (mkConst ``Nat))
  synthesizeSyntheticMVarsNoPostponing
  let arrExpr ← instantiateMVars arrExpr
  let idxNatExpr ← instantiateMVars idxNatExpr
  let arrTy ← whnf (← inferType arrExpr)
  unless arrTy.isAppOfArity ``Array 1 do
    throwErrorAt arrStx m!"expected an array (`T[]`) for {opDesc}, got `{← ppExpr arrTy}`"
  return (arrExpr, idxNatExpr, arrTy.getAppArgs[0]!)

open Lean Meta Elab Term in
@[term_elab srvGetElemStx]
def elabSrvGetElem : TermElab := fun stx expectedType? => do
  let (arrExpr, idxNatExpr, elemTy) ← elabArrAndIdx ⟨(stx.getArg 1)⟩ ⟨(stx.getArg 3)⟩ "indexing"
  let ltPrf ← proveBoundsFor stx arrExpr idxNatExpr
  let elemExpr ← mkAppOptM ``srvGetAt #[some elemTy, some arrExpr, some idxNatExpr, some ltPrf]
  match expectedType? with
  | some expTy => ensureHasType expTy elemExpr
  | none       => return elemExpr

open Lean Meta Elab Term in
@[term_elab srvSetElemStx]
def elabSrvSetElem : TermElab := fun stx expectedType? => do
  let valStx : Term := ⟨(stx.getArg 5)⟩
  let (arrExpr, idxNatExpr, elemTy) ← elabArrAndIdx ⟨(stx.getArg 1)⟩ ⟨(stx.getArg 3)⟩ "indexed assignment"
  let valExpr ← elabTermEnsuringType (← `(srvAutoField($valStx))) (some elemTy)
  synthesizeSyntheticMVarsNoPostponing
  let arrExpr ← instantiateMVars arrExpr
  let idxNatExpr ← instantiateMVars idxNatExpr
  let valExpr ← instantiateMVars valExpr
  let ltPrf ← proveBoundsFor stx arrExpr idxNatExpr
  let setExpr ← mkAppOptM ``Array.set #[some elemTy, some arrExpr, some idxNatExpr, some valExpr, some ltPrf]
  match expectedType? with
  | some expTy => ensureHasType expTy setExpr
  | none       => return setExpr

/-! ## Automated Server Invariant Prover (`qedSrvProveStep`, `qedSrvProveAsync`) -/

open Lean Meta in
private def poseInvFactsOnGoal (g0 : MVarId) : MetaM (MVarId × Array FVarId) := do
  let facts ← g0.withContext do
    let goalTy ← instantiateMVars (← g0.getType)
    let lctx ← getLCtx
    let mut scanExprs : Array Expr := #[goalTy]
    let mut forallHyps : Array Expr := #[]
    for decl in lctx do
      if !decl.isImplementationDetail then
        let dty ← instantiateMVars decl.type
        if !isSrvEqDecl decl then
          scanExprs := scanExprs.push dty
        else if let some (_, _, rhs) := dty.eq? then
          if !(rhs.getUsedConstants.any fun c => c == ``Array.set || c == ``Array.push) then
            scanExprs := scanExprs.push dty
        if dty.isForall then forallHyps := forallHyps.push decl.toExpr
    let factsRef ← IO.mkRef (#[] : Array Expr)
    let factSetRef ← IO.mkRef (({} : Std.HashSet Expr))
    let seenRef ← IO.mkRef (({} : Std.HashSet Expr))
    let nextScanRef ← IO.mkRef (#[] : Array Expr)
    let addFact (p : Expr) : MetaM Unit := do
      let s ← factSetRef.get
      unless s.contains p do
        factSetRef.set (s.insert p)
        factsRef.modify (·.push p)
        let pTy ← instantiateMVars (← inferType p)
        nextScanRef.modify (·.push pTy)
    for _ in [0:4] do
      if scanExprs.isEmpty then break
      nextScanRef.set #[]
      for e in scanExprs do
        e.forEach fun sub => do
          unless sub.hasLooseBVars do
            let seen ← seenRef.get
            unless seen.contains sub do
              seenRef.set (seen.insert sub)
              if sub.isAppOfArity ``Array.sumBy 3 then
                let sArgs := sub.getAppArgs
                if sArgs[1]!.isAppOfArity ``Array.set 5 then
                  let setArgs := sArgs[1]!.getAppArgs
                  if let some sumEq ← try
                      some <$> mkAppM ``Array.sumBy_set #[setArgs[1]!, sArgs[2]!, setArgs[2]!, setArgs[3]!, setArgs[4]!]
                    catch _ => pure none then
                    addFact sumEq
              if sub.isAppOfArity ``GetElem.getElem 8 then
                let ltPrf := sub.getAppArgs[7]!
                for fh in forallHyps do
                  if let some elemPrf ← try some <$> mkAppM ``Array.forall_elem #[ltPrf, fh] catch _ => pure none then
                    addFact elemPrf
              inspectFieldOrFin sub addFact
      scanExprs ← nextScanRef.get
    factsRef.get
  let mut g := g0
  let mut fvs : Array FVarId := #[]
  for idx in [0:facts.size] do
    let fPrf := facts[idx]!
    let fTy ← g.withContext (inferType fPrf)
    let (fv, g') ← (← g.assert (Name.mkSimple s!"_invFact{idx}") fTy fPrf).intro1P
    g := g'
    fvs := fvs.push fv
  return (g, fvs)

open Lean Meta Elab Tactic in
private def finishAtomDeepFallback (g : MVarId) : TacticM Bool := do
  let saved ← getGoals
  -- 1. Try `simp [*]` + `omega` (restore if unsuccessful so `g` stays unassigned)
  let s1 ← saveState
  let baseSimp ← getSimpTheorems
  let stWithHyps ← g.withContext do
    let mut st := baseSimp
    for d in (← getLCtx) do
      if !d.isImplementationDetail && !d.isLet then
        if (← try isProp d.type catch _ => pure false) then
          st ← try st.add (.fvar d.fvarId) #[] d.toExpr catch _ => pure st
    return st
  let simpStarCtx ← Simp.mkContext { zetaDelta := false, failIfUnchanged := false } #[stWithHyps] (← getSimpCongrTheorems)
  match ← simpGoalOnly g simpStarCtx with
  | none => setGoals saved; return true
  | some g' =>
      if ← tryDirectOmega g' then setGoals saved; return true
  restoreState s1
  -- 2. Try `simp_all` + basic closers (restore if unsuccessful)
  let s2 ← saveState
  let saCtx ← Simp.mkContext { zetaDelta := false, failIfUnchanged := false } #[baseSimp] (← getSimpCongrTheorems)
  match ← trySimpAll g saCtx #[] with
  | none => setGoals saved; return true
  | some g' =>
      if ← tryCloseBasic g' then setGoals saved; return true
  restoreState s2
  -- 3. Deepest fallback: nonlinear arithmetic or `grind`
  let s3 ← saveState
  setGoals [g]
  let ok ← try
      evalTactic (← `(tactic| first | qedNonlinearClose | grind))
      pure (← getGoals).isEmpty
    catch _ => pure false
  unless ok do restoreState s3
  setGoals saved
  return ok

open Lean Meta Elab Tactic in
private def finishAtomGoal (g0 : MVarId) (allowDeepFallback : Bool := true) : TacticM (Option MVarId) := do
  if ← tryCloseTrivial g0 then return none
  let mut g ← unfoldSrvHelpersGoal g0
  let (preCtx, _) ← mkCachedSimpCtx "finishAtomPre" finishAtomPreSimpNames
  match ← simpGoalOnly g preCtx with
  | none    => return none
  | some g' => g := g'
  let (dcCtx, _) ← mkCachedSimpCtx "dsimpCodec" dsimpCodecUnfoldNames { zetaDelta := false } false true
  match ← simpGoalOnly g dcCtx #[] #[] true true with
  | none    => return none
  | some g' => g := g'
  if ← tryCloseTrivial g then return none
  if ← tryDirectOmega g then return none
  -- Pose refined field / sumBy / forall_elem facts
  let (gPosed, invFactFVars) ← poseInvFactsOnGoal g
  g := gPosed
  unless invFactFVars.isEmpty do
    let (codecCtx, _) ← mkCachedSimpCtx "optCodecDsimp" optCodecSimpNames { zetaDelta := false } false true
    match ← simpGoalOnly g codecCtx #[] invFactFVars false true with
    | none    => return none
    | some g' => g := g'
  match ← simpGoalOnly g dcCtx #[] #[] true true with
  | none    => return none
  | some g' => g := g'
  if ← tryCloseBasic g then return none
  let (fbCtx, _) ← mkCachedSimpCtx "finishAtomFb" finishAtomFallbackSimpNames
  match ← simpGoalOnly g fbCtx with
  | none    => return none
  | some g' => g := g'
  if ← tryCloseBasic g then return none
  if allowDeepFallback then
    if ← finishAtomDeepFallback g then return none
  return some g

open Lean Meta in
private def collectReadySrvLetEqs (e : Expr) : Nat → MetaM (Array Expr)
  | 0 => return #[]
  | fuel + 1 => do
      let e := e.consumeMData
      if e.isAppOfArity ``Qed.Server.srvLetEq 4 then
        let outer := if !e.hasLooseBVars then #[e] else #[]
        return outer ++ (← collectReadySrvLetEqs (e.getAppArgs[2]!) fuel)
      else if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
        collectReadySrvLetEqs (e.getAppArgs[1]!) fuel
      else
        match e with
        | .app f a => return (← collectReadySrvLetEqs f fuel) ++ (← collectReadySrvLetEqs a fuel)
        | .proj _ _ b => collectReadySrvLetEqs b fuel
        | .letE _ _ v _ _ => collectReadySrvLetEqs v fuel
        | .forallE _ d b _ => return (← collectReadySrvLetEqs d fuel) ++ (← collectReadySrvLetEqs b fuel)
        | _ => return #[]

open Lean Meta in
private def tryPickSrvLetEq (gGoal : MVarId) (cands : Array Expr) (revCount : Nat) :
    MetaM (Option (Expr × Expr × MVarId × Nat)) := do
  let tgtNow ← gGoal.withContext (instantiateMVars (← gGoal.getType))
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

open Lean Meta in
private def finishElimSrvLetEq (kFun absBody : Expr) (newGoal : MVarId) (revertedCount : Nat) :
    MetaM MVarId := do
  let idx0 := (← newGoal.withContext getLCtx).size
  let (valName, idx1) ← nextFreshSrvName newGoal "_srvVal" idx0
  let (eqName, _) ← nextFreshSrvName newGoal "_srvEq" idx1
  let (valFVar, g1) ← newGoal.intro valName
  let (eqFVar, g2) ← g1.intro eqName
  let bodyApp := (mkApp2 kFun (mkFVar valFVar) (mkFVar eqFVar)).headBeta
  let reducedGoal := absBody.instantiate1 bodyApp
  let g3 ← tryGoalM g2 (·.change reducedGoal)
  if revertedCount > 0 then
    tryGoalM g3 fun x => Prod.snd <$> x.introN revertedCount
  else
    pure g3

open Lean Meta in
private def elimSrvLetEqGoal (g : MVarId) (allowHyps : Bool := true) : MetaM (Option MVarId) := do
  let tgt ← g.withContext (instantiateMVars (← g.getType))
  let mut picked? : Option (Expr × Expr × MVarId × Nat) := none
  if tgt.getUsedConstants.any (· == ``Qed.Server.srvLetEq) then
    let tgtCands ← collectReadySrvLetEqs tgt 1024
    picked? ← tryPickSrvLetEq g tgtCands 0
  if picked?.isNone && allowHyps then
    let lctx ← g.withContext getLCtx
    for decl in lctx do
      if !decl.isImplementationDetail && !decl.isLet then
        let dty ← g.withContext (instantiateMVars decl.type)
        if dty.getUsedConstants.any (· == ``Qed.Server.srvLetEq) then
          let cands ← collectReadySrvLetEqs dty 1024
          unless cands.isEmpty do
            let s ← saveState
            let attempt? ← try
                let (reverted, gRev) ← g.revert #[decl.fvarId]
                tryPickSrvLetEq gRev cands reverted.size
              catch _ => pure none
            if attempt?.isSome then
              picked? := attempt?
              break
            restoreState s
  let some (kFun, absBody, newGoal, revCount) := picked? | return none
  some <$> finishElimSrvLetEq kFun absBody newGoal revCount

open Lean Meta in
private def elimAllSrvLetEqTarget (g0 : MVarId) : MetaM (MVarId × Bool) := do
  let mut g := g0
  let mut did := false
  for _ in [0:128] do
    match ← elimSrvLetEqGoal g (allowHyps := false) with
    | some g' => g := g'; did := true
    | none    => break
  return (g, did)

open Lean Meta in
private def rewriteTargetByFVar (g : MVarId) (eqFVar : FVarId) : MetaM (Option MVarId) := do
  let s ← saveState
  try
    let tgt ← g.withContext (instantiateMVars (← g.getType))
    let rwRes ← g.withContext (g.rewrite tgt (mkFVar eqFVar))
    let g' ← g.replaceTargetEq rwRes.eNew rwRes.eqProof
    return some g'
  catch _ =>
    restoreState s
    return none

open Lean Meta in
private def mkArrCongrLemmas (elemTy lhs rhs hE : Expr) : MetaM (Expr × Expr) := do
  let sizeLhs ← mkAppM ``Array.size #[lhs]
  withLocalDecl `j .implicit (mkConst ``Nat) fun j => do
    let hjTy ← mkAppM ``LT.lt #[j, sizeLhs]
    withLocalDeclD `hj hjTy fun hj => do
      let p1 ← mkAppOptM ``Qed.Server.getElem_congr_arr #[some elemTy, some rhs, some lhs, some j, some hE, some hj]
      let p2 ← mkAppOptM ``Qed.Server.srvGetAt_congr_arr #[some elemTy, some rhs, some lhs, some j, some hE, some hj]
      return (← mkLambdaFVars #[j, hj] p1, ← mkLambdaFVars #[j, hj] p2)

open Lean Meta in
private def rewriteTargetEqsLinearGoal (g0 : MVarId) : MetaM (Option MVarId) := do
  let mut eqDecls : Array (FVarId × Option (Expr × Expr × Expr) × FVarId) := #[]
  for decl in (← g0.withContext getLCtx) do
    if !decl.isImplementationDetail && !decl.isLet && isSrvEqDecl decl then
      let dty ← g0.withContext (instantiateMVars decl.type)
      if let some (eqTy, lhs, rhs) := dty.eq? then
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
    let tgt ← g.withContext (instantiateMVars (← g.getType))
    if tgt.containsFVar fv then
      let mut progressed := false
      if let some (elemTy, lhs, rhs) := arrInfo? then
        let arrCongrRes ← g.withContext do
          try
            let base ← getCachedSimpThms "arrSetSimp" #[``Array.getElem_set_self, ``Array.getElem_set]
            let (c1, c2) ← mkArrCongrLemmas elemTy lhs rhs (mkFVar eqFv)
            let mut st := base
            st ← st.add (.other `arrCongr1) #[] c1
            st ← st.add (.other `arrCongr2) #[] c2
            let ctx ← Simp.mkContext { zetaDelta := false, failIfUnchanged := false } #[st] (← getSimpCongrTheorems)
            let mut sp : Simp.Simprocs := {}
            sp ← sp.add `reduceIte false
            return some (ctx, #[sp])
          catch _ => return none
        if let some (ctx, sp) := arrCongrRes then
          match ← simpGoalOnly g ctx sp with
          | none    => return none
          | some g' => g := g'; progressed := true
        let tgtAfter ← g.withContext (instantiateMVars (← g.getType))
        if tgtAfter.containsFVar fv then
          if let some g' ← rewriteTargetByFVar g eqFv then
            g := g'; progressed := true
      else
        if let some g' ← rewriteTargetByFVar g eqFv then
          g := g'; progressed := true
      if progressed then
        match ← simpGoalOnly g postRwCtx with
        | none    => return none
        | some g' => g := g'
  return some g

private theorem srv_forall_push {α : Type} {P : α → Prop} {xs : Array α} {v : α}
    (hxs : ∀ x ∈ xs, P x) (hv : P v) : ∀ x ∈ xs.push v, P x :=
  (Array.forall_push (P := P) (xs := xs) (v := v)).2 ⟨hxs, hv⟩

open Lean Meta Elab Tactic in
private def peelArrayForallGoal (g0 : MVarId) (allowDeepFallback : Bool := true) : TacticM (List MVarId) := do
  let emptyDsimpCtx ← Simp.mkContext { failIfUnchanged := false } #[] (← getSimpCongrTheorems)
  let rec loop : Nat → MVarId → TacticM (List MVarId)
    | 0, g => return [g]
    | fuel + 1, g => do
        let some g ← simpGoalOnly g emptyDsimpCtx #[] #[] true true
          | return []
        if ← tryCloseTrivial g then return []
        let tgt ← g.withContext (instantiateMVars (← g.getType))
        let .forallE _ _ (.forallE _ memTy _ _) _ := tgt.consumeMData | return [g]
        unless memTy.consumeMData.isAppOfArity ``Membership.mem 5 do return [g]
        let closeElemAndRecurse (gPrev gElem : MVarId) : TacticM (List MVarId) := do
          let elemRem : List MVarId ← match ← simpGoalOnly gElem emptyDsimpCtx #[] #[] true true with
            | none => pure []
            | some ge1 =>
                match ← rewriteTargetEqsLinearGoal ge1 with
                | none => pure []
                | some ge2 =>
                    match ← finishAtomGoal ge2 allowDeepFallback with
                    | none     => pure []
                    | some ge3 => pure [ge3]
          let prevRem ← loop fuel gPrev
          return prevRem ++ elemRem
        let arrExpr := (memTy.consumeMData.getAppArgs[3]!).consumeMData
        if arrExpr.isAppOfArity ``Array.set 5 then
          let s ← saveState
          match ← try some <$> g.applyConst ``Array.forall_set catch _ => pure none with
          | some [gPrev, gElem] => return ← closeElemAndRecurse gPrev gElem
          | _ => restoreState s
        if arrExpr.isAppOfArity ``Array.push 3 then
          let s ← saveState
          match ← try some <$> g.applyConst ``srv_forall_push catch _ => pure none with
          | some [gPrev, gElem] => return ← closeElemAndRecurse gPrev gElem
          | _ => restoreState s
        if let .fvar fv := arrExpr then
          let lctx ← g.withContext getLCtx
          let mut eqFv? : Option FVarId := none
          for decl in lctx do
            if !decl.isImplementationDetail && !decl.isLet && !decl.userName.hasMacroScopes then
              let dty ← g.withContext (instantiateMVars decl.type)
              if let some (_, lhs, _) := dty.eq? then
                if lhs.consumeMData == .fvar fv then
                  eqFv? := some decl.fvarId
                  break
          if let some eqFv := eqFv? then
            if let some g' ← rewriteTargetByFVar g eqFv then
              return ← loop fuel g'
        if ← g.assumptionCore then return []
        return [g]
  loop 128 g0

open Lean Meta in
private def substMatchEqHypsGoal (g0 : MVarId) : MetaM MVarId := do
  let mut g := g0
  for _ in [0:16] do
    let lctx ← g.withContext getLCtx
    let mut substGoal? : Option MVarId := none
    for decl in lctx do
      if substGoal?.isNone && !decl.isImplementationDetail && !decl.isLet then
        let uname := decl.userName.toString
        if uname.startsWith "_srvMatchEq" || uname.startsWith "_srvSplitH" then
          let dty ← g.withContext (instantiateMVars decl.type)
          if let some (_, lhs, rhs) := dty.eq? then
            if let .fvar fv := rhs.consumeMData then
              let fvMacro := (lctx.find? fv).map (·.userName.hasMacroScopes) |>.getD false
              if fv != decl.fvarId && !lhs.containsFVar fv && (fvMacro || uname.startsWith "_srvMatchEq") then
                let sSub ← saveState
                substGoal? ← g.withContext do
                  try some <$> (Prod.snd <$> Meta.substCore g decl.fvarId (symm := true)) catch _ => restoreState sSub; pure none
            if substGoal?.isNone then
              if let .fvar fv := lhs.consumeMData then
                let fvMacro := (lctx.find? fv).map (·.userName.hasMacroScopes) |>.getD false
                if fv != decl.fvarId && !rhs.containsFVar fv && fvMacro then
                  let sSub ← saveState
                  substGoal? ← g.withContext do
                    try some <$> (Prod.snd <$> Meta.substCore g decl.fvarId (symm := false)) catch _ => restoreState sSub; pure none
    match substGoal? with
    | some g' => g := g'
    | none    => break
  return g

open Lean Meta in
private def splitGoalAnds (g0 : MVarId) : MetaM (List MVarId) := do
  let rec loop : Nat → List MVarId → MetaM (List MVarId)
    | 0, gs => return gs
    | _, [] => return []
    | fuel + 1, g :: rest => do
        let tgt ← g.withContext (instantiateMVars (← g.getType))
        let tgtC := tgt.consumeMData
        if tgtC.isAppOfArity ``And 2 || tgtC.isAppOfArity ``Qed.Lang.QedAndProp 2 then
          let s ← saveState
          match ← try some <$> g.applyConst ``And.intro catch _ => restoreState s; pure none with
          | some [g1, g2] => loop fuel (g1 :: g2 :: rest)
          | _ => restoreState s; return g :: (← loop fuel rest)
        else
          return g :: (← loop fuel rest)
  loop 64 [g0]

open Lean Meta Elab Tactic in
private def closeLeafGoal (g0 : MVarId) (allowDeepFallback : Bool := true) : TacticM (List MVarId) := do
  -- Fast path 0: unwrap `srvWithNewState`, beta/proj-reduce target, and test trivial closure BEFORE touching LCtx!
  let mut g := g0
  let tgt0 ← g.withContext (instantiateMVars (← g.getType))
  if tgt0.consumeMData.isAppOf ``Qed.Server.srvWithNewState then
    let (wCtx, _) ← mkCachedSimpCtx "withNewState" #[``Qed.Server.srvWithNewState_apply]
    match ← simpGoalOnly g wCtx with
    | none    => return []
    | some g' => g := g'
  if ← tryCloseTrivial g then return []
  let emptyDsimpCtx ← Simp.mkContext { failIfUnchanged := false } #[] (← getSimpCongrTheorems)
  match ← simpGoalOnly g emptyDsimpCtx #[] #[] true true with
  | none    => return []
  | some g' => g := g'
  if ← tryCloseTrivial g then return []
  -- Standard leaf pipeline
  g ← tryGoalM g unfoldSrvHelpersGoal
  let (g1, _) ← splitAndHypsGoal g
  g := g1
  match ← tryGoalOptM g simpHypsEachGoal with
  | none    => return []
  | some g' => g := g'
  g ← substMatchEqHypsGoal g
  let tgt1 ← g.withContext (instantiateMVars (← g.getType))
  if tgt1.consumeMData.isAppOf ``Qed.Server.srvWithNewState then
    let (wCtx, _) ← mkCachedSimpCtx "withNewState" #[``Qed.Server.srvWithNewState_apply]
    match ← simpGoalOnly g wCtx with
    | none    => return []
    | some g' => g := g'
  match ← simpGoalOnly g emptyDsimpCtx #[] #[] true true with
  | none    => return []
  | some g' => g := g'
  let (dcCtx, _) ← mkCachedSimpCtx "dsimpCodec" dsimpCodecUnfoldNames { zetaDelta := false } false true
  match ← simpGoalOnly g dcCtx #[] #[] true true with
  | none    => return []
  | some g' => g := g'
  if ← tryCloseTrivial g then return []
  let (g2, didSplit2) ← splitAndHypsGoal g
  g := g2
  if didSplit2 then
    match ← tryGoalOptM g simpHypsEachGoal with
    | none    => return []
    | some g' => g := g'
    g ← substMatchEqHypsGoal g
  let conjuncts ← splitGoalAnds g
  let mut rem : List MVarId := []
  for cg in conjuncts do
    if ← tryCloseTrivial cg then continue
    let peeled ← peelArrayForallGoal cg allowDeepFallback
    for pg in peeled do
      if ← tryCloseTrivial pg then continue
      match ← rewriteTargetEqsLinearGoal pg with
      | none => pure ()
      | some rg =>
          if let some fg ← finishAtomGoal rg allowDeepFallback then
            rem := rem ++ [fg]
  return rem

open Lean Meta in
private def exprHasSplittable (e : Expr) : Bool :=
  e.getUsedConstants.any fun c =>
    c == ``ite || c == ``dite || c.toString.contains ".match_"

open Lean Meta in
private def splitEqHypGoal (g0 : MVarId) : MetaM (Option (List MVarId)) := do
  let lctx ← g0.withContext getLCtx
  let mut idx := lctx.size
  let mut gCur := g0
  let mut eqFVars : Array FVarId := #[]
  for decl in lctx do
    if !decl.isImplementationDetail && !decl.isLet then
      let ty ← gCur.withContext (instantiateMVars decl.type)
      if ty.isEq && exprHasSplittable ty then
        if decl.userName.hasMacroScopes then
          let (cand, nxt) ← nextFreshSrvName gCur "_srvMatchEq" idx
          idx := nxt
          gCur ← gCur.rename decl.fvarId cand
        eqFVars := eqFVars.push decl.fvarId
  for fv in eqFVars do
    if let some sgs ← trySplitLocalDecl gCur fv then
      return some sgs
  return none

open Lean Meta in
private def goalHasSplittableHyp (g : MVarId) : MetaM Bool := do
  let lctx ← g.withContext getLCtx
  for decl in lctx do
    if !decl.isImplementationDetail && !decl.isLet then
      let ty ← g.withContext (instantiateMVars decl.type)
      if ty.getUsedConstants.any (· == ``Qed.Server.srvLetEq) then
        return true
      if ty.isEq && exprHasSplittable ty then
        return true
  return false

open Lean Meta Elab Tactic in
private def proveStepSingleGoal (g0 : MVarId) (allStepCtx stepFloatCtx : Simp.Context) :
    TacticM (List MVarId) := do
  let (_, g1) ← g0.intros
  let some g2 ← simpGoalAllHyps g1 allStepCtx | return []
  let rec stepTargetLoop : Nat → List MVarId → TacticM (List MVarId)
    | 0, gs => return gs
    | _, [] => return []
    | fuel + 1, g :: rest => do
        if ← tryCloseTrivial g then return ← stepTargetLoop fuel rest
        let (gLet, didLet) ← elimAllSrvLetEqTarget g
        if didLet then
          match ← simpGoalOnly gLet stepFloatCtx with
          | none    => return ← stepTargetLoop fuel rest
          | some g' => return ← stepTargetLoop fuel (g' :: rest)
        match ← trySplitTarget g with
        | some sgs =>
            let mut next : List MVarId := []
            for sg in sgs do
              match ← simpGoalOnly sg stepFloatCtx with
              | none     => pure ()
              | some sg' => next := next ++ [sg']
            return ← stepTargetLoop fuel (next ++ rest)
        | none =>
            if !(← goalHasSplittableHyp g) then
              -- No splittable hyps: run full leaf closure directly once!
              let rem ← closeLeafGoal g (allowDeepFallback := true)
              return rem ++ (← stepTargetLoop fuel rest)
            -- Try FAST leaf closure (no `grind`/`simp_all`) BEFORE splitting any Eq hypothesis!
            let s ← saveState
            let leafRem ← closeLeafGoal g (allowDeepFallback := false)
            if leafRem.isEmpty then
              return ← stepTargetLoop fuel rest
            -- Leaf didn't close directly: try eliminating `srvLetEq` in a hyp or splitting a splittable `Eq` hyp
            restoreState s
            if let some gHypLet ← elimSrvLetEqGoal g (allowHyps := true) then
              match ← simpGoalOnly gHypLet stepFloatCtx with
              | none    => return ← stepTargetLoop fuel rest
              | some g' => return ← stepTargetLoop fuel (g' :: rest)
            if let some eqSgs ← splitEqHypGoal g then
              let mut next : List MVarId := []
              for sg in eqSgs do
                match ← simpGoalAllHyps sg stepFloatCtx with
                | none     => pure ()
                | some sg' => next := next ++ [sg']
              return ← stepTargetLoop fuel (next ++ rest)
            -- Nothing left to split: run full leaf closure (including deep fallback)
            let rem ← closeLeafGoal g (allowDeepFallback := true)
            return rem ++ (← stepTargetLoop fuel rest)
  stepTargetLoop 256 [g2]

open Lean Meta Elab Tactic in
private def throwStepFailure (rem : List MVarId) (fnStr lbl : String) : TacticM Unit := do
  let msg ← rem[0]!.withContext do Qed.Diag.ppQedExpr (← rem[0]!.getType)
  let moreNote := if rem.length > 1 then s!"\n  • (+ {rem.length - 1} more obligation(s))" else ""
  if lbl.startsWith "ensures:" then
    let postStr := (lbl.drop 8).toString.trimAscii.toString
    throwError m!"Server postcondition `ensures {postStr}` failed in `{fnStr}`:\n\
      {"  "}• must satisfy:  {msg}{moreNote}\n\n\
      Hint: Ensure every successful return path establishes `{postStr}`."
  else if lbl.startsWith "init:" then
    let invStr := (lbl.drop 5).toString.trimAscii.toString
    throwError m!"Server invariant `{invStr}` failed on initial state:\n\
      {"  "}• must satisfy:  {msg}{moreNote}\n\n\
      Hint: Update the initial `state` values so they satisfy `{invStr}`."
  else if lbl.startsWith "mutating:" then
    let invName := (lbl.drop 9).toString.trimAscii.toString
    throwError m!"Server invariant `{invName}` failed in `{fnStr}`:\n\
      {"  "}• must satisfy:  {msg}{moreNote}\n\n\
      Hint: Add a matching `requires` clause or guard mutations of that field with `if ...:`."
  else
    throwError m!"Server invariant `{lbl}` failed in `{fnStr}`:\n\
      {"  "}• must satisfy:  {msg}{moreNote}\n\n\
      Hint: Guard state mutations with `if ...:` or `requires ...` so this invariant holds across every branch."

open Lean Meta Elab Tactic in
private def runProveStepOnGoals (gs : List MVarId) (userNames : Array Name) (fnStr lbl : String) :
    TacticM Unit := do
  let allStepCtx ← mkDynamicSimpCtx userNames (some ("stepFixed", stepFixedSimpNames))
  let mut rem : List MVarId := []
  for g in gs do
    rem := rem ++ (← proveStepSingleGoal g allStepCtx allStepCtx)
  setGoals rem
  unless rem.isEmpty do
    throwStepFailure rem fnStr lbl

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvProveStep [$[$unfoldIds:ident],*] $fnLabel:str $invLabel:str) => do
      let userNames ← unfoldIds.mapM fun id => resolveGlobalConstNoOverload id
      runProveStepOnGoals (← getGoals) userNames fnLabel.getString invLabel.getString

/-! ## AST-Directed Async Provers (`qedSrvProveAsync`, `qedSrvProveAsyncEnsures`) -/

open Lean Meta in
private def normAsyncContGoal (g0 : MVarId) (dCtx sCtx : Simp.Context) : MetaM (Option MVarId) := do
  let some g1 ← try simpGoalOnly g0 dCtx #[] #[] true true catch _ => pure (some g0) | return none
  try simpGoalOnly g1 sCtx catch _ => return some g1

open Lean Meta in
private def initAsyncGoal (g0 : MVarId) (handlerConst : Name) (dCtx sCtx : Simp.Context) :
    MetaM (Option MVarId) := do
  let (_, g1) ← g0.intros
  let unfoldCtx ← mkDynamicSimpCtx #[handlerConst] (some ("asyncInit", asyncInitSimpNames))
  let some g2 ← try simpGoalOnly g1 unfoldCtx catch _ => pure (some g1) | return none
  normAsyncContGoal g2 dCtx sCtx

open Lean Meta Elab Tactic in
private def tryCloseConstMutInv (g0 : MVarId) : TacticM (Option MVarId) := do
  let (_, g1) ← g0.intros
  let tgt ← g1.withContext (instantiateMVars (← g1.getType))
  let tgtC := tgt.consumeMData
  if tgtC.isAppOfArity ``Qed.Server.ProgPreservesStepRel 5 then
    let relFn := tgtC.getAppArgs[3]!.consumeMData
    -- Pattern: `fun _sOld _sNew => ... ∨ P` where `P` does not depend on `_sOld` or `_sNew`
    if let .lam _ _ (.lam _ _ body _) _ := relFn then
      if body.isAppOfArity ``Or 2 then
        let rhs := body.getAppArgs[1]!
        if !rhs.hasLooseBVars then
          let s ← saveState
          try
            let [gH] ← g1.applyConst ``Qed.Server.progPreservesStepRel_of_const | restoreState s; return some g1
            let (_, gH2) ← gH.introN 2
            let [gR] ← gH2.applyConst ``Or.inr | restoreState s; return some g1
            let rem ← closeLeafGoal gR
            if rem.isEmpty then return none
            restoreState s
          catch _ => restoreState s
  return some g1

open Lean Meta in
private def stepAsyncPreservesLoop (dCtx sCtx : Simp.Context) (gInit : MVarId) :
    MetaM (List MVarId) := do
  let rec loop : Nat → List MVarId → MetaM (List MVarId)
    | 0, gs => return gs
    | _, [] => return []
    | fuel + 1, g :: rest => do
        let tgt ← g.withContext (instantiateMVars (← g.getType))
        let tgtC := tgt.consumeMData
        let isRel := tgtC.isAppOfArity ``Qed.Server.ProgPreservesStepRel 5
        let isInv := tgtC.isAppOfArity ``Qed.Server.ProgPreservesInv 4
        if !isRel && !isInv then
          return g :: (← loop fuel rest)
        let prog := (if isRel then tgtC.getAppArgs[4]! else tgtC.getAppArgs[3]!).consumeMData
        -- 1. Pure
        if prog.isAppOf ``Qed.Server.ThreadProg.pure || prog.isAppOf ``Pure.pure then
          let s ← saveState
          match ← try some <$> g.applyConst ``Qed.Server.ProgPreservesStepRel.pure catch _ => pure none with
          | some [] => return ← loop fuel rest
          | _ => restoreState s
        -- 2. Bind
        if prog.isAppOf ``Bind.bind || prog.isAppOf ``Qed.Server.ThreadProg.bind then
          let pArg := (if prog.isAppOf ``Bind.bind then prog.getAppArgs[4]! else prog.getAppArgs[3]!).consumeMData
          if pArg.isAppOf ``Qed.Server.MonadAtomic.runAtomic then
            let s ← saveState
            match ← try some <$> g.applyConst ``Qed.Server.runAtomic_bind_preservesStepRel catch _ => pure none with
            | some [gCont, gStep] =>
                let (_, gCont1) ← gCont.intro1
                let nextC ← match ← normAsyncContGoal gCont1 dCtx sCtx with | none => pure [] | some c => pure [c]
                return ← loop fuel (nextC ++ [gStep] ++ rest)
            | _ => restoreState s
          else if pArg.isAppOf ``Qed.Server.MonadAtomic.runAtomicRead then
            let s ← saveState
            match ← try some <$> g.applyConst ``Qed.Server.runAtomicRead_bind_preservesStepRel catch _ => pure none with
            | some [gCont, gRefl] =>
                let (_, gCont1) ← gCont.intro1
                let nextC ← match ← normAsyncContGoal gCont1 dCtx sCtx with | none => pure [] | some c => pure [c]
                return ← loop fuel (nextC ++ [gRefl] ++ rest)
            | _ => restoreState s
          else
            let s ← saveState
            match ← try some <$> g.applyConst ``Qed.Server.safeIO_bind_preservesStepRel catch _ => pure none with
            | some [gCont] =>
                let (_, gCont1) ← gCont.intro1
                let nextC ← match ← normAsyncContGoal gCont1 dCtx sCtx with | none => pure [] | some c => pure [c]
                return ← loop fuel (nextC ++ rest)
            | _ => restoreState s
        -- 3. Single runAtomic / runAtomicRead
        if prog.isAppOf ``Qed.Server.MonadAtomic.runAtomic then
          let s ← saveState
          match ← try some <$> g.applyConst ``Qed.Server.progPreservesStepRel_runAtomic catch _ => pure none with
          | some [gStep] => return gStep :: (← loop fuel rest)
          | _ => restoreState s
        if prog.isAppOf ``Qed.Server.MonadAtomic.runAtomicRead then
          let s ← saveState
          match ← try some <$> g.applyConst ``Qed.Server.progPreservesStepRel_runAtomicRead catch _ => pure none with
          | some [gRefl] => return gRefl :: (← loop fuel rest)
          | _ => restoreState s
        -- 4. `srvLetEq`
        if prog.isAppOf ``Qed.Server.srvLetEq then
          if let some gLet ← elimSrvLetEqGoal g (allowHyps := false) then
            let nextL ← match ← normAsyncContGoal gLet dCtx sCtx with | none => pure [] | some c => pure [c]
            return ← loop fuel (nextL ++ rest)
        -- 5. SafeIO whole program (no atomic calls inside)
        if !(prog.getUsedConstants.any fun c => c == ``Qed.Server.MonadAtomic.runAtomic || c == ``Qed.Server.MonadAtomic.runAtomicRead) then
          let s ← saveState
          match ← try some <$> g.applyConst ``Qed.Server.safeIO_preservesStepRel catch _ => pure none with
          | some [] => return ← loop fuel rest
          | _ => restoreState s
        -- 6. Split `ite` / `dite` / `match`
        match ← trySplitTarget g with
        | some sgs =>
            let mut next : List MVarId := []
            for sg in sgs do
              if let some sg' ← normAsyncContGoal sg dCtx sCtx then
                next := next ++ [sg']
            return ← loop fuel (next ++ rest)
        | none =>
            -- Last resort: try `safeIO_preservesStepRel` even if `runAtomic` appeared inside dead code
            let s ← saveState
            match ← try some <$> g.applyConst ``Qed.Server.safeIO_preservesStepRel catch _ => pure none with
            | some [] => return ← loop fuel rest
            | _ => restoreState s; return g :: (← loop fuel rest)
  loop 256 [gInit]

open Lean Meta in
private def stepAsyncEnsuresLoop (dCtx sCtx : Simp.Context) (gInit : MVarId) :
    MetaM (List MVarId) := do
  let rec loop : Nat → List MVarId → MetaM (List MVarId)
    | 0, gs => return gs
    | _, [] => return []
    | fuel + 1, g :: rest => do
        let tgt ← g.withContext (instantiateMVars (← g.getType))
        let tgtC := tgt.consumeMData
        unless tgtC.isAppOfArity ``Qed.Server.ProgEnsures 5 do
          return g :: (← loop fuel rest)
        let prog := tgtC.getAppArgs[4]!.consumeMData
        -- 1. Pure
        if prog.isAppOf ``Qed.Server.ThreadProg.pure then
          let s ← saveState
          match ← try some <$> g.applyConst ``Qed.Server.ProgEnsures.pure catch _ => pure none with
          | some [gPost] => return gPost :: (← loop fuel rest)
          | _ => restoreState s
        if prog.isAppOf ``Pure.pure then
          let s ← saveState
          match ← try some <$> g.applyConst ``Qed.Server.progEnsures_pure catch _ => pure none with
          | some [gPost] => return gPost :: (← loop fuel rest)
          | _ => restoreState s
        -- 2. Bind
        if prog.isAppOf ``Bind.bind || prog.isAppOf ``Qed.Server.ThreadProg.bind then
          let pArg := (if prog.isAppOf ``Bind.bind then prog.getAppArgs[4]! else prog.getAppArgs[3]!).consumeMData
          if pArg.isAppOf ``Qed.Server.MonadAtomic.runAtomic then
            let s ← saveState
            match ← try some <$> g.applyConst ``Qed.Server.runAtomic_bind_ensures catch _ => pure none with
            | some [gCont] =>
                let (_, gCont1) ← gCont.introN 2
                let nextC ← match ← normAsyncContGoal gCont1 dCtx sCtx with | none => pure [] | some c => pure [c]
                return ← loop fuel (nextC ++ rest)
            | _ => restoreState s
          else if pArg.isAppOf ``Qed.Server.MonadAtomic.runAtomicRead then
            let s ← saveState
            match ← try some <$> g.applyConst ``Qed.Server.runAtomicRead_bind_ensures catch _ => pure none with
            | some [gCont] =>
                let (_, gCont1) ← gCont.introN 2
                let nextC ← match ← normAsyncContGoal gCont1 dCtx sCtx with | none => pure [] | some c => pure [c]
                return ← loop fuel (nextC ++ rest)
            | _ => restoreState s
          else
            let s ← saveState
            match ← try some <$> g.applyConst ``Qed.Server.safeIOEnsures_bind catch _ => pure none with
            | some [gCont] =>
                let (_, gCont1) ← gCont.introN 2
                let nextC ← match ← normAsyncContGoal gCont1 dCtx sCtx with | none => pure [] | some c => pure [c]
                return ← loop fuel (nextC ++ rest)
            | _ =>
                restoreState s
                let isBranchP := (pArg.find? fun e =>
                  e.isAppOf ``ite || e.isAppOf ``dite ||
                  (e.getAppFn.constName?.any fun c => c.toString.contains ".match_")).isSome
                if isBranchP then
                  if let some sgs ← trySplitTarget g then
                    let mut next : List MVarId := []
                    for sg in sgs do
                      if let some sg' ← normAsyncContGoal sg dCtx sCtx then
                        next := next ++ [sg']
                    return ← loop fuel (next ++ rest)
                let s2 ← saveState
                match ← try some <$> g.applyConst ``Qed.Server.safeIO_bind_ensures catch _ => pure none with
                | some [gCont] =>
                    let (_, gCont1) ← gCont.intro1
                    let nextC ← match ← normAsyncContGoal gCont1 dCtx sCtx with | none => pure [] | some c => pure [c]
                    return ← loop fuel (nextC ++ rest)
                | _ => restoreState s2
        -- 3. Single runAtomic / runAtomicRead / SafeIOEnsures
        if prog.isAppOf ``Qed.Server.MonadAtomic.runAtomic then
          let s ← saveState
          match ← try some <$> g.applyConst ``Qed.Server.progEnsures_runAtomic catch _ => pure none with
          | some [gStep] => return gStep :: (← loop fuel rest)
          | _ => restoreState s
        if prog.isAppOf ``Qed.Server.MonadAtomic.runAtomicRead then
          let s ← saveState
          match ← try some <$> g.applyConst ``Qed.Server.progEnsures_runAtomicRead catch _ => pure none with
          | some [gStep] => return gStep :: (← loop fuel rest)
          | _ => restoreState s
        let sEns ← saveState
        match ← try some <$> g.applyConst ``Qed.Server.safeIOEnsures_final catch _ => pure none with
        | some [gImp] => return gImp :: (← loop fuel rest)
        | _ => restoreState sEns
        -- 4. `srvLetEq`
        if prog.isAppOf ``Qed.Server.srvLetEq then
          if let some gLet ← elimSrvLetEqGoal g (allowHyps := false) then
            let nextL ← match ← normAsyncContGoal gLet dCtx sCtx with | none => pure [] | some c => pure [c]
            return ← loop fuel (nextL ++ rest)
        -- 5. Split `ite` / `dite` / `match`
        match ← trySplitTarget g with
        | some sgs =>
            let mut next : List MVarId := []
            for sg in sgs do
              if let some sg' ← normAsyncContGoal sg dCtx sCtx then
                next := next ++ [sg']
            return ← loop fuel (next ++ rest)
        | none =>
            return g :: (← loop fuel rest)
  loop 256 [gInit]

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvProveAsync $handlerId:ident [$[$invUnfoldIds:ident],*] $fnLabel:str $invLabel:str) => do
      let g0 ← getMainGoal
      -- Fast path: `mutating <fld> requires <P>` where `<P>` already holds from `requires` hypotheses!
      let some g1 ← tryCloseConstMutInv g0 | replaceMainGoal []; return
      let handlerConst ← resolveGlobalConstNoOverload handlerId
      let userNames ← invUnfoldIds.mapM fun id => resolveGlobalConstNoOverload id
      let (dCtx, _) ← mkCachedSimpCtx "asyncDsimp" asyncDsimpNames { zetaDelta := false } false true
      let (sCtx, _) ← mkCachedSimpCtx "asyncNorm" asyncNormSimpNames
      let some gInit ← initAsyncGoal g1 handlerConst dCtx sCtx | replaceMainGoal []; return
      let leafGoals ← stepAsyncPreservesLoop dCtx sCtx gInit
      runProveStepOnGoals leafGoals userNames fnLabel.getString invLabel.getString

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvProveAsyncEnsures $handlerId:ident [$[$invUnfoldIds:ident],*] $fnLabel:str $invLabel:str) => do
      let g0 ← getMainGoal
      let handlerConst ← resolveGlobalConstNoOverload handlerId
      let userNames ← invUnfoldIds.mapM fun id => resolveGlobalConstNoOverload id
      let (dCtx, _) ← mkCachedSimpCtx "asyncDsimp" asyncDsimpNames { zetaDelta := false } false true
      let (sCtx, _) ← mkCachedSimpCtx "asyncNorm" asyncNormSimpNames
      let some gInit ← initAsyncGoal g0 handlerConst dCtx sCtx | replaceMainGoal []; return
      let leafGoals ← stepAsyncEnsuresLoop dCtx sCtx gInit
      runProveStepOnGoals leafGoals userNames fnLabel.getString invLabel.getString

/-! ## Client RPC Precondition Prover (`qedProveRpcReq`) -/

open Lean Meta Elab Tactic in
private def closeRpcReqLeaf (g0 : MVarId) : TacticM (Option MVarId) := do
  let (g, _) ← try splitAndHypsGoal g0 catch _ => pure (g0, false)
  if ← tryCloseBasic g then return none
  let baseSimp ← getSimpTheorems
  let saCtx ← Simp.mkContext { zetaDelta := true, zetaHave := true, failIfUnchanged := false } #[baseSimp] (← getSimpCongrTheorems)
  match ← trySimpAll g saCtx #[] with
  | none    => return none
  | some g' =>
      if ← tryCloseBasic g' then return none
      let saved ← getGoals
      let s ← saveState
      setGoals [g']
      let ok ← try
          evalTactic (← `(tactic| first | qedNonlinearClose | grind))
          pure (← getGoals).isEmpty
        catch _ => pure false
      unless ok do restoreState s
      setGoals saved
      return if ok then none else some g'

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedProveRpcReq) => do
      let g0 ← getMainGoal
      if ← tryCloseBasic g0 then replaceMainGoal []; return
      let (g1, _) ← try splitAndHypsGoal g0 catch _ => pure (g0, false)
      let mut g := g1
      g ← try unfoldSrvHelpersGoal g catch _ => pure g
      let dsimpAllCtx ← Simp.mkContext { failIfUnchanged := false } #[] (← getSimpCongrTheorems)
      let allFVars ← g.withContext do
        let mut arr : Array FVarId := #[]
        for d in (← getLCtx) do
          if !d.isImplementationDetail then arr := arr.push d.fvarId
        return arr
      match ← try simpGoalOnly g dsimpAllCtx #[] allFVars true true catch _ => pure (some g) with
      | none    => replaceMainGoal []; return
      | some g' => g := g'
      let facts ← g.withContext do
        let tgt ← instantiateMVars (← g.getType)
        collectProofFacts #[tgt]
      for idx in [0:facts.size] do
        let fPrf := facts[idx]!
        let fTy ← g.withContext (inferType fPrf)
        let (_, g') ← (← g.assert (Name.mkSimple s!"_reqFact{idx}") fTy fPrf).intro1P
        g := g'
      g ← try unfoldSrvHelpersGoal g catch _ => pure g
      let (abCtx, _) ← mkCachedSimpCtx "arrayAndBool" arrayAndBoolSimpNames { zetaDelta := true }
      match ← simpGoalAllHyps g abCtx with
      | none    => replaceMainGoal []; return
      | some g' => g := g'
      let (reqCtx, _) ← mkCachedSimpCtx "rpcReq" rpcReqSimpNames { zetaDelta := true, zetaHave := true }
      match ← simpGoalAllHyps g reqCtx with
      | none    => replaceMainGoal []; return
      | some g' => g := g'
      let (dcCtx, _) ← mkCachedSimpCtx "dsimpCodec" dsimpCodecUnfoldNames { zetaDelta := false } false true
      match ← try simpGoalOnly g dcCtx #[] #[] true true catch _ => pure (some g) with
      | none    => replaceMainGoal []; return
      | some g' => g := g'
      let conjuncts ← splitGoalAnds g
      let mut rem : List MVarId := []
      for cg in conjuncts do
        if let some fg ← closeRpcReqLeaf cg then
          rem := rem ++ [fg]
      setGoals rem
      unless rem.isEmpty do
        let msg ← rem[0]!.withContext do Qed.Diag.ppQedExpr (← rem[0]!.getType)
        throwError m!"Server `requires` precondition could not be proved:\n  • must satisfy:  {msg}\n\n\
          Hint: Guard this RPC call with `if ...:` so the precondition holds."

end Qed.Server
