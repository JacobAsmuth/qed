import Lean
import Qed.Lang
import Qed.Diag
import Qed.Collection

namespace Qed.Verify.Core

open Lean Meta Elab Tactic

/-! ## Shared Simp Name Tables -/

def boolSimpNames : Array Name := #[
  ``Bool.and_eq_true, ``Bool.or_eq_true, ``Bool.not_eq_true',
  ``beq_iff_eq, ``bne_iff_ne, ``decide_eq_true_eq]

def boolConstSimpNames : Array Name := #[
  ``Bool.true_and, ``Bool.and_true, ``Bool.false_and, ``Bool.and_false,
  ``Bool.true_or, ``Bool.or_true, ``Bool.false_or, ``Bool.or_false,
  ``Bool.not_false, ``Bool.not_true, ``ite_true, ``ite_false, ``dite_true, ``dite_false]

def dictSimpNames : Array Name := #[
  `Qed.Dict.emptyCollection_eq_empty, `Qed.Dict.getElem_eq_get,
  `Qed.Lang.QedMem.mem_dict, `Qed.Lang.QedMemProp.memProp_dict,
  `Qed.Dict.get_empty, `Qed.Dict.contains_empty, `Qed.Dict.size_empty, `Qed.Dict.isEmpty_empty,
  `Qed.Dict.get_set, `Qed.Dict.get_set_self, `Qed.Dict.contains_set, `Qed.Dict.contains_set_self,
  `Qed.Dict.get_remove, `Qed.Dict.get_remove_self, `Qed.Dict.contains_remove, `Qed.Dict.contains_remove_self,
  `Qed.Dict.size_set, `Qed.Dict.isEmpty_iff_size]

def optCodecSimpNames : Array Name := #[
  `Qed.Codec.valid, `Qed.Codec.refine, `Qed.Codec.jsonOnly, `Qed.Codec.text,
  `Qed.Codec.textarea, `Qed.Codec.nat, `Qed.Codec.int, `Qed.Codec.checkbox, `Qed.Codec.date]

def valUnwrapBaseNames : Array Name := #[
  `Qed.QedVal.val_field, `Qed.QedVal.val_ensured, ``Qed.Lang.QedVal.val_id]

def appPassThroughWrappers : Array Name := #[
  `Qed.Internal.App.withQueries, `Qed.Internal.App.withSubscriptions,
  `Qed.Internal.App.withStylesheets, `Qed.Internal.App.withExtraStyles,
  `Qed.App.withHead, `Qed.App.withSsrStatus]

def appWrapperBases : Array Name :=
  #[`Qed.Internal.mkApp, `Qed.Internal.mkRoutedApp, `Qed.Internal.App.withDehydrate] ++
  appPassThroughWrappers

/-- Expands `appWrapperBases` with each suffix (`"init"`, `"update"`, `"template"`, `"dehydrate"`,
    `"rehydrate"`), keeping only declarations present in `env`. -/
def appProjSimpNames (env : Environment) (suffixes : Array String) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for base in appWrapperBases do
    for suf in suffixes do
      let nm := base.appendAfter s!"_{suf}"
      if env.contains nm then out := out.push nm
  return out

/-- Base simp rules for `Qed.Server.Db` policy & invariant proofs (Wave 3 entry point). -/
def dbBaseSimpNames : Array Name :=
  boolSimpNames ++ valUnwrapBaseNames ++ #[
    ``Option.isSome_iff_ne_none, ``Option.getD_some, `Qed.Server.Db.some_getD_eq_self_iff,
    ``true_and, ``and_true, ``false_or, ``or_false, ``true_or, ``or_true, ``id_eq, ``ne_eq]

/-! ## Cached `Simp.Context` & Simproc Builders -/

def addSimpNamesWithEqns (st : SimpTheorems) (names : Array Name) (dsimpOnly : Bool := false)
    (withEqns : Bool := false) : MetaM (SimpTheorems × Array Name) := do
  let env ← getEnv
  let mut st := st
  let mut eqnsAdded : Array Name := #[]
  for n in names do
    if let some ci := env.find? n then
      match ci with
      | .thmInfo _ => unless dsimpOnly do st ← st.addConst n
      | _ =>
          st ← st.addDeclToUnfold n
          if withEqns && !dsimpOnly then
            if let some eqns ← getEqnsFor? n then
              for eq in eqns do
                st ← st.addConst eq
                eqnsAdded := eqnsAdded.push eq
  return (st, eqnsAdded)

def addSimpNames (st : SimpTheorems) (names : Array Name) (dsimpOnly : Bool := false)
    (withEqns : Bool := false) : MetaM SimpTheorems :=
  Prod.fst <$> addSimpNamesWithEqns st names dsimpOnly withEqns

initialize simpThmsCache :
    IO.Ref (Std.HashMap (String × Name × Bool × Bool) (SimpTheorems × Array Name)) ← IO.mkRef {}

initialize simprocsCache : IO.Ref (Std.HashMap (Array Name × Bool) Simp.SimprocsArray) ← IO.mkRef {}

def getCachedSimprocs (names : Array Name) (post : Bool := true) : MetaM Simp.SimprocsArray := do
  if names.isEmpty then return #[]
  let key := (names, post)
  if let some sp := (← simprocsCache.get).get? key then return sp
  let env ← getEnv
  let mut sp : Simp.Simprocs := {}; let mut anyAdded := false
  for n in names do
    if env.contains n then sp ← sp.add n post; anyAdded := true
  let arr := if anyAdded then #[sp] else #[]
  if anyAdded then simprocsCache.modify (·.insert key arr)
  return arr

def getCachedSimpThms (key : String) (names : Array Name) (dsimpOnly : Bool := false)
    (withEqns : Bool := true) : MetaM SimpTheorems := do
  let env ← getEnv
  let cacheKey := (key, env.header.mainModule, dsimpOnly, env.contains `Qed.Codec.valid)
  if let some (st, needed) := (← simpThmsCache.get).get? cacheKey then
    if needed.all env.contains then return st
  let (st, eqns) ← addSimpNamesWithEqns {} names dsimpOnly withEqns
  simpThmsCache.modify (·.insert cacheKey (st, eqns))
  return st

private def mkSimpCtx (cfg : Simp.Config) (thms : Array SimpTheorems) : MetaM Simp.Context := do
  Simp.mkContext { cfg with failIfUnchanged := false } thms (← getSimpCongrTheorems)

def mkCachedSimpCtx (key : String) (names : Array Name)
    (cfg : Simp.Config := { zetaDelta := false }) (simprocNames : Array Name := #[])
    (dsimpOnly : Bool := false) (withEqns : Bool := true) :
    MetaM (Simp.Context × Simp.SimprocsArray) := do
  return (← mkSimpCtx cfg #[← getCachedSimpThms key names dsimpOnly withEqns],
          ← getCachedSimprocs simprocNames)

def mkDynamicSimpCtx (extraNames : Array Name) (baseKey? : Option (String × Array Name) := none)
    (cfg : Simp.Config := { zetaDelta := false }) (dsimpOnly : Bool := false)
    (withEqns : Bool := true) : MetaM Simp.Context := do
  let baseSt ← match baseKey? with
    | some (k, ns) => getCachedSimpThms k ns dsimpOnly withEqns
    | none         => pure {}
  mkSimpCtx cfg #[← addSimpNames baseSt extraNames dsimpOnly withEqns]

def mkEmptyDsimpCtx (cfg : Simp.Config := {}) : MetaM Simp.Context :=
  mkSimpCtx cfg #[]

def mkSimpCtxWithBase (extraNames : Array Name := #[]) (cfg : Simp.Config := {})
    (cacheKey? : Option String := none) (withEqns : Bool := false) : MetaM Simp.Context := do
  let base ← getSimpTheorems
  let thms ← if extraNames.isEmpty then pure #[base]
    else match cacheKey? with
      | some k => pure #[base, ← getCachedSimpThms k extraNames false withEqns]
      | none   => pure #[← addSimpNames base extraNames false withEqns]
  mkSimpCtx cfg thms

/-! ## MetaM & TacticM Goal Helpers -/

def tryRestoreM {m : Type → Type} {s α : Type} [Monad m] [MonadBacktrack s m] [MonadExcept Exception m]
    (fail : α) (ok : α → Bool) (k : m α) : m α := do
  let st ← saveState
  try
    let r ← k
    unless ok r do restoreState st
    return r
  catch _ => restoreState st; return fail

def tryGoalM (g : MVarId) (k : MVarId → MetaM MVarId) : MetaM MVarId :=
  tryRestoreM g (fun _ => true) (k g)

def tryGoalOptM (g : MVarId) (k : MVarId → MetaM (Option MVarId)) : MetaM (Option MVarId) :=
  tryRestoreM (some g) (fun _ => true) (k g)

def simpGoalOnly (g : MVarId) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray := #[])
    (fvarIds : Array FVarId := #[]) (simplifyTarget : Bool := true) (dsimpOnly : Bool := false) :
    MetaM (Option MVarId) :=
  tryGoalOptM g fun g => do
    if dsimpOnly then return (← dsimpGoal g ctx simprocs simplifyTarget fvarIds).1
    return (← simpGoal g ctx simprocs none simplifyTarget fvarIds).1.map Prod.snd

def allUserFVars (g : MVarId) : MetaM (Array FVarId) := g.withContext do
  return (← getLCtx).foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d.fvarId

def simpGoalAllHyps (g : MVarId) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray := #[])
    (dsimpOnly : Bool := false) : MetaM (Option MVarId) := do
  simpGoalOnly g ctx simprocs (← allUserFVars g) true dsimpOnly

def trySimpAll (g : MVarId) (ctx : Simp.Context) (sp : Simp.SimprocsArray := #[]) :
    MetaM (Option MVarId) :=
  tryGoalOptM g fun g => return (← simpAll g ctx sp).1

def trySplitTarget (g : MVarId) : MetaM (Option (List MVarId)) :=
  tryRestoreM none Option.isSome (g.withContext (Meta.splitTarget? g))

def trySplitLocalDecl (g : MVarId) (fv : FVarId) : MetaM (Option (List MVarId)) :=
  tryRestoreM none Option.isSome (g.withContext (Meta.splitLocalDecl? g fv))

def tryApplyConst (g : MVarId) (c : Name) : MetaM (Option (List MVarId)) :=
  tryRestoreM none (fun _ => true) (some <$> g.applyConst c)

def tryReflGoal (g : MVarId) : MetaM Bool :=
  tryRestoreM false id (do g.refl; return true)

def tryTac (mk : TacticM (TSyntax `tactic)) (requireClosed : Bool := false) : TacticM Bool :=
  tryRestoreM false id do
    withoutRecover <| evalTactic (← mk)
    return !requireClosed || (← getGoals).isEmpty

def forEachGoal (f : MVarId → TacticM Unit) : TacticM Unit := do
  let mut rem : List MVarId := []
  for g in (← getGoals) do
    setGoals [g]; f g; rem := rem ++ (← getGoals)
  setGoals rem

/-- Extract the collection expression `xs` from a goal of shape `∀ c ∈ xs, P c`. -/
def extractForEachColl? (tgt : Expr) : Option Expr :=
  match tgt.consumeMData with
  | .forallE _ _ (.forallE _ memTy _ _) _ =>
      let memTy := memTy.consumeMData
      if memTy.isAppOfArity ``Membership.mem 5 then some memTy.getAppArgs[3]!.consumeMData else none
  | _ => none

def collectGoalConsts (g : MVarId) (includeLCtx : Bool := false) : MetaM (Std.HashSet Name) :=
  g.withContext do
    let mut s := (← instantiateMVars (← g.getType)).getUsedConstants.foldl (·.insert ·) {}
    if includeLCtx then
      for d in (← getLCtx) do
        if !d.isImplementationDetail then
          s := (← instantiateMVars d.type).getUsedConstants.foldl (·.insert ·) s
    return s

def assertFacts (g0 : MVarId) (pfx : String) (facts : Array Expr) : MetaM (MVarId × Array FVarId) := do
  let mut g := g0; let mut fvs : Array FVarId := #[]
  for idx in [0:facts.size] do
    let fPrf := facts[idx]!
    let (fv, g') ← (← g.assert (Name.mkSimple s!"{pfx}{idx}") (← g.withContext (inferType fPrf)) fPrf).intro1P
    g := g'; fvs := fvs.push fv
  return (g, fvs)

def namesToSimpLemmas (ns : Array Name) : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :=
  ns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)

def termsToSimpLemmas (ts : Array Term) : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :=
  ts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)

/-! ## Unified Refinement & Collection Fact Scanner -/

def isKnownNonRefinedHead (c : Name) : Bool :=
  c == ``Nat || c == ``Int || c == ``String || c == ``Bool || c == ``Unit ||
  c == ``ByteArray || c == ``Char || c == ``UInt8 || c == ``UInt16 ||
  c == ``UInt32 || c == ``UInt64 || c == ``USize || c == ``Array || c == ``List ||
  c == ``Option || c == ``Except || c == ``Prod || c == ``Eq || c == ``And ||
  c == ``Or || c == ``Not || c == ``LT.lt || c == ``LE.le || c == ``True ||
  c == ``False || c == `Qed.Server.RequestCtx || c == `Qed.Server.ApiError || c == `Qed.Server.WsEmit

structure FactScanConfig where
  scanLCtx : Bool := true
  scanLCtxValues : Bool := false
  includeMacroPropHyps : Bool := false
  includeFin : Bool := true
  includeDictRemove : Bool := false
  includeCollectionRules : Bool := false
  rounds : Nat := 1
  skipDecl : LocalDecl → Expr → Bool := fun _ _ => false

private def tryEmitFieldOrFin (env : Environment) (includeFin : Bool) (sub ty : Expr)
    (addFact : Expr → MetaM Unit) : MetaM Bool := do
  let emit (c : Name) : MetaM Unit := do
    if env.contains c then
      if let some p ← try some <$> mkAppM c #[sub] catch _ => pure none then addFact p
  if ty.isAppOfArity `Qed.Field 2 || ty.isAppOfArity `Qed.Ensured 2 then
    emit `Qed.Field.ok; return true
  if includeFin && ty.isAppOfArity ``Fin 1 then emit ``Fin.isLt; return true
  return false

private def inspectSubtermForFacts (env : Environment) (cfg : FactScanConfig)
    (forallHyps : Array Expr) (sub : Expr) (addFact : Expr → MetaM Unit) : MetaM Unit := do
  if sub.hasLooseBVars then return
  match sub with
  | .sort _ | .lit _ | .mvar _ | .bvar _ | .forallE .. | .lam .. => return
  | _ => pure ()
  if cfg.includeCollectionRules && sub.isAppOfArity ``Array.sumBy 3 then
    let sArgs := sub.getAppArgs
    if sArgs[1]!.isAppOfArity ``Array.set 5 then
      let a := sArgs[1]!.getAppArgs
      if let some p ← try some <$> mkAppM ``Array.sumBy_set #[a[1]!, sArgs[2]!, a[2]!, a[3]!, a[4]!] catch _ => pure none then addFact p
  if (cfg.includeDictRemove || cfg.includeCollectionRules) &&
      sub.isAppOfArity `Qed.Dict.remove 5 && env.contains `Qed.Dict.size_remove_le then
    let a := sub.getAppArgs
    if let some p ← try some <$> mkAppM `Qed.Dict.size_remove_le #[a[3]!, a[4]!] catch _ => pure none then addFact p
  if cfg.includeCollectionRules && sub.isAppOfArity ``GetElem.getElem 8 then
    for fh in forallHyps do
      if let some p ← try some <$> mkAppM ``Array.forall_elem #[sub.getAppArgs[7]!, fh] catch _ => pure none then addFact p
  let some t ← try some <$> inferType sub catch _ => pure none | return
  let tC := t.consumeMData
  if ← tryEmitFieldOrFin env cfg.includeFin sub tC addFact then return
  match tC.getAppFn with
  | .sort _ | .forallE .. => return
  | .const c _ => if isKnownNonRefinedHead c then return
  | _ => pure ()
  if let some ty ← try some <$> whnf tC catch _ => pure none then
    let _ ← tryEmitFieldOrFin env cfg.includeFin sub ty addFact

/-- Scans `extraExprs` (and optionally the local context) for `Field.ok`, `Ensured.ok`,
    `Fin.isLt`, `Dict.size_remove_le`, `Array.sumBy_set`, and `Array.forall_elem` facts. -/
def collectFacts (cfg : FactScanConfig := {}) (extraExprs : Array Expr := #[]) : MetaM (Array Expr) := do
  let env ← getEnv
  let factsRef ← IO.mkRef (#[] : Array Expr)
  let factSetRef ← IO.mkRef (({} : Std.HashSet Expr))
  let seenRef ← IO.mkRef (({} : Std.HashSet Expr))
  let nextScanRef ← IO.mkRef (#[] : Array Expr)
  let addFact (p : Expr) : MetaM Unit := do
    unless (← factSetRef.get).contains p do
      factSetRef.modify (·.insert p); factsRef.modify (·.push p)
      if cfg.rounds > 1 then nextScanRef.modify (·.push (← instantiateMVars (← inferType p)))
  let mut scanExprs : Array Expr := #[]
  let mut forallHyps : Array Expr := #[]
  if cfg.scanLCtx then
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        let dty ← instantiateMVars decl.type
        if cfg.includeMacroPropHyps && !decl.isLet && decl.userName.hasMacroScopes then
          if (← try isProp dty catch _ => pure false) then addFact decl.toExpr
        unless cfg.skipDecl decl dty do
          if cfg.scanLCtxValues then
            scanExprs := scanExprs.push decl.toExpr
            if let some val := decl.value? then scanExprs := scanExprs.push val
          else scanExprs := scanExprs.push dty
        if cfg.includeCollectionRules && dty.isForall then forallHyps := forallHyps.push decl.toExpr
  for e in extraExprs do scanExprs := scanExprs.push (← instantiateMVars e)
  for _ in [0:cfg.rounds] do
    if scanExprs.isEmpty then break
    nextScanRef.set #[]
    for e in scanExprs do
      e.forEach fun sub => do
        unless sub.hasLooseBVars || (← seenRef.get).contains sub do
          seenRef.modify (·.insert sub)
          inspectSubtermForFacts env cfg forallHyps sub addFact
    scanExprs ← nextScanRef.get
  factsRef.get

def collectAndAssertFacts (g0 : MVarId) (pfx : String) (cfg : FactScanConfig := {}) :
    MetaM (MVarId × Array FVarId) := do
  assertFacts g0 pfx (← g0.withContext do collectFacts cfg #[← instantiateMVars (← g0.getType)])

/-! ## Direct MetaM Closers & Unified Fallback Pipeline -/

def tryCloseTrivial (g : MVarId) (skipTarget : Expr → Bool := fun _ => false)
    (reducibleOnly : Bool := false) : MetaM Bool := do
  let tgtC := (← g.withContext do instantiateMVars (← g.getType)).consumeMData
  if tgtC.isConstOf ``True then g.assign (mkConst ``True.intro); return true
  if skipTarget tgtC then return false
  if reducibleOnly then
    return ← g.withContext <| withTransparency .reducible do
      if let some (_, lhs, rhs) := tgtC.eq? then
        if ← isDefEq lhs rhs then g.assign (← mkEqRefl lhs); return true
      for d in (← getLCtx) do
        if !d.isImplementationDetail && (← isDefEq d.type tgtC) then
          g.assign (mkFVar d.fvarId); return true
      return false
  if tgtC.isAppOfArity ``Eq 3 then if ← tryReflGoal g then return true
  if tgtC.isAppOfArity ``LE.le 4 || tgtC.isAppOfArity ``GE.ge 4 then
    let args := tgtC.getAppArgs
    if args[2]! == args[3]! then
      if ← tryRestoreM false id (return (← g.applyConst ``Nat.le_refl).isEmpty) then return true
  if ← g.assumptionCore then return true
  if tgtC.isAppOfArity ``Or 2 then
    if ← tryRestoreM false id (do match ← g.applyConst ``Or.inl with | [gL] => gL.refl; return true | _ => return false) then return true
    if ← tryRestoreM false id (do match ← g.applyConst ``Or.inr with | [gR] => gR.assumptionCore | _ => return false) then return true
  return false

def tryDirectDecide (g : MVarId) : MetaM Bool := do
  let tgt ← g.withContext do instantiateMVars (← g.getType)
  if tgt.hasFVar || tgt.hasMVar then return false
  tryRestoreM false id <| g.withContext do
    let decInst ← synthInstance (mkApp (mkConst ``Decidable) tgt)
    if ← isDefEq (mkApp2 (mkConst ``Decidable.decide) tgt decInst) (mkConst ``Bool.true) then
      g.assign (mkApp3 (mkConst ``of_decide_eq_true) tgt decInst (← mkEqRefl (mkConst ``Bool.true)))
      return true
    return false

def tryDirectOmega (g : MVarId) : MetaM Bool :=
  tryRestoreM false id do
    let some g' ← g.falseOrByContra | return true
    g'.withContext do Omega.omega ((← getPropHyps).toList.map mkFVar) g' {}
    return true

def tryCloseBasic (g : MVarId) (skipTarget : Expr → Bool := fun _ => false)
    (reducibleOnly : Bool := false) : MetaM Bool := do
  if ← tryCloseTrivial g skipTarget reducibleOnly then return true
  if ← tryDirectDecide g then return true
  tryDirectOmega g

def splitAndHypsGoal (g0 : MVarId) (existsOnly : Bool := false) (maxIters : Nat := 32) :
    MetaM (MVarId × Bool) := do
  let isMatchTy (t : Expr) : Bool :=
    t.isAppOfArity ``Exists 2 || (!existsOnly && (t.isAppOfArity ``And 2 || t.isAppOfArity ``Qed.Lang.QedAndProp 2))
  let mut g := g0; let mut didSplit := false
  for _ in [0:maxIters] do
    let mut nextG? : Option MVarId := none
    for decl in (← g.withContext getLCtx) do
      if nextG?.isNone && !decl.isImplementationDetail && !decl.isLet then
        let tC := decl.type.consumeMData
        let maybe := isMatchTy tC || match tC.getAppFn with | .const c _ => !isKnownNonRefinedHead c | _ => true
        if maybe then
          if let some g' ← tryRestoreM none Option.isSome do
              if isMatchTy (← g.withContext (whnf tC)) then
                return ((← g.cases decl.fvarId)[0]?).map (·.mvarId)
              return none then
            nextG? := some g'; didSplit := true
    match nextG? with | some g' => g := g' | none => break
  return (g, didSplit)

def splitGoalAnds (g0 : MVarId) (maxIters : Nat := 64) : MetaM (List MVarId) := do
  let rec loop : Nat → List MVarId → MetaM (List MVarId)
    | 0, gs => return gs
    | _, [] => return []
    | fuel + 1, g :: rest => do
        let tgtC := (← g.withContext (instantiateMVars (← g.getType))).consumeMData
        if tgtC.isAppOfArity ``And 2 || tgtC.isAppOfArity ``Qed.Lang.QedAndProp 2 then
          if let some [g1, g2] ← tryApplyConst g ``And.intro then return ← loop fuel (g1 :: g2 :: rest)
        return g :: (← loop fuel rest)
  loop maxIters [g0]

def tryDeepFallbackTactic (g : MVarId) (extraSimpAll : Array Name := #[]) : TacticM Bool := do
  let saved ← getGoals; setGoals [g]
  let ok ← tryTac (requireClosed := true) do
    let simpArgs ← namesToSimpLemmas extraSimpAll
    `(tactic|
      first
        | qedNonlinearClose
        | (try simp_all [$[$simpArgs],*];
           try (repeat' (split <;> try simp_all [$[$simpArgs],*]));
           all_goals (first | omega | decide | rfl))
        | grind)
  setGoals saved; return ok

structure CloseFallbackConfig where
  skipTarget : Expr → Bool := fun _ => false
  trySimpStarOmega : Bool := false
  simpAllCfg : Simp.Config := { zetaDelta := false }
  simpAllExtra : Array Name := #[]
  simpAllSimprocs : Array Name := #[]
  tryDeepFallback : Bool := true
  deepExtraSimpAll : Array Name := #[]

def closeWithFallback (g : MVarId) (cfg : CloseFallbackConfig := {}) : TacticM Bool := do
  if cfg.trySimpStarOmega then
    if ← tryRestoreM false id do
      let stWithHyps ← g.withContext do
        let mut st ← getSimpTheorems
        for d in (← getLCtx) do
          if !d.isImplementationDetail && !d.isLet && (← try isProp d.type catch _ => pure false) then
            st ← try st.add (.fvar d.fvarId) #[] d.toExpr catch _ => pure st
        return st
      let ctx ← mkSimpCtx cfg.simpAllCfg #[stWithHyps]
      match ← simpGoalOnly g ctx with | none => return true | some g' => tryDirectOmega g'
    then return true
  if ← tryRestoreM false id do
    let saCtx ← mkSimpCtxWithBase cfg.simpAllExtra cfg.simpAllCfg
    match ← trySimpAll g saCtx (← getCachedSimprocs cfg.simpAllSimprocs) with
    | none => return true
    | some g' => tryCloseBasic g' cfg.skipTarget
  then return true
  if cfg.tryDeepFallback then tryDeepFallbackTactic g cfg.deepExtraSimpAll else return false

/-! ## Wave 3 Public Entry Point (`Qed.Server.Db` & General Unfold-and-Solve Provers) -/

/-- Intros hypotheses, `dsimp`s `unfoldNames`, then runs `simp only` (`at *`) and `simp_all only`
    using cached `Simp.Context` + `simprocNames`. Returns `none` if the goal closes. -/
def simplifyWithUnfolds (g0 : MVarId) (unfoldNames extraSimpNames : Array Name)
    (simprocNames : Array Name := #[]) (simpCfg : Simp.Config := { zetaDelta := true }) :
    MetaM (Option MVarId) := do
  let (_, g1) ← g0.intros
  let sp ← getCachedSimprocs simprocNames
  let g2 ← if unfoldNames.isEmpty then pure g1 else do
    let some g' ← simpGoalAllHyps g1 (← mkDynamicSimpCtx unfoldNames none simpCfg true) #[] true | return none
    pure g'
  let some g3 ← simpGoalAllHyps g2 (← mkDynamicSimpCtx (unfoldNames ++ extraSimpNames) none simpCfg) sp | return none
  trySimpAll g3 (← mkDynamicSimpCtx extraSimpNames none simpCfg) sp

/-- Attempts to discharge all current goals via `simplifyWithUnfolds`, `tryCloseBasic`, and `grind`.
    On failure, restores state and runs `simplifyWithUnfolds` without closing for crisp diagnostics. -/
def solveWithUnfolds (unfoldNames extraSimpNames : Array Name)
    (simprocNames : Array Name := #[]) (simpCfg : Simp.Config := { zetaDelta := true }) :
    TacticM Bool := do
  let runPass (close : Bool) : TacticM Unit := forEachGoal fun g => do
    let some g' ← simplifyWithUnfolds g unfoldNames extraSimpNames simprocNames simpCfg | setGoals []
    if !close then setGoals [g']
    else if ← tryCloseBasic g' then setGoals []
    else do setGoals [g']; let _ ← tryTac `(tactic| grind)
  if ← tryRestoreM false id (do runPass true; return (← getGoals).isEmpty) then return true
  try runPass false catch _ => pure ()
  return false

end Qed.Verify.Core
