import Lean
import Qed.Lang
import Qed.Diag
import Qed.Collection

namespace Qed

class InvTarget (α : Type) (Model : outParam Type) where proj : α → Model
instance {Model : Type} : InvTarget Model Model := ⟨id⟩
instance {Model β : Type} : InvTarget (Model × β) Model := ⟨Prod.fst⟩
@[simp] theorem InvTarget.proj_id {Model : Type} (m : Model) : InvTarget.proj m = m := rfl
@[simp] theorem InvTarget.proj_fst {Model β : Type} (p : Model × β) : InvTarget.proj p = p.1 := rfl

end Qed

namespace Qed.Verify.Core

open Lean Meta Elab Tactic

def boolSimpNames : Array Name := #[``Bool.and_eq_true, ``Bool.or_eq_true, ``Bool.not_eq_true', ``beq_iff_eq, ``bne_iff_ne, ``decide_eq_true_eq]
def boolConstSimpNames : Array Name := #[``Bool.true_and, ``Bool.and_true, ``Bool.false_and, ``Bool.and_false,
  ``Bool.true_or, ``Bool.or_true, ``Bool.false_or, ``Bool.or_false, ``Bool.not_false, ``Bool.not_true, ``ite_true, ``ite_false, ``dite_true, ``dite_false]
def dictSimpNames : Array Name := #[`Qed.Dict.emptyCollection_eq_empty, `Qed.Dict.getElem_eq_get,
  `Qed.Lang.QedMem.mem_dict, `Qed.Lang.QedMemProp.memProp_dict, `Qed.Dict.get_empty, `Qed.Dict.contains_empty,
  `Qed.Dict.size_empty, `Qed.Dict.isEmpty_empty, `Qed.Dict.get_set, `Qed.Dict.get_set_self, `Qed.Dict.contains_set,
  `Qed.Dict.contains_set_self, `Qed.Dict.get_remove, `Qed.Dict.get_remove_self, `Qed.Dict.contains_remove,
  `Qed.Dict.contains_remove_self, `Qed.Dict.size_set, `Qed.Dict.isEmpty_iff_size]
def optCodecSimpNames : Array Name := #[`Qed.Codec.valid, `Qed.Codec.refine, `Qed.Codec.jsonOnly, `Qed.Codec.text,
  `Qed.Codec.textarea, `Qed.Codec.nat, `Qed.Codec.int, `Qed.Codec.checkbox, `Qed.Codec.date]
def valUnwrapBaseNames : Array Name := #[`Qed.QedVal.val_field, `Qed.QedVal.val_ensured, ``Qed.Lang.QedVal.val_id]
def appPassThroughWrappers : Array Name := #[`Qed.Internal.App.withQueries, `Qed.Internal.App.withSubscriptions,
  `Qed.Internal.App.withStylesheets, `Qed.Internal.App.withExtraStyles, `Qed.App.withHead, `Qed.App.withSsrStatus]
def appWrapperBases : Array Name := #[`Qed.Internal.mkApp, `Qed.Internal.mkRoutedApp, `Qed.Internal.App.withDehydrate] ++ appPassThroughWrappers
def appProjSimpNames (env : Environment) (suffixes : Array String) : Array Name :=
  appWrapperBases.foldl (init := #[]) fun out base =>
    suffixes.foldl (init := out) fun acc suf => let nm := base.appendAfter s!"_{suf}"; if env.contains nm then acc.push nm else acc
def dbBaseSimpNames : Array Name := boolSimpNames ++ valUnwrapBaseNames ++ optCodecSimpNames ++ #[``Option.isSome_iff_ne_none, ``Option.getD_some,
  `Qed.Server.Db.some_getD_eq_self_iff, ``List.any_eq_true, ``Array.contains_iff_mem,
  ``Qed.Lang.QedMem.mem_array, ``Qed.Lang.QedMem.mem_list, ``Qed.Lang.QedMemProp.memProp_array, ``Qed.Lang.QedMemProp.memProp_list,
  ``Qed.Lang.QedSeqLit.ofList_array, ``Qed.Lang.QedSeqLit.ofList_list, ``Array.mem_toArray, ``List.mem_cons, ``List.not_mem_nil,
  `Qed.Str.toLower_length, `Qed.Str.toUpper_length, `Qed.Str.truncate_length, `Qed.Str.take_length, `Qed.Str.drop_length,
  ``true_and, ``and_true, ``false_or, ``or_false, ``true_or, ``or_true, ``id_eq, ``ne_eq]

private def addSimpNamesWithEqns (st : SimpTheorems) (names : Array Name) (dsimpOnly : Bool := false) (withEqns : Bool := false) :
    MetaM SimpTheorems := do
  let env ← getEnv; let mut st := st
  for n in names do
    if let some ci := env.find? n then
      match ci with
      | .thmInfo _ => unless dsimpOnly do st ← st.addConst n
      | _ =>
          st ← st.addDeclToUnfold n
          if withEqns && !dsimpOnly then
            if let some eqns ← getEqnsFor? n then for eq in eqns do st ← st.addConst eq
  return st

/-- Collect every local-module constant (including `_simp_*` aux lemmas and generated equations)
    referenced by `st`, paired with its type, so cached `SimpTheorems` are never reused across
    async elaboration branches that lack or differently number those local declarations. -/
private def collectLocalSimpDeps (env : Environment) (st : SimpTheorems) : Array (Name × Expr) :=
  let map₂ := env.constants.map₂
  let addName (acc : Std.HashMap Name Expr) (c : Name) : Std.HashMap Name Expr :=
    if acc.contains c then acc
    else match map₂.find? c with
      | some ci => acc.insert c ci.type
      | none => acc
  let collectTree (acc : Std.HashMap Name Expr) (tree : SimpTheoremTree) : Std.HashMap Name Expr :=
    tree.foldValues (init := acc) fun acc thm => thm.proof.getUsedConstants.foldl addName acc
  let seen := collectTree (collectTree {} st.pre) st.post
  let seen := st.toUnfold.fold (init := seen) addName
  seen.fold (init := #[]) fun acc k ty => acc.push (k, ty)

initialize simpThmsCache : IO.Ref (Std.HashMap (String × Name × Bool × Bool × Bool) (SimpTheorems × Array (Name × Expr))) ← IO.mkRef {}
initialize simprocsCache : IO.Ref (Std.HashMap (Array Name × Bool) Simp.SimprocsArray) ← IO.mkRef {}

def getCachedSimprocs (names : Array Name) (post : Bool := true) : MetaM Simp.SimprocsArray := do
  if names.isEmpty then return #[]
  let key := (names, post)
  if let some sp := (← simprocsCache.get).get? key then return sp
  let env ← getEnv; let mut sp : Simp.Simprocs := {}; let mut any := false
  for n in names do if env.contains n then sp ← sp.add n post; any := true
  let arr := if any then #[sp] else #[]
  if any then simprocsCache.modify (·.insert key arr)
  return arr

def getCachedSimpThms (key : String) (names : Array Name) (dsimpOnly : Bool := false) (withEqns : Bool := true) : MetaM SimpTheorems := do
  let env ← getEnv
  let cacheKey := (key, env.header.mainModule, dsimpOnly, withEqns, env.contains `Qed.Codec.valid)
  if let some (st, needed) := (← simpThmsCache.get).get? cacheKey then
    if needed.all fun (k, ty) => match env.find? k with | some ci => ci.type == ty | none => false then
      return st
  let st ← addSimpNamesWithEqns {} names dsimpOnly withEqns
  let deps := collectLocalSimpDeps (← getEnv) st
  simpThmsCache.modify (·.insert cacheKey (st, deps)); return st

/-- Resolve a component `update`/`app` ident and include its generated hoisted helpers (`stepOwn`, `_reconcileHoisted`) when present. -/
def resolveCompUpdateUnfolds (idStx : Syntax) : CoreM (Array Name) := do
  let some cn ← try some <$> resolveGlobalConstNoOverload idStx catch _ => pure none | return #[]
  let env ← getEnv; let pfx := cn.getPrefix; let base := #[cn]
  if pfx.isAnonymous then return base
  let extras := if cn.getString! == "app" then #[pfx ++ `update, pfx ++ `stepOwn, pfx ++ `_reconcileHoisted]
                else #[pfx ++ `stepOwn, pfx ++ `_reconcileHoisted]
  return extras.foldl (init := base) fun acc aux =>
    if env.contains aux && !acc.contains aux then acc.push aux else acc

elab "qedWithFreshHeartbeats" tac:tacticSeq : tactic =>
  Core.withCurrHeartbeats (evalTactic tac)

private def mkSimpCtx (cfg : Simp.Config) (thms : Array SimpTheorems) : MetaM Simp.Context := do
  Simp.mkContext { cfg with failIfUnchanged := false } thms (← getSimpCongrTheorems)

def mkCachedSimpCtx (key : String) (names : Array Name) (cfg : Simp.Config := { zetaDelta := false })
    (simprocNames : Array Name := #[]) (dsimpOnly : Bool := false) (withEqns : Bool := true) : MetaM (Simp.Context × Simp.SimprocsArray) := do
  return (← mkSimpCtx cfg #[← getCachedSimpThms key names dsimpOnly withEqns], ← getCachedSimprocs simprocNames)

def mkDynamicSimpCtx (extraNames : Array Name) (baseKey? : Option (String × Array Name) := none)
    (cfg : Simp.Config := { zetaDelta := false }) (dsimpOnly : Bool := false) (withEqns : Bool := true) : MetaM Simp.Context := do
  let baseSt ← match baseKey? with | some (k, ns) => getCachedSimpThms k ns dsimpOnly withEqns | none => pure {}
  mkSimpCtx cfg #[← addSimpNamesWithEqns baseSt extraNames dsimpOnly withEqns]

def mkEmptyDsimpCtx (cfg : Simp.Config := {}) : MetaM Simp.Context := mkSimpCtx cfg #[]

def mkSimpCtxWithBase (extraNames : Array Name := #[]) (cfg : Simp.Config := {}) (cacheKey? : Option String := none)
    (withEqns : Bool := false) : MetaM Simp.Context := do
  let base ← getSimpTheorems
  let thms ← if extraNames.isEmpty then pure #[base]
    else match cacheKey? with
      | some k => pure #[base, ← getCachedSimpThms k extraNames false withEqns]
      | none   => pure #[← addSimpNamesWithEqns base extraNames false withEqns]
  mkSimpCtx cfg thms

@[noinline, nospecialize]
def tryRestoreM {m : Type → Type} {s α : Type} [Monad m] [MonadBacktrack s m] [MonadExcept Exception m]
    (fail : α) (ok : α → Bool) (k : m α) : m α := do
  let st ← saveState
  try
    let r ← k; unless ok r do restoreState st
    return r
  catch _ => restoreState st; return fail

def tryGoalM (g : MVarId) (k : MVarId → MetaM MVarId) : MetaM MVarId := tryRestoreM g (fun _ => true) (k g)
def tryGoalOptM (g : MVarId) (k : MVarId → MetaM (Option MVarId)) : MetaM (Option MVarId) := tryRestoreM (some g) (fun _ => true) (k g)

def simpGoalOnly (g : MVarId) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray := #[])
    (fvarIds : Array FVarId := #[]) (simplifyTarget : Bool := true) (dsimpOnly : Bool := false) : MetaM (Option MVarId) :=
  tryGoalOptM g fun g => do
    if dsimpOnly then return (← dsimpGoal g ctx simprocs simplifyTarget fvarIds).1
    return (← simpGoal g ctx simprocs none simplifyTarget fvarIds).1.map Prod.snd

def simpGoalAllHyps (g : MVarId) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray := #[]) (dsimpOnly : Bool := false) : MetaM (Option MVarId) := do
  let fvs ← g.withContext do return (← getLCtx).foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d.fvarId
  simpGoalOnly g ctx simprocs fvs true dsimpOnly

def trySimpAll (g : MVarId) (ctx : Simp.Context) (sp : Simp.SimprocsArray := #[]) : MetaM (Option MVarId) :=
  tryGoalOptM g fun g => return (← simpAll g ctx sp).1
def trySplitTarget (g : MVarId) : MetaM (Option (List MVarId)) := tryRestoreM none Option.isSome (g.withContext (Meta.splitTarget? g))
def trySplitLocalDecl (g : MVarId) (fv : FVarId) : MetaM (Option (List MVarId)) := tryRestoreM none Option.isSome (g.withContext (Meta.splitLocalDecl? g fv))
def tryApplyConst (g : MVarId) (c : Name) : MetaM (Option (List MVarId)) := tryRestoreM none (fun _ => true) (some <$> g.applyConst c)
def tryReflGoal (g : MVarId) : MetaM Bool := tryRestoreM false id do
  g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    if let some (_, lhs, rhs) := tgt.eq? then
      if ← isDefEq lhs rhs then
        let pf ← mkEqRefl lhs
        g.assign (if ← withTransparency .reducible (isDefEq lhs rhs) then pf else mkApp2 (mkConst ``id [Level.zero]) tgt pf)
        return true
      return false
    g.refl; return true
def tryTac (mk : TacticM (TSyntax `tactic)) (requireClosed : Bool := false) : TacticM Bool :=
  tryRestoreM false id do withoutRecover <| evalTactic (← mk); if requireClosed then return (← getGoals).isEmpty else return true

def forEachGoal (f : MVarId → TacticM Unit) : TacticM Unit := do
  let mut rem := []
  for g in (← getGoals) do setGoals [g]; f g; rem := rem ++ (← getGoals)
  setGoals rem

def extractForEachColl? (tgt : Expr) : Option Expr :=
  match tgt.consumeMData with
  | .forallE _ _ (.forallE _ memTy _ _) _ =>
      let m := memTy.consumeMData; if m.isAppOfArity ``Membership.mem 5 then some m.getAppArgs[3]!.consumeMData else none
  | _ => none

def collectGoalConsts (g : MVarId) (includeLCtx : Bool := false) : MetaM (Std.HashSet Name) := g.withContext do
  let mut s := (← instantiateMVars (← g.getType)).getUsedConstants.foldl (·.insert ·) {}
  if includeLCtx then
    for d in (← getLCtx) do if !d.isImplementationDetail then s := (← instantiateMVars d.type).getUsedConstants.foldl (·.insert ·) s
  return s

def assertFacts (g0 : MVarId) (pfx : String) (facts : Array Expr) : MetaM (MVarId × Array FVarId) := do
  let mut g := g0; let mut fvs := #[]
  for idx in [0:facts.size] do
    let p := facts[idx]!
    let (fv, g') ← (← g.assert (Name.mkSimple s!"{pfx}{idx}") (← g.withContext (inferType p)) p).intro1P
    g := g'; fvs := fvs.push fv
  return (g, fvs)

def namesToSimpLemmas (ns : Array Name) : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :=
  ns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
def termsToSimpLemmas (ts : Array Term) : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :=
  ts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)

private def nonRefinedHeads : Std.HashSet Name :=
  #[``Nat, ``Int, ``String, ``Bool, ``Unit, ``ByteArray, ``Char, ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize,
    ``Array, ``List, ``Option, ``Except, ``Prod, ``Eq, ``And, ``Or, ``Not, ``LT.lt, ``LE.le, ``True, ``False,
    `Qed.Server.RequestCtx, `Qed.Server.ApiError, `Qed.Server.WsEmit].foldl (·.insert ·) {}

structure FactScanConfig where
  scanLCtx : Bool := true
  scanLCtxValues : Bool := false
  includeMacroPropHyps : Bool := false
  includeFin : Bool := true
  includeDictRemove : Bool := false
  includeCollectionRules : Bool := false
  rounds : Nat := 1
  skipDecl : LocalDecl → Expr → Bool := fun _ _ => false

private def tryEmitApp (env : Environment) (c : Name) (args : Array Expr) (addFact : Expr → MetaM Unit) : MetaM Unit := do
  if env.contains c then if let some p ← try some <$> mkAppM c args catch _ => pure none then addFact p

private def tryEmitFieldOrFin (env : Environment) (includeFin : Bool) (sub ty : Expr) (addFact : Expr → MetaM Unit) : MetaM Bool := do
  if ty.isAppOfArity `Qed.Field 2 || ty.isAppOfArity `Qed.Ensured 2 then tryEmitApp env `Qed.Field.ok #[sub] addFact; return true
  if includeFin && ty.isAppOfArity ``Fin 1 then tryEmitApp env ``Fin.isLt #[sub] addFact; return true
  return false

private def strLenFactRules : Array (Name × Nat × Name) := #[
  (`Qed.Str.truncate, 3, `Qed.Str.truncate_length), (`Qed.Str.take, 2, `Qed.Str.take_length), (`Qed.Str.drop, 2, `Qed.Str.drop_length),
  (`Qed.Str.trim, 1, `Qed.Str.trim_length_le), (`Qed.Str.trimLeft, 1, `Qed.Str.trimLeft_length_le), (`Qed.Str.trimRight, 1, `Qed.Str.trimRight_length_le),
  (`Qed.Str.toLower, 1, `Qed.Str.toLower_length), (`Qed.Str.toUpper, 1, `Qed.Str.toUpper_length)]

private def skipInferFnHeads : Std.HashSet Name :=
  #[``Eq, ``Ne, ``And, ``Or, ``Not, ``Iff, ``Exists, ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge, ``BEq.beq, ``bne,
    ``Bool.and, ``Bool.or, ``Bool.not, ``Decidable.decide, ``Membership.mem, ``String.length, ``Array.size, ``List.length,
    ``Nat.succ, ``Nat.add, ``Nat.sub, ``Nat.mul, ``Int.ofNat, ``Int.negSucc, ``Option.some, ``Option.none,
    ``Except.ok, ``Except.error, ``Prod.mk, ``List.cons, ``List.nil, ``Array.mk, ``Array.toList, ``List.toArray,
    ``Fin.val, `Qed.Field.val, ``Qed.Lang.QedVal.val, ``Qed.Lang.QedAndProp, ``Qed.Lang.QedMem.mem, ``Qed.Lang.QedMemProp.memProp].foldl (·.insert ·) {}

private def inspectSubtermForFacts (env : Environment) (cfg : FactScanConfig) (forallHyps : Array Expr) (sub : Expr) (addFact : Expr → MetaM Unit) : MetaM Unit := do
  if sub.hasLooseBVars then return
  match sub with | .sort _ | .lit _ | .mvar _ | .bvar _ | .forallE .. | .lam .. => return | _ => pure ()
  if cfg.includeCollectionRules && sub.isAppOfArity ``Array.sumBy 3 then
    let sArgs := sub.getAppArgs
    if sArgs[1]!.isAppOfArity ``Array.set 5 then let a := sArgs[1]!.getAppArgs; tryEmitApp env ``Array.sumBy_set #[a[1]!, sArgs[2]!, a[2]!, a[3]!, a[4]!] addFact
  if (cfg.includeDictRemove || cfg.includeCollectionRules) && sub.isAppOfArity `Qed.Dict.remove 5 then
    let a := sub.getAppArgs; tryEmitApp env `Qed.Dict.size_remove_le #[a[3]!, a[4]!] addFact
  if cfg.includeCollectionRules && sub.isAppOfArity ``GetElem.getElem 8 then
    for fh in forallHyps do tryEmitApp env ``Array.forall_elem #[sub.getAppArgs[7]!, fh] addFact
  if let .const c _ := sub.getAppFn then
    let a := sub.getAppArgs
    if let some (_, _, lem) := strLenFactRules.find? fun (fn, ar, _) => fn == c && ar == a.size then
      tryEmitApp env lem a addFact
    if skipInferFnHeads.contains c || nonRefinedHeads.contains c then return
  let some t ← try some <$> inferType sub catch _ => pure none | return
  let tC := t.consumeMData
  if ← tryEmitFieldOrFin env cfg.includeFin sub tC addFact then return
  match tC.getAppFn with | .sort _ | .forallE .. => return | .const c _ => if nonRefinedHeads.contains c then return | _ => pure ()
  if let some ty ← try some <$> whnf tC catch _ => pure none then discard <| tryEmitFieldOrFin env cfg.includeFin sub ty addFact

private structure FactScanState where
  facts    : Array Expr := #[]
  factSet  : Std.HashSet Expr := {}
  seen     : Std.HashSet Expr := {}
  nextScan : Array Expr := #[]

@[noinline] def collectFacts (cfg : FactScanConfig := {}) (extraExprs : Array Expr := #[]) : MetaM (Array Expr) := do
  let env ← getEnv; let stRef ← IO.mkRef ({} : FactScanState)
  let addFact (p : Expr) : MetaM Unit := do
    if (← stRef.get).factSet.contains p then return
    let pTy? ← if cfg.rounds > 1 then some <$> instantiateMVars (← inferType p) else pure none
    stRef.modify fun s => { s with factSet := s.factSet.insert p, facts := s.facts.push p, nextScan := match pTy? with | some t => s.nextScan.push t | none => s.nextScan }
  let mut scanExprs : Array Expr := #[]; let mut forallHyps : Array Expr := #[]
  if cfg.scanLCtx then
    for decl in (← getLCtx) do
      if !decl.isImplementationDetail then
        let dty ← instantiateMVars decl.type
        if cfg.includeMacroPropHyps && !decl.isLet && decl.userName.hasMacroScopes then
          if (← try isProp dty catch _ => pure false) then addFact decl.toExpr
        unless cfg.skipDecl decl dty do
          if cfg.scanLCtxValues then
            scanExprs := scanExprs.push decl.toExpr; if let some val := decl.value? then scanExprs := scanExprs.push val
          else scanExprs := scanExprs.push dty
        if cfg.includeCollectionRules && dty.isForall then forallHyps := forallHyps.push decl.toExpr
  for e in extraExprs do scanExprs := scanExprs.push (← instantiateMVars e)
  for _ in [0:cfg.rounds] do
    if scanExprs.isEmpty then break
    stRef.modify fun s => { s with nextScan := #[] }
    for e in scanExprs do
      e.forEach fun sub => do
        if !sub.hasLooseBVars then
          if !(← stRef.get).seen.contains sub then
            stRef.modify fun s => { s with seen := s.seen.insert sub }
            inspectSubtermForFacts env cfg forallHyps sub addFact
    scanExprs := (← stRef.get).nextScan
  return (← stRef.get).facts

def collectAndAssertFacts (g0 : MVarId) (pfx : String) (cfg : FactScanConfig := {}) : MetaM (MVarId × Array FVarId) := do
  assertFacts g0 pfx (← g0.withContext do collectFacts cfg #[← instantiateMVars (← g0.getType)])

def tryCloseTrivial (g : MVarId) (skipTarget : Expr → Bool := fun _ => false) (reducibleOnly : Bool := false) : MetaM Bool := do
  let tgtC := (← g.withContext do instantiateMVars (← g.getType)).consumeMData
  if tgtC.isConstOf ``True then g.assign (mkConst ``True.intro); return true
  if skipTarget tgtC then return false
  if reducibleOnly then
    return ← g.withContext <| withTransparency .reducible do
      if let some (_, lhs, rhs) := tgtC.eq? then if ← isDefEq lhs rhs then g.assign (← mkEqRefl lhs); return true
      for d in (← getLCtx) do if !d.isImplementationDetail then if ← isDefEq d.type tgtC then g.assign (mkFVar d.fvarId); return true
      return false
  if tgtC.isAppOfArity ``Eq 3 then if ← tryReflGoal g then return true
  if (tgtC.isAppOfArity ``LE.le 4 || tgtC.isAppOfArity ``GE.ge 4) && tgtC.getAppArgs[2]! == tgtC.getAppArgs[3]! then
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
      g.assign (mkApp3 (mkConst ``of_decide_eq_true) tgt decInst (← mkEqRefl (mkConst ``Bool.true))); return true
    return false

def tryDirectOmega (g : MVarId) : MetaM Bool := tryRestoreM false id do
  let some g' ← g.falseOrByContra | return true
  g'.withContext do Omega.omega ((← getPropHyps).toList.map mkFVar) g' {}; return true

@[noinline]
private partial def proveGroundKernelProp (env : Environment) (e : Expr) : TacticM (Option Expr) := do
  let e := e.consumeMData
  match e with
  | .letE _ _ v b _ => proveGroundKernelProp env (b.instantiate1 v)
  | _ =>
      if e.isConstOf ``True then return some (mkConst ``True.intro)
      if e.isAppOfArity ``And 2 then
        let a := e.getAppArgs[0]!; let b := e.getAppArgs[1]!
        if let some pa ← proveGroundKernelProp env a then
          if let some pb ← proveGroundKernelProp env b then
            return some (mkApp4 (mkConst ``And.intro) a b pa pb)
        return none
      if let some (ty, lhs, rhs) := e.eq? then
        if (match Kernel.isDefEq env {} lhs rhs with | .ok true => true | _ => false) then
          return some (mkApp2 (mkConst ``Eq.refl [← getLevel ty]) ty lhs)
      let mv ← mkFreshExprMVar e
      let saved ← getGoals; setGoals [mv.mvarId!]
      let ok ← tryTac (requireClosed := true) `(tactic| decide +kernel)
      setGoals saved
      if ok then return some (← instantiateMVars mv)
      return none

/-- Close a ground goal quickly without blowing elaborator `maxRecDepth`: reducible-only trivial check
first, then kernel `Kernel.isDefEq` (handles `let`, `And`, `True`, and `Eq` on types without `DecidableEq`,
e.g. `Except`/`Json`) and `decide +kernel` for closed decidable propositions. -/
def tryCloseGroundKernel (g : MVarId) : TacticM Bool := do
  if ← tryCloseTrivial g (reducibleOnly := true) then return true
  let tgt ← g.withContext do instantiateMVars (← g.getType)
  if !tgt.hasFVar && !tgt.hasMVar && !tgt.hasLevelMVar then
    let env ← getEnv
    if let some pf ← g.withContext (proveGroundKernelProp env tgt) then
      g.assign pf
      return true
  return false

elab "qedCloseGround" : tactic => do
  let g ← getMainGoal
  if ← tryCloseGroundKernel g then replaceMainGoal []
  else throwError "qedCloseGround failed"

def tryCloseBasic (g : MVarId) (skipTarget : Expr → Bool := fun _ => false) (reducibleOnly : Bool := false) : MetaM Bool := do
  if ← tryCloseTrivial g skipTarget reducibleOnly then return true
  if ← tryDirectDecide g then return true
  tryDirectOmega g

def splitAndHypsGoal (g0 : MVarId) (existsOnly : Bool := false) (maxIters : Nat := 32) : MetaM (MVarId × Bool) := do
  let isMatchTy (t : Expr) := t.isAppOfArity ``Exists 2 || (!existsOnly && (t.isAppOfArity ``And 2 || t.isAppOfArity ``Qed.Lang.QedAndProp 2))
  let mut g := g0; let mut didSplit := false
  for _ in [0:maxIters] do
    let mut nextG? : Option MVarId := none
    for decl in (← g.withContext getLCtx) do
      if nextG?.isNone && !decl.isImplementationDetail && !decl.isLet then
        let tC := decl.type.consumeMData
        if isMatchTy tC || match tC.getAppFn with | .const c _ => !nonRefinedHeads.contains c | _ => true then
          if let some g' ← tryRestoreM none Option.isSome do
              if isMatchTy (← g.withContext (whnf tC)) then return ((← g.cases decl.fvarId)[0]?).map (·.mvarId) else return none then
            nextG? := some g'; didSplit := true
    match nextG? with | some g' => g := g' | none => break
  return (g, didSplit)

def splitGoalAnds (g0 : MVarId) (maxIters : Nat := 64) : MetaM (List MVarId) := do
  let rec loop : Nat → List MVarId → MetaM (List MVarId)
    | 0, gs => return gs | _, [] => return []
    | fuel + 1, g :: rest => do
        let t := (← g.withContext (instantiateMVars (← g.getType))).consumeMData
        if t.isAppOfArity ``And 2 || t.isAppOfArity ``Qed.Lang.QedAndProp 2 then
          if let some [g1, g2] ← tryApplyConst g ``And.intro then return ← loop fuel (g1 :: g2 :: rest)
        return g :: (← loop fuel rest)
  loop maxIters [g0]

structure CloseFallbackConfig where
  skipTarget : Expr → Bool := fun _ => false
  trySimpStarOmega : Bool := false
  simpAllCfg : Simp.Config := { zetaDelta := false }
  deepExtraSimpAll : Array Name := #[]

@[noinline] def closeWithFallback (g : MVarId) (cfg : CloseFallbackConfig := {}) : TacticM Bool := do
  if cfg.trySimpStarOmega then
    if ← tryRestoreM false id do
      let stWithHyps ← g.withContext do
        let mut st ← getSimpTheorems
        for d in (← getLCtx) do
          if !d.isImplementationDetail && !d.isLet then
            if ← try isProp d.type catch _ => pure false then st ← try st.add (.fvar d.fvarId) #[] d.toExpr catch _ => pure st
        return st
      match ← simpGoalOnly g (← mkSimpCtx cfg.simpAllCfg #[stWithHyps]) with | none => return true | some g' => tryDirectOmega g'
    then return true
  if ← tryRestoreM false id do
    match ← trySimpAll g (← mkSimpCtxWithBase #[] cfg.simpAllCfg) with
    | none => return true | some g' => tryCloseBasic g' cfg.skipTarget
  then return true
  let saved ← getGoals; setGoals [g]
  let ok ← tryTac (requireClosed := true) do
    let simpArgs ← namesToSimpLemmas cfg.deepExtraSimpAll
    `(tactic| first | qedNonlinearClose | (try simp_all [$[$simpArgs],*]; try (repeat' (split <;> try simp_all [$[$simpArgs],*])); all_goals (first | omega | decide | rfl)) | grind)
  setGoals saved; return ok

@[noinline] def solveWithUnfolds (unfoldNames extraSimpNames : Array Name) (simprocNames : Array Name := #[])
    (simpCfg : Simp.Config := { zetaDelta := true }) (harvestFacts : Bool := false)
    (scanLCtxValues : Bool := true) (clearErrorsOnFail : Bool := false) : TacticM Bool := do
  let sp ← getCachedSimprocs simprocNames
  let unfoldCtx? ← if unfoldNames.isEmpty then pure none else some <$> mkDynamicSimpCtx unfoldNames none simpCfg true
  let allCtx ← mkDynamicSimpCtx (unfoldNames ++ extraSimpNames) none simpCfg
  let extraCtx ← mkDynamicSimpCtx extraSimpNames none simpCfg
  let simplify (g0 : MVarId) (withFacts : Bool) : MetaM (Option MVarId) := do
    let (_, g1) ← g0.intros
    let g2 ← match unfoldCtx? with
      | none => pure g1
      | some uCtx =>
          let some g' ← simpGoalAllHyps g1 uCtx #[] true | return none
          pure g'
    let g2 ← if !withFacts then pure g2 else do pure (← collectAndAssertFacts g2 "_dbFact" { scanLCtx := true, scanLCtxValues, includeFin := true }).1
    let some g3 ← simpGoalAllHyps g2 allCtx sp | return none
    let g3 := (← splitAndHypsGoal g3).1
    trySimpAll g3 extraCtx sp
  let runPass (close : Bool) : TacticM Unit := forEachGoal fun g => do
    let some g' ← simplify g (close && harvestFacts) | setGoals []
    if !close then setGoals [g']
    else if ← tryCloseBasic g' then setGoals []
    else do setGoals [g']; discard <| tryTac `(tactic| grind)
  if ← tryRestoreM false id (do runPass true; return (← getGoals).isEmpty) then return true
  if !clearErrorsOnFail then try runPass false catch _ => pure ()
  return false

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

def relevantBoundaryLemmas (cs : Std.HashSet Name) : Array Name :=
  boundaryLemmaGroups.foldl (init := #[``Qed.Lang.QedVal.val_id]) fun acc (k, ns) => if cs.contains k then acc ++ ns else acc

def collectTriggered (env : Environment) (cs : Std.HashSet Name) (init : Array Name) (groups : Array (Array Name × Array Name)) : Array Name :=
  groups.foldl (init := init) fun acc (triggers, lemmas) => if triggers.any cs.contains then acc ++ lemmas.filter env.contains else acc

def relevantAppLemmas (env : Environment) (cs : Std.HashSet Name) : Array Name :=
  collectTriggered env cs #[``InvTarget.proj_id, ``InvTarget.proj_fst] #[
    (appWrapperBases ++ #[`Qed.App.init, `Qed.App.update], appProjSimpNames env #["init", "update"] ++
      #[`Qed.Query.boot, `Qed.Query.wrap, `Qed.Resource.query, `Qed.Resource.rpcQuery, `Qed.Subscription.boot, `Qed.Subscription.wrap, `Qed.Subscription.boot_state_eq]),
    (#[`Qed.Cached.activate, `Qed.Cached.all, `Qed.Cached.markRefetch, `Qed.Cached.invalidateAll],
     #[`Qed.Cached.activate, `Qed.Cached.all_empty, `Qed.Cached.all_markRefetch, `Qed.Cached.all_invalidateAll])]

@[noinline]
def runUnfoldPresent (extra : Array Term) (skip : Array Name := #[]) : TacticM Unit := do
  let g :: _ ← getGoals | return
  let cs ← collectGoalConsts g true
  let fixedL := (← namesToSimpLemmas (relevantAppLemmas (← getEnv) cs ++ relevantBoundaryLemmas cs)) ++ (← termsToSimpLemmas extra)
  Qed.qedUnfoldHelperLoop 12 (fun env n => if skip.contains n || !Qed.qedIsHelper env n then return false else return (← getProjectionFnInfo? n).isNone)
    fixedL (includeLCtx := true) (useSimpAll := true)

private def runFastClose : TacticM Unit := do
  if ← tryCloseTrivial (← getMainGoal) (reducibleOnly := true) then replaceMainGoal []
  else throwError "qedFastClose: not trivially closed"

elab "qedUnfoldPresent" "[" extra:term,* "]" : tactic => runUnfoldPresent extra.getElems
elab "qedFastClose" : tactic => runFastClose

macro "qedAutoClose" : tactic => `(tactic|
  (first
    | qedFastClose | contradiction | omega | decide | assumption | rfl | (qedNonlinearClose; done)
    | (try (repeat' (apply And.intro)); all_goals (first | qedFastClose | contradiction | omega | decide | (qedNonlinearClose; done) | grind); done)))

structure ParsedBlindTarget where
  paramId : Ident
  fields  : Array Ident

def parseBlindTarget (stx : Syntax) (includeGot : Bool := true) : Command.CommandElabM ParsedBlindTarget := do
  let rawId : Ident := ⟨stx.getArg 0⟩
  let optBraces := stx.getArg 1
  if optBraces.getNumArgs == 3 then
    return { paramId := rawId, fields := (optBraces.getArg 1).getSepArgs.map (⟨·⟩) }
  match rawId.getId.eraseMacroScopes with
  | .str .anonymous _ => return { paramId := rawId, fields := #[] }
  | .str (.str .anonymous p) f =>
      return { paramId := mkIdentFrom rawId (Name.mkSimple p), fields := #[mkIdentFrom rawId (Name.mkSimple f)] }
  | _ =>
      let tail := if includeGot then s!", got `{rawId.getId}`" else ""
      throwErrorAt rawId s!"`blindTo` expects `<param>`, `<param>.<field>`, or `<param>.\{f1, f2}`{tail}"

def fmtBlindTarget (t : ParsedBlindTarget) : String :=
  if t.fields.isEmpty then t.paramId.getId.toString
  else if t.fields.size == 1 then s!"{t.paramId.getId}.{t.fields[0]!.getId}"
  else s!"{t.paramId.getId}.\{" ++ String.intercalate ", " (t.fields.toList.map (·.getId.toString)) ++ "}"

@[noinline]
def buildBlindToArgs (targets : Array ParsedBlindTarget) (validParamNames : Array Name)
    (binderIds : Array Ident) (binderTys : Array Term) (fnErrCtx? : Option String := none) :
    Command.CommandElabM (Array (Ident × Option Term) × Array Term × Array Term) := do
  let mut paramBlinds : Array (Name × Bool × Array Ident) := #[]
  for t in targets do
    let pn := t.paramId.getId.eraseMacroScopes
    unless validParamNames.contains pn do
      match fnErrCtx? with
      | some fnStr => throwErrorAt t.paramId s!"unknown parameter `{pn}` in `blindTo` of `{fnStr}`"
      | none => throwErrorAt t.paramId s!"unknown parameter `{pn}` in `blindTo`{Qed.Diag.didYouMean pn.toString (validParamNames.toList.map toString)}"
    if let some pos := paramBlinds.findIdx? (·.1 == pn) then
      let (_, whole, flds) := paramBlinds[pos]!
      let whole' := whole || t.fields.isEmpty
      let flds' := if whole' then #[] else t.fields.foldl (fun acc f => if acc.any (·.getId.eraseMacroScopes == f.getId.eraseMacroScopes) then acc else acc.push f) flds
      paramBlinds := paramBlinds.set! pos (pn, whole', flds')
    else
      paramBlinds := paramBlinds.push (pn, t.fields.isEmpty, t.fields)
  let mut freshVars : Array (Ident × Option Term) := #[]
  let mut lhsArgs : Array Term := #[]
  let mut rhsArgs : Array Term := #[]
  for (bId, bTy) in binderIds.zip binderTys do
    let bn := bId.getId.eraseMacroScopes
    rhsArgs := rhsArgs.push ⟨bId.raw⟩
    match paramBlinds.find? (·.1 == bn) with
    | none => lhsArgs := lhsArgs.push ⟨bId.raw⟩
    | some (_, true, _) =>
        let fv := mkIdent (Name.mkSimple s!"_qed_blind_{bn}")
        freshVars := freshVars.push (fv, some bTy); lhsArgs := lhsArgs.push ⟨fv.raw⟩
    | some (_, false, flds) =>
        let mut updIds : Array Ident := #[]; let mut updVals : Array Term := #[]
        for f in flds do
          let fv := mkIdent (Name.mkSimple s!"_qed_blind_{bn}_{f.getId.eraseMacroScopes}")
          freshVars := freshVars.push (fv, none); updIds := updIds.push f; updVals := updVals.push ⟨fv.raw⟩
        lhsArgs := lhsArgs.push (← `({ $bId with $[$updIds:ident := $updVals:term],* }))
  return (freshVars, lhsArgs, rhsArgs)

@[noinline]
def mkBlindToEqProp (freshVars : Array (Ident × Option Term)) (lhsCall rhsCall : Term) : Command.CommandElabM Term := do
  freshVars.foldrM (init := ← `($lhsCall = $rhsCall)) fun (fv, ty?) acc => match ty? with
    | some ty => `(∀ ($fv:ident : $ty), $acc)
    | none    => `(∀ $fv:ident, $acc)

end Qed.Verify.Core
