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
  `Qed.Server.RequestCtx.principal_withAuth, `Qed.Server.RequestCtx.principal_forPrincipal, `Qed.Server.RequestCtx.principal_forUser,
  `Qed.Server.RequestCtx.userId_forUser, `Qed.Server.RequestCtx.userId_forPrincipal_system, `Qed.Server.RequestCtx.userId_forPrincipal_anonymous,
  ``true_and, ``and_true, ``false_or, ``or_false, ``true_or, ``or_true, ``id_eq, ``ne_eq]

@[noinline] def foldlMeta {α β : Type} (xs : Array α) (init : β) (f : β → α → MetaM β) : MetaM β :=
  let rec go : Nat → β → MetaM β | 0, acc => pure acc | r + 1, acc => do let i := xs.size - (r + 1); if h : i < xs.size then go r (← f acc xs[i]) else pure acc
  go xs.size init
@[noinline] def mapMeta {α β : Type} (xs : Array α) (f : α → MetaM β) : MetaM (Array β) :=
  foldlMeta xs (Array.mkEmpty xs.size) fun acc x => return acc.push (← f x)

def mkBoolEq (lhs rhs : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.one]) (mkConst ``Bool) lhs rhs
def mkBoolEqTrue (lhs : Expr) : Expr := mkBoolEq lhs (mkConst ``Bool.true)
def rflBoolTrue : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
def rflBoolFalse : Expr := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.false)

@[noinline] def closeAllGoals (f : MVarId → MetaM Bool) : List MVarId → MetaM Bool
  | [] => pure true | g :: r => do if ← f g then closeAllGoals f r else pure false
@[noinline] def filterUnsolvedM (f : MVarId → MetaM Bool) : List MVarId → MetaM (List MVarId)
  | [] => pure [] | g :: r => do if ← f g then filterUnsolvedM f r else return g :: (← filterUnsolvedM f r)

private def addSimpNamesWithEqns (st : SimpTheorems) (names : Array Name) (dsimpOnly : Bool := false) (withEqns : Bool := false) : MetaM SimpTheorems := do
  let env ← getEnv
  foldlMeta names st fun st n => do
    let some ci := env.find? n | return st
    match ci with
    | .thmInfo _ => if dsimpOnly then pure st else st.addConst n
    | _ =>
        let st ← st.addDeclToUnfold n
        if withEqns && !dsimpOnly then
          match ← getEqnsFor? n with | some eqns => foldlMeta eqns st fun s eq => s.addConst eq | none => pure st
        else pure st

/-- Collect every local-module constant referenced by `st`, paired with its type, so cached
    `SimpTheorems` are never reused across async branches with different local decls. -/
private def collectLocalSimpDeps (env : Environment) (st : SimpTheorems) : Array (Name × Expr) :=
  let map₂ := env.constants.map₂
  let addName (acc : Std.HashMap Name Expr) (c : Name) : Std.HashMap Name Expr :=
    if acc.contains c then acc else match map₂.find? c with | some ci => acc.insert c ci.type | none => acc
  let collectTree (acc : Std.HashMap Name Expr) (tree : SimpTheoremTree) : Std.HashMap Name Expr :=
    tree.foldValues (init := acc) fun acc thm => thm.proof.getUsedConstants.foldl addName acc
  let seen := st.toUnfold.fold (init := collectTree (collectTree {} st.pre) st.post) addName
  seen.fold (init := #[]) fun acc k ty => acc.push (k, ty)

initialize simpThmsCache : IO.Ref (Std.HashMap (String × Name × Bool × Bool × Bool) (SimpTheorems × Array (Name × Expr))) ← IO.mkRef {}
initialize simprocsCache : IO.Ref (Std.HashMap (Array Name × Bool) Simp.SimprocsArray) ← IO.mkRef {}

def getCachedSimprocs (names : Array Name) (post : Bool := true) : MetaM Simp.SimprocsArray := do
  if names.isEmpty then return #[]
  let key := (names, post)
  if let some sp := (← simprocsCache.get).get? key then return sp
  let env ← getEnv
  let (sp, any) ← foldlMeta names (({} : Simp.Simprocs), false) fun (sp, any) n =>
    if env.contains n then return (← sp.add n post, true) else pure (sp, any)
  let arr := if any then #[sp] else #[]
  if any then simprocsCache.modify (·.insert key arr)
  return arr

def getCachedSimpThms (key : String) (names : Array Name) (dsimpOnly : Bool := false) (withEqns : Bool := true) : MetaM SimpTheorems := do
  let env ← getEnv
  let cacheKey := (key, env.header.mainModule, dsimpOnly, withEqns, env.contains `Qed.Codec.valid)
  if let some (st, needed) := (← simpThmsCache.get).get? cacheKey then
    if needed.all fun (k, ty) => match env.find? k with | some ci => ci.type == ty | none => false then return st
  let st ← addSimpNamesWithEqns {} names dsimpOnly withEqns
  let deps := collectLocalSimpDeps (← getEnv) st
  simpThmsCache.modify (·.insert cacheKey (st, deps)); return st

/-- Resolve a component `update`/`app` ident and include its generated hoisted helpers (`stepOwn`, `_reconcileHoisted`) when present. -/
def resolveCompUpdateUnfolds (idStx : Syntax) : CoreM (Array Name) := do
  let some cn ← try some <$> resolveGlobalConstNoOverload idStx catch _ => pure none | return #[]
  let env ← getEnv; let pfx := cn.getPrefix; let base := #[cn]
  if pfx.isAnonymous then return base
  let extras := if cn.getString! == "app" then #[pfx ++ `update, pfx ++ `stepOwn, pfx ++ `_reconcileHoisted] else #[pfx ++ `stepOwn, pfx ++ `_reconcileHoisted]
  return extras.foldl (init := base) fun acc aux => if env.contains aux && !acc.contains aux then acc.push aux else acc

@[noinline, nospecialize] def withFreshHeartbeatsT {α : Type} (k : TacticM α) : TacticM α := Core.withCurrHeartbeats k
@[noinline] def isPropSafe (ty : Expr) : MetaM Bool := try isProp ty catch _ => pure false

@[noinline] private def getUserLCtxDecls (includeLet : Bool) : MetaM (Array LocalDecl) := do
  return (← getLCtx).foldl (init := #[]) fun acc d => if !d.isImplementationDetail && (includeLet || !d.isLet) then acc.push d else acc

@[noinline, nospecialize] def collectLCtxDecls {α : Type} (f : LocalDecl → MetaM (Option α)) (includeLet : Bool := true) : MetaM (Array α) := do
  foldlMeta (← getUserLCtxDecls includeLet) #[] fun acc d => do match ← f d with | some x => pure (acc.push x) | none => pure acc

@[noinline, nospecialize] def findLCtxDecl? {α : Type} (f : LocalDecl → MetaM (Option α)) (includeLet : Bool := true) : MetaM (Option α) := do
  let rec go : List LocalDecl → MetaM (Option α) | [] => pure none | d :: ds => do match ← f d with | some x => pure (some x) | none => go ds
  go (← getUserLCtxDecls includeLet).toList

/-- Synthesize `rfl` projection simp lemmas `(_reconcileHoisted ... sOld res)[.1].<f> = res[.1].<f>`
    for non-`_sub_*` state fields when `goalConsts` references no `_sub_*` projection. -/
@[noinline] def mkReconcileProjLemmas (reconName : Name) (goalConsts : Std.HashSet Name) : MetaM (Option (Array (Name × Expr))) := do
  let env ← getEnv
  let some ci := env.find? reconName | return none
  forallTelescope ci.type fun args retTy => do
    if args.size < 2 then return none
    let isPair := retTy.isAppOfArity ``Prod 2
    let stateTy := if isPair then retTy.appFn!.appArg! else retTy
    let some stateName := stateTy.getAppFn.constName? | return none
    if goalConsts.any fun c => c.getPrefix == stateName && c.getString!.startsWith "_sub_" then return none
    let fields := Lean.getStructureFields env stateName
    if fields.isEmpty then return none
    let reconApp := mkAppN (mkConst reconName) args; let resArg := args.back!
    let lhsBase ← if isPair then mkAppM ``Prod.fst #[reconApp] else pure reconApp
    let rhsBase ← if isPair then mkAppM ``Prod.fst #[resArg] else pure resArg
    let out ← foldlMeta fields #[] fun out f => do
      if f.toString.startsWith "_sub_" then return out
      let projName := stateName ++ f
      if !env.contains projName then return out
      let some lhs ← try some <$> mkAppM projName #[lhsBase] catch _ => pure none | return out
      let some rhs ← try some <$> mkAppM projName #[rhsBase] catch _ => pure none | return out
      if ← isDefEq lhs rhs then
        let eqTy ← mkEq lhs rhs
        return out.push (reconName ++ f, ← mkLambdaFVars args (mkApp2 (mkConst ``id [Level.zero]) eqTy (← mkEqRefl rhs)))
      return out
    return if out.isEmpty then none else some out

@[noinline] def addReconcileProjLemmas (st : SimpTheorems) (reconName : Name) (goalConsts : Std.HashSet Name) : MetaM (Option SimpTheorems) := do
  let some lems ← mkReconcileProjLemmas reconName goalConsts | return none
  some <$> foldlMeta lems st fun st' (nm, pf) => st'.add (.other nm) #[] pf

elab "qedWithFreshHeartbeats" tac:tacticSeq : tactic => withFreshHeartbeatsT (evalTactic tac)

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
  let thms ← if extraNames.isEmpty then pure #[base] else match cacheKey? with
    | some k => pure #[base, ← getCachedSimpThms k extraNames false withEqns]
    | none   => pure #[← addSimpNamesWithEqns base extraNames false withEqns]
  mkSimpCtx cfg thms

class TryRestore (m : Type → Type) where
  run {α : Type} : α → (α → Bool) → m α → m α

@[noinline] def tryRestoreMeta {α : Type} (fail : α) (ok : α → Bool) (k : MetaM α) : MetaM α := do
  let st ← saveState
  try
    let r ← k
    unless ok r do restoreState st
    return r
  catch _ => restoreState st; return fail

@[noinline] def tryRestoreTactic {α : Type} (fail : α) (ok : α → Bool) (k : TacticM α) : TacticM α := do
  let st ← saveState
  try
    let r ← k
    unless ok r do restoreState st
    return r
  catch _ => restoreState st; return fail

instance : TryRestore MetaM := ⟨tryRestoreMeta⟩
instance : TryRestore TacticM := ⟨tryRestoreTactic⟩

@[inline] def tryRestoreM {m : Type → Type} [TryRestore m] {α : Type} (fail : α) (ok : α → Bool) (k : m α) : m α :=
  TryRestore.run fail ok k

def tryGoalM (g : MVarId) (k : MVarId → MetaM MVarId) : MetaM MVarId := tryRestoreM g (fun _ => true) (k g)
def tryGoalOptM (g : MVarId) (k : MVarId → MetaM (Option MVarId)) : MetaM (Option MVarId) := tryRestoreM (some g) (fun _ => true) (k g)

def simpGoalOnly (g : MVarId) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray := #[])
    (fvarIds : Array FVarId := #[]) (simplifyTarget : Bool := true) (dsimpOnly : Bool := false) : MetaM (Option MVarId) :=
  tryGoalOptM g fun g => do
    if dsimpOnly then return (← dsimpGoal g ctx simprocs simplifyTarget fvarIds).1
    return (← simpGoal g ctx simprocs none simplifyTarget fvarIds).1.map Prod.snd

def simpGoalAllHyps (g : MVarId) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray := #[]) (dsimpOnly : Bool := false) : MetaM (Option MVarId) := do
  simpGoalOnly g ctx simprocs (← g.withContext <| collectLCtxDecls fun d => pure (some d.fvarId)) true dsimpOnly

def trySimpAll (g : MVarId) (ctx : Simp.Context) (sp : Simp.SimprocsArray := #[]) : MetaM (Option MVarId) := tryGoalOptM g fun g => return (← simpAll g ctx sp).1
def trySplitTarget (g : MVarId) : MetaM (Option (List MVarId)) := tryRestoreM none Option.isSome (g.withContext (Meta.splitTarget? g))
def trySplitLocalDecl (g : MVarId) (fv : FVarId) : MetaM (Option (List MVarId)) := tryRestoreM none Option.isSome (g.withContext (Meta.splitLocalDecl? g fv))
def tryApplyConst (g : MVarId) (c : Name) : MetaM (Option (List MVarId)) := tryRestoreM none (fun _ => true) (some <$> g.applyConst c)

def tryReflGoal (g : MVarId) : MetaM Bool := tryRestoreM false id <| g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  if let some (_, lhs, rhs) := tgt.eq? then
    if ← isDefEq lhs rhs then
      let pf ← mkEqRefl lhs
      g.assign (if ← withTransparency .reducible (isDefEq lhs rhs) then pf else mkApp2 (mkConst ``id [Level.zero]) tgt pf)
      return true
    return false
  g.refl; return true

@[noinline] def closeGoalsByRfl : TacticM Unit := do setGoals (← filterUnsolvedM tryReflGoal (← getGoals))

@[noinline] private def splitGoalsWith (splitter : MVarId → MetaM (Option (List MVarId))) (post : MVarId → MetaM (Option MVarId)) : Nat → List MVarId → MetaM (List MVarId)
  | 0, gs => pure gs | _, [] => pure []
  | fuel + 1, g :: rest => do
      match ← splitter g with
      | none => return g :: (← splitGoalsWith splitter post fuel rest)
      | some sub => splitGoalsWith splitter post fuel ((← sub.filterMapM post) ++ rest)

@[noinline] def splitTargetsRec (fuel : Nat) (gs : List MVarId) (dCtx? : Option Simp.Context := none) : MetaM (List MVarId) :=
  splitGoalsWith trySplitTarget (match dCtx? with | some dCtx => (simpGoalOnly · dCtx (dsimpOnly := true)) | none => (pure <| some ·)) fuel gs

private def trySplitAny (g : MVarId) : MetaM (Option (List MVarId)) := do
  if let some sub ← trySplitTarget g then return some sub
  g.withContext <| findLCtxDecl? (includeLet := false) fun d => trySplitLocalDecl g d.fvarId

def tryTac (mk : TacticM (TSyntax `tactic)) (requireClosed : Bool := false) : TacticM Bool :=
  tryRestoreM false id do withoutRecover <| evalTactic (← mk); if requireClosed then return (← getGoals).isEmpty else return true

@[noinline] def forEachGoal (f : MVarId → TacticM Unit) : TacticM Unit := do
  let rec go (rem : List MVarId) : List MVarId → TacticM (List MVarId)
    | [] => pure rem | g :: rest => do setGoals [g]; f g; go (rem ++ (← getGoals)) rest
  setGoals (← go [] (← getGoals))

def extractForEachColl? (tgt : Expr) : Option Expr :=
  match tgt.consumeMData with
  | .forallE _ _ (.forallE _ memTy _ _) _ =>
      let m := memTy.consumeMData; if m.isAppOfArity ``Membership.mem 5 then some m.getAppArgs[3]!.consumeMData else none
  | _ => none

def collectGoalConsts (g : MVarId) (includeLCtx : Bool := false) : MetaM (Std.HashSet Name) := g.withContext do
  let s := (← instantiateMVars (← g.getType)).getUsedConstants.foldl (·.insert ·) {}
  if !includeLCtx then return s
  return (← collectLCtxDecls fun d => some <$> instantiateMVars d.type).foldl (init := s) fun acc ty => ty.getUsedConstants.foldl (·.insert ·) acc

@[noinline] def buildFastReconThms? (g0 : MVarId) (reconNames : Array Name) : MetaM (Option SimpTheorems) := do
  if reconNames.isEmpty then return none
  let goalConsts ← collectGoalConsts g0 true
  foldlMeta reconNames (some ({} : SimpTheorems)) fun acc? rn => match acc? with | none => pure none | some st => addReconcileProjLemmas st rn goalConsts

@[noinline] def buildFastReconCtx? (updNames reconNames : Array Name) (baseKey? : Option (String × Array Name) := none) : TacticM (Option Simp.Context) := do
  let g0 :: _ ← getGoals | return none
  let some projSt ← buildFastReconThms? g0 reconNames | return none
  let baseCtx ← mkDynamicSimpCtx (updNames.filter (·.getString! != "_reconcileHoisted")) baseKey? (withEqns := false)
  some <$> Simp.mkContext baseCtx.config (baseCtx.simpTheorems.push projSt) baseCtx.congrTheorems

def assertFacts (g0 : MVarId) (pfx : String) (facts : Array Expr) : MetaM (MVarId × Array FVarId) := do
  let (g, fvs, _) ← foldlMeta facts (g0, Array.mkEmpty facts.size, 0) fun (g, fvs, idx) p => do
    let (fv, g') ← (← g.assert (Name.mkSimple s!"{pfx}{idx}") (← g.withContext (inferType p)) p).intro1P
    return (g', fvs.push fv, idx + 1)
  return (g, fvs)

def namesToSimpLemmas (ns : Array Name) : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :=
  Qed.Lang.runPQTactic (Qed.Lang.mapPQ ns fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term))
def termsToSimpLemmas (ts : Array Term) : TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :=
  Qed.Lang.runPQTactic (Qed.Lang.mapPQ ts fun t => `(Lean.Parser.Tactic.simpLemma| $t:term))

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
    foldlMeta forallHyps () fun _ fh => tryEmitApp env ``Array.forall_elem #[sub.getAppArgs[7]!, fh] addFact
  if let .const c _ := sub.getAppFn then
    let a := sub.getAppArgs
    if let some (_, _, lem) := strLenFactRules.find? fun (fn, ar, _) => fn == c && ar == a.size then tryEmitApp env lem a addFact
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
  let (scan0, forallHyps) ← if !cfg.scanLCtx then pure (#[], #[]) else do
    let entries ← collectLCtxDecls fun decl => do
      let dty ← instantiateMVars decl.type
      if cfg.includeMacroPropHyps && !decl.isLet && decl.userName.hasMacroScopes then if ← isPropSafe dty then addFact decl.toExpr
      let es := if cfg.skipDecl decl dty then #[] else if cfg.scanLCtxValues then match decl.value? with | some val => #[decl.toExpr, val] | none => #[decl.toExpr] else #[dty]
      return some (es, if cfg.includeCollectionRules && dty.isForall then some decl.toExpr else none)
    pure (entries.foldl (init := (#[], #[])) fun (esAcc, fhAcc) (es, fh?) => (esAcc ++ es, match fh? with | some fh => fhAcc.push fh | none => fhAcc))
  let initScan ← foldlMeta extraExprs scan0 fun acc e => return acc.push (← instantiateMVars e)
  let rec runRounds : Nat → Array Expr → MetaM Unit
    | 0, _ => pure ()
    | r + 1, scanExprs => do
        if scanExprs.isEmpty then return
        stRef.modify fun s => { s with nextScan := #[] }
        foldlMeta scanExprs () fun _ e => e.forEach fun sub => do
          if !sub.hasLooseBVars then if !(← stRef.get).seen.contains sub then
            stRef.modify fun s => { s with seen := s.seen.insert sub }; inspectSubtermForFacts env cfg forallHyps sub addFact
        runRounds r (← stRef.get).nextScan
  runRounds cfg.rounds initScan
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
      g.assumptionCore
  if tgtC.isAppOfArity ``Eq 3 then if ← tryReflGoal g then return true
  if (tgtC.isAppOfArity ``LE.le 4 || tgtC.isAppOfArity ``GE.ge 4) && tgtC.getAppArgs[2]! == tgtC.getAppArgs[3]! then
    if ← tryRestoreM false id (return (← g.applyConst ``Nat.le_refl).isEmpty) then return true
  if ← withTransparency .reducible g.assumptionCore then return true
  if tgtC.isAppOfArity ``Or 2 then
    if ← tryRestoreM false id (do match ← g.applyConst ``Or.inl with | [gL] => gL.refl; return true | _ => return false) then return true
    if ← tryRestoreM false id (do match ← g.applyConst ``Or.inr with | [gR] => withTransparency .reducible gR.assumptionCore | _ => return false) then return true
  return false

def tryDirectDecide (g : MVarId) : MetaM Bool := do
  let tgt ← g.withContext do instantiateMVars (← g.getType)
  if tgt.hasFVar || tgt.hasMVar then return false
  tryRestoreM false id <| g.withContext do
    let decInst ← synthInstance (mkApp (mkConst ``Decidable) tgt)
    if ← isDefEq (mkApp2 (mkConst ``Decidable.decide) tgt decInst) (mkConst ``Bool.true) then
      g.assign (mkApp3 (mkConst ``of_decide_eq_true) tgt decInst rflBoolTrue); return true
    return false

def tryDirectOmega (g : MVarId) : MetaM Bool := tryRestoreM false id do
  let some g' ← g.falseOrByContra | return true
  g'.withContext do Omega.omega ((← getPropHyps).toList.map mkFVar) g' {}; return true

private def classifyIneq? (tgt : Expr) : Option (Bool × Expr × Expr × Expr) :=
  let a := tgt.getAppArgs
  match tgt.getAppFn.constName? with
  | some ``LE.le  => if a.size == 4 then some (true,  a[0]!, a[2]!, a[3]!) else none
  | some ``GE.ge  => if a.size == 4 then some (true,  a[0]!, a[3]!, a[2]!) else none
  | some ``LT.lt  => if a.size == 4 then some (false, a[0]!, a[2]!, a[3]!) else none
  | some ``GT.gt  => if a.size == 4 then some (false, a[0]!, a[3]!, a[2]!) else none
  | some ``Nat.le => if a.size == 2 then some (true,  mkConst ``Nat, a[0]!, a[1]!) else none
  | some ``Nat.lt => if a.size == 2 then some (false, mkConst ``Nat, a[0]!, a[1]!) else none
  | some ``Int.le => if a.size == 2 then some (true,  mkConst ``Int, a[0]!, a[1]!) else none
  | some ``Int.lt => if a.size == 2 then some (false, mkConst ``Int, a[0]!, a[1]!) else none
  | _ => none

private def unwrapLetOnce (lctx : LocalContext) (e : Expr) : Expr :=
  match e.consumeMData with
  | .fvar fv => match lctx.find? fv with | some d => (d.value?.getD e).consumeMData | none => e.consumeMData
  | e => e

private def scanNonlinearOps (e : Expr) (flags : UInt8) : UInt8 :=
  e.foldConsts flags fun c f => match c with
    | ``HMul.hMul | ``Mul.mul | ``Nat.mul | ``Int.mul => f ||| 1
    | ``HDiv.hDiv | ``Div.div | ``Nat.div             => f ||| 2
    | ``HMod.hMod | ``Mod.mod | ``Nat.mod             => f ||| 4
    | _ => f

@[noinline] private def trySolveDivModBound (g : MVarId) (tgt lhs rhs : Expr) (isDiv : Bool) : MetaM Bool := do
  let pair? := if isDiv then
      if lhs.isAppOfArity ``HDiv.hDiv 6 then some (lhs.getAppArgs[4]!, lhs.getAppArgs[5]!)
      else if lhs.isAppOfArity ``Nat.div 2 then some (lhs.getAppArgs[0]!, lhs.getAppArgs[1]!) else none
    else
      if lhs.isAppOfArity ``HMod.hMod 6 then some (lhs.getAppArgs[4]!, lhs.getAppArgs[5]!)
      else if lhs.isAppOfArity ``Nat.mod 2 then some (lhs.getAppArgs[0]!, lhs.getAppArgs[1]!) else none
  let some (n, k) := pair? | return false
  tryRestoreM false id do
    let pf ← if isDiv then
        let m ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Nat.le) n rhs)
        unless ← tryDirectOmega m.mvarId! do return false
        mkAppM ``Nat.le_trans #[mkApp2 (mkConst ``Nat.div_le_self) n k, ← instantiateMVars m]
      else
        let m1 ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Nat.lt) (mkNatLit 0) k)
        unless ← tryDirectOmega m1.mvarId! do return false
        let m2 ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Nat.le) k rhs)
        unless ← tryDirectOmega m2.mvarId! do return false
        mkAppM ``Nat.lt_of_lt_of_le #[mkApp3 (mkConst ``Nat.mod_lt) n k (← instantiateMVars m1), ← instantiateMVars m2]
    if ← isDefEq (← inferType pf) tgt then g.assign pf; return true else return false

/-- Guarded MetaM nonlinear inequality closer: exits in 0ms unless the goal target is a Nat/Int
    inequality involving `*`, `/`, or `%`, and never creates unconstrained metavariables. -/
@[noinline] def tryCloseNonlinear (g : MVarId) : MetaM Bool := g.withContext do
  let tgt := (← instantiateMVars (← g.getType)).consumeMData
  let some (isLe, ty0, lhs0, rhs0) := classifyIneq? tgt | return false
  let lctx ← getLCtx
  let scanLet (e : Expr) (f : UInt8) : UInt8 := let u := unwrapLetOnce lctx e; if u != e then scanNonlinearOps u f else f
  let f0 := scanNonlinearOps tgt 0
  let flags := if f0 == 0 && tgt.hasFVar then scanLet rhs0 (scanLet lhs0 0) else f0
  if flags == 0 then return false
  let ty ← if ty0.isConstOf ``Nat || ty0.isConstOf ``Int then pure ty0 else whnf ty0
  let tryArms (arms : Array Name) : MetaM Bool :=
    foldlMeta arms false fun ok c => if ok then pure true else tryRestoreM false id (do closeAllGoals tryDirectOmega (← g.applyConst c))
  if ty.isConstOf ``Nat then
    if isLe then
      if (flags &&& 1) != 0 then if ← tryArms #[``Nat.mul_le_mul, ``Nat.mul_le_mul_left, ``Nat.mul_le_mul_right] then return true
      if (flags &&& 2) != 0 then
        if ← tryArms #[``Nat.div_le_div_right] then return true
        return ← trySolveDivModBound g tgt (unwrapLetOnce lctx lhs0) rhs0 true
    else
      if (flags &&& 1) != 0 then if ← tryArms #[``Nat.mul_lt_mul_of_pos_left, ``Nat.mul_lt_mul_of_pos_right] then return true
      if (flags &&& 4) != 0 then return ← trySolveDivModBound g tgt (unwrapLetOnce lctx lhs0) rhs0 false
  else if ty.isConstOf ``Int && isLe && (flags &&& 1) != 0 then
    return ← tryArms #[``Int.mul_nonneg, ``Int.mul_le_mul_of_nonneg_left, ``Int.mul_le_mul_of_nonneg_right, ``Int.mul_le_mul]
  return false

elab "qedNonlinearClose" : tactic => do
  if ← tryCloseNonlinear (← getMainGoal) then replaceMainGoal [] else throwError "qedNonlinearClose failed"

@[noinline] private partial def buildGroundKernelProof (check : Bool) (e : Expr) : MetaM (Option Expr) := do
  let isKDefEq (a b : Expr) : MetaM Bool := do return match Kernel.isDefEq (← getEnv) (← getLCtx) a b with | .ok true => true | _ => false
  let e := e.consumeMData
  match e with
  | .letE n ty v b nondep =>
      withLetDecl n ty v (nondep := nondep) fun fv => do
        let some pf ← buildGroundKernelProof check (b.instantiate1 fv) | return none
        return some (Expr.letE n ty v (pf.abstract #[fv]) nondep)
  | _ =>
      if e.isConstOf ``True then return some (mkConst ``True.intro)
      if e.isAppOfArity ``And 2 then
        let a := e.getAppArgs[0]!; let b := e.getAppArgs[1]!
        let some pa ← buildGroundKernelProof check a | return none
        let some pb ← buildGroundKernelProof check b | return none
        return some (mkApp4 (mkConst ``And.intro) a b pa pb)
      if let some (ty, lhs, rhs) := e.eq? then
        if !check then return some (mkApp2 (mkConst ``Eq.refl [← getLevel ty]) ty lhs)
        if ← isKDefEq lhs rhs then return some (mkApp2 (mkConst ``Eq.refl [← getLevel ty]) ty lhs)
      match ← trySynthInstance (mkApp (mkConst ``Decidable) e) with
      | .some decInst =>
          if !check then return some (mkApp3 (mkConst ``of_decide_eq_true) e decInst rflBoolTrue)
          if ← isKDefEq (mkApp2 (mkConst ``Decidable.decide) e decInst) (mkConst ``Bool.true) then
            return some (mkApp3 (mkConst ``of_decide_eq_true) e decInst rflBoolTrue)
          return none
      | _ => return none

/-- Close a ground goal quickly without blowing elaborator `maxRecDepth`. -/
def tryCloseGroundKernel (g : MVarId) (check : Bool := true) : MetaM Bool := do
  if ← tryCloseTrivial g (reducibleOnly := true) then return true
  let tgt ← g.withContext do instantiateMVars (← g.getType)
  if !tgt.hasFVar && !tgt.hasMVar && !tgt.hasLevelMVar then
    if let some pf ← withLCtx {} {} (buildGroundKernelProof check tgt) then g.assign pf; return true
  return false

elab "qedCloseGround" : tactic => do
  if ← tryCloseGroundKernel (← getMainGoal) (check := true) then replaceMainGoal [] else throwError "qedCloseGround failed"
elab "qedCloseGroundKernel" : tactic => do
  if ← tryCloseGroundKernel (← getMainGoal) (check := false) then replaceMainGoal [] else throwError "qedCloseGroundKernel failed"

def tryCloseBasic (g : MVarId) (skipTarget : Expr → Bool := fun _ => false) (reducibleOnly : Bool := false) : MetaM Bool := do
  if ← tryCloseTrivial g skipTarget reducibleOnly then return true
  if ← tryDirectDecide g then return true
  tryDirectOmega g

def splitAndHypsGoal (g0 : MVarId) (existsOnly : Bool := false) (maxIters : Nat := 32) : MetaM (MVarId × Bool) := do
  let isMatchTy (t : Expr) := t.isAppOfArity ``Exists 2 || (!existsOnly && (t.isAppOfArity ``And 2 || t.isAppOfArity ``Qed.Lang.QedAndProp 2))
  let rec go (g : MVarId) (didSplit : Bool) : Nat → MetaM (MVarId × Bool)
    | 0 => pure (g, didSplit)
    | r + 1 => do
        let nextG? ← g.withContext <| findLCtxDecl? (includeLet := false) fun decl => do
          let tC := decl.type.consumeMData
          if isMatchTy tC || match tC.getAppFn with | .const c _ => !nonRefinedHeads.contains c | _ => true then
            tryRestoreM none Option.isSome do if isMatchTy (← whnf tC) then return ((← g.cases decl.fvarId)[0]?).map (·.mvarId) else return none
          else return none
        match nextG? with | some g' => go g' true r | none => pure (g, didSplit)
  go g0 false maxIters

def splitGoalAnds (g0 : MVarId) (maxIters : Nat := 64) : MetaM (List MVarId) := do
  let rec loop : Nat → List MVarId → MetaM (List MVarId)
    | 0, gs => return gs | _, [] => return []
    | fuel + 1, g :: rest => do
        let t := (← g.withContext (instantiateMVars (← g.getType))).consumeMData
        if t.isAppOfArity ``And 2 || t.isAppOfArity ``Qed.Lang.QedAndProp 2 then
          if let some [g1, g2] ← tryApplyConst g ``And.intro then return ← loop fuel (g1 :: g2 :: rest)
        return g :: (← loop fuel rest)
  loop maxIters [g0]

@[noinline] private def tryGrindGoal (g : MVarId) : TacticM Bool := do
  let saved ← getGoals; setGoals [g]
  let ok ← tryTac (requireClosed := true) (Qed.Lang.runPQTactic `(tactic| grind))
  setGoals saved; return ok

structure CloseFallbackConfig where
  skipTarget : Expr → Bool := fun _ => false
  trySimpStarOmega : Bool := false
  simpAllCfg : Simp.Config := { zetaDelta := false }
  deepExtraSimpAll : Array Name := #[]

@[noinline] def closeWithFallback (g : MVarId) (cfg : CloseFallbackConfig := {}) : TacticM Bool := do
  if cfg.trySimpStarOmega then
    if ← tryRestoreM false id do
      let stWithHyps ← g.withContext do
        let hyps ← collectLCtxDecls (includeLet := false) fun d => do if ← isPropSafe d.type then pure (some (d.fvarId, d.toExpr)) else pure none
        foldlMeta hyps (← getSimpTheorems) fun st (fv, e) => try st.add (.fvar fv) #[] e catch _ => pure st
      match ← simpGoalOnly g (← mkSimpCtx cfg.simpAllCfg #[stWithHyps]) with | none => return true | some g' => tryDirectOmega g'
    then return true
  if ← tryRestoreM false id do
    match ← trySimpAll g (← mkSimpCtxWithBase #[] cfg.simpAllCfg) with
    | none => return true | some g' => tryCloseBasic g' cfg.skipTarget
  then return true
  if ← tryCloseNonlinear g then return true
  if ← tryRestoreM false id do
    let deepCtx ← mkSimpCtxWithBase cfg.deepExtraSimpAll (withEqns := true); let sp := #[← Simp.getSimprocs]
    let some g1 ← trySimpAll g deepCtx sp | return true
    let gs ← splitGoalsWith trySplitAny (trySimpAll · deepCtx sp) 16 [g1]
    closeAllGoals (fun sg => do if ← tryDirectOmega sg then pure true else if ← tryDirectDecide sg then pure true else tryReflGoal sg) gs
  then return true
  tryGrindGoal g

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
    trySimpAll (← splitAndHypsGoal g3).1 extraCtx sp
  let runPass (close : Bool) : TacticM Unit := forEachGoal fun g => do
    let some g' ← simplify g (close && harvestFacts) | setGoals []
    if !close then setGoals [g']
    else if ← tryCloseBasic g' then setGoals []
    else if ← tryGrindGoal g' then setGoals []
    else setGoals [g']
  if ← tryRestoreM false id (do runPass true; return (← getGoals).isEmpty) then return true
  if !clearErrorsOnFail then try runPass false catch _ => pure ()
  return false

private def boundaryLemmaGroups : Array (Name × Array Name) := #[
  (``Array.size, #[``Array.size_push, ``Array.size_modify, ``Array.size_set, ``Array.size_pop, ``Array.size_map, ``Array.size_append, ``Array.size_eraseIdx, ``Array.size_reverse, ``Array.size_extract, ``Array.size_swap, ``Array.size_mergeSort,
    ``Qed.qedSortKey_array_size, ``Qed.qedSortDescKey_array_size, ``Qed.qedSortCmp_array_size, ``Qed.qedSortDescCmp_array_size]),
  (``Array.sumBy, #[``Array.sumBy_empty, ``Array.sumBy_push, ``Array.sumBy_append, ``Array.sumBy_map, ``Array.sumBy_reverse, ``Array.sumBy_mergeSort, ``Qed.sumBy_qedSortKey]),
  (``Array.sumByInt, #[``Array.sumByInt_empty, ``Array.sumByInt_push, ``Array.sumByInt_append, ``Array.sumByInt_map, ``Array.sumByInt_reverse, ``Array.sumByInt_mergeSort, ``Qed.sumByInt_qedSortKey]),
  (``Array.countWhere, #[``Array.countWhere_empty, ``Array.countWhere_push, ``Array.countWhere_append, ``Array.countWhere_reverse, ``Array.countWhere_mergeSort, ``Qed.countWhere_qedSortKey]),
  (``Array.uniqueBy, #[``Array.uniqueBy_empty, ``Array.uniqueBy_push_iff]),
  (``Array.isSortedBy, #[``Array.isSortedBy_empty, ``Array.isSortedBy_singleton, ``Array.isSortedBy_push_iff]),
  (``Qed.qedIsSortedKey, #[``Qed.qedIsSortedKey_sortKey, ``Qed.qedIsSortedKey_array_empty, ``Qed.qedIsSortedKey_array_singleton, ``Qed.qedIsSortedKey_array_push_iff, ``Qed.qedIsSortedKey_list_nil, ``Qed.qedIsSortedKey_list_singleton]),
  (``Qed.qedIsSortedDescKey, #[``Qed.qedIsSortedDescKey_sortDescKey]),
  (``List.length, #[``List.length_cons, ``List.length_append, ``List.length_map,
    ``Qed.qedSortKey_list_length, ``Qed.qedSortDescKey_list_length, ``Qed.qedSortCmp_list_length, ``Qed.qedSortDescCmp_list_length]),
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

@[noinline] def runUnfoldPresent (extra : Array Term) (skip : Array Name := #[]) : TacticM Unit := do
  let g :: _ ← getGoals | return
  let cs ← collectGoalConsts g true
  let fixedL := (← namesToSimpLemmas (relevantAppLemmas (← getEnv) cs ++ relevantBoundaryLemmas cs)) ++ (← termsToSimpLemmas extra)
  Qed.qedUnfoldHelperLoop 12 (fun env n => if skip.contains n || !Qed.qedIsHelper env n then return false else return (← getProjectionFnInfo? n).isNone)
    fixedL (includeLCtx := true) (useSimpAll := true)

@[noinline] private def tryCloseAutoAtom (g : MVarId) : MetaM Bool := do
  if ← tryCloseTrivial g (reducibleOnly := true) then return true
  if ← tryRestoreM false id (g.contradictionCore {}) then return true
  if ← tryCloseBasic g then return true
  if ← tryCloseNonlinear g then return true
  tryRestoreM false id g.assumptionCore

@[noinline] private def runAutoClose : TacticM Unit := do
  let g ← getMainGoal
  if ← tryCloseAutoAtom g then replaceMainGoal []; return
  let ok ← tryRestoreM false id do
    let gs ← splitGoalAnds g
    let rec go : List MVarId → TacticM Bool
      | [] => pure true
      | sg :: rest => do
          if ← tryCloseAutoAtom sg then go rest
          else if ← tryGrindGoal sg then go rest
          else pure false
    go gs
  if ok then replaceMainGoal [] else throwError "qedAutoClose failed"

elab "qedUnfoldPresent" "[" extra:term,* "]" : tactic => runUnfoldPresent extra.getElems
elab "qedFastClose" : tactic => do
  if ← tryCloseTrivial (← getMainGoal) (reducibleOnly := true) then replaceMainGoal [] else throwError "qedFastClose: not trivially closed"
elab "qedAutoClose" : tactic => runAutoClose

structure ParsedBlindTarget where
  paramId : Ident
  fields  : Array Ident

def parseBlindTarget (stx : Syntax) (includeGot : Bool := true) : Command.CommandElabM ParsedBlindTarget := do
  let rawId : Ident := ⟨stx.getArg 0⟩; let optBraces := stx.getArg 1
  if optBraces.getNumArgs == 3 then return { paramId := rawId, fields := (optBraces.getArg 1).getSepArgs.map (⟨·⟩) }
  match rawId.getId.eraseMacroScopes with
  | .str .anonymous _ => return { paramId := rawId, fields := #[] }
  | .str (.str .anonymous p) f => return { paramId := mkIdentFrom rawId (Name.mkSimple p), fields := #[mkIdentFrom rawId (Name.mkSimple f)] }
  | _ => throwErrorAt rawId s!"`blindTo` expects `<param>`, `<param>.<field>`, or `<param>.\{f1, f2}`{if includeGot then s!", got `{rawId.getId}`" else ""}"

def fmtBlindTarget (t : ParsedBlindTarget) : String :=
  if t.fields.isEmpty then t.paramId.getId.toString
  else if t.fields.size == 1 then s!"{t.paramId.getId}.{t.fields[0]!.getId}"
  else s!"{t.paramId.getId}.\{" ++ String.intercalate ", " (t.fields.toList.map (·.getId.toString)) ++ "}"

@[noinline] def buildBlindToArgs (targets : Array ParsedBlindTarget) (validParamNames : Array Name)
    (binderIds : Array Ident) (binderTys : Array Term) (fnErrCtx? : Option String := none) :
    Command.CommandElabM (Array (Ident × Option Term) × Array Term × Array Term) := do
  let paramBlinds ← Qed.Lang.foldlCmd targets (#[] : Array (Name × Bool × Array Ident)) fun paramBlinds t => do
    let pn := t.paramId.getId.eraseMacroScopes
    unless validParamNames.contains pn do
      match fnErrCtx? with
      | some fnStr => throwErrorAt t.paramId s!"unknown parameter `{pn}` in `blindTo` of `{fnStr}`"
      | none => throwErrorAt t.paramId s!"unknown parameter `{pn}` in `blindTo`{Qed.Diag.didYouMean pn.toString (validParamNames.toList.map toString)}"
    if let some pos := paramBlinds.findIdx? (·.1 == pn) then
      let (_, whole, flds) := paramBlinds[pos]!
      let whole' := whole || t.fields.isEmpty
      let flds' := if whole' then #[] else t.fields.foldl (fun acc f => if acc.any (·.getId.eraseMacroScopes == f.getId.eraseMacroScopes) then acc else acc.push f) flds
      return paramBlinds.set! pos (pn, whole', flds')
    else return paramBlinds.push (pn, t.fields.isEmpty, t.fields)
  Qed.Lang.runPQ <| Qed.Lang.foldlPQ (binderIds.zip binderTys) (#[], #[], #[]) fun (freshVars, lhsArgs, rhsArgs) (bId, bTy) => do
    let bn := bId.getId.eraseMacroScopes; let rhsArgs := rhsArgs.push ⟨bId.raw⟩
    match paramBlinds.find? (·.1 == bn) with
    | none => return (freshVars, lhsArgs.push ⟨bId.raw⟩, rhsArgs)
    | some (_, true, _) => let fv := mkIdent (Name.mkSimple s!"_qed_blind_{bn}"); return (freshVars.push (fv, some bTy), lhsArgs.push ⟨fv.raw⟩, rhsArgs)
    | some (_, false, flds) =>
        let (freshVars, updIds, updVals) := flds.foldl (init := (freshVars, #[], #[])) fun (fvA, uI, uV) f =>
          let fv := mkIdent (Name.mkSimple s!"_qed_blind_{bn}_{f.getId.eraseMacroScopes}"); (fvA.push (fv, none), uI.push f, uV.push ⟨fv.raw⟩)
        return (freshVars, lhsArgs.push (← `({ $bId with $[$updIds:ident := $updVals:term],* })), rhsArgs)

@[noinline] def mkBlindToEqProp (freshVars : Array (Ident × Option Term)) (lhsCall rhsCall : Term) : Command.CommandElabM Term :=
  Qed.Lang.runPQ do
    Qed.Lang.foldrPQ freshVars (← `($lhsCall = $rhsCall)) fun (fv, ty?) acc => match ty? with
      | some ty => `(∀ ($fv:ident : $ty), $acc) | none => `(∀ $fv:ident, $acc)

private def staticInvNormNames : Array Name := #[
  `Qed.Lang.QedVal.val_id, `Qed.Lang.QedSeqLit.ofList_array, `Qed.Lang.QedSeqLit.ofList_list,
  `Qed.Lang.QedMemProp.memProp_array, `Qed.Lang.QedMemProp.memProp_list, ``Array.mem_def,
  ``Bool.and_eq_true, ``Bool.or_eq_true, ``Bool.not_eq_true', ``Bool.not_eq_false',
  ``decide_eq_true_eq, ``decide_eq_false_iff_not, ``beq_iff_eq, ``bne_iff_ne]

@[noinline] def lowerStaticInvExpr (aliases : Array (String × Term)) (stx : Syntax) : Elab.Command.CommandElabM Term := do
  let foldProjs (ref : Syntax) (base : Term) (fs : List Name) : ReaderT (Array String) Elab.Command.CommandElabM Term :=
    fs.foldlM (init := base) fun acc f => `(($acc).$(mkIdentFrom ref f):ident)
  let hooks : Qed.Lang.LowerHooks (ReaderT (Array String) Elab.Command.CommandElabM) :=
    { Qed.Lang.LowerHooks.mkDefault (fun ref msg => throwErrorAt ref msg) with
      withLocals := fun names => withReader (· ++ names)
      lowerType := fun t => Elab.liftMacroM (return (← Qed.Lang.lowerQedType t false).1)
      lowerPat := fun p => Elab.liftMacroM (Qed.Lang.lowerQedPat p)
      lowerIdent := fun ref id mode => do
        let locals ← read
        match id.getId.eraseMacroScopes.components with
        | [] => pure ⟨id.raw⟩
        | root :: rest =>
            let rs := root.toString
            if locals.contains rs then pure ⟨id.raw⟩
            else if let some (_, tgt) := aliases.find? (·.1 == rs) then foldProjs ref tgt rest
            else if !rest.isEmpty then pure ⟨id.raw⟩
            else match rs with
              | "true" => if mode == .propInv then `(True) else `(true)
              | "false" => if mode == .propInv then `(False) else `(false)
              | "none" => `(Option.none)
              | _ => pure ⟨id.raw⟩ }
  (Qed.Lang.lowerQedExpr hooks .propInv stx).run #[]

@[noinline] private def closeStaticInvSubgoal (unfolds : Array Name) (g : MVarId) : MetaM Bool := do
  if ← tryCloseGroundKernel g (check := true) then return true
  if ← tryCloseBasic g then return true
  let (_, g1) ← g.intros
  if ← tryCloseGroundKernel g1 (check := true) then return true
  if ← tryCloseBasic g1 then return true
  let ctx ← mkDynamicSimpCtx (staticInvNormNames ++ unfolds) none { zetaDelta := false } (withEqns := false)
  match ← simpGoalOnly g1 ctx with
  | none => return true
  | some g2 =>
      closeAllGoals (fun sg => do
        if ← tryCloseGroundKernel sg (check := true) then return true
        tryCloseBasic sg) (← splitGoalAnds g2)

/-- Elaborate and verify a compile-time `invariant <name>: <qedExpr>,+` over static metadata or top-level propositions. -/
@[noinline] def elabStaticMetaInv (scopeLabel : String) (fullDeclName : Name) (aliases : Array (String × Term))
    (unfolds : Array Name) (invId : Ident) (exprs : Array Syntax) (pf? : Option Term := none)
    (doc? : Option (TSyntax ``Lean.Parser.Command.docComment) := none) (isPrivate : Bool := false) : Elab.Command.CommandElabM Unit := do
  let lowered ← Qed.Lang.mapCmd exprs (lowerStaticInvExpr aliases)
  let combined ← Elab.liftMacroM <| Qed.mkConjBody lowered (ascribeProp := false)
  let invLeaf := invId.getId.eraseMacroScopes
  let dispName := if scopeLabel.isEmpty then invLeaf.toString else s!"{scopeLabel}.{invLeaf}"
  if let some pfT := pf? then
    let cmd ← Qed.Lang.runPQ `(command| $[$doc?:docComment]? theorem $(mkIdentFrom invId (`_root_ ++ fullDeclName)):ident : $combined := $pfT)
    Qed.Lang.elabCmdWithVis isPrivate cmd
    return
  let res ← Elab.Command.liftTermElabM do
    let propExpr ← instantiateMVars (← Term.elabTermEnsuringType combined (some (mkSort Level.zero)))
    Term.synthesizeSyntheticMVarsNoPostponing
    let propExpr ← instantiateMVars propExpr
    let savedMsgs ← Core.getMessageLog; Core.resetMessageLog
    let mvar ← Meta.mkFreshExprSyntheticOpaqueMVar propExpr
    let ok ← try
      let rem ← filterUnsolvedM (closeStaticInvSubgoal unfolds) (← splitGoalAnds mvar.mvarId!)
      pure (rem.isEmpty && !(← Core.getMessageLog).hasErrors)
    catch _ => pure false
    Core.setMessageLog savedMsgs
    if ok then return Except.ok (propExpr, ← instantiateMVars mvar)
    else
      let pp ← Qed.Diag.ppQedExpr propExpr
      return Except.error pp
  match res with
  | .ok (propExpr, proofVal) =>
      Elab.Command.liftTermElabM do
        let env ← getEnv
        let declName := if isPrivate then mkPrivateName env fullDeclName else fullDeclName
        addDecl (.thmDecl { name := declName, levelParams := [], type := propExpr, value := proofVal })
        addDeclarationRangesFromSyntax declName invId
        addDocString' declName Syntax.missing doc?
  | .error pp =>
      throwErrorAt invId s!"Invariant `{dispName}` failed:\n  • must satisfy:  {pp}"

end Qed.Verify.Core
