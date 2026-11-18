import Lean
import Qed.Schema
import Qed.Server.Core
import Qed.Server.Syntax

namespace Qed.Server

/-! ## Control-Flow Combinators & Auto-Lifting Helpers (`@[reducible]` for Zero-Cost Proofs & C Codegen) -/

/-- Index conversion allowing both `Nat` and `Fin n` to index `Array`s uniformly across mutations. -/
class SrvIdx (ι : Type) where
  toNat : ι → Nat

@[inline] instance : SrvIdx Nat := ⟨id⟩
@[inline] instance {n : Nat} : SrvIdx (Fin n) := ⟨Fin.val⟩

@[simp] theorem SrvIdx.toNat_nat (i : Nat) : SrvIdx.toNat i = i := rfl
@[simp] theorem SrvIdx.toNat_fin {n : Nat} (i : Fin n) : SrvIdx.toNat i = i.val := rfl

/-- Auto-lifts plain values `v : T` to `some v` in `T?` functions while keeping `Option T` un-nested. -/
class SrvLiftOpt (α : Type) (Inner : Type) where
  liftOpt : α → Option Inner

@[inline] instance {Inner : Type} : SrvLiftOpt (Option Inner) Inner := ⟨id⟩
@[inline] instance {Inner : Type} {p : Inner → Prop} : SrvLiftOpt (Qed.Field p) Inner := ⟨fun f => some f.val⟩
@[inline] instance {Inner : Type} {p : Inner → Prop} : SrvLiftOpt (Option (Qed.Field p)) Inner := ⟨Option.map Qed.Field.val⟩
@[inline] instance (priority := low) {Inner : Type} : SrvLiftOpt Inner Inner := ⟨Option.some⟩

@[simp] theorem SrvLiftOpt.liftOpt_opt {Inner : Type} (x : Option Inner) :
    SrvLiftOpt.liftOpt x = x := rfl
@[simp] theorem SrvLiftOpt.liftOpt_val {Inner : Type} (x : Inner) :
    SrvLiftOpt.liftOpt (Inner := Inner) x = some x := rfl

/-- Overloaded `fail(...)` builder supporting `fail("msg")`, `fail(code, "msg")`, and `fail(.tag, "msg")`. -/
def mkFail1 (msg : String) : ApiError := ApiError.badRequest msg
def mkFail2 (code : Nat) (msg : String) : ApiError := { code, message := msg }
def mkFailDom {ε : Type} (tag : ε) (msg : String) : SrvFailure ε := .domain tag msg

/-- Uniform API-error lifting for `ApiError` and inferred `SrvFailure ε`. -/
class SrvErr (E : Type) where
  ofApi : ApiError → E

@[reducible] instance : SrvErr ApiError := ⟨id⟩
@[reducible] instance {ε : Type} : SrvErr (SrvFailure ε) := ⟨SrvFailure.api⟩

/-- Unwraps `Except (SrvFailure ε)`, `Except ApiError`, `Except String`, or `Option` for `?` and `catch`. -/
class SrvUnwrap (E : Type) (W : Type) (Val : outParam Type) where
  unwrap : W → Except E Val

@[reducible] instance {E α : Type} : SrvUnwrap E (Except E α) α where
  unwrap := id

@[reducible] instance {ε α : Type} : SrvUnwrap (SrvFailure ε) (Except ApiError α) α where
  unwrap
    | .ok a    => .ok a
    | .error e => .error (.api e)

@[reducible] instance {E α : Type} [SrvErr E] : SrvUnwrap E (Except String α) α where
  unwrap
    | .ok a    => .ok a
    | .error e => .error (SrvErr.ofApi (ApiError.badRequest e))

@[reducible] instance {E α : Type} [SrvErr E] : SrvUnwrap E (Option α) α where
  unwrap
    | some a => .ok a
    | none   => .error (SrvErr.ofApi (ApiError.notFound "optional value was empty"))

/-- Unwraps `Option α` or `Except ApiError α` inside `T?` functions (`none` exits cleanly as `.ok none`). -/
class SrvUnwrapOpt (W : Type) (Inner : Type) (Val : outParam Type) where
  unwrapOpt : W → Except (Except ApiError (Option Inner)) Val

@[reducible] instance {Inner α : Type} : SrvUnwrapOpt (Option α) Inner α where
  unwrapOpt
    | some a => .ok a
    | none   => .error (.ok none)

@[reducible] instance {Inner α : Type} : SrvUnwrapOpt (Except ApiError α) Inner α where
  unwrapOpt
    | .ok a    => .ok a
    | .error e => .error (.error e)

/-- Pure statement sequencing with early `return` short-circuiting. -/
@[inline]
def srvSeq {σ ρ : Type} (first : σ × Option ρ) (next : σ → σ × Option ρ) : σ × Option ρ :=
  match first with
  | (s', none)   => next s'
  | (s', some r) => (s', some r)

@[simp] theorem srvSeq_none {σ ρ : Type} (s : σ) (next : σ → σ × Option ρ) :
    srvSeq (s, none) next = next s := rfl

@[simp] theorem srvSeq_some {σ ρ : Type} (s : σ) (r : ρ) (next : σ → σ × Option ρ) :
    srvSeq (s, some r) next = (s, some r) := rfl

/-- Transactional finalizer: commits `s'` on `.ok`, rolls back to entry state `s₀` on `.error`. -/
@[inline]
def srvFinish {E σ α : Type} [SrvErr E] (s₀ : σ) (res : σ × Option (Except E α)) : σ × Except E α :=
  match res with
  | (s', some (.ok v))    => (s', .ok v)
  | (_,  some (.error e)) => (s₀, .error e)
  | (_,  none)            => (s₀, .error (SrvErr.ofApi (ApiError.internal "unreachable missing return")))

@[simp] theorem srvFinish_ok {E σ α : Type} [SrvErr E] (s₀ s' : σ) (v : α) :
    srvFinish (E := E) s₀ (s', some (.ok v)) = (s', .ok v) := rfl

@[simp] theorem srvFinish_err {E σ α : Type} [SrvErr E] (s₀ s' : σ) (e : E) :
    srvFinish (E := E) (α := α) s₀ (s', some (.error e)) = (s₀, .error e) := rfl

@[simp] theorem srvFinish_none {E σ α : Type} [SrvErr E] (s₀ s' : σ) :
    srvFinish (E := E) s₀ (s', (none : Option (Except E α))) =
      (s₀, .error (SrvErr.ofApi (ApiError.internal "unreachable missing return"))) := rfl

/-- Transactional finalizer for `atomic` statement blocks: commits `s'` on `none`/`some (.ok v)`, rolls back to `s₀` on `some (.error e)`. -/
@[inline]
def srvAtomicCommit {E σ α : Type} (s₀ : σ) (res : σ × Option (Except E α)) :
    σ × Option (Except E α) :=
  match res with
  | (s', none)                  => (s', none)
  | (s', some (Except.ok v))    => (s', some (Except.ok v))
  | (_,  some (Except.error e)) => (s₀, some (Except.error e))

@[simp] theorem srvAtomicCommit_none {E σ α : Type} (s₀ s' : σ) :
    srvAtomicCommit (E := E) (α := α) s₀ (s', none) = (s', none) := rfl

@[simp] theorem srvAtomicCommit_ok {E σ α : Type} (s₀ s' : σ) (v : α) :
    srvAtomicCommit (E := E) s₀ (s', some (Except.ok v)) = (s', some (Except.ok v)) := rfl

@[simp] theorem srvAtomicCommit_err {E σ α : Type} (s₀ s' : σ) (e : E) :
    srvAtomicCommit (E := E) (α := α) s₀ (s', some (Except.error e)) = (s₀, some (Except.error e)) := rfl

/-- Effectful statement sequencing for `await`-containing handlers. -/
@[inline, specialize]
def srvSeqM {m : Type → Type} [Monad m] {ρ : Type}
    (first : m (Option ρ)) (next : Unit → m (Option ρ)) : m (Option ρ) := do
  match ← first with
  | some r => return some r
  | none   => next ()

@[inline, specialize]
def srvFinishM {E : Type} [SrvErr E] {m : Type → Type} [Monad m] {α : Type}
    (res : m (Option (Except E α))) : m (Except E α) := do
  match ← res with
  | some r => return r
  | none   => return .error (SrvErr.ofApi (ApiError.internal "unreachable missing return"))

/-! ## Opaque Equality-Abstracted SSA Stepping (`srvLetEq`) -/

/-- Continuation-passing equality binder keeping intermediate state updates opaque (`cdecl` + `hx : x = val`)
    so bounds checks and invariant leaves never suffer `zetaDelta` term-size blowup. -/
@[inline]
def srvLetEq {α β : Type} (val : α) (k : (x : α) → x = val → β) : β :=
  k val rfl

theorem srvLetEq_elim {α β : Type} (P : β → Prop) (val : α) (k : (x : α) → x = val → β)
    (hk : ∀ (x : α) (hx : x = val), P (k x hx)) : P (srvLetEq val k) :=
  hk val rfl

@[simp] theorem srvFinish_srvLetEq {E σ α γ : Type} [SrvErr E] (s₀ : σ) (val : γ)
    (k : (x : γ) → x = val → σ × Option (Except E α)) :
    srvFinish s₀ (srvLetEq val k) = srvLetEq val (fun x hx => srvFinish s₀ (k x hx)) := rfl

@[simp] theorem srvAtomicCommit_srvLetEq {E σ α γ : Type} (s₀ : σ) (val : γ)
    (k : (x : γ) → x = val → σ × Option (Except E α)) :
    srvAtomicCommit s₀ (srvLetEq val k) = srvLetEq val (fun x hx => srvAtomicCommit s₀ (k x hx)) := rfl

@[simp] theorem srvSeq_srvLetEq {σ ρ γ : Type} (val : γ)
    (k : (x : γ) → x = val → σ × Option ρ) (next : σ → σ × Option ρ) :
    srvSeq (srvLetEq val k) next = srvLetEq val (fun x hx => srvSeq (k x hx) next) := rfl

@[simp] theorem prod_fst_srvLetEq {α β γ : Type} (val : γ)
    (k : (x : γ) → x = val → α × β) :
    (srvLetEq val k).1 = srvLetEq val (fun x hx => (k x hx).1) := rfl

@[simp] theorem prod_snd_srvLetEq {α β γ : Type} (val : γ)
    (k : (x : γ) → x = val → α × β) :
    (srvLetEq val k).2 = srvLetEq val (fun x hx => (k x hx).2) := rfl

/-! ## Custom Term Elaborators for Proven Bounds (`srvGetElem`, `srvSetElem`) & `Field` Refinements (`srvAutoField`) -/

@[reducible, inline]
def srvGetAt {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) : α :=
  xs[i]'h

@[simp] theorem srvGetAt_eq {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) :
    srvGetAt xs i h = xs[i]'h := rfl

@[inline]
def srvWithNewState {σ : Type} (sNew : σ) (P : σ → Prop) : Prop := P sNew

@[simp] theorem srvWithNewState_srvLetEq {σ γ : Type} (val : γ)
    (k : (x : γ) → x = val → σ) (P : σ → Prop) :
    srvWithNewState (srvLetEq val k) P = srvLetEq val (fun x hx => srvWithNewState (k x hx) P) := rfl

theorem srvWithNewState_apply {σ : Type} (s : σ) (P : σ → Prop) :
    srvWithNewState s P = P s := rfl

@[inline]
def srvEnsPost {ε α : Type} (P : α → Prop) : Except ε α → Prop
  | .ok r    => P r
  | .error _ => True

@[simp] theorem srvEnsPost_ok {ε α : Type} (P : α → Prop) (r : α) :
    srvEnsPost (ε := ε) P (.ok r) = P r := rfl

@[simp] theorem srvEnsPost_err {ε α : Type} (P : α → Prop) (e : ε) :
    srvEnsPost P (.error e) = True := rfl

@[simp] theorem srvEnsPost_srvLetEq {ε α γ : Type} (P : α → Prop) (val : γ)
    (k : (x : γ) → x = val → Except ε α) :
    srvEnsPost P (srvLetEq val k) = srvLetEq val (fun x hx => srvEnsPost P (k x hx)) := rfl

@[inline]
def srvEnsPostOpt {ε α : Type} (P : α → Prop) : Except ε (Option α) → Prop
  | .ok (some r) => P r
  | _            => True

@[simp] theorem srvEnsPostOpt_some {ε α : Type} (P : α → Prop) (r : α) :
    srvEnsPostOpt (ε := ε) P (.ok (some r)) = P r := rfl

@[simp] theorem srvEnsPostOpt_none {ε α : Type} (P : α → Prop) :
    srvEnsPostOpt (ε := ε) P (.ok none) = True := rfl

@[simp] theorem srvEnsPostOpt_err {ε α : Type} (P : α → Prop) (e : ε) :
    srvEnsPostOpt P (.error e) = True := rfl

@[simp] theorem srvEnsPostOpt_srvLetEq {ε α γ : Type} (P : α → Prop) (val : γ)
    (k : (x : γ) → x = val → Except ε (Option α)) :
    srvEnsPostOpt P (srvLetEq val k) = srvLetEq val (fun x hx => srvEnsPostOpt P (k x hx)) := rfl

theorem getElem_congr_arr {α : Type} {xs ys : Array α} {j : Nat}
    (heq : ys = xs) (hj : j < ys.size) :
    ys[j]'hj = xs[j]'(heq ▸ hj) := by
  cases heq; rfl

theorem srvGetAt_congr_arr {α : Type} {xs ys : Array α} {j : Nat}
    (heq : ys = xs) (hj : j < ys.size) :
    srvGetAt ys j hj = xs[j]'(heq ▸ hj) := by
  cases heq; rfl

syntax "qedSimpHypsEach" : tactic

syntax (name := srvAutoFieldStx) "srvAutoField(" term ")" : term
syntax (name := srvTypedAsStx)   "srvTypedAs(" term ", " term ")" : term
syntax (name := srvGetElemStx)   "srvGetElem(" term ", " term ")" : term
syntax (name := srvSetElemStx)   "srvSetElem(" term ", " term ", " term ")" : term

open Lean Meta Elab Term Tactic in
private def inspectFieldOrFin (sub : Expr) (addFact : Expr → MetaM Unit) : MetaM Unit := do
  if !sub.hasLooseBVars then
    if let some ty ← try some <$> (do let t ← inferType sub; whnf t) catch _ => pure none then
      if ty.isAppOfArity ``Qed.Field 2 then
        if let some okPrf ← try some <$> mkAppM ``Qed.Field.ok #[sub] catch _ => pure none then
          addFact okPrf
      else if ty.isAppOfArity ``Qed.Ensured 2 then
        if let some okPrf ← try some <$> mkAppM ``Qed.Ensured.ok #[sub] catch _ => pure none then
          addFact okPrf
      else if ty.isAppOfArity ``Fin 1 then
        if let some ltPrf ← try some <$> mkAppM ``Fin.isLt #[sub] catch _ => pure none then
          addFact ltPrf

open Lean Meta Elab Term Tactic in
/-- Collects all closed subterms of type `Qed.Field _` or `Fin _` from `e` and local hypotheses so
    `omega` automatically sees `.ok` field refinements and `.isLt` index bounds. -/
def collectProofFacts (extraExprs : Array Expr) : TermElabM (Array Expr) := do
  let factsRef ← IO.mkRef (#[] : Array Expr)
  let addFact (fact : Expr) : MetaM Unit := do
    let cur ← factsRef.get
    unless cur.any (· == fact) do factsRef.set (cur.push fact)
  let lctx ← getLCtx
  for decl in lctx do
    if !decl.isImplementationDetail then
      let uname := decl.userName.toString
      let isSrvEq := !decl.userName.hasMacroScopes && (uname.startsWith "_srvEq" || uname.startsWith "_hLet")
      if !decl.isLet && decl.userName.hasMacroScopes then
        if (← try isProp decl.type catch _ => pure false) then
          liftMetaM <| addFact decl.toExpr
      unless isSrvEq do
        liftMetaM <| inspectFieldOrFin decl.toExpr addFact
        if let some val := decl.value? then
          val.forEach fun sub => inspectFieldOrFin sub addFact
  for e in extraExprs do
    (← instantiateMVars e).forEach fun sub => inspectFieldOrFin sub addFact
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

open Lean Meta Elab Tactic in
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

open Lean Meta Elab Tactic in
private def unfoldSrvHelpersInGoal : TacticM Unit := do
  let mut g ← getMainGoal
  let lctx0 ← g.withContext getLCtx
  let mut hIdx : Nat := lctx0.size
  let mut propFVars : Array FVarId := #[]
  -- Pass 1: rename macro-scoped Prop hyps (`rename` preserves all FVarIds).
  for decl in lctx0 do
    if !decl.isImplementationDetail && !decl.isLet then
      let uname := decl.userName.toString
      let isSrvEq := !decl.userName.hasMacroScopes && (uname.startsWith "_srvEq" || uname.startsWith "_hLet")
      unless isSrvEq do
        let ty ← g.withContext (instantiateMVars decl.type)
        if (← g.withContext (try isProp ty catch _ => pure false)) then
          if decl.userName.hasMacroScopes then
            let (cand, nxt) ← nextFreshSrvName g "_srvSplitH" hIdx
            hIdx := nxt
            g ← g.rename decl.fvarId cand
          propFVars := propFVars.push decl.fvarId
  -- Pass 2: unfold helpers in reverse order so `changeLocalDecl` never invalidates earlier FVarIds.
  for revIdx in [0:propFVars.size] do
    let fv := propFVars[propFVars.size - 1 - revIdx]!
    let curLctx ← g.withContext getLCtx
    if let some decl := curLctx.find? fv then
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
          if let some g' ← try some <$> g.changeLocalDecl fv ty' catch _ => pure none then
            g := g'
  let tgt ← g.withContext (instantiateMVars (← g.getType))
  if hasSrvHelperConst tgt then
    let tgt' ← g.withContext (unfoldSrvHelpersExpr tgt)
    if tgt' != tgt then
      g ← g.change tgt'
  replaceMainGoal [g]

syntax "qedUnfoldSrvHelpers" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedUnfoldSrvHelpers) => unfoldSrvHelpersInGoal

macro "qedDsimpCodecs" : tactic => `(tactic|
  try dsimp (config := { zetaDelta := false }) only
    [Qed.Lang.QedVal.val, Qed.Server.SrvIdx.toNat,
     Qed.Server.SrvLiftOpt.liftOpt, Qed.Server.srvGetAt,
     Qed.Codec.valid, Qed.Codec.refine, Qed.Codec.jsonOnly,
     Qed.Codec.text, Qed.Codec.textarea, Qed.Codec.nat,
     Qed.Codec.int, Qed.Codec.checkbox, Qed.Codec.date] at ⊢)

theorem srvDiteFalse_eq_true {P : Prop} [Decidable P] (t : P → Bool) :
    ((if h : P then t h else false) = true) ↔ ∃ h : P, t h = true := by
  by_cases hP : P <;> simp [hP]

theorem srvDiteFalse_eq_false {P : Prop} [Decidable P] (t : P → Bool) :
    ((if h : P then t h else false) = false) ↔ ∀ h : P, t h = false := by
  by_cases hP : P <;> simp [hP]

macro "qedSimpArrayAndBool" : tactic => `(tactic|
  try simp (config := { zetaDelta := true }) only
    [id_eq, ne_eq, Qed.Server.srvGetAt_eq, Qed.QedVal.val_field,
     Qed.QedVal.val_ensured, Qed.Lang.QedVal.val_id,
     Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
     Array.size_set, Array.size_push, Array.size_modify,
     Array.getElem_set_self,
     Qed.Server.srvDiteFalse_eq_true, Qed.Server.srvDiteFalse_eq_false,
     Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
     beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at *)

open Lean Meta Elab Term in
private def exprHasLetFVar (lctx : LocalContext) (e : Expr) : Bool :=
  e.hasAnyFVar fun fvid => match lctx.find? fvid with
    | some d => d.isLet
    | none   => false

open Lean Meta Elab Term in
private def wrapAuxProof (goalProp prf : Expr) : TermElabM Expr := do
  let prf ← instantiateMVars prf
  let goalProp ← instantiateMVars goalProp
  if prf.hasMVar || goalProp.hasMVar then
    return prf
  let lctx ← getLCtx
  if exprHasLetFVar lctx goalProp || exprHasLetFVar lctx prf then
    return prf
  liftMetaM <| Meta.mkAuxTheorem goalProp prf (zetaDelta := false)

open Lean Meta Elab Term Tactic in
@[term_elab srvAutoFieldStx]
def elabSrvAutoField : TermElab := fun stx expectedType? => do
  let valStx : Term := ⟨stx[1]⟩
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
        let localFactsRef ← IO.mkRef (#[] : Array Expr)
        let addLocalFact (p : Expr) : MetaM Unit := do
          let cur ← localFactsRef.get
          unless cur.any (· == p) do localFactsRef.set (cur.push p)
        valExpr.forEach fun sub => inspectFieldOrFin sub addLocalFact
        let localFacts ← localFactsRef.get
        let localFactIds : Array Ident := (Array.range localFacts.size).map fun i => mkIdent (Name.mkSimple s!"_srvFact{i}")
        let fastPrfStx ← `(by
          try simp (config := { zetaDelta := false }) only
            [id_eq, Qed.Server.srvGetAt_eq, Qed.QedVal.val_field,
             Qed.QedVal.val_ensured, Qed.Lang.QedVal.val_id,
             Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
             Qed.Codec.valid, Qed.Codec.refine, Qed.Codec.jsonOnly,
             Qed.Codec.text, Qed.Codec.textarea, Qed.Codec.nat,
             Qed.Codec.int, Qed.Codec.checkbox, Qed.Codec.date] at $[$localFactIds:ident]* ⊢
          qedDsimpCodecs
          first | rfl | decide | assumption | omega)
        let savedMsgs ← Core.getMessageLog
        Core.resetMessageLog
        let fastPrf? : Option Expr ← try
            let prf ← withPosedFacts localFacts <| elabTermEnsuringType fastPrfStx (some goalProp)
            synthesizeSyntheticMVarsNoPostponing
            let prf ← instantiateMVars prf
            let newMsgs ← Core.getMessageLog
            if !newMsgs.hasErrors && !prf.hasMVar then
              Core.setMessageLog (savedMsgs ++ newMsgs)
              pure (some prf)
            else
              Core.setMessageLog savedMsgs
              pure none
          catch _ =>
            Core.setMessageLog savedMsgs
            pure none
        if let some fastPrf := fastPrf? then
          let fastPrf ← wrapAuxProof goalProp fastPrf
          return ← mkAppOptM ``Qed.Field.mk #[some innerTy, some predFn, some valExpr, some fastPrf]
        let facts ← collectProofFacts #[valExpr]
        let prfStx ← `(by
          try qedUnfoldSrvHelpers
          try qedSimpHypsEach
          try simp (config := { zetaDelta := false }) only
            [id_eq, ne_eq, Qed.Server.srvGetAt_eq, Qed.QedVal.val_field,
             Qed.QedVal.val_ensured, Qed.Lang.QedVal.val_id,
             Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
             Array.size_set, Array.size_push, Array.getElem_set_self,
             Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
             beq_iff_eq, bne_iff_ne, decide_eq_true_eq]
          qedDsimpCodecs
          first | assumption | omega | decide | simp_all | (simp_all <;> omega) | (simp_all <;> decide))
        let preMsgs := (← Core.getMessageLog).toList.length
        let prfExpr ← try
            withPosedFacts facts <| elabTermEnsuringType prfStx (some goalProp)
          catch _ =>
            throwErrorAt stx m!"cannot prove schema field refinement `{← ppExpr goalProp}`.\n\
              Guard this mutation with an `if ...` check or `requires ...` precondition so Lean can verify it cannot violate the schema."
        let hasErr := ((← Core.getMessageLog).toList.drop preMsgs).any (·.severity == .error)
        let prfExpr ← if hasErr then pure prfExpr else wrapAuxProof goalProp prfExpr
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
@[term_elab srvTypedAsStx]
def elabSrvTypedAs : TermElab := fun stx expectedType? => do
  let tplExpr ← elabTerm stx[1] none
  synthesizeSyntheticMVarsNoPostponing
  let tplTy ← instantiateMVars (← inferType tplExpr)
  let valExpr ← elabTermEnsuringType stx[3] (some tplTy)
  match expectedType? with
  | some expTy => ensureHasType expTy valExpr
  | none       => return valExpr

open Lean Meta Elab Tactic in
private def splitAndHyps : TacticM Bool := do
  let mut didSplit := false
  for _ in [0:32] do
    let g ← getMainGoal
    let lctx ← g.withContext getLCtx
    let mut splitOne := false
    for decl in lctx do
      if !splitOne && !decl.isImplementationDetail then
        let ty ← g.withContext (whnf decl.type)
        if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 || ty.isAppOfArity ``Qed.Lang.QedAndProp 2 then
          let subgoals ← g.cases decl.fvarId
          replaceMainGoal (subgoals.toList.map (·.mvarId))
          splitOne := true
          didSplit := true
    unless splitOne do break
  return didSplit

syntax "qedSrvSplitHyps" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvSplitHyps) => discard splitAndHyps

open Lean Meta Elab Term in
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

open Lean Meta Elab Term in
private def proveSizeEqChain (lctx : LocalContext) (startArr : Expr) : MetaM (Expr × Option Expr) := do
  let mut cur := startArr
  let mut eqOpt? : Option Expr := none -- proof of `cur.size = startArr.size`
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
              let curEqPrev ← mkEqTrans eqCur eqSet
              let prevEqCur ← mkEqSymm curEqPrev
              next? := some (prevArr, prevEqCur)
              break
            else if !rhsC.containsFVar fv && !(rhsC.getUsedConstants.any (· == ``srvLetEq)) then
              let arrTy ← whnf (← inferType cur)
              let elemTy := if arrTy.isAppOfArity ``Array 1 then arrTy.getAppArgs[0]! else mkConst ``Unit
              let sizeFn ← mkAppOptM ``Array.size #[some elemTy]
              let curEqRhs ← mkAppM ``congrArg #[sizeFn, decl.toExpr]
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

open Lean Meta Elab Term in
private def collectSizeBoundHypIds : TermElabM (Array Ident) := do
  let mut ids : Array Ident := #[]
  for decl in (← getLCtx) do
    if !decl.isImplementationDetail && !decl.isLet && !decl.userName.hasMacroScopes then
      let ty ← instantiateMVars decl.type
      if (← try isProp ty catch _ => pure false) then
        let cs := ty.getUsedConstants
        let hasRel := cs.any fun c =>
          c == ``Array.size || c == ``LT.lt || c == ``LE.le || c == ``GE.ge || c == ``GT.gt
        let hasHeavy := cs.any fun c =>
          c == ``srvGetAt || c == ``RequestCtx || c == ``Array.set
        if hasRel && !hasHeavy then
          ids := ids.push (mkIdent decl.userName)
  return ids

open Lean Meta Elab Term in
private def proveBoundsFor (ref : Syntax) (arrExpr idxNatExpr : Expr) : TermElabM Expr := do
  let sizeExpr ← mkAppM ``Array.size #[arrExpr]
  let goalProp ← mkAppM ``LT.lt #[idxNatExpr, sizeExpr]
  let lctx ← getLCtx
  let (baseArr, sizeEqOpt?) ← proveSizeEqChain lctx arrExpr
  let targetSizeExpr ← mkAppM ``Array.size #[baseArr]
  let baseGoalProp ← mkAppM ``LT.lt #[idxNatExpr, targetSizeExpr]
  let sizeHIds ← collectSizeBoundHypIds
  let hypSimpTac ← if sizeHIds.isEmpty then `(tactic| skip) else `(tactic|
    try simp only
      [id_eq, ne_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
       beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
       Qed.Lang.not_qedAndProp, Qed.Lang.not_qedOrProp,
       Qed.QedVal.val_field, Qed.Lang.QedVal.val_id,
       Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin] at $[$sizeHIds:ident]*)
  let fastStx ← `(by
    try simp (config := { zetaDelta := true }) only
      [id_eq, Qed.Server.srvGetAt_eq, Qed.QedVal.val_field,
       Qed.Lang.QedVal.val_id, Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
       Array.size_set, Array.size_push, Array.size_modify] at ⊢
    $hypSimpTac:tactic
    first | assumption | omega)
  let savedMsgs ← Core.getMessageLog
  Core.resetMessageLog
  let fastAttempt? : Option Expr ← try
      let basePrf ← elabTermEnsuringType fastStx (some baseGoalProp)
      synthesizeSyntheticMVarsNoPostponing
      let basePrf ← instantiateMVars basePrf
      let newMsgs ← Core.getMessageLog
      if !newMsgs.hasErrors && !basePrf.hasMVar then
        Core.setMessageLog (savedMsgs ++ newMsgs)
        match sizeEqOpt? with
        | none       => pure (some basePrf)
        | some eqPrf => pure (some (← mkAppM ``Nat.lt_of_lt_of_eq #[basePrf, eqPrf]))
      else
        Core.setMessageLog savedMsgs
        pure none
    catch _ =>
      Core.setMessageLog savedMsgs
      pure none
  if let some prfExpr := fastAttempt? then
    return ← wrapAuxProof goalProp prfExpr
  let facts ← collectProofFacts #[arrExpr, idxNatExpr]
  let prfStx ← `(by
    try qedUnfoldSrvHelpers
    try dsimp (config := { zetaDelta := true }) only [] at *
    qedSimpArrayAndBool
    try qedSrvSplitHyps
    first
      | assumption | omega
      | (simp_all (config := { zetaDelta := true }) <;> omega)
      | (repeat' split <;> (try simp (config := { zetaDelta := true }) only [Array.size_set, Array.size_push] at *; omega)))
  let preMsgs := (← Core.getMessageLog).toList.length
  let prfExpr ← try
      withPosedFacts facts <| elabTermEnsuringType prfStx (some goalProp)
    catch _ =>
      let prettyArr ← ppExpr arrExpr
      let prettyIdx ← ppExpr idxNatExpr
      throwErrorAt ref m!"cannot prove array index `{prettyIdx}` is in bounds for `{prettyArr}`.\n\
        Use `if {prettyIdx} < ({prettyArr}).size` or `if let i = ({prettyArr}).findIndex(...)` before indexing."
  let hasErr := ((← Core.getMessageLog).toList.drop preMsgs).any (·.severity == .error)
  if hasErr then return prfExpr else wrapAuxProof goalProp prfExpr

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
  let (arrExpr, idxNatExpr, elemTy) ← elabArrAndIdx ⟨stx[1]⟩ ⟨stx[3]⟩ "indexing"
  let ltPrf ← proveBoundsFor stx arrExpr idxNatExpr
  let elemExpr ← mkAppOptM ``srvGetAt #[some elemTy, some arrExpr, some idxNatExpr, some ltPrf]
  match expectedType? with
  | some expTy => ensureHasType expTy elemExpr
  | none       => return elemExpr

open Lean Meta Elab Term in
@[term_elab srvSetElemStx]
def elabSrvSetElem : TermElab := fun stx expectedType? => do
  let valStx : Term := ⟨stx[5]⟩
  let (arrExpr, idxNatExpr, elemTy) ← elabArrAndIdx ⟨stx[1]⟩ ⟨stx[3]⟩ "indexed assignment"
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

/-! ## Automated Server Invariant Prover (`qedSrvProveStep`) -/

syntax "qedSrvFinishAtom" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvFinishAtom) => do
      unfoldSrvHelpersInGoal
      evalTactic (← `(tactic| (
        try simp (config := { zetaDelta := false }) only
          [Qed.Server.srvGetAt_eq, Qed.QedVal.val_field,
           Qed.QedVal.val_ensured, Qed.Lang.QedVal.val_id,
           Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
           Qed.Server.SrvLiftOpt.liftOpt_opt, Qed.Server.SrvLiftOpt.liftOpt_val,
           Array.getElem_set_self]
        qedDsimpCodecs)))
      if (← getUnsolvedGoals).isEmpty then return
      let invFactIds ← withMainContext do
        let goalTy ← instantiateMVars (← getMainTarget)
        let lctx ← getLCtx
        let mut scanExprs : Array Expr := #[goalTy]
        let mut forallHyps : Array Expr := #[]
        for decl in lctx do
          if !decl.isImplementationDetail then
            let dty ← instantiateMVars decl.type
            let uname := decl.userName.toString
            let isSrvEq := !decl.userName.hasMacroScopes && (uname.startsWith "_srvEq" || uname.startsWith "_hLet")
            if !isSrvEq then
              scanExprs := scanExprs.push dty
            else if let some (_, _, rhs) := dty.eq? then
              if !(rhs.getUsedConstants.any fun c => c == ``Array.set || c == ``Array.push) then
                scanExprs := scanExprs.push dty
            if dty.isForall then forallHyps := forallHyps.push decl.toExpr
        let factsRef ← IO.mkRef (#[] : Array Expr)
        let nextScanRef ← IO.mkRef (#[] : Array Expr)
        let addFact (p : Expr) : MetaM Unit := do
          let cur ← factsRef.get
          unless cur.any (· == p) do
            factsRef.set (cur.push p)
            let pTy ← instantiateMVars (← inferType p)
            nextScanRef.modify (·.push pTy)
        for _ in [0:4] do
          if scanExprs.isEmpty then break
          nextScanRef.set #[]
          for e in scanExprs do
            e.forEach fun sub => do
              if !sub.hasLooseBVars then
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
        let facts ← factsRef.get
        let mut ids : Array Ident := #[]
        for idx in [0:facts.size] do
          let fPrf := facts[idx]!
          let g ← getMainGoal
          let fTy ← g.withContext (inferType fPrf)
          let fname := Name.mkSimple s!"_invFact{idx}"
          let (_, g') ← (← g.assert fname fTy fPrf).intro1P
          replaceMainGoal [g']
          ids := ids.push (mkIdent fname)
        return ids
      unless invFactIds.isEmpty do
        evalTactic (← `(tactic|
          try dsimp (config := { zetaDelta := false }) only
            [Qed.Codec.valid, Qed.Codec.refine, Qed.Codec.jsonOnly,
             Qed.Codec.text, Qed.Codec.textarea, Qed.Codec.nat,
             Qed.Codec.int, Qed.Codec.checkbox, Qed.Codec.date] at $[$invFactIds:ident]*))
      evalTactic (← `(tactic| (
        qedDsimpCodecs
        first
          | rfl | decide | omega | assumption | trivial | (intros; trivial)
          | exact Or.inr (by assumption) | exact Or.inl rfl
          | (simp (config := { zetaDelta := false }) only
               [Qed.Server.srvGetAt_eq, Qed.QedVal.val_field,
                Qed.QedVal.val_ensured, Qed.Lang.QedVal.val_id,
                Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
                Array.getElem_set_self, Array.size_set, Array.size_push] <;>
             first | rfl | decide | omega | assumption)
          | (simp (config := { zetaDelta := false }) [*] <;> done)
          | (simp (config := { zetaDelta := false }) [*] <;> omega)
          | (simp_all (config := { zetaDelta := false }) <;> omega)
          | (simp_all (config := { zetaDelta := false }) <;> decide)
          | (simp_all (config := { zetaDelta := false }) <;> done))))

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSimpHypsEach) => do
      let g ← getMainGoal
      let lctx ← g.withContext getLCtx
      let mut hIds : Array Ident := #[]
      for decl in lctx do
        if !decl.isImplementationDetail && !decl.isLet && !decl.userName.hasMacroScopes then
          let uname := decl.userName.toString
          unless uname.startsWith "_srvEq" || uname.startsWith "_hLet" do
            if (← g.withContext (try isProp decl.type catch _ => pure false)) then
              hIds := hIds.push (mkIdent decl.userName)
      if !hIds.isEmpty then
        let hypSimpNames := #[
          ``id_eq, ``ne_eq, ``Prod.mk.injEq, ``Option.some.injEq, ``Except.ok.injEq, ``Except.error.injEq, ``reduceCtorEq,
          ``Qed.Lang.not_qedAndProp, ``Qed.Lang.not_qedOrProp,
          ``Qed.Server.srvGetAt_eq, ``Qed.QedVal.val_field,
          ``Qed.QedVal.val_ensured, ``Qed.Lang.QedVal.val_id,
          ``Qed.Server.SrvIdx.toNat_nat, ``Qed.Server.SrvIdx.toNat_fin,
          ``Qed.Server.SrvLiftOpt.liftOpt_opt, ``Qed.Server.SrvLiftOpt.liftOpt_val,
          ``Qed.Codec.valid, ``Qed.Codec.refine, ``Qed.Codec.jsonOnly,
          ``Qed.Codec.text, ``Qed.Codec.textarea, ``Qed.Codec.nat,
          ``Qed.Codec.int, ``Qed.Codec.checkbox, ``Qed.Codec.date,
          ``Array.size_set, ``Array.size_push, ``Array.getElem_set_self,
          ``Qed.Server.srvDiteFalse_eq_true, ``Qed.Server.srvDiteFalse_eq_false,
          ``Bool.and_eq_true, ``Bool.or_eq_true, ``Bool.not_eq_true',
          ``beq_iff_eq, ``bne_iff_ne, ``decide_eq_true_eq]
        let hypLems ← hypSimpNames.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
        let batchOk ← try
            evalTactic (← `(tactic| simp (config := { zetaDelta := false }) only [$[$hypLems],*] at $[$hIds:ident]*))
            pure true
          catch _ => pure false
        unless batchOk do
          for hId in hIds do
            if (← getUnsolvedGoals).isEmpty then return
            evalTactic (← `(tactic| try simp (config := { zetaDelta := false }) only [$[$hypLems],*] at $hId:ident))
      if (← getUnsolvedGoals).isEmpty then return
      evalTactic (← `(tactic|
        try simp (config := { zetaDelta := false }) only
          [id_eq, ne_eq, Qed.Server.srvSeq_none, Qed.Server.srvSeq_some,
           Qed.Server.srvFinish_ok, Qed.Server.srvFinish_err, Qed.Server.srvFinish_none,
           Qed.Server.srvAtomicCommit_none, Qed.Server.srvAtomicCommit_ok, Qed.Server.srvAtomicCommit_err,
           Qed.Server.srvGetAt_eq, Qed.QedVal.val_field,
           Qed.QedVal.val_ensured, Qed.Lang.QedVal.val_id,
           Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
           Qed.Server.SrvLiftOpt.liftOpt_opt, Qed.Server.SrvLiftOpt.liftOpt_val,
           Array.forall_push, Array.sumBy_empty, Array.sumBy_push,
           Array.size_set, Array.size_push, Array.getElem_set_self,
           Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
           beq_iff_eq, bne_iff_ne, decide_eq_true_eq]))

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

syntax "qedElimSrvLetEq" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedElimSrvLetEq) => do
      let tryPick (gGoal : MVarId) (cands : Array Expr) (revCount : Nat) :
          TacticM (Option (Expr × Expr × MVarId × Nat)) := do
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
          if res?.isSome then
            return res?
          restoreState s
        return none
      let g ← getMainGoal
      let tgt ← g.withContext (instantiateMVars (← g.getType))
      let tgtCands ← collectReadySrvLetEqs tgt 1024
      let mut picked? ← tryPick g tgtCands 0
      if picked?.isNone then
        let lctx ← g.withContext getLCtx
        for decl in lctx do
          if !decl.isImplementationDetail && !decl.isLet then
            let dty ← g.withContext (instantiateMVars decl.type)
            let cands ← collectReadySrvLetEqs dty 1024
            unless cands.isEmpty do
              let s ← saveState
              let attempt? ← try
                  let (reverted, gRev) ← g.revert #[decl.fvarId]
                  tryPick gRev cands reverted.size
                catch _ => pure none
              if attempt?.isSome then
                picked? := attempt?
                break
              restoreState s
      let some (kFun, absBody, newGoal, revertedCount) := picked?
        | throwError "qedElimSrvLetEq: no eliminable srvLetEq found"
      let idx0 := (← newGoal.withContext getLCtx).size
      let (valName, idx1) ← nextFreshSrvName newGoal "_srvVal" idx0
      let (eqName, _) ← nextFreshSrvName newGoal "_srvEq" idx1
      let (valFVar, g1) ← newGoal.intro valName
      let (eqFVar, g2) ← g1.intro eqName
      let bodyApp := (mkApp2 kFun (mkFVar valFVar) (mkFVar eqFVar)).headBeta
      let reducedGoal := absBody.instantiate1 bodyApp
      let g3 ← try g2.change reducedGoal catch _ => pure g2
      let g4 ← if revertedCount > 0 then
          try (Prod.snd <$> g3.introN revertedCount) catch _ => pure g3
        else pure g3
      replaceMainGoal [g4]

open Lean Meta Elab Tactic in
private def rewriteTargetEqsLinear : TacticM Unit := do
  let g :: rest ← getGoals | return
  setGoals [g]
  let mut eqDecls : Array (FVarId × Bool × Ident) := #[]
  for decl in (← g.withContext getLCtx) do
    if !decl.isImplementationDetail && !decl.isLet && !decl.userName.hasMacroScopes then
      let uname := decl.userName.toString
      if uname.startsWith "_srvEq" || uname.startsWith "_hLet" then
        let dty ← g.withContext (instantiateMVars decl.type)
        if let some (eqTy, lhs, rhs) := dty.eq? then
          if let .fvar fv := lhs.consumeMData then
            if !rhs.containsFVar fv then
              let isArr ← g.withContext do
                return (← whnf eqTy).isAppOfArity ``Array 1
              eqDecls := eqDecls.push (fv, isArr, mkIdent decl.userName)
  for revIdx in [0:eqDecls.size] do
    if (← getGoals).isEmpty then break
    let (fv, isArr, hId) := eqDecls[eqDecls.size - 1 - revIdx]!
    let tgt ← withMainContext do instantiateMVars (← getMainTarget)
    if tgt.containsFVar fv then
      try
        if isArr then
          try evalTactic (← `(tactic|
            simp (config := { zetaDelta := false }) only
              [Qed.Server.getElem_congr_arr $hId:ident, Qed.Server.srvGetAt_congr_arr $hId:ident,
               Array.getElem_set_self, Array.getElem_set, ↓reduceIte])) catch _ => pure ()
          if !(← getGoals).isEmpty then
            let tgtAfter ← withMainContext do instantiateMVars (← getMainTarget)
            if tgtAfter.containsFVar fv then
              try evalTactic (← `(tactic| rw [$hId:ident])) catch _ => pure ()
        else
          evalTactic (← `(tactic| rw [$hId:ident]))
        if !(← getGoals).isEmpty then
          evalTactic (← `(tactic|
            try simp (config := { zetaDelta := false }) only
              [Qed.Server.srvGetAt_eq, Array.getElem_set_self, Array.size_set, Array.size_push,
               Array.sumBy_empty, Array.sumBy_push, Qed.QedVal.val_field,
               Qed.QedVal.val_ensured, Qed.Lang.QedVal.val_id,
               Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
               Qed.Server.SrvLiftOpt.liftOpt_opt, Qed.Server.SrvLiftOpt.liftOpt_val]))
      catch _ => pure ()
  let rem ← getGoals
  setGoals (rem ++ rest)

open Lean Meta Elab Tactic in
private def peelArrayForall : TacticM Unit := do
  let rec loop : Nat → TacticM Unit
    | 0 => pure ()
    | fuel + 1 => do
        let g :: rest ← getGoals | return
        setGoals [g]
        try evalTactic (← `(tactic| dsimp only at ⊢)) catch _ => pure ()
        let g :: _ ← getGoals | setGoals rest; return
        let tgt ← g.withContext (instantiateMVars (← g.getType))
        let .forallE _ _ (.forallE _ memTy _ _) _ := tgt.consumeMData
          | setGoals (g :: rest); return
        unless memTy.consumeMData.isAppOfArity ``Membership.mem 5 do
          setGoals (g :: rest); return
        let arrExpr := (memTy.consumeMData.getAppArgs[3]!).consumeMData
        if arrExpr.isAppOfArity ``Array.set 5 then
          let ok ← try
              evalTactic (← `(tactic| apply Array.forall_set))
              pure true
            catch _ => pure false
          if ok then
            let subgoals ← getGoals
            if subgoals.length == 2 then
              let [gPrev, gElem] := subgoals | setGoals (subgoals ++ rest); return
              setGoals [gElem]
              try evalTactic (← `(tactic| dsimp only at ⊢)) catch _ => pure ()
              unless (← getGoals).isEmpty do
                rewriteTargetEqsLinear
                unless (← getGoals).isEmpty do
                  try evalTactic (← `(tactic| qedSrvFinishAtom)) catch _ => pure ()
              let elemRem ← getGoals
              setGoals [gPrev]
              loop fuel
              let prevRem ← getGoals
              setGoals (prevRem ++ elemRem ++ rest)
              return
        if arrExpr.isAppOfArity ``Array.push 3 then
          evalTactic (← `(tactic| rw [Array.forall_push]; apply And.intro))
          let [gPrev, gElem] ← getGoals | setGoals ((← getGoals) ++ rest); return
          setGoals [gElem]
          try evalTactic (← `(tactic| dsimp only at ⊢)) catch _ => pure ()
          unless (← getGoals).isEmpty do
            rewriteTargetEqsLinear
            unless (← getGoals).isEmpty do
              try evalTactic (← `(tactic| qedSrvFinishAtom)) catch _ => pure ()
          let elemRem ← getGoals
          setGoals [gPrev]
          loop fuel
          let prevRem ← getGoals
          setGoals (prevRem ++ elemRem ++ rest)
          return
        if let .fvar fv := arrExpr then
          let lctx ← g.withContext getLCtx
          let mut eqId? : Option Ident := none
          for decl in lctx do
            if !decl.isImplementationDetail && !decl.isLet && !decl.userName.hasMacroScopes then
              let dty ← g.withContext (instantiateMVars decl.type)
              if let some (_, lhs, _) := dty.eq? then
                if lhs.consumeMData == .fvar fv then
                  eqId? := some (mkIdent decl.userName)
                  break
          if let some eqId := eqId? then
            let ok ← try
                evalTactic (← `(tactic| rw [$eqId:ident]))
                pure true
              catch _ => pure false
            if ok then
              loop fuel
              let rem ← getGoals
              setGoals (rem ++ rest)
              return
        try evalTactic (← `(tactic| assumption)) catch _ => pure ()
        let rem ← getGoals
        setGoals (rem ++ rest)
  loop 128

open Lean Meta Elab Tactic in
private def substMatchEqHyps : TacticM Unit := do
  for _ in [0:16] do
    let g :: rest ← getGoals | return
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
                substGoal? ← g.withContext do
                  try some <$> (Prod.snd <$> Meta.substCore g decl.fvarId (symm := true)) catch _ => pure none
            if substGoal?.isNone then
              if let .fvar fv := lhs.consumeMData then
                let fvMacro := (lctx.find? fv).map (·.userName.hasMacroScopes) |>.getD false
                if fv != decl.fvarId && !rhs.containsFVar fv && fvMacro then
                  substGoal? ← g.withContext do
                    try some <$> (Prod.snd <$> Meta.substCore g decl.fvarId (symm := false)) catch _ => pure none
    match substGoal? with
    | some g' => setGoals (g' :: rest)
    | none    => break

syntax "qedSrvCloseLeaf" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvCloseLeaf) => do
      evalTactic (← `(tactic| (
        try qedUnfoldSrvHelpers
        try qedSrvSplitHyps
        try qedSimpHypsEach)))
      substMatchEqHyps
      evalTactic (← `(tactic| (
        try simp (config := { zetaDelta := false }) only [Qed.Server.srvWithNewState_apply]
        try dsimp only at ⊢
        qedDsimpCodecs)))
      if (← getUnsolvedGoals).isEmpty then return
      if (← try splitAndHyps catch _ => pure false) then
        evalTactic (← `(tactic| try qedSimpHypsEach))
        substMatchEqHyps
      evalTactic (← `(tactic| try (repeat' (apply And.intro))))
      let curGoals ← getGoals
      let mut rem : List MVarId := []
      for cg in curGoals do
        setGoals [cg]
        try evalTactic (← `(tactic| first | rfl | exact Or.inl rfl | exact Or.inr (by assumption) | assumption)) catch _ => pure ()
        unless (← getGoals).isEmpty do
          peelArrayForall
          unless (← getGoals).isEmpty do
            rewriteTargetEqsLinear
            unless (← getGoals).isEmpty do
              try evalTactic (← `(tactic| all_goals (try qedSrvFinishAtom))) catch _ => pure ()
        rem := rem ++ (← getGoals)
      setGoals rem

syntax "qedSplitEqHyp" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSplitEqHyp) => do
      let g ← getMainGoal
      let lctx ← g.withContext getLCtx
      let mut idx := lctx.size
      let mut gCur := g
      let mut eqIds : Array Ident := #[]
      for decl in lctx do
        if !decl.isImplementationDetail && !decl.isLet then
          let ty ← gCur.withContext (instantiateMVars decl.type)
          if ty.isEq then
            let name ← if decl.userName.hasMacroScopes then
                let (cand, nxt) ← nextFreshSrvName gCur "_srvMatchEq" idx
                idx := nxt
                gCur ← gCur.rename decl.fvarId cand
                pure cand
              else pure decl.userName
            eqIds := eqIds.push (mkIdent name)
      replaceMainGoal [gCur]
      for hId in eqIds do
        if (← try evalTactic (← `(tactic| split at $hId:ident)); pure true catch _ => pure false) then
          return
      throwError "qedSplitEqHyp: nothing to split"

syntax "qedSrvProveStep " "[" ident,* "]" str str : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvProveStep [$[$unfoldIds:ident],*] $fnLabel:str $invLabel:str) => do
      let userLemmas ← unfoldIds.mapM fun id => `(Lean.Parser.Tactic.simpLemma| $id:ident)
      let fixedNames := #[
        ``Qed.Server.srvSeq_none, ``Qed.Server.srvSeq_some, ``Qed.Server.srvSeq_srvLetEq,
        ``Qed.Server.srvFinish_ok, ``Qed.Server.srvFinish_err, ``Qed.Server.srvFinish_none, ``Qed.Server.srvFinish_srvLetEq,
        ``Qed.Server.srvAtomicCommit_none, ``Qed.Server.srvAtomicCommit_ok, ``Qed.Server.srvAtomicCommit_err, ``Qed.Server.srvAtomicCommit_srvLetEq,
        ``Qed.Server.srvWithNewState_srvLetEq,
        ``Qed.Server.srvEnsPost_ok, ``Qed.Server.srvEnsPost_err, ``Qed.Server.srvEnsPost_srvLetEq,
        ``Qed.Server.srvEnsPostOpt_some, ``Qed.Server.srvEnsPostOpt_none, ``Qed.Server.srvEnsPostOpt_err, ``Qed.Server.srvEnsPostOpt_srvLetEq,
        ``Qed.Server.prod_fst_srvLetEq, ``Qed.Server.prod_snd_srvLetEq,
        ``Qed.QedVal.val_field, ``Qed.QedVal.val_ensured, ``Qed.Lang.QedVal.val_id,
        ``Qed.Server.SrvIdx.toNat_nat, ``Qed.Server.SrvIdx.toNat_fin,
        ``Qed.Server.SrvLiftOpt.liftOpt_opt, ``Qed.Server.SrvLiftOpt.liftOpt_val
      ]
      let fixedLemmas ← fixedNames.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
      let allStepLemmas := userLemmas ++ fixedLemmas
      let stepFloatLemmas := fixedLemmas
      let runTac ← `(tactic| (
        intros;
        try simp (config := { zetaDelta := false }) only [$[$allStepLemmas],*] at *;
        try (repeat' (
          first
            | (qedElimSrvLetEq; try simp (config := { zetaDelta := false }) only [$[$stepFloatLemmas],*] at ⊢)
            | (split <;>
                try simp (config := { zetaDelta := false }) only [$[$stepFloatLemmas],*] at ⊢)
            | (qedSplitEqHyp <;>
                try simp (config := { zetaDelta := false }) only [$[$stepFloatLemmas],*] at *)));
        all_goals (try qedSrvCloseLeaf)))
      evalTactic runTac
      let rem ← getUnsolvedGoals
      unless rem.isEmpty do
        let msg ← rem[0]!.withContext do ppExpr (← instantiateMVars (← rem[0]!.getType))
        let lbl := invLabel.getString
        if lbl.startsWith "ensures:" then
          let postStr := (lbl.drop 8).toString.trimAscii.toString
          throwError m!"server postcondition `ensures {postStr}` could not be proved for `{fnLabel.getString}`.\n\
            Remaining proof obligation:\n  {msg}\n\
            Ensure every successful return path establishes `{postStr}`."
        else
          throwError m!"server invariant `{lbl}` could not be proved for `{fnLabel.getString}`.\n\
            Remaining proof obligation:\n  {msg}\n\
            Guard state mutations with `if ...` or `requires ...` so this invariant holds across every branch."

macro "qedNormAsyncCont" : tactic => `(tactic| (
  try dsimp (config := { zetaDelta := false }) only
    [Qed.Server.srvSeqM, Qed.Server.SrvUnwrap.unwrap, Qed.Server.SrvErr.ofApi, Qed.Server.SrvUnwrapOpt.unwrapOpt] at *
  try simp (config := { zetaDelta := false }) only
    [Qed.Server.srvFinish_ok, Qed.Server.srvFinish_err, Qed.Server.srvFinish_none, Qed.Server.srvFinish_srvLetEq,
     Qed.Server.srvAtomicCommit_none, Qed.Server.srvAtomicCommit_ok, Qed.Server.srvAtomicCommit_err, Qed.Server.srvAtomicCommit_srvLetEq,
     Qed.Server.srvEnsPost_ok, Qed.Server.srvEnsPost_err, Qed.Server.srvEnsPost_srvLetEq,
     Qed.Server.srvEnsPostOpt_some, Qed.Server.srvEnsPostOpt_none, Qed.Server.srvEnsPostOpt_err, Qed.Server.srvEnsPostOpt_srvLetEq,
     Qed.Server.prod_fst_srvLetEq, Qed.Server.prod_snd_srvLetEq,
     Qed.Server.threadProg_pure_bind, Qed.Server.threadProg_pure_bind', Qed.Server.threadProg_bind_assoc] at *))

macro "qedAsyncInit " handlerId:ident : tactic => `(tactic| (
  intros;
  unfold $handlerId:ident;
  try dsimp (config := { zetaDelta := false }) only [Qed.Server.srvFinishM, Qed.Server.srvSeqM] at *;
  try simp (config := { zetaDelta := false }) only
    [Qed.Server.srvFinishM, Qed.Server.srvSeqM,
     Qed.Server.srvFinish_srvLetEq, Qed.Server.srvAtomicCommit_srvLetEq,
     Qed.Server.srvEnsPost_ok, Qed.Server.srvEnsPost_err, Qed.Server.srvEnsPost_srvLetEq,
     Qed.Server.srvEnsPostOpt_some, Qed.Server.srvEnsPostOpt_none, Qed.Server.srvEnsPostOpt_err, Qed.Server.srvEnsPostOpt_srvLetEq,
     Qed.Server.prod_fst_srvLetEq, Qed.Server.prod_snd_srvLetEq,
     Qed.Server.threadProg_pure_bind, Qed.Server.threadProg_pure_bind', Qed.Server.threadProg_bind_assoc] at *))

syntax "qedSrvProveAsync " ident "[" ident,* "]" str str : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvProveAsync $handlerId:ident [$[$invUnfoldIds:ident],*] $fnLabel:str $invLabel:str) => do
      evalTactic (← `(tactic| (
        qedAsyncInit $handlerId;
        try (repeat' (
          first
            | apply Qed.Server.ProgPreservesStepRel.pure
            | apply Qed.Server.safeIO_preservesStepRel
            | (apply Qed.Server.safeIO_bind_preservesStepRel; intro; qedNormAsyncCont)
            | (apply Qed.Server.runAtomic_bind_preservesStepRel; intro; qedNormAsyncCont)
            | (apply Qed.Server.runAtomicRead_bind_preservesStepRel; intro; qedNormAsyncCont)
            | apply Qed.Server.progPreservesStepRel_runAtomic
            | apply Qed.Server.progPreservesStepRel_runAtomicRead
            | (qedElimSrvLetEq; qedNormAsyncCont)
            | (split <;> qedNormAsyncCont)));
        all_goals (qedSrvProveStep [$[$invUnfoldIds],*] $fnLabel $invLabel))))

syntax "qedSrvProveAsyncEnsures " ident "[" ident,* "]" str str : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvProveAsyncEnsures $handlerId:ident [$[$invUnfoldIds:ident],*] $fnLabel:str $invLabel:str) => do
      evalTactic (← `(tactic| (
        qedAsyncInit $handlerId;
        try (repeat' (
          first
            | apply Qed.Server.ProgEnsures.pure
            | apply Qed.Server.progEnsures_pure
            | (apply Qed.Server.safeIO_bind_ensures; intro; qedNormAsyncCont)
            | (apply Qed.Server.runAtomic_bind_ensures; intro _ _; qedNormAsyncCont)
            | (apply Qed.Server.runAtomicRead_bind_ensures; intro _ _; qedNormAsyncCont)
            | apply Qed.Server.progEnsures_runAtomic
            | apply Qed.Server.progEnsures_runAtomicRead
            | (qedElimSrvLetEq; qedNormAsyncCont)
            | (change Qed.Server.ProgEnsures _ _ _; split <;> qedNormAsyncCont)));
        all_goals (qedSrvProveStep [$[$invUnfoldIds],*] $fnLabel $invLabel))))

syntax "qedProveRpcReq" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedProveRpcReq) => do
      let facts ← withMainContext do
        let tgt ← instantiateMVars (← getMainTarget)
        collectProofFacts #[tgt]
      for idx in [0:facts.size] do
        let fPrf := facts[idx]!
        let g ← getMainGoal
        let fTy ← g.withContext (inferType fPrf)
        let (_, g') ← (← g.assert (Name.mkSimple s!"_reqFact{idx}") fTy fPrf).intro1P
        replaceMainGoal [g']
      let env ← getEnv
      let fixedNames := #[
        ``Option.isSome_iff_ne_none, ``ne_eq, ``Bool.and_eq_true, ``Bool.or_eq_true,
        ``Bool.not_eq_true', ``beq_iff_eq, ``bne_iff_ne, ``decide_eq_true_eq,
        ``Qed.Lang.QedVal.val_id, ``Qed.QedVal.val_field, ``Qed.QedVal.val_ensured,
        ``Qed.Codec.valid,
        ``Qed.Codec.refine, ``Qed.Codec.jsonOnly, ``Qed.Codec.text, ``Qed.Codec.textarea,
        ``Qed.Codec.nat, ``Qed.Codec.int, ``Qed.Codec.checkbox, ``Qed.Codec.date]
      let allReqSimp ← (fixedNames ++ (#[`Qed.Cached.all, `Qed.Resource.all].filter env.contains)).mapM fun n =>
        `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
      evalTactic (← `(tactic| (
        try qedUnfoldSrvHelpers
        qedSimpArrayAndBool
        try simp (config := { zetaDelta := true, zetaHave := true }) only [$[$allReqSimp],*] at *
        qedDsimpCodecs
        try (repeat' (apply And.intro))
        all_goals (
          try qedSrvSplitHyps
          try first
            | trivial | rfl | assumption | decide | omega
            | (simp_all (config := { zetaDelta := true, zetaHave := true }) <;> omega)
            | (simp_all (config := { zetaDelta := true, zetaHave := true }) <;> decide)))))
      let rem ← getUnsolvedGoals
      unless rem.isEmpty do
        let msg ← rem[0]!.withContext do ppExpr (← instantiateMVars (← rem[0]!.getType))
        throwError m!"cannot prove server `requires` precondition:\n  {msg}\n\
          Guard this RPC call with `when ...` or `if ...` so the server precondition is satisfied."

end Qed.Server
