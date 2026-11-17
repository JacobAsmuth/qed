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

/-- Overloaded `fail(...)` builder supporting `fail("msg")` and `fail(code, "msg")`. -/
def mkFail1 (msg : String) : ApiError := ApiError.badRequest msg
def mkFail2 (code : Nat) (msg : String) : ApiError := { code, message := msg }

/-- Unwraps `Except ApiError α`, `Except String α`, or `Option α` for `?` propagation in `T!` functions. -/
class SrvUnwrapErr (W : Type) (Val : outParam Type) where
  unwrapErr : W → Except ApiError Val

@[reducible] instance {α : Type} : SrvUnwrapErr (Except ApiError α) α where
  unwrapErr := id

@[reducible] instance {α : Type} : SrvUnwrapErr (Except String α) α where
  unwrapErr
    | .ok a    => .ok a
    | .error e => .error (ApiError.badRequest e)

@[reducible] instance {α : Type} : SrvUnwrapErr (Option α) α where
  unwrapErr
    | some a => .ok a
    | none   => .error (ApiError.notFound "optional value was empty")

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
def srvFinish {σ α : Type} (s₀ : σ) (res : σ × Option (Except ApiError α)) : σ × Except ApiError α :=
  match res with
  | (s', some (.ok v))    => (s', .ok v)
  | (_,  some (.error e)) => (s₀, .error e)
  | (_,  none)            => (s₀, .error (ApiError.internal "unreachable missing return"))

@[simp] theorem srvFinish_ok {σ α : Type} (s₀ s' : σ) (v : α) :
    srvFinish s₀ (s', some (.ok v)) = (s', .ok v) := rfl

@[simp] theorem srvFinish_err {σ α : Type} (s₀ s' : σ) (e : ApiError) :
    srvFinish (α := α) s₀ (s', some (.error e)) = (s₀, .error e) := rfl

@[simp] theorem srvFinish_none {σ α : Type} (s₀ s' : σ) :
    srvFinish s₀ (s', (none : Option (Except ApiError α))) =
      (s₀, .error (ApiError.internal "unreachable missing return")) := rfl

/-- Transactional finalizer for `atomic` statement blocks: commits `s'` on `none`/`some (.ok v)`, rolls back to `s₀` on `some (.error e)`. -/
@[inline]
def srvAtomicCommit {σ α : Type} (s₀ : σ) (res : σ × Option (Except ApiError α)) :
    σ × Option (Except ApiError α) :=
  match res with
  | (s', none)                  => (s', none)
  | (s', some (Except.ok v))    => (s', some (Except.ok v))
  | (_,  some (Except.error e)) => (s₀, some (Except.error e))

@[simp] theorem srvAtomicCommit_none {σ α : Type} (s₀ s' : σ) :
    srvAtomicCommit (α := α) s₀ (s', none) = (s', none) := rfl

@[simp] theorem srvAtomicCommit_ok {σ α : Type} (s₀ s' : σ) (v : α) :
    srvAtomicCommit s₀ (s', some (Except.ok v)) = (s', some (Except.ok v)) := rfl

@[simp] theorem srvAtomicCommit_err {σ α : Type} (s₀ s' : σ) (e : ApiError) :
    srvAtomicCommit (α := α) s₀ (s', some (Except.error e)) = (s₀, some (Except.error e)) := rfl

/-- Effectful statement sequencing for `await`-containing handlers. -/
@[inline, specialize]
def srvSeqM {m : Type → Type} [Monad m] {ρ : Type}
    (first : m (Option ρ)) (next : Unit → m (Option ρ)) : m (Option ρ) := do
  match ← first with
  | some r => return some r
  | none   => next ()

@[inline, specialize]
def srvFinishM {m : Type → Type} [Monad m] {α : Type}
    (res : m (Option (Except ApiError α))) : m (Except ApiError α) := do
  match ← res with
  | some r => return r
  | none   => return .error (ApiError.internal "unreachable missing return")

/-! ## Custom Term Elaborators for Proven Bounds (`srvGetElem`, `srvSetElem`) & `Field` Refinements (`srvAutoField`) -/

@[reducible, inline]
def srvGetAt {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) : α :=
  xs[i]'h

@[simp] theorem srvGetAt_eq {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) :
    srvGetAt xs i h = xs[i]'h := rfl

syntax (name := srvAutoFieldStx) "srvAutoField(" term ")" : term
syntax (name := srvGetElemStx)   "srvGetElem(" term ", " term ")" : term
syntax (name := srvSetElemStx)   "srvSetElem(" term ", " term ", " term ")" : term

open Lean Meta Elab Term Tactic in
private def inspectFieldOrFin (sub : Expr) (addFact : Expr → MetaM Unit) : MetaM Unit := do
  if !sub.hasLooseBVars then
    if let some ty ← try some <$> (do let t ← inferType sub; whnf t) catch _ => pure none then
      if ty.isAppOfArity ``Qed.Field 2 then
        if let some okPrf ← try some <$> mkAppM ``Qed.Field.ok #[sub] catch _ => pure none then
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
      if !decl.isLet then
        if (← try isProp decl.type catch _ => pure false) then
          liftMetaM <| addFact decl.toExpr
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
    if fn.isConstOf ``srvGetAt || fn.isConstOf ``SrvVal.val ||
       fn.isConstOf ``SrvIdx.toNat || fn.isConstOf ``SrvLiftOpt.liftOpt then
      if let some u ← (do if let some x ← unfoldProjInst? sub then pure (some x) else unfoldDefinition? sub) then
        return .visit (if u.isAppOfArity ``id 2 then u.getAppArgs[1]! else u)
    return .continue)

open Lean Meta Elab Tactic in
private def unfoldSrvHelpersInGoal : TacticM Unit := do
  let mut g ← getMainGoal
  -- First, expose inaccessible `h✝` Prop hypotheses generated by `split` so `simp` & `simp [*]` can use them
  let lctx0 ← g.withContext getLCtx
  let tgt0 ← g.withContext (instantiateMVars (← g.getType))
  let mut hIdx : Nat := 0
  for decl in lctx0 do
    if !decl.isImplementationDetail && !decl.isLet then
      if (← g.withContext (try isProp decl.type catch _ => pure false)) then
        if decl.userName.hasMacroScopes then
          g ← g.rename decl.fvarId (Name.mkSimple s!"_srvSplitH{hIdx}")
          hIdx := hIdx + 1
        if tgt0.containsFVar decl.fvarId then
          let ty ← g.withContext (instantiateMVars decl.type)
          let ty' ← g.withContext (unfoldSrvHelpersExpr ty)
          let (_, gFree) ← (← g.assert (Name.mkSimple s!"_srvFreeH{hIdx}") ty' (mkFVar decl.fvarId)).intro1P
          g := gFree
          hIdx := hIdx + 1
  -- Next, unfold `srvGetAt`/`SrvVal.val`/`SrvIdx.toNat`/`SrvLiftOpt.liftOpt` across hypotheses (gracefully skipping dependent fvars)
  let mut skipped : Array FVarId := #[]
  for _ in [0:64] do
    let lctx ← g.withContext getLCtx
    let mut changedOne := false
    for decl in lctx do
      if !changedOne && !decl.isImplementationDetail && !decl.isLet && !skipped.contains decl.fvarId then
        let ty ← g.withContext (instantiateMVars decl.type)
        let ty' ← g.withContext (unfoldSrvHelpersExpr ty)
        if ty' != ty then
          match ← try some <$> g.changeLocalDecl decl.fvarId ty' catch _ => pure none with
          | some g' =>
              g := g'
              changedOne := true
          | none =>
              skipped := skipped.push decl.fvarId
    unless changedOne do break
  let tgt ← g.withContext (instantiateMVars (← g.getType))
  let tgt' ← g.withContext (unfoldSrvHelpersExpr tgt)
  if tgt' != tgt then
    g ← g.change tgt'
  replaceMainGoal [g]

syntax "qedUnfoldSrvHelpers" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedUnfoldSrvHelpers) => unfoldSrvHelpersInGoal

macro "qedDsimpCodecs" : tactic => `(tactic|
  try dsimp (config := { zetaDelta := true }) only
    [Qed.Server.SrvVal.val, Qed.Server.SrvIdx.toNat,
     Qed.Server.SrvLiftOpt.liftOpt, Qed.Server.srvGetAt,
     Qed.Codec.refine, Qed.Codec.jsonOnly,
     Qed.Codec.text, Qed.Codec.textarea, Qed.Codec.nat,
     Qed.Codec.int, Qed.Codec.checkbox, Qed.Codec.date] at *)

macro "qedSimpArrayAndBool" : tactic => `(tactic|
  try simp (config := { zetaDelta := true }) only
    [id_eq, ne_eq, Qed.Server.srvGetAt_eq, Qed.Server.SrvVal.val_field, Qed.Server.SrvVal.val_id,
     Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
     Array.size_set, Array.size_push, Array.size_modify,
     Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
     beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at *)

open Lean Meta Elab Term in
private def wrapAuxProof (goalProp prf : Expr) : TermElabM Expr := do
  let prf ← instantiateMVars prf
  let goalProp ← instantiateMVars goalProp
  if prf.hasMVar || goalProp.hasMVar then
    return prf
  liftMetaM <| Meta.mkAuxTheorem goalProp prf (zetaDelta := true)

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
        let facts ← collectProofFacts #[valExpr]
        let prfStx ← `(by
          try qedUnfoldSrvHelpers
          qedSimpArrayAndBool
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
                 catch _ => elabTermEnsuringType (← `(Qed.Server.SrvVal.val $valStx)) (some expTy)
  let e ← elabTerm valStx none
  synthesizeSyntheticMVars (postpone := .yes)
  let ty ← whnf (← instantiateMVars (← inferType e))
  let e ← if ty.isAppOfArity ``Qed.Field 2 then mkAppM ``Qed.Field.val #[e] else pure e
  match expectedType? with
  | some expTy => ensureHasType expTy e
  | none       => return e

open Lean Meta Elab Term in
private def proveBoundsFor (ref : Syntax) (arrExpr idxNatExpr : Expr) : TermElabM Expr := do
  let sizeExpr ← mkAppM ``Array.size #[arrExpr]
  let goalProp ← mkAppM ``LT.lt #[idxNatExpr, sizeExpr]
  let facts ← collectProofFacts #[arrExpr, idxNatExpr]
  let prfStx ← `(by
    try qedUnfoldSrvHelpers
    try dsimp (config := { zetaDelta := true }) only [] at *
    qedSimpArrayAndBool
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
        if ty.isAppOfArity ``And 2 then
          let subgoals ← g.cases decl.fvarId
          replaceMainGoal (subgoals.toList.map (·.mvarId))
          splitOne := true
          didSplit := true
    unless splitOne do break
  return didSplit

syntax "qedSrvFinishAtom" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvFinishAtom) => do
      unfoldSrvHelpersInGoal
      evalTactic (← `(tactic| (
        try simp_all (config := { zetaDelta := true }) only
          [Qed.Server.srvGetAt_eq, Qed.Server.SrvVal.val_field, Qed.Server.SrvVal.val_id,
           Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
           Qed.Server.SrvLiftOpt.liftOpt_opt, Qed.Server.SrvLiftOpt.liftOpt_val]
        qedDsimpCodecs)))
      if (← getUnsolvedGoals).isEmpty then return
      withMainContext do
        let goalTy ← instantiateMVars (← getMainTarget)
        let lctx ← getLCtx
        let mut scanExprs : Array Expr := #[goalTy]
        let mut forallHyps : Array Expr := #[]
        for decl in lctx do
          if !decl.isImplementationDetail then
            let dty ← instantiateMVars decl.type
            scanExprs := scanExprs.push dty
            if dty.isForall then forallHyps := forallHyps.push decl.toExpr
        let factsRef ← IO.mkRef (#[] : Array Expr)
        let addFact (p : Expr) : MetaM Unit := do
          let cur ← factsRef.get
          unless cur.any (· == p) do factsRef.set (cur.push p)
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
        let facts ← factsRef.get
        for idx in [0:facts.size] do
          let fPrf := facts[idx]!
          let g ← getMainGoal
          let fTy ← g.withContext (inferType fPrf)
          let (_, g') ← (← g.assert (Name.mkSimple s!"_invFact{idx}") fTy fPrf).intro1P
          replaceMainGoal [g']
      evalTactic (← `(tactic| (
        qedDsimpCodecs
        first
          | rfl | decide | omega | assumption | trivial | (intros; trivial)
          | (simp (config := { zetaDelta := true }) [*] <;> done)
          | (simp (config := { zetaDelta := true }) [*] <;> omega)
          | (simp_all (config := { zetaDelta := true }) <;> omega)
          | (simp_all (config := { zetaDelta := true }) <;> decide)
          | (simp_all (config := { zetaDelta := true }) <;> done))))

syntax "qedSrvSplitHyps" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvSplitHyps) => discard splitAndHyps

syntax "qedSimpHypsEach" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSimpHypsEach) => do
      let g ← getMainGoal
      let lctx ← g.withContext getLCtx
      let mut hIds : Array Ident := #[]
      for decl in lctx do
        if !decl.isImplementationDetail && !decl.isLet && !decl.userName.hasMacroScopes then
          if (← g.withContext (try isProp decl.type catch _ => pure false)) then
            hIds := hIds.push (mkIdent decl.userName)
      if !hIds.isEmpty then
        let batchOk ← try
            evalTactic (← `(tactic|
              simp (config := { zetaDelta := true }) only
                [id_eq, ne_eq, Prod.mk.injEq, Option.some.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq,
                 Qed.Server.srvGetAt_eq, Qed.Server.SrvVal.val_field, Qed.Server.SrvVal.val_id,
                 Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
                 Qed.Server.SrvLiftOpt.liftOpt_opt, Qed.Server.SrvLiftOpt.liftOpt_val,
                 Array.size_set, Array.size_push,
                 Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
                 beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at $[$hIds:ident]*))
            pure true
          catch _ => pure false
        unless batchOk do
          for hId in hIds do
            if (← getUnsolvedGoals).isEmpty then return
            evalTactic (← `(tactic|
              try simp (config := { zetaDelta := true }) only
                [id_eq, ne_eq, Prod.mk.injEq, Option.some.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq,
                 Qed.Server.srvGetAt_eq, Qed.Server.SrvVal.val_field, Qed.Server.SrvVal.val_id,
                 Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
                 Qed.Server.SrvLiftOpt.liftOpt_opt, Qed.Server.SrvLiftOpt.liftOpt_val,
                 Array.size_set, Array.size_push,
                 Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
                 beq_iff_eq, bne_iff_ne, decide_eq_true_eq] at $hId:ident))
      if (← getUnsolvedGoals).isEmpty then return
      evalTactic (← `(tactic|
        try simp (config := { zetaDelta := true }) only
          [id_eq, ne_eq, Qed.Server.srvSeq_none, Qed.Server.srvSeq_some,
           Qed.Server.srvFinish_ok, Qed.Server.srvFinish_err, Qed.Server.srvFinish_none,
           Qed.Server.srvAtomicCommit_none, Qed.Server.srvAtomicCommit_ok, Qed.Server.srvAtomicCommit_err,
           Qed.Server.srvGetAt_eq, Qed.Server.SrvVal.val_field, Qed.Server.SrvVal.val_id,
           Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
           Qed.Server.SrvLiftOpt.liftOpt_opt, Qed.Server.SrvLiftOpt.liftOpt_val,
           Array.forall_push, Array.sumBy_empty, Array.sumBy_push, Array.size_set, Array.size_push,
           Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
           beq_iff_eq, bne_iff_ne, decide_eq_true_eq]))

syntax "qedSrvCloseLeaf" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvCloseLeaf) => do
      evalTactic (← `(tactic| (
        try qedUnfoldSrvHelpers
        try qedSrvSplitHyps
        try qedSimpHypsEach
        try subst_vars
        qedDsimpCodecs)))
      if (← getUnsolvedGoals).isEmpty then return
      if (← try splitAndHyps catch _ => pure false) then
        evalTactic (← `(tactic| try qedSimpHypsEach))
      evalTactic (← `(tactic| (
        try (repeat' (apply And.intro))
        all_goals (
          try (apply Array.forall_set; first | assumption | (simp [*]; done) | (simp_all; done))
          try qedSrvFinishAtom))))

syntax "qedSrvProveStep " "[" ident,* "]" str str : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvProveStep [$[$unfoldIds:ident],*] $fnLabel:str $invLabel:str) => do
      let simpLemmas ← unfoldIds.mapM fun id => `(Lean.Parser.Tactic.simpLemma| $id:ident)
      let runTac ← `(tactic| (
        intros;
        try dsimp (config := { zetaDelta := true }) only [] at *;
        try simp (config := { zetaDelta := true }) only
          [$[$simpLemmas],*,
           Qed.Server.srvSeq_none, Qed.Server.srvSeq_some,
           Qed.Server.srvFinish_ok, Qed.Server.srvFinish_err, Qed.Server.srvFinish_none,
           Qed.Server.srvAtomicCommit_none, Qed.Server.srvAtomicCommit_ok, Qed.Server.srvAtomicCommit_err,
           Qed.Server.SrvVal.val_field, Qed.Server.SrvVal.val_id,
           Qed.Server.SrvIdx.toNat_nat, Qed.Server.SrvIdx.toNat_fin,
           Qed.Server.SrvLiftOpt.liftOpt_opt, Qed.Server.SrvLiftOpt.liftOpt_val] at *;
        try (repeat' (
          split <;> (
            try dsimp (config := { zetaDelta := true }) only [] at *
            try simp (config := { zetaDelta := true }) only
              [Qed.Server.srvSeq_none, Qed.Server.srvSeq_some,
               Qed.Server.srvFinish_ok, Qed.Server.srvFinish_err, Qed.Server.srvFinish_none,
               Qed.Server.srvAtomicCommit_none, Qed.Server.srvAtomicCommit_ok, Qed.Server.srvAtomicCommit_err] at *)));
        all_goals (try qedSrvCloseLeaf)))
      evalTactic runTac
      let rem ← getUnsolvedGoals
      unless rem.isEmpty do
        let msg ← rem[0]!.withContext do ppExpr (← instantiateMVars (← rem[0]!.getType))
        throwError m!"server invariant `{invLabel.getString}` could not be proved for `{fnLabel.getString}`.\n\
          Remaining proof obligation:\n  {msg}\n\
          Guard state mutations with `if ...` or `requires ...` so this invariant holds across every branch."

macro "qedNormAsyncCont" : tactic => `(tactic| (
  try dsimp (config := { zetaDelta := true }) only [Qed.Server.srvSeqM] at *
  try simp (config := { zetaDelta := true }) only
    [Qed.Server.threadProg_pure_bind, Qed.Server.threadProg_pure_bind', Qed.Server.threadProg_bind_assoc] at *))

syntax "qedSrvProveAsync " ident "[" ident,* "]" str str : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| qedSrvProveAsync $handlerId:ident [$[$invUnfoldIds:ident],*] $fnLabel:str $invLabel:str) => do
      evalTactic (← `(tactic| (
        intros;
        unfold $handlerId:ident;
        try dsimp (config := { zetaDelta := true }) only [Qed.Server.srvFinishM, Qed.Server.srvSeqM] at *;
        try simp (config := { zetaDelta := true }) only
          [Qed.Server.srvFinishM, Qed.Server.srvSeqM,
           Qed.Server.threadProg_pure_bind, Qed.Server.threadProg_pure_bind', Qed.Server.threadProg_bind_assoc] at *;
        try (repeat' (
          first
            | apply Qed.Server.ProgPreservesStepRel.pure
            | apply Qed.Server.safeIO_preservesStepRel
            | (apply Qed.Server.safeIO_bind_preservesStepRel; intro; qedNormAsyncCont)
            | (apply Qed.Server.runAtomic_bind_preservesStepRel; intro; qedNormAsyncCont)
            | (apply Qed.Server.runAtomicRead_bind_preservesStepRel; intro; qedNormAsyncCont)
            | apply Qed.Server.progPreservesStepRel_runAtomic
            | apply Qed.Server.progPreservesStepRel_runAtomicRead
            | (split <;> qedNormAsyncCont)));
        all_goals (qedSrvProveStep [$[$invUnfoldIds],*] $fnLabel $invLabel))))

end Qed.Server
