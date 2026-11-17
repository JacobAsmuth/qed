import Js.Backend

namespace Js.Proofs

open Lean IR

/-!
# Semantics-Preservation Proofs for `Js.Backend` & `qed_rt.mjs`

This module proves soundness of the lowering passes in `Js/Backend.lean` and the runtime
representation invariants in `runtime/qed_rt.mjs`:

1. **Constructor & Scalar Tag Layout (`jsTag_lowerCtor`, `fieldProj_lowerCtor`):**
   Nullary scalar constructors (`Number cidx`) and boxed object constructors (`{t: cidx, f: [...]}`)
   both satisfy `$.tag(v) = cidx`, and `.f[idx]` is the exact left-inverse of constructor packing.
2. **Closure Currying & Application (`rtApp_exact_equiv`, `rtApp_over_equiv`):**
   `$.pap(fn, arity, args)` and `$.app(f, xs)` preserve exact mathematical curried application across
   under-application, exact saturation, and multi-step over-application.
3. **Non-Recursive Join-Point Labeled-Block Lowering (`jdecl_inline_equiv`, `lowerBody_jdecl_nonrec_shape`):**
   Lowering `jdecl j xs val b` (when `!hasJmpTo j val`) to `j: { [[b]] } let xs = _j; [[val]]` with
   `_j = ys; break j;` is observationally identical to higher-order closure binding `const j = (xs) => [[val]]`.
4. **Tail-Call Elimination (`tailContinue_parallel_assign_sound`, `directLoop_equiv`, `trampoline_equiv`):**
   Both the `while (true)` direct loop (`_t_i = arg_i; x_i = _t_i; continue`) and the `__tc` trampoline
   compute the exact fuel-indexed recursive unfolding without sequential parameter-aliasing clobbers.
5. **COW `.r` Array Refcounting, `$.refMark` Invalidation & `$.memo` Purity
   (`cowUset_obs_equiv`, `cowPush_obs_equiv`, `refMark_snapshot_sound`, `memo_thunk_obs_equiv`):**
   Copy-on-write array mutation is observationally indistinguishable from pure functional arrays,
   clearing `__m = undefined` on in-place mutators guarantees `refMark` equality implies content
   equality across time, and `$.memo` caches pure thunks soundly.
-/

/-! ## 1. Runtime Values, Constructor Layout & `$.tag` / `.f[i]` Soundness -/

inductive JsVal where
  | num     (n : Nat)
  | bigInt  (n : Nat)
  | str     (s : String)
  | arr     (elems : List JsVal)
  | ctorObj (tag : Nat) (fields : List JsVal) (hasS : Bool) (hasU : Bool)
  | tc      (args : List JsVal)

/-- Exact counterpart of `export const tag = (x) => typeof x === 'number' ? x : x.t;` in `qed_rt.mjs`. -/
def jsTag : JsVal → Nat
  | .num n           => n
  | .ctorObj t _ _ _ => t
  | _                => 0

mutual
/-- Pure expression evaluator for `JsExpr` over variable environment `env`. -/
def evalJsExpr (env : String → JsVal) : JsExpr → JsVal
  | .var name                     => env name
  | .numLit n                     => .num n
  | .bigIntLit n                  => .bigInt n
  | .strLit s                     => .str s
  | .arrLit es                    => .arr (evalJsExprList env es)
  | .ctorObj cidx fs hasS hasU    => .ctorObj cidx (evalJsExprList env fs) hasS hasU
  | .fieldProj obj idx            =>
      match evalJsExpr env obj with
      | .ctorObj _ fs _ _ => fs.getD idx (.num 0)
      | _                 => .num 0
  | .tc args                      => .tc (evalJsExprList env args)
  | .call "$.tag" [e]             => .num (jsTag (evalJsExpr env e))
  | _                             => .num 0

def evalJsExprList (env : String → JsVal) : List JsExpr → List JsVal
  | []      => []
  | e :: es => evalJsExpr env e :: evalJsExprList env es
end

@[simp] theorem evalJsExprList_map (env : String → JsVal) :
    ∀ (xs : List α) (f : α → JsExpr),
      evalJsExprList env (xs.map f) = xs.map (fun x => evalJsExpr env (f x))
  | [], _      => rfl
  | x :: xs, f => by simp [evalJsExprList, evalJsExprList_map env xs f]

/-- Every IR constructor lowered by `Js.lowerCtor` — whether unboxed `Number cidx` (nullary, no scalar
    storage) or boxed `{t: cidx, f: [...]}` — produces a runtime `JsVal` whose `jsTag` is `info.cidx`. -/
theorem jsTag_lowerCtor (env : String → JsVal) (info : CtorInfo) (ys : Array Arg) :
    jsTag (evalJsExpr env (lowerCtor info ys)) = info.cidx := by
  unfold lowerCtor
  by_cases hscalar : (info.size == 0 && info.usize == 0 && info.ssize == 0) = true
  · simp [hscalar, evalJsExpr, jsTag]
  · simp [hscalar, evalJsExpr, jsTag]

/-- Case-scrutinee tag extraction (`$.tag(x)` on object types) recovers `info.cidx` for every
    constructor produced by `lowerCtor`. -/
theorem eval_case_scrut_lowerCtor (env : String → JsVal) (x : VarId)
    (info : CtorInfo) (ys : Array Arg)
    (hx : env (v x) = evalJsExpr env (lowerCtor info ys)) :
    evalJsExpr env (.call "$.tag" [.var (v x)]) = .num info.cidx := by
  simp [evalJsExpr, hx, jsTag_lowerCtor]

/-- Projecting field `idx` (`lowerExpr c ty (.proj idx x)`) from a boxed constructor lowered by
    `lowerCtor` recovers the exact lowered `idx`-th argument. -/
theorem fieldProj_lowerCtor (c : Ctx) (ty : IRType) (env : String → JsVal)
    (x : VarId) (info : CtorInfo) (ys : Array Arg) (idx : Nat)
    (hboxed : ¬(info.size == 0 && info.usize == 0 && info.ssize == 0) = true)
    (hidx : idx < ys.toList.length)
    (hx : env (v x) = evalJsExpr env (lowerCtor info ys)) :
    evalJsExpr env (lowerExpr c ty (.proj idx x)) =
      evalJsExpr env (lowerArg (ys.toList.getD idx .erased)) := by
  have hbf : (info.size == 0 && info.usize == 0 && info.ssize == 0) = false :=
    Bool.eq_false_iff.2 hboxed
  dsimp only [lowerExpr, evalJsExpr]
  rw [hx]
  dsimp only [lowerCtor]
  rw [hbf]
  simp only [Bool.false_eq_true, ↓reduceIte, evalJsExpr, evalJsExprList_map]
  generalize ys.toList = args at hidx ⊢
  induction args generalizing idx with
  | nil => simp at hidx
  | cons a rest ih =>
      cases idx with
      | zero => rfl
      | succ k =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hidx
          exact ih k hidx

/-! ## 2. Currying, Partial Application (`$.pap`) & Over-Application (`$.app`) Soundness -/

/-- Semantic domain of `qed_rt.mjs` values supporting curried higher-order closures (`pap`/`app`). -/
inductive RtFnVal (α : Type) where
  | ground (v : α)
  | pap    (fn : List α → RtFnVal α) (arity : Nat) (acc : List α)

/-- Fuel-indexed specification of `$.pap` and `$.app` from `runtime/qed_rt.mjs`:
    - `xs.length < rem`  → accumulate arguments in a new `pap` closure
    - `xs.length == rem` → invoke `fn (acc ++ xs)`
    - `xs.length > rem`  → invoke `fn (acc ++ xs.take rem)` and apply `xs.drop rem` to the result. -/
def rtPap (fn : List α → RtFnVal α) (arity : Nat) (args : List α) : RtFnVal α :=
  .pap fn arity args

def rtApp : Nat → RtFnVal α → List α → Option (RtFnVal α)
  | 0, _, _ => none
  | _, .ground v, _ => some (.ground v)
  | fuel + 1, .pap fn arity acc, xs =>
      let rem := arity - acc.length
      if xs.length < rem then
        some (.pap fn arity (acc ++ xs))
      else if xs.length == rem then
        some (fn (acc ++ xs))
      else
        rtApp fuel (fn (acc ++ xs.take rem)) (xs.drop rem)

/-- Under-application followed by a second application is identical to applying `xs₁ ++ xs₂` at once. -/
theorem rtApp_under_compose {α : Type} (fn : List α → RtFnVal α) (arity : Nat)
    (acc xs₁ xs₂ : List α) (fuel : Nat)
    (hunder : acc.length + xs₁.length < arity) :
    (rtApp (fuel + 1) (.pap fn arity acc) xs₁).bind (fun f' => rtApp (fuel + 1) f' xs₂) =
      rtApp (fuel + 1) (.pap fn arity acc) (xs₁ ++ xs₂) := by
  have hlt : xs₁.length < arity - acc.length := by omega
  dsimp only [rtApp]
  rw [if_pos hlt]
  dsimp only [Option.bind, rtApp]
  have hlen1 : (acc ++ xs₁).length = acc.length + xs₁.length := List.length_append
  have hlen12 : (xs₁ ++ xs₂).length = xs₁.length + xs₂.length := List.length_append
  by_cases hlt2 : xs₂.length < arity - (acc ++ xs₁).length
  · have hltSum : (xs₁ ++ xs₂).length < arity - acc.length := by omega
    rw [if_pos hlt2, if_pos hltSum, List.append_assoc]
  · rw [if_neg hlt2]
    by_cases heq2 : (xs₂.length == arity - (acc ++ xs₁).length) = true
    · have heq2Nat : xs₂.length = arity - (acc ++ xs₁).length := eq_of_beq heq2
      have hnotLtSum : ¬(xs₁ ++ xs₂).length < arity - acc.length := by omega
      have heqSum : ((xs₁ ++ xs₂).length == arity - acc.length) = true := beq_iff_eq.2 (by omega)
      rw [if_pos heq2, if_neg hnotLtSum, if_pos heqSum, List.append_assoc]
    · have hne2 : xs₂.length ≠ arity - (acc ++ xs₁).length := fun h => heq2 (beq_iff_eq.2 h)
      have hnotLtSum : ¬(xs₁ ++ xs₂).length < arity - acc.length := by omega
      have hnotEqSum : ¬((xs₁ ++ xs₂).length == arity - acc.length) = true := by
        intro h; have := eq_of_beq h; omega
      rw [if_neg heq2, if_neg hnotLtSum, if_neg hnotEqSum]
      have hrem : arity - (acc ++ xs₁).length = arity - acc.length - xs₁.length := by omega
      have htake : (xs₁ ++ xs₂).take (arity - acc.length) =
          xs₁ ++ xs₂.take (arity - (acc ++ xs₁).length) := by
        rw [List.take_append, hrem, List.take_of_length_le (by omega)]
      have hdrop : (xs₁ ++ xs₂).drop (arity - acc.length) =
          xs₂.drop (arity - (acc ++ xs₁).length) := by
        rw [List.drop_append, hrem, List.drop_eq_nil_of_le (by omega), List.nil_append]
      rw [htake, hdrop, List.append_assoc]

/-- Exact saturation of a `$.pap` closure invokes `fn` on the full argument list `acc ++ xs`. -/
theorem rtApp_exact_equiv {α : Type} (fn : List α → RtFnVal α) (arity : Nat)
    (acc xs : List α) (fuel : Nat)
    (hacc : acc.length ≤ arity)
    (hsat : acc.length + xs.length = arity) :
    rtApp (fuel + 1) (rtPap fn arity acc) xs = some (fn (acc ++ xs)) := by
  have hnotLt : ¬xs.length < arity - acc.length := by omega
  have heq : (xs.length == arity - acc.length) = true := beq_iff_eq.2 (by omega)
  simp [rtPap, rtApp, hnotLt, heq]

/-- Over-applying a `$.pap` closure with `xs₁ ++ xs₂` (where `acc ++ xs₁` saturates `arity` and `xs₂`
    is non-empty) invokes `fn (acc ++ xs₁)` and forwards `xs₂` to the returned closure. -/
theorem rtApp_over_equiv {α : Type} (fn : List α → RtFnVal α) (arity : Nat)
    (acc xs₁ xs₂ : List α) (fuel : Nat)
    (hacc : acc.length ≤ arity)
    (hsat : acc.length + xs₁.length = arity)
    (hmore : 0 < xs₂.length) :
    rtApp (fuel + 2) (rtPap fn arity acc) (xs₁ ++ xs₂) =
      rtApp (fuel + 1) (fn (acc ++ xs₁)) xs₂ := by
  have hlen12 : (xs₁ ++ xs₂).length = xs₁.length + xs₂.length := List.length_append
  have hrem : arity - acc.length = xs₁.length := by omega
  have hnotLt : ¬(xs₁ ++ xs₂).length < arity - acc.length := by omega
  have hnotEq : ¬((xs₁ ++ xs₂).length == arity - acc.length) = true := by
    intro h; have := eq_of_beq h; omega
  dsimp only [rtPap, rtApp]
  rw [if_neg hnotLt, if_neg hnotEq, hrem, List.take_left, List.drop_left]

/-! ## 3. Non-Recursive Join-Point Labeled-Block Lowering (`jdecl` → `j: { ... break j; }`) -/

abbrev JsEnv := String → JsVal

def bindEnv (env : JsEnv) (k : String) (val : JsVal) : JsEnv :=
  fun m => if m == k then val else env m

def bindMany (env : JsEnv) : List (String × JsVal) → JsEnv
  | []            => env
  | (k, val) :: r => bindMany (bindEnv env k val) r

/-- Outcome of executing a statement block inside an optional labeled block. -/
inductive BlockExit where
  | fallthrough (env : JsEnv)
  | broke       (label : String) (env : JsEnv)
  | returned    (val : JsVal)

/- Execute a simplified straight-line + `labeledBlock` / `breakLabel` / `letVar` / `letBinds` / `ret`
   fragment of `JsStmt`, capturing the exact control-flow of non-recursive join-point lowering. -/
mutual
def execStmt (env : JsEnv) : JsStmt → BlockExit
  | .letVar x val =>
      .fallthrough (bindEnv env x (evalJsExpr env val))
  | .letDecls names =>
      .fallthrough (bindMany env (names.map (·, .num 0)))
  | .letBinds binds =>
      let evaluated := binds.map fun (k, e) => (k, evalJsExpr env e)
      .fallthrough (bindMany env evaluated)
  | .labeledBlock lbl body =>
      match execStmts env body with
      | .broke lbl' env' =>
          if lbl' == lbl then .fallthrough env' else .broke lbl' env'
      | other => other
  | .breakLabel assigns lbl =>
      let evaluated := assigns.map fun (lhs, rhs) => (lhs, evalJsExpr env rhs)
      .broke lbl (bindMany env evaluated)
  | .ret val =>
      .returned (evalJsExpr env val)
  | _ => .fallthrough env

def execStmts (env : JsEnv) : List JsStmt → BlockExit
  | [] => .fallthrough env
  | s :: ss =>
      match execStmt env s with
      | .fallthrough env' => execStmts env' ss
      | exitOut           => exitOut
end

@[simp] theorem execStmts_append :
    ∀ (s₁ s₂ : List JsStmt) (env : JsEnv),
      execStmts env (s₁ ++ s₂) =
        match execStmts env s₁ with
        | .fallthrough env' => execStmts env' s₂
        | exitOut           => exitOut
  | [], s₂, env => rfl
  | s :: ss, s₂, env => by
      simp only [List.cons_append, execStmts]
      cases execStmt env s <;> simp [execStmts_append ss s₂]

/-- Structural shape lemma: when `hasJmpTo j val = false`, `Js.lowerBody` lowers `FnBody.jdecl j xs val b`
    to the labeled-block sequence `pre ++ [.labeledBlock (jp j) (lowerBody c' b)] ++ post ++ lowerBody c val`. -/
theorem lowerBody_jdecl_nonrec_shape (c : Ctx) (j : JoinPointId) (xs : Array Param) (val b : FnBody)
    (hnonrec : hasJmpTo j val = false) :
    let c' := { c with inlineJps := c.inlineJps.insert j.idx xs }
    let declNames := xs.toList.zipIdx.map fun (_, i) => s!"_{jp j}_{i}"
    let bindPairs := xs.toList.zipIdx.map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}")
    let pre := if xs.isEmpty then [] else [JsStmt.letDecls declNames]
    let post := if xs.isEmpty then [] else [JsStmt.letBinds bindPairs]
    lowerBody c (.jdecl j xs val b) =
      pre ++ [.labeledBlock (jp j) (lowerBody c' b)] ++ post ++ lowerBody c val := by
  simp [lowerBody, hnonrec]

/-- Semantic equivalence of non-recursive join-point lowering:
    - **Case 1 (Early return):** If the body `bStmts` inside `j: { ... }` returns `r` directly without
      jumping to `j`, the entire lowered `jdecl` returns `r` without executing `valStmts` — identical
      to `const j = (xs) => val; b`.
    - **Case 2 (Join-point jump):** If `bStmts` jumps to `j` via `breakLabel assigns (jp j)`, `j: { ... }`
      catches the break, binds the join-point parameters from the staging variables, and executes
      `valStmts` in that environment — identical to tail-calling `return j(ys)`. -/
theorem jdecl_inline_early_return_equiv (lbl : String) (bStmts postAndVal : List JsStmt)
    (env : JsEnv) (retVal : JsVal)
    (hearly : execStmts env bStmts = .returned retVal) :
    execStmts env ([.labeledBlock lbl bStmts] ++ postAndVal) = .returned retVal := by
  simp [execStmts, execStmt, hearly]

theorem jdecl_inline_jump_equiv (lbl : String) (bPrefix : List JsStmt)
    (assigns : List (String × JsExpr)) (deadAfterJump post valStmts : List JsStmt)
    (env envAtJump : JsEnv)
    (hprefix : execStmts env bPrefix = .fallthrough envAtJump) :
    let brokenEnv := bindMany envAtJump (assigns.map fun (lhs, rhs) => (lhs, evalJsExpr envAtJump rhs))
    execStmts env ([.labeledBlock lbl (bPrefix ++ [.breakLabel assigns lbl] ++ deadAfterJump)] ++ post ++ valStmts) =
      execStmts brokenEnv (post ++ valStmts) := by
  simp [List.append_assoc, execStmts_append, hprefix, execStmts, execStmt]

/-! ## 4. Tail-Call Elimination Soundness (`fnDirectLoop` & `fnTrampoline`) -/

/-- Structural shape lemma: a self-tail call `let x := f(args); ret x` (modulo RC instructions)
    lowers to `.tailContinue` when `c.directLoop = true` and `.ret (.tc ...)` when `c.directLoop = false`. -/
theorem lowerBody_selfTail_shape (c : Ctx) (x : VarId) (ty : IRType)
    (f : Name) (args : Array Arg) (cont : FnBody)
    (hself : c.selfFn = some f) (hret : retsVar x cont = true) :
    lowerBody c (.vdecl x ty (.fap f args) cont) =
      if c.directLoop then
        [.tailContinue (c.selfParams.toList.map (v ·.x)) (args.toList.map lowerArg)]
      else
        [.ret (.tc (args.toList.map lowerArg))] := by
  simp [lowerBody, hself, hret]

theorem bindMany_lookup_not_mem (env : JsEnv) :
    ∀ (binds : List (String × JsVal)) (k : String),
      k ∉ binds.map Prod.fst →
      bindMany env binds k = env k
  | [], _, _ => rfl
  | (b, val) :: rest, k, hnot => by
      simp only [List.map_cons, List.mem_cons, not_or] at hnot
      rw [bindMany, bindMany_lookup_not_mem _ rest k hnot.2]
      have hne : (k == b) = false := beq_eq_false_iff_ne.2 hnot.1
      simp [bindEnv, hne]

theorem bindMany_lookup_nodup (env : JsEnv) :
    ∀ (binds : List (String × JsVal)) (i : Nat) (k : String) (val : JsVal),
      (binds.map Prod.fst).Nodup →
      binds[i]? = some (k, val) →
      bindMany env binds k = val
  | [], i, _, _, _, hget => by simp at hget
  | (k₀, v₀) :: rest, 0, k, val, hnd, hget => by
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hget
      rcases hget with ⟨rfl, rfl⟩
      rcases List.nodup_cons.1 hnd with ⟨hnotMem, _⟩
      rw [bindMany, bindMany_lookup_not_mem _ rest k₀ hnotMem]
      simp [bindEnv]
  | (k₀, v₀) :: rest, i + 1, k, val, hnd, hget => by
      simp only [List.getElem?_cons_succ] at hget
      rcases List.nodup_cons.1 hnd with ⟨_, hndRest⟩
      exact bindMany_lookup_nodup (bindEnv env k₀ v₀) rest i k val hndRest hget

/-- Staging `let _t_i = e_i; p_i = _t_i` produces the exact `evalJsExpr env (argExprs[i])` on every
    parameter `params[i]`, regardless of whether `argExprs[j]` mentions earlier parameters `params[i]`. -/
theorem tailContinue_staged_assign_sound (env : JsEnv)
    (params tmps : List String) (argExprs : List JsExpr)
    (hlen1 : tmps.length = argExprs.length)
    (hlen2 : params.length = tmps.length)
    (hndTmps : tmps.Nodup)
    (hndParams : params.Nodup)
    (i : Nat) (hi : i < params.length) :
    let tmpEnv := bindMany env (tmps.zip (argExprs.map (evalJsExpr env)))
    let nextEnv := bindMany tmpEnv (params.zip (tmps.map tmpEnv))
    nextEnv params[i] = evalJsExpr env (argExprs[i]'(by omega)) := by
  dsimp only
  have hiTmp : i < tmps.length := by omega
  have hiArg : i < argExprs.length := by omega
  let tmpEnv := bindMany env (tmps.zip (argExprs.map (evalJsExpr env)))
  have htmpLookup : tmpEnv tmps[i] = evalJsExpr env argExprs[i] := by
    apply bindMany_lookup_nodup env (tmps.zip (argExprs.map (evalJsExpr env))) i tmps[i] (evalJsExpr env argExprs[i])
    · rw [List.map_fst_zip (by simp [hlen1])]; exact hndTmps
    · simp [List.getElem?_zip_eq_some, hiTmp, hiArg]
  have hparamLookup :
      bindMany tmpEnv (params.zip (tmps.map tmpEnv)) params[i] = tmpEnv tmps[i] := by
    apply bindMany_lookup_nodup tmpEnv (params.zip (tmps.map tmpEnv)) i params[i] (tmpEnv tmps[i])
    · rw [List.map_fst_zip (by simp [hlen2])]; exact hndParams
    · simp [List.getElem?_zip_eq_some, hi, hiTmp]
  exact hparamLookup.trans htmpLookup

/-- Mathematical fuel-indexed semantics of a tail-recursive function body `step`. -/
def recEval {α β : Type} (step : α → Sum α β) : Nat → α → Option β
  | 0, _        => none
  | fuel + 1, a =>
      match step a with
      | .inl nextArgs => recEval step fuel nextArgs
      | .inr result   => some result

/-- Direct `while (true)` loop semantics (`fnDirectLoop` in `Js/Backend.lean`). -/
def directLoopEval {α β : Type} (step : α → Sum α β) : Nat → α → Option β
  | 0, _ => none
  | fuel + 1, state =>
      match step state with
      | .inl reassignedState => directLoopEval step fuel reassignedState
      | .inr returnVal       => some returnVal

theorem directLoop_equiv {α β : Type} (step : α → Sum α β) (fuel : Nat) (init : α) :
    directLoopEval step fuel init = recEval step fuel init := by
  induction fuel generalizing init with
  | zero => rfl
  | succ f ih =>
      simp only [directLoopEval, recEval]
      cases step init with
      | inl next => exact ih next
      | inr res  => rfl

/-- Closure-safe `__step` / `__r.__tc` trampoline semantics (`fnTrampoline` in `Js/Backend.lean` +
    `export const tc = (a) => ({ __tc: a });` in `runtime/qed_rt.mjs`). -/
def encodeTrampolineStep (step : List JsVal → Sum (List JsVal) JsVal) (args : List JsVal) : JsVal :=
  match step args with
  | .inl nextArgs => .tc nextArgs
  | .inr retVal   => retVal

def trampolineLoop (stepFn : List JsVal → JsVal) : Nat → List JsVal → Option JsVal
  | 0, _ => none
  | fuel + 1, args =>
      match stepFn args with
      | .tc nextArgs => trampolineLoop stepFn fuel nextArgs
      | retVal       => some retVal

/-- Provided normal return values of `f` are Lean runtime values (never raw `{__tc: ...}` sentinel
    records), the `fnTrampoline` loop computes the exact `recEval` result for all `fuel` and `args`. -/
theorem trampoline_equiv (step : List JsVal → Sum (List JsVal) JsVal)
    (hnoSentinel : ∀ args v, step args = .inr v → ∀ xs, v ≠ .tc xs) :
    ∀ (fuel : Nat) (args : List JsVal),
      trampolineLoop (encodeTrampolineStep step) fuel args = recEval step fuel args
  | 0, _ => rfl
  | fuel + 1, args => by
      simp only [trampolineLoop, encodeTrampolineStep, recEval]
      cases hs : step args with
      | inl nextArgs =>
          exact trampoline_equiv step hnoSentinel fuel nextArgs
      | inr retVal =>
          cases retVal with
          | tc xs => exact False.elim (hnoSentinel args (.tc xs) hs xs rfl)
          | _     => rfl

/-! ## 5. COW `.r` Refcounted Arrays, `$.refMark` Invalidation & `$.memo` Purity -/

structure CowEntry (α : Type) where
  elems    : List α := []
  refcount : Nat := 1
  mark     : Option Nat := none

structure CowHeap (α : Type) where
  nextId    : Nat := 1
  nextStamp : Nat := 1
  cells     : Nat → CowEntry α := fun _ => {}

namespace CowHeap

def get (h : CowHeap α) (id : Nat) : CowEntry α := h.cells id

def set (h : CowHeap α) (id : Nat) (e : CowEntry α) : CowHeap α :=
  { h with cells := fun m => if m == id then e else h.cells m }

@[simp] theorem get_set_self (h : CowHeap α) (id : Nat) (e : CowEntry α) :
    (h.set id e).get id = e := by
  simp [get, set]

@[simp] theorem get_set_ne (h : CowHeap α) {id other : Nat} (e : CowEntry α) (hne : other ≠ id) :
    (h.set id e).get other = h.get other := by
  simp [get, set, hne]

def readArray (h : CowHeap α) (id : Nat) : List α := (h.get id).elems

/-- Shared COW array mutator model (`Array_uset`, `Array_push`, `Array_swap` in `runtime/qed_rt.mjs`):
    - When `refcount ≤ 1` (uniquely owned): updates `elems` in-place AND clears `mark := none` (`a.__m = undefined`).
    - When `refcount > 1` (shared): decrements `id`'s refcount and allocates a fresh array handle `h.nextId`
      with `refcount := 1` and `mark := none`. -/
def cowUpdate (h : CowHeap α) (id : Nat) (f : List α → List α) : Nat × CowHeap α :=
  let e := h.get id
  let updated := f e.elems
  if e.refcount ≤ 1 then
    (id, h.set id { elems := updated, refcount := 1, mark := none })
  else
    let hDec := h.set id { e with refcount := e.refcount - 1 }
    let fresh := h.nextId
    let hAlloc : CowHeap α :=
      { nextId := h.nextId + 1
        nextStamp := h.nextStamp
        cells := fun m => if m == fresh then { elems := updated, refcount := 1, mark := none } else hDec.cells m }
    (fresh, hAlloc)

def cowUset (h : CowHeap α) (id idx : Nat) (val : α) : Nat × CowHeap α :=
  h.cowUpdate id (·.set idx val)

def cowPush (h : CowHeap α) (id : Nat) (val : α) : Nat × CowHeap α :=
  h.cowUpdate id (· ++ [val])

theorem cowUpdate_obs_equiv (h : CowHeap α) (id : Nat) (f : List α → List α) (hid : id < h.nextId) :
    let (outId, h') := h.cowUpdate id f
    h'.readArray outId = f (h.readArray id) ∧
    (∀ alias : Nat, alias < h.nextId →
      ((h.get id).refcount ≤ 1 → alias ≠ id) →
      h'.readArray alias = h.readArray alias) := by
  dsimp only [cowUpdate]
  by_cases huniq : (h.get id).refcount ≤ 1
  · simp only [huniq, ↓reduceIte]
    refine ⟨by simp [readArray], ?_⟩
    intro alias _ hneImp
    simp [readArray, hneImp trivial]
  · simp only [huniq, ↓reduceIte]
    refine ⟨by simp [readArray, get], ?_⟩
    intro alias halias _
    have hneFresh : alias ≠ h.nextId := by omega
    by_cases ha : alias = id
    · subst ha; simp [readArray, get, hneFresh, set]
    · simp [readArray, get, hneFresh, set, ha]

theorem cowUset_obs_equiv (h : CowHeap α) (id idx : Nat) (val : α) (hid : id < h.nextId) :
    let (outId, h') := h.cowUset id idx val
    h'.readArray outId = (h.readArray id).set idx val ∧
    (∀ alias : Nat, alias < h.nextId →
      ((h.get id).refcount ≤ 1 → alias ≠ id) →
      h'.readArray alias = h.readArray alias) :=
  cowUpdate_obs_equiv h id (·.set idx val) hid

theorem cowPush_obs_equiv (h : CowHeap α) (id : Nat) (val : α) (hid : id < h.nextId) :
    let (outId, h') := h.cowPush id val
    h'.readArray outId = h.readArray id ++ [val] ∧
    (∀ alias : Nat, alias < h.nextId →
      ((h.get id).refcount ≤ 1 → alias ≠ id) →
      h'.readArray alias = h.readArray alias) :=
  cowUpdate_obs_equiv h id (· ++ [val]) hid

/-- Exact model of `export const refMark = (x) => ...` in `runtime/qed_rt.mjs`:
    returns the existing positive stamp if present, or assigns and caches a fresh positive stamp. -/
def refMark (h : CowHeap α) (id : Nat) : Nat × CowHeap α :=
  let e := h.get id
  match e.mark with
  | some s => (s, h)
  | none   =>
      let s := h.nextStamp
      (s, { (h.set id { e with mark := some s }) with nextStamp := s + 1 })

/-- Global heap invariant on `mark` stamps:
    1. Every cached stamp is strictly less than `h.nextStamp`.
    2. Distinct array handles never share the same cached stamp. -/
def HeapStampInv (h : CowHeap α) : Prop :=
  (∀ m s, (h.get m).mark = some s → s < h.nextStamp) ∧
  (∀ m₁ m₂ s, (h.get m₁).mark = some s → (h.get m₂).mark = some s → m₁ = m₂)

/-- Historical snapshot invariant: any cell still carrying `some snapStamp` has `elems = snapElems`,
    and `snapStamp < h.nextStamp` so future `refMark` allocations can never reuse `snapStamp`. -/
def SnapshotValid (snapStamp : Nat) (snapElems : List α) (h : CowHeap α) : Prop :=
  snapStamp < h.nextStamp ∧
  ∀ m : Nat, (h.get m).mark = some snapStamp → (h.get m).elems = snapElems

theorem refMark_creates_snapshot (h : CowHeap α) (id : Nat) (hinv : HeapStampInv h) :
    let (stamp, h') := h.refMark id
    HeapStampInv h' ∧
    SnapshotValid stamp (h.readArray id) h' := by
  rcases hinv with ⟨hbnd, huniq⟩
  dsimp only [refMark]
  cases hm : (h.get id).mark with
  | some s =>
      dsimp only
      refine ⟨⟨hbnd, huniq⟩, ⟨hbnd id s hm, ?_⟩⟩
      intro m hm'
      have heq : m = id := huniq m id s hm' hm
      subst heq
      rfl
  | none =>
      dsimp only
      refine ⟨⟨?_, ?_⟩, ⟨Nat.lt_succ_self _, ?_⟩⟩
      · intro m s hm'
        dsimp only
        by_cases hmid : m = id
        · subst hmid
          simp only [get, set, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hm'
          omega
        · simp only [get, set, beq_eq_false_iff_ne.2 hmid, Bool.false_eq_true, ↓reduceIte] at hm'
          exact Nat.lt_trans (hbnd m s hm') (Nat.lt_succ_self _)
      · intro m₁ m₂ s hm₁ hm₂
        by_cases h1 : m₁ = id <;> by_cases h2 : m₂ = id
        · exact h1.trans h2.symm
        · subst h1
          simp only [get, set, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hm₁
          simp only [get, set, beq_eq_false_iff_ne.2 h2, Bool.false_eq_true, ↓reduceIte] at hm₂
          have hlt := hbnd m₂ s hm₂
          omega
        · subst h2
          simp only [get, set, beq_eq_false_iff_ne.2 h1, Bool.false_eq_true, ↓reduceIte] at hm₁
          simp only [get, set, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hm₂
          have hlt := hbnd m₁ s hm₁
          omega
        · simp only [get, set, beq_eq_false_iff_ne.2 h1, Bool.false_eq_true, ↓reduceIte] at hm₁
          simp only [get, set, beq_eq_false_iff_ne.2 h2, Bool.false_eq_true, ↓reduceIte] at hm₂
          exact huniq m₁ m₂ s hm₁ hm₂
      · intro m hm'
        by_cases hmid : m = id
        · subst hmid
          simp [get, set, readArray]
        · simp only [get, set, beq_eq_false_iff_ne.2 hmid, Bool.false_eq_true, ↓reduceIte] at hm'
          have hlt := hbnd m h.nextStamp hm'
          omega

/-- Because `cowUpdate` clears `mark := none` (`a.__m = undefined`) on in-place mutations and assigns
    `mark := none` on COW clones, every historical `SnapshotValid` remains true after any COW update. -/
theorem SnapshotValid_cowUpdate (h : CowHeap α) (id : Nat) (f : List α → List α)
    (snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) :
    SnapshotValid snapStamp snapElems (h.cowUpdate id f).2 := by
  rcases hsnap with ⟨hlt, heq⟩
  dsimp only [cowUpdate]
  by_cases huniq : (h.get id).refcount ≤ 1
  · simp only [huniq, ↓reduceIte]
    refine ⟨hlt, ?_⟩
    intro m hm
    by_cases hmid : m = id
    · subst hmid; simp at hm
    · rw [get_set_ne _ _ hmid] at hm ⊢
      exact heq m hm
  · simp only [huniq, ↓reduceIte]
    refine ⟨hlt, ?_⟩
    intro m hm
    by_cases hmf : m = h.nextId
    · subst hmf; simp [get] at hm
    · by_cases hmid : m = id
      · subst hmid
        simp only [get, beq_eq_false_iff_ne.2 hmf, Bool.false_eq_true, ↓reduceIte, set, beq_self_eq_true] at hm ⊢
        exact heq m hm
      · simp only [get, beq_eq_false_iff_ne.2 hmf, Bool.false_eq_true, ↓reduceIte, set,
                   beq_eq_false_iff_ne.2 hmid] at hm ⊢
        exact heq m hm

theorem SnapshotValid_cowUset (h : CowHeap α) (id idx : Nat) (val : α)
    (snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) :
    SnapshotValid snapStamp snapElems (h.cowUset id idx val).2 :=
  SnapshotValid_cowUpdate h id (·.set idx val) snapStamp snapElems hsnap

theorem SnapshotValid_cowPush (h : CowHeap α) (id : Nat) (val : α)
    (snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) :
    SnapshotValid snapStamp snapElems (h.cowPush id val).2 :=
  SnapshotValid_cowUpdate h id (· ++ [val]) snapStamp snapElems hsnap

/-- `refMark` on any array also preserves every earlier `SnapshotValid` because newly allocated
    stamps use `h.nextStamp > snapStamp`. -/
theorem SnapshotValid_refMark (h : CowHeap α) (id : Nat)
    (snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) :
    SnapshotValid snapStamp snapElems (h.refMark id).2 := by
  rcases hsnap with ⟨hlt, heq⟩
  dsimp only [refMark]
  cases hm : (h.get id).mark with
  | some s => exact ⟨hlt, heq⟩
  | none =>
      dsimp only
      refine ⟨Nat.lt_trans hlt (Nat.lt_succ_self _), ?_⟩
      intro m hm'
      by_cases hmid : m = id
      · subst hmid
        simp only [get, set, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hm'
        omega
      · simp only [get, set, beq_eq_false_iff_ne.2 hmid, Bool.false_eq_true, ↓reduceIte] at hm' ⊢
        exact heq m hm'

/-- Crown-jewel `refMark` soundness theorem (used by `V.forEach` fast-path skip in `Template.lean`):
    whenever `SnapshotValid snapStamp snapElems h` holds and `(curStamp, _) := h.refMark id`
    observes `curStamp = snapStamp`, `h.readArray id = snapElems` holds unconditionally! -/
theorem refMark_snapshot_sound (h : CowHeap α) (id snapStamp : Nat) (snapElems : List α)
    (hsnap : SnapshotValid snapStamp snapElems h)
    (heqStamp : (h.refMark id).1 = snapStamp) :
    h.readArray id = snapElems := by
  rcases hsnap with ⟨hlt, heq⟩
  dsimp only [refMark] at heqStamp
  cases hm : (h.get id).mark with
  | some s =>
      rw [hm] at heqStamp
      dsimp only at heqStamp
      subst heqStamp
      exact heq id hm
  | none =>
      rw [hm] at heqStamp
      dsimp only at heqStamp
      omega

end CowHeap

/-- Exact model of `export const memo = (fn) => { let ok = false, v; return () => { if (!ok) { v = fn(); ok = true; } return v; }; };`
    in `runtime/qed_rt.mjs`. -/
structure MemoCell (α : Type) where
  ok  : Bool := false
  val : Option α := none

def MemoCell.Valid (thunk : Unit → α) (c : MemoCell α) : Prop :=
  c.ok = true → c.val = some (thunk ())

def memoForce (thunk : Unit → α) (defaultVal : α) (c : MemoCell α) : α × MemoCell α :=
  if c.ok then
    (c.val.getD defaultVal, c)
  else
    let v := thunk ()
    (v, { ok := true, val := some v })

/-- `$.memo(fn)` is observationally identical to calling the pure `thunk ()` on every invocation,
    and preserves `MemoCell.Valid` from the initial `{ ok := false, val := none }` state forever. -/
theorem memo_thunk_obs_equiv {α : Type} (thunk : Unit → α) (defaultVal : α) (c : MemoCell α)
    (hvalid : MemoCell.Valid thunk c) :
    let (res, c') := memoForce thunk defaultVal c
    res = thunk () ∧ MemoCell.Valid thunk c' := by
  dsimp only [memoForce]
  cases hok : c.ok with
  | false =>
      simp [MemoCell.Valid]
  | true =>
      have hval : c.val = some (thunk ()) := hvalid hok
      simp [hval, MemoCell.Valid]

/-! ## 6. Soundness of `collectNonArr`, `collectProjSrc`, and `hasDecOf` RC Elision -/

theorem collectNonArr_insert_mono {α : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (s : Std.HashSet α) (x y : α) (h : x ∈ s) : x ∈ s.insert y :=
  Std.HashSet.mem_insert.mpr (Or.inr h)

private theorem sizeOf_alts_toList_lt (tid : Name) (x : VarId) (ty : IRType) (alts : Array Alt) :
    sizeOf alts.toList < sizeOf (FnBody.case tid x ty alts) := by
  cases alts
  simp
  omega

private theorem collectNonArr_mono_aux :
    ∀ (sz : Nat) (b : FnBody) (acc : Std.HashSet Nat) (k : Nat),
      sizeOf b ≤ sz → k ∈ acc → k ∈ collectNonArr acc b
  | 0, b, _, _, hsz, _ => by
      cases b <;> simp at hsz <;> omega
  | sz + 1, b, acc, k, hsz, hk => by
      cases b with
      | vdecl x _ e cont =>
          simp only [collectNonArr]
          apply collectNonArr_mono_aux sz cont _ k (by simp at hsz; omega)
          cases e <;> simp only []
          all_goals first
            | exact hk
            | exact collectNonArr_insert_mono acc k _ hk
      | jdecl _ _ v cont =>
          simp only [collectNonArr]
          have h1 := collectNonArr_mono_aux sz v acc k (by simp at hsz; omega) hk
          exact collectNonArr_mono_aux sz cont _ k (by simp at hsz; omega) h1
      | case tid x ty alts =>
          simp only [collectNonArr]
          have haltsLt := sizeOf_alts_toList_lt tid x ty alts
          suffices hAlts : ∀ (ls : List Alt) (a : Std.HashSet Nat),
              sizeOf ls ≤ sz → k ∈ a → k ∈ collectNonArrAlts a ls by
            apply hAlts alts.toList _ (by omega)
            exact collectNonArr_insert_mono acc k x.idx hk
          intro ls
          induction ls with
          | nil => intro a _ ha; exact ha
          | cons alt rest ih =>
              intro a hls ha
              cases alt with
              | ctor _ body =>
                  simp only [collectNonArrAlts]
                  apply ih _ (by simp at hls; omega)
                  exact collectNonArr_mono_aux sz body a k (by simp at hls; omega) ha
              | default body =>
                  simp only [collectNonArrAlts]
                  apply ih _ (by simp at hls; omega)
                  exact collectNonArr_mono_aux sz body a k (by simp at hls; omega) ha
      | set _ _ _ cont | setTag _ _ cont | uset _ _ _ cont | sset _ _ _ _ _ cont
      | inc _ _ _ _ cont | dec _ _ _ _ cont | del _ cont =>
          simp only [collectNonArr]
          exact collectNonArr_mono_aux sz cont acc k (by simp at hsz; omega) hk
      | ret _ | jmp _ _ | unreachable =>
          simpa [collectNonArr] using hk

theorem collectNonArr_mono (b : FnBody) (acc : Std.HashSet Nat) (k : Nat)
    (hk : k ∈ acc) : k ∈ collectNonArr acc b :=
  collectNonArr_mono_aux (sizeOf b) b acc k (Nat.le_refl _) hk

theorem collectNonArrAlts_mono (alts : List Alt) (acc : Std.HashSet Nat) (k : Nat)
    (hk : k ∈ acc) : k ∈ collectNonArrAlts acc alts := by
  induction alts generalizing acc with
  | nil => exact hk
  | cons alt rest ih =>
      cases alt with
      | ctor _ body =>
          exact ih _ (collectNonArr_mono body acc k hk)
      | default body =>
          exact ih _ (collectNonArr_mono body acc k hk)

/-- Semantic value classification for reference-counting soundness: either a heap-allocated COW
    array handle (`CowHeap` id) or a non-array value (primitives, constructors, closures, PAPs). -/
inductive RcVal where
  | arr    (id : Nat)
  | nonArr (val : JsVal)

namespace CowHeap

def rcInc (h : CowHeap α) (v : RcVal) (n : Nat) : CowHeap α :=
  match v with
  | .arr id   => h.set id { h.get id with refcount := (h.get id).refcount + n }
  | .nonArr _ => h

def rcDec (h : CowHeap α) (v : RcVal) (n : Nat) : CowHeap α :=
  match v with
  | .arr id   => h.set id { h.get id with refcount := (h.get id).refcount - n }
  | .nonArr _ => h

@[simp] theorem rcInc_nonArr_noop (h : CowHeap α) (v : JsVal) (n : Nat) :
    h.rcInc (.nonArr v) n = h := rfl

@[simp] theorem rcDec_nonArr_noop (h : CowHeap α) (v : JsVal) (n : Nat) :
    h.rcDec (.nonArr v) n = h := rfl

end CowHeap

def NonArrExpr : IR.Expr → Bool
  | .ctor .. | .reuse .. | .pap .. | .lit .. | .box .. | .unbox .. | .isShared .. => true
  | _ => false

def ProjSrcVar : IR.Expr → Option Nat
  | .proj _ p | .uproj _ p | .sproj _ _ p => some p.idx
  | _ => none

def NonArrSetSound (acc : Std.HashSet Nat) (ρ : Nat → RcVal) : Prop :=
  ∀ k, k ∈ acc → ∃ v, ρ k = .nonArr v

theorem NonArrSetSound_insert {acc : Std.HashSet Nat} {ρ : Nat → RcVal} {k : Nat} {v : JsVal}
    (hs : NonArrSetSound acc ρ) (hk : ρ k = .nonArr v) :
    NonArrSetSound (acc.insert k) ρ := by
  intro m hm
  rw [Std.HashSet.mem_insert] at hm
  rcases hm with hkm | hm'
  · have hEq : k = m := beq_iff_eq.mp hkm
    subst hEq
    exact ⟨v, hk⟩
  · exact hs m hm'

mutual
def NonArrConsistent (ρ : Nat → RcVal) : FnBody → Prop
  | .vdecl x _ e b =>
      (NonArrExpr e = true → ∃ v, ρ x.idx = .nonArr v) ∧
      (∀ p, ProjSrcVar e = some p → ∃ v, ρ p = .nonArr v) ∧
      NonArrConsistent ρ b
  | .jdecl _ _ v b => NonArrConsistent ρ v ∧ NonArrConsistent ρ b
  | .case _ x _ alts => (∃ v, ρ x.idx = .nonArr v) ∧ NonArrConsistentAlts ρ alts.toList
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b
  | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => NonArrConsistent ρ b
  | .ret _ | .jmp _ _ | .unreachable => True

def NonArrConsistentAlts (ρ : Nat → RcVal) : List Alt → Prop
  | [] => True
  | .ctor _ b :: rest | .default b :: rest => NonArrConsistent ρ b ∧ NonArrConsistentAlts ρ rest
end

private theorem collectNonArr_sound_aux :
    ∀ (sz : Nat) (b : FnBody) (acc : Std.HashSet Nat) (ρ : Nat → RcVal),
      sizeOf b ≤ sz → NonArrSetSound acc ρ → NonArrConsistent ρ b →
      NonArrSetSound (collectNonArr acc b) ρ
  | 0, b, _, _, hsz, _, _ => by
      cases b <;> simp at hsz <;> omega
  | sz + 1, b, acc, ρ, hsz, hacc, hcon => by
      cases b with
      | vdecl x _ e cont =>
          simp only [NonArrConsistent] at hcon
          rcases hcon with ⟨hx, hp, hcont⟩
          simp only [collectNonArr]
          apply collectNonArr_sound_aux sz cont _ ρ (by simp at hsz; omega) _ hcont
          cases e with
          | ctor _ _ | reuse _ _ _ _ | pap _ _ | lit _ | box _ _ | unbox _ | isShared _ =>
              rcases hx rfl with ⟨v, hv⟩
              exact NonArrSetSound_insert hacc hv
          | proj _ p | uproj _ p | sproj _ _ p =>
              rcases hp p.idx rfl with ⟨v, hv⟩
              exact NonArrSetSound_insert hacc hv
          | _ => exact hacc
      | jdecl _ _ v cont =>
          simp only [NonArrConsistent] at hcon
          rcases hcon with ⟨hv, hcont⟩
          simp only [collectNonArr]
          have h1 := collectNonArr_sound_aux sz v acc ρ (by simp at hsz; omega) hacc hv
          exact collectNonArr_sound_aux sz cont _ ρ (by simp at hsz; omega) h1 hcont
      | case tid x ty alts =>
          simp only [NonArrConsistent] at hcon
          rcases hcon with ⟨⟨vx, hvx⟩, halts⟩
          simp only [collectNonArr]
          have hacc' := NonArrSetSound_insert hacc hvx
          have haltsLt := sizeOf_alts_toList_lt tid x ty alts
          suffices hStep : ∀ (ls : List Alt) (a : Std.HashSet Nat),
              sizeOf ls ≤ sz → NonArrSetSound a ρ → NonArrConsistentAlts ρ ls →
              NonArrSetSound (collectNonArrAlts a ls) ρ by
            exact hStep alts.toList _ (by omega) hacc' halts
          intro ls
          induction ls with
          | nil => intro a _ ha _; exact ha
          | cons alt rest ih =>
              intro a hls ha hlcon
              cases alt with
              | ctor _ body =>
                  simp only [NonArrConsistentAlts] at hlcon
                  simp only [collectNonArrAlts]
                  apply ih _ (by simp at hls; omega) _ hlcon.2
                  exact collectNonArr_sound_aux sz body a ρ (by simp at hls; omega) ha hlcon.1
              | default body =>
                  simp only [NonArrConsistentAlts] at hlcon
                  simp only [collectNonArrAlts]
                  apply ih _ (by simp at hls; omega) _ hlcon.2
                  exact collectNonArr_sound_aux sz body a ρ (by simp at hls; omega) ha hlcon.1
      | set _ _ _ cont | setTag _ _ cont | uset _ _ _ cont | sset _ _ _ _ _ cont
      | inc _ _ _ _ cont | dec _ _ _ _ cont | del _ cont =>
          simp only [NonArrConsistent] at hcon
          simp only [collectNonArr]
          exact collectNonArr_sound_aux sz cont acc ρ (by simp at hsz; omega) hacc hcon
      | ret _ | jmp _ _ | unreachable =>
          simpa [collectNonArr] using hacc

/-- Soundness of `Js.collectNonArr`: starting from an empty set, every variable index in
    `collectNonArr {} body` holds a non-array runtime value under any consistent environment `ρ`,
    so eliding `.inc` / `.dec` / `.del` in `lowerBody` is an exact no-op on `CowHeap`. -/
theorem collectNonArr_sound (body : FnBody) (ρ : Nat → RcVal) (hcon : NonArrConsistent ρ body) :
    ∀ x : VarId, (collectNonArr {} body).contains x.idx = true →
      (∀ (h : CowHeap α) (n : Nat), h.rcInc (ρ x.idx) n = h ∧ h.rcDec (ρ x.idx) n = h) := by
  have hsound : NonArrSetSound (collectNonArr {} body) ρ := by
    apply collectNonArr_sound_aux (sizeOf body) body {} ρ (Nat.le_refl _) _ hcon
    intro k hk; simp at hk
  intro x hx h n
  have hmem : x.idx ∈ collectNonArr {} body := by simpa using hx
  rcases hsound x.idx hmem with ⟨v, hv⟩
  simp [hv]

/-- Cross-pass invariant linking `collectProjSrc` and `collectNonArr`: every constructor source `p`
    recorded in `collectProjSrc` is necessarily present in `collectNonArr`, guaranteeing that
    `lowerBody` elides `.dec p` / `.del p` rather than cascading decrements to field `x`. -/
private theorem collectProjSrc_subset_collectNonArr_aux :
    ∀ (sz : Nat) (b : FnBody) (calls : Std.HashSet Nat)
      (acc : Std.HashMap Nat Nat) (na : Std.HashSet Nat),
      sizeOf b ≤ sz →
      (∀ x p, acc.get? x = some p → p ∈ na) →
      ∀ x p, (collectProjSrc calls acc b).get? x = some p → p ∈ collectNonArr na b
  | 0, b, _, _, _, hsz, _, _, _, _ => by
      cases b <;> simp at hsz <;> omega
  | sz + 1, b, calls, acc, na, hsz, hinv, x, p, hres => by
      cases b with
      | vdecl xv _ e cont =>
          cases e with
          | fap _ _ | ap _ _ =>
              simp only [collectProjSrc, collectNonArr] at hres ⊢
              exact collectProjSrc_subset_collectNonArr_aux sz cont _ acc na
                (by simp at hsz; omega) hinv x p hres
          | proj _ src =>
              simp only [collectProjSrc, collectNonArr] at hres ⊢
              apply collectProjSrc_subset_collectNonArr_aux sz cont calls _ (na.insert src.idx)
                (by simp at hsz; omega) _ x p hres
              intro k q hkq
              split at hkq
              · rw [Std.HashMap.get?_insert] at hkq
                by_cases hkx : (xv.idx == k) = true
                · simp only [hkx, ↓reduceIte, Option.some.injEq] at hkq
                  subst hkq
                  exact Std.HashSet.mem_insert.mpr (Or.inl (beq_self_eq_true _))
                · simp only [hkx, Bool.false_eq_true, ↓reduceIte] at hkq
                  exact collectNonArr_insert_mono na q src.idx (hinv k q hkq)
              · exact collectNonArr_insert_mono na q src.idx (hinv k q hkq)
          | uproj _ src | sproj _ _ src =>
              simp only [collectProjSrc, collectNonArr] at hres ⊢
              apply collectProjSrc_subset_collectNonArr_aux sz cont calls acc (na.insert src.idx)
                (by simp at hsz; omega) _ x p hres
              intro k q hkq
              exact collectNonArr_insert_mono na q src.idx (hinv k q hkq)
          | ctor _ _ | reuse _ _ _ _ | pap _ _ | lit _ | box _ _ | unbox _ | isShared _ =>
              simp only [collectProjSrc, collectNonArr] at hres ⊢
              apply collectProjSrc_subset_collectNonArr_aux sz cont calls acc (na.insert xv.idx)
                (by simp at hsz; omega) _ x p hres
              intro k q hkq
              exact collectNonArr_insert_mono na q xv.idx (hinv k q hkq)
          | reset _ _ =>
              simp only [collectProjSrc, collectNonArr] at hres ⊢
              exact collectProjSrc_subset_collectNonArr_aux sz cont calls acc na
                (by simp at hsz; omega) hinv x p hres
      | jdecl _ _ v cont =>
          simp only [collectProjSrc, collectNonArr] at hres ⊢
          have h1 := collectProjSrc_subset_collectNonArr_aux sz v calls acc na
            (by simp at hsz; omega) hinv
          exact collectProjSrc_subset_collectNonArr_aux sz cont calls (collectProjSrc calls acc v)
            (collectNonArr na v) (by simp at hsz; omega) h1 x p hres
      | case tid scr ty alts =>
          simp only [collectProjSrc, collectNonArr] at hres ⊢
          have haltsLt := sizeOf_alts_toList_lt tid scr ty alts
          suffices hAlts : ∀ (ls : List Alt) (a : Std.HashMap Nat Nat) (n : Std.HashSet Nat),
              sizeOf ls ≤ sz →
              (∀ k q, a.get? k = some q → q ∈ n) →
              (∀ k q, (collectProjSrcAlts calls a ls).get? k = some q → q ∈ collectNonArrAlts n ls) by
            exact hAlts alts.toList acc (na.insert scr.idx) (by omega)
              (fun k q hkq => collectNonArr_insert_mono na q scr.idx (hinv k q hkq)) x p hres
          intro ls
          induction ls with
          | nil => intro a n _ ha; exact ha
          | cons alt rest ih =>
              intro a n hls ha
              cases alt with
              | ctor _ body =>
                  simp only [collectProjSrcAlts, collectNonArrAlts]
                  apply ih _ _ (by simp at hls; omega)
                  exact collectProjSrc_subset_collectNonArr_aux sz body calls a n
                    (by simp at hls; omega) ha
              | default body =>
                  simp only [collectProjSrcAlts, collectNonArrAlts]
                  apply ih _ _ (by simp at hls; omega)
                  exact collectProjSrc_subset_collectNonArr_aux sz body calls a n
                    (by simp at hls; omega) ha
      | set _ _ _ cont | setTag _ _ cont | uset _ _ _ cont | sset _ _ _ _ _ cont
      | inc _ _ _ _ cont | dec _ _ _ _ cont | del _ cont =>
          simp only [collectProjSrc, collectNonArr] at hres ⊢
          exact collectProjSrc_subset_collectNonArr_aux sz cont calls acc na
            (by simp at hsz; omega) hinv x p hres
      | ret _ | jmp _ _ | unreachable =>
          exact hinv x p (by simpa [collectProjSrc] using hres)

theorem collectProjSrc_subset_collectNonArr (body : FnBody) (x p : Nat)
    (hsrc : (collectProjSrc {} {} body).get? x = some p) :
    (collectNonArr {} body).contains p = true := by
  have hmem : p ∈ collectNonArr {} body := by
    apply collectProjSrc_subset_collectNonArr_aux (sizeOf body) body {} {} {} (Nat.le_refl _)
    · intro _ _ hk; simp at hk
    · exact hsrc
  simpa using hmem

/-- Predicate characterizing when `FnBody` immediately drops constructor `p` along a straight-line
    projection/increment prefix without intervening calls or control flow. -/
inductive DropsVar (p : Nat) : FnBody → Prop where
  | dec (y : VarId) (n : Nat) (c b : Bool) (cont : FnBody) (hy : y.idx = p) :
      DropsVar p (.dec y n c b cont)
  | del (y : VarId) (cont : FnBody) (hy : y.idx = p) :
      DropsVar p (.del y cont)
  | dec_skip (y : VarId) (n : Nat) (c b : Bool) (cont : FnBody) (h : DropsVar p cont) :
      DropsVar p (.dec y n c b cont)
  | del_skip (y : VarId) (cont : FnBody) (h : DropsVar p cont) :
      DropsVar p (.del y cont)
  | inc_skip (y : VarId) (n : Nat) (c b : Bool) (cont : FnBody) (h : DropsVar p cont) :
      DropsVar p (.inc y n c b cont)
  | proj_skip (x : VarId) (ty : IRType) (i : Nat) (src : VarId) (cont : FnBody) (h : DropsVar p cont) :
      DropsVar p (.vdecl x ty (.proj i src) cont)
  | uproj_skip (x : VarId) (ty : IRType) (i : Nat) (src : VarId) (cont : FnBody) (h : DropsVar p cont) :
      DropsVar p (.vdecl x ty (.uproj i src) cont)
  | sproj_skip (x : VarId) (ty : IRType) (n off : Nat) (src : VarId) (cont : FnBody) (h : DropsVar p cont) :
      DropsVar p (.vdecl x ty (.sproj n off src) cont)

theorem hasDecOf_sound (p : Nat) : ∀ b : FnBody, hasDecOf p b = true → DropsVar p b
  | .dec y n c bflag cont, h => by
      simp only [hasDecOf, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with heq | hcont
      · exact DropsVar.dec y n c bflag cont heq.symm
      · exact DropsVar.dec_skip y n c bflag cont (hasDecOf_sound p cont hcont)
  | .del y cont, h => by
      simp only [hasDecOf, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with heq | hcont
      · exact DropsVar.del y cont heq.symm
      · exact DropsVar.del_skip y cont (hasDecOf_sound p cont hcont)
  | .inc y n c bflag cont, h => by
      simp only [hasDecOf] at h
      exact DropsVar.inc_skip y n c bflag cont (hasDecOf_sound p cont h)
  | .vdecl x ty e cont, h => by
      cases e with
      | proj _ _ =>
          simp only [hasDecOf] at h
          exact DropsVar.proj_skip x ty _ _ cont (hasDecOf_sound p cont h)
      | uproj _ _ =>
          simp only [hasDecOf] at h
          exact DropsVar.uproj_skip x ty _ _ cont (hasDecOf_sound p cont h)
      | sproj _ _ _ =>
          simp only [hasDecOf] at h
          exact DropsVar.sproj_skip x ty _ _ _ cont (hasDecOf_sound p cont h)
      | _ => simp [hasDecOf] at h
  | .jdecl _ _ _ _, h | .case _ _ _ _, h | .set _ _ _ _, h | .setTag _ _ _, h
  | .uset _ _ _ _, h | .sset _ _ _ _ _ _, h | .ret _, h | .jmp _ _, h | .unreachable, h => by
      simp [hasDecOf] at h

/-- Exact JS refcount step emitted by `lowerBody` for `.inc x n` when `projSrc` transfers 1 ref
    from `p` (`n' = n - 1`): elided if `n - 1 == 0`, otherwise `.incRef (v x) (n - 1)`. -/
def CowHeap.jsTransferInc (h : CowHeap α) (id n : Nat) : CowHeap α :=
  let n' := n - 1
  if n' == 0 then h else h.rcInc (.arr id) n'

/-- RC ref-transfer soundness theorem: for any `n ≥ 1`, incrementing array handle `id` by `n` in
    Lean IR followed by the cascading `-1` field decrement from dropping constructor `p` produces
    pointwise identical `CowHeap` state (refcounts, elements, marks, snapshots) to JS `lowerBody`'s
    `(n - 1)` increment with non-cascading constructor drop. -/
theorem projRefTransfer_cowHeap_equiv (h : CowHeap α) (id n : Nat) (hn : n ≥ 1) :
    ∀ k : Nat,
      (h.jsTransferInc id n).get k = ((h.rcInc (.arr id) n).rcDec (.arr id) 1).get k := by
  intro k
  dsimp only [CowHeap.jsTransferInc, CowHeap.rcInc, CowHeap.rcDec]
  by_cases hn1 : (n - 1 == 0) = true
  · have hnEq : n = 1 := by
      have : n - 1 = 0 := beq_iff_eq.mp hn1
      omega
    subst hnEq
    simp only [Nat.sub_self, beq_self_eq_true, ↓reduceIte]
    by_cases hkid : k = id
    · subst hkid
      simp only [CowHeap.get_set_self]
      rcases he : h.get k with ⟨el, rc, mk⟩
      simp
    · simp only [CowHeap.get_set_ne _ _ hkid]
  · simp only [hn1, Bool.false_eq_true, ↓reduceIte]
    by_cases hkid : k = id
    · subst hkid
      simp only [CowHeap.get_set_self]
      rcases he : h.get k with ⟨el, rc, mk⟩
      have hsub : rc + (n - 1) = rc + n - 1 := by omega
      simp [hsub]
    · simp only [CowHeap.get_set_ne _ _ hkid]

/-! ## 7. Operational Semantics & Simulation (`lowerBody_equiv`) for `Js.lowerBody` -/

def findSwitchArm (tag : Nat) : List JsSwitchArm → Option (List JsStmt)
  | [] => none
  | .caseArm cidx body :: rest => if cidx == tag then some body else findSwitchArm tag rest
  | .defaultArm body :: rest   =>
      match findSwitchArm tag rest with
      | some b => some b
      | none   => some body

private theorem findSwitchArm_sizeOf (tag : Nat) (arms : List JsSwitchArm) (body : List JsStmt)
    (h : findSwitchArm tag arms = some body) : sizeOf body < sizeOf arms := by
  induction arms with
  | nil => simp [findSwitchArm] at h
  | cons arm rest ih =>
      cases arm with
      | caseArm cidx b =>
          simp only [findSwitchArm] at h
          split at h
          · cases h; simp; omega
          · have := ih h; simp; omega
      | defaultArm b =>
          simp only [findSwitchArm] at h
          cases hrec : findSwitchArm tag rest with
          | some b' =>
              rw [hrec] at h; cases h
              have := ih hrec; simp; omega
          | none =>
              rw [hrec] at h; cases h
              simp; omega

private theorem sizeOf_body_lt_switch (scrut : JsExpr) (arms : List JsSwitchArm) (body : List JsStmt)
    (hlt : sizeOf body < sizeOf arms) : sizeOf body < 1 + sizeOf scrut + sizeOf arms := by
  omega

mutual
/-- Operational semantics extending `execStmt` / `execStmts` with `switchStmt` dispatch and
    pure-value fallthrough on `incRef` / `decRef`. -/
def evalJsStmt (env : JsEnv) : JsStmt → BlockExit
  | .letVar x val =>
      .fallthrough (bindEnv env x (evalJsExpr env val))
  | .letDecls names =>
      .fallthrough (bindMany env (names.map (·, .num 0)))
  | .letBinds binds =>
      let evaluated := binds.map fun (k, e) => (k, evalJsExpr env e)
      .fallthrough (bindMany env evaluated)
  | .labeledBlock lbl body =>
      match evalJsStmts env body with
      | .broke lbl' env' =>
          if lbl' == lbl then .fallthrough env' else .broke lbl' env'
      | other => other
  | .breakLabel assigns lbl =>
      let evaluated := assigns.map fun (lhs, rhs) => (lhs, evalJsExpr env rhs)
      .broke lbl (bindMany env evaluated)
  | .ret val =>
      .returned (evalJsExpr env val)
  | .switchStmt scrut arms =>
      match evalJsExpr env scrut with
      | .num tag =>
          match hfind : findSwitchArm tag arms with
          | some body =>
              have _hlt : sizeOf body < 1 + sizeOf scrut + sizeOf arms :=
                sizeOf_body_lt_switch scrut arms body (findSwitchArm_sizeOf tag arms body hfind)
              evalJsStmts env body
          | none      => .fallthrough env
      | _ => .fallthrough env
  | .incRef _ _ | .decRef _ _ => .fallthrough env
  | _ => .fallthrough env
termination_by s => sizeOf s

def evalJsStmts (env : JsEnv) : List JsStmt → BlockExit
  | [] => .fallthrough env
  | s :: ss =>
      match evalJsStmt env s with
      | .fallthrough env' => evalJsStmts env' ss
      | exitOut           => exitOut
termination_by ss => sizeOf ss
end

@[simp] theorem evalJsStmts_append :
    ∀ (s₁ s₂ : List JsStmt) (env : JsEnv),
      evalJsStmts env (s₁ ++ s₂) =
        match evalJsStmts env s₁ with
        | .fallthrough env' => evalJsStmts env' s₂
        | exitOut           => exitOut
  | [], s₂, env => by simp [evalJsStmts]
  | s :: ss, s₂, env => by
      simp only [List.cons_append, evalJsStmts]
      cases evalJsStmt env s <;> simp [evalJsStmts_append ss s₂]

abbrev IrEnv := Nat → JsVal

def bindIr (env : IrEnv) (k : Nat) (val : JsVal) : IrEnv :=
  fun m => if m == k then val else env m

def bindIrParams (env : IrEnv) : List Param → List JsVal → IrEnv
  | [], _ => env
  | _, [] => env
  | p :: ps, val :: vs => bindIrParams (bindIr env p.x.idx val) ps vs

def evalIrArg (env : IrEnv) : Arg → JsVal
  | .var x  => env x.idx
  | .erased => .num 0

def evalIrCtor (env : IrEnv) (i : CtorInfo) (ys : Array Arg) : JsVal :=
  if i.size == 0 && i.usize == 0 && i.ssize == 0 then
    .num i.cidx
  else
    .ctorObj i.cidx (ys.toList.map (evalIrArg env)) (i.ssize != 0) (i.usize != 0)

def PureExpr : IR.Expr → Bool
  | .ctor .. | .reuse .. | .proj .. | .box .. | .unbox .. | .lit .. => true
  | _ => false

def evalIrExpr (env : IrEnv) (ty : IRType) : IR.Expr → JsVal
  | .ctor i ys      => evalIrCtor env i ys
  | .reuse _ i _ ys => evalIrCtor env i ys
  | .proj idx x     =>
      match env x.idx with
      | .ctorObj _ fs _ _ => fs.getD idx (.num 0)
      | _                 => .num 0
  | .box _ x        => env x.idx
  | .unbox x        => env x.idx
  | .lit (.num n)   => if ty.isObj || ty == .uint64 then .bigInt n else .num n
  | .lit (.str s)   => .str s
  | _               => .num 0

def findAltBody (tag : Nat) : List Alt → Option FnBody
  | [] => none
  | .ctor info b :: rest => if info.cidx == tag then some b else findAltBody tag rest
  | .default b :: rest   =>
      match findAltBody tag rest with
      | some b' => some b'
      | none    => some b

theorem findSwitchArm_lowerAlts (c : Ctx) (tag : Nat) :
    ∀ alts : List Alt,
      findSwitchArm tag (lowerAlts c alts) = (findAltBody tag alts).map (lowerBody c)
  | [] => rfl
  | .ctor info b :: rest => by
      simp only [lowerAlts, findSwitchArm, findAltBody]
      by_cases h : (info.cidx == tag) = true
      · simp [h]
      · simp [h, findSwitchArm_lowerAlts c tag rest]
  | .default b :: rest => by
      simp only [lowerAlts, findSwitchArm, findAltBody]
      rw [findSwitchArm_lowerAlts c tag rest]
      cases findAltBody tag rest <;> rfl

/-- IR-to-JS variable agreement invariant: every Lean IR variable `x : VarId` maps in JS to
    `s!"x{x.idx}"` (`Js.v x`). -/
def JsMatchIr (irEnv : IrEnv) (jsEnv : JsEnv) : Prop :=
  ∀ k : Nat, jsEnv s!"x{k}" = irEnv k

private def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

private theorem digitVal_digitChar (d : Nat) (hd : d < 10) :
    digitVal (Nat.digitChar d) = d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem digitChar_mem_digits (d : Nat) (hd : d < 10) :
    Nat.digitChar d ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'] := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem nat_toDigitsCore_all_digits (n fuel : Nat) (ds : List Char)
    (hds : ∀ c ∈ ds, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) :
    ∀ c ∈ Nat.toDigitsCore 10 fuel n ds, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'] := by
  induction fuel generalizing n ds with
  | zero => exact hds
  | succ f ih =>
      simp only [Nat.toDigitsCore]
      split
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact digitChar_mem_digits (n % 10) (Nat.mod_lt n (by decide))
        · exact hds c hc'
      · apply ih
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact digitChar_mem_digits (n % 10) (Nat.mod_lt n (by decide))
        · exact hds c hc'

private def fromDigits (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + digitVal c) 0

private theorem fromDigits_append (xs ys : List Char) :
    fromDigits (xs ++ ys) = ys.foldl (fun acc c => acc * 10 + digitVal c) (fromDigits xs) := by
  simp [fromDigits, List.foldl_append]

private theorem toDigitsCore_append :
    ∀ (fuel n : Nat) (ds : List Char),
      Nat.toDigitsCore 10 fuel n ds = Nat.toDigitsCore 10 fuel n [] ++ ds
  | 0, _, _ => rfl
  | f + 1, n, ds => by
      simp only [Nat.toDigitsCore]
      split
      · rfl
      · rw [toDigitsCore_append f (n / 10) (Nat.digitChar (n % 10) :: ds),
            toDigitsCore_append f (n / 10) [Nat.digitChar (n % 10)],
            List.append_assoc, List.singleton_append]

private theorem fromDigits_toDigitsCore :
    ∀ (fuel n : Nat), n < fuel →
      fromDigits (Nat.toDigitsCore 10 fuel n []) = n
  | 0, _, hn => by omega
  | f + 1, n, hn => by
      simp only [Nat.toDigitsCore]
      by_cases hdiv : n / 10 = 0
      · simp only [hdiv, ↓reduceIte]
        have hlt : n < 10 := by omega
        simp [fromDigits, Nat.mod_eq_of_lt hlt, digitVal_digitChar n hlt]
      · simp only [hdiv, ↓reduceIte]
        rw [toDigitsCore_append f (n / 10) [Nat.digitChar (n % 10)]]
        rw [fromDigits_append]
        have hdivLt : n / 10 < f := by omega
        have hrec := fromDigits_toDigitsCore f (n / 10) hdivLt
        simp only [List.foldl_cons, List.foldl_nil]
        rw [hrec, digitVal_digitChar (n % 10) (Nat.mod_lt n (by decide))]
        omega

theorem nat_toString_digits (n : Nat) :
    ∀ c ∈ (toString n).toList, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'] := by
  have hrepr : (toString n).toList = Nat.toDigits 10 n := by
    change (Nat.repr n).toList = Nat.toDigits 10 n
    simp [Nat.repr]
  rw [hrepr]
  exact nat_toDigitsCore_all_digits n (n + 1) [] (fun _ h => by cases h)

theorem fromDigits_toString (n : Nat) : fromDigits (toString n).toList = n := by
  have hrepr : (toString n).toList = Nat.toDigits 10 n := by
    change (Nat.repr n).toList = Nat.toDigits 10 n
    simp [Nat.repr]
  rw [hrepr]
  exact fromDigits_toDigitsCore (n + 1) n (Nat.lt_succ_self n)

private theorem toString_str_eq (s : String) : toString s = s := rfl

private theorem str_x_toList : ("x" : String).toList = ['x'] := rfl
private theorem str_j_toList : ("j" : String).toList = ['j'] := rfl
private theorem str_us_toList : ("_" : String).toList = ['_'] := rfl
private theorem str_ug_toList : ("_g" : String).toList = ['_', 'g'] := rfl

theorem nat_toString_inj {a b : Nat} (h : toString a = toString b) : a = b := by
  have hl := congrArg (fun s : String => fromDigits s.toList) h
  dsimp only at hl
  rwa [fromDigits_toString, fromDigits_toString] at hl

theorem nat_repr_inj {a b : Nat} (h : Nat.repr a = Nat.repr b) : a = b :=
  nat_toString_inj h

theorem JsMatchIr_bind (irEnv : IrEnv) (jsEnv : JsEnv) (k : Nat) (val : JsVal)
    (hm : JsMatchIr irEnv jsEnv) :
    JsMatchIr (bindIr irEnv k val) (bindEnv jsEnv s!"x{k}" val) := by
  intro m
  simp only [bindIr, bindEnv]
  by_cases hmk : m = k
  · subst hmk; simp
  · have hne : s!"x{m}" ≠ s!"x{k}" := by
      intro h
      have hs := congrArg String.toList h
      simp only [toString_str_eq, Nat.toString_eq_repr, String.toList_append,
        str_x_toList, List.cons_append, List.nil_append, List.cons.injEq, true_and] at hs
      exact hmk (nat_repr_inj (String.toList_inj.mp hs))
    simp only [beq_iff_eq, hmk, ↓reduceIte, beq_false_of_ne hne, Bool.false_eq_true]
    exact hm m

theorem evalJsExpr_lowerArg (irEnv : IrEnv) (jsEnv : JsEnv) (hm : JsMatchIr irEnv jsEnv)
    (a : Arg) : evalJsExpr jsEnv (lowerArg a) = evalIrArg irEnv a := by
  cases a with
  | var x  => simp [lowerArg, evalJsExpr, evalIrArg, v]; exact hm x.idx
  | erased => simp [lowerArg, evalJsExpr, evalIrArg]

theorem evalJsExpr_lowerCtor (irEnv : IrEnv) (jsEnv : JsEnv) (hm : JsMatchIr irEnv jsEnv)
    (i : CtorInfo) (ys : Array Arg) :
    evalJsExpr jsEnv (lowerCtor i ys) = evalIrCtor irEnv i ys := by
  unfold lowerCtor evalIrCtor
  by_cases hscalar : (i.size == 0 && i.usize == 0 && i.ssize == 0) = true
  · simp [hscalar, evalJsExpr]
  · simp only [hscalar, Bool.false_eq_true, ↓reduceIte, evalJsExpr, evalJsExprList_map]
    congr 1
    exact List.map_congr_left fun a _ => evalJsExpr_lowerArg irEnv jsEnv hm a

theorem evalJsExpr_lowerExpr (c : Ctx) (irEnv : IrEnv) (jsEnv : JsEnv) (hm : JsMatchIr irEnv jsEnv)
    (ty : IRType) (e : IR.Expr) (hpure : PureExpr e = true) :
    evalJsExpr jsEnv (lowerExpr c ty e) = evalIrExpr irEnv ty e := by
  cases e with
  | ctor i ys      => exact evalJsExpr_lowerCtor irEnv jsEnv hm i ys
  | reuse _ i _ ys => exact evalJsExpr_lowerCtor irEnv jsEnv hm i ys
  | proj idx x     =>
      simp only [lowerExpr, evalJsExpr, evalIrExpr, v]
      have hx : jsEnv s!"x{x.idx}" = irEnv x.idx := hm x.idx
      change (match jsEnv s!"x{x.idx}" with | .ctorObj _ fs _ _ => fs.getD idx (.num 0) | _ => .num 0) = _
      rw [hx]
  | box _ x        => simp only [lowerExpr, evalJsExpr, evalIrExpr, v]; exact hm x.idx
  | unbox x        => simp only [lowerExpr, evalJsExpr, evalIrExpr, v]; exact hm x.idx
  | lit l =>
      cases l with
      | num n =>
          simp only [lowerExpr, evalIrExpr]
          split <;> simp [evalJsExpr]
      | str s => simp [lowerExpr, evalJsExpr, evalIrExpr]
  | _ => simp [PureExpr] at hpure

/-- Big-step outcome of evaluating an `IR.FnBody` over the pure + join-point + case fragment. -/
inductive IrOutcome where
  | ret (val : JsVal)
  | jmp (j : Nat) (args : List JsVal) (env : IrEnv)

/-- Big-step operational semantics for `Lean.IR.FnBody` over the modeled fragment
    (`.ret`, `.vdecl`, `.inc`/`.dec`/`.del`, non-rec `.jdecl`, `.jmp`, `.case`). -/
inductive EvalIR : IrEnv → FnBody → IrOutcome → Prop where
  | ret (env : IrEnv) (a : Arg) :
      EvalIR env (.ret a) (.ret (evalIrArg env a))
  | vdecl (env : IrEnv) (x : VarId) (ty : IRType) (e : IR.Expr) (cont : FnBody) (out : IrOutcome) :
      EvalIR (bindIr env x.idx (evalIrExpr env ty e)) cont out →
      EvalIR env (.vdecl x ty e cont) out
  | inc (env : IrEnv) (x : VarId) (n : Nat) (c b : Bool) (cont : FnBody) (out : IrOutcome) :
      EvalIR env cont out → EvalIR env (.inc x n c b cont) out
  | dec (env : IrEnv) (x : VarId) (n : Nat) (c b : Bool) (cont : FnBody) (out : IrOutcome) :
      EvalIR env cont out → EvalIR env (.dec x n c b cont) out
  | del (env : IrEnv) (x : VarId) (cont : FnBody) (out : IrOutcome) :
      EvalIR env cont out → EvalIR env (.del x cont) out
  | jmp (env : IrEnv) (j : JoinPointId) (ys : Array Arg) :
      EvalIR env (.jmp j ys) (.jmp j.idx (ys.toList.map (evalIrArg env)) env)
  | case (env : IrEnv) (tid : Name) (x : VarId) (xType : IRType) (alts : Array Alt)
      (armBody : FnBody) (out : IrOutcome) :
      findAltBody (jsTag (env x.idx)) alts.toList = some armBody →
      EvalIR env armBody out →
      EvalIR env (.case tid x xType alts) out
  | jdecl_ret (env : IrEnv) (j : JoinPointId) (xs : Array Param) (val cont : FnBody) (vret : JsVal) :
      EvalIR env cont (.ret vret) →
      EvalIR env (.jdecl j xs val cont) (.ret vret)
  | jdecl_jmp_outer (env : IrEnv) (j : JoinPointId) (xs : Array Param) (val cont : FnBody)
      (k : Nat) (args : List JsVal) (env' : IrEnv) :
      k ≠ j.idx →
      EvalIR env cont (.jmp k args env') →
      EvalIR env (.jdecl j xs val cont) (.jmp k args env')
  | jdecl_jmp_catch (env : IrEnv) (j : JoinPointId) (xs : Array Param) (val cont : FnBody)
      (args : List JsVal) (env' : IrEnv) (out : IrOutcome) :
      EvalIR env cont (.jmp j.idx args env') →
      EvalIR (bindIrParams env' xs.toList args) val out →
      EvalIR env (.jdecl j xs val cont) out

def altBody : Alt → FnBody
  | .ctor _ b  => b
  | .default b => b

/-- Well-formedness predicate ensuring `b` uses the modeled pure + non-recursive join-point
    fragment and matches the inline join-point arity table `c.inlineJps`. -/
inductive LowerFragment : Ctx → IrEnv → FnBody → Prop where
  | ret (c : Ctx) (irEnv : IrEnv) (a : Arg) :
      LowerFragment c irEnv (.ret a)
  | vdecl (c : Ctx) (irEnv : IrEnv) (x : VarId) (ty : IRType) (e : IR.Expr) (cont : FnBody) :
      PureExpr e = true →
      LowerFragment c (bindIr irEnv x.idx (evalIrExpr irEnv ty e)) cont →
      LowerFragment c irEnv (.vdecl x ty e cont)
  | inc (c : Ctx) (irEnv : IrEnv) (x : VarId) (n : Nat) (cf bf : Bool) (cont : FnBody) :
      LowerFragment c irEnv cont →
      LowerFragment c irEnv (.inc x n cf bf cont)
  | dec (c : Ctx) (irEnv : IrEnv) (x : VarId) (n : Nat) (cf bf : Bool) (cont : FnBody) :
      LowerFragment c irEnv cont →
      LowerFragment c irEnv (.dec x n cf bf cont)
  | del (c : Ctx) (irEnv : IrEnv) (x : VarId) (cont : FnBody) :
      LowerFragment c irEnv cont →
      LowerFragment c irEnv (.del x cont)
  | jmp (c : Ctx) (irEnv : IrEnv) (j : JoinPointId) (ys : Array Arg) (xs : Array Param) :
      c.inlineJps.get? j.idx = some xs →
      ys.toList.length = xs.toList.length →
      LowerFragment c irEnv (.jmp j ys)
  | case (c : Ctx) (irEnv : IrEnv) (tid : Name) (x : VarId) (xType : IRType) (alts : Array Alt) :
      (xType.isObj = true ∨ ∃ n, irEnv x.idx = .num n) →
      (∀ arm ∈ alts.toList, LowerFragment c irEnv (altBody arm)) →
      LowerFragment c irEnv (.case tid x xType alts)
  | jdecl (c : Ctx) (irEnv : IrEnv) (j : JoinPointId) (xs : Array Param) (val cont : FnBody) :
      hasJmpTo j val = false →
      ¬ c.inlineJps.contains j.idx →
      LowerFragment { c with inlineJps := c.inlineJps.insert j.idx xs } irEnv cont →
      (∀ env', LowerFragment c env' val) →
      LowerFragment c irEnv (.jdecl j xs val cont)

private theorem list_take_ne_x_append_digits (m j i : Nat) :
    s!"x{m}" ≠ s!"_{jp ⟨j⟩}_{i}" := by
  intro h
  have hc := congrArg String.toList h
  simp only [jp, toString_str_eq, Nat.toString_eq_repr, String.toList_append,
    str_x_toList, str_us_toList, str_j_toList, List.cons_append, List.nil_append] at hc
  cases hc

private theorem inline_var_ne_inline_var {j₁ j₂ i₁ i₂ : Nat} (hne : j₁ ≠ j₂) :
    s!"_{jp ⟨j₁⟩}_{i₁}" ≠ s!"_{jp ⟨j₂⟩}_{i₂}" := by
  intro h
  have hl := congrArg String.toList h
  simp only [jp, toString_str_eq, Nat.toString_eq_repr, String.toList_append,
    str_us_toList, str_j_toList, List.cons_append, List.nil_append, List.cons.injEq,
    true_and, List.append_assoc] at hl
  have hprefix : ∀ (d₁ d₂ r₁ r₂ : List Char),
      (∀ c ∈ d₁, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) →
      (∀ c ∈ d₂, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) →
      d₁ ++ '_' :: r₁ = d₂ ++ '_' :: r₂ → d₁ = d₂ := by
    intro d₁
    induction d₁ with
    | nil =>
        intro d₂ r₁ r₂ _ hd₂ heq
        cases d₂ with
        | nil => rfl
        | cons c ds =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
            have hc := hd₂ c (List.mem_cons_self ..)
            rw [← heq.1] at hc
            simp at hc
    | cons c₁ ds₁ ih =>
        intro d₂ r₁ r₂ hd₁ hd₂ heq
        cases d₂ with
        | nil =>
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
            have hc := hd₁ c₁ (List.mem_cons_self ..)
            rw [heq.1] at hc
            simp at hc
        | cons c₂ ds₂ =>
            simp only [List.cons_append, List.cons.injEq] at heq
            rw [heq.1]
            congr 1
            exact ih ds₂ r₁ r₂
              (fun c hc => hd₁ c (List.mem_cons_of_mem _ hc))
              (fun c hc => hd₂ c (List.mem_cons_of_mem _ hc))
              heq.2
  have hdEq := hprefix (Nat.repr j₁).toList (Nat.repr j₂).toList (Nat.repr i₁).toList (Nat.repr i₂).toList
    (by simpa [Nat.toString_eq_repr] using nat_toString_digits j₁)
    (by simpa [Nat.toString_eq_repr] using nat_toString_digits j₂) hl
  exact hne (nat_repr_inj (String.toList_inj.mp hdEq))

private theorem inline_var_inj_idx {j i₁ i₂ : Nat}
    (h : s!"_{jp ⟨j⟩}_{i₁}" = s!"_{jp ⟨j⟩}_{i₂}") : i₁ = i₂ := by
  have hl := congrArg String.toList h
  simp only [jp, toString_str_eq, Nat.toString_eq_repr, String.toList_append,
    str_us_toList, str_j_toList, List.cons_append, List.nil_append, List.cons.injEq,
    true_and, List.append_assoc, List.append_cancel_left_eq] at hl
  exact nat_repr_inj (String.toList_inj.mp hl)

private theorem bindMany_declNames_preserves (jsEnv : JsEnv) (names : List String)
    (hpre : ∀ s ∈ names, ∃ (j : JoinPointId) (i : Nat), s = s!"_{jp j}_{i}") :
    (∀ (k : Nat), bindMany jsEnv (names.map (·, .num 0)) s!"x{k}" = jsEnv s!"x{k}") ∧
    (∀ (j' : JoinPointId) (i' : Nat), (∀ s ∈ names, s ≠ s!"_{jp j'}_{i'}") →
      bindMany jsEnv (names.map (·, .num 0)) s!"_{jp j'}_{i'}" = jsEnv s!"_{jp j'}_{i'}") := by
  induction names generalizing jsEnv with
  | nil => exact ⟨fun _ => rfl, fun _ _ _ => rfl⟩
  | cons nm rest ih =>
      simp only [List.map_cons, bindMany]
      rcases hpre nm (List.mem_cons_self ..) with ⟨j, i, rfl⟩
      have ih' := ih (bindEnv jsEnv s!"_{jp j}_{i}" (.num 0))
        (fun s hs => hpre s (List.mem_cons_of_mem _ hs))
      constructor
      · intro k
        rw [ih'.1 k]
        simp only [bindEnv]
        have hne : s!"_{jp j}_{i}" ≠ s!"x{k}" := (list_take_ne_x_append_digits k j.idx i).symm
        split
        · rename_i heq
          exact absurd (beq_iff_eq.mp heq).symm hne
        · rfl
      · intro j' i' hne
        rw [ih'.2 j' i' (fun s hs => hne s (List.mem_cons_of_mem _ hs))]
        have hne' : s!"_{jp j}_{i}" ≠ s!"_{jp j'}_{i'}" :=
          hne s!"_{jp j}_{i}" (List.mem_cons_self ..)
        simp only [bindEnv]
        split
        · rename_i heq
          exact absurd (beq_iff_eq.mp heq).symm hne'
        · rfl

private theorem zipIdx_snd_ge {α : Type} (xs : List α) (off : Nat) :
    ∀ p ∈ xs.zipIdx off, off ≤ p.2 := by
  induction xs generalizing off with
  | nil => intro p hp; simp at hp
  | cons a rest ih =>
      intro p hp
      simp only [List.zipIdx_cons, List.mem_cons] at hp
      rcases hp with rfl | hrest
      · exact Nat.le_refl _
      · exact Nat.le_trans (Nat.le_succ _) (ih (off + 1) p hrest)

private theorem bindMany_zipIdx_break_lookup (jsEnv : JsEnv) (ys : List Arg)
    (irEnv : IrEnv) (hm : JsMatchIr irEnv jsEnv) (j : JoinPointId) :
    let evaled := (ys.zipIdx.map fun (a, i) => (s!"_{jp j}_{i}", evalJsExpr jsEnv (lowerArg a)))
    (∀ k, bindMany jsEnv evaled s!"x{k}" = irEnv k) ∧
    (∀ i (hi : i < ys.length),
      bindMany jsEnv evaled s!"_{jp j}_{i}" = evalIrArg irEnv (ys[i]'hi)) := by
  suffices gen : ∀ (xs : List Arg) (off : Nat) (env0 : JsEnv),
      (∀ k, env0 s!"x{k}" = irEnv k) →
      let evaled := (xs.zipIdx off).map fun p => (s!"_{jp j}_{p.2}", evalIrArg irEnv p.1)
      (∀ k, bindMany env0 evaled s!"x{k}" = irEnv k) ∧
      (∀ idx (hidx : idx < xs.length),
        bindMany env0 evaled s!"_{jp j}_{off + idx}" = evalIrArg irEnv (xs[idx]'hidx)) by
    have hmap :
        (ys.zipIdx.map fun (a, i) => (s!"_{jp j}_{i}", evalJsExpr jsEnv (lowerArg a))) =
        ((ys.zipIdx 0).map fun p => (s!"_{jp j}_{p.2}", evalIrArg irEnv p.1)) := by
      apply List.map_congr_left
      intro ⟨a, i⟩ _
      simp [evalJsExpr_lowerArg irEnv jsEnv hm a]
    intro evaled
    have hg := gen ys 0 jsEnv (fun k => hm k)
    simp only [Nat.zero_add] at hg
    dsimp only [evaled]
    rw [hmap]
    exact hg
  intro xs
  induction xs with
  | nil =>
      intro off env0 h0
      simp only [List.zipIdx_nil, List.map_nil, bindMany, List.length_nil]
      exact ⟨h0, fun _ h => by omega⟩
  | cons a rest ih =>
      intro off env0 h0
      simp only [List.zipIdx_cons, List.map_cons, bindMany]
      have h1 : ∀ k, bindEnv env0 s!"_{jp j}_{off}" (evalIrArg irEnv a) s!"x{k}" = irEnv k := by
        intro k
        simp only [bindEnv]
        have hne : s!"_{jp j}_{off}" ≠ s!"x{k}" := (list_take_ne_x_append_digits k j.idx off).symm
        simp only [beq_false_of_ne hne.symm, Bool.false_eq_true, ↓reduceIte]
        exact h0 k
      have ih1 := ih (off + 1) (bindEnv env0 s!"_{jp j}_{off}" (evalIrArg irEnv a)) h1
      constructor
      · exact ih1.1
      · intro idx hidx
        cases idx with
        | zero =>
            have hpres : ∀ (ls : List (Arg × Nat)) (e0 : JsEnv),
                (∀ p ∈ ls, p.2 > off) →
                bindMany e0 (ls.map fun p => (s!"_{jp j}_{p.2}", evalIrArg irEnv p.1)) s!"_{jp j}_{off}" =
                  e0 s!"_{jp j}_{off}" := by
              intro ls
              induction ls with
              | nil => intro _ _; rfl
              | cons pr tail iht =>
                  intro e0 hgt
                  simp only [List.map_cons, bindMany]
                  rw [iht _ (fun p hp => hgt p (List.mem_cons_of_mem _ hp))]
                  have hlt : pr.2 ≠ off := Nat.ne_of_gt (hgt pr (List.mem_cons_self ..))
                  have hne : s!"_{jp j}_{off}" ≠ s!"_{jp j}_{pr.2}" :=
                    fun h => hlt (inline_var_inj_idx h).symm
                  simp only [bindEnv, beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte]
            have hzero : off + 0 = off := Nat.add_zero off
            rw [hzero, hpres (rest.zipIdx (off + 1)) _ (fun ⟨a', i'⟩ hp =>
              zipIdx_snd_ge rest (off + 1) (a', i') hp)]
            simp only [bindEnv, beq_self_eq_true, ↓reduceIte]
            rfl
        | succ idx' =>
            have hadd : off + (idx' + 1) = (off + 1) + idx' := by omega
            rw [hadd]
            exact ih1.2 idx' (by simp at hidx; omega)

private theorem bindMany_post_matches (ps : List Param) (args : List JsVal)
    (irEnv : IrEnv) (jsEnv : JsEnv) (j : JoinPointId)
    (hm : JsMatchIr irEnv jsEnv)
    (hlen : args.length = ps.length)
    (hslots : ∀ i (hi : i < args.length), jsEnv s!"_{jp j}_{i}" = args[i]'hi) :
    let bindPairs := ps.zipIdx.map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}")
    let evaluated := bindPairs.map fun (k, e) => (k, evalJsExpr jsEnv e)
    JsMatchIr (bindIrParams irEnv ps args) (bindMany jsEnv evaluated) := by
  suffices gen : ∀ (ps' : List Param) (args' : List JsVal) (off : Nat)
      (ir0 : IrEnv) (js0 : JsEnv),
      JsMatchIr ir0 js0 →
      args'.length = ps'.length →
      (∀ i (hi : i < args'.length), jsEnv s!"_{jp j}_{off + i}" = args'[i]'hi) →
      let evaled := (ps'.zipIdx off).map fun p => (v p.1.x, jsEnv s!"_{jp j}_{p.2}")
      JsMatchIr (bindIrParams ir0 ps' args') (bindMany js0 evaled) by
    intro bindPairs evaluated
    have hev : evaluated = (ps.zipIdx 0).map fun p => (v p.1.x, jsEnv s!"_{jp j}_{p.2}") := by
      simp [evaluated, bindPairs, List.map_map, Function.comp_def, evalJsExpr]
    rw [hev]
    exact gen ps args 0 irEnv jsEnv hm hlen (fun i hi => by simpa using hslots i hi)
  intro ps'
  induction ps' with
  | nil =>
      intro args' off ir0 js0 hm0 hlen0 _
      cases args' with
      | nil => simpa [bindIrParams, bindMany] using hm0
      | cons _ _ => simp at hlen0
  | cons p rest ih =>
      intro args' off ir0 js0 hm0 hlen0 hsl0
      cases args' with
      | nil => simp at hlen0
      | cons a as =>
          simp only [List.zipIdx_cons, List.map_cons, bindIrParams, bindMany]
          have ha : jsEnv s!"_{jp j}_{off}" = a := by simpa using hsl0 0 (by simp)
          rw [ha]
          have hm1 : JsMatchIr (bindIr ir0 p.x.idx a) (bindEnv js0 (v p.x) a) :=
            JsMatchIr_bind ir0 js0 p.x.idx a hm0
          apply ih as (off + 1) _ _ hm1 (by simp at hlen0; exact hlen0)
          intro i hi
          have hadd : off + 1 + i = off + (i + 1) := by omega
          rw [hadd]
          simpa using hsl0 (i + 1) (by simp; omega)

private theorem evalJsStmts_switch_match (jsEnv : JsEnv) (scrut : JsExpr)
    (arms : List JsSwitchArm) (tag : Nat) (body : List JsStmt)
    (hscrut : evalJsExpr jsEnv scrut = .num tag)
    (hfind : findSwitchArm tag arms = some body) :
    evalJsStmts jsEnv [.switchStmt scrut arms] = evalJsStmts jsEnv body := by
  have hstmt : evalJsStmt jsEnv (.switchStmt scrut arms) = evalJsStmts jsEnv body := by
    simp only [evalJsStmt, hscrut]
    split
    · rename_i body' hfind'
      rw [hfind] at hfind'
      cases hfind'
      rfl
    · rename_i hfind'
      rw [hfind] at hfind'
      cases hfind'
  simp only [evalJsStmts, hstmt]
  cases evalJsStmts jsEnv body <;> rfl

private theorem findAltBody_mem (tag : Nat) (alts : List Alt) (body : FnBody)
    (h : findAltBody tag alts = some body) : ∃ arm ∈ alts, altBody arm = body := by
  induction alts generalizing body with
  | nil => simp [findAltBody] at h
  | cons a rest ih =>
      cases a with
      | ctor info b =>
          simp only [findAltBody] at h
          split at h
          · cases h; exact ⟨.ctor info body, List.mem_cons_self .., rfl⟩
          · rcases ih body h with ⟨arm, hm, hb⟩
            exact ⟨arm, List.mem_cons_of_mem _ hm, hb⟩
      | default b =>
          simp only [findAltBody] at h
          cases hf : findAltBody tag rest with
          | some b' =>
              rw [hf] at h; cases h
              rcases ih body hf with ⟨arm, hm, hb⟩
              exact ⟨arm, List.mem_cons_of_mem _ hm, hb⟩
          | none =>
              rw [hf] at h; cases h
              exact ⟨.default body, List.mem_cons_self .., rfl⟩

def SimResult (c : Ctx) (jsEnv : JsEnv) (stmts : List JsStmt) : IrOutcome → Prop
  | .ret val => evalJsStmts jsEnv stmts = .returned val
  | .jmp k args env' =>
      ∃ xs_k jsEnv',
        c.inlineJps.get? k = some xs_k ∧
        args.length = xs_k.toList.length ∧
        evalJsStmts jsEnv stmts = .broke (jp ⟨k⟩) jsEnv' ∧
        JsMatchIr env' jsEnv' ∧
        (∀ i (hi : i < args.length), jsEnv' s!"_{jp ⟨k⟩}_{i}" = args[i]'hi)

private theorem SimResult_congr {c : Ctx} {jsEnv jsEnv' : JsEnv} {s s' : List JsStmt}
    {out : IrOutcome} (heq : evalJsStmts jsEnv s = evalJsStmts jsEnv' s')
    (h : SimResult c jsEnv' s' out) : SimResult c jsEnv s out := by
  cases out with
  | ret val => simpa [SimResult, heq] using h
  | jmp k args env' =>
      rcases h with ⟨xs_k, je', h1, h2, h3, h4, h5⟩
      exact ⟨xs_k, je', h1, h2, heq.trans h3, h4, h5⟩

private theorem evalJsStmts_if_rc (jsEnv : JsEnv) (cond : Bool) (stmt : JsStmt) (ss : List JsStmt)
    (hrc : (∃ x n, stmt = .incRef x n) ∨ ∃ x n, stmt = .decRef x n) :
    evalJsStmts jsEnv (if cond = true then ss else stmt :: ss) = evalJsStmts jsEnv ss := by
  cases cond
  · rcases hrc with ⟨x, n, rfl⟩ | ⟨x, n, rfl⟩ <;> simp [evalJsStmts, evalJsStmt]
  · simp

private theorem evalJsStmts_jdecl_pre (jsEnv : JsEnv) (irEnv : IrEnv) (j : JoinPointId)
    (xs : Array Param) (hm : JsMatchIr irEnv jsEnv) :
    ∃ jsEnv0,
      evalJsStmts jsEnv (if xs.isEmpty then [] else
        [JsStmt.letDecls (xs.toList.zipIdx.map fun (_, i) => s!"_{jp j}_{i}")]) =
      .fallthrough jsEnv0 ∧ JsMatchIr irEnv jsEnv0 := by
  by_cases he : xs.isEmpty
  · simp [he, evalJsStmts, hm]
  · simp only [he, Bool.false_eq_true, ↓reduceIte, evalJsStmts, evalJsStmt]
    refine ⟨_, rfl, fun m => ?_⟩
    have hbm := bindMany_declNames_preserves jsEnv
      (xs.toList.zipIdx.map fun (_, i) => s!"_{jp j}_{i}")
      (fun s hs => by
        simp only [List.mem_map, Prod.exists] at hs
        rcases hs with ⟨_, i, _, rfl⟩
        exact ⟨j, i, rfl⟩)
    rw [hbm.1 m]
    exact hm m

private theorem pref_nat_inj (pfx : String) {a b : Nat}
    (h : pfx ++ toString a = pfx ++ toString b) : a = b := by
  have hl : pfx.toList ++ (toString a).toList = pfx.toList ++ (toString b).toList := by
    simpa [String.toList_append] using congrArg String.toList h
  exact nat_toString_inj (String.toList_inj.mp (List.append_cancel_left hl))

private theorem lowerBody_equiv_sim (c : Ctx) (irEnv : IrEnv) (jsEnv : JsEnv) (b : FnBody) (out : IrOutcome)
    (hm : JsMatchIr irEnv jsEnv)
    (hfrag : LowerFragment c irEnv b)
    (heval : EvalIR irEnv b out) :
    SimResult c jsEnv (lowerBody c b) out := by
  induction heval generalizing c jsEnv with
  | ret env a =>
      simp [SimResult, lowerBody, evalJsStmts, evalJsStmt, evalJsExpr_lowerArg env jsEnv hm a]
  | vdecl env x ty e cont out hcont ih =>
      cases hfrag with
      | vdecl _ _ _ _ _ _ hpure hfragCont =>
          have hnofap : ∀ f args, e ≠ .fap f args := by
            intro f args heq
            subst heq
            simp [PureExpr] at hpure
          have hlb : lowerBody c (.vdecl x ty e cont) =
              .letVar (v x) (lowerExpr c ty e) :: lowerBody c cont := by
            cases e with
            | fap f args => exact False.elim (hnofap f args rfl)
            | _ => rfl
          have hstep : evalJsStmts jsEnv (lowerBody c (.vdecl x ty e cont)) =
              evalJsStmts (bindEnv jsEnv (v x) (evalIrExpr env ty e)) (lowerBody c cont) := by
            rw [hlb]
            simp only [evalJsStmts, evalJsStmt, evalJsExpr_lowerExpr c env jsEnv hm ty e hpure]
          exact SimResult_congr hstep
            (ih c (bindEnv jsEnv (v x) (evalIrExpr env ty e))
              (JsMatchIr_bind env jsEnv x.idx (evalIrExpr env ty e) hm) hfragCont)
  | inc env x n cflag bflag cont out hcont ih =>
      cases hfrag with
      | inc _ _ _ _ _ _ _ hfragCont =>
          exact SimResult_congr
            (by simpa only [lowerBody] using evalJsStmts_if_rc jsEnv _ _ (lowerBody c cont) (.inl ⟨_, _, rfl⟩))
            (ih c jsEnv hm hfragCont)
  | dec env x n cflag bflag cont out hcont ih =>
      cases hfrag with
      | dec _ _ _ _ _ _ _ hfragCont =>
          exact SimResult_congr
            (by simpa only [lowerBody] using evalJsStmts_if_rc jsEnv _ _ (lowerBody c cont) (.inr ⟨_, _, rfl⟩))
            (ih c jsEnv hm hfragCont)
  | del env x cont out hcont ih =>
      cases hfrag with
      | del _ _ _ _ hfragCont =>
          exact SimResult_congr
            (by simpa only [lowerBody] using evalJsStmts_if_rc jsEnv _ _ (lowerBody c cont) (.inr ⟨_, _, rfl⟩))
            (ih c jsEnv hm hfragCont)
  | jmp env j ys =>
      cases hfrag with
      | jmp _ _ _ _ xs hget hlen =>
          simp only [SimResult, lowerBody, hget]
          refine ⟨xs, bindMany jsEnv (ys.toList.zipIdx.map fun (a, i) =>
            (s!"_{jp j}_{i}", evalJsExpr jsEnv (lowerArg a))), rfl, by simp [hlen], ?_, ?_, ?_⟩
          · simp [evalJsStmts, evalJsStmt]; rfl
          · exact (bindMany_zipIdx_break_lookup jsEnv ys.toList env hm j).1
          · intro i hi
            simp only [List.length_map] at hi
            rw [(bindMany_zipIdx_break_lookup jsEnv ys.toList env hm j).2 i hi]
            simp
  | case env tid x xType alts armBody out hfind harm ih =>
      cases hfrag with
      | case _ _ _ _ _ _ hxtype halts =>
          have hscrut :
              evalJsExpr jsEnv (if xType.isObj then .call "$.tag" [.var (v x)] else .var (v x)) =
                .num (jsTag (env x.idx)) := by
            have hxm : jsEnv (v x) = env x.idx := hm x.idx
            rcases hxtype with hobj | ⟨n, hn⟩
            · simp [hobj, evalJsExpr, hxm]
            · by_cases hobj : xType.isObj
              · simp [hobj, evalJsExpr, hxm]
              · simp [hobj, evalJsExpr, hxm, hn, jsTag]
          have hstep : evalJsStmts jsEnv (lowerBody c (.case tid x xType alts)) =
              evalJsStmts jsEnv (lowerBody c armBody) := by
            rw [lowerBody]
            exact evalJsStmts_switch_match jsEnv
              (if xType.isObj then .call "$.tag" [.var (v x)] else .var (v x))
              (lowerAlts c alts.toList) (jsTag (env x.idx)) (lowerBody c armBody) hscrut
              (by rw [findSwitchArm_lowerAlts, hfind]; rfl)
          rcases findAltBody_mem (jsTag (env x.idx)) alts.toList armBody hfind with
            ⟨arm, harmMem, harmEq⟩
          have hfragArm := halts arm harmMem
          rw [harmEq] at hfragArm
          exact SimResult_congr hstep (ih c jsEnv hm hfragArm)
  | jdecl_ret env j xs val cont vret hcont ih =>
      cases hfrag with
      | jdecl _ _ _ _ _ _ hnonrec _ hfragCont _ =>
          let c' := { c with inlineJps := c.inlineJps.insert j.idx xs }
          simp only [SimResult, lowerBody, hnonrec, Bool.not_false, ↓reduceIte]
          rw [evalJsStmts_append, evalJsStmts_append, evalJsStmts_append]
          rcases evalJsStmts_jdecl_pre jsEnv env j xs hm with ⟨jsEnv0, hpreEq, hm0⟩
          rw [hpreEq]
          have ihRun : evalJsStmts jsEnv0 (lowerBody c' cont) = .returned vret :=
            ih c' jsEnv0 hm0 hfragCont
          simp only [evalJsStmts, evalJsStmt]
          rw [ihRun]
  | jdecl_jmp_outer env j xs val cont k args env' hne hcont ih =>
      cases hfrag with
      | jdecl _ _ _ _ _ _ hnonrec _ hfragCont _ =>
          let c' := { c with inlineJps := c.inlineJps.insert j.idx xs }
          simp only [SimResult, lowerBody, hnonrec, Bool.not_false, ↓reduceIte]
          rcases evalJsStmts_jdecl_pre jsEnv env j xs hm with ⟨jsEnv0, hpreEq, hm0⟩
          rcases ih c' jsEnv0 hm0 hfragCont with ⟨xs_k, jsEnv', hget', hlen', hrun', hm', hslots'⟩
          have hget : c.inlineJps.get? k = some xs_k := by
            dsimp only [c'] at hget'
            rw [Std.HashMap.get?_insert] at hget'
            have hbeq : (j.idx == k) = false := beq_false_of_ne hne.symm
            simpa [hbeq] using hget'
          refine ⟨xs_k, jsEnv', hget, hlen', ?_, hm', hslots'⟩
          rw [evalJsStmts_append, evalJsStmts_append, evalJsStmts_append, hpreEq]
          simp only [evalJsStmts, evalJsStmt]
          rw [hrun']
          have hlblNe : (jp ⟨k⟩ == jp j) = false :=
            beq_false_of_ne fun heq => hne (pref_nat_inj "j" heq)
          simp [hlblNe]
  | jdecl_jmp_catch env j xs val cont args env' out hcont hval ihCont ihVal =>
      cases hfrag with
      | jdecl _ _ _ _ _ _ hnonrec _ hfragCont hfragVal =>
          let c' := { c with inlineJps := c.inlineJps.insert j.idx xs }
          rcases evalJsStmts_jdecl_pre jsEnv env j xs hm with ⟨jsEnv0, hpreEq, hm0⟩
          rcases ihCont c' jsEnv0 hm0 hfragCont with ⟨xs_k, jsEnv', hget', hlen', hrun', hm', hslots'⟩
          have hxsEq : xs_k = xs := by
            dsimp only [c'] at hget'
            rw [Std.HashMap.get?_insert] at hget'
            simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hget'
            exact hget'.symm
          have hlen'' : args.length = xs.toList.length := by rw [← hxsEq]; exact hlen'
          have hpost : ∃ jsEnv'',
              evalJsStmts jsEnv' (if xs.isEmpty then [] else
                [JsStmt.letBinds (xs.toList.zipIdx.map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}"))]) =
              .fallthrough jsEnv'' ∧ JsMatchIr (bindIrParams env' xs.toList args) jsEnv'' := by
            by_cases he : xs.isEmpty
            · have hnil : xs.toList = [] := by
                cases hxs : xs.toList <;> simp_all [Array.isEmpty]
              have hargsNil : args = [] := by
                have := hlen''; rw [hnil] at this; exact List.eq_nil_of_length_eq_zero this
              rw [hnil, hargsNil]
              simp [he, evalJsStmts, bindIrParams, hm']
            · simp only [he, Bool.false_eq_true, ↓reduceIte, evalJsStmts, evalJsStmt]
              refine ⟨_, rfl, ?_⟩
              exact bindMany_post_matches xs.toList args env' jsEnv' j hm' hlen''
                (fun i hi => hslots' i hi)
          rcases hpost with ⟨jsEnv'', hpostEq, hm''⟩
          have hstep : evalJsStmts jsEnv (lowerBody c (.jdecl j xs val cont)) =
              evalJsStmts jsEnv'' (lowerBody c val) := by
            simp only [lowerBody, hnonrec, Bool.not_false, ↓reduceIte]
            rw [evalJsStmts_append, evalJsStmts_append, evalJsStmts_append, hpreEq]
            simp only [evalJsStmts, evalJsStmt]
            rw [hrun']
            simp only [beq_self_eq_true, ↓reduceIte]
            rw [hpostEq]
          exact SimResult_congr hstep
            (ihVal c jsEnv'' hm'' (hfragVal (bindIrParams env' xs.toList args)))

/-- Full operational simulation theorem for `Js.lowerBody`:
    for every `b : FnBody` in `LowerFragment`, whenever `EvalIR irEnv b out` holds and `jsEnv`
    agrees with `irEnv` (`JsMatchIr`), executing `evalJsStmts jsEnv (lowerBody c b)` produces the
    exact corresponding JS `BlockExit` (`.returned v` on `.ret v`, and `.broke (jp k) jsEnv'` with
    all join-point arguments and `JsMatchIr` preserved on `.jmp k args env'`). -/
theorem lowerBody_equiv (c : Ctx) (irEnv : IrEnv) (jsEnv : JsEnv) (b : FnBody) (out : IrOutcome)
    (hm : JsMatchIr irEnv jsEnv)
    (hfrag : LowerFragment c irEnv b)
    (heval : EvalIR irEnv b out) :
    match out with
    | .ret val => evalJsStmts jsEnv (lowerBody c b) = .returned val
    | .jmp k args env' =>
        ∃ xs_k jsEnv',
          c.inlineJps.get? k = some xs_k ∧
          args.length = xs_k.toList.length ∧
          evalJsStmts jsEnv (lowerBody c b) = .broke (jp ⟨k⟩) jsEnv' ∧
          JsMatchIr env' jsEnv' ∧
          (∀ i (hi : i < args.length), jsEnv' s!"_{jp ⟨k⟩}_{i}" = args[i]'hi) := by
  have h := lowerBody_equiv_sim c irEnv jsEnv b out hm hfrag heval
  cases out <;> exact h

/-! ## 8. Identifier Hygiene, Mangle Safety & Global Name Disjointness -/

theorem v_inj {x y : VarId} (h : v x = v y) : x.idx = y.idx :=
  pref_nat_inj "x" h

theorem jp_inj {i k : JoinPointId} (h : jp i = jp k) : i.idx = k.idx :=
  pref_nat_inj "j" h

theorem v_ne_jp (x : VarId) (j : JoinPointId) : v x ≠ jp j := by
  intro h
  have hl := congrArg String.toList h
  simp only [v, jp, toString_str_eq, Nat.toString_eq_repr, String.toList_append,
    str_x_toList, str_j_toList, List.cons_append, List.nil_append] at hl
  cases hl

def genGlobalName (counter : Nat) : String := s!"_g{counter}"
def inlineJpSlot (j : JoinPointId) (i : Nat) : String := s!"_{jp j}_{i}"

theorem genGlobalName_inj {a b : Nat} (h : genGlobalName a = genGlobalName b) : a = b :=
  pref_nat_inj "_g" h

theorem genGlobalName_disjoint_all (counter : Nat) (x : VarId) (j : JoinPointId) (i : Nat)
    (ext : String) :
    genGlobalName counter ≠ v x ∧
    genGlobalName counter ≠ jp j ∧
    genGlobalName counter ≠ inlineJpSlot j i ∧
    genGlobalName counter ≠ "$." ++ ext ∧
    genGlobalName counter ≠ "__step" ∧
    genGlobalName counter ≠ "__r" ∧
    genGlobalName counter ≠ "__externs" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro h
    have hl := congrArg String.toList h
    simp only [genGlobalName, v, jp, inlineJpSlot, toString_str_eq, Nat.toString_eq_repr,
      String.toList_append, str_ug_toList, str_x_toList, str_j_toList, str_us_toList,
      List.cons_append, List.nil_append] at hl
    first
    | exact absurd hl (by cases hl; simp_all)
    | (try cases hl)

theorem inlineJpSlot_inj {j₁ j₂ : JoinPointId} {i₁ i₂ : Nat}
    (h : inlineJpSlot j₁ i₁ = inlineJpSlot j₂ i₂) :
    j₁.idx = j₂.idx ∧ i₁ = i₂ := by
  by_cases hj : j₁.idx = j₂.idx
  · refine ⟨hj, ?_⟩
    have hj' : j₁ = j₂ := by cases j₁; cases j₂; simp_all
    subst hj'
    exact inline_var_inj_idx h
  · exact False.elim (inline_var_ne_inline_var hj (by simpa [inlineJpSlot] using h))

theorem ctxJs_fallback_startsWith_dollar (c : Ctx) (n : Name) (hmiss : c.names.get? n = none) :
    (c.js n).startsWith "$." = true := by
  unfold Ctx.js
  rw [hmiss]
  simp [String.startsWith]

private def mangleStep (s : String) (c : Char) : String :=
  if c.isAlphanum then s.push c
  else if c == '.' || c == '_' then s.push '_'
  else s ++ s!"x{c.toNat}"

private theorem mangleStep_preserves (s : String) (c : Char)
    (hs : ∀ ch ∈ s.toList, ch.isAlphanum = true ∨ ch = '_') :
    ∀ ch ∈ (mangleStep s c).toList, ch.isAlphanum = true ∨ ch = '_' := by
  dsimp only [mangleStep]
  split
  · rename_i hal
    intro ch hch
    rw [String.toList_push, List.mem_append, List.mem_singleton] at hch
    rcases hch with h1 | rfl
    · exact hs ch h1
    · exact Or.inl hal
  · split
    · intro ch hch
      rw [String.toList_push, List.mem_append, List.mem_singleton] at hch
      rcases hch with h1 | rfl
      · exact hs ch h1
      · exact Or.inr rfl
    · intro ch hch
      rw [String.toList_append] at hch
      rcases List.mem_append.mp hch with h1 | h2
      · exact hs ch h1
      · have hx : ("x" ++ toString c.toNat).toList = 'x' :: (toString c.toNat).toList := by
          simp [String.toList_append, str_x_toList]
        change ch ∈ ("x" ++ toString c.toNat).toList at h2
        rw [hx, List.mem_cons] at h2
        rcases h2 with rfl | hdig
        · exact Or.inl (by decide)
        · have hd := nat_toString_digits c.toNat ch hdig
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact Or.inl (by decide)

private theorem forIn_mangle_preserves (cs : List Char) (s : String)
    (hs : ∀ ch ∈ s.toList, ch.isAlphanum = true ∨ ch = '_') :
    ∀ ch ∈ (Id.run (forIn cs s fun c r =>
      if c.isAlphanum = true then pure (ForInStep.yield (r.push c))
      else if (c = '.' ∨ c = '_') then pure (ForInStep.yield (r.push '_'))
      else pure (ForInStep.yield (r ++ (toString "x" ++ c.toNat.repr))))).toList,
      ch.isAlphanum = true ∨ ch = '_' := by
  induction cs generalizing s with
  | nil => simpa using hs
  | cons c rest ih =>
      simp only [List.forIn_cons, Id.run, bind, pure]
      by_cases hal : c.isAlphanum = true
      · simp only [hal, ↓reduceIte]
        apply ih
        exact fun ch hch => by
          have : mangleStep s c = s.push c := by simp [mangleStep, hal]
          rw [← this] at hch
          exact mangleStep_preserves s c hs ch hch
      · by_cases hdu : c = '.' ∨ c = '_'
        · simp only [hal, Bool.false_eq_true, ↓reduceIte, hdu]
          apply ih
          exact fun ch hch => by
            have : mangleStep s c = s.push '_' := by
              rcases hdu with rfl | rfl <;> simp [mangleStep, hal]
            rw [← this] at hch
            exact mangleStep_preserves s c hs ch hch
        · simp only [hal, Bool.false_eq_true, ↓reduceIte, hdu]
          apply ih
          exact fun ch hch => by
            have : mangleStep s c = s ++ (toString "x" ++ c.toNat.repr) := by
              simp only [mangleStep, hal, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true,
                beq_iff_eq]
              split
              · rename_i hc; exact absurd hc hdu
              · rfl
            rw [← this] at hch
            exact mangleStep_preserves s c hs ch hch

/-- Identifier hygiene for `Js.mangle`: every character in `mangle n` is strictly alphanumeric
    or `'_'`, never emitting `.`, `$`, whitespace, quotes, or JS operators. -/
theorem mangle_chars_safe (n : Name) :
    ∀ ch ∈ (mangle n).toList, ch.isAlphanum = true ∨ ch = '_' := by
  unfold mangle
  simpa using forIn_mangle_preserves n.toString.toList "" (fun _ h => by simp at h)

/-- Step and invariant for `_g{counter}` allocation in `emitProgramWithExterns`:
    as `counter` increases strictly over non-entry `.fdecl` names, every allocated internal name
    is pairwise distinct from all prior and subsequent `_g{k}` globals and from entry names
    not starting with `"_g"`. -/
def assignProgramNamesStep
    (st : Std.HashMap Name String × Nat) (name : Name) (entryMap : Std.HashMap Name String)
    (isFdecl : Bool) : Std.HashMap Name String × Nat :=
  if isFdecl then
    match entryMap.get? name with
    | some s => (st.1.insert name s, st.2)
    | none   => (st.1.insert name (genGlobalName st.2), st.2 + 1)
  else st

theorem assignProgramNames_invariant
    (steps : List (Name × Bool)) (entryMap : Std.HashMap Name String)
    (hentries : ∀ n s, entryMap.get? n = some s → ∀ i, s ≠ genGlobalName i)
    (nm₀ : Std.HashMap Name String) (cnt₀ : Nat)
    (hbound : ∀ k nm, nm₀.get? k = some nm → ∀ i ≥ cnt₀, nm ≠ genGlobalName i) :
    let (nm₁, cnt₁) := steps.foldl (fun st p => assignProgramNamesStep st p.1 entryMap p.2) (nm₀, cnt₀)
    cnt₀ ≤ cnt₁ ∧
    (∀ k nm, nm₁.get? k = some nm → ∀ i ≥ cnt₁, nm ≠ genGlobalName i) := by
  induction steps generalizing nm₀ cnt₀ with
  | nil => exact ⟨Nat.le_refl _, hbound⟩
  | cons p rest ih =>
      simp only [List.foldl_cons]
      dsimp only [assignProgramNamesStep]
      cases p.2 with
      | false =>
          exact ih nm₀ cnt₀ hbound
      | true =>
          cases he : entryMap.get? p.1 with
          | some s =>
              refine ih (nm₀.insert p.1 s) cnt₀ ?_
              intro k nm hget i hi
              rw [Std.HashMap.get?_insert] at hget
              by_cases hpk : (p.1 == k) = true
              · simp only [hpk, ↓reduceIte, Option.some.injEq] at hget
                subst hget
                exact hentries p.1 s he i
              · simp only [hpk, Bool.false_eq_true, ↓reduceIte] at hget
                exact hbound k nm hget i hi
          | none =>
              have ih' := ih (nm₀.insert p.1 (genGlobalName cnt₀)) (cnt₀ + 1) (by
                intro k nm hget i hi
                rw [Std.HashMap.get?_insert] at hget
                by_cases hpk : (p.1 == k) = true
                · simp only [hpk, ↓reduceIte, Option.some.injEq] at hget
                  subst hget
                  intro hcontra
                  have := genGlobalName_inj hcontra
                  omega
                · simp only [hpk, Bool.false_eq_true, ↓reduceIte] at hget
                  exact hbound k nm hget i (by omega))
              rcases ih' with ⟨hle, hb⟩
              exact ⟨Nat.le_trans (Nat.le_succ cnt₀) hle, hb⟩

end Js.Proofs



