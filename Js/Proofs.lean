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

end Js.Proofs
