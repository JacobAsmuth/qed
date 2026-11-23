import Js.Proofs.Core

namespace Js.Proofs

open Lean IR

/-! ## 4. Unified Calculi, Simulation Predicates & Shared Step Lemmas -/

def bindEnv {α : Type} (env : String → α) (k : String) (val : α) : String → α := fun s => if s == k then val else env s
def bindMany {α : Type} : List (String × α) → (String → α) → (String → α)
  | [], env => env | (k, val) :: rest, env => bindMany rest (bindEnv env k val)
def bindIrParams (ps : Array Param) (vals : List JsVal) (ρ : Nat → JsVal) : Nat → JsVal :=
  match ps.toList, vals with | [], _ | _, [] => ρ | p :: prest, val :: vrest => bindIrParams ⟨prest⟩ vrest (fun k => if k == p.x.idx then val else ρ k)
@[simp] theorem bindEnv_self {α : Type} (env : String → α) (k : String) (val : α) : bindEnv env k val k = val := by simp [bindEnv]
@[simp] theorem bindEnv_ne {α : Type} (env : String → α) {k s : String} (val : α) (hne : s ≠ k) : bindEnv env k val s = env s := by simp [bindEnv, hne]

theorem bindMany_lookup_not_mem {α : Type} : ∀ (ps : List (String × α)) (env : String → α) (k : String), (∀ p ∈ ps, p.1 ≠ k) → bindMany ps env k = env k
  | [], _, _, _ => rfl | (_, _) :: rest, env, k, h => by simp only [bindMany, bindMany_lookup_not_mem rest _ k fun p hp => h p (.tail _ hp), bindEnv_ne env _ (h _ (.head _)).symm]
theorem bindMany_lookup_nodup {α : Type} : ∀ (ps : List (String × α)) (env : String → α), (ps.map Prod.fst).Nodup → ∀ k val, (k, val) ∈ ps → bindMany ps env k = val
  | [], _, _, _, _, hm => nomatch hm
  | (_, _) :: rest, env, hnd, k, val, hm => by
      simp only [List.map_cons, List.nodup_cons] at hnd; rcases List.mem_cons.1 hm with hhd | hmem
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhd; rw [bindMany, bindMany_lookup_not_mem rest _ k fun p hp heq => hnd.1 (List.mem_map.2 ⟨p, hp, heq⟩), bindEnv_self]
      · exact bindMany_lookup_nodup rest _ hnd.2 k val hmem

/-- Staged `tailContinue` assignment (`zip params args` via `bindMany`) updates every parameter slot without clobbering when `params.Nodup`. -/
theorem tailContinue_staged_assign_sound {α : Type} (params : List String) (args : List α) (hp : params.Nodup) (hlen : params.length = args.length) (env : String → α) :
    ∀ i (hi : i < params.length), bindMany (params.zip args) env params[i] = args[i]'(hlen ▸ hi) := fun i hi => by
  have hmem : (params[i], args[i]'(hlen ▸ hi)) ∈ params.zip args := List.mem_iff_getElem.2 ⟨i, by simp [List.length_zip]; omega, by simp⟩
  have hmap : ∀ (ps : List String) (as : List α), ps.length = as.length → (ps.zip as).map Prod.fst = ps := fun ps => by
    induction ps with | nil => exact fun _ _ => rfl | cons _ _ ih => exact fun as hl => by cases as with | nil => simp at hl | cons _ as => simp [ih as (by simpa using hl)]
  exact bindMany_lookup_nodup (params.zip args) env (by rw [hmap params args hlen]; exact hp) _ _ hmem

theorem lowerBody_jdecl_nonrec_shape (c : Ctx) (j : JoinPointId) (xs : Array Param) (val b : FnBody) (hnonrec : hasJmpTo j val = false) :
    lowerBody c (.jdecl j xs val b) =
      (if xs.isEmpty then [] else [JsStmt.letDecls (xs.toList.zipIdx.map fun (_, i) => s!"_{jp j}_{i}")]) ++
      [.labeledBlock (jp j) (lowerBody { c with inlineJps := c.inlineJps.insert j.idx xs } b)] ++
      (if xs.isEmpty then [] else [JsStmt.letBinds (xs.toList.zipIdx.map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}"))]) ++ lowerBody c val := by
  dsimp only [lowerBody]; rw [hnonrec]; rfl
theorem lowerBody_selfTail_shape (c : Ctx) (x : VarId) (ty : IRType) (f : Name) (args : Array Arg) (b : FnBody)
    (hself : c.selfFn = some f) (hret : retsVar x b = true) (hloop : c.directLoop = true) :
    lowerBody c (.vdecl x ty (.fap f args) b) = [.tailContinue (c.selfParams.toList.map (v ·.x)) (args.toList.map lowerArg)] := by
  dsimp only [lowerBody]; rw [hself, beq_self_eq_true, hret, hloop]; rfl

/-! ### Unified Fuel-Indexed JS & IR Calculi -/
abbrev JsFnMap := String → Option (List String × List JsStmt × (String → JsVal))
abbrev JsProg  := String → Option JsDecl
def JsVal.setField : JsVal → Nat → JsVal → JsVal | .ctorObj t fs hs hu u s, i, v => .ctorObj t (fs.set i v) hs hu u s | o, _, _ => o
def JsVal.setTag : JsVal → Nat → JsVal | .ctorObj _ fs hs hu u s, c => .ctorObj c fs hs hu u s | _, c => .num c
def JsVal.setU : JsVal → Nat → JsVal → JsVal | .ctorObj t fs hs hu u s, i, v => .ctorObj t fs hs hu (assocSet i v u) s | o, _, _ => o
def JsVal.setS : JsVal → Nat → Nat → JsVal → JsVal | .ctorObj t fs hs hu u s, n, off, v => .ctorObj t fs hs hu u (assocSet (n, off) v s) | o, _, _, _ => o
def JsVal.isNonArr : JsVal → Bool | .arr _ => false | _ => true
def JsVal.noTc : JsVal → Prop
  | .tc _ => False
  | .ctorObj _ fs _ _ u s => (∀ v ∈ fs, v.noTc) ∧ (∀ p ∈ u, p.2.noTc) ∧ (∀ p ∈ s, p.2.noTc)
  | .pap fn _ acc => (∀ j : JoinPointId, fn ≠ jp j) ∧ (∀ v ∈ acc, v.noTc)
  | _ => True
termination_by v => sizeOf v
decreasing_by all_goals (have := List.sizeOf_lt_of_mem ‹_›; simp_wf; first | omega | (cases ‹_ × _›; simp at this ⊢; omega))
def isSharedVal (h : CowHeap JsVal) : JsVal → Bool | .arr id => decide (1 < (h.get id).refcount) | _ => false
structure JsState where
  env : String → JsVal
  heap : CowHeap JsVal := {}
  fns : JsFnMap := fun _ => none
  memos : String → MemoCell JsVal := fun _ => {}
inductive BlockExit where | next | returned (v : JsVal) | jumped (label : String) | tailCont (args : List JsVal)

abbrev JsCallFn     := JsState → String → List JsVal → Option (JsVal × JsState)
abbrev JsAppFn      := JsState → JsVal → List JsVal → Option (JsVal × JsState)
abbrev JsStmtsFn    := JsState → List JsStmt → Option (BlockExit × JsState)
abbrev JsSelfTailFn := Bool → List String → List JsStmt → JsState → List JsVal → Option (JsVal × JsState)

mutual
def evalJsExprStep (doCall : JsCallFn) (doApp : JsAppFn) (st : JsState) : JsExpr → Option (JsVal × JsState)
  | .var name => some (st.env name, st) | .numLit n => some (.num n, st) | .bigIntLit n => some (.bigInt n, st) | .strLit s => some (.str s, st) | .arrLit _ => some (.arr 0, st)
  | .ctorObj t fs hs hu => match evalJsExprListStep doCall doApp st fs with | some (vs, st') => some (.ctorObj t vs hs hu [] [], st') | none => none
  | .fieldProj o i => match evalJsExprStep doCall doApp st o with | some (.ctorObj _ fs _ _ _ _, st') => some (fs.getD i (.num 0), st') | some (_, st') => some (.num 0, st') | none => none
  | .uProj o i => match evalJsExprStep doCall doApp st o with | some (.ctorObj _ _ _ _ u _, st') => some (assocGet i u, st') | some (_, st') => some (.num 0, st') | none => none
  | .sProj o n off => match evalJsExprStep doCall doApp st o with | some (.ctorObj _ _ _ _ _ s, st') => some (assocGet (n, off) s, st') | some (_, st') => some (.num 0, st') | none => none
  | .pap fn ar args => match evalJsExprListStep doCall doApp st args with | some (vs, st') => some (.pap fn ar vs, st') | none => none
  | .tc args => match evalJsExprListStep doCall doApp st args with | some (vs, st') => some (.tc vs, st') | none => none
  | .call fn args => match evalJsExprListStep doCall doApp st args with
      | none => none
      | some (vs, st1) =>
          if fn == "$.tag" then match vs with | [v] => some (.num (jsTag v), st1) | _ => doCall st1 fn vs
          else if fn == "$.isShared" then match vs with | [v] => some (.num (if isSharedVal st1.heap v then 1 else 0), st1) | _ => doCall st1 fn vs
          else if fn == "$.refMark" then match vs with
            | [.arr id] => let (stamp, h') := st1.heap.refMark id; some (.num stamp, { st1 with heap := h' })
            | _ => some (.num 0, st1)
          else doCall st1 fn vs
  | .app fnExpr args => match evalJsExprStep doCall doApp st fnExpr with | none => none | some (fnVal, st1) => match evalJsExprListStep doCall doApp st1 args with | none => none | some (vs, st2) => doApp st2 fnVal vs

def evalJsExprListStep (doCall : JsCallFn) (doApp : JsAppFn) (st : JsState) : List JsExpr → Option (List JsVal × JsState)
  | [] => some ([], st) | e :: es => match evalJsExprStep doCall doApp st e with | none => none | some (v, st1) => match evalJsExprListStep doCall doApp st1 es with | none => none | some (vs, st2) => some (v :: vs, st2)
end

def evalJsAssignsStep (doCall : JsCallFn) (doApp : JsAppFn) (st : JsState) : List (String × JsExpr) → Option (List (String × JsVal) × JsState)
  | [] => some ([], st) | (k, e) :: rest => match evalJsExprStep doCall doApp st e with | none => none | some (v, st1) => match evalJsAssignsStep doCall doApp st1 rest with | none => none | some (ps, st2) => some ((k, v) :: ps, st2)

mutual
def evalJsStmtStep (doCall : JsCallFn) (doApp : JsAppFn) (st : JsState) : JsStmt → Option (BlockExit × JsState)
  | .letVar x e => match evalJsExprStep doCall doApp st e with | some (v, st1) => some (.next, { st1 with env := bindEnv st1.env x v }) | none => none
  | .letDecls _ => some (.next, st)
  | .letBinds binds => match evalJsAssignsStep doCall doApp st binds with | some (ps, st1) => some (.next, { st1 with env := bindMany ps st1.env }) | none => none
  | .labeledBlock lbl body => match evalJsStmtsStep doCall doApp st body with | some (.jumped l, st1) => some (if l == lbl then .next else .jumped l, st1) | res => res
  | .constArrow name ps body => some (.next, { st with fns := bindEnv st.fns name (some (ps, body, st.env)) })
  | .setField x i e => match evalJsExprStep doCall doApp st e with | some (val, st1) => some (.next, { st1 with env := bindEnv st1.env x ((st1.env x).setField i val) }) | none => none
  | .setTag x cidx => some (.next, { st with env := bindEnv st.env x ((st.env x).setTag cidx) })
  | .setU x i e => match evalJsExprStep doCall doApp st e with | some (val, st1) => some (.next, { st1 with env := bindEnv st1.env x ((st1.env x).setU i val) }) | none => none
  | .setS x n off e => match evalJsExprStep doCall doApp st e with | some (val, st1) => some (.next, { st1 with env := bindEnv st1.env x ((st1.env x).setS n off val) }) | none => none
  | .incRef x n => some (.next, { st with heap := st.heap.rcInc (st.env x).toRcVal n })
  | .decRef x n => some (.next, { st with heap := st.heap.rcDec (st.env x).toRcVal n })
  | .ret e => match evalJsExprStep doCall doApp st e with | some (v, st1) => some (.returned v, st1) | none => none
  | .tailContinue ps args => match evalJsExprListStep doCall doApp st args with | some (vs, st1) => some (.tailCont vs, { st1 with env := bindMany (ps.zip vs) st1.env }) | none => none
  | .breakLabel assigns lbl => match evalJsAssignsStep doCall doApp st assigns with | some (ps, st1) => some (.jumped lbl, { st1 with env := bindMany ps st1.env }) | none => none
  | .throwUnreachable => none
  | .switchStmt scrut arms => match evalJsExprStep doCall doApp st scrut with | some (sv, st1) => evalJsArmsStep doCall doApp st1 (jsTag sv) arms | none => none

def evalJsStmtsStep (doCall : JsCallFn) (doApp : JsAppFn) (st : JsState) : List JsStmt → Option (BlockExit × JsState)
  | [] => some (.next, st) | s :: ss => match evalJsStmtStep doCall doApp st s with | some (.next, st1) => evalJsStmtsStep doCall doApp st1 ss | res => res

def evalJsArmsStep (doCall : JsCallFn) (doApp : JsAppFn) (st : JsState) (tag : Nat) : List JsSwitchArm → Option (BlockExit × JsState)
  | [] => none | .caseArm c b :: rest => if c == tag then evalJsStmtsStep doCall doApp st b else evalJsArmsStep doCall doApp st tag rest | .defaultArm b :: _ => evalJsStmtsStep doCall doApp st b
end

def evalJsSelfTailStep (stmtsPrev : JsStmtsFn) (selfTailPrev : JsSelfTailFn) : JsSelfTailFn :=
  fun dl ps body st args =>
    match stmtsPrev { env := bindMany (ps.zip args) (fun _ => .num 0), heap := st.heap, memos := st.memos } body with
    | some (.tailCont nextArgs, st1) => if dl then selfTailPrev true ps body { st with heap := st1.heap, memos := st1.memos } nextArgs else none
    | some (.returned (.tc nextArgs), st1) => if dl then some (.tc nextArgs, { st with heap := st1.heap, memos := st1.memos }) else selfTailPrev false ps body { st with heap := st1.heap, memos := st1.memos } nextArgs
    | some (.returned v, st1) => some (v, { st with heap := st1.heap, memos := st1.memos }) | _ => none

def evalJsDeclStep (stmtsPrev : JsStmtsFn) (callPrev : JsCallFn) (selfTailCur : JsSelfTailFn)
    (st : JsState) (jd : JsDecl) (args : List JsVal) : Option (JsVal × JsState) :=
  match jd with
  | .fnPlain _ _ ps body => match stmtsPrev { env := bindMany (ps.zip args) (fun _ => .num 0), heap := st.heap, memos := st.memos } body with
      | some (.returned v, st1) => some (v, { st with heap := st1.heap, memos := st1.memos }) | _ => none
  | .fnDirectLoop _ _ ps body => selfTailCur true ps body st args
  | .fnTrampoline _ _ ps body => selfTailCur false ps body st args
  | .memoThunk name body => let cell := st.memos name; if cell.ok then some (cell.val.getD (.num 0), st)
      else match stmtsPrev { env := fun _ => .num 0, heap := st.heap, memos := st.memos } body with
        | some (.returned v, st1) => some (v, { st with heap := st1.heap, memos := fun k => if k == name then { ok := true, val := some v } else st1.memos k }) | _ => none
  | .memoInit name initName => let cell := st.memos name; if cell.ok then some (cell.val.getD (.num 0), st)
      else match callPrev st initName [] with | some (v, st1) => some (v, { st with heap := st1.heap, memos := fun k => if k == name then { ok := true, val := some v } else st1.memos k }) | none => none

def evalJsCallStep (prog : JsProg) (stmtsPrev : JsStmtsFn) (declCur : JsState → JsDecl → List JsVal → Option (JsVal × JsState)) : JsCallFn :=
  fun st fn args => match st.fns fn with
    | some (ps, body, capEnv) => match stmtsPrev { env := bindMany (ps.zip args) capEnv, heap := st.heap, fns := st.fns, memos := st.memos } body with
        | some (.returned v, st1) => some (v, { st with heap := st1.heap, memos := st1.memos }) | _ => none
    | none => match prog fn with | some jd => declCur st jd args | none => none

def evalJsAppStep (callCur : JsCallFn) (appPrev : JsAppFn) : JsAppFn :=
  fun st fnVal xs => match fnVal with
    | .pap fn arity acc => let rem := arity - acc.length
        if xs.length < rem then some (.pap fn arity (acc ++ xs), st) else if xs.length == rem then callCur st fn (acc ++ xs)
        else if rem == 0 then none else match callCur st fn (acc ++ xs.take rem) with | some (res, st1) => appPrev st1 res (xs.drop rem) | none => none
    | v => some (v, st)

def evalJsFuel (prog : JsProg) : Nat → JsCallFn × JsAppFn × JsSelfTailFn
  | 0 => (fun _ _ _ => none, fun _ _ _ => none, fun _ _ _ _ _ => none)
  | f + 1 =>
      let prev := evalJsFuel prog f
      let stmtsF := evalJsStmtsStep prev.1 prev.2.1
      let selfTailCur := evalJsSelfTailStep stmtsF prev.2.2
      let declCur := evalJsDeclStep stmtsF prev.1 selfTailCur
      let callCur := evalJsCallStep prog stmtsF declCur
      let appCur := evalJsAppStep callCur prev.2.1
      (callCur, appCur, selfTailCur)

def evalJsCall (prog : JsProg) (fuel : Nat) (st : JsState) (fn : String) (args : List JsVal) : Option (JsVal × JsState) := (evalJsFuel prog fuel).1 st fn args
def evalJsApp (prog : JsProg) (fuel : Nat) (st : JsState) (fnVal : JsVal) (xs : List JsVal) : Option (JsVal × JsState) := (evalJsFuel prog fuel).2.1 st fnVal xs
def evalJsSelfTail (dl : Bool) (prog : JsProg) (fuel : Nat) (ps : List String) (body : List JsStmt) (st : JsState) (args : List JsVal) : Option (JsVal × JsState) := (evalJsFuel prog fuel).2.2 dl ps body st args
def evalJsDecl (prog : JsProg) (fuel : Nat) (st : JsState) (jd : JsDecl) (args : List JsVal) : Option (JsVal × JsState) :=
  match fuel with | 0 => none | f + 1 => let p := evalJsFuel prog f; let ss := evalJsStmtsStep p.1 p.2.1; evalJsDeclStep ss p.1 (evalJsSelfTailStep ss p.2.2) st jd args
def evalJsStmts (prog : JsProg) (fuel : Nat) (st : JsState) (ss : List JsStmt) : Option (BlockExit × JsState) := evalJsStmtsStep (evalJsCall prog fuel) (evalJsApp prog fuel) st ss
def evalJsArms (prog : JsProg) (fuel : Nat) (st : JsState) (tag : Nat) (arms : List JsSwitchArm) : Option (BlockExit × JsState) := evalJsArmsStep (evalJsCall prog fuel) (evalJsApp prog fuel) st tag arms

theorem jdecl_inline_early_return_equiv (prog : JsProg) (fuel : Nat) (st st' : JsState) (j : JoinPointId) (preBody postBody : List JsStmt) (v : JsVal)
    (hret : evalJsStmts prog fuel st preBody = some (.returned v, st')) : evalJsStmts prog fuel st ([.labeledBlock (jp j) preBody] ++ postBody) = some (.returned v, st') := by
  dsimp only [List.cons_append, List.nil_append, evalJsStmts, evalJsStmtsStep, evalJsStmtStep]; rw [show evalJsStmtsStep (evalJsCall prog fuel) (evalJsApp prog fuel) st preBody = some (.returned v, st') from hret]
theorem jdecl_inline_jump_equiv (prog : JsProg) (fuel : Nat) (st st1 : JsState) (j : JoinPointId) (postBody preBody : List JsStmt)
    (hbrk : evalJsStmts prog fuel st preBody = some (.jumped (jp j), st1)) : evalJsStmts prog fuel st ([.labeledBlock (jp j) preBody] ++ postBody) = evalJsStmts prog fuel st1 postBody := by
  dsimp only [List.cons_append, List.nil_append, evalJsStmts, evalJsStmtsStep, evalJsStmtStep]; rw [show evalJsStmtsStep (evalJsCall prog fuel) (evalJsApp prog fuel) st preBody = some (.jumped (jp j), st1) from hbrk]; simp only [beq_self_eq_true, ↓reduceIte]

abbrev IrProg  := Name → Option Decl
abbrev IrJpMap := Nat → Option (Array Param × FnBody × (Nat → JsVal))
structure IrState where
  env : Nat → JsVal
  heap : CowHeap JsVal := {}
  jps : IrJpMap := fun _ => none
  memos : Name → MemoCell JsVal := fun _ => {}
inductive IrOutcome where | returned (v : JsVal) | jumped (j : JoinPointId) (args : List JsVal)
def evalIrArg (ρ : Nat → JsVal) : Arg → JsVal | .var x => ρ x.idx | .erased => .num 0
def refMarkArg (ρ : Nat → JsVal) : Arg → Option JsVal | .var x => some (ρ x.idx) | .erased => none
def evalIrCtor (ρ : Nat → JsVal) (i : CtorInfo) (ys : Array Arg) : JsVal :=
  if i.size == 0 && i.usize == 0 && i.ssize == 0 then .num i.cidx else .ctorObj i.cidx (ys.toList.map (evalIrArg ρ)) (i.ssize != 0) (i.usize != 0) [] []
def evalIrPure (c : Ctx) (ty : IRType) (ρ : Nat → JsVal) : IR.Expr → JsVal
  | .ctor i ys | .reuse _ i _ ys => evalIrCtor ρ i ys | .reset .. => .num 0
  | .proj i x => match ρ x.idx with | .ctorObj _ fs _ _ _ _ => fs.getD i (.num 0) | _ => .num 0
  | .uproj i x => match ρ x.idx with | .ctorObj _ _ _ _ u _ => assocGet i u | _ => .num 0
  | .sproj n off x => match ρ x.idx with | .ctorObj _ _ _ _ _ s => assocGet (n, off) s | _ => .num 0
  | .pap f ys => .pap (c.js f) ((findEnvDecl c.env f).map (·.params.size) |>.getD ys.size) (ys.toList.map (evalIrArg ρ))
  | .box _ x | .unbox x => ρ x.idx | .lit (.num n) => if ty.isObj || ty == .uint64 then .bigInt n else .num n | .lit (.str s) => .str s | _ => .num 0

abbrev IrCallFn   := CowHeap JsVal → (Name → MemoCell JsVal) → Name → List JsVal → Option (JsVal × CowHeap JsVal × (Name → MemoCell JsVal))
abbrev IrAppFn    := CowHeap JsVal → (Name → MemoCell JsVal) → JsVal → List JsVal → Option (JsVal × CowHeap JsVal × (Name → MemoCell JsVal))
abbrev IrRecJmpFn := IrState → JoinPointId → List JsVal → Option (IrOutcome × IrState)

mutual
def evalIrBodyStep (c : Ctx) (doCall : IrCallFn) (doApp : IrAppFn) (doRecJmp : IrRecJmpFn) (inlineJps : List Nat) (st : IrState) : FnBody → Option (IrOutcome × IrState)
  | .vdecl x ty e cont => match e with
      | .fap f ys => if f == `Qed.refMark then
            let (val, h') := match ys.toList.filterMap (refMarkArg st.env) with | [.arr id] => let (s, h') := st.heap.refMark id; (JsVal.num s, h') | _ => (JsVal.num 0, st.heap)
            evalIrBodyStep c doCall doApp doRecJmp inlineJps { st with env := fun k => if k == x.idx then val else st.env k, heap := h' } cont
          else match doCall st.heap st.memos f (ys.toList.map (evalIrArg st.env)) with
            | some (val, h', m') => evalIrBodyStep c doCall doApp doRecJmp inlineJps { st with env := fun k => if k == x.idx then val else st.env k, heap := h', memos := m' } cont | none => none
      | .ap y ys => match doApp st.heap st.memos (st.env y.idx) (ys.toList.map (evalIrArg st.env)) with
            | some (val, h', m') => evalIrBodyStep c doCall doApp doRecJmp inlineJps { st with env := fun k => if k == x.idx then val else st.env k, heap := h', memos := m' } cont | none => none
      | .isShared y => evalIrBodyStep c doCall doApp doRecJmp inlineJps { st with env := fun k => if k == x.idx then JsVal.num (if isSharedVal st.heap (st.env y.idx) then 1 else 0) else st.env k } cont
      | _ => evalIrBodyStep c doCall doApp doRecJmp inlineJps { st with env := fun k => if k == x.idx then evalIrPure c ty st.env e else st.env k } cont
  | .jdecl j xs val cont => if !hasJmpTo j val then match evalIrBodyStep c doCall doApp doRecJmp (j.idx :: inlineJps) st cont with
        | some (.jumped j' args, st1) => if j' == j then evalIrBodyStep c doCall doApp doRecJmp inlineJps { st1 with env := bindIrParams xs args st1.env } val else some (.jumped j' args, st1) | res => res
      else evalIrBodyStep c doCall doApp doRecJmp inlineJps { st with jps := fun k => if k == j.idx then some (xs, val, st.env) else st.jps k } cont
  | .set x i y cont => evalIrBodyStep c doCall doApp doRecJmp inlineJps { st with env := fun k => if k == x.idx then (st.env x.idx).setField i (evalIrArg st.env y) else st.env k } cont
  | .setTag x cidx cont => evalIrBodyStep c doCall doApp doRecJmp inlineJps { st with env := fun k => if k == x.idx then (st.env x.idx).setTag cidx else st.env k } cont
  | .uset x i y cont => evalIrBodyStep c doCall doApp doRecJmp inlineJps { st with env := fun k => if k == x.idx then (st.env x.idx).setU i (st.env y.idx) else st.env k } cont
  | .sset x n off y _ cont => evalIrBodyStep c doCall doApp doRecJmp inlineJps { st with env := fun k => if k == x.idx then (st.env x.idx).setS n off (st.env y.idx) else st.env k } cont
  | .inc x n _ _ cont => evalIrBodyStep c doCall doApp doRecJmp inlineJps { st with heap := st.heap.rcInc (st.env x.idx).toRcVal n } cont
  | .dec x n _ _ cont => evalIrBodyStep c doCall doApp doRecJmp inlineJps { st with heap := st.heap.rcDec (st.env x.idx).toRcVal n } cont
  | .del x cont => evalIrBodyStep c doCall doApp doRecJmp inlineJps { st with heap := st.heap.rcDec (st.env x.idx).toRcVal 1 } cont
  | .ret a => some (.returned (evalIrArg st.env a), st)
  | .jmp j ys => let args := ys.toList.map (evalIrArg st.env); if j.idx ∈ inlineJps then some (.jumped j args, st) else doRecJmp st j args
  | .unreachable => none
  | .case _ x _ alts => evalIrAltsStep c doCall doApp doRecJmp inlineJps st (jsTag (st.env x.idx)) alts.toList

def evalIrAltsStep (c : Ctx) (doCall : IrCallFn) (doApp : IrAppFn) (doRecJmp : IrRecJmpFn) (inlineJps : List Nat) (st : IrState) (tag : Nat) : List Alt → Option (IrOutcome × IrState)
  | [] => none | .ctor info b :: rest => if info.cidx == tag then evalIrBodyStep c doCall doApp doRecJmp inlineJps st b else evalIrAltsStep c doCall doApp doRecJmp inlineJps st tag rest
  | .default b :: _ => evalIrBodyStep c doCall doApp doRecJmp inlineJps st b
end

def evalIrCallStep (prog : IrProg) (c : Ctx) (callPrev : IrCallFn) (bodyPrev : List Nat → IrState → FnBody → Option (IrOutcome × IrState)) : IrCallFn :=
  fun h memos f args => match prog f with
    | some (.fdecl _ xs _ body _) => if xs.isEmpty then
          let cell := memos f; if cell.ok then some (cell.val.getD (.num 0), h, memos)
          else match getInitFnNameFor? c.env f with
            | some initFn => match callPrev h memos initFn [] with | some (v, h', m') => some (v, h', fun k => if k == f then { ok := true, val := some v } else m' k) | none => none
            | none => match bodyPrev [] { env := fun _ => .num 0, heap := h, memos := memos } body with
                | some (.returned v, st1) => some (v, st1.heap, fun k => if k == f then { ok := true, val := some v } else st1.memos k) | _ => none
        else match bodyPrev [] { env := bindIrParams xs args (fun _ => .num 0), heap := h, memos := memos } body with
            | some (.returned v, st1) => some (v, st1.heap, st1.memos) | _ => none
    | _ => none

def evalIrAppStep (revName : String → Option Name) (callCur : IrCallFn) (appPrev : IrAppFn) : IrAppFn :=
  fun h memos fnVal xs => match fnVal with
    | .pap fnStr arity acc => let rem := arity - acc.length
        if xs.length < rem then some (.pap fnStr arity (acc ++ xs), h, memos)
        else match revName fnStr with
        | none => none
        | some fn =>
            if xs.length == rem then callCur h memos fn (acc ++ xs) else if rem == 0 then none
            else match callCur h memos fn (acc ++ xs.take rem) with | some (res, h', m') => appPrev h' m' res (xs.drop rem) | none => none
    | v => some (v, h, memos)

def evalIrRecJmpStep (bodyPrev : List Nat → IrState → FnBody → Option (IrOutcome × IrState)) : IrRecJmpFn :=
  fun st j args => match st.jps j.idx with
    | none => none
    | some (xs, val, capEnv) => match bodyPrev [] { env := bindIrParams xs args capEnv, heap := st.heap, jps := st.jps, memos := st.memos } val with
        | some (.returned v, st1) => some (.returned v, { st with heap := st1.heap, memos := st1.memos })
        | _ => none

def evalIrFuel (prog : IrProg) (c : Ctx) (revName : String → Option Name) : Nat → IrCallFn × IrAppFn × IrRecJmpFn
  | 0 => (fun _ _ _ _ => none, fun _ _ _ _ => none, fun _ _ _ => none)
  | f' + 1 =>
      let prev := evalIrFuel prog c revName f'
      let bodyPrev := evalIrBodyStep c prev.1 prev.2.1 prev.2.2
      let callCur := evalIrCallStep prog c prev.1 bodyPrev
      let appCur := evalIrAppStep revName callCur prev.2.1
      let recJmpCur := evalIrRecJmpStep bodyPrev
      (callCur, appCur, recJmpCur)

def evalIrCall (prog : IrProg) (c : Ctx) (revName : String → Option Name) (fuel : Nat) (h : CowHeap JsVal) (memos : Name → MemoCell JsVal) (f : Name) (args : List JsVal) : Option (JsVal × CowHeap JsVal × (Name → MemoCell JsVal)) := (evalIrFuel prog c revName fuel).1 h memos f args
def evalIrApp (prog : IrProg) (c : Ctx) (revName : String → Option Name) (fuel : Nat) (h : CowHeap JsVal) (memos : Name → MemoCell JsVal) (fnVal : JsVal) (xs : List JsVal) : Option (JsVal × CowHeap JsVal × (Name → MemoCell JsVal)) := (evalIrFuel prog c revName fuel).2.1 h memos fnVal xs
def evalIrBody (prog : IrProg) (c : Ctx) (revName : String → Option Name) (inlineJps : List Nat) (fuel : Nat) (st : IrState) (b : FnBody) : Option (IrOutcome × IrState) := evalIrBodyStep c (evalIrCall prog c revName fuel) (evalIrApp prog c revName fuel) (evalIrFuel prog c revName fuel).2.2 inlineJps st b
def evalIrAlts (prog : IrProg) (c : Ctx) (revName : String → Option Name) (inlineJps : List Nat) (fuel : Nat) (st : IrState) (tag : Nat) (alts : List Alt) : Option (IrOutcome × IrState) := evalIrAltsStep c (evalIrCall prog c revName fuel) (evalIrApp prog c revName fuel) (evalIrFuel prog c revName fuel).2.2 inlineJps st tag alts

/-! ### Helper Lemmas (Frame, Pure Expression Lowering, Join-Point Binders, `noTc`) -/

section ExprSteps
variable {doCall : JsCallFn} {doApp : JsAppFn} {st : JsState} {ρ : Nat → JsVal}
theorem evalJsExprStep_lowerArg (hm : ∀ w : VarId, ρ w.idx = st.env (v w)) (a : Arg) :
    evalJsExprStep doCall doApp st (lowerArg a) = some (evalIrArg ρ a, st) := by
  cases a with | var x => exact congrArg (fun u => some (u, st)) (hm x).symm | erased => rfl
theorem evalJsExprListStep_lowerArgs (hm : ∀ w : VarId, ρ w.idx = st.env (v w)) :
    ∀ as : List Arg, evalJsExprListStep doCall doApp st (as.map lowerArg) = some (as.map (evalIrArg ρ), st)
  | [] => rfl
  | a :: rest => by dsimp only [List.map, evalJsExprListStep]; rw [evalJsExprStep_lowerArg hm a]; dsimp only; rw [evalJsExprListStep_lowerArgs hm rest]
private theorem evalJsExprListStep_refMark (hm : ∀ w : VarId, ρ w.idx = st.env (v w)) (f : Arg → Option JsExpr) (hf : ∀ a, f a = match a with | .var x => some (.var (v x)) | .erased => none) :
    ∀ as : List Arg, evalJsExprListStep doCall doApp st (as.filterMap f) = some (as.filterMap (refMarkArg ρ), st)
  | [] => rfl
  | .erased :: rest => by dsimp only [List.filterMap, refMarkArg]; rw [hf .erased]; exact evalJsExprListStep_refMark hm f hf rest
  | .var x :: rest => by dsimp only [List.filterMap, refMarkArg]; rw [hf (.var x)]; dsimp only [evalJsExprListStep, evalJsExprStep]; rw [hm x, evalJsExprListStep_refMark hm f hf rest]
private theorem evalJsExprStep_lowerCtor (hm : ∀ w : VarId, ρ w.idx = st.env (v w)) (i : CtorInfo) (ys : Array Arg) :
    evalJsExprStep doCall doApp st (lowerCtor i ys) = some (evalIrCtor ρ i ys, st) := by
  dsimp only [lowerCtor, evalIrCtor]; split; rfl; dsimp only [evalJsExprStep]; rw [evalJsExprListStep_lowerArgs hm ys.toList]
private theorem evalJsExprStep_lowerPure (c : Ctx) (ty : IRType) (hm : ∀ w : VarId, ρ w.idx = st.env (v w)) (e : IR.Expr) (hpure : match e with | .fap .. | .ap .. | .isShared .. => False | _ => True) :
    evalJsExprStep doCall doApp st (lowerExpr c ty e) = some (evalIrPure c ty ρ e, st) := by
  cases e with
  | ctor i ys | reuse _ i _ ys => exact evalJsExprStep_lowerCtor hm i ys
  | reset _ _ => rfl
  | proj _ x | uproj _ x | sproj _ _ x => dsimp only [lowerExpr, evalJsExprStep, evalIrPure]; rw [hm x]; cases st.env (v x) <;> rfl
  | pap _ ys => dsimp only [lowerExpr, evalJsExprStep, evalIrPure]; rw [evalJsExprListStep_lowerArgs hm ys.toList]
  | box _ x | unbox x => exact congrArg (fun u => some (u, st)) (hm x).symm
  | lit lv => cases lv with | num _ => dsimp only [lowerExpr, evalIrPure]; split <;> rfl | str _ => rfl
  | fap _ _ | ap _ _ | isShared _ => exact False.elim hpure
private theorem evalJsExprStep_call_jp (j : JoinPointId) (es : List JsExpr) :
    evalJsExprStep doCall doApp st (.call (jp j) es) = match evalJsExprListStep doCall doApp st es with | some (vals, st1) => doCall st1 (jp j) vals | none => none := by
  dsimp only [evalJsExprStep]; cases evalJsExprListStep doCall doApp st es with | none => rfl | some _ =>
    have hne : ∀ s : String, s.toByteArray.data.toList.head? = some 36 → (jp j == s) = false := fun s hs => beq_false_of_ne fun h => by
      have h0 : (jp j).toByteArray.data.toList.head? = s.toByteArray.data.toList.head? := congrArg (fun x => x.toByteArray.data.toList.head?) h
      rw [hs] at h0; dsimp only [jp] at h0; rw [toString_str_eq, String.toByteArray_append, ByteArray.data_append, Array.toList_append] at h0
      have hj : "j".toByteArray.data.toList = [106] := rfl; rw [hj] at h0; cases h0
    rw [hne "$.tag" rfl, hne "$.isShared" rfl, hne "$.refMark" rfl]; rfl
end ExprSteps
theorem match_next_idem (r : Option (BlockExit × JsState)) : (match r with | some (.next, st1) => some (.next, st1) | res => res) = r := by
  cases r with | none => rfl | some p => rcases p with ⟨ex, _⟩; cases ex <;> rfl

local macro "mono_opt" hr:ident ":" e:term " with " h:term : tactic =>
  `(tactic| (cases h1 : $e; · rw [h1] at $hr:ident; cases $hr:term
             rw [h1] at $hr:ident; rw [$h h1]; clear h1; rename_i p $hr:ident; rcases p with ⟨_, _⟩; try dsimp only at $hr:ident ⊢))
local macro "mono_ite" hr:ident ":" c:term : tactic =>
  `(tactic| (by_cases hc : $c <;> first | rw [if_pos hc] at $hr:ident ⊢ | rw [if_neg hc] at $hr:ident ⊢))

section IrMono
variable (c : Ctx) {doCall₁ doCall₂ : IrCallFn} {doApp₁ doApp₂ : IrAppFn} {doRec₁ doRec₂ : IrRecJmpFn}
  (hCall : ∀ {h m f args r}, doCall₁ h m f args = some r → doCall₂ h m f args = some r)
  (hApp : ∀ {h m fv args r}, doApp₁ h m fv args = some r → doApp₂ h m fv args = some r)
  (hRec : ∀ {st j args r}, doRec₁ st j args = some r → doRec₂ st j args = some r)
include hCall hApp hRec
mutual
private theorem evalIrBodyStep_mono : ∀ {b : FnBody} {ij : List Nat} {st : IrState} {r : IrOutcome × IrState},
    evalIrBodyStep c doCall₁ doApp₁ doRec₁ ij st b = some r → evalIrBodyStep c doCall₂ doApp₂ doRec₂ ij st b = some r
  | .ret _, _, _, _, hr => hr | .unreachable, _, _, _, hr => nomatch hr
  | .set _ _ _ cont, _, _, _, hr | .setTag _ _ cont, _, _, _, hr | .uset _ _ _ cont, _, _, _, hr | .sset _ _ _ _ _ cont, _, _, _, hr
  | .inc _ _ _ _ cont, _, _, _, hr | .dec _ _ _ _ cont, _, _, _, hr | .del _ cont, _, _, _, hr => evalIrBodyStep_mono (b := cont) hr
  | .vdecl _ _ e cont, _, _, _, hr => by
      cases e with
      | fap f _ => dsimp only [evalIrBodyStep] at hr ⊢; mono_ite hr : (f == `Qed.refMark) = true; · exact evalIrBodyStep_mono (b := cont) hr
                   mono_opt hr : doCall₁ _ _ f _ with hCall; exact evalIrBodyStep_mono (b := cont) hr
      | ap _ _ => dsimp only [evalIrBodyStep] at hr ⊢; mono_opt hr : doApp₁ _ _ _ _ with hApp; exact evalIrBodyStep_mono (b := cont) hr
      | _ => exact evalIrBodyStep_mono (b := cont) hr
  | .jdecl j _ val cont, _, _, _, hr => by
      dsimp only [evalIrBodyStep] at hr ⊢; mono_ite hr : (!hasJmpTo j val) = true
      · mono_opt hr : evalIrBodyStep c doCall₁ doApp₁ doRec₁ _ _ cont with evalIrBodyStep_mono (b := cont)
        rename_i irO' _; cases irO' with | returned _ => exact hr | jumped j' _ => dsimp only at hr ⊢; mono_ite hr : (j' == j) = true; exact evalIrBodyStep_mono (b := val) hr; exact hr
      · exact evalIrBodyStep_mono (b := cont) hr
  | .jmp j _, ij, _, _, hr => by dsimp only [evalIrBodyStep] at hr ⊢; mono_ite hr : j.idx ∈ ij; exact hr; exact hRec hr
  | .case _ _ _ alts, _, _, _, hr => evalIrAltsStep_mono (alts := alts.toList) hr
private theorem evalIrAltsStep_mono : ∀ {alts : List Alt} {ij : List Nat} {st : IrState} {tag : Nat} {r : IrOutcome × IrState},
    evalIrAltsStep c doCall₁ doApp₁ doRec₁ ij st tag alts = some r → evalIrAltsStep c doCall₂ doApp₂ doRec₂ ij st tag alts = some r
  | [], _, _, _, _, hr => nomatch hr
  | .ctor info b :: rest, _, _, tag, _, hr => by
      have _ := @hCall; have _ := @hApp; have _ := @hRec
      dsimp only [evalIrAltsStep] at hr ⊢; mono_ite hr : (info.cidx == tag) = true; exact evalIrBodyStep_mono (b := b) hr; exact evalIrAltsStep_mono (alts := rest) hr
  | .default b :: _, _, _, _, _, hr => evalIrBodyStep_mono (b := b) hr
end
end IrMono

theorem evalIrCall_succ (prog : IrProg) (c : Ctx) (revName : String → Option Name) (f' : Nat) (h : CowHeap JsVal) (memos : Name → MemoCell JsVal) (f : Name) (args : List JsVal) : evalIrCall prog c revName (f' + 1) h memos f args = evalIrCallStep prog c (evalIrCall prog c revName f') (fun ij st b => evalIrBody prog c revName ij f' st b) h memos f args := rfl
theorem evalIrApp_succ (prog : IrProg) (c : Ctx) (revName : String → Option Name) (f' : Nat) (h : CowHeap JsVal) (memos : Name → MemoCell JsVal) (fnVal : JsVal) (xs : List JsVal) : evalIrApp prog c revName (f' + 1) h memos fnVal xs = evalIrAppStep revName (evalIrCall prog c revName (f' + 1)) (evalIrApp prog c revName f') h memos fnVal xs := rfl
private theorem evalIrRecJmp_succ (prog : IrProg) (c : Ctx) (revName : String → Option Name) (f' : Nat) (st : IrState) (j : JoinPointId) (args : List JsVal) : (evalIrFuel prog c revName (f' + 1)).2.2 st j args = evalIrRecJmpStep (fun ij st b => evalIrBody prog c revName ij f' st b) st j args := rfl

private theorem evalIr_mono_succ (prog : IrProg) (c : Ctx) (revName : String → Option Name) : ∀ fuel : Nat,
    (∀ {h memos f args r}, evalIrCall prog c revName fuel h memos f args = some r → evalIrCall prog c revName (fuel + 1) h memos f args = some r) ∧
    (∀ {h memos fnVal xs r}, evalIrApp prog c revName fuel h memos fnVal xs = some r → evalIrApp prog c revName (fuel + 1) h memos fnVal xs = some r) ∧
    (∀ {st j args r}, (evalIrFuel prog c revName fuel).2.2 st j args = some r → (evalIrFuel prog c revName (fuel + 1)).2.2 st j args = some r) ∧
    (∀ {inlineJps st b r}, evalIrBody prog c revName inlineJps fuel st b = some r → evalIrBody prog c revName inlineJps (fuel + 1) st b = some r)
  | 0 => ⟨(fun hr => nomatch hr), (fun hr => nomatch hr), (fun hr => nomatch hr), fun hr => evalIrBodyStep_mono c (fun h => by cases h) (fun h => by cases h) (fun h => by cases h) hr⟩
  | f' + 1 => by
      obtain ⟨ihCall, ihApp, _, ihBody⟩ := evalIr_mono_succ prog c revName f'
      have hCall : ∀ {h memos f args r}, evalIrCall prog c revName (f' + 1) h memos f args = some r → evalIrCall prog c revName (f' + 2) h memos f args = some r := by
        intro h memos f args r hr; rw [evalIrCall_succ] at hr ⊢; dsimp only [evalIrCallStep] at hr ⊢
        cases hp : prog f with | none => rw [hp] at hr; cases hr | some d => cases d with | extern _ _ _ _ => rw [hp] at hr; cases hr | fdecl _ xs _ b _ =>
          rw [hp] at hr; dsimp only at hr ⊢; mono_ite hr : xs.isEmpty = true
          · mono_ite hr : (memos f).ok = true; · exact hr
            cases hini : getInitFnNameFor? c.env f with
            | some ini => rw [hini] at hr; dsimp only at hr ⊢; mono_opt hr : evalIrCall prog c revName f' h memos ini [] with ihCall; exact hr
            | none => rw [hini] at hr; dsimp only at hr ⊢; mono_opt hr : evalIrBody prog c revName [] f' _ b with ihBody; exact hr
          · mono_opt hr : evalIrBody prog c revName [] f' _ b with ihBody; exact hr
      have hApp : ∀ {h memos fnVal xs r}, evalIrApp prog c revName (f' + 1) h memos fnVal xs = some r → evalIrApp prog c revName (f' + 2) h memos fnVal xs = some r := by
        intro h memos fnVal xs r hr; rw [evalIrApp_succ] at hr ⊢; dsimp only [evalIrAppStep] at hr ⊢; cases fnVal with
        | pap fnStr ar acc =>
          dsimp only at hr ⊢; mono_ite hr : xs.length < ar - acc.length; · exact hr
          cases hrev : revName fnStr with | none => rw [hrev] at hr; cases hr | some fn =>
            rw [hrev] at hr; dsimp only at hr ⊢; mono_ite hr : (xs.length == ar - acc.length) = true; · exact hCall hr
            mono_ite hr : (ar - acc.length == 0) = true; · cases hr
            mono_opt hr : evalIrCall prog c revName (f' + 1) h memos fn _ with hCall; exact ihApp hr
        | _ => exact hr
      have hRec : ∀ {st j args r}, (evalIrFuel prog c revName (f' + 1)).2.2 st j args = some r → (evalIrFuel prog c revName (f' + 2)).2.2 st j args = some r := by
        intro st j args r hr; rw [evalIrRecJmp_succ] at hr ⊢; dsimp only [evalIrRecJmpStep] at hr ⊢
        cases hj : st.jps j.idx with | none => rw [hj] at hr; cases hr | some jd => rw [hj] at hr; dsimp only at hr ⊢; mono_opt hr : evalIrBody prog c revName [] f' _ jd.2.1 with ihBody; exact hr
      exact ⟨hCall, hApp, hRec, fun hr => evalIrBodyStep_mono c hCall hApp hRec hr⟩

theorem evalIrCall_mono {prog c revName f₁ f₂ h memos f args r} (hle : f₁ ≤ f₂) (hr : evalIrCall prog c revName f₁ h memos f args = some r) : evalIrCall prog c revName f₂ h memos f args = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalIr_mono_succ prog c revName _).1 ih
theorem evalIrApp_mono {prog c revName f₁ f₂ h memos fnVal args r} (hle : f₁ ≤ f₂) (hr : evalIrApp prog c revName f₁ h memos fnVal args = some r) : evalIrApp prog c revName f₂ h memos fnVal args = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalIr_mono_succ prog c revName _).2.1 ih
theorem evalIrBody_mono {prog c revName inlineJps f₁ f₂ st b r} (hle : f₁ ≤ f₂) (hr : evalIrBody prog c revName inlineJps f₁ st b = some r) : evalIrBody prog c revName inlineJps f₂ st b = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalIr_mono_succ prog c revName _).2.2.2 ih

section JsMono
variable {c1 c2 : JsCallFn} {a1 a2 : JsAppFn}
  (hCall : ∀ {st fn args r}, c1 st fn args = some r → c2 st fn args = some r)
  (hApp : ∀ {st fnVal args r}, a1 st fnVal args = some r → a2 st fnVal args = some r)
include hCall hApp
mutual
private theorem evalJsExprStep_mono : ∀ {e : JsExpr} {st : JsState} {r : JsVal × JsState}, evalJsExprStep c1 a1 st e = some r → evalJsExprStep c2 a2 st e = some r
  | .var _, _, _, hr | .numLit _, _, _, hr | .bigIntLit _, _, _, hr | .strLit _, _, _, hr | .arrLit _, _, _, hr => hr
  | .ctorObj _ fs _ _, st, _, hr | .pap _ _ fs, st, _, hr | .tc fs, st, _, hr => by dsimp only [evalJsExprStep] at hr ⊢; mono_opt hr : evalJsExprListStep c1 a1 st fs with evalJsExprListStep_mono (es := fs); exact hr
  | .fieldProj o _, st, _, hr | .uProj o _, st, _, hr | .sProj o _ _, st, _, hr => by dsimp only [evalJsExprStep] at hr ⊢; mono_opt hr : evalJsExprStep c1 a1 st o with evalJsExprStep_mono (e := o); exact hr
  | .call fn args, st, _, hr => by
      dsimp only [evalJsExprStep] at hr ⊢; mono_opt hr : evalJsExprListStep c1 a1 st args with evalJsExprListStep_mono (es := args); rename_i vs _
      mono_ite hr : (fn == "$.tag") = true; · cases vs with | nil => exact hCall hr | cons _ t => cases t with | nil => exact hr | cons _ _ => exact hCall hr
      mono_ite hr : (fn == "$.isShared") = true; · cases vs with | nil => exact hCall hr | cons _ t => cases t with | nil => exact hr | cons _ _ => exact hCall hr
      mono_ite hr : (fn == "$.refMark") = true; · exact hr
      exact hCall hr
  | .app fnExpr args, st, _, hr => by dsimp only [evalJsExprStep] at hr ⊢; mono_opt hr : evalJsExprStep c1 a1 st fnExpr with evalJsExprStep_mono (e := fnExpr); mono_opt hr : evalJsExprListStep c1 a1 _ args with evalJsExprListStep_mono (es := args); exact hApp hr
private theorem evalJsExprListStep_mono : ∀ {es : List JsExpr} {st : JsState} {r : List JsVal × JsState}, evalJsExprListStep c1 a1 st es = some r → evalJsExprListStep c2 a2 st es = some r
  | [], _, _, hr => hr
  | e :: es, st, _, hr => by have _ := @hCall; have _ := @hApp; dsimp only [evalJsExprListStep] at hr ⊢; mono_opt hr : evalJsExprStep c1 a1 st e with evalJsExprStep_mono (e := e); mono_opt hr : evalJsExprListStep c1 a1 _ es with evalJsExprListStep_mono (es := es); exact hr
end
private theorem evalJsAssignsStep_mono : ∀ {ps : List (String × JsExpr)} {st : JsState} {r : List (String × JsVal) × JsState}, evalJsAssignsStep c1 a1 st ps = some r → evalJsAssignsStep c2 a2 st ps = some r
  | [], _, _, hr => hr
  | (_, e) :: rest, st, _, hr => by dsimp only [evalJsAssignsStep] at hr ⊢; mono_opt hr : evalJsExprStep c1 a1 st e with evalJsExprStep_mono hCall hApp (e := e); mono_opt hr : evalJsAssignsStep c1 a1 _ rest with evalJsAssignsStep_mono (ps := rest); exact hr
mutual
private theorem evalJsStmtStep_mono : ∀ {s : JsStmt} {st : JsState} {r : BlockExit × JsState}, evalJsStmtStep c1 a1 st s = some r → evalJsStmtStep c2 a2 st s = some r
  | .letDecls _, _, _, hr | .constArrow _ _ _, _, _, hr | .setTag _ _, _, _, hr | .incRef _ _, _, _, hr | .decRef _ _, _, _, hr => hr
  | .throwUnreachable, _, _, hr => nomatch hr
  | .letVar _ e, st, _, hr | .setField _ _ e, st, _, hr | .setU _ _ e, st, _, hr | .setS _ _ _ e, st, _, hr | .ret e, st, _, hr => by dsimp only [evalJsStmtStep] at hr ⊢; mono_opt hr : evalJsExprStep c1 a1 st e with evalJsExprStep_mono hCall hApp (e := e); exact hr
  | .letBinds ps, st, _, hr | .breakLabel ps _, st, _, hr => by dsimp only [evalJsStmtStep] at hr ⊢; mono_opt hr : evalJsAssignsStep c1 a1 st ps with evalJsAssignsStep_mono hCall hApp (ps := ps); exact hr
  | .tailContinue _ es, st, _, hr => by dsimp only [evalJsStmtStep] at hr ⊢; mono_opt hr : evalJsExprListStep c1 a1 st es with evalJsExprListStep_mono hCall hApp (es := es); exact hr
  | .labeledBlock _ ss, st, _, hr => by dsimp only [evalJsStmtStep] at hr ⊢; mono_opt hr : evalJsStmtsStep c1 a1 st ss with evalJsStmtsStep_mono (ss := ss); exact hr
  | .switchStmt scrut arms, st, _, hr => by dsimp only [evalJsStmtStep] at hr ⊢; mono_opt hr : evalJsExprStep c1 a1 st scrut with evalJsExprStep_mono hCall hApp (e := scrut); exact evalJsArmsStep_mono (arms := arms) hr
private theorem evalJsStmtsStep_mono : ∀ {ss : List JsStmt} {st : JsState} {r : BlockExit × JsState}, evalJsStmtsStep c1 a1 st ss = some r → evalJsStmtsStep c2 a2 st ss = some r
  | [], _, _, hr => hr
  | s :: ss, st, _, hr => by have _ := @hCall; have _ := @hApp; dsimp only [evalJsStmtsStep] at hr ⊢; mono_opt hr : evalJsStmtStep c1 a1 st s with evalJsStmtStep_mono (s := s); rename_i ex' _; cases ex' with | next => exact evalJsStmtsStep_mono (ss := ss) hr | _ => exact hr
private theorem evalJsArmsStep_mono : ∀ {arms : List JsSwitchArm} {st : JsState} {tag : Nat} {r : BlockExit × JsState}, evalJsArmsStep c1 a1 st tag arms = some r → evalJsArmsStep c2 a2 st tag arms = some r
  | [], _, _, _, hr => nomatch hr
  | .caseArm c b :: rest, _, tag, _, hr => by have _ := @hCall; have _ := @hApp; dsimp only [evalJsArmsStep] at hr ⊢; mono_ite hr : (c == tag) = true; exact evalJsStmtsStep_mono (ss := b) hr; exact evalJsArmsStep_mono (arms := rest) hr
  | .defaultArm b :: _, _, _, _, hr => evalJsStmtsStep_mono (ss := b) hr
end
end JsMono

theorem evalJsSelfTail_succ (dl : Bool) (prog : JsProg) (f' : Nat) (ps : List String) (body : List JsStmt) (st : JsState) (args : List JsVal) : evalJsSelfTail dl prog (f' + 1) ps body st args = evalJsSelfTailStep (evalJsStmts prog f') (fun dl' => evalJsSelfTail dl' prog f') dl ps body st args := rfl
theorem evalJsDecl_succ (prog : JsProg) (f' : Nat) (st : JsState) (jd : JsDecl) (args : List JsVal) : evalJsDecl prog (f' + 1) st jd args = evalJsDeclStep (evalJsStmts prog f') (evalJsCall prog f') (fun dl' => evalJsSelfTail dl' prog (f' + 1)) st jd args := rfl
theorem evalJsCall_succ (prog : JsProg) (f' : Nat) (st : JsState) (fn : String) (args : List JsVal) : evalJsCall prog (f' + 1) st fn args = evalJsCallStep prog (evalJsStmts prog f') (evalJsDecl prog (f' + 1)) st fn args := rfl
theorem evalJsApp_succ (prog : JsProg) (f' : Nat) (st : JsState) (fnVal : JsVal) (xs : List JsVal) : evalJsApp prog (f' + 1) st fnVal xs = evalJsAppStep (evalJsCall prog (f' + 1)) (evalJsApp prog f') st fnVal xs := rfl

private theorem evalJs_mono_succ (prog : JsProg) : ∀ fuel : Nat,
    (∀ {st fn args r}, evalJsCall prog fuel st fn args = some r → evalJsCall prog (fuel + 1) st fn args = some r) ∧
    (∀ {st fnVal xs r}, evalJsApp prog fuel st fnVal xs = some r → evalJsApp prog (fuel + 1) st fnVal xs = some r) ∧
    (∀ {ss st r}, evalJsStmts prog fuel st ss = some r → evalJsStmts prog (fuel + 1) st ss = some r) ∧
    (∀ {dl ps body st args r}, evalJsSelfTail dl prog fuel ps body st args = some r → evalJsSelfTail dl prog (fuel + 1) ps body st args = some r)
  | 0 => ⟨(fun hr => nomatch hr), (fun hr => nomatch hr), fun hr => evalJsStmtsStep_mono (fun h => by cases h) (fun h => by cases h) hr, (fun hr => nomatch hr)⟩
  | f' + 1 => by
      obtain ⟨ihCall, ihApp, ihStmts, ihST⟩ := evalJs_mono_succ prog f'
      have hST : ∀ {dl ps body st args r}, evalJsSelfTail dl prog (f' + 1) ps body st args = some r → evalJsSelfTail dl prog (f' + 2) ps body st args = some r := by
        intro dl ps body st args r hr; rw [evalJsSelfTail_succ] at hr ⊢; dsimp only [evalJsSelfTailStep] at hr ⊢; mono_opt hr : evalJsStmts prog f' _ body with ihStmts
        rename_i ex' _; cases ex' with
        | tailCont _ => cases dl <;> (first | cases hr | exact ihST hr)
        | returned v => cases v with | tc _ => cases dl <;> (first | exact hr | exact ihST hr) | _ => exact hr
        | _ => cases hr
      have hCall : ∀ {st fn args r}, evalJsCall prog (f' + 1) st fn args = some r → evalJsCall prog (f' + 2) st fn args = some r := by
        intro st fn args r hr; rw [evalJsCall_succ] at hr ⊢; dsimp only [evalJsCallStep] at hr ⊢
        cases hfn : st.fns fn with
        | some _ => rw [hfn] at hr; dsimp only at hr ⊢; mono_opt hr : evalJsStmts prog f' _ _ with ihStmts; exact hr
        | none => rw [hfn] at hr; dsimp only at hr ⊢; cases hp : prog fn with | none => rw [hp] at hr; cases hr | some jd =>
          rw [hp] at hr; dsimp only at hr ⊢; rw [evalJsDecl_succ] at hr ⊢; cases jd with
          | fnPlain _ _ _ _ => dsimp only [evalJsDeclStep] at hr ⊢; mono_opt hr : evalJsStmts prog f' _ _ with ihStmts; exact hr
          | fnDirectLoop _ _ _ _ | fnTrampoline _ _ _ _ => exact hST hr
          | memoThunk nm _ => dsimp only [evalJsDeclStep] at hr ⊢; mono_ite hr : (st.memos nm).ok = true; · exact hr
                              mono_opt hr : evalJsStmts prog f' _ _ with ihStmts; exact hr
          | memoInit nm _ => dsimp only [evalJsDeclStep] at hr ⊢; mono_ite hr : (st.memos nm).ok = true; · exact hr
                             mono_opt hr : evalJsCall prog f' st _ [] with ihCall; exact hr
      have hApp : ∀ {st fnVal xs r}, evalJsApp prog (f' + 1) st fnVal xs = some r → evalJsApp prog (f' + 2) st fnVal xs = some r := by
        intro st fnVal xs r hr; rw [evalJsApp_succ] at hr ⊢; dsimp only [evalJsAppStep] at hr ⊢; cases fnVal with
        | pap _ ar acc =>
          dsimp only at hr ⊢; mono_ite hr : xs.length < ar - acc.length; · exact hr
          mono_ite hr : (xs.length == ar - acc.length) = true; · exact hCall hr
          mono_ite hr : (ar - acc.length == 0) = true; · cases hr
          mono_opt hr : evalJsCall prog (f' + 1) st _ _ with hCall; exact ihApp hr
        | _ => exact hr
      exact ⟨hCall, hApp, fun hr => evalJsStmtsStep_mono hCall hApp hr, hST⟩

theorem evalJsCall_mono {prog f₁ f₂ st fn args r} (hle : f₁ ≤ f₂) (hr : evalJsCall prog f₁ st fn args = some r) : evalJsCall prog f₂ st fn args = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalJs_mono_succ prog _).1 ih
theorem evalJsApp_mono {prog f₁ f₂ st fnVal xs r} (hle : f₁ ≤ f₂) (hr : evalJsApp prog f₁ st fnVal xs = some r) : evalJsApp prog f₂ st fnVal xs = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalJs_mono_succ prog _).2.1 ih
theorem evalJsStmts_mono {prog f₁ f₂ st ss r} (hle : f₁ ≤ f₂) (hr : evalJsStmts prog f₁ st ss = some r) : evalJsStmts prog f₂ st ss = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalJs_mono_succ prog _).2.2.1 ih

private theorem noTc_num (n : Nat) : (JsVal.num n).noTc := by simp [JsVal.noTc]
private theorem noTc_str (s : String) : (JsVal.str s).noTc := by simp [JsVal.noTc]
private theorem noTc_bigInt (n : Nat) : (JsVal.bigInt n).noTc := by simp [JsVal.noTc]
private theorem noTc_getD {fs : List JsVal} {i : Nat} (h : ∀ v ∈ fs, v.noTc) : (fs.getD i (.num 0)).noTc := by
  rw [List.getD_eq_getElem?_getD]; cases hg : fs[i]? with | none => exact noTc_num 0 | some v => exact h v (List.mem_of_getElem? hg)
private theorem noTc_assocGet [BEq κ] : ∀ {ps : List (κ × JsVal)} {k : κ}, (∀ p ∈ ps, p.2.noTc) → (assocGet k ps).noTc
  | [], _, _ => noTc_num 0 | (_, _) :: _, _, h => by dsimp only [assocGet]; split; exact h _ (.head _); exact noTc_assocGet fun p hp => h p (.tail _ hp)
private theorem noTcPairs_set [BEq κ] : ∀ {ps : List (κ × JsVal)} {k : κ} {v : JsVal}, (∀ p ∈ ps, p.2.noTc) → v.noTc → ∀ p ∈ assocSet k v ps, p.2.noTc
  | [], _, _, _, hv, _, hp => (List.mem_singleton.1 hp) ▸ hv
  | _ :: _, _, _, hp, hv, q, hq => by
      dsimp only [assocSet] at hq; split at hq
      · exact (List.mem_cons.1 hq).elim (· ▸ hv) (fun h => hp q (.tail _ h))
      · exact (List.mem_cons.1 hq).elim (fun h => h ▸ hp _ (.head _)) (noTcPairs_set (fun p h => hp p (.tail _ h)) hv q)
theorem evalIrArg_noTc {ρ : Nat → JsVal} (hρ : ∀ k, (ρ k).noTc) : ∀ a : Arg, (evalIrArg ρ a).noTc | .var x => hρ x.idx | .erased => noTc_num 0
theorem evalIrPure_noTc (c : Ctx) (ty : IRType) {ρ : Nat → JsVal} (hρ : ∀ k, (ρ k).noTc) (e : IR.Expr) (hpap : ∀ f ys, e = .pap f ys → ∀ j : JoinPointId, c.js f ≠ jp j) : (evalIrPure c ty ρ e).noTc := by
  have hmap : ∀ ys : List Arg, ∀ v ∈ ys.map (evalIrArg ρ), v.noTc := fun ys v hv => by rcases List.mem_map.1 hv with ⟨a, _, rfl⟩; exact evalIrArg_noTc hρ a
  have hctor : ∀ info ys, (evalIrCtor ρ info ys).noTc := fun info ys => by dsimp only [evalIrCtor]; split; exact noTc_num _; rw [JsVal.noTc]; exact ⟨hmap ys.toList, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩
  cases e with
  | ctor i ys | reuse _ i _ ys => exact hctor i ys
  | proj _ x => dsimp only [evalIrPure]; have hx := hρ x.idx; cases h : ρ x.idx with | ctorObj => rw [h, JsVal.noTc] at hx; exact noTc_getD hx.1 | _ => exact noTc_num 0
  | uproj _ x => dsimp only [evalIrPure]; have hx := hρ x.idx; cases h : ρ x.idx with | ctorObj => rw [h, JsVal.noTc] at hx; exact noTc_assocGet hx.2.1 | _ => exact noTc_num 0
  | sproj _ _ x => dsimp only [evalIrPure]; have hx := hρ x.idx; cases h : ρ x.idx with | ctorObj => rw [h, JsVal.noTc] at hx; exact noTc_assocGet hx.2.2 | _ => exact noTc_num 0
  | pap f ys => rw [evalIrPure, JsVal.noTc]; exact ⟨hpap f ys rfl, hmap ys.toList⟩ | box _ x | unbox x => exact hρ x.idx
  | lit lv => cases lv with | num _ => dsimp only [evalIrPure]; split; exact noTc_bigInt _; exact noTc_num _ | str _ => exact noTc_str _
  | _ => exact noTc_num 0
private theorem env_eq_update {irEnv : Nat → JsVal} {jsEnv : String → JsVal} (hm : ∀ w : VarId, irEnv w.idx = jsEnv (v w)) (x : VarId) (val : JsVal) :
    ∀ w : VarId, (if w.idx == x.idx then val else irEnv w.idx) = bindEnv jsEnv (v x) val (v w) := fun w => by
  by_cases h : w.idx = x.idx; simp [h, bindEnv, show v w = v x from congrArg (fun k => s!"x{k}") h]; simp [beq_false_of_ne h, bindEnv, beq_false_of_ne (fun he => h (v_inj he)), hm w]
private theorem env_noTc_bind {ρ : Nat → JsVal} {k : Nat} {val : JsVal} (hρ : ∀ m, (ρ m).noTc) (hv : val.noTc) : ∀ m, (if m == k then val else ρ m).noTc := fun m => by split; exact hv; exact hρ m
def suffixFrom (k : Nat) : List (Nat × Nat) → List (Nat × Nat) | [] => [] | p :: rest => if p.1 == k then p :: rest else suffixFrom k rest
private theorem suffixFrom_head (k ar : Nat) (xs : List (Nat × Nat)) : suffixFrom k ((k, ar) :: xs) = (k, ar) :: xs := by simp [suffixFrom]
private theorem mem_suffixFrom_mem {k : Nat} {x : Nat × Nat} : ∀ {xs : List (Nat × Nat)}, x ∈ suffixFrom k xs → x ∈ xs | [], h => nomatch h | _ :: _, h => by dsimp only [suffixFrom] at h; split at h; exact h; exact .tail _ (mem_suffixFrom_mem h)
private theorem nodup_suffixFrom {k : Nat} : ∀ {xs : List (Nat × Nat)}, (xs.map Prod.fst).Nodup → ((suffixFrom k xs).map Prod.fst).Nodup | [], _ => List.nodup_nil | _ :: _, hnd => by dsimp only [suffixFrom]; split; exact hnd; exact nodup_suffixFrom (List.nodup_cons.1 hnd).2
private theorem suffixFrom_idem {k1 k2 ar2 : Nat} : ∀ {xs : List (Nat × Nat)}, (xs.map Prod.fst).Nodup → (k2, ar2) ∈ suffixFrom k1 xs → suffixFrom k2 (suffixFrom k1 xs) = suffixFrom k2 xs
  | [], _, hm => nomatch hm | p :: rest, hnd, hm => by
    have hndR := (List.nodup_cons.1 hnd).2; dsimp only [suffixFrom] at hm ⊢; split at hm; simp_all [suffixFrom]
    rename_i hne; have hne2 : p.1 ≠ k2 := fun heq => (List.nodup_cons.1 hnd).1 (heq ▸ List.mem_map.2 ⟨_, mem_suffixFrom_mem hm, rfl⟩); rw [if_neg hne, if_neg (fun h => hne2 (eq_of_beq h))]; exact suffixFrom_idem hndR hm
private theorem nodup_fst_eq {p q : Nat × Nat} : ∀ {xs : List (Nat × Nat)}, (xs.map Prod.fst).Nodup → p ∈ xs → q ∈ xs → p.1 = q.1 → p.2 = q.2
  | [], _, hp, _, _ => nomatch hp
  | r :: rest, hnd, hp, hq, heq => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hp with rfl | hp' <;> rcases List.mem_cons.1 hq with rfl | hq'
    · rfl
    · exact absurd (List.mem_map.2 ⟨q, hq', heq.symm⟩) hnd.1
    · exact absurd (List.mem_map.2 ⟨p, hp', heq⟩) hnd.1
    · exact nodup_fst_eq hnd.2 hp' hq' heq
private theorem bindIrParams_nodup_eq : ∀ (xs : List Param) (args : List JsVal) (ρ : Nat → JsVal) (envJs : String → JsVal),
    (xs.map (·.x.idx)).Nodup → (∀ w : VarId, ρ w.idx = envJs (v w)) → ∀ w : VarId, bindIrParams ⟨xs⟩ args ρ w.idx = bindMany (xs.zipWith (fun p val => (v p.x, val)) args) envJs (v w)
  | [], _, _, _, _, hm, w | _ :: _, [], _, _, _, hm, w => by simp [bindIrParams, bindMany, hm w]
  | p :: prest, _ :: vrest, _, _, hnd, hm, w => by
    simp only [List.map_cons, List.nodup_cons] at hnd; simp only [bindIrParams, List.zipWith_cons_cons, bindMany]
    apply bindIrParams_nodup_eq prest vrest _ _ hnd.2 _ w; intro u; by_cases hu : u.idx = p.x.idx; simp [hu, bindEnv, show v u = v p.x from congrArg (fun k => s!"x{k}") hu]; simp only [beq_false_of_ne hu, hm u, bindEnv]; rw [beq_false_of_ne fun hveq => hu (v_inj hveq)]
private theorem bindIrParams_noTc : ∀ (xs : List Param) (args : List JsVal) (ρ : Nat → JsVal), (∀ k, (ρ k).noTc) → (∀ a ∈ args, a.noTc) → ∀ k, (bindIrParams ⟨xs⟩ args ρ k).noTc
  | [], _, _, hρ, _, k | _ :: _, [], _, hρ, _, k => by simp [bindIrParams, hρ k]
  | _ :: prest, a :: vrest, _, hρ, ha, k => bindIrParams_noTc prest vrest _ (fun m => by split; exact ha a (.head _); exact hρ m) (fun x hx => ha x (.tail _ hx)) k
private theorem evalJsAssignsStep_zipIdx_vars {doCall doApp st} (j : JoinPointId) (args : List JsVal) :
    ∀ (ps : List Param) (off : Nat), (hlen : off + ps.length = args.length) → (∀ i (hi : i < ps.length), st.env s!"_{jp j}_{off + i}" = args[off + i]'(by omega)) →
      evalJsAssignsStep doCall doApp st ((ps.zipIdx off).map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}")) = some (ps.zipWith (fun p val => (v p.x, val)) (args.drop off), st)
  | [], _, _, _ => rfl
  | _ :: rest, off, hlen, hvals => by
    have hoff : off < args.length := by simp at hlen; omega
    have h0 : st.env s!"_{jp j}_{off}" = args[off] := by simpa using hvals 0 (by simp)
    have hrest := evalJsAssignsStep_zipIdx_vars (doCall := doCall) (doApp := doApp) (st := st) j args rest (off + 1) (by simp at hlen ⊢; omega) fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hvals (i + 1) (by simp at hi ⊢; omega)
    rw [← List.getElem_cons_drop hoff]; dsimp only [List.zipIdx_cons, List.map_cons, List.zipWith_cons_cons, evalJsAssignsStep, evalJsExprStep] at hrest ⊢; rw [h0, hrest]

/-! ### Simulation Contract, State Invariants & Step Infrastructure -/

def TailRcVarsOk (nonArr : Std.HashSet Nat) : FnBody → Prop | .inc x _ _ _ cont | .dec x _ _ _ cont | .del x cont => nonArr.contains x.idx = true ∧ TailRcVarsOk nonArr cont | .ret (.var _) => True | _ => False
def ExprWf (c : Ctx) (irProg : IrProg) (allowTailCont : Bool) (x : VarId) (cont : FnBody) : IR.Expr → Prop
  | .fap f _ => if f == `Qed.refMark then c.selfFn ≠ some `Qed.refMark else (∃ xs ty b info, irProg f = some (.fdecl f xs ty b info)) ∧ ((c.selfFn == some f && retsVar x cont) = true → allowTailCont = true ∧ TailRcVarsOk c.nonArr cont ∧ (c.directLoop = true → (c.selfParams.toList.map (·.x.idx)).Nodup))
  | .pap f _ => ∃ d, irProg f = some d | _ => True
mutual
def BodyWf (c : Ctx) (irProg : IrProg) (inlineJps recJps : List (Nat × Nat)) (allowTailCont : Bool) : FnBody → Prop
  | .vdecl x _ e cont => BodyWf c irProg inlineJps recJps allowTailCont cont ∧ ExprWf c irProg allowTailCont x cont e
  | .jdecl j xs val cont => (xs.toList.map (·.x.idx)).Nodup ∧ (∀ a, (j.idx, a) ∉ inlineJps) ∧ (∀ a, (j.idx, a) ∉ recJps) ∧ c.inlineJps.get? j.idx = none ∧
      if !hasJmpTo j val then BodyWf { c with inlineJps := c.inlineJps.insert j.idx xs } irProg ((j.idx, xs.size) :: inlineJps) recJps allowTailCont cont ∧ BodyWf c irProg inlineJps recJps allowTailCont val
      else BodyWf c irProg [] ((j.idx, xs.size) :: recJps) (if c.directLoop then false else allowTailCont) val ∧ BodyWf c irProg inlineJps ((j.idx, xs.size) :: recJps) allowTailCont cont
  | .inc x _ _ _ cont => BodyWf c irProg inlineJps recJps allowTailCont cont ∧ (c.nonArr.contains x.idx = true ∨ (match c.projSrc.get? x.idx with | some p => !hasDecOf p cont = true | none => true))
  | .dec _ _ _ _ cont | .del _ cont | .set _ _ _ cont | .setTag _ _ cont | .uset _ _ _ cont | .sset _ _ _ _ _ cont => BodyWf c irProg inlineJps recJps allowTailCont cont
  | .jmp j ys => (j.idx, ys.size) ∈ inlineJps ∨ (j.idx, ys.size) ∈ recJps
  | .case _ _ _ alts => AltsWf c irProg inlineJps recJps allowTailCont alts.toList
  | .ret _ | .unreachable => True
def AltsWf (c : Ctx) (irProg : IrProg) (inlineJps recJps : List (Nat × Nat)) (allowTailCont : Bool) : List Alt → Prop | [] => True | .ctor _ b :: rest | .default b :: rest => BodyWf c irProg inlineJps recJps allowTailCont b ∧ AltsWf c irProg inlineJps recJps allowTailCont rest
end

/-- Whole-program lowering contract relating Lean IR (`irProg`) and JS (`jsProg`) under context `c0` and `revName`. -/
structure ProgLowered (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) : Prop where
  c0_clean     : c0.selfFn = none ∧ c0.selfParams = #[] ∧ c0.directLoop = false ∧ ∀ k, c0.inlineJps.get? k = none
  fdecl_name   : ∀ f fnm xs ty b info, prog f = some (.fdecl fnm xs ty b info) → fnm = f
  js_at_fdecl  : ∀ f xs ty b info, prog f = some (.fdecl f xs ty b info) → jsProg (c0.js f) = lowerDecl c0 (.fdecl f xs ty b info)
  rev_ok       : ∀ f d, prog f = some d → revName (c0.js f) = some f
  rev_none     : ∀ s f, revName s = some f → prog f ≠ none ∧ c0.js f = s
  jsProg_dom   : ∀ s, jsProg s ≠ none → ∃ f, revName s = some f
  findEnv_ok   : ∀ f d, prog f = some d → findEnvDecl c0.env f = some d ∧ (match d with | .extern .. => False | _ => True) ∧ f ≠ `Qed.refMark
  fn_disjoint  : ∀ s f, revName s = some f → (∀ j : JoinPointId, s ≠ jp j) ∧ s ≠ "$.tag" ∧ s ≠ "$.isShared" ∧ s ≠ "$.refMark"
  decl_wf      : ∀ f xs ty b info, prog f = some (.fdecl f xs ty b info) →
    let cBase : Ctx := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b }
    if xs.isEmpty then match getInitFnNameFor? c0.env f with | some initFn => ∃ xs' ty' b' info', prog initFn = some (.fdecl initFn xs' ty' b' info') ∧ xs'.isEmpty | none => BodyWf cBase prog [] [] false b
    else (xs.toList.map (·.x.idx)).Nodup ∧ if hasSelfTail f b then
        if !hasJpSelfTail f b then BodyWf { cBase with selfFn := some f, selfParams := xs, directLoop := true } prog [] [] true b else BodyWf { cBase with selfFn := some f, selfParams := xs } prog [] [] true b
      else BodyWf cBase prog [] [] false b
  nonArr_typed : ∀ fuel h memos f args val h' m', (∀ g, (memos g).val.elim True JsVal.noTc) → evalIrCall prog c0 revName fuel h memos f args = some (val, h', m') → val.noTc ∧ (∀ g, (m' g).val.elim True JsVal.noTc)
  nonArr_pure  : ∀ (nonArr : Std.HashSet Nat) ρ ty (x : VarId) e, nonArr.contains x.idx = true → (∀ k, nonArr.contains k = true → (ρ k).isNonArr = true) → (evalIrPure c0 ty ρ e).isNonArr = true
  nonArr_call  : ∀ (nonArr : Std.HashSet Nat) fuel h memos f args val h' m' k, nonArr.contains k = true →
    (evalIrCall prog c0 revName fuel h memos f args = some (val, h', m') → val.isNonArr = true) ∧ (∀ fnVal, evalIrApp prog c0 revName fuel h memos fnVal args = some (val, h', m') → val.isNonArr = true)
  nonArr_param : ∀ (nonArr : Std.HashSet Nat) xs args ρ k, nonArr.contains k = true → (∀ m, nonArr.contains m = true → (ρ m).isNonArr = true) → (bindIrParams xs args ρ k).isNonArr = true
  nonArr_refMark : ∀ (nonArr : Std.HashSet Nat) (ys : List JsVal) (k : Nat), nonArr.contains k = true → (match ys with | [.arr id] => JsVal.arr id | _ => .num 0).isNonArr = true

structure StatesMatch (prog : IrProg) (c c0 : Ctx) (inlineJps recJps : List (Nat × Nat)) (allowTailCont : Bool) (irSt : IrState) (jsSt : JsState) : Prop where
  env_eq      : ∀ x : VarId, irSt.env x.idx = jsSt.env (v x)
  heap_eq     : irSt.heap = jsSt.heap
  memos_eq    : ∀ f, prog f ≠ none → irSt.memos f = jsSt.memos (c0.js f)
  memos_noTc  : ∀ f, (irSt.memos f).val.elim True JsVal.noTc
  env_noTc    : ∀ k, (irSt.env k).noTc
  nonArr_ok   : ∀ k, c.nonArr.contains k = true → (irSt.env k).isNonArr = true
  fns_only_jp : ∀ s, jsSt.fns s ≠ none → ∃ j : JoinPointId, s = jp j
  jps_none    : ∀ j : JoinPointId, irSt.jps j.idx = none ↔ jsSt.fns (jp j) = none
  jps_some    : ∀ (j : JoinPointId) xs val capIr, irSt.jps j.idx = some (xs, val, capIr) → (j.idx, xs.size) ∈ recJps →
    ∃ jpsMap capJs, let cVal : Ctx := { c with names := c0.names, min := c0.min, env := c0.env, inlineJps := jpsMap }
      jsSt.fns (jp j) = some (xs.toList.map (v ·.x), lowerBody cVal val, capJs) ∧
      (∀ p ∈ suffixFrom j.idx recJps, jpsMap.get? p.1 = none) ∧ (∀ x : VarId, capIr x.idx = capJs (v x)) ∧ (∀ k, (capIr k).noTc) ∧
      (∀ k, c.nonArr.contains k = true → (capIr k).isNonArr = true) ∧ (xs.toList.map (·.x.idx)).Nodup ∧ BodyWf cVal prog [] (suffixFrom j.idx recJps) (if c.directLoop then false else allowTailCont) val
  rec_ar      : ∀ (j : JoinPointId) ar xs val capIr, (j.idx, ar) ∈ recJps → irSt.jps j.idx = some (xs, val, capIr) → xs.size = ar
  rec_nodup   : (recJps.map Prod.fst).Nodup
  rec_disj    : ∀ p ∈ recJps, c.inlineJps.get? p.1 = none
  inline_sub  : ∀ idx ar, (idx, ar) ∈ inlineJps → ∃ xs, c.inlineJps.get? idx = some xs ∧ xs.size = ar

def CallPost (prog : IrProg) (c0 : Ctx) (v1 v2 : JsVal) (h1 : CowHeap JsVal) (m1 : Name → MemoCell JsVal) (jsSt st2 : JsState) : Prop :=
  v1 = v2 ∧ v1.noTc ∧ h1 = st2.heap ∧ st2.env = jsSt.env ∧ st2.fns = jsSt.fns ∧ (∀ g, prog g ≠ none → m1 g = st2.memos (c0.js g)) ∧ (∀ g, (m1 g).val.elim True JsVal.noTc)
def ExitRetOk (prog : IrProg) (c0 : Ctx) (v : JsVal) (irSt1 : IrState) (jsSt1 : JsState) : Prop :=
  v.noTc ∧ irSt1.heap = jsSt1.heap ∧ (∀ f, prog f ≠ none → irSt1.memos f = jsSt1.memos (c0.js f)) ∧ (∀ f, (irSt1.memos f).val.elim True JsVal.noTc)
def ExitJmpOk (prog : IrProg) (c c0 : Ctx) (inlineJps recJps : List (Nat × Nat)) (allowTailCont : Bool) (j : JoinPointId) (args : List JsVal) (irSt1 : IrState) (jsSt1 : JsState) : Prop :=
  (j.idx, args.length) ∈ inlineJps ∧ (∀ i (hi : i < args.length), jsSt1.env (inlineJpSlot j i) = args[i]'hi) ∧ (∀ a ∈ args, a.noTc) ∧ StatesMatch prog c c0 inlineJps recJps allowTailCont irSt1 jsSt1
def ExitMatchIJ (prog : IrProg) (c c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (fuel : Nat) (inlineJps recJps : List (Nat × Nat)) (allowTailCont : Bool) (jsSt : JsState) (b : FnBody) : IrOutcome → IrState → Prop
  | .jumped j args, irSt1 => ∃ fJs jsSt1, evalJsStmts jsProg fJs jsSt (lowerBody c b) = some (.jumped (jp j), jsSt1) ∧ ExitJmpOk prog c c0 inlineJps recJps allowTailCont j args irSt1 jsSt1
  | .returned val, irSt1 => (∃ fJs jsSt1, evalJsStmts jsProg fJs jsSt (lowerBody c b) = some (.returned val, jsSt1) ∧ ExitRetOk prog c0 val irSt1 jsSt1) ∨
      (allowTailCont = true ∧ ∃ fJs jsSt1 sf nextArgs m₀ fIr', fIr' ≤ fuel ∧ c.selfFn = some sf ∧ (∀ a ∈ nextArgs, a.noTc) ∧
        evalJsStmts jsProg fJs jsSt (lowerBody c b) = some (if c.directLoop then .tailCont nextArgs else .returned (.tc nextArgs), jsSt1) ∧
        (∀ f, prog f ≠ none → m₀ f = jsSt1.memos (c0.js f)) ∧ (∀ f, (m₀ f).val.elim True JsVal.noTc) ∧ evalIrCall prog c0 revName fIr' jsSt1.heap m₀ sf nextArgs = some (val, irSt1.heap, irSt1.memos))
def TailContCont (prog : IrProg) (c c0 : Ctx) (revName : String → Option Name) (inlineJps : List Nat) (irSt : IrState) (b : FnBody) (jsSt1 : JsState) (nextArgs : List JsVal) : Prop :=
  (∀ a ∈ nextArgs, a.noTc) ∧ ∃ sf m₀, c.selfFn = some sf ∧ (∀ f, prog f ≠ none → m₀ f = jsSt1.memos (c0.js f)) ∧ (∀ f, (m₀ f).val.elim True JsVal.noTc) ∧
    ∀ fIrRec v h' m', evalIrCall prog c0 revName fIrRec jsSt1.heap m₀ sf nextArgs = some (v, h', m') →
      ∃ fIr irSt1, evalIrBody prog c0 revName inlineJps fIr irSt b = some (.returned v, irSt1) ∧ v.noTc ∧ irSt1.heap = h' ∧ (∀ f, prog f ≠ none → irSt1.memos f = m' f) ∧ (∀ f, (irSt1.memos f).val.elim True JsVal.noTc)
def ExitMatchJI (prog : IrProg) (c c0 : Ctx) (revName : String → Option Name) (inlineJps recJps : List (Nat × Nat)) (allowTailCont : Bool) (irSt : IrState) (b : FnBody) : BlockExit → JsState → Prop
  | .next, _ => False
  | .jumped lbl, jsSt1 => ∃ fIr j args irSt1, lbl = jp j ∧ evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr irSt b = some (.jumped j args, irSt1) ∧ ExitJmpOk prog c c0 inlineJps recJps allowTailCont j args irSt1 jsSt1
  | .tailCont nextArgs, jsSt1 => allowTailCont = true ∧ c.directLoop = true ∧ TailContCont prog c c0 revName (inlineJps.map Prod.fst) irSt b jsSt1 nextArgs
  | .returned (.tc nextArgs), jsSt1 => allowTailCont = true ∧ c.directLoop = false ∧ TailContCont prog c c0 revName (inlineJps.map Prod.fst) irSt b jsSt1 nextArgs
  | .returned jval, jsSt1 => ∃ fIr irSt1, evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr irSt b = some (.returned jval, irSt1) ∧ ExitRetOk prog c0 jval irSt1 jsSt1

theorem jp_beq_self (j : JoinPointId) : (j == j) = true := (show (j == j) = (j.idx == j.idx) from rfl) ▸ beq_self_eq_true j.idx
private theorem jp_ext {j₁ j₂ : JoinPointId} (h : j₁.idx = j₂.idx) : j₁ = j₂ := by cases j₁; cases j₂; cases h; rfl
theorem ExitMatchJI.of_false_ret {prog c c0 revName inlineJps recJps irSt b v jsSt1} (h : ExitMatchJI prog c c0 revName inlineJps recJps false irSt b (.returned v) jsSt1) :
    ∃ fIr irSt1, evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr irSt b = some (.returned v, irSt1) ∧ ExitRetOk prog c0 v irSt1 jsSt1 := by cases v <;> first | exact absurd h.1 Bool.false_ne_true | exact h
theorem ExitMatchJI.of_ret_nonTc {prog c c0 revName allowTailCont stIr0 b v2 st2} (hex : ExitMatchJI prog c c0 revName [] [] allowTailCont stIr0 b (.returned v2) st2) (hnoTc : ∀ as, v2 = .tc as → c.directLoop = false → False) :
    ∃ fIrB irSt1, evalIrBody prog c0 revName [] fIrB stIr0 b = some (.returned v2, irSt1) ∧ ExitRetOk prog c0 v2 irSt1 st2 := by cases v2 <;> first | exact False.elim (hnoTc _ rfl hex.2.1) | exact hex

theorem rcInc_nonArr_noop_isNonArr (h : CowHeap JsVal) (val : JsVal) (n : Nat) (hna : val.isNonArr = true) : h.rcInc val.toRcVal n = h := by cases val <;> simp [JsVal.isNonArr] at hna <;> rfl
theorem rcDec_nonArr_noop_isNonArr (h : CowHeap JsVal) (val : JsVal) (n : Nat) (hna : val.isNonArr = true) : h.rcDec val.toRcVal n = h := by cases val <;> simp [JsVal.isNonArr] at hna <;> rfl
theorem evalIrBody_tailRcVarsOk (prog : IrProg) (c0 : Ctx) (nonArr : Std.HashSet Nat) (revName : String → Option Name) (inlineJps : List Nat) (fuel : Nat) (x : VarId) :
    ∀ (cont : FnBody) (st : IrState), TailRcVarsOk nonArr cont → retsVar x cont = true → (∀ k, nonArr.contains k = true → (st.env k).isNonArr = true) → evalIrBody prog c0 revName inlineJps fuel st cont = some (.returned (st.env x.idx), st) :=
  fnBody_ind (fun cont => ∀ st, TailRcVarsOk nonArr cont → retsVar x cont = true → (∀ k, nonArr.contains k = true → (st.env k).isNonArr = true) → evalIrBody prog c0 revName inlineJps fuel st cont = some (.returned (st.env x.idx), st)) fun cont ih st htr hret hna => by
    cases cont with
    | inc y n _ _ _ => dsimp only [evalIrBody, evalIrBodyStep]; rw [rcInc_nonArr_noop_isNonArr _ _ n (hna y.idx htr.1)]; exact ih st htr.2 hret hna
    | dec y n _ _ _ => dsimp only [evalIrBody, evalIrBodyStep]; rw [rcDec_nonArr_noop_isNonArr _ _ n (hna y.idx htr.1)]; exact ih st htr.2 hret hna
    | del y _ => dsimp only [evalIrBody, evalIrBodyStep]; rw [rcDec_nonArr_noop_isNonArr _ _ 1 (hna y.idx htr.1)]; exact ih st htr.2 hret hna
    | ret a => cases a with | erased => exact False.elim htr | var w => simp only [retsVar, skipRC] at hret; have hwx : w = x := (by cases w; cases x; congr; exact eq_of_beq hret); subst hwx; rfl
    | _ => exact False.elim htr

theorem evalJsStmts_letDecls_skip (prog : JsProg) (fuel : Nat) (st : JsState) (xs : Array Param) (names : List String) (ss : List JsStmt) :
    evalJsStmts prog fuel st ((if xs.isEmpty then [] else [JsStmt.letDecls names]) ++ ss) = evalJsStmts prog fuel st ss := by cases xs.isEmpty <;> rfl
theorem bindEnv_nonArr_of_expr (c : Ctx) (ρ : Nat → JsVal) (k : Nat) (v : JsVal) (hna : ∀ m, c.nonArr.contains m = true → (ρ m).isNonArr = true) (hv : c.nonArr.contains k = true → v.isNonArr = true) :
    ∀ m, c.nonArr.contains m = true → (if m == k then v else ρ m).isNonArr = true := fun m hm => by by_cases hmk : m = k; (subst hmk; simp [hv hm]); simp [beq_false_of_ne hmk, hna m hm]
theorem StatesMatch.updVar {prog : IrProg} {c c0 : Ctx} {inlineJps recJps allowTailCont irSt jsSt} (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) (x : VarId) {val : JsVal} (hnt : val.noTc) (hna : c.nonArr.contains x.idx = true → val.isNonArr = true) :
    StatesMatch prog c c0 inlineJps recJps allowTailCont { irSt with env := fun k => if k == x.idx then val else irSt.env k } { jsSt with env := bindEnv jsSt.env (v x) val } :=
  { hsm with env_eq := env_eq_update hsm.env_eq x val, env_noTc := env_noTc_bind hsm.env_noTc hnt, nonArr_ok := bindEnv_nonArr_of_expr c irSt.env x.idx val hsm.nonArr_ok hna }
theorem StatesMatch.updHeap {prog : IrProg} {c c0 : Ctx} {inlineJps recJps allowTailCont irSt jsSt} (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) {h1 h2 : CowHeap JsVal} (hhp : h1 = h2) :
    StatesMatch prog c c0 inlineJps recJps allowTailCont { irSt with heap := h1 } { jsSt with heap := h2 } := { hsm with heap_eq := hhp }
theorem StatesMatch.updCall {prog : IrProg} {c c0 : Ctx} {inlineJps recJps allowTailCont} {irSt : IrState} {jsSt jsSt1 : JsState} (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) (x : VarId) {val : JsVal} {h' : CowHeap JsVal} {m' : Name → MemoCell JsVal}
    (hnt : val.noTc) (hna : c.nonArr.contains x.idx = true → val.isNonArr = true) (hhp : h' = jsSt1.heap) (henv : jsSt1.env = jsSt.env) (hfns : jsSt1.fns = jsSt.fns) (hmEq : ∀ g, prog g ≠ none → m' g = jsSt1.memos (c0.js g)) (hmNo : ∀ g, (m' g).val.elim True JsVal.noTc) :
    StatesMatch prog c c0 inlineJps recJps allowTailCont { irSt with env := fun k => if k == x.idx then val else irSt.env k, heap := h', memos := m' } { jsSt1 with env := bindEnv jsSt1.env (v x) val } :=
  ⟨fun w => (by rw [henv]; exact env_eq_update hsm.env_eq x val w), hhp, hmEq, hmNo, env_noTc_bind hsm.env_noTc hnt, bindEnv_nonArr_of_expr c irSt.env x.idx val hsm.nonArr_ok hna,
   fun s hs => (by rw [hfns] at hs; exact hsm.fns_only_jp s hs), fun j' => (by rw [hfns]; exact hsm.jps_none j'), fun j' xs' val' capIr' hj' hm' => (by rw [hfns]; exact hsm.jps_some j' xs' val' capIr' hj' hm'), hsm.rec_ar, hsm.rec_nodup, hsm.rec_disj, hsm.inline_sub⟩
theorem StatesMatch.withCtx {prog : IrProg} {c c' c0 : Ctx} {inlineJps inlineJps' recJps allowTailCont} {irSt : IrState} {jsSt : JsState} (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) (hNA : c'.nonArr = c.nonArr) (hPS : c'.projSrc = c.projSrc) (hSF : c'.selfFn = c.selfFn) (hSP : c'.selfParams = c.selfParams) (hDL : c'.directLoop = c.directLoop) (hDisj : ∀ p ∈ recJps, c'.inlineJps.get? p.1 = none) (hIn : ∀ idx ar, (idx, ar) ∈ inlineJps' → ∃ xs, c'.inlineJps.get? idx = some xs ∧ xs.size = ar) :
    StatesMatch prog c' c0 inlineJps' recJps allowTailCont irSt jsSt :=
  { hsm with
    nonArr_ok := fun k hk => hsm.nonArr_ok k (hNA ▸ hk),
    jps_some := fun j' xs' val' capIr' hj' hm' => by simpa only [hNA, hPS, hSF, hSP, hDL] using hsm.jps_some j' xs' val' capIr' hj' hm',
    rec_disj := hDisj, inline_sub := hIn }
theorem findEnv_fap_args (c c0 : Ctx) (f : Name) (ys : Array Arg) (hnames : c.names = c0.names) (henv : c.env = c0.env) (hfe : findEnvDecl c0.env f = some (.fdecl xs₀ ps ty b info)) (hneq : f ≠ `Qed.refMark) : lowerApp c f ys = .call (c0.js f) (ys.toList.map lowerArg) := by
  have hjs : c.js f = c0.js f := by simp [Ctx.js, hnames]
  simp [lowerApp, beq_false_of_ne hneq, henv, hfe, hjs]
private theorem evalIrPure_ctx_eq (c c0 : Ctx) (hnames : c.names = c0.names) (henv : c.env = c0.env) : ∀ ty ρ e, evalIrPure c ty ρ e = evalIrPure c0 ty ρ e := fun ty ρ e => by
  cases e with | pap _ _ => dsimp only [evalIrPure, Ctx.js]; rw [hnames, henv] | lit lv => cases lv <;> rfl | _ => rfl
theorem evalIrPure_ctor_isNonArr (c : Ctx) (ty : IRType) (ρ : Nat → JsVal) : ∀ e : IR.Expr, (match e with | .ctor .. | .reuse .. | .reset .. | .pap .. | .lit .. | .isShared .. => True | _ => False) → (evalIrPure c ty ρ e).isNonArr = true := fun e he => by
  cases e with | ctor _ ys | reuse _ _ _ ys => dsimp only [evalIrPure, evalIrCtor]; split <;> rfl | reset _ _ | pap _ _ | isShared _ => rfl | lit lv => exact (by cases lv <;> dsimp only [evalIrPure] <;> first | rfl | (split <;> rfl)) | proj _ _ | uproj _ _ | sproj _ _ _ | fap _ _ | ap _ _ | box _ _ | unbox _ => exact False.elim he
private theorem zipWith_param_eq_zip : ∀ (l : List Param) (as : List JsVal), l.zipWith (fun p val => (v p.x, val)) as = (l.map (v ·.x)).zip as | [], _ | _ :: _, [] => rfl | _ :: rest, _ :: vs => by simp [List.zipWith_cons_cons, zipWith_param_eq_zip rest vs]
theorem evalIrBody_jmp_inline (prog : IrProg) (c : Ctx) (revName : String → Option Name) (inlineJps : List Nat) (fuel : Nat) (st : IrState) (j : JoinPointId) (ys : Array Arg) (hin : j.idx ∈ inlineJps) :
    evalIrBody prog c revName inlineJps fuel st (.jmp j ys) = some (.jumped j (ys.toList.map (evalIrArg st.env)), st) := by
  dsimp only [evalIrBody, evalIrBodyStep]; rw [if_pos hin]

theorem StatesMatch.initCall (prog : IrProg) (c c0 : Ctx) (allowTailCont : Bool) (jsSt : JsState) (h : CowHeap JsVal) (mIr : Name → MemoCell JsVal) (xs : Array Param) (args : List JsVal)
    (hhp : h = jsSt.heap) (hmEq : ∀ g, prog g ≠ none → mIr g = jsSt.memos (c0.js g)) (hmNo : ∀ g, (mIr g).val.elim True JsVal.noTc) (hnd : (xs.toList.map (·.x.idx)).Nodup) (hargs : ∀ a ∈ args, a.noTc) (hnp : ∀ k, c.nonArr.contains k = true → (bindIrParams xs args (fun _ => .num 0) k).isNonArr = true) :
    StatesMatch prog c c0 [] [] allowTailCont { env := bindIrParams xs args (fun _ => .num 0), heap := h, memos := mIr } { env := bindMany ((xs.toList.map (v ·.x)).zip args) (fun _ => .num 0), heap := jsSt.heap, memos := jsSt.memos } :=
  ⟨fun w => by cases xs with | mk xl => dsimp only; rw [bindIrParams_nodup_eq xl args (fun _ => .num 0) (fun _ => .num 0) hnd (fun _ => rfl) w, zipWith_param_eq_zip xl args],
   hhp, hmEq, hmNo, fun k => by cases xs with | mk xl => exact bindIrParams_noTc xl args (fun _ => .num 0) (fun _ => noTc_num 0) hargs k,
   hnp, fun _ hs => (nomatch hs), fun _ => ⟨fun _ => rfl, fun _ => rfl⟩, fun _ _ _ _ _ hm => (nomatch hm), fun _ _ _ _ _ hm => (nomatch hm), List.nodup_nil, fun _ hm => (nomatch hm), fun _ _ hm => (nomatch hm)⟩

private theorem StatesMatch.dropRecHead {prog c c0 inlineJps recJps allowTailCont irSt jsSt} {j : JoinPointId} {ar : Nat} (hnotRec : ∀ a, (j.idx, a) ∉ recJps) (hsm : StatesMatch prog c c0 inlineJps ((j.idx, ar) :: recJps) allowTailCont irSt jsSt) :
    StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt :=
  { hsm with
    jps_some := fun j' xs' val' capIr' hj' hm' => by
      have hne : j'.idx ≠ j.idx := fun he => hnotRec xs'.size (he ▸ hm')
      simpa only [show suffixFrom j'.idx ((j.idx, ar) :: recJps) = suffixFrom j'.idx recJps by simp [suffixFrom, beq_false_of_ne hne.symm]] using hsm.jps_some j' xs' val' capIr' hj' (.tail _ hm'),
    rec_ar := fun j' a' xs' val' capIr' hm' => hsm.rec_ar j' a' xs' val' capIr' (.tail _ hm'), rec_nodup := hsm.rec_nodup.of_cons, rec_disj := fun p hp => hsm.rec_disj p (.tail _ hp) }
theorem ExitMatchIJ.dropRecHead {prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt b irO irSt1} {j : JoinPointId} {ar : Nat} (hnotRec : ∀ a, (j.idx, a) ∉ recJps) (hex : ExitMatchIJ prog c c0 jsProg revName fuel inlineJps ((j.idx, ar) :: recJps) allowTailCont jsSt b irO irSt1) :
    ExitMatchIJ prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt b irO irSt1 := by
  cases irO with | returned _ => exact hex | jumped _ _ => rcases hex with ⟨fJs, jsSt1, hev, hok⟩; exact ⟨fJs, jsSt1, hev, hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.dropRecHead hnotRec⟩
theorem ExitMatchJI.dropRecHead {prog c c0 revName inlineJps recJps allowTailCont irSt b ex jsSt1} {j : JoinPointId} {ar : Nat} (hnotRec : ∀ a, (j.idx, a) ∉ recJps) (hex : ExitMatchJI prog c c0 revName inlineJps ((j.idx, ar) :: recJps) allowTailCont irSt b ex jsSt1) :
    ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt b ex jsSt1 := by
  cases ex with | next | tailCont _ => exact hex | returned v => cases v <;> exact hex | jumped _ => rcases hex with ⟨fIr, j', args, irSt1, rfl, hev, hok⟩; exact ⟨fIr, j', args, irSt1, rfl, hev, hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.dropRecHead hnotRec⟩

private theorem evalJsCall_selfTail_eq (dl : Bool) (jsProg : JsProg) (c : Ctx) (f : Name) (ps : List String) (body : List JsStmt) (st : JsState) (args : List JsVal) (fuel : Nat)
    (hfns : st.fns (c.js f) = none) (hprog : jsProg (c.js f) = some (if dl then .fnDirectLoop (c.js f) f ps body else .fnTrampoline (c.js f) f ps body)) :
    evalJsCall jsProg fuel st (c.js f) args = evalJsSelfTail dl jsProg fuel ps body st args := by
  cases fuel with | zero => rfl | succ _ => dsimp only [evalJsCall, evalJsSelfTail, evalJsFuel, evalJsCallStep]; rw [hfns, hprog]; cases dl <;> rfl
theorem evalJsCall_selfTail (dl : Bool) (jsProg : JsProg) (c0 : Ctx) (f : Name) (ps : List String) (body : List JsStmt) (st : JsState) (args : List JsVal) (k : Nat)
    (hfns : st.fns (c0.js f) = none) (hdecl : jsProg (c0.js f) = some (if dl then .fnDirectLoop (c0.js f) f ps body else .fnTrampoline (c0.js f) f ps body)) :
    ∀ (ex : BlockExit) (st1 : JsState), evalJsStmts jsProg k { env := bindMany (ps.zip args) (fun _ => .num 0), heap := st.heap, memos := st.memos } body = some (ex, st1) →
    (∀ v, v.noTc → ex = .returned v → evalJsCall jsProg (k + 1) st (c0.js f) args = some (v, { st with heap := st1.heap, memos := st1.memos })) ∧
    (∀ na, ex = (if dl then .tailCont na else .returned (.tc na)) → ∀ k', k ≤ k' → evalJsCall jsProg (k' + 1) st (c0.js f) args = evalJsCall jsProg k' { st with heap := st1.heap, memos := st1.memos } (c0.js f) na) := fun ex st1 hb =>
  ⟨fun v hv hex => by subst hex; rw [evalJsCall_selfTail_eq dl jsProg c0 f ps body st args (k + 1) hfns hdecl, evalJsSelfTail_succ]; dsimp only [evalJsSelfTailStep]; rw [hb]; cases v with | tc _ => simp [JsVal.noTc] at hv | _ => rfl,
   fun na hex k' hle => by subst hex; rw [evalJsCall_selfTail_eq dl jsProg c0 f ps body st args (k' + 1) hfns hdecl, evalJsCall_selfTail_eq dl jsProg c0 f ps body { st with heap := st1.heap, memos := st1.memos } na k' hfns hdecl, evalJsSelfTail_succ]; dsimp only [evalJsSelfTailStep]; rw [evalJsStmts_mono hle hb]; cases dl <;> rfl⟩
theorem evalJsCall_selfTail_inv (dl : Bool) (jsProg : JsProg) (c0 : Ctx) (f : Name) (ps : List String) (body : List JsStmt) (st : JsState) (args : List JsVal) (f' : Nat) (v2 : JsVal) (st2 : JsState)
    (hfns : st.fns (c0.js f) = none) (hdecl : jsProg (c0.js f) = some (if dl then .fnDirectLoop (c0.js f) f ps body else .fnTrampoline (c0.js f) f ps body)) (hjsc : evalJsCall jsProg (f' + 1) st (c0.js f) args = some (v2, st2)) :
    ∃ ex st1, evalJsStmts jsProg f' { env := bindMany (ps.zip args) (fun _ => .num 0), heap := st.heap, memos := st.memos } body = some (ex, st1) ∧
      ((∃ na, ex = (if dl then .tailCont na else .returned (.tc na)) ∧ evalJsCall jsProg f' { st with heap := st1.heap, memos := st1.memos } (c0.js f) na = some (v2, st2)) ∨
       (∃ v, ex = .returned v ∧ (dl = true ∨ ∀ na, v ≠ .tc na) ∧ v2 = v ∧ st2 = { st with heap := st1.heap, memos := st1.memos })) := by
  rw [evalJsCall_selfTail_eq dl jsProg c0 f ps body st args (f' + 1) hfns hdecl, evalJsSelfTail_succ] at hjsc; dsimp only [evalJsSelfTailStep] at hjsc
  cases h1 : evalJsStmts jsProg f' _ body with | none => rw [h1] at hjsc; cases hjsc | some r =>
  rcases r with ⟨ex, st1⟩; rw [h1] at hjsc; refine ⟨ex, st1, rfl, ?_⟩
  cases ex with
  | next | jumped _ => cases hjsc
  | tailCont na => cases dl with | false => cases hjsc | true => left; exact ⟨na, rfl, by rw [evalJsCall_selfTail_eq true jsProg c0 f ps body { st with heap := st1.heap, memos := st1.memos } na f' hfns hdecl]; exact hjsc⟩
  | returned v => cases v with
    | tc na => cases dl with | false => left; exact ⟨na, rfl, by rw [evalJsCall_selfTail_eq false jsProg c0 f ps body { st with heap := st1.heap, memos := st1.memos } na f' hfns hdecl]; exact hjsc⟩ | true => cases hjsc; right; exact ⟨_, rfl, Or.inl rfl, rfl, rfl⟩
    | _ => cases hjsc; right; exact ⟨_, rfl, Or.inr (fun _ h => nomatch h), rfl, rfl⟩

theorem memoUpdate_eq {prog : IrProg} {c0 : Ctx} {revName : String → Option Name} (hrev : ∀ f d, prog f = some d → revName (c0.js f) = some f) {mIr : Name → MemoCell JsVal} {mJs : String → MemoCell JsVal} (hmEq : ∀ g, prog g ≠ none → mIr g = mJs (c0.js g)) {f : Name} (hf : prog f ≠ none) (v : JsVal) :
    ∀ g, prog g ≠ none → (if g == f then { ok := true, val := some v } else mIr g) = (if c0.js g == c0.js f then { ok := true, val := some v } else mJs (c0.js g)) := fun g hg => by
  by_cases hgf : g = f; (subst hgf; simp)
  have hne : c0.js g ≠ c0.js f := fun heq => by cases hpg : prog g with | none => exact hg hpg | some dg => cases hpf : prog f with | none => exact hf hpf | some df => have e1 := hrev g dg hpg; have e2 := hrev f df hpf; rw [heq, e2] at e1; exact hgf (Option.some.inj e1.symm)
  simp [beq_false_of_ne hgf, beq_false_of_ne hne, hmEq g hg]

abbrev CallPre (prog : IrProg) (c0 : Ctx) (h : CowHeap JsVal) (mIr : Name → MemoCell JsVal) (args : List JsVal) (jsSt : JsState) (P : Prop) : Prop :=
  h = jsSt.heap → (∀ g, prog g ≠ none → mIr g = jsSt.memos (c0.js g)) → (∀ g, (mIr g).val.elim True JsVal.noTc) → (∀ a ∈ args, a.noTc) → (∀ s, jsSt.fns s ≠ none → ∃ j : JoinPointId, s = jp j) → P
abbrev CtxWf (prog : IrProg) (c c0 : Ctx) (P : Prop) : Prop :=
  c.names = c0.names → c.min = c0.min → c.env = c0.env → (∀ sf, c.selfFn = some sf → prog sf ≠ none ∧ c.selfParams.size > 0 ∧ (c.selfParams.toList.map (·.x.idx)).Nodup) → P

abbrev CallSimIJ (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (fuel : Nat) : Prop :=
  ∀ h mIr f args jsSt v1 h1 m1, prog f ≠ none → CallPre prog c0 h mIr args jsSt (evalIrCall prog c0 revName fuel h mIr f args = some (v1, h1, m1) → ∃ fJs st2, evalJsCall jsProg fJs jsSt (c0.js f) args = some (v1, st2) ∧ CallPost prog c0 v1 v1 h1 m1 jsSt st2)
abbrev AppSimIJ (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (fuel : Nat) : Prop :=
  ∀ h mIr fnVal args jsSt v1 h1 m1, fnVal.noTc → CallPre prog c0 h mIr args jsSt (evalIrApp prog c0 revName fuel h mIr fnVal args = some (v1, h1, m1) → ∃ fJs st2, evalJsApp jsProg fJs jsSt fnVal args = some (v1, st2) ∧ CallPost prog c0 v1 v1 h1 m1 jsSt st2)
abbrev BodySimIJ (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (fuel : Nat) : Prop :=
  ∀ c inlineJps recJps allowTailCont b irSt jsSt irO irSt1, CtxWf prog c c0 (BodyWf c prog inlineJps recJps allowTailCont b → StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt → evalIrBody prog c0 revName (inlineJps.map Prod.fst) fuel irSt b = some (irO, irSt1) → ExitMatchIJ prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt b irO irSt1)
abbrev CallSimJI (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (fuel : Nat) : Prop :=
  ∀ h mIr f args jsSt v2 st2, prog f ≠ none → CallPre prog c0 h mIr args jsSt (evalJsCall jsProg fuel jsSt (c0.js f) args = some (v2, st2) → ∃ fIr h1 m1, evalIrCall prog c0 revName fIr h mIr f args = some (v2, h1, m1) ∧ CallPost prog c0 v2 v2 h1 m1 jsSt st2)
abbrev AppSimJI (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (fuel : Nat) : Prop :=
  ∀ h mIr fnVal args jsSt v2 st2, fnVal.noTc → CallPre prog c0 h mIr args jsSt (evalJsApp jsProg fuel jsSt fnVal args = some (v2, st2) → ∃ fIr h1 m1, evalIrApp prog c0 revName fIr h mIr fnVal args = some (v2, h1, m1) ∧ CallPost prog c0 v2 v2 h1 m1 jsSt st2)
abbrev BodySimJI (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (fuel : Nat) : Prop :=
  ∀ c inlineJps recJps allowTailCont b irSt jsSt ex jsSt1, CtxWf prog c c0 (BodyWf c prog inlineJps recJps allowTailCont b → StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt → evalJsStmts jsProg fuel jsSt (lowerBody c b) = some (ex, jsSt1) → ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt b ex jsSt1)

private theorem mem_jmpSlots_fst (ρ : Nat → JsVal) (j : JoinPointId) : ∀ (ls : List Arg) (off : Nat) (nm : String), nm ∈ (((ls.zipIdx off).map fun (a, i) => (s!"_{jp j}_{i}", evalIrArg ρ a)).map Prod.fst) → ∃ k < ls.length, nm = inlineJpSlot j (off + k)
  | [], _, _, h => nomatch h | _ :: rest, off, nm, h => by simp only [List.zipIdx_cons, List.map_cons, List.mem_cons] at h; rcases h with rfl | htl; exact ⟨0, Nat.zero_lt_succ _, by simp [inlineJpSlot]⟩; obtain ⟨k, hk, heq⟩ := mem_jmpSlots_fst ρ j rest (off + 1) nm htl; exact ⟨k + 1, Nat.succ_lt_succ hk, by rw [heq, Nat.add_assoc, Nat.add_comm 1 k]⟩
theorem nodup_jmpSlots (ρ : Nat → JsVal) (j : JoinPointId) : ∀ (ls : List Arg) (off : Nat), (((ls.zipIdx off).map fun (a, i) => (s!"_{jp j}_{i}", evalIrArg ρ a)).map Prod.fst).Nodup
  | [], _ => by simp [List.zipIdx] | _ :: rest, off => by simp only [List.zipIdx_cons, List.map_cons, List.nodup_cons]; refine ⟨fun hm => ?_, nodup_jmpSlots ρ j rest (off + 1)⟩; obtain ⟨k, _, heq⟩ := mem_jmpSlots_fst ρ j rest (off + 1) _ hm; have := (inlineJpSlot_inj heq).2; omega
theorem mem_jmpSlots_getElem (ρ : Nat → JsVal) (j : JoinPointId) : ∀ (ls : List Arg) (off i : Nat) (hi : i < ls.length), (s!"_{jp j}_{off + i}", (ls.map (evalIrArg ρ))[i]'(by simpa using hi)) ∈ ((ls.zipIdx off).map fun (a, k) => (s!"_{jp j}_{k}", evalIrArg ρ a))
  | [], _, i, hi => absurd hi (Nat.not_lt_zero _) | _ :: _, off, 0, _ => by simp [List.zipIdx_cons] | _ :: rest, off, i + 1, hi => by simpa [List.zipIdx_cons, Nat.add_assoc, Nat.add_comm 1 i] using mem_jmpSlots_getElem ρ j rest (off + 1) i (Nat.lt_of_succ_lt_succ hi)
private theorem evalJsAssignsStep_jmp_inline {doCall doApp jsSt envIr} (j : JoinPointId) (henv : ∀ x, envIr x.idx = jsSt.env (v x)) :
    ∀ (ls : List Arg) (off : Nat), evalJsAssignsStep doCall doApp jsSt ((ls.zipIdx off).map fun (a, i) => ("_" ++ jp j ++ "_" ++ i.repr, lowerArg a)) = some ((ls.zipIdx off).map fun (a, i) => ("_" ++ jp j ++ "_" ++ i.repr, evalIrArg envIr a), jsSt)
  | [], _ => rfl
  | a :: rest, off => by dsimp only [List.zipIdx_cons, List.map_cons, evalJsAssignsStep]; rw [evalJsExprStep_lowerArg henv a]; dsimp only; rw [evalJsAssignsStep_jmp_inline j henv rest (off + 1)]
theorem evalIrBody_jmp_not_inline (prog : IrProg) (c : Ctx) (revName : String → Option Name) (inlineJps : List Nat) (f' : Nat) (st : IrState) (j : JoinPointId) (ys : Array Arg) (hnot : j.idx ∉ inlineJps) :
    evalIrBody prog c revName inlineJps (f' + 1) st (.jmp j ys) = match st.jps j.idx with | none => none | some (xs, val, capEnv) => match evalIrBody prog c revName [] f' { env := bindIrParams xs (ys.toList.map (evalIrArg st.env)) capEnv, heap := st.heap, jps := st.jps, memos := st.memos } val with | some (.returned v, st1) => some (.returned v, { st with heap := st1.heap, memos := st1.memos }) | _ => none := by
  dsimp only [evalIrBody, evalIrBodyStep]; rw [if_neg hnot]; rfl
private theorem bindIrParams_toList_eq (xs : Array Param) (as : List JsVal) (capIr : Nat → JsVal) (capJs : String → JsVal) (hnd : (xs.toList.map (·.x.idx)).Nodup) (hcapEq : ∀ x : VarId, capIr x.idx = capJs (v x)) (w : VarId) :
    bindIrParams xs as capIr w.idx = bindMany ((xs.toList.map (v ·.x)).zip as) capJs (v w) := by cases xs with | mk xl => rw [bindIrParams_nodup_eq xl as capIr capJs hnd hcapEq w, zipWith_param_eq_zip xl as]

theorem ExitMatchIJ.rwJsMono {prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt₁ jsSt₂ b₁ b₂ irO irSt1} {f₁ : Nat} (hstep : ∀ f₂, f₁ ≤ f₂ → evalJsStmts jsProg f₂ jsSt₁ (lowerBody c b₁) = evalJsStmts jsProg f₂ jsSt₂ (lowerBody c b₂)) (hex : ExitMatchIJ prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt₂ b₂ irO irSt1) :
    ExitMatchIJ prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt₁ b₁ irO irSt1 := by
  cases irO with
  | jumped _ _ => rcases hex with ⟨f₂, st1, hjs, hok⟩; exact ⟨max f₁ f₂, st1, by rw [hstep _ (Nat.le_max_left _ _)]; exact evalJsStmts_mono (Nat.le_max_right _ _) hjs, hok⟩
  | returned _ => rcases hex with ⟨f₂, st1, hjs, hok⟩ | ⟨hal, f₂, st1, sf, na, m0, fIr', hle, hsf, hna, hjs, hm0, hm0n, hrc⟩; left; exact ⟨max f₁ f₂, st1, by rw [hstep _ (Nat.le_max_left _ _)]; exact evalJsStmts_mono (Nat.le_max_right _ _) hjs, hok⟩; right; exact ⟨hal, max f₁ f₂, st1, sf, na, m0, fIr', hle, hsf, hna, by rw [hstep _ (Nat.le_max_left _ _)]; exact evalJsStmts_mono (Nat.le_max_right _ _) hjs, hm0, hm0n, hrc⟩
theorem ExitMatchJI.rwStep {prog c c0 revName inlineJps recJps allowTailCont irSt₁ irSt₂ b₁ b₂ ex jsSt1 f₁} (hex : ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt₂ b₂ ex jsSt1) (hcomb : ∀ f₂ irO irSt', evalIrBody prog c0 revName (inlineJps.map Prod.fst) f₂ irSt₂ b₂ = some (irO, irSt') → evalIrBody prog c0 revName (inlineJps.map Prod.fst) (max f₁ f₂) irSt₁ b₁ = some (irO, irSt')) :
    ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt₁ b₁ ex jsSt1 := by
  cases ex with
  | next => exact hex
  | jumped _ => rcases hex with ⟨f₂, j, as, st', rfl, hir, hok⟩; exact ⟨_, j, as, st', rfl, hcomb f₂ _ _ hir, hok⟩
  | tailCont _ => rcases hex with ⟨hal, hdl, hnt, sf, m0, hsf, hm0, hm0n, hk⟩; exact ⟨hal, hdl, hnt, sf, m0, hsf, hm0, hm0n, fun fR v h m hrc => let ⟨f₂, st', hir, hok⟩ := hk fR v h m hrc; ⟨_, st', hcomb f₂ _ _ hir, hok⟩⟩
  | returned v => cases v with
    | tc _ => rcases hex with ⟨hal, hdl, hnt, sf, m0, hsf, hm0, hm0n, hk⟩; exact ⟨hal, hdl, hnt, sf, m0, hsf, hm0, hm0n, fun fR v h m hrc => let ⟨f₂, st', hir, hok⟩ := hk fR v h m hrc; ⟨_, st', hcomb f₂ _ _ hir, hok⟩⟩
    | _ => rcases hex with ⟨f₂, st', hir, hok⟩; exact ⟨_, st', hcomb f₂ _ _ hir, hok⟩
theorem ExitMatchJI.rwBody {prog c c0 revName inlineJps recJps allowTailCont irSt₁ irSt₂ b₁ b₂ ex jsSt1} (hex : ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt₂ b₂ ex jsSt1) (hstep : ∀ fIr, evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr irSt₁ b₁ = evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr irSt₂ b₂) :
    ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt₁ b₁ ex jsSt1 := ExitMatchJI.rwStep (f₁ := 0) hex fun f₂ _ _ h => by rw [Nat.zero_max, hstep f₂]; exact h

theorem StatesMatch.pushInlineJp {prog c c0 inlineJps recJps allowTailCont irSt jsSt} (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) (j : JoinPointId) (xs : Array Param) (hnotIn : ∀ ar, (j.idx, ar) ∉ inlineJps) (hnotRec : ∀ ar, (j.idx, ar) ∉ recJps) :
    StatesMatch prog { c with inlineJps := c.inlineJps.insert j.idx xs } c0 ((j.idx, xs.size) :: inlineJps) recJps allowTailCont irSt jsSt :=
  have hc' : ∀ k, ({ c with inlineJps := c.inlineJps.insert j.idx xs } : Ctx).inlineJps.get? k = if k == j.idx then some xs else c.inlineJps.get? k := fun k => by dsimp only; rw [Std.HashMap.get?_insert]; by_cases hjk : j.idx = k; (subst hjk; simp); simp [beq_false_of_ne hjk, beq_false_of_ne (Ne.symm hjk)]
  hsm.withCtx rfl rfl rfl rfl rfl (fun p hp => by rw [hc', beq_false_of_ne (fun heq => hnotRec p.2 (by rcases p with ⟨a, b⟩; dsimp at heq; subst heq; exact hp))]; exact hsm.rec_disj p hp)
    (fun idx ar hm => (List.mem_cons.1 hm).elim (fun h => let ⟨e1, e2⟩ := Prod.mk.inj h; ⟨xs, by rw [hc', e1]; simp, e2.symm⟩) fun htl => let ⟨xs', hxs', har⟩ := hsm.inline_sub idx ar htl; ⟨xs', by rw [hc', beq_false_of_ne fun heq => hnotIn ar (by rw [← heq]; exact htl)]; exact hxs', har⟩)
theorem StatesMatch.bindInlineJp {prog c c0 jpsMap j' inlineJps recJps allowTailCont irStC jsStC} (hsm : StatesMatch prog { c with inlineJps := jpsMap } c0 (j' :: inlineJps) recJps allowTailCont irStC jsStC) (hdisj : ∀ p ∈ recJps, c.inlineJps.get? p.1 = none) (hsub : ∀ idx ar, (idx, ar) ∈ inlineJps → ∃ xs, c.inlineJps.get? idx = some xs ∧ xs.size = ar) (xs : Array Param) (args : List JsVal) (hnd : (xs.toList.map (·.x.idx)).Nodup) (hlen : xs.size = args.length) (hargsNoTc : ∀ a ∈ args, a.noTc) (hnaP : ∀ k, c.nonArr.contains k = true → (bindIrParams xs args irStC.env k).isNonArr = true) :
    StatesMatch prog c c0 inlineJps recJps allowTailCont { irStC with env := bindIrParams xs args irStC.env } (if xs.isEmpty then jsStC else { jsStC with env := bindMany (xs.toList.zipWith (fun p val => (v p.x, val)) args) jsStC.env }) := by
  have hsm' := hsm.withCtx (c' := c) rfl rfl rfl rfl rfl hdisj hsub; by_cases hemp : xs.isEmpty = true
  · obtain rfl : xs = #[] := Array.isEmpty_iff.1 hemp; obtain rfl : args = [] := List.length_eq_zero_iff.1 (by simpa using hlen.symm); simpa [bindIrParams] using hsm'
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte]; exact { hsm' with env_eq := fun w => (by cases xs with | mk xl => exact bindIrParams_nodup_eq xl args irStC.env jsStC.env hnd hsm.env_eq w), env_noTc := bindIrParams_noTc xs.toList args irStC.env hsm.env_noTc hargsNoTc, nonArr_ok := hnaP }
theorem StatesMatch.pushRecJp {prog c c0 inlineJps recJps allowTailCont irSt jsSt} (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) (hnames : c.names = c0.names) (hmin : c.min = c0.min) (henv : c.env = c0.env) (j : JoinPointId) (xs : Array Param) (val : FnBody) (hnd : (xs.toList.map (·.x.idx)).Nodup) (hnotRec : ∀ ar, (j.idx, ar) ∉ recJps) (hcNone : c.inlineJps.get? j.idx = none) (hwfVal : BodyWf c prog [] ((j.idx, xs.size) :: recJps) (if c.directLoop then false else allowTailCont) val) :
    StatesMatch prog c c0 inlineJps ((j.idx, xs.size) :: recJps) allowTailCont { irSt with jps := fun k => if k == j.idx then some (xs, val, irSt.env) else irSt.jps k } { jsSt with fns := bindEnv jsSt.fns (jp j) (some (xs.toList.map (v ·.x), lowerBody c val, jsSt.env)) } :=
  have hrecNodup : (((j.idx, xs.size) :: recJps).map Prod.fst).Nodup := List.nodup_cons.2 ⟨fun hm => by obtain ⟨⟨idx, sz⟩, hp, hpe⟩ := List.mem_map.1 hm; exact hnotRec sz (by dsimp at hpe; subst hpe; exact hp), hsm.rec_nodup⟩
  { hsm with
    fns_only_jp := fun s hs => (by by_cases hsj : s = jp j; exact ⟨j, hsj⟩; (simp only [bindEnv, beq_false_of_ne hsj] at hs; exact hsm.fns_only_jp s hs)),
    jps_none := fun j' => (by by_cases hjj : j' = j; (subst hjj; simp [bindEnv]); have hne : j'.idx ≠ j.idx := fun h => hjj (jp_ext h); simp [beq_false_of_ne hne, bindEnv, beq_false_of_ne (fun h => hne (jp_inj h)), hsm.jps_none j']),
    jps_some := fun j' xs' val' capIr' hj' hmem' => (by
      by_cases hjj : j' = j
      · subst hjj; simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hj'; obtain ⟨rfl, rfl, rfl⟩ := hj'; rw [suffixFrom_head]
        have hcEq : ({ c with names := c0.names, min := c0.min, env := c0.env, inlineJps := c.inlineJps } : Ctx) = c := by cases c; simp_all
        exact ⟨c.inlineJps, jsSt.env, by simp [bindEnv, hcEq], fun p hp => (List.mem_cons.1 hp).elim (fun h => by subst h; exact hcNone) (hsm.rec_disj _), hsm.env_eq, hsm.env_noTc, hsm.nonArr_ok, hnd, hcEq.symm ▸ hwfVal⟩
      · have hne : j'.idx ≠ j.idx := fun h => hjj (jp_ext h); simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte] at hj'
        obtain ⟨jm, cj, s1, rest⟩ := hsm.jps_some j' xs' val' capIr' hj' ((List.mem_cons.1 hmem').elim (fun h => absurd (Prod.mk.inj h).1 hne) id)
        rw [show suffixFrom j'.idx ((j.idx, xs.size) :: recJps) = suffixFrom j'.idx recJps by simp [suffixFrom, beq_false_of_ne hne.symm]]; exact ⟨jm, cj, by simp [bindEnv, beq_false_of_ne (fun h => hne (jp_inj h)), s1], rest⟩),
    rec_ar := fun j' ar xs' val' capIr' hmem' hj' => (by
      by_cases hjj : j' = j
      · subst hjj; simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hj'; obtain ⟨rfl, rfl, rfl⟩ := hj'; exact (nodup_fst_eq hrecNodup hmem' (.head _) rfl).symm
      · have hne : j'.idx ≠ j.idx := fun h => hjj (jp_ext h); simp only [beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte] at hj'; exact hsm.rec_ar j' ar xs' val' capIr' ((List.mem_cons.1 hmem').elim (fun h => absurd (Prod.mk.inj h).1 hne) id) hj'),
    rec_nodup := hrecNodup, rec_disj := fun p hp => (List.mem_cons.1 hp).elim (fun h => by subst h; exact hcNone) (hsm.rec_disj p) }
theorem StatesMatch.enterRecJp {prog c c0 inlineJps recJps allowTailCont irSt jsSt} (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) (hprogNA : ∀ (nonArr : Std.HashSet Nat) xs as ρ k, nonArr.contains k = true → (∀ m, nonArr.contains m = true → (ρ m).isNonArr = true) → (bindIrParams xs as ρ k).isNonArr = true) (hselfNodup : ∀ sf, c.selfFn = some sf → prog sf ≠ none ∧ c.selfParams.size > 0 ∧ (c.selfParams.toList.map (·.x.idx)).Nodup) {j : JoinPointId} {ys : Array Arg} {xs : Array Param} {val : FnBody} {capIr : Nat → JsVal} (hrec : (j.idx, ys.size) ∈ recJps) (hjir : irSt.jps j.idx = some (xs, val, capIr)) :
    ∃ cVal capJs, jsSt.fns (jp j) = some (xs.toList.map (v ·.x), lowerBody cVal val, capJs) ∧ cVal.names = c0.names ∧ cVal.min = c0.min ∧ cVal.env = c0.env ∧ cVal.selfFn = c.selfFn ∧ cVal.selfParams = c.selfParams ∧ cVal.directLoop = c.directLoop ∧ (∀ sf, cVal.selfFn = some sf → prog sf ≠ none ∧ cVal.selfParams.size > 0 ∧ (cVal.selfParams.toList.map (·.x.idx)).Nodup) ∧ BodyWf cVal prog [] (suffixFrom j.idx recJps) (if cVal.directLoop then false else allowTailCont) val ∧
      StatesMatch prog cVal c0 [] (suffixFrom j.idx recJps) (if cVal.directLoop then false else allowTailCont) { env := bindIrParams xs (ys.toList.map (evalIrArg irSt.env)) capIr, heap := irSt.heap, jps := irSt.jps, memos := irSt.memos } { env := bindMany ((xs.toList.map (v ·.x)).zip (ys.toList.map (evalIrArg irSt.env))) capJs, heap := jsSt.heap, fns := jsSt.fns, memos := jsSt.memos } := by
  obtain ⟨jpsMap, capJs, hjjs, hcvInNone, hcapEq, hcapNoTc, hcapNA, hnd, hwfVal⟩ := hsm.jps_some j xs val capIr hjir ((hsm.rec_ar j ys.size xs val capIr hrec hjir) ▸ hrec)
  have hargsNoTc : ∀ a ∈ ys.toList.map (evalIrArg irSt.env), a.noTc := fun a ha => by rcases List.mem_map.1 ha with ⟨a', _, rfl⟩; exact evalIrArg_noTc hsm.env_noTc a'
  let cVal : Ctx := { c with names := c0.names, min := c0.min, env := c0.env, inlineJps := jpsMap }
  refine ⟨cVal, capJs, hjjs, rfl, rfl, rfl, rfl, rfl, rfl, hselfNodup, hwfVal,
    { env_eq := bindIrParams_toList_eq xs _ capIr capJs hnd hcapEq, heap_eq := hsm.heap_eq, memos_eq := hsm.memos_eq, memos_noTc := hsm.memos_noTc, env_noTc := bindIrParams_noTc xs.toList _ capIr hcapNoTc hargsNoTc,
      nonArr_ok := fun k hk => hprogNA c.nonArr xs _ capIr k hk hcapNA, fns_only_jp := hsm.fns_only_jp, jps_none := hsm.jps_none,
      jps_some := fun j' xs' val' capIr' hj' hmem => (by
        have hsuf := suffixFrom_idem hsm.rec_nodup hmem
        have hdl : (if c.directLoop then false else if c.directLoop then false else allowTailCont) = if c.directLoop then false else allowTailCont := by cases c.directLoop <;> rfl
        simpa only [cVal, hsuf, hdl] using hsm.jps_some j' xs' val' capIr' hj' (mem_suffixFrom_mem hmem)),
      rec_ar := fun j' ar xs' val' capIr' hmem hj' => hsm.rec_ar j' ar xs' val' capIr' (mem_suffixFrom_mem hmem) hj', rec_nodup := nodup_suffixFrom hsm.rec_nodup, rec_disj := hcvInNone, inline_sub := fun _ _ hm => nomatch hm }⟩

def refMarkPair (h : CowHeap JsVal) : List JsVal → JsVal × CowHeap JsVal | [.arr id] => let p := h.refMark id; (.num p.1, p.2) | _ => (.num 0, h)
theorem StatesMatch.updRefMark {prog c c0 inlineJps recJps allowTailCont irSt jsSt} (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) (x : VarId) (vs : List JsVal) :
    StatesMatch prog c c0 inlineJps recJps allowTailCont { irSt with env := fun k => if k == x.idx then (refMarkPair irSt.heap vs).1 else irSt.env k, heap := (refMarkPair irSt.heap vs).2 } { jsSt with env := bindEnv jsSt.env (v x) (refMarkPair jsSt.heap vs).1, heap := (refMarkPair jsSt.heap vs).2 } := by
  cases vs with | cons v0 rest => (cases v0 with | arr _ => (cases rest with | nil => exact { hsm with env_eq := fun w => (by rw [hsm.heap_eq]; exact env_eq_update hsm.env_eq x _ w), heap_eq := by rw [hsm.heap_eq], env_noTc := env_noTc_bind hsm.env_noTc (noTc_num _), nonArr_ok := bindEnv_nonArr_of_expr c irSt.env x.idx _ hsm.nonArr_ok (fun _ => rfl) } | _ => exact hsm.updVar x (noTc_num 0) fun _ => rfl) | _ => exact hsm.updVar x (noTc_num 0) fun _ => rfl) | nil => exact hsm.updVar x (noTc_num 0) fun _ => rfl
theorem evalJsStmts_inlineJp_post (jsProg : JsProg) (fJs : Nat) (jsStC : JsState) (j j' : JoinPointId) (hj'eq : j' = j) (args : List JsVal) (xs : Array Param) (hlen : xs.size = args.length) (hslots : ∀ i (hi : i < args.length), jsStC.env (inlineJpSlot j' i) = args[i]'hi) (rhs : List JsStmt) :
    evalJsStmts jsProg fJs jsStC ((if xs.isEmpty then [] else [JsStmt.letBinds (xs.toList.zipIdx.map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}"))]) ++ rhs) = evalJsStmts jsProg fJs (if xs.isEmpty then jsStC else { jsStC with env := bindMany (xs.toList.zipWith (fun p val => (v p.x, val)) args) jsStC.env }) rhs := by
  by_cases hemp : xs.isEmpty = true
  · simp only [hemp, ↓reduceIte, List.nil_append]
  · have hzip := evalJsAssignsStep_zipIdx_vars (doCall := evalJsCall jsProg fJs) (doApp := evalJsApp jsProg fJs) (st := jsStC) j args xs.toList 0 (by simp [hlen]) fun i hi => by simpa [← hj'eq] using hslots i (by simp at hi; omega)
    rw [if_neg hemp, if_neg hemp]; dsimp only [List.cons_append, List.nil_append, evalJsStmts, evalJsStmtsStep, evalJsStmtStep]; rw [hzip]; rfl

theorem evalIrAlts_sim_ij {prog c c0 jsProg revName fuel inlineJps recJps allowTailCont irSt jsSt irO irSt1} {x : VarId} (arms : List Alt) (hawf : AltsWf c prog inlineJps recJps allowTailCont arms)
    (ih : ∀ arm ∈ arms, BodyWf c prog inlineJps recJps allowTailCont arm.body → evalIrBody prog c0 revName (inlineJps.map Prod.fst) fuel irSt arm.body = some (irO, irSt1) → ExitMatchIJ prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt arm.body irO irSt1)
    (haev : evalIrAlts prog c0 revName (inlineJps.map Prod.fst) fuel irSt (jsTag (irSt.env x.idx)) arms = some (irO, irSt1)) :
    match irO with
    | .jumped j args => ∃ fJs jsSt1, evalJsArms jsProg fJs jsSt (jsTag (irSt.env x.idx)) (lowerAlts c arms) = some (.jumped (jp j), jsSt1) ∧ ExitJmpOk prog c c0 inlineJps recJps allowTailCont j args irSt1 jsSt1
    | .returned val => (∃ fJs jsSt1, evalJsArms jsProg fJs jsSt (jsTag (irSt.env x.idx)) (lowerAlts c arms) = some (.returned val, jsSt1) ∧ ExitRetOk prog c0 val irSt1 jsSt1) ∨
        (allowTailCont = true ∧ ∃ fJs jsSt1 sf nextArgs m₀ fIr', fIr' ≤ fuel ∧ c.selfFn = some sf ∧ (∀ a ∈ nextArgs, a.noTc) ∧ evalJsArms jsProg fJs jsSt (jsTag (irSt.env x.idx)) (lowerAlts c arms) = some (if c.directLoop then .tailCont nextArgs else .returned (.tc nextArgs), jsSt1) ∧ (∀ f, prog f ≠ none → m₀ f = jsSt1.memos (c0.js f)) ∧ (∀ f, (m₀ f).val.elim True JsVal.noTc) ∧ evalIrCall prog c0 revName fIr' jsSt1.heap m₀ sf nextArgs = some (val, irSt1.heap, irSt1.memos)) := by
  induction arms with | nil => cases haev | cons arm rest ihA =>
    cases arm with
    | default bArm => have heq : ∀ fJs, evalJsArms jsProg fJs jsSt (jsTag (irSt.env x.idx)) (lowerAlts c (.default bArm :: rest)) = evalJsStmts jsProg fJs jsSt (lowerBody c bArm) := fun _ => rfl; cases irO <;> simpa only [heq] using ih (.default bArm) (.head _) hawf.1 haev
    | ctor info bArm =>
      dsimp only [evalIrAlts, evalIrAltsStep] at haev; by_cases hc : (info.cidx == jsTag (irSt.env x.idx)) = true
      · rw [if_pos hc] at haev; have heq : ∀ fJs, evalJsArms jsProg fJs jsSt (jsTag (irSt.env x.idx)) (lowerAlts c (.ctor info bArm :: rest)) = evalJsStmts jsProg fJs jsSt (lowerBody c bArm) := fun _ => by dsimp only [lowerAlts, evalJsArms, evalJsArmsStep]; rw [if_pos hc]; rfl
        cases irO <;> simpa only [heq] using ih (.ctor info bArm) (.head _) hawf.1 haev
      · rw [if_neg hc] at haev; have heq : ∀ fJs, evalJsArms jsProg fJs jsSt (jsTag (irSt.env x.idx)) (lowerAlts c (.ctor info bArm :: rest)) = evalJsArms jsProg fJs jsSt (jsTag (irSt.env x.idx)) (lowerAlts c rest) := fun _ => by dsimp only [lowerAlts, evalJsArms, evalJsArmsStep]; rw [if_neg hc]
        cases irO <;> simpa only [heq] using ihA hawf.2 (fun a hm => ih a (.tail _ hm)) haev

theorem evalJsArms_sim_ji {prog c c0 jsProg revName fuel inlineJps recJps allowTailCont irSt jsSt ex jsSt1} {x : VarId} (arms : List Alt) (hawf : AltsWf c prog inlineJps recJps allowTailCont arms)
    (ih : ∀ arm ∈ arms, BodyWf c prog inlineJps recJps allowTailCont arm.body → evalJsStmts jsProg fuel jsSt (lowerBody c arm.body) = some (ex, jsSt1) → ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt arm.body ex jsSt1)
    (haev : evalJsArms jsProg fuel jsSt (jsTag (irSt.env x.idx)) (lowerAlts c arms) = some (ex, jsSt1)) :
    ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt (.case default x default arms.toArray) ex jsSt1 := by
  induction arms with | nil => cases haev | cons arm rest ihA =>
    cases arm with
    | default bArm => exact ExitMatchJI.rwBody (ih (.default bArm) (.head _) hawf.1 haev) fun _ => rfl
    | ctor info bArm =>
      dsimp only [lowerAlts, evalJsArms, evalJsArmsStep] at haev; by_cases hc : (info.cidx == jsTag (irSt.env x.idx)) = true
      · rw [if_pos hc] at haev; exact ExitMatchJI.rwBody (ih (.ctor info bArm) (.head _) hawf.1 haev) fun _ => by dsimp only [evalIrBody, evalIrBodyStep, evalIrAltsStep]; rw [if_pos hc]; rfl
      · rw [if_neg hc] at haev; exact ExitMatchJI.rwBody (ihA hawf.2 (fun a hm => ih a (.tail _ hm)) haev) fun _ => by dsimp only [evalIrBody, evalIrBodyStep, evalIrAltsStep]; rw [if_neg hc]

/-! ### Unified Lockstep & Shared Simulation Step Lemmas -/

def Lockstep (prog : IrProg) (c c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name)
    (inlineJps recJps' : List (Nat × Nat)) (allowTailCont : Bool) (irSt : IrState) (jsSt : JsState) (b cont : FnBody) : Prop :=
  ∃ irSt' jsSt',
    (∀ fIr, evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr irSt b = evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr irSt' cont) ∧
    (∀ fJs, evalJsStmts jsProg fJs jsSt (lowerBody c b) = evalJsStmts jsProg fJs jsSt' (lowerBody c cont)) ∧
    StatesMatch prog c c0 inlineJps recJps' allowTailCont irSt' jsSt'

section LockstepLemmas
variable {prog : IrProg} {c c0 : Ctx} {jsProg : JsProg} {revName : String → Option Name}
  {inlineJps recJps : List (Nat × Nat)} {allowTailCont : Bool} {irSt : IrState} {jsSt : JsState}

theorem ExitMatchIJ.ofLockstep {fuel b cont irO irSt1} (L : Lockstep prog c c0 jsProg revName inlineJps recJps allowTailCont irSt jsSt b cont)
    (hcont : ∀ irSt' jsSt', StatesMatch prog c c0 inlineJps recJps allowTailCont irSt' jsSt' → evalIrBody prog c0 revName (inlineJps.map Prod.fst) fuel irSt' cont = some (irO, irSt1) → ExitMatchIJ prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt' cont irO irSt1)
    (hev : evalIrBody prog c0 revName (inlineJps.map Prod.fst) fuel irSt b = some (irO, irSt1)) : ExitMatchIJ prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt b irO irSt1 := by
  rcases L with ⟨irSt', jsSt', hir, hjs, hsm'⟩; exact ExitMatchIJ.rwJsMono (f₁ := 0) (fun fJs _ => hjs fJs) (hcont irSt' jsSt' hsm' (hir fuel ▸ hev))
theorem ExitMatchJI.ofLockstep {fuel b cont ex jsSt1} (L : Lockstep prog c c0 jsProg revName inlineJps recJps allowTailCont irSt jsSt b cont)
    (hcont : ∀ irSt' jsSt', StatesMatch prog c c0 inlineJps recJps allowTailCont irSt' jsSt' → evalJsStmts jsProg fuel jsSt' (lowerBody c cont) = some (ex, jsSt1) → ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt' cont ex jsSt1)
    (hev : evalJsStmts jsProg fuel jsSt (lowerBody c b) = some (ex, jsSt1)) : ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt b ex jsSt1 := by
  rcases L with ⟨irSt', jsSt', hir, hjs, hsm'⟩; exact ExitMatchJI.rwBody (hcont irSt' jsSt' hsm' (hjs fuel ▸ hev)) hir

theorem lockstep_stmt {b cont : FnBody} (hwf : BodyWf c prog inlineJps recJps allowTailCont b)
    (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt)
    (hsimple : match b with | .set _ _ _ c' | .setTag _ _ c' | .uset _ _ _ c' | .sset _ _ _ _ _ c' | .dec _ _ _ _ c' | .del _ c' | .inc _ _ _ _ c' => c' = cont | _ => False) :
    BodyWf c prog inlineJps recJps allowTailCont cont ∧ Lockstep prog c c0 jsProg revName inlineJps recJps allowTailCont irSt jsSt b cont := by
  have updVar : ∀ {b : FnBody} (x : VarId) (val : JsVal), val.noTc → (c.nonArr.contains x.idx = true → val.isNonArr = true) →
      (∀ fIr, evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr irSt b = evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr { irSt with env := fun k => if k == x.idx then val else irSt.env k } cont) →
      (∀ fJs, evalJsStmts jsProg fJs jsSt (lowerBody c b) = evalJsStmts jsProg fJs { jsSt with env := bindEnv jsSt.env (v x) val } (lowerBody c cont)) →
      Lockstep prog c c0 jsProg revName inlineJps recJps allowTailCont irSt jsSt b cont := fun x val hnt hna hir hjs => ⟨_, _, hir, hjs, hsm.updVar x hnt hna⟩
  have rcDec : ∀ {b : FnBody} (x : VarId) (n : Nat),
      lowerBody c b = (if c.nonArr.contains x.idx then lowerBody c cont else [.decRef (v x) n] ++ lowerBody c cont) →
      (∀ fIr, evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr irSt b = evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr { irSt with heap := irSt.heap.rcDec (irSt.env x.idx).toRcVal n } cont) →
      Lockstep prog c c0 jsProg revName inlineJps recJps allowTailCont irSt jsSt b cont := fun x n hlow hir =>
    if hna : c.nonArr.contains x.idx = true then
      ⟨irSt, jsSt, fun fIr => by rw [hir fIr, rcDec_nonArr_noop_isNonArr irSt.heap (irSt.env x.idx) n (hsm.nonArr_ok _ hna)], fun _ => by rw [hlow, if_pos hna], hsm⟩
    else ⟨_, { jsSt with heap := jsSt.heap.rcDec (jsSt.env (v x)).toRcVal n }, hir, fun _ => by rw [hlow, if_neg hna]; rfl, hsm.updHeap (by rw [hsm.heap_eq, hsm.env_eq x])⟩
  cases b with
  | set x i y c' =>
      subst hsimple; rw [BodyWf] at hwf; exact ⟨hwf, updVar x _
        (by generalize irSt.env x.idx = o, hsm.env_noTc x.idx = ho; cases o with | ctorObj => rw [JsVal.noTc] at ho; rw [JsVal.setField, JsVal.noTc]; exact ⟨fun v hv => (List.mem_or_eq_of_mem_set hv).elim (ho.1 v) (· ▸ evalIrArg_noTc hsm.env_noTc y), ho.2⟩ | _ => exact ho)
        (fun hm => by generalize irSt.env x.idx = o, hsm.nonArr_ok _ hm = ho; cases o <;> exact ho)
        (fun _ => rfl) (fun _ => by dsimp only [lowerBody, evalJsStmts, evalJsStmtsStep, evalJsStmtStep]; rw [evalJsExprStep_lowerArg hsm.env_eq y, hsm.env_eq x])⟩
  | setTag x cidx c' =>
      subst hsimple; rw [BodyWf] at hwf; exact ⟨hwf, updVar x _
        (by generalize irSt.env x.idx = o, hsm.env_noTc x.idx = ho; cases o with | ctorObj => rw [JsVal.noTc] at ho; rw [JsVal.setTag, JsVal.noTc]; exact ho | _ => exact noTc_num cidx)
        (fun _ => by cases irSt.env x.idx <;> rfl) (fun _ => rfl) (fun _ => by dsimp only [lowerBody, evalJsStmts, evalJsStmtsStep, evalJsStmtStep]; rw [hsm.env_eq x])⟩
  | uset x i y c' =>
      subst hsimple; rw [BodyWf] at hwf; exact ⟨hwf, updVar x _
        (by generalize irSt.env x.idx = o, hsm.env_noTc x.idx = ho; cases o with | ctorObj => rw [JsVal.noTc] at ho; rw [JsVal.setU, JsVal.noTc]; exact ⟨ho.1, noTcPairs_set ho.2.1 (hsm.env_noTc y.idx), ho.2.2⟩ | _ => exact ho)
        (fun hm => by generalize irSt.env x.idx = o, hsm.nonArr_ok _ hm = ho; cases o <;> exact ho)
        (fun _ => rfl) (fun _ => by dsimp only [lowerBody, evalJsStmts, evalJsStmtsStep, evalJsStmtStep, evalJsExprStep]; rw [hsm.env_eq x, hsm.env_eq y])⟩
  | sset x n off y ty c' =>
      subst hsimple; rw [BodyWf] at hwf; exact ⟨hwf, updVar x _
        (by generalize irSt.env x.idx = o, hsm.env_noTc x.idx = ho; cases o with | ctorObj => rw [JsVal.noTc] at ho; rw [JsVal.setS, JsVal.noTc]; exact ⟨ho.1, ho.2.1, noTcPairs_set ho.2.2 (hsm.env_noTc y.idx)⟩ | _ => exact ho)
        (fun hm => by generalize irSt.env x.idx = o, hsm.nonArr_ok _ hm = ho; cases o <;> exact ho)
        (fun _ => rfl) (fun _ => by dsimp only [lowerBody, evalJsStmts, evalJsStmtsStep, evalJsStmtStep, evalJsExprStep]; rw [hsm.env_eq x, hsm.env_eq y])⟩
  | dec x n _ _ c' => subst hsimple; rw [BodyWf] at hwf; exact ⟨hwf, rcDec x n rfl fun _ => rfl⟩
  | del x c' => subst hsimple; rw [BodyWf] at hwf; exact ⟨hwf, rcDec x 1 rfl fun _ => rfl⟩
  | inc x n cf bf c' =>
      subst hsimple; rw [BodyWf] at hwf; refine ⟨hwf.1, ?_⟩
      by_cases hna : c.nonArr.contains x.idx = true
      · exact ⟨irSt, jsSt, fun _ => by dsimp only [evalIrBody, evalIrBodyStep]; rw [rcInc_nonArr_noop_isNonArr irSt.heap (irSt.env x.idx) n (hsm.nonArr_ok _ hna)], fun _ => by dsimp only [lowerBody]; simp only [hna, Bool.or_true, ↓reduceIte], hsm⟩
      · rcases hwf.2 with hcont | hnt; exact absurd hcont hna
        have hl : lowerBody c (.inc x n cf bf c') = if n == 0 then lowerBody c c' else [.incRef (v x) n] ++ lowerBody c c' := by
          dsimp only [lowerBody]; cases hp : c.projSrc.get? x.idx with
          | none => simp [Bool.eq_false_iff.2 hna] | some p => simp only [hp] at hnt; simp [Bool.eq_false_iff.2 hna, (by cases h : hasDecOf p c' <;> simp [h] at hnt; rfl : hasDecOf p c' = false)]
        by_cases hn0 : n = 0; · subst hn0; exact ⟨irSt, jsSt, fun _ => by dsimp only [evalIrBody, evalIrBodyStep]; rw [CowHeap.rcInc_zero], fun _ => by rw [hl]; rfl, hsm⟩
        exact ⟨{ irSt with heap := irSt.heap.rcInc (irSt.env x.idx).toRcVal n }, { jsSt with heap := jsSt.heap.rcInc (jsSt.env (v x)).toRcVal n }, fun _ => rfl, fun _ => by rw [hl, if_neg (by rw [beq_false_of_ne hn0]; decide)]; rfl, hsm.updHeap (by rw [hsm.heap_eq, hsm.env_eq x])⟩
  | _ => exact False.elim hsimple

theorem lockstep_vdecl {x : VarId} {ty : IRType} {e : IR.Expr} {cont : FnBody} (hprog : ProgLowered prog c0 jsProg revName) (hnames : c.names = c0.names) (henv : c.env = c0.env)
    (hwf : BodyWf c prog inlineJps recJps allowTailCont (.vdecl x ty e cont)) (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt)
    (hsimple : match e with | .fap f _ => f = `Qed.refMark | .ap .. => False | _ => True) :
    BodyWf c prog inlineJps recJps allowTailCont cont ∧ Lockstep prog c c0 jsProg revName inlineJps recJps allowTailCont irSt jsSt (.vdecl x ty e cont) cont := by
  rw [BodyWf] at hwf; rcases hwf with ⟨hwfc, hwe⟩; refine ⟨hwfc, ?_⟩
  have pureStep : ∀ (e : IR.Expr), (match e with | .fap _ _ | .ap _ _ | .isShared _ => False | _ => True) → ExprWf c prog allowTailCont x cont e →
      Lockstep prog c c0 jsProg revName inlineJps recJps allowTailCont irSt jsSt (.vdecl x ty e cont) cont := fun e hpure hwe' => by
    have hnoTcV := evalIrPure_noTc c0 ty hsm.env_noTc e fun f' ys' he => by subst he; rcases hwe' with ⟨d, hd⟩; exact (hprog.fn_disjoint (c0.js f') f' (hprog.rev_ok f' d hd)).1
    have hnaV : c.nonArr.contains x.idx = true → (evalIrPure c0 ty irSt.env e).isNonArr = true := fun hx => by
      cases e <;> first | exact False.elim hpure | exact evalIrPure_ctor_isNonArr c0 ty irSt.env _ trivial | exact hprog.nonArr_pure c.nonArr irSt.env ty x _ hx hsm.nonArr_ok
    have hstep : lowerBody c (.vdecl x ty e cont) = .letVar (v x) (lowerExpr c ty e) :: lowerBody c cont := by cases e <;> first | exact False.elim hpure | rfl
    exact ⟨_, _, fun _ => by cases e <;> first | exact False.elim hpure | rfl,
      fun _ => by rw [hstep]; dsimp only [evalJsStmts, evalJsStmtsStep, evalJsStmtStep]; rw [evalJsExprStep_lowerPure c ty hsm.env_eq e hpure, evalIrPure_ctx_eq c c0 hnames henv], hsm.updVar x hnoTcV hnaV⟩
  cases e with
  | fap f ys =>
      dsimp only at hsimple; subst hsimple; simp only [ExprWf, beq_self_eq_true, ↓reduceIte] at hwe
      have hnotSelf : (c.selfFn == some `Qed.refMark && retsVar x cont) = false := by by_cases hc : c.selfFn == some `Qed.refMark; exact absurd (eq_of_beq hc) hwe; simp [Bool.eq_false_iff.2 hc]
      let vs := ys.toList.filterMap (refMarkArg irSt.env)
      refine ⟨{ irSt with env := fun k => if k == x.idx then (refMarkPair irSt.heap vs).1 else irSt.env k, heap := (refMarkPair irSt.heap vs).2 },
        { jsSt with env := bindEnv jsSt.env (v x) (refMarkPair jsSt.heap vs).1, heap := (refMarkPair jsSt.heap vs).2 }, fun _ => ?_, fun _ => ?_, hsm.updRefMark x vs⟩
      · dsimp only [evalIrBody, evalIrBodyStep]; rw [if_pos (beq_self_eq_true _)]; dsimp only [vs]; cases ys.toList.filterMap (refMarkArg irSt.env) with | nil => rfl | cons v0 rest => cases v0 with | arr _ => cases rest <;> rfl | _ => rfl
      · dsimp only [lowerBody]; rw [if_neg (by rw [hnotSelf]; decide)]; dsimp only [lowerExpr, lowerApp, evalJsStmts, evalJsStmtsStep, evalJsStmtStep]
        rw [if_pos (beq_self_eq_true _)]; dsimp only [evalJsExprStep]; rw [evalJsExprListStep_refMark hsm.env_eq _ (fun a => by cases a <;> rfl) ys.toList]
        dsimp only [vs]; cases ys.toList.filterMap (refMarkArg irSt.env) with | nil => rfl | cons v0 rest => cases v0 with | arr _ => cases rest <;> rfl | _ => rfl
  | ap _ _ => exact False.elim hsimple
  | isShared y =>
      exact ⟨_, _, fun _ => rfl, fun _ => by dsimp only [lowerBody, lowerExpr, evalJsStmts, evalJsStmtsStep, evalJsStmtStep, evalJsExprStep, evalJsExprListStep]; rw [hsm.env_eq y, hsm.heap_eq]; rfl, hsm.updVar x (noTc_num _) fun _ => rfl⟩
  | _ => exact pureStep _ trivial hwe
theorem lockstep_rec_jdecl (hnames : c.names = c0.names) (hmin : c.min = c0.min) (henv : c.env = c0.env)
    (j : JoinPointId) (xs : Array Param) (val cont : FnBody) (hjmpF : (!hasJmpTo j val) = false) (hnd : (xs.toList.map (·.x.idx)).Nodup)
    (hnotRec : ∀ ar, (j.idx, ar) ∉ recJps) (hcNone : c.inlineJps.get? j.idx = none)
    (hwfVal : BodyWf c prog [] ((j.idx, xs.size) :: recJps) (if c.directLoop then false else allowTailCont) val) (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) :
    Lockstep prog c c0 jsProg revName inlineJps ((j.idx, xs.size) :: recJps) allowTailCont irSt jsSt (.jdecl j xs val cont) cont :=
  ⟨_, _, fun _ => by dsimp only [evalIrBody, evalIrBodyStep]; rw [if_neg (by rw [hjmpF]; decide)],
    fun _ => by dsimp only [lowerBody]; rw [if_neg (by rw [hjmpF]; decide)]; rfl,
    hsm.pushRecJp hnames hmin henv j xs val hnd hnotRec hcNone hwfVal⟩

theorem inlineJmp_step {j : JoinPointId} {ys : Array Arg} (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) (hin : (j.idx, ys.size) ∈ inlineJps) :
    let jsSt' : JsState := { jsSt with env := bindMany ((ys.toList.zipIdx 0).map fun (a, i) => ("_" ++ jp j ++ "_" ++ i.repr, evalIrArg irSt.env a)) jsSt.env }
    (j.idx ∈ inlineJps.map Prod.fst) ∧ (∀ fJs, evalJsStmts jsProg fJs jsSt (lowerBody c (.jmp j ys)) = some (.jumped (jp j), jsSt')) ∧
    ExitJmpOk prog c c0 inlineJps recJps allowTailCont j (ys.toList.map (evalIrArg irSt.env)) irSt jsSt' := by
  obtain ⟨xs, hxs, _⟩ := hsm.inline_sub j.idx ys.size hin
  refine ⟨List.mem_map.2 ⟨(j.idx, ys.size), hin, rfl⟩,
    fun fJs => by dsimp only [lowerBody]; rw [show c.inlineJps.get? j.idx = some xs from hxs]; dsimp only [evalJsStmts, evalJsStmtsStep, evalJsStmtStep]; simp only [toString_str_eq, Nat.toString_eq_repr]; rw [evalJsAssignsStep_jmp_inline j hsm.env_eq ys.toList 0],
    by simpa using hin, fun i hi => by simpa using bindMany_lookup_nodup _ jsSt.env (nodup_jmpSlots irSt.env j ys.toList 0) _ _ (mem_jmpSlots_getElem irSt.env j ys.toList 0 i (by simpa using hi)),
    fun a ha => by rcases List.mem_map.1 ha with ⟨a', _, rfl⟩; exact evalIrArg_noTc hsm.env_noTc a',
    { hsm with env_eq := fun w => (by rw [hsm.env_eq w]; symm; exact bindMany_lookup_not_mem _ jsSt.env (v w) (fun p hp heq => by rcases List.mem_map.1 hp with ⟨⟨_, k⟩, _, rfl⟩; exact list_take_ne_x_append_digits w.idx j.idx k heq.symm)) }⟩
end LockstepLemmas

theorem caseScrut_eq (jsProg : JsProg) (c : Ctx) (tid : Name) (x : VarId) (xType : IRType) (alts : Array Alt) {irSt : IrState} {jsSt : JsState} (henv : ∀ w : VarId, irSt.env w.idx = jsSt.env (v w)) (fJs : Nat) :
    evalJsStmts jsProg fJs jsSt (lowerBody c (.case tid x xType alts)) = evalJsArms jsProg fJs jsSt (jsTag (irSt.env x.idx)) (lowerAlts c alts.toList) := by
  have hscr : evalJsExprStep (evalJsCall jsProg fJs) (evalJsApp jsProg fJs) jsSt (if xType.isObj then .call "$.tag" [.var (v x)] else .var (v x)) = some (if xType.isObj then .num (jsTag (jsSt.env (v x))) else jsSt.env (v x), jsSt) := by cases xType.isObj <;> rfl
  have htag : jsTag (if xType.isObj then .num (jsTag (jsSt.env (v x))) else jsSt.env (v x)) = jsTag (irSt.env x.idx) := by cases xType.isObj <;> simp [jsTag, henv x]
  dsimp only [lowerBody, evalJsStmts, evalJsStmtsStep, evalJsStmtStep]; rw [hscr]; dsimp only; rw [htag, match_next_idem]; rfl

theorem fdecl_fns_none {prog c0 jsProg revName} (hprog : ProgLowered prog c0 jsProg revName) {f : Name} {d : Decl} {jsSt : JsState} (hpf : prog f = some d) (hfns : ∀ s, jsSt.fns s ≠ none → ∃ j : JoinPointId, s = jp j) : jsSt.fns (c0.js f) = none := by
  cases hfn : jsSt.fns (c0.js f) with | none => rfl | some _ => obtain ⟨j, hj⟩ := hfns _ (by rw [hfn]; simp); exact absurd hj ((hprog.fn_disjoint _ f (hprog.rev_ok f _ hpf)).1 j)

theorem fdecl_selfTail_setup {prog c0 jsProg revName} (hprog : ProgLowered prog c0 jsProg revName) {f : Name} {xs : Array Param} {ty : IRType} {b : FnBody} {info : DeclInfo} (hpf : prog f = some (.fdecl f xs ty b info)) (hemp : xs.isEmpty = false) (hst : hasSelfTail f b = true) :
    let dl := !hasJpSelfTail f b; let cL := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b, selfFn := some f, selfParams := xs, directLoop := dl }
    xs.size > 0 ∧ (xs.toList.map (·.x.idx)).Nodup ∧ BodyWf cL prog [] [] true b ∧
      jsProg (c0.js f) = some (if dl then .fnDirectLoop (c0.js f) f (xs.toList.map (v ·.x)) (lowerBody cL b) else .fnTrampoline (c0.js f) f (xs.toList.map (v ·.x)) (lowerBody cL b)) := by
  have hjsD := hprog.js_at_fdecl f xs ty b info hpf; have hdwf := hprog.decl_wf f xs ty b info hpf; have hcdl0 := hprog.c0_clean.2.2.1
  simp only [hemp, Bool.false_eq_true, ↓reduceIte, hst] at hdwf; rcases hdwf with ⟨hnd, hwfBody⟩
  exact ⟨Nat.pos_of_ne_zero fun h0 => by simp [Array.isEmpty, h0] at hemp, hnd,
    by cases hjp : !hasJpSelfTail f b <;> simp only [hjp, ↓reduceIte, Bool.false_eq_true] at hwfBody ⊢ <;> cases c0 <;> simp_all,
    by rw [hjsD]; cases hjp : !hasJpSelfTail f b <;> simp_all [lowerDecl, Ctx.js]⟩

theorem fdecl_initCall {prog c0 jsProg revName} (hprog : ProgLowered prog c0 jsProg revName)
    (c : Ctx) (allowTailCont : Bool) (jsSt : JsState) (h : CowHeap JsVal) (mIr : Name → MemoCell JsVal) (xs : Array Param) (args : List JsVal)
    (hhp : h = jsSt.heap) (hmEq : ∀ g, prog g ≠ none → mIr g = jsSt.memos (c0.js g)) (hmNo : ∀ g, (mIr g).val.elim True JsVal.noTc)
    (hnd : (xs.toList.map (·.x.idx)).Nodup) (hargs : ∀ a ∈ args, a.noTc) :
    StatesMatch prog c c0 [] [] allowTailCont { env := bindIrParams xs args (fun _ => .num 0), heap := h, memos := mIr } { env := bindMany ((xs.toList.map (v ·.x)).zip args) (fun _ => .num 0), heap := jsSt.heap, memos := jsSt.memos } :=
  StatesMatch.initCall prog c c0 allowTailCont jsSt h mIr xs args hhp hmEq hmNo hnd hargs fun k hk => hprog.nonArr_param _ xs args _ k hk fun _ _ => rfl

/-! ### Shared Lowered-JS Step Equations & Simulation Helpers -/

section SharedSteps
variable {prog : IrProg} {jsProg : JsProg} {c c0 : Ctx} {revName : String → Option Name} {irSt : IrState} {jsSt : JsState}
theorem evalIrArgs_noTc {ρ : Nat → JsVal} (hρ : ∀ k, (ρ k).noTc) (ys : Array Arg) : ∀ a ∈ ys.toList.map (evalIrArg ρ), a.noTc := fun _ ha => by rcases List.mem_map.1 ha with ⟨a', _, rfl⟩; exact evalIrArg_noTc hρ a'
theorem memoVal_noTc {α : Type} {m : α → MemoCell JsVal} (hm : ∀ g, (m g).val.elim True JsVal.noTc) (f : α) : ((m f).val.getD (.num 0)).noTc := by have hmv := hm f; cases hv : (m f).val with | none => exact noTc_num 0 | some _ => rw [hv] at hmv; exact hmv
theorem memoUpdate_noTc {m : Name → MemoCell JsVal} (hm : ∀ g, (m g).val.elim True JsVal.noTc) (f : Name) {v : JsVal} (hv : v.noTc) : ∀ g, ((if g == f then { ok := true, val := some v } else m g) : MemoCell JsVal).val.elim True JsVal.noTc := fun g => by split; exact hv; exact hm g
theorem StatesMatch.recJp_not_inline {inlineJps recJps allowTailCont} (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) {j : JoinPointId} {ys : Array Arg} (hrec : (j.idx, ys.size) ∈ recJps) : c.inlineJps.get? j.idx = none ∧ j.idx ∉ inlineJps.map Prod.fst :=
  have hnone := hsm.rec_disj (j.idx, ys.size) hrec
  ⟨hnone, fun hm => by rcases List.mem_map.1 hm with ⟨p, hp, hpe⟩; obtain ⟨_, hxs, _⟩ := hsm.inline_sub p.1 p.2 hp; rw [hpe, hnone] at hxs; cases hxs⟩
theorem inlineJp_hit {j j' : JoinPointId} {xs : Array Param} {args : List JsVal} {inlineJps : List (Nat × Nat)} (hidx : j'.idx = j.idx) (hin' : (j'.idx, args.length) ∈ (j.idx, xs.size) :: inlineJps) (hnotIn : ∀ a, (j.idx, a) ∉ inlineJps) :
    j' = j ∧ (j' == j) = true ∧ (jp j' == jp j) = true ∧ xs.size = args.length :=
  have heq : j' = j := by cases j'; cases j; cases hidx; rfl
  ⟨heq, heq ▸ jp_beq_self j, by rw [heq]; simp, (List.mem_cons.1 hin').elim (fun h => (Prod.mk.inj h).2.symm) fun h => absurd (hidx ▸ h) (hnotIn _)⟩
theorem inlineJp_miss {j j' : JoinPointId} {n : Nat} {args : List JsVal} {inlineJps : List (Nat × Nat)} (hidx : j'.idx ≠ j.idx) (hin' : (j'.idx, args.length) ∈ (j.idx, n) :: inlineJps) :
    (j' == j) = false ∧ (jp j' == jp j) = false ∧ (j'.idx, args.length) ∈ inlineJps :=
  ⟨by change (j'.idx == j.idx) = false; exact beq_false_of_ne hidx, beq_false_of_ne fun h => hidx (jp_inj h), (List.mem_cons.1 hin').elim (fun h => absurd (Prod.mk.inj h).1 hidx) id⟩

theorem evalJsStmts_lower_ret (fJs : Nat) (henv : ∀ w : VarId, irSt.env w.idx = jsSt.env (v w)) (a : Arg) :
    evalJsStmts jsProg fJs jsSt (lowerBody c (.ret a)) = some (.returned (evalIrArg irSt.env a), jsSt) := by
  dsimp only [lowerBody, evalJsStmts, evalJsStmtsStep, evalJsStmtStep]; rw [evalJsExprStep_lowerArg henv a]
theorem evalJsStmts_lower_recJmp (fJs : Nat) (henv : ∀ w : VarId, irSt.env w.idx = jsSt.env (v w)) {j : JoinPointId} (ys : Array Arg) (hnone : c.inlineJps.get? j.idx = none) :
    evalJsStmts jsProg fJs jsSt (lowerBody c (.jmp j ys)) = match evalJsCall jsProg fJs jsSt (jp j) (ys.toList.map (evalIrArg irSt.env)) with | some (v, st1) => some (.returned v, st1) | none => none := by
  dsimp only [lowerBody]; rw [hnone]; dsimp only [evalJsStmts, evalJsStmtsStep, evalJsStmtStep]; rw [evalJsExprStep_call_jp, evalJsExprListStep_lowerArgs henv ys.toList, match_next_idem]
theorem evalJsStmts_lower_recJmp_call (f' : Nat) (henv : ∀ w : VarId, irSt.env w.idx = jsSt.env (v w)) {j : JoinPointId} (ys : Array Arg) (hnone : c.inlineJps.get? j.idx = none) {ps body capJs} (hjjs : jsSt.fns (jp j) = some (ps, body, capJs)) :
    evalJsStmts jsProg (f' + 1) jsSt (lowerBody c (.jmp j ys)) = match evalJsStmts jsProg f' { env := bindMany (ps.zip (ys.toList.map (evalIrArg irSt.env))) capJs, heap := jsSt.heap, fns := jsSt.fns, memos := jsSt.memos } body with | some (.returned v, st1) => some (.returned v, { jsSt with heap := st1.heap, memos := st1.memos }) | _ => none := by
  rw [evalJsStmts_lower_recJmp (f' + 1) henv ys hnone, evalJsCall_succ]; dsimp only [evalJsCallStep]; rw [hjjs]; dsimp only
  cases evalJsStmts jsProg f' _ body with | none => rfl | some p => rcases p with ⟨ex, _⟩; cases ex <;> rfl
theorem evalJsStmts_lower_inlineJdecl (fJs : Nat) (j : JoinPointId) (xs : Array Param) (val cont : FnBody) (hjmp : (!hasJmpTo j val) = true) :
    evalJsStmts jsProg fJs jsSt (lowerBody c (.jdecl j xs val cont)) = match evalJsStmts jsProg fJs jsSt (lowerBody { c with inlineJps := c.inlineJps.insert j.idx xs } cont) with
      | some (.jumped l, st1) => if l == jp j then evalJsStmts jsProg fJs st1 ((if xs.isEmpty then [] else [JsStmt.letBinds (xs.toList.zipIdx.map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}"))]) ++ lowerBody c val) else some (.jumped l, st1)
      | some (.next, st1) => evalJsStmts jsProg fJs st1 ((if xs.isEmpty then [] else [JsStmt.letBinds (xs.toList.zipIdx.map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}"))]) ++ lowerBody c val) | res => res := by
  dsimp only [lowerBody]; rw [if_pos hjmp, List.append_assoc, List.append_assoc, evalJsStmts_letDecls_skip]; dsimp only [List.cons_append, List.nil_append, evalJsStmts, evalJsStmtsStep, evalJsStmtStep]
  cases evalJsStmtsStep (evalJsCall jsProg fJs) (evalJsApp jsProg fJs) jsSt (lowerBody { c with inlineJps := c.inlineJps.insert j.idx xs } cont) with
  | none => rfl | some r => rcases r with ⟨ex, _⟩; cases ex with | jumped l => dsimp only; by_cases hlj : (l == jp j) = true; (rw [if_pos hlj, if_pos hlj]); (rw [if_neg hlj, if_neg hlj]) | _ => rfl
theorem evalJsStmts_lower_fap_selfTail (fJs : Nat) (henv : ∀ w : VarId, irSt.env w.idx = jsSt.env (v w)) (x : VarId) (ty : IRType) (f : Name) (ys : Array Arg) (cont : FnBody) (htc : (c.selfFn == some f && retsVar x cont) = true) :
    evalJsStmts jsProg fJs jsSt (lowerBody c (.vdecl x ty (.fap f ys) cont)) = some (if c.directLoop then .tailCont (ys.toList.map (evalIrArg irSt.env)) else .returned (.tc (ys.toList.map (evalIrArg irSt.env))), if c.directLoop then { jsSt with env := bindMany ((c.selfParams.toList.map (v ·.x)).zip (ys.toList.map (evalIrArg irSt.env))) jsSt.env } else jsSt) := by
  dsimp only [lowerBody]; rw [if_pos htc]; cases c.directLoop <;> (simp only [Bool.false_eq_true, ↓reduceIte]; dsimp only [evalJsStmts, evalJsStmtsStep, evalJsStmtStep, evalJsExprStep]; rw [evalJsExprListStep_lowerArgs henv ys.toList])
theorem evalJsStmts_lower_fap_call (fJs : Nat) (henv : ∀ w : VarId, irSt.env w.idx = jsSt.env (v w)) (x : VarId) (ty : IRType) (f : Name) (ys : Array Arg) (cont : FnBody) (htc : (c.selfFn == some f && retsVar x cont) = false) (hlow : lowerApp c f ys = .call (c0.js f) (ys.toList.map lowerArg)) (hne : c0.js f ≠ "$.tag" ∧ c0.js f ≠ "$.isShared" ∧ c0.js f ≠ "$.refMark") :
    evalJsStmts jsProg fJs jsSt (lowerBody c (.vdecl x ty (.fap f ys) cont)) = match evalJsCall jsProg fJs jsSt (c0.js f) (ys.toList.map (evalIrArg irSt.env)) with | some (vjs, st1) => evalJsStmts jsProg fJs { st1 with env := bindEnv st1.env (v x) vjs } (lowerBody c cont) | none => none := by
  dsimp only [lowerBody]; rw [if_neg (by rw [htc]; decide)]; dsimp only [lowerExpr]; rw [hlow]; dsimp only [evalJsStmts, evalJsStmtsStep, evalJsStmtStep, evalJsExprStep]
  rw [evalJsExprListStep_lowerArgs henv ys.toList]; dsimp only; rw [beq_false_of_ne hne.1, beq_false_of_ne hne.2.1, beq_false_of_ne hne.2.2]; simp only [Bool.false_eq_true, ↓reduceIte]; cases evalJsCall jsProg fJs jsSt (c0.js f) (ys.toList.map (evalIrArg irSt.env)) <;> rfl
theorem evalJsStmts_lower_ap (fJs : Nat) (henv : ∀ w : VarId, irSt.env w.idx = jsSt.env (v w)) (x : VarId) (ty : IRType) (y : VarId) (ys : Array Arg) (cont : FnBody) :
    evalJsStmts jsProg fJs jsSt (lowerBody c (.vdecl x ty (.ap y ys) cont)) = match evalJsApp jsProg fJs jsSt (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) with | some (vjs, st1) => evalJsStmts jsProg fJs { st1 with env := bindEnv st1.env (v x) vjs } (lowerBody c cont) | none => none := by
  dsimp only [lowerBody, lowerExpr, evalJsStmts, evalJsStmtsStep, evalJsStmtStep, evalJsExprStep]; rw [← henv y, evalJsExprListStep_lowerArgs henv ys.toList]; dsimp only; cases evalJsApp jsProg fJs jsSt (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) <;> rfl
theorem evalJsCall_lower_memo (f : Name) (xs : Array Param) (ty : IRType) (b : FnBody) (info : DeclInfo) (args : List JsVal) (f' : Nat) (hfns : jsSt.fns (c0.js f) = none) (hjsD : jsProg (c0.js f) = lowerDecl c0 (.fdecl f xs ty b info)) (hemp : xs.isEmpty = true) :
    evalJsCall jsProg (f' + 1) jsSt (c0.js f) args = if (jsSt.memos (c0.js f)).ok then some ((jsSt.memos (c0.js f)).val.getD (.num 0), jsSt)
      else match getInitFnNameFor? c0.env f with
        | some initFn => match evalJsCall jsProg f' jsSt (c0.js initFn) [] with | some (v, st1) => some (v, { jsSt with heap := st1.heap, memos := fun k => if k == c0.js f then { ok := true, val := some v } else st1.memos k }) | none => none
        | none => match evalJsStmts jsProg f' { env := fun _ => .num 0, heap := jsSt.heap, memos := jsSt.memos } (lowerBody { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b } b) with | some (.returned v, st1) => some (v, { jsSt with heap := st1.heap, memos := fun k => if k == c0.js f then { ok := true, val := some v } else st1.memos k }) | _ => none := by
  rw [evalJsCall_succ]; dsimp only [evalJsCallStep]; rw [hfns, hjsD]; dsimp only [lowerDecl]; rw [if_pos hemp]
  have hjsCtx : ∀ na ps g, ({ c0 with nonArr := na, projSrc := ps } : Ctx).js g = c0.js g := fun _ _ _ => rfl
  cases getInitFnNameFor? c0.env f <;> (dsimp only; rw [evalJsDecl_succ]; dsimp only [evalJsDeclStep]; simp only [hjsCtx])
theorem evalJsCall_lower_plain (f : Name) (xs : Array Param) (ty : IRType) (b : FnBody) (info : DeclInfo) (args : List JsVal) (f' : Nat) (hfns : jsSt.fns (c0.js f) = none) (hjsD : jsProg (c0.js f) = lowerDecl c0 (.fdecl f xs ty b info)) (hemp : xs.isEmpty = false) (hst : hasSelfTail f b = false) :
    evalJsCall jsProg (f' + 1) jsSt (c0.js f) args = match evalJsStmts jsProg f' { env := bindMany ((xs.toList.map (v ·.x)).zip args) (fun _ => .num 0), heap := jsSt.heap, memos := jsSt.memos } (lowerBody { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b } b) with | some (.returned v, st1) => some (v, { jsSt with heap := st1.heap, memos := st1.memos }) | _ => none := by
  rw [evalJsCall_succ]; dsimp only [evalJsCallStep]; rw [hfns, hjsD]; dsimp only [lowerDecl]; rw [if_neg (by rw [hemp]; decide), if_neg (by rw [hst]; decide)]; rfl
theorem evalIrBody_inlineJdecl (ij : List Nat) (fuel : Nat) (j : JoinPointId) (xs : Array Param) (val cont : FnBody) (hjmp : (!hasJmpTo j val) = true) :
    evalIrBody prog c0 revName ij fuel irSt (.jdecl j xs val cont) = match evalIrBody prog c0 revName (j.idx :: ij) fuel irSt cont with | some (.jumped j' args, st1) => if j' == j then evalIrBody prog c0 revName ij fuel { st1 with env := bindIrParams xs args st1.env } val else some (.jumped j' args, st1) | res => res := by
  dsimp only [evalIrBody, evalIrBodyStep]; rw [if_pos hjmp]
theorem evalIrBody_fap_tailRc (ij : List Nat) (fuel : Nat) (x : VarId) (ty : IRType) (f : Name) (ys : Array Arg) (cont : FnBody) {val h' m'} (href : (f == `Qed.refMark) = false) (htrc : TailRcVarsOk c.nonArr cont) (hretV : retsVar x cont = true) (hna : ∀ m, c.nonArr.contains m = true → (irSt.env m).isNonArr = true) (hvna : c.nonArr.contains x.idx = true → val.isNonArr = true) (hirc : evalIrCall prog c0 revName fuel irSt.heap irSt.memos f (ys.toList.map (evalIrArg irSt.env)) = some (val, h', m')) :
    evalIrBody prog c0 revName ij fuel irSt (.vdecl x ty (.fap f ys) cont) = some (.returned val, { env := fun k => if k == x.idx then val else irSt.env k, heap := h', jps := irSt.jps, memos := m' }) := by
  dsimp only [evalIrBody, evalIrBodyStep]; rw [if_neg (by rw [href]; decide), hirc]; simpa only [beq_self_eq_true, ↓reduceIte] using evalIrBody_tailRcVarsOk prog c0 c.nonArr revName ij fuel x cont { env := fun k => if k == x.idx then val else irSt.env k, heap := h', jps := irSt.jps, memos := m' } htrc hretV (bindEnv_nonArr_of_expr c irSt.env x.idx val hna hvna)
theorem ExitMatchIJ.of_false_ret {fuel inlineJps recJps b val irSt1} (h : ExitMatchIJ prog c c0 jsProg revName fuel inlineJps recJps false jsSt b (.returned val) irSt1) :
    ∃ fJs jsSt1, evalJsStmts jsProg fJs jsSt (lowerBody c b) = some (.returned val, jsSt1) ∧ ExitRetOk prog c0 val irSt1 jsSt1 := h.elim id fun ⟨hf, _⟩ => absurd hf Bool.false_ne_true
theorem evalIrCall_fdecl_memo (f' : Nat) {h mIr f xs ty b info args} (hpf : prog f = some (.fdecl f xs ty b info)) (hemp : xs.isEmpty = true) :
    evalIrCall prog c0 revName (f' + 1) h mIr f args = if (mIr f).ok then some ((mIr f).val.getD (.num 0), h, mIr)
      else match getInitFnNameFor? c0.env f with
        | some ini => match evalIrCall prog c0 revName f' h mIr ini [] with | some (v, h', m') => some (v, h', fun k => if k == f then { ok := true, val := some v } else m' k) | none => none
        | none => match evalIrBody prog c0 revName [] f' { env := fun _ => .num 0, heap := h, memos := mIr } b with | some (.returned v, st1) => some (v, st1.heap, fun k => if k == f then { ok := true, val := some v } else st1.memos k) | _ => none := by
  rw [evalIrCall_succ]; dsimp only [evalIrCallStep]; rw [hpf]; dsimp only; rw [if_pos hemp]
theorem evalIrCall_fdecl_nonempty (f' : Nat) {h mIr f xs ty b info args} (hpf : prog f = some (.fdecl f xs ty b info)) (hemp : xs.isEmpty = false) :
    evalIrCall prog c0 revName (f' + 1) h mIr f args = match evalIrBody prog c0 revName [] f' { env := bindIrParams xs args (fun _ => .num 0), heap := h, memos := mIr } b with | some (.returned v, st1) => some (v, st1.heap, st1.memos) | _ => none := by
  rw [evalIrCall_succ]; dsimp only [evalIrCallStep]; rw [hpf]; dsimp only; rw [if_neg (by rw [hemp]; decide)]
theorem evalJsCall_none_of_not_mem (f' : Nat) {fn args} (hfns : jsSt.fns fn = none) (hp : jsProg fn = none) : evalJsCall jsProg (f' + 1) jsSt fn args = none := by
  rw [evalJsCall_succ]; dsimp only [evalJsCallStep]; rw [hfns, hp]
end SharedSteps

end Js.Proofs
