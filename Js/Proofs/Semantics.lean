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
      (if xs.isEmpty then [] else [JsStmt.letBinds (xs.toList.zipIdx.map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}"))]) ++ lowerBody c val := by simp [lowerBody, hnonrec]
theorem lowerBody_selfTail_shape (c : Ctx) (x : VarId) (ty : IRType) (f : Name) (args : Array Arg) (b : FnBody)
    (hself : c.selfFn = some f) (hret : retsVar x b = true) (hloop : c.directLoop = true) :
    lowerBody c (.vdecl x ty (.fap f args) b) = [.tailContinue (c.selfParams.toList.map (v ·.x)) (args.toList.map lowerArg)] := by simp [lowerBody, hself, hret, hloop]

/-! ### Unified Fuel-Indexed JS & IR Calculi -/
abbrev JsFnMap := String → Option (List String × List JsStmt × (String → JsVal))
abbrev JsProg  := String → Option JsDecl
def JsVal.setField : JsVal → Nat → JsVal → JsVal | .ctorObj t fs hs hu u s, i, v => .ctorObj t (fs.set i v) hs hu u s | o, _, _ => o
def JsVal.setTag : JsVal → Nat → JsVal | .ctorObj _ fs hs hu u s, c => .ctorObj c fs hs hu u s | _, c => .num c
def JsVal.setU : JsVal → Nat → JsVal → JsVal | .ctorObj t fs hs hu u s, i, v => .ctorObj t fs hs hu (assocSet i v u) s | o, _, _ => o
def JsVal.setS : JsVal → Nat → Nat → JsVal → JsVal | .ctorObj t fs hs hu u s, n, off, v => .ctorObj t fs hs hu u (assocSet (n, off) v s) | o, _, _, _ => o
def JsVal.isNonArr : JsVal → Bool | .arr _ => false | _ => true
mutual
def JsVal.noTc : JsVal → Prop | .tc _ => False | .ctorObj _ fs _ _ u s => noTcList fs ∧ noTcU u ∧ noTcS s | .pap fn _ acc => (∀ j : JoinPointId, fn ≠ jp j) ∧ noTcList acc | _ => True
def JsVal.noTcList : List JsVal → Prop | [] => True | v :: vs => v.noTc ∧ noTcList vs
def JsVal.noTcU : List (Nat × JsVal) → Prop | [] => True | p :: ps => p.2.noTc ∧ noTcU ps
def JsVal.noTcS : List ((Nat × Nat) × JsVal) → Prop | [] => True | p :: ps => p.2.noTc ∧ noTcS ps
end
def isSharedVal (h : CowHeap JsVal) : JsVal → Bool | .arr id => decide (1 < (h.get id).refcount) | _ => false
structure JsState where
  env : String → JsVal
  heap : CowHeap JsVal := {}
  fns : JsFnMap := fun _ => none
  memos : String → MemoCell JsVal := fun _ => {}
inductive BlockExit where | next | returned (v : JsVal) | jumped (label : String) | tailCont (args : List JsVal)

mutual
def evalJsExprM (prog : JsProg) (fuel : Nat) (st : JsState) : JsExpr → Option (JsVal × JsState)
  | .var name => some (st.env name, st) | .numLit n => some (.num n, st) | .bigIntLit n => some (.bigInt n, st) | .strLit s => some (.str s, st) | .arrLit _ => some (.arr 0, st)
  | .ctorObj t fs hs hu => match evalJsExprListM prog fuel st fs with | some (vs, st') => some (.ctorObj t vs hs hu [] [], st') | none => none
  | .fieldProj o i => match evalJsExprM prog fuel st o with | some (.ctorObj _ fs _ _ _ _, st') => some (fs.getD i (.num 0), st') | some (_, st') => some (.num 0, st') | none => none
  | .uProj o i => match evalJsExprM prog fuel st o with | some (.ctorObj _ _ _ _ u _, st') => some (assocGet i u, st') | some (_, st') => some (.num 0, st') | none => none
  | .sProj o n off => match evalJsExprM prog fuel st o with | some (.ctorObj _ _ _ _ _ s, st') => some (assocGet (n, off) s, st') | some (_, st') => some (.num 0, st') | none => none
  | .pap fn ar args => match evalJsExprListM prog fuel st args with | some (vs, st') => some (.pap fn ar vs, st') | none => none
  | .tc args => match evalJsExprListM prog fuel st args with | some (vs, st') => some (.tc vs, st') | none => none
  | .call fn args => match evalJsExprListM prog fuel st args with
      | none => none
      | some (vs, st1) => match fn, vs with
          | "$.tag", [v] => some (.num (jsTag v), st1) | "$.isShared", [v] => some (.num (if isSharedVal st1.heap v then 1 else 0), st1)
          | "$.refMark", [.arr id] => let (stamp, h') := st1.heap.refMark id; some (.num stamp, { st1 with heap := h' })
          | "$.refMark", _ => some (.num 0, st1) | _, _ => evalJsCall prog fuel st1 fn vs
  | .app fnExpr args => match evalJsExprM prog fuel st fnExpr with | none => none | some (fnVal, st1) => match evalJsExprListM prog fuel st1 args with | none => none | some (vs, st2) => evalJsApp prog fuel st2 fnVal vs
termination_by e => (fuel, 4, sizeOf e)
def evalJsExprListM (prog : JsProg) (fuel : Nat) (st : JsState) : List JsExpr → Option (List JsVal × JsState)
  | [] => some ([], st) | e :: es => match evalJsExprM prog fuel st e with | none => none | some (v, st1) => match evalJsExprListM prog fuel st1 es with | none => none | some (vs, st2) => some (v :: vs, st2)
termination_by es => (fuel, 4, sizeOf es)
def evalJsAssigns (prog : JsProg) (fuel : Nat) (st : JsState) : List (String × JsExpr) → Option (List (String × JsVal) × JsState)
  | [] => some ([], st) | (k, e) :: rest => match evalJsExprM prog fuel st e with | none => none | some (v, st1) => match evalJsAssigns prog fuel st1 rest with | none => none | some (ps, st2) => some ((k, v) :: ps, st2)
termination_by ps => (fuel, 4, sizeOf ps)
def evalJsStmt (prog : JsProg) (fuel : Nat) (st : JsState) : JsStmt → Option (BlockExit × JsState)
  | .letVar x e => match evalJsExprM prog fuel st e with | some (v, st1) => some (.next, { st1 with env := bindEnv st1.env x v }) | none => none
  | .letDecls _ => some (.next, st)
  | .letBinds binds => match evalJsAssigns prog fuel st binds with | some (ps, st1) => some (.next, { st1 with env := bindMany ps st1.env }) | none => none
  | .labeledBlock lbl body => match evalJsStmts prog fuel st body with | some (.jumped l, st1) => some (if l == lbl then .next else .jumped l, st1) | res => res
  | .constArrow name ps body => some (.next, { st with fns := bindEnv st.fns name (some (ps, body, st.env)) })
  | .setField x i e => match evalJsExprM prog fuel st e with | some (val, st1) => some (.next, { st1 with env := bindEnv st1.env x ((st1.env x).setField i val) }) | none => none
  | .setTag x cidx => some (.next, { st with env := bindEnv st.env x ((st.env x).setTag cidx) })
  | .setU x i e => match evalJsExprM prog fuel st e with | some (val, st1) => some (.next, { st1 with env := bindEnv st1.env x ((st1.env x).setU i val) }) | none => none
  | .setS x n off e => match evalJsExprM prog fuel st e with | some (val, st1) => some (.next, { st1 with env := bindEnv st1.env x ((st1.env x).setS n off val) }) | none => none
  | .incRef x n => some (.next, { st with heap := st.heap.rcInc (st.env x).toRcVal n })
  | .decRef x n => some (.next, { st with heap := st.heap.rcDec (st.env x).toRcVal n })
  | .ret e => match evalJsExprM prog fuel st e with | some (v, st1) => some (.returned v, st1) | none => none
  | .tailContinue ps args => match evalJsExprListM prog fuel st args with | some (vs, st1) => some (.tailCont vs, { st1 with env := bindMany (ps.zip vs) st1.env }) | none => none
  | .breakLabel assigns lbl => match evalJsAssigns prog fuel st assigns with | some (ps, st1) => some (.jumped lbl, { st1 with env := bindMany ps st1.env }) | none => none
  | .throwUnreachable => none
  | .switchStmt scrut arms => match evalJsExprM prog fuel st scrut with | some (sv, st1) => evalJsArms prog fuel st1 (jsTag sv) arms | none => none
termination_by s => (fuel, 4, sizeOf s)
def evalJsStmts (prog : JsProg) (fuel : Nat) (st : JsState) : List JsStmt → Option (BlockExit × JsState)
  | [] => some (.next, st) | s :: ss => match evalJsStmt prog fuel st s with | some (.next, st1) => evalJsStmts prog fuel st1 ss | res => res
termination_by ss => (fuel, 4, sizeOf ss)
def evalJsArms (prog : JsProg) (fuel : Nat) (st : JsState) (tag : Nat) : List JsSwitchArm → Option (BlockExit × JsState)
  | [] => none | .caseArm c b :: rest => if c == tag then evalJsStmts prog fuel st b else evalJsArms prog fuel st tag rest | .defaultArm b :: _ => evalJsStmts prog fuel st b
termination_by arms => (fuel, 4, sizeOf arms)
def evalJsDirectLoop (prog : JsProg) (fuel : Nat) (ps : List String) (body : List JsStmt) (st : JsState) (args : List JsVal) : Option (JsVal × JsState) :=
  match fuel with | 0 => none | f + 1 => match evalJsStmts prog f { env := bindMany (ps.zip args) (fun _ => .num 0), heap := st.heap, memos := st.memos } body with
    | some (.returned v, st1) => some (v, { st with heap := st1.heap, memos := st1.memos })
    | some (.tailCont nextArgs, st1) => evalJsDirectLoop prog f ps body { st with heap := st1.heap, memos := st1.memos } nextArgs | _ => none
termination_by (fuel, 0, 0)
def evalJsTrampoline (prog : JsProg) (fuel : Nat) (ps : List String) (body : List JsStmt) (st : JsState) (args : List JsVal) : Option (JsVal × JsState) :=
  match fuel with | 0 => none | f + 1 => match evalJsStmts prog f { env := bindMany (ps.zip args) (fun _ => .num 0), heap := st.heap, memos := st.memos } body with
    | some (.returned (.tc nextArgs), st1) => evalJsTrampoline prog f ps body { st with heap := st1.heap, memos := st1.memos } nextArgs
    | some (.returned v, st1) => some (v, { st with heap := st1.heap, memos := st1.memos }) | _ => none
termination_by (fuel, 0, 0)
def evalJsDecl (prog : JsProg) (fuel : Nat) (st : JsState) (jd : JsDecl) (args : List JsVal) : Option (JsVal × JsState) :=
  match fuel, jd with
  | 0, _ => none
  | f + 1, .fnPlain _ _ ps body => match evalJsStmts prog f { env := bindMany (ps.zip args) (fun _ => .num 0), heap := st.heap, memos := st.memos } body with
      | some (.returned v, st1) => some (v, { st with heap := st1.heap, memos := st1.memos }) | _ => none
  | f + 1, .fnDirectLoop _ _ ps body => evalJsDirectLoop prog (f + 1) ps body st args
  | f + 1, .fnTrampoline _ _ ps body => evalJsTrampoline prog (f + 1) ps body st args
  | f + 1, .memoThunk name body => let cell := st.memos name; if cell.ok then some (cell.val.getD (.num 0), st)
      else match evalJsStmts prog f { env := fun _ => .num 0, heap := st.heap, memos := st.memos } body with
        | some (.returned v, st1) => some (v, { st with heap := st1.heap, memos := fun k => if k == name then { ok := true, val := some v } else st1.memos k }) | _ => none
  | f + 1, .memoInit name initName => let cell := st.memos name; if cell.ok then some (cell.val.getD (.num 0), st)
      else match evalJsCall prog f st initName [] with | some (v, st1) => some (v, { st with heap := st1.heap, memos := fun k => if k == name then { ok := true, val := some v } else st1.memos k }) | none => none
termination_by (fuel, 1, 0)
def evalJsCall (prog : JsProg) (fuel : Nat) (st : JsState) (fn : String) (args : List JsVal) : Option (JsVal × JsState) :=
  match fuel with | 0 => none | f + 1 => match st.fns fn with
    | some (ps, body, capEnv) => match evalJsStmts prog f { env := bindMany (ps.zip args) capEnv, heap := st.heap, fns := st.fns, memos := st.memos } body with
        | some (.returned v, st1) => some (v, { st with heap := st1.heap, memos := st1.memos }) | _ => none
    | none => match prog fn with | some jd => evalJsDecl prog (f + 1) st jd args | none => none
termination_by (fuel, 2, 0)
def evalJsApp (prog : JsProg) (fuel : Nat) (st : JsState) (fnVal : JsVal) (xs : List JsVal) : Option (JsVal × JsState) :=
  match fuel, fnVal with
  | 0, _ => none
  | f + 1, .pap fn arity acc => let rem := arity - acc.length
      if xs.length < rem then some (.pap fn arity (acc ++ xs), st) else if xs.length == rem then evalJsCall prog (f + 1) st fn (acc ++ xs)
      else if rem == 0 then none else match evalJsCall prog (f + 1) st fn (acc ++ xs.take rem) with | some (res, st1) => evalJsApp prog f st1 res (xs.drop rem) | none => none
  | _ + 1, v => some (v, st)
termination_by (fuel, 3, 0)
end

theorem evalJsStmts_append (prog : JsProg) (fuel : Nat) (st : JsState) (s₁ s₂ : List JsStmt) :
    evalJsStmts prog fuel st (s₁ ++ s₂) = match evalJsStmts prog fuel st s₁ with | some (.next, st1) => evalJsStmts prog fuel st1 s₂ | res => res := by
  induction s₁ generalizing st with | nil => simp [evalJsStmts] | cons s _ ih => simp only [List.cons_append, evalJsStmts]; cases hs : evalJsStmt prog fuel st s with | none => simp | some r => rcases r with ⟨ex, st1⟩; cases ex <;> simp [ih st1]
theorem jdecl_inline_early_return_equiv (prog : JsProg) (fuel : Nat) (st st' : JsState) (j : JoinPointId) (preBody postBody : List JsStmt) (v : JsVal)
    (hret : evalJsStmts prog fuel st preBody = some (.returned v, st')) : evalJsStmts prog fuel st ([.labeledBlock (jp j) preBody] ++ postBody) = some (.returned v, st') := by simp [evalJsStmts, evalJsStmt, hret]
theorem jdecl_inline_jump_equiv (prog : JsProg) (fuel : Nat) (st st1 : JsState) (j : JoinPointId) (postBody preBody : List JsStmt)
    (hbrk : evalJsStmts prog fuel st preBody = some (.jumped (jp j), st1)) : evalJsStmts prog fuel st ([.labeledBlock (jp j) preBody] ++ postBody) = evalJsStmts prog fuel st1 postBody := by simp [evalJsStmts, evalJsStmt, hbrk]

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

mutual
def evalIrBody (prog : IrProg) (c : Ctx) (revName : String → Option Name) (inlineJps : List Nat) (fuel : Nat) (st : IrState) : FnBody → Option (IrOutcome × IrState)
  | .vdecl x ty e cont => match e with
      | .fap f ys => if f == `Qed.refMark then
            let (val, h') := match ys.toList.filterMap (refMarkArg st.env) with | [.arr id] => let (s, h') := st.heap.refMark id; (JsVal.num s, h') | _ => (JsVal.num 0, st.heap)
            evalIrBody prog c revName inlineJps fuel { st with env := fun k => if k == x.idx then val else st.env k, heap := h' } cont
          else match evalIrCall prog c revName fuel st.heap st.memos f (ys.toList.map (evalIrArg st.env)) with
            | some (val, h', m') => evalIrBody prog c revName inlineJps fuel { st with env := fun k => if k == x.idx then val else st.env k, heap := h', memos := m' } cont | none => none
      | .ap y ys => match evalIrApp prog c revName fuel st.heap st.memos (st.env y.idx) (ys.toList.map (evalIrArg st.env)) with
            | some (val, h', m') => evalIrBody prog c revName inlineJps fuel { st with env := fun k => if k == x.idx then val else st.env k, heap := h', memos := m' } cont | none => none
      | .isShared y => evalIrBody prog c revName inlineJps fuel { st with env := fun k => if k == x.idx then JsVal.num (if isSharedVal st.heap (st.env y.idx) then 1 else 0) else st.env k } cont
      | _ => evalIrBody prog c revName inlineJps fuel { st with env := fun k => if k == x.idx then evalIrPure c ty st.env e else st.env k } cont
  | .jdecl j xs val cont => if !hasJmpTo j val then match evalIrBody prog c revName (j.idx :: inlineJps) fuel st cont with
        | some (.jumped j' args, st1) => if j' == j then evalIrBody prog c revName inlineJps fuel { st1 with env := bindIrParams xs args st1.env } val else some (.jumped j' args, st1) | res => res
      else evalIrBody prog c revName inlineJps fuel { st with jps := fun k => if k == j.idx then some (xs, val, st.env) else st.jps k } cont
  | .set x i y cont => evalIrBody prog c revName inlineJps fuel { st with env := fun k => if k == x.idx then (st.env x.idx).setField i (evalIrArg st.env y) else st.env k } cont
  | .setTag x cidx cont => evalIrBody prog c revName inlineJps fuel { st with env := fun k => if k == x.idx then (st.env x.idx).setTag cidx else st.env k } cont
  | .uset x i y cont => evalIrBody prog c revName inlineJps fuel { st with env := fun k => if k == x.idx then (st.env x.idx).setU i (st.env y.idx) else st.env k } cont
  | .sset x n off y _ cont => evalIrBody prog c revName inlineJps fuel { st with env := fun k => if k == x.idx then (st.env x.idx).setS n off (st.env y.idx) else st.env k } cont
  | .inc x n _ _ cont => evalIrBody prog c revName inlineJps fuel { st with heap := st.heap.rcInc (st.env x.idx).toRcVal n } cont
  | .dec x n _ _ cont => evalIrBody prog c revName inlineJps fuel { st with heap := st.heap.rcDec (st.env x.idx).toRcVal n } cont
  | .del x cont => evalIrBody prog c revName inlineJps fuel { st with heap := st.heap.rcDec (st.env x.idx).toRcVal 1 } cont
  | .ret a => some (.returned (evalIrArg st.env a), st)
  | .jmp j ys => let args := ys.toList.map (evalIrArg st.env); if j.idx ∈ inlineJps then some (.jumped j args, st)
      else match fuel with
      | 0 => none
      | f' + 1 => match st.jps j.idx with
        | none => none
        | some (xs, val, capEnv) => match evalIrBody prog c revName [] f' { env := bindIrParams xs args capEnv, heap := st.heap, jps := st.jps, memos := st.memos } val with
            | some (.returned v, st1) => some (.returned v, { st with heap := st1.heap, memos := st1.memos })
            | _ => none
  | .unreachable => none
  | .case _ x _ alts => have : sizeOf alts.toList < sizeOf alts + 1 := by cases alts; simp; omega
      evalIrAlts prog c revName inlineJps fuel st (jsTag (st.env x.idx)) alts.toList
termination_by b => (fuel, 4, sizeOf b)
def evalIrAlts (prog : IrProg) (c : Ctx) (revName : String → Option Name) (inlineJps : List Nat) (fuel : Nat) (st : IrState) (tag : Nat) : List Alt → Option (IrOutcome × IrState)
  | [] => none | .ctor info b :: rest => if info.cidx == tag then evalIrBody prog c revName inlineJps fuel st b else evalIrAlts prog c revName inlineJps fuel st tag rest
  | .default b :: _ => evalIrBody prog c revName inlineJps fuel st b
termination_by alts => (fuel, 4, sizeOf alts)
def evalIrCall (prog : IrProg) (c : Ctx) (revName : String → Option Name) (fuel : Nat) (h : CowHeap JsVal) (memos : Name → MemoCell JsVal) (f : Name) (args : List JsVal) :
    Option (JsVal × CowHeap JsVal × (Name → MemoCell JsVal)) :=
  match fuel with | 0 => none | f' + 1 => match prog f with
    | some (.fdecl _ xs _ body _) => if xs.isEmpty then
          let cell := memos f; if cell.ok then some (cell.val.getD (.num 0), h, memos)
          else match getInitFnNameFor? c.env f with
            | some initFn => match evalIrCall prog c revName f' h memos initFn [] with | some (v, h', m') => some (v, h', fun k => if k == f then { ok := true, val := some v } else m' k) | none => none
            | none => match evalIrBody prog c revName [] f' { env := fun _ => .num 0, heap := h, memos := memos } body with
                | some (.returned v, st1) => some (v, st1.heap, fun k => if k == f then { ok := true, val := some v } else st1.memos k) | _ => none
        else match evalIrBody prog c revName [] f' { env := bindIrParams xs args (fun _ => .num 0), heap := h, memos := memos } body with
            | some (.returned v, st1) => some (v, st1.heap, st1.memos) | _ => none
    | _ => none
termination_by (fuel, 2, 0)
def evalIrApp (prog : IrProg) (c : Ctx) (revName : String → Option Name) (fuel : Nat) (h : CowHeap JsVal) (memos : Name → MemoCell JsVal) (fnVal : JsVal) (xs : List JsVal) :
    Option (JsVal × CowHeap JsVal × (Name → MemoCell JsVal)) :=
  match fuel, fnVal with
  | 0, _ => none
  | f' + 1, .pap fnStr arity acc => let rem := arity - acc.length
      if xs.length < rem then some (.pap fnStr arity (acc ++ xs), h, memos)
      else match revName fnStr with
      | none => none
      | some fn =>
          if xs.length == rem then evalIrCall prog c revName (f' + 1) h memos fn (acc ++ xs) else if rem == 0 then none
          else match evalIrCall prog c revName (f' + 1) h memos fn (acc ++ xs.take rem) with | some (res, h', m') => evalIrApp prog c revName f' h' m' res (xs.drop rem) | none => none
  | _ + 1, v => some (v, h, memos)
termination_by (fuel, 3, 0)
end

/-! ### Helper Lemmas (Frame, Pure Expression Lowering, Join-Point Binders, `noTc`) -/

theorem evalJsExprM_lowerArg (prog : JsProg) (fuel : Nat) (st : JsState) (ρ : Nat → JsVal) (hm : ∀ w : VarId, ρ w.idx = st.env (v w)) (a : Arg) :
    evalJsExprM prog fuel st (lowerArg a) = some (evalIrArg ρ a, st) := by cases a <;> simp [lowerArg, evalJsExprM, evalIrArg, hm]
theorem evalJsExprListM_lowerArgs (prog : JsProg) (fuel : Nat) (st : JsState) (ρ : Nat → JsVal) (hm : ∀ w : VarId, ρ w.idx = st.env (v w)) :
    ∀ as : List Arg, evalJsExprListM prog fuel st (as.map lowerArg) = some (as.map (evalIrArg ρ), st)
  | [] => by simp [evalJsExprListM] | a :: rest => by simp [evalJsExprListM, evalJsExprM_lowerArg prog fuel st ρ hm a, evalJsExprListM_lowerArgs prog fuel st ρ hm rest]
theorem evalJsExprListM_refMark (prog : JsProg) (fuel : Nat) (st : JsState) (ρ : Nat → JsVal) (hm : ∀ w : VarId, ρ w.idx = st.env (v w))
    (f : Arg → Option JsExpr) (hf : ∀ a, f a = match a with | .var x => some (.var (v x)) | .erased => none) :
    ∀ as : List Arg, evalJsExprListM prog fuel st (as.filterMap f) = some (as.filterMap (refMarkArg ρ), st)
  | [] => by simp [evalJsExprListM] | .erased :: rest => by simp [hf .erased, refMarkArg, evalJsExprListM_refMark prog fuel st ρ hm f hf rest]
  | .var x :: rest => by simp [hf (.var x), refMarkArg, evalJsExprListM, evalJsExprM, hm x, evalJsExprListM_refMark prog fuel st ρ hm f hf rest]
theorem evalJsExprM_lowerCtor (prog : JsProg) (fuel : Nat) (st : JsState) (ρ : Nat → JsVal) (hm : ∀ w : VarId, ρ w.idx = st.env (v w)) (i : CtorInfo) (ys : Array Arg) :
    evalJsExprM prog fuel st (lowerCtor i ys) = some (evalIrCtor ρ i ys, st) := by dsimp only [lowerCtor, evalIrCtor]; split <;> simp [evalJsExprM, evalJsExprListM_lowerArgs prog fuel st ρ hm ys.toList]
theorem evalJsExprM_lowerPure (prog : JsProg) (fuel : Nat) (c : Ctx) (ty : IRType) (st : JsState) (ρ : Nat → JsVal) (hm : ∀ w : VarId, ρ w.idx = st.env (v w))
    (e : IR.Expr) (hpure : match e with | .fap .. | .ap .. | .isShared .. => False | _ => True) : evalJsExprM prog fuel st (lowerExpr c ty e) = some (evalIrPure c ty ρ e, st) := by
  cases e with
  | ctor i ys | reuse _ i _ ys => exact evalJsExprM_lowerCtor prog fuel st ρ hm i ys | reset _ _ => simp [lowerExpr, evalJsExprM, evalIrPure]
  | proj _ x | uproj _ x | sproj _ _ x => simp [lowerExpr, evalJsExprM, evalIrPure, hm x]; cases st.env (v x) <;> rfl
  | pap _ ys => simp [lowerExpr, evalJsExprM, evalIrPure, evalJsExprListM_lowerArgs prog fuel st ρ hm ys.toList]
  | box _ x | unbox x => simp [lowerExpr, evalJsExprM, evalIrPure, hm x] | lit lv => cases lv <;> (simp [lowerExpr, evalJsExprM, evalIrPure]; try split <;> simp [evalJsExprM])
  | fap _ _ | ap _ _ | isShared _ => exact False.elim hpure
theorem evalJsExprM_call_jp (prog : JsProg) (fuel : Nat) (st : JsState) (j : JoinPointId) (es : List JsExpr) :
    evalJsExprM prog fuel st (.call (jp j) es) = match evalJsExprListM prog fuel st es with | some (vals, st1) => evalJsCall prog fuel st1 (jp j) vals | none => none := by
  simp only [evalJsExprM]; cases evalJsExprListM prog fuel st es with | none => rfl | some p =>
    have hne : ∀ s : String, s.toList.head? = some '$' → jp j ≠ s := fun s hs h => by have h0 := congrArg (fun x => x.toList.head?) h; simp [jp, hs, String.toList_append] at h0
    rcases p with ⟨vs, st1⟩; rcases vs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> simp [hne "$.tag" rfl, hne "$.isShared" rfl, hne "$.refMark" rfl]
private theorem evalJsDirectLoop_frame (prog : JsProg) (ps : List String) (body : List JsStmt) :
    ∀ k st0 as0 val st', evalJsDirectLoop prog k ps body st0 as0 = some (val, st') → st'.env = st0.env ∧ st'.fns = st0.fns
  | 0, _, _, _, _, h => by simp [evalJsDirectLoop] at h
  | k + 1, st0, as0, val, st', h => by
      simp only [evalJsDirectLoop] at h; cases h1 : evalJsStmts prog k { env := bindMany (ps.zip as0) (fun _ => .num 0), heap := st0.heap, memos := st0.memos } body with
      | none => rw [h1] at h; cases h | some r => rcases r with ⟨ex, st1⟩; rw [h1] at h; cases ex with
        | returned _ => cases h; exact ⟨rfl, rfl⟩ | tailCont nextArgs => exact evalJsDirectLoop_frame prog ps body k { st0 with heap := st1.heap, memos := st1.memos } nextArgs val st' h | next | jumped _ => cases h
private theorem evalJsTrampoline_frame (prog : JsProg) (ps : List String) (body : List JsStmt) :
    ∀ k st0 as0 val st', evalJsTrampoline prog k ps body st0 as0 = some (val, st') → st'.env = st0.env ∧ st'.fns = st0.fns
  | 0, _, _, _, _, h => by simp [evalJsTrampoline] at h
  | k + 1, st0, as0, val, st', h => by
      simp only [evalJsTrampoline] at h; cases h1 : evalJsStmts prog k { env := bindMany (ps.zip as0) (fun _ => .num 0), heap := st0.heap, memos := st0.memos } body with
      | none => rw [h1] at h; cases h | some r => rcases r with ⟨ex, st1⟩; rw [h1] at h; cases ex with
        | returned v => (cases v with | tc nextArgs => exact evalJsTrampoline_frame prog ps body k { st0 with heap := st1.heap, memos := st1.memos } nextArgs val st' h | _ => cases h; exact ⟨rfl, rfl⟩)
        | next | jumped _ | tailCont _ => cases h
private theorem evalJsCall_frame (prog : JsProg) : ∀ fuel st fn args val st', evalJsCall prog fuel st fn args = some (val, st') → st'.env = st.env ∧ st'.fns = st.fns
  | 0, _, _, _, _, _, h => by simp [evalJsCall] at h
  | f + 1, st, fn, args, val, st', h => by
      simp only [evalJsCall] at h; cases hf : st.fns fn with
      | some fdata =>
          rcases fdata with ⟨ps, body, cap⟩; simp only [hf] at h
          cases h1 : evalJsStmts prog f { env := bindMany (ps.zip args) cap, heap := st.heap, fns := st.fns, memos := st.memos } body with
          | none => simp only [h1] at h; cases h
          | some r => rcases r with ⟨ex, _⟩; simp only [h1] at h; cases ex <;> cases h; exact ⟨rfl, rfl⟩
      | none =>
          simp only [hf] at h; cases hp : prog fn with
          | none => simp only [hp] at h; cases h
          | some jd =>
              simp only [hp] at h; cases jd with
              | fnPlain _ _ ps body =>
                  simp only [evalJsDecl] at h
                  cases h1 : evalJsStmts prog f { env := bindMany (ps.zip args) (fun _ => .num 0), heap := st.heap, memos := st.memos } body with
                  | none => simp only [h1] at h; cases h
                  | some r => rcases r with ⟨ex, _⟩; simp only [h1] at h; cases ex <;> cases h; exact ⟨rfl, rfl⟩
              | fnDirectLoop _ _ ps body => simp only [evalJsDecl] at h; exact evalJsDirectLoop_frame prog ps body (f + 1) st args val st' h
              | fnTrampoline _ _ ps body => simp only [evalJsDecl] at h; exact evalJsTrampoline_frame prog ps body (f + 1) st args val st' h
              | memoThunk _ body =>
                  simp only [evalJsDecl] at h; split at h
                  · cases h; exact ⟨rfl, rfl⟩
                  · cases h1 : evalJsStmts prog f { env := fun _ => .num 0, heap := st.heap, memos := st.memos } body with
                    | none => simp only [h1] at h; cases h
                    | some r => rcases r with ⟨ex, _⟩; simp only [h1] at h; cases ex <;> cases h; exact ⟨rfl, rfl⟩
              | memoInit _ initName =>
                  simp only [evalJsDecl] at h; split at h
                  · cases h; exact ⟨rfl, rfl⟩
                  · cases h1 : evalJsCall prog f st initName [] with
                    | none => simp only [h1] at h; cases h
                    | some r => simp only [h1] at h; cases h; exact ⟨rfl, rfl⟩
private theorem evalJsApp_frame (prog : JsProg) : ∀ fuel st fnVal xs val st', evalJsApp prog fuel st fnVal xs = some (val, st') → st'.env = st.env ∧ st'.fns = st.fns
  | 0, _, _, _, _, _, h => by unfold evalJsApp at h; cases h
  | f + 1, st, fnVal, xs, val, st', happ => by
      unfold evalJsApp at happ; cases fnVal with
      | pap fn ar acc =>
          dsimp only at happ; split at happ; (cases happ; exact ⟨rfl, rfl⟩); split at happ; exact evalJsCall_frame prog (f + 1) st fn (acc ++ xs) val st' happ
          split at happ; cases happ; cases h1 : evalJsCall prog (f + 1) st fn (acc ++ xs.take (ar - acc.length)) with
          | none => rw [h1] at happ; cases happ | some r => rcases r with ⟨res, st1⟩; rw [h1] at happ; obtain ⟨h1e, h1f⟩ := evalJsCall_frame prog (f + 1) st fn _ _ _ h1; obtain ⟨f1, f2⟩ := evalJsApp_frame prog f st1 res (xs.drop _) val st' happ; exact ⟨f1.trans h1e, f2.trans h1f⟩
      | num _ | bigInt _ | str _ | arr _ | ctorObj _ _ _ _ _ _ | tc _ => dsimp only at happ; cases happ; exact ⟨rfl, rfl⟩
theorem match_next_idem (r : Option (BlockExit × JsState)) : (match r with | some (.next, st1) => some (.next, st1) | res => res) = r := by
  cases r with | none => rfl | some p => rcases p with ⟨ex, _⟩; cases ex <;> rfl

private theorem evalIr_mono_succ : ∀ fuel : Nat,
    (∀ prog c revName h memos f args r, evalIrCall prog c revName fuel h memos f args = some r → evalIrCall prog c revName (fuel + 1) h memos f args = some r) ∧
    (∀ prog c revName h memos fnVal xs r, evalIrApp prog c revName fuel h memos fnVal xs = some r → evalIrApp prog c revName (fuel + 1) h memos fnVal xs = some r) ∧
    (∀ prog c revName inlineJps st b r, evalIrBody prog c revName inlineJps fuel st b = some r → evalIrBody prog c revName inlineJps (fuel + 1) st b = some r) := by
  intro fuel; induction fuel using Nat.strongRecOn with | ind fuel ih =>
  have hCall : ∀ prog c revName h memos f args r, evalIrCall prog c revName fuel h memos f args = some r → evalIrCall prog c revName (fuel + 1) h memos f args = some r := by
    cases fuel with
    | zero => intro _ _ _ _ _ _ _ _ hr; simp [evalIrCall] at hr
    | succ f' =>
      intro prog c revName h memos f args r hr; (conv at hr => lhs; unfold evalIrCall); (conv => lhs; unfold evalIrCall); dsimp only at hr ⊢
      cases hp : prog f with | none => simp [hp] at hr | some d => cases d with | extern _ _ _ _ => simp [hp] at hr | fdecl fn xs ty b info =>
        simp only [hp] at hr ⊢; by_cases hemp : xs.isEmpty = true
        · simp only [hemp, ↓reduceIte] at hr ⊢; by_cases hmok : (memos f).ok = true; (simp only [hmok, ↓reduceIte] at hr ⊢; exact hr)
          simp only [Bool.eq_false_iff.2 hmok, Bool.false_eq_true, ↓reduceIte] at hr ⊢; cases hini : getInitFnNameFor? c.env f with
          | some ini => simp only [hini] at hr ⊢; cases h1 : evalIrCall prog c revName f' h memos ini [] with | none => rw [h1] at hr; cases hr | some _ => rw [h1] at hr; rw [(ih f' (Nat.lt_succ_self f')).1 _ _ _ _ _ _ _ _ h1]; exact hr
          | none => simp only [hini] at hr ⊢; cases h1 : evalIrBody prog c revName [] f' _ b with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [(ih f' (Nat.lt_succ_self f')).2.2 _ _ _ _ _ _ _ h1]; cases p.1 <;> exact hr
        · simp only [Bool.eq_false_iff.2 hemp, Bool.false_eq_true, ↓reduceIte] at hr ⊢; cases h1 : evalIrBody prog c revName [] f' _ b with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [(ih f' (Nat.lt_succ_self f')).2.2 _ _ _ _ _ _ _ h1]; cases p.1 <;> exact hr
  have hApp : ∀ prog c revName h memos fnVal xs r, evalIrApp prog c revName fuel h memos fnVal xs = some r → evalIrApp prog c revName (fuel + 1) h memos fnVal xs = some r := by
    cases fuel with
    | zero => intro _ _ _ _ _ _ _ _ hr; simp [evalIrApp] at hr
    | succ f' =>
      intro prog c revName h memos fnVal xs r hr; cases fnVal with
      | pap fnStr arity acc =>
        simp only [evalIrApp] at hr ⊢; by_cases hlt : xs.length < arity - acc.length; (simp only [hlt, ↓reduceIte] at hr ⊢; exact hr)
        simp only [hlt, ↓reduceIte] at hr ⊢; cases hrev : revName fnStr with | none => simp [hrev] at hr | some fn =>
          simp only [hrev] at hr ⊢; by_cases heq : (xs.length == arity - acc.length) = true; (simp only [heq, ↓reduceIte] at hr ⊢; exact hCall _ _ _ _ _ _ _ _ hr)
          simp only [heq, Bool.false_eq_true, ↓reduceIte] at hr ⊢; by_cases hz : (arity - acc.length == 0) = true; simp [hz] at hr
          simp only [hz, Bool.false_eq_true, ↓reduceIte] at hr ⊢; cases h1 : evalIrCall prog c revName (f' + 1) h memos fn (acc ++ xs.take (arity - acc.length)) with | none => simp [h1] at hr | some _ => rw [h1] at hr; rw [hCall _ _ _ _ _ _ _ _ h1]; exact (ih f' (Nat.lt_succ_self f')).2.1 _ _ _ _ _ _ _ _ hr
      | _ => simpa [evalIrApp] using hr
  refine ⟨hCall, hApp, fun prog c revName inlineJps st b r hr => ?_⟩; revert inlineJps st r hr
  refine fnBody_ind (fun b => ∀ inlineJps st r, evalIrBody prog c revName inlineJps fuel st b = some r → evalIrBody prog c revName inlineJps (fuel + 1) st b = some r) (fun b hb inlineJps st r hr => ?_) b; cases b with
  | ret _ | unreachable => simp [evalIrBody] at hr ⊢; try exact hr
  | set _ _ _ _ | setTag _ _ _ | uset _ _ _ _ | sset _ _ _ _ _ _ | inc _ _ _ _ _ | dec _ _ _ _ _ | del _ _ => simp only [evalIrBody] at hr ⊢; exact hb _ _ _ hr
  | vdecl x ty e cont => cases e with
    | fap f ys =>
        simp only [evalIrBody] at hr ⊢; by_cases href : (f == `Qed.refMark) = true; (simp only [href, ↓reduceIte] at hr ⊢; exact hb _ _ _ hr)
        simp only [href, Bool.false_eq_true, ↓reduceIte] at hr ⊢; cases h1 : evalIrCall prog c revName fuel st.heap st.memos f (ys.toList.map (evalIrArg st.env)) with | none => simp [h1] at hr | some _ => rw [h1] at hr; rw [hCall _ _ _ _ _ _ _ _ h1]; exact hb _ _ _ hr
    | ap y ys => simp only [evalIrBody] at hr ⊢; cases h1 : evalIrApp prog c revName fuel st.heap st.memos (st.env y.idx) (ys.toList.map (evalIrArg st.env)) with | none => simp [h1] at hr | some _ => rw [h1] at hr; rw [hApp _ _ _ _ _ _ _ _ h1]; exact hb _ _ _ hr
    | _ => simp only [evalIrBody] at hr ⊢; exact hb _ _ _ hr
  | jdecl j xs val cont =>
      simp only [evalIrBody] at hr ⊢; by_cases hj : (!hasJmpTo j val) = true
      · simp only [hj, ↓reduceIte] at hr ⊢; cases h1 : evalIrBody prog c revName (j.idx :: inlineJps) fuel st cont with
        | none => simp [h1] at hr | some p => rcases p with ⟨irO', _⟩; rw [h1] at hr; rw [hb.2 _ _ _ h1]; cases irO' with | returned _ => exact hr | jumped j' _ =>
          dsimp only at hr ⊢; by_cases heq : (j' == j) = true; (simp only [heq, ↓reduceIte] at hr ⊢; exact hb.1 _ _ _ hr); simp only [heq, Bool.false_eq_true, ↓reduceIte] at hr ⊢; exact hr
      · simp only [hj, Bool.false_eq_true, ↓reduceIte] at hr ⊢; exact hb.2 _ _ _ hr
  | jmp j ys =>
      by_cases hin : j.idx ∈ inlineJps; (cases fuel <;> simp only [evalIrBody, hin, ↓reduceIte] at hr ⊢ <;> exact hr)
      cases fuel with
      | zero => simp [evalIrBody, hin] at hr
      | succ f' =>
          simp only [evalIrBody, hin, ↓reduceIte] at hr ⊢; cases hj : st.jps j.idx with
          | none => rw [hj] at hr; cases hr | some jdata => simp only [hj] at hr ⊢; cases h1 : evalIrBody prog c revName [] f' _ jdata.2.1 with
            | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [(ih f' (Nat.lt_succ_self f')).2.2 _ _ _ _ _ _ _ h1]; cases p.1 <;> exact hr
  | case _ x _ alts =>
      simp only [evalIrBody] at hr ⊢; have hbList : ∀ arm ∈ alts.toList, ∀ inlineJps st r, evalIrBody prog c revName inlineJps fuel st arm.body = some r → evalIrBody prog c revName inlineJps (fuel + 1) st arm.body = some r := fun arm hm => hb arm hm
      clear hb; generalize alts.toList = ls at hr hbList; induction ls with
      | nil => simp [evalIrAlts] at hr
      | cons arm _ ihA =>
          cases arm with
          | ctor info bArm => simp only [evalIrAlts] at hr ⊢; by_cases hc : (info.cidx == jsTag (st.env x.idx)) = true; (simp only [hc, ↓reduceIte] at hr ⊢; exact hbList (.ctor info bArm) (.head _) _ _ _ hr); simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr ⊢; exact ihA hr fun a hm => hbList a (.tail _ hm)
          | default bArm => simp only [evalIrAlts] at hr ⊢; exact hbList (.default bArm) (.head _) _ _ _ hr

theorem evalIrCall_mono {prog c revName f₁ f₂ h memos f args r} (hle : f₁ ≤ f₂) (hr : evalIrCall prog c revName f₁ h memos f args = some r) : evalIrCall prog c revName f₂ h memos f args = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalIr_mono_succ _).1 _ _ _ _ _ _ _ _ ih
theorem evalIrApp_mono {prog c revName f₁ f₂ h memos fnVal args r} (hle : f₁ ≤ f₂) (hr : evalIrApp prog c revName f₁ h memos fnVal args = some r) : evalIrApp prog c revName f₂ h memos fnVal args = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalIr_mono_succ _).2.1 _ _ _ _ _ _ _ _ ih
theorem evalIrBody_mono {prog c revName inlineJps f₁ f₂ st b r} (hle : f₁ ≤ f₂) (hr : evalIrBody prog c revName inlineJps f₁ st b = some r) : evalIrBody prog c revName inlineJps f₂ st b = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalIr_mono_succ _).2.2 _ _ _ _ _ _ _ ih

private theorem evalJsExprM_call_mono (prog : JsProg) (fuel : Nat) (hCall : ∀ st fn args r, evalJsCall prog fuel st fn args = some r → evalJsCall prog (fuel + 1) st fn args = some r) (fn : String) (vs : List JsVal) (st1 : JsState) (r : JsVal × JsState) :
    (match fn, vs with | "$.tag", [v] => some (.num (jsTag v), st1) | "$.isShared", [v] => some (.num (if isSharedVal st1.heap v then 1 else 0), st1) | "$.refMark", [.arr id] => let p := st1.heap.refMark id; some (.num p.1, { st1 with heap := p.2 }) | "$.refMark", _ => some (.num 0, st1) | _, _ => evalJsCall prog fuel st1 fn vs) = some r →
    (match fn, vs with | "$.tag", [v] => some (.num (jsTag v), st1) | "$.isShared", [v] => some (.num (if isSharedVal st1.heap v then 1 else 0), st1) | "$.refMark", [.arr id] => let p := st1.heap.refMark id; some (.num p.1, { st1 with heap := p.2 }) | "$.refMark", _ => some (.num 0, st1) | _, _ => evalJsCall prog (fuel + 1) st1 fn vs) = some r := fun hr => by split at hr <;> first | exact hr | exact hCall _ _ _ _ hr

mutual
private def evalJsExprM_mono_step (prog : JsProg) (fuel : Nat) (hCall : ∀ st fn args r, evalJsCall prog fuel st fn args = some r → evalJsCall prog (fuel + 1) st fn args = some r) (hApp : ∀ st fnVal args r, evalJsApp prog fuel st fnVal args = some r → evalJsApp prog (fuel + 1) st fnVal args = some r) :
    ∀ (e : JsExpr) (st : JsState) (r : JsVal × JsState), evalJsExprM prog fuel st e = some r → evalJsExprM prog (fuel + 1) st e = some r
  | .var _, _, _, hr | .numLit _, _, _, hr | .bigIntLit _, _, _, hr | .strLit _, _, _, hr | .arrLit _, _, _, hr => by simpa [evalJsExprM] using hr
  | .ctorObj _ fs _ _, st, r, hr | .pap _ _ fs, st, r, hr | .tc fs, st, r, hr => by simp only [evalJsExprM] at hr ⊢; cases h1 : evalJsExprListM prog fuel st fs with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [evalJsExprListM_mono_step prog fuel hCall hApp fs st p h1]; exact hr
  | .fieldProj o _, st, r, hr | .uProj o _, st, r, hr | .sProj o _ _, st, r, hr => by simp only [evalJsExprM] at hr ⊢; cases h1 : evalJsExprM prog fuel st o with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [evalJsExprM_mono_step prog fuel hCall hApp o st p h1]; exact hr
  | .call fn args, st, r, hr => by simp only [evalJsExprM] at hr ⊢; cases h1 : evalJsExprListM prog fuel st args with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [evalJsExprListM_mono_step prog fuel hCall hApp args st p h1]; exact evalJsExprM_call_mono prog fuel hCall fn p.1 p.2 r hr
  | .app fnExpr args, st, r, hr => by simp only [evalJsExprM] at hr ⊢; cases h1 : evalJsExprM prog fuel st fnExpr with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [evalJsExprM_mono_step prog fuel hCall hApp fnExpr st p h1]; dsimp only at hr ⊢; cases h2 : evalJsExprListM prog fuel p.2 args with | none => rw [h2] at hr; cases hr | some q => rw [h2] at hr; rw [evalJsExprListM_mono_step prog fuel hCall hApp args p.2 q h2]; exact hApp _ _ _ _ hr
private def evalJsExprListM_mono_step (prog : JsProg) (fuel : Nat) (hCall : ∀ st fn args r, evalJsCall prog fuel st fn args = some r → evalJsCall prog (fuel + 1) st fn args = some r) (hApp : ∀ st fnVal args r, evalJsApp prog fuel st fnVal args = some r → evalJsApp prog (fuel + 1) st fnVal args = some r) :
    ∀ (es : List JsExpr) (st : JsState) (r : List JsVal × JsState), evalJsExprListM prog fuel st es = some r → evalJsExprListM prog (fuel + 1) st es = some r
  | [], _, _, hr => by simpa [evalJsExprListM] using hr
  | e :: es, st, r, hr => by simp only [evalJsExprListM] at hr ⊢; cases h1 : evalJsExprM prog fuel st e with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [evalJsExprM_mono_step prog fuel hCall hApp e st p h1]; dsimp only at hr ⊢; cases h2 : evalJsExprListM prog fuel p.2 es with | none => rw [h2] at hr; cases hr | some q => rw [h2] at hr; rw [evalJsExprListM_mono_step prog fuel hCall hApp es p.2 q h2]; exact hr
private def evalJsAssigns_mono_step (prog : JsProg) (fuel : Nat) (hCall : ∀ st fn args r, evalJsCall prog fuel st fn args = some r → evalJsCall prog (fuel + 1) st fn args = some r) (hApp : ∀ st fnVal args r, evalJsApp prog fuel st fnVal args = some r → evalJsApp prog (fuel + 1) st fnVal args = some r) :
    ∀ (ps : List (String × JsExpr)) (st : JsState) (r : List (String × JsVal) × JsState), evalJsAssigns prog fuel st ps = some r → evalJsAssigns prog (fuel + 1) st ps = some r
  | [], _, _, hr => by simpa [evalJsAssigns] using hr
  | (_, e) :: rest, st, r, hr => by simp only [evalJsAssigns] at hr ⊢; cases h1 : evalJsExprM prog fuel st e with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [evalJsExprM_mono_step prog fuel hCall hApp e st p h1]; dsimp only at hr ⊢; cases h2 : evalJsAssigns prog fuel p.2 rest with | none => rw [h2] at hr; cases hr | some q => rw [h2] at hr; rw [evalJsAssigns_mono_step prog fuel hCall hApp rest p.2 q h2]; exact hr
end
mutual
private def evalJsStmt_mono_step (prog : JsProg) (fuel : Nat) (hCall : ∀ st fn args r, evalJsCall prog fuel st fn args = some r → evalJsCall prog (fuel + 1) st fn args = some r) (hApp : ∀ st fnVal args r, evalJsApp prog fuel st fnVal args = some r → evalJsApp prog (fuel + 1) st fnVal args = some r) :
    ∀ (s : JsStmt) (st : JsState) (r : BlockExit × JsState), evalJsStmt prog fuel st s = some r → evalJsStmt prog (fuel + 1) st s = some r
  | .letDecls _, _, _, hr | .constArrow _ _ _, _, _, hr | .setTag _ _, _, _, hr | .incRef _ _, _, _, hr | .decRef _ _, _, _, hr | .throwUnreachable, _, _, hr => by simp [evalJsStmt] at hr ⊢; try exact hr
  | .letVar _ e, st, r, hr | .setField _ _ e, st, r, hr | .setU _ _ e, st, r, hr | .setS _ _ _ e, st, r, hr | .ret e, st, r, hr => by simp only [evalJsStmt] at hr ⊢; cases h1 : evalJsExprM prog fuel st e with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [evalJsExprM_mono_step prog fuel hCall hApp e st p h1]; exact hr
  | .letBinds ps, st, r, hr | .breakLabel ps _, st, r, hr => by simp only [evalJsStmt] at hr ⊢; cases h1 : evalJsAssigns prog fuel st ps with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [evalJsAssigns_mono_step prog fuel hCall hApp ps st p h1]; exact hr
  | .tailContinue _ es, st, r, hr => by simp only [evalJsStmt] at hr ⊢; cases h1 : evalJsExprListM prog fuel st es with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [evalJsExprListM_mono_step prog fuel hCall hApp es st p h1]; exact hr
  | .labeledBlock _ ss, st, r, hr => by simp only [evalJsStmt] at hr ⊢; cases h1 : evalJsStmts prog fuel st ss with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [evalJsStmts_mono_step prog fuel hCall hApp ss st p h1]; exact hr
  | .switchStmt scrut arms, st, r, hr => by simp only [evalJsStmt] at hr ⊢; cases h1 : evalJsExprM prog fuel st scrut with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [evalJsExprM_mono_step prog fuel hCall hApp scrut st p h1]; exact evalJsArms_mono_step prog fuel hCall hApp arms p.2 _ r hr
private def evalJsStmts_mono_step (prog : JsProg) (fuel : Nat) (hCall : ∀ st fn args r, evalJsCall prog fuel st fn args = some r → evalJsCall prog (fuel + 1) st fn args = some r) (hApp : ∀ st fnVal args r, evalJsApp prog fuel st fnVal args = some r → evalJsApp prog (fuel + 1) st fnVal args = some r) :
    ∀ (ss : List JsStmt) (st : JsState) (r : BlockExit × JsState), evalJsStmts prog fuel st ss = some r → evalJsStmts prog (fuel + 1) st ss = some r
  | [], _, _, hr => by simpa [evalJsStmts] using hr
  | s :: ss, st, r, hr => by simp only [evalJsStmts] at hr ⊢; cases h1 : evalJsStmt prog fuel st s with | none => rw [h1] at hr; cases hr | some p =>
      rcases p with ⟨ex', st'⟩; rw [h1] at hr; rw [evalJsStmt_mono_step prog fuel hCall hApp s st (ex', st') h1]; cases ex' with | next => exact evalJsStmts_mono_step prog fuel hCall hApp ss st' r hr | returned _ | jumped _ | tailCont _ => exact hr
private def evalJsArms_mono_step (prog : JsProg) (fuel : Nat) (hCall : ∀ st fn args r, evalJsCall prog fuel st fn args = some r → evalJsCall prog (fuel + 1) st fn args = some r) (hApp : ∀ st fnVal args r, evalJsApp prog fuel st fnVal args = some r → evalJsApp prog (fuel + 1) st fnVal args = some r) :
    ∀ (arms : List JsSwitchArm) (st : JsState) (tag : Nat) (r : BlockExit × JsState), evalJsArms prog fuel st tag arms = some r → evalJsArms prog (fuel + 1) st tag arms = some r
  | [], _, _, _, hr => by simp [evalJsArms] at hr
  | .caseArm c b :: rest, st, tag, r, hr => by simp only [evalJsArms] at hr ⊢; by_cases hc : (c == tag) = true; (simp only [hc, ↓reduceIte] at hr ⊢; exact evalJsStmts_mono_step prog fuel hCall hApp b st r hr); simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr ⊢; exact evalJsArms_mono_step prog fuel hCall hApp rest st tag r hr
  | .defaultArm b :: _, st, _, r, hr => by simp only [evalJsArms] at hr ⊢; exact evalJsStmts_mono_step prog fuel hCall hApp b st r hr
end

private theorem evalJs_mono_succ (prog : JsProg) : ∀ fuel : Nat,
    (∀ st fn args r, evalJsCall prog fuel st fn args = some r → evalJsCall prog (fuel + 1) st fn args = some r) ∧
    (∀ st fnVal xs r, evalJsApp prog fuel st fnVal xs = some r → evalJsApp prog (fuel + 1) st fnVal xs = some r) ∧
    (∀ ss st r, evalJsStmts prog fuel st ss = some r → evalJsStmts prog (fuel + 1) st ss = some r) ∧
    (∀ ps body st args r, evalJsDirectLoop prog fuel ps body st args = some r → evalJsDirectLoop prog (fuel + 1) ps body st args = some r) ∧
    (∀ ps body st args r, evalJsTrampoline prog fuel ps body st args = some r → evalJsTrampoline prog (fuel + 1) ps body st args = some r) := by
  intro fuel; induction fuel using Nat.strongRecOn with | ind fuel ih =>
  have hDL : ∀ ps body st args r, evalJsDirectLoop prog fuel ps body st args = some r → evalJsDirectLoop prog (fuel + 1) ps body st args = some r := by
    cases fuel with
    | zero => intro _ _ _ _ _ hr; simp [evalJsDirectLoop] at hr
    | succ f' =>
      intro ps body st args r hr; (conv at hr => lhs; unfold evalJsDirectLoop); (conv => lhs; unfold evalJsDirectLoop)
      cases h1 : evalJsStmts prog f' _ body with | none => rw [h1] at hr; cases hr | some p =>
        rcases p with ⟨ex', _⟩; rw [h1] at hr; rw [(ih f' (Nat.lt_succ_self f')).2.2.1 _ _ _ h1]; cases ex' with | tailCont _ => exact (ih f' (Nat.lt_succ_self f')).2.2.2.1 _ _ _ _ _ hr | returned _ => exact hr | next | jumped _ => cases hr
  have hTR : ∀ ps body st args r, evalJsTrampoline prog fuel ps body st args = some r → evalJsTrampoline prog (fuel + 1) ps body st args = some r := by
    cases fuel with
    | zero => intro _ _ _ _ _ hr; simp [evalJsTrampoline] at hr
    | succ f' =>
      intro ps body st args r hr; (conv at hr => lhs; unfold evalJsTrampoline); (conv => lhs; unfold evalJsTrampoline)
      cases h1 : evalJsStmts prog f' _ body with | none => rw [h1] at hr; cases hr | some p =>
        rcases p with ⟨ex', _⟩; rw [h1] at hr; rw [(ih f' (Nat.lt_succ_self f')).2.2.1 _ _ _ h1]; cases ex' with | returned v => (cases v with | tc _ => exact (ih f' (Nat.lt_succ_self f')).2.2.2.2 _ _ _ _ _ hr | _ => exact hr) | next | jumped _ | tailCont _ => cases hr
  have hCall : ∀ st fn args r, evalJsCall prog fuel st fn args = some r → evalJsCall prog (fuel + 1) st fn args = some r := by
    cases fuel with
    | zero => intro _ _ _ _ hr; simp [evalJsCall] at hr
    | succ f' =>
      intro st fn args r hr; (conv at hr => lhs; unfold evalJsCall); (conv => lhs; unfold evalJsCall); cases hfn : st.fns fn with
      | some fnD => simp only [hfn] at hr ⊢; cases h1 : evalJsStmts prog f' _ fnD.2.1 with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [(ih f' (Nat.lt_succ_self f')).2.2.1 _ _ _ h1]; cases p.1 <;> exact hr
      | none => simp only [hfn] at hr ⊢; cases hp : prog fn with | none => rw [hp] at hr; cases hr | some jd => simp only [hp] at hr ⊢; cases jd with
        | fnPlain _ _ _ body => simp only [evalJsDecl] at hr ⊢; cases h1 : evalJsStmts prog f' _ body with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [(ih f' (Nat.lt_succ_self f')).2.2.1 _ _ _ h1]; cases p.1 <;> exact hr
        | fnDirectLoop _ _ ps body => simp only [evalJsDecl] at hr ⊢; exact hDL ps body st args r hr
        | fnTrampoline _ _ ps body => simp only [evalJsDecl] at hr ⊢; exact hTR ps body st args r hr
        | memoThunk name body =>
            simp only [evalJsDecl] at hr ⊢; by_cases hmok : (st.memos name).ok = true; (simp only [hmok, ↓reduceIte] at hr ⊢; exact hr)
            simp only [Bool.eq_false_iff.2 hmok, Bool.false_eq_true, ↓reduceIte] at hr ⊢; cases h1 : evalJsStmts prog f' _ body with | none => rw [h1] at hr; cases hr | some p => rw [h1] at hr; rw [(ih f' (Nat.lt_succ_self f')).2.2.1 _ _ _ h1]; cases p.1 <;> exact hr
        | memoInit name initName =>
            simp only [evalJsDecl] at hr ⊢; by_cases hmok : (st.memos name).ok = true; (simp only [hmok, ↓reduceIte] at hr ⊢; exact hr)
            simp only [Bool.eq_false_iff.2 hmok, Bool.false_eq_true, ↓reduceIte] at hr ⊢; cases h1 : evalJsCall prog f' st initName [] with | none => rw [h1] at hr; cases hr | some _ => rw [h1] at hr; rw [(ih f' (Nat.lt_succ_self f')).1 _ _ _ _ h1]; exact hr
  have hApp : ∀ st fnVal xs r, evalJsApp prog fuel st fnVal xs = some r → evalJsApp prog (fuel + 1) st fnVal xs = some r := by
    cases fuel with
    | zero => intro _ _ _ _ hr; simp [evalJsApp] at hr
    | succ f' =>
      intro st fnVal xs r hr; cases fnVal with
      | pap fn ar acc =>
        simp only [evalJsApp] at hr ⊢; by_cases hlt : xs.length < ar - acc.length; (simp only [hlt, ↓reduceIte] at hr ⊢; exact hr)
        simp only [hlt, ↓reduceIte] at hr ⊢; by_cases heq : (xs.length == ar - acc.length) = true; (simp only [heq, ↓reduceIte] at hr ⊢; exact hCall _ _ _ _ hr)
        simp only [heq, Bool.false_eq_true, ↓reduceIte] at hr ⊢; by_cases hz : (ar - acc.length == 0) = true; simp [hz] at hr
        simp only [hz, Bool.false_eq_true, ↓reduceIte] at hr ⊢; cases h1 : evalJsCall prog (f' + 1) st fn (acc ++ xs.take (ar - acc.length)) with | none => rw [h1] at hr; cases hr | some _ => rw [h1] at hr; rw [hCall _ _ _ _ h1]; exact (ih f' (Nat.lt_succ_self f')).2.1 _ _ _ _ hr
      | _ => simp [evalJsApp] at hr ⊢; exact hr
  exact ⟨hCall, hApp, evalJsStmts_mono_step prog fuel hCall hApp, hDL, hTR⟩

theorem evalJsCall_mono {prog f₁ f₂ st fn args r} (hle : f₁ ≤ f₂) (hr : evalJsCall prog f₁ st fn args = some r) : evalJsCall prog f₂ st fn args = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalJs_mono_succ prog _).1 _ _ _ _ ih
theorem evalJsApp_mono {prog f₁ f₂ st fnVal xs r} (hle : f₁ ≤ f₂) (hr : evalJsApp prog f₁ st fnVal xs = some r) : evalJsApp prog f₂ st fnVal xs = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalJs_mono_succ prog _).2.1 _ _ _ _ ih
theorem evalJsStmts_mono {prog f₁ f₂ st ss r} (hle : f₁ ≤ f₂) (hr : evalJsStmts prog f₁ st ss = some r) : evalJsStmts prog f₂ st ss = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalJs_mono_succ prog _).2.2.1 _ _ _ ih
theorem evalJsDirectLoop_mono {prog f₁ f₂ ps body st args r} (hle : f₁ ≤ f₂) (hr : evalJsDirectLoop prog f₁ ps body st args = some r) : evalJsDirectLoop prog f₂ ps body st args = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalJs_mono_succ prog _).2.2.2.1 _ _ _ _ _ ih
theorem evalJsTrampoline_mono {prog f₁ f₂ ps body st args r} (hle : f₁ ≤ f₂) (hr : evalJsTrampoline prog f₁ ps body st args = some r) : evalJsTrampoline prog f₂ ps body st args = some r := by induction hle with | refl => exact hr | step _ ih => exact (evalJs_mono_succ prog _).2.2.2.2 _ _ _ _ _ ih

private theorem noTc_getD {fs : List JsVal} {i : Nat} (h : JsVal.noTcList fs) : (fs.getD i (.num 0)).noTc := by induction fs generalizing i with | nil => exact trivial | cons _ _ ih => cases i with | zero => exact h.1 | succ _ => exact ih h.2
private theorem noTc_assocGet [BEq κ] : ∀ {ps : List (κ × JsVal)} {k : κ}, (∀ p ∈ ps, p.2.noTc) → (assocGet k ps).noTc
  | [], _, _ => trivial | (_, _) :: _, _, h => by dsimp only [assocGet]; split; exact h _ (.head _); exact noTc_assocGet fun p hp => h p (.tail _ hp)
private theorem noTcU_mem : ∀ {u : List (Nat × JsVal)}, JsVal.noTcU u → ∀ p ∈ u, p.2.noTc | [], _, _, h => nomatch h | _ :: _, hu, _, h => (List.mem_cons.1 h).elim (· ▸ hu.1) (noTcU_mem hu.2 _)
private theorem noTcS_mem : ∀ {s : List ((Nat × Nat) × JsVal)}, JsVal.noTcS s → ∀ p ∈ s, p.2.noTc | [], _, _, h => nomatch h | _ :: _, hs, _, h => (List.mem_cons.1 h).elim (· ▸ hs.1) (noTcS_mem hs.2 _)
private theorem noTcList_map (f : α → JsVal) : ∀ (xs : List α), (∀ a ∈ xs, (f a).noTc) → JsVal.noTcList (xs.map f)
  | [], _ => trivial | a :: rest, h => ⟨h a (.head _), noTcList_map f rest fun x hx => h x (.tail _ hx)⟩
theorem noTcList_append : ∀ {a b : List JsVal}, JsVal.noTcList a → JsVal.noTcList b → JsVal.noTcList (a ++ b) | [], _, _, hb => hb | _ :: _, _, ha, hb => ⟨ha.1, noTcList_append ha.2 hb⟩
theorem noTcList_take {a : List JsVal} (n : Nat) (ha : JsVal.noTcList a) : JsVal.noTcList (a.take n) := by induction a generalizing n with | nil => simp; exact trivial | cons _ _ ih => cases n with | zero => trivial | succ k => exact ⟨ha.1, ih k ha.2⟩
theorem noTcList_drop {a : List JsVal} (n : Nat) (ha : JsVal.noTcList a) : JsVal.noTcList (a.drop n) := by induction a generalizing n with | nil => simp; exact trivial | cons _ _ ih => cases n with | zero => exact ha | succ k => exact ih k ha.2
theorem noTcList_of_forall {xs : List JsVal} (h : ∀ a ∈ xs, a.noTc) : JsVal.noTcList xs := by simpa using noTcList_map id xs h
theorem noTcList_mem : ∀ {xs : List JsVal}, JsVal.noTcList xs → ∀ a ∈ xs, a.noTc | [], _, _, h => nomatch h | _ :: _, hx, _, h => (List.mem_cons.1 h).elim (· ▸ hx.1) (noTcList_mem hx.2 _)
private theorem noTcList_set : ∀ {fs : List JsVal} {i : Nat} {v : JsVal}, JsVal.noTcList fs → v.noTc → JsVal.noTcList (fs.set i v)
  | [], _, _, _, _ => trivial | _ :: _, 0, _, hfs, hv => ⟨hv, hfs.2⟩ | _ :: _, _ + 1, _, hfs, hv => ⟨hfs.1, noTcList_set hfs.2 hv⟩
private theorem noTcU_set : ∀ {u : List (Nat × JsVal)} {k : Nat} {v : JsVal}, JsVal.noTcU u → v.noTc → JsVal.noTcU (assocSet k v u)
  | [], _, _, _, hv => ⟨hv, trivial⟩ | _ :: _, _, _, hu, hv => by dsimp only [assocSet]; split; exact ⟨hv, hu.2⟩; exact ⟨hu.1, noTcU_set hu.2 hv⟩
private theorem noTcS_set : ∀ {s : List ((Nat × Nat) × JsVal)} {k : Nat × Nat} {v : JsVal}, JsVal.noTcS s → v.noTc → JsVal.noTcS (assocSet k v s)
  | [], _, _, _, hv => ⟨hv, trivial⟩ | _ :: _, _, _, hs, hv => by dsimp only [assocSet]; split; exact ⟨hv, hs.2⟩; exact ⟨hs.1, noTcS_set hs.2 hv⟩
theorem evalIrArg_noTc {ρ : Nat → JsVal} (hρ : ∀ k, (ρ k).noTc) : ∀ a : Arg, (evalIrArg ρ a).noTc | .var x => hρ x.idx | .erased => trivial
theorem evalIrPure_noTc (c : Ctx) (ty : IRType) {ρ : Nat → JsVal} (hρ : ∀ k, (ρ k).noTc) (e : IR.Expr) (hpap : ∀ f ys, e = .pap f ys → ∀ j : JoinPointId, c.js f ≠ jp j) : (evalIrPure c ty ρ e).noTc := by
  have hctor : ∀ info ys, (evalIrCtor ρ info ys).noTc := fun info ys => by dsimp only [evalIrCtor]; split; trivial; exact ⟨noTcList_map _ _ fun a _ => evalIrArg_noTc hρ a, trivial, trivial⟩
  cases e with
  | ctor i ys | reuse _ i _ ys => exact hctor i ys
  | proj _ x => dsimp only [evalIrPure]; have hx := hρ x.idx; cases h : ρ x.idx with | ctorObj => exact noTc_getD (h ▸ hx).1 | _ => trivial
  | uproj _ x => dsimp only [evalIrPure]; have hx := hρ x.idx; cases h : ρ x.idx with | ctorObj => exact noTc_assocGet (noTcU_mem (h ▸ hx).2.1) | _ => trivial
  | sproj _ _ x => dsimp only [evalIrPure]; have hx := hρ x.idx; cases h : ρ x.idx with | ctorObj => exact noTc_assocGet (noTcS_mem (h ▸ hx).2.2) | _ => trivial
  | pap f ys => exact ⟨hpap f ys rfl, noTcList_map _ _ fun a _ => evalIrArg_noTc hρ a⟩ | box _ x | unbox x => exact hρ x.idx
  | lit lv => cases lv <;> dsimp only [evalIrPure] <;> (try split) <;> trivial | _ => trivial
theorem noTc_setField {o v : JsVal} {i : Nat} (ho : o.noTc) (hv : v.noTc) : (o.setField i v).noTc := by cases o with | ctorObj => exact ⟨noTcList_set ho.1 hv, ho.2⟩ | _ => exact ho
theorem noTc_setTag {o : JsVal} {cidx : Nat} (ho : o.noTc) : (o.setTag cidx).noTc := by cases o with | ctorObj => exact ho | _ => trivial
theorem noTc_setU {o v : JsVal} {i : Nat} (ho : o.noTc) (hv : v.noTc) : (o.setU i v).noTc := by cases o with | ctorObj => exact ⟨ho.1, noTcU_set ho.2.1 hv, ho.2.2⟩ | _ => exact ho
theorem noTc_setS {o v : JsVal} {n off : Nat} (ho : o.noTc) (hv : v.noTc) : (o.setS n off v).noTc := by cases o with | ctorObj => exact ⟨ho.1, ho.2.1, noTcS_set ho.2.2 hv⟩ | _ => exact ho
theorem isNonArr_setField {o v : JsVal} {i : Nat} (ho : o.isNonArr = true) : (o.setField i v).isNonArr = true := by cases o <;> exact ho
theorem isNonArr_setTag {o : JsVal} {cidx : Nat} : (o.setTag cidx).isNonArr = true := by cases o <;> rfl
theorem isNonArr_setU {o v : JsVal} {i : Nat} (ho : o.isNonArr = true) : (o.setU i v).isNonArr = true := by cases o <;> exact ho
theorem isNonArr_setS {o v : JsVal} {n off : Nat} (ho : o.isNonArr = true) : (o.setS n off v).isNonArr = true := by cases o <;> exact ho
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
private theorem evalJsAssigns_zipIdx_vars (prog : JsProg) (fuel : Nat) (st : JsState) (j : JoinPointId) (args : List JsVal) :
    ∀ (ps : List Param) (off : Nat), (hlen : off + ps.length = args.length) → (∀ i (hi : i < ps.length), st.env s!"_{jp j}_{off + i}" = args[off + i]'(by omega)) →
      evalJsAssigns prog fuel st ((ps.zipIdx off).map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}")) = some (ps.zipWith (fun p val => (v p.x, val)) (args.drop off), st)
  | [], _, _, _ => by simp [List.zipIdx, evalJsAssigns]
  | _ :: rest, off, hlen, hvals => by
    have hoff : off < args.length := by simp at hlen; omega
    have h0 : st.env s!"_{jp j}_{off}" = args[off] := by simpa using hvals 0 (by simp)
    have hrest := evalJsAssigns_zipIdx_vars prog fuel st j args rest (off + 1) (by simp at hlen ⊢; omega) fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1 i] using hvals (i + 1) (by simp at hi ⊢; omega)
    rw [← List.getElem_cons_drop hoff]; simp only [List.zipIdx_cons, List.map_cons, List.zipWith_cons_cons, evalJsAssigns, evalJsExprM, h0, hrest]

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
  | .case _ _ _ alts => have : sizeOf alts.toList < sizeOf alts + 1 := by cases alts; simp; omega
      AltsWf c irProg inlineJps recJps allowTailCont alts.toList
  | .ret _ | .unreachable => True
termination_by b => sizeOf b
def AltsWf (c : Ctx) (irProg : IrProg) (inlineJps recJps : List (Nat × Nat)) (allowTailCont : Bool) : List Alt → Prop | [] => True | .ctor _ b :: rest | .default b :: rest => BodyWf c irProg inlineJps recJps allowTailCont b ∧ AltsWf c irProg inlineJps recJps allowTailCont rest
termination_by alts => sizeOf alts
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
    ∃ cVal capJs, jsSt.fns (jp j) = some (xs.toList.map (v ·.x), lowerBody cVal val, capJs) ∧ cVal.names = c0.names ∧ cVal.min = c0.min ∧ cVal.env = c0.env ∧
      cVal.nonArr = c.nonArr ∧ cVal.projSrc = c.projSrc ∧ cVal.selfFn = c.selfFn ∧ cVal.selfParams = c.selfParams ∧ cVal.directLoop = c.directLoop ∧
      (∀ p ∈ suffixFrom j.idx recJps, cVal.inlineJps.get? p.1 = none) ∧ (∀ x : VarId, capIr x.idx = capJs (v x)) ∧ (∀ k, (capIr k).noTc) ∧
      (∀ k, c.nonArr.contains k = true → (capIr k).isNonArr = true) ∧ (xs.toList.map (·.x.idx)).Nodup ∧ BodyWf cVal prog [] (suffixFrom j.idx recJps) (if cVal.directLoop then false else allowTailCont) val
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
theorem filterMap_var_ext (g₁ g₂ : Arg → Option JsVal) (h : ∀ a, g₁ a = g₂ a) (as : List Arg) : as.filterMap g₁ = as.filterMap g₂ := congrArg (fun f => as.filterMap f) (funext h)
theorem ExitMatchJI.of_false_ret {prog c c0 revName inlineJps recJps irSt b v jsSt1} (h : ExitMatchJI prog c c0 revName inlineJps recJps false irSt b (.returned v) jsSt1) :
    ∃ fIr irSt1, evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr irSt b = some (.returned v, irSt1) ∧ ExitRetOk prog c0 v irSt1 jsSt1 := by cases v <;> first | exact absurd h.1 Bool.false_ne_true | exact h
theorem ExitMatchJI.of_ret_nonTc {prog c c0 revName allowTailCont stIr0 b v2 st2}
    (hex : ExitMatchJI prog c c0 revName [] [] allowTailCont stIr0 b (.returned v2) st2)
    (hnoTc : ∀ as, v2 = .tc as → c.directLoop = false → False) :
    ∃ fIrB irSt1, evalIrBody prog c0 revName [] fIrB stIr0 b = some (.returned v2, irSt1) ∧ ExitRetOk prog c0 v2 irSt1 st2 := by
  cases v2 with
  | tc as => exact False.elim (hnoTc as rfl hex.2.1)
  | num _ | str _ | bigInt _ | ctorObj _ _ _ _ _ _ | arr _ | pap _ _ _ => exact hex

theorem rcInc_nonArr_noop_isNonArr (h : CowHeap JsVal) (val : JsVal) (n : Nat) (hna : val.isNonArr = true) : h.rcInc val.toRcVal n = h := by cases val <;> simp [JsVal.isNonArr] at hna <;> rfl
theorem rcDec_nonArr_noop_isNonArr (h : CowHeap JsVal) (val : JsVal) (n : Nat) (hna : val.isNonArr = true) : h.rcDec val.toRcVal n = h := by cases val <;> simp [JsVal.isNonArr] at hna <;> rfl
theorem evalIrBody_tailRcVarsOk (prog : IrProg) (c0 : Ctx) (nonArr : Std.HashSet Nat) (revName : String → Option Name) (inlineJps : List Nat) (fuel : Nat) (x : VarId) :
    ∀ (cont : FnBody) (st : IrState), TailRcVarsOk nonArr cont → retsVar x cont = true → (∀ k, nonArr.contains k = true → (st.env k).isNonArr = true) → evalIrBody prog c0 revName inlineJps fuel st cont = some (.returned (st.env x.idx), st)
  | .inc y n _ _ cont, st, htr, hret, hna => by simp only [evalIrBody, rcInc_nonArr_noop_isNonArr _ _ n (hna y.idx htr.1)]; exact evalIrBody_tailRcVarsOk prog c0 nonArr revName inlineJps fuel x cont st htr.2 hret hna
  | .dec y n _ _ cont, st, htr, hret, hna => by simp only [evalIrBody, rcDec_nonArr_noop_isNonArr _ _ n (hna y.idx htr.1)]; exact evalIrBody_tailRcVarsOk prog c0 nonArr revName inlineJps fuel x cont st htr.2 hret hna
  | .del y cont, st, htr, hret, hna => by simp only [evalIrBody, rcDec_nonArr_noop_isNonArr _ _ 1 (hna y.idx htr.1)]; exact evalIrBody_tailRcVarsOk prog c0 nonArr revName inlineJps fuel x cont st htr.2 hret hna
  | .ret (.var w), st, _, hret, _ => by simp only [retsVar, skipRC] at hret; have hwx : w = x := (by cases w; cases x; congr; exact eq_of_beq hret); subst hwx; simp [evalIrBody, evalIrArg]
  | .ret .erased, _, htr, _, _ | .vdecl _ _ _ _, _, htr, _, _ | .jdecl _ _ _ _, _, htr, _, _ | .case _ _ _ _, _, htr, _, _ | .set _ _ _ _, _, htr, _, _ | .setTag _ _ _, _, htr, _, _ | .uset _ _ _ _, _, htr, _, _ | .sset _ _ _ _ _ _, _, htr, _, _ | .jmp _ _, _, htr, _, _ | .unreachable, _, htr, _, _ => False.elim htr

theorem evalJsStmts_letDecls_skip (prog : JsProg) (fuel : Nat) (st : JsState) (xs : Array Param) (names : List String) (ss : List JsStmt) :
    evalJsStmts prog fuel st ((if xs.isEmpty then [] else [JsStmt.letDecls names]) ++ ss) = evalJsStmts prog fuel st ss := by by_cases hemp : xs.isEmpty = true <;> simp [hemp, evalJsStmts, evalJsStmt]
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
  ⟨hsm.env_eq, hsm.heap_eq, hsm.memos_eq, hsm.memos_noTc, hsm.env_noTc, fun k hk => hsm.nonArr_ok k (hNA ▸ hk), hsm.fns_only_jp, hsm.jps_none,
   fun j' xs' val' capIr' hj' hm' => let ⟨cv, cj, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15⟩ := hsm.jps_some j' xs' val' capIr' hj' hm'
     ⟨cv, cj, s1, s2, s3, s4, hNA ▸ s5, hPS ▸ s6, hSF ▸ s7, hSP ▸ s8, hDL ▸ s9, s10, s11, s12, fun k hk => s13 k (hNA ▸ hk), s14, s15⟩, hsm.rec_ar, hsm.rec_nodup, hDisj, hIn⟩
theorem findEnv_fap_args (c c0 : Ctx) (f : Name) (ys : Array Arg) (hnames : c.names = c0.names) (henv : c.env = c0.env) (hfe : findEnvDecl c0.env f = some (.fdecl xs₀ ps ty b info)) (hneq : f ≠ `Qed.refMark) : lowerApp c f ys = .call (c0.js f) (ys.toList.map lowerArg) := by
  have hjs : c.js f = c0.js f := by simp [Ctx.js, hnames]
  simp [lowerApp, beq_false_of_ne hneq, henv, hfe, hjs]
private theorem evalIrPure_ctx_eq (c c0 : Ctx) (hnames : c.names = c0.names) (henv : c.env = c0.env) : ∀ ty ρ e, evalIrPure c ty ρ e = evalIrPure c0 ty ρ e := fun ty ρ e => by cases e with | lit lv => cases lv <;> simp [evalIrPure] | _ => simp [evalIrPure, Ctx.js, hnames, henv]
theorem evalIrPure_ctor_isNonArr (c : Ctx) (ty : IRType) (ρ : Nat → JsVal) : ∀ e : IR.Expr, (match e with | .ctor .. | .reuse .. | .reset .. | .pap .. | .lit .. | .isShared .. => True | _ => False) → (evalIrPure c ty ρ e).isNonArr = true := fun e he => by
  cases e with | ctor _ ys | reuse _ _ _ ys => dsimp only [evalIrPure, evalIrCtor]; split <;> rfl | reset _ _ | pap _ _ | isShared _ => rfl | lit lv => exact (by cases lv <;> dsimp only [evalIrPure] <;> first | rfl | (split <;> rfl)) | proj _ _ | uproj _ _ | sproj _ _ _ | fap _ _ | ap _ _ | box _ _ | unbox _ => exact False.elim he
private theorem zipWith_param_eq_zip : ∀ (l : List Param) (as : List JsVal), l.zipWith (fun p val => (v p.x, val)) as = (l.map (v ·.x)).zip as | [], _ | _ :: _, [] => rfl | _ :: rest, _ :: vs => by simp [List.zipWith_cons_cons, zipWith_param_eq_zip rest vs]
theorem evalIrBody_jmp_inline (prog : IrProg) (c : Ctx) (revName : String → Option Name) (inlineJps : List Nat) (fuel : Nat) (st : IrState) (j : JoinPointId) (ys : Array Arg) (hin : j.idx ∈ inlineJps) :
    evalIrBody prog c revName inlineJps fuel st (.jmp j ys) = some (.jumped j (ys.toList.map (evalIrArg st.env)), st) := by cases fuel <;> simp [evalIrBody, hin]

theorem StatesMatch.initCall (prog : IrProg) (c c0 : Ctx) (allowTailCont : Bool) (jsSt : JsState) (h : CowHeap JsVal) (mIr : Name → MemoCell JsVal) (xs : Array Param) (args : List JsVal)
    (hhp : h = jsSt.heap) (hmEq : ∀ g, prog g ≠ none → mIr g = jsSt.memos (c0.js g)) (hmNo : ∀ g, (mIr g).val.elim True JsVal.noTc) (hnd : (xs.toList.map (·.x.idx)).Nodup) (hargs : ∀ a ∈ args, a.noTc) (hnp : ∀ k, c.nonArr.contains k = true → (bindIrParams xs args (fun _ => .num 0) k).isNonArr = true) :
    StatesMatch prog c c0 [] [] allowTailCont { env := bindIrParams xs args (fun _ => .num 0), heap := h, memos := mIr } { env := bindMany ((xs.toList.map (v ·.x)).zip args) (fun _ => .num 0), heap := jsSt.heap, memos := jsSt.memos } :=
  { env_eq := fun w => (by cases xs with | mk xl => dsimp only; rw [bindIrParams_nodup_eq xl args (fun _ => .num 0) (fun _ => .num 0) hnd (fun _ => rfl) w, zipWith_param_eq_zip xl args])
    heap_eq := hhp
    memos_eq := hmEq
    memos_noTc := hmNo
    env_noTc := fun k => (by cases xs with | mk xl => exact bindIrParams_noTc xl args (fun _ => .num 0) (fun _ => trivial) hargs k)
    nonArr_ok := hnp
    fns_only_jp := fun _ hs => (nomatch hs)
    jps_none := fun _ => ⟨fun _ => rfl, fun _ => rfl⟩
    jps_some := fun _ _ _ _ _ hm => (nomatch hm)
    rec_ar := fun _ _ _ _ _ hm => (nomatch hm)
    rec_nodup := List.nodup_nil
    rec_disj := fun _ hm => (nomatch hm)
    inline_sub := fun _ _ hm => (nomatch hm) }

private theorem StatesMatch.dropRecHead {prog c c0 inlineJps recJps allowTailCont irSt jsSt} {j : JoinPointId} {ar : Nat} (hnotRec : ∀ a, (j.idx, a) ∉ recJps) (hsm : StatesMatch prog c c0 inlineJps ((j.idx, ar) :: recJps) allowTailCont irSt jsSt) :
    StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt :=
  { hsm with
    jps_some := fun j' xs' val' capIr' hj' hm' => (by
      have hne : j'.idx ≠ j.idx := fun he => hnotRec xs'.size (he ▸ hm')
      simpa only [show suffixFrom j'.idx ((j.idx, ar) :: recJps) = suffixFrom j'.idx recJps by simp [suffixFrom, beq_false_of_ne hne.symm]] using hsm.jps_some j' xs' val' capIr' hj' (.tail _ hm')),
    rec_ar := fun j' a' xs' val' capIr' hm' => hsm.rec_ar j' a' xs' val' capIr' (.tail _ hm'), rec_nodup := hsm.rec_nodup.of_cons, rec_disj := fun p hp => hsm.rec_disj p (.tail _ hp) }
theorem ExitMatchIJ.dropRecHead {prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt b irO irSt1} {j : JoinPointId} {ar : Nat} (hnotRec : ∀ a, (j.idx, a) ∉ recJps) (hex : ExitMatchIJ prog c c0 jsProg revName fuel inlineJps ((j.idx, ar) :: recJps) allowTailCont jsSt b irO irSt1) :
    ExitMatchIJ prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt b irO irSt1 := by
  cases irO with | returned _ => exact hex | jumped _ _ => rcases hex with ⟨fJs, jsSt1, hev, hok⟩; exact ⟨fJs, jsSt1, hev, hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.dropRecHead hnotRec⟩
theorem ExitMatchJI.dropRecHead {prog c c0 revName inlineJps recJps allowTailCont irSt b ex jsSt1} {j : JoinPointId} {ar : Nat} (hnotRec : ∀ a, (j.idx, a) ∉ recJps) (hex : ExitMatchJI prog c c0 revName inlineJps ((j.idx, ar) :: recJps) allowTailCont irSt b ex jsSt1) :
    ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt b ex jsSt1 := by
  cases ex with | next | tailCont _ => exact hex | returned v => cases v <;> exact hex | jumped _ => rcases hex with ⟨fIr, j', args, irSt1, rfl, hev, hok⟩; exact ⟨fIr, j', args, irSt1, rfl, hev, hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.dropRecHead hnotRec⟩

private theorem evalJsCall_directLoop (jsProg : JsProg) (c : Ctx) (f : Name) (ps : List String) (body : List JsStmt) (st : JsState) (args : List JsVal) (fuel : Nat) (hfns : st.fns (c.js f) = none) (hprog : jsProg (c.js f) = some (.fnDirectLoop (c.js f) f ps body)) :
    evalJsCall jsProg fuel st (c.js f) args = evalJsDirectLoop jsProg fuel ps body st args := by cases fuel <;> simp [evalJsCall, evalJsDirectLoop, hfns, hprog, evalJsDecl]
private theorem evalJsCall_trampoline (jsProg : JsProg) (c : Ctx) (f : Name) (ps : List String) (body : List JsStmt) (st : JsState) (args : List JsVal) (fuel : Nat) (hfns : st.fns (c.js f) = none) (hprog : jsProg (c.js f) = some (.fnTrampoline (c.js f) f ps body)) :
    evalJsCall jsProg fuel st (c.js f) args = evalJsTrampoline jsProg fuel ps body st args := by cases fuel <;> simp [evalJsCall, evalJsTrampoline, hfns, hprog, evalJsDecl]
theorem evalJsCall_selfTail (dl : Bool) (jsProg : JsProg) (c0 : Ctx) (f : Name) (ps : List String) (body : List JsStmt) (st : JsState) (args : List JsVal) (k : Nat)
    (hfns : st.fns (c0.js f) = none) (hdecl : jsProg (c0.js f) = some (if dl then .fnDirectLoop (c0.js f) f ps body else .fnTrampoline (c0.js f) f ps body)) :
    ∀ (ex : BlockExit) (st1 : JsState), evalJsStmts jsProg k { env := bindMany (ps.zip args) (fun _ => .num 0), heap := st.heap, memos := st.memos } body = some (ex, st1) →
    (∀ v, v.noTc → ex = .returned v → evalJsCall jsProg (k + 1) st (c0.js f) args = some (v, { st with heap := st1.heap, memos := st1.memos })) ∧
    (∀ na, ex = (if dl then .tailCont na else .returned (.tc na)) → ∀ k', k ≤ k' → evalJsCall jsProg (k' + 1) st (c0.js f) args = evalJsCall jsProg k' { st with heap := st1.heap, memos := st1.memos } (c0.js f) na) := by
  intro ex st1 hb; cases dl
  · refine ⟨fun v hv hex => (by subst hex; cases v with | tc _ => exact False.elim hv | _ => simp [evalJsCall_trampoline jsProg c0 f ps body st args (k + 1) hfns hdecl, evalJsTrampoline.eq_2, hb]),
      fun na hex k' hle => (by subst hex; rw [evalJsCall_trampoline jsProg c0 f ps body st args (k' + 1) hfns hdecl, evalJsCall_trampoline jsProg c0 f ps body { st with heap := st1.heap, memos := st1.memos } na k' hfns hdecl, evalJsTrampoline.eq_2]; simp [evalJsStmts_mono hle hb])⟩
  · refine ⟨fun v _ hex => (by subst hex; simp [evalJsCall_directLoop jsProg c0 f ps body st args (k + 1) hfns hdecl, evalJsDirectLoop.eq_2, hb]),
      fun na hex k' hle => (by subst hex; rw [evalJsCall_directLoop jsProg c0 f ps body st args (k' + 1) hfns hdecl, evalJsCall_directLoop jsProg c0 f ps body { st with heap := st1.heap, memos := st1.memos } na k' hfns hdecl, evalJsDirectLoop.eq_2]; simp [evalJsStmts_mono hle hb])⟩
theorem evalJsCall_selfTail_inv (dl : Bool) (jsProg : JsProg) (c0 : Ctx) (f : Name) (ps : List String) (body : List JsStmt) (st : JsState) (args : List JsVal) (f' : Nat) (v2 : JsVal) (st2 : JsState)
    (hfns : st.fns (c0.js f) = none) (hdecl : jsProg (c0.js f) = some (if dl then .fnDirectLoop (c0.js f) f ps body else .fnTrampoline (c0.js f) f ps body)) (hjsc : evalJsCall jsProg (f' + 1) st (c0.js f) args = some (v2, st2)) :
    ∃ ex st1, evalJsStmts jsProg f' { env := bindMany (ps.zip args) (fun _ => .num 0), heap := st.heap, memos := st.memos } body = some (ex, st1) ∧
      ((∃ na, ex = (if dl then .tailCont na else .returned (.tc na)) ∧ evalJsCall jsProg f' { st with heap := st1.heap, memos := st1.memos } (c0.js f) na = some (v2, st2)) ∨
       (∃ v, ex = .returned v ∧ (dl = true ∨ ∀ na, v ≠ .tc na) ∧ v2 = v ∧ st2 = { st with heap := st1.heap, memos := st1.memos })) := by
  cases dl
  · rw [evalJsCall_trampoline jsProg c0 f ps body st args (f' + 1) hfns hdecl, evalJsTrampoline.eq_2] at hjsc
    cases h1 : evalJsStmts jsProg f' _ body with | none => rw [h1] at hjsc; cases hjsc | some r =>
    rcases r with ⟨ex, st1⟩; rw [h1] at hjsc; refine ⟨ex, st1, rfl, ?_⟩
    cases ex with | next | jumped _ | tailCont _ => cases hjsc | returned v => cases v with
      | tc na => left; exact ⟨na, rfl, by rw [evalJsCall_trampoline jsProg c0 f ps body { st with heap := st1.heap, memos := st1.memos } na f' hfns hdecl]; exact hjsc⟩
      | num _ | str _ | bigInt _ | ctorObj _ _ _ _ _ _ | arr _ | pap _ _ _ => cases hjsc; right; exact ⟨_, rfl, Or.inr (fun _ h => nomatch h), rfl, rfl⟩
  · rw [evalJsCall_directLoop jsProg c0 f ps body st args (f' + 1) hfns hdecl, evalJsDirectLoop.eq_2] at hjsc
    cases h1 : evalJsStmts jsProg f' _ body with | none => rw [h1] at hjsc; cases hjsc | some r =>
    rcases r with ⟨ex, st1⟩; rw [h1] at hjsc; refine ⟨ex, st1, rfl, ?_⟩
    cases ex with
    | next | jumped _ => cases hjsc
    | tailCont na => left; exact ⟨na, rfl, by rw [evalJsCall_directLoop jsProg c0 f ps body { st with heap := st1.heap, memos := st1.memos } na f' hfns hdecl]; exact hjsc⟩
    | returned v => right; exact ⟨v, rfl, Or.inl rfl, by cases v <;> (cases hjsc; exact ⟨rfl, rfl⟩)⟩

theorem memoUpdate_eq {prog : IrProg} {c0 : Ctx} {revName : String → Option Name} (hrev : ∀ f d, prog f = some d → revName (c0.js f) = some f) {mIr : Name → MemoCell JsVal} {mJs : String → MemoCell JsVal} (hmEq : ∀ g, prog g ≠ none → mIr g = mJs (c0.js g)) {f : Name} (hf : prog f ≠ none) (v : JsVal) :
    ∀ g, prog g ≠ none → (if g == f then { ok := true, val := some v } else mIr g) = (if c0.js g == c0.js f then { ok := true, val := some v } else mJs (c0.js g)) := fun g hg => by
  by_cases hgf : g = f; (subst hgf; simp)
  have hne : c0.js g ≠ c0.js f := fun heq => by cases hpg : prog g with | none => exact hg hpg | some dg => cases hpf : prog f with | none => exact hf hpf | some df => have e1 := hrev g dg hpg; have e2 := hrev f df hpf; rw [heq, e2] at e1; exact hgf (Option.some.inj e1.symm)
  simp [beq_false_of_ne hgf, beq_false_of_ne hne, hmEq g hg]

abbrev CallSimIJ (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (fuel : Nat) : Prop :=
  ∀ (h : CowHeap JsVal) (mIr : Name → MemoCell JsVal) (f : Name) (args : List JsVal) (jsSt : JsState) (v1 : JsVal) (h1 : CowHeap JsVal) (m1 : Name → MemoCell JsVal),
    prog f ≠ none → h = jsSt.heap → (∀ g, prog g ≠ none → mIr g = jsSt.memos (c0.js g)) → (∀ g, (mIr g).val.elim True JsVal.noTc) → (∀ a ∈ args, a.noTc) → (∀ s, jsSt.fns s ≠ none → ∃ j : JoinPointId, s = jp j) →
    evalIrCall prog c0 revName fuel h mIr f args = some (v1, h1, m1) → ∃ fJs st2, evalJsCall jsProg fJs jsSt (c0.js f) args = some (v1, st2) ∧ CallPost prog c0 v1 v1 h1 m1 jsSt st2
abbrev AppSimIJ (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (fuel : Nat) : Prop :=
  ∀ (h : CowHeap JsVal) (mIr : Name → MemoCell JsVal) (fnVal : JsVal) (args : List JsVal) (jsSt : JsState) (v1 : JsVal) (h1 : CowHeap JsVal) (m1 : Name → MemoCell JsVal),
    h = jsSt.heap → (∀ g, prog g ≠ none → mIr g = jsSt.memos (c0.js g)) → (∀ g, (mIr g).val.elim True JsVal.noTc) → fnVal.noTc → (∀ a ∈ args, a.noTc) → (∀ s, jsSt.fns s ≠ none → ∃ j : JoinPointId, s = jp j) →
    evalIrApp prog c0 revName fuel h mIr fnVal args = some (v1, h1, m1) → ∃ fJs st2, evalJsApp jsProg fJs jsSt fnVal args = some (v1, st2) ∧ CallPost prog c0 v1 v1 h1 m1 jsSt st2
abbrev BodySimIJ (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (fuel : Nat) : Prop :=
  ∀ (c : Ctx) (inlineJps recJps : List (Nat × Nat)) (allowTailCont : Bool) (b : FnBody) (irSt : IrState) (jsSt : JsState) (irO : IrOutcome) (irSt1 : IrState),
    c.names = c0.names → c.min = c0.min → c.env = c0.env → (∀ sf, c.selfFn = some sf → prog sf ≠ none ∧ c.selfParams.size > 0 ∧ (c.selfParams.toList.map (·.x.idx)).Nodup) → BodyWf c prog inlineJps recJps allowTailCont b → StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt →
    evalIrBody prog c0 revName (inlineJps.map Prod.fst) fuel irSt b = some (irO, irSt1) → ExitMatchIJ prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt b irO irSt1

abbrev CallSimJI (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (fuel : Nat) : Prop :=
  ∀ (h : CowHeap JsVal) (mIr : Name → MemoCell JsVal) (f : Name) (args : List JsVal) (jsSt : JsState) (v2 : JsVal) (st2 : JsState),
    prog f ≠ none → h = jsSt.heap → (∀ g, prog g ≠ none → mIr g = jsSt.memos (c0.js g)) → (∀ g, (mIr g).val.elim True JsVal.noTc) → (∀ a ∈ args, a.noTc) → (∀ s, jsSt.fns s ≠ none → ∃ j : JoinPointId, s = jp j) →
    evalJsCall jsProg fuel jsSt (c0.js f) args = some (v2, st2) → ∃ fIr h1 m1, evalIrCall prog c0 revName fIr h mIr f args = some (v2, h1, m1) ∧ CallPost prog c0 v2 v2 h1 m1 jsSt st2
abbrev AppSimJI (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (fuel : Nat) : Prop :=
  ∀ (h : CowHeap JsVal) (mIr : Name → MemoCell JsVal) (fnVal : JsVal) (args : List JsVal) (jsSt : JsState) (v2 : JsVal) (st2 : JsState),
    h = jsSt.heap → (∀ g, prog g ≠ none → mIr g = jsSt.memos (c0.js g)) → (∀ g, (mIr g).val.elim True JsVal.noTc) → fnVal.noTc → (∀ a ∈ args, a.noTc) → (∀ s, jsSt.fns s ≠ none → ∃ j : JoinPointId, s = jp j) →
    evalJsApp jsProg fuel jsSt fnVal args = some (v2, st2) → ∃ fIr h1 m1, evalIrApp prog c0 revName fIr h mIr fnVal args = some (v2, h1, m1) ∧ CallPost prog c0 v2 v2 h1 m1 jsSt st2
abbrev BodySimJI (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (fuel : Nat) : Prop :=
  ∀ (c : Ctx) (inlineJps recJps : List (Nat × Nat)) (allowTailCont : Bool) (b : FnBody) (irSt : IrState) (jsSt : JsState) (ex : BlockExit) (jsSt1 : JsState),
    c.names = c0.names → c.min = c0.min → c.env = c0.env → (∀ sf, c.selfFn = some sf → prog sf ≠ none ∧ c.selfParams.size > 0 ∧ (c.selfParams.toList.map (·.x.idx)).Nodup) →
    BodyWf c prog inlineJps recJps allowTailCont b → StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt →
    evalJsStmts jsProg fuel jsSt (lowerBody c b) = some (ex, jsSt1) → ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt b ex jsSt1

private theorem mem_jmpSlots_fst (ρ : Nat → JsVal) (j : JoinPointId) : ∀ (ls : List Arg) (off : Nat) (nm : String), nm ∈ (((ls.zipIdx off).map fun (a, i) => (s!"_{jp j}_{i}", evalIrArg ρ a)).map Prod.fst) → ∃ k < ls.length, nm = inlineJpSlot j (off + k)
  | [], _, _, h => nomatch h | _ :: rest, off, nm, h => by simp only [List.zipIdx_cons, List.map_cons, List.mem_cons] at h; rcases h with rfl | htl; exact ⟨0, Nat.zero_lt_succ _, by simp [inlineJpSlot]⟩; obtain ⟨k, hk, heq⟩ := mem_jmpSlots_fst ρ j rest (off + 1) nm htl; exact ⟨k + 1, Nat.succ_lt_succ hk, by rw [heq, Nat.add_assoc, Nat.add_comm 1 k]⟩
theorem nodup_jmpSlots (ρ : Nat → JsVal) (j : JoinPointId) : ∀ (ls : List Arg) (off : Nat), (((ls.zipIdx off).map fun (a, i) => (s!"_{jp j}_{i}", evalIrArg ρ a)).map Prod.fst).Nodup
  | [], _ => by simp [List.zipIdx] | _ :: rest, off => by simp only [List.zipIdx_cons, List.map_cons, List.nodup_cons]; refine ⟨fun hm => ?_, nodup_jmpSlots ρ j rest (off + 1)⟩; obtain ⟨k, _, heq⟩ := mem_jmpSlots_fst ρ j rest (off + 1) _ hm; have := (inlineJpSlot_inj heq).2; omega
theorem mem_jmpSlots_getElem (ρ : Nat → JsVal) (j : JoinPointId) : ∀ (ls : List Arg) (off i : Nat) (hi : i < ls.length), (s!"_{jp j}_{off + i}", (ls.map (evalIrArg ρ))[i]'(by simpa using hi)) ∈ ((ls.zipIdx off).map fun (a, k) => (s!"_{jp j}_{k}", evalIrArg ρ a))
  | [], _, i, hi => absurd hi (Nat.not_lt_zero _) | _ :: _, off, 0, _ => by simp [List.zipIdx_cons] | _ :: rest, off, i + 1, hi => by simpa [List.zipIdx_cons, Nat.add_assoc, Nat.add_comm 1 i] using mem_jmpSlots_getElem ρ j rest (off + 1) i (Nat.lt_of_succ_lt_succ hi)
theorem evalJsAssigns_jmp_inline (prog : JsProg) (fuel : Nat) (jsSt : JsState) (envIr : Nat → JsVal) (j : JoinPointId) (henv : ∀ x, envIr x.idx = jsSt.env (v x)) :
    ∀ (ls : List Arg) (off : Nat), evalJsAssigns prog fuel jsSt ((ls.zipIdx off).map fun (a, i) => ("_" ++ jp j ++ "_" ++ i.repr, lowerArg a)) = some ((ls.zipIdx off).map fun (a, i) => ("_" ++ jp j ++ "_" ++ i.repr, evalIrArg envIr a), jsSt)
  | [], _ => by simp [List.zipIdx, evalJsAssigns] | a :: rest, off => by simp only [List.zipIdx_cons, List.map_cons, evalJsAssigns, evalJsExprM_lowerArg prog fuel jsSt envIr henv a, evalJsAssigns_jmp_inline prog fuel jsSt envIr j henv rest (off + 1)]
theorem evalIrBody_jmp_not_inline (prog : IrProg) (c : Ctx) (revName : String → Option Name) (inlineJps : List Nat) (f' : Nat) (st : IrState) (j : JoinPointId) (ys : Array Arg) (hnot : j.idx ∉ inlineJps) :
    evalIrBody prog c revName inlineJps (f' + 1) st (.jmp j ys) = match st.jps j.idx with | none => none | some (xs, val, capEnv) => match evalIrBody prog c revName [] f' { env := bindIrParams xs (ys.toList.map (evalIrArg st.env)) capEnv, heap := st.heap, jps := st.jps, memos := st.memos } val with | some (.returned v, st1) => some (.returned v, { st with heap := st1.heap, memos := st1.memos }) | _ => none := by simp [evalIrBody, hnot]
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
    jps_none := fun j' => (by by_cases hjj : j'.idx = j.idx; (have hj'eq : j' = j := (by cases j'; cases j; simp_all); subst hj'eq; simp [bindEnv]); simp [beq_false_of_ne hjj, bindEnv, beq_false_of_ne (fun h => hjj (jp_inj h)), hsm.jps_none j']),
    jps_some := fun j' xs' val' capIr' hj' hmem' => (by
      by_cases hjj : j'.idx = j.idx
      · have hj'eq : j' = j := (by cases j'; cases j; simp_all); subst hj'eq; simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hj'; obtain ⟨rfl, rfl, rfl⟩ := hj'; rw [suffixFrom_head]
        exact ⟨c, jsSt.env, by simp [bindEnv], hnames, hmin, henv, rfl, rfl, rfl, rfl, rfl, fun p hp => (List.mem_cons.1 hp).elim (fun h => by subst h; exact hcNone) (hsm.rec_disj _), hsm.env_eq, hsm.env_noTc, hsm.nonArr_ok, hnd, hwfVal⟩
      · simp only [beq_false_of_ne hjj, Bool.false_eq_true, ↓reduceIte] at hj'; obtain ⟨cv, cj, s1, rest⟩ := hsm.jps_some j' xs' val' capIr' hj' ((List.mem_cons.1 hmem').elim (fun h => absurd (Prod.mk.inj h).1 hjj) id)
        have hjpNe : jp j' ≠ jp j := fun h => hjj (jp_inj h); rw [show suffixFrom j'.idx ((j.idx, xs.size) :: recJps) = suffixFrom j'.idx recJps by simp [suffixFrom, beq_false_of_ne (Ne.symm hjj)]]; exact ⟨cv, cj, by simp [bindEnv, beq_false_of_ne hjpNe, s1], rest⟩),
    rec_ar := fun j' ar xs' val' capIr' hmem' hj' => (by
      by_cases hjj : j'.idx = j.idx
      · have hj'eq : j' = j := (by cases j'; cases j; simp_all); subst hj'eq; simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hj'; obtain ⟨rfl, rfl, rfl⟩ := hj'; exact (nodup_fst_eq hrecNodup hmem' (.head _) rfl).symm
      · simp only [beq_false_of_ne hjj, Bool.false_eq_true, ↓reduceIte] at hj'; exact hsm.rec_ar j' ar xs' val' capIr' ((List.mem_cons.1 hmem').elim (fun h => absurd (Prod.mk.inj h).1 hjj) id) hj'),
    rec_nodup := hrecNodup, rec_disj := fun p hp => (List.mem_cons.1 hp).elim (fun h => by subst h; exact hcNone) (hsm.rec_disj p) }
theorem StatesMatch.enterRecJp {prog c c0 inlineJps recJps allowTailCont irSt jsSt} (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) (hprogNA : ∀ (nonArr : Std.HashSet Nat) xs as ρ k, nonArr.contains k = true → (∀ m, nonArr.contains m = true → (ρ m).isNonArr = true) → (bindIrParams xs as ρ k).isNonArr = true) (hselfNodup : ∀ sf, c.selfFn = some sf → prog sf ≠ none ∧ c.selfParams.size > 0 ∧ (c.selfParams.toList.map (·.x.idx)).Nodup) {j : JoinPointId} {ys : Array Arg} {xs : Array Param} {val : FnBody} {capIr : Nat → JsVal} (hrec : (j.idx, ys.size) ∈ recJps) (hjir : irSt.jps j.idx = some (xs, val, capIr)) :
    ∃ cVal capJs, jsSt.fns (jp j) = some (xs.toList.map (v ·.x), lowerBody cVal val, capJs) ∧ cVal.names = c0.names ∧ cVal.min = c0.min ∧ cVal.env = c0.env ∧ cVal.selfFn = c.selfFn ∧ cVal.selfParams = c.selfParams ∧ cVal.directLoop = c.directLoop ∧ (∀ sf, cVal.selfFn = some sf → prog sf ≠ none ∧ cVal.selfParams.size > 0 ∧ (cVal.selfParams.toList.map (·.x.idx)).Nodup) ∧ BodyWf cVal prog [] (suffixFrom j.idx recJps) (if cVal.directLoop then false else allowTailCont) val ∧
      StatesMatch prog cVal c0 [] (suffixFrom j.idx recJps) (if cVal.directLoop then false else allowTailCont) { env := bindIrParams xs (ys.toList.map (evalIrArg irSt.env)) capIr, heap := irSt.heap, jps := irSt.jps, memos := irSt.memos } { env := bindMany ((xs.toList.map (v ·.x)).zip (ys.toList.map (evalIrArg irSt.env))) capJs, heap := jsSt.heap, fns := jsSt.fns, memos := jsSt.memos } := by
  obtain ⟨cVal, capJs, hjjs, hcvN, hcvM, hcvE, hcvNA, hcvPS, hcvSF, hcvSP, hcvDL, hcvInNone, hcapEq, hcapNoTc, hcapNA, hnd, hwfVal⟩ := hsm.jps_some j xs val capIr hjir ((hsm.rec_ar j ys.size xs val capIr hrec hjir) ▸ hrec)
  have hargsNoTc : ∀ a ∈ ys.toList.map (evalIrArg irSt.env), a.noTc := fun a ha => by rcases List.mem_map.1 ha with ⟨a', _, rfl⟩; exact evalIrArg_noTc hsm.env_noTc a'
  refine ⟨cVal, capJs, hjjs, hcvN, hcvM, hcvE, hcvSF, hcvSP, hcvDL, by rw [hcvSF, hcvSP]; exact hselfNodup, hwfVal,
    { env_eq := bindIrParams_toList_eq xs _ capIr capJs hnd hcapEq, heap_eq := hsm.heap_eq, memos_eq := hsm.memos_eq, memos_noTc := hsm.memos_noTc, env_noTc := bindIrParams_noTc xs.toList _ capIr hcapNoTc hargsNoTc,
      nonArr_ok := fun k hk => hprogNA cVal.nonArr xs _ capIr k hk fun m hm => hcapNA m (hcvNA ▸ hm), fns_only_jp := hsm.fns_only_jp, jps_none := hsm.jps_none,
      jps_some := fun j' xs' val' capIr' hj' hmem => (by
        obtain ⟨cv', cj', s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15⟩ := hsm.jps_some j' xs' val' capIr' hj' (mem_suffixFrom_mem hmem); have hsuf := suffixFrom_idem hsm.rec_nodup hmem
        refine ⟨cv', cj', s1, s2, s3, s4, hcvNA ▸ s5, hcvPS ▸ s6, hcvSF ▸ s7, hcvSP ▸ s8, hcvDL ▸ s9, fun p hp => s10 p (hsuf ▸ hp), s11, s12, fun k hk => s13 k (by rw [← hcvNA]; exact hk), s14, ?_⟩
        rw [hsuf, show (if cv'.directLoop then false else if cVal.directLoop then false else allowTailCont) = if cv'.directLoop then false else allowTailCont by rw [hcvDL, ← s9]; cases cv'.directLoop <;> rfl]; exact s15),
      rec_ar := fun j' ar xs' val' capIr' hmem hj' => hsm.rec_ar j' ar xs' val' capIr' (mem_suffixFrom_mem hmem) hj', rec_nodup := nodup_suffixFrom hsm.rec_nodup, rec_disj := fun p hp => hcvInNone p hp, inline_sub := fun _ _ hm => nomatch hm }⟩

def refMarkPair (h : CowHeap JsVal) : List JsVal → JsVal × CowHeap JsVal | [.arr id] => let p := h.refMark id; (.num p.1, p.2) | _ => (.num 0, h)
theorem StatesMatch.updRefMark {prog c c0 inlineJps recJps allowTailCont irSt jsSt} (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) (x : VarId) (vs : List JsVal) :
    StatesMatch prog c c0 inlineJps recJps allowTailCont { irSt with env := fun k => if k == x.idx then (refMarkPair irSt.heap vs).1 else irSt.env k, heap := (refMarkPair irSt.heap vs).2 } { jsSt with env := bindEnv jsSt.env (v x) (refMarkPair jsSt.heap vs).1, heap := (refMarkPair jsSt.heap vs).2 } := by
  cases vs with | nil => exact hsm.updVar x trivial fun _ => rfl | cons v0 rest => cases v0 with
    | arr id => cases rest with | nil => exact { hsm with env_eq := fun w => (by rw [hsm.heap_eq]; exact env_eq_update hsm.env_eq x _ w), heap_eq := by rw [hsm.heap_eq], env_noTc := env_noTc_bind hsm.env_noTc trivial, nonArr_ok := bindEnv_nonArr_of_expr c irSt.env x.idx _ hsm.nonArr_ok (fun _ => rfl) } | cons _ _ => exact hsm.updVar x trivial fun _ => rfl
    | num _ | bigInt _ | str _ | ctorObj _ _ _ _ _ _ | pap _ _ _ | tc _ => exact hsm.updVar x trivial fun _ => rfl
theorem evalJsStmts_inlineJp_post (jsProg : JsProg) (fJs : Nat) (jsStC : JsState) (j j' : JoinPointId) (hj'eq : j' = j) (args : List JsVal) (xs : Array Param) (hlen : xs.size = args.length) (hslots : ∀ i (hi : i < args.length), jsStC.env (inlineJpSlot j' i) = args[i]'hi) (rhs : List JsStmt) :
    evalJsStmts jsProg fJs jsStC ((if xs.isEmpty then [] else [JsStmt.letBinds (xs.toList.zipIdx.map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}"))]) ++ rhs) = evalJsStmts jsProg fJs (if xs.isEmpty then jsStC else { jsStC with env := bindMany (xs.toList.zipWith (fun p val => (v p.x, val)) args) jsStC.env }) rhs := by
  by_cases hemp : xs.isEmpty = true; simp [hemp]; have hzip := evalJsAssigns_zipIdx_vars jsProg fJs jsStC j args xs.toList 0 (by simp [hlen]) fun i hi => by simpa [← hj'eq] using hslots i (by simp at hi; omega)
  simp only [hemp, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, evalJsStmts, evalJsStmt, hzip]; simp

theorem evalIrAlts_sim_ij {prog c c0 jsProg revName fuel inlineJps recJps allowTailCont irSt jsSt irO irSt1} {x : VarId} (arms : List Alt) (hawf : AltsWf c prog inlineJps recJps allowTailCont arms)
    (ih : ∀ arm ∈ arms, BodyWf c prog inlineJps recJps allowTailCont arm.body → evalIrBody prog c0 revName (inlineJps.map Prod.fst) fuel irSt arm.body = some (irO, irSt1) → ExitMatchIJ prog c c0 jsProg revName fuel inlineJps recJps allowTailCont jsSt arm.body irO irSt1)
    (haev : evalIrAlts prog c0 revName (inlineJps.map Prod.fst) fuel irSt (jsTag (irSt.env x.idx)) arms = some (irO, irSt1)) :
    match irO with
    | .jumped j args => ∃ fJs jsSt1, evalJsArms jsProg fJs jsSt (jsTag (irSt.env x.idx)) (lowerAlts c arms) = some (.jumped (jp j), jsSt1) ∧ ExitJmpOk prog c c0 inlineJps recJps allowTailCont j args irSt1 jsSt1
    | .returned val => (∃ fJs jsSt1, evalJsArms jsProg fJs jsSt (jsTag (irSt.env x.idx)) (lowerAlts c arms) = some (.returned val, jsSt1) ∧ ExitRetOk prog c0 val irSt1 jsSt1) ∨
        (allowTailCont = true ∧ ∃ fJs jsSt1 sf nextArgs m₀ fIr', fIr' ≤ fuel ∧ c.selfFn = some sf ∧ (∀ a ∈ nextArgs, a.noTc) ∧ evalJsArms jsProg fJs jsSt (jsTag (irSt.env x.idx)) (lowerAlts c arms) = some (if c.directLoop then .tailCont nextArgs else .returned (.tc nextArgs), jsSt1) ∧ (∀ f, prog f ≠ none → m₀ f = jsSt1.memos (c0.js f)) ∧ (∀ f, (m₀ f).val.elim True JsVal.noTc) ∧ evalIrCall prog c0 revName fIr' jsSt1.heap m₀ sf nextArgs = some (val, irSt1.heap, irSt1.memos)) := by
  induction arms with
  | nil => simp [evalIrAlts] at haev
  | cons arm rest ihA =>
    cases arm with
    | ctor info bArm =>
        simp only [AltsWf, evalIrAlts, lowerAlts, evalJsArms] at hawf haev ⊢; by_cases hc : info.cidx = jsTag (irSt.env x.idx)
        · simp only [hc, beq_self_eq_true, ↓reduceIte] at haev ⊢; have hr := ih (.ctor info bArm) (.head _) hawf.1 haev; cases irO <;> exact hr
        · simp only [beq_false_of_ne hc, Bool.false_eq_true, ↓reduceIte] at haev ⊢; have h1 := ihA hawf.2 (fun a hm => ih a (.tail _ hm)) haev; cases irO <;> simpa [evalIrAlts, beq_false_of_ne hc] using h1
    | default bArm => simp only [AltsWf, evalIrAlts, lowerAlts, evalJsArms] at hawf haev ⊢; have hr := ih (.default bArm) (.head _) hawf.1 haev; cases irO <;> exact hr

theorem evalJsArms_sim_ji {prog c c0 jsProg revName fuel inlineJps recJps allowTailCont irSt jsSt ex jsSt1} {x : VarId} (arms : List Alt) (hawf : AltsWf c prog inlineJps recJps allowTailCont arms)
    (ih : ∀ arm ∈ arms, BodyWf c prog inlineJps recJps allowTailCont arm.body → evalJsStmts jsProg fuel jsSt (lowerBody c arm.body) = some (ex, jsSt1) → ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt arm.body ex jsSt1)
    (haev : evalJsArms jsProg fuel jsSt (jsTag (irSt.env x.idx)) (lowerAlts c arms) = some (ex, jsSt1)) :
    ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt (.case default x default arms.toArray) ex jsSt1 := by
  induction arms with
  | nil => simp [lowerAlts, evalJsArms] at haev
  | cons arm rest ihA =>
    cases arm with
    | ctor info bArm =>
        simp only [AltsWf, lowerAlts, evalJsArms] at hawf haev; by_cases hc : info.cidx = jsTag (irSt.env x.idx)
        · simp only [hc, beq_self_eq_true, ↓reduceIte] at haev
          exact ExitMatchJI.rwBody (ih (.ctor info bArm) (.head _) hawf.1 haev) fun _ => by simp [evalIrBody, evalIrAlts, Alt.body, hc]
        · simp only [beq_false_of_ne hc, Bool.false_eq_true, ↓reduceIte] at haev
          exact ExitMatchJI.rwBody (ihA hawf.2 (fun a hm => ih a (.tail _ hm)) haev) fun _ => by simp [evalIrBody, evalIrAlts, beq_false_of_ne hc]
    | default bArm =>
        simp only [AltsWf, lowerAlts, evalJsArms] at hawf haev
        exact ExitMatchJI.rwBody (ih (.default bArm) (.head _) hawf.1 haev) fun _ => by simp [evalIrBody, evalIrAlts, Alt.body]

theorem eval_sim_ij_rcDec {prog : IrProg} {c c0 : Ctx} {jsProg : JsProg} {revName : String → Option Name} {fSub : Nat} {inlineJps recJps allowTailCont} {irSt : IrState} {jsSt : JsState} (x : VarId) (n : Nat) (b cont : FnBody) {irO irSt1}
    (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt)
    (hlow : lowerBody c b = if c.nonArr.contains x.idx then lowerBody c cont else [.decRef (v x) n] ++ lowerBody c cont)
    (hir : evalIrBody prog c0 revName (inlineJps.map Prod.fst) fSub irSt b = evalIrBody prog c0 revName (inlineJps.map Prod.fst) fSub { irSt with heap := irSt.heap.rcDec (irSt.env x.idx).toRcVal n } cont)
    (hcont : ∀ irSt' jsSt', StatesMatch prog c c0 inlineJps recJps allowTailCont irSt' jsSt' → evalIrBody prog c0 revName (inlineJps.map Prod.fst) fSub irSt' cont = some (irO, irSt1) → ExitMatchIJ prog c c0 jsProg revName fSub inlineJps recJps allowTailCont jsSt' cont irO irSt1)
    (hev : evalIrBody prog c0 revName (inlineJps.map Prod.fst) fSub irSt b = some (irO, irSt1)) : ExitMatchIJ prog c c0 jsProg revName fSub inlineJps recJps allowTailCont jsSt b irO irSt1 := by
  rw [hir] at hev; by_cases hna : c.nonArr.contains x.idx = true
  · rw [rcDec_nonArr_noop_isNonArr irSt.heap (irSt.env x.idx) n (hsm.nonArr_ok _ hna)] at hev
    exact ExitMatchIJ.rwJsMono (f₁ := 0) (fun _ _ => by simp [hlow, hna]) (hcont irSt jsSt hsm hev)
  · exact ExitMatchIJ.rwJsMono (f₁ := 0) (fun _ _ => by simp [hlow, Bool.eq_false_iff.2 hna, evalJsStmts, evalJsStmt])
      (hcont _ { jsSt with heap := jsSt.heap.rcDec (jsSt.env (v x)).toRcVal n } (hsm.updHeap (by rw [hsm.heap_eq, hsm.env_eq x])) hev)

theorem eval_sim_ji_rcDec {prog : IrProg} {c c0 : Ctx} {jsProg : JsProg} {revName : String → Option Name} {fSub : Nat} {inlineJps recJps allowTailCont} {irSt : IrState} {jsSt jsSt1 : JsState} (x : VarId) (n : Nat) (b cont : FnBody) {ex}
    (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt)
    (hlow : lowerBody c b = if c.nonArr.contains x.idx then lowerBody c cont else [.decRef (v x) n] ++ lowerBody c cont)
    (hir : ∀ fIr, evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr irSt b = evalIrBody prog c0 revName (inlineJps.map Prod.fst) fIr { irSt with heap := irSt.heap.rcDec (irSt.env x.idx).toRcVal n } cont)
    (hcont : ∀ irSt' jsSt', StatesMatch prog c c0 inlineJps recJps allowTailCont irSt' jsSt' → evalJsStmts jsProg fSub jsSt' (lowerBody c cont) = some (ex, jsSt1) → ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt' cont ex jsSt1)
    (hev : evalJsStmts jsProg fSub jsSt (lowerBody c b) = some (ex, jsSt1)) : ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt b ex jsSt1 := by
  rw [hlow] at hev; by_cases hna : c.nonArr.contains x.idx = true
  · simp only [hna, ↓reduceIte] at hev; exact ExitMatchJI.rwBody (hcont irSt jsSt hsm hev) fun fIr => by rw [hir fIr, rcDec_nonArr_noop_isNonArr _ _ n (hsm.nonArr_ok _ hna)]
  · simp only [Bool.eq_false_iff.2 hna, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append, evalJsStmts, evalJsStmt] at hev
    exact ExitMatchJI.rwBody (hcont _ _ (hsm.updHeap (by rw [hsm.heap_eq, hsm.env_eq x])) hev) hir

theorem eval_sim_ij_pure_vdecl {prog : IrProg} {c c0 : Ctx} {jsProg : JsProg} {revName : String → Option Name} {fSub : Nat} {inlineJps recJps allowTailCont} {irSt : IrState} {jsSt : JsState} {x : VarId} {ty : IRType} {cont : FnBody} {irO irSt1}
    (hprog : ProgLowered prog c0 jsProg revName) (hnames : c.names = c0.names) (henv : c.env = c0.env) (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) (e : IR.Expr) (hpure : match e with | .fap _ _ | .ap _ _ | .isShared _ => False | _ => True) (hpap : ∀ f ys, e = .pap f ys → ∃ d, prog f = some d) (hnaV : c.nonArr.contains x.idx = true → (evalIrPure c0 ty irSt.env e).isNonArr = true)
    (hcont : StatesMatch prog c c0 inlineJps recJps allowTailCont { irSt with env := fun k => if k == x.idx then evalIrPure c0 ty irSt.env e else irSt.env k } { jsSt with env := bindEnv jsSt.env (v x) (evalIrPure c0 ty irSt.env e) } → evalIrBody prog c0 revName (inlineJps.map Prod.fst) fSub { irSt with env := fun k => if k == x.idx then evalIrPure c0 ty irSt.env e else irSt.env k } cont = some (irO, irSt1) → ExitMatchIJ prog c c0 jsProg revName fSub inlineJps recJps allowTailCont { jsSt with env := bindEnv jsSt.env (v x) (evalIrPure c0 ty irSt.env e) } cont irO irSt1)
    (hev : evalIrBody prog c0 revName (inlineJps.map Prod.fst) fSub irSt (.vdecl x ty e cont) = some (irO, irSt1)) : ExitMatchIJ prog c c0 jsProg revName fSub inlineJps recJps allowTailCont jsSt (.vdecl x ty e cont) irO irSt1 := by
  have hce := evalIrPure_ctx_eq c c0 hnames henv ty irSt.env e; have hnoTcV := evalIrPure_noTc c0 ty hsm.env_noTc e fun f' ys' he => let ⟨d, hd⟩ := hpap f' ys' he; (hprog.fn_disjoint (c0.js f') f' (hprog.rev_ok f' d hd)).1
  have hev' : evalIrBody prog c0 revName (inlineJps.map Prod.fst) fSub { irSt with env := fun k => if k == x.idx then evalIrPure c0 ty irSt.env e else irSt.env k } cont = some (irO, irSt1) := by cases e <;> first | exact False.elim hpure | (simp only [evalIrBody] at hev; simpa [hce] using hev)
  have hstep : lowerBody c (.vdecl x ty e cont) = .letVar (v x) (lowerExpr c ty e) :: lowerBody c cont := by cases e <;> first | exact False.elim hpure | rfl
  exact ExitMatchIJ.rwJsMono (f₁ := 0) (fun fJs _ => by rw [hstep, evalJsStmts, evalJsStmt, evalJsExprM_lowerPure jsProg fJs c ty jsSt irSt.env hsm.env_eq e hpure, hce]) (hcont (hsm.updVar x hnoTcV hnaV) hev')

theorem eval_sim_ji_pure_vdecl {prog : IrProg} {c c0 : Ctx} {jsProg : JsProg} {revName : String → Option Name} {fSub : Nat} {inlineJps recJps allowTailCont} {irSt : IrState} {jsSt jsSt1 : JsState} {x : VarId} {ty : IRType} {cont : FnBody} {ex}
    (hprog : ProgLowered prog c0 jsProg revName) (hnames : c.names = c0.names) (henv : c.env = c0.env) (hsm : StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt) (e : IR.Expr) (hpure : match e with | .fap _ _ | .ap _ _ | .isShared _ => False | _ => True) (hpap : ∀ f ys, e = .pap f ys → ∃ d, prog f = some d) (hnaV : c.nonArr.contains x.idx = true → (evalIrPure c0 ty irSt.env e).isNonArr = true)
    (hcont : StatesMatch prog c c0 inlineJps recJps allowTailCont { irSt with env := fun k => if k == x.idx then evalIrPure c0 ty irSt.env e else irSt.env k } { jsSt with env := bindEnv jsSt.env (v x) (evalIrPure c0 ty irSt.env e) } → evalJsStmts jsProg fSub { jsSt with env := bindEnv jsSt.env (v x) (evalIrPure c0 ty irSt.env e) } (lowerBody c cont) = some (ex, jsSt1) → ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont { irSt with env := fun k => if k == x.idx then evalIrPure c0 ty irSt.env e else irSt.env k } cont ex jsSt1)
    (hev : evalJsStmts jsProg fSub jsSt (lowerBody c (.vdecl x ty e cont)) = some (ex, jsSt1)) : ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt (.vdecl x ty e cont) ex jsSt1 := by
  have hce := evalIrPure_ctx_eq c c0 hnames henv ty irSt.env e; have hnoTcV := evalIrPure_noTc c0 ty hsm.env_noTc e fun f' ys' he => let ⟨d, hd⟩ := hpap f' ys' he; (hprog.fn_disjoint (c0.js f') f' (hprog.rev_ok f' d hd)).1
  have hstep : lowerBody c (.vdecl x ty e cont) = .letVar (v x) (lowerExpr c ty e) :: lowerBody c cont := by cases e <;> first | exact False.elim hpure | rfl
  rw [hstep, evalJsStmts, evalJsStmt, evalJsExprM_lowerPure jsProg fSub c ty jsSt irSt.env hsm.env_eq e hpure, hce] at hev
  exact ExitMatchJI.rwBody (hcont (hsm.updVar x hnoTcV hnaV) hev) fun _ => by cases e <;> first | exact False.elim hpure | (simp only [evalIrBody]; try rw [hce])

end Js.Proofs
