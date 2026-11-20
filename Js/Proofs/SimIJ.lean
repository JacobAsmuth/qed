import Js.Proofs.Semantics

namespace Js.Proofs

open Lean IR

/-! ## 5a. Forward Simulation (`IR → JS`) -/

private theorem eval_sim_ij_body_step (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name)
    (hprog : ProgLowered prog c0 jsProg revName) (fSub : Nat) (hcallSub : CallSimIJ prog c0 jsProg revName fSub)
    (happSub : AppSimIJ prog c0 jsProg revName fSub) (hbodyPrev : ∀ f' < fSub, BodySimIJ prog c0 jsProg revName f') : BodySimIJ prog c0 jsProg revName fSub := by
  intro c inlineJps recJps allowTailCont b; revert c inlineJps recJps allowTailCont
  refine fnBody_ind (fun b => ∀ c inlineJps recJps allowTailCont irSt jsSt irO irSt1, c.names = c0.names → c.min = c0.min → c.env = c0.env →
    (∀ sf, c.selfFn = some sf → prog sf ≠ none ∧ c.selfParams.size > 0 ∧ (c.selfParams.toList.map (·.x.idx)).Nodup) → BodyWf c prog inlineJps recJps allowTailCont b →
    StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt → evalIrBody prog c0 revName (inlineJps.map Prod.fst) fSub irSt b = some (irO, irSt1) →
    ExitMatchIJ prog c c0 jsProg revName fSub inlineJps recJps allowTailCont jsSt b irO irSt1)
    (fun b hb c inlineJps recJps allowTailCont irSt jsSt irO irSt1 hnames hmin henv hselfNodup hwf hsm hev => ?_) b
  cases b with
  | ret a =>
      simp only [evalIrBody, Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev; left
      exact ⟨0, jsSt, by simp [lowerBody, evalJsStmts, evalJsStmt, evalJsExprM_lowerArg jsProg 0 jsSt irSt.env hsm.env_eq a], evalIrArg_noTc hsm.env_noTc a, hsm.heap_eq, hsm.memos_eq, hsm.memos_noTc⟩
  | unreachable => simp [evalIrBody] at hev
  | set x i y cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_set x i y cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf) hev
  | setTag x cidx cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_setTag x cidx cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf) hev
  | uset x i y cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_uset x i y cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf) hev
  | sset x n off y ty cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_sset x n off y ty cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf) hev
  | dec x n cf bf cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_rcDec x n (.dec x n cf bf cont) cont hsm rfl fun _ => by simp only [evalIrBody]) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf) hev
  | del x cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_rcDec x 1 (.del x cont) cont hsm rfl fun _ => by simp only [evalIrBody]) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf) hev
  | inc x n cf bf cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_inc x n cf bf cont hsm hwf.2) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf.1) hev
  | case tid x xType alts =>
      rw [BodyWf] at hwf; simp only [evalIrBody] at hev
      have hsw := caseScrut_eq jsProg c tid x xType alts hsm.env_eq
      have hres := evalIrAlts_sim_ij (x := x) alts.toList hwf (fun arm hm hwfa ha => hb arm hm c inlineJps recJps allowTailCont irSt jsSt irO irSt1 hnames hmin henv hselfNodup hwfa hsm ha) hev
      cases irO with
      | jumped _ _ => rcases hres with ⟨fJs, st1, hjs, hok⟩; exact ⟨fJs, st1, by rw [hsw fJs]; exact hjs, hok⟩
      | returned _ =>
          rcases hres with ⟨fJs, st1, hjs, hok⟩ | ⟨hal, fJs, st1, sf, na, m0, fIr', hle, hsf, hna', hjs, hm0, hm0n, hrc⟩
          · left; exact ⟨fJs, st1, by rw [hsw fJs]; exact hjs, hok⟩
          · right; exact ⟨hal, fJs, st1, sf, na, m0, fIr', hle, hsf, hna', by rw [hsw fJs]; exact hjs, hm0, hm0n, hrc⟩
  | jmp j ys =>
      rw [BodyWf] at hwf; rcases hwf with hin | hrec
      · obtain ⟨hnotInM, hjsStep, hok⟩ := inlineJmp_step (jsProg := jsProg) hsm hin
        rw [evalIrBody_jmp_inline _ _ _ _ _ _ _ _ hnotInM] at hev; simp only [Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev
        exact ⟨0, _, hjsStep 0, hok⟩
      · have hnone : c.inlineJps.get? j.idx = none := hsm.rec_disj (j.idx, ys.size) hrec
        have hnotIn : j.idx ∉ inlineJps.map Prod.fst := fun hm => by rcases List.mem_map.1 hm with ⟨p, hp, hpe⟩; obtain ⟨xs, hxs, _⟩ := hsm.inline_sub p.1 p.2 hp; rw [hpe, hnone] at hxs; contradiction
        cases fSub with
        | zero => simp [evalIrBody, hnotIn] at hev
        | succ f' =>
            rw [evalIrBody_jmp_not_inline _ _ _ _ _ _ _ _ hnotIn] at hev; cases hjir : irSt.jps j.idx with | none => rw [hjir] at hev; cases hev | some jdata =>
            rcases jdata with ⟨xs, val, capIr⟩; rw [hjir] at hev; dsimp only at hev
            obtain ⟨cVal, capJs, hjjs, hcvN, hcvM, hcvE, hcvSF, hcvSP, hcvDL, hselfVal, hwfVal, hsmVal⟩ := hsm.enterRecJp hprog.nonArr_param hselfNodup hrec hjir
            cases hirV : evalIrBody prog c0 revName [] f' { env := bindIrParams xs (ys.toList.map (evalIrArg irSt.env)) capIr, heap := irSt.heap, jps := irSt.jps, memos := irSt.memos } val with
            | none => rw [hirV] at hev; cases hev
            | some irR =>
                rcases irR with ⟨irOVal, st1⟩; rw [hirV] at hev; cases irOVal with | jumped _ _ => cases hev | returned rval =>
                simp only [Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev
                have hex := hbodyPrev f' (Nat.lt_succ_self f') cVal [] (suffixFrom j.idx recJps) _ val _ _ (.returned rval) st1 hcvN hcvM hcvE hselfVal hwfVal hsmVal hirV
                have hnone' : c.inlineJps[j.idx]? = none := hnone
                rcases hex with ⟨fJsVal, jsStVal, hjsVal, hnt, hhp1, hmEq1, hmNo1⟩ | ⟨halV, fJsVal, jsStVal, sf, na, m0, fIr', hle', hsf, hna', hjsVal, hm0, hm0n, hrc⟩
                · left; refine ⟨fJsVal + 1, { jsSt with heap := jsStVal.heap, memos := jsStVal.memos }, ?_, hnt, hhp1, hmEq1, hmNo1⟩
                  simp [lowerBody, hnone', evalJsStmts, evalJsStmt, evalJsExprM_call_jp, evalJsExprListM_lowerArgs jsProg (fJsVal + 1) jsSt irSt.env hsm.env_eq ys.toList, evalJsCall, hjjs, hjsVal]
                · have hcValDL : cVal.directLoop = false := by cases h : cVal.directLoop <;> simp_all
                  rw [hcValDL] at hjsVal; right; refine ⟨by simpa [hcValDL] using halV, fJsVal + 1, { jsSt with heap := jsStVal.heap, memos := jsStVal.memos }, sf, na, m0, fIr', Nat.le_succ_of_le hle', hcvSF ▸ hsf, hna', ?_, hm0, hm0n, hrc⟩
                  rw [← hcvDL, hcValDL]; simp [lowerBody, hnone', evalJsStmts, evalJsStmt, evalJsExprM_call_jp, evalJsExprListM_lowerArgs jsProg (fJsVal + 1) jsSt irSt.env hsm.env_eq ys.toList, evalJsCall, hjjs, hjsVal]
  | jdecl j xs val cont =>
      rw [BodyWf] at hwf; rcases hwf with ⟨hnd, hnotIn, hnotRec, hcNone, hrec⟩; by_cases hjmp : (!hasJmpTo j val) = true
      · simp only [hjmp, ↓reduceIte] at hrec; simp only [evalIrBody, hjmp, ↓reduceIte] at hev
        have hlower : ∀ fJs st, evalJsStmts jsProg fJs st (lowerBody c (.jdecl j xs val cont)) = match evalJsStmts jsProg fJs st (lowerBody { c with inlineJps := c.inlineJps.insert j.idx xs } cont) with
          | some (.jumped l, st1) => if l == jp j then evalJsStmts jsProg fJs st1 ((if xs.isEmpty then [] else [JsStmt.letBinds (xs.toList.zipIdx.map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}"))]) ++ lowerBody c val) else some (.jumped l, st1)
          | some (.next, st1) => evalJsStmts jsProg fJs st1 ((if xs.isEmpty then [] else [JsStmt.letBinds (xs.toList.zipIdx.map fun (p, i) => (v p.x, JsExpr.var s!"_{jp j}_{i}"))]) ++ lowerBody c val) | res => res := fun fJs st => by
          simp only [lowerBody, hjmp, ↓reduceIte, List.append_assoc]; rw [evalJsStmts_letDecls_skip]; simp only [List.cons_append, List.nil_append, evalJsStmts, evalJsStmt]
          cases evalJsStmts jsProg fJs st (lowerBody { c with inlineJps := c.inlineJps.insert j.idx xs } cont) with | none => rfl | some r => rcases r with ⟨ex, _⟩; cases ex with
            | jumped l => by_cases hlj : (l == jp j) = true <;> simp [hlj] | next | returned _ | tailCont _ => rfl
        cases hirC : evalIrBody prog c0 revName (j.idx :: inlineJps.map Prod.fst) fSub irSt cont with | none => rw [hirC] at hev; cases hev | some irRC =>
        rcases irRC with ⟨irOC, irStC⟩; rw [hirC] at hev
        have hexC := hb.2 { c with inlineJps := c.inlineJps.insert j.idx xs } ((j.idx, xs.size) :: inlineJps) recJps allowTailCont irSt jsSt irOC irStC hnames hmin henv hselfNodup hrec.1 (hsm.pushInlineJp j xs hnotIn hnotRec) hirC
        cases irOC with
        | returned rv =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev; dsimp only [ExitMatchIJ] at hexC ⊢
            rcases hexC with ⟨fJs, jsSt1, hjs, hok⟩ | ⟨hal, fJs, jsSt1, sf, na, m0, fIr', hle, hsf, hna', hjs, hm0, hm0n, hrc⟩
            · left; exact ⟨fJs, jsSt1, by rw [hlower fJs jsSt, hjs], hok⟩
            · right; exact ⟨hal, fJs, jsSt1, sf, na, m0, fIr', hle, hsf, hna', by rw [hlower fJs jsSt, hjs]; cases c.directLoop <;> rfl, hm0, hm0n, hrc⟩
        | jumped j' args =>
            dsimp only at hev; rcases hexC with ⟨fJsC, jsStC, hjsC, hin', hslots, hargsNoTc, hsm1⟩; by_cases hj'j : j'.idx = j.idx
            · have hj'eq : j' = j := (by cases j'; cases j; cases hj'j; rfl); have hjpBeq : (jp j' == jp j) = true := by rw [hj'eq]; simp
              rw [show (j' == j) = true from hj'eq ▸ jp_beq_self j] at hev; simp only [↓reduceIte] at hev
              have hlen : xs.size = args.length := (List.mem_cons.1 hin').elim (fun h => (Prod.mk.inj h).2.symm) fun h => absurd h fun h' => hnotIn _ (by rw [← hj'j]; exact h')
              exact ExitMatchIJ.rwJsMono (f₁ := fJsC) (fun fJs hf => by rw [hlower _ jsSt, evalJsStmts_mono hf hjsC]; dsimp only; rw [if_pos hjpBeq, evalJsStmts_inlineJp_post jsProg fJs jsStC j j' hj'eq args xs hlen hslots])
                (hb.1 c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hrec.2 (hsm1.bindInlineJp hsm.rec_disj hsm.inline_sub xs args hnd hlen hargsNoTc fun k hk => hprog.nonArr_param c.nonArr xs args _ k hk hsm1.nonArr_ok) hev)
            · have hjpNe : (jp j' == jp j) = false := beq_false_of_ne fun hje => hj'j (jp_inj hje)
              have hneJ : (j' == j) = false := by change (j'.idx == j.idx) = false; exact beq_false_of_ne hj'j
              rw [if_neg (by rw [hneJ]; simp)] at hev; simp only [Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev
              exact ⟨fJsC, jsStC, by rw [hlower fJsC jsSt, hjsC]; simp [hjpNe], (List.mem_cons.1 hin').elim (fun h => absurd (Prod.mk.inj h).1 hj'j) id, hslots, hargsNoTc, hsm1.withCtx rfl rfl rfl rfl rfl hsm.rec_disj hsm.inline_sub⟩
      · have hjmpF : (!hasJmpTo j val) = false := Bool.eq_false_iff.2 hjmp; simp only [hjmpF, Bool.false_eq_true, ↓reduceIte] at hrec
        exact ExitMatchIJ.dropRecHead hnotRec (ExitMatchIJ.ofLockstep (lockstep_rec_jdecl hnames hmin henv j xs val cont hjmpF hnd hnotRec hcNone hrec.1 hsm) (fun _ _ => hb.2 c inlineJps ((j.idx, xs.size) :: recJps) allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hrec.2) hev)
  | vdecl x ty e cont =>
      rw [BodyWf] at hwf; rcases hwf with ⟨hwfc, hwe⟩; dsimp only [ExprWf] at hwe; cases e with
      | fap f ys =>
          by_cases href : f = `Qed.refMark
          · subst href; simp only [beq_self_eq_true, ↓reduceIte] at hwe
            exact ExitMatchIJ.ofLockstep (lockstep_refMark x ty ys cont hsm hwe) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwfc) hev
          · have hrefF : (f == `Qed.refMark) = false := beq_false_of_ne href; simp only [hrefF, Bool.false_eq_true, ↓reduceIte] at hwe
            rcases hwe with ⟨⟨_, _, _, _, hfd⟩, htail⟩; have hlow := findEnv_fap_args c c0 f ys hnames henv (hprog.findEnv_ok f _ hfd).1 href
            obtain ⟨hne1, hne2, hne3⟩ := (hprog.fn_disjoint (c0.js f) f (hprog.rev_ok f _ hfd)).2; simp only [evalIrBody, hrefF, Bool.false_eq_true, ↓reduceIte] at hev
            cases hirc : evalIrCall prog c0 revName fSub irSt.heap irSt.memos f (ys.toList.map (evalIrArg irSt.env)) with | none => rw [hirc] at hev; cases hev | some irRes =>
            rcases irRes with ⟨val, h', m'⟩; rw [hirc] at hev; obtain ⟨hvalNT, hm'NT⟩ := hprog.nonArr_typed fSub irSt.heap irSt.memos f _ val h' m' hsm.memos_noTc hirc
            have hna' := bindEnv_nonArr_of_expr c irSt.env x.idx val hsm.nonArr_ok (fun hm => (hprog.nonArr_call c.nonArr fSub irSt.heap irSt.memos f _ val h' m' x.idx hm).1 hirc)
            by_cases htc : (c.selfFn == some f && retsVar x cont) = true
            · obtain ⟨hal, htrc, _⟩ := htail htc; have hsf : c.selfFn = some f := eq_of_beq (Bool.and_eq_true_iff.1 htc).1; have hretV : retsVar x cont = true := (Bool.and_eq_true_iff.1 htc).2
              have htailEq := evalIrBody_tailRcVarsOk prog c0 c.nonArr revName (inlineJps.map Prod.fst) fSub x cont { env := fun k => if k == x.idx then val else irSt.env k, heap := h', jps := irSt.jps, memos := m' } htrc hretV hna'
              simp only [beq_self_eq_true, ↓reduceIte] at htailEq; dsimp only at hev; rw [htailEq, Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev
              have hnaNT : ∀ a ∈ ys.toList.map (evalIrArg irSt.env), a.noTc := fun a ha => by rcases List.mem_map.1 ha with ⟨a', _, rfl⟩; exact evalIrArg_noTc hsm.env_noTc a'
              right; cases hdl : c.directLoop
              · exact ⟨hal, 0, jsSt, f, ys.toList.map (evalIrArg irSt.env), irSt.memos, fSub, Nat.le_refl _, hsf, hnaNT, by simp [lowerBody, htc, hdl, evalJsStmts, evalJsStmt, evalJsExprM, evalJsExprListM_lowerArgs jsProg 0 jsSt irSt.env hsm.env_eq ys.toList], hsm.memos_eq, hsm.memos_noTc, by rw [← hsm.heap_eq, hirc]⟩
              · exact ⟨hal, 0, { jsSt with env := bindMany ((c.selfParams.toList.map (v ·.x)).zip (ys.toList.map (evalIrArg irSt.env))) jsSt.env }, f, ys.toList.map (evalIrArg irSt.env), irSt.memos, fSub, Nat.le_refl _, hsf, hnaNT, by simp [lowerBody, htc, hdl, evalJsStmts, evalJsStmt, evalJsExprListM_lowerArgs jsProg 0 jsSt irSt.env hsm.env_eq ys.toList], hsm.memos_eq, hsm.memos_noTc, by rw [← hsm.heap_eq, hirc]⟩
            · obtain ⟨fJs1, jsSt1, hjsc, _, _, hhp', hme1, hmfns1, hmeq1, hmno1⟩ := hcallSub irSt.heap irSt.memos f (ys.toList.map (evalIrArg irSt.env)) jsSt val h' m'
                (by rw [hfd]; simp) hsm.heap_eq hsm.memos_eq hsm.memos_noTc (fun a ha => by rcases List.mem_map.1 ha with ⟨a', _, rfl⟩; exact evalIrArg_noTc hsm.env_noTc a') hsm.fns_only_jp hirc
              exact ExitMatchIJ.rwJsMono (f₁ := fJs1) (fun fJs hf => by simp [lowerBody, lowerExpr, hlow, Bool.eq_false_iff.2 htc, evalJsStmts, evalJsStmt, evalJsExprM, hne1, hne2, hne3, evalJsExprListM_lowerArgs jsProg fJs jsSt irSt.env hsm.env_eq ys.toList, evalJsCall_mono hf hjsc])
                (hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwfc (hsm.updCall x hvalNT (fun hm => (hprog.nonArr_call c.nonArr fSub irSt.heap irSt.memos f _ val h' m' x.idx hm).1 hirc) hhp' hme1 hmfns1 hmeq1 hmno1) hev)
      | ap y ys =>
          simp only [evalIrBody] at hev; cases hirc : evalIrApp prog c0 revName fSub irSt.heap irSt.memos (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) with | none => rw [hirc] at hev; cases hev | some irRes =>
          rcases irRes with ⟨val, h', m'⟩; rw [hirc] at hev
          obtain ⟨fJs1, jsSt1, hjsc, _, hvnt, hhp', hme1, hmfns1, hmeq1, hmno1⟩ := happSub irSt.heap irSt.memos (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) jsSt val h' m' hsm.heap_eq hsm.memos_eq hsm.memos_noTc (hsm.env_noTc y.idx) (fun a ha => by rcases List.mem_map.1 ha with ⟨a', _, rfl⟩; exact evalIrArg_noTc hsm.env_noTc a') hsm.fns_only_jp hirc
          exact ExitMatchIJ.rwJsMono (f₁ := fJs1) (fun fJs hf => by simp [lowerBody, lowerExpr, evalJsStmts, evalJsStmt, evalJsExprM, ← hsm.env_eq y, evalJsExprListM_lowerArgs jsProg fJs jsSt irSt.env hsm.env_eq ys.toList, evalJsApp_mono hf hjsc])
            (hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwfc (hsm.updCall x hvnt (fun hm => (hprog.nonArr_call c.nonArr fSub irSt.heap irSt.memos default _ val h' m' x.idx hm).2 (irSt.env y.idx) hirc) hhp' hme1 hmfns1 hmeq1 hmno1) hev)
      | isShared y => exact ExitMatchIJ.ofLockstep (lockstep_isShared x ty y cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwfc) hev
      | pap _ _ => exact ExitMatchIJ.ofLockstep (lockstep_pure_vdecl hprog hnames henv hsm _ trivial (fun f' ys' he => by injection he with hf _; exact hf ▸ hwe) (fun _ => evalIrPure_ctor_isNonArr c0 ty irSt.env _ trivial)) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwfc) hev
      | ctor _ _ | reuse _ _ _ _ | reset _ _ | lit _ => exact ExitMatchIJ.ofLockstep (lockstep_pure_vdecl hprog hnames henv hsm _ trivial (fun _ _ he => nomatch he) (fun _ => evalIrPure_ctor_isNonArr c0 ty irSt.env _ trivial)) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwfc) hev
      | proj _ _ | uproj _ _ | sproj _ _ _ | box _ _ | unbox _ => exact ExitMatchIJ.ofLockstep (lockstep_pure_vdecl hprog hnames henv hsm _ trivial (fun _ _ he => nomatch he) (fun hx => hprog.nonArr_pure c.nonArr irSt.env ty x _ hx hsm.nonArr_ok)) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwfc) hev

private theorem eval_sim_ij_call_step (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (hprog : ProgLowered prog c0 jsProg revName) (f' : Nat) (ihCall : ∀ k < f' + 1, CallSimIJ prog c0 jsProg revName k) (ihBody : BodySimIJ prog c0 jsProg revName f') :
    CallSimIJ prog c0 jsProg revName (f' + 1) := by
  intro h mIr f args jsSt v1 h1 m1 hf hhp hmEq hmNo hargs hfns hirc
  cases hpf : prog f with | none => simp [evalIrCall, hpf] at hirc | some d => cases d with
  | extern _ _ _ _ => exact False.elim (hprog.findEnv_ok f _ hpf).2.1
  | fdecl fnm xs ty b info =>
      have hfnm := hprog.fdecl_name f fnm xs ty b info hpf; subst fnm
      have hfnsNone := fdecl_fns_none hprog hpf hfns
      have hjsD := hprog.js_at_fdecl f xs ty b info hpf; have hdwf := hprog.decl_wf f xs ty b info hpf; dsimp only at hdwf
      have hjsCtx : ∀ na ps g, ({ c0 with nonArr := na, projSrc := ps } : Ctx).js g = c0.js g := fun _ _ _ => rfl
      simp only [evalIrCall, hpf] at hirc; by_cases hemp : xs.isEmpty = true
      · simp only [hemp, ↓reduceIte] at hirc hdwf; have hcOk : (mIr f).ok = (jsSt.memos (c0.js f)).ok := by rw [hmEq f hf]
        by_cases hmok : (mIr f).ok = true
        · simp only [hmok, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hirc; obtain ⟨rfl, rfl, rfl⟩ := hirc
          have hnt : ((mIr f).val.getD (.num 0)).noTc := by have hmv := hmNo f; cases hv : (mIr f).val with | none => exact trivial | some _ => rw [hv] at hmv; simpa using hmv
          exact ⟨1, jsSt, (by cases hini : getInitFnNameFor? c0.env f <;> simp [evalJsCall, hfnsNone, hjsD, lowerDecl, hjsCtx, hemp, hini, evalJsDecl, ← hmEq f hf, hmok]), rfl, hnt, hhp, rfl, rfl, hmEq, hmNo⟩
        · have hmokF : (mIr f).ok = false := Bool.eq_false_iff.2 hmok; have hmokJs : (jsSt.memos (c0.js f)).ok = false := by rw [← hcOk, hmokF]
          simp only [hmokF, Bool.false_eq_true, ↓reduceIte] at hirc; cases hini : getInitFnNameFor? c0.env f with
          | some initFn =>
              simp only [hini] at hirc hdwf; rcases hdwf with ⟨_, _, _, _, hiniDom, _⟩
              cases hirI : evalIrCall prog c0 revName f' h mIr initFn [] with | none => rw [hirI] at hirc; cases hirc | some irR =>
              rcases irR with ⟨v0, h0, m0⟩; rw [hirI, Option.some.injEq, Prod.mk.injEq] at hirc; obtain ⟨rfl, rfl, rfl⟩ := hirc
              obtain ⟨fJsI, stI, hjsI, _, hvnt, hh1, _, _, hm1Eq, hm1No⟩ := ihCall f' (Nat.lt_succ_self f') h mIr initFn [] jsSt v0 h1 m0 (by rw [hiniDom]; simp) hhp hmEq hmNo (fun _ h => nomatch h) hfns hirI
              exact ⟨fJsI + 1, { jsSt with heap := stI.heap, memos := fun k => if k == c0.js f then { ok := true, val := some v0 } else stI.memos k },
                by simp [evalJsCall, hfnsNone, hjsD, lowerDecl, hjsCtx, hemp, hini, evalJsDecl, hmokJs, hjsI], rfl, hvnt, hh1, rfl, rfl, memoUpdate_eq hprog.rev_ok hm1Eq hf v0, fun g => by dsimp only; split; exact hvnt; exact hm1No g⟩
          | none =>
              simp only [hini] at hirc hdwf; let cM := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b }
              let stIr0 : IrState := { env := fun _ => .num 0, heap := h, memos := mIr }; let stJs0 : JsState := { env := fun _ => .num 0, heap := jsSt.heap, memos := jsSt.memos }
              cases hirB : evalIrBody prog c0 revName [] f' stIr0 b with | none => rw [hirB] at hirc; cases hirc | some irR => rcases irR with ⟨irO, irSt1⟩; rw [hirB] at hirc; cases irO with | jumped _ _ => cases hirc | returned rv =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hirc; obtain ⟨rfl, rfl, rfl⟩ := hirc
              rcases ihBody cM [] [] false b stIr0 stJs0 (.returned rv) irSt1 rfl rfl rfl (fun _ h => by simp [cM, hprog.c0_clean.1] at h) hdwf
                (StatesMatch.initCall prog cM c0 false jsSt h mIr #[] [] hhp hmEq hmNo List.nodup_nil (fun _ h => nomatch h) (fun _ _ => rfl)) hirB with ⟨fJsB, jsSt1, hjsB, hvnt, hh1, hm1Eq, hm1No⟩ | ⟨hfalse, _⟩
              · refine ⟨fJsB + 1, { jsSt with heap := jsSt1.heap, memos := fun k => if k == c0.js f then { ok := true, val := some rv } else jsSt1.memos k }, ?_, rfl, hvnt, hh1, rfl, rfl, memoUpdate_eq hprog.rev_ok hm1Eq hf rv, fun g => by dsimp only; split; exact hvnt; exact hm1No g⟩
                rw [evalJsCall, hfnsNone, hjsD]; simp only [lowerDecl, hjsCtx, hemp, ↓reduceIte, hini, evalJsDecl, hmokJs, Bool.false_eq_true]; dsimp only [cM, stJs0] at hjsB; rw [hjsB]
              · exact absurd hfalse Bool.false_ne_true
      · have hempF : xs.isEmpty = false := Bool.eq_false_iff.2 hemp; simp only [hempF, Bool.false_eq_true, ↓reduceIte] at hirc hdwf; rcases hdwf with ⟨hnd, hwfBody⟩
        let stIr0 : IrState := { env := bindIrParams xs args (fun _ => .num 0), heap := h, memos := mIr }; let stJs0 : JsState := { env := bindMany ((xs.toList.map (v ·.x)).zip args) (fun _ => .num 0), heap := jsSt.heap, memos := jsSt.memos }
        cases hirB : evalIrBody prog c0 revName [] f' stIr0 b with | none => rw [hirB] at hirc; cases hirc | some irR => rcases irR with ⟨irO, irSt1⟩; rw [hirB] at hirc; cases irO with | jumped _ _ => cases hirc | returned rv =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hirc; obtain ⟨rfl, rfl, rfl⟩ := hirc
        by_cases hst : hasSelfTail f b = true
        · let dl := !hasJpSelfTail f b
          let cL := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b, selfFn := some f, selfParams := xs, directLoop := dl }
          obtain ⟨hxsPos, _, hcLwf, hjsL⟩ := fdecl_selfTail_setup hprog hpf hempF hst
          rcases ihBody cL [] [] true b stIr0 stJs0 (.returned rv) irSt1 rfl rfl rfl (fun _ hs => by cases hs; exact ⟨hf, hxsPos, hnd⟩) hcLwf
            (fdecl_initCall hprog cL true jsSt h mIr xs args hhp hmEq hmNo hnd hargs) hirB with
            ⟨fJsB, jsSt1, hjsB, hvnt, hh1, hm1Eq, hm1No⟩ | ⟨_, fJsB, jsSt1, sf, na, m0, fIr', hle', hsf, hna', hjsB, hm0, hm0n, hrc⟩
          · exact ⟨fJsB + 1, { jsSt with heap := jsSt1.heap, memos := jsSt1.memos }, (evalJsCall_selfTail dl jsProg c0 f _ (lowerBody cL b) jsSt args fJsB hfnsNone hjsL _ _ (by simpa [stJs0] using hjsB)).1 rv hvnt rfl, rfl, hvnt, hh1, rfl, rfl, hm1Eq, hm1No⟩
          · cases hsf; obtain ⟨fJsRec, st2, hjRec, _, hvnt, hh2, he2, hf2, hm2Eq, hm2No⟩ := ihCall fIr' (Nat.lt_succ_of_le hle') jsSt1.heap m0 f na { jsSt with heap := jsSt1.heap, memos := jsSt1.memos } rv irSt1.heap irSt1.memos hf rfl hm0 hm0n hna' hfns hrc
            refine ⟨max fJsB fJsRec + 1, st2, ?_, rfl, hvnt, hh2, he2, hf2, hm2Eq, hm2No⟩
            rw [(evalJsCall_selfTail dl jsProg c0 f _ (lowerBody cL b) jsSt args fJsB hfnsNone hjsL _ _ (by simpa [stJs0, cL] using hjsB)).2 na rfl (max fJsB fJsRec) (Nat.le_max_left _ _)]
            exact evalJsCall_mono (Nat.le_max_right _ _) hjRec
        · simp only [hst, Bool.false_eq_true, ↓reduceIte] at hwfBody; let cP := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b }
          rcases ihBody cP [] [] false b stIr0 stJs0 (.returned rv) irSt1 rfl rfl rfl (fun _ h => by simp [cP, hprog.c0_clean.1] at h) hwfBody
            (fdecl_initCall hprog cP false jsSt h mIr xs args hhp hmEq hmNo hnd hargs) hirB with ⟨fJsB, jsSt1, hjsB, hvnt, hh1, hm1Eq, hm1No⟩ | ⟨hfalse, _⟩
          · refine ⟨fJsB + 1, { jsSt with heap := jsSt1.heap, memos := jsSt1.memos }, ?_, rfl, hvnt, hh1, rfl, rfl, hm1Eq, hm1No⟩
            rw [evalJsCall, hfnsNone, hjsD]; simp only [lowerDecl, hjsCtx, hempF, Bool.false_eq_true, ↓reduceIte, hst, evalJsDecl]; dsimp only [cP, stJs0] at hjsB; rw [hjsB]
          · exact absurd hfalse Bool.false_ne_true

private theorem eval_sim_ij_app_step (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (hprog : ProgLowered prog c0 jsProg revName) (f' : Nat) (ihCall : CallSimIJ prog c0 jsProg revName (f' + 1)) (ihApp : AppSimIJ prog c0 jsProg revName f') : AppSimIJ prog c0 jsProg revName (f' + 1) := by
  intro h mIr fnVal args jsSt v1 h1 m1 hhp hmEq hmNo hfnNT hargs hfns happ; cases fnVal with
  | pap fnStr arity acc =>
      rcases hfnNT with ⟨hfnNotJp, haccNT⟩; simp only [evalIrApp] at happ; by_cases hlt : args.length < arity - acc.length
      · simp only [hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at happ; obtain ⟨rfl, rfl, rfl⟩ := happ
        exact ⟨1, jsSt, by simp [evalJsApp, hlt], rfl, ⟨hfnNotJp, noTcList_append haccNT (noTcList_of_forall hargs)⟩, hhp, rfl, rfl, hmEq, hmNo⟩
      · simp only [hlt] at happ; cases hrev : revName fnStr with | none => rw [hrev] at happ; cases happ | some fnName =>
        rw [hrev] at happ; obtain ⟨hfnDom, hc0fn⟩ := hprog.rev_none fnStr fnName hrev; have hallNT : ∀ a ∈ acc ++ args, a.noTc := noTcList_mem (noTcList_append haccNT (noTcList_of_forall hargs))
        by_cases heq : args.length == arity - acc.length
        · simp only [heq, ↓reduceIte] at happ; obtain ⟨fJs, st2, hjsc, hpost⟩ := ihCall h mIr fnName (acc ++ args) jsSt v1 h1 m1 hfnDom hhp hmEq hmNo hallNT hfns happ
          obtain ⟨k, rfl⟩ : ∃ k, fJs = k + 1 := by cases fJs with | zero => simp [evalJsCall] at hjsc | succ k => exact ⟨k, rfl⟩
          exact ⟨k + 1, st2, by simp [evalJsApp, hlt, heq, ← hc0fn, hjsc], hpost⟩
        · by_cases hrem : arity - acc.length == 0; simp [heq, hrem] at happ
          simp only [heq, hrem, Bool.false_eq_true, ↓reduceIte] at happ
          cases hirc : evalIrCall prog c0 revName (f' + 1) h mIr fnName (acc ++ args.take (arity - acc.length)) with | none => rw [hirc] at happ; cases happ | some irR =>
          rcases irR with ⟨res, h0, m0⟩; rw [hirc] at happ
          obtain ⟨fJs1, st1, hjsc1, _, hresNT, hh0, hstE, hstF, hm0Eq, hm0No⟩ := ihCall h mIr fnName (acc ++ args.take (arity - acc.length)) jsSt res h0 m0 hfnDom hhp hmEq hmNo (noTcList_mem (noTcList_append haccNT (noTcList_take _ (noTcList_of_forall hargs)))) hfns hirc
          obtain ⟨fJs2, st2, hjsc2, _, hvnt, hh2, he2, hf2, hm2Eq, hm2No⟩ := ihApp h0 m0 res (args.drop (arity - acc.length)) st1 v1 h1 m1 hh0 hm0Eq hm0No hresNT (noTcList_mem (noTcList_drop _ (noTcList_of_forall hargs))) (fun s hs => by rw [hstF] at hs; exact hfns s hs) happ
          exact ⟨max fJs1 fJs2 + 1, st2, by simp [evalJsApp, hlt, heq, hrem, ← hc0fn, evalJsCall_mono (Nat.le_succ_of_le (Nat.le_max_left fJs1 fJs2)) hjsc1, evalJsApp_mono (Nat.le_max_right fJs1 fJs2) hjsc2], rfl, hvnt, hh2, he2.trans hstE, hf2.trans hstF, hm2Eq, hm2No⟩
  | num _ | str _ | bigInt _ | ctorObj _ _ _ _ _ _ | arr _ => simp only [evalIrApp, Option.some.injEq, Prod.mk.injEq] at happ; obtain ⟨rfl, rfl, rfl⟩ := happ; exact ⟨1, jsSt, by simp [evalJsApp], rfl, hfnNT, hhp, rfl, rfl, hmEq, hmNo⟩
  | tc _ => exact False.elim hfnNT

theorem eval_sim_ir_to_js (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (hprog : ProgLowered prog c0 jsProg revName) :
    ∀ fuel : Nat, CallSimIJ prog c0 jsProg revName fuel ∧ AppSimIJ prog c0 jsProg revName fuel ∧ BodySimIJ prog c0 jsProg revName fuel := fun fuel => by
  induction fuel using Nat.strongRecOn with | ind fuel ih =>
  have hCall : CallSimIJ prog c0 jsProg revName fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [evalIrCall] at h | succ f' => exact eval_sim_ij_call_step prog c0 jsProg revName hprog f' (fun k hk => (ih k hk).1) (ih f' (Nat.lt_succ_self f')).2.2
  have hApp : AppSimIJ prog c0 jsProg revName fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [evalIrApp] at h | succ f' => exact eval_sim_ij_app_step prog c0 jsProg revName hprog f' hCall (ih f' (Nat.lt_succ_self f')).2.1
  exact ⟨hCall, hApp, eval_sim_ij_body_step prog c0 jsProg revName hprog fuel hCall hApp (fun f' hf' => (ih f' hf').2.2)⟩

end Js.Proofs
