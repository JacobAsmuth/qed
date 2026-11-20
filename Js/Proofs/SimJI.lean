import Js.Proofs.Semantics

namespace Js.Proofs

open Lean IR

/-! ## 5b. Backward Simulation (`JS → IR`) -/

private theorem eval_sim_ji_body_step (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name)
    (hprog : ProgLowered prog c0 jsProg revName) (fSub : Nat) (hcallSub : CallSimJI prog c0 jsProg revName fSub)
    (happSub : AppSimJI prog c0 jsProg revName fSub) (hbodyPrev : ∀ f' < fSub, BodySimJI prog c0 jsProg revName f') : BodySimJI prog c0 jsProg revName fSub := by
  intro c inlineJps recJps allowTailCont b; revert c inlineJps recJps allowTailCont
  refine fnBody_ind (fun b => ∀ c inlineJps recJps allowTailCont irSt jsSt ex jsSt1, c.names = c0.names → c.min = c0.min → c.env = c0.env →
    (∀ sf, c.selfFn = some sf → prog sf ≠ none ∧ c.selfParams.size > 0 ∧ (c.selfParams.toList.map (·.x.idx)).Nodup) → BodyWf c prog inlineJps recJps allowTailCont b →
    StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt → evalJsStmts jsProg fSub jsSt (lowerBody c b) = some (ex, jsSt1) →
    ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt b ex jsSt1)
    (fun b hb c inlineJps recJps allowTailCont irSt jsSt ex jsSt1 hnames hmin henv hselfNodup hwf hsm hev => ?_) b
  cases b with
  | ret a =>
      simp [lowerBody, evalJsStmts, evalJsStmt, evalJsExprM_lowerArg jsProg fSub jsSt irSt.env hsm.env_eq a] at hev; obtain ⟨rfl, rfl⟩ := hev
      have hnt := evalIrArg_noTc hsm.env_noTc a; cases heq : evalIrArg irSt.env a with | tc _ => rw [heq] at hnt; exact False.elim hnt | _ => exact ⟨0, irSt, by simp [evalIrBody, heq], by rw [← heq]; exact hnt, hsm.heap_eq, hsm.memos_eq, hsm.memos_noTc⟩
  | unreachable => simp [lowerBody, evalJsStmts, evalJsStmt] at hev
  | set x i y cont => rw [BodyWf] at hwf; exact ExitMatchJI.ofLockstep (lockstep_set x i y cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwf) hev
  | setTag x cidx cont => rw [BodyWf] at hwf; exact ExitMatchJI.ofLockstep (lockstep_setTag x cidx cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwf) hev
  | uset x i y cont => rw [BodyWf] at hwf; exact ExitMatchJI.ofLockstep (lockstep_uset x i y cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwf) hev
  | sset x n off y ty cont => rw [BodyWf] at hwf; exact ExitMatchJI.ofLockstep (lockstep_sset x n off y ty cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwf) hev
  | dec x n cf bf cont => rw [BodyWf] at hwf; exact ExitMatchJI.ofLockstep (lockstep_rcDec x n (.dec x n cf bf cont) cont hsm rfl fun _ => by simp only [evalIrBody]) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwf) hev
  | del x cont => rw [BodyWf] at hwf; exact ExitMatchJI.ofLockstep (lockstep_rcDec x 1 (.del x cont) cont hsm rfl fun _ => by simp only [evalIrBody]) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwf) hev
  | inc x n cf bf cont => rw [BodyWf] at hwf; exact ExitMatchJI.ofLockstep (lockstep_inc x n cf bf cont hsm hwf.2) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwf.1) hev
  | case tid x xType alts =>
      rw [BodyWf] at hwf
      rw [caseScrut_eq jsProg c tid x xType alts hsm.env_eq fSub] at hev
      have hres := evalJsArms_sim_ji (x := x) alts.toList hwf (fun arm hm hwfa ha => hb arm hm c inlineJps recJps allowTailCont irSt jsSt ex jsSt1 hnames hmin henv hselfNodup hwfa hsm ha) hev
      exact ExitMatchJI.rwBody hres fun _ => by simp [evalIrBody]
  | jmp j ys =>
      rw [BodyWf] at hwf; rcases hwf with hin | hrec
      · obtain ⟨hnotInM, hjsStep, hok⟩ := inlineJmp_step (jsProg := jsProg) hsm hin
        rw [hjsStep fSub, Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev
        exact ⟨0, j, ys.toList.map (evalIrArg irSt.env), irSt, rfl, evalIrBody_jmp_inline _ _ _ _ 0 _ _ _ hnotInM, hok⟩
      · have hnone : c.inlineJps.get? j.idx = none := hsm.rec_disj (j.idx, ys.size) hrec
        have hnotIn : j.idx ∉ inlineJps.map Prod.fst := fun hm => by rcases List.mem_map.1 hm with ⟨p, hp, hpe⟩; obtain ⟨xs, hxs, _⟩ := hsm.inline_sub p.1 p.2 hp; rw [hpe, hnone] at hxs; contradiction
        have hjJsNone : jsProg (jp j) = none := by cases hpj : jsProg (jp j) with | none => rfl | some _ => obtain ⟨f', hf'⟩ := hprog.jsProg_dom (jp j) (by rw [hpj]; simp); exact absurd rfl ((hprog.fn_disjoint (jp j) f' hf').1 j)
        dsimp only [lowerBody] at hev; rw [show c.inlineJps.get? j.idx = none from hnone] at hev
        simp only [evalJsStmts, evalJsStmt, evalJsExprM_call_jp, evalJsExprListM_lowerArgs jsProg fSub jsSt irSt.env hsm.env_eq ys.toList] at hev
        cases fSub with | zero => simp [evalJsCall] at hev | succ f' =>
        cases hjir : irSt.jps j.idx with | none => simp [evalJsCall, (hsm.jps_none j).1 hjir, hjJsNone] at hev | some jdata =>
        rcases jdata with ⟨xs, val, capIr⟩; obtain ⟨cVal, capJs, hjjs, hcvN, hcvM, hcvE, hcvSF, _, hcvDL, hselfVal, hwfVal, hsmVal⟩ := hsm.enterRecJp hprog.nonArr_param hselfNodup hrec hjir
        simp only [evalJsCall, hjjs] at hev; cases hjsV : evalJsStmts jsProg f' _ (lowerBody cVal val) with | none => rw [hjsV] at hev; cases hev | some jsR =>
        rcases jsR with ⟨exV, jsStV⟩; rw [hjsV] at hev; cases exV with | next | tailCont _ | jumped _ => cases hev | returned rval =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev
        have hex := hbodyPrev f' (Nat.lt_succ_self f') cVal [] (suffixFrom j.idx recJps) _ val _ _ (.returned rval) jsStV hcvN hcvM hcvE hselfVal hwfVal hsmVal hjsV
        have hstep : ∀ f₂ r irSt', evalIrBody prog c0 revName [] f₂ { env := bindIrParams xs (ys.toList.map (evalIrArg irSt.env)) capIr, heap := irSt.heap, jps := irSt.jps, memos := irSt.memos } val = some (.returned r, irSt') →
            evalIrBody prog c0 revName (inlineJps.map Prod.fst) (f₂ + 1) irSt (.jmp j ys) = some (.returned r, { irSt with heap := irSt'.heap, memos := irSt'.memos }) := fun f₂ r irSt' h => by rw [evalIrBody_jmp_not_inline _ _ _ _ _ _ _ _ hnotIn, hjir]; dsimp only at h ⊢; rw [h]
        cases rval with
        | tc _ => rcases hex with ⟨halV, hcValDL, hnt, sf, m0, hsf, hm0Eq, hm0No, hk⟩; exact ⟨by simpa [hcValDL] using halV, hcvDL ▸ hcValDL, hnt, sf, m0, hcvSF ▸ hsf, hm0Eq, hm0No, fun fIrRec v h' m' hrc => let ⟨fIrV, irStV, hirV, rest⟩ := hk fIrRec v h' m' hrc; ⟨fIrV + 1, _, hstep _ _ _ hirV, rest⟩⟩
        | _ => rcases hex with ⟨fIrV, irStV, hirV, rest⟩; exact ⟨fIrV + 1, _, hstep _ _ _ hirV, rest⟩
  | jdecl j xs val cont =>
      rw [BodyWf] at hwf; rcases hwf with ⟨hnd, hnotIn, hnotRec, hcNone, hrec⟩; by_cases hjmp : (!hasJmpTo j val) = true
      · simp only [hjmp, ↓reduceIte] at hrec
        have hdecl : evalJsStmts jsProg fSub jsSt (if xs.isEmpty then [] else [JsStmt.letDecls (xs.toList.zipIdx.map fun (p, i) => s!"_{jp j}_{i}")]) = some (.next, jsSt) := by cases xs.isEmpty <;> simp [evalJsStmts, evalJsStmt]
        simp only [lowerBody, hjmp, ↓reduceIte, List.append_assoc, evalJsStmts_append, hdecl, evalJsStmts, evalJsStmt] at hev
        cases hjsC : evalJsStmts jsProg fSub jsSt (lowerBody { c with inlineJps := c.inlineJps.insert j.idx xs } cont) with | none => rw [hjsC] at hev; cases hev | some jsRC =>
        rcases jsRC with ⟨exC, jsStC⟩; rw [hjsC] at hev
        have hexC := hb.2 { c with inlineJps := c.inlineJps.insert j.idx xs } ((j.idx, xs.size) :: inlineJps) recJps allowTailCont irSt jsSt exC jsStC hnames hmin henv hselfNodup hrec.1 (hsm.pushInlineJp j xs hnotIn hnotRec) hjsC
        have hretWrap : ∀ {k}, TailContCont prog { c with inlineJps := c.inlineJps.insert j.idx xs } c0 revName (j.idx :: inlineJps.map Prod.fst) irSt cont jsSt1 k → TailContCont prog c c0 revName (inlineJps.map Prod.fst) irSt (.jdecl j xs val cont) jsSt1 k := fun hk => by
          rcases hk with ⟨hnt, sf, m0, hsf, hm0Eq, hm0No, hfk⟩
          exact ⟨hnt, sf, m0, hsf, hm0Eq, hm0No, fun fIrRec v h' m' hrc => let ⟨fIrC, irStC, hirC, rest⟩ := hfk fIrRec v h' m' hrc; ⟨fIrC, irStC, by simp only [evalIrBody, hjmp, ↓reduceIte]; rw [hirC], rest⟩⟩
        cases exC with
        | next => exact False.elim hexC
        | tailCont _ => simp only [Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev; exact ⟨hexC.1, hexC.2.1, hretWrap hexC.2.2⟩
        | returned vjs =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev
            cases vjs with
            | tc _ => exact ⟨hexC.1, hexC.2.1, hretWrap hexC.2.2⟩
            | _ => rcases hexC with ⟨fIrC, irStC, hirC, rest⟩; exact ⟨fIrC, irStC, by simp only [evalIrBody, hjmp, ↓reduceIte]; dsimp only [List.map] at hirC; rw [hirC], rest⟩
        | jumped lbl =>
            rcases hexC with ⟨fIrC, j', args, irStC, rfl, hirC, hin', hslots, hargsNoTc, hsm1⟩; dsimp only [List.map] at hirC; by_cases hj'j : j'.idx = j.idx
            · have hj'eq : j' = j := (by cases j'; cases j; cases hj'j; rfl); have hj'beq : (j' == j) = true := by rw [hj'eq]; exact jp_beq_self j
              simp only [show (jp j' == jp j) = true from by rw [hj'eq]; simp, ↓reduceIte] at hev
              have hlen : xs.size = args.length := (List.mem_cons.1 hin').elim (fun h => (Prod.mk.inj h).2.symm) fun h => absurd h (fun h' => hnotIn _ (by rw [← hj'j]; exact h'))
              rw [← evalJsStmts_append, evalJsStmts_inlineJp_post jsProg fSub jsStC j j' hj'eq args xs hlen hslots] at hev
              exact ExitMatchJI.rwStep (f₁ := fIrC) (hb.1 c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hrec.2 (hsm1.bindInlineJp hsm.rec_disj hsm.inline_sub xs args hnd hlen hargsNoTc (fun k hk => hprog.nonArr_param c.nonArr xs args irStC.env k hk hsm1.nonArr_ok)) hev)
                (fun _ _ _ hirV => by simp only [evalIrBody, hjmp, ↓reduceIte]; rw [evalIrBody_mono (Nat.le_max_left _ _) hirC]; simp only [hj'beq, ↓reduceIte]; exact evalIrBody_mono (Nat.le_max_right _ _) hirV)
            · have hjpNe : (jp j' == jp j) = false := beq_false_of_ne fun hje => hj'j (jp_inj hje)
              simp only [hjpNe, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev
              refine ⟨fIrC, j', args, irStC, rfl, ?_, (List.mem_cons.1 hin').elim (fun h => absurd (Prod.mk.inj h).1 hj'j) id, hslots, hargsNoTc, hsm1.withCtx rfl rfl rfl rfl rfl hsm.rec_disj hsm.inline_sub⟩
              have hneJ : (j' == j) = false := by change (j'.idx == j.idx) = false; exact beq_false_of_ne hj'j
              simp only [evalIrBody, hjmp, ↓reduceIte]; rw [hirC]; simp [hneJ]
      · have hjmpF : (!hasJmpTo j val) = false := Bool.eq_false_iff.2 hjmp; simp only [hjmpF, Bool.false_eq_true, ↓reduceIte] at hrec
        exact ExitMatchJI.dropRecHead hnotRec (ExitMatchJI.ofLockstep (lockstep_rec_jdecl hnames hmin henv j xs val cont hjmpF hnd hnotRec hcNone hrec.1 hsm) (fun _ _ => hb.2 c inlineJps ((j.idx, xs.size) :: recJps) allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hrec.2) hev)
  | vdecl x ty e cont =>
      rw [BodyWf] at hwf; rcases hwf with ⟨hwfc, hwe⟩; dsimp only [ExprWf] at hwe; cases e with
      | fap f ys =>
          by_cases href : f = `Qed.refMark
          · subst href; simp only [beq_self_eq_true, ↓reduceIte] at hwe
            exact ExitMatchJI.ofLockstep (lockstep_refMark x ty ys cont hsm hwe) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwfc) hev
          · have hrefF : (f == `Qed.refMark) = false := beq_false_of_ne href; simp only [hrefF, Bool.false_eq_true, ↓reduceIte] at hwe
            rcases hwe with ⟨⟨_, _, _, _, hfd⟩, htail⟩; have hlow := findEnv_fap_args c c0 f ys hnames henv (hprog.findEnv_ok f _ hfd).1 href
            obtain ⟨hne1, hne2, hne3⟩ := (hprog.fn_disjoint (c0.js f) f (hprog.rev_ok f _ hfd)).2
            by_cases htc : (c.selfFn == some f && retsVar x cont) = true
            · obtain ⟨hal, htrc, _⟩ := htail htc; have hsf : c.selfFn = some f := eq_of_beq (Bool.and_eq_true_iff.1 htc).1; have hretV : retsVar x cont = true := (Bool.and_eq_true_iff.1 htc).2
              have hnaNT : ∀ a ∈ ys.toList.map (evalIrArg irSt.env), a.noTc := fun a ha => by rcases List.mem_map.1 ha with ⟨a', _, rfl⟩; exact evalIrArg_noTc hsm.env_noTc a'
              cases hdl : c.directLoop <;> simp [lowerBody, htc, hdl, evalJsStmts, evalJsStmt, evalJsExprM, evalJsExprListM_lowerArgs jsProg fSub jsSt irSt.env hsm.env_eq ys.toList] at hev <;>
                (obtain ⟨rfl, rfl⟩ := hev; refine ⟨hal, hdl, hnaNT, f, irSt.memos, hsf, hsm.memos_eq, hsm.memos_noTc, fun fIrRec v h' m' hrc => ?_⟩
                 obtain ⟨hvalNT, hm'NT⟩ := hprog.nonArr_typed fIrRec jsSt.heap irSt.memos f _ v h' m' hsm.memos_noTc hrc
                 have hna' := bindEnv_nonArr_of_expr c irSt.env x.idx v hsm.nonArr_ok (fun hm => (hprog.nonArr_call c.nonArr fIrRec jsSt.heap irSt.memos f _ v h' m' x.idx hm).1 hrc)
                 have htailEq := evalIrBody_tailRcVarsOk prog c0 c.nonArr revName (inlineJps.map Prod.fst) fIrRec x cont { env := fun k => if k == x.idx then v else irSt.env k, heap := h', jps := irSt.jps, memos := m' } htrc hretV hna'
                 simp only [beq_self_eq_true, ↓reduceIte] at htailEq
                 exact ⟨fIrRec, { env := fun k => if k == x.idx then v else irSt.env k, heap := h', jps := irSt.jps, memos := m' }, by simp only [evalIrBody, hrefF, Bool.false_eq_true, ↓reduceIte, hsm.heap_eq]; rw [hrc]; exact htailEq, hvalNT, rfl, fun _ _ => rfl, hm'NT⟩)
            · simp [lowerBody, lowerExpr, hlow, Bool.eq_false_iff.2 htc, evalJsStmts, evalJsStmt, evalJsExprM, hne1, hne2, hne3, evalJsExprListM_lowerArgs jsProg fSub jsSt irSt.env hsm.env_eq ys.toList] at hev
              cases hjsc : evalJsCall jsProg fSub jsSt (c0.js f) (ys.toList.map (evalIrArg irSt.env)) with | none => rw [hjsc] at hev; cases hev | some jsRes =>
              rcases jsRes with ⟨vjs, jsStC⟩; rw [hjsc] at hev
              obtain ⟨fIr1, h', m', hirc, _, hvnt, hhp', hme1, hmfns1, hmeq1, hmno1⟩ := hcallSub irSt.heap irSt.memos f (ys.toList.map (evalIrArg irSt.env)) jsSt vjs jsStC
                (by rw [hfd]; simp) hsm.heap_eq hsm.memos_eq hsm.memos_noTc (fun a ha => by rcases List.mem_map.1 ha with ⟨a', _, rfl⟩; exact evalIrArg_noTc hsm.env_noTc a') hsm.fns_only_jp hjsc
              exact ExitMatchJI.rwStep (f₁ := fIr1) (hb c inlineJps recJps allowTailCont _ { jsStC with env := bindEnv jsStC.env (v x) vjs } ex jsSt1 hnames hmin henv hselfNodup hwfc
                  (hsm.updCall x hvnt (fun hm => (hprog.nonArr_call c.nonArr fIr1 irSt.heap irSt.memos f _ vjs h' m' x.idx hm).1 hirc) hhp' hme1 hmfns1 hmeq1 hmno1) hev)
                (fun _ _ _ hir2 => by simp only [evalIrBody, hrefF, Bool.false_eq_true, ↓reduceIte]; rw [evalIrCall_mono (Nat.le_max_left _ _) hirc]; exact evalIrBody_mono (Nat.le_max_right _ _) hir2)
      | ap y ys =>
          simp only [lowerBody, lowerExpr, evalJsStmts, evalJsStmt, evalJsExprM, evalJsExprListM_lowerArgs jsProg fSub jsSt irSt.env hsm.env_eq ys.toList] at hev
          rw [← hsm.env_eq y] at hev; cases hjsc : evalJsApp jsProg fSub jsSt (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) with | none => rw [hjsc] at hev; cases hev | some jsRes =>
          rcases jsRes with ⟨vjs, jsStC⟩; rw [hjsc] at hev
          obtain ⟨fIr1, h', m', hirc, _, hvnt, hhp', hme1, hmfns1, hmeq1, hmno1⟩ := happSub irSt.heap irSt.memos (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) jsSt vjs jsStC
            hsm.heap_eq hsm.memos_eq hsm.memos_noTc (hsm.env_noTc y.idx) (fun a ha => by rcases List.mem_map.1 ha with ⟨a', _, rfl⟩; exact evalIrArg_noTc hsm.env_noTc a') hsm.fns_only_jp hjsc
          exact ExitMatchJI.rwStep (f₁ := fIr1) (hb c inlineJps recJps allowTailCont _ { jsStC with env := bindEnv jsStC.env (v x) vjs } ex jsSt1 hnames hmin henv hselfNodup hwfc
              (hsm.updCall x hvnt (fun hm => (hprog.nonArr_call c.nonArr fIr1 irSt.heap irSt.memos default _ vjs h' m' x.idx hm).2 (irSt.env y.idx) hirc) hhp' hme1 hmfns1 hmeq1 hmno1) hev)
            (fun _ _ _ hir2 => by simp only [evalIrBody]; rw [evalIrApp_mono (Nat.le_max_left _ _) hirc]; exact evalIrBody_mono (Nat.le_max_right _ _) hir2)
      | isShared y => exact ExitMatchJI.ofLockstep (lockstep_isShared x ty y cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwfc) hev
      | pap _ _ => exact ExitMatchJI.ofLockstep (lockstep_pure_vdecl hprog hnames henv hsm _ trivial (fun f' ys' he => by injection he with hf _; exact hf ▸ hwe) (fun _ => evalIrPure_ctor_isNonArr c0 ty irSt.env _ trivial)) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwfc) hev
      | ctor _ _ | reuse _ _ _ _ | reset _ _ | lit _ => exact ExitMatchJI.ofLockstep (lockstep_pure_vdecl hprog hnames henv hsm _ trivial (fun _ _ he => nomatch he) (fun _ => evalIrPure_ctor_isNonArr c0 ty irSt.env _ trivial)) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwfc) hev
      | proj _ _ | uproj _ _ | sproj _ _ _ | box _ _ | unbox _ => exact ExitMatchJI.ofLockstep (lockstep_pure_vdecl hprog hnames henv hsm _ trivial (fun _ _ he => nomatch he) (fun hx => hprog.nonArr_pure c.nonArr irSt.env ty x _ hx hsm.nonArr_ok)) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwfc) hev

private theorem eval_sim_ji_call_step (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name)
    (hprog : ProgLowered prog c0 jsProg revName) (f' : Nat) (ihCall : CallSimJI prog c0 jsProg revName f') (ihBody : BodySimJI prog c0 jsProg revName f') :
    CallSimJI prog c0 jsProg revName (f' + 1) := by
  intro h mIr f args jsSt v2 st2 hf hhp hmEq hmNo hargs hfns hjsc
  cases hpf : prog f with | none => exact absurd hpf hf | some d => cases d with
  | extern _ _ _ _ => exact False.elim (hprog.findEnv_ok f _ hpf).2.1
  | fdecl fnm xs ty b info =>
      have hfnm := hprog.fdecl_name f fnm xs ty b info hpf; subst fnm
      have hfnsNone := fdecl_fns_none hprog hpf hfns
      have hjsD := hprog.js_at_fdecl f xs ty b info hpf; have hdwf := hprog.decl_wf f xs ty b info hpf; dsimp only at hdwf
      have hjsCtx : ∀ na ps g, ({ c0 with nonArr := na, projSrc := ps } : Ctx).js g = c0.js g := fun _ _ _ => rfl
      by_cases hemp : xs.isEmpty = true
      · rw [evalJsCall, hfnsNone, hjsD] at hjsc; simp only [hemp, ↓reduceIte, lowerDecl] at hjsc hdwf; have hcOk : (mIr f).ok = (jsSt.memos (c0.js f)).ok := by rw [hmEq f hf]
        by_cases hmok : (jsSt.memos (c0.js f)).ok = true
        · have hnt : ((jsSt.memos (c0.js f)).val.getD (.num 0)).noTc := by have hmv := hmNo f; rw [hmEq f hf] at hmv; cases hv : (jsSt.memos (c0.js f)).val with | none => trivial | some _ => rw [hv] at hmv; exact hmv
          cases hini : getInitFnNameFor? c0.env f <;> simp only [hini, evalJsDecl, hjsCtx, hmok, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hjsc <;>
            (obtain ⟨rfl, rfl⟩ := hjsc; exact ⟨1, h, mIr, by simp [evalIrCall, hpf, hemp, hmok, hmEq f hf], rfl, hnt, hhp, rfl, rfl, hmEq, hmNo⟩)
        · have hmokF : (jsSt.memos (c0.js f)).ok = false := Bool.eq_false_iff.2 hmok; have hmokIr : (mIr f).ok = false := hcOk ▸ hmokF
          cases hini : getInitFnNameFor? c0.env f with
          | some initFn =>
              simp only [hini, evalJsDecl, hjsCtx, hmokF, Bool.false_eq_true, ↓reduceIte] at hjsc hdwf; rcases hdwf with ⟨_, _, _, _, hiniDom, _⟩
              cases hjsI : evalJsCall jsProg f' jsSt (c0.js initFn) [] with | none => rw [hjsI] at hjsc; cases hjsc | some jsR =>
              rcases jsR with ⟨v0, st0⟩; rw [hjsI, Option.some.injEq, Prod.mk.injEq] at hjsc; obtain ⟨rfl, rfl⟩ := hjsc
              obtain ⟨fIrI, h0, m0, hirI, _, hvnt, hh0, _, _, hm0Eq, hm0No⟩ := ihCall h mIr initFn [] jsSt v0 st0 (by rw [hiniDom]; simp) hhp hmEq hmNo (fun _ h => nomatch h) hfns hjsI
              exact ⟨fIrI + 1, h0, fun k => if k == f then { ok := true, val := some v0 } else m0 k, by simp [evalIrCall, hpf, hemp, hmokIr, hini, hirI], rfl, hvnt, hh0, rfl, rfl, memoUpdate_eq hprog.rev_ok hm0Eq hf v0, fun g => by dsimp only; split; exact hvnt; exact hm0No g⟩
          | none =>
              simp only [hini, evalJsDecl, hjsCtx, hmokF, Bool.false_eq_true, ↓reduceIte] at hjsc hdwf
              let cM := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b }; let stIr0 : IrState := { env := fun _ => .num 0, heap := h, memos := mIr }; let stJs0 : JsState := { env := fun _ => .num 0, heap := jsSt.heap, memos := jsSt.memos }
              cases hjsB : evalJsStmts jsProg f' stJs0 (lowerBody cM b) with | none => rw [hjsB] at hjsc; cases hjsc | some jsR => rcases jsR with ⟨ex, jsSt1⟩; rw [hjsB] at hjsc; cases ex with | next | tailCont _ | jumped _ => cases hjsc | returned rv =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hjsc; obtain ⟨rfl, rfl⟩ := hjsc
              have hex := ihBody cM [] [] false b stIr0 stJs0 (.returned rv) jsSt1 rfl rfl rfl (fun _ h => by simp [cM, hprog.c0_clean.1] at h) hdwf
                (StatesMatch.initCall prog cM c0 false jsSt h mIr #[] [] hhp hmEq hmNo List.nodup_nil (fun _ h => nomatch h) (fun _ _ => rfl)) hjsB
              obtain ⟨fIrB, irSt1, hirB, hvnt, hh1, hm1Eq, hm1No⟩ := hex.of_false_ret; dsimp only [stIr0, List.map] at hirB
              exact ⟨fIrB + 1, irSt1.heap, fun k => if k == f then { ok := true, val := some rv } else irSt1.memos k, by simp [evalIrCall, hpf, hemp, hmokIr, hini, hirB], rfl, hvnt, hh1, rfl, rfl, memoUpdate_eq hprog.rev_ok hm1Eq hf rv, fun g => by dsimp only; split; exact hvnt; exact hm1No g⟩
      · have hempF : xs.isEmpty = false := Bool.eq_false_iff.2 hemp; simp only [hempF, Bool.false_eq_true, ↓reduceIte] at hdwf; rcases hdwf with ⟨hnd, hwfBody⟩
        let stIr0 : IrState := { env := bindIrParams xs args (fun _ => .num 0), heap := h, memos := mIr }; let stJs0 : JsState := { env := bindMany ((xs.toList.map (v ·.x)).zip args) (fun _ => .num 0), heap := jsSt.heap, memos := jsSt.memos }
        by_cases hst : hasSelfTail f b = true
        · let dl := !hasJpSelfTail f b
          let cL := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b, selfFn := some f, selfParams := xs, directLoop := dl }
          obtain ⟨hxsPos, _, hcLwf, hjsL⟩ := fdecl_selfTail_setup hprog hpf hempF hst
          obtain ⟨ex, jsSt1, hjsB, hinv⟩ := evalJsCall_selfTail_inv (hdecl := hjsL) (hfns := hfnsNone) (hjsc := hjsc)
          have hex := ihBody cL [] [] true b stIr0 stJs0 ex jsSt1 rfl rfl rfl (fun _ hs => by cases hs; exact ⟨hf, hxsPos, hnd⟩) hcLwf
            (fdecl_initCall hprog cL true jsSt h mIr xs args hhp hmEq hmNo hnd hargs) hjsB
          have hrecCase : ∀ na, evalJsCall jsProg f' { jsSt with heap := jsSt1.heap, memos := jsSt1.memos } (c0.js f) na = some (v2, st2) → TailContCont prog cL c0 revName ([] : List Nat) stIr0 b jsSt1 na →
              ∃ fIr h1 m1, evalIrCall prog c0 revName fIr h mIr f args = some (v2, h1, m1) ∧ CallPost prog c0 v2 v2 h1 m1 jsSt st2 := fun na hrcCall hk => by
            rcases hk with ⟨hnaNT, sf, m0, hsf, hm0Eq, hm0No, hcont⟩; cases hsf
            obtain ⟨fIrRec, h', m', hrc, _, _, hh2, he2, hf2, hm2Eq, _⟩ := ihCall jsSt1.heap m0 f na { jsSt with heap := jsSt1.heap, memos := jsSt1.memos } v2 st2 hf rfl hm0Eq hm0No hnaNT hfns hrcCall
            obtain ⟨fIrB, irSt1, hirB, hvnt, hh1, hm1Eq, hm1No⟩ := hcont fIrRec v2 h' m' hrc; dsimp only [stIr0] at hirB
            exact ⟨fIrB + 1, irSt1.heap, irSt1.memos, by simp [evalIrCall, hpf, hempF, hirB], rfl, hvnt, hh1.trans hh2, he2, hf2, fun g hg => by rw [hm1Eq g hg, hm2Eq g hg], hm1No⟩
          rcases hinv with ⟨na, hexEq, hrcCall⟩ | ⟨rv, hexEq, hntc, rfl, rfl⟩
          · rw [hexEq] at hex; cases hdl : !hasJpSelfTail f b <;> (simp only [hdl, Bool.false_eq_true, ↓reduceIte] at hex; exact hrecCase na hrcCall hex.2.2)
          · rw [hexEq] at hex
            have hexRet := hex.of_ret_nonTc fun _ hvEq hdlF => by
              subst hvEq
              rcases hntc with hdlT | hne
              · exact Bool.false_ne_true (hdlF.symm.trans (by simpa [cL, dl] using hdlT))
              · exact hne _ rfl
            rcases hexRet with ⟨fIrB, irSt1, hirB, hvnt, hh1, hm1Eq, hm1No⟩
            dsimp only [stIr0, List.map] at hirB
            exact ⟨fIrB + 1, irSt1.heap, irSt1.memos, by simp [evalIrCall, hpf, hempF, hirB], rfl, hvnt, hh1, rfl, rfl, hm1Eq, hm1No⟩
        · rw [evalJsCall, hfnsNone, hjsD] at hjsc; simp only [hst, Bool.false_eq_true, ↓reduceIte, lowerDecl, hjsCtx, hempF, evalJsDecl] at hjsc hwfBody
          let cP := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b }
          cases hjsB : evalJsStmts jsProg f' stJs0 (lowerBody cP b) with | none => rw [hjsB] at hjsc; cases hjsc | some jsR =>
          rcases jsR with ⟨ex, jsSt1⟩; rw [hjsB] at hjsc; cases ex with | next | tailCont _ | jumped _ => cases hjsc | returned rv =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hjsc; obtain ⟨rfl, rfl⟩ := hjsc
          have hex := ihBody cP [] [] false b stIr0 stJs0 (.returned rv) jsSt1 rfl rfl rfl (fun _ h => by simp [cP, hprog.c0_clean.1] at h) hwfBody
            (fdecl_initCall hprog cP false jsSt h mIr xs args hhp hmEq hmNo hnd hargs) hjsB
          obtain ⟨fIrB, irSt1, hirB, hvnt, hh1, hm1Eq, hm1No⟩ := hex.of_false_ret; dsimp only [stIr0, List.map] at hirB
          exact ⟨fIrB + 1, irSt1.heap, irSt1.memos, by simp [evalIrCall, hpf, hempF, hirB], rfl, hvnt, hh1, rfl, rfl, hm1Eq, hm1No⟩

private theorem eval_sim_ji_app_step (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (hprog : ProgLowered prog c0 jsProg revName) (f' : Nat)
    (ihCall : CallSimJI prog c0 jsProg revName (f' + 1)) (ihApp : AppSimJI prog c0 jsProg revName f') : AppSimJI prog c0 jsProg revName (f' + 1) := by
  intro h mIr fnVal args jsSt v2 st2 hhp hmEq hmNo hfnNT hargs hfns happ; cases fnVal with
  | pap fnStr arity acc =>
      rcases hfnNT with ⟨hfnNotJp, haccNT⟩; simp only [evalJsApp] at happ; by_cases hlt : args.length < arity - acc.length
      · simp only [hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at happ; obtain ⟨rfl, rfl⟩ := happ
        exact ⟨1, h, mIr, by simp [evalIrApp, hlt], rfl, ⟨hfnNotJp, noTcList_append haccNT (noTcList_of_forall hargs)⟩, hhp, rfl, rfl, hmEq, hmNo⟩
      · simp only [hlt, ↓reduceIte] at happ; cases hrev : revName fnStr with
        | none =>
            have hfnsN : jsSt.fns fnStr = none := by cases hsf : jsSt.fns fnStr with | none => rfl | some _ => obtain ⟨j, hj⟩ := hfns _ (by rw [hsf]; simp); exact absurd hj (hfnNotJp j)
            have hjspN : jsProg fnStr = none := by cases hp : jsProg fnStr with | none => rfl | some _ => obtain ⟨f', hf'⟩ := hprog.jsProg_dom fnStr (by rw [hp]; simp); rw [hrev] at hf'; cases hf'
            by_cases heq : args.length == arity - acc.length; simp [heq, evalJsCall, hfnsN, hjspN] at happ; by_cases hrem : arity - acc.length == 0 <;> simp [heq, hrem, evalJsCall, hfnsN, hjspN] at happ
        | some fnName =>
            obtain ⟨hfnDom, hc0fn⟩ := hprog.rev_none fnStr fnName hrev; have hallNT : ∀ a ∈ acc ++ args, a.noTc := noTcList_mem (noTcList_append haccNT (noTcList_of_forall hargs))
            by_cases heq : args.length == arity - acc.length
            · simp only [heq, ↓reduceIte, ← hc0fn] at happ; obtain ⟨fIr, h1, m1, hirc, hpost⟩ := ihCall h mIr fnName (acc ++ args) jsSt v2 st2 hfnDom hhp hmEq hmNo hallNT hfns happ
              obtain ⟨k, rfl⟩ : ∃ k, fIr = k + 1 := by cases fIr with | zero => simp [evalIrCall] at hirc | succ k => exact ⟨k, rfl⟩
              exact ⟨k + 1, h1, m1, by simp [evalIrApp, hlt, hrev, heq, hirc], hpost⟩
            · by_cases hrem : arity - acc.length == 0; simp [heq, hrem] at happ
              simp only [heq, hrem, Bool.false_eq_true, ↓reduceIte] at happ
              cases hjsc1 : evalJsCall jsProg (f' + 1) jsSt fnStr (acc ++ args.take (arity - acc.length)) with | none => rw [hjsc1] at happ; cases happ | some jsR1 =>
              rcases jsR1 with ⟨res, st1⟩; rw [hjsc1] at happ; rw [← hc0fn] at hjsc1
              obtain ⟨fIr1, h0, m0, hirc1, _, hresNT, hh0, hstE, hstF, hm0Eq, hm0No⟩ := ihCall h mIr fnName (acc ++ args.take (arity - acc.length)) jsSt res st1 hfnDom hhp hmEq hmNo (noTcList_mem (noTcList_append haccNT (noTcList_take _ (noTcList_of_forall hargs)))) hfns hjsc1
              obtain ⟨fIr2, h1, m1, hirc2, _, hvnt, hh1, he1, hf1, hm1Eq, hm1No⟩ := ihApp h0 m0 res (args.drop (arity - acc.length)) st1 v2 st2 hh0 hm0Eq hm0No hresNT (noTcList_mem (noTcList_drop _ (noTcList_of_forall hargs))) (fun s hs => by rw [hstF] at hs; exact hfns s hs) happ
              obtain ⟨k, hkEq⟩ : ∃ k, max fIr1 (fIr2 + 1) = k + 1 := ⟨max (fIr1 - 1) fIr2, by omega⟩
              exact ⟨max fIr1 (fIr2 + 1), h1, m1, by rw [hkEq]; simp [evalIrApp, hlt, hrev, heq, hrem, evalIrCall_mono (hkEq ▸ Nat.le_max_left fIr1 (fIr2 + 1) : fIr1 ≤ k + 1) hirc1, evalIrApp_mono (by have := hkEq ▸ Nat.le_max_right fIr1 (fIr2 + 1); omega : fIr2 ≤ k) hirc2], rfl, hvnt, hh1, he1.trans hstE, hf1.trans hstF, hm1Eq, hm1No⟩
  | num _ | str _ | bigInt _ | ctorObj _ _ _ _ _ _ | arr _ => simp only [evalJsApp, Option.some.injEq, Prod.mk.injEq] at happ; obtain ⟨rfl, rfl⟩ := happ; exact ⟨1, h, mIr, by simp [evalIrApp], rfl, hfnNT, hhp, rfl, rfl, hmEq, hmNo⟩
  | tc _ => exact False.elim hfnNT

theorem eval_sim_js_to_ir (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (hprog : ProgLowered prog c0 jsProg revName) :
    ∀ fuel : Nat, CallSimJI prog c0 jsProg revName fuel ∧ AppSimJI prog c0 jsProg revName fuel ∧ BodySimJI prog c0 jsProg revName fuel := fun fuel => by
  induction fuel using Nat.strongRecOn with | ind fuel ih =>
  have hCall : CallSimJI prog c0 jsProg revName fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [evalJsCall] at h | succ f' => exact eval_sim_ji_call_step prog c0 jsProg revName hprog f' (ih f' (Nat.lt_succ_self f')).1 (ih f' (Nat.lt_succ_self f')).2.2
  have hApp : AppSimJI prog c0 jsProg revName fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [evalJsApp] at h | succ f' => exact eval_sim_ji_app_step prog c0 jsProg revName hprog f' hCall (ih f' (Nat.lt_succ_self f')).2.1
  exact ⟨hCall, hApp, eval_sim_ji_body_step prog c0 jsProg revName hprog fuel hCall hApp (fun f' hf' => (ih f' hf').2.2)⟩

end Js.Proofs
