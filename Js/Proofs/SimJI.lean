import Js.Proofs.Semantics

namespace Js.Proofs
open Lean IR

/-! ## 5b. Backward Simulation (`JS → IR`) -/

section
variable (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (hprog : ProgLowered prog c0 jsProg revName)
include hprog

private theorem eval_sim_ji_body_step (fSub : Nat) (hcallSub : CallSimJI prog c0 jsProg revName fSub) (happSub : AppSimJI prog c0 jsProg revName fSub) (hbodyPrev : ∀ f' < fSub, BodySimJI prog c0 jsProg revName f') : BodySimJI prog c0 jsProg revName fSub := by
  intro c inlineJps recJps allowTailCont b; revert c inlineJps recJps allowTailCont
  refine fnBody_ind (fun b => ∀ c inlineJps recJps allowTailCont irSt jsSt ex jsSt1, CtxWf prog c0 c (BodyWf c prog inlineJps recJps allowTailCont b → StatesMatch prog c c0 inlineJps recJps allowTailCont irSt jsSt → evalJsStmts jsProg fSub jsSt (lowerBody c b) = some (ex, jsSt1) → ExitMatchJI prog c c0 revName inlineJps recJps allowTailCont irSt b ex jsSt1))
    (fun b hb c inlineJps recJps allowTailCont irSt jsSt ex jsSt1 hnames hmin henv hselfNodup hwf hsm hev => ?_) b
  cases b with
  | ret a => rw [evalJsStmts_lower_ret fSub hsm.env_eq a] at hev; cases hev; have hnt := evalIrArg_noTc hsm.env_noTc a; cases heq : evalIrArg irSt.env a with | tc _ => rw [heq] at hnt; simp [JsVal.noTc] at hnt | _ => exact ⟨0, irSt, by dsimp only [evalIrBody, evalIrBodyStep]; rw [heq], by rw [← heq]; exact hnt, hsm.heap_eq, hsm.memos_eq, hsm.memos_noTc⟩
  | unreachable => cases hev
  | set _ _ _ cont | setTag _ _ cont | uset _ _ _ cont | sset _ _ _ _ _ cont | dec _ _ _ _ cont | del _ cont | inc _ _ _ _ cont => have ⟨hwfc, hL⟩ := lockstep_stmt (jsProg := jsProg) (revName := revName) hwf hsm rfl; exact ExitMatchJI.ofLockstep hL (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwfc) hev
  | case tid x xType alts => exact ExitMatchJI.rwBody (evalJsArms_sim_ji x alts.toList hwf (fun arm hm hwfa ha => hb arm hm c inlineJps recJps allowTailCont irSt jsSt ex jsSt1 hnames hmin henv hselfNodup hwfa hsm ha) (caseScrut_eq tid x xType alts hsm.env_eq fSub ▸ hev)) fun _ => rfl
  | jmp j ys =>
      rw [BodyWf] at hwf; rcases hwf with hin | hrec
      · obtain ⟨hnotInM, hjsStep, hok⟩ := inlineJmp_step (jsProg := jsProg) hsm hin; rw [hjsStep fSub] at hev; cases hev; exact ⟨0, j, ys.toList.map (evalIrArg irSt.env), irSt, rfl, evalIrBody_jmp_inline _ 0 j ys hnotInM, hok⟩
      · obtain ⟨hnone, hnotIn⟩ := hsm.recJp_not_inline hrec
        have hjJsNone : jsProg (jp j) = none := by cases hpj : jsProg (jp j) with | none => rfl | some _ => obtain ⟨f', hf'⟩ := hprog.jsProg_dom (jp j) (by rw [hpj]; simp); exact absurd rfl ((hprog.fn_disjoint (jp j) f' hf').1 j)
        cases fSub with | zero => rw [evalJsStmts_lower_recJmp 0 hsm.env_eq ys hnone] at hev; cases hev | succ f' =>
        cases hjir : irSt.jps j.idx with
        | none => rw [evalJsStmts_lower_recJmp (f' + 1) hsm.env_eq ys hnone, evalJsCall_none_of_not_mem f' ((hsm.jps_none j).1 hjir) hjJsNone] at hev; cases hev
        | some jdata =>
        rcases jdata with ⟨xs, val, capIr⟩; obtain ⟨cVal, capJs, hjjs, hcvN, hcvM, hcvE, hcvSF, _, hcvDL, hselfVal, hwfVal, hsmVal⟩ := hsm.enterRecJp hprog.nonArr_param hselfNodup hrec hjir
        rw [evalJsStmts_lower_recJmp_call f' hsm.env_eq ys hnone hjjs] at hev; unret_js hjsV : evalJsStmts jsProg f' _ (lowerBody cVal val) at hev => rval jsStV; obtain ⟨rfl, rfl⟩ := hev
        have hex := hbodyPrev f' (Nat.lt_succ_self f') cVal [] (suffixFrom j.idx recJps) _ val _ _ (.returned rval) jsStV hcvN hcvM hcvE hselfVal hwfVal hsmVal hjsV
        have hstep : ∀ f₂ r irSt', evalIrBody prog c0 revName [] f₂ { env := bindIrParams xs (ys.toList.map (evalIrArg irSt.env)) capIr, heap := irSt.heap, jps := irSt.jps, memos := irSt.memos } val = some (.returned r, irSt') →
            evalIrBody prog c0 revName (inlineJps.map Prod.fst) (f₂ + 1) irSt (.jmp j ys) = some (.returned r, { irSt with heap := irSt'.heap, memos := irSt'.memos }) := fun f₂ r irSt' h => by rw [evalIrBody_jmp_not_inline _ _ j ys hnotIn, hjir]; dsimp only at h ⊢; rw [h]
        cases rval with
        | tc _ => rcases hex with ⟨halV, hcValDL, hnt, sf, m0, hsf, hm0Eq, hm0No, hk⟩; exact ⟨by simpa [hcValDL] using halV, hcvDL ▸ hcValDL, hnt, sf, m0, hcvSF ▸ hsf, hm0Eq, hm0No, fun fIrRec v h' m' hrc => let ⟨fIrV, irStV, hirV, rest⟩ := hk fIrRec v h' m' hrc; ⟨fIrV + 1, _, hstep _ _ _ hirV, rest⟩⟩
        | _ => rcases hex with ⟨fIrV, irStV, hirV, rest⟩; exact ⟨fIrV + 1, _, hstep _ _ _ hirV, rest⟩
  | jdecl j xs val cont =>
      rw [BodyWf] at hwf; rcases hwf with ⟨hnd, hnotIn, hnotRec, hcNone, hrec⟩; by_cases hjmp : (!hasJmpTo j val) = true
      · simp only [hjmp, ↓reduceIte] at hrec; rw [evalJsStmts_lower_inlineJdecl fSub j xs val cont hjmp] at hev
        unopt hjsC : evalJsStmts jsProg fSub jsSt (lowerBody { c with inlineJps := c.inlineJps.insert j.idx xs } cont) at hev => exC jsStC
        have hexC := hb.2 { c with inlineJps := c.inlineJps.insert j.idx xs } ((j.idx, xs.size) :: inlineJps) recJps allowTailCont irSt jsSt exC jsStC hnames hmin henv hselfNodup hrec.1 (hsm.pushInlineJp j xs hnotIn hnotRec) hjsC
        have hretWrap {k} : TailContCont prog { c with inlineJps := c.inlineJps.insert j.idx xs } c0 revName (j.idx :: inlineJps.map Prod.fst) irSt cont jsSt1 k → TailContCont prog c c0 revName (inlineJps.map Prod.fst) irSt (.jdecl j xs val cont) jsSt1 k := fun ⟨hnt, sf, m0, hsf, hm0Eq, hm0No, hfk⟩ =>
          ⟨hnt, sf, m0, hsf, hm0Eq, hm0No, fun fIrRec v h' m' hrc => let ⟨fIrC, irStC, hirC, rest⟩ := hfk fIrRec v h' m' hrc; ⟨fIrC, irStC, by rw [evalIrBody_inlineJdecl _ _ j xs val cont hjmp, hirC], rest⟩⟩
        cases exC with
        | next => exact False.elim hexC
        | tailCont _ => cases hev; exact ⟨hexC.1, hexC.2.1, hretWrap hexC.2.2⟩
        | returned vjs => cases hev; cases vjs with | tc _ => exact ⟨hexC.1, hexC.2.1, hretWrap hexC.2.2⟩ | _ => rcases hexC with ⟨fIrC, irStC, hirC, rest⟩; dsimp only [List.map] at hirC; exact ⟨fIrC, irStC, by rw [evalIrBody_inlineJdecl _ _ j xs val cont hjmp, hirC], rest⟩
        | jumped lbl =>
            rcases hexC with ⟨fIrC, j', args, irStC, rfl, hirC, hin', hslots, hargsNoTc, hsm1⟩; dsimp only [List.map] at hirC; dsimp only at hev; by_cases hj'j : j'.idx = j.idx
            · obtain ⟨hj'eq, hj'beq, hjpBeq, hlen⟩ := inlineJp_hit hj'j hin' hnotIn; rw [if_pos hjpBeq, evalJsStmts_inlineJp_post fSub j j' hj'eq args xs hlen hslots] at hev
              exact ExitMatchJI.rwStep (f₁ := fIrC) (hb.1 c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hrec.2 (hsm1.bindInlineJp hsm.rec_disj hsm.inline_sub xs args hnd hlen hargsNoTc (fun k hk => hprog.nonArr_param c.nonArr xs args irStC.env k hk hsm1.nonArr_ok)) hev)
                (fun _ _ _ hirV => by rw [evalIrBody_inlineJdecl _ _ j xs val cont hjmp, evalIrBody_mono (Nat.le_max_left _ _) hirC]; dsimp only; rw [if_pos hj'beq]; exact evalIrBody_mono (Nat.le_max_right _ _) hirV)
            · obtain ⟨hneJ, hjpNe, hin0⟩ := inlineJp_miss hj'j hin'; rw [if_neg (by rw [hjpNe]; decide)] at hev; cases hev
              exact ⟨fIrC, j', args, irStC, rfl, by rw [evalIrBody_inlineJdecl _ _ j xs val cont hjmp, hirC]; dsimp only; rw [if_neg (by rw [hneJ]; decide)], hin0, hslots, hargsNoTc, hsm1.withCtx rfl rfl rfl rfl rfl hsm.rec_disj hsm.inline_sub⟩
      · have hjmpF : (!hasJmpTo j val) = false := Bool.eq_false_iff.2 hjmp; simp only [hjmpF, Bool.false_eq_true, ↓reduceIte] at hrec
        exact ExitMatchJI.dropRecHead hnotRec (ExitMatchJI.ofLockstep (lockstep_rec_jdecl hnames hmin henv j xs val cont hjmpF hnd hnotRec hcNone hrec.1 hsm) (fun _ _ => hb.2 c inlineJps ((j.idx, xs.size) :: recJps) allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hrec.2) hev)
  | vdecl x ty e cont => cases e with
      | fap f ys =>
          by_cases href : f = `Qed.refMark
          · subst href; have ⟨hwfc, hL⟩ := lockstep_vdecl hprog hnames henv hwf hsm rfl; exact ExitMatchJI.ofLockstep hL (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwfc) hev
          · obtain ⟨hwfc, hrefF, hdom, hlow, hne, htail⟩ := fap_nonRef_setup hprog hnames henv hwf href
            by_cases htc : (c.selfFn == some f && retsVar x cont) = true
            · obtain ⟨hal, htrc, _⟩ := htail htc; rw [evalJsStmts_lower_fap_selfTail fSub hsm.env_eq x ty f ys cont htc] at hev
              cases hdl : c.directLoop <;> (rw [hdl] at hev; simp only [Bool.false_eq_true, ↓reduceIte] at hev; cases hev; refine ⟨hal, hdl, evalIrArgs_noTc hsm.env_noTc ys, f, irSt.memos, eq_of_beq (Bool.and_eq_true_iff.1 htc).1, hsm.memos_eq, hsm.memos_noTc, fun fIrRec v h' m' hrc => ?_⟩; obtain ⟨hvalNT, hm'NT⟩ := hprog.nonArr_typed fIrRec jsSt.heap irSt.memos f _ v h' m' hsm.memos_noTc hrc; exact ⟨fIrRec, _, evalIrBody_fap_tailRc _ _ x ty f ys cont hrefF htrc (Bool.and_eq_true_iff.1 htc).2 hsm.nonArr_ok (fun hm => (hprog.nonArr_call c.nonArr fIrRec jsSt.heap irSt.memos f _ v h' m' x.idx hm).1 hrc) (hsm.heap_eq.symm ▸ hrc), hvalNT, rfl, fun _ _ => rfl, hm'NT⟩)
            · rw [evalJsStmts_lower_fap_call fSub hsm.env_eq x ty f ys cont (Bool.eq_false_iff.2 htc) hlow hne] at hev
              unopt hjsc : evalJsCall jsProg fSub jsSt (c0.js f) (ys.toList.map (evalIrArg irSt.env)) at hev => vjs jsStC
              obtain ⟨fIr1, h', m', hirc, _, hvnt, hhp', hme1, hmfns1, hmeq1, hmno1⟩ := hcallSub irSt.heap irSt.memos f (ys.toList.map (evalIrArg irSt.env)) jsSt vjs jsStC hdom hsm.heap_eq hsm.memos_eq hsm.memos_noTc (evalIrArgs_noTc hsm.env_noTc ys) hsm.fns_only_jp hjsc
              exact ExitMatchJI.rwStep (f₁ := fIr1) (hb c inlineJps recJps allowTailCont _ { jsStC with env := bindEnv jsStC.env (v x) vjs } ex jsSt1 hnames hmin henv hselfNodup hwfc (hsm.updCall x hvnt (fun hm => (hprog.nonArr_call c.nonArr fIr1 irSt.heap irSt.memos f _ vjs h' m' x.idx hm).1 hirc) hhp' hme1 hmfns1 hmeq1 hmno1) hev)
                (fun _ _ _ hir2 => by dsimp only [evalIrBody, evalIrBodyStep]; rw [if_neg (by rw [hrefF]; decide), evalIrCall_mono (Nat.le_max_left _ _) hirc]; exact evalIrBody_mono (Nat.le_max_right _ _) hir2)
      | ap y ys =>
          rw [BodyWf] at hwf; rw [evalJsStmts_lower_ap fSub hsm.env_eq x ty y ys cont] at hev; unopt hjsc : evalJsApp jsProg fSub jsSt (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) at hev => vjs jsStC
          obtain ⟨fIr1, h', m', hirc, _, hvnt, hhp', hme1, hmfns1, hmeq1, hmno1⟩ := happSub irSt.heap irSt.memos (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) jsSt vjs jsStC (hsm.env_noTc y.idx) hsm.heap_eq hsm.memos_eq hsm.memos_noTc (evalIrArgs_noTc hsm.env_noTc ys) hsm.fns_only_jp hjsc
          exact ExitMatchJI.rwStep (f₁ := fIr1) (hb c inlineJps recJps allowTailCont _ { jsStC with env := bindEnv jsStC.env (v x) vjs } ex jsSt1 hnames hmin henv hselfNodup hwf.1 (hsm.updCall x hvnt (fun hm => (hprog.nonArr_call c.nonArr fIr1 irSt.heap irSt.memos default _ vjs h' m' x.idx hm).2 (irSt.env y.idx) hirc) hhp' hme1 hmfns1 hmeq1 hmno1) hev)
            (fun _ _ _ hir2 => by dsimp only [evalIrBody, evalIrBodyStep]; rw [evalIrApp_mono (Nat.le_max_left _ _) hirc]; exact evalIrBody_mono (Nat.le_max_right _ _) hir2)
      | _ => have ⟨hwfc, hL⟩ := lockstep_vdecl hprog hnames henv hwf hsm trivial; exact ExitMatchJI.ofLockstep hL (fun _ _ => hb c inlineJps recJps allowTailCont _ _ ex jsSt1 hnames hmin henv hselfNodup hwfc) hev

private theorem eval_sim_ji_call_step (f' : Nat) (ihCall : CallSimJI prog c0 jsProg revName f') (ihBody : BodySimJI prog c0 jsProg revName f') : CallSimJI prog c0 jsProg revName (f' + 1) := by
  intro h mIr f args jsSt v2 st2 hf hhp hmEq hmNo hargs hfns hjsc
  cases hpf : prog f with | none => exact absurd hpf hf | some d => cases d with
  | extern _ _ _ _ => exact False.elim (hprog.findEnv_ok f _ hpf).2.1
  | fdecl fnm xs ty b info =>
      have hfnm := hprog.fdecl_name f fnm xs ty b info hpf; subst fnm
      have hfnsNone := fdecl_fns_none hprog hpf hfns; have hjsD := hprog.js_at_fdecl f xs ty b info hpf; have hdwf := hprog.decl_wf f xs ty b info hpf; dsimp only at hdwf
      by_cases hemp : xs.isEmpty = true
      · rw [evalJsCall_lower_memo f xs ty b info args f' hfnsNone hjsD hemp] at hjsc; simp only [hemp, ↓reduceIte] at hdwf; have hcOk : (mIr f).ok = (jsSt.memos (c0.js f)).ok := by rw [hmEq f hf]
        by_cases hmok : (jsSt.memos (c0.js f)).ok = true
        · rw [if_pos hmok] at hjsc; cases hjsc; exact ⟨1, h, mIr, by rw [evalIrCall_fdecl_memo 0 hpf hemp, hmEq f hf, if_pos hmok], rfl, hmEq f hf ▸ memoVal_noTc hmNo f, hhp, rfl, rfl, hmEq, hmNo⟩
        · have hmokIr : (mIr f).ok = false := hcOk ▸ Bool.eq_false_iff.2 hmok; rw [if_neg hmok] at hjsc; cases hini : getInitFnNameFor? c0.env f with
          | some initFn =>
              rw [hini] at hjsc; dsimp only at hjsc; simp only [hini] at hdwf; rcases hdwf with ⟨_, _, _, _, hiniDom, _⟩; unopt hjsI : evalJsCall jsProg f' jsSt (c0.js initFn) [] at hjsc => v0 st0; cases hjsc
              obtain ⟨fIrI, h0, m0, hirI, _, hvnt, hh0, _, _, hm0Eq, hm0No⟩ := ihCall h mIr initFn [] jsSt v2 st0 (by rw [hiniDom]; simp) hhp hmEq hmNo (fun _ h => nomatch h) hfns hjsI
              exact ⟨fIrI + 1, h0, fun k => if k == f then { ok := true, val := some v2 } else m0 k, by rw [evalIrCall_fdecl_memo fIrI hpf hemp, if_neg (by rw [hmokIr]; decide), hini]; dsimp only; rw [hirI], rfl, hvnt, hh0, rfl, rfl, memoUpdate_eq hprog.rev_ok hm0Eq hf v2, memoUpdate_noTc hm0No f hvnt⟩
          | none =>
              rw [hini] at hjsc; dsimp only at hjsc; simp only [hini] at hdwf; let cM := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b }
              unret_js hjsB : evalJsStmts jsProg f' { env := fun _ => .num 0, heap := jsSt.heap, memos := jsSt.memos } (lowerBody cM b) at hjsc => rv jsSt1; obtain ⟨rfl, rfl⟩ := hjsc
              obtain ⟨fIrB, irSt1, hirB, hvnt, hh1, hm1Eq, hm1No⟩ := (ihBody cM [] [] false b _ _ (.returned rv) jsSt1 rfl rfl rfl (fun _ h => by simp [cM, hprog.c0_clean.1] at h) hdwf (fdecl_initCall hprog cM false jsSt h mIr #[] [] hhp hmEq hmNo List.nodup_nil fun _ h => nomatch h) hjsB).of_false_ret
              dsimp only [List.map, bindIrParams] at hirB; exact ⟨fIrB + 1, irSt1.heap, fun k => if k == f then { ok := true, val := some rv } else irSt1.memos k, by rw [evalIrCall_fdecl_memo fIrB hpf hemp, if_neg (by rw [hmokIr]; decide), hini]; dsimp only; rw [hirB], rfl, hvnt, hh1, rfl, rfl, memoUpdate_eq hprog.rev_ok hm1Eq hf rv, memoUpdate_noTc hm1No f hvnt⟩
      · have hempF : xs.isEmpty = false := Bool.eq_false_iff.2 hemp; simp only [hempF, Bool.false_eq_true, ↓reduceIte] at hdwf; rcases hdwf with ⟨hnd, hwfBody⟩
        by_cases hst : hasSelfTail f b = true
        · let dl := !hasJpSelfTail f b; let cL := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b, selfFn := some f, selfParams := xs, directLoop := dl }
          obtain ⟨hxsPos, _, hcLwf, hjsL⟩ := fdecl_selfTail_setup hprog hpf hempF hst; obtain ⟨ex, jsSt1, hjsB, hinv⟩ := evalJsCall_selfTail_inv hfnsNone hjsL hjsc
          have hex := ihBody cL [] [] true b _ _ ex jsSt1 rfl rfl rfl (fun _ hs => by cases hs; exact ⟨hf, hxsPos, hnd⟩) hcLwf (fdecl_initCall hprog cL true jsSt h mIr xs args hhp hmEq hmNo hnd hargs) hjsB
          rcases hinv with ⟨na, hexEq, hrcCall⟩ | ⟨rv, hexEq, hntc, rfl, rfl⟩
          · rw [hexEq] at hex; have hk : TailContCont prog cL c0 revName [] { env := bindIrParams xs args (fun _ => .num 0), heap := h, memos := mIr } b jsSt1 na := by cases hdl : !hasJpSelfTail f b <;> (simp only [hdl, Bool.false_eq_true, ↓reduceIte] at hex; exact hex.2.2)
            rcases hk with ⟨hnaNT, sf, m0, hsf, hm0Eq, hm0No, hcont⟩; cases hsf
            obtain ⟨fIrRec, h', m', hrc, _, _, hh2, he2, hf2, hm2Eq, _⟩ := ihCall jsSt1.heap m0 f na { jsSt with heap := jsSt1.heap, memos := jsSt1.memos } v2 st2 hf rfl hm0Eq hm0No hnaNT hfns hrcCall
            obtain ⟨fIrB, irSt1, hirB, hvnt, hh1, hm1Eq, hm1No⟩ := hcont fIrRec v2 h' m' hrc
            exact ⟨fIrB + 1, irSt1.heap, irSt1.memos, by rw [evalIrCall_fdecl_nonempty fIrB hpf hempF, hirB], rfl, hvnt, hh1.trans hh2, he2, hf2, fun g hg => by rw [hm1Eq g hg, hm2Eq g hg], hm1No⟩
          · rw [hexEq] at hex; obtain ⟨fIrB, irSt1, hirB, hvnt, hh1, hm1Eq, hm1No⟩ := hex.of_ret_nonTc fun _ hvEq hdlF => by subst hvEq; exact hntc.elim (fun hdlT => Bool.false_ne_true (hdlF.symm.trans (by simpa [cL, dl] using hdlT))) (fun hne => hne _ rfl)
            exact ⟨fIrB + 1, irSt1.heap, irSt1.memos, by rw [evalIrCall_fdecl_nonempty fIrB hpf hempF, hirB], rfl, hvnt, hh1, rfl, rfl, hm1Eq, hm1No⟩
        · have hstF : hasSelfTail f b = false := Bool.eq_false_iff.2 hst; rw [evalJsCall_lower_plain f xs ty b info args f' hfnsNone hjsD hempF hstF] at hjsc; simp only [hstF, Bool.false_eq_true, ↓reduceIte] at hwfBody
          let cP := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b }
          unret_js hjsB : evalJsStmts jsProg f' { env := bindMany ((xs.toList.map (v ·.x)).zip args) (fun _ => .num 0), heap := jsSt.heap, memos := jsSt.memos } (lowerBody cP b) at hjsc => rv jsSt1; obtain ⟨rfl, rfl⟩ := hjsc
          obtain ⟨fIrB, irSt1, hirB, hvnt, hh1, hm1Eq, hm1No⟩ := (ihBody cP [] [] false b _ _ (.returned rv) jsSt1 rfl rfl rfl (fun _ h => by simp [cP, hprog.c0_clean.1] at h) hwfBody (fdecl_initCall hprog cP false jsSt h mIr xs args hhp hmEq hmNo hnd hargs) hjsB).of_false_ret
          exact ⟨fIrB + 1, irSt1.heap, irSt1.memos, by rw [evalIrCall_fdecl_nonempty fIrB hpf hempF]; dsimp only [List.map] at hirB; rw [hirB], rfl, hvnt, hh1, rfl, rfl, hm1Eq, hm1No⟩

private theorem eval_sim_ji_app_step (f' : Nat) (ihCall : CallSimJI prog c0 jsProg revName (f' + 1)) (ihApp : AppSimJI prog c0 jsProg revName f') : AppSimJI prog c0 jsProg revName (f' + 1) := by
  intro h mIr fnVal args jsSt v2 st2 hfnNT hhp hmEq hmNo hargs hfns happ; rw [evalJsApp_succ] at happ; dsimp only [evalJsAppStep] at happ; cases fnVal with
  | pap fnStr arity acc =>
      rw [JsVal.noTc] at hfnNT; rcases hfnNT with ⟨hfnNotJp, haccNT⟩; dsimp only at happ; by_cases hlt : args.length < arity - acc.length
      · rw [if_pos hlt] at happ; cases happ; exact ⟨1, h, mIr, by rw [evalIrApp_succ]; dsimp only [evalIrAppStep]; rw [if_pos hlt], rfl, by rw [JsVal.noTc]; exact ⟨hfnNotJp, noTc_append haccNT hargs⟩, hhp, rfl, rfl, hmEq, hmNo⟩
      · rw [if_neg hlt] at happ; cases hrev : revName fnStr with
        | none =>
            have hfnsN : jsSt.fns fnStr = none := by cases hsf : jsSt.fns fnStr with | none => rfl | some _ => obtain ⟨j, hj⟩ := hfns _ (by rw [hsf]; simp); exact absurd hj (hfnNotJp j)
            have hjspN : jsProg fnStr = none := by cases hp : jsProg fnStr with | none => rfl | some _ => obtain ⟨f', hf'⟩ := hprog.jsProg_dom fnStr (by rw [hp]; simp); rw [hrev] at hf'; cases hf'
            by_cases heq : args.length == arity - acc.length; · rw [if_pos heq, evalJsCall_none_of_not_mem f' hfnsN hjspN] at happ; cases happ
            rw [if_neg heq] at happ; by_cases hrem : arity - acc.length == 0 <;> (first | rw [if_pos hrem] at happ | rw [if_neg hrem, evalJsCall_none_of_not_mem f' hfnsN hjspN] at happ) <;> cases happ
        | some fnName =>
            obtain ⟨hfnDom, hc0fn⟩ := hprog.rev_none fnStr fnName hrev
            by_cases heq : args.length == arity - acc.length
            · rw [if_pos heq, ← hc0fn] at happ; obtain ⟨fIr, h1, m1, hirc, hpost⟩ := ihCall h mIr fnName (acc ++ args) jsSt v2 st2 hfnDom hhp hmEq hmNo (noTc_append haccNT hargs) hfns happ
              obtain ⟨k, rfl⟩ : ∃ k, fIr = k + 1 := by cases fIr with | zero => cases hirc | succ k => exact ⟨k, rfl⟩
              exact ⟨k + 1, h1, m1, by rw [evalIrApp_succ]; dsimp only [evalIrAppStep]; rw [if_neg hlt, hrev]; dsimp only; rw [if_pos heq]; exact hirc, hpost⟩
            · rw [if_neg heq] at happ; by_cases hrem : arity - acc.length == 0; · rw [if_pos hrem] at happ; cases happ
              rw [if_neg hrem] at happ; unopt hjsc1 : evalJsCall jsProg (f' + 1) jsSt fnStr (acc ++ args.take (arity - acc.length)) at happ => res st1; rw [← hc0fn] at hjsc1
              obtain ⟨fIr1, h0, m0, hirc1, _, hresNT, hh0, hstE, hstF, hm0Eq, hm0No⟩ := ihCall h mIr fnName (acc ++ args.take (arity - acc.length)) jsSt res st1 hfnDom hhp hmEq hmNo (noTc_append haccNT fun a ht => hargs a (List.mem_of_mem_take ht)) hfns hjsc1
              obtain ⟨fIr2, h1, m1, hirc2, _, hvnt, hh1, he1, hf1, hm1Eq, hm1No⟩ := ihApp h0 m0 res (args.drop (arity - acc.length)) st1 v2 st2 hresNT hh0 hm0Eq hm0No (fun a ha => hargs a (List.mem_of_mem_drop ha)) (fun s hs => by rw [hstF] at hs; exact hfns s hs) happ
              obtain ⟨k, hkEq⟩ : ∃ k, max fIr1 (fIr2 + 1) = k + 1 := ⟨max (fIr1 - 1) fIr2, by omega⟩
              exact ⟨max fIr1 (fIr2 + 1), h1, m1, by rw [hkEq, evalIrApp_succ]; dsimp only [evalIrAppStep]; rw [if_neg hlt, hrev]; dsimp only; rw [if_neg heq, if_neg hrem, evalIrCall_mono (hkEq ▸ Nat.le_max_left fIr1 (fIr2 + 1) : fIr1 ≤ k + 1) hirc1]; exact evalIrApp_mono (by have := hkEq ▸ Nat.le_max_right fIr1 (fIr2 + 1); omega : fIr2 ≤ k) hirc2, rfl, hvnt, hh1, he1.trans hstE, hf1.trans hstF, hm1Eq, hm1No⟩
  | tc _ => simp [JsVal.noTc] at hfnNT | _ => cases happ; exact ⟨1, h, mIr, rfl, rfl, hfnNT, hhp, rfl, rfl, hmEq, hmNo⟩

theorem eval_sim_js_to_ir : ∀ fuel : Nat, CallSimJI prog c0 jsProg revName fuel ∧ AppSimJI prog c0 jsProg revName fuel ∧ BodySimJI prog c0 jsProg revName fuel := fun fuel => by
  induction fuel using Nat.strongRecOn with | ind fuel ih =>
  have hCall : CallSimJI prog c0 jsProg revName fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; cases h | succ f' => exact eval_sim_ji_call_step prog c0 jsProg revName hprog f' (ih f' (Nat.lt_succ_self f')).1 (ih f' (Nat.lt_succ_self f')).2.2
  have hApp : AppSimJI prog c0 jsProg revName fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; cases h | succ f' => exact eval_sim_ji_app_step prog c0 jsProg revName hprog f' hCall (ih f' (Nat.lt_succ_self f')).2.1
  exact ⟨hCall, hApp, eval_sim_ji_body_step prog c0 jsProg revName hprog fuel hCall hApp (fun f' hf' => (ih f' hf').2.2)⟩
end
end Js.Proofs
