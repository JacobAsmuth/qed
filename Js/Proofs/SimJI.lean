import Js.Proofs.Semantics

namespace Js.Proofs
open Lean IR

/-! ## 5b. Backward Simulation (`JS → IR`) -/

section
variable (E : SimEnv) (hprog : ProgLoweredE E)
include hprog

private theorem eval_sim_ji_body_step (fSub : Nat) (hcallSub : CallSimJI E fSub) (happSub : AppSimJI E fSub) (hbodyPrev : ∀ f' < fSub, BodySimJI E f') : BodySimJI E fSub := by
  intro bc b; revert bc
  refine fnBody_ind (fun b => ∀ (bc : BodyCtx) irSt jsSt ex jsSt1, CtxOk E bc.c → E.wf bc b → E.sm bc irSt jsSt → evalJsStmts E.jsProg fSub jsSt (lowerBody bc.c b) = some (ex, jsSt1) → E.ji bc irSt b ex jsSt1)
    (fun b hb bc irSt jsSt ex jsSt1 hctx hwf hsm hev => ?_) b
  cases b with
  | ret a => rw [evalJsStmts_lower_ret (E := E) fSub hsm.env_eq a] at hev; cases hev; have hnt := evalIrArg_noTc hsm.env_noTc a; cases heq : evalIrArg irSt.env a with | tc _ => rw [heq] at hnt; exact False.elim (by unfold JsVal.noTc at hnt; exact hnt) | _ => exact ⟨0, irSt, by dsimp only [SimEnv.irBody, evalIrBody, evalIrBodyStep]; rw [heq], by rw [← heq]; exact hnt, hsm.heap_eq, hsm.memos_eq, hsm.memos_noTc⟩
  | unreachable => cases hev
  | set _ _ _ cont | setTag _ _ cont | uset _ _ _ cont | sset _ _ _ _ _ cont | dec _ _ _ _ cont | del _ cont | inc _ _ _ _ cont =>
      have ⟨hwfc, hL⟩ := lockstep_stmt (E := E) hwf hsm rfl; exact ExitMatchJIE.ofLockstep rfl hL (fun _ _ => hb bc _ _ ex jsSt1 hctx hwfc) hev
  | case tid x xType alts =>
      rw [SimEnv.wf, BodyWfE] at hwf; exact ExitMatchJIE.rwBody (evalJsArms_sim_ji x alts.toList hwf (fun arm hm hwfa ha => hb arm hm bc irSt jsSt ex jsSt1 hctx hwfa hsm ha) (caseScrut_eq (E := E) tid x xType alts hsm.env_eq fSub ▸ hev)) fun _ => rfl
  | jmp j ys =>
      rw [SimEnv.wf, BodyWfE] at hwf; rcases hwf with hin | hrec
      · obtain ⟨hnotInM, hjsStep, hok⟩ := inlineJmp_step (E := E) hsm hin; rw [hjsStep fSub] at hev; cases hev; exact ⟨0, j, ys.toList.map (evalIrArg irSt.env), irSt, rfl, evalIrBody_jmp_inline (E := E) _ 0 j ys hnotInM, hok⟩
      · obtain ⟨hnone, hnotIn⟩ := hsm.recJp_not_inline hrec
        cases fSub with | zero => rw [evalJsStmts_lower_recJmp (E := E) 0 hsm.env_eq ys hnone] at hev; cases hev | succ f' =>
        cases hjir : irSt.jps j.idx with
        | none => rw [evalJsStmts_lower_recJmp (E := E) (f' + 1) hsm.env_eq ys hnone, evalJsCall_none_of_not_mem (E := E) f' ((hsm.jps_none j).1 hjir) (jsProg_jp_none hprog j)] at hev; cases hev
        | some jdata =>
        rcases jdata with ⟨xs, val, capIr⟩; obtain ⟨bcVal, capJs, hjjs, hcvIn, hcvATC, hcvSF, hcvDL, hctxVal, hwfVal, hsmVal⟩ := hsm.enterRecJp hprog.nonArr_param hctx hrec hjir
        rw [evalJsStmts_lower_recJmp_call (E := E) f' hsm.env_eq ys hnone hjjs] at hev
        obtain ⟨rval, jsStV, hjsV, hev⟩ := optJsRet_eq_some hev; cases hev
        have hex := hbodyPrev f' (Nat.lt_succ_self f') bcVal val _ _ (.returned rval) jsStV hctxVal hwfVal hsmVal hjsV
        have hstep : ∀ f₂ r irSt', E.irBody bcVal.inlineIds f₂ { env := bindIrParams xs (ys.toList.map (evalIrArg irSt.env)) capIr, heap := irSt.heap, jps := irSt.jps, memos := irSt.memos } val = some (.returned r, irSt') →
            E.irBody bc.inlineIds (f₂ + 1) irSt (.jmp j ys) = some (.returned r, { irSt with heap := irSt'.heap, memos := irSt'.memos }) := fun f₂ r irSt' h => by rw [BodyCtx.inlineIds, hcvIn] at h; dsimp only [List.map] at h; rw [evalIrBody_jmp_not_inline (E := E) _ _ j ys hnotIn, hjir, Option.bind_some]; dsimp only; rw [h]; rfl
        cases rval with
        | tc _ => rcases hex with ⟨halV, _, hnt, sf, m0, hsf, hm0Eq, hm0No, hk⟩; obtain ⟨hbcDL, hbcATC⟩ := directLoop_false_of_recTail (hcvATC ▸ halV)
                  exact ⟨hbcATC, hbcDL, hnt, sf, m0, hcvSF ▸ hsf, hm0Eq, hm0No, fun fIrRec v h' m' hrc => let ⟨fIrV, irStV, hirV, rest⟩ := hk fIrRec v h' m' hrc; ⟨fIrV + 1, _, hstep _ _ _ hirV, rest⟩⟩
        | _ => rcases hex with ⟨fIrV, irStV, hirV, rest⟩; exact ⟨fIrV + 1, _, hstep _ _ _ hirV, rest⟩
  | jdecl j xs val cont =>
      rw [SimEnv.wf, BodyWfE] at hwf; rcases hwf with ⟨hnd, hnotIn, hnotRec, hcNone, hrec⟩; by_cases hjmp : (!hasJmpTo j val) = true
      · simp only [hjmp, ↓reduceIte] at hrec; rw [evalJsStmts_lower_inlineJdecl (E := E) fSub j xs val cont hjmp] at hev
        obtain ⟨⟨exC, jsStC⟩, hjsC, hev⟩ := bind_eq_some hev
        have hexC := hb.2 (bc.pushInline j xs) irSt jsSt exC jsStC ⟨hctx.names, hctx.min, hctx.env, hctx.selfNodup⟩ hrec.1 (hsm.pushInlineJp j xs hnotIn hnotRec) hjsC
        have hretWrap {k} : E.tc (bc.pushInline j xs) irSt cont jsSt1 k → E.tc bc irSt (.jdecl j xs val cont) jsSt1 k := fun ⟨hnt, sf, m0, hsf, hm0Eq, hm0No, hfk⟩ =>
          ⟨hnt, sf, m0, hsf, hm0Eq, hm0No, fun fIrRec v h' m' hrc => let ⟨fIrC, irStC, hirC, rest⟩ := hfk fIrRec v h' m' hrc; ⟨fIrC, irStC, by dsimp only [BodyCtx.inlineIds, List.map] at hirC; change E.irBody _ _ _ _ = _; rw [evalIrBody_inlineJdecl (E := E) _ _ j xs val cont hjmp]; dsimp only [SimEnv.irBody]; rw [hirC]; rfl, rest⟩⟩
        cases exC with
        | next => exact False.elim hexC | tailCont _ => cases hev; exact ⟨hexC.1, hexC.2.1, hretWrap hexC.2.2⟩
        | returned vjs => cases hev; cases vjs with | tc _ => exact ⟨hexC.1, hexC.2.1, hretWrap hexC.2.2⟩ | _ => rcases hexC with ⟨fIrC, irStC, hirC, rest⟩; dsimp only [BodyCtx.inlineIds, List.map] at hirC; exact ⟨fIrC, irStC, by change E.irBody _ _ _ _ = _; rw [evalIrBody_inlineJdecl (E := E) _ _ j xs val cont hjmp]; dsimp only [SimEnv.irBody]; rw [hirC]; rfl, rest⟩
        | jumped lbl =>
            rcases hexC with ⟨fIrC, j', args, irStC, rfl, hirC, hin', hslots, hargsNoTc, hsm1⟩; dsimp only [BodyCtx.inlineIds, List.map] at hirC; dsimp only at hev; by_cases hj'j : j'.idx = j.idx
            · obtain ⟨hj'eq, hj'beq, hjpBeq, hlen⟩ := inlineJp_hit hj'j hin' hnotIn; rw [ite_eq_left hjpBeq, evalJsStmts_inlineJp_post (E := E) fSub j j' hj'eq args xs hlen hslots] at hev
              exact ExitMatchJIE.rwStep (f₁ := fIrC) (hb.1 bc _ _ ex jsSt1 hctx hrec.2 (hsm.bindInlineJp hsm1 xs args hnd hlen hargsNoTc (fun k hk => hprog.nonArr_param bc.c.nonArr xs args irStC.env k hk hsm1.nonArr_ok)) hev)
                (fun _ _ _ hirV => by change E.irBody _ _ _ _ = _; rw [evalIrBody_inlineJdecl (E := E) _ _ j xs val cont hjmp]; dsimp only [SimEnv.irBody]; rw [evalIrBody_mono (Nat.le_max_left _ _) hirC, Option.bind_some]; dsimp only; rw [ite_eq_left hj'beq]; exact evalIrBody_mono (Nat.le_max_right _ _) hirV)
            · obtain ⟨hneJ, hjpNe, hin0⟩ := inlineJp_miss hj'j hin'; rw [ite_eq_right_false hjpNe] at hev; cases hev
              exact ⟨fIrC, j', args, irStC, rfl, by change E.irBody _ _ _ _ = _; rw [evalIrBody_inlineJdecl (E := E) _ _ j xs val cont hjmp]; dsimp only [SimEnv.irBody]; rw [hirC, Option.bind_some]; dsimp only; rw [ite_eq_right_false hneJ], hin0, hslots, hargsNoTc, hsm.popInline hsm1⟩
      · have hjmpF : (!hasJmpTo j val) = false := Bool.eq_false_iff.2 hjmp; simp only [hjmpF, Bool.false_eq_true, ↓reduceIte] at hrec
        exact ExitMatchJIE.dropRecHead hnotRec (ExitMatchJIE.ofLockstep rfl (lockstep_rec_jdecl hctx j xs val cont hjmpF hnd hnotRec hcNone hrec.1 hsm) (fun _ _ => hb.2 (bc.pushRec j xs.size) _ _ ex jsSt1 hctx hrec.2) hev)
  | vdecl x ty e cont => cases e with
      | fap f ys =>
          by_cases href : f = `Qed.refMark
          · subst href; have ⟨hwfc, hL⟩ := lockstep_vdecl hprog hctx hwf hsm rfl; exact ExitMatchJIE.ofLockstep rfl hL (fun _ _ => hb bc _ _ ex jsSt1 hctx hwfc) hev
          · obtain ⟨hwfc, hrefF, hdom, hlow, hne, htail⟩ := fap_nonRef_setup hprog hctx hwf href
            by_cases htc : (bc.c.selfFn == some f && retsVar x cont) = true
            · obtain ⟨hal, htrc, _⟩ := htail htc; rw [evalJsStmts_lower_fap_selfTail (E := E) fSub hsm.env_eq x ty f ys cont htc] at hev
              exact ExitMatchJIE.ofSelfTail hal (Option.some.inj hev) ⟨evalIrArgs_noTc hsm.env_noTc ys, f, irSt.memos, eq_of_beq (Bool.and_eq_true_iff.1 htc).1, hsm.memos_eq, hsm.memos_noTc, fun fIrRec v h' m' hrc =>
                let ⟨hvalNT, hm'NT⟩ := hprog.nonArr_typed fIrRec jsSt.heap irSt.memos f _ v h' m' hsm.memos_noTc hrc
                ⟨fIrRec, _, evalIrBody_fap_tailRc (E := E) _ _ x ty f ys cont hrefF htrc (Bool.and_eq_true_iff.1 htc).2 hsm.nonArr_ok (fun hm => (hprog.nonArr_call bc.c.nonArr fIrRec jsSt.heap irSt.memos f _ v h' m' x.idx hm).1 hrc) (hsm.heap_eq.symm ▸ hrc), hvalNT, rfl, fun _ _ => rfl, hm'NT⟩⟩
            · rw [evalJsStmts_lower_fap_call (E := E) fSub hsm.env_eq x ty f ys cont (Bool.eq_false_iff.2 htc) hlow hne] at hev
              obtain ⟨⟨vjs, jsStC⟩, hjsc, hev⟩ := bind_eq_some hev
              obtain ⟨fIr1, h', m', hirc, hpost⟩ := hcallSub irSt.heap irSt.memos f (ys.toList.map (evalIrArg irSt.env)) jsSt vjs jsStC hdom hsm.heap_eq hsm.memos_eq hsm.memos_noTc (evalIrArgs_noTc hsm.env_noTc ys) hsm.fns_only_jp hjsc
              exact ExitMatchJIE.rwStep (f₁ := fIr1) (hb bc _ _ ex jsSt1 hctx hwfc (hsm.updCallPost x (fun hm => (hprog.nonArr_call bc.c.nonArr fIr1 irSt.heap irSt.memos f _ vjs h' m' x.idx hm).1 hirc) hpost) hev)
                (fun _ _ _ hir2 => by dsimp only [SimEnv.irBody, evalIrBody, evalIrBodyStep]; rw [ite_eq_right_false hrefF, evalIrCall_mono (Nat.le_max_left _ _) hirc, Option.bind_some]; exact evalIrBody_mono (Nat.le_max_right _ _) hir2)
      | ap y ys =>
          rw [SimEnv.wf, BodyWfE] at hwf; rw [evalJsStmts_lower_ap (E := E) fSub hsm.env_eq x ty y ys cont] at hev
          obtain ⟨⟨vjs, jsStC⟩, hjsc, hev⟩ := bind_eq_some hev
          obtain ⟨fIr1, h', m', hirc, hpost⟩ := happSub irSt.heap irSt.memos (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) jsSt vjs jsStC (hsm.env_noTc y.idx) hsm.heap_eq hsm.memos_eq hsm.memos_noTc (evalIrArgs_noTc hsm.env_noTc ys) hsm.fns_only_jp hjsc
          exact ExitMatchJIE.rwStep (f₁ := fIr1) (hb bc _ _ ex jsSt1 hctx hwf.1 (hsm.updCallPost x (fun hm => (hprog.nonArr_call bc.c.nonArr fIr1 irSt.heap irSt.memos default _ vjs h' m' x.idx hm).2 (irSt.env y.idx) hirc) hpost) hev)
            (fun _ _ _ hir2 => by dsimp only [SimEnv.irBody, evalIrBody, evalIrBodyStep]; rw [evalIrApp_mono (Nat.le_max_left _ _) hirc, Option.bind_some]; exact evalIrBody_mono (Nat.le_max_right _ _) hir2)
      | _ => have ⟨hwfc, hL⟩ := lockstep_vdecl hprog hctx hwf hsm trivial; exact ExitMatchJIE.ofLockstep rfl hL (fun _ _ => hb bc _ _ ex jsSt1 hctx hwfc) hev

private theorem eval_sim_ji_call_step (f' : Nat) (ihCall : CallSimJI E f') (ihBody : BodySimJI E f') : CallSimJI E (f' + 1) := by
  intro h mIr f args jsSt v2 st2 hf hhp hmEq hmNo hargs hfns hjsc
  cases hpf : E.prog f with | none => exact absurd hpf hf | some d => cases d with
  | extern _ _ _ _ => exact False.elim (hprog.findEnv_ok f _ hpf).2.1
  | fdecl fnm xs ty b info =>
      have hfnm := hprog.fdecl_name f fnm xs ty b info hpf; subst fnm
      have hfnsNone := fdecl_fns_none hprog hpf hfns; have hjsD := hprog.js_at_fdecl f xs ty b info hpf; have hdwf := hprog.decl_wf f xs ty b info hpf; dsimp only at hdwf
      by_cases hemp : xs.isEmpty = true
      · rw [evalJsCall_lower_memo (E := E) f xs ty b info args f' hfnsNone hjsD hemp] at hjsc; simp only [hemp, ↓reduceIte] at hdwf; have hcOk : (mIr f).ok = (jsSt.memos (E.c0.js f)).ok := by rw [hmEq f hf]
        by_cases hmok : (jsSt.memos (E.c0.js f)).ok = true
        · rw [ite_eq_left hmok] at hjsc; cases hjsc; exact ⟨1, h, mIr, by rw [evalIrCall_fdecl_memo (E := E) 0 hpf hemp, hmEq f hf, ite_eq_left hmok], CallPost.refl (hmEq f hf ▸ memoVal_noTc hmNo f) hhp hmEq hmNo⟩
        · have hmokIr : (mIr f).ok = false := hcOk ▸ Bool.eq_false_iff.2 hmok; rw [ite_eq_right hmok] at hjsc; cases hini : getInitFnNameFor? E.c0.env f with
          | some initFn =>
              rw [hini] at hjsc; simp only [hini] at hdwf; rcases hdwf with ⟨_, _, _, _, hiniDom, _⟩
              obtain ⟨⟨v0, st0⟩, hjsI, hjsc⟩ := bind_eq_some hjsc; cases hjsc
              obtain ⟨fIrI, h0, m0, hirI, _, hvnt, hh0, _, _, hm0Eq, hm0No⟩ := ihCall h mIr initFn [] jsSt v2 st0 (by rw [hiniDom]; simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hhp hmEq hmNo (fun _ h => nomatch h) hfns hjsI
              exact ⟨fIrI + 1, h0, _, by rw [evalIrCall_fdecl_memo (E := E) fIrI hpf hemp, ite_eq_right_false hmokIr, hini]; dsimp only; rw [hirI]; rfl, CallPost.memoUpd hprog hf hvnt hh0 hm0Eq hm0No⟩
          | none =>
              rw [hini] at hjsc; simp only [hini] at hdwf; obtain ⟨rv, jsSt1, hjsB, hjsc⟩ := optJsRet_eq_some hjsc; cases hjsc
              obtain ⟨fIrB, irSt1, hirB, hvnt, hh1, hm1Eq, hm1No⟩ := (ihBody ⟨E.baseCtx b, [], [], false⟩ b _ _ (.returned v2) jsSt1 (base_ctx_ok hprog b) hdwf (fdecl_initCall hprog (E.baseCtx b) false jsSt h mIr #[] [] hhp hmEq hmNo List.nodup_nil fun _ h => nomatch h) hjsB).of_false_ret
              dsimp only [List.map, bindIrParams] at hirB; exact ⟨fIrB + 1, irSt1.heap, _, by rw [evalIrCall_fdecl_memo (E := E) fIrB hpf hemp, ite_eq_right_false hmokIr, hini]; dsimp only; rw [hirB]; rfl, CallPost.memoUpd hprog hf hvnt hh1 hm1Eq hm1No⟩
      · have hempF : xs.isEmpty = false := Bool.eq_false_iff.2 hemp; simp only [hempF, Bool.false_eq_true, ↓reduceIte] at hdwf; rcases hdwf with ⟨hnd, hwfBody⟩
        by_cases hst : hasSelfTail f b = true
        · let dl := !hasJpSelfTail f b; let cL := { E.baseCtx b with selfFn := some f, selfParams := xs, directLoop := dl }
          obtain ⟨hxsPos, _, hcLwf, hjsL⟩ := fdecl_selfTail_setup hprog hpf hempF hst; obtain ⟨ex, jsSt1, hjsB, hinv⟩ := evalJsCall_selfTail_inv hfnsNone hjsL hjsc
          have hex := ihBody ⟨cL, [], [], true⟩ b _ _ ex jsSt1 (selfTail_ctx_ok hf hxsPos hnd) hcLwf (fdecl_initCall hprog cL true jsSt h mIr xs args hhp hmEq hmNo hnd hargs) hjsB
          rcases hinv with ⟨na, hexEq, hrcCall⟩ | ⟨rv, hexEq, hntc, rfl, rfl⟩
          · rcases ExitMatchJIE.tailContOf (hexEq ▸ hex) with ⟨hnaNT, sf, m0, hsf, hm0Eq, hm0No, hcont⟩; cases hsf
            obtain ⟨fIrRec, h', m', hrc, _, _, hh2, he2, hf2, hm2Eq, _⟩ := ihCall jsSt1.heap m0 f na { jsSt with heap := jsSt1.heap, memos := jsSt1.memos } v2 st2 hf rfl hm0Eq hm0No hnaNT hfns hrcCall
            obtain ⟨fIrB, irSt1, hirB, hvnt, hh1, hm1Eq, hm1No⟩ := hcont fIrRec v2 h' m' hrc
            exact ⟨fIrB + 1, irSt1.heap, irSt1.memos, by rw [evalIrCall_fdecl_nonempty (E := E) fIrB hpf hempF]; dsimp only [SimEnv.irBody]; dsimp only [BodyCtx.inlineIds, List.map] at hirB; rw [hirB]; rfl, rfl, hvnt, hh1.trans hh2, he2, hf2, fun g hg => by rw [hm1Eq g hg, hm2Eq g hg], hm1No⟩
          · rw [hexEq] at hex; obtain ⟨fIrB, irSt1, hirB, hok⟩ := hex.of_ret_nonTc fun _ hvEq hdlF => by subst hvEq; exact hntc.elim (fun hdlT => Bool.false_ne_true (hdlF.symm.trans (by simpa only [cL, dl] using hdlT))) (fun hne => hne _ rfl)
            exact ⟨fIrB + 1, irSt1.heap, irSt1.memos, by rw [evalIrCall_fdecl_nonempty (E := E) fIrB hpf hempF, hirB]; rfl, CallPost.ofRet hok⟩
        · have hstF : hasSelfTail f b = false := Bool.eq_false_iff.2 hst; rw [evalJsCall_lower_plain (E := E) f xs ty b info args f' hfnsNone hjsD hempF hstF] at hjsc; simp only [hstF, Bool.false_eq_true, ↓reduceIte] at hwfBody
          obtain ⟨rv, jsSt1, hjsB, hjsc⟩ := optJsRet_eq_some hjsc; cases hjsc
          obtain ⟨fIrB, irSt1, hirB, hok⟩ := (ihBody ⟨E.baseCtx b, [], [], false⟩ b _ _ (.returned v2) jsSt1 (base_ctx_ok hprog b) hwfBody (fdecl_initCall hprog (E.baseCtx b) false jsSt h mIr xs args hhp hmEq hmNo hnd hargs) hjsB).of_false_ret
          exact ⟨fIrB + 1, irSt1.heap, irSt1.memos, by rw [evalIrCall_fdecl_nonempty (E := E) fIrB hpf hempF]; dsimp only [List.map] at hirB; rw [hirB]; rfl, CallPost.ofRet hok⟩

private theorem eval_sim_ji_app_step (f' : Nat) (ihCall : CallSimJI E (f' + 1)) (ihApp : AppSimJI E f') : AppSimJI E (f' + 1) := by
  intro h mIr fnVal args jsSt v2 st2 hfnNT hhp hmEq hmNo hargs hfns happ; have happ0 := happ; rw [evalJsApp_succ] at happ; dsimp only [evalJsAppStep] at happ; cases fnVal with
  | pap fnStr arity acc =>
      unfold JsVal.noTc at hfnNT; rcases hfnNT with ⟨hfnNotJp, haccNT⟩; dsimp only at happ; by_cases hlt : args.length < arity - acc.length
      · rw [ite_eq_left hlt] at happ; cases happ; exact ⟨1, h, mIr, by rw [SimEnv.irApp, evalIrApp_succ]; dsimp only [evalIrAppStep]; rw [ite_eq_left hlt], CallPost.refl (by unfold JsVal.noTc; exact ⟨hfnNotJp, noTc_append haccNT hargs⟩) hhp hmEq hmNo⟩
      · rw [ite_eq_right hlt] at happ; cases hrev : E.revName fnStr with
        | none => exact False.elim (pap_not_found_none hprog f' hfnNotJp hfns hrev hlt happ0)
        | some fnName =>
            obtain ⟨hfnDom, hc0fn⟩ := hprog.rev_none fnStr fnName hrev
            by_cases heq : args.length == arity - acc.length
            · rw [ite_eq_left heq, ← hc0fn] at happ; obtain ⟨fIr, h1, m1, hirc, hpost⟩ := ihCall h mIr fnName (acc ++ args) jsSt v2 st2 hfnDom hhp hmEq hmNo (noTc_append haccNT hargs) hfns happ
              obtain ⟨k, rfl⟩ : ∃ k, fIr = k + 1 := by cases fIr with | zero => cases hirc | succ k => exact ⟨k, rfl⟩
              exact ⟨k + 1, h1, m1, by rw [SimEnv.irApp, evalIrApp_succ]; dsimp only [evalIrAppStep]; rw [ite_eq_right hlt, hrev, Option.bind_some, ite_eq_left heq]; exact hirc, hpost⟩
            · rw [ite_eq_right heq] at happ; by_cases hrem : arity - acc.length == 0; · rw [ite_eq_left hrem] at happ; cases happ
              rw [ite_eq_right hrem] at happ; obtain ⟨⟨res, st1⟩, hjsc1, happ⟩ := bind_eq_some happ; rw [← hc0fn] at hjsc1
              obtain ⟨fIr1, h0, m0, hirc1, hp1⟩ := ihCall h mIr fnName (acc ++ args.take (arity - acc.length)) jsSt res st1 hfnDom hhp hmEq hmNo (noTc_append haccNT fun a ht => hargs a (List.mem_of_mem_take ht)) hfns hjsc1
              obtain ⟨fIr2, h1, m1, hirc2, hp2⟩ := ihApp h0 m0 res (args.drop (arity - acc.length)) st1 v2 st2 hp1.2.1 hp1.2.2.1 hp1.2.2.2.2.2.1 hp1.2.2.2.2.2.2 (fun a ha => hargs a (List.mem_of_mem_drop ha)) (fun s hs => hfns s (hp1.2.2.2.2.1 ▸ hs)) happ
              obtain ⟨k, hkEq⟩ : ∃ k, max fIr1 (fIr2 + 1) = k + 1 := ⟨max (fIr1 - 1) fIr2, by omega⟩
              exact ⟨max fIr1 (fIr2 + 1), h1, m1, by rw [hkEq, SimEnv.irApp, evalIrApp_succ]; dsimp only [evalIrAppStep]; rw [ite_eq_right hlt, hrev, Option.bind_some, ite_eq_right heq, ite_eq_right hrem, evalIrCall_mono (hkEq ▸ Nat.le_max_left fIr1 (fIr2 + 1) : fIr1 ≤ k + 1) hirc1, Option.bind_some]; exact evalIrApp_mono (by have := hkEq ▸ Nat.le_max_right fIr1 (fIr2 + 1); omega : fIr2 ≤ k) hirc2, hp1.transState hp2⟩
  | tc _ => exact False.elim (by unfold JsVal.noTc at hfnNT; exact hfnNT) | _ => cases happ; exact ⟨1, h, mIr, rfl, CallPost.refl hfnNT hhp hmEq hmNo⟩

theorem eval_sim_js_to_ir : ∀ fuel : Nat, CallSimJI E fuel ∧ AppSimJI E fuel ∧ BodySimJI E fuel := fun fuel => by
  induction fuel using Nat.strongRecOn with | ind fuel ih =>
  have hCall : CallSimJI E fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; cases h | succ f' => exact eval_sim_ji_call_step E hprog f' (ih f' (Nat.lt_succ_self f')).1 (ih f' (Nat.lt_succ_self f')).2.2
  have hApp : AppSimJI E fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; cases h | succ f' => exact eval_sim_ji_app_step E hprog f' hCall (ih f' (Nat.lt_succ_self f')).2.1
  exact ⟨hCall, hApp, eval_sim_ji_body_step E hprog fuel hCall hApp (fun f' hf' => (ih f' hf').2.2)⟩
end
end Js.Proofs
