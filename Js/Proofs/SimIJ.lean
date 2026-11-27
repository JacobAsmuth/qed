import Js.Proofs.Semantics

namespace Js.Proofs
open Lean IR

/-! ## 5a. Forward Simulation (`IR → JS`) -/

section
variable (E : SimEnv) (hprog : ProgLoweredE E)
include hprog

private theorem eval_sim_ij_body_step (fSub : Nat) (hcallSub : CallSimIJ E fSub) (happSub : AppSimIJ E fSub) (hbodyPrev : ∀ f' < fSub, BodySimIJ E f') : BodySimIJ E fSub := by
  intro bc b; revert bc
  refine fnBody_ind (fun b => ∀ (bc : BodyCtx) irSt jsSt irO irSt1, CtxOk E bc.c → E.wf bc b → E.sm bc irSt jsSt → E.irBody bc.inlineIds fSub irSt b = some (irO, irSt1) → E.ij fSub bc jsSt b irO irSt1)
    (fun b hb bc irSt jsSt irO irSt1 hctx hwf hsm hev => ?_) b
  cases b with
  | ret a => cases hev; left; exact ⟨0, jsSt, evalJsStmts_lower_ret (E := E) 0 hsm.env_eq a, evalIrArg_noTc hsm.env_noTc a, hsm.heap_eq, hsm.memos_eq, hsm.memos_noTc⟩
  | unreachable => cases hev
  | set _ _ _ cont | setTag _ _ cont | uset _ _ _ cont | sset _ _ _ _ _ cont | dec _ _ _ _ cont | del _ cont | inc _ _ _ _ cont =>
      have ⟨hwfc, hL⟩ := lockstep_stmt (E := E) hwf hsm rfl; exact ExitMatchIJE.ofLockstep rfl hL (fun _ _ => hb bc _ _ irO irSt1 hctx hwfc) hev
  | case tid x xType alts =>
      exact evalIrAlts_sim_ij tid x xType hsm.env_eq alts.toList hwf (fun arm hm hwfa ha => hb arm hm bc irSt jsSt irO irSt1 hctx hwfa hsm ha) hev
  | jmp j ys =>
      rcases hwf with hin | hrec
      · obtain ⟨hnotInM, hjsStep, hok⟩ := inlineJmp_step (E := E) hsm hin; rw [evalIrBody_jmp_inline (E := E) _ _ j ys hnotInM] at hev; cases hev; exact ⟨0, _, hjsStep 0, hok⟩
      · obtain ⟨hnone, hnotIn⟩ := hsm.recJp_not_inline hrec
        cases fSub with | zero => dsimp only [SimEnv.irBody, evalIrBody, evalIrBodyStep] at hev; rw [ite_eq_right hnotIn] at hev; cases hev | succ f' =>
        rw [evalIrBody_jmp_not_inline (E := E) _ _ j ys hnotIn] at hev
        obtain ⟨⟨xs, val, capIr⟩, hjir, hev⟩ := bind_eq_some hev; obtain ⟨rval, st1, hirV, hev⟩ := optIrRet_eq_some hev; cases hev
        obtain ⟨bcVal, capJs, hjjs, hcvIn, hcvATC, hcvSF, hcvDL, hctxVal, hwfVal, hsmVal⟩ := hsm.enterRecJp hprog.nonArr_param hctx hrec hjir
        rcases hbodyPrev f' (Nat.lt_succ_self f') bcVal val _ _ (.returned rval) st1 hctxVal hwfVal hsmVal (by rw [BodyCtx.inlineIds, hcvIn]; exact hirV) with
          ⟨fJsVal, jsStVal, hjsVal, hok⟩ | ⟨halV, fJsVal, jsStVal, sf, na, m0, fIr', hle', hsf, hna', hjsVal, hm0, hm0n, hrc⟩
        · left; exact ⟨fJsVal + 1, { jsSt with heap := jsStVal.heap, memos := jsStVal.memos }, by rw [evalJsStmts_lower_recJmp_call (E := E) fJsVal hsm.env_eq ys hnone hjjs, hjsVal]; rfl, hok⟩
        · obtain ⟨hbcDL, hbcATC⟩ := directLoop_false_of_recTail (hcvATC ▸ halV); rw [hcvDL, hbcDL] at hjsVal
          right; exact ⟨hbcATC, fJsVal + 1, { jsSt with heap := jsStVal.heap, memos := jsStVal.memos }, sf, na, m0, fIr', Nat.le_succ_of_le hle', hcvSF ▸ hsf, hna', by rw [hbcDL, evalJsStmts_lower_recJmp_call (E := E) fJsVal hsm.env_eq ys hnone hjjs, hjsVal]; rfl, hm0, hm0n, hrc⟩
  | jdecl j xs val cont =>
      rcases hwf with ⟨hnd, hnotIn, hnotRec, hcNone, hrec⟩; by_cases hjmp : (!hasJmpTo j val) = true
      · simp only [hjmp, ↓reduceIte] at hrec; rw [evalIrBody_inlineJdecl (E := E) _ _ j xs val cont hjmp] at hev
        have hlower := fun fJs st => evalJsStmts_lower_inlineJdecl (E := E) (bc := bc) (jsSt := st) fJs j xs val cont hjmp
        obtain ⟨⟨irOC, irStC⟩, hirC, hev⟩ := bind_eq_some hev
        have hexC := hb.2 (bc.pushInline j xs) irSt jsSt irOC irStC ⟨hctx.names, hctx.min, hctx.env, hctx.selfNodup⟩ hrec.1 (hsm.pushInlineJp j xs hnotIn hnotRec) hirC
        cases irOC with
        | returned rv => cases hev; exact hexC.elim (fun ⟨fJs, jsSt1, hjs, hok⟩ => .inl ⟨fJs, jsSt1, by rw [hlower fJs jsSt, hjs]; rfl, hok⟩) fun ⟨hal, fJs, jsSt1, sf, na, m0, fIr', hle, hsf, hna', hjs, hm0, hm0n, hrc⟩ => .inr ⟨hal, fJs, jsSt1, sf, na, m0, fIr', hle, hsf, hna', by rw [hlower fJs jsSt, hjs]; cases bc.c.directLoop <;> rfl, hm0, hm0n, hrc⟩
        | jumped j' args =>
            dsimp only at hev; rcases hexC with ⟨fJsC, jsStC, hjsC, hin', hslots, hargsNoTc, hsm1⟩; by_cases hj'j : j'.idx = j.idx
            · obtain ⟨hj'eq, hj'beq, hjpBeq, hlen⟩ := inlineJp_hit hj'j hin' hnotIn; rw [ite_eq_left hj'beq] at hev
              exact ExitMatchIJE.rwJsMono (f₁ := fJsC) (fun fJs hf => by rw [hlower _ jsSt, evalJsStmts_mono hf hjsC, Option.bind_some]; dsimp only; rw [ite_eq_left hjpBeq, evalJsStmts_inlineJp_post (E := E) fJs j j' hj'eq args xs hlen hslots]) (hb.1 bc _ _ irO irSt1 hctx hrec.2 (hsm.bindInlineJp hsm1 xs args hnd hlen hargsNoTc fun k hk => hprog.nonArr_param bc.c.nonArr xs args _ k hk hsm1.nonArr_ok) hev)
            · obtain ⟨hneJ, hjpNe, hin0⟩ := inlineJp_miss hj'j hin'; rw [ite_eq_right_false hneJ] at hev; cases hev; exact ⟨fJsC, jsStC, by rw [hlower fJsC jsSt, hjsC, Option.bind_some]; simp only [hjpNe, Bool.false_eq_true, ↓reduceIte], hin0, hslots, hargsNoTc, hsm.popInline hsm1⟩
      · have hjmpF : (!hasJmpTo j val) = false := Bool.eq_false_iff.2 hjmp; simp only [hjmpF, Bool.false_eq_true, ↓reduceIte] at hrec
        exact ExitMatchIJE.dropRecHead hnotRec (ExitMatchIJE.ofLockstep rfl (lockstep_rec_jdecl hctx j xs val cont hjmpF hnd hnotRec hcNone hrec.1 hsm) (fun _ _ => hb.2 (bc.pushRec j xs.size) _ _ irO irSt1 hctx hrec.2) hev)
  | vdecl x ty e cont => cases e with
      | fap f ys =>
          by_cases href : f = `Qed.refMark
          · subst href; have ⟨hwfc, hL⟩ := lockstep_vdecl hprog hctx hwf hsm rfl; exact ExitMatchIJE.ofLockstep rfl hL (fun _ _ => hb bc _ _ irO irSt1 hctx hwfc) hev
          · obtain ⟨hwfc, hrefF, hdom, hlow, hne, htail⟩ := fap_nonRef_setup hprog hctx hwf href
            have hev0 := hev; dsimp only [SimEnv.irBody, evalIrBody, evalIrBodyStep] at hev; rw [ite_eq_right_false hrefF] at hev
            obtain ⟨⟨val, h', m'⟩, hirc, hev⟩ := bind_eq_some hev
            by_cases htc : (bc.c.selfFn == some f && retsVar x cont) = true
            · obtain ⟨hal, htrc, _⟩ := htail htc; rw [evalIrBody_fap_tailRc (E := E) _ _ x ty f ys cont hrefF htrc (Bool.and_eq_true_iff.1 htc).2 hsm.nonArr_ok (fun hm => (hprog.nonArr_call bc.c.nonArr fSub irSt.heap irSt.memos f _ val h' m' x.idx hm).1 hirc) hirc] at hev0; cases hev0
              right; exact ⟨hal, 0, _, f, ys.toList.map (evalIrArg irSt.env), irSt.memos, fSub, Nat.le_refl _, eq_of_beq (Bool.and_eq_true_iff.1 htc).1, evalIrArgs_noTc hsm.env_noTc ys, evalJsStmts_lower_fap_selfTail (E := E) 0 hsm.env_eq x ty f ys cont htc, hsm.memos_eq, hsm.memos_noTc, hsm.heap_eq ▸ hirc⟩
            · obtain ⟨fJs1, jsSt1, hjsc, hpost⟩ := hcallSub irSt.heap irSt.memos f (ys.toList.map (evalIrArg irSt.env)) jsSt val h' m' hdom hsm.heap_eq hsm.memos_eq hsm.memos_noTc (evalIrArgs_noTc hsm.env_noTc ys) hsm.fns_only_jp hirc
              exact ExitMatchIJE.rwJsMono (f₁ := fJs1) (fun fJs hf => by rw [evalJsStmts_lower_fap_call (E := E) fJs hsm.env_eq x ty f ys cont (Bool.eq_false_iff.2 htc) hlow hne, evalJsCall_mono hf hjsc]; rfl) (hb bc _ _ irO irSt1 hctx hwfc (hsm.updCallPost x (fun hm => (hprog.nonArr_call bc.c.nonArr fSub irSt.heap irSt.memos f _ val h' m' x.idx hm).1 hirc) hpost) hev)
      | ap y ys =>
          dsimp only [SimEnv.irBody, evalIrBody, evalIrBodyStep] at hev; obtain ⟨⟨val, h', m'⟩, hirc, hev⟩ := bind_eq_some hev
          obtain ⟨fJs1, jsSt1, hjsc, hpost⟩ := happSub irSt.heap irSt.memos (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) jsSt val h' m' (hsm.env_noTc y.idx) hsm.heap_eq hsm.memos_eq hsm.memos_noTc (evalIrArgs_noTc hsm.env_noTc ys) hsm.fns_only_jp hirc
          exact ExitMatchIJE.rwJsMono (f₁ := fJs1) (fun fJs hf => by rw [evalJsStmts_lower_ap (E := E) fJs hsm.env_eq x ty y ys cont, evalJsApp_mono hf hjsc]; rfl) (hb bc _ _ irO irSt1 hctx hwf.1 (hsm.updCallPost x (fun hm => (hprog.nonArr_call bc.c.nonArr fSub irSt.heap irSt.memos default _ val h' m' x.idx hm).2 (irSt.env y.idx) hirc) hpost) hev)
      | _ => have ⟨hwfc, hL⟩ := lockstep_vdecl hprog hctx hwf hsm trivial; exact ExitMatchIJE.ofLockstep rfl hL (fun _ _ => hb bc _ _ irO irSt1 hctx hwfc) hev

private theorem eval_sim_ij_call_step (f' : Nat) (ihCall : ∀ k < f' + 1, CallSimIJ E k) (ihBody : BodySimIJ E f') : CallSimIJ E (f' + 1) := by
  intro h mIr f args jsSt v1 h1 m1 hf hhp hmEq hmNo hargs hfns hirc
  refine fdecl_cases hprog hf hhp hmEq hmNo hargs hfns ?_ ?_ ?_ ?_ ?_
  · intro hIr hJs; rw [hIr] at hirc; cases hirc; exact ⟨1, jsSt, hJs 0, CallPost.refl (memoVal_noTc hmNo f) hhp hmEq hmNo⟩
  · intro ini hDom hIr hJs; rw [hIr] at hirc; obtain ⟨⟨v0, h0, m0⟩, hirI, hirc⟩ := bind_eq_some hirc; cases hirc
    obtain ⟨fJsI, stI, hjsI, _, hvnt, hh1, _, _, hm1Eq, hm1No⟩ := ihCall f' (Nat.lt_succ_self f') h mIr ini [] jsSt v1 h1 m0 hDom hhp hmEq hmNo (fun _ h => nomatch h) hfns hirI
    exact ⟨fJsI + 1, _, by rw [hJs fJsI, hjsI]; rfl, CallPost.memoUpd hprog hf hvnt hh1 hm1Eq hm1No⟩
  · intro b hctx hwf hsm hIr hJs; rw [hIr] at hirc; obtain ⟨rv, irSt1, hirB, hirc⟩ := optIrRet_eq_some hirc; cases hirc
    obtain ⟨fJsB, jsSt1, hjsB, hvnt, hh1, hm1Eq, hm1No⟩ := (ihBody ⟨E.baseCtx b, [], [], false⟩ b _ _ (.returned v1) irSt1 hctx hwf hsm hirB).of_false_ret
    exact ⟨fJsB + 1, _, by rw [hJs fJsB, hjsB]; rfl, CallPost.memoUpd hprog hf hvnt hh1 hm1Eq hm1No⟩
  · intro xs b dl cL hfnsN hjsL hctx hwf hsm hIr; rw [hIr] at hirc; obtain ⟨rv, irSt1, hirB, hirc⟩ := optIrRet_eq_some hirc; cases hirc
    rcases ihBody ⟨cL, [], [], true⟩ b _ _ (.returned v1) irSt1 hctx hwf hsm hirB with
      ⟨fJsB, jsSt1, hjsB, hok⟩ | ⟨_, fJsB, jsSt1, sf, na, m0, fIr', hle', hsf, hna', hjsB, hm0, hm0n, hrc⟩
    · exact ⟨fJsB + 1, _, (evalJsCall_selfTail (E := E) dl f _ _ args fJsB hfnsN hjsL hjsB).1 v1 hok.1 rfl, CallPost.ofRet hok⟩
    · cases hsf; obtain ⟨fJsRec, st2, hjRec, hpost⟩ := ihCall fIr' (Nat.lt_succ_of_le hle') jsSt1.heap m0 f na { jsSt with heap := jsSt1.heap, memos := jsSt1.memos } v1 irSt1.heap irSt1.memos hf rfl hm0 hm0n hna' hfns hrc
      exact ⟨max fJsB fJsRec + 1, st2, by rw [(evalJsCall_selfTail (E := E) dl f _ _ args fJsB hfnsN hjsL hjsB).2 na rfl (max fJsB fJsRec) (Nat.le_max_left _ _)]; exact evalJsCall_mono (Nat.le_max_right _ _) hjRec, hpost⟩
  · intro xs b hctx hwf hsm hIr hJs; rw [hIr] at hirc; obtain ⟨rv, irSt1, hirB, hirc⟩ := optIrRet_eq_some hirc; cases hirc
    obtain ⟨fJsB, jsSt1, hjsB, hok⟩ := (ihBody ⟨E.baseCtx b, [], [], false⟩ b _ _ (.returned v1) irSt1 hctx hwf hsm hirB).of_false_ret
    exact ⟨fJsB + 1, _, by rw [hJs fJsB, hjsB]; rfl, CallPost.ofRet hok⟩

private theorem eval_sim_ij_app_step (f' : Nat) (ihCall : CallSimIJ E (f' + 1)) (ihApp : AppSimIJ E f') : AppSimIJ E (f' + 1) := by
  intro h mIr fnVal args jsSt v1 h1 m1 hfnNT hhp hmEq hmNo hargs hfns happ
  refine app_cases (h := h) (mIr := mIr) hprog hfnNT hargs hfns ?_ ?_ ?_ ?_
  · intro v hv hIr hJs; rw [hIr] at happ; cases happ; exact ⟨1, jsSt, hJs 0, CallPost.refl hv hhp hmEq hmNo⟩
  · intro hIr _; rw [hIr] at happ; cases happ
  · intro fnName args' hDom haNT hIr hJs; rw [hIr] at happ
    obtain ⟨fJs, st2, hjsc, hpost⟩ := ihCall h mIr fnName args' jsSt v1 h1 m1 hDom hhp hmEq hmNo haNT hfns happ
    obtain ⟨k, rfl⟩ : ∃ k, fJs = k + 1 := by cases fJs with | zero => cases hjsc | succ k => exact ⟨k, rfl⟩
    exact ⟨k + 1, st2, by rw [hJs k]; exact hjsc, hpost⟩
  · intro fnName a1 a2 hDom ha1 ha2 hIr hJs; rw [hIr] at happ; obtain ⟨⟨res, h0, m0⟩, hirc, happ⟩ := bind_eq_some happ
    obtain ⟨fJs1, st1, hjsc1, hp1⟩ := ihCall h mIr fnName a1 jsSt res h0 m0 hDom hhp hmEq hmNo ha1 hfns hirc
    obtain ⟨fJs2, st2, hjsc2, hp2⟩ := ihApp h0 m0 res a2 st1 v1 h1 m1 hp1.2.1 hp1.2.2.1 hp1.2.2.2.2.2.1 hp1.2.2.2.2.2.2 ha2 (fun s hs => hfns s (hp1.2.2.2.2.1 ▸ hs)) happ
    exact ⟨max fJs1 fJs2 + 1, st2, by rw [hJs (max fJs1 fJs2), evalJsCall_mono (Nat.le_succ_of_le (Nat.le_max_left fJs1 fJs2)) hjsc1, Option.bind_some]; exact evalJsApp_mono (Nat.le_max_right fJs1 fJs2) hjsc2, hp1.transState hp2⟩

theorem eval_sim_ir_to_js : ∀ fuel : Nat, CallSimIJ E fuel ∧ AppSimIJ E fuel ∧ BodySimIJ E fuel := fun fuel => by
  induction fuel using Nat.strongRecOn with | ind fuel ih =>
  have hCall : CallSimIJ E fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; cases h | succ f' => exact eval_sim_ij_call_step E hprog f' (fun k hk => (ih k hk).1) (ih f' (Nat.lt_succ_self f')).2.2
  have hApp : AppSimIJ E fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; cases h | succ f' => exact eval_sim_ij_app_step E hprog f' hCall (ih f' (Nat.lt_succ_self f')).2.1
  exact ⟨hCall, hApp, eval_sim_ij_body_step E hprog fuel hCall hApp (fun f' hf' => (ih f' hf').2.2)⟩
end
end Js.Proofs
