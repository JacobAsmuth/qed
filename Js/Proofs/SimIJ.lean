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
  | ret a => dsimp only [SimEnv.irBody, evalIrBody, evalIrBodyStep] at hev; cases hev; left; exact ⟨0, jsSt, evalJsStmts_lower_ret (E := E) 0 hsm.env_eq a, evalIrArg_noTc hsm.env_noTc a, hsm.heap_eq, hsm.memos_eq, hsm.memos_noTc⟩
  | unreachable => cases hev
  | set _ _ _ cont | setTag _ _ cont | uset _ _ _ cont | sset _ _ _ _ _ cont | dec _ _ _ _ cont | del _ cont | inc _ _ _ _ cont =>
      have ⟨hwfc, hL⟩ := lockstep_stmt (E := E) hwf hsm rfl; exact ExitMatchIJE.ofLockstep rfl hL (fun _ _ => hb bc _ _ irO irSt1 hctx hwfc) hev
  | case tid x xType alts =>
      rw [SimEnv.wf, BodyWfE] at hwf; exact evalIrAlts_sim_ij tid x xType hsm.env_eq alts.toList hwf (fun arm hm hwfa ha => hb arm hm bc irSt jsSt irO irSt1 hctx hwfa hsm ha) hev
  | jmp j ys =>
      rw [SimEnv.wf, BodyWfE] at hwf; rcases hwf with hin | hrec
      · obtain ⟨hnotInM, hjsStep, hok⟩ := inlineJmp_step (E := E) hsm hin; rw [evalIrBody_jmp_inline (E := E) _ _ j ys hnotInM] at hev; cases hev; exact ⟨0, _, hjsStep 0, hok⟩
      · obtain ⟨hnone, hnotIn⟩ := hsm.recJp_not_inline hrec
        cases fSub with | zero => dsimp only [SimEnv.irBody, evalIrBody, evalIrBodyStep] at hev; rw [ite_eq_right hnotIn] at hev; cases hev | succ f' =>
        rw [evalIrBody_jmp_not_inline (E := E) _ _ j ys hnotIn] at hev; unopt3 hjir : irSt.jps j.idx at hev => xs val capIr
        obtain ⟨bcVal, capJs, hjjs, hcvIn, hcvATC, hcvSF, hcvDL, hctxVal, hwfVal, hsmVal⟩ := hsm.enterRecJp hprog.nonArr_param hctx hrec hjir
        unret_ir hirV : E.irBody [] f' _ val at hev => rval st1; obtain ⟨rfl, rfl⟩ := hev
        rcases hbodyPrev f' (Nat.lt_succ_self f') bcVal val _ _ (.returned rval) st1 hctxVal hwfVal hsmVal (by rw [BodyCtx.inlineIds, hcvIn]; exact hirV) with
          ⟨fJsVal, jsStVal, hjsVal, hok⟩ | ⟨halV, fJsVal, jsStVal, sf, na, m0, fIr', hle', hsf, hna', hjsVal, hm0, hm0n, hrc⟩
        · left; exact ⟨fJsVal + 1, { jsSt with heap := jsStVal.heap, memos := jsStVal.memos }, by rw [evalJsStmts_lower_recJmp_call (E := E) fJsVal hsm.env_eq ys hnone hjjs, hjsVal], hok⟩
        · obtain ⟨hbcDL, hbcATC⟩ := directLoop_false_of_recTail (hcvATC ▸ halV); rw [hcvDL, hbcDL] at hjsVal
          right; exact ⟨hbcATC, fJsVal + 1, { jsSt with heap := jsStVal.heap, memos := jsStVal.memos }, sf, na, m0, fIr', Nat.le_succ_of_le hle', hcvSF ▸ hsf, hna', by rw [hbcDL, evalJsStmts_lower_recJmp_call (E := E) fJsVal hsm.env_eq ys hnone hjjs, hjsVal]; rfl, hm0, hm0n, hrc⟩
  | jdecl j xs val cont =>
      rw [SimEnv.wf, BodyWfE] at hwf; rcases hwf with ⟨hnd, hnotIn, hnotRec, hcNone, hrec⟩; by_cases hjmp : (!hasJmpTo j val) = true
      · simp only [hjmp, ↓reduceIte] at hrec; rw [evalIrBody_inlineJdecl (E := E) _ _ j xs val cont hjmp] at hev
        have hlower := fun fJs st => evalJsStmts_lower_inlineJdecl (E := E) (bc := bc) (jsSt := st) fJs j xs val cont hjmp
        unopt hirC : E.irBody (j.idx :: bc.inlineIds) fSub irSt cont at hev => irOC irStC
        have hexC := hb.2 (bc.pushInline j xs) irSt jsSt irOC irStC ⟨hctx.names, hctx.min, hctx.env, hctx.selfNodup⟩ hrec.1 (hsm.pushInlineJp j xs hnotIn hnotRec) hirC
        cases irOC with
        | returned rv => cases hev; exact hexC.elim (fun ⟨fJs, jsSt1, hjs, hok⟩ => .inl ⟨fJs, jsSt1, by rw [hlower fJs jsSt, hjs], hok⟩) fun ⟨hal, fJs, jsSt1, sf, na, m0, fIr', hle, hsf, hna', hjs, hm0, hm0n, hrc⟩ => .inr ⟨hal, fJs, jsSt1, sf, na, m0, fIr', hle, hsf, hna', evalJsStmts_lower_inlineJdecl_tail hjmp hjs, hm0, hm0n, hrc⟩
        | jumped j' args =>
            dsimp only at hev; rcases hexC with ⟨fJsC, jsStC, hjsC, hin', hslots, hargsNoTc, hsm1⟩; by_cases hj'j : j'.idx = j.idx
            · obtain ⟨hj'eq, hj'beq, hjpBeq, hlen⟩ := inlineJp_hit hj'j hin' hnotIn; rw [ite_eq_left hj'beq] at hev
              exact ExitMatchIJE.rwJsMono (f₁ := fJsC) (fun fJs hf => by rw [hlower _ jsSt, evalJsStmts_mono hf hjsC]; dsimp only; rw [ite_eq_left hjpBeq, evalJsStmts_inlineJp_post (E := E) fJs j j' hj'eq args xs hlen hslots]) (hb.1 bc _ _ irO irSt1 hctx hrec.2 (hsm1.bindInlineJp hsm.rec_disj hsm.inline_sub xs args hnd hlen hargsNoTc fun k hk => hprog.nonArr_param bc.c.nonArr xs args _ k hk hsm1.nonArr_ok) hev)
            · obtain ⟨hneJ, hjpNe, hin0⟩ := inlineJp_miss hj'j hin'; rw [ite_eq_right (by rw [hneJ]; decide)] at hev; cases hev; exact ⟨fJsC, jsStC, by rw [hlower fJsC jsSt, hjsC]; simp only [hjpNe, Bool.false_eq_true, ↓reduceIte], hin0, hslots, hargsNoTc, hsm1.withCtx (c' := bc.c) (ij' := bc.inlineJps) rfl rfl rfl rfl rfl hsm.rec_disj hsm.inline_sub⟩
      · have hjmpF : (!hasJmpTo j val) = false := Bool.eq_false_iff.2 hjmp; simp only [hjmpF, Bool.false_eq_true, ↓reduceIte] at hrec
        exact ExitMatchIJE.dropRecHead hnotRec (ExitMatchIJE.ofLockstep rfl (lockstep_rec_jdecl hctx j xs val cont hjmpF hnd hnotRec hcNone hrec.1 hsm) (fun _ _ => hb.2 (bc.pushRec j xs.size) _ _ irO irSt1 hctx hrec.2) hev)
  | vdecl x ty e cont => cases e with
      | fap f ys =>
          by_cases href : f = `Qed.refMark
          · subst href; have ⟨hwfc, hL⟩ := lockstep_vdecl hprog hctx hwf hsm rfl; exact ExitMatchIJE.ofLockstep rfl hL (fun _ _ => hb bc _ _ irO irSt1 hctx hwfc) hev
          · obtain ⟨hwfc, hrefF, hdom, hlow, hne, htail⟩ := fap_nonRef_setup hprog hctx hwf href
            have hev0 := hev; dsimp only [SimEnv.irBody, evalIrBody, evalIrBodyStep] at hev; rw [ite_eq_right (by rw [hrefF]; decide)] at hev
            unopt3 hirc : evalIrCall E.prog E.c0 E.revName fSub irSt.heap irSt.memos f (ys.toList.map (evalIrArg irSt.env)) at hev => val h' m'
            obtain ⟨hvalNT, _⟩ := hprog.nonArr_typed fSub irSt.heap irSt.memos f _ val h' m' hsm.memos_noTc hirc
            by_cases htc : (bc.c.selfFn == some f && retsVar x cont) = true
            · obtain ⟨hal, htrc, _⟩ := htail htc; rw [evalIrBody_fap_tailRc (E := E) _ _ x ty f ys cont hrefF htrc (Bool.and_eq_true_iff.1 htc).2 hsm.nonArr_ok (fun hm => (hprog.nonArr_call bc.c.nonArr fSub irSt.heap irSt.memos f _ val h' m' x.idx hm).1 hirc) hirc] at hev0; cases hev0
              right; exact ⟨hal, 0, _, f, ys.toList.map (evalIrArg irSt.env), irSt.memos, fSub, Nat.le_refl _, eq_of_beq (Bool.and_eq_true_iff.1 htc).1, evalIrArgs_noTc hsm.env_noTc ys, evalJsStmts_lower_fap_selfTail (E := E) 0 hsm.env_eq x ty f ys cont htc, hsm.memos_eq, hsm.memos_noTc, hsm.heap_eq ▸ hirc⟩
            · obtain ⟨fJs1, jsSt1, hjsc, _, _, hhp', hme1, hmfns1, hmeq1, hmno1⟩ := hcallSub irSt.heap irSt.memos f (ys.toList.map (evalIrArg irSt.env)) jsSt val h' m' hdom hsm.heap_eq hsm.memos_eq hsm.memos_noTc (evalIrArgs_noTc hsm.env_noTc ys) hsm.fns_only_jp hirc
              exact ExitMatchIJE.rwJsMono (f₁ := fJs1) (fun fJs hf => by rw [evalJsStmts_lower_fap_call (E := E) fJs hsm.env_eq x ty f ys cont (Bool.eq_false_iff.2 htc) hlow hne, evalJsCall_mono hf hjsc]) (hb bc _ _ irO irSt1 hctx hwfc (hsm.updCall x hvalNT (fun hm => (hprog.nonArr_call bc.c.nonArr fSub irSt.heap irSt.memos f _ val h' m' x.idx hm).1 hirc) hhp' hme1 hmfns1 hmeq1 hmno1) hev)
      | ap y ys =>
          rw [SimEnv.wf, BodyWfE] at hwf; dsimp only [SimEnv.irBody, evalIrBody, evalIrBodyStep] at hev; unopt3 hirc : evalIrApp E.prog E.c0 E.revName fSub irSt.heap irSt.memos (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) at hev => val h' m'
          obtain ⟨fJs1, jsSt1, hjsc, _, hvnt, hhp', hme1, hmfns1, hmeq1, hmno1⟩ := happSub irSt.heap irSt.memos (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) jsSt val h' m' (hsm.env_noTc y.idx) hsm.heap_eq hsm.memos_eq hsm.memos_noTc (evalIrArgs_noTc hsm.env_noTc ys) hsm.fns_only_jp hirc
          exact ExitMatchIJE.rwJsMono (f₁ := fJs1) (fun fJs hf => by rw [evalJsStmts_lower_ap (E := E) fJs hsm.env_eq x ty y ys cont, evalJsApp_mono hf hjsc]) (hb bc _ _ irO irSt1 hctx hwf.1 (hsm.updCall x hvnt (fun hm => (hprog.nonArr_call bc.c.nonArr fSub irSt.heap irSt.memos default _ val h' m' x.idx hm).2 (irSt.env y.idx) hirc) hhp' hme1 hmfns1 hmeq1 hmno1) hev)
      | _ => have ⟨hwfc, hL⟩ := lockstep_vdecl hprog hctx hwf hsm trivial; exact ExitMatchIJE.ofLockstep rfl hL (fun _ _ => hb bc _ _ irO irSt1 hctx hwfc) hev

private theorem eval_sim_ij_call_step (f' : Nat) (ihCall : ∀ k < f' + 1, CallSimIJ E k) (ihBody : BodySimIJ E f') : CallSimIJ E (f' + 1) := by
  intro h mIr f args jsSt v1 h1 m1 hf hhp hmEq hmNo hargs hfns hirc
  cases hpf : E.prog f with | none => exact absurd hpf hf | some d => cases d with
  | extern _ _ _ _ => exact False.elim (hprog.findEnv_ok f _ hpf).2.1
  | fdecl fnm xs ty b info =>
      have hfnm := hprog.fdecl_name f fnm xs ty b info hpf; subst fnm
      have hfnsNone := fdecl_fns_none hprog hpf hfns; have hjsD := hprog.js_at_fdecl f xs ty b info hpf; have hdwf := hprog.decl_wf f xs ty b info hpf; dsimp only at hdwf
      by_cases hemp : xs.isEmpty = true
      · rw [evalIrCall_fdecl_memo (E := E) f' hpf hemp] at hirc; simp only [hemp, ↓reduceIte] at hdwf; have hcOk : (mIr f).ok = (jsSt.memos (E.c0.js f)).ok := by rw [hmEq f hf]
        by_cases hmok : (mIr f).ok = true
        · rw [ite_eq_left hmok] at hirc; cases hirc; exact ⟨1, jsSt, by rw [evalJsCall_lower_memo (E := E) f xs ty b info args 0 hfnsNone hjsD hemp, ← hmEq f hf, ite_eq_left hmok], rfl, memoVal_noTc hmNo f, hhp, rfl, rfl, hmEq, hmNo⟩
        · have hmokJs : (jsSt.memos (E.c0.js f)).ok = false := by rw [← hcOk, Bool.eq_false_iff.2 hmok]
          rw [ite_eq_right hmok] at hirc; cases hini : getInitFnNameFor? E.c0.env f with
          | some initFn =>
              rw [hini] at hirc; dsimp only at hirc; simp only [hini] at hdwf; rcases hdwf with ⟨_, _, _, _, hiniDom, _⟩; unopt3 hirI : E.irCall f' h mIr initFn [] at hirc => v0 h0 m0; cases hirc
              obtain ⟨fJsI, stI, hjsI, _, hvnt, hh1, _, _, hm1Eq, hm1No⟩ := ihCall f' (Nat.lt_succ_self f') h mIr initFn [] jsSt v1 h1 m0 (by rw [hiniDom]; simp only [ne_eq, reduceCtorEq, not_false_eq_true]) hhp hmEq hmNo (fun _ h => nomatch h) hfns hirI
              exact ⟨fJsI + 1, { jsSt with heap := stI.heap, memos := fun k => if k == E.c0.js f then { ok := true, val := some v1 } else stI.memos k }, by rw [evalJsCall_lower_memo (E := E) f xs ty b info args fJsI hfnsNone hjsD hemp, ite_eq_right (by rw [hmokJs]; decide), hini]; dsimp only; rw [hjsI], rfl, hvnt, hh1, rfl, rfl, memoUpdate_eq hprog.rev_ok hm1Eq hf v1, memoUpdate_noTc hm1No f hvnt⟩
          | none =>
              rw [hini] at hirc; dsimp only at hirc; simp only [hini] at hdwf; let cM := { E.c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b }
              unret_ir hirB : E.irBody [] f' { env := fun _ => .num 0, heap := h, memos := mIr } b at hirc => rv irSt1; obtain ⟨rfl, rfl, rfl⟩ := hirc
              obtain ⟨fJsB, jsSt1, hjsB, hvnt, hh1, hm1Eq, hm1No⟩ := (ihBody ⟨cM, [], [], false⟩ b _ _ (.returned rv) irSt1 ⟨rfl, rfl, rfl, fun _ h => by simp only [cM, hprog.c0_clean.1, reduceCtorEq] at h⟩ hdwf (fdecl_initCall hprog cM false jsSt h mIr #[] [] hhp hmEq hmNo List.nodup_nil fun _ h => nomatch h) hirB).of_false_ret
              exact ⟨fJsB + 1, { jsSt with heap := jsSt1.heap, memos := fun k => if k == E.c0.js f then { ok := true, val := some rv } else jsSt1.memos k }, by rw [evalJsCall_lower_memo (E := E) f xs ty b info args fJsB hfnsNone hjsD hemp, ite_eq_right (by rw [hmokJs]; decide), hini]; dsimp only [cM, bindMany, List.map, List.zip, List.zipWith] at hjsB ⊢; rw [hjsB], rfl, hvnt, hh1, rfl, rfl, memoUpdate_eq hprog.rev_ok hm1Eq hf rv, memoUpdate_noTc hm1No f hvnt⟩
      · have hempF : xs.isEmpty = false := Bool.eq_false_iff.2 hemp; rw [evalIrCall_fdecl_nonempty (E := E) f' hpf hempF] at hirc; simp only [hempF, Bool.false_eq_true, ↓reduceIte] at hdwf; rcases hdwf with ⟨hnd, hwfBody⟩
        unret_ir hirB : E.irBody [] f' { env := bindIrParams xs args (fun _ => .num 0), heap := h, memos := mIr } b at hirc => rv irSt1; obtain ⟨rfl, rfl, rfl⟩ := hirc
        by_cases hst : hasSelfTail f b = true
        · let dl := !hasJpSelfTail f b; let cL := { E.c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b, selfFn := some f, selfParams := xs, directLoop := dl }
          obtain ⟨hxsPos, _, hcLwf, hjsL⟩ := fdecl_selfTail_setup hprog hpf hempF hst
          rcases ihBody ⟨cL, [], [], true⟩ b _ _ (.returned rv) irSt1 ⟨rfl, rfl, rfl, fun _ hs => by cases hs; exact ⟨hf, hxsPos, hnd⟩⟩ hcLwf (fdecl_initCall hprog cL true jsSt h mIr xs args hhp hmEq hmNo hnd hargs) hirB with
            ⟨fJsB, jsSt1, hjsB, hvnt, hh1, hm1Eq, hm1No⟩ | ⟨_, fJsB, jsSt1, sf, na, m0, fIr', hle', hsf, hna', hjsB, hm0, hm0n, hrc⟩
          · exact ⟨fJsB + 1, { jsSt with heap := jsSt1.heap, memos := jsSt1.memos }, (evalJsCall_selfTail (E := E) dl f _ (lowerBody cL b) args fJsB hfnsNone hjsL hjsB).1 rv hvnt rfl, rfl, hvnt, hh1, rfl, rfl, hm1Eq, hm1No⟩
          · cases hsf; obtain ⟨fJsRec, st2, hjRec, _, hvnt, hh2, he2, hf2, hm2Eq, hm2No⟩ := ihCall fIr' (Nat.lt_succ_of_le hle') jsSt1.heap m0 f na { jsSt with heap := jsSt1.heap, memos := jsSt1.memos } rv irSt1.heap irSt1.memos hf rfl hm0 hm0n hna' hfns hrc
            exact ⟨max fJsB fJsRec + 1, st2, by rw [(evalJsCall_selfTail (E := E) dl f _ (lowerBody cL b) args fJsB hfnsNone hjsL hjsB).2 na rfl (max fJsB fJsRec) (Nat.le_max_left _ _)]; exact evalJsCall_mono (Nat.le_max_right _ _) hjRec, rfl, hvnt, hh2, he2, hf2, hm2Eq, hm2No⟩
        · have hstF : hasSelfTail f b = false := Bool.eq_false_iff.2 hst; simp only [hstF, Bool.false_eq_true, ↓reduceIte] at hwfBody; let cP := { E.c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b }
          obtain ⟨fJsB, jsSt1, hjsB, hvnt, hh1, hm1Eq, hm1No⟩ := (ihBody ⟨cP, [], [], false⟩ b _ _ (.returned rv) irSt1 ⟨rfl, rfl, rfl, fun _ h => by simp only [cP, hprog.c0_clean.1, reduceCtorEq] at h⟩ hwfBody (fdecl_initCall hprog cP false jsSt h mIr xs args hhp hmEq hmNo hnd hargs) hirB).of_false_ret
          exact ⟨fJsB + 1, { jsSt with heap := jsSt1.heap, memos := jsSt1.memos }, by rw [evalJsCall_lower_plain (E := E) f xs ty b info args fJsB hfnsNone hjsD hempF hstF]; dsimp only [cP] at hjsB; rw [hjsB], rfl, hvnt, hh1, rfl, rfl, hm1Eq, hm1No⟩

private theorem eval_sim_ij_app_step (f' : Nat) (ihCall : CallSimIJ E (f' + 1)) (ihApp : AppSimIJ E f') : AppSimIJ E (f' + 1) := by
  intro h mIr fnVal args jsSt v1 h1 m1 hfnNT hhp hmEq hmNo hargs hfns happ; rw [SimEnv.irApp, evalIrApp_succ] at happ; dsimp only [evalIrAppStep] at happ; cases fnVal with
  | pap fnStr arity acc =>
      unfold JsVal.noTc at hfnNT; rcases hfnNT with ⟨hfnNotJp, haccNT⟩; dsimp only at happ; by_cases hlt : args.length < arity - acc.length
      · rw [ite_eq_left hlt] at happ; cases happ; exact ⟨1, jsSt, by rw [evalJsApp_succ]; dsimp only [evalJsAppStep]; rw [ite_eq_left hlt], rfl, by unfold JsVal.noTc; exact ⟨hfnNotJp, noTc_append haccNT hargs⟩, hhp, rfl, rfl, hmEq, hmNo⟩
      · rw [ite_eq_right hlt] at happ; cases hrev : E.revName fnStr with | none => rw [hrev] at happ; cases happ | some fnName =>
        rw [hrev] at happ; dsimp only at happ; obtain ⟨hfnDom, hc0fn⟩ := hprog.rev_none fnStr fnName hrev
        by_cases heq : args.length == arity - acc.length
        · rw [ite_eq_left heq] at happ; obtain ⟨fJs, st2, hjsc, hpost⟩ := ihCall h mIr fnName (acc ++ args) jsSt v1 h1 m1 hfnDom hhp hmEq hmNo (noTc_append haccNT hargs) hfns happ
          obtain ⟨k, rfl⟩ : ∃ k, fJs = k + 1 := by cases fJs with | zero => cases hjsc | succ k => exact ⟨k, rfl⟩
          exact ⟨k + 1, st2, by rw [evalJsApp_succ]; dsimp only [evalJsAppStep]; rw [ite_eq_right hlt, ite_eq_left heq, ← hc0fn]; exact hjsc, hpost⟩
        · rw [ite_eq_right heq] at happ; by_cases hrem : arity - acc.length == 0; · rw [ite_eq_left hrem] at happ; cases happ
          rw [ite_eq_right hrem] at happ; unopt3 hirc : evalIrCall E.prog E.c0 E.revName (f' + 1) h mIr fnName (acc ++ args.take (arity - acc.length)) at happ => res h0 m0
          obtain ⟨fJs1, st1, hjsc1, _, hresNT, hh0, hstE, hstF, hm0Eq, hm0No⟩ := ihCall h mIr fnName (acc ++ args.take (arity - acc.length)) jsSt res h0 m0 hfnDom hhp hmEq hmNo (noTc_append haccNT fun a ht => hargs a (List.mem_of_mem_take ht)) hfns hirc
          obtain ⟨fJs2, st2, hjsc2, _, hvnt, hh2, he2, hf2, hm2Eq, hm2No⟩ := ihApp h0 m0 res (args.drop (arity - acc.length)) st1 v1 h1 m1 hresNT hh0 hm0Eq hm0No (fun a ha => hargs a (List.mem_of_mem_drop ha)) (fun s hs => by rw [hstF] at hs; exact hfns s hs) happ
          exact ⟨max fJs1 fJs2 + 1, st2, by rw [evalJsApp_succ]; dsimp only [evalJsAppStep]; rw [ite_eq_right hlt, ite_eq_right heq, ite_eq_right hrem, ← hc0fn, evalJsCall_mono (Nat.le_succ_of_le (Nat.le_max_left fJs1 fJs2)) hjsc1]; exact evalJsApp_mono (Nat.le_max_right fJs1 fJs2) hjsc2, rfl, hvnt, hh2, he2.trans hstE, hf2.trans hstF, hm2Eq, hm2No⟩
  | tc _ => exact False.elim (by unfold JsVal.noTc at hfnNT; exact hfnNT) | _ => cases happ; exact ⟨1, jsSt, rfl, rfl, hfnNT, hhp, rfl, rfl, hmEq, hmNo⟩

theorem eval_sim_ir_to_js : ∀ fuel : Nat, CallSimIJ E fuel ∧ AppSimIJ E fuel ∧ BodySimIJ E fuel := fun fuel => by
  induction fuel using Nat.strongRecOn with | ind fuel ih =>
  have hCall : CallSimIJ E fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; cases h | succ f' => exact eval_sim_ij_call_step E hprog f' (fun k hk => (ih k hk).1) (ih f' (Nat.lt_succ_self f')).2.2
  have hApp : AppSimIJ E fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; cases h | succ f' => exact eval_sim_ij_app_step E hprog f' hCall (ih f' (Nat.lt_succ_self f')).2.1
  exact ⟨hCall, hApp, eval_sim_ij_body_step E hprog fuel hCall hApp (fun f' hf' => (ih f' hf').2.2)⟩
end
end Js.Proofs
