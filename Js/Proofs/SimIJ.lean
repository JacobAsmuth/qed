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
      dsimp only [evalIrBody, evalIrBodyStep] at hev; injection hev with hev; injection hev with h1 h2; subst h1 h2
      left; exact ⟨0, jsSt, evalJsStmts_lower_ret 0 hsm.env_eq a, evalIrArg_noTc hsm.env_noTc a, hsm.heap_eq, hsm.memos_eq, hsm.memos_noTc⟩
  | unreachable => cases hev
  | set x i y cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_set x i y cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf) hev
  | setTag x cidx cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_setTag x cidx cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf) hev
  | uset x i y cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_uset x i y cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf) hev
  | sset x n off y ty cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_sset x n off y ty cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf) hev
  | dec x n cf bf cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_rcDec x n (.dec x n cf bf cont) cont hsm rfl fun _ => rfl) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf) hev
  | del x cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_rcDec x 1 (.del x cont) cont hsm rfl fun _ => rfl) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf) hev
  | inc x n cf bf cont => rw [BodyWf] at hwf; exact ExitMatchIJ.ofLockstep (lockstep_inc x n cf bf cont hsm hwf.2) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwf.1) hev
  | case tid x xType alts =>
      rw [BodyWf] at hwf; dsimp only [evalIrBody, evalIrBodyStep] at hev; have hsw := caseScrut_eq jsProg c tid x xType alts hsm.env_eq
      have hres := evalIrAlts_sim_ij (x := x) alts.toList hwf (fun arm hm hwfa ha => hb arm hm c inlineJps recJps allowTailCont irSt jsSt irO irSt1 hnames hmin henv hselfNodup hwfa hsm ha) hev
      cases irO <;> simpa only [ExitMatchIJ, hsw] using hres
  | jmp j ys =>
      rw [BodyWf] at hwf; rcases hwf with hin | hrec
      · obtain ⟨hnotInM, hjsStep, hok⟩ := inlineJmp_step (jsProg := jsProg) hsm hin
        rw [evalIrBody_jmp_inline _ _ _ _ _ _ _ _ hnotInM, Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev; exact ⟨0, _, hjsStep 0, hok⟩
      · obtain ⟨hnone, hnotIn⟩ := hsm.recJp_not_inline hrec
        cases fSub with | zero => dsimp only [evalIrBody, evalIrBodyStep] at hev; rw [if_neg hnotIn] at hev; cases hev | succ f' =>
        rw [evalIrBody_jmp_not_inline _ _ _ _ _ _ _ _ hnotIn] at hev; cases hjir : irSt.jps j.idx with | none => rw [hjir] at hev; cases hev | some jdata =>
        rcases jdata with ⟨xs, val, capIr⟩; rw [hjir] at hev; dsimp only at hev
        obtain ⟨cVal, capJs, hjjs, hcvN, hcvM, hcvE, hcvSF, _, hcvDL, hselfVal, hwfVal, hsmVal⟩ := hsm.enterRecJp hprog.nonArr_param hselfNodup hrec hjir
        cases hirV : evalIrBody prog c0 revName [] f' { env := bindIrParams xs (ys.toList.map (evalIrArg irSt.env)) capIr, heap := irSt.heap, jps := irSt.jps, memos := irSt.memos } val with | none => rw [hirV] at hev; cases hev | some irR =>
        rcases irR with ⟨irOVal, st1⟩; rw [hirV] at hev; cases irOVal with | jumped _ _ => cases hev | returned rval =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev
        rcases hbodyPrev f' (Nat.lt_succ_self f') cVal [] (suffixFrom j.idx recJps) _ val _ _ (.returned rval) st1 hcvN hcvM hcvE hselfVal hwfVal hsmVal hirV with
          ⟨fJsVal, jsStVal, hjsVal, hnt, hhp1, hmEq1, hmNo1⟩ | ⟨halV, fJsVal, jsStVal, sf, na, m0, fIr', hle', hsf, hna', hjsVal, hm0, hm0n, hrc⟩
        · left; exact ⟨fJsVal + 1, { jsSt with heap := jsStVal.heap, memos := jsStVal.memos }, by rw [evalJsStmts_lower_recJmp_call fJsVal hsm.env_eq ys hnone hjjs, hjsVal], hnt, hhp1, hmEq1, hmNo1⟩
        · have hcValDL : cVal.directLoop = false := by cases h : cVal.directLoop with | false => rfl | true => rw [h] at halV; exact nomatch halV
          rw [hcValDL] at halV hjsVal
          right; exact ⟨halV, fJsVal + 1, { jsSt with heap := jsStVal.heap, memos := jsStVal.memos }, sf, na, m0, fIr', Nat.le_succ_of_le hle', hcvSF ▸ hsf, hna', by rw [← hcvDL, hcValDL, evalJsStmts_lower_recJmp_call fJsVal hsm.env_eq ys hnone hjjs, hjsVal]; rfl, hm0, hm0n, hrc⟩
  | jdecl j xs val cont =>
      rw [BodyWf] at hwf; rcases hwf with ⟨hnd, hnotIn, hnotRec, hcNone, hrec⟩; by_cases hjmp : (!hasJmpTo j val) = true
      · simp only [hjmp, ↓reduceIte] at hrec; rw [evalIrBody_inlineJdecl _ _ j xs val cont hjmp] at hev
        have hlower := fun fJs st => evalJsStmts_lower_inlineJdecl (jsProg := jsProg) (c := c) (jsSt := st) fJs j xs val cont hjmp
        cases hirC : evalIrBody prog c0 revName (j.idx :: inlineJps.map Prod.fst) fSub irSt cont with | none => rw [hirC] at hev; cases hev | some irRC =>
        rcases irRC with ⟨irOC, irStC⟩; rw [hirC] at hev
        have hexC := hb.2 { c with inlineJps := c.inlineJps.insert j.idx xs } ((j.idx, xs.size) :: inlineJps) recJps allowTailCont irSt jsSt irOC irStC hnames hmin henv hselfNodup hrec.1 (hsm.pushInlineJp j xs hnotIn hnotRec) hirC
        cases irOC with
        | returned rv =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev; dsimp only [ExitMatchIJ] at hexC ⊢
            exact hexC.elim (fun ⟨fJs, jsSt1, hjs, hok⟩ => .inl ⟨fJs, jsSt1, by rw [hlower fJs jsSt, hjs], hok⟩)
              (fun ⟨hal, fJs, jsSt1, sf, na, m0, fIr', hle, hsf, hna', hjs, hm0, hm0n, hrc⟩ => .inr ⟨hal, fJs, jsSt1, sf, na, m0, fIr', hle, hsf, hna', by rw [hlower fJs jsSt, hjs]; cases c.directLoop <;> rfl, hm0, hm0n, hrc⟩)
        | jumped j' args =>
            dsimp only at hev; rcases hexC with ⟨fJsC, jsStC, hjsC, hin', hslots, hargsNoTc, hsm1⟩; by_cases hj'j : j'.idx = j.idx
            · obtain ⟨hj'eq, hj'beq, hjpBeq, hlen⟩ := inlineJp_hit hj'j hin' hnotIn; rw [if_pos hj'beq] at hev
              exact ExitMatchIJ.rwJsMono (f₁ := fJsC) (fun fJs hf => by rw [hlower _ jsSt, evalJsStmts_mono hf hjsC]; dsimp only; rw [if_pos hjpBeq, evalJsStmts_inlineJp_post jsProg fJs jsStC j j' hj'eq args xs hlen hslots])
                (hb.1 c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hrec.2 (hsm1.bindInlineJp hsm.rec_disj hsm.inline_sub xs args hnd hlen hargsNoTc fun k hk => hprog.nonArr_param c.nonArr xs args _ k hk hsm1.nonArr_ok) hev)
            · obtain ⟨hneJ, hjpNe, hin0⟩ := inlineJp_miss hj'j hin'
              rw [if_neg (by rw [hneJ]; decide), Option.some.injEq, Prod.mk.injEq] at hev; obtain ⟨rfl, rfl⟩ := hev
              exact ⟨fJsC, jsStC, by rw [hlower fJsC jsSt, hjsC]; simp [hjpNe], hin0, hslots, hargsNoTc, hsm1.withCtx rfl rfl rfl rfl rfl hsm.rec_disj hsm.inline_sub⟩
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
            obtain ⟨hne1, hne2, hne3⟩ := (hprog.fn_disjoint (c0.js f) f (hprog.rev_ok f _ hfd)).2
            have hev0 := hev; dsimp only [evalIrBody, evalIrBodyStep] at hev; rw [if_neg (by rw [hrefF]; decide)] at hev
            cases hirc : evalIrCall prog c0 revName fSub irSt.heap irSt.memos f (ys.toList.map (evalIrArg irSt.env)) with | none => rw [hirc] at hev; cases hev | some irRes =>
            rcases irRes with ⟨val, h', m'⟩; rw [hirc] at hev; obtain ⟨hvalNT, _⟩ := hprog.nonArr_typed fSub irSt.heap irSt.memos f _ val h' m' hsm.memos_noTc hirc
            by_cases htc : (c.selfFn == some f && retsVar x cont) = true
            · obtain ⟨hal, htrc, _⟩ := htail htc; have hsf : c.selfFn = some f := eq_of_beq (Bool.and_eq_true_iff.1 htc).1; have hretV : retsVar x cont = true := (Bool.and_eq_true_iff.1 htc).2
              rw [evalIrBody_fap_tailRc _ _ x ty f ys cont hrefF htrc hretV hsm.nonArr_ok (fun hm => (hprog.nonArr_call c.nonArr fSub irSt.heap irSt.memos f _ val h' m' x.idx hm).1 hirc) hirc, Option.some.injEq, Prod.mk.injEq] at hev0; obtain ⟨rfl, rfl⟩ := hev0
              right; exact ⟨hal, 0, _, f, ys.toList.map (evalIrArg irSt.env), irSt.memos, fSub, Nat.le_refl _, hsf, evalIrArgs_noTc hsm.env_noTc ys,
                evalJsStmts_lower_fap_selfTail 0 hsm.env_eq x ty f ys cont htc, by cases c.directLoop <;> exact hsm.memos_eq, hsm.memos_noTc, by cases c.directLoop <;> simp only [Bool.false_eq_true, ↓reduceIte, ← hsm.heap_eq, hirc]⟩
            · obtain ⟨fJs1, jsSt1, hjsc, _, _, hhp', hme1, hmfns1, hmeq1, hmno1⟩ := hcallSub irSt.heap irSt.memos f (ys.toList.map (evalIrArg irSt.env)) jsSt val h' m'
                (by rw [hfd]; simp) hsm.heap_eq hsm.memos_eq hsm.memos_noTc (evalIrArgs_noTc hsm.env_noTc ys) hsm.fns_only_jp hirc
              refine ExitMatchIJ.rwJsMono (f₁ := fJs1) (fun fJs hf => by rw [evalJsStmts_lower_fap_call fJs hsm.env_eq x ty f ys cont (Bool.eq_false_iff.2 htc) hlow ⟨hne1, hne2, hne3⟩, evalJsCall_mono hf hjsc])
                (hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwfc (hsm.updCall x hvalNT (fun hm => (hprog.nonArr_call c.nonArr fSub irSt.heap irSt.memos f _ val h' m' x.idx hm).1 hirc) hhp' hme1 hmfns1 hmeq1 hmno1) hev)
      | ap y ys =>
          dsimp only [evalIrBody, evalIrBodyStep] at hev; cases hirc : evalIrApp prog c0 revName fSub irSt.heap irSt.memos (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) with | none => rw [hirc] at hev; cases hev | some irRes =>
          rcases irRes with ⟨val, h', m'⟩; rw [hirc] at hev
          obtain ⟨fJs1, jsSt1, hjsc, _, hvnt, hhp', hme1, hmfns1, hmeq1, hmno1⟩ := happSub irSt.heap irSt.memos (irSt.env y.idx) (ys.toList.map (evalIrArg irSt.env)) jsSt val h' m' hsm.heap_eq hsm.memos_eq hsm.memos_noTc (hsm.env_noTc y.idx) (evalIrArgs_noTc hsm.env_noTc ys) hsm.fns_only_jp hirc
          exact ExitMatchIJ.rwJsMono (f₁ := fJs1) (fun fJs hf => by rw [evalJsStmts_lower_ap fJs hsm.env_eq x ty y ys cont, evalJsApp_mono hf hjsc])
            (hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwfc (hsm.updCall x hvnt (fun hm => (hprog.nonArr_call c.nonArr fSub irSt.heap irSt.memos default _ val h' m' x.idx hm).2 (irSt.env y.idx) hirc) hhp' hme1 hmfns1 hmeq1 hmno1) hev)
      | isShared y => exact ExitMatchIJ.ofLockstep (lockstep_isShared x ty y cont hsm) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwfc) hev
      | pap _ _ => exact ExitMatchIJ.ofLockstep (lockstep_pure_vdecl hprog hnames henv hsm _ trivial (fun f' ys' he => by injection he with hf _; exact hf ▸ hwe) (fun _ => evalIrPure_ctor_isNonArr c0 ty irSt.env _ trivial)) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwfc) hev
      | ctor _ _ | reuse _ _ _ _ | reset _ _ | lit _ => exact ExitMatchIJ.ofLockstep (lockstep_pure_vdecl hprog hnames henv hsm _ trivial (fun _ _ he => nomatch he) (fun _ => evalIrPure_ctor_isNonArr c0 ty irSt.env _ trivial)) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwfc) hev
      | proj _ _ | uproj _ _ | sproj _ _ _ | box _ _ | unbox _ => exact ExitMatchIJ.ofLockstep (lockstep_pure_vdecl hprog hnames henv hsm _ trivial (fun _ _ he => nomatch he) (fun hx => hprog.nonArr_pure c.nonArr irSt.env ty x _ hx hsm.nonArr_ok)) (fun _ _ => hb c inlineJps recJps allowTailCont _ _ irO irSt1 hnames hmin henv hselfNodup hwfc) hev

private theorem eval_sim_ij_call_step (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (hprog : ProgLowered prog c0 jsProg revName) (f' : Nat) (ihCall : ∀ k < f' + 1, CallSimIJ prog c0 jsProg revName k) (ihBody : BodySimIJ prog c0 jsProg revName f') :
    CallSimIJ prog c0 jsProg revName (f' + 1) := by
  intro h mIr f args jsSt v1 h1 m1 hf hhp hmEq hmNo hargs hfns hirc
  cases hpf : prog f with | none => exact absurd hpf hf | some d => cases d with
  | extern _ _ _ _ => exact False.elim (hprog.findEnv_ok f _ hpf).2.1
  | fdecl fnm xs ty b info =>
      have hfnm := hprog.fdecl_name f fnm xs ty b info hpf; subst fnm
      have hfnsNone := fdecl_fns_none hprog hpf hfns; have hjsD := hprog.js_at_fdecl f xs ty b info hpf; have hdwf := hprog.decl_wf f xs ty b info hpf; dsimp only at hdwf
      by_cases hemp : xs.isEmpty = true
      · rw [evalIrCall_fdecl_memo f' hpf hemp] at hirc; simp only [hemp, ↓reduceIte] at hdwf; have hcOk : (mIr f).ok = (jsSt.memos (c0.js f)).ok := by rw [hmEq f hf]
        by_cases hmok : (mIr f).ok = true
        · rw [if_pos hmok, Option.some.injEq, Prod.mk.injEq] at hirc; obtain ⟨rfl, rfl, rfl⟩ := hirc
          exact ⟨1, jsSt, by rw [evalJsCall_lower_memo f xs ty b info args 0 hfnsNone hjsD hemp, ← hmEq f hf, if_pos hmok], rfl, memoVal_noTc hmNo f, hhp, rfl, rfl, hmEq, hmNo⟩
        · have hmokJs : (jsSt.memos (c0.js f)).ok = false := by rw [← hcOk, Bool.eq_false_iff.2 hmok]
          rw [if_neg hmok] at hirc; cases hini : getInitFnNameFor? c0.env f with
          | some initFn =>
              rw [hini] at hirc; dsimp only at hirc; simp only [hini] at hdwf; rcases hdwf with ⟨_, _, _, _, hiniDom, _⟩
              cases hirI : evalIrCall prog c0 revName f' h mIr initFn [] with | none => rw [hirI] at hirc; cases hirc | some irR =>
              rcases irR with ⟨v0, h0, m0⟩; rw [hirI, Option.some.injEq, Prod.mk.injEq] at hirc; obtain ⟨rfl, rfl, rfl⟩ := hirc
              obtain ⟨fJsI, stI, hjsI, _, hvnt, hh1, _, _, hm1Eq, hm1No⟩ := ihCall f' (Nat.lt_succ_self f') h mIr initFn [] jsSt v0 h1 m0 (by rw [hiniDom]; simp) hhp hmEq hmNo (fun _ h => nomatch h) hfns hirI
              exact ⟨fJsI + 1, { jsSt with heap := stI.heap, memos := fun k => if k == c0.js f then { ok := true, val := some v0 } else stI.memos k },
                by rw [evalJsCall_lower_memo f xs ty b info args fJsI hfnsNone hjsD hemp, if_neg (by rw [hmokJs]; decide), hini]; dsimp only; rw [hjsI],
                rfl, hvnt, hh1, rfl, rfl, memoUpdate_eq hprog.rev_ok hm1Eq hf v0, memoUpdate_noTc hm1No f hvnt⟩
          | none =>
              rw [hini] at hirc; dsimp only at hirc; simp only [hini] at hdwf; let cM := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b }
              cases hirB : evalIrBody prog c0 revName [] f' { env := fun _ => .num 0, heap := h, memos := mIr } b with | none => rw [hirB] at hirc; cases hirc | some irR => rcases irR with ⟨irO, irSt1⟩; rw [hirB] at hirc; cases irO with | jumped _ _ => cases hirc | returned rv =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hirc; obtain ⟨rfl, rfl, rfl⟩ := hirc
              obtain ⟨fJsB, jsSt1, hjsB, hvnt, hh1, hm1Eq, hm1No⟩ := (ihBody cM [] [] false b _ _ (.returned rv) irSt1 rfl rfl rfl (fun _ h => by simp [cM, hprog.c0_clean.1] at h) hdwf
                (fdecl_initCall hprog cM false jsSt h mIr #[] [] hhp hmEq hmNo List.nodup_nil fun _ h => nomatch h) hirB).of_false_ret
              exact ⟨fJsB + 1, { jsSt with heap := jsSt1.heap, memos := fun k => if k == c0.js f then { ok := true, val := some rv } else jsSt1.memos k },
                by rw [evalJsCall_lower_memo f xs ty b info args fJsB hfnsNone hjsD hemp, if_neg (by rw [hmokJs]; decide), hini]; dsimp only [cM, bindMany, List.map, List.zip, List.zipWith] at hjsB ⊢; rw [hjsB],
                rfl, hvnt, hh1, rfl, rfl, memoUpdate_eq hprog.rev_ok hm1Eq hf rv, memoUpdate_noTc hm1No f hvnt⟩
      · have hempF : xs.isEmpty = false := Bool.eq_false_iff.2 hemp; rw [evalIrCall_fdecl_nonempty f' hpf hempF] at hirc; simp only [hempF, Bool.false_eq_true, ↓reduceIte] at hdwf; rcases hdwf with ⟨hnd, hwfBody⟩
        cases hirB : evalIrBody prog c0 revName [] f' { env := bindIrParams xs args (fun _ => .num 0), heap := h, memos := mIr } b with | none => rw [hirB] at hirc; cases hirc | some irR => rcases irR with ⟨irO, irSt1⟩; rw [hirB] at hirc; cases irO with | jumped _ _ => cases hirc | returned rv =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hirc; obtain ⟨rfl, rfl, rfl⟩ := hirc
        by_cases hst : hasSelfTail f b = true
        · let dl := !hasJpSelfTail f b; let cL := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b, selfFn := some f, selfParams := xs, directLoop := dl }
          obtain ⟨hxsPos, _, hcLwf, hjsL⟩ := fdecl_selfTail_setup hprog hpf hempF hst
          rcases ihBody cL [] [] true b _ _ (.returned rv) irSt1 rfl rfl rfl (fun _ hs => by cases hs; exact ⟨hf, hxsPos, hnd⟩) hcLwf
            (fdecl_initCall hprog cL true jsSt h mIr xs args hhp hmEq hmNo hnd hargs) hirB with
            ⟨fJsB, jsSt1, hjsB, hvnt, hh1, hm1Eq, hm1No⟩ | ⟨_, fJsB, jsSt1, sf, na, m0, fIr', hle', hsf, hna', hjsB, hm0, hm0n, hrc⟩
          · exact ⟨fJsB + 1, { jsSt with heap := jsSt1.heap, memos := jsSt1.memos }, (evalJsCall_selfTail dl jsProg c0 f _ (lowerBody cL b) jsSt args fJsB hfnsNone hjsL _ _ hjsB).1 rv hvnt rfl, rfl, hvnt, hh1, rfl, rfl, hm1Eq, hm1No⟩
          · cases hsf; obtain ⟨fJsRec, st2, hjRec, _, hvnt, hh2, he2, hf2, hm2Eq, hm2No⟩ := ihCall fIr' (Nat.lt_succ_of_le hle') jsSt1.heap m0 f na { jsSt with heap := jsSt1.heap, memos := jsSt1.memos } rv irSt1.heap irSt1.memos hf rfl hm0 hm0n hna' hfns hrc
            exact ⟨max fJsB fJsRec + 1, st2, by rw [(evalJsCall_selfTail dl jsProg c0 f _ (lowerBody cL b) jsSt args fJsB hfnsNone hjsL _ _ (by simpa [cL] using hjsB)).2 na rfl (max fJsB fJsRec) (Nat.le_max_left _ _)]; exact evalJsCall_mono (Nat.le_max_right _ _) hjRec, rfl, hvnt, hh2, he2, hf2, hm2Eq, hm2No⟩
        · have hstF : hasSelfTail f b = false := Bool.eq_false_iff.2 hst; simp only [hstF, Bool.false_eq_true, ↓reduceIte] at hwfBody
          let cP := { c0 with nonArr := collectNonArr {} b, projSrc := collectProjSrc {} {} b }
          obtain ⟨fJsB, jsSt1, hjsB, hvnt, hh1, hm1Eq, hm1No⟩ := (ihBody cP [] [] false b _ _ (.returned rv) irSt1 rfl rfl rfl (fun _ h => by simp [cP, hprog.c0_clean.1] at h) hwfBody
            (fdecl_initCall hprog cP false jsSt h mIr xs args hhp hmEq hmNo hnd hargs) hirB).of_false_ret
          exact ⟨fJsB + 1, { jsSt with heap := jsSt1.heap, memos := jsSt1.memos }, by rw [evalJsCall_lower_plain f xs ty b info args fJsB hfnsNone hjsD hempF hstF]; dsimp only [cP] at hjsB; rw [hjsB], rfl, hvnt, hh1, rfl, rfl, hm1Eq, hm1No⟩

private theorem eval_sim_ij_app_step (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (hprog : ProgLowered prog c0 jsProg revName) (f' : Nat) (ihCall : CallSimIJ prog c0 jsProg revName (f' + 1)) (ihApp : AppSimIJ prog c0 jsProg revName f') : AppSimIJ prog c0 jsProg revName (f' + 1) := by
  intro h mIr fnVal args jsSt v1 h1 m1 hhp hmEq hmNo hfnNT hargs hfns happ; rw [evalIrApp_succ] at happ; dsimp only [evalIrAppStep] at happ; cases fnVal with
  | pap fnStr arity acc =>
      rw [JsVal.noTc] at hfnNT; rcases hfnNT with ⟨hfnNotJp, haccNT⟩; dsimp only at happ; by_cases hlt : args.length < arity - acc.length
      · rw [if_pos hlt, Option.some.injEq, Prod.mk.injEq] at happ; obtain ⟨rfl, rfl, rfl⟩ := happ
        exact ⟨1, jsSt, by rw [evalJsApp_succ]; dsimp only [evalJsAppStep]; rw [if_pos hlt], rfl, by rw [JsVal.noTc]; exact ⟨hfnNotJp, noTcList_append haccNT (noTcList_of_forall hargs)⟩, hhp, rfl, rfl, hmEq, hmNo⟩
      · rw [if_neg hlt] at happ; cases hrev : revName fnStr with | none => rw [hrev] at happ; cases happ | some fnName =>
        rw [hrev] at happ; dsimp only at happ; obtain ⟨hfnDom, hc0fn⟩ := hprog.rev_none fnStr fnName hrev
        by_cases heq : args.length == arity - acc.length
        · rw [if_pos heq] at happ; obtain ⟨fJs, st2, hjsc, hpost⟩ := ihCall h mIr fnName (acc ++ args) jsSt v1 h1 m1 hfnDom hhp hmEq hmNo (noTcList_mem (noTcList_append haccNT (noTcList_of_forall hargs))) hfns happ
          obtain ⟨k, rfl⟩ : ∃ k, fJs = k + 1 := by cases fJs with | zero => cases hjsc | succ k => exact ⟨k, rfl⟩
          exact ⟨k + 1, st2, by rw [evalJsApp_succ]; dsimp only [evalJsAppStep]; rw [if_neg hlt, if_pos heq, ← hc0fn]; exact hjsc, hpost⟩
        · rw [if_neg heq] at happ; by_cases hrem : arity - acc.length == 0; · rw [if_pos hrem] at happ; cases happ
          rw [if_neg hrem] at happ; cases hirc : evalIrCall prog c0 revName (f' + 1) h mIr fnName (acc ++ args.take (arity - acc.length)) with | none => rw [hirc] at happ; cases happ | some irR =>
          rcases irR with ⟨res, h0, m0⟩; rw [hirc] at happ
          obtain ⟨fJs1, st1, hjsc1, _, hresNT, hh0, hstE, hstF, hm0Eq, hm0No⟩ := ihCall h mIr fnName (acc ++ args.take (arity - acc.length)) jsSt res h0 m0 hfnDom hhp hmEq hmNo (noTcList_mem (noTcList_append haccNT (noTcList_take _ (noTcList_of_forall hargs)))) hfns hirc
          obtain ⟨fJs2, st2, hjsc2, _, hvnt, hh2, he2, hf2, hm2Eq, hm2No⟩ := ihApp h0 m0 res (args.drop (arity - acc.length)) st1 v1 h1 m1 hh0 hm0Eq hm0No hresNT (noTcList_mem (noTcList_drop _ (noTcList_of_forall hargs))) (fun s hs => by rw [hstF] at hs; exact hfns s hs) happ
          exact ⟨max fJs1 fJs2 + 1, st2, by rw [evalJsApp_succ]; dsimp only [evalJsAppStep]; rw [if_neg hlt, if_neg heq, if_neg hrem, ← hc0fn, evalJsCall_mono (Nat.le_succ_of_le (Nat.le_max_left fJs1 fJs2)) hjsc1]; exact evalJsApp_mono (Nat.le_max_right fJs1 fJs2) hjsc2, rfl, hvnt, hh2, he2.trans hstE, hf2.trans hstF, hm2Eq, hm2No⟩
  | tc _ => simp [JsVal.noTc] at hfnNT
  | _ => simp only [Option.some.injEq, Prod.mk.injEq] at happ; obtain ⟨rfl, rfl, rfl⟩ := happ; exact ⟨1, jsSt, rfl, rfl, hfnNT, hhp, rfl, rfl, hmEq, hmNo⟩

theorem eval_sim_ir_to_js (prog : IrProg) (c0 : Ctx) (jsProg : JsProg) (revName : String → Option Name) (hprog : ProgLowered prog c0 jsProg revName) :
    ∀ fuel : Nat, CallSimIJ prog c0 jsProg revName fuel ∧ AppSimIJ prog c0 jsProg revName fuel ∧ BodySimIJ prog c0 jsProg revName fuel := fun fuel => by
  induction fuel using Nat.strongRecOn with | ind fuel ih =>
  have hCall : CallSimIJ prog c0 jsProg revName fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; cases h | succ f' => exact eval_sim_ij_call_step prog c0 jsProg revName hprog f' (fun k hk => (ih k hk).1) (ih f' (Nat.lt_succ_self f')).2.2
  have hApp : AppSimIJ prog c0 jsProg revName fuel := by cases fuel with | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; cases h | succ f' => exact eval_sim_ij_app_step prog c0 jsProg revName hprog f' hCall (ih f' (Nat.lt_succ_self f')).2.1
  exact ⟨hCall, hApp, eval_sim_ij_body_step prog c0 jsProg revName hprog fuel hCall hApp (fun f' hf' => (ih f' hf').2.2)⟩

end Js.Proofs
