import Qed.Proofs.KeyedReconcile
import Qed.Proofs.ViewPatch.Build
import Qed.Proofs.ViewPatch.Keyed
import Qed.Proofs.ViewPatch.Runtime

namespace Qed

section
variable {σ msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)

private abbrev PatchViewGoal (v : View σ msg) (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg) : Prop :=
  childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") → View.DomClean v → pre.length + 1 + suf.length < UInt32.size →
  a.nextId + htmlNodeCount (View.render v s₂) < UInt32.size → htmlDepth (View.render v s₂) ≤ f → parent.toNat < a.nextId → 0 < a.nextId →
  a.get parent = .element pns ptag pst pmg (pre ++ vst.rootNode :: suf) → (pre ++ vst.rootNode :: suf).Nodup → ¬Sold parent.toNat →
  (∀ k, Sold k → k < a.nextId) → (∀ r ∈ pre ++ vst.rootNode :: suf, r.toNat < a.nextId) → VStateValid f childNs v s₁ a Sold vst →
  PatchViewPost f childNs parent pns ptag pst pmg v s₂ pre suf Sold a ((patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) v s₂ vst).run a)

private theorem noop_post {v : View σ msg} {s₂ : σ} {pre suf : List Dom.Node} {Sold : Nat → Prop} {a : DomArena msg} {vst' : VState σ msg}
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ vst'.rootNode :: suf)) (hnd : (pre ++ vst'.rootNode :: suf).Nodup)
    (hparNodes : ∀ r ∈ pre ++ vst'.rootNode :: suf, r.toNat < a.nextId) (hval' : VStateValid f childNs v s₂ a (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a.nextId)) vst') :
    PatchViewPost f childNs parent pns ptag pst pmg v s₂ pre suf Sold a (vst', a) :=
  ⟨Nat.le_refl _, Nat.le_add_right .., fun _ _ _ _ => rfl, hpar, hnd, hparNodes, hval', VStateValid_equiv hval'⟩

private theorem patchHtml_post {v : View σ msg} {s₂ : σ} {h₁ : Html msg} {node : Dom.Node} {pre suf : List Dom.Node} {Sold : Nat → Prop} {a : DomArena msg}
    (mk : Dom.Node → VState σ msg) (hroot : ∀ n, (mk n).rootNode = n) (hmt : ∀ n a', VStateMatches v s₂ a' n (mk n))
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") (hpreLen : pre.length + 1 + suf.length < UInt32.size)
    (hbound : a.nextId + htmlNodeCount (View.render v s₂) < UInt32.size) (hdep : htmlDepth (View.render v s₂) ≤ f) (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ node :: suf)) (hnd : (pre ++ node :: suf).Nodup) (hparOut : ¬Sold parent.toNat)
    (hSoldLt : ∀ k, Sold k → k < a.nextId) (hparNodes : ∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId) (hcl : CleanDomSubtree f childNs h₁ a Sold node) (hcl₂ : (View.render v s₂).DomClean = true) :
    PatchViewPost f childNs parent pns ptag pst pmg v s₂ pre suf Sold a ((patchHtmlSubtreeM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node h₁ (View.render v s₂) >>= fun n => pure (mk n)).run a) := by
  have hp := patchHtmlSubtreeM_spec f childNs parent pns ptag pst pmg h₁ (View.render v s₂) node pre suf Sold a hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hcl hcl₂
  dsimp only [PatchViewPost, StateT.run, bind, StateT.bind, pure, StateT.pure] at hp ⊢
  rcases hsp : patchHtmlSubtreeM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node h₁ (View.render v s₂) a with ⟨n, a'⟩
  rw [hsp] at hp; dsimp only [VStateValid] at hp ⊢; rw [hroot n]
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, ⟨hp.2.2.2.2.2.2.1, hmt n a'⟩, hp.2.2.2.2.2.2.2⟩

private theorem patchViewKidsM_spec_of (kids : List (View σ msg)) (s₁ s₂ : σ)
    (hView : ∀ k ∈ kids, ∀ pre suf Sold a vst, PatchViewGoal f childNs parent pns ptag pst pmg k s₁ s₂ pre suf Sold a vst) :
    ∀ targetsDone preC sufC kstates Sdone Srem a,
      childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") → View.DomCleanEach kids →
      htmlListDepth (View.renderEach kids s₂) ≤ f → a.nextId + htmlListNodeCount (View.renderEach kids s₂) < UInt32.size →
      parent.toNat < a.nextId → 0 < a.nextId → a.get parent = .element pns ptag pst pmg (preC ++ sufC) → (preC ++ sufC).Nodup →
      (∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId) → CleanDomChildren f childNs targetsDone a Sdone preC →
      (∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) → (∀ k, Sdone k → Srem k → False) →
      (∀ r ∈ sufC, r.toNat < a.nextId ∧ r ≠ parent) → CleanDomChildren f childNs (View.renderEach kids s₁) a Srem sufC → VStateKidsMatches kids s₁ a sufC kstates →
      let (ks', aOut) := (patchViewKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat preC.length) kids s₂ kstates).run a
      ∃ Snew, let domCs' := ks'.map VState.rootNode
        a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount (View.renderEach kids s₂) ∧ aOut.get parent = .element pns ptag pst pmg (preC ++ domCs') ∧ (preC ++ domCs').Nodup ∧
        (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧ (∀ k, Snew k → (Sdone k ∨ Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧
        CleanDomChildren f childNs (targetsDone ++ View.renderEach kids s₂) aOut Snew (preC ++ domCs') ∧ VStateKidsMatches kids s₂ aOut domCs' ks' := by
  induction kids with
  | nil =>
      intro _ _ sufC kstates Sdone _ _ _ _ _ _ _ _ hpar hnd hSdone hDone _ _ _ hCl hVk
      cases sufC with | cons _ _ => exact False.elim hCl | nil => cases kstates with | cons _ _ => exact False.elim hVk | nil =>
      exact ⟨Sdone, Nat.le_refl _, Nat.le_refl _, hpar, hnd, fun _ _ _ _ => rfl, fun k hk => ⟨.inl hk, (hSdone k hk).1⟩, by rw [View.renderEach, List.map_nil, List.append_nil, List.append_nil]; exact hDone, trivial⟩
  | cons k rest ih =>
      intro targetsDone preC sufC kstates Sdone Srem a hchildNs ⟨hkCl, hrestCl⟩ hdep hbound hparLt hpos hpar hnd hSdone hDone hSrem hDisj hsufB hCl hVk
      cases sufC with | nil => exact False.elim hCl | cons _ sufRest => cases kstates with | nil => exact False.elim hVk | cons kst restSt =>
      rcases hCl with ⟨Sc, Srest, hSc, hSr, hDSr, hcCl, hSufCl⟩; rcases hVk with ⟨rfl, hkMatch, hRestMatch⟩
      simp only [View.renderEach, htmlListDepth] at hdep; simp only [View.renderEach, htmlListNodeCount] at hbound ⊢
      have hparNodes : ∀ r ∈ preC ++ kst.rootNode :: sufRest, r.toNat < a.nextId := fun r hr => (List.mem_append.1 hr).elim (fun hp => (hSdone _ (CleanDomChildren_mem hDone r hp)).2) fun hc => (hsufB r hc).1
      have hpreLen : preC.length + 1 + sufRest.length < UInt32.size := by have := nodup_nodes_lt_length_le a.nextId (preC ++ kst.rootNode :: sufRest) hnd hparNodes; simp only [List.length_append, List.length_cons] at this; omega
      have hpatchK := hView k (.head _) preC sufRest Sc a kst hchildNs hkCl hpreLen (by omega) (Nat.le_trans (Nat.le_max_left ..) hdep) hparLt hpos hpar hnd (fun h => (hSrem _ (hSc _ h)).1 rfl) (fun x hx => (hSrem x (hSc x hx)).2) hparNodes ⟨hcCl, hkMatch⟩
      dsimp only [patchViewKidsM, StateT.run, bind, StateT.bind, pure, StateT.pure] at hpatchK ⊢
      rcases hpK : patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat preC.length) k s₂ kst a with ⟨kst', aMid⟩
      rw [hpK] at hpatchK; rcases hpatchK with ⟨haMidGe, haMidBound, hfrMid, hparMid, hndMid, _, hValK', _⟩
      let Sdone' : Nat → Prop := fun x => Sdone x ∨ (Sc x ∨ (a.nextId ≤ x ∧ x < aMid.nextId))
      have ⟨hSdone', hDone'⟩ := clean_done_extend haMidGe hparLt hSdone (fun x h => hSrem x (hSc x h)) (fun x h1 h2 => hDisj x h1 (hSc x h2))
        (fun m hm => hfrMid m (node_ne_of_toNat_ne (hSdone _ hm).1) (fun hsc => hDisj _ hm (hSc _ hsc)) (hSdone _ hm).2) hDone hValK'.1
      have hfrSuf : ∀ m : Dom.Node, Srest m.toNat → aMid.get m = a.get m := fun m hm => hfrMid m (node_ne_of_toNat_ne (hSrem _ (hSr _ hm)).1) (fun hsc => hDSr _ hsc hm) (hSrem _ (hSr _ hm)).2
      rw [show UInt32.ofNat preC.length + 1 = UInt32.ofNat (preC ++ [kst'.rootNode]).length by simp only [List.length_append, List.length_singleton]; exact uint32_ofNat_succ preC.length (by omega)]
      have hih := ih (fun x hx => hView x (.tail _ hx)) (targetsDone ++ [View.render k s₂]) (preC ++ [kst'.rootNode]) sufRest restSt Sdone' Srest aMid
        hchildNs hrestCl (Nat.le_trans (Nat.le_max_right ..) hdep) (by omega) (Nat.lt_of_lt_of_le hparLt haMidGe) (Nat.lt_of_lt_of_le hpos haMidGe)
        (by rw [List.append_assoc, List.singleton_append]; exact hparMid) (by rw [List.append_assoc, List.singleton_append]; exact hndMid) hSdone' hDone'
        (fun x hx => let hb := hSrem x (hSr x hx); ⟨hb.1, Nat.lt_of_lt_of_le hb.2 haMidGe⟩) (fun x h1 h2 => not_Sdone_extend (fun h => hDisj x h (hSr x h2)) (fun hsc => hDSr x hsc h2) (hSrem x (hSr x h2)).2 h1)
        (fun r hr => let hb := hsufB r (.tail _ hr); ⟨Nat.lt_of_lt_of_le hb.1 haMidGe, hb.2⟩) (CleanDomChildren_frame hfrSuf hSufCl) (VStateKidsMatches_frame hfrSuf hSufCl hRestMatch)
      dsimp only [StateT.run] at hih ⊢; rcases hpR : patchViewKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (preC ++ [kst'.rootNode]).length) rest s₂ restSt aMid with ⟨_, _⟩
      rw [hpR] at hih; rcases hih with ⟨Snew, haOutGe, haOutBound, hparR, hndR, hfrR, hSnew, hCleanR, hVstR⟩
      rw [List.append_assoc, List.singleton_append] at hparR hndR hCleanR; rw [List.append_assoc, List.singleton_append] at hCleanR
      exact ⟨Snew, Nat.le_trans haMidGe haOutGe, Nat.le_trans haOutBound (Nat.add_assoc _ _ _ ▸ Nat.add_le_add_right haMidBound _), hparR, hndR,
        fun m hmPar hmR hmLt => (hfrR m hmPar (fun hr => hmR (hSr _ hr)) (Nat.lt_of_lt_of_le hmLt haMidGe)).trans (hfrMid m hmPar (fun hsc => hmR (hSc _ hsc)) hmLt),
        clean_step_Snew_compose haMidGe haOutGe hSc hSr hSnew, hCleanR, rfl,
        VStateMatches_frame (fun m hm => hfrR m (node_ne_of_toNat_ne (hSdone' m.toNat (.inr hm)).1) (fun hr => hm.elim (fun hs => hDSr _ hs hr) fun hlo => Nat.not_lt.2 hlo.1 (hSrem _ (hSr _ hr)).2) (hSdone' m.toNat (.inr hm)).2) hValK'.1 hValK'.2, hVstR⟩

private theorem patchViewM_ifElse_spec (cond : σ → Bool) (yes no : View σ msg) (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg)
    (ihY : ∀ inner, PatchViewGoal f childNs parent pns ptag pst pmg yes s₁ s₂ pre suf Sold a inner) (ihN : ∀ inner, PatchViewGoal f childNs parent pns ptag pst pmg no s₁ s₂ pre suf Sold a inner) :
    PatchViewGoal f childNs parent pns ptag pst pmg (.ifElse cond yes no) s₁ s₂ pre suf Sold a vst := by
  intro hchildNs hclean hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
  cases vst with
  | cond wasYes inner =>
    rcases hval with ⟨hcl, hwy, hin⟩; let targetV := if cond s₂ then yes else no
    have hren : View.render (.ifElse cond yes no) s₂ = View.render targetV s₂ := by dsimp only [targetV, View.render]; cases cond s₂ <;> rfl
    dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
    by_cases hsame : cond s₂ = wasYes
    · simp only [beq_iff_eq.2 hsame, ↓reduceIte]
      have hih : PatchViewPost f childNs parent pns ptag pst pmg targetV s₂ pre suf Sold a ((patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) targetV s₂ inner).run a) := by
        have hc₁ : cond s₁ = cond s₂ := hwy.symm.trans hsame.symm
        cases hc₂ : cond s₂ <;> simp only [targetV, hc₁, hc₂, Bool.false_eq_true, ↓reduceIte, View.render] at hbound hdep hcl hin ⊢
        · exact ihN inner hchildNs hclean.2 hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes ⟨hcl, hin⟩
        · exact ihY inner hchildNs hclean.1 hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes ⟨hcl, hin⟩
      dsimp only [PatchViewPost, StateT.run, StateT.bind, StateT.pure] at hih ⊢
      rcases hp : patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) targetV s₂ inner a with ⟨_, _⟩
      rw [hp] at hih; rcases hih with ⟨h1, h2, h3, h4, h5, h6, ⟨hcl', hm'⟩, heqv'⟩
      cases hc₂ : cond s₂ <;> (simp only [targetV, hc₂, Bool.false_eq_true, ↓reduceIte] at hp hm' ⊢; rw [hp]; exact ⟨h1, hren.symm ▸ h2, h3, h4, h5, h6, ⟨hren.symm ▸ hcl', hc₂.symm, by rw [hc₂]; exact hm'⟩, hren.symm ▸ heqv'⟩)
    · simp only [beq_eq_false_iff_ne.2 hsame, Bool.false_eq_true, ↓reduceIte, StateT.bind]
      rw [show MonadDom.childNamespace (m := StateM (DomArena msg)) parent a = (childNs, a) by simp only [MonadDom.childNamespace, hpar, hchildNs]]; dsimp only [Bind.bind]
      have huJ : (UInt32.ofNat pre.length).toNat = pre.length := uint32_toNat_ofNat_lt pre.length (by omega)
      have hbuild := buildViewM_vstate_spec childNs targetV s₂ a f (by dsimp only [targetV]; cases cond s₂; exact hclean.2; exact hclean.1) hpos (hren ▸ hbound) (hren ▸ hdep)
      dsimp only [StateT.run] at hbuild; rcases hB : buildViewM (m := StateM (DomArena msg)) childNs targetV s₂ a with ⟨⟨n2, newInner⟩, aMid⟩
      rw [hB] at hbuild; rcases hbuild with ⟨hn2Root, haMidGe, haMidBound, haMidFr, hVstMid, _⟩
      have hparMid : aMid.get parent = .element pns ptag pst pmg (pre ++ inner.rootNode :: suf) := (haMidFr parent hparLt).trans hpar
      let a' := aMid.set parent (.element pns ptag pst pmg (pre ++ n2 :: suf))
      have hVst' : VStateValid f childNs targetV s₂ a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) newInner := VStateValid_mono (fun _ => .inr) (VStateValid_frame (fun m hm => DomArena.get_set_ne _ _ fun e => Nat.not_lt.2 hm.1 (e ▸ hparLt)) hVstMid)
      have hVstIf : VStateValid f childNs (.ifElse cond yes no) s₂ a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) (.cond (cond s₂) newInner) := ⟨hren.symm ▸ hVst'.1, rfl, by cases hc₂ : cond s₂ <;> (simp only [targetV, hc₂, ↓reduceIte, Bool.false_eq_true] at hVst' ⊢; exact hVst'.2)⟩
      suffices hPost : PatchViewPost f childNs parent pns ptag pst pmg (.ifElse cond yes no) s₂ pre suf Sold a (.cond (cond s₂) newInner, a') by
        cases hc₂ : cond s₂ <;> (simp only [targetV, hc₂, Bool.false_eq_true, ↓reduceIte, StateT.bind, StateT.pure, Bind.bind] at hB ⊢; rw [hB]; simpa only [DomArena.modifyChildren, DomArena.modify, hparMid, huJ, listReplaceAt_append_middle, pure, a', hc₂] using hPost)
      exact ⟨haMidGe, hren.symm ▸ haMidBound, fun m hmPar _ hmLt => (DomArena.get_set_ne _ _ hmPar).trans (haMidFr m hmLt), by dsimp only [VState.rootNode]; rw [hn2Root]; exact DomArena.get_set_self ..,
        by dsimp only [VState.rootNode]; rw [hn2Root]; exact nodup_append_replace hnd (.inr fun hm => Nat.not_lt.2 (hn2Root ▸ VStateValid_root_mem hVstMid).1 (hparNodes n2 hm)),
        fun r hr => (List.mem_append.1 hr).elim (fun hp => Nat.lt_of_lt_of_le (hparNodes r (List.mem_append_left _ hp)) haMidGe) fun hc => (List.mem_cons.1 hc).elim (· ▸ (VStateValid_root_mem hVstMid).2) fun htl => Nat.lt_of_lt_of_le (hparNodes r (List.mem_append_right _ (.tail _ htl))) haMidGe,
        hVstIf, VStateValid_equiv hVstIf⟩
  | _ => exact False.elim hval.2

private theorem patchViewM_element_spec (tag : String) (attrs : List (VAttr σ msg)) (kids : List (View σ msg)) (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg)
    (ihk : ∀ k ∈ kids, ∀ f' node realNs st' mg' pre' suf' Sold' a' vst', PatchViewGoal f' (Dom.childNsOf childNs tag) node realNs tag st' mg' k s₁ s₂ pre' suf' Sold' a' vst') :
    PatchViewGoal f childNs parent pns ptag pst pmg (.element tag attrs kids) s₁ s₂ pre suf Sold a vst := by
  intro hchildNs hclean _ hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
  cases vst with
  | elem node kstates =>
    dsimp only [VStateValid, VState.rootNode] at hpar hnd hparNodes hval; rcases hval with ⟨hcl, _, _, _, st, mg, domCs, hgetM, hksM⟩
    cases f with | zero => exact False.elim hcl | succ f' =>
    rcases hcl with ⟨hnodeMem, _, _, _, _, _, hnodeGet, hElClean, hElEq, hmg, hCleanCs⟩; rw [hgetM] at hnodeGet; cases hnodeGet
    have hdyn := applyDynAttrsM_spec a node (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st mg domCs attrs s₁ s₂ hclean.1 hElClean hElEq hmg
    rw [DomArena.set_get_self a hgetM] at hdyn; rcases hdyn with ⟨ha1Next, ha1Ne, st', mg', ha1Get, hElClean', hElEq', hmg'⟩
    let a1 := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a).2; have ha1N : a1.nextId = a.nextId := ha1Next
    simp only [View.render, htmlNodeCount] at hbound; simp only [View.render, htmlDepth] at hdep
    have hkids := patchViewKidsM_spec_of f' (Dom.childNsOf childNs tag) node (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st' mg' kids s₁ s₂
      (fun k hk pre' suf' Sold' a' vst' => ihk k hk f' node _ st' mg' pre' suf' Sold' a' vst') [] [] domCs kstates (fun _ => False) (fun k => Sold k ∧ k ≠ node.toNat) a1
      (childNamespace_eq_childNsOf (ptag := tag) (by rw [hchildNs]; split <;> simp)).symm hclean.2 (by omega) (ha1N ▸ Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left _ 1) _) hbound)
      (ha1N ▸ hSoldLt _ hnodeMem) (ha1N ▸ hpos) ha1Get (CleanDomChildren_nodup hCleanCs).1 (fun _ h => h.elim) trivial (fun k hk => ⟨hk.2, ha1N ▸ hSoldLt k hk.1⟩) (fun _ h => h.elim)
      (fun r hr => let hb := CleanDomChildren_mem hCleanCs r hr; ⟨ha1N ▸ hSoldLt _ hb.1, node_ne_of_toNat_ne hb.2⟩)
      (CleanDomChildren_frame (fun m hm => ha1Ne m (node_ne_of_toNat_ne hm.2)) hCleanCs) (VStateKidsMatches_frame (fun m hm => ha1Ne m (node_ne_of_toNat_ne hm.2)) hCleanCs hksM)
    dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure] at hkids ⊢
    rw [show applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a = ((), a1) from rfl]; dsimp only
    rcases hkRun : patchViewKidsM (m := StateM (DomArena msg)) node 0 kids s₂ kstates a1 with ⟨ks', aOut⟩; rw [show (UInt32.ofNat ([] : List Dom.Node).length) = 0 from rfl, hkRun] at hkids
    rcases hkids with ⟨Snew, haOutGe, haOutBound, hnodeOut, _, hfrOut, hSnew, hCleanOut, hVstOut⟩; have haGe : a.nextId ≤ aOut.nextId := ha1N ▸ haOutGe
    have hvalOut : VStateValid (f' + 1) childNs (.element tag attrs kids) s₂ aOut (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) (.elem node ks') :=
      ⟨⟨.inl hnodeMem, hclean.1.1 s₂, hclean.1.2.1 s₂, st', mg', ks'.map VState.rootNode, hnodeOut, hElClean', hElEq', hmg',
        CleanDomChildren_mono (fun k hk => ⟨(hSnew k hk).1.elim False.elim fun h => h.elim (fun hs => .inl hs.1) fun ha => .inr ⟨ha1N ▸ ha.1, ha.2⟩, (hSnew k hk).2⟩) hCleanOut⟩, rfl, _, tag, st', mg', ks'.map VState.rootNode, hnodeOut, hVstOut⟩
    exact ⟨haGe, by simp only [View.render, htmlNodeCount]; omega, fun m _ hmOut hmLt => let hmn : m ≠ node := fun h => hmOut (h ▸ hnodeMem); (hfrOut m hmn (fun h => hmOut h.1) (ha1N ▸ hmLt)).trans (ha1Ne m hmn),
      by have hne : parent ≠ node := fun h => hparOut (h ▸ hnodeMem); rw [hfrOut parent hne (fun h => hparOut h.1) (ha1N ▸ hparLt), ha1Ne parent hne, hpar]; rfl, hnd, fun r hr => Nat.lt_of_lt_of_le (hparNodes r hr) haGe, hvalOut, VStateValid_equiv hvalOut⟩
  | _ => exact False.elim hval.2
end

theorem patchViewM_spec {σ msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (v : View σ msg) (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg)
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") (hclean : View.DomClean v) (hpreLen : pre.length + 1 + suf.length < UInt32.size)
    (hbound : a.nextId + htmlNodeCount (View.render v s₂) < UInt32.size) (hdep : htmlDepth (View.render v s₂) ≤ f) (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ vst.rootNode :: suf)) (hnd : (pre ++ vst.rootNode :: suf).Nodup)
    (hparOut : ¬Sold parent.toNat) (hSoldLt : ∀ k, Sold k → k < a.nextId) (hparNodes : ∀ r ∈ pre ++ vst.rootNode :: suf, r.toNat < a.nextId)
    (hval : VStateValid f childNs v s₁ a Sold vst) :
    PatchViewPost f childNs parent pns ptag pst pmg v s₂ pre suf Sold a ((patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) v s₂ vst).run a) := by
  suffices h : PatchViewGoal f childNs parent pns ptag pst pmg v s₁ s₂ pre suf Sold a vst from h hchildNs hclean hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
  clear hchildNs hclean hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
  induction v using View.ind generalizing f childNs parent pns ptag pst pmg pre suf Sold a vst with
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      intro hchildNs hclean _ hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
      exact patchViewM_keyedList_spec f childNs parent pns ptag pst pmg tag attrs keys marks rowSig rowEv rowsHtml tmpl? s₁ s₂ pre suf Sold a vst hchildNs hclean hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
  | text _ => intro _ _ _ _ _ _ _ hpar hnd _ _ hparNodes hval; cases vst with | text _ => exact noop_post f childNs parent pns ptag pst pmg hpar hnd hparNodes (VStateValid_mono (fun _ => .inl) hval) | _ => exact False.elim hval.2
  | static _ => intro _ _ _ _ _ _ _ hpar hnd _ _ hparNodes hval; cases vst with | stat _ => exact noop_post f childNs parent pns ptag pst pmg hpar hnd hparNodes (VStateValid_mono (fun _ => .inl) hval) | _ => exact False.elim hval.2
  | dyn get =>
      intro _ _ _ _ _ _ _ hpar hnd hparOut _ hparNodes hval
      cases vst with
      | dyn node _ =>
        rcases hval with ⟨hcl, _, rfl⟩; cases f with | zero => exact False.elim hcl | succ f' =>
        rcases hcl with ⟨hmem, hget⟩; dsimp only [VState.rootNode] at hmem hget hpar hnd hparNodes; dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
        by_cases heq : get s₂ = get s₁
        · simp only [show (get s₂ != get s₁) = false by simp [heq], Bool.false_eq_true, ↓reduceIte]
          exact noop_post (f' + 1) childNs parent pns ptag pst pmg hpar hnd hparNodes ⟨⟨.inl hmem, heq.symm ▸ hget⟩, rfl, rfl⟩
        · simp only [show (get s₂ != get s₁) = true by simp [heq], ↓reduceIte, StateT.bind, pure, StateT.pure, MonadDom.setText, DomArena.modify]; rw [hget]
          have hval' : VStateValid (f' + 1) childNs (.dyn get) s₂ (a.set node (.text (get s₂))) (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a.nextId)) (.dyn node (get s₂)) := ⟨⟨.inl hmem, DomArena.get_set_self ..⟩, rfl, rfl⟩
          exact ⟨Nat.le_refl _, Nat.le_add_right .., fun m _ hmOut _ => DomArena.get_set_ne _ _ fun hEq => hmOut (hEq ▸ hmem), (DomArena.get_set_ne _ _ (fun h : parent = node => hparOut (h ▸ hmem))).trans hpar, hnd, hparNodes, hval', VStateValid_equiv hval'⟩
      | _ => exact False.elim hval.2
  | dynNode get =>
      intro hchildNs hclean hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
      cases vst with | dynNode node _ => rcases hval with ⟨hcl, _, rfl⟩; exact patchHtml_post f childNs parent pns ptag pst pmg (fun n => .dynNode n (get s₂)) (fun _ => rfl) (fun _ _ => ⟨rfl, rfl⟩) hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hcl (hclean s₂) | _ => exact False.elim hval.2
  | memo sm =>
      intro hchildNs hclean hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
      cases vst with
      | memo node _ _ =>
        rcases hval with ⟨hcl, _, rfl, rfl⟩; dsimp only [patchViewM]
        by_cases hkey : sm.keyOf s₂ = sm.keyOf s₁
        · have heval : sm.eval s₂ = sm.eval s₁ := sm.sound s₂ s₁ hkey; simp only [beq_iff_eq.2 hkey, ↓reduceIte, StateT.run, pure, StateT.pure]
          exact noop_post f childNs parent pns ptag pst pmg hpar hnd hparNodes ⟨by rw [View.render, heval]; exact CleanDomSubtree_mono (fun _ => .inl) hcl, rfl, hkey.symm, heval.symm⟩
        · simp only [beq_eq_false_iff_ne.2 hkey, Bool.false_eq_true, ↓reduceIte]
          exact patchHtml_post f childNs parent pns ptag pst pmg (fun n => .memo n (sm.keyOf s₂) (sm.eval s₂)) (fun _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩) hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hcl (hclean s₂)
      | _ => exact False.elim hval.2
  | ifElse cond yes no ihy ihn => exact patchViewM_ifElse_spec f childNs parent pns ptag pst pmg cond yes no s₁ s₂ pre suf Sold a vst (ihy f childNs parent pns ptag pst pmg pre suf Sold a) (ihn f childNs parent pns ptag pst pmg pre suf Sold a)
  | element tag attrs kids ihk => exact patchViewM_element_spec f childNs parent pns ptag pst pmg tag attrs kids s₁ s₂ pre suf Sold a vst (fun k hk f' node realNs st' mg' => ihk k hk f' (Dom.childNsOf childNs tag) node realNs tag st' mg')

theorem patchViewKidsM_spec {σ msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (kids : List (View σ msg)) (targetsDone : List (Html msg)) (preC sufC : List Dom.Node) (kstates : List (VState σ msg)) (s₁ s₂ : σ) (Sdone Srem : Nat → Prop) (a : DomArena msg)
    (hchildNs : childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")) (hclean : View.DomCleanEach kids) (hdep : htmlListDepth (View.renderEach kids s₂) ≤ f)
    (hbound : a.nextId + htmlListNodeCount (View.renderEach kids s₂) < UInt32.size) (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (preC ++ sufC)) (hnd : (preC ++ sufC).Nodup) (hSdone : ∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId)
    (hDone : CleanDomChildren f childNs targetsDone a Sdone preC) (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) (hDisj : ∀ k, Sdone k → Srem k → False)
    (hsufB : ∀ r ∈ sufC, r.toNat < a.nextId ∧ r ≠ parent) (hCl : CleanDomChildren f childNs (View.renderEach kids s₁) a Srem sufC) (hVk : VStateKidsMatches kids s₁ a sufC kstates) :
    let (ks', aOut) := (patchViewKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat preC.length) kids s₂ kstates).run a
    ∃ Snew, let domCs' := ks'.map VState.rootNode
      a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount (View.renderEach kids s₂) ∧ aOut.get parent = .element pns ptag pst pmg (preC ++ domCs') ∧ (preC ++ domCs').Nodup ∧
      (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧ (∀ k, Snew k → (Sdone k ∨ Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧
      CleanDomChildren f childNs (targetsDone ++ View.renderEach kids s₂) aOut Snew (preC ++ domCs') ∧ VStateKidsMatches kids s₂ aOut domCs' ks' :=
  patchViewKidsM_spec_of f childNs parent pns ptag pst pmg kids s₁ s₂ (fun k _ pre' suf' Sold' a' vst' => patchViewM_spec f childNs parent pns ptag pst pmg k s₁ s₂ pre' suf' Sold' a' vst')
    targetsDone preC sufC kstates Sdone Srem a hchildNs hclean hdep hbound hparLt hpos hpar hnd hSdone hDone hSrem hDisj hsufB hCl hVk

end Qed
