import Qed.Proofs.KeyedReconcile
import Qed.Proofs.ViewPatch.Build
import Qed.Proofs.ViewPatch.Keyed
import Qed.Proofs.ViewPatch.Runtime

namespace Qed

section
variable {σ msg : Type} (ep : ElemPar msg)

private abbrev PatchViewGoal (v : View σ msg) (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg) : Prop :=
  ParentSlot ep vst.rootNode pre suf Sold a → View.DomClean v → a.nextId + htmlNodeCount (View.render v s₂) < UInt32.size →
  htmlDepth (View.render v s₂) ≤ ep.f → VStateValid ep.f ep.childNs v s₁ a Sold vst →
  PatchViewPost ep v s₂ pre suf Sold a ((patchViewM (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) v s₂ vst).run a)

private theorem noop_post {v : View σ msg} {s₂ : σ} {pre suf : List Dom.Node} {Sold : Nat → Prop} {a : DomArena msg} {vst' : VState σ msg}
    (ps : ParentSlot ep vst'.rootNode pre suf Sold a) (hval' : VStateValid ep.f ep.childNs v s₂ a (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a.nextId)) vst') :
    PatchViewPost ep v s₂ pre suf Sold a (vst', a) := ⟨ArenaExt.refl, ps.hpar, ps.hnd, ps.hparNodes, hval', VStateValid_equiv hval'⟩

private theorem patchHtml_post {v : View σ msg} {s₂ : σ} {h₁ : Html msg} {node : Dom.Node} {pre suf : List Dom.Node} {Sold : Nat → Prop} {a : DomArena msg}
    (mk : Dom.Node → VState σ msg) (hroot : ∀ n, (mk n).rootNode = n) (hmt : ∀ n a', VStateMatches v s₂ a' n (mk n))
    (ps : ParentSlot ep node pre suf Sold a) (hbound : a.nextId + htmlNodeCount (View.render v s₂) < UInt32.size)
    (hdep : htmlDepth (View.render v s₂) ≤ ep.f) (hcl : CleanDomSubtree ep.f ep.childNs h₁ a Sold node) (hcl₂ : (View.render v s₂).DomClean = true) :
    PatchViewPost ep v s₂ pre suf Sold a ((patchHtmlSubtreeM (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) node h₁ (View.render v s₂) >>= fun n => pure (mk n)).run a) := by
  have ⟨hext, h4, h5, h6, h7, h8⟩ := patchHtmlSubtreeM_spec ep h₁ (View.render v s₂) node pre suf Sold a ps hbound hdep hcl hcl₂
  dsimp only [PatchViewPost, StateT.run]; rw [ArenaM.bind_eq, ArenaM.pure_eq]; dsimp only [VStateValid]; rw [hroot]
  exact ⟨hext, h4, h5, h6, ⟨h7, hmt ..⟩, h8⟩

private theorem patchViewKidsM_spec_of (kids : List (View σ msg)) (s₁ s₂ : σ) (hView : ∀ k ∈ kids, ∀ pre suf Sold a vst, PatchViewGoal ep k s₁ s₂ pre suf Sold a vst) :
    ∀ targetsDone preC sufC kstates Sdone Srem a, ParentListCtx ep (preC ++ sufC) Srem a → View.DomCleanEach kids → htmlListDepth (View.renderEach kids s₂) ≤ ep.f →
      a.nextId + htmlListNodeCount (View.renderEach kids s₂) < UInt32.size → (preC ++ sufC).Nodup →
      (∀ k, Sdone k → k ≠ ep.parent.toNat ∧ k < a.nextId) → CleanDomChildren ep.f ep.childNs targetsDone a Sdone preC →
      (∀ k, Sdone k → Srem k → False) → (∀ r ∈ sufC, r.toNat < a.nextId ∧ r ≠ ep.parent) → CleanDomChildren ep.f ep.childNs (View.renderEach kids s₁) a Srem sufC → VStateKidsMatches kids s₁ a sufC kstates →
      let (ks', aOut) := (patchViewKidsM (m := ArenaM msg) ep.parent (UInt32.ofNat preC.length) kids s₂ kstates).run a
      ∃ Snew, let domCs' := ks'.map VState.rootNode
        ArenaExt a aOut (fun k => k = ep.parent.toNat ∨ Srem k) (htmlListNodeCount (View.renderEach kids s₂)) ∧ aOut.get ep.parent = ep.entry (preC ++ domCs') ∧ (preC ++ domCs').Nodup ∧
        (∀ k, Snew k → (Sdone k ∨ Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ ep.parent.toNat) ∧ CleanDomChildren ep.f ep.childNs (targetsDone ++ View.renderEach kids s₂) aOut Snew (preC ++ domCs') ∧ VStateKidsMatches kids s₂ aOut domCs' ks' := by
  induction kids with
  | nil => intro _ _ sufC kstates Sdone _ _ plc _ _ _ hnd hSdone hDone _ _ hCl hVk
           cases sufC with | cons _ _ => exact False.elim hCl | nil => cases kstates with | cons _ _ => exact False.elim hVk | nil =>
           exact ⟨Sdone, ArenaExt.refl, plc.hpar, hnd, fun k hk => ⟨.inl hk, (hSdone k hk).1⟩, by rw [View.renderEach, List.map_nil, List.append_nil, List.append_nil]; exact hDone, trivial⟩
  | cons k rest ih =>
      intro targetsDone preC sufC kstates Sdone Srem a plc ⟨hkCl, hrestCl⟩ hdep hbound hnd hSdone hDone hDisj hsufB hCl hVk
      cases sufC with | nil => exact False.elim hCl | cons _ sufRest => cases kstates with | nil => exact False.elim hVk | cons kst restSt =>
      rcases hCl with ⟨Sc, Srest, hSc, hSr, hDSr, hcCl, hSufCl⟩; rcases hVk with ⟨rfl, hkMatch, hRestMatch⟩; simp only [View.renderEach, htmlListDepth, htmlListNodeCount] at hdep hbound ⊢
      have hparNodes : ∀ r ∈ preC ++ kst.rootNode :: sufRest, r.toNat < a.nextId := fun r hr => (List.mem_append.1 hr).elim (fun hp => (hSdone _ (CleanDomChildren_mem hDone r hp)).2) fun hc => (hsufB r hc).1
      have hpreLen : preC.length + 1 + sufRest.length < UInt32.size := by have := nodup_nodes_lt_length_le a.nextId (preC ++ kst.rootNode :: sufRest) hnd hparNodes; simp only [List.length_append, List.length_cons] at this; omega
      have ⟨haMidExt, hparMid, hndMid, _, hValK', _⟩ := hView k (.head _) preC sufRest Sc a kst
        ⟨plc.hchildNs, hpreLen, plc.hparLt, plc.hposId, plc.hpar, hnd, fun h => (plc.hSrem _ (hSc _ h)).1 rfl, fun x hx => (plc.hSrem x (hSc x hx)).2, hparNodes⟩
        hkCl (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right _ _) _) hbound) (Nat.le_trans (Nat.le_max_left ..) hdep) ⟨hcCl, hkMatch⟩
      let rK := patchViewM (m := ArenaM msg) ep.parent (UInt32.ofNat preC.length) k s₂ kst a; let kst' := rK.1; let aMid := rK.2
      have ⟨hSdone', hDone'⟩ := clean_done_extend haMidExt.next_ge plc.hparLt hSdone (fun x h => plc.hSrem x (hSc x h)) (fun x h1 h2 => hDisj x h1 (hSc x h2))
        (fun m hm => haMidExt.frame m (hSdone _ hm).2 fun h => h.elim (hSdone _ hm).1 fun hsc => hDisj _ hm (hSc _ hsc)) hDone hValK'.1
      have hfrSuf : ∀ m : Dom.Node, Srest m.toNat → aMid.get m = a.get m := fun m hm => haMidExt.frame m (plc.hSrem _ (hSr _ hm)).2 fun h => h.elim (plc.hSrem _ (hSr _ hm)).1 fun hsc => hDSr _ hsc hm
      have huNext : UInt32.ofNat preC.length + 1 = UInt32.ofNat (preC ++ [kst'.rootNode]).length := by simp only [List.length_append, List.length_singleton]; exact uint32_ofNat_succ preC.length (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hpreLen)
      have ⟨Snew, hextR, hparR, hndR, hSnew, hCleanR, hVstR⟩ := ih (fun x hx => hView x (.tail _ hx)) (targetsDone ++ [View.render k s₂]) (preC ++ [kst'.rootNode]) sufRest restSt _ Srest aMid
        ⟨plc.hchildNs, haMidExt.lt plc.hparLt, haMidExt.lt plc.hposId, by rw [List.append_assoc, List.singleton_append]; exact hparMid, fun x hx => let hb := plc.hSrem x (hSr x hx); ⟨hb.1, haMidExt.lt hb.2⟩⟩
        hrestCl (Nat.le_trans (Nat.le_max_right ..) hdep) (haMidExt.bound_sub hbound) (by rw [List.append_assoc, List.singleton_append]; exact hndMid) hSdone' hDone'
        (fun x h1 h2 => not_Sdone_extend (fun h => hDisj x h (hSr x h2)) (fun hsc => hDSr x hsc h2) (plc.hSrem x (hSr x h2)).2 h1)
        (fun r hr => let hb := hsufB r (.tail _ hr); ⟨haMidExt.lt hb.1, hb.2⟩) (CleanDomChildren_frame hfrSuf hSufCl) (VStateKidsMatches_frame hfrSuf hSufCl hRestMatch)
      dsimp only [patchViewKidsM, StateT.run]; simp only [ArenaM.bind_eq, ArenaM.pure_eq, huNext]; rw [List.append_assoc, List.singleton_append] at hparR hndR hCleanR; rw [List.append_assoc, List.singleton_append] at hCleanR
      exact ⟨Snew, haMidExt.trans hextR (fun _ h => h.imp id (hSc _)) (fun _ _ h => h.imp id (hSr _)) (Nat.le_refl _), hparR, hndR, clean_step_Snew_compose haMidExt.next_ge hextR.next_ge hSc hSr hSnew, hCleanR, rfl,
        VStateMatches_frame (fun m hm => hextR.frame m (hSdone' m.toNat (.inr hm)).2 fun h => h.elim (hSdone' m.toNat (.inr hm)).1 fun hr => hm.elim (fun hs => hDSr _ hs hr) fun hlo => Nat.not_lt.2 hlo.1 (plc.hSrem _ (hSr _ hr)).2) hValK'.1 hValK'.2, hVstR⟩

private theorem patchViewM_ifElse_spec (cond : σ → Bool) (yes no : View σ msg) (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg)
    (ihY : ∀ inner, PatchViewGoal ep yes s₁ s₂ pre suf Sold a inner) (ihN : ∀ inner, PatchViewGoal ep no s₁ s₂ pre suf Sold a inner) :
    PatchViewGoal ep (.ifElse cond yes no) s₁ s₂ pre suf Sold a vst := by
  intro ps hclean hbound hdep hval
  cases vst with
  | cond wasYes inner =>
    rcases hval with ⟨hcl, hwy, hin⟩; let targetV := if cond s₂ then yes else no
    have hren : View.render (.ifElse cond yes no) s₂ = View.render targetV s₂ := by dsimp only [targetV, View.render]; cases cond s₂ <;> rfl
    dsimp only [patchViewM, StateT.run]
    by_cases hsame : cond s₂ = wasYes
    · simp only [beq_iff_eq.2 hsame, ↓reduceIte]; have hc₁ : cond s₁ = cond s₂ := hwy.symm.trans hsame.symm
      cases hc₂ : cond s₂ <;> (
        simp only [hc₁, hc₂, Bool.false_eq_true, ↓reduceIte, View.render] at hbound hdep hcl hin ⊢
        have hih : PatchViewPost ep targetV s₂ pre suf Sold a ((patchViewM (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) targetV s₂ inner).run a) := by
          simp only [targetV, hc₂, Bool.false_eq_true, ↓reduceIte]; first | exact ihN inner ps hclean.2 hbound hdep ⟨hcl, hin⟩ | exact ihY inner ps hclean.1 hbound hdep ⟨hcl, hin⟩
        rcases hih with ⟨hext, h4, h5, h6, ⟨hcl', hm'⟩, heqv'⟩
        dsimp only [PatchViewPost, VStateValid, View.render]; simp only [targetV, hc₂, Bool.false_eq_true, ↓reduceIte] at hext h4 h5 h6 hcl' hm' heqv' ⊢
        rw [ArenaM.bind_eq, ArenaM.pure_eq]; exact ⟨hext, h4, h5, h6, ⟨hcl', hc₂.symm, by rw [hc₂]; exact hm'⟩, heqv'⟩)
    · simp only [beq_eq_false_iff_ne.2 hsame, Bool.false_eq_true, ↓reduceIte]
      have hns : MonadDom.childNamespace (m := ArenaM msg) ep.parent a = (ep.childNs, a) := (ArenaM.childNamespace_elem ps.hpar).trans (by rw [← ps.hchildNs])
      have ⟨hn2Root, haMidGe, haMidBound, haMidFr, hVstMid, _⟩ := buildViewM_vstate_spec ep.childNs targetV s₂ a ep.f (by dsimp only [targetV]; cases cond s₂; exact hclean.2; exact hclean.1) ps.hpos (hren ▸ hbound) (hren ▸ hdep)
      let rB := buildViewM (m := ArenaM msg) ep.childNs targetV s₂ a; let n2 := rB.1.1; let newInner := rB.1.2; let aMid := rB.2; let a' := aMid.set ep.parent (ep.entry (pre ++ n2 :: suf))
      have hVst' : VStateValid ep.f ep.childNs targetV s₂ a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) newInner := VStateValid_mono (fun _ => .inr) (hVstMid.frame_set_ne fun h => Nat.not_lt.2 h.1 ps.hparLt)
      have hVstIf : VStateValid ep.f ep.childNs (.ifElse cond yes no) s₂ a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) (.cond (cond s₂) newInner) :=
        ⟨hren.symm ▸ hVst'.1, rfl, by cases hc₂ : cond s₂ <;> (simp only [targetV, hc₂, ↓reduceIte, Bool.false_eq_true] at hVst' ⊢; exact hVst'.2)⟩
      have hrep : MonadDom.replaceChild (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) n2 aMid = ((), a') := by
        simp only [MonadDom.replaceChild, DomArena.modifyChildren, DomArena.modify, show aMid.get ep.parent = ep.entry (pre ++ inner.rootNode :: suf) from (haMidFr ep.parent ps.hparLt).trans ps.hpar, ElemPar.entry, uint32_toNat_ofNat_lt pre.length (by have := ps.hpreLen; omega), listReplaceAt_append_middle, a']
      suffices hPost : PatchViewPost ep (.ifElse cond yes no) s₂ pre suf Sold a (.cond (cond s₂) newInner, a') by
        rw [stateM_bind_step hns]; cases hc₂ : cond s₂ <;> (simp only [hc₂, Bool.false_eq_true, ↓reduceIte] at hPost ⊢; dsimp only [rB, n2, newInner, aMid, targetV] at hrep hPost ⊢; simp only [hc₂, Bool.false_eq_true, ↓reduceIte] at hrep hPost; rw [ArenaM.bind_eq, stateM_bind_step hrep, ArenaM.pure_eq]; exact hPost)
      exact ⟨⟨haMidGe, hren.symm ▸ haMidBound, fun m hmLt hn => (aMid.get_set_ne _ (node_ne_of_toNat_ne fun h => hn (.inl h))).trans (haMidFr m hmLt)⟩,
        by dsimp only [VState.rootNode]; rw [hn2Root]; exact DomArena.get_set_self .., by dsimp only [VState.rootNode]; rw [hn2Root]; exact nodup_append_replace ps.hnd (.inr fun hm => Nat.not_lt.2 (hn2Root ▸ VStateValid_root_mem hVstMid).1 (ps.hparNodes n2 hm)),
        fun r hr => (List.mem_append.1 hr).elim (fun hp => Nat.lt_of_lt_of_le (ps.hparNodes r (List.mem_append_left _ hp)) haMidGe) fun hc => (List.mem_cons.1 hc).elim (· ▸ (VStateValid_root_mem hVstMid).2) fun htl => Nat.lt_of_lt_of_le (ps.hparNodes r (List.mem_append_right _ (.tail _ htl))) haMidGe,
        hVstIf, VStateValid_equiv hVstIf⟩
  | _ => exact False.elim hval.2

private theorem patchViewM_element_spec (tag : String) (attrs : List (VAttr σ msg)) (kids : List (View σ msg)) (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg)
    (ihk : ∀ k ∈ kids, ∀ ep' pre' suf' Sold' a' vst', PatchViewGoal ep' k s₁ s₂ pre' suf' Sold' a' vst') :
    PatchViewGoal ep (.element tag attrs kids) s₁ s₂ pre suf Sold a vst := by
  intro ps hclean hbound hdep hval
  cases vst with
  | elem node kstates =>
    dsimp only [VStateValid, VState.rootNode] at ps hval; rcases hval with ⟨hcl, _, _, _, st, mg, domCs, hgetM, hksM⟩
    cases hf : ep.f with | zero => rw [hf] at hcl; exact False.elim hcl | succ f' =>
    rw [hf] at hcl hdep; rcases hcl with ⟨hnodeMem, _, _, _, _, _, hnodeGet, hElClean, hElEq, hmg, hCleanCs⟩; rw [hgetM] at hnodeGet; cases hnodeGet
    rcases applyDynAttrsM_elem_ext hgetM hclean.1 ⟨hElClean, hElEq, hmg⟩ with ⟨ha1Ext, ha1Next, ha1Ne, st', mg', ha1Get, hElClean', hElEq', hmg'⟩
    let a1 := (applyDynAttrsM (m := ArenaM msg) node attrs s₂ a).2; have ha1N : a1.nextId = a.nextId := ha1Next; simp only [View.render, htmlNodeCount, htmlDepth] at hbound hdep
    let epC : ElemPar msg := ⟨f', Dom.childNsOf ep.childNs tag, node, if ep.childNs == "" && tag == "svg" then Dom.svgNs else ep.childNs, tag, st', mg'⟩
    have ⟨Snew, hextOut, hnodeOut, _, hSnew, hCleanOut, hVstOut⟩ := patchViewKidsM_spec_of epC kids s₁ s₂ (fun k hk => ihk k hk epC) [] [] domCs kstates (fun _ => False) (fun k => Sold k ∧ k ≠ node.toNat) a1
      ⟨(ep.childNsOk_child ps.hchildNs tag).symm, ha1N ▸ ps.hSoldLt _ hnodeMem, ha1N ▸ ps.hpos, ha1Get, fun k hk => ⟨hk.2, ha1N ▸ ps.hSoldLt k hk.1⟩⟩
      hclean.2 (Nat.le_of_add_le_add_left (a := 1) (Nat.add_comm f' 1 ▸ hdep)) (ha1N ▸ Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left _ 1) _) hbound)
      (CleanDomChildren_nodup hCleanCs).1 (fun _ h => h.elim) trivial (fun _ h => h.elim)
      (fun r hr => let hb := CleanDomChildren_mem hCleanCs r hr; ⟨ha1N ▸ ps.hSoldLt _ hb.1, node_ne_of_toNat_ne hb.2⟩)
      (CleanDomChildren_frame (fun m hm => ha1Ne m (node_ne_of_toNat_ne hm.2)) hCleanCs) (VStateKidsMatches_frame (fun m hm => ha1Ne m (node_ne_of_toNat_ne hm.2)) hCleanCs hksM)
    dsimp only [patchViewM, StateT.run]; rw [stateM_bind_step (show applyDynAttrsM (m := ArenaM msg) node attrs s₂ a = ((), a1) from rfl), ArenaM.bind_eq, ArenaM.pure_eq]
    have hextSold : ArenaExt a _ Sold (htmlNodeCount (View.render (.element tag attrs kids) s₂)) := ha1Ext.trans hextOut (fun _ h => h ▸ hnodeMem) (fun _ _ h => h.elim (· ▸ hnodeMem) (·.1)) (by simp only [View.render, htmlNodeCount]; omega)
    have hvalOut' : VStateValid (f' + 1) ep.childNs (.element tag attrs kids) s₂ _ (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < _)) (.elem node _) :=
      ⟨⟨.inl hnodeMem, hclean.1.1 s₂, hclean.1.2.1 s₂, st', mg', _, hnodeOut, hElClean', hElEq', hmg',
        CleanDomChildren_mono (fun k hk => ⟨(hSnew k hk).1.elim False.elim fun h => h.elim (fun hs => .inl hs.1) fun ha => .inr ⟨ha1N ▸ ha.1, ha.2⟩, (hSnew k hk).2⟩) hCleanOut⟩, rfl, _, tag, st', mg', _, hnodeOut, hVstOut⟩
    have hvalOut : VStateValid ep.f ep.childNs (.element tag attrs kids) s₂ _ (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < _)) (.elem node _) := hf ▸ hvalOut'
    exact ⟨hextSold.mono (fun _ => .inr) (Nat.le_refl _), (hextSold.frame ep.parent ps.hparLt ps.hparOut).trans ps.hpar, ps.hnd, fun r hr => hextSold.lt (ps.hparNodes r hr), hvalOut, VStateValid_equiv hvalOut⟩
  | _ => exact False.elim hval.2
end

theorem patchViewM_spec {σ msg : Type} (ep : ElemPar msg) (v : View σ msg) (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg)
    (ps : ParentSlot ep vst.rootNode pre suf Sold a) (hclean : View.DomClean v)
    (hbound : a.nextId + htmlNodeCount (View.render v s₂) < UInt32.size) (hdep : htmlDepth (View.render v s₂) ≤ ep.f) (hval : VStateValid ep.f ep.childNs v s₁ a Sold vst) :
    PatchViewPost ep v s₂ pre suf Sold a ((patchViewM (m := StateM (DomArena msg)) ep.parent (UInt32.ofNat pre.length) v s₂ vst).run a) := by
  induction v using View.ind generalizing ep pre suf Sold a vst with
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      exact patchViewM_keyedList_spec ep tag attrs keys marks rowSig rowEv rowsHtml tmpl? s₁ s₂ pre suf Sold a vst ps hclean hbound hdep hval
  | text _ => cases vst with | text _ => exact noop_post ep ps (VStateValid_mono (fun _ => .inl) hval) | _ => exact False.elim hval.2
  | static _ => cases vst with | stat _ => exact noop_post ep ps (VStateValid_mono (fun _ => .inl) hval) | _ => exact False.elim hval.2
  | dyn get =>
      cases vst with
      | dyn node _ =>
        rcases hval with ⟨hcl, _, rfl⟩; cases hf : ep.f with | zero => rw [hf] at hcl; exact False.elim hcl | succ f' =>
        rw [hf] at hcl; rcases hcl with ⟨hmem, hget⟩; dsimp only [VState.rootNode] at hmem hget ps; dsimp only [patchViewM, StateT.run]
        by_cases heq : get s₂ = get s₁
        · simp only [show (get s₂ != get s₁) = false by simp only [bne, beq_iff_eq.2 heq, Bool.not_true], Bool.false_eq_true, ↓reduceIte, ArenaM.pure_eq]
          exact noop_post ep ps (hf ▸ ⟨⟨.inl hmem, heq.symm ▸ hget⟩, rfl, rfl⟩)
        · simp only [show (get s₂ != get s₁) = true by simp only [bne, beq_eq_false_iff_ne.2 heq, Bool.not_false], ↓reduceIte, ArenaM.bind_eq, ArenaM.pure_eq, MonadDom.setText, DomArena.modify]; rw [hget]
          have hval' : VStateValid ep.f ep.childNs (.dyn get) s₂ (a.set node (.text (get s₂))) (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a.nextId)) (.dyn node (get s₂)) := hf ▸ ⟨⟨.inl hmem, DomArena.get_set_self ..⟩, rfl, rfl⟩
          exact ⟨(ArenaExt.of_set (.inr hmem)).mono (fun _ h => h) (Nat.zero_le _), (a.get_set_ne _ fun h : ep.parent = node => ps.hparOut (h ▸ hmem)).trans ps.hpar, ps.hnd, ps.hparNodes, hval', VStateValid_equiv hval'⟩
      | _ => exact False.elim hval.2
  | dynNode get =>
      cases vst with | dynNode node _ => rcases hval with ⟨hcl, _, rfl⟩; exact patchHtml_post ep (fun n => .dynNode n (get s₂)) (fun _ => rfl) (fun _ _ => ⟨rfl, rfl⟩) ps hbound hdep hcl (hclean s₂) | _ => exact False.elim hval.2
  | memo sm =>
      cases vst with
      | memo node _ _ =>
        rcases hval with ⟨hcl, _, rfl, rfl⟩; dsimp only [patchViewM]
        by_cases hkey : sm.keyOf s₂ = sm.keyOf s₁
        · have heval := sm.sound s₂ s₁ hkey; simp only [beq_iff_eq.2 hkey, ↓reduceIte, StateT.run, ArenaM.pure_eq]
          exact noop_post ep ps ⟨by rw [View.render, heval]; exact CleanDomSubtree_mono (fun _ => .inl) hcl, rfl, hkey.symm, heval.symm⟩
        · simp only [beq_eq_false_iff_ne.2 hkey, Bool.false_eq_true, ↓reduceIte]
          exact patchHtml_post ep (fun n => .memo n (sm.keyOf s₂) (sm.eval s₂)) (fun _ => rfl) (fun _ _ => ⟨rfl, rfl, rfl⟩) ps hbound hdep hcl (hclean s₂)
      | _ => exact False.elim hval.2
  | ifElse cond yes no ihy ihn => exact patchViewM_ifElse_spec ep cond yes no s₁ s₂ pre suf Sold a vst (fun inner => ihy ep pre suf Sold a inner) (fun inner => ihn ep pre suf Sold a inner) ps hclean hbound hdep hval
  | element tag attrs kids ihk => exact patchViewM_element_spec ep tag attrs kids s₁ s₂ pre suf Sold a vst (fun k hk ep' pre' suf' Sold' a' vst' => ihk k hk ep' pre' suf' Sold' a' vst') ps hclean hbound hdep hval

theorem patchViewKidsM_spec {σ msg : Type} (ep : ElemPar msg) (kids : List (View σ msg)) (targetsDone : List (Html msg)) (preC sufC : List Dom.Node) (kstates : List (VState σ msg)) (s₁ s₂ : σ) (Sdone Srem : Nat → Prop) (a : DomArena msg)
    (plc : ParentListCtx ep (preC ++ sufC) Srem a) (hclean : View.DomCleanEach kids) (hdep : htmlListDepth (View.renderEach kids s₂) ≤ ep.f)
    (hbound : a.nextId + htmlListNodeCount (View.renderEach kids s₂) < UInt32.size) (hnd : (preC ++ sufC).Nodup)
    (hSdone : ∀ k, Sdone k → k ≠ ep.parent.toNat ∧ k < a.nextId) (hDone : CleanDomChildren ep.f ep.childNs targetsDone a Sdone preC)
    (hDisj : ∀ k, Sdone k → Srem k → False) (hsufB : ∀ r ∈ sufC, r.toNat < a.nextId ∧ r ≠ ep.parent)
    (hCl : CleanDomChildren ep.f ep.childNs (View.renderEach kids s₁) a Srem sufC) (hVk : VStateKidsMatches kids s₁ a sufC kstates) :
    let (ks', aOut) := (patchViewKidsM (m := StateM (DomArena msg)) ep.parent (UInt32.ofNat preC.length) kids s₂ kstates).run a
    ∃ Snew, let domCs' := ks'.map VState.rootNode
      ArenaExt a aOut (fun k => k = ep.parent.toNat ∨ Srem k) (htmlListNodeCount (View.renderEach kids s₂)) ∧ aOut.get ep.parent = ep.entry (preC ++ domCs') ∧ (preC ++ domCs').Nodup ∧
      (∀ k, Snew k → (Sdone k ∨ Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ ep.parent.toNat) ∧
      CleanDomChildren ep.f ep.childNs (targetsDone ++ View.renderEach kids s₂) aOut Snew (preC ++ domCs') ∧ VStateKidsMatches kids s₂ aOut domCs' ks' :=
  patchViewKidsM_spec_of ep kids s₁ s₂ (fun k _ pre' suf' Sold' a' vst' => patchViewM_spec ep k s₁ s₂ pre' suf' Sold' a' vst')
    targetsDone preC sufC kstates Sdone Srem a plc hclean hdep hbound hnd hSdone hDone hDisj hsufB hCl hVk

end Qed
