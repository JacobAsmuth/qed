import Qed.Proofs.ViewPatch.VState

namespace Qed

section
variable {σ msg : Type}

private theorem buildViewKidsM_eq_buildDomListM_of (ns : String) (parent : Dom.Node) (s : σ) :
    ∀ (ks : List (View σ msg)), (∀ k ∈ ks, ∀ a, View.DomClean k → let r := (buildViewM (m := ArenaM msg) ns k s).run a; let d := (buildDomM (m := ArenaM msg) ns (View.render k s)).run a; r.1.1 = d.1 ∧ r.2.SameDom d.2) →
      ∀ a, View.DomCleanEach ks → ((buildViewKidsM (m := ArenaM msg) ns parent ks s).run a).2.SameDom ((buildDomListM (m := ArenaM msg) ns parent (View.renderEach ks s)).run a).2
  | [], _, _, _ => .refl _
  | k :: rest, hV, a, ⟨hk, hrest⟩ => by
      have ⟨h1, h2⟩ := hV k (.head _) a hk; dsimp only [buildViewKidsM, buildDomListM, View.renderEach, StateT.run] at h1 ⊢; simp only [ArenaM.bind_eq, ArenaM.pure_eq]; rw [h1]
      exact (buildViewKidsM_eq_buildDomListM_of ns parent s rest (fun x hx => hV x (.tail _ hx)) _ hrest).trans (buildDomListM_sameDom ns parent (View.renderEach rest s) ((DomArena.MetaIndep.appendChild parent _).sameDom h2))

theorem buildViewM_eq_buildDomM (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (hcl : View.DomClean v) :
    let r := (buildViewM (m := StateM (DomArena msg)) ns v s).run a; let d := (buildDomM (m := StateM (DomArena msg)) ns (View.render v s)).run a; r.1.1 = d.1 ∧ r.2.SameDom d.2 := by
  induction v using View.ind generalizing ns a with
  | text _ | dyn _ | static _ | dynNode _ | memo _ => exact ⟨rfl, .refl _⟩
  | ifElse c y no ihy ihn => cases hc : c s <;> (simp only [buildViewM, View.render, StateT.run, ArenaM.bind_eq, ArenaM.pure_eq, hc, Bool.false_eq_true, ↓reduceIte]; first | exact ihn ns a hcl.2 | exact ihy ns a hcl.1)
  | element tag attrs kids ihk =>
      dsimp only [buildViewM, buildDomM, MonadDom.createElement, View.render, StateT.run]; simp only [ArenaM.bind_eq, ArenaM.pure_eq, hcl.1.1 s, Bool.not_false, ↓reduceIte]
      exact ⟨trivial, buildViewKidsM_eq_buildDomListM_of (Dom.childNsOf ns tag) _ s kids (fun k hk a' => ihk k hk _ a') _ hcl.2⟩
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      cases tmpl? with | some _ => exact False.elim hcl | none =>
      dsimp only [buildViewM, buildDomM, MonadDom.createElement, View.render, StateT.run]; simp only [ArenaM.bind_eq, ArenaM.pure_eq, hcl.1.1 s, Bool.not_false, ↓reduceIte]
      rw [Html.map_prefixSignals_of_DomCleanList _ (hcl.2.2.1 s)]; exact ⟨trivial, buildDomListM_sameDom (Dom.childNsOf ns tag) _ (rowsHtml s) (seedRowsM_sameDom ..)⟩

private abbrev BuildMatches (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (f : Nat) : Prop :=
  View.DomClean v → 0 < a.nextId → a.nextId + htmlNodeCount (View.render v s) < UInt32.size → htmlDepth (View.render v s) ≤ f →
  let ((root, vst), a') := (buildViewM (m := ArenaM msg) ns v s).run a; vst.rootNode = root ∧ VStateMatches v s a' root vst

private theorem buildViewKidsM_matches (ep : ElemPar msg) (s : σ) :
    ∀ (ks : List (View σ msg)), (∀ k ∈ ks, ∀ a, BuildMatches ep.childNs k s a ep.f) →
      ∀ (a : DomArena msg) (acc : List Dom.Node), View.DomCleanEach ks → ep.parent.toNat < a.nextId → 0 < a.nextId →
        a.nextId + htmlListNodeCount (View.renderEach ks s) < UInt32.size → htmlListDepth (View.renderEach ks s) ≤ ep.f →
        (∀ c ∈ acc, c.toNat < a.nextId) → a.get ep.parent = ep.entry acc →
        let (ksts, aOut) := (buildViewKidsM (m := ArenaM msg) ep.childNs ep.parent ks s).run a
        ∃ csNew, aOut.get ep.parent = ep.entry (acc ++ csNew) ∧ (∀ m : Dom.Node, m ≠ ep.parent → m.toNat < a.nextId → aOut.get m = a.get m) ∧ VStateKidsMatches ks s aOut csNew ksts
  | [], _, _, _, _, _, _, _, _, _, hpar => ⟨[], by simpa only [List.append_nil] using hpar, fun _ _ _ => rfl, trivial⟩
  | k :: rest, hV, a, acc, ⟨hkCl, hrestCl⟩, hparLt, hpos, hbound, hdep, haccLt, hpar => by
      simp only [View.renderEach, htmlListNodeCount, htmlListDepth] at hbound hdep
      have hkM := hV k (.head _) a hkCl hpos (by omega) (Nat.le_trans (Nat.le_max_left ..) hdep)
      have ⟨hroot, hsd⟩ := buildViewM_eq_buildDomM ep.childNs k s a hkCl
      have ⟨_, _, haMidExt0, _, _, hkClFn⟩ := buildDomM_spec_full ep.childNs (View.render k s) a ep.f hpos (by omega) (Nat.le_trans (Nat.le_max_left ..) hdep)
      have haMidExt := haMidExt0.sameDom hsd; have hkClean := hroot ▸ CleanDomSubtree_frame (fun m _ => hsd.get_eq m) (hsd.1 ▸ hkClFn (View.DomClean_render hkCl s))
      have ⟨hknGe, hknLt⟩ := CleanDomSubtree_root_mem hkClean
      let r := buildViewM (m := ArenaM msg) ep.childNs k s a; let kn := r.1.1; let aMid := r.2; let aAfter := aMid.set ep.parent (ep.entry (acc ++ [kn]))
      have hparMid : aMid.get ep.parent = ep.entry acc := (haMidExt.frame_lt hparLt).trans hpar
      have happ : MonadDom.appendChild (m := ArenaM msg) ep.parent kn aMid = ((), aAfter) := by
        cases hkG : aMid.get kn with
        | fragment fcs => exact False.elim (CleanDomSubtree_not_fragment hkClean fcs hkG)
        | _ => simp only [MonadDom.appendChild, hkG, DomArena.modifyChildren, DomArena.modify, hparMid, ElemPar.entry, List.erase_of_not_mem (fun hm => Nat.not_lt.2 hknGe (haccLt kn hm)), aAfter]
      have ⟨csRest, hparOut, hfrRest, hvkRest⟩ := buildViewKidsM_matches ep s rest (fun x hx => hV x (.tail _ hx)) aAfter (acc ++ [kn]) hrestCl
        (haMidExt.lt hparLt) (haMidExt.lt hpos) (haMidExt.bound_sub hbound) (Nat.le_trans (Nat.le_max_right ..) hdep)
        (fun c hc => (List.mem_append.1 hc).elim (fun h1 => haMidExt.lt (haccLt c h1)) (fun h2 => List.mem_singleton.1 h2 ▸ hknLt)) (DomArena.get_set_self ..)
      dsimp only [buildViewKidsM, StateT.run]; rw [ArenaM.bind_eq, stateM_bind_step happ, ArenaM.bind_eq, ArenaM.pure_eq]; rw [List.append_assoc, List.singleton_append] at hparOut
      exact ⟨kn :: csRest, hparOut, fun m hmn hm => (hfrRest m hmn (haMidExt.lt hm)).trans ((DomArena.get_set_ne _ _ hmn).trans (haMidExt.frame_lt hm)),
        hkM.1.symm, VStateMatches_frame (fun m hm => (hfrRest m (node_ne_of_toNat_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hparLt hm.1))) hm.2).trans (aMid.get_set_ne_of_gt _ (Nat.lt_of_lt_of_le hparLt hm.1))) hkClean hkM.2, hvkRest⟩

private theorem buildViewM_matches (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (fuel : Nat) : BuildMatches ns v s a fuel := by
  intro hcl hpos hbound hdep; induction v using View.ind generalizing ns a fuel with
  | text _ | static _ => exact ⟨rfl, rfl⟩ | dyn _ | dynNode _ => exact ⟨rfl, rfl, rfl⟩ | memo _ => exact ⟨rfl, rfl, rfl, rfl⟩
  | ifElse c y no ihy ihn =>
      cases hc : c s <;> (
        simp only [buildViewM, View.render, StateT.run, ArenaM.bind_eq, ArenaM.pure_eq, hc, Bool.false_eq_true, ↓reduceIte] at hbound hdep ⊢
        have ih := by first | exact ihn ns a fuel hcl.2 hpos hbound hdep | exact ihy ns a fuel hcl.1 hpos hbound hdep
        exact ⟨ih.1, hc.symm, by simp only [hc, Bool.false_eq_true, ↓reduceIte, ih.2]⟩)
  | element tag attrs kids ihk =>
      cases fuel with | zero => simp only [View.render, htmlDepth] at hdep; omega | succ f =>
      simp only [View.render, htmlNodeCount, htmlDepth] at hbound hdep
      let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns; let node := UInt32.ofNat a.nextId; let a1 : DomArena msg := { a with nextId := a.nextId + 1 }
      let st := evalSpecAttrs (attrs.map (VAttr.eval s)); let mg := (normalizeAttrs (attrs.map (VAttr.eval s))).filterMap managedAttrName
      have hnodeNat : node.toNat = a.nextId := uint32_toNat_ofNat_lt a.nextId (by omega)
      have ⟨csNew, hparOut, _, hvk⟩ := buildViewKidsM_matches ⟨f, Dom.childNsOf ns tag, node, realNs, tag, st, mg⟩ s kids (fun k hk a' => ihk k hk _ a' f)
        (a1.set node (.element realNs tag st mg [])) [] hcl.2 (by dsimp only [a1, DomArena.set]; omega) (by dsimp only [a1, DomArena.set]; omega) (by dsimp only [a1, DomArena.set]; omega) (by dsimp only; omega) (fun _ h => nomatch h) (DomArena.get_set_self ..)
      dsimp only [buildViewM, MonadDom.createElement, StateT.run] at hparOut hvk ⊢; simp only [ArenaM.bind_eq, ArenaM.pure_eq]
      rw [DomArena.alloc_eq]; dsimp only; rw [applyAttrsM_fresh_element a1 node realNs tag [] (attrs.map (VAttr.eval s))]
      exact ⟨rfl, rfl, realNs, tag, st, mg, csNew, by simpa only [List.nil_append] using hparOut, hvk⟩
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      cases tmpl? with | some _ => exact False.elim hcl | none =>
      dsimp only [buildViewM, MonadDom.createElement, StateT.run]; simp only [ArenaM.bind_eq, ArenaM.pure_eq]; exact ⟨rfl, rfl, rfl, Html.map_prefixSignals_of_DomCleanList _ (hcl.2.2.1 s)⟩

theorem buildViewM_vstate_spec (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (fuel : Nat) (hclean : View.DomClean v)
    (hpos : 0 < a.nextId) (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ fuel) :
    let ((root, vst), a') := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
    vst.rootNode = root ∧ a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
    (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
    VStateValid fuel ns v s a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) vst ∧ DomTreeAssocEquiv (readDomTree fuel a' vst.rootNode) (specDom ns (View.render v s)) :=
  have ⟨hroot, hsd⟩ := buildViewM_eq_buildDomM ns v s a hclean
  have ⟨_, _, hext, _, _, hclFn⟩ := buildDomM_spec_full ns (View.render v s) a fuel hpos hbound hdep
  have hmt := buildViewM_matches ns v s a fuel hclean hpos hbound hdep
  have hext' := hext.sameDom hsd
  have hval := VStateValid.of_sameDom hsd (hsd.1 ▸ hclFn (View.DomClean_render hclean s)) (hmt.1.trans hroot) (hroot ▸ hmt.2)
  ⟨hmt.1, hext'.next_ge, hext'.next_le, fun _ hm => hext'.frame_lt hm, hval, VStateValid_equiv hval⟩

end
end Qed
