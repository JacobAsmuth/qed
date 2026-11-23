import Qed.Proofs.ViewPatch.VState

namespace Qed

section
variable {σ msg : Type}
private abbrev ArenaM (msg : Type) := StateM (DomArena msg)

private theorem buildViewKidsM_eq_buildDomListM_of (ns : String) (parent : Dom.Node) (s : σ) :
    ∀ (ks : List (View σ msg)), (∀ k ∈ ks, ∀ a, View.DomClean k → let r := (buildViewM (m := ArenaM msg) ns k s).run a; let d := (buildDomM (m := ArenaM msg) ns (View.render k s)).run a; r.1.1 = d.1 ∧ r.2.SameDom d.2) →
      ∀ a, View.DomCleanEach ks → ((buildViewKidsM (m := ArenaM msg) ns parent ks s).run a).2.SameDom ((buildDomListM (m := ArenaM msg) ns parent (View.renderEach ks s)).run a).2
  | [], _, _, _ => .refl _
  | k :: rest, hV, a, ⟨hk, hrest⟩ => by
      dsimp only [buildViewKidsM, buildDomListM, View.renderEach, StateT.run, bind, StateT.bind, pure, StateT.pure]
      rcases hbv : buildViewM (m := ArenaM msg) ns k s a with ⟨pk, a1⟩; rcases hbd : buildDomM (m := ArenaM msg) ns (View.render k s) a with ⟨dn, ad⟩
      dsimp only; have ⟨h1, h2⟩ : pk.1 = dn ∧ a1.SameDom ad := by simpa [StateT.run, hbv, hbd] using hV k (.head _) a hk
      rw [h1]; rcases ha1 : MonadDom.appendChild (m := ArenaM msg) parent dn a1 with ⟨_, s1⟩; rcases ha2 : MonadDom.appendChild (m := ArenaM msg) parent dn ad with ⟨_, s2⟩
      exact (buildViewKidsM_eq_buildDomListM_of ns parent s rest (fun x hx => hV x (.tail _ hx)) s1 hrest).trans
        (buildDomListM_sameDom ns parent (View.renderEach rest s) (by simpa [ha1, ha2] using (DomArena.MetaIndep.appendChild parent dn).sameDom h2))

theorem buildViewM_eq_buildDomM (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (hcl : View.DomClean v) :
    let r := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
    let d := (buildDomM (m := StateM (DomArena msg)) ns (View.render v s)).run a
    r.1.1 = d.1 ∧ r.2.SameDom d.2 := by
  induction v using View.ind generalizing ns a with
  | text _ | dyn _ | static _ | dynNode _ | memo _ => exact ⟨rfl, .refl _⟩
  | ifElse c y no ihy ihn =>
      cases hc : c s <;> (
        simp only [buildViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure, hc, Bool.false_eq_true, ↓reduceIte]
        rcases hyR : buildViewM (m := ArenaM msg) ns _ s a with ⟨_, _⟩; first | simpa [StateT.run, hyR] using ihn ns a hcl.2 | simpa [StateT.run, hyR] using ihy ns a hcl.1)
  | element tag attrs kids ihk =>
      dsimp only [buildViewM, buildDomM, MonadDom.createElement, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
      rcases a.alloc _ with ⟨node, a1⟩; rcases applyAttrsM (m := ArenaM msg) node _ a1 with ⟨_, a2⟩; simp only [hcl.1.1 s, Bool.not_false, ↓reduceIte, bind, StateT.bind, pure, StateT.pure]
      rcases hbk : buildViewKidsM (m := ArenaM msg) (Dom.childNsOf ns tag) node kids s a2 with ⟨_, _⟩; rcases hbd : buildDomListM (m := ArenaM msg) (Dom.childNsOf ns tag) node (View.renderEach kids s) a2 with ⟨_, _⟩
      exact ⟨rfl, by simpa [StateT.run, hbk, hbd] using buildViewKidsM_eq_buildDomListM_of (Dom.childNsOf ns tag) node s kids (fun k hk a' => ihk k hk _ a') a2 hcl.2⟩
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      cases tmpl? with | some _ => exact False.elim hcl | none =>
      dsimp only [buildViewM, buildDomM, MonadDom.createElement, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
      rcases a.alloc _ with ⟨node, a1⟩; rcases applyAttrsM (m := ArenaM msg) node _ a1 with ⟨_, a2⟩; simp only [hcl.1.1 s, Bool.not_false, ↓reduceIte, bind, StateT.bind, pure, StateT.pure]
      rcases hsRun : seedRowsM (m := ArenaM msg) s!"§{node}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a2 with ⟨_, a3⟩
      have hseed := seedRowsM_sameDom s!"§{node}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a2
      dsimp only [StateT.run] at hseed ⊢; rw [hsRun] at hseed; rw [Html.map_prefixSignals_of_DomCleanList _ (hcl.2.2.1 s)]
      rcases hbl1 : buildDomListM (m := ArenaM msg) (Dom.childNsOf ns tag) node (rowsHtml s) a3 with ⟨_, _⟩; rcases hbl2 : buildDomListM (m := ArenaM msg) (Dom.childNsOf ns tag) node (rowsHtml s) a2 with ⟨_, _⟩
      exact ⟨rfl, by simpa [hbl1, hbl2] using buildDomListM_sameDom (Dom.childNsOf ns tag) node (rowsHtml s) hseed⟩

private theorem buildViewM_dom_spec (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (fuel : Nat)
    (hcl : View.DomClean v) (hpos : 0 < a.nextId) (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ fuel) :
    let ((root, _), a') := (buildViewM (m := ArenaM msg) ns v s).run a
    a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧ ArenaExt a a' (fun _ => False) (htmlNodeCount (View.render v s)) ∧
    CleanDomSubtree fuel ns (View.render v s) a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root := by
  have heq := buildViewM_eq_buildDomM ns v s a hcl; have hdom := buildDomM_spec_full ns (View.render v s) a fuel hpos hbound hdep
  dsimp only [StateT.run] at heq hdom ⊢; rcases hbv : buildViewM (m := ArenaM msg) ns v s a with ⟨⟨_, _⟩, _⟩; rcases hbd : buildDomM (m := ArenaM msg) ns (View.render v s) a with ⟨_, _⟩
  rw [hbv] at heq; rw [hbd] at heq hdom; rcases heq with ⟨rfl, hsd⟩; rcases hdom with ⟨hge, hlt, hext, _, _, hclFn⟩
  exact ⟨hge, hsd.1 ▸ hlt, hext.sameDom hsd, CleanDomSubtree_frame (fun m _ => hsd.get_eq m) (hsd.1 ▸ hclFn (View.DomClean_render hcl s))⟩

private abbrev BuildMatches (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (f : Nat) : Prop :=
  View.DomClean v → 0 < a.nextId → a.nextId + htmlNodeCount (View.render v s) < UInt32.size → htmlDepth (View.render v s) ≤ f →
  let ((root, vst), a') := (buildViewM (m := ArenaM msg) ns v s).run a; vst.rootNode = root ∧ VStateMatches v s a' root vst

private theorem buildViewKidsM_matches (childNs : String) (parent : Dom.Node) (s : σ) (f : Nat) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) :
    ∀ (ks : List (View σ msg)), (∀ k ∈ ks, ∀ a, BuildMatches childNs k s a f) →
      ∀ (a : DomArena msg) (acc : List Dom.Node), View.DomCleanEach ks → parent.toNat < a.nextId → 0 < a.nextId →
        a.nextId + htmlListNodeCount (View.renderEach ks s) < UInt32.size → htmlListDepth (View.renderEach ks s) ≤ f →
        (∀ c ∈ acc, c.toNat < a.nextId) → a.get parent = .element pns ptag pst pmg acc →
        let (ksts, aOut) := (buildViewKidsM (m := ArenaM msg) childNs parent ks s).run a
        ∃ csNew, aOut.get parent = .element pns ptag pst pmg (acc ++ csNew) ∧
          (∀ m : Dom.Node, m ≠ parent → m.toNat < a.nextId → aOut.get m = a.get m) ∧ VStateKidsMatches ks s aOut csNew ksts
  | [], _, _, _, _, _, _, _, _, _, hpar => ⟨[], by simpa using hpar, fun _ _ _ => rfl, trivial⟩
  | k :: rest, hV, a, acc, ⟨hkCl, hrestCl⟩, hparLt, hpos, hbound, hdep, haccLt, hpar => by
      simp only [View.renderEach, htmlListNodeCount, htmlListDepth] at hbound hdep
      have hkM := hV k (.head _) a hkCl hpos (by omega) (Nat.le_trans (Nat.le_max_left ..) hdep)
      have hkD := buildViewM_dom_spec childNs k s a f hkCl hpos (by omega) (Nat.le_trans (Nat.le_max_left ..) hdep)
      dsimp only [StateT.run, buildViewKidsM, bind, StateT.bind, pure, StateT.pure] at hkM hkD ⊢
      rcases hbK : buildViewM (m := ArenaM msg) childNs k s a with ⟨⟨kn, kst⟩, aMid⟩
      rw [hbK] at hkM hkD; rcases hkD with ⟨hknGe, hknLt, haMidExt, hkClean⟩
      let aAfter := aMid.set parent (.element pns ptag pst pmg (acc ++ [kn]))
      dsimp only; rw [show MonadDom.appendChild (m := ArenaM msg) parent kn aMid = ((), aAfter) by
            cases hkG : aMid.get kn with
            | fragment fcs => exact False.elim (CleanDomSubtree_not_fragment hkClean fcs hkG)
            | _ => simp only [MonadDom.appendChild, hkG, DomArena.modifyChildren, DomArena.modify, (haMidExt.frame parent hparLt id).trans hpar, List.erase_of_not_mem (fun hm => by have := haccLt kn hm; omega), aAfter]]
      dsimp only
      have hih := buildViewKidsM_matches childNs parent s f pns ptag pst pmg rest (fun x hx => hV x (.tail _ hx)) aAfter (acc ++ [kn]) hrestCl
        (Nat.lt_of_lt_of_le hparLt haMidExt.next_ge) (Nat.lt_of_lt_of_le hpos haMidExt.next_ge) (by have := haMidExt.next_le; dsimp only [aAfter, DomArena.set]; omega)
        (Nat.le_trans (Nat.le_max_right ..) hdep) (fun c hc => (List.mem_append.1 hc).elim (fun h1 => Nat.lt_of_lt_of_le (haccLt c h1) haMidExt.next_ge) (fun h2 => (List.mem_singleton.1 h2) ▸ hknLt)) (DomArena.get_set_self ..)
      dsimp only [StateT.run] at hih; rcases hbR : buildViewKidsM (m := ArenaM msg) childNs parent rest s aAfter with ⟨_, _⟩
      rw [hbR] at hih; rcases hih with ⟨csRest, hparOut, hfrRest, hvkRest⟩; rw [List.append_assoc, List.singleton_append] at hparOut
      exact ⟨kn :: csRest, hparOut, fun m hmn hm => (hfrRest m hmn (Nat.lt_of_lt_of_le hm haMidExt.next_ge)).trans ((DomArena.get_set_ne _ _ hmn).trans (haMidExt.frame m hm id)),
        hkM.1.symm, VStateMatches_frame (fun m hm => (hfrRest m (node_ne_of_toNat_ne (by omega)) hm.2).trans (DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega)))) hkClean hkM.2, hvkRest⟩

private theorem buildViewM_matches (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (fuel : Nat) : BuildMatches ns v s a fuel := by
  intro hcl hpos hbound hdep
  induction v using View.ind generalizing ns a fuel with
  | text _ | static _ => exact ⟨rfl, rfl⟩ | dyn _ | dynNode _ => exact ⟨rfl, rfl, rfl⟩ | memo _ => exact ⟨rfl, rfl, rfl, rfl⟩
  | ifElse c y no ihy ihn =>
      cases hc : c s <;> (
        simp only [buildViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure, hc, Bool.false_eq_true, ↓reduceIte] at hbound hdep ⊢
        have ih := by first | exact ihn ns a fuel hcl.2 hpos hbound hdep | exact ihy ns a fuel hcl.1 hpos hbound hdep
        dsimp only [StateT.run] at ih; rcases hb : buildViewM (m := ArenaM msg) ns _ s a with ⟨⟨_, _⟩, _⟩; rw [hb] at ih; exact ⟨ih.1, hc.symm, by simp [hc, ih.2]⟩)
  | element tag attrs kids ihk =>
      cases fuel with | zero => simp only [View.render, htmlDepth] at hdep; omega | succ f =>
      simp only [View.render, htmlNodeCount, htmlDepth] at hbound hdep
      let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns; let node := UInt32.ofNat a.nextId; let a1 : DomArena msg := { a with nextId := a.nextId + 1 }
      let st := evalSpecAttrs (attrs.map (VAttr.eval s)); let mg := (normalizeAttrs (attrs.map (VAttr.eval s))).filterMap managedAttrName
      have hnodeNat : node.toNat = a.nextId := uint32_toNat_ofNat_lt a.nextId (by omega)
      have hkids := buildViewKidsM_matches (Dom.childNsOf ns tag) node s f realNs tag st mg kids (fun k hk a' => ihk k hk _ a' f)
        (a1.set node (.element realNs tag st mg [])) [] hcl.2 (by dsimp only [a1, DomArena.set]; omega) (by dsimp only [a1, DomArena.set]; omega)
        (by dsimp only [a1, DomArena.set]; omega) (by omega) (fun _ h => nomatch h) (DomArena.get_set_self ..)
      dsimp only [buildViewM, MonadDom.createElement, DomArena.alloc, StateT.run, bind, StateT.bind, pure, StateT.pure] at hkids ⊢
      rw [show ({ a with nextId := a.nextId + 1, store := fun m => if (m == node) = true then ArenaEntry.element realNs tag {} [] [] else a.store m } : DomArena msg) = a1.set node (.element realNs tag {} [] []) from rfl,
          applyAttrsM_fresh_element a1 node realNs tag [] (attrs.map (VAttr.eval s))]
      dsimp only; rcases hbk : buildViewKidsM (m := ArenaM msg) (Dom.childNsOf ns tag) node kids s (a1.set node (.element realNs tag st mg [])) with ⟨_, _⟩
      rw [hbk] at hkids; rcases hkids with ⟨csNew, hparOut, _, hvk⟩; exact ⟨rfl, rfl, realNs, tag, st, mg, csNew, by simpa using hparOut, hvk⟩
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      cases tmpl? with | some _ => exact False.elim hcl | none =>
      dsimp only [buildViewM, MonadDom.createElement, StateT.run, bind, StateT.bind, pure, StateT.pure]
      split; rename_i heq; split at heq; split at heq; split at heq; cases heq; exact ⟨rfl, rfl, rfl, Html.map_prefixSignals_of_DomCleanList _ (hcl.2.2.1 s)⟩

theorem buildViewM_vstate_spec (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (fuel : Nat) (hclean : View.DomClean v)
    (hpos : 0 < a.nextId) (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ fuel) :
    let ((root, vst), a') := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
    vst.rootNode = root ∧ a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
    (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
    VStateValid fuel ns v s a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) vst ∧ DomTreeAssocEquiv (readDomTree fuel a' vst.rootNode) (specDom ns (View.render v s)) := by
  have hdom := buildViewM_dom_spec ns v s a fuel hclean hpos hbound hdep; have hmt := buildViewM_matches ns v s a fuel hclean hpos hbound hdep
  dsimp only [StateT.run] at hdom hmt ⊢; rcases hbv : buildViewM (m := ArenaM msg) ns v s a with ⟨⟨_, vst⟩, a'⟩; rw [hbv] at hdom hmt; rcases hdom with ⟨_, _, hext, hcl⟩
  have hval : VStateValid fuel ns v s a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) vst := ⟨hmt.1.symm ▸ hcl, hmt.1.symm ▸ hmt.2⟩
  exact ⟨hmt.1, hext.next_ge, hext.next_le, fun m hm => hext.frame m hm id, hval, VStateValid_equiv hval⟩

end
end Qed
