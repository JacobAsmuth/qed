import Qed.Proofs.ViewPatch.VState

namespace Qed

private theorem buildViewKidsM_eq_buildDomListM_of {σ msg : Type} (ns : String) (parent : Dom.Node)
    (ks : List (View σ msg)) (s : σ)
    (hView : ∀ k ∈ ks, ∀ (a : DomArena msg), View.DomClean k →
      let r := (buildViewM (m := StateM (DomArena msg)) ns k s).run a
      let d := (buildDomM (m := StateM (DomArena msg)) ns (View.render k s)).run a
      r.1.1 = d.1 ∧ r.2.SameDom d.2) :
    ∀ (a : DomArena msg), View.DomCleanEach ks →
      ((buildViewKidsM (m := StateM (DomArena msg)) ns parent ks s).run a).2.SameDom
        ((buildDomListM (m := StateM (DomArena msg)) ns parent (View.renderEach ks s)).run a).2 := by
  induction ks with
  | nil => intro _ _; exact .refl _
  | cons k rest ih =>
      intro a ⟨hkCl, hrestCl⟩
      have hk := hView k (.head _) a hkCl
      dsimp only [buildViewKidsM, buildDomListM, View.renderEach, StateT.run, bind, StateT.bind, pure, StateT.pure] at hk ⊢
      cases hbv : buildViewM (m := StateM (DomArena msg)) ns k s a with
      | mk pk a1 =>
          cases hbd : buildDomM (m := StateM (DomArena msg)) ns (View.render k s) a with
          | mk dn ad =>
              rw [hbv, hbd] at hk; dsimp only at hk ⊢
              rw [hk.1]
              have happ : ∀ (x y : DomArena msg), x.SameDom y →
                  (MonadDom.appendChild (m := StateM (DomArena msg)) parent dn x).2.SameDom
                    (MonadDom.appendChild (m := StateM (DomArena msg)) parent dn y).2 := by
                intro x y ⟨h1, h2⟩
                cases x; cases y; cases h1; cases h2
                dsimp only [MonadDom.appendChild, DomArena.get, DomArena.set, DomArena.modifyChildren, DomArena.modify]
                split <;> exact ⟨rfl, rfl⟩
              have haEq := happ a1 ad hk.2
              cases ha1 : MonadDom.appendChild (m := StateM (DomArena msg)) parent dn a1 with
              | mk _ s1 =>
                  cases ha2 : MonadDom.appendChild (m := StateM (DomArena msg)) parent dn ad with
                  | mk _ s2 =>
                      rw [ha1, ha2] at haEq; dsimp only at haEq
                      have hrest1 := ih (fun x hx => hView x (.tail _ hx)) s1 hrestCl
                      have hrest2 := buildDomListM_sameDom ns parent (View.renderEach rest s) haEq
                      dsimp only [StateT.run] at hrest1
                      exact hrest1.trans hrest2

theorem buildViewM_eq_buildDomM {σ msg : Type} (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg)
    (hcl : View.DomClean v) :
    let r := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
    let d := (buildDomM (m := StateM (DomArena msg)) ns (View.render v s)).run a
    r.1.1 = d.1 ∧ r.2.SameDom d.2 := by
  induction v using View.ind generalizing ns a with
  | text _ | dyn _ | static _ | dynNode _ | memo _ => exact ⟨rfl, .refl _⟩
  | ifElse c y no ihy ihn =>
      rcases hcl with ⟨hy, hn⟩
      cases hc : c s <;>
        simp only [buildViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure, hc, Bool.false_eq_true, ↓reduceIte]
      · have ih := ihn ns a hn; dsimp only [StateT.run] at ih
        cases hyR : buildViewM (m := StateM (DomArena msg)) ns no s a with | mk _ _ => rw [hyR] at ih; exact ih
      · have ih := ihy ns a hy; dsimp only [StateT.run] at ih
        cases hyR : buildViewM (m := StateM (DomArena msg)) ns y s a with | mk _ _ => rw [hyR] at ih; exact ih
  | element tag attrs kids ihk =>
      rcases hcl with ⟨ha, hks⟩
      dsimp only [buildViewM, buildDomM, MonadDom.createElement, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
      cases hce : a.alloc (ArenaEntry.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag {} [] []) with
      | mk node a1 =>
          dsimp only
          cases ha1 : applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s)) a1 with
          | mk _ a2 =>
              dsimp only
              simp only [ha.1 s, Bool.not_false, ↓reduceIte, bind, StateT.bind, pure, StateT.pure]
              have hkids := buildViewKidsM_eq_buildDomListM_of (Dom.childNsOf ns tag) node kids s
                (fun k hk a' hkCl => ihk k hk (Dom.childNsOf ns tag) a' hkCl) a2 hks
              dsimp only [StateT.run] at hkids
              cases hbk : buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s a2 with
              | mk _ _ =>
                  cases hbd : buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node (View.renderEach kids s) a2 with
                  | mk _ _ => dsimp only; rw [hbk, hbd] at hkids; exact ⟨rfl, hkids⟩
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      cases tmpl? with
      | some _ => exact False.elim hcl
      | none =>
          rcases hcl with ⟨ha, hrows⟩
          dsimp only [buildViewM, buildDomM, MonadDom.createElement, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
          cases hce : a.alloc (ArenaEntry.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag {} [] []) with
          | mk node a1 =>
              dsimp only
              cases ha1 : applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s)) a1 with
              | mk _ a2 =>
                  dsimp only
                  simp only [ha.1 s, Bool.not_false, ↓reduceIte, bind, StateT.bind, pure, StateT.pure]
                  have hseed := seedRowsM_sameDom s!"§{node}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a2
                  dsimp only [StateT.run] at hseed
                  cases hsRun : seedRowsM (m := StateM (DomArena msg)) s!"§{node}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a2 with
                  | mk _ a3 =>
                      rw [hsRun] at hseed; dsimp only at hseed ⊢
                      rw [Html.map_prefixSignals_of_DomCleanList s!"§{node}§" (hrows.2.1 s)]
                      have hb := buildDomListM_sameDom (Dom.childNsOf ns tag) node (rowsHtml s) hseed
                      cases hbl1 : buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node (rowsHtml s) a3 with
                      | mk _ _ =>
                          cases hbl2 : buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node (rowsHtml s) a2 with
                          | mk _ _ => dsimp only; rw [hbl1, hbl2] at hb; exact ⟨rfl, hb⟩

theorem buildViewKidsM_eq_buildDomListM {σ msg : Type} (ns : String) (parent : Dom.Node)
    (ks : List (View σ msg)) (s : σ) (a : DomArena msg) (hcl : View.DomCleanEach ks) :
    ((buildViewKidsM (m := StateM (DomArena msg)) ns parent ks s).run a).2.SameDom
      ((buildDomListM (m := StateM (DomArena msg)) ns parent (View.renderEach ks s)).run a).2 :=
  buildViewKidsM_eq_buildDomListM_of ns parent ks s (fun k _ a' hkCl => buildViewM_eq_buildDomM ns k s a' hkCl) a hcl

private theorem buildViewKidsM_matches {σ msg : Type} (childNs : String) (parent : Dom.Node)
    (ks : List (View σ msg)) (s : σ) (f : Nat)
    (hView : ∀ k ∈ ks, ∀ (a : DomArena msg), View.DomClean k → 0 < a.nextId →
      a.nextId + htmlNodeCount (View.render k s) < UInt32.size → htmlDepth (View.render k s) ≤ f →
      let ((root, vst), a') := (buildViewM (m := StateM (DomArena msg)) childNs k s).run a
      vst.rootNode = root ∧ VStateMatches k s a' root vst) :
    ∀ (aBase : DomArena msg) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (acc : List Dom.Node),
      View.DomCleanEach ks → parent.toNat < aBase.nextId → 0 < aBase.nextId →
      aBase.nextId + htmlListNodeCount (View.renderEach ks s) < UInt32.size →
      htmlListDepth (View.renderEach ks s) ≤ f → (∀ c ∈ acc, c.toNat < aBase.nextId) →
      let aIn := aBase.set parent (.element pns ptag pst pmg acc)
      let (ksts, aOut) := (buildViewKidsM (m := StateM (DomArena msg)) childNs parent ks s).run aIn
      ∃ csNew, aOut.get parent = .element pns ptag pst pmg (acc ++ csNew) ∧
        VStateKidsMatches ks s aOut csNew ksts := by
  induction ks with
  | nil =>
      intro aBase pns ptag pst pmg acc _ _ _ _ _ _
      exact ⟨[], by simp, trivial⟩
  | cons k rest ih =>
      intro aBase pns ptag pst pmg acc ⟨hkCl, hrestCl⟩ hparLt hpos hbound hdep haccLt
      simp only [View.renderEach, htmlListNodeCount] at hbound; simp only [View.renderEach, htmlListDepth] at hdep
      have hkDep : htmlDepth (View.render k s) ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
      have hrestDep : htmlListDepth (View.renderEach rest s) ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
      let aIn := aBase.set parent (.element pns ptag pst pmg acc)
      have haInNext : aIn.nextId = aBase.nextId := rfl
      have hkMatch := hView k (.head _) aIn hkCl hpos (by omega) hkDep
      have hkEq := buildViewM_eq_buildDomM childNs k s aIn hkCl
      have hkDom := buildDomM_spec_full childNs (View.render k s) aIn f hpos (by omega) hkDep
      dsimp only [StateT.run] at hkMatch hkEq hkDom
      cases hbK : buildViewM (m := StateM (DomArena msg)) childNs k s aIn with
      | mk p1 aMid =>
          rcases p1 with ⟨kn, kst⟩
          cases hbd : buildDomM (m := StateM (DomArena msg)) childNs (View.render k s) aIn with
          | mk dn ad =>
              rw [hbK] at hkMatch hkEq; rw [hbd] at hkEq hkDom; dsimp only at hkMatch hkEq hkDom
              rcases hkEq with ⟨rfl, hsd⟩
              rcases hkDom with ⟨hknGe, hknLt, haMidExt, _, _, hkClFn⟩
              have haMidExt' := haMidExt.sameDom hsd
              have hkClean : CleanDomSubtree f childNs (View.render k s) aMid (fun c => aBase.nextId ≤ c ∧ c < aMid.nextId) kn :=
                CleanDomSubtree_frame (fun m _ => hsd.get_eq m) (hsd.1 ▸ hkClFn (View.DomClean_render hkCl s))
              have hknGe' : aBase.nextId ≤ kn.toNat := hknGe
              have hknLt' : kn.toNat < aMid.nextId := hsd.1 ▸ hknLt
              have hparMid : aMid.get parent = .element pns ptag pst pmg acc := by
                rw [haMidExt'.frame parent hparLt id]; exact DomArena.get_set_self ..
              have hknNotIn : kn ∉ acc := fun hm => by have := haccLt kn hm; omega
              let aAfter := aMid.set parent (.element pns ptag pst pmg (acc ++ [kn]))
              have happRun : MonadDom.appendChild (m := StateM (DomArena msg)) parent kn aMid = ((), aAfter) := by
                cases hkG : aMid.get kn with
                | fragment fcs => exact False.elim (CleanDomSubtree_not_fragment hkClean fcs hkG)
                | null | text _ | element _ _ _ _ _ =>
                    simp only [MonadDom.appendChild, hkG, DomArena.modifyChildren, DomArena.modify, hparMid, List.erase_of_not_mem hknNotIn, aAfter]
              have haccLt' : ∀ c ∈ acc ++ [kn], c.toNat < aMid.nextId := fun c hc => by
                rcases List.mem_append.1 hc with h1 | h2
                · exact Nat.lt_of_lt_of_le (haccLt c h1) haMidExt'.next_ge
                · rw [List.mem_singleton] at h2; subst h2; exact hknLt'
              have hih := ih (fun x hx => hView x (.tail _ hx)) aMid pns ptag pst pmg (acc ++ [kn]) hrestCl
                (Nat.lt_of_lt_of_le hparLt haMidExt'.next_ge) (by have := haMidExt'.next_ge; omega)
                (by have := haMidExt'.next_le; omega) hrestDep haccLt'
              have hrestEq := buildViewKidsM_eq_buildDomListM childNs parent rest s aAfter hrestCl
              have hrestDom := buildDomListM_spec_full childNs (View.renderEach rest s) aMid parent
                (ArenaEntry.element pns ptag pst pmg) (.inl ⟨pns, ptag, pst, pmg, fun _ => rfl⟩)
                (acc ++ [kn]) f (Nat.lt_of_lt_of_le hparLt haMidExt'.next_ge) (by have := haMidExt'.next_ge; omega)
                (by have := haMidExt'.next_le; omega) hrestDep haccLt'
              dsimp only [StateT.run] at hih hrestEq hrestDom ⊢
              dsimp only [buildViewKidsM, bind, StateT.bind, pure, StateT.pure]
              rw [hbK]; dsimp only; rw [happRun]; dsimp only
              cases hbR : buildViewKidsM (m := StateM (DomArena msg)) childNs parent rest s aAfter with
              | mk restKsts aOut =>
                  rw [hbR] at hih hrestEq; dsimp only at hih hrestEq
                  rcases hih with ⟨csRest, hparOut, hvkRest⟩
                  rcases hrestDom with ⟨_, _, _, hrestExt, _, _, _⟩
                  have hrestExt' := hrestExt.sameDom hrestEq
                  have hkMatchOut : VStateMatches k s aOut kn kst :=
                    VStateMatches_frame (fun m hm => hrestExt'.frame m hm.2 (by omega)) hkClean hkMatch.2
                  rw [List.append_assoc, List.singleton_append] at hparOut
                  exact ⟨kn :: csRest, hparOut, hkMatch.1.symm, hkMatchOut, hvkRest⟩

private theorem buildViewM_matches {σ msg : Type} (ns : String) (v : View σ msg) (s : σ)
    (a : DomArena msg) (fuel : Nat) (hcl : View.DomClean v) (hpos : 0 < a.nextId)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ fuel) :
    let ((root, vst), a') := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
    vst.rootNode = root ∧ VStateMatches v s a' root vst := by
  induction v using View.ind generalizing ns a fuel with
  | text _ | static _ => exact ⟨rfl, rfl⟩
  | dyn _ | dynNode _ => exact ⟨rfl, rfl, rfl⟩
  | memo _ => exact ⟨rfl, rfl, rfl, rfl⟩
  | ifElse c y no ihy ihn =>
      rcases hcl with ⟨hy, hn⟩
      cases hc : c s <;>
        (simp only [buildViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure, hc, Bool.false_eq_true, ↓reduceIte] at hbound hdep ⊢
         have ih := by first | exact ihn ns a fuel hn hpos hbound hdep | exact ihy ns a fuel hy hpos hbound hdep
         dsimp only [StateT.run] at ih
         cases hb : buildViewM (m := StateM (DomArena msg)) ns _ s a with
         | mk p a' => rcases p with ⟨r, inner⟩; rw [hb] at ih; exact ⟨ih.1, hc.symm, by simp [hc, ih.2]⟩)
  | element tag attrs kids ihk =>
      rcases hcl with ⟨haClean, hkidsClean⟩
      cases fuel with
      | zero => simp only [View.render, htmlDepth] at hdep; omega
      | succ f =>
          simp only [View.render, htmlNodeCount] at hbound; simp only [View.render, htmlDepth] at hdep
          let node := UInt32.ofNat a.nextId
          have hnodeNat : node.toNat = a.nextId := uint32_toNat_ofNat_lt a.nextId (by omega)
          let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
          let st := evalSpecAttrs (attrs.map (VAttr.eval s))
          let mg := (normalizeAttrs (attrs.map (VAttr.eval s))).filterMap managedAttrName
          let a1 : DomArena msg := { a with nextId := a.nextId + 1 }
          have hkids := buildViewKidsM_matches (Dom.childNsOf ns tag) node kids s f
            (fun k hk a' hkCl hpos' hbd' hdp' => ihk k hk (Dom.childNsOf ns tag) a' f hkCl hpos' hbd' hdp')
            a1 realNs tag st mg [] hkidsClean (by dsimp only [a1]; omega) (by dsimp only [a1]; omega)
            (by dsimp only [a1]; omega) (by omega) (fun _ h => nomatch h)
          dsimp only [buildViewM, MonadDom.createElement, DomArena.alloc, StateT.run, bind, StateT.bind, pure, StateT.pure] at hkids ⊢
          change (match applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s)) (a1.set node (.element realNs tag {} [] [])) with
                  | (_, s0) => match buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s s0 with
                    | (ks, s1) => (VState.elem node ks).rootNode = node ∧ VStateMatches (.element tag attrs kids) s s1 node (.elem node ks))
          rw [applyAttrsM_fresh_element a1 node realNs tag [] (attrs.map (VAttr.eval s))]
          dsimp only
          cases hbk : buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s (a1.set node (.element realNs tag st mg [])) with
          | mk ksts aOut =>
              rw [hbk] at hkids; rcases hkids with ⟨csNew, hparOut, hvk⟩
              rw [List.nil_append] at hparOut
              exact ⟨rfl, rfl, realNs, tag, st, mg, csNew, hparOut, hvk⟩
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      cases tmpl? with
      | some _ => exact False.elim hcl
      | none =>
          rcases hcl with ⟨_, hrows⟩
          dsimp only [buildViewM, MonadDom.createElement, StateT.run, bind, StateT.bind, pure, StateT.pure]
          cases a.alloc (ArenaEntry.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag {} [] []) with
          | mk node a1 =>
              dsimp only
              cases applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s)) a1 with
              | mk _ a2 =>
                  dsimp only
                  cases seedRowsM (m := StateM (DomArena msg)) s!"§{node}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a2 with
                  | mk perRow a3 =>
                      dsimp only
                      cases buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node ((rowsHtml s).map (Html.prefixSignals s!"§{node}§")) a3 with
                      | mk _ _ =>
                          exact ⟨rfl, rfl, rfl, Html.map_prefixSignals_of_DomCleanList _ (hrows.2.1 s)⟩

theorem buildViewM_vstate_spec {σ msg : Type} (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (fuel : Nat)
    (hclean : View.DomClean v) (hpos : 0 < a.nextId)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ fuel) :
    let ((root, vst), a') := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
    vst.rootNode = root ∧ a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
    (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
    VStateValid fuel ns v s a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) vst ∧
    DomTreeAssocEquiv (readDomTree fuel a' vst.rootNode) (specDom ns (View.render v s)) := by
  have heq := buildViewM_eq_buildDomM ns v s a hclean
  have hdom := buildDomM_spec_full ns (View.render v s) a fuel hpos hbound hdep
  have hmt := buildViewM_matches ns v s a fuel hclean hpos hbound hdep
  dsimp only [StateT.run] at heq hdom hmt ⊢
  cases hbv : buildViewM (m := StateM (DomArena msg)) ns v s a with
  | mk p a' =>
      rcases p with ⟨root, vst⟩
      cases hbd : buildDomM (m := StateM (DomArena msg)) ns (View.render v s) a with
      | mk droot aDom =>
          rw [hbv] at heq hmt; rw [hbd] at heq hdom; dsimp only at heq hdom hmt ⊢
          rcases heq with ⟨rfl, hsd⟩
          rcases hdom with ⟨_, _, hext, _, _, hclFn⟩
          have hext' := hext.sameDom hsd
          have hcl : CleanDomSubtree fuel ns (View.render v s) a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root :=
            CleanDomSubtree_frame (fun m _ => hsd.get_eq m) (hsd.1 ▸ hclFn (View.DomClean_render hclean s))
          have hval : VStateValid fuel ns v s a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) vst :=
            ⟨hmt.1.symm ▸ hcl, hmt.1.symm ▸ hmt.2⟩
          exact ⟨hmt.1, hext'.next_ge, hext'.next_le, fun m hm => hext'.frame m hm id, hval, VStateValid_equiv hval⟩


end Qed
