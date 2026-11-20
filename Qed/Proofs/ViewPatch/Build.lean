import Qed.Proofs.ViewPatch.VState

namespace Qed

private theorem view_sizeOf_pos {σ msg : Type} (v : View σ msg) : 0 < sizeOf v := by
  cases v <;> simp only [View.text.sizeOf_spec, View.dyn.sizeOf_spec, View.static.sizeOf_spec,
    View.dynNode.sizeOf_spec, View.memo.sizeOf_spec, View.ifElse.sizeOf_spec,
    View.element.sizeOf_spec, View.keyedList.sizeOf_spec] <;> omega

private theorem view_sizeOf_ifElse_left {σ msg : Type} (c : σ → Bool) (y n : View σ msg) :
    sizeOf y < sizeOf (View.ifElse c y n) := by
  simp only [View.ifElse.sizeOf_spec]; omega

private theorem view_sizeOf_ifElse_right {σ msg : Type} (c : σ → Bool) (y n : View σ msg) :
    sizeOf n < sizeOf (View.ifElse c y n) := by
  simp only [View.ifElse.sizeOf_spec]; omega

private theorem view_sizeOf_element_mem {σ msg : Type} {tag : String} {attrs : List (VAttr σ msg)}
    {ks : List (View σ msg)} {k : View σ msg} (hk : k ∈ ks) :
    sizeOf k < sizeOf (View.element tag attrs ks) := by
  have h1 : sizeOf k < sizeOf ks := List.sizeOf_lt_of_mem hk
  simp only [View.element.sizeOf_spec]; omega

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

private theorem buildViewM_eq_buildDomM_aux {σ msg : Type} :
    ∀ (n : Nat) (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg),
      sizeOf v ≤ n → View.DomClean v →
      let r := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
      let d := (buildDomM (m := StateM (DomArena msg)) ns (View.render v s)).run a
      r.1.1 = d.1 ∧ r.2.SameDom d.2
  | 0, _, v, _, _, hsz, _ => absurd (Nat.lt_of_lt_of_le (view_sizeOf_pos v) hsz) (Nat.lt_irrefl 0)
  | _ + 1, _, .text _, _, _, _, _ | _ + 1, _, .dyn _, _, _, _, _ | _ + 1, _, .static _, _, _, _, _
  | _ + 1, _, .dynNode _, _, _, _, _ | _ + 1, _, .memo _, _, _, _, _ => ⟨rfl, .refl _⟩
  | n + 1, ns, .ifElse c y no, s, a, hsz, ⟨hy, hn⟩ => by
      cases hc : c s <;>
        simp only [buildViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure, hc, Bool.false_eq_true, ↓reduceIte]
      · have ih := buildViewM_eq_buildDomM_aux n ns no s a
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (view_sizeOf_ifElse_right c y no) hsz)) hn
        dsimp only [StateT.run] at ih
        cases hyR : buildViewM (m := StateM (DomArena msg)) ns no s a with
        | mk _ _ => rw [hyR] at ih; exact ih
      · have ih := buildViewM_eq_buildDomM_aux n ns y s a
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (view_sizeOf_ifElse_left c y no) hsz)) hy
        dsimp only [StateT.run] at ih
        cases hyR : buildViewM (m := StateM (DomArena msg)) ns y s a with
        | mk _ _ => rw [hyR] at ih; exact ih
  | n + 1, ns, .element tag attrs kids, s, a, hsz, ⟨ha, hks⟩ => by
      dsimp only [buildViewM, buildDomM, MonadDom.createElement, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
      cases hce : a.alloc (ArenaEntry.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag {} [] []) with
      | mk node a1 =>
          dsimp only
          cases ha1 : applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s)) a1 with
          | mk _ a2 =>
              dsimp only
              simp only [ha.1 s, Bool.not_false, ↓reduceIte, bind, StateT.bind, pure, StateT.pure]
              have hkids := buildViewKidsM_eq_buildDomListM_of (Dom.childNsOf ns tag) node kids s
                (fun k hk a' hkCl => buildViewM_eq_buildDomM_aux n (Dom.childNsOf ns tag) k s a'
                  (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (view_sizeOf_element_mem hk) hsz)) hkCl) a2 hks
              dsimp only [StateT.run] at hkids
              cases hbk : buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s a2 with
              | mk _ _ =>
                  cases hbd : buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node (View.renderEach kids s) a2 with
                  | mk _ _ => dsimp only; rw [hbk, hbd] at hkids; exact ⟨rfl, hkids⟩
  | _ + 1, _, .keyedList _ _ _ _ _ _ _ (some _), _, _, _, h => False.elim h
  | _ + 1, ns, .keyedList tag attrs keys marks rowSig rowEv rowsHtml none, s, a, _, ⟨ha, hrows⟩ => by
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

theorem buildViewM_eq_buildDomM {σ msg : Type} (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg)
    (hcl : View.DomClean v) :
    let r := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
    let d := (buildDomM (m := StateM (DomArena msg)) ns (View.render v s)).run a
    r.1.1 = d.1 ∧ r.2.SameDom d.2 :=
  buildViewM_eq_buildDomM_aux (sizeOf v) ns v s a (Nat.le_refl _) hcl

theorem buildViewKidsM_eq_buildDomListM {σ msg : Type} (ns : String) (parent : Dom.Node)
    (ks : List (View σ msg)) (s : σ) (a : DomArena msg) (hcl : View.DomCleanEach ks) :
    ((buildViewKidsM (m := StateM (DomArena msg)) ns parent ks s).run a).2.SameDom
      ((buildDomListM (m := StateM (DomArena msg)) ns parent (View.renderEach ks s)).run a).2 :=
  buildViewKidsM_eq_buildDomListM_of ns parent ks s (fun k _ a' hkCl => buildViewM_eq_buildDomM ns k s a' hkCl) a hcl

private theorem buildViewKidsM_vstate_clean_of {σ msg : Type} (childNs : String)
    (ks : List (View σ msg)) (s : σ) (f : Nat)
    (hView : ∀ k ∈ ks, ∀ (a : DomArena msg),
      View.DomClean k → 0 < a.nextId → a.nextId + htmlNodeCount (View.render k s) < UInt32.size →
      htmlDepth (View.render k s) ≤ f →
      let ((root, vst), a') := (buildViewM (m := StateM (DomArena msg)) childNs k s).run a
      vst.rootNode = root ∧ a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧
      a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render k s) ∧
      (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
      CleanDomSubtree f childNs (View.render k s) a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root ∧
      VStateMatches k s a' root vst) :
    ∀ (hsAcc : List (View σ msg)) (aBase : DomArena msg) (parent : Dom.Node)
      (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
      (acc : List Dom.Node) (kAcc : List (VState σ msg)) (Sacc : Nat → Prop),
      View.DomCleanEach ks → parent.toNat < aBase.nextId → 0 < aBase.nextId →
      aBase.nextId + htmlListNodeCount (View.renderEach ks s) < UInt32.size →
      htmlListDepth (View.renderEach ks s) ≤ f →
      (∀ k, Sacc k → parent.toNat < k ∧ k < aBase.nextId) →
      CleanDomChildren f childNs (View.renderEach hsAcc s) (aBase.set parent (.element pns ptag pst pmg acc)) Sacc acc →
      VStateKidsMatches hsAcc s (aBase.set parent (.element pns ptag pst pmg acc)) acc kAcc →
      let (ksts, aOut) := (buildViewKidsM (m := StateM (DomArena msg)) childNs parent ks s).run (aBase.set parent (.element pns ptag pst pmg acc))
      ∃ (csNew : List Dom.Node) (aBase' : DomArena msg),
        aOut = aBase'.set parent (.element pns ptag pst pmg (acc ++ csNew)) ∧
        aBase.nextId ≤ aBase'.nextId ∧
        aBase'.nextId ≤ aBase.nextId + htmlListNodeCount (View.renderEach ks s) ∧
        (∀ m, m.toNat < aBase.nextId → m ≠ parent → aOut.get m = aBase.get m) ∧
        CleanDomChildren f childNs (View.renderEach (hsAcc ++ ks) s) aOut (fun k => Sacc k ∨ (aBase.nextId ≤ k ∧ k < aOut.nextId)) (acc ++ csNew) ∧
        VStateKidsMatches (hsAcc ++ ks) s aOut (acc ++ csNew) (kAcc ++ ksts) := by
  induction ks with
  | nil =>
      intro hsAcc aBase parent pns ptag pst pmg acc kAcc Sacc _ _ _ _ _ _ hcl hvk
      dsimp only [buildViewKidsM, StateT.run, pure, StateT.pure, htmlListNodeCount]
      refine ⟨[], aBase, ?_, Nat.le_refl _, ?_, fun _ _ h => DomArena.get_set_ne _ _ h, ?_, ?_⟩
      · rw [List.append_nil]
      · rw [View.renderEach, htmlListNodeCount, Nat.add_zero]; exact Nat.le_refl _
      · rw [List.append_nil, List.append_nil]; exact CleanDomChildren_mono (fun _ h => .inl h) hcl
      · rw [List.append_nil, List.append_nil, List.append_nil]; exact hvk
  | cons k rest ih =>
      intro hsAcc aBase parent pns ptag pst pmg acc kAcc Sacc
        ⟨hkCl, hrestCl⟩ hparLt hpos hbound hdep hSacc hclAcc hvkAcc
      simp only [View.renderEach, htmlListNodeCount] at hbound; simp only [View.renderEach, htmlListDepth] at hdep
      have hkDep : htmlDepth (View.render k s) ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
      have hrestDep : htmlListDepth (View.renderEach rest s) ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
      let a0 := aBase.set parent (.element pns ptag pst pmg acc)
      have ha0Next : a0.nextId = aBase.nextId := rfl
      have hkSpec := hView k (.head _) a0 hkCl hpos (by rw [ha0Next]; omega) hkDep
      dsimp only [StateT.run] at hkSpec
      cases hbK : buildViewM (m := StateM (DomArena msg)) childNs k s a0 with
      | mk p1 aMid =>
          rcases p1 with ⟨kn, kst⟩
          rw [hbK] at hkSpec
          rcases hkSpec with ⟨hkRoot, hknGe, hknLt, haMidGe, haMidBound, haMidFr, hkClean, hkMatch⟩
          rw [ha0Next] at hknGe haMidGe haMidBound haMidFr hkClean
          have hparMid : aMid.get parent = .element pns ptag pst pmg acc := by
            rw [haMidFr parent hparLt]; exact DomArena.get_set_self _ _ _
          have hknNotIn : kn ∉ acc := fun hm => by
            have := (hSacc kn.toNat (CleanDomChildren_mem hclAcc kn hm)).2; omega
          let aAfter := aMid.set parent (.element pns ptag pst pmg (acc ++ [kn]))
          have haAfterNext : aAfter.nextId = aMid.nextId := rfl
          have happRun : MonadDom.appendChild (m := StateM (DomArena msg)) parent kn aMid = ((), aAfter) := by
            cases hkG : aMid.get kn with
            | fragment fcs => exact False.elim (CleanDomSubtree_not_fragment hkClean fcs hkG)
            | null | text _ | element _ _ _ _ _ =>
                simp only [MonadDom.appendChild, hkG, DomArena.modifyChildren, DomArena.modify, hparMid, List.erase_of_not_mem hknNotIn, aAfter]
          have hSacc' : ∀ c, (Sacc c ∨ (aBase.nextId ≤ c ∧ c < aAfter.nextId)) → parent.toNat < c ∧ c < aAfter.nextId := fun c hc => by
            rcases hc with h | h; have := hSacc c h; exact ⟨this.1, by omega⟩; exact ⟨by omega, h.2⟩
          have hclAccAfter : CleanDomChildren f childNs (View.renderEach hsAcc s) aAfter Sacc acc :=
            CleanDomChildren_frame (fun m hm => by
              have hb := hSacc _ hm; rw [DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega)), haMidFr m hb.2]) hclAcc
          have hkCleanAfter : CleanDomSubtree f childNs (View.render k s) aAfter (fun c => aBase.nextId ≤ c ∧ c < aAfter.nextId) kn :=
            CleanDomSubtree_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega))) hkClean
          have hclMid : CleanDomChildren f childNs (View.renderEach (hsAcc ++ [k]) s) aAfter
              (fun c => Sacc c ∨ (aBase.nextId ≤ c ∧ c < aAfter.nextId)) (acc ++ [kn]) := by
            have hclOne : CleanDomChildren f childNs [View.render k s] aAfter (fun c => aBase.nextId ≤ c ∧ c < aAfter.nextId) [kn] :=
              ⟨_, fun _ => False, fun _ h => h, fun _ h => h.elim, fun _ _ h => h.elim, hkCleanAfter, trivial⟩
            rw [View.renderEach_append]
            exact CleanDomChildren_append (fun c h1 h2 => by have := (hSacc c h1).2; omega) hclAccAfter hclOne
          have hvkAccAfter : VStateKidsMatches hsAcc s aAfter acc kAcc :=
            VStateKidsMatches_frame (fun m hm => by
              have hb := hSacc _ hm; rw [DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega)), haMidFr m hb.2]) hclAcc hvkAcc
          have hkMatchAfter : VStateMatches k s aAfter kn kst :=
            VStateMatches_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega))) hkClean hkMatch
          have hvkJoin : ∀ (hs : List (View σ msg)) (ac : List Dom.Node) (kac : List (VState σ msg)),
              VStateKidsMatches hs s aAfter ac kac → VStateKidsMatches (hs ++ [k]) s aAfter (ac ++ [kn]) (kac ++ [kst]) := by
            intro hs; induction hs with
            | nil => intro ac kac hvk; cases ac <;> cases kac <;> simp only [VStateKidsMatches, List.nil_append] at hvk ⊢; exact ⟨hkRoot.symm, hkMatchAfter, trivial⟩
            | cons _ _ ihh =>
                intro ac kac hvk
                cases ac with | nil => exact False.elim hvk | cons _ _ =>
                  cases kac with | nil => exact False.elim hvk | cons _ _ =>
                    exact ⟨hvk.1, hvk.2.1, ihh _ _ hvk.2.2⟩
          have hvkMid := hvkJoin hsAcc acc kAcc hvkAccAfter
          have hih := ih (fun x hx => hView x (.tail _ hx)) (hsAcc ++ [k]) aMid parent pns ptag pst pmg
            (acc ++ [kn]) (kAcc ++ [kst]) (fun c => Sacc c ∨ (aBase.nextId ≤ c ∧ c < aAfter.nextId))
            hrestCl (by omega) (by omega) (by omega) hrestDep hSacc' hclMid hvkMid
          dsimp only [StateT.run] at hih ⊢
          dsimp only [buildViewKidsM, bind, StateT.bind, pure, StateT.pure]
          rw [hbK]; dsimp only; rw [happRun]; dsimp only
          cases hbR : buildViewKidsM (m := StateM (DomArena msg)) childNs parent rest s aAfter with
          | mk restKsts aOut =>
              rw [hbR] at hih; dsimp only at hih
              rcases hih with ⟨csRest, aBase', hOutEq, hGeR, hBdR, hFrR, hClR, hVkR⟩
              simp only [List.append_assoc, List.singleton_append] at hOutEq hClR hVkR
              have haOutNext : aOut.nextId = aBase'.nextId := by rw [hOutEq]; rfl
              simp only [View.renderEach, htmlListNodeCount]
              refine ⟨kn :: csRest, aBase', hOutEq, by omega, by omega, fun m hmLt hmNe => ?_,
                CleanDomChildren_mono (fun c hc => hc.elim
                  (fun h => h.elim .inl (fun h2 => .inr ⟨h2.1, by rw [haOutNext]; rw [haAfterNext] at h2; exact Nat.lt_of_lt_of_le h2.2 hGeR⟩))
                  (fun h => .inr ⟨Nat.le_trans haMidGe h.1, h.2⟩)) hClR, hVkR⟩
              rw [hFrR m (by omega) hmNe, haMidFr m hmLt]; exact DomArena.get_set_ne _ _ hmNe

private theorem buildViewM_vstate_clean_aux {σ msg : Type} :
    ∀ (n : Nat) (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (fuel : Nat),
      sizeOf v ≤ n → View.DomClean v → 0 < a.nextId → a.nextId + htmlNodeCount (View.render v s) < UInt32.size →
      htmlDepth (View.render v s) ≤ fuel →
      let ((root, vst), a') := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
      vst.rootNode = root ∧ a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧
      a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
      (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
      CleanDomSubtree fuel ns (View.render v s) a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root ∧
      VStateMatches v s a' root vst
  | 0, _, v, _, _, _, hsz, _, _, _, _ => absurd (Nat.lt_of_lt_of_le (view_sizeOf_pos v) hsz) (Nat.lt_irrefl 0)
  | _ + 1, ns, .text str, _, a, fuel, _, _, hpos, hbound, hdep => by
      cases fuel with | zero => simp only [View.render, htmlDepth] at hdep; omega | succ _ =>
        have hs := buildDomM_spec ns (.text str) a _ hpos hbound hdep
        have hc := CleanDomSubtree_of_buildDomM ns (.text str) a _ rfl hpos hbound hdep
        simp only [buildViewM, buildDomM, MonadDom.createText, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at hs hc ⊢
        cases hb : a.alloc (.text str) with
        | mk r a' => rw [hb] at hs hc; dsimp only at hs hc ⊢; exact ⟨rfl, hs.1, hs.2.1, Nat.le_trans hs.1 (Nat.le_of_lt hs.2.1), hs.2.2.1, hs.2.2.2.1, hc, rfl⟩
  | _ + 1, ns, .dyn get, s, a, fuel, _, _, hpos, hbound, hdep => by
      cases fuel with | zero => simp only [View.render, htmlDepth] at hdep; omega | succ _ =>
        have hs := buildDomM_spec ns (.text (get s)) a _ hpos hbound hdep
        have hc := CleanDomSubtree_of_buildDomM ns (.text (get s)) a _ rfl hpos hbound hdep
        simp only [buildViewM, buildDomM, MonadDom.createText, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at hs hc ⊢
        cases hb : a.alloc (.text (get s)) with
        | mk r a' => rw [hb] at hs hc; dsimp only at hs hc ⊢; exact ⟨rfl, hs.1, hs.2.1, Nat.le_trans hs.1 (Nat.le_of_lt hs.2.1), hs.2.2.1, hs.2.2.2.1, hc, rfl, rfl⟩
  | _ + 1, ns, .static html, _, a, fuel, _, hcl, hpos, hbound, hdep => by
      have hs := buildDomM_spec ns html a fuel hpos hbound hdep
      have hc := CleanDomSubtree_of_buildDomM ns html a fuel hcl hpos hbound hdep
      simp only [buildViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at hs hc ⊢
      cases hb : buildDomM (m := StateM (DomArena msg)) ns html a with
      | mk r a' => rw [hb] at hs hc; dsimp only at hs hc; exact ⟨rfl, hs.1, hs.2.1, Nat.le_trans hs.1 (Nat.le_of_lt hs.2.1), hs.2.2.1, hs.2.2.2.1, hc, rfl⟩
  | _ + 1, ns, .dynNode get, s, a, fuel, _, hcl, hpos, hbound, hdep => by
      have hs := buildDomM_spec ns (get s) a fuel hpos hbound hdep
      have hc := CleanDomSubtree_of_buildDomM ns (get s) a fuel (hcl s) hpos hbound hdep
      simp only [buildViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at hs hc ⊢
      cases hb : buildDomM (m := StateM (DomArena msg)) ns (get s) a with
      | mk r a' => rw [hb] at hs hc; dsimp only at hs hc; exact ⟨rfl, hs.1, hs.2.1, Nat.le_trans hs.1 (Nat.le_of_lt hs.2.1), hs.2.2.1, hs.2.2.2.1, hc, rfl, rfl⟩
  | _ + 1, ns, .memo sm, s, a, fuel, _, hcl, hpos, hbound, hdep => by
      have hs := buildDomM_spec ns (sm.eval s) a fuel hpos hbound hdep
      have hc := CleanDomSubtree_of_buildDomM ns (sm.eval s) a fuel (hcl s) hpos hbound hdep
      simp only [buildViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at hs hc ⊢
      cases hb : buildDomM (m := StateM (DomArena msg)) ns (sm.eval s) a with
      | mk r a' => rw [hb] at hs hc; dsimp only at hs hc; exact ⟨rfl, hs.1, hs.2.1, Nat.le_trans hs.1 (Nat.le_of_lt hs.2.1), hs.2.2.1, hs.2.2.2.1, hc, rfl, rfl, rfl⟩
  | n + 1, ns, .ifElse c y no, s, a, fuel, hsz, ⟨hy, hn⟩, hpos, hbound, hdep => by
      have hwrap : ∀ (v' : View σ msg) (b : Bool), c s = b → (if b then y else no) = v' →
          (let ((root, vst), a') := (buildViewM (m := StateM (DomArena msg)) ns v' s).run a
           vst.rootNode = root ∧ a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧
           a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render v' s) ∧
           (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
           CleanDomSubtree fuel ns (View.render v' s) a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root ∧
           VStateMatches v' s a' root vst) →
          let ((root, vst), a') := (buildViewM (m := StateM (DomArena msg)) ns (.ifElse c y no) s).run a
          vst.rootNode = root ∧ a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧
          a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render (.ifElse c y no) s) ∧
          (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
          CleanDomSubtree fuel ns (View.render (.ifElse c y no) s) a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root ∧
          VStateMatches (.ifElse c y no) s a' root vst := by
        intro v' b hcb hveq ih
        dsimp only [StateT.run] at ih
        cases hb : buildViewM (m := StateM (DomArena msg)) ns v' s a with
        | mk p a' =>
            rcases p with ⟨r, inner⟩; rw [hb] at ih; rcases ih with ⟨hroot, h1, h2, h3, h4, h5, h6, h7⟩
            dsimp only [buildViewM, View.render, StateT.run, bind]
            cases b <;> (simp only [hcb, Bool.false_eq_true, ↓reduceIte, StateT.bind, pure, StateT.pure] at hveq ⊢; subst hveq; rw [hb]; dsimp only; exact ⟨hroot, h1, h2, h3, h4, h5, h6, ⟨hcb.symm, by simp only [hcb, Bool.false_eq_true, ↓reduceIte]; exact h7⟩⟩)
      cases hc : c s
      · exact hwrap no false hc rfl (buildViewM_vstate_clean_aux n ns no s a fuel
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (view_sizeOf_ifElse_right c y no) hsz)) hn hpos
          (by simp only [View.render, hc, Bool.false_eq_true, ↓reduceIte] at hbound; exact hbound)
          (by simp only [View.render, hc, Bool.false_eq_true, ↓reduceIte] at hdep; exact hdep))
      · exact hwrap y true hc rfl (buildViewM_vstate_clean_aux n ns y s a fuel
          (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (view_sizeOf_ifElse_left c y no) hsz)) hy hpos
          (by simp only [View.render, hc, ↓reduceIte] at hbound; exact hbound)
          (by simp only [View.render, hc, ↓reduceIte] at hdep; exact hdep))
  | n + 1, ns, .element tag attrs kids, s, a, fuel, hsz, ⟨haClean, hkidsClean⟩, hpos, hbound, hdep => by
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
          let aElem := a1.set node (.element realNs tag st mg [])
          have ha1Next : a1.nextId = a.nextId + 1 := rfl
          have hkids := buildViewKidsM_vstate_clean_of (Dom.childNsOf ns tag) kids s f
            (fun k hk a' hkCl hpos' hbd' hdp' => buildViewM_vstate_clean_aux n (Dom.childNsOf ns tag) k s a' f
              (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (view_sizeOf_element_mem hk) hsz)) hkCl hpos' hbd' hdp')
            [] a1 node realNs tag st mg [] [] (fun _ => False) hkidsClean
            (by rw [hnodeNat, ha1Next]; omega) (by rw [ha1Next]; omega)
            (by rw [ha1Next]; omega) (by omega) (fun _ h => h.elim) trivial trivial
          dsimp only [StateT.run] at hkids
          rcases hkids with ⟨csNew, aBase', hOutEq, haBaseGe, haBaseBound, haOutFr, hCleanOut, hVstOut⟩
          simp only [List.nil_append] at hOutEq hCleanOut hVstOut
          rw [hOutEq] at hCleanOut hVstOut
          rw [ha1Next] at haBaseGe haBaseBound hCleanOut
          have hrun : buildViewM (m := StateM (DomArena msg)) ns (.element tag attrs kids) s a =
              ((node, VState.elem node (buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s aElem).1),
               (buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s aElem).2) := by
            dsimp only [buildViewM, MonadDom.createElement, DomArena.alloc, bind, StateT.bind, pure, StateT.pure]
            change (match applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s)) (a1.set node (.element realNs tag {} [] [])) with
                    | (_, s0) =>
                        match buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s s0 with
                        | (ks, s1) => ((node, VState.elem node ks), s1)) = _
            rw [applyAttrsM_fresh_element a1 node realNs tag [] (attrs.map (VAttr.eval s))]; rfl
          dsimp only [StateT.run]; rw [hrun]; dsimp only; rw [hOutEq]
          have hltBase : node.toNat < (aBase'.set node (.element realNs tag st mg csNew)).nextId := by
            change node.toNat < aBase'.nextId; rw [hnodeNat]; omega
          simp only [View.render, htmlNodeCount]
          refine ⟨rfl, by rw [hnodeNat]; exact Nat.le_refl _, hltBase,
            by change a.nextId ≤ aBase'.nextId; omega, by change aBase'.nextId ≤ _; omega, fun m hm => ?_,
            ⟨⟨by rw [hnodeNat]; exact Nat.le_refl _, hltBase⟩, haClean.1 s, haClean.2.1 s, st, mg, csNew, DomArena.get_set_self _ _ _,
             ElemClean_evalSpecAttrs (haClean.2.1 s), ElemStateEquiv.refl st,
             fun nm hnm => List.contains_iff_mem.2 hnm,
             CleanDomChildren_mono (fun k hk => Or.elim hk (fun h => False.elim h) (fun h => ⟨⟨by omega, h.2⟩, by rw [hnodeNat]; omega⟩)) hCleanOut⟩,
            rfl, realNs, tag, st, mg, csNew, DomArena.get_set_self _ _ _, hVstOut⟩
          · have hne : m ≠ node := node_ne_of_toNat_ne (by rw [hnodeNat]; omega)
            rw [← hOutEq]; rw [haOutFr m (by rw [ha1Next]; omega) hne]; rfl
  | _ + 1, _, .keyedList _ _ _ _ _ _ _ (some _), _, _, _, _, h, _, _, _ => False.elim h
  | _ + 1, ns, .keyedList tag attrs keys marks rowSig rowEv rowsHtml none, s, a, fuel, _, ⟨ha, hrows⟩, hpos, hbound, hdep => by
      have heq := buildViewM_eq_buildDomM ns (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s a ⟨ha, hrows⟩
      have hs := buildDomM_spec ns (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s) a fuel hpos hbound hdep
      have hc := CleanDomSubtree_of_buildDomM ns (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s) a fuel
        (View.DomClean_render (v := .keyedList tag attrs keys marks rowSig rowEv rowsHtml) ⟨ha, hrows⟩ s) hpos hbound hdep
      have hvst : ∃ oldSigs, ((buildViewM (m := StateM (DomArena msg)) ns (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s).run a).1.2 =
          let r := ((buildViewM (m := StateM (DomArena msg)) ns (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s).run a).1.1
          .list r (disambiguateKeys (keys s)) oldSigs (rowsHtml s) (marks s) s!"§{r}§" := by
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
                        exact ⟨perRow, by rw [Html.map_prefixSignals_of_DomCleanList _ (hrows.2.1 s)]⟩
      rcases hvst with ⟨perRow, hvstEq⟩
      dsimp only [StateT.run] at heq hs hc hvstEq ⊢
      cases hbv : buildViewM (m := StateM (DomArena msg)) ns (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s a with
      | mk p1 aOut =>
          rcases p1 with ⟨root, vst⟩
          cases hbd : buildDomM (m := StateM (DomArena msg)) ns (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s) a with
          | mk droot aDom =>
              rw [hbv] at heq hvstEq; rw [hbd] at heq hs hc; dsimp only at heq hs hc hvstEq ⊢
              subst hvstEq
              rcases heq with ⟨hnEq, hsd⟩
              rw [← hnEq] at hs hc
              rw [hsd.1]
              refine ⟨rfl, hs.1, hs.2.1, Nat.le_trans hs.1 (Nat.le_of_lt hs.2.1), hs.2.2.1,
                fun m hm => (hsd.get_eq m).trans (hs.2.2.2.1 m hm),
                CleanDomSubtree_frame (fun m _ => hsd.get_eq m) hc, rfl, rfl, rfl⟩

theorem buildViewM_vstate_spec {σ msg : Type} (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (fuel : Nat)
    (hclean : View.DomClean v) (hpos : 0 < a.nextId)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ fuel) :
    let ((root, vst), a') := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
    vst.rootNode = root ∧ a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
    (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
    VStateValid fuel ns v s a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) vst ∧
    DomTreeAssocEquiv (readDomTree fuel a' vst.rootNode) (specDom ns (View.render v s)) := by
  have h := buildViewM_vstate_clean_aux (sizeOf v) ns v s a fuel (Nat.le_refl _) hclean hpos hbound hdep
  dsimp only [StateT.run] at h ⊢
  rcases h with ⟨hroot, _, _, ha1, ha2, hfr, hcl, hmt⟩
  have hval : VStateValid fuel ns v s _ (fun k => a.nextId ≤ k ∧ k < _) _ := ⟨hroot ▸ hcl, hroot ▸ hmt⟩
  exact ⟨hroot, ha1, ha2, hfr, hval, VStateValid_equiv hval⟩


end Qed
