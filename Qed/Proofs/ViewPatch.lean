import Qed.Proofs.KeyedReconcile
import Qed.Proofs.ViewPatch.Build
import Qed.Proofs.ViewPatch.Keyed
import Qed.Proofs.ViewPatch.Runtime

namespace Qed

section
variable {σ msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node)
  (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)

private abbrev PatchViewGoal (v : View σ msg) (s₁ s₂ : σ) (pre suf : List Dom.Node)
    (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg) : Prop :=
  childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") →
  View.DomClean v → pre.length + 1 + suf.length < UInt32.size →
  a.nextId + htmlNodeCount (View.render v s₂) < UInt32.size →
  htmlDepth (View.render v s₂) ≤ f → parent.toNat < a.nextId → 0 < a.nextId →
  a.get parent = .element pns ptag pst pmg (pre ++ vst.rootNode :: suf) →
  (pre ++ vst.rootNode :: suf).Nodup → ¬Sold parent.toNat →
  (∀ k, Sold k → k < a.nextId) → (∀ r ∈ pre ++ vst.rootNode :: suf, r.toNat < a.nextId) →
  VStateValid f childNs v s₁ a Sold vst →
  PatchViewPost f childNs parent pns ptag pst pmg v s₂ pre suf Sold a
    ((patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) v s₂ vst).run a)

private theorem patchViewM_leaf_spec (v : View σ msg)
    (hleaf : match v with | .text _ | .static _ | .dyn _ | .dynNode _ | .memo _ => True | _ => False)
    (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg) :
    PatchViewGoal f childNs parent pns ptag pst pmg v s₁ s₂ pre suf Sold a vst := by
  intro hchildNs hclean hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
  cases v with
  | ifElse _ _ _ | element _ _ _ | keyedList _ _ _ _ _ _ _ _ => exact False.elim hleaf
  | text _ | static _ =>
      cases vst <;> try exact False.elim hval.2
      dsimp only [patchViewM, StateT.run, pure, StateT.pure]
      exact ⟨Nat.le_refl _, by omega, fun _ _ _ _ => rfl, hpar, hnd, hparNodes,
        VStateValid_mono (fun _ => .inl) hval, CleanDomSubtree_equiv hval.1⟩
  | dyn get =>
      cases vst with
      | dyn node _ =>
          rcases hval with ⟨hcl, _, rfl⟩
          cases f with
          | zero => simp [CleanDomSubtree] at hcl
          | succ f' =>
              rcases hcl with ⟨hmem, hget⟩
              dsimp only [VState.rootNode] at hmem hget
              dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
              by_cases heq : get s₂ = get s₁
              · simp only [show (get s₂ != get s₁) = false by simp [heq], Bool.false_eq_true, ↓reduceIte]
                have hval' : VStateValid (f' + 1) childNs (.dyn get) s₂ a (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a.nextId)) (.dyn node (get s₂)) :=
                  ⟨⟨.inl hmem, by simpa [View.render, heq] using hget⟩, rfl, rfl⟩
                exact ⟨Nat.le_refl _, by simp [View.render, htmlNodeCount], fun _ _ _ _ => rfl, hpar, hnd, hparNodes, hval', VStateValid_equiv hval'⟩
              · simp only [show (get s₂ != get s₁) = true by simp [heq], ↓reduceIte, StateT.bind, pure, StateT.pure, MonadDom.setText, DomArena.modify]
                rw [hget]; dsimp only
                have hval' : VStateValid (f' + 1) childNs (.dyn get) s₂ (a.set node (.text (get s₂))) (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a.nextId)) (.dyn node (get s₂)) :=
                  ⟨⟨.inl hmem, DomArena.get_set_self _ _ _⟩, rfl, rfl⟩
                exact ⟨Nat.le_refl _, by simp [View.render, htmlNodeCount], fun m _ hmOut _ => DomArena.get_set_ne _ _ (fun hEq => hmOut (hEq ▸ hmem)),
                  by rw [DomArena.get_set_ne _ _ (fun h : parent = node => hparOut (h ▸ hmem))]; simpa [VState.rootNode] using hpar,
                  hnd, hparNodes, hval', VStateValid_equiv hval'⟩
      | _ => exact False.elim hval.2
  | dynNode get =>
      cases vst with
      | dynNode node _ =>
          rcases hval with ⟨hcl, _, rfl⟩
          have hp := patchHtmlSubtreeM_spec f childNs parent pns ptag pst pmg (get s₁) (get s₂) node pre suf Sold a
            hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hcl (hclean s₂)
          dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure] at hp ⊢
          rcases hsp : patchHtmlSubtreeM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (get s₁) (get s₂) a with ⟨n', a'⟩
          rw [hsp] at hp; exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, ⟨hp.2.2.2.2.2.2.1, rfl, rfl⟩, hp.2.2.2.2.2.2.2⟩
      | _ => exact False.elim hval.2
  | memo sm =>
      cases vst with
      | memo node lastKey lastHtml =>
          rcases hval with ⟨hcl, _, rfl, rfl⟩
          dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
          by_cases hkey : sm.keyOf s₂ = sm.keyOf s₁
          · have heval : sm.eval s₂ = sm.eval s₁ := sm.sound s₂ s₁ hkey
            simp only [beq_iff_eq.2 hkey, ↓reduceIte]
            have hval' : VStateValid f childNs (.memo sm) s₂ a (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a.nextId)) (.memo node (sm.keyOf s₁) (sm.eval s₁)) :=
              ⟨by simpa [View.render, heval] using CleanDomSubtree_mono (fun _ => .inl) hcl, rfl, hkey.symm, heval.symm⟩
            exact ⟨Nat.le_refl _, by omega, fun _ _ _ _ => rfl, hpar, hnd, hparNodes, hval', VStateValid_equiv hval'⟩
          · simp only [beq_eq_false_iff_ne.2 hkey, Bool.false_eq_true, ↓reduceIte, StateT.bind, pure, StateT.pure]
            have hp := patchHtmlSubtreeM_spec f childNs parent pns ptag pst pmg (sm.eval s₁) (sm.eval s₂) node pre suf Sold a
              hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hcl (hclean s₂)
            dsimp only [StateT.run] at hp
            rcases hsp : patchHtmlSubtreeM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (sm.eval s₁) (sm.eval s₂) a with ⟨n', a'⟩
            rw [hsp] at hp; exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1, ⟨hp.2.2.2.2.2.2.1, rfl, rfl, rfl⟩, hp.2.2.2.2.2.2.2⟩
      | _ => exact False.elim hval.2

private abbrev PatchViewKidsGoal (kids : List (View σ msg)) (targetsDone : List (Html msg))
    (preC sufC : List Dom.Node) (kstates : List (VState σ msg)) (s₁ s₂ : σ)
    (Sdone Srem : Nat → Prop) (a : DomArena msg) : Prop :=
  childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") →
  View.DomCleanEach kids → htmlListDepth (View.renderEach kids s₂) ≤ f →
  a.nextId + htmlListNodeCount (View.renderEach kids s₂) < UInt32.size →
  parent.toNat < a.nextId → 0 < a.nextId →
  a.get parent = .element pns ptag pst pmg (preC ++ sufC) → (preC ++ sufC).Nodup →
  (∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId) →
  CleanDomChildren f childNs targetsDone a Sdone preC →
  (∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) → (∀ k, Sdone k → Srem k → False) →
  (∀ r ∈ sufC, r.toNat < a.nextId ∧ r ≠ parent) →
  CleanDomChildren f childNs (View.renderEach kids s₁) a Srem sufC →
  VStateKidsMatches kids s₁ a sufC kstates →
  let (ks', aOut) := (patchViewKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat preC.length) kids s₂ kstates).run a
  ∃ Snew, let domCs' := ks'.map VState.rootNode
    a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount (View.renderEach kids s₂) ∧
    aOut.get parent = .element pns ptag pst pmg (preC ++ domCs') ∧ (preC ++ domCs').Nodup ∧
    (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    (∀ k, Snew k → (Sdone k ∨ Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧
    CleanDomChildren f childNs (targetsDone ++ View.renderEach kids s₂) aOut Snew (preC ++ domCs') ∧
    VStateKidsMatches kids s₂ aOut domCs' ks'

private theorem patchViewM_ifElse_spec (cond : σ → Bool) (yes no : View σ msg) (s₁ s₂ : σ)
    (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg)
    (ihY : ∀ inner, PatchViewGoal f childNs parent pns ptag pst pmg yes s₁ s₂ pre suf Sold a inner)
    (ihN : ∀ inner, PatchViewGoal f childNs parent pns ptag pst pmg no s₁ s₂ pre suf Sold a inner) :
    PatchViewGoal f childNs parent pns ptag pst pmg (.ifElse cond yes no) s₁ s₂ pre suf Sold a vst := by
  intro hchildNs hclean hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
  cases vst with
  | cond wasYes inner =>
      rcases hval with ⟨hcl, ⟨hwy, hin⟩⟩
      let targetV := if cond s₂ then yes else no
      have hren : View.render (.ifElse cond yes no) s₂ = View.render targetV s₂ := by
        dsimp only [targetV, View.render]; cases cond s₂ <;> rfl
      dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
      by_cases hsame : cond s₂ = wasYes
      · simp only [beq_iff_eq.2 hsame, ↓reduceIte]
        have hih : PatchViewPost f childNs parent pns ptag pst pmg targetV s₂ pre suf Sold a
            ((patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) targetV s₂ inner).run a) := by
          have hc₁ : cond s₁ = cond s₂ := hwy.symm.trans hsame.symm
          cases hc₂ : cond s₂ <;>
            simp only [targetV, hc₁, hc₂, Bool.false_eq_true, ↓reduceIte, View.render] at hbound hdep hcl hin ⊢
          · exact ihN inner hchildNs hclean.2 hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes ⟨hcl, hin⟩
          · exact ihY inner hchildNs hclean.1 hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes ⟨hcl, hin⟩
        dsimp only [PatchViewPost, StateT.run, StateT.bind, StateT.pure] at hih ⊢
        rcases hp : patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) targetV s₂ inner a with ⟨inner', a'⟩
        rw [hp] at hih; rcases hih with ⟨h1, h2, h3, h4, h5, h6, ⟨hcl', hm'⟩, heqv'⟩
        cases hc₂ : cond s₂ <;> (
          simp only [targetV, hc₂, Bool.false_eq_true, ↓reduceIte, StateT.bind, StateT.pure] at hp hm' ⊢
          rw [hp]
          exact ⟨h1, hren.symm ▸ h2, h3, h4, h5, h6, ⟨hren.symm ▸ hcl', hc₂.symm, by simpa [hc₂] using hm'⟩, hren.symm ▸ heqv'⟩)
      · simp only [beq_eq_false_iff_ne.2 hsame, Bool.false_eq_true, ↓reduceIte, StateT.bind]
        have hnsRun : MonadDom.childNamespace (m := StateM (DomArena msg)) parent a = (childNs, a) := by
          simp only [MonadDom.childNamespace, hpar, hchildNs]
        have huJ : (UInt32.ofNat pre.length).toNat = pre.length := uint32_toNat_ofNat_lt pre.length (by omega)
        rw [hnsRun]; dsimp only [Bind.bind]
        have htargetClean : View.DomClean targetV := by dsimp only [targetV]; cases cond s₂; exact hclean.2; exact hclean.1
        have hbuild := buildViewM_vstate_spec childNs targetV s₂ a f htargetClean hpos (hren ▸ hbound) (hren ▸ hdep)
        dsimp only [StateT.run] at hbuild
        rcases hB : buildViewM (m := StateM (DomArena msg)) childNs targetV s₂ a with ⟨⟨n2, newInner⟩, aMid⟩
        rw [hB] at hbuild; rcases hbuild with ⟨hn2Root, haMidGe, haMidBound, haMidFr, hVstMid, _⟩
        have hparMid : aMid.get parent = .element pns ptag pst pmg (pre ++ inner.rootNode :: suf) := by
          rw [haMidFr parent hparLt]; exact hpar
        let a' := aMid.set parent (.element pns ptag pst pmg (pre ++ n2 :: suf))
        have hn2Ge : a.nextId ≤ n2.toNat := by have hrm := VStateValid_root_mem hVstMid; rw [hn2Root] at hrm; exact hrm.1
        have hn2NotIn : n2 ∉ pre ++ inner.rootNode :: suf := fun hm => Nat.not_lt.2 hn2Ge (hparNodes n2 hm)
        have hVst' : VStateValid f childNs targetV s₂ a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) newInner :=
          VStateValid_mono (fun _ => .inr) (VStateValid_frame (fun m hm =>
            DomArena.get_set_ne _ _ (fun hEq => Nat.not_lt.2 hm.1 (hEq ▸ hparLt))) hVstMid)
        have hVstIf : VStateValid f childNs (.ifElse cond yes no) s₂ a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) (.cond (cond s₂) newInner) :=
          ⟨hren.symm ▸ hVst'.1, rfl, by cases hc₂ : cond s₂ <;> simpa [targetV, hc₂] using hVst'.2⟩
        suffices hPost : PatchViewPost f childNs parent pns ptag pst pmg (.ifElse cond yes no) s₂ pre suf Sold a (.cond (cond s₂) newInner, a') by
          cases hc₂ : cond s₂ <;> (
            simp only [targetV, hc₂, Bool.false_eq_true, ↓reduceIte, StateT.bind, StateT.pure, Bind.bind] at hB ⊢
            rw [hB]; simpa only [DomArena.modifyChildren, DomArena.modify, hparMid, huJ, listReplaceAt_append_middle, pure, a', hc₂] using hPost)
        refine ⟨haMidGe, hren.symm ▸ haMidBound,
          fun m hmPar _ hmLt => by rw [DomArena.get_set_ne _ _ hmPar, haMidFr m hmLt],
          by simp only [VState.rootNode, hn2Root]; exact DomArena.get_set_self _ _ _,
          by simp only [VState.rootNode, hn2Root]; exact nodup_append_replace hnd (.inr hn2NotIn),
          fun r hr => ?_, hVstIf, VStateValid_equiv hVstIf⟩
        rcases List.mem_append.1 hr with hp | hc
        · exact Nat.lt_of_lt_of_le (hparNodes r (List.mem_append_left _ hp)) haMidGe
        · exact (List.mem_cons.1 hc).elim (fun h => h ▸ (VStateValid_root_mem hVstMid).2)
            fun htl => Nat.lt_of_lt_of_le (hparNodes r (List.mem_append_right _ (.tail _ htl))) haMidGe
  | _ => exact False.elim hval.2

private theorem patchViewM_element_spec (tag : String) (attrs : List (VAttr σ msg)) (kids : List (View σ msg)) (s₁ s₂ : σ)
    (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg)
    (ihK : ∀ f' node realNs st' mg' domCs kstates a1,
      PatchViewKidsGoal f' (Dom.childNsOf childNs tag) node realNs tag st' mg'
        kids [] [] domCs kstates s₁ s₂ (fun _ => False) (fun k => Sold k ∧ k ≠ node.toNat) a1) :
    PatchViewGoal f childNs parent pns ptag pst pmg (.element tag attrs kids) s₁ s₂ pre suf Sold a vst := by
  intro hchildNs hclean _ hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
  cases vst with
  | elem node kstates =>
      dsimp only [VStateValid, VState.rootNode] at hpar hnd hparNodes hval
      rcases hval with ⟨hcl, _, ns', tag', st, mg, domCs, hgetM, hksM⟩
      cases f with
      | zero => exact False.elim hcl
      | succ f' =>
          rcases hcl with ⟨hnodeMem, _, _, st0, mg0, domCs0, hnodeGet, hElClean, hElEq, hmg, hCleanCs⟩
          rw [hgetM] at hnodeGet; cases hnodeGet
          have hne : node ≠ parent := fun h => hparOut (h ▸ hnodeMem)
          have hnodeLt : node.toNat < a.nextId := hSoldLt _ hnodeMem
          have hdyn := applyDynAttrsM_spec a node (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st mg domCs attrs s₁ s₂ hclean.1 hElClean hElEq hmg
          rw [DomArena.set_get_self a hgetM] at hdyn
          rcases hdyn with ⟨ha1Next, ha1Ne, st', mg', ha1Get, hElClean', hElEq', hmg'⟩
          let a1 := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a).2
          have ha1N : a1.nextId = a.nextId := ha1Next
          have hCleanCs1 := CleanDomChildren_frame (fun m hm => ha1Ne m (node_ne_of_toNat_ne hm.2)) hCleanCs
          have hksM1 := VStateKidsMatches_frame (fun m hm => ha1Ne m (node_ne_of_toNat_ne hm.2)) hCleanCs hksM
          have hndCs := CleanDomChildren_nodup hCleanCs
          have hChildNodes : ∀ r ∈ domCs, r.toNat < a1.nextId ∧ r ≠ node := fun r hr =>
            have hb := CleanDomChildren_mem hCleanCs r hr; ⟨ha1N ▸ hSoldLt _ hb.1, node_ne_of_toNat_ne hb.2⟩
          simp only [View.render, htmlNodeCount] at hbound; simp only [View.render, htmlDepth] at hdep
          have hccNs := childNamespace_eq_childNsOf (ptag := tag) (show childNs = "" ∨ childNs = Dom.svgNs by rw [hchildNs]; split <;> simp)
          have hkids := ihK f' node (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) st' mg' domCs kstates a1
            hccNs.symm hclean.2 (by omega)
            (ha1N ▸ Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left _ 1) _) hbound)
            (ha1N ▸ hnodeLt) (ha1N ▸ hpos) ha1Get hndCs.1
            (fun _ h => h.elim) trivial (fun k hk => ⟨hk.2, ha1N ▸ hSoldLt k hk.1⟩)
            (fun _ h => h.elim) hChildNodes hCleanCs1 hksM1
          dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure] at hkids ⊢
          rw [show applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a = ((), a1) from rfl]; dsimp only
          cases hkRun : patchViewKidsM (m := StateM (DomArena msg)) node 0 kids s₂ kstates a1 with
          | mk ks' aOut =>
              rw [show (UInt32.ofNat ([] : List Dom.Node).length) = 0 from rfl, hkRun] at hkids; dsimp only at hkids
              rcases hkids with ⟨Snew, haOutGe, haOutBound, hnodeOut, _, hfrOut, hSnew, hCleanOut, hVstOut⟩
              have haGe : a.nextId ≤ aOut.nextId := ha1N ▸ haOutGe
              have hvalOut : VStateValid (f' + 1) childNs (.element tag attrs kids) s₂ aOut
                  (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) (.elem node ks') :=
                ⟨⟨.inl hnodeMem, hclean.1.1 s₂, hclean.1.2.1 s₂, st', mg', ks'.map VState.rootNode,
                  hnodeOut, hElClean', hElEq', hmg',
                  CleanDomChildren_mono (fun k hk => ⟨(hSnew k hk).1.elim (fun h => h.elim)
                    (fun h => h.elim (fun hs => .inl hs.1) (fun ha => .inr ⟨ha1N ▸ ha.1, ha.2⟩)), (hSnew k hk).2⟩) hCleanOut⟩,
                 rfl, _, tag, st', mg', ks'.map VState.rootNode, hnodeOut, hVstOut⟩
              exact ⟨haGe, by simp only [View.render, htmlNodeCount]; omega,
                fun m _ hmOut hmLt => by have hmn : m ≠ node := fun h => hmOut (h ▸ hnodeMem); rw [hfrOut m hmn (fun h => hmOut h.1) (ha1N ▸ hmLt), ha1Ne m hmn],
                by rw [hfrOut parent hne.symm (fun h => hparOut h.1) (ha1N ▸ hparLt), ha1Ne parent hne.symm, hpar]; rfl,
                hnd, fun r hr => Nat.lt_of_lt_of_le (hparNodes r hr) haGe, hvalOut, VStateValid_equiv hvalOut⟩
  | _ => exact False.elim hval.2

private theorem patchViewKidsM_spec_of (kids : List (View σ msg)) (s₁ s₂ : σ)
    (hView : ∀ k ∈ kids, ∀ pre suf Sold a vst,
      PatchViewGoal f childNs parent pns ptag pst pmg k s₁ s₂ pre suf Sold a vst) :
    ∀ targetsDone preC sufC kstates Sdone Srem a,
      PatchViewKidsGoal f childNs parent pns ptag pst pmg kids targetsDone preC sufC kstates s₁ s₂ Sdone Srem a := by
  induction kids with
  | nil =>
      intro targetsDone preC sufC kstates Sdone Srem a
        _ _ _ _ _ _ hpar hnd hSdone hDone _ _ _ hCl hVk
      cases sufC with | cons _ _ => exact False.elim hCl | nil =>
        cases kstates with | cons _ _ => exact False.elim hVk | nil =>
          dsimp only [patchViewKidsM, StateT.run, pure, StateT.pure, View.renderEach, htmlListNodeCount, List.map_nil]
          rw [List.append_nil] at hpar hnd
          exact ⟨Sdone, Nat.le_refl _, Nat.le_refl _, by rw [List.append_nil]; exact hpar,
            by rw [List.append_nil]; exact hnd, fun _ _ _ _ => rfl,
            fun k hk => ⟨.inl hk, (hSdone k hk).1⟩, by rw [List.append_nil, List.append_nil]; exact hDone, trivial⟩
  | cons k rest ih =>
      intro targetsDone preC sufC kstates Sdone Srem a
        hchildNs hclean hdep hbound hparLt hpos hpar hnd hSdone hDone hSrem hDisj hsufB hCl hVk
      rcases hclean with ⟨hkCl, hrestCl⟩
      cases sufC with | nil => exact False.elim hCl | cons c sufRest =>
        cases kstates with | nil => exact False.elim hVk | cons kst restSt =>
          rcases hCl with ⟨Sc, Srest, hSc, hSr, hDSr, hcCl, hSufCl⟩
          rcases hVk with ⟨rfl, hkMatch, hRestMatch⟩
          simp only [View.renderEach, htmlListDepth] at hdep; simp only [View.renderEach, htmlListNodeCount] at hbound ⊢
          have hparNodes : ∀ r ∈ preC ++ kst.rootNode :: sufRest, r.toNat < a.nextId := fun r hr =>
            (List.mem_append.1 hr).elim (fun hp => (hSdone _ (CleanDomChildren_mem hDone r hp)).2) (fun hc => (hsufB r hc).1)
          have hpreLen : preC.length + 1 + sufRest.length < UInt32.size := by
            have := nodup_nodes_lt_length_le a.nextId (preC ++ kst.rootNode :: sufRest) hnd hparNodes
            simp only [List.length_append, List.length_cons] at this; omega
          have hpatchK := hView k (.head _) preC sufRest Sc a kst
            hchildNs hkCl hpreLen (by omega) (Nat.le_trans (Nat.le_max_left _ _) hdep) hparLt hpos hpar hnd
            (fun h => (hSrem _ (hSc _ h)).1 rfl) (fun x hx => (hSrem x (hSc x hx)).2) hparNodes ⟨hcCl, hkMatch⟩
          dsimp only [patchViewKidsM, StateT.run, bind, StateT.bind, pure, StateT.pure] at hpatchK ⊢
          cases hpK : patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat preC.length) k s₂ kst a with
          | mk kst' aMid =>
              rw [hpK] at hpatchK
              rcases hpatchK with ⟨haMidGe, haMidBound, hfrMid, hparMid, hndMid, _, hValK', _⟩
              let Sdone' : Nat → Prop := fun x => Sdone x ∨ (Sc x ∨ (a.nextId ≤ x ∧ x < aMid.nextId))
              have ⟨hSdone', hDone'⟩ := clean_done_extend haMidGe hparLt hSdone (fun x h => hSrem x (hSc x h))
                (fun x h1 h2 => hDisj x h1 (hSc x h2))
                (fun m hm => hfrMid m (node_ne_of_toNat_ne (hSdone _ hm).1) (fun hsc => hDisj _ hm (hSc _ hsc)) (hSdone _ hm).2)
                hDone hValK'.1
              have hfrSuf : ∀ m : Dom.Node, Srest m.toNat → aMid.get m = a.get m := fun m hm =>
                hfrMid m (node_ne_of_toNat_ne (hSrem _ (hSr _ hm)).1) (fun hsc => hDSr _ hsc hm) (hSrem _ (hSr _ hm)).2
              rw [show UInt32.ofNat preC.length + 1 = UInt32.ofNat (preC ++ [kst'.rootNode]).length by
                simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
                exact uint32_ofNat_succ preC.length (by omega)]
              have hih := ih (fun x hx => hView x (.tail _ hx)) (targetsDone ++ [View.render k s₂])
                (preC ++ [kst'.rootNode]) sufRest restSt Sdone' Srest aMid hchildNs hrestCl
                (Nat.le_trans (Nat.le_max_right _ _) hdep) (by omega)
                (Nat.lt_of_lt_of_le hparLt haMidGe) (Nat.lt_of_lt_of_le hpos haMidGe)
                (by simpa [List.append_assoc] using hparMid) (by simpa [List.append_assoc] using hndMid)
                hSdone' hDone'
                (fun x hx => have hb := hSrem x (hSr x hx); ⟨hb.1, Nat.lt_of_lt_of_le hb.2 haMidGe⟩)
                (fun x h1 h2 => not_Sdone_extend (fun h => hDisj x h (hSr x h2)) (fun hsc => hDSr x hsc h2) (hSrem x (hSr x h2)).2 h1)
                (fun r hr => have hb := hsufB r (.tail _ hr); ⟨Nat.lt_of_lt_of_le hb.1 haMidGe, hb.2⟩)
                (CleanDomChildren_frame hfrSuf hSufCl) (VStateKidsMatches_frame hfrSuf hSufCl hRestMatch)
              dsimp only [StateT.run] at hih ⊢
              cases hpR : patchViewKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (preC ++ [kst'.rootNode]).length) rest s₂ restSt aMid with
              | mk restSt' aOut =>
                  rw [hpR] at hih; dsimp only at hih
                  rcases hih with ⟨Snew, haOutGe, haOutBound, hparR, hndR, hfrR, hSnew, hCleanR, hVstR⟩
                  have hValKOut := VStateMatches_frame (fun m hm => by
                    have hnmR : ¬Srest m.toNat := fun hr => hm.elim (fun hs => hDSr _ hs hr)
                      (fun hlo => Nat.not_lt.2 hlo.1 (hSrem _ (hSr _ hr)).2)
                    exact hfrR m (node_ne_of_toNat_ne (hSdone' m.toNat (.inr hm)).1) hnmR (hSdone' m.toNat (.inr hm)).2)
                    hValK'.1 hValK'.2
                  rw [List.append_assoc, List.singleton_append] at hparR hndR hCleanR
                  rw [List.append_assoc, List.singleton_append] at hCleanR
                  refine ⟨Snew, Nat.le_trans haMidGe haOutGe,
                    Nat.le_trans haOutBound (Nat.add_assoc _ _ _ ▸ Nat.add_le_add_right haMidBound _),
                    hparR, hndR,
                    fun m hmPar hmR hmLt =>
                      (hfrR m hmPar (fun hr => hmR (hSr _ hr)) (Nat.lt_of_lt_of_le hmLt haMidGe)).trans
                        (hfrMid m hmPar (fun hsc => hmR (hSc _ hsc)) hmLt),
                    clean_step_Snew_compose haMidGe haOutGe hSc hSr hSnew, hCleanR, rfl, hValKOut, hVstR⟩

end

theorem patchViewM_spec {σ msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (v : View σ msg) (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg)
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (hclean : View.DomClean v) (hpreLen : pre.length + 1 + suf.length < UInt32.size)
    (hbound : a.nextId + htmlNodeCount (View.render v s₂) < UInt32.size)
    (hdep : htmlDepth (View.render v s₂) ≤ f) (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ vst.rootNode :: suf))
    (hnd : (pre ++ vst.rootNode :: suf).Nodup) (hparOut : ¬Sold parent.toNat)
    (hSoldLt : ∀ k, Sold k → k < a.nextId) (hparNodes : ∀ r ∈ pre ++ vst.rootNode :: suf, r.toNat < a.nextId)
    (hval : VStateValid f childNs v s₁ a Sold vst) :
    PatchViewPost f childNs parent pns ptag pst pmg v s₂ pre suf Sold a
      ((patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) v s₂ vst).run a) := by
  suffices h : PatchViewGoal f childNs parent pns ptag pst pmg v s₁ s₂ pre suf Sold a vst from
    h hchildNs hclean hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
  clear hchildNs hclean hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
  induction v using View.ind generalizing f childNs parent pns ptag pst pmg pre suf Sold a vst with
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      intro hchildNs hclean _ hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
      exact patchViewM_keyedList_spec f childNs parent pns ptag pst pmg tag attrs keys marks rowSig rowEv rowsHtml tmpl?
        s₁ s₂ pre suf Sold a vst hchildNs hclean hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hval
  | text _ | static _ | dyn _ | dynNode _ | memo _ =>
      exact patchViewM_leaf_spec f childNs parent pns ptag pst pmg _ trivial s₁ s₂ pre suf Sold a vst
  | ifElse cond yes no ihy ihn =>
      exact patchViewM_ifElse_spec f childNs parent pns ptag pst pmg cond yes no s₁ s₂ pre suf Sold a vst
        (fun inner => ihy f childNs parent pns ptag pst pmg pre suf Sold a inner)
        (fun inner => ihn f childNs parent pns ptag pst pmg pre suf Sold a inner)
  | element tag attrs kids ihk =>
      exact patchViewM_element_spec f childNs parent pns ptag pst pmg tag attrs kids s₁ s₂ pre suf Sold a vst
        (fun f' node realNs st' mg' domCs kstates a1 =>
          patchViewKidsM_spec_of f' (Dom.childNsOf childNs tag) node realNs tag st' mg' kids s₁ s₂
            (fun k hk pre' suf' Sold' a' vst' => ihk k hk f' (Dom.childNsOf childNs tag) node realNs tag st' mg' pre' suf' Sold' a' vst')
            [] [] domCs kstates (fun _ => False) (fun k => Sold k ∧ k ≠ node.toNat) a1)

theorem patchViewKidsM_spec {σ msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (kids : List (View σ msg)) (targetsDone : List (Html msg)) (preC sufC : List Dom.Node)
    (kstates : List (VState σ msg)) (s₁ s₂ : σ) (Sdone Srem : Nat → Prop) (a : DomArena msg)
    (hchildNs : childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else ""))
    (hclean : View.DomCleanEach kids) (hdep : htmlListDepth (View.renderEach kids s₂) ≤ f)
    (hbound : a.nextId + htmlListNodeCount (View.renderEach kids s₂) < UInt32.size)
    (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (preC ++ sufC)) (hnd : (preC ++ sufC).Nodup)
    (hSdone : ∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId)
    (hDone : CleanDomChildren f childNs targetsDone a Sdone preC)
    (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) (hDisj : ∀ k, Sdone k → Srem k → False)
    (hsufB : ∀ r ∈ sufC, r.toNat < a.nextId ∧ r ≠ parent)
    (hCl : CleanDomChildren f childNs (View.renderEach kids s₁) a Srem sufC)
    (hVk : VStateKidsMatches kids s₁ a sufC kstates) :
    let (ks', aOut) := (patchViewKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat preC.length) kids s₂ kstates).run a
    ∃ Snew, let domCs' := ks'.map VState.rootNode
      a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount (View.renderEach kids s₂) ∧
      aOut.get parent = .element pns ptag pst pmg (preC ++ domCs') ∧ (preC ++ domCs').Nodup ∧
      (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      (∀ k, Snew k → (Sdone k ∨ Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧
      CleanDomChildren f childNs (targetsDone ++ View.renderEach kids s₂) aOut Snew (preC ++ domCs') ∧
      VStateKidsMatches kids s₂ aOut domCs' ks' :=
  patchViewKidsM_spec_of f childNs parent pns ptag pst pmg kids s₁ s₂
    (fun k _ pre' suf' Sold' a' vst' => patchViewM_spec f childNs parent pns ptag pst pmg k s₁ s₂ pre' suf' Sold' a' vst')
    targetsDone preC sufC kstates Sdone Srem a
    hchildNs hclean hdep hbound hparLt hpos hpar hnd hSdone hDone hSrem hDisj hsufB hCl hVk

end Qed
