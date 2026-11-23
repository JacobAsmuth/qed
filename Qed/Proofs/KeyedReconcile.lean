import Qed.Proofs.DomSubtree

namespace Qed

def InPlaceChildPatchSpec (fuel : Nat) (childNs : String) (parent : Dom.Node) (j : UInt32)
    (child : Dom.Node) (p : Patch msg) (target : Html msg)
    (lo hi : Nat) (aIn aOut : DomArena msg) : Prop :=
  ((applyToDomM (m := StateM (DomArena msg)) parent j child p).run aIn).2 = aOut ∧
  aIn.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ aIn.nextId + htmlNodeCount target ∧
  (∀ m : Dom.Node, (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < aIn.nextId → aOut.get m = aIn.get m) ∧
  SubtreeInSet fuel aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (aIn.nextId ≤ k ∧ k < aOut.nextId)) child ∧
  readDomTree fuel aOut child = specDom childNs target

theorem InPlaceChildPatchSpec_setText (a : DomArena msg) (parent child : Dom.Node) (idx : UInt32)
    (sOld sNew : String) (childNs : String) (fuel : Nat) (hf : 0 < fuel) (hlo : child.toNat < a.nextId) :
    InPlaceChildPatchSpec fuel childNs parent idx child (.setText sNew) (.text sNew)
      child.toNat (child.toNat + 1) (a.set child (.text sOld))
      ((applyToDomM (m := StateM (DomArena msg)) parent idx child (.setText sNew)).run
        (a.set child (.text sOld))).2 := by
  have hget : ((applyToDomM (m := StateM (DomArena msg)) parent idx child (.setText sNew)).run
      (a.set child (.text sOld))).2 = a.set child (.text sNew) := by
    simp [applyToDomM, StateT.run, MonadDom.setText, DomArena.modify, DomArena.get_set_self, DomArena.set_set]
  cases fuel with
  | zero => omega
  | succ _ =>
      refine ⟨rfl, by simp [hget], by simp [hget, htmlNodeCount], fun m hm _ => ?_,
        by simp only [hget]; exact ⟨.inl ⟨Nat.le_refl _, by omega⟩, by simp [DomArena.get_set_self]⟩,
        by simp [hget, readDomTree, DomArena.get_set_self, specDom]⟩
      simp [hget, DomArena.get_set_ne _ _ (show m ≠ child from fun heq => by subst heq; omega)]

theorem keyed_step_insertBefore_create (pre suf : List Dom.Node) (cn : Dom.Node)
    (hnd : (pre ++ suf).Nodup) (hnot : cn ∉ pre ++ suf) :
    w3cInsertBefore (pre ++ suf) pre.length cn = pre ++ cn :: suf := by
  rw [w3cInsertBefore_step pre suf cn hnd (fun h => hnot (List.mem_append_left _ h)),
      List.erase_of_not_mem (fun h => hnot (List.mem_append_right _ h))]

theorem positional_step_reuse_tail {msg : Type} (parent : Dom.Node) (pns ptag : String)
    (pst : SpecElemState msg) (pmg : List String)
    (pre : List Dom.Node) (hd : Dom.Node) (tl : List Dom.Node) (a : DomArena msg) :
    pre.length < UInt32.size →
    (MonadDom.childAt (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)).run
      (a.set parent (.element pns ptag pst pmg (pre ++ hd :: tl))) =
      (hd, a.set parent (.element pns ptag pst pmg (pre ++ hd :: tl))) := by
  intro hlt
  have hu : (UInt32.ofNat pre.length).toNat = pre.length := uint32_toNat_ofNat_lt pre.length hlt
  simp [MonadDom.childAt, StateT.run, DomArena.get_set_self, hu]

theorem positional_removeTail_spec {msg : Type} (a : DomArena msg) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (targets rem : List Dom.Node) (hlen : targets.length + rem.length < UInt32.size) :
    ((MonadDom.childCount (m := StateM (DomArena msg)) parent >>= fun count =>
      removeTailM (m := StateM (DomArena msg)) parent (UInt32.ofNat targets.length)
        (count.toNat - targets.length)).run
      (a.set parent (.element pns ptag pst pmg (targets ++ rem)))).2 =
      a.set parent (.element pns ptag pst pmg targets) := by
  have huCount : (UInt32.ofNat (targets ++ rem).length).toNat = targets.length + rem.length := by
    rw [uint32_toNat_ofNat_lt _ (by simp; omega)]; simp
  dsimp only [bind, StateT.bind, StateT.run, MonadDom.childCount]
  rw [DomArena.get_set_self]; dsimp only; rw [huCount, Nat.add_sub_cancel_left]
  have hr := removeTailM_spec a parent targets.length rem.length pns ptag pst pmg (targets ++ rem)
  dsimp only [StateT.run] at hr
  rw [hr, uint32_toNat_ofNat_lt targets.length (by omega), removeTailSpec_append]

/-! ## Keyed Index Injectivity, `CleanDomSubtree`, & Complete `applyToDomM` / `patchHtmlSubtreeM` -/

theorem validatedKeyIndex_inj {cs : List (Html msg)} {idx : Std.HashMap String Nat}
    (hv : validatedKeyIndex cs = some idx) {i₁ i₂ : Nat} {k : String}
    (h₁ : i₁ < cs.length) (h₂ : i₂ < cs.length)
    (hk₁ : cs[i₁].keyOf = some k) (hk₂ : cs[i₂].keyOf = some k) : i₁ = i₂ := by
  have ⟨_, hspec⟩ := validatedKeyIndex_spec hv
  rcases hspec i₁ h₁ with ⟨k₁, heq₁, hidx₁⟩; rcases hspec i₂ h₂ with ⟨k₂, heq₂, hidx₂⟩
  rw [hk₁] at heq₁; cases heq₁; rw [hk₂] at heq₂; cases heq₂
  exact Option.some.inj (hidx₁.symm.trans hidx₂)

def DiffStepsValid {msg : Type} (c₁ c₂ : List (Html msg)) (steps : List (KeyedStep msg)) : Prop :=
  steps.length = c₂.length ∧
  (∀ (i : Nat) (hi : i < c₂.length),
    (∀ newH, steps[i]? = some (.create newH) → newH = c₂[i]) ∧
    (∀ j p, steps[i]? = some (.reuse j p) → ∃ _ : j < c₁.length, p = diff c₁[j] c₂[i])) ∧
  ∀ i₁ i₂ j₁ j₂ p₁ p₂, i₁ < steps.length → i₂ < steps.length →
    steps[i₁]? = some (.reuse j₁ p₁) → steps[i₂]? = some (.reuse j₂ p₂) → j₁ = j₂ → i₁ = i₂

private theorem diff_steps_valid_of {msg : Type} {c₁ c₂ : List (Html msg)} {steps : List (KeyedStep msg)}
    (P : (i : Nat) → i < c₂.length → (j : Nat) → j < c₁.length → Prop) (hlen : steps.length = c₂.length)
    (hAt : ∀ (i : Nat) (hi : i < c₂.length),
      steps[i]'(hlen ▸ hi) = .create c₂[i] ∨
      ∃ j, ∃ hj : j < c₁.length, P i hi j hj ∧ steps[i]'(hlen ▸ hi) = .reuse j (diff c₁[j] c₂[i]))
    (hInj : ∀ i₁ i₂ (hi₁ : i₁ < c₂.length) (hi₂ : i₂ < c₂.length) j (hj : j < c₁.length),
      P i₁ hi₁ j hj → P i₂ hi₂ j hj → i₁ = i₂) :
    DiffStepsValid c₁ c₂ steps := by
  have hreuse : ∀ (i : Nat) (hi : i < c₂.length) j p, steps[i]? = some (.reuse j p) →
      ∃ hj : j < c₁.length, P i hi j hj ∧ p = diff c₁[j] c₂[i] := fun i hi j p h => by
    rw [List.getElem?_eq_getElem (hlen ▸ hi)] at h
    rcases hAt i hi with hc | ⟨j', hj', hp, hr⟩
    · rw [hc] at h; cases h
    · rw [hr] at h; cases h; exact ⟨hj', hp, rfl⟩
  refine ⟨hlen, fun i hi => ⟨fun newH h => ?_, fun j p h => let ⟨hj, _, hp⟩ := hreuse i hi j p h; ⟨hj, hp⟩⟩,
    fun i₁ i₂ j₁ j₂ p₁ p₂ hi₁ hi₂ h1 h2 hj => by
      subst hj; rcases hreuse i₁ (hlen ▸ hi₁) j₁ p₁ h1 with ⟨hj₁, hp1, _⟩
      rcases hreuse i₂ (hlen ▸ hi₂) j₁ p₂ h2 with ⟨_, hp2, _⟩
      exact hInj i₁ i₂ (hlen ▸ hi₁) (hlen ▸ hi₂) j₁ hj₁ hp1 hp2⟩
  rw [List.getElem?_eq_getElem (hlen ▸ hi)] at h
  rcases hAt i hi with hc | ⟨_, _, _, hr⟩ <;> (first | rw [hc] at h | rw [hr] at h) <;> cases h; rfl

private theorem diff_steps_valid_pos {msg : Type} {t : String} {a₁ a₂ : List (Attr msg)}
    {c₁ c₂ : List (Html msg)} {steps : List (KeyedStep msg)}
    (hun : validatedKeyIndex c₁ = none ∨ validatedKeyIndex c₂ = none)
    (hdiff : diff (.element t a₁ c₁) (.element t a₂ c₂) = .patchElement a₂ steps) :
    DiffStepsValid c₁ c₂ steps := by
  rcases diff_positional_reuses (t := t) (a₁ := a₁) (a₂ := a₂) hun with ⟨s', hEq, hlen, hAt⟩
  rw [hEq] at hdiff; cases hdiff
  exact diff_steps_valid_of (fun i _ j _ => i = j) hlen
    (fun i hi => by by_cases hc : i < c₁.length; exact .inr ⟨i, hc, rfl, (hAt i hi).1 hc⟩; exact .inl ((hAt i hi).2 (Nat.le_of_not_lt hc)))
    (fun _ _ _ _ _ _ h1 h2 => h1.trans h2.symm)

theorem diff_steps_valid {t : String} {a₁ a₂ : List (Attr msg)} {c₁ c₂ : List (Html msg)} {steps : List (KeyedStep msg)}
    (hdiff : diff (.element t a₁ c₁) (.element t a₂ c₂) = .patchElement a₂ steps) :
    DiffStepsValid c₁ c₂ steps := by
  cases h₁ : validatedKeyIndex c₁ with
  | none => exact diff_steps_valid_pos (Or.inl h₁) hdiff
  | some _ =>
      cases h₂ : validatedKeyIndex c₂ with
      | none => exact diff_steps_valid_pos (Or.inr h₂) hdiff
      | some _ =>
          rcases diff_keyed_reuses (t := t) (a₁ := a₁) (a₂ := a₂) h₁ h₂ with ⟨s', hEq, hlen, hAt⟩
          rw [hEq] at hdiff; cases hdiff
          exact diff_steps_valid_of (fun i hi j hj => ∃ k, c₂[i].keyOf = some k ∧ c₁[j].keyOf = some k) hlen
            (fun i hi => by
              rcases (validatedKeyIndex_spec h₂).2 i hi with ⟨k, hkc₂, _⟩
              by_cases hex : ∃ j, ∃ hj : j < c₁.length, c₁[j].keyOf = some k
              · rcases hex with ⟨j, hj, hkj⟩; exact .inr ⟨j, hj, ⟨k, hkc₂, hkj⟩, (hAt i hi).1 j hj k hkc₂ hkj⟩
              · exact .inl ((hAt i hi).2 k hkc₂ fun j hj hk => hex ⟨j, hj, hk⟩))
            (fun i₁ i₂ hi₁ hi₂ _ _ ⟨k₁, h1, ho1⟩ ⟨k₂, h2, ho2⟩ => by
              rw [ho1] at ho2; cases ho2; exact validatedKeyIndex_inj h₂ hi₁ hi₂ h1 h2)

abbrev PatchSpecOut {msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (oldH newH : Html msg) (node : Dom.Node) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a a' : DomArena msg) : Prop :=
  a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount newH ∧
  (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
  ∃ newNode, (diff oldH newH = .replace newH ∨ newNode = node) ∧
    a'.get parent = .element pns ptag pst pmg (pre ++ newNode :: suf) ∧ (pre ++ newNode :: suf).Nodup ∧
    (∀ r ∈ pre ++ newNode :: suf, r.toNat < a'.nextId) ∧ CleanDomSubtree f childNs newH a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) newNode

def PatchSpecAt {msg : Type} (f : Nat) : Prop :=
  ∀ (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (oldH newH : Html msg) (node : Dom.Node) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg),
    childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") →
    pre.length + 1 + suf.length < UInt32.size → a.nextId + htmlNodeCount newH < UInt32.size → htmlDepth newH ≤ f →
    parent.toNat < a.nextId → 0 < a.nextId → a.get parent = .element pns ptag pst pmg (pre ++ node :: suf) →
    (pre ++ node :: suf).Nodup → ¬Sold parent.toNat → (∀ k, Sold k → k < a.nextId) →
    (∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId) → CleanDomSubtree f childNs oldH a Sold node → newH.DomClean = true →
    PatchSpecOut f childNs parent pns ptag pst pmg oldH newH node pre suf Sold a
      ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (diff oldH newH)).run a).2

abbrev ReconcileStepOut {msg : Type} (f : Nat) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (childNs : String)
    (nSteps sufLen : Nat) (targets targetsDone : List (Html msg)) (pre : List Dom.Node) (Sdone Srem : Nat → Prop) (a aOut : DomArena msg) : Prop :=
  ∃ targetsOut sufRem Snew, targetsOut.length = nSteps ∧ (targetsOut ++ sufRem).length ≤ sufLen + nSteps ∧
    a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount targets ∧
    aOut.get parent = .element pns ptag pst pmg ((pre ++ targetsOut) ++ sufRem) ∧
    (∀ m : Dom.Node, m ≠ parent → ¬Sdone m.toNat → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    (∀ k, Snew k → (Sdone k ∨ Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧
    CleanDomChildren f childNs (targetsDone ++ targets) aOut Snew (pre ++ targetsOut)

abbrev ReconcileStepAt0Out {msg : Type} (f : Nat) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (childNs : String)
    (nSteps domLen : Nat) (c₂ : List (Html msg)) (Srem : Nat → Prop) (a aOut : DomArena msg) : Prop :=
  ∃ targetsOut sufRem Snew, targetsOut.length = nSteps ∧ (targetsOut ++ sufRem).length ≤ domLen + nSteps ∧
    a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount c₂ ∧ aOut.get parent = .element pns ptag pst pmg (targetsOut ++ sufRem) ∧
    (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    (∀ k, Snew k → (Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧ CleanDomChildren f childNs c₂ aOut Snew targetsOut

abbrev ReconcileTailOut {msg : Type} (f : Nat) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (childNs : String)
    (c₂ : List (Html msg)) (Srem : Nat → Prop) (a aOut : DomArena msg) : Prop :=
  ∃ targetsOut Snew, a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount c₂ ∧ aOut.get parent = .element pns ptag pst pmg targetsOut ∧
    (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    (∀ k, Snew k → (Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧ CleanDomChildren f childNs c₂ aOut Snew targetsOut

section
variable {msg : Type} {f : Nat} {parent : Dom.Node} {pns ptag : String}
  {pst : SpecElemState msg} {pmg : List String} {childNs : String}

private theorem reconcile_nil_out {targetsDone : List (Html msg)} {pre suf : List Dom.Node}
    {Sdone Srem : Nat → Prop} {a : DomArena msg}
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ suf))
    (hSdone : ∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId)
    (hDoneC : CleanDomChildren f childNs targetsDone a Sdone pre) :
    ReconcileStepOut f parent pns ptag pst pmg childNs 0 suf.length [] targetsDone pre Sdone Srem a a :=
  ⟨[], suf, Sdone, rfl, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
    by rw [List.append_nil]; exact hpar, fun _ _ _ _ _ => rfl, fun k hk => ⟨.inl hk, (hSdone k hk).1⟩,
    by rw [List.append_nil, List.append_nil]; exact hDoneC⟩

private theorem reconcile_cons_bounds {t : Html msg} {tRest : List (Html msg)}
    {pre suf : List Dom.Node} {sRestLen : Nat} {a : DomArena msg}
    (hclean : Html.DomCleanList (t :: tRest) = true) (hdep : htmlListDepth (t :: tRest) ≤ f)
    (hsz : pre.length + suf.length + (sRestLen + 1) < UInt32.size)
    (hbound : a.nextId + htmlListNodeCount (t :: tRest) < UInt32.size) :
    (t.DomClean = true ∧ Html.DomCleanList tRest = true) ∧ htmlDepth t ≤ f ∧ htmlListDepth tRest ≤ f ∧
    pre.length + 1 < UInt32.size ∧ UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) ∧
    a.nextId + htmlNodeCount t < UInt32.size := by
  simp only [Html.DomCleanList, Bool.and_eq_true] at hclean
  simp only [htmlListDepth] at hdep; simp only [htmlListNodeCount] at hbound
  have hpreLtU : pre.length + 1 < UInt32.size := by omega
  exact ⟨hclean, Nat.le_trans (Nat.le_max_left _ _) hdep, Nat.le_trans (Nat.le_max_right _ _) hdep,
    hpreLtU, uint32_ofNat_succ pre.length hpreLtU, Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right _ _) _) hbound⟩

private theorem cleanChildren_dom_bounds {c₁ c₂ : List (Html msg)} {domCs : List Dom.Node}
    {Srem : Nat → Prop} {a : DomArena msg} {n : Nat}
    (hn : n = c₂.length) (hbound : a.nextId + htmlListNodeCount c₂ < UInt32.size)
    (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) (hCleanCs : CleanDomChildren f childNs c₁ a Srem domCs) :
    (domCs.Nodup ∧ domCs.length = c₁.length) ∧ (∀ r ∈ domCs, r.toNat < a.nextId ∧ r ≠ parent) ∧
    domCs.length ≤ a.nextId ∧ ([] : List Dom.Node).length + domCs.length + n < UInt32.size := by
  have hnd := CleanDomChildren_nodup hCleanCs
  have hsufB : ∀ r ∈ domCs, r.toNat < a.nextId ∧ r ≠ parent := fun r hr =>
    have hb := hSrem r.toNat (CleanDomChildren_mem hCleanCs r hr); ⟨hb.2, node_ne_of_toNat_ne hb.1⟩
  have hdomLe := nodup_nodes_lt_length_le a.nextId domCs hnd.1 fun r hr => (hsufB r hr).1
  have := list_length_le_htmlListNodeCount c₂
  exact ⟨hnd, hsufB, hdomLe, by simp; omega⟩

private theorem clean_build_child
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    {newH : Html msg} {cs : List Dom.Node} {a : DomArena msg}
    (hclean : newH.DomClean = true) (hdep : htmlDepth newH ≤ f)
    (hbound : a.nextId + htmlNodeCount newH < UInt32.size) (hparLt : parent.toNat < a.nextId)
    (hpos : 0 < a.nextId) (hpar : a.get parent = .element pns ptag pst pmg cs) :
    ∃ cn aMid,
      MonadDom.childNamespace (m := StateM (DomArena msg)) parent a = (childNs, a) ∧
      buildDomM (m := StateM (DomArena msg)) childNs newH a = (cn, aMid) ∧
      a.nextId ≤ cn.toNat ∧ cn.toNat < aMid.nextId ∧
      a.nextId ≤ aMid.nextId ∧ aMid.nextId ≤ a.nextId + htmlNodeCount newH ∧
      aMid.get parent = .element pns ptag pst pmg cs ∧
      (∀ m : Dom.Node, m.toNat < a.nextId → aMid.get m = a.get m) ∧
      ∀ e, CleanDomSubtree f childNs newH (aMid.set parent e) (fun k => a.nextId ≤ k ∧ k < aMid.nextId) cn := by
  have hbuild := buildDomM_spec_full childNs newH a f hpos hbound hdep
  dsimp only [StateT.run] at hbuild
  cases hB : buildDomM (m := StateM (DomArena msg)) childNs newH a with
  | mk cn aMid =>
      rw [hB] at hbuild; dsimp only at hbuild
      rcases hbuild with ⟨hge, hlt, hext, _, _, hcl⟩
      have hfr : ∀ m : Dom.Node, m.toNat < a.nextId → aMid.get m = a.get m := fun m hm => hext.frame m hm id
      exact ⟨cn, aMid, by simp [MonadDom.childNamespace, hpar, hchildNs], rfl, hge, hlt, hext.next_ge, hext.next_le,
        by rw [hfr parent hparLt, hpar], hfr, fun e =>
          CleanDomSubtree_frame (fun m _ => DomArena.get_set_ne _ _ fun heq => by subst heq; omega) (hcl hclean)⟩

private theorem clean_create_step
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    {newH : Html msg} {targetsDone : List (Html msg)} {pre suf : List Dom.Node} {Sdone : Nat → Prop} {a : DomArena msg}
    (hclean : newH.DomClean = true) (hdep : htmlDepth newH ≤ f)
    (hsz : pre.length + suf.length + 1 < UInt32.size) (hbound : a.nextId + htmlNodeCount newH < UInt32.size)
    (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId) (hpar : a.get parent = .element pns ptag pst pmg (pre ++ suf))
    (hnd : (pre ++ suf).Nodup) (hSdone : ∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId)
    (hDoneC : CleanDomChildren f childNs targetsDone a Sdone pre) (hsufB : ∀ r ∈ suf, r.toNat < a.nextId ∧ r ≠ parent) :
    ∃ cn aIns,
      (∀ {α} (k : StateM (DomArena msg) α),
        (do let ns ← MonadDom.childNamespace parent; let cn' ← buildDomM ns newH
            MonadDom.insertBeforeNode parent (UInt32.ofNat pre.length) cn'; k) a = k aIns) ∧
      a.nextId ≤ aIns.nextId ∧ aIns.nextId ≤ a.nextId + htmlNodeCount newH ∧
      aIns.get parent = .element pns ptag pst pmg ((pre ++ [cn]) ++ suf) ∧ ((pre ++ [cn]) ++ suf).Nodup ∧
      (∀ m : Dom.Node, m ≠ parent → m.toNat < a.nextId → aIns.get m = a.get m) ∧
      CleanDomChildren f childNs (targetsDone ++ [newH]) aIns (fun k => Sdone k ∨ (a.nextId ≤ k ∧ k < aIns.nextId)) (pre ++ [cn]) := by
  rcases clean_build_child hchildNs hclean hdep hbound hparLt hposId hpar with
    ⟨cn, aMid, hns, hB, hge, _, haGe, haLe, hparMid, hfr, hcl⟩
  have hcnNotIn : cn ∉ pre ++ suf := fun hm => by
    rcases List.mem_append.1 hm with hp | hs
    · have := (hSdone _ (CleanDomChildren_mem hDoneC cn hp)).2; omega
    · have := (hsufB cn hs).1; omega
  let aIns := aMid.set parent (.element pns ptag pst pmg ((pre ++ [cn]) ++ suf))
  have hinsRun : MonadDom.insertBeforeNode (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) cn aMid = ((), aIns) := by
    simp only [MonadDom.insertBeforeNode, DomArena.modifyChildren, DomArena.modify, hparMid,
               uint32_toNat_ofNat_lt pre.length (by omega), keyed_step_insertBefore_create pre suf cn hnd hcnNotIn,
               aIns, List.append_assoc, List.singleton_append]
  have hDoneIns : CleanDomChildren f childNs targetsDone aIns Sdone pre :=
    CleanDomChildren_frame (fun m hm => by
      rw [DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSdone _ hm).1)]; exact hfr m (hSdone _ hm).2) hDoneC
  have hDone' := CleanDomChildren_append (fun k hk1 hk2 => by have := (hSdone k hk1).2; omega) hDoneIns
    (show CleanDomChildren f childNs [newH] aIns (fun k => a.nextId ≤ k ∧ k < aIns.nextId) [cn] from
      ⟨fun k => a.nextId ≤ k ∧ k < aIns.nextId, fun _ => False, fun _ h => h, fun _ h => h.elim, fun _ _ h => h.elim, hcl _, trivial⟩)
  exact ⟨cn, aIns, fun k => by dsimp only [bind]; rw [stateM_bind_step hns, stateM_bind_step hB, stateM_bind_step hinsRun],
    haGe, haLe, DomArena.get_set_self _ _ _, nodup_snoc_append hnd hcnNotIn,
    fun m hmPar hmLt => by rw [DomArena.get_set_ne _ _ hmPar, hfr m hmLt], hDone'⟩

private theorem clean_reuse_step (hPatch : @PatchSpecAt msg f)
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    {cOld t : Html msg} {targetsDone : List (Html msg)} {child : Dom.Node} {pre sufRest : List Dom.Node}
    {Sdone Sc : Nat → Prop} {a a1 : DomArena msg}
    (ha1Next : a1.nextId = a.nextId) (hfr1 : ∀ m : Dom.Node, m ≠ parent → a1.get m = a.get m)
    (hsz : pre.length + 1 + sufRest.length < UInt32.size) (htBound : a.nextId + htmlNodeCount t < UInt32.size)
    (htDep : htmlDepth t ≤ f) (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId)
    (hpar1 : a1.get parent = .element pns ptag pst pmg (pre ++ child :: sufRest)) (hnd1 : (pre ++ child :: sufRest).Nodup)
    (hSdone : ∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId) (hScB : ∀ k, Sc k → k ≠ parent.toNat ∧ k < a.nextId)
    (hDisj : ∀ k, Sdone k → Sc k → False) (hDoneC : CleanDomChildren f childNs targetsDone a Sdone pre)
    (hsufB1 : ∀ r ∈ child :: sufRest, r.toNat < a.nextId) (hcClean1 : CleanDomSubtree f childNs cOld a1 Sc child) (htClean : t.DomClean = true) :
    let aMid := (applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff cOld t) a1).2
    let Sdone' : Nat → Prop := fun k => Sdone k ∨ (Sc k ∨ (a.nextId ≤ k ∧ k < aMid.nextId))
    ∃ newChild, a.nextId ≤ aMid.nextId ∧ aMid.nextId ≤ a.nextId + htmlNodeCount t ∧
      aMid.get parent = .element pns ptag pst pmg ((pre ++ [newChild]) ++ sufRest) ∧ ((pre ++ [newChild]) ++ sufRest).Nodup ∧
      (∀ m : Dom.Node, m ≠ parent → ¬Sc m.toNat → m.toNat < a.nextId → aMid.get m = a.get m) ∧
      (∀ k, Sdone' k → k ≠ parent.toNat ∧ k < aMid.nextId) ∧ CleanDomChildren f childNs (targetsDone ++ [t]) aMid Sdone' (pre ++ [newChild]) := by
  have hParNodes1 : ∀ r ∈ pre ++ child :: sufRest, r.toNat < a1.nextId := fun r hr => by
    rw [ha1Next]; rcases List.mem_append.1 hr with hp | hc
    · exact (hSdone _ (CleanDomChildren_mem hDoneC r hp)).2
    · exact hsufB1 r hc
  have hPatchC := hPatch childNs parent pns ptag pst pmg cOld t child pre sufRest Sc a1
    hchildNs hsz (ha1Next ▸ htBound) htDep (ha1Next ▸ hparLt) (ha1Next ▸ hposId) hpar1 hnd1
    (fun h => (hScB parent.toNat h).1 rfl) (fun k hk => ha1Next ▸ (hScB k hk).2) hParNodes1 hcClean1 htClean
  dsimp only [PatchSpecOut, StateT.run] at hPatchC
  rcases hPatchC with ⟨haMidLe, haMidBound, hframeMid, newChild, _, hparMid, hndMid, _, hcNew⟩
  rw [ha1Next] at haMidLe haMidBound hframeMid hcNew
  have hframe : ∀ m : Dom.Node, m ≠ parent → ¬Sc m.toNat → m.toNat < a.nextId →
      (applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff cOld t) a1).2.get m = a.get m :=
    fun m hmPar hsc hmLt => (hframeMid m hmPar hsc hmLt).trans (hfr1 m hmPar)
  have ⟨hSdone', hDone'⟩ := clean_done_extend haMidLe hparLt hSdone hScB hDisj
    (fun m hm => hframe m (node_ne_of_toNat_ne (hSdone _ hm).1) (fun hsc => hDisj _ hm hsc) (hSdone _ hm).2) hDoneC hcNew
  exact ⟨newChild, haMidLe, haMidBound, by rw [List.append_assoc, List.singleton_append]; exact hparMid,
    by rw [List.append_assoc, List.singleton_append]; exact hndMid, hframe, hSdone', hDone'⟩

private theorem clean_step_reconcile_combine {nRest sufRestLen sufLen : Nat} {t : Html msg} {tRest targetsDone : List (Html msg)}
    {pre : List Dom.Node} {newChild : Dom.Node} {Sdone Sdone' Srem Srest : Nat → Prop} {a aMid aOut : DomArena msg}
    (hsufLe : sufRestLen ≤ sufLen) (haMidLe : a.nextId ≤ aMid.nextId) (haMidBound : aMid.nextId ≤ a.nextId + htmlNodeCount t)
    (hSr : ∀ k, Srest k → Srem k) (hSdone'Sub : ∀ k, Sdone' k → Sdone k ∨ Srem k ∨ (a.nextId ≤ k ∧ k < aMid.nextId))
    (hNotSdone' : ∀ k, ¬Sdone k → ¬Srem k → k < a.nextId → ¬Sdone' k)
    (hframeMid : ∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aMid.get m = a.get m)
    (hih : ReconcileStepOut f parent pns ptag pst pmg childNs nRest sufRestLen tRest (targetsDone ++ [t]) (pre ++ [newChild]) Sdone' Srest aMid aOut) :
    ReconcileStepOut f parent pns ptag pst pmg childNs (nRest + 1) sufLen (t :: tRest) targetsDone pre Sdone Srem a aOut := by
  rcases hih with ⟨targetsRest, sufRem, Snew, hlenR, htotLenR, hmonoR, hboundR, hparR, hfrR, hSnew, hDoneR⟩
  simp only [List.append_assoc, List.singleton_append] at hparR hDoneR
  refine ⟨newChild :: targetsRest, sufRem, Snew, congrArg Nat.succ hlenR,
    by simp only [List.cons_append, List.length_cons] at htotLenR ⊢; omega,
    Nat.le_trans haMidLe hmonoR,
    by simp only [htmlListNodeCount]; exact Nat.le_trans hboundR (Nat.add_assoc _ _ _ ▸ Nat.add_le_add_right haMidBound _),
    by simp only [List.append_assoc]; exact hparR,
    fun m hmPar hmD hmR hmLt => (hfrR m hmPar (hNotSdone' _ hmD hmR hmLt) (fun hr => hmR (hSr _ hr)) (Nat.lt_of_lt_of_le hmLt haMidLe)).trans (hframeMid m hmPar hmR hmLt),
    fun k hk => by
      rcases hSnew k hk with ⟨h1 | h2 | ⟨hlo, hhi⟩, hnp⟩
      · exact ⟨(hSdone'Sub k h1).imp id (fun h => h.imp id (fun ⟨h1, h2⟩ => ⟨h1, Nat.lt_of_lt_of_le h2 hmonoR⟩)), hnp⟩
      · exact ⟨.inr (.inl (hSr k h2)), hnp⟩
      · exact ⟨.inr (.inr ⟨Nat.le_trans haMidLe hlo, hhi⟩), hnp⟩, hDoneR⟩

private theorem no_reuse_of_allCreates_top :
    ∀ (xs : List (KeyedStep msg)) (k idx : Nat) (p : Patch msg), allCreates xs = true → xs[k]? = some (.reuse idx p) → False
  | [], _, _, _, _, h => by simp at h
  | .reuse _ _ :: _, _, _, _, hc, _ => by simp [allCreates] at hc
  | .create _ :: _, 0, _, _, _, h => by simp at h
  | .create _ :: sr, k + 1, idx, p, hc, h => no_reuse_of_allCreates_top sr k idx p hc (by simpa using h)

private def PosStepsMatch (base : Nat) (steps : List (KeyedStep msg)) (targets oldRem : List (Html msg)) : Prop :=
  ∀ (k : Nat) (hk : k < targets.length),
    (∀ newH, steps[k]? = some (.create newH) → newH = targets[k]) ∧
    (∀ idx p, steps[k]? = some (.reuse idx p) → idx = base + k ∧ ∃ c, oldRem[k]? = some c ∧ p = diff c targets[k])

private def PosSufClean (f : Nat) (ns : String) :
    List (KeyedStep msg) → List (Html msg) → DomArena msg → (Nat → Prop) → List Dom.Node → Prop
  | .reuse _ _ :: _, oldRem, a, Srem, suf => CleanDomChildren f ns oldRem a Srem suf
  | _, _, _, _, _ => True

private theorem applyPositionalStepsM_clean_step (hPatch : @PatchSpecAt msg f)
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (steps : List (KeyedStep msg)) (targets targetsDone oldRem : List (Html msg))
    (pre suf : List Dom.Node) (Sdone Srem : Nat → Prop) (a : DomArena msg)
    (hlen : steps.length = targets.length) (hpos : positional pre.length steps = true)
    (hmatch : PosStepsMatch pre.length steps targets oldRem)
    (hclean : Html.DomCleanList targets = true) (hdep : htmlListDepth targets ≤ f)
    (hsz : pre.length + suf.length + steps.length < UInt32.size)
    (hbound : a.nextId + htmlListNodeCount targets < UInt32.size) (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ suf)) (hnd : (pre ++ suf).Nodup)
    (hSdone : ∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId) (hDoneC : CleanDomChildren f childNs targetsDone a Sdone pre)
    (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) (hDisj : ∀ k, Sdone k → Srem k → False)
    (hsufB : ∀ r ∈ suf, r.toNat < a.nextId ∧ r ≠ parent) (hsufC : PosSufClean f childNs steps oldRem a Srem suf) :
    ReconcileStepOut f parent pns ptag pst pmg childNs steps.length suf.length targets targetsDone pre Sdone Srem a
      ((applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) steps).run a).2 := by
  induction steps generalizing targets targetsDone oldRem pre suf Sdone Srem a with
  | nil =>
      cases targets with
      | cons _ _ => cases hlen
      | nil => exact reconcile_nil_out hpar hSdone hDoneC
  | cons step sRest ih =>
      cases targets with
      | nil => cases hlen
      | cons t tRest =>
          simp only [List.length_cons] at hlen hsz
          have hlen' : sRest.length = tRest.length := Nat.succ.inj hlen
          rcases reconcile_cons_bounds hclean hdep hsz hbound with ⟨hclean, htDep, hrestDep, hpreLtU, huJNext, htBound⟩
          have hStep0 := hmatch 0 (Nat.zero_lt_succ _)
          simp only [List.getElem_cons_zero] at hStep0
          cases step with
          | reuse oldIdx p =>
              simp only [PosSufClean] at hsufC
              simp only [positional, Bool.and_eq_true, beq_iff_eq] at hpos
              rcases hStep0.2 oldIdx p rfl with ⟨hIdxEq, cOld, hcOld0, hpEq⟩; subst hpEq
              cases oldRem with
              | nil => cases hcOld0
              | cons cO oldRest =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at hcOld0; subst hcOld0
                  cases suf with
                  | nil => exact False.elim hsufC
                  | cons child sufRest =>
                      simp only [List.length_cons] at hsz
                      rcases hsufC with ⟨Sc, Srest, hSc, hSr, hDSr, hcClean, hSufClean⟩
                      have hchildAt := positional_step_reuse_tail parent pns ptag pst pmg pre child sufRest a (Nat.lt_of_le_of_lt (Nat.le_succ _) hpreLtU)
                      dsimp only [StateT.run] at hchildAt
                      let aMid := (applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff cO t) a).2
                      rcases clean_reuse_step hPatch hchildNs rfl (fun _ _ => rfl) (by omega) htBound htDep hparLt hposId hpar hnd hSdone
                        (fun k h => hSrem k (hSc k h)) (fun k h1 h2 => hDisj k h1 (hSc k h2)) hDoneC (fun r hr => (hsufB r hr).1) hcClean hclean.1 with
                        ⟨newChild, haMidLe, haMidBound, hparMid, hndMid, hframeMid, hSdone', hDone'⟩
                      have hih := ih tRest (targetsDone ++ [t]) oldRest (pre ++ [newChild]) sufRest _ Srest aMid
                        hlen' (by rw [List.length_append, List.length_singleton]; exact hpos.2)
                        (fun k hk => by
                          have hm' := hmatch (k + 1) (Nat.succ_lt_succ hk)
                          simp only [List.getElem?_cons_succ, List.getElem_cons_succ, List.length_append, List.length_singleton] at hm' ⊢
                          exact ⟨hm'.1, fun idx' p' hs => let hr := hm'.2 idx' p' hs; ⟨by omega, hr.2⟩⟩)
                        hclean.2 hrestDep (by simp only [List.length_append, List.length_singleton]; omega)
                        (Nat.lt_of_le_of_lt (Nat.add_le_add_right haMidBound _) (Nat.add_assoc _ _ _ ▸ hbound))
                        (Nat.lt_of_lt_of_le hparLt haMidLe) (Nat.lt_of_lt_of_le hposId haMidLe) hparMid hndMid hSdone' hDone'
                        (fun k hk => have hb := hSrem k (hSr k hk); ⟨hb.1, Nat.lt_of_lt_of_le hb.2 haMidLe⟩)
                        (fun k hk1 hk2 => not_Sdone_extend (fun h1 => hDisj k h1 (hSr k hk2)) (fun h => hDSr k h hk2) (hSrem k (hSr k hk2)).2 hk1)
                        (fun r hr => have hb := hsufB r (.tail _ hr); ⟨Nat.lt_of_lt_of_le hb.1 haMidLe, hb.2⟩)
                        (by cases sRest with | nil => trivial | cons stp _ => cases stp with | create _ => trivial | reuse _ _ =>
                          exact CleanDomChildren_frame (fun m hm => hframeMid m (node_ne_of_toNat_ne (hSrem _ (hSr _ hm)).1) (fun hsc => hDSr _ hsc hm) (hSrem _ (hSr _ hm)).2) hSufClean)
                      dsimp only [StateT.run] at hih ⊢
                      rw [show applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) (.reuse oldIdx (diff cO t) :: sRest) a =
                          applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (pre ++ [newChild]).length) sRest aMid from by
                        dsimp only [applyPositionalStepsM, bind]; rw [DomArena.set_get_self a hpar] at hchildAt
                        rw [stateM_bind_step hchildAt, stateM_bind_step (show applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff cO t) a = ((), aMid) from rfl)]
                        simp only [List.length_append, List.length_singleton, huJNext]]
                      exact clean_step_reconcile_combine (Nat.le_succ _) haMidLe haMidBound hSr
                        (fun k hk => hk.imp id (fun h => h.imp (hSc k) id))
                        (fun k hD hR hLt => not_Sdone_extend hD (fun hsc => hR (hSc k hsc)) hLt)
                        (fun m hmPar hmR hmLt => hframeMid m hmPar (fun hsc => hmR (hSc _ hsc)) hmLt) hih
          | create newH =>
              simp only [positional] at hpos
              have htEq : newH = t := hStep0.1 newH rfl
              rcases clean_create_step hchildNs hclean.1 htDep (by omega) htBound hparLt hposId hpar hnd hSdone hDoneC hsufB with
                ⟨cn, aIns, hrun, haInsGe, haInsLe, hparIns, hnd', hfrIns, hDone'⟩
              have hih := ih tRest (targetsDone ++ [t]) [] (pre ++ [cn]) suf (fun k => Sdone k ∨ (a.nextId ≤ k ∧ k < aIns.nextId)) Srem aIns
                hlen' (by cases sRest with | nil => rfl | cons s0 _ => cases s0 with | reuse _ _ => cases hpos | create _ => exact hpos)
                (fun k hk => by
                  have hm := hmatch (k + 1) (Nat.succ_lt_succ hk)
                  simp only [List.getElem?_cons_succ, List.getElem_cons_succ] at hm
                  exact ⟨hm.1, fun idx' p' hs => False.elim (no_reuse_of_allCreates_top sRest k idx' p' hpos hs)⟩)
                hclean.2 hrestDep (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
                (Nat.lt_of_le_of_lt (Nat.add_le_add_right haInsLe _) (Nat.add_assoc _ _ _ ▸ hbound))
                (Nat.lt_of_lt_of_le hparLt haInsGe) (Nat.lt_of_lt_of_le hposId haInsGe) hparIns hnd'
                (clean_done_alloc_bounds haInsGe hparLt hSdone) hDone'
                (fun k hk => have hb := hSrem k hk; ⟨hb.1, Nat.lt_of_lt_of_le hb.2 haInsGe⟩)
                (fun k hk1 hk2 => hk1.elim (fun h => hDisj k h hk2) (fun hhi => Nat.not_lt.2 hhi.1 (hSrem k hk2).2))
                (fun r hr => have hb := hsufB r hr; ⟨Nat.lt_of_lt_of_le hb.1 haInsGe, hb.2⟩)
                (by cases sRest with | nil => trivial | cons s0 _ => cases s0 with | create _ => trivial | reuse _ _ => cases hpos)
              dsimp only [StateT.run] at hih ⊢
              rw [show applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) (.create newH :: sRest) a =
                  applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (pre ++ [cn]).length) sRest aIns from by
                rw [htEq]; dsimp only [applyPositionalStepsM]; rw [hrun]; simp only [List.length_append, List.length_singleton, huJNext]]
              exact clean_step_reconcile_combine (Nat.le_refl _) haInsGe haInsLe (fun _ h => h)
                (fun _ hk => hk.imp id .inr) (fun _ hD _ hLt h => h.elim hD (fun hlo => Nat.not_lt.2 hlo.1 hLt))
                (fun m hmPar _ hmLt => hfrIns m hmPar hmLt) hih

private theorem replace_child_clean
    {newH : Html msg} {node : Dom.Node} {pre suf : List Dom.Node} {Sold : Nat → Prop} {a : DomArena msg}
    (hchildNs : childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else ""))
    (hpreLen : pre.length + 1 + suf.length < UInt32.size) (hbound : a.nextId + htmlNodeCount newH < UInt32.size)
    (hdep : htmlDepth newH ≤ f) (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ node :: suf)) (hnd : (pre ++ node :: suf).Nodup)
    (_hSoldLt : ∀ k, Sold k → k < a.nextId) (hparNodesLt : ∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId) (hcleanNew : newH.DomClean = true) :
    let a' := ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (.replace newH)).run a).2
    a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount newH ∧
    (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
    ∃ newNode,
      (StateT.bind (MonadDom.childNamespace (m := StateM (DomArena msg)) parent) fun ns' =>
        StateT.bind (buildDomM (m := StateM (DomArena msg)) ns' newH) fun n2' =>
        StateT.bind (MonadDom.replaceChild (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) n2') fun _ => StateT.pure n2') a = (newNode, a') ∧
      a'.get parent = .element pns ptag pst pmg (pre ++ newNode :: suf) ∧ (pre ++ newNode :: suf).Nodup ∧
      (∀ r ∈ pre ++ newNode :: suf, r.toNat < a'.nextId) ∧ CleanDomSubtree f childNs newH a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) newNode := by
  rcases clean_build_child hchildNs hcleanNew hdep hbound hparLt hpos hpar with
    ⟨n2, aMid, hns, hB, hn2Ge, hn2Lt, haGe, haLe, hparMid, hfr, hcl⟩
  let a' := aMid.set parent (.element pns ptag pst pmg (pre ++ n2 :: suf))
  have hrep : MonadDom.replaceChild (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) n2 aMid = ((), a') := by
    simp [MonadDom.replaceChild, DomArena.modifyChildren, DomArena.modify, hparMid, uint32_toNat_ofNat_lt pre.length (by omega), listReplaceAt_append_middle, a']
  have hrun : applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (.replace newH) a = ((), a') := by
    dsimp only [applyToDomM, bind]; rw [stateM_bind_step hns, stateM_bind_step hB, hrep]
  dsimp only [StateT.run]; rw [hrun]
  have hn2NotIn : n2 ∉ pre ++ node :: suf := fun hm => by have := hparNodesLt n2 hm; omega
  refine ⟨haGe, haLe, fun m hmPar _ hmLt => by rw [DomArena.get_set_ne _ _ hmPar, hfr m hmLt],
    n2, by rw [stateM_bind_step hns, stateM_bind_step hB, stateM_bind_step hrep]; rfl,
    DomArena.get_set_self _ _ _, nodup_append_replace hnd (.inr hn2NotIn), fun r hr => ?_, CleanDomSubtree_mono (fun _ hk => .inr hk) (hcl _)⟩
  rcases List.mem_append.1 hr with hp | hc
  · exact Nat.lt_of_lt_of_le (hparNodesLt r (List.mem_append_left _ hp)) haGe
  · rcases List.mem_cons.1 hc with rfl | hs
    · exact hn2Lt
    · exact Nat.lt_of_lt_of_le (hparNodesLt r (List.mem_append_right _ (.tail _ hs))) haGe

private theorem positional_reuse_idx :
    ∀ (base : Nat) (steps : List (KeyedStep msg)) (k idx : Nat) (p : Patch msg),
      positional base steps = true → steps[k]? = some (.reuse idx p) → idx = base + k
  | _, [], _, _, _, _, h => by simp at h
  | _, .create _ :: _, 0, _, _, _, h => by simp at h
  | _, .create _ :: rest, k + 1, idx, p, hpos, h => False.elim (no_reuse_of_allCreates_top rest k idx p hpos (by simpa using h))
  | base, .reuse j _ :: _, 0, idx, _, hpos, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq, KeyedStep.reuse.injEq] at h
      simp only [positional, Bool.and_eq_true, beq_iff_eq] at hpos; omega
  | base, .reuse _ _ :: rest, k + 1, idx, p, hpos, h => by
      simp only [positional, Bool.and_eq_true] at hpos
      have := positional_reuse_idx (base + 1) rest k idx p hpos.2 (by simpa using h); omega

private theorem mem_of_diff_children_nodup (c₁ : List (Html msg)) (liveCs : List Dom.Node)
    (hnd : liveCs.Nodup) (hlen : liveCs.length = c₁.length) :
    ∀ i₁ i₂, i₁ < c₁.length → i₂ < c₁.length →
      ({ toList := liveCs } : Array Dom.Node).getD i₁ 0 = ({ toList := liveCs } : Array Dom.Node).getD i₂ 0 → i₁ = i₂ :=
  fun i₁ i₂ hi₁ hi₂ hEq => by
    simp [Array.getD, hlen, hi₁, hi₂] at hEq
    exact nodup_getElem_inj (hlen ▸ hi₁) (hlen ▸ hi₂) hnd hEq

private theorem applyPositionalStepsM_clean_at0 (hPatch : @PatchSpecAt msg f)
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (steps : List (KeyedStep msg)) (c₁ c₂ : List (Html msg)) (domCs : List Dom.Node) (Srem : Nat → Prop) (a : DomArena msg)
    (hsteps : steps.length = c₂.length) (hpos : positional 0 steps = true) (hvalid : DiffStepsValid c₁ c₂ steps)
    (hclean : Html.DomCleanList c₂ = true) (hdep : htmlListDepth c₂ ≤ f) (hbound : a.nextId + htmlListNodeCount c₂ < UInt32.size)
    (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId) (hpar : a.get parent = .element pns ptag pst pmg domCs)
    (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) (hCleanCs : CleanDomChildren f childNs c₁ a Srem domCs) :
    ReconcileStepAt0Out f parent pns ptag pst pmg childNs steps.length domCs.length c₂ Srem a
      ((applyPositionalStepsM (m := StateM (DomArena msg)) parent 0 steps).run a).2 := by
  rcases cleanChildren_dom_bounds hsteps hbound hSrem hCleanCs with ⟨hnd, hsufB, _, hsz⟩
  have hMatch : PosStepsMatch 0 steps c₂ c₁ := fun k hk =>
    ⟨(hvalid.2.1 k hk).1, fun j p hsk => by
      have hjEq := positional_reuse_idx 0 steps k j p hpos hsk
      rcases (hvalid.2.1 k hk).2 j p hsk with ⟨hj, hp⟩; simp only [Nat.zero_add] at hjEq; subst hjEq
      exact ⟨(Nat.zero_add j).symm, c₁[j], List.getElem?_eq_getElem hj, hp⟩⟩
  have hSufC : PosSufClean f childNs steps c₁ a Srem domCs := by
    cases steps with | nil => trivial | cons stp _ => cases stp with | create _ => trivial | reuse _ _ => exact hCleanCs
  simpa [ReconcileStepOut, ReconcileStepAt0Out] using applyPositionalStepsM_clean_step hPatch hchildNs
    steps c₂ [] c₁ [] domCs (fun _ => False) Srem a hsteps hpos hMatch hclean hdep hsz hbound hparLt hposId
    hpar (by simpa using hnd.1) (fun _ h => h.elim) trivial hSrem (fun _ h => h.elim) hsufB hSufC

private theorem finish_reconcile_removeTail {nSteps domLen : Nat} {c₂ : List (Html msg)} {Srem : Nat → Prop}
    {a aMid : DomArena msg} (hsize : domLen + nSteps < UInt32.size)
    (hstep : ReconcileStepAt0Out f parent pns ptag pst pmg childNs nSteps domLen c₂ Srem a aMid) :
    ReconcileTailOut f parent pns ptag pst pmg childNs c₂ Srem a
      ((do let count ← MonadDom.childCount parent; removeTailM (m := StateM (DomArena msg)) parent (UInt32.ofNat nSteps) (count.toNat - nSteps)).run aMid).2 := by
  rcases hstep with ⟨targetsOut, sufRem, Snew, hlenT, htotLen, haMidLe, haMidBound, hnodeMid, hfrMid, hSnew, hCleanOut⟩
  simp only [List.length_append] at htotLen
  have hremTail := positional_removeTail_spec aMid parent pns ptag pst pmg targetsOut sufRem (by omega)
  rw [DomArena.set_get_self aMid hnodeMid] at hremTail
  dsimp only [ReconcileTailOut, StateT.run] at hremTail ⊢; rw [← hlenT, hremTail]
  exact ⟨targetsOut, Snew, haMidLe, haMidBound, DomArena.get_set_self _ _ _,
    fun m hmPar hmS hmLt => by rw [DomArena.get_set_ne _ _ hmPar]; exact hfrMid m hmPar hmS hmLt,
    hSnew, CleanDomChildren_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSnew m.toNat hm).2)) hCleanOut⟩

private theorem applyPositionalStepsM_with_removeTail (hPatch : @PatchSpecAt msg f)
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (steps : List (KeyedStep msg)) (c₁ c₂ : List (Html msg)) (domCs : List Dom.Node) (Srem : Nat → Prop) (a : DomArena msg)
    (hsteps : steps.length = c₂.length) (hpos : positional 0 steps = true) (hvalid : DiffStepsValid c₁ c₂ steps)
    (hclean : Html.DomCleanList c₂ = true) (hdep : htmlListDepth c₂ ≤ f) (hbound : a.nextId + htmlListNodeCount c₂ < UInt32.size)
    (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId) (hpar : a.get parent = .element pns ptag pst pmg domCs)
    (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) (hCleanCs : CleanDomChildren f childNs c₁ a Srem domCs) :
    ReconcileTailOut f parent pns ptag pst pmg childNs c₂ Srem a
      ((do applyPositionalStepsM (m := StateM (DomArena msg)) parent 0 steps; let count ← MonadDom.childCount parent; removeTailM parent (UInt32.ofNat steps.length) (count.toNat - steps.length)).run a).2 := by
  rcases cleanChildren_dom_bounds hsteps hbound hSrem hCleanCs with ⟨_, _, _, hsz⟩
  have hres := applyPositionalStepsM_clean_at0 hPatch hchildNs
    steps c₁ c₂ domCs Srem a hsteps hpos hvalid hclean hdep hbound hparLt hposId hpar hSrem hCleanCs
  have hfin := finish_reconcile_removeTail (by simp at hsz; omega) hres
  dsimp only [StateT.run, bind, StateT.bind] at hfin ⊢
  cases hP : applyPositionalStepsM (m := StateM (DomArena msg)) parent 0 steps a with
  | mk _ aMid => rw [hP] at hfin; exact hfin

end

def KeyedCleanMatch {msg : Type} (c₁ : List (Html msg)) (usedIdxs : List Nat)
    (steps : List (KeyedStep msg)) (targets : List (Html msg)) : Prop :=
  (∀ (i : Nat) (hi : i < targets.length),
    (∀ newH, steps[i]? = some (.create newH) → newH = targets[i]) ∧
    (∀ j p, steps[i]? = some (.reuse j p) → j ∉ usedIdxs ∧ ∃ _ : j < c₁.length, p = diff c₁[j] targets[i])) ∧
  ∀ i₁ i₂ j₁ j₂ p₁ p₂, i₁ < steps.length → i₂ < steps.length →
    steps[i₁]? = some (.reuse j₁ p₁) → steps[i₂]? = some (.reuse j₂ p₂) → j₁ = j₂ → i₁ = i₂

theorem applyKeyedStepsM_reconcile_spec {msg : Type} (f : Nat) (hPatch : @PatchSpecAt msg f)
    (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (childNs : String) (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (c₁ : List (Html msg)) (live : Array Dom.Node) (Si : Nat → Nat → Prop) (baseLimit : Nat) (_hliveLen : live.size = c₁.length)
    (hSiB : ∀ i k, Si i k → k ≠ parent.toNat ∧ k < baseLimit) (hSiDisj : ∀ i₁ i₂, i₁ ≠ i₂ → ∀ k, Si i₁ k → Si i₂ k → False)
    (hliveInj : ∀ i₁ i₂, i₁ < c₁.length → i₂ < c₁.length → live.getD i₁ 0 = live.getD i₂ 0 → i₁ = i₂)
    (steps : List (KeyedStep msg)) (targets targetsDone : List (Html msg)) (usedIdxs : List Nat)
    (pre suf : List Dom.Node) (Sdone : Nat → Prop) (a : DomArena msg)
    (hlen : steps.length = targets.length) (hkm : KeyedCleanMatch c₁ usedIdxs steps targets)
    (hclean : Html.DomCleanList targets = true) (hdep : htmlListDepth targets ≤ f)
    (hsz : pre.length + suf.length + steps.length < UInt32.size)
    (hbase : baseLimit ≤ a.nextId) (hbound : a.nextId + htmlListNodeCount targets < UInt32.size)
    (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ suf)) (hnd : (pre ++ suf).Nodup)
    (hSdone : ∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId) (hDoneC : CleanDomChildren f childNs targetsDone a Sdone pre)
    (hLive : ∀ (i : Nat) (hi : i < c₁.length), i ∉ usedIdxs → live.getD i 0 ∈ suf ∧ CleanDomSubtree f childNs c₁[i] a (Si i) (live.getD i 0))
    (hDisj : ∀ i, i ∉ usedIdxs → ∀ k, Si i k → Sdone k → False) (hsufB : ∀ r ∈ suf, r.toNat < a.nextId ∧ r ≠ parent) :
    let (finalJ, aOut) := (applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat pre.length) steps).run a
    finalJ.toNat = pre.length + steps.length ∧
    ReconcileStepOut f parent pns ptag pst pmg childNs steps.length suf.length targets targetsDone pre Sdone (fun k => ∃ i, Si i k) a aOut := by
  induction steps generalizing targets targetsDone usedIdxs pre suf Sdone a with
  | nil =>
      cases targets with
      | cons _ _ => cases hlen
      | nil =>
          exact ⟨uint32_toNat_ofNat_lt pre.length (by simp only [List.length_nil] at hsz; omega),
            reconcile_nil_out hpar hSdone hDoneC⟩
  | cons step sRest ih =>
      cases targets with
      | nil => cases hlen
      | cons t tRest =>
          simp only [List.length_cons] at hlen hsz
          have hlen' : sRest.length = tRest.length := Nat.succ.inj hlen
          rcases reconcile_cons_bounds hclean hdep hsz hbound with ⟨hclean, htDep, hrestDep, hpreLtU, huJNext, htBound⟩
          have hStep0 := hkm.1 0 (Nat.zero_lt_succ _)
          simp only [List.getElem_cons_zero] at hStep0
          cases step with
          | reuse oldIdx p =>
              rcases hStep0.2 oldIdx p rfl with ⟨hOldNotUsed, hOldLt, hpEq⟩; subst hpEq
              rcases hLive oldIdx hOldLt hOldNotUsed with ⟨hChildSuf, hChildClean⟩
              let child := live.getD oldIdx 0
              have hChildNotPre : child ∉ pre := fun hp => (List.nodup_append.1 hnd).2.2 child hp child hChildSuf rfl
              let a1 := a.set parent (.element pns ptag pst pmg (pre ++ child :: suf.erase child))
              have hparIns : MonadDom.insertBeforeNode (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child a = ((), a1) := by
                simp only [MonadDom.insertBeforeNode, DomArena.modifyChildren, DomArena.modify, hpar,
                           uint32_toNat_ofNat_lt pre.length (Nat.lt_of_le_of_lt (Nat.le_succ _) hpreLtU),
                           w3cInsertBefore_step pre suf child hnd hChildNotPre, a1]
              have hnd1 : (pre ++ child :: suf.erase child).Nodup := by
                have h := nodup_move_to_pre hnd hChildSuf (.inl rfl)
                rw [List.append_assoc, List.singleton_append] at h; exact h
              have hChildClean1 : CleanDomSubtree f childNs c₁[oldIdx] a1 (Si oldIdx) child :=
                CleanDomSubtree_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSiB oldIdx m.toNat hm).1)) hChildClean
              have hEraseLe : (suf.erase child).length ≤ suf.length := List.length_erase_le
              let aMid := (applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff c₁[oldIdx] t) a1).2
              rcases clean_reuse_step (a := a) (a1 := a1) hPatch hchildNs rfl (fun _ hm => DomArena.get_set_ne _ _ hm) (by omega) htBound htDep hparLt hposId
                (DomArena.get_set_self _ _ _) hnd1 hSdone (fun k h => let hb := hSiB _ k h; ⟨hb.1, Nat.lt_of_lt_of_le hb.2 hbase⟩)
                (fun k h1 h2 => hDisj oldIdx hOldNotUsed k h2 h1) hDoneC
                (fun r hr => by rcases List.mem_cons.1 hr with rfl | hs; exact (hsufB child hChildSuf).1; exact (hsufB r (List.mem_of_mem_erase hs)).1)
                hChildClean1 hclean.1 with ⟨newChild, haMidLe, haMidBound, hparMid, hndMid, hframeMid, hSdone', hDone'⟩
              have hLive' : ∀ (i : Nat) (hi : i < c₁.length), i ∉ oldIdx :: usedIdxs →
                  live.getD i 0 ∈ suf.erase child ∧ CleanDomSubtree f childNs c₁[i] aMid (Si i) (live.getD i 0) := fun i hi hnotUsed => by
                have hneIdx : i ≠ oldIdx := fun h => hnotUsed (h ▸ .head _)
                rcases hLive i hi (fun h => hnotUsed (.tail _ h)) with ⟨hInSuf, hCleanI⟩
                exact ⟨(List.mem_erase_of_ne (fun hEq => hneIdx (hliveInj i oldIdx hi hOldLt hEq))).2 hInSuf,
                  CleanDomSubtree_frame (fun m hm => let hSi := hSiB i m.toNat hm
                    hframeMid m (node_ne_of_toNat_ne hSi.1) (fun ho => hSiDisj i oldIdx hneIdx m.toNat hm ho) (Nat.lt_of_lt_of_le hSi.2 hbase)) hCleanI⟩
              have hMatchRest : KeyedCleanMatch c₁ (oldIdx :: usedIdxs) sRest tRest := by
                refine ⟨fun i hi => ⟨(hkm.1 (i + 1) (Nat.succ_lt_succ hi)).1, fun j' p' hs => ?_⟩, fun i₁ i₂ j₁ j₂ p₁ p₂ hi₁ hi₂ h1 h2 hj => ?_⟩
                · have hm := (hkm.1 (i + 1) (Nat.succ_lt_succ hi)).2 j' p' hs
                  have hne : j' ≠ oldIdx := fun hEq =>
                    Nat.zero_ne_add_one i (hkm.2 0 (i + 1) oldIdx j' (diff c₁[oldIdx] t) p'
                      (Nat.zero_lt_succ _) (Nat.succ_lt_succ (hlen' ▸ hi)) rfl hs hEq.symm)
                  exact ⟨fun hu => by rcases List.mem_cons.1 hu with h0 | ht; exact hne h0; exact hm.1 ht, hm.2⟩
                · exact Nat.succ.inj (hkm.2 (i₁ + 1) (i₂ + 1) j₁ j₂ p₁ p₂ (Nat.succ_lt_succ hi₁) (Nat.succ_lt_succ hi₂) h1 h2 hj)
              have hih := ih tRest (targetsDone ++ [t]) (oldIdx :: usedIdxs) (pre ++ [newChild]) (suf.erase child) _ aMid
                hlen' hMatchRest hclean.2 hrestDep (by simp only [List.length_append, List.length_singleton]; omega)
                (Nat.le_trans hbase haMidLe) (Nat.lt_of_le_of_lt (Nat.add_le_add_right haMidBound _) (Nat.add_assoc _ _ _ ▸ hbound))
                (Nat.lt_of_lt_of_le hparLt haMidLe) (Nat.lt_of_lt_of_le hposId haMidLe) hparMid hndMid hSdone' hDone' hLive'
                (fun i hi k hsi hk => not_Sdone_extend (hDisj i (fun h => hi (.tail _ h)) k hsi)
                  (hSiDisj i oldIdx (fun h => hi (h ▸ .head _)) k hsi) (Nat.lt_of_lt_of_le (hSiB i k hsi).2 hbase) hk)
                (fun r hr => have hr0 := hsufB r (List.mem_of_mem_erase hr); ⟨Nat.lt_of_lt_of_le hr0.1 haMidLe, hr0.2⟩)
              dsimp only [StateT.run] at hih ⊢
              rw [show applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat pre.length) (.reuse oldIdx (diff c₁[oldIdx] t) :: sRest) a =
                  applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat (pre ++ [newChild]).length) sRest aMid from by
                dsimp only [applyKeyedStepsM, bind]
                rw [stateM_bind_step hparIns, stateM_bind_step (show applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff c₁[oldIdx] t) a1 = ((), aMid) from rfl)]
                simp only [List.length_append, List.length_singleton, huJNext]]
              exact ⟨by have hfj := hih.1; simp only [List.length_append, List.length_cons, List.length_nil] at hfj ⊢; omega,
                clean_step_reconcile_combine hEraseLe haMidLe haMidBound (fun _ h => h)
                  (fun _ hk => hk.imp id (fun h => h.imp (fun hsi => ⟨oldIdx, hsi⟩) id))
                  (fun _ hD hR hLt => not_Sdone_extend hD (fun hsi => hR ⟨oldIdx, hsi⟩) hLt)
                  (fun m hmPar hmR hmLt => hframeMid m hmPar (fun hsi => hmR ⟨oldIdx, hsi⟩) hmLt) hih.2⟩
          | create newH =>
              have htEq : newH = t := hStep0.1 newH rfl
              rcases clean_create_step hchildNs hclean.1 htDep (by omega) htBound hparLt hposId hpar hnd hSdone hDoneC hsufB with
                ⟨cn, aIns, hrun, haInsGe, haInsLe, hparIns, hnd', hfrIns, hDone'⟩
              have hLiveIns : ∀ (i : Nat) (hi : i < c₁.length), i ∉ usedIdxs →
                  live.getD i 0 ∈ suf ∧ CleanDomSubtree f childNs c₁[i] aIns (Si i) (live.getD i 0) := fun i hi hnu =>
                let ⟨hs, hcl⟩ := hLive i hi hnu
                ⟨hs, CleanDomSubtree_frame (fun m hm => hfrIns m (node_ne_of_toNat_ne (hSiB i m.toNat hm).1) (Nat.lt_of_lt_of_le (hSiB i m.toNat hm).2 hbase)) hcl⟩
              have hMatchRest : KeyedCleanMatch c₁ usedIdxs sRest tRest :=
                ⟨fun i hi => hkm.1 (i + 1) (Nat.succ_lt_succ hi),
                  fun i₁ i₂ j₁ j₂ p₁ p₂ hi₁ hi₂ h1 h2 hj =>
                    Nat.succ.inj (hkm.2 (i₁ + 1) (i₂ + 1) j₁ j₂ p₁ p₂ (Nat.succ_lt_succ hi₁) (Nat.succ_lt_succ hi₂) h1 h2 hj)⟩
              have hih := ih tRest (targetsDone ++ [t]) usedIdxs (pre ++ [cn]) suf
                (fun k => Sdone k ∨ (a.nextId ≤ k ∧ k < aIns.nextId)) aIns
                hlen' hMatchRest hclean.2 hrestDep (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
                (Nat.le_trans hbase haInsGe) (Nat.lt_of_le_of_lt (Nat.add_le_add_right haInsLe _) (Nat.add_assoc _ _ _ ▸ hbound))
                (Nat.lt_of_lt_of_le hparLt haInsGe) (Nat.lt_of_lt_of_le hposId haInsGe) hparIns hnd'
                (clean_done_alloc_bounds haInsGe hparLt hSdone) hDone' hLiveIns
                (fun i hnu k hsi hk => hk.elim (fun h => hDisj i hnu k hsi h) (fun hhi => Nat.not_lt.2 hhi.1 (Nat.lt_of_lt_of_le (hSiB i k hsi).2 hbase)))
                (fun r hr => have hb := hsufB r hr; ⟨Nat.lt_of_lt_of_le hb.1 haInsGe, hb.2⟩)
              dsimp only [StateT.run] at hih ⊢
              rw [show applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat pre.length) (.create newH :: sRest) a =
                  applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat (pre ++ [cn]).length) sRest aIns from by
                rw [htEq]; dsimp only [applyKeyedStepsM]; rw [hrun]; simp only [List.length_append, List.length_singleton, huJNext]]
              exact ⟨by have hfj := hih.1; simp only [List.length_append, List.length_cons, List.length_nil] at hfj ⊢; omega,
                clean_step_reconcile_combine (Nat.le_refl _) haInsGe haInsLe (fun _ h => h)
                  (fun _ hk => hk.imp id .inr) (fun _ hD _ hLt h => h.elim hD (fun hlo => Nat.not_lt.2 hlo.1 hLt))
                  (fun m hmPar _ hmLt => hfrIns m hmPar hmLt) hih.2⟩

theorem applyKeyedStepsM_with_removeTail_spec {msg : Type} (f : Nat) (hPatch : @PatchSpecAt msg f)
    (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (childNs : String) (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (steps : List (KeyedStep msg)) (c₁ c₂ : List (Html msg)) (domCs : List Dom.Node) (Srem : Nat → Prop) (a : DomArena msg)
    (hvalid : DiffStepsValid c₁ c₂ steps) (hclean : Html.DomCleanList c₂ = true) (hdep : htmlListDepth c₂ ≤ f)
    (hbound : a.nextId + htmlListNodeCount c₂ < UInt32.size) (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg domCs) (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId)
    (hCleanCs : CleanDomChildren f childNs c₁ a Srem domCs) :
    ReconcileTailOut f parent pns ptag pst pmg childNs c₂ Srem a
      ((do let live ← snapshotChildrenM parent 0 #[] domCs.length; let finalJ ← applyKeyedStepsM parent live 0 steps; let count ← MonadDom.childCount parent; removeTailM (m := StateM (DomArena msg)) parent finalJ (count.toNat - finalJ.toNat)).run a).2 := by
  rcases cleanChildren_dom_bounds hvalid.1 hbound hSrem hCleanCs with ⟨hnd, hsufB, hdomLe, hsz⟩
  rcases CleanDomChildren_indexed hCleanCs with ⟨Si, hSiSub, hSiDisj, hSiGet⟩
  let live : Array Dom.Node := { toList := domCs }
  have hsnap : snapshotChildrenM (m := StateM (DomArena msg)) parent 0 #[] domCs.length a = (live, a) := by
    have hs := snapshotChildrenM_spec a parent pns ptag pst pmg domCs (by omega) 0 domCs.length #[] (by simp)
    rw [DomArena.set_get_self a hpar] at hs; simpa [live, StateT.run] using hs
  have hres := applyKeyedStepsM_reconcile_spec f hPatch parent pns ptag pst pmg childNs hchildNs
    c₁ live Si a.nextId (by simp [live, hnd.2])
    (fun i k hk => have hb := hSiSub i k hk; ⟨(hSrem k hb).1, (hSrem k hb).2⟩)
    hSiDisj (mem_of_diff_children_nodup c₁ domCs hnd.1 hnd.2)
    steps c₂ [] [] [] domCs (fun _ => False) a hvalid.1
    ⟨fun i hi => ⟨(hvalid.2.1 i hi).1, fun j p hs => ⟨(fun hm => nomatch hm), (hvalid.2.1 i hi).2 j p hs⟩⟩, hvalid.2.2⟩
    hclean hdep hsz (Nat.le_refl _) hbound hparLt hposId hpar (by simpa using hnd.1)
    (fun _ h => h.elim) trivial
    (fun i hi _ => ⟨by simp [live, Array.getD, hnd.2, hi], by
      have hget : live.getD i 0 = domCs[i]'(hnd.2 ▸ hi) := by simp [live, Array.getD, hnd.2, hi]
      rw [hget]; exact hSiGet i hi (hnd.2 ▸ hi)⟩)
    (fun _ _ _ _ h => h.elim) hsufB
  simp only [List.length_nil, show (UInt32.ofNat 0 : Dom.Node) = 0 from rfl, ReconcileStepOut, StateT.run, Nat.zero_add] at hres
  cases hK : applyKeyedStepsM (m := StateM (DomArena msg)) parent live 0 steps a with
  | mk finalJ aMid =>
      rw [hK] at hres
      rcases hres with ⟨hfjNat, targetsOut, sufRem, Snew, hlenT, htotLen, haMidLe, haMidBound, hnodeMid, hfrMid, hSnew, hCleanOut⟩
      simp only [List.nil_append] at hnodeMid hCleanOut
      have hfjEq : finalJ = UInt32.ofNat steps.length :=
        uint32_eq_of_toNat_eq (by rw [hfjNat, uint32_toNat_ofNat_lt _ (by simp at hsz; omega)])
      have hfin := finish_reconcile_removeTail (nSteps := steps.length) (domLen := domCs.length) (c₂ := c₂) (Srem := Srem) (a := a)
        (by simp at hsz; omega) ⟨targetsOut, sufRem, Snew, hlenT, htotLen, haMidLe, haMidBound, hnodeMid,
          fun m hmPar hmS hmLt => hfrMid m hmPar (fun h => h.elim) (fun ⟨i, hsi⟩ => hmS (hSiSub i m.toNat hsi)) hmLt,
          fun k hk => by rcases hSnew k hk with ⟨hF | ⟨i, hSi⟩ | hA, hnp⟩; exact hF.elim; exact ⟨.inl (hSiSub i k hSi), hnp⟩; exact ⟨.inr hA, hnp⟩,
          hCleanOut⟩
      dsimp only [StateT.run, bind, StateT.bind] at hfin ⊢
      rw [hsnap]; dsimp only; rw [hK, hfjEq]; dsimp only
      rwa [uint32_toNat_ofNat_lt steps.length (by simp at hsz; omega)]

theorem applyToDomM_spec {msg : Type} (fuel : Nat) : @PatchSpecAt msg fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      intro childNs parent pns ptag pst pmg oldH newH node pre suf Sold a
        hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hcleanOld hcleanNew
      cases fuel with
      | zero => cases newH <;> simp [htmlDepth] at hdep
      | succ f =>
          have hPatchF : @PatchSpecAt msg f := ih f (Nat.lt_succ_self f)
          have hReplace : diff oldH newH = .replace newH →
              PatchSpecOut (f + 1) childNs parent pns ptag pst pmg oldH newH node pre suf Sold a
                ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (diff oldH newH)).run a).2 := fun hd => by
            rcases replace_child_clean hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hSoldLt hparNodes hcleanNew with
              ⟨hle, hbd, hfr, n2, _, hpar', hnd', hnodes', hcl'⟩
            dsimp only [PatchSpecOut]; rw [hd]; exact ⟨hle, hbd, hfr, n2, .inl rfl, hpar', hnd', hnodes', hcl'⟩
          cases oldH with
          | text sOld =>
              cases newH with
              | text sNew =>
                  rcases hcleanOld with ⟨hnodeIn, hnodeGet⟩
                  have hne : node ≠ parent := fun h => hparOut (h ▸ hnodeIn)
                  dsimp only [PatchSpecOut, diff, applyToDomM, StateT.run, MonadDom.setText, DomArena.modify]
                  rw [hnodeGet]; dsimp only
                  exact ⟨Nat.le_refl _, by simp [htmlNodeCount],
                    fun m _ hmOut _ => DomArena.get_set_ne _ _ (fun heq => hmOut (congrArg UInt32.toNat heq ▸ hnodeIn)),
                    node, .inr rfl, by rw [DomArena.get_set_ne _ _ hne.symm, hpar], hnd, hparNodes, .inl hnodeIn, DomArena.get_set_self _ _ _⟩
              | element _ _ _ => exact hReplace rfl
          | element t₁ a₁ c₁ =>
              cases newH with
              | text _ => exact hReplace rfl
              | element t₂ a₂ c₂ =>
                  by_cases ht : t₁ = t₂
                  · subst ht
                    rcases hcleanOld with ⟨hnodeIn, _, _, st, mg, domCs, hnodeGet, hElClean, _, _, hCleanCs⟩
                    simp only [Html.DomClean, Bool.and_eq_true] at hcleanNew
                    rcases hcleanNew with ⟨⟨hownNewT, ha₂Clean⟩, hc₂Clean⟩
                    have hownNewF : ownsChildren a₂ = false := by simpa using hownNewT
                    simp only [htmlNodeCount] at hbound; simp only [htmlDepth] at hdep
                    have hc₂Dep : htmlListDepth c₂ ≤ f := by omega
                    have hne : node ≠ parent := fun h => hparOut (h ▸ hnodeIn)
                    have hnodeLt : node.toNat < a.nextId := hSoldLt _ hnodeIn
                    let realNs := if childNs == "" && t₁ == "svg" then Dom.svgNs else childNs
                    have hccNs := childNamespace_eq_childNsOf (ptag := t₁) (show childNs = "" ∨ childNs = Dom.svgNs by rw [hchildNs]; split <;> simp)
                    have hattrs := ElemClean_applyAttrsM a node realNs t₁ st mg domCs a₂ hElClean ha₂Clean
                    rw [DomArena.set_get_self a hnodeGet] at hattrs
                    rcases hattrs with ⟨st', ha1Get, ha1Equiv, hElClean'⟩
                    let mg' := (normalizeAttrs a₂).filterMap managedAttrName
                    let a1 := (applyAttrsM (m := StateM (DomArena msg)) node a₂ a).2
                    have ha1Next : a1.nextId = a.nextId := (applyAttrsM_preserves a node a₂).1
                    have ha1Ne : ∀ m, m ≠ node → a1.get m = a.get m := (applyAttrsM_preserves a node a₂).2
                    have hCleanCs1 := CleanDomChildren_frame (fun m hm => ha1Ne m (node_ne_of_toNat_ne hm.2)) hCleanCs
                    have hdomLe : domCs.length ≤ a1.nextId := nodup_nodes_lt_length_le a1.nextId domCs (CleanDomChildren_nodup hCleanCs).1 fun r hr => by
                      rw [ha1Next]; exact hSoldLt _ (CleanDomChildren_mem hCleanCs r hr).1
                    have ⟨steps, hdiffEq⟩ : ∃ steps, diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂) = .patchElement a₂ steps := by
                      cases h : diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂) with
                      | replace _ | setText _ => simp [diff] at h
                      | patchElement a₂' s => obtain ⟨rfl, _⟩ : a₂ = a₂' ∧ True := ⟨by simp [diff] at h; exact h.1, trivial⟩; exact ⟨s, rfl⟩
                    have hvalid := diff_steps_valid hdiffEq
                    have hSrem : ∀ k, (Sold k ∧ k ≠ node.toNat) → k ≠ node.toNat ∧ k < a1.nextId := fun k hk => ⟨hk.2, by rw [ha1Next]; exact hSoldLt k hk.1⟩
                    have hRec : ReconcileTailOut f node realNs t₁ st' mg' (Dom.childNsOf childNs t₁) c₂ (fun k => Sold k ∧ k ≠ node.toNat) a1
                        ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂))).run a).2 := by
                      dsimp only [StateT.run]; rw [hdiffEq]; dsimp only [applyToDomM, bind, StateT.bind, pure, StateT.pure]
                      rw [show applyAttrsM (m := StateM (DomArena msg)) node a₂ a = ((), a1) from rfl]; dsimp only
                      simp only [hownNewF, Bool.false_eq_true, ↓reduceIte, StateT.bind, bind]; rw [ha1Get]; dsimp only
                      by_cases hposSt : positional 0 steps = true
                      · simp only [hposSt, ↓reduceIte]
                        exact applyPositionalStepsM_with_removeTail hPatchF hccNs.symm steps c₁ c₂ domCs _ a1 hvalid.1 hposSt hvalid hc₂Clean hc₂Dep (by omega) (by omega) (by omega) ha1Get hSrem hCleanCs1
                      · simp only [Bool.eq_false_iff.2 hposSt, Bool.false_eq_true, ↓reduceIte]
                        rw [show (UInt32.ofNat domCs.length).toNat = domCs.length from uint32_toNat_ofNat_lt _ (by omega)]
                        exact applyKeyedStepsM_with_removeTail_spec f hPatchF node realNs t₁ st' mg' (Dom.childNsOf childNs t₁) hccNs.symm steps c₁ c₂ domCs _ a1 hvalid hc₂Clean hc₂Dep (by omega) (by omega) (by omega) ha1Get hSrem hCleanCs1
                    rcases hRec with ⟨targetsOut, Snew, haOutGe, haOutBound, hnodeOut, hfrOut, hSnew, hCleanOut⟩
                    refine ⟨by omega, by simp only [htmlNodeCount]; omega, fun m _ hmOut hmLt => ?_, node, .inr rfl, ?_, hnd,
                      fun r hr => Nat.lt_of_lt_of_le (hparNodes r hr) (by omega),
                      .inl hnodeIn, hownNewF, ha₂Clean, st', mg', targetsOut, hnodeOut, hElClean',
                      ha1Equiv, fun nm hnm => List.contains_iff_mem.2 hnm,
                      CleanDomChildren_mono (fun k hk => ⟨(hSnew k hk).1.elim (fun h => .inl h.1) (fun h => .inr ⟨by omega, h.2⟩), (hSnew k hk).2⟩) hCleanOut⟩
                    · have hmNeNode : m ≠ node := fun h => hmOut (h ▸ hnodeIn)
                      rw [hfrOut m hmNeNode (fun h => hmOut h.1) (by omega), ha1Ne m hmNeNode]
                    · rw [hfrOut parent hne.symm (fun h => hparOut h.1) (by omega), ha1Ne parent hne.symm, hpar]
                  · exact hReplace (by simp [diff, ht])

theorem applyPositionalStepsM_spec {msg : Type} (f : Nat)
    (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (childNs : String) (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (steps : List (KeyedStep msg)) (c₁ c₂ : List (Html msg)) (domCs : List Dom.Node) (Srem : Nat → Prop) (a : DomArena msg)
    (hsteps : steps.length = c₂.length) (hpos : positional 0 steps = true)
    (hvalid : DiffStepsValid c₁ c₂ steps) (hclean : Html.DomCleanList c₂ = true) (hdep : htmlListDepth c₂ ≤ f)
    (hbound : a.nextId + htmlListNodeCount c₂ < UInt32.size) (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg domCs) (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId)
    (hCleanCs : CleanDomChildren f childNs c₁ a Srem domCs) :
    ReconcileStepAt0Out f parent pns ptag pst pmg childNs steps.length domCs.length c₂ Srem a
      ((applyPositionalStepsM (m := StateM (DomArena msg)) parent 0 steps).run a).2 :=
  applyPositionalStepsM_clean_at0 (applyToDomM_spec f) hchildNs
    steps c₁ c₂ domCs Srem a hsteps hpos hvalid hclean hdep hbound hparLt hposId hpar hSrem hCleanCs

theorem patchHtmlSubtreeM_spec {msg : Type} (f : Nat)
    (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (oldH newH : Html msg) (node : Dom.Node) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg)
    (hchildNs : childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else ""))
    (hpreLen : pre.length + 1 + suf.length < UInt32.size) (hbound : a.nextId + htmlNodeCount newH < UInt32.size)
    (hdep : htmlDepth newH ≤ f) (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ node :: suf)) (hnd : (pre ++ node :: suf).Nodup)
    (hparOut : ¬Sold parent.toNat) (hSoldLt : ∀ k, Sold k → k < a.nextId) (hparNodes : ∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId)
    (hcleanOld : CleanDomSubtree f childNs oldH a Sold node) (hcleanNew : newH.DomClean = true) :
    let (newNode, a') := (patchHtmlSubtreeM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node oldH newH).run a
    a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount newH ∧
    (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
    a'.get parent = .element pns ptag pst pmg (pre ++ newNode :: suf) ∧ (pre ++ newNode :: suf).Nodup ∧
    (∀ r ∈ pre ++ newNode :: suf, r.toNat < a'.nextId) ∧ CleanDomSubtree f childNs newH a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) newNode ∧
    DomTreeAssocEquiv (readDomTree f a' newNode) (specDom childNs newH) := by
  have hSpec := applyToDomM_spec f childNs parent pns ptag pst pmg oldH newH node pre suf Sold a
    hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hcleanOld hcleanNew
  dsimp only [PatchSpecOut, StateT.run] at hSpec
  cases hd : diff oldH newH with
  | replace h2 =>
      have h2Eq : h2 = newH := by
        cases oldH <;> cases newH <;> simp [diff] at hd <;> try (subst hd; rfl)
        split at hd <;> simp at hd; subst hd; rfl
      subst h2Eq
      rcases replace_child_clean hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hSoldLt hparNodes hcleanNew with
        ⟨hle, hbd, hfr, n2, hEqRun, hpar', hnd', hnodes', hcl'⟩
      dsimp only [patchHtmlSubtreeM, StateT.run, bind, StateT.bind, pure, StateT.pure]; rw [hd]; dsimp only; rw [hEqRun]
      exact ⟨hle, hbd, hfr, hpar', hnd', hnodes', hcl', CleanDomSubtree_equiv hcl'⟩
  | setText _ | patchElement _ _ =>
      rw [hd] at hSpec; rcases hSpec with ⟨hle, hbd, hfr, newNode, hEq, hpar', hnd', hnodes', hcl'⟩
      rcases hEq with hc | rfl; cases hc
      dsimp only [patchHtmlSubtreeM, StateT.run, bind, StateT.bind, pure, StateT.pure]; rw [hd]; dsimp only
      exact ⟨hle, hbd, hfr, hpar', hnd', hnodes', hcl', CleanDomSubtree_equiv hcl'⟩

end Qed
