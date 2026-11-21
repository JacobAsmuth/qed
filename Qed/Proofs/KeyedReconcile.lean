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
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hget]
  · simp [hget, htmlNodeCount]
  · intro m hm _; simp only [hget]
    have hne : m ≠ child := by intro heq; subst heq; omega
    simp [DomArena.get_set_ne _ _ hne]
  · simp only [hget]; cases fuel with | zero => omega | succ _ => refine ⟨.inl ⟨Nat.le_refl _, by omega⟩, by simp [DomArena.get_set_self]⟩
  · simp only [hget]; cases fuel with | zero => omega | succ _ => simp [readDomTree, DomArena.get_set_self, specDom]

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
  have hc : (targets ++ rem).length < UInt32.size := by simp; omega
  have huCount : (UInt32.ofNat (targets ++ rem).length).toNat = targets.length + rem.length := by
    rw [uint32_toNat_ofNat_lt _ hc]; simp
  have huAt : (UInt32.ofNat targets.length).toNat = targets.length :=
    uint32_toNat_ofNat_lt targets.length (by omega)
  dsimp only [bind, StateT.bind, StateT.run, MonadDom.childCount]
  rw [DomArena.get_set_self]; dsimp only; rw [huCount, Nat.add_sub_cancel_left]
  have hr := removeTailM_spec a parent targets.length rem.length pns ptag pst pmg (targets ++ rem)
  dsimp only [StateT.run] at hr; rw [hr, huAt, removeTailSpec_append]

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

private theorem diff_steps_valid_pos {msg : Type} {t : String} {a₁ a₂ : List (Attr msg)}
    {c₁ c₂ : List (Html msg)} {steps : List (KeyedStep msg)}
    (hun : validatedKeyIndex c₁ = none ∨ validatedKeyIndex c₂ = none)
    (hdiff : diff (.element t a₁ c₁) (.element t a₂ c₂) = .patchElement a₂ steps) :
    DiffStepsValid c₁ c₂ steps := by
  rcases diff_positional_reuses (t := t) (a₁ := a₁) (a₂ := a₂) hun with ⟨s', hEq, hlen, hAt⟩
  rw [hEq] at hdiff; cases hdiff
  refine ⟨hlen, fun i hi => ⟨fun newH h => ?_, fun j p h => ?_⟩, fun i₁ i₂ j₁ j₂ p₁ p₂ hi₁ hi₂ h1 h2 hj => ?_⟩
  · rw [List.getElem?_eq_getElem (hlen ▸ hi)] at h
    by_cases hc : i < c₁.length
    · rw [(hAt i hi).1 hc] at h; cases h
    · rw [(hAt i hi).2 (Nat.le_of_not_lt hc)] at h; cases h; rfl
  · rw [List.getElem?_eq_getElem (hlen ▸ hi)] at h
    by_cases hc : i < c₁.length
    · rw [(hAt i hi).1 hc] at h; cases h; exact ⟨hc, rfl⟩
    · rw [(hAt i hi).2 (Nat.le_of_not_lt hc)] at h; cases h
  · rw [List.getElem?_eq_getElem hi₁] at h1; rw [List.getElem?_eq_getElem hi₂] at h2
    have hlt1 : i₁ < c₁.length := by by_cases hc : i₁ < c₁.length; exact hc; rw [(hAt i₁ (hlen ▸ hi₁)).2 (Nat.le_of_not_lt hc)] at h1; cases h1
    have hlt2 : i₂ < c₁.length := by by_cases hc : i₂ < c₁.length; exact hc; rw [(hAt i₂ (hlen ▸ hi₂)).2 (Nat.le_of_not_lt hc)] at h2; cases h2
    rw [(hAt i₁ (hlen ▸ hi₁)).1 hlt1] at h1; rw [(hAt i₂ (hlen ▸ hi₂)).1 hlt2] at h2; cases h1; cases h2; exact hj

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
          have hSpec2 := (validatedKeyIndex_spec h₂).2
          have hReuseKey : ∀ (i j : Nat) (p : Patch msg) (hi : i < c₂.length),
              steps[i]'(hlen ▸ hi) = .reuse j p → ∃ k, c₂[i].keyOf = some k ∧ ∃ _ : j < c₁.length, c₁[j].keyOf = some k := by
            intro i j p hi hs; rcases hSpec2 i hi with ⟨k, hkc₂, _⟩
            by_cases hex : ∃ j', ∃ hj' : j' < c₁.length, c₁[j'].keyOf = some k
            · rcases hex with ⟨j', hj', hkj'⟩; rw [(hAt i hi).1 j' hj' k hkc₂ hkj'] at hs; cases hs; exact ⟨k, hkc₂, hj', hkj'⟩
            · rw [(hAt i hi).2 k hkc₂ (fun j' hj' hk => hex ⟨j', hj', hk⟩)] at hs; cases hs
          refine ⟨hlen, fun i hi => ⟨fun newH h => ?_, fun j p h => ?_⟩, fun i₁ i₂ j₁ j₂ p₁ p₂ hi₁ hi₂ h1 h2 hj => ?_⟩
          · rcases hSpec2 i hi with ⟨k, hkc₂, _⟩; rw [List.getElem?_eq_getElem (hlen ▸ hi)] at h
            by_cases hex : ∃ j, ∃ hj : j < c₁.length, c₁[j].keyOf = some k
            · rcases hex with ⟨j, hj, hkj⟩; rw [(hAt i hi).1 j hj k hkc₂ hkj] at h; cases h
            · rw [(hAt i hi).2 k hkc₂ (fun j hj hk => hex ⟨j, hj, hk⟩)] at h; cases h; rfl
          · rw [List.getElem?_eq_getElem (hlen ▸ hi)] at h
            rcases hReuseKey i j p hi (Option.some.inj h) with ⟨k', hkc', hj, hko'⟩
            rw [(hAt i hi).1 j hj k' hkc' hko'] at h; cases h; exact ⟨hj, rfl⟩
          · rw [List.getElem?_eq_getElem hi₁] at h1; rw [List.getElem?_eq_getElem hi₂] at h2
            rcases hReuseKey i₁ j₁ p₁ (hlen ▸ hi₁) (Option.some.inj h1) with ⟨k₁, hkc₁, hj₁, hkc₁Old⟩
            rcases hReuseKey i₂ j₂ p₂ (hlen ▸ hi₂) (Option.some.inj h2) with ⟨k₂, hkc₂, hj₂, hkc₂Old⟩
            subst hj; rw [hkc₁Old] at hkc₂Old; cases hkc₂Old
            exact validatedKeyIndex_inj h₂ (hlen ▸ hi₁) (hlen ▸ hi₂) hkc₁ hkc₂


def PatchSpecAt {msg : Type} (f : Nat) : Prop :=
  ∀ (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (oldH newH : Html msg) (node : Dom.Node) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg),
    childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") →
    pre.length + 1 + suf.length < UInt32.size → a.nextId + htmlNodeCount newH < UInt32.size → htmlDepth newH ≤ f →
    parent.toNat < a.nextId → 0 < a.nextId → a.get parent = .element pns ptag pst pmg (pre ++ node :: suf) →
    (pre ++ node :: suf).Nodup → ¬Sold parent.toNat → (∀ k, Sold k → k < a.nextId) →
    (∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId) → CleanDomSubtree f childNs oldH a Sold node → newH.DomClean = true →
    let a' := ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (diff oldH newH)).run a).2
    a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount newH ∧
    (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
    ∃ newNode, (diff oldH newH = .replace newH ∨ newNode = node) ∧
      a'.get parent = .element pns ptag pst pmg (pre ++ newNode :: suf) ∧ (pre ++ newNode :: suf).Nodup ∧
      (∀ r ∈ pre ++ newNode :: suf, r.toNat < a'.nextId) ∧ CleanDomSubtree f childNs newH a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) newNode

private theorem clean_create_step {msg : Type} (f : Nat)
    (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (childNs : String) (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (newH : Html msg) (targetsDone : List (Html msg)) (pre suf : List Dom.Node) (Sdone : Nat → Prop) (a : DomArena msg)
    (hclean : newH.DomClean = true) (hdep : htmlDepth newH ≤ f)
    (hsz : pre.length + suf.length + 1 < UInt32.size) (hbound : a.nextId + htmlNodeCount newH < UInt32.size)
    (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId) (hpar : a.get parent = .element pns ptag pst pmg (pre ++ suf))
    (hnd : (pre ++ suf).Nodup) (hSdone : ∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId)
    (hDoneC : CleanDomChildren f childNs targetsDone a Sdone pre) (hsufB : ∀ r ∈ suf, r.toNat < a.nextId ∧ r ≠ parent) :
    ∃ cn aMid aIns,
      MonadDom.childNamespace (m := StateM (DomArena msg)) parent a = (childNs, a) ∧
      buildDomM (m := StateM (DomArena msg)) childNs newH a = (cn, aMid) ∧
      aMid.modifyChildren parent (fun cs => w3cInsertBefore cs (UInt32.ofNat pre.length).toNat cn) = aIns ∧
      a.nextId ≤ aIns.nextId ∧ aIns.nextId ≤ a.nextId + htmlNodeCount newH ∧ aIns.nextId = aMid.nextId ∧
      aIns.get parent = .element pns ptag pst pmg ((pre ++ [cn]) ++ suf) ∧ ((pre ++ [cn]) ++ suf).Nodup ∧
      (∀ m : Dom.Node, m ≠ parent → m.toNat < a.nextId → aIns.get m = a.get m) ∧
      CleanDomChildren f childNs (targetsDone ++ [newH]) aIns (fun k => Sdone k ∨ (a.nextId ≤ k ∧ k < aIns.nextId)) (pre ++ [cn]) := by
  have hchildNsRun : MonadDom.childNamespace (m := StateM (DomArena msg)) parent a = (childNs, a) := by
    simp [MonadDom.childNamespace, hpar, hchildNs]
  have hbuildMono := buildDomM_nextId_mono childNs newH a
  have hbuildSpec := buildDomM_spec childNs newH a f hposId hbound hdep
  have hbuildClean := CleanDomSubtree_of_buildDomM childNs newH a f hclean hposId hbound hdep
  dsimp only [StateT.run] at hbuildMono hbuildSpec hbuildClean
  cases hB : buildDomM (m := StateM (DomArena msg)) childNs newH a with
  | mk cn aMid =>
      rw [hB] at hbuildMono hbuildSpec hbuildClean; dsimp only at hbuildMono hbuildSpec hbuildClean
      rcases hbuildSpec with ⟨hcnGe, hcnLt, haMidBound, haMidFrame, _, _⟩
      have hparMid : aMid.get parent = .element pns ptag pst pmg (pre ++ suf) := by rw [haMidFrame parent hparLt, hpar]
      have hcnNotIn : cn ∉ pre ++ suf := fun hm => by
        rcases List.mem_append.1 hm with hp | hs
        · have := (hSdone _ (CleanDomChildren_mem hDoneC cn hp)).2; omega
        · have := (hsufB cn hs).1; omega
      have huJ : (UInt32.ofNat pre.length).toNat = pre.length := uint32_toNat_ofNat_lt pre.length (by omega)
      let aIns := aMid.set parent (.element pns ptag pst pmg ((pre ++ [cn]) ++ suf))
      have haInsNext : aIns.nextId = aMid.nextId := rfl
      have hinsRun : (aMid.modifyChildren parent fun cs => w3cInsertBefore cs (UInt32.ofNat pre.length).toNat cn) = aIns := by
        simp only [DomArena.modifyChildren, DomArena.modify, hparMid, huJ,
                   keyed_step_insertBefore_create pre suf cn hnd hcnNotIn, aIns, List.append_assoc, List.singleton_append]
      have hDoneIns : CleanDomChildren f childNs targetsDone aIns Sdone pre :=
        CleanDomChildren_frame (fun m hm => by
          rw [DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSdone _ hm).1)]; exact haMidFrame m (hSdone _ hm).2) hDoneC
      have hcnIns : CleanDomSubtree f childNs newH aIns (fun k => a.nextId ≤ k ∧ k < aIns.nextId) cn :=
        CleanDomSubtree_frame (fun m _ => DomArena.get_set_ne _ _ fun heq => by subst heq; omega) hbuildClean
      have hDone' := CleanDomChildren_append (fun k hk1 hk2 => by have := (hSdone k hk1).2; omega) hDoneIns
        (show CleanDomChildren f childNs [newH] aIns (fun k => a.nextId ≤ k ∧ k < aIns.nextId) [cn] from
          ⟨fun k => a.nextId ≤ k ∧ k < aIns.nextId, fun _ => False, fun _ h => h, fun _ h => h.elim, fun _ _ h => h.elim, hcnIns, trivial⟩)
      exact ⟨cn, aMid, aIns, hchildNsRun, rfl, hinsRun, hbuildMono, haMidBound, haInsNext,
        DomArena.get_set_self _ _ _, nodup_snoc_append hnd hcnNotIn,
        fun m hmPar hmLt => by rw [DomArena.get_set_ne _ _ hmPar, haMidFrame m hmLt], hDone'⟩

private theorem no_reuse_of_allCreates_top {msg : Type} :
    ∀ (xs : List (KeyedStep msg)) (k idx : Nat) (p : Patch msg), allCreates xs = true → xs[k]? = some (.reuse idx p) → False
  | [], _, _, _, _, h => by simp at h
  | .reuse _ _ :: _, _, _, _, hc, _ => by simp [allCreates] at hc
  | .create _ :: _, 0, _, _, _, h => by simp at h
  | .create _ :: sr, k + 1, idx, p, hc, h => no_reuse_of_allCreates_top sr k idx p hc (by simpa using h)

private def PosStepsMatch {msg : Type} (base : Nat) (steps : List (KeyedStep msg)) (targets oldRem : List (Html msg)) : Prop :=
  ∀ (k : Nat) (hk : k < targets.length),
    (∀ newH, steps[k]? = some (.create newH) → newH = targets[k]) ∧
    (∀ idx p, steps[k]? = some (.reuse idx p) → idx = base + k ∧ ∃ c, oldRem[k]? = some c ∧ p = diff c targets[k])

private def PosSufClean {msg : Type} (f : Nat) (ns : String) :
    List (KeyedStep msg) → List (Html msg) → DomArena msg → (Nat → Prop) → List Dom.Node → Prop
  | .reuse _ _ :: _, oldRem, a, Srem, suf => CleanDomChildren f ns oldRem a Srem suf
  | _, _, _, _, _ => True

private theorem applyPositionalStepsM_clean_step {msg : Type} (f : Nat) (hPatch : @PatchSpecAt msg f)
    (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (childNs : String) (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
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
    let aOut := ((applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) steps).run a).2
    ∃ targetsOut sufRem Snew, targetsOut.length = steps.length ∧ (targetsOut ++ sufRem).length ≤ suf.length + steps.length ∧
      a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount targets ∧
      aOut.get parent = .element pns ptag pst pmg ((pre ++ targetsOut) ++ sufRem) ∧
      (∀ m : Dom.Node, m ≠ parent → ¬Sdone m.toNat → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      (∀ k, Snew k → (Sdone k ∨ Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧
      CleanDomChildren f childNs (targetsDone ++ targets) aOut Snew (pre ++ targetsOut) := by
  induction steps generalizing targets targetsDone oldRem pre suf Sdone Srem a with
  | nil =>
      cases targets with
      | cons _ _ => cases hlen
      | nil =>
          dsimp only [applyPositionalStepsM, StateT.run, pure, StateT.pure, htmlListNodeCount]
          exact ⟨[], suf, Sdone, rfl, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
            by rw [List.append_nil]; exact hpar, fun _ _ _ _ _ => rfl, fun k hk => ⟨.inl hk, (hSdone k hk).1⟩,
            by rw [List.append_nil, List.append_nil]; exact hDoneC⟩
  | cons step sRest ih =>
      cases targets with
      | nil => cases hlen
      | cons t tRest =>
          simp only [List.length_cons] at hlen hsz
          have hlen' : sRest.length = tRest.length := Nat.succ.inj hlen
          simp only [Html.DomCleanList, Bool.and_eq_true] at hclean
          simp only [htmlListDepth] at hdep; simp only [htmlListNodeCount] at hbound ⊢
          have htDep : htmlDepth t ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
          have hrestDep : htmlListDepth tRest ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
          have hpreLtU : pre.length + 1 < UInt32.size := by omega
          have huJNext : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) := uint32_ofNat_succ pre.length hpreLtU
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
                      have htBound : a.nextId + htmlNodeCount t < UInt32.size :=
                        Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right _ _) _) hbound
                      have hPatchC := hPatch childNs parent pns ptag pst pmg cO t child pre sufRest Sc a
                        hchildNs (by omega) htBound htDep hparLt hposId hpar hnd
                        (fun h => (hSrem _ (hSc _ h)).1 rfl) (fun k hk => (hSrem k (hSc k hk)).2)
                        (fun r hr => by
                          rcases List.mem_append.1 hr with hp | hc
                          · exact (hSdone _ (CleanDomChildren_mem hDoneC r hp)).2
                          · rcases List.mem_cons.1 hc with rfl | hs
                            · exact (hSrem _ (hSc _ (CleanDomSubtree_root_mem hcClean))).2
                            · exact (hsufB r (.tail _ hs)).1)
                        hcClean hclean.1
                      dsimp only [StateT.run] at hPatchC hchildAt
                      rcases hPatchC with ⟨haMidLe, haMidBound, hframeMid, newChild, _, hparMid, hndMid, _, hcNew⟩
                      let aMid := (applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff cO t) a).2
                      have haMidLe' : a.nextId ≤ aMid.nextId := haMidLe
                      have haMidBound' : aMid.nextId ≤ a.nextId + htmlNodeCount t := haMidBound
                      have hApEq : (applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff cO t) a).2 = aMid := rfl
                      let Sdone' : Nat → Prop := fun k => Sdone k ∨ (Sc k ∨ (a.nextId ≤ k ∧ k < aMid.nextId))
                      have ⟨hSdone', hDone'⟩ := clean_done_extend haMidLe' hparLt hSdone (fun k h => hSrem k (hSc k h))
                        (fun k h1 h2 => hDisj k h1 (hSc k h2))
                        (fun m hm => hframeMid m (node_ne_of_toNat_ne (hSdone _ hm).1) (fun hsc => hDisj _ hm (hSc _ hsc)) (hSdone _ hm).2)
                        hDoneC hcNew
                      have hMatchRest : PosStepsMatch (pre ++ [newChild]).length sRest tRest oldRest := by
                        intro k hk; have hm' := hmatch (k + 1) (Nat.succ_lt_succ hk)
                        simp only [List.getElem?_cons_succ, List.getElem_cons_succ, List.length_append, List.length_singleton] at hm' ⊢
                        exact ⟨hm'.1, fun idx' p' hs => let hr := hm'.2 idx' p' hs; ⟨by omega, hr.2⟩⟩
                      have hSufCleanMid : PosSufClean f childNs sRest oldRest aMid Srest sufRest := by
                        cases sRest with
                        | nil => trivial
                        | cons stp _ => cases stp with
                          | create _ => trivial
                          | reuse _ _ => exact CleanDomChildren_frame (fun m hm =>
                              hframeMid m (node_ne_of_toNat_ne (hSrem _ (hSr _ hm)).1) (fun hsc => hDSr _ hsc hm) (hSrem _ (hSr _ hm)).2) hSufClean
                      have hposRest : positional (pre ++ [newChild]).length sRest = true := by
                        rw [List.length_append, List.length_singleton]; exact hpos.2
                      have hparMid' : aMid.get parent = .element pns ptag pst pmg ((pre ++ [newChild]) ++ sufRest) := by
                        rw [List.append_assoc, List.singleton_append]; exact hparMid
                      have hndMid' : ((pre ++ [newChild]) ++ sufRest).Nodup := by
                        rw [List.append_assoc, List.singleton_append]; exact hndMid
                      have hRestBound : aMid.nextId + htmlListNodeCount tRest < UInt32.size :=
                        Nat.lt_of_le_of_lt (Nat.add_le_add_right haMidBound' _) (Nat.add_assoc _ _ _ ▸ hbound)
                      have hih := ih tRest (targetsDone ++ [t]) oldRest (pre ++ [newChild]) sufRest Sdone' Srest aMid
                        hlen' hposRest hMatchRest hclean.2 hrestDep
                        (by simp only [List.length_append, List.length_singleton]; omega) hRestBound
                        (Nat.lt_of_lt_of_le hparLt haMidLe') (Nat.lt_of_lt_of_le hposId haMidLe')
                        hparMid' hndMid' hSdone' hDone' (fun k hk => have hb := hSrem k (hSr k hk); ⟨hb.1, Nat.lt_of_lt_of_le hb.2 haMidLe'⟩)
                        (fun k hk1 hk2 => not_Sdone_extend (fun h1 => hDisj k h1 (hSr k hk2)) (fun h => hDSr k h hk2) (hSrem k (hSr k hk2)).2 hk1)
                        (fun r hr => have hb := hsufB r (.tail _ hr); ⟨Nat.lt_of_lt_of_le hb.1 haMidLe', hb.2⟩) hSufCleanMid
                      rcases hih with ⟨targetsRest, sufRem, Snew, hlenR, htotLenR, hmonoR, hboundR, hparR, hfrR, hSnew, hDoneR⟩
                      have hstepRun : applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) (.reuse oldIdx (diff cO t) :: sRest) a =
                          applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (pre ++ [newChild]).length) sRest aMid := by
                        dsimp only [applyPositionalStepsM, bind, StateT.bind]
                        have haEq := DomArena.set_get_self a hpar; rw [haEq] at hchildAt
                        change (match MonadDom.childAt (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) a with
                                | (ch, a1) => match applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) ch (diff cO t) a1 with
                                  | (_, a2) => applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length + 1) sRest a2) = _
                        rw [hchildAt]; dsimp only
                        change (match applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff cO t) a with
                                | (_, a2) => applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length + 1) sRest a2) = _
                        cases hAp : applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff cO t) a with
                        | mk _ a2 => have hEq2 : a2 = aMid := by rw [← hApEq, hAp]
                                     subst hEq2; simp only [List.length_append, List.length_singleton, huJNext]
                      dsimp only [StateT.run] at hlenR htotLenR hmonoR hboundR hparR hfrR hSnew hDoneR ⊢
                      rw [hstepRun]
                      simp only [List.append_assoc, List.singleton_append] at hparR hDoneR
                      refine ⟨newChild :: targetsRest, sufRem, Snew, congrArg Nat.succ hlenR,
                        by simp only [List.cons_append, List.length_cons] at htotLenR ⊢; omega,
                        Nat.le_trans haMidLe' hmonoR,
                        Nat.le_trans hboundR (Nat.add_assoc _ _ _ ▸ Nat.add_le_add_right haMidBound' _),
                        by simp only [List.append_assoc]; exact hparR,
                        fun m hmPar hmD hmR hmLt =>
                          (hfrR m hmPar (not_Sdone_extend hmD (fun hsc => hmR (hSc _ hsc)) hmLt) (fun hr => hmR (hSr _ hr)) (Nat.lt_of_lt_of_le hmLt haMidLe')).trans
                            (hframeMid m hmPar (fun hsc => hmR (hSc _ hsc)) hmLt),
                        clean_step_Snew_compose haMidLe' hmonoR hSc hSr hSnew, hDoneR⟩
          | create newH =>
              simp only [positional] at hpos
              have htEq : newH = t := hStep0.1 newH rfl
              have htBound : a.nextId + htmlNodeCount t < UInt32.size :=
                Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right _ _) _) hbound
              rcases clean_create_step f parent pns ptag pst pmg childNs hchildNs t targetsDone pre suf Sdone a
                hclean.1 htDep (by omega) htBound hparLt hposId hpar hnd hSdone hDoneC hsufB with
                ⟨cn, aMid, aIns, hchildNsRun, hbuildEq, hinsRun, haInsGe, haInsLe, haInsMid, hparIns, hnd', hfrIns, hDone'⟩
              have hMatchRest : PosStepsMatch (pre ++ [cn]).length sRest tRest [] := by
                intro k hk; have hm := hmatch (k + 1) (Nat.succ_lt_succ hk)
                simp only [List.getElem?_cons_succ, List.getElem_cons_succ, List.length_append, List.length_singleton] at hm ⊢
                refine ⟨hm.1, fun idx' p' hs => False.elim (no_reuse_of_allCreates_top sRest k idx' p' hpos hs)⟩
              have hposRest : positional (pre ++ [cn]).length sRest = true := by
                cases sRest with | nil => rfl | cons s0 _ => cases s0 with | reuse _ _ => cases hpos | create _ => exact hpos
              have hsufCleanIns : PosSufClean f childNs sRest [] aIns Srem suf := by
                cases sRest with | nil => trivial | cons s0 _ => cases s0 with | create _ => trivial | reuse _ _ => cases hpos
              have hRestBound : aIns.nextId + htmlListNodeCount tRest < UInt32.size :=
                Nat.lt_of_le_of_lt (Nat.add_le_add_right haInsLe _) (Nat.add_assoc _ _ _ ▸ hbound)
              have hih := ih tRest (targetsDone ++ [t]) [] (pre ++ [cn]) suf (fun k => Sdone k ∨ (a.nextId ≤ k ∧ k < aIns.nextId)) Srem aIns
                hlen' hposRest hMatchRest hclean.2 hrestDep (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
                hRestBound (Nat.lt_of_lt_of_le hparLt haInsGe) (Nat.lt_of_lt_of_le hposId haInsGe) hparIns hnd'
                (clean_done_alloc_bounds haInsGe hparLt hSdone) hDone'
                (fun k hk => have hb := hSrem k hk; ⟨hb.1, Nat.lt_of_lt_of_le hb.2 haInsGe⟩)
                (fun k hk1 hk2 => hk1.elim (fun h => hDisj k h hk2) (fun hhi => Nat.not_lt.2 hhi.1 (hSrem k hk2).2))
                (fun r hr => have hb := hsufB r hr; ⟨Nat.lt_of_lt_of_le hb.1 haInsGe, hb.2⟩) hsufCleanIns
              have hstepRun : applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) (.create newH :: sRest) a =
                  applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (pre ++ [cn]).length) sRest aIns := by
                rw [htEq]; dsimp only [applyPositionalStepsM, bind, StateT.bind]
                change (match MonadDom.childNamespace (m := StateM (DomArena msg)) parent a with
                        | (ns', a1) => match buildDomM (m := StateM (DomArena msg)) ns' t a1 with
                          | (cn', a2) => match MonadDom.insertBeforeNode (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) cn' a2 with
                            | (_, a3) => applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length + 1) sRest a3) = _
                rw [hchildNsRun]; dsimp only; rw [hbuildEq]; dsimp only
                rw [hinsRun]; simp only [List.length_append, List.length_singleton, huJNext]
              dsimp only [StateT.run] at hih ⊢; rw [hstepRun]
              rcases hih with ⟨targetsRest, sufRem, Snew, hlenR, htotLenR, hmonoR, hboundR, hparR, hfrR, hSnew, hDoneR⟩
              simp only [List.append_assoc, List.singleton_append] at hparR hDoneR
              refine ⟨cn :: targetsRest, sufRem, Snew, congrArg Nat.succ hlenR,
                by simp only [List.cons_append, List.length_cons] at htotLenR ⊢; omega,
                Nat.le_trans haInsGe hmonoR,
                Nat.le_trans hboundR (Nat.add_assoc _ _ _ ▸ Nat.add_le_add_right haInsLe _),
                by simp only [List.append_assoc]; exact hparR,
                fun m hmPar hmD hmR hmLt =>
                  (hfrR m hmPar (fun h => h.elim hmD (fun hlo => Nat.not_lt.2 hlo.1 hmLt)) hmR (Nat.lt_of_lt_of_le hmLt haInsGe)).trans
                    (hfrIns m hmPar hmLt),
                clean_create_Snew_compose haInsGe hmonoR hSnew, hDoneR⟩


private theorem replace_child_clean {msg : Type} (f : Nat)
    (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (newH : Html msg) (node : Dom.Node) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg)
    (hchildNs : childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else ""))
    (hpreLen : pre.length + 1 + suf.length < UInt32.size) (hbound : a.nextId + htmlNodeCount newH < UInt32.size)
    (hdep : htmlDepth newH ≤ f) (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ node :: suf)) (hnd : (pre ++ node :: suf).Nodup)
    (_hSoldLt : ∀ k, Sold k → k < a.nextId) (hparNodesLt : ∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId) (hcleanNew : newH.DomClean = true) :
    let a' := ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (.replace newH)).run a).2
    a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount newH ∧
    (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
    ∃ newNode, (newNode = ((buildDomM (m := StateM (DomArena msg)) childNs newH).run a).1) ∧
      a'.get parent = .element pns ptag pst pmg (pre ++ newNode :: suf) ∧ (pre ++ newNode :: suf).Nodup ∧
      (∀ r ∈ pre ++ newNode :: suf, r.toNat < a'.nextId) ∧ CleanDomSubtree f childNs newH a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) newNode := by
  have hchildNsRun : MonadDom.childNamespace (m := StateM (DomArena msg)) parent a = (childNs, a) := by
    simp [MonadDom.childNamespace, hpar, hchildNs]
  have hbuildMono := buildDomM_nextId_mono childNs newH a
  have hbuildSpec := buildDomM_spec childNs newH a f hpos hbound hdep
  have hbuildClean := CleanDomSubtree_of_buildDomM childNs newH a f hcleanNew hpos hbound hdep
  dsimp only [StateT.run] at hbuildMono hbuildSpec hbuildClean ⊢
  cases hB : buildDomM (m := StateM (DomArena msg)) childNs newH a with
  | mk n2 aMid =>
      rw [hB] at hbuildMono hbuildSpec hbuildClean; dsimp only at hbuildMono hbuildSpec hbuildClean
      rcases hbuildSpec with ⟨hn2Ge, hn2Lt, haMidBound, haMidFrame, _, _⟩
      have hparMid : aMid.get parent = .element pns ptag pst pmg (pre ++ node :: suf) := by rw [haMidFrame parent hparLt, hpar]
      have huJ : (UInt32.ofNat pre.length).toNat = pre.length := uint32_toNat_ofNat_lt pre.length (by omega)
      let a' := aMid.set parent (.element pns ptag pst pmg (pre ++ n2 :: suf))
      have ha'Next : a'.nextId = aMid.nextId := rfl
      have hrun : applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (.replace newH) a = ((), a') := by
        dsimp only [applyToDomM, bind, StateT.bind]
        change (match MonadDom.childNamespace (m := StateM (DomArena msg)) parent a with
                | (ns', a1) => match buildDomM (m := StateM (DomArena msg)) ns' newH a1 with
                  | (n2', a2) => MonadDom.replaceChild (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) n2' a2) = _
        rw [hchildNsRun]; dsimp only; rw [hB]; dsimp only
        simp [MonadDom.replaceChild, DomArena.modifyChildren, DomArena.modify, hparMid, huJ, listReplaceAt_append_middle, a']
      rw [hrun, ha'Next]
      have hn2NotIn : n2 ∉ pre ++ node :: suf := fun hm => by have := hparNodesLt n2 hm; omega
      refine ⟨hbuildMono, haMidBound, fun m hmPar _ hmLt => by rw [DomArena.get_set_ne _ _ hmPar, haMidFrame m hmLt],
        n2, rfl, DomArena.get_set_self _ _ _, nodup_append_replace hnd (.inr hn2NotIn), fun r hr => ?_, ?_⟩
      · rcases List.mem_append.1 hr with hp | hc
        · have := hparNodesLt r (List.mem_append_left _ hp); omega
        · rcases List.mem_cons.1 hc with rfl | hs
          · exact hn2Lt
          · have := hparNodesLt r (List.mem_append_right _ (.tail _ hs)); omega
      · exact CleanDomSubtree_mono (fun _ hk => .inr hk)
          (CleanDomSubtree_frame (fun m _ => DomArena.get_set_ne _ _ fun heq => by subst heq; omega) hbuildClean)

private theorem positional_reuse_idx {msg : Type} :
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


private theorem mem_of_diff_children_nodup {msg : Type} (c₁ : List (Html msg)) (liveCs : List Dom.Node)
    (hnd : liveCs.Nodup) (hlen : liveCs.length = c₁.length) :
    ∀ i₁ i₂, i₁ < c₁.length → i₂ < c₁.length →
      ({ toList := liveCs } : Array Dom.Node).getD i₁ 0 = ({ toList := liveCs } : Array Dom.Node).getD i₂ 0 → i₁ = i₂ := by
  intro i₁ i₂ hi₁ hi₂ hEq
  have ha₁ : ({ toList := liveCs } : Array Dom.Node).getD i₁ 0 = liveCs[i₁]'(hlen ▸ hi₁) := by simp [Array.getD, hlen, hi₁]
  have ha₂ : ({ toList := liveCs } : Array Dom.Node).getD i₂ 0 = liveCs[i₂]'(hlen ▸ hi₂) := by simp [Array.getD, hlen, hi₂]
  rw [ha₁, ha₂] at hEq; exact nodup_getElem_inj (hlen ▸ hi₁) (hlen ▸ hi₂) hnd hEq

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
    ∃ targetsOut sufRem Snew, finalJ.toNat = pre.length + steps.length ∧ targetsOut.length = steps.length ∧
      (targetsOut ++ sufRem).length ≤ suf.length + steps.length ∧
      a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount targets ∧
      aOut.get parent = .element pns ptag pst pmg ((pre ++ targetsOut) ++ sufRem) ∧
      (∀ m : Dom.Node, m ≠ parent → ¬Sdone m.toNat → (∀ i, ¬Si i m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      (∀ k, Snew k → (Sdone k ∨ (∃ i, Si i k) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧
      CleanDomChildren f childNs (targetsDone ++ targets) aOut Snew (pre ++ targetsOut) := by
  induction steps generalizing targets targetsDone usedIdxs pre suf Sdone a with
  | nil =>
      cases targets with
      | cons _ _ => cases hlen
      | nil =>
          dsimp only [applyKeyedStepsM, StateT.run, pure, StateT.pure, htmlListNodeCount]
          exact ⟨[], suf, Sdone, uint32_toNat_ofNat_lt pre.length (by simp only [List.length_nil] at hsz; omega),
            rfl, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, by rw [List.append_nil]; exact hpar,
            fun _ _ _ _ _ => rfl, fun k hk => ⟨.inl hk, (hSdone k hk).1⟩,
            by rw [List.append_nil, List.append_nil]; exact hDoneC⟩
  | cons step sRest ih =>
      cases targets with
      | nil => cases hlen
      | cons t tRest =>
          simp only [List.length_cons] at hlen hsz
          have hlen' : sRest.length = tRest.length := Nat.succ.inj hlen
          simp only [Html.DomCleanList, Bool.and_eq_true] at hclean
          simp only [htmlListDepth] at hdep; simp only [htmlListNodeCount] at hbound ⊢
          have htDep : htmlDepth t ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
          have hrestDep : htmlListDepth tRest ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
          have hpreLtU : pre.length + 1 < UInt32.size := by omega
          have huJNext : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) := uint32_ofNat_succ pre.length hpreLtU
          have htBound : a.nextId + htmlNodeCount t < UInt32.size :=
            Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right _ _) _) hbound
          have hStep0 := hkm.1 0 (Nat.zero_lt_succ _)
          simp only [List.getElem_cons_zero] at hStep0
          cases step with
          | reuse oldIdx p =>
              rcases hStep0.2 oldIdx p rfl with ⟨hOldNotUsed, hOldLt, hpEq⟩; subst hpEq
              rcases hLive oldIdx hOldLt hOldNotUsed with ⟨hChildSuf, hChildClean⟩
              let child := live.getD oldIdx 0
              have hChildNotPre : child ∉ pre := fun hp => (List.nodup_append.1 hnd).2.2 child hp child hChildSuf rfl
              let a1 := a.set parent (.element pns ptag pst pmg (pre ++ child :: suf.erase child))
              have ha1Next : a1.nextId = a.nextId := rfl
              have hparIns : MonadDom.insertBeforeNode (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child a = ((), a1) := by
                simp only [MonadDom.insertBeforeNode, DomArena.modifyChildren, DomArena.modify, hpar,
                           uint32_toNat_ofNat_lt pre.length (Nat.lt_of_le_of_lt (Nat.le_succ _) hpreLtU),
                           w3cInsertBefore_step pre suf child hnd hChildNotPre, a1]
              have hnd1 : (pre ++ child :: suf.erase child).Nodup := by
                have h := nodup_move_to_pre hnd hChildSuf (.inl rfl)
                rw [List.append_assoc, List.singleton_append] at h; exact h
              have hChildClean1 : CleanDomSubtree f childNs c₁[oldIdx] a1 (Si oldIdx) child :=
                CleanDomSubtree_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSiB oldIdx m.toNat hm).1)) hChildClean
              have hParNodes1 : ∀ r ∈ pre ++ child :: suf.erase child, r.toNat < a1.nextId := fun r hr => by
                rw [ha1Next]; rcases List.mem_append.1 hr with hp | hc
                · exact (hSdone _ (CleanDomChildren_mem hDoneC r hp)).2
                · rcases List.mem_cons.1 hc with rfl | hs
                  · exact (hsufB child hChildSuf).1
                  · exact (hsufB r (List.mem_of_mem_erase hs)).1
              have hEraseLe : (suf.erase child).length ≤ suf.length := List.length_erase_le
              have hPatchC := hPatch childNs parent pns ptag pst pmg c₁[oldIdx] t child pre (suf.erase child) (Si oldIdx) a1
                hchildNs (by omega) htBound htDep hparLt hposId (DomArena.get_set_self _ _ _) hnd1 (fun h => (hSiB oldIdx parent.toNat h).1 rfl)
                (fun k hk => Nat.lt_of_lt_of_le (hSiB oldIdx k hk).2 hbase) hParNodes1 hChildClean1 hclean.1
              dsimp only [StateT.run] at hPatchC
              rcases hPatchC with ⟨haMidLe, haMidBound, hframeMid, newChild, _, hparMid, hndMid, _, hcNew⟩
              let aMid := (applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff c₁[oldIdx] t) a1).2
              have haMidLe' : a.nextId ≤ aMid.nextId := haMidLe
              have haMidBound' : aMid.nextId ≤ a.nextId + htmlNodeCount t := haMidBound
              have hApEq : (applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff c₁[oldIdx] t) a1).2 = aMid := rfl
              let Sdone' : Nat → Prop := fun k => Sdone k ∨ (Si oldIdx k ∨ (a1.nextId ≤ k ∧ k < aMid.nextId))
              have ⟨hSdone', hDone'⟩ := clean_done_extend haMidLe' hparLt hSdone
                (fun k h => let hb := hSiB _ k h; ⟨hb.1, Nat.lt_of_lt_of_le hb.2 hbase⟩)
                (fun k h1 h2 => hDisj oldIdx hOldNotUsed k h2 h1)
                (fun m hm =>
                  (hframeMid m (node_ne_of_toNat_ne (hSdone _ hm).1) (fun h => hDisj _ hOldNotUsed _ h hm) (hSdone _ hm).2).trans
                    (DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSdone _ hm).1)))
                hDoneC hcNew
              have hLive' : ∀ (i : Nat) (hi : i < c₁.length), i ∉ oldIdx :: usedIdxs →
                  live.getD i 0 ∈ suf.erase child ∧ CleanDomSubtree f childNs c₁[i] aMid (Si i) (live.getD i 0) := by
                intro i hi hnotUsed
                have hneIdx : i ≠ oldIdx := fun h => hnotUsed (h ▸ .head _)
                rcases hLive i hi (fun h => hnotUsed (.tail _ h)) with ⟨hInSuf, hCleanI⟩
                refine ⟨(List.mem_erase_of_ne (fun hEq => hneIdx (hliveInj i oldIdx hi hOldLt hEq))).2 hInSuf,
                  CleanDomSubtree_frame (fun m hm => ?_) hCleanI⟩
                have hSi := hSiB i m.toNat hm
                exact (hframeMid m (node_ne_of_toNat_ne hSi.1) (fun ho => hSiDisj i oldIdx hneIdx m.toNat hm ho)
                  (Nat.lt_of_lt_of_le hSi.2 hbase)).trans (DomArena.get_set_ne _ _ (node_ne_of_toNat_ne hSi.1))
              have hMatchRest : KeyedCleanMatch c₁ (oldIdx :: usedIdxs) sRest tRest := by
                refine ⟨fun i hi => ⟨(hkm.1 (i + 1) (Nat.succ_lt_succ hi)).1, fun j' p' hs => ?_⟩, fun i₁ i₂ j₁ j₂ p₁ p₂ hi₁ hi₂ h1 h2 hj => ?_⟩
                · have hm := (hkm.1 (i + 1) (Nat.succ_lt_succ hi)).2 j' p' hs
                  have hne : j' ≠ oldIdx := fun hEq =>
                    Nat.zero_ne_add_one i (hkm.2 0 (i + 1) oldIdx j' (diff c₁[oldIdx] t) p'
                      (Nat.zero_lt_succ _) (Nat.succ_lt_succ (hlen' ▸ hi)) rfl hs hEq.symm)
                  exact ⟨fun hu => by rcases List.mem_cons.1 hu with h0 | ht; exact hne h0; exact hm.1 ht, hm.2⟩
                · exact Nat.succ.inj (hkm.2 (i₁ + 1) (i₂ + 1) j₁ j₂ p₁ p₂ (Nat.succ_lt_succ hi₁) (Nat.succ_lt_succ hi₂) h1 h2 hj)
              have hSufCleanLen : (pre ++ [newChild]).length + (suf.erase child).length + sRest.length < UInt32.size := by
                simp only [List.length_append, List.length_singleton]; omega
              have hparMid' : aMid.get parent = .element pns ptag pst pmg ((pre ++ [newChild]) ++ suf.erase child) := by
                rw [List.append_assoc, List.singleton_append]; exact hparMid
              have hndMid' : ((pre ++ [newChild]) ++ suf.erase child).Nodup := by
                rw [List.append_assoc, List.singleton_append]; exact hndMid
              have hRestBound : aMid.nextId + htmlListNodeCount tRest < UInt32.size :=
                Nat.lt_of_le_of_lt (Nat.add_le_add_right haMidBound' _) (Nat.add_assoc _ _ _ ▸ hbound)
              have hih := ih tRest (targetsDone ++ [t]) (oldIdx :: usedIdxs) (pre ++ [newChild]) (suf.erase child) Sdone' aMid
                hlen' hMatchRest hclean.2 hrestDep hSufCleanLen (Nat.le_trans hbase haMidLe') hRestBound
                (Nat.lt_of_lt_of_le hparLt haMidLe') (Nat.lt_of_lt_of_le hposId haMidLe') hparMid' hndMid'
                hSdone' hDone' hLive'
                (fun i hi k hsi hk => not_Sdone_extend (hDisj i (fun h => hi (.tail _ h)) k hsi)
                  (hSiDisj i oldIdx (fun h => hi (h ▸ .head _)) k hsi) (Nat.lt_of_lt_of_le (hSiB i k hsi).2 hbase) hk)
                (fun r hr => have hr0 := hsufB r (List.mem_of_mem_erase hr); ⟨Nat.lt_of_lt_of_le hr0.1 haMidLe', hr0.2⟩)
              have hstepRun : applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat pre.length) (.reuse oldIdx (diff c₁[oldIdx] t) :: sRest) a =
                  applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat (pre ++ [newChild]).length) sRest aMid := by
                dsimp only [applyKeyedStepsM, bind, StateT.bind]
                change (match MonadDom.insertBeforeNode (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child a with
                        | (_, a1') => match applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff c₁[oldIdx] t) a1' with
                          | (_, a2) => applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat pre.length + 1) sRest a2) = _
                rw [hparIns]; dsimp only
                change (match applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff c₁[oldIdx] t) a1 with
                        | (_, a2) => applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat pre.length + 1) sRest a2) = _
                cases hAp : applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff c₁[oldIdx] t) a1 with
                | mk _ a2 => have hEq2 : a2 = aMid := by rw [← hApEq, hAp]
                             subst hEq2; simp only [List.length_append, List.length_singleton, huJNext]
              dsimp only [StateT.run] at hih ⊢; rw [hstepRun]
              rcases hih with ⟨targetsRest, sufRem, Snew, hfj, hlenR, htotLenR, hmonoR, hboundR, hparR, hfrR, hSnew, hDoneR⟩
              simp only [List.append_assoc, List.singleton_append] at hparR hDoneR
              refine ⟨newChild :: targetsRest, sufRem, Snew, by simp only [List.length_append, List.length_cons, List.length_nil] at hfj ⊢; omega,
                congrArg Nat.succ hlenR,
                by simp only [List.cons_append, List.length_cons] at htotLenR ⊢; omega,
                Nat.le_trans haMidLe' hmonoR,
                Nat.le_trans hboundR (Nat.add_assoc _ _ _ ▸ Nat.add_le_add_right haMidBound' _),
                by simp only [List.append_assoc]; exact hparR,
                fun m hmPar hmD hmAll hmLt =>
                  ((hfrR m hmPar (not_Sdone_extend hmD (hmAll oldIdx) hmLt) hmAll (Nat.lt_of_lt_of_le hmLt haMidLe')).trans
                    (hframeMid m hmPar (hmAll oldIdx) hmLt)).trans (DomArena.get_set_ne _ _ hmPar),
                clean_step_Snew_compose haMidLe' hmonoR (fun _ hsi => ⟨oldIdx, hsi⟩) (fun _ h => h) hSnew, hDoneR⟩
          | create newH =>
              have htEq : newH = t := hStep0.1 newH rfl
              rcases clean_create_step f parent pns ptag pst pmg childNs hchildNs t targetsDone pre suf Sdone a
                hclean.1 htDep (by omega) htBound hparLt hposId hpar hnd hSdone hDoneC hsufB with
                ⟨cn, aMid, aIns, hchildNsRun, hbuildEq, hinsRun, haInsGe, haInsLe, haInsMid, hparIns, hnd', hfrIns, hDone'⟩
              have hLiveIns : ∀ (i : Nat) (hi : i < c₁.length), i ∉ usedIdxs →
                  live.getD i 0 ∈ suf ∧ CleanDomSubtree f childNs c₁[i] aIns (Si i) (live.getD i 0) := by
                intro i hi hnu; rcases hLive i hi hnu with ⟨hs, hcl⟩
                refine ⟨hs, CleanDomSubtree_frame (fun m hm => hfrIns m (node_ne_of_toNat_ne (hSiB i m.toNat hm).1) (Nat.lt_of_lt_of_le (hSiB i m.toNat hm).2 hbase)) hcl⟩
              have hMatchRest : KeyedCleanMatch c₁ usedIdxs sRest tRest := by
                refine ⟨fun i hi => hkm.1 (i + 1) (Nat.succ_lt_succ hi),
                  fun i₁ i₂ j₁ j₂ p₁ p₂ hi₁ hi₂ h1 h2 hj =>
                    Nat.succ.inj (hkm.2 (i₁ + 1) (i₂ + 1) j₁ j₂ p₁ p₂ (Nat.succ_lt_succ hi₁) (Nat.succ_lt_succ hi₂) h1 h2 hj)⟩
              have hRestBound : aIns.nextId + htmlListNodeCount tRest < UInt32.size :=
                Nat.lt_of_le_of_lt (Nat.add_le_add_right haInsLe _) (Nat.add_assoc _ _ _ ▸ hbound)
              have hih := ih tRest (targetsDone ++ [t]) usedIdxs (pre ++ [cn]) suf
                (fun k => Sdone k ∨ (a.nextId ≤ k ∧ k < aIns.nextId)) aIns
                hlen' hMatchRest hclean.2 hrestDep (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
                (Nat.le_trans hbase haInsGe) hRestBound (Nat.lt_of_lt_of_le hparLt haInsGe) (Nat.lt_of_lt_of_le hposId haInsGe) hparIns hnd'
                (clean_done_alloc_bounds haInsGe hparLt hSdone) hDone' hLiveIns
                (fun i hnu k hsi hk => hk.elim (fun h => hDisj i hnu k hsi h) (fun hhi => Nat.not_lt.2 hhi.1 (Nat.lt_of_lt_of_le (hSiB i k hsi).2 hbase)))
                (fun r hr => have hb := hsufB r hr; ⟨Nat.lt_of_lt_of_le hb.1 haInsGe, hb.2⟩)
              have hstepRun : applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat pre.length) (.create newH :: sRest) a =
                  applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat (pre ++ [cn]).length) sRest aIns := by
                rw [htEq]; dsimp only [applyKeyedStepsM, bind, StateT.bind]
                change (match MonadDom.childNamespace (m := StateM (DomArena msg)) parent a with
                        | (ns', a1) => match buildDomM (m := StateM (DomArena msg)) ns' t a1 with
                          | (cn', a2) => match MonadDom.insertBeforeNode (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) cn' a2 with
                            | (_, a3) => applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat pre.length + 1) sRest a3) = _
                rw [hchildNsRun]; dsimp only; rw [hbuildEq]; dsimp only
                rw [hinsRun]; simp only [List.length_append, List.length_singleton, huJNext]
              dsimp only [StateT.run] at hih ⊢; rw [hstepRun]
              rcases hih with ⟨targetsRest, sufRem, Snew, hfj, hlenR, htotLenR, hmonoR, hboundR, hparR, hfrR, hSnew, hDoneR⟩
              simp only [List.append_assoc, List.singleton_append] at hparR hDoneR
              refine ⟨cn :: targetsRest, sufRem, Snew, by simp only [List.length_append, List.length_cons, List.length_nil] at hfj ⊢; omega,
                congrArg Nat.succ hlenR,
                by simp only [List.cons_append, List.length_cons] at htotLenR ⊢; omega,
                Nat.le_trans haInsGe hmonoR,
                Nat.le_trans hboundR (Nat.add_assoc _ _ _ ▸ Nat.add_le_add_right haInsLe _),
                by simp only [List.append_assoc]; exact hparR,
                fun m hmPar hmD hmAll hmLt =>
                  (hfrR m hmPar (fun h => h.elim hmD (fun hlo => Nat.not_lt.2 hlo.1 hmLt)) hmAll (Nat.lt_of_lt_of_le hmLt haInsGe)).trans
                    (hfrIns m hmPar hmLt),
                clean_create_Snew_compose haInsGe hmonoR hSnew, hDoneR⟩

private theorem applyPositionalStepsM_clean_at0 {msg : Type} (f : Nat) (hPatch : @PatchSpecAt msg f)
    (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (childNs : String) (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (steps : List (KeyedStep msg)) (c₁ c₂ : List (Html msg)) (domCs : List Dom.Node) (Srem : Nat → Prop) (a : DomArena msg)
    (hsteps : steps.length = c₂.length) (hpos : positional 0 steps = true) (hvalid : DiffStepsValid c₁ c₂ steps)
    (hclean : Html.DomCleanList c₂ = true) (hdep : htmlListDepth c₂ ≤ f) (hbound : a.nextId + htmlListNodeCount c₂ < UInt32.size)
    (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId) (hpar : a.get parent = .element pns ptag pst pmg domCs)
    (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) (hCleanCs : CleanDomChildren f childNs c₁ a Srem domCs) :
    let aOut := ((applyPositionalStepsM (m := StateM (DomArena msg)) parent 0 steps).run a).2
    ∃ targetsOut sufRem Snew, targetsOut.length = steps.length ∧ (targetsOut ++ sufRem).length ≤ domCs.length + steps.length ∧
      a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount c₂ ∧ aOut.get parent = .element pns ptag pst pmg (targetsOut ++ sufRem) ∧
      (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      (∀ k, Snew k → (Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧ CleanDomChildren f childNs c₂ aOut Snew targetsOut := by
  have hnd := CleanDomChildren_nodup hCleanCs
  have hsufB : ∀ r ∈ domCs, r.toNat < a.nextId ∧ r ≠ parent := fun r hr =>
    have hb := hSrem r.toNat (CleanDomChildren_mem hCleanCs r hr); ⟨hb.2, node_ne_of_toNat_ne hb.1⟩
  have hdomLe : domCs.length ≤ a.nextId := nodup_nodes_lt_length_le a.nextId domCs hnd.1 fun r hr => (hsufB r hr).1
  have hsz : ([] : List Dom.Node).length + domCs.length + steps.length < UInt32.size := by
    have := list_length_le_htmlListNodeCount c₂; simp; omega
  have hMatch : PosStepsMatch 0 steps c₂ c₁ := fun k hk =>
    ⟨(hvalid.2.1 k hk).1, fun j p hsk => by
      have hjEq := positional_reuse_idx 0 steps k j p hpos hsk
      rcases (hvalid.2.1 k hk).2 j p hsk with ⟨hj, hp⟩; simp only [Nat.zero_add] at hjEq; subst hjEq
      exact ⟨(Nat.zero_add j).symm, c₁[j], List.getElem?_eq_getElem hj, hp⟩⟩
  have hSufC : PosSufClean f childNs steps c₁ a Srem domCs := by
    cases steps with | nil => trivial | cons stp _ => cases stp with | create _ => trivial | reuse _ _ => exact hCleanCs
  simpa using applyPositionalStepsM_clean_step f hPatch parent pns ptag pst pmg childNs hchildNs
    steps c₂ [] c₁ [] domCs (fun _ => False) Srem a hsteps hpos hMatch hclean hdep hsz hbound hparLt hposId
    hpar (by simpa using hnd.1) (fun _ h => h.elim) trivial hSrem (fun _ h => h.elim) hsufB hSufC

private theorem finish_reconcile_removeTail {msg : Type} (f : Nat)
    (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (childNs : String) (c₂ : List (Html msg)) (Srem Snew : Nat → Prop)
    (a aMid : DomArena msg) (targetsOut sufRem : List Dom.Node)
    (hsize : targetsOut.length + sufRem.length < UInt32.size)
    (haMidLe : a.nextId ≤ aMid.nextId) (haMidBound : aMid.nextId ≤ a.nextId + htmlListNodeCount c₂)
    (hnodeMid : aMid.get parent = .element pns ptag pst pmg (targetsOut ++ sufRem))
    (hfrMid : ∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aMid.get m = a.get m)
    (hSnew : ∀ k, Snew k → (Srem k ∨ (a.nextId ≤ k ∧ k < aMid.nextId)) ∧ k ≠ parent.toNat)
    (hCleanOut : CleanDomChildren f childNs c₂ aMid Snew targetsOut) :
    let aOut := ((do let count ← MonadDom.childCount parent; removeTailM (m := StateM (DomArena msg)) parent (UInt32.ofNat targetsOut.length) (count.toNat - targetsOut.length)).run aMid).2
    ∃ targetsOut' Snew', a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount c₂ ∧
      aOut.get parent = .element pns ptag pst pmg targetsOut' ∧
      (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      (∀ k, Snew' k → (Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧
      CleanDomChildren f childNs c₂ aOut Snew' targetsOut' := by
  have hremTail := positional_removeTail_spec aMid parent pns ptag pst pmg targetsOut sufRem hsize
  rw [DomArena.set_get_self aMid hnodeMid] at hremTail
  dsimp only [StateT.run] at hremTail ⊢; rw [hremTail]
  exact ⟨targetsOut, Snew, haMidLe, haMidBound, DomArena.get_set_self _ _ _,
    fun m hmPar hmS hmLt => by rw [DomArena.get_set_ne _ _ hmPar]; exact hfrMid m hmPar hmS hmLt,
    hSnew, CleanDomChildren_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSnew m.toNat hm).2)) hCleanOut⟩

private theorem applyPositionalStepsM_with_removeTail {msg : Type} (f : Nat) (hPatch : @PatchSpecAt msg f)
    (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (childNs : String) (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (steps : List (KeyedStep msg)) (c₁ c₂ : List (Html msg)) (domCs : List Dom.Node) (Srem : Nat → Prop) (a : DomArena msg)
    (hsteps : steps.length = c₂.length) (hpos : positional 0 steps = true) (hvalid : DiffStepsValid c₁ c₂ steps)
    (hclean : Html.DomCleanList c₂ = true) (hdep : htmlListDepth c₂ ≤ f) (hbound : a.nextId + htmlListNodeCount c₂ < UInt32.size)
    (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId) (hpar : a.get parent = .element pns ptag pst pmg domCs)
    (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) (hCleanCs : CleanDomChildren f childNs c₁ a Srem domCs) :
    let aOut := ((do applyPositionalStepsM (m := StateM (DomArena msg)) parent 0 steps; let count ← MonadDom.childCount parent; removeTailM parent (UInt32.ofNat steps.length) (count.toNat - steps.length)).run a).2
    ∃ targetsOut Snew, a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount c₂ ∧
      aOut.get parent = .element pns ptag pst pmg targetsOut ∧
      (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      (∀ k, Snew k → (Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧ CleanDomChildren f childNs c₂ aOut Snew targetsOut := by
  have hnd := CleanDomChildren_nodup hCleanCs
  have hdomLe : domCs.length ≤ a.nextId := nodup_nodes_lt_length_le a.nextId domCs hnd.1
    fun r hr => (hSrem r.toNat (CleanDomChildren_mem hCleanCs r hr)).2
  have hres := applyPositionalStepsM_clean_at0 f hPatch parent pns ptag pst pmg childNs hchildNs
    steps c₁ c₂ domCs Srem a hsteps hpos hvalid hclean hdep hbound hparLt hposId hpar hSrem hCleanCs
  dsimp only [StateT.run] at hres ⊢
  rcases hres with ⟨targetsOut, sufRem, Snew, hlenT, htotLen, haMidLe, haMidBound, hnodeMid, hfrMid, hSnew, hCleanOut⟩
  simp only [List.length_append] at htotLen
  cases hP : applyPositionalStepsM (m := StateM (DomArena msg)) parent 0 steps a with
  | mk _ aMid =>
      rw [hP] at haMidLe haMidBound hnodeMid hfrMid hSnew hCleanOut
      have hsize : targetsOut.length + sufRem.length < UInt32.size := by
        have := list_length_le_htmlListNodeCount c₂; omega
      have hfin := finish_reconcile_removeTail f parent pns ptag pst pmg childNs c₂ Srem Snew a aMid targetsOut sufRem
        hsize haMidLe haMidBound hnodeMid hfrMid hSnew hCleanOut
      dsimp only [StateT.run, bind, StateT.bind] at hfin ⊢
      rw [hP]; dsimp only; rwa [← hlenT]

theorem applyKeyedStepsM_with_removeTail_spec {msg : Type} (f : Nat) (hPatch : @PatchSpecAt msg f)
    (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (childNs : String) (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (steps : List (KeyedStep msg)) (c₁ c₂ : List (Html msg)) (domCs : List Dom.Node) (Srem : Nat → Prop) (a : DomArena msg)
    (hvalid : DiffStepsValid c₁ c₂ steps) (hclean : Html.DomCleanList c₂ = true) (hdep : htmlListDepth c₂ ≤ f)
    (hbound : a.nextId + htmlListNodeCount c₂ < UInt32.size) (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg domCs) (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId)
    (hCleanCs : CleanDomChildren f childNs c₁ a Srem domCs) :
    let aOut := ((do let live ← snapshotChildrenM parent 0 #[] domCs.length; let finalJ ← applyKeyedStepsM parent live 0 steps; let count ← MonadDom.childCount parent; removeTailM (m := StateM (DomArena msg)) parent finalJ (count.toNat - finalJ.toNat)).run a).2
    ∃ targetsOut Snew, a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount c₂ ∧
      aOut.get parent = .element pns ptag pst pmg targetsOut ∧
      (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      (∀ k, Snew k → (Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧ CleanDomChildren f childNs c₂ aOut Snew targetsOut := by
  have hnd := CleanDomChildren_nodup hCleanCs
  have hsufB : ∀ r ∈ domCs, r.toNat < a.nextId ∧ r ≠ parent := fun r hr =>
    have hb := hSrem r.toNat (CleanDomChildren_mem hCleanCs r hr); ⟨hb.2, node_ne_of_toNat_ne hb.1⟩
  have hdomLe : domCs.length ≤ a.nextId := nodup_nodes_lt_length_le a.nextId domCs hnd.1 fun r hr => (hsufB r hr).1
  have hsz : ([] : List Dom.Node).length + domCs.length + steps.length < UInt32.size := by
    have := list_length_le_htmlListNodeCount c₂; simp [hvalid.1]; omega
  rcases CleanDomChildren_indexed hCleanCs with ⟨Si, hSiSub, hSiDisj, hSiGet⟩
  let live : Array Dom.Node := { toList := domCs }
  have hsnap : snapshotChildrenM (m := StateM (DomArena msg)) parent 0 #[] domCs.length a = (live, a) := by
    have hs := snapshotChildrenM_spec a parent pns ptag pst pmg domCs (by omega) 0 domCs.length #[] (by simp)
    rw [DomArena.set_get_self a hpar] at hs; simpa [live, StateT.run] using hs
  have hKm : KeyedCleanMatch c₁ [] steps c₂ := by
    refine ⟨fun i hi => ⟨(hvalid.2.1 i hi).1, fun j p hs => ?_⟩, hvalid.2.2⟩
    exact ⟨(fun hm => nomatch hm), (hvalid.2.1 i hi).2 j p hs⟩
  have hres := applyKeyedStepsM_reconcile_spec f hPatch parent pns ptag pst pmg childNs hchildNs
    c₁ live Si a.nextId (by simp [live, hnd.2])
    (fun i k hk => have hb := hSiSub i k hk; ⟨(hSrem k hb).1, (hSrem k hb).2⟩)
    hSiDisj (mem_of_diff_children_nodup c₁ domCs hnd.1 hnd.2)
    steps c₂ [] [] [] domCs (fun _ => False) a
    hvalid.1 hKm hclean hdep hsz (Nat.le_refl _) hbound hparLt hposId hpar (by simpa using hnd.1)
    (fun _ h => h.elim) trivial
    (fun i hi _ => ⟨by simp [live, Array.getD, hnd.2, hi], by
      have hget : live.getD i 0 = domCs[i]'(hnd.2 ▸ hi) := by simp [live, Array.getD, hnd.2, hi]
      rw [hget]; exact hSiGet i hi (hnd.2 ▸ hi)⟩)
    (fun _ _ _ _ h => h.elim) hsufB
  have h0 : (UInt32.ofNat 0 : Dom.Node) = 0 := rfl
  simp only [List.length_nil] at hres; rw [h0] at hres
  dsimp only [StateT.run] at hres ⊢
  rcases hres with ⟨targetsOut, sufRem, Snew, hfjNat, hlenT, htotLen, haMidLe, haMidBound, hnodeMid, hfrMid, hSnew, hCleanOut⟩
  simp only [List.nil_append] at hnodeMid hCleanOut
  simp only [List.length_append] at htotLen
  cases hK : applyKeyedStepsM (m := StateM (DomArena msg)) parent live 0 steps a with
  | mk finalJ aMid =>
      rw [hK] at hfjNat haMidLe haMidBound hnodeMid hfrMid hSnew hCleanOut
      have hfjEq : finalJ = UInt32.ofNat targetsOut.length :=
        uint32_eq_of_toNat_eq (by rw [hfjNat, hlenT, Nat.zero_add, uint32_toNat_ofNat_lt _ (by omega)])
      have hfin := finish_reconcile_removeTail f parent pns ptag pst pmg childNs c₂ Srem Snew a aMid targetsOut sufRem
        (by omega) haMidLe haMidBound hnodeMid
        (fun m hmPar hmS hmLt => hfrMid m hmPar (fun h => h.elim) (fun i hsi => hmS (hSiSub i m.toNat hsi)) hmLt)
        (fun k hk => by rcases hSnew k hk with ⟨hF | ⟨i, hSi⟩ | hA, hnp⟩; exact hF.elim; exact ⟨.inl (hSiSub i k hSi), hnp⟩; exact ⟨.inr hA, hnp⟩)
        hCleanOut
      dsimp only [StateT.run, bind, StateT.bind] at hfin ⊢
      rw [hsnap]; dsimp only; rw [hK, hfjEq]; dsimp only
      rwa [uint32_toNat_ofNat_lt targetsOut.length (by omega)]

theorem applyToDomM_spec {msg : Type} (fuel : Nat) : @PatchSpecAt msg fuel := by
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
      intro childNs parent pns ptag pst pmg oldH newH node pre suf Sold a
        hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hcleanOld hcleanNew
      cases fuel with
      | zero => cases newH <;> simp [htmlDepth] at hdep
      | succ f =>
          have hPatchF : @PatchSpecAt msg f := ih f (Nat.lt_succ_self f)
          cases oldH with
          | text sOld =>
              cases newH with
              | text sNew =>
                  rcases hcleanOld with ⟨hnodeIn, hnodeGet⟩
                  have hne : node ≠ parent := fun h => hparOut (h ▸ hnodeIn)
                  dsimp only [diff, applyToDomM, StateT.run, MonadDom.setText, DomArena.modify]
                  rw [hnodeGet]; dsimp only
                  refine ⟨Nat.le_refl _, by simp [htmlNodeCount],
                    fun m _ hmOut _ => DomArena.get_set_ne _ _ (fun heq => hmOut (congrArg UInt32.toNat heq ▸ hnodeIn)),
                    node, .inr rfl, ?_, hnd, hparNodes, .inl hnodeIn, DomArena.get_set_self _ _ _⟩
                  rw [DomArena.get_set_ne _ _ hne.symm, hpar]
              | element t₂ a₂ c₂ =>
                  rcases replace_child_clean (f + 1) childNs parent pns ptag pst pmg (.element t₂ a₂ c₂) node pre suf Sold a
                    hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hSoldLt hparNodes hcleanNew with ⟨hle, hbd, hfr, n2, _, hpar', hnd', hnodes', hcl'⟩
                  exact ⟨hle, hbd, hfr, n2, .inl rfl, hpar', hnd', hnodes', hcl'⟩
          | element t₁ a₁ c₁ =>
              cases newH with
              | text sNew =>
                  rcases replace_child_clean (f + 1) childNs parent pns ptag pst pmg (.text sNew) node pre suf Sold a
                    hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hSoldLt hparNodes hcleanNew with ⟨hle, hbd, hfr, n2, _, hpar', hnd', hnodes', hcl'⟩
                  exact ⟨hle, hbd, hfr, n2, .inl rfl, hpar', hnd', hnodes', hcl'⟩
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
                    have hchildNsV : childNs = "" ∨ childNs = Dom.svgNs := by rw [hchildNs]; split <;> simp
                    have hccNs := childNamespace_eq_childNsOf (ptag := t₁) hchildNsV
                    have haSet := DomArena.set_get_self a hnodeGet
                    have hattrs := ElemClean_applyAttrsM a node realNs t₁ st mg domCs a₂ hElClean ha₂Clean
                    rw [haSet] at hattrs
                    rcases hattrs with ⟨st', ha1Get, ha1Equiv, hElClean'⟩
                    let mg' := (normalizeAttrs a₂).filterMap managedAttrName
                    let a1 := (applyAttrsM (m := StateM (DomArena msg)) node a₂ a).2
                    have ha1Next : a1.nextId = a.nextId := by have hnx := applyAttrsM_nextId a node a₂ (.element realNs t₁ st mg domCs); rw [haSet] at hnx; exact hnx
                    have ha1Ne : ∀ m, m ≠ node → a1.get m = a.get m := fun m hm => by have := applyAttrsM_get_ne a node a₂ (.element realNs t₁ st mg domCs) m hm; rw [haSet] at this; exact this
                    have hCleanCs1 := CleanDomChildren_frame (fun m hm => ha1Ne m (node_ne_of_toNat_ne hm.2)) hCleanCs
                    have hndCs := CleanDomChildren_nodup hCleanCs
                    have hdomLe : domCs.length ≤ a1.nextId := nodup_nodes_lt_length_le a1.nextId domCs hndCs.1 fun r hr => by
                      rw [ha1Next]; exact hSoldLt _ (CleanDomChildren_mem hCleanCs r hr).1
                    have hcount0 : MonadDom.childCount (m := StateM (DomArena msg)) node a1 = (UInt32.ofNat domCs.length, a1) := by
                      change (match a1.get node with | .element _ _ _ _ cs | .fragment cs => UInt32.ofNat cs.length | _ => 0, a1) = _
                      rw [ha1Get]
                    have hdiffEx : ∃ steps, diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂) = .patchElement a₂ steps := by
                      cases h : diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂) with
                      | replace _ | setText _ => simp [diff] at h
                      | patchElement a₂' s => have : a₂' = a₂ := by simp [diff] at h; exact h.1.symm
                                              subst this; exact ⟨s, rfl⟩
                    rcases hdiffEx with ⟨steps, hdiffEq⟩
                    have hvalid := diff_steps_valid hdiffEq
                    have hA : applyAttrsM (m := StateM (DomArena msg)) node a₂ a = ((), a1) := rfl
                    have hfinish : ∀ (aOut : DomArena msg),
                        (applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂)) a).2 = aOut →
                        (∃ targetsOut Snew, a1.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a1.nextId + htmlListNodeCount c₂ ∧
                          aOut.get node = .element realNs t₁ st' mg' targetsOut ∧
                          (∀ m : Dom.Node, m ≠ node → ¬(Sold m.toNat ∧ m.toNat ≠ node.toNat) → m.toNat < a1.nextId → aOut.get m = a1.get m) ∧
                          (∀ k, Snew k → ((Sold k ∧ k ≠ node.toNat) ∨ (a1.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ node.toNat) ∧
                          CleanDomChildren f (Dom.childNsOf childNs t₁) c₂ aOut Snew targetsOut) →
                        a.nextId ≤ ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂))).run a).2.nextId ∧
                        ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂))).run a).2.nextId ≤ a.nextId + htmlNodeCount (.element t₁ a₂ c₂) ∧
                        (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId →
                          ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂))).run a).2.get m = a.get m) ∧
                        ∃ newNode, (diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂) = .replace (.element t₁ a₂ c₂) ∨ newNode = node) ∧
                          ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂))).run a).2.get parent = .element pns ptag pst pmg (pre ++ newNode :: suf) ∧
                          (pre ++ newNode :: suf).Nodup ∧
                          (∀ r ∈ pre ++ newNode :: suf, r.toNat < ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂))).run a).2.nextId) ∧
                          CleanDomSubtree (f + 1) childNs (.element t₁ a₂ c₂)
                            ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂))).run a).2
                            (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂))).run a).2.nextId))
                            newNode := by
                      intro aOut hrun hres
                      rcases hres with ⟨targetsOut, Snew, haOutGe, haOutBound, hnodeOut, hfrOut, hSnew, hCleanOut⟩
                      dsimp only [StateT.run]; rw [hrun]
                      refine ⟨by omega, by simp only [htmlNodeCount]; omega, fun m hmPar hmOut hmLt => ?_, node, .inr rfl, ?_, hnd,
                        fun r hr => Nat.lt_of_lt_of_le (hparNodes r hr) (by omega),
                        .inl hnodeIn, hownNewF, ha₂Clean, st', mg', targetsOut, hnodeOut, hElClean',
                        ha1Equiv, fun nm hnm => List.contains_iff_mem.2 hnm, ?_⟩
                      · have hmNeNode : m ≠ node := fun h => hmOut (h ▸ hnodeIn)
                        rw [hfrOut m hmNeNode (fun h => hmOut h.1) (by omega), ha1Ne m hmNeNode]
                      · rw [hfrOut parent hne.symm (fun h => hparOut h.1) (by omega), ha1Ne parent hne.symm, hpar]
                      · exact CleanDomChildren_mono (fun k hk => ⟨(hSnew k hk).1.elim (fun h => .inl h.1) (fun h => .inr ⟨by omega, h.2⟩), (hSnew k hk).2⟩) hCleanOut
                    by_cases hposSt : positional 0 steps = true
                    · refine hfinish _ ?_ (applyPositionalStepsM_with_removeTail f hPatchF node realNs t₁ st' mg' (Dom.childNsOf childNs t₁) hccNs.symm
                        steps c₁ c₂ domCs (fun k => Sold k ∧ k ≠ node.toNat) a1 hvalid.1 hposSt hvalid hc₂Clean hc₂Dep
                        (by omega) (by omega) (by omega) ha1Get (fun k hk => ⟨hk.2, by rw [ha1Next]; exact hSoldLt k hk.1⟩) hCleanCs1)
                      rw [hdiffEq]; dsimp only [applyToDomM, bind, StateT.bind, pure, StateT.pure]
                      rw [hA]; dsimp only; simp only [hownNewF, Bool.false_eq_true, ↓reduceIte, StateT.bind, bind]
                      rw [ha1Get]; dsimp only; simp only [hposSt, ↓reduceIte]; rfl
                    · have hposF : positional 0 steps = false := Bool.eq_false_iff.2 hposSt
                      have hdomLen : (UInt32.ofNat domCs.length).toNat = domCs.length := uint32_toNat_ofNat_lt _ (by omega)
                      refine hfinish _ ?_ (applyKeyedStepsM_with_removeTail_spec f hPatchF node realNs t₁ st' mg' (Dom.childNsOf childNs t₁) hccNs.symm
                        steps c₁ c₂ domCs (fun k => Sold k ∧ k ≠ node.toNat) a1 hvalid hc₂Clean hc₂Dep
                        (by omega) (by omega) (by omega) ha1Get (fun k hk => ⟨hk.2, by rw [ha1Next]; exact hSoldLt k hk.1⟩) hCleanCs1)
                      rw [hdiffEq]; dsimp only [applyToDomM, bind, StateT.bind, pure, StateT.pure]
                      rw [hA]; dsimp only; simp only [hownNewF, Bool.false_eq_true, ↓reduceIte, StateT.bind, bind]
                      rw [ha1Get]; dsimp only; simp only [hposF, Bool.false_eq_true, ↓reduceIte, hdomLen]; rfl
                  · have hdiffR : diff (.element t₁ a₁ c₁) (.element t₂ a₂ c₂) = .replace (.element t₂ a₂ c₂) := by simp [diff, ht]
                    rcases replace_child_clean (f + 1) childNs parent pns ptag pst pmg (.element t₂ a₂ c₂) node pre suf Sold a
                      hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hSoldLt hparNodes hcleanNew with ⟨hle, hbd, hfr, n2, _, hpar', hnd', hnodes', hcl'⟩
                    rw [hdiffR]; exact ⟨hle, hbd, hfr, n2, .inl rfl, hpar', hnd', hnodes', hcl'⟩

theorem applyPositionalStepsM_spec {msg : Type} (f : Nat)
    (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (childNs : String) (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (steps : List (KeyedStep msg)) (c₁ c₂ : List (Html msg)) (domCs : List Dom.Node) (Srem : Nat → Prop) (a : DomArena msg)
    (hsteps : steps.length = c₂.length) (hpos : positional 0 steps = true)
    (hvalid : DiffStepsValid c₁ c₂ steps) (hclean : Html.DomCleanList c₂ = true) (hdep : htmlListDepth c₂ ≤ f)
    (hbound : a.nextId + htmlListNodeCount c₂ < UInt32.size) (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg domCs) (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId)
    (hCleanCs : CleanDomChildren f childNs c₁ a Srem domCs) :
    let aOut := ((applyPositionalStepsM (m := StateM (DomArena msg)) parent 0 steps).run a).2
    ∃ targetsOut sufRem Snew, targetsOut.length = steps.length ∧ (targetsOut ++ sufRem).length ≤ domCs.length + steps.length ∧
      a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount c₂ ∧ aOut.get parent = .element pns ptag pst pmg (targetsOut ++ sufRem) ∧
      (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      (∀ k, Snew k → (Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧ CleanDomChildren f childNs c₂ aOut Snew targetsOut :=
  applyPositionalStepsM_clean_at0 f (applyToDomM_spec f) parent pns ptag pst pmg childNs hchildNs
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
  dsimp only [StateT.run] at hSpec
  cases hd : diff oldH newH with
  | replace h2 =>
      have h2Eq : h2 = newH := by
        cases oldH <;> cases newH <;> simp [diff] at hd <;> try (subst hd; rfl)
        split at hd <;> simp at hd; subst hd; rfl
      subst h2Eq
      have hrep := replace_child_clean f childNs parent pns ptag pst pmg h2 node pre suf Sold a
        hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hSoldLt hparNodes hcleanNew
      dsimp only [StateT.run] at hrep
      rcases hrep with ⟨hle, hbd, hfr, n2, hn2Eq, hpar', hnd', hnodes', hcl'⟩
      have hEqRun :
          (StateT.bind (MonadDom.childNamespace (m := StateM (DomArena msg)) parent) fun ns' =>
           StateT.bind (buildDomM (m := StateM (DomArena msg)) ns' h2) fun n2' =>
           StateT.bind (MonadDom.replaceChild (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) n2') fun _ => StateT.pure n2') a =
          (n2, ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (.replace h2)).run a).2) := by
        dsimp only [applyToDomM, StateT.run, bind, StateT.bind, pure, StateT.pure]
        have hns : MonadDom.childNamespace (m := StateM (DomArena msg)) parent a = (childNs, a) := by
          simp [MonadDom.childNamespace, hpar, hchildNs]
        change (match MonadDom.childNamespace (m := StateM (DomArena msg)) parent a with
                | (ns', a1) => match buildDomM (m := StateM (DomArena msg)) ns' h2 a1 with
                  | (n2', a2) => match MonadDom.replaceChild (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) n2' a2 with
                    | (_, a3) => (n2', a3)) =
               (n2, (match MonadDom.childNamespace (m := StateM (DomArena msg)) parent a with
                    | (ns', a1) => match buildDomM (m := StateM (DomArena msg)) ns' h2 a1 with
                      | (n2', a2) => MonadDom.replaceChild (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) n2' a2).2)
        rw [hns]; dsimp only
        cases hB : buildDomM (m := StateM (DomArena msg)) childNs h2 a with
        | mk n' a' =>
            rw [hB] at hn2Eq; dsimp only at hn2Eq; subst hn2Eq
            cases hR : MonadDom.replaceChild (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) n2 a' with
            | mk _ a3 => rfl
      dsimp only [patchHtmlSubtreeM, StateT.run, bind, StateT.bind, pure, StateT.pure]; rw [hd]; dsimp only; rw [hEqRun]
      exact ⟨hle, hbd, hfr, hpar', hnd', hnodes', hcl', CleanDomSubtree_equiv hcl'⟩
  | setText _ | patchElement _ _ =>
      rw [hd] at hSpec; rcases hSpec with ⟨hle, hbd, hfr, newNode, hEq, hpar', hnd', hnodes', hcl'⟩
      rcases hEq with hc | rfl; cases hc
      dsimp only [patchHtmlSubtreeM, StateT.run, bind, StateT.bind, pure, StateT.pure]; rw [hd]; dsimp only
      exact ⟨hle, hbd, hfr, hpar', hnd', hnodes', hcl', CleanDomSubtree_equiv hcl'⟩

end Qed
