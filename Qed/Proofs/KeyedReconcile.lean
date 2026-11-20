import Qed.Proofs.DomArena

namespace Qed

/-! ## Pure Diff & W3C `insertBefore` Keyed/Positional Reconciler Equivalence -/

theorem insertBeforeRef_split {child ref : Dom.Node} :
    ∀ (pre suf : List Dom.Node),
      ref ∉ pre →
      insertBeforeRef child ref (pre ++ ref :: suf) = pre ++ child :: ref :: suf
  | [], suf, _ => by simp [insertBeforeRef]
  | x :: xs, suf, href => by
      have hne : (x == ref) = false := beq_eq_false_iff_ne.2 (fun h => href (by simp [h]))
      simp [insertBeforeRef, hne, insertBeforeRef_split xs suf (fun h => href (List.mem_cons_of_mem x h))]

theorem erase_append_right_of_not_mem {α : Type} [BEq α] [LawfulBEq α]
    (pre suf : List α) {x : α} (hnot : x ∉ pre) :
    (pre ++ suf).erase x = pre ++ suf.erase x := by
  induction pre with
  | nil => rfl
  | cons a rest ih =>
      have hne : (a == x) = false := beq_eq_false_iff_ne.2 (fun h => hnot (by simp [h]))
      simp [hne, ih (fun h => hnot (List.mem_cons_of_mem a h))]

private theorem not_mem_left_of_nodup_append {α : Type} {xs ys : List α} {y : α}
    (hnd : (xs ++ ys).Nodup) (hy : y ∈ ys) : y ∉ xs := by
  induction xs with
  | nil => intro h; nomatch h
  | cons x rest ih =>
      rcases List.nodup_cons.1 hnd with ⟨hx, hrest⟩
      intro hm
      rcases List.mem_cons.1 hm with rfl | htail
      · exact hx (List.mem_append_right rest hy)
      · exact ih hrest htail

private theorem nodup_reinsert {α : Type} [BEq α] [LawfulBEq α] {pre suf : List α} {c : α}
    (hnd : (pre ++ suf).Nodup) (hc : c ∉ pre) :
    (pre ++ c :: suf.erase c).Nodup := by
  induction pre with
  | nil =>
      simp only [List.nil_append] at hnd ⊢
      refine List.nodup_cons.2 ⟨?_, hnd.erase c⟩
      clear hc
      induction suf with
      | nil => simp
      | cons s srest ihS =>
          rcases List.nodup_cons.1 hnd with ⟨hs, hsrest⟩
          by_cases hsc : s == c
          · have heq : s = c := eq_of_beq hsc
            subst heq; simpa [List.erase_cons] using hs
          · simp only [List.erase_cons, hsc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, not_or]
            refine ⟨fun h => hsc (beq_iff_eq.2 h.symm), ihS hsrest⟩
  | cons p prest ih =>
      simp only [List.cons_append] at hnd ⊢
      rcases List.nodup_cons.1 hnd with ⟨hp, hprest⟩
      have hcp : c ≠ p := fun h => hc (by simp [h])
      refine List.nodup_cons.2 ⟨?_, ih hprest (fun h => hc (List.mem_cons_of_mem p h))⟩
      intro hm
      rcases List.mem_append.1 hm with h1 | h2
      · exact hp (List.mem_append_left _ h1)
      · rcases List.mem_cons.1 h2 with hpeq | her
        · exact hcp hpeq.symm
        · exact hp (List.mem_append_right _ (List.mem_of_mem_erase her))

/-- Unified W3C `insertBefore` step theorem: whether `child` is freshly created (`child ∉ suf`)
    or reused from `suf` (`child ∈ suf`), as long as `(pre ++ suf).Nodup` and `child ∉ pre`,
    `w3cInsertBefore (pre ++ suf) pre.length child = pre ++ child :: suf.erase child`. -/
theorem w3cInsertBefore_step (pre suf : List Dom.Node) (child : Dom.Node)
    (hnd : (pre ++ suf).Nodup) (hnotPre : child ∉ pre) :
    w3cInsertBefore (pre ++ suf) pre.length child = pre ++ child :: suf.erase child := by
  unfold w3cInsertBefore
  rw [List.drop_left]
  cases suf with
  | nil => simp [List.erase_of_not_mem hnotPre]
  | cons ref rest =>
      by_cases hrc : ref == child
      · have heq : ref = child := eq_of_beq hrc
        subst heq; simp
      · simp only [hrc, Bool.false_eq_true, ↓reduceIte]
        rw [erase_append_right_of_not_mem pre (ref :: rest) hnotPre]
        have hrc' : (ref == child) = false := Bool.eq_false_iff.2 hrc
        simp only [List.erase_cons, hrc', Bool.false_eq_true, ↓reduceIte]
        have hrefNotPre : ref ∉ pre := not_mem_left_of_nodup_append hnd (List.mem_cons_self ..)
        exact insertBeforeRef_split pre (rest.erase child) hrefNotPre

def w3cPlaceSeq : List Dom.Node → Nat → List Dom.Node → List Dom.Node
  | cs, _, [] => cs
  | cs, j, target :: rest => w3cPlaceSeq (w3cInsertBefore cs j target) (j + 1) rest

theorem w3cPlaceSeq_invariant (targets : List Dom.Node) :
    ∀ (pre suf : List Dom.Node),
      (pre ++ suf).Nodup → targets.Nodup → (∀ t ∈ targets, t ∉ pre) →
      ∃ rem, w3cPlaceSeq (pre ++ suf) pre.length targets = pre ++ targets ++ rem := by
  induction targets with
  | nil => intro pre suf _ _ _; exact ⟨suf, by simp [w3cPlaceSeq]⟩
  | cons t rest ih =>
      intro pre suf hnd htnd hdisj
      rcases List.nodup_cons.1 htnd with ⟨htRest, hrestNd⟩
      have htNotPre : t ∉ pre := hdisj t (List.mem_cons_self ..)
      have hstep := w3cInsertBefore_step pre suf t hnd htNotPre
      have hnd' : ((pre ++ [t]) ++ suf.erase t).Nodup := by
        simpa [List.append_assoc] using nodup_reinsert hnd htNotPre
      have hdisj' : ∀ r ∈ rest, r ∉ pre ++ [t] := by
        intro r hr hm
        rcases List.mem_append.1 hm with h1 | h2
        · exact hdisj r (List.mem_cons_of_mem t hr) h1
        · simp only [List.mem_singleton] at h2; subst h2; exact htRest hr
      have hlen' : (pre ++ [t]).length = pre.length + 1 := by simp
      rcases ih (pre ++ [t]) (suf.erase t) hnd' hrestNd hdisj' with ⟨rem, heq⟩
      refine ⟨rem, ?_⟩
      simp only [w3cPlaceSeq, hstep]
      have hassoc : pre ++ t :: suf.erase t = (pre ++ [t]) ++ suf.erase t := by simp
      rw [hassoc, ← hlen', heq]; simp [List.append_assoc]

/-- Complete keyed child-order reconciliation theorem: placing any duplicate-free `targets` sequence
    via W3C `insertBefore` over an existing duplicate-free `live` child list and removing the
    trailing unused suffix yields `targets` in exact order. -/
theorem w3cReconcileKeyed_eq (live targets : List Dom.Node)
    (hlive : live.Nodup) (htargets : targets.Nodup) :
    let placed := w3cPlaceSeq live 0 targets
    removeTailSpec targets.length (placed.length - targets.length) placed = targets := by
  rcases w3cPlaceSeq_invariant targets [] live (by simpa using hlive) htargets
    (fun _ _ h => nomatch h) with ⟨rem, hplaced⟩
  dsimp only; simp only [List.nil_append, List.length_nil] at hplaced
  rw [hplaced]
  have hsub : (targets ++ rem).length - targets.length = rem.length := by simp
  rw [hsub]; exact removeTailSpec_append targets rem

/-! ## Child Reconciliation & Full Subtree Patching on `DomArena` -/

private theorem getElem?_getD_of_lt {α : Type} (xs : List α) (i : Nat) (d : α) (h : i < xs.length) :
    xs[i]?.getD d = xs[i] := by simp [List.getElem?_eq_getElem h]

theorem snapshotChildrenM_spec (a : DomArena msg) (node : Dom.Node) (pns ptag : String)
    (pst : SpecElemState msg) (pmg : List String) (cs : List Dom.Node)
    (hsize : cs.length < UInt32.size) :
    ∀ (i rem : Nat) (acc : Array Dom.Node),
      i + rem = cs.length →
      (snapshotChildrenM (m := StateM (DomArena msg)) node i acc rem).run
        (a.set node (.element pns ptag pst pmg cs)) =
        (⟨acc.toList ++ cs.drop i⟩, a.set node (.element pns ptag pst pmg cs)) := by
  intro i rem; induction rem generalizing i with
  | zero =>
      intro acc hsum
      have hi : i = cs.length := by omega
      subst hi; cases acc with | mk _ => simp [snapshotChildrenM, StateT.run, pure, StateT.pure]
  | succ r ih =>
      intro acc hsum
      have hlt : i < cs.length := by omega
      have hu : (UInt32.ofNat i).toNat = i := uint32_toNat_ofNat_lt i (by omega)
      have hchildAt :
          (MonadDom.childAt (m := StateM (DomArena msg)) node (UInt32.ofNat i)).run
            (a.set node (.element pns ptag pst pmg cs)) =
            (cs[i], a.set node (.element pns ptag pst pmg cs)) := by
        simp [MonadDom.childAt, StateT.run, DomArena.get_set_self, hu, getElem?_getD_of_lt cs i 0 hlt]
      have hdrop : cs.drop i = cs[i] :: cs.drop (i + 1) := List.drop_eq_getElem_cons hlt
      dsimp only [snapshotChildrenM, StateT.run, bind, StateT.bind]
      change (match (MonadDom.childAt (m := StateM (DomArena msg)) node (UInt32.ofNat i)).run
                (a.set node (.element pns ptag pst pmg cs)) with
              | (child, s') =>
                (snapshotChildrenM (m := StateM (DomArena msg)) node (i + 1) (acc.push child) r).run s') = _
      rw [hchildAt]; dsimp only; rw [ih (i + 1) (acc.push cs[i]) (by omega)]
      simp only [Array.toList_push, List.append_assoc, List.singleton_append, hdrop]

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

theorem w3cInsertBefore_fresh_append (pre suf : List Dom.Node) (cn : Dom.Node)
    (hnot : cn ∉ pre ++ suf) (hdisj : ∀ r ∈ suf, r ∉ pre) :
    w3cInsertBefore (pre ++ suf) pre.length cn = pre ++ cn :: suf := by
  unfold w3cInsertBefore; rw [List.drop_left, List.erase_of_not_mem hnot]
  cases suf with
  | nil => simp
  | cons ref rest =>
      have hrc : (ref == cn) = false := beq_eq_false_iff_ne.2 (fun h => hnot (by simp [h]))
      simp only [hrc, Bool.false_eq_true, ↓reduceIte]
      exact insertBeforeRef_split pre rest (hdisj ref (List.mem_cons_self ..))

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

mutual
  def CleanDomSubtree {msg : Type} : Nat → String → Html msg → DomArena msg → (Nat → Prop) → Dom.Node → Prop
    | 0, _, _, _, _, _ => False
    | _ + 1, _, .text s, a, S, n => S n.toNat ∧ a.get n = .text s
    | f + 1, ns, .element tag attrs cs, a, S, n =>
        let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
        S n.toNat ∧ ownsChildren attrs = false ∧ attrs.all Attr.DomClean = true ∧
        ∃ st mg domCs, a.get n = .element realNs tag st mg domCs ∧
          ElemClean st mg ∧ ElemStateEquiv st (evalSpecAttrs attrs) ∧
          (∀ nm ∈ (normalizeAttrs attrs).filterMap managedAttrName, mg.contains nm = true) ∧
          CleanDomChildren f (Dom.childNsOf ns tag) cs a (fun k => S k ∧ k ≠ n.toNat) domCs

  def CleanDomChildren {msg : Type} : Nat → String → List (Html msg) → DomArena msg → (Nat → Prop) → List Dom.Node → Prop
    | _, _, [], _, _, [] => True
    | f, ns, c :: cs, a, S, d :: ds =>
        ∃ Sc Srest, (∀ k, Sc k → S k) ∧ (∀ k, Srest k → S k) ∧ (∀ k, Sc k → Srest k → False) ∧
          CleanDomSubtree f ns c a Sc d ∧ CleanDomChildren f ns cs a Srest ds
    | _, _, _, _, _, _ => False
end

theorem CleanDomSubtree_root_mem {msg : Type} :
    ∀ {f : Nat} {ns : String} {h : Html msg} {a : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
      CleanDomSubtree f ns h a S n → S n.toNat
  | 0, _, _, _, _, _, h => by simp [CleanDomSubtree] at h
  | _ + 1, _, .text _, _, _, _, h => h.1
  | _ + 1, _, .element _ _ _, _, _, _, h => h.1

theorem CleanDomChildren_mem {msg : Type} :
    ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node},
      CleanDomChildren f ns cs a S ds → ∀ d ∈ ds, S d.toNat
  | _, _, [], _, _, [], _ => fun _ hm => nomatch hm
  | _, _, _ :: _, _, _, _ :: _, ⟨_, _, hSc, hSr, _, hHd, hTl⟩ => fun d hd => by
      rcases List.mem_cons.1 hd with rfl | hr
      · exact hSc _ (CleanDomSubtree_root_mem hHd)
      · exact hSr _ (CleanDomChildren_mem hTl d hr)
  | _, _, [], _, _, _ :: _, h => False.elim h
  | _, _, _ :: _, _, _, [], h => False.elim h

theorem CleanDomChildren_nodup {msg : Type} :
    ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node},
      CleanDomChildren f ns cs a S ds → ds.Nodup ∧ ds.length = cs.length
  | _, _, [], _, _, [], _ => ⟨List.nodup_nil, rfl⟩
  | _, _, _ :: _, _, _, _ :: _, ⟨_, _, _, _, hDisj, hHd, hTl⟩ => by
      have ⟨hnd, hlen⟩ := CleanDomChildren_nodup hTl
      exact ⟨List.nodup_cons.2 ⟨fun hm => hDisj _ (CleanDomSubtree_root_mem hHd) (CleanDomChildren_mem hTl _ hm), hnd⟩, by simp [hlen]⟩
  | _, _, [], _, _, _ :: _, h => False.elim h
  | _, _, _ :: _, _, _, [], h => False.elim h

mutual
  theorem CleanDomSubtree_mono {msg : Type} :
      ∀ {f : Nat} {ns : String} {h : Html msg} {a : DomArena msg} {S S' : Nat → Prop} {n : Dom.Node},
        (∀ k, S k → S' k) → CleanDomSubtree f ns h a S n → CleanDomSubtree f ns h a S' n
    | 0, _, _, _, _, _, _, _, hc => by simp [CleanDomSubtree] at hc
    | _ + 1, _, .text _, _, _, _, _, hsub, ⟨hn, hg⟩ => ⟨hsub _ hn, hg⟩
    | f + 1, ns, .element _ _ _, _, _, _, n, hsub, ⟨hn, ho, ha, st, mg, domCs, hg, hcl, heq, hmg, hcs⟩ =>
        ⟨hsub _ hn, ho, ha, st, mg, domCs, hg, hcl, heq, hmg, CleanDomChildren_mono (fun _ hk => ⟨hsub _ hk.1, hk.2⟩) hcs⟩

  theorem CleanDomChildren_mono {msg : Type} :
      ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S S' : Nat → Prop} {ds : List Dom.Node},
        (∀ k, S k → S' k) → CleanDomChildren f ns cs a S ds → CleanDomChildren f ns cs a S' ds
    | _, _, [], _, _, _, [], _, _ => trivial
    | _, _, _ :: _, _, _, _, _ :: _, hsub, ⟨Sc, Srest, hSc, hSr, hDisj, hHd, hTl⟩ =>
        ⟨Sc, Srest, fun k hk => hsub k (hSc k hk), fun k hk => hsub k (hSr k hk), hDisj, hHd, hTl⟩
    | _, _, [], _, _, _, _ :: _, _, hc => False.elim hc
    | _, _, _ :: _, _, _, _, [], _, hc => False.elim hc
end

mutual
  theorem CleanDomSubtree_frame {msg : Type} :
      ∀ {f : Nat} {ns : String} {h : Html msg} {a a' : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
        (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) → CleanDomSubtree f ns h a S n → CleanDomSubtree f ns h a' S n
    | 0, _, _, _, _, _, _, _, hc => by simp [CleanDomSubtree] at hc
    | _ + 1, _, .text _, _, _, _, n, hfr, ⟨hn, hg⟩ => ⟨hn, (hfr n hn).trans hg⟩
    | f + 1, ns, .element _ _ _, _, _, _, n, hfr, ⟨hn, ho, ha, st, mg, domCs, hg, hcl, heq, hmg, hcs⟩ =>
        ⟨hn, ho, ha, st, mg, domCs, (hfr n hn).trans hg, hcl, heq, hmg, CleanDomChildren_frame (fun m hm => hfr m hm.1) hcs⟩

  theorem CleanDomChildren_frame {msg : Type} :
      ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a a' : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node},
        (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) → CleanDomChildren f ns cs a S ds → CleanDomChildren f ns cs a' S ds
    | _, _, [], _, _, _, [], _, _ => trivial
    | _, _, _ :: _, _, _, _, _ :: _, hfr, ⟨Sc, Srest, hSc, hSr, hDisj, hHd, hTl⟩ =>
        ⟨Sc, Srest, hSc, hSr, hDisj,
         CleanDomSubtree_frame (fun m hm => hfr m (hSc _ hm)) hHd,
         CleanDomChildren_frame (fun m hm => hfr m (hSr _ hm)) hTl⟩
    | _, _, [], _, _, _, _ :: _, _, hc => False.elim hc
    | _, _, _ :: _, _, _, _, [], _, hc => False.elim hc
end

mutual
  theorem CleanDomSubtree_equiv {msg : Type} :
      ∀ {f : Nat} {ns : String} {h : Html msg} {a : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
        CleanDomSubtree f ns h a S n → DomTreeAssocEquiv (readDomTree f a n) (specDom ns h)
    | 0, _, _, _, _, _, hc => by simp [CleanDomSubtree] at hc
    | _ + 1, _, .text _, _, _, _, ⟨_, hg⟩ => by simp [readDomTree, hg, specDom, DomTreeAssocEquiv]
    | f + 1, _, .element _ _ _, _, _, _, ⟨_, ho, _, _, _, _, hg, _, heq, _, hcs⟩ => by
        dsimp only [readDomTree, specDom]; rw [hg, ho]; exact ⟨rfl, rfl, heq, CleanDomChildren_equiv hcs⟩

  theorem CleanDomChildren_equiv {msg : Type} :
      ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node},
        CleanDomChildren f ns cs a S ds → DomTreeListAssocEquiv (ds.map (readDomTree f a)) (specDomList ns cs)
    | _, _, [], _, _, [], _ => trivial
    | _, _, _ :: _, _, _, _ :: _, ⟨_, _, _, _, _, hHd, hTl⟩ => ⟨CleanDomSubtree_equiv hHd, CleanDomChildren_equiv hTl⟩
    | _, _, [], _, _, _ :: _, hc => False.elim hc
    | _, _, _ :: _, _, _, [], hc => False.elim hc
end

theorem CleanDomChildren_append {msg : Type} :
    ∀ {f : Nat} {ns : String} {xs₁ xs₂ : List (Html msg)} {a : DomArena msg}
      {S₁ S₂ : Nat → Prop} {ds₁ ds₂ : List Dom.Node},
      (∀ k, S₁ k → S₂ k → False) →
      CleanDomChildren f ns xs₁ a S₁ ds₁ → CleanDomChildren f ns xs₂ a S₂ ds₂ →
      CleanDomChildren f ns (xs₁ ++ xs₂) a (fun k => S₁ k ∨ S₂ k) (ds₁ ++ ds₂)
  | _, _, [], _, _, _, _, [], _, _, _, h2 => CleanDomChildren_mono (fun _ hk => .inr hk) h2
  | _, _, _ :: _, _, _, _, S₂, _ :: _, _, hDisj, ⟨Sc, Srest, hSc, hSr, hD, hHd, hTl⟩, h2 =>
      ⟨Sc, fun k => Srest k ∨ S₂ k, fun k hk => .inl (hSc k hk), fun k hk => hk.elim (fun h => .inl (hSr k h)) .inr,
       fun k hk1 hk2 => hk2.elim (hD k hk1) (hDisj k (hSc k hk1)), hHd, CleanDomChildren_append (fun k h1 h2' => hDisj k (hSr k h1) h2') hTl h2⟩
  | _, _, [], _, _, _, _, _ :: _, _, _, hc, _ => False.elim hc
  | _, _, _ :: _, _, _, _, _, [], _, _, hc, _ => False.elim hc

theorem CleanDomChildren_indexed {msg : Type} :
    ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node},
      CleanDomChildren f ns cs a S ds →
      ∃ (Si : Nat → Nat → Prop), (∀ i k, Si i k → S k) ∧
        (∀ i₁ i₂, i₁ ≠ i₂ → ∀ k, Si i₁ k → Si i₂ k → False) ∧
        (∀ (i : Nat) (h1 : i < cs.length) (h2 : i < ds.length), CleanDomSubtree f ns cs[i] a (Si i) ds[i])
  | _, _, [], _, _, [], _ => ⟨fun _ _ => False, fun _ _ h => h.elim, fun _ _ _ _ h => h.elim, fun _ h => nomatch h⟩
  | _, _, _ :: _, _, _, _ :: _, ⟨Sc, Srest, hSc, hSr, hDisj, hHd, hTl⟩ => by
      rcases CleanDomChildren_indexed hTl with ⟨SiTail, hSub, hPair, hGet⟩
      refine ⟨fun | 0 => Sc | i + 1 => SiTail i, ?_, ?_, ?_⟩
      · intro i k hk; cases i with | zero => exact hSc k hk | succ i => exact hSr k (hSub i k hk)
      · intro i₁ i₂ hne k h1 h2
        cases i₁ <;> cases i₂
        · exact absurd rfl hne
        · exact hDisj k h1 (hSub _ k h2)
        · exact hDisj k h2 (hSub _ k h1)
        · exact hPair _ _ (by omega) k h1 h2
      · intro i h1 h2; cases i with | zero => exact hHd | succ i => exact hGet i (by simpa using h1) (by simpa using h2)
  | _, _, [], _, _, _ :: _, hc => False.elim hc
  | _, _, _ :: _, _, _, [], hc => False.elim hc

mutual
  theorem CleanDomSubtree_DomClean {msg : Type} :
      ∀ {f : Nat} {ns : String} {h : Html msg} {a : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
        CleanDomSubtree f ns h a S n → h.DomClean = true
    | 0, _, _, _, _, _, hc => by simp [CleanDomSubtree] at hc
    | _ + 1, _, .text _, _, _, _, _ => rfl
    | _ + 1, _, .element _ _ _, _, _, _, ⟨_, ho, ha, _, _, _, _, _, _, _, hcs⟩ => by
        simp [Html.DomClean, ho, ha, CleanDomChildren_DomCleanList hcs]

  theorem CleanDomChildren_DomCleanList {msg : Type} :
      ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node},
        CleanDomChildren f ns cs a S ds → Html.DomCleanList cs = true
    | _, _, [], _, _, [], _ => rfl
    | _, _, _ :: _, _, _, _ :: _, ⟨_, _, _, _, _, hHd, hTl⟩ => by
        simp [Html.DomCleanList, CleanDomSubtree_DomClean hHd, CleanDomChildren_DomCleanList hTl]
    | _, _, [], _, _, _ :: _, hc => False.elim hc
    | _, _, _ :: _, _, _, [], hc => False.elim hc
end

theorem CleanDomSubtree_not_fragment {msg : Type} {f : Nat} {ns : String} {h : Html msg}
    {a : DomArena msg} {S : Nat → Prop} {n : Dom.Node} (hcl : CleanDomSubtree f ns h a S n) :
    ∀ fcs, a.get n ≠ .fragment fcs := by
  cases f with
  | zero => simp [CleanDomSubtree] at hcl
  | succ _ => cases h with
    | text _ => intro fcs hf; simp [CleanDomSubtree] at hcl; rw [hcl.2] at hf; cases hf
    | element _ _ _ => intro fcs hf; rcases hcl with ⟨_, _, _, _, _, _, hg, _⟩; rw [hg] at hf; cases hf

private theorem appendChild_nextId {msg : Type} (p c : Dom.Node) (a : DomArena msg) :
    ((MonadDom.appendChild (m := StateM (DomArena msg)) p c).run a).2.nextId = a.nextId := by
  dsimp only [MonadDom.appendChild, StateT.run]; split <;> rfl

mutual
  theorem buildDomM_nextId_mono {msg : Type} (ns : String) :
      ∀ (h : Html msg) (a : DomArena msg), a.nextId ≤ ((buildDomM (m := StateM (DomArena msg)) ns h).run a).2.nextId
    | .text _, _ => by simp [buildDomM, MonadDom.createText, DomArena.alloc, StateT.run]
    | .element tag attrs cs, a => by
        let node := UInt32.ofNat a.nextId
        let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
        let a1 : DomArena msg := { a with nextId := a.nextId + 1 }
        have hnx := applyAttrsM_nextId a1 node attrs (.element realNs tag {} [] [])
        dsimp only [StateT.run] at hnx
        dsimp only [buildDomM, MonadDom.createElement, DomArena.alloc, StateT.run, bind, StateT.bind, pure, StateT.pure]
        change a.nextId ≤ (match applyAttrsM (m := StateM (DomArena msg)) node attrs (a1.set node (.element realNs tag {} [] [])) with
          | (_, s) => (if (!ownsChildren attrs) = true then
              StateT.bind (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node cs) fun _ => StateT.pure node
            else (StateT.pure PUnit.unit).bind fun _ => StateT.pure node) s).2.nextId
        cases hres : applyAttrsM (m := StateM (DomArena msg)) node attrs (a1.set node (.element realNs tag {} [] [])) with
        | mk _ s1 =>
            rw [hres] at hnx
            have hs1 : a.nextId ≤ s1.nextId := by dsimp [a1] at hnx; omega
            cases ownsChildren attrs with
            | true => exact hs1
            | false =>
                have hm := buildDomListM_nextId_mono (Dom.childNsOf ns tag) node cs s1
                dsimp only [StateT.run] at hm; exact Nat.le_trans hs1 hm

  theorem buildDomListM_nextId_mono {msg : Type} (ns : String) (parent : Dom.Node) :
      ∀ (cs : List (Html msg)) (a : DomArena msg), a.nextId ≤ ((buildDomListM (m := StateM (DomArena msg)) ns parent cs).run a).2.nextId
    | [], _ => by simp [buildDomListM, StateT.run, pure, StateT.pure]
    | c :: rest, a => by
        have h1 := buildDomM_nextId_mono ns c a
        dsimp only [buildDomListM, StateT.run, bind, StateT.bind] at h1 ⊢
        cases hres : buildDomM (m := StateM (DomArena msg)) ns c a with
        | mk cn aMid =>
            rw [hres] at h1; dsimp only at h1
            have h2 := appendChild_nextId parent cn aMid
            dsimp only [StateT.run] at h2
            cases hApp : MonadDom.appendChild (m := StateM (DomArena msg)) parent cn aMid with
            | mk _ a2 =>
                rw [hApp] at h2; dsimp only at h2 ⊢
                have h3 := buildDomListM_nextId_mono ns parent rest a2
                dsimp only [StateT.run] at h3 ⊢
                exact Nat.le_trans h1 (by rw [← h2]; simpa [hApp] using h3)
end

mutual
  theorem CleanDomSubtree_of_buildDomM {msg : Type} (ns : String) :
      ∀ (h : Html msg) (a : DomArena msg) (fuel : Nat),
        h.DomClean = true → 0 < a.nextId → a.nextId + htmlNodeCount h < UInt32.size → htmlDepth h ≤ fuel →
        let (root, a') := (buildDomM (m := StateM (DomArena msg)) ns h).run a
        CleanDomSubtree fuel ns h a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root
    | .text s, a, fuel, _, _, hbound, hdep => by
        cases fuel with
        | zero => simp [htmlDepth] at hdep
        | succ _ =>
            simp only [htmlNodeCount] at hbound
            have htoNat : (UInt32.ofNat a.nextId).toNat = a.nextId := uint32_toNat_ofNat_lt _ (by omega)
            simp [buildDomM, MonadDom.createText, DomArena.alloc, StateT.run, CleanDomSubtree, DomArena.get, htoNat]
    | .element tag attrs children, a, fuel, hclean, hpos, hbound, hdep => by
        cases fuel with
        | zero => simp [htmlDepth] at hdep
        | succ f =>
            simp only [Html.DomClean, Bool.and_eq_true] at hclean
            rcases hclean with ⟨⟨hownT, hAclean⟩, hKclean⟩
            have hownF : ownsChildren attrs = false := by simpa using hownT
            simp only [htmlNodeCount] at hbound; simp only [htmlDepth] at hdep
            let node := UInt32.ofNat a.nextId
            have hnodeNat : node.toNat = a.nextId := uint32_toNat_ofNat_lt _ (by omega)
            let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
            let st := evalSpecAttrs attrs; let mg := (normalizeAttrs attrs).filterMap managedAttrName
            let a1 : DomArena msg := { a with nextId := a.nextId + 1 }
            have ha1Next : a1.nextId = a.nextId + 1 := rfl
            let aElem := a1.set node (.element realNs tag st mg [])
            have haElemNext : aElem.nextId = a.nextId + 1 := rfl
            have hrun : buildDomM (m := StateM (DomArena msg)) ns (.element tag attrs children) a =
                (node, (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node children aElem).2) := by
              dsimp only [buildDomM, MonadDom.createElement, DomArena.alloc, StateT.run, bind, StateT.bind, pure, StateT.pure]
              change (match applyAttrsM (m := StateM (DomArena msg)) node attrs (a1.set node (.element realNs tag {} [] [])) with
                      | (_, s) => (if (!ownsChildren attrs) = true then
                         StateT.bind (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node children) (fun _ => StateT.pure node)
                         else StateT.bind (StateT.pure PUnit.unit) (fun _ => StateT.pure node)) s) = _
              rw [applyAttrsM_fresh_element a1 node realNs tag [] attrs, hownF]; rfl
            rcases CleanDomChildren_of_buildDomListM (Dom.childNsOf ns tag) children [] a1 node (ArenaEntry.element realNs tag st mg)
              (.inl ⟨realNs, tag, st, mg, fun _ => rfl⟩) [] f
              (fun _ => False) hKclean (by omega) (by omega) (by omega) (by omega) (fun _ h => h.elim) trivial with
              ⟨csNew, aBase', ha'Eq, _, _, _, hcleanOut⟩
            have hmono := buildDomListM_nextId_mono (Dom.childNsOf ns tag) node children aElem
            dsimp only [StateT.run] at hmono ha'Eq hcleanOut ⊢
            rw [hrun]; dsimp only
            refine ⟨by omega, hownF, hAclean, st, mg, csNew, ?_,
              ElemClean_evalSpecAttrs hAclean, ElemStateEquiv.refl st,
              fun nm hnm => List.contains_iff_mem.2 hnm, ?_⟩
            · rw [ha'Eq, DomArena.get_set_self]; dsimp only [realNs]; simp only [List.nil_append]
            · refine CleanDomChildren_mono (fun k hk => ?_) (by simpa [List.nil_append] using hcleanOut)
              rcases hk with ⟨h1, h2⟩
              exact ⟨⟨by omega, h2⟩, fun heq => by dsimp only [a1] at h1; omega⟩

  theorem CleanDomChildren_of_buildDomListM {msg : Type} (childNs : String) :
      ∀ (cs hsAcc : List (Html msg)) (aBase : DomArena msg) (parent : Dom.Node)
        (mkPar : List Dom.Node → ArenaEntry msg),
        ((∃ pns ptag pst pmg, ∀ ds, mkPar ds = .element pns ptag pst pmg ds) ∨ (∀ ds, mkPar ds = .fragment ds)) →
        ∀ (acc : List Dom.Node) (f : Nat) (Sacc : Nat → Prop),
        Html.DomCleanList cs = true → parent.toNat < aBase.nextId → 0 < aBase.nextId → aBase.nextId + htmlListNodeCount cs < UInt32.size →
        htmlListDepth cs ≤ f → (∀ k, Sacc k → parent.toNat < k ∧ k < aBase.nextId) →
        CleanDomChildren f childNs hsAcc (aBase.set parent (mkPar acc)) Sacc acc →
        let aIn := aBase.set parent (mkPar acc)
        let aOut := ((buildDomListM (m := StateM (DomArena msg)) childNs parent cs).run aIn).2
        ∃ (csNew : List Dom.Node) (aBase' : DomArena msg),
          aOut = aBase'.set parent (mkPar (acc ++ csNew)) ∧
          aBase.nextId ≤ aOut.nextId ∧
          aOut.nextId ≤ aBase.nextId + htmlListNodeCount cs ∧
          (∀ m : Dom.Node, m.toNat < aBase.nextId → m ≠ parent → aOut.get m = aBase.get m) ∧
          CleanDomChildren f childNs (hsAcc ++ cs) aOut (fun k => Sacc k ∨ (aBase.nextId ≤ k ∧ k < aOut.nextId)) (acc ++ csNew)
    | [], hsAcc, aBase, parent, mkPar, _, acc, f, Sacc, _, _, _, _, _, _, haccClean => by
        refine ⟨[], aBase, by simp [buildDomListM, StateT.run, pure, StateT.pure],
          Nat.le_refl _, by simp [buildDomListM, StateT.run, pure, StateT.pure, htmlListNodeCount],
          fun m _ hne => by simp [buildDomListM, StateT.run, pure, StateT.pure, DomArena.get_set_ne _ _ hne], ?_⟩
        simpa [buildDomListM, StateT.run, pure, StateT.pure] using CleanDomChildren_mono (fun _ hk => .inl hk) haccClean
    | c :: rest, hsAcc, aBase, parent, mkPar, hmk, acc, f, Sacc,
        hclean, hparLt, hpos, hbound, hdep, hSacc, haccClean => by
        simp only [Html.DomCleanList, Bool.and_eq_true] at hclean
        simp only [htmlListNodeCount] at hbound; simp only [htmlListDepth] at hdep
        have hcDep : htmlDepth c ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
        have hrestDep : htmlListDepth rest ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
        let aIn := aBase.set parent (mkPar acc)
        have haInNext : aIn.nextId = aBase.nextId := rfl
        have hcSpec := buildDomM_spec childNs c aIn f (by omega) (by omega) hcDep
        have hcClean := CleanDomSubtree_of_buildDomM childNs c aIn f hclean.1 (by omega) (by omega) hcDep
        have haMidLe := buildDomM_nextId_mono childNs c aIn
        dsimp only [StateT.run] at hcSpec hcClean haMidLe
        cases hR : buildDomM (m := StateM (DomArena msg)) childNs c aIn with
        | mk cn aMid =>
            rw [hR] at hcSpec hcClean haMidLe; dsimp only at hcSpec hcClean haMidLe
            rcases hcSpec with ⟨hcnGe, hcnLt, haMidBound, haMidFrame, _, _⟩
            rw [haInNext] at hcnGe haMidLe haMidBound
            have hparInMid : aMid.get parent = mkPar acc := by
              rw [haMidFrame parent (by omega)]; simp [aIn, DomArena.get_set_self]
            have hcnNotFrag : ∀ fcs, aMid.get cn ≠ .fragment fcs := fun fcs => by
              have hb := buildDomM_not_fragment childNs c aIn f fcs (by omega) (by omega) hcDep
              dsimp only [StateT.run] at hb; rw [hR] at hb; exact hb
            have hcnNotInAcc : cn ∉ acc := fun hmem => by have := hSacc _ (CleanDomChildren_mem haccClean cn hmem); omega
            let aAfter := aMid.set parent (mkPar (acc ++ [cn]))
            have haAfterNext : aAfter.nextId = aMid.nextId := rfl
            let Sc : Nat → Prop := fun k => aBase.nextId ≤ k ∧ k < aMid.nextId
            have haccMid : CleanDomChildren f childNs hsAcc aAfter Sacc acc :=
              CleanDomChildren_frame (fun m hm => by
                have hb := hSacc _ hm; rw [DomArena.get_set_ne _ _ (fun h => by subst h; omega)]; exact haMidFrame m (by rw [haInNext]; exact hb.2)) haccClean
            have hcAfter : CleanDomSubtree f childNs c aAfter Sc cn :=
              CleanDomSubtree_frame (fun m _ => DomArena.get_set_ne _ _ fun heq => by subst heq; omega) hcClean
            have hcombClean : CleanDomChildren f childNs (hsAcc ++ [c]) aAfter (fun k => Sacc k ∨ Sc k) (acc ++ [cn]) :=
              CleanDomChildren_append (fun k hk1 hk2 => by have := hSacc k hk1; omega) haccMid
                (show CleanDomChildren f childNs [c] aAfter Sc [cn] from
                  ⟨Sc, fun _ => False, fun _ h => h, fun _ h => h.elim, fun _ _ h => h.elim, hcAfter, trivial⟩)
            rcases CleanDomChildren_of_buildDomListM childNs rest (hsAcc ++ [c]) aMid parent mkPar hmk (acc ++ [cn]) f
              (fun k => Sacc k ∨ Sc k) hclean.2 (by omega) (by omega) (by omega) hrestDep
              (fun k hk => hk.elim (fun h => let b := hSacc k h; ⟨b.1, by omega⟩) (fun h => ⟨by omega, h.2⟩))
              hcombClean with ⟨csRest, aBase'', haOutEq, haOutGe, haOutBound, haOutFrame, hcleanFinal⟩
            have hstepRun := buildDomListM_step childNs parent c rest aIn aMid cn mkPar hmk acc hR hparInMid hcnNotFrag hcnNotInAcc
            have haRestMono := buildDomListM_nextId_mono childNs parent rest aAfter
            dsimp only [StateT.run] at hstepRun hcleanFinal haOutEq haRestMono haOutGe haOutBound haOutFrame ⊢
            rw [haAfterNext] at haRestMono
            refine ⟨cn :: csRest, aBase'', by rw [hstepRun]; simpa [List.append_assoc, aAfter] using haOutEq,
              by rw [hstepRun]; omega, by rw [hstepRun]; simp only [htmlListNodeCount]; omega, fun m hm hne => ?_, ?_⟩
            · rw [hstepRun, haOutFrame m (by omega) hne, haMidFrame m (by rw [haInNext]; exact hm)]
              exact DomArena.get_set_ne _ _ hne
            · rw [hstepRun]; refine CleanDomChildren_mono (fun k hk => ?_) (by simpa [List.append_assoc, aAfter] using hcleanFinal)
              rcases hk with (hS | hSc) | hRest
              · exact .inl hS
              · exact .inr ⟨hSc.1, by omega⟩
              · exact .inr ⟨by omega, hRest.2⟩
end

theorem listReplaceAt_append_middle {α : Type} :
    ∀ (pre : List α) (x y : α) (suf : List α), listReplaceAt (pre ++ x :: suf) pre.length y = pre ++ y :: suf
  | [], _, _, _ => rfl
  | _ :: pre, x, y, suf => by simp [listReplaceAt, listReplaceAt_append_middle pre x y suf]

theorem list_length_le_htmlListNodeCount {msg : Type} :
    ∀ (cs : List (Html msg)), cs.length ≤ htmlListNodeCount cs
  | [] => Nat.le_refl 0
  | c :: cs => by
      have hc : 1 ≤ htmlNodeCount c := by cases c <;> (simp [htmlNodeCount]; try omega)
      have hcs := list_length_le_htmlListNodeCount cs; simp only [List.length_cons, htmlListNodeCount]; omega

private theorem nodup_snoc_append {α : Type} {pre suf : List α} {cn : α}
    (hnd : (pre ++ suf).Nodup) (hnot : cn ∉ pre ++ suf) : ((pre ++ [cn]) ++ suf).Nodup := by
  rcases List.nodup_append.1 hnd with ⟨hp, hs, hd⟩
  have hcns : cn ∉ pre ∧ cn ∉ suf := by simpa [List.mem_append, not_or] using hnot
  refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨hp, List.pairwise_singleton _ _, fun x hx y hy hEq => by
    simp only [List.mem_singleton] at hy; subst hy; subst hEq; exact hcns.1 hx⟩, hs, fun x hx y hy hEq => ?_⟩
  rcases List.mem_append.1 hx with hxp | hxc
  · exact hd x hxp y hy hEq
  · simp only [List.mem_singleton] at hxc; subst hxc; subst hEq; exact hcns.2 hy

private theorem not_mem_erase_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs : List α} {x : α}, xs.Nodup → x ∉ xs.erase x
  | [], _, _ => fun h => nomatch h
  | y :: ys, x, hnd => by
      rcases List.nodup_cons.1 hnd with ⟨hy, hys⟩
      by_cases hyx : y = x
      · subst hyx; simpa [List.erase_cons_head] using hy
      · have hbeq : (y == x) = false := beq_eq_false_iff_ne.2 hyx
        simp only [List.erase_cons, hbeq, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        intro h; rcases h with rfl | ht; exact hyx rfl; exact not_mem_erase_of_nodup hys ht

private theorem erase_nat_step (n : Nat) :
    ∀ (xs : List Nat), xs.Nodup → (∀ x ∈ xs, x < n + 1) →
      (xs.erase n).Nodup ∧ (∀ y ∈ xs.erase n, y < n) ∧ xs.length ≤ (xs.erase n).length + 1
  | [], _, _ => ⟨by simp, fun _ h => by simp at h, by simp⟩
  | x :: xs, hnd, hlt => by
      rcases List.nodup_cons.1 hnd with ⟨hxNot, hxsNd⟩
      have hxLt := hlt x (.head _); have hxsLt : ∀ y ∈ xs, y < n + 1 := fun y hy => hlt y (.tail _ hy)
      by_cases hxn : x = n
      · subst hxn; simp only [List.erase_cons_head]
        exact ⟨hxsNd, fun y hy => by have := hxsLt y hy; have hne : y ≠ x := fun h => hxNot (h ▸ hy); omega, Nat.le_refl _⟩
      · have hbeq : (x == n) = false := beq_eq_false_iff_ne.2 hxn
        simp only [List.erase_cons, hbeq, Bool.false_eq_true, ↓reduceIte]
        rcases erase_nat_step n xs hxsNd hxsLt with ⟨heNd, heLt, heLen⟩
        exact ⟨List.nodup_cons.2 ⟨fun h => hxNot (List.mem_of_mem_erase h), heNd⟩,
               fun y hy => by rcases List.mem_cons.1 hy with rfl | ht; omega; exact heLt y ht, by simp; omega⟩

theorem nodup_lt_length_le :
    ∀ (n : Nat) (xs : List Nat), xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, hlt => absurd (hlt x (.head _)) (Nat.not_lt_zero _)
  | n + 1, xs, hnd, hlt => by
      rcases erase_nat_step n xs hnd hlt with ⟨heNd, heLt, heLen⟩
      have := nodup_lt_length_le n (xs.erase n) heNd heLt; omega

theorem nodup_nodes_lt_length_le (n : Nat) (xs : List Dom.Node)
    (hnd : xs.Nodup) (hlt : ∀ x ∈ xs, x.toNat < n) : xs.length ≤ n := by
  have hmapNd : (xs.map UInt32.toNat).Nodup := by
    clear hlt; induction xs with
    | nil => exact List.nodup_nil
    | cons x xs ih =>
        rcases List.nodup_cons.1 hnd with ⟨hxNot, hxsNd⟩
        refine List.nodup_cons.2 ⟨fun hm => ?_, ih hxsNd⟩
        rcases List.mem_map.1 hm with ⟨y, hy, hyEq⟩; exact hxNot ((uint32_eq_of_toNat_eq hyEq) ▸ hy)
  have hmapLt : ∀ k ∈ xs.map UInt32.toNat, k < n := fun k hk => by rcases List.mem_map.1 hk with ⟨y, hy, rfl⟩; exact hlt y hy
  simpa using nodup_lt_length_le n (xs.map UInt32.toNat) hmapNd hmapLt

theorem nodup_append_replace {α : Type} {pre suf : List α} {x y : α}
    (hnd : (pre ++ x :: suf).Nodup) (hy : y = x ∨ y ∉ pre ++ x :: suf) : (pre ++ y :: suf).Nodup := by
  rcases hy with rfl | hnot
  · exact hnd
  · rcases List.nodup_append.1 hnd with ⟨hpre, hcons, hdisj⟩
    rcases List.nodup_cons.1 hcons with ⟨_, hsuf⟩
    refine List.nodup_append.2 ⟨hpre, List.nodup_cons.2 ⟨fun h => hnot (by simp [h]), hsuf⟩, fun a ha b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hbs
    · intro hEq; subst hEq; exact hnot (by simp [ha])
    · exact hdisj a ha b (.tail _ hbs)

theorem nodup_move_to_pre {α : Type} [BEq α] [LawfulBEq α] {pre suf : List α} {x y : α}
    (hnd : (pre ++ suf).Nodup) (hx : x ∈ suf) (hy : y = x ∨ y ∉ pre ++ suf) : ((pre ++ [y]) ++ suf.erase x).Nodup := by
  rcases List.nodup_append.1 hnd with ⟨hpre, hsuf, hdisj⟩
  have hyNotPre : y ∉ pre := fun hp => hy.elim (fun h => hdisj _ (h ▸ hp) _ hx rfl) (fun hn => hn (by simp [hp]))
  have hyNotSufE : y ∉ suf.erase x := fun hs => hy.elim (fun h => not_mem_erase_of_nodup hsuf (h ▸ hs)) (fun hn => hn (by simp [List.mem_of_mem_erase hs]))
  refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨hpre, List.pairwise_singleton _ _, fun a ha b hb => by
    simp only [List.mem_singleton] at hb; subst hb; intro hEq; subst hEq; exact hyNotPre ha⟩,
    hsuf.erase x, fun a ha b hb => ?_⟩
  rcases List.mem_append.1 ha with hap | ha1
  · exact hdisj a hap b (List.mem_of_mem_erase hb)
  · simp only [List.mem_singleton] at ha1; subst ha1; intro hEq; subst hEq; exact hyNotSufE hb

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
    (childNs : String) (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") :
    ∀ (steps : List (KeyedStep msg)) (targets targetsDone oldRem : List (Html msg))
      (pre suf : List Dom.Node) (Sdone Srem : Nat → Prop) (a : DomArena msg),
      steps.length = targets.length → positional pre.length steps = true → PosStepsMatch pre.length steps targets oldRem →
      Html.DomCleanList targets = true → htmlListDepth targets ≤ f → pre.length + suf.length + steps.length < UInt32.size →
      a.nextId + htmlListNodeCount targets < UInt32.size → parent.toNat < a.nextId → 0 < a.nextId →
      a.get parent = .element pns ptag pst pmg (pre ++ suf) → (pre ++ suf).Nodup →
      (∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId) → CleanDomChildren f childNs targetsDone a Sdone pre →
      (∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) → (∀ k, Sdone k → Srem k → False) →
      (∀ r ∈ suf, r.toNat < a.nextId ∧ r ≠ parent) → PosSufClean f childNs steps oldRem a Srem suf →
      let aOut := ((applyPositionalStepsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) steps).run a).2
      ∃ targetsOut sufRem Snew, targetsOut.length = steps.length ∧ (targetsOut ++ sufRem).length ≤ suf.length + steps.length ∧
        a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount targets ∧
        aOut.get parent = .element pns ptag pst pmg ((pre ++ targetsOut) ++ sufRem) ∧
        (∀ m : Dom.Node, m ≠ parent → ¬Sdone m.toNat → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
        (∀ k, Snew k → (Sdone k ∨ Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧
        CleanDomChildren f childNs (targetsDone ++ targets) aOut Snew (pre ++ targetsOut)
  | [], targets, _, _, pre, suf, Sdone, _, a, hlen, _, _, _, _, _, _, _, _, hpar, _, hSdone, hDoneC, _, _, _, _ => by
      cases targets with
      | cons _ _ => simp at hlen
      | nil =>
          dsimp only [applyPositionalStepsM, StateT.run, pure, StateT.pure]
          exact ⟨[], suf, Sdone, rfl, by simp, Nat.le_refl _, by simp [htmlListNodeCount], by simpa using hpar, fun _ _ _ _ _ => rfl, fun k hk => ⟨.inl hk, (hSdone k hk).1⟩, by simpa using hDoneC⟩
  | step :: sRest, targets, targetsDone, oldRem, pre, suf, Sdone, Srem, a,
      hlen, hpos, hmatch, hclean, hdep, hsz, hbound, hparLt, hposId, hpar, hnd, hSdone, hDoneC, hSrem, hDisj, hsufB, hsufC => by
      cases targets with
      | nil => simp at hlen
      | cons t tRest =>
          simp only [List.length_cons] at hlen hsz
          have hlen' : sRest.length = tRest.length := Nat.succ.inj hlen
          simp only [Html.DomCleanList, Bool.and_eq_true] at hclean
          simp only [htmlListDepth] at hdep; simp only [htmlListNodeCount] at hbound ⊢
          have htDep : htmlDepth t ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
          have hrestDep : htmlListDepth tRest ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
          have huJNext : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) := uint32_ofNat_succ pre.length (by omega)
          have hStep0 := hmatch 0 (by simp)
          simp only [List.getElem_cons_zero] at hStep0
          cases step with
          | reuse oldIdx p =>
              simp only [PosSufClean] at hsufC
              simp only [positional, Bool.and_eq_true, beq_iff_eq] at hpos
              rcases hStep0.2 oldIdx p rfl with ⟨hIdxEq, cOld, hcOld0, hpEq⟩; subst hpEq
              cases oldRem with
              | nil => simp at hcOld0
              | cons cO oldRest =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at hcOld0; subst hcOld0
                  cases suf with
                  | nil => exact False.elim hsufC
                  | cons child sufRest =>
                      simp only [List.length_cons] at hsz
                      rcases hsufC with ⟨Sc, Srest, hSc, hSr, hDSr, hcClean, hSufClean⟩
                      have hchildAt := positional_step_reuse_tail parent pns ptag pst pmg pre child sufRest a (by omega)
                      have hPatchC := hPatch childNs parent pns ptag pst pmg cO t child pre sufRest Sc a
                        hchildNs (by omega) (by omega) htDep hparLt hposId hpar hnd
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
                      let Sc' : Nat → Prop := fun k => Sc k ∨ (a.nextId ≤ k ∧ k < aMid.nextId)
                      let Sdone' : Nat → Prop := fun k => Sdone k ∨ Sc' k
                      have hDoneMid : CleanDomChildren f childNs targetsDone aMid Sdone pre :=
                        CleanDomChildren_frame (fun m hm =>
                          hframeMid m (node_ne_of_toNat_ne (hSdone _ hm).1) (fun hsc => hDisj _ hm (hSc _ hsc)) (hSdone _ hm).2) hDoneC
                      have hDone' := CleanDomChildren_append (fun k hk1 hk2 =>
                        hk2.elim (fun hsc => hDisj k hk1 (hSc k hsc)) (fun hlo => by have := (hSdone k hk1).2; omega))
                        hDoneMid (show CleanDomChildren f childNs [t] aMid Sc' [newChild] from
                          ⟨Sc', fun _ => False, fun _ h => h, fun _ h => h.elim, fun _ _ h => h.elim, hcNew, trivial⟩)
                      have hSdone' : ∀ k, Sdone' k → k ≠ parent.toNat ∧ k < aMid.nextId := fun k hk => hk.elim
                        (fun h1 => have hb := hSdone k h1; ⟨hb.1, by omega⟩)
                        (fun h2 => h2.elim (fun h => have hb := hSrem k (hSc k h); ⟨hb.1, by omega⟩) (fun h3 => ⟨by omega, h3.2⟩))
                      have hMatchRest : PosStepsMatch (pre ++ [newChild]).length sRest tRest oldRest := by
                        intro k hk; have hm' := hmatch (k + 1) (by simpa using hk)
                        simp only [List.getElem?_cons_succ, List.getElem_cons_succ, List.length_append, List.length_singleton] at hm' ⊢
                        exact ⟨hm'.1, fun idx' p' hs => let hr := hm'.2 idx' p' hs; ⟨by omega, hr.2⟩⟩
                      have hSufCleanMid : PosSufClean f childNs sRest oldRest aMid Srest sufRest := by
                        cases sRest with
                        | nil => trivial
                        | cons stp _ => cases stp with
                          | create _ => trivial
                          | reuse _ _ => exact CleanDomChildren_frame (fun m hm =>
                              hframeMid m (node_ne_of_toNat_ne (hSrem _ (hSr _ hm)).1) (fun hsc => hDSr _ hsc hm) (hSrem _ (hSr _ hm)).2) hSufClean
                      have hih := applyPositionalStepsM_clean_step f hPatch parent pns ptag pst pmg childNs hchildNs
                        sRest tRest (targetsDone ++ [t]) oldRest (pre ++ [newChild]) sufRest Sdone' Srest aMid
                        hlen' (by simpa [List.length_append, hpos.1] using hpos.2) hMatchRest hclean.2 hrestDep
                        (by simp only [List.length_append, List.length_singleton]; omega) (by omega) (by omega) (by omega)
                        (by simpa [List.append_assoc] using hparMid) (by simpa [List.append_assoc] using hndMid)
                        hSdone' hDone' (fun k hk => have hb := hSrem k (hSr k hk); ⟨hb.1, by omega⟩)
                        (fun k hk1 hk2 => hk1.elim (fun h1 => hDisj k h1 (hSr k hk2))
                          (fun h2 => h2.elim (fun h => hDSr k h hk2) (fun _ => by have := (hSrem k (hSr k hk2)).2; omega)))
                        (fun r hr => have hb := hsufB r (.tail _ hr); ⟨by omega, hb.2⟩) hSufCleanMid
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
                      refine ⟨newChild :: targetsRest, sufRem, Snew, by simpa using hlenR,
                        by simp only [List.cons_append, List.length_cons] at htotLenR ⊢; omega,
                        by omega, by omega, by simpa [List.append_assoc] using hparR, fun m hmPar hmD hmR hmLt => ?_,
                        fun k hk => ?_, by simpa [List.append_assoc] using hDoneR⟩
                      · have hnmD' : ¬Sdone' m.toNat := fun h => h.elim hmD (fun h2 => h2.elim (fun hsc => hmR (hSc _ hsc)) (fun _ => by omega))
                        rw [hfrR m hmPar hnmD' (fun hr => hmR (hSr _ hr)) (by omega), hframeMid m hmPar (fun hsc => hmR (hSc _ hsc)) hmLt]
                      · rcases hSnew k hk with ⟨hS | hSr' | hA, hnp⟩
                        · exact ⟨hS.elim .inl (fun h2 => h2.elim (fun hsc => .inr (.inl (hSc _ hsc))) (fun hhi => .inr (.inr ⟨hhi.1, by omega⟩))), hnp⟩
                        · exact ⟨.inr (.inl (hSr _ hSr')), hnp⟩
                        · exact ⟨.inr (.inr ⟨by omega, hA.2⟩), hnp⟩
          | create newH =>
              simp only [positional] at hpos
              have htEq : newH = t := hStep0.1 newH rfl
              rcases clean_create_step f parent pns ptag pst pmg childNs hchildNs t targetsDone pre suf Sdone a
                hclean.1 htDep (by omega) (by omega) hparLt hposId hpar hnd hSdone hDoneC hsufB with
                ⟨cn, aMid, aIns, hchildNsRun, hbuildEq, hinsRun, haInsGe, haInsLe, haInsMid, hparIns, hnd', hfrIns, hDone'⟩
              have hMatchRest : PosStepsMatch (pre ++ [cn]).length sRest tRest [] := by
                intro k hk; have hm := hmatch (k + 1) (by simpa using hk)
                simp only [List.getElem?_cons_succ, List.getElem_cons_succ, List.length_append, List.length_singleton] at hm ⊢
                refine ⟨hm.1, fun idx' p' hs => False.elim (no_reuse_of_allCreates_top sRest k idx' p' hpos hs)⟩
              have hposRest : positional (pre ++ [cn]).length sRest = true := by
                cases sRest with | nil => rfl | cons s0 _ => cases s0 with | reuse _ _ => simp [allCreates] at hpos | create _ => simpa [positional] using hpos
              have hsufCleanIns : PosSufClean f childNs sRest [] aIns Srem suf := by
                cases sRest with | nil => trivial | cons s0 _ => cases s0 with | create _ => trivial | reuse _ _ => simp [allCreates] at hpos
              have hih := applyPositionalStepsM_clean_step f hPatch parent pns ptag pst pmg childNs hchildNs
                sRest tRest (targetsDone ++ [t]) [] (pre ++ [cn]) suf (fun k => Sdone k ∨ (a.nextId ≤ k ∧ k < aIns.nextId)) Srem aIns
                hlen' hposRest hMatchRest hclean.2 hrestDep (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
                (by omega) (by omega) (by omega) hparIns hnd'
                (fun k hk => hk.elim (fun h => have hb := hSdone k h; ⟨hb.1, by omega⟩) (fun h => ⟨by omega, h.2⟩)) hDone'
                (fun k hk => have hb := hSrem k hk; ⟨hb.1, by omega⟩)
                (fun k hk1 hk2 => hk1.elim (fun h => hDisj k h hk2) (fun hhi => by have := (hSrem k hk2).2; omega))
                (fun r hr => have hb := hsufB r hr; ⟨by omega, hb.2⟩) hsufCleanIns
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
              refine ⟨cn :: targetsRest, sufRem, Snew, by simpa using hlenR,
                by simp only [List.cons_append, List.length_cons] at htotLenR ⊢; omega,
                by omega, by omega, by simpa [List.append_assoc] using hparR, fun m hmPar hmD hmR hmLt => ?_,
                fun k hk => ?_, by simpa [List.append_assoc] using hDoneR⟩
              · rw [hfrR m hmPar (fun h => h.elim hmD (fun _ => by omega)) hmR (by omega), hfrIns m hmPar hmLt]
              · rcases hSnew k hk with ⟨hS | hR | hA, hnp⟩
                · exact ⟨hS.elim .inl (fun h2 => .inr (.inr ⟨h2.1, by omega⟩)), hnp⟩
                · exact ⟨.inr (.inl hR), hnp⟩
                · exact ⟨.inr (.inr ⟨by omega, hA.2⟩), hnp⟩

theorem childNamespace_eq_childNsOf {ns ptag : String} (hns : ns = "" ∨ ns = Dom.svgNs) :
    (if (if ns == "" && ptag == "svg" then Dom.svgNs else ns) == Dom.svgNs && ptag != "foreignObject"
      then Dom.svgNs else "") = Dom.childNsOf ns ptag := by
  rcases hns with rfl | rfl <;> by_cases hfo : ptag = "foreignObject"
  · subst hfo; simp [Dom.childNsOf]
  · by_cases hsvg : ptag = "svg" <;> simp [Dom.childNsOf, Dom.svgNs, hfo, hsvg]
  · subst hfo; simp [Dom.childNsOf, Dom.svgNs]
  · simp [Dom.childNsOf, Dom.svgNs, hfo]

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

theorem nodup_getElem_inj {α : Type} :
    ∀ {xs : List α} {i₁ i₂ : Nat} (h₁ : i₁ < xs.length) (h₂ : i₂ < xs.length), xs.Nodup → xs[i₁] = xs[i₂] → i₁ = i₂
  | [], _, _, h₁, _, _, _ => nomatch h₁
  | x :: xs, 0, 0, _, _, _, _ => rfl
  | x :: xs, 0, i₂ + 1, _, h₂, hnd, hEq => by
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hEq
      exact absurd (hEq.symm ▸ List.getElem_mem (by simpa using h₂)) (List.nodup_cons.1 hnd).1
  | x :: xs, i₁ + 1, 0, h₁, _, hnd, hEq => by
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hEq
      exact absurd (hEq ▸ List.getElem_mem (by simpa using h₁)) (List.nodup_cons.1 hnd).1
  | x :: xs, i₁ + 1, i₂ + 1, h₁, h₂, hnd, hEq =>
      congrArg Nat.succ (nodup_getElem_inj (by simpa using h₁) (by simpa using h₂) (List.nodup_cons.1 hnd).2 hEq)

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
    (c₁ : List (Html msg)) (live : Array Dom.Node) (Si : Nat → Nat → Prop) (baseLimit : Nat) (hliveLen : live.size = c₁.length)
    (hSiB : ∀ i k, Si i k → k ≠ parent.toNat ∧ k < baseLimit) (hSiDisj : ∀ i₁ i₂, i₁ ≠ i₂ → ∀ k, Si i₁ k → Si i₂ k → False)
    (hliveInj : ∀ i₁ i₂, i₁ < c₁.length → i₂ < c₁.length → live.getD i₁ 0 = live.getD i₂ 0 → i₁ = i₂) :
    ∀ (steps : List (KeyedStep msg)) (targets targetsDone : List (Html msg)) (usedIdxs : List Nat)
      (pre suf : List Dom.Node) (Sdone : Nat → Prop) (a : DomArena msg),
      steps.length = targets.length → KeyedCleanMatch c₁ usedIdxs steps targets →
      Html.DomCleanList targets = true → htmlListDepth targets ≤ f → pre.length + suf.length + steps.length < UInt32.size →
      baseLimit ≤ a.nextId → a.nextId + htmlListNodeCount targets < UInt32.size → parent.toNat < a.nextId → 0 < a.nextId →
      a.get parent = .element pns ptag pst pmg (pre ++ suf) → (pre ++ suf).Nodup →
      (∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId) → CleanDomChildren f childNs targetsDone a Sdone pre →
      (∀ (i : Nat) (hi : i < c₁.length), i ∉ usedIdxs → live.getD i 0 ∈ suf ∧ CleanDomSubtree f childNs c₁[i] a (Si i) (live.getD i 0)) →
      (∀ i, i ∉ usedIdxs → ∀ k, Si i k → Sdone k → False) → (∀ r ∈ suf, r.toNat < a.nextId ∧ r ≠ parent) →
      let (finalJ, aOut) := (applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat pre.length) steps).run a
      ∃ targetsOut sufRem Snew, finalJ.toNat = pre.length + steps.length ∧ targetsOut.length = steps.length ∧
        (targetsOut ++ sufRem).length ≤ suf.length + steps.length ∧
        a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount targets ∧
        aOut.get parent = .element pns ptag pst pmg ((pre ++ targetsOut) ++ sufRem) ∧
        (∀ m : Dom.Node, m ≠ parent → ¬Sdone m.toNat → (∀ i, ¬Si i m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
        (∀ k, Snew k → (Sdone k ∨ (∃ i, Si i k) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧
        CleanDomChildren f childNs (targetsDone ++ targets) aOut Snew (pre ++ targetsOut)
  | [], targets, _, _, pre, suf, Sdone, a, hlen, _, _, _, hsz, _, _, _, _, hpar, _, hSdone, hDoneC, _, _, _ => by
      cases targets with
      | cons _ _ => simp at hlen
      | nil =>
          dsimp only [applyKeyedStepsM, StateT.run, pure, StateT.pure]
          exact ⟨[], suf, Sdone, uint32_toNat_ofNat_lt pre.length (by simp at hsz; omega), rfl, by simp, Nat.le_refl _,
            by simp [htmlListNodeCount], by simpa using hpar, fun _ _ _ _ _ => rfl, fun k hk => ⟨.inl hk, (hSdone k hk).1⟩, by simpa using hDoneC⟩
  | step :: sRest, targets, targetsDone, usedIdxs, pre, suf, Sdone, a,
      hlen, hkm, hclean, hdep, hsz, hbase, hbound, hparLt, hposId, hpar, hnd, hSdone, hDoneC, hLive, hDisj, hsufB => by
      cases targets with
      | nil => simp at hlen
      | cons t tRest =>
          simp only [List.length_cons] at hlen hsz
          have hlen' : sRest.length = tRest.length := Nat.succ.inj hlen
          simp only [Html.DomCleanList, Bool.and_eq_true] at hclean
          simp only [htmlListDepth] at hdep; simp only [htmlListNodeCount] at hbound ⊢
          have htDep : htmlDepth t ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
          have hrestDep : htmlListDepth tRest ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
          have huJNext : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) := uint32_ofNat_succ pre.length (by omega)
          have hStep0 := hkm.1 0 (by simp)
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
                           uint32_toNat_ofNat_lt pre.length (by omega), w3cInsertBefore_step pre suf child hnd hChildNotPre, a1]
              have hnd1 : (pre ++ child :: suf.erase child).Nodup := by
                simpa [child, List.append_assoc] using nodup_move_to_pre hnd hChildSuf (.inl rfl)
              have hChildClean1 : CleanDomSubtree f childNs c₁[oldIdx] a1 (Si oldIdx) child :=
                CleanDomSubtree_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSiB oldIdx m.toNat hm).1)) hChildClean
              have hParNodes1 : ∀ r ∈ pre ++ child :: suf.erase child, r.toNat < a1.nextId := fun r hr => by
                rw [ha1Next]; rcases List.mem_append.1 hr with hp | hc
                · exact (hSdone _ (CleanDomChildren_mem hDoneC r hp)).2
                · rcases List.mem_cons.1 hc with rfl | hs; exact (hsufB child hChildSuf).1; exact (hsufB r (List.mem_of_mem_erase hs)).1
              have hPatchC := hPatch childNs parent pns ptag pst pmg c₁[oldIdx] t child pre (suf.erase child) (Si oldIdx) a1
                hchildNs (by have := List.length_erase_le (l := suf) (a := child); omega) (by rw [ha1Next]; omega) htDep (by rw [ha1Next]; omega)
                (by rw [ha1Next]; omega) (DomArena.get_set_self _ _ _) hnd1 (fun h => (hSiB oldIdx parent.toNat h).1 rfl)
                (fun k hk => by rw [ha1Next]; exact Nat.lt_of_lt_of_le (hSiB oldIdx k hk).2 hbase) hParNodes1 hChildClean1 hclean.1
              dsimp only [StateT.run] at hPatchC
              rcases hPatchC with ⟨haMidLe, haMidBound, hframeMid, newChild, _, hparMid, hndMid, _, hcNew⟩
              let aMid := (applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff c₁[oldIdx] t) a1).2
              have haMidLe' : a1.nextId ≤ aMid.nextId := haMidLe
              have haMidBound' : aMid.nextId ≤ a1.nextId + htmlNodeCount t := haMidBound
              have hApEq : (applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) child (diff c₁[oldIdx] t) a1).2 = aMid := rfl
              let Sc' : Nat → Prop := fun k => Si oldIdx k ∨ (a1.nextId ≤ k ∧ k < aMid.nextId)
              let Sdone' : Nat → Prop := fun k => Sdone k ∨ Sc' k
              have hDoneMid : CleanDomChildren f childNs targetsDone aMid Sdone pre :=
                CleanDomChildren_frame (fun m hm =>
                  (hframeMid m (node_ne_of_toNat_ne (hSdone _ hm).1) (fun h => hDisj _ hOldNotUsed _ h hm) (by rw [ha1Next]; exact (hSdone _ hm).2)).trans
                    (DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSdone _ hm).1))) hDoneC
              have hDone' := CleanDomChildren_append (fun k hk1 hk2 =>
                hk2.elim (fun hsi => hDisj oldIdx hOldNotUsed k hsi hk1) (fun hlo => by have := (hSdone k hk1).2; omega))
                hDoneMid (show CleanDomChildren f childNs [t] aMid Sc' [newChild] from
                  ⟨Sc', fun _ => False, fun _ h => h, fun _ h => h.elim, fun _ _ h => h.elim, hcNew, trivial⟩)
              have hLive' : ∀ (i : Nat) (hi : i < c₁.length), i ∉ oldIdx :: usedIdxs →
                  live.getD i 0 ∈ suf.erase child ∧ CleanDomSubtree f childNs c₁[i] aMid (Si i) (live.getD i 0) := by
                intro i hi hnotUsed
                have hneIdx : i ≠ oldIdx := fun h => hnotUsed (h ▸ .head _)
                rcases hLive i hi (fun h => hnotUsed (.tail _ h)) with ⟨hInSuf, hCleanI⟩
                refine ⟨(List.mem_erase_of_ne (fun hEq => hneIdx (hliveInj i oldIdx hi hOldLt hEq))).2 hInSuf,
                  CleanDomSubtree_frame (fun m hm => ?_) hCleanI⟩
                have hSi := hSiB i m.toNat hm
                exact (hframeMid m (node_ne_of_toNat_ne hSi.1) (fun ho => hSiDisj i oldIdx hneIdx m.toNat hm ho) (by rw [ha1Next]; omega)).trans
                  (DomArena.get_set_ne _ _ (node_ne_of_toNat_ne hSi.1))
              have hMatchRest : KeyedCleanMatch c₁ (oldIdx :: usedIdxs) sRest tRest := by
                refine ⟨fun i hi => ⟨(hkm.1 (i + 1) (by simpa using hi)).1, fun j' p' hs => ?_⟩, fun i₁ i₂ j₁ j₂ p₁ p₂ hi₁ hi₂ h1 h2 hj => ?_⟩
                · have hm := (hkm.1 (i + 1) (by simpa using hi)).2 j' p' (by simpa using hs)
                  have hne : j' ≠ oldIdx := fun hEq => by
                    have := hkm.2 0 (i + 1) oldIdx j' (diff c₁[oldIdx] t) p' (by simp) (by simp; omega) (by simp) (by simpa using hs) hEq.symm; omega
                  exact ⟨fun hu => by rcases List.mem_cons.1 hu with h0 | ht; exact hne h0; exact hm.1 ht, hm.2⟩
                · have := hkm.2 (i₁ + 1) (i₂ + 1) j₁ j₂ p₁ p₂ (by simp; omega) (by simp; omega) (by simpa using h1) (by simpa using h2) hj; omega
              have hSufCleanLen : (pre ++ [newChild]).length + (suf.erase child).length + sRest.length < UInt32.size := by
                have := List.length_erase_le (l := suf) (a := child); simp only [List.length_append, List.length_singleton]; omega
              have hih := applyKeyedStepsM_reconcile_spec f hPatch parent pns ptag pst pmg childNs hchildNs c₁ live Si baseLimit
                hliveLen hSiB hSiDisj hliveInj sRest tRest (targetsDone ++ [t]) (oldIdx :: usedIdxs) (pre ++ [newChild]) (suf.erase child) Sdone' aMid
                hlen' hMatchRest hclean.2 hrestDep hSufCleanLen (by omega) (by omega) (by omega) (by omega)
                (by simpa [List.append_assoc] using hparMid) (by simpa [List.append_assoc] using hndMid)
                (fun k hk => hk.elim (fun h => have hb := hSdone k h; ⟨hb.1, by omega⟩)
                  (fun h => h.elim (fun h2 => have hb := hSiB _ k h2; ⟨hb.1, by omega⟩) (fun h3 => ⟨by omega, h3.2⟩)))
                hDone' hLive'
                (fun i hi k hsi hk => by
                  have hneIdx : i ≠ oldIdx := fun h => hi (h ▸ .head _)
                  rcases hk with h1 | (h2 | h3)
                  · exact hDisj i (fun h => hi (.tail _ h)) k hsi h1
                  · exact hSiDisj i oldIdx hneIdx k hsi h2
                  · have := (hSiB i k hsi).2; omega)
                (fun r hr => have hr0 := hsufB r (List.mem_of_mem_erase hr); ⟨by omega, hr0.2⟩)
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
              refine ⟨newChild :: targetsRest, sufRem, Snew, by simp only [List.length_append, List.length_cons, List.length_nil] at hfj ⊢; omega,
                by simpa using hlenR,
                by have := List.length_erase_le (l := suf) (a := child); simp only [List.cons_append, List.length_cons] at htotLenR ⊢; omega,
                by omega, by omega, by simpa [List.append_assoc] using hparR, fun m hmPar hmD hmAll hmLt => ?_, fun k hk => ?_,
                by simpa [List.append_assoc] using hDoneR⟩
              · have hnmD' : ¬Sdone' m.toNat := fun h => h.elim hmD (fun h2 => h2.elim (hmAll oldIdx) (fun _ => by omega))
                rw [hfrR m hmPar hnmD' hmAll (by omega), hframeMid m hmPar (hmAll oldIdx) (by omega), DomArena.get_set_ne _ _ hmPar]
              · rcases hSnew k hk with ⟨hS | hEx | hA, hnp⟩
                · exact ⟨hS.elim .inl (fun h2 => h2.elim (fun hsi => .inr (.inl ⟨oldIdx, hsi⟩)) (fun hhi => .inr (.inr ⟨by omega, by omega⟩))), hnp⟩
                · exact ⟨.inr (.inl hEx), hnp⟩
                · exact ⟨.inr (.inr ⟨by omega, hA.2⟩), hnp⟩
          | create newH =>
              have htEq : newH = t := hStep0.1 newH rfl
              rcases clean_create_step f parent pns ptag pst pmg childNs hchildNs t targetsDone pre suf Sdone a
                hclean.1 htDep (by omega) (by omega) hparLt hposId hpar hnd hSdone hDoneC hsufB with
                ⟨cn, aMid, aIns, hchildNsRun, hbuildEq, hinsRun, haInsGe, haInsLe, haInsMid, hparIns, hnd', hfrIns, hDone'⟩
              have hLiveIns : ∀ (i : Nat) (hi : i < c₁.length), i ∉ usedIdxs →
                  live.getD i 0 ∈ suf ∧ CleanDomSubtree f childNs c₁[i] aIns (Si i) (live.getD i 0) := by
                intro i hi hnu; rcases hLive i hi hnu with ⟨hs, hcl⟩
                refine ⟨hs, CleanDomSubtree_frame (fun m hm => hfrIns m (node_ne_of_toNat_ne (hSiB i m.toNat hm).1) (by have := (hSiB i m.toNat hm).2; omega)) hcl⟩
              have hMatchRest : KeyedCleanMatch c₁ usedIdxs sRest tRest := by
                refine ⟨fun i hi => by simpa [List.getElem?_cons_succ, List.getElem_cons_succ] using hkm.1 (i + 1) (by simpa using hi),
                  fun i₁ i₂ j₁ j₂ p₁ p₂ hi₁ hi₂ h1 h2 hj => by
                    have := hkm.2 (i₁ + 1) (i₂ + 1) j₁ j₂ p₁ p₂ (by simp; omega) (by simp; omega) (by simpa using h1) (by simpa using h2) hj; omega⟩
              have hih := applyKeyedStepsM_reconcile_spec f hPatch parent pns ptag pst pmg childNs hchildNs c₁ live Si baseLimit
                hliveLen hSiB hSiDisj hliveInj sRest tRest (targetsDone ++ [t]) usedIdxs (pre ++ [cn]) suf
                (fun k => Sdone k ∨ (a.nextId ≤ k ∧ k < aIns.nextId)) aIns
                hlen' hMatchRest hclean.2 hrestDep (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
                (by omega) (by omega) (by omega) (by omega) hparIns hnd'
                (fun k hk => hk.elim (fun h => have hb := hSdone k h; ⟨hb.1, by omega⟩) (fun h => ⟨by omega, h.2⟩)) hDone' hLiveIns
                (fun i hnu k hsi hk => hk.elim (fun h => hDisj i hnu k hsi h) (fun hhi => by have := (hSiB i k hsi).2; omega))
                (fun r hr => have hb := hsufB r hr; ⟨by omega, hb.2⟩)
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
              refine ⟨cn :: targetsRest, sufRem, Snew, by simp only [List.length_append, List.length_cons, List.length_nil] at hfj ⊢; omega,
                by simpa using hlenR,
                by simp only [List.cons_append, List.length_cons] at htotLenR ⊢; omega,
                by omega, by omega, by simpa [List.append_assoc] using hparR, fun m hmPar hmD hmAll hmLt => ?_, fun k hk => ?_,
                by simpa [List.append_assoc] using hDoneR⟩
              · rw [hfrR m hmPar (fun h => h.elim hmD (fun _ => by omega)) hmAll (by omega), hfrIns m hmPar hmLt]
              · rcases hSnew k hk with ⟨hS | hEx | hA, hnp⟩
                · exact ⟨hS.elim .inl (fun h2 => .inr (.inr ⟨h2.1, by omega⟩)), hnp⟩
                · exact ⟨.inr (.inl hEx), hnp⟩
                · exact ⟨.inr (.inr ⟨by omega, hA.2⟩), hnp⟩

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
