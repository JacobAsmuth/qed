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
      dsimp only [snapshotChildrenM, StateT.run, bind] at hchildAt ih ⊢
      rw [stateM_bind_step hchildAt, ih (i + 1) (acc.push cs[i]) (by omega)]
      simp only [Array.toList_push, List.append_assoc, List.singleton_append, hdrop]

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

theorem nodup_snoc_append {α : Type} {pre suf : List α} {cn : α}
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


theorem childNamespace_eq_childNsOf {ns ptag : String} (hns : ns = "" ∨ ns = Dom.svgNs) :
    (if (if ns == "" && ptag == "svg" then Dom.svgNs else ns) == Dom.svgNs && ptag != "foreignObject"
      then Dom.svgNs else "") = Dom.childNsOf ns ptag := by
  rcases hns with rfl | rfl <;> by_cases hfo : ptag = "foreignObject"
  · subst hfo; simp [Dom.childNsOf]
  · by_cases hsvg : ptag = "svg" <;> simp [Dom.childNsOf, Dom.svgNs, hfo, hsvg]
  · subst hfo; simp [Dom.childNsOf, Dom.svgNs]
  · simp [Dom.childNsOf, Dom.svgNs, hfo]


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

theorem clean_done_extend {msg : Type} {f : Nat} {childNs : String}
    {parent newChild : Dom.Node} {t : Html msg} {targetsDone : List (Html msg)} {pre : List Dom.Node}
    {Sdone Sc : Nat → Prop} {a aMid : DomArena msg}
    (haMidLe : a.nextId ≤ aMid.nextId) (hparLt : parent.toNat < a.nextId)
    (hSdone : ∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId)
    (hScB : ∀ k, Sc k → k ≠ parent.toNat ∧ k < a.nextId) (hDisj : ∀ k, Sdone k → ¬Sc k)
    (hFrame : ∀ m : Dom.Node, Sdone m.toNat → aMid.get m = a.get m)
    (hDoneC : CleanDomChildren f childNs targetsDone a Sdone pre)
    (hcNew : CleanDomSubtree f childNs t aMid (fun k => Sc k ∨ (a.nextId ≤ k ∧ k < aMid.nextId)) newChild) :
    let Sdone' := fun k => Sdone k ∨ (Sc k ∨ (a.nextId ≤ k ∧ k < aMid.nextId))
    (∀ k, Sdone' k → k ≠ parent.toNat ∧ k < aMid.nextId) ∧
    CleanDomChildren f childNs (targetsDone ++ [t]) aMid Sdone' (pre ++ [newChild]) :=
  ⟨fun k hk => hk.elim (fun h1 => let hb := hSdone k h1; ⟨hb.1, Nat.lt_of_lt_of_le hb.2 haMidLe⟩)
    (fun h2 => h2.elim (fun h => let hb := hScB k h; ⟨hb.1, Nat.lt_of_lt_of_le hb.2 haMidLe⟩)
      (fun h3 => ⟨fun hEq => Nat.not_lt.2 h3.1 (hEq ▸ hparLt), h3.2⟩)),
   CleanDomChildren_append (fun k hk1 hk2 => hk2.elim (hDisj k hk1) (fun hlo => Nat.not_lt.2 hlo.1 (hSdone k hk1).2))
    (CleanDomChildren_frame hFrame hDoneC) ⟨_, fun _ => False, fun _ h => h, fun _ h => h.elim, fun _ _ h => h.elim, hcNew, trivial⟩⟩

theorem clean_done_alloc_bounds {msg : Type} {parent : Dom.Node} {Sdone : Nat → Prop} {a aMid : DomArena msg}
    (haMidLe : a.nextId ≤ aMid.nextId) (hparLt : parent.toNat < a.nextId)
    (hSdone : ∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId) :
    ∀ k, (Sdone k ∨ (a.nextId ≤ k ∧ k < aMid.nextId)) → k ≠ parent.toNat ∧ k < aMid.nextId :=
  fun k hk => hk.elim (fun h => let hb := hSdone k h; ⟨hb.1, Nat.lt_of_lt_of_le hb.2 haMidLe⟩)
    (fun h => ⟨fun hEq => Nat.not_lt.2 h.1 (hEq ▸ hparLt), h.2⟩)

theorem clean_step_Snew_compose {Sdone Sc Srest Srem Snew : Nat → Prop} {n₀ n₁ n₂ p : Nat}
    (h01 : n₀ ≤ n₁) (h12 : n₁ ≤ n₂) (hSc : ∀ k, Sc k → Srem k) (hSr : ∀ k, Srest k → Srem k)
    (hSnew : ∀ k, Snew k → ((Sdone k ∨ (Sc k ∨ (n₀ ≤ k ∧ k < n₁))) ∨ Srest k ∨ (n₁ ≤ k ∧ k < n₂)) ∧ k ≠ p) :
    ∀ k, Snew k → (Sdone k ∨ Srem k ∨ (n₀ ≤ k ∧ k < n₂)) ∧ k ≠ p := fun k hk => by
  rcases hSnew k hk with ⟨hS | hSr' | hA, hnp⟩
  · exact ⟨hS.elim .inl (fun h2 => h2.elim (fun hsc => .inr (.inl (hSc k hsc))) (fun hhi => .inr (.inr ⟨hhi.1, Nat.lt_of_lt_of_le hhi.2 h12⟩))), hnp⟩
  · exact ⟨.inr (.inl (hSr k hSr')), hnp⟩
  · exact ⟨.inr (.inr ⟨Nat.le_trans h01 hA.1, hA.2⟩), hnp⟩

theorem clean_create_Snew_compose {Sdone Srem Snew : Nat → Prop} {n₀ n₁ n₂ p : Nat}
    (h01 : n₀ ≤ n₁) (h12 : n₁ ≤ n₂)
    (hSnew : ∀ k, Snew k → ((Sdone k ∨ (n₀ ≤ k ∧ k < n₁)) ∨ Srem k ∨ (n₁ ≤ k ∧ k < n₂)) ∧ k ≠ p) :
    ∀ k, Snew k → (Sdone k ∨ Srem k ∨ (n₀ ≤ k ∧ k < n₂)) ∧ k ≠ p :=
  clean_step_Snew_compose (Sc := fun _ => False) h01 h12 (fun _ h => h.elim) (fun _ h => h)
    fun j hj => let ⟨h, hnp⟩ := hSnew j hj; ⟨h.elim (fun hs => .inl (hs.elim .inl (fun ha => .inr (.inr ha)))) .inr, hnp⟩

theorem not_Sdone_extend {Sdone Sc : Nat → Prop} {n₀ n₁ k : Nat}
    (hD : ¬Sdone k) (hSc : ¬Sc k) (hLt : k < n₀) : ¬(Sdone k ∨ (Sc k ∨ (n₀ ≤ k ∧ k < n₁))) :=
  fun h => h.elim hD (fun h2 => h2.elim hSc (fun hlo => Nat.not_lt.2 hlo.1 hLt))

end Qed
