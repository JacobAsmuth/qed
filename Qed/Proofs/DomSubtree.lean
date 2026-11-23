import Qed.Proofs.DomArena

namespace Qed
variable {msg : Type}
private abbrev ArenaM (msg : Type) := StateM (DomArena msg)

/-! ## Pure Diff & W3C `insertBefore` Keyed/Positional Reconciler Equivalence -/

theorem insertBeforeRef_split {child ref : Dom.Node} :
    ∀ (pre suf : List Dom.Node), ref ∉ pre → insertBeforeRef child ref (pre ++ ref :: suf) = pre ++ child :: ref :: suf
  | [], _, _ => by simp [insertBeforeRef]
  | x :: xs, suf, href => by simp [insertBeforeRef, beq_eq_false_iff_ne.2 (show x ≠ ref from fun h => href (by simp [h])), insertBeforeRef_split xs suf fun h => href (.tail _ h)]

section
variable {α : Type}
theorem erase_append_right_of_not_mem [BEq α] [LawfulBEq α] :
    ∀ (pre suf : List α) {x : α}, x ∉ pre → (pre ++ suf).erase x = pre ++ suf.erase x
  | [], _, _, _ => rfl
  | a :: pre, suf, x, hnot => by simp [beq_eq_false_iff_ne.2 (show a ≠ x from fun h => hnot (by simp [h])), erase_append_right_of_not_mem pre suf fun h => hnot (.tail _ h)]
private theorem nodup_insert_middle {pre suf : List α} {c : α} (hnd : (pre ++ suf).Nodup) (hpre : c ∉ pre) (hsuf : c ∉ suf) : (pre ++ c :: suf).Nodup :=
  have ⟨hp, hs, hd⟩ := List.nodup_append.1 hnd
  List.nodup_append.2 ⟨hp, List.nodup_cons.2 ⟨hsuf, hs⟩, fun a ha b hb => (List.mem_cons.1 hb).elim (fun h e => hpre (h ▸ e ▸ ha)) (hd a ha b)⟩
private theorem nodup_erase_suf [BEq α] [LawfulBEq α] {pre suf : List α} {x : α} (hnd : (pre ++ suf).Nodup) : (pre ++ suf.erase x).Nodup :=
  have ⟨hp, hs, hd⟩ := List.nodup_append.1 hnd; List.nodup_append.2 ⟨hp, hs.erase x, fun a ha b hb => hd a ha b (List.mem_of_mem_erase hb)⟩
theorem listReplaceAt_append_middle : ∀ (pre : List α) (x y : α) (suf : List α), listReplaceAt (pre ++ x :: suf) pre.length y = pre ++ y :: suf
  | [], _, _, _ => rfl | _ :: pre, x, y, suf => by simp [listReplaceAt, listReplaceAt_append_middle pre x y suf]
theorem nodup_snoc_append {pre suf : List α} {cn : α} (hnd : (pre ++ suf).Nodup) (hnot : cn ∉ pre ++ suf) : ((pre ++ [cn]) ++ suf).Nodup := by
  rw [List.append_assoc, List.singleton_append]; exact nodup_insert_middle hnd (fun h => hnot (by simp [h])) (fun h => hnot (by simp [h]))
theorem nodup_append_replace {pre suf : List α} {x y : α} (hnd : (pre ++ x :: suf).Nodup) (hy : y = x ∨ y ∉ pre ++ x :: suf) : (pre ++ y :: suf).Nodup :=
  hy.elim (· ▸ hnd) fun hnot => have ⟨hpre, hcons, hdisj⟩ := List.nodup_append.1 hnd
    nodup_insert_middle (List.nodup_append.2 ⟨hpre, (List.nodup_cons.1 hcons).2, fun a ha b hb => hdisj a ha b (.tail _ hb)⟩)
      (fun h => hnot (by simp [h])) (fun h => hnot (by simp [h]))
theorem nodup_move_to_pre [BEq α] [LawfulBEq α] {pre suf : List α} {x y : α} (hnd : (pre ++ suf).Nodup) (hx : x ∈ suf) (hy : y = x ∨ y ∉ pre ++ suf) : ((pre ++ [y]) ++ suf.erase x).Nodup := by
  rw [List.append_assoc, List.singleton_append]; have ⟨_, hsuf, hdisj⟩ := List.nodup_append.1 hnd
  exact nodup_insert_middle (nodup_erase_suf hnd)
    (fun hp => hy.elim (fun h => hdisj _ (h ▸ hp) _ hx rfl) fun hn => hn (by simp [hp]))
    (fun hs => hy.elim (fun h => hsuf.not_mem_erase (h ▸ hs)) fun hn => hn (by simp [List.mem_of_mem_erase hs]))
theorem nodup_getElem_inj {xs : List α} {i₁ i₂ : Nat} (h₁ : i₁ < xs.length) (h₂ : i₂ < xs.length) (hnd : xs.Nodup) (hEq : xs[i₁] = xs[i₂]) : i₁ = i₂ := by
  rcases Nat.lt_trichotomy i₁ i₂ with hlt | rfl | hgt
  · exact absurd hEq ((List.pairwise_iff_getElem.1 hnd) i₁ i₂ h₁ h₂ hlt)
  · rfl
  · exact absurd hEq.symm ((List.pairwise_iff_getElem.1 hnd) i₂ i₁ h₂ h₁ hgt)
end

theorem w3cInsertBefore_step (pre suf : List Dom.Node) (child : Dom.Node) (hnd : (pre ++ suf).Nodup) (hnotPre : child ∉ pre) :
    w3cInsertBefore (pre ++ suf) pre.length child = pre ++ child :: suf.erase child := by
  unfold w3cInsertBefore; rw [List.drop_left]
  cases suf with
  | nil => simp [List.erase_of_not_mem hnotPre]
  | cons ref rest => by_cases hrc : ref == child; · cases eq_of_beq hrc; simp
                     · simp only [hrc, Bool.false_eq_true, ↓reduceIte, erase_append_right_of_not_mem pre (ref :: rest) hnotPre, List.erase_cons]
                       exact insertBeforeRef_split pre (rest.erase child) fun h => (List.nodup_append.1 hnd).2.2 _ h _ (.head _) rfl

theorem w3cInsertBefore_fresh_append (pre suf : List Dom.Node) (cn : Dom.Node) (hnot : cn ∉ pre ++ suf) (hdisj : ∀ r ∈ suf, r ∉ pre) :
    w3cInsertBefore (pre ++ suf) pre.length cn = pre ++ cn :: suf := by
  unfold w3cInsertBefore; rw [List.drop_left, List.erase_of_not_mem hnot]
  cases suf with
  | nil => simp
  | cons ref rest => simp only [beq_eq_false_iff_ne.2 (show ref ≠ cn from fun h => hnot (by simp [h])), Bool.false_eq_true, ↓reduceIte]
                     exact insertBeforeRef_split pre rest (hdisj ref (.head _))

def w3cPlaceSeq : List Dom.Node → Nat → List Dom.Node → List Dom.Node
  | cs, _, [] => cs | cs, j, target :: rest => w3cPlaceSeq (w3cInsertBefore cs j target) (j + 1) rest

theorem w3cPlaceSeq_invariant (targets : List Dom.Node) :
    ∀ (pre suf : List Dom.Node), (pre ++ suf).Nodup → targets.Nodup → (∀ t ∈ targets, t ∉ pre) → ∃ rem, w3cPlaceSeq (pre ++ suf) pre.length targets = pre ++ targets ++ rem := by
  induction targets with
  | nil => exact fun pre suf _ _ _ => ⟨suf, by simp [w3cPlaceSeq]⟩
  | cons t rest ih =>
      intro pre suf hnd htnd hdisj; rcases List.nodup_cons.1 htnd with ⟨htRest, hrestNd⟩; have htNotPre := hdisj t (.head _)
      rcases ih (pre ++ [t]) (suf.erase t) (by simpa [List.append_assoc] using nodup_insert_middle (nodup_erase_suf hnd) htNotPre (List.nodup_append.1 hnd).2.1.not_mem_erase)
        hrestNd (fun r hr hm => (List.mem_append.1 hm).elim (hdisj r (.tail _ hr)) fun h2 => htRest (List.mem_singleton.1 h2 ▸ hr)) with ⟨rem, heq⟩
      refine ⟨rem, ?_⟩; simp only [w3cPlaceSeq, w3cInsertBefore_step pre suf t hnd htNotPre]
      rw [show pre ++ t :: suf.erase t = (pre ++ [t]) ++ suf.erase t by simp, show pre.length + 1 = (pre ++ [t]).length by simp, heq]; simp [List.append_assoc]

theorem w3cReconcileKeyed_eq (live targets : List Dom.Node) (hlive : live.Nodup) (htargets : targets.Nodup) :
    let placed := w3cPlaceSeq live 0 targets; removeTailSpec targets.length (placed.length - targets.length) placed = targets := by
  rcases w3cPlaceSeq_invariant targets [] live (by simpa using hlive) htargets (fun _ _ h => nomatch h) with ⟨rem, hplaced⟩
  dsimp only; simp only [List.nil_append, List.length_nil] at hplaced
  rw [hplaced, show (targets ++ rem).length - targets.length = rem.length by simp]; exact removeTailSpec_append targets rem

/-! ## Child Reconciliation & Full Subtree Patching on `DomArena` -/

theorem snapshotChildrenM_spec (a : DomArena msg) (node : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (cs : List Dom.Node) (hsize : cs.length < UInt32.size) :
    ∀ (i rem : Nat) (acc : Array Dom.Node), i + rem = cs.length →
      (snapshotChildrenM (m := ArenaM msg) node i acc rem).run (a.set node (.element pns ptag pst pmg cs)) = (⟨acc.toList ++ cs.drop i⟩, a.set node (.element pns ptag pst pmg cs))
  | i, 0, ⟨_⟩, hsum => by cases (show i = cs.length by omega); simp [snapshotChildrenM, StateT.run, pure, StateT.pure]
  | i, r + 1, acc, hsum => by
      have hlt : i < cs.length := by omega
      have hca : (MonadDom.childAt (m := ArenaM msg) node (UInt32.ofNat i)).run (a.set node (.element pns ptag pst pmg cs)) = (cs[i], a.set node (.element pns ptag pst pmg cs)) := by
        simp [MonadDom.childAt, StateT.run, DomArena.get_set_self, uint32_toNat_ofNat_lt i (by omega), List.getElem?_eq_getElem hlt]
      have hih := snapshotChildrenM_spec a node pns ptag pst pmg cs hsize (i + 1) r (acc.push cs[i]) (by omega)
      dsimp only [snapshotChildrenM, StateT.run, bind] at hca hih ⊢; rw [stateM_bind_step hca, hih]
      simp only [Array.toList_push, List.append_assoc, List.singleton_append, List.drop_eq_getElem_cons hlt]

theorem list_length_le_htmlListNodeCount : ∀ (cs : List (Html msg)), cs.length ≤ htmlListNodeCount cs
  | [] => Nat.le_refl 0
  | c :: cs => by have : 1 ≤ htmlNodeCount c := by cases c <;> simp [htmlNodeCount]
                  have := list_length_le_htmlListNodeCount cs; simp only [List.length_cons, htmlListNodeCount]; omega

theorem nodup_lt_length_le : ∀ (n : Nat) (xs : List Nat), xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, hlt => absurd (hlt x (.head _)) (Nat.not_lt_zero _)
  | n + 1, xs, hnd, hlt => by
      have hih := nodup_lt_length_le n (xs.erase n) (hnd.erase n) fun y hy => by
        have := hlt y (List.mem_of_mem_erase hy); have : y ≠ n := fun e => hnd.not_mem_erase (e ▸ hy); omega
      by_cases hm : n ∈ xs; · rw [List.length_erase_of_mem hm] at hih; omega
      · rw [List.erase_of_not_mem hm] at hih; omega

theorem nodup_nodes_lt_length_le (n : Nat) (xs : List Dom.Node) (hnd : xs.Nodup) (hlt : ∀ x ∈ xs, x.toNat < n) : xs.length ≤ n := by
  simpa using nodup_lt_length_le n (xs.map UInt32.toNat) (hnd.map UInt32.toNat fun _ _ h h' => h (uint32_eq_of_toNat_eq h'))
    (fun k hk => by rcases List.mem_map.1 hk with ⟨y, hy, rfl⟩; exact hlt y hy)

theorem childNamespace_eq_childNsOf {ns ptag : String} (hns : ns = "" ∨ ns = Dom.svgNs) :
    (if (if ns == "" && ptag == "svg" then Dom.svgNs else ns) == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") = Dom.childNsOf ns ptag := by
  rcases hns with rfl | rfl <;> by_cases hfo : ptag = "foreignObject" <;> try (subst hfo; simp [Dom.childNsOf, Dom.svgNs])
  · by_cases hsvg : ptag = "svg" <;> simp [Dom.childNsOf, Dom.svgNs, hfo, hsvg]
  · simp [Dom.childNsOf, Dom.svgNs, hfo]

theorem clean_done_alloc_bounds {parent : Dom.Node} {Sdone : Nat → Prop} {a aMid : DomArena msg}
    (haMidLe : a.nextId ≤ aMid.nextId) (hparLt : parent.toNat < a.nextId) (hSdone : ∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId) :
    ∀ k, (Sdone k ∨ (a.nextId ≤ k ∧ k < aMid.nextId)) → k ≠ parent.toNat ∧ k < aMid.nextId :=
  fun k hk => hk.elim (fun h => let hb := hSdone k h; ⟨hb.1, Nat.lt_of_lt_of_le hb.2 haMidLe⟩) (fun h => ⟨fun e => Nat.not_lt.2 h.1 (e ▸ hparLt), h.2⟩)

theorem clean_done_extend {f : Nat} {childNs : String} {parent newChild : Dom.Node} {t : Html msg} {targetsDone : List (Html msg)}
    {pre : List Dom.Node} {Sdone Sc : Nat → Prop} {a aMid : DomArena msg} (haMidLe : a.nextId ≤ aMid.nextId) (hparLt : parent.toNat < a.nextId)
    (hSdone : ∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId) (hScB : ∀ k, Sc k → k ≠ parent.toNat ∧ k < a.nextId)
    (hDisj : ∀ k, Sdone k → ¬Sc k) (hFrame : ∀ m : Dom.Node, Sdone m.toNat → aMid.get m = a.get m) (hDoneC : CleanDomChildren f childNs targetsDone a Sdone pre)
    (hcNew : CleanDomSubtree f childNs t aMid (fun k => Sc k ∨ (a.nextId ≤ k ∧ k < aMid.nextId)) newChild) :
    let Sdone' := fun k => Sdone k ∨ (Sc k ∨ (a.nextId ≤ k ∧ k < aMid.nextId))
    (∀ k, Sdone' k → k ≠ parent.toNat ∧ k < aMid.nextId) ∧ CleanDomChildren f childNs (targetsDone ++ [t]) aMid Sdone' (pre ++ [newChild]) :=
  ⟨fun k hk => hk.elim (fun h1 => let hb := hSdone k h1; ⟨hb.1, Nat.lt_of_lt_of_le hb.2 haMidLe⟩) (clean_done_alloc_bounds haMidLe hparLt hScB k),
   CleanDomChildren_append (fun k hk1 hk2 => hk2.elim (hDisj k hk1) fun hlo => Nat.not_lt.2 hlo.1 (hSdone k hk1).2)
    (CleanDomChildren_frame hFrame hDoneC) (DisjointDomList.singleton hcNew)⟩

theorem clean_step_Snew_compose {Sdone Sc Srest Srem Snew : Nat → Prop} {n₀ n₁ n₂ p : Nat}
    (h01 : n₀ ≤ n₁) (h12 : n₁ ≤ n₂) (hSc : ∀ k, Sc k → Srem k) (hSr : ∀ k, Srest k → Srem k)
    (hSnew : ∀ k, Snew k → ((Sdone k ∨ (Sc k ∨ (n₀ ≤ k ∧ k < n₁))) ∨ Srest k ∨ (n₁ ≤ k ∧ k < n₂)) ∧ k ≠ p) :
    ∀ k, Snew k → (Sdone k ∨ Srem k ∨ (n₀ ≤ k ∧ k < n₂)) ∧ k ≠ p := fun k hk => by
  rcases hSnew k hk with ⟨hS | hSr' | hA, hnp⟩
  · exact ⟨hS.elim .inl fun h2 => h2.elim (fun hsc => .inr (.inl (hSc k hsc))) fun hhi => .inr (.inr ⟨hhi.1, Nat.lt_of_lt_of_le hhi.2 h12⟩), hnp⟩
  · exact ⟨.inr (.inl (hSr k hSr')), hnp⟩
  · exact ⟨.inr (.inr ⟨Nat.le_trans h01 hA.1, hA.2⟩), hnp⟩

theorem not_Sdone_extend {Sdone Sc : Nat → Prop} {n₀ n₁ k : Nat} (hD : ¬Sdone k) (hSc : ¬Sc k) (hLt : k < n₀) :
    ¬(Sdone k ∨ (Sc k ∨ (n₀ ≤ k ∧ k < n₁))) := fun h => h.elim hD fun h2 => h2.elim hSc fun hlo => Nat.not_lt.2 hlo.1 hLt

end Qed
