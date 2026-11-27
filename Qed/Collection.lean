import Qed.Html

namespace Qed

@[simp] theorem _root_.Array.forall_push {α : Type} {P : α → Prop} {xs : Array α} {v : α} : (∀ x ∈ xs.push v, P x) ↔ (∀ x ∈ xs, P x) ∧ P v :=
  ⟨fun h => ⟨fun x hx => h x (Array.mem_push.2 (.inl hx)), h v (Array.mem_push.2 (.inr rfl))⟩, fun ⟨hxs, hv⟩ x hx => (Array.mem_push.1 hx).elim (hxs x) (· ▸ hv)⟩
theorem _root_.Array.forall_set {α : Type u} {P : α → Prop} {xs : Array α} {i : Nat} {v : α} (h : i < xs.size) (hxs : ∀ x ∈ xs, P x) (hv : P v) : ∀ x ∈ xs.set i v h, P x := fun x hx =>
  (List.mem_or_eq_of_mem_set (Array.toList_set (xs := xs) (i := i) (x := v) (h := h) ▸ Array.mem_def.1 hx)).elim (fun hm => hxs x (Array.mem_def.2 hm)) (· ▸ hv)
theorem _root_.Array.forall_elem {α : Type u} {P : α → Prop} {xs : Array α} {i : Nat} (h : i < xs.size) (hxs : ∀ x ∈ xs, P x) : P xs[i] := hxs xs[i] (Array.getElem_mem h)

section SublistMem
variable {α : Type u}
private theorem toList_filter_sublist (xs : Array α) (p : α → Bool) : (xs.filter p).toList.Sublist xs.toList := Array.toList_filter ▸ List.filter_sublist
private theorem toList_pop_sublist (xs : Array α) : xs.pop.toList.Sublist xs.toList := Array.toList_pop ▸ List.dropLast_sublist _
private theorem toList_eraseIdx_sublist (xs : Array α) (i : Nat) (hi : i < xs.size) : (xs.eraseIdx i hi).toList.Sublist xs.toList := Array.toList_eraseIdx ▸ List.eraseIdx_sublist _ _
private theorem toList_extract_sublist (xs : Array α) (s e : Nat) : (xs.extract s e).toList.Sublist xs.toList := Array.toList_extract ▸ (List.take_sublist _ _).trans (List.drop_sublist _ _)
private theorem mem_of_sublist {xs ys : Array α} (hsub : ys.toList.Sublist xs.toList) {x : α} (h : x ∈ ys) : x ∈ xs := Array.mem_def.2 (hsub.subset (Array.mem_def.1 h))
@[grind →] theorem array_mem_of_mem_pop {xs : Array α} {x : α} (h : x ∈ xs.pop) : x ∈ xs := mem_of_sublist (toList_pop_sublist xs) h
@[grind →] theorem array_mem_of_mem_eraseIdx {xs : Array α} {i : Nat} {hi : i < xs.size} {x : α} (h : x ∈ xs.eraseIdx i hi) : x ∈ xs := Array.mem_of_mem_eraseIdx h
@[grind →] theorem array_mem_of_mem_extract {xs : Array α} {start stop : Nat} {x : α} (h : x ∈ xs.extract start stop) : x ∈ xs := mem_of_sublist (toList_extract_sublist xs start stop) h
@[grind →] theorem array_mem_of_mem_swap {xs : Array α} {i j : Nat} {hi : i < xs.size} {hj : j < xs.size} {x : α} (h : x ∈ xs.swap i j hi hj) : x ∈ xs :=
  Array.forall_set (by simp [hj]) (Array.forall_set hi (fun _ => id) (Array.getElem_mem hj)) (Array.getElem_mem hi) x h
end SublistMem

section GenericSum
variable {β : Type} [Add β] [Zero β] [Std.Associative (α := β) (· + ·)]
private def arraySumBy {α : Type} (xs : Array α) (f : α → β) : β := xs.foldl (fun acc x => acc + f x) 0
private theorem list_sum_perm [Std.Commutative (α := β) (· + ·)] {a b : List β} (h : a.Perm b) : a.sum = b.sum := by
  induction h with | nil => rfl | cons _ _ ih => simp only [List.sum_cons, ih] | swap _ _ _ => simp only [List.sum_cons]; ac_rfl | trans _ _ ih1 ih2 => exact ih1.trans ih2
private theorem list_sum_map_set [Std.Commutative (α := β) (· + ·)] {α : Type} (f : α → β) : ∀ (l : List α) (i : Nat) (x : α) (h : i < l.length), ((l.set i x).map f).sum + f l[i] = (l.map f).sum + f x
  | [], _, _, h => nomatch h | _ :: _, 0, _, _ => by simp only [List.set_cons_zero, List.map_cons, List.sum_cons, List.getElem_cons_zero]; ac_rfl
  | _ :: ys, i + 1, x, h => by simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ, Std.Associative.assoc, list_sum_map_set f ys i x (by simpa using h)]
private theorem list_sum_map_eraseIdx [Std.Commutative (α := β) (· + ·)] {α : Type} (f : α → β) : ∀ (l : List α) (i : Nat) (h : i < l.length), ((l.eraseIdx i).map f).sum + f l[i] = (l.map f).sum
  | [], _, h => nomatch h | _ :: _, 0, _ => by simp only [List.eraseIdx_zero, List.tail_cons, List.map_cons, List.sum_cons, List.getElem_cons_zero]; exact Std.Commutative.comm (op := (· + ·)) _ _
  | _ :: ys, i + 1, h => by simp only [List.eraseIdx_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ, Std.Associative.assoc, list_sum_map_eraseIdx f ys i (by simpa using h)]

section IdSum
variable [Std.LawfulIdentity (α := β) (· + ·) 0]
private theorem list_sum_append : ∀ (a b : List β), (a ++ b).sum = a.sum + b.sum
  | [], _ => (Std.LawfulLeftIdentity.left_id _).symm
  | x :: xs, ys => by simp only [List.cons_append, List.sum_cons, list_sum_append xs ys, Std.Associative.assoc]
private theorem foldl_add_eq_sum {α : Type} (f : α → β) : ∀ (l : List α) (init : β), l.foldl (fun acc x => acc + f x) init = init + (l.map f).sum
  | [], _ => (Std.LawfulRightIdentity.right_id _).symm
  | _ :: xs, _ => by simp only [List.foldl_cons, List.map_cons, List.sum_cons, foldl_add_eq_sum f xs, Std.Associative.assoc]
private theorem foldl_sum_eq {α : Type} (xs : Array α) (f : α → β) : arraySumBy xs f = (xs.toList.map f).sum := by
  rw [arraySumBy, ← Array.foldl_toList, foldl_add_eq_sum]; exact Std.LawfulLeftIdentity.left_id _
private theorem arraySumBy_append {α : Type} (xs ys : Array α) (f : α → β) : arraySumBy (xs ++ ys) f = arraySumBy xs f + arraySumBy ys f := by
  rw [foldl_sum_eq, foldl_sum_eq, foldl_sum_eq, Array.toList_append, List.map_append, list_sum_append]
private theorem arraySumBy_push {α : Type} (xs : Array α) (f : α → β) (v : α) : arraySumBy (xs.push v) f = arraySumBy xs f + f v := by
  rw [foldl_sum_eq, foldl_sum_eq, Array.toList_push, List.map_append, List.map_cons, List.map_nil, list_sum_append, List.sum_cons, List.sum_nil]
  simp only [Std.LawfulRightIdentity.right_id]
private theorem arraySumBy_map {α γ : Type} (xs : Array α) (g : α → γ) (f : γ → β) : arraySumBy (xs.map g) f = arraySumBy xs (fun x => f (g x)) := by
  rw [foldl_sum_eq, foldl_sum_eq, Array.toList_map, List.map_map]; rfl

section CommSum
variable [Std.Commutative (α := β) (· + ·)]
private theorem arraySumBy_of_perm {α : Type} {xs ys : Array α} (h : ys.toList.Perm xs.toList) (f : α → β) : arraySumBy ys f = arraySumBy xs f := by
  rw [foldl_sum_eq, foldl_sum_eq]; exact list_sum_perm (h.map f)
private theorem arraySumBy_reverse {α : Type} (xs : Array α) (f : α → β) : arraySumBy xs.reverse f = arraySumBy xs f := arraySumBy_of_perm (Array.toList_reverse ▸ List.reverse_perm _) f
private theorem arraySumBy_mergeSort {α : Type} (xs : Array α) (le : α → α → Bool) (f : α → β) : arraySumBy (xs.mergeSort le) f = arraySumBy xs f :=
  arraySumBy_of_perm (Array.perm_iff_toList_perm.1 (Array.mergeSort_perm (xs := xs) (le := le))) f
private theorem arraySumBy_set {α : Type} (xs : Array α) (f : α → β) (i : Nat) (v : α) (h : i < xs.size) : arraySumBy (xs.set i v h) f + f xs[i] = arraySumBy xs f + f v := by
  rw [foldl_sum_eq, foldl_sum_eq, Array.toList_set]; exact list_sum_map_set f xs.toList i v h
private theorem arraySumBy_eraseIdx {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) (f : α → β) : arraySumBy (xs.eraseIdx i h) f + f xs[i] = arraySumBy xs f := by
  rw [foldl_sum_eq, foldl_sum_eq, Array.toList_eraseIdx]; exact list_sum_map_eraseIdx f xs.toList i h
end CommSum
end IdSum
end GenericSum

private theorem list_sum_nat_sublist {a b : List Nat} (h : a.Sublist b) : a.sum ≤ b.sum := by induction h <;> simp <;> omega
private theorem list_sum_nat_le_length_mul {α : Type} (f : α → Nat) (bound : Nat) : ∀ {l : List α}, (∀ x ∈ l, f x ≤ bound) → (l.map f).sum ≤ l.length * bound
  | [], _ => by simp
  | x :: xs, h => by have := h x (by simp); have := list_sum_nat_le_length_mul f bound (l := xs) fun y hy => h y (by simp [hy]); simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]; omega

def _root_.Array.sumBy {α : Type} (xs : Array α) (f : α → Nat) : Nat := arraySumBy xs f
def _root_.Array.sumByInt {α : Type} (xs : Array α) (f : α → Int) : Int := arraySumBy xs f
private theorem sumBy_of_sublist {α : Type} {xs ys : Array α} (f : α → Nat) (hsub : ys.toList.Sublist xs.toList) : ys.sumBy f ≤ xs.sumBy f := by
  rw [Array.sumBy, Array.sumBy, foldl_sum_eq, foldl_sum_eq]; exact list_sum_nat_sublist (hsub.map f)

section SumCount
variable {α β : Type}
@[simp, grind =] theorem _root_.Array.sumBy_empty (f : α → Nat) : (#[] : Array α).sumBy f = 0 := rfl
@[simp, grind =] theorem _root_.Array.sumBy_push (xs : Array α) (f : α → Nat) (v : α) : (xs.push v).sumBy f = xs.sumBy f + f v := arraySumBy_push xs f v
@[simp, grind =] theorem _root_.Array.sumBy_append (xs ys : Array α) (f : α → Nat) : (xs ++ ys).sumBy f = xs.sumBy f + ys.sumBy f := arraySumBy_append xs ys f
@[simp, grind =] theorem _root_.Array.sumBy_map (xs : Array α) (g : α → β) (f : β → Nat) : (xs.map g).sumBy f = xs.sumBy (fun x => f (g x)) := arraySumBy_map xs g f
@[simp, grind =] theorem _root_.Array.sumBy_reverse (xs : Array α) (f : α → Nat) : xs.reverse.sumBy f = xs.sumBy f := arraySumBy_reverse xs f
@[simp, grind =] theorem _root_.Array.sumBy_mergeSort (xs : Array α) (le : α → α → Bool) (f : α → Nat) : (xs.mergeSort le).sumBy f = xs.sumBy f := arraySumBy_mergeSort xs le f
@[grind =] theorem _root_.Array.sumBy_set (xs : Array α) (f : α → Nat) (i : Nat) (v : α) (h : i < xs.size) : (xs.set i v h).sumBy f + f xs[i] = xs.sumBy f + f v := arraySumBy_set xs f i v h
@[grind =] theorem _root_.Array.sumBy_eraseIdx (xs : Array α) (i : Nat) (h : i < xs.size) (f : α → Nat) : (xs.eraseIdx i h).sumBy f + f xs[i] = xs.sumBy f := arraySumBy_eraseIdx xs i h f
@[grind <=] theorem _root_.Array.sumBy_filter_le (xs : Array α) (p : α → Bool) (f : α → Nat) : (xs.filter p).sumBy f ≤ xs.sumBy f := sumBy_of_sublist f (toList_filter_sublist xs p)
@[grind <=] theorem _root_.Array.sumBy_pop_le (xs : Array α) (f : α → Nat) : xs.pop.sumBy f ≤ xs.sumBy f := sumBy_of_sublist f (toList_pop_sublist xs)
@[grind <=] theorem _root_.Array.sumBy_extract_le (xs : Array α) (start stop : Nat) (f : α → Nat) : (xs.extract start stop).sumBy f ≤ xs.sumBy f := sumBy_of_sublist f (toList_extract_sublist xs start stop)
theorem _root_.Array.sumBy_le_size_mul {xs : Array α} (f : α → Nat) (bound : Nat) (h : ∀ x ∈ xs, f x ≤ bound) : xs.sumBy f ≤ xs.size * bound := by
  rw [Array.sumBy, foldl_sum_eq, ← Array.length_toList]; exact list_sum_nat_le_length_mul f bound fun y hy => h y (Array.mem_toList_iff.1 hy)

@[simp, grind =] theorem _root_.Array.sumByInt_empty (f : α → Int) : (#[] : Array α).sumByInt f = 0 := rfl
@[simp, grind =] theorem _root_.Array.sumByInt_push (xs : Array α) (x : α) (f : α → Int) : (xs.push x).sumByInt f = xs.sumByInt f + f x := arraySumBy_push xs f x
@[simp, grind =] theorem _root_.Array.sumByInt_append (xs ys : Array α) (f : α → Int) : (xs ++ ys).sumByInt f = xs.sumByInt f + ys.sumByInt f := arraySumBy_append xs ys f
@[simp, grind =] theorem _root_.Array.sumByInt_map (xs : Array α) (g : α → β) (f : β → Int) : (xs.map g).sumByInt f = xs.sumByInt (fun x => f (g x)) := arraySumBy_map xs g f
@[simp, grind =] theorem _root_.Array.sumByInt_reverse (xs : Array α) (f : α → Int) : xs.reverse.sumByInt f = xs.sumByInt f := arraySumBy_reverse xs f
@[simp, grind =] theorem _root_.Array.sumByInt_mergeSort (xs : Array α) (le : α → α → Bool) (f : α → Int) : (xs.mergeSort le).sumByInt f = xs.sumByInt f := arraySumBy_mergeSort xs le f
@[grind =] theorem _root_.Array.sumByInt_set (xs : Array α) (i : Nat) (x : α) (h : i < xs.size) (f : α → Int) : (xs.set i x h).sumByInt f + f xs[i] = xs.sumByInt f + f x := arraySumBy_set xs f i x h
@[grind =] theorem _root_.Array.sumByInt_eraseIdx (xs : Array α) (i : Nat) (h : i < xs.size) (f : α → Int) : (xs.eraseIdx i h).sumByInt f + f xs[i] = xs.sumByInt f := arraySumBy_eraseIdx xs i h f

def _root_.Array.countWhere (xs : Array α) (p : α → Bool) : Nat := xs.sumBy fun x => if p x then 1 else 0
@[simp, grind =] theorem _root_.Array.countWhere_empty (p : α → Bool) : (#[] : Array α).countWhere p = 0 := rfl
@[simp, grind =] theorem _root_.Array.countWhere_push (xs : Array α) (x : α) (p : α → Bool) : (xs.push x).countWhere p = xs.countWhere p + (if p x then 1 else 0) := Array.sumBy_push xs _ x
@[simp, grind =] theorem _root_.Array.countWhere_append (xs ys : Array α) (p : α → Bool) : (xs ++ ys).countWhere p = xs.countWhere p + ys.countWhere p := Array.sumBy_append xs ys _
@[simp, grind =] theorem _root_.Array.countWhere_reverse (xs : Array α) (p : α → Bool) : xs.reverse.countWhere p = xs.countWhere p := Array.sumBy_reverse xs _
@[simp, grind =] theorem _root_.Array.countWhere_mergeSort (xs : Array α) (le : α → α → Bool) (p : α → Bool) : (xs.mergeSort le).countWhere p = xs.countWhere p := Array.sumBy_mergeSort xs le _
@[grind <=] theorem _root_.Array.countWhere_le_size (xs : Array α) (p : α → Bool) : xs.countWhere p ≤ xs.size :=
  Nat.mul_one xs.size ▸ Array.sumBy_le_size_mul (xs := xs) (fun x => if p x then 1 else 0) 1 fun x _ => by cases p x <;> decide
@[grind <=] theorem _root_.Array.countWhere_filter_le (xs : Array α) (q p : α → Bool) : (xs.filter q).countWhere p ≤ xs.countWhere p := Array.sumBy_filter_le xs q _
@[grind <=] theorem _root_.Array.countWhere_pop_le (xs : Array α) (p : α → Bool) : xs.pop.countWhere p ≤ xs.countWhere p := Array.sumBy_pop_le xs _
@[grind =] theorem _root_.Array.countWhere_set (xs : Array α) (i : Nat) (x : α) (h : i < xs.size) (p : α → Bool) : (xs.set i x h).countWhere p + (if p xs[i] then 1 else 0) = xs.countWhere p + (if p x then 1 else 0) := Array.sumBy_set xs _ i x h
@[grind =] theorem _root_.Array.countWhere_eraseIdx (xs : Array α) (i : Nat) (h : i < xs.size) (p : α → Bool) : (xs.eraseIdx i h).countWhere p + (if p xs[i] then 1 else 0) = xs.countWhere p := Array.sumBy_eraseIdx xs i h _
end SumCount

section UniqueSorted
variable {α β : Type}
def _root_.Array.uniqueBy (xs : Array α) (key : α → β) : Prop := (xs.toList.map key).Nodup
instance [DecidableEq β] (xs : Array α) (key : α → β) : Decidable (xs.uniqueBy key) := inferInstanceAs (Decidable (xs.toList.map key).Nodup)
private theorem uniqueBy_of_perm {xs ys : Array α} {key : α → β} (hp : xs.toList.Perm ys.toList) (h : xs.uniqueBy key) : ys.uniqueBy key := ((hp.map key).nodup_iff).1 h
@[simp, grind .] theorem _root_.Array.uniqueBy_empty (key : α → β) : (#[] : Array α).uniqueBy key := List.nodup_nil
@[simp, grind =] theorem _root_.Array.uniqueBy_push_iff (xs : Array α) (x : α) (key : α → β) :
    (xs.push x).uniqueBy key ↔ xs.uniqueBy key ∧ ∀ y ∈ xs, key y ≠ key x := by
  simp only [Array.uniqueBy, Array.toList_push, List.map_append, List.map_cons, List.map_nil, List.nodup_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, true_and, List.mem_cons, List.mem_map, Array.mem_toList_iff]
  exact ⟨fun ⟨h, d⟩ => ⟨h, fun y hy e => d _ ⟨y, hy, rfl⟩ _ (.inl rfl) e⟩, fun ⟨h, n⟩ => ⟨h, fun _ ⟨y, hy, he⟩ _ hk e => hk.elim (fun h' => n y hy ((he.trans e).trans h')) False.elim⟩⟩
@[grind ←] theorem _root_.Array.uniqueBy_filter {xs : Array α} {key : α → β} {p : α → Bool} (h : xs.uniqueBy key) : (xs.filter p).uniqueBy key := h.sublist ((toList_filter_sublist xs p).map _)
@[grind ←] theorem _root_.Array.uniqueBy_pop {xs : Array α} {key : α → β} (h : xs.uniqueBy key) : xs.pop.uniqueBy key := h.sublist ((toList_pop_sublist xs).map _)
@[grind ←] theorem _root_.Array.uniqueBy_eraseIdx {xs : Array α} {key : α → β} {i : Nat} {hi : i < xs.size} (h : xs.uniqueBy key) : (xs.eraseIdx i hi).uniqueBy key := h.sublist ((toList_eraseIdx_sublist xs i hi).map _)
@[grind ←] theorem _root_.Array.uniqueBy_extract {xs : Array α} {key : α → β} {start stop : Nat} (h : xs.uniqueBy key) : (xs.extract start stop).uniqueBy key := h.sublist ((toList_extract_sublist xs start stop).map _)
@[grind ←] theorem _root_.Array.uniqueBy_reverse {xs : Array α} {key : α → β} (h : xs.uniqueBy key) : xs.reverse.uniqueBy key := uniqueBy_of_perm (Array.toList_reverse ▸ List.reverse_perm _).symm h
@[grind ←] theorem _root_.Array.uniqueBy_mergeSort {xs : Array α} {key : α → β} {le : α → α → Bool} (h : xs.uniqueBy key) : (xs.mergeSort le).uniqueBy key :=
  uniqueBy_of_perm (Array.perm_iff_toList_perm.1 (Array.mergeSort_perm (xs := xs) (le := le))).symm h
@[grind ←] theorem _root_.Array.uniqueBy_map_same_key {xs : Array α} {key : α → β} {g : α → α} (hKey : ∀ y ∈ xs, key (g y) = key y) (h : xs.uniqueBy key) : (xs.map g).uniqueBy key := by
  simp only [Array.uniqueBy, Array.toList_map, List.map_map, Function.comp_def]; rwa [List.map_congr_left fun y hy => hKey y (Array.mem_toList_iff.1 hy)]

def _root_.Array.isSortedBy (xs : Array α) (key : α → Nat) : Prop := xs.toList.Pairwise (fun a b => key a ≤ key b)
instance (xs : Array α) (key : α → Nat) : Decidable (xs.isSortedBy key) := inferInstanceAs (Decidable (xs.toList.Pairwise (fun a b => key a ≤ key b)))
@[simp, grind .] theorem _root_.Array.isSortedBy_empty (key : α → Nat) : (#[] : Array α).isSortedBy key := List.Pairwise.nil
@[simp, grind .] theorem _root_.Array.isSortedBy_singleton (x : α) (key : α → Nat) : #[x].isSortedBy key := List.pairwise_singleton _ _
@[simp, grind =] theorem _root_.Array.isSortedBy_push_iff (xs : Array α) (x : α) (key : α → Nat) : (xs.push x).isSortedBy key ↔ xs.isSortedBy key ∧ ∀ y ∈ xs, key y ≤ key x := by
  simp only [Array.isSortedBy, Array.toList_push, List.pairwise_append, List.pairwise_singleton, List.mem_singleton, forall_eq, true_and, Array.mem_toList_iff]
@[grind ←] theorem _root_.Array.isSortedBy_filter {xs : Array α} {key : α → Nat} {p : α → Bool} (h : xs.isSortedBy key) : (xs.filter p).isSortedBy key := h.sublist (toList_filter_sublist xs p)
@[grind ←] theorem _root_.Array.isSortedBy_pop {xs : Array α} {key : α → Nat} (h : xs.isSortedBy key) : xs.pop.isSortedBy key := h.sublist (toList_pop_sublist xs)
@[grind ←] theorem _root_.Array.isSortedBy_eraseIdx {xs : Array α} {key : α → Nat} {i : Nat} {hi : i < xs.size} (h : xs.isSortedBy key) : (xs.eraseIdx i hi).isSortedBy key := h.sublist (toList_eraseIdx_sublist xs i hi)
@[grind ←] theorem _root_.Array.isSortedBy_extract {xs : Array α} {key : α → Nat} {start stop : Nat} (h : xs.isSortedBy key) : (xs.extract start stop).isSortedBy key := h.sublist (toList_extract_sublist xs start stop)
@[grind .] theorem _root_.Array.isSortedBy_mergeSort_le (xs : Array α) (key : α → Nat) : (xs.mergeSort (fun a b => decide (key a ≤ key b))).isSortedBy key :=
  (Array.pairwise_mergeSort (xs := xs) (le := fun a b => decide (key a ≤ key b))
    (trans := fun _ _ _ hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (total := fun a b => by by_cases h : key a ≤ key b <;> simp [h] <;> omega)).imp fun hab => by simpa using hab
end UniqueSorted

/-! ## Bounded `range(stop | start, stop | start, stop, step)`, Loop Folding, Coalescing & `dedupBy` -/

/-- Zero-allocation bounded arithmetic progression `start, start + step, ... < stop`.
    Always total: `step == 0` or `start >= stop` produces 0 iterations. -/
structure QedRange where
  start : Nat
  stop  : Nat
  step  : Nat := 1
deriving Inhabited, DecidableEq, Repr

namespace QedRange
@[inline] def mk1 (stop : Nat) : QedRange := ⟨0, stop, 1⟩
@[inline] def mk2 (start stop : Nat) : QedRange := ⟨start, stop, 1⟩
@[inline] def mk3 (start stop step : Nat) : QedRange := ⟨start, stop, step⟩
@[inline] def count (r : QedRange) : Nat := if r.step == 0 || r.stop ≤ r.start then 0 else (r.stop - r.start + r.step - 1) / r.step
def toListAux (cur step : Nat) : Nat → List Nat | 0 => [] | k + 1 => cur :: toListAux (cur + step) step k
def toList (r : QedRange) : List Nat := toListAux r.start r.step r.count
def toArray (r : QedRange) : Array Nat := r.toList.toArray
def reverse (r : QedRange) : List Nat := r.toList.reverse

theorem toListAux_bounds (cur step : Nat) (hstep : 0 < step) :
    ∀ (k stop : Nat), (k > 0 → cur + (k - 1) * step < stop) → ∀ i ∈ toListAux cur step k, cur ≤ i ∧ i < stop
  | 0, _, _, _, hi => nomatch hi
  | k + 1, stop, hlim, i, hi => by
      simp only [toListAux, List.mem_cons] at hi
      rcases hi with rfl | hmem
      · have := hlim (Nat.succ_pos k); exact ⟨Nat.le_refl _, by omega⟩
      · have hrec := toListAux_bounds (cur + step) step hstep k stop (fun hk => by
          have h0 := hlim (Nat.succ_pos k); simp only [Nat.add_sub_cancel] at h0
          have : cur + step + (k - 1) * step = cur + k * step := by cases k with | zero => omega | succ k' => simp [Nat.succ_mul]; omega
          omega) i hmem
        exact ⟨by omega, hrec.2⟩

theorem mem_toList_bounds (r : QedRange) {i : Nat} (hi : i ∈ r.toList) : r.start ≤ i ∧ i < r.stop := by
  unfold toList count at hi
  by_cases h0 : r.step == 0 || r.stop ≤ r.start
  · simp [h0, toListAux] at hi
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at hi
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at h0
    refine toListAux_bounds r.start r.step (Nat.pos_of_ne_zero h0.1) ((r.stop - r.start + r.step - 1) / r.step) r.stop (fun hk => ?_) i hi
    have hmul := Nat.div_mul_le_self (r.stop - r.start + r.step - 1) r.step
    have : ((r.stop - r.start + r.step - 1) / r.step - 1) * r.step + r.step = ((r.stop - r.start + r.step - 1) / r.step) * r.step := by
      cases hc : (r.stop - r.start + r.step - 1) / r.step with | zero => omega | succ _ => simp [Nat.succ_mul]
    omega
theorem toListAux_length (cur step : Nat) : ∀ k, (toListAux cur step k).length = k
  | 0 => rfl
  | k + 1 => by simp only [toListAux, List.length_cons, toListAux_length]

theorem toList_length (r : QedRange) : r.toList.length = r.count := toListAux_length _ _ _

theorem count_mk1 (n : Nat) : (mk1 n).count = n := by
  unfold count mk1
  cases n with
  | zero => rfl
  | succ m => simp

theorem toList_mk1_length (n : Nat) : (mk1 n).toList.length = n := by
  rw [toList_length, count_mk1]

theorem prefix_elem_eq (cur step : Nat) :
    ∀ (k : Nat) (seen : List Nat) (x : Nat) (rest : List Nat),
      seen ++ x :: rest = toListAux cur step k → x = cur + seen.length * step
  | 0, [], _, _, h => nomatch h
  | 0, _ :: _, _, _, h => nomatch h
  | k + 1, [], x, rest, h => by simp only [List.nil_append, toListAux, List.cons.injEq] at h; simp only [List.length_nil]; omega
  | k + 1, a :: bs, x, rest, h => by
      simp only [List.cons_append, toListAux, List.cons.injEq] at h
      have ih := prefix_elem_eq (cur + step) step k bs x rest h.2
      simp only [List.length_cons, Nat.succ_mul] at ih ⊢; omega

theorem prefix_elem_toList (r : QedRange) {seen rest : List Nat} {x : Nat}
    (h : seen ++ x :: rest = r.toList) : x = r.start + seen.length * r.step :=
  prefix_elem_eq r.start r.step r.count seen x rest h

theorem start_mk1 (n : Nat) : (mk1 n).start = 0 := rfl
theorem stop_mk1  (n : Nat) : (mk1 n).stop = n := rfl
theorem step_mk1  (n : Nat) : (mk1 n).step = 1 := rfl
theorem start_mk2 (a b : Nat) : (mk2 a b).start = a := rfl
theorem stop_mk2  (a b : Nat) : (mk2 a b).stop = b := rfl
theorem step_mk2  (a b : Nat) : (mk2 a b).step = 1 := rfl
theorem start_mk3 (a b c : Nat) : (mk3 a b c).start = a := rfl
theorem stop_mk3  (a b c : Nat) : (mk3 a b c).stop = b := rfl
theorem step_mk3  (a b c : Nat) : (mk3 a b c).step = c := rfl

end QedRange

/-- Total loop-control result for `for ... in ...:` with `let mut`, `continue`, `break`, and `return`. -/
inductive QedLoopStep (σ ρ : Type) where
  | next (st : σ)
  | breakLoop (st : σ)
  | ret (st : σ) (val : ρ)
deriving Inhabited, DecidableEq, Repr

/-- Unified iterable class for `for x in xs:` over `List`, `Array`, and `QedRange`. -/
class QedIterable (C : Type) (α : outParam Type) where toList : C → List α
instance {α : Type} : QedIterable (List α) α := ⟨id⟩
instance {α : Type} : QedIterable (Array α) α := ⟨Array.toList⟩
instance : QedIterable QedRange Nat := ⟨QedRange.toList⟩
@[simp] theorem qedIterable_toList_list  {α : Type} (xs : List α)  : QedIterable.toList xs = xs := rfl
@[simp] theorem qedIterable_toList_array {α : Type} (xs : Array α) : QedIterable.toList xs = xs.toList := rfl
@[simp] theorem qedIterable_toList_range (r : QedRange)            : QedIterable.toList r = r.toList := rfl

/-- Closure-free pure fold for `for x in xs:` with mutable state `σ` and early `break`/`return`. -/
def qedForFoldList {α σ ρ : Type} (xs : List α) (st : σ) (body : σ → α → QedLoopStep σ ρ) : σ × Option ρ :=
  match xs with
  | [] => (st, none)
  | x :: rest => match body st x with | .next st' => qedForFoldList rest st' body | .breakLoop st' => (st', none) | .ret st' v => (st', some v)

/-- Zero-allocation pure range loop for `for i in range(...)`. -/
def qedForRangeAux {σ ρ : Type} (cur step : Nat) : Nat → σ → (σ → Nat → QedLoopStep σ ρ) → σ × Option ρ
  | 0, st, _ => (st, none)
  | k + 1, st, body => match body st cur with | .next st' => qedForRangeAux (cur + step) step k st' body | .breakLoop st' => (st', none) | .ret st' v => (st', some v)

def qedForRange {σ ρ : Type} (r : QedRange) (st : σ) (body : σ → Nat → QedLoopStep σ ρ) : σ × Option ρ := qedForRangeAux r.start r.step r.count st body
def qedForFold {C α σ ρ : Type} [QedIterable C α] (xs : C) (st : σ) (body : σ → α → QedLoopStep σ ρ) : σ × Option ρ := qedForFoldList (QedIterable.toList xs) st body

/-- Proof-only annotation wrappers carrying an explicit `for`-loop invariant predicate (`Prop`-erased at runtime). -/
@[inline] def qedForFoldAnn {α σ ρ : Type} (xs : List α) (st : σ) (body : σ → α → QedLoopStep σ ρ) (_inv : List α → σ → Prop) : σ × Option ρ :=
  qedForFoldList xs st body
@[inline] def qedForRangeAnn {σ ρ : Type} (r : QedRange) (st : σ) (body : σ → Nat → QedLoopStep σ ρ) (_inv : List Nat → σ → Prop) : σ × Option ρ :=
  qedForRange r st body

theorem qedForFoldAnn_eq_foldList {α σ ρ : Type} (xs : List α) (st : σ) (body : σ → α → QedLoopStep σ ρ) (inv : List α → σ → Prop) :
    qedForFoldAnn xs st body inv = qedForFoldList xs st body := rfl

theorem qedForRangeAux_eq_foldList {σ ρ : Type} (cur step : Nat) :
    ∀ (k : Nat) (st : σ) (body : σ → Nat → QedLoopStep σ ρ),
      qedForRangeAux cur step k st body = qedForFoldList (QedRange.toListAux cur step k) st body
  | 0, _, _ => rfl
  | k + 1, st, body => by
      simp only [qedForRangeAux, QedRange.toListAux, qedForFoldList]
      cases body st cur with
      | next st' => exact qedForRangeAux_eq_foldList (cur + step) step k st' body
      | breakLoop st' => rfl
      | ret st' v => rfl

theorem qedForRange_eq_foldList {σ ρ : Type} (r : QedRange) (st : σ) (body : σ → Nat → QedLoopStep σ ρ) :
    qedForRange r st body = qedForFoldList r.toList st body :=
  qedForRangeAux_eq_foldList r.start r.step r.count st body

theorem qedForRangeAnn_eq_foldList {σ ρ : Type} (r : QedRange) (st : σ) (body : σ → Nat → QedLoopStep σ ρ) (inv : List Nat → σ → Prop) :
    qedForRangeAnn r st body inv = qedForFoldList r.toList st body :=
  qedForRange_eq_foldList r st body

/-- Opaque step-matcher for `qedForFoldList_spec` so `split` splits the loop body's `if`/`match`
    before dispatching on `.next`/`.breakLoop`/`.ret`, avoiding spurious unreachable branches. -/
def qedMatchStep {σ ρ : Type} (s : QedLoopStep σ ρ)
    (onNext : σ → Prop) (onBreak : σ → Prop) (onRet : σ → ρ → Prop) : Prop :=
  match s with
  | .next st'      => onNext st'
  | .breakLoop st' => onBreak st'
  | .ret st' v     => onRet st' v

theorem qedMatchStep_next {σ ρ : Type} (st' : σ) (fn fb : σ → Prop) (fr : σ → ρ → Prop) :
    qedMatchStep (.next st') fn fb fr = fn st' := rfl
theorem qedMatchStep_break {σ ρ : Type} (st' : σ) (fn fb : σ → Prop) (fr : σ → ρ → Prop) :
    qedMatchStep (.breakLoop st') fn fb fr = fb st' := rfl
theorem qedMatchStep_ret {σ ρ : Type} (st' : σ) (v : ρ) (fn fb : σ → Prop) (fr : σ → ρ → Prop) :
    qedMatchStep (.ret st' v) fn fb fr = fr st' v := rfl
theorem qedMatchStep_dite {σ ρ : Type} {c : Prop} [Decidable c]
    (t : c → QedLoopStep σ ρ) (e : ¬ c → QedLoopStep σ ρ) (fn fb : σ → Prop) (fr : σ → ρ → Prop) :
    qedMatchStep (dite c t e) fn fb fr = dite c (fun h => qedMatchStep (t h) fn fb fr) (fun h => qedMatchStep (e h) fn fb fr) := by
  by_cases h : c <;> simp [h]
theorem qedMatchStep_ite {σ ρ : Type} {c : Prop} [Decidable c]
    (t e : QedLoopStep σ ρ) (fn fb : σ → Prop) (fr : σ → ρ → Prop) :
    qedMatchStep (ite c t e) fn fb fr = ite c (qedMatchStep t fn fb fr) (qedMatchStep e fn fb fr) := by
  by_cases h : c <;> simp [h]
theorem qedMatchStep_option {α σ ρ : Type} (o : Option α)
    (onNone : QedLoopStep σ ρ) (onSome : α → QedLoopStep σ ρ) (fn fb : σ → Prop) (fr : σ → ρ → Prop) :
    qedMatchStep (Option.casesOn o onNone onSome) fn fb fr =
      Option.casesOn o (qedMatchStep onNone fn fb fr) (fun a => qedMatchStep (onSome a) fn fb fr) := by
  cases o <;> rfl

private theorem qedForFoldList_spec_aux {α σ ρ : Type} (xs : List α)
    (I : List α → σ → Prop) (P : σ × Option ρ → Prop) (body : σ → α → QedLoopStep σ ρ)
    (hStep : ∀ seen x rest st, seen ++ x :: rest = xs → I seen st →
      qedMatchStep (body st x) (fun st' => I (seen ++ [x]) st') (fun st' => P (st', none)) (fun st' v => P (st', some v)))
    (hDone : ∀ st, I xs st → P (st, none)) :
    ∀ seen rem st, seen ++ rem = xs → I seen st → P (qedForFoldList rem st body)
  | seen, [], st, heq, hI => by
      simp only [List.append_nil] at heq; subst heq; exact hDone st hI
  | seen, x :: rest, st, heq, hI => by
      unfold qedForFoldList
      have hs := hStep seen x rest st heq hI
      cases hb : body st x with
      | next st' =>
          rw [hb, qedMatchStep_next] at hs
          exact qedForFoldList_spec_aux xs I P body hStep hDone (seen ++ [x]) rest st'
            (by simpa [List.append_assoc] using heq) hs
      | breakLoop st' => rw [hb, qedMatchStep_break] at hs; exact hs
      | ret st' v     => rw [hb, qedMatchStep_ret] at hs; exact hs

theorem qedForFoldList_spec {α σ ρ : Type} (xs : List α) (st0 : σ)
    (body : σ → α → QedLoopStep σ ρ) (I : List α → σ → Prop) (P : σ × Option ρ → Prop)
    (hInit : I [] st0)
    (hStep : ∀ seen x rest st, seen ++ x :: rest = xs → I seen st →
      qedMatchStep (body st x) (fun st' => I (seen ++ [x]) st') (fun st' => P (st', none)) (fun st' v => P (st', some v)))
    (hDone : ∀ st, I xs st → P (st, none)) :
    P (qedForFoldList xs st0 body) :=
  qedForFoldList_spec_aux xs I P body hStep hDone [] xs st0 rfl hInit

theorem mem_of_append_cons {α : Type} {seen rest xs : List α} {x : α} (h : seen ++ x :: rest = xs) : x ∈ xs := by
  rw [← h]; exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))

theorem mem_array_of_mem_toList {α : Type} {a : α} {xs : Array α} (h : a ∈ xs.toList) : a ∈ xs :=
  Array.mem_toList_iff.mp h

theorem mem_of_prefix_append_cons {α : Type} {seen rest xs : List α} {x y : α} (h : seen ++ x :: rest = xs) (hy : y ∈ seen) : y ∈ xs := by
  rw [← h]; exact List.mem_append.2 (Or.inl hy)

theorem forall_mem_append_singleton {α : Type} {xs : List α} {x : α} {P : α → Prop} :
    (∀ y ∈ xs ++ [x], P y) ↔ (∀ y ∈ xs, P y) ∧ P x := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨fun h => ⟨fun y hy => h y (.inl hy), h x (.inr rfl)⟩, fun ⟨h1, h2⟩ y hy => hy.elim (h1 y) (· ▸ h2)⟩

theorem exists_mem_append_singleton {α : Type} {xs : List α} {x : α} {P : α → Prop} :
    (∃ y ∈ xs ++ [x], P y) ↔ (∃ y ∈ xs, P y) ∨ P x := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨fun ⟨y, hy, hp⟩ => hy.elim (fun h1 => .inl ⟨y, h1, hp⟩) (fun h2 => .inr (h2 ▸ hp)),
         fun h => h.elim (fun ⟨y, hy, hp⟩ => ⟨y, .inl hy, hp⟩) (fun hp => ⟨x, .inr rfl, hp⟩)⟩

theorem forall_mem_nil_iff {α : Type} {P : α → Prop} : (∀ y ∈ ([] : List α), P y) ↔ True :=
  ⟨fun _ => trivial, fun _ _ h => nomatch h⟩

theorem exists_mem_nil_iff {α : Type} {P : α → Prop} : (∃ y ∈ ([] : List α), P y) ↔ False :=
  ⟨fun ⟨_, h, _⟩ => List.not_mem_nil h, False.elim⟩

/-- Non-reducible marker used to verify standalone `for` loop invariants when a `fn` has no `ensures`. -/
def QedLoopInvCheck {α : Type} (_ : α) : Prop := True
theorem qedLoopInvCheck_intro {α : Type} (x : α) : QedLoopInvCheck x := True.intro

/-- Typeclass for `a ?? b` coalescing (lazy lowering via `toOption`). -/
class QedCoalesce (C : Type) (α : outParam Type) where toOption : C → Option α
instance {α : Type} : QedCoalesce (Option α) α := ⟨id⟩
@[simp] theorem qedCoalesce_option {α : Type} (o : Option α) : QedCoalesce.toOption o = o := rfl

/-- Deduplicates an array preserving first-seen order by key. -/
def _root_.Array.dedupBy {α β : Type} [BEq β] (xs : Array α) (key : α → β) : Array α :=
  xs.foldl (init := #[]) fun acc x => let kx := key x; if acc.any (fun y => key y == kx) then acc else acc.push x

namespace Lang

/-! ## Shared Runtime Typeclasses & Proof Helpers (Kernel-Reducible, Zero Overhead) -/

class QedVal (α : Type) (β : outParam Type) where val : α → β
@[reducible, inline] instance (priority := low) {α : Type} : QedVal α α := ⟨id⟩
@[simp] theorem QedVal.val_id {α : Type} (x : α) : QedVal.val x = x := rfl

class QedSeqLit (C : Type) (α : outParam Type) where ofList : List α → C
@[default_instance, reducible, inline] instance {α : Type} : QedSeqLit (Array α) α := ⟨List.toArray⟩
@[reducible, inline] instance {α : Type} : QedSeqLit (List α) α := ⟨id⟩
@[simp] theorem QedSeqLit.ofList_array {α : Type} (xs : List α) : (QedSeqLit.ofList xs : Array α) = xs.toArray := rfl
@[simp] theorem QedSeqLit.ofList_list {α : Type} (xs : List α) : (QedSeqLit.ofList xs : List α) = xs := rfl

class QedMem (α : Type) (C : Type) where mem : α → C → Bool
class QedMemProp (α : Type) (C : Type) where memProp : α → C → Prop

@[inline] instance {α : Type} [BEq α] : QedMem α (Array α) := ⟨fun x xs => xs.contains x⟩
@[simp] theorem QedMem.mem_array {α : Type} [BEq α] (x : α) (xs : Array α) : QedMem.mem x xs = xs.contains x := rfl
@[reducible] instance {α : Type} : QedMemProp α (Array α) := ⟨fun x xs => x ∈ xs⟩
@[simp] theorem QedMemProp.memProp_array {α : Type} (x : α) (xs : Array α) : QedMemProp.memProp x xs = (x ∈ xs) := rfl
instance {α : Type} [DecidableEq α] (x : α) (xs : Array α) : Decidable (QedMemProp.memProp x xs) := inferInstanceAs (Decidable (x ∈ xs))

@[inline] instance {α : Type} [BEq α] : QedMem α (List α) := ⟨fun x xs => xs.contains x⟩
@[simp] theorem QedMem.mem_list {α : Type} [BEq α] (x : α) (xs : List α) : QedMem.mem x xs = xs.contains x := rfl
@[reducible] instance {α : Type} : QedMemProp α (List α) := ⟨fun x xs => x ∈ xs⟩
@[simp] theorem QedMemProp.memProp_list {α : Type} (x : α) (xs : List α) : QedMemProp.memProp x xs = (x ∈ xs) := rfl
instance {α : Type} [DecidableEq α] (x : α) (xs : List α) : Decidable (QedMemProp.memProp x xs) := inferInstanceAs (Decidable (x ∈ xs))

@[inline] instance : QedMem Char String := ⟨fun c s => s.contains c⟩
@[simp] theorem QedMem.mem_string (c : Char) (s : String) : QedMem.mem c s = s.contains c := rfl
@[reducible] instance : QedMemProp Char String := ⟨fun c s => s.contains c = true⟩
@[simp] theorem QedMemProp.memProp_string (c : Char) (s : String) : QedMemProp.memProp c s = (s.contains c = true) := rfl
instance (c : Char) (s : String) : Decidable (QedMemProp.memProp c s) := inferInstanceAs (Decidable (s.contains c = true))

end Lang

/-! ## Component Primitive, `Array.sortBy`, and `ForEach` Preservation Lemmas -/

structure Component (Model Msg : Type) where mk :: (update : Model → Msg → Model) (view : Model → Html Msg)
def Component.render (c : Component Model Msg) (wrap : Msg → PMsg) (m : Model) : Html PMsg := (c.view m).map wrap
def Component.updateKeyed (c : Component Model Msg) (key : Model → String) (models : Array Model) (k : String) (msg : Msg) : Array Model :=
  models.map fun r => if key r == k then c.update r msg else r

-- `mergeSort` provides `Array.mem_mergeSort`; `Array.qsort` has no stdlib membership lemma.
@[reducible] def _root_.Array.sortBy {α} (a : Array α) (le : α → α → Bool) : Array α := a.mergeSort le
@[simp, grind =] theorem _root_.Array.mem_sortBy {α} {a : Array α} {le : α → α → Bool} {y : α} : y ∈ a.sortBy le ↔ y ∈ a := Array.mem_mergeSort

/-! ## Verified `min`, `max`, `sort`, `isSorted`, `isMinOf`, `isMaxOf` (`QedOrd`, `Desc`, `QedSeq`) -/

/-- Wrapper that reverses `QedOrd` on a single component (e.g. `s => (Desc(s.score), s.name)`). -/
structure DescKey (α : Type) where
  val : α
deriving Inhabited, DecidableEq, Repr

/-- Flip comparison direction for a single sort/min/max key component. -/
@[inline] def Desc {α : Type} (x : α) : DescKey α := ⟨x⟩

/-- Lawful total order powering verified `min`, `max`, `sort`, and `isSorted` over arbitrary keys and tuples. -/
class QedOrd (α : Type) where
  le          : α → α → Prop
  leB         : α → α → Bool
  leB_iff     : ∀ a b, leB a b = true ↔ le a b
  le_refl     : ∀ a, le a a
  le_trans    : ∀ a b c, le a b → le b c → le a c
  le_total    : ∀ a b, le a b ∨ le b a
  le_antisymm : ∀ a b, le a b → le b a → a = b

namespace QedOrd

@[instance_reducible, inline] def ofLinearOrder (α : Type) [LE α] [DecidableLE α] [Std.IsLinearOrder α] : QedOrd α where
  le := (· ≤ ·)
  leB a b := decide (a ≤ b)
  leB_iff _ _ := decide_eq_true_iff
  le_refl := Std.le_refl
  le_trans _ _ _ := Std.le_trans
  le_total _ _ := Std.le_total
  le_antisymm _ _ := Std.le_antisymm

instance : QedOrd Nat := ofLinearOrder Nat
instance : QedOrd Int := ofLinearOrder Int
instance : QedOrd Char := ofLinearOrder Char
instance : QedOrd String := ofLinearOrder String

instance : QedOrd Bool where
  le := (· ≤ ·)
  leB a b := !a || b
  leB_iff a b := by cases a <;> cases b <;> decide
  le_refl a := by cases a <;> decide
  le_trans a b c := by cases a <;> cases b <;> cases c <;> decide
  le_total a b := by cases a <;> cases b <;> decide
  le_antisymm a b := by cases a <;> cases b <;> decide

instance {α : Type} [QedOrd α] : QedOrd (DescKey α) where
  le a b := QedOrd.le b.val a.val
  leB a b := QedOrd.leB b.val a.val
  leB_iff a b := QedOrd.leB_iff b.val a.val
  le_refl a := QedOrd.le_refl a.val
  le_trans a b c hab hbc := QedOrd.le_trans c.val b.val a.val hbc hab
  le_total a b := (QedOrd.le_total b.val a.val)
  le_antisymm a b hab hba := by cases a; cases b; congr; exact QedOrd.le_antisymm _ _ hba hab

instance {α β : Type} [QedOrd α] [QedOrd β] : QedOrd (α × β) where
  le a b := QedOrd.le a.1 b.1 ∧ (a.1 = b.1 → QedOrd.le a.2 b.2)
  leB a b := if QedOrd.leB a.1 b.1 then (if QedOrd.leB b.1 a.1 then QedOrd.leB a.2 b.2 else true) else false
  leB_iff a b := by
    by_cases h1 : QedOrd.leB a.1 b.1 = true
    · by_cases h2 : QedOrd.leB b.1 a.1 = true
      · simp only [h1, h2, ↓reduceIte, QedOrd.leB_iff]
        have ha : QedOrd.le a.1 b.1 := (QedOrd.leB_iff _ _).1 h1
        have heq : a.1 = b.1 := QedOrd.le_antisymm _ _ ha ((QedOrd.leB_iff _ _).1 h2)
        exact ⟨fun h => ⟨ha, fun _ => h⟩, fun ⟨_, h⟩ => h heq⟩
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, true_iff]
        have ha : QedOrd.le a.1 b.1 := (QedOrd.leB_iff _ _).1 h1
        exact ⟨ha, fun heq => False.elim (h2 ((QedOrd.leB_iff _ _).2 (heq ▸ QedOrd.le_refl _)))⟩
    · simp only [h1, ↓reduceIte, Bool.false_eq_true, false_iff]
      intro ⟨ha, _⟩; exact h1 ((QedOrd.leB_iff _ _).2 ha)
  le_refl a := ⟨QedOrd.le_refl a.1, fun _ => QedOrd.le_refl a.2⟩
  le_trans a b c := fun ⟨h1, h2⟩ ⟨g1, g2⟩ =>
    ⟨QedOrd.le_trans _ _ _ h1 g1, fun heq =>
      have hab : a.1 = b.1 := QedOrd.le_antisymm _ _ h1 (heq ▸ g1)
      QedOrd.le_trans _ _ _ (h2 hab) (g2 (hab.symm.trans heq))⟩
  le_total a b := by
    by_cases h1 : QedOrd.leB a.1 b.1 = true
    · by_cases h2 : QedOrd.leB b.1 a.1 = true
      · have hab := (QedOrd.leB_iff _ _).1 h1; have hba := (QedOrd.leB_iff _ _).1 h2
        exact (QedOrd.le_total a.2 b.2).elim (fun h => .inl ⟨hab, fun _ => h⟩) (fun h => .inr ⟨hba, fun _ => h⟩)
      · exact .inl ⟨(QedOrd.leB_iff _ _).1 h1, fun heq => False.elim (h2 ((QedOrd.leB_iff _ _).2 (heq ▸ QedOrd.le_refl _)))⟩
    · have hba : QedOrd.le b.1 a.1 := (QedOrd.le_total a.1 b.1).elim (fun h => False.elim (h1 ((QedOrd.leB_iff _ _).2 h))) id
      exact .inr ⟨hba, fun heq => False.elim (h1 ((QedOrd.leB_iff _ _).2 (heq ▸ QedOrd.le_refl _)))⟩
  le_antisymm a b := fun ⟨h1, h2⟩ ⟨g1, g2⟩ => by
    have heq1 : a.1 = b.1 := QedOrd.le_antisymm _ _ h1 g1
    have heq2 : a.2 = b.2 := QedOrd.le_antisymm _ _ (h2 heq1) (g2 heq1.symm)
    cases a; cases b; cases heq1; cases heq2; rfl

def optLe {α : Type} [QedOrd α] : Option α → Option α → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => QedOrd.le a b

def optLeB {α : Type} [QedOrd α] : Option α → Option α → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => QedOrd.leB a b

instance {α : Type} [QedOrd α] : QedOrd (Option α) where
  le := optLe
  leB := optLeB
  leB_iff a b := by cases a <;> cases b <;> simp [optLe, optLeB, QedOrd.leB_iff]
  le_refl a := by cases a with | none => trivial | some x => exact QedOrd.le_refl x
  le_trans a b c := by
    cases a <;> cases b <;> cases c <;> simp [optLe]
    exact QedOrd.le_trans _ _ _
  le_total a b := by
    cases a <;> cases b <;> simp [optLe]
    exact QedOrd.le_total _ _
  le_antisymm a b := by
    cases a <;> cases b <;> simp [optLe]
    exact QedOrd.le_antisymm _ _

def listLe {α : Type} [QedOrd α] : List α → List α → Prop
  | [], _ => True
  | _ :: _, [] => False
  | a :: as, b :: bs => QedOrd.le a b ∧ (a = b → listLe as bs)

def listLeB {α : Type} [QedOrd α] : List α → List α → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if QedOrd.leB a b then (if QedOrd.leB b a then listLeB as bs else true) else false

private theorem listLeB_iff {α : Type} [QedOrd α] : ∀ (as bs : List α), listLeB as bs = true ↔ listLe as bs
  | [], _ => by simp [listLe, listLeB]
  | _ :: _, [] => by simp [listLe, listLeB]
  | a :: as, b :: bs => by
      simp only [listLe, listLeB]
      by_cases h1 : QedOrd.leB a b = true
      · by_cases h2 : QedOrd.leB b a = true
        · simp only [h1, h2, ↓reduceIte, listLeB_iff]
          have ha := (QedOrd.leB_iff _ _).1 h1
          have heq := QedOrd.le_antisymm _ _ ha ((QedOrd.leB_iff _ _).1 h2)
          exact ⟨fun h => ⟨ha, fun _ => h⟩, fun ⟨_, h⟩ => h heq⟩
        · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, true_iff]
          exact ⟨(QedOrd.leB_iff _ _).1 h1, fun heq => False.elim (h2 ((QedOrd.leB_iff _ _).2 (heq ▸ QedOrd.le_refl _)))⟩
      · simp only [h1, ↓reduceIte, Bool.false_eq_true, false_iff]
        intro ⟨ha, _⟩; exact h1 ((QedOrd.leB_iff _ _).2 ha)

private theorem listLe_refl {α : Type} [QedOrd α] : ∀ (as : List α), listLe as as
  | [] => trivial
  | a :: as => ⟨QedOrd.le_refl a, fun _ => listLe_refl as⟩

private theorem listLe_trans {α : Type} [QedOrd α] : ∀ (as bs cs : List α), listLe as bs → listLe bs cs → listLe as cs
  | [], _, _, _, _ => trivial
  | _ :: _, [], _, h, _ => False.elim h
  | _ :: _, _ :: _, [], _, h => False.elim h
  | a :: as, b :: bs, _ :: cs, ⟨h1, h2⟩, ⟨g1, g2⟩ =>
      ⟨QedOrd.le_trans _ _ _ h1 g1, fun heq =>
        have hab : a = b := QedOrd.le_antisymm _ _ h1 (heq ▸ g1)
        listLe_trans as bs cs (h2 hab) (g2 (hab.symm.trans heq))⟩

private theorem listLe_total {α : Type} [QedOrd α] : ∀ (as bs : List α), listLe as bs ∨ listLe bs as
  | [], _ => .inl trivial
  | _ :: _, [] => .inr trivial
  | a :: as, b :: bs => by
      by_cases h1 : QedOrd.leB a b = true
      · by_cases h2 : QedOrd.leB b a = true
        · have hab := (QedOrd.leB_iff _ _).1 h1; have hba := (QedOrd.leB_iff _ _).1 h2
          exact (listLe_total as bs).elim (fun h => .inl ⟨hab, fun _ => h⟩) (fun h => .inr ⟨hba, fun _ => h⟩)
        · exact .inl ⟨(QedOrd.leB_iff _ _).1 h1, fun heq => False.elim (h2 ((QedOrd.leB_iff _ _).2 (heq ▸ QedOrd.le_refl _)))⟩
      · have hba : QedOrd.le b a := (QedOrd.le_total a b).elim (fun h => False.elim (h1 ((QedOrd.leB_iff _ _).2 h))) id
        exact .inr ⟨hba, fun heq => False.elim (h1 ((QedOrd.leB_iff _ _).2 (heq ▸ QedOrd.le_refl _)))⟩

private theorem listLe_antisymm {α : Type} [QedOrd α] : ∀ (as bs : List α), listLe as bs → listLe bs as → as = bs
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => False.elim h
  | _ :: _, [], h, _ => False.elim h
  | a :: as, b :: bs, ⟨h1, h2⟩, ⟨g1, g2⟩ => by
      have heq := QedOrd.le_antisymm _ _ h1 g1
      have htl := listLe_antisymm as bs (h2 heq) (g2 heq.symm)
      rw [heq, htl]

instance {α : Type} [QedOrd α] : QedOrd (List α) where
  le := listLe
  leB := listLeB
  leB_iff := listLeB_iff
  le_refl := listLe_refl
  le_trans := listLe_trans
  le_total := listLe_total
  le_antisymm := listLe_antisymm

instance {α : Type} [QedOrd α] : QedOrd (Array α) where
  le a b := listLe a.toList b.toList
  leB a b := listLeB a.toList b.toList
  leB_iff a b := listLeB_iff a.toList b.toList
  le_refl a := listLe_refl a.toList
  le_trans a b c := listLe_trans a.toList b.toList c.toList
  le_total a b := listLe_total a.toList b.toList
  le_antisymm a b hab hba := Array.toList_inj.1 (listLe_antisymm a.toList b.toList hab hba)

theorem le_nat (a b : Nat) : QedOrd.le a b ↔ a ≤ b := Iff.rfl
theorem le_int (a b : Int) : QedOrd.le a b ↔ a ≤ b := Iff.rfl
theorem le_char (a b : Char) : QedOrd.le a b ↔ a ≤ b := Iff.rfl
theorem le_string (a b : String) : QedOrd.le a b ↔ a ≤ b := Iff.rfl
theorem le_bool (a b : Bool) : QedOrd.le a b ↔ a ≤ b := Iff.rfl
theorem le_desc {α : Type} [QedOrd α] (a b : DescKey α) : QedOrd.le a b ↔ QedOrd.le b.val a.val := Iff.rfl
theorem le_desc_mk {α : Type} [QedOrd α] (a b : α) : QedOrd.le (Desc a) (Desc b) ↔ QedOrd.le b a := Iff.rfl
theorem le_prod {α β : Type} [QedOrd α] [QedOrd β] (a b : α × β) : QedOrd.le a b ↔ QedOrd.le a.1 b.1 ∧ (a.1 = b.1 → QedOrd.le a.2 b.2) := Iff.rfl
theorem le_option_none {α : Type} [QedOrd α] (b : Option α) : QedOrd.le (none : Option α) b ↔ True := Iff.rfl
theorem le_option_some_none {α : Type} [QedOrd α] (a : α) : QedOrd.le (some a) none ↔ False := Iff.rfl
theorem le_option_some {α : Type} [QedOrd α] (a b : α) : QedOrd.le (some a) (some b) ↔ QedOrd.le a b := Iff.rfl
theorem leB_eq_true {α : Type} [QedOrd α] (a b : α) : QedOrd.leB a b = true ↔ QedOrd.le a b := QedOrd.leB_iff a b
theorem leB_eq_false {α : Type} [QedOrd α] (a b : α) : QedOrd.leB a b = false ↔ ¬ QedOrd.le a b := by
  rw [← QedOrd.leB_iff]; cases QedOrd.leB a b <;> decide
theorem leB_total {α : Type} [QedOrd α] (a b : α) : (QedOrd.leB a b || QedOrd.leB b a) = true := by
  rw [Bool.or_eq_true, QedOrd.leB_iff, QedOrd.leB_iff]; exact QedOrd.le_total a b
theorem leB_trans {α : Type} [QedOrd α] (a b c : α) (h1 : QedOrd.leB a b = true) (h2 : QedOrd.leB b c = true) :
    QedOrd.leB a c = true :=
  (QedOrd.leB_iff a c).2 (QedOrd.le_trans a b c ((QedOrd.leB_iff a b).1 h1) ((QedOrd.leB_iff b c).1 h2))

end QedOrd

/-- Core O(n) list extremum scan by comparator `le : α → α → Bool` (keeps first element on ties). -/
def qedMinListBy {α : Type} (le : α → α → Bool) (xs : List α) : Option α :=
  xs.foldl (fun acc y => match acc with | none => some y | some cur => if le cur y then some cur else some y) none

/-- Zero-allocation O(n) array extremum scan by comparator `le : α → α → Bool`. -/
@[inline] def qedMinArrayBy {α : Type} (le : α → α → Bool) (xs : Array α) : Option α :=
  xs.foldl (fun acc y => match acc with | none => some y | some cur => if le cur y then some cur else some y) none

theorem qedMinArrayBy_eq_list {α : Type} (le : α → α → Bool) (xs : Array α) :
    qedMinArrayBy le xs = qedMinListBy le xs.toList := by
  simp only [qedMinArrayBy, qedMinListBy, Array.foldl_toList]

theorem qedMinListBy_nil {α : Type} (le : α → α → Bool) : qedMinListBy le [] = none := rfl

theorem qedMinListBy_append_singleton {α : Type} (le : α → α → Bool) (xs : List α) (x : α) :
    qedMinListBy le (xs ++ [x]) = match qedMinListBy le xs with
      | none => some x
      | some cur => if le cur x then some cur else some x := by
  simp only [qedMinListBy, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem qedMinListBy_foldl_some {α : Type} (le : α → α → Bool) :
    ∀ (xs : List α) (acc : α),
      (xs.foldl (fun a y => match a with | none => some y | some cur => if le cur y then some cur else some y) (some acc)).isSome = true
  | [], _ => rfl
  | x :: rest, acc => by
      simp only [List.foldl_cons]
      cases le acc x <;> exact qedMinListBy_foldl_some le rest _

theorem qedMinListBy_isSome_iff {α : Type} (le : α → α → Bool) (xs : List α) :
    (qedMinListBy le xs).isSome = true ↔ ∃ x ∈ xs, True := by
  cases xs with
  | nil => simp [qedMinListBy]
  | cons a rest =>
      constructor
      · intro _; exact ⟨a, List.mem_cons_self, trivial⟩
      · intro _; exact qedMinListBy_foldl_some le rest a

private theorem qedMinListBy_foldl_mem {α : Type} (le : α → α → Bool) :
    ∀ (xs : List α) (acc : Option α) (b : α),
      xs.foldl (fun a y => match a with | none => some y | some cur => if le cur y then some cur else some y) acc = some b →
      acc = some b ∨ b ∈ xs
  | [], acc, b, h => .inl h
  | x :: rest, none, b, h => by
      simp only [List.foldl_cons] at h
      rcases qedMinListBy_foldl_mem le rest (some x) b h with heq | hmem
      · cases heq; exact .inr List.mem_cons_self
      · exact .inr (List.mem_cons_of_mem x hmem)
  | x :: rest, some cur, b, h => by
      simp only [List.foldl_cons] at h
      by_cases hle : le cur x = true
      · simp only [hle, ↓reduceIte] at h
        rcases qedMinListBy_foldl_mem le rest (some cur) b h with heq | hmem
        · exact .inl heq
        · exact .inr (List.mem_cons_of_mem x hmem)
      · have hlf : le cur x = false := Bool.eq_false_iff.2 hle
        simp only [hlf, Bool.false_eq_true, ↓reduceIte] at h
        rcases qedMinListBy_foldl_mem le rest (some x) b h with heq | hmem
        · cases heq; exact .inr List.mem_cons_self
        · exact .inr (List.mem_cons_of_mem x hmem)

theorem qedMinListBy_mem {α : Type} {le : α → α → Bool} {xs : List α} {b : α}
    (h : qedMinListBy le xs = some b) : b ∈ xs := by
  rcases qedMinListBy_foldl_mem le xs none b h with hno | hm
  · cases hno
  · exact hm

private theorem qedMinListBy_foldl_le {α : Type} (le : α → α → Bool)
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true) :
    ∀ (xs seen : List α) (acc : Option α) (b : α),
      (∀ c, acc = some c → ∀ y ∈ seen, le c y = true) →
      (acc = none → seen = []) →
      xs.foldl (fun a y => match a with | none => some y | some cur => if le cur y then some cur else some y) acc = some b →
      ∀ y ∈ seen ++ xs, le b y = true
  | [], seen, acc, b, hInv, _, h, y, hy => by
      simp only [List.append_nil] at hy
      exact hInv b h y hy
  | x :: rest, seen, none, b, _, hNil, h, y, hy => by
      have hs := hNil rfl; subst hs
      simp only [List.foldl_cons] at h
      have hRefl : le x x = true := by have ht := hTotal x x; simpa using ht
      have hRec := qedMinListBy_foldl_le le hTrans hTotal rest [x] (some x) b
        (fun c hc z hz => by cases hc; simp only [List.mem_singleton] at hz; subst hz; exact hRefl)
        (fun hno => nomatch hno) h y (by simpa using hy)
      exact hRec
  | x :: rest, seen, some cur, b, hInv, _, h, y, hy => by
      simp only [List.foldl_cons] at h
      have hCur := hInv cur rfl
      by_cases hle : le cur x = true
      · simp only [hle, ↓reduceIte] at h
        have hNext : ∀ c, some cur = some c → ∀ z ∈ seen ++ [x], le c z = true := fun c hc z hz => by
          cases hc; simp only [List.mem_append, List.mem_singleton] at hz
          exact hz.elim (hCur z) (fun heq => heq ▸ hle)
        exact qedMinListBy_foldl_le le hTrans hTotal rest (seen ++ [x]) (some cur) b hNext (fun hno => nomatch hno) h y
          (by simpa [List.append_assoc] using hy)
      · have hlf : le cur x = false := Bool.eq_false_iff.2 hle
        simp only [hlf, Bool.false_eq_true, ↓reduceIte] at h
        have hxCur : le x cur = true := by have ht := hTotal cur x; simp [hlf] at ht; exact ht
        have hRefl : le x x = true := by have ht := hTotal x x; simpa using ht
        have hNext : ∀ c, some x = some c → ∀ z ∈ seen ++ [x], le c z = true := fun c hc z hz => by
          cases hc; simp only [List.mem_append, List.mem_singleton] at hz
          exact hz.elim (fun hz' => hTrans x cur z hxCur (hCur z hz')) (fun heq => heq ▸ hRefl)
        exact qedMinListBy_foldl_le le hTrans hTotal rest (seen ++ [x]) (some x) b hNext (fun hno => nomatch hno) h y
          (by simpa [List.append_assoc] using hy)

theorem qedMinListBy_le {α : Type} {le : α → α → Bool} {xs : List α} {b : α}
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true)
    (h : qedMinListBy le xs = some b) : ∀ y ∈ xs, le b y = true :=
  qedMinListBy_foldl_le le hTrans hTotal xs [] none b (fun _ hno => nomatch hno) (fun _ => rfl) h

/-- O(n) adjacent-pair sortedness check for runtime `Bool` evaluation. -/
def qedIsSortedListB {α : Type} (le : α → α → Bool) : List α → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => le a b && qedIsSortedListB le (b :: rest)

theorem qedIsSortedListB_eq_true_iff {α : Type} {le : α → α → Bool}
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true) :
    ∀ (xs : List α), qedIsSortedListB le xs = true ↔ xs.Pairwise (fun a b => le a b = true)
  | [] => by simp [qedIsSortedListB]
  | [_] => by simp [qedIsSortedListB]
  | a :: b :: rest => by
      simp only [qedIsSortedListB, Bool.and_eq_true, qedIsSortedListB_eq_true_iff hTrans (b :: rest), List.pairwise_cons]
      constructor
      · intro ⟨hab, hB, hRest⟩
        refine ⟨fun y hy => ?_, hB, hRest⟩
        simp only [List.mem_cons] at hy
        exact hy.elim (fun heq => heq ▸ hab) (fun hr => hTrans a b y hab (hB y hr))
      · intro ⟨hA, hB, hRest⟩
        exact ⟨hA b List.mem_cons_self, hB, hRest⟩

/-- Structurally recursive, kernel-reducible, stable O(n log n) bottom-up merge sort. -/
def qedMergeGo {α : Type} (le : α → α → Bool) (x : α) (xs : List α) (mergeTail : List α → List α) : List α → List α
  | [] => x :: xs
  | y :: ys => if le x y then x :: mergeTail (y :: ys) else y :: qedMergeGo le x xs mergeTail ys

def qedMerge {α : Type} (le : α → α → Bool) : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => qedMergeGo le x xs (qedMerge le xs) ys

def qedMergePairs {α : Type} (le : α → α → Bool) : List (List α) → List (List α)
  | a :: b :: rest => qedMerge le a b :: qedMergePairs le rest
  | runs => runs

def qedMergeAll {α : Type} (le : α → α → Bool) : Nat → List (List α) → List α
  | 0, [] => []
  | 0, [r] => r
  | 0, r :: rs => rs.foldl (qedMerge le) r
  | _ + 1, [] => []
  | _ + 1, [r] => r
  | fuel + 1, a :: b :: rest => qedMergeAll le fuel (qedMergePairs le (a :: b :: rest))

def qedMergeSortList {α : Type} (le : α → α → Bool) (xs : List α) : List α :=
  qedMergeAll le xs.length (xs.map ([·]))

private theorem qedMergeGo_perm {α : Type} (le : α → α → Bool) (x : α) (xs : List α)
    (mergeTail : List α → List α) (hTail : ∀ zs, (mergeTail zs).Perm (xs ++ zs)) :
    ∀ ys, (qedMergeGo le x xs mergeTail ys).Perm (x :: xs ++ ys)
  | [] => by simp [qedMergeGo]
  | y :: ys => by
      simp only [qedMergeGo]
      split
      · exact (hTail (y :: ys)).cons x
      · exact ((qedMergeGo_perm le x xs mergeTail hTail ys).cons y).trans List.perm_middle.symm

private theorem qedMerge_perm {α : Type} (le : α → α → Bool) :
    ∀ (xs ys : List α), (qedMerge le xs ys).Perm (xs ++ ys)
  | [], ys => by simp [qedMerge]
  | x :: xs, ys => qedMergeGo_perm le x xs (qedMerge le xs) (qedMerge_perm le xs) ys

private theorem qedMergePairs_flatten_perm {α : Type} (le : α → α → Bool) :
    ∀ (runs : List (List α)), (qedMergePairs le runs).flatten.Perm runs.flatten
  | [] => .refl _
  | [_] => .refl _
  | a :: b :: rest => by
      simp only [qedMergePairs, List.flatten_cons]
      rw [← List.append_assoc]
      exact (qedMerge_perm le a b).append (qedMergePairs_flatten_perm le rest)

private theorem foldl_qedMerge_perm {α : Type} (le : α → α → Bool) :
    ∀ (rs : List (List α)) (acc : List α), (rs.foldl (qedMerge le) acc).Perm (acc ++ rs.flatten)
  | [], acc => by simp
  | r :: rs, acc => by
      simp only [List.foldl_cons, List.flatten_cons, ← List.append_assoc]
      exact (foldl_qedMerge_perm le rs (qedMerge le acc r)).trans ((qedMerge_perm le acc r).append_right _)

private theorem qedMergeAll_perm {α : Type} (le : α → α → Bool) :
    ∀ (fuel : Nat) (runs : List (List α)), (qedMergeAll le fuel runs).Perm runs.flatten
  | 0, [] => .refl _
  | 0, [r] => by simp [qedMergeAll]
  | 0, r :: r' :: rs => by
      simp only [qedMergeAll, List.flatten_cons]
      exact foldl_qedMerge_perm le (r' :: rs) r
  | _ + 1, [] => .refl _
  | _ + 1, [r] => by simp [qedMergeAll]
  | fuel + 1, a :: b :: rest =>
      (qedMergeAll_perm le fuel (qedMergePairs le (a :: b :: rest))).trans
        (qedMergePairs_flatten_perm le (a :: b :: rest))

private theorem flatten_map_singleton {α : Type} : ∀ (xs : List α), (xs.map ([·])).flatten = xs
  | [] => rfl
  | x :: xs => by simp [flatten_map_singleton xs]

theorem qedMergeSortList_perm {α : Type} (le : α → α → Bool) (xs : List α) :
    (qedMergeSortList le xs).Perm xs := by
  have h := qedMergeAll_perm le xs.length (xs.map ([·]))
  rwa [flatten_map_singleton] at h

private theorem qedMergeGo_pairwise {α : Type} (le : α → α → Bool)
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true)
    (x : α) (xs : List α) (mergeTail : List α → List α)
    (hTailPerm : ∀ zs, (mergeTail zs).Perm (xs ++ zs))
    (hTailPw : ∀ zs, zs.Pairwise (fun a b => le a b = true) → (mergeTail zs).Pairwise (fun a b => le a b = true))
    (hx : ∀ z ∈ xs, le x z = true) (hxs : xs.Pairwise (fun a b => le a b = true)) :
    ∀ ys, ys.Pairwise (fun a b => le a b = true) → (qedMergeGo le x xs mergeTail ys).Pairwise (fun a b => le a b = true)
  | [], _ => List.pairwise_cons.2 ⟨hx, hxs⟩
  | y :: ys, hys => by
      simp only [qedMergeGo]
      have ⟨hy, hys'⟩ := List.pairwise_cons.1 hys
      by_cases hxy : le x y = true
      · simp only [hxy, ↓reduceIte, List.pairwise_cons]
        refine ⟨fun z hz => ?_, hTailPw (y :: ys) hys⟩
        rcases List.mem_append.1 ((hTailPerm (y :: ys)).subset hz) with hzx | hzy
        · exact hx z hzx
        · rcases List.mem_cons.1 hzy with rfl | hzy'
          · exact hxy
          · exact hTrans x y z hxy (hy z hzy')
      · have hxyf : le x y = false := Bool.eq_false_iff.2 hxy
        have hyx : le y x = true := by have ht := hTotal x y; simp [hxyf] at ht; exact ht
        simp only [hxyf, Bool.false_eq_true, ↓reduceIte, List.pairwise_cons]
        refine ⟨fun z hz => ?_, qedMergeGo_pairwise le hTrans hTotal x xs mergeTail hTailPerm hTailPw hx hxs ys hys'⟩
        have hz' := (qedMergeGo_perm le x xs mergeTail hTailPerm ys).subset hz
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hz'
        rcases hz' with rfl | hzx | hzy
        · exact hyx
        · exact hTrans y x z hyx (hx z hzx)
        · exact hy z hzy

private theorem qedMerge_pairwise {α : Type} (le : α → α → Bool)
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true) :
    ∀ (xs ys : List α), xs.Pairwise (fun a b => le a b = true) → ys.Pairwise (fun a b => le a b = true) →
      (qedMerge le xs ys).Pairwise (fun a b => le a b = true)
  | [], _, _, hys => hys
  | x :: xs, ys, hxs, hys =>
      let ⟨hx, hxs'⟩ := List.pairwise_cons.1 hxs
      qedMergeGo_pairwise le hTrans hTotal x xs (qedMerge le xs) (qedMerge_perm le xs)
        (fun zs hzs => qedMerge_pairwise le hTrans hTotal xs zs hxs' hzs) hx hxs' ys hys

private theorem qedMergePairs_pairwise {α : Type} (le : α → α → Bool)
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true) :
    ∀ (runs : List (List α)), (∀ r ∈ runs, r.Pairwise (fun a b => le a b = true)) →
      ∀ r ∈ qedMergePairs le runs, r.Pairwise (fun a b => le a b = true)
  | [], _ => fun _ h => nomatch h
  | [_], hr => hr
  | a :: b :: rest, hr => by
      intro r hrm
      simp only [qedMergePairs, List.mem_cons] at hrm
      rcases hrm with rfl | hrest
      · exact qedMerge_pairwise le hTrans hTotal a b (hr a List.mem_cons_self) (hr b (List.mem_cons_of_mem _ List.mem_cons_self))
      · exact qedMergePairs_pairwise le hTrans hTotal rest (fun x hx => hr x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))) r hrest

private theorem foldl_qedMerge_pairwise {α : Type} (le : α → α → Bool)
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true) :
    ∀ (rs : List (List α)) (acc : List α), acc.Pairwise (fun a b => le a b = true) →
      (∀ r ∈ rs, r.Pairwise (fun a b => le a b = true)) →
      (rs.foldl (qedMerge le) acc).Pairwise (fun a b => le a b = true)
  | [], _, hAcc, _ => hAcc
  | r :: rs, acc, hAcc, hrs =>
      foldl_qedMerge_pairwise le hTrans hTotal rs (qedMerge le acc r)
        (qedMerge_pairwise le hTrans hTotal acc r hAcc (hrs r List.mem_cons_self))
        (fun x hx => hrs x (List.mem_cons_of_mem _ hx))

private theorem qedMergeAll_pairwise {α : Type} (le : α → α → Bool)
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true) :
    ∀ (fuel : Nat) (runs : List (List α)), (∀ r ∈ runs, r.Pairwise (fun a b => le a b = true)) →
      (qedMergeAll le fuel runs).Pairwise (fun a b => le a b = true)
  | 0, [], _ => List.Pairwise.nil
  | 0, [r], hr => hr r List.mem_cons_self
  | 0, r :: r' :: rs, hr =>
      foldl_qedMerge_pairwise le hTrans hTotal (r' :: rs) r (hr r List.mem_cons_self) (fun x hx => hr x (List.mem_cons_of_mem _ hx))
  | _ + 1, [], _ => List.Pairwise.nil
  | _ + 1, [r], hr => hr r List.mem_cons_self
  | fuel + 1, a :: b :: rest, hr =>
      qedMergeAll_pairwise le hTrans hTotal fuel (qedMergePairs le (a :: b :: rest))
        (qedMergePairs_pairwise le hTrans hTotal (a :: b :: rest) hr)

theorem qedMergeSortList_pairwise {α : Type} (le : α → α → Bool)
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true) (xs : List α) :
    (qedMergeSortList le xs).Pairwise (fun a b => le a b = true) :=
  qedMergeAll_pairwise le hTrans hTotal xs.length (xs.map ([·])) (fun r hr => by
    rcases List.mem_map.1 hr with ⟨x, _, rfl⟩
    exact List.pairwise_singleton _ x)

/-- Unified sequence interface for verified `min`, `max`, `sort`, and `isSorted` on `Array` and `List`. -/
class QedSeq (C : Type) (α : outParam Type) where
  toList  : C → List α
  sortCmp : C → (α → α → Bool) → C
  minCmp  : C → (α → α → Bool) → Option α
  toList_sortCmp_perm : ∀ xs le, (toList (sortCmp xs le)).Perm (toList xs)
  pairwise_sortCmp    : ∀ xs le,
    (∀ a b c, le a b = true → le b c = true → le a c = true) →
    (∀ a b, (le a b || le b a) = true) →
    (toList (sortCmp xs le)).Pairwise (fun a b => le a b = true)
  minCmp_eq_list      : ∀ xs le, minCmp xs le = qedMinListBy le (toList xs)

instance {α : Type} : QedSeq (Array α) α where
  toList := Array.toList
  sortCmp xs le := (qedMergeSortList le xs.toList).toArray
  minCmp xs le := qedMinArrayBy le xs
  toList_sortCmp_perm xs le := qedMergeSortList_perm le xs.toList
  pairwise_sortCmp xs le hTr hTo := qedMergeSortList_pairwise le hTr hTo xs.toList
  minCmp_eq_list xs le := qedMinArrayBy_eq_list le xs

instance {α : Type} : QedSeq (List α) α where
  toList := id
  sortCmp xs le := qedMergeSortList le xs
  minCmp xs le := qedMinListBy le xs
  toList_sortCmp_perm xs le := qedMergeSortList_perm le xs
  pairwise_sortCmp xs le hTr hTo := qedMergeSortList_pairwise le hTr hTo xs
  minCmp_eq_list _ _ := rfl

theorem QedSeq.toList_array {α : Type} (xs : Array α) : QedSeq.toList xs = xs.toList := rfl
theorem QedSeq.toList_list  {α : Type} (xs : List α)  : QedSeq.toList xs = xs := rfl

/-! ### Key-based verified operations (`min`, `max`, `sort`, `sortDesc`, `isSorted`, `isMinOf`, `isMaxOf`) -/

@[inline] def qedSortKey {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) : C :=
  QedSeq.sortCmp xs (fun a b => QedOrd.leB (key a) (key b))

@[inline] def qedSortDescKey {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) : C :=
  qedSortKey xs (fun x => Desc (key x))

@[inline] def qedMinKey {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) : Option α :=
  QedSeq.minCmp xs (fun a b => QedOrd.leB (key a) (key b))

@[inline] def qedMaxKey {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) : Option α :=
  qedMinKey xs (fun x => Desc (key x))

def qedIsSortedKey {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) : Prop :=
  (QedSeq.toList xs).Pairwise (fun a b => QedOrd.le (key a) (key b))

def qedIsSortedDescKey {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) : Prop :=
  qedIsSortedKey xs (fun x => Desc (key x))

@[inline] def qedIsSortedKeyB {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) : Bool :=
  qedIsSortedListB (fun a b => QedOrd.leB (key a) (key b)) (QedSeq.toList xs)

@[inline] def qedIsSortedDescKeyB {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) : Bool :=
  qedIsSortedKeyB xs (fun x => Desc (key x))

def qedIsMinOfKey {C α β : Type} [QedSeq C α] [QedOrd β] (res : Option α) (xs : C) (key : α → β) : Prop :=
  (∀ b, res = some b → b ∈ QedSeq.toList xs ∧ ∀ x ∈ QedSeq.toList xs, QedOrd.le (key b) (key x)) ∧
  ((∃ x ∈ QedSeq.toList xs, True) → res.isSome = true)

def qedIsMaxOfKey {C α β : Type} [QedSeq C α] [QedOrd β] (res : Option α) (xs : C) (key : α → β) : Prop :=
  qedIsMinOfKey res xs (fun x => Desc (key x))

/-! ### Comparator-based verified operations (`(a, b) => Bool`) -/

@[inline] def qedSortCmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : C :=
  QedSeq.sortCmp xs le

@[inline] def qedSortDescCmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : C :=
  QedSeq.sortCmp xs (fun a b => le b a)

@[inline] def qedMinCmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : Option α :=
  QedSeq.minCmp xs le

@[inline] def qedMaxCmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : Option α :=
  QedSeq.minCmp xs (fun a b => le b a)

def qedIsSortedCmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : Prop :=
  (QedSeq.toList xs).Pairwise (fun a b => le a b = true)

def qedIsSortedDescCmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : Prop :=
  (QedSeq.toList xs).Pairwise (fun a b => le b a = true)

@[inline] def qedIsSortedCmpB {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : Bool :=
  qedIsSortedListB le (QedSeq.toList xs)

@[inline] def qedIsSortedDescCmpB {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : Bool :=
  qedIsSortedListB (fun a b => le b a) (QedSeq.toList xs)

def qedIsMinOfCmp {C α : Type} [QedSeq C α] (res : Option α) (xs : C) (le : α → α → Bool) : Prop :=
  (∀ b, res = some b → b ∈ QedSeq.toList xs ∧ ∀ x ∈ QedSeq.toList xs, le b x = true) ∧
  ((∃ x ∈ QedSeq.toList xs, True) → res.isSome = true)

def qedIsMaxOfCmp {C α : Type} [QedSeq C α] (res : Option α) (xs : C) (le : α → α → Bool) : Prop :=
  qedIsMinOfCmp res xs (fun a b => le b a)

/-! ### Decidability & Core Proof Lemmas (Zero Axioms) -/

theorem qedIsSortedKeyB_eq_true {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) :
    qedIsSortedKeyB xs key = true ↔ qedIsSortedKey xs key := by
  rw [qedIsSortedKeyB, qedIsSortedListB_eq_true_iff (fun a b c => QedOrd.leB_trans (key a) (key b) (key c)), qedIsSortedKey]
  exact ⟨fun h => h.imp (fun hab => (QedOrd.leB_iff _ _).1 hab), fun h => h.imp (fun hab => (QedOrd.leB_iff _ _).2 hab)⟩

theorem qedIsSortedDescKeyB_eq_true {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) :
    qedIsSortedDescKeyB xs key = true ↔ qedIsSortedDescKey xs key :=
  qedIsSortedKeyB_eq_true xs (fun x => Desc (key x))

instance {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) : Decidable (qedIsSortedKey xs key) :=
  if h : qedIsSortedKeyB xs key = true then isTrue ((qedIsSortedKeyB_eq_true xs key).1 h)
  else isFalse (fun hp => h ((qedIsSortedKeyB_eq_true xs key).2 hp))

instance {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) : Decidable (qedIsSortedDescKey xs key) :=
  inferInstanceAs (Decidable (qedIsSortedKey xs (fun x => Desc (key x))))

instance {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : Decidable (qedIsSortedCmp xs le) :=
  inferInstanceAs (Decidable ((QedSeq.toList xs).Pairwise (fun a b => le a b = true)))

instance {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : Decidable (qedIsSortedDescCmp xs le) :=
  inferInstanceAs (Decidable ((QedSeq.toList xs).Pairwise (fun a b => le b a = true)))

section OrdTheorems
variable {C α β : Type} [QedSeq C α] [QedOrd β]

theorem qedMinKey_mem {xs : C} {key : α → β} {b : α} (h : qedMinKey xs key = some b) :
    b ∈ QedSeq.toList xs := by
  rw [qedMinKey, QedSeq.minCmp_eq_list] at h; exact qedMinListBy_mem h

theorem qedMinKey_le {xs : C} {key : α → β} {b : α} (h : qedMinKey xs key = some b) :
    ∀ x ∈ QedSeq.toList xs, QedOrd.le (key b) (key x) := by
  rw [qedMinKey, QedSeq.minCmp_eq_list] at h
  intro x hx
  exact (QedOrd.leB_iff _ _).1 (qedMinListBy_le (fun a b c => QedOrd.leB_trans (key a) (key b) (key c))
    (fun a b => QedOrd.leB_total (key a) (key b)) h x hx)

theorem qedMinKey_isSome_iff (xs : C) (key : α → β) :
    (qedMinKey xs key).isSome = true ↔ ∃ x ∈ QedSeq.toList xs, True := by
  rw [qedMinKey, QedSeq.minCmp_eq_list]; exact qedMinListBy_isSome_iff _ _

theorem qedMaxKey_mem {xs : C} {key : α → β} {b : α} (h : qedMaxKey xs key = some b) :
    b ∈ QedSeq.toList xs := qedMinKey_mem h

theorem qedMaxKey_ge {xs : C} {key : α → β} {b : α} (h : qedMaxKey xs key = some b) :
    ∀ x ∈ QedSeq.toList xs, QedOrd.le (key x) (key b) := qedMinKey_le h

theorem qedMaxKey_isSome_iff (xs : C) (key : α → β) :
    (qedMaxKey xs key).isSome = true ↔ ∃ x ∈ QedSeq.toList xs, True := qedMinKey_isSome_iff xs _

theorem qedIsMinOfKey_minKey (xs : C) (key : α → β) : qedIsMinOfKey (qedMinKey xs key) xs key :=
  ⟨fun _ h => ⟨qedMinKey_mem h, qedMinKey_le h⟩, (qedMinKey_isSome_iff xs key).2⟩

theorem qedIsMaxOfKey_maxKey (xs : C) (key : α → β) : qedIsMaxOfKey (qedMaxKey xs key) xs key :=
  qedIsMinOfKey_minKey xs (fun x => Desc (key x))

theorem qedSortKey_toList_perm (xs : C) (key : α → β) :
    (QedSeq.toList (qedSortKey xs key)).Perm (QedSeq.toList xs) :=
  QedSeq.toList_sortCmp_perm xs _

theorem qedSortKey_toList_mem (xs : C) (key : α → β) (y : α) :
    y ∈ QedSeq.toList (qedSortKey xs key) ↔ y ∈ QedSeq.toList xs :=
  (qedSortKey_toList_perm xs key).mem_iff

theorem qedSortKey_toList_length (xs : C) (key : α → β) :
    (QedSeq.toList (qedSortKey xs key)).length = (QedSeq.toList xs).length :=
  (qedSortKey_toList_perm xs key).length_eq

theorem qedIsSortedKey_sortKey (xs : C) (key : α → β) : qedIsSortedKey (qedSortKey xs key) key :=
  (QedSeq.pairwise_sortCmp xs (fun a b => QedOrd.leB (key a) (key b))
    (fun a b c => QedOrd.leB_trans (key a) (key b) (key c))
    (fun a b => QedOrd.leB_total (key a) (key b))).imp (fun h => (QedOrd.leB_iff _ _).1 h)

theorem qedIsSortedDescKey_sortDescKey (xs : C) (key : α → β) : qedIsSortedDescKey (qedSortDescKey xs key) key :=
  qedIsSortedKey_sortKey xs (fun x => Desc (key x))

theorem qedIsMinOfKey_sorted_head {xs : C} {key : α → β} (hs : qedIsSortedKey xs key) :
    qedIsMinOfKey (QedSeq.toList xs)[0]? xs key := by
  unfold qedIsSortedKey at hs
  unfold qedIsMinOfKey
  cases hl : QedSeq.toList xs with
  | nil =>
      exact ⟨(fun _ h => nomatch h), (fun ⟨_, hx, _⟩ => nomatch hx)⟩
  | cons a rest =>
      rw [hl] at hs
      have ⟨hHead, _⟩ := List.pairwise_cons.1 hs
      refine ⟨fun b hb => ?_, fun _ => rfl⟩
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb; subst hb
      refine ⟨List.mem_cons_self, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hr
      · exact QedOrd.le_refl _
      · exact hHead x hr

theorem qedSortKey_head?_isMinOf (xs : C) (key : α → β) :
    qedIsMinOfKey (QedSeq.toList (qedSortKey xs key))[0]? xs key := by
  have h0 := qedIsMinOfKey_sorted_head (qedIsSortedKey_sortKey xs key)
  have hMem := qedSortKey_toList_mem xs key
  refine ⟨fun b hb => ?_, fun ⟨x, hx, _⟩ => h0.2 ⟨x, (hMem x).2 hx, trivial⟩⟩
  have ⟨hm, hle⟩ := h0.1 b hb
  exact ⟨(hMem b).1 hm, fun x hx => hle x ((hMem x).2 hx)⟩

theorem qedMinCmp_mem {xs : C} {le : α → α → Bool} {b : α} (h : qedMinCmp xs le = some b) :
    b ∈ QedSeq.toList xs := by
  rw [qedMinCmp, QedSeq.minCmp_eq_list] at h; exact qedMinListBy_mem h

theorem qedMinCmp_le {xs : C} {le : α → α → Bool} {b : α}
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true)
    (h : qedMinCmp xs le = some b) : ∀ x ∈ QedSeq.toList xs, le b x = true := by
  rw [qedMinCmp, QedSeq.minCmp_eq_list] at h; exact qedMinListBy_le hTrans hTotal h

theorem qedMinCmp_isSome_iff (xs : C) (le : α → α → Bool) :
    (qedMinCmp xs le).isSome = true ↔ ∃ x ∈ QedSeq.toList xs, True := by
  rw [qedMinCmp, QedSeq.minCmp_eq_list]; exact qedMinListBy_isSome_iff _ _

theorem qedMaxCmp_mem {xs : C} {le : α → α → Bool} {b : α} (h : qedMaxCmp xs le = some b) :
    b ∈ QedSeq.toList xs := qedMinCmp_mem (le := fun a b => le b a) h

theorem qedMaxCmp_ge {xs : C} {le : α → α → Bool} {b : α}
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true)
    (h : qedMaxCmp xs le = some b) : ∀ x ∈ QedSeq.toList xs, le x b = true :=
  qedMinCmp_le (le := fun a b => le b a) (fun a b c h1 h2 => hTrans c b a h2 h1) (fun a b => hTotal b a) h

theorem qedMaxCmp_isSome_iff (xs : C) (le : α → α → Bool) :
    (qedMaxCmp xs le).isSome = true ↔ ∃ x ∈ QedSeq.toList xs, True :=
  qedMinCmp_isSome_iff xs (fun a b => le b a)

theorem qedIsMinOfCmp_minCmp (xs : C) (le : α → α → Bool)
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true) : qedIsMinOfCmp (qedMinCmp xs le) xs le :=
  ⟨fun _ h => ⟨qedMinCmp_mem h, qedMinCmp_le hTrans hTotal h⟩, (qedMinCmp_isSome_iff xs le).2⟩

theorem qedIsMaxOfCmp_maxCmp (xs : C) (le : α → α → Bool)
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true) : qedIsMaxOfCmp (qedMaxCmp xs le) xs le :=
  qedIsMinOfCmp_minCmp xs (fun a b => le b a) (fun a b c h1 h2 => hTrans c b a h2 h1) (fun a b => hTotal b a)

theorem qedIsSortedCmp_sortCmp (xs : C) (le : α → α → Bool)
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true) : qedIsSortedCmp (qedSortCmp xs le) le :=
  QedSeq.pairwise_sortCmp xs le hTrans hTotal

theorem qedIsSortedDescCmp_sortDescCmp (xs : C) (le : α → α → Bool)
    (hTrans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (hTotal : ∀ a b, (le a b || le b a) = true) : qedIsSortedDescCmp (qedSortDescCmp xs le) le :=
  QedSeq.pairwise_sortCmp xs (fun a b => le b a) (fun a b c h1 h2 => hTrans c b a h2 h1) (fun a b => hTotal b a)

end OrdTheorems

section ConcreteSeqLemmas
variable {α β : Type} [QedOrd β]

theorem Array.mem_filter_of_size_eq {p : α → Bool} {xs : Array α} {stop : Nat} (h : xs.size = stop) {a : α} :
    a ∈ Array.filter p xs 0 stop ↔ a ∈ xs ∧ p a = true := by subst h; exact Array.mem_filter
theorem Array.toList_filter_of_size_eq {p : α → Bool} {xs : Array α} {stop : Nat} (h : xs.size = stop) :
    (Array.filter p xs 0 stop).toList = xs.toList.filter p := by subst h; exact Array.toList_filter
theorem Array.forall_mem_filter_of_size_eq {p : α → Bool} {xs : Array α} {stop : Nat} (h : xs.size = stop) {Q : α → Prop} :
    (∀ x ∈ Array.filter p xs 0 stop, Q x) ↔ ∀ x ∈ xs, p x = true → Q x := by
  subst h; simp only [Array.mem_filter, and_imp]
theorem Array.exists_mem_filter_of_size_eq {p : α → Bool} {xs : Array α} {stop : Nat} (h : xs.size = stop) {Q : α → Prop} :
    (∃ x ∈ Array.filter p xs 0 stop, Q x) ↔ ∃ x ∈ xs, p x = true ∧ Q x := by
  subst h; simp only [Array.mem_filter, and_assoc]
theorem Array.forall_mem_filter {xs : Array α} {p : α → Bool} {Q : α → Prop} :
    (∀ x ∈ xs.filter p, Q x) ↔ ∀ x ∈ xs, p x = true → Q x := by
  simp only [Array.mem_filter, and_imp]
theorem Array.exists_mem_filter {xs : Array α} {p : α → Bool} {Q : α → Prop} :
    (∃ x ∈ xs.filter p, Q x) ↔ ∃ x ∈ xs, p x = true ∧ Q x := by
  simp only [Array.mem_filter, and_assoc]
theorem List.forall_mem_filter {xs : List α} {p : α → Bool} {Q : α → Prop} :
    (∀ x ∈ xs.filter p, Q x) ↔ ∀ x ∈ xs, p x = true → Q x := by
  simp only [List.mem_filter, and_imp]
theorem List.exists_mem_filter {xs : List α} {p : α → Bool} {Q : α → Prop} :
    (∃ x ∈ xs.filter p, Q x) ↔ ∃ x ∈ xs, p x = true ∧ Q x := by
  simp only [List.mem_filter, and_assoc]
theorem Array.forall_mem_map {γ : Type} {xs : Array α} {f : α → γ} {Q : γ → Prop} :
    (∀ y ∈ xs.map f, Q y) ↔ ∀ x ∈ xs, Q (f x) := by
  simp only [Array.mem_map]; exact ⟨fun h x hx => h (f x) ⟨x, hx, rfl⟩, fun h _ ⟨x, hx, heq⟩ => heq ▸ h x hx⟩
theorem Array.exists_mem_map {γ : Type} {xs : Array α} {f : α → γ} {Q : γ → Prop} :
    (∃ y ∈ xs.map f, Q y) ↔ ∃ x ∈ xs, Q (f x) := by
  simp only [Array.mem_map]; exact ⟨fun ⟨_, ⟨x, hx, heq⟩, hq⟩ => ⟨x, hx, heq ▸ hq⟩, fun ⟨x, hx, hq⟩ => ⟨f x, ⟨x, hx, rfl⟩, hq⟩⟩
theorem List.forall_mem_map {γ : Type} {xs : List α} {f : α → γ} {Q : γ → Prop} :
    (∀ y ∈ xs.map f, Q y) ↔ ∀ x ∈ xs, Q (f x) := by
  simp only [List.mem_map]; exact ⟨fun h x hx => h (f x) ⟨x, hx, rfl⟩, fun h _ ⟨x, hx, heq⟩ => heq ▸ h x hx⟩
theorem List.exists_mem_map {γ : Type} {xs : List α} {f : α → γ} {Q : γ → Prop} :
    (∃ y ∈ xs.map f, Q y) ↔ ∃ x ∈ xs, Q (f x) := by
  simp only [List.mem_map]; exact ⟨fun ⟨_, ⟨x, hx, heq⟩, hq⟩ => ⟨x, hx, heq ▸ hq⟩, fun ⟨x, hx, hq⟩ => ⟨f x, ⟨x, hx, rfl⟩, hq⟩⟩
theorem Array.size_filter_le_self (xs : Array α) (p : α → Bool) : (xs.filter p).size ≤ xs.size :=
  Array.size_filter_le
theorem List.length_filter_le_self (xs : List α) (p : α → Bool) : (xs.filter p).length ≤ xs.length :=
  List.length_filter_le p xs

@[simp, grind =] theorem qedSortKey_array_mem (xs : Array α) (key : α → β) (y : α) :
    y ∈ qedSortKey xs key ↔ y ∈ xs := by
  simpa only [← Array.mem_toList_iff, ← QedSeq.toList_array] using qedSortKey_toList_mem xs key y
@[simp, grind =] theorem qedSortDescKey_array_mem (xs : Array α) (key : α → β) (y : α) :
    y ∈ qedSortDescKey xs key ↔ y ∈ xs := qedSortKey_array_mem xs (fun x => Desc (key x)) y
@[simp, grind =] theorem qedSortCmp_array_mem (xs : Array α) (le : α → α → Bool) (y : α) :
    y ∈ qedSortCmp xs le ↔ y ∈ xs := by
  simpa only [qedSortCmp, ← Array.mem_toList_iff, ← QedSeq.toList_array] using (QedSeq.toList_sortCmp_perm xs le).mem_iff
@[simp, grind =] theorem qedSortDescCmp_array_mem (xs : Array α) (le : α → α → Bool) (y : α) :
    y ∈ qedSortDescCmp xs le ↔ y ∈ xs := qedSortCmp_array_mem xs (fun a b => le b a) y

@[simp, grind =] theorem qedSortKey_array_size (xs : Array α) (key : α → β) :
    (qedSortKey xs key).size = xs.size := by
  simpa only [← Array.length_toList, ← QedSeq.toList_array] using qedSortKey_toList_length xs key
@[simp, grind =] theorem qedSortDescKey_array_size (xs : Array α) (key : α → β) :
    (qedSortDescKey xs key).size = xs.size := qedSortKey_array_size xs (fun x => Desc (key x))
@[simp, grind =] theorem qedSortCmp_array_size (xs : Array α) (le : α → α → Bool) :
    (qedSortCmp xs le).size = xs.size := by
  simpa only [qedSortCmp, ← Array.length_toList, ← QedSeq.toList_array] using (QedSeq.toList_sortCmp_perm xs le).length_eq
@[simp, grind =] theorem qedSortDescCmp_array_size (xs : Array α) (le : α → α → Bool) :
    (qedSortDescCmp xs le).size = xs.size := qedSortCmp_array_size xs (fun a b => le b a)

@[simp, grind =] theorem qedSortKey_list_mem (xs : List α) (key : α → β) (y : α) :
    y ∈ qedSortKey xs key ↔ y ∈ xs := qedSortKey_toList_mem xs key y
@[simp, grind =] theorem qedSortDescKey_list_mem (xs : List α) (key : α → β) (y : α) :
    y ∈ qedSortDescKey xs key ↔ y ∈ xs := qedSortKey_list_mem xs (fun x => Desc (key x)) y
@[simp, grind =] theorem qedSortCmp_list_mem (xs : List α) (le : α → α → Bool) (y : α) :
    y ∈ qedSortCmp xs le ↔ y ∈ xs := (QedSeq.toList_sortCmp_perm xs le).mem_iff
@[simp, grind =] theorem qedSortDescCmp_list_mem (xs : List α) (le : α → α → Bool) (y : α) :
    y ∈ qedSortDescCmp xs le ↔ y ∈ xs := qedSortCmp_list_mem xs (fun a b => le b a) y

@[simp, grind =] theorem qedSortKey_list_length (xs : List α) (key : α → β) :
    (qedSortKey xs key).length = xs.length := qedSortKey_toList_length xs key
@[simp, grind =] theorem qedSortDescKey_list_length (xs : List α) (key : α → β) :
    (qedSortDescKey xs key).length = xs.length := qedSortKey_list_length xs (fun x => Desc (key x))
@[simp, grind =] theorem qedSortCmp_list_length (xs : List α) (le : α → α → Bool) :
    (qedSortCmp xs le).length = xs.length := (QedSeq.toList_sortCmp_perm xs le).length_eq
@[simp, grind =] theorem qedSortDescCmp_list_length (xs : List α) (le : α → α → Bool) :
    (qedSortDescCmp xs le).length = xs.length := qedSortCmp_list_length xs (fun a b => le b a)

theorem qedSortKey_array_head?_isMinOf (xs : Array α) (key : α → β) :
    qedIsMinOfKey (qedSortKey xs key)[0]? xs key := by
  simpa only [QedSeq.toList_array, Array.getElem?_toList] using qedSortKey_head?_isMinOf xs key

theorem qedSortKey_list_head?_isMinOf (xs : List α) (key : α → β) :
    qedIsMinOfKey (qedSortKey xs key)[0]? xs key :=
  qedSortKey_head?_isMinOf xs key

@[simp, grind .] theorem qedIsSortedKey_array_empty (key : α → β) : qedIsSortedKey (#[] : Array α) key := List.Pairwise.nil
@[simp, grind .] theorem qedIsSortedKey_array_singleton (x : α) (key : α → β) : qedIsSortedKey #[x] key := List.pairwise_singleton _ _
@[simp, grind =] theorem qedIsSortedKey_array_push_iff (xs : Array α) (x : α) (key : α → β) :
    qedIsSortedKey (xs.push x) key ↔ qedIsSortedKey xs key ∧ ∀ y ∈ xs, QedOrd.le (key y) (key x) := by
  simp only [qedIsSortedKey, QedSeq.toList_array, Array.toList_push, List.pairwise_append, List.pairwise_singleton, List.mem_singleton, forall_eq, true_and, Array.mem_toList_iff]
@[grind ←] theorem qedIsSortedKey_array_filter {xs : Array α} {key : α → β} {p : α → Bool} (h : qedIsSortedKey xs key) :
    qedIsSortedKey (xs.filter p) key := h.sublist (toList_filter_sublist xs p)
theorem qedIsSortedKey_array_filter_of_size_eq {xs : Array α} {key : α → β} {p : α → Bool} {stop : Nat}
    (hs : xs.size = stop) (h : qedIsSortedKey xs key) : qedIsSortedKey (Array.filter p xs 0 stop) key := by
  subst hs; exact qedIsSortedKey_array_filter h
@[grind ←] theorem qedIsSortedKey_array_pop {xs : Array α} {key : α → β} (h : qedIsSortedKey xs key) :
    qedIsSortedKey xs.pop key := h.sublist (toList_pop_sublist xs)
@[grind ←] theorem qedIsSortedKey_array_extract {xs : Array α} {key : α → β} {s e : Nat} (h : qedIsSortedKey xs key) :
    qedIsSortedKey (xs.extract s e) key := h.sublist (toList_extract_sublist xs s e)
@[simp, grind .] theorem qedIsSortedKey_list_nil (key : α → β) : qedIsSortedKey ([] : List α) key := List.Pairwise.nil
@[simp, grind .] theorem qedIsSortedKey_list_singleton (x : α) (key : α → β) : qedIsSortedKey [x] key := List.pairwise_singleton _ _
@[grind ←] theorem qedIsSortedKey_list_filter {xs : List α} {key : α → β} {p : α → Bool} (h : qedIsSortedKey xs key) :
    qedIsSortedKey (xs.filter p) key := h.sublist List.filter_sublist

theorem qedIsSortedKey_array_getElem {xs : Array α} {key : α → β} (h : qedIsSortedKey xs key)
    {i j : Nat} (hi : i < xs.size) (hj : j < xs.size) (hij : i < j) :
    QedOrd.le (key xs[i]) (key xs[j]) := by
  have hp := (List.pairwise_iff_getElem.1 h) i j (by simpa [QedSeq.toList_array] using hi) (by simpa [QedSeq.toList_array] using hj) hij
  simpa [QedSeq.toList_array] using hp

@[simp, grind =] theorem sumBy_qedSortKey (xs : Array α) (key : α → β) (f : α → Nat) : (qedSortKey xs key).sumBy f = xs.sumBy f :=
  arraySumBy_of_perm (qedSortKey_toList_perm xs key) f
@[simp, grind =] theorem sumByInt_qedSortKey (xs : Array α) (key : α → β) (f : α → Int) : (qedSortKey xs key).sumByInt f = xs.sumByInt f :=
  arraySumBy_of_perm (qedSortKey_toList_perm xs key) f
@[simp, grind =] theorem countWhere_qedSortKey (xs : Array α) (key : α → β) (p : α → Bool) : (qedSortKey xs key).countWhere p = xs.countWhere p :=
  sumBy_qedSortKey xs key _
@[grind ←] theorem uniqueBy_qedSortKey {γ : Type} {xs : Array α} {k1 : α → γ} {key : α → β} (h : xs.uniqueBy k1) : (qedSortKey xs key).uniqueBy k1 :=
  uniqueBy_of_perm (qedSortKey_toList_perm xs key).symm h
@[simp] theorem qedMinKey_array_eq (xs : Array α) (key : α → β) :
    qedMinKey xs key = qedMinListBy (fun a b => QedOrd.leB (key a) (key b)) xs.toList := qedMinArrayBy_eq_list _ xs
@[simp] theorem qedMinKey_list_eq (xs : List α) (key : α → β) :
    qedMinKey xs key = qedMinListBy (fun a b => QedOrd.leB (key a) (key b)) xs := rfl
@[simp] theorem qedMaxKey_array_eq (xs : Array α) (key : α → β) :
    qedMaxKey xs key = qedMinListBy (fun a b => QedOrd.leB (key b) (key a)) xs.toList := qedMinArrayBy_eq_list _ xs
@[simp] theorem qedMaxKey_list_eq (xs : List α) (key : α → β) :
    qedMaxKey xs key = qedMinListBy (fun a b => QedOrd.leB (key b) (key a)) xs := rfl
@[grind ←] theorem qedIsSortedDescKey_array_filter {xs : Array α} {key : α → β} {p : α → Bool} (h : qedIsSortedDescKey xs key) :
    qedIsSortedDescKey (xs.filter p) key := qedIsSortedKey_array_filter h
theorem qedIsSortedDescKey_array_filter_of_size_eq {xs : Array α} {key : α → β} {p : α → Bool} {stop : Nat}
    (hs : xs.size = stop) (h : qedIsSortedDescKey xs key) : qedIsSortedDescKey (Array.filter p xs 0 stop) key :=
  qedIsSortedKey_array_filter_of_size_eq hs h
@[grind ←] theorem qedIsSortedDescKey_list_filter {xs : List α} {key : α → β} {p : α → Bool} (h : qedIsSortedDescKey xs key) :
    qedIsSortedDescKey (xs.filter p) key := qedIsSortedKey_list_filter h

end ConcreteSeqLemmas

/-! ### Type-Directed Dispatch for Named Key/Comparator Functions & Scalar `min`/`max` -/

/-- Dispatches 2-arg free `min(a, b)`: scalar `Min.min`, key-function `qedMinKey`, or 2-arg comparator `qedMinCmp`. -/
class QedMin2 (α β : Type) (γ : outParam Type) where
  run : α → β → γ

@[reducible, inline] instance (priority := high) {C α β : Type} [QedSeq C α] [QedOrd β] : QedMin2 C (α → β) (Option α) := ⟨qedMinKey⟩
@[reducible, inline] instance (priority := high) {C α : Type} [QedSeq C α] : QedMin2 C (α → α → Bool) (Option α) := ⟨qedMinCmp⟩
@[reducible, inline] instance {α : Type} [Min α] : QedMin2 α α α := ⟨Min.min⟩

/-- Dispatches 2-arg free `max(a, b)`: scalar `Max.max`, key-function `qedMaxKey`, or 2-arg comparator `qedMaxCmp`. -/
class QedMax2 (α β : Type) (γ : outParam Type) where
  run : α → β → γ

@[reducible, inline] instance (priority := high) {C α β : Type} [QedSeq C α] [QedOrd β] : QedMax2 C (α → β) (Option α) := ⟨qedMaxKey⟩
@[reducible, inline] instance (priority := high) {C α : Type} [QedSeq C α] : QedMax2 C (α → α → Bool) (Option α) := ⟨qedMaxCmp⟩
@[reducible, inline] instance {α : Type} [Max α] : QedMax2 α α α := ⟨Max.max⟩

/-- Dispatches non-lambda key/comparator arguments (`scoreOf : α → β` vs `cmp : α → α → Bool`) across all order ops. -/
class QedOrdArg (C : Type) (α : outParam Type) (F : Type) where
  sortFn          : C → F → C
  sortDescFn      : C → F → C
  minFn           : C → F → Option α
  maxFn           : C → F → Option α
  isSortedFn      : C → F → Prop
  isSortedDescFn  : C → F → Prop
  isSortedBFn     : C → F → Bool
  isSortedDescBFn : C → F → Bool
  isMinOfFn       : Option α → C → F → Prop
  isMaxOfFn       : Option α → C → F → Prop

@[reducible, inline] instance {C α β : Type} [QedSeq C α] [QedOrd β] : QedOrdArg C α (α → β) where
  sortFn := qedSortKey
  sortDescFn := qedSortDescKey
  minFn := qedMinKey
  maxFn := qedMaxKey
  isSortedFn := qedIsSortedKey
  isSortedDescFn := qedIsSortedDescKey
  isSortedBFn := qedIsSortedKeyB
  isSortedDescBFn := qedIsSortedDescKeyB
  isMinOfFn := qedIsMinOfKey
  isMaxOfFn := qedIsMaxOfKey

@[reducible, inline] instance {C α : Type} [QedSeq C α] : QedOrdArg C α (α → α → Bool) where
  sortFn := qedSortCmp
  sortDescFn := qedSortDescCmp
  minFn := qedMinCmp
  maxFn := qedMaxCmp
  isSortedFn := qedIsSortedCmp
  isSortedDescFn := qedIsSortedDescCmp
  isSortedBFn := qedIsSortedCmpB
  isSortedDescBFn := qedIsSortedDescCmpB
  isMinOfFn := qedIsMinOfCmp
  isMaxOfFn := qedIsMaxOfCmp

@[simp] theorem QedMin2.run_scalar {α : Type} [Min α] (a b : α) : QedMin2.run a b = Min.min a b := rfl
@[simp] theorem QedMin2.run_key {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) : QedMin2.run xs key = qedMinKey xs key := rfl
@[simp] theorem QedMin2.run_cmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : QedMin2.run xs le = qedMinCmp xs le := rfl
@[simp] theorem QedMax2.run_scalar {α : Type} [Max α] (a b : α) : QedMax2.run a b = Max.max a b := rfl
@[simp] theorem QedMax2.run_key {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (key : α → β) : QedMax2.run xs key = qedMaxKey xs key := rfl
@[simp] theorem QedMax2.run_cmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : QedMax2.run xs le = qedMaxCmp xs le := rfl
@[simp] theorem QedOrdArg.sortFn_key {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (k : α → β) : QedOrdArg.sortFn xs k = qedSortKey xs k := rfl
@[simp] theorem QedOrdArg.sortFn_cmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : QedOrdArg.sortFn xs le = qedSortCmp xs le := rfl
@[simp] theorem QedOrdArg.sortDescFn_key {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (k : α → β) : QedOrdArg.sortDescFn xs k = qedSortDescKey xs k := rfl
@[simp] theorem QedOrdArg.sortDescFn_cmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : QedOrdArg.sortDescFn xs le = qedSortDescCmp xs le := rfl
@[simp] theorem QedOrdArg.minFn_key {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (k : α → β) : QedOrdArg.minFn xs k = qedMinKey xs k := rfl
@[simp] theorem QedOrdArg.minFn_cmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : QedOrdArg.minFn xs le = qedMinCmp xs le := rfl
@[simp] theorem QedOrdArg.maxFn_key {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (k : α → β) : QedOrdArg.maxFn xs k = qedMaxKey xs k := rfl
@[simp] theorem QedOrdArg.maxFn_cmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : QedOrdArg.maxFn xs le = qedMaxCmp xs le := rfl
@[simp] theorem QedOrdArg.isSortedFn_key {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (k : α → β) : QedOrdArg.isSortedFn xs k = qedIsSortedKey xs k := rfl
@[simp] theorem QedOrdArg.isSortedFn_cmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : QedOrdArg.isSortedFn xs le = qedIsSortedCmp xs le := rfl
@[simp] theorem QedOrdArg.isSortedDescFn_key {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (k : α → β) : QedOrdArg.isSortedDescFn xs k = qedIsSortedDescKey xs k := rfl
@[simp] theorem QedOrdArg.isSortedDescFn_cmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : QedOrdArg.isSortedDescFn xs le = qedIsSortedDescCmp xs le := rfl
@[simp] theorem QedOrdArg.isSortedBFn_key {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (k : α → β) : QedOrdArg.isSortedBFn xs k = qedIsSortedKeyB xs k := rfl
@[simp] theorem QedOrdArg.isSortedBFn_cmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : QedOrdArg.isSortedBFn xs le = qedIsSortedCmpB xs le := rfl
@[simp] theorem QedOrdArg.isSortedDescBFn_key {C α β : Type} [QedSeq C α] [QedOrd β] (xs : C) (k : α → β) : QedOrdArg.isSortedDescBFn xs k = qedIsSortedDescKeyB xs k := rfl
@[simp] theorem QedOrdArg.isSortedDescBFn_cmp {C α : Type} [QedSeq C α] (xs : C) (le : α → α → Bool) : QedOrdArg.isSortedDescBFn xs le = qedIsSortedDescCmpB xs le := rfl
@[simp] theorem QedOrdArg.isMinOfFn_key {C α β : Type} [QedSeq C α] [QedOrd β] (r : Option α) (xs : C) (k : α → β) : QedOrdArg.isMinOfFn r xs k = qedIsMinOfKey r xs k := rfl
@[simp] theorem QedOrdArg.isMinOfFn_cmp {C α : Type} [QedSeq C α] (r : Option α) (xs : C) (le : α → α → Bool) : QedOrdArg.isMinOfFn r xs le = qedIsMinOfCmp r xs le := rfl
@[simp] theorem QedOrdArg.isMaxOfFn_key {C α β : Type} [QedSeq C α] [QedOrd β] (r : Option α) (xs : C) (k : α → β) : QedOrdArg.isMaxOfFn r xs k = qedIsMaxOfKey r xs k := rfl
@[simp] theorem QedOrdArg.isMaxOfFn_cmp {C α : Type} [QedSeq C α] (r : Option α) (xs : C) (le : α → α → Bool) : QedOrdArg.isMaxOfFn r xs le = qedIsMaxOfCmp r xs le := rfl

namespace ForEach
theorem forall_qedSortKey {α β : Type} [QedOrd β] {P : α → Prop} {a : Array α} {key : α → β}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ qedSortKey a key, P y := fun y hy => h y ((qedSortKey_array_mem a key y).1 hy)
theorem forall_qedSortDescKey {α β : Type} [QedOrd β] {P : α → Prop} {a : Array α} {key : α → β}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ qedSortDescKey a key, P y := fun y hy => h y ((qedSortDescKey_array_mem a key y).1 hy)
theorem forall_qedSortCmp {α : Type} {P : α → Prop} {a : Array α} {le : α → α → Bool}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ qedSortCmp a le, P y := fun y hy => h y ((qedSortCmp_array_mem a le y).1 hy)
theorem forall_qedSortDescCmp {α : Type} {P : α → Prop} {a : Array α} {le : α → α → Bool}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ qedSortDescCmp a le, P y := fun y hy => h y ((qedSortDescCmp_array_mem a le y).1 hy)
end ForEach

namespace ForEach
variable {α : Type} {P : α → Prop}

theorem forall_map {a : Array α} {g : α → α} (hg : ∀ y ∈ a, P (g y)) : ∀ y ∈ a.map g, P y := by
  intro y hy; obtain ⟨x, hx, rfl⟩ := Array.mem_map.1 hy; exact hg x hx
theorem updateKeyed_forall {Msg} (c : Component α Msg) (key : α → String) (hc : ∀ r m, P r → P (c.update r m))
    {a : Array α} {k : String} {msg : Msg} (h : ∀ y ∈ a, P y) : ∀ y ∈ Component.updateKeyed c key a k msg, P y :=
  forall_map fun x hx => by split; exact hc x msg (h x hx); exact h x hx

variable {a : Array α}
theorem forall_push {x : α} (h : ∀ y ∈ a, P y) (hx : P x) : ∀ y ∈ a.push x, P y := by simpa only [Array.mem_push, or_imp, forall_and, forall_eq] using And.intro h hx
theorem forall_filter {f : α → Bool} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.filter f, P y := fun y hy => h y (Array.mem_filter.1 hy).1
theorem forall_sortBy {le : α → α → Bool} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.sortBy le, P y := fun y hy => h y (Array.mem_mergeSort.1 hy)
theorem forall_append {b : Array α} (ha : ∀ y ∈ a, P y) (hb : ∀ y ∈ b, P y) : ∀ y ∈ a ++ b, P y := fun y hy => (Array.mem_append.1 hy).elim (ha y) (hb y)
theorem forall_pop (h : ∀ y ∈ a, P y) : ∀ y ∈ a.pop, P y := fun _ hy => h _ (array_mem_of_mem_pop hy)
theorem forall_reverse (h : ∀ y ∈ a, P y) : ∀ y ∈ a.reverse, P y := fun _ hy => h _ (Array.mem_reverse.1 hy)
theorem forall_extract {start stop : Nat} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.extract start stop, P y := fun _ hy => h _ (array_mem_of_mem_extract hy)
theorem forall_eraseIdx {i : Nat} {hi : i < a.size} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.eraseIdx i hi, P y := fun _ hy => h _ (Array.mem_of_mem_eraseIdx hy)
theorem forall_eraseIdxIfInBounds {i : Nat} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.eraseIdxIfInBounds i, P y := by unfold Array.eraseIdxIfInBounds; split; exact forall_eraseIdx h; exact h
theorem forall_set {i : Nat} {x : α} {hi : i < a.size} (h : ∀ y ∈ a, P y) (hx : P x) : ∀ y ∈ a.set i x hi, P y := Array.forall_set hi h hx
theorem forall_setIfInBounds {i : Nat} {x : α} (h : ∀ y ∈ a, P y) (hx : P x) : ∀ y ∈ a.setIfInBounds i x, P y := by unfold Array.setIfInBounds; split; exact forall_set h hx; exact h
theorem forall_swap {i j : Nat} {hi : i < a.size} {hj : j < a.size} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.swap i j hi hj, P y := fun _ hy => h _ (array_mem_of_mem_swap hy)
theorem forall_swapIfInBounds {i j : Nat} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.swapIfInBounds i j, P y := by unfold Array.swapIfInBounds; split <;> (try split) <;> first | exact forall_swap h | exact h
theorem forall_modify {i : Nat} {f : α → α} (h : ∀ y ∈ a, P y) (hf : ∀ y ∈ a, P y → P (f y)) : ∀ y ∈ a.modify i f, P y := by
  have hMod : a.modify i f = if hi : i < a.size then a.set i (f a[i]) hi else a := by simp [Array.modify, Array.modifyM]; split <;> rfl
  rw [hMod]; split; next hi => exact forall_set h (hf _ (Array.getElem_mem hi) (h _ (Array.getElem_mem hi)))
  exact h

end ForEach

end Qed
