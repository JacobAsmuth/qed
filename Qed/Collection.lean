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
