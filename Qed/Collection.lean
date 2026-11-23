namespace Qed

def _root_.Array.findIndex {α : Type} (xs : Array α) (p : α → Bool) : Option (Fin xs.size) := Array.findFinIdx? p xs
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
@[grind →] theorem array_mem_of_mem_pop {xs : Array α} {x : α} (h : x ∈ xs.pop) : x ∈ xs := Array.mem_def.2 ((toList_pop_sublist xs).subset (Array.mem_def.1 h))
@[grind →] theorem array_mem_of_mem_eraseIdx {xs : Array α} {i : Nat} {hi : i < xs.size} {x : α} (h : x ∈ xs.eraseIdx i hi) : x ∈ xs := Array.mem_of_mem_eraseIdx h
@[grind →] theorem array_mem_of_mem_extract {xs : Array α} {start stop : Nat} {x : α} (h : x ∈ xs.extract start stop) : x ∈ xs := Array.mem_def.2 ((toList_extract_sublist xs start stop).subset (Array.mem_def.1 h))
@[grind →] theorem array_mem_of_mem_swap {xs : Array α} {i j : Nat} {hi : i < xs.size} {hj : j < xs.size} {x : α} (h : x ∈ xs.swap i j hi hj) : x ∈ xs :=
  Array.forall_set (by simp [hj]) (Array.forall_set hi (fun _ => id) (Array.getElem_mem hj)) (Array.getElem_mem hi) x h
end SublistMem

section GenericSum
variable {β : Type} [Add β] [Zero β] [Std.Associative (α := β) (· + ·)]
private theorem foldl_add_eq_sum [Std.LawfulIdentity (α := β) (· + ·) 0] {α : Type} (f : α → β) :
    ∀ (l : List α) (init : β), l.foldl (fun acc x => acc + f x) init = init + (l.map f).sum
  | [], _ => by simp [Std.LawfulRightIdentity.right_id]
  | _ :: xs, _ => by simp only [List.foldl_cons, List.map_cons, List.sum_cons, foldl_add_eq_sum f xs, Std.Associative.assoc]
private theorem foldl_sum_eq [Std.LawfulIdentity (α := β) (· + ·) 0] {α : Type} (xs : Array α) (f : α → β) :
    xs.foldl (fun acc x => acc + f x) 0 = (xs.toList.map f).sum := by rw [← Array.foldl_toList, foldl_add_eq_sum]; exact Std.LawfulLeftIdentity.left_id _
private theorem list_sum_perm [Std.Commutative (α := β) (· + ·)] {a b : List β} (h : a.Perm b) : a.sum = b.sum := by
  induction h with | nil => rfl | cons _ _ ih => simp only [List.sum_cons, ih] | swap _ _ _ => simp only [List.sum_cons]; ac_rfl | trans _ _ ih1 ih2 => exact ih1.trans ih2
private theorem list_sum_map_set [Std.Commutative (α := β) (· + ·)] {α : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat) (x : α) (h : i < l.length), ((l.set i x).map f).sum + f l[i] = (l.map f).sum + f x
  | [], _, _, h => nomatch h | _ :: _, 0, _, _ => by simp only [List.set_cons_zero, List.map_cons, List.sum_cons, List.getElem_cons_zero]; ac_rfl
  | _ :: ys, i + 1, x, h => by simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ, Std.Associative.assoc, list_sum_map_set f ys i x (by simpa using h)]
private theorem list_sum_map_eraseIdx [Std.Commutative (α := β) (· + ·)] {α : Type} (f : α → β) :
    ∀ (l : List α) (i : Nat) (h : i < l.length), ((l.eraseIdx i).map f).sum + f l[i] = (l.map f).sum
  | [], _, h => nomatch h | _ :: _, 0, _ => by simp only [List.eraseIdx_zero, List.tail_cons, List.map_cons, List.sum_cons, List.getElem_cons_zero]; exact Std.Commutative.comm (op := (· + ·)) _ _
  | _ :: ys, i + 1, h => by simp only [List.eraseIdx_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ, Std.Associative.assoc, list_sum_map_eraseIdx f ys i (by simpa using h)]
end GenericSum

private theorem list_sum_nat_sublist {a b : List Nat} (h : a.Sublist b) : a.sum ≤ b.sum := by induction h <;> simp <;> omega
private theorem list_sum_nat_le_length_mul {α : Type} (f : α → Nat) (bound : Nat) : ∀ {l : List α}, (∀ x ∈ l, f x ≤ bound) → (l.map f).sum ≤ l.length * bound
  | [], _ => by simp
  | x :: xs, h => by have := h x (by simp); have := list_sum_nat_le_length_mul f bound (l := xs) fun y hy => h y (by simp [hy]); simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]; omega

def _root_.Array.sumBy {α : Type} (xs : Array α) (f : α → Nat) : Nat := xs.foldl (fun acc x => acc + f x) 0
def _root_.Array.sumByInt {α : Type} (xs : Array α) (f : α → Int) : Int := xs.foldl (fun acc x => acc + f x) 0
private theorem sumBy_of_sublist {α : Type} {xs ys : Array α} (f : α → Nat) (hsub : ys.toList.Sublist xs.toList) : ys.sumBy f ≤ xs.sumBy f := by
  rw [Array.sumBy, Array.sumBy, foldl_sum_eq, foldl_sum_eq]; exact list_sum_nat_sublist (hsub.map f)

local macro "def_array_sum_lemmas " fn:ident ty:term : command => do
  let suf (s : String) := Lean.mkIdentFrom fn (fn.getId.appendAfter s)
  let hEmpty := suf "_empty"; let hAppend := suf "_append"; let hMap := suf "_map"
  let hRev := suf "_reverse"; let hSort := suf "_mergeSort"; let hErase := suf "_eraseIdx"
  `(@[simp, grind =] theorem $hEmpty {α : Type} (f : α → $ty) : $fn (#[] : Array α) f = 0 := rfl
    @[simp, grind =] theorem $hAppend {α : Type} (xs ys : Array α) (f : α → $ty) : $fn (xs ++ ys) f = $fn xs f + $fn ys f := by rw [$fn:ident, $fn:ident, $fn:ident, foldl_sum_eq, foldl_sum_eq, foldl_sum_eq]; simp
    @[simp, grind =] theorem $hMap {α β : Type} (xs : Array α) (g : α → β) (f : β → $ty) : $fn (xs.map g) f = $fn xs (fun x => f (g x)) := by rw [$fn:ident, $fn:ident, foldl_sum_eq, foldl_sum_eq]; simp [List.map_map, Function.comp_def]
    @[simp, grind =] theorem $hRev {α : Type} (xs : Array α) (f : α → $ty) : $fn xs.reverse f = $fn xs f := by rw [$fn:ident, $fn:ident, foldl_sum_eq, foldl_sum_eq]; simp
    @[simp, grind =] theorem $hSort {α : Type} (xs : Array α) (le : α → α → Bool) (f : α → $ty) : $fn (xs.mergeSort le) f = $fn xs f := by rw [$fn:ident, $fn:ident, foldl_sum_eq, foldl_sum_eq]; exact list_sum_perm ((Array.perm_iff_toList_perm.1 (Array.mergeSort_perm (xs := xs) (le := le))).map f)
    @[grind =] theorem $hErase {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) (f : α → $ty) : $fn (xs.eraseIdx i h) f + f xs[i] = $fn xs f := by rw [$fn:ident, $fn:ident, foldl_sum_eq, foldl_sum_eq, Array.toList_eraseIdx]; exact list_sum_map_eraseIdx f xs.toList i h)

def_array_sum_lemmas _root_.Array.sumBy Nat
def_array_sum_lemmas _root_.Array.sumByInt Int

section SumCount
variable {α : Type}
@[simp, grind =] theorem _root_.Array.sumBy_push (xs : Array α) (f : α → Nat) (v : α) : (xs.push v).sumBy f = xs.sumBy f + f v := by simp [Array.sumBy, foldl_sum_eq]
@[grind <=] theorem _root_.Array.sumBy_filter_le (xs : Array α) (p : α → Bool) (f : α → Nat) : (xs.filter p).sumBy f ≤ xs.sumBy f := sumBy_of_sublist f (toList_filter_sublist xs p)
@[grind <=] theorem _root_.Array.sumBy_pop_le (xs : Array α) (f : α → Nat) : xs.pop.sumBy f ≤ xs.sumBy f := sumBy_of_sublist f (toList_pop_sublist xs)
@[grind <=] theorem _root_.Array.sumBy_extract_le (xs : Array α) (start stop : Nat) (f : α → Nat) : (xs.extract start stop).sumBy f ≤ xs.sumBy f := sumBy_of_sublist f (toList_extract_sublist xs start stop)
@[grind =] theorem _root_.Array.sumBy_set (xs : Array α) (f : α → Nat) (i : Nat) (v : α) (h : i < xs.size) : (xs.set i v h).sumBy f + f xs[i] = xs.sumBy f + f v := by rw [Array.sumBy, Array.sumBy, foldl_sum_eq, foldl_sum_eq, Array.toList_set]; exact list_sum_map_set f xs.toList i v h
theorem _root_.Array.sumBy_le_size_mul {xs : Array α} (f : α → Nat) (bound : Nat) (h : ∀ x ∈ xs, f x ≤ bound) : xs.sumBy f ≤ xs.size * bound := by rw [Array.sumBy, foldl_sum_eq, ← Array.length_toList]; exact list_sum_nat_le_length_mul f bound fun y hy => h y (Array.mem_toList_iff.1 hy)

@[simp, grind =] theorem _root_.Array.sumByInt_push (xs : Array α) (x : α) (f : α → Int) : (xs.push x).sumByInt f = xs.sumByInt f + f x := by simp [Array.sumByInt, foldl_sum_eq]
@[grind =] theorem _root_.Array.sumByInt_set (xs : Array α) (i : Nat) (x : α) (h : i < xs.size) (f : α → Int) : (xs.set i x h).sumByInt f + f xs[i] = xs.sumByInt f + f x := by rw [Array.sumByInt, Array.sumByInt, foldl_sum_eq, foldl_sum_eq, Array.toList_set]; exact list_sum_map_set f xs.toList i x h

def _root_.Array.countWhere (xs : Array α) (p : α → Bool) : Nat := xs.sumBy fun x => if p x then 1 else 0
@[simp, grind =] theorem _root_.Array.countWhere_empty (p : α → Bool) : (#[] : Array α).countWhere p = 0 := rfl
@[simp, grind =] theorem _root_.Array.countWhere_push (xs : Array α) (x : α) (p : α → Bool) : (xs.push x).countWhere p = xs.countWhere p + (if p x then 1 else 0) := Array.sumBy_push xs _ x
@[simp, grind =] theorem _root_.Array.countWhere_append (xs ys : Array α) (p : α → Bool) : (xs ++ ys).countWhere p = xs.countWhere p + ys.countWhere p := Array.sumBy_append xs ys _
@[simp, grind =] theorem _root_.Array.countWhere_reverse (xs : Array α) (p : α → Bool) : xs.reverse.countWhere p = xs.countWhere p := Array.sumBy_reverse xs _
@[simp, grind =] theorem _root_.Array.countWhere_mergeSort (xs : Array α) (le : α → α → Bool) (p : α → Bool) : (xs.mergeSort le).countWhere p = xs.countWhere p := Array.sumBy_mergeSort xs le _
@[grind <=] theorem _root_.Array.countWhere_le_size (xs : Array α) (p : α → Bool) : xs.countWhere p ≤ xs.size := by simpa [Array.countWhere] using Array.sumBy_le_size_mul (xs := xs) (fun x => if p x then 1 else 0) 1 fun x _ => by dsimp only; split <;> omega
@[grind <=] theorem _root_.Array.countWhere_filter_le (xs : Array α) (q p : α → Bool) : (xs.filter q).countWhere p ≤ xs.countWhere p := Array.sumBy_filter_le xs q _
@[grind <=] theorem _root_.Array.countWhere_pop_le (xs : Array α) (p : α → Bool) : xs.pop.countWhere p ≤ xs.countWhere p := Array.sumBy_pop_le xs _
@[grind =] theorem _root_.Array.countWhere_set (xs : Array α) (i : Nat) (x : α) (h : i < xs.size) (p : α → Bool) : (xs.set i x h).countWhere p + (if p xs[i] then 1 else 0) = xs.countWhere p + (if p x then 1 else 0) := Array.sumBy_set xs _ i x h
@[grind =] theorem _root_.Array.countWhere_eraseIdx (xs : Array α) (i : Nat) (h : i < xs.size) (p : α → Bool) : (xs.eraseIdx i h).countWhere p + (if p xs[i] then 1 else 0) = xs.countWhere p := Array.sumBy_eraseIdx xs i h _
end SumCount

def _root_.Array.uniqueBy {α β : Type} (xs : Array α) (key : α → β) : Prop := (xs.toList.map key).Nodup
instance {α β : Type} [DecidableEq β] (xs : Array α) (key : α → β) : Decidable (xs.uniqueBy key) := inferInstanceAs (Decidable (xs.toList.map key).Nodup)
@[simp, grind .] theorem _root_.Array.uniqueBy_empty {α β : Type} (key : α → β) : (#[] : Array α).uniqueBy key := by simp [Array.uniqueBy]
@[simp, grind =] theorem _root_.Array.uniqueBy_push_iff {α β : Type} (xs : Array α) (x : α) (key : α → β) :
    (xs.push x).uniqueBy key ↔ xs.uniqueBy key ∧ ∀ y ∈ xs, key y ≠ key x := by
  simp only [Array.uniqueBy, Array.toList_push, List.map_append, List.map_cons, List.map_nil, List.nodup_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, true_and, List.mem_cons, List.mem_map, Array.mem_toList_iff]
  exact ⟨fun ⟨h, d⟩ => ⟨h, fun y hy e => d _ ⟨y, hy, rfl⟩ _ (.inl rfl) e⟩, fun ⟨h, n⟩ => ⟨h, fun _ ⟨y, hy, he⟩ _ hk e => hk.elim (fun h' => n y hy ((he.trans e).trans h')) False.elim⟩⟩

local macro "def_sublist_pres " fn:ident " {" ts:ident* "} " keyTy:term " by " ofSub:term : command => do
  let suf (s : String) := Lean.mkIdentFrom fn (fn.getId.appendAfter s)
  let hF := suf "_filter"; let hP := suf "_pop"; let hE := suf "_eraseIdx"; let hX := suf "_extract"
  `(@[grind ←] theorem $hF {α $ts:ident* : Type} {xs : Array α} {key : α → $keyTy} {p : α → Bool} (h : $fn xs key) : $fn (xs.filter p) key := $ofSub (toList_filter_sublist xs p) h
    @[grind ←] theorem $hP {α $ts:ident* : Type} {xs : Array α} {key : α → $keyTy} (h : $fn xs key) : $fn xs.pop key := $ofSub (toList_pop_sublist xs) h
    @[grind ←] theorem $hE {α $ts:ident* : Type} {xs : Array α} {key : α → $keyTy} {i : Nat} {hi : i < xs.size} (h : $fn xs key) : $fn (xs.eraseIdx i hi) key := $ofSub (toList_eraseIdx_sublist xs i hi) h
    @[grind ←] theorem $hX {α $ts:ident* : Type} {xs : Array α} {key : α → $keyTy} {start stop : Nat} (h : $fn xs key) : $fn (xs.extract start stop) key := $ofSub (toList_extract_sublist xs start stop) h)

def_sublist_pres _root_.Array.uniqueBy {β} β by (fun hsub h => h.sublist (hsub.map _))
@[grind ←] theorem _root_.Array.uniqueBy_reverse {α β : Type} {xs : Array α} {key : α → β} (h : xs.uniqueBy key) : xs.reverse.uniqueBy key := by simp only [Array.uniqueBy, Array.toList_reverse, List.map_reverse]; exact (List.reverse_perm _).nodup_iff.2 h
@[grind ←] theorem _root_.Array.uniqueBy_mergeSort {α β : Type} {xs : Array α} {key : α → β} {le : α → α → Bool} (h : xs.uniqueBy key) : (xs.mergeSort le).uniqueBy key := (((Array.perm_iff_toList_perm.1 (Array.mergeSort_perm (xs := xs) (le := le))).map key).nodup_iff).2 h
@[grind ←] theorem _root_.Array.uniqueBy_map_same_key {α β : Type} {xs : Array α} {key : α → β} {g : α → α} (hKey : ∀ y ∈ xs, key (g y) = key y) (h : xs.uniqueBy key) : (xs.map g).uniqueBy key := by
  simp only [Array.uniqueBy, Array.toList_map, List.map_map, Function.comp_def]; rwa [List.map_congr_left fun y hy => hKey y (Array.mem_toList_iff.1 hy)]

def _root_.Array.isSortedBy {α : Type} (xs : Array α) (key : α → Nat) : Prop := xs.toList.Pairwise (fun a b => key a ≤ key b)
instance {α : Type} (xs : Array α) (key : α → Nat) : Decidable (xs.isSortedBy key) := inferInstanceAs (Decidable (xs.toList.Pairwise (fun a b => key a ≤ key b)))
@[simp, grind .] theorem _root_.Array.isSortedBy_empty {α : Type} (key : α → Nat) : (#[] : Array α).isSortedBy key := by simp [Array.isSortedBy]
@[simp, grind .] theorem _root_.Array.isSortedBy_singleton {α : Type} (x : α) (key : α → Nat) : #[x].isSortedBy key := by simp [Array.isSortedBy]
@[simp, grind =] theorem _root_.Array.isSortedBy_push_iff {α : Type} (xs : Array α) (x : α) (key : α → Nat) : (xs.push x).isSortedBy key ↔ xs.isSortedBy key ∧ ∀ y ∈ xs, key y ≤ key x := by
  simp only [Array.isSortedBy, Array.toList_push, List.pairwise_append, List.pairwise_singleton, List.mem_singleton, forall_eq, true_and, Array.mem_toList_iff]
def_sublist_pres _root_.Array.isSortedBy {} Nat by (fun hsub h => h.sublist hsub)
@[grind .] theorem _root_.Array.isSortedBy_mergeSort_le {α : Type} (xs : Array α) (key : α → Nat) : (xs.mergeSort (fun a b => decide (key a ≤ key b))).isSortedBy key :=
  (Array.pairwise_mergeSort (xs := xs) (le := fun a b => decide (key a ≤ key b))
    (trans := fun _ _ _ hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (total := fun a b => by by_cases h : key a ≤ key b <;> simp [h] <;> omega)).imp fun hab => by simpa using hab

macro "qedNonlinearClose" : tactic => `(tactic| first
  | (apply Nat.mul_le_mul <;> omega) | (apply Nat.mul_le_mul_left <;> omega) | (apply Nat.mul_le_mul_right <;> omega)
  | (apply Nat.mul_lt_mul_of_pos_left <;> omega) | (apply Nat.mul_lt_mul_of_pos_right <;> omega) | (apply Nat.div_le_div_right; omega)
  | (exact Nat.le_trans (Nat.div_le_self _ _) (by omega)) | (exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))
  | (apply Int.mul_nonneg <;> omega) | (apply Int.mul_le_mul_of_nonneg_left <;> omega)
  | (apply Int.mul_le_mul_of_nonneg_right <;> omega) | (apply Int.mul_le_mul <;> omega))

end Qed
