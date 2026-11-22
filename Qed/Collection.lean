namespace Qed

/-! ## Safe Array Indexing, Membership & Collection Queries

Total helpers (`findIndex`, `sumBy`, `sumByInt`, `countWhere`, `uniqueBy`, `isSortedBy`) backed by
`@[simp, grind]` preservation lemmas so aggregate, count, uniqueness, and ordering invariants
prove automatically without `:= by`. -/

def _root_.Array.findIndex {α : Type} (xs : Array α) (p : α → Bool) : Option (Fin xs.size) :=
  Array.findFinIdx? p xs

@[simp] theorem _root_.Array.forall_push {α : Type} {P : α → Prop} {xs : Array α} {v : α} :
    (∀ x ∈ xs.push v, P x) ↔ (∀ x ∈ xs, P x) ∧ P v := by
  constructor
  · intro h; exact ⟨fun x hx => h x (Array.mem_push.2 (.inl hx)), h v (Array.mem_push.2 (.inr rfl))⟩
  · rintro ⟨hxs, hv⟩ x hx; rcases Array.mem_push.1 hx with hm | rfl; exact hxs x hm; exact hv

theorem _root_.Array.forall_set {α : Type u} {P : α → Prop} {xs : Array α} {i : Nat} {v : α}
    (h : i < xs.size) (hxs : ∀ x ∈ xs, P x) (hv : P v) :
    ∀ x ∈ xs.set i v h, P x := by
  intro x hx; rw [Array.mem_def, Array.toList_set] at hx
  rcases List.mem_or_eq_of_mem_set hx with hm | rfl; exact hxs x (Array.mem_def.2 hm); exact hv

theorem _root_.Array.forall_elem {α : Type u} {P : α → Prop} {xs : Array α} {i : Nat}
    (h : i < xs.size) (hxs : ∀ x ∈ xs, P x) : P xs[i] :=
  hxs xs[i] (Array.getElem_mem h)

private theorem toList_filter_sublist {α : Type u} (xs : Array α) (p : α → Bool) :
    (xs.filter p).toList.Sublist xs.toList := by rw [Array.toList_filter]; exact List.filter_sublist

private theorem toList_pop_sublist {α : Type u} (xs : Array α) :
    xs.pop.toList.Sublist xs.toList := by rw [Array.toList_pop]; exact List.dropLast_sublist _

private theorem toList_eraseIdx_sublist {α : Type u} (xs : Array α) (i : Nat) (hi : i < xs.size) :
    (xs.eraseIdx i hi).toList.Sublist xs.toList := by rw [Array.toList_eraseIdx]; exact List.eraseIdx_sublist _ _

private theorem toList_extract_sublist {α : Type u} (xs : Array α) (start stop : Nat) :
    (xs.extract start stop).toList.Sublist xs.toList := by
  rw [Array.toList_extract]; exact (List.take_sublist _ _).trans (List.drop_sublist _ _)

@[grind →] theorem array_mem_of_mem_pop {α : Type u} {xs : Array α} {x : α} (h : x ∈ xs.pop) : x ∈ xs :=
  Array.mem_def.2 ((toList_pop_sublist xs).subset (Array.mem_def.1 h))

@[grind →] theorem array_mem_of_mem_eraseIdx {α : Type u} {xs : Array α} {i : Nat} {hi : i < xs.size} {x : α}
    (h : x ∈ xs.eraseIdx i hi) : x ∈ xs :=
  Array.mem_of_mem_eraseIdx h

@[grind →] theorem array_mem_of_mem_extract {α : Type u} {xs : Array α} {start stop : Nat} {x : α}
    (h : x ∈ xs.extract start stop) : x ∈ xs :=
  Array.mem_def.2 ((toList_extract_sublist xs start stop).subset (Array.mem_def.1 h))

@[grind →] theorem array_mem_of_mem_swap {α : Type u} {xs : Array α} {i j : Nat}
    {hi : i < xs.size} {hj : j < xs.size} {x : α} (h : x ∈ xs.swap i j hi hj) : x ∈ xs := by
  unfold Array.swap at h; rw [Array.mem_def, Array.toList_set] at h
  rcases List.mem_or_eq_of_mem_set h with h1 | rfl
  · rw [Array.toList_set] at h1
    rcases List.mem_or_eq_of_mem_set h1 with h2 | rfl
    · exact Array.mem_def.2 h2
    · exact Array.getElem_mem hj
  · exact Array.getElem_mem hi

/-! ### Generic `List.sum` Helpers (Shared by `Nat` and `Int`) -/

private theorem foldl_add_eq_sum {α β : Type} [Add β] [Zero β]
    [Std.Associative (α := β) (· + ·)] [Std.LawfulIdentity (α := β) (· + ·) 0] (f : α → β) :
    ∀ (l : List α) (init : β), l.foldl (fun acc x => acc + f x) init = init + (l.map f).sum
  | [], init => by simp [Std.LawfulRightIdentity.right_id]
  | x :: xs, init => by
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [foldl_add_eq_sum f xs (init + f x), Std.Associative.assoc (op := (· + ·))]

private theorem list_sum_perm {β : Type} [Add β] [Zero β]
    [Std.Associative (α := β) (· + ·)] [Std.Commutative (α := β) (· + ·)] {a b : List β} (h : a.Perm b) :
    a.sum = b.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.sum_cons, ih]
  | swap _ _ _ => simp only [List.sum_cons]; ac_rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem list_sum_map_set {α β : Type} [Add β] [Zero β]
    [Std.Associative (α := β) (· + ·)] [Std.Commutative (α := β) (· + ·)]
    (f : α → β) :
    ∀ (l : List α) (i : Nat) (x : α) (h : i < l.length),
      ((l.set i x).map f).sum + f l[i] = (l.map f).sum + f x
  | [], _, _, h => nomatch h
  | y :: ys, 0, x, _ => by
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons, List.getElem_cons_zero]; ac_rfl
  | y :: ys, i + 1, x, h => by
      have ih := list_sum_map_set f ys i x (by simpa using h)
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      rw [Std.Associative.assoc (op := (· + ·)), ih, ← Std.Associative.assoc (op := (· + ·))]

private theorem list_sum_map_eraseIdx {α β : Type} [Add β] [Zero β]
    [Std.Associative (α := β) (· + ·)] [Std.Commutative (α := β) (· + ·)]
    (f : α → β) :
    ∀ (l : List α) (i : Nat) (h : i < l.length),
      ((l.eraseIdx i).map f).sum + f l[i] = (l.map f).sum
  | [], _, h => nomatch h
  | y :: ys, 0, _ => by
      simp only [List.eraseIdx_zero, List.tail_cons, List.map_cons, List.sum_cons, List.getElem_cons_zero]
      exact Std.Commutative.comm (op := (· + ·)) _ _
  | y :: ys, i + 1, h => by
      have ih := list_sum_map_eraseIdx f ys i (by simpa using h)
      simp only [List.eraseIdx_cons_succ, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      rw [Std.Associative.assoc (op := (· + ·)), ih]

private theorem list_sum_nat_sublist {a b : List Nat} (h : a.Sublist b) : a.sum ≤ b.sum := by
  induction h <;> simp <;> omega

private theorem list_sum_nat_le_length_mul {α : Type} (f : α → Nat) (bound : Nat) :
    ∀ {l : List α}, (∀ x ∈ l, f x ≤ bound) → (l.map f).sum ≤ l.length * bound
  | [], _ => by simp
  | x :: xs, h => by
      have hx := h x (by simp)
      have hxs := list_sum_nat_le_length_mul f bound (l := xs) (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]; omega

private theorem foldl_sum_eq {α β : Type} [Add β] [Zero β]
    [Std.Associative (α := β) (· + ·)] [Std.LawfulIdentity (α := β) (· + ·) 0]
    (xs : Array α) (f : α → β) :
    xs.foldl (fun acc x => acc + f x) 0 = (xs.toList.map f).sum := by
  rw [← Array.foldl_toList, foldl_add_eq_sum]; exact Std.LawfulLeftIdentity.left_id _

private theorem foldl_sum_mergeSort {α β : Type} [Add β] [Zero β]
    [Std.Associative (α := β) (· + ·)] [Std.Commutative (α := β) (· + ·)] [Std.LawfulIdentity (α := β) (· + ·) 0]
    (xs : Array α) (le : α → α → Bool) (f : α → β) :
    (xs.mergeSort le).foldl (fun acc x => acc + f x) 0 = xs.foldl (fun acc x => acc + f x) 0 := by
  rw [foldl_sum_eq, foldl_sum_eq]
  exact list_sum_perm ((Array.perm_iff_toList_perm.1 (Array.mergeSort_perm (xs := xs) (le := le))).map f)

/-! ### `Array.sumBy` (`Nat`) -/

def _root_.Array.sumBy {α : Type} (xs : Array α) (f : α → Nat) : Nat :=
  xs.foldl (fun acc x => acc + f x) 0

private theorem sumBy_of_sublist {α : Type} {xs ys : Array α} (f : α → Nat)
    (hsub : ys.toList.Sublist xs.toList) : ys.sumBy f ≤ xs.sumBy f := by
  rw [Array.sumBy, Array.sumBy, foldl_sum_eq, foldl_sum_eq]; exact list_sum_nat_sublist (hsub.map f)

@[simp, grind =] theorem _root_.Array.sumBy_empty {α : Type} (f : α → Nat) : (#[] : Array α).sumBy f = 0 := rfl
@[simp, grind =] theorem _root_.Array.sumBy_push {α : Type} (xs : Array α) (f : α → Nat) (v : α) :
    (xs.push v).sumBy f = xs.sumBy f + f v := by simp [Array.sumBy, foldl_sum_eq]
@[simp, grind =] theorem _root_.Array.sumBy_append {α : Type} (xs ys : Array α) (f : α → Nat) :
    (xs ++ ys).sumBy f = xs.sumBy f + ys.sumBy f := by rw [Array.sumBy, Array.sumBy, Array.sumBy, foldl_sum_eq, foldl_sum_eq, foldl_sum_eq]; simp
@[simp, grind =] theorem _root_.Array.sumBy_map {α β : Type} (xs : Array α) (g : α → β) (f : β → Nat) :
    (xs.map g).sumBy f = xs.sumBy (fun x => f (g x)) := by rw [Array.sumBy, Array.sumBy, foldl_sum_eq, foldl_sum_eq]; simp [List.map_map, Function.comp_def]
@[simp, grind =] theorem _root_.Array.sumBy_reverse {α : Type} (xs : Array α) (f : α → Nat) :
    xs.reverse.sumBy f = xs.sumBy f := by rw [Array.sumBy, Array.sumBy, foldl_sum_eq, foldl_sum_eq]; simp
@[simp, grind =] theorem _root_.Array.sumBy_mergeSort {α : Type} (xs : Array α) (le : α → α → Bool) (f : α → Nat) :
    (xs.mergeSort le).sumBy f = xs.sumBy f := foldl_sum_mergeSort xs le f
@[grind <=] theorem _root_.Array.sumBy_filter_le {α : Type} (xs : Array α) (p : α → Bool) (f : α → Nat) :
    (xs.filter p).sumBy f ≤ xs.sumBy f := sumBy_of_sublist f (toList_filter_sublist xs p)
@[grind <=] theorem _root_.Array.sumBy_pop_le {α : Type} (xs : Array α) (f : α → Nat) :
    xs.pop.sumBy f ≤ xs.sumBy f := sumBy_of_sublist f (toList_pop_sublist xs)
@[grind <=] theorem _root_.Array.sumBy_extract_le {α : Type} (xs : Array α) (start stop : Nat) (f : α → Nat) :
    (xs.extract start stop).sumBy f ≤ xs.sumBy f := sumBy_of_sublist f (toList_extract_sublist xs start stop)
@[grind =] theorem _root_.Array.sumBy_set {α : Type} (xs : Array α) (f : α → Nat) (i : Nat) (v : α) (h : i < xs.size) :
    (xs.set i v h).sumBy f + f xs[i] = xs.sumBy f + f v := by
  rw [Array.sumBy, Array.sumBy, foldl_sum_eq, foldl_sum_eq, Array.toList_set]; exact list_sum_map_set f xs.toList i v h
@[grind =] theorem _root_.Array.sumBy_eraseIdx {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) (f : α → Nat) :
    (xs.eraseIdx i h).sumBy f + f xs[i] = xs.sumBy f := by
  rw [Array.sumBy, Array.sumBy, foldl_sum_eq, foldl_sum_eq, Array.toList_eraseIdx]; exact list_sum_map_eraseIdx f xs.toList i h

theorem _root_.Array.sumBy_le_size_mul {α : Type} {xs : Array α} (f : α → Nat) (bound : Nat)
    (h : ∀ x ∈ xs, f x ≤ bound) : xs.sumBy f ≤ xs.size * bound := by
  rw [Array.sumBy, foldl_sum_eq, ← Array.length_toList]
  exact list_sum_nat_le_length_mul f bound (fun y hy => h y (Array.mem_toList_iff.1 hy))

/-! ### `Array.sumByInt` (`Int`) -/

def _root_.Array.sumByInt {α : Type} (xs : Array α) (f : α → Int) : Int :=
  xs.foldl (fun acc x => acc + f x) 0

@[simp, grind =] theorem _root_.Array.sumByInt_empty {α : Type} (f : α → Int) : (#[] : Array α).sumByInt f = 0 := rfl
@[simp, grind =] theorem _root_.Array.sumByInt_push {α : Type} (xs : Array α) (x : α) (f : α → Int) :
    (xs.push x).sumByInt f = xs.sumByInt f + f x := by simp [Array.sumByInt, foldl_sum_eq]
@[simp, grind =] theorem _root_.Array.sumByInt_append {α : Type} (xs ys : Array α) (f : α → Int) :
    (xs ++ ys).sumByInt f = xs.sumByInt f + ys.sumByInt f := by rw [Array.sumByInt, Array.sumByInt, Array.sumByInt, foldl_sum_eq, foldl_sum_eq, foldl_sum_eq]; simp
@[simp, grind =] theorem _root_.Array.sumByInt_map {α β : Type} (xs : Array α) (g : α → β) (f : β → Int) :
    (xs.map g).sumByInt f = xs.sumByInt (fun x => f (g x)) := by rw [Array.sumByInt, Array.sumByInt, foldl_sum_eq, foldl_sum_eq]; simp [List.map_map, Function.comp_def]
@[simp, grind =] theorem _root_.Array.sumByInt_reverse {α : Type} (xs : Array α) (f : α → Int) :
    xs.reverse.sumByInt f = xs.sumByInt f := by rw [Array.sumByInt, Array.sumByInt, foldl_sum_eq, foldl_sum_eq]; simp
@[simp, grind =] theorem _root_.Array.sumByInt_mergeSort {α : Type} (xs : Array α) (le : α → α → Bool) (f : α → Int) :
    (xs.mergeSort le).sumByInt f = xs.sumByInt f := foldl_sum_mergeSort xs le f
@[grind =] theorem _root_.Array.sumByInt_set {α : Type} (xs : Array α) (i : Nat) (x : α) (h : i < xs.size) (f : α → Int) :
    (xs.set i x h).sumByInt f + f xs[i] = xs.sumByInt f + f x := by
  rw [Array.sumByInt, Array.sumByInt, foldl_sum_eq, foldl_sum_eq, Array.toList_set]; exact list_sum_map_set f xs.toList i x h
@[grind =] theorem _root_.Array.sumByInt_eraseIdx {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) (f : α → Int) :
    (xs.eraseIdx i h).sumByInt f + f xs[i] = xs.sumByInt f := by
  rw [Array.sumByInt, Array.sumByInt, foldl_sum_eq, foldl_sum_eq, Array.toList_eraseIdx]; exact list_sum_map_eraseIdx f xs.toList i h

/-! ### `Array.countWhere` -/

def _root_.Array.countWhere {α : Type} (xs : Array α) (p : α → Bool) : Nat :=
  xs.sumBy (fun x => if p x then 1 else 0)

@[simp, grind =] theorem _root_.Array.countWhere_empty {α : Type} (p : α → Bool) :
    (#[] : Array α).countWhere p = 0 := rfl

@[simp, grind =] theorem _root_.Array.countWhere_push {α : Type} (xs : Array α) (x : α) (p : α → Bool) :
    (xs.push x).countWhere p = xs.countWhere p + (if p x then 1 else 0) :=
  Array.sumBy_push xs _ x

@[simp, grind =] theorem _root_.Array.countWhere_append {α : Type} (xs ys : Array α) (p : α → Bool) :
    (xs ++ ys).countWhere p = xs.countWhere p + ys.countWhere p :=
  Array.sumBy_append xs ys _

@[simp, grind =] theorem _root_.Array.countWhere_reverse {α : Type} (xs : Array α) (p : α → Bool) :
    xs.reverse.countWhere p = xs.countWhere p :=
  Array.sumBy_reverse xs _

@[simp, grind =] theorem _root_.Array.countWhere_mergeSort {α : Type} (xs : Array α) (le : α → α → Bool) (p : α → Bool) :
    (xs.mergeSort le).countWhere p = xs.countWhere p :=
  Array.sumBy_mergeSort xs le _

@[grind <=] theorem _root_.Array.countWhere_le_size {α : Type} (xs : Array α) (p : α → Bool) :
    xs.countWhere p ≤ xs.size := by
  simpa [Array.countWhere] using
    Array.sumBy_le_size_mul (xs := xs) (fun x => if p x then 1 else 0) 1 (fun x _ => by dsimp only; split <;> omega)

@[grind <=] theorem _root_.Array.countWhere_filter_le {α : Type} (xs : Array α) (q p : α → Bool) :
    (xs.filter q).countWhere p ≤ xs.countWhere p := Array.sumBy_filter_le xs q _

@[grind <=] theorem _root_.Array.countWhere_pop_le {α : Type} (xs : Array α) (p : α → Bool) :
    xs.pop.countWhere p ≤ xs.countWhere p := Array.sumBy_pop_le xs _

@[grind =] theorem _root_.Array.countWhere_set {α : Type} (xs : Array α) (i : Nat) (x : α) (h : i < xs.size) (p : α → Bool) :
    (xs.set i x h).countWhere p + (if p xs[i] then 1 else 0) = xs.countWhere p + (if p x then 1 else 0) :=
  Array.sumBy_set xs _ i x h

@[grind =] theorem _root_.Array.countWhere_eraseIdx {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) (p : α → Bool) :
    (xs.eraseIdx i h).countWhere p + (if p xs[i] then 1 else 0) = xs.countWhere p :=
  Array.sumBy_eraseIdx xs i h _

/-! ### `Array.uniqueBy` (`Decidable`) -/

def _root_.Array.uniqueBy {α β : Type} (xs : Array α) (key : α → β) : Prop :=
  (xs.toList.map key).Nodup

instance {α β : Type} [DecidableEq β] (xs : Array α) (key : α → β) : Decidable (xs.uniqueBy key) :=
  inferInstanceAs (Decidable (xs.toList.map key).Nodup)

@[simp, grind .] theorem _root_.Array.uniqueBy_empty {α β : Type} (key : α → β) :
    (#[] : Array α).uniqueBy key := by simp [Array.uniqueBy]

@[simp, grind =] theorem _root_.Array.uniqueBy_push_iff {α β : Type} (xs : Array α) (x : α) (key : α → β) :
    (xs.push x).uniqueBy key ↔ xs.uniqueBy key ∧ ∀ y ∈ xs, key y ≠ key x := by
  simp only [Array.uniqueBy, Array.toList_push, List.map_append, List.map_cons, List.map_nil,
    List.nodup_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
    and_self, true_and, List.mem_cons, List.mem_map, Array.mem_toList_iff]
  exact ⟨fun ⟨h, d⟩ => ⟨h, fun y hy e => d _ ⟨y, hy, rfl⟩ _ (.inl rfl) e⟩,
         fun ⟨h, n⟩ => ⟨h, fun _ ⟨y, hy, he⟩ _ hk hEq => hk.elim (fun e => n y hy ((he.trans hEq).trans e)) False.elim⟩⟩

private theorem uniqueBy_of_sublist {α β : Type} {xs ys : Array α} {key : α → β}
    (hsub : ys.toList.Sublist xs.toList) (h : xs.uniqueBy key) : ys.uniqueBy key :=
  h.sublist (hsub.map key)

@[grind ←] theorem _root_.Array.uniqueBy_filter {α β : Type} {xs : Array α} {key : α → β} {p : α → Bool}
    (h : xs.uniqueBy key) : (xs.filter p).uniqueBy key := uniqueBy_of_sublist (toList_filter_sublist xs p) h
@[grind ←] theorem _root_.Array.uniqueBy_pop {α β : Type} {xs : Array α} {key : α → β}
    (h : xs.uniqueBy key) : xs.pop.uniqueBy key := uniqueBy_of_sublist (toList_pop_sublist xs) h
@[grind ←] theorem _root_.Array.uniqueBy_eraseIdx {α β : Type} {xs : Array α} {key : α → β}
    {i : Nat} {hi : i < xs.size} (h : xs.uniqueBy key) : (xs.eraseIdx i hi).uniqueBy key :=
  uniqueBy_of_sublist (toList_eraseIdx_sublist xs i hi) h
@[grind ←] theorem _root_.Array.uniqueBy_extract {α β : Type} {xs : Array α} {key : α → β}
    {start stop : Nat} (h : xs.uniqueBy key) : (xs.extract start stop).uniqueBy key :=
  uniqueBy_of_sublist (toList_extract_sublist xs start stop) h

@[grind ←] theorem _root_.Array.uniqueBy_reverse {α β : Type} {xs : Array α} {key : α → β}
    (h : xs.uniqueBy key) : xs.reverse.uniqueBy key := by
  simp only [Array.uniqueBy, Array.toList_reverse, List.map_reverse]
  exact (List.reverse_perm _).nodup_iff.2 h

@[grind ←] theorem _root_.Array.uniqueBy_mergeSort {α β : Type} {xs : Array α} {key : α → β}
    {le : α → α → Bool} (h : xs.uniqueBy key) : (xs.mergeSort le).uniqueBy key :=
  (((Array.perm_iff_toList_perm.1 (Array.mergeSort_perm (xs := xs) (le := le))).map key).nodup_iff).2 h

@[grind ←] theorem _root_.Array.uniqueBy_map_same_key {α β : Type} {xs : Array α} {key : α → β}
    {g : α → α} (hKey : ∀ y ∈ xs, key (g y) = key y) (h : xs.uniqueBy key) : (xs.map g).uniqueBy key := by
  simp only [Array.uniqueBy, Array.toList_map, List.map_map, Function.comp_def]
  rwa [List.map_congr_left (fun y hy => hKey y (Array.mem_toList_iff.1 hy))]

/-! ### `Array.isSortedBy` (`Decidable`) -/

def _root_.Array.isSortedBy {α : Type} (xs : Array α) (key : α → Nat) : Prop :=
  xs.toList.Pairwise (fun a b => key a ≤ key b)

instance {α : Type} (xs : Array α) (key : α → Nat) : Decidable (xs.isSortedBy key) :=
  inferInstanceAs (Decidable (xs.toList.Pairwise (fun a b => key a ≤ key b)))

@[simp, grind .] theorem _root_.Array.isSortedBy_empty {α : Type} (key : α → Nat) :
    (#[] : Array α).isSortedBy key := by simp [Array.isSortedBy]

@[simp, grind .] theorem _root_.Array.isSortedBy_singleton {α : Type} (x : α) (key : α → Nat) :
    #[x].isSortedBy key := by simp [Array.isSortedBy]

@[simp, grind =] theorem _root_.Array.isSortedBy_push_iff {α : Type} (xs : Array α) (x : α) (key : α → Nat) :
    (xs.push x).isSortedBy key ↔ xs.isSortedBy key ∧ ∀ y ∈ xs, key y ≤ key x := by
  simp only [Array.isSortedBy, Array.toList_push, List.pairwise_append, List.pairwise_singleton,
    List.mem_singleton, forall_eq, true_and, Array.mem_toList_iff]

@[grind ←] theorem _root_.Array.isSortedBy_filter {α : Type} {xs : Array α} {key : α → Nat} {p : α → Bool}
    (h : xs.isSortedBy key) : (xs.filter p).isSortedBy key := h.sublist (toList_filter_sublist xs p)
@[grind ←] theorem _root_.Array.isSortedBy_pop {α : Type} {xs : Array α} {key : α → Nat}
    (h : xs.isSortedBy key) : xs.pop.isSortedBy key := h.sublist (toList_pop_sublist xs)
@[grind ←] theorem _root_.Array.isSortedBy_eraseIdx {α : Type} {xs : Array α} {key : α → Nat}
    {i : Nat} {hi : i < xs.size} (h : xs.isSortedBy key) : (xs.eraseIdx i hi).isSortedBy key :=
  h.sublist (toList_eraseIdx_sublist xs i hi)
@[grind ←] theorem _root_.Array.isSortedBy_extract {α : Type} {xs : Array α} {key : α → Nat}
    {start stop : Nat} (h : xs.isSortedBy key) : (xs.extract start stop).isSortedBy key :=
  h.sublist (toList_extract_sublist xs start stop)

@[grind .] theorem _root_.Array.isSortedBy_mergeSort_le {α : Type} (xs : Array α) (key : α → Nat) :
    (xs.mergeSort (fun a b => decide (key a ≤ key b))).isSortedBy key :=
  (Array.pairwise_mergeSort (xs := xs) (le := fun a b => decide (key a ≤ key b))
    (trans := fun _ _ _ hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (total := fun a b => by by_cases h : key a ≤ key b <;> simp [h] <;> omega)).imp
    (by intro _ _ hab; simpa using hab)

/-! ### Shared Nonlinear Monotonicity Closer -/

macro "qedNonlinearClose" : tactic => `(tactic|
  (first
    | (apply Nat.mul_le_mul <;> omega)
    | (apply Nat.mul_le_mul_left <;> omega)
    | (apply Nat.mul_le_mul_right <;> omega)
    | (apply Nat.mul_lt_mul_of_pos_left <;> omega)
    | (apply Nat.mul_lt_mul_of_pos_right <;> omega)
    | (apply Nat.div_le_div_right; omega)
    | (exact Nat.le_trans (Nat.div_le_self _ _) (by omega))
    | (exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))
    | (apply Int.mul_nonneg <;> omega)
    | (apply Int.mul_le_mul_of_nonneg_left <;> omega)
    | (apply Int.mul_le_mul_of_nonneg_right <;> omega)
    | (apply Int.mul_le_mul <;> omega)))

end Qed
