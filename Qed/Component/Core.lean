import Qed.Html
import Qed.Collection

namespace Qed

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
theorem forall_push {x : α} (h : ∀ y ∈ a, P y) (hx : P x) : ∀ y ∈ a.push x, P y := by
  simpa only [Array.mem_push, or_imp, forall_and, forall_eq] using And.intro h hx
theorem forall_filter {f : α → Bool} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.filter f, P y := fun y hy => h y (Array.mem_filter.1 hy).1
theorem forall_sortBy {le : α → α → Bool} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.sortBy le, P y := fun y hy => h y (Array.mem_mergeSort.1 hy)
theorem forall_append {b : Array α} (ha : ∀ y ∈ a, P y) (hb : ∀ y ∈ b, P y) : ∀ y ∈ a ++ b, P y := fun y hy => (Array.mem_append.1 hy).elim (ha y) (hb y)
theorem forall_pop (h : ∀ y ∈ a, P y) : ∀ y ∈ a.pop, P y := fun _ hy => h _ (array_mem_of_mem_pop hy)
theorem forall_reverse (h : ∀ y ∈ a, P y) : ∀ y ∈ a.reverse, P y := fun _ hy => h _ (Array.mem_reverse.1 hy)
theorem forall_extract {start stop : Nat} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.extract start stop, P y := fun _ hy => h _ (array_mem_of_mem_extract hy)
theorem forall_eraseIdx {i : Nat} {hi : i < a.size} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.eraseIdx i hi, P y := fun _ hy => h _ (Array.mem_of_mem_eraseIdx hy)
theorem forall_eraseIdxIfInBounds {i : Nat} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.eraseIdxIfInBounds i, P y := by
  unfold Array.eraseIdxIfInBounds; split; exact forall_eraseIdx h; exact h
theorem forall_set {i : Nat} {x : α} {hi : i < a.size} (h : ∀ y ∈ a, P y) (hx : P x) : ∀ y ∈ a.set i x hi, P y := Array.forall_set hi h hx
theorem forall_setIfInBounds {i : Nat} {x : α} (h : ∀ y ∈ a, P y) (hx : P x) : ∀ y ∈ a.setIfInBounds i x, P y := by
  unfold Array.setIfInBounds; split; exact forall_set h hx; exact h
theorem forall_swap {i j : Nat} {hi : i < a.size} {hj : j < a.size} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.swap i j hi hj, P y := fun _ hy => h _ (array_mem_of_mem_swap hy)
theorem forall_swapIfInBounds {i j : Nat} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.swapIfInBounds i j, P y := by
  unfold Array.swapIfInBounds; split <;> (try split) <;> first | exact forall_swap h | exact h
theorem forall_modify {i : Nat} {f : α → α} (h : ∀ y ∈ a, P y) (hf : ∀ y ∈ a, P y → P (f y)) : ∀ y ∈ a.modify i f, P y := by
  intro y hy
  have hMod : a.modify i f = if hi : i < a.size then a.set i (f a[i]) hi else a := by simp [Array.modify, Array.modifyM]; split <;> rfl
  rw [hMod] at hy; split at hy
  · rename_i hi; exact forall_set h (hf _ (Array.getElem_mem hi) (h _ (Array.getElem_mem hi))) y hy
  · exact h y hy

end ForEach
end Qed
