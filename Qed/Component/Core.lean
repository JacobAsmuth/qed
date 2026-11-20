import Qed.Html
import Qed.Collection

namespace Qed

structure Component (Model : Type) (Msg : Type) where
  update : Model → Msg → Model
  view   : Model → Html Msg

namespace Component
variable {Model Msg PMsg : Type}

def render (c : Component Model Msg) (wrap : Msg → PMsg) (m : Model) : Html PMsg :=
  (c.view m).map wrap

def updateKeyed (c : Component Model Msg) (key : Model → String)
    (models : Array Model) (k : String) (msg : Msg) : Array Model :=
  models.map fun r => if key r == k then c.update r msg else r

end Component

namespace ForEach

theorem forall_push {α} {P : α → Prop} {a : Array α} {x : α}
    (h : ∀ y ∈ a, P y) (hx : P x) : ∀ y ∈ a.push x, P y := by
  simpa only [Array.mem_push, or_imp, forall_and, forall_eq] using And.intro h hx

theorem forall_filter {α} {P : α → Prop} {a : Array α} {f : α → Bool}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ a.filter f, P y := by
  simpa only [Array.mem_filter, and_imp] using fun y hy _ => h y hy

theorem forall_map {α} {P : α → Prop} {a : Array α} {g : α → α}
    (hg : ∀ y ∈ a, P (g y)) : ∀ y ∈ a.map g, P y := by
  intro y hy; rw [Array.mem_map] at hy; obtain ⟨x, hx, rfl⟩ := hy; exact hg x hx

theorem updateKeyed_forall {α Msg} {P : α → Prop} (c : Component α Msg) (key : α → String)
    (hc : ∀ r m, P r → P (c.update r m))
    {a : Array α} {k : String} {msg : Msg}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ Component.updateKeyed c key a k msg, P y := by
  intro y hy; simp only [Component.updateKeyed, Array.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy; split
  · exact hc x msg (h x hx)
  · exact h x hx

-- `mergeSort` provides `Array.mem_mergeSort`; `Array.qsort` has no stdlib membership lemma.
@[reducible] def _root_.Array.sortBy {α} (a : Array α) (le : α → α → Bool) : Array α := a.mergeSort le

@[simp, grind =] theorem _root_.Array.mem_sortBy {α} {a : Array α} {le : α → α → Bool} {y : α} :
    y ∈ a.sortBy le ↔ y ∈ a :=
  Array.mem_mergeSort

theorem forall_sortBy {α} {P : α → Prop} {a : Array α} {le : α → α → Bool}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ a.sortBy le, P y := by
  intro y hy; simp only [Array.sortBy, Array.mem_mergeSort] at hy; exact h y hy

theorem forall_append {α} {P : α → Prop} {a b : Array α}
    (ha : ∀ y ∈ a, P y) (hb : ∀ y ∈ b, P y) : ∀ y ∈ a ++ b, P y := fun y hy =>
  (Array.mem_append.1 hy).elim (ha y) (hb y)

theorem forall_pop {α} {P : α → Prop} {a : Array α} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.pop, P y :=
  fun _ hy => h _ (array_mem_of_mem_pop hy)

theorem forall_reverse {α} {P : α → Prop} {a : Array α} (h : ∀ y ∈ a, P y) : ∀ y ∈ a.reverse, P y :=
  fun _ hy => h _ (Array.mem_reverse.1 hy)

theorem forall_extract {α} {P : α → Prop} {a : Array α} {start stop : Nat}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ a.extract start stop, P y :=
  fun _ hy => h _ (array_mem_of_mem_extract hy)

theorem forall_eraseIdx {α} {P : α → Prop} {a : Array α} {i : Nat} {hi : i < a.size}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ a.eraseIdx i hi, P y :=
  fun _ hy => h _ (Array.mem_of_mem_eraseIdx hy)

theorem forall_eraseIdxIfInBounds {α} {P : α → Prop} {a : Array α} {i : Nat}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ a.eraseIdxIfInBounds i, P y := by
  unfold Array.eraseIdxIfInBounds; split; exact forall_eraseIdx h; exact h

theorem forall_set {α} {P : α → Prop} {a : Array α} {i : Nat} {x : α} {hi : i < a.size}
    (h : ∀ y ∈ a, P y) (hx : P x) : ∀ y ∈ a.set i x hi, P y :=
  Array.forall_set hi h hx

theorem forall_setIfInBounds {α} {P : α → Prop} {a : Array α} {i : Nat} {x : α}
    (h : ∀ y ∈ a, P y) (hx : P x) : ∀ y ∈ a.setIfInBounds i x, P y := by
  unfold Array.setIfInBounds; split; exact forall_set h hx; exact h

theorem forall_swap {α} {P : α → Prop} {a : Array α} {i j : Nat} {hi : i < a.size} {hj : j < a.size}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ a.swap i j hi hj, P y :=
  fun _ hy => h _ (array_mem_of_mem_swap hy)

theorem forall_swapIfInBounds {α} {P : α → Prop} {a : Array α} {i j : Nat}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ a.swapIfInBounds i j, P y := by
  unfold Array.swapIfInBounds; split <;> (try split) <;> first | exact forall_swap h | exact h

theorem forall_modify {α} {P : α → Prop} {a : Array α} {i : Nat} {f : α → α}
    (h : ∀ y ∈ a, P y) (hf : ∀ y ∈ a, P y → P (f y)) : ∀ y ∈ a.modify i f, P y := by
  intro y hy
  have hMod : a.modify i f = if hi : i < a.size then a.set i (f a[i]) hi else a := by
    simp [Array.modify, Array.modifyM]; split <;> rfl
  rw [hMod] at hy; split at hy
  · rename_i hi; exact forall_set h (hf _ (Array.getElem_mem hi) (h _ (Array.getElem_mem hi))) y hy
  · exact h y hy

end ForEach

end Qed
