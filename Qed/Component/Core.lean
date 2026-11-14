import Qed.Html

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

def each (c : Component Model Msg) (keyOf : Model → String) (rows : Array Model)
    (route : String → Msg → PMsg)
    (wrap : Model → Html PMsg → Html PMsg := fun _ child => child) : Array (Html PMsg) :=
  rows.map fun row =>
    let k := keyOf row
    let child := wrap row (render c (route k) row)
    match child with
    | .element tag attrs children =>
        .element tag (.key k :: attrs.filter (fun | .key _ => false | _ => true)) children
    | other => .element "div" [.key k] [other]

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

theorem forall_sortBy {α} {P : α → Prop} {a : Array α} {le : α → α → Bool}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ a.sortBy le, P y := by
  intro y hy; simp only [Array.sortBy, Array.mem_mergeSort] at hy; exact h y hy

end ForEach

end Qed
