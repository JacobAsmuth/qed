import Qed.Html
import Std.Data.HashMap

namespace Qed

def Html.keyOf : Html msg → Option String
  | .element _ attrs _ => attrs.findSome? (fun | .key k => some k | _ => none) | _ => none

def validatedKeyIndex (cs : List (Html msg)) : Option (Std.HashMap String Nat) := go cs 0 ∅
where
  go : List (Html msg) → Nat → Std.HashMap String Nat → Option (Std.HashMap String Nat)
    | [], _, index => some index
    | c :: rest, i, index => do let key ← c.keyOf; if index.contains key then none else go rest (i + 1) (index.insert key i)

mutual
  inductive Patch (msg : Type) where
    | replace (new : Html msg)
    | setText (content : String)
    | patchElement (attrs : List (Attr msg)) (steps : List (KeyedStep msg))
  inductive KeyedStep (msg : Type) where
    | reuse (oldIndex : Nat) (p : Patch msg)
    | create (h : Html msg)
end

mutual
  def diff : Html msg → Html msg → Patch msg
    | .text _, .text s => .setText s
    | .element t₁ _ c₁, .element t₂ a₂ c₂ =>
        if t₁ = t₂ then
          let oldArr := c₁.toArray
          let pick : Nat → Html msg → Option Nat :=
            match validatedKeyIndex c₁ with
            | some index => if (validatedKeyIndex c₂).isSome then fun _ n => n.keyOf.bind (index[·]?) else fun i _ => if i < oldArr.size then some i else none
            | none => fun i _ => if i < oldArr.size then some i else none
          .patchElement a₂ (diffChildrenTR oldArr pick #[] 0 c₂).toList
        else .replace (.element t₂ a₂ c₂)
    | _, b => .replace b
  def diffChildrenTR (oldArr : Array (Html msg)) (pick : Nat → Html msg → Option Nat) (acc : Array (KeyedStep msg)) : Nat → List (Html msg) → Array (KeyedStep msg)
    | _, [] => acc
    | i, n :: ns => diffChildrenTR oldArr pick (acc.push (match pick i n with | some j => .reuse j (diff (oldArr.getD j default) n) | none => .create n)) (i + 1) ns
end

def diffChildren (oldArr : Array (Html msg)) (pick : Nat → Html msg → Option Nat) : Nat → List (Html msg) → List (KeyedStep msg)
  | _, [] => []
  | i, n :: ns => (match pick i n with | some j => .reuse j (diff (oldArr.getD j default) n) | none => .create n) :: diffChildren oldArr pick (i + 1) ns

theorem diffChildrenTR_toList (oldArr : Array (Html msg)) (pick : Nat → Html msg → Option Nat) :
    ∀ (news : List (Html msg)) (acc : Array (KeyedStep msg)) (i : Nat), (diffChildrenTR oldArr pick acc i news).toList = acc.toList ++ diffChildren oldArr pick i news
  | [], _, _ => by simp [diffChildrenTR, diffChildren]
  | _ :: ns, acc, i => by simp [diffChildrenTR, diffChildren, diffChildrenTR_toList oldArr pick ns]

mutual
  def applyPatch : Patch msg → Html msg → Html msg
    | .replace new, _ => new | .setText s, _ => .text s
    | .patchElement attrs steps, .element tag _ children => .element tag attrs (applyChildrenTR #[] steps children.toArray).toList
    | .patchElement _ _, h => h
  def applyChild (old : Array (Html msg)) : KeyedStep msg → Html msg
    | .reuse i p => applyPatch p (old.getD i default) | .create h => h
  def applyChildrenTR (acc : Array (Html msg)) : List (KeyedStep msg) → Array (Html msg) → Array (Html msg)
    | [], _ => acc | step :: rest, old => applyChildrenTR (acc.push (applyChild old step)) rest old
end

def applyChildren (steps : List (KeyedStep msg)) (old : List (Html msg)) : List (Html msg) := steps.map (applyChild old.toArray)

theorem applyChildrenTR_toList : ∀ (steps : List (KeyedStep msg)) (acc : Array (Html msg)) (old : Array (Html msg)),
    (applyChildrenTR acc steps old).toList = acc.toList ++ steps.map (applyChild old)
  | [], _, _ => by simp [applyChildrenTR]
  | _ :: rest, acc, old => by simp [applyChildrenTR, applyChildrenTR_toList rest]

mutual
  theorem diff_apply : ∀ (a b : Html msg), applyPatch (diff a b) a = b
    | .element t₁ a₁ c₁, .element t₂ a₂ c₂ => by
        simp only [diff]; split
        · rename_i ht; subst ht; simp only [applyPatch, applyChildrenTR_toList, diffChildrenTR_toList, List.nil_append]
          exact congrArg (Html.element t₁ a₂) (diffChildren_apply c₁ _ 0 c₂)
        · rfl
    | .text _, .text _ | .text _, .element .. | .element .., .text _ => rfl
  theorem diffChildren_apply (old : List (Html msg)) :
      ∀ (pick : Nat → Html msg → Option Nat) (i : Nat) (news : List (Html msg)), applyChildren (diffChildren old.toArray pick i news) old = news
    | _, _, [] => rfl
    | pick, i, n :: ns => by
        have tail := diffChildren_apply old pick (i + 1) ns; simp only [applyChildren] at tail
        cases h : pick i n <;> simp [diffChildren, h, applyChildren, applyChild, diff_apply, tail]
end

/-! ## Key-Preserving & Positional Reuse Theorems -/

private theorem validatedKeyIndex_go_spec :
    ∀ (cs : List (Html msg)) (base : Nat) (acc index : Std.HashMap String Nat),
      validatedKeyIndex.go cs base acc = some index →
      (∀ (k : String) (j : Nat), acc[k]? = some j → index[k]? = some j) ∧
      (∀ (k : String) (j : Nat), index[k]? = some j → (acc[k]? = some j) ∨ (∃ d, ∃ _ : d < cs.length, j = base + d ∧ cs[d].keyOf = some k)) ∧
      (∀ (d : Nat) (hd : d < cs.length), ∃ k, cs[d].keyOf = some k ∧ index[k]? = some (base + d))
  | [], _, _, _, hgo => by simp only [validatedKeyIndex.go, Option.some.injEq] at hgo; subst hgo; exact ⟨fun _ _ h => h, fun _ _ h => .inl h, fun _ hd => nomatch hd⟩
  | c :: rest, base, acc, index, hgo => by
      simp only [validatedKeyIndex.go] at hgo
      cases hk : c.keyOf with
      | none => simp [hk, bind, Option.bind] at hgo
      | some key =>
          simp only [hk, bind, Option.bind] at hgo
          by_cases hcon : acc.contains key = true
          · simp [hcon] at hgo
          · simp only [Bool.eq_false_iff.2 hcon, Bool.false_eq_true, ↓reduceIte] at hgo
            rcases validatedKeyIndex_go_spec rest (base + 1) (acc.insert key base) index hgo with ⟨ihMono, ihInv, ihElem⟩
            have hkeyNone : acc[key]? = none := Std.HashMap.getElem?_eq_none hcon
            refine ⟨fun k j hkAcc => ?_, fun k j hkIdx => ?_, fun d hd => ?_⟩
            · have hne : (key == k) = false := beq_eq_false_iff_ne.2 fun h => by subst h; simp [hkeyNone] at hkAcc
              exact ihMono k j (by rw [Std.HashMap.getElem?_insert, ite_eq_right (by simp [hne])]; exact hkAcc)
            · rcases ihInv k j hkIdx with hkIns | ⟨d, hd, hjd, hcd⟩
              · rw [Std.HashMap.getElem?_insert] at hkIns; split at hkIns
                · rename_i hbeq; rcases eq_of_beq hbeq with rfl; cases hkIns; exact .inr ⟨0, by simp, by omega, hk⟩
                · exact .inl hkIns
              · exact .inr ⟨d + 1, by simp only [List.length_cons]; omega, by omega, hcd⟩
            · cases d with
              | zero => exact ⟨key, hk, ihMono key base (by rw [Std.HashMap.getElem?_insert, ite_eq_left (beq_self_eq_true key)])⟩
              | succ d' => rcases ihElem d' (Nat.lt_of_succ_lt_succ hd) with ⟨k', hk', hidx'⟩; exact ⟨k', hk', by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hidx'⟩

theorem validatedKeyIndex_spec {cs : List (Html msg)} {index : Std.HashMap String Nat} (hval : validatedKeyIndex cs = some index) :
    (∀ (k : String) (j : Nat), index[k]? = some j → ∃ _ : j < cs.length, cs[j].keyOf = some k) ∧
    (∀ (j : Nat) (hj : j < cs.length), ∃ k, cs[j].keyOf = some k ∧ index[k]? = some j) := by
  rcases validatedKeyIndex_go_spec cs 0 ∅ index hval with ⟨_, hInv, hElem⟩
  exact ⟨fun k j hj => (hInv k j hj).elim (by simp) (fun ⟨_, hd, hjd, hcd⟩ => hjd ▸ ⟨by simpa using hd, by simpa using hcd⟩), fun j hj => by simpa using hElem j hj⟩

theorem diffChildren_length (oldArr : Array (Html msg)) (pick : Nat → Html msg → Option Nat) :
    ∀ (news : List (Html msg)) (i : Nat), (diffChildren oldArr pick i news).length = news.length
  | [], _ => rfl | _ :: ns, i => by simp [diffChildren, diffChildren_length oldArr pick ns (i + 1)]

theorem diffChildren_getElem (oldArr : Array (Html msg)) (pick : Nat → Html msg → Option Nat) :
    ∀ (news : List (Html msg)) (i idx : Nat) (hidx : idx < news.length),
      (diffChildren oldArr pick i news)[idx]'(by rw [diffChildren_length]; exact hidx) =
        match pick (i + idx) news[idx] with | some j => .reuse j (diff (oldArr.getD j default) news[idx]) | none => .create news[idx]
  | [], _, _, hidx => nomatch hidx
  | _ :: _, _, 0, _ => by simp [diffChildren]
  | _ :: ns, i, k + 1, hidx => by
      simp only [diffChildren, List.getElem_cons_succ]
      exact (diffChildren_getElem oldArr pick ns (i + 1) k (Nat.lt_of_succ_lt_succ hidx)).trans (by simp [Nat.add_comm, Nat.add_left_comm])

private theorem diff_steps_of_pick {c₁ c₂ : List (Html msg)} (pick : Nat → Html msg → Option Nat) :
    let steps := (diffChildrenTR c₁.toArray pick #[] 0 c₂).toList
    ∃ (hlen : steps.length = c₂.length), ∀ (i : Nat) (hi : i < c₂.length),
      steps[i]'(hlen ▸ hi) = match pick i c₂[i] with | some j => .reuse j (diff (c₁.toArray.getD j default) c₂[i]) | none => .create c₂[i] := by
  intro steps; have hEq : steps = diffChildren c₁.toArray pick 0 c₂ := by simp [steps, diffChildrenTR_toList]
  exact ⟨by simp [hEq, diffChildren_length], fun i hi => by simpa [hEq, Nat.zero_add] using diffChildren_getElem c₁.toArray pick c₂ 0 i hi⟩

theorem diff_keyed_reuses {t : String} {a₁ a₂ : List (Attr msg)} {c₁ c₂ : List (Html msg)} {idx₁ idx₂ : Std.HashMap String Nat}
    (h₁ : validatedKeyIndex c₁ = some idx₁) (h₂ : validatedKeyIndex c₂ = some idx₂) :
    ∃ steps, diff (.element t a₁ c₁) (.element t a₂ c₂) = .patchElement a₂ steps ∧
      ∃ (hlen : steps.length = c₂.length), ∀ (i : Nat) (hi : i < c₂.length),
        (∀ (j : Nat) (hj : j < c₁.length) (k : String), c₂[i].keyOf = some k → c₁[j].keyOf = some k → steps[i]'(hlen ▸ hi) = .reuse j (diff c₁[j] c₂[i])) ∧
        (∀ (k : String), c₂[i].keyOf = some k → (∀ (j : Nat) (hj : j < c₁.length), c₁[j].keyOf ≠ some k) → steps[i]'(hlen ▸ hi) = .create c₂[i]) := by
  let pick := fun (_ : Nat) (n : Html msg) => n.keyOf.bind (idx₁[·]?)
  obtain ⟨hlen, hget⟩ := diff_steps_of_pick (c₁ := c₁) (c₂ := c₂) pick; have ⟨hspec1, hspec2⟩ := validatedKeyIndex_spec h₁
  refine ⟨_, by simp [diff, h₁, h₂, pick], hlen, fun i hi => ⟨fun j hj k hk₂ hk₁ => ?_, fun k hk₂ hnone => ?_⟩⟩
  · obtain ⟨k', hk'₁, hidxk'⟩ := hspec2 j hj; rw [hk₁] at hk'₁; cases hk'₁; rw [hget i hi]; simp [pick, hk₂, hidxk', Array.getD, hj]
  · have hnoneIdx : idx₁[k]? = none := by cases hq : idx₁[k]? with | none => rfl | some j => obtain ⟨hj, hcj⟩ := hspec1 k j hq; exact absurd hcj (hnone j hj)
    rw [hget i hi]; simp [pick, hk₂, hnoneIdx]

theorem diff_positional_reuses {t : String} {a₁ a₂ : List (Attr msg)} {c₁ c₂ : List (Html msg)}
    (hunkeyed : validatedKeyIndex c₁ = none ∨ validatedKeyIndex c₂ = none) :
    ∃ steps, diff (.element t a₁ c₁) (.element t a₂ c₂) = .patchElement a₂ steps ∧
      ∃ (hlen : steps.length = c₂.length), ∀ (i : Nat) (hi : i < c₂.length),
        (∀ (hi1 : i < c₁.length), steps[i]'(hlen ▸ hi) = .reuse i (diff c₁[i] c₂[i])) ∧
        (c₁.length ≤ i → steps[i]'(hlen ▸ hi) = .create c₂[i]) := by
  let pick := fun i (_ : Html msg) => if i < c₁.toArray.size then some i else none
  obtain ⟨hlen, hget⟩ := diff_steps_of_pick (c₁ := c₁) (c₂ := c₂) pick
  have hdiffEq : diff (.element t a₁ c₁) (.element t a₂ c₂) = .patchElement a₂ (diffChildrenTR c₁.toArray pick #[] 0 c₂).toList := by
    rcases hunkeyed with h1 | h2; simp [diff, h1, pick]; cases h1 : validatedKeyIndex c₁ <;> simp [diff, h1, h2, pick]
  exact ⟨_, hdiffEq, hlen, fun i hi => ⟨fun hi1 => by rw [hget i hi]; simp [pick, Array.getD, hi1], fun hge => by rw [hget i hi]; simp [pick, Nat.not_lt_of_ge hge]⟩⟩

end Qed
