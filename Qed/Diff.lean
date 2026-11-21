import Qed.Html
import Std.Data.HashMap

namespace Qed

def Html.keyOf : Html msg → Option String
  | .element _ attrs _ => attrs.findSome? (fun a => match a with | .key k => some k | _ => none)
  | _                  => none

def validatedKeyIndex (cs : List (Html msg)) : Option (Std.HashMap String Nat) :=
  go cs 0 ∅
where
  go : List (Html msg) → Nat → Std.HashMap String Nat → Option (Std.HashMap String Nat)
    | [], _, index => some index
    | c :: rest, i, index => do
        let key ← c.keyOf
        if index.contains key then none else go rest (i + 1) (index.insert key i)

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
    | .text _,          .text s          => .setText s
    | .element t₁ _ c₁, .element t₂ a₂ c₂ =>
        if t₁ = t₂ then
          let oldArr := c₁.toArray
          let pick : Nat → Html msg → Option Nat :=
            match validatedKeyIndex c₁ with
            | some index =>
                if (validatedKeyIndex c₂).isSome then
                  fun _ n => n.keyOf.bind (fun k => index[k]?)
                else
                  fun i _ => if i < oldArr.size then some i else none
            | none =>
                fun i _ => if i < oldArr.size then some i else none
          .patchElement a₂ (diffChildrenTR oldArr pick #[] 0 c₂).toList
        else .replace (.element t₂ a₂ c₂)
    | _,                b                 => .replace b
  def diffChildrenTR (oldArr : Array (Html msg)) (pick : Nat → Html msg → Option Nat)
      (acc : Array (KeyedStep msg)) : Nat → List (Html msg) → Array (KeyedStep msg)
    | _, []      => acc
    | i, n :: ns =>
        diffChildrenTR oldArr pick (acc.push (match pick i n with
          | some j => .reuse j (diff (oldArr.getD j default) n)
          | none   => .create n)) (i + 1) ns
end

def diffChildren (oldArr : Array (Html msg)) (pick : Nat → Html msg → Option Nat) :
    Nat → List (Html msg) → List (KeyedStep msg)
  | _, []      => []
  | i, n :: ns =>
      (match pick i n with
       | some j => .reuse j (diff (oldArr.getD j default) n)
       | none   => .create n) :: diffChildren oldArr pick (i + 1) ns

theorem diffChildrenTR_toList (oldArr : Array (Html msg)) (pick : Nat → Html msg → Option Nat)
    (news : List (Html msg)) :
    ∀ (acc : Array (KeyedStep msg)) (i : Nat),
      (diffChildrenTR oldArr pick acc i news).toList = acc.toList ++ diffChildren oldArr pick i news := by
  induction news with
  | nil => intro acc i; simp [diffChildrenTR, diffChildren]
  | cons n ns ih => intro acc i; simp [diffChildrenTR, diffChildren, ih]

mutual
  def applyPatch : Patch msg → Html msg → Html msg
    | .replace new,              _                       => new
    | .setText s,                _                       => .text s
    | .patchElement attrs steps, .element tag _ children => .element tag attrs (applyChildrenTR #[] steps children.toArray).toList
    | .patchElement _ _,         h                       => h
  def applyChild (old : Array (Html msg)) : KeyedStep msg → Html msg
    | .reuse i p => applyPatch p (old.getD i default)
    | .create h => h
  def applyChildrenTR (acc : Array (Html msg)) :
      List (KeyedStep msg) → Array (Html msg) → Array (Html msg)
    | [], _ => acc
    | step :: rest, old => applyChildrenTR (acc.push (applyChild old step)) rest old
end

def applyChildren (steps : List (KeyedStep msg)) (old : List (Html msg)) : List (Html msg) :=
  steps.map (applyChild old.toArray)

theorem applyChildrenTR_toList (steps : List (KeyedStep msg)) :
    ∀ (acc : Array (Html msg)) (old : Array (Html msg)),
      (applyChildrenTR acc steps old).toList = acc.toList ++ steps.map (applyChild old) := by
  induction steps with
  | nil => intro acc old; simp [applyChildrenTR]
  | cons step rest ih => intro acc old; simp [applyChildrenTR, ih]

mutual
  theorem diff_apply : ∀ (a b : Html msg), applyPatch (diff a b) a = b := by
    intro a b
    cases a <;> cases b <;> try rfl
    case element.element t₁ a₁ c₁ t₂ a₂ c₂ =>
      simp only [diff]
      split
      · rename_i ht; subst ht
        simp only [applyPatch, applyChildrenTR_toList, diffChildrenTR_toList, List.nil_append]
        exact congrArg (Html.element t₁ a₂) (diffChildren_apply c₁ _ 0 c₂)
      · rfl
  theorem diffChildren_apply (old : List (Html msg)) :
      ∀ (pick : Nat → Html msg → Option Nat) (i : Nat) (news : List (Html msg)),
        applyChildren (diffChildren old.toArray pick i news) old = news
    | _, _, [] => rfl
    | pick, i, n :: ns => by
        have tail := diffChildren_apply old pick (i + 1) ns
        simp only [applyChildren] at tail
        cases h : pick i n <;>
          simp [diffChildren, h, applyChildren, applyChild, diff_apply, tail]
end

/-! ## Key-Preserving & Positional Reuse Theorems -/

private theorem validatedKeyIndex_go_spec (cs : List (Html msg)) :
    ∀ (base : Nat) (acc index : Std.HashMap String Nat),
      (∀ (k : String) (j : Nat), acc[k]? = some j → j < base) →
      validatedKeyIndex.go cs base acc = some index →
      (∀ (k : String) (j : Nat), acc[k]? = some j → index[k]? = some j) ∧
      (∀ (k : String) (j : Nat), index[k]? = some j →
        (acc[k]? = some j) ∨ (∃ d, ∃ _ : d < cs.length, j = base + d ∧ cs[d].keyOf = some k)) ∧
      (∀ (d : Nat) (hd : d < cs.length),
        ∃ k, cs[d].keyOf = some k ∧ index[k]? = some (base + d)) := by
  induction cs with
  | nil =>
      intro base acc index _ hgo
      simp only [validatedKeyIndex.go, Option.some.injEq] at hgo
      subst hgo
      exact ⟨fun _ _ h => h, fun _ _ hj => .inl hj, fun _ hd => by simp at hd⟩
  | cons c rest ih =>
      intro base acc index hlt hgo
      simp only [validatedKeyIndex.go] at hgo
      cases hk : c.keyOf with
      | none => simp [hk, bind, Option.bind] at hgo
      | some key =>
          simp only [hk, bind, Option.bind] at hgo
          by_cases hcon : acc.contains key = true
          · simp [hcon] at hgo
          · have hconF : acc.contains key = false := Bool.eq_false_iff.2 hcon
            simp only [hconF, Bool.false_eq_true, ↓reduceIte] at hgo
            have hlt' : ∀ (k : String) (j : Nat), (acc.insert key base)[k]? = some j → j < base + 1 := by
              intro k j hj
              rw [Std.HashMap.getElem?_insert] at hj
              split at hj
              · cases hj; omega
              · exact Nat.lt_trans (hlt k j hj) (Nat.lt_succ_self _)
            rcases ih (base + 1) (acc.insert key base) index hlt' hgo with ⟨ihMono, ihInv, ihElem⟩
            have hkeyNone : acc[key]? = none := by
              have hc : acc[key]?.isSome = false := by
                rw [← Std.HashMap.contains_eq_isSome_getElem?]; exact hconF
              cases hacc : acc[key]? with
              | none => rfl
              | some _ => simp [hacc] at hc
            have hkeyIns : (acc.insert key base)[key]? = some base := by
              rw [Std.HashMap.getElem?_insert, if_pos (beq_self_eq_true key)]
            refine ⟨?_, ?_, ?_⟩
            · intro k j hkAcc
              have hne : (key == k) = false := by
                cases hb : (key == k) with
                | false => rfl
                | true =>
                    have heq : key = k := eq_of_beq hb
                    subst heq; rw [hkeyNone] at hkAcc; cases hkAcc
              apply ihMono
              rw [Std.HashMap.getElem?_insert, if_neg (by simp [hne])]
              exact hkAcc
            · intro k j hkIdx
              rcases ihInv k j hkIdx with hkIns | ⟨d, hd, hjd, hcd⟩
              · rw [Std.HashMap.getElem?_insert] at hkIns
                split at hkIns
                · rename_i hbeq
                  have heq : key = k := eq_of_beq hbeq
                  subst heq
                  cases hkIns
                  exact .inr ⟨0, by simp, by omega, hk⟩
                · exact .inl hkIns
              · exact .inr ⟨d + 1, by simp only [List.length_cons]; omega, by omega, hcd⟩
            · intro d hd
              cases d with
              | zero =>
                  exact ⟨key, hk, ihMono key base hkeyIns⟩
              | succ d' =>
                  simp only [List.length_cons, Nat.succ_lt_succ_iff] at hd
                  rcases ihElem d' hd with ⟨k', hk', hidx'⟩
                  refine ⟨k', hk', ?_⟩
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hidx'

theorem validatedKeyIndex_spec {cs : List (Html msg)} {index : Std.HashMap String Nat}
    (hval : validatedKeyIndex cs = some index) :
    (∀ (k : String) (j : Nat), index[k]? = some j → ∃ _ : j < cs.length, cs[j].keyOf = some k) ∧
    (∀ (j : Nat) (hj : j < cs.length), ∃ k, cs[j].keyOf = some k ∧ index[k]? = some j) := by
  have hgo := validatedKeyIndex_go_spec cs 0 ∅ index (fun _ _ h => by simp at h) hval
  rcases hgo with ⟨_, hInv, hElem⟩
  refine ⟨?_, ?_⟩
  · intro k j hj
    rcases hInv k j hj with hEmp | ⟨d, hd, hjd, hcd⟩
    · simp at hEmp
    · subst hjd
      exact ⟨by simpa using hd, by simpa using hcd⟩
  · intro j hj
    simpa using hElem j hj

theorem diffChildren_length (oldArr : Array (Html msg)) (pick : Nat → Html msg → Option Nat)
    (news : List (Html msg)) (i : Nat) :
    (diffChildren oldArr pick i news).length = news.length := by
  induction news generalizing i with
  | nil => rfl
  | cons n ns ih => simp [diffChildren, ih]

theorem diffChildren_getElem (oldArr : Array (Html msg)) (pick : Nat → Html msg → Option Nat)
    (news : List (Html msg)) :
    ∀ (i idx : Nat) (hidx : idx < news.length),
      (diffChildren oldArr pick i news)[idx]'(by rw [diffChildren_length]; exact hidx) =
        match pick (i + idx) news[idx] with
        | some j => .reuse j (diff (oldArr.getD j default) news[idx])
        | none   => .create news[idx] := by
  induction news with
  | nil => intro i idx hidx; simp at hidx
  | cons n ns ih =>
      intro i idx hidx
      cases idx with
      | zero =>
          simp [diffChildren]
      | succ k =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at hidx
          simp only [diffChildren, List.getElem_cons_succ]
          exact ih (i + 1) k hidx |>.trans (by simp [Nat.add_comm, Nat.add_left_comm])

theorem diff_keyed_reuses {t : String} {a₁ a₂ : List (Attr msg)} {c₁ c₂ : List (Html msg)}
    {idx₁ idx₂ : Std.HashMap String Nat}
    (h₁ : validatedKeyIndex c₁ = some idx₁)
    (h₂ : validatedKeyIndex c₂ = some idx₂) :
    ∃ steps,
      diff (.element t a₁ c₁) (.element t a₂ c₂) = .patchElement a₂ steps ∧
      ∃ (hlen : steps.length = c₂.length),
      ∀ (i : Nat) (hi : i < c₂.length),
        (∀ (j : Nat) (hj : j < c₁.length) (k : String),
          c₂[i].keyOf = some k → c₁[j].keyOf = some k →
          steps[i]'(hlen ▸ hi) = .reuse j (diff c₁[j] c₂[i])) ∧
        (∀ (k : String),
          c₂[i].keyOf = some k → (∀ (j : Nat) (hj : j < c₁.length), c₁[j].keyOf ≠ some k) →
          steps[i]'(hlen ▸ hi) = .create c₂[i]) := by
  let pick := fun (_ : Nat) (n : Html msg) => n.keyOf.bind (fun k => idx₁[k]?)
  let steps := (diffChildrenTR c₁.toArray pick #[] 0 c₂).toList
  have hstepsEq : steps = diffChildren c₁.toArray pick 0 c₂ := by
    simp [steps, diffChildrenTR_toList]
  have hlen : steps.length = c₂.length := by
    simp [hstepsEq, diffChildren_length]
  refine ⟨steps, ?_, hlen, ?_⟩
  · simp [diff, h₁, h₂, steps, pick]
  · intro i hi
    have hget : steps[i]'(hlen ▸ hi) =
        match pick (0 + i) c₂[i] with
        | some j => .reuse j (diff (c₁.toArray.getD j default) c₂[i])
        | none   => .create c₂[i] := by
      have hraw := diffChildren_getElem c₁.toArray pick c₂ 0 i hi
      simpa [hstepsEq] using hraw
    have ⟨hspec1, hspec2⟩ := validatedKeyIndex_spec h₁
    refine ⟨?_, ?_⟩
    · intro j hj k hk₂ hk₁
      obtain ⟨k', hk'₁, hidxk'⟩ := hspec2 j hj
      rw [hk₁] at hk'₁
      cases hk'₁
      have hpick : pick (0 + i) c₂[i] = some j := by
        simp [pick, hk₂, hidxk']
      rw [hget, hpick]
      have hgetD : c₁.toArray.getD j default = c₁[j] := by
        simp [Array.getD, hj]
      simp [hgetD]
    · intro k hk₂ hnone
      have hnoneIdx : idx₁[k]? = none := by
        cases hq : idx₁[k]? with
        | none => rfl
        | some j =>
            obtain ⟨hj, hcj⟩ := hspec1 k j hq
            exact False.elim (hnone j hj hcj)
      have hpick : pick (0 + i) c₂[i] = none := by
        simp [pick, hk₂, hnoneIdx]
      rw [hget, hpick]

theorem diff_positional_reuses {t : String} {a₁ a₂ : List (Attr msg)} {c₁ c₂ : List (Html msg)}
    (hunkeyed : validatedKeyIndex c₁ = none ∨ validatedKeyIndex c₂ = none) :
    ∃ steps,
      diff (.element t a₁ c₁) (.element t a₂ c₂) = .patchElement a₂ steps ∧
      ∃ (hlen : steps.length = c₂.length),
      ∀ (i : Nat) (hi : i < c₂.length),
        (∀ (hi1 : i < c₁.length), steps[i]'(hlen ▸ hi) = .reuse i (diff c₁[i] c₂[i])) ∧
        (c₁.length ≤ i → steps[i]'(hlen ▸ hi) = .create c₂[i]) := by
  let pick := fun i (_ : Html msg) => if i < c₁.toArray.size then some i else none
  let steps := (diffChildrenTR c₁.toArray pick #[] 0 c₂).toList
  have hstepsEq : steps = diffChildren c₁.toArray pick 0 c₂ := by
    simp [steps, diffChildrenTR_toList]
  have hlen : steps.length = c₂.length := by
    simp [hstepsEq, diffChildren_length]
  have hdiffEq : diff (.element t a₁ c₁) (.element t a₂ c₂) = .patchElement a₂ steps := by
    rcases hunkeyed with h1 | h2
    · simp [diff, h1, steps, pick]
    · cases h1 : validatedKeyIndex c₁ <;> simp [diff, h1, h2, steps, pick]
  refine ⟨steps, hdiffEq, hlen, ?_⟩
  intro i hi
  have hget : steps[i]'(hlen ▸ hi) =
      match pick (0 + i) c₂[i] with
      | some j => .reuse j (diff (c₁.toArray.getD j default) c₂[i])
      | none   => .create c₂[i] := by
    have hraw := diffChildren_getElem c₁.toArray pick c₂ 0 i hi
    simpa [hstepsEq] using hraw
  refine ⟨?_, ?_⟩
  · intro hi1
    have hsz : i < c₁.toArray.size := by simpa using hi1
    rw [hget, Nat.zero_add]
    simp only [pick, hsz, ↓reduceIte]
    have hgetD : c₁.toArray.getD i default = c₁[i] := by simp [Array.getD, hi1]
    simp [hgetD]
  · intro hge
    have hnot : ¬ i < c₁.length := Nat.not_lt_of_ge hge
    rw [hget, Nat.zero_add]
    simp [pick, hnot]

end Qed
