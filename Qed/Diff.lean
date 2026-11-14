import Qed.Html
import Std.Data.HashMap

namespace Qed

def Html.keyOf : Html msg → Option String
  | .element _ attrs _ => attrs.findSome? (fun a => match a with | .key k => some k | _ => none)
  | .lazy _ sub        => Html.keyOf sub
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
    | lazyReuse (key : String) (sub : Html msg)
    | lazyPatch (key : String) (sub : Patch msg)
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
          let positional := fun i (_ : Html msg) => if i < oldArr.size then some i else none
          let pick : Nat → Html msg → Option Nat :=
            match validatedKeyIndex c₁ with
            | some index =>
                if (validatedKeyIndex c₂).isSome then
                  fun _ n => n.keyOf.bind (fun k => index[k]?)
                else positional
            | none => positional
          .patchElement a₂ (diffChildrenTR oldArr pick #[] 0 c₂).toList
        else .replace (.element t₂ a₂ c₂)
    | .lazy k₁ s₁,      .lazy k₂ s₂      =>
        if k₁ = k₂ then .lazyReuse k₂ s₂ else .lazyPatch k₂ (diff s₁ s₂)
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
    | .lazyReuse key sub,        _                       => .lazy key sub
    | .lazyPatch key p,          .lazy _ s               => .lazy key (applyPatch p s)
    | .lazyPatch key p,          h                       => .lazy key (applyPatch p h)
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
      · rename_i ht
        subst ht
        simp only [applyPatch, applyChildrenTR_toList, diffChildrenTR_toList, List.nil_append]
        exact congrArg (Html.element t₁ a₂) (diffChildren_apply c₁ _ 0 c₂)
      · rfl
    case lazy.lazy k₁ s₁ k₂ s₂ =>
      simp only [diff]
      split <;> simp [applyPatch, diff_apply s₁ s₂]
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

end Qed
