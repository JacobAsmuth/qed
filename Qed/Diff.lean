/-
  Qed.Diff — a virtual-DOM diff/patch engine, proven correct.

  `diff old new` computes a `Patch`; `applyPatch` is the *pure model* of applying
  it. The correctness theorem

      diff_apply : applyPatch (diff a b) a = b

  says the patched tree is *exactly* the new tree your `view` produced — so the
  incremental update path can never drift from the source of truth. The impure
  applier in `Qed.Driver` mirrors `applyPatch` onto real DOM nodes (preserving
  node identity, hence focus/scroll/selection), and that thin mirror is all that
  remains trusted.

  Children are reconciled in one of two ways:

  * **Positionally** (the default): a common prefix is patched pairwise, then the
    extra new children are appended or the extra old ones dropped. Adding/removing
    at the end is exact; a removal in the middle shifts the rows below it.
  * **By key** (`Attr.key`, like React/Vue): when every new child carries a key, a
    child is matched to the previous child with the same key, so a *reordered* or
    *middle-removed* row keeps its own DOM node (and the focus/scroll inside it).

  The correctness proof covers both: a keyed `reuse` step stores `diff oldChild
  newChild`, and `applyPatch (diff x n) x = n` holds for *any* `x` by `diff_apply`,
  so the key-matching heuristic only affects *which* node is reused (identity),
  never the result (correctness). A node whose *tag* changes is still replaced
  wholesale.
-/
import Qed.Html

namespace Qed

/-- A child's reconciliation key, if it set one (an element with an `Attr.key`). -/
def Html.keyOf : Html msg → Option String
  | .element _ attrs _ => attrs.findSome? (fun a => match a with | .key k => some k | _ => none)
  | _                  => none

/-- Reconcile this child list by key? Only when *every* child carries one. -/
def childrenKeyed (cs : List (Html msg)) : Bool := cs.all (fun c => (Html.keyOf c).isSome)

/-- The index of the old child carrying `key`, if any. -/
def findKeyIdx (old : List (Html msg)) (key : String) : Option Nat :=
  old.findIdx? (fun o => Html.keyOf o == some key)

mutual
  /-- A description of how to turn one `Html` node into another. -/
  inductive Patch (msg : Type) where
    /-- Replace the node wholesale (tag changed, or text ↔ element). -/
    | replace (new : Html msg)
    /-- Both nodes are text; set the content. -/
    | setText (content : String)
    /-- Same-tag elements, positional children: install the new attributes and
        reconcile the children with `kids`. -/
    | patchElement (attrs : List (Attr msg)) (kids : ChildPatch msg)
    /-- Same-tag elements, keyed children: install the new attributes and rebuild
        the child list from `steps` (each names an old child to reuse, or a new one
        to create), in the new order. -/
    | patchKeyed (attrs : List (Attr msg)) (steps : List (KeyedStep msg))
  /-- How to turn one list of children into another, walking them in parallel. -/
  inductive ChildPatch (msg : Type) where
    /-- Patch the next old child with `p`, then continue with the rest. -/
    | patch (p : Patch msg) (rest : ChildPatch msg)
    /-- The old children ran out: append these new children (empty when the lists
        had equal length). -/
    | append (news : List (Html msg))
    /-- The new children ran out: drop every remaining old child. -/
    | drop
  /-- One entry of a keyed reconcile, in new-child order. -/
  inductive KeyedStep (msg : Type) where
    /-- Reuse the old child at `oldIndex` (matched by key), patched with `p`. -/
    | reuse (oldIndex : Nat) (p : Patch msg)
    /-- No old child had this key: build `h` fresh. -/
    | create (h : Html msg)
end

mutual
  /-- Compute the patch from `old` to `new`. Recurses on the *new* tree; the old
      tree is only ever read (positionally, or by key lookup), never recursed into —
      which is what lets the key-matched `diff (old.getD i …) n` call below
      terminate (its second argument `n` is a child of the new tree). -/
  def diff : Html msg → Html msg → Patch msg
    | .text _,          .text s          => .setText s
    | .element t₁ _ c₁, .element t₂ a₂ c₂ =>
        if t₁ = t₂ then
          if childrenKeyed c₂ then .patchKeyed a₂ (diffKeyed c₁ c₂)
          else .patchElement a₂ (diffChildren c₁ c₂)
        else .replace (.element t₂ a₂ c₂)
    | _,                b                 => .replace b
  /-- Positional reconcile: a pairwise-patched prefix, then append the surplus new
      children or drop the surplus old ones. -/
  def diffChildren : List (Html msg) → List (Html msg) → ChildPatch msg
    | a :: as, b :: bs => .patch (diff a b) (diffChildren as bs)
    | [],      bs      => .append bs
    | _ :: _,  []      => .drop
  /-- Keyed reconcile: for each new child (in order) reuse the like-keyed old child
      patched in place, else create it fresh. -/
  def diffKeyed : List (Html msg) → List (Html msg) → List (KeyedStep msg)
    | _,   []      => []
    | old, n :: ns =>
        (match Html.keyOf n with
         | some k => match findKeyIdx old k with
                     | some i => .reuse i (diff (old.getD i default) n)
                     | none   => .create n
         | none   => .create n) :: diffKeyed old ns
end

mutual
  /-- The pure model of applying a patch to a node. -/
  def applyPatch : Patch msg → Html msg → Html msg
    | .replace new,             _                       => new
    | .setText s,               _                       => .text s
    | .patchElement attrs kids, .element tag _ children => .element tag attrs (applyChildren kids children)
    | .patchKeyed attrs steps,  .element tag _ children => .element tag attrs (applyKeyed steps children)
    | .patchElement _ _,        h                       => h
    | .patchKeyed _ _,          h                       => h
  /-- Apply a positional child-list patch to a list of children. -/
  def applyChildren : ChildPatch msg → List (Html msg) → List (Html msg)
    | .patch p rest, c :: cs => applyPatch p c :: applyChildren rest cs
    | .patch _ _,    []      => []
    | .append ns,    _       => ns
    | .drop,         _       => []
  /-- Apply a keyed reconcile: each step yields one new child, reusing the old child
      at its recorded index or building a fresh one. -/
  def applyKeyed : List (KeyedStep msg) → List (Html msg) → List (Html msg)
    | [],                _   => []
    | .reuse i p :: rest, old => applyPatch p (old.getD i default) :: applyKeyed rest old
    | .create h :: rest,  old => h :: applyKeyed rest old
end

mutual
  /-- **Correctness:** patching `a` with `diff a b` reproduces `b` exactly. -/
  theorem diff_apply : ∀ (a b : Html msg), applyPatch (diff a b) a = b
    | .text _,           .text s           => by simp [diff, applyPatch]
    | .text _,           .element _ _ _    => by simp [diff, applyPatch]
    | .element _ _ _,    .text _           => by simp [diff, applyPatch]
    | .element t₁ a₁ c₁, .element t₂ a₂ c₂ => by
        simp only [diff]
        split
        · rename_i ht
          subst ht
          split
          · simp only [applyPatch]; rw [diffKeyed_apply c₁ c₂]
          · simp only [applyPatch]; rw [diffChildren_apply c₁ c₂]
        · simp only [applyPatch]
  /-- The positional child-list analogue. Holds for child lists of any lengths. -/
  theorem diffChildren_apply :
      ∀ (as bs : List (Html msg)), applyChildren (diffChildren as bs) as = bs
    | [],      _       => by simp [diffChildren, applyChildren]
    | a :: as, b :: bs => by
        simp only [diffChildren, applyChildren]
        rw [diff_apply a b, diffChildren_apply as bs]
    | _ :: _,  []      => by simp [diffChildren, applyChildren]
  /-- The keyed analogue: whichever old child a key matched, patching it with the
      recorded `diff` reproduces the new child (`diff_apply`), so the rebuilt list
      equals the new children exactly. -/
  theorem diffKeyed_apply :
      ∀ (old new : List (Html msg)), applyKeyed (diffKeyed old new) old = new
    | _,   []      => by simp [diffKeyed, applyKeyed]
    | old, n :: ns => by
        simp only [diffKeyed]
        split
        · split
          · rename_i i _
            simp only [applyKeyed]
            rw [diff_apply (old.getD i default) n, diffKeyed_apply old ns]
          · simp only [applyKeyed]; rw [diffKeyed_apply old ns]
        · simp only [applyKeyed]; rw [diffKeyed_apply old ns]
end

end Qed
