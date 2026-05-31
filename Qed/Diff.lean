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
import Std.Data.HashMap

namespace Qed

/-- A child's reconciliation key, if it set one (an element with an `Attr.key`). -/
def Html.keyOf : Html msg → Option String
  | .element _ attrs _ => attrs.findSome? (fun a => match a with | .key k => some k | _ => none)
  | _                  => none

/-- Reconcile this child list by key? Only when *every* child carries one. -/
def childrenKeyed (cs : List (Html msg)) : Bool := cs.all (fun c => (Html.keyOf c).isSome)

/-- Maps each key to the index of the *first* old child carrying it, built once per
    keyed list so the reconcile can look a child up in `O(1)`. Correctness does not
    depend on this map: a wrong or missing index just reuses a different (or default)
    old node, which `diff` still patches into the correct result, so it carries no
    proof obligation. -/
def keyIndex (old : List (Html msg)) : Std.HashMap String Nat :=
  (old.foldl (init := ((∅ : Std.HashMap String Nat), 0)) fun (acc, i) c =>
    match Html.keyOf c with
    | some k => (if acc.contains k then acc else acc.insert k i, i + 1)
    | none   => (acc, i + 1)).1

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
    /-- Two `lazy` nodes shared a key: the content is unchanged, so the driver keeps the
        old DOM. Carries the new node (`lazy key sub`) so the *pure* model still produces
        it exactly — only the driver elides the work. -/
    | lazyReuse (key : String) (sub : Html msg)
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
          if childrenKeyed c₂ then .patchKeyed a₂ (diffKeyed c₁.toArray (keyIndex c₁) c₂)
          else .patchElement a₂ (diffChildren c₁ c₂)
        else .replace (.element t₂ a₂ c₂)
    | .lazy k₁ _,       .lazy k₂ s₂      =>
        -- same key ⇒ unchanged: skip without diffing `s₂`; else rebuild it
        if k₁ = k₂ then .lazyReuse k₂ s₂ else .replace (.lazy k₂ s₂)
    | _,                b                 => .replace b
  /-- Positional reconcile: a pairwise-patched prefix, then append the surplus new
      children or drop the surplus old ones. -/
  def diffChildren : List (Html msg) → List (Html msg) → ChildPatch msg
    | a :: as, b :: bs => .patch (diff a b) (diffChildren as bs)
    | [],      bs      => .append bs
    | _ :: _,  []      => .drop
  /-- Keyed reconcile: for each new child (in order) reuse the like-keyed old child
      patched in place, else create it fresh. The old children come pre-indexed —
      `oldArr` for `O(1)` access by position, `km` for `O(1)` key lookup — so the whole
      reconcile is `O(n)`. -/
  def diffKeyed (oldArr : Array (Html msg)) (km : Std.HashMap String Nat) :
      List (Html msg) → List (KeyedStep msg)
    | []      => []
    | n :: ns =>
        (match Html.keyOf n with
         | some k => match km[k]? with
                     | some i => .reuse i (diff (oldArr.getD i default) n)
                     | none   => .create n
         | none   => .create n) :: diffKeyed oldArr km ns
end

mutual
  /-- The pure model of applying a patch to a node. -/
  def applyPatch : Patch msg → Html msg → Html msg
    | .replace new,             _                       => new
    | .setText s,               _                       => .text s
    | .patchElement attrs kids, .element tag _ children => .element tag attrs (applyChildren kids children)
    | .patchKeyed attrs steps,  .element tag _ children => .element tag attrs (applyKeyed steps children)
    | .lazyReuse key sub,       _                       => .lazy key sub
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
    | .reuse i p :: rest, old => applyPatch p (old.toArray.getD i default) :: applyKeyed rest old
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
    -- a `lazyReuse` (same key) and a `replace` (different key) both yield the new node,
    -- so the model is exact either way — no appeal to the equal-key promise here.
    | .lazy _ _,         .lazy _ _         => by simp only [diff]; split <;> simp [applyPatch]
    | .lazy _ _,         .text _           => by simp [diff, applyPatch]
    | .lazy _ _,         .element _ _ _    => by simp [diff, applyPatch]
    | .text _,           .lazy _ _         => by simp [diff, applyPatch]
    | .element _ _ _,    .lazy _ _         => by simp [diff, applyPatch]
  /-- The positional child-list analogue. Holds for child lists of any lengths. -/
  theorem diffChildren_apply :
      ∀ (as bs : List (Html msg)), applyChildren (diffChildren as bs) as = bs
    | [],      _       => by simp [diffChildren, applyChildren]
    | a :: as, b :: bs => by
        simp only [diffChildren, applyChildren]
        rw [diff_apply a b, diffChildren_apply as bs]
    | _ :: _,  []      => by simp [diffChildren, applyChildren]
  /-- The keyed analogue: whichever old child the key map pointed at, patching it with
      the recorded `diff` reproduces the new child (`diff_apply`), so the rebuilt list
      equals the new children exactly. The proof holds for *any* index the map returns,
      so the map itself needs no correctness proof. -/
  theorem diffKeyed_apply :
      ∀ (old new : List (Html msg)),
        applyKeyed (diffKeyed old.toArray (keyIndex old) new) old = new
    | _,   []      => by simp [diffKeyed, applyKeyed]
    | old, n :: ns => by
        simp only [diffKeyed]
        split
        · split
          · rename_i i _
            simp only [applyKeyed]
            rw [diff_apply (old.toArray.getD i default) n, diffKeyed_apply old ns]
          · simp only [applyKeyed]; rw [diffKeyed_apply old ns]
        · simp only [applyKeyed]; rw [diffKeyed_apply old ns]
end

end Qed
