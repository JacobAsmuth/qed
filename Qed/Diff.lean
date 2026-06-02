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

  Children are reconciled through **one** path: a list of `KeyedStep`s, each naming an
  old child to reuse (patched in place) or a new one to build. The two reconcile
  *strategies* differ only in how each new child is matched to an old one — the `pick`
  function handed to `diffChildren`:

  * **Positionally** (the default): the i-th new child reuses the i-th old child, so a
    common prefix is patched pairwise, then surplus new children are created and surplus
    old ones dropped. Adding/removing at the end is exact; a removal in the middle shifts
    the rows below it.
  * **By key** (`Attr.key`, like React/Vue): when every new child carries a key, a child
    is matched to the old child with the same key, so a *reordered* or *middle-removed*
    row keeps its own DOM node (and the focus/scroll inside it).

  The correctness proof is **`pick`-agnostic**: a `reuse j` step stores `diff oldChild
  newChild`, and `applyPatch (diff x n) x = n` holds for *any* `x` by `diff_apply`, so the
  matcher only affects *which* node is reused (identity), never the result (correctness).
  That is what lets positional and keyed share one function and one theorem. A node whose
  *tag* changes is still replaced wholesale.
-/
import Qed.Html
import Std.Data.HashMap

namespace Qed

/-- A child's reconciliation key, if it set one (an element with an `Attr.key`, or a
    `lazy` wrapping one — so a memoized row still reconciles by its stable key while its
    `lazy` key tracks content). -/
def Html.keyOf : Html msg → Option String
  | .element _ attrs _ => attrs.findSome? (fun a => match a with | .key k => some k | _ => none)
  | .lazy _ sub        => Html.keyOf sub
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
    /-- Same-tag elements: install the new attributes and rebuild the child list from
        `steps` (each names an old child to reuse, or a new one to create), in the new
        order. Positional and keyed reconcile both produce this — they differ only in how
        `diffChildren` matched each new child (by position, or by key). -/
    | patchElement (attrs : List (Attr msg)) (steps : List (KeyedStep msg))
    /-- Two `lazy` nodes shared a key: the content is unchanged, so the driver keeps the
        old DOM. Carries the new node (`lazy key sub`) so the *pure* model still produces
        it exactly — only the driver elides the work. -/
    | lazyReuse (key : String) (sub : Html msg)
    /-- Two `lazy` nodes with *different* keys: the content changed, so patch it in place
        (cheaper than rebuilding) and record the new key. -/
    | lazyPatch (key : String) (sub : Patch msg)
  /-- One entry of a children reconcile, in new-child order. -/
  inductive KeyedStep (msg : Type) where
    /-- Reuse the old child at `oldIndex` (matched by position or key), patched with `p`. -/
    | reuse (oldIndex : Nat) (p : Patch msg)
    /-- No old child matched: build `h` fresh. -/
    | create (h : Html msg)
end

mutual
  /-- Compute the patch from `old` to `new`. Recurses on the *new* tree; the old
      tree is only ever read (positionally, or by key lookup), never recursed into —
      which is what lets the matched `diff (oldArr.getD j …) n` call in `diffChildren`
      terminate (its second argument `n` is a child of the new tree). -/
  def diff : Html msg → Html msg → Patch msg
    | .text _,          .text s          => .setText s
    | .element t₁ _ c₁, .element t₂ a₂ c₂ =>
        if t₁ = t₂ then
          let oldArr := c₁.toArray
          -- one reconcile; only the matcher differs. Keyed: match by key (`keyIndex` built
          -- once, so lookup is O(1)). Positional: the i-th new child reuses the i-th old one.
          let pick : Nat → Html msg → Option Nat :=
            if childrenKeyed c₂ then
              let km := keyIndex c₁
              fun _ n => (Html.keyOf n).bind (fun k => km[k]?)
            else
              fun i _ => if i < oldArr.size then some i else none
          .patchElement a₂ (diffChildren oldArr pick 0 c₂)
        else .replace (.element t₂ a₂ c₂)
    | .lazy k₁ s₁,      .lazy k₂ s₂      =>
        -- same key ⇒ unchanged: skip without diffing `s₂`; else patch the content
        if k₁ = k₂ then .lazyReuse k₂ s₂ else .lazyPatch k₂ (diff s₁ s₂)
    | _,                b                 => .replace b
  /-- The one children reconcile. For each new child (in order) `pick` chooses which old
      child to reuse — by position or by key — patched in place; `none` builds it fresh.
      Surplus old children are simply never referenced (so they drop). `pick` is a pure
      performance/identity choice: whatever index it returns, `diff` patches that old child
      into the new one exactly, so it carries no proof obligation (`diffChildren_apply`). -/
  def diffChildren (oldArr : Array (Html msg)) (pick : Nat → Html msg → Option Nat) :
      Nat → List (Html msg) → List (KeyedStep msg)
    | _, []      => []
    | i, n :: ns =>
        (match pick i n with
         | some j => .reuse j (diff (oldArr.getD j default) n)
         | none   => .create n) :: diffChildren oldArr pick (i + 1) ns
end

mutual
  /-- The pure model of applying a patch to a node. -/
  def applyPatch : Patch msg → Html msg → Html msg
    | .replace new,              _                       => new
    | .setText s,                _                       => .text s
    | .patchElement attrs steps, .element tag _ children => .element tag attrs (applyChildren steps children)
    | .lazyReuse key sub,        _                       => .lazy key sub
    | .lazyPatch key p,          .lazy _ s               => .lazy key (applyPatch p s)
    | .lazyPatch key p,          h                       => .lazy key (applyPatch p h)
    | .patchElement _ _,         h                       => h
  /-- Apply a children reconcile: each step yields one new child, reusing the old child
      at its recorded index or building a fresh one. -/
  def applyChildren : List (KeyedStep msg) → List (Html msg) → List (Html msg)
    | [],                 _   => []
    | .reuse i p :: rest, old => applyPatch p (old.toArray.getD i default) :: applyChildren rest old
    | .create h :: rest,  old => h :: applyChildren rest old
end

mutual
  /-- **Correctness:** patching `a` with `diff a b` reproduces `b` exactly. The element
      case is one branch for both reconcile strategies: `diffChildren_apply` is
      `pick`-agnostic, so positional and keyed close identically. -/
  theorem diff_apply : ∀ (a b : Html msg), applyPatch (diff a b) a = b
    | .text _,           .text s           => by simp [diff, applyPatch]
    | .text _,           .element _ _ _    => by simp [diff, applyPatch]
    | .element _ _ _,    .text _           => by simp [diff, applyPatch]
    | .element t₁ a₁ c₁, .element t₂ a₂ c₂ => by
        simp only [diff]
        split
        · rename_i ht
          subst ht
          simp only [applyPatch]; rw [diffChildren_apply c₁]
        · simp only [applyPatch]
    -- a `lazyReuse` (same key) and a `lazyPatch` (different key, carrying `diff s₁ s₂`)
    -- both reproduce the new node exactly — no appeal to the equal-key promise here.
    | .lazy k₁ s₁,       .lazy k₂ s₂       => by
        simp only [diff]
        split
        · simp [applyPatch]
        · simp only [applyPatch]; rw [diff_apply s₁ s₂]
    | .lazy _ _,         .text _           => by simp [diff, applyPatch]
    | .lazy _ _,         .element _ _ _    => by simp [diff, applyPatch]
    | .text _,           .lazy _ _         => by simp [diff, applyPatch]
    | .element _ _ _,    .lazy _ _         => by simp [diff, applyPatch]
  /-- The children analogue, for child lists of any lengths and **any matcher**: whichever
      old child `pick` returns, patching it with the recorded `diff` reproduces the new child
      (`diff_apply`), so the rebuilt list equals the new children exactly. Holding for every
      `pick`/`i` is what lets positional and keyed reconcile share this one proof — the
      matcher carries no correctness obligation. -/
  theorem diffChildren_apply (old : List (Html msg)) :
      ∀ (pick : Nat → Html msg → Option Nat) (i : Nat) (news : List (Html msg)),
        applyChildren (diffChildren old.toArray pick i news) old = news
    | _,    _, []      => by simp [diffChildren, applyChildren]
    | pick, i, n :: ns => by
        simp only [diffChildren]
        split
        · rename_i j _
          simp only [applyChildren]
          rw [diff_apply (old.toArray.getD j default) n, diffChildren_apply old pick (i + 1) ns]
        · simp only [applyChildren]; rw [diffChildren_apply old pick (i + 1) ns]
end

end Qed
