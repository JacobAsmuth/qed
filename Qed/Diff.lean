/-
  Qed.Diff — a virtual-DOM diff/patch engine, proven correct.

  `diff old new` computes a `Patch`; `applyPatch` is the *pure model* of applying
  it. The correctness theorem

      diff_apply : applyPatch (diff a b) a = b

  says the patched tree is *exactly* the new tree your `view` produced — so the
  pure incremental update agrees with a fresh tree. The impure applier in `Qed.Driver`
  implements these operations on live nodes; browser differential tests check that boundary.

  Children are reconciled through **one** path: a list of `KeyedStep`s, each naming an
  old child to reuse (patched in place) or a new one to build. The two reconcile
  *strategies* differ only in how each new child is matched to an old one — the `pick`
  function handed to `diffChildren`:

  * **Positionally** (the default): the i-th new child reuses the i-th old child, so a
    common prefix is patched pairwise, then surplus new children are created and surplus
    old ones dropped. Adding/removing at the end is exact; a removal in the middle shifts
    the rows below it.
  * **By key** (`Attr.key`, like React/Vue): when both lists have distinct keys, a child
    is matched to the old child with the same key, so a *reordered* or *middle-removed*
    row keeps its own DOM node (and the focus/scroll inside it).

  The correctness proof is **`pick`-agnostic**: a `reuse j` step stores `diff oldChild
  newChild`, and `applyPatch (diff x n) x = n` holds for *any* `x` by `diff_apply`, so the
  matcher only affects *which* pure subtree is reused, never the resulting pure tree.
  The DOM additionally requires distinct, in-bounds reuse indices: one node cannot occupy
  two positions. Duplicate or missing sibling keys therefore use positional matching.
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

/-- Validate distinct sibling keys and index them in one traversal. Missing or duplicate
    keys stop immediately; the resulting map can be reused directly by the matcher. -/
def validatedKeyIndex (cs : List (Html msg)) : Option (Std.HashMap String Nat) :=
  go cs 0 ∅
where
  go : List (Html msg) → Nat → Std.HashMap String Nat → Option (Std.HashMap String Nat)
    | [], _, index => some index
    | c :: rest, i, index => do
        let key ← c.keyOf
        if index.contains key then none else go rest (i + 1) (index.insert key i)

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
      which is what lets the matched `diff (oldArr.getD j …) n` call in `diffChildrenTR`
      terminate (its second argument `n` is a child of the new tree). -/
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
        -- same key ⇒ unchanged: skip without diffing `s₂`; else patch the content
        if k₁ = k₂ then .lazyReuse k₂ s₂ else .lazyPatch k₂ (diff s₁ s₂)
    | _,                b                 => .replace b
  /-- The one children reconcile, tail-recursive over the new children (accumulating into
      `acc`), so it runs in O(1) JS stack for a list of any length. For each new child
      `pick` chooses which old child to reuse — by position or by key — patched in place;
      `none` builds it fresh. `pick` carries no proof obligation (`diffChildren_apply`). -/
  def diffChildrenTR (oldArr : Array (Html msg)) (pick : Nat → Html msg → Option Nat)
      (acc : Array (KeyedStep msg)) : Nat → List (Html msg) → Array (KeyedStep msg)
    | _, []      => acc
    | i, n :: ns =>
        diffChildrenTR oldArr pick (acc.push (match pick i n with
          | some j => .reuse j (diff (oldArr.getD j default) n)
          | none   => .create n)) (i + 1) ns
end

/-- The structural model of the children reconcile — the spec `diff_apply` reasons about.
    The runtime form `diffChildrenTR` is proven to produce exactly this (`diffChildrenTR_toList`). -/
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
  /-- The pure model of applying a patch to a node. -/
  def applyPatch : Patch msg → Html msg → Html msg
    | .replace new,              _                       => new
    | .setText s,                _                       => .text s
    | .patchElement attrs steps, .element tag _ children => .element tag attrs (applyChildrenTR #[] steps children.toArray).toList
    | .lazyReuse key sub,        _                       => .lazy key sub
    | .lazyPatch key p,          .lazy _ s               => .lazy key (applyPatch p s)
    | .lazyPatch key p,          h                       => .lazy key (applyPatch p h)
    | .patchElement _ _,         h                       => h
  /-- Interpret one child step against the old children, indexed once by the caller. -/
  def applyChild (old : Array (Html msg)) : KeyedStep msg → Html msg
    | .reuse i p => applyPatch p (old.getD i default)
    | .create h => h
  /-- Tail-recursive traversal, sharing the same step interpretation as the structural spec. -/
  def applyChildrenTR (acc : Array (Html msg)) :
      List (KeyedStep msg) → Array (Html msg) → Array (Html msg)
    | [], _ => acc
    | step :: rest, old => applyChildrenTR (acc.push (applyChild old step)) rest old
end

/-- Structural specification: interpret each step against one snapshot of the old children. -/
def applyChildren (steps : List (KeyedStep msg)) (old : List (Html msg)) : List (Html msg) :=
  steps.map (applyChild old.toArray)

theorem applyChildrenTR_toList (steps : List (KeyedStep msg)) :
    ∀ (acc : Array (Html msg)) (old : Array (Html msg)),
      (applyChildrenTR acc steps old).toList = acc.toList ++ steps.map (applyChild old) := by
  induction steps with
  | nil => intro acc old; simp [applyChildrenTR]
  | cons step rest ih => intro acc old; simp [applyChildrenTR, ih]

mutual
  /-- **Correctness:** patching `a` with `diff a b` reproduces `b` exactly. The element
      case is one branch for both reconcile strategies: `diffChildren_apply` is
      `pick`-agnostic, so positional and keyed close identically. -/
  theorem diff_apply : ∀ (a b : Html msg), applyPatch (diff a b) a = b := by
    intro a b
    cases a <;> cases b <;> try rfl
    case element.element t₁ a₁ c₁ t₂ a₂ c₂ =>
      simp only [diff]
      split
      · rename_i ht
        subst ht
        -- Bridge the runtime traversals to their structural specifications.
        simp only [applyPatch, applyChildrenTR_toList, diffChildrenTR_toList, List.nil_append]
        exact congrArg (Html.element t₁ a₂) (diffChildren_apply c₁ _ 0 c₂)
      · rfl
    -- Both lazy patch forms reproduce the supplied new tree in the pure model.
    case lazy.lazy k₁ s₁ k₂ s₂ =>
      simp only [diff]
      split <;> simp [applyPatch, diff_apply s₁ s₂]
  /-- The children analogue, for child lists of any lengths and **any matcher**: whichever
      old child `pick` returns, patching it with the recorded `diff` reproduces the new child
      (`diff_apply`), so the rebuilt list equals the new children exactly. Holding for every
      `pick`/`i` is what lets positional and keyed reconcile share this one proof — the
      matcher carries no correctness obligation. -/
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
