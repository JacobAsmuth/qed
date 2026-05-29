/-
  Qed.Diff — a virtual-DOM diff/patch engine, proven correct.

  `diff old new` computes a minimal-ish `Patch`; `applyPatch` is the *pure model*
  of applying it. The correctness theorem

      diff_apply : applyPatch (diff a b) a = b

  says the patched tree is *exactly* the new tree your `view` produced — so the
  incremental update path can never drift from the source of truth. The impure
  applier in `Qed.Driver` mirrors `applyPatch` onto real DOM nodes (preserving
  node identity, hence focus/scroll/selection), and that thin mirror is all that
  remains trusted.

  Scope: this version diffs children *positionally* and falls back to a wholesale
  `replace` when the tag or child count differs. Keyed reconciliation (matching
  moved children) is a later milestone; the proof here is exact for the
  fixed-structure case that covers most views.
-/
import Qed.Html

namespace Qed

/-- A description of how to turn one `Html` node into another. -/
inductive Patch (msg : Type) where
  /-- Replace the node wholesale (tag changed, or text ↔ element). -/
  | replace (new : Html msg)
  /-- Both nodes are text; set the content. -/
  | setText (content : String)
  /-- Both nodes are elements with the same tag and child count: install the new
      attributes and patch each child in place. -/
  | patchElement (attrs : List (Attr msg)) (kids : List (Patch msg))

mutual
  /-- Compute the patch from `old` to `new`. -/
  def diff : Html msg → Html msg → Patch msg
    | .text _,           .text s            => .setText s
    | .element t₁ _ c₁,  .element t₂ a₂ c₂  =>
        if t₁ = t₂ ∧ c₁.length = c₂.length then
          .patchElement a₂ (diffList c₁ c₂)
        else
          .replace (.element t₂ a₂ c₂)
    | _,                 b                  => .replace b
  /-- Diff two child lists pairwise (used only when lengths match). -/
  def diffList : List (Html msg) → List (Html msg) → List (Patch msg)
    | a :: as, b :: bs => diff a b :: diffList as bs
    | _,       _       => []
end

mutual
  /-- The pure model of applying a patch to a node. -/
  def applyPatch : Patch msg → Html msg → Html msg
    | .replace new,             _                      => new
    | .setText s,               _                      => .text s
    | .patchElement attrs kids, .element tag _ children => .element tag attrs (applyList kids children)
    | .patchElement _ _,        h                      => h
  /-- Apply a list of child patches pairwise. -/
  def applyList : List (Patch msg) → List (Html msg) → List (Html msg)
    | p :: ps, c :: cs => applyPatch p c :: applyList ps cs
    | _,       _       => []
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
        · rename_i h
          obtain ⟨ht, hlen⟩ := h
          subst ht
          simp only [applyPatch]
          rw [diffList_apply c₁ c₂ hlen]
        · simp only [applyPatch]
  /-- The child-list analogue, used by `diff_apply`. -/
  theorem diffList_apply :
      ∀ (as bs : List (Html msg)), as.length = bs.length → applyList (diffList as bs) as = bs
    | [],      [],      _ => by simp [diffList, applyList]
    | a :: as, b :: bs, h => by
        have hlen : as.length = bs.length := by simp only [List.length_cons] at h; omega
        simp only [diffList, applyList]
        rw [diff_apply a b, diffList_apply as bs hlen]
    | [],      _ :: _,  h => by simp at h
    | _ :: _,  [],      h => by simp at h
end

end Qed
