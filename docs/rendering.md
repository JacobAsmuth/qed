# Rendering proofs and browser checks

Qed views have a pure specification—rendering a `View` at state `s` produces an `Html` value—and
an imperative browser driver that updates live DOM nodes in place. Qed connects the two with
Lean refinement proofs over a pure DOM model and differential tests running in real Chromium.

## Pure specs and driver proofs

At the pure `Html` and `View` layer:

- **`diff_apply`** (`Qed/Diff.lean`) proves that diffing an old `Html` tree against a new one
  and applying the resulting patch yields the exact new `Html` tree.
- **`applyValues_render` and `patch_render`** (`Qed/View/Core.lean`) prove that updating dynamic
  bindings in place when a template's structure is stable—and falling back to a tree diff when
  branches flip—always matches `View.render`.
- **Conditionals (`showIf` / `ifElse`):** `showIf` lowers to `ifElse` with an empty text branch
  so rendering, patching, and hydration share a single conditional path. Hidden branches reserve
  their signal indices so sibling bindings stay aligned, and a branch that remains hidden stays
  structurally stable regardless of changes inside it.

In [`Qed/Proofs/DomEquiv.lean`](../Qed/Proofs/DomEquiv.lean), these theorems are lifted to the
imperative `MonadDom` driver (`Qed/Driver/`). Evaluated against a pure W3C DOM arena
(`SpecDom`), Qed proves that initial mounts (`buildDomM`), text-run hydration, W3C
`insertBefore` keyed moves, fine-grained `.dyn` updates, `V.memo` skipping, and SSR rehydration
(`App.ssr_rehydrate_equiv`) produce the exact DOM tree specified by `Html.render`.

### Tail-recursive compilation (`@[csimp]`)

To keep proofs simple without sacrificing runtime stack safety, Qed defines structural recursion
for verification and swaps in accumulator implementations during compilation via proven
`@[csimp]` equivalence theorems:

- **HTML string serialization** (`Qed/Render.lean`) collects sibling fragments into an array and
  joins them once, keeping wide sibling lists off the JavaScript call stack while preserving
  handler registration order (deeply nested markup still recurses by tree depth).
- **Pure child patching** (`Qed/Diff.lean`) converts the old child list to an array once and
  steps through siblings with a tail-recursive accumulator (`applyChildrenTR_toList`).

## How the browser reconciles updates

Updating live browser DOM state requires a few guarantees beyond pure HTML serialization:

- **Keyed siblings:** Standard virtual-DOM diffing indexes keyed children in a single pass
  (`validatedKeyIndex`). If keys are missing or duplicated in plain `Html` lists, Qed falls back
  to positional patching so a single DOM node is never reused twice.
- **Duplicate keys in `V.forEach`:** Fine-grained template lists pass keys through
  `disambiguateKeys` (proved collision-free by `forEach_disambiguated_keys_nodup`) during mount,
  update, and hydration. Duplicate user keys never crash the driver or collide on signal names.
- **Signals vs. structural rows:** Template list rows whose dynamic parts are pure text/value
  signals update directly in place without regenerating HTML. Rows containing conditionals,
  helper views, nested lists, or dynamic event closures fall back to keyed diffing, since
  identical HTML strings do not imply identical closures or props.
- **Single-pass list alignment:** When a `V.forEach` list reorders or adds items, Qed aligns old
  DOM nodes, copy-on-write array marks (`refMark`), and signals in one pass, rendering fresh row
  HTML lazily only when a newly inserted key appears.
- **Local components:** Updating a parent refreshes a local component's live `prop`s and
  event callbacks without resetting its persisted local state; `initial` is read only on first
  mount.
- **Attribute and property cleanup:** Full attribute reconciliation removes stale attributes and
  event listeners and resets removed controlled `value` and `checked` DOM properties.
- **Verified subtree memoization (`Qed.lazy` / `V.memo`):** Memoized subtrees require a
  `LawfulKey` argument whose serialization is provably injective (`toKey a = toKey b → a = b`).
  When keys match, skipping the subtree is guaranteed exact by both `applyValues_render` and
  `patchViewM_memo_hit`.

## Differential and browser tests

Proofs verify the Lean driver against `SpecDom`; browser tests verify that `runtime/qed_dom.mjs`
and Chromium behave the same way. Run the browser equivalence suite directly with:

```bash
node test/dom_equivalence_test.mjs
```

This suite compiles [`Examples/DomProbe.lean`](../Examples/DomProbe.lean) and runs deterministic
and seeded mutation sequences through the real JavaScript driver in headless Chromium:

- After every update, it asserts that the live DOM matches both a fresh `buildDom` mount and
  parsed `Html.render` markup (including namespaces, attributes, `value`/`checked` properties,
  and dispatched click messages).
- Dedicated checks verify DOM node preservation across keyed reorders, `V.memo` cache hits, and
  duplicate-key disambiguation across mount, patch, and hydration lifecycles.

In addition, [`test/js_gate_test.mjs`](../test/js_gate_test.mjs) tests native Lean against
transpiled JavaScript on pure rendering (including 16,000-sibling wide lists and handler order)
and key indexing, while feature suites in [`test/`](../test) exercise SSR hydration, local
components, and browser effects end-to-end.
