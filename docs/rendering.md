# Rendering proofs

Qed views have a pure specification—rendering a `View` at state `s` produces an `Html` value—and
an imperative browser driver that updates live DOM nodes in place. Qed connects the two with
Lean refinement proofs over a pure W3C DOM arena model.

## Pure specs and driver proofs

At the pure `Html` and `View` layer:

- **`diff_apply`** in `Qed/Diff.lean` proves that diffing an old `Html` tree against a new one
  and applying the resulting patch yields the exact new `Html` tree.
- **Conditionals with `showIf` and `ifElse`:** `showIf` lowers to `ifElse` with an empty text branch
  so rendering, patching, and hydration share a single conditional path. Hidden branches reserve
  their signal indices so sibling bindings stay aligned, and `patchViewM` skips unchanged hidden
  branches in place.

In [`Qed/Proofs/`](../Qed/Proofs)—spanning `DomArena.lean`, `KeyedReconcile.lean`, `ViewPatch.lean`, and `Hydration.lean`—these theorems are lifted to the
imperative `MonadDom` driver in `Qed/Driver/`. Evaluated against a pure W3C DOM arena
`SpecDom`, Qed proves via unified `CleanDomSubtree` and `VStateValid` invariants that initial
mounts `buildDomM`/`buildViewM`, positional and keyed tree patching `applyToDomM` and `patchHtmlSubtreeM`,
full incremental view patching `patchViewM`, `V.forEach` template reconciliation and
hydration, template row and signal alignment, runtime handler, local-cell, and FIFO queue specs, text-run
hydration `hydrateDomM`/`hydrateViewM`, `V.memo` skipping, and end-to-end SSR rehydration and client
patching produce the exact DOM tree specified by `Html.render`. Component elaboration in
`Qed/Component/Elab.lean` also emits `<Comp>.app_view_eq` via verified template lifting in
`Qed/View/Lift.lean` and transports view invariants onto `App.view` through `canonical_congr_pred`.

### Tail-recursive compilation with `@[csimp]`

To keep proofs simple without sacrificing runtime stack safety, Qed defines structural recursion
for verification and swaps in accumulator implementations during compilation via proven
`@[csimp]` equivalence theorems:

- **HTML string serialization** in `Qed/Render.lean` collects sibling fragments into an array and
  joins them once, keeping wide sibling lists off the JavaScript call stack while preserving
  handler registration order; deeply nested markup still recurses by tree depth.
- **Pure child patching** in `Qed/Diff.lean` converts the old child list to an array once and
  steps through siblings with a tail-recursive accumulator proved by `applyChildrenTR_toList`.

## How the browser reconciles updates

Updating live browser DOM state requires a few guarantees beyond pure HTML serialization:

- **Keyed siblings:** Standard virtual-DOM diffing indexes keyed children in a single pass via
  `validatedKeyIndex`. If keys are missing or duplicated in plain `Html` lists, Qed falls back
  to positional patching so a single DOM node is never reused twice.
- **Duplicate keys in `V.forEach`:** Fine-grained template lists pass keys through
  `disambiguateKeys`—proved collision-free by `forEach_disambiguated_keys_nodup`—during mount,
  update, and hydration. Duplicate user keys never crash the driver or collide on signal names.
- **Signals vs. structural rows:** Template list rows whose dynamic parts are pure text/value
  signals update directly in place without regenerating HTML. Rows containing conditionals,
  helper views, nested lists, or dynamic event closures fall back to keyed diffing, since
  identical HTML strings do not imply identical closures or props.
- **Single-pass list alignment:** When a `V.forEach` list reorders or adds items, Qed aligns old
  DOM nodes, copy-on-write array `refMark`s, and signals in one pass, rendering fresh row
  HTML lazily only when a newly inserted key appears.
- **Local components:** Updating a parent refreshes a local component's live `prop`s and
  event callbacks without resetting its persisted local state; `initial` is read only on first
  mount.
- **Attribute, event handler, and property cleanup:** Full attribute reconciliation removes stale
  attributes, updates and retains `clicks` and `inputs` event handlers via `ElemStateEquiv.dispatchInput`,
  and resets removed controlled `value` and `checked` DOM properties.
- **Verified subtree memoization with `Qed.lazy` / `V.memo`:** Memoized subtrees require a
  `LawfulKey` argument whose serialization is provably injective: `toKey a = toKey b → a = b`.
  When keys match, skipping the subtree is guaranteed exact by `patchViewM_memo_hit`.

## End-to-end verification

Proofs verify the Lean driver against `SpecDom`, while `qed check` verifies that every reachable
`@[extern]` symbol in the browser driver has a matching export in `runtime/qed_rt.mjs` and every
`Cmd` effect has a handler in `runtime/qed_host.mjs`. Run the full native integration test suite
covering SSR, RPCs, databases, and WebSockets with:

```bash
./scripts/qed test
```
