# Rendering proofs and browser checks

`diff_apply` proves that applying a diff to a pure `Html` tree produces the new tree.
`applyValues_render` covers stable template structure, and `patch_render` covers the
general template update. These theorems do not model browser node identity or execute
the imperative driver.

The HTML string renderer keeps structural `renderNode`/`renderChildren` definitions for proofs.
Two `@[csimp]` theorems substitute an equivalent accumulator renderer during compilation,
preserving both markup and the handler table. Sibling fragments are collected and joined once,
so wide lists do not grow the JavaScript call stack. Deeply nested trees still recurse by depth.

Pure child patching converts the old sibling list to an array once, then shares one step
interpreter between a structural `map` and an accumulator traversal. `applyChildrenTR_toList`
proves their equivalence for any initial accumulator and old array. This avoids repeated
list-to-array conversion in the pure evaluator; the browser uses its separate DOM applier.

`showIf` is shorthand for `ifElse` with an empty text branch, so rendering, patching,
and hydration share one conditional implementation. Its equivalence lemmas preserve HTML,
structural fingerprints, and signal numbering, including the indices reserved by hidden
branches. A branch that stays hidden is structurally stable regardless of its child.
`View.showIf` and `V.showIf` remain available for constructing views; code that pattern-matches
on `View` handles conditionals through the `ifElse` constructor.

The browser implementation needs additional rules:

- Ordinary keyed reconciliation uses `validatedKeyIndex` to check and index siblings in
  one traversal, reusing the old list's index. Missing or duplicate keys use positional
  reconciliation, avoiding reuse of one node twice.
- Fine-grained lists reject duplicate reconciliation keys on build, update, and hydration
  before seeding signals or moving rows. These lists cannot use positional fallback
  because their signals are addressed by key.
- Rows containing helper views, conditionals, nested lists, or dynamic attribute handlers
  use ordinary keyed reconciliation. Equal serialized HTML does not imply equal props or
  event behavior. Rows handled entirely by signals retain their direct update path.
- Structural list updates align old rows, marks, and signals in one pass. Fresh row HTML
  is generated only when an added key is encountered, then shared for the remaining additions.
- Full attribute updates remove obsolete attributes and event slots, and reset removed
  controlled `value` and `checked` properties. Bound attributes that change names use
  the same reconciliation; fixed-name value bindings retain their direct update path.
- `Html.lazy` remains a trusted escape hatch: equal memo keys must imply equal content,
  including handler behavior. Its browser skip is not justified by `diff_apply`, whose
  pure `lazyReuse` case simply returns the supplied new subtree.

Run the browser differential check with:

```sh
node test/dom_equivalence_test.mjs
```

The test compiles `Examples.DomProbe`, then runs deterministic and seeded update sequences
through the real transpiled driver in Chromium. After every ordinary tree update it compares
the live DOM with both a fresh `buildDom` and parsed `Html.render` output. Template updates
are compared with `View.render` followed by `Html.render`.

Snapshots include tree structure, namespaces, attributes, and input properties. Internal
handler IDs and signal markers are excluded from structural comparison; active click slots
are checked separately against the expected messages. Dedicated assertions cover surviving
keyed-node identity, valid memo reuse, and duplicate-key rejection in template lifecycle paths.

The fixtures cover additions, removals, reorders, duplicate keys, root/tag changes, attribute
and handler removal, controlled inputs, SVG attributes, signals, and conditional templates.
They are regression evidence, not a proof of the driver or exhaustive coverage of HTML,
hydration, local components, or arbitrary user-supplied templates. Existing browser suites
provide additional coverage for those features.

The native/JavaScript gate also covers serialization of up to 16,000 siblings (including
handler order) and successful/failed key indexing. Local timing checks are useful for comparing
these pure operations; they do not predict end-to-end browser performance.
