# How Qed works

Qed components generate a typed message enum and a pure update function. When an event fires,
it dispatches a message; the update function computes the next state; the renderer updates the
DOM. When an app grows to need routing or side effects, you can write that same architecture
explicitly with `Model`, `Msg`, `update` (or `transition`), and `ui`—and keep using the same
components inside it.

## From Lean to the browser

```text
Lean app: components, reducers, views, and declared invariants
   │  lake build: Lean's kernel checks all types and proofs
   ▼
qedjs: verifies Lean.Environment, then lowers Lean IR → JavaScript
   ▼
app.mjs + qed_rt.mjs: compiled app code and Lean primitives
   ▼
qed_dom.mjs + qed_host.mjs: DOM updates, event wiring, and browser effects
```

Qed compiles the exact same update, view, and diff functions that your proofs reason about.
Proofs exist only at compile time and are erased before JavaScript is emitted.

### What is proved vs. trusted

Lean's kernel checks your app invariants, HTML5 and URL safety, SSR state round-trips, the
imperative DOM driver logic, and the IR-to-JS lowering rules.

Every verified system still has a trusted computing base. Qed relies on:

- Lean's kernel and compiler IR generator working correctly.
- Pretty-printing the verified JavaScript AST to `.mjs` text (`Js/Backend.lean`).
- The small hand-written JS runtime (`runtime/`) and the browser's own DOM/Web APIs.

Because browser APIs, network requests, and out-of-memory errors sit outside pure functional
models, Qed pairs its compile-time proofs with differential and headless-browser test suites.

## What Qed checks at compile time

- **State transitions:** `invariant … preserved_by update` proves that if a rule holds before
  an update, it still holds afterward (and on `init` when requested). See
  [invariants](invariants.md).
- **Views, HTML5 validity, and XSS safety:** `invariant … holds_in view` checks custom view
  and styling rules. In addition, every `App` and local component carries an automatic
  `valid_view` proof (`Html.valid`) that rules out browser-rewritten HTML5 nesting (like
  `<div>` inside `<p>` or nested `<button>`s), children inside void tags, `<script>` / `srcdoc` /
  inline `on*` attributes, raw HTML injection, and untyped `href` / `src` / `action` URLs.
  SSR script, JSON, and CSS payloads are also proved breakout-free.
- **Isomorphic SSR and DOM updates:** Every SSR `Dehydrate` codec proves both `round_trip` and
  `dehydrate_view` (restoring server state renders the exact same initial HTML). Over in
  [`Qed/Proofs/DomEquiv.lean`](../Qed/Proofs/DomEquiv.lean), Qed proves that mounting,
  hydration, W3C `insertBefore` keyed moves, fine-grained signal updates, and `V.memo` skipping
  match fresh `Html.render` output.
- **Forms and routes:** `schema` proves that a form's submit button enables if and only if its
  parser succeeds. `router` proves that formatting a route to a URL and parsing it back returns
  the original route and produces a safe URL.
- **Total execution and JS lowering:** [`Js/VerifyEnv.lean`](../Js/VerifyEnv.lean) inspects the
  compiled `Lean.Environment` on every build, allowing only Lean's three standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`) and rejecting `sorry`, `native_decide`, custom
  axioms, `partial`, `unsafe`, `while` loops, user `@[implemented_by]`, and unverified
  `@[extern]` declarations. [`Js/Proofs.lean`](../Js/Proofs.lean) proves semantics preservation
  for constructor layouts, curried closures, tail-call loops, trampolines, and copy-on-write
  array snapshots (`refMark`).

Always check that an invariant states what you actually mean. Proving `0 ≤ quantity` prevents
underflow, not ordering more items than are in stock. Similarly, a valid book route proves URL
well-formedness, not that the book exists on your server.

## Verification commands

Unsolved proof goals fail normal Lean compilation. Running `qed check` or `qed build` also runs
three repository-wide gates:

1. **Kernel environment gate (`qedjs --verify-env`):** checks the transitive closure of
   compiled declarations for standard axioms and totality.
2. **Axiom manifest (`scripts/axioms.lean`):** runs `#print axioms` on core framework theorems
   when present.
3. **Source and effect checks:** rejects forbidden proof-skipping tactics in source files and
   verifies that every `Cmd` effect emitted in `Qed/` has a matching handler in
   `runtime/qed_host.mjs`.

During development, `qed dev` typechecks and verifies proofs for the active app on each save.
Run `qed check` or `qed build` before shipping to run the full environment and manifest checks.

## Tests and benchmarks

- [`test/js_gate_test.mjs`](../test/js_gate_test.mjs) compares native Lean output against
  transpiled JavaScript across rendering, diffing, arithmetic, JSON, routing, and runtime
  edge cases.
- [`test/dom_equivalence_test.mjs`](../test/dom_equivalence_test.mjs) runs generated update
  sequences in Chromium and checks that incremental DOM mutations match a fresh render,
  covering attributes, event handlers, keyed reorders, `V.memo`, and duplicate keys.
- Additional browser suites in [`test/`](../test) cover effects, WebSockets, streaming, local
  components, and SSR hydration.

See [rendering details](rendering.md) for how direct signal bindings, structural reconciliation,
and memoization work. Proofs guarantee correctness, not speed—reproducible benchmarks live in
[`Examples/Bench`](../Examples/Bench), [`test/bench_template.mjs`](../test/bench_template.mjs),
and [`test/bench_react.mjs`](../test/bench_react.mjs).

## Server rendering and deployment

For an entry module with `def main : IO Unit := Qed.run <app>`, `qed build` outputs both the
client bundle and `dist/ssr.mjs`:

```js
import render from './dist/ssr.mjs'; // async (Request) => Response
```

For each incoming request, the SSR handler matches the URL route, runs the app's initial HTTP
queries (skipping browser-only effects and bounding replay rounds), and renders the HTML
document.

To deploy with SSR:

1. Serve static client assets from `dist/` and pass page requests to `dist/ssr.mjs` in any
   runtime with standard `Request`, `Response`, and `fetch` APIs (`qed start` runs this
   locally).
2. Host your backend `/api` endpoints separately, or pass a custom `fetch` into
   `makeHandler(mod, { fetch, title, … })` from `dist/ssr.mjs`.
3. State restoration is automatic: `ui` and `component` apps synthesize a verified `Dehydrate`
   codec by default so the browser restores server state without re-fetching startup data
   (customizable with `(ephemeral := […])`, `(dehydrate := […])`, or `(dehydrate := false)`).
   [Bookshelf](../Examples/Bookshelf.lean) and [`test/bookshelf_ssr_test.mjs`](../test/bookshelf_ssr_test.mjs)
   demonstrate zero-refetch startup.

The same build output also works as a static single-page app: point client routes at
`index.html` on any static host.

## Source map

| Path | Purpose |
|------|---------|
| `Qed/Html.lean` | Typed `Html` / `Attr` / `Url` virtual DOM and static HTML5 validity rules (`Html.valid`). |
| `Qed/Jsx.lean` | JSX syntax (`<div class="x" onClick={.tap}>…</div>`), lowered to typed `Html` builders. |
| `Qed/Notation.lean` | Attribute, event, link, and `Qed.lazy` helpers used by JSX and plain Lean views. |
| `Qed/View.lean` (`Qed/View/`) | Fine-grained `View` templates (`dyn`, `showIf`, `ifElse`, `forEach`, `memo`), `view%` lifting, and `patch_render` proofs. |
| `Qed/Diff.lean` | Pure tree diffing and keyed/positional child reconciliation, plus `diff_apply`. |
| `Qed/Dom.lean` / `Qed/Driver.lean` (`Qed/Driver/`) | Total `MonadDom` interface and browser driver for mounting, patching, hydration, and local state. |
| `Qed/Proofs/DomEquiv.lean` | Refinement proofs linking the `MonadDom` driver, keyed moves, hydration, `SoundMemo`, and SSR to `Html.render`. |
| `Qed/Runtime.lean` (`Qed/Runtime/`) | TEA `App` and `ui` builders, `Cmd` effects, typed ports, local components, and `Dehydrate` codecs. |
| `Qed/Ssr.lean` | Document serialization (`renderDocument`), breakout-safety proofs, and per-request SSR execution. |
| `Qed/Steps.lean` | `steps` macro for effectful transitions where branches return either `model` or `(model, cmd)`. |
| `Qed/Json.lean` (`Qed/Json/`) | Total JSON parser/renderer and `ToJson` / `FromJson` / `LawfulJson` round-trip proofs. |
| `Qed/Router.lean` | `Router` / `LawfulKey` classes, the `router` macro, and verified URL formatting/parsing. |
| `Qed/Schema.lean` | Refined `Field` types, form controls, and the `schema` macro (generates `Draft`, `formView`, `canSubmit_iff`, and JSON codecs). |
| `Qed/Component.lean` (`Qed/Component/`) | `component` macro (`prop`, `state`, `emits`, `action`, `collection`, `invariant`, `view`). |
| `Qed/Invariant.lean` (`Qed/Invariant/`) | `invariant` command (`preserved_by`, `holds_in`, `for_each`) and proof automation. |
| `Js/Backend.lean` | Total Lean IR to typed JavaScript AST compiler and pretty-printer. |
| `Js/VerifyEnv.lean` | Kernel `Lean.Environment` gate enforcing standard axioms and total definitions. |
| `Js/Proofs.lean` | Operational semantics and soundness proofs for JS lowering and copy-on-write arrays. |
| `Cli.lean` (`Cli/`) | `qed` CLI (`dev`, `build`, `start`, `test`, `check`, `clean`, `new`, `doctor`). |
| `runtime/` | JavaScript primitives (`qed_rt.mjs`), DOM bindings (`qed_dom.mjs`), effects (`qed_host.mjs`), and server helpers. |
| `Examples/` · `test/` | Runnable example apps, benchmarks, and differential/browser test suites. |
