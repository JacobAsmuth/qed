# How Qed works

Qed components generate a typed message type and a pure reducer. An event dispatches a
message; the reducer computes the next state; the renderer applies the change. When an app
needs routing or effects, it can write that architecture explicitly with `Model`, `Msg`,
`update`/`transition`, and `ui`. The same components still work inside it.

## From Lean to the browser

```text
Lean app: components, reducers, views, and declared invariants
   │  lake build: Lean's kernel checks the proofs
   ▼
qedjs: Lean compiler IR → JavaScript for the app, framework, and driver
   ▼
app.mjs + qed_rt.mjs: compiled code and Lean primitives
   ▼
qed_dom.mjs + qed_host.mjs: DOM calls, event wiring, and effects
```

Qed compiles the same reducer and diff functions that the proofs refer to. The compiler
removes the proofs, so they don't run in the browser.

Those proofs cover the Lean code. They rely on Lean's proof checker and compiler working
correctly. Qed also relies on `qedjs` translating the code correctly and on its JavaScript
runtime and browser code behaving as expected. We test the translation and browser behavior,
but the Lean proofs don't check those steps. The app can still fail because of bugs there,
unsafe code, a panic, running out of memory, or a failed browser API call.

## What is checked

- **State transitions:** `invariant … preserved_by update` proves that an update preserves
  the rule, assuming it is true before the update. The starting state must satisfy it too.
  A rule about your model says nothing about the state of an external server.
- **Views:** `invariant … holds_in view` proves the specified predicate over the pure view.
  See [invariants](invariants.md) for styling predicates and contracts over child collections.
- **Rendering:** updating a pure `Html` tree gives the same result as rendering it again
  from scratch. The proofs don't cover the code that makes the actual DOM changes.
- **Forms and routes:** Qed generates proofs that the form's submit check agrees with its parser
  and that a route converted to a URL parses back to the same route. A valid route
  to a book doesn't tell you whether that book exists.
- **Lean definitions:** exhaustive pattern matching and termination checking apply to total
  definitions. These checks catch missing cases and recursion that Lean cannot show will finish.

Check that each invariant says what you need it to say. Proving that a quantity is nonnegative,
for example, doesn't check whether it exceeds the stock available. You'll still want browser
and integration tests for the rest of the app.

## Tests

[`test/js_gate_test.mjs`](../test/js_gate_test.mjs) compares native Lean and transpiled JavaScript
on rendering, diffing, arithmetic, JSON, routing, and other probes.
[`test/dom_equivalence_test.mjs`](../test/dom_equivalence_test.mjs) compares incremental DOM
updates with fresh rendering after generated update sequences, including attribute removal,
event handlers, and keyed reorders. Other browser tests exercise effects and hydration.
Like other tests, these cover the cases they run.

[Rendering details](rendering.md) document direct binding updates, structural reconciliation,
key requirements, and the trusted `Html.lazy` escape hatch. Performance depends on the app;
[`Examples/Bench`](../Examples/Bench), [`test/bench_template.mjs`](../test/bench_template.mjs),
and [`test/bench_react.mjs`](../test/bench_react.mjs) contain reproducible benchmarks.
The proofs don't tell you how fast an app will be; that's what the benchmarks measure.

## Verification commands

Unsolved proof goals fail Lean compilation. `qed build` and `qed check` also scan selected
sources for `sorry`, `admit`, and `native_decide`. When `scripts/axioms.lean` exists, they run
that manifest and reject output containing `sorryAx` or `error:`. This covers only the listed
theorems and does not enforce an axiom whitelist; a passing check does not rule out unexpected
axioms. The note about updates without invariants comes from a source scan and can miss cases.

`qed dev` compiles the selected entry and its dependencies on each rebuild, so their proofs
are checked then. Run `qed check` or `qed build` for the additional source and manifest checks.

## Server rendering and deployment

For a recognized `def main : IO Unit := Qed.run <app>` entry, `qed build` emits both the client
bundle and `dist/ssr.mjs`. The handler routes each request, performs the app's HTTP effects,
and renders the same view as the client. SSR skips browser-only effects and limits HTTP
replay rounds.

```js
import render from './dist/ssr.mjs'; // async (Request) => Response
```

Serve the client assets and pass page requests to this handler in a runtime with compatible
`Request`, `Response`, and `fetch` APIs. `qed start` does that locally. Provide the app's API
separately; the generated server does not implement `/api` endpoints for you. You can use
`makeHandler(mod, { fetch, title, … })` from the generated module to supply a data source.

With `dehydrate` and `rehydrate` configured on the app, the client restores the server's model
without repeating startup requests. [Bookshelf](../Examples/Bookshelf.lean) implements both
hooks; its [hydration test](../test/bookshelf_hydrate_test.mjs) asserts zero client API calls
on the initial catalog load.

The same build also works as a static single-page app. Configure a static host to serve
`index.html` for client routes, and supply any APIs the app uses.

## Source files

| Path | What |
|------|------|
| `Qed/Html.lean` | The typed virtual DOM every bit of syntax becomes. |
| `Qed/Jsx.lean` | The JSX view syntax: `<div class="x" onClick={.tap}>…</div>`, expanded to `el "tag" [attrs] [kids]`. |
| `Qed/Notation.lean` | The attribute and event helpers (`cls`, `onClick`, `value`, …) JSX attributes expand to. |
| `Qed/View.lean` | The rendering model: `View` (`dyn`/`showIf`/`ifElse`/`forEach`/`dynNode`) and the `view%` lift behind `ui`; built once, then changed bindings patch (`patch_render`/`applyValues_render`). |
| `Qed/Runtime.lean` | The Elm Architecture: `App`, the `ui` builder, the `Cmd` effects + `port`/`onPort`, local components, and the render primitives. |
| `Qed/Ssr.lean` | The per-request SSR step `dist/ssr.mjs` loops: route, run the app's queries, render, dehydrate. |
| `Qed/Steps.lean` | The `steps` builder for effectful transitions: arms are bare models or `(model, cmd)` pairs. |
| `Qed/Diff.lean` | The reconciler the engine uses internally: one children reconcile shared by positional and keyed, `lazy` memoization, and the `diff_apply` proof. |
| `Qed/Json.lean` | JSON parser/renderer + the `ToJson`/`FromJson` classes, with the `parse_depth_le`/`parse_render` proofs. |
| `Qed/Router.lean` | The `Router` class (round-trip law as a field), the `router` command, `toURL`/`fromURL`. |
| `Qed/Schema.lean` | `Field p`, the `Codec` controls, and the `schema` command. One declaration yields the form (Draft + `parse` + `formView` + `canSubmit_iff`) and the JSON codec (`ToJson`/`FromJson` + `decode`/`encode`). |
| `Qed/Component.lean` | `Component`, the `for_each` lift lemmas, and the `component` declaration (`state`/`prop`/`action`/`collection`/`view`). |
| `Qed/Invariant.lean` | The `invariant` command (`preserved_by` / `holds_in` / `for_each`). See [invariants](invariants.md). |
| `Qed/Dom.lean` / `Qed/Driver.lean` | The DOM primitives and imperative browser driver; part of the trusted implementation. |
| `Js/Backend.lean` | The Lean IR to JavaScript transpiler. |
| `runtime/` | Hand-written JavaScript for Lean primitives, DOM operations, browser effects, and serving/SSR hosts. |
| `Examples/` · `test/` | Example apps and the browser tests that drive them. |
