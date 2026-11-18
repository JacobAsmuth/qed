# Qed Examples

Six focused examples walking through every layer of Qed: components and invariants, `for_each` collections and scoped CSS, validated forms, streaming effects, routed SSR, and a verified full-stack server + client app.

## Running the examples

Any example runs directly via `QED_WEB_ROOT` (`./scripts/qed dev` defaults to `Examples.Counter`):

```bash
QED_WEB_ROOT=Examples.Todo ./scripts/qed dev
```

Open http://localhost:8000 to view the app. Examples backed by HTTP or SSE pair a `--dev` build with a local server:

```bash
# Bookshelf REST API and generated SSR handler
QED_WEB_ROOT=Examples.Bookshelf ./scripts/qed build --dev
node Examples/bookshelf-server.mjs

# Streaming Chat with mock OpenAI SSE endpoint
QED_WEB_ROOT=Examples.Chat ./scripts/qed build --dev
python3 test/mock_llm.py 8000 .qed/dev

# CloudBooks full-stack client and native server build
QED_WEB_ROOT=Examples.CloudBooks ./scripts/qed dev
```

Run all proof/environment checks and the 4 automated TCB test suites from the repo root:

```bash
./scripts/qed check
./scripts/qed test
```

---

## Tour

1. **[Counter.lean](Counter.lean)** — Basic component state, explicit `action`s, DOM focus preservation across updates, and an automatic arithmetic `invariant` (`0 <= count`).
2. **[Todo.lean](Todo.lean)** — Child `Row` components inside a parent `collection` (`push`, `filter`, `sortBy`), scoped `css` classes, and `for_each` invariants lifting both child state (`rowsSafe`) and view styling rules (`rowsStyled`).
3. **[Signup.lean](Signup.lean)** — A `schema` with `where` validation predicates (`'@' in email`), automatic JSON/Protobuf codecs, and a self-hosted `<Account.Form reset onSubmit={...}/>` gated on schema validity.
4. **[Chat.lean](Chat.lean)** — Streaming Server-Sent Events with `Cmd.stream`, loop rendering, and an effect-safety invariant (`pending -> 0 < turns.size`).
5. **[Bookshelf.lean](Bookshelf.lean)** — Complete routed SPA + JS SSR app combining `router`, `<Book.Form>`, `token`/`css`/`theme` styling, `Resource` HTTP requests, `<Await>` with error handling, `Cmd.pushUrl`, and SSR hydration (paired with [bookshelf-server.mjs](bookshelf-server.mjs)).
6. **[CloudBooks.lean](CloudBooks.lean)** — End-to-end verified `fullstack` app pairing typed `external` HTTP APIs and a stateful native `server` (`invariant`s, `requires`/`ensures` contracts, `ensure`, `return atomic:`, `session` auth) with a `Storefront` client component.

---

## Appendix: Compiler Gates & Benchmarks

These files support the test suites and benchmarks rather than serving as user-facing app examples:

- **Compiler & runtime gates** — [SyntaxChecks.lean](SyntaxChecks.lean), [ServerChecks.lean](ServerChecks.lean), [JsGate.lean](JsGate.lean), and [DomProbe.lean](DomProbe.lean) check compile-time diagnostics and Lean/JS/DOM equivalence.
- **Benchmarks** — [Bench/](Bench/) contains pipeline and view-layer benchmarks, run via `lake exe bench`, `test/bench_react.mjs`, and `test/bench_template.mjs`.
