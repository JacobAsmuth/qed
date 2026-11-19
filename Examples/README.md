# Qed Examples

Seven focused examples walking through every layer of Qed: components and invariants, `for_each` collections and scoped CSS, validated forms, streaming effects, routed SSR, full-stack RPCs, and multiplexed/3rd-party WebSockets.

## Running the examples

Any example runs directly via `QED_WEB_ROOT` (`./scripts/qed dev` defaults to `Examples.Counter`):

```bash
QED_WEB_ROOT=Examples.Todo ./scripts/qed dev
```

Open http://localhost:8000 to view the app. Examples backed by HTTP, SSE, or WebSockets pair a `--dev` build with a local server:

```bash
# Bookshelf REST API and generated SSR handler
QED_WEB_ROOT=Examples.Bookshelf ./scripts/qed build --dev
node Examples/bookshelf-server.mjs

# Streaming Chat with mock OpenAI SSE endpoint
QED_WEB_ROOT=Examples.Chat ./scripts/qed build --dev
python3 test/mock_llm.py 8000 .qed/dev

# CloudBooks full-stack client and native server build
QED_WEB_ROOT=Examples.CloudBooks ./scripts/qed dev

# LiveRoom full-stack multiplexed & 3rd-party WebSocket app
QED_WEB_ROOT=Examples.LiveRoom ./scripts/qed dev
```

Run all proof/environment checks and the 5 automated test suites from the repo root:

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
7. **[LiveRoom.lean](LiveRoom.lean)** — End-to-end verified `fullstack` WebSocket app combining multiplexed binary server `channel`s (`on_join`, `on_send`, `on_leave`, transactional `emit`, `ctx.connId`) and 3rd-party `external` `ws` feeds (JSON, raw text, binary `Proto(T)`) with configurable per-subscription `reconnect` policies.

---

## Compiler Gates & Benchmarks

Compiler/runtime test modules live in [../Tests/](../Tests/) (`SyntaxChecks`, `ServerChecks`, `CssChecks`, `JsGate`, `DomProbe`), and pipeline/view benchmarks live in [../Bench/](../Bench/) (`lake exe bench`, `test/bench_react.mjs`, `test/bench_template.mjs`).
