# Qed Examples

Seven focused examples walking through every layer of Qed: components and invariants, `for_each` collections and scoped CSS, validated forms, streaming effects, routed SSR, full-stack RPCs, and multiplexed or third-party WebSockets.

## Running the examples

Any example runs directly via `QED_WEB_ROOT`; `./scripts/qed dev` defaults to `Examples.Counter`:

```bash
QED_WEB_ROOT=Examples.Todo ./scripts/qed dev
```

Open http://localhost:8000 to view the app. Full-stack examples run with the same command:

```bash
# Bookshelf routed SSR app
QED_WEB_ROOT=Examples.Bookshelf ./scripts/qed dev

# CloudBooks full-stack client and native server build
QED_WEB_ROOT=Examples.CloudBooks ./scripts/qed dev

# LiveRoom full-stack multiplexed & third-party WebSocket app
QED_WEB_ROOT=Examples.LiveRoom ./scripts/qed dev
```

Run all proof checks and the 4 native test suites from the repo root:

```bash
./scripts/qed check
./scripts/qed test
```

---

## Tour

1. **[Counter.lean](Counter.lean)** — Basic component state, explicit `action`s, DOM focus preservation across updates, and an automatic `0 <= count` invariant.
2. **[Todo.lean](Todo.lean)** — Child `Row` components inside a parent `collection` using `push`, `filter`, and `sortBy`, scoped `style` blocks, and `for_each` invariants lifting both child state and view styling rules.
3. **[Signup.lean](Signup.lean)** — A `schema` with `where` validation predicates, automatic JSON and Protobuf codecs, and a self-hosted `<Account.Form reset onSubmit={...}/>` gated on schema validity.
4. **[Chat.lean](Chat.lean)** — Streaming Server-Sent Events with `Cmd.stream`, loop rendering, and an effect-safety invariant `pending -> 0 < turns.size`.
5. **[Bookshelf.lean](Bookshelf.lean)** — Routed SPA and native SSR app combining `router`, `<Book.Form>`, `style` and `theme`, `Resource` HTTP requests, `<Await>`, `Cmd.pushUrl`, and SSR hydration.
6. **[CloudBooks.lean](CloudBooks.lean)** — Full-stack app pairing typed `external` HTTP APIs and a stateful native `server` with `invariant`, `requires`/`ensures`, `atomic:`, and `session` auth alongside a `Storefront` client component.
7. **[LiveRoom.lean](LiveRoom.lean)** — Full-stack WebSocket app combining multiplexed binary server `channel`s with `on_join`, `on_send`, `on_leave`, and transactional `emit`, plus third-party `external` `ws` feeds with per-subscription `reconnect` policies.

---

## Compiler Gates & Benchmarks

Compiler and runtime test modules live in [../Tests/](../Tests/), covering `SyntaxChecks`, `ServerChecks`, `DbChecks`, `CssChecks`, `JsGate`, `SpeculativeChecks`, and the native `Tests/Runner.lean` test runner. Pipeline benchmarks live in [../Bench/](../Bench/) via `lake exe bench`.
