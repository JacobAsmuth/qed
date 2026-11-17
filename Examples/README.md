# Qed Examples

A guided tour through Qed, moving from single components with local state to verified forms,
collection invariants, async effects, streaming, SSR, and a full-stack server + client app.

## Running the examples

Any self-contained browser example runs locally via `QED_WEB_ROOT`. `Examples.Web` runs `Counter`
by default:

```bash
QED_WEB_ROOT=Examples.TodoWeb ./scripts/qed dev
```

Open http://localhost:8000 to view the app. Examples backed by HTTP, SSE, or WebSockets pair a
`--dev` build with a local test server:

```bash
# Bookshelf REST API and generated SSR handler
QED_WEB_ROOT=Examples.BookshelfWeb ./scripts/qed build --dev
node Examples/bookshelf-server.mjs

# Streaming Chat with mock OpenAI SSE endpoint
QED_WEB_ROOT=Examples.ChatWeb ./scripts/qed build --dev
python3 test/mock_llm.py 8000 .qed/dev

# CloudBooks full-stack client and server build
QED_WEB_ROOT=Examples.CloudBooks ./scripts/qed build --dev
```

Run all proof/environment checks and the 15 automated test suites from the repo root:

```bash
./scripts/qed check
./scripts/qed test
```

---

## I. Components, State & Invariants

1. **[Hello.lean](Hello.lean)** — The smallest Qed app: inferred `state`, two-way `bind`, and
   mixed JSX text interpolation.
2. **[Counter.lean](Counter.lean)** — Explicit `action` handlers, a compile-time state `invariant`,
   and DOM focus preservation across updates.
3. **[Live.lean](Live.lean)** — Inline state handlers, handlers reading live state expressions, and
   open DOM events such as `onDoubleClick`.

## II. Views, Scoped Styles & Proofs

4. **[Badge.lean](Badge.lean)** — Proof-only component with scoped `css` classes verified by inline
   view styling invariants alongside arithmetic state invariants.
5. **[Template.lean](Template.lean)** — Core JSX control flow: conditionals, keyed and keyless
   `for` loops, structural element switches, inline editing toggles, scoped `css` rules,
   and a custom `invariant ... := by ...` preservation proof.

## III. Child Components, Collections & Local State

6. **[Todo.lean](Todo.lean)** — Parent-owned `collection` rows. Iterating with `for` automatically
   injects each row's declared `key` and routes child events.
7. **[Feed.lean](Feed.lean)** — Proof-only example using inline `for_each` to lift child state and
   view styling invariants across parent sort, map, filter, and push operations.
8. **[Local.lean](Local.lean)** — Dynamic keyed child instances whose state lives outside the
   parent model, nested child components, typed `event` bubbling, and `(field := ·)` setters.

## IV. Forms, Validation & Routing

9. **[Signup.lean](Signup.lean)** — A `schema` defining editable drafts, proof-carrying validation,
   JSON codecs, and a declarative `<Account.Form>` gated on schema validity.
10. **[Booking.lean](Booking.lean)** — Context-parameterized `schema Appt (today : Date)` combining
    a startup `Cmd.now` lookup with `<Appt.Form>` and an invariant linking booking state to loaded
    context.
11. **[Users.lean](Users.lean)** — Verified `router`, reactive `route` state, cached remote `query`
    fetching, focus/keyboard handlers, and declarative async rendering via `<Await>`.

## V. Effects, Realtime & Full-Stack

12. **[Effects.lean](Effects.lean)** — Pure side effects via `Cmd`: `start` initialization, local
    storage, document title, randomness, timers and debouncing, file picking, focus, batching, and
    typed outbound/inbound `port`s.
13. **[Chat.lean](Chat.lean)** — Streaming Server-Sent Events with `Cmd.stream`, loop rendering,
    and an invariant proving a pending response implies a non-empty conversation.
14. **[Socket.lean](Socket.lean)** — WebSockets via `Cmd.wsOpen`, `Cmd.wsSend`, and `Cmd.wsClose`,
    guarded actions, and an invariant proving the composer cannot hold text while offline.
15. **[Bookshelf.lean](Bookshelf.lean)** — Complete routed client app combining `router`, `schema`
    forms, `token`/`css`/`theme` styling, early `return` in `route` arms, `<Await>` with `err`,
    `Resource` HTTP requests, `Cmd.pushUrl`, and SSR hydration.
16. **[CloudBooks.lean](CloudBooks.lean)** — End-to-end verified full-stack app combining typed
    `external` HTTP APIs, a stateful `server` with authorization rules and `atomic` invariants,
    `component`, and `fullstack`.

---

## Appendix: Entry Points, Substrates & Benchmarks

These files support the test suites and benchmarks rather than introducing new app features:

- **`*Web.lean` / [Web.lean](Web.lean)** — Minimal `Qed.run` browser entrypoints selected with
  `QED_WEB_ROOT`. `Web.lean` defaults to `Counter.app`.
- **Compiler & proof suites** — [SyntaxChecks.lean](SyntaxChecks.lean),
  [ServerChecks.lean](ServerChecks.lean), [JsGate.lean](JsGate.lean),
  and [DomProbe.lean](DomProbe.lean) check compile-time errors and JS/DOM equivalence.
- **Benchmarks** — [Bench/](Bench/) contains pipeline and view-layer benchmarks, run via
  `lake exe bench`, `test/bench_react.mjs`, and `test/bench_template.mjs`.
