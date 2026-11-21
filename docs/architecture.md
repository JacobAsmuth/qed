# How Qed works

Qed is a full-stack web language embedded in [Lean 4](https://lean-lang.org). Instead of
bolting static checks onto template strings or maintaining a separate specification language, Qed
provides Lean 4 elaborators for `schema`, `router`, `style`, `theme`, `keyframes`, `component`, `external`, `database`, `server`,
`fullstack`, and JSX. These desugar UI views, client state machines, wire protocols, database schemas, and backend
handlers into **ordinary Lean 4 definitions and proof obligations**.

Lean's typechecker and theorem-proving kernel verify your invariants on the exact same functions
that compile to browser JavaScript and native server machine code. All proofs live in Lean's
`Prop` universe and are erased before any executable code is emitted.

## Language building blocks

A Qed program is composed from declarative blocks that share types and proofs end-to-end:

| Construct | What you write | What Qed generates & proves |
|-----------|----------------|-----------------------------|
| `schema` | Fields with `where` refinement predicates | Editable `Draft`, proof-carrying `Field` records, `<Schema.Form>` with self-hosted draft, optional `reset`/`bind`, and validated `onSubmit`, `canSubmit_iff`, plus `LawfulJson` and `LawfulProto` codecs. |
| `router` | Named routes and URL patterns | Inductive route type, `Router` instance, proven `round_trip`, and `isSafeUrl` guarantees for links and navigation. |
| `style` / `theme` / `keyframes` | Scoped CSS blocks, typed design tokens, and animations | Compile-time-baked scoped CSS classes, WCAG contrast proofs, and `verify_theme` completeness checks, collected into `styles.css` or `<style id="qed-styles">` and queryable by view invariants. |
| `component` | `session`, data and `Html` `prop`s, `bind`, `state`, `ephemeral`, `collection`, `route`, `start`, `port`, `query`, `subscribe`, `action`, `await`/`catch`, `invariant`, and JSX `view` with implicit `{children}` | Typed `Msg`, `init`, `update`, fine-grained `View` template, `App`, SSR `session` hydration, client RPC `requires` proofs, exhaustive domain `catch`, `Html.valid` proof, `Dehydrate` SSR codec, and state/styling invariant proofs. |
| `external` | Base URL, auth schemes, and typed HTTP endpoints | Typed client functions with origin pinning, CRLF-sanitized headers, JSON/Protobuf/Bytes codecs, and SSRF-guarded `Webhook` calls. |
| `database` | Endpoint config, `table` columns with `where`/`immutable`, row-level `policy` rules, `old(...)` and `transition` invariants | Typed row structs with JSON/Protobuf codecs, parameterized `SqlQuery` compiler proved injection-free, DDL and Postgres RLS generation, and zero-trust query verification. |
| `server` | `env`, `use db`, `state`, `invariant` rules, and `def` handlers with `requires`, `ensures`, `atomic`, `fail(.tag)`, and `await` | Transactional `MonadServer` and `MonadAtomic` handlers, inferred domain error enums, `ProgEnsures` postconditions, Protobuf RPC dispatchers, and proofs of state preservation, auth checks, and linearizability. |
| `fullstack` | A `server` paired with a `client` component or `App` | Typed client-to-server binary Protobuf RPCs under `/_qed/rpc/…`, `rpc_endpoints_valid` and `ssr_rpc_closure_complete` closure theorems, client-leak isolation, and a unified native server + client build. |

For component composition—pure wrappers, hoisted stateful sub-components, keyed `LocalDef` cells,
and `collection`s—see [Components](components.md). For writing and proving rules over state,
collections, and views, see [Invariants](invariants.md).

## Two execution targets from one source

Qed compiles client and backend code through separate pipelines while enforcing
`verifyNoServerLeakInClient`, which forbids server secrets, database configs, state boxes, and handlers from
entering client JavaScript:

```text
Lean app: schemas, routers, components, and optional external/database/server/fullstack blocks
   │
   ├──▶ Client bundle: qedjs lowers Lean.IR → typed JS AST
   │       └─▶ app.mjs + runtime/qed_rt.mjs, qed_dom.mjs, qed_host.mjs
   │
   └──▶ Native server binary: Lean C backend + rust/qed_server
           • Static assets + /_qed/health
           • In-memory SSR via App.ssrRenderNativeBytes
           • /_qed/rpc/<Server>/<fn> binary Protobuf RPCs
           • /_qed/ws/<Server> multiplexed RFC 6455 WebSockets
           • Embedded SQLite, PostgreSQL v3 wire protocol, and HTTP SQL
```

### Browser rendering & DOM updates

JSX expressions compile to typed `Html` values and are lifted into `View` templates by
[`Qed/View/Lift.lean`](../Qed/View/Lift.lean). When state changes, the browser driver updates
tracked text, attribute, and `value`/`checked` bindings directly through signals and falls back
to keyed or positional DOM diffing when structural branches or lists change. See
[Rendering](rendering.md) for how signal templates, `V.memo`, and W3C `insertBefore` reconciliation
are proved equivalent to fresh `Html.render`.

### Native server & in-memory SSR

For both standalone `component` apps and `fullstack` apps, `qed build` compiles the client to
`app.mjs` and links the server through Lean's C backend with the Rust I/O, TLS, and SQLite shim
in [`rust/qed_server/`](../rust/qed_server) into `dist/server`. HTTP/1.1 parsing and formatting,
static path and MIME policy, CSRF/CSWSH origin checks, SSRF IP CIDR policy, RFC 6455 WebSocket
framing, PostgreSQL v3 wire protocol, HTTP SQL codecs, and GCP RS256 OAuth2 all execute in total,
verified Lean in `Qed/Server/`. Worker threads run an `SO_REUSEPORT` + `epoll`/`kqueue` socket
loop, share state through an `RwLock` `StateBox`, call `external` APIs over an outbound
keep-alive `rustls` pool, serve binary Protobuf RPCs and multiplexed WebSockets, and execute SSR
directly in memory via `App.ssrRenderNativeBytes`. For raw static directories without a `component`,
`qed serve` runs the same native HTTP/1.1 server directly from the `qed` CLI.

Every `component` app synthesizes a verified `Dehydrate` codec automatically so the browser
restores server-rendered state without re-fetching startup data; mark client-only fields
`ephemeral` to exclude them from serialization.

## What is proved vs. trusted

### Checked by Lean's kernel

- **State, database, contracts, & concurrency invariants:** Component `invariant`s prove preservation
  across `init`—including mountable components with `prop`s—every action, `for_each` child collections,
  and SSR `Dehydrate` slices via `dehydrate_inv`, while `App.guardRehydrate` enforces the invariant on
  untrusted client payloads. Server `invariant`s and `def` contracts prove initial validity, single-step
  preservation, two-state `old` monotonicity rules, `mutating ... requires ...` authorization policies,
  read-only non-mutation, `ensures` postconditions via `ProgEnsures`, and multi-core linearizability via
  transactional `atomic` blocks with rollback on error. Database queries prove parameterized
  SQL-injection non-interference, row-level `policy` rules, `immutable` columns, and column/transition
  invariants. Client RPC calls prove server `requires` preconditions and SSR-hydrated `session` auth at
  every call site, enforce exhaustive `catch` handling of `fail(.tag)` domain errors, and carry
  zero-trust re-verified `Ensured` postconditions back into client component invariants.
- **Views, HTML5 validity, and XSS closure:** Every `component` carries an automatic `valid_view`
  proof over `Html.valid` banning invalid HTML5 nesting such as `<div>` inside `<p>` or nested
  `<button>`s, children inside void elements, `<script>`/`<base>`/`<object>`/`<embed>` tags,
  inline `on*`/`srcdoc` attributes, raw markup injection, `<script>`/`<style>` breakout sequences,
  and untyped URLs on `href`, `src`, and `action`. Stylesheets prove kernel-reducible `cssHash`
  scoping and strip `/*` comments and `<`/`</style` breakout sequences. Inline and `holds_in` view
  invariants check both positive and negative styling predicates such as `roleLacks` and `tagLacks`.
- **Isomorphic SSR, DOM driver, and memoization:** Every `Dehydrate` codec proves `round_trip`
  and `dehydrate_view`, and every component emits `<Comp>.app_view_eq` alongside `canonical_congr_pred`
  transporting view predicates to `App.view`. [`Qed/Proofs/`](../Qed/Proofs)—spanning `DomArena.lean`,
  `KeyedReconcile.lean`, `ViewPatch.lean`, and `Hydration.lean`—proves against a pure `SpecDom` model
  using `CleanDomSubtree` and `VStateValid` invariants that mounting, W3C `insertBefore` patching,
  full `patchViewM` and `hydrateViewM` lifecycles including `V.forEach` lists, row/signal alignment,
  handler retention, local-cell and FIFO queue specs, HTML5 text-run hydration, `LawfulKey`-indexed
  `V.memo` skipping, and end-to-end SSR rehydration and patching match `Html.render`.
- **Schemas, routes, and wire codecs:** `schema` proves submit eligibility matches schema validity
  via `canSubmit_iff`. `router` proves `Router.round_trip` and `isSafeUrl_toURL`. `LawfulJson` and
  `LawfulProto` prove JSON and Protobuf round-trips, framing non-smuggling, bounded-depth parsing,
  binary RPC transparency, and full-stack SSR/RPC equivalence.
- **Total execution & JS lowering:** [`Js/Proofs.lean`](../Js/Proofs.lean) proves semantics
  preservation for constructor layouts, curried closures, non-recursive join-point blocks,
  tail-call loops and trampolines, `$.memo` thunks, and copy-on-write arrays with `refMark`
  snapshots.

Always check that an invariant states what you actually mean. Proving `0 ≤ quantity` prevents
underflow, not ordering more stock than exists; proving a route valid checks URL well-formedness,
not that the resource exists on disk or in a database.

### Trusted Computing Base

Qed relies on:

- Lean 4's kernel, macro and elaboration hygiene, compiler IR generator, and C backend.
- Pretty-printing the typed JS AST to `.mjs` text in [`Js/Backend.lean`](../Js/Backend.lean).
- The hand-written JS runtime in [`runtime/`](../runtime) and the native Rust I/O, crypto, and
  SQLite shim in [`rust/qed_server/`](../rust/qed_server) and [`Qed/Server/Prim.lean`](../Qed/Server/Prim.lean).
- Browser DOM and Web APIs, `rustls`/`ring`/`rusqlite`, and the OS kernel.

Because real browsers, network I/O, and memory allocation sit outside pure Lean models, Qed pairs
compile-time proofs with native end-to-end integration test suites.

## Verification gates, builds, and tests

Every JS build runs `verifyReachable` and `verifyNoServerLeakInClient` inside
[`Js/Backend.lean`](../Js/Backend.lean). Running `qed check` or `qed build` without `--dev` runs
all five verification gates in [`Cli/Verify.lean`](../Cli/Verify.lean):

1. **Forbidden tactics scan:** rejects `sorry`, `admit`, and `native_decide` across Lean sources.
2. **Axiom manifest:** runs `#print axioms` in [`scripts/axioms.lean`](../scripts/axioms.lean) on
   core framework, JS-lowering, Protobuf, SSR, server, and database theorems when present.
3. **Kernel environment gate:** `qedjs --verify-env` inspects the transitive closure of compiled
   declarations in [`Js/VerifyEnv.lean`](../Js/VerifyEnv.lean), permitting only `propext`,
   `Classical.choice`, and `Quot.sound` while rejecting custom axioms, `partial`, `unsafe`,
   `while`/`Lean.Loop.forIn` loops, user `@[implemented_by]`, and unverified `opaque` or
   `@[extern]` declarations outside `Qed.Dom` and `Qed.Server.Prim`.
4. **Effect coverage:** verifies every `Cmd` effect emitted in `Qed/` has a handler in
   [`runtime/qed_host.mjs`](../runtime/qed_host.mjs).
5. **Extern coverage:** `qedjs --check-externs` verifies every reachable `@[extern]` symbol has a
   matching export in [`runtime/qed_rt.mjs`](../runtime/qed_rt.mjs).

During development, `qed dev` watches `.lean` and runtime files, rebuilds `.qed/dev/`, restarts
the native server when present, and reloads the browser on success. Run `qed check`, `qed build`,
and `qed start` or `qed preview` for production builds; `qed build` emits content-hashed immutable
client assets `app.<hash>.mjs`, `qed_host.<hash>.mjs`, `styles.<hash>.css`, and `qed_manifest.json`
alongside `dist/server`.

`qed test` builds and runs the native Lean test runner in [`Tests/Runner.lean`](../Tests/Runner.lean) with zero Node.js or Python dependencies:

- [`Tests/Native/CliScaffold.lean`](../Tests/Native/CliScaffold.lean) — `qed new`, production builds with content-hashed assets, native SSR and `qed serve` traversal guards, and kernel/extern verification gates.
- [`Tests/Native/FullstackRpc.lean`](../Tests/Native/FullstackRpc.lean) — native Rust/Lean server RFC 9112 framing, concurrent handler pool, auth/expiring tokens/rotation, RS256 OAuth2 and TLS/HTTP external calls, SSR, and `/_qed/rpc/…` binary Protobuf RPCs.
- [`Tests/Native/Database.lean`](../Tests/Native/Database.lean) — multi-transport database integration tests running the same compiled server binary against embedded SQLite with restart durability, HTTP SQL, and PostgreSQL v3 wire protocol with SCRAM-SHA-256 auth, plus RLS isolation and client leak checks.
- [`Tests/Native/WebSocket.lean`](../Tests/Native/WebSocket.lean) — RFC 6455 multiplexed server channels, CSWSH origin enforcement, cross-worker broadcasts, and transactional `emit` rollback.
- Pipeline benchmarks live in [`Bench/`](../Bench) via `lake exe bench`.

## Source map

| Path | Purpose |
|------|---------|
| [`Qed.lean`](../Qed.lean) | Public framework umbrella; omits browser-only `Qed.Dom`/`Qed.Driver` and C-linked `Qed.Server.Native` so user modules target both JS and native servers. |
| [`Qed/Html.lean`](../Qed/Html.lean) · [`Qed/Jsx.lean`](../Qed/Jsx.lean) · [`Qed/Notation.lean`](../Qed/Notation.lean) | Typed `Html` / `Attr` / `Url` virtual DOM, static `Html.valid` HTML5/XSS rules, JSX syntax, and attribute/event helpers. |
| [`Qed/Style.lean`](../Qed/Style.lean) | First-class `style`, `theme`, `keyframes`, and `verify_theme` DSLs, WCAG contrast proofs, and scoped stylesheet rendering. |
| [`Qed/View.lean`](../Qed/View.lean) · [`Qed/Render.lean`](../Qed/Render.lean) · [`Qed/Diff.lean`](../Qed/Diff.lean) | Fine-grained `View` templates in `Qed/View/`, template lifting, tail-recursive `@[csimp]` HTML rendering, and keyed/positional diffing via `diff_apply`. |
| [`Qed/Dom.lean`](../Qed/Dom.lean) · [`Qed/Driver.lean`](../Qed/Driver.lean) · [`Qed/Proofs/`](../Qed/Proofs) | Total `MonadDom` interface, imperative browser driver in `Qed/Driver/`, and `SpecDom` refinement proofs covering `DomArena`, `ViewPatch`, `KeyedReconcile`, and `Hydration`. |
| [`Qed/Runtime.lean`](../Qed/Runtime.lean) · [`Qed/Resource.lean`](../Qed/Resource.lean) · [`Qed/Ssr.lean`](../Qed/Ssr.lean) | `App`, `Cmd` effects, `LocalDef` cells in `Qed/Runtime/`, `Resource`/`Cached`/`<Await>`, `Dehydrate` codecs, breakout-safe document serialization, and JS + native in-memory SSR. |
| [`Qed/Json.lean`](../Qed/Json.lean) · [`Qed/Proto.lean`](../Qed/Proto.lean) | Total JSON and binary Protocol Buffers parsers and encoders under `Qed/Json/` and `Qed/Proto/` with `LawfulJson` and `LawfulProto` proofs. |
| [`Qed/Date.lean`](../Qed/Date.lean) · [`Qed/Router.lean`](../Qed/Router.lean) · [`Qed/Schema.lean`](../Qed/Schema.lean) | Date utilities, `router` macro + `Router.round_trip`, and `schema` macro under `Qed/Schema/` generating `Field`, `Draft`, `formView`, `canSubmit_iff`, and JSON/Proto codecs. |
| [`Qed/Component.lean`](../Qed/Component.lean) · [`Qed/Invariant.lean`](../Qed/Invariant.lean) | `component` macro under `Qed/Component/`, and automated state, `for_each`, and view/styling invariant provers under `Qed/Invariant/`. |
| [`Qed/Server.lean`](../Qed/Server.lean) · [`Qed/Server/Db/`](../Qed/Server/Db) · [`rust/qed_server/`](../rust/qed_server) | `external`, `database`, `server`, and `fullstack` DSLs, invariant provers, HTTP/1.1 + WS + PostgreSQL/HTTP SQL stack in `Qed/Server/`, and the Rust `epoll`/`kqueue` + `rustls` + `rusqlite` + `openat2` shim. |
| [`Js/Backend.lean`](../Js/Backend.lean) · [`Js/VerifyEnv.lean`](../Js/VerifyEnv.lean) · [`Js/Proofs.lean`](../Js/Proofs.lean) · [`Js/Main.lean`](../Js/Main.lean) | Total Lean IR → typed JS AST compiler, `qedjs` CLI, kernel/client-leak gates, and lowering soundness proofs. |
| [`Cli.lean`](../Cli.lean) | `qed` CLI under `Cli/`: `dev`, `build`, `start`, `preview`, `test`, `check`, `clean`, `new`, `doctor`. |
| [`runtime/`](../runtime) | Browser runtime ES modules: `qed_rt.mjs`, `qed_dom.mjs`, `qed_host.mjs`. |
| [`Examples/`](../Examples) · [`Tests/`](../Tests) · [`scripts/axioms.lean`](../scripts/axioms.lean) | Guided example apps, compile-time checks, native Lean integration test suites, and `#print axioms` manifest. |
