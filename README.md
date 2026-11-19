# Qed

**A full-stack web framework where the compiler proves your app's behavior, not just its types.**

Qed is a web framework for [Lean 4](https://lean-lang.org) with a unified Python-esque syntax for JSX components, typed routing, schemas, scoped CSS, and an optional native full-stack server. Instead of checking types at rest and hoping tests catch logic bugs later, you write the rules your app must obey right inside your components, views, forms, and server handlers. Lean's kernel then proves they hold across *every* possible state transition and input before any code runs.

All proofs are erased at compile time. In the browser, Qed runs as plain, dependency-free JavaScript ES modules with **no Lean or WebAssembly runtime required**.

[Why Qed](#why-qed-what-other-frameworks-cant-give-you) · [See it in action](#see-it-in-action) · [Get started](#get-started) · [Example tour](Examples/README.md)

---

## Why Qed? (What other frameworks can't give you)

Most typed web frameworks (TypeScript, React, Next.js, Elm, Rust) can tell you that `quantity` is a `number`, or that a route handler returns a `Response`. What they **cannot** do at compile time is prove that your *behavior* obeys your domain rules:

| Concern | Typical frameworks | Qed |
|---|---|---|
| **State & business rules** | Tested on sample inputs; edge cases slip through to runtime assertions. | **Proved across every action and input**: bounds, state preconditions, child collections, and monotonic server state. |
| **HTML & XSS safety** | Linters warn on common cases; runtime sanitizers or CSP catch mistakes late. | **Proved valid at compile time**: rejects invalid HTML5 tag nesting, script and inline-event injection, and untyped URLs. |
| **Conditional styling** | Visual bugs in forgotten branches are found manually or via screenshot diffs. | **Proved across every branch**: guarantees every rendered button or role carries an allowed style in all states. |
| **Forms, JSON & RPCs** | Separate form state, UI validation, types, and backend decoders that drift over time. | **Generated from one schema**: editable draft, `<Schema.Form>`, proof-carrying type, and matching JSON & Protobuf codecs. |
| **Server concurrency & auth** | Missing auth checks, data races across `await`, and secret leaks rely on code review. | **Enforced by the compiler**: mutation auth policies, race-free `atomic` blocks around `await`, and no server leaks into client JS. |
| **DOM updates & SSR** | Virtual DOM and hydration mismatches surface only in browser logs at runtime. | **Verified rendering**: fine-grained DOM patches, keyed moves, and SSR hydration match fresh HTML rendering. |

Invariants are opt-in, so you don't have to prove everything up front. Start with ordinary components and schemas, and add rules wherever a bug would actually hurt.

---

## See it in action

### 1. State rules that can't be bypassed

Consider a quantity picker whose `inRange` invariant keeps its value between `1` and `10` (a slightly annotated version of the `App.lean` scaffolded by `qed new`):

```lean
import Qed
open Qed

component Quantity:
  state quantity = 1
  action increase when quantity < 10: quantity += 1
  action decrease when 1 < quantity:  quantity -= 1
  invariant inRange: 1 <= quantity <= 10
  view:
    <div>
      <button onClick={.decrease}>−</button>
      <span>{quantity}</span>
      <button onClick={.increase}>+</button>
    </div>
```

Qed checks that `inRange` holds on the initial state and after *every* action, including new actions you add months later.

If you forget the `when 1 < quantity` guard on `decrease`, compilation fails immediately and points to the exact branch:

```text
invariant `Quantity.inRange` isn't preserved by `Quantity.update`, the automation couldn't close every message.

  • case `decrease` still needs:  1 ≤ m.quantity - 1 ∧ m.quantity - 1 ≤ 10
```

Simple arithmetic, boolean, `Option`, and `match` invariants prove automatically. More complex properties (such as uniqueness or ID allocation across arrays) can lift child invariants with `for_each` or supply a short Lean proof with `:= by`. See the [invariant guide](docs/invariants.md).

### 2. Valid HTML and styling rules across every branch

Every `component` verifies its JSX view at compile time, catching invalid HTML5 nesting, unsafe tags, inline `on*` handlers, and untyped URLs before your app ever loads in a browser.

You can also enforce styling rules directly on rendered elements using scoped `css` definitions:

```lean
def enabledStyle : Style := css
  [backgroundColor (hex "2563eb"), color (hex "fff"), cursor "pointer"]

def disabledStyle : Style := css
  [backgroundColor (hex "e5e7eb"), color (hex "6b7280"), cursor "not-allowed"]

component ModeButtons:
  state editing = false
  invariant exactlyOne("edit", "save", enabledStyle, disabledStyle)
  view:
    <div>
      <button role="edit" disabled={editing} onClick={editing = true}
        {disabledStyle if editing else enabledStyle}>Edit</button>
      <button role="save" disabled={not editing} onClick={editing = false}
        {enabledStyle if editing else disabledStyle}>Save</button>
    </div>
```

Each `css` value compiles to a scoped class that Qed collects and injects automatically. The `exactlyOne` invariant proves that in every state, one button carries `enabledStyle` and the other carries `disabledStyle`. If a copy-paste mistake gives both buttons the same style or leaves one unstyled, the build fails.

### 3. One schema for forms, validation, and wire codecs

```lean
schema Order:
  name        : String where name.length >= 1
  quantity    : Nat    where 1 <= quantity <= 10
  acceptTerms : Bool   where acceptTerms
```

From this single `schema`, Qed generates:

- `Order.Draft` for editable, possibly incomplete UI input.
- `<Order.Form onSubmit={.submit}/>` (with self-hosted draft state by default, optional `reset`, or explicit `bind={draft}`), whose submit button is disabled until the draft satisfies every `where` rule and passes the validated `Order` directly to `onSubmit`.
- `Order.parse`, returning `Order?` where every field in `Order` carries a compile-time proof of its constraints.
- JSON and binary Protobuf codecs (`Order.encode` and matching decoders) that enforce the exact same rules on the wire.

See [Signup](Examples/Signup.lean) and [Bookshelf](Examples/Bookshelf.lean) for complete schema-backed forms (schemas also support context parameters like `schema Appt(today: Date):` for rules checked against live state).

### 4. Full-stack server rules, client–server contracts, and race-free `await`

When you build a full-stack app with `server` and `fullstack`, Qed extends those same compile-time guarantees across backend state, external HTTP calls, and binary Protobuf RPCs—using the exact same Python-esque expression and statement syntax on both client and server:

```lean
external PaymentApi:
  base "https://payments.example.com"
  post "/charge" charge(amount: Nat) -> Bool

server Store:
  state stock       : Nat = 10
  state totalOrders : Nat = 0

  invariant stock <= 10000
  invariant totalOrders >= old(totalOrders)
  invariant mutating stock requires ctx.userId != none

  def placeOrder(qty: Nat) -> Nat!:
    requires ctx.userId != none
    requires 1 <= qty <= 10
    ensures result <= 10000
    await PaymentApi.charge(qty)?
    return atomic:
      ensure stock >= qty else fail(.outOfStock)
      stock -= qty
      totalOrders += 1
      return stock
```

```lean
component Checkout:
  session user
  state lastRemaining : Nat = 0
  state status        = ""
  invariant validRemaining: lastRemaining <= 10000

  action buy(qty: Nat) when user.isSome, 1 <= qty <= 10:
    let rem = await Store.placeOrder(qty) catch:
      case .outOfStock: status = "Out of stock"
      case .failed(err): status = err
    lastRemaining = rem
    status = f"Left: {rem}"
```

- **Authorization & state invariants:** `mutating stock requires ctx.userId != none` rejects any endpoint that could modify `stock` without an authenticated user, while `old(totalOrders)` proves `totalOrders` can never decrease.
- **Compile-time TOCTOU protection:** If a handler uses `await`, Qed rejects any state read or write outside an `atomic:` block, and rejects `await` *inside* `atomic:` so locks never span network I/O.
- **Client–server RPC contracts (`requires` & `ensures`):** Calling `Store.placeOrder(qty)` from a `component` proves both session authentication (`session user`) and parameter `requires` at the client call site, while `ensures result <= 10000` is re-verified zero-trust in `FromProto` (`Ensured`) and feeds client component `invariant`s automatically.
- **Reactive server `query` caching:** Declaring `query item = Store.get(id) when let .detail(id) = route` (or `when user.isSome, ...`) enforces read-only server endpoints at compile time, derives collision-free binary Protobuf `Cached` keys with stale-while-revalidate and stale-response race rejection, preloads active queries on SSR with zero-refetch hydration, and propagates `requires`, `session`, and `ensures` (`Cached.all`) across components.
- **Typed domain errors & endpoint closure:** Inferred `fail(.tag)` variants enforce exhaustive `await ... catch:` handling in client actions, and `fullstack` proves every reachable client RPC targets a mounted server method while keeping server secrets and handlers out of client JS.

See [CloudBooks](Examples/CloudBooks.lean) for a complete full-stack app.

---

## What ships to production

Qed compiles the same source into clean, runtime-minimal artifacts:

- **Client-only or Node/Edge SSR:** `qed build` compiles your client code into plain JavaScript ES modules (`dist/app.mjs`) and emits `dist/ssr.mjs`, an async `(Request) => Response` handler that preserves component state across server rendering and hydration.
- **Full-stack native server (`fullstack`):** Packages your client bundle with a native server binary (`dist/server`) that serves static assets, binary Protobuf RPCs, and in-memory SSR.
- **No hidden escape hatches (`qed check`):** Production builds verify that every proof is complete, with no placeholders or unchecked escape hatches, so all guarantees are backed by Lean's kernel.

More details: [How Qed works](docs/architecture.md) · [Rendering & DOM proofs](docs/rendering.md)

---

## Get started

**Prerequisites:** Bash, Git, and `curl` for the installer, plus a Node.js version with `fetch`, `Request`, and `Response` for SSR. The installer sets up `elan` (Lean's toolchain manager) if needed, installs Qed into `~/.qed`, and builds the `qed` CLI (the first build also downloads the pinned Lean toolchain).

```bash
curl -sSfL https://raw.githubusercontent.com/JacobAsmuth/qed/main/install.sh | bash
export PATH="$HOME/.elan/bin:$HOME/.qed/bin:$PATH"
qed new myapp
cd myapp
qed dev
```

Open **http://localhost:8000** to see the `Quantity` app running with live reload. If an invariant fails during `qed dev`, the rebuild stops with the exact proof goal while the dev server keeps serving the last working build.

All Qed DSL blocks (`component`, `server`, `external`, `schema`, `router`, `invariant`, and JSX `{...}`) use plain ASCII Python-esque syntax (`and`, `or`, `not`, `in`, `not in`, `is`, `is not`, `<=`, `>=`, `==`, `!=`, `1 <= x <= 10`, `f"..."`, `a if cond else b`, `all x in xs: ...`)—no Unicode input required.

### CLI commands

```bash
qed check      # verify all proofs and client-isolation checks
qed build      # production client bundle + SSR handler (or native server) → dist/
qed start      # serve dist/ (alias: qed preview)
qed test       # run browser and full-stack test suites (when present)
qed doctor     # inspect local dependencies
qed clean      # remove build outputs
```

Inside this repository, `npm run dev`, `npm run build`, and `npm run test` are also available as aliases.

---

## Learn more

- **[Example tour](Examples/README.md):** Guided progression through six examples: [Counter](Examples/Counter.lean), [Todo](Examples/Todo.lean) (`for_each` collections & scoped CSS), [Signup](Examples/Signup.lean) (validated forms), [Chat](Examples/Chat.lean) (streaming SSE), [Bookshelf](Examples/Bookshelf.lean) (routing & SSR), and [CloudBooks](Examples/CloudBooks.lean) (full-stack server & RPCs).
- **[Components & apps](docs/components.md):** Props, `slot`s, `children`, `bind:`, `route`, `query`, `<Await>`, and stateful composition.
- **[Styling & verified CSS](docs/styling.md):** First-class `style` blocks, deterministic `extends`, typed `theme`s with WCAG contrast proofs, `keyframes`, `strict_tokens`, `verify_theme`, and build-time CSS extraction.
- **[Invariants](docs/invariants.md):** Automatic proofs, `:= by` tactic proofs, `for_each` collection lifts, and view/styling predicates.
- **[How Qed works](docs/architecture.md):** Compilation pipeline, trusted computing base, verification gates, and source map.
- **[Rendering & DOM proofs](docs/rendering.md):** Direct signal updates, keyed reconciliation, verified memoization, and browser equivalence tests.

Qed apps live inside Lean 4 files, so you can drop down to full Lean definitions and tactic proofs (`:= by`) whenever you need custom data structures or domain lemmas. JavaScript interop uses [typed ports](docs/components.md).

Questions and issues: [GitHub issues](https://github.com/JacobAsmuth/qed/issues).

## License

MIT. See [LICENSE](LICENSE).
