# Qed

**A full-stack web framework where the compiler proves your app's behavior, not just its types.**

Qed embeds a Python-esque web language—JSX components, scoped CSS, schemas, routing, and an optional native server—inside [Lean 4](https://lean-lang.org). Instead of checking types at rest and hoping tests catch logic bugs later, you write the rules your app must obey right inside your components, forms, styles, and server handlers. Lean's kernel proves they hold across *every* possible state transition and input before any code runs.

- **Plain JavaScript in the browser:** Proofs live in Lean's `Prop` universe and are erased at compile time. The browser ships plain, dependency-free ES modules—**no Lean or WebAssembly runtime**.
- **Opt-in proofs, plain ASCII syntax:** No Unicode symbols and no theorem-proving background required. Simple arithmetic, boolean, `Option`, and view invariants prove automatically; drop into Lean tactics (`:= by`) only when you want custom domain proofs.
- **No silent escape hatches:** `qed check` verifies the compiled environment against Lean's standard axioms—rejecting `sorry`, `admit`, `native_decide`, and `unsafe` code.

[See it in action](#see-it-in-action) · [Types vs. proofs](#types-vs-proofs) · [What ships](#what-ships-to-production) · [Get started](#get-started) · [Examples](Examples/README.md)

---

## See it in action

### 1. State rules that can't be bypassed

Here is a quantity picker whose `inRange` invariant keeps `quantity` between `1` and `10` (a slightly annotated version of the `App.lean` scaffolded by `qed new`):

```lean
import Qed
open Qed

component Quantity:
  state quantity = 1
  action increase:
    if quantity < 10: quantity += 1
  action decrease:
    if quantity > 1: quantity -= 1
  invariant inRange: 1 <= quantity <= 10
  view:
    <div>
      <button onClick={.decrease}>−</button>
      <span>{quantity}</span>
      <button onClick={.increase}>+</button>
    </div>
```

If you forget the `if quantity > 1:` guard in `decrease`—or someone adds a new action months later that can underflow `quantity`—compilation fails immediately and points to the exact branch:

```text
Invariant `Quantity.inRange` failed in `Quantity.update`:
  • action `decrease` must satisfy:  1 <= quantity - 1 and quantity - 1 <= 10

Hint: Guard the failing branch with `if ...:`, fix the update, or weaken the invariant.
```

Qed checks that `inRange` holds on the initial state, across every action, and across SSR dehydration/rehydration. More complex properties (such as ID uniqueness across arrays) can lift child invariants with `for_each` or supply a short Lean proof with `:= by`. See the [invariant guide](docs/invariants.md).

---

### 2. Server auth, race-free `await`, and client–server contracts

With `server` and `fullstack`, the same compile-time guarantees extend across backend state, external HTTP calls, and binary Protobuf RPCs—using the same Python-esque syntax on both client and server:

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

  action buy(qty: Nat):
    if user.isSome and 1 <= qty <= 10:
      let rem = await Store.placeOrder(qty) catch:
        case .outOfStock: status = "Out of stock"
        case .failed(err): status = err
      lastRemaining = rem
      status = f"Left: {rem}"
```

- **Auth & monotonic state:** `mutating stock requires ctx.userId != none` rejects any endpoint that could modify `stock` without an authenticated user; `old(totalOrders)` proves `totalOrders` can never decrease.
- **No TOCTOU races across `await`:** In any handler that awaits I/O, Qed rejects state reads or writes outside `atomic:` and forbids `await` *inside* `atomic:`—so locks never span network calls and check-then-act races won't compile.
- **End-to-end `requires` & `ensures`:** Calling `Store.placeOrder(qty)` proves session auth and parameter preconditions at the client call site. Server `ensures` postconditions are re-checked zero-trust on incoming wire bytes and feed directly into client component invariants.
- **Typed errors, optimistic UI & reactive queries:** `fail(.tag)` enforces exhaustive `await ... catch:` handling; `await ... predict` gives verified optimistic updates with automatic rollback on failure; `query` declarations enforce read-only endpoints with SSR preloading and stale-response rejection; `fullstack` proves every client RPC targets a mounted server method while keeping server secrets out of client JS.

See [CloudBooks](Examples/CloudBooks.lean) for a complete full-stack app, and [LiveRoom](Examples/LiveRoom.lean) for multiplexed & third-party WebSockets.

---

### 3. One schema for forms, validation, and wire codecs

```lean
schema Order:
  name        : String where name.length >= 1
  quantity    : Nat    where 1 <= quantity <= 10
  acceptTerms : Bool   where acceptTerms
```

From this single `schema`, Qed generates:

- `Order.Draft` for editable, possibly incomplete UI input.
- `<Order.Form onSubmit={.submit}/>` (self-hosted draft state by default, with optional `reset` or explicit `bind={draft}`), whose submit button stays disabled until the draft satisfies every `where` rule and passes the validated `Order` directly to `onSubmit`.
- `Order.parse`, returning `Order?` where every field carries a compile-time proof of its constraints.
- Matching JSON and binary Protobuf codecs that enforce the exact same rules on the wire.

See [Signup](Examples/Signup.lean) and [Bookshelf](Examples/Bookshelf.lean) for complete schema-backed forms (schemas also accept context parameters like `schema Appt(today: Date):` for rules checked against live state).

---

### 4. Valid HTML, scoped CSS, and styling invariants

Every `component` verifies its JSX view at compile time—rejecting invalid HTML5 tag nesting, unsafe tags, inline `on*` handlers, and untyped URLs before the app ever loads in a browser.

Scoped `style` blocks validate CSS properties and values at compile time (and `theme` blocks can even verify light/dark WCAG contrast ratios), and view invariants can enforce styling rules across every UI state:

```lean
style enabledStyle:
  background-color: #2563eb
  color: #ffffff
  cursor: pointer

style disabledStyle:
  background-color: #e5e7eb
  color: #6b7280
  cursor: not-allowed

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

Each `style` compiles to a scoped, build-time-extracted class. The `exactlyOne` invariant proves that in every reachable state, one button carries `enabledStyle` and the other carries `disabledStyle`—a copy-paste bug that styles both identically or leaves one unstyled fails the build. See [Styling & verified CSS](docs/styling.md).

---

## Types vs. proofs

Typed web frameworks (TypeScript, Elm, Rust) can tell you that `quantity` is a `number` or that a handler returns a `Response`. What they cannot prove at compile time is that your *behavior* obeys your domain rules:

| Concern | Typical typed frameworks | Qed |
|---|---|---|
| **State & business rules** | Tested on sample inputs; edge cases slip into runtime assertions. | **Proved across every action and input:** bounds, preconditions, child collections, and monotonic server state. |
| **Server concurrency & auth** | Missing auth checks, races across `await`, and secret leaks rely on code review. | **Enforced by the compiler:** mutation auth policies, race-free `atomic:` blocks around `await`, and zero server leaks into client JS. |
| **Forms, JSON & RPCs** | Separate form state, UI validation, types, and backend decoders that drift over time. | **Generated from one schema:** editable draft, `<Schema.Form>`, proof-carrying type, and matching JSON & Protobuf codecs. |
| **HTML & XSS safety** | Linters warn on common cases; runtime sanitizers or CSP catch mistakes late. | **Proved valid at compile time:** rejects invalid HTML5 nesting, script/inline-event injection, and untyped URLs. |
| **Conditional styling & contrast** | Visual bugs in forgotten branches are found manually or via screenshot diffs. | **Proved across every branch:** guarantees allowed role styles in all states and WCAG contrast on typed themes. |
| **DOM updates & SSR** | Virtual DOM and hydration mismatches surface in browser logs at runtime. | **Verified rendering:** fine-grained signal DOM patches, keyed moves, and SSR hydration proved equivalent to fresh HTML rendering. |

Invariants are opt-in: start with ordinary components and schemas, and add rules wherever a bug would actually hurt.

---

## What ships to production

Qed compiles one source tree into runtime-minimal artifacts:

- **Client + Node/Edge SSR:** `qed build` lowers client code from Lean IR to content-hashed, dependency-free JavaScript ES modules (`dist/app.<hash>.mjs`, `dist/styles.<hash>.css`, and `dist/qed_manifest.json` served with `Cache-Control: immutable`) with fine-grained signal DOM updates, plus `dist/ssr.mjs`—an async `(Request) => Response` handler that preserves component state across SSR and hydration.
- **Full-stack native server (`fullstack`):** Compiles server logic—including verified HTTP/1.1, WebSocket framing, SSRF, and CSRF checks—through Lean's C backend and links it with a minimal Rust TLS/I/O shim (`rustls` + `openat2`) into a single `dist/server` binary serving static assets, binary Protobuf RPCs, multiplexed WebSockets, and zero-hop in-memory SSR.
- **Trusted computing base:** `qed check` verifies the Lean environment is free of `sorry` and unchecked axioms and enforces client isolation. The exact boundary between kernel-proved code and the TCB (the Lean-to-JS emitter, browser DOM driver, and Rust I/O shim) is documented in [How Qed works](docs/architecture.md).

More details: [How Qed works](docs/architecture.md) · [Rendering & DOM proofs](docs/rendering.md)

---

## Get started

**Prerequisites:** Bash, Git, and `curl` for the installer, plus a Node.js version with `fetch`, `Request`, and `Response` for JS SSR. The installer sets up `elan` (Lean's toolchain manager) and `rustup`/`cargo` (for the native full-stack server shim) if missing, installs Qed into `~/.qed`, and builds the `qed` CLI (the first build also downloads the pinned Lean toolchain).

```bash
curl -sSfL https://raw.githubusercontent.com/JacobAsmuth/qed/main/install.sh | bash
export PATH="$HOME/.elan/bin:$HOME/.qed/bin:$PATH"
qed new myapp
cd myapp
qed dev
```

Open **http://localhost:8000** to see the `Quantity` app running with live reload. If an invariant fails during `qed dev`, the rebuild stops with the exact proof goal while the dev server keeps serving the last working build.

### CLI commands

```bash
qed check      # verify all proofs, axioms, and client-isolation checks
qed build      # production client bundle + SSR handler (or native server) → dist/
qed start      # serve dist/ (alias: qed preview)
qed test       # run browser and full-stack test suites (when present)
qed doctor     # inspect local dependencies
qed clean      # remove build outputs
```

Inside this repository, `npm run dev`, `npm run build`, and `npm run test` are also available as aliases.

---

## Learn more

- **[Example tour](Examples/README.md):** Seven progressive examples—[Counter](Examples/Counter.lean), [Todo](Examples/Todo.lean) (`for_each` collections & scoped CSS), [Signup](Examples/Signup.lean) (validated forms), [Chat](Examples/Chat.lean) (streaming SSE), [Bookshelf](Examples/Bookshelf.lean) (routing & SSR), [CloudBooks](Examples/CloudBooks.lean) (full-stack server & RPCs), and [LiveRoom](Examples/LiveRoom.lean) (multiplexed & third-party WebSockets).
- **[Components & apps](docs/components.md):** Props, `slot`s, `children`, `bind:`, `route`, `query`, `subscribe`, optimistic `predict`, `<Await>`, and stateful composition.
- **[Styling & verified CSS](docs/styling.md):** First-class `style` blocks, deterministic `extends`, typed `theme`s with WCAG contrast proofs, `keyframes`, `strict_tokens`, `verify_theme`, and build-time CSS extraction.
- **[Invariants](docs/invariants.md):** Automatic proofs, `:= by` tactic proofs, `for_each` collection lifts, and view/styling predicates.
- **[How Qed works](docs/architecture.md):** Compilation pipeline, trusted computing base, verification gates, and source map.
- **[Rendering & DOM proofs](docs/rendering.md):** Direct signal updates, keyed reconciliation, verified memoization, and browser equivalence tests.

Because Qed apps live inside Lean 4 files, you can drop down to full Lean definitions and tactic proofs (`:= by`) whenever you need custom data structures or domain lemmas. JavaScript interop uses [typed ports](docs/components.md).

Questions and issues: [GitHub issues](https://github.com/JacobAsmuth/qed/issues).

## License

MIT. See [LICENSE](LICENSE).
