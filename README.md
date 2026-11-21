# Qed

**A full-stack web framework where the compiler proves your app's behavior, not just its types.**

Qed embeds a Python-esque web language—JSX components, scoped CSS, schemas, routing, and an optional native server—inside [Lean 4](https://lean-lang.org). Instead of checking types at rest and hoping tests catch logic bugs later, you write the rules your app must obey right inside your components, forms, styles, and server handlers. Lean's kernel proves they hold across *every* possible state transition and input before any code runs.

- **Plain JavaScript in the browser:** Proofs live in Lean's `Prop` universe and are erased at compile time. The browser ships plain, dependency-free ES modules—**no Lean or WebAssembly runtime**.
- **Opt-in proofs, plain ASCII syntax:** No Unicode symbols and no theorem-proving background required. Simple arithmetic, boolean, `Option`, and view invariants prove automatically; drop into Lean tactics with `:= by` only when you want custom domain proofs.
- **No silent escape hatches:** `qed check` verifies the compiled environment against Lean's standard axioms—rejecting `sorry`, `admit`, `native_decide`, and `unsafe` code.

[See it in action](#see-it-in-action) · [Types vs. proofs](#types-vs-proofs) · [What ships](#what-ships-to-production) · [Get started](#get-started) · [Examples](Examples/README.md)

---

## See it in action

### 1. State rules that can't be bypassed

Here is a quantity picker whose `inRange` invariant keeps `quantity` between `1` and `10`:

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

Qed checks that `inRange` holds on the initial state, across every action, and across SSR dehydration and rehydration. For properties like ID uniqueness across arrays, you can lift child invariants with `for_each` or supply a short Lean proof with `:= by`. See the [invariant guide](docs/invariants.md).

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

  invariant maxStock: stock <= 10000
  invariant ordersMonotonic: totalOrders >= old(totalOrders)
  invariant authStock: mutating stock requires ctx.userId != none

  def placeOrder(qty: Nat) -> Nat!:
    requires ctx.userId != none
    requires 1 <= qty <= 10
    ensures result <= 10000
    await PaymentApi.charge(qty)?
    atomic:
      if stock < qty: return fail(.outOfStock)
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

### 3. Verified databases and row-level policies

A `database` block declares your connection, tables, column constraints, row-level access policies, and state transitions in one place:

```lean
database NotesDb:
  url secret("DATABASE_URL")
  dev sqlite ".qed/dev.db"

  table notes:
    id      : Nat    primary_key
    ownerId : String immutable where 1 <= ownerId.length <= 64
    body    : String           where 1 <= body.length <= 2000
    version : Nat
    status  : String

    policy read, write requires some(row.ownerId) == ctx.userId
    invariant versionUp:  row.version >= old(row.version)
    invariant statusFlow: transition row.status: "draft" -> "published" -> "archived"
```

```lean
server NotesApi:
  use db : NotesDb

  def getNote(noteId: Nat) -> NotesDb.notes?!:
    requires ctx.userId != none
    if let some(uid) = ctx.userId:
      return await db.notes.findOne(where = r => r.id == noteId and r.ownerId == uid)?
    return none

  def publishNote(noteId: Nat) -> NotesDb.notes?!:
    requires ctx.userId != none
    let uid = ctx.userId.getD("")
    return await db.notes.updateOne(
      where = r => r.id == noteId and r.ownerId == uid and r.status == "draft",
      set   = r => { status = "published", version = r.version + 1 }
    )?
```

If an endpoint reads, updates, or deletes a row without proving the table's `policy`—for example, forgetting `r.ownerId == uid` in `getNote`—compilation fails:

```text
Database read policy `NotesDb.notes.read` failed in `getNote → NotesDb.notes.findOne`:
  • must prove: some ownerId = ctx.userId

Hint: Ensure `where = r => ...` (together with `requires` / `if` guards) implies `some(row.ownerId) == ctx.userId`.
```

- **Row-level policies:** `policy read` / `write` / `insert` / `update` / `delete` are checked on every query against `ctx` and `row`.
- **Column & transition checks:** Column `where` rules, `immutable` fields, `old(...)` invariants, and `transition` rules are proved on every `insert` and `update`, and `where` constraints connect through `requires` back to client RPC callers.
- **Parameterized queries:** Query values are always sent as bound parameters, never interpolated into SQL strings.
- **Swappable backends:** `DATABASE_URL` selects PostgreSQL, embedded SQLite, or HTTP SQL—including Cloudflare D1 and Turso—with the same server code, and tables and indexes are created automatically on startup.

See [DbChecks](Tests/DbChecks.lean) for positive and negative compile-time examples.

---

### 4. One schema for forms, validation, and wire codecs

```lean
schema Order:
  name        : String where name.length >= 1
  quantity    : Nat    where 1 <= quantity <= 10
  acceptTerms : Bool   where acceptTerms
```

From this single `schema`, Qed generates:

- `Order.Draft` for editable, possibly incomplete UI input.
- `<Order.Form onSubmit={.submit}/>`, whose submit button stays disabled until the draft satisfies every `where` rule and passes the validated `Order` directly to `onSubmit`.
- `Order.parse`, returning `Order?` where every field carries a compile-time proof of its constraints.
- Matching JSON and binary Protobuf codecs that enforce the exact same rules on the wire.

See [Signup](Examples/Signup.lean) and [Bookshelf](Examples/Bookshelf.lean) for complete schema-backed forms. Schemas also accept context parameters like `schema Appt(today: Date):` for rules checked against live state.

---

### 5. Valid HTML, scoped CSS, and styling invariants

Every `component` verifies its JSX view at compile time—rejecting invalid HTML5 tag nesting, unsafe tags, inline `on*` handlers, and untyped URLs before the app ever loads in a browser.

Scoped `style` blocks validate CSS properties and values at compile time, `theme` blocks can verify light and dark WCAG contrast ratios, and view invariants can enforce styling rules across every UI state:

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
  invariant modeExclusive: exactlyOne("edit", "save", enabledStyle, disabledStyle)
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

Typed web frameworks like TypeScript, Elm, and Rust can tell you that `quantity` is a `number` or that a handler returns a `Response`. What they cannot prove at compile time is that your *behavior* obeys your domain rules:

| Concern | Typical typed frameworks | Qed |
|---|---|---|
| **State & business rules** | Tested on sample inputs; edge cases slip into runtime assertions. | **Proved across every action and input:** bounds, preconditions, child collections, and monotonic server state. |
| **Server concurrency & auth** | Missing auth checks, races across `await`, and secret leaks rely on code review. | **Enforced by the compiler:** mutation auth policies, race-free `atomic:` blocks around `await`, and zero server leaks into client JS. |
| **Database queries & access** | Missing `WHERE owner_id = ...` filters, invalid column writes, and bad status updates fail at runtime. | **Checked on every query:** row-level `policy` rules, `immutable` columns, `where`/`transition` invariants, and bound SQL parameters. |
| **Forms, JSON & RPCs** | Separate form state, UI validation, types, and backend decoders that drift over time. | **Generated from one schema:** editable draft, `<Schema.Form>`, proof-carrying type, and matching JSON & Protobuf codecs. |
| **HTML & XSS safety** | Linters warn on common cases; runtime sanitizers or CSP catch mistakes late. | **Proved valid at compile time:** rejects invalid HTML5 nesting, script/inline-event injection, and untyped URLs. |
| **Conditional styling & contrast** | Visual bugs in forgotten branches are found manually or via screenshot diffs. | **Proved across every branch:** guarantees allowed role styles in all states and WCAG contrast on typed themes. |
| **DOM updates & SSR** | Virtual DOM and hydration mismatches surface in browser logs at runtime. | **Verified rendering:** fine-grained signal DOM patches, keyed moves, and SSR hydration proved equivalent to fresh HTML rendering. |

Invariants are opt-in: start with ordinary components and schemas, and add rules wherever a bug would actually hurt.

---

## What ships to production

`qed build` writes self-contained build outputs to `dist/`:

- **Frontend:** Plain, dependency-free JavaScript ES modules in `app.<hash>.mjs` and extracted CSS in `styles.<hash>.css`. Proofs are erased at compile time—no Lean or WebAssembly runtime ships to the browser.
- **Native server:** A single compiled `server` binary serving static assets, in-memory SSR, RPCs, WebSockets, and SQLite, PostgreSQL, or HTTP SQL databases.

More details—including the trusted computing base—are in [How Qed works](docs/architecture.md) and [Rendering & DOM proofs](docs/rendering.md).

---

## Get started

**Prerequisites:** Bash, Git, and `curl` for the installer. The installer sets up `elan` and `rustup`/`cargo` if missing, installs Qed into `~/.qed`, downloads the pinned Lean toolchain, and builds the `qed` CLI—no Node.js or Python required.

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
qed build      # production client bundle and native server → dist/
qed start      # serve dist/, alias: qed preview
qed serve      # serve a static directory natively
qed test       # run native test suites
qed doctor     # inspect local dependencies
qed clean      # remove build outputs
```

---

## Learn more

- **[Example tour](Examples/README.md):** Seven progressive examples—[Counter](Examples/Counter.lean), [Todo](Examples/Todo.lean), [Signup](Examples/Signup.lean), [Chat](Examples/Chat.lean), [Bookshelf](Examples/Bookshelf.lean), [CloudBooks](Examples/CloudBooks.lean), and [LiveRoom](Examples/LiveRoom.lean).
- **[Components & apps](docs/components.md):** Props, `slot`s, `children`, `bind:`, `route`, `query`, `subscribe`, optimistic `predict`, `<Await>`, and stateful composition.
- **[Styling & verified CSS](docs/styling.md):** First-class `style` blocks, deterministic `extends`, typed `theme`s with WCAG contrast proofs, `keyframes`, `strict_tokens`, `verify_theme`, and build-time CSS extraction.
- **[Invariants](docs/invariants.md):** Automatic proofs, `:= by` tactic proofs, `for_each` collection lifts, and view/styling predicates.
- **[How Qed works](docs/architecture.md):** Compilation pipeline, trusted computing base, verification gates, and source map.
- **[Rendering & DOM proofs](docs/rendering.md):** Direct signal updates, keyed reconciliation, and verified memoization.

Because Qed apps live inside Lean 4 files, you can drop down to full Lean definitions and `:= by` tactic proofs whenever you need custom data structures or domain lemmas. JavaScript interop uses [typed ports](docs/components.md).

Questions and issues: [GitHub issues](https://github.com/JacobAsmuth/qed/issues).

## License

MIT. See [LICENSE](LICENSE).
