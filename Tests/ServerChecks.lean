import Qed
open Qed

namespace ServerChecks

external PingApi:
  base "https://api.example.com"

  get "/ping"
    ping() -> String

schema CheckedItem:
  label : String where 1 <= label.length <= 32
  stock : Nat    where stock <= 100

-- 1. Rejects TOCTOU state read outside `atomic` in an `await`-using function
/--
error: cannot access server state `count` outside an `atomic` block in `bump` because `bump` uses `await` (prevents TOCTOU data races across suspension points)
-/
#guard_msgs in
server BadToctouRead:
  state count: Nat = 0
  def bump() -> Nat!:
    let c = count
    await PingApi.ping()?
    return c

-- 2. Rejects state mutation outside `atomic` in an `await`-using function
/--
error: cannot access server state `count` outside an `atomic` block in `bump` because `bump` uses `await` (prevents TOCTOU data races across suspension points)
-/
#guard_msgs in
server BadOutsideAtomicMut:
  state count: Nat = 0
  def bump() -> Nat!:
    await PingApi.ping()?
    count += 1
    return 1

-- 3. Rejects redundant `atomic` in a synchronous function ("only one way")
/--
error: redundant `atomic` block: `bump` has no `await` calls, so it already executes atomically
-/
#guard_msgs in
server BadRedundantAtomic:
  state count: Nat = 0
  def bump() -> Nat:
    atomic:
      count += 1
    return count

-- 4. Rejects `await` inside an `atomic` block (locks never span network I/O)
/--
error: cannot use `await` inside an `atomic` block; perform external I/O outside `atomic` so shared locks never span network calls
-/
#guard_msgs in
server BadAwaitInAtomic:
  state count: Nat = 0
  def bump() -> Nat!:
    await PingApi.ping()?
    atomic:
      await PingApi.ping()?
      count += 1
    return 1

-- 5. Rejects unhandled fallible `await` binding without `?` or `catch`
/--
error: unhandled fallible `await` expression; append `?` to propagate errors or use `let x = await ... catch err:` to handle them inline
-/
#guard_msgs in
server BadUnhandledError:
  def callIt() -> String:
    let res = await PingApi.ping()
    return "ok"

-- 6. Rejects unproven array indexing `items[idx]` without bounds guard
/--
error: Array index `idx` could be out of bounds for `items`:
  • must satisfy:  idx < items.size

Hint: Guard this access with `if idx < items.size:` or `ensure idx < items.size else ...`.
-/
#guard_msgs in
server BadArrayBounds:
  state items: Nat[] = [10, 20]
  def readAt(idx: Nat) -> Nat:
    return items[idx]

-- 7. Rejects invalid `schema` `Field` refinement at compile time
/--
error: Schema field rule `1 <= "".length and "".length <= 32` failed for `""`.

Hint: Guard this value with `if ...:`, `ensure ... else ...`, or a `requires` precondition so it satisfies the schema's `where` rule.
-/
#guard_msgs in
server BadFieldRefinement:
  def makeEmpty() -> CheckedItem:
    return CheckedItem(label="", stock=5)

-- 8. Rejects mutation that can violate a single-state `invariant`
/--
error: Server invariant `stock <= 100` failed in `overflow`:
  • must satisfy:  stock + 50 <= 100

Hint: Guard state mutations with `if ...:`, `ensure ... else ...`, or `requires ...` so this invariant holds across every branch.
-/
#guard_msgs in
server BadSingleStateInv:
  state stock: Nat = 10
  invariant stock <= 100
  def overflow() -> Nat:
    stock += 50
    return stock

-- 9. Rejects mutation that violates a two-state `old(...)` monotonicity `invariant`
/--
error: Server invariant `orders >= old(orders)` failed in `resetOrders`:
  • must satisfy:  0 >= orders

Hint: Guard state mutations with `if ...:`, `ensure ... else ...`, or `requires ...` so this invariant holds across every branch.
-/
#guard_msgs in
server BadTwoStateInv:
  state orders: Nat = 5
  invariant orders >= old(orders)
  def resetOrders() -> Nat:
    orders = 0
    return orders

-- 10. Rejects mutation that violates `invariant mutating <field> requires <cond>`
/--
error: Server invariant `mutating items requires ctx.userId != none` failed in `unauthenticatedPush`:
  • must satisfy:  items.push x = items or ctx.userId != none

Hint: Add a matching `requires` clause or guard mutations of that field with `if ...:` / `ensure ... else ...`.
-/
#guard_msgs in
server BadMutatingAuthInv:
  state items: Nat[] = [1]
  invariant mutating items requires ctx.userId != none
  def unauthenticatedPush(x: Nat) -> Nat:
    items.push(x)
    return items.size

-- 11. Rejects false server `ensures` postcondition at compile time
/--
error: Server postcondition `ensures result > 10` failed in `compute`:
  • must satisfy:  5 > 10

Hint: Ensure every successful return path establishes `result > 10`.
-/
#guard_msgs in
server BadServerEnsures:
  def compute(x: Nat) -> Nat:
    ensures result > 10
    return 5

-- Valid helper servers for client RPC contract, session auth, domain catch, and closure tests
server CheckedSrv:
  def buy(qty: Nat) -> Nat!:
    requires ctx.userId != none
    requires 1 <= qty <= 50
    ensures result == qty, 1 <= result <= 50
    if qty == 49:
      return fail(.soldOut)
    elif qty == 50:
      return fail(.limitReached)
    return qty

server OtherSrv:
  def ping() -> Nat:
    return 1

-- 12. Rejects client RPC call when server parameter `requires` cannot be proved
/--
error: RPC `CheckedSrv.buy` precondition `1 <= qty <= 50` could not be proved here:
  • must satisfy:  1 <= 0 and 0 <= 50

Hint: Pass valid arguments, guard with `if`/`ensure`, or add a component `invariant`.
-/
#guard_msgs in
component BadClientRequiresParam:
  session user
  state last : Nat = 0
  action go:
    if user.isSome:
      let n = await CheckedSrv.buy(0) catch:
        case _: pass
      last = n
  view: <span>{last}</span>

-- 13. Rejects client RPC call requiring `ctx.userId != none` without authenticated `session`
/--
error: RPC `CheckedSrv.buy` requires an authenticated session (`ctx.userId != none`), but `BadClientRequiresAuth` has no `session` field.

Hint: Add `session user` to `BadClientRequiresAuth` and guard the call with `if user.isSome:`.
-/
#guard_msgs in
component BadClientRequiresAuth:
  state last : Nat = 0
  action go:
    let n = await CheckedSrv.buy(1) catch:
      case _: pass
    last = n
  view: <span>{last}</span>

-- 14. Rejects non-exhaustive client `await ... catch` missing a typed `fail(.tag)` branch
/--
error: `await CheckedSrv.buy(...)` has unhandled domain error(s): .limitReached; handle them with `catch: case .limitReached: ...`
-/
#guard_msgs in
component BadClientNonExhaustiveCatch:
  session user
  state last : Nat = 0
  action go:
    if user.isSome:
      let n = await CheckedSrv.buy(1) catch:
        case .soldOut:   pass
        case .failed(_): pass
      last = n
  view: <span>{last}</span>

-- 15. Rejects `fullstack` whose client calls an RPC on an unmounted server
component CallsOther:
  state v : Resource Nat
  action go:
    v = await OtherSrv.ping()
  view: <span>ok</span>

/--
error: `fullstack BadFs` mounts `server CheckedSrv`, but client `CallsOther` calls RPC `OtherSrv.ping` on unmounted server `OtherSrv`
-/
#guard_msgs in
fullstack BadFs:
  server CheckedSrv
  client CallsOther
  title "Bad"

-- 16. Component `invariant` discharges server parameter `requires`, and server `ensures` flows into client `invariant`
component InvariantSatisfiesRequires:
  session user
  state qty    : Nat = 5
  state bought : Nat = 0
  invariant qtyInBounds: 1 <= qty <= 50
  invariant boughtValid: bought == 0 or 1 <= bought <= 50
  action setQty(q: Nat):
    if 1 <= q <= 50:
      qty = q
  action purchase:
    ensure user.isSome else return
    let got = await CheckedSrv.buy(qty) catch:
      case .soldOut:      pass
      case .limitReached: pass
      case .failed(_):    pass
    bought = got
  view: <span>{bought}</span>

server QuerySrv:
  state hits : Nat = 0
  def bump() -> Nat:
    hits += 1
    return hits
  def quote(qty: Nat) -> Nat:
    requires ctx.userId != none
    requires 1 <= qty <= 50
    ensures result == qty, 1 <= result <= 50
    return qty

-- 17. Rejects reactive `query` calling a mutating server RPC (read-only gate)
/--
error: reactive `query count` cannot call mutating server RPC `QuerySrv.bump`; `query` only permits read-only server functions
-/
#guard_msgs in
component BadMutatingQuery:
  query count = QuerySrv.bump()
  view: <span>ok</span>

-- 18. Rejects reactive `query` when server parameter `requires` cannot be proved
/--
error: RPC `QuerySrv.quote` precondition `1 <= qty <= 50` could not be proved here:
  • must satisfy:  1 <= 0 and 0 <= 50

Hint: Pass valid arguments, guard with `if`/`ensure`, or add a component `invariant`.
-/
#guard_msgs in
component BadQueryRequiresParam:
  session user
  query q = QuerySrv.quote(0) if user.isSome
  view: <span>ok</span>

-- 19. Rejects reactive `query` requiring `ctx.userId != none` without an active session guard
/--
error: RPC `QuerySrv.quote` requires an authenticated session (`user != none`), which could not be proved here.

Hint: Guard this call with `if user.isSome:`, `ensure user.isSome else return`, or `invariant ...: user.isSome`.
-/
#guard_msgs in
component BadQueryRequiresAuth:
  session user
  query q = QuerySrv.quote(5)
  view: <span>ok</span>

-- 20. Reactive `query` proves `requires` from `if` + `invariant`, and feeds `ensures` into `Cached.all`
component VerifiedQueryFlow:
  session user
  state qty : Nat = 5
  invariant qtyInBounds: 1 <= qty <= 50
  query quote = QuerySrv.quote(qty) if user.isSome
  invariant quoteValid: quote.all(v => 1 <= v <= 50)
  query echoed = QuerySrv.quote(v) if let .ok(v) = quote.state, user.isSome
  invariant echoedValid: echoed.all(v => 1 <= v <= 50)
  action setQty(q: Nat):
    if 1 <= q <= 50:
      qty = q
  view:
    <div>
      <Await of={quote} as={v}><span>{f"{v}"}</span></Await>
      <Await of={echoed} as={e}><span>{f"{e}"}</span></Await>
    </div>

-- 21. Rejects 3rd-party `external` combining client-usable `ws` channels with server `auth` secrets
/--
error: `external BadAuthWs` declares client-usable `ws` channels and cannot attach server `auth` secrets; split server-authenticated HTTP endpoints into a separate `external` block
-/
#guard_msgs in
external BadAuthWs:
  base "wss://ws.example.com"
  auth bearer(secret("WS_SECRET"))
  ws "/stream"
    feed() -> String

-- 22. Rejects `emit` violating channel `ensures` at compile time
/--
error: Channel `ensures` postcondition failed at `emit`:
  • must satisfy:  99 <= 50

Hint: Ensure the emitted event satisfies the channel's `ensures` clause.
-/
#guard_msgs in
server BadEmitSrv:
  channel bounded() -> Nat:
    ensures event <= 50
    on_join:
      pass
  def pushBad() -> Unit:
    emit bounded(99)
    return ()

server WsCheckSrv:
  channel gauge(room: Nat) -> Nat:
    requires ctx.userId != none
    requires room <= 10
    ensures event <= 50
    on_join:
      pass
    on_send(v: Nat):
      requires v <= 50
      emit gauge(room, v)
    on_leave:
      pass

-- 23. Rejects `subscribe` requiring `ctx.userId != none` without session guard
/--
error: RPC `WsCheckSrv.gauge` requires an authenticated session (`user != none`), which could not be proved here.

Hint: Guard this call with `if user.isSome:`, `ensure user.isSome else return`, or `invariant ...: user.isSome`.
-/
#guard_msgs in
component BadSubNoAuth:
  session user
  subscribe g = WsCheckSrv.gauge(1):
    on_message(v):
      pass
  view: <span>ok</span>

-- 24. Rejects `subscribe` violating channel parameter `requires`
/--
error: RPC `WsCheckSrv.gauge` precondition `room <= 10` could not be proved here:
  • must satisfy:  99 <= 10

Hint: Pass valid arguments, guard with `if`/`ensure`, or add a component `invariant`.
-/
#guard_msgs in
component BadSubBadParam:
  session user
  subscribe g = WsCheckSrv.gauge(99) if user.isSome:
    on_message(v):
      pass
  view: <span>ok</span>

-- 25. Rejects `send` violating channel `on_send` `requires`
/--
error: RPC `WsCheckSrv.gauge.send` precondition `v <= 50` could not be proved here:
  • must satisfy:  77 <= 50

Hint: Pass valid arguments, guard with `if`/`ensure`, or add a component `invariant`.
-/
#guard_msgs in
component BadSendParam:
  session user
  subscribe g = WsCheckSrv.gauge(1) if user.isSome:
    on_message(v):
      pass
  action go:
    send g(77)
  view: <span>ok</span>

-- 26. Rejects `fullstack` mounting a server when client subscribes to a different server's channel
component SubOtherWs:
  session user
  subscribe g = WsCheckSrv.gauge(1) if user.isSome:
    on_message(_):
      pass
  view: <span>ok</span>

/--
error: `fullstack BadWsFs` mounts `server CheckedSrv`, but client `SubOtherWs` subscribes to WebSocket channel `WsCheckSrv.gauge` on unmounted server `WsCheckSrv`
-/
#guard_msgs in
fullstack BadWsFs:
  server CheckedSrv
  client SubOtherWs
  title "BadWs"

-- 27. Positive: channel `ensures event <= 50` flows automatically into client component `invariant`
component VerifiedWsEnsures:
  session user
  state lastVal : Nat = 0
  invariant lastBounded: lastVal <= 50
  subscribe g = WsCheckSrv.gauge(1) if user.isSome:
    on_message(v):
      lastVal = v
  action sendOk(n: Nat):
    if n <= 50:
      send g(n)
  view: <span>{lastVal}</span>

end ServerChecks
