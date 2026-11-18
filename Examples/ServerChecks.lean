import Qed
open Qed

namespace ServerChecks

external PingApi
  base "https://api.example.com"

  get "/ping"
    ping() -> String

schema CheckedItem where
  label : String where 1 <= label.length, label.length <= 32
  stock : Nat    where stock <= 100

-- 1. Rejects TOCTOU state read outside `atomic` in an `await`-using function
/--
error: cannot access server state `count` outside an `atomic` block in `bump` because `bump` uses `await` (prevents TOCTOU data races across suspension points)
-/
#guard_msgs in
server BadToctouRead
  state count: Nat = 0
  fn bump() -> Nat!
    let c = count
    let _ = await PingApi.ping()?
    return c

-- 2. Rejects state mutation outside `atomic` in an `await`-using function
/--
error: cannot access server state `count` outside an `atomic` block in `bump` because `bump` uses `await` (prevents TOCTOU data races across suspension points)
-/
#guard_msgs in
server BadOutsideAtomicMut
  state count: Nat = 0
  fn bump() -> Nat!
    let _ = await PingApi.ping()?
    count += 1
    return 1

-- 3. Rejects redundant `atomic` in a synchronous function ("only one way")
/--
error: redundant `atomic` block: `bump` has no `await` calls, so it already executes atomically
-/
#guard_msgs in
server BadRedundantAtomic
  state count: Nat = 0
  fn bump() -> Nat
    atomic
      count += 1
    return count

-- 4. Rejects `await` inside an `atomic` block (locks never span network I/O)
/--
error: cannot use `await` inside an `atomic` block; perform external I/O outside `atomic` so shared locks never span network calls
-/
#guard_msgs in
server BadAwaitInAtomic
  state count: Nat = 0
  fn bump() -> Nat!
    let _ = await PingApi.ping()?
    atomic
      let _ = await PingApi.ping()?
      count += 1
    return 1

-- 5. Rejects unhandled fallible `await` binding without `?` or `catch`
/--
error: unhandled fallible `await` expression; append `?` to propagate errors or use `let x = await ... catch err` to handle them inline
-/
#guard_msgs in
server BadUnhandledError
  fn callIt() -> String
    let res = await PingApi.ping()
    return "ok"

-- 6. Rejects unproven array indexing `items[idx]` without bounds guard
/--
error: unsolved goals
_s0 : State
ctx : Server.RequestCtx
idx : Nat
⊢ idx < _s0.items.size
-/
#guard_msgs in
server BadArrayBounds
  state items: Nat[] = [10, 20]
  fn readAt(idx: Nat) -> Nat
    return items[idx]

-- 7. Rejects invalid `schema` `Field` refinement at compile time
/--
error: unsolved goals
m✝ : Type → Type
inst✝¹ : Monad m✝
inst✝ : Server.MonadServer m✝
ctx : Server.RequestCtx
⊢ False
-/
#guard_msgs in
server BadFieldRefinement
  fn makeEmpty() -> CheckedItem
    return CheckedItem(label = "", stock = 5)

-- 8. Rejects mutation that can violate a single-state `invariant`
/--
error: server invariant `StateInv` could not be proved for `overflow`.
Remaining proof obligation:
  _s0.stock + 50 ≤ 100
Guard state mutations with `if ...` or `requires ...` so this invariant holds across every branch.
-/
#guard_msgs in
server BadSingleStateInv
  state stock: Nat = 10
  invariant stock <= 100
  fn overflow() -> Nat
    stock += 50
    return stock

-- 9. Rejects mutation that violates a two-state `old(...)` monotonicity `invariant`
/--
error: server invariant `orders >= old(orders)` could not be proved for `resetOrders`.
Remaining proof obligation:
  0 ≥ _s0.orders
Guard state mutations with `if ...` or `requires ...` so this invariant holds across every branch.
-/
#guard_msgs in
server BadTwoStateInv
  state orders: Nat = 5
  invariant orders >= old(orders)
  fn resetOrders() -> Nat
    orders = 0
    return orders

-- 10. Rejects mutation that violates `invariant mutating <field> requires <cond>`
/--
error: server invariant `mutating items requires ctx.userId != none` could not be proved for `unauthenticatedPush`.
Remaining proof obligation:
  _s0.items.push x = _s0.items ∨ ¬ctx.userId = none
Guard state mutations with `if ...` or `requires ...` so this invariant holds across every branch.
-/
#guard_msgs in
server BadMutatingAuthInv
  state items: Nat[] = [1]
  invariant mutating items requires ctx.userId != none
  fn unauthenticatedPush(x: Nat) -> Nat
    items.push(x)
    return items.size

-- 11. Rejects false server `ensures` postcondition at compile time
/--
error: server postcondition `ensures result > 10` could not be proved for `compute`.
Remaining proof obligation:
  5 > 10
Ensure every successful return path establishes `result > 10`.
-/
#guard_msgs in
server BadServerEnsures
  fn compute(x: Nat) -> Nat
    ensures result > 10
    return 5

-- Valid helper servers for client RPC contract, session auth, domain catch, and closure tests
server CheckedSrv
  fn buy(qty: Nat) -> Nat!
    requires ctx.userId != none
    requires 1 <= qty && qty <= 50
    ensures result == qty && 1 <= result && result <= 50
    if qty == 49
      return fail(.soldOut)
    if qty == 50
      return fail(.limitReached)
    return qty

server OtherSrv
  fn ping() -> Nat
    return 1

-- 12. Rejects client RPC call when server parameter `requires` cannot be proved
/--
error: RPC `CheckedSrv.buy` precondition `1 <= qty && qty <= 50` could not be proved at this call site.
Supply literals, guard with `when`/`if`, pass refined `Field`/`Ensured` values, or declare a component `invariant`.
-/
#guard_msgs in
component BadClientRequiresParam where
  session user
  state last : Nat := 0
  action go when user.isSome =>
    let n := await CheckedSrv.buy(0) catch
      | _ => ()
    last := n
  view => <span>{last}</span>

-- 13. Rejects client RPC call requiring `ctx.userId != none` without authenticated `session`
/--
error: RPC `CheckedSrv.buy` requires an authenticated session (`ctx.userId != none`), but component `BadClientRequiresAuth` has no `session` state.
Add `session user` and guard the call with `when user.isSome =>` or `if user.isSome then ...`.
-/
#guard_msgs in
component BadClientRequiresAuth where
  state last : Nat := 0
  action go =>
    let n := await CheckedSrv.buy(1) catch
      | _ => ()
    last := n
  view => <span>{last}</span>

-- 14. Rejects non-exhaustive client `await ... catch` missing a typed `fail(.tag)` branch
/--
error: `await CheckedSrv.buy(...)` has unhandled domain error(s): .limitReached; handle them with `catch | .tag => ...`
-/
#guard_msgs in
component BadClientNonExhaustiveCatch where
  session user
  state last : Nat := 0
  action go when user.isSome =>
    let n := await CheckedSrv.buy(1) catch
      | .soldOut   => ()
      | .failed _  => ()
    last := n
  view => <span>{last}</span>

-- 15. Rejects `fullstack` whose client calls an RPC on an unmounted server
component CallsOther where
  state v : Resource Nat := .idle
  action go =>
    v := await OtherSrv.ping()
  view => <span>ok</span>

/--
error: `fullstack BadFs` mounts `server CheckedSrv`, but client `CallsOther` calls RPC `OtherSrv.ping` on unmounted server `OtherSrv`
-/
#guard_msgs in
fullstack BadFs
  server CheckedSrv
  client CallsOther
  title "Bad"

-- 16. Component `invariant` discharges server parameter `requires`, and server `ensures` flows into client `invariant`
component InvariantSatisfiesRequires where
  session user
  state qty    : Nat := 5
  state bought : Nat := 0
  invariant qtyInBounds : 1 ≤ qty, qty ≤ 50
  invariant boughtValid : bought = 0 ∨ (1 ≤ bought ∧ bought ≤ 50)
  action setQty (q : Nat) when (1 ≤ q ∧ q ≤ 50) =>
    qty := q
  action purchase when user.isSome =>
    let got := await CheckedSrv.buy(qty) catch
      | .soldOut      => ()
      | .limitReached => ()
      | .failed _     => ()
    bought := got
  view => <span>{bought}</span>

end ServerChecks
