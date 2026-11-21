import Qed
open Qed

namespace SpeculativeChecks

/-! ## Shared Test Schemas & Servers -/

schema SpecBook:
  slot  : Nat    where slot <= 1000
  title : String where 1 <= title.length <= 64
  stock : Nat    where stock <= 10000

server StoreSrv:
  state stock : Nat = 10
  invariant maxStock: stock <= 10000

  def placeOrder(qty: Nat) -> Nat!:
    requires ctx.userId != none
    requires 1 <= qty <= 10
    ensures result <= 10000
    if stock < qty: return fail(.outOfStock)
    stock -= qty
    return stock

  def claim(id: Nat) -> Nat!:
    ensures result <= 100
    if id == 0:
      return fail(.locked)
    if id == 99:
      return 2
    return 1

  def fetchItems() -> Nat[]:
    return [10, 20]

server CatalogSrv:
  state books : SpecBook[] = [
    SpecBook(slot=0, title="Lean 4", stock=10),
    SpecBook(slot=1, title="Qed", stock=5)
  ]

  def order(idx: Nat, qty: Nat) -> SpecBook!:
    requires ctx.userId != none
    requires 1 <= qty <= 10
    ensures result.slot == idx, result.stock < 10000
    if idx >= books.size: return fail(.notFound)
    if books[idx].slot != idx: return fail(.notFound)
    if books[idx].stock < qty: return fail(.outOfStock)
    books[idx].stock -= qty
    return books[idx]

/-! ## 1. Compile-Time Negative Tests (`#guard_msgs`) -/

-- 1a. Rejects prediction that violates server `ensures` postcondition
/--
error: Predicted response for `StoreSrv.placeOrder` does not satisfy server `ensures` postcondition:
  • must satisfy:  20000 <= 10000

Hint: Ensure the predicted value satisfies the server method's `ensures` clause (or guard it inside a `predict:` block).
-/
#guard_msgs in
component BadPredictEnsures:
  session user
  state remaining : Nat = 10
  action buy:
    if user.isSome:
      let rem = await StoreSrv.placeOrder(1) predict 20000 catch:
        case .outOfStock: pass
        case .failed(_): pass
      remaining = rem
  view: <span>{remaining}</span>

-- 1b. Rejects side effects inside speculative continuation after `predict`
/--
error: cannot run side effects or emit events inside a speculative continuation after `predict` (side effects cannot be rolled back); move it into `on_confirm:`
-/
#guard_msgs in
component BadSpecPerform:
  session user
  port log : String
  state remaining : Nat = 10
  invariant validRemaining: remaining <= 10000
  action buy:
    if user.isSome and 1 <= remaining:
      let rem = await StoreSrv.placeOrder(1) predict remaining - 1 catch:
        case .outOfStock: pass
        case .failed(_): pass
      remaining = rem
      log.send("bought")
  view: <span>{remaining}</span>

-- 1c. Rejects nested `await` inside speculative continuation after `predict`
/--
error: cannot `await` inside a speculative continuation after `predict`; move sequential `await` calls into `on_confirm:`
-/
#guard_msgs in
component BadSpecNestedAwait:
  session user
  state remaining : Nat = 10
  invariant validRemaining: remaining <= 10000
  action buy:
    if user.isSome and 1 <= remaining:
      let rem = await StoreSrv.placeOrder(1) predict remaining - 1 catch:
        case .outOfStock: pass
        case .failed(_): pass
      remaining = rem
      let _ = await StoreSrv.claim(1) catch:
        case _: pass
  view: <span>{remaining}</span>

-- 1d. Rejects `on_confirm` without `predict`
/--
error: `on_confirm` requires a `predict` clause on the same `await`
-/
#guard_msgs in
component BadOnConfirmWithoutPredict:
  session user
  state remaining : Nat = 10
  action buy:
    if user.isSome:
      let rem = await StoreSrv.placeOrder(1)
        on_confirm: remaining = rem
        catch:
          case .outOfStock: pass
          case .failed(_): pass
      remaining = rem
  view: <span>{remaining}</span>

-- 1e. Rejects `rollback` without `predict`
/--
error: `rollback` requires a `predict` clause on the same `await`
-/
#guard_msgs in
component BadRollbackWithoutPredict:
  session user
  state remaining : Nat = 10
  action buy:
    if user.isSome:
      let rem = await StoreSrv.placeOrder(1)
        rollback: remaining = 0
        catch:
          case .outOfStock: pass
          case .failed(_): pass
      remaining = rem
  view: <span>{remaining}</span>

-- 1f. Rejects `predict` on a non-`await` `let`
/--
error: `predict`, `on_confirm`, `rollback`, and `catch` can only be used on an `await` server RPC call
-/
#guard_msgs in
component BadPredictOnNonAwait:
  state count : Nat = 0
  action bump:
    let n = count + 1 predict 2
    count = n
  view: <span>{count}</span>

-- 1g. Rejects `predict` on a non-`await` assignment
/--
error: `predict` can only be used on an `await` server RPC call
-/
#guard_msgs in
component BadPredictOnAssign:
  state count : Nat = 0
  action bump:
    count = 1 predict 2
  view: <span>{count}</span>

-- 1h. Rejects state mutation inside `predict:` block
/--
error: `predict:` computes a predicted server response and cannot mutate state or perform side effects
-/
#guard_msgs in
component BadMutateInPredict:
  session user
  state remaining : Nat = 10
  action buy:
    if user.isSome:
      let rem = await StoreSrv.placeOrder(1)
        predict:
          remaining = 0
          return 0
        catch:
          case .outOfStock: pass
          case .failed(_): pass
      remaining = rem
  view: <span>{remaining}</span>

-- 1i. Rejects `predict` inside a `server` function
/--
error: `predict`, `on_confirm`, and `rollback` are only supported on client `component` `await` calls, not in `server` functions
-/
#guard_msgs in
server BadServerPredict:
  def f() -> Nat:
    let x = 1 predict 1
    return x

-- 1j. Rejects unhandled domain errors on a `predict`ed `await`
/--
error: `await StoreSrv.placeOrder(...)` has unhandled domain error(s): .outOfStock; handle them with `catch: case .outOfStock: ...`
-/
#guard_msgs in
component BadPredictUnhandledDomainErr:
  session user
  state remaining : Nat = 10
  invariant validRemaining: remaining <= 10000
  action buy:
    if user.isSome and 1 <= remaining:
      let rem = await StoreSrv.placeOrder(1) predict remaining - 1
      remaining = rem
  view: <span>{remaining}</span>

-- 1k. Rejects component invariant violation inside `rollback` branch
-- Run in `withoutModifyingEnv` so the expected failed proof is not persisted in `.olean`.
local elab "rollback_env " cmd:command : command =>
  Lean.withoutModifyingEnv (Lean.Elab.Command.elabCommand cmd)

/--
error: Invariant `BadRollbackInv.bounded` failed in `BadRollbackInv.update`:
  • `rollback` branch must satisfy:  20000 <= 10000

Hint: Guard the failing branch with `if ...:`, fix the update, or weaken the invariant.
      If the rule does hold, add `using [lemma]` or a manual `:= by` proof.
-/
#guard_msgs in
rollback_env
component BadRollbackInv:
  state val : Nat = 0
  invariant bounded: val <= 10000
  action go:
    let r = await StoreSrv.claim(1)
      predict 1
      rollback:
        val = 20000
      catch:
        case .locked: pass
        case .failed(_): pass
    val = r
  view: <span>{val}</span>

/-! ## 2. Positive Runtime & Proof Tests -/

-- 2a. Inline `predict`, `on_confirm:`, `catch:`, concurrent local edits, out-of-order resolution
component CheckoutSpec:
  session user
  state remaining      : Nat    = 10
  state status         : String = ""
  state note           : String = ""
  state confirmedCount : Nat    = 0
  state clicks         : Nat    = 0

  invariant validRemaining: remaining <= 10000

  action setNote(s: String):
    note = s

  action buy(qty: Nat):
    if not (user.isSome and 1 <= qty <= 10 and qty <= remaining): return
    clicks += 1
    let rem = await StoreSrv.placeOrder(qty)
      predict remaining - qty
      on_confirm:
        confirmedCount += 1
        status = f"Confirmed: {rem}"
      catch:
        case .outOfStock:  status = "Out of stock"
        case .failed(err): status = err
    remaining = rem
    status = f"Pending: {rem}"

  view:
    <div>
      <span class="rem">{remaining}</span>
      <span class="status">{status}</span>
      <span class="note">{note}</span>
      <span class="confirmed">{confirmedCount}</span>
      <span class="clicks">{clicks}</span>
    </div>

-- Verify generated invariant + SpecEngine theorems compose cleanly
theorem checkoutSpec_spec_inv :
    ∀ st msg, Qed.SpecEngine.SpecInv (fun s : CheckoutSpec.State => s.remaining ≤ 10000) st →
      Qed.SpecEngine.SpecInv (fun s : CheckoutSpec.State => s.remaining ≤ 10000)
        (CheckoutSpec.app.update st msg).1 := by
  intro st msg h
  exact Qed.SpecEngine.step_preserves_inv CheckoutSpec.update CheckoutSpec._specClassify
    (fun s m hs => CheckoutSpec.validRemaining.2 s m hs) st msg h

-- Generic trace combinators to drive speculative component `app.update`
private def step {S M C : Type} (upd : S → M → S × C) (st : S) (m : M) : S := (upd st m).1
private def runTrace {S M C : Type} (upd : S → M → S × C) (st : S) (ms : List M) : S :=
  ms.foldl (step upd) st

private def mkOrderOk (qty v : Nat) (h : v ≤ 10000) : StoreSrv.placeOrder_Outcome qty :=
  .ok ⟨v, h⟩

-- Tests 1-5: Dispatch + hit, mismatch, error rollback with concurrent local edit, out-of-order resolution, rehydration
#guard
  let u := CheckoutSpec.app.update
  let cs0 := step u CheckoutSpec.app.init.1 (._onSession (some "alice"))
  -- 1. Dispatch + Prediction Hit (`actual == predicted`)
  let sDisp := step u cs0 (.buy 2)
  let sHit := step u sDisp (._specRes_0 0 2 8 (mkOrderOk 2 8 (by omega)))
  -- 2. Prediction Mismatch (rollback + re-apply continuation with `actual` + `on_confirm`)
  let sMisDisp := step u sHit (.buy 1)
  let sMis := step u sMisDisp (._specRes_0 1 1 7 (mkOrderOk 1 5 (by omega)))
  -- 3. Server Error Rollback WITH Concurrent Local Edit (`note` preserved, `clicks` committed, `remaining` rolled back)
  let sErrTyped := runTrace u sMis [.buy 3, .setNote "keep me"]
  let sAfterErr := step u sErrTyped (._specRes_0 2 3 2 (.err .outOfStock "outOfStock"))
  -- 4. Two Overlapping Predictions Resolving Out-Of-Order (`txId = 4` before `txId = 3`)
  let sTwo2 := runTrace u sAfterErr [.buy 1, .buy 1]
  let sTwoRes2 := step u sTwo2 (._specRes_0 4 1 3 (mkOrderOk 1 2 (by omega)))
  let sTwoRes1 := step u sTwoRes2 (._specRes_0 3 1 4 (.err .outOfStock "outOfStock"))
  -- Test 1 assertions
  sDisp.visible.remaining == 8 && sDisp.visible.status == "Pending: 8" && sDisp.visible.clicks == 1 &&
  sDisp.confirmed.remaining == 10 && sDisp.confirmed.clicks == 1 && sDisp.log.length == 1 &&
  sHit.visible.remaining == 8 && sHit.confirmed.remaining == 8 && sHit.visible.confirmedCount == 1 &&
  sHit.visible.status == "Confirmed: 8" && sHit.log.isEmpty &&
  -- Test 2 assertions
  sMisDisp.visible.remaining == 7 && sMisDisp.visible.status == "Pending: 7" &&
  sMis.visible.remaining == 5 && sMis.confirmed.remaining == 5 && sMis.visible.confirmedCount == 2 &&
  sMis.visible.status == "Confirmed: 5" && sMis.log.isEmpty &&
  -- Test 3 assertions
  sErrTyped.visible.remaining == 2 && sErrTyped.visible.note == "keep me" && sErrTyped.log.length == 2 &&
  sAfterErr.visible.remaining == 5 && sAfterErr.confirmed.remaining == 5 && sAfterErr.visible.status == "Out of stock" &&
  sAfterErr.visible.note == "keep me" && sAfterErr.visible.clicks == 3 && sAfterErr.visible.confirmedCount == 2 &&
  sAfterErr.log.isEmpty &&
  -- Test 4 assertions
  sTwo2.visible.remaining == 3 && sTwo2.confirmed.remaining == 5 && sTwo2.log.length == 3 &&
  sTwoRes2.visible.remaining == 2 && sTwoRes2.confirmed.remaining == 5 && sTwoRes2.log.length == 4 &&
  sTwoRes1.visible.remaining == 2 && sTwoRes1.confirmed.remaining == 2 && sTwoRes1.visible.confirmedCount == 3 &&
  sTwoRes1.log.isEmpty &&
  -- Test 5: Rehydration guard rejects invalid state & preserves valid state
  (CheckoutSpec.app.rehydrate (CheckoutSpec.app.dehydrate sHit)).isSome &&
  (CheckoutSpec.app.rehydrate "{\"user\":null,\"remaining\":99999,\"status\":\"\",\"note\":\"\",\"confirmedCount\":0,\"clicks\":0}").isNone

-- 2b. Explicit `rollback(actual):` override (aborts continuation & `on_confirm` on mismatch)
component ClaimSpec:
  state owned     : Nat[]  = []
  state status    : String = ""
  state confirmed : Nat    = 0

  action claimItem(id: Nat):
    let res = await StoreSrv.claim(id)
      predict 1
      on_confirm:
        confirmed += 1
      rollback(actual):
        status = f"Mismatch:{actual}"
      catch:
        case .locked:      status = "Locked"
        case .failed(err): status = err
    owned.push(id)
    status = "Claimed"

  view: <span>{status}</span>

#guard
  let u := ClaimSpec.app.update
  let cl1 := step u ClaimSpec.app.init.1 (.claimItem 42)
  let clMiss := step u cl1 (._specRes_0 0 42 1 (.ok ⟨2, by simp [StoreSrv.claim_ens]⟩))
  let clHit := runTrace u clMiss [.claimItem 7, ._specRes_0 1 7 1 (.ok ⟨1, by simp [StoreSrv.claim_ens]⟩)]
  cl1.visible.owned == #[42] && cl1.visible.status == "Claimed" &&
  clMiss.visible.owned == #[] && clMiss.confirmed.owned == #[] && clMiss.visible.confirmed == 0 &&
  clMiss.visible.status == "Mismatch:2" && clMiss.log.isEmpty &&
  clHit.visible.owned == #[7] && clHit.visible.confirmed == 1 && clHit.visible.status == "Claimed" &&
  clHit.log.isEmpty

-- 2c. Conditional `predict:` block with Schema `Field` refinements, server `ensures`, and client `invariant`
component CatalogSpec:
  session user
  state books       : Resource SpecBook[]
  state lastSlot    : Nat?
  state lastOrdered : SpecBook?
  state statusMsg   : String = ""

  invariant orderedMatchesSlot:
    all b, idx: (lastOrdered == some(b) and lastSlot == some(idx)) -> b.slot == idx

  action loadDemo(bs: SpecBook[]):
    books = .ok(bs)

  action orderOne(idx: Nat):
    if user.isSome:
      let updated = await CatalogSrv.order(idx, 1)
        predict:
          if let .ok(arr) = books:
            if idx < arr.size and arr[idx].slot == idx and arr[idx].stock >= 1:
              let b = arr[idx]
              return SpecBook(slot=b.slot, title=b.title, stock=b.stock - 1)
        catch:
          case .outOfStock:  statusMsg = "Out of stock"
          case .notFound:    statusMsg = "Not found"
          case .failed(err): statusMsg = err
      books = books.map(arr => arr.set(idx, updated) if idx < arr.size else arr)
      lastSlot = some(idx)
      lastOrdered = some(updated)
      statusMsg = f"Ordered {updated.title}"

  view: <span>{statusMsg}</span>

private def mkSpecBook (slot : Nat) (hSlot : slot ≤ 1000) (stock : Nat) (hStock : stock ≤ 10000) : SpecBook :=
  { slot := ⟨slot, by simp [Codec.refine, Codec.nat]; exact hSlot⟩
    title := ⟨"Lean 4", by simp [Codec.refine, Codec.text]; decide⟩
    stock := ⟨stock, by simp [Codec.refine, Codec.nat]; exact hStock⟩ }

#guard
  let u := CatalogSpec.app.update
  let catAuth := step u CatalogSpec.app.init.1 (._onSession (some "alice"))
  let catUnpred := step u catAuth (.orderOne 0)
  let sampleBook := mkSpecBook 0 (by omega) 10 (by omega)
  let actualBook := mkSpecBook 0 (by omega) 6 (by omega)
  let predBook := mkSpecBook 0 (by omega) 9 (by omega)
  let catPred := runTrace u catAuth [.loadDemo #[sampleBook], .orderOne 0]
  let catReconciled := step u catPred
    (._specRes_0 0 0 predBook (.ok ⟨actualBook, by simp [CatalogSrv.order_ens, actualBook, mkSpecBook]; decide⟩))
  catUnpred.log.isEmpty && catUnpred.visible.lastOrdered.isNone &&
  catPred.log.length == 1 && (catPred.visible.lastOrdered.map (·.stock.val)) == some 9 &&
  catPred.visible.statusMsg == "Ordered Lean 4" &&
  catReconciled.log.isEmpty && (catReconciled.visible.lastOrdered.map (·.stock.val)) == some 6

-- 2d. `Resource` assignment shorthand `field = await ... predict ...`
component ResourceSpec:
  state items : Resource Nat[]
  action refresh:
    items = await StoreSrv.fetchItems() predict [1, 2, 3]
  view:
    <Await of={items} as={xs} err={e} loading={<span>loading</span>} failed={<span>{e}</span>}>
      <span>{xs.size}</span>
    </Await>

#guard
  let u := ResourceSpec.app.update
  let rs1 := step u ResourceSpec.app.init.1 .refresh
  let rs2 := step u rs1 (._specRes_0 0 #[1, 2, 3] (.ok #[10, 20]))
  let rs4 := runTrace u rs2 [.refresh, ._specRes_0 1 #[1, 2, 3] (.failed "boom")]
  rs1.log.length == 1 && rs1.visible.items.get? == some #[1, 2, 3] &&
  rs2.log.isEmpty && rs2.visible.items.get? == some #[10, 20] &&
  rs4.log.isEmpty && (match rs4.visible.items with | .failed "boom" => true | _ => false)

/-! ## 3. Kernel-Enforced Soundness Checks (`SpecEq`, `specClassify_pure`, `_specPredict_ens_*`, `specApp_*`) -/

-- 3a. Auto-generated `LawfulBEq` & lawful `SpecEq` for `schema` types and `Date`
example : LawfulBEq SpecBook := inferInstance
example : LawfulBEq Date := inferInstance
example : SpecEq SpecBook := inferInstance
example : SpecEq Date := inferInstance

-- 3b. Unlawful `BEq` (without `LawfulBEq` or `DecidableEq`) is rejected by `SpecEq`
private structure UnlawfulEq where
  n : Nat

private instance : BEq UnlawfulEq := ⟨fun _ _ => true⟩

/--
error: failed to synthesize instance of type class
  SpecEq UnlawfulEq

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : SpecEq UnlawfulEq := inferInstance

-- 3c. Kernel-checked purity of speculative continuations (`specClassify_pure`)
example := @CheckoutSpec.specClassify_pure
example := @ClaimSpec.specClassify_pure
example := @CatalogSpec.specClassify_pure
example := @ResourceSpec.specClassify_pure

-- 3d. Kernel-checked prediction `ensures` theorems (`_specPredict_ens_*`)
example := @CheckoutSpec._specPredict_ens_0
example := @ClaimSpec._specPredict_ens_0
example := @CatalogSpec._specPredict_ens_0

-- 3e. Kernel-checked `App`-level speculative invariant, coherence, and well-formed ID proofs
example := @CheckoutSpec.specApp_init_inv
example := @CheckoutSpec.specApp_preserves_inv
example := @CheckoutSpec.specApp_init_coherent
example := @CheckoutSpec.specApp_preserves_coherent
example := @CheckoutSpec.specApp_init_wellFormedIds
example := @CheckoutSpec.specApp_preserves_wellFormedIds
example := @CatalogSpec.specApp_init_inv
example := @CatalogSpec.specApp_preserves_inv

fullstack SpecMain:
  server StoreSrv
  client CheckoutSpec
  title "Speculative Check"

end SpeculativeChecks
