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
  invariant stock <= 10000

  def placeOrder(qty: Nat) -> Nat!:
    requires ctx.userId != none
    requires 1 <= qty <= 10
    ensures result <= 10000
    ensure stock >= qty else fail(.outOfStock)
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
    ensure idx < books.size and books[idx].slot == idx else fail(.notFound)
    ensure books[idx].stock >= qty else fail(.outOfStock)
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

-- 1b. Rejects `perform` inside speculative continuation after `predict`
/--
error: cannot use `perform` inside a speculative continuation after `predict` (side effects cannot be rolled back); move it into `on_confirm:`
-/
#guard_msgs in
component BadSpecPerform:
  session user
  port log : String
  state remaining : Nat = 10
  invariant remaining <= 10000
  action buy:
    if user.isSome and 1 <= remaining:
      let rem = await StoreSrv.placeOrder(1) predict remaining - 1 catch:
        case .outOfStock: pass
        case .failed(_): pass
      remaining = rem
      perform log("bought")
  view: <span>{remaining}</span>

-- 1c. Rejects nested `await` inside speculative continuation after `predict`
/--
error: cannot `await` inside a speculative continuation after `predict`; move sequential `await` calls into `on_confirm:`
-/
#guard_msgs in
component BadSpecNestedAwait:
  session user
  state remaining : Nat = 10
  invariant remaining <= 10000
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
  invariant remaining <= 10000
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
    ensure user.isSome and 1 <= qty <= 10 and qty <= remaining else return
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

-- Helper to drive `CheckoutSpec.app.update`
private def csInit : Qed.SpecState CheckoutSpec.State CheckoutSpec.Msg :=
  (CheckoutSpec.app.update CheckoutSpec.app.init.1 (._onSession (some "alice"))).1

private def mkOrderOk (qty v : Nat) (h : v ≤ 10000) : StoreSrv.placeOrder_Outcome qty :=
  .ok ⟨v, h⟩

-- Test 1: Dispatch + Prediction Hit (`actual == predicted`)
private def csAfterDispatch := (CheckoutSpec.app.update csInit (.buy 2)).1
#guard csAfterDispatch.visible.remaining == 8
#guard csAfterDispatch.visible.status == "Pending: 8"
#guard csAfterDispatch.visible.clicks == 1
#guard csAfterDispatch.confirmed.remaining == 10
#guard csAfterDispatch.confirmed.clicks == 1
#guard csAfterDispatch.log.length == 1

private def csAfterHit :=
  (CheckoutSpec.app.update csAfterDispatch (._specRes_0 0 2 8 (mkOrderOk 2 8 (by omega)))).1
#guard csAfterHit.visible.remaining == 8
#guard csAfterHit.confirmed.remaining == 8
#guard csAfterHit.visible.confirmedCount == 1
#guard csAfterHit.visible.status == "Confirmed: 8"
#guard csAfterHit.log.isEmpty

-- Test 2: Prediction Mismatch (default: rollback + re-apply continuation with `actual` + `on_confirm`)
private def csMismatchDisp := (CheckoutSpec.app.update csAfterHit (.buy 1)).1
#guard csMismatchDisp.visible.remaining == 7
#guard csMismatchDisp.visible.status == "Pending: 7"
private def csAfterMismatch :=
  (CheckoutSpec.app.update csMismatchDisp (._specRes_0 1 1 7 (mkOrderOk 1 5 (by omega)))).1
#guard csAfterMismatch.visible.remaining == 5
#guard csAfterMismatch.confirmed.remaining == 5
#guard csAfterMismatch.visible.confirmedCount == 2
#guard csAfterMismatch.visible.status == "Confirmed: 5"
#guard csAfterMismatch.log.isEmpty

-- Test 3: Server Error Rollback WITH Concurrent Local Edit (`note` preserved, `clicks` committed, `remaining` rolled back!)
private def csErrDisp := (CheckoutSpec.app.update csAfterMismatch (.buy 3)).1
private def csErrTyped := (CheckoutSpec.app.update csErrDisp (.setNote "keep me")).1
#guard csErrTyped.visible.remaining == 2
#guard csErrTyped.visible.note == "keep me"
#guard csErrTyped.log.length == 2
private def csAfterErr :=
  (CheckoutSpec.app.update csErrTyped (._specRes_0 2 3 2 (.err .outOfStock "outOfStock"))).1
#guard csAfterErr.visible.remaining == 5
#guard csAfterErr.confirmed.remaining == 5
#guard csAfterErr.visible.status == "Out of stock"
#guard csAfterErr.visible.note == "keep me"
#guard csAfterErr.visible.clicks == 3
#guard csAfterErr.visible.confirmedCount == 2
#guard csAfterErr.log.isEmpty

-- Test 4: Two Overlapping Predictions Resolving Out-Of-Order (`txId = 4` before `txId = 3`)
private def csTwo1 := (CheckoutSpec.app.update csAfterErr (.buy 1)).1     -- txId 3, predicts 4
private def csTwo2 := (CheckoutSpec.app.update csTwo1 (.buy 1)).1         -- txId 4, predicts 3
#guard csTwo2.visible.remaining == 3
#guard csTwo2.confirmed.remaining == 5
#guard csTwo2.log.length == 3           -- pending 3, resolved pre(buy2), pending 4
-- Second RPC (`txId = 4`) returns FIRST with mismatch `actual = 2`
private def csTwoRes2 :=
  (CheckoutSpec.app.update csTwo2 (._specRes_0 4 1 3 (mkOrderOk 1 2 (by omega)))).1
#guard csTwoRes2.visible.remaining == 2
#guard csTwoRes2.confirmed.remaining == 5  -- txId 3 still pending!
#guard csTwoRes2.log.length == 4           -- pending 3, resolved pre(buy2), resolved cont 4, resolved confirm 4
-- First RPC (`txId = 3`) now fails with `.outOfStock`
private def csTwoRes1 :=
  (CheckoutSpec.app.update csTwoRes2 (._specRes_0 3 1 4 (.err .outOfStock "outOfStock"))).1
#guard csTwoRes1.visible.remaining == 2
#guard csTwoRes1.confirmed.remaining == 2
#guard csTwoRes1.visible.confirmedCount == 3
#guard csTwoRes1.log.isEmpty

-- Test 5: Rehydration guard rejects invalid state & preserves valid state
#guard (CheckoutSpec.app.rehydrate (CheckoutSpec.app.dehydrate csAfterHit)).isSome
#guard (CheckoutSpec.app.rehydrate "{\"user\":null,\"remaining\":99999,\"status\":\"\",\"note\":\"\",\"confirmedCount\":0,\"clicks\":0}").isNone

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

private def cl0 := ClaimSpec.app.init.1
private def cl1 := (ClaimSpec.app.update cl0 (.claimItem 42)).1
#guard cl1.visible.owned == #[42]
#guard cl1.visible.status == "Claimed"
-- Mismatch (`actual = 2`): reverts `owned` to `[]`, skips `on_confirm`, runs `rollback(actual):`
private def clMiss := (ClaimSpec.app.update cl1 (._specRes_0 0 42 1 (.ok ⟨2, by simp [StoreSrv.claim_ens]⟩))).1
#guard clMiss.visible.owned == #[]
#guard clMiss.confirmed.owned == #[]
#guard clMiss.visible.confirmed == 0
#guard clMiss.visible.status == "Mismatch:2"
#guard clMiss.log.isEmpty
-- Hit (`actual = 1`): commits `owned == #[7]` and runs `on_confirm`
private def clHitDisp := (ClaimSpec.app.update clMiss (.claimItem 7)).1
private def clHit := (ClaimSpec.app.update clHitDisp (._specRes_0 1 7 1 (.ok ⟨1, by simp [StoreSrv.claim_ens]⟩))).1
#guard clHit.visible.owned == #[7]
#guard clHit.visible.confirmed == 1
#guard clHit.visible.status == "Claimed"
#guard clHit.log.isEmpty

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

private def catAuth :=
  (CatalogSpec.app.update CatalogSpec.app.init.1 (._onSession (some "alice"))).1
-- When `books` is `.idle`, `predict:` falls through (`none`) -> unpredicted fallback (`log = []`)
private def catUnpred := (CatalogSpec.app.update catAuth (.orderOne 0)).1
#guard catUnpred.log.isEmpty
#guard catUnpred.visible.lastOrdered.isNone
-- When `books` is loaded, `predict:` succeeds -> immediate speculative update!
private def sampleBook : SpecBook := mkSpecBook 0 (by omega) 10 (by omega)
private def catLoaded := (CatalogSpec.app.update catAuth (.loadDemo #[sampleBook])).1
private def catPred := (CatalogSpec.app.update catLoaded (.orderOne 0)).1
#guard catPred.log.length == 1
#guard (catPred.visible.lastOrdered.map (fun b => b.stock.val)) == some 9
#guard catPred.visible.statusMsg == "Ordered Lean 4"
-- Server returns actual stock = 6 (mismatch): rolls back 9 and reconciles to 6!
private def actualBook : SpecBook := mkSpecBook 0 (by omega) 6 (by omega)
private def predBook : SpecBook := mkSpecBook 0 (by omega) 9 (by omega)
private def catReconciled :=
  (CatalogSpec.app.update catPred
    (._specRes_0 0 0 predBook (.ok ⟨actualBook, by simp [CatalogSrv.order_ens, actualBook, mkSpecBook]; decide⟩))).1
#guard catReconciled.log.isEmpty
#guard (catReconciled.visible.lastOrdered.map (fun b => b.stock.val)) == some 6

-- 2d. `Resource` assignment shorthand `field = await ... predict ...`
component ResourceSpec:
  state items : Resource Nat[]
  action refresh:
    items = await StoreSrv.fetchItems() predict [1, 2, 3]
  view:
    <Await of={items} as={xs} err={e} loading={<span>loading</span>} failed={<span>{e}</span>}>
      <span>{xs.size}</span>
    </Await>

private def rs0 := ResourceSpec.app.init.1
private def rs1 := (ResourceSpec.app.update rs0 .refresh).1
#guard rs1.log.length == 1
#guard rs1.visible.items.get? == some #[1, 2, 3]
-- Mismatch: server returns #[10, 20]
private def rs2 := (ResourceSpec.app.update rs1 (._specRes_0 0 #[1, 2, 3] (.ok #[10, 20]))).1
#guard rs2.log.isEmpty
#guard rs2.visible.items.get? == some #[10, 20]
-- Error: reverts `.ok` to `.failed`
private def rs3 := (ResourceSpec.app.update rs2 .refresh).1
private def rs4 := (ResourceSpec.app.update rs3 (._specRes_0 1 #[1, 2, 3] (.failed "boom"))).1
#guard rs4.log.isEmpty
#guard (match rs4.visible.items with | .failed "boom" => true | _ => false)

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

end SpeculativeChecks
