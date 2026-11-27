import Qed
import QedTests.CheckHelper
open Qed

namespace SpeculativeChecks
schema SpecBook:
  slot  : Nat    where slot <= 1000
  title : String where 1 <= title.length <= 64
  stock : Nat    where stock <= 10000
server StoreSrv:
  state stock : Nat = 10
  invariant maxStock: stock <= 10000
  rpc placeOrder(qty: Nat) -> Nat!:
    requires ctx.userId != none, 1 <= qty <= 10
    ensures result <= 10000
    if stock < qty: return fail(.outOfStock)
    stock -= qty
    return stock
  rpc claim(id: Nat) -> Nat!:
    ensures result <= 100
    if id == 0: return fail(.locked)
    if id == 99: return 2
    return 1
  rpc fetchItems() -> Nat[]: return [10, 20]
server CatalogSrv:
  state books : SpecBook[] = [SpecBook(slot=0, title="Lean 4", stock=10), SpecBook(slot=1, title="Qed", stock=5)]
  rpc order(idx: Nat, qty: Nat) -> SpecBook!:
    requires ctx.userId != none, 1 <= qty <= 10
    ensures result.slot == idx, result.stock < 10000
    if idx >= books.size: return fail(.notFound)
    if books[idx].slot != idx: return fail(.notFound)
    if books[idx].stock < qty: return fail(.outOfStock)
    books[idx].stock -= qty
    return books[idx]

/-! ## 1. Compile-Time Negative Tests -/
bad_spec_act "Predicted response for `StoreSrv.placeOrder` does not satisfy server `ensures` postcondition:\n  • must satisfy:  20000 <= 10000" BadPredictEnsures :
  if user.isSome:
    let rem = await StoreSrv.placeOrder(1) predict 20000 catch:
      case _: pass
    remaining = rem
expect_err "cannot run side effects or emit events inside a speculative continuation after `predict`" in
component BadSpecPerform:
  session user
  port log : String
  state remaining : Nat = 10
  invariant validRemaining: remaining <= 10000
  action buy:
    if user.isSome and 1 <= remaining:
      let rem = await StoreSrv.placeOrder(1) predict remaining - 1 catch:
        case _: pass
      remaining = rem
      log.send("bought")
  view: <span>{remaining}</span>
bad_spec_act "cannot `await` inside a speculative continuation after `predict`" BadSpecNestedAwait :
  if user.isSome and 1 <= remaining:
    let rem = await StoreSrv.placeOrder(1) predict remaining - 1 catch:
      case _: pass
    remaining = rem
    let _ = await StoreSrv.claim(1) catch:
      case _: pass
bad_spec_act "`on_confirm` requires a `predict` clause on the same `await`" BadOnConfirmWithoutPredict :
  if user.isSome:
    let rem = await StoreSrv.placeOrder(1)
      on_confirm: remaining = rem
      catch:
        case _: pass
    remaining = rem
bad_spec_act "`rollback` requires a `predict` clause on the same `await`" BadRollbackWithoutPredict :
  if user.isSome:
    let rem = await StoreSrv.placeOrder(1)
      rollback: remaining = 0
      catch:
        case _: pass
    remaining = rem
bad_comp_act "`predict`, `on_confirm`, `rollback`, and `catch` can only be used on an `await` server RPC call" BadPredictOnNonAwait count : Nat = 0 | bump : let n = count + 1 predict 2; count = n
bad_comp_act "`predict` can only be used on an `await` server RPC call" BadPredictOnAssign count : Nat = 0 | bump : count = 1 predict 2
bad_spec_act "`predict:` computes a predicted server response and cannot mutate state or perform side effects" BadMutateInPredict :
  if user.isSome:
    let rem = await StoreSrv.placeOrder(1)
      predict: remaining = 0; return 0
      catch:
        case _: pass
    remaining = rem
bad_srv "`predict`, `on_confirm`, and `rollback` are only supported on client `component` `await` calls, not in `server` functions" BadServerPredict : rpc f() -> Nat: let x = 1 predict 1; return x
bad_spec_act "`await StoreSrv.placeOrder(...)` has unhandled domain error(s): .outOfStock" BadPredictUnhandledDomainErr :
  if user.isSome and 1 <= remaining: let rem = await StoreSrv.placeOrder(1) predict remaining - 1; remaining = rem
bad_comp_inv "Invariant `BadRollbackInv.bounded` failed in `BadRollbackInv.update`:\n  • `rollback` branch must satisfy:  20000 <= 10000" BadRollbackInv val : Nat = 0 | bounded : val <= 10000 | go :
  let r = await StoreSrv.claim(1) predict 1
    rollback: val = 20000
    catch:
      case _: pass
  | val = r

/-! ## 2. Positive Runtime & Proof Tests -/
component CheckoutSpec:
  session user
  state remaining      : Nat    = 10
  state status         : String = ""
  state note           : String = ""
  state confirmedCount : Nat    = 0
  state clicks         : Nat    = 0
  invariant validRemaining: remaining <= 10000
  action setNote(s: String): note = s
  action buy(qty: Nat):
    if not (user.isSome and 1 <= qty <= 10 and qty <= remaining): return
    clicks += 1
    let rem = await StoreSrv.placeOrder(qty) predict remaining - qty
      on_confirm: confirmedCount += 1; status = f"Confirmed: {rem}"
      catch:
        case .outOfStock: status = "Out of stock"
        case .failed(err): status = err
    remaining = rem
    status = f"Pending: {rem}"
  view: <div><span class="rem">{remaining}</span><span class="status">{status}</span><span class="note">{note}</span><span class="confirmed">{confirmedCount}</span><span class="clicks">{clicks}</span></div>
theorem checkoutSpec_spec_inv :
    ∀ st msg, Qed.SpecEngine.SpecInv (fun s : CheckoutSpec.State => s.remaining ≤ 10000) st →
      Qed.SpecEngine.SpecInv (fun s : CheckoutSpec.State => s.remaining ≤ 10000) (CheckoutSpec.app.update st msg).1 := fun st msg h =>
  Qed.SpecEngine.step_preserves_inv CheckoutSpec.update CheckoutSpec._specClassify (fun s m hs => CheckoutSpec.validRemaining.2 s m hs) st msg h
component ClaimSpec:
  state owned     : Nat[]  = []
  state status    : String = ""
  state confirmed : Nat    = 0
  action claimItem(id: Nat):
    let res = await StoreSrv.claim(id) predict 1
      on_confirm: confirmed += 1
      rollback(actual): status = f"Mismatch:{actual}"
      catch:
        case .locked: status = "Locked"
        case .failed(err): status = err
    owned.push(id)
    status = "Claimed"
  view: <span>{status}</span>
component CatalogSpec:
  session user
  state books       : Resource SpecBook[]
  state lastSlot    : Nat?
  state lastOrdered : SpecBook?
  state statusMsg   : String = ""
  invariant orderedMatchesSlot: all b, idx: (lastOrdered == some(b) and lastSlot == some(idx)) -> b.slot == idx
  action loadDemo(bs: SpecBook[]): books = .ok(bs)
  action orderOne(idx: Nat):
    if user.isSome:
      let updated = await CatalogSrv.order(idx, 1)
        predict:
          if let .ok(arr) = books:
            if idx < arr.size and arr[idx].slot == idx and arr[idx].stock >= 1: let b = arr[idx]; return SpecBook(slot=b.slot, title=b.title, stock=b.stock - 1)
        catch:
          case .outOfStock: statusMsg = "Out of stock"
          case .notFound: statusMsg = "Not found"
          case .failed(err): statusMsg = err
      books = books.map(arr => arr.set(idx, updated) if idx < arr.size else arr)
      lastSlot = some(idx)
      lastOrdered = some(updated)
      statusMsg = f"Ordered {updated.title}"
  view: <span>{statusMsg}</span>
component ResourceSpec:
  state items : Resource Nat[]
  action refresh: items = await StoreSrv.fetchItems() predict [1, 2, 3]
  view: <Await of={items} as={xs} err={e} loading={<span>loading</span>} failed={<span>{e}</span>}><span>{xs.size}</span></Await>
private def step {S M C : Type} (upd : S → M → S × C) (st : S) (m : M) : S := (upd st m).1
private def runTrace {S M C : Type} (upd : S → M → S × C) (st : S) (ms : List M) : S := ms.foldl (step upd) st
private def mkOrderOk (qty v : Nat) (h : v ≤ 10000) : StoreSrv.placeOrder_Outcome qty := .ok ⟨v, h⟩
private def mkSpecBook (slot : Nat) (hSlot : slot ≤ 1000) (stock : Nat) (hStock : stock ≤ 10000) : SpecBook :=
  { slot := ⟨slot, by simp [Codec.refine, Codec.nat]; exact hSlot⟩, title := ⟨"Lean 4", by simp [Codec.refine, Codec.text]; decide⟩, stock := ⟨stock, by simp [Codec.refine, Codec.nat]; exact hStock⟩ }
example : (
  let u := CheckoutSpec.app.update
  let snap (s : Qed.SpecState CheckoutSpec.State CheckoutSpec.Msg) := (s.visible.remaining, s.confirmed.remaining, s.visible.status, s.visible.note, s.visible.confirmedCount, s.visible.clicks, s.confirmed.clicks, s.log.length)
  let sDisp := runTrace u CheckoutSpec.app.init.1 [._onSession (some "alice"), .buy 2]
  let sHit := step u sDisp (._specRes_0 0 2 8 (mkOrderOk 2 8 (by omega)))
  let sMisDisp := step u sHit (.buy 1); let sMis := step u sMisDisp (._specRes_0 1 1 7 (mkOrderOk 1 5 (by omega)))
  let sErrTyped := runTrace u sMis [.buy 3, .setNote "keep me"]; let sAfterErr := step u sErrTyped (._specRes_0 2 3 2 (.err .outOfStock "outOfStock"))
  let sTwo2 := runTrace u sAfterErr [.buy 1, .buy 1]; let sTwoRes2 := step u sTwo2 (._specRes_0 4 1 3 (mkOrderOk 1 2 (by omega)))
  let sTwoRes1 := step u sTwoRes2 (._specRes_0 3 1 4 (.err .outOfStock "outOfStock"))
  let uc := ClaimSpec.app.update; let cl1 := step uc ClaimSpec.app.init.1 (.claimItem 42)
  let clMiss := step uc cl1 (._specRes_0 0 42 1 (.ok ⟨2, by simp [StoreSrv.claim_ens]⟩))
  let clHit := runTrace uc clMiss [.claimItem 7, ._specRes_0 1 7 1 (.ok ⟨1, by simp [StoreSrv.claim_ens]⟩)]
  let uk := CatalogSpec.app.update; let catAuth := step uk CatalogSpec.app.init.1 (._onSession (some "alice")); let catUnpred := step uk catAuth (.orderOne 0)
  let sampleBook := mkSpecBook 0 (by omega) 10 (by omega); let actualBook := mkSpecBook 0 (by omega) 6 (by omega); let predBook := mkSpecBook 0 (by omega) 9 (by omega)
  let catPred := runTrace uk catAuth [.loadDemo #[sampleBook], .orderOne 0]
  let catReconciled := step uk catPred (._specRes_0 0 0 predBook (.ok ⟨actualBook, by simp [CatalogSrv.order_ens, actualBook, mkSpecBook]⟩))
  let ur := ResourceSpec.app.update; let rs1 := step ur ResourceSpec.app.init.1 .refresh; let rs2 := step ur rs1 (._specRes_0 0 #[1, 2, 3] (.ok #[10, 20]))
  let rs4 := runTrace ur rs2 [.refresh, ._specRes_0 1 #[1, 2, 3] (.failed "boom")]
  [(sDisp, (8, 10, "Pending: 8", "", 0, 1, 1, 1)), (sHit, (8, 8, "Confirmed: 8", "", 1, 1, 1, 0)), (sMisDisp, (7, 8, "Pending: 7", "", 1, 2, 2, 1)),
   (sMis, (5, 5, "Confirmed: 5", "", 2, 2, 2, 0)), (sErrTyped, (2, 5, "Pending: 2", "keep me", 2, 3, 3, 2)), (sAfterErr, (5, 5, "Out of stock", "keep me", 2, 3, 3, 0))].all (fun (s, w) => snap s == w) &&
  (sTwo2.visible.remaining, sTwo2.confirmed.remaining, sTwo2.log.length) == (3, 5, 3) && (sTwoRes2.visible.remaining, sTwoRes2.confirmed.remaining, sTwoRes2.log.length) == (2, 5, 4) &&
  (sTwoRes1.visible.remaining, sTwoRes1.confirmed.remaining, sTwoRes1.visible.confirmedCount, sTwoRes1.log.length) == (2, 2, 3, 0) &&
  (CheckoutSpec.app.rehydrate (CheckoutSpec.app.dehydrate sHit)).isSome && (CheckoutSpec.app.rehydrate "{\"user\":null,\"remaining\":99999,\"status\":\"\",\"note\":\"\",\"confirmedCount\":0,\"clicks\":0}").isNone &&
  (cl1.visible.owned, cl1.visible.status) == (#[42], "Claimed") && (clMiss.visible.owned, clMiss.confirmed.owned, clMiss.visible.confirmed, clMiss.visible.status, clMiss.log.isEmpty) == (#[], #[], 0, "Mismatch:2", true) &&
  (clHit.visible.owned, clHit.visible.confirmed, clHit.visible.status, clHit.log.isEmpty) == (#[7], 1, "Claimed", true) &&
  catUnpred.log.isEmpty && catUnpred.visible.lastOrdered.isNone && (catPred.log.length, catPred.visible.lastOrdered.map (·.stock.val), catPred.visible.statusMsg) == (1, some 9, "Ordered Lean 4") &&
  (catReconciled.log.isEmpty, catReconciled.visible.lastOrdered.map (·.stock.val)) == (true, some 6) &&
  rs1.log.length == 1 && rs1.visible.items.get? == some #[1, 2, 3] && rs2.log.isEmpty && rs2.visible.items.get? == some #[10, 20] && rs4.log.isEmpty && (match rs4.visible.items with | .failed "boom" => true | _ => false)) = true := by decide +kernel

/-! ## 3. Kernel-Enforced Soundness Checks -/
example : PProd (LawfulBEq SpecBook ∧ LawfulBEq Date) (SpecEq SpecBook × SpecEq Date) := ⟨⟨inferInstance, inferInstance⟩, (inferInstance, inferInstance)⟩
private structure UnlawfulEq where n : Nat
private instance : BEq UnlawfulEq := ⟨fun _ _ => true⟩
expect_err "failed to synthesize instance of type class\n  SpecEq UnlawfulEq" in example : SpecEq UnlawfulEq := inferInstance
check_decls [CheckoutSpec.specClassify_pure, ClaimSpec.specClassify_pure, CatalogSpec.specClassify_pure, ResourceSpec.specClassify_pure,
  CheckoutSpec._specPredict_ens_0, ClaimSpec._specPredict_ens_0, CatalogSpec._specPredict_ens_0,
  CheckoutSpec.specApp_init_inv, CheckoutSpec.specApp_preserves_inv, CheckoutSpec.specApp_init_coherent, CheckoutSpec.specApp_preserves_coherent,
  CheckoutSpec.specApp_init_wellFormedIds, CheckoutSpec.specApp_preserves_wellFormedIds, CatalogSpec.specApp_init_inv, CatalogSpec.specApp_preserves_inv]
fullstack SpecMain:
  server StoreSrv
  client CheckoutSpec
  title "Speculative Check"
end SpeculativeChecks
