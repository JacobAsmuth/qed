import Qed
open Qed

namespace SpeculativeApp

server SpecDemoSrv:
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
    return [10, 20, 30]

component SpecDemoClient:
  session user
  state remaining      : Nat    = 10
  state status         : String = "Ready"
  state note           : String = ""
  state confirmedCount : Nat    = 0
  state clicks         : Nat    = 0
  state owned          : Nat[]  = []
  state claimStatus    : String = ""
  state items          : Resource Nat[]

  invariant validRemaining: remaining <= 10000

  action buy(qty: Nat):
    if user.isSome and 1 <= qty <= 10 and qty <= remaining:
      clicks += 1
      let rem = await SpecDemoSrv.placeOrder(qty)
        predict remaining - qty
        on_confirm:
          confirmedCount += 1
          status = f"Confirmed: {rem}"
        catch:
          case .outOfStock:  status = "Out of stock"
          case .failed(err): status = err
      remaining = rem
      status = f"Pending: {rem}"

  action claimItem(id: Nat):
    let _ = await SpecDemoSrv.claim(id)
      predict 1
      on_confirm:
        confirmedCount += 1
      rollback(actual):
        claimStatus = f"Mismatch:{actual}"
      catch:
        case .locked:      claimStatus = "Locked"
        case .failed(err): claimStatus = err
    owned.push(id)
    claimStatus = "Claimed"

  action refreshItems:
    items = await SpecDemoSrv.fetchItems() predict [1, 2, 3]

  view:
    <div class="spec-demo">
      <span class="rem">{remaining}</span>
      <span class="status">{status}</span>
      <span class="confirmed">{confirmedCount}</span>
      <span class="clicks">{clicks}</span>
      <span class="owned-count">{owned.size}</span>
      <span class="claim-status">{claimStatus}</span>
      <input class="note-input" bind={note} />
      <span class="note-mirror">{note}</span>
      <button class="buy-2" onClick={.buy(2)}>Buy 2</button>
      <button class="buy-1" onClick={.buy(1)}>Buy 1</button>
      <button class="buy-4" onClick={.buy(4)}>Buy 4</button>
      <button class="claim-ok" onClick={.claimItem(7)}>Claim 7</button>
      <button class="claim-miss" onClick={.claimItem(99)}>Claim 99</button>
      <button class="refresh-items" onClick={.refreshItems}>Refresh</button>
      <Await of={items} as={xs} err={e}
        loading={<span class="items-val">loading</span>}
        failed={<span class="items-val">{e}</span>}>
        <span class="items-val">{xs.size}</span>
      </Await>
    </div>

fullstack Main:
  server SpecDemoSrv
  client SpecDemoClient
  title "Speculative Demo"

end SpeculativeApp
