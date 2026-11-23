import Qed
import Qed.Server.Http
import Tests.CheckHelper
open Qed

namespace ServerChecks
external PingApi:
  base "https://api.example.com"
  get "/ping" ping() -> String
schema CheckedItem:
  label : String where 1 <= label.length <= 32
  stock : Nat    where stock <= 100
bad_srv_st "cannot access server state `count` outside an `atomic` block in `bump`" BadToctouRead count : Nat = 0 |
  def bump() -> Nat!:
    let c = count
    await PingApi.ping()?
    return c
bad_srv_st "cannot access server state `count` outside an `atomic` block in `bump`" BadOutsideAtomicMut count : Nat = 0 |
  def bump() -> Nat!:
    await PingApi.ping()?
    count += 1
    return 1
bad_srv_st "redundant `atomic` block: `bump` has no `await` calls" BadRedundantAtomic count : Nat = 0 |
  def bump() -> Nat:
    atomic: count += 1
    return count
bad_srv_st "cannot use `await` inside an `atomic` block" BadAwaitInAtomic count : Nat = 0 |
  def bump() -> Nat!:
    await PingApi.ping()?
    atomic:
      await PingApi.ping()?
      count += 1
    return 1
bad_srv1 "unhandled fallible `await` expression" BadUnhandledError :
  def callIt() -> String:
    let res = await PingApi.ping()
    return "ok"
bad_srv_st "Array index `idx` could be out of bounds for `items`:\n  • must satisfy:  idx < items.size" BadArrayBounds items : Nat[] = [10, 20] | def readAt(idx: Nat) -> Nat: return items[idx]
bad_srv1 "Schema field rule `1 <= \"\".length and \"\".length <= 32` failed for `\"\"`." BadFieldRefinement : def makeEmpty() -> CheckedItem: return CheckedItem(label="", stock=5)
bad_srv_inv "Server invariant `maxStock` failed in `overflow`:\n  • must satisfy:  stock + 50 <= 100" BadSingleStateInv stock : Nat = 10 | maxStock : stock <= 100 |
  def overflow() -> Nat:
    stock += 50
    return stock
bad_srv_inv "Server invariant `ordersMonotonic` failed in `resetOrders`:\n  • must satisfy:  0 >= orders" BadTwoStateInv orders : Nat = 5 | ordersMonotonic : orders >= old(orders) |
  def resetOrders() -> Nat:
    orders = 0
    return orders
expect_err "Server invariant `authItems` failed in `unauthenticatedPush`:\n  • must satisfy:  items.push x = items or ctx.userId != none" in
server BadMutatingAuthInv:
  state items: Nat[] = [1]
  invariant authItems: mutating items requires ctx.userId != none
  def unauthenticatedPush(x: Nat) -> Nat:
    items.push(x)
    return items.size
bad_srv1 "Server postcondition `ensures result > 10` failed in `compute`:\n  • must satisfy:  5 > 10" BadServerEnsures :
  def compute(x: Nat) -> Nat:
    ensures result > 10
    return 5
server CheckedSrv:
  def buy(qty: Nat) -> Nat!:
    requires ctx.userId != none, 1 <= qty <= 50
    ensures result == qty, 1 <= result <= 50
    if qty == 49: return fail(.soldOut)
    elif qty == 50: return fail(.limitReached)
    return qty
server OtherSrv:
  def ping() -> Nat: return 1
bad_comp_sess "RPC `CheckedSrv.buy` precondition `1 <= qty <= 50` could not be proved here:\n  • must satisfy:  1 <= 0 and 0 <= 50" BadClientRequiresParam :
  if user.isSome:
    let _ = await CheckedSrv.buy(0) catch:
      case _: pass
expect_err "RPC `CheckedSrv.buy` requires an authenticated session (`ctx.userId != none`), but `BadClientRequiresAuth` has no `session` field." in
component BadClientRequiresAuth:
  action go:
    let _ = await CheckedSrv.buy(1) catch:
      case _: pass
  view: <span>ok</span>
bad_comp_sess "`await CheckedSrv.buy(...)` has unhandled domain error(s): .limitReached" BadClientNonExhaustiveCatch :
  if user.isSome:
    let _ = await CheckedSrv.buy(1) catch:
      case .soldOut:   pass
      case .failed(_): pass
component CallsOther:
  state v : Resource Nat
  action go: v = await OtherSrv.ping()
  view: <span>ok</span>
bad_fs "`fullstack BadFs` mounts `server CheckedSrv`, but client `CallsOther` calls RPC `OtherSrv.ping` on unmounted server `OtherSrv`" BadFs CheckedSrv CallsOther
component InvariantSatisfiesRequires:
  session user
  state qty    : Nat = 5
  state bought : Nat = 0
  invariant qtyInBounds: 1 <= qty <= 50
  invariant boughtValid: bought == 0 or 1 <= bought <= 50
  action setQty(q: Nat): if 1 <= q <= 50: qty = q
  action purchase:
    if not user.isSome: return
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
    requires ctx.userId != none, 1 <= qty <= 50
    ensures result == qty, 1 <= result <= 50
    return qty
expect_err "reactive `query count` cannot call mutating server RPC `QuerySrv.bump`" in
component BadMutatingQuery:
  query count = QuerySrv.bump()
  view: <span>ok</span>
expect_err "RPC `QuerySrv.quote` precondition `1 <= qty <= 50` could not be proved here:\n  • must satisfy:  1 <= 0 and 0 <= 50" in
component BadQueryRequiresParam:
  session user
  query q = QuerySrv.quote(0) if user.isSome
  view: <span>ok</span>
expect_err "RPC `QuerySrv.quote` requires an authenticated session (`user != none`)" in
component BadQueryRequiresAuth:
  session user
  query q = QuerySrv.quote(5)
  view: <span>ok</span>
component VerifiedQueryFlow:
  session user
  state qty : Nat = 5
  invariant qtyInBounds: 1 <= qty <= 50
  query quote = QuerySrv.quote(qty) if user.isSome
  invariant quoteValid: quote.all(v => 1 <= v <= 50)
  query echoed = QuerySrv.quote(v) if let .ok(v) = quote.state, user.isSome
  invariant echoedValid: echoed.all(v => 1 <= v <= 50)
  action setQty(q: Nat): if 1 <= q <= 50: qty = q
  view: <div><Await of={quote} as={v}><span>{f"{v}"}</span></Await><Await of={echoed} as={e}><span>{f"{e}"}</span></Await></div>
expect_err "`external BadAuthWs` declares client-usable `ws` channels and cannot attach server `auth` secrets" in
external BadAuthWs:
  base "wss://ws.example.com"
  auth bearer(secret("WS_SECRET"))
  ws "/stream" feed() -> String
expect_err "Channel `ensures` postcondition failed at `emit`:\n  • must satisfy:  99 <= 50" in
server BadEmitSrv:
  channel bounded() -> Nat:
    ensures event <= 50
    on_join: pass
  def pushBad() -> Unit:
    bounded.emit(99)
    return ()
server WsCheckSrv:
  channel gauge(room: Nat) -> Nat:
    requires ctx.userId != none, room <= 10
    ensures event <= 50
    on_join: pass
    on_send(v: Nat):
      requires v <= 50
      gauge.emit(room, v)
    on_leave: pass
expect_err "RPC `WsCheckSrv.gauge` requires an authenticated session (`user != none`)" in
component BadSubNoAuth:
  session user
  subscribe g = WsCheckSrv.gauge(1):
    on_message(_): pass
  view: <span>ok</span>
expect_err "RPC `WsCheckSrv.gauge` precondition `room <= 10` could not be proved here:\n  • must satisfy:  99 <= 10" in
component BadSubBadParam:
  session user
  subscribe g = WsCheckSrv.gauge(99) if user.isSome:
    on_message(_): pass
  view: <span>ok</span>
expect_err "RPC `WsCheckSrv.gauge.send` precondition `v <= 50` could not be proved here:\n  • must satisfy:  77 <= 50" in
component BadSendParam:
  session user
  subscribe g = WsCheckSrv.gauge(1) if user.isSome:
    on_message(_): pass
  action go: g.send(77)
  view: <span>ok</span>
component SubOtherWs:
  session user
  subscribe g = WsCheckSrv.gauge(1) if user.isSome:
    on_message(_): pass
  view: <span>ok</span>
bad_fs "`fullstack BadWsFs` mounts `server CheckedSrv`, but client `SubOtherWs` subscribes to WebSocket channel `WsCheckSrv.gauge` on unmounted server `WsCheckSrv`" BadWsFs CheckedSrv SubOtherWs
component VerifiedWsEnsures:
  session user
  state lastVal : Nat = 0
  invariant lastBounded: lastVal <= 50
  subscribe g = WsCheckSrv.gauge(1) if user.isSome:
    on_message(v): lastVal = v
  action sendOk(n: Nat): if n <= 50: g.send(n)
  view: <span>{lastVal}</span>
#guard
  let ck := (Qed.Server.SetCookie.mkSafe "qed_session" "tok\r\nX-Evil: 1" (maxAge? := some 3600) (secure := true)).render
  let parseGz (h : String) := (Qed.Server.Http.parseRequestHead s!"GET /app.js HTTP/1.1\r\nHost: localhost\r\nAccept-Encoding: {h}".toUTF8).toOption.map (·.acceptsGzip)
  let doc := Qed.renderDocument "Default" "<p>ok</p>" "/qed_host.mjs" (headMeta := { title := some "Page </title><script>alert(1)</script>", description := some "Desc \"quoted\" <tag>", metaTags := [("og:title", "OG \"bad\"")], canonical := some "https://example.com/posts/1" })
  let badDoc := Qed.renderDocument "Default" "<p>ok</p>" "/qed_host.mjs" (headMeta := { canonical := some "javascript:alert(1)" })
  ["qed_session=tokX-Evil: 1", "HttpOnly", "SameSite=Lax", "Secure", "Max-Age=3600"].all (ck.contains ·) && !ck.contains '\r' && !ck.contains '\n' &&
  parseGz "br, gzip, deflate" == some true && parseGz "gzip;q=0" == some false &&
  ["<title>Page &lt;/title&gt;&lt;script&gt;alert(1)&lt;/script&gt;</title>", "<meta name=\"description\" content=\"Desc &quot;quoted&quot; &lt;tag&gt;\">", "<meta name=\"og:title\" content=\"OG &quot;bad&quot;\">", "<link rel=\"canonical\" href=\"https://example.com/posts/1\">"].all (doc.contains ·) &&
  !doc.contains "<script>alert(1)</script>" && !badDoc.contains "rel=\"canonical\"" && !badDoc.contains "javascript:"
server WebEssentialsSrv:
  state hits : Nat = 0
  invariant hitsBounded: hits <= 1000
  def login(token: String) -> String:
    setCookie("qed_session", token)
    return "ok"
  get "/robots.txt": return text("User-agent: *\nAllow: /\n")
  post "/webhook":
    requires ctx.isAuthenticated
    atomic: if hits < 1000: hits += 1
    setCookie("wh_seen", "1")
    return json({ ok = true })
  post "/echo-cookie":
    atomic: if hits < 1000: hits += 1
    setCookie("echo_ck", ctx.body)
    return json({ ok = true })
  get "/stats": return json({ ok = true, hits = hits })
  get "/hits": return json(hits)
  stream "/events":
    send("hello", event = "greeting", id = "1")
    send("world")
bad_srv_inv "Server invariant `hitsBounded` failed in `POST /bad`:\n  • must satisfy:  hits + 5 <= 10" BadHttpRouteInv hits : Nat = 0 | hitsBounded : hits <= 10 |
  post "/bad":
    hits += 5
    return text("oops")
bad_srv1 "`send(...)` is only available inside `stream \"/...\":` routes" BadSendOutsideStream :
  get "/bad-send":
    send("nope")
    return text("ok")
component SimpleHeadPage:
  head:
    title       "Simple Page"
    description "Static head metadata"
    meta        "og:site_name", "Qed"
  view: <main><h1>Hello</h1></main>
example : (SimpleHeadPage.app.headFor SimpleHeadPage.init).title = some "Simple Page" ∧ SimpleHeadPage.app.ssrStatus SimpleHeadPage.init = 200 := ⟨rfl, rfl⟩
expect_err "`case` inside `head:` requires a `route` declaration on `component BadHeadCase`" in
component BadHeadCase:
  head:
    case .home: title "Nope"
  view: <main>ok</main>

end ServerChecks
