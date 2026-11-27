import Qed
import Qed.Server.Http
import QedTests.CheckHelper
open Qed

namespace ServerChecks
external PingApi:
  base "https://api.example.com"
  get "/ping" ping() -> String
schema CheckedItem:
  label : String where 1 <= label.length <= 32
  stock : Nat    where stock <= 100
bad_srv "cannot access server state `count` outside an `atomic` block in `bump`" BadToctouRead : state count : Nat = 0 | rpc bump() -> Nat!: let c = count; await PingApi.ping()?; return c
bad_srv "cannot access server state `count` outside an `atomic` block in `bump`" BadOutsideAtomicMut : state count : Nat = 0 | rpc bump() -> Nat!: await PingApi.ping()?; count += 1; return 1
bad_srv "redundant `atomic` block: `bump` has no `await` calls" BadRedundantAtomic : state count : Nat = 0 | rpc bump() -> Nat: atomic: count += 1; return count
bad_srv "cannot use `await` inside an `atomic` block" BadAwaitInAtomic : state count : Nat = 0 |
  rpc bump() -> Nat!:
    await PingApi.ping()?
    atomic: await PingApi.ping()?; count += 1
    return 1
bad_srv "unhandled fallible `await` expression" BadUnhandledError : rpc callIt() -> String: let res = await PingApi.ping(); return "ok"
bad_srv "Array index `idx` could be out of bounds for `items`:\n  • must satisfy:  idx < items.size" BadArrayBounds : state items : Nat[] = [10, 20] | rpc readAt(idx: Nat) -> Nat: return items[idx]
bad_srv "Schema field rule `1 <= \"\".length and \"\".length <= 32` failed for `\"\"`." BadFieldRefinement : rpc makeEmpty() -> CheckedItem: return CheckedItem(label="", stock=5)
bad_srv "Server invariant `maxStock` failed in `overflow`:\n  • must satisfy:  stock + 50 <= 100" BadSingleStateInv : state stock : Nat = 10 | invariant maxStock: stock <= 100 | rpc overflow() -> Nat: stock += 50; return stock
bad_srv "Server invariant `ordersMonotonic` failed in `resetOrders`:\n  • must satisfy:  0 >= orders" BadTwoStateInv : state orders : Nat = 5 | invariant ordersMonotonic: orders >= old(orders) | rpc resetOrders() -> Nat: orders = 0; return orders
bad_srv "Server invariant `authItems` failed in `unauthenticatedPush`:\n  • must satisfy:  items.push x = items or ctx.userId != none" BadMutatingAuthInv : state items : Nat[] = [1] | invariant authItems: mutating items requires ctx.userId != none | rpc unauthenticatedPush(x: Nat) -> Nat: items.push(x); return items.size
bad_srv "Server postcondition `ensures result > 10` failed in `compute`:\n  • must satisfy:  5 > 10" BadServerEnsures :
  rpc compute(x: Nat) -> Nat:
    ensures result > 10
    return 5
server CheckedSrv:
  rpc buy(qty: Nat) -> Nat!:
    requires ctx.userId != none, 1 <= qty <= 50
    ensures result == qty, 1 <= result <= 50
    if qty == 49: return fail(.soldOut)
    elif qty == 50: return fail(.limitReached)
    return qty
server OtherSrv:
  rpc ping() -> Nat: return 1
bad_comp_sess "RPC `CheckedSrv.buy` precondition `1 <= qty <= 50` could not be proved here:\n  • must satisfy:  1 <= 0 and 0 <= 50" BadClientRequiresParam : if user.isSome: let _ = await CheckedSrv.buy(0) catch: case _: pass
bad_comp "RPC `CheckedSrv.buy` requires an authenticated session (`ctx.userId != none`), but `BadClientRequiresAuth` has no `session` field." BadClientRequiresAuth : action go: let _ = await CheckedSrv.buy(1) catch: case _: pass | view: <span>ok</span>
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
  rpc bump() -> Nat: hits += 1; return hits
  rpc quote(qty: Nat) -> Nat:
    requires ctx.userId != none, 1 <= qty <= 50
    ensures result == qty, 1 <= result <= 50
    return qty
bad_comp_query "reactive `query count` cannot call mutating server RPC `QuerySrv.bump`" BadMutatingQuery count = QuerySrv.bump()
bad_comp_query "RPC `QuerySrv.quote` precondition `1 <= qty <= 50` could not be proved here:\n  • must satisfy:  1 <= 0 and 0 <= 50" BadQueryRequiresParam q = QuerySrv.quote(0) if user.isSome
bad_comp_query "RPC `QuerySrv.quote` requires an authenticated session (`user != none`)" BadQueryRequiresAuth q = QuerySrv.quote(5)
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
bad_ext "`external BadAuthWs` declares client-usable `ws` channels and cannot attach server `auth` secrets" BadAuthWs : base "wss://ws.example.com" | auth bearer(secret("WS_SECRET")) | ws "/stream" feed() -> String
bad_srv "Channel `ensures` postcondition failed at `emit`:\n  • must satisfy:  99 <= 50" BadEmitSrv :
  channel bounded() -> Nat:
    ensures event <= 50
    on_join: pass
  | rpc pushBad() -> Unit: bounded.emit(99); return ()
server WsCheckSrv:
  channel gauge(room: Nat) -> Nat:
    requires ctx.userId != none, room <= 10
    ensures event <= 50
    on_join: pass
    on_send(v: Nat):
      requires v <= 50
      gauge.emit(room, v)
    on_leave: pass
bad_comp_sub "RPC `WsCheckSrv.gauge` requires an authenticated session (`user != none`)" BadSubNoAuth g = WsCheckSrv.gauge(1)
bad_comp_sub "RPC `WsCheckSrv.gauge` precondition `room <= 10` could not be proved here:\n  • must satisfy:  99 <= 10" BadSubBadParam g = WsCheckSrv.gauge(99) if user.isSome
bad_comp_sub "RPC `WsCheckSrv.gauge.send` precondition `v <= 50` could not be proved here:\n  • must satisfy:  77 <= 50" BadSendParam g = WsCheckSrv.gauge(1) if user.isSome | go : g.send(77)
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
bad_srv "Server invariant `hitsBounded` failed in `POST /bad`:\n  • must satisfy:  hits + 5 <= 10" BadHttpRouteInv : state hits : Nat = 0 | invariant hitsBounded: hits <= 10 | post "/bad": hits += 5; return text("oops")
bad_srv "`send(...)` is only available inside `stream \"/...\":` routes" BadSendOutsideStream : get "/bad-send": send("nope"); return text("ok")
component SimpleHeadPage:
  head:
    title       "Simple Page"
    description "Static head metadata"
    meta        "og:site_name", "Qed"
  view: <main><h1>Hello</h1></main>
example : (SimpleHeadPage.app.headFor SimpleHeadPage.init).title = some "Simple Page" ∧ SimpleHeadPage.app.ssrStatus SimpleHeadPage.init = 200 := ⟨rfl, rfl⟩
bad_comp "`case` inside `head:` requires a `route` declaration on `component BadHeadCase`" BadHeadCase :
  head:
    case .home: title "Nope"
  | view: <main>ok</main>

-- Stateless `server` and per-viewer `channel ... project(...)` with `blindTo`
record RawGameRoom:
  code           : String
  secretLocation : String
  secretPack     : String
  spyIds         : String[]
record RedactedGameView:
  code           : String
  secretLocation : String?
  secretPack     : String?
  isSpy          : Bool
server stateless RedactedHub:
  channel room(code: String) -> RedactedGameView:
    requires ctx.userId != none
    ensures event.code == code
    project(raw: RawGameRoom):
      if ctx.userId.getD("") in raw.spyIds:
        ensures result.secretLocation == none, result.secretPack == none
        blindTo raw.{secretLocation, secretPack}
      let isSpy = ctx.userId.getD("") in raw.spyIds
      return { code = code, secretLocation = none if isSpy else some(raw.secretLocation), secretPack = none if isSpy else some(raw.secretPack), isSpy = isSpy }
    on_join: pass
  rpc pushState(code: String, loc: String, pack: String, spies: String[]) -> Unit:
    requires ctx.userId != none
    room.emit(code, { code = code, secretLocation = loc, secretPack = pack, spyIds = spies })
check_decls [RedactedHub.is_stateless, RedactedHub.room_project_ensures, RedactedHub.room_project_blindTo, RedactedHub.room_project_channel_ensures]
example : RedactedHub.wsProject { userId := some "alice" } "other" ByteArray.empty ByteArray.empty = .passthrough := rfl
bad_srv "`server stateless BadStatelessSrv` forbids in-memory `state` field `count`" [stateless] BadStatelessSrv : state count : Nat = 0 | rpc getCount() -> Nat: return count
bad_srv "`blindTo raw.secretLocation` failed in `LeakyProjSrv.room_project`" [stateless] LeakyProjSrv :
  channel room(code: String) -> RedactedGameView:
    project(raw: RawGameRoom):
      if ctx.userId.getD("") in raw.spyIds:
        blindTo raw.secretLocation
      return { code = f"{code}:{raw.secretLocation}", secretLocation = none, secretPack = none, isSpy = true }

/-! ## Track 0, 1, 3 & 4: `rpc` vs `fn`, `before:`, `requires auth`, `newId`, `mintBearerToken`, `gcpMetadata`, 5xx redaction -/
enum ExtTab:
  overview
  deployLogs = "deploy-logs"
external GcpAdcExt:
  base "https://run.googleapis.com"
  auth gcpMetadata
  get "/v2/projects/:proj/locations/:tab" listLocs(proj: String, tab: ExtTab) -> String
record EchoReq:
  msg : String
external GcpIdExt:
  base "https://my-svc.run.app"
  auth gcpMetadata("https://my-svc.run.app")
  get "/health" health() -> String
router GuardedRoute:
  home    = "/"
  project = "/projects/:slug"
server GuardedApi:
  state hits : Nat = 0
  state revoked : String[] = []
  invariant hitsNonNeg: hits >= 0
  before:
    if let some(authHdr) = ctx.header("authorization"):
      if authHdr in revoked:
        return fail(401, "token revoked")
  fn bump(n: Nat) -> Nat:
    atomic:
      hits += n
      return hits
  fn formatGreeting(who: String) -> String: return f"hi {who}"
  read_only fn readHitsHelper() -> Nat!:
    atomic: return hits
  fn mintAndHash(uid: String) -> (String, String)!:
    let tok = await Qed.Server.mintBearerToken(uid, 3600)?
    let digest = await Qed.Server.hashBearerToken(tok)?
    return (tok, digest)
  read_only rpc readHits() -> Nat!: return await readHitsHelper()?
  read_only rpc billingUrl() -> Qed.Url: return url("https://billing.example.com/portal")
  rpc hello() -> String!:
    requires auth
    let n = await bump(1)?
    let id = await Qed.Server.newId("req_")?
    if id.val.length < 1: return fail(400, "unreachable")
    return f"{formatGreeting(uid)}:{n}"
  rpc whoNamed() -> String!:
    requires auth(callerId)
    return callerId
  rpc createToken() -> (String, String)!:
    requires auth
    return await mintAndHash(uid)?
  rpc revokeHeader(hdr: String) -> Unit: revoked.push(hdr)
  get "/api/ping": return Qed.Server.HttpResponse.text("pong")
  get "/legacy": return redirect(GuardedRoute.project("demo"))
  post "/api/echo":
    let req = ctx.parseJson(EchoReq)?
    let tag = ctx.queryParam("tag").getD("none")
    return text(f"{tag}:{req.msg}")
  channel feed() -> String:
    on_join: pass
    on_send(msg: String): feed.emit(msg)
check_decls [Qed.Server.ApiError.wireMessage_prod_5xx]
bad_srv "`read_only rpc badMut` is not read-only: it mutates server state" BadReadOnlyMutSrv : state x : Nat = 0 | read_only rpc badMut() -> Nat: x += 1; return x
bad_srv "`read_only rpc badCookie` is not read-only: it sets or clears cookies" BadReadOnlyCookieSrv : read_only rpc badCookie() -> Unit: setCookie("a", "b")

/-! ## Phase 3 Tests: Richer `external`, `service`, `Crypto`/`Time`/`Random`/`secret`, Default Params, Guard-`let`, `prove:` -/
schema StripeCheckoutReq:
  mode       : String
  successUrl : String
  quantity   : Nat
  coupon     : String?
external SecretManagerApi:
  base "https://secretmanager.googleapis.com"
  auth gcpMetadata
  ssrf_guard
  post "/v1/projects/{project}/secrets" createSecret(project: String, query("secretId") secretId: String, body: Json) -> Json ok [200, 201, 409]
  post "/v1/projects/{project}/secrets/{id}:addVersion" addVersion(project: String, id: String, body: Json) -> Json
  get "/v1/projects/{project}/secrets" listSecrets(project: String, query pageSize: Nat?, query filter: String?) -> Json
external StripeFormApi:
  base "https://api.stripe.com"
  auth bearer(secret("STRIPE_API_KEY"))
  post "/v1/checkout/sessions" createSession(header("Idempotency-Key") idemKey: String?, body: Form(StripeCheckoutReq)) -> Json
  get "/v1/customers" listCustomers(query("starting_after") after: String?, query limit: Nat?) -> Json
external GuardedLocalApi:
  base "http://127.0.0.1:1"
  get "/ping" ping() -> String
external UnguardedLocalApi:
  base "http://127.0.0.1:1"
  ssrf_guard false
  get "/ping" ping() -> String
bad_ext "`Form(T)` is only supported for HTTP request body parameters, not response types" BadFormRetApi : base "https://api.example.com" | get "/bad" bad() -> Form(StripeCheckoutReq)
bad_ext "HTTP status code `999` in `ok [...]` must be between 100 and 599" BadOkStatusApi : base "https://api.example.com" | get "/bad" bad() -> String ok [200, 999]

private def doublePlus (n : Nat) : Nat := n + n + 1
private theorem doublePlus_odd (n : Nat) : doublePlus n % 2 = 1 := by unfold doublePlus; omega
fn checkPureGuardAndProve(opt: (Nat, Nat)?, bonus: Nat = 1) -> Nat:
  ensures result % 2 == 1
    prove:
      dsimp only [checkPureGuardAndProve]
      cases opt with
      | none => simp [doublePlus_odd]
      | some p => simp [doublePlus_odd]
  let some((a, b)) = opt else return doublePlus(bonus)
  return doublePlus(a + b + bonus)
service Webhooks:
  secret signingKey = "WEBHOOK_SECRET"
  env region = "APP_REGION" ?? "us-central1"
  fn parseSigHeader(hdr: String) -> (Nat, String)?:
    match Qed.Str.splitChar(hdr, ','):
      case [tsStr, sig]:
        let some(ts) = Qed.Str.parseNat?(tsStr) else return none
        return some((ts, sig))
      case _: return none
  read_only fn verifyWithKey(key: Secret, payload: String, sigHeader: String, toleranceSec: Nat = 300) -> Bool:
    let some((ts, v1)) = parseSigHeader(sigHeader) else return false
    let now = await Time.nowSec()
    if absDiff(now, ts) > toleranceSec: return false
    let expected = await Crypto.hmacSha256Hex(key, f"{ts}.{payload}")
    return await Crypto.constEq(v1, expected)
  read_only fn verifyStripe(payload: String, sigHeader: String, toleranceSec: Nat = 300) -> Bool!:
    return await verifyWithKey(signingKey, payload, sigHeader, toleranceSec)
  read_only fn issueNonce(seed: Nat) -> Nat!:
    ensures result % 2 == 1
      prove: exact doublePlus_odd seed
    let _tok = await Random.hex(16)
    let _uid = await Random.uuid()
    let _b64 = Base64.encodeString(region)
    return doublePlus(seed)
service BillingSvc:
  use hooks : Webhooks
  read_only fn checkEvent(payload: String, sig: String) -> Bool!: return await hooks.verifyStripe(payload, sig)?
  fn syncSecret(project: String, id: String, raw: String) -> Json!:
    let _ = await SecretManagerApi.createSecret(project, id, Json.obj([].toList))?
    let payload = Json.obj([("payload", Json.obj([("data", Json.str(Base64.encodeString(raw)))].toList))].toList)
    return await SecretManagerApi.addVersion(project, id, payload)?
  fn openCheckout(req: StripeCheckoutReq, idem: String? = none) -> Json!: return await StripeFormApi.createSession(idem, req)?
server stateless ServiceHost:
  use billing : BillingSvc
  use hooks : Webhooks
  read_only rpc verifyWebhook(payload: String, sig: String) -> Bool!: return await billing.checkEvent(payload, sig)?
  read_only rpc getOddToken(n: Nat) -> Nat!:
    ensures result % 2 == 1
      prove: exact doublePlus_odd n
    let _ = await hooks.issueNonce(n)?
    return doublePlus(n)
  rpc createCheckout(req: StripeCheckoutReq) -> String!:
    let res = await billing.openCheckout(req)?
    return res.render
  rpc rotateSecret(project: String, id: String, raw: String) -> String!:
    let res = await billing.syncSecret(project, id, raw)?
    return res.render

/-! ## Effect-Aware Contracts (`no_http`, `no_decrypt`, `no_crypto`, `no_db_write`, `ensures_fails`) & Service/Server `example` Blocks -/
external ItemSyncApi:
  base "https://items.example.com"
  post "/v1/sync/{id}" syncOne(id: String) -> String
database ExVaultDb:
  sqlite ".qed/ex_vault_checks.db"
  table vault_items:
    id      : String primary_key immutable where 1 <= id.length <= 64
    ownerId : String immutable where 1 <= ownerId.length <= 64
    label   : String where 1 <= label.length <= 120
    payload : encrypted(String, key = secret("VAULT_KEY"))
    policy read, write requires some(ownerId) == ctx.userId
service BatchSyncSvc:
  env region = "SYNC_REGION" ?? "us-west1"
  fn syncAll(ids: String[]) -> Nat!:
    if ids == []: no_http
    no_db_write
    no_crypto
    for id in ids:
      let _ = await ItemSyncApi.syncOne(id)?
    return ids.size
  fn rejectEmpty(name: String) -> String!:
    if name == "": ensures_fails 400
    no_http, no_crypto, no_db_write
    if name == "": return fail(400, "empty name")
    return f"{region}:{name}"
  example emptyNoHttp:
    call syncAll([])
    expect ok(0)
    expect http_calls == 0
  example batchCallsUpstream:
    with http POST "https://items.example.com/v1/sync/a" => 200 "ok"
    with http POST "https://items.example.com/v1/sync/b" => 200 "ok"
    call syncAll(["a", "b"])
    expect ok(2)
    expect http_calls == 2
    expect http[0].method == "POST"
    expect http[0].url == "https://items.example.com/v1/sync/a"
  example upstreamErrorPropagates:
    with http_error POST "https://items.example.com/v1/sync/bad" => 502 "upstream down"
    call syncAll(["bad"])
    expect error(502)
    expect http_calls == 1
  example customEnvRegion:
    with env "SYNC_REGION" = "eu-central1"
    call rejectEmpty("alpha")
    expect ok("eu-central1:alpha")
  example emptyNameFails:
    call rejectEmpty("")
    expect error(400)
server VaultExApi:
  use db : ExVaultDb
  use syncer : BatchSyncSvc
  state counter : Nat = 0
  invariant counterCap: counter <= 100
  read_only rpc listMeta() -> ExVaultDb.vault_items.Meta[]!:
    requires auth
    no_http, no_decrypt, no_db_write
    return await db.vault_items.selectMeta(where = r => r.ownerId == uid, orderBy = "id")?
  rpc saveItem(id: String, label: String, payload: String) -> ExVaultDb.vault_items!:
    requires auth, 1 <= id.length <= 64, 1 <= label.length <= 120, 1 <= uid.length <= 64
    no_http
    return await db.vault_items.insert(id = id, ownerId = uid, label = label, payload = payload)?
  rpc bumpAndStamp() -> Nat!:
    requires auth
    no_http, no_db_write
    let now = await Time.nowMs()
    setCookie("last_seen", f"{now}")
    atomic:
      if counter < 100: counter += 1
      return counter
  get "/health":
    no_http, no_db_write, no_crypto
    return text("alive")
  post "/echo":
    requires auth
    no_http, no_db_write
    let hdr = if let some(h) = ctx.header("x-tag"): h else: "none"
    return text(f"{hdr}:{ctx.query}:{ctx.body}")
  example seedAndListMeta:
    with user "alice"
    with db vault_items = [{ id = "v1", ownerId = "alice", label = "prod-db", payload = "sec1" }, { id = "v2", ownerId = "bob", label = "other", payload = "sec2" }]
    call listMeta()
    expect ok([{ id = "v1", ownerId = "alice", label = "prod-db" }])
    expect decrypt_calls == 0
    expect http_calls == 0
  example insertEncryptsAndPersists:
    with env "VAULT_KEY" = "test-vault-key"
    with user "alice"
    call saveItem("v9", "api-key", "secret-val")
    expect ok
    expect encrypt_calls == 1
    expect db_count("vault_items") == 1
  example insertMissingKeyFails:
    with user "alice"
    call saveItem("v9", "api-key", "secret-val")
    expect error(500)
  example unauthBlocked:
    call listMeta()
    expect error(401)
  example statefulBumpSetsCookie:
    with user "alice"
    with role "admin"
    with now = 1700000000000
    with state = { counter = 4 }
    call bumpAndStamp()
    expect ok(5)
    expect state.counter == 5
    expect cookies.size == 1
  example httpHealthRoute:
    get "/health"
    expect status == 200
  example httpEchoRoute:
    with user "alice"
    with header "x-tag" = "v1"
    with query = "q=1"
    with body = "hi"
    post "/echo"
    expect status == 200
bad_svc "Server invariant `no_http` failed in `sneaky`" BadNoHttpSvc :
  fn sneaky(id: String) -> String!:
    no_http
    return await ItemSyncApi.syncOne(id)?
bad_db "Server invariant `no_decrypt` failed in `readSecret`" ExVaultDb :
  read_only rpc readSecret() -> ExVaultDb.vault_items[]!:
    requires auth
    no_decrypt
    return await db.vault_items.select(where = r => r.ownerId == uid)?
bad_db "Server invariant `no_db_write` failed in `sneakyInsert`" ExVaultDb :
  rpc sneakyInsert(id: String, label: String, payload: String) -> ExVaultDb.vault_items!:
    requires auth, 1 <= id.length <= 64, 1 <= label.length <= 120, 1 <= uid.length <= 64
    no_db_write
    return await db.vault_items.insert(id = id, ownerId = uid, label = label, payload = payload)?
bad_svc "Server postcondition `ensures ensures_fails 400` failed in `actuallySucceeds`" BadEnsuresFailsSvc :
  fn actuallySucceeds(n: Nat) -> Nat!:
    ensures_fails 400
    return n + 1
bad_svc "proved that the proposition" BadSrvExampleSvc : fn inc(n: Nat) -> Nat!: return n + 1 |
  example wrongResult:
    call inc(1)
    expect ok(99)

/-! ## Multi-Origin External, Async Loops/Retry, and Verified `every` Jobs -/
enum CloudRegion:
  usEast = "us-east1"
  euWest = "europe-west1"
enum PayloadEnum:
  one(v: Nat)
external CloudRunApi:
  base "https://{region}-run.googleapis.com" where region : CloudRegion
  get "/v2/services/{svcId}" getService(region: CloudRegion, svcId: String) -> String
external RegionalCdnApi:
  base "https://{tier}.{zone}.cdn.example.com" where tier in ["edge", "origin"], zone : CloudRegion
  get "/health" health(tier: String, zone: CloudRegion) -> String
example : ∀ r, Qed.Server.isValidBaseOrigin (CloudRunApi.resolveBaseOrigin r) = true := CloudRunApi.resolveBaseOrigin_valid
example : ∀ t z o, RegionalCdnApi.resolveBaseOrigin t z = .ok o → Qed.Server.isValidBaseOrigin o = true := RegionalCdnApi.resolveBaseOrigin_valid
service RetryLoopSvc:
  fn fetchWithRetry(region: CloudRegion, svcId: String) -> String!:
    let mut lastErr = "no attempts"
    for attempt in range(0, 6, 2):
      let res = await CloudRunApi.getService(region, svcId)
        catch err:
          lastErr = err.message
          continue
      return res
    return fail(503, lastErr)
  fn collectFiltered(xs: Nat[]) -> Nat!:
    no_http
    let mut total = 0
    for x in xs:
      if x == 0: continue
      if x > 50: break
      total += x
    return total
  example retrySucceedsSecond:
    with http_error GET "https://us-east1-run.googleapis.com/v2/services/app1" => 503 "busy"
    with http GET "https://us-east1-run.googleapis.com/v2/services/app1" => 200 "ready"
    call fetchWithRetry(.usEast, "app1")
    expect ok("ready")
  example retryExhaustsAll:
    with http_error GET "https://us-east1-run.googleapis.com/v2/services/app1" => 503 "down"
    call fetchWithRetry(.usEast, "app1")
    expect error(503)
  example loopSkipsAndBreaks:
    call collectFiltered([0, 4, 6, 99, 10])
    expect ok(10)
server WorkerLoopSrv:
  state processed : Nat = 0
  state pending   : Nat = 3
  every 5s drainOne -> Bool:
    no_http, no_decrypt
    let mut didWork = false
    atomic:
      if pending > 0:
        pending -= 1
        processed += 1
        didWork = true
    return didWork
  every 30s heartbeat:
    no_http, no_decrypt
    atomic: processed += 0
bad_ext "has no matching `where region : Enum` or `where region in [...]` allowlist" BadMissingBaseWhere : base "https://{region}-run.googleapis.com" | get "/ping" ping(region: String) -> String
bad_ext "must be a unit `enum`" BadPayloadEnumWhere : base "https://{p}.example.com" where p : PayloadEnum | get "/ping" ping(p: PayloadEnum) -> String
bad_ext "invalid expanded `base` origin" BadExpandedOrigin : base "https://{host}.example.com" where host in ["good", "bad@evil"] | get "/ping" ping(host: String) -> String
bad_ext "requires a matching parameter `region` on endpoint `ping`" BadMissingEndpointBaseParam : base "https://{region}-run.googleapis.com" where region : CloudRegion | get "/ping" ping() -> String
bad_srv "Server invariant `no_http` failed in `badJob`" BadEveryNoHttpSrv :
  every 10s badJob -> Bool:
    no_http
    let _ = await PingApi.ping()
      catch _err: return false
    return true
bad_srv "`every` job `badRet` return type must be `Bool`" BadEveryRetTypeSrv : every 10s badRet -> String: return "nope"
bad_srv "missing `return` on fallthrough path of `-> Bool` job `badFallthrough`" BadEveryFallthroughSrv : every 10s badFallthrough -> Bool: let _x = 1
bad_svc "`break` can only be used inside a `for` loop" BadAsyncBreakSvc : fn bad() -> Nat!: break; return 1

/-! ## Kernel Reduction, Webhook Effects & Ergonomics Regressions -/
/-- External JSON API used to verify `decodeRespJson` reduces in Lean's kernel. -/
external JsonEchoApi:
  base "https://api.json-echo.example.com"
  get "/item/{id}" getItem(id: String) -> Json
structure ErgoQueryPlan where
  orderBy? : Option String
  limit?   : Option Nat
deriving BEq, Repr
private def testAlertWebhookUrl : Qed.Server.WebhookUrl := Qed.Server.WebhookUrl.make "https://hooks.example.com/alerts" (by decide +kernel)
private def testRawWebhookUrl : Qed.Server.WebhookUrl := Qed.Server.WebhookUrl.make "https://hooks.example.com/raw" (by decide +kernel)
/-- Service exercising external `-> Json`, `Webhook`, trailing `?`, cons patterns, tuple `let`, multiline signatures, doc comments, and type inference. -/
service ErgoAndKernelSvc:
  /-- Fetch a JSON item from an external endpoint returning `-> Json`. -/
  fn fetchJsonName(id: String) -> String!:
    let j = await JsonEchoApi.getItem(id)?
    return j.strAtD("name", "empty")
  /-- Dispatch a JSON webhook alert and prove no DB write / decrypt / crypto effects. -/
  fn dispatchJsonAlert(url: WebhookUrl, msg: String) -> String!:
    no_db_write, no_decrypt, no_crypto
    let payload = Json.object([("msg", .str(msg)), ("tags", Json.array([.str("alert")]))])
    let resp : Json = await Qed.Server.Webhook.postJson(url, payload)?
    return resp.strAtD("status", "sent")
  /-- Dispatch a raw bytes webhook alert and prove no DB write / decrypt / crypto effects. -/
  fn dispatchBytesAlert(url: WebhookUrl, raw: Bytes) -> Nat!:
    no_db_write, no_decrypt, no_crypto
    let resp = await Qed.Server.Webhook.postBytes(url, "application/octet-stream", raw)?
    return resp.size
  /-- Trailing `?` ergonomics: `arr[0]?`, user `plan.orderBy?`, Json `.obj?`/`.str?`, local `x?`. -/
  fn inspectPlan(arr: String[], plan: ErgoQueryPlan, v: Json) -> String:
    let first? = arr[0]?
    let ord? = plan.orderBy?
    let hasObj = v.obj?.isSome
    let label = v.str? ?? (first? ?? "none")
    let suffix = if hasObj: "obj" else: ord? ?? "default"
    return label ++ ":" ++ suffix
  /-- Explicit `(arr[0])?` still unwraps an element of `Array (Option String)`. -/
  fn unwrapFirstOpt(arr: String?[]) -> String!:
    if arr.size == 0: return fail(400, "empty")
    let s = (arr[0])?
    return s
  /-- Cons pattern matching (`case x :: xs:`) and tuple destructuring (`let (a, b) = ...`). -/
  fn sumHeadPair(xs: List Nat, pair: (Nat, (Nat, Nat))) -> Nat:
    let (a, (b, _)) = pair
    match xs:
      case []: return a + b
      case h :: []: return h + a + b
      case h1 :: h2 :: _: return h1 + h2 + a + b
  /-- Multiline signature with multi-word return type and `let mut : List Json = []`. -/
  fn buildJsonList(
    xs: String[],
    tag: String
  ) -> Except Qed.Server.ApiError Json:
    let mut acc : List Json = []
    for x in xs: acc = List.cons(Json.obj([("tag", .str(tag)), ("v", .str(x))]), acc)
    return .ok(Json.arr(acc.reverse))
  /-- Doc-commented example testing `-> Json` external endpoint, `Webhook`, and dotted `.ok(...)`. -/
  example jsonEndpointAndDottedOk:
    with http GET "https://api.json-echo.example.com/item/42" => 200 "{\"name\":\"widget\"}"
    call fetchJsonName("42")
    expect result.map(s => s ++ "!") == .ok("widget!")
  example jsonEndpointEmptyBody:
    with http GET "https://api.json-echo.example.com/item/empty" => 200 "   "
    call fetchJsonName("empty")
    expect ok("empty")
  example webhookJsonAndBytes:
    with http POST "https://hooks.example.com/alerts" => 200 "{\"status\":\"accepted\"}"
    call dispatchJsonAlert(testAlertWebhookUrl, "hi")
    expect ok("accepted")
  example webhookBytesOk:
    with http POST "https://hooks.example.com/raw" => 200 "pong"
    call dispatchBytesAlert(testRawWebhookUrl, "ping".toUTF8)
    expect ok(4)
  example ergoHelpersWork:
    call inspectPlan(["alpha"], { orderBy? = some("id"), limit? = none }, Json.str("beta"))
    expect result == "beta:id"
  example explicitUnwrapArrElem:
    call unwrapFirstOpt([some("ok")])
    expect ok("ok")
  example consAndTupleWork:
    call sumHeadPair([10, 20, 30], (1, (2, 99)))
    expect result == 33
  example listMutAndJsonObjWork:
    call buildJsonList(["a", "b"], "k")
    expect result == .ok(Json.arr([Json.obj([("tag", .str("k")), ("v", .str("a"))]), Json.obj([("tag", .str("k")), ("v", .str("b"))])]))
bad_svc "Server invariant `no_http` failed in `badWebhookNoHttp`" BadWebhookNoHttpSvc :
  fn badWebhookNoHttp(url: WebhookUrl) -> String!:
    no_http
    let resp : Json = await Qed.Server.Webhook.postJson(url, Json.null)?
    return resp.render
/-- Stateful server verifying doc comments, multiline `rpc` signature, and tuple `let` across `atomic:`. -/
server ErgoStatefulSrv:
  /-- Running total state. -/
  state total : Nat = 0
  /-- Multiline `rpc` with tuple `let` inside `atomic:` exporting a destructured binding. -/
  rpc addAndSplit(
    pair: (Nat, Nat)
  ) -> Except String Nat:
    let _ = await PingApi.ping()
      catch _e: ""
    atomic:
      let (delta, bonus) = pair
      total += delta
    return .ok(bonus)
end ServerChecks
