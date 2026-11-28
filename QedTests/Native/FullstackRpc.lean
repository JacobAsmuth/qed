import QedTests.Native.Harness
import Examples.CloudBooks
import QedTests.ServerChecks
import Qed.Server.Native
open System (FilePath)
open Qed.Server Qed.Server.Http

namespace QedTests.Native.FullstackRpc

structure MockExtState where
  (tokenExchanges d1Count : Nat := 0) (rsaVerified sawUnescaped failD1 : Bool := false) (gcsObjects : Std.HashMap String ByteArray := {})

private def startMockExternal (pemKey : String) : IO (Except String (String × IO.Ref MockExtState × IO Unit)) := do
  let stRef ← IO.mkRef ({} : MockExtState); let b64Url (s : String) := (Qed.Base64.decodeUrl s).toOption.getD ByteArray.empty
  let res ← startMockHttpServer fun method target hdrs body => do
    let authHdr := (getHeader? hdrs "authorization").getD ""; let (pathOnly, queryStr) := splitPathQuery target
    if method == "POST" && pathOnly == "/oauth2/token" then
      let assertion := ((Qed.Auth.parseQueryParams (utf8Str body)).lookup "assertion").getD ""
      match assertion.splitOn "." with
      | [p0, p1, p2] =>
          let okSig ← Prim.rsaSha256Verify pemKey (s!"{p0}.{p1}").toUTF8 (b64Url p2); let claims := utf8Str (b64Url p1)
          if okSig && claims.contains "qed-test@proj.iam.gserviceaccount.com" && claims.contains "devstorage.read_write" then
            stRef.modify fun s => { s with rsaVerified := true, tokenExchanges := s.tokenExchanges + 1 }
            return jsonStrResp 200 "{\"access_token\":\"mock-gcs-token-777\",\"expires_in\":3600}"
          else return jsonStrResp 401 "{\"error\":\"invalid_grant\"}"
      | _ => return jsonStrResp 401 "{\"error\":\"invalid_grant\"}"
    else if pathOnly.startsWith "/upload/storage/v1/b/" || pathOnly.startsWith "/storage/v1/b/" then
      if authHdr != "Bearer mock-gcs-token-777" then return txtResp 401 "unauthorized gcs"
      else if method == "POST" && pathOnly == "/upload/storage/v1/b/qed-covers/o" then
        let name := ((Qed.Auth.parseQueryParams queryStr).lookup "name").getD ""
        stRef.modify fun s => { s with gcsObjects := s.gcsObjects.insert name body }
        return jsonStrResp 200 s!"\{\"name\":\"{name}\",\"size\":{body.size}}"
      else if method == "GET" && pathOnly.startsWith "/storage/v1/b/qed-covers/o/" then
        if target.contains "/o/covers/" then stRef.modify fun s => { s with sawUnescaped := true }
        match (← stRef.get).gcsObjects[dropChars pathOnly "/storage/v1/b/qed-covers/o/".length]? with
        | some stored => return (200, "application/octet-stream", stored) | none => return txtResp 404 "object not found"
      else return txtResp 404 "unknown gcs"
    else if method == "POST" && pathOnly == "/accounts/demo-account/d1/database/demo-db/query" then
      if authHdr != "Bearer test-cf-d1-secret" then return txtResp 401 "unauthorized d1"
      let fail := (← stRef.get).failD1; stRef.modify fun s => { s with d1Count := s.d1Count + 1 }
      return if fail then jsonStrResp 500 "{\"success\":false,\"error\":\"simulated D1 outage\"}" else jsonStrResp 200 "{\"success\":true}"
    else return txtResp 404 s!"unknown mock route: {target}"
  return res.map fun (port, stop) => (s!"http://127.0.0.1:{port}", stRef, stop)

private def gunzipBytes (gz : ByteArray) : IO (Except String ByteArray) :=
  withTempDir "qed-gz-test" fun tmp => do
    let (gzFile, outFile) := (s!"{tmp}/in.gz", s!"{tmp}/out.bin"); IO.FS.writeBinFile gzFile gz
    let (code, _, err) ← runCmd "sh" #["-c", s!"gzip -dc '{gzFile}' > '{outFile}'"]
    if code != 0 then return .error s!"gzip -dc failed ({code}): {err}" else return .ok (← IO.FS.readBinFile outFile)

private def checkGzipResp (c : TestChecker) (label : String) (res : Except String HttpResp) (rawWant : String) : IO Unit :=
  c.checkHttp label res (headers := [("content-encoding", some "gzip"), ("vary", some "Accept-Encoding")]) (extra := fun r => do
    c.check s!"{label} smaller than raw ({r.body.size} < {rawWant.utf8ByteSize})" (r.body.size < rawWant.utf8ByteSize)
    c.expectOk s!"{label} gunzip" (← gunzipBytes r.body) fun raw => c.checkEq s!"{label} decompresses identically" (String.fromUTF8? raw) (some rawWant))

private def runMovedServerChecks (c : TestChecker) : IO Unit := do
  let ck := (Qed.Server.SetCookie.mkSafe "qed_session" "tok\r\nX-Evil: 1" (maxAge? := some 3600) (secure := true)).render
  let parseGz (h : String) := (parseRequestHead s!"GET /app.js HTTP/1.1\r\nHost: localhost\r\nAccept-Encoding: {h}".toUTF8).toOption.map (·.acceptsGzip)
  let doc := Qed.renderDocument "Default" "<p>ok</p>" "/qed_host.mjs" (headMeta := { title := some "Page </title><script>alert(1)</script>", description := some "Desc \"quoted\" <tag>", metaTags := [("og:title", "OG \"bad\"")], canonical := some "https://example.com/posts/1" })
  let badDoc := Qed.renderDocument "Default" "<p>ok</p>" "/qed_host.mjs" (headMeta := { canonical := some "javascript:alert(1)" })
  let rawRoom : ServerChecks.RawGameRoom := { code := "ABCD", secretLocation := "Casino", secretPack := "Classic", spyIds := #["bob"] }
  let (params, payload) := (Qed.Proto.encode "ABCD", Qed.Proto.encode rawRoom)
  let aliceOut := (ServerChecks.RedactedHub.wsProject (RequestCtx.forUser "alice") "room" params payload).bind id
  let bobOut := (ServerChecks.RedactedHub.wsProject (RequestCtx.forUser "bob") "room" params payload).bind id
  c.checkAll [
    ("[srv-pure] SetCookie.mkSafe strips CRLF and emits flags",
      hasAll ck ["qed_session=tokX-Evil: 1", "HttpOnly", "SameSite=Lax", "Secure", "Max-Age=3600"] && !ck.toList.contains '\r' && !ck.toList.contains '\n'),
    ("[srv-pure] parseRequestHead acceptsGzip", parseGz "br, gzip, deflate" == some true && parseGz "gzip;q=0" == some false),
    ("[srv-pure] renderDocument escapes head meta & strips javascript: canonical",
      hasAll doc ["<title>Page &lt;/title&gt;&lt;script&gt;alert(1)&lt;/script&gt;</title>", "<meta name=\"description\" content=\"Desc &quot;quoted&quot; &lt;tag&gt;\">",
       "<meta name=\"og:title\" content=\"OG &quot;bad&quot;\">", "<link rel=\"canonical\" href=\"https://example.com/\">".replace "example.com/" "example.com/posts/1"] &&
      !doc.contains "<script>alert(1)</script>" && !badDoc.contains "rel=\"canonical\"" && !badDoc.contains "javascript:"),
    ("[srv-pure] RedactedHub.wsProject exposes secrets to alice & redacts for bob",
      (aliceOut.bind fun bs => (Qed.Proto.decode (α := ServerChecks.RedactedGameView) bs).toOption) == some { code := "ABCD", secretLocation := some "Casino", secretPack := some "Classic", isSpy := false } &&
      (bobOut.bind fun bs => (Qed.Proto.decode (α := ServerChecks.RedactedGameView) bs).toOption) == some { code := "ABCD", secretLocation := none, secretPack := none, isSpy := true }),
    ("[srv-pure] Webhooks.parseSigHeader & Base64.decodeString?",
      ServerChecks.Webhooks.parseSigHeader "1700000000,deadbeef" == some (1700000000, "deadbeef") &&
      ServerChecks.Webhooks.parseSigHeader "bad" == none && Qed.Base64.decodeString? (Qed.Base64.encodeString "qed-ok") == some "qed-ok"),
    ("[srv-pure] buildExternalSuffix compound & query params",
      (Qed.Server.buildExternalSuffix [.lit "v1", .lit "projects", .seg "p1", .lit "secrets", .compound [.param "my-sec", .lit ":addVersion"]] [("pageSize", .omit), ("filter", .omit)]).toOption == some "v1/projects/p1/secrets/my-sec:addVersion" &&
      (Qed.Server.buildExternalSuffix [.lit "v1", .lit "customers"] [("starting_after", Qed.Server.ToQueryVal.toQueryVal (none : Option String)), ("limit", Qed.Server.ToQueryVal.toQueryVal (some (25 : Nat)))]).toOption == some "v1/customers?limit=25"),
    ("[srv-pure] encodeFormBodyOf StripeCheckoutReq",
      String.fromUTF8? (Qed.Server.encodeFormBodyOf ({ mode := "payment", successUrl := "https://a.test/ok", quantity := 2, coupon := none : ServerChecks.StripeCheckoutReq })) == some "mode=payment&successUrl=https%3A%2F%2Fa.test%2Fok&quantity=2"),
    ("[srv-pure] GuardedApi methods/readOnly/wireMessage/redirect/queryParam & GcpAdc/GcpId secrets",
      ServerChecks.GcpAdcExt.secrets.isEmpty && ServerChecks.GcpIdExt.secrets.isEmpty &&
      ["bump", "formatGreeting", "mintAndHash"].all (!ServerChecks.GuardedApi.methods.contains ·) &&
      ["hello", "whoNamed", "createToken"].all ServerChecks.GuardedApi.methods.contains &&
      ["readHits", "billingUrl"].all ServerChecks.GuardedApi.readOnlyMethods.contains &&
      (ApiError.internal "pg password leaked").wireMessage false == "internal server error" &&
      (ApiError.internal "pg password leaked").wireMessage true == "pg password leaked" &&
      (ApiError.forbidden "nope").wireMessage false == "nope" &&
      (HttpResponse.redirect ServerChecks.GuardedRoute.home).headers == [("Location", "/")] &&
      (HttpResponse.redirect (ServerChecks.GuardedRoute.project "demo")).headers == [("Location", "/projects/demo")] &&
      (HttpResponse.redirect "/raw").headers == [("Location", "/raw")] &&
      (HttpResponse.redirect (WebhookUrl.make "https://hooks.example.com/ok")).headers == [("Location", "https://hooks.example.com/ok")] &&
      (WebhookUrl.parse? "http://insecure.example.com").isNone &&
      ({ query := "?a=1&tag=hi+qed", body := "{\"msg\":\"yo\"}" : RequestCtx }).queryParam "tag" == some "hi qed"),
    ("[srv-pure] Webhooks/ServiceHost secrets, Secret redaction, checkPureGuardAndProve, absDiff",
      ServerChecks.Webhooks.secrets == #["WEBHOOK_SECRET"] && ServerChecks.ServiceHost.secrets.contains "WEBHOOK_SECRET" &&
      ServerChecks.ServiceHost.secrets.contains "STRIPE_API_KEY" && toString (Qed.Secret.ofString "super-secret") == "<redacted>" &&
      ServerChecks.checkPureGuardAndProve none == 3 && ServerChecks.checkPureGuardAndProve (some (2, 3)) 4 == 19 &&
      Qed.absDiff (10 : Nat) 3 == 7 && Qed.absDiff (3 : Nat) 10 == 7),
    ("[srv-pure] Multi-origin CloudRunApi/RegionalCdnApi, WorkerLoopSrv jobs, SseEvent, encodeMultiSeg",
      ServerChecks.CloudRunApi.allowedBaseOrigins == #["https://us-east1-run.googleapis.com", "https://europe-west1-run.googleapis.com"] &&
      ServerChecks.CloudRunApi.resolveBaseOrigin .usEast == "https://us-east1-run.googleapis.com" && ServerChecks.RegionalCdnApi.allowedBaseOrigins.size == 4 &&
      (match ServerChecks.RegionalCdnApi.resolveBaseOrigin "edge" .euWest with | .ok s => s == "https://edge.europe-west1.cdn.example.com" | .error _ => false) &&
      !(ServerChecks.RegionalCdnApi.resolveBaseOrigin "evil" .usEast).isOk &&
      ServerChecks.WorkerLoopSrv.jobs.size == 2 && ServerChecks.WorkerLoopSrv.jobs[0]?.map (·.name) == some "drainOne" &&
      ServerChecks.WorkerLoopSrv.jobs[0]?.map (·.runWorkM?.isSome) == some true &&
      ({ data := "line1\nline2", event := some "msg" : SseEvent }).render == "event: msg\ndata: line1\ndata: line2\n\n" &&
      Qed.Server.encodeMultiSeg "/a/b c" == .ok "a/b%20c" && !(Qed.Server.encodeMultiSeg "/a/b c/").isOk)]

private def runWebEssentialsSuite (c : TestChecker) : IO Unit :=
  withDevApp c "QedTests.WebEssentialsFixture" fun dir => do
    let jsContent := String.join (List.replicate 40 "export function qedHello(x) { return 'hello-' + x; }\n")
    let hashedFile := s!"{dir}/bundle.deadbeef.mjs"; IO.FS.writeFile hashedFile jsContent
    let authSecret := "web-essentials-hmac-secret"; let aliceTok ← signSessionToken authSecret "alice"
    try
      withNativeServer c "[web-essentials] child native server healthy" dir #[("QED_WORKERS", some "2"), ("QED_AUTH_SECRET", some authSecret)] (dev := false) fun srv => do
        forList [1, 2] fun pass => do checkGzipResp c s!"[web-essentials] hashed JS gzip pass {pass}" (← httpReq srv.port "GET" "/bundle.deadbeef.mjs" #[("Accept-Encoding", "gzip")]) jsContent
        c.checkHttp "[web-essentials] hashed JS plain" (← httpReq srv.port "GET" "/bundle.deadbeef.mjs") (headers := [("content-encoding", none)]) (bodyEq? := some jsContent)
        c.checkHttp "[web-essentials] GET /robots.txt" (← httpReq srv.port "GET" "/robots.txt") (bodyEq? := some "User-agent: *\nAllow: /\n")
        c.checkStatus "[web-essentials] unauth POST /webhook rejected 401" (← httpReq srv.port "POST" "/webhook" #[] "{}".toUTF8) 401
        forList [
            ("auth POST /webhook", "/webhook", #[("Authorization", s!"Bearer {aliceTok}")], "{}", "auth POST /webhook emitted Set-Cookie wh_seen=1", ["wh_seen=1", "HttpOnly", "SameSite=Lax"]),
            ("POST /echo-cookie", "/echo-cookie", #[], "val123\r\nX-Inject: bad", "POST /echo-cookie emitted sanitized HttpOnly SameSite=Lax cookie", ["echo_ck=val123X-Inject: bad", "HttpOnly", "SameSite=Lax"])] fun (lbl, path, hdrs, body, cLbl, ckFlags) => do
          c.checkHttp s!"[web-essentials] {lbl}" (← httpReq srv.port "POST" path hdrs body.toUTF8) (bodyEq? := some "{\"ok\":true}") (extra := (·.checkCookieFlag c s!"[web-essentials] {cLbl}" ckFlags))
        c.checkHttp "[web-essentials] RPC login" (← httpRpc srv.port "WebEssentialsSrv" "login" (Qed.Proto.encode "sess_tok_42")) (extra := fun r => do
          c.checkEq "[web-essentials] RPC login payload" (Qed.Proto.decode (α := String) r.body) (.ok "ok")
          r.checkCookieFlag c "[web-essentials] RPC login emitted Set-Cookie qed_session" ["qed_session=sess_tok_42", "HttpOnly", "SameSite=Lax"])
        c.checkHttp "[web-essentials] GET /events SSE" (← httpReq srv.port "GET" "/events")
          (headers := [("content-type", some "text/event-stream; charset=utf-8"), ("cache-control", some "no-cache")]) (bodyEq? := some "event: greeting\nid: 1\ndata: hello\n\ndata: world\n\n")
        c.checkHttp "[web-essentials] SSR GET /" (← httpReq srv.port "GET" "/")
          (contains := ["<title>Home &lt;/title&gt;&lt;script&gt;alert(1)&lt;/script&gt;</title>", "<meta name=\"description\" content=\"Verified &quot;SSR&quot; &lt;head&gt;\">", "<link rel=\"canonical\" href=\"https://example.com/\">"])
          (notContains := ["<script>alert(1)</script>"]) (extra := (·.checkDefaultCsp c "[web-essentials] SSR GET / has strict default CSP"))
        c.checkHttp "[web-essentials] SSR GET /missing" (← httpReq srv.port "GET" "/missing") (status? := some 404) (contains := ["<title>404 Not Found</title>"])
        c.checkHttp "[web-essentials] SSR GET /old" (← httpReq srv.port "GET" "/old") (status? := some 302) (headers := [("location", some "/new")])
    finally rmRf hashedFile

private def runServiceAndExternalSuite (c : TestChecker) : IO Unit := do
  let logRef ← IO.mkRef (#[] : Array (String × String × Option String × Option String × String))
  let ssrfSeenRef ← IO.mkRef false
  let startMock := startMockHttpServer fun method target hdrs body => do
    logRef.modify (·.push (method, target, getHeader? hdrs "content-type", getHeader? hdrs "idempotency-key", utf8Str body))
    let (pathOnly, queryStr) := splitPathQuery target
    if method == "POST" && pathOnly == "/v1/checkout/sessions" then return jsonStrResp 200 "{\"id\":\"cs_live_1\"}"
    else if method == "GET" && pathOnly == "/v1/customers" then return jsonStrResp 200 "{\"data\":[]}"
    else if method == "POST" && pathOnly == "/v1/projects/p1/secrets" && queryStr == "secretId=my-key" then return jsonStrResp 409 "{\"error\":\"ALREADY_EXISTS\"}"
    else if method == "POST" && pathOnly == "/v1/projects/p1/secrets/my-key:addVersion" then return jsonStrResp 200 "{\"name\":\"projects/p1/secrets/my-key/versions/1\"}"
    else return txtResp 404 s!"unexpected mock route: {method} {target}"
  withMockServer c "[svc-ext] start mock" startMock (·.2) fun (port, _) => do
    let baseInst := Native.mkNativeServerInst none none
    let envMap : List (String × String) := [("WEBHOOK_SECRET", "whsec_test_key_99"), ("STRIPE_API_KEY", "sk_test_123")]
    let srvInst := withMockEnvInst baseInst (fun v => pure (envMap.lookup v)) (onHttp? := some fun req => do
      if req.ssrfGuard then ssrfSeenRef.set true
      let target := if req.pathAndQuery.startsWith "/" then req.pathAndQuery else "/" ++ req.pathAndQuery
      let authHdrs := match req.auth with | .bearerSecret k => (envMap.lookup k).elim [] fun v => [("Authorization", "Bearer " ++ v)] | _ => []
      match ← httpReq port req.method target (authHdrs ++ req.headers).toArray req.body with
      | .error e => return .error (ApiError.internal e)
      | .ok r => return .ok { status := r.status.toUInt32, body := r.body })
    let _ ← (letI : MonadServer IO := srvInst; do
      let uuid ← Qed.Random.uuid
      let (parts, verChar, varChar) := (uuid.splitOn "-", uuid.toList[14]?, uuid.toList[19]?)
      c.check s!"[svc-ext] Random.uuid v4 valid format ({uuid})" (uuid.length == 36 && parts.map (·.length) == [8, 4, 4, 4, 12] && verChar == some '4' && varChar.any fun ch => ch == '8' || ch == '9' || ch == 'a' || ch == 'b')
      let (nowSec, payload) := (← Qed.Time.nowSec, "{\"type\":\"invoice.paid\"}")
      let oldTs := if nowSec > 900 then nowSec - 900 else 0
      let goodSig ← Qed.Crypto.hmacSha256Hex (Qed.Secret.ofString "whsec_test_key_99") s!"{nowSec}.{payload}"
      let oldSig ← Qed.Crypto.hmacSha256Hex (Qed.Secret.ofString "whsec_test_key_99") s!"{oldTs}.{payload}"
      let callHost (fn : String) (req : ByteArray) := @ServerChecks.ServiceHost.dispatchM IO _ srvInst {} fn req
      forList [("accepts valid HMAC within tolerance", s!"{nowSec},{goodSig}", true),
          ("rejects tampered HMAC (constEq)", s!"{nowSec},0000000000000000000000000000000000000000000000000000000000000000", false),
          ("rejects replayed timestamp outside tolerance", s!"{oldTs},{oldSig}", false)] fun (lbl, hdr, want) => do
        c.checkProto s!"[svc-ext] verifyWebhook {lbl}" (← callHost "verifyWebhook" (Qed.Proto.encode (payload, hdr))) want
      c.checkProto "[svc-ext] getOddToken proves ensures via prove: and returns 15" (← callHost "getOddToken" (Qed.Proto.encode (7 : Nat))) (15 : Nat)
      let checkoutReq : ServerChecks.StripeCheckoutReq := { mode := "payment", successUrl := "https://app.test/ok", quantity := 3, coupon := none }
      c.checkProtoBy (α := String) "[svc-ext] createCheckout sends Form(T) and returns cs_live_1" (← callHost "createCheckout" (Qed.Proto.encode checkoutReq)) (·.contains "cs_live_1") true
      c.expectOk "[svc-ext] StripeFormApi.createSession with Idempotency-Key" (← @ServerChecks.StripeFormApi.createSession IO _ srvInst (some "idem-42") checkoutReq) fun j =>
        c.check "[svc-ext] createSession response id" (j.render.contains "cs_live_1")
      c.expectOk "[svc-ext] StripeFormApi.listCustomers omits none query param" (← @ServerChecks.StripeFormApi.listCustomers IO _ srvInst none (some 25)) fun _ => pure ()
      c.checkProtoBy (α := String) "[svc-ext] rotateSecret accepts 409 on createSecret and hits {id}:addVersion" (← callHost "rotateSecret" (Qed.Proto.encode ("p1", ("my-key", "secret-val")))) (·.contains "versions/1") true
      let blockedRes ← @ServerChecks.GuardedLocalApi.ping IO _ baseInst
      let unguardedSeenRef ← IO.mkRef true
      let spyInst := withMockEnvInst baseInst (fun _ => pure none) (onHttp? := some fun req => do unguardedSeenRef.set req.ssrfGuard; return .ok { status := 200, body := "pong".toUTF8 })
      let _ ← @ServerChecks.UnguardedLocalApi.ping IO _ spyInst
      let logs ← logRef.get
      c.checkAll [
        ("[svc-ext] SecretManagerApi set ssrfGuard=true on OutboundReq", ← ssrfSeenRef.get),
        ("[svc-ext] default ssrf_guard blocks 127.0.0.1 with opt-out hint", match blockedRes with | .error e => e.message.contains "SSRF blocked:" && e.message.contains "add `ssrf_guard false` to `external GuardedLocalApi`" | .ok _ => false),
        ("[svc-ext] `ssrf_guard false` sets ssrfGuard=false on OutboundReq", !(← unguardedSeenRef.get)),
        ("[svc-ext] Form(T) sent application/x-www-form-urlencoded with URL-encoded body",
          logs.any fun (m, t, ct, _, b) => m == "POST" && t == "/v1/checkout/sessions" && ct == some "application/x-www-form-urlencoded" && b == "mode=payment&successUrl=https%3A%2F%2Fapp.test%2Fok&quantity=3"),
        ("[svc-ext] optional header Idempotency-Key omitted when none and sent when some",
          logs.any (fun (_, t, _, ik, _) => t == "/v1/checkout/sessions" && ik.isNone) && logs.any (fun (_, t, _, ik, _) => t == "/v1/checkout/sessions" && ik == some "idem-42")),
        ("[svc-ext] optional query param omitted when none (`?limit=25` only)", logs.any fun (m, t, _, _, _) => m == "GET" && t == "/v1/customers?limit=25")] : IO Unit)

private def runCloudBooksSuite (c : TestChecker) : IO Unit := do
  let tPem ← IO.asTask (prio := .dedicated) (runCmd "openssl" #["genpkey", "-algorithm", "RSA", "-pkeyopt", "rsa_keygen_bits:2048"])
  withDevApp c "Examples.CloudBooks" fun dir => do
    let (okPem, pemKey, pemErr) ← IO.ofExcept (← IO.wait tPem)
    if okPem != 0 then c.check "openssl generated test RSA key" false pemErr; return
    let tLeak ← IO.asTask (prio := .dedicated) (checkLeakGate c "Examples.CloudBooks" #["CloudBooks.Catalog.initState", "CloudBooks.Catalog.secrets", "CloudBooks.Catalog.dispatchM", "CloudBooks.Catalog.order_handler", "CloudBooks.CloudflareD1.secrets"])
    let (fcCode, _, fcErr) ← runCmd (dir ++ "/server") #[dir, "18999"] (env := #[("CF_D1_TOKEN", none), ("GCP_SA_JSON", none)])
    c.checkEq "fail-closed exit code without secrets" fcCode 1
    forList ["GCP_SA_JSON", "CF_D1_TOKEN"] fun secret => c.check s!"stderr mentions {secret}" (fcErr.contains secret) fcErr
    withMockServer c "startMockExternal" (startMockExternal pemKey) (·.2.2) fun (extBase, mockRef, _) => do
      let saJson := Qed.Json.render (.obj [("client_email", .str "qed-test@proj.iam.gserviceaccount.com"), ("private_key", .str pemKey), ("token_uri", .str s!"{extBase}/oauth2/token")])
      let (authSecret, prevSecret, nowSec) := ("super-secret-hmac-key", "previous-rotated-hmac-key", (← Prim.nowMs).toNat / 1000)
      let (validTok, validV1, rotatedV1, expiredV1) := (← signSessionToken authSecret "alice", ← signExpiringSessionToken authSecret "alice" (nowSec + 3600),
        ← signExpiringSessionToken prevSecret "alice" (nowSec + 3600), ← signExpiringSessionToken authSecret "alice" 1)
      let baseEnv : Array (String × Option String) := #[("QED_AUTH_SECRET", some authSecret), ("CF_D1_TOKEN", some "test-cf-d1-secret"), ("GCP_SA_JSON", some saJson),
        ("QED_GCP_TOKEN_URL", some s!"{extBase}/oauth2/token"), ("QED_EXT_GCPSTORAGE_BASE", some extBase), ("QED_EXT_CLOUDFLARED1_BASE", some extBase)]
      runTasks [
        withNativeServer c "native server healthy" dir (baseEnv ++ #[("QED_WORKERS", some "4"), ("QED_AUTH_SECRET_PREV", some prevSecret)]) (dev := true) fun srv => do
          forList [("HTTP/1.1 without Host rejected 400", "GET /_qed/health HTTP/1.1\r\nConnection: close\r\n\r\n"),
              ("HTTP/1.1 duplicate Host rejected 400", "GET /_qed/health HTTP/1.1\r\nHost: 127.0.0.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n"),
              ("whitespace before colon rejected 400", "GET /_qed/health HTTP/1.1\r\nHost: 127.0.0.1\r\nContent-Length : 0\r\nConnection: close\r\n\r\n")] fun (lbl, raw) =>
            c.checkRaw400 srv.port lbl raw
          c.checkRawNoLeak srv.port "path traversal never leaks lakefile.lean" "/../lakefile.lean" "lean_lib Qed"
          c.checkHttp "missing static asset" (← httpReq srv.port "GET" "/does-not-exist.js") (status? := some 404) (headers := [("x-content-type-options", some "nosniff")])
          withSymlink ((← IO.currentDir) / "lakefile.lean").toString s!"{dir}/escape.txt" do
            c.checkHttp "symlink escape check" (← httpReq srv.port "GET" "/escape.txt") (status? := some 404) (notContains := ["lean_lib Qed"])
          let postRpc (m : String) (body : ByteArray) (tok? : Option String := none) := httpRpc srv.port "Catalog" m body tok?
          let validV2 ← Qed.Auth.Oidc.signSessionCookieV2 authSecret { userId := "alice", claims := [("email_verified", "true")] } 3600
          let (ckHdr, sameOrig, orderReq) := (("Cookie", s!"qed_session={validV2}"), ("Origin", s!"http://127.0.0.1:{srv.port}"), fun idx qty : Nat => Qed.Proto.encode (idx, qty))
          let orderCk (tok : String) := httpRpc srv.port "Catalog" "order" (orderReq 0 99) none #[("Cookie", s!"qed_session={tok}"), sameOrig]
          c.checkStatusAll [
            ("RPC rejects cross-origin Origin with 403", httpRpc srv.port "Catalog" "list" ByteArray.empty none #[ckHdr, ("Origin", "https://evil.example.com")], 403),
            ("RPC rejects non-protobuf Content-Type with 415", httpReq srv.port "POST" "/_qed/rpc/Catalog/list" #[ckHdr, ("Content-Type", "text/plain")] "a=1".toUTF8, 415),
            ("RPC accepts same-origin protobuf with 200", httpRpc srv.port "Catalog" "list" ByteArray.empty none #[ckHdr, sameOrig, ("Sec-Fetch-Site", "same-origin")], 200),
            ("v1 bearer token in qed_session cookie rejected 401", orderCk validV1, 401),
            ("legacy HMAC token in qed_session cookie rejected 401", orderCk validTok, 401),
            ("v2 session cookie accepted in qed_session (hits requires 400)", orderCk validV2, 400),
            ("unauth order rejected 401", postRpc "order" (orderReq 0 1) none, 401),
            ("forged HMAC rejected 401", postRpc "order" (orderReq 0 1) (some ("alice." ++ String.ofList (List.replicate 64 '0'))), 401),
            ("v2 session cookie in Authorization Bearer rejected 401", postRpc "order" (orderReq 0 99) (some validV2), 401),
            ("expired v1 token rejected 401", postRpc "order" (orderReq 0 1) (some expiredV1), 401),
            ("requires qty <= 50 rejected 400", postRpc "order" (orderReq 0 99) (some validV1), 400),
            ("rotated QED_AUTH_SECRET_PREV accepted (hits requires 400)", postRpc "order" (orderReq 0 99) (some rotatedV1), 400)]
          let mintInst := withMockEnvInst (inferInstance : MonadServer IO) fun v => pure (if v == "QED_AUTH_SECRET" then some authSecret else none)
          match ← @Qed.Server.mintBearerToken IO _ mintInst "alice" 3600 "QED_AUTH_SECRET", ← @Qed.Server.mintBearerToken IO _ mintInst "alice" 3600 "QED_AUTH_SECRET" with
          | .ok t1, .ok t2 =>
              c.check "mintBearerToken emits distinct random-JTI v3 tokens in same second" (t1.startsWith "v3." && t2.startsWith "v3." && t1 != t2) s!"got {t1} vs {t2}"
              c.checkStatusAll [("v3 bearer token accepted in Authorization Bearer (hits requires 400)", postRpc "order" (orderReq 0 99) (some t1), 400),
                ("v3 bearer token in qed_session cookie rejected 401", orderCk t1, 401)]
          | e1, e2 => c.check "mintBearerToken succeeded" false s!"{repr e1} / {repr e2}"
          let pngBytes := ByteArray.mk #[0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a, 0x00, 0xff, 0x42]
          c.checkHttp "addBook RPC" (← postRpc "addBook" (Qed.Proto.encode ("plfa", ("Programming Language Foundations", ((5 : Nat), pngBytes)))) (some validTok)) (headers := [("content-type", some "application/x-protobuf")])
          let st1 ← mockRef.get
          c.checkAll [("GCP RS256 JWT signature verified", st1.rsaVerified), ("GCP token exchanged once on upload", st1.tokenExchanges == 1), ("GCS received exact raw PNG bytes", st1.gcsObjects["covers/plfa.png"]? == some pngBytes)]
          c.checkHttp "cover RPC" (← postRpc "cover" (Qed.Proto.encode "plfa.png")) (extra := fun r => c.checkEq "cover round-tripped exact binary PNG" (Qed.Proto.decode (α := ByteArray) r.body) (.ok pngBytes))
          let st2 ← mockRef.get
          c.checkAll [(":key* preserved literal / in download path", st2.sawUnescaped), ("StateBox OAuth2 cache reused token without re-exchange", st2.tokenExchanges == 1)]
          mockRef.modify fun s => { s with failD1 := true }
          c.checkStatus "order succeeds via catch fallback on D1 500" (← postRpc "order" (orderReq 0 1) (some validTok)) 200
          mockRef.modify fun s => { s with failD1 := false }
          c.check "all 8 concurrent orders returned 200" (← runParallelAll 8 do return match ← postRpc "order" (orderReq 0 1) (some validTok) with | .ok r => r.status == 200 | .error _ => false)
          c.checkEq "Cloudflare D1 received all 9 order queries" (← mockRef.get).d1Count 9
          let rawSsrRef ← IO.mkRef ""
          c.checkHttp "native SSR GET /" (← httpReq srv.port "GET" "/" #[ckHdr]) (contains := ["id=\"qed-state\""])
            (extra := fun r => do r.checkDefaultCsp c "SSR HTML includes strict default Content-Security-Policy"; rawSsrRef.set r.bodyStr)
          checkGzipResp c "SSR gzip GET /" (← httpReq srv.port "GET" "/" #[ckHdr, ("Accept-Encoding", "gzip")]) (← rawSsrRef.get),
        withNativeServer c "rate-limited server healthy" dir (baseEnv ++ #[("QED_WORKERS", some "2"), ("QED_RATE_LIMIT_RPS", some "1"), ("QED_RATE_LIMIT_BURST", some "2"), ("QED_CSP", some "default-src 'none'")]) (dev := true) fun srvRl => do
          let rlAll ← (List.range 4).mapM fun _ => httpReq srvRl.port "GET" "/"
          c.checkHttp "rate-limit req 1" rlAll[0]! (headers := [("content-security-policy", some "default-src 'none'")])
          c.checkStatus "rate-limit req 2 allowed (200)" rlAll[1]! 200
          let rlResps := (rlAll.drop 2).filterMap Except.toOption
          c.checkAll [("burst excess rejected with 429 Too Many Requests", rlResps.any (·.status == 429)),
            ("429 response includes Retry-After header", rlResps.any fun r => r.status == 429 && (r.header? "retry-after").isSome)]]
    if let .error e ← IO.wait tLeak then throw e

def run : IO Bool := do
  let c ← mkChecker "fullstack-rpc"
  runTasks [runCloudBooksSuite c, runWebEssentialsSuite c, runServiceAndExternalSuite c, runMovedServerChecks c]
  c.finish

end QedTests.Native.FullstackRpc
