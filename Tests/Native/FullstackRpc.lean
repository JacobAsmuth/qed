import Tests.Native.Harness
import Examples.CloudBooks
import Tests.ServerChecks
import Qed.Server.Native
open System (FilePath)
open Qed.Server Qed.Server.Http

namespace Tests.Native.FullstackRpc

structure MockExtState where
  tokenExchanges : Nat := 0
  rsaVerified    : Bool := false
  sawUnescaped   : Bool := false
  failD1         : Bool := false
  gcsObjects     : Std.HashMap String ByteArray := {}
  d1Count        : Nat := 0

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

private def runWebEssentialsSuite (c : TestChecker) : IO Unit :=
  withDevApp c "Tests.WebEssentialsFixture" fun dir => do
    let jsContent := String.join (List.replicate 40 "export function qedHello(x) { return 'hello-' + x; }\n")
    let hashedFile := s!"{dir}/bundle.deadbeef.mjs"; IO.FS.writeFile hashedFile jsContent
    let authSecret := "web-essentials-hmac-secret"; let aliceTok ← signSessionToken authSecret "alice"
    try
      withNativeServer c "[web-essentials] child native server healthy" dir #[("QED_WORKERS", some "2"), ("QED_AUTH_SECRET", some authSecret)] (dev := false) fun srv => do
        for pass in [1, 2] do checkGzipResp c s!"[web-essentials] hashed JS gzip pass {pass}" (← httpReq srv.port "GET" "/bundle.deadbeef.mjs" #[("Accept-Encoding", "gzip")]) jsContent
        c.checkHttp "[web-essentials] hashed JS plain" (← httpReq srv.port "GET" "/bundle.deadbeef.mjs") (headers := [("content-encoding", none)]) (bodyEq? := some jsContent)
        c.checkHttp "[web-essentials] GET /robots.txt" (← httpReq srv.port "GET" "/robots.txt") (bodyEq? := some "User-agent: *\nAllow: /\n")
        c.checkStatus "[web-essentials] unauth POST /webhook rejected 401" (← httpReq srv.port "POST" "/webhook" #[] "{}".toUTF8) 401
        for (lbl, path, hdrs, body, cLbl, ckFlags) in [
            ("auth POST /webhook", "/webhook", #[("Authorization", s!"Bearer {aliceTok}")], "{}", "auth POST /webhook emitted Set-Cookie wh_seen=1", ["wh_seen=1", "HttpOnly", "SameSite=Lax"]),
            ("POST /echo-cookie", "/echo-cookie", #[], "val123\r\nX-Inject: bad", "POST /echo-cookie emitted sanitized HttpOnly SameSite=Lax cookie", ["echo_ck=val123X-Inject: bad", "HttpOnly", "SameSite=Lax"])] do
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

def run : IO Bool := do
  let c ← mkChecker "fullstack-rpc"
  withDevApp c "Examples.CloudBooks" fun dir => do
    checkLeakGate c "Examples.CloudBooks" #["CloudBooks.Catalog.initState", "CloudBooks.Catalog.secrets", "CloudBooks.Catalog.dispatchM", "CloudBooks.Catalog.order_handler", "CloudBooks.CloudflareD1.secrets"]
    let (fcCode, _, fcErr) ← runCmd (dir ++ "/server") #[dir, "18999"] (env := #[("CF_D1_TOKEN", none), ("GCP_SA_JSON", none)])
    c.checkEq "fail-closed exit code without secrets" fcCode 1
    for secret in ["GCP_SA_JSON", "CF_D1_TOKEN"] do c.check s!"stderr mentions {secret}" (fcErr.contains secret) fcErr
    let (okPem, pemKey, pemErr) ← runCmd "openssl" #["genpkey", "-algorithm", "RSA", "-pkeyopt", "rsa_keygen_bits:2048"]
    if okPem != 0 then c.check "openssl generated test RSA key" false pemErr; return
    withMockServer c "startMockExternal" (startMockExternal pemKey) (·.2.2) fun (extBase, mockRef, _) => do
      let saJson := Qed.Json.render (.obj [("client_email", .str "qed-test@proj.iam.gserviceaccount.com"), ("private_key", .str pemKey), ("token_uri", .str s!"{extBase}/oauth2/token")])
      let (authSecret, prevSecret, nowSec) := ("super-secret-hmac-key", "previous-rotated-hmac-key", (← Prim.nowMs).toNat / 1000)
      let (validTok, validV1, rotatedV1, expiredV1) := (← signSessionToken authSecret "alice", ← signExpiringSessionToken authSecret "alice" (nowSec + 3600),
        ← signExpiringSessionToken prevSecret "alice" (nowSec + 3600), ← signExpiringSessionToken authSecret "alice" 1)
      let baseEnv : Array (String × Option String) := #[("QED_AUTH_SECRET", some authSecret), ("CF_D1_TOKEN", some "test-cf-d1-secret"), ("GCP_SA_JSON", some saJson),
        ("QED_GCP_TOKEN_URL", some s!"{extBase}/oauth2/token"), ("QED_EXT_GCPSTORAGE_BASE", some extBase), ("QED_EXT_CLOUDFLARED1_BASE", some extBase)]
      withNativeServer c "native server healthy" dir (baseEnv ++ #[("QED_WORKERS", some "4"), ("QED_AUTH_SECRET_PREV", some prevSecret)]) (dev := true) fun srv => do
        for (lbl, raw) in [("HTTP/1.1 without Host rejected 400", "GET /_qed/health HTTP/1.1\r\nConnection: close\r\n\r\n"),
            ("HTTP/1.1 duplicate Host rejected 400", "GET /_qed/health HTTP/1.1\r\nHost: 127.0.0.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n"),
            ("whitespace before colon rejected 400", "GET /_qed/health HTTP/1.1\r\nHost: 127.0.0.1\r\nContent-Length : 0\r\nConnection: close\r\n\r\n")] do
          c.checkRaw400 srv.port lbl raw
        c.checkRawNoLeak srv.port "path traversal never leaks lakefile.lean" "/../lakefile.lean" "lean_lib Qed"
        c.checkHttp "missing static asset" (← httpReq srv.port "GET" "/does-not-exist.js") (status? := some 404) (headers := [("x-content-type-options", some "nosniff")])
        withSymlink ((← IO.currentDir) / "lakefile.lean").toString s!"{dir}/escape.txt" do
          c.checkHttp "symlink escape check" (← httpReq srv.port "GET" "/escape.txt") (status? := some 404) (notContains := ["lean_lib Qed"])
        let postRpc (m : String) (body : ByteArray) (tok? : Option String := none) := httpRpc srv.port "Catalog" m body tok?
        let ckHdr := ("Cookie", s!"qed_session={validTok}")
        c.checkStatus "RPC rejects cross-origin Origin with 403" (← httpRpc srv.port "Catalog" "list" ByteArray.empty none #[ckHdr, ("Origin", "https://evil.example.com")]) 403
        c.checkStatus "RPC rejects non-protobuf Content-Type with 415" (← httpReq srv.port "POST" "/_qed/rpc/Catalog/list" #[ckHdr, ("Content-Type", "text/plain")] "a=1".toUTF8) 415
        c.checkStatus "RPC accepts same-origin protobuf with 200" (← httpRpc srv.port "Catalog" "list" ByteArray.empty none #[ckHdr, ("Origin", s!"http://127.0.0.1:{srv.port}"), ("Sec-Fetch-Site", "same-origin")]) 200
        let orderReq (idx qty : Nat) := Qed.Proto.encode (idx, qty)
        for (lbl, req, tok?, want) in [("unauth order rejected 401", orderReq 0 1, none, 401), ("forged HMAC rejected 401", orderReq 0 1, some ("alice." ++ String.ofList (List.replicate 64 '0')), 401),
            ("expired v1 token rejected 401", orderReq 0 1, some expiredV1, 401), ("requires qty <= 50 rejected 400", orderReq 0 99, some validV1, 400),
            ("rotated QED_AUTH_SECRET_PREV accepted (hits requires 400)", orderReq 0 99, some rotatedV1, 400)] do
          c.checkStatus lbl (← postRpc "order" req tok?) want
        let pngBytes := ByteArray.mk #[0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a, 0x00, 0xff, 0x42]
        c.checkHttp "addBook RPC" (← postRpc "addBook" (Qed.Proto.encode ("plfa", ("Programming Language Foundations", ((5 : Nat), pngBytes)))) (some validTok)) (headers := [("content-type", some "application/x-protobuf")])
        let st1 ← mockRef.get
        c.check "GCP RS256 JWT signature verified" st1.rsaVerified
        c.checkEq "GCP token exchanged once on upload" st1.tokenExchanges 1
        c.checkEq "GCS received exact raw PNG bytes" (st1.gcsObjects["covers/plfa.png"]?) (some pngBytes)
        c.checkHttp "cover RPC" (← postRpc "cover" (Qed.Proto.encode "plfa.png")) (extra := fun r => c.checkEq "cover round-tripped exact binary PNG" (Qed.Proto.decode (α := ByteArray) r.body) (.ok pngBytes))
        let st2 ← mockRef.get
        c.check ":key* preserved literal / in download path" st2.sawUnescaped
        c.checkEq "StateBox OAuth2 cache reused token without re-exchange" st2.tokenExchanges 1
        mockRef.modify fun s => { s with failD1 := true }
        c.checkStatus "order succeeds via catch fallback on D1 500" (← postRpc "order" (orderReq 0 1) (some validTok)) 200
        mockRef.modify fun s => { s with failD1 := false }
        c.check "all 8 concurrent orders returned 200" (← runParallelAll 8 do return match ← postRpc "order" (orderReq 0 1) (some validTok) with | .ok r => r.status == 200 | .error _ => false)
        c.checkEq "Cloudflare D1 received all 9 order queries" (← mockRef.get).d1Count 9
        let rawSsrRef ← IO.mkRef ""
        c.checkHttp "native SSR GET /" (← httpReq srv.port "GET" "/" #[ckHdr]) (contains := ["id=\"qed-state\""])
          (extra := fun r => do r.checkDefaultCsp c "SSR HTML includes strict default Content-Security-Policy"; rawSsrRef.set r.bodyStr)
        checkGzipResp c "SSR gzip GET /" (← httpReq srv.port "GET" "/" #[ckHdr, ("Accept-Encoding", "gzip")]) (← rawSsrRef.get)
      withNativeServer c "rate-limited server healthy" dir (baseEnv ++ #[("QED_WORKERS", some "2"), ("QED_RATE_LIMIT_RPS", some "1"), ("QED_RATE_LIMIT_BURST", some "2"), ("QED_CSP", some "default-src 'none'")]) (dev := true) fun srvRl => do
        let rlAll ← (List.range 4).mapM fun _ => httpReq srvRl.port "GET" "/"
        c.checkHttp "rate-limit req 1" rlAll[0]! (headers := [("content-security-policy", some "default-src 'none'")])
        c.checkStatus "rate-limit req 2 allowed (200)" rlAll[1]! 200
        let rlResps := (rlAll.drop 2).filterMap Except.toOption
        c.check "burst excess rejected with 429 Too Many Requests" (rlResps.any (·.status == 429))
        c.check "429 response includes Retry-After header" (rlResps.any fun r => r.status == 429 && (r.header? "retry-after").isSome)
    runWebEssentialsSuite c
  c.finish

end Tests.Native.FullstackRpc
