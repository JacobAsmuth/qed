import Tests.Native.Harness
import Examples.CloudBooks
import Tests.ServerChecks
import Qed.Server.Native

open System (FilePath)
open Qed.Server
open Qed.Server.Http

namespace Tests.Native.FullstackRpc

private def decodeBase64Url (s : String) : ByteArray :=
  let std := (s.replace "-" "+").replace "_" "/"
  let pad := (4 - std.length % 4) % 4
  let padded := std ++ String.ofList (List.replicate pad '=')
  let valOf (c : Char) : Nat :=
    let n := c.toNat
    if 65 ≤ n && n ≤ 90 then n - 65
    else if 97 ≤ n && n ≤ 122 then n - 71
    else if 48 ≤ n && n ≤ 57 then n + 4
    else if c == '+' then 62
    else if c == '/' then 63
    else 255
  Id.run do
    let cs := padded.toList.toArray
    let mut out := ByteArray.empty
    let mut i := 0
    while i + 3 < cs.size do
      let c0 := valOf cs[i]!
      let c1 := valOf cs[i + 1]!
      let c2 := valOf cs[i + 2]!
      let c3 := valOf cs[i + 3]!
      if c0 < 64 && c1 < 64 then
        out := out.push (UInt8.ofNat ((c0 <<< 2) ||| (c1 >>> 4)))
        if cs[i + 2]! != '=' && c2 < 64 then
          out := out.push (UInt8.ofNat (((c1 &&& 0xF) <<< 4) ||| (c2 >>> 2)))
          if cs[i + 3]! != '=' && c3 < 64 then
            out := out.push (UInt8.ofNat (((c2 &&& 0x3) <<< 6) ||| c3))
      i := i + 4
    return out

private def urlDecodeForm (s : String) : String :=
  let s := s.replace "+" " "
  let cs := s.toList.toArray
  let hexVal (c : Char) : Option Nat :=
    let n := c.toNat
    if 48 ≤ n && n ≤ 57 then some (n - 48)
    else if 65 ≤ n && n ≤ 70 then some (n - 55)
    else if 97 ≤ n && n ≤ 102 then some (n - 87)
    else none
  Id.run do
    let mut bs := ByteArray.empty
    let mut i := 0
    while i < cs.size do
      if cs[i]! == '%' && i + 2 < cs.size then
        match hexVal cs[i + 1]!, hexVal cs[i + 2]! with
        | some h1, some h2 =>
            bs := bs.push (UInt8.ofNat (h1 * 16 + h2))
            i := i + 3
        | _, _ =>
            bs := bs.push (UInt8.ofNat cs[i]!.toNat)
            i := i + 1
      else
        bs := bs.push (UInt8.ofNat cs[i]!.toNat)
        i := i + 1
    return (String.fromUTF8? bs).getD s

structure MockExtState where
  tokenExchanges : Nat := 0
  rsaVerified    : Bool := false
  sawUnescaped   : Bool := false
  failD1         : Bool := false
  gcsObjects     : Std.HashMap String ByteArray := {}
  d1Count        : Nat := 0

private def startMockExternal (pemKey : String) :
    IO (Except String (String × IO.Ref MockExtState × IO Unit)) := do
  match ← Prim.tcpListen 0 with
  | .error e => return .error e
  | .ok (lid, port) =>
      let stRef ← IO.mkRef ({} : MockExtState)
      let runningRef ← IO.mkRef true
      let _ ← IO.asTask (prio := .dedicated) do
        while ← runningRef.get do
          match ← Prim.tcpAccept lid 100 with
          | .error "timeout" => pure ()
          | .error _ => break
          | .ok conn =>
              try
                if let some (method, target, hdrs, body) ← readOneHttpReq conn then
                  let authHdr := (hdrs.find? fun (k, _) => k.toLower == "authorization").map Prod.snd |>.getD ""
                  let (pathOnly, queryStr) := match target.splitOn "?" with
                    | p :: q :: _ => (p, q)
                    | _           => (target, "")
                  let (status, ctype, respBytes) ← do
                    if method == "POST" && pathOnly == "/oauth2/token" then
                      let form := (String.fromUTF8? body).getD ""
                      let mut assertion := ""
                      for pair in form.splitOn "&" do
                        match pair.splitOn "=" with
                        | ["assertion", v] => assertion := urlDecodeForm v
                        | _ => pure ()
                      match assertion.splitOn "." with
                      | [p0, p1, p2] =>
                          let sigBytes := decodeBase64Url p2
                          let okSig ← Prim.rsaSha256Verify pemKey (s!"{p0}.{p1}").toUTF8 sigBytes
                          let claimsStr := (String.fromUTF8? (decodeBase64Url p1)).getD ""
                          if okSig && claimsStr.contains "qed-test@proj.iam.gserviceaccount.com" &&
                             claimsStr.contains "devstorage.read_write" then
                            stRef.modify fun s => { s with rsaVerified := true, tokenExchanges := s.tokenExchanges + 1 }
                            pure (200, "application/json", "{\"access_token\":\"mock-gcs-token-777\",\"expires_in\":3600}".toUTF8)
                          else
                            pure (401, "application/json", "{\"error\":\"invalid_grant\"}".toUTF8)
                      | _ => pure (401, "application/json", "{\"error\":\"invalid_grant\"}".toUTF8)
                    else if pathOnly.startsWith "/upload/storage/v1/b/" || pathOnly.startsWith "/storage/v1/b/" then
                      if authHdr != "Bearer mock-gcs-token-777" then
                        pure (401, "text/plain", "unauthorized gcs".toUTF8)
                      else if method == "POST" && pathOnly == "/upload/storage/v1/b/qed-covers/o" then
                        let mut name := ""
                        for pair in queryStr.splitOn "&" do
                          match pair.splitOn "=" with
                          | ["name", v] => name := urlDecodeForm v
                          | _ => pure ()
                        stRef.modify fun s => { s with gcsObjects := s.gcsObjects.insert name body }
                        pure (200, "application/json", s!"\{\"name\":\"{name}\",\"size\":{body.size}}".toUTF8)
                      else if method == "GET" && pathOnly.startsWith "/storage/v1/b/qed-covers/o/" then
                        if target.contains "/o/covers/" then
                          stRef.modify fun s => { s with sawUnescaped := true }
                        let key := String.ofList (pathOnly.toList.drop "/storage/v1/b/qed-covers/o/".length)
                        let st ← stRef.get
                        match st.gcsObjects[key]? with
                        | some stored => pure (200, "application/octet-stream", stored)
                        | none => pure (404, "text/plain", "object not found".toUTF8)
                      else pure (404, "text/plain", "unknown gcs".toUTF8)
                    else if method == "POST" && pathOnly == "/accounts/demo-account/d1/database/demo-db/query" then
                      if authHdr != "Bearer test-cf-d1-secret" then
                        pure (401, "text/plain", "unauthorized d1".toUTF8)
                      else
                        let st ← stRef.get
                        stRef.modify fun s => { s with d1Count := s.d1Count + 1 }
                        if st.failD1 then
                          pure (500, "application/json", "{\"success\":false,\"error\":\"simulated D1 outage\"}".toUTF8)
                        else
                          pure (200, "application/json", "{\"success\":true}".toUTF8)
                    else
                      pure (404, "text/plain", s!"unknown mock route: {target}".toUTF8)
                  let wire := formatHttpResponse status ctype respBytes false false true
                  discard <| Prim.outboundWriteAll conn wire
              catch _ => pure ()
              Prim.outboundRelease conn 0
      return .ok (s!"http://127.0.0.1:{port}", stRef, do runningRef.set false; Prim.tcpCloseListener lid)

private def gunzipBytes (gz : ByteArray) : IO (Except String ByteArray) := do
  let tmp ← makeTempDir "qed-gz-test"
  try
    let gzFile := s!"{tmp}/in.gz"
    let outFile := s!"{tmp}/out.bin"
    IO.FS.writeBinFile gzFile gz
    let (code, _, err) ← runCmd "sh" #["-c", s!"gzip -dc '{gzFile}' > '{outFile}'"]
    if code != 0 then
      return .error s!"gzip -dc failed ({code}): {err}"
    let raw ← IO.FS.readBinFile outFile
    return .ok raw
  finally
    rmRf tmp

private def runWebEssentialsSuite (c : TestChecker) : IO Unit := do
  let some dir ← buildDevApp "Tests.WebEssentialsFixture"
    | c.check "[web-essentials] buildDevApp Tests.WebEssentialsFixture" false; return

  -- Write a content-hashed JS asset (> 256 bytes, compressible) to test CachedStaticAsset gzip cache
  let jsContent := String.join (List.replicate 40 "export function qedHello(x) { return 'hello-' + x; }\n")
  let hashedFile := s!"{dir}/bundle.deadbeef.mjs"
  IO.FS.writeFile hashedFile jsContent
  let authSecret := "web-essentials-hmac-secret"
  let aliceTok ← signSessionToken authSecret "alice"
  let (srv, ready) ← startNativeServer dir #[
    ("QED_WORKERS", some "2"),
    ("QED_AUTH_SECRET", some authSecret)
  ] (dev := false)
  try
    c.check "[web-essentials] child native server healthy" ready
    if !ready then return

    -- 1. CachedStaticAsset pre-compressed gzip (first request fills cache, second hits cache)
    for pass in [1, 2] do
      match ← httpReq srv.port "GET" "/bundle.deadbeef.mjs" #[("Accept-Encoding", "gzip")] with
      | .ok r =>
          c.checkEq s!"[web-essentials] hashed JS gzip pass {pass} status 200" r.status 200
          c.checkEq s!"[web-essentials] hashed JS gzip pass {pass} Content-Encoding" (r.header? "content-encoding") (some "gzip")
          c.checkEq s!"[web-essentials] hashed JS gzip pass {pass} Vary" (r.header? "vary") (some "Accept-Encoding")
          c.check s!"[web-essentials] hashed JS gzip pass {pass} smaller than raw ({r.body.size} < {jsContent.utf8ByteSize})"
            (r.body.size < jsContent.utf8ByteSize)
          match ← gunzipBytes r.body with
          | .ok raw => c.checkEq s!"[web-essentials] hashed JS gzip pass {pass} decompresses identically" (String.fromUTF8? raw) (some jsContent)
          | .error e => c.check s!"[web-essentials] gunzip pass {pass}" false e
      | .error e => c.check s!"[web-essentials] hashed JS gzip pass {pass}" false e

    -- Without Accept-Encoding: gzip, serves uncompressed asset with Vary: Accept-Encoding
    match ← httpReq srv.port "GET" "/bundle.deadbeef.mjs" with
    | .ok r =>
        c.checkEq "[web-essentials] hashed JS plain status 200" r.status 200
        c.checkEq "[web-essentials] hashed JS plain no Content-Encoding" (r.header? "content-encoding") none
        c.checkEq "[web-essentials] hashed JS plain body exact" r.bodyStr jsContent
    | .error e => c.check "[web-essentials] hashed JS plain" false e

    -- 2. Custom HTTP routes: GET /robots.txt, POST /webhook (401 unauth, 200 auth + Set-Cookie), POST /echo-cookie
    match ← httpReq srv.port "GET" "/robots.txt" with
    | .ok r =>
        c.checkEq "[web-essentials] GET /robots.txt status 200" r.status 200
        c.checkEq "[web-essentials] GET /robots.txt body" r.bodyStr "User-agent: *\nAllow: /\n"
    | .error e => c.check "[web-essentials] GET /robots.txt" false e

    match ← httpReq srv.port "POST" "/webhook" #[] "{}".toUTF8 with
    | .ok r => c.checkEq "[web-essentials] unauth POST /webhook rejected 401" r.status 401
    | .error e => c.check "[web-essentials] POST /webhook unauth" false e

    match ← httpReq srv.port "POST" "/webhook" #[("Authorization", s!"Bearer {aliceTok}")] "{}".toUTF8 with
    | .ok r =>
        c.checkEq "[web-essentials] auth POST /webhook status 200" r.status 200
        c.checkEq "[web-essentials] auth POST /webhook JSON body" r.bodyStr "{\"ok\":true}"
        let sc := (r.header? "set-cookie").getD ""
        c.check "[web-essentials] auth POST /webhook emitted Set-Cookie wh_seen=1"
          (sc.contains "wh_seen=1" && sc.contains "HttpOnly" && sc.contains "SameSite=Lax") sc
    | .error e => c.check "[web-essentials] POST /webhook auth" false e

    match ← httpReq srv.port "POST" "/echo-cookie" #[] "val123\r\nX-Inject: bad".toUTF8 with
    | .ok r =>
        c.checkEq "[web-essentials] POST /echo-cookie status 200" r.status 200
        c.checkEq "[web-essentials] POST /echo-cookie JSON body" r.bodyStr "{\"ok\":true}"
        let sc := (r.header? "set-cookie").getD ""
        c.check "[web-essentials] POST /echo-cookie emitted sanitized HttpOnly SameSite=Lax cookie"
          (sc.contains "echo_ck=val123X-Inject: bad" && sc.contains "HttpOnly" && sc.contains "SameSite=Lax") sc
    | .error e => c.check "[web-essentials] POST /echo-cookie" false e

    -- 3. RPC `setCookie(...)` emits Set-Cookie header on Protobuf response
    match ← httpReq srv.port "POST" "/_qed/rpc/WebEssentialsSrv/login"
      #[("Content-Type", "application/x-protobuf")] (Qed.Proto.encode "sess_tok_42") with
    | .ok r =>
        c.checkEq "[web-essentials] RPC login status 200" r.status 200
        c.checkEq "[web-essentials] RPC login payload" (Qed.Proto.decode (α := String) r.body) (.ok "ok")
        let sc := (r.header? "set-cookie").getD ""
        c.check "[web-essentials] RPC login emitted Set-Cookie qed_session"
          (sc.contains "qed_session=sess_tok_42" && sc.contains "HttpOnly" && sc.contains "SameSite=Lax") sc
    | .error e => c.check "[web-essentials] RPC login" false e

    -- 4. Server-side SSE streaming route (`stream "/events"`)
    match ← httpReq srv.port "GET" "/events" with
    | .ok r =>
        c.checkEq "[web-essentials] GET /events SSE status 200" r.status 200
        c.checkEq "[web-essentials] GET /events Content-Type" (r.header? "content-type") (some "text/event-stream; charset=utf-8")
        c.checkEq "[web-essentials] GET /events Cache-Control" (r.header? "cache-control") (some "no-cache")
        c.checkEq "[web-essentials] GET /events SSE wire format" r.bodyStr
          "event: greeting\nid: 1\ndata: hello\n\ndata: world\n\n"
    | .error e => c.check "[web-essentials] GET /events SSE" false e

    -- 5. Per-route `<head>` metadata, XSS escaping, CSP header & SSR HTTP status codes (200 / 404 / 302)
    match ← httpReq srv.port "GET" "/" with
    | .ok r =>
        c.checkEq "[web-essentials] SSR GET / status 200" r.status 200
        c.check "[web-essentials] SSR GET / escaped title XSS"
          (r.bodyStr.contains "<title>Home &lt;/title&gt;&lt;script&gt;alert(1)&lt;/script&gt;</title>" &&
           !r.bodyStr.contains "<script>alert(1)</script>")
        c.check "[web-essentials] SSR GET / meta description & canonical"
          (r.bodyStr.contains "<meta name=\"description\" content=\"Verified &quot;SSR&quot; &lt;head&gt;\">" &&
           r.bodyStr.contains "<link rel=\"canonical\" href=\"https://example.com/\">")
        let csp := (r.header? "content-security-policy").getD ""
        c.check "[web-essentials] SSR GET / has strict default CSP"
          (csp.contains "default-src 'self'" && csp.contains "script-src 'self'" && csp.contains "object-src 'none'") csp
    | .error e => c.check "[web-essentials] SSR GET /" false e

    match ← httpReq srv.port "GET" "/missing" with
    | .ok r =>
        c.checkEq "[web-essentials] SSR GET /missing returns HTTP 404" r.status 404
        c.check "[web-essentials] SSR GET /missing renders 404 <title>" (r.bodyStr.contains "<title>404 Not Found</title>")
    | .error e => c.check "[web-essentials] SSR GET /missing" false e

    match ← httpReq srv.port "GET" "/old" with
    | .ok r =>
        c.checkEq "[web-essentials] SSR GET /old returns HTTP 302" r.status 302
        c.checkEq "[web-essentials] SSR GET /old sets Location: /new" (r.header? "location") (some "/new")
    | .error e => c.check "[web-essentials] SSR GET /old" false e
  finally
    srv.stop
    rmRf hashedFile

def run : IO Bool := do
  let c ← mkChecker "fullstack-rpc"
  let some dir ← buildDevApp "Examples.CloudBooks"
    | c.check "buildDevApp Examples.CloudBooks" false; return ← c.finish

  -- 1. Client bundle server-leak gate
  checkLeakGate c "Examples.CloudBooks" #[
    "CloudBooks.Catalog.initState",
    "CloudBooks.Catalog.secrets",
    "CloudBooks.Catalog.dispatchM",
    "CloudBooks.Catalog.order_handler",
    "CloudBooks.CloudflareD1.secrets"
  ]

  -- 2. Fail-closed startup secret check
  let (fcCode, _, fcErr) ← runCmd (dir ++ "/server") #[dir, "18999"]
    (env := #[("CF_D1_TOKEN", none), ("GCP_SA_JSON", none)])
  c.checkEq "fail-closed exit code without secrets" fcCode 1
  c.check "stderr mentions GCP_SA_JSON" (fcErr.contains "GCP_SA_JSON") fcErr
  c.check "stderr mentions CF_D1_TOKEN" (fcErr.contains "CF_D1_TOKEN") fcErr

  -- 3. Generate ephemeral 2048-bit RSA keypair via openssl & launch native mock external server
  let (okPem, pemKey, pemErr) ← runCmd "openssl" #["genpkey", "-algorithm", "RSA", "-pkeyopt", "rsa_keygen_bits:2048"]
  if okPem != 0 then
    c.check "openssl generated test RSA key" false pemErr
    return ← c.finish

  match ← startMockExternal pemKey with
  | .error e => c.check "startMockExternal" false e; return ← c.finish
  | .ok (extBase, mockRef, stopMock) =>
      try
        let saJson := Qed.Json.render (.obj [
          ("client_email", .str "qed-test@proj.iam.gserviceaccount.com"),
          ("private_key", .str pemKey),
          ("token_uri", .str s!"{extBase}/oauth2/token")
        ])
        let authSecret := "super-secret-hmac-key"
        let prevSecret := "previous-rotated-hmac-key"
        let validTok ← signSessionToken authSecret "alice"
        let nowSec := (← Prim.nowMs).toNat / 1000
        let validV1 ← signExpiringSessionToken authSecret "alice" (nowSec + 3600)
        let rotatedV1 ← signExpiringSessionToken prevSecret "alice" (nowSec + 3600)
        let expiredV1 ← signExpiringSessionToken authSecret "alice" 1

        let (srv, healthy) ← startNativeServer dir #[
          ("QED_WORKERS", some "4"),
          ("QED_AUTH_SECRET", some authSecret),
          ("QED_AUTH_SECRET_PREV", some prevSecret),
          ("CF_D1_TOKEN", some "test-cf-d1-secret"),
          ("GCP_SA_JSON", some saJson),
          ("QED_GCP_TOKEN_URL", some s!"{extBase}/oauth2/token"),
          ("QED_EXT_GCPSTORAGE_BASE", some extBase),
          ("QED_EXT_CLOUDFLARED1_BASE", some extBase)
        ]
        try
          c.check "native server healthy" healthy

          -- 4. RFC 9112 smuggling, traversal, symlink escape, CSRF
          let checkRaw400 (lbl raw : String) : IO Unit := do
            match ← rawTcpReq srv.port raw.toUTF8 with
            | .ok resp => c.check lbl (((String.fromUTF8? resp).getD "").startsWith "HTTP/1.1 400 ")
            | .error e => c.check lbl false e
          checkRaw400 "HTTP/1.1 without Host rejected 400" "GET /_qed/health HTTP/1.1\r\nConnection: close\r\n\r\n"
          checkRaw400 "HTTP/1.1 duplicate Host rejected 400" "GET /_qed/health HTTP/1.1\r\nHost: 127.0.0.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n"
          checkRaw400 "whitespace before colon rejected 400" "GET /_qed/health HTTP/1.1\r\nHost: 127.0.0.1\r\nContent-Length : 0\r\nConnection: close\r\n\r\n"

          match ← rawTcpReq srv.port "GET /../lakefile.lean HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n".toUTF8 with
          | .ok resp => c.check "path traversal never leaks lakefile.lean" (!(((String.fromUTF8? resp).getD "").contains "lean_lib Qed"))
          | .error e => c.check "path traversal test" false e

          match ← httpReq srv.port "GET" "/does-not-exist.js" with
          | .ok r =>
              c.checkEq "missing static asset returns 404" r.status 404
              c.checkEq "nosniff header present" (r.header? "x-content-type-options") (some "nosniff")
          | .error e => c.check "missing static asset" false e

          let cwd ← IO.currentDir
          let escLink := s!"{dir}/escape.txt"
          rmRf escLink
          discard <| runCmd "ln" #["-s", (cwd / "lakefile.lean").toString, escLink]
          try
            match ← httpReq srv.port "GET" "/escape.txt" with
            | .ok r =>
                c.checkEq "symlink inside staticDir returns 404" r.status 404
                c.check "symlink blocked by openat2/O_NOFOLLOW" (!r.bodyStr.contains "lean_lib Qed")
            | .error e => c.check "symlink escape check" false e
          finally
            rmRf escLink

          let postRpc (m : String) (body : ByteArray) (tok? : Option String := none) :=
            let hdrs := #[("Content-Type", "application/x-protobuf")] ++
              match tok? with | some t => #[("Authorization", s!"Bearer {t}")] | none => #[]
            httpReq srv.port "POST" s!"/_qed/rpc/Catalog/{m}" hdrs body

          match ← httpReq srv.port "POST" "/_qed/rpc/Catalog/list"
            #[("Cookie", s!"qed_session={validTok}"), ("Content-Type", "application/x-protobuf"),
              ("Origin", "https://evil.example.com")] ByteArray.empty with
          | .ok r => c.checkEq "RPC rejects cross-origin Origin with 403" r.status 403
          | .error e => c.check "cross-origin RPC" false e

          match ← httpReq srv.port "POST" "/_qed/rpc/Catalog/list"
            #[("Cookie", s!"qed_session={validTok}"), ("Content-Type", "text/plain")] "a=1".toUTF8 with
          | .ok r => c.checkEq "RPC rejects non-protobuf Content-Type with 415" r.status 415
          | .error e => c.check "non-protobuf RPC" false e

          match ← httpReq srv.port "POST" "/_qed/rpc/Catalog/list"
            #[("Cookie", s!"qed_session={validTok}"), ("Content-Type", "application/x-protobuf"),
              ("Origin", s!"http://127.0.0.1:{srv.port}"), ("Sec-Fetch-Site", "same-origin")] ByteArray.empty with
          | .ok r => c.checkEq "RPC accepts same-origin protobuf with 200" r.status 200
          | .error e => c.check "same-origin RPC" false e

          -- 5. Auth, v1 expiry, rotation, and `requires` enforcement
          let orderReq (idx qty : Nat) := Qed.Proto.encode (idx, qty)
          let checkStatus (lbl : String) (resp : Except String HttpResp) (want : Nat) : IO Unit :=
            match resp with | .ok r => c.checkEq lbl r.status want | .error e => c.check lbl false e
          checkStatus "unauth order rejected 401" (← postRpc "order" (orderReq 0 1) none) 401
          checkStatus "forged HMAC rejected 401" (← postRpc "order" (orderReq 0 1) (some ("alice." ++ String.ofList (List.replicate 64 '0')))) 401
          checkStatus "expired v1 token rejected 401" (← postRpc "order" (orderReq 0 1) (some expiredV1)) 401
          checkStatus "requires qty <= 50 rejected 400" (← postRpc "order" (orderReq 0 99) (some validV1)) 400
          checkStatus "rotated QED_AUTH_SECRET_PREV accepted (hits requires 400)" (← postRpc "order" (orderReq 0 99) (some rotatedV1)) 400

          -- 6. GCP RS256 OAuth2 + binary PNG round-trip + StateBox token caching
          let pngBytes := ByteArray.mk #[0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a, 0x00, 0xff, 0x42]
          let addReq := Qed.Proto.encode ("plfa", ("Programming Language Foundations", ((5 : Nat), pngBytes)))
          match ← postRpc "addBook" addReq (some validTok) with
          | .ok r =>
              c.checkEq "addBook status 200" r.status 200
              c.checkEq "addBook content-type protobuf" (r.header? "content-type") (some "application/x-protobuf")
          | .error e => c.check "addBook RPC" false e

          let st1 ← mockRef.get
          c.check "GCP RS256 JWT signature verified" st1.rsaVerified
          c.checkEq "GCP token exchanged once on upload" st1.tokenExchanges 1
          c.checkEq "GCS received exact raw PNG bytes" (st1.gcsObjects["covers/plfa.png"]?) (some pngBytes)

          match ← postRpc "cover" (Qed.Proto.encode "plfa.png") none with
          | .ok r =>
              c.checkEq "cover download status 200" r.status 200
              c.checkEq "cover round-tripped exact binary PNG" (Qed.Proto.decode (α := ByteArray) r.body) (.ok pngBytes)
          | .error e => c.check "cover RPC" false e

          let st2 ← mockRef.get
          c.check ":key* preserved literal / in download path" st2.sawUnescaped
          c.checkEq "StateBox OAuth2 cache reused token without re-exchange" st2.tokenExchanges 1

          -- 7. Inline `catch` fallback on D1 500 + 8 concurrent `await`+`atomic` RPCs
          mockRef.modify fun s => { s with failD1 := true }
          checkStatus "order succeeds via catch fallback on D1 500" (← postRpc "order" (orderReq 0 1) (some validTok)) 200
          mockRef.modify fun s => { s with failD1 := false }

          let mut tasks : Array (Task (Except IO.Error (Except String HttpResp))) := #[]
          for _ in [0 : 8] do
            tasks := tasks.push (← IO.asTask (prio := .dedicated) (postRpc "order" (orderReq 0 1) (some validTok)))
          let mut all200 := true
          for t in tasks do
            match ← IO.wait t with
            | .ok (.ok r) => if r.status != 200 then all200 := false
            | _ => all200 := false
          c.check "all 8 concurrent orders returned 200" all200
          c.checkEq "Cloudflare D1 received all 9 order queries" (← mockRef.get).d1Count 9

          -- 8. Native SSR HTML + strict default CSP + gzip compression
          let mut rawSsrHtml := ""
          match ← httpReq srv.port "GET" "/" #[("Cookie", s!"qed_session={validTok}")] with
          | .ok r =>
              c.checkEq "native SSR GET / returns 200" r.status 200
              c.check "SSR HTML includes qed-state dehydration" (r.bodyStr.contains "id=\"qed-state\"")
              let csp := (r.header? "content-security-policy").getD ""
              c.check "SSR HTML includes strict default Content-Security-Policy"
                (csp.contains "default-src 'self'" && csp.contains "script-src 'self'" && csp.contains "object-src 'none'") csp
              rawSsrHtml := r.bodyStr
          | .error e => c.check "native SSR GET /" false e

          match ← httpReq srv.port "GET" "/" #[("Cookie", s!"qed_session={validTok}"), ("Accept-Encoding", "gzip")] with
          | .ok r =>
              c.checkEq "SSR gzip GET / returns 200" r.status 200
              c.checkEq "SSR gzip Content-Encoding header" (r.header? "content-encoding") (some "gzip")
              c.checkEq "SSR gzip Vary header" (r.header? "vary") (some "Accept-Encoding")
              c.check "SSR gzip body smaller than uncompressed" (r.body.size < rawSsrHtml.utf8ByteSize)
              match ← gunzipBytes r.body with
              | .ok decomp => c.checkEq "SSR gzip decompresses identically" (String.fromUTF8? decomp) (some rawSsrHtml)
              | .error e => c.check "SSR gunzip" false e
          | .error e => c.check "SSR gzip GET /" false e
        finally
          srv.stop

        -- 9. Per-IP Rate Limiter (429 Too Many Requests + Retry-After) & QED_CSP override
        let (srvRl, rlOk) ← startNativeServer dir #[
          ("QED_WORKERS", some "2"),
          ("QED_AUTH_SECRET", some authSecret),
          ("CF_D1_TOKEN", some "test-cf-d1-secret"),
          ("GCP_SA_JSON", some saJson),
          ("QED_GCP_TOKEN_URL", some s!"{extBase}/oauth2/token"),
          ("QED_EXT_GCPSTORAGE_BASE", some extBase),
          ("QED_EXT_CLOUDFLARED1_BASE", some extBase),
          ("QED_RATE_LIMIT_RPS", some "1"),
          ("QED_RATE_LIMIT_BURST", some "2"),
          ("QED_CSP", some "default-src 'none'")
        ]
        try
          c.check "rate-limited server healthy" rlOk
          if rlOk then
            let r1 ← httpReq srvRl.port "GET" "/"
            let r2 ← httpReq srvRl.port "GET" "/"
            let r3 ← httpReq srvRl.port "GET" "/"
            let r4 ← httpReq srvRl.port "GET" "/"
            match r1 with
            | .ok r =>
                c.checkEq "rate-limit req 1 allowed (200)" r.status 200
                c.checkEq "QED_CSP override applied" (r.header? "content-security-policy") (some "default-src 'none'")
            | .error e => c.check "rate-limit req 1" false e
            match r2 with
            | .ok r => c.checkEq "rate-limit req 2 allowed (200)" r.status 200
            | .error e => c.check "rate-limit req 2" false e
            let got429 := match r3, r4 with
              | .ok a, .ok b => a.status == 429 || b.status == 429
              | .ok a, _     => a.status == 429
              | _, .ok b     => b.status == 429
              | _, _         => false
            let hasRetryAfter := match r3, r4 with
              | .ok a, .ok b => (a.status == 429 && (a.header? "retry-after").isSome) || (b.status == 429 && (b.header? "retry-after").isSome)
              | .ok a, _     => a.status == 429 && (a.header? "retry-after").isSome
              | _, .ok b     => b.status == 429 && (b.header? "retry-after").isSome
              | _, _         => false
            c.check "burst excess rejected with 429 Too Many Requests" got429
            c.check "429 response includes Retry-After header" hasRetryAfter
        finally
          srvRl.stop
      finally
        stopMock

  -- 10. Web Essentials suite (CachedStaticAsset gzip, Set-Cookie, custom HTTP routes, SSE stream, per-route head & 404/302 SSR)
  runWebEssentialsSuite c
  c.finish

end Tests.Native.FullstackRpc
