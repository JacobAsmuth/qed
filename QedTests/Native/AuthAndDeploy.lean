import Qed.Auth.Oidc
import Qed.Server.Native
import Qed.Cloud.Executor
import Qed.Deploy
import Cli.DevAuth
import Cli.Scaffold
import QedTests.Native.Harness
import QedTests.AuthChecks
import QedTests.ServerChecks
open Qed.Auth Qed.Auth.Oidc Qed.Server QedTests.Native

namespace QedTests.Native.AuthAndDeploy

private def stripHostPrefix (url : String) : String :=
  match url.splitOn "://" with
  | [_, rest] => match rest.splitOn "/" with | _ :: segs => "/" ++ String.intercalate "/" segs | [] => "/"
  | _ => url

private def testCryptoAndJwtCore (c : TestChecker) : IO Unit := do
  c.expectOk "ecP256Keygen succeeds" (← Prim.ecP256Keygen) fun (pkcs8, pubX, pubY) => do
    c.check "ecP256Keygen produces 32B X/Y" (pubX.size == 32 && pubY.size == 32)
    let kp : Qed.Cli.DevAuth.DevAuthKeypair := { kid := "k1", pkcs8Der := pkcs8, xB64 := base64UrlEncode pubX, yB64 := base64UrlEncode pubY }
    let (jwk, nowSec) := (JwkKey.ecP256 "k1" pubX pubY, (← Prim.nowMs).toNat / 1000)
    c.expectOk "signDevIdToken succeeds" (← Qed.Cli.DevAuth.signDevIdToken kp "https://idp.test" "usr_42" "aud_app" "nonce_xyz" "alice@test.dev" "admin" "org_7" true 600) fun jwt => do
      let vcfg : OidcValidationCfg := { issuer := "https://idp.test", audience := "aud_app", expectedNonce? := some "nonce_xyz" }
      c.expectOk "ES256 JWK verify valid JWT" (← verifyJwtWithKeys vcfg #[jwk] jwt nowSec) fun vc => do
        let u := AuthChecks.CloudAuth.fromClaims vc.claims
        c.checkEq "ES256 extracted claims (sub, role, orgId, email, verified)" (u.id, u.role, u.orgId, u.email, u.verified) ("usr_42", "admin", some "org_7", "alice@test.dev", true)
      let noneTok := s!"{base64UrlEncode "{\"alg\":\"none\",\"typ\":\"JWT\"}".toUTF8}.{base64UrlEncode "{\"iss\":\"https://idp.test\",\"sub\":\"admin\",\"aud\":\"aud_app\",\"exp\":9999999999}".toUTF8}.sig"
      for (lbl, cfg, tok, ts) in [("wrong audience", { vcfg with audience := "other_app" }, jwt, nowSec), ("wrong issuer", { vcfg with issuer := "https://evil.test" }, jwt, nowSec),
          ("wrong nonce", { vcfg with expectedNonce? := some "wrong" }, jwt, nowSec), ("expired token", vcfg, jwt, nowSec + 10000),
          ("tampered signature", vcfg, jwt ++ "A", nowSec), ("alg:none", vcfg, noneTok, nowSec)] do
        c.check s!"JWT {lbl} rejected" (!(← verifyJwtWithKeys cfg #[jwk] tok ts).isOk)
  let sample := "hello+/world=123\x00\xff".toUTF8; let enc := base64UrlEncode sample
  c.check "base64url has no + / =" (!enc.contains "+" && !enc.contains "/" && !enc.contains "=")
  c.checkEq "base64url round-trip" (base64UrlDecode enc) (.ok sample)
  c.check "DeployManifest rejects bad version" (!({ version := 2 } : Qed.Deploy.DeployManifest).validate.isOk)
  c.check "DeployManifest rejects unsafe auth callback" (!(Qed.Deploy.validateAuthManifest { name := "Bad", issuerEnv := "QED_AUTH_ISSUER", audienceEnv := "QED_AUTH_AUDIENCE", callbackPath := "//evil.com/cb" }).isOk)
  let (testSecret, txBody) := ("qed-test-session-secret-32-bytes", "tx1.1700000600.eyJzdGF0ZSI6IjEyMyJ9")
  let v2Tok ← signSessionCookieV2 testSecret { userId := "usr_alice", claims := [("role", "admin")] } 60
  let signHex (msg : String) : IO String := return Qed.Proto.encodeHex (← Prim.hmacSha256 testSecret.toUTF8 msg.toUTF8)
  let txDomTok := s!"{txBody}.{← signHex s!"qed-tx:{txBody}"}"
  for (lbl, tok, now) in [("raw-signed tx1.* cookie", s!"{txBody}.{← signHex txBody}", 1700000000), ("domain-separated tx1.* cookie", txDomTok, 1700000000),
      ("qed-tx: prefixed tx1.* replay", s!"qed-tx:{txDomTok}", 1700000000), ("NUL-separated qed-tx\\0 replay", s!"qed-tx\x00{txBody}.{← signHex s!"qed-tx\x00{txBody}"}", 1700000000), ("expired v2.* cookie", v2Tok, 9999999999)] do
    c.checkEq s!"verifyUserTokenWithNow rejects {lbl}" (← Qed.Server.Native.verifyUserTokenWithNow [testSecret] tok now) none
  c.checkEq "verifySessionCookieV2 rejects expired v2.* cookie" (← verifySessionCookieV2 [testSecret] v2Tok 9999999999) none
  c.checkEq "RequestCtx.isAuthenticated rejects unverified Bearer token" ({ userId := none, bearerToken := some "forged-invalid-token", headers := [("authorization", "Bearer forged-invalid-token")] } : Qed.Server.RequestCtx).isAuthenticated false
  c.checkEq "RequestCtx.isAuthenticated accepts verified userId" ({ userId := some "usr_alice" } : Qed.Server.RequestCtx).isAuthenticated true

private def testOidcFlowAndDeployManifest (c : TestChecker) : IO Unit :=
  withDevApp c "QedTests.AuthChecks" fun outDir => do
    c.check "buildDevApp QedTests.AuthChecks succeeded" true
    let manifestPath := outDir ++ "/qed_deploy.json"; let existsM ← (System.FilePath.mk manifestPath).pathExists
    c.check "qed_deploy.json emitted on build" existsM
    if existsM then
      c.expectOk "qed_deploy.json valid JSON" (Qed.Json.parse (← IO.FS.readFile manifestPath)) fun j => do
        for (lbl, p, want) in [("mode is fullstack", "mode", "fullstack"), ("csp matches defaultCsp", "csp", Qed.Server.defaultCsp),
            ("auth.name", "auth.name", "CloudAuth"), ("auth.callbackPath", "auth.callbackPath", "/_qed/auth/callback")] do c.checkJsonStr s!"manifest {lbl}" j p want
        for (lbl, p, pred) in [("auth.claims has 4 typed claims", "auth.claims", fun xs : List Qed.Json => xs.length == 4),
            ("auth.providers has 3 providers", "auth.providers", (·.length == 3)),
            ("egress contains BillingApi origin", "egress", (·.any (·.str? == some "https://billing.example.com"))),
            ("databases contains AuthNotesDb", "databases", (·.any (·.pathStr? "name" == some "AuthNotesDb"))),
            ("secrets contains AUTH_NOTES_DB_URL", "secrets", (·.any (·.str? == some "AUTH_NOTES_DB_URL")))] do
          c.checkJsonArr s!"manifest {lbl}" j p pred
    checkLeakGate c "QedTests.AuthChecks" #["AuthChecks.CloudAuth.config", "AuthChecks.CloudAuth.secrets"]
    let devAuthPort ← Prim.freePort
    withNativeBin c "qed dev-auth started cleanly" (← qedBinPath) #["dev-auth", toString devAuthPort] devAuthPort #[] fun _ => do
      c.checkHttp "dev-auth discovery" (← httpReq devAuthPort "GET" "/.well-known/openid-configuration") (contains := ["ES256", "S256"])
      c.checkHttp "dev-auth JWKS" (← httpReq devAuthPort "GET" "/jwks.json") (contains := ["\"P-256\""])
      let issuerUrl := s!"http://127.0.0.1:{devAuthPort}"
      let postTokenForm (pairs : List (String × String)) := httpReq devAuthPort "POST" "/token" #[("Content-Type", "application/x-www-form-urlencoded")] (encodeFormBody pairs).toUTF8
      withTempDir "qed-auth-test" fun tmpDir =>
        withNativeServer c "AuthApp native server started cleanly" outDir #[("QED_AUTH_ISSUER", some issuerUrl), ("QED_AUTH_AUDIENCE", some "qed-cloud-test"),
            ("QED_AUTH_CLIENT_ID", some "qed-cloud-test"), ("AUTH_NOTES_DB_URL", some s!"sqlite://{tmpDir}/auth.db")] (dev := true) fun appProc => do
          c.checkStatus "unauthenticated /_qed/auth/me returns 401" (← httpReq appProc.port "GET" "/_qed/auth/me") 401
          c.checkHttp "GET /_qed/auth/login open-redirect test" (← httpReq appProc.port "GET" "/_qed/auth/login?returnTo=//evil.com") (status? := some 302)
            (extra := fun r => let loc := (r.header? "location").getD ""; c.check "login redirects to dev-auth /authorize with PKCE S256" (loc.startsWith (issuerUrl ++ "/authorize") && loc.contains "code_challenge_method=S256"))
          let authRpc (fn : String) (tok? : Option String := none) (extraHdrs : Array (String × String) := #[]) := httpRpc appProc.port "AuthApi" fn (Qed.Proto.encode ()) tok? extraHdrs
          let aliceParams := "&auto=1&sub=usr_alice&role=admin&email=alice%40qed.dev&orgId=org_42"
          let doOidcLogin (tag returnTo queryExtra : String) (fullChecks : Bool := false) : IO String := do
            let .ok r1 ← httpReq appProc.port "GET" s!"/_qed/auth/login?returnTo={returnTo}" | c.check s!"{tag} login step 1" false; return ""
            if fullChecks then c.checkEq s!"{tag} login step 1 status 302" r1.status 302
            let txCookie? := r1.cookie? "qed_auth_tx"
            if fullChecks then
              c.check s!"{tag} login sets HttpOnly qed_auth_tx cookie" txCookie?.isSome
              let txVal := match (txCookie?.getD "").splitOn "=" with | _ :: rest => String.intercalate "=" rest | [] => ""
              c.check "qed_auth_tx uses tx1. envelope" (txVal.startsWith "tx1.")
              for (lbl, act) in [("replaying tx1.* as qed_session to /_qed/auth/me", httpReq appProc.port "GET" "/_qed/auth/me" #[("Cookie", s!"qed_session={txVal}")]),
                  ("replaying tx1.* as Bearer to /_qed/auth/me", httpReq appProc.port "GET" "/_qed/auth/me" #[("Authorization", s!"Bearer {txVal}")]),
                  ("replaying tx1.* as qed_session to auth RPC", authRpc "whoami" none #[("Cookie", s!"qed_session={txVal}")]),
                  ("replaying tx1.* as Bearer to auth RPC", authRpc "whoami" (some txVal)),
                  ("replaying qed-tx: prefixed tx1.* to /_qed/auth/me", httpReq appProc.port "GET" "/_qed/auth/me" #[("Cookie", s!"qed_session=qed-tx:{txVal}")]),
                  ("replaying qed-tx: prefixed tx1.* as Bearer to auth RPC", authRpc "whoami" (some s!"qed-tx:{txVal}"))] do
                c.checkStatus s!"{lbl} returns 401" (← act) 401
            let .ok r2 ← httpReq devAuthPort "GET" (stripHostPrefix ((r1.header? "location").getD "") ++ queryExtra) | c.check s!"{tag} authorize step 2" false; return ""
            if fullChecks then c.checkEq "dev-auth /authorize auto redirects 302" r2.status 302
            let cbPath := stripHostPrefix ((r2.header? "location").getD "")
            if fullChecks then
              c.check "authorize redirects back to /_qed/auth/callback" (cbPath.startsWith "/_qed/auth/callback?")
              c.checkStatus "callback rejects mismatched state (403)" (← httpReq appProc.port "GET" (cbPath ++ "tampered") #[("Cookie", txCookie?.getD "")]) 403
            let .ok r3 ← httpReq appProc.port "GET" cbPath #[("Cookie", txCookie?.getD "")] | c.check s!"{tag} callback step 3" false; return ""
            c.checkEq s!"{tag} callback succeeds with 302" r3.status 302
            if fullChecks then c.checkEq s!"{tag} callback redirects to sanitized returnTo {returnTo}" (r3.header? "location") (some returnTo)
            let sessC? := r3.cookie? "qed_session"
            if fullChecks then c.check s!"{tag} callback sets signed v2 qed_session cookie" (sessC?.any (·.contains "v2."))
            return sessC?.getD ""
          let checkProfile (tag cookie : String) (k : AuthChecks.AuthNotesDb.profiles → IO Unit) : IO Unit := do
            c.checkHttp s!"getProfile after {tag}" (← authRpc "getProfile" none #[("Cookie", cookie)]) (extra := fun r =>
              c.expectOk s!"decode getProfile after {tag}" (Qed.Proto.decode (α := Option AuthChecks.AuthNotesDb.profiles) r.body) fun
                | some prof => k prof | none => c.check s!"profile exists after {tag}" false "got none")
          let sessionCookie ← doOidcLogin "OIDC" "/dashboard" aliceParams (fullChecks := true)
          if !sessionCookie.isEmpty then
            c.checkHttp "authenticated /_qed/auth/me" (← httpReq appProc.port "GET" "/_qed/auth/me" #[("Cookie", sessionCookie)]) (contains := ["\"usr_alice\"", "\"admin\"", "\"org_42\""])
            c.checkStatus "admin RPC with OIDC v2 cookie returns 200" (← authRpc "adminAction" none #[("Cookie", sessionCookie)]) 200
            checkProfile "1st sign-in" sessionCookie fun prof => c.checkEq "onCreateAccount(0)+onSignIn(+1) stored profile" (prof.id, prof.email, prof.logins) ("usr_alice", "alice@qed.dev", 1)
            let logoutRaw := (AuthChecks.CloudAuth.logoutUrl "/").raw
            c.checkHttp "GET logoutUrl(/) rejects Sec-Fetch-Site: cross-site (403)" (← httpReq appProc.port "GET" logoutRaw #[("Cookie", sessionCookie), ("Sec-Fetch-Site", "cross-site")])
              (status? := some 403) (extra := fun r => c.check "cross-site GET logout does not clear qed_session" (r.cookie? "qed_session").isNone)
            for (lbl, extraHdrs) in [("same-origin", #[("Sec-Fetch-Site", "same-origin")]), ("none", #[("Sec-Fetch-Site", "none")]), ("direct", #[])] do
              c.checkHttp s!"GET logoutUrl(/) allows {lbl} (302)" (← httpReq appProc.port "GET" logoutRaw (#[("Cookie", sessionCookie)] ++ extraHdrs))
                (status? := some 302) (headers := [("location", some "/")]) (extra := (·.checkCookieFlag c s!"{lbl} GET logout emits Max-Age=0 clear cookie" ["qed_session=", "Max-Age=0"]))
            c.checkHttp "POST /_qed/auth/logout" (← httpReq appProc.port "POST" "/_qed/auth/logout" #[("Cookie", sessionCookie), ("Origin", s!"http://127.0.0.1:{appProc.port}")])
              (extra := (·.checkCookieFlag c "logout emits Max-Age=0 clear cookie" ["qed_session=", "Max-Age=0"]))
            let sessCookie2 ← doOidcLogin "2nd OIDC" "/" aliceParams
            if !sessCookie2.isEmpty then checkProfile "2nd sign-in" sessCookie2 fun prof2 => c.checkEq "2nd sign-in skips onCreateAccount and increments logins == 2" prof2.logins 2
          for (sub, role, checkAdminWant, checkWhoami) in [("usr_bob", "member", 403, true), ("usr_root", "admin", 200, false)] do
            let tok? := match ← postTokenForm [("grant_type", "direct_dev_token"), ("audience", "qed-cloud-test"), ("sub", sub), ("role", role), ("email", s!"{sub}@qed.dev")] with
              | .ok r => if r.status == 200 then (Qed.Json.parse r.bodyStr).toOption.bind (·.strAt? "id_token") else none | .error _ => none
            match tok? with
            | none => c.check s!"mint {role} ES256 JWT" false
            | some jwt =>
                if checkWhoami then c.checkStatus s!"{role} Bearer ES256 JWT passes whoami (200)" (← authRpc "whoami" (some jwt)) 200
                c.checkStatus s!"{role} Bearer ES256 JWT adminAction ({checkAdminWant})" (← authRpc "adminAction" (some jwt)) checkAdminWant
          let chal := base64UrlEncode (← Prim.sha256 "correct-verifier-123".toUTF8)
          c.expectOk "PKCE authorize setup" (← httpReq devAuthPort "GET" s!"/authorize?auto=1&client_id=qed-cloud-test&redirect_uri=http%3A%2F%2F127.0.0.1%3A9999%2Fcb&state=s1&nonce=n1&code_challenge={chal}") fun r => do
            let code := ((parseQueryParams (splitPathQuery ((r.header? "location").getD "")).2).lookup "code").getD ""
            c.checkStatus "PKCE S256 rejects wrong code_verifier (400)" (← postTokenForm [("grant_type", "authorization_code"), ("code", code), ("redirect_uri", "http://127.0.0.1:9999/cb"), ("client_id", "qed-cloud-test"), ("code_verifier", "WRONG-verifier")]) 400

private def testRoadmapRuntimeFeatures (c : TestChecker) : IO Unit := do
  -- 1. `before:` middleware hook across RPC, HTTP route, and WebSocket join/send (and passthrough on unmatched HTTP)
  let box ← Prim.mkStateBox ServerChecks.GuardedApi.initState
  let inst := Native.withStateBox box
  let okCtx : RequestCtx := { userId := some "usr_alice", headers := [("authorization", "Bearer good_tok")] }
  let revCtx : RequestCtx := { userId := some "usr_alice", headers := [("authorization", "Bearer bad_tok")] }
  -- Revoke "Bearer bad_tok"
  let revBody := Qed.Proto.encode "Bearer bad_tok"
  let _ ← @ServerChecks.GuardedApi.dispatchM IO _ _ inst okCtx "revokeHeader" revBody
  -- RPC allowed for good token, blocked (401) for revoked token
  c.expectOk "[before] RPC allows non-revoked bearer" (← @ServerChecks.GuardedApi.dispatchM IO _ _ inst okCtx "hello" ByteArray.empty) fun bs =>
    c.expectOk "[before] RPC decode hello" (Qed.Proto.decode (α := String) bs) fun s =>
      c.checkEq "[before] hello returned greeting + helper bump" s "hi usr_alice:1"
  match ← @ServerChecks.GuardedApi.dispatchM IO _ _ inst revCtx "hello" ByteArray.empty with
  | .error e => c.checkEq "[before] RPC rejects revoked bearer (401)" (e.code, e.message) (401, "token revoked")
  | .ok _ => c.check "[before] RPC rejects revoked bearer" false "unexpectedly succeeded"
  -- HTTP route allowed for good token, blocked for revoked token, unmatched passes through as none
  match ← @ServerChecks.GuardedApi.httpDispatchM IO _ _ inst okCtx "GET" "/api/ping" with
  | .ok (some resp) => c.checkEq "[before] HTTP route allows good bearer" (resp.status, utf8Str resp.body) (200, "pong")
  | _ => c.check "[before] HTTP route allows good bearer" false
  match ← @ServerChecks.GuardedApi.httpDispatchM IO _ _ inst revCtx "GET" "/api/ping" with
  | .error e => c.checkEq "[before] HTTP route rejects revoked bearer (401)" e.code 401
  | _ => c.check "[before] HTTP route rejects revoked bearer" false
  match ← @ServerChecks.GuardedApi.httpDispatchM IO _ _ inst revCtx "GET" "/unmatched" with
  | .ok none => c.check "[before] unmatched HTTP route bypasses before hook" true
  | _ => c.check "[before] unmatched HTTP route bypasses before hook" false
  -- `ctx.parseJson` + `ctx.queryParam` in HTTP routes (200 on valid JSON, 400 on malformed JSON)
  let echoOkCtx : RequestCtx := { okCtx with query := "?tag=hello+world", body := "{\"msg\":\"qed\"}" }
  match ← @ServerChecks.GuardedApi.httpDispatchM IO _ _ inst echoOkCtx "POST" "/api/echo" with
  | .ok (some resp) => c.checkEq "[ctx-http] parseJson + queryParam succeeds" (resp.status, utf8Str resp.body) (200, "hello world:qed")
  | _ => c.check "[ctx-http] parseJson + queryParam succeeds" false
  let echoBadCtx : RequestCtx := { okCtx with body := "{not json" }
  match ← @ServerChecks.GuardedApi.httpDispatchM IO _ _ inst echoBadCtx "POST" "/api/echo" with
  | .error e => c.checkEq "[ctx-http] parseJson rejects malformed JSON (400)" e.code 400
  | _ => c.check "[ctx-http] parseJson rejects malformed JSON (400)" false
  -- WebSocket join (1) & send (2) blocked for revoked token, allowed for good token; leave (3) bypasses `before:`
  match ← @ServerChecks.GuardedApi.wsDispatchM IO _ _ inst okCtx 1 "feed" ByteArray.empty ByteArray.empty with
  | .ok _ => c.check "[before] WS join allows good bearer" true
  | .error e => c.check "[before] WS join allows good bearer" false e.message
  match ← @ServerChecks.GuardedApi.wsDispatchM IO _ _ inst revCtx 1 "feed" ByteArray.empty ByteArray.empty with
  | .error e => c.checkEq "[before] WS join rejects revoked bearer (401)" e.code 401
  | .ok _ => c.check "[before] WS join rejects revoked bearer" false
  match ← @ServerChecks.GuardedApi.wsDispatchM IO _ _ inst revCtx 2 "feed" ByteArray.empty (Qed.Proto.encode "hi") with
  | .error e => c.checkEq "[before] WS send rejects revoked bearer (401)" e.code 401
  | .ok _ => c.check "[before] WS send rejects revoked bearer" false
  match ← @ServerChecks.GuardedApi.wsDispatchM IO _ _ inst revCtx 3 "feed" ByteArray.empty ByteArray.empty with
  | .ok _ => c.check "[before] WS leave bypasses before hook" true
  | .error e => c.check "[before] WS leave bypasses before hook" false e.message
  -- Private helper not reachable via RPC dispatch
  match ← @ServerChecks.GuardedApi.dispatchM IO _ _ inst okCtx "bump" (Qed.Proto.encode (1 : Nat)) with
  | .error e => c.checkEq "[fn-private] private fn unreachable via dispatchM (404)" e.code 404
  | .ok _ => c.check "[fn-private] private fn unreachable via dispatchM" false
  -- 2. `hashBearerToken` + `mintBearerToken` validation
  c.expectOk "[token] hashBearerToken deterministic 64-hex" (← Qed.Server.hashBearerToken (m := IO) "sample-token") fun h1 => do
    c.expectOk "[token] hashBearerToken second call" (← Qed.Server.hashBearerToken (m := IO) "sample-token") fun h2 =>
      c.check "[token] hash deterministic and 64 hex chars" (h1 == h2 && h1.length == 64)
  c.check "[token] mintBearerToken rejects empty userId" (match ← Qed.Server.mintBearerToken (m := IO) "" with | .error e => e.code == 400 | .ok _ => false)
  c.check "[token] mintBearerToken rejects missing secret env" (match ← Qed.Server.mintBearerToken (m := IO) "usr_1" 60 "QED_NONEXISTENT_TOKEN_SECRET_XYZ" with | .error e => e.code == 500 | .ok _ => false)
  -- 3. `fetchGcpMetadataToken` & `GcpAuthMode.metadata` against local mock metadata server
  let flavorOkRef ← IO.mkRef false
  let mockRes ← startMockHttpServer fun _ path hdrs _ => do
    let hasFlavor := hdrs.any fun (k, v) => k.toLower == "metadata-flavor" && v == "Google"
    if !hasFlavor then return (403, "text/plain", "missing Metadata-Flavor".toUTF8)
    flavorOkRef.set true
    if path.startsWith "/computeMetadata/v1/instance/service-accounts/default/identity" then
      return (200, "text/plain", "mock-oidc-id-jwt".toUTF8)
    else if path == "/computeMetadata/v1/instance/service-accounts/default/token" then
      return (200, "application/json", "{\"access_token\":\"mock-adc-access-tok\",\"expires_in\":1800}".toUTF8)
    else return (404, "text/plain", "not found".toUTF8)
  c.expectOk "[gcp-metadata] mock server started" mockRes fun (port, stop) => do
    try
      let cache ← Prim.mkStateBox (#[] : Array Native.GcpTokenCacheEntry)
      let base := s!"http://127.0.0.1:{port}"
      c.expectOk "[gcp-metadata] fetchGcpMetadataToken OAuth2 succeeds" (← Native.fetchGcpMetadataToken (some cache) none (some base)) fun tok =>
        c.checkEq "[gcp-metadata] OAuth2 token matches mock" tok "mock-adc-access-tok"
      c.expectOk "[gcp-metadata] fetchGcpMetadataToken OIDC identity succeeds" (← Native.fetchGcpMetadataToken (some cache) (some "https://svc.run.app") (some base)) fun idTok =>
        c.checkEq "[gcp-metadata] OIDC id token matches mock" idTok "mock-oidc-id-jwt"
      c.check "[gcp-metadata] Metadata-Flavor: Google header sent" (← flavorOkRef.get)
    finally
      stop
  -- 4. `Cli.renderStagedLakefile` extracts authoritative `QedServer` roots from `lakefile.lean`
  let lakeSrc ← IO.FS.readFile "lakefile.lean"
  c.expectOk "[stage-sdk] renderStagedLakefile succeeds" (Qed.Cli.renderStagedLakefile lakeSrc) fun staged => do
    c.check "[stage-sdk] uses inputBinFile for libqed_server" (staged.contains "inputBinFile (pkg.staticLibDir / nameToStaticLib \"qed_server\")")
    c.check "[stage-sdk] preserves QedServer roots" (staged.contains "lean_lib QedServer" && staged.contains "`Qed.Cloud.Executor")
  -- 5. `qedjs --verify-env` verifies `Qed.Str`, `Qed.Time`, session propagation, query controls, nested mutation, or-patterns, JSX `let`
  let (code, _, err) ← runCmd (← qedjsBinPath) #["--verify-env", "QedTests.SyntaxChecks"]
  c.check "[js-verify-env] QedTests.SyntaxChecks (Qed.Str + Qed.Time + Track 2/5) passes qedjs --verify-env" (code == 0) err

def run : IO Bool := do
  let c ← mkChecker "auth-and-deploy"; testCryptoAndJwtCore c; testOidcFlowAndDeployManifest c; testRoadmapRuntimeFeatures c; c.finish

end QedTests.Native.AuthAndDeploy
