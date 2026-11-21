import Qed.Auth.Oidc
import Qed.Deploy
import Cli.DevAuth
import Tests.Native.Harness
import Tests.AuthChecks

open Qed.Auth
open Qed.Auth.Oidc
open Qed.Server
open Tests.Native

namespace Tests.Native.AuthAndDeploy

private def extractSetCookies (hdrs : Array (String × String)) : List String :=
  hdrs.foldl (init := []) fun acc (k, v) =>
    if k.toLower == "set-cookie" then acc ++ [v] else acc

private def cookiePairFromSetCookie (sc : String) : String :=
  (sc.splitOn ";").headD "" |>.trimAscii.toString

private def findCookieByName (setCookies : List String) (name : String) : Option String :=
  setCookies.findSome? fun sc =>
    let pair := cookiePairFromSetCookie sc
    if pair.startsWith (name ++ "=") then some pair else none

private def stripHostPrefix (url : String) : String :=
  match url.splitOn "://" with
  | [_, rest] =>
      match rest.splitOn "/" with
      | _ :: segs => "/" ++ String.intercalate "/" segs
      | []        => "/"
  | _ => url

private def testCryptoAndJwtCore (c : TestChecker) : IO Unit := do
  -- 1. Generate real ephemeral P-256 keypair & verify ES256 JWT via `verifyJwtWithKeys`
  let kpRes ← Prim.ecP256Keygen
  match kpRes with
  | .error e =>
      c.check "ecP256Keygen succeeds" false e
  | .ok (pkcs8, pubX, pubY) =>
      c.check "ecP256Keygen produces 32B X/Y" (pubX.size == 32 && pubY.size == 32)
      let kp : Qed.Cli.DevAuth.DevAuthKeypair := {
        kid := "k1", pkcs8Der := pkcs8
        xB64 := base64UrlEncode pubX, yB64 := base64UrlEncode pubY
      }
      let jwk : JwkKey := .ecP256 "k1" pubX pubY
      let nowSec := ((← Prim.nowMs).toNat) / 1000
      let tokRes ← Qed.Cli.DevAuth.signDevIdToken kp "https://idp.test" "usr_42" "aud_app"
        "nonce_xyz" "alice@test.dev" "admin" "org_7" true 600
      match tokRes with
      | .error e => c.check "signDevIdToken succeeds" false e
      | .ok jwt =>
          let vcfg : OidcValidationCfg := {
            issuer := "https://idp.test", audience := "aud_app", expectedNonce? := some "nonce_xyz"
          }
          let okRes ← verifyJwtWithKeys vcfg #[jwk] jwt nowSec
          match okRes with
          | .error e => c.check "ES256 JWK verify valid JWT" false e
          | .ok vc =>
              let u := AuthChecks.CloudAuth.fromClaims vc.claims
              c.checkEq "ES256 extracted sub" u.id "usr_42"
              c.checkEq "ES256 extracted role" u.role "admin"
              c.checkEq "ES256 extracted orgId" u.orgId (some "org_7")
              c.checkEq "ES256 extracted email" u.email "alice@test.dev"
              c.checkEq "ES256 extracted verified" u.verified true

          -- Wrong audience rejected
          let badAud ← verifyJwtWithKeys { vcfg with audience := "other_app" } #[jwk] jwt nowSec
          c.check "JWT wrong audience rejected" (!badAud.isOk)

          -- Wrong issuer rejected
          let badIss ← verifyJwtWithKeys { vcfg with issuer := "https://evil.test" } #[jwk] jwt nowSec
          c.check "JWT wrong issuer rejected" (!badIss.isOk)

          -- Wrong nonce rejected
          let badNonce ← verifyJwtWithKeys { vcfg with expectedNonce? := some "wrong" } #[jwk] jwt nowSec
          c.check "JWT wrong nonce rejected" (!badNonce.isOk)

          -- Expired token rejected
          let expired ← verifyJwtWithKeys vcfg #[jwk] jwt (nowSec + 10000)
          c.check "JWT expired token rejected" (!expired.isOk)

          -- Tampered signature rejected
          let tampered := jwt ++ "A"
          let badSig ← verifyJwtWithKeys vcfg #[jwk] tampered nowSec
          c.check "JWT tampered signature rejected" (!badSig.isOk)

          -- `alg: none` forgery rejected
          let noneHdr := base64UrlEncode "{\"alg\":\"none\",\"typ\":\"JWT\"}".toUTF8
          let nonePay := base64UrlEncode "{\"iss\":\"https://idp.test\",\"sub\":\"admin\",\"aud\":\"aud_app\",\"exp\":9999999999}".toUTF8
          let noneTok := s!"{noneHdr}.{nonePay}.sig"
          let noneRes ← verifyJwtWithKeys vcfg #[jwk] noneTok nowSec
          c.check "JWT alg:none rejected" (!noneRes.isOk)

  -- 2. Base64URL round-trip & DeployManifest compile-time validation checks
  let sample := "hello+/world=123\x00\xff".toUTF8
  let enc := base64UrlEncode sample
  c.check "base64url has no + / =" (!enc.contains "+" && !enc.contains "/" && !enc.contains "=")
  c.checkEq "base64url round-trip" (base64UrlDecode enc) (.ok sample)
  c.check "DeployManifest rejects bad version"
    (!({ version := 2 } : Qed.Deploy.DeployManifest).validate.isOk)
  c.check "DeployManifest rejects unsafe auth callback"
    (!(Qed.Deploy.validateAuthManifest {
      name := "Bad", issuerEnv := "QED_AUTH_ISSUER", audienceEnv := "QED_AUTH_AUDIENCE",
      callbackPath := "//evil.com/cb" }).isOk)

private def testOidcFlowAndDeployManifest (c : TestChecker) : IO Unit := do
  -- 1. Build `Tests.AuthChecks` fullstack app (also emits `qed_deploy.json`)
  let some outDir ← buildDevApp "Tests.AuthChecks"
    | do c.check "buildDevApp Tests.AuthChecks" false; return
  c.check "buildDevApp Tests.AuthChecks succeeded" true

  -- 2. Verify `qed_deploy.json` manifest was emitted and contains all expected infra metadata
  let manifestPath := outDir ++ "/qed_deploy.json"
  let existsM ← (System.FilePath.mk manifestPath).pathExists
  c.check "qed_deploy.json emitted on build" existsM
  if existsM then
    let raw ← IO.FS.readFile manifestPath
    match Qed.Json.parse raw with
    | .error e => c.check "qed_deploy.json valid JSON" false e
    | .ok j =>
        c.checkEq "manifest mode is fullstack" ((j.get? "mode").bind (·.str?)) (some "fullstack")
        let authObj? := j.get? "auth"
        c.checkEq "manifest auth.name" (authObj?.bind (·.get? "name") |>.bind (·.str?)) (some "CloudAuth")
        c.checkEq "manifest auth.callbackPath" (authObj?.bind (·.get? "callbackPath") |>.bind (·.str?)) (some "/_qed/auth/callback")
        let hasClaims := match authObj?.bind (·.get? "claims") with
          | some (.arr cs) => cs.length == 4
          | _              => false
        c.check "manifest auth.claims has 4 typed claims" hasClaims
        let hasProvs := match authObj?.bind (·.get? "providers") with
          | some (.arr ps) => ps.length == 3
          | _              => false
        c.check "manifest auth.providers has 3 providers" hasProvs
        let hasEgress := match j.get? "egress" with
          | some (.arr es) => es.any (fun x => x.str? == some "https://billing.example.com")
          | _              => false
        c.check "manifest egress contains BillingApi origin" hasEgress
        let hasDb := match j.get? "databases" with
          | some (.arr ds) => ds.any (fun d => (d.get? "name").bind (·.str?) == some "AuthNotesDb")
          | _              => false
        c.check "manifest databases contains AuthNotesDb" hasDb
        let hasSecrets := match j.get? "secrets" with
          | some (.arr ss) => ss.any (fun s => s.str? == some "AUTH_NOTES_DB_URL")
          | _              => false
        c.check "manifest secrets contains AUTH_NOTES_DB_URL" hasSecrets

  -- 3. Verify client bundle leak gate blocks `CloudAuth.config` & `CloudAuth.secrets`
  checkLeakGate c "Tests.AuthChecks" #[
    "AuthChecks.CloudAuth.config",
    "AuthChecks.CloudAuth.secrets"
  ]

  -- 4. Spawn built-in `qed dev-auth` ephemeral ES256 OIDC IdP
  let devAuthPort ← Prim.freePort
  let qedBin ← qedBinPath
  let (devAuthProc, devAuthUp) ← startNativeBin qedBin #["dev-auth", toString devAuthPort] devAuthPort
  c.check "qed dev-auth started cleanly" devAuthUp
  if !devAuthUp then
    devAuthProc.stop
    return

  -- Check discovery & JWKS endpoints on dev-auth
  match ← httpReq devAuthPort "GET" "/.well-known/openid-configuration" with
  | .ok r =>
      c.checkEq "dev-auth discovery HTTP 200" r.status 200
      c.check "dev-auth discovery advertises ES256 & S256"
        (r.bodyStr.contains "ES256" && r.bodyStr.contains "S256")
  | .error e => c.check "dev-auth discovery reachable" false e

  match ← httpReq devAuthPort "GET" "/jwks.json" with
  | .ok r =>
      c.checkEq "dev-auth JWKS HTTP 200" r.status 200
      c.check "dev-auth JWKS serves EC P-256 key" (r.bodyStr.contains "\"P-256\"")
  | .error e => c.check "dev-auth JWKS reachable" false e

  -- 5. Spawn `Tests.AuthChecks` fullstack server pointed at `dev-auth`
  let issuerUrl := s!"http://127.0.0.1:{devAuthPort}"
  let dbPath := s!"/tmp/qed-auth-test-{devAuthPort}.db"
  let (appProc, appUp) ← startNativeServer outDir #[
    ("QED_AUTH_ISSUER", some issuerUrl),
    ("QED_AUTH_AUDIENCE", some "qed-cloud-test"),
    ("QED_AUTH_CLIENT_ID", some "qed-cloud-test"),
    ("AUTH_NOTES_DB_URL", some s!"sqlite://{dbPath}")
  ] (dev := true)
  c.check "AuthApp native server started cleanly" appUp
  if !appUp then
    appProc.stop
    devAuthProc.stop
    rmRf dbPath
    return

  -- 6. Unauthenticated `/_qed/auth/me` → 401
  match ← httpReq appProc.port "GET" "/_qed/auth/me" with
  | .ok r => c.checkEq "unauthenticated /_qed/auth/me returns 401" r.status 401
  | .error e => c.check "GET /_qed/auth/me" false e

  -- 7. Open-redirect attempt on `/_qed/auth/login?returnTo=//evil.com` → succeeds with sanitized `/`
  match ← httpReq appProc.port "GET" "/_qed/auth/login?returnTo=//evil.com" with
  | .ok r =>
      c.checkEq "login returns 302 redirect" r.status 302
      let loc := (r.header? "location").getD ""
      c.check "login redirects to dev-auth /authorize with PKCE S256"
        (loc.startsWith (issuerUrl ++ "/authorize") && loc.contains "code_challenge_method=S256")
  | .error e => c.check "GET /_qed/auth/login open-redirect test" false e

  -- 8. Full OIDC Authorization Code + PKCE S256 login flow!
  let mut sessionCookie := ""
  match ← httpReq appProc.port "GET" "/_qed/auth/login?returnTo=/dashboard" with
  | .error e => c.check "OIDC login step 1" false e
  | .ok r1 =>
      c.checkEq "OIDC login step 1 status 302" r1.status 302
      let setCookies1 := extractSetCookies r1.headers
      let txCookie? := findCookieByName setCookies1 "qed_auth_tx"
      c.check "OIDC login sets HttpOnly qed_auth_tx cookie" txCookie?.isSome
      let authLoc := (r1.header? "location").getD ""
      -- Follow redirect to dev-auth /authorize with `&auto=1&sub=usr_alice&role=admin&email=alice@qed.dev&orgId=org_42`
      let authPath := stripHostPrefix authLoc ++ "&auto=1&sub=usr_alice&role=admin&email=alice%40qed.dev&orgId=org_42"
      match ← httpReq devAuthPort "GET" authPath with
      | .error e => c.check "OIDC authorize step 2" false e
      | .ok r2 =>
          c.checkEq "dev-auth /authorize auto redirects 302" r2.status 302
          let cbLoc := (r2.header? "location").getD ""
          let cbPath := stripHostPrefix cbLoc
          c.check "authorize redirects back to /_qed/auth/callback" (cbPath.startsWith "/_qed/auth/callback?")

          -- 8a. Negative test: tampered `state` fails with 403!
          let txCookie := txCookie?.getD ""
          match ← httpReq appProc.port "GET" (cbPath ++ "tampered") #[("Cookie", txCookie)] with
          | .ok rBadState => c.checkEq "callback rejects mismatched state (403)" rBadState.status 403
          | .error e => c.check "callback mismatched state check" false e

          -- 8b. Real callback with valid `code`, `state`, and `qed_auth_tx` cookie!
          match ← httpReq appProc.port "GET" cbPath #[("Cookie", txCookie)] with
          | .error e => c.check "OIDC callback step 3" false e
          | .ok r3 =>
              c.checkEq "OIDC callback succeeds with 302" r3.status 302
              c.checkEq "OIDC callback redirects to sanitized returnTo /dashboard"
                (r3.header? "location") (some "/dashboard")
              let setCookies3 := extractSetCookies r3.headers
              let sessC? := findCookieByName setCookies3 "qed_session"
              c.check "OIDC callback sets signed v2 qed_session cookie" (sessC?.any (·.contains "v2."))
              sessionCookie := sessC?.getD ""

  -- 9. Verify `/_qed/auth/me` with `qed_session` cookie returns authenticated admin claims
  if !sessionCookie.isEmpty then
    match ← httpReq appProc.port "GET" "/_qed/auth/me" #[("Cookie", sessionCookie)] with
    | .ok r =>
        c.checkEq "authenticated /_qed/auth/me returns 200" r.status 200
        c.check "authenticated /_qed/auth/me returns sub & admin role"
          (r.bodyStr.contains "\"usr_alice\"" && r.bodyStr.contains "\"admin\"" && r.bodyStr.contains "\"org_42\"")
    | .error e => c.check "authenticated /_qed/auth/me" false e

    -- 10. Call role-gated RPC `adminAction` with `qed_session` cookie → 200!
    let emptyProto := Qed.Proto.encode ()
    match ← httpReq appProc.port "POST" "/_qed/rpc/AuthApi/adminAction"
        #[("Content-Type", "application/x-protobuf"), ("Cookie", sessionCookie)] emptyProto with
    | .ok r =>
        c.checkEq "admin RPC with OIDC v2 cookie returns 200" r.status 200
    | .error e => c.check "admin RPC with OIDC v2 cookie" false e

    -- 10a. Verify `onCreateAccount` + `onSignIn` fired on 1st sign-in (`logins == 1`)!
    match ← httpReq appProc.port "POST" "/_qed/rpc/AuthApi/getProfile"
        #[("Content-Type", "application/x-protobuf"), ("Cookie", sessionCookie)] emptyProto with
    | .ok r =>
        c.checkEq "getProfile after 1st sign-in returns 200" r.status 200
        match Qed.Proto.decode (α := Option AuthChecks.AuthNotesDb.profiles) r.body with
        | .ok (some prof) =>
            c.checkEq "onCreateAccount stored profile id" prof.id "usr_alice"
            c.checkEq "onCreateAccount stored profile email" prof.email "alice@qed.dev"
            c.checkEq "onCreateAccount(0) + onSignIn(+1) -> logins == 1" prof.logins 1
        | .ok none => c.check "profile exists after 1st sign-in" false "got none"
        | .error e => c.check "decode getProfile after 1st sign-in" false e
    | .error e => c.check "getProfile after 1st sign-in" false e

    -- 11. Logout via `logoutUrl` (`GET /_qed/auth/logout?returnTo=/`) redirects 302 and clears cookie!
    match ← httpReq appProc.port "GET" (AuthChecks.CloudAuth.logoutUrl "/").raw
        #[("Cookie", sessionCookie)] with
    | .ok r =>
        c.checkEq "GET logoutUrl(/) returns 302" r.status 302
        c.checkEq "GET logoutUrl(/) redirects to /" (r.header? "location") (some "/")
        let scs := extractSetCookies r.headers
        c.check "GET logoutUrl emits Max-Age=0 clear cookie" (scs.any fun s => s.contains "qed_session=" && s.contains "Max-Age=0")
    | .error e => c.check "GET logoutUrl(/)" false e

    -- 11a. POST logout (without returnTo) also clears cookie and returns 200 JSON
    match ← httpReq appProc.port "POST" "/_qed/auth/logout"
        #[("Cookie", sessionCookie), ("Origin", s!"http://127.0.0.1:{appProc.port}")] with
    | .ok r =>
        c.checkEq "POST /_qed/auth/logout returns 200" r.status 200
        let scs := extractSetCookies r.headers
        c.check "logout emits Max-Age=0 clear cookie" (scs.any fun s => s.contains "qed_session=" && s.contains "Max-Age=0")
    | .error e => c.check "POST /_qed/auth/logout" false e

    -- 11b. Second OIDC sign-in as Alice: `onCreateAccount` must NOT re-run; `onSignIn` increments `logins` to 2!
    match ← httpReq appProc.port "GET" "/_qed/auth/login?returnTo=/" with
    | .error e => c.check "2nd OIDC login step 1" false e
    | .ok r1b =>
        let txCookie2 := (findCookieByName (extractSetCookies r1b.headers) "qed_auth_tx").getD ""
        let authPath2 := stripHostPrefix ((r1b.header? "location").getD "") ++
          "&auto=1&sub=usr_alice&role=admin&email=alice%40qed.dev&orgId=org_42"
        match ← httpReq devAuthPort "GET" authPath2 with
        | .error e => c.check "2nd OIDC authorize step 2" false e
        | .ok r2b =>
            let cbPath2 := stripHostPrefix ((r2b.header? "location").getD "")
            match ← httpReq appProc.port "GET" cbPath2 #[("Cookie", txCookie2)] with
            | .error e => c.check "2nd OIDC callback step 3" false e
            | .ok r3b =>
                c.checkEq "2nd OIDC callback succeeds with 302" r3b.status 302
                let sessCookie2 := (findCookieByName (extractSetCookies r3b.headers) "qed_session").getD ""
                match ← httpReq appProc.port "POST" "/_qed/rpc/AuthApi/getProfile"
                    #[("Content-Type", "application/x-protobuf"), ("Cookie", sessCookie2)] emptyProto with
                | .ok rp2 =>
                    c.checkEq "getProfile after 2nd sign-in returns 200" rp2.status 200
                    match Qed.Proto.decode (α := Option AuthChecks.AuthNotesDb.profiles) rp2.body with
                    | .ok (some prof2) =>
                        c.checkEq "2nd sign-in skips onCreateAccount and increments logins == 2" prof2.logins 2
                    | .ok none => c.check "profile exists after 2nd sign-in" false "got none"
                    | .error e => c.check "decode getProfile after 2nd sign-in" false e
                | .error e => c.check "getProfile after 2nd sign-in" false e

  -- 12. Bearer ES256 JWT mode (Firebase/Supabase/Clerk style): member rejected (403), admin allowed (200)!
  let mintBearer (sub role : String) : IO (Option String) := do
    let body := encodeFormBody [
      ("grant_type", "direct_dev_token"),
      ("audience", "qed-cloud-test"),
      ("sub", sub),
      ("role", role),
      ("email", s!"{sub}@qed.dev")
    ]
    match ← httpReq devAuthPort "POST" "/token"
        #[("Content-Type", "application/x-www-form-urlencoded")] body.toUTF8 with
    | .ok r =>
        if r.status == 200 then
          return (Qed.Json.parse r.bodyStr).toOption.bind (·.get? "id_token") |>.bind (·.str?)
        else return none
    | .error _ => return none

  let emptyProto := Qed.Proto.encode ()
  match ← mintBearer "usr_bob" "member" with
  | none => c.check "mint member ES256 JWT" false
  | some memberJwt =>
      -- Member can call `whoami` (200)
      match ← httpReq appProc.port "POST" "/_qed/rpc/AuthApi/whoami"
          #[("Content-Type", "application/x-protobuf"), ("Authorization", "Bearer " ++ memberJwt)] emptyProto with
      | .ok r => c.checkEq "member Bearer ES256 JWT passes whoami (200)" r.status 200
      | .error e => c.check "member Bearer whoami" false e
      -- Member is forbidden from `adminAction` (403)
      match ← httpReq appProc.port "POST" "/_qed/rpc/AuthApi/adminAction"
          #[("Content-Type", "application/x-protobuf"), ("Authorization", "Bearer " ++ memberJwt)] emptyProto with
      | .ok r => c.checkEq "member Bearer ES256 JWT blocked on adminAction (403)" r.status 403
      | .error e => c.check "member Bearer adminAction" false e

  match ← mintBearer "usr_root" "admin" with
  | none => c.check "mint admin ES256 JWT" false
  | some adminJwt =>
      match ← httpReq appProc.port "POST" "/_qed/rpc/AuthApi/adminAction"
          #[("Content-Type", "application/x-protobuf"), ("Authorization", "Bearer " ++ adminJwt)] emptyProto with
      | .ok r => c.checkEq "admin Bearer ES256 JWT passes adminAction (200)" r.status 200
      | .error e => c.check "admin Bearer adminAction" false e

  -- 13. PKCE S256 enforcement test on dev-auth `/token`: wrong `code_verifier` fails with 400!
  let chal := base64UrlEncode (← Prim.sha256 "correct-verifier-123".toUTF8)
  let pkceAuthPath := s!"/authorize?auto=1&client_id=qed-cloud-test&redirect_uri=http%3A%2F%2F127.0.0.1%3A9999%2Fcb&state=s1&nonce=n1&code_challenge={chal}"
  match ← httpReq devAuthPort "GET" pkceAuthPath with
  | .ok r =>
      let loc := (r.header? "location").getD ""
      let q := match loc.splitOn "?" with | _ :: qs => String.intercalate "?" qs | _ => ""
      let code := ((parseQueryParams q).find? (·.1 == "code")).map Prod.snd |>.getD ""
      let badForm := encodeFormBody [
        ("grant_type", "authorization_code"),
        ("code", code),
        ("redirect_uri", "http://127.0.0.1:9999/cb"),
        ("client_id", "qed-cloud-test"),
        ("code_verifier", "WRONG-verifier")
      ]
      match ← httpReq devAuthPort "POST" "/token"
          #[("Content-Type", "application/x-www-form-urlencoded")] badForm.toUTF8 with
      | .ok rt => c.checkEq "PKCE S256 rejects wrong code_verifier (400)" rt.status 400
      | .error e => c.check "PKCE wrong verifier check" false e
  | .error e => c.check "PKCE authorize setup" false e

  -- Clean teardown (prevents hanging background child processes!)
  appProc.stop
  devAuthProc.stop
  rmRf dbPath

def run : IO Bool := do
  let c ← mkChecker "auth-and-deploy"
  testCryptoAndJwtCore c
  testOidcFlowAndDeployManifest c
  c.finish

end Tests.Native.AuthAndDeploy
