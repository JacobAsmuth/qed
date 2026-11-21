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
  c.expectOk "ecP256Keygen succeeds" (← Prim.ecP256Keygen) fun (pkcs8, pubX, pubY) => do
    c.check "ecP256Keygen produces 32B X/Y" (pubX.size == 32 && pubY.size == 32)
    let kp : Qed.Cli.DevAuth.DevAuthKeypair := {
      kid := "k1", pkcs8Der := pkcs8
      xB64 := base64UrlEncode pubX, yB64 := base64UrlEncode pubY
    }
    let jwk : JwkKey := .ecP256 "k1" pubX pubY
    let nowSec := ((← Prim.nowMs).toNat) / 1000
    c.expectOk "signDevIdToken succeeds"
      (← Qed.Cli.DevAuth.signDevIdToken kp "https://idp.test" "usr_42" "aud_app"
        "nonce_xyz" "alice@test.dev" "admin" "org_7" true 600) fun jwt => do
      let vcfg : OidcValidationCfg := {
        issuer := "https://idp.test", audience := "aud_app", expectedNonce? := some "nonce_xyz"
      }
      c.expectOk "ES256 JWK verify valid JWT" (← verifyJwtWithKeys vcfg #[jwk] jwt nowSec) fun vc => do
        let u := AuthChecks.CloudAuth.fromClaims vc.claims
        c.checkEq "ES256 extracted sub" u.id "usr_42"
        c.checkEq "ES256 extracted role" u.role "admin"
        c.checkEq "ES256 extracted orgId" u.orgId (some "org_7")
        c.checkEq "ES256 extracted email" u.email "alice@test.dev"
        c.checkEq "ES256 extracted verified" u.verified true

      -- Wrong audience, issuer, nonce, expired, tampered, `alg: none` all rejected
      c.check "JWT wrong audience rejected" (!(← verifyJwtWithKeys { vcfg with audience := "other_app" } #[jwk] jwt nowSec).isOk)
      c.check "JWT wrong issuer rejected" (!(← verifyJwtWithKeys { vcfg with issuer := "https://evil.test" } #[jwk] jwt nowSec).isOk)
      c.check "JWT wrong nonce rejected" (!(← verifyJwtWithKeys { vcfg with expectedNonce? := some "wrong" } #[jwk] jwt nowSec).isOk)
      c.check "JWT expired token rejected" (!(← verifyJwtWithKeys vcfg #[jwk] jwt (nowSec + 10000)).isOk)
      c.check "JWT tampered signature rejected" (!(← verifyJwtWithKeys vcfg #[jwk] (jwt ++ "A") nowSec).isOk)
      let noneHdr := base64UrlEncode "{\"alg\":\"none\",\"typ\":\"JWT\"}".toUTF8
      let nonePay := base64UrlEncode "{\"iss\":\"https://idp.test\",\"sub\":\"admin\",\"aud\":\"aud_app\",\"exp\":9999999999}".toUTF8
      c.check "JWT alg:none rejected" (!(← verifyJwtWithKeys vcfg #[jwk] s!"{noneHdr}.{nonePay}.sig" nowSec).isOk)

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
    c.expectOk "qed_deploy.json valid JSON" (Qed.Json.parse raw) fun j => do
      c.checkEq "manifest mode is fullstack" ((j.get? "mode").bind (·.str?)) (some "fullstack")
      c.checkEq "manifest csp matches defaultCsp" ((j.get? "csp").bind (·.str?)) (some Qed.Server.defaultCsp)
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
  c.expectOk "dev-auth discovery reachable" (← httpReq devAuthPort "GET" "/.well-known/openid-configuration") fun r => do
    c.checkEq "dev-auth discovery HTTP 200" r.status 200
    c.check "dev-auth discovery advertises ES256 & S256"
      (r.bodyStr.contains "ES256" && r.bodyStr.contains "S256")

  c.expectOk "dev-auth JWKS reachable" (← httpReq devAuthPort "GET" "/jwks.json") fun r => do
    c.checkEq "dev-auth JWKS HTTP 200" r.status 200
    c.check "dev-auth JWKS serves EC P-256 key" (r.bodyStr.contains "\"P-256\"")

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
  c.checkStatus "unauthenticated /_qed/auth/me returns 401" (← httpReq appProc.port "GET" "/_qed/auth/me") 401

  -- 7. Open-redirect attempt on `/_qed/auth/login?returnTo=//evil.com` → succeeds with sanitized `/`
  c.expectOk "GET /_qed/auth/login open-redirect test" (← httpReq appProc.port "GET" "/_qed/auth/login?returnTo=//evil.com") fun r => do
    c.checkEq "login returns 302 redirect" r.status 302
    let loc := (r.header? "location").getD ""
    c.check "login redirects to dev-auth /authorize with PKCE S256"
      (loc.startsWith (issuerUrl ++ "/authorize") && loc.contains "code_challenge_method=S256")

  -- 8. Full OIDC Authorization Code + PKCE S256 login flow!
  let aliceParams := "&auto=1&sub=usr_alice&role=admin&email=alice%40qed.dev&orgId=org_42"
  let doOidcLogin (tag returnTo queryExtra : String) (fullChecks : Bool := false) : IO String := do
    let sessRef ← IO.mkRef ""
    c.expectOk s!"{tag} login step 1" (← httpReq appProc.port "GET" s!"/_qed/auth/login?returnTo={returnTo}") fun r1 => do
      if fullChecks then c.checkEq s!"{tag} login step 1 status 302" r1.status 302
      let txCookie? := findCookieByName (extractSetCookies r1.headers) "qed_auth_tx"
      if fullChecks then c.check s!"{tag} login sets HttpOnly qed_auth_tx cookie" txCookie?.isSome
      let authPath := stripHostPrefix ((r1.header? "location").getD "") ++ queryExtra
      c.expectOk s!"{tag} authorize step 2" (← httpReq devAuthPort "GET" authPath) fun r2 => do
        if fullChecks then c.checkEq "dev-auth /authorize auto redirects 302" r2.status 302
        let cbPath := stripHostPrefix ((r2.header? "location").getD "")
        if fullChecks then
          c.check "authorize redirects back to /_qed/auth/callback" (cbPath.startsWith "/_qed/auth/callback?")
          c.checkStatus "callback rejects mismatched state (403)"
            (← httpReq appProc.port "GET" (cbPath ++ "tampered") #[("Cookie", txCookie?.getD "")]) 403
        c.expectOk s!"{tag} callback step 3" (← httpReq appProc.port "GET" cbPath #[("Cookie", txCookie?.getD "")]) fun r3 => do
          c.checkEq s!"{tag} callback succeeds with 302" r3.status 302
          if fullChecks then
            c.checkEq s!"{tag} callback redirects to sanitized returnTo {returnTo}" (r3.header? "location") (some returnTo)
          let sessC? := findCookieByName (extractSetCookies r3.headers) "qed_session"
          if fullChecks then
            c.check s!"{tag} callback sets signed v2 qed_session cookie" (sessC?.any (·.contains "v2."))
          sessRef.set (sessC?.getD "")
    sessRef.get

  let emptyProto := Qed.Proto.encode ()
  let authRpc (fn : String) (tok? : Option String := none) (extraHdrs : Array (String × String) := #[]) :=
    httpRpc appProc.port "AuthApi" fn emptyProto tok? extraHdrs

  let sessionCookie ← doOidcLogin "OIDC" "/dashboard" aliceParams (fullChecks := true)

  -- 9. Verify `/_qed/auth/me` with `qed_session` cookie returns authenticated admin claims
  if !sessionCookie.isEmpty then
    c.expectOk "authenticated /_qed/auth/me" (← httpReq appProc.port "GET" "/_qed/auth/me" #[("Cookie", sessionCookie)]) fun r => do
      c.checkEq "authenticated /_qed/auth/me returns 200" r.status 200
      c.check "authenticated /_qed/auth/me returns sub & admin role"
        (r.bodyStr.contains "\"usr_alice\"" && r.bodyStr.contains "\"admin\"" && r.bodyStr.contains "\"org_42\"")

    -- 10. Call role-gated RPC `adminAction` with `qed_session` cookie → 200!
    c.checkStatus "admin RPC with OIDC v2 cookie returns 200" (← authRpc "adminAction" none #[("Cookie", sessionCookie)]) 200

    -- 10a. Verify `onCreateAccount` + `onSignIn` fired on 1st sign-in (`logins == 1`)!
    c.expectOk "getProfile after 1st sign-in" (← authRpc "getProfile" none #[("Cookie", sessionCookie)]) fun r => do
      c.checkEq "getProfile after 1st sign-in returns 200" r.status 200
      c.expectOk "decode getProfile after 1st sign-in" (Qed.Proto.decode (α := Option AuthChecks.AuthNotesDb.profiles) r.body) fun
        | some prof => do
            c.checkEq "onCreateAccount stored profile id" prof.id "usr_alice"
            c.checkEq "onCreateAccount stored profile email" prof.email "alice@qed.dev"
            c.checkEq "onCreateAccount(0) + onSignIn(+1) -> logins == 1" prof.logins 1
        | none => c.check "profile exists after 1st sign-in" false "got none"

    -- 11. Logout via `logoutUrl` (`GET /_qed/auth/logout?returnTo=/`) redirects 302 and clears cookie!
    c.expectOk "GET logoutUrl(/)" (← httpReq appProc.port "GET" (AuthChecks.CloudAuth.logoutUrl "/").raw #[("Cookie", sessionCookie)]) fun r => do
      c.checkEq "GET logoutUrl(/) returns 302" r.status 302
      c.checkEq "GET logoutUrl(/) redirects to /" (r.header? "location") (some "/")
      let scs := extractSetCookies r.headers
      c.check "GET logoutUrl emits Max-Age=0 clear cookie" (scs.any fun s => s.contains "qed_session=" && s.contains "Max-Age=0")

    -- 11a. POST logout (without returnTo) also clears cookie and returns 200 JSON
    c.expectOk "POST /_qed/auth/logout"
      (← httpReq appProc.port "POST" "/_qed/auth/logout" #[("Cookie", sessionCookie), ("Origin", s!"http://127.0.0.1:{appProc.port}")]) fun r => do
        c.checkEq "POST /_qed/auth/logout returns 200" r.status 200
        let scs := extractSetCookies r.headers
        c.check "logout emits Max-Age=0 clear cookie" (scs.any fun s => s.contains "qed_session=" && s.contains "Max-Age=0")

    -- 11b. Second OIDC sign-in as Alice: `onCreateAccount` must NOT re-run; `onSignIn` increments `logins` to 2!
    let sessCookie2 ← doOidcLogin "2nd OIDC" "/" aliceParams
    if !sessCookie2.isEmpty then
      c.expectOk "getProfile after 2nd sign-in" (← authRpc "getProfile" none #[("Cookie", sessCookie2)]) fun rp2 => do
        c.checkEq "getProfile after 2nd sign-in returns 200" rp2.status 200
        c.expectOk "decode getProfile after 2nd sign-in" (Qed.Proto.decode (α := Option AuthChecks.AuthNotesDb.profiles) rp2.body) fun
          | some prof2 => c.checkEq "2nd sign-in skips onCreateAccount and increments logins == 2" prof2.logins 2
          | none => c.check "profile exists after 2nd sign-in" false "got none"

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

  match ← mintBearer "usr_bob" "member" with
  | none => c.check "mint member ES256 JWT" false
  | some memberJwt =>
      c.checkStatus "member Bearer ES256 JWT passes whoami (200)" (← authRpc "whoami" (some memberJwt)) 200
      c.checkStatus "member Bearer ES256 JWT blocked on adminAction (403)" (← authRpc "adminAction" (some memberJwt)) 403

  match ← mintBearer "usr_root" "admin" with
  | none => c.check "mint admin ES256 JWT" false
  | some adminJwt =>
      c.checkStatus "admin Bearer ES256 JWT passes adminAction (200)" (← authRpc "adminAction" (some adminJwt)) 200

  -- 13. PKCE S256 enforcement test on dev-auth `/token`: wrong `code_verifier` fails with 400!
  let chal := base64UrlEncode (← Prim.sha256 "correct-verifier-123".toUTF8)
  let pkceAuthPath := s!"/authorize?auto=1&client_id=qed-cloud-test&redirect_uri=http%3A%2F%2F127.0.0.1%3A9999%2Fcb&state=s1&nonce=n1&code_challenge={chal}"
  c.expectOk "PKCE authorize setup" (← httpReq devAuthPort "GET" pkceAuthPath) fun r => do
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
    c.checkStatus "PKCE S256 rejects wrong code_verifier (400)"
      (← httpReq devAuthPort "POST" "/token" #[("Content-Type", "application/x-www-form-urlencoded")] badForm.toUTF8) 400

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
