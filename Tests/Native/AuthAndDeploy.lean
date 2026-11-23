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

private def stripHostPrefix (url : String) : String :=
  match url.splitOn "://" with
  | [_, rest] => match rest.splitOn "/" with | _ :: segs => "/" ++ String.intercalate "/" segs | [] => "/"
  | _ => url

private def testCryptoAndJwtCore (c : TestChecker) : IO Unit := do
  -- 1. Generate real ephemeral P-256 keypair & verify ES256 JWT via `verifyJwtWithKeys`
  c.expectOk "ecP256Keygen succeeds" (← Prim.ecP256Keygen) fun (pkcs8, pubX, pubY) => do
    c.check "ecP256Keygen produces 32B X/Y" (pubX.size == 32 && pubY.size == 32)
    let kp : Qed.Cli.DevAuth.DevAuthKeypair := { kid := "k1", pkcs8Der := pkcs8, xB64 := base64UrlEncode pubX, yB64 := base64UrlEncode pubY }
    let (jwk, nowSec) := (JwkKey.ecP256 "k1" pubX pubY, (← Prim.nowMs).toNat / 1000)
    c.expectOk "signDevIdToken succeeds"
      (← Qed.Cli.DevAuth.signDevIdToken kp "https://idp.test" "usr_42" "aud_app" "nonce_xyz" "alice@test.dev" "admin" "org_7" true 600) fun jwt => do
      let vcfg : OidcValidationCfg := { issuer := "https://idp.test", audience := "aud_app", expectedNonce? := some "nonce_xyz" }
      c.expectOk "ES256 JWK verify valid JWT" (← verifyJwtWithKeys vcfg #[jwk] jwt nowSec) fun vc => do
        let u := AuthChecks.CloudAuth.fromClaims vc.claims
        c.checkEq "ES256 extracted claims (sub, role, orgId, email, verified)"
          (u.id, u.role, u.orgId, u.email, u.verified) ("usr_42", "admin", some "org_7", "alice@test.dev", true)

      let noneHdr := base64UrlEncode "{\"alg\":\"none\",\"typ\":\"JWT\"}".toUTF8
      let nonePay := base64UrlEncode "{\"iss\":\"https://idp.test\",\"sub\":\"admin\",\"aud\":\"aud_app\",\"exp\":9999999999}".toUTF8
      let noneTok := s!"{noneHdr}.{nonePay}.sig"
      for (lbl, cfg, tok, ts) in [
          ("wrong audience", { vcfg with audience := "other_app" }, jwt, nowSec),
          ("wrong issuer", { vcfg with issuer := "https://evil.test" }, jwt, nowSec),
          ("wrong nonce", { vcfg with expectedNonce? := some "wrong" }, jwt, nowSec),
          ("expired token", vcfg, jwt, nowSec + 10000),
          ("tampered signature", vcfg, jwt ++ "A", nowSec),
          ("alg:none", vcfg, noneTok, nowSec)] do
        c.check s!"JWT {lbl} rejected" (!(← verifyJwtWithKeys cfg #[jwk] tok ts).isOk)

  -- 2. Base64URL round-trip & DeployManifest compile-time validation checks
  let sample := "hello+/world=123\x00\xff".toUTF8
  let enc := base64UrlEncode sample
  c.check "base64url has no + / =" (!enc.contains "+" && !enc.contains "/" && !enc.contains "=")
  c.checkEq "base64url round-trip" (base64UrlDecode enc) (.ok sample)
  c.check "DeployManifest rejects bad version" (!({ version := 2 } : Qed.Deploy.DeployManifest).validate.isOk)
  c.check "DeployManifest rejects unsafe auth callback"
    (!(Qed.Deploy.validateAuthManifest { name := "Bad", issuerEnv := "QED_AUTH_ISSUER", audienceEnv := "QED_AUTH_AUDIENCE", callbackPath := "//evil.com/cb" }).isOk)

private def testOidcFlowAndDeployManifest (c : TestChecker) : IO Unit := do
  -- 1. Build `Tests.AuthChecks` fullstack app & verify `qed_deploy.json` manifest + leak gate
  let some outDir ← buildDevApp "Tests.AuthChecks"
    | do c.check "buildDevApp Tests.AuthChecks" false; return
  c.check "buildDevApp Tests.AuthChecks succeeded" true

  let manifestPath := outDir ++ "/qed_deploy.json"
  let existsM ← (System.FilePath.mk manifestPath).pathExists
  c.check "qed_deploy.json emitted on build" existsM
  if existsM then
    c.expectOk "qed_deploy.json valid JSON" (Qed.Json.parse (← IO.FS.readFile manifestPath)) fun j => do
      c.checkJsonStr "manifest mode is fullstack" j "mode" "fullstack"
      c.checkJsonStr "manifest csp matches defaultCsp" j "csp" Qed.Server.defaultCsp
      c.checkJsonStr "manifest auth.name" j "auth.name" "CloudAuth"
      c.checkJsonStr "manifest auth.callbackPath" j "auth.callbackPath" "/_qed/auth/callback"
      c.checkJsonArr "manifest auth.claims has 4 typed claims" j "auth.claims" (·.length == 4)
      c.checkJsonArr "manifest auth.providers has 3 providers" j "auth.providers" (·.length == 3)
      c.checkJsonArr "manifest egress contains BillingApi origin" j "egress" (·.any (·.str? == some "https://billing.example.com"))
      c.checkJsonArr "manifest databases contains AuthNotesDb" j "databases" (·.any fun d => (d.atPath "name").bind (·.str?) == some "AuthNotesDb")
      c.checkJsonArr "manifest secrets contains AUTH_NOTES_DB_URL" j "secrets" (·.any (·.str? == some "AUTH_NOTES_DB_URL"))

  checkLeakGate c "Tests.AuthChecks" #["AuthChecks.CloudAuth.config", "AuthChecks.CloudAuth.secrets"]

  -- 2. Spawn `qed dev-auth` ephemeral ES256 OIDC IdP & `Tests.AuthChecks` fullstack server
  let devAuthPort ← Prim.freePort
  withNativeBin c "qed dev-auth started cleanly" (← qedBinPath) #["dev-auth", toString devAuthPort] devAuthPort #[] fun _ => do
    c.checkHttp "dev-auth discovery" (← httpReq devAuthPort "GET" "/.well-known/openid-configuration") (contains := ["ES256", "S256"])
    c.checkHttp "dev-auth JWKS" (← httpReq devAuthPort "GET" "/jwks.json") (contains := ["\"P-256\""])

    let issuerUrl := s!"http://127.0.0.1:{devAuthPort}"
    let postTokenForm (pairs : List (String × String)) :=
      httpReq devAuthPort "POST" "/token" #[("Content-Type", "application/x-www-form-urlencoded")] (encodeFormBody pairs).toUTF8
    withTempDir "qed-auth-test" fun tmpDir => do
      withNativeServer c "AuthApp native server started cleanly" outDir #[
        ("QED_AUTH_ISSUER", some issuerUrl), ("QED_AUTH_AUDIENCE", some "qed-cloud-test"),
        ("QED_AUTH_CLIENT_ID", some "qed-cloud-test"), ("AUTH_NOTES_DB_URL", some s!"sqlite://{tmpDir}/auth.db")
      ] (dev := true) fun appProc => do
        -- 3. Unauthenticated `/_qed/auth/me` & open-redirect check
        c.checkStatus "unauthenticated /_qed/auth/me returns 401" (← httpReq appProc.port "GET" "/_qed/auth/me") 401
        c.checkHttp "GET /_qed/auth/login open-redirect test" (← httpReq appProc.port "GET" "/_qed/auth/login?returnTo=//evil.com")
          (status? := some 302) (extra := fun r =>
            let loc := (r.header? "location").getD ""
            c.check "login redirects to dev-auth /authorize with PKCE S256" (loc.startsWith (issuerUrl ++ "/authorize") && loc.contains "code_challenge_method=S256"))

        -- 4. Full OIDC Authorization Code + PKCE S256 login flow
        let aliceParams := "&auto=1&sub=usr_alice&role=admin&email=alice%40qed.dev&orgId=org_42"
        let doOidcLogin (tag returnTo queryExtra : String) (fullChecks : Bool := false) : IO String := do
          let .ok r1 ← httpReq appProc.port "GET" s!"/_qed/auth/login?returnTo={returnTo}"
            | c.check s!"{tag} login step 1" false; return ""
          if fullChecks then c.checkEq s!"{tag} login step 1 status 302" r1.status 302
          let txCookie? := r1.cookie? "qed_auth_tx"
          if fullChecks then c.check s!"{tag} login sets HttpOnly qed_auth_tx cookie" txCookie?.isSome
          let .ok r2 ← httpReq devAuthPort "GET" (stripHostPrefix ((r1.header? "location").getD "") ++ queryExtra)
            | c.check s!"{tag} authorize step 2" false; return ""
          if fullChecks then c.checkEq "dev-auth /authorize auto redirects 302" r2.status 302
          let cbPath := stripHostPrefix ((r2.header? "location").getD "")
          if fullChecks then
            c.check "authorize redirects back to /_qed/auth/callback" (cbPath.startsWith "/_qed/auth/callback?")
            c.checkStatus "callback rejects mismatched state (403)"
              (← httpReq appProc.port "GET" (cbPath ++ "tampered") #[("Cookie", txCookie?.getD "")]) 403
          let .ok r3 ← httpReq appProc.port "GET" cbPath #[("Cookie", txCookie?.getD "")]
            | c.check s!"{tag} callback step 3" false; return ""
          c.checkEq s!"{tag} callback succeeds with 302" r3.status 302
          if fullChecks then c.checkEq s!"{tag} callback redirects to sanitized returnTo {returnTo}" (r3.header? "location") (some returnTo)
          let sessC? := r3.cookie? "qed_session"
          if fullChecks then c.check s!"{tag} callback sets signed v2 qed_session cookie" (sessC?.any (·.contains "v2."))
          return sessC?.getD ""

        let authRpc (fn : String) (tok? : Option String := none) (extraHdrs : Array (String × String) := #[]) :=
          httpRpc appProc.port "AuthApi" fn (Qed.Proto.encode ()) tok? extraHdrs
        let checkProfile (tag cookie : String) (k : AuthChecks.AuthNotesDb.profiles → IO Unit) : IO Unit := do
          c.checkHttp s!"getProfile after {tag}" (← authRpc "getProfile" none #[("Cookie", cookie)]) (extra := fun r =>
            c.expectOk s!"decode getProfile after {tag}" (Qed.Proto.decode (α := Option AuthChecks.AuthNotesDb.profiles) r.body) fun
              | some prof => k prof | none => c.check s!"profile exists after {tag}" false "got none")

        let sessionCookie ← doOidcLogin "OIDC" "/dashboard" aliceParams (fullChecks := true)
        if !sessionCookie.isEmpty then
          c.checkHttp "authenticated /_qed/auth/me" (← httpReq appProc.port "GET" "/_qed/auth/me" #[("Cookie", sessionCookie)])
            (contains := ["\"usr_alice\"", "\"admin\"", "\"org_42\""])
          c.checkStatus "admin RPC with OIDC v2 cookie returns 200" (← authRpc "adminAction" none #[("Cookie", sessionCookie)]) 200
          checkProfile "1st sign-in" sessionCookie fun prof =>
            c.checkEq "onCreateAccount(0)+onSignIn(+1) stored profile" (prof.id, prof.email, prof.logins) ("usr_alice", "alice@qed.dev", 1)

          -- Logout via GET `logoutUrl` & POST `/_qed/auth/logout`, then 2nd sign-in increments `logins` to 2
          c.checkHttp "GET logoutUrl(/)" (← httpReq appProc.port "GET" (AuthChecks.CloudAuth.logoutUrl "/").raw #[("Cookie", sessionCookie)])
            (status? := some 302) (headers := [("location", some "/")])
            (extra := (·.checkCookieFlag c "GET logoutUrl emits Max-Age=0 clear cookie" ["qed_session=", "Max-Age=0"]))
          c.checkHttp "POST /_qed/auth/logout"
            (← httpReq appProc.port "POST" "/_qed/auth/logout" #[("Cookie", sessionCookie), ("Origin", s!"http://127.0.0.1:{appProc.port}")])
            (extra := (·.checkCookieFlag c "logout emits Max-Age=0 clear cookie" ["qed_session=", "Max-Age=0"]))
          let sessCookie2 ← doOidcLogin "2nd OIDC" "/" aliceParams
          if !sessCookie2.isEmpty then
            checkProfile "2nd sign-in" sessCookie2 fun prof2 =>
              c.checkEq "2nd sign-in skips onCreateAccount and increments logins == 2" prof2.logins 2

        -- 5. Bearer ES256 JWT mode (member 403, admin 200) & PKCE S256 wrong verifier (400)
        for (sub, role, checkAdminWant, checkWhoami) in [("usr_bob", "member", 403, true), ("usr_root", "admin", 200, false)] do
          let tok? ← match ← postTokenForm [("grant_type", "direct_dev_token"), ("audience", "qed-cloud-test"), ("sub", sub), ("role", role), ("email", s!"{sub}@qed.dev")] with
            | .ok r => pure (if r.status == 200 then (Qed.Json.path? r.bodyStr "id_token").bind (·.str?) else none)
            | .error _ => pure none
          match tok? with
          | none => c.check s!"mint {role} ES256 JWT" false
          | some jwt =>
              if checkWhoami then c.checkStatus s!"{role} Bearer ES256 JWT passes whoami (200)" (← authRpc "whoami" (some jwt)) 200
              c.checkStatus s!"{role} Bearer ES256 JWT adminAction ({checkAdminWant})" (← authRpc "adminAction" (some jwt)) checkAdminWant

        let chal := base64UrlEncode (← Prim.sha256 "correct-verifier-123".toUTF8)
        let pkcePath := s!"/authorize?auto=1&client_id=qed-cloud-test&redirect_uri=http%3A%2F%2F127.0.0.1%3A9999%2Fcb&state=s1&nonce=n1&code_challenge={chal}"
        c.expectOk "PKCE authorize setup" (← httpReq devAuthPort "GET" pkcePath) fun r => do
          let code := ((parseQueryParams (splitPathQuery ((r.header? "location").getD "")).2).lookup "code").getD ""
          c.checkStatus "PKCE S256 rejects wrong code_verifier (400)" (← postTokenForm [
            ("grant_type", "authorization_code"), ("code", code),
            ("redirect_uri", "http://127.0.0.1:9999/cb"), ("client_id", "qed-cloud-test"), ("code_verifier", "WRONG-verifier")
          ]) 400

def run : IO Bool := do
  let c ← mkChecker "auth-and-deploy"
  testCryptoAndJwtCore c
  testOidcFlowAndDeployManifest c
  c.finish

end Tests.Native.AuthAndDeploy
