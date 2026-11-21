import Qed
open Qed

namespace AuthChecks

/-! ## Compile-Time & Kernel Proofs for Verified OIDC Auth & Deploy Manifests -/

auth CloudAuth:
  issuer        env("QED_AUTH_ISSUER") ?? "http://127.0.0.1:8001"
  audience      env("QED_AUTH_AUDIENCE") ?? "qed-cloud-test"
  client_id     env("QED_AUTH_CLIENT_ID") ?? "qed-cloud-test"
  providers     [email, google, github]
  session       ttl = 7200
  claims:
    email    : String = ""
    role     : String = "member"
    orgId    : String?
    verified : Bool   = false

external BillingApi:
  base "https://billing.example.com"
  get "/status" status() -> Bool

database AuthNotesDb:
  url secret("AUTH_NOTES_DB_URL")
  dev sqlite ".qed/test_auth_notes.db"

  table notes:
    id      : Nat    primary_key
    ownerId : String immutable where 1 <= ownerId.length <= 64
    body    : String           where 1 <= body.length <= 500

    policy read, write requires some(row.ownerId) == ctx.userId

server AuthApi:
  use auth : CloudAuth
  use db   : AuthNotesDb

  state adminCalls : Nat = 0
  invariant nonNegCalls: adminCalls >= 0
  invariant adminOnly: mutating adminCalls requires ctx.userId != none and ctx.hasClaim("role", "admin")

  def whoami() -> CloudAuth.User!:
    requires ctx.userId != none
    if let some(u) = CloudAuth.fromCtx(ctx):
      return u
    return fail(.unauthorized)

  def adminAction() -> Nat!:
    requires ctx.userId != none
    requires ctx.hasClaim("role", "admin")
    adminCalls += 1
    return adminCalls

  def pingBilling() -> Bool!:
    return await BillingApi.status()?

component AuthShell:
  session user
  state status = "ready"
  view:
    <main>
      <h1>Auth Test</h1>
      <a href={CloudAuth.loginUrl("/dashboard")}>Sign in</a>
      <p>{status}</p>
    </main>

fullstack AuthApp:
  server AuthApi
  client AuthShell
  title "Auth Test App"

-- Verify `<Auth>.User` codecs satisfy `LawfulJson` & `LawfulProto`
example : Qed.LawfulJson CloudAuth.User := inferInstance
example : Qed.LawfulProto CloudAuth.User := inferInstance

-- Verify compile-time JWT algorithm & redirect security theorems
example : Qed.Auth.parseJwtAlg "none" = none := Qed.Auth.parseJwtAlg_rejects_none
example : Qed.Auth.parseJwtAlg "HS256" = none := Qed.Auth.parseJwtAlg_rejects_hs256
example : Qed.Auth.isSafeReturnTo "//evil.com" = false := Qed.Auth.isSafeReturnTo_rejects_protocol_relative
example : Qed.Auth.isSafeReturnTo "javascript:alert(1)" = false := Qed.Auth.isSafeReturnTo_rejects_javascript
example : Qed.Auth.isSafeReturnTo "/dashboard?tab=1" = true := by decide

-- Verify `CloudAuth.loginUrl` returns a verified `Qed.Url` and open redirects sanitize to `/`
example : (CloudAuth.loginUrl "//evil.com").raw = (CloudAuth.loginUrl "/").raw := rfl
example : Qed.Auth.sanitizeReturnTo (some "//evil.com") = "/" := by decide
example : Qed.Auth.sanitizeReturnTo (some "/dashboard") = "/dashboard" := by decide

-- Verify `CloudAuth.fromCtx` extracts typed claims deterministically (including `email_verified` alias)
example :
    CloudAuth.fromCtx { userId := some "u1", claims := [("email", "a@b.c"), ("role", "admin"), ("orgId", "org_1"), ("email_verified", "true")] } =
    some { id := "u1", email := "a@b.c", role := "admin", orgId := some "org_1", verified := true } := by decide

end AuthChecks
