import Qed
open Qed

namespace AuthChecks

/-! ## Compile-Time & Kernel Proofs for Verified OIDC Auth & Deploy Manifests -/

auth CloudAuth:
  issuer    env("QED_AUTH_ISSUER") ?? "http://127.0.0.1:8001"
  audience  env("QED_AUTH_AUDIENCE") ?? "qed-cloud-test"
  clientId  env("QED_AUTH_CLIENT_ID") ?? "qed-cloud-test"
  providers [email, google, github]
  session   ttl = 7200
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
  table profiles:
    id     : String primary_key where 1 <= id.length <= 128
    email  : String             where email.length <= 254
    logins : Nat
    policy read, write requires some(row.id) == ctx.userId

server AuthApi:
  use auth : CloudAuth
  use db   : AuthNotesDb
  state adminCalls : Nat = 0
  invariant nonNegCalls: adminCalls >= 0
  invariant adminOnly: mutating adminCalls requires ctx.userId != none and ctx.hasClaim("role", "admin")

  onCreateAccount(user):
    if 1 <= user.id.length <= 128 and user.email.length <= 254:
      await db.profiles.insert(id = user.id, email = user.email, logins = 0)?

  onSignIn(user):
    if user.email.length <= 254:
      await db.profiles.updateOne(where = r => r.id == user.id, set = r => { email = user.email, logins = r.logins + 1 })?

  def whoami() -> CloudAuth.User!:
    requires ctx.userId != none
    if let some(u) = CloudAuth.fromCtx(ctx): return u
    return fail(.unauthorized)

  def getProfile() -> AuthNotesDb.profiles?!:
    requires ctx.userId != none
    if let some(uid) = ctx.userId:
      return await db.profiles.findOne(where = r => r.id == uid)?
    return none

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
      <a href={CloudAuth.logoutUrl("/")}>Sign out</a>
      <p>{status}</p>
    </main>

fullstack AuthApp:
  server AuthApi
  client AuthShell
  title "Auth Test App"

-- Verify `<Auth>.User` codecs, JWT algorithm & open-redirect security theorems, and `fromCtx`
example : Qed.LawfulJson CloudAuth.User × Qed.LawfulProto CloudAuth.User := (inferInstance, inferInstance)
example : Qed.Auth.parseJwtAlg "none" = none ∧ Qed.Auth.parseJwtAlg "HS256" = none :=
  ⟨Qed.Auth.parseJwtAlg_rejects_none, Qed.Auth.parseJwtAlg_rejects_hs256⟩
example : Qed.Auth.isSafeReturnTo "//evil.com" = false ∧ Qed.Auth.isSafeReturnTo "javascript:alert(1)" = false :=
  ⟨Qed.Auth.isSafeReturnTo_rejects_protocol_relative, Qed.Auth.isSafeReturnTo_rejects_javascript⟩
example : (CloudAuth.loginUrl "//evil.com").raw = (CloudAuth.loginUrl "/").raw ∧
    (CloudAuth.logoutUrl "//evil.com").raw = (CloudAuth.logoutUrl "/").raw := ⟨rfl, rfl⟩
#guard Qed.Auth.isSafeReturnTo "/dashboard?tab=1" &&
  (CloudAuth.logoutUrl "/bye").raw == "/_qed/auth/logout?returnTo=%2Fbye" &&
  Qed.Auth.sanitizeReturnTo (some "//evil.com") == "/" &&
  Qed.Auth.sanitizeReturnTo (some "/dashboard") == "/dashboard" &&
  CloudAuth.fromCtx { userId := some "u1", claims := [("email", "a@b.c"), ("role", "admin"), ("orgId", "org_1"), ("email_verified", "true")] } ==
    some { id := "u1", email := "a@b.c", role := "admin", orgId := some "org_1", verified := true }

/-- error: `onSignIn` in `server MissingAuthServer` requires `use auth : <Auth>` -/
#guard_msgs in
server MissingAuthServer:
  onSignIn(user): pass

end AuthChecks
