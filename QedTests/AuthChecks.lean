import Qed
import QedTests.CheckHelper
open Qed

namespace AuthChecks
/-- Documented OIDC auth configuration with inline metadata invariants. -/
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
  invariant shortSession: session_ttl <= 86400
  invariant hasGoogle: "google" in providers
  invariant notManaged: not is_managed
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
  onCreateAccount(user): if 1 <= user.id.length <= 128 and user.email.length <= 254: await db.profiles.insert(id = user.id, email = user.email, logins = 0)?
  onSignIn(user): if user.email.length <= 254: await db.profiles.updateOne(where = r => r.id == user.id, set = r => { email = user.email, logins = r.logins + 1 })?
  rpc whoami() -> CloudAuth.User!:
    requires ctx.userId != none
    if let some(u) = CloudAuth.fromCtx(ctx): return u
    return fail(.unauthorized)
  rpc getProfile() -> AuthNotesDb.profiles?!:
    requires ctx.userId != none
    if let some(uid) = ctx.userId: return await db.profiles.findOne(where = r => r.id == uid)?
    return none
  rpc doubleLogins() -> AuthNotesDb.profiles?!:
    requires ctx.userId != none
    if let some(uid) = ctx.userId: return await db.profiles.updateOne(where = r => r.id == uid, set = { logins *= 2, })?
    return none
  rpc adminAction() -> Nat!:
    requires ctx.userId != none, ctx.hasClaim("role", "admin")
    adminCalls += 1
    return adminCalls
  rpc pingBilling() -> Bool!: return await BillingApi.status()?
  rpc whoamiUser() -> String!:
    requires auth(user)
    return f"{user.id}:{user.role}"
  rpc approveInteractive() -> String!:
    requires auth, ctx.isSession, user.emailVerified
    return user.id
/-- Documented app router. -/
router AuthRoute:
  home      = "/"
  dashboard = "/dashboard"
  project   = "/projects/:slug"
component AuthShell:
  session user
  state status = "ready"
  view: <main><h1>Auth Test</h1><a href={CloudAuth.loginUrl("/dashboard")}>Sign in</a><a href={CloudAuth.loginUrl(AuthRoute.dashboard)}>Sign in typed</a><a href={CloudAuth.logoutUrl("/")}>Sign out</a><a href={CloudAuth.logoutUrl(AuthRoute.home)}>Sign out typed</a><p>{status}</p></main>
/-- Documented fullstack application wiring. -/
fullstack AuthApp:
  server AuthApi
  client AuthShell
  title "Auth Test App"
check_decls [CloudAuth.shortSession, CloudAuth.hasGoogle, CloudAuth.notManaged]
expect_err "Invariant `BadAuthInv.tooShort` failed" in
  auth BadAuthInv:
    managed [google]
    session ttl = 3600
    invariant tooShort: session_ttl <= 60
example : Qed.LawfulJson CloudAuth.User × Qed.LawfulProto CloudAuth.User := (inferInstance, inferInstance)
example : Qed.Auth.parseJwtAlg "none" = none ∧ Qed.Auth.parseJwtAlg "HS256" = none ∧ Qed.Auth.isSafeReturnTo "//evil.com" = false ∧ Qed.Auth.isSafeReturnTo "javascript:alert(1)" = false ∧
    (CloudAuth.loginUrl "//evil.com").raw = (CloudAuth.loginUrl "/").raw ∧ (CloudAuth.logoutUrl "//evil.com").raw = (CloudAuth.logoutUrl "/").raw ∧ (CloudAuth.loginUrl).raw = (CloudAuth.loginUrl "/").raw :=
  ⟨Qed.Auth.parseJwtAlg_rejects_none, Qed.Auth.parseJwtAlg_rejects_hs256, Qed.Auth.isSafeReturnTo_rejects_protocol_relative, Qed.Auth.isSafeReturnTo_rejects_javascript, rfl, rfl, rfl⟩
bad_srv "`onSignIn` in `server MissingAuthServer` requires `use auth : <Auth>`" MissingAuthServer : onSignIn(user): pass
end AuthChecks
