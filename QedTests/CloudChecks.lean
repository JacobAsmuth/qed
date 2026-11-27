import Qed
import Qed.Cloud.Proofs
import QedTests.CheckHelper
open Qed Qed.Cloud

namespace CloudChecks
auth ManagedAuth:
  managed [google, github, email]
  session ttl = 7200
  claims:
    email : String = ""
    role  : String = "member"
database NotesDb:
  managed postgres
  table notes:
    id      : Nat    primary_key
    ownerId : String immutable where 1 <= ownerId.length <= 64
    body    : String           where 1 <= body.length <= 500
    policy read, write requires some(row.ownerId) == ctx.userId
database EphemeralPreviewDb:
  managed postgres:
    preview ephemeral
    dev sqlite ".qed/custom-dev.db"
  table items:
    id   : Nat    primary_key
    name : String where 1 <= name.length <= 100
database SplitPreviewDb:
  postgres secret("DATABASE_URL")
  preview  postgres secret("PREVIEW_DB_URL")
  table t:
    id : Nat primary_key
server NotesApi:
  use auth : ManagedAuth
  use db   : NotesDb
  rpc ok() -> Bool: return true
server SplitPreviewSrv:
  use db : SplitPreviewDb
  rpc ok() -> Bool: return true
component NotesShell:
  session user
  state status = "ready"
  view: <main><h1>Notes</h1><p>{status}</p></main>
fullstack NotesApp:
  server NotesApi
  client NotesShell
  title "Notes App"
deploy NotesDeploy:
  app     NotesApp
  regions [us_central1, europe_west1]
  domain  "notes.example.com"
  compute performance
  timeout 5m
  preview:
    on_pr      true
    subdomain  "preview"
    protection team_only
    ttl        7d
  invariant privatePreview:  preview.protection == team_only
  invariant hasProdDomain:   domain.isSome and preview.subdomain.isSome
  invariant includesCentral: us_central1 in regions
  invariant perfTier:        compute == performance
deploy MinimalDeploy:
  app     NotesApp
  regions [europe_west1, europe_west4]
  domain  "eu.notes.example.com"
  invariant euResidency: all r in regions: r.inEu
deploy StaticShellDeploy:
  app     NotesShell
  regions [us_central1]
  domain  "static.notes.example.com"
server StatefulApi:
  state count : Nat = 0
  invariant nonNeg: count >= 0
  rpc inc() -> Nat:
    count += 1
    return count
deploy StatefulDeploy:
  app     StatefulApi
  regions [us_central1]
server CronApi:
  every 60 s cleanup: pass
  rpc ok() -> Bool: return true
deploy CronDeploy:
  app CronApi
def multiEnvManifest : Qed.Deploy.DeployManifest := {
  version := 1, auth? := some ManagedAuth.config, databases := [{
    dbName := `ByoDb, shortName := "ByoDb", configConst := `ByoDb.config, ensureSchemaConst := `ByoDb.ensureSchema,
    secrets := #["PROD_DB_URL", "STAGING_DB_URL", "PREVIEW_DB_URL"], tables := #[],
    envSpecs := { dev := .byoSqlite ".qed/dev.db", preview := .byoPostgres { envVar := "PREVIEW_DB_URL", scope := .pinned .preview },
                  staging := .byoPostgres { envVar := "STAGING_DB_URL", scope := .pinned .staging }, prod := .byoPostgres { envVar := "PROD_DB_URL", scope := .pinned .prod } } }] }
example : (
  let sh : ShardProject := ⟨"s1-prod", "s1-nonprod", by decide⟩
  let (k, kp) : DeployKey × DeployKey := ({ shard := sh, tenant := ⟨1, by decide⟩, app := ⟨1, by decide⟩, env := .prod }, { shard := sh, tenant := ⟨1, by decide⟩, app := ⟨1, by decide⟩, env := .preview ⟨42, by decide⟩ })
  let (plan, prevPlan) := (compileInfra k "h1" NotesDeploy.spec { version := 1, secrets := ["K"], egress := ["https://a.com"] }, compileInfra kp "h1" NotesDeploy.spec { version := 1, secrets := ["K"], egress := ["https://a.com"] })
  let (acts, td) := (planRollout { key := k, secretNames := ["K", "OLD"], egressAllow := ["https://a.com", "https://b.com"] } plan, planPreviewTeardown { key := kp, bindings := prevPlan.bindings })
  NotesDeploy.spec.compute == .performance && NotesDeploy.spec.timeoutSec? == some 300 && NotesDeploy.spec.preview.ttlSec == 7 * 86400 &&
  MinimalDeploy.spec.compute == .standard && MinimalDeploy.spec.timeoutSec? == none && NotesDb.config.isManaged && ManagedAuth.config.isManaged &&
  SplitPreviewSrv.secrets == #[] && NotesDb.config.endpointForEnv .prod == .managedPostgres "NotesDb" .prod &&
  EphemeralPreviewDb.config.endpointForEnv .preview == .sqlitePath "/tmp/qed-preview-EphemeralPreviewDb.db" && EphemeralPreviewDb.config.endpointForEnv .dev == .sqlitePath ".qed/custom-dev.db" &&
  ["http://127.0.0.2:8001/auth", "http://[::1]:8001", "http://app.localhost:3000", "http://localhost.:8080", "http://a@b@127.0.0.1:8080", "http://localhost\\@evil.com",
   "http://2130706433", "http://0x7f000001", "http://0177.0.0.1", "http://0", "http://0.0.0.0", "http://[::]", "http://[0::1]", "http://[::0:1]", "http://[0:0:0:0:0:0:0:1]",
   "http://[::ffff:7f00:1]", "http://[::ffff:127.0.0.1]", "http://[0:0:0:0:0:ffff:127.0.0.1]", "http://[::1%25lo]:8080", "http://[::1%lo]:8080", "http://[::127.0.0.1]:8080", "http://localhost ", "  http://127.0.0.1 \t"].all isLocalhostUrl &&
  ["http://[::8.8.8.8]:8080", "http://[::2]:8080", "https://notlocalhost.example.com/v127.0.0.1", "http://127.evil.com", "http://metadata.local", "http://[::ffff:127.evil.com]", "http://127.0.0.256"].all (!isLocalhostUrl ·) &&
  ["http://127.0.0.1", "http://127.0.0.1:8080", "http://127.0.0.1:8080/", "http://localhost", "http://localhost:3000/", "http://[::1]", "http://[::1]:8080/"].all isStrictLoopbackUrl &&
  ["http://127.evil.com", "http://127.0.0.1:8080/path", "http://127.0.0.1?a=1", "http://127.0.0.1#h", "http://127.0.0.1@evil.com", "http://127.0.0.1\\@evil.com", "http://127.0.0.1//", "https://127.0.0.1", "http://127.0.0.1:0", "http://127.0.0.1:70000"].all (!isStrictLoopbackUrl ·) &&
  isValidHostname "notes.example.com" && ["127.0.0.1", "169.254.169.254", "169.254.169.0xfe", "127.0.0.0x01", "198.18.0.0x01", "224.0.0.0xfb", "1.1.1.0x01"].all (!isValidHostname ·) &&
  (HostPattern.exact "Notes.Example.COM").matches "notes.example.com" && (HostPattern.wildcard "Example.COM").matches "App.example.com" && (derivePreviewHost "notes.example.com" "preview").matches "pr-42.preview.notes.example.com" &&
  ([({ name := "D", appName := "A", domain? := some "app.localhost" } : DeploySpec), { name := "D", appName := "A", domain? := some "app.local" },
    { name := "D", appName := "A", regions := [.us_central1, .us_central1] }, { name := "", appName := "A" }, { name := "D", appName := "" },
    { name := "D", appName := "A", domain? := some "a.b.example.com", preview := { host? := some (.wildcard "example.com"), subdomain? := none } },
    { name := "D", appName := "A", domain? := some "app.example.com", preview := { host? := some (.exact "example.com"), subdomain? := none } }]).all (fun s => !s.validate.isOk) &&
  ["https://billing.example.com", "https://api.stripe.com:443"].all Qed.Deploy.isValidEgressOrigin &&
  ["http://billing.example.com", "https://billing.example.com/path", "https://metadata.google.internal", "https://169.254.169.254", "https://169.254.169.0xfe", "https://1.1.1.0x01", "https://10.0.0.1", "https://localhost", "https://*.example.com"].all (!Qed.Deploy.isValidEgressOrigin ·) &&
  [("/../etc/passwd", "text/plain"), ("/a//b.js", "text/javascript")].all (fun (p, m) => !({ version := 1, assets := [{ path := p, mime := m }] } : Qed.Deploy.DeployManifest).validate.isOk) &&
  ["/qed_deploy.json", "/sub/QED_DEPLOY.JSON", "/qed_manifest.json", "/sub/QED_MANIFEST.JSON", "/app.js?v=1", "/app.js#top"].all (!Qed.Deploy.isValidAssetPath ·) && Qed.Deploy.isValidAssetPath "/assets/app.js" &&
  (multiEnvManifest.footprintFor .preview).secrets.map (·.envVar) == ["PREVIEW_DB_URL"] &&
  (multiEnvManifest.footprintFor .prod).secrets.map (·.envVar) == ["PROD_DB_URL", "QED_AUTH_CLIENT_SECRET"] && (multiEnvManifest.footprintFor .dev).secrets == [] &&
  [.setEgressRules k ["https://a.com", "https://b.com"], .narrowEgressRules k ["https://a.com"], .deleteSecret k "OLD"].all acts.contains &&
  plan.bindings.contains { principal := .allUsers, role := .storageLegacyObjectReader, resource := .assetPrefix k "h1" true } &&
  prevPlan.bindings.contains { principal := .edgeRouter, role := .storageLegacyObjectReader, resource := .assetPrefix kp "h1" false } && !prevPlan.bindings.any (·.principal == .allUsers) &&
  [.deleteEgressPolicy kp, .pruneDenyException kp, .deleteServiceAccount kp].all td.contains && !td.any fun | .revokeBinding b => b.resource.isAsset | _ => false) = true := by decide +kernel

/-! ## 3. Negative Elaborator Guard Tests -/
bad_deploy1 "`deploy BadStatefulMultiRegion`: server `StatefulApi` uses in-memory `state`, which can only run in a single region" BadStatefulMultiRegion StatefulApi : regions [us_central1, europe_west1]
bad_deploy1 "`deploy BadTimeout`: `timeout` (7201s) must be between 1s and 3600s" BadTimeout NotesApp : timeout 7201s
bad_deploy1 "`deploy BadDomain`: invalid RFC 1123 production `domain` `https://notes.example.com`" BadDomain NotesApp : domain "https://notes.example.com"
expect_err "`deploy BadOverlap`: preview host `*.example.com` overlaps production domain `notes.example.com`" in
deploy BadOverlap:
  app    NotesApp
  domain "notes.example.com"
  preview:
    domain "*.example.com"
expect_err "`deploy BadPublicPreview`: `auth ManagedAuth` uses `managed` auth" in
deploy BadPublicPreview:
  app NotesApp
  preview:
    protection public
database BadSqliteDb:
  sqlite "/tmp/prod.db"
  table t:
    id : Nat primary_key
server BadSqliteSrv:
  use db : BadSqliteDb
  rpc ping() -> Bool: return true
bad_deploy "`deploy BadSqlite`: database `BadSqliteDb` uses ephemeral SQLite in `prod`" BadSqlite BadSqliteSrv
server LoopbackEnvSrv:
  env apiUrl = "API_URL" ?? "http://localhost:9000"
  rpc ping() -> String: return apiUrl
bad_deploy "`deploy BadLoopbackEnv`: server `LoopbackEnvSrv` `env apiUrl` (`API_URL`) has a loopback default (`http://localhost:9000`)" BadLoopbackEnv LoopbackEnvSrv
expect_err "cannot combine `managed [...]` with explicit OIDC clauses in `auth BadMixedAuth`" in
auth BadMixedAuth:
  managed [google]
  issuer env("X") ?? "http://127.0.0.1:8001"
expect_err "cannot combine a default endpoint with `prod` in `database BadDefaultProdDb`" in
database BadDefaultProdDb:
  postgres secret("DEFAULT_URL")
  prod     postgres secret("PROD_URL")
  table t:
    id : Nat primary_key
expect_err "cannot override `prod` inside `managed postgres:` in `database BadManagedProdDb`" in
database BadManagedProdDb:
  managed postgres:
    prod sqlite "/tmp/bad.db"
  table t:
    id : Nat primary_key
expect_err "deploy invariant `BadInv.wrongTier` failed to prove" in
deploy BadInv:
  app     NotesApp
  compute standard
  invariant wrongTier: compute == xlarge
bad_deploy1 "use `timeout_sec` (Option Nat, in seconds) inside deploy invariants" BadInvField NotesApp : invariant badField: timeout == none

end CloudChecks
