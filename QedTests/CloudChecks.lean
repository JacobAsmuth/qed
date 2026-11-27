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
  rpc inc() -> Nat: count += 1; return count
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
    shortName := "ByoDb", secrets := ["PROD_DB_URL", "STAGING_DB_URL", "PREVIEW_DB_URL"],
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
  isLocalhostUrl "http://[::1]:8001" && !isLocalhostUrl "http://127.evil.com" && isStrictLoopbackUrl "http://127.0.0.1:8080/" && !isStrictLoopbackUrl "http://127.0.0.1/path" &&
  isValidHostname "notes.example.com" && !isValidHostname "169.254.169.254" && Qed.Deploy.isValidEgressOrigin "https://billing.example.com" && !Qed.Deploy.isValidEgressOrigin "http://billing.example.com" &&
  Qed.Deploy.isValidAssetPath "/assets/app.js" && !Qed.Deploy.isValidAssetPath "/qed_deploy.json" &&
  (multiEnvManifest.footprintFor .preview).secrets.map (·.envVar) == ["PREVIEW_DB_URL"] &&
  (multiEnvManifest.footprintFor .prod).secrets.map (·.envVar) == ["PROD_DB_URL", "QED_AUTH_CLIENT_SECRET"] && (multiEnvManifest.footprintFor .dev).secrets == [] &&
  [.setEgressRules k ["https://a.com", "https://b.com"], .narrowEgressRules k ["https://a.com"], .deleteSecret k "OLD"].all acts.contains &&
  plan.bindings.contains { principal := .allUsers, role := .storageLegacyObjectReader, resource := .assetPrefix k "h1" true } &&
  prevPlan.bindings.contains { principal := .edgeRouter, role := .storageLegacyObjectReader, resource := .assetPrefix kp "h1" false } && !prevPlan.bindings.any (·.principal == .allUsers) &&
  [.deleteEgressPolicy kp, .pruneDenyException kp, .deleteServiceAccount kp].all td.contains && !td.any fun | .revokeBinding b => b.resource.isAsset | _ => false) = true := by decide +kernel

/-! ## 3. Negative Elaborator Guard Tests -/
bad_deploy "`deploy BadStatefulMultiRegion`: server `StatefulApi` uses in-memory `state`, which can only run in a single region" BadStatefulMultiRegion StatefulApi : regions [us_central1, europe_west1]
bad_deploy "`deploy BadTimeout`: `timeout` (7201s) must be between 1s and 3600s" BadTimeout NotesApp : timeout 7201s
bad_deploy "`deploy BadDomain`: invalid RFC 1123 production `domain` `https://notes.example.com`" BadDomain NotesApp : domain "https://notes.example.com"
bad_deploy "`deploy BadOverlap`: preview host `*.example.com` overlaps production domain `notes.example.com`" BadOverlap NotesApp : domain "notes.example.com" |
  preview:
    domain "*.example.com"
bad_deploy "`deploy BadPublicPreview`: `auth ManagedAuth` uses `managed` auth" BadPublicPreview NotesApp :
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
bad_deploy "deploy invariant `BadInv.wrongTier` failed to prove" BadInv NotesApp : compute standard | invariant wrongTier: compute == xlarge
bad_deploy "use `timeout_sec` (Option Nat, in seconds) inside deploy invariants" BadInvField NotesApp : invariant badField: timeout == none
end CloudChecks
