import Qed
import Qed.Cloud.Proofs
open Qed
open Qed.Cloud

namespace CloudChecks

/-! ## 1. Surface Grammar & Elaboration Smoke Tests (`managed`, `deploy`, `compute`, duration units) -/

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

external BillingApi:
  base "https://billing.example.com"
  get "/status" status() -> Bool

server NotesApi:
  use auth : ManagedAuth
  use db   : NotesDb

  def getNote(noteId: Nat) -> NotesDb.notes?!:
    requires ctx.userId != none
    if let some(uid) = ctx.userId:
      return await db.notes.findOne(where = r => r.id == noteId and r.ownerId == uid)?
    return none

  def pingBilling() -> Bool!:
    return await BillingApi.status()?

server SplitPreviewSrv:
  use db : SplitPreviewDb
  def ok() -> Bool:
    return true

component NotesShell:
  session user
  state status = "ready"
  view:
    <main>
      <h1>Notes</h1>
      <p>{status}</p>
    </main>

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

-- Minimal Vercel-style 4-line deploy (all defaults derived automatically)
deploy MinimalDeploy:
  app     NotesApp
  regions [europe_west1, europe_west4]
  domain  "eu.notes.example.com"
  invariant euResidency: all r in regions: r.inEu

-- Standalone client-only `component` deploy
deploy StaticShellDeploy:
  app     NotesShell
  regions [us_central1]
  domain  "static.notes.example.com"

-- Stateful single-region server & cron server deploy with ZERO manual scaling config!
server StatefulApi:
  state count : Nat = 0
  invariant nonNeg: count >= 0
  def inc() -> Nat:
    count += 1
    return count

deploy StatefulDeploy:
  app     StatefulApi
  regions [us_central1]

server CronApi:
  every 60 s cleanup:
    pass
  def ok() -> Bool:
    return true

deploy CronDeploy:
  app CronApi

-- Elaborated values (compute presets, duration units, managed expansion, split-env secrets)
#guard NotesDeploy.spec.compute == .performance
#guard NotesDeploy.spec.timeoutSec? == some 300
#guard NotesDeploy.spec.preview.ttlSec == 7 * 86400
#guard MinimalDeploy.spec.compute == .standard && MinimalDeploy.spec.timeoutSec? == none
#guard NotesDb.config.isManaged && ManagedAuth.config.isManaged
#guard SplitPreviewSrv.secrets == #[]
#guard NotesDb.config.endpointForEnv .prod == .managedPostgres "NotesDb" .prod
#guard EphemeralPreviewDb.config.endpointForEnv .preview == .sqlitePath "/tmp/qed-preview-EphemeralPreviewDb.db"
#guard EphemeralPreviewDb.config.endpointForEnv .dev == .sqlitePath ".qed/custom-dev.db"

/-! ## 2. Concrete Computational Edge Cases (Unproved Parsers / Rollout Diff) -/

-- Authority-aware loopback detection & wildcard positive match
#guard isLocalhostUrl "http://127.0.0.2:8001/auth" && isLocalhostUrl "http://[::1]:8001"
#guard isLocalhostUrl "http://app.localhost:3000" && !isLocalhostUrl "https://notlocalhost.example.com/v127.0.0.1"
#guard (derivePreviewHost "notes.example.com" "preview").matches "pr-42.preview.notes.example.com"

-- Per-env footprint isolates secrets and excludes managed auth secret in dev/preview
def multiEnvManifest : Qed.Deploy.DeployManifest := {
  version := 1
  databases := [{
    dbName := `ByoDb, shortName := "ByoDb",
    configConst := `ByoDb.config, ensureSchemaConst := `ByoDb.ensureSchema,
    secrets := #["PROD_DB_URL", "STAGING_DB_URL", "PREVIEW_DB_URL"],
    envSpecs := {
      dev     := .byoSqlite ".qed/dev.db",
      preview := .byoPostgres { envVar := "PREVIEW_DB_URL", scope := .pinned .preview },
      staging := .byoPostgres { envVar := "STAGING_DB_URL", scope := .pinned .staging },
      prod    := .byoPostgres { envVar := "PROD_DB_URL", scope := .pinned .prod }
    },
    tables := #[]
  }]
  auth? := some ManagedAuth.config
}
#guard (multiEnvManifest.footprintFor .preview).secrets.map (·.envVar) == ["PREVIEW_DB_URL"]
#guard (multiEnvManifest.footprintFor .prod).secrets.map (·.envVar) == ["PROD_DB_URL", "QED_AUTH_CLIENT_SECRET"]
#guard (multiEnvManifest.footprintFor .dev).secrets == []

-- Zero-downtime egress union (Phase 1) + narrowing (Phase 4)
#guard
  let k : DeployKey := { shard := ⟨"s1"⟩, tenant := ⟨1, by decide⟩, app := ⟨1, by decide⟩, env := .prod }
  let plan := compileInfra k "h1" NotesDeploy.spec { version := 1, secrets := ["K"], egress := ["https://a.com"] }
  let live : GcpObservedState := { key := k, secretNames := ["K", "OLD"], egressAllow := ["https://a.com", "https://b.com"] }
  let acts := planRollout live plan
  acts.contains (.setEgressRules k ["https://a.com", "https://b.com"]) &&
  acts.contains (.narrowEgressRules k ["https://a.com"]) &&
  acts.contains (.deleteSecret k "OLD")

/-! ## 3. Negative Elaborator Guard Tests (1 per distinct check) -/

/--
error: `deploy BadStatefulMultiRegion`: server `StatefulApi` uses in-memory `state`, which can only run in a single region (`regions.length = 1`) to preserve `atomic:` and state invariants.

Hint: Deploy to a single region, or move mutable state into a `database` block to deploy multi-region.
-/
#guard_msgs in
deploy BadStatefulMultiRegion:
  app     StatefulApi
  regions [us_central1, europe_west1]

/--
error: `deploy BadTimeout`: `timeout` (7201s) must be between 1s and 3600s
-/
#guard_msgs in
deploy BadTimeout:
  app     NotesApp
  timeout 7201s

/--
error: `deploy BadDomain`: invalid RFC 1123 production `domain` `https://notes.example.com` (omit scheme/path/trailing dot)
-/
#guard_msgs in
deploy BadDomain:
  app    NotesApp
  domain "https://notes.example.com"

/--
error: `deploy BadOverlap`: preview host `*.example.com` overlaps production domain `notes.example.com`
-/
#guard_msgs in
deploy BadOverlap:
  app    NotesApp
  domain "notes.example.com"
  preview:
    domain "*.example.com"

/--
error: `deploy BadPublicPreview`: `auth ManagedAuth` uses `managed` auth (which enables the persona-switcher Preview IdP on previews), so `preview:` cannot set `protection public`.

Hint: Set `protection team_only` inside `preview:`.
-/
#guard_msgs in
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
  def ping() -> Bool:
    return true

/--
error: `deploy BadSqlite`: database `BadSqliteDb` uses ephemeral SQLite in `prod`, which loses all data when Cloud Run recycles containers.

Hint: Use `managed postgres` (or BYO `postgres` / `turso` / `d1`) for production.
-/
#guard_msgs in
deploy BadSqlite:
  app BadSqliteSrv

server LoopbackEnvSrv:
  env apiUrl = "API_URL" ?? "http://localhost:9000"
  def ping() -> String:
    return apiUrl

/--
error: `deploy BadLoopbackEnv`: server `LoopbackEnvSrv` `env apiUrl` (`API_URL`) has a loopback default (`http://localhost:9000`), which must not ship to production.
-/
#guard_msgs in
deploy BadLoopbackEnv:
  app LoopbackEnvSrv

/--
error: cannot combine `managed [...]` with explicit OIDC clauses in `auth BadMixedAuth`
-/
#guard_msgs in
auth BadMixedAuth:
  managed [google]
  issuer env("X") ?? "http://127.0.0.1:8001"

/--
error: cannot combine a default endpoint with `prod` in `database BadDefaultProdDb`
-/
#guard_msgs in
database BadDefaultProdDb:
  postgres secret("DEFAULT_URL")
  prod     postgres secret("PROD_URL")
  table t:
    id : Nat primary_key

/--
error: cannot override `prod` inside `managed postgres:` in `database BadManagedProdDb`
-/
#guard_msgs in
database BadManagedProdDb:
  managed postgres:
    prod sqlite "/tmp/bad.db"
  table t:
    id : Nat primary_key

/--
error: deploy invariant `BadInv.wrongTier` failed to prove
-/
#guard_msgs in
deploy BadInv:
  app     NotesApp
  compute standard
  invariant wrongTier: compute == xlarge

/--
error: use `timeout_sec` (Option Nat, in seconds) inside deploy invariants
-/
#guard_msgs in
deploy BadInvField:
  app NotesApp
  invariant badField: timeout == none

end CloudChecks
