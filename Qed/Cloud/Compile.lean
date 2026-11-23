import Qed.Cloud.Gcp
import Qed.Deploy

/-! ## Verified Cloud Run Infrastructure Compiler & 4-Phase Rollout Planner (`Qed.Cloud.Compile`)
    Pure, total Lean functions that compile a `DeploySpec` + `DeployManifest` into:
    - `GcpPlan`: exact least-privilege Cloud Run, Secret Manager, Cloud SQL, GCS CDN,
      IAM binding, IAM deny, and egress allowlist configuration for a single `(shard, tenant, app, env)`.
    - `compileOrgPolicy`: multi-tenant org IAM/egress policy across an arbitrary list of plans.
    - `planRollout`: 4-phase zero-downtime Cloud Run revision rollout plan (including additive
      Phase 1 egress union and Phase 4 narrowing, plus mismatched `live.key` safety).
    - `planPreviewTeardown`: safe PR-preview teardown planner (guaranteed no-op on non-preview envs). -/

namespace Qed.Cloud

/-- Enforces physical cluster separation: `.prod` uses `prodCluster`; all non-prod envs
    (`.staging`, `.preview _`) strictly use `nonProdCluster`. -/
def clusterForEnv : EnvInstance → DbCluster
  | .prod => .prodCluster
  | _     => .nonProdCluster

structure GcpPlan where
  key              : DeployKey
  buildHash        : String
  regions          : List GcpRegion
  scale            : ScaleSpec
  serviceAccountId : String
  cloudRunName     : String
  secretNames      : List String
  managedDbs       : List (String × DbCluster)
  assetPaths       : List String
  egressAllow      : List String
  bindings         : List GcpIamBinding
  denies           : List GcpDenyRule
deriving Inhabited, DecidableEq, Repr

/-- Compiles a verified `DeploySpec` + `DeployManifest` into a least-privilege `GcpPlan`
    for a single concrete `(shard, tenant, app, env)` slice. -/
def compileInfra (key : DeployKey) (buildHash : String)
    (spec : DeploySpec) (m : Qed.Deploy.DeployManifest) : GcpPlan :=
  let fp := m.footprintFor key.env.toDeployEnv
  let secretNames := fp.secrets.map (·.envVar)
  let cl := clusterForEnv key.env
  let managedDbs := fp.managedDbs.map fun (dbName, _) => (dbName, cl)
  let secretBindings := secretNames.map fun s =>
    { principal := .runtimeSa key, role := .secretManagerAccessor, resource := .secret key s : GcpIamBinding }
  let dbBindings := managedDbs.map fun (dbName, c) =>
    { principal := .runtimeSa key, role := .cloudSqlClient, resource := .cloudSqlDb c key dbName : GcpIamBinding }
  let runBinding : GcpIamBinding := { principal := .edgeRouter, role := .runInvoker, resource := .cloudRun key }
  let assetBindings : List GcpIamBinding :=
    [ { principal := .builder,  role := .storageObjectAdmin,  resource := .assetPrefix key buildHash },
      { principal := .allUsers, role := .storageObjectViewer, resource := .assetPrefix key buildHash } ]
  let denyPub (perms : List GcpPermission) (resource : GcpResource) : GcpDenyRule :=
    { principals := [.allUsers, .allAuthenticatedUsers], permissions := perms, resource }
  let hasState    := (m.server?.map (·.hasState)).getD false
  let hasJobs     := (m.server?.map fun s => !s.jobs.isEmpty).getD false
  let hasChannels := (m.server?.map fun s => !s.channels.isEmpty).getD false
  let isSingleInstance := hasState || (!fp.ephemeralDbs.isEmpty && key.env.isPreview)
  { key, buildHash
    regions          := if isSingleInstance then spec.regions.take 1 else spec.regions
    scale := {
      minInstances := if hasJobs then 1 else 0
      maxInstances := if isSingleInstance then 1 else 100
      memoryMb     := spec.compute.memoryMb
      cpuMilli     := spec.compute.cpuMilli
      concurrency  := 1000
      timeoutSec   := spec.timeoutSec?.getD (if hasChannels then 3600 else 60)
    }
    serviceAccountId := renderSaId key, cloudRunName := renderCloudRunName key
    secretNames, managedDbs, assetPaths := m.assets.map (·.path), egressAllow := fp.egress
    bindings         := secretBindings ++ dbBindings ++ [runBinding] ++ assetBindings
    denies           := denyPub [.runInvoke] (.cloudRun key) :: secretNames.map (denyPub [.secretAccessor] ∘ .secret key) }

/-- Aggregates an arbitrary multi-tenant list of compiled `GcpPlan`s into one org-wide
    `GcpPolicyState` for cross-tenant & preview-vs-prod isolation verification. -/
def compileOrgPolicy (plans : List GcpPlan) : GcpPolicyState :=
  { bindings    := plans.flatMap (·.bindings)
    denies      := plans.flatMap (·.denies)
    egressAllow := plans.flatMap fun p => p.egressAllow.map (p.key, ·) }

/-- Live observed state for a single deployed slice prior to rollout or teardown. -/
structure GcpObservedState where
  key         : DeployKey
  secretNames : List String := []
  managedDbs  : List String := []
  egressAllow : List String := []
  bindings    : List GcpIamBinding := []
deriving Inhabited, DecidableEq, Repr

/-- Computes a 4-phase zero-downtime Cloud Run rollout plan:
    1. Provision assets, secrets, managed DBs, new IAM bindings, deny rules, and additive egress union
    2. Deploy new Cloud Run revision at 0% traffic & run health check
    3. Atomically shift traffic 0% -> 100%
    4. Revoke stale non-asset IAM bindings, removed secrets, and narrow removed egress AFTER traffic flip
    If `live.key ≠ desired.key`, `live` is safely ignored (treated as empty) so a wrong observation
    can never drop secrets or skip required grants. -/
def planRollout (live : GcpObservedState) (desired : GcpPlan) : List GcpAction :=
  let liveSecrets  := if live.key == desired.key then live.secretNames else []
  let liveBindings := if live.key == desired.key then live.bindings else []
  let liveEgress   := if live.key == desired.key then live.egressAllow else []
  let widenedEgress := (liveEgress ++ desired.egressAllow).eraseDups
  let needsNarrow   := liveEgress.any fun o => !desired.egressAllow.contains o
  let phase1 :=
    (if desired.assetPaths.isEmpty then [] else [.uploadAssets desired.key desired.buildHash desired.assetPaths]) ++
    (desired.secretNames.map fun s => .ensureSecret desired.key s) ++
    (desired.managedDbs.map fun (dbName, cl) => .ensureDb cl desired.key dbName) ++
    ((desired.bindings.filter fun b => !liveBindings.contains b).map .grantBinding) ++
    (desired.denies.map .putDenyRule) ++
    [.setEgressRules desired.key widenedEgress]
  let phase2 : List GcpAction :=
    [ .deployRevisionZero desired.key desired.buildHash desired.scale,
      .healthCheck desired.key desired.buildHash ]
  let phase3 : List GcpAction :=
    [ .shiftTraffic100 desired.key desired.buildHash ]
  let phase4 :=
    ((liveBindings.filter fun b =>
        b.resource.ownerKey == desired.key &&
        !(b.resource.isPublicAsset && b.principal == .allUsers && b.role == .storageObjectViewer) &&
        !desired.bindings.contains b).map .revokeBinding) ++
    ((liveSecrets.filter fun s => !desired.secretNames.contains s).map fun s =>
      .deleteSecret desired.key s) ++
    (if needsNarrow then [.narrowEgressRules desired.key desired.egressAllow] else [])
  phase1 ++ phase2 ++ phase3 ++ phase4

/-- Tears down an ephemeral PR preview environment cleanly.
    Strictly returns `[]` for non-preview environments (`.prod`, `.staging`). -/
def planPreviewTeardown (live : GcpObservedState) : List GcpAction :=
  if !live.key.env.isPreview then []
  else
    let revokes :=
      (live.bindings.filter fun b => b.resource.ownerKey == live.key).map .revokeBinding
    let delSecrets := live.secretNames.map fun s => .deleteSecret live.key s
    let dropDbs := live.managedDbs.map fun db => .dropPreviewDb live.key db
    revokes ++ delSecrets ++ dropDbs ++ [.deleteService live.key]

end Qed.Cloud
