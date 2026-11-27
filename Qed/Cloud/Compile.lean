import Qed.Cloud.Gcp
import Qed.Deploy

/-! ## Verified Cloud Run Infrastructure Compiler & 4-Phase Rollout Planner (`Qed.Cloud.Compile`) -/

namespace Qed.Cloud

def clusterForEnv : EnvInstance → DbCluster | .prod => .prodCluster | _ => .nonProdCluster

structure GcpPlan where
  (key : DeployKey) (buildHash : String) (regions : List GcpRegion) (scale : ScaleSpec)
  (serviceAccountId cloudRunName : String) (secretNames : List String)
  (managedDbs : List (String × DbCluster)) (assetPaths egressAllow : List String)
  (bindings : List GcpIamBinding) (denies : List GcpDenyRule)
deriving Inhabited, DecidableEq, Repr

def compileInfra (key : DeployKey) (buildHash : String) (spec : DeploySpec) (m : Qed.Deploy.DeployManifest) : GcpPlan :=
  let fp := m.footprintFor key.env.toDeployEnv
  let secretNames := fp.secrets.map (·.envVar)
  let managedDbs := fp.managedDbs.map fun (dbName, _) => (dbName, clusterForEnv key.env)
  let assetIsPublic := !(key.env.isPreview && spec.preview.protection == .team_only)
  let assetRes : GcpResource := .assetPrefix key buildHash assetIsPublic
  let denyPub (perms : List GcpPermission) (resource : GcpResource) : GcpDenyRule := { principals := [.allUsers, .allAuthenticatedUsers], permissions := perms, resource }
  let hasState := (m.server?.map (·.hasState)).getD false
  let hasJobs := (m.server?.map fun s => !s.jobs.isEmpty).getD false
  let hasChannels := (m.server?.map fun s => !s.channels.isEmpty).getD false
  let isSingle := hasState || (!fp.ephemeralDbs.isEmpty && key.env.isPreview)
  { key, buildHash, regions := if isSingle then spec.regions.take 1 else spec.regions,
    scale := {
      minInstances := if hasJobs then 1 else 0, maxInstances := if isSingle then 1 else 100,
      memoryMb := spec.compute.memoryMb, cpuMilli := spec.compute.cpuMilli, concurrency := 1000,
      timeoutSec := spec.timeoutSec?.getD (if hasChannels then 3600 else 60) },
    serviceAccountId := renderSaId key, cloudRunName := renderCloudRunName key,
    secretNames, managedDbs, assetPaths := m.assets.map (·.path), egressAllow := fp.egress,
    bindings :=
      (secretNames.map fun s => { principal := .runtimeSa key, role := .secretManagerAccessor, resource := .secret key s : GcpIamBinding }) ++
      (managedDbs.map fun (dbName, c) => { principal := .runtimeSa key, role := .cloudSqlClient, resource := .cloudSqlDb c key dbName : GcpIamBinding }) ++
      [{ principal := .edgeRouter, role := .runInvoker, resource := .cloudRun key }] ++
      [{ principal := .builder, role := .storageObjectAdmin, resource := assetRes },
       { principal := if assetIsPublic then .allUsers else .edgeRouter, role := .storageLegacyObjectReader, resource := assetRes }],
    denies := denyPub [.runInvoke] (.cloudRun key) :: secretNames.map (denyPub [.secretAccessor] ∘ .secret key) }

def compileOrgPolicy (plans : List GcpPlan) : GcpPolicyState :=
  { bindings := plans.flatMap (·.bindings), denies := plans.flatMap (·.denies), egressAllow := plans.flatMap fun p => p.egressAllow.map (p.key, ·) }

def realizeGcpBinding (b : GcpIamBinding) : GcpIamBinding :=
  match b.resource with | .cloudSqlDb cl k _ => { b with resource := .project (k.shard.clusterProject cl) } | _ => b

def realizeOrgPolicy (plans : List GcpPlan) : GcpPolicyState :=
  let st := compileOrgPolicy plans; { st with bindings := st.bindings.map realizeGcpBinding }

structure GcpObservedState where
  (key : DeployKey) (secretNames managedDbs egressAllow : List String := []) (bindings : List GcpIamBinding := [])
deriving Inhabited, DecidableEq, Repr

def planRollout (live : GcpObservedState) (desired : GcpPlan) : List GcpAction :=
  let sameKey := live.key == desired.key
  let (liveSecrets, liveBindings, liveEgress) := (if sameKey then live.secretNames else [], if sameKey then live.bindings else [], if sameKey then live.egressAllow else [])
  let phase1 :=
    (if desired.assetPaths.isEmpty then [] else [.uploadAssets desired.key desired.buildHash desired.assetPaths]) ++
    (desired.secretNames.map (.ensureSecret desired.key)) ++ (desired.managedDbs.map fun (db, cl) => .ensureDb cl desired.key db) ++
    ((desired.bindings.filter (!liveBindings.contains ·)).map .grantBinding) ++ (desired.denies.map .putDenyRule) ++
    [.setEgressRules desired.key (liveEgress ++ desired.egressAllow).eraseDups]
  let phase2 : List GcpAction := [.deployRevisionZero desired.key desired.buildHash desired.scale, .healthCheck desired.key desired.buildHash]
  let phase3 : List GcpAction := [.shiftTraffic100 desired.key desired.buildHash]
  let phase4 :=
    ((liveBindings.filter fun b => b.resource.ownerKey? == some desired.key && !b.resource.isAsset && !desired.bindings.contains b).map .revokeBinding) ++
    ((liveSecrets.filter (!desired.secretNames.contains ·)).map (.deleteSecret desired.key)) ++
    (if liveEgress.any (!desired.egressAllow.contains ·) then [.narrowEgressRules desired.key desired.egressAllow] else [])
  phase1 ++ phase2 ++ phase3 ++ phase4

def planPreviewTeardown (live : GcpObservedState) : List GcpAction :=
  if !live.key.env.isPreview then []
  else
    ((live.bindings.filter fun b => b.resource.ownerKey? == some live.key && !b.resource.isAsset).map .revokeBinding) ++
    (live.secretNames.map (.deleteSecret live.key)) ++ (live.managedDbs.map (.dropPreviewDb live.key)) ++
    ([.deleteService live.key, .deleteEgressPolicy live.key, .pruneDenyException live.key, .deleteServiceAccount live.key] : List GcpAction)

end Qed.Cloud
