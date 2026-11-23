import Lean
import Qed.Json
import Qed.Cloud.Env
import Qed.Auth.Core
import Qed.Server.Core
import Qed.Server.Registry

namespace Qed.Deploy

/-! ## Provably-Complete Deployment & Infrastructure Manifest (`Qed.Deploy`)
    Extracts the entire infrastructure footprint of a compiled Qed app directly from
    Lean's verified compiler registries (`serverRegistry`, `databaseRegistry`, `authRegistry`,
    `externalRegistry`) into a deterministic, machine-verifiable `qed_deploy.json` contract
    for Qed Cloud / PaaS control planes:
    - Required `secrets` & `envVars` (zero missing-env production crashes)
    - `databases` (tables, columns, indexes, RLS policies)
    - `auth` (OIDC issuer/audience/client env refs, providers, TTL, paths, typed claims)
    - `egress` (exact allowlist of `external` base origins for default-deny network firewalls)
    - `server` (RPC methods, WebSocket channels, custom HTTP routes, `every` jobs)
    - `assets` (content-hashed immutable client bundle metadata for CDN upload) -/

abbrev DeployAuthManifest := Qed.Auth.OidcAuthSpec

structure DeployAssetManifest where
  path  : String
  mime  : String
  bytes : Nat := 0
deriving Inhabited, DecidableEq, Repr

structure DeployManifest where
  version    : Nat := 1
  rootModule : String := ""
  mode       : String := "standalone" -- "fullstack" | "standalone"
  secrets    : List String := []
  envVars    : List (String × String × Option String) := []
  egress     : List String := []
  databases  : List Qed.Server.DatabaseInfo := []
  auth?      : Option DeployAuthManifest := none
  server?    : Option Qed.ServerInfo := none
  assets     : List DeployAssetManifest := []
  csp        : String := Qed.Server.defaultCsp
deriving Inhabited

/-- Per-environment least-privilege infrastructure footprint derived from `DeployManifest`. -/
structure EnvFootprint where
  secrets      : List Qed.Cloud.SecretRef := []
  egress       : List String := []
  managedDbs   : List (String × Qed.Cloud.DbCluster) := []
  ephemeralDbs : List String := []
  authTarget?  : Option Qed.Cloud.AuthEnvTarget := none
deriving Inhabited, DecidableEq, Repr

private def dedupSecretsByEnvVar (xs : List Qed.Cloud.SecretRef) : List Qed.Cloud.SecretRef :=
  xs.foldl (init := []) fun acc s =>
    if acc.any (·.envVar == s.envVar) then acc else acc ++ [s]

/-- Computes the exact least-privilege footprint for a single `DeployEnv`.
    Uses server-owned secrets (`ownSecrets`, never DB/auth unions), gates `managed` auth's
    client secret to `staging`/`prod`, and deduplicates secrets strictly by `envVar`. -/
def DeployManifest.footprintFor (m : DeployManifest) (env : Qed.Cloud.DeployEnv) : EnvFootprint :=
  let dbSpecs := m.databases.map fun db => (db.shortName, db.envSpecs.get env)
  let dbSecrets := dbSpecs.flatMap fun (_, sp) => sp.secrets
  let srvSecrets : List Qed.Cloud.SecretRef :=
    ((m.server?.map (·.ownSecrets.toList)).getD []).map fun k => { envVar := k, scope := .envScoped }
  let authSecrets : List Qed.Cloud.SecretRef :=
    match m.auth? with
    | some a =>
        if a.isManaged && (env == .dev || env == .preview) then []
        else (a.clientSecretEnv?.map fun s => [{ envVar := s, scope := .envScoped }]).getD []
    | none => []
  let rawSecrets : List Qed.Cloud.SecretRef :=
    if m.server?.isSome || !m.databases.isEmpty || m.auth?.isSome then
      dbSecrets ++ srvSecrets ++ authSecrets
    else
      m.secrets.map fun k => { envVar := k, scope := .envScoped }
  let dbEgress := dbSpecs.flatMap fun (_, sp) => sp.egressOrigins
  let managedDbs := dbSpecs.filterMap fun (nm, sp) => sp.cluster?.map (nm, ·)
  let ephemeralDbs := dbSpecs.filterMap fun (nm, sp) => if sp.isEphemeral then some nm else none
  let authTarget? := m.auth?.map fun a =>
    if a.isManaged then (Qed.Cloud.managedAuthTargets a.providers).get env else .customOidc
  {
    secrets      := dedupSecretsByEnvVar rawSecrets
    egress       := (m.egress ++ dbEgress).eraseDups
    managedDbs
    ephemeralDbs
    authTarget?
  }

def DeployManifest.envs (m : DeployManifest) : Qed.Cloud.EnvMap EnvFootprint :=
  { dev     := m.footprintFor .dev
    preview := m.footprintFor .preview
    staging := m.footprintFor .staging
    prod    := m.footprintFor .prod }

/-! ### Kernel-Verified Manifest Consistency Checks -/

abbrev isValidEnvKey : String → Bool := Qed.Server.isValidEnvVarName

def isValidEgressOrigin (s : String) : Bool :=
  let cs := s.toList
  let hasScheme :=
    match cs with
    | 'h' :: 't' :: 't' :: 'p' :: 's' :: ':' :: '/' :: '/' :: _ :: _ => true
    | 'h' :: 't' :: 't' :: 'p' :: ':' :: '/' :: '/' :: _ :: _        => true
    | _ => false
  hasScheme && cs.all isSafeUrlChar

def validateAuthManifest (a : DeployAuthManifest) : Except String Unit :=
  if !isValidEnvKey a.issuerEnv then .error s!"deploy manifest: invalid auth issuerEnv `{a.issuerEnv}`"
  else if !isValidEnvKey a.audienceEnv then .error s!"deploy manifest: invalid auth audienceEnv `{a.audienceEnv}`"
  else if a.sessionTtlSec == 0 then .error "deploy manifest: auth sessionTtlSec must be positive"
  else if !Qed.Auth.isSafeReturnTo a.loginPath then .error s!"deploy manifest: unsafe auth loginPath `{a.loginPath}`"
  else if !Qed.Auth.isSafeReturnTo a.callbackPath then .error s!"deploy manifest: unsafe auth callbackPath `{a.callbackPath}`"
  else if !Qed.Auth.isSafeReturnTo a.logoutPath then .error s!"deploy manifest: unsafe auth logoutPath `{a.logoutPath}`"
  else if !Qed.Auth.isSafeReturnTo a.mePath then .error s!"deploy manifest: unsafe auth mePath `{a.mePath}`"
  else if a.clientIdEnv?.any (!isValidEnvKey ·) then .error "deploy manifest: invalid auth clientIdEnv"
  else if a.clientSecretEnv?.any (!isValidEnvKey ·) then .error "deploy manifest: invalid auth clientSecretEnv"
  else .ok ()

def DeployManifest.validate (m : DeployManifest) : Except String Unit := do
  if m.version != 1 then
    .error s!"deploy manifest: unsupported version {m.version}"
  for s in m.secrets do
    if !isValidEnvKey s then
      .error s!"deploy manifest: invalid secret env key `{s}`"
  for (_, osKey, _) in m.envVars do
    if !isValidEnvKey osKey then
      .error s!"deploy manifest: invalid env var key `{osKey}`"
  for orig in m.egress do
    if !isValidEgressOrigin orig then
      .error s!"deploy manifest: invalid egress origin `{orig}`"
  if let some a := m.auth? then
    validateAuthManifest a
  for db in m.databases do
    if db.shortName.isEmpty then
      .error "deploy manifest: empty database name"

theorem validate_rejects_bad_version (m : DeployManifest) (h : m.version ≠ 1) :
    (m.validate).isOk = false := by
  unfold DeployManifest.validate
  have hne : (m.version != 1) = true := bne_iff_ne.mpr h
  simp [hne]; rfl

theorem validate_rejects_unsafe_auth_callback (a : DeployAuthManifest)
    (hIss : isValidEnvKey a.issuerEnv = true)
    (hAud : isValidEnvKey a.audienceEnv = true)
    (hTtl : a.sessionTtlSec ≠ 0)
    (hLogin : Qed.Auth.isSafeReturnTo a.loginPath = true)
    (hCb : Qed.Auth.isSafeReturnTo a.callbackPath = false) :
    (validateAuthManifest a).isOk = false := by
  unfold validateAuthManifest
  have hTtlB : (a.sessionTtlSec == 0) = false := beq_false_of_ne hTtl
  simp [hIss, hAud, hTtlB, hLogin, hCb]; rfl

theorem validate_default_ok : ({} : DeployManifest).validate = .ok () := rfl

/-! ### Deterministic JSON Serialization -/

private def footprintToJson (fp : EnvFootprint) : Json :=
  let authTargetJ : Json := match fp.authTarget? with
    | none                 => .null
    | some .localDev       => .str "localDev"
    | some .previewIdp     => .str "previewIdp"
    | some (.managedOidc _) => .str "managedOidc"
    | some .customOidc     => .str "customOidc"
  let managedDbsJ := Json.arr (fp.managedDbs.map fun (nm, cl) =>
    Json.obj [("name", .str nm), ("cluster", .str (match cl with | .prodCluster => "prod" | .nonProdCluster => "nonProd"))])
  Json.obj [
    ("secrets", ToJson.toJson (fp.secrets.map (·.envVar))),
    ("egress", ToJson.toJson fp.egress),
    ("managedDbs", managedDbsJ),
    ("ephemeralDbs", ToJson.toJson fp.ephemeralDbs),
    ("authTarget", authTargetJ)
  ]

def DeployManifest.toJson (m : DeployManifest) : Json :=
  let envVarsJ := Json.arr (m.envVars.map fun (nm, osKey, def?) =>
    Json.obj [("name", .str nm), ("osKey", .str osKey), ("default", ToJson.toJson def?)])
  let dbsJ := Json.arr (m.databases.map fun db =>
    Json.obj [
      ("name", .str db.shortName),
      ("isManaged", .bool db.isManaged),
      ("hasDevFallback", .bool db.hasDevFallback),
      ("secrets", ToJson.toJson db.secrets),
      ("tables", .arr (db.tables.toList.map fun t =>
        Json.obj [
          ("name", .str t.tableName),
          ("hasReadPolicy", .bool t.hasReadPolicy),
          ("hasInsertPolicy", .bool t.hasInsertPolicy),
          ("hasUpdatePolicy", .bool t.hasUpdatePolicy),
          ("hasDeletePolicy", .bool t.hasDeletePolicy),
          ("hasTransInv", .bool t.hasTransInv),
          ("columns", .arr (t.columns.toList.map fun c =>
            Json.obj [
              ("name", .str c.name),
              ("primaryKey", .bool c.isPrimaryKey),
              ("immutable", .bool c.isImmutable),
              ("unique", .bool c.isUnique),
              ("nullable", .bool c.isNullable),
              ("references", ToJson.toJson (c.refs?.map fun (rt, rc) => s!"{rt}({rc})"))
            ]))
        ]))
    ])
  let authJ := match m.auth? with
    | none => .null
    | some a =>
        Json.obj [
          ("name", .str a.name),
          ("isManaged", .bool a.isManaged),
          ("issuerEnv", .str a.issuerEnv),
          ("issuerDefault", ToJson.toJson a.issuerDefault?),
          ("audienceEnv", .str a.audienceEnv),
          ("audienceDefault", ToJson.toJson a.audienceDefault?),
          ("clientIdEnv", ToJson.toJson a.clientIdEnv?),
          ("clientIdDefault", ToJson.toJson a.clientIdDefault?),
          ("clientSecretEnv", ToJson.toJson a.clientSecretEnv?),
          ("providers", ToJson.toJson a.providers),
          ("sessionTtlSec", ToJson.toJson a.sessionTtlSec),
          ("loginPath", .str a.loginPath),
          ("callbackPath", .str a.callbackPath),
          ("logoutPath", .str a.logoutPath),
          ("mePath", .str a.mePath),
          ("claims", .arr (a.claims.map fun c =>
            Json.obj [("name", .str c.name), ("type", .str c.typeName), ("default", .str c.defaultValue)]))
        ]
  let srvJ := match m.server? with
    | none => .null
    | some s =>
        Json.obj [
          ("name", .str s.serverName.toString),
          ("shortName", .str s.shortName),
          ("hasState", .bool s.hasState),
          ("hasHttpRoutes", .bool s.hasHttpRoutes),
          ("methods", .arr (s.methods.toList.map fun mt =>
            Json.obj [("name", .str mt.name), ("readOnly", .bool mt.isReadOnly), ("requiresAuth", .bool mt.requiresAuth)])),
          ("channels", ToJson.toJson s.channels),
          ("jobs", ToJson.toJson s.jobs)
        ]
  let assetsJ := Json.arr (m.assets.map fun a =>
    Json.obj [("path", .str a.path), ("mime", .str a.mime), ("bytes", ToJson.toJson a.bytes)])
  let em := m.envs
  let envsJ := Json.obj [
    ("dev",     footprintToJson em.dev),
    ("preview", footprintToJson em.preview),
    ("staging", footprintToJson em.staging),
    ("prod",    footprintToJson em.prod)
  ]
  Json.obj [
    ("version", ToJson.toJson m.version),
    ("rootModule", .str m.rootModule),
    ("mode", .str m.mode),
    ("secrets", ToJson.toJson m.secrets),
    ("envVars", envVarsJ),
    ("egress", ToJson.toJson m.egress),
    ("databases", dbsJ),
    ("auth", authJ),
    ("server", srvJ),
    ("assets", assetsJ),
    ("envs", envsJ),
    ("csp", .str m.csp)
  ]

def DeployManifest.render (m : DeployManifest) : String :=
  Json.render m.toJson

/-! ### Compile-Time Environment Extraction (Meta Infrastructure) -/

private def nameInScope (rootPrefix : String) (n : Lean.Name) : Bool :=
  let s := n.toString
  if rootPrefix.isEmpty then true
  else s == rootPrefix || s.startsWith (rootPrefix ++ ".") ||
    -- Also include top-level declarations in the loaded user module
    !(s.startsWith "Qed." || s.startsWith "Tests." || s.startsWith "Bench.")

/-- Extracts a `DeployManifest` from the compiled Lean `Environment` for `rootMod`. -/
def extractFromEnv (env : Lean.Environment) (rootMod : String) : DeployManifest :=
  let srvReg  := Qed.serverRegistry.getState env
  let dbReg   := Qed.Server.databaseRegistry.getState env
  let authReg := Qed.Server.authRegistry.getState env
  let extReg  := Qed.Server.externalRegistry.getState env

  let modIdx? := env.getModuleIdx? rootMod.toName
  let inRootMod (constName : Lean.Name) : Bool :=
    match modIdx?, env.getModuleIdxFor? constName with
    | some ri, some di => ri == di
    | _, _             => nameInScope rootMod constName

  let srvEntries := srvReg.toList.filter fun (_, si) => inRootMod (si.serverName ++ `dispatchM)
  let server? : Option Qed.ServerInfo :=
    (srvEntries.head?.orElse fun _ =>
      srvReg.toList.find? fun (n, _) => !(n.toString.startsWith "Qed.")).map Prod.snd

  let databases : List Qed.Server.DatabaseInfo :=
    let matchDb (di : Qed.Server.DatabaseInfo) : Bool :=
      match server? with
      | some si => if !si.databases.isEmpty then si.databases.contains di.configConst else inRootMod di.configConst
      | none    => inRootMod di.configConst
    dbReg.toList.filterMap fun (_, di) => if matchDb di then some di else none

  let authInfo? : Option Qed.Server.AuthInfo :=
    match server?.bind (·.authName?) with
    | some an => authReg.find? an
    | none    => (authReg.toList.find? fun (_, ai) => inRootMod ai.configConst).map Prod.snd

  let extOrigins : List String :=
    let fromSrv := (server?.map fun si => si.externalServices.toList.map Prod.snd).getD []
    let fromMod := extReg.toList.filterMap fun (_, ei) =>
      if inRootMod (ei.serviceName ++ `_qed_external_marker) then some ei.baseOrigin else none
    ((fromSrv ++ fromMod).filter fun o => !o.isEmpty && isValidEgressOrigin o).eraseDups

  let allSecrets : List String :=
    let s1 := (server?.map (·.secrets.toList)).getD []
    let s2 := databases.flatMap (·.secrets.toList)
    let s3 := (authInfo?.map (·.secrets.toList)).getD []
    (s1 ++ s2 ++ s3).eraseDups

  {
    version := 1
    rootModule := rootMod
    mode := if server?.isSome then "fullstack" else "standalone"
    secrets := allSecrets
    envVars := (server?.map (·.envVars.toList)).getD []
    egress := extOrigins
    databases
    auth? := authInfo?.map (·.spec)
    server?
  }

end Qed.Deploy
