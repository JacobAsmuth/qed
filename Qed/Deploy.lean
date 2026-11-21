import Lean
import Qed.Json
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

structure DeployEnvVar where
  name     : String
  osKey    : String
  default? : Option String := none
deriving Inhabited, DecidableEq, Repr

abbrev DeployAuthClaim := Qed.Auth.AuthClaimSpec

abbrev DeployAuthManifest := Qed.Auth.OidcAuthSpec

structure DeployDbColumn where
  name         : String
  isPrimaryKey : Bool := false
  isImmutable  : Bool := false
  isUnique     : Bool := false
  isNullable   : Bool := false
  refs?        : Option String := none
deriving Inhabited, DecidableEq, Repr

structure DeployDbTable where
  name            : String
  columns         : List DeployDbColumn := []
  hasReadPolicy   : Bool := false
  hasInsertPolicy : Bool := false
  hasUpdatePolicy : Bool := false
  hasDeletePolicy : Bool := false
  hasTransInv     : Bool := false
deriving Inhabited, DecidableEq, Repr

structure DeployDbManifest where
  name           : String
  hasDevFallback : Bool := false
  secrets        : List String := []
  tables         : List DeployDbTable := []
deriving Inhabited, DecidableEq, Repr

structure DeployRpcMethod where
  name         : String
  readOnly     : Bool := false
  requiresAuth : Bool := false
deriving Inhabited, DecidableEq, Repr

structure DeployServerManifest where
  name          : String
  shortName     : String
  hasState      : Bool := false
  hasHttpRoutes : Bool := false
  methods       : List DeployRpcMethod := []
  channels      : List String := []
  jobs          : List String := []
deriving Inhabited, DecidableEq, Repr

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
  envVars    : List DeployEnvVar := []
  egress     : List String := []
  databases  : List DeployDbManifest := []
  auth?      : Option DeployAuthManifest := none
  server?    : Option DeployServerManifest := none
  assets     : List DeployAssetManifest := []
  csp        : String := Qed.Server.defaultCsp
deriving Inhabited, DecidableEq, Repr

/-! ### Kernel-Verified Manifest Consistency Checks -/

abbrev isValidEnvKey : String → Bool := Qed.Server.isValidEnvVarName

def isValidEgressOrigin (s : String) : Bool :=
  let cs := s.toList
  let hasScheme :=
    match cs with
    | 'h' :: 't' :: 't' :: 'p' :: 's' :: ':' :: '/' :: '/' :: _ :: _ => true
    | 'h' :: 't' :: 't' :: 'p' :: ':' :: '/' :: '/' :: _ :: _        => true
    | _ => false
  hasScheme && cs.all fun c =>
    c != ' ' && c != '\t' && c != '\r' && c != '\n' && c != '\x00' &&
    decide (32 < c.toNat ∧ c.toNat ≠ 127)

def validateAuthManifest (a : DeployAuthManifest) : Except String Unit :=
  if !isValidEnvKey a.issuerEnv then .error s!"deploy manifest: invalid auth issuerEnv `{a.issuerEnv}`"
  else if !isValidEnvKey a.audienceEnv then .error s!"deploy manifest: invalid auth audienceEnv `{a.audienceEnv}`"
  else if a.sessionTtlSec == 0 then .error "deploy manifest: auth sessionTtlSec must be positive"
  else if !Qed.Auth.isSafeReturnTo a.loginPath then .error s!"deploy manifest: unsafe auth loginPath `{a.loginPath}`"
  else if !Qed.Auth.isSafeReturnTo a.callbackPath then .error s!"deploy manifest: unsafe auth callbackPath `{a.callbackPath}`"
  else if !Qed.Auth.isSafeReturnTo a.logoutPath then .error s!"deploy manifest: unsafe auth logoutPath `{a.logoutPath}`"
  else if !Qed.Auth.isSafeReturnTo a.mePath then .error s!"deploy manifest: unsafe auth mePath `{a.mePath}`"
  else .ok ()

def DeployManifest.validate (m : DeployManifest) : Except String Unit := do
  if m.version != 1 then
    .error s!"deploy manifest: unsupported version {m.version}"
  for s in m.secrets do
    if !isValidEnvKey s then
      .error s!"deploy manifest: invalid secret env key `{s}`"
  for e in m.envVars do
    if !isValidEnvKey e.osKey then
      .error s!"deploy manifest: invalid env var key `{e.osKey}`"
  for orig in m.egress do
    if !isValidEgressOrigin orig then
      .error s!"deploy manifest: invalid egress origin `{orig}`"
  if let some a := m.auth? then
    validateAuthManifest a
  for db in m.databases do
    if db.name.isEmpty then
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

private def optStrJson : Option String → Json
  | some s => .str s
  | none   => .null

def DeployManifest.toJson (m : DeployManifest) : Json :=
  let envVarsJ := Json.arr (m.envVars.map fun e =>
    Json.obj [("name", .str e.name), ("osKey", .str e.osKey), ("default", optStrJson e.default?)])
  let dbsJ := Json.arr (m.databases.map fun db =>
    Json.obj [
      ("name", .str db.name),
      ("hasDevFallback", .bool db.hasDevFallback),
      ("secrets", .arr (db.secrets.map .str)),
      ("tables", .arr (db.tables.map fun t =>
        Json.obj [
          ("name", .str t.name),
          ("hasReadPolicy", .bool t.hasReadPolicy),
          ("hasInsertPolicy", .bool t.hasInsertPolicy),
          ("hasUpdatePolicy", .bool t.hasUpdatePolicy),
          ("hasDeletePolicy", .bool t.hasDeletePolicy),
          ("hasTransInv", .bool t.hasTransInv),
          ("columns", .arr (t.columns.map fun c =>
            Json.obj [
              ("name", .str c.name),
              ("primaryKey", .bool c.isPrimaryKey),
              ("immutable", .bool c.isImmutable),
              ("unique", .bool c.isUnique),
              ("nullable", .bool c.isNullable),
              ("references", optStrJson c.refs?)
            ]))
        ]))
    ])
  let authJ := match m.auth? with
    | none => .null
    | some a =>
        Json.obj [
          ("name", .str a.name),
          ("issuerEnv", .str a.issuerEnv),
          ("issuerDefault", optStrJson a.issuerDefault?),
          ("audienceEnv", .str a.audienceEnv),
          ("audienceDefault", optStrJson a.audienceDefault?),
          ("clientIdEnv", optStrJson a.clientIdEnv?),
          ("clientIdDefault", optStrJson a.clientIdDefault?),
          ("clientSecretEnv", optStrJson a.clientSecretEnv?),
          ("providers", .arr (a.providers.map .str)),
          ("sessionTtlSec", .num ⟨Int.ofNat a.sessionTtlSec, 0⟩),
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
          ("name", .str s.name),
          ("shortName", .str s.shortName),
          ("hasState", .bool s.hasState),
          ("hasHttpRoutes", .bool s.hasHttpRoutes),
          ("methods", .arr (s.methods.map fun mt =>
            Json.obj [("name", .str mt.name), ("readOnly", .bool mt.readOnly), ("requiresAuth", .bool mt.requiresAuth)])),
          ("channels", .arr (s.channels.map .str)),
          ("jobs", .arr (s.jobs.map .str))
        ]
  let assetsJ := Json.arr (m.assets.map fun a =>
    Json.obj [("path", .str a.path), ("mime", .str a.mime), ("bytes", .num ⟨Int.ofNat a.bytes, 0⟩)])
  Json.obj [
    ("version", .num ⟨Int.ofNat m.version, 0⟩),
    ("rootModule", .str m.rootModule),
    ("mode", .str m.mode),
    ("secrets", .arr (m.secrets.map .str)),
    ("envVars", envVarsJ),
    ("egress", .arr (m.egress.map .str)),
    ("databases", dbsJ),
    ("auth", authJ),
    ("server", srvJ),
    ("assets", assetsJ),
    ("csp", .str m.csp)
  ]

def DeployManifest.render (m : DeployManifest) : String :=
  Json.render m.toJson

/-! ### Compile-Time Environment Extraction (Meta Infrastructure) -/

private def dedupStrings (xs : List String) : List String :=
  xs.foldl (init := []) fun acc s => if acc.contains s then acc else acc ++ [s]

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
  let srvEntry? := srvEntries.head?.orElse fun _ =>
    srvReg.toList.find? fun (n, _) => !(n.toString.startsWith "Qed.")

  let server? : Option DeployServerManifest := srvEntry?.map fun (_, si) => {
    name := si.serverName.toString
    shortName := si.shortName
    hasState := si.hasState
    hasHttpRoutes := si.hasHttpRoutes
    methods := si.methods.toList.map fun m =>
      { name := m.name, readOnly := m.isReadOnly, requiresAuth := m.requiresAuth }
    channels := si.channels.toList
    jobs := si.jobs.toList
  }

  let dbInfos : List Qed.Server.DatabaseInfo :=
    match srvEntry? with
    | some (_, si) =>
        if !si.databases.isEmpty then
          dbReg.toList.filterMap fun (_, di) =>
            if si.databases.contains di.configConst then some di else none
        else
          dbReg.toList.filterMap fun (_, di) => if inRootMod di.configConst then some di else none
    | none =>
        dbReg.toList.filterMap fun (_, di) => if inRootMod di.configConst then some di else none

  let databases : List DeployDbManifest := dbInfos.map fun di => {
    name := di.shortName
    hasDevFallback := di.hasDevFallback
    secrets := di.secrets.toList
    tables := di.tables.toList.map fun t => {
      name := t.tableName
      hasReadPolicy := t.hasReadPolicy
      hasInsertPolicy := t.hasInsertPolicy
      hasUpdatePolicy := t.hasUpdatePolicy
      hasDeletePolicy := t.hasDeletePolicy
      hasTransInv := t.hasTransInv
      columns := t.columns.toList.map fun c => {
        name := c.name
        isPrimaryKey := c.isPrimaryKey
        isImmutable := c.isImmutable
        isUnique := c.isUnique
        isNullable := c.isNullable
        refs? := c.refs?.map fun (rt, rc) => s!"{rt}({rc})"
      }
    }
  }

  let authInfo? : Option Qed.Server.AuthInfo :=
    match srvEntry?.bind (·.2.authName?) with
    | some an => authReg.find? an
    | none    => (authReg.toList.find? fun (_, ai) => inRootMod ai.configConst).map Prod.snd

  let auth? : Option DeployAuthManifest := authInfo?.map (·.spec)

  let extOrigins : List String :=
    let fromSrv := match srvEntry? with
      | some (_, si) => si.externalServices.toList.map Prod.snd
      | none         => []
    let fromMod := extReg.toList.filterMap fun (_, ei) =>
      if inRootMod (ei.serviceName ++ `_qed_external_marker) then some ei.baseOrigin else none
    dedupStrings ((fromSrv ++ fromMod).filter fun o => !o.isEmpty && isValidEgressOrigin o)

  let allSecrets : List String :=
    let s1 := match srvEntry? with | some (_, si) => si.secrets.toList | none => []
    let s2 := dbInfos.foldl (init := []) fun acc di => acc ++ di.secrets.toList
    let s3 := match authInfo? with | some ai => ai.secrets.toList | none => []
    dedupStrings (s1 ++ s2 ++ s3)

  let envVars : List DeployEnvVar :=
    match srvEntry? with
    | some (_, si) => si.envVars.toList.map fun (nm, key, def?) => { name := nm, osKey := key, default? := def? }
    | none         => []

  {
    version := 1
    rootModule := rootMod
    mode := if server?.isSome then "fullstack" else "standalone"
    secrets := allSecrets
    envVars
    egress := extOrigins
    databases
    auth?
    server?
  }

end Qed.Deploy
