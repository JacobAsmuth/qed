import Lean
import Qed.Json
import Qed.Cloud.Env
import Qed.Cloud.Gcp
import Qed.Auth.Core
import Qed.Server.Core
import Qed.Server.Registry

namespace Qed.Deploy

/-! ## Provably-Complete Deployment & Infrastructure Manifest (`Qed.Deploy`) -/

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
  deploy?    : Option Qed.Cloud.DeploySpec := none
  assets     : List DeployAssetManifest := []
  csp        : String := Qed.Server.defaultCsp
deriving Inhabited

structure EnvFootprint where
  secrets      : List Qed.Cloud.SecretRef := []
  egress       : List String := []
  managedDbs   : List (String × Qed.Cloud.DbCluster) := []
  ephemeralDbs : List String := []
  authTarget?  : Option Qed.Cloud.AuthEnvTarget := none
deriving Inhabited, DecidableEq, Repr

private def dedupSecretsByEnvVar (xs : List Qed.Cloud.SecretRef) : List Qed.Cloud.SecretRef :=
  xs.foldl (init := []) fun acc s => if acc.any (·.envVar == s.envVar) then acc else acc ++ [s]

def DeployManifest.footprintFor (m : DeployManifest) (env : Qed.Cloud.DeployEnv) : EnvFootprint :=
  let dbSpecs := m.databases.map fun db => (db.shortName, db.envSpecs.get env)
  let dbSecrets := dbSpecs.flatMap fun (_, sp) => sp.secrets.filter (·.allowedIn env)
  let srvSecrets : List Qed.Cloud.SecretRef := ((m.server?.map (·.ownSecrets.toList)).getD []).map fun k => { envVar := k, scope := .envScoped }
  let authSecrets : List Qed.Cloud.SecretRef := match m.auth? with
    | some a => if a.isManaged && (env == .dev || env == .preview) then []
                else (a.clientSecretEnv?.map fun s => [{ envVar := s, scope := .envScoped }]).getD []
    | none => []
  let rawSecrets := if m.server?.isSome || !m.databases.isEmpty || m.auth?.isSome then dbSecrets ++ srvSecrets ++ authSecrets
    else m.secrets.map fun k => { envVar := k, scope := .envScoped }
  { secrets := dedupSecretsByEnvVar rawSecrets, egress := (m.egress ++ dbSpecs.flatMap (·.2.egressOrigins)).eraseDups,
    managedDbs := dbSpecs.filterMap fun (nm, sp) => sp.cluster?.map (nm, ·),
    ephemeralDbs := dbSpecs.filterMap fun (nm, sp) => if sp.isEphemeral then some nm else none,
    authTarget? := m.auth?.map fun a => if a.isManaged then (Qed.Cloud.managedAuthTargets a.providers).get env else .customOidc }

def DeployManifest.envs (m : DeployManifest) : Qed.Cloud.EnvMap EnvFootprint :=
  { dev := m.footprintFor .dev, preview := m.footprintFor .preview, staging := m.footprintFor .staging, prod := m.footprintFor .prod }

/-! ### Kernel-Verified Manifest Consistency Checks -/

abbrev isValidEnvKey : String → Bool := Qed.Server.isValidEnvVarName

private def isPrivateOrMetadataHost (host : String) : Bool :=
  let low := host.toLower
  low == "metadata.google.internal" || [".internal", ".localdomain", ".home.arpa"].any (low.endsWith ·) ||
  (Qed.Cloud.parseIpv4UInt32 low).any fun ip =>
    let (b0, b1) := (ip >>> 24, (ip >>> 16) &&& 0xFF)
    b0 == 0 || b0 == 10 || b0 == 127 || (b0 == 100 && 64 ≤ b1 && b1 ≤ 127) ||
    (b0 == 169 && b1 == 254) || (b0 == 172 && 16 ≤ b1 && b1 ≤ 31) || (b0 == 192 && b1 == 168)

def isValidEgressOrigin (s : String) : Bool :=
  match s.toList with
  | 'h' :: 't' :: 't' :: 'p' :: 's' :: ':' :: '/' :: '/' :: auth =>
      if auth.isEmpty || auth.any (fun c => "/?#@\\*".contains c || c.toNat ≤ 32 || c.toNat == 127) then false
      else
        let (hc, portOk) := match Qed.Cloud.splitCharAux ':' auth [] with
          | [h] => (h, true) | [h, p] => (h, (Qed.Cloud.parsePort? p).isSome) | _ => ([], false)
        let host := String.ofList hc
        portOk && !hc.isEmpty && Qed.Cloud.isValidHostname host && !Qed.Cloud.isLocalhostUrl s && !Qed.Cloud.isReservedLocalDomain host && !isPrivateOrMetadataHost host
  | _ => false

def isValidDbShortName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => let isA (ch : Char) := ('A' ≤ ch && ch ≤ 'Z') || ('a' ≤ ch && ch ≤ 'z')
               s.toList.length ≤ 63 && isA c && cs.all fun ch => isA ch || ('0' ≤ ch && ch ≤ '9') || ch == '_'

def isValidAssetPath (p : String) : Bool :=
  let cs := p.toList
  if cs.isEmpty || cs.any (fun c => c == '\\' || c == '?' || c == '#' || c.toNat < 32 || c.toNat == 127) then false
  else
    let rel := match cs with | '/' :: rest => rest | _ => cs
    if rel.isEmpty then false
    else
      let segs := Qed.Cloud.splitCharAux '/' rel []
      let lastOk := (segs.getLast?.map fun last => let low := last.map Qed.Cloud.asciiToLower; low != "qed_deploy.json".toList && low != "qed_manifest.json".toList).getD false
      lastOk && segs.all fun seg => !seg.isEmpty && seg != ['.'] && seg != ['.', '.']

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

private def checkEach {α : Type} (xs : List α) (ok : α → Bool) (err : α → String) : Except String Unit :=
  xs.forM fun x => if ok x then .ok () else .error s!"deploy manifest: {err x}"

def DeployManifest.validate (m : DeployManifest) : Except String Unit := do
  if m.version != 1 then .error s!"deploy manifest: unsupported version {m.version}"
  checkEach m.secrets isValidEnvKey (s!"invalid secret env key `{·}`")
  checkEach m.envVars (isValidEnvKey ·.2.1) (fun (_, k, _) => s!"invalid env var key `{k}`")
  checkEach m.egress isValidEgressOrigin (s!"invalid egress origin `{·}`")
  if let some a := m.auth? then validateAuthManifest a
  if let some d := m.deploy? then d.validate
  let dbVars := m.databases.map (Qed.Cloud.managedPostgresSecretVar ·.shortName)
  if dbVars.eraseDups.length != dbVars.length then .error "deploy manifest: duplicate database name or managedPostgresSecretVar collision"
  for db in m.databases do
    if !isValidDbShortName db.shortName then .error s!"deploy manifest: invalid database name `{db.shortName}`"
    for e in Qed.Cloud.DeployEnv.all do
      checkEach (db.envSpecs.get e).secrets (·.allowedIn e) (fun sr => s!"database `{db.shortName}` binds pinned secret `{sr.envVar}` into `{e}`")
      checkEach (db.envSpecs.get e).secrets (isValidEnvKey ·.envVar) (fun sr => s!"database `{db.shortName}` has invalid secret env key `{sr.envVar}`")
  for e in Qed.Cloud.DeployEnv.all do
    let fp := m.footprintFor e
    checkEach fp.secrets (·.allowedIn e) (fun sr => s!"footprint for `{e}` contains disallowed pinned secret `{sr.envVar}`")
    checkEach fp.secrets (isValidEnvKey ·.envVar) (fun sr => s!"footprint for `{e}` contains invalid secret env key `{sr.envVar}`")
    checkEach fp.egress isValidEgressOrigin (fun o => s!"footprint for `{e}` contains invalid egress origin `{o}`")
  checkEach m.assets (isValidAssetPath ·.path) (fun a => s!"invalid asset path `{a.path}`")

theorem validate_rejects_bad_version (m : DeployManifest) (h : m.version ≠ 1) : (m.validate).isOk = false := by
  unfold DeployManifest.validate; simp [bne_iff_ne.mpr h]; rfl

theorem validate_rejects_unsafe_auth_callback (a : DeployAuthManifest)
    (hIss : isValidEnvKey a.issuerEnv = true) (hAud : isValidEnvKey a.audienceEnv = true) (hTtl : a.sessionTtlSec ≠ 0)
    (hLogin : Qed.Auth.isSafeReturnTo a.loginPath = true) (hCb : Qed.Auth.isSafeReturnTo a.callbackPath = false) :
    (validateAuthManifest a).isOk = false := by
  unfold validateAuthManifest; simp [hIss, hAud, beq_false_of_ne hTtl, hLogin, hCb]; rfl

theorem validate_default_ok : ({} : DeployManifest).validate = .ok () := rfl

/-! ### Deterministic JSON Serialization -/

private def optJson {α : Type} (o : Option α) (f : α → Json) : Json := (o.map f).getD .null

private def footprintToJson (fp : EnvFootprint) : Json := Json.obj [
  ("secrets", ToJson.toJson (fp.secrets.map (·.envVar))), ("egress", ToJson.toJson fp.egress),
  ("managedDbs", .arr <| fp.managedDbs.map fun (nm, cl) => Json.obj [("name", .str nm), ("cluster", .str (match cl with | .prodCluster => "prod" | .nonProdCluster => "nonProd"))]),
  ("ephemeralDbs", ToJson.toJson fp.ephemeralDbs),
  ("authTarget", optJson fp.authTarget? fun | .localDev => .str "localDev" | .previewIdp => .str "previewIdp" | .managedOidc _ => .str "managedOidc" | .customOidc => .str "customOidc")]

def DeployManifest.toJson (m : DeployManifest) : Json := Json.obj [
  ("version", ToJson.toJson m.version), ("rootModule", .str m.rootModule), ("mode", .str m.mode), ("secrets", ToJson.toJson m.secrets),
  ("envVars", .arr <| m.envVars.map fun (nm, osKey, def?) => Json.obj [("name", .str nm), ("osKey", .str osKey), ("default", ToJson.toJson def?)]),
  ("egress", ToJson.toJson m.egress),
  ("databases", .arr <| m.databases.map fun db => Json.obj [
    ("name", .str db.shortName), ("isManaged", .bool db.isManaged), ("hasDevFallback", .bool db.hasDevFallback), ("secrets", ToJson.toJson db.secrets),
    ("tables", .arr <| db.tables.toList.map fun t => Json.obj [
      ("name", .str t.tableName), ("hasReadPolicy", .bool t.hasReadPolicy), ("hasInsertPolicy", .bool t.hasInsertPolicy),
      ("hasUpdatePolicy", .bool t.hasUpdatePolicy), ("hasDeletePolicy", .bool t.hasDeletePolicy), ("hasTransInv", .bool t.hasTransInv),
      ("columns", .arr <| t.columns.toList.map fun c => Json.obj [
        ("name", .str c.name), ("primaryKey", .bool c.isPrimaryKey), ("immutable", .bool c.isImmutable),
        ("unique", .bool c.isUnique), ("nullable", .bool c.isNullable),
        ("references", ToJson.toJson (c.refs?.map fun (rt, rc) => s!"{rt}({rc})"))])])]),
  ("auth", optJson m.auth? fun a => Json.obj [
    ("name", .str a.name), ("isManaged", .bool a.isManaged), ("issuerEnv", .str a.issuerEnv), ("issuerDefault", ToJson.toJson a.issuerDefault?),
    ("audienceEnv", .str a.audienceEnv), ("audienceDefault", ToJson.toJson a.audienceDefault?), ("clientIdEnv", ToJson.toJson a.clientIdEnv?),
    ("clientIdDefault", ToJson.toJson a.clientIdDefault?), ("clientSecretEnv", ToJson.toJson a.clientSecretEnv?), ("providers", ToJson.toJson a.providers),
    ("sessionTtlSec", ToJson.toJson a.sessionTtlSec), ("loginPath", .str a.loginPath), ("callbackPath", .str a.callbackPath),
    ("logoutPath", .str a.logoutPath), ("mePath", .str a.mePath),
    ("claims", .arr <| a.claims.map fun c => Json.obj [("name", .str c.name), ("type", .str c.typeName), ("default", .str c.defaultValue)])]),
  ("server", optJson m.server? fun s => Json.obj [
    ("name", .str s.serverName.toString), ("shortName", .str s.shortName), ("hasState", .bool s.hasState), ("hasHttpRoutes", .bool s.hasHttpRoutes),
    ("methods", .arr <| s.methods.toList.map fun mt => Json.obj [("name", .str mt.name), ("readOnly", .bool mt.isReadOnly), ("requiresAuth", .bool mt.requiresAuth)]),
    ("channels", ToJson.toJson s.channels), ("jobs", ToJson.toJson s.jobs)]),
  ("deploy", optJson m.deploy? fun d => Json.obj [
    ("name", .str d.name), ("appName", .str d.appName), ("regions", ToJson.toJson (d.regions.map Qed.Cloud.GcpRegion.toString)),
    ("domain", ToJson.toJson d.domain?), ("compute", .str d.compute.toString), ("timeoutSec", ToJson.toJson d.timeoutSec?),
    ("preview", Json.obj [
      ("enabled", .bool d.preview.enabled), ("subdomain", ToJson.toJson d.preview.subdomain?),
      ("host", ToJson.toJson (d.preview.resolvedHost? d.domain? |>.map (·.render))),
      ("protection", .str (match d.preview.protection with | .team_only => "team_only" | .pub => "public")), ("ttlSec", ToJson.toJson d.preview.ttlSec)])]),
  ("assets", .arr <| m.assets.map fun a => Json.obj [("path", .str a.path), ("mime", .str a.mime), ("bytes", ToJson.toJson a.bytes)]),
  ("envs", Json.obj <| Qed.Cloud.DeployEnv.all.map fun e => (e.toString, footprintToJson (m.footprintFor e))),
  ("csp", .str m.csp)]

def DeployManifest.render (m : DeployManifest) : String := Json.render m.toJson

/-! ### Compile-Time Environment Extraction (Meta Infrastructure) -/

def extractFromEnv (env : Lean.Environment) (rootMod : String)
    (targetServer? : Option Lean.Name := none) (explicitTarget : Bool := false) : DeployManifest :=
  let (srvReg, dbReg, authReg, extReg) :=
    (Qed.serverRegistry.getState env, Qed.Server.databaseRegistry.getState env, Qed.Server.authRegistry.getState env, Qed.Server.externalRegistry.getState env)
  let modIdx? := env.getModuleIdx? rootMod.toName
  let inRootMod (c : Lean.Name) : Bool := match modIdx?, env.getModuleIdxFor? c with
    | some ri, some di => ri == di | _, _ => rootMod.isEmpty || c.toString == rootMod || c.toString.startsWith (rootMod ++ ".")
  let server? : Option Qed.ServerInfo := match targetServer? with
    | some srvName => srvReg.find? srvName
    | none => if explicitTarget then none else (srvReg.toList.find? fun (_, si) => inRootMod (si.serverName ++ `dispatchM)).map Prod.snd
  let databases := match server? with
    | some si => dbReg.toList.filterMap fun (_, di) => if si.databases.contains di.configConst then some di else none
    | none => if explicitTarget then [] else dbReg.toList.filterMap fun (_, di) => if inRootMod di.configConst then some di else none
  let authInfo? : Option Qed.Server.AuthInfo := match server? with
    | some si => si.authName?.bind authReg.find?
    | none => if explicitTarget then none else (authReg.toList.find? fun (_, ai) => inRootMod ai.configConst).map Prod.snd
  let rawEgress : List String := match server? with
    | some si => si.externalServices.toList.map Prod.snd
    | none => if explicitTarget then [] else extReg.toList.filterMap fun (_, ei) => if inRootMod (ei.serviceName ++ `_qed_external_marker) then some ei.baseOrigin else none
  { version := 1, rootModule := rootMod, mode := if server?.isSome then "fullstack" else "standalone",
    secrets := ((server?.map (·.secrets.toList)).getD [] ++ databases.flatMap (·.secrets.toList) ++ (authInfo?.map (·.secrets.toList)).getD []).eraseDups,
    envVars := (server?.map (·.envVars.toList)).getD [],
    egress := (rawEgress.filter fun o => !o.isEmpty && isValidEgressOrigin o).eraseDups,
    databases, auth? := authInfo?.map (·.spec), server? }

end Qed.Deploy
