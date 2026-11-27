import Qed.Json.Basic
import Qed.Cloud.Gcp
import Qed.Auth.Core
import Qed.Server.Core

namespace Qed.Deploy
open Qed.Cloud

/-! ## Provably-Complete Deployment & Infrastructure Manifest (`Qed.Deploy`) -/

abbrev DeployAuthManifest := Qed.Auth.OidcAuthSpec

structure DeployAssetManifest where
  (path mime : String) (bytes : Nat := 0)
deriving Inhabited, DecidableEq

structure DeployColumnManifest where
  (name : String) (isPrimaryKey isImmutable isUnique isNullable : Bool := false) (refs? : Option (String × String) := none)
deriving Inhabited

structure DeployTableManifest where
  (tableName : String) (columns : List DeployColumnManifest := [])
  (hasReadPolicy hasInsertPolicy hasUpdatePolicy hasDeletePolicy hasTransInv : Bool := false)
deriving Inhabited

structure DeployDbManifest where
  (shortName : String) (secrets : List String := []) (hasDevFallback isManaged : Bool := false)
  (envSpecs : EnvMap DbEnvSpec := EnvMap.ofDefault (.byoSqlite "")) (tables : List DeployTableManifest := [])
deriving Inhabited

structure DeployMethodManifest where
  (name : String) (isReadOnly requiresAuth : Bool := false)
deriving Inhabited

structure DeployServerManifest where
  (name shortName : String) (hasState : Bool := false) (ownSecrets : List String := [])
  (hasHttpRoutes : Bool := false) (methods : List DeployMethodManifest := []) (channels jobs : List String := [])
deriving Inhabited

structure DeployManifest where
  (version : Nat := 1) (rootModule : String := "") (mode : String := "standalone")
  (secrets : List String := []) (envVars : List (String × String × Option String) := [])
  (egress : List String := []) (databases : List DeployDbManifest := [])
  (auth? : Option DeployAuthManifest := none) (server? : Option DeployServerManifest := none)
  (deploy? : Option DeploySpec := none) (assets : List DeployAssetManifest := []) (csp : String := Qed.Server.defaultCsp)
deriving Inhabited

structure EnvFootprint where
  (secrets : List SecretRef := []) (egress : List String := []) (managedDbs : List (String × DbCluster) := [])
  (ephemeralDbs : List String := []) (authTarget? : Option AuthEnvTarget := none)
deriving Inhabited, DecidableEq

private def dedupSecretsByEnvVar (xs : List SecretRef) : List SecretRef :=
  xs.foldl (init := []) fun acc s => if acc.any (·.envVar == s.envVar) then acc else acc ++ [s]

def DeployManifest.footprintFor (m : DeployManifest) (env : DeployEnv) : EnvFootprint :=
  let dbSpecs := m.databases.map fun db => (db.shortName, db.envSpecs.get env)
  let mkScoped (k : String) : SecretRef := { envVar := k, scope := .envScoped }
  let dbSecrets := dbSpecs.flatMap fun (_, sp) => sp.secrets.filter (·.allowedIn env)
  let srvSecrets := ((m.server?.map (·.ownSecrets)).getD []).map mkScoped
  let authSecrets := match m.auth? with
    | some a => if a.isManaged && (env == .dev || env == .preview) then [] else (a.clientSecretEnv?.map fun s => [mkScoped s]).getD []
    | none => []
  let rawSecrets := if m.server?.isSome || !m.databases.isEmpty || m.auth?.isSome then dbSecrets ++ srvSecrets ++ authSecrets else m.secrets.map mkScoped
  { secrets := dedupSecretsByEnvVar rawSecrets, egress := (m.egress ++ dbSpecs.flatMap (·.2.egressOrigins)).eraseDups,
    managedDbs := dbSpecs.filterMap fun (nm, sp) => sp.cluster?.map (nm, ·),
    ephemeralDbs := dbSpecs.filterMap fun (nm, sp) => if sp.isEphemeral then some nm else none,
    authTarget? := m.auth?.map fun a => if a.isManaged then (managedAuthTargets a.providers).get env else .customOidc }

def DeployManifest.envs (m : DeployManifest) : EnvMap EnvFootprint :=
  { dev := m.footprintFor .dev, preview := m.footprintFor .preview, staging := m.footprintFor .staging, prod := m.footprintFor .prod }

/-! ### Kernel-Verified Manifest Consistency Checks -/

abbrev isValidEnvKey : String → Bool := Qed.Server.isValidEnvVarName

private def isPrivateOrMetadataHost (host : String) : Bool :=
  let low := Qed.Str.toLower host
  low == "metadata.google.internal" || [".internal", ".localdomain", ".home.arpa"].any (Qed.Str.endsWith low ·) ||
  (parseIpv4UInt32 low).any fun ip =>
    let (b0, b1) := (ip >>> 24, (ip >>> 16) &&& 0xFF)
    b0 == 0 || b0 == 10 || b0 == 127 || (b0 == 100 && 64 ≤ b1 && b1 ≤ 127) ||
    (b0 == 169 && b1 == 254) || (b0 == 172 && 16 ≤ b1 && b1 ≤ 31) || (b0 == 192 && b1 == 168)

def isValidEgressOrigin (s : String) : Bool :=
  match parseHttpsHostPort? s (lowercaseHost := false) with
  | some (host, _) => !isLocalhostUrl s && !isReservedLocalDomain host && !isPrivateOrMetadataHost host
  | none => false

def isValidDbShortName (s : String) : Bool := checkAsciiIdent 1 63 isAsciiAlpha (fun c => isAsciiAlnum c || c == '_') (s := s)

def isValidAssetPath (p : String) : Bool :=
  let cs := p.toList
  if cs.isEmpty || Env.hasCtrlOrWs p "\\?#" (forbidWs := false) then false
  else
    let rel := match cs with | '/' :: rest => rest | _ => cs
    if rel.isEmpty then false
    else
      let segs := splitCharAux '/' rel []
      let lastOk := (segs.getLast?.map fun last => let low := last.map asciiToLower; low != "qed_deploy.json".toList && low != "qed_manifest.json".toList).getD false
      lastOk && segs.all fun seg => !seg.isEmpty && seg != ['.'] && seg != ['.', '.']

private def checkAll (xs : List (Bool × String)) : Except String Unit :=
  xs.forM fun (bad, msg) => if bad then .error s!"deploy manifest: {msg}" else .ok ()
private def checkEach {α : Type} (xs : List α) (ok : α → Bool) (err : α → String) : Except String Unit :=
  xs.forM fun x => if ok x then .ok () else .error s!"deploy manifest: {err x}"

def validateAuthManifest (a : DeployAuthManifest) : Except String Unit :=
  checkAll [
    (!isValidEnvKey a.issuerEnv, s!"invalid auth issuerEnv `{a.issuerEnv}`"),
    (!isValidEnvKey a.audienceEnv, s!"invalid auth audienceEnv `{a.audienceEnv}`"),
    (a.sessionTtlSec == 0, "auth sessionTtlSec must be positive"),
    (!Qed.Auth.isSafeReturnTo a.loginPath, s!"unsafe auth loginPath `{a.loginPath}`"),
    (!Qed.Auth.isSafeReturnTo a.callbackPath, s!"unsafe auth callbackPath `{a.callbackPath}`"),
    (!Qed.Auth.isSafeReturnTo a.logoutPath, s!"unsafe auth logoutPath `{a.logoutPath}`"),
    (!Qed.Auth.isSafeReturnTo a.mePath, s!"unsafe auth mePath `{a.mePath}`"),
    (a.clientIdEnv?.any (!isValidEnvKey ·), "invalid auth clientIdEnv"),
    (a.clientSecretEnv?.any (!isValidEnvKey ·), "invalid auth clientSecretEnv")]

def DeployManifest.validate (m : DeployManifest) : Except String Unit := do
  if m.version != 1 then .error s!"deploy manifest: unsupported version {m.version}"
  checkEach m.secrets isValidEnvKey (s!"invalid secret env key `{·}`")
  checkEach m.envVars (isValidEnvKey ·.2.1) (fun (_, k, _) => s!"invalid env var key `{k}`")
  checkEach m.egress isValidEgressOrigin (s!"invalid egress origin `{·}`")
  if let some a := m.auth? then validateAuthManifest a
  if let some d := m.deploy? then d.validate
  let dbVars := m.databases.map (managedPostgresSecretVar ·.shortName)
  if dbVars.eraseDups.length != dbVars.length then .error "deploy manifest: duplicate database name or managedPostgresSecretVar collision"
  let checkSecrets (pfx badPinMsg : String) (e : DeployEnv) (srs : List SecretRef) : Except String Unit := do
    checkEach srs (·.allowedIn e) (fun sr => s!"{pfx} {badPinMsg} `{sr.envVar}`{if badPinMsg == "binds pinned secret" then s!" into `{e}`" else ""}")
    checkEach srs (isValidEnvKey ·.envVar) (fun sr => s!"{pfx} {if badPinMsg == "binds pinned secret" then "has" else "contains"} invalid secret env key `{sr.envVar}`")
  for db in m.databases do
    if !isValidDbShortName db.shortName then .error s!"deploy manifest: invalid database name `{db.shortName}`"
    for e in DeployEnv.all do checkSecrets s!"database `{db.shortName}`" "binds pinned secret" e (db.envSpecs.get e).secrets
  for e in DeployEnv.all do
    let fp := m.footprintFor e
    checkSecrets s!"footprint for `{e}`" "contains disallowed pinned secret" e fp.secrets
    checkEach fp.egress isValidEgressOrigin (fun o => s!"footprint for `{e}` contains invalid egress origin `{o}`")
  checkEach m.assets (isValidAssetPath ·.path) (fun a => s!"invalid asset path `{a.path}`")

theorem validate_rejects_bad_version (m : DeployManifest) (h : m.version ≠ 1) : (m.validate).isOk = false := by
  unfold DeployManifest.validate; simp [bne_iff_ne.mpr h]; rfl

theorem validate_rejects_unsafe_auth_callback (a : DeployAuthManifest)
    (hIss : isValidEnvKey a.issuerEnv = true) (hAud : isValidEnvKey a.audienceEnv = true) (hTtl : a.sessionTtlSec ≠ 0)
    (hLogin : Qed.Auth.isSafeReturnTo a.loginPath = true) (hCb : Qed.Auth.isSafeReturnTo a.callbackPath = false) :
    (validateAuthManifest a).isOk = false := by
  unfold validateAuthManifest checkAll; simp [hIss, hAud, beq_false_of_ne hTtl, hLogin, hCb]; rfl

theorem validate_default_ok : ({} : DeployManifest).validate = .ok () := rfl

/-! ### Deterministic JSON Serialization -/

private def optJson {α : Type} (o : Option α) (f : α → Json) : Json := (o.map f).getD .null
private def jArr {α : Type} (xs : List α) (f : α → Json) : Json := .arr (xs.map f)
private def strObj (fs : List (String × String)) : Json := .obj (fs.map fun (k, v) => (k, .str v))
private def boolFs (fs : List (String × Bool)) : List (String × Json) := fs.map fun (k, v) => (k, .bool v)

private def footprintToJson (fp : EnvFootprint) : Json := .obj [
  ("secrets", toJson (fp.secrets.map (·.envVar))), ("egress", toJson fp.egress),
  ("managedDbs", jArr fp.managedDbs fun (nm, cl) => strObj [("name", nm), ("cluster", match cl with | .prodCluster => "prod" | .nonProdCluster => "nonProd")]),
  ("ephemeralDbs", toJson fp.ephemeralDbs),
  ("authTarget", optJson fp.authTarget? fun | .localDev => .str "localDev" | .previewIdp => .str "previewIdp" | .managedOidc _ => .str "managedOidc" | .customOidc => .str "customOidc")]

def DeployManifest.toJson (m : DeployManifest) : Json :=
  let tj {α : Type} [ToJson α] (x : α) : Json := ToJson.toJson x
  .obj [
    ("version", tj m.version), ("rootModule", .str m.rootModule), ("mode", .str m.mode), ("secrets", tj m.secrets),
    ("envVars", jArr m.envVars fun (nm, osKey, def?) => .obj [("name", .str nm), ("osKey", .str osKey), ("default", tj def?)]),
    ("egress", tj m.egress),
    ("databases", jArr m.databases fun db => .obj <| [("name", .str db.shortName)] ++ boolFs [("isManaged", db.isManaged), ("hasDevFallback", db.hasDevFallback)] ++
      [("secrets", tj db.secrets), ("tables", jArr db.tables fun t => .obj <| [("name", .str t.tableName)] ++
        boolFs [("hasReadPolicy", t.hasReadPolicy), ("hasInsertPolicy", t.hasInsertPolicy), ("hasUpdatePolicy", t.hasUpdatePolicy), ("hasDeletePolicy", t.hasDeletePolicy), ("hasTransInv", t.hasTransInv)] ++
        [("columns", jArr t.columns fun c => .obj <| [("name", .str c.name)] ++ boolFs [("primaryKey", c.isPrimaryKey), ("immutable", c.isImmutable), ("unique", c.isUnique), ("nullable", c.isNullable)] ++
          [("references", tj (c.refs?.map fun (rt, rc) => s!"{rt}({rc})"))])])]),
    ("auth", optJson m.auth? fun a => .obj [
      ("name", .str a.name), ("isManaged", .bool a.isManaged), ("issuerEnv", .str a.issuerEnv), ("issuerDefault", tj a.issuerDefault?),
      ("audienceEnv", .str a.audienceEnv), ("audienceDefault", tj a.audienceDefault?), ("clientIdEnv", tj a.clientIdEnv?),
      ("clientIdDefault", tj a.clientIdDefault?), ("clientSecretEnv", tj a.clientSecretEnv?), ("providers", tj a.providers),
      ("sessionTtlSec", tj a.sessionTtlSec), ("loginPath", .str a.loginPath), ("callbackPath", .str a.callbackPath),
      ("logoutPath", .str a.logoutPath), ("mePath", .str a.mePath),
      ("claims", jArr a.claims fun c => strObj [("name", c.name), ("type", c.typeName), ("default", c.defaultValue)])]),
    ("server", optJson m.server? fun s => .obj <| [("name", .str s.name), ("shortName", .str s.shortName)] ++
      boolFs [("hasState", s.hasState), ("hasHttpRoutes", s.hasHttpRoutes)] ++
      [("methods", jArr s.methods fun mt => .obj <| [("name", .str mt.name)] ++ boolFs [("readOnly", mt.isReadOnly), ("requiresAuth", mt.requiresAuth)]),
       ("channels", tj s.channels), ("jobs", tj s.jobs)]),
    ("deploy", optJson m.deploy? fun d => .obj [
      ("name", .str d.name), ("appName", .str d.appName), ("regions", tj (d.regions.map GcpRegion.toString)),
      ("domain", tj d.domain?), ("compute", .str d.compute.toString), ("timeoutSec", tj d.timeoutSec?),
      ("preview", .obj [("enabled", .bool d.preview.enabled), ("subdomain", tj d.preview.subdomain?),
        ("host", tj (d.preview.resolvedHost? d.domain? |>.map (·.render))),
        ("protection", .str (match d.preview.protection with | .team_only => "team_only" | .pub => "public")), ("ttlSec", tj d.preview.ttlSec)])]),
    ("assets", jArr m.assets fun a => .obj [("path", .str a.path), ("mime", .str a.mime), ("bytes", tj a.bytes)]),
    ("envs", .obj <| DeployEnv.all.map fun e => (e.toString, footprintToJson (m.footprintFor e))),
    ("csp", .str m.csp)]

def DeployManifest.render (m : DeployManifest) : String := Json.render m.toJson

end Qed.Deploy
