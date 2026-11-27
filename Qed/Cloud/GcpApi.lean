import Qed.Cloud.Compile
import Qed.Json.Basic

/-! ## Pure Verified GCP REST Wire Codecs & Live Drift Verifier (`Qed.Cloud.GcpApi`) -/

namespace Qed.Cloud
open Qed

/-! ### 1. Configurable GCP Endpoints, HTTP Request & JSON Helpers -/

structure GcpEndpoints where baseOverride? : Option String := none
deriving Inhabited
def GcpEndpoints.allLocal (u : String) : GcpEndpoints := { baseOverride? := some (trimTrailingSlash u) }
def GcpEndpoints.url (ep : GcpEndpoints) (svc path : String) : String := s!"{ep.baseOverride?.getD s!"https://{svc}.googleapis.com"}{path}"

structure GcpHttpRequest where
  (method url : String) (headers : List (String × String) := []) (body : String := "") (contentType : String := "application/json")
deriving Inhabited, BEq
private def GcpEndpoints.req (ep : GcpEndpoints) (method svc path : String) (body? : Option Json := none) : GcpHttpRequest :=
  { method, url := ep.url svc path, body := (body?.map Json.render).getD "" }

private def jPathArr (j : Json) (p : String) : List Json := ((j.atPath p).bind (·.arr?)).getD []
private def jStrArr (j : Json) (k : String) : List String := (j.arrAt k).filterMap (·.str?)
private def optStrField (k s : String) : List (String × Json) := if s.isEmpty then [] else [(k, .str s)]
private def optJsonField (k : String) (v? : Option Json) : List (String × Json) := (v?.map fun v => [(k, v)]).getD []
private def isNullOrNone : Option Json → Bool | none | some .null => true | some _ => false
def nonEmptyStr? (s? : Option String) : Option String := s?.bind fun s => if s.isEmpty then none else some s
private def mkKindObj (kind : String) (fs : List (String × Json) := []) : Json := .obj (("kind", .str kind) :: fs)

/-! ### 2. Validated GCP Project IDs, Resource Paths, Principals & Roles -/

private def isTokenChar (c : Char) : Bool := isAsciiAlnum c || c == '_' || c == '-'
def isValidGcpProjectId (s : String) : Bool := checkAsciiIdent 5 30 isDnsAlpha isDnsLabelChar (· != '-') s
def isValidGcpProjectIdOrNumber (s : String) : Bool := isValidGcpProjectId s || (!s.isEmpty && s.length ≤ 20 && s.toList.all fun c => '0' ≤ c && c ≤ '9')
private def isCanonicalBoundedNat (s : String) (bound : Nat) : Bool := match decNat s with | some n => n < bound && encNat n == s | none => false

def isCanonicalSaId (saId : String) : Bool := match saId.splitOn "-" with
  | ["q", tStr, aStr, envTag] => isCanonicalBoundedNat tStr 1000000 && isCanonicalBoundedNat aStr 100000 &&
      (envTag == "p" || envTag == "s" || (envTag.startsWith "r" && isCanonicalBoundedNat (envTag.drop 1).toString 100000))
  | _ => false
def isQedRuntimeSaEmailInProject (projId email : String) : Bool :=
  let suf := s!"@{projId}.iam.gserviceaccount.com"
  email.endsWith suf && email.length > suf.length && let saId := (email.dropEnd suf.length).toString; !saId.contains "@" && isCanonicalSaId saId
def isQedRuntimeSaMember (projId member : String) : Bool := member.startsWith "serviceAccount:" && isQedRuntimeSaEmailInProject projId (member.drop 15).toString

def trimLeadingSlash (s : String) : String := if s.startsWith "/" then (s.drop 1).toString else s
abbrev isSafeRelativeAssetPath : String → Bool := Qed.Deploy.isValidAssetPath
def sanitizeToken (s : String) (maxLen : Nat := 24) : String :=
  let cs := s.toLower.toList.map fun c => if isDnsAlnum c || c == '-' then c else '-'
  match ((cs.dropWhile (· == '-') |>.take maxLen).reverse.dropWhile (· == '-')).reverse with | [] => "0" | xs => String.ofList xs

private def mkBounded (bound n : Nat) (lbl : String) : Except String (BoundedId bound) :=
  if h : n < bound then .ok ⟨n, h⟩ else .error s!"{lbl} {n} out of bounds (< {bound})"

private def checkGcpProj (lbl pid : String) : Except String Unit :=
  if isValidGcpProjectId pid then .ok () else .error s!"invalid GCP {lbl} project id `{pid}` (expected 5-30 chars `[a-z][a-z0-9-]*[a-z0-9]`)"

def DeployKey.mkChecked (prodProjectId nonProdProjectId : String) (tNum aNum : Nat) (envKind : String) (prNum? : Option Nat := none) : Except String DeployKey := do
  checkGcpProj "prod" prodProjectId; checkGcpProj "non-prod" nonProdProjectId
  let shard ← ShardProject.mkPair prodProjectId nonProdProjectId
  let tenant ← mkBounded 1000000 tNum "tenant id"; let app ← mkBounded 100000 aNum "app id"
  let env ← match envKind with
    | "prod" => .ok EnvInstance.prod | "staging" => .ok EnvInstance.staging
    | "preview" => match prNum? with | some prNum => EnvInstance.preview <$> mkBounded 100000 prNum "PR number" | none => .error "preview environment requires a PR number"
    | other => .error s!"unknown env `{other}` (expected prod, staging, or preview)"
  return { shard, tenant, app, env }

def DeployKey.mkCheckedStr (prodProjectId nonProdProjectId tenantStr appStr envKind prStr : String) : Except String DeployKey := do
  let some tNum := tenantStr.toNat? | .error s!"invalid tenant id `{tenantStr}`"
  let some aNum := appStr.toNat? | .error s!"invalid app id `{appStr}`"
  DeployKey.mkChecked prodProjectId nonProdProjectId tNum aNum envKind (if envKind == "preview" then prStr.toNat? else none)

def secretId (k : DeployKey) (secretName : String) : String := s!"{renderKeySlug k}-{secretName}"
def secretResourcePath (k : DeployKey) (secretName : String) : String := s!"projects/{Qed.encodeSeg (k.shard.projectFor k.env)}/secrets/{Qed.encodeSeg (secretId k secretName)}"
def cloudRunServicePath (k : DeployKey) (r : GcpRegion) : String := s!"projects/{Qed.encodeSeg (k.shard.projectFor k.env)}/locations/{r}/services/{renderCloudRunName k}"
def cloudRunRevisionName (k : DeployKey) (buildHash : String) : String := s!"{renderCloudRunName k}-{sanitizeToken buildHash 16}"
def assetBucketName (k : DeployKey) (isPublic : Bool := true) : String := s!"{if isPublic then "qed-assets-" else "qed-assets-priv-"}{k.shard.projectFor k.env}"
def assetObjectPath (k : DeployKey) (buildHash relPath : String) : String := s!"{renderKeySlug k}/{sanitizeToken buildHash 16}/{trimLeadingSlash relPath}"
def sqlInstanceName (cl : DbCluster) (k : DeployKey) : String := s!"qed-{match cl with | .prodCluster => "prod" | .nonProdCluster => "nonprod"}-{k.shard.clusterProject cl}"
def sqlDbName (k : DeployKey) (dbName : String) : String := s!"{renderKeySlug k}_{dbName}"
def egressPolicyPath (k : DeployKey) (r : GcpRegion) : String := s!"projects/{Qed.encodeSeg (k.shard.projectFor k.env)}/locations/{r}/gatewaySecurityPolicies/egress-{renderKeySlug k}"
def sqlIamUserName (k : DeployKey) : String := let email := renderSaEmail k; let suf := ".gserviceaccount.com"; if email.endsWith suf then (email.dropEnd suf.length).toString else email
def GcpPlan.assetsArePublic (plan : GcpPlan) : Bool := (plan.bindings.findSome? fun b => match b.resource with | .assetPrefix _ _ isPub => some isPub | _ => none).getD true

def GcpPrincipal.gcpMember (edgeSaEmail builderSaEmail : String) : GcpPrincipal → String
  | .allUsers => "allUsers" | .allAuthenticatedUsers => "allAuthenticatedUsers" | .builder => s!"serviceAccount:{builderSaEmail}"
  | .edgeRouter => s!"serviceAccount:{edgeSaEmail}" | .runtimeSa k => s!"serviceAccount:{renderSaEmail k}" | .external e => if e.contains ":" then e else s!"serviceAccount:{e}"
def parseGcpMember (edgeSaEmail builderSaEmail : String) (key : DeployKey) (member : String) : GcpPrincipal :=
  match [("allUsers", .allUsers), ("allAuthenticatedUsers", .allAuthenticatedUsers), (s!"serviceAccount:{renderSaEmail key}", .runtimeSa key),
      (s!"serviceAccount:{edgeSaEmail}", .edgeRouter), (s!"serviceAccount:{builderSaEmail}", .builder)].find? (·.1 == member) with
  | some (_, p) => p | none => .external member

def GcpRole.all : List GcpRole := [.secretManagerAccessor, .runInvoker, .cloudSqlClient, .storageLegacyObjectReader, .storageObjectAdmin]
def GcpRole.parse? (s : String) : Option GcpRole := GcpRole.all.find? (·.gcpName == s)
private def permV2Table : List (GcpPermission × String) := [
  (.secretAccessor, "secretmanager.googleapis.com/versions.access"), (.runInvoke, "run.googleapis.com/routes.invoke"),
  (.cloudSqlClient, "cloudsql.googleapis.com/instances.connect"), (.storageObjectViewer, "storage.googleapis.com/objects.get"),
  (.storageObjectAdmin, "storage.googleapis.com/objects.create"), (.iamSetPolicy, "iam.googleapis.com/serviceAccounts.setIamPolicy"),
  (.iamActAs, "iam.googleapis.com/serviceAccounts.actAs"), (.iamGetAccessToken, "iam.googleapis.com/serviceAccounts.getAccessToken"),
  (.iamSignJwt, "iam.googleapis.com/serviceAccounts.signJwt")]
def GcpPermission.all : List GcpPermission := permV2Table.map Prod.fst
def GcpPermission.gcpV2Name (p : GcpPermission) : String := (permV2Table.find? (·.1 == p)).map Prod.snd |>.getD ""
def GcpResource.denyPolicyId : GcpResource → String
  | .cloudRun _ => "deny-qed-run-public" | .secret _ _ => "deny-qed-secrets-public" | .cloudSqlDb _ _ _ => "deny-qed-sql-public"
  | .assetPrefix _ _ _ => "deny-qed-gcs-public" | .project _ => "deny-qed-project-public"
def isImmutableAssetPath (relPath : String) : Bool :=
  let clean := trimLeadingSlash relPath; let base := if clean.endsWith ".map" then (clean.dropEnd 4).toString else clean
  let leaf := (Qed.Str.splitChar base '/').reverse.headD base
  match (Qed.Str.splitChar leaf '.').reverse with
  | ext :: hash :: stem :: _ => !stem.isEmpty && ["mjs", "js", "css"].contains ext.toLower && 8 ≤ hash.length && hash.length ≤ 16 && hash.toList.all fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')
  | _ => false
def assetMimeType (relPath : String) : String :=
  match (relPath.splitOn ".").reverse with
  | ext :: _ :: _ => match ext.toLower with
      | "mjs" | "js" => "text/javascript; charset=utf-8" | "css" => "text/css; charset=utf-8" | "html" => "text/html; charset=utf-8"
      | "json" | "map" => "application/json; charset=utf-8" | "webmanifest" => "application/manifest+json; charset=utf-8"
      | "xml" => "application/xml; charset=utf-8" | "txt" => "text/plain; charset=utf-8" | "pdf" => "application/pdf"
      | "svg" => "image/svg+xml" | "png" => "image/png" | "jpg" | "jpeg" => "image/jpeg" | "gif" => "image/gif"
      | "webp" => "image/webp" | "avif" => "image/avif" | "ico" => "image/x-icon" | "wasm" => "application/wasm"
      | "woff2" => "font/woff2" | "woff" => "font/woff" | "ttf" => "font/ttf" | "otf" => "font/otf"
      | "mp4" => "video/mp4" | "webm" => "video/webm" | "mp3" => "audio/mpeg" | "ogg" => "audio/ogg" | _ => "application/octet-stream"
  | _ => "application/octet-stream"

/-! ### 3. Pure ETag-, Condition-, & AuditConfig-Safe IAM Policy Model -/

private def optJsonEq (a b : Option Json) : Bool := a.map Json.render == b.map Json.render
structure IamPolicyEntry where (role : String) (members : List String) (condition? : Option Json := none)
deriving Inhabited
instance : BEq IamPolicyEntry := ⟨fun a b => a.role == b.role && a.members == b.members && optJsonEq a.condition? b.condition?⟩

structure IamPolicyDoc where (version : Nat := 3) (etag : String := "") (bindings : List IamPolicyEntry := []) (auditConfigs? : Option Json := none)
deriving Inhabited
instance : BEq IamPolicyDoc := ⟨fun a b => a.version == b.version && a.etag == b.etag && a.bindings == b.bindings && optJsonEq a.auditConfigs? b.auditConfigs?⟩

@[noinline, nospecialize] private def fld {α : Type} [FromJsonField α] (j : Json) (k : String) : Except String α := fromField j k

private instance : ToJson IamPolicyEntry := ⟨fun e => .obj <| [("role", .str e.role), ("members", toJson e.members)] ++ optJsonField "condition" e.condition?⟩
private instance : FromJson IamPolicyEntry := ⟨fun j => do return { role := ← fld j "role", members := ← fld j "members", condition? := ← fld j "condition" }⟩

def IamPolicyDoc.toJson (p : IamPolicyDoc) : Json :=
  .obj <| [("version", ToJson.toJson p.version)] ++ optStrField "etag" p.etag ++ [("bindings", ToJson.toJson p.bindings)] ++ optJsonField "auditConfigs" p.auditConfigs?
def IamPolicyDoc.fromJson (j : Json) : Except String IamPolicyDoc := do
  return { version := (j.natAt? "version").getD 3, etag := j.strAtD "etag",
           bindings := (← fld (α := Option (List IamPolicyEntry)) j "bindings").getD [], auditConfigs? := ← fld j "auditConfigs" }

def IamPolicyDoc.addBinding (p : IamPolicyDoc) (role member : String) : IamPolicyDoc :=
  if p.bindings.any fun e => e.role == role && e.condition?.isNone then
    { p with bindings := p.bindings.map fun e => if e.role == role && e.condition?.isNone && !e.members.contains member then { e with members := e.members ++ [member] } else e }
  else { p with bindings := p.bindings ++ [{ role, members := [member] }] }
def IamPolicyDoc.removeBinding (p : IamPolicyDoc) (role member : String) (includeConditional : Bool := false) : IamPolicyDoc :=
  { p with bindings := p.bindings.filterMap fun e =>
      if e.role == role && (includeConditional || e.condition?.isNone) then let ms := e.members.filter (· != member); if ms.isEmpty then none else some { e with members := ms } else some e }
theorem IamPolicyDoc.addBinding_preserves_etag (p : IamPolicyDoc) (role member : String) : (p.addBinding role member).etag = p.etag := by
  unfold IamPolicyDoc.addBinding; split <;> rfl
theorem IamPolicyDoc.removeBinding_preserves_etag (p : IamPolicyDoc) (role member : String) (includeConditional : Bool := false) :
    (p.removeBinding role member includeConditional).etag = p.etag := rfl

def IamPolicyDoc.partitionBindings (p : IamPolicyDoc) (edgeSaEmail builderSaEmail : String) (key : DeployKey) (res : GcpResource) :
    List GcpIamBinding × List (String × String × GcpResource) :=
  p.bindings.foldl (init := ([], [])) fun (known, raw) e =>
    if e.condition?.isSome then (known, raw ++ e.members.map (·, s!"{e.role}[conditional]", res))
    else match GcpRole.parse? e.role with
      | some role => (known ++ e.members.map fun m => { principal := parseGcpMember edgeSaEmail builderSaEmail key m, role, resource := res }, raw)
      | none      => (known, raw ++ e.members.map (·, e.role, res))

/-! ### 4. Pure GCP REST Request Builders, Byte-Collision & URI/LRO Validators -/

private def bytesMatchAt (hay needle : ByteArray) (off : Nat) : Nat → Bool
  | 0 => true | k + 1 => hay.get! (off + k) == needle.get! k && bytesMatchAt hay needle off k
def byteArrayContains (hay needle : ByteArray) : Bool :=
  if needle.isEmpty then true else if hay.size < needle.size then false
  else let rec go (i : Nat) : Nat → Bool | 0 => false | fuel + 1 => bytesMatchAt hay needle i needle.size || go (i + 1) fuel
    go 0 (hay.size - needle.size + 1)

private def projV1Req (ep : GcpEndpoints) (m svc : String) (k : DeployKey) (tail : String) (body? : Option Json := none) : GcpHttpRequest :=
  ep.req m svc s!"/v1/projects/{Qed.encodeSeg (k.shard.projectFor k.env)}/{tail}" body?
def reqCreateServiceAccount (ep : GcpEndpoints) (key : DeployKey) : GcpHttpRequest :=
  projV1Req ep "POST" "iam" key "serviceAccounts" (some <| .obj [("accountId", .str (renderSaId key)), ("serviceAccount", .obj [("displayName", .str s!"Qed runtime SA ({renderKeySlug key})")])])
def reqDeleteServiceAccount (ep : GcpEndpoints) (key : DeployKey) : GcpHttpRequest := projV1Req ep "DELETE" "iam" key s!"serviceAccounts/{Qed.encodeSeg (renderSaEmail key)}"
def reqEnsureSecret (ep : GcpEndpoints) (key : DeployKey) (secretName : String) : GcpHttpRequest :=
  projV1Req ep "POST" "secretmanager" key s!"secrets?secretId={Qed.encodeSeg (secretId key secretName)}" (some <| .obj [("replication", .obj [("automatic", .obj [])])])
def reqDeleteSecret (ep : GcpEndpoints) (key : DeployKey) (secretName : String) : GcpHttpRequest := ep.req "DELETE" "secretmanager" s!"/v1/{secretResourcePath key secretName}"
def reqListSecrets (ep : GcpEndpoints) (key : DeployKey) (pageToken? : Option String := none) : GcpHttpRequest :=
  let pt := (nonEmptyStr? pageToken?).elim "" fun t => s!"&pageToken={Qed.encodeSeg t}"
  projV1Req ep "GET" "secretmanager" key s!"secrets?filter={Qed.encodeSeg s!"name:{renderKeySlug key}-"}&pageSize=100{pt}"
def parseNextPageToken? (j : Json) : Option String := nonEmptyStr? (j.strAt? "nextPageToken")

private def parsePrefixedNames (j : Json) (arrField pfx : String) (takeLeaf : Bool) : List String :=
  (j.arrAt arrField).filterMap fun item => (item.strAt? "name").bind fun s =>
    let nm := if takeLeaf then (s.splitOn "/").getLastD s else s
    if nm.startsWith pfx then some (nm.drop pfx.length).toString else none
def parseListedSecrets (key : DeployKey) (j : Json) : List String := parsePrefixedNames j "secrets" s!"{renderKeySlug key}-" true
def parseListedDbs (key : DeployKey) (j : Json) : List String := parsePrefixedNames j "items" s!"{renderKeySlug key}_" false

def reqUploadAsset (ep : GcpEndpoints) (key : DeployKey) (buildHash relPath : String) (fileBytes : ByteArray) (boundary : String) (isPublic : Bool := true) :
    Except String (GcpHttpRequest × ByteArray) := do
  if boundary.isEmpty || boundary.length > 70 || !boundary.toList.all isTokenChar then .error "reqUploadAsset: invalid multipart boundary"
  let (mime, vis) := (assetMimeType relPath, if isPublic then "public" else "private")
  let cc := if isImmutableAssetPath relPath then s!"{vis}, max-age=31536000, immutable" else s!"{vis}, max-age=0, must-revalidate"
  let metaJson := Json.render <| .obj [("name", .str (assetObjectPath key buildHash relPath)), ("cacheControl", .str cc), ("contentType", .str mime)]
  let bBytes := boundary.toUTF8
  if byteArrayContains metaJson.toUTF8 bBytes || byteArrayContains fileBytes bBytes then .error "reqUploadAsset: multipart boundary collides with payload bytes"
  let head := s!"--{boundary}\r\nContent-Type: application/json; charset=UTF-8\r\n\r\n{metaJson}\r\n--{boundary}\r\nContent-Type: {mime}\r\n\r\n"
  return ({
    method := "POST", headers := [("Cache-Control", cc)], contentType := s!"multipart/related; boundary={boundary}",
    url := ep.url "storage" s!"/upload/storage/v1/b/{Qed.encodeSeg (assetBucketName key isPublic)}/o?uploadType=multipart" },
    head.toUTF8 ++ fileBytes ++ s!"\r\n--{boundary}--\r\n".toUTF8)

private def sqlInstReq (ep : GcpEndpoints) (m : String) (cl : DbCluster) (k : DeployKey) (suf : String) (body? : Option Json := none) : GcpHttpRequest :=
  ep.req m "sqladmin" s!"/v1/projects/{Qed.encodeSeg (k.shard.clusterProject cl)}/instances/{Qed.encodeSeg (sqlInstanceName cl k)}/{suf}" body?
private def sqlObj (cl : DbCluster) (k : DeployKey) (extra : List (String × Json)) : Option Json :=
  some <| .obj (extra ++ [("project", .str (k.shard.clusterProject cl)), ("instance", .str (sqlInstanceName cl k))])
def reqEnsureDb (ep : GcpEndpoints) (cl : DbCluster) (key : DeployKey) (dbName : String) : GcpHttpRequest := sqlInstReq ep "POST" cl key "databases" (sqlObj cl key [("name", .str (sqlDbName key dbName))])
def reqEnsureSqlIamUser (ep : GcpEndpoints) (cl : DbCluster) (key : DeployKey) : GcpHttpRequest := sqlInstReq ep "POST" cl key "users" (sqlObj cl key [("name", .str (sqlIamUserName key)), ("type", .str "CLOUD_IAM_SERVICE_ACCOUNT")])
def reqDeleteSqlIamUser (ep : GcpEndpoints) (cl : DbCluster) (key : DeployKey) : GcpHttpRequest := sqlInstReq ep "DELETE" cl key s!"users?name={Qed.encodeSeg (sqlIamUserName key)}"
def reqListDbs (ep : GcpEndpoints) (cl : DbCluster) (key : DeployKey) : GcpHttpRequest := sqlInstReq ep "GET" cl key "databases"
def reqDropPreviewDb (ep : GcpEndpoints) (key : DeployKey) (dbName : String) : GcpHttpRequest := sqlInstReq ep "DELETE" .nonProdCluster key s!"databases/{Qed.encodeSeg (sqlDbName key dbName)}"
def reqGetSqlOp (ep : GcpEndpoints) (projId opId : String) : GcpHttpRequest := ep.req "GET" "sqladmin" s!"/v1/projects/{Qed.encodeSeg projId}/operations/{Qed.encodeSeg opId}"
def isSqlOperationInProgress (bodyTxt : String) : Bool := bodyTxt.contains "operationInProgress" || bodyTxt.contains "already in progress"

def iamPolicyUrls (ep : GcpEndpoints) (region : GcpRegion) (res : GcpResource) : String × String × String × Bool :=
  let v3 (p : String) := (s!"{p}:getIamPolicy?options.requestedPolicyVersion=3", s!"{p}:setIamPolicy", "POST", true)
  let crm (pid : String) := let p := ep.url "cloudresourcemanager" s!"/v3/projects/{Qed.encodeSeg pid}"; (s!"{p}:getIamPolicy", s!"{p}:setIamPolicy", "POST", true)
  match res with
  | .cloudRun k => v3 (ep.url "run" s!"/v2/{cloudRunServicePath k region}")
  | .secret k s => v3 (ep.url "secretmanager" s!"/v1/{secretResourcePath k s}")
  | .assetPrefix k _ pub => let p := ep.url "storage" s!"/storage/v1/b/{Qed.encodeSeg (assetBucketName k pub)}/iam"; (s!"{p}?optionsRequestedPolicyVersion=3", p, "PUT", false)
  | .cloudSqlDb cl k _ => crm (k.shard.clusterProject cl)
  | .project projId => crm projId

def reqGetIamPolicy (ep : GcpEndpoints) (region : GcpRegion) (res : GcpResource) : GcpHttpRequest :=
  let isPost := match res with | .cloudSqlDb _ _ _ | .project _ => true | _ => false
  { method := if isPost then "POST" else "GET", url := (iamPolicyUrls ep region res).1, body := if isPost then "{\"options\":{\"requestedPolicyVersion\":3}}" else "" }
def reqSetIamPolicy (ep : GcpEndpoints) (region : GcpRegion) (res : GcpResource) (doc : IamPolicyDoc) : GcpHttpRequest :=
  let (_, setUrl, setMethod, wrap) := iamPolicyUrls ep region res
  { method := setMethod, url := setUrl, body := Json.render (if wrap then Json.obj [("policy", doc.toJson)] else doc.toJson) }

private def saV2Pfx : String := "principal://iam.googleapis.com/projects/-/serviceAccounts/"
private def saV2Principal (email : String) : String := saV2Pfx ++ email
private def denyPolicyParentForProj (projId : String) : String := Qed.encodeSeg s!"cloudresourcemanager.googleapis.com/projects/{projId}"
private def fixedDenyPrins (edgeSa builderSa : String) (deployerSa? : Option String) : List String :=
  [saV2Principal edgeSa, saV2Principal builderSa] ++ (nonEmptyStr? deployerSa?).elim [] fun d => [saV2Principal d]

def reqGetDenyPolicyById (ep : GcpEndpoints) (projId denyId : String) : GcpHttpRequest := ep.req "GET" "iam" s!"/v2/policies/{denyPolicyParentForProj projId}/denypolicies/{denyId}"
def reqGetDenyRule (ep : GcpEndpoints) (rule : GcpDenyRule) : GcpHttpRequest := reqGetDenyPolicyById ep rule.resource.projectOf rule.resource.denyPolicyId
def parseDenyExceptionPrincipals (j : Json) : List String := (jPathArr j "rules.0.denyRule.exceptionPrincipals").filterMap (·.str?)

def isAllowedDenyExceptionPrincipal (projId edgeSaEmail builderSaEmail : String) (deployerSaEmail? : Option String) (allowRuntimeSas : Bool) (prin : String) : Bool :=
  (fixedDenyPrins edgeSaEmail builderSaEmail deployerSaEmail?).contains prin ||
  (allowRuntimeSas && prin.startsWith saV2Pfx && isQedRuntimeSaEmailInProject projId (prin.drop saV2Pfx.length).toString)

def isValidDenyPolicyDoc (projId edgeSaEmail builderSaEmail : String) (deployerSaEmail? : Option String) (allowRuntimeSas : Bool) (reqPerms : List GcpPermission) (j : Json) : Bool :=
  isNullOrNone (j.atPath "rules.0.denialCondition") && (j.atPath "rules.0.denyRule").any fun rJ =>
    (match rJ.get? "exceptionPermissions" with | none | some .null | some (.arr []) => true | _ => false) &&
    (match rJ.get? "exceptionPrincipals" with | none | some .null => true | some (.arr xs) => xs.all (·.str?.isSome) | _ => false) &&
    isNullOrNone (rJ.get? "denialCondition") && (jStrArr rJ "deniedPrincipals").contains "principalSet://goog/public:all" &&
    reqPerms.all (fun p => (jStrArr rJ "deniedPermissions").contains p.gcpV2Name) &&
    (jStrArr rJ "exceptionPrincipals").all (isAllowedDenyExceptionPrincipal projId edgeSaEmail builderSaEmail deployerSaEmail? allowRuntimeSas)

private def mkDenyPolicyReq (ep : GcpEndpoints) (projId denyId : String) (etag? : Option String) (exceptions : List String) (perms : List GcpPermission) : GcpHttpRequest :=
  let (parent, body) := (denyPolicyParentForProj projId, Json.obj <| [("displayName", .str s!"Qed Cloud deny ({denyId})")] ++ etag?.elim [] (optStrField "etag") ++ [
    ("rules", .arr [Json.obj [("denyRule", Json.obj [("deniedPrincipals", toJson (["principalSet://goog/public:all"] : List String)),
      ("exceptionPrincipals", toJson exceptions), ("deniedPermissions", toJson (perms.map GcpPermission.gcpV2Name))])]])])
  match etag? with
  | none   => ep.req "POST" "iam" s!"/v2/policies/{parent}/denypolicies?policyId={denyId}" (some body)
  | some _ => ep.req "PUT"  "iam" s!"/v2/policies/{parent}/denypolicies/{denyId}" (some body)

def reqUpsertDenyRule (ep : GcpEndpoints) (edgeSaEmail builderSaEmail : String) (rule : GcpDenyRule) (existingEtag? : Option String := none)
    (existingExceptions : List String := []) (deployerSaEmail? : Option String := none) : GcpHttpRequest :=
  let (projId, allowRt) := (rule.resource.projectOf, match rule.resource with | .cloudRun _ => false | _ => true)
  let needed := fixedDenyPrins edgeSaEmail builderSaEmail deployerSaEmail? ++ (if allowRt then [saV2Principal (renderSaEmail rule.resource.ownerKey)] else [])
  mkDenyPolicyReq ep projId rule.resource.denyPolicyId existingEtag?
    ((existingExceptions.filter (isAllowedDenyExceptionPrincipal projId edgeSaEmail builderSaEmail deployerSaEmail? allowRt)) ++ needed).eraseDups rule.permissions

def reqPruneDenyException (ep : GcpEndpoints) (edgeSaEmail builderSaEmail : String) (key : DeployKey) (existingEtag : String)
    (existingExceptions : List String) (deployerSaEmail? : Option String := none) : Option GcpHttpRequest :=
  let (projId, saPrin) := (key.shard.projectFor key.env, saV2Principal (renderSaEmail key))
  let nextExcs := existingExceptions.filter fun p => p != saPrin && isAllowedDenyExceptionPrincipal projId edgeSaEmail builderSaEmail deployerSaEmail? true p
  if nextExcs == existingExceptions then none else some (mkDenyPolicyReq ep projId "deny-qed-secrets-public" (some existingEtag) nextExcs [.secretAccessor])

abbrev egressOriginHost : String → String := extractUrlHost
def reqPutEgressPolicy (ep : GcpEndpoints) (region : GcpRegion) (key : DeployKey) (origins : List String) : GcpHttpRequest :=
  let cleanOrigins := origins.filter Qed.Deploy.isValidEgressOrigin
  let rules := cleanOrigins.zipIdx.map fun (orig, idx) => Json.obj [("name", .str s!"allow-{idx}"), ("priority", toJson (idx + 1)),
    ("basicProfile", .str "ALLOW"), ("enabled", .bool true), ("sessionMatcher", .str s!"host() == '{(egressOriginHost orig).replace "'" ""}'"), ("description", .str orig)]
  ep.req "PUT" "networksecurity" s!"/v1/{egressPolicyPath key region}" (some <| Json.obj [("name", .str (egressPolicyPath key region)),
    ("description", .str s!"Qed Cloud default-deny egress allowlist ({renderKeySlug key})"), ("allowedOrigins", toJson cleanOrigins), ("rules", .arr rules)])
def reqGetEgressPolicy (ep : GcpEndpoints) (region : GcpRegion) (key : DeployKey) : GcpHttpRequest := ep.req "GET" "networksecurity" s!"/v1/{egressPolicyPath key region}"
def reqDeleteEgressPolicy (ep : GcpEndpoints) (region : GcpRegion) (key : DeployKey) : GcpHttpRequest := ep.req "DELETE" "networksecurity" s!"/v1/{egressPolicyPath key region}"

private def parseCelHostMatcher? (expr : String) : Option String :=
  let pfx := "host() == '"
  if expr.startsWith pfx && expr.endsWith "'" && expr.length > pfx.length + 1 then
    let host := ((expr.drop pfx.length).dropEnd 1).toString; if !Env.hasCtrlOrWs host "'\"" && isValidHostname host then some host else none
  else none

def parseEgressPolicy (j : Json) : List String :=
  let metaOrigins := jStrArr j "allowedOrigins"
  match j.get? "rules" with
  | some (.arr rs) => rs.filterMap fun r =>
      let prof := r.strAtD "basicProfile" "ALLOW"
      if !(r.boolAt? "enabled").getD true || prof == "DENY" then none
      else if prof != "ALLOW" then some s!"<unsafe-cel-rule:{Json.render r}>"
      else match (r.strAt? "sessionMatcher").bind parseCelHostMatcher? with
        | some host => some <| (metaOrigins.find? (egressOriginHost · == host)).getD <|
            (r.strAt? "description").bind (fun d => if d.startsWith "https://" && egressOriginHost d == host then some d else none) |>.getD s!"https://{host}"
        | none => some s!"<unsafe-cel-rule:{r.strAtD "sessionMatcher" (Json.render r)}>"
  | _ => metaOrigins

def formatCpuLimit (cpuMilli : Nat) : String := if cpuMilli % 1000 == 0 then toString (cpuMilli / 1000) else s!"{cpuMilli}m"
def parseAllTrafficTargets (j : Json) : List Json := j.arrAt "traffic"
private def revisionLeaf (r : String) : String := (r.splitOn "/").getLastD r
private def nonEmptyLeaf? (s? : Option String) : Option String := (nonEmptyStr? s?).map revisionLeaf

private def resolveLatestServingRevision? (j : Json) (targetPct : Nat) : Option String :=
  let findWith (p : Json → Bool) := (j.arrAt "trafficStatuses").findSome? fun t => if p t then nonEmptyLeaf? (t.strAt? "revision") else none
  (findWith (·.strAt? "type" == some "TRAFFIC_TARGET_ALLOCATION_TYPE_LATEST")).orElse fun _ =>
    (findWith fun t => t.strAt? "tag" != some "candidate" && (t.natAt? "percent").getD 0 == targetPct).orElse fun _ => nonEmptyLeaf? (j.strAt? "latestReadyRevision")

def parseLiveTrafficTargets (j : Json) : Except String (List Json) := do
  let kept := (j.arrAt "traffic").filter fun t => t.strAt? "tag" != some "candidate" && (t.natAt? "percent").getD 0 > 0
  let total := kept.foldl (init := 0) fun acc t => acc + (t.natAt? "percent").getD 0
  if total == 0 then return []
  if total != 100 then .error s!"Cloud Run live traffic percentages sum to {total} (expected 0 or 100; refusing invalid PATCH)"
  kept.mapM fun t => do
    let pct := (t.natAt? "percent").getD 0
    if t.strAt? "type" == some "TRAFFIC_TARGET_ALLOCATION_TYPE_LATEST" || (nonEmptyStr? (t.strAt? "revision")).isNone then
      let some rev := resolveLatestServingRevision? j pct
        | .error "Cloud Run service has unpinned TRAFFIC_TARGET_ALLOCATION_TYPE_LATEST (or missing revision) and no resolvable serving revision in trafficStatuses/latestReadyRevision; refusing to deploy"
      return Json.obj <| [("type", .str "TRAFFIC_TARGET_ALLOCATION_TYPE_REVISION"), ("revision", .str rev), ("percent", toJson pct)] ++ optStrField "tag" (t.strAtD "tag")
    else return t

private def runSvcUrl (k : DeployKey) (r : GcpRegion) (q : String := "") : String := s!"/v2/{cloudRunServicePath k r}{q}"

@[noinline] def reqDeployRevisionZero (ep : GcpEndpoints) (region : GcpRegion) (key : DeployKey) (buildHash imageUri : String)
    (scale : ScaleSpec) (secretNames : List String) (existingTraffic : List Json := []) : GcpHttpRequest :=
  let rev := cloudRunRevisionName key buildHash
  let envVars := Json.obj [("name", .str "QED_DEPLOY_ENV"), ("value", .str (toString key.env.toDeployEnv))] ::
    secretNames.map fun s => .obj [("name", .str s), ("valueSource", .obj [("secretKeyRef", .obj [("secret", .str (secretId key s)), ("version", .str "latest")])])]
  let candTarget := Json.obj [("type", .str "TRAFFIC_TARGET_ALLOCATION_TYPE_REVISION"), ("revision", .str rev), ("percent", toJson (if existingTraffic.isEmpty then (100 : Nat) else 0)), ("tag", .str "candidate")]
  ep.req "PATCH" "run" (runSvcUrl key region "?allowMissing=true") (some <| .obj [
    ("ingress", .str "INGRESS_TRAFFIC_INTERNAL_LOAD_BALANCER"),
    ("template", .obj [("revision", .str rev), ("serviceAccount", .str (renderSaEmail key)),
      ("maxInstanceRequestConcurrency", toJson scale.concurrency), ("timeout", .str s!"{scale.timeoutSec}s"),
      ("scaling", .obj [("minInstanceCount", toJson scale.minInstances), ("maxInstanceCount", toJson scale.maxInstances)]),
      ("vpcAccess", .obj [("egress", .str "VPC_EGRESS_ALL_TRAFFIC"), ("networkInterfaces", .arr [.obj [("network", .str "qed-vpc"), ("subnetwork", .str s!"qed-swp-{region}")]])]),
      ("containers", .arr [.obj [("image", .str imageUri), ("resources", .obj [("limits", .obj [("cpu", .str (formatCpuLimit scale.cpuMilli)), ("memory", .str s!"{scale.memoryMb}Mi")])]), ("env", .arr envVars)]])]),
    ("traffic", .arr (existingTraffic ++ [candTarget]))])

def reqGetCloudRunService (ep : GcpEndpoints) (region : GcpRegion) (key : DeployKey) : GcpHttpRequest := ep.req "GET" "run" (runSvcUrl key region)
def reqGetCloudRunOp (ep : GcpEndpoints) (opName : String) : GcpHttpRequest := ep.req "GET" (if opName.startsWith "policies/" then "iam" else "run") s!"/v2/{trimLeadingSlash opName}"
def reqRestoreTraffic (ep : GcpEndpoints) (region : GcpRegion) (key : DeployKey) (targets : List Json) : GcpHttpRequest := ep.req "PATCH" "run" (runSvcUrl key region "?updateMask=traffic") (some <| .obj [("traffic", .arr targets)])
def reqShiftTraffic100 (ep : GcpEndpoints) (region : GcpRegion) (key : DeployKey) (buildHash : String) : GcpHttpRequest :=
  reqRestoreTraffic ep region key [.obj [("type", .str "TRAFFIC_TARGET_ALLOCATION_TYPE_REVISION"), ("revision", .str (cloudRunRevisionName key buildHash)), ("percent", toJson (100 : Nat))]]
def reqDeleteCloudRunService (ep : GcpEndpoints) (region : GcpRegion) (key : DeployKey) : GcpHttpRequest := ep.req "DELETE" "run" (runSvcUrl key region)

private def isSafeOpId (s : String) : Bool := !s.isEmpty && s != "." && s != ".." && !s.contains ".." && s.toList.all fun c => isTokenChar c || c == '.'

def isValidLroOpName (raw : String) : Bool :=
  if raw.isEmpty || raw.startsWith "/" || raw.contains ".." || Env.hasCtrlOrWs raw "?#\\" then false
  else match raw.splitOn "/" with
    | ["projects", proj, "locations", loc, "operations", opId] => !raw.contains "%" && isValidGcpProjectIdOrNumber proj && ((GcpRegion.parse? loc).isSome || loc == "global") && isSafeOpId opId
    | ["policies", parent, "denypolicies", policyId, "operations", opId] =>
        let lowPfx := "cloudresourcemanager.googleapis.com%2fprojects%2f"
        parent.toLower.startsWith lowPfx && isValidGcpProjectIdOrNumber (parent.drop lowPfx.length).toString && isSafeOpId policyId && isSafeOpId opId
    | _ => false

def parsePendingLro (j : Json) : Except String (Option String) :=
  if j.boolAt? "done" == some true then .ok none
  else let explicitFalse := j.boolAt? "done" == some false
    match j.strAt? "name" with
    | some nm => if explicitFalse || nm.contains "/operations/" then (if isValidLroOpName nm then .ok (some nm) else .error s!"unsafe/invalid GCP LRO operation name `{nm}`") else .ok none
    | none => if explicitFalse then .error "pending GCP LRO missing `name`" else .ok none

def parsePendingSqlOp (j : Json) : Except String (Option String) :=
  if j.strAt? "kind" != some "sql#operation" then .ok none
  else match j.get? "error" with
    | some .null | none => match j.strAt? "status" with
        | some "DONE" => .ok none
        | some "PENDING" | some "RUNNING" => match j.strAt? "name" with
            | some opId => if isSafeOpId opId then .ok (some opId) else .error s!"unsafe/invalid Cloud SQL operation id `{opId}`"
            | none => .error "pending Cloud SQL operation missing `name`"
        | some other => .error s!"unexpected Cloud SQL operation status `{other}`" | none => .error "Cloud SQL `sql#operation` missing `status`"
    | some errJ => .error s!"Cloud SQL operation failed: {Json.render errJ}"

def extractStrictCloudRunHost? (rawUrl : String) : Option String :=
  match parseHttpsHostPort? rawUrl (lowercaseHost := false) with
  | some (rest, none) => match (rest.splitOn ".").reverse with
      | ["app", "run", mid, svc] => if !svc.isEmpty && (mid == "a" || (GcpRegion.parse? mid).isSome) then some rest else none | _ => none
  | _ => none
def isValidCloudRunCandidatePair (candUrl baseUri : String) : Bool :=
  match extractStrictCloudRunHost? candUrl, extractStrictCloudRunHost? baseUri with | some c, some b => c == b || c == "candidate---" ++ b | _, _ => false
def isValidCloudRunCandidateForService (key : DeployKey) (region : GcpRegion) (candUrl baseUri : String) : Bool :=
  isValidCloudRunCandidatePair candUrl baseUri && (extractStrictCloudRunHost? baseUri).any fun b => b.startsWith (renderCloudRunName key ++ "-") && (b.endsWith ".a.run.app" || b.endsWith s!".{region}.run.app")

def parseCloudRunCandidateUrls (expectedRev : String) (j : Json) (strictRunApp : Bool := false) : Option (String × String) :=
  let baseUri := j.strAt? "uri"
  (j.arrAt "trafficStatuses").findSome? fun t =>
    if t.strAt? "tag" == some "candidate" && (t.strAt? "revision").any fun r => r == expectedRev || r.endsWith ("/" ++ expectedRev) then
      (t.strAt? "uri").bind fun u => let b := baseUri.getD u; if !strictRunApp || isValidCloudRunCandidatePair u b then some (u, b) else none
    else none

structure CloudRunSpecSnapshot where
  (region : GcpRegion) (existsService invokerIamDisabled : Bool := false)
  (ingress serviceAccount vpcEgress : String := "") (vpcInterfaces : List (String × String) := [])
  (containerCount : Nat := 0) (deployEnv? : Option String := none) (envNames : List String := [])
  (envBindings : List (String × Option String) := []) (secretEnvRefs unexpectedVolumes unexpectedVolumeMounts : List String := [])
  (hasCommandOverride : Bool := false) (latestReadyRevision? latestCreatedRevision? : Option String := none)
  (servingTraffic : List (String × String × Nat) := []) (taggedRoutes : List (String × String) := [])
deriving Inhabited

@[noinline] def parseCloudRunServiceSpec (region : GcpRegion) (j : Json) : CloudRunSpecSnapshot :=
  let (containers, volumes) := (jPathArr j "template.containers", jPathArr j "template.volumes")
  let envs := containers.flatMap (·.arrAt "env")
  let envBindings := envs.filterMap fun e => (e.strAt? "name").map (·, e.pathStr? "valueSource.secretKeyRef.secret")
  let deployEnvVals := envs.filterMap fun e => if e.strAt? "name" == some "QED_DEPLOY_ENV" then some (e.strAt? "value") else none
  let volKind (v : Json) := (["secret", "cloudSqlInstance", "gcs", "nfs", "emptyDir"].find? fun k => (v.get? k).isSome).getD "volume"
  let extractServing (f : String) := (j.arrAt f).filterMap fun t => let pct := (t.natAt? "percent").getD 0; if pct > 0 then some (t.strAtD "type", revisionLeaf (t.strAtD "revision"), pct) else none
  let extractTagged (f : String) := (j.arrAt f).filterMap fun t => (nonEmptyStr? (t.strAt? "tag")).map (·, revisionLeaf (t.strAtD "revision"))
  let tsServing := extractServing "trafficStatuses"
  { region, existsService := true, invokerIamDisabled := (j.boolAt? "invokerIamDisabled").getD false,
    ingress := j.strAtD "ingress", serviceAccount := (j.pathStr? "template.serviceAccount").getD "", vpcEgress := (j.pathStr? "template.vpcAccess.egress").getD "",
    vpcInterfaces := (jPathArr j "template.vpcAccess.networkInterfaces").map fun ni => (ni.strAtD "network", ni.strAtD "subnetwork"),
    containerCount := containers.length, deployEnv? := match deployEnvVals with | [some v] => some v | [] => none | _ => some "<invalid>",
    envNames := (envBindings.map Prod.fst).eraseDups, envBindings,
    secretEnvRefs := (envBindings.filterMap Prod.snd ++ volumes.filterMap (·.pathStr? "secret.secret")).eraseDups,
    unexpectedVolumes := (volumes.map fun v => s!"{volKind v}:{v.strAtD "name" "<unnamed>"}").eraseDups,
    unexpectedVolumeMounts := (containers.flatMap fun c => (c.arrAt "volumeMounts").map fun m => s!"{m.strAtD "name" "<unnamed>"}:{m.strAtD "mountPath" "<unknown>"}").eraseDups,
    hasCommandOverride := containers.any fun c => !(c.arrAt "command").isEmpty || !(c.arrAt "args").isEmpty,
    latestReadyRevision? := nonEmptyLeaf? (j.strAt? "latestReadyRevision"), latestCreatedRevision? := nonEmptyLeaf? (j.strAt? "latestCreatedRevision"),
    servingTraffic := if !tsServing.isEmpty then tsServing else extractServing "traffic",
    taggedRoutes := (extractTagged "trafficStatuses" ++ extractTagged "traffic").eraseDups }

/-! ### 5. Validated `ToJson` / `FromJson` Codecs for `GcpPlan` -/

@[noinline] private def findEnumJson {α : Type} (all : List α) (f : α → String) (lbl : String) (j : Json) : Except String α := do
  let s : String ← fromJson j; (all.find? (f · == s)).elim (.error s!"unknown {lbl} `{s}`") .ok
@[instance_reducible] private def mkEnumToJson {α : Type} (f : α → String) : ToJson α := ⟨.str ∘ f⟩
@[instance_reducible] private def mkEnumFromJson {α : Type} (all : List α) (f : α → String) (lbl : String) : FromJson α := ⟨findEnumJson all f lbl⟩

@[noinline] private def deployKeyToJson (k : DeployKey) : Json := .obj [
  ("prodProjectId", .str k.shard.prodProjectId), ("nonProdProjectId", .str k.shard.nonProdProjectId), ("tenant", toJson k.tenant.num), ("app", toJson k.app.num),
  ("env", match k.env with | .prod => mkKindObj "prod" | .staging => mkKindObj "staging" | .preview pr => mkKindObj "preview" [("pr", toJson pr.num)])]
@[noinline] private def deployKeyFromJson (j : Json) : Except String DeployKey := do
  let envJ ← j.field "env"
  DeployKey.mkChecked (← fld j "prodProjectId") (← fld j "nonProdProjectId") (← fld j "tenant") (← fld j "app") (← fld envJ "kind") (← fld envJ "pr")
instance : ToJson DeployKey := ⟨deployKeyToJson⟩
instance : FromJson DeployKey := ⟨deployKeyFromJson⟩
private def dbClusterStr : DbCluster → String | .prodCluster => "prod" | .nonProdCluster => "nonProd"
private instance : ToJson DbCluster := mkEnumToJson dbClusterStr
private instance : FromJson DbCluster := mkEnumFromJson [.prodCluster, .nonProdCluster] dbClusterStr "DbCluster"
private instance : ToJson GcpRegion := mkEnumToJson GcpRegion.toString
private instance : FromJson GcpRegion := mkEnumFromJson GcpRegion.all GcpRegion.toString "region"
private instance : ToJson GcpRole := mkEnumToJson GcpRole.gcpName
private instance : FromJson GcpRole := mkEnumFromJson GcpRole.all GcpRole.gcpName "role"
private instance : ToJson GcpPermission := mkEnumToJson GcpPermission.gcpV2Name
private instance : FromJson GcpPermission := mkEnumFromJson GcpPermission.all GcpPermission.gcpV2Name "permission"

private def unitPrincipals : List (String × GcpPrincipal) := [("allUsers", .allUsers), ("allAuthenticatedUsers", .allAuthenticatedUsers), ("builder", .builder), ("edgeRouter", .edgeRouter)]
@[noinline] private def gcpPrincipalToJson : GcpPrincipal → Json
  | .runtimeSa k => mkKindObj "runtimeSa" [("key", toJson k)] | .external e => mkKindObj "external" [("email", .str e)]
  | p => mkKindObj ((unitPrincipals.find? (·.2 == p)).map Prod.fst |>.getD "allUsers")
@[noinline] private def gcpPrincipalFromJson (j : Json) : Except String GcpPrincipal := do
  let k : String ← fld j "kind"
  if let some (_, p) := unitPrincipals.find? (·.1 == k) then return p
  match k with | "runtimeSa" => return .runtimeSa (← fld j "key") | "external" => return .external (← fld j "email") | other => .error s!"unknown principal kind `{other}`"
private instance : ToJson GcpPrincipal := ⟨gcpPrincipalToJson⟩
private instance : FromJson GcpPrincipal := ⟨gcpPrincipalFromJson⟩
@[noinline] private def gcpResourceToJson : GcpResource → Json
  | .secret k s => mkKindObj "secret" [("key", toJson k), ("name", .str s)] | .cloudRun k => mkKindObj "cloudRun" [("key", toJson k)]
  | .cloudSqlDb c k db => mkKindObj "cloudSqlDb" [("cluster", toJson c), ("key", toJson k), ("db", .str db)]
  | .assetPrefix k h pub => mkKindObj "assetPrefix" [("key", toJson k), ("hash", .str h), ("isPublic", .bool pub)] | .project p => mkKindObj "project" [("projectId", .str p)]
@[noinline] private def gcpResourceFromJson (j : Json) : Except String GcpResource := do match (← fld (α := String) j "kind") with
  | "secret" => return .secret (← fld j "key") (← fld j "name") | "cloudRun" => return .cloudRun (← fld j "key")
  | "cloudSqlDb" => return .cloudSqlDb (← fld j "cluster") (← fld j "key") (← fld j "db")
  | "assetPrefix" => return .assetPrefix (← fld j "key") (← fld j "hash") ((← fld (α := Option Bool) j "isPublic").getD true)
  | "project" => let p : String ← fld j "projectId"; if !isValidGcpProjectId p then .error s!"invalid project resource id `{p}`" else return .project p
  | other => .error s!"unknown resource kind `{other}`"
private instance : ToJson GcpResource := ⟨gcpResourceToJson⟩
private instance : FromJson GcpResource := ⟨gcpResourceFromJson⟩
json_obj_codec% private GcpIamBinding [principal, role, resource]
json_obj_codec% private GcpDenyRule [principals, permissions, resource]
json_obj_codec% private ScaleSpec [minInstances, maxInstances, memoryMb, cpuMilli, concurrency, timeoutSec]

private def reqPlan (ok : Bool) (msg : String) : Except String Unit := if ok then .ok () else .error s!"GcpPlan.fromJson: {msg}"
@[noinline, nospecialize] private def reqPlanAll {α : Type} (xs : List α) (ok : α → Bool) (msg : α → String) : Except String Unit := xs.forM fun x => reqPlan (ok x) (msg x)

@[noinline] private def validateGcpPlan (p : GcpPlan) : Except String Unit := do
  let key := p.key
  reqPlan (p.serviceAccountId == renderSaId key) s!"serviceAccountId `{p.serviceAccountId}` does not match canonical `{renderSaId key}`"
  reqPlan (p.cloudRunName == renderCloudRunName key) s!"cloudRunName `{p.cloudRunName}` does not match canonical `{renderCloudRunName key}`"
  p.scale.validate
  reqPlan (!p.regions.isEmpty && p.regions.eraseDups.length == p.regions.length) "regions must be non-empty and duplicate-free"
  reqPlanAll p.assetPaths isSafeRelativeAssetPath (s!"unsafe asset path `{·}`")
  reqPlanAll p.egressAllow Qed.Deploy.isValidEgressOrigin (s!"unsafe egress origin `{·}`")
  reqPlanAll p.secretNames Qed.Server.isValidEnvVarName (s!"invalid secret env var name `{·}`")
  reqPlanAll p.managedDbs (Qed.Deploy.isValidDbShortName ·.1) (fun (db, _) => s!"invalid managed DB name `{db}`")
  reqPlanAll p.managedDbs (·.2 == clusterForEnv key.env) (fun _ => s!"database cluster does not match environment `{key.env.toDeployEnv}`")
  let assetPubFlags := p.bindings.filterMap fun b => match b.resource with | .assetPrefix _ _ pub => some pub | _ => none
  reqPlan (assetPubFlags.eraseDups.length ≤ 1) "inconsistent assetPrefix `isPublic` flags across bindings"
  let expectedAssetPub := assetPubFlags.headD true; let expectedAssetReader : GcpPrincipal := if expectedAssetPub then .allUsers else .edgeRouter
  reqPlanAll p.bindings (fun b => match b.principal, b.role, b.resource with
    | .runtimeSa k', .secretManagerAccessor, .secret k s => k' == key && k == key && p.secretNames.contains s
    | .runtimeSa k', .cloudSqlClient, .cloudSqlDb cl k db => k' == key && k == key && cl == clusterForEnv key.env && p.managedDbs.contains (db, cl)
    | .edgeRouter, .runInvoker, .cloudRun k => k == key
    | .builder, .storageObjectAdmin, .assetPrefix k h pub => k == key && h == p.buildHash && pub == expectedAssetPub
    | prin, .storageLegacyObjectReader, .assetPrefix k h pub => prin == expectedAssetReader && k == key && h == p.buildHash && pub == expectedAssetPub
    | _, _, _ => false) (fun _ => "binding does not match any legal compiled least-privilege shape")
  reqPlanAll p.denies (fun d => d.principals == [.allUsers, .allAuthenticatedUsers] && match d.resource, d.permissions with
    | .cloudRun k, [.runInvoke] => k == key | .secret k s, [.secretAccessor] => k == key && p.secretNames.contains s | _, _ => false)
    (fun _ => "deny rule does not match any legal compiled least-privilege shape")
  let hasPubDeny (res : GcpResource) (perm : GcpPermission) :=
    p.denies.any fun d => d.resource == res && d.principals.contains .allUsers && d.principals.contains .allAuthenticatedUsers && d.permissions.contains perm
  reqPlan (hasPubDeny (.cloudRun key) .runInvoke) "missing mandatory public Cloud Run deny rule"
  reqPlanAll p.secretNames (fun s => hasPubDeny (.secret key s) .secretAccessor) (s!"missing mandatory public deny rule for secret `{·}`")

@[noinline] def GcpPlan.toJson (p : GcpPlan) : Json := .obj [
  ("key", ToJson.toJson p.key), ("buildHash", .str p.buildHash), ("regions", ToJson.toJson p.regions), ("scale", ToJson.toJson p.scale),
  ("serviceAccountId", .str p.serviceAccountId), ("cloudRunName", .str p.cloudRunName), ("secretNames", ToJson.toJson p.secretNames),
  ("managedDbs", ToJson.toJson p.managedDbs), ("assetPaths", ToJson.toJson p.assetPaths), ("egressAllow", ToJson.toJson p.egressAllow),
  ("bindings", ToJson.toJson p.bindings), ("denies", ToJson.toJson p.denies)]

@[noinline] def GcpPlan.fromJson (j : Json) : Except String GcpPlan := do
  let p : GcpPlan := {
    key := ← fld j "key", buildHash := ← fld j "buildHash", regions := ← fld j "regions", scale := ← fld j "scale",
    serviceAccountId := ← fld j "serviceAccountId", cloudRunName := ← fld j "cloudRunName", secretNames := ← fld j "secretNames",
    managedDbs := ← fld j "managedDbs", assetPaths := ← fld j "assetPaths", egressAllow := ← fld j "egressAllow",
    bindings := ← fld j "bindings", denies := ← fld j "denies" }
  validateGcpPlan p; return p

/-! ### 6. Pure Live Security Drift Verifier (`checkDrift`, `checkDriftLive`) & Universal Theorems -/

inductive DriftFinding where
  | keyMismatch (observed desired : DeployKey) | unauthorizedBinding (binding : GcpIamBinding)
  | unauthorizedRawBinding (member role : String) (resource : GcpResource) | missingBinding (binding : GcpIamBinding)
  | missingRegionalBinding (region : GcpRegion) (binding : GcpIamBinding) | missingRegion (region : GcpRegion)
  | missingRegionalEgressPolicy (region : GcpRegion) | unsafeCloudRunSpec (region : GcpRegion) (detail : String)
  | missingDenyPolicy (policyId : String) | extraSecret (secretName : String) | missingSecret (secretName : String)
  | extraDb (dbName : String) | missingDb (dbName : String) | extraEgress (origin : String) | missingEgress (origin : String)
  | missingRegionalEgress (region : GcpRegion) (origin : String)
deriving Inhabited, DecidableEq

structure GcpLiveSnapshot where
  (observed : GcpObservedState) (rawBindings : List (String × String × GcpResource) := [])
  (regionStates : List (GcpRegion × List GcpIamBinding × List String) := [])
  (serviceSpecs : List CloudRunSpecSnapshot := []) (presentDenyPolicies : List String := []) (presentEgressPolicies : List GcpRegion := [])
deriving Inhabited

private def diffMap {α β : Type} [BEq α] (xs ys : List α) (f : α → β) : List β := (xs.filter (!ys.contains ·)).map f

def checkDrift (observed : GcpObservedState) (desired : GcpPlan) : List DriftFinding :=
  if observed.key != desired.key then [.keyMismatch observed.key desired.key]
  else
    let desiredDbNames := desired.managedDbs.map Prod.fst
    diffMap observed.bindings desired.bindings .unauthorizedBinding ++
    ((desired.bindings.filter fun b => !b.resource.isAsset && !observed.bindings.contains b).map .missingBinding) ++
    diffMap observed.secretNames desired.secretNames .extraSecret ++ diffMap desired.secretNames observed.secretNames .missingSecret ++
    diffMap observed.managedDbs desiredDbNames .extraDb ++ diffMap desiredDbNames observed.managedDbs .missingDb ++
    diffMap observed.egressAllow desired.egressAllow .extraEgress ++ diffMap desired.egressAllow observed.egressAllow .missingEgress

@[noinline] private def checkServiceSpecDrift (desired : GcpPlan) (spec : CloudRunSpecSnapshot) : List DriftFinding :=
  let fail (msg : String) := DriftFinding.unsafeCloudRunSpec spec.region msg
  if !spec.existsService then [fail "Cloud Run service does not exist"]
  else
    let (projId, expectedSub, expectedEnv) := (desired.key.shard.projectFor desired.key.env, s!"qed-swp-{spec.region}", toString desired.key.env.toDeployEnv)
    let ifaceOk (net sub : String) :=
      (net == "qed-vpc" || net == s!"projects/{projId}/global/networks/qed-vpc") &&
      (sub == expectedSub || sub == s!"projects/{projId}/regions/{spec.region}/subnetworks/{expectedSub}")
    let scalarChecks : List (Bool × String) := [
      (spec.invokerIamDisabled, "invokerIamDisabled is true"),
      (spec.ingress != "INGRESS_TRAFFIC_INTERNAL_LOAD_BALANCER", s!"ingress is `{spec.ingress}` (expected INGRESS_TRAFFIC_INTERNAL_LOAD_BALANCER)"),
      (spec.serviceAccount != renderSaEmail desired.key, s!"serviceAccount is `{spec.serviceAccount}` (expected {renderSaEmail desired.key})"),
      (spec.vpcEgress != "VPC_EGRESS_ALL_TRAFFIC", s!"vpcAccess.egress is `{spec.vpcEgress}` (expected VPC_EGRESS_ALL_TRAFFIC)"),
      (spec.vpcInterfaces.isEmpty || !spec.vpcInterfaces.all fun (n, s) => ifaceOk n s, s!"vpcAccess.networkInterfaces does not match qed-vpc/{expectedSub}"),
      (spec.deployEnv? != some expectedEnv, s!"QED_DEPLOY_ENV is `{spec.deployEnv?.getD "<missing>"}` (expected `{expectedEnv}`)"),
      (spec.containerCount != 1, s!"template.containers count is {spec.containerCount} (expected 1; sidecars forbidden)"),
      (spec.hasCommandOverride, "unexpected container command/args override")]
    let revChecks : List (Bool × String) :=
      if spec.latestReadyRevision?.isSome || spec.latestCreatedRevision?.isSome then
        match spec.latestReadyRevision?, spec.latestCreatedRevision? with
        | some r, some cr =>
            let totalPct := spec.servingTraffic.foldl (init := 0) fun acc (_, _, p) => acc + p
            let allOnReady := spec.servingTraffic.all fun (typ, rev, _) => rev == r || (rev.isEmpty && typ == "TRAFFIC_TARGET_ALLOCATION_TYPE_LATEST")
            [(r != cr, s!"latestReadyRevision (`{r}`) != latestCreatedRevision (`{cr}`)"), (totalPct != 100 || !allOnReady, s!"serving traffic does not route 100% exclusively to latestReadyRevision `{r}`")]
        | _, _ => [(true, "missing latestReadyRevision or latestCreatedRevision")]
      else []
    let envF := spec.envNames.filterMap fun nm =>
      if nm == "QED_DEPLOY_ENV" then none else if !Qed.Server.isValidEnvVarName nm then some (fail s!"forbidden/reserved container env var `{nm}`")
      else if !desired.secretNames.contains nm then some (fail s!"unexpected undeclared container env var `{nm}`") else none
    let secBindF := desired.secretNames.filterMap fun s =>
      let expId := secretId desired.key s
      match spec.envBindings.filter (·.1 == s) with
      | [(_, some refId)] => if refId == expId then none else some (fail s!"secret env `{s}` references `{refId}` (expected `{expId}`)")
      | [(_, none)] => some (fail s!"secret env `{s}` is overridden with plaintext value instead of secretKeyRef `{expId}`")
      | [] => some (fail s!"missing secretKeyRef env binding for `{s}` (expected `{expId}`)")
      | _ => some (fail s!"duplicate env bindings for secret `{s}` (expected exactly one secretKeyRef `{expId}`)")
    ((scalarChecks ++ revChecks).filterMap fun (bad, msg) => if bad then some (fail msg) else none) ++ envF ++ secBindF ++
    diffMap spec.secretEnvRefs (desired.secretNames.map (secretId desired.key)) (fun s => fail s!"unexpected secret ref `{s}`") ++
    spec.taggedRoutes.map (fun (tg, rev) => fail s!"unexpected tagged traffic route `{tg}` -> `{rev}`") ++
    spec.unexpectedVolumes.map (fun vol => fail s!"unexpected template.volumes entry `{vol}`") ++
    spec.unexpectedVolumeMounts.map (fun vm => fail s!"unexpected container volumeMount `{vm}`")

@[noinline] def checkDriftLive (snap : GcpLiveSnapshot) (desired : GcpPlan) : List DriftFinding :=
  if snap.observed.key != desired.key then [.keyMismatch snap.observed.key desired.key]
  else
    let desiredRun := desired.bindings.filter fun b => match b.resource with | .cloudRun _ => true | _ => false
    let regF := desired.regions.flatMap fun reg =>
      let missEgPol := if snap.presentEgressPolicies.contains reg then [] else [.missingRegionalEgressPolicy reg]
      match snap.regionStates.find? (·.1 == reg) with
      | some (_, rbs, regs) => missEgPol ++ diffMap rbs desired.bindings .unauthorizedBinding ++ diffMap desiredRun rbs (.missingRegionalBinding reg) ++
          diffMap regs desired.egressAllow .extraEgress ++ diffMap desired.egressAllow regs (.missingRegionalEgress reg)
      | none => [.missingRegion reg] ++ missEgPol ++ desiredRun.map (.missingRegionalBinding reg) ++ desired.egressAllow.map (.missingRegionalEgress reg)
    let extraRegF := (snap.regionStates.filter (!desired.regions.contains ·.1)).flatMap fun (_, rbs, regs) =>
      diffMap rbs desired.bindings .unauthorizedBinding ++ diffMap regs desired.egressAllow .extraEgress
    let specF := desired.regions.flatMap fun reg =>
      (snap.serviceSpecs.find? (·.region == reg)).elim [.unsafeCloudRunSpec reg "missing Cloud Run service spec observation"] (checkServiceSpecDrift desired)
    let denyF := diffMap (desired.denies.map (·.resource.denyPolicyId)).eraseDups snap.presentDenyPolicies .missingDenyPolicy
    (checkDrift snap.observed desired ++ snap.rawBindings.map (fun (m, r, res) => DriftFinding.unauthorizedRawBinding m r res) ++ regF ++ extraRegF ++ specF ++ denyF).eraseDups

theorem checkDrift_catches_allUsers_invoke (key : DeployKey) (buildHash : String) (spec : DeploySpec) (m : Qed.Deploy.DeployManifest)
    (observed : GcpObservedState) (hkey : observed.key = key)
    (hpub : { principal := .allUsers, role := .runInvoker, resource := .cloudRun key : GcpIamBinding } ∈ observed.bindings) :
    DriftFinding.unauthorizedBinding { principal := .allUsers, role := .runInvoker, resource := .cloudRun key } ∈ checkDrift observed (compileInfra key buildHash spec m) := by
  let bad : GcpIamBinding := { principal := .allUsers, role := .runInvoker, resource := .cloudRun key }
  have hnotDesired : bad ∉ (compileInfra key buildHash spec m).bindings := by
    intro hmem; simp only [compileInfra, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with (((⟨_, _, h⟩ | ⟨_, _, h⟩) | h) | (h | h)) <;> simp [bad] at h
  have hnotContains : ((compileInfra key buildHash spec m).bindings.contains bad) = false := by
    cases hc : (compileInfra key buildHash spec m).bindings.contains bad with | false => rfl | true => exact absurd (List.contains_iff_mem.mp hc) hnotDesired
  have hne : (observed.key != (compileInfra key buildHash spec m).key) = false := by simp [compileInfra, hkey]
  unfold checkDrift diffMap; simp only [hne, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_map, List.mem_filter, Bool.not_eq_true']
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨bad, ⟨hpub, hnotContains⟩, rfl⟩))))))

theorem checkDriftLive_catches_unrecognized_role (snap : GcpLiveSnapshot) (desired : GcpPlan) (hkey : snap.observed.key = desired.key)
    (member role : String) (res : GcpResource) (hmem : (member, role, res) ∈ snap.rawBindings) :
    DriftFinding.unauthorizedRawBinding member role res ∈ checkDriftLive snap desired := by
  have hne : (snap.observed.key != desired.key) = false := by simp [hkey]
  unfold checkDriftLive; simp only [hne, Bool.false_eq_true, ↓reduceIte, List.mem_eraseDups, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(member, role, res), hmem, rfl⟩))))

end Qed.Cloud
