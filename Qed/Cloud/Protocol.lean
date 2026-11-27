import Qed.Base64
import Qed.Json.Basic
import Qed.Cloud.Env
import Qed.Date

/-! ## Hosted Qed Cloud Wire Protocol (`Qed.Cloud.Protocol`) -/

namespace Qed.Cloud.Protocol
open Qed Qed.Cloud

/-! ### 1. Bounds, Base64 & Input Validators -/

def maxSourceFiles      : Nat := 500
def maxSourceFileBytes  : Nat := 2 * 1024 * 1024
def maxTotalSourceBytes : Nat := 16 * 1024 * 1024

abbrev encodeBase64 (bs : ByteArray) : String := Qed.Base64.encode bs
abbrev decodeBase64? (s : String) : Option ByteArray := (Qed.Base64.decode s).toOption

def isValidAppSlug (s : String) : Bool := checkAsciiIdent 2 48 isDnsAlpha isDnsLabelChar (· != '-') s && !Qed.Str.contains s "--"
def isValidEnvName (s : String) : Bool := ["prod", "staging", "preview"].contains s
def isValidDeployStatus (s : String) : Bool := ["queued", "verifying", "building", "deploying", "live", "failed", "canceled"].contains s
def isValidDeploymentId (s : String) : Bool := checkAsciiIdent 1 128 isAsciiAlnum (fun c => isAsciiAlnum c || c == '_' || c == '-') (s := s)
def isValidLogSeverity (s : String) : Bool := ["debug", "info", "warn", "error"].contains s
def isValidSecretKey (s : String) : Bool :=
  checkAsciiIdent 1 64 (fun c => ('A' ≤ c && c ≤ 'Z') || c == '_') (fun c => ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '_') (s := s)
def isValidModuleName (s : String) : Bool := !s.isEmpty && s.length ≤ 128 && s.toList.all fun c => c.isAlphanum || c == '.' || c == '_'

def isValidDeviceUserCode (s : String) : Bool :=
  let cs := s.toList; let isCode (c : Char) := ('A' ≤ c && c ≤ 'Z') || ('2' ≤ c && c ≤ '9')
  cs.length == 9 && cs[4]? == some '-' && (cs.take 4).all isCode && (cs.drop 5).all isCode

def validateSecretTarget (appSlug envStr name : String) (fmt : String → String := id) (envHint : Bool := false) : Except String Unit := do
  if !isValidAppSlug appSlug then throw s!"invalid app slug `{fmt appSlug}`"
  if !isValidEnvName envStr then throw s!"invalid env `{fmt envStr}`{if envHint then " (expected prod, staging, or preview)" else ""}"
  if !isValidSecretKey name then throw s!"invalid secret name `{fmt name}` (use UPPER_SNAKE_CASE)"

private def forbiddenSourceTopDirs : List String := ["dist", "node_modules", "target"]
private def allowedSourceExactNames : List String :=
  ["lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json", "qed.json", "robots.txt", "sitemap.xml", "manifest.json"]
private def binarySourceExts : List String := [".png", ".jpg", ".jpeg", ".gif", ".webp", ".ico", ".woff", ".woff2", ".ttf", ".otf"]
private def textSourceExts : List String := [".lean", ".css", ".html", ".js", ".mjs", ".json", ".txt", ".xml", ".webmanifest", ".svg"]

private def hasExtIn (exts : List String) (seg : String) : Bool :=
  let low := Qed.Str.toLower seg; exts.any fun ext => low.length > ext.length && Qed.Str.endsWith low ext

def isBinarySourceExt (p : String) : Bool :=
  let seg := (Qed.Str.splitChar p '/').getLastD p; !Qed.Str.startsWith seg "." && hasExtIn binarySourceExts seg

def isValidSourceRelPath (p : String) : Bool :=
  !p.isEmpty && p.length ≤ 240 && !Qed.Str.startsWith p "/" && !Qed.Str.endsWith p "/" &&
  !Env.hasCtrlOrWs p "\\?#:" (forbidWs := false) &&
  let segs := Qed.Str.splitChar p '/'
  let last := segs.getLastD ""
  !segs.isEmpty && segs.all (fun seg => !seg.isEmpty && !Qed.Str.startsWith seg "." && !forbiddenSourceTopDirs.contains (Qed.Str.toLower seg)) &&
  (allowedSourceExactNames.contains last || hasExtIn textSourceExts last || hasExtIn binarySourceExts last)

def normalizeApiBase (raw : String) : String := trimTrailingSlash (Qed.Str.trim raw)

def isValidCloudApiUrl (raw : String) : Bool :=
  let u := normalizeApiBase raw
  !u.isEmpty && !Env.hasCtrlOrWs u "@\\?#" && (isStrictLoopbackUrl u || (parseHttpsHostPort? u).isSome)

/-! ### 2. Device Login & Account Protocol -/

structure DeviceStartResp where (deviceCode userCode verifyUrl : String) (expiresInSec : Nat := 600) (intervalSec : Nat := 2) deriving Inhabited
json_obj_codec% DeviceStartResp [deviceCode, userCode, verifyUrl, expiresInSec, intervalSec]

structure DevicePollReq where deviceCode : String deriving Inhabited
json_obj_codec% DevicePollReq [deviceCode]

structure DevicePollResp where (status : String) (token userId email : Option String := none) deriving Inhabited
json_obj_codec% DevicePollResp [status, token, userId, email]

structure WhoamiResp where (userId email : String) (tenantId appsCount : Nat) deriving Inhabited
json_obj_codec% WhoamiResp [userId, email, tenantId, appsCount]

/-! ### 3. Source Bundle & Deployment Protocol -/

structure SourceFile where (path content : String) (encoding : String := "utf8") deriving Inhabited, BEq

private def SourceFile.withEncoding {α : Type} (f : SourceFile) (maxBytes? : Option Nat)
    (onUtf8 : String → α) (onBin : ByteArray → α) : Except String α := do
  if f.encoding == "utf8" then pure (onUtf8 f.content)
  else if f.encoding == "base64" then
    if let some lim := maxBytes? then
      if f.content.utf8ByteSize > Qed.Base64.encodedLength lim then throw s!"source file `{f.path}` exceeds max size (> {lim} bytes)"
    match decodeBase64? f.content with
    | some bs => pure (onBin bs)
    | none    => throw s!"source file `{f.path}` has invalid base64 content"
  else throw s!"source file `{f.path}` has invalid encoding `{f.encoding}` (expected utf8 or base64)"

def SourceFile.decodedBytes (f : SourceFile) : Except String ByteArray := f.withEncoding none String.toUTF8 id
json_obj_codec% SourceFile [path, content, encoding := "utf8"]

structure SourceBundle where files : Array SourceFile deriving Inhabited, BEq

def SourceBundle.validate (b : SourceBundle) : Except String Unit := do
  if b.files.isEmpty then throw "source bundle cannot be empty"
  if b.files.size > maxSourceFiles then throw s!"source bundle has {b.files.size} files (max {maxSourceFiles})"
  discard <| b.files.foldlM (init := ((0 : Nat), ([] : List String))) fun (totalBytes, seen) f => do
    if !isValidSourceRelPath f.path then throw s!"invalid source file path `{f.path}`"
    if seen.contains f.path then throw s!"duplicate source file path `{f.path}`"
    let sz ← f.withEncoding (some maxSourceFileBytes) String.utf8ByteSize ByteArray.size
    if sz > maxSourceFileBytes then throw s!"source file `{f.path}` exceeds max size ({sz} > {maxSourceFileBytes} bytes)"
    let nextBytes := totalBytes + sz
    if nextBytes > maxTotalSourceBytes then throw s!"source bundle exceeds max total size ({maxTotalSourceBytes} bytes)"
    return (nextBytes, f.path :: seen)
  if !b.files.any (Qed.Str.endsWith ·.path ".lean") then throw "source bundle must include at least one `.lean` file"
json_obj_codec% SourceBundle [files] validate SourceBundle.validate

structure DeployUploadReq where
  (appSlug : String) (env : String := "prod") (pr : Nat := 0) (mod : String := "App") (deployName : String := "") (bundle : SourceBundle)
deriving Inhabited

def DeployUploadReq.validate (r : DeployUploadReq) : Except String Unit := do
  if !isValidAppSlug r.appSlug then throw s!"invalid app slug `{r.appSlug}` (use 2-48 lowercase letters, digits, or single hyphens)"
  if !isValidEnvName r.env then throw s!"invalid env `{r.env}` (expected prod, staging, or preview)"
  if r.env == "preview" && r.pr == 0 then throw "preview deploy requires a positive PR number"
  if r.env != "preview" && r.pr != 0 then throw "PR number is only valid for preview deploys"
  if !isValidModuleName r.mod then throw s!"invalid root module `{r.mod}`"
  if !r.deployName.isEmpty && !isValidModuleName r.deployName then throw s!"invalid deploy spec name `{r.deployName}`"
  r.bundle.validate
json_obj_codec% DeployUploadReq [appSlug, env, pr, mod, deployName, bundle] validate DeployUploadReq.validate

structure DeployUploadResp where (deploymentId appSlug : String) (tenantId appId : Nat) (status dashboardUrl : String) deriving Inhabited
json_obj_codec% DeployUploadResp [deploymentId, appSlug, tenantId, appId, status, dashboardUrl]

structure DeployLogEntry where (seq ts : Nat) (level message : String) deriving Inhabited
json_obj_codec% DeployLogEntry [seq, ts, level, message]

structure DeploymentView where
  (id appSlug env : String) (pr : Nat) (status url buildHash : String) (verifiedDecls : Nat)
  (errorMsg : String) (createdAt updatedAt : Nat) (logs : Array DeployLogEntry := #[])
deriving Inhabited
json_obj_codec% DeploymentView [id, appSlug, env, pr, status, url, buildHash, verifiedDecls, errorMsg, createdAt, updatedAt, logs]

structure AppSummary where (slug : String) (tenantId appId : Nat) (prodUrl lastStatus : String) (deployCount createdAt : Nat) deriving Inhabited
json_obj_codec% AppSummary [slug, tenantId, appId, prodUrl, lastStatus, deployCount, createdAt]

structure AppsListResp where apps : Array AppSummary deriving Inhabited
json_obj_codec% AppsListResp [apps]

structure SecretSetReq where (appSlug : String) (env : String := "prod") (name value : String) deriving Inhabited, BEq
def SecretSetReq.validate (r : SecretSetReq) : Except String Unit := do
  validateSecretTarget r.appSlug r.env r.name
  if r.value.isEmpty || r.value.utf8ByteSize > 65536 then throw "secret value must be 1..65536 bytes"
json_obj_codec% SecretSetReq [appSlug, env, name, value] validate SecretSetReq.validate

structure SecretsListResp where (appSlug : String) (names : Array String) deriving Inhabited
json_obj_codec% SecretsListResp [appSlug, names]

structure SecretDeleteReq where (appSlug : String) (env : String := "prod") (name : String) deriving Inhabited, BEq
def SecretDeleteReq.validate (r : SecretDeleteReq) : Except String Unit := validateSecretTarget r.appSlug r.env r.name
json_obj_codec% SecretDeleteReq [appSlug, env := "prod", name] validate SecretDeleteReq.validate

structure RollbackReq where (appSlug deploymentId : String) deriving Inhabited
json_obj_codec% RollbackReq [appSlug, deploymentId]

structure CancelDeployReq where deploymentId : String deriving Inhabited, BEq
def CancelDeployReq.validate (r : CancelDeployReq) : Except String Unit := do
  if !isValidDeploymentId r.deploymentId then throw s!"invalid deployment id `{r.deploymentId}`"
json_obj_codec% CancelDeployReq [deploymentId] validate CancelDeployReq.validate

structure RuntimeLogView where (id timestamp severity source message : String) deriving Inhabited, BEq
json_obj_codec% RuntimeLogView [id, timestamp, severity, source, message]

structure RuntimeLogsResp where
  (appSlug env : String) (pr : Nat := 0) (logs : Array RuntimeLogView) (nextPageToken : Option String := none)
deriving Inhabited, BEq
json_obj_codec% RuntimeLogsResp [appSlug, env, pr := 0, logs, nextPageToken]

structure TokenRevokeResp where revoked : Bool deriving Inhabited, BEq
json_obj_codec% TokenRevokeResp [revoked]

end Qed.Cloud.Protocol
