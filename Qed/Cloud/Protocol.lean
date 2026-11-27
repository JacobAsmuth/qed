import Qed.Base64
import Qed.Json.Basic
import Qed.Cloud.Env
import Qed.Date

/-! ## Hosted Qed Cloud Wire Protocol (`Qed.Cloud.Protocol`)
    Pure, verified JSON request/response types and input validators shared between
    the open-source `qed` CLI client and the hosted Qed Cloud control plane. -/

namespace Qed.Cloud.Protocol

open Qed Qed.Cloud

/-! ### 1. Bounds, Base64 & Input Validators -/

def maxSourceFiles      : Nat := 500
def maxSourceFileBytes  : Nat := 2 * 1024 * 1024
def maxTotalSourceBytes : Nat := 16 * 1024 * 1024

/-- Pure, total standard Base64 encoder backed by formally verified `Qed.Base64.encode`. -/
def encodeBase64 (bs : ByteArray) : String := Qed.Base64.encode bs

/-- Pure, total standard Base64 decoder backed by formally verified `Qed.Base64.decode`. -/
def decodeBase64? (s : String) : Option ByteArray := (Qed.Base64.decode s).toOption

def isValidAppSlug (s : String) : Bool :=
  match s.toList with
  | c :: rest =>
      let cs := c :: rest
      2 ≤ cs.length && cs.length ≤ 48 && 'a' ≤ c && c ≤ 'z' &&
      cs.all (fun ch => ('a' ≤ ch && ch ≤ 'z') || ('0' ≤ ch && ch ≤ '9') || ch == '-') &&
      cs.getLastD '-' != '-' && !Qed.Str.contains s "--"
  | [] => false

def isValidEnvName (s : String) : Bool :=
  s == "prod" || s == "staging" || s == "preview"

def isValidDeployStatus (s : String) : Bool :=
  ["queued", "verifying", "building", "deploying", "live", "failed", "canceled"].contains s

private def isAsciiAlnum (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9')

def isValidDeploymentId (s : String) : Bool :=
  match s.toList with
  | c :: rest =>
      let cs := c :: rest
      1 ≤ cs.length && cs.length ≤ 128 && isAsciiAlnum c &&
      cs.all (fun ch => isAsciiAlnum ch || ch == '_' || ch == '-')
  | [] => false

def isValidLogSeverity (s : String) : Bool :=
  ["debug", "info", "warn", "error"].contains s

def isValidDeviceUserCode (s : String) : Bool :=
  let cs := s.toList
  cs.length == 9 && cs[4]? == some '-' &&
  let isCodeChar (c : Char) : Bool := ('A' ≤ c && c ≤ 'Z') || ('2' ≤ c && c ≤ '9')
  (cs.take 4).all isCodeChar && (cs.drop 5).all isCodeChar

def isValidSecretKey (s : String) : Bool :=
  match s.toList with
  | c :: rest =>
      let cs := c :: rest
      1 ≤ cs.length && cs.length ≤ 64 && (('A' ≤ c && c ≤ 'Z') || c == '_') &&
      cs.all (fun ch => ('A' ≤ ch && ch ≤ 'Z') || ('0' ≤ ch && ch ≤ '9') || ch == '_')
  | [] => false

def isValidModuleName (s : String) : Bool :=
  !s.isEmpty && s.length ≤ 128 && s.toList.all (fun c => c.isAlphanum || c == '.' || c == '_')

def validateSecretTarget (appSlug envStr name : String) (fmt : String → String := id)
    (envHint : Bool := false) : Except String Unit := do
  if !isValidAppSlug appSlug then throw s!"invalid app slug `{fmt appSlug}`"
  if !isValidEnvName envStr then
    throw s!"invalid env `{fmt envStr}`{if envHint then " (expected prod, staging, or preview)" else ""}"
  if !isValidSecretKey name then throw s!"invalid secret name `{fmt name}` (use UPPER_SNAKE_CASE)"

private def forbiddenSourceTopDirs : List String :=
  ["dist", "node_modules", "target"]

private def allowedSourceExactNames : List String :=
  ["lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json",
   "qed.json", "robots.txt", "sitemap.xml", "manifest.json"]

private def binarySourceExts : List String :=
  [".png", ".jpg", ".jpeg", ".gif", ".webp", ".ico", ".woff", ".woff2", ".ttf", ".otf"]

private def textSourceExts : List String :=
  [".lean", ".css", ".html", ".js", ".mjs", ".json", ".txt", ".xml", ".webmanifest", ".svg"]

private def hasExtIn (exts : List String) (seg : String) : Bool :=
  let lower := Qed.Str.toLower seg
  exts.any fun ext => lower.length > ext.length && Qed.Str.endsWith lower ext

def isBinarySourceExt (p : String) : Bool :=
  let seg := (Qed.Str.splitChar p '/').getLastD p
  !Qed.Str.startsWith seg "." && hasExtIn binarySourceExts seg

private def isAllowedSourceExt (seg : String) : Bool :=
  allowedSourceExactNames.contains seg || hasExtIn textSourceExts seg || hasExtIn binarySourceExts seg

def isValidSourceRelPath (p : String) : Bool :=
  !p.isEmpty && p.length ≤ 240 && !Qed.Str.startsWith p "/" && !Qed.Str.endsWith p "/" &&
  !p.toList.any (fun c => c.toNat < 0x20 || c.toNat == 0x7F || c == '\\' || c == '?' || c == '#' || c == ':') &&
  let segs := Qed.Str.splitChar p '/'
  !segs.isEmpty &&
  segs.all (fun seg => !seg.isEmpty && !Qed.Str.startsWith seg "." && !forbiddenSourceTopDirs.contains (Qed.Str.toLower seg)) &&
  isAllowedSourceExt (segs.getLastD "")

def normalizeApiBase (raw : String) : String :=
  let t := Qed.Str.trim raw
  if Qed.Str.endsWith t "/" then Qed.Str.take t (t.length - 1) else t

/-- Hosted Qed Cloud API base must be either `https://<valid-host>[:port]` (for Cloud Run `*.a.run.app`
    or custom domain) or a strict loopback HTTP URL (`http://127.0.0.1[:port]` / `http://localhost[:port]`)
    for local development. Rejects paths, queries, fragments, credentials, and control chars. -/
def isValidCloudApiUrl (raw : String) : Bool :=
  let u := normalizeApiBase raw
  if u.isEmpty || u.toList.any (fun c => c.isWhitespace || c.toNat < 0x20 || c.toNat == 0x7F || c == '@' || c == '\\' || c == '?' || c == '#') then false
  else if Qed.Str.startsWith u "http://" then isStrictLoopbackUrl u
  else if Qed.Str.startsWith u "https://" then
    let auth := Qed.Str.drop u 8
    !auth.isEmpty && !Qed.Str.contains auth "/" &&
    match Qed.Str.splitChar auth ':' with
    | [h] => isValidHostname (Qed.Str.toLower h)
    | [h, pStr] =>
        match Qed.Str.parseNat? pStr with
        | some p => 1 ≤ p && p ≤ 65535 && Nat.repr p == pStr && isValidHostname (Qed.Str.toLower h)
        | none => false
    | _ => false
  else false

/-! ### 2. Device Login & Account Protocol -/

structure DeviceStartResp where
  deviceCode   : String
  userCode     : String
  verifyUrl    : String
  expiresInSec : Nat := 600
  intervalSec  : Nat := 2
deriving Inhabited, BEq, Repr
json_obj_codec% DeviceStartResp [deviceCode, userCode, verifyUrl, expiresInSec, intervalSec]

structure DevicePollReq where
  deviceCode : String
deriving Inhabited, BEq, Repr
json_obj_codec% DevicePollReq [deviceCode]

structure DevicePollResp where
  status : String
  token  : Option String := none
  userId : Option String := none
  email  : Option String := none
deriving Inhabited, BEq, Repr
json_obj_codec% DevicePollResp [status, token, userId, email]

structure WhoamiResp where
  userId    : String
  email     : String
  tenantId  : Nat
  appsCount : Nat
deriving Inhabited, BEq, Repr
json_obj_codec% WhoamiResp [userId, email, tenantId, appsCount]

/-! ### 3. Source Bundle & Deployment Protocol -/

structure SourceFile where
  path     : String
  content  : String
  encoding : String := "utf8"
deriving Inhabited, BEq, Repr

private def SourceFile.withEncoding {α : Type} (f : SourceFile) (maxBytes? : Option Nat)
    (onUtf8 : String → α) (onBin : ByteArray → α) : Except String α := do
  if f.encoding == "utf8" then pure (onUtf8 f.content)
  else if f.encoding == "base64" then
    if let some lim := maxBytes? then
      if f.content.utf8ByteSize > Qed.Base64.encodedLength lim then
        throw s!"source file `{f.path}` exceeds max size (> {lim} bytes)"
    match decodeBase64? f.content with
    | some bs => pure (onBin bs)
    | none    => throw s!"source file `{f.path}` has invalid base64 content"
  else throw s!"source file `{f.path}` has invalid encoding `{f.encoding}` (expected utf8 or base64)"

def SourceFile.decodedBytes (f : SourceFile) : Except String ByteArray :=
  f.withEncoding none String.toUTF8 id

json_obj_codec% SourceFile [path, content, encoding := "utf8"]

structure SourceBundle where
  files : Array SourceFile
deriving Inhabited, BEq, Repr

def SourceBundle.validate (b : SourceBundle) : Except String Unit := do
  if b.files.isEmpty then throw "source bundle cannot be empty"
  if b.files.size > maxSourceFiles then throw s!"source bundle has {b.files.size} files (max {maxSourceFiles})"
  let mut totalBytes : Nat := 0
  let mut seen : List String := []
  for f in b.files do
    if !isValidSourceRelPath f.path then throw s!"invalid source file path `{f.path}`"
    if seen.contains f.path then throw s!"duplicate source file path `{f.path}`"
    let sz ← f.withEncoding (some maxSourceFileBytes) String.utf8ByteSize ByteArray.size
    if sz > maxSourceFileBytes then throw s!"source file `{f.path}` exceeds max size ({sz} > {maxSourceFileBytes} bytes)"
    totalBytes := totalBytes + sz
    if totalBytes > maxTotalSourceBytes then throw s!"source bundle exceeds max total size ({maxTotalSourceBytes} bytes)"
    seen := f.path :: seen
  if !b.files.any (fun f => Qed.Str.endsWith f.path ".lean") then
    throw "source bundle must include at least one `.lean` file"

json_obj_codec% SourceBundle [files] validate SourceBundle.validate

structure DeployUploadReq where
  appSlug    : String
  env        : String := "prod"
  pr         : Nat := 0
  mod        : String := "App"
  deployName : String := ""
  bundle     : SourceBundle
deriving Inhabited, BEq, Repr

def DeployUploadReq.validate (r : DeployUploadReq) : Except String Unit := do
  if !isValidAppSlug r.appSlug then throw s!"invalid app slug `{r.appSlug}` (use 2-48 lowercase letters, digits, or single hyphens)"
  if !isValidEnvName r.env then throw s!"invalid env `{r.env}` (expected prod, staging, or preview)"
  if r.env == "preview" && r.pr == 0 then throw "preview deploy requires a positive PR number"
  if r.env != "preview" && r.pr != 0 then throw "PR number is only valid for preview deploys"
  if !isValidModuleName r.mod then throw s!"invalid root module `{r.mod}`"
  if !r.deployName.isEmpty && !isValidModuleName r.deployName then throw s!"invalid deploy spec name `{r.deployName}`"
  r.bundle.validate

json_obj_codec% DeployUploadReq [appSlug, env, pr, mod, deployName, bundle] validate DeployUploadReq.validate

structure DeployUploadResp where
  deploymentId : String
  appSlug      : String
  tenantId     : Nat
  appId        : Nat
  status       : String
  dashboardUrl : String
deriving Inhabited, BEq, Repr
json_obj_codec% DeployUploadResp [deploymentId, appSlug, tenantId, appId, status, dashboardUrl]

structure DeployLogEntry where
  seq     : Nat
  ts      : Nat
  level   : String
  message : String
deriving Inhabited, BEq, Repr
json_obj_codec% DeployLogEntry [seq, ts, level, message]

structure DeploymentView where
  id            : String
  appSlug       : String
  env           : String
  pr            : Nat
  status        : String
  url           : String
  buildHash     : String
  verifiedDecls : Nat
  errorMsg      : String
  createdAt     : Nat
  updatedAt     : Nat
  logs          : Array DeployLogEntry := #[]
deriving Inhabited, BEq, Repr
json_obj_codec% DeploymentView [id, appSlug, env, pr, status, url, buildHash, verifiedDecls, errorMsg, createdAt, updatedAt, logs]

structure AppSummary where
  slug        : String
  tenantId    : Nat
  appId       : Nat
  prodUrl     : String
  lastStatus  : String
  deployCount : Nat
  createdAt   : Nat
deriving Inhabited, BEq, Repr
json_obj_codec% AppSummary [slug, tenantId, appId, prodUrl, lastStatus, deployCount, createdAt]

structure AppsListResp where
  apps : Array AppSummary
deriving Inhabited, BEq, Repr
json_obj_codec% AppsListResp [apps]

structure SecretSetReq where
  appSlug : String
  env     : String := "prod"
  name    : String
  value   : String
deriving Inhabited, BEq, Repr

def SecretSetReq.validate (r : SecretSetReq) : Except String Unit := do
  validateSecretTarget r.appSlug r.env r.name
  if r.value.isEmpty || r.value.utf8ByteSize > 65536 then throw "secret value must be 1..65536 bytes"

json_obj_codec% SecretSetReq [appSlug, env, name, value] validate SecretSetReq.validate

structure SecretsListResp where
  appSlug : String
  names   : Array String
deriving Inhabited, BEq, Repr
json_obj_codec% SecretsListResp [appSlug, names]

structure SecretDeleteReq where
  appSlug : String
  env     : String := "prod"
  name    : String
deriving Inhabited, BEq, Repr

def SecretDeleteReq.validate (r : SecretDeleteReq) : Except String Unit :=
  validateSecretTarget r.appSlug r.env r.name

json_obj_codec% SecretDeleteReq [appSlug, env := "prod", name] validate SecretDeleteReq.validate

structure RollbackReq where
  appSlug      : String
  deploymentId : String
deriving Inhabited, BEq, Repr
json_obj_codec% RollbackReq [appSlug, deploymentId]

structure CancelDeployReq where
  deploymentId : String
deriving Inhabited, BEq, Repr

def CancelDeployReq.validate (r : CancelDeployReq) : Except String Unit := do
  if !isValidDeploymentId r.deploymentId then throw s!"invalid deployment id `{r.deploymentId}`"

json_obj_codec% CancelDeployReq [deploymentId] validate CancelDeployReq.validate

structure RuntimeLogView where
  id        : String
  timestamp : String
  severity  : String
  source    : String
  message   : String
deriving Inhabited, BEq, Repr
json_obj_codec% RuntimeLogView [id, timestamp, severity, source, message]

structure RuntimeLogsResp where
  appSlug       : String
  env           : String
  pr            : Nat := 0
  logs          : Array RuntimeLogView
  nextPageToken : Option String := none
deriving Inhabited, BEq, Repr
json_obj_codec% RuntimeLogsResp [appSlug, env, pr := 0, logs, nextPageToken]

structure TokenRevokeResp where
  revoked : Bool
deriving Inhabited, BEq, Repr
json_obj_codec% TokenRevokeResp [revoked]

end Qed.Cloud.Protocol
