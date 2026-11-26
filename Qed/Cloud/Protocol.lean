import Qed.Base64
import Qed.Json
import Qed.Server.Net

/-! ## Hosted Qed Cloud Wire Protocol (`Qed.Cloud.Protocol`)
    Pure, verified JSON request/response types and input validators shared between
    the open-source `qed` CLI client and the hosted Qed Cloud control plane. -/

namespace Qed.Cloud.Protocol

open Qed Qed.Server.Net

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
      cs.getLastD '-' != '-' && !s.contains "--"
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
  let lower := seg.toLower
  exts.any fun ext => lower.length > ext.length && lower.endsWith ext

def isBinarySourceExt (p : String) : Bool :=
  let seg := (p.splitOn "/").getLastD p
  !seg.startsWith "." && hasExtIn binarySourceExts seg

private def isAllowedSourceExt (seg : String) : Bool :=
  allowedSourceExactNames.contains seg || hasExtIn textSourceExts seg || hasExtIn binarySourceExts seg

def isValidSourceRelPath (p : String) : Bool :=
  !p.isEmpty && p.length ≤ 240 && !p.startsWith "/" && !p.endsWith "/" &&
  !p.toList.any (fun c => c.toNat < 0x20 || c.toNat == 0x7F || c == '\\' || c == '?' || c == '#' || c == ':') &&
  let segs := p.splitOn "/"
  !segs.isEmpty &&
  segs.all (fun seg => !seg.isEmpty && !seg.startsWith "." && !forbiddenSourceTopDirs.contains seg.toLower) &&
  isAllowedSourceExt (segs.getLastD "")

def normalizeApiBase (raw : String) : String :=
  let t := raw.trimAscii.toString
  if t.endsWith "/" then (t.dropEnd 1).toString else t

/-- Hosted Qed Cloud API base must be either `https://<valid-host>[:port]` (for Cloud Run `*.a.run.app`
    or custom domain) or a strict loopback HTTP URL (`http://127.0.0.1[:port]` / `http://localhost[:port]`)
    for local development. Rejects paths, queries, fragments, credentials, and control chars. -/
def isValidCloudApiUrl (raw : String) : Bool :=
  let u := normalizeApiBase raw
  if u.isEmpty || u.toList.any (fun c => c.isWhitespace || c.toNat < 0x20 || c.toNat == 0x7F || "@\\?#".contains c) then false
  else if u.startsWith "http://" then isStrictLoopbackUrl u
  else if u.startsWith "https://" then
    let auth := (u.drop 8).toString
    !auth.isEmpty && !auth.contains "/" &&
    match auth.splitOn ":" with
    | [h] => isValidHostname h.toLower
    | [h, pStr] =>
        match pStr.toNat? with
        | some p => 1 ≤ p && p ≤ 65535 && toString p == pStr && isValidHostname h.toLower
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
deriving Inhabited, DecidableEq, Repr

instance : ToJson DeviceStartResp where
  toJson r := .obj [
    ("deviceCode", .str r.deviceCode), ("userCode", .str r.userCode),
    ("verifyUrl", .str r.verifyUrl), ("expiresInSec", toJson r.expiresInSec),
    ("intervalSec", toJson r.intervalSec)]

instance : FromJson DeviceStartResp where
  fromJson j := do
    return {
      deviceCode := ← fromField j "deviceCode", userCode := ← fromField j "userCode",
      verifyUrl := ← fromField j "verifyUrl", expiresInSec := ← fromField j "expiresInSec",
      intervalSec := ← fromField j "intervalSec" }

structure DevicePollReq where
  deviceCode : String
deriving Inhabited, DecidableEq, Repr

instance : ToJson DevicePollReq where
  toJson r := .obj [("deviceCode", .str r.deviceCode)]

instance : FromJson DevicePollReq where
  fromJson j := return { deviceCode := ← fromField j "deviceCode" }

structure DevicePollResp where
  status : String
  token  : Option String := none
  userId : Option String := none
  email  : Option String := none
deriving Inhabited, DecidableEq, Repr

instance : ToJson DevicePollResp where
  toJson r := .obj [
    ("status", .str r.status), ("token", toJson r.token),
    ("userId", toJson r.userId), ("email", toJson r.email)]

instance : FromJson DevicePollResp where
  fromJson j := do
    return {
      status := ← fromField j "status", token := ← fromField j "token",
      userId := ← fromField j "userId", email := ← fromField j "email" }

structure WhoamiResp where
  userId    : String
  email     : String
  tenantId  : Nat
  appsCount : Nat
deriving Inhabited, DecidableEq, Repr

instance : ToJson WhoamiResp where
  toJson r := .obj [
    ("userId", .str r.userId), ("email", .str r.email),
    ("tenantId", toJson r.tenantId), ("appsCount", toJson r.appsCount)]

instance : FromJson WhoamiResp where
  fromJson j := do
    return {
      userId := ← fromField j "userId", email := ← fromField j "email",
      tenantId := ← fromField j "tenantId", appsCount := ← fromField j "appsCount" }

/-! ### 3. Source Bundle & Deployment Protocol -/

structure SourceFile where
  path     : String
  content  : String
  encoding : String := "utf8"
deriving Inhabited, DecidableEq, Repr

def SourceFile.decodedBytes (f : SourceFile) : Except String ByteArray :=
  if f.encoding == "utf8" then .ok f.content.toUTF8
  else if f.encoding == "base64" then
    match decodeBase64? f.content with
    | some bs => .ok bs
    | none    => .error s!"source file `{f.path}` has invalid base64 content"
  else
    .error s!"source file `{f.path}` has invalid encoding `{f.encoding}` (expected utf8 or base64)"

instance : ToJson SourceFile where
  toJson f := .obj [("path", .str f.path), ("content", .str f.content), ("encoding", .str f.encoding)]

instance : FromJson SourceFile where
  fromJson j := do
    let enc? : Option String ← fromField j "encoding"
    return { path := ← fromField j "path", content := ← fromField j "content", encoding := enc?.getD "utf8" }

structure SourceBundle where
  files : Array SourceFile
deriving Inhabited, DecidableEq, Repr

def SourceBundle.validate (b : SourceBundle) : Except String Unit := do
  if b.files.isEmpty then throw "source bundle cannot be empty"
  if b.files.size > maxSourceFiles then throw s!"source bundle has {b.files.size} files (max {maxSourceFiles})"
  let mut totalBytes : Nat := 0
  let mut seen : List String := []
  for f in b.files do
    if !isValidSourceRelPath f.path then throw s!"invalid source file path `{f.path}`"
    if seen.contains f.path then throw s!"duplicate source file path `{f.path}`"
    let sz ←
      if f.encoding == "utf8" then
        pure f.content.utf8ByteSize
      else if f.encoding == "base64" then
        if f.content.utf8ByteSize > Qed.Base64.encodedLength maxSourceFileBytes then
          throw s!"source file `{f.path}` exceeds max size (> {maxSourceFileBytes} bytes)"
        match decodeBase64? f.content with
        | some bs => pure bs.size
        | none    => throw s!"source file `{f.path}` has invalid base64 content"
      else
        throw s!"source file `{f.path}` has invalid encoding `{f.encoding}` (expected utf8 or base64)"
    if sz > maxSourceFileBytes then throw s!"source file `{f.path}` exceeds max size ({sz} > {maxSourceFileBytes} bytes)"
    totalBytes := totalBytes + sz
    if totalBytes > maxTotalSourceBytes then throw s!"source bundle exceeds max total size ({maxTotalSourceBytes} bytes)"
    seen := f.path :: seen
  if !b.files.any (fun f => f.path.endsWith ".lean") then
    throw "source bundle must include at least one `.lean` file"

instance : ToJson SourceBundle where
  toJson b := .obj [("files", toJson b.files)]

instance : FromJson SourceBundle where
  fromJson j := do
    let files : Array SourceFile ← fromField j "files"
    let b : SourceBundle := { files }
    b.validate
    return b

structure DeployUploadReq where
  appSlug    : String
  env        : String := "prod"
  pr         : Nat := 0
  mod        : String := "App"
  deployName : String := ""
  bundle     : SourceBundle
deriving Inhabited, DecidableEq, Repr

def DeployUploadReq.validate (r : DeployUploadReq) : Except String Unit := do
  if !isValidAppSlug r.appSlug then throw s!"invalid app slug `{r.appSlug}` (use 2-48 lowercase letters, digits, or single hyphens)"
  if !isValidEnvName r.env then throw s!"invalid env `{r.env}` (expected prod, staging, or preview)"
  if r.env == "preview" && r.pr == 0 then throw "preview deploy requires a positive PR number"
  if r.env != "preview" && r.pr != 0 then throw "PR number is only valid for preview deploys"
  if r.mod.isEmpty || r.mod.length > 128 || !r.mod.toList.all (fun c => c.isAlphanum || c == '.' || c == '_') then
    throw s!"invalid root module `{r.mod}`"
  if !r.deployName.isEmpty && (r.deployName.length > 128 || !r.deployName.toList.all (fun c => c.isAlphanum || c == '.' || c == '_')) then
    throw s!"invalid deploy spec name `{r.deployName}`"
  r.bundle.validate

instance : ToJson DeployUploadReq where
  toJson r := .obj [
    ("appSlug", .str r.appSlug), ("env", .str r.env), ("pr", toJson r.pr),
    ("mod", .str r.mod), ("deployName", .str r.deployName), ("bundle", toJson r.bundle)]

instance : FromJson DeployUploadReq where
  fromJson j := do
    let r : DeployUploadReq := {
      appSlug := ← fromField j "appSlug", env := ← fromField j "env", pr := ← fromField j "pr",
      mod := ← fromField j "mod", deployName := ← fromField j "deployName", bundle := ← fromField j "bundle" }
    r.validate
    return r

structure DeployUploadResp where
  deploymentId : String
  appSlug      : String
  tenantId     : Nat
  appId        : Nat
  status       : String
  dashboardUrl : String
deriving Inhabited, DecidableEq, Repr

instance : ToJson DeployUploadResp where
  toJson r := .obj [
    ("deploymentId", .str r.deploymentId), ("appSlug", .str r.appSlug),
    ("tenantId", toJson r.tenantId), ("appId", toJson r.appId),
    ("status", .str r.status), ("dashboardUrl", .str r.dashboardUrl)]

instance : FromJson DeployUploadResp where
  fromJson j := do
    return {
      deploymentId := ← fromField j "deploymentId", appSlug := ← fromField j "appSlug",
      tenantId := ← fromField j "tenantId", appId := ← fromField j "appId",
      status := ← fromField j "status", dashboardUrl := ← fromField j "dashboardUrl" }

structure DeployLogEntry where
  seq     : Nat
  ts      : Nat
  level   : String
  message : String
deriving Inhabited, DecidableEq, Repr

instance : ToJson DeployLogEntry where
  toJson e := .obj [
    ("seq", toJson e.seq), ("ts", toJson e.ts),
    ("level", .str e.level), ("message", .str e.message)]

instance : FromJson DeployLogEntry where
  fromJson j := do
    return {
      seq := ← fromField j "seq", ts := ← fromField j "ts",
      level := ← fromField j "level", message := ← fromField j "message" }

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
deriving Inhabited, DecidableEq, Repr

instance : ToJson DeploymentView where
  toJson d := .obj [
    ("id", .str d.id), ("appSlug", .str d.appSlug), ("env", .str d.env), ("pr", toJson d.pr),
    ("status", .str d.status), ("url", .str d.url), ("buildHash", .str d.buildHash),
    ("verifiedDecls", toJson d.verifiedDecls), ("errorMsg", .str d.errorMsg),
    ("createdAt", toJson d.createdAt), ("updatedAt", toJson d.updatedAt), ("logs", toJson d.logs)]

instance : FromJson DeploymentView where
  fromJson j := do
    return {
      id := ← fromField j "id", appSlug := ← fromField j "appSlug", env := ← fromField j "env",
      pr := ← fromField j "pr", status := ← fromField j "status", url := ← fromField j "url",
      buildHash := ← fromField j "buildHash", verifiedDecls := ← fromField j "verifiedDecls",
      errorMsg := ← fromField j "errorMsg", createdAt := ← fromField j "createdAt",
      updatedAt := ← fromField j "updatedAt", logs := ← fromField j "logs" }

structure AppSummary where
  slug        : String
  tenantId    : Nat
  appId       : Nat
  prodUrl     : String
  lastStatus  : String
  deployCount : Nat
  createdAt   : Nat
deriving Inhabited, DecidableEq, Repr

instance : ToJson AppSummary where
  toJson a := .obj [
    ("slug", .str a.slug), ("tenantId", toJson a.tenantId), ("appId", toJson a.appId),
    ("prodUrl", .str a.prodUrl), ("lastStatus", .str a.lastStatus),
    ("deployCount", toJson a.deployCount), ("createdAt", toJson a.createdAt)]

instance : FromJson AppSummary where
  fromJson j := do
    return {
      slug := ← fromField j "slug", tenantId := ← fromField j "tenantId", appId := ← fromField j "appId",
      prodUrl := ← fromField j "prodUrl", lastStatus := ← fromField j "lastStatus",
      deployCount := ← fromField j "deployCount", createdAt := ← fromField j "createdAt" }

structure AppsListResp where
  apps : Array AppSummary
deriving Inhabited, DecidableEq, Repr

instance : ToJson AppsListResp where
  toJson r := .obj [("apps", toJson r.apps)]

instance : FromJson AppsListResp where
  fromJson j := return { apps := ← fromField j "apps" }

structure SecretSetReq where
  appSlug : String
  env     : String := "prod"
  name    : String
  value   : String
deriving Inhabited, DecidableEq, Repr

def SecretSetReq.validate (r : SecretSetReq) : Except String Unit := do
  if !isValidAppSlug r.appSlug then throw s!"invalid app slug `{r.appSlug}`"
  if !isValidEnvName r.env then throw s!"invalid env `{r.env}`"
  if !isValidSecretKey r.name then throw s!"invalid secret name `{r.name}` (use UPPER_SNAKE_CASE)"
  if r.value.isEmpty || r.value.utf8ByteSize > 65536 then throw "secret value must be 1..65536 bytes"

instance : ToJson SecretSetReq where
  toJson r := .obj [("appSlug", .str r.appSlug), ("env", .str r.env), ("name", .str r.name), ("value", .str r.value)]

instance : FromJson SecretSetReq where
  fromJson j := do
    let r : SecretSetReq := {
      appSlug := ← fromField j "appSlug", env := ← fromField j "env",
      name := ← fromField j "name", value := ← fromField j "value" }
    r.validate
    return r

structure SecretsListResp where
  appSlug : String
  names   : Array String
deriving Inhabited, DecidableEq, Repr

instance : ToJson SecretsListResp where
  toJson r := .obj [("appSlug", .str r.appSlug), ("names", toJson r.names)]

instance : FromJson SecretsListResp where
  fromJson j := return { appSlug := ← fromField j "appSlug", names := ← fromField j "names" }

structure SecretDeleteReq where
  appSlug : String
  env     : String := "prod"
  name    : String
deriving Inhabited, DecidableEq, Repr

def SecretDeleteReq.validate (r : SecretDeleteReq) : Except String Unit := do
  if !isValidAppSlug r.appSlug then throw s!"invalid app slug `{r.appSlug}`"
  if !isValidEnvName r.env then throw s!"invalid env `{r.env}`"
  if !isValidSecretKey r.name then throw s!"invalid secret name `{r.name}` (use UPPER_SNAKE_CASE)"

instance : ToJson SecretDeleteReq where
  toJson r := .obj [("appSlug", .str r.appSlug), ("env", .str r.env), ("name", .str r.name)]

instance : FromJson SecretDeleteReq where
  fromJson j := do
    let env? : Option String ← fromField j "env"
    let r : SecretDeleteReq := {
      appSlug := ← fromField j "appSlug",
      env := env?.getD "prod",
      name := ← fromField j "name" }
    r.validate
    return r

structure RollbackReq where
  appSlug      : String
  deploymentId : String
deriving Inhabited, DecidableEq, Repr

instance : ToJson RollbackReq where
  toJson r := .obj [("appSlug", .str r.appSlug), ("deploymentId", .str r.deploymentId)]

instance : FromJson RollbackReq where
  fromJson j := return { appSlug := ← fromField j "appSlug", deploymentId := ← fromField j "deploymentId" }

structure CancelDeployReq where
  deploymentId : String
deriving Inhabited, DecidableEq, Repr

def CancelDeployReq.validate (r : CancelDeployReq) : Except String Unit := do
  if !isValidDeploymentId r.deploymentId then throw s!"invalid deployment id `{r.deploymentId}`"

instance : ToJson CancelDeployReq where
  toJson r := .obj [("deploymentId", .str r.deploymentId)]

instance : FromJson CancelDeployReq where
  fromJson j := do
    let r : CancelDeployReq := { deploymentId := ← fromField j "deploymentId" }
    r.validate
    return r

structure RuntimeLogView where
  id        : String
  timestamp : String
  severity  : String
  source    : String
  message   : String
deriving Inhabited, DecidableEq, Repr

instance : ToJson RuntimeLogView where
  toJson e := .obj [
    ("id", .str e.id), ("timestamp", .str e.timestamp),
    ("severity", .str e.severity), ("source", .str e.source),
    ("message", .str e.message)]

instance : FromJson RuntimeLogView where
  fromJson j := do
    return {
      id := ← fromField j "id", timestamp := ← fromField j "timestamp",
      severity := ← fromField j "severity", source := ← fromField j "source",
      message := ← fromField j "message" }

structure RuntimeLogsResp where
  appSlug       : String
  env           : String
  pr            : Nat := 0
  logs          : Array RuntimeLogView
  nextPageToken : Option String := none
deriving Inhabited, DecidableEq, Repr

instance : ToJson RuntimeLogsResp where
  toJson r := .obj [
    ("appSlug", .str r.appSlug), ("env", .str r.env), ("pr", toJson r.pr),
    ("logs", toJson r.logs), ("nextPageToken", toJson r.nextPageToken)]

instance : FromJson RuntimeLogsResp where
  fromJson j := do
    let pr? : Option Nat ← fromField j "pr"
    return {
      appSlug := ← fromField j "appSlug", env := ← fromField j "env",
      pr := pr?.getD 0, logs := ← fromField j "logs",
      nextPageToken := ← fromField j "nextPageToken" }

structure TokenRevokeResp where
  revoked : Bool
deriving Inhabited, DecidableEq, Repr

instance : ToJson TokenRevokeResp where
  toJson r := .obj [("revoked", .bool r.revoked)]

instance : FromJson TokenRevokeResp where
  fromJson j := return { revoked := ← fromField j "revoked" }

#guard isValidAppSlug "my-app-1" && !isValidAppSlug "A" && !isValidAppSlug "my--app" && !isValidAppSlug "-bad"
#guard isValidDeploymentId "dep_abc-1" && isValidDeploymentId "0123" && !isValidDeploymentId "" && !isValidDeploymentId "-bad" && !isValidDeploymentId "--help" && !isValidDeploymentId "_bad"
#guard isValidDeployStatus "live" && isValidDeployStatus "canceled" && !isValidDeployStatus "unknown"
#guard
  ["App.lean", "styles/main.css", "lean-toolchain", "lakefile.lean", "lakefile.toml", "lake-manifest.json",
   "qed.json", "robots.txt", "sitemap.xml", "manifest.json", "public/logo.png", "public/hero.jpg",
   "public/photo.jpeg", "public/anim.gif", "public/icon.svg", "public/img.webp", "public/favicon.ico",
   "fonts/inter.woff", "fonts/inter.woff2", "fonts/inter.ttf", "fonts/inter.otf", "public/data.json",
   "public/notes.txt", "public/feed.xml", "public/site.webmanifest", "public/index.html",
   "public/app.js", "public/mod.mjs"].all isValidSourceRelPath
#guard
  ["../secret.lean", "../logo.png", ".env", ".env.prod", ".env.json", ".ENV.txt",
   ".git/config.txt", ".lake/a.lean", ".qed/cache.json", ".config/qed/credentials.json",
   ".docker/config.json", ".ssh/id_rsa.txt", ".htaccess.txt", "..png", ".a.png",
   "dist/app.mjs", "node_modules/pkg/index.js", "target/out.txt", "/etc/passwd", "public/a\\b.png",
   "public/a.png?v=1", "public/a.png#frag", "public/a:b.png", "public/a\nb.png", ".png", "public/.png", ".json"].all (!isValidSourceRelPath ·)
#guard isBinarySourceExt "public/logo.png" && !isBinarySourceExt "public/.png" && !isBinarySourceExt "public/.a.png" && !isBinarySourceExt ".png"
#guard
  [ByteArray.empty, ByteArray.mk #[0], ByteArray.mk #[0, 1], ByteArray.mk #[0, 1, 2],
   ByteArray.mk #[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0xFF]].all fun bs =>
    (decodeBase64? (encodeBase64 bs)).map (·.data) == some bs.data
#guard
  ["abc", "ab!d", "AA==AAAA", "AB==", "AP==", "AAB=", "///=", "//=="].all fun s => (decodeBase64? s).isNone
#guard isValidCloudApiUrl "http://127.0.0.1:8080" && isValidCloudApiUrl "https://api.qed.cloud" && isValidCloudApiUrl "https://qed-cloud-abc-uc.a.run.app" && !isValidCloudApiUrl "http://example.com" && !isValidCloudApiUrl "https://a.run.app/path"
#guard isValidDeviceUserCode "ABCD-2345" && !isValidDeviceUserCode "abcd-2345" && !isValidDeviceUserCode "ABCD2345"

end Qed.Cloud.Protocol
