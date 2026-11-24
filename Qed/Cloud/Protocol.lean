import Qed.Json
import Qed.Server.Net

/-! ## Hosted Qed Cloud Wire Protocol (`Qed.Cloud.Protocol`)
    Pure, verified JSON request/response types and input validators shared between
    the open-source `qed` CLI client and the hosted Qed Cloud control plane. -/

namespace Qed.Cloud.Protocol

open Qed Qed.Server.Net

/-! ### 1. Bounds & Input Validators -/

def maxSourceFiles      : Nat := 500
def maxSourceFileBytes  : Nat := 1024 * 1024
def maxTotalSourceBytes : Nat := 8 * 1024 * 1024

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
  ["queued", "verifying", "building", "deploying", "live", "failed"].contains s

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
  [".git", ".lake", ".qed", "dist", "node_modules", "target", ".claude", ".gemini"]

private def isAllowedSourceExt (seg : String) : Bool :=
  seg == "lean-toolchain" || seg == "lakefile.lean" || seg == "lakefile.toml" ||
  seg == "lake-manifest.json" || seg == "qed.json" ||
  seg.endsWith ".lean" || seg.endsWith ".css"

def isValidSourceRelPath (p : String) : Bool :=
  !p.isEmpty && p.length ≤ 240 && !p.startsWith "/" && !p.endsWith "/" &&
  !p.toList.any (fun c => c.toNat < 0x20 || c.toNat == 0x7F || c == '\\' || c == '?' || c == '#' || c == ':') &&
  let segs := p.splitOn "/"
  !segs.isEmpty &&
  segs.all (fun seg => !seg.isEmpty && seg != "." && seg != ".." && !seg.startsWith ".env" && !forbiddenSourceTopDirs.contains seg) &&
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
  path    : String
  content : String
deriving Inhabited, DecidableEq, Repr

instance : ToJson SourceFile where
  toJson f := .obj [("path", .str f.path), ("content", .str f.content)]

instance : FromJson SourceFile where
  fromJson j := return { path := ← fromField j "path", content := ← fromField j "content" }

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
    let sz := f.content.utf8ByteSize
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

structure RollbackReq where
  appSlug      : String
  deploymentId : String
deriving Inhabited, DecidableEq, Repr

instance : ToJson RollbackReq where
  toJson r := .obj [("appSlug", .str r.appSlug), ("deploymentId", .str r.deploymentId)]

instance : FromJson RollbackReq where
  fromJson j := return { appSlug := ← fromField j "appSlug", deploymentId := ← fromField j "deploymentId" }

#guard isValidAppSlug "my-app-1" && !isValidAppSlug "A" && !isValidAppSlug "my--app" && !isValidAppSlug "-bad"
#guard isValidSourceRelPath "App.lean" && isValidSourceRelPath "styles/main.css" && isValidSourceRelPath "lean-toolchain"
#guard !isValidSourceRelPath "../secret.lean" && !isValidSourceRelPath ".env.prod" && !isValidSourceRelPath ".lake/a.lean" && !isValidSourceRelPath "/etc/passwd"
#guard isValidCloudApiUrl "http://127.0.0.1:8080" && isValidCloudApiUrl "https://qed-cloud-abc-uc.a.run.app" && !isValidCloudApiUrl "http://example.com" && !isValidCloudApiUrl "https://a.run.app/path"
#guard isValidDeviceUserCode "ABCD-2345" && !isValidDeviceUserCode "abcd-2345" && !isValidDeviceUserCode "ABCD2345"

end Qed.Cloud.Protocol
