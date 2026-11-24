import Cli.Common
import Qed.Cloud.Protocol
import Qed.Server.Native

open System (FilePath)
open Qed Qed.Cloud Qed.Cloud.Protocol Qed.Server.Net Qed.Server.Native

namespace Qed.Cli

/-! ## Hosted Qed Cloud CLI Client (`Cli.Cloud`)
    Handles `qed login`, `qed logout`, `qed whoami`, `qed status`, `qed logs`,
    `qed secrets`, `qed rollback`, and hosted `qed deploy`. -/

/-- Default hosted Qed Cloud control plane URL (override with `--api` or `QED_CLOUD_API`). -/
def defaultCloudApiUrl? : Option String := some "https://qed-cloud-gxm6ngh3xq-uc.a.run.app"

structure CloudCredentials where
  apiBase : String
  token   : String
  userId  : String
  email   : String
deriving Inhabited, DecidableEq, Repr

instance : ToJson CloudCredentials where
  toJson c := .obj [
    ("apiBase", .str c.apiBase), ("token", .str c.token),
    ("userId", .str c.userId), ("email", .str c.email)]

instance : FromJson CloudCredentials where
  fromJson j := do
    return {
      apiBase := ← fromField j "apiBase", token := ← fromField j "token",
      userId := ← fromField j "userId", email := ← fromField j "email" }

private def credentialsPath : IO FilePath := do
  if let some p ← nonEmptyEnv "QED_CREDENTIALS_FILE" then return FilePath.mk p
  let home := (← nonEmptyEnv "HOME").getD "."
  return FilePath.mk home / ".config" / "qed" / "credentials.json"

private def loadCredentials? : IO (Option CloudCredentials) := do
  let p ← credentialsPath
  if !(← p.pathExists) then return none
  match ← symlinkType? p with
  | some .file =>
      let raw ← try IO.FS.readFile p catch _ => return none
      return (Json.parse raw.cliTrim >>= fromJson).toOption
  | _ => return none

private def saveCredentials (c : CloudCredentials) : ExceptT String IO Unit := do
  let p ← liftIO credentialsPath
  if let some dir := p.parent then
    IO.FS.createDirAll dir
    discard <| liftIO (shQuiet "chmod" #["700", dir.toString])
  if let some ty ← liftIO (symlinkType? p) then
    if ty != .file then throw s!"refusing to overwrite symlink or non-regular credentials file `{p}`"
  IO.FS.writeFile p ((toJson c).render ++ "\n")
  discard <| liftIO (shQuiet "chmod" #["600", p.toString])

private def resolveApiBase (flagApi? : Option String) (creds? : Option CloudCredentials) : ExceptT String IO String := do
  let envApi? ← liftIO (nonEmptyEnv "QED_CLOUD_API")
  let raw? := flagApi?.orElse (fun _ => envApi?) |>.orElse (fun _ => creds?.map (·.apiBase)) |>.orElse (fun _ => defaultCloudApiUrl?)
  match raw? with
  | none =>
      throw "missing Qed Cloud API URL: pass `--api <url>` (e.g. `https://<service>.a.run.app` or `http://127.0.0.1:8080`) or set `QED_CLOUD_API`"
  | some raw =>
      let u := normalizeApiBase raw
      if !isValidCloudApiUrl u then
        throw s!"invalid Qed Cloud API URL `{raw}` (must be `https://<host>[:port]` or local loopback `http://127.0.0.1[:port]`)"
      return u

private def requireAuthFor (apiBase : String) : ExceptT String IO CloudCredentials := do
  let some creds ← liftIO loadCredentials?
    | throw s!"not logged in to Qed Cloud. Run: qed login --api {apiBase}"
  if normalizeApiBase creds.apiBase != apiBase then
    throw s!"stored credentials are for `{creds.apiBase}`, not `{apiBase}` (refusing to send token to another host; run `qed login --api {apiBase}`)"
  if creds.token.isEmpty then throw "stored credentials have an empty token; run `qed login` again"
  return creds

private def cloudHttpJson {α : Type} [FromJson α] (apiBase method path : String)
    (token? : Option String) (body? : Option Json := none) : ExceptT String IO α := do
  let isLocal := isStrictLoopbackUrl apiBase
  let url := apiBase ++ path
  let mut hdrs : Array (String × String) := #[("Accept", "application/json")]
  if let some tok := token? then hdrs := hdrs.push ("Authorization", s!"Bearer {tok}")
  let bodyBytes : ByteArray := match body? with
    | some j => j.render.toUTF8
    | none   => ByteArray.empty
  if body?.isSome then hdrs := hdrs.push ("Content-Type", "application/json")
  let (status, respBody, _) ← match ← liftIO (execHttpCall method url hdrs bodyBytes (ssrfGuard := !isLocal)) with
    | .ok r    => pure r
    | .error e => throw s!"cannot reach Qed Cloud at `{apiBase}`: {e}"
  let txt := (String.fromUTF8? respBody).getD ""
  if status < 200 || status >= 300 then
    let detail := match Json.parse txt.cliTrim with
      | .ok j => (j.strAt? "error").orElse (fun _ => j.strAt? "message") |>.getD txt.cliTrim
      | .error _ => txt.cliTrim
    throw s!"Qed Cloud API error (HTTP {status}): {if detail.isEmpty then "request failed" else detail}"
  match Json.parse txt.cliTrim with
  | .error e => throw s!"invalid JSON response from Qed Cloud `{path}`: {e}"
  | .ok j    => match (fromJson j : Except String α) with
      | .ok v    => return v
      | .error e => throw s!"unexpected Qed Cloud response for `{path}`: {e}"

private def sanitizeSlugFromDir (dirName : String) : String :=
  let raw := String.ofList <| dirName.toLower.toList.map fun c =>
    if ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') then c else '-'
  let parts := (raw.splitOn "-").filter (!·.isEmpty)
  let joined := "-".intercalate parts
  let clipped := (joined.take 48).toString
  let trimmed := if clipped.endsWith "-" then (clipped.dropEnd 1).toString else clipped
  if isValidAppSlug trimmed then trimmed else "qed-app"

private def defaultAppSlug : IO String := do
  let cwd ← IO.currentDir
  return sanitizeSlugFromDir (cwd.fileName.getD "qed-app")

private def collectSourceFilesLoop (rootReal : FilePath) (rootPfx : String) :
    Nat → List (FilePath × String) → Array SourceFile → Nat → ExceptT String IO SourceBundle
  | 0, _, _, _ => throw "source directory traversal exceeded depth/file budget"
  | _, [], acc, _ => do
      let b : SourceBundle := { files := acc }
      match b.validate with
      | .ok ()   => return b
      | .error e => throw e
  | fuel + 1, (dir, relPfx) :: rest, acc, totalBytes => do
      let entries ← liftIO (dir.readDir)
      let sorted := entries.qsort (fun a b => a.fileName < b.fileName)
      let mut nextDirs := rest
      let mut nextAcc := acc
      let mut nextBytes := totalBytes
      for e in sorted do
        let name := e.fileName
        if name.startsWith "." || ["dist", "node_modules", "target"].contains name then continue
        let full := dir / name
        let some ty ← liftIO (symlinkType? full) | continue
        if ty == .symlink then continue
        let some rp ← liftIO (realPath? full) | continue
        if !rp.toString.startsWith rootPfx then continue
        let rel := if relPfx.isEmpty then name else s!"{relPfx}/{name}"
        if ty == .dir then
          nextDirs := (full, rel) :: nextDirs
        else if ty == .file && isValidSourceRelPath rel then
          if nextAcc.size >= maxSourceFiles then
            throw s!"project exceeds maximum of {maxSourceFiles} source files"
          let bytes ← liftIO (IO.FS.readBinFile full)
          if bytes.size > maxSourceFileBytes then
            throw s!"source file `{rel}` exceeds {maxSourceFileBytes} bytes"
          nextBytes := nextBytes + bytes.size
          if nextBytes > maxTotalSourceBytes then
            throw s!"project source exceeds {maxTotalSourceBytes} bytes"
          let some content := String.fromUTF8? bytes
            | throw s!"source file `{rel}` is not valid UTF-8"
          nextAcc := nextAcc.push { path := rel, content }
      collectSourceFilesLoop rootReal rootPfx fuel nextDirs nextAcc nextBytes

def collectSourceBundle (rootDir : FilePath) : ExceptT String IO SourceBundle := do
  let some rootReal ← liftIO (realPath? rootDir) | throw s!"project directory not found: `{rootDir}`"
  collectSourceFilesLoop rootReal (dirPrefix rootReal) 2000 [(rootReal, "")] #[] 0

/-! ### CLI Commands: `login`, `logout`, `whoami`, `status`, `logs`, `secrets`, `rollback`, hosted `deploy` -/

private def parseApiFlag : List String → Option String × List String
  | "--api" :: u :: r => let (_, rest) := parseApiFlag r; (some u, rest)
  | x :: r            => let (u?, rest) := parseApiFlag r; (u?, x :: rest)
  | []                => (none, [])

private def pollDeviceLoop (apiBase deviceCode : String) (intervalMs : UInt32) : Nat → ExceptT String IO DevicePollResp
  | 0 => throw "login timed out waiting for browser approval"
  | fuel + 1 => do
      let r : DevicePollResp ← cloudHttpJson apiBase "POST" "/api/v1/cli/device/poll" none (some (toJson ({ deviceCode } : DevicePollReq)))
      if r.status == "approved" then return r
      if r.status == "expired" then throw "device login code expired; run `qed login` again"
      liftIO (IO.sleep intervalMs)
      pollDeviceLoop apiBase deviceCode intervalMs fuel

private def runLogin (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, rest) := parseApiFlag args
  let noOpen := rest.contains "--no-open"
  for f in rest do if f != "--no-open" then throw s!"unknown `qed login` flag: `{f}`"
  let creds? ← liftIO loadCredentials?
  let apiBase ← resolveApiBase flagApi? creds?
  liftIO (step s!"starting Qed Cloud login at {apiBase}")
  let start : DeviceStartResp ← cloudHttpJson apiBase "POST" "/api/v1/cli/device" none (some (.obj []))
  liftIO <| IO.println ""
  liftIO <| IO.println s!"  Confirmation code: {bold start.userCode}"
  liftIO <| IO.println s!"  Approve in browser: {start.verifyUrl}"
  liftIO <| IO.println ""
  liftIO <| (← IO.getStdout).flush
  if !noOpen then
    let opener := if System.Platform.isOSX then "open" else "xdg-open"
    if ← liftIO (onPath opener) then
      discard <| liftIO (IO.Process.spawn { cmd := opener, args := #[start.verifyUrl], stdin := .null, stdout := .null, stderr := .null })
  liftIO (step "waiting for browser approval...")
  let intervalSec := max 1 (min 10 start.intervalSec)
  let maxPolls := max 10 (min 300 (start.expiresInSec / intervalSec))
  let poll ← pollDeviceLoop apiBase start.deviceCode (intervalSec.toUInt32 * 1000) maxPolls
  let some tok := poll.token | throw "control plane approved login without issuing a token"
  let userId := poll.userId.getD "user"
  let email := poll.email.getD userId
  saveCredentials { apiBase, token := tok, userId, email }
  liftIO (IO.println (green s!"✓ logged in as {email} ({apiBase})"))
  return 0

def cmdLogin (args : List String) : IO UInt32 := do
  match ← (runLogin args).run with | .ok c => return c | .error e => IO.eprintln (red s!"✗ {e}"); return 1

def cmdLogout : IO UInt32 := do
  let p ← credentialsPath
  if ← p.pathExists then
    removeIfExists p
    IO.println (green "✓ logged out of Qed Cloud")
  else
    IO.println "already logged out"
  return 0

private def runWhoami (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, rest) := parseApiFlag args
  if !rest.isEmpty then throw s!"unexpected arguments to `qed whoami`: {" ".intercalate rest}"
  let apiBase ← resolveApiBase flagApi? (← liftIO loadCredentials?)
  let creds ← requireAuthFor apiBase
  let me : WhoamiResp ← cloudHttpJson apiBase "GET" "/api/v1/whoami" (some creds.token)
  liftIO <| IO.println s!"{green "✓"} {me.email} (id={me.userId}, tenant={me.tenantId}, apps={me.appsCount}) @ {apiBase}"
  return 0

def cmdWhoami (args : List String) : IO UInt32 := do
  match ← (runWhoami args).run with | .ok c => return c | .error e => IO.eprintln (red s!"✗ {e}"); return 1

private def runStatus (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, rest) := parseApiFlag args
  let filterSlug? := rest.head?
  let apiBase ← resolveApiBase flagApi? (← liftIO loadCredentials?)
  let creds ← requireAuthFor apiBase
  let resp : AppsListResp ← cloudHttpJson apiBase "GET" "/api/v1/apps" (some creds.token)
  let apps : Array AppSummary := match filterSlug? with
    | some s => resp.apps.filter (fun (a : AppSummary) => a.slug == s)
    | none   => resp.apps
  if apps.isEmpty then
    liftIO <| IO.println (match filterSlug? with | some s => s!"no app named `{s}`" | none => "no deployed apps yet. Run `qed deploy` in a Qed project.")
    return 0
  for a in apps do
    let urlTxt := if a.prodUrl.isEmpty then "(no live URL yet)" else a.prodUrl
    liftIO <| IO.println s!"  {bold a.slug}  [{a.lastStatus}]  deploys={a.deployCount}  {urlTxt}"
  return 0

def cmdStatus (args : List String) : IO UInt32 := do
  match ← (runStatus args).run with | .ok c => return c | .error e => IO.eprintln (red s!"✗ {e}"); return 1

private def printNewLogs (logs : Array DeployLogEntry) (lastSeq : Nat) : IO Nat := do
  let mut cur := lastSeq
  for entry in logs do
    if entry.seq > cur then
      let tag := if entry.level == "error" then red "ERR" else if entry.level == "ok" then green "OK " else "   "
      IO.println s!"  {tag} {entry.message}"
      cur := entry.seq
  (← IO.getStdout).flush
  return cur

private def streamDeployLoop (apiBase token deployId : String) : Nat → Nat → ExceptT String IO DeploymentView
  | 0, _ => throw s!"timed out waiting for deployment `{deployId}` to finish"
  | fuel + 1, lastSeq => do
      let dv : DeploymentView ← cloudHttpJson apiBase "GET" s!"/api/v1/deployment?id={deployId}" (some token)
      let nextSeq ← liftIO (printNewLogs dv.logs lastSeq)
      if dv.status == "live" || dv.status == "failed" then return dv
      liftIO (IO.sleep 1000)
      streamDeployLoop apiBase token deployId fuel nextSeq

private def runLogs (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, rest0) := parseApiFlag args
  let follow := rest0.contains "--follow" || rest0.contains "-f"
  let positional := rest0.filter (fun s => s != "--follow" && s != "-f")
  let some deployId := positional.head? | throw "usage: qed logs <deployment-id> [--follow] [--api <url>]"
  let apiBase ← resolveApiBase flagApi? (← liftIO loadCredentials?)
  let creds ← requireAuthFor apiBase
  if follow then
    let dv ← streamDeployLoop apiBase creds.token deployId 600 0
    return if dv.status == "live" then 0 else 1
  else
    let dv : DeploymentView ← cloudHttpJson apiBase "GET" s!"/api/v1/deployment?id={deployId}" (some creds.token)
    liftIO <| IO.println s!"{bold dv.appSlug} ({dv.env}) [{dv.status}] id={dv.id}"
    discard <| liftIO (printNewLogs dv.logs 0)
    return 0

def cmdLogs (args : List String) : IO UInt32 := do
  match ← (runLogs args).run with | .ok c => return c | .error e => IO.eprintln (red s!"✗ {e}"); return 1

private def runSecrets (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, rest) := parseApiFlag args
  let apiBase ← resolveApiBase flagApi? (← liftIO loadCredentials?)
  let creds ← requireAuthFor apiBase
  match rest with
  | ["list", appSlug] =>
      let r : SecretsListResp ← cloudHttpJson apiBase "GET" s!"/api/v1/secrets?app={appSlug}" (some creds.token)
      if r.names.isEmpty then liftIO (IO.println s!"no secrets configured for `{appSlug}`")
      else for n in r.names do liftIO (IO.println s!"  {n}")
      return 0
  | "set" :: appSlug :: name :: tail =>
      let rec parseTail (envName : String) (val? : Option String) : List String → Except String (String × Option String)
        | [] => .ok (envName, val?)
        | "--env" :: e :: r => parseTail e val? r
        | "--value" :: v :: r => parseTail envName (some v) r
        | f :: _ => .error s!"unknown `qed secrets set` flag: `{f}`"
      let (envStr, vFlag?) ← match parseTail "prod" none tail with | .ok p => pure p | .error e => throw e
      let secretVal ← match vFlag? with
        | some v => pure v
        | none =>
            match ← liftIO (nonEmptyEnv "QED_SECRET_VALUE") with
            | some v => pure v
            | none => throw "provide secret value via `--value <val>` or `QED_SECRET_VALUE` env var"
      let req : SecretSetReq := { appSlug, env := envStr, name, value := secretVal }
      match req.validate with | .ok () => pure () | .error e => throw e
      let _ : Json ← cloudHttpJson apiBase "POST" "/api/v1/secrets" (some creds.token) (some (toJson req))
      liftIO (IO.println (green s!"✓ secret `{name}` set for `{appSlug}` ({envStr})"))
      return 0
  | _ => throw "usage: qed secrets list <app> | qed secrets set <app> <NAME> [--env prod|staging|preview] [--value <val>]"

def cmdSecrets (args : List String) : IO UInt32 := do
  match ← (runSecrets args).run with | .ok c => return c | .error e => IO.eprintln (red s!"✗ {e}"); return 1

private def runRollback (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, rest) := parseApiFlag args
  let [appSlug, deploymentId] := rest | throw "usage: qed rollback <app> <deployment-id> [--api <url>]"
  let apiBase ← resolveApiBase flagApi? (← liftIO loadCredentials?)
  let creds ← requireAuthFor apiBase
  let resp : DeployUploadResp ← cloudHttpJson apiBase "POST" "/api/v1/rollback" (some creds.token)
    (some (toJson ({ appSlug, deploymentId } : RollbackReq)))
  liftIO (IO.println (green s!"✓ rollback queued: {resp.deploymentId} ({resp.dashboardUrl})"))
  return 0

def cmdRollback (args : List String) : IO UInt32 := do
  match ← (runRollback args).run with | .ok c => return c | .error e => IO.eprintln (red s!"✗ {e}"); return 1

private structure HostedDeployOpts where
  api?        : Option String := none
  appSlug?    : Option String := none
  envStr      : String := "prod"
  pr          : Nat := 0
  mod?        : Option String := none
  deployName  : String := ""
  noWait      : Bool := false

private def parseHostedDeployOpts : List String → HostedDeployOpts → Except String HostedDeployOpts
  | [], o => .ok o
  | "--api" :: v :: r, o => parseHostedDeployOpts r { o with api? := some v }
  | "--app" :: v :: r, o => parseHostedDeployOpts r { o with appSlug? := some v }
  | "--env" :: v :: r, o => parseHostedDeployOpts r { o with envStr := v }
  | "--pr" :: v :: r, o => match v.toNat? with | some n => parseHostedDeployOpts r { o with pr := n } | none => .error s!"invalid `--pr`: `{v}`"
  | "--mod" :: v :: r, o => parseHostedDeployOpts r { o with mod? := some v }
  | "--deploy" :: v :: r, o => parseHostedDeployOpts r { o with deployName := v }
  | "--no-wait" :: r, o => parseHostedDeployOpts r { o with noWait := true }
  | flag :: _, _ => .error s!"unknown `qed deploy` flag: `{flag}`"

private def runHostedDeploy (args : List String) : ExceptT String IO UInt32 := do
  let opts ← match parseHostedDeployOpts args {} with | .ok o => pure o | .error e => throw e
  let apiBase ← resolveApiBase opts.api? (← liftIO loadCredentials?)
  let creds ← requireAuthFor apiBase
  let appSlug ← match opts.appSlug? with | some s => pure s | none => liftIO defaultAppSlug
  let mod ← match opts.mod? with | some m => pure m | none => liftIO jsRoot
  liftIO (step s!"bundling verified source for `{appSlug}` (root={mod}, env={opts.envStr})")
  let bundle ← collectSourceBundle (FilePath.mk ".")
  let req : DeployUploadReq := { appSlug, env := opts.envStr, pr := opts.pr, mod, deployName := opts.deployName, bundle }
  match req.validate with | .ok () => pure () | .error e => throw e
  liftIO (step s!"uploading {bundle.files.size} file(s) to Qed Cloud ({apiBase})")
  let up : DeployUploadResp ← cloudHttpJson apiBase "POST" "/api/v1/deploy" (some creds.token) (some (toJson req))
  liftIO <| IO.println s!"  deployment: {bold up.deploymentId} (tenant={up.tenantId}, app={up.appId})"
  liftIO <| IO.println s!"  dashboard:  {up.dashboardUrl}"
  if opts.noWait then return 0
  liftIO (step "streaming remote verification & rollout logs...")
  let final ← streamDeployLoop apiBase creds.token up.deploymentId 600 0
  if final.status == "live" then
    liftIO <| IO.println (green s!"✓ live at {final.url} (verified {final.verifiedDecls} decls, build {final.buildHash})")
    return 0
  else
    throw s!"deployment `{final.id}` failed: {final.errorMsg}"

def cmdHostedDeploy (args : List String) : IO UInt32 := do
  match ← (runHostedDeploy args).run with | .ok c => return c | .error e => IO.eprintln (red s!"✗ {e}"); return 1

end Qed.Cli
