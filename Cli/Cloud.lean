import Std.Data.HashSet
import Cli.Common
import Qed.Router.Basic
import Qed.Cloud.Protocol
import Qed.Server.Native

open System (FilePath)
open Qed Qed.Cloud Qed.Cloud.Protocol Qed.Server.Net Qed.Server.Native

namespace Qed.Cli

/-! ## Hosted Qed Cloud CLI Client (`Cli.Cloud`)
    Handles `qed login`, `qed logout`, `qed whoami`, `qed status`, `qed logs`,
    `qed cancel`, `qed secrets`, `qed rollback`, and hosted `qed deploy`. -/

/-- Default hosted Qed Cloud control plane URL (override with `--api` or `QED_CLOUD_API`). -/
def defaultCloudApiUrl? : Option String := some "https://api.qed.cloud"

structure CloudCredentials where
  apiBase : String
  token   : String
  userId  : String
  email   : String
deriving Inhabited, BEq, Repr
json_obj_codec% CloudCredentials [apiBase, token, userId, email]

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

private def validateCloudApiBase (raw : String) : Except String String :=
  let u := normalizeApiBase raw
  if isValidCloudApiUrl u then .ok u
  else .error s!"invalid Qed Cloud API URL `{redactArg raw}` (must be `https://<host>[:port]` or local loopback `http://127.0.0.1[:port]`)"

private def resolveApiBase (flagApi? : Option String) (creds? : Option CloudCredentials) : ExceptT String IO String := do
  let raw? := (← liftIO (optOrEnv flagApi? "QED_CLOUD_API")).orElse (fun _ => creds?.map (·.apiBase)) |>.orElse (fun _ => defaultCloudApiUrl?)
  match raw? with
  | none =>
      throw "missing Qed Cloud API URL: pass `--api <url>` (e.g. `https://api.qed.cloud` or `http://127.0.0.1:8080`) or set `QED_CLOUD_API`"
  | some raw => liftP (validateCloudApiBase raw)

private def validateExplicitToken (raw : String) : Except String String :=
  let t := raw.cliTrim
  if t.isEmpty then .error "provided authentication token is empty"
  else if t.toList.any (fun c => c.isWhitespace || c.toNat < 0x20 || c.toNat == 0x7F) then
    .error "invalid authentication token (contains whitespace or control characters)"
  else .ok t

private def resolveExplicitToken (flagToken? : Option String) (allowEnv : Bool := true) : ExceptT String IO (Option String) := do
  let raw? ← if allowEnv then liftIO (optOrEnv flagToken? "QED_CLOUD_TOKEN") else pure flagToken?
  raw?.mapM fun raw => liftP (validateExplicitToken raw)

private def requireAuthFor (apiBase : String) (flagToken? : Option String := none) : ExceptT String IO CloudCredentials := do
  if let some tok ← resolveExplicitToken flagToken? then
    return { apiBase, token := tok, userId := "token", email := "token" }
  let some creds ← liftIO loadCredentials?
    | throw s!"not logged in to Qed Cloud. Run `qed login --api {apiBase}`, pass `--token <token>`, or set `QED_CLOUD_TOKEN`"
  if normalizeApiBase creds.apiBase != apiBase then
    throw s!"stored credentials are for `{creds.apiBase}`, not `{apiBase}` (refusing to send token to another host; run `qed login --api {apiBase}`)"
  if creds.token.isEmpty then throw "stored credentials have an empty token; run `qed login` again"
  return creds

private def resolveCloudAuth (flagApi? flagTok? : Option String) : ExceptT String IO (String × CloudCredentials) := do
  let hasExplicitTok ← match flagTok? with
    | some _ => pure true
    | none   => pure (← liftIO (nonEmptyEnv "QED_CLOUD_TOKEN")).isSome
  let creds? ← if hasExplicitTok then pure none else liftIO loadCredentials?
  let apiBase ← resolveApiBase flagApi? creds?
  let creds ← requireAuthFor apiBase flagTok?
  return (apiBase, creds)

private def cloudHttpJson {α : Type} [FromJson α] (apiBase method path : String)
    (token? : Option String) (body? : Option Json := none) : ExceptT String IO α := do
  let (_, j) ← liftE <| execHttpJson method (apiBase ++ path) token?
    (body?.elim ByteArray.empty (·.render.toUTF8)) (body?.map fun _ => "application/json")
    #[("Accept", "application/json")] (ssrfGuard := !isStrictLoopbackUrl apiBase)
    (fmtTransportErr := fun e => s!"cannot reach Qed Cloud at `{apiBase}`: {e}")
    (fmtStatusErr := fun status txt =>
      let t := txt.cliTrim
      let detail := match Json.parse t with
        | .ok j => (j.strAt? "error").orElse (fun _ => j.strAt? "message") |>.getD t
        | .error _ => t
      s!"Qed Cloud API error (HTTP {status}): {if detail.isEmpty then "request failed" else detail}")
    (fmtJsonErr := fun _ e => s!"invalid JSON response from Qed Cloud `{path}`: {e}")
  liftP <| (fromJson j : Except String α).mapError (s!"unexpected Qed Cloud response for `{path}`: {·}")

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

private def checkSize (rel : String) (fileSz nextTotal : Nat) : Except String Unit := do
  if fileSz > maxSourceFileBytes then throw s!"source file `{rel}` exceeds {maxSourceFileBytes} bytes"
  if nextTotal > maxTotalSourceBytes then throw s!"project source exceeds {maxTotalSourceBytes} bytes"

private def collectSourceFilesLoop (rootReal : FilePath) (rootPfx : String) :
    Nat → List (FilePath × String) → Array SourceFile → Nat → ExceptT String IO SourceBundle
  | 0, _, _, _ => throw "source directory traversal exceeded depth/file budget"
  | _, [], acc, _ => do
      let b : SourceBundle := { files := acc }
      liftP b.validate
      return b
  | fuel + 1, (dir, relPfx) :: rest, acc, totalBytes => do
      let entries ← liftIO (dir.readDir)
      let sorted := entries.qsort (fun a b => a.fileName < b.fileName)
      let mut nextDirs := rest
      let mut nextAcc := acc
      let mut nextBytes := totalBytes
      for e in sorted do
        let name := e.fileName
        if name.startsWith "." || ["dist", "node_modules", "target"].contains name.toLower then continue
        let full := dir / name
        let some md ← liftIO (symlinkMetadata? full) | continue
        if md.type == .symlink then continue
        let some rp ← liftIO (realPath? full) | continue
        if !rp.toString.startsWith rootPfx then continue
        let rel := if relPfx.isEmpty then name else s!"{relPfx}/{name}"
        if md.type == .dir then
          nextDirs := (full, rel) :: nextDirs
        else if md.type == .file && isValidSourceRelPath rel then
          if nextAcc.size >= maxSourceFiles then
            throw s!"project exceeds maximum of {maxSourceFiles} source files"
          let metaBytes := md.byteSize.toNat
          liftP (checkSize rel metaBytes (nextBytes + metaBytes))
          let bytes ← liftIO (IO.FS.readBinFile full)
          liftP (checkSize rel bytes.size (nextBytes + bytes.size))
          nextBytes := nextBytes + bytes.size
          let file : SourceFile ←
            if isBinarySourceExt name then
              pure { path := rel, content := encodeBase64 bytes, encoding := "base64" }
            else
              match String.fromUTF8? bytes with
              | some content => pure { path := rel, content, encoding := "utf8" }
              | none =>
                  if rel.toLower.endsWith ".lean" then
                    throw s!"source file `{rel}` is not valid UTF-8"
                  else
                    pure { path := rel, content := encodeBase64 bytes, encoding := "base64" }
          nextAcc := nextAcc.push file
      collectSourceFilesLoop rootReal rootPfx fuel nextDirs nextAcc nextBytes

def collectSourceBundle (rootDir : FilePath) : ExceptT String IO SourceBundle := do
  let some rootReal ← liftIO (realPath? rootDir) | throw s!"project directory not found: `{rootDir}`"
  collectSourceFilesLoop rootReal (dirPrefix rootReal) 2000 [(rootReal, "")] #[] 0

/-! ### Pure CLI Parsers & Query Builders -/

private def requireValid (ok : Bool) (msg : String) : Except String Unit :=
  if ok then .ok () else .error msg
private def requireSlug (s : String) : Except String Unit :=
  requireValid (isValidAppSlug s) s!"invalid app slug `{redactArg s}`"
private def requireEnv (e : String) : Except String Unit :=
  requireValid (isValidEnvName e) s!"invalid env `{redactArg e}` (expected prod, staging, or preview)"
private def requireDeployId (id : String) : Except String Unit :=
  requireValid (isValidDeploymentId id) s!"invalid deployment id `{redactArg id}`"
private def parsePrFlag (v : String) : Except String Nat :=
  v.toNat?.elim (.error s!"invalid `--pr`: `{redactArg v}`") .ok

def parseCloudFlags (args : List String) : Except String (Option String × Option String × List String) := do
  let ((api?, tok?), rest) ← parseCliFlags {
    flags := [
      .valOk ["--api"] (fun (_, t) u => (some u, t)),
      .valOk ["--token"] (fun (a, _) t => (a, some t)),
      .passThroughVal ["--value", "--search"] ],
    passDash := true, unknownErr := fun _ => ""
  } (none, none) args
  return (api?, tok?, rest)

def splitSecretAssignment (s : String) : Option (String × String) :=
  match s.splitOn "=" with
  | k :: v :: rest => some (k, "=".intercalate (v :: rest))
  | _ => none

structure SecretSetParsed where
  appSlug : String
  env     : String
  name    : String
  value?  : Option String
deriving Inhabited, BEq, Repr

def parseSecretsSetArgs (args : List String) : Except String SecretSetParsed := do
  let ((appFlag?, envStr, valFlag?), pos) ← parseCliFlags {
    flags := [
      .valOk ["--app"] (fun (_, e, v) a => (some a, e, v)),
      .valOk ["--env"] (fun (a, _, v) e => (a, e, v)),
      .valOk ["--value"] (fun (a, e, _) v => (a, e, some v)) ],
    unknownErr := fun x => s!"unknown `qed secrets set` flag: `{redactArg x}`"
  } (none, "prod", none) args
  let (appSlug, target) ← match appFlag?, pos with
    | some a, [t]    => .ok (a, t)
    | none, [a, t]   => .ok (a, t)
    | some _, []     => .error "missing secret `<NAME>` or `KEY=VALUE`"
    | none, [] | none, [_] => .error "usage: qed secrets set <app> <NAME|KEY=VALUE> [--env prod|staging|preview] [--value <val>]"
    | _, _           => .error "too many positional arguments to `qed secrets set`"
  match splitSecretAssignment target with
  | some (k, v) =>
      if valFlag?.isSome then .error "cannot combine `KEY=VALUE` with `--value`"
      else .ok { appSlug, env := envStr, name := k, value? := some v }
  | none =>
      .ok { appSlug, env := envStr, name := target, value? := valFlag? }

private def parseSecretsAppEnvArgs (subCmd : String) (args : List String) (needName : Bool) :
    Except String (String × Option String × Option String) := do
  let ((appFlag?, envFlag?), pos) ← parseCliFlags {
    flags := [
      .valOk ["--app"] (fun (_, e) a => (some a, e)),
      .valOk ["--env"] (fun (a, _) e => (a, some e)) ],
    unknownErr := fun x => s!"unknown `qed secrets {subCmd}` flag: `{redactArg x}`"
  } (none, none) args
  if needName then
    match appFlag?, pos with
    | some a, [n]  => .ok (a, envFlag?, some n)
    | none, [a, n] => .ok (a, envFlag?, some n)
    | _, _ => .error s!"usage: qed secrets {subCmd} <app> <NAME> [--env prod|staging|preview]"
  else
    match appFlag?, pos with
    | some a, [] => .ok (a, envFlag?, none)
    | none, [a]  => .ok (a, envFlag?, none)
    | _, _ => .error s!"usage: qed secrets {subCmd} <app> [--env prod|staging|preview]"

structure LogsCliOpts where
  target    : String := ""
  runtime   : Bool := false
  envStr    : String := "prod"
  pr        : Nat := 0
  severity? : Option String := none
  search?   : Option String := none
  follow    : Bool := false
deriving Inhabited, BEq, Repr

def parseLogsArgs (args : List String) : Except String LogsCliOpts := do
  let ((o, hasRuntimeFlag, hasPrFlag), pos) ← parseCliFlags (σ := LogsCliOpts × Bool × Bool) {
    flags := [
      .bool ["--runtime"] (fun (o, hr, hp) => ({ o with runtime := true }, hr, hp)),
      .bool ["--follow", "-f"] (fun (o, hr, hp) => ({ o with follow := true }, hr, hp)),
      .valOk ["--env"] (fun (o, _, hp) v => ({ o with envStr := v }, true, hp)),
      .val ["--pr"] (fun (o, _, _) v => (parsePrFlag v).map fun n => ({ o with pr := n }, true, true)),
      .valOk ["--severity"] (fun (o, _, hp) v => ({ o with severity? := some v.toLower }, true, hp)),
      .valOk ["--search"] (fun (o, _, hp) v => ({ o with search? := some v }, true, hp)) ],
    unknownErr := fun x => s!"unknown `qed logs` flag: `{redactArg x}`"
  } ({}, false, false) args
  let target ← match pos with
    | [t] => .ok t
    | []  => .error "usage: qed logs <deployment-id> [--follow] | qed logs <app-slug> --runtime [--env prod|staging|preview] [--pr <N>] [--severity info|warn|error|debug] [--search <q>] [--follow]"
    | _   => .error "too many positional arguments to `qed logs`"
  let o := { o with target }
  if !o.runtime then
    requireValid (!hasRuntimeFlag) "`--env`, `--pr`, `--severity`, and `--search` require `--runtime`"
    requireDeployId o.target
  else
    requireSlug o.target
    requireEnv o.envStr
    requireValid (!(o.envStr == "preview" && o.pr == 0)) "preview runtime logs require `--pr <positive-number>`"
    requireValid (!(o.envStr != "preview" && (hasPrFlag || o.pr != 0))) "`--pr` is only valid with `--env preview`"
    if let some sev := o.severity? then
      requireValid (isValidLogSeverity sev) s!"invalid severity `{redactArg sev}` (expected debug, info, warn, or error)"
  .ok o

def buildRuntimeLogsPath (appSlug envStr : String) (pr : Nat := 0)
    (severity? : Option String := none) (search? : Option String := none) : String :=
  let base := [s!"app={Qed.encodeSeg appSlug}", s!"env={Qed.encodeSeg envStr}"]
  let withPr := if pr > 0 then base ++ [s!"pr={pr}"] else base
  let withSev := match severity? with
    | some sev => if sev.isEmpty then withPr else withPr ++ [s!"severity={Qed.encodeSeg sev.toLower}"]
    | none     => withPr
  let withSearch := match search? with
    | some q => if q.isEmpty then withSev else withSev ++ [s!"search={Qed.encodeSeg q}"]
    | none   => withSev
  "/api/v1/logs/runtime?" ++ "&".intercalate withSearch

/-! ### CLI Commands: `login`, `logout`, `whoami`, `status`, `logs`, `cancel`, `secrets`, `rollback`, hosted `deploy` -/

private def pollDeviceLoop (apiBase deviceCode : String) (intervalMs : UInt32) : Nat → ExceptT String IO DevicePollResp
  | 0 => throw "login timed out waiting for browser approval"
  | fuel + 1 => do
      let r : DevicePollResp ← cloudHttpJson apiBase "POST" "/api/v1/cli/device/poll" none (some (toJson ({ deviceCode } : DevicePollReq)))
      if r.status == "approved" then return r
      if r.status == "expired" then throw "device login code expired; run `qed login` again"
      liftIO (IO.sleep intervalMs)
      pollDeviceLoop apiBase deviceCode intervalMs fuel

private def rejectLeadingDashFlags (cmdName : String) (args : List String) : Except String Unit :=
  match args.find? (·.startsWith "-") with
  | some f => .error s!"unknown `{cmdName}` flag: `{redactArg f}`"
  | none   => .ok ()

private def runLogin (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  if flagTok?.isSome then throw "`--token` is not valid for `qed login`"
  let noOpen := rest.contains "--no-open"
  for f in rest do if f != "--no-open" then throw s!"unknown `qed login` flag: `{redactArg f}`"
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

def cmdLogin (args : List String) : IO UInt32 := runExceptCmd (runLogin args)

private def bestEffortRevokeToken (apiBase token : String) : IO Unit := do
  match ← (cloudHttpJson (α := TokenRevokeResp) apiBase "POST" "/api/v1/tokens/revoke-current" (some token) (some (.obj []))).run with
  | .ok resp =>
      if !resp.revoked then
        IO.eprintln "warning: server reported token was already revoked or inactive"
  | .error e =>
      IO.eprintln s!"warning: could not revoke token on server ({e})"

private def deleteCredentialsFile (p : FilePath) : ExceptT String IO Unit := do
  let err? ← liftIO (try IO.FS.removeFile p; pure none catch e => pure (some (toString e)))
  if ← liftIO p.pathExists then
    let detail := err?.elim "file still exists" id
    throw s!"failed to remove credentials file `{p}`: {detail}"

private def runLogout (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  if !rest.isEmpty then throw s!"unexpected arguments to `qed logout`: {" ".intercalate (rest.map redactArg)}"
  let validatedFlagApi? ← flagApi?.mapM (fun raw => liftP (validateCloudApiBase raw))
  if let some tok ← resolveExplicitToken flagTok? (allowEnv := false) then
    let apiBase ← resolveApiBase validatedFlagApi? none
    let resp : TokenRevokeResp ← cloudHttpJson apiBase "POST" "/api/v1/tokens/revoke-current" (some tok) (some (.obj []))
    if resp.revoked then
      liftIO (IO.println (green "✓ token revoked"))
    else
      liftIO (IO.println "token was already revoked or inactive")
    return 0
  let p ← liftIO credentialsPath
  if ← liftIO p.pathExists then
    if let some creds ← liftIO loadCredentials? then
      if !creds.token.isEmpty then
        let storedBase := normalizeApiBase creds.apiBase
        let revokeBase? : Option String := match validatedFlagApi? with
          | some u => if !storedBase.isEmpty && storedBase == u then some u else none
          | none   => if !storedBase.isEmpty && isValidCloudApiUrl storedBase then some storedBase else none
        match revokeBase? with
        | some base => liftIO (bestEffortRevokeToken base creds.token)
        | none =>
            if let some u := validatedFlagApi? then
              liftIO (IO.eprintln s!"warning: stored credentials are for `{creds.apiBase}`, not `{u}`; skipping remote token revoke")
    deleteCredentialsFile p
    liftIO (IO.println (green "✓ logged out of Qed Cloud"))
    return 0
  else
    liftIO (IO.println "already logged out")
    return 0

def cmdLogout (args : List String := []) : IO UInt32 := runExceptCmd (runLogout args)

private def runWhoami (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  if !rest.isEmpty then throw s!"unexpected arguments to `qed whoami`: {" ".intercalate (rest.map redactArg)}"
  let (apiBase, creds) ← resolveCloudAuth flagApi? flagTok?
  let me : WhoamiResp ← cloudHttpJson apiBase "GET" "/api/v1/whoami" (some creds.token)
  liftIO <| IO.println s!"{green "✓"} {me.email} (id={me.userId}, tenant={me.tenantId}, apps={me.appsCount}) @ {apiBase}"
  return 0

def cmdWhoami (args : List String) : IO UInt32 := runExceptCmd (runWhoami args)

private def runStatus (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  liftP (rejectLeadingDashFlags "qed status" rest)
  let filterSlug? ← match rest with
    | []  => pure none
    | [s] => liftP (requireSlug s); pure (some s)
    | _   => throw "usage: qed status [app] [--api <url>] [--token <tok>]"
  let (apiBase, creds) ← resolveCloudAuth flagApi? flagTok?
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

def cmdStatus (args : List String) : IO UInt32 := runExceptCmd (runStatus args)

private def printNewLogs (logs : Array DeployLogEntry) (lastSeq : Nat) : IO Nat := do
  let mut cur := lastSeq
  for entry in logs do
    if entry.seq > cur then
      let tag := if entry.level == "error" then red "ERR" else if entry.level == "ok" then green "OK " else "   "
      IO.println s!"  {tag} {entry.message}"
      cur := entry.seq
  (← IO.getStdout).flush
  return cur

private def isTerminalDeployStatus (s : String) : Bool :=
  s == "live" || s == "failed" || s == "canceled"

private def streamDeployLoop (apiBase token deployId : String) : Nat → Nat → ExceptT String IO DeploymentView
  | 0, _ => throw s!"timed out waiting for deployment `{deployId}` to finish"
  | fuel + 1, lastSeq => do
      let dv : DeploymentView ← cloudHttpJson apiBase "GET" s!"/api/v1/deployment?id={Qed.encodeSeg deployId}" (some token)
      let nextSeq ← liftIO (printNewLogs dv.logs lastSeq)
      if isTerminalDeployStatus dv.status then return dv
      liftIO (IO.sleep 1000)
      streamDeployLoop apiBase token deployId fuel nextSeq

private def formatRuntimeSeverity (sev : String) : String :=
  match sev.toLower with
  | "error" => red "ERROR"
  | "warn" | "warning" => "\x1b[33mWARN \x1b[0m"
  | "debug" => "\x1b[2mDEBUG\x1b[0m"
  | _       => green "INFO "

private def runtimeLogDedupKey (e : RuntimeLogView) : String :=
  if e.id.isEmpty then s!"{e.timestamp}|{e.source}|{e.message}" else e.id

def filterNewRuntimeLogs (logs : Array RuntimeLogView) (seen : Std.HashSet String) :
    Array RuntimeLogView × Std.HashSet String :=
  logs.foldl (init := (#[], seen)) fun (acc, s) entry =>
    let key := runtimeLogDedupKey entry
    if s.contains key then (acc, s) else (acc.push entry, s.insert key)

private def printRuntimeLogs (logs : Array RuntimeLogView) (seen : Std.HashSet String) : IO (Std.HashSet String × Nat) := do
  let (fresh, nextSeen) := filterNewRuntimeLogs logs seen
  for entry in fresh do
    let ts := if entry.timestamp.isEmpty then "-" else entry.timestamp
    let src := if entry.source.isEmpty then "app" else entry.source
    IO.println s!"  {ts}  {formatRuntimeSeverity entry.severity}  [{src}]  {entry.message}"
  if !fresh.isEmpty then (← IO.getStdout).flush
  return (nextSeen, fresh.size)

private def streamRuntimeLogsLoop (apiBase token path : String) :
    Nat → Std.HashSet String → ExceptT String IO Unit
  | 0, _ => pure ()
  | fuel + 1, seen => do
      let resp : RuntimeLogsResp ← cloudHttpJson apiBase "GET" path (some token)
      let (seen', _) ← liftIO (printRuntimeLogs resp.logs seen)
      let nextSeen :=
        if seen'.size > 10000 then
          resp.logs.foldl (init := ({} : Std.HashSet String)) fun acc e => acc.insert (runtimeLogDedupKey e)
        else seen'
      liftIO (IO.sleep 2000)
      streamRuntimeLogsLoop apiBase token path fuel nextSeen

private def runLogs (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  let opts ← liftP (parseLogsArgs rest)
  let (apiBase, creds) ← resolveCloudAuth flagApi? flagTok?
  if opts.runtime then
    let path := buildRuntimeLogsPath opts.target opts.envStr opts.pr opts.severity? opts.search?
    let prTag := if opts.pr > 0 then s!" pr #{opts.pr}" else ""
    if opts.follow then
      liftIO (step s!"following runtime logs for `{opts.target}` ({opts.envStr}{prTag})")
      streamRuntimeLogsLoop apiBase creds.token path 1800 {}
      return 0
    else
      let resp : RuntimeLogsResp ← cloudHttpJson apiBase "GET" path (some creds.token)
      liftIO <| IO.println s!"{bold resp.appSlug} ({resp.env}{if resp.pr > 0 then s!" pr #{resp.pr}" else ""}) runtime logs"
      if resp.logs.isEmpty then
        liftIO <| IO.println "  (no runtime logs found)"
      else
        discard <| liftIO (printRuntimeLogs resp.logs {})
      return 0
  else if opts.follow then
    let dv ← streamDeployLoop apiBase creds.token opts.target 600 0
    return if dv.status == "live" then 0 else 1
  else
    let dv : DeploymentView ← cloudHttpJson apiBase "GET" s!"/api/v1/deployment?id={Qed.encodeSeg opts.target}" (some creds.token)
    liftIO <| IO.println s!"{bold dv.appSlug} ({dv.env}) [{dv.status}] id={dv.id}"
    discard <| liftIO (printNewLogs dv.logs 0)
    return 0

def cmdLogs (args : List String) : IO UInt32 := runExceptCmd (runLogs args)

private def runCancel (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  liftP (rejectLeadingDashFlags "qed cancel" rest)
  let [deployId] := rest | throw "usage: qed cancel <deployment-id> [--api <url>] [--token <tok>]"
  liftP (requireDeployId deployId)
  let req : CancelDeployReq := { deploymentId := deployId }
  liftP req.validate
  let (apiBase, creds) ← resolveCloudAuth flagApi? flagTok?
  let resp : Json ← cloudHttpJson apiBase "POST" "/api/v1/deployment/cancel" (some creds.token) (some (toJson req))
  let st := (resp.strAt? "status").getD "canceled"
  liftIO (IO.println (green s!"✓ deployment `{deployId}` {st}"))
  return 0

def cmdCancel (args : List String) : IO UInt32 := runExceptCmd (runCancel args)

private def runSecrets (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  match rest with
  | "list" :: tail =>
      let (appSlug, env?, _) ← liftP (parseSecretsAppEnvArgs "list" tail false)
      liftP (requireSlug appSlug)
      if let some e := env? then liftP (requireEnv e)
      let (apiBase, creds) ← resolveCloudAuth flagApi? flagTok?
      let envQ := env?.elim "" fun e => s!"&env={Qed.encodeSeg e}"
      let r : SecretsListResp ← cloudHttpJson apiBase "GET" s!"/api/v1/secrets?app={Qed.encodeSeg appSlug}{envQ}" (some creds.token)
      let names : Array String := match env? with
        | some e => r.names.filter fun (n : String) => !n.contains ":" || n.startsWith s!"{e}:"
        | none   => r.names
      if names.isEmpty then
        liftIO (IO.println s!"no secrets configured for `{appSlug}`{env?.elim "" fun e => s!" ({e})"}")
      else
        for n in names do liftIO (IO.println s!"  {n}")
      return 0
  | "set" :: tail =>
      let parsed ← liftP (parseSecretsSetArgs tail)
      liftP (validateSecretTarget parsed.appSlug parsed.env parsed.name redactArg (envHint := true))
      let secretVal ← match parsed.value? with
        | some v => pure v
        | none =>
            match ← liftIO (IO.getEnv "QED_SECRET_VALUE") with
            | some v =>
                if v.isEmpty then throw "provide secret value via `KEY=VALUE`, `--value <val>`, or `QED_SECRET_VALUE` env var"
                else pure v
            | none => throw "provide secret value via `KEY=VALUE`, `--value <val>`, or `QED_SECRET_VALUE` env var"
      let req : SecretSetReq := { appSlug := parsed.appSlug, env := parsed.env, name := parsed.name, value := secretVal }
      liftP req.validate
      let (apiBase, creds) ← resolveCloudAuth flagApi? flagTok?
      let _ : Json ← cloudHttpJson apiBase "POST" "/api/v1/secrets" (some creds.token) (some (toJson req))
      liftIO (IO.println (green s!"✓ secret `{req.name}` set for `{req.appSlug}` ({req.env})"))
      return 0
  | "delete" :: tail =>
      let (appSlug, env?, name?) ← liftP (parseSecretsAppEnvArgs "delete" tail true)
      let some name := name? | throw "usage: qed secrets delete <app> <NAME> [--env prod|staging|preview]"
      let envStr := env?.getD "prod"
      liftP (validateSecretTarget appSlug envStr name redactArg (envHint := true))
      let req : SecretDeleteReq := { appSlug, env := envStr, name }
      liftP req.validate
      let (apiBase, creds) ← resolveCloudAuth flagApi? flagTok?
      let _ : Json ← cloudHttpJson apiBase "POST" "/api/v1/secrets/delete" (some creds.token) (some (toJson req))
      liftIO (IO.println (green s!"✓ secret `{req.name}` deleted for `{req.appSlug}` ({req.env})"))
      return 0
  | _ => throw "usage: qed secrets list <app> [--env ...] | set <app> <NAME|KEY=VALUE> [--env ...] [--value <val>] | delete <app> <NAME> [--env ...]"

def cmdSecrets (args : List String) : IO UInt32 := runExceptCmd (runSecrets args)

private def runRollback (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  liftP (rejectLeadingDashFlags "qed rollback" rest)
  let [appSlug, deploymentId] := rest | throw "usage: qed rollback <app> <deployment-id> [--api <url>] [--token <tok>]"
  liftP (requireSlug appSlug)
  liftP (requireDeployId deploymentId)
  let (apiBase, creds) ← resolveCloudAuth flagApi? flagTok?
  let resp : DeployUploadResp ← cloudHttpJson apiBase "POST" "/api/v1/rollback" (some creds.token)
    (some (toJson ({ appSlug, deploymentId } : RollbackReq)))
  liftIO (IO.println (green s!"✓ rollback queued: {resp.deploymentId} ({resp.dashboardUrl})"))
  return 0

def cmdRollback (args : List String) : IO UInt32 := runExceptCmd (runRollback args)

private structure HostedDeployOpts where
  api?        : Option String := none
  token?      : Option String := none
  appSlug?    : Option String := none
  envStr      : String := "prod"
  pr          : Nat := 0
  mod?        : Option String := none
  deployName  : String := ""
  noWait      : Bool := false

private def parseHostedDeployOpts (args : List String) : Except String HostedDeployOpts :=
  let bad (x : String) := s!"unknown or incomplete `qed deploy` flag: `{redactArg x}`"
  Prod.fst <$> parseCliFlags {
    flags := [
      .bool ["--no-wait"] (fun o => { o with noWait := true }),
      .valOk ["--api"] (fun o v => { o with api? := some v }),
      .valOk ["--token"] (fun o v => { o with token? := some v }),
      .valOk ["--app"] (fun o v => { o with appSlug? := some v }),
      .valOk ["--env"] (fun o v => { o with envStr := v }),
      .val ["--pr"] (fun o v => (parsePrFlag v).map fun n => { o with pr := n }),
      .valOk ["--mod"] (fun o v => { o with mod? := some v }),
      .valOk ["--deploy"] (fun o v => { o with deployName := v }) ],
    allowPos := false, unknownErr := bad, missingErr := bad
  } {} args

private def runHostedDeploy (args : List String) : ExceptT String IO UInt32 := do
  let opts ← liftP (parseHostedDeployOpts args)
  let (apiBase, creds) ← resolveCloudAuth opts.api? opts.token?
  let appSlug ← match opts.appSlug? with | some s => pure s | none => liftIO defaultAppSlug
  liftP (requireSlug appSlug)
  liftP (requireEnv opts.envStr)
  let mod ← match opts.mod? with | some m => pure m | none => liftIO jsRoot
  liftP (requireValid (isValidModuleName mod) s!"invalid root module `{redactArg mod}`")
  liftP (requireValid (opts.deployName.isEmpty || isValidModuleName opts.deployName) s!"invalid deploy spec name `{redactArg opts.deployName}`")
  liftIO (step s!"bundling verified source for `{appSlug}` (root={mod}, env={opts.envStr})")
  let bundle ← collectSourceBundle (FilePath.mk ".")
  let req : DeployUploadReq := { appSlug, env := opts.envStr, pr := opts.pr, mod, deployName := opts.deployName, bundle }
  liftP req.validate
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
  else if final.status == "canceled" then
    throw s!"deployment `{final.id}` was canceled{if final.errorMsg.isEmpty then "" else s!": {final.errorMsg}"}"
  else
    throw s!"deployment `{final.id}` failed: {final.errorMsg}"

def cmdHostedDeploy (args : List String) : IO UInt32 := runExceptCmd (runHostedDeploy args)

end Qed.Cli
