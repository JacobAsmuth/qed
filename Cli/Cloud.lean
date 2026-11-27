import Std.Data.HashSet
import Cli.Common
import Qed.Router.Basic
import Qed.Cloud.Protocol
import Qed.Server.Native
open System (FilePath)
open Qed Qed.Cloud Qed.Cloud.Protocol Qed.Server.Net Qed.Server.Native

namespace Qed.Cli

/-! ## Hosted Qed Cloud CLI Client (`Cli.Cloud`) -/

def defaultCloudApiUrl? : Option String := some "https://api.qed.cloud"

structure CloudCredentials where
  (apiBase token userId email : String)
deriving Inhabited
json_obj_codec% CloudCredentials [apiBase, token, userId, email]

private def credentialsPath : IO FilePath := do
  if let some p ← nonEmptyEnv "QED_CREDENTIALS_FILE" then return FilePath.mk p
  return FilePath.mk ((← nonEmptyEnv "HOME").getD ".") / ".config" / "qed" / "credentials.json"

private def loadCredentials? : IO (Option CloudCredentials) := do
  let p ← credentialsPath
  if !(← p.pathExists) then return none
  match ← symlinkType? p with
  | some .file => return (← try pure (some (← IO.FS.readFile p)) catch _ => pure none).bind fun raw => (Json.parse raw.cliTrim >>= fromJson).toOption
  | _ => return none

private def saveCredentials (c : CloudCredentials) : ExceptT String IO Unit := do
  let p ← liftIO credentialsPath
  if let some dir := p.parent then IO.FS.createDirAll dir; discard <| liftIO (shQuiet "chmod" #["700", dir.toString])
  if let some ty ← liftIO (symlinkType? p) then if ty != .file then throw s!"refusing to overwrite symlink or non-regular credentials file `{p}`"
  IO.FS.writeFile p ((toJson c).render ++ "\n"); discard <| liftIO (shQuiet "chmod" #["600", p.toString])

private def validateCloudApiBase (raw : String) : Except String String :=
  let u := normalizeApiBase raw
  if isValidCloudApiUrl u then .ok u
  else .error s!"invalid Qed Cloud API URL `{redactArg raw}` (must be `https://<host>[:port]` or local loopback `http://127.0.0.1[:port]`)"

private def resolveApiBase (flagApi? : Option String) (creds? : Option CloudCredentials) : ExceptT String IO String := do
  let some raw := (← liftIO (optOrEnv flagApi? "QED_CLOUD_API")).orElse (fun _ => creds?.map (·.apiBase)) |>.orElse (fun _ => defaultCloudApiUrl?)
    | throw "missing Qed Cloud API URL: pass `--api <url>` (e.g. `https://api.qed.cloud` or `http://127.0.0.1:8080`) or set `QED_CLOUD_API`"
  liftP (validateCloudApiBase raw)

private def resolveExplicitToken (flagToken? : Option String) (allowEnv : Bool := true) : ExceptT String IO (Option String) := do
  let raw? ← if allowEnv then liftIO (optOrEnv flagToken? "QED_CLOUD_TOKEN") else pure flagToken?
  raw?.mapM fun raw => liftP <| let t := raw.cliTrim
    if t.isEmpty then .error "provided authentication token is empty"
    else if Env.hasCtrlOrWs t then .error "invalid authentication token (contains whitespace or control characters)" else .ok t

private def resolveCloudAuth (flagApi? flagTok? : Option String) : ExceptT String IO (String × CloudCredentials) := do
  let hasExplicitTok ← match flagTok? with | some _ => pure true | none => pure (← liftIO (nonEmptyEnv "QED_CLOUD_TOKEN")).isSome
  let creds? ← if hasExplicitTok then pure none else liftIO loadCredentials?
  let apiBase ← resolveApiBase flagApi? creds?
  if let some tok ← resolveExplicitToken flagTok? then return (apiBase, { apiBase, token := tok, userId := "token", email := "token" })
  let some creds := creds? | throw s!"not logged in to Qed Cloud. Run `qed login --api {apiBase}`, pass `--token <token>`, or set `QED_CLOUD_TOKEN`"
  if normalizeApiBase creds.apiBase != apiBase then
    throw s!"stored credentials are for `{creds.apiBase}`, not `{apiBase}` (refusing to send token to another host; run `qed login --api {apiBase}`)"
  if creds.token.isEmpty then throw "stored credentials have an empty token; run `qed login` again"
  return (apiBase, creds)

@[noinline, nospecialize]
private def cloudHttpJson {α : Type} [FromJson α] (apiBase method path : String)
    (token? : Option String) (body? : Option Json := none) : ExceptT String IO α := do
  let (_, j) ← liftE <| execHttpJson method (apiBase ++ path) token?
    (body?.elim ByteArray.empty (·.render.toUTF8)) (body?.map fun _ => "application/json")
    #[("Accept", "application/json")] (ssrfGuard := !isStrictLoopbackUrl apiBase)
    (fmtTransportErr := fun e => s!"cannot reach Qed Cloud at `{apiBase}`: {e}")
    (fmtStatusErr := fun status txt =>
      let t := txt.cliTrim
      let detail := match Json.parse t with | .ok j => (j.strAt? "error").orElse (fun _ => j.strAt? "message") |>.getD t | .error _ => t
      s!"Qed Cloud API error (HTTP {status}): {if detail.isEmpty then "request failed" else detail}")
    (fmtJsonErr := fun _ e => s!"invalid JSON response from Qed Cloud `{path}`: {e}")
  liftP <| (fromJson j : Except String α).mapError (s!"unexpected Qed Cloud response for `{path}`: {·}")

private def defaultAppSlug : IO String := do
  let raw := String.ofList <| ((← IO.currentDir).fileName.getD "qed-app").toLower.toList.map fun c => if ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') then c else '-'
  let clipped := ("-".intercalate ((raw.splitOn "-").filter (!·.isEmpty)) |>.take 48).toString
  let trimmed := if clipped.endsWith "-" then (clipped.dropEnd 1).toString else clipped
  return if isValidAppSlug trimmed then trimmed else "qed-app"

private def checkSize (rel : String) (fileSz nextTotal : Nat) : Except String Unit := do
  if fileSz > maxSourceFileBytes then throw s!"source file `{rel}` exceeds {maxSourceFileBytes} bytes"
  if nextTotal > maxTotalSourceBytes then throw s!"project source exceeds {maxTotalSourceBytes} bytes"

private def collectSourceFilesLoop (rootReal : FilePath) (rootPfx : String) :
    Nat → List (FilePath × String) → Array SourceFile → Nat → ExceptT String IO SourceBundle
  | 0, _, _, _ => throw "source directory traversal exceeded depth/file budget"
  | _, [], acc, _ => do let b : SourceBundle := { files := acc }; liftP b.validate; return b
  | fuel + 1, (dir, relPfx) :: rest, acc, totalBytes => do
      let (nextDirs, nextAcc, nextBytes) ← ((← liftIO dir.readDir).qsort (·.fileName < ·.fileName)).foldlM (init := (rest, acc, totalBytes)) fun st e => do
        let (nd, na, nb) := st; let name := e.fileName
        if name.startsWith "." || ["dist", "node_modules", "target"].contains name.toLower then return st
        let full := dir / name
        let some md ← liftIO (symlinkMetadata? full) | return st
        if md.type == .symlink then return st
        let some rp ← liftIO (realPath? full) | return st
        if !rp.toString.startsWith rootPfx then return st
        let rel := if relPfx.isEmpty then name else s!"{relPfx}/{name}"
        if md.type == .dir then return ((full, rel) :: nd, na, nb)
        else if md.type == .file && isValidSourceRelPath rel then
          if na.size >= maxSourceFiles then throw s!"project exceeds maximum of {maxSourceFiles} source files"
          liftP (checkSize rel md.byteSize.toNat (nb + md.byteSize.toNat))
          let bytes ← liftIO (IO.FS.readBinFile full)
          liftP (checkSize rel bytes.size (nb + bytes.size))
          let file : SourceFile ←
            if isBinarySourceExt name then pure { path := rel, content := encodeBase64 bytes, encoding := "base64" }
            else match String.fromUTF8? bytes with
              | some content => pure { path := rel, content, encoding := "utf8" }
              | none => if rel.toLower.endsWith ".lean" then throw s!"source file `{rel}` is not valid UTF-8"
                        else pure { path := rel, content := encodeBase64 bytes, encoding := "base64" }
          return (nd, na.push file, nb + bytes.size)
        else return st
      collectSourceFilesLoop rootReal rootPfx fuel nextDirs nextAcc nextBytes

def collectSourceBundle (rootDir : FilePath) : ExceptT String IO SourceBundle := do
  let some rootReal ← liftIO (realPath? rootDir) | throw s!"project directory not found: `{rootDir}`"
  collectSourceFilesLoop rootReal (dirPrefix rootReal) 2000 [(rootReal, "")] #[] 0

/-! ### Pure CLI Parsers & Query Builders -/

private def requireValid (ok : Bool) (msg : String) : Except String Unit := if ok then .ok () else .error msg
private def requireSlug (s : String) : Except String Unit := requireValid (isValidAppSlug s) s!"invalid app slug `{redactArg s}`"
private def requireEnv (e : String) : Except String Unit := requireValid (isValidEnvName e) s!"invalid env `{redactArg e}` (expected prod, staging, or preview)"
private def requireDeployId (id : String) : Except String Unit := requireValid (isValidDeploymentId id) s!"invalid deployment id `{redactArg id}`"
private def parsePrFlag (v : String) : Except String Nat := v.toNat?.elim (.error s!"invalid `--pr`: `{redactArg v}`") .ok

def parseCloudFlags (args : List String) : Except String (Option String × Option String × List String) := do
  let ((api?, tok?), rest) ← parseCliFlags {
    flags := [.valOk ["--api"] (fun (_, t) u => (some u, t)), .valOk ["--token"] (fun (a, _) t => (a, some t)), .passThroughVal ["--value", "--search"]],
    passDash := true, unknownErr := fun _ => "" } (none, none) args
  return (api?, tok?, rest)

def splitSecretAssignment (s : String) : Option (String × String) :=
  match s.splitOn "=" with | k :: v :: rest => some (k, "=".intercalate (v :: rest)) | _ => none

structure SecretSetParsed where
  (appSlug env name : String)
  value? : Option String
deriving Inhabited, BEq

private def parseSecretsPos (subCmd : String) (args : List String) (allowVal needTarget : Bool) :
    Except String (String × Option String × Option String × Option String) := do
  let flags : List (CliFlagSpec (Option String × Option String × Option String)) :=
    [.valOk ["--app"] (fun (_, e, v) a => (some a, e, v)), .valOk ["--env"] (fun (a, _, v) e => (a, some e, v))] ++
    (if allowVal then [.valOk ["--value"] (fun (a, e, _) v => (a, e, some v))] else [])
  let ((appFlag?, envFlag?, valFlag?), pos) ← parseCliFlags { flags, unknownErr := fun x => s!"unknown `qed secrets {subCmd}` flag: `{redactArg x}`" } (none, none, none) args
  let usage := s!"usage: qed secrets {subCmd} <app>{if needTarget then if allowVal then " <NAME|KEY=VALUE>" else " <NAME>" else ""} [--env prod|staging|preview]{if allowVal then " [--value <val>]" else ""}"
  match needTarget, appFlag?, pos with
  | true, some a, [t] | true, none, [a, t] => .ok (a, envFlag?, valFlag?, some t)
  | false, some a, [] | false, none, [a] => .ok (a, envFlag?, valFlag?, none)
  | true, some _, [] => .error (if allowVal then "missing secret `<NAME>` or `KEY=VALUE`" else usage)
  | _, _, _ => .error (if allowVal && pos.length > (if appFlag?.isSome then 1 else 2) then "too many positional arguments to `qed secrets set`" else usage)

def parseSecretsSetArgs (args : List String) : Except String SecretSetParsed := do
  let (appSlug, envFlag?, valFlag?, some target) ← parseSecretsPos "set" args true true | .error "missing secret `<NAME>` or `KEY=VALUE`"
  match splitSecretAssignment target with
  | some (k, v) => if valFlag?.isSome then .error "cannot combine `KEY=VALUE` with `--value`" else .ok { appSlug, env := envFlag?.getD "prod", name := k, value? := some v }
  | none => .ok { appSlug, env := envFlag?.getD "prod", name := target, value? := valFlag? }

structure LogsCliOpts where
  target : String := ""
  (runtime follow : Bool := false)
  envStr : String := "prod"
  pr : Nat := 0
  (severity? search? : Option String := none)
deriving Inhabited, BEq

def parseLogsArgs (args : List String) : Except String LogsCliOpts := do
  let ((o, hasRuntimeFlag, hasPrFlag), pos) ← parseCliFlags (σ := LogsCliOpts × Bool × Bool) {
    flags := [.bool ["--runtime"] (fun (o, hr, hp) => ({ o with runtime := true }, hr, hp)), .bool ["--follow", "-f"] (fun (o, hr, hp) => ({ o with follow := true }, hr, hp)),
      .valOk ["--env"] (fun (o, _, hp) v => ({ o with envStr := v }, true, hp)), .val ["--pr"] (fun (o, _, _) v => (parsePrFlag v).map fun n => ({ o with pr := n }, true, true)),
      .valOk ["--severity"] (fun (o, _, hp) v => ({ o with severity? := some v.toLower }, true, hp)), .valOk ["--search"] (fun (o, _, hp) v => ({ o with search? := some v }, true, hp))],
    unknownErr := fun x => s!"unknown `qed logs` flag: `{redactArg x}`" } ({}, false, false) args
  let [target] := pos | .error (if pos.isEmpty then "usage: qed logs <deployment-id> [--follow] | qed logs <app-slug> --runtime [--env prod|staging|preview] [--pr <N>] [--severity info|warn|error|debug] [--search <q>] [--follow]" else "too many positional arguments to `qed logs`")
  let o := { o with target }
  if !o.runtime then requireValid (!hasRuntimeFlag) "`--env`, `--pr`, `--severity`, and `--search` require `--runtime`"; requireDeployId o.target
  else
    requireSlug o.target; requireEnv o.envStr
    requireValid (!(o.envStr == "preview" && o.pr == 0)) "preview runtime logs require `--pr <positive-number>`"
    requireValid (!(o.envStr != "preview" && (hasPrFlag || o.pr != 0))) "`--pr` is only valid with `--env preview`"
    if let some sev := o.severity? then requireValid (isValidLogSeverity sev) s!"invalid severity `{redactArg sev}` (expected debug, info, warn, or error)"
  .ok o

def buildRuntimeLogsPath (appSlug envStr : String) (pr : Nat := 0) (severity? : Option String := none) (search? : Option String := none) : String :=
  let optP (k : String) (v? : Option String) (f : String → String := id) := v?.bind fun s => if s.isEmpty then none else some s!"{k}={Qed.encodeSeg (f s)}"
  "/api/v1/logs/runtime?" ++ "&".intercalate ([some s!"app={Qed.encodeSeg appSlug}", some s!"env={Qed.encodeSeg envStr}",
    if pr > 0 then some s!"pr={pr}" else none, optP "severity" severity? String.toLower, optP "search" search?].filterMap id)

/-! ### CLI Commands -/

@[noinline, nospecialize]
private def pollUntil {σ α : Type} (intervalMs : UInt32) (onTimeout : ExceptT String IO α)
    (stepFn : σ → ExceptT String IO (Sum α σ)) : Nat → σ → ExceptT String IO α
  | 0, _ => onTimeout
  | fuel + 1, st => do match ← stepFn st with | .inl done => return done | .inr next => liftIO (IO.sleep intervalMs); pollUntil intervalMs onTimeout stepFn fuel next

@[noinline, nospecialize]
private def withCloudAuthM {α : Type} (args : List String) (parse : List String → ExceptT String IO α)
    (f : α → String → CloudCredentials → ExceptT String IO UInt32) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args); let parsed ← parse rest
  let (apiBase, creds) ← resolveCloudAuth flagApi? flagTok?; f parsed apiBase creds

@[noinline, nospecialize]
private def withCloudAuth {α : Type} (args : List String) (parse : List String → Except String α)
    (f : α → String → CloudCredentials → ExceptT String IO UInt32) : ExceptT String IO UInt32 :=
  withCloudAuthM args (fun rest => liftP (parse rest)) f

private def rejectLeadingDashFlags (cmdName : String) (args : List String) : Except String Unit :=
  match args.find? (·.startsWith "-") with | some f => .error s!"unknown `{cmdName}` flag: `{redactArg f}`" | none => .ok ()

private def runLogin (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  if flagTok?.isSome then throw "`--token` is not valid for `qed login`"
  if let some f := rest.find? (· != "--no-open") then throw s!"unknown `qed login` flag: `{redactArg f}`"
  let apiBase ← resolveApiBase flagApi? (← liftIO loadCredentials?)
  liftIO (step s!"starting Qed Cloud login at {apiBase}")
  let start : DeviceStartResp ← cloudHttpJson apiBase "POST" "/api/v1/cli/device" none (some (.obj []))
  liftIO <| do IO.println s!"\n  Confirmation code: {bold start.userCode}\n  Approve in browser: {start.verifyUrl}\n"; (← IO.getStdout).flush
  if !rest.contains "--no-open" then
    let opener := if System.Platform.isOSX then "open" else "xdg-open"
    if ← liftIO (onPath opener) then discard <| liftIO (IO.Process.spawn { cmd := opener, args := #[start.verifyUrl], stdin := .null, stdout := .null, stderr := .null })
  liftIO (step "waiting for browser approval...")
  let intervalSec := max 1 (min 10 start.intervalSec)
  let poll ← pollUntil (intervalSec.toUInt32 * 1000) (throw "login timed out waiting for browser approval") (fun () => do
    let r : DevicePollResp ← cloudHttpJson apiBase "POST" "/api/v1/cli/device/poll" none (some (toJson ({ deviceCode := start.deviceCode } : DevicePollReq)))
    if r.status == "approved" then return .inl r else if r.status == "expired" then throw "device login code expired; run `qed login` again" else return .inr ()) (max 10 (min 300 (start.expiresInSec / intervalSec))) ()
  let some tok := poll.token | throw "control plane approved login without issuing a token"
  let userId := poll.userId.getD "user"; let email := poll.email.getD userId
  saveCredentials { apiBase, token := tok, userId, email }; liftIO (IO.println (green s!"✓ logged in as {email} ({apiBase})")); return 0

private def runLogout (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  if !rest.isEmpty then throw s!"unexpected arguments to `qed logout`: {" ".intercalate (rest.map redactArg)}"
  let validatedFlagApi? ← flagApi?.mapM fun raw => liftP (validateCloudApiBase raw)
  if let some tok ← resolveExplicitToken flagTok? (allowEnv := false) then
    let resp : TokenRevokeResp ← cloudHttpJson (← resolveApiBase validatedFlagApi? none) "POST" "/api/v1/tokens/revoke-current" (some tok) (some (.obj []))
    liftIO (IO.println (if resp.revoked then green "✓ token revoked" else "token was already revoked or inactive")); return 0
  let p ← liftIO credentialsPath
  if !(← liftIO p.pathExists) then liftIO (IO.println "already logged out"); return 0
  if let some creds ← liftIO loadCredentials? then if !creds.token.isEmpty then
    let storedBase := normalizeApiBase creds.apiBase
    let revokeBase? := match validatedFlagApi? with
      | some u => if !storedBase.isEmpty && storedBase == u then some u else none
      | none => if !storedBase.isEmpty && isValidCloudApiUrl storedBase then some storedBase else none
    match revokeBase? with
    | some base => liftIO do
        match ← (cloudHttpJson (α := TokenRevokeResp) base "POST" "/api/v1/tokens/revoke-current" (some creds.token) (some (.obj []))).run with
        | .ok r => if !r.revoked then IO.eprintln "warning: server reported token was already revoked or inactive"
        | .error e => IO.eprintln s!"warning: could not revoke token on server ({e})"
    | none => if let some u := validatedFlagApi? then liftIO (IO.eprintln s!"warning: stored credentials are for `{creds.apiBase}`, not `{u}`; skipping remote token revoke")
  let err? ← liftIO (try IO.FS.removeFile p; pure none catch e => pure (some (toString e)))
  if ← liftIO p.pathExists then throw s!"failed to remove credentials file `{p}`: {err?.getD "file still exists"}"
  liftIO (IO.println (green "✓ logged out of Qed Cloud")); return 0

private def runWhoami (args : List String) : ExceptT String IO UInt32 :=
  withCloudAuth args (fun rest => requireValid rest.isEmpty s!"unexpected arguments to `qed whoami`: {" ".intercalate (rest.map redactArg)}") fun () apiBase creds => do
    let me : WhoamiResp ← cloudHttpJson apiBase "GET" "/api/v1/whoami" (some creds.token)
    liftIO <| IO.println s!"{green "✓"} {me.email} (id={me.userId}, tenant={me.tenantId}, apps={me.appsCount}) @ {apiBase}"; return 0

private def runStatus (args : List String) : ExceptT String IO UInt32 :=
  withCloudAuth args (fun rest => do rejectLeadingDashFlags "qed status" rest; match rest with | [] => .ok none | [s] => requireSlug s; .ok (some s) | _ => .error "usage: qed status [app] [--api <url>] [--token <tok>]")
    fun filterSlug? apiBase creds => do
      let resp : AppsListResp ← cloudHttpJson apiBase "GET" "/api/v1/apps" (some creds.token)
      let apps := filterSlug?.elim resp.apps fun s => resp.apps.filter (·.slug == s)
      if apps.isEmpty then liftIO <| IO.println (filterSlug?.elim "no deployed apps yet. Run `qed deploy` in a Qed project." (s!"no app named `{·}`"))
      else liftIO <| apps.forM fun a => IO.println s!"  {bold a.slug}  [{a.lastStatus}]  deploys={a.deployCount}  {if a.prodUrl.isEmpty then "(no live URL yet)" else a.prodUrl}"
      return 0

private def printNewLogs (logs : Array DeployLogEntry) (lastSeq : Nat) : IO Nat := do
  let cur ← logs.foldlM (init := lastSeq) fun c entry => do
    if entry.seq > c then
      IO.println s!"  {if entry.level == "error" then red "ERR" else if entry.level == "ok" then green "OK " else "   "} {entry.message}"; return entry.seq
    return c
  (← IO.getStdout).flush; return cur

private def streamDeployLoop (apiBase token deployId : String) (fuel : Nat := 600) : ExceptT String IO DeploymentView :=
  pollUntil 1000 (throw s!"timed out waiting for deployment `{deployId}` to finish") (fun lastSeq => do
    let dv : DeploymentView ← cloudHttpJson apiBase "GET" s!"/api/v1/deployment?id={Qed.encodeSeg deployId}" (some token)
    let nextSeq ← liftIO (printNewLogs dv.logs lastSeq)
    return if ["live", "failed", "canceled"].contains dv.status then .inl dv else .inr nextSeq) fuel 0

private def formatRuntimeSeverity (sev : String) : String :=
  match sev.toLower with | "error" => red "ERROR" | "warn" | "warning" => "\x1b[33mWARN \x1b[0m" | "debug" => "\x1b[2mDEBUG\x1b[0m" | _ => green "INFO "
private def runtimeLogDedupKey (e : RuntimeLogView) : String := if e.id.isEmpty then s!"{e.timestamp}|{e.source}|{e.message}" else e.id

def filterNewRuntimeLogs (logs : Array RuntimeLogView) (seen : Std.HashSet String) : Array RuntimeLogView × Std.HashSet String :=
  logs.foldl (init := (#[], seen)) fun (acc, s) entry => let key := runtimeLogDedupKey entry; if s.contains key then (acc, s) else (acc.push entry, s.insert key)

private def printRuntimeLogs (logs : Array RuntimeLogView) (seen : Std.HashSet String) : IO (Std.HashSet String × Nat) := do
  let (fresh, nextSeen) := filterNewRuntimeLogs logs seen
  fresh.forM fun entry => IO.println s!"  {if entry.timestamp.isEmpty then "-" else entry.timestamp}  {formatRuntimeSeverity entry.severity}  [{if entry.source.isEmpty then "app" else entry.source}]  {entry.message}"
  if !fresh.isEmpty then (← IO.getStdout).flush
  return (nextSeen, fresh.size)

private def runLogs (args : List String) : ExceptT String IO UInt32 :=
  withCloudAuth args parseLogsArgs fun opts apiBase creds => do
    if opts.runtime then
      let path := buildRuntimeLogsPath opts.target opts.envStr opts.pr opts.severity? opts.search?
      if opts.follow then
        liftIO (step s!"following runtime logs for `{opts.target}` ({opts.envStr}{if opts.pr > 0 then s!" pr #{opts.pr}" else ""})")
        pollUntil 2000 (pure ()) (fun seen => do
          let resp : RuntimeLogsResp ← cloudHttpJson apiBase "GET" path (some creds.token)
          let (seen', _) ← liftIO (printRuntimeLogs resp.logs seen)
          return .inr (if seen'.size > 10000 then resp.logs.foldl (init := {}) fun acc e => acc.insert (runtimeLogDedupKey e) else seen')) 1800 {}
      else
        let resp : RuntimeLogsResp ← cloudHttpJson apiBase "GET" path (some creds.token)
        liftIO <| IO.println s!"{bold resp.appSlug} ({resp.env}{if resp.pr > 0 then s!" pr #{resp.pr}" else ""}) runtime logs"
        if resp.logs.isEmpty then liftIO (IO.println "  (no runtime logs found)") else discard <| liftIO (printRuntimeLogs resp.logs {})
      return 0
    else if opts.follow then return if (← streamDeployLoop apiBase creds.token opts.target).status == "live" then 0 else 1
    else
      let dv : DeploymentView ← cloudHttpJson apiBase "GET" s!"/api/v1/deployment?id={Qed.encodeSeg opts.target}" (some creds.token)
      liftIO <| IO.println s!"{bold dv.appSlug} ({dv.env}) [{dv.status}] id={dv.id}"; discard <| liftIO (printNewLogs dv.logs 0); return 0

private def runCancel (args : List String) : ExceptT String IO UInt32 :=
  withCloudAuth args (fun rest => do
    rejectLeadingDashFlags "qed cancel" rest
    let [deployId] := rest | .error "usage: qed cancel <deployment-id> [--api <url>] [--token <tok>]"
    requireDeployId deployId; let req : CancelDeployReq := { deploymentId := deployId }; req.validate; .ok req) fun req apiBase creds => do
      let resp : Json ← cloudHttpJson apiBase "POST" "/api/v1/deployment/cancel" (some creds.token) (some (toJson req))
      liftIO (IO.println (green s!"✓ deployment `{req.deploymentId}` {(resp.strAt? "status").getD "canceled"}")); return 0

private inductive SecretsCmd | list (appSlug : String) (env? : Option String) | set (req : SecretSetReq) | del (req : SecretDeleteReq)

private def runSecrets (args : List String) : ExceptT String IO UInt32 :=
  withCloudAuthM (α := SecretsCmd) args (fun rest => match rest with
    | "list" :: tail => liftP do
        let (appSlug, env?, _, _) ← parseSecretsPos "list" tail false false
        requireSlug appSlug; if let some e := env? then requireEnv e
        return .list appSlug env?
    | "set" :: tail => do
        let parsed ← liftP (parseSecretsSetArgs tail); liftP (validateSecretTarget parsed.appSlug parsed.env parsed.name redactArg (envHint := true))
        let secretVal ← match parsed.value? with
          | some v => pure v
          | none => match ← liftIO (IO.getEnv "QED_SECRET_VALUE") with
              | some v => if !v.isEmpty then pure v else throw "provide secret value via `KEY=VALUE`, `--value <val>`, or `QED_SECRET_VALUE` env var"
              | none => throw "provide secret value via `KEY=VALUE`, `--value <val>`, or `QED_SECRET_VALUE` env var"
        let req : SecretSetReq := { appSlug := parsed.appSlug, env := parsed.env, name := parsed.name, value := secretVal }
        liftP req.validate; return .set req
    | "delete" :: tail => liftP do
        let (appSlug, env?, _, some name) ← parseSecretsPos "delete" tail false true | .error "usage: qed secrets delete <app> <NAME> [--env prod|staging|preview]"
        let envStr := env?.getD "prod"; validateSecretTarget appSlug envStr name redactArg (envHint := true)
        let req : SecretDeleteReq := { appSlug, env := envStr, name }; req.validate; return .del req
    | _ => throw "usage: qed secrets list <app> [--env ...] | set <app> <NAME|KEY=VALUE> [--env ...] [--value <val>] | delete <app> <NAME> [--env ...]")
    fun cmd apiBase creds => match cmd with
      | .list appSlug env? => do
          let r : SecretsListResp ← cloudHttpJson apiBase "GET" s!"/api/v1/secrets?app={Qed.encodeSeg appSlug}{env?.elim "" fun e => s!"&env={Qed.encodeSeg e}"}" (some creds.token)
          let names := env?.elim r.names fun e => r.names.filter fun n => !n.contains ":" || n.startsWith s!"{e}:"
          if names.isEmpty then liftIO (IO.println s!"no secrets configured for `{appSlug}`{env?.elim "" fun e => s!" ({e})"}")
          else liftIO <| names.forM fun n => IO.println s!"  {n}"
          return 0
      | .set req => do
          let _ : Json ← cloudHttpJson apiBase "POST" "/api/v1/secrets" (some creds.token) (some (toJson req))
          liftIO (IO.println (green s!"✓ secret `{req.name}` set for `{req.appSlug}` ({req.env})")); return 0
      | .del req => do
          let _ : Json ← cloudHttpJson apiBase "POST" "/api/v1/secrets/delete" (some creds.token) (some (toJson req))
          liftIO (IO.println (green s!"✓ secret `{req.name}` deleted for `{req.appSlug}` ({req.env})")); return 0

private def runRollback (args : List String) : ExceptT String IO UInt32 :=
  withCloudAuth args (fun rest => do
    rejectLeadingDashFlags "qed rollback" rest
    let [appSlug, deploymentId] := rest | .error "usage: qed rollback <app> <deployment-id> [--api <url>] [--token <tok>]"
    requireSlug appSlug; requireDeployId deploymentId; .ok ({ appSlug, deploymentId } : RollbackReq)) fun req apiBase creds => do
      let resp : DeployUploadResp ← cloudHttpJson apiBase "POST" "/api/v1/rollback" (some creds.token) (some (toJson req))
      liftIO (IO.println (green s!"✓ rollback queued: {resp.deploymentId} ({resp.dashboardUrl})")); return 0

private structure HostedDeployOpts where
  (appSlug? mod? : Option String := none)
  envStr : String := "prod"
  pr : Nat := 0
  deployName : String := ""
  noWait : Bool := false

private def runHostedDeploy (args : List String) : ExceptT String IO UInt32 :=
  let bad (x : String) := s!"unknown or incomplete `qed deploy` flag: `{redactArg x}`"
  withCloudAuth args (fun rest => Prod.fst <$> parseCliFlags {
    flags := [.bool ["--no-wait"] ({ · with noWait := true }), .valOk ["--app"] (fun o v => { o with appSlug? := some v }),
      .valOk ["--env"] (fun o v => { o with envStr := v }), .val ["--pr"] (fun o v => (parsePrFlag v).map fun n => { o with pr := n }),
      .valOk ["--mod"] (fun o v => { o with mod? := some v }), .valOk ["--deploy"] (fun o v => { o with deployName := v })],
    allowPos := false, unknownErr := bad, missingErr := bad } ({} : HostedDeployOpts) rest) fun opts apiBase creds => do
      let appSlug ← opts.appSlug?.elim (liftIO defaultAppSlug) pure; liftP (requireSlug appSlug); liftP (requireEnv opts.envStr)
      let mod ← opts.mod?.elim (liftIO jsRoot) pure
      liftP (requireValid (isValidModuleName mod) s!"invalid root module `{redactArg mod}`")
      liftP (requireValid (opts.deployName.isEmpty || isValidModuleName opts.deployName) s!"invalid deploy spec name `{redactArg opts.deployName}`")
      liftIO (step s!"bundling verified source for `{appSlug}` (root={mod}, env={opts.envStr})")
      let bundle ← collectSourceBundle (FilePath.mk ".")
      let req : DeployUploadReq := { appSlug, env := opts.envStr, pr := opts.pr, mod, deployName := opts.deployName, bundle }; liftP req.validate
      liftIO (step s!"uploading {bundle.files.size} file(s) to Qed Cloud ({apiBase})")
      let up : DeployUploadResp ← cloudHttpJson apiBase "POST" "/api/v1/deploy" (some creds.token) (some (toJson req))
      liftIO <| IO.println s!"  deployment: {bold up.deploymentId} (tenant={up.tenantId}, app={up.appId})\n  dashboard:  {up.dashboardUrl}"
      if opts.noWait then return 0
      liftIO (step "streaming remote verification & rollout logs...")
      let final ← streamDeployLoop apiBase creds.token up.deploymentId
      if final.status == "live" then liftIO <| IO.println (green s!"✓ live at {final.url} (verified {final.verifiedDecls} decls, build {final.buildHash})"); return 0
      else if final.status == "canceled" then throw s!"deployment `{final.id}` was canceled{if final.errorMsg.isEmpty then "" else s!": {final.errorMsg}"}"
      else throw s!"deployment `{final.id}` failed: {final.errorMsg}"

def cmdHostedDeploy (args : List String) : IO UInt32 := runExceptCmd (runHostedDeploy args)

def cloudCmds : List (String × (List String → ExceptT String IO UInt32)) := [
  ("login", runLogin), ("logout", runLogout), ("whoami", runWhoami), ("status", runStatus),
  ("logs", runLogs), ("cancel", runCancel), ("secrets", runSecrets), ("rollback", runRollback)]

end Qed.Cli
