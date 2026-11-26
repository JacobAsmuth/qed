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

def redactArg (s : String) : String :=
  match s.splitOn "=" with
  | k :: _ :: _ => s!"{k}=<redacted>"
  | _           => s

private def liftP {α : Type} (e : Except String α) : ExceptT String IO α :=
  ExceptT.mk (pure e)

private def runCloudCmd (act : ExceptT String IO UInt32) : IO UInt32 := do
  match ← act.run with
  | .ok c    => return c
  | .error e => IO.eprintln (red s!"✗ {e}"); return 1

private def validateCloudApiBase (raw : String) : Except String String :=
  let u := normalizeApiBase raw
  if isValidCloudApiUrl u then .ok u
  else .error s!"invalid Qed Cloud API URL `{redactArg raw}` (must be `https://<host>[:port]` or local loopback `http://127.0.0.1[:port]`)"

private def resolveApiBase (flagApi? : Option String) (creds? : Option CloudCredentials) : ExceptT String IO String := do
  let envApi? ← liftIO (nonEmptyEnv "QED_CLOUD_API")
  let raw? := flagApi?.orElse (fun _ => envApi?) |>.orElse (fun _ => creds?.map (·.apiBase)) |>.orElse (fun _ => defaultCloudApiUrl?)
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
  match flagToken? with
  | some raw => some <$> liftP (validateExplicitToken raw)
  | none =>
      if allowEnv then
        match ← liftIO (nonEmptyEnv "QED_CLOUD_TOKEN") with
        | some raw => some <$> liftP (validateExplicitToken raw)
        | none     => pure none
      else pure none

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

private def symlinkMetadata? (p : FilePath) : IO (Option IO.FS.Metadata) :=
  try some <$> p.symlinkMetadata catch _ => pure none

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
          if metaBytes > maxSourceFileBytes then
            throw s!"source file `{rel}` exceeds {maxSourceFileBytes} bytes"
          if nextBytes + metaBytes > maxTotalSourceBytes then
            throw s!"project source exceeds {maxTotalSourceBytes} bytes"
          let bytes ← liftIO (IO.FS.readBinFile full)
          if bytes.size > maxSourceFileBytes then
            throw s!"source file `{rel}` exceeds {maxSourceFileBytes} bytes"
          nextBytes := nextBytes + bytes.size
          if nextBytes > maxTotalSourceBytes then
            throw s!"project source exceeds {maxTotalSourceBytes} bytes"
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

private def stripFlagEq? (flag : String) (arg : String) : Option String :=
  let pfx := flag ++ "="
  if arg.startsWith pfx then some (arg.drop pfx.length).toString else none

def parseCloudFlags (args : List String) : Except String (Option String × Option String × List String) :=
  let rec go (api? tok? : Option String) (acc : List String) :
      List String → Except String (Option String × Option String × List String)
    | [] => .ok (api?, tok?, acc.reverse)
    | "--api" :: u :: r => go (some u) tok? acc r
    | ["--api"] => .error "missing value for `--api`"
    | "--token" :: t :: r => go api? (some t) acc r
    | ["--token"] => .error "missing value for `--token`"
    | "--value" :: v :: r => go api? tok? (v :: "--value" :: acc) r
    | "--search" :: q :: r => go api? tok? (q :: "--search" :: acc) r
    | x :: r =>
        if let some u := stripFlagEq? "--api" x then go (some u) tok? acc r
        else if let some t := stripFlagEq? "--token" x then go api? (some t) acc r
        else go api? tok? (x :: acc) r
  go none none [] args

def splitSecretAssignment (s : String) : Option (String × String) :=
  match s.splitOn "=" with
  | k :: v :: rest => some (k, "=".intercalate (v :: rest))
  | _ => none

structure SecretSetParsed where
  appSlug : String
  env     : String
  name    : String
  value?  : Option String
deriving Inhabited, DecidableEq, Repr

def parseSecretsSetArgs (args : List String) : Except String SecretSetParsed := do
  let rec go (app? : Option String) (envStr : String) (val? : Option String) (pos : List String) :
      List String → Except String (Option String × String × Option String × List String)
    | [] => .ok (app?, envStr, val?, pos.reverse)
    | "--app" :: a :: r => go (some a) envStr val? pos r
    | ["--app"] => .error "missing value for `--app`"
    | "--env" :: e :: r => go app? e val? pos r
    | ["--env"] => .error "missing value for `--env`"
    | "--value" :: v :: r => go app? envStr (some v) pos r
    | ["--value"] => .error "missing value for `--value`"
    | x :: r =>
        if let some a := stripFlagEq? "--app" x then go (some a) envStr val? pos r
        else if let some e := stripFlagEq? "--env" x then go app? e val? pos r
        else if let some v := stripFlagEq? "--value" x then go app? envStr (some v) pos r
        else if x.startsWith "-" then .error s!"unknown `qed secrets set` flag: `{redactArg x}`"
        else go app? envStr val? (x :: pos) r
  let (appFlag?, envStr, valFlag?, pos) ← go none "prod" none [] args
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
  let rec go (app? env? : Option String) (pos : List String) :
      List String → Except String (Option String × Option String × List String)
    | [] => .ok (app?, env?, pos.reverse)
    | "--app" :: a :: r => go (some a) env? pos r
    | ["--app"] => .error "missing value for `--app`"
    | "--env" :: e :: r => go app? (some e) pos r
    | ["--env"] => .error "missing value for `--env`"
    | x :: r =>
        if let some a := stripFlagEq? "--app" x then go (some a) env? pos r
        else if let some e := stripFlagEq? "--env" x then go app? (some e) pos r
        else if x.startsWith "-" then .error s!"unknown `qed secrets {subCmd}` flag: `{redactArg x}`"
        else go app? env? (x :: pos) r
  let (appFlag?, envFlag?, pos) ← go none none [] args
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
deriving Inhabited, DecidableEq, Repr

def parseLogsArgs (args : List String) : Except String LogsCliOpts := do
  let rec go (o : LogsCliOpts) (hasRuntimeFlag hasPrFlag : Bool) (pos : List String) :
      List String → Except String (LogsCliOpts × Bool × Bool × List String)
    | [] => .ok (o, hasRuntimeFlag, hasPrFlag, pos.reverse)
    | "--runtime" :: r => go { o with runtime := true } hasRuntimeFlag hasPrFlag pos r
    | "--follow" :: r | "-f" :: r => go { o with follow := true } hasRuntimeFlag hasPrFlag pos r
    | "--env" :: v :: r => go { o with envStr := v } true hasPrFlag pos r
    | ["--env"] => .error "missing value for `--env`"
    | "--pr" :: v :: r =>
        match v.toNat? with
        | some n => go { o with pr := n } true true pos r
        | none   => .error s!"invalid `--pr`: `{redactArg v}`"
    | ["--pr"] => .error "missing value for `--pr`"
    | "--severity" :: v :: r => go { o with severity? := some v.toLower } true hasPrFlag pos r
    | ["--severity"] => .error "missing value for `--severity`"
    | "--search" :: v :: r => go { o with search? := some v } true hasPrFlag pos r
    | ["--search"] => .error "missing value for `--search`"
    | x :: r =>
        if let some v := stripFlagEq? "--env" x then go { o with envStr := v } true hasPrFlag pos r
        else if let some v := stripFlagEq? "--pr" x then
          match v.toNat? with
          | some n => go { o with pr := n } true true pos r
          | none   => .error s!"invalid `--pr`: `{redactArg v}`"
        else if let some v := stripFlagEq? "--severity" x then go { o with severity? := some v.toLower } true hasPrFlag pos r
        else if let some v := stripFlagEq? "--search" x then go { o with search? := some v } true hasPrFlag pos r
        else if x.startsWith "-" then .error s!"unknown `qed logs` flag: `{redactArg x}`"
        else go o hasRuntimeFlag hasPrFlag (x :: pos) r
  let (o, hasRuntimeFlag, hasPrFlag, pos) ← go {} false false [] args
  let target ← match pos with
    | [t] => .ok t
    | []  => .error "usage: qed logs <deployment-id> [--follow] | qed logs <app-slug> --runtime [--env prod|staging|preview] [--pr <N>] [--severity info|warn|error|debug] [--search <q>] [--follow]"
    | _   => .error "too many positional arguments to `qed logs`"
  let o := { o with target }
  if !o.runtime then
    if hasRuntimeFlag then .error "`--env`, `--pr`, `--severity`, and `--search` require `--runtime`"
    if !isValidDeploymentId o.target then .error s!"invalid deployment id `{redactArg o.target}`"
  else
    if !isValidAppSlug o.target then .error s!"invalid app slug `{redactArg o.target}`"
    if !isValidEnvName o.envStr then .error s!"invalid env `{redactArg o.envStr}` (expected prod, staging, or preview)"
    if o.envStr == "preview" && o.pr == 0 then .error "preview runtime logs require `--pr <positive-number>`"
    if o.envStr != "preview" && (hasPrFlag || o.pr != 0) then .error "`--pr` is only valid with `--env preview`"
    if let some sev := o.severity? then
      if !isValidLogSeverity sev then .error s!"invalid severity `{redactArg sev}` (expected debug, info, warn, or error)"
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

private def validateSecretMeta (appSlug envStr name : String) : Except String Unit := do
  if !isValidAppSlug appSlug then .error s!"invalid app slug `{redactArg appSlug}`"
  if !isValidEnvName envStr then .error s!"invalid env `{redactArg envStr}` (expected prod, staging, or preview)"
  if !isValidSecretKey name then .error s!"invalid secret name `{redactArg name}` (use UPPER_SNAKE_CASE)"

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

def cmdLogin (args : List String) : IO UInt32 := runCloudCmd (runLogin args)

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

def cmdLogout (args : List String := []) : IO UInt32 := runCloudCmd (runLogout args)

private def runWhoami (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  if !rest.isEmpty then throw s!"unexpected arguments to `qed whoami`: {" ".intercalate (rest.map redactArg)}"
  let (apiBase, creds) ← resolveCloudAuth flagApi? flagTok?
  let me : WhoamiResp ← cloudHttpJson apiBase "GET" "/api/v1/whoami" (some creds.token)
  liftIO <| IO.println s!"{green "✓"} {me.email} (id={me.userId}, tenant={me.tenantId}, apps={me.appsCount}) @ {apiBase}"
  return 0

def cmdWhoami (args : List String) : IO UInt32 := runCloudCmd (runWhoami args)

private def runStatus (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  liftP (rejectLeadingDashFlags "qed status" rest)
  let filterSlug? ← match rest with
    | []  => pure none
    | [s] =>
        if !isValidAppSlug s then throw s!"invalid app slug `{redactArg s}`"
        pure (some s)
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

def cmdStatus (args : List String) : IO UInt32 := runCloudCmd (runStatus args)

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

def cmdLogs (args : List String) : IO UInt32 := runCloudCmd (runLogs args)

private def runCancel (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  liftP (rejectLeadingDashFlags "qed cancel" rest)
  let [deployId] := rest | throw "usage: qed cancel <deployment-id> [--api <url>] [--token <tok>]"
  if !isValidDeploymentId deployId then throw s!"invalid deployment id `{redactArg deployId}`"
  let req : CancelDeployReq := { deploymentId := deployId }
  liftP req.validate
  let (apiBase, creds) ← resolveCloudAuth flagApi? flagTok?
  let resp : Json ← cloudHttpJson apiBase "POST" "/api/v1/deployment/cancel" (some creds.token) (some (toJson req))
  let st := (resp.strAt? "status").getD "canceled"
  liftIO (IO.println (green s!"✓ deployment `{deployId}` {st}"))
  return 0

def cmdCancel (args : List String) : IO UInt32 := runCloudCmd (runCancel args)

private def runSecrets (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  match rest with
  | "list" :: tail =>
      let (appSlug, env?, _) ← liftP (parseSecretsAppEnvArgs "list" tail false)
      if !isValidAppSlug appSlug then throw s!"invalid app slug `{redactArg appSlug}`"
      if let some e := env? then
        if !isValidEnvName e then throw s!"invalid env `{redactArg e}` (expected prod, staging, or preview)"
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
      liftP (validateSecretMeta parsed.appSlug parsed.env parsed.name)
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
      liftP (validateSecretMeta appSlug envStr name)
      let req : SecretDeleteReq := { appSlug, env := envStr, name }
      liftP req.validate
      let (apiBase, creds) ← resolveCloudAuth flagApi? flagTok?
      let _ : Json ← cloudHttpJson apiBase "POST" "/api/v1/secrets/delete" (some creds.token) (some (toJson req))
      liftIO (IO.println (green s!"✓ secret `{req.name}` deleted for `{req.appSlug}` ({req.env})"))
      return 0
  | _ => throw "usage: qed secrets list <app> [--env ...] | set <app> <NAME|KEY=VALUE> [--env ...] [--value <val>] | delete <app> <NAME> [--env ...]"

def cmdSecrets (args : List String) : IO UInt32 := runCloudCmd (runSecrets args)

private def runRollback (args : List String) : ExceptT String IO UInt32 := do
  let (flagApi?, flagTok?, rest) ← liftP (parseCloudFlags args)
  liftP (rejectLeadingDashFlags "qed rollback" rest)
  let [appSlug, deploymentId] := rest | throw "usage: qed rollback <app> <deployment-id> [--api <url>] [--token <tok>]"
  if !isValidAppSlug appSlug then throw s!"invalid app slug `{redactArg appSlug}`"
  if !isValidDeploymentId deploymentId then throw s!"invalid deployment id `{redactArg deploymentId}`"
  let (apiBase, creds) ← resolveCloudAuth flagApi? flagTok?
  let resp : DeployUploadResp ← cloudHttpJson apiBase "POST" "/api/v1/rollback" (some creds.token)
    (some (toJson ({ appSlug, deploymentId } : RollbackReq)))
  liftIO (IO.println (green s!"✓ rollback queued: {resp.deploymentId} ({resp.dashboardUrl})"))
  return 0

def cmdRollback (args : List String) : IO UInt32 := runCloudCmd (runRollback args)

private structure HostedDeployOpts where
  api?        : Option String := none
  token?      : Option String := none
  appSlug?    : Option String := none
  envStr      : String := "prod"
  pr          : Nat := 0
  mod?        : Option String := none
  deployName  : String := ""
  noWait      : Bool := false

private def parseHostedDeployOpts : List String → HostedDeployOpts → Except String HostedDeployOpts
  | [], o => .ok o
  | "--api" :: v :: r, o => parseHostedDeployOpts r { o with api? := some v }
  | "--token" :: v :: r, o => parseHostedDeployOpts r { o with token? := some v }
  | "--app" :: v :: r, o => parseHostedDeployOpts r { o with appSlug? := some v }
  | "--env" :: v :: r, o => parseHostedDeployOpts r { o with envStr := v }
  | "--pr" :: v :: r, o => match v.toNat? with | some n => parseHostedDeployOpts r { o with pr := n } | none => .error s!"invalid `--pr`: `{redactArg v}`"
  | "--mod" :: v :: r, o => parseHostedDeployOpts r { o with mod? := some v }
  | "--deploy" :: v :: r, o => parseHostedDeployOpts r { o with deployName := v }
  | "--no-wait" :: r, o => parseHostedDeployOpts r { o with noWait := true }
  | x :: r, o =>
      if let some v := stripFlagEq? "--api" x then parseHostedDeployOpts r { o with api? := some v }
      else if let some v := stripFlagEq? "--token" x then parseHostedDeployOpts r { o with token? := some v }
      else if let some v := stripFlagEq? "--app" x then parseHostedDeployOpts r { o with appSlug? := some v }
      else if let some v := stripFlagEq? "--env" x then parseHostedDeployOpts r { o with envStr := v }
      else if let some v := stripFlagEq? "--pr" x then
        match v.toNat? with
        | some n => parseHostedDeployOpts r { o with pr := n }
        | none   => .error s!"invalid `--pr`: `{redactArg v}`"
      else if let some v := stripFlagEq? "--mod" x then parseHostedDeployOpts r { o with mod? := some v }
      else if let some v := stripFlagEq? "--deploy" x then parseHostedDeployOpts r { o with deployName := v }
      else .error s!"unknown or incomplete `qed deploy` flag: `{redactArg x}`"

private def runHostedDeploy (args : List String) : ExceptT String IO UInt32 := do
  let opts ← liftP (parseHostedDeployOpts args {})
  let (apiBase, creds) ← resolveCloudAuth opts.api? opts.token?
  let appSlug ← match opts.appSlug? with | some s => pure s | none => liftIO defaultAppSlug
  if !isValidAppSlug appSlug then throw s!"invalid app slug `{redactArg appSlug}`"
  if !isValidEnvName opts.envStr then throw s!"invalid env `{redactArg opts.envStr}` (expected prod, staging, or preview)"
  let mod ← match opts.mod? with | some m => pure m | none => liftIO jsRoot
  if mod.isEmpty || mod.length > 128 || !mod.toList.all (fun c => c.isAlphanum || c == '.' || c == '_') then
    throw s!"invalid root module `{redactArg mod}`"
  if !opts.deployName.isEmpty && (opts.deployName.length > 128 || !opts.deployName.toList.all (fun c => c.isAlphanum || c == '.' || c == '_')) then
    throw s!"invalid deploy spec name `{redactArg opts.deployName}`"
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

def cmdHostedDeploy (args : List String) : IO UInt32 := runCloudCmd (runHostedDeploy args)

end Qed.Cli
