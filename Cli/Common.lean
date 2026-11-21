open System (FilePath)

def String.cliTrim (s : String) : String :=
  s.trimAscii.toString

namespace Qed.Cli

def devDir         : FilePath := ".qed" / "dev"
def distDir        : FilePath := "dist"
def devPort        : String := "8000"
def axiomsManifest : FilePath := "scripts" / "axioms.lean"

def env (k : String) : IO (Option String) := IO.getEnv k
def frameworkHome : IO FilePath := return (← env "QED_HOME").getD "."
def runtimeFile (name : String) : IO FilePath := return (← frameworkHome) / "runtime" / name

def webRoot : IO String := do
  if let some r ← env "QED_WEB_ROOT" then return r
  if (← (FilePath.mk "Web.lean").pathExists) then return "Web"
  if (← (FilePath.mk "App.lean").pathExists) then return "App"
  if (← (FilePath.mk "Examples" / "Counter.lean").pathExists) then
    return "Examples.Counter"
  return "App"

def jsRoot : IO String := do
  match ← env "QED_JS_ROOT" with
  | some r => return r
  | none   => webRoot

def takeIdentChars (s : String) : String :=
  (s.takeWhile fun c => c.isAlphanum || c == '.' || c == '_' || c == '\'').toString

private def scanModuleTokens {α : Type} (mod : String) (init : α)
    (onLine : List String → List String → α → Except α α) : IO α := do
  let path := FilePath.mk ((mod.replace "." "/") ++ ".lean")
  if !(← path.pathExists) then return init
  let src ← IO.FS.readFile path
  let mut depth : Nat := 0
  let mut nsStack : List String := []
  let mut acc := init
  for raw in src.splitOn "\n" do
    let inComment := depth > 0
    depth := depth + ((raw.splitOn "/-").length - 1) - ((raw.splitOn "-/").length - 1)
    if inComment then continue
    let code := (raw.splitOn "--").headD raw
    let toks := ((code.replace "\t" " ").splitOn " ").filter (· != "")
    match toks with
    | "namespace" :: ns :: _ =>
        let cleanNs := takeIdentChars ns
        if !cleanNs.isEmpty then nsStack := cleanNs :: nsStack
    | "end" :: _ =>
        nsStack := nsStack.drop 1
    | _ =>
        match onLine nsStack toks acc with
        | .error done => return done
        | .ok next    => acc := next
  return acc

def fullstackAppName (mod : String) : IO (Option String) :=
  scanModuleTokens mod none fun nsStack toks _ =>
    match toks with
    | "fullstack" :: rawName :: _ =>
        let fs := takeIdentChars rawName
        if fs.isEmpty then .ok none
        else .error (some (String.intercalate "." (nsStack.reverse ++ [fs])))
    | _ => .ok none

def ssrAppName (mod : String) : IO (Option String) := do
  let path := FilePath.mk ((mod.replace "." "/") ++ ".lean")
  if !(← path.pathExists) then return none
  let src ← IO.FS.readFile path
  match src.splitOn "Qed.run " with
  | _ :: rest :: _ =>
      let name := takeIdentChars (rest.dropWhile (· == ' ')).toString
      return if name.isEmpty then none else some name
  | _ => return none

def componentAppName (mod : String) : IO (Option String) := do
  let (lastTop, lastAny) ← scanModuleTokens mod (none, none) fun nsStack toks (lastTop, lastAny) =>
    match toks with
    | "component" :: rawName :: _ =>
        let cName := takeIdentChars rawName
        if cName.isEmpty then .ok (lastTop, lastAny)
        else
          let top' := if nsStack.isEmpty then some s!"{cName}.app" else lastTop
          let any' := some (String.intercalate "." (nsStack.reverse ++ [cName, "app"]))
          .ok (top', any')
    | _ => .ok (lastTop, lastAny)
  return lastTop.orElse (fun _ => lastAny)

inductive AppMode where
  | fullstack (fsName : String)
  | ssr (appName : String)
  | component (appName : String)
  | raw

def resolveAppMode (mod : String) : IO AppMode := do
  if let some fsName ← fullstackAppName mod then return .fullstack fsName
  if let some appName ← ssrAppName mod then return .ssr appName
  if let some appName ← componentAppName mod then return .component appName
  return .raw

def driverEntries : Array String := #[
  "main:__main",
  "Qed.qedInit:qed_init", "Qed.qedDispatch:qed_dispatch", "Qed.qedDispatchStr:qed_dispatch_str",
  "Qed.qedStreamChunk:qed_stream_chunk", "Qed.qedStreamDone:qed_stream_done",
  "Qed.qedHttpDone:qed_http_done", "Qed.qedHttpBytesDone:qed_http_bytes_done",
  "Qed.qedUrlChanged:qed_url_changed",
  "Qed.qedLocalDispatch:qed_local_dispatch", "Qed.qedLocalDispatchStr:qed_local_dispatch_str",
  "Qed.qedLocalSnapshot:qed_local_snapshot", "Qed.qedLocalRestore:qed_local_restore",
  "Qed.qedDehydrate:qed_dehydrate",
  "Qed.qedEffectDone:qed_effect_done", "Qed.qedPortRecv:qed_port_recv",
  "Qed.qedWsOpen:qed_ws_open", "Qed.qedWsBytes:qed_ws_bytes",
  "Qed.qedWsText:qed_ws_text", "Qed.qedWsClose:qed_ws_close"]

def bold   (s : String) : String := s!"\x1b[1m{s}\x1b[0m"
def green  (s : String) : String := s!"\x1b[32m{s}\x1b[0m"
def red    (s : String) : String := s!"\x1b[31m{s}\x1b[0m"
def step   (s : String) : IO Unit := IO.println (bold s!"▸ {s}")

private def useColor : IO Bool := do
  match ← env "NO_COLOR" with
  | some v => return v.isEmpty
  | none   => return true

private def paint (enabled : Bool) (code s : String) : String :=
  if enabled then s!"\x1b[{code}m{s}\x1b[0m" else s

/-- Parses a Lean diagnostic header line like `error: File.lean:12:4: msg` or
    `File.lean:12:4: error: msg` into `(severity, path, line, col, msg)`. -/
private def parseLeanDiagLine (line : String) : Option (String × String × Nat × Nat × String) := do
  let parseLocMsg (sev rest : String) : Option (String × String × Nat × Nat × String) := do
    match rest.splitOn ":" with
    | path :: lnS :: colS :: msgParts =>
        let ln ← lnS.cliTrim.toNat?
        let col ← colS.cliTrim.toNat?
        some (sev, path.cliTrim, ln, col, (String.intercalate ":" msgParts).cliTrim)
    | _ => none
  -- Handle `error(lean.xxx): File.lean:12:4: msg`
  if line.startsWith "error(" then
    match line.splitOn "): " with
    | _ :: restParts => return ← parseLocMsg "error" (String.intercalate "): " restParts)
    | _ => failure
  for (pfx, sev) in [("error:", "error"), ("warning:", "warning")] do
    if line.startsWith pfx then
      if let some r := parseLocMsg sev (line.drop pfx.length).toString.cliTrim then return r
  -- Handle `File.lean:12:4: error: msg`
  match line.splitOn ":" with
  | path :: lnS :: colS :: sevS :: msgParts =>
      if path.endsWith ".lean" then
        let sev := sevS.cliTrim
        if sev == "error" || sev == "warning" then
          return ← parseLocMsg sev (String.intercalate ":" (path :: lnS :: colS :: msgParts))
      failure
  | _ => failure

private def readSourceSnippet (path : String) (ln col : Nat) (color : Bool) : IO String := do
  let fp : FilePath := path
  if !(← fp.pathExists) || ln == 0 then return ""
  try
    let content ← IO.FS.readFile fp
    let lines := (content.splitOn "\n").toArray
    if ln > lines.size then return ""
    let srcLine := lines[ln - 1]!
    let prevLine? := if ln >= 2 then some lines[ln - 2]! else none
    let gutterW := max 3 (toString ln).length
    let padNum (n : Nat) : String :=
      let s := toString n
      String.ofList (List.replicate (gutterW - s.length) ' ') ++ s
    let blankGutter := String.ofList (List.replicate gutterW ' ')
    let bar := paint color "2" "|"
    let caretPad := String.ofList (List.replicate col ' ')
    let caret := paint color "1;31" "^"
    let mut out := ""
    if let some pl := prevLine? then
      if !pl.cliTrim.isEmpty then
        out := out ++ s!"  {paint color "2" (padNum (ln - 1))} {bar} {paint color "2" pl}\n"
    out := out ++ s!"  {paint color "1" (padNum ln)} {bar} {srcLine}\n"
    out := out ++ s!"  {blankGutter} {bar} {caretPad}{caret}\n"
    return out
  catch _ => return ""

initialize lastBuildErrorRef : IO.Ref String ← IO.mkRef ""

def clearLastBuildError : IO Unit := lastBuildErrorRef.set ""
def getLastBuildError : IO String := lastBuildErrorRef.get

/-- Formats raw Lake / Lean compiler output into clean, readable terminal diagnostics:
    strips `trace: .> LEAN_PATH=...` noise and redundant build-failure footers, adds ANSI
    colors when `allowColor` is true, and displays source snippets with caret pointers for `.lean` errors. -/
def formatLakeDiagnostics (raw : String) (allowColor : Bool := true) : IO String := do
  if (← env "QED_VERBOSE") == some "1" && allowColor then return raw
  let color := allowColor && (← useColor)
  let lines := raw.splitOn "\n"
  let mut out : Array String := #[]
  let mut skipTargetBullets := false
  let mut hasPrettyDiag := false
  for line in lines do
    let t := line.cliTrim
    if t.startsWith "trace: .>" ||
       t == "error: Lean exited with code 1" ||
       t == "error: build failed" ||
       t == "info: stderr:" ||
       t.startsWith "✔ [" ||
       t.startsWith "ℹ [" then
      continue
    if t == "Some required targets logged failures:" then
      skipTargetBullets := true
      continue
    if skipTargetBullets then
      if t.startsWith "- " then continue
      else skipTargetBullets := false
    if t.startsWith "✖ [" then
      continue
    match parseLeanDiagLine line with
    | some (sev, path, ln, col, msg) =>
        if msg == "could not synthesize default value for parameter 'hvalid' using tactics" ||
           msg == "could not synthesize default value for parameter 'valid_view' using tactics" ||
           msg == "could not synthesize default value for parameter 'hview' using tactics" ||
           msg == "could not synthesize default value for parameter 'hpres' using tactics" then
          continue
        hasPrettyDiag := true
        let sevTag := if sev == "error" then paint color "1;31" "error" else paint color "1;33" "warning"
        let locTag := paint color "1" s!"{path}:{ln}:{col}"
        let snippet ← readSourceSnippet path ln col color
        if !out.isEmpty then out := out.push ""
        out := out.push s!"{sevTag}: {locTag}"
        if !snippet.isEmpty then
          let trimmedSnip := if snippet.endsWith "\n" then String.ofList snippet.toList.dropLast else snippet
          out := out.push trimmedSnip
        if !msg.isEmpty then
          out := out.push s!"  {msg}"
    | none =>
        if t.startsWith "Hint:" then
          let rest := (t.drop 5).toString
          out := out.push s!"  {paint color "1;36" "Hint:"}{rest}"
        else if t.startsWith "• " then
          let rest := (t.drop 2).toString
          out := out.push s!"    {paint color "1;31" "•"} {rest}"
        else if hasPrettyDiag && !t.isEmpty then
          out := out.push s!"  {line}"
        else if !t.isEmpty then
          out := out.push line
  let formatted := String.intercalate "\n" out.toList
  if formatted.cliTrim.isEmpty then return raw else return formatted ++ "\n"

def sh (cmd : String) (args : Array String) (extraEnv : Array (String × Option String) := #[]) : IO UInt32 := do
  let child ← IO.Process.spawn
    { cmd := cmd, args := args, env := extraEnv, stdin := .inherit, stdout := .inherit, stderr := .inherit }
  child.wait

def shOut (cmd : String) (args : Array String) (extraEnv : Array (String × Option String) := #[]) : IO (UInt32 × String) := do
  let o ← IO.Process.output { cmd := cmd, args := args, env := extraEnv }
  return (o.exitCode, o.stdout ++ o.stderr)

def shQuiet (cmd : String) (args : Array String) (extraEnv : Array (String × Option String) := #[]) : IO UInt32 := do
  let (code, out) ← shOut cmd args extraEnv
  if code != 0 then IO.eprint out
  return code

private def shDiag (cmd : String) (args : Array String) (extraEnv : Array (String × Option String) := #[]) : IO UInt32 := do
  let (code, out) ← shOut cmd args extraEnv
  if code != 0 then
    IO.eprint (← formatLakeDiagnostics out true)
    lastBuildErrorRef.set (← formatLakeDiagnostics out false)
  return code

def shLakeBuild (args : Array String) : IO UInt32 := shDiag "lake" args

def shLean (leanPath : String) (args : Array String) : IO UInt32 :=
  shDiag "lean" args #[("LEAN_PATH", some leanPath)]

def onPath (cmd : String) : IO Bool := do
  return (← shOut "bash" #["-c", s!"command -v {cmd}"]).1 == 0

partial def collect (dir : FilePath) (ext : String) (skipDirs : List String := []) :
    IO (Array FilePath) := do
  if !(← dir.pathExists) then return #[]
  let mut acc : Array FilePath := #[]
  for entry in (← dir.readDir) do
    let p := entry.path
    if (← p.isDir) then
      if (p.fileName.getD "") ∉ skipDirs then
        acc := acc ++ (← collect p ext skipDirs)
    else if p.extension == some ext then
      acc := acc.push p
  return acc

private def escapeJsonStr (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if c == '\n' then out := out ++ "\\n"
    else if c == '\r' then out := out ++ "\\r"
    else if c == '\t' then out := out ++ "\\t"
    else if c.toNat < 32 then pure ()
    else out := out.push c
  return out

def writeDevStatusJson (outDir : FilePath) (status : String) (kind : String := "hmr")
    (errText : String := "") (durationMs : Nat := 0) (bumpId : Bool := true)
    (sseUrl : String := "") : IO String := do
  IO.FS.createDirAll outDir
  let buildIdPath := outDir / "__build_id"
  let idStr ←
    if bumpId || !(← buildIdPath.pathExists) then
      let id := toString (← IO.monoMsNow)
      IO.FS.writeFile buildIdPath id
      pure id
    else
      pure (← IO.FS.readFile buildIdPath).cliTrim
  let sseField := if sseUrl.isEmpty then "" else s!",\"sseUrl\":\"{escapeJsonStr sseUrl}\""
  let json :=
    s!"\{\"id\":\"{escapeJsonStr idStr}\"," ++
    s!"\"status\":\"{escapeJsonStr status}\"," ++
    s!"\"kind\":\"{escapeJsonStr kind}\"," ++
    s!"\"durationMs\":{durationMs}," ++
    s!"\"error\":\"{escapeJsonStr errText}\"{sseField}}\n"
  let tmp := outDir / "__dev_status.tmp"
  IO.FS.writeFile tmp json
  IO.FS.rename tmp (outDir / "__dev_status")
  return json

def writeIfChanged (path : FilePath) (content : String) : IO Bool := do
  if (← path.pathExists) then
    if (← IO.FS.readFile path) == content then
      return false
  IO.FS.writeFile path content
  return true

initialize leanPathCache : IO.Ref (Option String) ← IO.mkRef none

def mtimeNs (p : FilePath) : IO (Option Int) := do
  if !(← p.pathExists) then return none
  try
    let m ← p.metadata
    return some (m.modified.sec * 1000000000 + Int.ofNat m.modified.nsec.toNat)
  catch _ => return none

def isUpToDate (out : FilePath) (deps : Array FilePath) : IO Bool := do
  let some outT ← mtimeNs out | return false
  for d in deps do
    let some dt ← mtimeNs d | return false
    if dt > outT then return false
  return true

def lakeEnvLeanPath : IO (Option String) := do
  if let some lp ← leanPathCache.get then return some lp
  if let some lp ← env "LEAN_PATH" then
    let trimmed := lp.cliTrim
    if !trimmed.isEmpty then
      leanPathCache.set (some trimmed)
      return some trimmed
  let isInRepo ← (FilePath.mk "Examples").pathExists
  let hasPkgs ← (FilePath.mk ".lake" / "packages").pathExists
  if isInRepo && !hasPkgs then
    let o ← IO.Process.output { cmd := "lean", args := #["--print-libdir"] }
    if o.exitCode == 0 then
      let sysLib := o.stdout.cliTrim
      if !sysLib.isEmpty then
        let cwd ← IO.currentDir
        let lp := s!"{cwd / ".lake" / "build" / "lib" / "lean"}:{sysLib}"
        leanPathCache.set (some lp)
        return some lp
  let o ← IO.Process.output { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"] }
  if o.exitCode != 0 then
    IO.eprint (o.stdout ++ o.stderr)
    return none
  let trimmed := o.stdout.cliTrim
  leanPathCache.set (some trimmed)
  return some trimmed

def lakeQueryPaths (targets : Array String) : IO (Option (Array String)) := do
  let o ← IO.Process.output { cmd := "lake", args := #["query"] ++ targets }
  if o.exitCode != 0 then
    IO.eprint (o.stdout ++ o.stderr)
    return none
  let paths := (o.stdout.splitOn "\n").toArray.map String.cliTrim |>.filter (!·.isEmpty)
  return some paths

def resolveQedjsBin (needBuild : Bool := true) : IO (Option FilePath) := do
  let qh ← frameworkHome
  let prebuilt := qh / ".lake" / "build" / "bin" / "qedjs"
  let isInRepo ← (FilePath.mk "Examples").pathExists
  if isInRepo && (!needBuild || (← env "QED_PREBUILT") == some "1") && (← prebuilt.pathExists) then
    return some prebuilt
  if !isInRepo && (← prebuilt.pathExists) then
    let tcMatch ← do
      let appTc : FilePath := "lean-toolchain"
      let fwTc := qh / "lean-toolchain"
      if (← appTc.pathExists) && (← fwTc.pathExists) then
        pure ((← IO.FS.readFile appTc).cliTrim == (← IO.FS.readFile fwTc).cliTrim)
      else pure false
    if tcMatch then return some prebuilt
  let target := if isInRepo then "qedjs" else "qed/qedjs"
  if needBuild then
    if (← shQuiet "lake" #["build", target]) != 0 then return none
  if isInRepo && (← prebuilt.pathExists) then
    return some prebuilt
  let some paths ← lakeQueryPaths #[target] | return none
  return paths[0]?.map FilePath.mk

structure QedjsEnv where
  bin      : FilePath
  leanPath : String

def resolveQedjsEnv (needBuild : Bool := true) : IO (Option QedjsEnv) := do
  let some bin ← resolveQedjsBin needBuild | return none
  let some leanPath ← lakeEnvLeanPath | return none
  return some { bin, leanPath }

def QedjsEnv.run (q : QedjsEnv) (args : Array String) (quiet : Bool := false)
    (extraPath : Option String := none) : IO Bool := do
  let lp := match extraPath with | some p => s!"{p}:{q.leanPath}" | none => q.leanPath
  let env := #[("LEAN_PATH", some lp)]
  let code ← if quiet then shQuiet q.bin.toString args env else sh q.bin.toString args env
  return code == 0

def QedjsEnv.runOut (q : QedjsEnv) (args : Array String) (quiet : Bool := false)
    (extraPath : Option String := none) : IO (Bool × String) := do
  let lp := match extraPath with | some p => s!"{p}:{q.leanPath}" | none => q.leanPath
  let (code, out) ← shOut q.bin.toString args #[("LEAN_PATH", some lp)]
  if code != 0 then
    IO.eprint out
    lastBuildErrorRef.set out
  else if !quiet then
    for line in out.splitOn "\n" do
      let t := line.cliTrim
      if !t.isEmpty && !t.startsWith "HAS_CSS:" && !t.startsWith "STYLESHEET:" then
        IO.println line
  return (code == 0, out)

end Qed.Cli
