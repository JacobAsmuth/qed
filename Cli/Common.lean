import Qed.Json.Basic
open System (FilePath)

def String.cliTrim (s : String) : String := s.trimAscii.toString

namespace Qed.Cli

def devDir : FilePath := ".qed" / "dev"
def distDir : FilePath := "dist"
def devPort : String := "8000"
def axiomsManifest : FilePath := "scripts" / "axioms.lean"

def env (k : String) : IO (Option String) := IO.getEnv k
def nonEmptyEnv (k : String) : IO (Option String) := do return (← env k).bind fun s => let t := s.cliTrim; if t.isEmpty then none else some t
def optOrEnv (o : Option String) (k : String) : IO (Option String) := o.elim (nonEmptyEnv k) (pure ∘ some)
def frameworkHome : IO FilePath := return (← env "QED_HOME").getD "."
def runtimeFile (name : String) : IO FilePath := return (← frameworkHome) / "runtime" / name
def isInRepo : IO Bool := (FilePath.mk "Examples").pathExists
def modLeanPath (mod : String) : FilePath := FilePath.mk ((mod.replace "." "/") ++ ".lean")
def modOleanPath (mod : String) : FilePath := FilePath.mk ".lake" / "build" / "lib" / "lean" / ((mod.replace "." "/") ++ ".olean")
def dirPrefix (realDir : FilePath) : String := let s := realDir.toString; if s.endsWith "/" then s else s ++ "/"
def realPath? (p : FilePath) : IO (Option FilePath) := try some <$> IO.FS.realPath p catch _ => pure none
def symlinkMetadata? (p : FilePath) : IO (Option IO.FS.Metadata) := try some <$> p.symlinkMetadata catch _ => pure none
def symlinkType? (p : FilePath) : IO (Option IO.FS.FileType) := return (← symlinkMetadata? p).map (·.type)
def removeIfExists (p : FilePath) : IO Unit := do if ← p.pathExists then try IO.FS.removeFile p catch _ => pure ()
def andB [Monad m] (a : Bool) (b : m Bool) : m Bool := if a then b else pure false
def orB [Monad m] (a : Bool) (b : m Bool) : m Bool := if a then pure true else b

def writeBytesInsideDir (realOutDir : FilePath) (fileName : String) (bytes : ByteArray) : IO (Except String FilePath) := do
  let dst := realOutDir / fileName
  if let some ty ← symlinkType? dst then
    if ty != .file then return .error s!"refusing to overwrite symlink or non-regular file `{dst}`"
    let dstReal ← try IO.FS.realPath dst catch e => return .error s!"failed to canonicalize `{dst}`: {e}"
    if !dstReal.toString.startsWith (dirPrefix realOutDir) then return .error s!"refusing to write `{dst}` resolving outside `{realOutDir}`"
  IO.FS.writeBinFile dst bytes; return .ok dst

def writeFileInsideDir (realOutDir : FilePath) (fileName content : String) : IO (Except String FilePath) :=
  writeBytesInsideDir realOutDir fileName content.toUTF8

def redactArg (s : String) : String := match s.splitOn "=" with | k :: _ :: _ => s!"{k}=<redacted>" | _ => s

inductive CliFlagSpec (σ : Type) where
  | bool (names : List String) (update : σ → σ) | val (names : List String) (update : σ → String → Except String σ) | passThroughVal (names : List String)

def CliFlagSpec.valOk {σ : Type} (names : List String) (f : σ → String → σ) : CliFlagSpec σ := .val names fun s v => .ok (f s v)

structure CliParseConfig (σ : Type) where
  flags      : List (CliFlagSpec σ)
  allowEq    : Bool := true
  allowPos   : Bool := true
  passDash   : Bool := false
  unknownErr : String → String
  missingErr : String → String := fun f => s!"missing value for `{f}`"

def parseCliFlags {σ : Type} (cfg : CliParseConfig σ) (init : σ) (args : List String) : Except String (σ × List String) :=
  let findBool (a : String) := cfg.flags.findSome? fun | .bool ns u => if ns.contains a then some u else none | _ => none
  let findVal (a : String) := cfg.flags.findSome? fun | .val ns u => if ns.contains a then some u else none | _ => none
  let findValEq (a : String) := if !cfg.allowEq then none else cfg.flags.findSome? fun
    | .val ns u => ns.findSome? fun nm => let pfx := nm ++ "="; if a.startsWith pfx then some (u, (a.drop pfx.length).toString) else none
    | _ => none
  let isPassVal (a : String) := cfg.flags.any fun | .passThroughVal ns => ns.contains a | _ => false
  let rec go (st : σ) (pos : List String) : List String → Except String (σ × List String)
    | [] => .ok (st, pos.reverse)
    | a :: rest =>
        if let some u := findBool a then go (u st) pos rest
        else if let some u := findVal a then match rest with | v :: r => u st v >>= fun st' => go st' pos r | [] => .error (cfg.missingErr a)
        else if let some (u, v) := findValEq a then u st v >>= fun st' => go st' pos rest
        else if isPassVal a then match rest with | v :: r => go st (v :: a :: pos) r | [] => go st (a :: pos) []
        else if !cfg.allowPos || (!cfg.passDash && a.startsWith "-") then .error (cfg.unknownErr a)
        else go st (a :: pos) rest
  go init [] args

def webRoot : IO String := do
  if let some r ← env "QED_WEB_ROOT" then return r
  for (p, m) in [(FilePath.mk "Web.lean", "Web"), (FilePath.mk "App.lean", "App"), (FilePath.mk "Examples" / "Counter.lean", "Examples.Counter")] do
    if ← p.pathExists then return m
  return "App"

def jsRoot : IO String := do match ← env "QED_JS_ROOT" with | some r => return r | none => webRoot
def readTrimmed? (p : FilePath) : IO (Option String) := do if !(← p.pathExists) then return none else return some (← IO.FS.readFile p).cliTrim
def nonEmptyLines (s : String) : List String := (s.splitOn "\n").map String.cliTrim |>.filter (!·.isEmpty)
def parsePort (s : String) (default : Nat := 8000) : UInt16 := (s.toNat?.getD default).toUInt16
def takeIdentChars (s : String) : String := (s.takeWhile fun c => c.isAlphanum || c == '.' || c == '_' || c == '\'').toString
def tokenizeCodeLine (raw : String) : List String := (((raw.splitOn "--").headD raw).replace "\t" " ").splitOn " " |>.filter (!·.isEmpty)

def parseLeanImports (src : String) : Array String := Id.run do
  let mut imps : Array String := #[]
  for raw in src.splitOn "\n" do
    for d in (match tokenizeCodeLine raw with | "import" :: ds | "public" :: "import" :: ds => ds | _ => []) do
      let m := takeIdentChars d; if !m.isEmpty then imps := imps.push m
  return imps

inductive AppMode where | fullstack (fsName : String) | ssr (appName : String) | component (appName : String) | raw

def resolveAppMode (mod : String) : IO AppMode := do
  let path := modLeanPath mod; if !(← path.pathExists) then return .raw
  let src ← IO.FS.readFile path
  let mut depth : Nat := 0; let mut nsStack : List String := []; let mut lastTop : Option String := none; let mut lastAny : Option String := none
  for raw in src.splitOn "\n" do
    let inComment := depth > 0
    depth := depth + ((raw.splitOn "/-").length - 1) - ((raw.splitOn "-/").length - 1)
    if inComment then continue
    match tokenizeCodeLine raw with
    | "namespace" :: ns :: _ => let c := takeIdentChars ns; if !c.isEmpty then nsStack := c :: nsStack
    | "end" :: _ => nsStack := nsStack.drop 1
    | "fullstack" :: rawName :: _ => let fs := takeIdentChars rawName; if !fs.isEmpty then return .fullstack (".".intercalate (nsStack.reverse ++ [fs]))
    | "component" :: rawName :: _ =>
        let cName := takeIdentChars rawName
        if !cName.isEmpty then
          if nsStack.isEmpty then lastTop := some s!"{cName}.app"
          lastAny := some (".".intercalate (nsStack.reverse ++ [cName, "app"]))
    | _ => pure ()
  if let _ :: rest :: _ := src.splitOn "Qed.run " then
    let name := takeIdentChars (rest.dropWhile (· == ' ')).toString; if !name.isEmpty then return .ssr name
  return (lastTop.orElse fun _ => lastAny).elim .raw .component

def driverEntries : Array String := #[
  "main:__main", "Qed.qedInit:qed_init", "Qed.qedDispatch:qed_dispatch", "Qed.qedDispatchStr:qed_dispatch_str",
  "Qed.qedStreamChunk:qed_stream_chunk", "Qed.qedStreamDone:qed_stream_done", "Qed.qedHttpDone:qed_http_done",
  "Qed.qedHttpBytesDone:qed_http_bytes_done", "Qed.qedUrlChanged:qed_url_changed", "Qed.qedLocalDispatch:qed_local_dispatch",
  "Qed.qedLocalDispatchStr:qed_local_dispatch_str", "Qed.qedLocalSnapshot:qed_local_snapshot", "Qed.qedLocalRestore:qed_local_restore",
  "Qed.qedDehydrate:qed_dehydrate", "Qed.qedEffectDone:qed_effect_done", "Qed.qedPortRecv:qed_port_recv",
  "Qed.qedWsOpen:qed_ws_open", "Qed.qedWsBytes:qed_ws_bytes", "Qed.qedWsText:qed_ws_text", "Qed.qedWsClose:qed_ws_close"]

private def paint (enabled : Bool) (code s : String) : String := if enabled then s!"\x1b[{code}m{s}\x1b[0m" else s
def bold (s : String) : String := paint true "1" s
def green (s : String) : String := paint true "32" s
def red (s : String) : String := paint true "31" s
def step (s : String) : IO Unit := IO.println (bold s!"▸ {s}")
def runExceptCmd (act : ExceptT String IO UInt32) : IO UInt32 := do match ← act.run with | .ok c => return c | .error e => IO.eprintln (red s!"✗ {e}"); return 1
private def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

private def parseLeanDiagLine (line : String) : Option (String × String × Nat × Nat × String) := do
  let parseLoc (sev rest : String) : Option (String × String × Nat × Nat × String) := do
    let path :: lnS :: colS :: msgParts := rest.splitOn ":" | none
    some (sev, path.cliTrim, ← lnS.cliTrim.toNat?, ← colS.cliTrim.toNat?, (":".intercalate msgParts).cliTrim)
  if line.startsWith "error(" then
    let _ :: restParts := line.splitOn "): " | failure
    return ← parseLoc "error" ("): ".intercalate restParts)
  for (pfx, sev) in [("error:", "error"), ("warning:", "warning")] do
    if line.startsWith pfx then if let some r := parseLoc sev (line.drop pfx.length).toString.cliTrim then return r
  let path :: lnS :: colS :: sevS :: msgParts := line.splitOn ":" | failure
  let sev := sevS.cliTrim; guard (path.endsWith ".lean" && (sev == "error" || sev == "warning"))
  parseLoc sev (":".intercalate (path :: lnS :: colS :: msgParts))

private def readSourceSnippet (path : String) (ln col : Nat) (color : Bool) : IO String := do
  let fp : FilePath := path; if ← orB (ln == 0) ((!·) <$> fp.pathExists) then return ""
  try
    let lines := ((← IO.FS.readFile fp).splitOn "\n").toArray; if ln > lines.size then return ""
    let w := max 3 (toString ln).length; let bar := paint color "2" "|"
    let pad (n : Nat) := let s := toString n; spaces (w - s.length) ++ s
    let prevRow := if ln >= 2 && !lines[ln - 2]!.cliTrim.isEmpty then [s!"  {paint color "2" (pad (ln - 1))} {bar} {paint color "2" lines[ln - 2]!}"] else []
    return "\n".intercalate (prevRow ++ [s!"  {paint color "1" (pad ln)} {bar} {lines[ln - 1]!}", s!"  {spaces w} {bar} {spaces col}{paint color "1;31" "^"}"])
  catch _ => return ""

initialize lastBuildErrorRef : IO.Ref String ← IO.mkRef ""
def clearLastBuildError : IO Unit := lastBuildErrorRef.set ""
def getLastBuildError : IO String := lastBuildErrorRef.get

def formatLakeDiagnostics (raw : String) (allowColor : Bool := true) : IO String := do
  if ← andB allowColor ((· == some "1") <$> env "QED_VERBOSE") then return raw
  let color ← andB allowColor ((fun v => (v.getD "").isEmpty) <$> env "NO_COLOR")
  let mut out : Array String := #[]; let mut skipBullets := false; let mut hasPretty := false
  for line in raw.splitOn "\n" do
    let t := line.cliTrim
    if ["error: Lean exited with code 1", "error: build failed", "info: stderr:"].contains t || ["trace: .>", "✔ [", "ℹ [", "✖ ["].any (t.startsWith ·) then continue
    if t == "Some required targets logged failures:" then skipBullets := true; continue
    if skipBullets then if t.startsWith "- " then continue else skipBullets := false
    match parseLeanDiagLine line with
    | some (sev, path, ln, col, msg) =>
        if ["hvalid", "valid_view", "hview", "hpres"].any (fun p => msg == s!"could not synthesize default value for parameter '{p}' using tactics") then continue
        hasPretty := true; let snippet ← readSourceSnippet path ln col color
        if !out.isEmpty then out := out.push ""
        out := out.push s!"{paint color (if sev == "error" then "1;31" else "1;33") sev}: {paint color "1" s!"{path}:{ln}:{col}"}"
        if !snippet.isEmpty then out := out.push snippet
        if !msg.isEmpty then out := out.push s!"  {msg}"
    | none =>
        if t.startsWith "Hint:" then out := out.push s!"  {paint color "1;36" "Hint:"}{(t.drop 5).toString}"
        else if t.startsWith "• " then out := out.push s!"    {paint color "1;31" "•"} {(t.drop 2).toString}"
        else if !t.isEmpty then out := out.push (if hasPretty then s!"  {line}" else line)
  let formatted := "\n".intercalate out.toList
  return if formatted.cliTrim.isEmpty then raw else formatted ++ "\n"

def sh (cmd : String) (args : Array String) (extraEnv : Array (String × Option String) := #[]) : IO UInt32 := do
  (← IO.Process.spawn { cmd, args, env := extraEnv, stdin := .inherit, stdout := .inherit, stderr := .inherit }).wait
def shOut (cmd : String) (args : Array String) (extraEnv : Array (String × Option String) := #[]) : IO (UInt32 × String) := do
  let o ← IO.Process.output { cmd, args, env := extraEnv }; return (o.exitCode, o.stdout ++ o.stderr)
private def shCapture (diag : Bool) (cmd : String) (args : Array String) (extraEnv : Array (String × Option String) := #[]) : IO UInt32 := do
  let (code, out) ← shOut cmd args extraEnv
  if code != 0 then
    if diag then IO.eprint (← formatLakeDiagnostics out true); lastBuildErrorRef.set (← formatLakeDiagnostics out false) else IO.eprint out
  return code
def shQuiet (cmd : String) (args : Array String) (extraEnv : Array (String × Option String) := #[]) : IO UInt32 := shCapture false cmd args extraEnv
def shLakeBuild (args : Array String) : IO UInt32 := shCapture true "lake" args
def shLean (leanPath : String) (args : Array String) : IO UInt32 := shCapture true "lean" args #[("LEAN_PATH", some leanPath)]
def onPath (cmd : String) : IO Bool := return (← shOut "bash" #["-c", s!"command -v {cmd}"]).1 == 0

partial def collect (dir : FilePath) (ext : String) (skipDirs : List String := []) : IO (Array FilePath) := do
  if !(← dir.pathExists) then return #[]
  let mut acc : Array FilePath := #[]
  for entry in (← try dir.readDir catch _ => pure #[]) do
    let p := entry.path
    if ← try p.isDir catch _ => pure false then if (p.fileName.getD "") ∉ skipDirs then acc := acc ++ (← collect p ext skipDirs)
    else if p.extension == some ext then acc := acc.push p
  return acc

def writeDevStatusJson (outDir : FilePath) (status : String) (kind : String := "hmr")
    (errText : String := "") (durationMs : Nat := 0) (bumpId : Bool := true) (sseUrl : String := "") : IO String := do
  IO.FS.createDirAll outDir; let buildIdPath := outDir / "__build_id"
  let idStr ← if ← orB bumpId ((!·) <$> buildIdPath.pathExists) then
      let id := toString (← IO.monoMsNow); IO.FS.writeFile buildIdPath id; pure id
    else pure (← IO.FS.readFile buildIdPath).cliTrim
  let json := Qed.Json.render (.obj ([("id", .str idStr), ("status", .str status), ("kind", .str kind),
    ("durationMs", .num ⟨Int.ofNat durationMs, 0⟩), ("error", .str errText)] ++ (if sseUrl.isEmpty then [] else [("sseUrl", .str sseUrl)]))) ++ "\n"
  let tmp := outDir / "__dev_status.tmp"; IO.FS.writeFile tmp json; IO.FS.rename tmp (outDir / "__dev_status"); return json

def writeIfChanged (path : FilePath) (content : String) : IO Bool := do
  if ← path.pathExists then if (← IO.FS.readFile path) == content then return false
  IO.FS.writeFile path content; return true

initialize leanPathCache : IO.Ref (Option String) ← IO.mkRef none

def mtimeNs (p : FilePath) : IO (Option Int) := do
  if !(← p.pathExists) then return none
  try let m ← p.metadata; return some (m.modified.sec * 1000000000 + Int.ofNat m.modified.nsec.toNat) catch _ => return none

def isUpToDate (out : FilePath) (deps : Array FilePath) : IO Bool := do
  let some outT ← mtimeNs out | return false
  deps.allM fun d => return (← mtimeNs d).any (· ≤ outT)

def lakeEnvLeanPath : IO (Option String) := do
  if let some lp ← leanPathCache.get then return some lp
  let cache (lp : String) : IO (Option String) := do leanPathCache.set (some lp); return some lp
  if let some lp ← nonEmptyEnv "LEAN_PATH" then return ← cache lp
  if ← andB (← isInRepo) ((!·) <$> (FilePath.mk ".lake" / "packages").pathExists) then
    let o ← IO.Process.output { cmd := "lean", args := #["--print-libdir"] }; let sysLib := o.stdout.cliTrim
    if o.exitCode == 0 && !sysLib.isEmpty then return ← cache s!"{(← IO.currentDir) / ".lake" / "build" / "lib" / "lean"}:{sysLib}"
  let o ← IO.Process.output { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"] }
  if o.exitCode != 0 then IO.eprint (o.stdout ++ o.stderr); return none
  cache o.stdout.cliTrim

def lakeQueryPaths (targets : Array String) : IO (Option (Array String)) := do
  let o ← IO.Process.output { cmd := "lake", args := #["query"] ++ targets }
  if o.exitCode != 0 then IO.eprint (o.stdout ++ o.stderr); return none
  return some (nonEmptyLines o.stdout).toArray

def resolveQedjsBin (needBuild : Bool := true) : IO (Option FilePath) := do
  let (qh, inRepo) := (← frameworkHome, ← isInRepo); let prebuilt := qh / ".lake" / "build" / "bin" / "qedjs"
  if ← prebuilt.pathExists then
    if ← andB inRepo (orB (!needBuild) ((· == some "1") <$> env "QED_PREBUILT")) then return some prebuilt
    if !inRepo then if let (some a, some b) := (← readTrimmed? "lean-toolchain", ← readTrimmed? (qh / "lean-toolchain")) then if a == b then return some prebuilt
  let target := if inRepo then "qedjs" else "qed/qedjs"
  if needBuild then if (← shQuiet "lake" #["build", target]) != 0 then return none
  if ← andB inRepo prebuilt.pathExists then return some prebuilt
  return (← lakeQueryPaths #[target]).bind (·[0]?.map FilePath.mk)

structure QedjsEnv where
  bin      : FilePath
  leanPath : String

def resolveQedjsEnv (needBuild : Bool := true) : IO (Option QedjsEnv) := do
  let some bin ← resolveQedjsBin needBuild | return none
  let some leanPath ← lakeEnvLeanPath | return none
  return some { bin, leanPath }

private def QedjsEnv.envWith (q : QedjsEnv) (extraPath : Option String) : Array (String × Option String) :=
  #[("LEAN_PATH", some (extraPath.elim q.leanPath (s!"{·}:{q.leanPath}")))]

def QedjsEnv.run (q : QedjsEnv) (args : Array String) (quiet : Bool := false) (extraPath : Option String := none) : IO Bool := do
  let e := q.envWith extraPath; return (← if quiet then shQuiet q.bin.toString args e else sh q.bin.toString args e) == 0

def QedjsEnv.runOut (q : QedjsEnv) (args : Array String) (quiet : Bool := false) (extraPath : Option String := none) : IO (Bool × String) := do
  let (code, out) ← shOut q.bin.toString args (q.envWith extraPath)
  if code != 0 then IO.eprint out; lastBuildErrorRef.set out
  else if !quiet then
    for line in out.splitOn "\n" do let t := line.cliTrim; if !t.isEmpty && !t.startsWith "HAS_CSS:" && !t.startsWith "STYLESHEET:" then IO.println line
  return (code == 0, out)

end Qed.Cli
