open System (FilePath)

def String.trimmed (s : String) : String :=
  String.ofList (((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)

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
  if !(← (FilePath.mk "Web.lean").pathExists) && (← (FilePath.mk "Examples" / "Web.lean").pathExists) then
    return "Examples.Web"
  return "Web"

def jsRoot : IO String := do
  match ← env "QED_JS_ROOT" with
  | some r => return r
  | none   => webRoot

def takeIdentChars (s : String) : String :=
  (s.takeWhile fun c => c.isAlphanum || c == '.' || c == '_' || c == '\'').toString

def fullstackAppName (mod : String) : IO (Option String) := do
  let path := FilePath.mk ((mod.replace "." "/") ++ ".lean")
  if !(← path.pathExists) then return none
  let src ← IO.FS.readFile path
  let mut depth : Nat := 0
  let mut nsStack : List String := []
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
    | "fullstack" :: rawName :: _ =>
        let fs := takeIdentChars rawName
        if !fs.isEmpty then
          return some (String.intercalate "." (nsStack.reverse ++ [fs]))
    | _ => pure ()
  return none

def ssrAppName (mod : String) : IO (Option String) := do
  let path := FilePath.mk ((mod.replace "." "/") ++ ".lean")
  if !(← path.pathExists) then return none
  let src ← IO.FS.readFile path
  match src.splitOn "Qed.run " with
  | _ :: rest :: _ =>
      let name := takeIdentChars (rest.dropWhile (· == ' ')).toString
      return if name.isEmpty then none else some name
  | _ => return none

def driverEntries : Array String := #[
  "main:__main",
  "Qed.qedInit:qed_init", "Qed.qedDispatch:qed_dispatch", "Qed.qedDispatchStr:qed_dispatch_str",
  "Qed.qedStreamChunk:qed_stream_chunk", "Qed.qedStreamDone:qed_stream_done",
  "Qed.qedHttpDone:qed_http_done", "Qed.qedHttpBytesDone:qed_http_bytes_done",
  "Qed.qedUrlChanged:qed_url_changed",
  "Qed.qedLocalDispatch:qed_local_dispatch", "Qed.qedLocalDispatchStr:qed_local_dispatch_str",
  "Qed.qedLocalSnapshot:qed_local_snapshot", "Qed.qedLocalRestore:qed_local_restore",
  "Qed.qedEffectDone:qed_effect_done", "Qed.qedPortRecv:qed_port_recv"]

def bold  (s : String) : String := s!"\x1b[1m{s}\x1b[0m"
def green (s : String) : String := s!"\x1b[32m{s}\x1b[0m"
def red   (s : String) : String := s!"\x1b[31m{s}\x1b[0m"
def step  (s : String) : IO Unit := IO.println (bold s!"▸ {s}")

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

def writeBuildId (outDir : FilePath) : IO Unit := do
  IO.FS.writeFile (outDir / "__build_id") (toString (← IO.monoMsNow))

end Qed.Cli
