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
