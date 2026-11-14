import Cli.Common

open System (FilePath)

namespace Qed.Cli

def cmdDoctor : IO UInt32 := do
  IO.println "qed doctor:"
  let report (label : String) (ok : Bool) : IO Unit :=
    IO.println s!"  {if ok then green "✓" else red "✗"} {label}"
  for c in ["lean", "lake", "node", "python3"] do
    report c (← onPath c)
  return 0

def cmdNew (dir : String) : IO UInt32 := do
  let root : FilePath := dir
  if (← root.pathExists) then IO.eprintln (red s!"{dir} already exists"); return 1
  step s!"scaffolding {dir}"
  IO.FS.createDirAll root
  IO.FS.writeFile (root / "lean-toolchain")
    (← IO.FS.readFile ((← frameworkHome) / "lean-toolchain"))
  IO.FS.writeFile (root / "lakefile.lean") <|
    "import Lake\nopen Lake DSL\n\n" ++
    "package app where\n\n" ++
    "require qed from git \"https://github.com/JacobAsmuth/qed\" @ \"main\"\n\n" ++
    "@[default_target] lean_lib App where\n\n" ++
    "lean_exe web where\n  root := `Web\n"
  IO.FS.writeFile (root / "App.lean") <|
    "import Qed\nopen Qed\n\n" ++
    "component Quantity where\n" ++
    "  state quantity := 1\n" ++
    "  action increase when quantity < 10 => quantity += 1\n" ++
    "  action decrease when 1 < quantity  => quantity -= 1\n" ++
    "  invariant 1 ≤ quantity, quantity ≤ 10\n" ++
    "  view =>\n" ++
    "    <div>\n" ++
    "      <button onClick={.decrease}>−</button>\n" ++
    "      <span>{quantity}</span>\n" ++
    "      <button onClick={.increase}>+</button>\n" ++
    "    </div>\n"
  IO.FS.writeFile (root / "Web.lean") <|
    "import App\nimport Qed.Driver\n\ndef main : IO Unit := Qed.run Quantity.app\n"
  IO.println (green s!"✓ created {dir}/")
  IO.println s!"  next:  cd {dir} && qed dev"
  return 0

def usage : IO UInt32 := do
  IO.println "qed, a verified web frontend toolchain\n"
  IO.println "Usage: qed <command>\n"
  IO.println "  dev            watch + rebuild + serve with live-reload"
  IO.println "  build          production build → dist/ (optimized, verified)"
  IO.println "  start|preview  serve the build (server-rendered when ssr.mjs is present)"
  IO.println "  test           run the browser tests (if present)"
  IO.println "  check          verify proofs + no-sorry + axioms"
  IO.println "  clean          remove build outputs"
  IO.println "  new <dir>      scaffold a new app"
  IO.println "  doctor         report which dependencies are present"
  return 0

end Qed.Cli
