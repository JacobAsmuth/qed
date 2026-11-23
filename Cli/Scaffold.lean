import Cli.Common

open System (FilePath)

namespace Qed.Cli

def cmdDoctor : IO UInt32 := do
  IO.println "qed doctor:"
  let report (label : String) (ok : Bool) : IO Unit :=
    IO.println s!"  {if ok then green "✓" else red "✗"} {label}"
  for c in ["lean", "lake", "cargo"] do
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
    "@[default_target] lean_lib App where\n"
  IO.FS.writeFile (root / "App.lean") <|
    "import Qed\nopen Qed\n\n" ++
    "component Quantity:\n" ++
    "  state quantity = 1\n" ++
    "  action increase:\n" ++
    "    if quantity < 10: quantity += 1\n" ++
    "  action decrease:\n" ++
    "    if quantity > 1: quantity -= 1\n" ++
    "  invariant inRange: 1 <= quantity <= 10\n" ++
    "  view:\n" ++
    "    <div>\n" ++
    "      <button onClick={.decrease}>−</button>\n" ++
    "      <span>{quantity}</span>\n" ++
    "      <button onClick={.increase}>+</button>\n" ++
    "    </div>\n"
  IO.println (green s!"✓ created {dir}/")
  IO.println s!"  next:  cd {dir} && qed dev"
  return 0

def usage : IO UInt32 := do
  IO.print <|
    "qed, a verified full-stack web toolchain\n\nUsage: qed <command>\n\n" ++
    "  dev            watch + rebuild + serve with live-reload\n" ++
    "  build          production build → dist/ (JS client + native server, verified)\n" ++
    "  start|preview  serve the build\n" ++
    "  serve <dir>    serve a static directory natively\n" ++
    "  manifest       emit & validate qed_deploy.json infrastructure manifest\n" ++
    "  dev-auth [p]   run local ES256 OIDC dev identity provider\n" ++
    "  test           run the native test suite (if present)\n" ++
    "  check          verify proofs + no-sorry + axioms\n" ++
    "  clean          remove build outputs\n" ++
    "  new <dir>      scaffold a new app\n" ++
    "  doctor         report which dependencies are present\n"
  return 0

end Qed.Cli
