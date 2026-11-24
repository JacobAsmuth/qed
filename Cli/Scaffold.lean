import Cli.Common

open System (FilePath)

namespace Qed.Cli

def cmdDoctor : IO UInt32 := do
  IO.println "qed doctor:"
  for c in ["lean", "lake", "cargo"] do
    IO.println s!"  {if ← onPath c then green "✓" else red "✗"} {c}"
  return 0

def cmdNew (dir : String) : IO UInt32 := do
  let root : FilePath := dir
  if ← root.pathExists then IO.eprintln (red s!"{dir} already exists"); return 1
  step s!"scaffolding {dir}"; IO.FS.createDirAll root
  IO.FS.writeFile (root / "lean-toolchain") (← IO.FS.readFile ((← frameworkHome) / "lean-toolchain"))
  IO.FS.writeFile (root / "lakefile.lean") <|
    "import Lake\nopen Lake DSL\n\npackage app where\n\nrequire qed from git \"https://github.com/JacobAsmuth/qed\" @ \"main\"\n\n@[default_target] lean_lib App where\n"
  IO.FS.writeFile (root / "App.lean") <|
    "import Qed\nopen Qed\n\ncomponent Quantity:\n  state quantity = 1\n  action increase:\n    if quantity < 10: quantity += 1\n  action decrease:\n    if quantity > 1: quantity -= 1\n  invariant inRange: 1 <= quantity <= 10\n  view:\n    <div>\n      <button onClick={.decrease}>−</button>\n      <span>{quantity}</span>\n      <button onClick={.increase}>+</button>\n    </div>\n"
  IO.println (green s!"✓ created {dir}/"); IO.println s!"  next:  cd {dir} && qed dev"; return 0

def usage : IO UInt32 := do
  IO.print <|
    "qed, a verified full-stack web toolchain\n\nUsage: qed <command>\n\n" ++
    "  dev            watch + rebuild + serve with live-reload\n" ++
    "  build          production build → dist/ (JS client + native server, verified)\n" ++
    "  start|preview  serve the build\n" ++
    "  serve <dir>    serve a static directory natively\n" ++
    "  manifest       emit & validate qed_deploy.json infrastructure manifest\n" ++
    "  login          authenticate this CLI with Qed Cloud (browser device flow)\n" ++
    "  logout         remove stored Qed Cloud credentials\n" ++
    "  whoami         show the logged-in Qed Cloud account\n" ++
    "  deploy         deploy to hosted Qed Cloud (or `--local-gcp` for direct GCP deploy)\n" ++
    "  status [app]   show deployed apps, statuses, and URLs\n" ++
    "  logs <id>      view or follow (`-f`) deployment verification & rollout logs\n" ++
    "  secrets        manage app secrets (`list <app>` | `set <app> <NAME>`)\n" ++
    "  rollback       roll back an app to a previous deployment\n" ++
    "  dev-auth [p]   run local ES256 OIDC dev identity provider\n" ++
    "  test           run the native test suite (if present)\n" ++
    "  check          verify proofs + no-sorry + axioms\n" ++
    "  clean          remove build outputs\n" ++
    "  new <dir>      scaffold a new app\n" ++
    "  doctor         report which dependencies are present\n"
  return 0

end Qed.Cli
