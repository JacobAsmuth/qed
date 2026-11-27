import Cli.Common
open System (FilePath)

namespace Qed.Cli

def cmdDoctor : IO UInt32 := do
  IO.println "qed doctor:"
  for c in ["lean", "lake", "cargo"] do IO.println s!"  {if ← onPath c then green "✓" else red "✗"} {c}"
  return 0

def cmdNew (dir : String) : IO UInt32 := do
  let root : FilePath := dir
  if ← root.pathExists then IO.eprintln (red s!"{dir} already exists"); return 1
  step s!"scaffolding {dir}"; IO.FS.createDirAll root
  IO.FS.writeFile (root / "lean-toolchain") (← IO.FS.readFile ((← frameworkHome) / "lean-toolchain"))
  IO.FS.writeFile (root / "lakefile.lean")
    "import Lake\nopen Lake DSL\n\npackage app where\n\nrequire qed from git \"https://github.com/JacobAsmuth/qed\" @ \"main\"\n\n@[default_target] lean_lib App where\n"
  IO.FS.writeFile (root / "App.lean")
    "import Qed\nopen Qed\n\ncomponent Quantity:\n  state quantity = 1\n  action increase:\n    if quantity < 10: quantity += 1\n  action decrease:\n    if quantity > 1: quantity -= 1\n  invariant inRange: 1 <= quantity <= 10\n  view:\n    <div>\n      <button onClick={.decrease}>−</button>\n      <span>{quantity}</span>\n      <button onClick={.increase}>+</button>\n    </div>\n"
  IO.println (green s!"✓ created {dir}/"); IO.println s!"  next:  cd {dir} && qed dev"; return 0

private def copyFileRaw (src dst : FilePath) (exec : Bool := false) : IO Unit := do
  if let some parent := dst.parent then IO.FS.createDirAll parent
  IO.FS.writeBinFile dst (← IO.FS.readBinFile src)
  if exec then
    let rx : IO.AccessRight := { read := true, execution := true }
    IO.setAccessRights dst { user := { read := true, write := true, execution := true }, group := rx, other := rx }

private def copyFileIfExists (src dst : FilePath) (exec : Bool := false) : IO Unit := do if ← src.pathExists then copyFileRaw src dst exec

private partial def copyTree (src dst : FilePath) : IO Unit := do
  let md ← src.metadata
  if md.type == .dir then IO.FS.createDirAll dst; for entry in ← src.readDir do copyTree entry.path (dst / entry.fileName)
  else if md.type == .file then copyFileRaw src dst

private def copyTreeIfExists (src dst : FilePath) : IO Unit := do if ← src.pathExists then copyTree src dst
private def copyWithSufs (srcDir dstDir : FilePath) (base : String) (sufs : List String) : IO Unit := do
  for suf in sufs do copyFileIfExists (srcDir / (base ++ suf)) (dstDir / (base ++ suf))

def renderStagedLakefile (lakeSrc : String) : Except String String :=
  let block := ((lakeSrc.splitOn "\n").dropWhile (!·.startsWith "lean_lib QedServer")).takeWhile (!·.cliTrim.isEmpty)
  if block.isEmpty then .error "could not find `lean_lib QedServer` block in source lakefile.lean"
  else .ok <| "import Lake\nopen Lake DSL\n\npackage qed where\n\nextern_lib libqed_server pkg := do\n  inputBinFile (pkg.staticLibDir / nameToStaticLib \"qed_server\")\n\n@[default_target]\nlean_lib Qed where\n\n" ++ "\n".intercalate block ++ "\n"

def cmdStageSdk (args : List String) : IO UInt32 := do
  let (flags, pos) := args.partition (·.startsWith "-")
  unless flags.all (· == "--no-bins") && pos.length == 1 do IO.eprintln "usage: qed stage-sdk <dir> [--no-bins]"; return 1
  let (dst, home) := (FilePath.mk pos[0]!, ← frameworkHome); let lakePath := home / "lakefile.lean"
  unless ← lakePath.pathExists do IO.eprintln (red s!"cannot find Qed framework lakefile.lean at `{lakePath}` (set QED_HOME)"); return 1
  let libDir := home / ".lake" / "build" / "lib"
  for req in [libDir / "libqed_server.a", libDir / "lean" / "Qed.olean"] do
    unless ← req.pathExists do IO.eprintln (red s!"missing prebuilt artifact `{req}`; run `lake build Qed QedServer` first"); return 1
  let stagedLake ← match renderStagedLakefile (← IO.FS.readFile lakePath) with | .ok s => pure s | .error e => IO.eprintln (red e); return 1
  step s!"staging prebuilt Qed SDK into {dst}"; IO.FS.createDirAll dst; IO.FS.writeFile (dst / "lakefile.lean") stagedLake
  for rel in [FilePath.mk "lean-toolchain", "Qed.lean", FilePath.mk "scripts" / "axioms.lean"] do copyFileIfExists (home / rel) (dst / rel)
  for dir in ["Qed", "runtime"] do copyTreeIfExists (home / dir) (dst / dir)
  let dstLib := dst / ".lake" / "build" / "lib"
  for base in ["libqed_server.a", "libqed_Qed.a", "libqed_QedServer.a"] do copyWithSufs libDir dstLib base ["", ".hash", ".rsp", ".trace"]
  for (sub, sufs) in [(FilePath.mk "lib" / "lean", [".olean", ".olean.private", ".olean.server", ".ilean", ".trace"]),
      (FilePath.mk "ir", [".c", ".c.o", ".c.o.export", ".c.o.noexport", ".setup.json", ".trace", ".c.trace"])] do
    let (sDir, dDir) := (home / ".lake" / "build" / sub, dst / ".lake" / "build" / sub)
    copyWithSufs sDir dDir "Qed" sufs; copyTreeIfExists (sDir / "Qed") (dDir / "Qed")
  if !flags.contains "--no-bins" then
    for b in ["qed", "qedjs"] do copyFileIfExists (home / ".lake" / "build" / "bin" / b) (dst / ".lake" / "build" / "bin" / b) (exec := true)
  IO.println (green s!"✓ staged prebuilt Qed SDK at {dst}/"); return 0

def usage : IO UInt32 := do
  IO.print <| "qed, a verified full-stack web toolchain\n\nUsage: qed <command>\n\n" ++ String.join ([
    ("dev", "watch + rebuild + serve with live-reload"),
    ("build", "production build → dist/ (JS client + native server, verified)"),
    ("start|preview", "serve the build"), ("serve <dir>", "serve a static directory natively"),
    ("manifest", "emit & validate qed_deploy.json infrastructure manifest"),
    ("login", "authenticate this CLI with Qed Cloud (browser device flow)"),
    ("logout", "revoke token and remove stored Qed Cloud credentials"),
    ("whoami", "show the logged-in Qed Cloud account"),
    ("deploy", "deploy to hosted Qed Cloud (or `--local-gcp` for direct GCP deploy)"),
    ("status [app]", "show deployed apps, statuses, and URLs"),
    ("logs <target>", "view or follow (`-f`) deployment or `--runtime` logs"),
    ("cancel <id>", "cancel a queued or in-progress deployment"),
    ("secrets", "manage app secrets (`list` | `set` | `delete`)"),
    ("rollback", "roll back an app to a previous deployment"),
    ("dev-auth [p]", "run local ES256 OIDC dev identity provider"),
    ("stage-sdk <d>", "stage prebuilt Qed SDK (`Qed`, `QedServer`, `libqed_server.a`) for containers"),
    ("test", "run the native test suite (if present)"), ("check", "verify proofs + no-sorry + axioms"),
    ("clean", "remove build outputs"), ("new <dir>", "scaffold a new app"),
    ("doctor", "report which dependencies are present")].map fun (c, d) => s!"  {c}{String.ofList (List.replicate (15 - c.length) ' ')}{d}\n")
  return 0

end Qed.Cli
