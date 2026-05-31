/-
  The `qed` CLI — build/run/verify tooling for Qed apps.

  Commands mirror the npm/vite vocabulary:

      qed dev      watch sources, rebuild, serve with live-reload
      qed build    production build → dist/ (optimized + verified)
      qed start    serve the production build  (alias: preview)
      qed test     run the browser test suite (if present)
      qed check    verify only: proofs + no-sorry + axiom-clean
      qed clean    remove build outputs
      qed new DIR  scaffold a new app
      qed doctor   report which dependencies are present

  Every `build`/`dev`/`check` runs verification: `lake build` (so the kernel checks
  every proof — a failed proof is a build error), a grep for
  `sorry`/`admit`/`native_decide`, and the axiom manifest if one is present.

  Two locations matter, kept separate so the CLI works outside the framework
  checkout: the current directory is the *project* (your app + lakefile), and
  `QED_HOME` is the *framework* (its `runtime/` driver and `scripts/`). Caches
  (the wasm runtime, emscripten) live under `~/.qed`. The CLI orchestrates lake,
  emcc, python3, and node; the build logic and verification policy live here.
-/
open System (FilePath)

namespace Qed.Cli

/-! ### Locations -/

def leanWasmVersion : String := "4.15.0"
def wasmToolchain   : String := s!"lean-{leanWasmVersion}-linux_wasm32"
def devDir          : FilePath := ".qed" / "dev"
def distDir         : FilePath := "dist"
def devPort         : String := "8000"

def env (k : String) : IO (Option String) := IO.getEnv k

def homeDir : IO FilePath := return (← env "HOME").getD "."
/-- Cache root for downloaded toolchains and emscripten. -/
def cacheDir : IO FilePath := return (← homeDir) / ".qed"
/-- The framework checkout (its `runtime/` and `scripts/`). Defaults to the
    current directory for in-repo development. -/
def frameworkHome : IO FilePath := return (← env "QED_HOME").getD "."
/-- The project's web-entry module. Apps use `Web`; the framework demo overrides
    this to `Examples.Web` via `QED_WEB_ROOT`. -/
def webRoot : IO String := return (← env "QED_WEB_ROOT").getD "Web"
def toolchainDir : IO FilePath := return (← cacheDir) / "toolchains" / wasmToolchain
def runtimeFile (name : String) : IO FilePath := return (← frameworkHome) / "runtime" / name
/-- Per-project axiom manifest gated by `check`/`build` (skipped if absent). -/
def axiomsManifest : FilePath := "scripts" / "axioms.lean"

/-! ### Terminal + process helpers -/

def bold  (s : String) : String := s!"\x1b[1m{s}\x1b[0m"
def green (s : String) : String := s!"\x1b[32m{s}\x1b[0m"
def red   (s : String) : String := s!"\x1b[31m{s}\x1b[0m"
def step  (s : String) : IO Unit := IO.println (bold s!"▸ {s}")

def sh (cmd : String) (args : Array String) : IO UInt32 := do
  let child ← IO.Process.spawn
    { cmd := cmd, args := args, stdin := .inherit, stdout := .inherit, stderr := .inherit }
  child.wait

def shOut (cmd : String) (args : Array String) : IO (UInt32 × String) := do
  let o ← IO.Process.output { cmd := cmd, args := args }
  return (o.exitCode, o.stdout ++ o.stderr)

def onPath (cmd : String) : IO Bool := do
  return (← shOut "bash" #["-c", s!"command -v {cmd}"]).1 == 0

/-- Recursively collect files with `ext`, skipping the named directories. -/
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

/-! ### Toolchains (downloaded on demand into ~/.qed) -/

def ensureToolchain : IO Unit := do
  let tc ← toolchainDir
  if !(← tc.pathExists) then
    step s!"downloading {wasmToolchain} (prebuilt Lean wasm runtime)"
    IO.FS.createDirAll ((← cacheDir) / "toolchains")
    let url := s!"https://github.com/leanprover/lean4/releases/download/v{leanWasmVersion}/{wasmToolchain}.tar.zst"
    let tar := ((← cacheDir) / "toolchains" / s!"{wasmToolchain}.tar.zst").toString
    let _ ← sh "curl" #["-sSfL", url, "-o", tar]
    let _ ← sh "tar" #["--zstd", "-xf", tar, "-C", ((← cacheDir) / "toolchains").toString]

/-- Find an `emsdk_env.sh` to source (cache first, then `~/emsdk`). -/
def findEmsdkEnv : IO (Option FilePath) := do
  for c in [(← cacheDir) / "emsdk" / "emsdk_env.sh", (← homeDir) / "emsdk" / "emsdk_env.sh"] do
    if (← c.pathExists) then return some c
  return none

/-- Ensure an emcc is available, installing emscripten into ~/.qed/emsdk only if
    nothing usable is found. Returns an env file to source, or none if `emcc` is
    already directly on PATH. -/
def ensureEmscripten : IO (Option FilePath) := do
  if let some e ← findEmsdkEnv then return some e
  if (← onPath "emcc") then return none
  step "installing emscripten (one-time, ~1GB) into ~/.qed/emsdk"
  let dir := (← cacheDir) / "emsdk"
  let _ ← sh "git" #["clone", "--depth", "1", "https://github.com/emscripten-core/emsdk.git", dir.toString]
  let _ ← sh "bash" #["-c", s!"cd {dir} && ./emsdk install latest && ./emsdk activate latest"]
  return some (dir / "emsdk_env.sh")

/-- Run emcc, sourcing the emscripten environment if needed. -/
def runEmcc (args : Array String) : IO UInt32 := do
  match ← ensureEmscripten with
  | some envFile =>
      sh "bash" (#["-c", s!"source {envFile} >/dev/null 2>&1; emcc \"$@\"", "emcc"] ++ args)
  | none => sh "emcc" args

/-! ### WASM build -/

def emccArgs (cfiles : Array FilePath) (outJs : FilePath) (prod : Bool)
    (tc qh : FilePath) : Array String :=
  #["-o", outJs.toString, "-I", (tc / "include").toString, "-L", (tc / "lib" / "lean").toString]
  ++ cfiles.map (·.toString)
  ++ #[(qh / "runtime" / "qed_dom.c").toString, (qh / "runtime" / "uv_stubs.c").toString]
  ++ #["-lInit", "-lLean", "-lleancpp", "-lleanrt", "-lStd",
       "-sFORCE_FILESYSTEM", "-sMODULARIZE", "-sEXPORT_NAME=Qed",
       "-sEXPORTED_FUNCTIONS=_main,_qed_run_init,_qed_run_dispatch,_qed_run_dispatch_str,_qed_run_stream_chunk,_qed_run_stream_done,_qed_run_http_done,_qed_run_url_changed,_qed_run_local_dispatch,_qed_run_local_dispatch_str,_qed_run_local_snapshot,_qed_run_local_restore,_qed_run_effect_done,_qed_run_port_recv,_malloc,_free",
       "-sEXPORTED_RUNTIME_METHODS=ccall,cwrap,stringToNewUTF8",
       "-sEXIT_RUNTIME=0", "-sMAIN_MODULE=2", "-sLINKABLE=0", "-sEXPORT_ALL=0",
       -- the diff/render walk a child list with one stack frame per element; the
       -- default 64KB wasm stack overflows on long lists, so give it room (16MB),
       -- and start with enough memory to hold the stack-first layout.
       "-sSTACK_SIZE=16777216", "-sINITIAL_MEMORY=33554432",
       "-sALLOW_MEMORY_GROWTH=1", "-fwasm-exceptions", "-pthread", "-flto"]
  ++ (if prod then #["-Oz"] else #[])

/-- Generate C for the web entry (and its dependencies, including the qed package)
    and link it to `outDir/qed.{js,wasm}`. -/
def linkWasm (outDir : FilePath) (prod : Bool) : IO Bool := do
  ensureToolchain
  let wr ← webRoot
  if (← sh "lake" #["build", wr ++ ":c.o"]) != 0 then return false
  -- Collect *generated* Lean C from the project and from Lake dependency packages
  -- (the qed lib) — only files under a `build/ir` dir, never hand-written C like
  -- the framework's runtime/*.c that a git dependency carries in its checkout.
  -- Native.c / Cli.c each carry their own `main`; only the web entry's belongs.
  let allC ← collect ".lake" "c"
  -- Each of these modules carries its own `main`; link only the chosen web entry.
  let entryC := ((wr.splitOn ".").getLastD "") ++ ".c"   -- e.g. "ChatWeb.c"
  let altMains := ["Native.c", "Cli.c", "Web.c", "ChatWeb.c", "SignupWeb.c", "BookingWeb.c", "TodoWeb.c", "UsersWeb.c", "LocalWeb.c", "EffectsWeb.c", "Bench.c", "BenchAppWeb.c", "SignalsWeb.c", "TemplateWeb.c", "BenchScalarWeb.c", "BenchScalarDiffWeb.c", "BenchListWeb.c", "BenchListDiffWeb.c"].filter (· ≠ entryC)
  let cfiles := allC.filter (fun p =>
    (p.toString.splitOn "build/ir").length > 1 && (p.fileName.getD "") ∉ altMains)
  IO.FS.createDirAll outDir
  let tc ← toolchainDir
  let qh ← frameworkHome
  let code ← runEmcc (emccArgs cfiles (outDir / "qed.js") prod tc qh)
  return code == 0

/-- Copy the page + host driver (+ server for prod) next to the wasm. -/
def stageAssets (outDir : FilePath) (withServer : Bool) : IO Unit := do
  let names := if withServer then ["index.html", "host.js", "serve.py"] else ["index.html", "host.js"]
  for n in names do
    let src ← runtimeFile n
    let _ ← sh "cp" #[src.toString, (outDir / n).toString]

def writeBuildId (outDir : FilePath) : IO Unit := do
  IO.FS.writeFile (outDir / "__build_id") (toString (← IO.monoMsNow))

/-! ### Verification (run by build/dev/check) -/

def grepForbidden : IO Bool := do
  -- Check proof-bearing app/framework sources. Skip build dirs, the axiom
  -- manifest (mentions `sorryAx`), and the CLI itself (these words appear in it
  -- as string data, not as tactics).
  let all ← collect "." "lean" [".lake", ".qed", "dist", "toolchains", "node_modules", ".git", "scripts"]
  let files := all.filter (fun p => p.fileName != some "Cli.lean")
  let bad := ["sorry", "admit", "native_decide"]
  let mut clean := true
  for f in files do
    for line in (← IO.FS.readFile f).splitOn "\n" do
      let isPolicy := (line.splitOn "never emit").length > 1 || (line.splitOn "fails to compile").length > 1
      if !isPolicy && bad.any (fun w => (line.splitOn w).length > 1) then
        IO.eprintln (red s!"  forbidden tactic in {f}: {line.trim}")
        clean := false
  return clean

def axiomClean : IO Bool := do
  if !(← axiomsManifest.pathExists) then return true
  let (_, out) ← shOut "lake" #["env", "lean", "--root=.", axiomsManifest.toString]
  IO.print out
  return !((out.splitOn "sorryAx").length > 1) && !((out.splitOn "error:").length > 1)

/-- Every effect `kind` a `Cmd` can emit (`.fx "…"` / `.fxResult "…"` in `Runtime.lean`)
    must have a matching `case '…'` in the host's effect switch, or that effect silently
    no-ops at runtime. This static diff keeps the Lean and JS sides honest — the one bug
    that otherwise only shows up as a `console.warn` in a user's browser. Silent on
    success; prints the offenders (and returns false) on a gap. -/
def effectsCovered : IO Bool := do
  let qh ← frameworkHome
  let runtimePath := qh / "Qed" / "Runtime.lean"
  let hostPath    := qh / "runtime" / "host.js"
  unless (← runtimePath.pathExists) && (← hostPath.pathExists) do return true  -- not the framework layout
  let runtime ← IO.FS.readFile runtimePath
  let host    ← IO.FS.readFile hostPath
  -- the first quoted token after each `marker`
  let after (marker close src : String) : List String :=
    match src.splitOn marker with
    | _ :: rest => rest.map (fun c => (c.splitOn close).headD "")
    | []        => []
  let emitted := (after ".fx \"" "\"" runtime) ++ (after ".fxResult \"" "\"" runtime)
  let handled := after "case '" "'" host
  let missing := emitted.filter (fun k => k != "" && !handled.contains k)
  for k in missing do
    IO.eprintln (red s!"  effect kind \"{k}\" is emitted by a Cmd but no host.js case handles it")
  return missing.isEmpty

def verify : IO Bool := do
  step "checking proofs (lake build)"
  if (← sh "lake" #["build"]) != 0 then return false
  let wr ← webRoot
  if (← sh "lake" #["build", wr ++ ":c.o"]) != 0 then return false
  step "verifying (no sorry / axiom-clean / effect coverage)"
  let ok1 ← grepForbidden
  let ok2 ← axiomClean
  let ok3 ← effectsCovered
  return ok1 && ok2 && ok3

/-! ### Commands -/

def cmdCheck : IO UInt32 := do
  if (← verify) then IO.println (green "✓ verified"); return 0
  else IO.eprintln (red "✗ verification failed"); return 1

def cmdBuild (prod : Bool) : IO UInt32 := do
  if !(← verify) then IO.eprintln (red "✗ verification failed"); return 1
  let outDir := if prod then distDir else devDir
  step (if prod then "linking optimized WASM → dist/" else "linking WASM")
  if !(← linkWasm outDir prod) then IO.eprintln (red "✗ wasm link failed"); return 1
  stageAssets outDir (withServer := prod)
  IO.println (green s!"✓ build complete → {outDir}")
  return 0

def serveDir (dir : FilePath) : IO UInt32 := do
  IO.println s!"serving {dir} → http://localhost:{devPort}"
  let serve ← runtimeFile "serve.py"
  sh "python3" #[serve.toString, devPort, dir.toString]

def cmdStart : IO UInt32 := do
  if !(← (distDir / "qed.wasm").pathExists) then
    IO.eprintln (red "no production build found — run `qed build` first"); return 1
  serveDir distDir

def cmdTest : IO UInt32 := do
  let mut failed := false
  -- Counter: build the default web entry, then drive it.
  if (← (FilePath.mk "test" / "browser_test.mjs").pathExists) then
    if (← cmdBuild (prod := false)) != 0 then return 1
    step "running browser tests (counter)"
    if (← sh "node" #["test/browser_test.mjs"]) != 0 then failed := true
  -- Chat: the screenshot test builds the chat entry + mock backend itself.
  if (← (FilePath.mk "test" / "chat_test.mjs").pathExists) then
    step "running screenshot tests (chat)"
    if (← sh "node" #["test/chat_test.mjs"]) != 0 then failed := true
  -- Signup: the form test builds the signup entry itself.
  if (← (FilePath.mk "test" / "signup_test.mjs").pathExists) then
    step "running form tests (signup)"
    if (← sh "node" #["test/signup_test.mjs"]) != 0 then failed := true
  -- Booking: threads the current time in via Cmd.now; builds its own entry.
  if (← (FilePath.mk "test" / "booking_test.mjs").pathExists) then
    step "running current-time tests (booking)"
    if (← sh "node" #["test/booking_test.mjs"]) != 0 then failed := true
  -- Todo: dynamic add/remove; asserts surviving rows keep their DOM identity.
  if (← (FilePath.mk "test" / "todo_test.mjs").pathExists) then
    step "running dynamic-list tests (todo)"
    if (← sh "node" #["test/todo_test.mjs"]) != 0 then failed := true
  -- Users: HTTP fetch+decode, URL routing, and the form/keyboard/focus events.
  if (← (FilePath.mk "test" / "users_test.mjs").pathExists) then
    step "running routing/http/events tests (users)"
    if (← sh "node" #["test/users_test.mjs"]) != 0 then failed := true
  -- Local: keyed local-state components — sibling isolation, caret, bubbling, persist.
  if (← (FilePath.mk "test" / "local_test.mjs").pathExists) then
    step "running local-state tests (local)"
    if (← sh "node" #["test/local_test.mjs"]) != 0 then failed := true
  -- Effects: native effect set (storage/title/timer/random/file/batch/focus) + ports.
  if (← (FilePath.mk "test" / "effects_test.mjs").pathExists) then
    step "running native-effects tests (effects)"
    if (← sh "node" #["test/effects_test.mjs"]) != 0 then failed := true
  -- Signals: fine-grained reactivity — setSignal updates only the bound node, no re-render.
  if (← (FilePath.mk "test" / "signals_test.mjs").pathExists) then
    step "running signals tests (signals)"
    if (← sh "node" #["test/signals_test.mjs"]) != 0 then failed := true
  -- View templates: build once, patch only changed bindings; lists update via signals.
  if (← (FilePath.mk "test" / "template_test.mjs").pathExists) then
    step "running template tests (View)"
    if (← sh "node" #["test/template_test.mjs"]) != 0 then failed := true
  if failed then return 1 else return 0

def cmdClean : IO UInt32 := do
  let _ ← sh "lake" #["clean"]
  let _ ← sh "rm" #["-rf", distDir.toString, (FilePath.mk ".qed").toString]
  IO.println (green "✓ cleaned")
  return 0

partial def watchLoop (marker : FilePath) : IO Unit := do
  IO.sleep 400
  let qh ← frameworkHome
  let find := s!"find . -name '*.lean' -newer {marker} -not -path './.lake/*' -not -path './.qed/*' 2>/dev/null | head -1; " ++
              s!"find {qh}/runtime -newer {marker} 2>/dev/null | head -1"
  let (_, out) ← shOut "bash" #["-c", find]
  if out.trim != "" then
    let _ ← sh "touch" #[marker.toString]
    step "change detected — rebuilding"
    if (← linkWasm devDir (prod := false)) then
      stageAssets devDir (withServer := false)
      writeBuildId devDir
      let _ ← effectsCovered   -- warn (non-fatal) if a new effect lacks a host.js case
      IO.println (green "✓ reloaded")
    else
      IO.eprintln (red "✗ build failed — fix and save again")
  watchLoop marker

def cmdDev : IO UInt32 := do
  IO.FS.createDirAll devDir
  let marker := devDir / ".watch"
  let _ ← sh "touch" #[marker.toString]
  step "initial build"
  if (← linkWasm devDir (prod := false)) then
    stageAssets devDir (withServer := false)
  else
    IO.eprintln (red "initial build failed — fix the error and save; dev will rebuild")
  writeBuildId devDir
  let serve ← runtimeFile "serve.py"
  let _server ← IO.Process.spawn
    { cmd := "python3", args := #[serve.toString, devPort, devDir.toString],
      stdin := .null, stdout := .null, stderr := .inherit }
  IO.println (green s!"\nqed dev → http://localhost:{devPort}   (watching; Ctrl-C to stop)\n")
  watchLoop marker
  return 0

def cmdDoctor : IO UInt32 := do
  IO.println "qed doctor:"
  let report (label : String) (ok : Bool) : IO Unit :=
    IO.println s!"  {if ok then green "✓" else red "✗"} {label}"
  for c in ["lean", "lake", "python3", "node", "curl"] do
    report c (← onPath c)
  let hasEmcc ← onPath "emcc"
  let hasEmsdk := (← findEmsdkEnv).isSome
  report "emscripten (emcc / emsdk)" (hasEmcc || hasEmsdk)
  let tc ← toolchainDir
  report s!"wasm runtime ({wasmToolchain})" (← tc.pathExists)
  return 0

def cmdNew (dir : String) : IO UInt32 := do
  let root : FilePath := dir
  if (← root.pathExists) then IO.eprintln (red s!"{dir} already exists"); return 1
  step s!"scaffolding {dir}"
  IO.FS.createDirAll root
  IO.FS.writeFile (root / "lean-toolchain") s!"leanprover/lean4:v{leanWasmVersion}\n"
  IO.FS.writeFile (root / "lakefile.lean") <|
    "import Lake\nopen Lake DSL\n\n" ++
    "package app where\n\n" ++
    "require qed from git \"https://github.com/JacobAsmuth/qed\" @ \"main\"\n\n" ++
    "@[default_target] lean_lib App where\n\n" ++
    "lean_exe web where\n  root := `Web\n"
  IO.FS.writeFile (root / "App.lean") <|
    "import Qed\nopen Qed\n\n" ++
    "structure Model where\n  count : Int\nderiving Inhabited\n\n" ++
    "inductive Msg | increment | decrement | reset\n\n" ++
    "def init : Model := { count := 0 }\n\n" ++
    "def update (m : Model) : Msg → Model\n" ++
    "  | .increment => { m with count := m.count + 1 }\n" ++
    "  | .decrement => { m with count := if 0 < m.count then m.count - 1 else m.count }\n" ++
    "  | .reset     => { m with count := 0 }\n\n" ++
    "def view (m : Model) : Html Msg :=\n" ++
    "  div [cls \"counter\"] [\n" ++
    "    button [onClick .decrement] [text \"−\"],\n" ++
    "    span   [cls \"count\"]        [text (toString m.count)],\n" ++
    "    button [onClick .increment] [text \"+\"],\n" ++
    "    button [onClick .reset]     [text \"reset\"] ]\n\n" ++
    "def app : App Model Msg := sandbox init update view\n\n" ++
    "invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update\n"
  IO.FS.writeFile (root / "Web.lean") <|
    "import App\nimport Qed.Driver\n\ndef main : IO Unit := Qed.run app\n"
  IO.println (green s!"✓ created {dir}/")
  IO.println s!"  next:  cd {dir} && qed dev"
  return 0

def usage : IO UInt32 := do
  IO.println "qed — a verified web frontend toolchain\n"
  IO.println "Usage: qed <command>\n"
  IO.println "  dev            watch + rebuild + serve with live-reload"
  IO.println "  build          production build → dist/ (optimized, verified)"
  IO.println "  start|preview  serve the build"
  IO.println "  test           run the browser tests (if present)"
  IO.println "  check          verify proofs + no-sorry + axioms"
  IO.println "  clean          remove build outputs"
  IO.println "  new <dir>      scaffold a new app"
  IO.println "  doctor         report which dependencies are present"
  return 0

end Qed.Cli

open Qed.Cli in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["dev"]                  => cmdDev
  | ["build"]                => cmdBuild (prod := true)
  | ["build", "--dev"]       => cmdBuild (prod := false)
  | ["start"] | ["preview"]  => cmdStart
  | ["test"]                 => cmdTest
  | ["check"]                => cmdCheck
  | ["clean"]                => cmdClean
  | ["doctor"]               => cmdDoctor
  | ["new", dir]             => cmdNew dir
  | [] | ["help"] | ["--help"] | ["-h"] => usage
  | _ => IO.eprintln s!"unknown command: {" ".intercalate args}"; usage
