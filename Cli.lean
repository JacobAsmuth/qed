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

  `build` transpiles the app and the verified framework/driver to plain JavaScript
  (see `Js/Backend.lean`): the proven `render`/`diff`/`update` and the whole `Qed.run`
  loop run in the browser unchanged. No WASM, no emscripten, no cross-origin isolation.

  Two locations matter, kept separate so the CLI works outside the framework
  checkout: the current directory is the *project* (your app + lakefile), and
  `QED_HOME` is the *framework* (its `runtime/` JS + `scripts/`). The CLI orchestrates
  lake, the transpiler (`qedjs`), python3 (a static dev server), and node.
-/
open System (FilePath)

namespace Qed.Cli

/-! ### Locations -/

def leanVersion : String := "4.15.0"
def devDir      : FilePath := ".qed" / "dev"
def distDir     : FilePath := "dist"
def devPort     : String := "8000"

def env (k : String) : IO (Option String) := IO.getEnv k

/-- The framework checkout (its `runtime/` JS and `scripts/`). Defaults to the
    current directory for in-repo development. -/
def frameworkHome : IO FilePath := return (← env "QED_HOME").getD "."
/-- The project's web-entry module. Apps use `Web`; the framework demo overrides
    this to `Examples.Web` via `QED_WEB_ROOT`. -/
def webRoot : IO String := return (← env "QED_WEB_ROOT").getD "Web"
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
  let driverPath  := qh / "Qed" / "Driver.lean"
  let hostPath    := qh / "runtime" / "qed_host.mjs"
  unless (← runtimePath.pathExists) && (← hostPath.pathExists) do return true  -- not the framework layout
  let runtime ← IO.FS.readFile runtimePath
  let driver  ← if (← driverPath.pathExists) then IO.FS.readFile driverPath else pure ""
  let host    ← IO.FS.readFile hostPath
  -- the first quoted token after each `marker`
  let after (marker close src : String) : List String :=
    match src.splitOn marker with
    | _ :: rest => rest.map (fun c => (c.splitOn close).headD "")
    | []        => []
  -- kinds come from `Cmd` smart constructors (`.fx`/`.fxResult` in Runtime) AND from the
  -- driver itself (`Dom.effect "…"`, e.g. `signal.set`/`ws.open`/`event.listen`) — both must
  -- have a qed_host.mjs case, so scan both files.
  let emitted := (after ".fx \"" "\"" runtime) ++ (after ".fxResult \"" "\"" runtime)
              ++ (after "Dom.effect \"" "\"" driver) ++ (after "Dom.effectResult \"" "\"" driver)
  let handled := after "case '" "'" host
  let missing := emitted.filter (fun k => k != "" && !handled.contains k)
  for k in missing do
    IO.eprintln (red s!"  effect kind \"{k}\" is emitted by a Cmd but no qed_host.mjs case handles it")
  return missing.isEmpty

/-- Net bracket nesting a token contributes (`{`/`(`/`[` open, `}`/`)`/`]` close). -/
def bracketDelta (s : String) : Int :=
  s.foldl (fun d c =>
    if c == '{' || c == '(' || c == '[' then d + 1
    else if c == '}' || c == ')' || c == ']' then d - 1 else d) 0

/-- Drop one `term:max` from the front of a token list — a single token, or a balanced
    `{…}`/`(…)`/`[…]` group — so a record-literal `init` (`ui { … } update fun …`) is
    skipped whole and the *next* token is the update term. -/
def dropTerm : List String → List String
  | []       => []
  | t0 :: tl =>
      let rec skip (depth : Int) : List String → List String
        | []      => []
        | r :: rs => if depth ≤ 0 then r :: rs else skip (depth + bracketDelta r) rs
      skip (bracketDelta t0) tl

/-- A non-fatal nudge (never gates the build): app updates wired into a `ui` builder that
    carry no `invariant … preserved_by <update>`. Changing your program's state is almost
    always a claim you can state and have machine-checked, so a zero here is worth a second
    look — but an honest "nothing to prove here" is fine, which is why this only reports,
    never fails. Heuristic and per-file (a builder and its invariant live in the same
    module), comment-aware so prose mentioning `ui` doesn't count. -/
def invariantNote : IO Unit := do
  let files := (← collect "." "lean" [".lake", ".qed", "dist", "toolchains", "node_modules", ".git", "scripts"])
    |>.filter (·.fileName != some "Cli.lean")   -- this file holds the keywords as string data
  let tokensOf (line : String) : List String :=
    ((line.replace "\t" " ").splitOn " ").filter (· != "")
  let isName (s : String) : Bool :=
    !s.isEmpty && s != "fun" && s.all (fun c => c.isAlphanum || c == '_' || c == '.' || c == '\'')
  let mut uncovered : Array (FilePath × String) := #[]
  for f in files do
    let mut depth : Nat := 0                 -- multi-line `/- … -/` nesting
    let mut updates : List String := []      -- update fns wired into a `ui` builder here
    let mut covered : List String := []      -- update fns this file states an invariant for
    for raw in (← IO.FS.readFile f).splitOn "\n" do
      let inComment := depth > 0
      depth := depth + ((raw.splitOn "/-").length - 1) - ((raw.splitOn "-/").length - 1)
      if inComment then continue             -- inside a block comment: skip the whole line
      let ts := tokensOf ((raw.splitOn "--").headD raw)   -- drop a `--` line comment
      match ts.dropWhile (· != "preserved_by") with       -- `… preserved_by upd`
      | _ :: name :: _ => covered := name :: covered
      | _              => pure ()
      let afterUi := (ts.dropWhile (· != "ui")).drop 1     -- tokens after a `ui` builder token
      if afterUi.contains "fun" then                       -- a real `ui … fun … =>` call, not prose
        match dropTerm afterUi with                        -- skip the `init` term; update is next
        | upd :: _ => if isName upd then updates := upd :: updates
        | []       => pure ()
    for u in updates do
      unless covered.contains u do uncovered := uncovered.push (f, u)
  unless uncovered.isEmpty do
    IO.println s!"  note: {uncovered.size} update(s) change state with no `invariant … preserved_by` — consider stating one:"
    for (f, u) in uncovered do IO.println s!"    {u}  ({f})"

def verify : IO Bool := do
  step "checking proofs (lake build)"
  if (← sh "lake" #["build"]) != 0 then return false
  -- Build the example modules too, so their proofs are checked — the `invariant`s (model
  -- `preserved_by` and styling `holds_in`) are theorems that only fire when their module builds.
  if (← sh "lake" #["build", "Examples"]) != 0 then return false
  step "verifying (no sorry / axiom-clean / effect coverage)"
  let ok1 ← grepForbidden
  let ok2 ← axiomClean
  let ok3 ← effectsCovered
  return ok1 && ok2 && ok3

/-! ### Commands -/

def cmdCheck : IO UInt32 := do
  if (← verify) then
    invariantNote          -- informational nudge after a clean verdict; never gates `check`
    IO.println (green "✓ verified"); return 0
  else IO.eprintln (red "✗ verification failed"); return 1

/-- The app's *web entry* module — the one whose `main` is `Qed.run app` (what
    `qed new` scaffolds). Set `QED_JS_ROOT` for the framework's own examples. -/
def jsRoot : IO String := do
  match ← env "QED_JS_ROOT" with
  | some r => return r
  | none   => return (← env "QED_WEB_ROOT").getD "Web"

/-- The page that loads the transpiled app. In dev it polls `__build_id` to live-reload.
    Paths are absolute (and `<base href="/">` is set) so deep-link routes like `/users/ada`
    still resolve the module and assets correctly. -/
def indexHtml (dev : Bool) : String :=
  let reload := if dev then
    "<script>(function(){let v=null;setInterval(async()=>{try{const t=await (await fetch('/__build_id',{cache:'no-store'})).text();if(v&&v!==t)location.reload();v=t;}catch(e){}},700)})()</script>\n"
  else ""
  "<!doctype html>\n<html lang=\"en\">\n<head><meta charset=\"utf-8\"><base href=\"/\">" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"><title>qed</title></head>\n" ++
  "<body><div id=\"app\">loading…</div>\n" ++ reload ++
  "<script type=\"module\" src=\"/qed_host.mjs\"></script>\n</body>\n</html>\n"

/-- The transpiler entry set: the app's `main` (`Qed.run app`) plus the framework's 13
    `@[export]` driver functions. This is fixed and app-agnostic — no per-app shim. -/
def driverEntries : Array String := #[
  "main:__main",
  "Qed.qedInit:qed_init", "Qed.qedDispatch:qed_dispatch", "Qed.qedDispatchStr:qed_dispatch_str",
  "Qed.qedStreamChunk:qed_stream_chunk", "Qed.qedStreamDone:qed_stream_done",
  "Qed.qedHttpDone:qed_http_done", "Qed.qedUrlChanged:qed_url_changed",
  "Qed.qedLocalDispatch:qed_local_dispatch", "Qed.qedLocalDispatchStr:qed_local_dispatch_str",
  "Qed.qedLocalSnapshot:qed_local_snapshot", "Qed.qedLocalRestore:qed_local_restore",
  "Qed.qedEffectDone:qed_effect_done", "Qed.qedPortRecv:qed_port_recv"]

/-- Transpile the app AND the verified framework/driver (render, the proven diff, the
    whole `Qed.run` loop) to plain JavaScript and stage a runnable bundle in `outDir`.
    The only hand-written JS is the DOM externs + event/effect host (`qed_dom.mjs` /
    `qed_host.mjs`), the irreducible FFI. Works for any app whose entry is `Qed.run app`. -/
def buildJs (outDir : FilePath) (prod : Bool) : IO Bool := do
  let mod ← jsRoot
  if (← sh "lake" #["build", mod, "qedjs"]) != 0 then return false
  IO.FS.createDirAll outDir
  let qedjs := ((".lake" : FilePath) / "build" / "bin" / "qedjs").toString
  let appOut := (outDir / "app.mjs").toString
  let minArgs := if prod then #["--min"] else #[]   -- the transpiler already tree-shakes
  if (← sh "lake" (#["env", qedjs] ++ minArgs ++ #[appOut, mod, "--"] ++ driverEntries)) != 0 then
    return false
  for f in ["qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"] do
    IO.FS.writeFile (outDir / f) (← IO.FS.readFile (← runtimeFile f))
  IO.FS.writeFile (outDir / "index.html") (indexHtml (dev := !prod))
  if prod then
    if (← onPath "esbuild") then
      for f in ["app.mjs", "qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"] do
        let p := (outDir / f).toString
        discard <| sh "bash" #["-c", s!"esbuild {p} --minify --format=esm --outfile={p}.min && mv {p}.min {p}"]
  return true

def cmdBuild (prod : Bool) : IO UInt32 := do
  if !(← verify) then IO.eprintln (red "✗ verification failed"); return 1
  let outDir := if prod then distDir else devDir
  step s!"transpiling Lean → JavaScript → {outDir}/"
  if !(← buildJs outDir prod) then IO.eprintln (red "✗ build failed"); return 1
  let (_, sz) ← shOut "bash" #["-c", s!"cat {outDir}/*.mjs | gzip -c | wc -c"]
  IO.println (green s!"✓ build complete → {outDir} (no WASM) — {sz.trim} bytes gzipped")
  return 0

def serveDir (dir : FilePath) : IO UInt32 := do
  IO.println s!"serving {dir} → http://localhost:{devPort}"
  sh "python3" #["-m", "http.server", devPort, "--directory", dir.toString]

def cmdStart : IO UInt32 := do
  if !(← (distDir / "app.mjs").pathExists) then
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
  -- SSR + hydration: server-rendered #app is adopted in place by the client (no rebuild).
  if (← (FilePath.mk "test" / "ssr_test.mjs").pathExists) then
    step "running SSR/hydration tests"
    if (← sh "node" #["test/ssr_test.mjs"]) != 0 then failed := true
  -- Dynamic SSR: a per-request Lean renderer produces the page for each route.
  if (← (FilePath.mk "test" / "ssr_dynamic_test.mjs").pathExists) then
    step "running dynamic-SSR tests"
    if (← sh "node" #["test/ssr_dynamic_test.mjs"]) != 0 then failed := true
  -- Template hydration: a view% fine-grained template app adopts server DOM (incl. signals).
  if (← (FilePath.mk "test" / "ssr_template_test.mjs").pathExists) then
    step "running template-hydration tests"
    if (← sh "node" #["test/ssr_template_test.mjs"]) != 0 then failed := true
  -- Bookshelf: the full stack in one app — routing + Resource (list+detail) + form POST + styles.
  if (← (FilePath.mk "test" / "bookshelf_test.mjs").pathExists) then
    step "running end-to-end app tests (bookshelf)"
    if (← sh "node" #["test/bookshelf_test.mjs"]) != 0 then failed := true
  -- Bookshelf SSR: a per-request Lean renderer produces each route's page server-side.
  if (← (FilePath.mk "test" / "bookshelf_ssr_test.mjs").pathExists) then
    step "running end-to-end SSR tests (bookshelf)"
    if (← sh "node" #["test/bookshelf_ssr_test.mjs"]) != 0 then failed := true
  -- Dehydrated SSR: the client starts from the server's model (no flash, no refetch).
  if (← (FilePath.mk "test" / "bookshelf_hydrate_test.mjs").pathExists) then
    step "running end-to-end hydration tests (bookshelf dehydrated SSR)"
    if (← sh "node" #["test/bookshelf_hydrate_test.mjs"]) != 0 then failed := true
  -- WebSockets: open/send/receive/close over a real socket against an echo server.
  if (← (FilePath.mk "test" / "socket_test.mjs").pathExists) then
    step "running end-to-end WebSocket tests (socket)"
    if (← sh "node" #["test/socket_test.mjs"]) != 0 then failed := true
  -- Live handlers: a message embedding model state stays current across updates.
  if (← (FilePath.mk "test" / "live_test.mjs").pathExists) then
    step "running end-to-end live-handler tests (live)"
    if (← sh "node" #["test/live_test.mjs"]) != 0 then failed := true
  -- JS transpiler — the differential gate: transpiled-from-Lean functions must be
  -- byte-identical to native Lean (render, diff, JSON, Date, strings, closures…).
  if (← (FilePath.mk "test" / "js_gate_test.mjs").pathExists) then
    step "running differential gate (transpiled JS == native Lean)"
    if (← sh "node" #["test/js_gate_test.mjs"]) != 0 then failed := true
  -- JS transpiler — the FULL transpiled driver (no WASM): build, then drive it in a browser.
  if (← (FilePath.mk "test" / "js_driver_browser_test.mjs").pathExists) then
    step "building JS bundle + running transpiled-driver browser test"
    if !(← buildJs devDir (prod := false)) then failed := true
    else if (← sh "node" #["test/js_driver_browser_test.mjs"]) != 0 then failed := true
  -- SVG namespaces: createElement + childNamespace inheritance (incl. foreignObject) + xlink attrs.
  if (← (FilePath.mk "test" / "svg_test.mjs").pathExists) then
    step "running SVG namespace tests (DOM boundary)"
    if (← sh "node" #["test/svg_test.mjs"]) != 0 then failed := true
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
    if (← buildJs devDir (prod := false)) then
      writeBuildId devDir
      let _ ← effectsCovered   -- warn (non-fatal) if a new effect lacks a qed_host.mjs case
      IO.println (green "✓ reloaded")
    else
      IO.eprintln (red "✗ build failed — fix and save again")
  watchLoop marker

def cmdDev : IO UInt32 := do
  IO.FS.createDirAll devDir
  let marker := devDir / ".watch"
  let _ ← sh "touch" #[marker.toString]
  step "initial build"
  unless (← buildJs devDir (prod := false)) do
    IO.eprintln (red "initial build failed — fix the error and save; dev will rebuild")
  writeBuildId devDir
  let _server ← IO.Process.spawn
    { cmd := "python3", args := #["-m", "http.server", devPort, "--directory", devDir.toString],
      stdin := .null, stdout := .null, stderr := .inherit }
  IO.println (green s!"\nqed dev → http://localhost:{devPort}   (watching; Ctrl-C to stop)\n")
  watchLoop marker
  return 0

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
  IO.FS.writeFile (root / "lean-toolchain") s!"leanprover/lean4:v{leanVersion}\n"
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
    "def app : App Model Msg := ui init update fun m =>\n" ++
    "  div [cls \"counter\"] [\n" ++
    "    button [onClick .decrement] [text \"−\"],\n" ++
    "    span   [cls \"count\"]        [text (toString m.count)],\n" ++
    "    button [onClick .increment] [text \"+\"],\n" ++
    "    button [onClick .reset]     [text \"reset\"] ]\n\n" ++
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
