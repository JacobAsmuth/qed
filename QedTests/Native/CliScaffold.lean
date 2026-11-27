import QedTests.Native.Harness
import Cli.Watch
import Js.Backend
open System (FilePath)
open Qed.Server Qed.Cli.Watch

namespace QedTests.Native.CliScaffold

private def isHashedMjs (prefixStr s : String) : Bool :=
  s.startsWith s!"/{prefixStr}." && s.endsWith ".mjs" && s.length == prefixStr.length + 18

private def checkSourceMapJson (c : TestChecker) (tag : String) (mapPath : FilePath) (wantFile : String) (checkDetails : Bool := false) : IO Unit := do
  let existsF ← mapPath.pathExists; c.check s!"{tag} .mjs.map exists" existsF
  if !existsF then return
  let raw ← IO.FS.readFile mapPath
  c.expectOk s!"{tag} sourcemap valid JSON" (Qed.Json.parse raw) fun sm => do
    c.checkJsonInt s!"{tag} sourcemap version == 3" sm "version" 3
    c.checkJsonStr s!"{tag} sourcemap file == {wantFile}" sm "file" wantFile
    if checkDetails then
      c.checkJsonArr s!"{tag} sourcemap lists App.lean in sources" sm "sources" (fun xs => !xs.isEmpty && xs.any (·.str? == some "App.lean")) raw
      c.checkJsonArr s!"{tag} sourcemap has non-empty names" sm "names" (!·.isEmpty)
      c.checkJsonPath s!"{tag} sourcemap has non-empty VLQ mappings" sm "mappings" fun | .str m => !m.isEmpty && m.contains ";" | _ => false

private def runPureVlqAndWatcherChecks (c : TestChecker) (scratch : String) : IO Unit := do
  forList [(0, "A"), (1, "C"), (-1, "D"), (16, "gB"), (-16, "hB"), (123, "2H")] fun (n, want) => c.checkEq s!"VLQ encode {n}" (Js.encodeVlqInt n) want
  let (seenIds, _, idsClean) := (List.range 400).foldl (init := (({} : Std.HashSet String), 0, true)) fun (seen, idx, ok) _ =>
    let (nm, nextIdx) := Js.nextShortIdent Js.jsMinReservedSet idx
    (seen.insert nm, nextIdx, ok && !seen.contains nm && !Js.jsMinReservedSet.contains nm && !nm.startsWith "$" && !nm.startsWith "_")
  c.checkAll [
    ("VLQ encode/decode round-trip on all samples", [0, 1, -1, 15, -15, 16, -16, 123, -123, 1024, -1024, 99999, -99999].all fun v => Js.decodeVlqInt (Js.encodeVlqInt v) == some v),
    ("400 generated short identifiers are unique and skip reserved words/$", seenIds.size == 400 && idsClean)]
  runTasks [
    (do
      let (watchRoot, watchRt) := (FilePath.mk scratch / "watch_proj", FilePath.mk scratch / "watch_rt")
      IO.FS.createDirAll (watchRoot / ".lake"); IO.FS.createDirAll watchRt
      -- Write fixture files from a short-lived child so concurrent `IO.Process.spawn` calls in sibling suites cannot inherit non-CLOEXEC writable FDs and emit delayed Linux `IN_CLOSE_WRITE` events.
      let writeInChild (path content : String) : IO Unit := discard <| runCmd "sh" #["-c", "printf '%s' \"$1\" > \"$2\"", "--", content, path]
      forList [(watchRoot / "Demo.lean", "def x := 1\n"), (watchRoot / "site.css", "body{}\n"), (watchRt / "qed_dev.mjs", "// v1\n")] fun (p, s) => writeInChild p.toString s
      c.expectOk "OS file watcher opens cleanly" (← FileWatcher.open watchRoot.toString watchRt.toString #[".lake", ".git"]) fun w => do
        try
          writeInChild (watchRoot / ".lake" / "ignored.lean").toString "-- ignore\n"
          let evSkip ← w.wait 80; c.check "OS watcher ignores skipped .lake/ directory" (!evSkip.any && !evSkip.error) (reprStr evSkip)
          forList [(".lean", watchRoot / "Demo.lean", "def x := 2\n", fun (e : WatchEvents) => e.lean),
              (".css", watchRoot / "site.css", "body{color:red}\n", fun e => e.css), ("runtime .mjs", watchRt / "qed_dev.mjs", "// v2\n", fun e => e.runtime)] fun (label, path, content, proj) => do
            let t ← IO.asTask (prio := .dedicated) (w.wait 1500); IO.sleep 30; writeInChild path.toString content
            let ev := (← IO.wait t).toOption.getD { lean := false, css := false, runtime := false, error := true }
            c.check s!"OS watcher detects {label} modification" (proj ev && !ev.error) (reprStr ev)
        finally w.close),
    (do
      c.expectOk "DevSseServer starts on ephemeral port" (← DevSseServer.start 0) fun sse => do
        try
          c.check "DevSseServer bound ephemeral port > 0" (sse.port > 0)
          sse.publish "{\"id\":\"42\",\"status\":\"ok\",\"kind\":\"hmr\",\"durationMs\":9,\"error\":\"\"}"
          c.expectOk "TCP connect to DevSseServer" (← Prim.outboundAcquire 0 "127.0.0.1" sse.port 0 (fun _ => false)) fun (hNat, _) => do
            let h := hNat.toUInt64
            let okW := (← Prim.outboundWriteAll h s!"GET /events HTTP/1.1\r\nHost: 127.0.0.1:{sse.port}\r\nAccept: text/event-stream\r\n\r\n".toUTF8).isOk
            let readStr : IO String := do if !okW then return "" else return ((← Prim.outboundReadSome h 4096).toOption.bind String.fromUTF8?).getD ""
            let body ← readStr; IO.sleep 30
            sse.publish "{\"id\":\"43\",\"status\":\"building\",\"kind\":\"hmr\",\"durationMs\":0,\"error\":\"\"}"
            let pushed ← readStr; Prim.outboundRelease h 0
            c.check "DevSseServer returns 200 text/event-stream with CORS and initial event" (["200 OK", "text/event-stream", "Access-Control-Allow-Origin: *", "data: {\"id\":\"42\",\"status\":\"ok\""].all (body.contains ·)) body
            c.check "DevSseServer pushes live building event to connected client" (pushed.contains "data: {\"id\":\"43\",\"status\":\"building\"") pushed
        finally sse.stop)]

def run : IO Bool := do
  let c ← mkChecker "cli-scaffold"
  let (root, cli, qedjs) := (← IO.currentDir, ← qedBinPath, ← qedjsBinPath)
  let cleanEnv : Array (String × Option String) := #[("QED_HOME", some root.toString), ("QED_WEB_ROOT", none), ("QED_JS_ROOT", none),
    ("QED_SKIP_VERIFY", none), ("LEAN_PATH", none), ("QED_PREBUILT", none), ("QED_OUT_DIR", none)]
  let runCli (label : String) (cwd : FilePath) (args : Array String) : IO Unit := do
    let (code, out, err) ← runCmd cli args (cwd := some cwd) (env := cleanEnv); c.check label (code == 0) (out ++ err)
  withTempDir "qed-scaffold-test" fun scratch => do
    let tSide ← IO.asTask (prio := .dedicated) (runPureVlqAndWatcherChecks c scratch)
    let appDir := FilePath.mk s!"{scratch}/app"
    runCli "qed new succeeds" root #["new", appDir.toString]
    c.checkEq "lean-toolchain matches repo" (← IO.FS.readFile (appDir / "lean-toolchain")) (← IO.FS.readFile (root / "lean-toolchain"))
    let lfPath := appDir / "lakefile.lean"
    IO.FS.writeFile lfPath ((← IO.FS.readFile lfPath).replace "from git \"https://github.com/JacobAsmuth/qed\" @ \"main\"" s!"from \"{root.toString}\"")
    runCli "qed build succeeds" appDir #["build"]
    let distDir := appDir / "dist"; let manifestRaw ← IO.FS.readFile (distDir / "qed_manifest.json")
    let (hostPath, appPath) := (Qed.Json.pathStr manifestRaw "host", Qed.Json.pathStr manifestRaw "app")
    forList [("host", "qed_host", hostPath), ("app", "app", appPath), ("rt", "qed_rt", Qed.Json.pathStr manifestRaw "rt"), ("dom", "qed_dom", Qed.Json.pathStr manifestRaw "dom")] fun (key, pfx, p) =>
      c.check s!"manifest {key} hashed" (isHashedMjs pfx p) p
    forList [("unhashed dist/app.mjs removed", distDir / "app.mjs", false), ("dev client qed_dev.mjs omitted from prod dist", distDir / "qed_dev.mjs", false), ("native dist/server binary built", distDir / "server", true)] fun (lbl, p, want) => do
      c.check lbl ((← p.pathExists) == want)
    let appJs ← IO.FS.readFile (distDir / dropChars appPath)
    c.checkAll [("app bundle contains qed_init", appJs.contains "qed_init"), ("app bundle exports qed_dehydrate for HMR", appJs.contains "qed_dehydrate"),
      ("minified prod app.mjs removes _g0 internal prefix", !appJs.contains "function _g0(" && !appJs.contains "const _g0 "),
      ("minified prod app.mjs strips /* comments */", !appJs.contains "/* "), ("minified prod app.mjs preserves $ runtime calls", appJs.contains "$.")]
    let secretDir := appDir / "dist-secret"; IO.FS.createDirAll secretDir
    IO.FS.writeFile (secretDir / "leak.txt") "TOP_SECRET_SIBLING"
    discard <| runCmd "ln" #["-s", (secretDir / "leak.txt").toString, (distDir / "escape.txt").toString]
    runTasks [
      (withNativeServer c "standalone native server healthy" distDir.toString #[] (dev := false) fun srv => do
        c.checkHttp "SSR GET /" (← httpReq srv.port "GET" "/") (contains := ["<span>1</span>", hostPath])
        c.checkHttp "GET hashed asset" (← httpReq srv.port "GET" appPath) (headers := [("cache-control", some "public, max-age=31536000, immutable"), ("x-content-type-options", some "nosniff")])
        forList [("blocks /../dist-secret/leak.txt", "/../dist-secret/leak.txt"), ("blocks /%2e%2e%2fdist-secret/leak.txt", "/%2e%2e%2fdist-secret/leak.txt"), ("blocks symlink /escape.txt", "/escape.txt")] fun (lbl, p) =>
          c.checkRawNoLeak srv.port lbl p "TOP_SECRET_SIBLING"),
      (do
        let staticPort ← Prim.freePort
        withNativeBin c "qed serve native static server healthy" cli #["serve", distDir.toString, toString staticPort, "--dev"] staticPort cleanEnv fun _ => do
          c.checkStatus "qed serve serves hashed asset 200" (← httpReq staticPort "GET" appPath) 200
          c.checkHttp "qed serve GET /__dev_status" (← httpReq staticPort "GET" "/__dev_status") (contains := ["\"status\":\"ok\""])),
      (do
        let strippedRt := s!"{scratch}/stripped_rt.mjs"
        IO.FS.writeFile strippedRt ((← IO.FS.readFile (root / "runtime" / "qed_rt.mjs")).replace "export const Array_push" "export const Removed_Array_push")
        let (cExt, outExt, errExt) ← runCmd "lake" #["env", qedjs, "--check-externs", strippedRt, "App", "--", "Quantity.app:app"] (cwd := some appDir) (env := cleanEnv)
        c.check "stripped qed_rt fails --check-externs" (cExt != 0 && (outExt ++ errExt).contains "Array_push") (outExt ++ errExt)),
      (do
        runCli "qed build --dev succeeds" appDir #["build", "--dev", "--no-verify"]
        let devOut := appDir / ".qed" / "dev"; let devAppJs ← IO.FS.readFile (devOut / "app.mjs")
        c.checkAll [("dev app.mjs references sourceMappingURL", devAppJs.contains "//# sourceMappingURL=app.mjs.map"),
          ("dev qed_dev.mjs emitted", ← (devOut / "qed_dev.mjs").pathExists)]
        checkSourceMapJson c "dev" (devOut / "app.mjs.map") "app.mjs" (checkDetails := true)
        c.check "minified prod app.mjs is >25% smaller than dev app.mjs" (appJs.length * 4 < devAppJs.length * 3) s!"prod={appJs.length} dev={devAppJs.length}")]
    runCli "qed build --sourcemap succeeds" appDir #["build", "--sourcemap"]
    let appName2 := dropChars (Qed.Json.pathStr (← IO.FS.readFile (distDir / "qed_manifest.json")) "app")
    c.check "prod --sourcemap appends hashed sourceMappingURL" ((← IO.FS.readFile (distDir / appName2)).contains s!"//# sourceMappingURL={appName2}.map")
    checkSourceMapJson c "prod" (distDir / s!"{appName2}.map") appName2
    let appLean := appDir / "App.lean"; let validSrc ← IO.FS.readFile appLean
    let withBenign := (validSrc.replace "<span>{quantity}</span>" "<span>{my_handler(my_step(quantity + initState - 1))}</span>\n      <small>{admitted_sorry_msg}</small>").replace "open Qed\n"
      ("open Qed\n\n-- comments mentioning sorry, admit, native_decide must be ignored\n/- nested /- block comment with sorry and admit -/ still comment -/\n" ++
       "def initState : Nat := 1\ndef my_handler (n : Nat) : Nat := n\ndef my_step (n : Nat) : Nat := n\ndef admitted_sorry_msg : String := \"We are sorry, please admit this item\"\n")
    forList [("benign comments/strings/client helpers pass qed check", withBenign, true, ""),
        ("real sorry inside interpolated string rejected", validSrc ++ "\ndef badInterp : String := s!\"{(by sorry : Nat)}\" -- never emit\n", false, "forbidden token `sorry`"),
        ("partial def rejected by kernel gate", validSrc ++ "\npartial def spin (n : Nat) : Nat := spin n\n", false, "kernel gate: `partial` or `opaque` declaration `spin`"),
        ("repeatM loop rejected by kernel gate", validSrc ++ "\ndef badRepeat (n : Nat) : Id Nat := repeatM (fun i => if i < n then pure (.inl (i + 1)) else pure (.inr i)) 0\n", false, "kernel gate: unbounded `while`/`repeat`/`partial_fixpoint` loop inside `badRepeat`")] fun (label, src, wantOk, wantSub) => do
      IO.FS.writeFile appLean src
      let (code, out, err) ← runCmd cli #["check"] (cwd := some appDir) (env := cleanEnv); let combined := out ++ err
      c.check label ((code == 0) == wantOk && (wantSub.isEmpty || combined.contains wantSub)) combined
    if let .error e ← IO.wait tSide then throw e
  c.finish

end QedTests.Native.CliScaffold
