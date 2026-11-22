import Tests.Native.Harness
import Cli.Watch
import Js.Backend

open System (FilePath)
open Qed.Server
open Qed.Cli.Watch

namespace Tests.Native.CliScaffold

private def isHashedMjs (prefixStr s : String) : Bool :=
  s.startsWith s!"/{prefixStr}." && s.endsWith ".mjs" &&
    s.length == prefixStr.length + 1 + 1 + 12 + 4

def run : IO Bool := do
  let c ← mkChecker "cli-scaffold"
  let root ← IO.currentDir
  let cli ← qedBinPath
  let qedjs ← qedjsBinPath
  let cleanEnv : Array (String × Option String) := #[
    ("QED_HOME", some root.toString), ("QED_WEB_ROOT", none), ("QED_JS_ROOT", none),
    ("QED_SKIP_VERIFY", none), ("LEAN_PATH", none), ("QED_PREBUILT", none), ("QED_OUT_DIR", none)
  ]
  withTempDir "qed-scaffold-test" fun scratch => do
    let appDir := s!"{scratch}/app"
    -- 1. `qed new` scaffolding
    let (cNew, outNew, errNew) ← runCmd cli #["new", appDir] (cwd := some root) (env := cleanEnv)
    c.check "qed new succeeds" (cNew == 0) (outNew ++ errNew)
    c.checkEq "lean-toolchain matches repo" (← IO.FS.readFile (FilePath.mk appDir / "lean-toolchain")) (← IO.FS.readFile (root / "lean-toolchain"))

    -- Point `lakefile.lean` at local repo
    let lfPath := FilePath.mk appDir / "lakefile.lean"
    IO.FS.writeFile lfPath ((← IO.FS.readFile lfPath).replace
      "from git \"https://github.com/JacobAsmuth/qed\" @ \"main\"" s!"from \"{root.toString}\"")

    -- 2. Full verified production build (`qed build`) -> hashed JS assets + native SSR `dist/server`
    let (cBld, outBld, errBld) ← runCmd cli #["build"] (cwd := some (FilePath.mk appDir)) (env := cleanEnv)
    c.check "qed build succeeds" (cBld == 0) (outBld ++ errBld)

    let distDir := FilePath.mk appDir / "dist"
    let manifestRaw ← IO.FS.readFile (distDir / "qed_manifest.json")
    let hostPath := Qed.Json.pathStr manifestRaw "host"
    let appPath  := Qed.Json.pathStr manifestRaw "app"
    for (key, pfx, p) in [("host", "qed_host", hostPath), ("app", "app", appPath),
        ("rt", "qed_rt", Qed.Json.pathStr manifestRaw "rt"), ("dom", "qed_dom", Qed.Json.pathStr manifestRaw "dom")] do
      c.check s!"manifest {key} hashed" (isHashedMjs pfx p) p
    c.check "unhashed dist/app.mjs removed" (!(← (distDir / "app.mjs").pathExists))
    c.check "dev client qed_dev.mjs omitted from prod dist" (!(← (distDir / "qed_dev.mjs").pathExists))
    c.check "native dist/server binary built" (← (distDir / "server").pathExists)
    let appJs ← IO.FS.readFile (distDir / (String.ofList (appPath.toList.drop 1)))
    c.check "app bundle contains qed_init" (appJs.contains "qed_init")
    c.check "app bundle exports qed_dehydrate for HMR" (appJs.contains "qed_dehydrate")

    -- 3. Native standalone SSR + immutable asset headers + path traversal/symlink defense
    let secretDir := FilePath.mk appDir / "dist-secret"
    IO.FS.createDirAll secretDir
    IO.FS.writeFile (secretDir / "leak.txt") "TOP_SECRET_SIBLING"
    discard <| runCmd "ln" #["-s", (secretDir / "leak.txt").toString, (distDir / "escape.txt").toString]

    withNativeServer c "standalone native server healthy" distDir.toString #[] (dev := false) fun srv => do
      c.checkHttp "SSR GET /" (← httpReq srv.port "GET" "/") (contains := ["<span>1</span>", hostPath])
      c.checkHttp "GET hashed asset" (← httpReq srv.port "GET" appPath) (headers := [
        ("cache-control", some "public, max-age=31536000, immutable"),
        ("x-content-type-options", some "nosniff")
      ])
      let checkNoLeak (label reqPath : String) : IO Unit := do
        let raw := s!"GET {reqPath} HTTP/1.1\r\nHost: 127.0.0.1:{srv.port}\r\nConnection: close\r\n\r\n".toUTF8
        c.expectOk label (← rawTcpReq srv.port raw) fun resp =>
          let s := (String.fromUTF8? resp).getD ""
          c.check label (!s.contains "TOP_SECRET_SIBLING") s
      checkNoLeak "blocks /../dist-secret/leak.txt" "/../dist-secret/leak.txt"
      checkNoLeak "blocks /%2e%2e%2fdist-secret/leak.txt" "/%2e%2e%2fdist-secret/leak.txt"
      checkNoLeak "blocks symlink /escape.txt" "/escape.txt"

    -- 4. Native `qed serve <dir> <port> --dev` static server + `/__dev_status` JSON endpoint
    let staticPort ← Prim.freePort
    withNativeBin c "qed serve native static server healthy" cli #["serve", distDir.toString, toString staticPort, "--dev"] staticPort cleanEnv fun _ => do
      c.checkStatus "qed serve serves hashed asset 200" (← httpReq staticPort "GET" appPath) 200
      c.checkHttp "qed serve GET /__dev_status" (← httpReq staticPort "GET" "/__dev_status") (contains := ["\"status\":\"ok\""])

    -- 5. `--min` identifier shortening, Source Map v3 VLQ & `.mjs.map` (dev & prod)
    for (n, want) in [(0, "A"), (1, "C"), (-1, "D"), (16, "gB"), (-16, "hB"), (123, "2H")] do
      c.checkEq s!"VLQ encode {n}" (Js.encodeVlqInt n) want
    let vlqSamples : List Int := [0, 1, -1, 15, -15, 16, -16, 123, -123, 1024, -1024, 99999, -99999]
    c.check "VLQ encode/decode round-trip on all samples" (vlqSamples.all fun v => Js.decodeVlqInt (Js.encodeVlqInt v) == some v)

    -- Base-52/62 short identifier hygiene & uniqueness
    let (idList, idsClean) := Id.run do
      let mut seen : Std.HashSet String := {}
      let mut idx := 0
      let mut ok := true
      for _ in [0:400] do
        let (nm, nextIdx) := Js.nextShortIdent Js.jsMinReservedSet idx
        if seen.contains nm || Js.jsMinReservedSet.contains nm || nm.startsWith "$" || nm.startsWith "_" then ok := false
        seen := seen.insert nm; idx := nextIdx
      return (seen.size, ok)
    c.check "400 generated short identifiers are unique and skip reserved words/$" (idList == 400 && idsClean)

    -- Dev build emits `app.mjs` + `app.mjs.map` + `//# sourceMappingURL=app.mjs.map` + `qed_dev.mjs`
    let (cDev, outDev, errDev) ← runCmd cli #["build", "--dev", "--no-verify"] (cwd := some (FilePath.mk appDir)) (env := cleanEnv)
    c.check "qed build --dev succeeds" (cDev == 0) (outDev ++ errDev)
    let devOut := FilePath.mk appDir / ".qed" / "dev"
    let devAppJs ← IO.FS.readFile (devOut / "app.mjs")
    let devMapPath := devOut / "app.mjs.map"
    c.check "dev app.mjs references sourceMappingURL" (devAppJs.contains "//# sourceMappingURL=app.mjs.map")
    c.check "dev app.mjs.map exists" (← devMapPath.pathExists)
    c.check "dev qed_dev.mjs emitted" (← (devOut / "qed_dev.mjs").pathExists)
    let devMapRaw ← IO.FS.readFile devMapPath
    c.expectOk "dev sourcemap valid JSON" (Qed.Json.parse devMapRaw) fun sm => do
      c.checkJsonInt "dev sourcemap version == 3" sm "version" 3
      c.checkJsonStr "dev sourcemap file == app.mjs" sm "file" "app.mjs"
      c.checkJsonPath "dev sourcemap lists App.lean in sources" sm "sources" (detail := devMapRaw) fun
        | .arr xs => !xs.isEmpty && xs.any (·.str? == some "App.lean") | _ => false
      c.checkJsonPath "dev sourcemap has non-empty names" sm "names" fun | .arr xs => !xs.isEmpty | _ => false
      c.checkJsonPath "dev sourcemap has non-empty VLQ mappings" sm "mappings" fun
        | .str m => !m.isEmpty && m.contains ";" | _ => false

    -- Minified prod `appJs` (from step 2) is significantly smaller and strips `_g0` / block comments
    c.check "minified prod app.mjs is >25% smaller than dev app.mjs" (appJs.length * 4 < devAppJs.length * 3)
      s!"prod={appJs.length} dev={devAppJs.length}"
    c.check "minified prod app.mjs removes _g0 internal prefix" (!appJs.contains "function _g0(" && !appJs.contains "const _g0 ")
    c.check "minified prod app.mjs strips /* comments */" (!appJs.contains "/* ")
    c.check "minified prod app.mjs preserves $ runtime calls" (appJs.contains "$.")

    -- Prod build with `--sourcemap` emits hashed `app.<hash>.mjs.map` matching `app.<hash>.mjs`
    let (cProdMap, outProdMap, errProdMap) ← runCmd cli #["build", "--sourcemap"] (cwd := some (FilePath.mk appDir)) (env := cleanEnv)
    c.check "qed build --sourcemap succeeds" (cProdMap == 0) (outProdMap ++ errProdMap)
    let appName2 := String.ofList ((Qed.Json.pathStr (← IO.FS.readFile (distDir / "qed_manifest.json")) "app").toList.drop 1)
    let prodJs2 ← IO.FS.readFile (distDir / appName2)
    let prodMap2Path := distDir / s!"{appName2}.map"
    c.check "prod --sourcemap appends hashed sourceMappingURL" (prodJs2.contains s!"//# sourceMappingURL={appName2}.map")
    c.check "prod --sourcemap emits hashed .mjs.map" (← prodMap2Path.pathExists)
    if ← prodMap2Path.pathExists then
      c.expectOk "prod sourcemap valid JSON" (Qed.Json.parse (← IO.FS.readFile prodMap2Path)) fun sm => do
        c.checkJsonInt "prod sourcemap version == 3" sm "version" 3
        c.checkJsonStr "prod sourcemap file matches hashed bundle" sm "file" appName2

    -- 6. OS-native file watcher FFI (`Cli.Watch.FileWatcher`) + Dev SSE push server (`Cli.Watch.DevSseServer`)
    let watchRoot := FilePath.mk scratch / "watch_proj"
    let watchSkip := watchRoot / ".lake"
    let watchRt   := FilePath.mk scratch / "watch_rt"
    IO.FS.createDirAll watchSkip
    IO.FS.createDirAll watchRt
    IO.FS.writeFile (watchRoot / "Demo.lean") "def x := 1\n"
    IO.FS.writeFile (watchRoot / "site.css") "body{}\n"
    IO.FS.writeFile (watchRt / "qed_dev.mjs") "// v1\n"
    c.expectOk "OS file watcher opens cleanly" (← FileWatcher.open watchRoot.toString watchRt.toString #[".lake", ".git"]) fun w => do
      try
        -- Ignored directory must not trigger watch events
        IO.FS.writeFile (watchSkip / "ignored.lean") "-- ignore\n"
        let evSkip ← w.wait 80
        c.check "OS watcher ignores skipped .lake/ directory" (!evSkip.any && !evSkip.error) (reprStr evSkip)

        let waitWatchEdit (path : FilePath) (content : String) := do
          let t ← IO.asTask (w.wait 1500)
          IO.sleep 30
          IO.FS.writeFile path content
          return (← IO.wait t).toOption.getD { lean := false, css := false, runtime := false, error := true }

        for (label, path, content, proj) in [
            (".lean", watchRoot / "Demo.lean", "def x := 2\n", fun (e : WatchEvents) => e.lean),
            (".css", watchRoot / "site.css", "body{color:red}\n", fun e => e.css),
            ("runtime .mjs", watchRt / "qed_dev.mjs", "// v2\n", fun e => e.runtime)] do
          let ev ← waitWatchEdit path content
          c.check s!"OS watcher detects {label} modification" (proj ev && !ev.error) (reprStr ev)
      finally
        w.close

    c.expectOk "DevSseServer starts on ephemeral port" (← DevSseServer.start 0) fun sse => do
      try
        c.check "DevSseServer bound ephemeral port > 0" (sse.port > 0)
        sse.publish "{\"id\":\"42\",\"status\":\"ok\",\"kind\":\"hmr\",\"durationMs\":9,\"error\":\"\"}"
        c.expectOk "TCP connect to DevSseServer" (← Prim.outboundAcquire 0 "127.0.0.1" sse.port 0 (fun _ => false)) fun (hNat, _) => do
          let h := hNat.toUInt64
          let req := s!"GET /events HTTP/1.1\r\nHost: 127.0.0.1:{sse.port}\r\nAccept: text/event-stream\r\n\r\n".toUTF8
          let okW := (← Prim.outboundWriteAll h req).isOk
          let readStr : IO String := do
            if !okW then return ""
            return ((← Prim.outboundReadSome h 4096).toOption.bind String.fromUTF8?).getD ""
          let body ← readStr
          -- Also verify live push on an already-open SSE connection
          IO.sleep 30
          sse.publish "{\"id\":\"43\",\"status\":\"building\",\"kind\":\"hmr\",\"durationMs\":0,\"error\":\"\"}"
          let pushed ← readStr
          Prim.outboundRelease h 0
          c.check "DevSseServer returns 200 text/event-stream with CORS and initial event"
            (body.contains "200 OK" &&
             body.contains "text/event-stream" &&
             body.contains "Access-Control-Allow-Origin: *" &&
             body.contains "data: {\"id\":\"42\",\"status\":\"ok\"") body
          c.check "DevSseServer pushes live building event to connected client"
            (pushed.contains "data: {\"id\":\"43\",\"status\":\"building\"") pushed
      finally
        sse.stop

    -- 7. `--check-externs` catches stripped extern in `qed_rt.mjs`
    let strippedRt := s!"{scratch}/stripped_rt.mjs"
    let rtSrc ← IO.FS.readFile (root / "runtime" / "qed_rt.mjs")
    IO.FS.writeFile strippedRt (rtSrc.replace "export const Array_push" "export const Removed_Array_push")
    let (cExt, outExt, errExt) ← runCmd "lake"
      #["env", qedjs, "--check-externs", strippedRt, "App", "--", "Quantity.app:app"]
      (cwd := some (FilePath.mk appDir)) (env := cleanEnv)
    c.check "stripped qed_rt fails --check-externs" (cExt != 0 && (outExt ++ errExt).contains "Array_push")
      (outExt ++ errExt)

    -- 6. Lexical `grepForbidden` + client leak false-positive & true-positive checks
    let appLean := FilePath.mk appDir / "App.lean"
    let validSrc ← IO.FS.readFile appLean
    let withBenign := (validSrc.replace
      "<span>{quantity}</span>"
      "<span>{my_handler(my_step(quantity + initState - 1))}</span>\n      <small>{admitted_sorry_msg}</small>").replace
      "open Qed\n"
      ("open Qed\n\n-- comments mentioning sorry, admit, native_decide must be ignored\n" ++
       "/- nested /- block comment with sorry and admit -/ still comment -/\n" ++
       "def initState : Nat := 1\n" ++
       "def my_handler (n : Nat) : Nat := n\n" ++
       "def my_step (n : Nat) : Nat := n\n" ++
       "def admitted_sorry_msg : String := \"We are sorry, please admit this item\"\n")
    for (label, src, wantOk, wantSub) in [
        ("benign comments/strings/client helpers pass qed check", withBenign, true, ""),
        ("real sorry inside interpolated string rejected",
          validSrc ++ "\ndef badInterp : String := s!\"{(by sorry : Nat)}\" -- never emit\n", false, "forbidden token `sorry`"),
        ("partial def rejected by kernel gate",
          validSrc ++ "\npartial def spin (n : Nat) : Nat := spin n\n", false, "kernel gate: `partial` or `opaque` declaration `spin`")] do
      IO.FS.writeFile appLean src
      let (code, out, err) ← runCmd cli #["check"] (cwd := some (FilePath.mk appDir)) (env := cleanEnv)
      let combined := out ++ err
      c.check label ((code == 0) == wantOk && (wantSub.isEmpty || combined.contains wantSub)) combined
  c.finish

end Tests.Native.CliScaffold
