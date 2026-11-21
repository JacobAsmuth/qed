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
  let scratch ← makeTempDir "qed-scaffold-test"
  let appDir := s!"{scratch}/app"
  let cleanEnv : Array (String × Option String) := #[
    ("QED_HOME", some root.toString),
    ("QED_WEB_ROOT", none),
    ("QED_JS_ROOT", none),
    ("QED_SKIP_VERIFY", none),
    ("LEAN_PATH", none),
    ("QED_PREBUILT", none),
    ("QED_OUT_DIR", none)
  ]
  try
    -- 1. `qed new` scaffolding
    let (cNew, outNew, errNew) ← runCmd cli #["new", appDir] (cwd := some root) (env := cleanEnv)
    c.check "qed new succeeds" (cNew == 0) (outNew ++ errNew)
    let tcApp ← IO.FS.readFile (FilePath.mk appDir / "lean-toolchain")
    let tcRoot ← IO.FS.readFile (root / "lean-toolchain")
    c.checkEq "lean-toolchain matches repo" tcApp tcRoot

    -- Point `lakefile.lean` at local repo
    let lfPath := FilePath.mk appDir / "lakefile.lean"
    let lfSrc ← IO.FS.readFile lfPath
    IO.FS.writeFile lfPath (lfSrc.replace
      "from git \"https://github.com/JacobAsmuth/qed\" @ \"main\""
      s!"from \"{root.toString}\"")

    -- 2. Full verified production build (`qed build`) -> hashed JS assets + native SSR `dist/server`
    let (cBld, outBld, errBld) ← runCmd cli #["build"] (cwd := some (FilePath.mk appDir)) (env := cleanEnv)
    c.check "qed build succeeds" (cBld == 0) (outBld ++ errBld)

    let distDir := FilePath.mk appDir / "dist"
    let manifestRaw ← IO.FS.readFile (distDir / "qed_manifest.json")
    let manifestJson := match Qed.Json.parse manifestRaw with | .ok j => j | .error _ => .null
    let hostPath := ((manifestJson.get? "host").bind (·.str?)).getD ""
    let appPath  := ((manifestJson.get? "app").bind (·.str?)).getD ""
    let rtPath   := ((manifestJson.get? "rt").bind (·.str?)).getD ""
    let domPath  := ((manifestJson.get? "dom").bind (·.str?)).getD ""
    c.check "manifest host hashed" (isHashedMjs "qed_host" hostPath) hostPath
    c.check "manifest app hashed" (isHashedMjs "app" appPath) appPath
    c.check "manifest rt hashed" (isHashedMjs "qed_rt" rtPath) rtPath
    c.check "manifest dom hashed" (isHashedMjs "qed_dom" domPath) domPath
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

    let (srv, healthy) ← startNativeServer distDir.toString #[] (dev := false)
    try
      c.check "standalone native server healthy" healthy
      match ← httpReq srv.port "GET" "/" with
      | .ok r =>
          c.checkEq "SSR GET / returns 200" r.status 200
          let html := r.bodyStr
          c.check "SSR HTML renders initial quantity 1" (html.contains "<span>1</span>") html
          c.check "SSR HTML references hashed host script" (html.contains hostPath) html
      | .error e => c.check "SSR GET / succeeded" false e

      match ← httpReq srv.port "GET" appPath with
      | .ok r =>
          c.checkEq "hashed asset returns 200" r.status 200
          c.checkEq "hashed asset immutable cache-control"
            (r.header? "cache-control") (some "public, max-age=31536000, immutable")
          c.checkEq "hashed asset nosniff" (r.header? "x-content-type-options") (some "nosniff")
      | .error e => c.check "GET hashed asset succeeded" false e

      let checkNoLeak (label reqPath : String) : IO Unit := do
        let raw := s!"GET {reqPath} HTTP/1.1\r\nHost: 127.0.0.1:{srv.port}\r\nConnection: close\r\n\r\n".toUTF8
        match ← rawTcpReq srv.port raw with
        | .ok resp =>
            let s := (String.fromUTF8? resp).getD ""
            c.check label (!s.contains "TOP_SECRET_SIBLING") s
        | .error e => c.check label false e
      checkNoLeak "blocks /../dist-secret/leak.txt" "/../dist-secret/leak.txt"
      checkNoLeak "blocks /%2e%2e%2fdist-secret/leak.txt" "/%2e%2e%2fdist-secret/leak.txt"
      checkNoLeak "blocks symlink /escape.txt" "/escape.txt"
    finally
      srv.stop

    -- 4. Native `qed serve <dir> <port> --dev` static server + `/__dev_status` JSON endpoint
    let staticPort ← Prim.freePort
    let (stSrv, stOk) ← startNativeBin cli #["serve", distDir.toString, toString staticPort, "--dev"] staticPort cleanEnv
    try
      c.check "qed serve native static server healthy" stOk
      match ← httpReq staticPort "GET" appPath with
      | .ok r =>
          c.checkEq "qed serve serves hashed asset 200" r.status 200
      | .error e => c.check "qed serve GET hashed asset" false e
      match ← httpReq staticPort "GET" "/__dev_status" with
      | .ok r =>
          c.checkEq "dev mode /__dev_status returns 200" r.status 200
          c.check "dev mode /__dev_status returns valid JSON status" (r.bodyStr.contains "\"status\":\"ok\"") r.bodyStr
      | .error e => c.check "qed serve GET /__dev_status" false e
    finally
      stSrv.stop

    -- 5. `--min` identifier shortening, Source Map v3 VLQ & `.mjs.map` (dev & prod)
    c.checkEq "VLQ encode 0" (Js.encodeVlqInt 0) "A"
    c.checkEq "VLQ encode 1" (Js.encodeVlqInt 1) "C"
    c.checkEq "VLQ encode -1" (Js.encodeVlqInt (-1)) "D"
    c.checkEq "VLQ encode 16" (Js.encodeVlqInt 16) "gB"
    c.checkEq "VLQ encode -16" (Js.encodeVlqInt (-16)) "hB"
    c.checkEq "VLQ encode 123" (Js.encodeVlqInt 123) "2H"
    let vlqSamples : List Int := [0, 1, -1, 15, -15, 16, -16, 123, -123, 1024, -1024, 99999, -99999]
    let vlqAllRt := vlqSamples.all fun v => Js.decodeVlqInt (Js.encodeVlqInt v) == some v
    c.check "VLQ encode/decode round-trip on all samples" vlqAllRt

    -- Base-52/62 short identifier hygiene & uniqueness
    let (idList, idsClean) := Id.run do
      let mut seen : Std.HashSet String := {}
      let mut idx := 0
      let mut ok := true
      for _ in [0:400] do
        let (nm, nextIdx) := Js.nextShortIdent Js.jsMinReservedSet idx
        if seen.contains nm || Js.jsMinReservedSet.contains nm || nm.startsWith "$" || nm.startsWith "_" then
          ok := false
        seen := seen.insert nm
        idx := nextIdx
      return (seen.size, ok)
    c.check "400 generated short identifiers are unique and skip reserved words/$" (idList == 400 && idsClean)

    -- Dev build emits `app.mjs` + `app.mjs.map` + `//# sourceMappingURL=app.mjs.map` + `qed_dev.mjs`
    let (cDev, outDev, errDev) ← runCmd cli #["build", "--dev", "--no-verify"]
      (cwd := some (FilePath.mk appDir)) (env := cleanEnv)
    c.check "qed build --dev succeeds" (cDev == 0) (outDev ++ errDev)
    let devOut := FilePath.mk appDir / ".qed" / "dev"
    let devAppJs ← IO.FS.readFile (devOut / "app.mjs")
    let devMapPath := devOut / "app.mjs.map"
    c.check "dev app.mjs references sourceMappingURL" (devAppJs.contains "//# sourceMappingURL=app.mjs.map")
    c.check "dev app.mjs.map exists" (← devMapPath.pathExists)
    c.check "dev qed_dev.mjs emitted" (← (devOut / "qed_dev.mjs").pathExists)
    let devMapRaw ← IO.FS.readFile devMapPath
    match Qed.Json.parse devMapRaw with
    | .ok sm =>
        c.checkEq "dev sourcemap version == 3" (((sm.get? "version").bind (·.num?)).bind (·.toInt?)) (some 3)
        c.checkEq "dev sourcemap file == app.mjs" ((sm.get? "file").bind (·.str?)) (some "app.mjs")
        let hasSources := match sm.get? "sources" with
          | some (.arr xs) => !xs.isEmpty && xs.any (fun x => x.str? == some "App.lean")
          | _ => false
        let hasNames := match sm.get? "names" with | some (.arr xs) => !xs.isEmpty | _ => false
        let hasMappings := match (sm.get? "mappings").bind (·.str?) with
          | some m => !m.isEmpty && m.contains ";"
          | none => false
        c.check "dev sourcemap lists App.lean in sources" hasSources devMapRaw
        c.check "dev sourcemap has non-empty names" hasNames
        c.check "dev sourcemap has non-empty VLQ mappings" hasMappings
    | .error e => c.check "dev sourcemap valid JSON" false e

    -- Minified prod `appJs` (from step 2) is significantly smaller and strips `_g0` / block comments
    c.check "minified prod app.mjs is >25% smaller than dev app.mjs" (appJs.length * 4 < devAppJs.length * 3)
      s!"prod={appJs.length} dev={devAppJs.length}"
    c.check "minified prod app.mjs removes _g0 internal prefix" (!appJs.contains "function _g0(" && !appJs.contains "const _g0 ")
    c.check "minified prod app.mjs strips /* comments */" (!appJs.contains "/* ")
    c.check "minified prod app.mjs preserves $ runtime calls" (appJs.contains "$.")

    -- Prod build with `--sourcemap` emits hashed `app.<hash>.mjs.map` matching `app.<hash>.mjs`
    let (cProdMap, outProdMap, errProdMap) ← runCmd cli #["build", "--sourcemap"]
      (cwd := some (FilePath.mk appDir)) (env := cleanEnv)
    c.check "qed build --sourcemap succeeds" (cProdMap == 0) (outProdMap ++ errProdMap)
    let manifestRaw2 ← IO.FS.readFile (distDir / "qed_manifest.json")
    let manifestJson2 := match Qed.Json.parse manifestRaw2 with | .ok j => j | .error _ => .null
    let appPath2 := ((manifestJson2.get? "app").bind (·.str?)).getD ""
    let appName2 := String.ofList (appPath2.toList.drop 1)
    let prodJs2 ← IO.FS.readFile (distDir / appName2)
    let prodMap2Path := distDir / s!"{appName2}.map"
    c.check "prod --sourcemap appends hashed sourceMappingURL" (prodJs2.contains s!"//# sourceMappingURL={appName2}.map")
    c.check "prod --sourcemap emits hashed .mjs.map" (← prodMap2Path.pathExists)
    if ← prodMap2Path.pathExists then
      match Qed.Json.parse (← IO.FS.readFile prodMap2Path) with
      | .ok sm =>
          c.checkEq "prod sourcemap version == 3" (((sm.get? "version").bind (·.num?)).bind (·.toInt?)) (some 3)
          c.checkEq "prod sourcemap file matches hashed bundle" ((sm.get? "file").bind (·.str?)) (some appName2)
      | .error e => c.check "prod sourcemap valid JSON" false e

    -- 6. OS-native file watcher FFI (`Cli.Watch.FileWatcher`) + Dev SSE push server (`Cli.Watch.DevSseServer`)
    let watchRoot := FilePath.mk scratch / "watch_proj"
    let watchSkip := watchRoot / ".lake"
    let watchRt   := FilePath.mk scratch / "watch_rt"
    IO.FS.createDirAll watchSkip
    IO.FS.createDirAll watchRt
    IO.FS.writeFile (watchRoot / "Demo.lean") "def x := 1\n"
    IO.FS.writeFile (watchRoot / "site.css") "body{}\n"
    IO.FS.writeFile (watchRt / "qed_dev.mjs") "// v1\n"
    match ← FileWatcher.open watchRoot.toString watchRt.toString #[".lake", ".git"] with
    | .error e => c.check "OS file watcher opens cleanly" false e
    | .ok w =>
        try
          -- Ignored directory must not trigger watch events
          IO.FS.writeFile (watchSkip / "ignored.lean") "-- ignore\n"
          let evSkip ← w.wait 80
          c.check "OS watcher ignores skipped .lake/ directory" (!evSkip.any && !evSkip.error) (reprStr evSkip)

          -- Modifying a .lean file triggers `ev.lean`
          let tLean ← IO.asTask (w.wait 1500)
          IO.sleep 30
          IO.FS.writeFile (watchRoot / "Demo.lean") "def x := 2\n"
          let evLean := (← IO.wait tLean).toOption.getD { lean := false, css := false, runtime := false, error := true }
          c.check "OS watcher detects .lean modification" (evLean.lean && !evLean.error) (reprStr evLean)

          -- Modifying a .css file triggers `ev.css`
          let tCss ← IO.asTask (w.wait 1500)
          IO.sleep 30
          IO.FS.writeFile (watchRoot / "site.css") "body{color:red}\n"
          let evCss := (← IO.wait tCss).toOption.getD { lean := false, css := false, runtime := false, error := true }
          c.check "OS watcher detects .css modification" (evCss.css && !evCss.error) (reprStr evCss)

          -- Modifying a runtime .mjs file triggers `ev.runtime`
          let tRt ← IO.asTask (w.wait 1500)
          IO.sleep 30
          IO.FS.writeFile (watchRt / "qed_dev.mjs") "// v2\n"
          let evRt := (← IO.wait tRt).toOption.getD { lean := false, css := false, runtime := false, error := true }
          c.check "OS watcher detects runtime .mjs modification" (evRt.runtime && !evRt.error) (reprStr evRt)
        finally
          w.close

    match ← DevSseServer.start 0 with
    | .error e => c.check "DevSseServer starts on ephemeral port" false e
    | .ok sse =>
        try
          c.check "DevSseServer bound ephemeral port > 0" (sse.port > 0)
          sse.publish "{\"id\":\"42\",\"status\":\"ok\",\"kind\":\"hmr\",\"durationMs\":9,\"error\":\"\"}"
          match ← Prim.outboundAcquire 0 "127.0.0.1" sse.port 0 (fun _ => false) with
          | .error e => c.check "TCP connect to DevSseServer" false e
          | .ok (hNat, _) =>
              let h := hNat.toUInt64
              let req := s!"GET /events HTTP/1.1\r\nHost: 127.0.0.1:{sse.port}\r\nAccept: text/event-stream\r\n\r\n".toUTF8
              let okW ← match ← Prim.outboundWriteAll h req with | .ok () => pure true | .error _ => pure false
              let body ← if okW then
                  match ← Prim.outboundReadSome h 4096 with
                  | .ok bs => pure ((String.fromUTF8? bs).getD "")
                  | .error _ => pure ""
                else pure ""
              -- Also verify live push on an already-open SSE connection
              IO.sleep 30
              sse.publish "{\"id\":\"43\",\"status\":\"building\",\"kind\":\"hmr\",\"durationMs\":0,\"error\":\"\"}"
              let pushed ← if okW then
                  match ← Prim.outboundReadSome h 4096 with
                  | .ok bs => pure ((String.fromUTF8? bs).getD "")
                  | .error _ => pure ""
                else pure ""
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
    IO.FS.writeFile appLean withBenign
    let (cBenign, outBenign, errBenign) ← runCmd cli #["check"] (cwd := some (FilePath.mk appDir)) (env := cleanEnv)
    c.check "benign comments/strings/client helpers pass qed check" (cBenign == 0) (outBenign ++ errBenign)

    IO.FS.writeFile appLean (validSrc ++ "\ndef badInterp : String := s!\"{(by sorry : Nat)}\" -- never emit\n")
    let (cSorry, outSorry, errSorry) ← runCmd cli #["check"] (cwd := some (FilePath.mk appDir)) (env := cleanEnv)
    c.check "real sorry inside interpolated string rejected"
      (cSorry != 0 && (outSorry ++ errSorry).contains "forbidden token `sorry`") (outSorry ++ errSorry)

    IO.FS.writeFile appLean (validSrc ++ "\npartial def spin (n : Nat) : Nat := spin n\n")
    let (cPart, outPart, errPart) ← runCmd cli #["check"] (cwd := some (FilePath.mk appDir)) (env := cleanEnv)
    c.check "partial def rejected by kernel gate"
      (cPart != 0 && (outPart ++ errPart).contains "kernel gate: `partial` or `opaque` declaration `spin`")
      (outPart ++ errPart)
  finally
    rmRf scratch
  c.finish

end Tests.Native.CliScaffold
