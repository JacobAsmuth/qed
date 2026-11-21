import Tests.Native.Harness

open System (FilePath)
open Qed.Server

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

    -- 5. `--check-externs` catches stripped extern in `qed_rt.mjs`
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
