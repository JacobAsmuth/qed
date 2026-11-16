import Cli.Verify

open System (FilePath)

namespace Qed.Cli

def indexHtml (dev : Bool) : String :=
  let reload := if dev then
    "<script>(function(){let v=null;setInterval(async()=>{try{const t=await (await fetch('/__build_id',{cache:'no-store'})).text();if(v&&v!==t)location.reload();v=t;}catch(e){}},700)})()</script>\n"
  else ""
  "<!doctype html>\n<html lang=\"en\">\n<head><meta charset=\"utf-8\"><base href=\"/\">" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"><title>qed</title></head>\n" ++
  "<body><div id=\"app\">loading…</div>\n" ++ reload ++
  "<script type=\"module\" src=\"/qed_host.mjs\"></script>\n</body>\n</html>\n"

private def isFrameworkOrStdRoot (modName : String) : Bool :=
  let root := (modName.splitOn ".").headD modName
  root == "Init" || root == "Std" || root == "Lean" || root == "Lake" ||
  root == "Qed" || root == "Js" || root == "Cli"

private partial def collectLocalModulesLoop :
    List String → Array String → IO (Array String)
  | [], visited => return visited
  | m :: rest, visited => do
      if visited.contains m || isFrameworkOrStdRoot m then
        collectLocalModulesLoop rest visited
      else
        let path := FilePath.mk ((m.replace "." "/") ++ ".lean")
        if !(← path.pathExists) then
          collectLocalModulesLoop rest visited
        else
          let src ← IO.FS.readFile path
          let mut deps : List String := []
          for raw in src.splitOn "\n" do
            let code := (raw.splitOn "--").headD raw
            let toks := ((code.replace "\t" " ").splitOn " ").filter (· != "")
            let afterImp := match toks with
              | "import" :: ds => ds
              | "public" :: "import" :: ds => ds
              | _ => []
            for d in afterImp do
              let dm := takeIdentChars d
              if !dm.isEmpty && !isFrameworkOrStdRoot dm then
                deps := deps ++ [dm]
          collectLocalModulesLoop (rest ++ deps) (visited.push m)

private def collectLocalModules (rootMod : String) : IO (Array String) :=
  collectLocalModulesLoop [rootMod] #[]

private def lakeQueryPaths (targets : Array String) : IO (Option (Array String)) := do
  let o ← IO.Process.output { cmd := "lake", args := #["query"] ++ targets }
  if o.exitCode != 0 then
    IO.eprint (o.stdout ++ o.stderr)
    return none
  let paths := (o.stdout.splitOn "\n").toArray.map String.trimmed |>.filter (!·.isEmpty)
  return some paths

private def lakeEnvLeanPath : IO (Option String) := do
  let o ← IO.Process.output { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"] }
  if o.exitCode != 0 then
    IO.eprint (o.stdout ++ o.stderr)
    return none
  return some o.stdout.trimmed

private def resolveSharedLibArg (soname fallbackFlag : String) : IO String := do
  let o ← IO.Process.output { cmd := "cc", args := #[s!"-print-file-name={soname}"] }
  if o.exitCode == 0 then
    let p := o.stdout.trimmed
    if !p.isEmpty && p != soname && (← (FilePath.mk p).pathExists) then
      return p
  return fallbackFlag

private def removeIfExists (p : FilePath) : IO Unit := do
  if ← p.pathExists then
    try IO.FS.removeFile p catch _ => pure ()

def ssrWrapper (appName : String) (cacheKey : String := "") : String :=
  let title := (appName.splitOn ".").headD "qed"
  let appImport := "./ssr_app.mjs" ++ (if cacheKey.isEmpty then "" else s!"?build={cacheKey}")
  "import * as mod from '" ++ appImport ++ "';\n" ++
  "import * as rt from './qed_rt.mjs';\n" ++
  "import { makeHandler } from './qed_ssr_host.mjs';\n" ++
  "rt.assertExterns(mod.__externs, rt);\n" ++
  "export { makeHandler, mod };\n" ++
  "export default makeHandler(mod, { title: '" ++ title ++ "', script: '/qed_host.mjs' });\n"

private def writeClientShell (outDir : FilePath) (prod : Bool) : IO Unit := do
  for f in ["qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"] do
    IO.FS.writeFile (outDir / f) (← IO.FS.readFile (← runtimeFile f))
  IO.FS.writeFile (outDir / "index.html") (indexHtml (dev := !prod))

private def minifyBundles (outDir : FilePath) (files : List String) : IO Unit := do
  if (← onPath "esbuild") then
    for f in files do
      let p := outDir / f
      if (← p.pathExists) then
        discard <| sh "bash" #["-c", s!"esbuild {p} --minify --format=esm --outfile={p}.min && mv {p}.min {p}"]

private def verifyBuiltExterns (outDir : FilePath) (bundles : List String) : IO Bool := do
  unless (← onPath "node") do return true
  let existing ← bundles.filterM fun f => (outDir / FilePath.mk f).pathExists
  if existing.isEmpty then return true
  let script :=
    "import path from 'node:path'; import { pathToFileURL } from 'node:url';" ++
    "const rt = await import(pathToFileURL(path.resolve(process.argv[1])).href);" ++
    "for (const f of process.argv.slice(2)) {" ++
    "  const m = await import(pathToFileURL(path.resolve(f)).href);" ++
    "  rt.assertExterns(m.__externs, rt);" ++
    "}"
  let rtArg := (outDir / "qed_rt.mjs").toString
  let bundleArgs := existing.toArray.map fun f => (outDir / FilePath.mk f).toString
  return (← sh "node" (#["--input-type=module", "-e", script, rtArg] ++ bundleArgs)) == 0

private def resolveServeCmd (dir : FilePath) (port : String) (dev : Bool) :
    IO (String × Array String × Bool) := do
  let devArg := if dev then #["--dev"] else #[]
  if (← (dir / "server").pathExists) then
    return ((dir / "server").toString, #[dir.toString, port] ++ devArg, true)
  else if (← (dir / "ssr.mjs").pathExists) && (← onPath "node") then
    return ("node", #[(← runtimeFile "qed_serve.mjs").toString, dir.toString, port] ++ devArg, false)
  else
    return ("python3", #["-m", "http.server", port, "--directory", dir.toString], false)

def buildFullstack (mod fsName : String) (outDir : FilePath) (prod : Bool) : IO Bool := do
  if (← sh "lake" #["build", mod, "Qed.Driver", "qed/QedServer", "qed/qedjs"]) != 0 then
    return false
  let some qedjsPaths ← lakeQueryPaths #["qed/qedjs"] | return false
  let some qedjsBin := qedjsPaths[0]? | return false
  let some baseLp ← lakeEnvLeanPath | return false
  let rtPath ← runtimeFile "qed_rt.mjs"
  let genDir : FilePath := ".qed" / "gen"
  IO.FS.createDirAll genDir
  IO.FS.createDirAll outDir

  -- 1. Synthesize & compile client entrypoint → `app.mjs` (enforcing `verifyNoServerLeakInClient`)
  let cliLean := genDir / "ClientMain.lean"
  let cliOlean := genDir / "ClientMain.olean"
  IO.FS.writeFile cliLean s!"import {mod}\nimport Qed.Driver\n\ndef main : IO Unit := Qed.run {fsName}.clientApp\n"
  if (← sh "lake" #["env", "lean", "-R", genDir.toString, cliLean.toString, "-o", cliOlean.toString]) != 0 then
    return false
  let minArgs := if prod then #["--min"] else #[]
  let rtArgs := #["--rt", rtPath.toString]
  let lpEnv := #[("LEAN_PATH", some s!"{genDir}:{baseLp}")]
  if (← sh qedjsBin (minArgs ++ rtArgs ++ #[(outDir / "app.mjs").toString, "ClientMain", "--"] ++ driverEntries) lpEnv) != 0 then
    return false
  writeClientShell outDir prod
  for stale in ["ssr.mjs", "ssr_app.mjs", "qed_ssr_host.mjs"] do
    removeIfExists (outDir / stale)
  if prod then minifyBundles outDir ["app.mjs", "qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"]
  if !(← verifyBuiltExterns outDir ["app.mjs"]) then return false

  -- 2. Synthesize & compile native multi-core C/Lean server binary → `<outDir>/server`
  let srvLean := genDir / "ServerMain.lean"
  let srvC := genDir / "ServerMain.c"
  IO.FS.writeFile srvLean s!"import {mod}\nimport Qed.Server.Native\n\nqedServerMain {fsName}\n"
  if (← sh "lake" #["env", "lean", "-R", genDir.toString, srvLean.toString, "-c", srvC.toString]) != 0 then
    return false
  let localMods ← collectLocalModules mod
  let queryTargets := (localMods.map fun m => s!"+{m}:c.o") ++ #["qed/QedServer:static", "qed/Qed:static"]
  let some linkInputs ← lakeQueryPaths queryTargets | return false
  let sslLib ← resolveSharedLibArg "libssl.so" "-lssl"
  let cryptoLib ← resolveSharedLibArg "libcrypto.so" "-lcrypto"
  let srvTmp := outDir / "server.tmp"
  let leancArgs := #["env", "leanc", "-O3", "-DNDEBUG", srvC.toString] ++
    linkInputs ++ #["-pthread", sslLib, cryptoLib, "-Wl,--allow-shlib-undefined", "-o", srvTmp.toString]
  if (← sh "lake" leancArgs) != 0 then return false
  IO.FS.rename srvTmp (outDir / "server")
  return true

def buildJs (outDir : FilePath) (prod : Bool) : IO Bool := do
  let mod ← jsRoot
  if let some fsName ← fullstackAppName mod then
    return ← buildFullstack mod fsName outDir prod
  if (← sh "lake" #["build", mod, "qedjs"]) != 0 then return false
  IO.FS.createDirAll outDir
  removeIfExists (outDir / "server")
  let rtPath ← runtimeFile "qed_rt.mjs"
  let minArgs := if prod then #["--min"] else #[]
  let rtArgs := #["--rt", rtPath.toString]
  if (← sh "lake" (#["exe", "qedjs"] ++ minArgs ++ rtArgs ++ #[(outDir / "app.mjs").toString, mod, "--"] ++ driverEntries)) != 0 then
    return false
  writeClientShell outDir prod
  match ← ssrAppName mod with
  | some appName =>
      let ssrOut := (outDir / "ssr_app.mjs").toString
      if (← sh "lake" (#["exe", "qedjs"] ++ minArgs ++ rtArgs ++ #[ssrOut, mod, "--", s!"{appName}:app", "Qed.App.ssrStep:ssrStep"])) != 0 then
        return false
      IO.FS.writeFile (outDir / "qed_ssr_host.mjs") (← IO.FS.readFile (← runtimeFile "qed_ssr_host.mjs"))
      let cacheKey ← if prod then pure "" else toString <$> IO.monoMsNow
      IO.FS.writeFile (outDir / "ssr.mjs") (ssrWrapper appName cacheKey)
  | none =>
      IO.println s!"  note: no `Qed.run <app>` found in {mod}, skipping the SSR handler (ssr.mjs)"
  if prod then
    minifyBundles outDir ["app.mjs", "qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs", "ssr_app.mjs", "qed_ssr_host.mjs"]
  if !(← verifyBuiltExterns outDir ["app.mjs", "ssr_app.mjs"]) then return false
  return true

def cmdBuild (prod : Bool) (skipVerify : Bool := false) : IO UInt32 := do
  let skip := !prod && (skipVerify || (← env "QED_SKIP_VERIFY") == some "1")
  if !skip then
    if !(← verify) then IO.eprintln (red "✗ verification failed"); return 1
  let outDir := if prod then distDir else devDir
  step s!"compiling Lean → {outDir}/"
  if !(← buildJs outDir prod) then IO.eprintln (red "✗ build failed"); return 1
  let (_, sz) ← shOut "bash" #["-c",
    s!"cat {outDir}/app.mjs {outDir}/qed_rt.mjs {outDir}/qed_dom.mjs {outDir}/qed_host.mjs | gzip -c | wc -c"]
  let srvNote := if (← (outDir / "server").pathExists) then s!" + native binary {outDir}/server" else ""
  IO.println (green s!"✓ build complete → {outDir}{srvNote}, {sz.trimmed} bytes gzipped to the client")
  return 0

def serveDir (dir : FilePath) (dev : Bool := false) : IO UInt32 := do
  let port := (← env "PORT").getD devPort
  let (cmd, args, _) ← resolveServeCmd dir port dev
  if cmd == "python3" then IO.println s!"serving {dir} → http://localhost:{port}"
  sh cmd args

def cmdStart : IO UInt32 := do
  if !(← (distDir / "app.mjs").pathExists) then
    IO.eprintln (red "no production build found, run `qed build` first"); return 1
  serveDir distDir

def cmdClean : IO UInt32 := do
  let _ ← sh "lake" #["clean"]
  let _ ← sh "rm" #["-rf", distDir.toString, (FilePath.mk ".qed").toString]
  IO.println (green "✓ cleaned")
  return 0

private def spawnDevChild (port : String) :
    IO (IO.Process.Child ⟨.null, .null, .inherit⟩ × Bool) := do
  let (cmd, args, isNative) ← resolveServeCmd devDir port true
  let c ← IO.Process.spawn { cmd, args, stdin := .null, stdout := .null, stderr := .inherit }
  return (c, isNative)

partial def watchLoop (marker : FilePath) (port : String)
    (curServer : IO.Process.Child ⟨.null, .null, .inherit⟩) (isNative : Bool) : IO Unit := do
  IO.sleep 400
  let qh ← frameworkHome
  let find := s!"find . -name '*.lean' -newer {marker} -not -path './.lake/*' -not -path './.qed/*' 2>/dev/null | head -1; " ++
              s!"find {qh}/runtime -newer {marker} 2>/dev/null | head -1"
  let (_, out) ← shOut "bash" #["-c", find]
  let mut nextSrv := curServer
  let mut nextNative := isNative
  if out.trimmed != "" then
    let _ ← sh "touch" #[marker.toString]
    step "change detected, rebuilding"
    if (← buildJs devDir (prod := false)) then
      let nowNative ← (devDir / "server").pathExists
      if nextNative || nowNative then
        curServer.kill
        discard <| curServer.wait
        let (restarted, nat) ← spawnDevChild port
        nextSrv := restarted
        nextNative := nat
      writeBuildId devDir
      let _ ← effectsCovered
      IO.println (green "✓ reloaded")
    else
      IO.eprintln (red "✗ build failed, fix and save again")
  watchLoop marker port nextSrv nextNative

def cmdDev : IO UInt32 := do
  IO.FS.createDirAll devDir
  let marker := devDir / ".watch"
  let _ ← sh "touch" #[marker.toString]
  step "initial build"
  unless (← buildJs devDir (prod := false)) do
    IO.eprintln (red "initial build failed, fix the error and save; dev will rebuild")
  writeBuildId devDir
  let port := (← env "PORT").getD devPort
  let ssr := (← (devDir / "ssr.mjs").pathExists) && (← onPath "node")
  let (serverChild, isNative) ← spawnDevChild port
  let modeTag := if isNative then "   (Full-Stack Native + SSR)" else if ssr then "   (SSR)" else ""
  IO.println (green s!"\nqed dev → http://localhost:{port}{modeTag}   (watching; Ctrl-C to stop)\n")
  watchLoop marker port serverChild isNative
  return 0

end Qed.Cli
