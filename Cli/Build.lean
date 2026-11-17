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
    let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
    for f in files do
      let p := outDir / f
      if (← p.pathExists) then
        let t ← IO.asTask do
          let minP := s!"{p}.min"
          if (← sh "esbuild" #[p.toString, "--minify", "--format=esm", s!"--outfile={minP}"]) == 0 then
            IO.FS.rename minP p
        tasks := tasks.push t
    for t in tasks do
      discard <| IO.wait t

private def resolveServeCmd (dir : FilePath) (port : String) (dev : Bool) :
    IO (String × Array String × Bool) := do
  let devArg := if dev then #["--dev"] else #[]
  if (← (dir / "server").pathExists) then
    return ((dir / "server").toString, #[dir.toString, port] ++ devArg, true)
  else if (← (dir / "ssr.mjs").pathExists) && (← onPath "node") then
    return ("node", #[(← runtimeFile "qed_serve.mjs").toString, dir.toString, port] ++ devArg, false)
  else
    return ("python3", #["-m", "http.server", port, "--directory", dir.toString], false)

initialize fullstackLinkCache :
    IO.Ref (Option (Array String × Array String × String × String)) ← IO.mkRef none

private def resolveLinkMeta (cObjTargets : Array String) :
    IO (Option (Array String × String × String)) := do
  if let some (cachedTargets, cachedInputs, ssl, crypto) ← fullstackLinkCache.get then
    if cachedTargets == cObjTargets then
      let mut ok := true
      for p in cachedInputs do
        if !(← (FilePath.mk p).pathExists) then ok := false; break
      if ok then return some (cachedInputs, ssl, crypto)
  let tSsl ← IO.asTask (resolveSharedLibArg "libssl.so" "-lssl")
  let tCrypto ← IO.asTask (resolveSharedLibArg "libcrypto.so" "-lcrypto")
  let some linkInputs ← lakeQueryPaths cObjTargets | return none
  let sslLib := (← IO.wait tSsl).toOption.getD "-lssl"
  let cryptoLib := (← IO.wait tCrypto).toOption.getD "-lcrypto"
  fullstackLinkCache.set (some (cObjTargets, linkInputs, sslLib, cryptoLib))
  return some (linkInputs, sslLib, cryptoLib)

def buildFullstack (mod fsName : String) (outDir : FilePath) (prod : Bool)
    (alreadyBuilt : Bool := false) : IO Bool := do
  let localMods ← collectLocalModules mod
  let cObjTargets := (localMods.map fun m => s!"+{m}:c.o") ++ #["qed/QedServer:static", "qed/Qed:static"]
  let isInRepo ← (FilePath.mk "Examples").pathExists
  let prebuilt := (← env "QED_PREBUILT") == some "1"
  let lakeTargets :=
    (if alreadyBuilt || prebuilt then #[] else #[mod]) ++
    #["Qed.Driver"] ++
    (if isInRepo && !prebuilt then #["qedjs"] else #[]) ++
    cObjTargets
  if (← sh "lake" (#["build"] ++ lakeTargets)) != 0 then
    return false
  let some q ← resolveQedjsEnv (needBuild := !isInRepo && !prebuilt) | return false
  let rtPath ← runtimeFile "qed_rt.mjs"
  let genDir : FilePath := ".qed" / "gen" / mod
  IO.FS.createDirAll genDir
  IO.FS.createDirAll outDir

  let modOlean := FilePath.mk ".lake" / "build" / "lib" / "lean" / ((mod.replace "." "/") ++ ".olean")
  let fwRoot ← if isInRepo then pure (FilePath.mk ".") else frameworkHome
  let drvOlean := fwRoot / ".lake" / "build" / "lib" / "lean" / "Qed" / "Driver.olean"
  let cliLean := genDir / "ClientMain.lean"
  let cliOlean := genDir / "ClientMain.olean"
  let cliChanged ← writeIfChanged cliLean s!"import {mod}\nimport Qed.Driver\n\ndef main : IO Unit := Qed.run {fsName}.clientApp\n"
  let srvLean := genDir / "ServerMain.lean"
  let srvC := genDir / "ServerMain.c"
  let srvChanged ← writeIfChanged srvLean s!"import {mod}\nimport Qed.Server.Native\n\nqedServerMain {fsName}\n"

  let mut cliDeps : Array FilePath := #[cliLean, modOlean]
  if ← drvOlean.pathExists then cliDeps := cliDeps.push drvOlean
  let appMjs := outDir / "app.mjs"
  let srvBin := outDir / "server"

  -- 1. Synthesize & compile client entrypoint → `app.mjs` (enforcing `verifyNoServerLeakInClient`)
  let tClient ← IO.asTask do
    if cliChanged || prod || !(← isUpToDate cliOlean cliDeps) then
      if (← sh "lake" #["env", "lean", "-R", genDir.toString, cliLean.toString, "-o", cliOlean.toString]) != 0 then
        return false
    if prod || !(← isUpToDate appMjs #[cliOlean, q.bin, rtPath, modOlean]) then
      let minArgs := if prod then #["--min"] else #[]
      let rtArgs := #["--rt", rtPath.toString]
      if !(← q.run (minArgs ++ rtArgs ++ #[appMjs.toString, "ClientMain", "--"] ++ driverEntries) (extraPath := some genDir.toString)) then
        return false
    writeClientShell outDir prod
    for stale in ["ssr.mjs", "ssr_app.mjs", "qed_ssr_host.mjs"] do
      removeIfExists (outDir / stale)
    if prod then minifyBundles outDir ["app.mjs", "qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"]
    return true

  -- 2. Synthesize & compile native multi-core C/Lean server binary → `<outDir>/server`
  let tServer ← IO.asTask do
    let some (linkInputs, sslLib, cryptoLib) ← resolveLinkMeta cObjTargets | return false
    let linkFiles := linkInputs.map FilePath.mk
    let srvCDeps := #[srvLean, modOlean] ++ linkFiles
    if srvChanged || prod || !(← isUpToDate srvC srvCDeps) then
      if (← sh "lake" #["env", "lean", "-R", genDir.toString, srvLean.toString, "-c", srvC.toString]) != 0 then
        return false
    let linkDeps := #[srvC] ++ linkFiles
    if prod || !(← isUpToDate srvBin linkDeps) then
      let srvTmp := outDir / "server.tmp"
      let optFlags := if prod then #["-O3", "-DNDEBUG"] else #["-O0"]
      let leancArgs := #["env", "leanc"] ++ optFlags ++ #[srvC.toString] ++
        linkInputs ++ #["-pthread", sslLib, cryptoLib, "-Wl,--allow-shlib-undefined", "-o", srvTmp.toString]
      if (← sh "lake" leancArgs) != 0 then return false
      IO.FS.rename srvTmp srvBin
    return true

  let cliOk := (← IO.wait tClient).toOption.getD false
  let srvOk := (← IO.wait tServer).toOption.getD false
  return cliOk && srvOk

def buildJs (outDir : FilePath) (prod : Bool) (alreadyBuilt : Bool := false) : IO Bool := do
  let mod ← jsRoot
  if let some fsName ← fullstackAppName mod then
    return ← buildFullstack mod fsName outDir prod alreadyBuilt
  let isInRepo ← (FilePath.mk "Examples").pathExists
  let prebuilt := (← env "QED_PREBUILT") == some "1"
  if !prebuilt && !alreadyBuilt then
    let targets := if isInRepo then #[mod, "qedjs"] else #[mod]
    if (← sh "lake" (#["build"] ++ targets)) != 0 then return false
  let some q ← resolveQedjsEnv (needBuild := !isInRepo && !prebuilt) | return false
  IO.FS.createDirAll outDir
  removeIfExists (outDir / "server")
  let rtPath ← runtimeFile "qed_rt.mjs"
  let minArgs := if prod then #["--min"] else #[]
  let rtArgs := #["--rt", rtPath.toString]
  let ssrOpt ← ssrAppName mod
  let alsoArgs : Array String := match ssrOpt with
    | some appName => #["--also", (outDir / "ssr_app.mjs").toString, "--", s!"{appName}:app", "Qed.App.ssrStep:ssrStep"]
    | none => #[]
  if !(← q.run (minArgs ++ rtArgs ++ #[(outDir / "app.mjs").toString, mod, "--"] ++ driverEntries ++ alsoArgs)) then
    return false
  writeClientShell outDir prod
  match ssrOpt with
  | some appName =>
      IO.FS.writeFile (outDir / "qed_ssr_host.mjs") (← IO.FS.readFile (← runtimeFile "qed_ssr_host.mjs"))
      let cacheKey ← if prod then pure "" else toString <$> IO.monoMsNow
      IO.FS.writeFile (outDir / "ssr.mjs") (ssrWrapper appName cacheKey)
  | none =>
      IO.println s!"  note: no `Qed.run <app>` found in {mod}, skipping the SSR handler (ssr.mjs)"
  if prod then
    minifyBundles outDir ["app.mjs", "qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs", "ssr_app.mjs", "qed_ssr_host.mjs"]
  return true

def cmdBuild (prod : Bool) (skipVerify : Bool := false) : IO UInt32 := do
  let skip := !prod && (skipVerify || (← env "QED_SKIP_VERIFY") == some "1")
  if !skip then
    if !(← verify (checkExterns := false)) then IO.eprintln (red "✗ verification failed"); return 1
  let outOverride ← if prod then pure none else env "QED_OUT_DIR"
  let outDir := match outOverride with
    | some d => FilePath.mk d
    | none   => if prod then distDir else devDir
  if outOverride.isNone then step s!"compiling Lean → {outDir}/"
  if !(← buildJs outDir prod (alreadyBuilt := !skip)) then IO.eprintln (red "✗ build failed"); return 1
  if outOverride.isNone then
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
  let leanFind := s!"find . -name '*.lean' -newer {marker} -not -path './.lake/*' -not -path './.qed/*' 2>/dev/null | head -1"
  let rtFind := s!"find {qh}/runtime -newer {marker} 2>/dev/null | head -1"
  let (_, leanOut) ← shOut "bash" #["-c", leanFind]
  let (_, rtOut) ← if leanOut.trimmed.isEmpty then shOut "bash" #["-c", rtFind] else pure (0, "")
  let mut nextSrv := curServer
  let mut nextNative := isNative
  if !leanOut.trimmed.isEmpty then
    let _ ← sh "touch" #[marker.toString]
    step "change detected, rebuilding"
    let prevSrvMtime ← mtimeNs (devDir / "server")
    if (← buildJs devDir (prod := false)) then
      let nowNative ← (devDir / "server").pathExists
      let newSrvMtime ← mtimeNs (devDir / "server")
      if (nextNative != nowNative) || (nowNative && prevSrvMtime != newSrvMtime) then
        curServer.kill
        discard <| curServer.wait
        let (restarted, nat) ← spawnDevChild port
        nextSrv := restarted
        nextNative := nat
      writeBuildId devDir
      if (← (FilePath.mk "Examples").pathExists) then
        let _ ← effectsCovered
      IO.println (green "✓ reloaded")
    else
      IO.eprintln (red "✗ build failed, fix and save again")
  else if !rtOut.trimmed.isEmpty then
    let _ ← sh "touch" #[marker.toString]
    step "runtime change detected, reloading"
    writeClientShell devDir (prod := false)
    if (← (devDir / "qed_ssr_host.mjs").pathExists) then
      IO.FS.writeFile (devDir / "qed_ssr_host.mjs") (← IO.FS.readFile (← runtimeFile "qed_ssr_host.mjs"))
    writeBuildId devDir
    IO.println (green "✓ reloaded (runtime)")
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
