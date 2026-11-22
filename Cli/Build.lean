import Cli.Verify
import Cli.Watch
import Cli.DevAuth
import Qed.Server.Native
import Qed.Deploy

open System (FilePath)

namespace Qed.Cli

def indexHtml (dev : Bool) (hasStylesCss : Bool := false) (stylesheets : List String := [])
    (hostScript : String := "/qed_host.mjs") (stylesHref : String := "/styles.css")
    (sseUrl : String := "") : String :=
  let reload := if dev then
    "<script type=\"module\" src=\"/qed_dev.mjs\"></script>\n"
  else ""
  let sseMeta := if dev && !sseUrl.isEmpty then
    s!"<meta name=\"qed-dev-sse\" content=\"{sseUrl}\">"
  else ""
  let extLinks := String.join (stylesheets.map fun href =>
    s!"<link rel=\"stylesheet\" href=\"{href}\">")
  let styleLink := if hasStylesCss then s!"<link rel=\"stylesheet\" data-qed-styles href=\"{stylesHref}\">" else ""
  "<!doctype html>\n<html lang=\"en\">\n<head><meta charset=\"utf-8\"><base href=\"/\">" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"><title>qed</title>" ++
  sseMeta ++ extLinks ++ styleLink ++ "</head>\n" ++
  "<body><div id=\"app\">loading…</div>\n" ++ reload ++
  s!"<script type=\"module\" src=\"{hostScript}\"></script>\n</body>\n</html>\n"

private def isFrameworkOrStdRoot (modName : String) : Bool :=
  let root := (modName.splitOn ".").headD modName
  root == "Init" || root == "Std" || root == "Lean" || root == "Lake" ||
  root == "Qed" || root == "Js" || root == "Cli"

private def readLocalImports (modName : String) : IO (List String × Bool) := do
  let path := modLeanPath modName
  if !(← path.pathExists) then return ([], false)
  let imps := parseLeanImports (← IO.FS.readFile path)
  let importsDriver := imps.any fun d => d == "Qed.Driver" || d == "Qed.Dom"
  let deps := imps.toList.filter fun d => d != "Qed.Driver" && d != "Qed.Dom" && !isFrameworkOrStdRoot d
  return (deps, importsDriver)

private partial def collectLocalModulesLoop (skipDriver : Bool) :
    List String → Array String → IO (Array String)
  | [], visited => return visited
  | m :: rest, visited => do
      if visited.contains m || isFrameworkOrStdRoot m then
        collectLocalModulesLoop skipDriver rest visited
      else if !(← (modLeanPath m).pathExists) then
        collectLocalModulesLoop skipDriver rest visited
      else
        let (deps, importsDriver) ← readLocalImports m
        let nextVisited := if skipDriver && importsDriver then visited else visited.push m
        collectLocalModulesLoop skipDriver (rest ++ deps) nextVisited

private def collectLocalModules (rootMod : String) (skipDriver : Bool := false) : IO (Array String) :=
  collectLocalModulesLoop skipDriver [rootMod] #[]

private def serverImportModules (rootMod : String) : IO (Array String) := do
  let (deps, importsDriver) ← readLocalImports rootMod
  if importsDriver && !deps.isEmpty then
    return deps.toArray
  else
    return #[rootMod]

private def removeIfExists (p : FilePath) : IO Unit := do
  if ← p.pathExists then
    try IO.FS.removeFile p catch _ => pure ()

private def copyLocalStylesheets (outDir : FilePath) (sheets : List String) : IO Unit := do
  for href in sheets do
    if href.startsWith "/" && !href.startsWith "//" then
      let rel := String.ofList (href.toList.drop 1)
      let candidates : List FilePath := [FilePath.mk rel, FilePath.mk "public" / rel, FilePath.mk "assets" / rel]
      for src in candidates do
        if ← src.pathExists then
          let dst := outDir / rel
          if let some p := dst.parent then IO.FS.createDirAll p
          IO.FS.writeBinFile dst (← IO.FS.readBinFile src)
          break

private def parseCssOutput (outDir : FilePath) (out : String) : IO (Bool × List String) := do
  let mut hasCss := false
  let mut sheets : List String := []
  for line in out.splitOn "\n" do
    let t := line.cliTrim
    if t == "HAS_CSS:1" then hasCss := true
    else if t.startsWith "STYLESHEET:" then
      let s := (String.ofList (t.toList.drop 11)).cliTrim
      if !s.isEmpty then sheets := sheets ++ [s]
  copyLocalStylesheets outDir sheets
  return (hasCss, sheets)

private def saveCssMeta (metaPath : FilePath) (hasCss : Bool) (sheets : List String) : IO Unit := do
  let header := if hasCss then "1" else "0"
  let content := String.intercalate "\n" (header :: sheets) ++ "\n"
  discard <| writeIfChanged metaPath content

private def devTargetStamp : FilePath := ".qed" / "last_dev_target.txt"

private def isSameDevTarget (outDir : FilePath) (mod : String) : IO Bool := do
  if !(← devTargetStamp.pathExists) then return false
  return (← IO.FS.readFile devTargetStamp).cliTrim == s!"{outDir}|{mod}"

private def recordDevTarget (outDir : FilePath) (mod : String) : IO Unit := do
  if let some p := devTargetStamp.parent then IO.FS.createDirAll p
  discard <| writeIfChanged devTargetStamp s!"{outDir}|{mod}\n"

private def loadCssMeta (metaPath : FilePath) : IO (Option (Bool × List String)) := do
  if !(← metaPath.pathExists) then return none
  let lines := ((← IO.FS.readFile metaPath).splitOn "\n").map String.cliTrim |>.filter (!·.isEmpty)
  match lines with
  | "1" :: rest => return some (true, rest)
  | "0" :: rest => return some (false, rest)
  | _ => return none

private def writeClientShell (outDir : FilePath) (prod : Bool)
    (hasStylesCss : Bool := false) (stylesheets : List String := []) (sseUrl : String := "") : IO Unit := do
  for f in ["qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"] do
    discard <| writeIfChanged (outDir / f) (← IO.FS.readFile (← runtimeFile f))
  if !prod then
    discard <| writeIfChanged (outDir / "qed_dev.mjs") (← IO.FS.readFile (← runtimeFile "qed_dev.mjs"))
  else
    removeIfExists (outDir / "qed_dev.mjs")
  discard <| writeIfChanged (outDir / "index.html")
    (indexHtml (dev := !prod) hasStylesCss stylesheets (sseUrl := sseUrl))

private def shortContentHash (bytes : ByteArray) : String :=
  let h : UInt64 := bytes.data.foldl (init := 14695981039346656037) fun acc b =>
    (acc ^^^ b.toUInt64) * 1099511628211
  let hex : Array Char := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  String.ofList <| (List.range 12).map fun i =>
    let shift := UInt64.ofNat ((11 - i) * 4)
    hex[((h >>> shift) &&& 0xF).toNat]!

private def replaceJsImport (src oldSpec newSpec : String) : String :=
  (src.replace s!"'{oldSpec}'" s!"'{newSpec}'").replace s!"\"{oldSpec}\"" s!"\"{newSpec}\""

private def isHexHash (hash : String) : Bool :=
  hash.length >= 8 && hash.length <= 16 &&
    hash.toList.all fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

private def isHashedManagedAsset (name : String) : Bool :=
  match (name.splitOn ".").reverse with
  | ext :: hash :: stem :: [] =>
      let managedStem := stem == "app" || stem == "qed_rt" || stem == "qed_dom" ||
        stem == "qed_host" || stem == "styles"
      let validExt := (stem == "styles" && ext == "css") || (stem != "styles" && ext == "mjs")
      managedStem && validExt && isHexHash hash
  | "map" :: "mjs" :: hash :: stem :: [] =>
      (stem == "app" || stem == "qed_rt" || stem == "qed_dom" || stem == "qed_host") && isHexHash hash
  | _ => false

private def cleanStaleHashedAssets (outDir : FilePath) : IO Unit := do
  if ← outDir.pathExists then
    for entry in ← outDir.readDir do
      if isHashedManagedAsset entry.fileName then
        removeIfExists entry.path

private def hashAsset (outDir : FilePath) (stem : String)
    (rewrites : List (String × String) := []) : IO String := do
  let orig := outDir / s!"{stem}.mjs"
  let origMap := outDir / s!"{stem}.mjs.map"
  let raw ← IO.FS.readFile orig
  let rewritten := rewrites.foldl (fun acc (oldSpec, newSpec) => replaceJsImport acc oldSpec newSpec) raw
  let hashed := s!"{stem}.{shortContentHash rewritten.toUTF8}.mjs"
  let hasMap ← origMap.pathExists
  let finalJs :=
    if hasMap then
      rewritten.replace s!"//# sourceMappingURL={stem}.mjs.map" s!"//# sourceMappingURL={hashed}.map"
    else rewritten
  IO.FS.writeFile (outDir / hashed) finalJs
  removeIfExists orig
  if hasMap then
    let mapRaw ← IO.FS.readFile origMap
    let mapUpdated := mapRaw.replace s!"\"file\":\"{stem}.mjs\"" s!"\"file\":\"{hashed}\""
    IO.FS.writeFile (outDir / s!"{hashed}.map") mapUpdated
    removeIfExists origMap
  return hashed

/-- Emits content-hashed immutable production client assets (`<name>.<12-hex>.(mjs|css)`),
    rewrites ESM import specifiers bottom-up, updates `index.html`, and writes
    `qed_manifest.json` so native servers resolve the hashed entrypoints. -/
private def finalizeProdAssets (outDir : FilePath) (hasStylesCss : Bool) (stylesheets : List String) : IO Unit := do
  cleanStaleHashedAssets outDir
  let rtFile ← hashAsset outDir "qed_rt"
  let domFile ← hashAsset outDir "qed_dom" [("./qed_rt.mjs", s!"./{rtFile}")]
  let appFile ← hashAsset outDir "app" [("./qed_rt.mjs", s!"./{rtFile}")]
  let hostFile ← hashAsset outDir "qed_host" [
    ("./app.mjs", s!"./{appFile}"),
    ("./qed_rt.mjs", s!"./{rtFile}"),
    ("./qed_dom.mjs", s!"./{domFile}")
  ]

  let mut stylesHref := "/styles.css"
  let mut stylesField : List (String × Qed.Json) := []
  if hasStylesCss && (← (outDir / "styles.css").pathExists) then
    let cssRaw ← IO.FS.readBinFile (outDir / "styles.css")
    let cssFile := s!"styles.{shortContentHash cssRaw}.css"
    IO.FS.writeBinFile (outDir / cssFile) cssRaw
    removeIfExists (outDir / "styles.css")
    stylesHref := s!"/{cssFile}"
    stylesField := [("styles", .str stylesHref)]

  IO.FS.writeFile (outDir / "index.html")
    (indexHtml (dev := false) hasStylesCss stylesheets (hostScript := s!"/{hostFile}") (stylesHref := stylesHref))

  let manifest := Qed.Json.render (.obj ([
    ("host", .str s!"/{hostFile}"), ("app", .str s!"/{appFile}"),
    ("rt", .str s!"/{rtFile}"), ("dom", .str s!"/{domFile}")
  ] ++ stylesField)) ++ "\n"
  IO.FS.writeFile (outDir / "qed_manifest.json") manifest

private def resolveServeCmd (dir : FilePath) (port : String) (dev : Bool) :
    IO (String × Array String × Bool) := do
  let devArg := if dev then #["--dev"] else #[]
  if (← (dir / "server").pathExists) then
    return ((dir / "server").toString, #[dir.toString, port] ++ devArg, true)
  else
    let selfBin ← IO.appPath
    return (selfBin.toString, #["serve", dir.toString, port] ++ devArg, false)

initialize fullstackLinkCache :
    IO.Ref (Option (Array String × Array String)) ← IO.mkRef none

private def serverCObjTargets (mod : String) : IO (Array String) := do
  let localMods ← collectLocalModules mod (skipDriver := true)
  return (localMods.map fun m => s!"+{m}:c.o") ++
    #["qed/QedServer:static", "qed/Qed:static", "qed/libqed_server"]

private def resolveLinkMeta (genDir : FilePath) (cObjTargets : Array String) :
    IO (Option (Array String)) := do
  let allExist (ps : Array String) : IO Bool := ps.allM fun p => (FilePath.mk p).pathExists
  if let some (cachedTargets, cachedInputs) ← fullstackLinkCache.get then
    if cachedTargets == cObjTargets && (← allExist cachedInputs) then return some cachedInputs
  let cacheKey := String.intercalate " " cObjTargets.toList
  let metaFile := genDir / "link_meta.txt"
  let lakeDep : Array FilePath ←
    if (← (FilePath.mk "lakefile.lean").pathExists) then pure #[FilePath.mk "lakefile.lean"]
    else if (← (FilePath.mk "lakefile.toml").pathExists) then pure #[FilePath.mk "lakefile.toml"]
    else pure #[]
  if (← isUpToDate metaFile lakeDep) then
    match ((← IO.FS.readFile metaFile).splitOn "\n").map String.cliTrim |>.filter (!·.isEmpty) with
    | k :: rest =>
        if k == cacheKey && !rest.isEmpty then
          let paths := rest.toArray
          if ← allExist paths then
            fullstackLinkCache.set (some (cObjTargets, paths))
            return some paths
    | _ => pure ()
  let some linkInputs ← lakeQueryPaths cObjTargets | return none
  fullstackLinkCache.set (some (cObjTargets, linkInputs))
  IO.FS.createDirAll genDir
  IO.FS.writeFile metaFile (String.intercalate "\n" (cacheKey :: linkInputs.toList) ++ "\n")
  return some linkInputs

private def compileClientMain (leanPath mod appExpr : String) (inRepo prod : Bool) :
    IO (Option (FilePath × FilePath)) := do
  let fwRoot ← if inRepo then pure (FilePath.mk ".") else frameworkHome
  let genDir : FilePath := ".qed" / "gen" / mod
  IO.FS.createDirAll genDir
  let modOlean := modOleanPath mod
  let drvOlean := fwRoot / ".lake" / "build" / "lib" / "lean" / "Qed" / "Driver.olean"
  let cliLean := genDir / "ClientMain.lean"
  let cliOlean := genDir / "ClientMain.olean"
  let cliChanged ← writeIfChanged cliLean s!"import {mod}\nimport Qed.Driver\n\ndef main : IO Unit := Qed.run {appExpr}\n"
  let mut cliDeps : Array FilePath := #[cliLean, modOlean]
  if ← drvOlean.pathExists then cliDeps := cliDeps.push drvOlean
  if cliChanged || prod || !(← isUpToDate cliOlean cliDeps) then
    if (← shLean leanPath #["-R", genDir.toString, cliLean.toString, "-o", cliOlean.toString]) != 0 then
      return none
  return some (genDir, cliOlean)

private def tryCachedCss (outDir cssPath cssMetaPath : FilePath)
    (cssAppExpr? : Option String) (jsDeps : Array FilePath) : IO (Option (Bool × List String)) := do
  let some _ := cssAppExpr? | return some (false, [])
  unless ← isUpToDate cssMetaPath jsDeps do return none
  let some (hasCss, sheets) ← loadCssMeta cssMetaPath | return none
  if hasCss && !(← isUpToDate cssPath jsDeps) then return none
  copyLocalStylesheets outDir sheets
  return some (hasCss, sheets)

private def buildWithNativeServer (mod : String) (clientAppExpr? : Option String)
    (cssAppExpr? : Option String) (serverMainSrc? : Option String) (outDir : FilePath) (prod : Bool)
    (alreadyBuilt : Bool := false) (cObjsBuilt : Bool := false)
    (sourceMap : Bool := false) (sseUrl : String := "") : IO Bool := do
  let buildServer := serverMainSrc?.isSome
  let wantMap := !prod || sourceMap
  let cObjTargets ← if buildServer then serverCObjTargets mod else pure #[]
  let inRepo ← isInRepo
  let prebuilt := (← env "QED_PREBUILT") == some "1"
  if !cObjsBuilt then
    let lakeTargets :=
      (if alreadyBuilt || prebuilt then #[] else #[mod]) ++
      (if alreadyBuilt || (clientAppExpr?.isNone && cssAppExpr?.isNone) then #[] else #["Qed.Driver"]) ++
      (if inRepo && !prebuilt && !alreadyBuilt then #["qedjs"] else #[]) ++
      cObjTargets
    if !lakeTargets.isEmpty then
      if (← shLakeBuild (#["build"] ++ lakeTargets)) != 0 then
        return false
  let some q ← resolveQedjsEnv (needBuild := !inRepo && !prebuilt && !alreadyBuilt) | return false
  let rtPath ← runtimeFile "qed_rt.mjs"
  let genDir : FilePath := ".qed" / "gen" / mod
  if clientAppExpr?.isSome || cssAppExpr?.isSome || buildServer then
    IO.FS.createDirAll genDir
  IO.FS.createDirAll outDir

  let modOlean := modOleanPath mod
  let appMjs := outDir / "app.mjs"
  let appMap := outDir / "app.mjs.map"
  let cssPath := outDir / "styles.css"
  let cssMetaPath := genDir / "css_meta.txt"
  let srvBin := outDir / "server"
  if !buildServer then removeIfExists srvBin
  if !wantMap then removeIfExists appMap

  let sameTarget ← if prod then pure false else isSameDevTarget outDir mod

  -- 1. Synthesize & compile client entrypoint → `app.mjs` + `styles.css` in a single `qedjs` run
  --    (enforcing `verifyNoServerLeakInClient`)
  let tClient ← IO.asTask do
    let (cliGen?, jsDeps) ← match clientAppExpr? with
      | some appExpr =>
          let some (gd, cliOlean) ← compileClientMain q.leanPath mod appExpr inRepo prod | return false
          pure (some gd, #[cliOlean, q.bin, rtPath, modOlean])
      | none =>
          pure (none, #[q.bin, rtPath, modOlean])
    let mapReady ← if wantMap then appMap.pathExists else pure true
    let cached? ← if sameTarget && !prod && mapReady && (← isUpToDate appMjs jsDeps) then
      tryCachedCss outDir cssPath cssMetaPath cssAppExpr? jsDeps else pure none
    let (hasCss, sheets) ← match cached? with
      | some res => pure res
      | none =>
          let minArgs := if prod then #["--min"] else #[]
          let mapArgs := if wantMap then #["--sourcemap"] else #[]
          let rtArgs := #["--rt", rtPath.toString]
          let cssArgs := match cssAppExpr? with
            | some expr => #["--css", cssPath.toString, expr]
            | none      => #[]
          let (entryMod, extraPath) := match cliGen? with
            | some gd => ("ClientMain", some gd.toString)
            | none    => (mod, none)
          let (ok, out) ← q.runOut (minArgs ++ mapArgs ++ rtArgs ++ cssArgs ++ #[appMjs.toString, entryMod, "--"] ++ driverEntries) (extraPath := extraPath)
          if !ok then return false
          match cssAppExpr? with
          | some _ =>
              let (hc, shs) ← parseCssOutput outDir out
              saveCssMeta cssMetaPath hc shs
              pure (hc, shs)
          | none => pure (false, [])
    writeClientShell outDir prod hasCss sheets (sseUrl := sseUrl)
    if prod then
      finalizeProdAssets outDir hasCss sheets
    else
      removeIfExists (outDir / "qed_manifest.json")
    return true

  -- 2. Synthesize & compile native Rust/Lean server binary → `<outDir>/server` while `tClient` runs
  let buildSrv (serverMainSrc : String) : IO Bool := do
    let srvLean := genDir / "ServerMain.lean"
    let srvC := genDir / "ServerMain.c"
    let srvChanged ← writeIfChanged srvLean serverMainSrc
    let some linkInputs ← resolveLinkMeta genDir cObjTargets | return false
    let linkFiles := linkInputs.map FilePath.mk
    if srvChanged || prod || !(← isUpToDate srvC (#[srvLean, modOlean] ++ linkFiles)) then
      if (← shLean q.leanPath #["-R", genDir.toString, srvLean.toString, "-c", srvC.toString]) != 0 then
        return false
    if !sameTarget || prod || !(← isUpToDate srvBin (#[srvC] ++ linkFiles)) then
      let srvTmp := outDir / "server.tmp"
      let optFlags := if prod then #["-O3", "-DNDEBUG"] else #["-O0"]
      let linkerPlatformFlags :=
        if System.Platform.isOSX then #["-Wl,-undefined,dynamic_lookup"] else #["-Wl,--allow-shlib-undefined"]
      let compileArgs := optFlags ++ #[srvC.toString] ++
        linkInputs ++ #["-pthread"] ++ linkerPlatformFlags ++ #["-o", srvTmp.toString]
      let code ← if (← onPath "leanc") then sh "leanc" compileArgs
        else sh "lake" (#["env", "leanc"] ++ compileArgs)
      if code != 0 then return false
      IO.FS.rename srvTmp srvBin
    return true
  let srvOk ← match serverMainSrc? with
    | none => pure true
    | some serverMainSrc => buildSrv serverMainSrc

  let cliOk := (← IO.wait tClient).toOption.getD false
  if cliOk && srvOk && !prod then recordDevTarget outDir mod
  return cliOk && srvOk

private def standaloneServerSrc (mod appName : String) (prod fastClientDev : Bool) : IO (Option String) := do
  if !prod && fastClientDev then return none
  let title := (appName.splitOn ".").headD "qed"
  let impLines := String.intercalate "\n" ((← serverImportModules mod).toList.map fun m => s!"import {m}")
  return some s!"{impLines}\nimport Qed.Server.Native\n\ndef main (args : List String) : IO UInt32 :=\n  Qed.Server.Native.runStandaloneApp {appName} \"{title}\" args\n"

def buildJs (outDir : FilePath) (prod : Bool) (alreadyBuilt : Bool := false)
    (cObjsBuilt : Bool := false) (fastClientDev : Bool := false)
    (sourceMap : Bool := false) (sseUrl : String := "") : IO Bool := do
  let mod ← jsRoot
  let mode ← resolveAppMode mod
  let wantMap := !prod || sourceMap
  match mode with
  | .fullstack fsName =>
      let srvSrc := s!"import {mod}\nimport Qed.Server.Native\n\nqedServerMain {fsName}\n"
      buildWithNativeServer mod (some s!"{fsName}.clientApp") (some s!"{fsName}.clientApp")
        (some srvSrc) outDir prod alreadyBuilt cObjsBuilt wantMap sseUrl
  | .component appName => do
      let srvSrc? ← standaloneServerSrc mod appName prod fastClientDev
      buildWithNativeServer mod (some appName) (some appName) srvSrc? outDir prod alreadyBuilt cObjsBuilt wantMap sseUrl
  | .ssr appName => do
      let srvSrc? ← standaloneServerSrc mod appName prod fastClientDev
      buildWithNativeServer mod none (some appName) srvSrc? outDir prod alreadyBuilt cObjsBuilt wantMap sseUrl
  | .raw =>
      buildWithNativeServer mod none none none outDir prod alreadyBuilt cObjsBuilt wantMap sseUrl

private def clientBundlePaths (outDir : FilePath) : IO (List FilePath) := do
  let defaultNames : List String := ["app.mjs", "qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"]
  if ← (outDir / "app.mjs").pathExists then
    return defaultNames.map fun n => outDir / FilePath.mk n
  let mut found : List FilePath := []
  if ← outDir.pathExists then
    for entry in ← outDir.readDir do
      if isHashedManagedAsset entry.fileName && entry.fileName.endsWith ".mjs" then
        found := entry.path :: found
  return found

private def runDeployManifest (mod : String) (outFile : FilePath) (assetsDir? : Option FilePath)
    (needBuild : Bool) (mods? : Option (Array String) := none) : IO (Bool × String) := do
  let some q ← resolveQedjsEnv (needBuild := needBuild) | return (false, "✗ could not locate qedjs")
  let mods ← match mods? with | some ms => pure ms | none => serverImportModules mod
  let assetsArgs := match assetsDir? with | some d => #["--assets-dir", d.toString] | none => #[]
  q.runOut (#["--emit-deploy-manifest", outFile.toString, mod] ++ assetsArgs ++ mods) (quiet := true)

private def emitDeployManifest (outDir : FilePath) (mod : String) : IO Bool :=
  Prod.fst <$> runDeployManifest mod (outDir / "qed_deploy.json") (some outDir) false

private def deployManifestHasAuth (outDir : FilePath) : IO Bool := do
  let p := outDir / "qed_deploy.json"
  if !(← p.pathExists) then return false
  match Qed.Json.parse (← IO.FS.readFile p) with
  | .ok j => return match j.get? "auth" with | some (.obj _) => true | _ => false
  | .error _ => return false

def cmdManifest (args : List String) : IO UInt32 := do
  let mod ← jsRoot
  let outPath := FilePath.mk (args.getD 0 (distDir / "qed_deploy.json").toString)
  let mods ← serverImportModules mod
  if (← sh "lake" (#["build"] ++ mods)) != 0 then IO.eprintln (red "✗ build failed"); return 1
  let assetsDir? := if (← distDir.pathExists) then some distDir else none
  let (ok, out) ← runDeployManifest mod outPath assetsDir? true (some mods)
  if !ok then IO.eprintln (red out.cliTrim); return 1
  IO.println (green s!"✓ {out.cliTrim}")
  return 0

def cmdDevAuth (args : List String) : IO UInt32 := do
  let port : UInt16 := ((args.getD 0 "8001").toNat?.getD 8001).toUInt16
  IO.println (green s!"qed dev-auth → http://127.0.0.1:{port}   (local ES256 OIDC IdP)")
  DevAuth.runDevAuthServer port

def cmdBuild (prod : Bool) (skipVerify : Bool := false) (sourceMap : Bool := false) : IO UInt32 := do
  let skip := !prod && (skipVerify || (← env "QED_SKIP_VERIFY") == some "1")
  let wantMap := !prod || sourceMap || (← env "QED_SOURCEMAP") == some "1"
  let mod ← jsRoot
  let mode ← resolveAppMode mod
  let extraLakeTargets ← match mode with
    | .raw => pure #[]
    | _    => pure (#["Qed.Driver"] ++ (← serverCObjTargets mod))
  if !skip then
    if !(← verify (checkExterns := false) (extraLakeTargets := extraLakeTargets)) then
      IO.eprintln (red "✗ verification failed"); return 1
  let outOverride ← if prod then pure none else env "QED_OUT_DIR"
  let outDir := match outOverride with
    | some d => FilePath.mk d
    | none   => if prod then distDir else devDir
  if outOverride.isNone then step s!"compiling Lean → {outDir}/"
  if !(← buildJs outDir prod (alreadyBuilt := !skip) (cObjsBuilt := !skip && !extraLakeTargets.isEmpty) (sourceMap := wantMap)) then
    IO.eprintln (red "✗ build failed"); return 1
  if !(← emitDeployManifest outDir mod) then
    IO.eprintln (red "✗ deploy manifest validation failed"); return 1
  if outOverride.isNone then
    let bundlePaths ← clientBundlePaths outDir
    let mut rawBytes := ByteArray.empty
    for p in bundlePaths do rawBytes := rawBytes ++ (← IO.FS.readBinFile p)
    let sz ← if bundlePaths.isEmpty then pure 0 else (·.size) <$> Qed.Server.Prim.gzipCompress rawBytes
    let srvNote := if (← (outDir / "server").pathExists) then s!" + native binary {outDir}/server" else ""
    IO.println (green s!"✓ build complete → {outDir}{srvNote}, {sz} bytes gzipped to the client")
  return 0

def cmdServe (args : List String) : IO UInt32 := do
  let devMode := args.contains "--dev"
  let posArgs := args.filter (· != "--dev")
  let dir := posArgs.getD 0 distDir.toString
  let port : UInt16 := ((posArgs.getD 1 ((← env "PORT").getD devPort)).toNat?.getD 8000).toUInt16
  Qed.Server.Native.runStaticDir dir port devMode

def serveDir (dir : FilePath) (dev : Bool := false) : IO UInt32 := do
  let port := (← env "PORT").getD devPort
  let (cmd, args, _) ← resolveServeCmd dir port dev
  sh cmd args

def cmdStart : IO UInt32 := do
  let hasDist := (← (distDir / "index.html").pathExists) ||
    (← (distDir / "server").pathExists) || (← (distDir / "app.mjs").pathExists)
  if !hasDist then
    IO.eprintln (red "no production build found, run `qed build` first"); return 1
  serveDir distDir

def cmdClean : IO UInt32 := do
  let _ ← sh "lake" #["clean"]
  let _ ← sh "rm" #["-rf", distDir.toString, (FilePath.mk ".qed").toString]
  IO.println (green "✓ cleaned")
  return 0

private def spawnDevChild (port : String) (extraEnv : Array (String × Option String) := #[]) :
    IO (IO.Process.Child ⟨.null, .null, .inherit⟩ × Bool) := do
  let (cmd, args, isNative) ← resolveServeCmd devDir port true
  let c ← IO.Process.spawn { cmd, args, env := extraEnv, stdin := .null, stdout := .null, stderr := .inherit }
  return (c, isNative)

private def spawnDevAuthChild : IO (IO.Process.Child ⟨.null, .null, .inherit⟩ × UInt16) := do
  let p ← Qed.Server.Prim.freePort
  let selfBin ← IO.appPath
  let c ← IO.Process.spawn {
    cmd := selfBin.toString
    args := #["dev-auth", toString p.toNat]
    stdin := .null, stdout := .null, stderr := .inherit
  }
  return (c, p)

/-- Waits up to `timeoutMs` for the local dev server at `127.0.0.1:<port>` to answer `/_qed/health`
    so the browser never sees `ECONNREFUSED` during a server restart. -/
private def waitDevServerHealthy (port : UInt16) (timeoutMs : Nat := 3000) : IO Unit := do
  let deadline := (← IO.monoMsNow) + timeoutMs
  let url := s!"http://127.0.0.1:{port}/_qed/health"
  for _ in [:120] do
    match ← Qed.Server.Native.execHttpCall "GET" url #[] ByteArray.empty false with
    | .ok (200, _, _) => return
    | _ =>
        if (← IO.monoMsNow) >= deadline then return
        IO.sleep 25

private def scanNewestMtime (dir : FilePath) (ext : String) (skipDirs : List String) : IO Int := do
  let mut newest : Int := 0
  for p in ← collect dir ext skipDirs do
    if let some mt ← mtimeNs p then
      if mt > newest then newest := mt
  return newest

private def devSkipDirs : List String :=
  [".lake", ".qed", "dist", ".git", "toolchains", "target", "scratch", "node_modules"]

private def scanDevMtimes (qh : FilePath) : IO (Int × Int × Int) :=
  return (← scanNewestMtime "." "lean" devSkipDirs,
          ← scanNewestMtime "." "css" devSkipDirs,
          ← scanNewestMtime (qh / "runtime") "mjs" [])

private def fileHash? (p : FilePath) : IO (Option String) := do
  if !(← p.pathExists) then return none
  try return some (shortContentHash (← IO.FS.readBinFile p))
  catch _ => return none

private def refreshLocalCss (outDir : FilePath) : IO Unit := do
  let mod ← jsRoot
  let metaPath : FilePath := ".qed" / "gen" / mod / "css_meta.txt"
  if let some (_, sheets) ← loadCssMeta metaPath then
    copyLocalStylesheets outDir sheets

private def publishDevStatus (outDir : FilePath) (sse? : Option Watch.DevSseServer)
    (status : String) (kind : String := "hmr") (errText : String := "")
    (durationMs : Nat := 0) (bumpId : Bool := true) : IO Unit := do
  let sseUrl := match sse? with | some s => s.url | none => ""
  let json ← writeDevStatusJson outDir status kind errText durationMs bumpId sseUrl
  if let some srv := sse? then
    srv.publish json

partial def watchLoop (watcher? : Option Watch.FileWatcher) (sse? : Option Watch.DevSseServer)
    (lastLeanMt lastCssMt lastRtMt : Int) (port : String)
    (curServer : IO.Process.Child ⟨.null, .null, .inherit⟩) (isNative : Bool)
    (devEnv : Array (String × Option String) := #[]) : IO Unit := do
  let qh ← frameworkHome
  let sseUrl := match sse? with | some s => s.url | none => ""
  let mut nextWatcher? := watcher?
  let mut leanChanged := false
  let mut cssChanged := false
  let mut rtChanged := false
  let mut nextLeanMt := lastLeanMt
  let mut nextCssMt := lastCssMt
  let mut nextRtMt := lastRtMt

  match watcher? with
  | some w =>
      let ev ← w.wait 1000
      if ev.error then
        w.close
        nextWatcher? := none
      else
        leanChanged := ev.lean
        cssChanged := ev.css
        rtChanged := ev.runtime
  | none =>
      IO.sleep 120
      let (curLeanMt, curCssMt, curRtMt) ← scanDevMtimes qh
      if curLeanMt > lastLeanMt then
        nextLeanMt := curLeanMt; leanChanged := true
      else if curCssMt > lastCssMt then
        nextCssMt := curCssMt; cssChanged := true
      else if curRtMt > lastRtMt then
        nextRtMt := curRtMt; rtChanged := true

  let mut nextSrv := curServer
  let mut nextNative := isNative
  let portNum : UInt16 := (port.toNat?.getD 8000).toUInt16

  let t0 ← IO.monoMsNow
  let finishOk (kind msg : String) (post : IO Unit := pure ()) : IO Unit := do
    let elapsed := (← IO.monoMsNow) - t0
    publishDevStatus devDir sse? "ok" kind "" elapsed true
    post
    IO.println (green s!"✓ {msg}{elapsed}ms)")

  if leanChanged then
    step "change detected, rebuilding"
    clearLastBuildError
    publishDevStatus devDir sse? "building" "hmr" "" 0 false
    let prevAppHash ← fileHash? (devDir / "app.mjs")
    let prevCssHash ← fileHash? (devDir / "styles.css")
    let prevSrvMtime ← mtimeNs (devDir / "server")
    if (← buildJs devDir (prod := false) (fastClientDev := true) (sourceMap := true) (sseUrl := sseUrl)) then
      let nowNative ← (devDir / "server").pathExists
      let newSrvMtime ← mtimeNs (devDir / "server")
      let newAppHash ← fileHash? (devDir / "app.mjs")
      let newCssHash ← fileHash? (devDir / "styles.css")
      let serverChanged := (nextNative != nowNative) || (nowNative && prevSrvMtime != newSrvMtime)
      if serverChanged then
        curServer.kill
        discard <| curServer.wait
        let (restarted, nat) ← spawnDevChild port devEnv
        nextSrv := restarted
        nextNative := nat
        waitDevServerHealthy portNum
      let cssOnly := !serverChanged && prevAppHash == newAppHash && prevCssHash != newCssHash
      let kind := if cssOnly then "css" else "hmr"
      finishOk kind s!"reloaded ({kind}, " (do if ← isInRepo then discard effectsCovered)
    else
      let elapsed := (← IO.monoMsNow) - t0
      publishDevStatus devDir sse? "error" "hmr" (← getLastBuildError) elapsed false
      IO.eprintln (red "✗ build failed, fix and save again")
  else if cssChanged then
    refreshLocalCss devDir
    finishOk "css" "styles updated ("
  else if rtChanged then
    step "runtime change detected, reloading"
    let mod ← jsRoot
    let (hasCss, sheets) := (← loadCssMeta (".qed" / "gen" / mod / "css_meta.txt")).getD (false, [])
    writeClientShell devDir (prod := false) hasCss sheets (sseUrl := sseUrl)
    finishOk "full" "reloaded runtime ("

  watchLoop nextWatcher? sse? nextLeanMt nextCssMt nextRtMt port nextSrv nextNative devEnv

def cmdDev : IO UInt32 := do
  IO.FS.createDirAll devDir
  let qh ← frameworkHome
  let mod ← jsRoot
  let ssePort : UInt16 := match ← env "QED_DEV_SSE_PORT" with
    | some s => (s.toNat?.getD 0).toUInt16
    | none   => 0
  let sse? ← match ← Watch.DevSseServer.start ssePort with
    | .ok srv => pure (some srv)
    | .error _ => pure none
  let sseUrl := match sse? with | some s => s.url | none => ""
  let watcher? ← match ← Watch.FileWatcher.open "." (qh / "runtime").toString devSkipDirs.toArray with
    | .ok w => pure (some w)
    | .error _ => pure none
  let (initLeanMt, initCssMt, initRtMt) ← if watcher?.isSome then pure (0, 0, 0) else scanDevMtimes qh
  let t0 ← IO.monoMsNow
  step "initial build"
  clearLastBuildError
  let initOk ← buildJs devDir (prod := false) (fastClientDev := true) (sourceMap := true) (sseUrl := sseUrl)
  let elapsed := (← IO.monoMsNow) - t0
  let mut devEnv : Array (String × Option String) := #[]
  let mut devAuthNote := ""
  if initOk then
    discard <| emitDeployManifest devDir mod
    if (← deployManifestHasAuth devDir) && (← env "QED_AUTH_ISSUER").isNone then
      let (_authChild, authPort) ← spawnDevAuthChild
      waitDevServerHealthy authPort
      let issUrl := s!"http://127.0.0.1:{authPort.toNat}"
      devEnv := devEnv.push ("QED_AUTH_ISSUER", some issUrl)
      devAuthNote := s!" + dev-auth ({issUrl})"
    publishDevStatus devDir sse? "ok" "hmr" "" elapsed true
  else
    let errText ← getLastBuildError
    publishDevStatus devDir sse? "error" "hmr" errText elapsed true
    IO.eprintln (red "initial build failed, fix the error and save; dev will rebuild")
  let port := (← env "PORT").getD devPort
  let portNum : UInt16 := (port.toNat?.getD 8000).toUInt16
  let (serverChild, isNative) ← spawnDevChild port devEnv
  waitDevServerHealthy portNum
  let modeTag := if isNative then "   (Native + SSR + HMR)" else "   (HMR)"
  let watchTag := match watcher?, sse? with
    | some _, some _ => "OS watch + SSE push"
    | some _, none   => "OS watch"
    | none, some _   => "SSE push"
    | none, none     => "watching"
  IO.println (green s!"\nqed dev → http://localhost:{port}{modeTag}{devAuthNote}   ({watchTag}; Ctrl-C to stop)\n")
  watchLoop watcher? sse? initLeanMt initCssMt initRtMt port serverChild isNative devEnv
  return 0

end Qed.Cli
