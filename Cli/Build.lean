import Cli.Verify

open System (FilePath)

namespace Qed.Cli

def indexHtml (dev : Bool) (hasStylesCss : Bool := false) (stylesheets : List String := [])
    (hostScript : String := "/qed_host.mjs") (stylesHref : String := "/styles.css") : String :=
  let reload := if dev then
    "<script>(function(){let v=null;setInterval(async()=>{try{const t=await (await fetch('/__build_id',{cache:'no-store'})).text();if(v&&v!==t)location.reload();v=t;}catch(e){}},700)})()</script>\n"
  else ""
  let extLinks := String.join (stylesheets.map fun href =>
    s!"<link rel=\"stylesheet\" href=\"{href}\">")
  let styleLink := if hasStylesCss then s!"<link rel=\"stylesheet\" data-qed-styles href=\"{stylesHref}\">" else ""
  "<!doctype html>\n<html lang=\"en\">\n<head><meta charset=\"utf-8\"><base href=\"/\">" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"><title>qed</title>" ++
  extLinks ++ styleLink ++ "</head>\n" ++
  "<body><div id=\"app\">loading…</div>\n" ++ reload ++
  s!"<script type=\"module\" src=\"{hostScript}\"></script>\n</body>\n</html>\n"

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

private def removeIfExists (p : FilePath) : IO Unit := do
  if ← p.pathExists then
    try IO.FS.removeFile p catch _ => pure ()

def ssrWrapper (appName : String) (cacheKey : String := "")
    (rtImport : String := "./qed_rt.mjs") (hostScript : String := "/qed_host.mjs") : String :=
  let title := (appName.splitOn ".").headD "qed"
  let appImport := "./ssr_app.mjs" ++ (if cacheKey.isEmpty then "" else s!"?build={cacheKey}")
  "import * as mod from '" ++ appImport ++ "';\n" ++
  "import * as rt from '" ++ rtImport ++ "';\n" ++
  "import { makeHandler } from './qed_ssr_host.mjs';\n" ++
  "rt.assertExterns(mod.__externs, rt);\n" ++
  "export { makeHandler, mod };\n" ++
  "export default makeHandler(mod, { title: '" ++ title ++ "', script: '" ++ hostScript ++ "' });\n"

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
    let t := line.trimmed
    if t == "HAS_CSS:1" then hasCss := true
    else if t.startsWith "STYLESHEET:" then
      let s := (String.ofList (t.toList.drop 11)).trimmed
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
  return (← IO.FS.readFile devTargetStamp).trimmed == s!"{outDir}|{mod}"

private def recordDevTarget (outDir : FilePath) (mod : String) : IO Unit := do
  if let some p := devTargetStamp.parent then IO.FS.createDirAll p
  discard <| writeIfChanged devTargetStamp s!"{outDir}|{mod}\n"

private def loadCssMeta (metaPath : FilePath) : IO (Option (Bool × List String)) := do
  if !(← metaPath.pathExists) then return none
  let lines := ((← IO.FS.readFile metaPath).splitOn "\n").map String.trimmed |>.filter (!·.isEmpty)
  match lines with
  | "1" :: rest => return some (true, rest)
  | "0" :: rest => return some (false, rest)
  | _ => return none

private def writeClientShell (outDir : FilePath) (prod : Bool)
    (hasStylesCss : Bool := false) (stylesheets : List String := []) : IO Unit := do
  for f in ["qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"] do
    discard <| writeIfChanged (outDir / f) (← IO.FS.readFile (← runtimeFile f))
  discard <| writeIfChanged (outDir / "index.html") (indexHtml (dev := !prod) hasStylesCss stylesheets)

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

private def shortContentHash (bytes : ByteArray) : String :=
  let h : UInt64 := bytes.data.foldl (init := 14695981039346656037) fun acc b =>
    (acc ^^^ b.toUInt64) * 1099511628211
  let hex : Array Char := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  String.ofList <| (List.range 12).map fun i =>
    let shift := UInt64.ofNat ((11 - i) * 4)
    hex[((h >>> shift) &&& 0xF).toNat]!

private def replaceJsImport (src oldSpec newSpec : String) : String :=
  (src.replace s!"'{oldSpec}'" s!"'{newSpec}'").replace s!"\"{oldSpec}\"" s!"\"{newSpec}\""

private def isHashedManagedAsset (name : String) : Bool :=
  match (name.splitOn ".").reverse with
  | ext :: hash :: stem :: [] =>
      let managedStem := stem == "app" || stem == "qed_rt" || stem == "qed_dom" ||
        stem == "qed_host" || stem == "styles"
      let validExt := (stem == "styles" && ext == "css") || (stem != "styles" && ext == "mjs")
      managedStem && validExt && hash.length >= 8 && hash.length <= 16 &&
        hash.toList.all fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')
  | _ => false

private def cleanStaleHashedAssets (outDir : FilePath) : IO Unit := do
  if ← outDir.pathExists then
    for entry in ← outDir.readDir do
      if isHashedManagedAsset entry.fileName then
        removeIfExists entry.path

private def hashAsset (outDir : FilePath) (stem : String)
    (rewrites : List (String × String) := []) : IO String := do
  let orig := outDir / s!"{stem}.mjs"
  let raw ← IO.FS.readFile orig
  let rewritten := rewrites.foldl (fun acc (oldSpec, newSpec) => replaceJsImport acc oldSpec newSpec) raw
  let hashed := s!"{stem}.{shortContentHash rewritten.toUTF8}.mjs"
  IO.FS.writeFile (outDir / hashed) rewritten
  removeIfExists orig
  return hashed

/-- Emits content-hashed immutable production client assets (`<name>.<12-hex>.(mjs|css)`),
    rewrites ESM import specifiers bottom-up, updates `index.html` and `ssr.mjs`, and writes
    `qed_manifest.json` so native servers and tooling resolve the hashed entrypoints. -/
private def finalizeProdAssets (outDir : FilePath) (hasStylesCss : Bool) (stylesheets : List String)
    (ssrAppName? : Option String) : IO Unit := do
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
  let mut stylesEntry := ""
  if hasStylesCss && (← (outDir / "styles.css").pathExists) then
    let cssRaw ← IO.FS.readBinFile (outDir / "styles.css")
    let cssFile := s!"styles.{shortContentHash cssRaw}.css"
    IO.FS.writeBinFile (outDir / cssFile) cssRaw
    removeIfExists (outDir / "styles.css")
    stylesHref := s!"/{cssFile}"
    stylesEntry := s!",\"styles\":\"/{cssFile}\""

  IO.FS.writeFile (outDir / "index.html")
    (indexHtml (dev := false) hasStylesCss stylesheets (hostScript := s!"/{hostFile}") (stylesHref := stylesHref))

  if let some appName := ssrAppName? then
    let ssrAppPath := outDir / "ssr_app.mjs"
    if ← ssrAppPath.pathExists then
      let ssrAppRaw ← IO.FS.readFile ssrAppPath
      IO.FS.writeFile ssrAppPath (replaceJsImport ssrAppRaw "./qed_rt.mjs" s!"./{rtFile}")
    IO.FS.writeFile (outDir / "ssr.mjs")
      (ssrWrapper appName "" (rtImport := s!"./{rtFile}") (hostScript := s!"/{hostFile}"))

  let manifest :=
    "{" ++
    s!"\"host\":\"/{hostFile}\"," ++
    s!"\"app\":\"/{appFile}\"," ++
    s!"\"rt\":\"/{rtFile}\"," ++
    s!"\"dom\":\"/{domFile}\"" ++
    stylesEntry ++
    "}\n"
  IO.FS.writeFile (outDir / "qed_manifest.json") manifest

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
    IO.Ref (Option (Array String × Array String)) ← IO.mkRef none

private def fullstackCObjTargets (mod : String) : IO (Array String) := do
  let localMods ← collectLocalModules mod
  return (localMods.map fun m => s!"+{m}:c.o") ++
    #["qed/QedServer:static", "qed/Qed:static", "qed/libqed_server"]

private def resolveLinkMeta (genDir : FilePath) (cObjTargets : Array String) :
    IO (Option (Array String)) := do
  if let some (cachedTargets, cachedInputs) ← fullstackLinkCache.get then
    if cachedTargets == cObjTargets then
      let mut ok := true
      for p in cachedInputs do
        if !(← (FilePath.mk p).pathExists) then ok := false; break
      if ok then return some cachedInputs
  let cacheKey := String.intercalate " " cObjTargets.toList
  let metaFile := genDir / "link_meta.txt"
  let lakeDep : Array FilePath ←
    if (← (FilePath.mk "lakefile.lean").pathExists) then pure #[FilePath.mk "lakefile.lean"]
    else if (← (FilePath.mk "lakefile.toml").pathExists) then pure #[FilePath.mk "lakefile.toml"]
    else pure #[]
  if (← isUpToDate metaFile lakeDep) then
    let lines := ((← IO.FS.readFile metaFile).splitOn "\n").map String.trimmed |>.filter (!·.isEmpty)
    match lines with
    | k :: rest =>
        if k == cacheKey && !rest.isEmpty then
          let paths := rest.toArray
          let mut ok := true
          for p in paths do
            if !(← (FilePath.mk p).pathExists) then ok := false; break
          if ok then
            fullstackLinkCache.set (some (cObjTargets, paths))
            return some paths
    | _ => pure ()
  let some linkInputs ← lakeQueryPaths cObjTargets | return none
  fullstackLinkCache.set (some (cObjTargets, linkInputs))
  IO.FS.createDirAll genDir
  IO.FS.writeFile metaFile (String.intercalate "\n" (cacheKey :: linkInputs.toList) ++ "\n")
  return some linkInputs

private def compileClientMain (leanPath mod appExpr : String) (isInRepo prod : Bool) :
    IO (Option (FilePath × FilePath)) := do
  let fwRoot ← if isInRepo then pure (FilePath.mk ".") else frameworkHome
  let genDir : FilePath := ".qed" / "gen" / mod
  IO.FS.createDirAll genDir
  let modOlean := FilePath.mk ".lake" / "build" / "lib" / "lean" / ((mod.replace "." "/") ++ ".olean")
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

def buildFullstack (mod fsName : String) (outDir : FilePath) (prod : Bool)
    (alreadyBuilt : Bool := false) (cObjsBuilt : Bool := false) : IO Bool := do
  let cObjTargets ← fullstackCObjTargets mod
  let isInRepo ← (FilePath.mk "Examples").pathExists
  let prebuilt := (← env "QED_PREBUILT") == some "1"
  if !cObjsBuilt then
    let lakeTargets :=
      (if alreadyBuilt || prebuilt then #[] else #[mod]) ++
      (if alreadyBuilt then #[] else #["Qed.Driver"]) ++
      (if isInRepo && !prebuilt && !alreadyBuilt then #["qedjs"] else #[]) ++
      cObjTargets
    if (← shLakeBuild (#["build"] ++ lakeTargets)) != 0 then
      return false
  let some q ← resolveQedjsEnv (needBuild := !isInRepo && !prebuilt && !alreadyBuilt) | return false
  let rtPath ← runtimeFile "qed_rt.mjs"
  let genDir : FilePath := ".qed" / "gen" / mod
  IO.FS.createDirAll genDir
  IO.FS.createDirAll outDir

  let modOlean := FilePath.mk ".lake" / "build" / "lib" / "lean" / ((mod.replace "." "/") ++ ".olean")
  let srvLean := genDir / "ServerMain.lean"
  let srvC := genDir / "ServerMain.c"
  let srvChanged ← writeIfChanged srvLean s!"import {mod}\nimport Qed.Server.Native\n\nqedServerMain {fsName}\n"

  let appMjs := outDir / "app.mjs"
  let cssPath := outDir / "styles.css"
  let cssMetaPath := genDir / "css_meta.txt"
  let srvBin := outDir / "server"

  let sameTarget ← if prod then pure false else isSameDevTarget outDir mod

  -- 1. Synthesize & compile client entrypoint → `app.mjs` + `styles.css` in a single `qedjs` run
  --    (enforcing `verifyNoServerLeakInClient`)
  let tClient ← IO.asTask do
    let some (_, cliOlean) ← compileClientMain q.leanPath mod s!"{fsName}.clientApp" isInRepo prod | return false
    let jsDeps := #[cliOlean, q.bin, rtPath, modOlean]
    let cached? : Option (Bool × List String) ←
      if sameTarget && !prod && (← isUpToDate appMjs jsDeps) && (← isUpToDate cssMetaPath jsDeps) then
        match ← loadCssMeta cssMetaPath with
        | some (hasCss, sheets) =>
            if !hasCss || (← isUpToDate cssPath jsDeps) then
              copyLocalStylesheets outDir sheets
              pure (some (hasCss, sheets))
            else pure none
        | none => pure none
      else pure none
    let (hasCss, sheets) ← match cached? with
      | some res => pure res
      | none =>
          let minArgs := if prod then #["--min"] else #[]
          let rtArgs := #["--rt", rtPath.toString]
          let cssArgs := #["--css", cssPath.toString, s!"{fsName}.clientApp"]
          let (ok, out) ← q.runOut (minArgs ++ rtArgs ++ cssArgs ++ #[appMjs.toString, "ClientMain", "--"] ++ driverEntries) (extraPath := some genDir.toString)
          if !ok then return false
          let (hc, shs) ← parseCssOutput outDir out
          saveCssMeta cssMetaPath hc shs
          pure (hc, shs)
    writeClientShell outDir prod hasCss sheets
    for stale in ["ssr.mjs", "ssr_app.mjs", "qed_ssr_host.mjs"] do
      removeIfExists (outDir / stale)
    if prod then
      minifyBundles outDir ["app.mjs", "qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"]
      finalizeProdAssets outDir hasCss sheets none
    else
      removeIfExists (outDir / "qed_manifest.json")
    return true

  -- 2. Synthesize & compile native multi-core Rust/Lean server binary → `<outDir>/server`
  let tServer ← IO.asTask do
    let some linkInputs ← resolveLinkMeta genDir cObjTargets | return false
    let linkFiles := linkInputs.map FilePath.mk
    let srvCDeps := #[srvLean, modOlean] ++ linkFiles
    if srvChanged || prod || !(← isUpToDate srvC srvCDeps) then
      if (← shLean q.leanPath #["-R", genDir.toString, srvLean.toString, "-c", srvC.toString]) != 0 then
        return false
    let linkDeps := #[srvC] ++ linkFiles
    if !sameTarget || prod || !(← isUpToDate srvBin linkDeps) then
      let srvTmp := outDir / "server.tmp"
      let optFlags := if prod then #["-O3", "-DNDEBUG"] else #["-O0"]
      let linkerPlatformFlags : Array String :=
        if System.Platform.isOSX then #["-Wl,-undefined,dynamic_lookup"]
        else #["-Wl,--allow-shlib-undefined"]
      let compileArgs := optFlags ++ #[srvC.toString] ++
        linkInputs ++ #["-pthread"] ++ linkerPlatformFlags ++ #["-o", srvTmp.toString]
      let code ← if (← onPath "leanc") then sh "leanc" compileArgs
        else sh "lake" (#["env", "leanc"] ++ compileArgs)
      if code != 0 then return false
      IO.FS.rename srvTmp srvBin
    return true

  let cliOk := (← IO.wait tClient).toOption.getD false
  let srvOk := (← IO.wait tServer).toOption.getD false
  if cliOk && srvOk && !prod then recordDevTarget outDir mod
  return cliOk && srvOk

def buildJs (outDir : FilePath) (prod : Bool) (alreadyBuilt : Bool := false)
    (cObjsBuilt : Bool := false) : IO Bool := do
  let mod ← jsRoot
  let mode ← resolveAppMode mod
  if let .fullstack fsName := mode then
    return ← buildFullstack mod fsName outDir prod alreadyBuilt cObjsBuilt
  let isInRepo ← (FilePath.mk "Examples").pathExists
  let prebuilt := (← env "QED_PREBUILT") == some "1"
  let (autoComp, ssrOpt) : Option String × Option String := match mode with
    | .ssr appName       => (none, some appName)
    | .component appName => (some appName, some appName)
    | _                  => (none, none)
  if !prebuilt && !alreadyBuilt then
    let targets := #[mod] ++ (if autoComp.isSome then #["Qed.Driver"] else #[]) ++ (if isInRepo then #["qedjs"] else #[])
    if (← shLakeBuild (#["build"] ++ targets)) != 0 then return false
  else if autoComp.isSome then
    let fwRoot ← if isInRepo then pure (FilePath.mk ".") else frameworkHome
    let drvOlean := fwRoot / ".lake" / "build" / "lib" / "lean" / "Qed" / "Driver.olean"
    if !(← drvOlean.pathExists) then
      if (← shLakeBuild #["build", "Qed.Driver"]) != 0 then return false
  let some q ← resolveQedjsEnv (needBuild := !isInRepo && !prebuilt && !alreadyBuilt) | return false
  let genDir : FilePath := ".qed" / "gen" / mod
  IO.FS.createDirAll genDir
  IO.FS.createDirAll outDir
  removeIfExists (outDir / "server")
  let rtPath ← runtimeFile "qed_rt.mjs"
  let modOlean := FilePath.mk ".lake" / "build" / "lib" / "lean" / ((mod.replace "." "/") ++ ".olean")
  let appMjs := outDir / "app.mjs"
  let ssrMjs := outDir / "ssr_app.mjs"
  let cssPath := outDir / "styles.css"
  let cssMetaPath := genDir / "css_meta.txt"
  let (cliGen?, jsDeps) ← match autoComp with
    | some appName =>
        let some (gd, cliOlean) ← compileClientMain q.leanPath mod appName isInRepo prod | return false
        pure (some gd, #[cliOlean, q.bin, rtPath, modOlean])
    | none =>
        pure (none, #[q.bin, rtPath, modOlean])
  let sameTarget ← if prod then pure false else isSameDevTarget outDir mod
  let cached? : Option (Bool × List String) ←
    if sameTarget && !prod && (← isUpToDate appMjs jsDeps) && (ssrOpt.isNone || (← isUpToDate ssrMjs jsDeps)) then
      match ssrOpt with
      | none => pure (some (false, []))
      | some _ =>
          if (← isUpToDate cssMetaPath jsDeps) then
            match ← loadCssMeta cssMetaPath with
            | some (hasCss, sheets) =>
                if !hasCss || (← isUpToDate cssPath jsDeps) then
                  copyLocalStylesheets outDir sheets
                  pure (some (hasCss, sheets))
                else pure none
            | none => pure none
          else pure none
    else pure none
  let (hasCss, sheets) ← match cached? with
    | some res => pure res
    | none =>
        let minArgs := if prod then #["--min"] else #[]
        let rtArgs := #["--rt", rtPath.toString]
        let cssArgs : Array String := match ssrOpt with
          | some appName => #["--css", cssPath.toString, appName]
          | none         => #[]
        let alsoArgs : Array String := match ssrOpt with
          | some appName => #["--also", ssrMjs.toString, "--", s!"{appName}:app", "Qed.App.ssrStep:ssrStep"]
          | none => #[]
        let (ok, out) ← match cliGen? with
          | some gd =>
              q.runOut (minArgs ++ rtArgs ++ cssArgs ++ #[appMjs.toString, "ClientMain", "--"] ++ driverEntries ++ alsoArgs) (extraPath := some gd.toString)
          | none =>
              q.runOut (minArgs ++ rtArgs ++ cssArgs ++ #[appMjs.toString, mod, "--"] ++ driverEntries ++ alsoArgs)
        if !ok then return false
        match ssrOpt with
        | some _ =>
            let (hc, shs) ← parseCssOutput outDir out
            saveCssMeta cssMetaPath hc shs
            pure (hc, shs)
        | none => pure (false, [])
  writeClientShell outDir prod hasCss sheets
  match ssrOpt with
  | some appName =>
      discard <| writeIfChanged (outDir / "qed_ssr_host.mjs") (← IO.FS.readFile (← runtimeFile "qed_ssr_host.mjs"))
      let cacheKey ← if prod then pure "" else toString <$> IO.monoMsNow
      IO.FS.writeFile (outDir / "ssr.mjs") (ssrWrapper appName cacheKey)
  | none =>
      IO.println s!"  note: no `Qed.run <app>` found in {mod}, skipping the SSR handler (ssr.mjs)"
  if prod then
    minifyBundles outDir ["app.mjs", "qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs", "ssr_app.mjs", "qed_ssr_host.mjs"]
    finalizeProdAssets outDir hasCss sheets ssrOpt
  else
    removeIfExists (outDir / "qed_manifest.json")
    recordDevTarget outDir mod
  return true

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

def cmdBuild (prod : Bool) (skipVerify : Bool := false) : IO UInt32 := do
  let skip := !prod && (skipVerify || (← env "QED_SKIP_VERIFY") == some "1")
  let mod ← jsRoot
  let mode ← resolveAppMode mod
  let extraLakeTargets ← match mode with
    | .fullstack _ => pure (#["Qed.Driver"] ++ (← fullstackCObjTargets mod))
    | _            => pure #[]
  if !skip then
    if !(← verify (checkExterns := false) (extraLakeTargets := extraLakeTargets)) then
      IO.eprintln (red "✗ verification failed"); return 1
  let outOverride ← if prod then pure none else env "QED_OUT_DIR"
  let outDir := match outOverride with
    | some d => FilePath.mk d
    | none   => if prod then distDir else devDir
  if outOverride.isNone then step s!"compiling Lean → {outDir}/"
  if !(← buildJs outDir prod (alreadyBuilt := !skip) (cObjsBuilt := !skip && !extraLakeTargets.isEmpty)) then
    IO.eprintln (red "✗ build failed"); return 1
  if outOverride.isNone then
    let bundlePaths ← clientBundlePaths outDir
    let filesArg := String.intercalate " " (bundlePaths.map (fun p => s!"'{p}'"))
    let (_, sz) ← if bundlePaths.isEmpty then pure (0, "0") else
      shOut "bash" #["-c", s!"cat {filesArg} | gzip -c | wc -c"]
    let srvNote := if (← (outDir / "server").pathExists) then s!" + native binary {outDir}/server" else ""
    IO.println (green s!"✓ build complete → {outDir}{srvNote}, {sz.trimmed} bytes gzipped to the client")
  return 0

def serveDir (dir : FilePath) (dev : Bool := false) : IO UInt32 := do
  let port := (← env "PORT").getD devPort
  let (cmd, args, _) ← resolveServeCmd dir port dev
  if cmd == "python3" then IO.println s!"serving {dir} → http://localhost:{port}"
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
