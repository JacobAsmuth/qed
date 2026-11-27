import Cli.Verify
import Cli.Watch
import Cli.DevAuth
import Qed.Server.Native
open System (FilePath)

namespace Qed.Cli

def indexHtml (dev : Bool) (hasStylesCss : Bool := false) (stylesheets : List String := [])
    (hostScript : String := "/qed_host.mjs") (stylesHref : String := "/styles.css") (sseUrl : String := "") : String :=
  "<!doctype html>\n<html lang=\"en\">\n<head><meta charset=\"utf-8\"><base href=\"/\"><meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"><title>qed</title>" ++
  (if dev && !sseUrl.isEmpty then s!"<meta name=\"qed-dev-sse\" content=\"{Qed.escapeHtml sseUrl}\">" else "") ++
  Qed.renderStylesheetLinks stylesheets ++
  (if hasStylesCss then s!"<link rel=\"stylesheet\" data-qed-styles href=\"{Qed.escapeHtml stylesHref}\">" else "") ++
  s!"</head>\n<body><div id=\"app\">loading…</div>\n{if dev then "<script type=\"module\" src=\"/qed_dev.mjs\"></script>\n" else ""}<script type=\"module\" src=\"{Qed.escapeHtml hostScript}\"></script>\n</body>\n</html>\n"

private def isFrameworkOrStdRoot (modName : String) : Bool :=
  ["Init", "Std", "Lean", "Lake", "Qed", "Js", "Cli"].contains ((modName.splitOn ".").headD modName)

private def readLocalImports (modName : String) : IO (List String × Bool) := do
  let path := modLeanPath modName; if !(← path.pathExists) then return ([], false)
  let imps := parseLeanImports (← IO.FS.readFile path)
  return (imps.toList.filter fun d => d != "Qed.Driver" && d != "Qed.Dom" && !isFrameworkOrStdRoot d, imps.any fun d => d == "Qed.Driver" || d == "Qed.Dom")

private partial def collectLocalModulesLoop (skipDriver : Bool) : List String → Array String → IO (Array String)
  | [], visited => return visited
  | m :: rest, visited => do
      if ← orB (visited.contains m || isFrameworkOrStdRoot m) ((!·) <$> (modLeanPath m).pathExists) then collectLocalModulesLoop skipDriver rest visited
      else let (deps, importsDriver) ← readLocalImports m; collectLocalModulesLoop skipDriver (rest ++ deps) (if skipDriver && importsDriver then visited else visited.push m)

private def serverImportModules (rootMod : String) : IO (Array String) := do
  let (deps, importsDriver) ← readLocalImports rootMod; return if importsDriver && !deps.isEmpty then deps.toArray else #[rootMod]

private def isSafeStylesheetHref (href : String) : Bool :=
  href.startsWith "/" && !href.startsWith "//" && !href.endsWith "/" && href.toLower.endsWith ".css" &&
  !Qed.Cloud.Env.hasCtrlOrWs href "\\?#" (forbidWs := false) &&
  let segs := (href.drop 1).toString.splitOn "/"; !segs.isEmpty && segs.all fun s => !s.isEmpty && !s.startsWith "."

private def ensureSafeSubdir (outReal : FilePath) (outPrefix : String) : List String → IO (Option FilePath)
  | [] => pure (some outReal)
  | seg :: rest => do
      let next := outReal / seg
      match ← symlinkType? next with
      | some ty => if ty != .dir then return none
      | none => try IO.FS.createDir next catch _ => return none
      let some nextReal ← realPath? next | return none
      if !nextReal.toString.startsWith outPrefix then return none
      ensureSafeSubdir nextReal outPrefix rest

private def copyFirstLocalSheet (rootPrefix : String) (outReal : FilePath) (outPrefix : String) (segs : List String) (fileName : String) : List FilePath → IO Unit
  | [] => pure ()
  | src :: rest => do
      if ← src.pathExists then
        if let some sr ← realPath? src then
          let isFile ← try pure ((← sr.metadata).type == .file) catch _ => pure false
          if isFile && sr.toString.startsWith rootPrefix then
            if let some dstParent ← ensureSafeSubdir outReal outPrefix segs.dropLast then
              discard <| writeBytesInsideDir dstParent fileName (← IO.FS.readBinFile sr)
            return
      copyFirstLocalSheet rootPrefix outReal outPrefix segs fileName rest

private def copyLocalStylesheets (outDir : FilePath) (sheets : List String) : IO Unit := do
  let rootPrefix := dirPrefix (← IO.FS.realPath "."); IO.FS.createDirAll outDir
  let outReal ← IO.FS.realPath outDir; let outPrefix := dirPrefix outReal
  sheets.forM fun href => do
    if isSafeStylesheetHref href then
      let rel := (href.drop 1).toString; let segs := rel.splitOn "/"; let fileName := segs.getLastD ""
      if !fileName.isEmpty then
        copyFirstLocalSheet rootPrefix outReal outPrefix segs fileName [FilePath.mk rel, FilePath.mk "public" / rel, FilePath.mk "assets" / rel]

private def parseCssOutput (outDir : FilePath) (out : String) : IO (Bool × List String) := do
  let lines := nonEmptyLines out
  let sheets := lines.filterMap fun t => if t.startsWith "STYLESHEET:" then let s := (t.drop 11).toString.cliTrim; if s.isEmpty then none else some s else none
  copyLocalStylesheets outDir sheets; return (lines.contains "HAS_CSS:1", sheets)

private def loadCssMeta (metaPath : FilePath) : IO (Option (Bool × List String)) := do
  let some raw ← readTrimmed? metaPath | return none
  return match nonEmptyLines raw with | "1" :: rest => some (true, rest) | "0" :: rest => some (false, rest) | _ => none

private def writeClientShell (outDir : FilePath) (prod : Bool) (hasStylesCss : Bool := false) (stylesheets : List String := []) (sseUrl : String := "") : IO Unit := do
  (["qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"] ++ (if prod then [] else ["qed_dev.mjs"])).forM fun f => do
    discard <| writeIfChanged (outDir / f) (← IO.FS.readFile (← runtimeFile f))
  if prod then removeIfExists (outDir / "qed_dev.mjs")
  discard <| writeIfChanged (outDir / "index.html") (indexHtml (dev := !prod) hasStylesCss stylesheets (sseUrl := sseUrl))

def shortContentHash (bytes : ByteArray) : String :=
  let h : UInt64 := bytes.data.foldl (init := 14695981039346656037) fun acc b => (acc ^^^ b.toUInt64) * 1099511628211
  let hex : Array Char := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  String.ofList <| (List.range 12).map fun i => hex[((h >>> UInt64.ofNat ((11 - i) * 4)) &&& 0xF).toNat]!

private def isHashedManagedAsset (name : String) : Bool :=
  let isMap := name.endsWith ".mjs.map"; let base := if isMap then (name.dropEnd 4).toString else name
  let parts := base.splitOn "."; let stem := parts.headD ""
  parts.length == 3 && ["app", "qed_rt", "qed_dom", "qed_host", "styles"].contains stem && (!isMap || stem != "styles") && Qed.Server.Http.isContentHashedAsset base

private def hashAsset (outDir : FilePath) (stem : String) (rewrites : List (String × String) := []) : IO String := do
  let (orig, origMap) := (outDir / s!"{stem}.mjs", outDir / s!"{stem}.mjs.map")
  let rewritten := rewrites.foldl (fun acc (o, n) => (acc.replace s!"'{o}'" s!"'{n}'").replace s!"\"{o}\"" s!"\"{n}\"") (← IO.FS.readFile orig)
  let hashed := s!"{stem}.{shortContentHash rewritten.toUTF8}.mjs"; let hasMap ← origMap.pathExists
  IO.FS.writeFile (outDir / hashed) (if hasMap then rewritten.replace s!"//# sourceMappingURL={stem}.mjs.map" s!"//# sourceMappingURL={hashed}.map" else rewritten)
  removeIfExists orig
  if hasMap then IO.FS.writeFile (outDir / s!"{hashed}.map") ((← IO.FS.readFile origMap).replace s!"\"file\":\"{stem}.mjs\"" s!"\"file\":\"{hashed}\""); removeIfExists origMap
  return hashed

private def finalizeProdAssets (outDir : FilePath) (hasStylesCss : Bool) (stylesheets : List String) : IO Unit := do
  if ← outDir.pathExists then (← outDir.readDir).forM fun e => if isHashedManagedAsset e.fileName then removeIfExists e.path else pure ()
  let rtFile ← hashAsset outDir "qed_rt"
  let domFile ← hashAsset outDir "qed_dom" [("./qed_rt.mjs", s!"./{rtFile}")]
  let appFile ← hashAsset outDir "app" [("./qed_rt.mjs", s!"./{rtFile}")]
  let hostFile ← hashAsset outDir "qed_host" [("./app.mjs", s!"./{appFile}"), ("./qed_rt.mjs", s!"./{rtFile}"), ("./qed_dom.mjs", s!"./{domFile}")]
  let (stylesHref, stylesField) ← if ← andB hasStylesCss (outDir / "styles.css").pathExists then do
      let cssRaw ← IO.FS.readBinFile (outDir / "styles.css"); let cssFile := s!"styles.{shortContentHash cssRaw}.css"
      IO.FS.writeBinFile (outDir / cssFile) cssRaw; removeIfExists (outDir / "styles.css"); pure (s!"/{cssFile}", [("styles", Qed.Json.str s!"/{cssFile}")])
    else pure ("/styles.css", [])
  IO.FS.writeFile (outDir / "index.html") (indexHtml (dev := false) hasStylesCss stylesheets (hostScript := s!"/{hostFile}") (stylesHref := stylesHref))
  IO.FS.writeFile (outDir / "qed_manifest.json") <|
    Qed.Json.render (.obj ([("host", .str s!"/{hostFile}"), ("app", .str s!"/{appFile}"), ("rt", .str s!"/{rtFile}"), ("dom", .str s!"/{domFile}")] ++ stylesField)) ++ "\n"

private def resolveServeCmd (dir : FilePath) (port : String) (dev : Bool) : IO (String × Array String × Bool) := do
  let devArg := if dev then #["--dev"] else #[]
  if ← (dir / "server").pathExists then return ((dir / "server").toString, #[dir.toString, port] ++ devArg, true)
  return ((← IO.appPath).toString, #["serve", dir.toString, port] ++ devArg, false)

initialize fullstackLinkCache : IO.Ref (Option (Array String × Array String)) ← IO.mkRef none

private def serverCObjTargets (mod : String) : IO (Array String) := do
  return ((← collectLocalModulesLoop true [mod] #[]).map fun m => s!"+{m}:c.o") ++ #["qed/QedServer:static", "qed/Qed:static", "qed/libqed_server"]

private def staticLibPaths : List (String × FilePath) :=
  [("qed/QedServer:static", ".lake" / "build" / "lib" / "libqed_QedServer.a"),
   ("qed/Qed:static", ".lake" / "build" / "lib" / "libqed_Qed.a"),
   ("qed/libqed_server", ".lake" / "build" / "lib" / "libqed_server.a")]

private def resolveDirectLinkInputs (cObjTargets : Array String) : IO (Option (Array String)) :=
  cObjTargets.foldlM (init := some #[]) fun acc? t => do
    let some out := acc? | return none
    let p? : Option FilePath ← match staticLibPaths.lookup t with
      | some p => pure (some p)
      | none =>
          if t.startsWith "+" && t.endsWith ":c.o" then
            let b := (FilePath.mk ".lake" / "build" / "ir" / (((t.drop 1).dropEnd 4).toString.replace "." "/")).toString
            let exp := FilePath.mk (b ++ ".c.o.export")
            pure (some (if ← exp.pathExists then exp else FilePath.mk (b ++ ".c.o")))
          else pure none
    match p? with
    | some p => if ← p.pathExists then return some (out.push p.toString) else return none
    | none => return none

private def resolveLinkMeta (genDir : FilePath) (cObjTargets : Array String) (inRepo : Bool) : IO (Option (Array String)) := do
  let allExist (ps : Array String) : IO Bool := ps.allM fun p => (FilePath.mk p).pathExists
  if let some (ct, ci) ← fullstackLinkCache.get then if ← andB (ct == cObjTargets) (allExist ci) then return some ci
  if inRepo then if let some direct ← resolveDirectLinkInputs cObjTargets then fullstackLinkCache.set (some (cObjTargets, direct)); return some direct
  let (cacheKey, metaFile) := (" ".intercalate cObjTargets.toList, genDir / "link_meta.txt")
  let lakeDep ← if ← (FilePath.mk "lakefile.lean").pathExists then pure #[FilePath.mk "lakefile.lean"]
    else if ← (FilePath.mk "lakefile.toml").pathExists then pure #[FilePath.mk "lakefile.toml"] else pure #[]
  if ← isUpToDate metaFile lakeDep then
    if let k :: rest := nonEmptyLines (← IO.FS.readFile metaFile) then
      if ← andB (k == cacheKey && !rest.isEmpty) (allExist rest.toArray) then fullstackLinkCache.set (some (cObjTargets, rest.toArray)); return some rest.toArray
  let some linkInputs ← lakeQueryPaths cObjTargets | return none
  fullstackLinkCache.set (some (cObjTargets, linkInputs)); IO.FS.createDirAll genDir
  IO.FS.writeFile metaFile ("\n".intercalate (cacheKey :: linkInputs.toList) ++ "\n"); return some linkInputs

private def compileClientMain (leanPath mod appExpr : String) (inRepo : Bool) : IO (Option (FilePath × FilePath)) := do
  let fwRoot ← if inRepo then pure (FilePath.mk ".") else frameworkHome
  let genDir : FilePath := ".qed" / "gen" / mod; IO.FS.createDirAll genDir
  let (drvOlean, cliLean, cliOlean) := (fwRoot / ".lake" / "build" / "lib" / "lean" / "Qed" / "Driver.olean", genDir / "ClientMain.lean", genDir / "ClientMain.olean")
  let cliChanged ← writeIfChanged cliLean s!"import {mod}\nimport Qed.Driver\n\ndef main : IO Unit := Qed.run {appExpr}\n"
  let cliDeps := #[cliLean, modOleanPath mod] ++ (if ← drvOlean.pathExists then #[drvOlean] else #[])
  if ← orB cliChanged ((!·) <$> isUpToDate cliOlean cliDeps) then
    if (← shLean leanPath #["-R", genDir.toString, cliLean.toString, "-o", cliOlean.toString]) != 0 then return none
  return some (genDir, cliOlean)

private def tryCachedCss (outDir cssPath cssMetaPath : FilePath) (cssAppExpr? : Option String) (jsDeps : Array FilePath) : IO (Option (Bool × List String)) := do
  let some _ := cssAppExpr? | return some (false, [])
  unless ← isUpToDate cssMetaPath jsDeps do return none
  let some (hasCss, sheets) ← loadCssMeta cssMetaPath | return none
  if ← andB hasCss ((!·) <$> isUpToDate cssPath jsDeps) then return none
  copyLocalStylesheets outDir sheets; return some (hasCss, sheets)

private def prebuiltArtifactsReady (mod : String) (inRepo needDrv buildServer : Bool) (cObjTargets : Array String) : IO Bool := do
  let fwRoot ← if inRepo then pure (FilePath.mk ".") else frameworkHome
  unless ← (modOleanPath mod).pathExists do return false
  if needDrv then unless ← (fwRoot / ".lake" / "build" / "lib" / "lean" / "Qed" / "Driver.olean").pathExists do return false
  if !buildServer then return true
  if inRepo then return (← resolveDirectLinkInputs cObjTargets).isSome else return false

private def buildWithNativeServer (mod : String) (clientAppExpr? cssAppExpr? serverMainSrc? : Option String)
    (outDir : FilePath) (prod alreadyBuilt cObjsBuilt wantMap : Bool) (sseUrl : String) : IO Bool := do
  let buildServer := serverMainSrc?.isSome; let cObjTargets ← if buildServer then serverCObjTargets mod else pure #[]
  let (inRepo, prebuilt, needDrv) := (← isInRepo, (← env "QED_PREBUILT") == some "1", clientAppExpr?.isSome || cssAppExpr?.isSome)
  let prebuiltOk ← andB prebuilt (prebuiltArtifactsReady mod inRepo needDrv buildServer cObjTargets)
  let (effBuilt, effCObjs) := (alreadyBuilt || prebuiltOk, cObjsBuilt || prebuiltOk)
  if !effCObjs then
    let lakeTargets := (if effBuilt || prebuilt then #[] else #[mod]) ++ (if effBuilt || !needDrv then #[] else #["Qed.Driver"]) ++
      (if inRepo && !prebuilt && !effBuilt then #["qedjs"] else #[]) ++ cObjTargets
    if !lakeTargets.isEmpty then if (← shLakeBuild (#["build"] ++ lakeTargets)) != 0 then return false
  let some q ← resolveQedjsEnv (needBuild := !inRepo && !prebuilt && !effBuilt) | return false
  let (rtPath, genDir) := (← runtimeFile "qed_rt.mjs", FilePath.mk ".qed" / "gen" / mod)
  if needDrv || buildServer then IO.FS.createDirAll genDir
  IO.FS.createDirAll outDir
  let (modOlean, appMjs, appMap, cssPath, cssMetaPath, srvBin) :=
    (modOleanPath mod, outDir / "app.mjs", outDir / "app.mjs.map", outDir / "styles.css", genDir / "css_meta.txt", outDir / "server")
  if !buildServer then removeIfExists srvBin
  if !wantMap then removeIfExists appMap
  let (stampPath, stampVal) := (outDir / ".qed_target", s!"{mod}|{prod}|{wantMap}")
  let prevStamp? ← readTrimmed? stampPath
  let sameClient := prevStamp? == some stampVal
  let sameServer := match prevStamp?.map (·.splitOn "|") with | some (pm :: pp :: _) => pm == mod && pp == toString prod | _ => false
  let tClient ← IO.asTask do
    let (cliGen?, jsDeps) ← match clientAppExpr? with
      | some appExpr =>
          let some (gd, cliOlean) ← compileClientMain q.leanPath mod appExpr inRepo | return false
          pure (some gd, #[cliOlean, q.bin, rtPath, modOlean])
      | none         => pure (none, #[q.bin, rtPath, modOlean])
    let cached? ← if ← andB (sameClient && !prod) (do andB (← orB (!wantMap) appMap.pathExists) (isUpToDate appMjs jsDeps)) then
        tryCachedCss outDir cssPath cssMetaPath cssAppExpr? jsDeps else pure none
    let (hasCss, sheets) ← match cached? with
      | some res => pure res
      | none =>
          let args := (if prod then #["--min"] else #[]) ++ (if wantMap then #["--sourcemap"] else #[]) ++ #["--rt", rtPath.toString] ++
            (cssAppExpr?.elim #[] fun e => #["--css", cssPath.toString, e]) ++ #[appMjs.toString, if cliGen?.isSome then "ClientMain" else mod, "--"] ++ driverEntries
          let (ok, out) ← q.runOut args (extraPath := cliGen?.map FilePath.toString); if !ok then return false
          if cssAppExpr?.isSome then
            let (hc, shs) ← parseCssOutput outDir out; discard <| writeIfChanged cssMetaPath ("\n".intercalate ((if hc then "1" else "0") :: shs) ++ "\n"); pure (hc, shs)
          else pure (false, [])
    writeClientShell outDir prod hasCss sheets (sseUrl := sseUrl)
    if prod then finalizeProdAssets outDir hasCss sheets else removeIfExists (outDir / "qed_manifest.json")
    return true
  let srvOk ← match serverMainSrc? with
    | none => pure true
    | some serverMainSrc => do
        let (srvLean, srvC) := (genDir / "ServerMain.lean", genDir / "ServerMain.c")
        let srvChanged ← writeIfChanged srvLean serverMainSrc
        let some linkInputs ← resolveLinkMeta genDir cObjTargets inRepo | return false
        let linkFiles := linkInputs.map FilePath.mk
        if ← orB srvChanged ((!·) <$> isUpToDate srvC (#[srvLean, modOlean] ++ linkFiles)) then
          if (← shLean q.leanPath #["-R", genDir.toString, srvLean.toString, "-c", srvC.toString]) != 0 then return false
        if ← orB (!sameServer) ((!·) <$> isUpToDate srvBin (#[srvC] ++ linkFiles)) then
          let srvTmp := outDir / "server.tmp"
          let compileArgs := (if prod then #["-O3", "-DNDEBUG"] else #["-O0"]) ++ #[srvC.toString] ++ linkInputs ++
            #["-pthread", if System.Platform.isOSX then "-Wl,-undefined,dynamic_lookup" else "-Wl,--allow-shlib-undefined", "-o", srvTmp.toString]
          if (← if ← onPath "leanc" then sh "leanc" compileArgs else sh "lake" (#["env", "leanc"] ++ compileArgs)) != 0 then return false
          IO.FS.rename srvTmp srvBin
        pure true
  let cliOk := (← IO.wait tClient).toOption.getD false
  if cliOk && srvOk then discard <| writeIfChanged stampPath (stampVal ++ "\n")
  return cliOk && srvOk

private def standaloneServerSrc (mod appName : String) (prod fastClientDev : Bool) : IO (Option String) := do
  if !prod && fastClientDev then return none
  let impLines := "\n".intercalate ((← serverImportModules mod).toList.map (s!"import {·}"))
  return some s!"{impLines}\nimport Qed.Server.Native\n\ndef main (args : List String) : IO UInt32 :=\n  Qed.Server.Native.runStandaloneApp {appName} \"{(appName.splitOn ".").headD "qed"}\" args\n"

def buildJs (outDir : FilePath) (prod : Bool) (alreadyBuilt : Bool := false) (cObjsBuilt : Bool := false)
    (fastClientDev : Bool := false) (sourceMap : Bool := false) (sseUrl : String := "") (mod? : Option String := none) : IO Bool := do
  let mod ← mod?.elim jsRoot pure
  let (cli?, css?, srv?) ← match ← resolveAppMode mod with
    | .fullstack fs => pure (some s!"{fs}.clientApp", some s!"{fs}.clientApp", some s!"import {mod}\nimport Qed.Server.Native\n\nqedServerMain {fs}\n")
    | .component a  => pure (some a, some a, ← standaloneServerSrc mod a prod fastClientDev)
    | .ssr a        => pure (none, some a, ← standaloneServerSrc mod a prod fastClientDev)
    | .raw          => pure (none, none, none)
  buildWithNativeServer mod cli? css? srv? outDir prod alreadyBuilt cObjsBuilt (!prod || sourceMap) sseUrl

private def clientBundlePaths (outDir : FilePath) : IO (List FilePath) := do
  if ← (outDir / "app.mjs").pathExists then return ["app.mjs", "qed_rt.mjs", "qed_dom.mjs", "qed_host.mjs"].map (outDir / FilePath.mk ·)
  if !(← outDir.pathExists) then return []
  return (← outDir.readDir).toList.filterMap fun e => if isHashedManagedAsset e.fileName && e.fileName.endsWith ".mjs" then some e.path else none

private def runDeployManifest (mod : String) (outFile : FilePath) (assetsDir? : Option FilePath) (needBuild : Bool) (mods? : Option (Array String) := none) : IO (Bool × String) := do
  let some q ← resolveQedjsEnv (needBuild := needBuild) | return (false, "✗ could not locate qedjs")
  let mods ← mods?.elim (serverImportModules mod) pure
  q.runOut (#["--emit-deploy-manifest", outFile.toString, mod] ++ (assetsDir?.elim #[] fun d => #["--assets-dir", d.toString]) ++ mods) (quiet := true)

private def emitDeployManifest (outDir : FilePath) (mod : String) : IO Bool := Prod.fst <$> runDeployManifest mod (outDir / "qed_deploy.json") (some outDir) false
private def deployManifestHasAuth (outDir : FilePath) : IO Bool := do
  let some raw ← readTrimmed? (outDir / "qed_deploy.json") | return false
  return match Qed.Json.parse raw with | .ok j => (j.get? "auth").any (fun | .obj _ => true | _ => false) | .error _ => false

def cmdManifest (args : List String) : IO UInt32 := do
  let mod ← jsRoot; let outPath := FilePath.mk (args.getD 0 (distDir / "qed_deploy.json").toString); let mods ← serverImportModules mod
  if (← sh "lake" (#["build"] ++ mods)) != 0 then IO.eprintln (red "✗ build failed"); return 1
  let (ok, out) ← runDeployManifest mod outPath (if ← distDir.pathExists then some distDir else none) true (some mods)
  if !ok then IO.eprintln (red out.cliTrim); return 1
  IO.println (green s!"✓ {out.cliTrim}"); return 0

def cmdDevAuth (args : List String) : IO UInt32 := do
  let port := parsePort (args.getD 0 "8001") 8001
  IO.println (green s!"qed dev-auth → http://127.0.0.1:{port}   (local ES256 OIDC IdP)"); DevAuth.runDevAuthServer port

def cmdBuild (prod : Bool) (skipVerify : Bool := false) (sourceMap : Bool := false) (mod? : Option String := none) (outDir? : Option FilePath := none) : IO UInt32 := do
  let skip ← andB (!prod) (orB skipVerify ((· == some "1") <$> env "QED_SKIP_VERIFY"))
  let wantMap ← orB (!prod || sourceMap) ((· == some "1") <$> env "QED_SOURCEMAP")
  let mod ← mod?.elim jsRoot pure
  let (alreadyBuilt, cObjsBuilt) ← if skip then pure (false, false) else do
    let extraLakeTargets ← match ← resolveAppMode mod with
      | .raw => pure (if mod?.isSome then #[mod] else #[]) | _ => pure ((if mod?.isSome then #[mod] else #[]) ++ #["Qed.Driver"] ++ (← serverCObjTargets mod))
    if !(← verify (checkExterns := false) (extraLakeTargets := extraLakeTargets) (targetMod? := some mod)) then IO.eprintln (red "✗ verification failed"); return 1
    pure (true, !extraLakeTargets.isEmpty)
  let outOverride ← if prod then pure none else env "QED_OUT_DIR"
  let outDir := outDir?.getD (outOverride.elim (if prod then distDir else devDir) FilePath.mk)
  if outOverride.isNone then step s!"compiling Lean → {outDir}/"
  if !(← buildJs outDir prod (alreadyBuilt := alreadyBuilt) (cObjsBuilt := cObjsBuilt) (sourceMap := wantMap) (mod? := some mod)) then IO.eprintln (red "✗ build failed"); return 1
  if !(← emitDeployManifest outDir mod) then IO.eprintln (red "✗ deploy manifest validation failed"); return 1
  if outOverride.isNone then
    let bundlePaths ← clientBundlePaths outDir
    let rawBytes ← bundlePaths.foldlM (init := ByteArray.empty) fun acc p => return acc ++ (← IO.FS.readBinFile p)
    let sz ← if bundlePaths.isEmpty then pure 0 else (·.size) <$> Qed.Server.Prim.gzipCompress rawBytes
    IO.println (green s!"✓ build complete → {outDir}{if ← (outDir / "server").pathExists then s!" + native binary {outDir}/server" else ""}, {sz} bytes gzipped to the client")
  return 0

def cmdServe (args : List String) : IO UInt32 := do
  let posArgs := args.filter (· != "--dev")
  Qed.Server.Native.runStaticDir (posArgs.getD 0 distDir.toString) (parsePort (posArgs.getD 1 ((← env "PORT").getD devPort))) (args.contains "--dev")
def serveDir (dir : FilePath) (dev : Bool := false) : IO UInt32 := do
  let (cmd, args, _) ← resolveServeCmd dir ((← env "PORT").getD devPort) dev; sh cmd args
def cmdStart : IO UInt32 := do
  unless ← [distDir / "index.html", distDir / "server", distDir / "app.mjs"].anyM (·.pathExists) do IO.eprintln (red "no production build found, run `qed build` first"); return 1
  serveDir distDir
def cmdClean : IO UInt32 := do discard <| sh "lake" #["clean"]; discard <| sh "rm" #["-rf", distDir.toString, ".qed"]; IO.println (green "✓ cleaned"); return 0

private def spawnBg (cmd : String) (args : Array String) (extraEnv : Array (String × Option String) := #[]) : IO (IO.Process.Child ⟨.null, .null, .inherit⟩) :=
  IO.Process.spawn { cmd, args, env := extraEnv, stdin := .null, stdout := .null, stderr := .inherit }
private def spawnDevChild (port : String) (extraEnv : Array (String × Option String) := #[]) := do
  let (cmd, args, isNative) ← resolveServeCmd devDir port true; return (← spawnBg cmd args extraEnv, isNative)
private def waitHealthyLoop (port : UInt16) (deadline : Nat) : Nat → IO Unit
  | 0 => pure ()
  | fuel + 1 => do
      match ← Qed.Server.Native.execHttpCall "GET" s!"http://127.0.0.1:{port}/_qed/health" #[] ByteArray.empty false with
      | .ok (200, _, _) => return
      | _ => if (← IO.monoMsNow) >= deadline then return else IO.sleep 25; waitHealthyLoop port deadline fuel

private def waitDevServerHealthy (port : UInt16) (timeoutMs : Nat := 3000) : IO Unit := do
  waitHealthyLoop port ((← IO.monoMsNow) + timeoutMs) 120
private def devSkipDirs : List String := [".lake", ".qed", "dist", ".git", "toolchains", "target", "scratch", "node_modules"]
private def scanDevMtimes (qh : FilePath) : IO (Int × Int × Int) := do
  let newest (dir : FilePath) (ext : String) (sk : List String) : IO Int := do (← collect dir ext sk).foldlM (init := 0) fun best p => return max best ((← mtimeNs p).getD 0)
  return (← newest "." "lean" devSkipDirs, ← newest "." "css" devSkipDirs, ← newest (qh / "runtime") "mjs" [])
private def fileHash? (p : FilePath) : IO (Option String) := do
  if !(← p.pathExists) then return none
  try return some (shortContentHash (← IO.FS.readBinFile p)) catch _ => return none
private def publishDevStatus (outDir : FilePath) (sse? : Option Watch.DevSseServer)
    (status : String) (kind : String := "hmr") (errText : String := "") (durationMs : Nat := 0) (bumpId : Bool := true) : IO Unit := do
  let json ← writeDevStatusJson outDir status kind errText durationMs bumpId ((sse?.map (·.url)).getD "")
  if let some srv := sse? then srv.publish json

private structure DevWatchState where
  watcher?  : Option Watch.FileWatcher
  (leanMt cssMt rtMt : Int)
  curServer : IO.Process.Child ⟨.null, .null, .inherit⟩
  isNative  : Bool

private partial def devWatchLoop (qh : FilePath) (port sseUrl : String) (portNum : UInt16)
    (sse? : Option Watch.DevSseServer) (devEnv : Array (String × Option String)) (st : DevWatchState) : IO UInt32 := do
  let (st, leanChg, cssChg, rtChg) ← match st.watcher? with
    | some w => let ev ← w.wait 1000; if ev.error then w.close; pure ({ st with watcher? := none }, false, false, false) else pure (st, ev.lean, ev.css, ev.runtime)
    | none =>
        IO.sleep 120; let (cL, cC, cR) ← scanDevMtimes qh
        if cL > st.leanMt then pure ({ st with leanMt := cL }, true, false, false)
        else if cC > st.cssMt then pure ({ st with cssMt := cC }, false, true, false)
        else if cR > st.rtMt then pure ({ st with rtMt := cR }, false, false, true)
        else pure (st, false, false, false)
  let tStart ← IO.monoMsNow
  let finishOk (kind msg : String) (post : IO Unit := pure ()) : IO Unit := do
    let ms := (← IO.monoMsNow) - tStart; publishDevStatus devDir sse? "ok" kind "" ms true; post; IO.println (green s!"✓ {msg}{ms}ms)")
  let cssMeta (_ : Unit) := do loadCssMeta (".qed" / "gen" / (← jsRoot) / "css_meta.txt")
  let st ← if leanChg then
      step "change detected, rebuilding"; clearLastBuildError; publishDevStatus devDir sse? "building" "hmr" "" 0 false
      let (prevApp, prevCss, prevSrv) := (← fileHash? (devDir / "app.mjs"), ← fileHash? (devDir / "styles.css"), ← mtimeNs (devDir / "server"))
      if ← buildJs devDir (prod := false) (fastClientDev := true) (sourceMap := true) (sseUrl := sseUrl) then
        let nowNative ← (devDir / "server").pathExists
        let srvChanged ← orB (st.isNative != nowNative) (andB nowNative ((prevSrv != ·) <$> mtimeNs (devDir / "server")))
        let st ← if srvChanged then
            st.curServer.kill; discard <| st.curServer.wait
            let (restarted, nat) ← spawnDevChild port devEnv; waitDevServerHealthy portNum
            pure { st with curServer := restarted, isNative := nat }
          else pure st
        let isCss ← andB (!srvChanged) (do if prevApp == (← fileHash? (devDir / "app.mjs")) then pure (prevCss != (← fileHash? (devDir / "styles.css"))) else pure false)
        finishOk (if isCss then "css" else "hmr") s!"reloaded ({if isCss then "css" else "hmr"}, " (do if ← isInRepo then discard effectsCovered)
        pure st
      else publishDevStatus devDir sse? "error" "hmr" (← getLastBuildError) ((← IO.monoMsNow) - tStart) false; IO.eprintln (red "✗ build failed, fix and save again"); pure st
    else if cssChg then
      if let some (_, sheets) ← cssMeta () then copyLocalStylesheets devDir sheets
      finishOk "css" "styles updated ("; pure st
    else if rtChg then
      step "runtime change detected, reloading"; let (hasCss, sheets) := (← cssMeta ()).getD (false, [])
      writeClientShell devDir (prod := false) hasCss sheets (sseUrl := sseUrl); finishOk "full" "reloaded runtime ("; pure st
    else pure st
  devWatchLoop qh port sseUrl portNum sse? devEnv st

def cmdDev : IO UInt32 := do
  IO.FS.createDirAll devDir; let (qh, mod) := (← frameworkHome, ← jsRoot)
  let sse? := (← Watch.DevSseServer.start (parsePort ((← env "QED_DEV_SSE_PORT").getD "0") 0)).toOption
  let sseUrl := (sse?.map (·.url)).getD ""
  let initWatcher? := (← Watch.FileWatcher.open "." (qh / "runtime").toString devSkipDirs.toArray).toOption
  let (initLeanMt, initCssMt, initRtMt) ← if initWatcher?.isSome then pure (0, 0, 0) else scanDevMtimes qh
  let t0 ← IO.monoMsNow; step "initial build"; clearLastBuildError
  let initOk ← buildJs devDir (prod := false) (fastClientDev := true) (sourceMap := true) (sseUrl := sseUrl)
  let elapsed := (← IO.monoMsNow) - t0
  let (devEnv, devAuthNote) ← if initOk then
      discard <| emitDeployManifest devDir mod
      let auth ← if ← deployManifestHasAuth devDir then
          if (← env "QED_AUTH_ISSUER").isNone then
            let authPort ← Qed.Server.Prim.freePort; discard <| spawnBg (← IO.appPath).toString #["dev-auth", toString authPort.toNat]; waitDevServerHealthy authPort
            let issUrl := s!"http://127.0.0.1:{authPort.toNat}"; pure (#[("QED_AUTH_ISSUER", some issUrl)], s!" + dev-auth ({issUrl})")
          else pure (#[], "")
        else pure (#[], "")
      publishDevStatus devDir sse? "ok" "hmr" "" elapsed true; pure auth
    else publishDevStatus devDir sse? "error" "hmr" (← getLastBuildError) elapsed true; IO.eprintln (red "initial build failed, fix the error and save; dev will rebuild"); pure (#[], "")
  let port := (← env "PORT").getD devPort; let portNum := parsePort port; let (initServer, initNative) ← spawnDevChild port devEnv
  let st : DevWatchState := { watcher? := initWatcher?, leanMt := initLeanMt, cssMt := initCssMt, rtMt := initRtMt, curServer := initServer, isNative := initNative }
  waitDevServerHealthy portNum
  let watchTag := match st.watcher?, sse? with | some _, some _ => "OS watch + SSE push" | some _, none => "OS watch" | none, some _ => "SSE push" | none, none => "watching"
  IO.println (green s!"\nqed dev → http://localhost:{port}{if st.isNative then "   (Native + SSR + HMR)" else "   (HMR)"}{devAuthNote}   ({watchTag}; Ctrl-C to stop)\n")
  devWatchLoop qh port sseUrl portNum sse? devEnv st

end Qed.Cli
