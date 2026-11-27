import Js.Backend
import Qed.Deploy
import Qed.Cloud.Elab
import Qed.Cloud.GcpApi
open Lean

def parseEntry (s : String) : Name × String :=
  match s.splitOn ":" with | [d] => (d.toName, d) | [d, e] => (d.toName, e) | _ => (s.toName, s)

def splitDashes : List String → List String × List String
  | [] => ([], []) | "--" :: rest => ([], rest) | a :: rest => let (h, t) := splitDashes rest; (a :: h, t)

private unsafe def enableInitExecUnsafe : IO Unit := Lean.enableInitializersExecution
@[implemented_by enableInitExecUnsafe] private opaque enableInitExec : IO Unit

private def fail {α : Type} (msg : String) : IO α := throw (IO.userError msg)
private def orThrow {α : Type} : Except String α → IO α | .ok v => pure v | .error e => fail e

private def isStrictlyInsideDir (realDir realPath : System.FilePath) : Bool :=
  let base := realDir.toString
  realPath.toString.startsWith (if base.endsWith "/" then base else base ++ "/")

private def verifyModuleProvenance (env : Environment) : IO Unit := do
  let sysLibReal ← IO.FS.realPath ((← Lean.findSysroot) / "lib" / "lean")
  let mut fwRoot? : Option System.FilePath := none
  let checkOlean (modName : Name) (kind : String) (root : System.FilePath) (label : String) : IO Unit := do
    let oleanReal ← IO.FS.realPath (← Lean.findOLean modName)
    if !isStrictlyInsideDir root oleanReal then
      fail s!"module provenance gate: {kind} module `{modName}` resolved to `{oleanReal}` outside {label} `{root}`"
  for modName in env.header.moduleNames do
    if Js.isToolchainModule modName then checkOlean modName "toolchain" sysLibReal "Lean sysroot"
    else if Js.isFrameworkModule modName then
      let fwRoot ← match fwRoot? with
        | some r => pure r
        | none =>
            let appReal ← IO.FS.realPath (← IO.appPath)
            let some buildDir := appReal.parent.bind (·.parent) | fail s!"module provenance gate: cannot resolve Qed build root from `{appReal}`"
            let cand := buildDir / "lib" / "lean"
            if !(← (cand / "Qed.olean").pathExists) then fail s!"module provenance gate: missing canonical `Qed.olean` under `{cand}`"
            let r ← IO.FS.realPath cand; fwRoot? := some r; pure r
      checkOlean modName "framework" fwRoot "Qed library"

private def loadEnv (mods : List String) (loadExts : Bool := false) : IO Environment := do
  if loadExts then enableInitExec
  let env ← importModules (mods.map fun m => ({ module := m.toName } : Import)).toArray {} (trustLevel := 1024) (leakEnv := true) (loadExts := loadExts)
  verifyModuleProvenance env; return env

private structure JsCliFlags where
  min : Bool := false
  sourceMap : Bool := false
  rt? : Option String := none
  css? : Option (String × String) := none
  assetsDir? : Option String := none
  deployName? : Option String := none

private def parseJsFlags : List String → JsCliFlags → Except String (JsCliFlags × List String)
  | [], f => .ok (f, [])
  | "--min" :: r, f => parseJsFlags r { f with min := true }
  | "--sourcemap" :: r, f => parseJsFlags r { f with sourceMap := true }
  | "--rt" :: p :: r, f => parseJsFlags r { f with rt? := some p }
  | "--assets-dir" :: d :: r, f => parseJsFlags r { f with assetsDir? := some d }
  | "--deploy" :: n :: r, f => parseJsFlags r { f with deployName? := some n }
  | "--css" :: cp :: ad :: r, f => parseJsFlags r { f with css? := some (cp, ad) }
  | ["--css"], _ | ["--css", _], _ => .error "missing arguments for `--css <out.css> <appDecl>`"
  | [a], f => if a == "--rt" || a == "--assets-dir" || a == "--deploy" then .error s!"missing argument for `{a}`" else .ok (f, [a])
  | a :: r, f => do let (f', rem) ← parseJsFlags r f; return (f', a :: rem)

private def writeFileMkdir (path : System.FilePath) (content : String) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path content

private def writeJsBundle (env : Environment) (avail? : Option (Std.HashSet String))
    (outPath : String) (entryArgs : List String) (min sourceMap : Bool) : IO Unit := do
  let entries := entryArgs.map parseEntry
  if entries.isEmpty then fail "no entry decls given (after `--`)"
  let p : System.FilePath := outPath; let fileName := p.fileName.getD "app.mjs"; let mapName := fileName ++ ".map"
  let (js, smJson, externs) ← orThrow <| Js.emitProgramWithSourceMap env entries min
    (if sourceMap then fileName else "") (if sourceMap then some mapName else none)
  if let some avail := avail? then orThrow (Js.checkRtExterns avail externs)
  writeFileMkdir p js
  let mapNote ← if sourceMap then IO.FS.writeFile (System.FilePath.mk (outPath ++ ".map")) smJson; pure s!" + {mapName} ({smJson.length} bytes)" else pure ""
  IO.println s!"wrote {outPath} ({js.length} bytes){mapNote}"

private def tryImport (mods : List String) : IO (Option Environment) := (some <$> loadEnv mods) <|> pure none

private partial def verifyModBatch (mods : List String) (skipFw : Bool) : IO Nat := do
  match mods with
  | [] => pure 0
  | [m] => orThrow (Js.verifyProjectEnv (← loadEnv [m]) skipFw)
  | _ => if let some env ← tryImport mods then orThrow (Js.verifyProjectEnv env skipFw) else
      let mid := mods.length / 2
      let tL ← IO.asTask (verifyModBatch (mods.take mid) skipFw); let tR ← IO.asTask (verifyModBatch (mods.drop mid) skipFw)
      return (← IO.ofExcept (← IO.wait tL)) + (← IO.ofExcept (← IO.wait tR))

private unsafe def evalCssForAppUnsafe (env : Environment) (appName : Name) : IO (String × List String) := do
  let m : MetaM (String × List String) := do
    let appExpr := Lean.mkConst appName
    let cssStr ← Meta.evalExpr String (Lean.mkConst ``String) (← Meta.mkAppM `Qed.renderStyleSheet #[← Meta.mkProjection appExpr `styles])
    let sheets ← try
        Meta.evalExpr (List String) (Lean.mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``String))
          (← Meta.mkProjection appExpr `stylesheets)
      catch _ => pure []
    return (cssStr, sheets)
  return (← m.toIO { fileName := "<qedjs>", fileMap := default } { env }).1

@[implemented_by evalCssForAppUnsafe]
private opaque evalCssForApp (env : Environment) (appName : Name) : IO (String × List String)

private def emitCssForApp (env : Environment) (outPath : String) (appName : Name) : IO Unit := do
  let (cssStr, sheets) ← evalCssForApp env appName; let p : System.FilePath := outPath
  if !cssStr.isEmpty then writeFileMkdir p cssStr; IO.println "HAS_CSS:1"
  else
    if ← p.pathExists then try IO.FS.removeFile p catch _ => pure ()
    IO.println "HAS_CSS:0"
  for s in sheets do let t := s.trimAscii.toString; if !t.isEmpty then IO.println s!"STYLESHEET:{t}"

private def guessDeployAssetMime (name : String) : Option String :=
  #[(".mjs", "text/javascript; charset=utf-8"), (".js", "text/javascript; charset=utf-8"),
    (".css", "text/css; charset=utf-8"), (".html", "text/html; charset=utf-8"),
    (".map", "application/json; charset=utf-8")].findSome? fun (ext, m) => if name.endsWith ext then some m else none

private partial def scanDeployAssetsRec (realDir curDir : System.FilePath) (relPrefix : String)
    (acc : Array Qed.Deploy.DeployAssetManifest) : IO (Array Qed.Deploy.DeployAssetManifest) := do
  let mut out := acc
  let checkReal (p : System.FilePath) (err : String) : IO System.FilePath := do
    let r ← IO.FS.realPath p; if !isStrictlyInsideDir realDir r then fail err else pure r
  for entry in (← curDir.readDir) do
    let name := entry.fileName; let relPath := if relPrefix.isEmpty then name else s!"{relPrefix}/{name}"
    let smd ← entry.path.symlinkMetadata
    if smd.type == .symlink then
      let reject ← if (guessDeployAssetMime name).isSome then pure true else try entry.path.isDir catch _ => pure false
      if reject then fail s!"asset `{relPath}` is a symlink (rejected)"
    else if smd.type == .dir then
      out ← scanDeployAssetsRec realDir (← checkReal entry.path s!"asset directory `{relPath}` resolves outside `{realDir}`") relPath out
    else if smd.type == .file then
      if let some mime := guessDeployAssetMime name then
        discard <| checkReal entry.path s!"asset `{relPath}` resolves outside `{realDir}` (symlink escape rejected)"
        out := out.push { path := "/" ++ relPath, mime, bytes := smd.byteSize.toNat }
  return out

private def findDeploySpec (env : Environment) (rootMod : String) (deployName? : Option String := none) :
    Except String (Option Qed.Cloud.DeploySpec) :=
  let reg : List (Name × Qed.Cloud.DeployInfo) := (Qed.Cloud.deployRegistry.getState env).toList
  let inRoot := (env.getModuleIdx? rootMod.toName).elim [] fun idx => reg.filter fun (_, di) => env.getModuleIdxFor? di.specConst == some idx
  match deployName? with
  | some want =>
      let matchesWant (p : Name × Qed.Cloud.DeployInfo) := p.1.toString == want || p.2.spec.name == want
      ((inRoot.find? matchesWant).orElse fun _ => reg.find? matchesWant).elim
        (.error s!"unknown `deploy` target `{want}` in `{rootMod}`") (fun (_, di) => .ok (some di.spec))
  | none => match inRoot with
      | [] => .ok none | [(_, di)] => .ok (some di.spec)
      | many => .error s!"multiple `deploy` blocks in `{rootMod}` ({String.intercalate ", " (many.map fun (_, di) => di.spec.name)}); pass `--deploy <Name>` to select one"

private def resolveDeployServer (env : Environment) (deploy? : Option Qed.Cloud.DeploySpec) : Option Name :=
  deploy?.bind fun d =>
    ((Qed.Server.fullstackRegistry.getState env).toList.findSome? fun (n, fi) =>
      if n.toString == d.appName || fi.fullstackName.toString == d.appName then some fi.serverName else none).orElse
    fun _ => (Qed.serverRegistry.getState env).toList.findSome? fun (n, si) =>
      if n.toString == d.appName || si.serverName.toString == d.appName then some si.serverName else none

private def toDeployDbManifest (di : Qed.Server.DatabaseInfo) : Qed.Deploy.DeployDbManifest := {
  shortName := di.shortName, secrets := di.secrets.toList, hasDevFallback := di.hasDevFallback,
  isManaged := di.isManaged, envSpecs := di.envSpecs,
  tables := di.tables.toList.map fun t => {
    tableName := t.tableName, hasReadPolicy := t.hasReadPolicy, hasInsertPolicy := t.hasInsertPolicy,
    hasUpdatePolicy := t.hasUpdatePolicy, hasDeletePolicy := t.hasDeletePolicy, hasTransInv := t.hasTransInv,
    columns := t.columns.toList.map fun c => {
      name := c.name, isPrimaryKey := c.isPrimaryKey, isImmutable := c.isImmutable,
      isUnique := c.isUnique, isNullable := c.isNullable, refs? := c.refs? } } }

private def toDeployServerManifest (si : Qed.ServerInfo) : Qed.Deploy.DeployServerManifest := {
  name := si.serverName.toString, shortName := si.shortName, hasState := si.hasState,
  ownSecrets := si.ownSecrets.toList, hasHttpRoutes := si.hasHttpRoutes,
  methods := si.methods.toList.map fun mt => { name := mt.name, isReadOnly := mt.isReadOnly, requiresAuth := mt.requiresAuth },
  channels := si.channels.toList, jobs := si.jobs.toList }

private def extractFromEnv (env : Environment) (rootMod : String)
    (targetServer? : Option Name := none) (explicitTarget : Bool := false) : Qed.Deploy.DeployManifest :=
  let (srvReg, dbReg, authReg, extReg) :=
    (Qed.serverRegistry.getState env, Qed.Server.databaseRegistry.getState env, Qed.Server.authRegistry.getState env, Qed.Server.externalRegistry.getState env)
  let modIdx? := env.getModuleIdx? rootMod.toName
  let inRootMod (c : Name) : Bool := match modIdx?, env.getModuleIdxFor? c with
    | some ri, some di => ri == di | _, _ => rootMod.isEmpty || c.toString == rootMod || c.toString.startsWith (rootMod ++ ".")
  let server? : Option Qed.ServerInfo := match targetServer? with
    | some srvName => srvReg.find? srvName
    | none => if explicitTarget then none else (srvReg.toList.find? fun (_, si) => inRootMod (si.serverName ++ `dispatchM)).map Prod.snd
  let databases : List Qed.Server.DatabaseInfo := match server? with
    | some si => dbReg.toList.filterMap fun (_, di) => if si.databases.contains di.configConst then some di else none
    | none => if explicitTarget then [] else dbReg.toList.filterMap fun (_, di) => if inRootMod di.configConst then some di else none
  let authInfo? : Option Qed.Server.AuthInfo := match server? with
    | some si => si.authName?.bind authReg.find?
    | none => if explicitTarget then none else (authReg.toList.find? fun (_, ai) => inRootMod ai.configConst).map Prod.snd
  let rawEgress : List String := match server? with
    | some si => si.externalServices.toList.map Prod.snd
    | none => if explicitTarget then [] else extReg.toList.filterMap fun (_, ei) => if inRootMod (ei.serviceName ++ `_qed_external_marker) then some ei.baseOrigin else none
  { version := 1, rootModule := rootMod, mode := if server?.isSome then "fullstack" else "standalone",
    secrets := ((server?.map (·.secrets.toList)).getD [] ++ databases.flatMap (·.secrets.toList) ++ (authInfo?.map (·.secrets.toList)).getD []).eraseDups,
    envVars := (server?.map (·.envVars.toList)).getD [],
    egress := (rawEgress.filter fun o => !o.isEmpty && Qed.Deploy.isValidEgressOrigin o).eraseDups,
    databases := databases.map toDeployDbManifest, auth? := authInfo?.map (·.spec), server? := server?.map toDeployServerManifest }

private def prepareDeployManifest (rootMod : String) (rest : List String) :
    IO (Qed.Deploy.DeployManifest × Option Qed.Cloud.DeploySpec) := do
  let (flags, mods) ← orThrow (parseJsFlags rest {}); let targetMods := if mods.isEmpty then [rootMod] else mods
  discard <| orThrow (Js.verifyProjectEnv (← loadEnv targetMods (loadExts := false)) (skipFramework := false))
  let env ← loadEnv targetMods (loadExts := true)
  let assets ← flags.assetsDir?.elim (pure []) fun d => do
    let dir := System.FilePath.mk d
    if !(← dir.pathExists) then pure [] else
      let rd ← IO.FS.realPath dir; return ((← scanDeployAssetsRec rd rd "" #[]).qsort (·.path < ·.path)).toList
  let deploy? ← orThrow (findDeploySpec env rootMod flags.deployName?)
  let manifest : Qed.Deploy.DeployManifest := {
    extractFromEnv env rootMod (resolveDeployServer env deploy?) (explicitTarget := deploy?.isSome) with deploy?, assets
  }
  orThrow manifest.validate; return (manifest, deploy?)

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  match args with
  | "--emit-deploy-manifest" :: outJson :: rootMod :: rest =>
    let (m, _) ← prepareDeployManifest rootMod rest; writeFileMkdir outJson (m.render ++ "\n")
    IO.println s!"wrote {outJson} (mode={m.mode}, secrets={m.secrets.length}, dbs={m.databases.length}, egress={m.egress.length}, auth={m.auth?.isSome})"
  | "--emit-cloud-plan" :: outJson :: rootMod :: envStr :: prStr :: prodProject :: nonProdProject :: tenantStr :: appStr :: buildHash :: rest =>
    let key ← orThrow (Qed.Cloud.DeployKey.mkCheckedStr prodProject nonProdProject tenantStr appStr envStr prStr)
    let (manifest, deploy?) ← prepareDeployManifest rootMod rest
    let spec := deploy?.getD { name := rootMod, appName := rootMod }; orThrow spec.validate
    let plan := Qed.Cloud.compileInfra key buildHash spec manifest; let rendered := Qed.Json.render plan.toJson
    if outJson == "-" then IO.println rendered
    else writeFileMkdir outJson (rendered ++ "\n"); IO.println s!"wrote {outJson} (service={plan.cloudRunName}, regions={plan.regions.length}, secrets={plan.secretNames.length})"
  | "--verify-env" :: rest =>
    let skipFw := rest.contains "--skip-qed"; let mods := rest.filter (· ≠ "--skip-qed")
    if mods.isEmpty then fail "usage: qedjs --verify-env [--skip-qed] <module>…"
    let total ← match ← tryImport mods with
      | some env => orThrow (Js.verifyProjectEnv env skipFw)
      | none =>
          let (fwMods, userMods) := mods.partition fun m => Js.isFrameworkModule m.toName
          let tFw ← IO.asTask (if fwMods.isEmpty then pure 0 else verifyModBatch fwMods skipFw)
          let tUsr ← IO.asTask (verifyModBatch userMods skipFw)
          pure ((← IO.ofExcept (← IO.wait tFw)) + (← IO.ofExcept (← IO.wait tUsr)))
    IO.println s!"kernel-verified {total} declarations across {mods.length} root module(s)"
  | "--check-externs" :: rtPath :: rest =>
    let (mods, entryArgs) := splitDashes rest
    if mods.isEmpty || entryArgs.isEmpty then fail "usage: qedjs --check-externs <rt.mjs> <module>… -- <decl>[:<export>]…"
    let (_, externs) ← orThrow (Js.collectProgramExterns (← loadEnv mods) (entryArgs.map (parseEntry · |>.1)))
    orThrow (Js.checkRtExterns (Js.rtExports (← IO.FS.readFile rtPath)) externs)
  | "--check-leak-each" :: rest =>
    let (mod, decls) ← match rest with
      | m :: "--" :: ds => pure (m, ds)
      | m :: ds => pure (m, ds)
      | [] => fail "usage: qedjs --check-leak-each <module> <decl1> [<decl2> ...]"
    if decls.isEmpty then fail "usage: qedjs --check-leak-each <module> <decl1> [<decl2> ...]"
    let env ← loadEnv [mod]
    let mut failed := 0
    for decl in decls do
      match Js.collectProgramExterns env [(parseEntry decl).1] with
      | .error err =>
          let cleanErr := err.replace "\n" " "
          if err.contains "client bundle leak gate" then
            IO.println s!"PASS\t{decl}\t{cleanErr}"
          else
            IO.println s!"FAIL\t{decl}\t{cleanErr}"; failed := failed + 1
      | .ok _ =>
          IO.println s!"FAIL\t{decl}\tallowed in client bundle (not blocked by client bundle leak gate)"
          failed := failed + 1
    if failed > 0 then fail s!"leak gate check failed for {failed}/{decls.length} declaration(s) in `{mod}`"
  | _ =>
    let (flags, cleanArgs) ← orThrow (parseJsFlags args {})
    match splitDashes cleanArgs with
    | (out :: mods, rest) =>
      let env ← loadEnv mods
      let avail? ← flags.rt?.mapM fun rtPath => Js.rtExports <$> IO.FS.readFile rtPath
      writeJsBundle env avail? out rest flags.min flags.sourceMap
      if let some (cssOut, appDecl) := flags.css? then
        discard <| orThrow (Js.verifyProjectEnv env (skipFramework := false))
        try emitCssForApp env cssOut (parseEntry appDecl).1 catch _ => IO.println "HAS_CSS:0"
    | ([], _) => fail "usage: qedjs [--min] [--sourcemap] [--rt <rt.mjs>] [--css <out.css> <appDecl>] <out.mjs> <module>… -- <decl>[:<export>]…"
