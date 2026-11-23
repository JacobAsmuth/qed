import Js.Backend
import Qed.Deploy
open Lean

def parseEntry (s : String) : Name × String :=
  match s.splitOn ":" with
  | [d]    => (d.toName, d)
  | [d, e] => (d.toName, e)
  | _      => (s.toName, s)

def splitDashes : List String → List String × List String
  | []           => ([], [])
  | "--" :: rest => ([], rest)
  | a :: rest    => let (h, t) := splitDashes rest; (a :: h, t)

private unsafe def enableInitExecUnsafe : IO Unit :=
  Lean.enableInitializersExecution

@[implemented_by enableInitExecUnsafe]
private opaque enableInitExec : IO Unit

private def loadEnv (mods : List String) (loadExts : Bool := false) : IO Environment := do
  if loadExts then enableInitExec
  let imports := mods.map fun m => ({ module := m.toName } : Import)
  importModules imports.toArray {} (trustLevel := 1024) (leakEnv := true) (loadExts := loadExts)

private def orThrow {α : Type} : Except String α → IO α
  | .ok v    => pure v
  | .error e => throw (IO.userError e)

private structure JsCliFlags where
  min : Bool := false
  sourceMap : Bool := false
  rt? : Option String := none
  css? : Option (String × String) := none
  assetsDir? : Option String := none

private def parseJsFlags : List String → JsCliFlags → Except String (JsCliFlags × List String)
  | [], f => .ok (f, [])
  | "--min" :: rest, f => parseJsFlags rest { f with min := true }
  | "--sourcemap" :: rest, f => parseJsFlags rest { f with sourceMap := true }
  | ["--rt"], _ => .error "missing argument for `--rt`"
  | "--rt" :: path :: rest, f => parseJsFlags rest { f with rt? := some path }
  | "--assets-dir" :: dir :: rest, f => parseJsFlags rest { f with assetsDir? := some dir }
  | ["--css"], _ | ["--css", _], _ => .error "missing arguments for `--css <out.css> <appDecl>`"
  | "--css" :: cssPath :: appDecl :: rest, f => parseJsFlags rest { f with css? := some (cssPath, appDecl) }
  | a :: rest, f => do let (f', rem) ← parseJsFlags rest f; return (f', a :: rem)

private def writeJsBundle (env : Environment) (avail? : Option (Std.HashSet String))
    (outPath : String) (entryArgs : List String) (min : Bool) (sourceMap : Bool := false) : IO Unit := do
  let entries := entryArgs.map parseEntry
  if entries.isEmpty then throw (IO.userError "no entry decls given (after `--`)")
  let p : System.FilePath := outPath
  if let some dir := p.parent then IO.FS.createDirAll dir
  let fileName := p.fileName.getD "app.mjs"
  let mapFileName := fileName ++ ".map"
  let (js, smJson, externs) ← orThrow <| Js.emitProgramWithSourceMap env entries min
    (if sourceMap then fileName else "") (if sourceMap then some mapFileName else none)
  if let some avail := avail? then orThrow (Js.checkRtExterns avail externs)
  IO.FS.writeFile p js
  let mapNote ← if sourceMap then
    IO.FS.writeFile (System.FilePath.mk (outPath ++ ".map")) smJson
    pure s!" + {mapFileName} ({smJson.length} bytes)"
  else pure ""
  IO.println s!"wrote {outPath} ({js.length} bytes){mapNote}"

private def tryImport (mods : List String) : IO (Option Environment) :=
  (some <$> loadEnv mods) <|> return none

private partial def verifyModBatch (mods : List String) (skipFw : Bool) : IO Nat := do
  match mods with
  | []  => return 0
  | [m] => orThrow (Js.verifyProjectEnv (← loadEnv [m]) skipFw)
  | _   =>
      if let some env ← tryImport mods then
        orThrow (Js.verifyProjectEnv env skipFw)
      else
        let mid := mods.length / 2
        let tL ← IO.asTask (verifyModBatch (mods.take mid) skipFw)
        let tR ← IO.asTask (verifyModBatch (mods.drop mid) true)
        return (← IO.ofExcept (← IO.wait tL)) + (← IO.ofExcept (← IO.wait tR))

private unsafe def evalCssForAppUnsafe (env : Environment) (appName : Name) : IO (String × List String) := do
  let m : MetaM (String × List String) := do
    let appExpr := Lean.mkConst appName
    let stylesProj ← Meta.mkProjection appExpr `styles
    let cssExpr ← Meta.mkAppM `Qed.renderStyleSheet #[stylesProj]
    let cssStr ← Meta.evalExpr String (Lean.mkConst ``String) cssExpr
    let sheets ← try
        let shProj ← Meta.mkProjection appExpr `stylesheets
        let listStrTy := Lean.mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``String)
        Meta.evalExpr (List String) listStrTy shProj
      catch _ => pure []
    return (cssStr, sheets)
  let (res, _) ← m.toIO { fileName := "<qedjs>", fileMap := default } { env }
  return res

@[implemented_by evalCssForAppUnsafe]
private opaque evalCssForApp (env : Environment) (appName : Name) : IO (String × List String)

private def emitCssForApp (env : Environment) (outPath : String) (appName : Name) : IO Unit := do
  let (cssStr, sheets) ← evalCssForApp env appName
  let p : System.FilePath := outPath
  if !cssStr.isEmpty then
    if let some dir := p.parent then IO.FS.createDirAll dir
    IO.FS.writeFile p cssStr
    IO.println s!"HAS_CSS:1"
  else
    if ← p.pathExists then try IO.FS.removeFile p catch _ => pure ()
    IO.println s!"HAS_CSS:0"
  for s in sheets do
    let t := s.trimAscii.toString
    if !t.isEmpty then
      IO.println s!"STYLESHEET:{t}"

private def guessDeployAssetMime (name : String) : Option String :=
  if name.endsWith ".mjs" || name.endsWith ".js" then some "text/javascript; charset=utf-8"
  else if name.endsWith ".css" then some "text/css; charset=utf-8"
  else if name.endsWith ".html" then some "text/html; charset=utf-8"
  else if name.endsWith ".map" then some "application/json; charset=utf-8"
  else none

private def scanDeployAssets (dir : System.FilePath) : IO (List Qed.Deploy.DeployAssetManifest) := do
  if !(← dir.pathExists) then return []
  let mut out : Array Qed.Deploy.DeployAssetManifest := #[]
  for entry in (← dir.readDir) do
    let name := entry.fileName
    if let some mime := guessDeployAssetMime name then
      let md ← entry.path.metadata
      out := out.push { path := "/" ++ name, mime, bytes := md.byteSize.toNat }
  return (out.qsort fun a b => a.path < b.path).toList

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  match args with
  | "--emit-deploy-manifest" :: outJson :: rootMod :: rest =>
    let (flags, mods) ← orThrow (parseJsFlags rest {})
    let env ← loadEnv (if mods.isEmpty then [rootMod] else mods) (loadExts := true)
    let assets ← match flags.assetsDir? with
      | some d => scanDeployAssets (System.FilePath.mk d)
      | none   => pure []
    let manifest : Qed.Deploy.DeployManifest := { Qed.Deploy.extractFromEnv env rootMod with assets }
    orThrow manifest.validate
    let p : System.FilePath := outJson
    if let some dir := p.parent then IO.FS.createDirAll dir
    IO.FS.writeFile p (manifest.render ++ "\n")
    IO.println s!"wrote {outJson} (mode={manifest.mode}, secrets={manifest.secrets.length}, dbs={manifest.databases.length}, egress={manifest.egress.length}, auth={manifest.auth?.isSome})"
  | "--verify-env" :: rest =>
    let skipFw := rest.contains "--skip-qed"
    let mods := rest.filter (· ≠ "--skip-qed")
    if mods.isEmpty then
      throw (IO.userError "usage: qedjs --verify-env [--skip-qed] <module>…")
    let total ← match ← tryImport mods with
      | some env => orThrow (Js.verifyProjectEnv env skipFw)
      | none =>
          let (fwMods, userMods) := mods.partition fun m => Js.isFrameworkModule m.toName
          let tFw ← if skipFw || fwMods.isEmpty then IO.asTask (pure 0)
            else IO.asTask (verifyModBatch fwMods false)
          let userSkipFw := skipFw || !fwMods.isEmpty
          let tUsr ← IO.asTask (verifyModBatch userMods userSkipFw)
          pure ((← IO.ofExcept (← IO.wait tFw)) + (← IO.ofExcept (← IO.wait tUsr)))
    IO.println s!"kernel-verified {total} declarations across {mods.length} root module(s)"
  | "--check-externs" :: rtPath :: rest =>
    let (mods, entryArgs) := splitDashes rest
    if mods.isEmpty || entryArgs.isEmpty then
      throw (IO.userError "usage: qedjs --check-externs <rt.mjs> <module>… -- <decl>[:<export>]…")
    let (_, externs) ← orThrow (Js.collectProgramExterns (← loadEnv mods) (entryArgs.map (parseEntry · |>.1)))
    let avail := Js.rtExports (← IO.FS.readFile rtPath)
    orThrow (Js.checkRtExterns avail externs)
  | _ =>
    let (flags, cleanArgs) ← orThrow (parseJsFlags args {})
    let (head, rest) := splitDashes cleanArgs
    match head with
    | out :: mods =>
      let env ← loadEnv mods
      let avail? ← flags.rt?.mapM fun rtPath => return Js.rtExports (← IO.FS.readFile rtPath)
      writeJsBundle env avail? out rest flags.min flags.sourceMap
      if let some (cssOut, appDecl) := flags.css? then
        try
          emitCssForApp env cssOut (parseEntry appDecl).1
        catch _ =>
          IO.println "HAS_CSS:0"
    | [] => throw (IO.userError "usage: qedjs [--min] [--sourcemap] [--rt <rt.mjs>] [--css <out.css> <appDecl>] <out.mjs> <module>… -- <decl>[:<export>]…")
