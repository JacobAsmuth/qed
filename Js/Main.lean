import Js.Backend
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

private def loadEnv (mods : List String) : IO Environment := do
  let imports := mods.map fun m => ({ module := m.toName } : Import)
  importModules imports.toArray {} (trustLevel := 1024)

private def orThrow {α : Type} : Except String α → IO α
  | .ok v    => pure v
  | .error e => throw (IO.userError e)

private def parseRtFlag : List String → Except String (Option String × List String)
  | [] => .ok (none, [])
  | ["--rt"] => .error "missing argument for `--rt`"
  | "--rt" :: path :: rest => return (some path, (← parseRtFlag rest).2)
  | a :: rest => do
      let (rt, rem) ← parseRtFlag rest
      return (rt, a :: rem)

private def checkExternsAgainstRt (avail : Std.HashSet String) (externs : List String) : IO Unit := do
  let missing := externs.filter (!avail.contains ·)
  if !missing.isEmpty then
    throw (IO.userError s!"qed_rt: missing externs: {String.intercalate ", " missing}")

private def splitAlso : List String → List String × Option (String × List String)
  | [] => ([], none)
  | "--also" :: out2 :: "--" :: entries2 => ([], some (out2, entries2))
  | a :: rest =>
      let (h, also) := splitAlso rest
      (a :: h, also)

private def writeJsBundle (env : Environment) (avail? : Option (Std.HashSet String))
    (outPath : String) (entryArgs : List String) (min : Bool) : IO Unit := do
  let entries := entryArgs.map parseEntry
  if entries.isEmpty then throw (IO.userError "no entry decls given (after `--`)")
  let (js, externs) ← orThrow (Js.emitProgramWithExterns env entries min)
  if let some avail := avail? then checkExternsAgainstRt avail externs
  let p : System.FilePath := outPath
  if let some dir := p.parent then IO.FS.createDirAll dir
  IO.FS.writeFile p js
  IO.println s!"wrote {outPath} ({js.length} bytes)"

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
        let cL ← match ← IO.wait tL with | .ok n => pure n | .error e => throw e
        let cR ← match ← IO.wait tR with | .ok n => pure n | .error e => throw e
        return cL + cR

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

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  match args with
  | "--emit-css" :: outCss :: rest =>
    let (mods, entryArgs) := splitDashes rest
    if mods.isEmpty || entryArgs.isEmpty then
      throw (IO.userError "usage: qedjs --emit-css <out.css> <module>… -- <appDecl>")
    let env ← loadEnv mods
    let appName := (parseEntry entryArgs.head!).1
    emitCssForApp env outCss appName
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
          let fwTotal ← match ← IO.wait tFw with | .ok n => pure n | .error e => throw e
          let usrTotal ← match ← IO.wait tUsr with | .ok n => pure n | .error e => throw e
          pure (fwTotal + usrTotal)
    IO.println s!"kernel-verified {total} declarations across {mods.length} root module(s)"
  | "--check-externs" :: rtPath :: rest =>
    let (mods, entryArgs) := splitDashes rest
    if mods.isEmpty || entryArgs.isEmpty then
      throw (IO.userError "usage: qedjs --check-externs <rt.mjs> <module>… -- <decl>[:<export>]…")
    let (_, _, externs) ← orThrow (Js.collectProgramExterns (← loadEnv mods) (entryArgs.map (parseEntry · |>.1)))
    let avail := Js.rtExports (← IO.FS.readFile rtPath)
    checkExternsAgainstRt avail externs
  | _ =>
    let min := args.contains "--min"
    let (rt?, cleanArgs) ← orThrow (parseRtFlag (args.filter (· ≠ "--min")))
    let (head, restWithAlso) := splitDashes cleanArgs
    let (rest, also?) := splitAlso restWithAlso
    match head with
    | out :: mods =>
      let env ← loadEnv mods
      let avail? ← rt?.mapM fun rtPath => return Js.rtExports (← IO.FS.readFile rtPath)
      writeJsBundle env avail? out rest min
      if let some (out2, entries2) := also? then
        writeJsBundle env avail? out2 entries2 min
    | [] => throw (IO.userError "usage: qedjs [--min] [--rt <rt.mjs>] <out.mjs> <module>… -- <decl>[:<export>]… [--also <out2.mjs> -- <decl>…]")
