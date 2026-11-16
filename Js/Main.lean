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

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  match args with
  | "--verify-env" :: rest =>
    let skipFw := rest.contains "--skip-qed"
    let mods := rest.filter (· ≠ "--skip-qed")
    if mods.isEmpty then
      throw (IO.userError "usage: qedjs --verify-env [--skip-qed] <module>…")
    let tryImport (ms : List String) : IO (Option Environment) :=
      (some <$> loadEnv ms) <|> return none
    let total ← match ← tryImport mods with
      | some env => orThrow (Js.verifyProjectEnv env skipFw)
      | none => mods.foldlM (fun sum m => return sum + (← orThrow (Js.verifyProjectEnv (← loadEnv [m]) skipFw))) 0
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
