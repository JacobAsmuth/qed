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

private def checkExternsAgainstRt (rtPath : String) (externs : List String) : IO Unit := do
  orThrow (Js.verifyRtExterns (← IO.FS.readFile rtPath) externs)

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  match args with
  | "--verify-env" :: mods =>
    if mods.isEmpty then
      throw (IO.userError "usage: qedjs --verify-env <module>…")
    let tryImport (ms : List String) : IO (Option Environment) :=
      (some <$> loadEnv ms) <|> return none
    let total ← match ← tryImport mods with
      | some env => orThrow (Js.verifyProjectEnv env)
      | none => mods.foldlM (fun sum m => return sum + (← orThrow (Js.verifyProjectEnv (← loadEnv [m])))) 0
    IO.println s!"kernel-verified {total} declarations across {mods.length} root module(s)"
  | "--check-externs" :: rtPath :: rest =>
    let (mods, entryArgs) := splitDashes rest
    if mods.isEmpty || entryArgs.isEmpty then
      throw (IO.userError "usage: qedjs --check-externs <rt.mjs> <module>… -- <decl>[:<export>]…")
    let (_, _, externs) ← orThrow (Js.collectProgramExterns (← loadEnv mods) (entryArgs.map (parseEntry · |>.1)))
    checkExternsAgainstRt rtPath externs
  | _ =>
    let min := args.contains "--min"
    let (rt?, cleanArgs) ← orThrow (parseRtFlag (args.filter (· ≠ "--min")))
    let (head, rest) := splitDashes cleanArgs
    match head with
    | out :: mods =>
      let entries := rest.map parseEntry
      if entries.isEmpty then throw (IO.userError "no entry decls given (after `--`)")
      let (js, externs) ← orThrow (Js.emitProgramWithExterns (← loadEnv mods) entries min)
      if let some rtPath := rt? then checkExternsAgainstRt rtPath externs
      let p : System.FilePath := out
      if let some dir := p.parent then IO.FS.createDirAll dir
      IO.FS.writeFile p js
      IO.println s!"wrote {out} ({js.length} bytes)"
    | [] => throw (IO.userError "usage: qedjs [--min] [--rt <rt.mjs>] <out.mjs> <module>… -- <decl>[:<export>]…")
