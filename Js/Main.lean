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

private def parseRtFlag : List String → Except String (Option String × List String)
  | [] => .ok (none, [])
  | ["--rt"] => .error "missing argument for `--rt`"
  | "--rt" :: path :: rest => do
      let (_, rem) ← parseRtFlag rest
      return (some path, rem)
  | a :: rest => do
      let (rt, rem) ← parseRtFlag rest
      return (rt, a :: rem)

private def checkExternsAgainstRt (rtPath : String) (externs : List String) : IO Unit := do
  let rtSrc ← IO.FS.readFile rtPath
  match Js.verifyRtExterns rtSrc externs with
  | .ok ()   => pure ()
  | .error e => throw (IO.userError e)

def main (args : List String) : IO Unit := do
  match args with
  | "--verify-env" :: mods =>
    if mods.isEmpty then
      throw (IO.userError "usage: qedjs --verify-env <module>…")
    Lean.initSearchPath (← Lean.findSysroot)
    let tryImport (ms : List String) : IO (Option Environment) := do
      let imports := ms.map fun m => ({ module := m.toName } : Import)
      try some <$> importModules imports.toArray {} (trustLevel := 1024)
      catch _ => return none
    let verifyEnvOrThrow (env : Environment) : IO Nat :=
      match Js.verifyProjectEnv env with
      | .ok n    => return n
      | .error e => throw (IO.userError e)
    let total ← match ← tryImport mods with
      | some env => verifyEnvOrThrow env
      | none =>
          let mut sum := 0
          for m in mods do
            let env ← importModules #[{ module := m.toName }] {} (trustLevel := 1024)
            sum := sum + (← verifyEnvOrThrow env)
          pure sum
    IO.println s!"kernel-verified {total} declarations across {mods.length} root module(s)"
  | "--check-externs" :: rtPath :: rest =>
    let (mods, entryArgs) := splitDashes rest
    if mods.isEmpty || entryArgs.isEmpty then
      throw (IO.userError "usage: qedjs --check-externs <rt.mjs> <module>… -- <decl>[:<export>]…")
    let entries := entryArgs.map parseEntry
    Lean.initSearchPath (← Lean.findSysroot)
    let imports := mods.map fun m => ({ module := m.toName } : Import)
    let env ← importModules imports.toArray {} (trustLevel := 1024)
    match Js.collectProgramExterns env (entries.map (·.1)) with
    | .ok (_, _, externs) => checkExternsAgainstRt rtPath externs
    | .error e => throw (IO.userError e)
  | _ =>
    let min := args.contains "--min"
    let (rt?, cleanArgs) ← match parseRtFlag (args.filter (· ≠ "--min")) with
      | .ok v    => pure v
      | .error e => throw (IO.userError e)
    let (head, rest) := splitDashes cleanArgs
    match head with
    | out :: mods =>
      let entries := rest.map parseEntry
      if entries.isEmpty then throw (IO.userError "no entry decls given (after `--`)")
      Lean.initSearchPath (← Lean.findSysroot)
      let imports := mods.map fun m => ({ module := m.toName } : Import)
      let env ← importModules imports.toArray {} (trustLevel := 1024)
      match Js.emitProgramWithExterns env entries min with
      | .ok (js, externs) =>
          if let some rtPath := rt? then
            checkExternsAgainstRt rtPath externs
          let p : System.FilePath := out
          if let some dir := p.parent then IO.FS.createDirAll dir
          IO.FS.writeFile p js
          IO.println s!"wrote {out} ({js.length} bytes)"
      | .error e => throw (IO.userError e)
    | [] => throw (IO.userError "usage: qedjs [--min] [--rt <rt.mjs>] <out.mjs> <module>… -- <decl>[:<export>]…")
