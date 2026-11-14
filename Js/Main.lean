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
  | _ =>
    let min := args.contains "--min"
    let (head, rest) := splitDashes (args.filter (· ≠ "--min"))
    match head with
    | out :: mods =>
      let entries := rest.map parseEntry
      if entries.isEmpty then throw (IO.userError "no entry decls given (after `--`)")
      Lean.initSearchPath (← Lean.findSysroot)
      let imports := mods.map fun m => ({ module := m.toName } : Import)
      let env ← importModules imports.toArray {} (trustLevel := 1024)
      match Js.emitProgram env entries min with
      | .ok js =>
          let p : System.FilePath := out
          if let some dir := p.parent then IO.FS.createDirAll dir
          IO.FS.writeFile p js
          IO.println s!"wrote {out} ({js.length} bytes)"
      | .error e => throw (IO.userError e)
    | [] => throw (IO.userError "usage: qedjs <out.mjs> <module>… -- <decl>[:<export>]…")
