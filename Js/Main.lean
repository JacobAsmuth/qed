/-
  Js.Main — CLI front-end for the Lean-IR → JS transpiler.

  Usage:  qedjs <out.mjs> <module> [<module> …] -- <declName>[:<exportName>] …

  Imports the given modules, transpiles the reachable closure from the entry decls,
  and writes the JS module.
-/
import Js.Backend
open Lean

def parseEntry (s : String) : Name × String :=
  match s.splitOn ":" with
  | [d]    => (d.toName, d)
  | [d, e] => (d.toName, e)
  | _      => (s.toName, s)

/-- Split a list at the first `"--"` marker. -/
partial def splitDashes : List String → List String × List String
  | []           => ([], [])
  | "--" :: rest => ([], rest)
  | a :: rest    => let (h, t) := splitDashes rest; (a :: h, t)

def main (args : List String) : IO Unit := do
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
