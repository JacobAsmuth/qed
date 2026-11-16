import Cli.Common

open System (FilePath)

namespace Qed.Cli

def grepForbidden : IO Bool := do
  let all ← collect "." "lean" [".lake", ".qed", "dist", "toolchains", "node_modules", ".git", "scripts", "Cli"]
  let files := all.filter (fun p => p.fileName != some "Cli.lean")
  let bad := ["sorry", "admit", "native_decide"]
  let mut clean := true
  for f in files do
    for line in (← IO.FS.readFile f).splitOn "\n" do
      let isPolicy := line.contains "never emit" || line.contains "fails to compile"
      if !isPolicy && bad.any (line.contains ·) then
        IO.eprintln (red s!"  forbidden tactic in {f}: {line.trimmed}")
        clean := false
  return clean

def axiomClean : IO Bool := do
  if !(← axiomsManifest.pathExists) then return true
  let (_, out) ← shOut "lake" #["env", "lean", "--root=.", axiomsManifest.toString]
  let clean := !out.contains "sorryAx"
    && !out.contains "Lean.ofReduceBool"
    && !out.contains "Lean.trustCompiler"
    && !out.contains "error:"
  if !clean then IO.eprint out
  return clean

def effectsCovered : IO Bool := do
  let qh ← frameworkHome
  let qedDir   := qh / "Qed"
  let hostPath := qh / "runtime" / "qed_host.mjs"
  unless (← qedDir.pathExists) && (← hostPath.pathExists) do return true
  let leanFiles ← collect qedDir "lean"
  let mut qedSrc := ""
  for f in leanFiles do
    qedSrc := qedSrc ++ "\n" ++ (← IO.FS.readFile f)
  let host ← IO.FS.readFile hostPath
  let after (marker close src : String) : List String :=
    match src.splitOn marker with
    | _ :: rest => rest.map (fun c => (c.splitOn close).headD "")
    | []        => []
  let emitted := (after ".fx \"" "\"" qedSrc) ++ (after ".fxResult \"" "\"" qedSrc)
              ++ (after "Dom.effect \"" "\"" qedSrc) ++ (after "Dom.effectResult \"" "\"" qedSrc)
  let handled := after "case '" "'" host
  let missing := emitted.filter (fun k => k != "" && !handled.contains k)
  for k in missing do
    IO.eprintln (red s!"  effect kind \"{k}\" is emitted by a Cmd but no qed_host.mjs case handles it")
  return missing.isEmpty

def kernelEnvClean : IO Bool := do
  let root ← webRoot
  if (← (FilePath.mk "Examples").pathExists) then
    if (← shQuiet "lake" #["build", "qedjs"]) != 0 then return false
    let mods := #[
      "Qed", "Qed.Driver", "Qed.Server.Native", "Qed.Proofs.DomEquiv", "Js.Backend", "Js.Proofs",
      "Examples.Bookshelf", "Examples.CloudBooks", "Examples.ServerChecks",
      "Examples.Todo", "Examples.Chat", "Examples.Signup",
      "Examples.Booking", "Examples.Users", "Examples.Local", "Examples.Effects",
      "Examples.Template", "Examples.Socket", "Examples.Live", "Examples.DomProbe",
      "Examples.JsGate", root
    ]
    return (← shQuiet "lake" (#["exe", "qedjs", "--verify-env"] ++ mods)) == 0
  else
    if (← shQuiet "lake" #["build", root, "qedjs"]) != 0 then return false
    return (← shQuiet "lake" #["exe", "qedjs", "--verify-env", root]) == 0

def externsCovered : IO Bool := do
  let rtPath ← runtimeFile "qed_rt.mjs"
  unless (← rtPath.pathExists) do return true
  let mod ← jsRoot
  let modPath := FilePath.mk ((mod.replace "." "/") ++ ".lean")
  let hasExamples ← (FilePath.mk "Examples").pathExists
  let mut mods : Array String := #[]
  let mut entries : Array String := #[]
  if ← modPath.pathExists then
    if !hasExamples && mod != (← webRoot) then
      if (← shQuiet "lake" #["build", mod]) != 0 then return false
    match ← fullstackAppName mod with
    | some fsName =>
        mods := #[mod, "Qed.Driver"]
        entries := #[s!"{fsName}.clientApp"] ++ driverEntries.filter (!·.startsWith "main:")
    | none =>
        mods := #[mod]
        entries := driverEntries ++
          (match ← ssrAppName mod with | some a => #[s!"{a}:app", "Qed.App.ssrStep:ssrStep"] | none => #[])
  if hasExamples then
    mods := mods.push "Examples.JsGate"
    entries := entries ++ #["JsGate.run", "JsGate.counts", "JsGate.probeCount", "JsGate.names"]
  if entries.isEmpty then return true
  return (← shQuiet "lake" (#["exe", "qedjs", "--check-externs", rtPath.toString] ++ mods ++ #["--"] ++ entries)) == 0

def verify : IO Bool := do
  step "verifying proofs & axioms"
  if (← shQuiet "lake" #["build"]) != 0 then return false
  if (← (FilePath.mk "Examples").pathExists) then
    if (← shQuiet "lake" #["build", "Examples"]) != 0 then return false
  let ok1 ← grepForbidden
  let ok2 ← axiomClean
  let ok3 ← kernelEnvClean
  let ok4 ← effectsCovered
  let ok5 ← if ok3 then externsCovered else pure false
  return ok1 && ok2 && ok3 && ok4 && ok5

def cmdCheck : IO UInt32 := do
  if (← verify) then
    IO.println (green "✓ verified"); return 0
  else IO.eprintln (red "✗ verification failed"); return 1

end Qed.Cli
