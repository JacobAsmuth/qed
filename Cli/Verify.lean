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
  let after (marker close src : String) : List String :=
    match src.splitOn marker with
    | _ :: rest => rest.map (fun c => (c.splitOn close).headD "")
    | []        => []
  let mut emitted : List String := []
  for f in leanFiles do
    let src ← IO.FS.readFile f
    for marker in [".fx \"", ".fxResult \"", "Dom.effect \"", "Dom.effectResult \""] do
      for k in after marker "\"" src do
        if k != "" && !emitted.contains k then
          emitted := k :: emitted
  let host ← IO.FS.readFile hostPath
  let handled := after "case '" "'" host
  let missing := emitted.filter (fun k => !handled.contains k)
  for k in missing do
    IO.eprintln (red s!"  effect kind \"{k}\" is emitted by a Cmd but no qed_host.mjs case handles it")
  return missing.isEmpty

def kernelEnvClean (q? : Option QedjsEnv := none) : IO Bool := do
  let root ← webRoot
  let hasExamples ← (FilePath.mk "Examples").pathExists
  let some q ← (match q? with | some e => pure (some e) | none => resolveQedjsEnv (needBuild := !hasExamples)) | return false
  if hasExamples then
    let mods := #[
      "Qed", "Qed.Driver", "Qed.Server.Native", "Qed.Proofs.DomEquiv", "Js.Backend", "Js.Proofs",
      "Examples.Bookshelf", "Examples.CloudBooks", "Examples.ServerChecks",
      "Examples.Todo", "Examples.Chat", "Examples.Signup",
      "Examples.Booking", "Examples.Users", "Examples.Local", "Examples.Effects",
      "Examples.Template", "Examples.Socket", "Examples.Live", "Examples.DomProbe",
      "Examples.JsGate", root
    ]
    q.run (#["--verify-env"] ++ mods) (quiet := true)
  else
    if (← shQuiet "lake" #["build", root]) != 0 then return false
    q.run #["--verify-env", "--skip-qed", root] (quiet := true)

def externsCovered (q? : Option QedjsEnv := none) : IO Bool := do
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
  let some q ← (match q? with | some e => pure (some e) | none => resolveQedjsEnv) | return false
  q.run (#["--check-externs", rtPath.toString] ++ mods ++ #["--"] ++ entries) (quiet := true)

def verify (checkExterns : Bool := true) : IO Bool := do
  step "verifying proofs & axioms"
  let hasExamples ← (FilePath.mk "Examples").pathExists
  if hasExamples then
    if (← shQuiet "lake" #["build", "Qed", "QedServer", "QedProofs", "JsProofs", "qedjs", "Examples"]) != 0 then return false
  else
    let root ← webRoot
    if (← shQuiet "lake" #["build", root]) != 0 then return false
  let tGrep ← IO.asTask grepForbidden
  let tAxiom ← IO.asTask axiomClean
  let tEff ← if hasExamples then IO.asTask effectsCovered else IO.asTask (pure true)
  let q? ← resolveQedjsEnv (needBuild := false)
  let ok3 ← kernelEnvClean q?
  let ok5 ← if checkExterns && ok3 then externsCovered q? else pure ok3
  let ok1 := (← IO.wait tGrep).toOption.getD false
  let ok2 := (← IO.wait tAxiom).toOption.getD false
  let ok4 := (← IO.wait tEff).toOption.getD false
  return ok1 && ok2 && ok3 && ok4 && ok5

def cmdCheck : IO UInt32 := do
  if (← verify (checkExterns := true)) then
    IO.println (green "✓ verified"); return 0
  else IO.eprintln (red "✗ verification failed"); return 1

end Qed.Cli
