import Cli.Common
import Std.Data.HashMap
import Std.Data.HashSet

open System (FilePath)

namespace Qed.Cli

private def isLeanIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

private def isLeanIdentCont (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

private def forbiddenTokens : List String :=
  ["sorry", "admit", "native_decide", "sorryAx"]

/-- Lexically scan a Lean source file for forbidden proof-bypass tokens (`sorry`, `admit`,
    `native_decide`, `sorryAx`), skipping line/nested-block comments, char literals, and plain
    string literals while still scanning `{...}` code expressions inside `s!"..."`, `m!"..."`,
    and `f"..."` interpolated strings. -/
def findForbiddenTokens (src : String) : Array (Nat × String) := Id.run do
  let cs := src.toList.toArray
  let n := cs.size
  let mut i := 0
  let mut line := 1
  let mut inInterpStr := false
  let mut interpBraces : Array Nat := #[]
  let mut hits : Array (Nat × String) := #[]
  while i < n do
    if inInterpStr then
      let c := cs[i]!
      if c == '\\' then
        if i + 1 < n then
          if cs[i + 1]! == '\n' then line := line + 1
          i := i + 2
        else
          i := i + 1
      else if c == '"' then
        inInterpStr := false
        i := i + 1
      else if c == '{' then
        if i + 1 < n && cs[i + 1]! == '{' then
          i := i + 2
        else
          interpBraces := interpBraces.push 0
          inInterpStr := false
          i := i + 1
      else
        if c == '\n' then line := line + 1
        i := i + 1
    else
      let c := cs[i]!
      if c == '\n' then
        line := line + 1
        i := i + 1
      else if c == '-' && i + 1 < n && cs[i + 1]! == '-' then
        i := i + 2
        while i < n && cs[i]! != '\n' do
          i := i + 1
      else if c == '/' && i + 1 < n && cs[i + 1]! == '-' then
        let mut depth := 1
        i := i + 2
        while i < n && depth > 0 do
          let ch := cs[i]!
          if ch == '\n' then
            line := line + 1
            i := i + 1
          else if ch == '/' && i + 1 < n && cs[i + 1]! == '-' then
            depth := depth + 1
            i := i + 2
          else if ch == '-' && i + 1 < n && cs[i + 1]! == '/' then
            depth := depth - 1
            i := i + 2
          else
            i := i + 1
      else if c == '{' && !interpBraces.isEmpty then
        let top := interpBraces.back!
        interpBraces := interpBraces.pop.push (top + 1)
        i := i + 1
      else if c == '}' && !interpBraces.isEmpty then
        let top := interpBraces.back!
        if top == 0 then
          interpBraces := interpBraces.pop
          inInterpStr := true
        else
          interpBraces := interpBraces.pop.push (top - 1)
        i := i + 1
      else if c == '"' then
        let isBangInterp :=
          i >= 2 && cs[i - 1]! == '!' &&
          (cs[i - 2]! == 's' || cs[i - 2]! == 'm') &&
          (i == 2 || !isLeanIdentCont cs[i - 3]!)
        let isFInterp :=
          i >= 1 && cs[i - 1]! == 'f' &&
          (i == 1 || !isLeanIdentCont cs[i - 2]!)
        if isBangInterp || isFInterp then
          inInterpStr := true
          i := i + 1
        else
          i := i + 1
          while i < n do
            let ch := cs[i]!
            if ch == '\\' then
              if i + 1 < n then
                if cs[i + 1]! == '\n' then line := line + 1
                i := i + 2
              else
                i := i + 1
            else if ch == '"' then
              i := i + 1
              break
            else
              if ch == '\n' then line := line + 1
              i := i + 1
      else if c == '\'' && (i == 0 || !isLeanIdentCont cs[i - 1]!) then
        let mut j := i + 1
        let mut closed := false
        if j < n && cs[j]! == '\\' then
          j := j + 2
          while j < n && j < i + 10 && cs[j]! != '\n' do
            if cs[j]! == '\'' then closed := true; j := j + 1; break
            j := j + 1
        else if j + 1 < n && cs[j]! != '\n' && cs[j + 1]! == '\'' then
          closed := true
          j := j + 2
        i := if closed then j else i + 1
      else if isLeanIdentStart c then
        let start := i
        let tokLine := line
        i := i + 1
        while i < n && isLeanIdentCont cs[i]! do
          i := i + 1
        let tok := String.ofList (cs.extract start i).toList
        if forbiddenTokens.contains tok then
          hits := hits.push (tokLine, tok)
      else
        i := i + 1
  return hits

def grepForbidden : IO Bool := do
  let all ← collect "." "lean" [".lake", ".qed", "dist", "scratch", "toolchains", "node_modules", ".git", "scripts", "Cli"]
  let files := all.filter (fun p => p.fileName != some "Cli.lean")
  let mut clean := true
  for f in files do
    let hits := findForbiddenTokens (← IO.FS.readFile f)
    for (ln, tok) in hits do
      IO.eprintln (red s!"  forbidden token `{tok}` in {f}:{ln}")
      clean := false
  return clean

def axiomClean (leanPath? : Option String := none) : IO Bool := do
  if !(← axiomsManifest.pathExists) then return true
  let (code, out) ← match leanPath? with
    | some lp => shOut "lean" #["--root=.", axiomsManifest.toString] #[("LEAN_PATH", some lp)]
    | none    => shOut "lake" #["env", "lean", "--root=.", axiomsManifest.toString]
  let clean := code == 0
    && !out.contains "sorryAx"
    && !out.contains "Lean.ofReduceBool"
    && !out.contains "Lean.trustCompiler"
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

private def pathToModule (base : FilePath) (p : FilePath) : Option String :=
  let s := p.toString
  let pref := base.toString ++ "/"
  let rel := if s.startsWith pref then (s.drop pref.length).toString else s
  if rel.endsWith ".lean" then
    some (((rel.dropEnd 5).toString).replace "/" ".")
  else none

/-- Fast (~15ms), zero-jitter structural build-time guardrails for the QED repo:
    prevents accidental `Lean` meta leaks into pure modules, critical-path/proof
    import regressions, and Rust `Cargo.lock` crate bloat. -/
def buildGraphClean : IO Bool := do
  let qh ← frameworkHome
  let qedDir := qh / "Qed"
  unless (← qedDir.pathExists) do return true
  let mut files ← collect qedDir "lean"
  let qedRoot := qh / "Qed.lean"
  if ← qedRoot.pathExists then files := files.push qedRoot
  let mut adj : Std.HashMap String (Array String) := {}
  for f in files do
    if let some mod := pathToModule qh f then
      adj := adj.insert mod (parseLeanImports (← IO.FS.readFile f))
  let reaches (start target : String) : Bool := Id.run do
    let mut visited : Std.HashSet String := {}
    let mut stack : Array String := #[start]
    while !stack.isEmpty do
      let cur := stack.back!
      stack := stack.pop
      if !visited.contains cur then
        visited := visited.insert cur
        for dep in adj.getD cur #[] do
          if dep == target || (target == "Lean" && dep.startsWith "Lean.") then
            return true
          if !visited.contains dep && adj.contains dep then
            stack := stack.push dep
    return false
  let mut ok := true
  -- 1. Pure non-meta modules must never transitively import `Lean` (~185ms/file tax).
  let purePrefixes := #["Qed.Driver.", "Qed.Socket.", "Qed.Speculative.", "Qed.Proofs."]
  let pureExact := #[
    "Qed.Html", "Qed.Render", "Qed.View.Core", "Qed.Ssr", "Qed.Resource",
    "Qed.Socket", "Qed.Driver", "Qed.Speculative",
    "Qed.Runtime.AppCore", "Qed.Runtime.LocalCore", "Qed.Runtime.Cmd",
    "Qed.Server.Core", "Qed.Server.Http", "Qed.Server.Net", "Qed.Server.Prim",
    "Qed.Server.Native", "Qed.Server.Ensured",
    "Qed.Server.Db.Core", "Qed.Server.Db.HttpSql", "Qed.Server.Db.PgWire"
  ]
  for (mod, _) in adj.toList do
    let isPure := pureExact.contains mod || purePrefixes.any (mod.startsWith ·)
    if isPure && reaches mod "Lean" then
      IO.eprintln (red s!"  build-graph regression: pure module `{mod}` transitively imports `Lean`")
      ok := false
  -- 2. Critical-path & proof-separation boundaries (direct or transitive).
  let forbiddenEdges : Array (String × String) := #[
    ("Qed.Style.Syntax",          "Qed.Style.Proofs"),
    ("Qed.Component.Speculative", "Qed.Speculative.Proofs"),
    ("Qed.Server.Core",           "Qed.Json.Proofs"),
    ("Qed.Socket.Basic",          "Qed.Json.Proofs"),
    ("Qed.Server.Syntax",         "Qed.Server.Core"),
    ("Qed.Server.FnElab",         "Qed.Server.Invariant"),
    ("Qed.Server.FnElab",         "Qed.Server.External"),
    ("Qed.Invariant.State",       "Qed.Runtime.App"),
    ("Qed.Invariant.View",        "Qed.Runtime.App"),
    ("Qed.Invariant.ForEach",     "Qed.Runtime.App"),
    ("Qed.Invariant.View",        "Qed.Invariant.State"),
    ("Qed.Schema",                "Qed.Runtime.Verify"),
    ("Qed.Component.Rewrite",     "Qed.Runtime.Verify")
  ]
  for (src, dst) in forbiddenEdges do
    if adj.contains src && reaches src dst then
      IO.eprintln (red s!"  build-graph regression: `{src}` reaches forbidden dependency `{dst}`")
      ok := false
  -- 3. Rust `Cargo.lock` crate-count cap (baseline: 46 with bundled `rusqlite` SQLite + `ring` TLS).
  let lockPath := qh / "rust" / "qed_server" / "Cargo.lock"
  if ← lockPath.pathExists then
    let lockSrc ← IO.FS.readFile lockPath
    let pkgCount := (lockSrc.splitOn "\n[[package]]\n").length - 1 +
      (if lockSrc.startsWith "[[package]]\n" then 1 else 0)
    if pkgCount > 50 then
      IO.eprintln (red s!"  build-graph regression: rust/qed_server/Cargo.lock has {pkgCount} packages (budget ≤ 50)")
      ok := false
  return ok

def kernelEnvClean (q? : Option QedjsEnv := none) (alreadyBuilt : Bool := false) : IO Bool := do
  let root ← webRoot
  let hasExamples ← (FilePath.mk "Examples").pathExists
  let some q ← (match q? with | some e => pure (some e) | none => resolveQedjsEnv (needBuild := !hasExamples)) | return false
  if hasExamples then
    let baseMods := #[
      "Qed", "Qed.Driver", "Qed.Server.Native",
      "Qed.Proofs.DomArena", "Qed.Proofs.ViewPatch", "Qed.Proofs.KeyedReconcile", "Qed.Proofs.Hydration",
      "Js.Backend", "Js.Proofs",
      "Examples.Counter", "Examples.Todo", "Examples.Signup",
      "Examples.Chat", "Examples.Bookshelf", "Examples.CloudBooks", "Examples.LiveRoom",
      "Tests.ServerChecks", "Tests.DbChecks", "Tests.SpeculativeChecks", "Tests.JsGate", "Tests.VerificationChecks"
    ]
    let mods := if baseMods.contains root then baseMods else baseMods.push root
    q.run (#["--verify-env"] ++ mods) (quiet := true)
  else
    if !alreadyBuilt then
      if (← shQuiet "lake" #["build", root]) != 0 then return false
    q.run #["--verify-env", "--skip-qed", root] (quiet := true)

def externsCovered (q? : Option QedjsEnv := none) (alreadyBuilt : Bool := false) : IO Bool := do
  let rtPath ← runtimeFile "qed_rt.mjs"
  unless (← rtPath.pathExists) do return true
  let mod ← jsRoot
  let modPath := FilePath.mk ((mod.replace "." "/") ++ ".lean")
  let hasExamples ← (FilePath.mk "Examples").pathExists
  let mut mods : Array String := #[]
  let mut entries : Array String := #[]
  if ← modPath.pathExists then
    if !alreadyBuilt && !hasExamples && mod != (← webRoot) then
      if (← shQuiet "lake" #["build", mod]) != 0 then return false
    match ← resolveAppMode mod with
    | .fullstack fsName =>
        mods := #[mod, "Qed.Driver"]
        entries := #[s!"{fsName}.clientApp", "Qed.run"] ++ driverEntries.filter (!·.startsWith "main:")
    | .ssr a =>
        mods := #[mod]
        entries := driverEntries ++ #[s!"{a}:app", "Qed.App.ssrStep:ssrStep"]
    | .component a =>
        mods := #[mod, "Qed.Driver"]
        entries := #["Qed.run"] ++ driverEntries.filter (!·.startsWith "main:") ++ #[s!"{a}:app", "Qed.App.ssrStep:ssrStep"]
    | .raw =>
        mods := #[mod]
        entries := driverEntries
  if hasExamples then
    mods := mods.push "Tests.JsGate"
    entries := entries ++ #["JsGate.run", "JsGate.counts", "JsGate.probeCount", "JsGate.names"]
  if entries.isEmpty then return true
  let some q ← (match q? with | some e => pure (some e) | none => resolveQedjsEnv) | return false
  q.run (#["--check-externs", rtPath.toString] ++ mods ++ #["--"] ++ entries) (quiet := true)

def verify (checkExterns : Bool := true) (extraLakeTargets : Array String := #[]) : IO Bool := do
  step "verifying proofs & axioms"
  let hasExamples ← (FilePath.mk "Examples").pathExists
  -- Start source-only checks and LEAN_PATH lookup in parallel with `lake build`.
  let tGrep ← IO.asTask grepForbidden
  let tEff ← if hasExamples then IO.asTask effectsCovered else IO.asTask (pure true)
  let tGraph ← if hasExamples then IO.asTask buildGraphClean else IO.asTask (pure true)
  let tLp ← IO.asTask lakeEnvLeanPath
  let lakeOk ← if hasExamples then
    let base := #["Qed", "Qed.Driver", "QedServer", "QedProofs", "JsProofs", "qedjs", "Examples", "Tests"]
    let extra := extraLakeTargets.filter (!base.contains ·)
    pure ((← shLakeBuild (#["build"] ++ base ++ extra)) == 0)
  else
    let root ← webRoot
    let jsMod ← jsRoot
    let base := if checkExterns && jsMod != root then #[root, jsMod] else #[root]
    let extra := extraLakeTargets.filter (!base.contains ·)
    pure ((← shLakeBuild (#["build"] ++ base ++ extra)) == 0)
  if !lakeOk then
    discard <| IO.wait tGrep
    discard <| IO.wait tEff
    discard <| IO.wait tGraph
    discard <| IO.wait tLp
    return false
  let lp? := (← IO.wait tLp).toOption.join
  let q? ← match ← resolveQedjsBin (needBuild := false), lp? with
    | some bin, some leanPath => pure (some { bin, leanPath : QedjsEnv })
    | _, _ => resolveQedjsEnv (needBuild := false)
  let tAxiom ← IO.asTask (axiomClean (q?.map (·.leanPath)))
  let tExt ← if checkExterns then IO.asTask (externsCovered q? (alreadyBuilt := true)) else IO.asTask (pure true)
  let ok3 ← kernelEnvClean q? (alreadyBuilt := true)
  let ok5 := (← IO.wait tExt).toOption.getD false
  let ok1 := (← IO.wait tGrep).toOption.getD false
  let ok2 := (← IO.wait tAxiom).toOption.getD false
  let ok4 := (← IO.wait tEff).toOption.getD false
  let ok6 := (← IO.wait tGraph).toOption.getD false
  return ok1 && ok2 && ok3 && ok4 && ok5 && ok6

def cmdCheck : IO UInt32 := do
  if (← verify (checkExterns := true)) then
    IO.println (green "✓ verified"); return 0
  else IO.eprintln (red "✗ verification failed"); return 1

end Qed.Cli
