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
      let isPolicy := (line.splitOn "never emit").length > 1 || (line.splitOn "fails to compile").length > 1
      if !isPolicy && bad.any (fun w => (line.splitOn w).length > 1) then
        IO.eprintln (red s!"  forbidden tactic in {f}: {line.trimmed}")
        clean := false
  return clean

def axiomClean : IO Bool := do
  if !(← axiomsManifest.pathExists) then return true
  let (_, out) ← shOut "lake" #["env", "lean", "--root=.", axiomsManifest.toString]
  let clean := !((out.splitOn "sorryAx").length > 1) && !((out.splitOn "error:").length > 1)
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

def bracketDelta (s : String) : Int :=
  s.foldl (fun d c =>
    if c == '{' || c == '(' || c == '[' then d + 1
    else if c == '}' || c == ')' || c == ']' then d - 1 else d) 0

def dropTerm : List String → List String
  | []       => []
  | t0 :: tl =>
      let rec skip (depth : Int) : List String → List String
        | []      => []
        | r :: rs => if depth ≤ 0 then r :: rs else skip (depth + bracketDelta r) rs
      skip (bracketDelta t0) tl

def invariantNote : IO Unit := do
  let files := (← collect "." "lean" [".lake", ".qed", "dist", "toolchains", "node_modules", ".git", "scripts", "Cli"])
    |>.filter (·.fileName != some "Cli.lean")
  let tokensOf (line : String) : List String :=
    ((line.replace "\t" " ").splitOn " ").filter (· != "")
  let isName (s : String) : Bool :=
    !s.isEmpty && s != "fun" && s.all (fun c => c.isAlphanum || c == '_' || c == '.' || c == '\'')
  let mut uncovered : Array (FilePath × String) := #[]
  for f in files do
    let mut depth : Nat := 0
    let mut updates : List String := []
    let mut covered : List String := []
    for raw in (← IO.FS.readFile f).splitOn "\n" do
      let inComment := depth > 0
      depth := depth + ((raw.splitOn "/-").length - 1) - ((raw.splitOn "-/").length - 1)
      if inComment then continue
      let ts := tokensOf ((raw.splitOn "--").headD raw)
      match ts.dropWhile (· != "preserved_by") with
      | _ :: name :: _ => covered := name :: covered
      | _              => pure ()
      let afterUi := (ts.dropWhile (· != "ui")).drop 1
      if afterUi.contains "fun" then
        match dropTerm afterUi with
        | upd :: _ => if isName upd then updates := upd :: updates
        | []       => pure ()
    for u in updates do
      unless covered.contains u do uncovered := uncovered.push (f, u)
  unless uncovered.isEmpty do
    IO.println s!"  note: {uncovered.size} update(s) change state with no `invariant … preserved_by`, consider stating one:"
    for (f, u) in uncovered do IO.println s!"    {u}  ({f})"

def verify : IO Bool := do
  step "verifying proofs & axioms"
  if (← shQuiet "lake" #["build"]) != 0 then return false
  if (← (FilePath.mk "Examples").pathExists) then
    if (← shQuiet "lake" #["build", "Examples"]) != 0 then return false
  let ok1 ← grepForbidden
  let ok2 ← axiomClean
  let ok3 ← effectsCovered
  return ok1 && ok2 && ok3

def cmdCheck : IO UInt32 := do
  if (← verify) then
    invariantNote
    IO.println (green "✓ verified"); return 0
  else IO.eprintln (red "✗ verification failed"); return 1

end Qed.Cli
