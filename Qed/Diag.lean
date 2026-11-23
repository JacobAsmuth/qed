import Lean

namespace Qed.Diag

/-! ## Edit Distance & "Did You Mean?" Suggestions -/

/-- Total Levenshtein edit distance between two strings (case-insensitive). -/
def editDistance (a b : String) : Nat := Id.run do
  let xs := a.toLower.toList.toArray
  let ys := b.toLower.toList.toArray
  let m := xs.size
  let n := ys.size
  if m == 0 then return n
  if n == 0 then return m
  let mut prev : Array Nat := Array.range (n + 1)
  for i in [0:m] do
    let mut curr : Array Nat := Array.replicate (n + 1) 0
    curr := curr.set! 0 (i + 1)
    for j in [0:n] do
      let cost := if xs[i]! == ys[j]! then 0 else 1
      let del := prev[j + 1]! + 1
      let ins := curr[j]! + 1
      let sub := prev[j]! + cost
      curr := curr.set! (j + 1) (min del (min ins sub))
    prev := curr
  return prev[n]!

/-- Finds the closest candidate to `needle` within an adaptive edit-distance budget. -/
def suggestClosest (needle : String) (candidates : List String) : Option String := Id.run do
  if needle.isEmpty then return none
  let maxDist := if needle.length <= 3 then 1 else if needle.length <= 7 then 2 else 3
  let mut best : Option (Nat × String) := none
  for cand in candidates do
    if cand != needle then
      let d := editDistance needle cand
      if d <= maxDist then
        match best with
        | none => best := some (d, cand)
        | some (bd, _) => if d < bd then best := some (d, cand)
  return best.map (·.2)

def didYouMean (needle : String) (candidates : List String) : String :=
  match suggestClosest needle candidates with
  | some c => s!" (did you mean `{c}`?)"
  | none   => ""

/-! ## Qed-Native ASCII Formatting for Proof Obligations -/

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''

private def isMacroIndexChar (c : Char) : Bool :=
  c.isDigit || c == '⁰' || c == '¹' || c == '²' || c == '³' || c == '⁴' ||
  c == '⁵' || c == '⁶' || c == '⁷' || c == '⁸' || c == '⁹'

private def stripMacroDaggersLoop (skipping : Bool) : List Char → List Char
  | [] => []
  | '✝' :: rest => stripMacroDaggersLoop true rest
  | c :: rest =>
      if skipping && isMacroIndexChar c then stripMacroDaggersLoop true rest
      else c :: stripMacroDaggersLoop false rest

private def stripMacroDaggers (s : String) : String :=
  String.ofList (stripMacroDaggersLoop false s.toList)

/-- Removes internal state variable prefixes like `_s0.`, `_s1.`, `_qed_s.`, `_s.`, or `m.`
    when they appear at an identifier boundary followed by a field name. -/
def stripStatePrefixes (s : String) (prefixes : List String := []) : String := Id.run do
  let allPfx := ["_qed_s", "_s0", "_s1", "_s"] ++ prefixes
  let cs := s.toList.toArray
  let n := cs.size
  let mut out : Array Char := #[]
  let mut i : Nat := 0
  for _ in [0:n] do
    if i >= n then break
    let prevIsIdent := i > 0 && isIdentChar cs[i - 1]!
    let mut matchedLen : Nat := 0
    if !prevIsIdent then
      for pfx in allPfx do
        if matchedLen == 0 then
          let pcs := pfx.toList.toArray
          let plen := pcs.size
          if plen > 0 && i + plen + 1 < n && cs[i + plen]! == '.' &&
              (cs[i + plen + 1]!.isAlpha || cs[i + plen + 1]! == '_') then
            let mut ok := true
            for k in [0:plen] do
              if cs[i + k]! != pcs[k]! then ok := false
            if ok then
              matchedLen := plen + 1
    if matchedLen > 0 then
      i := i + matchedLen
    else
      out := out.push cs[i]!
      i := i + 1
  return String.ofList out.toList

/-- Collapses runs of whitespace/newlines into single spaces for compact one-line obligations. -/
private def collapseSpaces (s : String) : String :=
  String.intercalate " " ((s.split Char.isWhitespace).toList.filterMap fun sl =>
    if sl.isEmpty then none else some sl.toString)

/-- Rewrites `¬a = b` and `¬(a = b)` clauses (including inside `∧`, `∨`, `→` compounds) to `a != b`. -/
private def rewriteNotEqAtom (chunk : String) : String :=
  let t := chunk.trimAscii.toString
  let inner? :=
    if t.startsWith "¬(" && t.endsWith ")" then some ((String.ofList ((t.toList.drop 2).dropLast)).trimAscii.toString)
    else if t.startsWith "¬" && !t.startsWith "¬(" then some ((String.ofList (t.toList.drop 1)).trimAscii.toString)
    else none
  match inner? with
  | some inner =>
      if (inner.splitOn " = ").length == 2 && !inner.contains '∧' && !inner.contains '∨' && !inner.contains '→' then
        inner.replace " = " " != "
      else chunk
  | none => chunk

private def rewriteNotEq (s : String) : String :=
  let byOr := s.splitOn " ∨ " |>.map fun part =>
    let byAnd := part.splitOn " ∧ " |>.map fun sub =>
      let byImp := sub.splitOn " → " |>.map rewriteNotEqAtom
      String.intercalate " → " byImp
    String.intercalate " ∧ " byAnd
  String.intercalate " ∨ " byOr

private def asciiReplacements : Array (String × String) := #[
  (" ≤ ", " <= "), (" ≥ ", " >= "), (" ≠ ", " != "), (" ∧ ", " and "), (" ∨ ", " or "),
  (" → ", " -> "), (" ↔ ", " <-> "), ("≤", "<="), ("≥", ">="), ("≠", "!="),
  ("¬(", "not ("), ("¬", "not "), ("∀ ", "all "), ("∃ ", "exists ")
]

/-- Converts a Lean pretty-printed proposition/expression into Qed's plain ASCII syntax. -/
def toQedAscii (raw : String) (stripPrefixes : List String := []) : String :=
  let s := rewriteNotEq (stripStatePrefixes (collapseSpaces (stripMacroDaggers raw)) stripPrefixes)
  (asciiReplacements.foldl (fun acc (a, b) => acc.replace a b) s).trimAscii.toString

/-! ## Case Tag Formatting -/

private def isSplitSuffix (s : String) : Bool :=
  ["pos", "neg", "inl", "inr", "isTrue", "isFalse", "intro", "mk", "left", "right",
   "some", "none", "ok", "err", "failed", "loading", "idle"].contains s ||
  s.startsWith "h_" || s.startsWith "case" || s.all Char.isDigit

/-- Extracts the root component/message tag, dropping `step.` prefixes and tactic split suffixes. -/
def rootCaseTag (tag : Lean.Name) : String :=
  let parts := tag.components.map (·.toString)
  let parts := match parts with
    | "step" :: rest => rest
    | other => other
  let parts := match parts with
    | [] => []
    | first :: rest =>
        let kept := rest.takeWhile fun p => !isSplitSuffix p
        first :: kept
  String.intercalate "." parts

private def caseTagPrefixes : Array (String × (String → String)) := #[
  ("_query_",        fun s => s!"query `{s}`"),
  ("_wsJoin_",       fun s => s!"subscribe `{s}` (`on_join`)"),
  ("_wsMsg_",        fun s => s!"subscribe `{s}` (`on_event`)"),
  ("_wsStatus_",     fun s => s!"subscribe `{s}` (status)"),
  ("_specRollback_", fun _ => "`rollback` branch"),
  ("_specConfirm_",  fun _ => "`on_confirm` branch"),
  ("_specCont_",     fun _ => "speculative `predict` update"),
  ("_specPre_",      fun _ => "before speculative `await`"),
  ("_specRes_",      fun _ => "speculative resolution"),
  ("_cont_",         fun _ => "continuation after `await`"),
  ("_form_reset_",   fun _ => "form `reset`"),
  ("_sub_",          fun _ => "child component update"),
  ("set_",           fun s => s!"handler updating `{s}`")
]

/-- Formats a goal tag into a human-readable Qed branch label (e.g. `action \`decrease\``, `rollback`). -/
def formatCaseTag (tag : Lean.Name) : String :=
  let raw := rootCaseTag tag
  if raw.isEmpty || raw == "_" || raw == "anonymous" then "this branch"
  else if raw == "init" then "initial state"
  else if raw == "_onRoute" then "route change"
  else match caseTagPrefixes.find? fun (pfx, _) => raw.startsWith pfx with
    | some (pfx, fmt) => fmt (raw.drop pfx.length).toString
    | none            => s!"action `{raw}`"

/-! ## MetaM Expression Cleaner & Pretty-Printer -/

private def cleanQedUnwrapTable : Array (Lean.Name × Nat × Nat) := #[
  (`Qed.Lang.QedVal.val, 4, 3), (`Qed.Field.val, 3, 2), (`Qed.Ensured.val, 3, 2),
  (`Qed.Server.SrvIdx.toNat, 3, 2), (`Qed.Server.SrvLiftOpt.liftOpt, 4, 3),
  (`Qed.Lang.QedSeqLit.ofList, 4, 3), (``id, 2, 1)
]

section MetaHelpers
open Lean Meta Elab Tactic Command

/-- Unwraps internal Qed wrapper projections/coercions (`QedVal.val`, `Field.val`, `Ensured.val`,
    `SrvIdx.toNat`, `SrvLiftOpt.liftOpt`, `QedSeqLit.ofList`, `id`) so pretty-printed proof
    obligations read like the user's source code. -/
def cleanQedExpr (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  Meta.transform e (pre := fun sub => do
    match sub with
    | .proj nm 0 inner =>
        return if nm == `Qed.Field || nm == `Qed.Ensured then .visit inner else .continue
    | _ =>
        if let some c := sub.getAppFn.constName? then
          let args := sub.getAppArgs
          if let some (_, _, idx) := cleanQedUnwrapTable.find? fun (nm, ar, _) => nm == c && args.size == ar then
            return .visit args[idx]!
        return .continue)

/-- Returns the root component of the module defining `n`, or `fallback.getRoot` for current-module declarations. -/
def modRootOf (env : Environment) (n : Name) (fallback : Name := .anonymous) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames.getD idx.toNat fallback).getRoot
  | none     => fallback.getRoot

/-- Checks whether `root` belongs to the Lean toolchain (`Init`, `Std`, `Lean`, `Lake`) and optionally `Qed`. -/
def isToolchainRoot (root : Name) (includeQed : Bool := false) : Bool :=
  root == `Init || root == `Std || root == `Lean || root == `Lake || (includeQed && root == `Qed)

/-- Pretty-prints a Lean expression in clean Qed-native ASCII syntax. -/
def ppQedExpr (e : Expr) (stripPrefixes : List String := []) : MetaM String := do
  let cleaned ← cleanQedExpr e
  let fmt ← Meta.ppExpr cleaned
  return toQedAscii fmt.pretty stripPrefixes

/-- Registers a persistent `NameMap` environment extension keyed by `keyOf`. -/
def mkNameMapExt {α : Type} [Inhabited α] (keyOf : α → Name)
    (name : Name := by exact decl_name%) :
    IO (SimplePersistentEnvExtension α (NameMap α)) :=
  registerSimplePersistentEnvExtension {
    name := name
    addImportedFn := fun arrays =>
      arrays.foldl (fun acc arr => arr.foldl (fun m info => m.insert (keyOf info) info) acc) {}
    addEntryFn := fun m info => m.insert (keyOf info) info
  }

/-- Resolves `ref` inside a `NameMap α` by trying `currNs ++ clean`, `clean`, open namespaces,
    and Lean global name resolution (either directly on `clean` or via a probe suffix whose
    resolved prefix is looked up in `reg`). -/
def lookupNameMap? {α : Type} (reg : NameMap α) (env : Environment)
    (currNs : Name) (openDecls : List OpenDecl) (ref : Name)
    (probeSuffix? : Option Name := none) : Option α :=
  let clean := ref.eraseMacroScopes
  (reg.find? (currNs ++ clean)).orElse fun _ =>
    (reg.find? clean).orElse fun _ =>
      let fromOpen := openDecls.findSome? fun
        | .simple ns _ => reg.find? (ns ++ clean)
        | .explicit id declName => if id == clean then reg.find? declName else none
      fromOpen.orElse fun _ =>
        match probeSuffix? with
        | some suf =>
            (ResolveName.resolveGlobalName env {} currNs openDecls (clean ++ suf)).findSome?
              fun (full, _) => reg.find? full.getPrefix
        | none =>
            (ResolveName.resolveGlobalName env {} currNs openDecls clean).findSome?
              fun (full, _) => reg.find? full

/-- Resolves `ref` inside a persistent `NameMap` environment extension. -/
def lookupNameMapExt? {α : Type} [Inhabited α]
    (ext : SimplePersistentEnvExtension α (NameMap α))
    (env : Environment) (currNs : Name)
    (openDecls : List OpenDecl) (ref : Name)
    (probeSuffix? : Option Name := none) : Option α :=
  lookupNameMap? (ext.getState env) env currNs openDecls ref probeSuffix?

/-- Recursively checks whether a `Language.SnapshotTree` contains any logged errors. -/
def snapshotTreeHasErrors : Nat → Language.SnapshotTree → Bool
  | 0, tree => tree.element.diagnostics.msgLog.hasErrors
  | fuel + 1, tree =>
      tree.element.diagnostics.msgLog.hasErrors ||
      tree.children.any fun t => snapshotTreeHasErrors fuel t.get

/-- Formats unsolved goals via `formatGoal?` (deduplicating and optionally capping the list)
    and throws a structured diagnostic error when any goal remains. -/
def throwUnsolvedGoals
    (header : MessageData)
    (footer : MessageData := m!"")
    (ref? : Option Syntax := none)
    (stripPrefixes : List String := [])
    (bulletPrefix : String := "  • must satisfy:  ")
    (formatGoal? : Option (MVarId → MetaM (Option String)) := none)
    (maxShown? : Option Nat := none)
    (moreLabel : String := "failing branch(es)")
    (goals? : Option (List MVarId) := none) : TacticM Unit := do
  let goals ← match goals? with | some gs => pure gs | none => getUnsolvedGoals
  if goals.isEmpty then return
  let fmtGoal : MVarId → MetaM (Option String) := formatGoal?.getD fun g => do
    let s ← g.withContext (ppQedExpr (← instantiateMVars (← g.getType)) stripPrefixes)
    return some s!"{bulletPrefix}{s}"
  let mut lines : Array String := #[]
  for g in goals do
    if let some line ← fmtGoal g then
      unless lines.contains line do
        lines := lines.push line
  let shown := match maxShown? with
    | some k => lines.extract 0 (min lines.size k)
    | none   => lines
  let extra := match maxShown? with
    | some k => if lines.size > k then s!"\n  • (+ {lines.size - k} more {moreLabel})" else ""
    | none   => ""
  let bodyPart : MessageData :=
    if shown.isEmpty then m!""
    else m!"\n{String.intercalate "\n" shown.toList}{extra}"
  let fullMsg : MessageData := m!"{header}{bodyPart}{footer}"
  match ref? with
  | some ref => throwErrorAt ref fullMsg
  | none     => throwError fullMsg

/-- Runs `action` inside `liftTermElabM` while rolling back `Command.State`, returning the result
    (or `none` on exception) together with any messages logged during the probe. -/
def probeTermElabMsgs {α : Type} (action : Term.TermElabM α) :
    CommandElabM (Option α × List Message) := do
  let saved ← get
  let preCount := saved.messages.toList.length
  let res? ← try some <$> liftTermElabM action catch _ => pure none
  let newMsgs := (← get).messages.toList.drop preCount
  set saved
  return (res?, newMsgs)

/-- Probes a `TermElabM Bool` check in isolation, returning `true` iff it succeeds with `true`
    and logs no error messages. -/
def probeTermElabOk (action : Term.TermElabM Bool) : CommandElabM Bool := do
  let (res?, msgs) ← probeTermElabMsgs action
  return res? == some true && msgs.all (·.severity != .error)

end MetaHelpers

end Qed.Diag
