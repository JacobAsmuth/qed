import Lean

namespace Qed.Diag

/-! ## Edit Distance & "Did You Mean?" Suggestions -/

def editDistance (a b : String) : Nat := Id.run do
  let xs := a.toLower.toList.toArray; let ys := b.toLower.toList.toArray
  let mut prev := Array.range (ys.size + 1)
  for i in [0:xs.size] do
    let mut curr := (Array.replicate (ys.size + 1) 0).set! 0 (i + 1)
    for j in [0:ys.size] do
      curr := curr.set! (j + 1) (min (prev[j + 1]! + 1) (min (curr[j]! + 1) (prev[j]! + if xs[i]! == ys[j]! then 0 else 1)))
    prev := curr
  return prev[ys.size]!

def suggestClosest (needle : String) (candidates : List String) : Option String :=
  if needle.isEmpty then none else
    let maxDist := if needle.length <= 3 then 1 else if needle.length <= 7 then 2 else 3
    (candidates.foldl (init := none) fun (best : Option (Nat × String)) cand =>
      if cand == needle then best else
        let d := editDistance needle cand
        if d <= maxDist && best.all (d < ·.1) then some (d, cand) else best).map (·.2)

def didYouMean (needle : String) (candidates : List String) : String :=
  (suggestClosest needle candidates).elim "" (s!" (did you mean `{·}`?)")

/-! ## Qed-Native ASCII Formatting for Proof Obligations -/

private def stripMacroDaggersLoop (skip : Bool) : List Char → List Char
  | [] => [] | '✝' :: r => stripMacroDaggersLoop true r
  | c :: r => if skip && (c.isDigit || "⁰¹²³⁴⁵⁶⁷⁸⁹".contains c) then stripMacroDaggersLoop true r else c :: stripMacroDaggersLoop false r

def stripStatePrefixes (s : String) (prefixes : List String := []) : String := Id.run do
  let allPfx := (["_qed_s", "_s0", "_s1", "_s"] ++ prefixes).filter (!·.isEmpty) |>.map (·.toList.toArray)
  let cs := s.toList.toArray; let n := cs.size; let mut out : Array Char := #[]; let mut i : Nat := 0
  for _ in [0:n] do
    if i >= n then break
    let prevIdent := i > 0 && (cs[i - 1]!.isAlphanum || cs[i - 1]! == '_' || cs[i - 1]! == '\'')
    let hit := if prevIdent then none else allPfx.find? fun p =>
      i + p.size + 1 < n && cs[i + p.size]! == '.' && (cs[i + p.size + 1]!.isAlpha || cs[i + p.size + 1]! == '_') && cs.extract i (i + p.size) == p
    match hit with | some p => i := i + p.size + 1 | none => out := out.push cs[i]!; i := i + 1
  return String.ofList out.toList

private def rewriteNotEqAtom (chunk : String) : String :=
  let t := chunk.trimAscii.toString
  let inner? := if t.startsWith "¬(" && t.endsWith ")" then some (String.ofList (t.toList.drop 2).dropLast).trimAscii.toString
    else if t.startsWith "¬" && !t.startsWith "¬(" then some (String.ofList (t.toList.drop 1)).trimAscii.toString else none
  match inner? with
  | some inner => if (inner.splitOn " = ").length == 2 && !inner.toList.any ("∧∨→".contains ·) then inner.replace " = " " != " else chunk
  | none => chunk

private def asciiReplacements : Array (String × String) := #[
  (" ≤ ", " <= "), (" ≥ ", " >= "), (" ≠ ", " != "), (" ∧ ", " and "), (" ∨ ", " or "), (" → ", " -> "), (" ↔ ", " <-> "),
  (" ^ ", " ** "), (" &&& ", " & "), (" ||| ", " | "), (" ^^^ ", " ^ "), (" <<< ", " << "), (" >>> ", " >> "), ("~~~", "~"),
  ("≤", "<="), ("≥", ">="), ("≠", "!="), ("¬(", "not ("), ("¬", "not "), ("∀ ", "all "), ("∃ ", "any ")]

def toQedAscii (raw : String) (stripPrefixes : List String := []) : String :=
  let collapsed := String.intercalate " " (((String.ofList (stripMacroDaggersLoop false raw.toList)).split Char.isWhitespace).toList.filterMap fun sl => if sl.isEmpty then none else some sl.toString)
  let s := ([" ∨ ", " ∧ ", " → "].foldr (fun sep f t => String.intercalate sep ((t.splitOn sep).map f)) rewriteNotEqAtom) (stripStatePrefixes collapsed stripPrefixes)
  (asciiReplacements.foldl (fun acc (a, b) => acc.replace a b) s).trimAscii.toString

/-! ## Case Tag Formatting -/

private def isSplitSuffix (s : String) : Bool :=
  ["pos", "neg", "inl", "inr", "isTrue", "isFalse", "intro", "mk", "left", "right",
   "some", "none", "ok", "err", "failed", "loading", "idle"].contains s || s.startsWith "h_" || s.startsWith "case" || s.all Char.isDigit

def rootCaseTag (tag : Lean.Name) : String :=
  let parts := match tag.components.map (·.toString) with | "step" :: rest => rest | other => other
  String.intercalate "." (match parts with | [] => [] | first :: rest => first :: rest.takeWhile (!isSplitSuffix ·))

private def caseTagPrefixes : Array (String × (String → String)) := #[
  ("_query_", (s!"query `{·}`")), ("_wsJoin_", (s!"subscribe `{·}` (`on_join`)")), ("_wsMsg_", (s!"subscribe `{·}` (`on_event`)")),
  ("_wsStatus_", (s!"subscribe `{·}` (status)")), ("_specRollback_", fun _ => "`rollback` branch"), ("_specConfirm_", fun _ => "`on_confirm` branch"),
  ("_specCont_", fun _ => "speculative `predict` update"), ("_specPre_", fun _ => "before speculative `await`"), ("_specRes_", fun _ => "speculative resolution"),
  ("_cont_", fun _ => "continuation after `await`"), ("_form_reset_", fun _ => "form `reset`"), ("_sub_", fun _ => "child component update"), ("set_", (s!"handler updating `{·}`"))]

def formatCaseTag (tag : Lean.Name) : String :=
  match rootCaseTag tag with
  | "" | "_" | "anonymous" => "this branch" | "init" => "initial state" | "_onRoute" => "route change"
  | raw => match caseTagPrefixes.find? (raw.startsWith ·.1) with | some (pfx, fmt) => fmt (raw.drop pfx.length).toString | none => s!"action `{raw}`"

/-! ## MetaM Expression Cleaner & Pretty-Printer -/

private def cleanQedUnwrapTable : Array (Lean.Name × Nat × Nat) := #[
  (`Qed.Lang.QedVal.val, 4, 3), (`Qed.Field.val, 3, 2), (`Qed.Ensured.val, 3, 2), (`Qed.Server.SrvIdx.toNat, 3, 2),
  (`Qed.Server.SrvLiftOpt.liftOpt, 4, 3), (`Qed.Lang.QedSeqLit.ofList, 4, 3), (``id, 2, 1)]

section MetaHelpers
open Lean Meta Elab Tactic Command

def cleanQedExpr (e : Expr) : MetaM Expr := do
  Meta.transform (← instantiateMVars e) (pre := fun sub => do
    if let .proj nm 0 inner := sub then return if nm == `Qed.Field || nm == `Qed.Ensured then .visit inner else .continue
    if let some c := sub.getAppFn.constName? then
      let args := sub.getAppArgs
      if let some (_, _, idx) := cleanQedUnwrapTable.find? fun (nm, ar, _) => nm == c && args.size == ar then return .visit args[idx]!
    return .continue)

def modRootOf (env : Environment) (n : Name) (fallback : Name := .anonymous) : Name :=
  ((env.getModuleIdxFor? n).map (env.header.moduleNames.getD ·.toNat fallback)).getD fallback |>.getRoot
def isToolchainRoot (root : Name) (includeQed : Bool := false) : Bool :=
  root == `Init || root == `Std || root == `Lean || root == `Lake || (includeQed && root == `Qed)
def ppQedExpr (e : Expr) (stripPrefixes : List String := []) : MetaM String := do
  return toQedAscii (← Meta.ppExpr (← cleanQedExpr e)).pretty stripPrefixes

def mkNameMapExt {α : Type} [Inhabited α] (keyOf : α → Name) (name : Name := by exact decl_name%) : IO (SimplePersistentEnvExtension α (NameMap α)) :=
  registerSimplePersistentEnvExtension {
    name
    addImportedFn := fun arrs => arrs.foldl (fun acc arr => arr.foldl (fun m i => m.insert (keyOf i) i) acc) {}
    addEntryFn := fun m i => m.insert (keyOf i) i
  }

def lookupNameMap? {α : Type} (reg : NameMap α) (env : Environment) (currNs : Name) (openDecls : List OpenDecl)
    (ref : Name) (probeSuffix? : Option Name := none) : Option α :=
  let clean := ref.eraseMacroScopes
  (reg.find? (currNs ++ clean)).orElse fun _ => (reg.find? clean).orElse fun _ =>
    (openDecls.findSome? fun | .simple ns _ => reg.find? (ns ++ clean) | .explicit id d => if id == clean then reg.find? d else none).orElse fun _ =>
      (ResolveName.resolveGlobalName env {} currNs openDecls (probeSuffix?.elim clean (clean ++ ·))).findSome? fun (full, _) =>
        reg.find? (if probeSuffix?.isSome then full.getPrefix else full)

def lookupNameMapExt? {α : Type} [Inhabited α] (ext : SimplePersistentEnvExtension α (NameMap α))
    (env : Environment) (currNs : Name) (openDecls : List OpenDecl) (ref : Name) (probeSuffix? : Option Name := none) : Option α :=
  lookupNameMap? (ext.getState env) env currNs openDecls ref probeSuffix?

def snapshotTreeHasErrors : Nat → Language.SnapshotTree → Bool
  | 0, tree => tree.element.diagnostics.msgLog.hasErrors
  | fuel + 1, tree => tree.element.diagnostics.msgLog.hasErrors || tree.children.any (snapshotTreeHasErrors fuel ·.get)

def throwUnsolvedGoals (header : MessageData) (footer : MessageData := m!"") (ref? : Option Syntax := none)
    (stripPrefixes : List String := []) (bulletPrefix : String := "  • must satisfy:  ")
    (formatGoal? : Option (MVarId → MetaM (Option String)) := none) (maxShown? : Option Nat := none)
    (moreLabel : String := "failing branch(es)") (goals? : Option (List MVarId) := none) : TacticM Unit := do
  let goals ← goals?.elim getUnsolvedGoals pure
  if goals.isEmpty then return
  let fmtGoal := formatGoal?.getD fun g => do return some s!"{bulletPrefix}{← g.withContext (ppQedExpr (← instantiateMVars (← g.getType)) stripPrefixes)}"
  let mut lines : Array String := #[]
  for g in goals do if let some line ← fmtGoal g then if !lines.contains line then lines := lines.push line
  let (shown, extra) := match maxShown? with
    | some k => (lines.extract 0 (min lines.size k), if lines.size > k then s!"\n  • (+ {lines.size - k} more {moreLabel})" else "")
    | none => (lines, "")
  let fullMsg := m!"{header}{if shown.isEmpty then m!"" else m!"\n{String.intercalate "\n" shown.toList}{extra}"}{footer}"
  match ref? with | some ref => throwErrorAt ref fullMsg | none => throwError fullMsg

def probeTermElabMsgs {α : Type} (action : Term.TermElabM α) : CommandElabM (Option α × List Message) := do
  let saved ← get; let preCount := saved.messages.toList.length
  let res? ← try some <$> liftTermElabM action catch _ => pure none
  let newMsgs := (← get).messages.toList.drop preCount; set saved; return (res?, newMsgs)

def probeTermElabOk (action : Term.TermElabM Bool) : CommandElabM Bool := do
  let (res?, msgs) ← probeTermElabMsgs action; return res? == some true && msgs.all (·.severity != .error)

end MetaHelpers
end Qed.Diag
