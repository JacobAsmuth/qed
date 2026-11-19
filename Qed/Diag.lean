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
private def collapseSpaces (s : String) : String := Id.run do
  let mut out : Array Char := #[]
  let mut prevWs := false
  for c in s.toList do
    if c.isWhitespace then
      if !prevWs && !out.isEmpty then
        out := out.push ' '
        prevWs := true
    else
      out := out.push c
      prevWs := false
  let res := String.ofList out.toList
  if res.endsWith " " then String.ofList res.toList.dropLast else res

/-- Rewrites `¬a = b` and `¬(a = b)` clauses (including inside `∧`, `∨`, `→` compounds) to `a != b`. -/
private def rewriteNotEqAtom (chunk : String) : String :=
  let t := chunk.trimAscii.toString
  if t.startsWith "¬(" && t.endsWith ")" then
    let inner := (String.ofList ((t.toList.drop 2).dropLast)).trimAscii.toString
    if (inner.splitOn " = ").length == 2 && !inner.contains '∧' && !inner.contains '∨' && !inner.contains '→' then
      inner.replace " = " " != "
    else chunk
  else if t.startsWith "¬" && !t.startsWith "¬(" then
    let inner := (String.ofList (t.toList.drop 1)).trimAscii.toString
    if (inner.splitOn " = ").length == 2 && !inner.contains '∧' && !inner.contains '∨' && !inner.contains '→' then
      inner.replace " = " " != "
    else chunk
  else chunk

private def rewriteNotEq (s : String) : String :=
  let byOr := s.splitOn " ∨ " |>.map fun part =>
    let byAnd := part.splitOn " ∧ " |>.map fun sub =>
      let byImp := sub.splitOn " → " |>.map rewriteNotEqAtom
      String.intercalate " → " byImp
    String.intercalate " ∧ " byAnd
  String.intercalate " ∨ " byOr

/-- Converts a Lean pretty-printed proposition/expression into Qed's plain ASCII syntax. -/
def toQedAscii (raw : String) (stripPrefixes : List String := []) : String :=
  let s0 := collapseSpaces (stripMacroDaggers raw)
  let s1 := stripStatePrefixes s0 stripPrefixes
  let s2 := rewriteNotEq s1
  let s3 := s2
    |>.replace " ≤ " " <= "
    |>.replace " ≥ " " >= "
    |>.replace " ≠ " " != "
    |>.replace " ∧ " " and "
    |>.replace " ∨ " " or "
    |>.replace " → " " -> "
    |>.replace " ↔ " " <-> "
    |>.replace "≤" "<="
    |>.replace "≥" ">="
    |>.replace "≠" "!="
    |>.replace "¬(" "not ("
    |>.replace "¬" "not "
    |>.replace "∀ " "all "
    |>.replace "∃ " "exists "
  s3.trimAscii.toString

/-! ## Case Tag Formatting -/

private def isSplitSuffix (s : String) : Bool :=
  s == "pos" || s == "neg" || s == "inl" || s == "inr" ||
  s == "isTrue" || s == "isFalse" || s == "intro" || s == "mk" ||
  s == "left" || s == "right" || s == "some" || s == "none" ||
  s == "ok" || s == "err" || s == "failed" || s == "loading" || s == "idle" ||
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

/-- Formats a goal tag into a human-readable Qed branch label (e.g. `action \`decrease\``, `rollback`). -/
def formatCaseTag (tag : Lean.Name) : String :=
  let raw := rootCaseTag tag
  if raw.isEmpty || raw == "_" || raw == "anonymous" then
    "this branch"
  else if raw == "init" then
    "initial state"
  else if raw == "_onRoute" then
    "route change"
  else if raw.startsWith "_query_" then
    s!"query `{(raw.drop 7).toString}`"
  else if raw.startsWith "_wsJoin_" then
    s!"subscribe `{(raw.drop 8).toString}` (`on_join`)"
  else if raw.startsWith "_wsMsg_" then
    s!"subscribe `{(raw.drop 7).toString}` (`on_event`)"
  else if raw.startsWith "_wsStatus_" then
    s!"subscribe `{(raw.drop 10).toString}` (status)"
  else if raw.startsWith "_specRollback_" then
    "`rollback` branch"
  else if raw.startsWith "_specConfirm_" then
    "`on_confirm` branch"
  else if raw.startsWith "_specCont_" then
    "speculative `predict` update"
  else if raw.startsWith "_specPre_" then
    "before speculative `await`"
  else if raw.startsWith "_specRes_" then
    "speculative resolution"
  else if raw.startsWith "_cont_" then
    "continuation after `await`"
  else if raw.startsWith "_form_reset_" then
    "form `reset`"
  else if raw.startsWith "_sub_" then
    "child component update"
  else if raw.startsWith "set_" then
    s!"handler updating `{(raw.drop 4).toString}`"
  else
    s!"action `{raw}`"

/-! ## MetaM Expression Cleaner & Pretty-Printer -/

open Lean Meta in
/-- Unwraps internal Qed wrapper projections/coercions (`QedVal.val`, `Field.val`, `Ensured.val`,
    `SrvIdx.toNat`, `SrvLiftOpt.liftOpt`, `QedSeqLit.ofList`, `id`) so pretty-printed proof
    obligations read like the user's source code. -/
def cleanQedExpr (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  Meta.transform e (pre := fun sub => do
    match sub with
    | .proj nm 0 inner =>
        if nm == `Qed.Field || nm == `Qed.Ensured then
          return .visit inner
        return .continue
    | _ =>
        let fn := sub.getAppFn
        let args := sub.getAppArgs
        match fn.constName? with
        | some `Qed.Lang.QedVal.val =>
            if args.size == 4 then return .visit args[3]!
            return .continue
        | some `Qed.Field.val =>
            if args.size == 3 then return .visit args[2]!
            return .continue
        | some `Qed.Ensured.val =>
            if args.size == 3 then return .visit args[2]!
            return .continue
        | some `Qed.Server.SrvIdx.toNat =>
            if args.size == 3 then return .visit args[2]!
            return .continue
        | some `Qed.Server.SrvLiftOpt.liftOpt =>
            if args.size == 4 then return .visit args[3]!
            return .continue
        | some `Qed.Lang.QedSeqLit.ofList =>
            if args.size == 4 then return .visit args[3]!
            return .continue
        | some ``id =>
            if args.size == 2 then return .visit args[1]!
            return .continue
        | _ => return .continue)

open Lean Meta in
/-- Pretty-prints a Lean expression in clean Qed-native ASCII syntax. -/
def ppQedExpr (e : Expr) (stripPrefixes : List String := []) : MetaM String := do
  let cleaned ← cleanQedExpr e
  let fmt ← Meta.ppExpr cleaned
  return toQedAscii fmt.pretty stripPrefixes

end Qed.Diag
