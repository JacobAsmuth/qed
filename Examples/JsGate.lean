/-
  The differential gate: a registry of probe functions, each `Nat → String` (a case
  index → a stringified result). The harness runs every `(probe, i)` natively in Lean
  and (transpiled) under node and asserts identical output, so any emitter/extern/
  representation divergence shows up as a mismatch. Add a probe by extending `run`,
  `counts`, and `probeCount` — it then covers that area of the framework automatically.
-/
import Qed
import Examples.JsProbe
open Qed

namespace JsGate

/-- Int/Nat arithmetic: mul/sub/add, `decLt`, `neg`, truncated `Nat.sub`, `emod`. -/
def arith (i : Nat) : String :=
  let n : Int := (Int.ofNat i) - 7
  let a := n * n - 3 * n
  let b := if 0 < n then n else -n
  let c : Nat := i * i + 5
  s!"{a + b}|{b}|{c - 100}|{c % 7}|{n.natAbs}"

def strs : Array String := #["", "a", "héllo", "日本語!", "a<b&c", "  sp  ", "café", "x\ny\tz"]
/-- String ops, exercising the UTF-8 byte-offset `Pos` layer: `length`, `++`, `take`,
    `drop`, `reverse`, `splitOn`. -/
def strop (i : Nat) : String :=
  let s := strs.getD i ""
  s!"{s.length}|{(s ++ "!?").take 4}|{s.drop 2}|{s.toList.reverse.asString}|{String.intercalate "," (s.splitOn "<")}"

def jsons : Array String :=
  #["null", "true", "[1,2,3]", "{\"a\":1,\"b\":[true,null]}", "\"x\\ny\"", "123", "[]", "{}",
    "[[1],[2,3],[]]", "{\"n\":-4,\"s\":\"hi\"}"]
/-- JSON parse → render round-trip (the fuel parser + renderer + escapes). -/
def jsonRt (i : Nat) : String :=
  match Json.parse (jsons.getD i "null") with
  | .ok j    => Json.render j
  | .error e => s!"ERR {e}"

def dates : Array String := #["2024-02-29", "2023-02-29", "2024-13-01", "2024-06-15", "bad", "2024-1-5", "0001-12-31"]
/-- Verified `Date` parse → render (leap-year + calendar validation). -/
def dateP (i : Nat) : String :=
  match Date.parse? (dates.getD i "") with
  | some d => d.toString
  | none   => "none"

/-- Array + higher-order closures (`pap`/`ap`): `range`, `map`, `filter`, `foldl`. -/
def arrP (i : Nat) : String :=
  let a := (Array.range (i + 1)).map (fun x => x * 2)
  let b := a.filter (fun x => x % 3 == 0)
  s!"{a.toList}|{b.size}|{a.foldl (· + ·) 0}|{a.reverse.toList}"

-- A self-contained router for the probe, so the gate stays independent of any example app
-- (an app refactor must never perturb the differential oracle).
router GateR where
  home => ""
  user (name : String) => "users"

def routes : Array String := #["/", "/users/ada", "/users/alan", "/users/a%20b", "/nope/x"]
/-- The verified `router` — percent-codec + `fromURL` parse + `toURL` print round-trip. -/
def routeP (i : Nat) : String :=
  match (Router.fromURL (routes.getD i "") : Option GateR) with
  | some r => Router.toURL r
  | none   => "none"

/-- The decoded segment list `fromURL` feeds to `parse` — isolates split/filter/decodeSeg. -/
def segP (i : Nat) : String :=
  let p := routes.getD i ""
  toString (((p.splitOn "/").filter (· ≠ "")).map decodeSeg)

/-- A probe dispatcher: `run probe i` is the i-th case of the named probe. -/
def run (probe i : Nat) : String :=
  match probe with
  | 0 => JsProbe.renderCase i      -- Html.render (escaping, attrs, void, signals, lazy)
  | 1 => JsProbe.diffCase i        -- applyPatch (diff a b) a, rendered (diff_apply)
  | 2 => arith i
  | 3 => strop i
  | 4 => jsonRt i
  | 5 => dateP i
  | 6 => arrP i
  | 7 => routeP i
  | 8 => segP i
  | _ => ""

def counts (probe : Nat) : Nat :=
  match probe with
  | 0 => JsProbe.treeCount
  | 1 => JsProbe.pairCount
  | 2 => 32
  | 3 => strs.size
  | 4 => jsons.size
  | 5 => dates.size
  | 6 => 12
  | 7 => routes.size
  | 8 => routes.size
  | _ => 0

def probeCount : Nat := 9

def names : Array String := #["render", "diff", "arith", "string", "json", "date", "array", "router", "seg"]

/-- A JSON string literal, so outputs containing tabs/newlines survive the line format. -/
def jsonStr (s : String) : String :=
  "\"" ++ (s.foldl (init := "") fun acc c =>
    acc ++ (match c with
      | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\t' => "\\t" | '\r' => "\\r"
      | c => if c.toNat < 32 then "" else toString c)) ++ "\""

/-- Dump the oracle: one `probe<TAB>i<TAB>json(output)` line per case. -/
def emitOracle : IO Unit := do
  let mut out : Array String := #[]
  for p in [0:probeCount] do
    for i in [0:counts p] do
      out := out.push s!"{p}\t{i}\t{jsonStr (run p i)}"
  IO.print (String.intercalate "\n" out.toList)

end JsGate
