import Qed
import Examples.JsProbe
open Qed

namespace JsGate

def arith (i : Nat) : String :=
  let n : Int := (Int.ofNat i) - 7
  let a := n * n - 3 * n
  let b := if 0 < n then n else -n
  let c : Nat := i * i + 5
  s!"{a + b}|{b}|{c - 100}|{c % 7}|{n.natAbs}"

def strs : Array String := #["", "a", "héllo", "日本語!", "a<b&c", "  sp  ", "café", "x\ny\tz"]
def strop (i : Nat) : String :=
  let s := strs.getD i ""
  s!"{s.length}|{(s ++ "!?").take 4}|{s.drop 2}|{s.toList.reverse |> String.ofList}|{String.intercalate "," (s.splitOn "<")}"

def jsons : Array String :=
  #["null", "true", "[1,2,3]", "{\"a\":1,\"b\":[true,null]}", "\"x\\ny\"", "123", "[]", "{}",
    "[[1],[2,3],[]]", "{\"n\":-4,\"s\":\"hi\"}"]
def jsonRt (i : Nat) : String :=
  match Json.parse (jsons.getD i "null") with
  | .ok j    => Json.render j
  | .error e => s!"ERR {e}"

def dates : Array String := #["2024-02-29", "2023-02-29", "2024-13-01", "2024-06-15", "bad", "2024-1-5", "0001-12-31"]
def dateP (i : Nat) : String :=
  match Date.parse? (dates.getD i "") with
  | some d => d.toString
  | none   => "none"

def arrP (i : Nat) : String :=
  let a := (Array.range (i + 1)).map (fun x => x * 2)
  let b := a.filter (fun x => x % 3 == 0)
  s!"{a.toList}|{b.size}|{a.foldl (· + ·) 0}|{a.reverse.toList}"

router GateR where
  home => ""
  user (name : String) => "users"

def routes : Array String := #["/", "/users/ada", "/users/alan", "/users/a%20b", "/nope/x"]
def routeP (i : Nat) : String :=
  match (Router.fromURL (routes.getD i "") : Option GateR) with
  | some r => Router.toURL r
  | none   => "none"

def segP (i : Nat) : String :=
  let p := routes.getD i ""
  toString (((p.splitOn "/").filter (· ≠ "")).map decodeSeg)

schema ProtoRec where
  id  : String where 1 <= id.length, id.length <= 32
  qty : Nat    where qty <= 500
  raw : Bytes

private def protoRoundTrip {α : Type} [ToProto α] [FromProto α] (a : α) (eq : α → α → Bool) : String :=
  let bs := Proto.encode a
  let ok := match Proto.decode (α := α) bs with
    | .ok b    => eq a b
    | .error _ => false
  s!"{Proto.encodeHex bs}|{ok}"

def protoP (i : Nat) : String :=
  match i with
  | 0 => protoRoundTrip () (fun _ _ => true)
  | 1 => protoRoundTrip (true, false) (· == ·)
  | 2 => protoRoundTrip #[0, 1, 127, 128, 16384, 1000000007] (· == ·)
  | 3 => protoRoundTrip #[(0 : Int), -1, 1, -64, 64, -100000, 100000] (· == ·)
  | 4 => protoRoundTrip ((0xDEADBEEF : UInt32), (0x0102030405060708 : UInt64)) (· == ·)
  | 5 => protoRoundTrip #["", "héllo", "日本語!"] (· == ·)
  | 6 =>
      let grown := (List.range 300).foldl (fun acc n => acc.push (UInt8.ofNat (n % 256))) ByteArray.empty
      protoRoundTrip grown (fun a b => a.data == b.data)
  | 7 =>
      let opts : Array (Option (Array Int)) := #[none, some #[], some #[-42, 0, 999]]
      protoRoundTrip opts (· == ·)
  | 8 =>
      let r1 : Resource (String × Nat) := .idle
      let r2 : Resource (String × Nat) := .ok ("qed", 42)
      let r3 : Resource (String × Nat) := .failed "err"
      let eqR (x y : Resource (String × Nat)) : Bool :=
        match x, y with
        | .idle, .idle => true
        | .loading, .loading => true
        | .ok a, .ok b => a == b
        | .failed a, .failed b => a == b
        | _, _ => false
      String.intercalate ";" [protoRoundTrip r1 eqR, protoRoundTrip r2 eqR, protoRoundTrip r3 eqR]
  | 9 =>
      let recVal : ProtoRec := {
        id  := ⟨"tpil4", by dsimp [Codec.refine]; decide⟩
        qty := ⟨12, by dsimp [Codec.refine]; decide⟩
        raw := ByteArray.mk #[0x89, 0x50, 0x4E, 0x47]
      }
      protoRoundTrip recVal (fun a b =>
        a.id.val == b.id.val && a.qty.val == b.qty.val && a.raw.data == b.raw.data)
  | _ => ""

def run (probe i : Nat) : String :=
  match probe with
  | 0 => JsProbe.renderCase i
  | 1 => JsProbe.diffCase i
  | 2 => arith i
  | 3 => strop i
  | 4 => jsonRt i
  | 5 => dateP i
  | 6 => arrP i
  | 7 => routeP i
  | 8 => segP i
  | 9 => JsProbe.childPatchCase i
  | 10 => JsProbe.wideRenderCase i
  | 11 => JsProbe.keyIndexCase i
  | 12 => protoP i
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
  | 9 => 5
  | 10 => 5
  | 11 => 6
  | 12 => 10
  | _ => 0

def probeCount : Nat := 13

def names : Array String := #["render", "diff", "arith", "string", "json", "date", "array", "router", "seg",
  "childPatch", "wideRender", "keyIndex", "proto"]

def jsonStr (s : String) : String :=
  "\"" ++ (s.foldl (init := "") fun acc c =>
    acc ++ (match c with
      | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\t' => "\\t" | '\r' => "\\r"
      | c => if c.toNat < 32 then "" else toString c)) ++ "\""

def emitOracle : IO Unit := do
  let mut out : Array String := #[]
  for p in [0:probeCount] do
    for i in [0:counts p] do
      out := out.push s!"{p}\t{i}\t{jsonStr (run p i)}"
  IO.print (String.intercalate "\n" out.toList)

end JsGate
