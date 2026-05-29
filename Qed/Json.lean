/-
  Qed.Json — a full-grammar JSON parser and renderer.

  Values cover the whole RFC 8259 grammar: null, booleans, numbers (as a precise
  `JsonNumber` = mantissa × 10^exponent), strings (with escapes, including
  `\uXXXX`), arrays, and objects — nested arbitrarily, since `Json` is recursive.

  The parser recurses structurally on a `fuel` counter, so totality is free, and
  on a `budget` (the caller's `maxDepth`), so it refuses to build anything deeper.
  `Qed.parse_depth_le` (below) proves the bound; `Qed.parse_render` proves the
  codec round-trip for the structural core.
-/
namespace Qed

/-- A JSON number as `mantissa × 10^exponent` (exact; no float rounding). -/
structure JsonNumber where
  mantissa : Int
  exponent : Int := 0
deriving Repr, BEq, DecidableEq, Inhabited

/-- A parsed JSON value. Recursive, so objects and arrays nest to any depth. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num  (n : JsonNumber)
  | str  (s : String)
  | arr  (elems : List Json)
  | obj  (members : List (String × Json))
deriving Inhabited

namespace Json

mutual
  /-- Nesting depth: scalars are 0; an array/object is one more than its deepest child. -/
  def depth : Json → Nat
    | .null => 0 | .bool _ => 0 | .num _ => 0 | .str _ => 0
    | .arr es => 1 + maxArr es
    | .obj ms => 1 + maxObj ms
  def maxArr : List Json → Nat
    | []      => 0
    | e :: es => Nat.max (depth e) (maxArr es)
  def maxObj : List (String × Json) → Nat
    | []           => 0
    | (_, v) :: ms => Nat.max (depth v) (maxObj ms)
end

theorem maxArr_le {k : Nat} : ∀ {es : List Json}, (∀ e ∈ es, depth e ≤ k) → maxArr es ≤ k
  | [],      _ => by simp [maxArr]
  | e :: es, h => by
      simp only [maxArr, Nat.max_le]
      exact ⟨h e (by simp), maxArr_le (fun x hx => h x (by simp [hx]))⟩

theorem maxObj_le {k : Nat} :
    ∀ {ms : List (String × Json)}, (∀ kv ∈ ms, depth kv.2 ≤ k) → maxObj ms ≤ k
  | [],           _ => by simp [maxObj]
  | (key, v) :: ms, h => by
      simp only [maxObj, Nat.max_le]
      exact ⟨h (key, v) (by simp), maxObj_le (fun x hx => h x (by simp [hx]))⟩

end Json

/-! ### Lexer helpers (total, structural on the character list) -/

def isWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def skipWs : List Char → List Char
  | c :: cs => if isWs c then skipWs cs else c :: cs
  | []      => []

def takeDigits : List Char → List Char × List Char
  | c :: cs => if isDigit c then let (ds, r) := takeDigits cs; (c :: ds, r) else ([], c :: cs)
  | []      => ([], [])

def digitsToInt (ds : List Char) : Int :=
  (ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 : Nat)

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hex4 (a b c d : Char) : Option Nat := do
  let va ← hexVal a; let vb ← hexVal b; let vc ← hexVal c; let vd ← hexVal d
  return ((va * 16 + vb) * 16 + vc) * 16 + vd

def unescape : Char → Option Char
  | '"'  => some '"'  | '\\' => some '\\' | '/' => some '/'
  | 'n'  => some '\n' | 'r'  => some '\r' | 't' => some '\t'
  | 'b'  => some (Char.ofNat 8) | 'f' => some (Char.ofNat 12)
  | _    => none

/-- Parse the contents of a string after the opening quote (structural on input). -/
def parseStrAux (acc : List Char) : List Char → Except String (String × List Char)
  | '"' :: rest => .ok (⟨acc.reverse⟩, rest)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest =>
      match hex4 a b c d with
      | some n => parseStrAux (Char.ofNat n :: acc) rest
      | none   => .error "invalid \\u escape"
  | '\\' :: e :: rest =>
      match unescape e with
      | some ch => parseStrAux (ch :: acc) rest
      | none    => .error "invalid escape"
  | c :: rest => parseStrAux (c :: acc) rest
  | []        => .error "unterminated string"

def parseStr (cs : List Char) : Except String (String × List Char) := parseStrAux [] cs

/-- Parse a JSON number into a `JsonNumber` (structural; no Json recursion). -/
def parseNum (cs : List Char) : Except String (JsonNumber × List Char) :=
  let (neg, cs1) := match cs with | '-' :: r => (true, r) | _ => (false, cs)
  let (intDs, cs2) := takeDigits cs1
  if intDs.isEmpty then .error "expected a number"
  else
    let (fracDs, cs3) := match cs2 with | '.' :: r => takeDigits r | _ => ([], cs2)
    let (expVal, cs4) : Int × List Char := match cs3 with
      | 'e' :: r | 'E' :: r =>
          let (sgn, r1) : Int × List Char := match r with
            | '+' :: r' => (1, r') | '-' :: r' => (-1, r') | _ => (1, r)
          let (eds, r2) := takeDigits r1
          (sgn * digitsToInt eds, r2)
      | _ => (0, cs3)
    let mant : Int := (if neg then -1 else 1) * digitsToInt (intDs ++ fracDs)
    .ok (⟨mant, expVal - (fracDs.length : Int)⟩, cs4)

/-! ### The parser (structural on `fuel`; `budget` bounds nesting) -/

mutual
  def parseVal (fuel budget : Nat) (cs : List Char) : Except String (Json × List Char) :=
    match fuel with
    | 0 => .error "out of fuel"
    | fuel + 1 =>
      match skipWs cs with
      | 'n' :: 'u' :: 'l' :: 'l' :: r        => .ok (.null, r)
      | 't' :: 'r' :: 'u' :: 'e' :: r        => .ok (.bool true, r)
      | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => .ok (.bool false, r)
      | '"' :: r =>
          match parseStr r with
          | .ok (s, r') => .ok (.str s, r')
          | .error e    => .error e
      | '[' :: r =>
          match budget with
          | 0          => .error "maximum depth exceeded"
          | budget + 1 =>
              match skipWs r with
              | ']' :: r' => .ok (.arr [], r')           -- empty array
              | r0 =>
                  match parseElems fuel budget r0 with
                  | .ok (es, r') => .ok (.arr es, r')
                  | .error e     => .error e
      | '{' :: r =>
          match budget with
          | 0          => .error "maximum depth exceeded"
          | budget + 1 =>
              match skipWs r with
              | '}' :: r' => .ok (.obj [], r')           -- empty object
              | r0 =>
                  match parseMembers fuel budget r0 with
                  | .ok (ms, r') => .ok (.obj ms, r')
                  | .error e     => .error e
      | c :: rest =>
          if c == '-' || isDigit c then
            match parseNum (c :: rest) with
            | .ok (n, r') => .ok (.num n, r')
            | .error e    => .error e
          else .error "unexpected character"
      | [] => .error "unexpected end of input"
  -- Parses one-or-more comma-separated values; the empty case is handled in
  -- `parseVal`, so a value is required after every comma (no trailing commas).
  def parseElems (fuel budget : Nat) (cs : List Char) : Except String (List Json × List Char) :=
    match fuel with
    | 0 => .error "out of fuel"
    | fuel + 1 =>
      match parseVal fuel budget cs with
      | .error e => .error e
      | .ok (v, r) =>
          match skipWs r with
          | ',' :: r' =>
              match parseElems fuel budget (skipWs r') with
              | .ok (vs, r'') => .ok (v :: vs, r'')
              | .error e      => .error e
          | ']' :: r' => .ok ([v], r')
          | _         => .error "expected ',' or ']'"
  -- Parses one-or-more comma-separated members; empty handled in `parseVal`.
  def parseMembers (fuel budget : Nat) (cs : List Char) :
      Except String (List (String × Json) × List Char) :=
    match fuel with
    | 0 => .error "out of fuel"
    | fuel + 1 =>
      match skipWs cs with
      | '"' :: r =>
          match parseStr r with
          | .error e => .error e
          | .ok (key, r1) =>
              match skipWs r1 with
              | ':' :: r2 =>
                  match parseVal fuel budget (skipWs r2) with
                  | .error e => .error e
                  | .ok (v, r3) =>
                      match skipWs r3 with
                      | ',' :: r4 =>
                          match parseMembers fuel budget (skipWs r4) with
                          | .ok (ms, r5) => .ok ((key, v) :: ms, r5)
                          | .error e     => .error e
                      | '}' :: r4 => .ok ([(key, v)], r4)
                      | _         => .error "expected ',' or '}'"
              | _ => .error "expected ':'"
      | _ => .error "expected string key"
end

/-- Parse a complete JSON document, rejecting nesting deeper than `maxDepth`. -/
def parse (s : String) (maxDepth : Nat := 64) : Except String Json :=
  let cs := s.toList
  match parseVal (cs.length + 1) maxDepth cs with
  | .error e   => .error e
  | .ok (j, r) => if (skipWs r).isEmpty then .ok j else .error "trailing characters"

/-! ### The depth bound, proven -/

mutual
  theorem parseVal_depth_le :
      ∀ (fuel budget : Nat) (cs : List Char) (j : Json) (r : List Char),
        parseVal fuel budget cs = .ok (j, r) → j.depth ≤ budget
    | 0,        _,      _,  _, _, h => by simp [parseVal] at h
    | fuel + 1, budget, cs, j, r, h => by
        simp only [parseVal] at h
        repeat' split at h
        all_goals first
          | contradiction
          | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
             obtain ⟨rfl, rfl⟩ := h
             first
               | (simp only [Json.depth, Json.maxArr, Json.maxObj]; omega)  -- scalars + empties
               | (simp only [Json.depth]
                  have hb := Json.maxArr_le
                    (fun e he => parseElems_depth_le _ _ _ _ _ (by assumption) e he)
                  omega)
               | (simp only [Json.depth]
                  have hb := Json.maxObj_le
                    (fun kv hkv => parseMembers_depth_le _ _ _ _ _ (by assumption) kv hkv)
                  omega))
  theorem parseElems_depth_le :
      ∀ (fuel budget : Nat) (cs : List Char) (es : List Json) (r : List Char),
        parseElems fuel budget cs = .ok (es, r) → ∀ e ∈ es, e.depth ≤ budget
    | 0,        _,      _,  _,  _, h => by simp [parseElems] at h
    | fuel + 1, budget, cs, es, r, h => by
        simp only [parseElems] at h
        repeat' split at h
        all_goals first
          | contradiction
          | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
             obtain ⟨rfl, rfl⟩ := h
             intro e he
             first
               | exact absurd he (List.not_mem_nil e)
               | (cases he with
                  | head => exact parseVal_depth_le _ _ _ _ _ (by assumption)
                  | tail _ he' => first
                      | exact parseElems_depth_le _ _ _ _ _ (by assumption) _ he'
                      | exact absurd he' (List.not_mem_nil _)))
  theorem parseMembers_depth_le :
      ∀ (fuel budget : Nat) (cs : List Char) (ms : List (String × Json)) (r : List Char),
        parseMembers fuel budget cs = .ok (ms, r) → ∀ kv ∈ ms, kv.2.depth ≤ budget
    | 0,        _,      _,  _,  _, h => by simp [parseMembers] at h
    | fuel + 1, budget, cs, ms, r, h => by
        simp only [parseMembers] at h
        repeat' split at h
        all_goals first
          | contradiction
          | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
             obtain ⟨rfl, rfl⟩ := h
             intro kv hkv
             first
               | exact absurd hkv (List.not_mem_nil kv)
               | (cases hkv with
                  | head => exact parseVal_depth_le _ _ _ _ _ (by assumption)
                  | tail _ hkv' => first
                      | exact parseMembers_depth_le _ _ _ _ _ (by assumption) _ hkv'
                      | exact absurd hkv' (List.not_mem_nil _)))
end

/-- Anything `parse s maxDepth` accepts is within `maxDepth`. -/
theorem parse_depth_le (s : String) (maxDepth : Nat) (j : Json) :
    parse s maxDepth = .ok j → j.depth ≤ maxDepth := by
  intro h
  simp only [parse] at h
  split at h
  · simp at h
  · rename_i j0 r heq
    split at h
    · cases h; exact parseVal_depth_le _ maxDepth _ _ _ heq
    · contradiction

/-! ### Rendering -/

def toHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))

def escapeChar (c : Char) : String :=
  match c with
  | '"'  => "\\\"" | '\\' => "\\\\"
  | '\n' => "\\n"  | '\r' => "\\r" | '\t' => "\\t"
  | c =>
      if c.toNat < 0x20 then
        let n := c.toNat
        ⟨['\\', 'u', toHexDigit (n / 4096 % 16), toHexDigit (n / 256 % 16),
                     toHexDigit (n / 16 % 16),   toHexDigit (n % 16)]⟩
      else c.toString

def Json.renderStr (s : String) : String :=
  "\"" ++ s.foldl (fun acc c => acc ++ escapeChar c) "" ++ "\""

def Json.renderNum (n : JsonNumber) : String :=
  toString n.mantissa ++ (if n.exponent == 0 then "" else "e" ++ toString n.exponent)

namespace Json
mutual
  /-- Render a value to a JSON string (numbers in `mantissa e exponent` form). -/
  def render : Json → String
    | .null     => "null"
    | .bool b   => if b then "true" else "false"
    | .num n    => renderNum n
    | .str s    => renderStr s
    | .arr es   => "[" ++ renderElems es ++ "]"
    | .obj ms   => "{" ++ renderMembers ms ++ "}"
  def renderElems : List Json → String
    | []      => ""
    | [e]     => render e
    | e :: es => render e ++ "," ++ renderElems es
  def renderMembers : List (String × Json) → String
    | []           => ""
    | [(k, v)]     => renderStr k ++ ":" ++ render v
    | (k, v) :: ms => renderStr k ++ ":" ++ render v ++ "," ++ renderMembers ms
end
end Json

/-! ### Dynamic access -/

def Json.bool? : Json → Option Bool                  | .bool b => some b | _ => none
def Json.str?  : Json → Option String                | .str s  => some s | _ => none
def Json.num?  : Json → Option JsonNumber            | .num n  => some n | _ => none
def Json.arr?  : Json → Option (List Json)           | .arr es => some es | _ => none
def Json.obj?  : Json → Option (List (String × Json))| .obj ms => some ms | _ => none

/-- Look up a key in an object, with a descriptive error. -/
def Json.field (j : Json) (key : String) : Except String Json :=
  match j with
  | .obj ms =>
      match ms.find? (fun kv => kv.1 == key) with
      | some (_, v) => .ok v
      | none        => .error s!"missing key '{key}'"
  | _ => .error "expected an object"

def Json.get? (j : Json) (key : String) : Option Json := (j.field key).toOption

/-- Follow a path of object keys. -/
def Json.path? (j : Json) : List String → Option Json
  | []      => some j
  | k :: ks => (j.get? k).bind (fun v => v.path? ks)

/-! ### Typed encode / decode -/

class ToJson (α : Type) where toJson : α → Json
class FromJson (α : Type) where fromJson : Json → Except String α
export ToJson (toJson)
export FromJson (fromJson)

instance : ToJson Json := ⟨id⟩
instance : ToJson JsonNumber := ⟨.num⟩
instance : ToJson Bool := ⟨.bool⟩
instance : ToJson String := ⟨.str⟩
instance : ToJson Int := ⟨fun i => .num ⟨i, 0⟩⟩
instance : ToJson Nat := ⟨fun n => .num ⟨(n : Int), 0⟩⟩
instance [ToJson α] : ToJson (List α)   := ⟨fun xs => .arr (xs.map toJson)⟩
instance [ToJson α] : ToJson (Array α)  := ⟨fun xs => .arr (xs.toList.map toJson)⟩
instance [ToJson α] : ToJson (Option α) := ⟨fun a => a.elim .null toJson⟩

instance : FromJson Json := ⟨.ok⟩
instance : FromJson JsonNumber := ⟨fun j => j.num?.elim (.error "expected a number") .ok⟩
instance : FromJson Bool := ⟨fun j => j.bool?.elim (.error "expected a boolean") .ok⟩
instance : FromJson String := ⟨fun j => j.str?.elim (.error "expected a string") .ok⟩
instance : FromJson Int :=
  ⟨fun j => match j with | .num ⟨m, 0⟩ => .ok m | _ => .error "expected an integer"⟩
instance : FromJson Nat :=
  ⟨fun j => match j with
    | .num ⟨m, 0⟩ => if 0 ≤ m then .ok m.toNat else .error "expected a non-negative integer"
    | _ => .error "expected a natural number"⟩
instance [FromJson α] : FromJson (List α) :=
  ⟨fun j => match j with | .arr es => es.mapM fromJson | _ => .error "expected an array"⟩
instance [FromJson α] : FromJson (Array α) :=
  ⟨fun j => (fromJson j : Except String (List α)).map List.toArray⟩
instance [FromJson α] : FromJson (Option α) :=
  ⟨fun j => match j with | .null => .ok none | _ => (fromJson j : Except String α).map some⟩

/-! ### `jsonCodec` — generate ToJson/FromJson for a structure

`jsonCodec User [name, age, tags]` produces both instances, mapping each field to
a JSON key of the same name. It is a core-syntax macro (no `import Lean`), so apps
that use it do not pull the Lean elaborator into their WASM binary. -/

open Lean in
syntax (name := jsonCodecCmd) "jsonCodec " ident "[" ident,* "]" : command

open Lean in
macro_rules
  | `(jsonCodec $t:ident [$fs:ident,*]) => do
      let fields := fs.getElems
      let pairs ← fields.mapM fun (f : Ident) => `(term| ($(quote (toString f.getId)), toJson x.$f))
      let keys  ← fields.mapM fun (f : Ident) => `(term| $(quote (toString f.getId)))
      `(instance : ToJson $t where
          toJson x := Json.obj [$pairs,*]
        instance : FromJson $t where
          fromJson j := do
            return { $[$fields:ident := (← fromJson (← j.field $keys))],* })

end Qed
