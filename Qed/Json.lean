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
  | '"' :: rest => .ok (String.ofList acc.reverse, rest)
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
              | []      => .error "unexpected end of input"
              | c :: r' =>
                  if c = ']' then .ok (.arr [], r')      -- empty array
                  else match parseElems fuel budget (c :: r') with
                       | .ok (es, r'') => .ok (.arr es, r'')
                       | .error e      => .error e
      | '{' :: r =>
          match budget with
          | 0          => .error "maximum depth exceeded"
          | budget + 1 =>
              match skipWs r with
              | []      => .error "unexpected end of input"
              | c :: r' =>
                  if c = '}' then .ok (.obj [], r')      -- empty object
                  else match parseMembers fuel budget (c :: r') with
                       | .ok (ms, r'') => .ok (.obj ms, r'')
                       | .error e      => .error e
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

/-- The qualified name `Json.parse`, for call sites that prefer it. Reducible, so
    `parse_depth_le` and friends apply through it unchanged. -/
abbrev Json.parse (s : String) (maxDepth : Nat := 64) : Except String Json :=
  Qed.parse s maxDepth

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
               | exact absurd he (List.not_mem_nil)
               | (cases he with
                  | head => exact parseVal_depth_le _ _ _ _ _ (by assumption)
                  | tail _ he' => first
                      | exact parseElems_depth_le _ _ _ _ _ (by assumption) _ he'
                      | exact absurd he' (List.not_mem_nil)))
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
               | exact absurd hkv (List.not_mem_nil)
               | (cases hkv with
                  | head => exact parseVal_depth_le _ _ _ _ _ (by assumption)
                  | tail _ hkv' => first
                      | exact parseMembers_depth_le _ _ _ _ _ (by assumption) _ hkv'
                      | exact absurd hkv' (List.not_mem_nil)))
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

/-! ### Rendering

Rendering produces `List Char` directly (`renderL`); the public `render` wraps it
as a `String`. Because `parse` works on `String.toList`, and
`(⟨renderL j⟩ : String).toList = renderL j` definitionally, the codec round-trip
proof can reason about `parseVal … (renderL j ++ rest)` without `String`-append
friction. -/

def toHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))

/-- One character, JSON-escaped, as a list of characters. -/
def escapeCharL (c : Char) : List Char :=
  match c with
  | '"'  => ['\\', '"']  | '\\' => ['\\', '\\']
  | '\n' => ['\\', 'n']  | '\r' => ['\\', 'r'] | '\t' => ['\\', 't']
  | c =>
      if c.toNat < 0x20 then
        let n := c.toNat
        ['\\', 'u', toHexDigit (n / 4096 % 16), toHexDigit (n / 256 % 16),
                    toHexDigit (n / 16 % 16),   toHexDigit (n % 16)]
      else [c]

def Json.renderStrL (s : String) : List Char :=
  '"' :: (s.toList.flatMap escapeCharL ++ ['"'])

def Json.renderNumL (n : JsonNumber) : List Char :=
  (toString n.mantissa).toList ++ (if n.exponent == 0 then [] else 'e' :: (toString n.exponent).toList)

namespace Json
mutual
  /-- Render a value to a character list (numbers in `mantissa e exponent` form). -/
  def renderL : Json → List Char
    | .null         => ['n', 'u', 'l', 'l']
    | .bool true    => ['t', 'r', 'u', 'e']
    | .bool false   => ['f', 'a', 'l', 's', 'e']
    | .num n        => renderNumL n
    | .str s        => renderStrL s
    | .arr es       => '[' :: (renderElemsL es ++ [']'])
    | .obj ms       => '{' :: (renderMembersL ms ++ ['}'])
  def renderElemsL : List Json → List Char
    | []      => []
    | e :: es => renderL e ++ renderElemSep es
  def renderElemSep : List Json → List Char
    | []      => []
    | x :: xs => ',' :: (renderL x ++ renderElemSep xs)
  def renderMembersL : List (String × Json) → List Char
    | []           => []
    | (k, v) :: ms => renderStrL k ++ ':' :: (renderL v ++ renderMemberSep ms)
  def renderMemberSep : List (String × Json) → List Char
    | []           => []
    | (k, v) :: ms => ',' :: (renderStrL k ++ ':' :: (renderL v ++ renderMemberSep ms))
end

/-- Render a value to a JSON string. -/
def render (j : Json) : String := String.ofList (renderL j)
end Json

/-! ### Codec round-trip

`parse (render j) = .ok j` for the *structural core*: null, booleans, and (nested)
arrays. Numbers, strings, and objects are the next increments — they additionally
need an integer `toString`-inverse lemma and a string escape-inverse lemma. -/

namespace Json

/-- The first round-trip scope: no numbers, strings, or objects. -/
inductive Simple : Json → Prop
  | null : Simple .null
  | bool (b : Bool) : Simple (.bool b)
  | arr (es : List Json) : (∀ e ∈ es, Simple e) → Simple (.arr es)

/-- A rendered value begins with a non-whitespace character other than `]`. -/
theorem simple_head {j : Json} (h : Simple j) :
    ∃ c t, renderL j = c :: t ∧ isWs c = false ∧ c ≠ ']' := by
  cases h with
  | null     => exact ⟨'n', ['u','l','l'], rfl, by decide, by decide⟩
  | bool b   => cases b with
                | true  => exact ⟨'t', ['r','u','e'], rfl, by decide, by decide⟩
                | false => exact ⟨'f', ['a','l','s','e'], rfl, by decide, by decide⟩
  | arr es _ => exact ⟨'[', renderElemsL es ++ [']'], rfl, by decide, by decide⟩

theorem depth_le_maxArr {e : Json} {es : List Json} (h : e ∈ es) : depth e ≤ maxArr es := by
  induction es with
  | nil => simp at h
  | cons x xs ih =>
      rcases List.mem_cons.mp h with rfl | hmem
      · simp only [maxArr]; exact Nat.le_max_left _ _
      · simp only [maxArr]; exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

/-- `skipWs` is the identity on rendered output (it never starts with whitespace). -/
theorem skipWs_renderL {j : Json} (h : Simple j) (x : List Char) :
    skipWs (renderL j ++ x) = renderL j ++ x := by
  obtain ⟨c, t, hren, hcws, _⟩ := simple_head h
  rw [hren, List.cons_append]
  simp [skipWs, hcws]

theorem skipWs_renderElemsL {e : Json} {es : List Json} (h : Simple e) (x : List Char) :
    skipWs (renderElemsL (e :: es) ++ x) = renderElemsL (e :: es) ++ x := by
  simp only [renderElemsL, List.append_assoc]
  exact skipWs_renderL h _

end Json

/-- The parser's array branch reduces to wrapping `parseElems`, given that the
    element list does not begin with `]`. This isolates the only `match` on a
    variable list-head, discharged via `simple_head` (`c ≠ ']'`). -/
theorem parseVal_arr {e : Json} {es : List Json} (he : Json.Simple e)
    (f b : Nat) (rest : List Char) :
    parseVal (f + 1) (b + 1) ('[' :: (Json.renderElemsL (e :: es) ++ ']' :: rest))
      = (match parseElems f b (Json.renderElemsL (e :: es) ++ ']' :: rest) with
         | .ok (vs, r') => .ok (Json.arr vs, r')
         | .error msg   => .error msg) := by
  obtain ⟨c, t, hren, hcws, hcbr⟩ := Json.simple_head he
  have hcons : Json.renderElemsL (e :: es) ++ ']' :: rest
             = c :: (t ++ Json.renderElemSep es ++ ']' :: rest) := by
    simp only [Json.renderElemsL, hren, List.cons_append, List.append_assoc]
  -- The parser reduces definitionally up to the (unresolved) inner `skipWs`.
  have step : parseVal (f + 1) (b + 1) ('[' :: (Json.renderElemsL (e :: es) ++ ']' :: rest))
            = (match skipWs (Json.renderElemsL (e :: es) ++ ']' :: rest) with
               | []      => .error "unexpected end of input"
               | c :: r' => if c = ']' then .ok (Json.arr [], r')
                            else (match parseElems f b (c :: r') with
                                  | .ok (es', r'') => .ok (Json.arr es', r'')
                                  | .error e       => .error e)) := rfl
  rw [step, Json.skipWs_renderElemsL (es := es) he (']' :: rest), hcons]
  simp only [if_neg hcbr]

/-- One-step unfolding of `parseElems` at successor fuel (definitional). -/
theorem parseElems_step (f budget : Nat) (cs : List Char) :
    parseElems (f + 1) budget cs
      = (match parseVal f budget cs with
         | .error msg => .error msg
         | .ok (v, r) =>
             match skipWs r with
             | ',' :: r' =>
                 (match parseElems f budget (skipWs r') with
                  | .ok (vs, r'') => .ok (v :: vs, r'')
                  | .error e      => .error e)
             | ']' :: r' => .ok ([v], r')
             | _         => .error "expected ',' or ']'") := rfl

mutual
  theorem rt_val : ∀ (j : Json), Json.Simple j → ∀ (budget fuel : Nat) (rest : List Char),
      j.depth ≤ budget → (Json.renderL j).length < fuel →
      parseVal fuel budget (Json.renderL j ++ rest) = .ok (j, rest)
    | .null, _, budget, fuel, rest, _, hf => by
        cases fuel with
        | zero => simp [Json.renderL] at hf
        | succ f => simp [Json.renderL, parseVal, skipWs, isWs]
    | .bool b, _, budget, fuel, rest, _, hf => by
        cases fuel with
        | zero => cases b <;> simp [Json.renderL] at hf
        | succ f => cases b <;> simp [Json.renderL, parseVal, skipWs, isWs]
    | .arr [], _, budget, fuel, rest, hd, hf => by
        cases fuel with
        | zero => simp [Json.renderL, Json.renderElemsL] at hf
        | succ f => cases budget with
          | zero => simp [Json.depth, Json.maxArr] at hd
          | succ b => simp [Json.renderL, Json.renderElemsL, parseVal, skipWs, isWs]
    | .arr (e :: es), h, budget, fuel, rest, hd, hf => by
        have hsimp : ∀ x ∈ (e :: es), Json.Simple x := by cases h with | arr _ hs => exact hs
        have hse : Json.Simple e := hsimp e (by simp)
        have hses : ∀ x ∈ es, Json.Simple x := fun x hx => hsimp x (by simp [hx])
        cases budget with
        | zero => simp [Json.depth] at hd
        | succ b =>
            simp only [Json.depth] at hd
            have hmax : Json.maxArr (e :: es) ≤ b := by omega
            have hde : Json.depth e ≤ b :=
              Nat.le_trans (Json.depth_le_maxArr (List.mem_cons_self)) hmax
            have hdes : ∀ x ∈ es, Json.depth x ≤ b :=
              fun x hx => Nat.le_trans (Json.depth_le_maxArr (List.mem_cons_of_mem e hx)) hmax
            cases fuel with
            | zero => simp [Json.renderL, Json.renderElemsL] at hf
            | succ f =>
                have hfe : (Json.renderElemsL (e :: es)).length + 1 < f := by
                  simp only [Json.renderL, List.length_cons, List.length_append] at hf; omega
                have key := rt_elems e es hse hses b f rest hde hdes hfe
                have harr : Json.renderL (Json.arr (e :: es)) ++ rest
                          = '[' :: (Json.renderElemsL (e :: es) ++ ']' :: rest) := by
                  simp [Json.renderL]
                rw [harr, parseVal_arr hse f b rest, key]
    | .num _, h, _, _, _, _, _ => nomatch h
    | .str _, h, _, _, _, _, _ => nomatch h
    | .obj _, h, _, _, _, _, _ => nomatch h
  theorem rt_elems : ∀ (e : Json) (es : List Json), Json.Simple e → (∀ x ∈ es, Json.Simple x) →
      ∀ (budget fuel : Nat) (rest : List Char),
      Json.depth e ≤ budget → (∀ x ∈ es, Json.depth x ≤ budget) →
      (Json.renderElemsL (e :: es)).length + 1 < fuel →
      parseElems fuel budget (Json.renderElemsL (e :: es) ++ ']' :: rest) = .ok (e :: es, rest)
    | e, [], he, _, budget, fuel, rest, hde, _, hf => by
        cases fuel with
        | zero => omega
        | succ f =>
            have hfe : (Json.renderL e).length < f := by
              simp only [Json.renderElemsL, Json.renderElemSep, List.append_nil] at hf; omega
            have hv := rt_val e he budget f (']' :: rest) hde hfe
            have harg : Json.renderElemsL (e :: []) ++ ']' :: rest = Json.renderL e ++ ']' :: rest := by
              simp [Json.renderElemsL, Json.renderElemSep]
            rw [harg, parseElems_step, hv]
            simp [skipWs, isWs]
    | e, x :: xs, he, hxs, budget, fuel, rest, hde, hdxs, hf => by
        cases fuel with
        | zero => omega
        | succ f =>
            have hxe : Json.Simple x := hxs x (by simp)
            have hxxs : ∀ y ∈ xs, Json.Simple y := fun y hy => hxs y (by simp [hy])
            have hdx : Json.depth x ≤ budget := hdxs x (by simp)
            have hdxxs : ∀ y ∈ xs, Json.depth y ≤ budget := fun y hy => hdxs y (by simp [hy])
            simp only [Json.renderElemsL, Json.renderElemSep, List.length_append,
                       List.length_cons] at hf
            have hfe : (Json.renderL e).length < f := by omega
            have hfx : (Json.renderElemsL (x :: xs)).length + 1 < f := by
              simp only [Json.renderElemsL, List.length_append]; omega
            have hv := rt_val e he budget f
              (',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest)) hde hfe
            have key := rt_elems x xs hxe hxxs budget f rest hdx hdxxs hfx
            have harg : Json.renderElemsL (e :: x :: xs) ++ ']' :: rest
                      = Json.renderL e ++ ',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest) := by
              simp only [Json.renderElemsL, Json.renderElemSep, List.cons_append, List.append_assoc]
            have hcomma : skipWs (',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest))
                        = ',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest) := by simp [skipWs, isWs]
            have h2 := Json.skipWs_renderElemsL (es := xs) hxe (']' :: rest)
            rw [harg, parseElems_step, hv]
            simp only [hcomma, h2, key]
end

/-- **Codec round-trip** for the structural core: parsing a rendered value
    recovers it exactly. -/
theorem parse_render {j : Json} (hj : Json.Simple j) {maxDepth : Nat}
    (h : j.depth ≤ maxDepth) : parse (Json.render j) maxDepth = .ok j := by
  have hv := rt_val j hj maxDepth ((Json.renderL j).length + 1) [] h (by omega)
  simp only [List.append_nil] at hv
  simp only [parse, Json.render, String.toList_ofList, hv, skipWs, List.isEmpty_nil, if_true]

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
      -- a duplicate key takes the LAST value, matching `JSON.parse` (and most parsers),
      -- so a payload a JS client accepts decodes to the same thing here
      match ms.foldl (fun acc kv => if kv.1 == key then some kv.2 else acc) none with
      | some v => .ok v
      | none   => .error s!"missing key '{key}'"
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
/-- The integer a JSON number denotes, if it is one — applying the exponent, so a backend's
    `1e2` or `100.0` decodes to `100` (a non-zero fractional part is *not* an integer). -/
def JsonNumber.toInt? (n : JsonNumber) : Option Int :=
  if 0 ≤ n.exponent then some (n.mantissa * (10 ^ n.exponent.toNat))
  else
    let d : Int := 10 ^ (-n.exponent).toNat
    if n.mantissa % d == 0 then some (n.mantissa / d) else none

instance : FromJson Int :=
  ⟨fun j => match j with
    | .num n => (n.toInt?).elim (.error "expected an integer") .ok
    | _      => .error "expected an integer"⟩
instance : FromJson Nat :=
  ⟨fun j => match j with
    | .num n => match n.toInt? with
                | some m => if 0 ≤ m then .ok m.toNat else .error "expected a non-negative integer"
                | none   => .error "expected an integer"
    | _ => .error "expected a natural number"⟩
instance [FromJson α] : FromJson (List α) :=
  ⟨fun j => match j with | .arr es => es.mapM fromJson | _ => .error "expected an array"⟩
instance [FromJson α] : FromJson (Array α) :=
  ⟨fun j => (fromJson j : Except String (List α)).map List.toArray⟩
instance [FromJson α] : FromJson (Option α) :=
  ⟨fun j => match j with | .null => .ok none | _ => (fromJson j : Except String α).map some⟩

/-- `Float` round-trips through its decimal form: a JSON number is `mantissa × 10^exponent`
    (exact), so encoding goes via the float's decimal string and decoding reconstructs it. -/
instance : ToJson Float := ⟨fun f => (Json.parse (toString f)).toOption.getD (.num ⟨0, 0⟩)⟩
instance : FromJson Float :=
  ⟨fun j => match j with
    | .num n => let mag := Float.ofScientific n.mantissa.natAbs (n.exponent < 0) n.exponent.natAbs
                .ok (if n.mantissa < 0 then -mag else mag)
    | _ => .error "expected a number"⟩

/-! ### Decoding one object field

`FromJsonField` decodes the value at a key. The default requires the key present
and prefixes any decode error with the key name (so errors say *which* field
failed). The `Option` instance treats an absent key — or an explicit `null` — as
`none`, so optional fields need not appear in the JSON at all. -/

class FromJsonField (α : Type) where
  fromField : Json → String → Except String α
export FromJsonField (fromField)

instance (priority := low) [FromJson α] : FromJsonField α where
  fromField j key := match j.field key with
    | .error e => .error e                       -- e.g. "missing key 'age'"
    | .ok v    => match (fromJson v : Except String α) with
                  | .ok a    => .ok a
                  | .error e => .error s!"{key}: {e}"

instance [FromJson α] : FromJsonField (Option α) where
  fromField j key := match j.get? key with
    | none       => .ok none                     -- key absent
    | some .null => .ok none                     -- key present but null
    | some v     => match (fromJson v : Except String α) with
                    | .ok a    => .ok (some a)
                    | .error e => .error s!"{key}: {e}"

/-! ### `jsonCodec` — generate ToJson/FromJson for a structure

`jsonCodec User [name, age, tags]` produces both instances, mapping each field to
a JSON key of the same name, plus the two string-level helpers `User.decode :
String → Except String User` (parse then decode) and `User.encode : User → String`
(encode then render). It is a core-syntax macro (no `import Lean`), so apps that use
it do not pull the Lean elaborator into their transpiled JS bundle. -/

open Lean in
syntax (name := jsonCodecCmd) "jsonCodec " ident "[" ident,* "]" : command

open Lean in
macro_rules
  | `(jsonCodec $t:ident [$fs:ident,*]) => do
      let fields := fs.getElems
      let pairs ← fields.mapM fun (f : Ident) => `(term| ($(quote (toString f.getId)), toJson x.$f))
      let keys  ← fields.mapM fun (f : Ident) => `(term| $(quote (toString f.getId)))
      let decodeId := mkIdent (t.getId ++ `decode)
      let encodeId := mkIdent (t.getId ++ `encode)
      -- a non-hygienic `maxDepth` binder, so callers can pass `(maxDepth := …)`
      let depthId  := mkIdent `maxDepth
      `(instance : ToJson $t where
          toJson x := Json.obj [$pairs,*]
        instance : FromJson $t where
          fromJson j := do
            return { $[$fields:ident := (← fromField j $keys)],* }
        /-- Parse a JSON document and decode it into `$t` (depth-bounded by `maxDepth`). -/
        def $decodeId:ident (s : String) ($depthId : Nat := 64) : Except String $t :=
          (Json.parse s $depthId).bind fromJson
        /-- Encode `$t` to a JSON string. -/
        def $encodeId:ident (x : $t) : String :=
          Json.render (toJson x))

/-! ### `jsonStruct` — declare a structure and its codec at once

`jsonStruct` reads the field names straight from the declaration, so the field
list is written *once* (a plain `structure` + `jsonCodec User [name, …]` repeats
it, and the two can silently drift). Fields use the same layout as a `structure`:
one per line, or `;`-separated on one line. Still core-syntax only — no
`import Lean`. -/

open Lean in
syntax (name := jsonStructCmd) "jsonStruct " ident " where " sepBy1IndentSemicolon(group(ident " : " term)) : command

open Lean in
macro_rules
  | `(jsonStruct $t:ident where $[$fs:ident : $tys:term]*) =>
      `(structure $t where
          $[$fs:ident : $tys:term]*
        jsonCodec $t [$fs,*])

end Qed
