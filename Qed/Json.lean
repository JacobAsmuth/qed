/-
  Qed.Json: a full-grammar JSON parser and renderer.

  Values cover the whole RFC 8259 grammar: null, booleans, numbers (as a precise
  `JsonNumber` = mantissa × 10^exponent), strings (with escapes, including
  `\uXXXX`), arrays, and objects, nested arbitrarily, since `Json` is recursive.

  The parser recurses structurally on a `fuel` counter, so totality is free, and
  on a `budget` (the caller's `maxDepth`), so it refuses to build anything deeper.
  `Qed.parse_depth_le` (below) proves the bound; `Qed.parse_render` proves the
  codec round-trip for the whole grammar: `parse (render j) = .ok j` for every
  value, including numbers (via a verified decimal renderer) and strings (via
  an escape-inverse lemma).
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

/-- `maxArr` is the least bound on its elements' depths: it is within `k` iff every
    element is. `.mpr` bounds an array's depth from its elements'; `.mp` (at `k :=
    maxArr es`) recovers each element's bound from the array's. -/
theorem maxArr_le_iff {k : Nat} : ∀ {es : List Json}, maxArr es ≤ k ↔ ∀ e ∈ es, depth e ≤ k
  | []      => by simp [maxArr]
  | e :: es => by simp [maxArr, Nat.max_le, maxArr_le_iff (es := es)]

/-- The object analogue of `maxArr_le_iff`, over the members' values. -/
theorem maxObj_le_iff {k : Nat} :
    ∀ {ms : List (String × Json)}, maxObj ms ≤ k ↔ ∀ kv ∈ ms, depth kv.2 ≤ k
  | []          => by simp [maxObj]
  | (_, v) :: ms => by simp [maxObj, Nat.max_le, maxObj_le_iff (ms := ms)]

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
                  have hb := Json.maxArr_le_iff.mpr
                    (fun e he => parseElems_depth_le _ _ _ _ _ (by assumption) e he)
                  omega)
               | (simp only [Json.depth]
                  have hb := Json.maxObj_le_iff.mpr
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

/-- Decimal digit characters of `n`, most significant first, prepended to `acc`. -/
def natDigitsAux (n : Nat) (acc : List Char) : List Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n % 10) :: acc
  else natDigitsAux (n / 10) (Char.ofNat ('0'.toNat + n % 10) :: acc)
termination_by n
decreasing_by omega

/-- An integer's characters: optional minus sign, then decimal digits. The same
    output as `toString`, but defined by recursion the round-trip proof inverts. -/
def intCharsL (i : Int) : List Char :=
  (if i < 0 then ['-'] else []) ++ natDigitsAux i.natAbs []

def Json.renderNumL (n : JsonNumber) : List Char :=
  intCharsL n.mantissa ++ (if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent)

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

`parse (render j) = .ok j` for every value: the inverse lemmas below cover
numbers (`parseNum_render`), strings (`parseStr_render`), and the structural
cases, so `parse_render` holds for the whole grammar. -/

/-- The digit character for `k < 10` carries exactly `k` (and is a digit). -/
theorem digit_spec (k : Nat) (h : k < 10) :
    (Char.ofNat ('0'.toNat + k)).toNat - '0'.toNat = k
    ∧ isDigit (Char.ofNat ('0'.toNat + k)) = true :=
  match k, h with
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | _ + 10, h => absurd h (by omega)

/-- The accumulator only ever rides along on the right. -/
theorem natDigitsAux_append (n : Nat) : ∀ acc : List Char,
    natDigitsAux n acc = natDigitsAux n [] ++ acc := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro acc
    rw [natDigitsAux.eq_def (acc := acc), natDigitsAux.eq_def (acc := [])]
    by_cases h : n < 10
    · simp [h]
    · simp only [if_neg h]
      rw [ih (n / 10) (by omega), ih (n / 10) (by omega) [_]]
      simp

/-- One unfolding step in last-digit-first form. -/
theorem natDigits_unfold (n : Nat) :
    natDigitsAux n [] = (if n < 10 then [] else natDigitsAux (n / 10) [])
                        ++ [Char.ofNat ('0'.toNat + n % 10)] := by
  rw [natDigitsAux.eq_def]
  by_cases h : n < 10
  · simp [h]
  · simp only [if_neg h]
    exact natDigitsAux_append (n / 10) [_]

theorem natDigits_ne_nil (n : Nat) : natDigitsAux n [] ≠ [] := by
  rw [natDigits_unfold]; simp

theorem natDigits_digit (n : Nat) : ∀ c ∈ natDigitsAux n [], isDigit c = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits_unfold]
    intro c hc
    rw [List.mem_append] at hc
    cases hc with
    | inr h =>
        rw [List.mem_singleton] at h; subst h
        exact (digit_spec _ (Nat.mod_lt _ (by omega))).2
    | inl h =>
        by_cases h10 : n < 10
        · simp [h10] at h
        · exact ih (n / 10) (by omega) c (by simpa [h10] using h)

theorem foldl_natDigits (n : Nat) :
    (natDigitsAux n []).foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits_unfold, List.foldl_append]
    by_cases h : n < 10
    · simp only [if_pos h, List.foldl_nil, List.foldl_cons]
      rw [(digit_spec _ (Nat.mod_lt _ (by omega))).1]
      omega
    · simp only [if_neg h, List.foldl_cons, List.foldl_nil]
      rw [ih (n / 10) (by omega), (digit_spec _ (Nat.mod_lt _ (by omega))).1]
      omega

theorem digitsToInt_natDigits (n : Nat) : digitsToInt (natDigitsAux n []) = (n : Int) := by
  rw [digitsToInt, foldl_natDigits]

/-- A remainder that cannot extend a rendered number: empty, or headed by a
    character that is no digit and none of `.`, `e`, `E`. Every JSON delimiter
    (`,`, `]`, `}`, end of input) qualifies. -/
def numDelim : List Char → Bool
  | []     => true
  | c :: _ => !(isDigit c || c == '.' || c == 'e' || c == 'E')

theorem takeDigits_cons_not {c : Char} {t : List Char} (h : isDigit c = false) :
    takeDigits (c :: t) = ([], c :: t) := by
  simp [takeDigits, h]

theorem takeDigits_stop {cs : List Char} (h : numDelim cs = true) :
    takeDigits cs = ([], cs) := by
  match cs with
  | [] => rfl
  | c :: t =>
      simp only [numDelim, Bool.not_eq_true', Bool.or_eq_false_iff] at h
      exact takeDigits_cons_not h.1.1.1

/-- `takeDigits` consumes exactly a digit run, stopping at a non-digit. -/
theorem takeDigits_append (ds : List Char) (hds : ∀ c ∈ ds, isDigit c = true)
    (rest : List Char) (hrest : takeDigits rest = ([], rest)) :
    takeDigits (ds ++ rest) = (ds, rest) := by
  induction ds with
  | nil => simpa using hrest
  | cons c t ih =>
      have hc : isDigit c = true := hds c (by simp)
      have ht := ih (fun x hx => hds x (by simp [hx]))
      simp [takeDigits, hc, ht]

/-- A digit run is nonempty and starts with a digit. -/
theorem natDigits_cons (m : Nat) :
    ∃ c t, natDigitsAux m [] = c :: t ∧ isDigit c = true := by
  match h : natDigitsAux m [] with
  | [] => exact absurd h (natDigits_ne_nil m)
  | c :: t => exact ⟨c, t, rfl, natDigits_digit m c (h ▸ List.mem_cons_self ..)⟩

theorem digit_not_sign {c : Char} (h : isDigit c = true) : c ≠ '-' ∧ c ≠ '+' :=
  ⟨fun e => by subst e; exact absurd h (by decide),
   fun e => by subst e; exact absurd h (by decide)⟩

theorem numDelim_head {c : Char} {t : List Char} (h : numDelim (c :: t) = true) :
    isDigit c = false ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' := by
  simp only [numDelim, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- The number codec round-trip: `parseNum` inverts `renderNumL` whenever the
    remainder cannot extend the number (`numDelim`). -/
theorem parseNum_render (n : JsonNumber) (rest : List Char) (hr : numDelim rest = true) :
    parseNum (Json.renderNumL n ++ rest) = .ok (n, rest) := by
  obtain ⟨m, ex⟩ := n
  by_cases hm : m < 0 <;> by_cases hex : ex = 0
  · -- m < 0, ex = 0
    have harg : Json.renderNumL ⟨m, ex⟩ ++ rest = '-' :: (natDigitsAux m.natAbs [] ++ rest) := by
      simp [Json.renderNumL, intCharsL, hm, hex]
    rw [harg]
    simp only [parseNum]
    rw [takeDigits_append _ (natDigits_digit _) _ (takeDigits_stop hr)]
    rw [if_neg (by simp [natDigits_ne_nil])]
    cases rest with
    | nil => simp [digitsToInt_natDigits, hex]; omega
    | cons c t =>
        obtain ⟨hd, hdot, he, hE⟩ := numDelim_head hr
        simp [hdot, he, hE, digitsToInt_natDigits, hex]
        omega
  · -- m < 0, ex ≠ 0
    by_cases hexn : ex < 0
    · have harg : Json.renderNumL ⟨m, ex⟩ ++ rest
          = '-' :: (natDigitsAux m.natAbs []
              ++ ('e' :: ('-' :: (natDigitsAux ex.natAbs [] ++ rest)))) := by
        simp [Json.renderNumL, intCharsL, hm, hex, hexn]
      rw [harg]
      simp only [parseNum]
      rw [takeDigits_append _ (natDigits_digit _) _ (takeDigits_cons_not (by decide))]
      rw [if_neg (by simp [natDigits_ne_nil])]
      have hte : takeDigits (natDigitsAux ex.natAbs [] ++ rest)
          = (natDigitsAux ex.natAbs [], rest) :=
        takeDigits_append _ (natDigits_digit _) _ (takeDigits_stop hr)
      simp [hte, digitsToInt_natDigits]
      omega
    · obtain ⟨c1, t1, hex0, hc1⟩ := natDigits_cons ex.natAbs
      obtain ⟨hns, hps⟩ := digit_not_sign hc1
      have harg : Json.renderNumL ⟨m, ex⟩ ++ rest
          = '-' :: (natDigitsAux m.natAbs []
              ++ ('e' :: (natDigitsAux ex.natAbs [] ++ rest))) := by
        simp [Json.renderNumL, intCharsL, hm, hex, hexn]
      rw [harg]
      simp only [parseNum]
      rw [takeDigits_append _ (natDigits_digit _) _ (takeDigits_cons_not (by decide))]
      rw [if_neg (by simp [natDigits_ne_nil])]
      rw [hex0]
      simp only [List.cons_append]
      have htd : takeDigits (c1 :: (t1 ++ rest)) = (c1 :: t1, rest) := by
        have := takeDigits_append _ (natDigits_digit ex.natAbs) _ (takeDigits_stop hr)
        rwa [hex0, List.cons_append] at this
      have hdi : digitsToInt (c1 :: t1) = (ex.natAbs : Int) := by
        have := digitsToInt_natDigits ex.natAbs
        rwa [hex0] at this
      simp [hns, hps, htd, hdi, digitsToInt_natDigits]
      omega
  · -- m ≥ 0, ex = 0
    obtain ⟨c0, t0, hm0, hc0⟩ := natDigits_cons m.natAbs
    obtain ⟨hns, hps⟩ := digit_not_sign hc0
    have harg : Json.renderNumL ⟨m, ex⟩ ++ rest = c0 :: (t0 ++ rest) := by
      simp [Json.renderNumL, intCharsL, hm, hex, hm0]
    rw [harg]
    simp only [parseNum]
    have htd : takeDigits (c0 :: (t0 ++ rest)) = (c0 :: t0, rest) := by
      have := takeDigits_append _ (natDigits_digit m.natAbs) _ (takeDigits_stop hr)
      rwa [hm0, List.cons_append] at this
    have hdi : digitsToInt (c0 :: t0) = (m.natAbs : Int) := by
      have := digitsToInt_natDigits m.natAbs
      rwa [hm0] at this
    cases rest with
    | nil =>
        rw [List.append_nil] at htd
        simp [hns, htd, hdi, hex]
        omega
    | cons c t =>
        obtain ⟨hd, hdot, he, hE⟩ := numDelim_head hr
        simp [hns, htd, hdi, hdot, he, hE, hex]
        omega
  · -- m ≥ 0, ex ≠ 0
    obtain ⟨c0, t0, hm0, hc0⟩ := natDigits_cons m.natAbs
    obtain ⟨hns0, hps0⟩ := digit_not_sign hc0
    by_cases hexn : ex < 0
    · have harg : Json.renderNumL ⟨m, ex⟩ ++ rest
          = c0 :: (t0 ++ ('e' :: ('-' :: (natDigitsAux ex.natAbs [] ++ rest)))) := by
        simp [Json.renderNumL, intCharsL, hm, hex, hexn, hm0]
      rw [harg]
      simp only [parseNum]
      have htd : takeDigits (c0 :: (t0 ++ ('e' :: ('-' :: (natDigitsAux ex.natAbs [] ++ rest)))))
          = (c0 :: t0, 'e' :: ('-' :: (natDigitsAux ex.natAbs [] ++ rest))) := by
        have := takeDigits_append _ (natDigits_digit m.natAbs)
          ('e' :: ('-' :: (natDigitsAux ex.natAbs [] ++ rest))) (takeDigits_cons_not (by decide))
        rwa [hm0, List.cons_append] at this
      have hdi : digitsToInt (c0 :: t0) = (m.natAbs : Int) := by
        have := digitsToInt_natDigits m.natAbs
        rwa [hm0] at this
      have hte : takeDigits (natDigitsAux ex.natAbs [] ++ rest)
          = (natDigitsAux ex.natAbs [], rest) :=
        takeDigits_append _ (natDigits_digit _) _ (takeDigits_stop hr)
      simp [hns0, htd, hdi, hte, digitsToInt_natDigits]
      omega
    · obtain ⟨c1, t1, hex0, hc1⟩ := natDigits_cons ex.natAbs
      obtain ⟨hns1, hps1⟩ := digit_not_sign hc1
      have harg : Json.renderNumL ⟨m, ex⟩ ++ rest
          = c0 :: (t0 ++ ('e' :: (c1 :: (t1 ++ rest)))) := by
        simp [Json.renderNumL, intCharsL, hm, hex, hexn, hm0, hex0]
      rw [harg]
      simp only [parseNum]
      have htd : takeDigits (c0 :: (t0 ++ ('e' :: (c1 :: (t1 ++ rest)))))
          = (c0 :: t0, 'e' :: (c1 :: (t1 ++ rest))) := by
        have := takeDigits_append _ (natDigits_digit m.natAbs)
          ('e' :: (c1 :: (t1 ++ rest))) (takeDigits_cons_not (by decide))
        rwa [hm0, List.cons_append] at this
      have htd1 : takeDigits (c1 :: (t1 ++ rest)) = (c1 :: t1, rest) := by
        have := takeDigits_append _ (natDigits_digit ex.natAbs) _ (takeDigits_stop hr)
        rwa [hex0, List.cons_append] at this
      have hdi : digitsToInt (c0 :: t0) = (m.natAbs : Int) := by
        have := digitsToInt_natDigits m.natAbs
        rwa [hm0] at this
      have hdi1 : digitsToInt (c1 :: t1) = (ex.natAbs : Int) := by
        have := digitsToInt_natDigits ex.natAbs
        rwa [hex0] at this
      simp [hns0, hns1, hps1, htd, htd1, hdi, hdi1]
      omega


theorem hexVal_toHexDigit (d : Nat) (h : d < 16) : hexVal (toHexDigit d) = some d :=
  match d, h with
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | 10, _ => by decide
  | 11, _ => by decide
  | 12, _ => by decide
  | 13, _ => by decide
  | 14, _ => by decide
  | 15, _ => by decide
  | _ + 16, h => absurd h (by omega)

/-- Parsing one escaped character undoes the escaping. -/
theorem parseStrAux_escape (c : Char) (acc rest : List Char) :
    parseStrAux acc (escapeCharL c ++ rest) = parseStrAux (c :: acc) rest := by
  simp only [escapeCharL]
  split
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rename_i cv h1 h2 h3 h4 h5
    by_cases hlt : c.toNat < 0x20
    · simp only [if_pos hlt, List.cons_append]
      have h16 : ∀ k : Nat, k % 16 < 16 := fun k => Nat.mod_lt _ (by omega)
      have harith : ((c.toNat / 4096 % 16 * 16 + c.toNat / 256 % 16) * 16 + c.toNat / 16 % 16) * 16
              + c.toNat % 16 = c.toNat := by omega
      simp [parseStrAux, hex4, hexVal_toHexDigit _ (h16 _), harith, Char.ofNat_toNat]
    · simp only [if_neg hlt, List.cons_append, List.nil_append]
      rw [parseStrAux.eq_def]
      have h2' : c ≠ '\\' := h2
      simp [h2']


/-- Parsing an escaped character run stops exactly at the closing quote. -/
theorem parseStrAux_flatMap (cs : List Char) : ∀ (acc rest : List Char),
    parseStrAux acc (cs.flatMap escapeCharL ++ '"' :: rest)
      = .ok (String.ofList (acc.reverse ++ cs), rest) := by
  induction cs with
  | nil => intro acc rest; simp [parseStrAux]
  | cons c cs ih =>
      intro acc rest
      rw [List.flatMap_cons, List.append_assoc, parseStrAux_escape, ih]
      simp

/-- The string codec round-trip: parsing a rendered string body recovers it. -/
theorem parseStr_render (s : String) (rest : List Char) :
    parseStr (s.toList.flatMap escapeCharL ++ '"' :: rest) = .ok (s, rest) := by
  rw [parseStr, parseStrAux_flatMap]
  simp [String.ofList_toList]


theorem numDelim_cons {c : Char} {t : List Char}
    (h : (isDigit c || c == '.' || c == 'e' || c == 'E') = false) :
    numDelim (c :: t) = true := by
  simp [numDelim, h]

theorem digit_not_special {c : Char} (h : isDigit c = true) :
    isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> (intro rfl; exact absurd h (by decide))
  · intro rfl; exact absurd h (by decide)
  · intro rfl; exact absurd h (by decide)

theorem digit_not_starts {c : Char} (h : isDigit c = true) :
    c ≠ 'n' ∧ c ≠ 't' ∧ c ≠ 'f' ∧ c ≠ '"' ∧ c ≠ '[' ∧ c ≠ '{' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro rfl; exact absurd h (by decide))

/-- Every rendered value begins with a non-whitespace character that closes
    neither an array nor an object. -/
theorem renderL_head (j : Json) :
    ∃ c t, Json.renderL j = c :: t ∧ isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases j with
  | null => exact ⟨'n', _, rfl, by decide, by decide, by decide⟩
  | bool b => cases b with
      | true => exact ⟨'t', _, rfl, by decide, by decide, by decide⟩
      | false => exact ⟨'f', _, rfl, by decide, by decide, by decide⟩
  | str s => exact ⟨'"', _, rfl, by decide, by decide, by decide⟩
  | arr es => exact ⟨'[', _, rfl, by decide, by decide, by decide⟩
  | obj ms => exact ⟨'{', _, rfl, by decide, by decide, by decide⟩
  | num n =>
      by_cases hm : n.mantissa < 0
      · refine ⟨'-', natDigitsAux n.mantissa.natAbs []
            ++ (if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent),
            ?_, by decide, by decide, by decide⟩
        simp [Json.renderL, Json.renderNumL, intCharsL, hm]
      · obtain ⟨c0, t0, h0, hc0⟩ := natDigits_cons n.mantissa.natAbs
        obtain ⟨hws, hbr, hbc⟩ := digit_not_special hc0
        refine ⟨c0, t0 ++ (if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent),
                ?_, hws, hbr, hbc⟩
        simp [Json.renderL, Json.renderNumL, intCharsL, hm, h0]

/-- `skipWs` is the identity on rendered output (it never starts with whitespace). -/
theorem skipWs_renderL (j : Json) (x : List Char) :
    skipWs (Json.renderL j ++ x) = Json.renderL j ++ x := by
  obtain ⟨c, t, hren, hcws, _, _⟩ := renderL_head j
  rw [hren, List.cons_append]
  simp [skipWs, hcws]

theorem skipWs_renderElemsL (e : Json) (es : List Json) (x : List Char) :
    skipWs (Json.renderElemsL (e :: es) ++ x) = Json.renderElemsL (e :: es) ++ x := by
  simp only [Json.renderElemsL, List.append_assoc]
  exact skipWs_renderL e _

/-- A value whose input starts like a number parses through `parseNum`. -/
theorem parseVal_to_parseNum (f b : Nat) (c0 : Char) (t : List Char)
    (hws : isWs c0 = false)
    (hn : c0 ≠ 'n') (ht : c0 ≠ 't') (hf : c0 ≠ 'f') (hq : c0 ≠ '"')
    (hbk : c0 ≠ '[') (hbc : c0 ≠ '{') (hg : (c0 == '-' || isDigit c0) = true) :
    parseVal (f + 1) b (c0 :: t)
      = (match parseNum (c0 :: t) with
         | .ok (n, r') => .ok (.num n, r')
         | .error e => .error e) := by
  simp only [parseVal]
  rw [show skipWs (c0 :: t) = c0 :: t from by simp [skipWs, hws]]
  simp [hn, ht, hf, hg]

theorem parseVal_num (n : JsonNumber) (f b : Nat) (rest : List Char)
    (hr : numDelim rest = true) :
    parseVal (f + 1) b (Json.renderNumL n ++ rest) = .ok (.num n, rest) := by
  by_cases hm : n.mantissa < 0
  · have harg : Json.renderNumL n ++ rest
        = '-' :: (natDigitsAux n.mantissa.natAbs []
            ++ ((if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent) ++ rest)) := by
      simp [Json.renderNumL, intCharsL, hm]
    rw [harg, parseVal_to_parseNum f b '-' _ (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), ← harg, parseNum_render n rest hr]
  · obtain ⟨c0, t0, h0, hc0⟩ := natDigits_cons n.mantissa.natAbs
    obtain ⟨hn, ht, hf', hq, hbk, hbc⟩ := digit_not_starts hc0
    obtain ⟨hws, _, _⟩ := digit_not_special hc0
    obtain ⟨hminus, _⟩ := digit_not_sign hc0
    have harg : Json.renderNumL n ++ rest
        = c0 :: (t0 ++ ((if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent) ++ rest)) := by
      simp [Json.renderNumL, intCharsL, hm, h0]
    rw [harg, parseVal_to_parseNum f b c0 _ hws hn ht hf' hq hbk hbc (by simp [hc0]),
        ← harg, parseNum_render n rest hr]


theorem renderMembersL_cons (k : String) (v : Json) (ms : List (String × Json)) :
    Json.renderMembersL ((k, v) :: ms)
      = Json.renderStrL k ++ ':' :: (Json.renderL v ++ Json.renderMemberSep ms) := rfl

theorem renderMemberSep_cons (k : String) (v : Json) (ms : List (String × Json)) :
    Json.renderMemberSep ((k, v) :: ms) = ',' :: Json.renderMembersL ((k, v) :: ms) := rfl

theorem skipWs_renderMembersL (k : String) (v : Json) (ms : List (String × Json)) (x : List Char) :
    skipWs (Json.renderMembersL ((k, v) :: ms) ++ x)
      = Json.renderMembersL ((k, v) :: ms) ++ x := by
  simp only [renderMembersL_cons, Json.renderStrL, List.cons_append, List.append_assoc]
  simp [skipWs, isWs]

/-- The parser's array branch reduces to wrapping `parseElems`, given that the
    element list does not begin with `]`. This isolates the only `match` on a
    variable list-head, discharged via `renderL_head` (`c ≠ ']'`). -/
theorem parseVal_arr (e : Json) (es : List Json) (f b : Nat) (rest : List Char) :
    parseVal (f + 1) (b + 1) ('[' :: (Json.renderElemsL (e :: es) ++ ']' :: rest))
      = (match parseElems f b (Json.renderElemsL (e :: es) ++ ']' :: rest) with
         | .ok (vs, r') => .ok (Json.arr vs, r')
         | .error msg   => .error msg) := by
  obtain ⟨c, t, hren, hcws, hcbr, _⟩ := renderL_head e
  have hcons : Json.renderElemsL (e :: es) ++ ']' :: rest
             = c :: (t ++ Json.renderElemSep es ++ ']' :: rest) := by
    simp only [Json.renderElemsL, hren, List.cons_append, List.append_assoc]
  have step : parseVal (f + 1) (b + 1) ('[' :: (Json.renderElemsL (e :: es) ++ ']' :: rest))
            = (match skipWs (Json.renderElemsL (e :: es) ++ ']' :: rest) with
               | []      => .error "unexpected end of input"
               | c :: r' => if c = ']' then .ok (Json.arr [], r')
                            else (match parseElems f b (c :: r') with
                                  | .ok (es', r'') => .ok (Json.arr es', r'')
                                  | .error e       => .error e)) := rfl
  rw [step, skipWs_renderElemsL e es (']' :: rest), hcons]
  simp only [if_neg hcbr]

/-- The parser's object branch reduces to wrapping `parseMembers`: the member
    list begins with a key's `"`, never `}`. The object analogue of `parseVal_arr`. -/
theorem parseVal_obj (k : String) (v : Json) (ms : List (String × Json))
    (f b : Nat) (rest : List Char) :
    parseVal (f + 1) (b + 1) ('{' :: (Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest))
      = (match parseMembers f b (Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest) with
         | .ok (ms', r') => .ok (Json.obj ms', r')
         | .error msg   => .error msg) := by
  have hcons : Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest
      = '"' :: (k.toList.flatMap escapeCharL
          ++ ('"' :: (':' :: (Json.renderL v ++ (Json.renderMemberSep ms ++ '}' :: rest))))) := by
    simp [renderMembersL_cons, Json.renderStrL]
  have step : parseVal (f + 1) (b + 1) ('{' :: (Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest))
      = (match skipWs (Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest) with
         | []      => .error "unexpected end of input"
         | c :: r' => if c = '}' then .ok (Json.obj [], r')
                      else (match parseMembers f b (c :: r') with
                            | .ok (ms', r'') => .ok (Json.obj ms', r'')
                            | .error e       => .error e)) := rfl
  rw [step, skipWs_renderMembersL, hcons]
  simp only [if_neg (by decide : ¬('"' = '}'))]

/-- One-step unfolding of `parseMembers` at successor fuel (definitional). -/
theorem parseMembers_step (f budget : Nat) (cs : List Char) :
    parseMembers (f + 1) budget cs
      = (match skipWs cs with
         | '"' :: r =>
             match parseStr r with
             | .error e => .error e
             | .ok (key, r1) =>
                 match skipWs r1 with
                 | ':' :: r2 =>
                     match parseVal f budget (skipWs r2) with
                     | .error e => .error e
                     | .ok (v, r3) =>
                         match skipWs r3 with
                         | ',' :: r4 =>
                             match parseMembers f budget (skipWs r4) with
                             | .ok (ms, r5) => .ok ((key, v) :: ms, r5)
                             | .error e     => .error e
                         | '}' :: r4 => .ok ([(key, v)], r4)
                         | _         => .error "expected ',' or '}'"
                 | _ => .error "expected ':'"
         | _ => .error "expected string key") := rfl

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
  theorem rt_val : ∀ (j : Json) (budget fuel : Nat) (rest : List Char),
      j.depth ≤ budget → (Json.renderL j).length < fuel → numDelim rest = true →
      parseVal fuel budget (Json.renderL j ++ rest) = .ok (j, rest)
    | .null, budget, fuel, rest, _, hf, _ => by
        cases fuel with
        | zero => simp [Json.renderL] at hf
        | succ f => simp [Json.renderL, parseVal, skipWs, isWs]
    | .bool b, budget, fuel, rest, _, hf, _ => by
        cases fuel with
        | zero => cases b <;> simp [Json.renderL] at hf
        | succ f => cases b <;> simp [Json.renderL, parseVal, skipWs, isWs]
    | .num n, budget, fuel, rest, _, hf, hr => by
        cases fuel with
        | zero => exact absurd hf (Nat.not_lt_zero _)
        | succ f => exact parseVal_num n f budget rest hr
    | .str s, budget, fuel, rest, _, hf, _ => by
        cases fuel with
        | zero => exact absurd hf (Nat.not_lt_zero _)
        | succ f =>
            have harg : Json.renderL (.str s) ++ rest
                = '"' :: (s.toList.flatMap escapeCharL ++ ('"' :: rest)) := by
              simp [Json.renderL, Json.renderStrL]
            rw [harg]
            simp [parseVal, skipWs, isWs, parseStr_render]
    | .arr [], budget, fuel, rest, hd, hf, _ => by
        cases fuel with
        | zero => simp [Json.renderL, Json.renderElemsL] at hf
        | succ f => cases budget with
          | zero => simp [Json.depth, Json.maxArr] at hd
          | succ b => simp [Json.renderL, Json.renderElemsL, parseVal, skipWs, isWs]
    | .arr (e :: es), budget, fuel, rest, hd, hf, _ => by
        cases budget with
        | zero => simp [Json.depth] at hd
        | succ b =>
            simp only [Json.depth] at hd
            have hdall : ∀ x ∈ (e :: es), Json.depth x ≤ b :=
              Json.maxArr_le_iff.mp (by omega)
            cases fuel with
            | zero => simp [Json.renderL, Json.renderElemsL] at hf
            | succ f =>
                have hfe : (Json.renderElemsL (e :: es)).length + 1 < f := by
                  simp only [Json.renderL, List.length_cons, List.length_append] at hf; omega
                have key := rt_elems e es b f rest hdall hfe
                have harr : Json.renderL (Json.arr (e :: es)) ++ rest
                          = '[' :: (Json.renderElemsL (e :: es) ++ ']' :: rest) := by
                  simp [Json.renderL]
                rw [harr, parseVal_arr e es f b rest, key]
    | .obj [], budget, fuel, rest, hd, hf, _ => by
        cases fuel with
        | zero => simp [Json.renderL, Json.renderMembersL] at hf
        | succ f => cases budget with
          | zero => simp [Json.depth, Json.maxObj] at hd
          | succ b => simp [Json.renderL, Json.renderMembersL, parseVal, skipWs, isWs]
    | .obj ((k, v) :: ms), budget, fuel, rest, hd, hf, _ => by
        cases budget with
        | zero => simp [Json.depth] at hd
        | succ b =>
            simp only [Json.depth] at hd
            have hdall : ∀ x ∈ ((k, v) :: ms), Json.depth x.2 ≤ b :=
              Json.maxObj_le_iff.mp (by omega)
            cases fuel with
            | zero => simp [Json.renderL, Json.renderMembersL] at hf
            | succ f =>
                have hfm : (Json.renderMembersL ((k, v) :: ms)).length + 1 < f := by
                  simp only [Json.renderL, List.length_cons, List.length_append] at hf; omega
                have key := rt_members (k, v) ms b f rest hdall hfm
                have hobj : Json.renderL (Json.obj ((k, v) :: ms)) ++ rest
                          = '{' :: (Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest) := by
                  simp [Json.renderL]
                rw [hobj, parseVal_obj k v ms f b rest, key]
  termination_by j _ _ _ _ _ _ => sizeOf j
  theorem rt_elems : ∀ (e : Json) (es : List Json),
      ∀ (budget fuel : Nat) (rest : List Char),
      (∀ x ∈ e :: es, Json.depth x ≤ budget) →
      (Json.renderElemsL (e :: es)).length + 1 < fuel →
      parseElems fuel budget (Json.renderElemsL (e :: es) ++ ']' :: rest) = .ok (e :: es, rest)
    | e, [], budget, fuel, rest, hd, hf => by
        cases fuel with
        | zero => omega
        | succ f =>
            have hfe : (Json.renderL e).length < f := by
              simp only [Json.renderElemsL, Json.renderElemSep, List.append_nil] at hf; omega
            have hv := rt_val e budget f (']' :: rest) (hd e (by simp)) hfe
              (numDelim_cons (by decide))
            have harg : Json.renderElemsL (e :: []) ++ ']' :: rest = Json.renderL e ++ ']' :: rest := by
              simp [Json.renderElemsL, Json.renderElemSep]
            rw [harg, parseElems_step, hv]
            simp [skipWs, isWs]
    | e, x :: xs, budget, fuel, rest, hd, hf => by
        cases fuel with
        | zero => omega
        | succ f =>
            have hdtail : ∀ y ∈ x :: xs, Json.depth y ≤ budget := fun y hy => hd y (by simp [hy])
            simp only [Json.renderElemsL, Json.renderElemSep, List.length_append,
                       List.length_cons] at hf
            have hfe : (Json.renderL e).length < f := by omega
            have hfx : (Json.renderElemsL (x :: xs)).length + 1 < f := by
              simp only [Json.renderElemsL, List.length_append]; omega
            have hv := rt_val e budget f
              (',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest)) (hd e (by simp)) hfe
              (numDelim_cons (by decide))
            have key := rt_elems x xs budget f rest hdtail hfx
            have harg : Json.renderElemsL (e :: x :: xs) ++ ']' :: rest
                      = Json.renderL e ++ ',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest) := by
              simp only [Json.renderElemsL, Json.renderElemSep, List.cons_append, List.append_assoc]
            have hcomma : skipWs (',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest))
                        = ',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest) := by simp [skipWs, isWs]
            have h2 := skipWs_renderElemsL x xs (']' :: rest)
            rw [harg, parseElems_step, hv]
            simp only [hcomma, h2, key]
  termination_by e es _ _ _ _ _ => sizeOf e + sizeOf es
  theorem rt_members : ∀ (kv : String × Json) (ms : List (String × Json)),
      ∀ (budget fuel : Nat) (rest : List Char),
      (∀ x ∈ kv :: ms, Json.depth x.2 ≤ budget) →
      (Json.renderMembersL (kv :: ms)).length + 1 < fuel →
      parseMembers fuel budget (Json.renderMembersL (kv :: ms) ++ '}' :: rest)
        = .ok (kv :: ms, rest)
    | (k, v), [], budget, fuel, rest, hd, hf => by
        cases fuel with
        | zero => omega
        | succ f =>
            have hfe : (Json.renderL v).length < f := by
              simp only [renderMembersL_cons, Json.renderMemberSep, Json.renderStrL,
                         List.append_nil, List.length_append, List.length_cons] at hf
              omega
            have hv := rt_val v budget f ('}' :: rest) (hd (k, v) (by simp)) hfe
              (numDelim_cons (by decide))
            have harg : Json.renderMembersL ((k, v) :: []) ++ '}' :: rest
                = '"' :: (k.toList.flatMap escapeCharL
                    ++ ('"' :: (':' :: (Json.renderL v ++ '}' :: rest)))) := by
              simp [renderMembersL_cons, Json.renderMemberSep, Json.renderStrL]
            rw [harg, parseMembers_step]
            simp [skipWs, isWs, parseStr_render, skipWs_renderL, hv]
    | (k, v), (k', v') :: ms, budget, fuel, rest, hd, hf => by
        cases fuel with
        | zero => omega
        | succ f =>
            have hdtail : ∀ y ∈ (k', v') :: ms, Json.depth y.2 ≤ budget :=
              fun y hy => hd y (by simp [hy])
            simp only [renderMembersL_cons (ms := (k', v') :: ms), renderMemberSep_cons,
                       List.length_append, List.length_cons] at hf
            have hfe : (Json.renderL v).length < f := by
              simp only [Json.renderStrL, List.length_cons, List.length_append] at hf; omega
            have hfx : (Json.renderMembersL ((k', v') :: ms)).length + 1 < f := by
              simp only [Json.renderStrL, List.length_cons, List.length_append] at hf; omega
            have hv := rt_val v budget f
              (',' :: (Json.renderMembersL ((k', v') :: ms) ++ '}' :: rest)) (hd (k, v) (by simp))
              hfe (numDelim_cons (by decide))
            have key := rt_members (k', v') ms budget f rest hdtail hfx
            have harg : Json.renderMembersL ((k, v) :: (k', v') :: ms) ++ '}' :: rest
                = '"' :: (k.toList.flatMap escapeCharL
                    ++ ('"' :: (':' :: (Json.renderL v
                        ++ (',' :: (Json.renderMembersL ((k', v') :: ms) ++ '}' :: rest)))))) := by
              simp [renderMembersL_cons (ms := (k', v') :: ms), renderMemberSep_cons,
                    Json.renderStrL]
            rw [harg, parseMembers_step]
            simp [skipWs, isWs, parseStr_render, skipWs_renderL, hv,
                  skipWs_renderMembersL, key]
  termination_by kv ms _ _ _ _ _ => sizeOf kv + sizeOf ms
end

/-- **Codec round-trip**, whole grammar: parsing a rendered value recovers it
    exactly, for every `Json` value within `maxDepth`. -/
theorem parse_render {j : Json} {maxDepth : Nat}
    (h : j.depth ≤ maxDepth) : parse (Json.render j) maxDepth = .ok j := by
  have hv := rt_val j maxDepth ((Json.renderL j).length + 1) [] h (by omega) rfl
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
/-- The integer a JSON number denotes, if it is one, applying the exponent, so a backend's
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
failed). The `Option` instance treats an absent key, or an explicit `null`, as
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

/-! The typed structure codecs (`ToJson`/`FromJson` instances, `decode`/`encode`) are
generated by the `schema` command (`Qed/Schema.lean`), which folds the JSON side of a
declaration together with its form. The classes and field decoders above are the JSON
half it builds on. -/

end Qed
