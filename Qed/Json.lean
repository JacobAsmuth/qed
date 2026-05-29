/-
  Qed.Json — a JSON parser with a *user-defined* recursion bound, proven never to
  exceed it (dream-API #6).

  The developer picks the maximum nesting depth; the parser refuses to build
  anything deeper. Two guarantees:

    * **Totality is free.** The parser recurses structurally on a `fuel` counter,
      so Lean accepts it as terminating with no well-founded-recursion proof.
    * **The bound is proven.** `parse_depth_le` shows that *any* value the parser
      returns has `depth ≤ maxDepth`, so a deeply-nested input cannot exceed the
      limit.

  Scope: null / bool / number / string / array. Objects are a mechanical
  extension (they mirror arrays); every scalar is depth 0, so adding them does
  not change the bound argument.
-/
namespace Qed

/-- A parsed JSON value. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num  (n : Nat)
  | str  (s : String)
  | arr  (elems : List Json)

namespace Json

mutual
  /-- Nesting depth: scalars are 0, an array is one more than its deepest element. -/
  def depth : Json → Nat
    | .null   => 0
    | .bool _ => 0
    | .num _  => 0
    | .str _  => 0
    | .arr es => 1 + maxDepth es
  /-- The maximum `depth` over a list of values (0 for the empty list). -/
  def maxDepth : List Json → Nat
    | []      => 0
    | e :: es => Nat.max (depth e) (maxDepth es)
end

/-- If every element is within `k`, so is the list maximum. -/
theorem maxDepth_le {k : Nat} : ∀ {es : List Json}, (∀ e ∈ es, depth e ≤ k) → maxDepth es ≤ k
  | [],      _ => by simp [maxDepth]
  | e :: es, h => by
      simp only [maxDepth, Nat.max_le]
      exact ⟨h e (by simp), maxDepth_le (fun x hx => h x (by simp [hx]))⟩

end Json

/-! ### Lexer helpers (all total, structural on the character list) -/

def isWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def skipWs : List Char → List Char
  | c :: cs => if isWs c then skipWs cs else c :: cs
  | []      => []

/-- Consume a maximal run of digits (possibly empty). -/
def takeDigits : List Char → List Char × List Char
  | c :: cs => if isDigit c then let (ds, r) := takeDigits cs; (c :: ds, r) else ([], c :: cs)
  | []      => ([], [])

def digitsToNat (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- Read characters up to (and consuming) a closing `"`. No escape handling. -/
def takeUntilQuote : List Char → Option (List Char × List Char)
  | '"' :: cs => some ([], cs)
  | c   :: cs => (takeUntilQuote cs).map (fun (s, r) => (c :: s, r))
  | []        => none

/-! ### The parser

Both functions recurse structurally on `fuel`, so termination is automatic.
`budget` is the remaining nesting allowance: an array may only be parsed when
`budget > 0`, and its elements are parsed with `budget - 1`. -/

mutual
  /-- Parse one value. -/
  def parseVal (fuel budget : Nat) (cs : List Char) : Except String (Json × List Char) :=
    match fuel with
    | 0 => .error "out of fuel"
    | fuel + 1 =>
      match skipWs cs with
      | 'n' :: 'u' :: 'l' :: 'l' :: r        => .ok (.null, r)
      | 't' :: 'r' :: 'u' :: 'e' :: r        => .ok (.bool true, r)
      | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => .ok (.bool false, r)
      | '"' :: r =>
          match takeUntilQuote r with
          | some (s, r') => .ok (.str ⟨s⟩, r')
          | none         => .error "unterminated string"
      | '[' :: r =>
          match budget with
          | 0          => .error "maximum depth exceeded"
          | budget + 1 =>
              match parseElems fuel budget (skipWs r) with
              | .ok (es, r') => .ok (.arr es, r')
              | .error e     => .error e
      | (c :: _) =>
          if isDigit c then
            let (ds, r) := takeDigits (skipWs cs)
            .ok (.num (digitsToNat ds), r)
          else .error "unexpected character"
      | [] => .error "unexpected end of input"
  /-- Parse the remaining elements of an array (positioned just after `[` or `,`). -/
  def parseElems (fuel budget : Nat) (cs : List Char) : Except String (List Json × List Char) :=
    match fuel with
    | 0 => .error "out of fuel"
    | fuel + 1 =>
      match cs with
      | ']' :: r => .ok ([], r)
      | _ =>
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
end

/-- Parse a complete JSON value, rejecting nesting deeper than `maxDepth`. -/
def parse (maxDepth : Nat) (s : String) : Except String Json :=
  let cs := s.toList
  match parseVal (cs.length + 1) maxDepth cs with
  | .error e    => .error e
  | .ok (j, r)  => if (skipWs r).isEmpty then .ok j else .error "trailing characters"

/-! ### The depth bound, proven -/

mutual
  /-- A value the parser returns is no deeper than the budget it was given. -/
  theorem parseVal_depth_le :
      ∀ (fuel budget : Nat) (cs : List Char) (j : Json) (r : List Char),
        parseVal fuel budget cs = .ok (j, r) → j.depth ≤ budget
    | 0,        _,      _,  _, _, h => by simp [parseVal] at h
    | fuel + 1, budget, cs, j, r, h => by
        simp only [parseVal] at h
        repeat' split at h
        all_goals first
          | contradiction                                             -- `.error = .ok`
          | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
             obtain ⟨rfl, rfl⟩ := h
             first
               | (simp only [Json.depth]; omega)                      -- scalar: depth 0
               | (simp only [Json.depth]                              -- array
                  have hb := Json.maxDepth_le
                    (fun e he => parseElems_depth_le _ _ _ _ _ (by assumption) e he)
                  omega))
  /-- Every element the array parser returns is within budget. -/
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
               | exact absurd he (List.not_mem_nil e)                 -- es = []
               | (cases he with
                  | head => exact parseVal_depth_le _ _ _ _ _ (by assumption)
                  | tail _ he' => first
                      | exact parseElems_depth_le _ _ _ _ _ (by assumption) _ he'
                      | exact absurd he' (List.not_mem_nil _)))
end

/-- Anything `parse maxDepth` accepts is within `maxDepth`. -/
theorem parse_depth_le (maxDepth : Nat) (s : String) (j : Json) :
    parse maxDepth s = .ok j → j.depth ≤ maxDepth := by
  intro h
  simp only [parse] at h
  split at h
  · simp at h
  · rename_i j0 r heq
    split at h
    · cases h; exact parseVal_depth_le _ maxDepth _ _ _ heq
    · contradiction

end Qed
