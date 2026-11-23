import Qed.Html

namespace Qed

structure JsonNumber where
  mantissa : Int
  exponent : Int := 0
deriving Repr, BEq, DecidableEq, Inhabited

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

theorem maxArr_le_iff {k : Nat} : ∀ {es : List Json}, maxArr es ≤ k ↔ ∀ e ∈ es, depth e ≤ k
  | []      => by simp [maxArr]
  | e :: es => by simp [maxArr, Nat.max_le, maxArr_le_iff (es := es)]

theorem maxObj_le_iff {k : Nat} :
    ∀ {ms : List (String × Json)}, maxObj ms ≤ k ↔ ∀ kv ∈ ms, depth kv.2 ≤ k
  | []           => by simp [maxObj]
  | (_, v) :: ms => by simp [maxObj, Nat.max_le, maxObj_le_iff (ms := ms)]

end Json

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

abbrev hexVal : Char → Option Nat := unhexNat?

def hex4 (a b c d : Char) : Option Nat := do
  let va ← hexVal a; let vb ← hexVal b; let vc ← hexVal c; let vd ← hexVal d
  return ((va * 16 + vb) * 16 + vc) * 16 + vd

def unescape : Char → Option Char
  | '"'  => some '"'  | '\\' => some '\\' | '/' => some '/'
  | 'n'  => some '\n' | 'r'  => some '\r' | 't' => some '\t'
  | 'b'  => some (Char.ofNat 8) | 'f' => some (Char.ofNat 12)
  | _    => none

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

def parseStrFastAux (acc : String) : List Char → Except String (String × List Char)
  | '"' :: rest => .ok (acc, rest)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest =>
      match hex4 a b c d with
      | some n => parseStrFastAux (acc.push (Char.ofNat n)) rest
      | none   => .error "invalid \\u escape"
  | '\\' :: e :: rest =>
      match unescape e with
      | some ch => parseStrFastAux (acc.push ch) rest
      | none    => .error "invalid escape"
  | c :: rest => parseStrFastAux (acc.push c) rest
  | []        => .error "unterminated string"

def parseStrFast (cs : List Char) : Except String (String × List Char) := parseStrFastAux "" cs

private theorem push_ofList_rev (acc : List Char) (c : Char) :
    (String.ofList acc.reverse).push c = String.ofList (c :: acc).reverse := by
  ext; simp

private theorem parseStrFastAux_eq (acc : List Char) (cs : List Char) :
    parseStrFastAux (String.ofList acc.reverse) cs = parseStrAux acc cs := by
  induction acc, cs using parseStrAux.induct with
  | case1 acc rest => rfl
  | case2 acc a b c d rest n hn ih => simp only [parseStrFastAux, parseStrAux, hn, push_ofList_rev, ih]
  | case3 acc a b c d rest hn => simp only [parseStrFastAux, parseStrAux, hn]
  | case4 acc e rest _ ch hch ih => simp only [parseStrFastAux, parseStrAux, hch, push_ofList_rev, ih]
  | case5 acc e rest _ hch => simp only [parseStrFastAux, parseStrAux, hch]
  | case6 acc c rest _ _ _ ih => simp only [parseStrFastAux, parseStrAux, push_ofList_rev, ih]
  | case7 acc => rfl

@[csimp] theorem parseStr_eq_parseStrFast : @parseStr = @parseStrFast := by
  funext cs; exact (parseStrFastAux_eq [] cs).symm

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

mutual
  def parseVal (fuel budget : Nat) (cs : List Char) : Except String (Json × List Char) :=
    match fuel with
    | 0 => .error "out of fuel"
    | fuel + 1 =>
      match skipWs cs with
      | 'n' :: 'u' :: 'l' :: 'l' :: r        => .ok (.null, r)
      | 't' :: 'r' :: 'u' :: 'e' :: r        => .ok (.bool true, r)
      | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => .ok (.bool false, r)
      | '"' :: r => do let (s, r') ← parseStr r; return (.str s, r')
      | '[' :: r =>
          match budget with
          | 0          => .error "maximum depth exceeded"
          | budget + 1 =>
              match skipWs r with
              | []      => .error "unexpected end of input"
              | c :: r' =>
                  if c = ']' then .ok (.arr [], r')
                  else do let (es, r'') ← parseElems fuel budget (c :: r'); return (.arr es, r'')
      | '{' :: r =>
          match budget with
          | 0          => .error "maximum depth exceeded"
          | budget + 1 =>
              match skipWs r with
              | []      => .error "unexpected end of input"
              | c :: r' =>
                  if c = '}' then .ok (.obj [], r')
                  else do let (ms, r'') ← parseMembers fuel budget (c :: r'); return (.obj ms, r'')
      | c :: rest =>
          if c == '-' || isDigit c then do let (n, r') ← parseNum (c :: rest); return (.num n, r')
          else .error "unexpected character"
      | [] => .error "unexpected end of input"
  def parseElems (fuel budget : Nat) (cs : List Char) : Except String (List Json × List Char) :=
    match fuel with
    | 0 => .error "out of fuel"
    | fuel + 1 => do
      let (v, r) ← parseVal fuel budget cs
      match skipWs r with
      | ',' :: r' => let (vs, r'') ← parseElems fuel budget (skipWs r'); return (v :: vs, r'')
      | ']' :: r' => .ok ([v], r')
      | _         => .error "expected ',' or ']'"
  def parseMembers (fuel budget : Nat) (cs : List Char) :
      Except String (List (String × Json) × List Char) :=
    match fuel with
    | 0 => .error "out of fuel"
    | fuel + 1 =>
      match skipWs cs with
      | '"' :: r => do
          let (key, r1) ← parseStr r
          match skipWs r1 with
          | ':' :: r2 =>
              let (v, r3) ← parseVal fuel budget (skipWs r2)
              match skipWs r3 with
              | ',' :: r4 => let (ms, r5) ← parseMembers fuel budget (skipWs r4); return ((key, v) :: ms, r5)
              | '}' :: r4 => .ok ([(key, v)], r4)
              | _         => .error "expected ',' or '}'"
          | _ => .error "expected ':'"
      | _ => .error "expected string key"
end

def parse (s : String) (maxDepth : Nat := 64) : Except String Json :=
  let cs := s.toList
  match parseVal (cs.length + 1) maxDepth cs with
  | .error e   => .error e
  | .ok (j, r) => if (skipWs r).isEmpty then .ok j else .error "trailing characters"

abbrev Json.parse (s : String) (maxDepth : Nat := 64) : Except String Json :=
  Qed.parse s maxDepth

abbrev toHexDigit : Nat → Char := hexDigitLower

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

def natDigitsAux (n : Nat) (acc : List Char) : List Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n % 10) :: acc
  else natDigitsAux (n / 10) (Char.ofNat ('0'.toNat + n % 10) :: acc)
termination_by n
decreasing_by omega

def intCharsL (i : Int) : List Char :=
  (if i < 0 then ['-'] else []) ++ natDigitsAux i.natAbs []

def Json.renderNumL (n : JsonNumber) : List Char :=
  intCharsL n.mantissa ++ (if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent)

namespace Json
mutual
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
    | e :: es => match es with
      | []     => renderL e
      | _ :: _ => renderL e ++ ',' :: renderElemsL es
  def renderMembersL : List (String × Json) → List Char
    | []           => []
    | (k, v) :: ms => match ms with
      | []     => renderStrL k ++ ':' :: renderL v
      | _ :: _ => renderStrL k ++ ':' :: (renderL v ++ ',' :: renderMembersL ms)
end

def render (j : Json) : String := String.ofList (renderL j)

def appendEscaped (acc : String) (c : Char) : String :=
  match c with
  | '"'  => acc ++ "\\\"" | '\\' => acc ++ "\\\\"
  | '\n' => acc ++ "\\n"  | '\r' => acc ++ "\\r" | '\t' => acc ++ "\\t"
  | c =>
      if c.toNat < 0x20 then
        let n := c.toNat
        acc ++ String.ofList ['\\', 'u', toHexDigit (n / 4096 % 16), toHexDigit (n / 256 % 16),
                                         toHexDigit (n / 16 % 16),   toHexDigit (n % 16)]
      else acc.push c

@[inline] def needsJsonEscape (c : Char) : Bool :=
  c == '"' || c == '\\' || c.toNat < 0x20

@[inline] private def needsJsonEscapeByte (b : UInt8) : Bool :=
  b < 32 || b == 34 || b == 92

def renderStrAcc (s : String) (acc : String) : String :=
  let acc1 := acc.push '"'
  let acc2 := if !hasAsciiByte s needsJsonEscapeByte then acc1 ++ s else s.foldl appendEscaped acc1
  acc2.push '"'

def pushChars (acc : String) : List Char → String
  | []      => acc
  | c :: cs => pushChars (acc.push c) cs

private def pushNatAcc (n : Nat) (acc : String) : String :=
  if n < 10 then
    acc.push (Char.ofNat ('0'.toNat + n))
  else if n < 100 then
    (acc.push (Char.ofNat ('0'.toNat + n / 10))).push (Char.ofNat ('0'.toNat + n % 10))
  else
    pushChars acc (natDigitsAux n [])

def pushIntAcc (i : Int) (acc : String) : String :=
  pushNatAcc i.natAbs (if i < 0 then acc.push '-' else acc)

def renderNumAcc (n : JsonNumber) (acc : String) : String :=
  let acc1 := pushIntAcc n.mantissa acc
  if n.exponent == 0 then acc1 else pushIntAcc n.exponent (acc1.push 'e')

mutual
  def renderAcc (acc : String) : Json → String
    | .null       => acc ++ "null"
    | .bool true  => acc ++ "true"
    | .bool false => acc ++ "false"
    | .num n      => renderNumAcc n acc
    | .str s      => renderStrAcc s acc
    | .arr es     => (renderElemsAcc (acc.push '[') es).push ']'
    | .obj ms     => (renderMembersAcc (acc.push '{') ms).push '}'
  def renderElemsAcc (acc : String) : List Json → String
    | []      => acc
    | e :: es => match es with
      | []     => renderAcc acc e
      | _ :: _ => renderElemsAcc ((renderAcc acc e).push ',') es
  def renderMembersAcc (acc : String) : List (String × Json) → String
    | []           => acc
    | (k, v) :: ms => match ms with
      | []     => renderAcc ((renderStrAcc k acc).push ':') v
      | _ :: _ => renderMembersAcc ((renderAcc ((renderStrAcc k acc).push ':') v).push ',') ms
end

def renderFast (j : Json) : String := renderAcc "" j

private theorem ofList_append (xs ys : List Char) :
    String.ofList (xs ++ ys) = String.ofList xs ++ String.ofList ys := by
  ext; simp

private theorem ofList_cons (c : Char) (cs : List Char) :
    String.ofList (c :: cs) = String.singleton c ++ String.ofList cs := by
  ext; simp

private theorem push_eq_append (acc : String) (c : Char) :
    acc.push c = acc ++ String.singleton c := by
  ext; simp

private theorem pushChars_eq (acc : String) (cs : List Char) :
    pushChars acc cs = acc ++ String.ofList cs := by
  induction cs generalizing acc with
  | nil => simp [pushChars]
  | cons c cs ih =>
      simp only [pushChars, ih, push_eq_append, ofList_cons, String.append_assoc]

private theorem appendEscaped_eq (acc : String) (c : Char) :
    appendEscaped acc c = acc ++ String.ofList (escapeCharL c) := by
  unfold appendEscaped escapeCharL
  repeat' split
  all_goals (ext; simp)

private theorem foldl_appendEscaped_eq (cs : List Char) (acc : String) :
    cs.foldl appendEscaped acc = acc ++ String.ofList (cs.flatMap escapeCharL) := by
  induction cs generalizing acc with
  | nil => simp
  | cons c cs ih =>
      simp only [List.foldl_cons, List.flatMap_cons, ih, ofList_append, appendEscaped_eq, String.append_assoc]

private theorem escapeCharL_of_not_needs {c : Char} (h : needsJsonEscape c = false) :
    escapeCharL c = [c] := by
  simp only [needsJsonEscape, Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not] at h
  unfold escapeCharL
  split <;> first | exact absurd rfl h.1.1 | exact absurd rfl h.1.2 | (exfalso; apply h.2; decide) | simp [h.2]

private theorem flatMap_escapeCharL_of_none : ∀ (cs : List Char),
    cs.any needsJsonEscape = false → cs.flatMap escapeCharL = cs
  | [], _ => rfl
  | c :: cs, h => by
      simp only [List.any_cons, Bool.or_eq_false_iff] at h
      simp [List.flatMap_cons, escapeCharL_of_not_needs h.1, flatMap_escapeCharL_of_none cs h.2]

private theorem needsJsonEscapeByte_hi :
    ∀ b : BitVec 8, b.toNat ≥ 128 → needsJsonEscapeByte ⟨b⟩ = false := by decide

private theorem needsJsonEscapeByte_lo :
    ∀ n : Fin 128, needsJsonEscapeByte (UInt8.ofNat n.val) = needsJsonEscape (Char.ofNat n.val) := by decide

private theorem hasJsonEscapeByte_eq (s : String) :
    hasAsciiByte s needsJsonEscapeByte = s.toList.any needsJsonEscape :=
  hasAsciiByte_eq_any s needsJsonEscapeByte needsJsonEscape
    (fun b => needsJsonEscapeByte_hi b.toBitVec)
    (fun c hc => by simpa [Char.ofNat_toNat] using needsJsonEscapeByte_lo ⟨c.toNat, by omega⟩)
    (fun c hgt => by
      simp only [needsJsonEscape, Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
      refine ⟨⟨?_, ?_⟩, by omega⟩ <;> (rintro rfl; exact absurd hgt (by decide)))

theorem renderStrAcc_eq (s acc : String) :
    renderStrAcc s acc = acc ++ String.ofList (renderStrL s) := by
  unfold renderStrAcc renderStrL
  have hfold : s.foldl appendEscaped (acc.push '"') = s.toList.foldl appendEscaped (acc.push '"') := by simp
  dsimp only; rw [hfold, hasJsonEscapeByte_eq]
  cases ha : s.toList.any needsJsonEscape with
  | false =>
      simp only [Bool.not_false, ↓reduceIte, flatMap_escapeCharL_of_none s.toList ha,
        push_eq_append, ofList_cons, ofList_append, String.ofList_toList, String.append_assoc]; rfl
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, foldl_appendEscaped_eq,
        push_eq_append, ofList_cons, ofList_append, String.append_assoc]; rfl

private theorem pushNatAcc_eq (n : Nat) (acc : String) :
    pushNatAcc n acc = acc ++ String.ofList (natDigitsAux n []) := by
  unfold pushNatAcc
  split
  · rename_i h10
    rw [natDigitsAux, if_pos h10, show n % 10 = n from Nat.mod_eq_of_lt h10]
    ext; simp
  · rename_i hge10
    split
    · rename_i h100
      have hd : n / 10 < 10 := by omega
      rw [natDigitsAux, if_neg hge10, natDigitsAux, if_pos hd, show (n / 10) % 10 = n / 10 from Nat.mod_eq_of_lt hd]
      ext; simp [List.append_assoc]
    · exact pushChars_eq acc (natDigitsAux n [])

private theorem pushIntAcc_eq (i : Int) (acc : String) :
    pushIntAcc i acc = acc ++ String.ofList (intCharsL i) := by
  unfold pushIntAcc intCharsL
  split <;> simp [pushNatAcc_eq, push_eq_append, String.append_assoc]

private theorem renderNumAcc_eq (n : JsonNumber) (acc : String) :
    renderNumAcc n acc = acc ++ String.ofList (renderNumL n) := by
  unfold renderNumAcc renderNumL
  split <;> simp [pushIntAcc_eq, push_eq_append, String.append_assoc]

mutual
  theorem renderAcc_eq (acc : String) (j : Json) :
      renderAcc acc j = acc ++ String.ofList (renderL j) := by
    cases j with
    | null => rfl
    | bool b => cases b <;> rfl
    | num n => exact renderNumAcc_eq n acc
    | str s => exact renderStrAcc_eq s acc
    | arr es =>
        unfold renderAcc renderL
        rw [renderElemsAcc_eq, push_eq_append, push_eq_append, ofList_cons, ofList_append, String.append_assoc, String.append_assoc]; rfl
    | obj ms =>
        unfold renderAcc renderL
        rw [renderMembersAcc_eq, push_eq_append, push_eq_append, ofList_cons, ofList_append, String.append_assoc, String.append_assoc]; rfl
  theorem renderElemsAcc_eq (acc : String) (es : List Json) :
      renderElemsAcc acc es = acc ++ String.ofList (renderElemsL es) := by
    match es with
    | [] => simp [renderElemsAcc, renderElemsL]
    | [e] => exact renderAcc_eq acc e
    | e :: x :: xs =>
        unfold renderElemsAcc renderElemsL
        rw [renderElemsAcc_eq, push_eq_append, renderAcc_eq, ofList_append, ofList_cons,
          String.append_assoc, String.append_assoc]
  theorem renderMembersAcc_eq (acc : String) (ms : List (String × Json)) :
      renderMembersAcc acc ms = acc ++ String.ofList (renderMembersL ms) := by
    match ms with
    | [] => simp [renderMembersAcc, renderMembersL]
    | [(k, v)] =>
        simp only [renderMembersAcc, renderMembersL, renderAcc_eq, push_eq_append, renderStrAcc_eq,
          ofList_append, ofList_cons, String.append_assoc]
    | (k, v) :: kv' :: ms =>
        rw [renderMembersAcc.eq_def, renderMembersL.eq_def]; dsimp only
        rw [renderMembersAcc_eq, push_eq_append, renderAcc_eq, push_eq_append, renderStrAcc_eq,
          ofList_append, ofList_cons, ofList_append, ofList_cons]
        simp only [String.append_assoc]
end

theorem renderFast_eq (j : Json) : renderFast j = String.ofList (renderL j) := by
  unfold renderFast; rw [renderAcc_eq]; simp

@[csimp] theorem render_eq_renderFast : @Json.render = @Json.renderFast := by
  funext j; exact (renderFast_eq j).symm

end Json

def Json.bool? : Json → Option Bool                  | .bool b => some b | _ => none
def Json.str?  : Json → Option String                | .str s  => some s | _ => none
def Json.num?  : Json → Option JsonNumber            | .num n  => some n | _ => none
def Json.arr?  : Json → Option (List Json)           | .arr es => some es | _ => none
def Json.obj?  : Json → Option (List (String × Json))| .obj ms => some ms | _ => none

def Json.field (j : Json) (key : String) : Except String Json :=
  match j with
  | .obj ms =>
      -- Duplicate keys take the last value, matching `JSON.parse`.
      match ms.foldl (fun acc kv => if kv.1 == key then some kv.2 else acc) none with
      | some v => .ok v
      | none   => .error s!"missing key '{key}'"
  | _ => .error "expected an object"

def Json.get? (j : Json) (key : String) : Option Json := (j.field key).toOption

/-- Walks a dot-separated path (object keys and numeric array indices, e.g. `"choices.0.delta.content"`). -/
def Json.atPath (j : Json) (path : String) : Option Json :=
  (path.splitOn ".").foldlM (init := j) fun cur seg =>
    match cur with
    | .arr es => seg.toNat?.bind (es[·]?)
    | .obj _  => cur.get? seg
    | _       => none

/-- Parses a JSON string and extracts the value at a dot-separated path. -/
def Json.path? (raw : String) (path : String) : Option Json :=
  (Json.parse raw).toOption.bind (·.atPath path)

/-- Parses a JSON string and extracts a `String` at a dot-separated path (defaulting to `default`). -/
def Json.pathStr (raw : String) (path : String) (default : String := "") : String :=
  ((Json.path? raw path).bind (·.str?)).getD default

class ToJson (α : Type) where toJson : α → Json
class FromJson (α : Type) where fromJson : Json → Except String α
export ToJson (toJson)
export FromJson (fromJson)

instance : ToJson Unit := ⟨fun () => .arr []⟩
instance : ToJson Json := ⟨id⟩
instance : ToJson JsonNumber := ⟨.num⟩
instance : ToJson Bool := ⟨.bool⟩
instance : ToJson String := ⟨.str⟩
instance : ToJson Int := ⟨fun i => .num ⟨i, 0⟩⟩
instance : ToJson Nat := ⟨fun n => .num ⟨(n : Int), 0⟩⟩
instance [ToJson α] : ToJson (List α)   := ⟨fun xs => .arr (xs.map toJson)⟩
instance [ToJson α] : ToJson (Array α)  := ⟨fun xs => .arr (xs.toList.map toJson)⟩
instance [ToJson α] : ToJson (Option α) := ⟨fun a => a.elim .null toJson⟩
instance [ToJson α] [ToJson β] : ToJson (α × β) := ⟨fun (a, b) => .arr [toJson a, toJson b]⟩
instance [ToJson α] [ToJson β] : ToJson (Sum α β) := ⟨fun
  | .inl a => .arr [.num ⟨0, 0⟩, toJson a]
  | .inr b => .arr [.num ⟨1, 0⟩, toJson b]⟩

instance : FromJson Unit := ⟨fun | .arr [] => .ok () | _ => .error "expected []"⟩
instance : FromJson Json := ⟨.ok⟩
instance : FromJson JsonNumber := ⟨fun j => j.num?.elim (.error "expected a number") .ok⟩
instance : FromJson Bool := ⟨fun j => j.bool?.elim (.error "expected a boolean") .ok⟩
instance : FromJson String := ⟨fun j => j.str?.elim (.error "expected a string") .ok⟩

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
instance [FromJson α] [FromJson β] : FromJson (α × β) :=
  ⟨fun | .arr [ja, jb] => do return (← fromJson ja, ← fromJson jb)
       | _             => .error "expected a 2-element array"⟩
instance [FromJson α] [FromJson β] : FromJson (Sum α β) :=
  ⟨fun | .arr [.num ⟨0, 0⟩, ja] => (fromJson ja : Except String α).map Sum.inl
       | .arr [.num ⟨1, 0⟩, jb] => (fromJson jb : Except String β).map Sum.inr
       | _                      => .error "expected a tagged sum array"⟩

instance : ToJson Float := ⟨fun f => (Json.parse (toString f)).toOption.getD (.num ⟨0, 0⟩)⟩
instance : FromJson Float :=
  ⟨fun j => match j with
    | .num n => let mag := Float.ofScientific n.mantissa.natAbs (n.exponent < 0) n.exponent.natAbs
                .ok (if n.mantissa < 0 then -mag else mag)
    | _ => .error "expected a number"⟩

class FromJsonField (α : Type) where
  fromField : Json → String → Except String α
export FromJsonField (fromField)

@[inline] abbrev fromFieldVal [FromJson α] (key : String) (v : Json) : Except String α :=
  match (fromJson v : Except String α) with
  | .ok a    => .ok a
  | .error e => .error s!"{key}: {e}"

instance (priority := low) [FromJson α] : FromJsonField α where
  fromField j key := match j.field key with
    | .error e => .error e
    | .ok v    => fromFieldVal key v

instance [FromJson α] : FromJsonField (Option α) where
  fromField j key := match j.get? key with
    | none | some .null => .ok none
    | some v            => (fromFieldVal key v).map some

end Qed
