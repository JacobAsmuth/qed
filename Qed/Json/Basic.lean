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
                  if c = ']' then .ok (.arr [], r')
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
                  if c = '}' then .ok (.obj [], r')
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

def parse (s : String) (maxDepth : Nat := 64) : Except String Json :=
  let cs := s.toList
  match parseVal (cs.length + 1) maxDepth cs with
  | .error e   => .error e
  | .ok (j, r) => if (skipWs r).isEmpty then .ok j else .error "trailing characters"

abbrev Json.parse (s : String) (maxDepth : Nat := 64) : Except String Json :=
  Qed.parse s maxDepth

def toHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))

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

def escapeCharsTR : List Char → String → String
  | [], acc      => acc
  | c :: cs, acc => escapeCharsTR cs (appendEscaped acc c)

def renderStrFast (s : String) : String :=
  escapeCharsTR s.toList "\"" ++ "\""

mutual
  def renderFast : Json → String
    | .null       => "null"
    | .bool true  => "true"
    | .bool false => "false"
    | .num n      => String.ofList (renderNumL n)
    | .str s      => renderStrFast s
    | .arr es     => "[" ++ renderElemsFast es ++ "]"
    | .obj ms     => "{" ++ renderMembersFast ms ++ "}"
  def renderElemsFast : List Json → String
    | []      => ""
    | e :: es => renderFast e ++ renderElemSepFast es
  def renderElemSepFast : List Json → String
    | []      => ""
    | x :: xs => "," ++ (renderFast x ++ renderElemSepFast xs)
  def renderMembersFast : List (String × Json) → String
    | []           => ""
    | (k, v) :: ms => renderStrFast k ++ ":" ++ (renderFast v ++ renderMemberSepFast ms)
  def renderMemberSepFast : List (String × Json) → String
    | []           => ""
    | (k, v) :: ms => "," ++ (renderStrFast k ++ ":" ++ (renderFast v ++ renderMemberSepFast ms))
end

private theorem ofList_append (xs ys : List Char) :
    String.ofList (xs ++ ys) = String.ofList xs ++ String.ofList ys := by
  ext; simp

private theorem ofList_cons (c : Char) (cs : List Char) :
    String.ofList (c :: cs) = String.singleton c ++ String.ofList cs := by
  ext; simp

private theorem appendEscaped_eq (acc : String) (c : Char) :
    appendEscaped acc c = acc ++ String.ofList (escapeCharL c) := by
  unfold appendEscaped escapeCharL
  repeat' split
  all_goals (ext; simp)

private theorem escapeCharsTR_eq (cs : List Char) (acc : String) :
    escapeCharsTR cs acc = acc ++ String.ofList (cs.flatMap escapeCharL) := by
  induction cs generalizing acc with
  | nil => simp [escapeCharsTR]
  | cons c cs ih =>
    simp only [escapeCharsTR, List.flatMap_cons, ih, ofList_append, appendEscaped_eq, String.append_assoc]

theorem renderStrFast_eq (s : String) : renderStrFast s = String.ofList (renderStrL s) := by
  unfold renderStrFast renderStrL
  rw [escapeCharsTR_eq, ofList_cons, ofList_append, String.append_assoc]; rfl

mutual
  theorem renderFast_eq (j : Json) : renderFast j = String.ofList (renderL j) := by
    cases j with
    | null | num _ => rfl
    | bool b => cases b <;> rfl
    | str s => exact renderStrFast_eq s
    | arr es =>
        unfold renderFast renderL
        rw [ofList_cons, ofList_append, renderElemsFast_eq, String.append_assoc]; rfl
    | obj ms =>
        unfold renderFast renderL
        rw [ofList_cons, ofList_append, renderMembersFast_eq, String.append_assoc]; rfl
  theorem renderElemsFast_eq (es : List Json) :
       renderElemsFast es = String.ofList (renderElemsL es) := by
    cases es with
    | nil => rfl
    | cons e es =>
        unfold renderElemsFast renderElemsL
        rw [ofList_append, renderFast_eq, renderElemSepFast_eq]
  theorem renderElemSepFast_eq (es : List Json) :
      renderElemSepFast es = String.ofList (renderElemSep es) := by
    cases es with
    | nil => rfl
    | cons x xs =>
        unfold renderElemSepFast renderElemSep
        rw [ofList_cons, ofList_append, renderFast_eq, renderElemSepFast_eq]; rfl
  theorem renderMembersFast_eq (ms : List (String × Json)) :
      renderMembersFast ms = String.ofList (renderMembersL ms) := by
    cases ms with
    | nil => rfl
    | cons kv ms =>
        rcases kv with ⟨k, v⟩
        unfold renderMembersFast renderMembersL
        rw [ofList_append, ofList_cons, ofList_append, renderStrFast_eq,
          renderFast_eq, renderMemberSepFast_eq, String.append_assoc]; rfl
  theorem renderMemberSepFast_eq (ms : List (String × Json)) :
      renderMemberSepFast ms = String.ofList (renderMemberSep ms) := by
    cases ms with
    | nil => rfl
    | cons kv ms =>
        rcases kv with ⟨k, v⟩
        unfold renderMemberSepFast renderMemberSep
        rw [ofList_cons, ofList_append, ofList_cons, ofList_append,
          renderStrFast_eq, renderFast_eq, renderMemberSepFast_eq, String.append_assoc]; rfl
end

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

def Json.path? (j : Json) : List String → Option Json
  | []      => some j
  | k :: ks => (j.get? k).bind (fun v => v.path? ks)

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
instance [ToJson α] [ToJson β] : ToJson (α × β) := ⟨fun (a, b) => .arr [toJson a, toJson b]⟩

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

instance : ToJson Float := ⟨fun f => (Json.parse (toString f)).toOption.getD (.num ⟨0, 0⟩)⟩
instance : FromJson Float :=
  ⟨fun j => match j with
    | .num n => let mag := Float.ofScientific n.mantissa.natAbs (n.exponent < 0) n.exponent.natAbs
                .ok (if n.mantissa < 0 then -mag else mag)
    | _ => .error "expected a number"⟩

class FromJsonField (α : Type) where
  fromField : Json → String → Except String α
export FromJsonField (fromField)

instance (priority := low) [FromJson α] : FromJsonField α where
  fromField j key := match j.field key with
    | .error e => .error e
    | .ok v    => match (fromJson v : Except String α) with
                  | .ok a    => .ok a
                  | .error e => .error s!"{key}: {e}"

instance [FromJson α] : FromJsonField (Option α) where
  fromField j key := match j.get? key with
    | none       => .ok none
    | some .null => .ok none
    | some v     => match (fromJson v : Except String α) with
                    | .ok a    => .ok (some a)
                    | .error e => .error s!"{key}: {e}"

end Qed
