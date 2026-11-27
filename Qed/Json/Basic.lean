import Qed.Html

namespace Qed

structure JsonNumber where
  mantissa : Int
  exponent : Int := 0
deriving Repr, BEq, DecidableEq, Inhabited

def JsonNumber.toInt? (n : JsonNumber) : Option Int :=
  if 0 ≤ n.exponent then some (n.mantissa * (10 ^ n.exponent.toNat))
  else let d : Int := 10 ^ (-n.exponent).toNat; if n.mantissa % d == 0 then some (n.mantissa / d) else none

inductive Json where
  | null | bool (b : Bool) | num (n : JsonNumber) | str (s : String)
  | arr (elems : List Json) | obj (members : List (String × Json))
deriving Inhabited

namespace Json
mutual
  def depth : Json → Nat | .arr es => 1 + maxArr es | .obj ms => 1 + maxObj ms | _ => 0
  def maxArr : List Json → Nat | [] => 0 | e :: es => Nat.max (depth e) (maxArr es)
  def maxObj : List (String × Json) → Nat | [] => 0 | (_, v) :: ms => Nat.max (depth v) (maxObj ms)
end
theorem maxArr_le_iff {k : Nat} : ∀ {es : List Json}, maxArr es ≤ k ↔ ∀ e ∈ es, depth e ≤ k
  | [] => by simp only [maxArr, Nat.zero_le, List.not_mem_nil, false_implies, implies_true]
  | _ :: es => by simp only [maxArr, Nat.max_le, maxArr_le_iff (es := es), List.mem_cons, forall_eq_or_imp]
theorem maxObj_le_iff {k : Nat} : ∀ {ms : List (String × Json)}, maxObj ms ≤ k ↔ ∀ kv ∈ ms, depth kv.2 ≤ k
  | [] => by simp only [maxObj, Nat.zero_le, List.not_mem_nil, false_implies, implies_true]
  | (_, _) :: ms => by simp only [maxObj, Nat.max_le, maxObj_le_iff (ms := ms), List.mem_cons, forall_eq_or_imp]
end Json

def isWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def skipWs : List Char → List Char | c :: cs => if isWs c then skipWs cs else c :: cs | [] => []
def takeDigits : List Char → List Char × List Char
  | c :: cs => if isDigit c then let (ds, r) := takeDigits cs; (c :: ds, r) else ([], c :: cs)
  | [] => ([], [])
def digitsToInt (ds : List Char) : Int := (ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 : Nat)
abbrev hexVal : Char → Option Nat := unhexNat?
def hex4 (a b c d : Char) : Option Nat := do
  return (((← hexVal a) * 16 + (← hexVal b)) * 16 + (← hexVal c)) * 16 + (← hexVal d)
def unescape : Char → Option Char
  | '"' => some '"' | '\\' => some '\\' | '/' => some '/' | 'n' => some '\n'
  | 'r' => some '\r' | 't' => some '\t' | 'b' => some (Char.ofNat 8) | 'f' => some (Char.ofNat 12) | _ => none

def parseStrAux (acc : List Char) : List Char → Except String (String × List Char)
  | [] => .error "unterminated string"
  | c :: rest =>
      if c == '"' then .ok (String.ofList acc.reverse, rest)
      else if c == '\\' then match rest with
        | 'u' :: a :: b :: c :: d :: r => (hex4 a b c d).elim (.error "invalid \\u escape") fun n => parseStrAux (Char.ofNat n :: acc) r
        | e :: r => (unescape e).elim (.error "invalid escape") fun ch => parseStrAux (ch :: acc) r
        | [] => .error "unterminated string"
      else parseStrAux (c :: acc) rest
def parseStr (cs : List Char) : Except String (String × List Char) := parseStrAux [] cs

@[inline] def parseSigned (allowPlus : Bool) (cs : List Char) : Int × List Char × List Char :=
  let (sgn, cs1) : Int × List Char := match cs with
    | c :: r => if c == '-' then (-1, r) else if allowPlus && c == '+' then (1, r) else (1, cs)
    | [] => (1, [])
  let (ds, rest) := takeDigits cs1; (sgn, ds, rest)
def parseFrac : List Char → List Char × List Char | c :: r => if c == '.' then takeDigits r else ([], c :: r) | [] => ([], [])
def parseExp : List Char → Int × List Char
  | c :: r => if c == 'e' || c == 'E' then let (sgn, eds, r2) := parseSigned true r; (sgn * digitsToInt eds, r2) else (0, c :: r)
  | [] => (0, [])
def parseNum (cs : List Char) : Except String (JsonNumber × List Char) :=
  let (sgn, intDs, cs2) := parseSigned false cs
  if intDs.isEmpty then .error "expected a number"
  else let (fracDs, cs3) := parseFrac cs2; let (expVal, cs4) := parseExp cs3
       .ok (⟨sgn * digitsToInt (intDs ++ fracDs), expVal - (fracDs.length : Int)⟩, cs4)

def parseLit : List Char → Except String (Json × List Char)
  | 'n' :: 'u' :: 'l' :: 'l' :: r => .ok (.null, r) | 't' :: 'r' :: 'u' :: 'e' :: r => .ok (.bool true, r)
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: r => .ok (.bool false, r) | _ => .error "unexpected character"

@[inline] def parseContainer {α : Type} (close : Char) (empty : Json) (wrap : α → Json)
    (parseItems : Nat → List Char → Except String (α × List Char)) : Nat → List Char → Except String (Json × List Char)
  | 0, _ => .error "maximum depth exceeded"
  | b + 1, r => match skipWs r with
      | [] => .error "unexpected end of input"
      | c :: r' => if c == close then .ok (empty, r') else (parseItems b (c :: r')).map fun (xs, r'') => (wrap xs, r'')

@[inline] def parseSep {α : Type} (close : Char) (err : String) (step : List Char → Except String (α × List Char))
    (rec : List Char → Except String (List α × List Char)) (cs : List Char) : Except String (List α × List Char) :=
  (step cs).bind fun (v, r) => match skipWs r with
    | [] => .error err
    | c :: r' => if c == ',' then (rec (skipWs r')).map fun (vs, r'') => (v :: vs, r'') else if c == close then .ok ([v], r') else .error err

@[inline] def parseMember (pVal : List Char → Except String (Json × List Char)) (cs : List Char) : Except String ((String × Json) × List Char) :=
  match skipWs cs with
  | '"' :: r => (parseStr r).bind fun (k, r1) => match skipWs r1 with
      | ':' :: r2 => (pVal (skipWs r2)).map fun (v, r3) => ((k, v), r3)
      | _ => .error "expected ':'"
  | _ => .error "expected string key"

mutual
  def parseVal : Nat → Nat → List Char → Except String (Json × List Char)
    | 0, _, _ => .error "out of fuel"
    | fuel + 1, budget, cs => match skipWs cs with
      | [] => .error "unexpected end of input"
      | c :: r =>
          if c == '"' then (parseStr r).map fun (s, r') => (.str s, r')
          else if c == '[' then parseContainer ']' (.arr []) .arr (parseElems fuel) budget r
          else if c == '{' then parseContainer '}' (.obj []) .obj (parseMembers fuel) budget r
          else if c == '-' || isDigit c then (parseNum (c :: r)).map fun (n, r') => (.num n, r')
          else parseLit (c :: r)
  def parseElems : Nat → Nat → List Char → Except String (List Json × List Char)
    | 0, _, _ => .error "out of fuel"
    | fuel + 1, budget, cs => parseSep ']' "expected ',' or ']'" (parseVal fuel budget) (parseElems fuel budget) cs
  def parseMembers : Nat → Nat → List Char → Except String (List (String × Json) × List Char)
    | 0, _, _ => .error "out of fuel"
    | fuel + 1, budget, cs => parseSep '}' "expected ',' or '}'" (parseMember (parseVal fuel budget)) (parseMembers fuel budget) cs
end

def parse (s : String) (maxDepth : Nat := 64) : Except String Json :=
  let cs := s.toList; (parseVal (cs.length + 1) maxDepth cs).bind fun (j, r) => if (skipWs r).isEmpty then .ok j else .error "trailing characters"
abbrev Json.parse (s : String) (maxDepth : Nat := 64) : Except String Json := Qed.parse s maxDepth
abbrev toHexDigit : Nat → Char := hexDigitLower
def hexEscapeL (n : Nat) : List Char := ['\\', 'u', toHexDigit (n / 4096 % 16), toHexDigit (n / 256 % 16), toHexDigit (n / 16 % 16), toHexDigit (n % 16)]
def escapeCharL : Char → List Char
  | '"' => ['\\', '"'] | '\\' => ['\\', '\\'] | '\n' => ['\\', 'n'] | '\r' => ['\\', 'r'] | '\t' => ['\\', 't']
  | c => if c.toNat < 0x20 then hexEscapeL c.toNat else [c]
def Json.renderStrL (s : String) : List Char := '"' :: (s.toList.flatMap escapeCharL ++ ['"'])

def natDigitsAux (n : Nat) (acc : List Char) : List Char :=
  let acc' := Char.ofNat ('0'.toNat + n % 10) :: acc; if n < 10 then acc' else natDigitsAux (n / 10) acc'
termination_by n
decreasing_by omega

def intCharsL (i : Int) : List Char := (if i < 0 then ['-'] else []) ++ natDigitsAux i.natAbs []
def Json.renderNumL (n : JsonNumber) : List Char := intCharsL n.mantissa ++ (if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent)

namespace Json
mutual
  def renderL : Json → List Char
    | .null => ['n', 'u', 'l', 'l'] | .bool true => ['t', 'r', 'u', 'e'] | .bool false => ['f', 'a', 'l', 's', 'e']
    | .num n => renderNumL n | .str s => renderStrL s
    | .arr es => '[' :: (renderElemsL es ++ [']']) | .obj ms => '{' :: (renderMembersL ms ++ ['}'])
  def renderElemsL : List Json → List Char | [] => [] | [e] => renderL e | e :: x :: xs => renderL e ++ ',' :: renderElemsL (x :: xs)
  def renderMembersL : List (String × Json) → List Char
    | [] => [] | [(k, v)] => renderStrL k ++ ':' :: renderL v | (k, v) :: m :: ms => renderStrL k ++ ':' :: (renderL v ++ ',' :: renderMembersL (m :: ms))
end
def render (j : Json) : String := String.ofList (renderL j)

private def appendEscaped (acc : String) : Char → String
  | '"' => acc ++ "\\\"" | '\\' => acc ++ "\\\\" | '\n' => acc ++ "\\n" | '\r' => acc ++ "\\r" | '\t' => acc ++ "\\t"
  | c => if c.toNat < 0x20 then acc ++ String.ofList (hexEscapeL c.toNat) else acc.push c
@[inline] private def needsJsonEscape (c : Char) : Bool := c == '"' || c == '\\' || c.toNat < 0x20
@[inline] private def needsJsonEscapeByte (b : UInt8) : Bool := b == 34 || b == 92 || b < 32
private def renderStrAcc (s acc : String) : String :=
  let acc1 := acc.push '"'; (if !hasAsciiByte s needsJsonEscapeByte then acc1 ++ s else s.foldl appendEscaped acc1).push '"'
private def pushNatAcc (n : Nat) (acc : String) : String :=
  if n < 10 then acc.push (Char.ofNat ('0'.toNat + n))
  else if n < 100 then (acc.push (Char.ofNat ('0'.toNat + n / 10))).push (Char.ofNat ('0'.toNat + n % 10))
  else (natDigitsAux n []).foldl String.push acc
private def pushIntAcc (i : Int) (acc : String) : String := pushNatAcc i.natAbs (if i < 0 then acc.push '-' else acc)
private def renderNumAcc (n : JsonNumber) (acc : String) : String :=
  let acc1 := pushIntAcc n.mantissa acc; if n.exponent == 0 then acc1 else pushIntAcc n.exponent (acc1.push 'e')

mutual
  private def renderAcc (acc : String) : Json → String
    | .null => acc ++ "null" | .bool true => acc ++ "true" | .bool false => acc ++ "false"
    | .num n => renderNumAcc n acc | .str s => renderStrAcc s acc
    | .arr es => (renderElemsAcc (acc.push '[') es).push ']' | .obj ms => (renderMembersAcc (acc.push '{') ms).push '}'
  private def renderElemsAcc (acc : String) : List Json → String
    | [] => acc | [e] => renderAcc acc e | e :: x :: xs => renderElemsAcc ((renderAcc acc e).push ',') (x :: xs)
  private def renderMembersAcc (acc : String) : List (String × Json) → String
    | [] => acc | [(k, v)] => renderAcc ((renderStrAcc k acc).push ':') v
    | (k, v) :: m :: ms => renderMembersAcc ((renderAcc ((renderStrAcc k acc).push ':') v).push ',') (m :: ms)
end
def renderFast (j : Json) : String := renderAcc "" j

private theorem str_push_eq (a : String) (c : Char) : a.push c = a ++ String.ofList [c] :=
  String.toList_injective (by simp only [String.toList_push, String.toList_append, String.toList_ofList])
private theorem str_append_ofList (a : String) (xs ys : List Char) : (a ++ String.ofList xs) ++ String.ofList ys = a ++ String.ofList (xs ++ ys) :=
  String.toList_injective (by simp only [String.toList_append, String.toList_ofList, List.append_assoc])
private theorem str_push_ofList (a : String) (c : Char) (xs : List Char) : a.push c ++ String.ofList xs = a ++ String.ofList (c :: xs) :=
  by rw [str_push_eq, str_append_ofList, List.singleton_append]
private theorem str_wrap_ofList (a : String) (l r : Char) (xs : List Char) : ((a.push l) ++ String.ofList xs).push r = a ++ String.ofList (l :: (xs ++ [r])) :=
  by rw [str_push_ofList, str_push_eq, str_append_ofList, List.cons_append]

private theorem foldl_appendEscaped_eq : ∀ (cs : List Char) (acc : String), cs.foldl appendEscaped acc = acc ++ String.ofList (cs.flatMap escapeCharL)
  | [], _ => by simp only [List.foldl_nil, List.flatMap_nil, String.ofList_nil, String.append_empty]
  | c :: cs, acc => by
      have ha : appendEscaped acc c = acc ++ String.ofList (escapeCharL c) := by unfold appendEscaped escapeCharL; split <;> first | rfl | (split <;> first | rfl | exact str_push_eq acc c)
      simp only [List.foldl_cons, List.flatMap_cons, foldl_appendEscaped_eq cs, ha]; exact str_append_ofList ..

private theorem flatMap_escapeCharL_of_none : ∀ cs : List Char, cs.any needsJsonEscape = false → cs.flatMap escapeCharL = cs
  | [], _ => rfl
  | c :: cs, h => by
      simp only [List.any_cons, Bool.or_eq_false_iff, needsJsonEscape, beq_eq_false_iff_ne, decide_eq_false_iff_not] at h
      have he : escapeCharL c = [c] := by unfold escapeCharL; split <;> first | exact absurd rfl h.1.1.1 | exact absurd rfl h.1.1.2 | (exfalso; apply h.1.2; decide) | exact ite_eq_right h.1.2
      simp only [List.flatMap_cons, he, flatMap_escapeCharL_of_none cs h.2, List.singleton_append]

private theorem hasJsonEscapeByte_eq (s : String) : hasAsciiByte s needsJsonEscapeByte = s.toList.any needsJsonEscape :=
  hasAsciiByte_eq_any s needsJsonEscapeByte needsJsonEscape
    (fun b hb => by simp only [needsJsonEscapeByte, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]; refine ⟨⟨?_, ?_⟩, fun h => absurd (UInt8.lt_iff_toNat_lt.1 h) (by change ¬ b.toNat < 32; omega)⟩ <;> (rintro rfl; exact absurd hb (by decide)))
    (fun c hc => by simp only [needsJsonEscapeByte, needsJsonEscape, show (34 : UInt8) = UInt8.ofNat '"'.toNat from rfl, show (92 : UInt8) = UInt8.ofNat '\\'.toNat from rfl,
      asciiByte_beq_char c hc '"' (by decide), asciiByte_beq_char c hc '\\' (by decide), decide_eq_decide.2 (show (UInt8.ofNat c.toNat < 32) ↔ c.toNat < 0x20 by rw [UInt8.lt_iff_toNat_lt]; change c.toNat % 256 < 32 ↔ c.toNat < 32; omega)])
    (fun c hgt => by simp only [needsJsonEscape, Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]; refine ⟨⟨?_, ?_⟩, by omega⟩ <;> (rintro rfl; exact absurd hgt (by decide)))

private theorem renderStrAcc_eq (s acc : String) : renderStrAcc s acc = acc ++ String.ofList (renderStrL s) := by
  unfold renderStrAcc renderStrL; dsimp only
  rw [show s.foldl appendEscaped (acc.push '"') = s.toList.foldl appendEscaped (acc.push '"') by rw [String.foldl_eq_foldl_toList], hasJsonEscapeByte_eq]
  cases ha : s.toList.any needsJsonEscape
  · simp only [Bool.not_false, ↓reduceIte, flatMap_escapeCharL_of_none s.toList ha]; rw [← String.ofList_toList (s := s), str_wrap_ofList, String.toList_ofList]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, foldl_appendEscaped_eq, str_wrap_ofList]

private theorem renderNumAcc_eq (n : JsonNumber) (acc : String) : renderNumAcc n acc = acc ++ String.ofList (renderNumL n) := by
  let rec hfold : ∀ (cs : List Char) (a : String), cs.foldl String.push a = a ++ String.ofList cs
    | [], _ => by simp only [List.foldl_nil, String.ofList_nil, String.append_empty] | c :: cs, a => by simp only [List.foldl_cons, hfold cs]; exact str_push_ofList ..
  have hnat (m : Nat) (a : String) : pushNatAcc m a = a ++ String.ofList (natDigitsAux m []) := by
    unfold pushNatAcc; split
    · rename_i h10; rw [natDigitsAux, ite_eq_left h10, Nat.mod_eq_of_lt h10]; exact str_push_eq ..
    · rename_i hge10; split
      · rename_i h100; have hd : m / 10 < 10 := by omega
        rw [natDigitsAux, ite_eq_right hge10, natDigitsAux, ite_eq_left hd, Nat.mod_eq_of_lt hd, str_push_eq, str_push_ofList]
      · exact hfold _ a
  have hint (i : Int) (a : String) : pushIntAcc i a = a ++ String.ofList (intCharsL i) := by
    unfold pushIntAcc intCharsL; split <;> rw [hnat]
    · exact str_push_ofList ..
    · rfl
  unfold renderNumAcc renderNumL; split <;> simp only [hint]
  · rw [List.append_nil]
  · rw [str_push_ofList, str_append_ofList]

mutual
  private theorem renderAcc_eq (acc : String) : ∀ j, renderAcc acc j = acc ++ String.ofList (renderL j)
    | .null => rfl | .bool b => by cases b <;> rfl | .num n => renderNumAcc_eq n acc | .str s => renderStrAcc_eq s acc
    | .arr es => by unfold renderAcc renderL; rw [renderElemsAcc_eq]; exact str_wrap_ofList ..
    | .obj ms => by unfold renderAcc renderL; rw [renderMembersAcc_eq]; exact str_wrap_ofList ..
  private theorem renderElemsAcc_eq (acc : String) : ∀ es, renderElemsAcc acc es = acc ++ String.ofList (renderElemsL es)
    | [] => by simp only [renderElemsAcc, renderElemsL, String.ofList_nil, String.append_empty] | [e] => renderAcc_eq acc e
    | e :: x :: xs => by unfold renderElemsAcc renderElemsL; rw [renderElemsAcc_eq, renderAcc_eq, str_push_ofList, str_append_ofList]
  private theorem renderMembersAcc_eq (acc : String) : ∀ ms, renderMembersAcc acc ms = acc ++ String.ofList (renderMembersL ms)
    | [] => by simp only [renderMembersAcc, renderMembersL, String.ofList_nil, String.append_empty]
    | [(k, v)] => by unfold renderMembersAcc renderMembersL; rw [renderAcc_eq, renderStrAcc_eq, str_push_ofList, str_append_ofList]
    | (k, v) :: m :: ms => by unfold renderMembersAcc renderMembersL; rw [renderMembersAcc_eq, renderAcc_eq, renderStrAcc_eq, str_push_ofList, str_push_ofList, str_append_ofList, str_append_ofList, List.cons_append]
end
@[csimp] theorem render_eq_renderFast : @Json.render = @Json.renderFast := by
  funext j; symm; unfold render renderFast; rw [renderAcc_eq, String.empty_append]
end Json

instance : Repr Json where reprPrec j _ := Std.Format.text j.render

def Json.bool? : Json → Option Bool                   | .bool b => some b | _ => none
def Json.str?  : Json → Option String                 | .str s  => some s | _ => none
def Json.num?  : Json → Option JsonNumber             | .num n  => some n | _ => none
def Json.arr?  : Json → Option (List Json)            | .arr es => some es | _ => none
def Json.obj?  : Json → Option (List (String × Json)) | .obj ms => some ms | _ => none
def Json.object (entries : Array (String × Json)) : Json := .obj entries.toList
def Json.array  (entries : Array Json) : Json := .arr entries.toList
def Json.field (j : Json) (key : String) : Except String Json :=
  match j with | .obj ms => (ms.foldl (fun acc kv => if kv.1 == key then some kv.2 else acc) none).elim (.error s!"missing key '{key}'") .ok | _ => .error "expected an object"
def Json.get? (j : Json) (key : String) : Option Json := (j.field key).toOption
def Json.strAt? (j : Json) (k : String) : Option String := (j.get? k).bind (·.str?)
def Json.strAtD (j : Json) (k : String) (d : String := "") : String := (j.strAt? k).getD d
def Json.boolAt? (j : Json) (k : String) : Option Bool := (j.get? k).bind (·.bool?)
def Json.natAt? (j : Json) (k : String) : Option Nat := (j.get? k).bind (·.num?) |>.bind fun n => n.toInt?.bind fun i => if 0 ≤ i then some i.toNat else none
def Json.arrAt (j : Json) (k : String) : List Json := ((j.get? k).bind (·.arr?)).getD []
/-- Walks a dot-separated path (object keys and numeric array indices, e.g. `"choices.0.delta.content"`). -/
def Json.atPath (j : Json) (path : String) : Option Json :=
  (Str.splitChar path '.').foldlM (init := j) fun cur seg => match cur with | .arr es => (Str.parseNat? seg).bind (es[·]?) | .obj _ => cur.get? seg | _ => none
def Json.pathStr? (j : Json) (path : String) : Option String := (j.atPath path).bind (·.str?)
def Json.path? (raw : String) (path : String) : Option Json := (Json.parse raw).toOption.bind (·.atPath path)
def Json.pathStr (raw : String) (path : String) (default : String := "") : String := ((Json.path? raw path).bind (·.str?)).getD default

class ToJson (α : Type) where toJson : α → Json
class FromJson (α : Type) where fromJson : Json → Except String α
export ToJson (toJson)
export FromJson (fromJson)

instance : ToJson Unit := ⟨fun _ => .arr []⟩
instance : FromJson Unit := ⟨fun | .arr [] => .ok () | _ => .error "expected []"⟩
instance : ToJson Json := ⟨id⟩
instance : FromJson Json := ⟨.ok⟩
instance : ToJson JsonNumber := ⟨.num⟩
instance : FromJson JsonNumber := ⟨fun j => j.num?.elim (.error "expected a number") .ok⟩
instance : ToJson Bool := ⟨.bool⟩
instance : FromJson Bool := ⟨fun j => j.bool?.elim (.error "expected a boolean") .ok⟩
instance : ToJson String := ⟨.str⟩
instance : FromJson String := ⟨fun j => j.str?.elim (.error "expected a string") .ok⟩
instance : ToJson Int := ⟨fun i => .num ⟨i, 0⟩⟩
instance : FromJson Int := ⟨fun | .num n => n.toInt?.elim (.error "expected an integer") .ok | _ => .error "expected an integer"⟩
instance : ToJson Nat := ⟨fun n => .num ⟨(n : Int), 0⟩⟩
instance : FromJson Nat := ⟨fun | .num n => n.toInt?.elim (.error "expected an integer") fun m => if 0 ≤ m then .ok m.toNat else .error "expected a non-negative integer" | _ => .error "expected a natural number"⟩
instance : ToJson Float := ⟨fun f => (Json.parse (toString f)).toOption.getD (.num ⟨0, 0⟩)⟩
instance : FromJson Float := ⟨fun | .num n => let mag := Float.ofScientific n.mantissa.natAbs (n.exponent < 0) n.exponent.natAbs; .ok (if n.mantissa < 0 then -mag else mag) | _ => .error "expected a number"⟩
section
variable {α β : Type}
instance [ToJson α] : ToJson (List α) := ⟨fun xs => .arr (xs.map toJson)⟩
instance [FromJson α] : FromJson (List α) := ⟨fun | .arr es => es.mapM fromJson | _ => .error "expected an array"⟩
instance [ToJson α] : ToJson (Array α) := ⟨fun xs => .arr (xs.toList.map toJson)⟩
instance [FromJson α] : FromJson (Array α) := ⟨fun j => (fromJson j : Except String (List α)).map List.toArray⟩
instance [ToJson α] : ToJson (Option α) := ⟨fun a => a.elim .null toJson⟩
instance [FromJson α] : FromJson (Option α) := ⟨fun | .null => .ok none | j => (fromJson j : Except String α).map some⟩
instance [ToJson α] [ToJson β] : ToJson (α × β) := ⟨fun (a, b) => .arr [toJson a, toJson b]⟩
instance [FromJson α] [FromJson β] : FromJson (α × β) := ⟨fun | .arr [ja, jb] => (fromJson ja).bind fun a => (fromJson jb).map (a, ·) | _ => .error "expected a 2-element array"⟩
instance [ToJson α] [ToJson β] : ToJson (Sum α β) := ⟨fun | .inl a => .arr [.num ⟨0, 0⟩, toJson a] | .inr b => .arr [.num ⟨1, 0⟩, toJson b]⟩
instance [FromJson α] [FromJson β] : FromJson (Sum α β) := ⟨fun | .arr [.num ⟨0, 0⟩, ja] => (fromJson ja : Except String α).map .inl | .arr [.num ⟨1, 0⟩, jb] => (fromJson jb : Except String β).map .inr | _ => .error "expected a tagged sum array"⟩
end

class FromJsonField (α : Type) where fromField : Json → String → Except String α
export FromJsonField (fromField)
@[inline] abbrev fromFieldVal [FromJson α] (key : String) (v : Json) : Except String α :=
  match (fromJson v : Except String α) with | .ok a => .ok a | .error e => .error s!"{key}: {e}"
instance (priority := low) [FromJson α] : FromJsonField α where fromField j key := (j.field key).bind (fromFieldVal key)
instance [FromJson α] : FromJsonField (Option α) where
  fromField j key := match j.get? key with | none | some .null => .ok none | some v => (fromFieldVal key v).map some

declare_syntax_cat jsonObjField
syntax ident (" := " term)? : jsonObjField

syntax "json_obj_codec% " (&"private ")? ident " [" jsonObjField,* "]" (" validate " term)? : command

macro_rules
  | `(json_obj_codec% $[private%$p?]? $ty:ident [$fs:jsonObjField,*] $[validate $val?:term]?) => do
      let rec go : List (Lean.TSyntax `jsonObjField) → Array (Lean.TSyntax `term) → Array Lean.Ident → Array (Lean.TSyntax `term) →
          Lean.MacroM (Array (Lean.TSyntax `term) × Array Lean.Ident × Array (Lean.TSyntax `term))
        | [], es, ds, vs => pure (es, ds, vs)
        | f :: rest, es, ds, vs => do
            let `(jsonObjField| $id:ident $[:= $d?:term]?) := f | Lean.Macro.throwUnsupported
            let k := Lean.Syntax.mkStrLit id.getId.eraseMacroScopes.toString
            let decVal ← match d? with
              | some d => `((← Qed.fromField (α := Option _) j $k).getD $d)
              | none   => `(← Qed.fromField j $k)
            go rest (es.push (← `(($k, Qed.toJson v.$id)))) (ds.push id) (vs.push decVal)
      let (encItems, decFields, decVals) ← go fs.getElems.toList #[] #[] #[]
      let toBody ← `(fun (v : $ty) => Qed.Json.obj [$[$encItems:term],*])
      let recExpr ← `(({ $[$decFields:ident := $decVals:term],* } : $ty))
      let fromBody ← match val? with
        | some vfn => `(fun j => do let r := $recExpr; let () ← ($vfn:term) r; return r)
        | none     => `(fun j => do return $recExpr)
      let mkInst (cls body : Lean.TSyntax `term) (low : Bool := false) := match p?, low with
        | some _, true  => `(command| private instance (priority := low) : $cls := ⟨$body⟩)
        | some _, false => `(command| private instance : $cls := ⟨$body⟩)
        | none,   true  => `(command| instance (priority := low) : $cls := ⟨$body⟩)
        | none,   false => `(command| instance : $cls := ⟨$body⟩)
      return Lean.mkNullNode #[← mkInst (← `(Qed.ToJson $ty)) toBody, ← mkInst (← `(Qed.FromJson $ty)) fromBody,
        ← mkInst (← `(Repr $ty)) (← `(fun (v : $ty) _ => Std.Format.text (Qed.Json.render (Qed.toJson v)))) (low := true)]

end Qed
