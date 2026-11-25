import Std.Data.String.ToNat
import Std.Data.String.ToInt
import Qed.Html

namespace Qed

class RouteParam (α : Type) where
  toSeg : α → String
  fromSeg : String → Option α
  round_trip : ∀ a, fromSeg (toSeg a) = some a
attribute [simp] RouteParam.round_trip
instance : RouteParam String := ⟨id, some, fun _ => rfl⟩
instance : RouteParam Nat    := ⟨Nat.repr, String.toNat?, Nat.toNat?_repr⟩
instance : RouteParam Int    := ⟨Int.repr, String.toInt?, Int.toInt?_repr⟩
@[simp] theorem RouteParam.toSeg_string (s : String) : RouteParam.toSeg s = s := rfl
@[simp] theorem RouteParam.fromSeg_string (s : String) : (RouteParam.fromSeg s : Option String) = some s := rfl

class Router (α : Type) where
  print : α → List String
  parse : List String → Option α
  round_trip : ∀ a, parse (print a) = some a
class LawfulKey (α : Type) where
  toKey : α → String
  injective : ∀ a₁ a₂ : α, toKey a₁ = toKey a₂ → a₁ = a₂
@[reducible] def LawfulKey.ofRouteParam {α : Type} [RouteParam α] : LawfulKey α :=
  ⟨RouteParam.toSeg, fun a₁ a₂ h => Option.some.inj (by rw [← RouteParam.round_trip a₁, h, RouteParam.round_trip])⟩
instance : LawfulKey String := .ofRouteParam
instance : LawfulKey Nat    := .ofRouteParam
instance : LawfulKey Int    := .ofRouteParam
instance : LawfulKey Bool   := ⟨fun | true => "1" | false => "0", fun a₁ a₂ h => by cases a₁ <;> cases a₂ <;> simp_all⟩

abbrev hexDigit (n : UInt8) : Char := hexDigitUpper n.toNat
@[inline] abbrev isUnreservedNat (n : Nat) : Bool :=
  (48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || n == 45 || n == 95 || n == 46 || n == 126
@[inline] def isUnreserved (b : UInt8) : Bool := isUnreservedNat b.toNat
@[inline] def isPctEncodedChar (c : Char) : Bool := isUnreservedNat c.toNat || c.toNat == 37
@[inline] def isSafePathBodyChar (c : Char) : Bool := isSafeUrlChar c && c.toNat != 92
private theorem isPctEncodedChar_hexDigitUpper_fin : ∀ d : Fin 16, isPctEncodedChar (hexDigitUpper d.val) = true := by decide
theorem isPctEncodedChar_hexDigit (n : UInt8) : isPctEncodedChar (hexDigit n) = true := by
  simpa [hexDigit, hexDigitUpper] using isPctEncodedChar_hexDigitUpper_fin ⟨n.toNat % 16, Nat.mod_lt _ (by omega)⟩
theorem unreserved_toNat {b : UInt8} (h : isUnreserved b = true) :
    b.toNat ≤ 126 ∧ b.toNat ≠ 37 ∧ (Char.ofNat b.toNat).toNat = b.toNat := by
  have hb : b.toNat ≤ 126 ∧ b.toNat ≠ 37 := by
    simp only [isUnreserved, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h; omega
  exact ⟨hb.1, hb.2, by simp [Char.ofNat, Nat.isValidChar, show b.toNat < 0xd800 by omega, Char.ofNatAux, Char.toNat]⟩
theorem isPctEncodedChar_unreserved {b : UInt8} (h : isUnreserved b = true) : isPctEncodedChar (Char.ofNat b.toNat) = true := by
  simp only [isPctEncodedChar, (unreserved_toNat h).2.2, show isUnreservedNat b.toNat = true from h, Bool.true_or]

def encodeUTF8Loop (bs : ByteArray) (i : Nat) (acc : String) : String :=
  if h : i < bs.size then
    let b := bs[i]
    encodeUTF8Loop bs (i + 1) <| if isUnreserved b then acc.push (Char.ofNat b.toNat)
      else ((acc.push '%').push (hexDigit (b >>> 4))).push (hexDigit (b &&& 0x0F))
  else acc
termination_by bs.size - i
decreasing_by exact Nat.sub_succ_lt_self bs.size i h
theorem encodeUTF8Loop_pct (bs : ByteArray) (i : Nat) (acc : String) (hacc : acc.toList.all isPctEncodedChar = true) :
    (encodeUTF8Loop bs i acc).toList.all isPctEncodedChar = true := by
  fun_induction encodeUTF8Loop bs i acc with
  | case2 => exact hacc
  | case1 i acc _ b ih =>
      apply ih; by_cases hu : isUnreserved b <;>
        simp [hu, String.toList_push, hacc, isPctEncodedChar_unreserved, show isPctEncodedChar '%' = true from rfl, isPctEncodedChar_hexDigit]
def encodeSeg (s : String) : String := encodeUTF8Loop s.toUTF8 0 ""
theorem encodeSeg_pct (s : String) : (encodeSeg s).toList.all isPctEncodedChar = true := encodeUTF8Loop_pct s.toUTF8 0 "" rfl
theorem encodeSeg_safe (s : String) : (encodeSeg s).toList.all isSafePathBodyChar = true :=
  List.all_eq_true.2 fun c hc => by
    have h := List.all_eq_true.1 (encodeSeg_pct s) c hc
    simp only [isPctEncodedChar, isSafePathBodyChar, isSafeUrlChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at h ⊢; omega
@[inline] def unhex (c : Char) : Option UInt8 := (unhexNat? c).map UInt8.ofNat
def decodeBytes : List Char → ByteArray → ByteArray
  | '%' :: h :: l :: rest, acc => match unhex h, unhex l with
      | some hi, some lo => decodeBytes rest (acc.push ((hi <<< 4) ||| lo))
      | _, _             => decodeBytes (h :: l :: rest) (acc.push 37)
  | c :: rest, acc => decodeBytes rest (acc ++ c.toString.toUTF8)
  | [], acc => acc
def decodeSeg (s : String) : String := (String.fromUTF8? (decodeBytes s.toList .empty)).getD s

def urlDecodeComponent (s : String) : String :=
  (String.fromUTF8? (decodeBytes (s.toList.map fun c => if c == '+' then ' ' else c) .empty)).getD s

private def splitAmp : List Char → List Char → List String
  | [], acc => [String.ofList acc.reverse]
  | c :: cs, acc => if c == '&' then String.ofList acc.reverse :: splitAmp cs [] else splitAmp cs (c :: acc)

private def splitFirstEq : List Char → List Char → String × String
  | [], acc => (String.ofList acc.reverse, "")
  | c :: cs, acc => if c == '=' then (String.ofList acc.reverse, String.ofList cs) else splitFirstEq cs (c :: acc)

def parseQueryParams (q : String) : List (String × String) :=
  let cs := match q.toList with | '?' :: rest => rest | rest => rest
  if cs.isEmpty then [] else (splitAmp cs []).filterMap fun pair =>
    if pair.isEmpty then none
    else let (k, v) := splitFirstEq pair.toList []; some (urlDecodeComponent k, urlDecodeComponent v)

def joinSlash : List String → String
  | [] => "" | [s] => s | s :: ss => s ++ "/" ++ joinSlash ss
theorem joinSlash_all (p : Char → Bool) (hslash : p '/' = true) :
    ∀ (segs : List String), (∀ s ∈ segs, s.toList.all p = true) → (joinSlash segs).toList.all p = true
  | [], _ => rfl
  | [s], hs => hs s (.head _)
  | s₁ :: s₂ :: rest, hs => by
      simp only [joinSlash, String.toList_append, List.all_append, hs s₁ (.head _),
        show "/".toList = ['/'] from rfl, List.all_cons, List.all_nil, hslash, Bool.and_true,
        joinSlash_all p hslash (s₂ :: rest) fun x hx => hs x (.tail _ hx)]
private theorem dropWhile_slash_safe : ∀ (cs : List Char), cs.all isSafePathBodyChar = true →
    hasSafeUrlPrefix ('/' :: cs.dropWhile (· == '/')) = true ∧ ('/' :: cs.dropWhile (· == '/')).all isSafeUrlChar = true
  | [], _ => ⟨rfl, rfl⟩
  | c :: rest, hcs => by
      simp only [List.all_cons, Bool.and_eq_true] at hcs
      cases hslash : (c == '/') with
      | true => simpa only [List.dropWhile, hslash, ↓reduceIte] using dropWhile_slash_safe rest hcs.2
      | false =>
          rcases Bool.and_eq_true_iff.1 hcs.1 with ⟨hcUrl, hcNot92⟩; simp only [List.dropWhile, hslash]
          refine ⟨?_, by simp only [List.all_cons, Bool.and_eq_true, show isSafeUrlChar '/' = true from rfl, hcUrl, true_and,
            List.all_eq_true.2 fun x hx => (Bool.and_eq_true_iff.1 (List.all_eq_true.1 hcs.2 x hx)).1]⟩
          change (c != '/' && c != '\\') = true
          simp only [Bool.and_eq_true, bne, hslash, Bool.not_false, true_and, Bool.not_eq_true', beq_eq_false_iff_ne]
          exact fun h => by subst h; cases hcNot92
def Router.toURL {α} [Router α] (a : α) : String :=
  String.ofList ('/' :: (joinSlash ((Router.print a).map encodeSeg)).toList.dropWhile (· == '/'))
@[simp] theorem Router.isSafeUrl_toURL {α : Type} [Router α] (a : α) : isSafeUrl (Router.toURL a) = true := by
  unfold Router.toURL isSafeUrl; rw [String.toList_ofList]
  exact Bool.and_eq_true_iff.2 <| dropWhile_slash_safe _ <| joinSlash_all isSafePathBodyChar rfl _ fun s hs => by
    rcases List.mem_map.1 hs with ⟨raw, _, rfl⟩; exact encodeSeg_safe raw
def Router.toUrl {α : Type} [Router α] (a : α) : Url := ⟨Router.toURL a, Router.isSafeUrl_toURL a⟩
def stripQueryAndHash (path : String) : String := String.ofList (path.toList.takeWhile fun c => c != '#' && c != '?')
def splitSlashChars : List Char → List Char → List String
  | [], acc => [String.ofList acc.reverse]
  | c :: cs, acc => if c == '/' then String.ofList acc.reverse :: splitSlashChars cs [] else splitSlashChars cs (c :: acc)
def splitSlash (s : String) : List String := splitSlashChars s.toList []
def Router.fromURL {α} [Router α] (path : String) : Option α :=
  Router.parse (((splitSlash (stripQueryAndHash path)).filter (· ≠ "")).map decodeSeg)

class ToHref (α : Type) where toUrl : α → Url
def ToHref.toHref {α : Type} [ToHref α] (v : α) : String := (ToHref.toUrl v).raw
instance : ToHref Url := ⟨id⟩
instance [Router R] : ToHref R := ⟨Router.toUrl⟩
@[simp] theorem ToHref.toUrl_url (u : Url) : ToHref.toUrl u = u := rfl
@[simp] theorem ToHref.toHref_url (u : Url) : ToHref.toHref u = u.raw := rfl
@[simp] theorem ToHref.toHref_route {R : Type} [Router R] (r : R) : ToHref.toHref r = Router.toURL r := rfl
@[simp] theorem ToHref.isSafeUrl_toHref {α : Type} [ToHref α] (v : α) : isSafeUrl (ToHref.toHref v) = true := (ToHref.toUrl v).safe

/-- URL or path destination accepted by redirects, `head: canonical`, and auth `returnTo` helpers.
    Accepts `String`, `Qed.Url`, or any typed `router` value via `ToHref`. -/
structure HrefTarget where
  raw : String
deriving Inhabited, DecidableEq, Repr

namespace HrefTarget
def root : HrefTarget := ⟨"/"⟩
instance : Coe String HrefTarget := ⟨HrefTarget.mk⟩
instance {α : Type} [ToHref α] : CoeTC α HrefTarget := ⟨fun a => ⟨ToHref.toHref a⟩⟩
end HrefTarget
end Qed
