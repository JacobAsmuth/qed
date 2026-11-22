import Std.Data.String.ToNat
import Std.Data.String.ToInt
import Qed.Html

namespace Qed

class RouteParam (α : Type) where
  toSeg      : α → String
  fromSeg    : String → Option α
  round_trip : ∀ a, fromSeg (toSeg a) = some a

attribute [simp] RouteParam.round_trip

instance : RouteParam String := ⟨id, some, fun _ => rfl⟩
instance : RouteParam Nat    := ⟨Nat.repr, String.toNat?, Nat.toNat?_repr⟩
instance : RouteParam Int    := ⟨Int.repr, String.toInt?, Int.toInt?_repr⟩

@[simp] theorem RouteParam.toSeg_string (s : String) : RouteParam.toSeg s = s := rfl

class Router (α : Type) where
  print      : α → List String
  parse      : List String → Option α
  round_trip : ∀ a, parse (print a) = some a

class LawfulKey (α : Type) where
  toKey     : α → String
  injective : ∀ a₁ a₂ : α, toKey a₁ = toKey a₂ → a₁ = a₂

@[reducible] def LawfulKey.ofRouteParam {α : Type} [RouteParam α] : LawfulKey α where
  toKey := RouteParam.toSeg
  injective a₁ a₂ h := Option.some.inj (by rw [← RouteParam.round_trip a₁, h, RouteParam.round_trip])

instance : LawfulKey String := .ofRouteParam
instance : LawfulKey Nat    := .ofRouteParam
instance : LawfulKey Int    := .ofRouteParam

instance : LawfulKey Bool where
  toKey | true => "1" | false => "0"
  injective a₁ a₂ h := by cases a₁ <;> cases a₂ <;> simp_all

def hexDigit (n : UInt8) : Char :=
  match n.toNat % 16 with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9'
  | 10 => 'A' | 11 => 'B' | 12 => 'C' | 13 => 'D' | 14 => 'E'
  | _ => 'F'

def isUnreserved (b : UInt8) : Bool :=
  let c := b.toNat
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
    || c == 45 || c == 95 || c == 46 || c == 126

@[inline] def isPctEncodedChar (c : Char) : Bool :=
  let n := c.toNat
  (48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) ||
    n == 45 || n == 95 || n == 46 || n == 126 || n == 37

@[inline] def isSafePathBodyChar (c : Char) : Bool :=
  isSafeUrlChar c && c.toNat != 92

theorem isPctEncodedChar_hexDigit (n : UInt8) :
    isPctEncodedChar (hexDigit n) = true := by
  unfold hexDigit; split <;> rfl

theorem isPctEncodedChar_unreserved {b : UInt8} (h : isUnreserved b = true) :
    isPctEncodedChar (Char.ofNat b.toNat) = true := by
  unfold isUnreserved at h
  have hb : b.toNat ≤ 126 ∧ b.toNat ≥ 45 := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h; omega
  have hv : b.toNat.isValidChar := by simp [Nat.isValidChar]; omega
  have htn : (Char.ofNat b.toNat).toNat = b.toNat := by simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]
  unfold isPctEncodedChar; rw [htn]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h ⊢; omega

def encodeUTF8Loop (bs : ByteArray) (i : Nat) (acc : String) : String :=
  if h : i < bs.size then
    let b := bs[i]
    let next := if isUnreserved b then acc.push (Char.ofNat b.toNat)
                else ((acc.push '%').push (hexDigit (b >>> 4))).push (hexDigit (b &&& 0x0F))
    encodeUTF8Loop bs (i + 1) next
  else acc
termination_by bs.size - i

theorem encodeUTF8Loop_pct (bs : ByteArray) :
    ∀ (i : Nat) (acc : String),
      acc.toList.all isPctEncodedChar = true →
      (encodeUTF8Loop bs i acc).toList.all isPctEncodedChar = true := by
  intro i
  induction hfuel : bs.size - i generalizing i with
  | zero =>
      intro acc hacc; unfold encodeUTF8Loop
      have hnot : ¬ i < bs.size := by omega
      simp [hnot, hacc]
  | succ _ ih =>
      intro acc hacc; unfold encodeUTF8Loop
      have hlt : i < bs.size := by omega
      simp only [hlt, ↓reduceDIte]
      apply ih (i + 1) (by omega)
      by_cases hu : isUnreserved bs[i]
      · simp [hu, String.toList_push, hacc, isPctEncodedChar_unreserved hu]
      · have hpct : isPctEncodedChar '%' = true := rfl
        simp [hu, String.toList_push, hacc, hpct, isPctEncodedChar_hexDigit]

def encodeSeg (s : String) : String :=
  encodeUTF8Loop s.toUTF8 0 ""

theorem encodeSeg_pct (s : String) :
    (encodeSeg s).toList.all isPctEncodedChar = true :=
  encodeUTF8Loop_pct s.toUTF8 0 "" rfl

theorem encodeSeg_safe (s : String) :
    (encodeSeg s).toList.all isSafePathBodyChar = true := by
  have h := encodeSeg_pct s
  rw [List.all_eq_true] at h ⊢
  intro c hc; specialize h c hc
  unfold isPctEncodedChar at h; unfold isSafePathBodyChar isSafeUrlChar
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at h ⊢
  omega

def unhex (c : Char) : Option UInt8 :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (UInt8.ofNat (n - 48))
  else if 65 ≤ n && n ≤ 70 then some (UInt8.ofNat (n - 55))
  else if 97 ≤ n && n ≤ 102 then some (UInt8.ofNat (n - 87))
  else none

def decodeBytes : List Char → ByteArray → ByteArray
  | '%' :: h :: l :: rest, acc =>
      match unhex h, unhex l with
      | some hi, some lo => decodeBytes rest (acc.push ((hi <<< 4) ||| lo))
      | _,       _       => decodeBytes (h :: l :: rest) (acc.push 37)
  | c :: rest, acc => decodeBytes rest (acc ++ c.toString.toUTF8)
  | [], acc => acc

def decodeSeg (s : String) : String :=
  (String.fromUTF8? (decodeBytes s.toList .empty)).getD s

def joinSlash : List String → String
  | []      => ""
  | [s]     => s
  | s :: ss => s ++ "/" ++ joinSlash ss

private theorem joinSlash_safe :
    ∀ (segs : List String),
      (∀ s ∈ segs, s.toList.all isSafePathBodyChar = true) →
      (joinSlash segs).toList.all isSafePathBodyChar = true
  | [], _ => rfl
  | [s], hs => hs s (by simp)
  | s₁ :: s₂ :: rest, hs => by
      have hslash : isSafePathBodyChar '/' = true := rfl
      have ih := joinSlash_safe (s₂ :: rest) (fun x hx => hs x (by simp [hx]))
      simp [joinSlash, String.toList_append, hs s₁ (by simp), hslash, ih]

private theorem dropWhile_slash_safe :
    ∀ (cs : List Char),
      cs.all isSafePathBodyChar = true →
      hasSafeUrlPrefix ('/' :: cs.dropWhile (· == '/')) = true ∧
      ('/' :: cs.dropWhile (· == '/')).all isSafeUrlChar = true
  | [], _ => ⟨rfl, rfl⟩
  | c :: rest, hcs => by
      simp only [List.all_cons, Bool.and_eq_true] at hcs
      by_cases hslash : (c == '/') = true
      · simpa [List.dropWhile, hslash] using dropWhile_slash_safe rest hcs.2
      · have hcf : (c == '/') = false := Bool.eq_false_iff.2 hslash
        rcases Bool.and_eq_true_iff.1 hcs.1 with ⟨hcUrl, hcNot92⟩
        have hnotBs : (c != '\\') = true := bne_iff_ne.2 fun h => by subst h; simp at hcNot92
        have hnotSlash : (c != '/') = true := bne_iff_ne.2 fun h => by subst h; simp at hcf
        have hrestUrl : rest.all isSafeUrlChar = true :=
          List.all_eq_true.2 fun x hx => (Bool.and_eq_true_iff.1 (List.all_eq_true.1 hcs.2 x hx)).1
        exact ⟨by simp [List.dropWhile, hcf, hasSafeUrlPrefix, hnotSlash, hnotBs],
               by simp [List.dropWhile, hcf, show isSafeUrlChar '/' = true from rfl, hcUrl, hrestUrl]⟩

def Router.toURL {α} [Router α] (a : α) : String :=
  String.ofList ('/' :: (joinSlash ((Router.print a).map encodeSeg)).toList.dropWhile (· == '/'))

@[simp] theorem Router.isSafeUrl_toURL {α : Type} [Router α] (a : α) :
    isSafeUrl (Router.toURL a) = true := by
  unfold Router.toURL isSafeUrl
  rw [String.toList_ofList]
  have hbody : (joinSlash ((Router.print a).map encodeSeg)).toList.all isSafePathBodyChar = true := by
    apply joinSlash_safe
    intro s hs
    rcases List.mem_map.1 hs with ⟨raw, _, rfl⟩
    exact encodeSeg_safe raw
  have ⟨hpfx, hall⟩ := dropWhile_slash_safe _ hbody
  exact Bool.and_eq_true_iff.2 ⟨hpfx, hall⟩

def Router.toUrl {α : Type} [Router α] (a : α) : Url :=
  ⟨Router.toURL a, Router.isSafeUrl_toURL a⟩

def stripQueryAndHash (path : String) : String :=
  String.ofList (path.toList.takeWhile fun c => c != '#' && c != '?')

def splitSlashChars : List Char → List Char → List String
  | [],      acc => [String.ofList acc.reverse]
  | c :: cs, acc =>
      if c == '/' then String.ofList acc.reverse :: splitSlashChars cs []
      else splitSlashChars cs (c :: acc)

def splitSlash (s : String) : List String :=
  splitSlashChars s.toList []

def Router.fromURL {α} [Router α] (path : String) : Option α :=
  Router.parse (((splitSlash (stripQueryAndHash path)).filter (· ≠ "")).map decodeSeg)

class ToHref (α : Type) where
  toUrl : α → Url

def ToHref.toHref {α : Type} [ToHref α] (v : α) : String := (ToHref.toUrl v).raw

instance : ToHref Url := ⟨id⟩
instance [Router R] : ToHref R := ⟨Router.toUrl⟩

@[simp] theorem ToHref.toUrl_url (u : Url) : ToHref.toUrl u = u := rfl
@[simp] theorem ToHref.toHref_url (u : Url) : ToHref.toHref u = u.raw := rfl
@[simp] theorem ToHref.toHref_route {R : Type} [Router R] (r : R) :
    ToHref.toHref r = Router.toURL r := rfl
@[simp] theorem ToHref.isSafeUrl_toHref {α : Type} [ToHref α] (v : α) :
    isSafeUrl (ToHref.toHref v) = true := (ToHref.toUrl v).safe


end Qed
