import Qed.Html
import Qed.Router.Basic
import Qed.Json.Lawful

namespace Qed

/-! ## JS-Safe Pure String Helpers (`Qed.Str`)

All functions in `Qed.Str` use structural/fuel recursion on `List Char` with no
`String.Slice` patterns or `Std.Iter` loops, so they pass `qedjs --verify-env`
and work identically in browser JS and native Lean. -/

namespace Str

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def dropWhileWs : List Char → List Char
  | [] => []
  | c :: cs => if isWs c then dropWhileWs cs else c :: cs

def trimLeft (s : String) : String := String.ofList (dropWhileWs s.toList)
def trimRight (s : String) : String := String.ofList (dropWhileWs s.toList.reverse).reverse
def trim (s : String) : String := String.ofList (dropWhileWs (dropWhileWs s.toList).reverse).reverse

def toLower (s : String) : String := String.ofList (s.toList.map Char.toLower)
def toUpper (s : String) : String := String.ofList (s.toList.map Char.toUpper)

def startsWith (s pfx : String) : Bool := listStartsWith s.toList pfx.toList
def endsWith (s sfx : String) : Bool := listStartsWith s.toList.reverse sfx.toList.reverse
def contains (haystack needle : String) : Bool :=
  if needle.isEmpty then true else listContains needle.toList haystack.toList

def containsCI (haystack needle : String) : Bool :=
  contains (toLower haystack) (toLower needle)

def take (s : String) (n : Nat) : String := String.ofList (s.toList.take n)
def drop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

def truncate (s : String) (maxLen : Nat) (ellipsis : String := "...") : String :=
  if s.length ≤ maxLen then s
  else if maxLen ≤ ellipsis.length then take s maxLen
  else take s (maxLen - ellipsis.length) ++ ellipsis

private def splitAux (sep : List Char) (sepLen : Nat) (cur : List Char) (acc : List String) : Nat → List Char → List String
  | 0, xs => (String.ofList (cur.reverse ++ xs) :: acc).reverse
  | _, [] => (String.ofList cur.reverse :: acc).reverse
  | fuel + 1, xs@(c :: cs) =>
      if listStartsWith xs sep then splitAux sep sepLen [] (String.ofList cur.reverse :: acc) fuel (xs.drop sepLen)
      else splitAux sep sepLen (c :: cur) acc fuel cs

def split (s sep : String) : List String :=
  if sep.isEmpty then [s]
  else match sep.toList with
    | [c] => splitChar s c
    | sepCs => splitAux sepCs sepCs.length [] [] (s.length + 1) s.toList

def replace (s old new : String) : String :=
  if old.isEmpty then s else String.intercalate new (split s old)

private theorem dropWhileWs_length_le : ∀ cs : List Char, (dropWhileWs cs).length ≤ cs.length
  | [] => Nat.le_refl 0
  | c :: cs => by unfold dropWhileWs; split; exact Nat.le_trans (dropWhileWs_length_le cs) (Nat.le_succ _); exact Nat.le_refl _

theorem take_length (s : String) (n : Nat) : (take s n).length = min s.length n := by simp only [take, String.length_ofList, List.length_take, String.length_toList]; exact Nat.min_comm _ _
theorem take_length_le (s : String) (n : Nat) : (take s n).length ≤ n := by rw [take_length]; exact Nat.min_le_right _ _
theorem drop_length (s : String) (n : Nat) : (drop s n).length = s.length - n := by simp only [drop, String.length_ofList, List.length_drop, String.length_toList]
theorem trimLeft_length_le (s : String) : (trimLeft s).length ≤ s.length := by simpa only [trimLeft, String.length_ofList, String.length_toList] using dropWhileWs_length_le s.toList
theorem trimRight_length_le (s : String) : (trimRight s).length ≤ s.length := by simpa only [trimRight, String.length_ofList, List.length_reverse, String.length_toList] using dropWhileWs_length_le s.toList.reverse
theorem trim_length_le (s : String) : (trim s).length ≤ s.length := by
  have : (dropWhileWs (dropWhileWs s.toList).reverse).reverse.length ≤ s.toList.length := by
    rw [List.length_reverse]; exact Nat.le_trans (dropWhileWs_length_le _) (by rw [List.length_reverse]; exact dropWhileWs_length_le _)
  simpa only [trim, String.length_ofList, String.length_toList] using this
theorem toLower_length (s : String) : (toLower s).length = s.length := by simp only [toLower, String.length_ofList, List.length_map, String.length_toList]
theorem toUpper_length (s : String) : (toUpper s).length = s.length := by simp only [toUpper, String.length_ofList, List.length_map, String.length_toList]
theorem truncate_length (s : String) (maxLen : Nat) (ellipsis : String := "...") :
    (truncate s maxLen ellipsis).length = min s.length maxLen := by
  unfold truncate; split; · omega
  · split; · exact take_length s maxLen
    · rw [String.length_append, take_length]; omega

-- Prevent `Meta.whnf`/`isDefEq` from unfolding string helper internals during DB `where` / invariant proofs
-- while keeping kernel `decide +kernel` working.
attribute [irreducible] trimLeft trimRight trim toLower toUpper contains containsCI take drop truncate split replace

end Str

private def padZero (w : Nat) (s : String) : String :=
  if s.length < w then String.ofList (List.replicate (w - s.length) '0') ++ s else s
private def padNat (w n : Nat) : String := padZero w (Nat.repr n)
private def pad2 (n : Nat) : String := padNat 2 n
private def fmtYmd (y : Int) (m d : Nat) : String :=
  (if y < 0 then "-" ++ padNat 4 y.natAbs else padNat 4 y.toNat) ++ "-" ++ pad2 m ++ "-" ++ pad2 d

def isLeapYear (y : Int) : Bool := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
def daysInMonth (year : Int) : Nat → Nat | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31 | 4 | 6 | 9 | 11 => 30 | 2 => if isLeapYear year then 29 else 28 | _ => 0

structure Date where
  year : Int
  month : Nat
  day : Nat
  ok : 1 ≤ month ∧ month ≤ 12 ∧ 1 ≤ day ∧ day ≤ daysInMonth year month

namespace Date
def mk? (year : Int) (month day : Nat) : Option Date :=
  if h : 1 ≤ month ∧ month ≤ 12 ∧ 1 ≤ day ∧ day ≤ daysInMonth year month then some ⟨year, month, day, h⟩ else none
def parse? (s : String) : Option Date :=
  match Str.splitChar s '-' with
  | [y, m, d] => do mk? ((← Str.parseNat? y) : Int) (← Str.parseNat? m) (← Str.parseNat? d)
  | ["", y, m, d] => do
      let yn ← Str.parseNat? y
      if yn == 0 then none else mk? (-(Int.ofNat yn)) (← Str.parseNat? m) (← Str.parseNat? d)
  | _ => none
protected def toString (d : Date) : String := fmtYmd d.year d.month d.day
instance : ToString Date := ⟨Date.toString⟩
@[reducible] instance : Coe Date (Html msg) := ⟨fun d => .text (toString d)⟩
def before (a b : Date) : Bool := a.year < b.year || (a.year == b.year && (a.month < b.month || (a.month == b.month && a.day < b.day)))

section RoundTripProof
private theorem parseNatAux_repZero : ∀ k xs, Str.parseNatAux 0 (List.replicate k '0' ++ xs) = Str.parseNatAux 0 xs
  | 0, _ => rfl
  | k + 1, xs => by simp only [List.replicate_succ, List.cons_append, Str.parseNatAux]; exact parseNatAux_repZero k xs

private theorem padNat_noDash (w n : Nat) : '-' ∉ (padNat w n).toList := by
  unfold padNat padZero; have hdig : '-' ∉ (Nat.repr n).toList := Str.nat_toString_not_mem (by decide) n
  split
  · rw [String.toList_append, String.toList_ofList, List.mem_append]
    exact fun h => h.elim (fun hr => by cases List.eq_of_mem_replicate hr) hdig
  · exact hdig

private theorem parseNat?_padNat (w n : Nat) : Str.parseNat? (padNat w n) = some n := by
  have hrep (k : Nat) : Str.parseNat? (String.ofList (List.replicate k '0') ++ Nat.repr n) = some n := by
    unfold Str.parseNat? Nat.repr Nat.toDigits; rw [String.toList_append, String.toList_ofList, String.toList_ofList]
    have hne := Str.toDigitsCore_ne_nil n n []
    cases hEq : List.replicate k '0' ++ Nat.toDigitsCore 10 (n + 1) n [] with
    | nil => exact absurd (List.append_eq_nil_iff.1 hEq).2 hne
    | cons _ _ => dsimp only; rw [← hEq, parseNatAux_repZero, Str.parseNatAux_toDigitsCore n n [] (Nat.le_refl n)]; rfl
  unfold padNat padZero; split
  · exact hrep _
  · exact Str.parseNat?_repr n

private theorem splitChar_sep (s : String) (a : String) (ha : '-' ∉ a.toList) :
    Str.splitChar (a ++ "-" ++ s) '-' = a :: Str.splitChar s '-' := by
  unfold Str.splitChar
  rw [show (a ++ "-" ++ s).toList = a.toList ++ '-' :: s.toList by simp [String.toList_append, List.append_assoc],
      Str.splitCharAux_append_not_mem '-' a.toList s.toList [] [] ha, Str.splitCharAux_acc,
      List.reverse_nil, List.nil_append, String.ofList_toList]
  rfl

private theorem splitChar_single (a : String) (ha : '-' ∉ a.toList) : Str.splitChar a '-' = [a] := by
  unfold Str.splitChar; rw [Str.splitCharAux_not_mem '-' a.toList [] [] ha, List.reverse_nil, List.nil_append, String.ofList_toList]; rfl

private theorem splitChar_ymd (a b c : String) (ha : '-' ∉ a.toList) (hb : '-' ∉ b.toList) (hc : '-' ∉ c.toList) :
    Str.splitChar (a ++ "-" ++ b ++ "-" ++ c) '-' = [a, b, c] := by
  rw [show a ++ "-" ++ b ++ "-" ++ c = a ++ "-" ++ (b ++ "-" ++ c) by simp only [String.append_assoc],
      splitChar_sep _ a ha, splitChar_sep _ b hb, splitChar_single c hc]

theorem parse?_toString (d : Date) : Date.parse? (Date.toString d) = some d := by
  cases d with | mk yr mo dy hok =>
  unfold Date.toString fmtYmd pad2 Date.parse?
  have hmo := padNat_noDash 2 mo; have hdy := padNat_noDash 2 dy
  cases yr with
  | ofNat n =>
      have hnn : ¬(Int.ofNat n < 0) := Int.not_lt.2 (Int.natCast_nonneg n)
      simp only [hnn, ↓reduceIte]
      rw [splitChar_ymd _ _ _ (padNat_noDash 4 (Int.ofNat n).toNat) hmo hdy]
      have htn : (Int.ofNat n).toNat = n := rfl
      simp only [htn, parseNat?_padNat, Bind.bind, Option.bind, Date.mk?]
      exact dite_eq_left hok
  | negSucc k =>
      have hneg : Int.negSucc k < 0 := Int.negSucc_lt_zero k
      simp only [hneg, ↓reduceIte]
      have hpre : "-" ++ padNat 4 (Int.negSucc k).natAbs ++ "-" ++ padNat 2 mo ++ "-" ++ padNat 2 dy =
          "" ++ "-" ++ (padNat 4 (Int.negSucc k).natAbs ++ "-" ++ padNat 2 mo ++ "-" ++ padNat 2 dy) := by
        simp only [String.empty_append, String.append_assoc]
      rw [hpre, splitChar_sep _ "" (by simp), splitChar_ymd _ _ _ (padNat_noDash 4 _) hmo hdy]
      have hna : (Int.negSucc k).natAbs = k + 1 := rfl
      have hnegEq : -(Int.ofNat (k + 1)) = Int.negSucc k := rfl
      simp only [hna, parseNat?_padNat, Bind.bind, Option.bind, Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte, hnegEq, Date.mk?]
      exact dite_eq_left hok
end RoundTripProof
end Date

instance : RouteParam Date := ⟨Date.toString, Date.parse?, Date.parse?_toString⟩
instance : LawfulKey Date := .ofRouteParam

instance : Inhabited Date := ⟨⟨1970, 1, 1, by decide⟩⟩
instance : BEq Date := ⟨fun a b => a.year == b.year && a.month == b.month && a.day == b.day⟩
instance : LawfulBEq Date where
  eq_of_beq {a b} h := by cases a; cases b; simp only [BEq.beq, Bool.and_eq_true, decide_eq_true_eq] at h; rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  rfl := by simp [BEq.beq]
instance : DecidableEq Date := fun a b => decidable_of_iff ((a == b) = true) beq_iff_eq
instance : Repr Date := ⟨fun d _ => repr (Date.toString d)⟩
instance : LT Date := ⟨fun a b => a.before b = true⟩
instance : LE Date := ⟨fun a b => b.before a = false⟩
instance (a b : Date) : Decidable (a < b) := inferInstanceAs (Decidable (a.before b = true))
instance (a b : Date) : Decidable (a ≤ b) := inferInstanceAs (Decidable (b.before a = false))
instance : ToJson Date := ⟨fun d => .str d.toString⟩
instance : FromJson Date := ⟨fun j => j.str?.elim (.error "expected a date string") fun s => (Date.parse? s).elim (.error "expected a date (YYYY-MM-DD)") .ok⟩
instance : LawfulJson Date where
  fromJson_toJson d := by simp [toJson, fromJson, Json.str?, Date.parse?_toString]
instance : NonNullJson Date := ⟨nofun⟩

/-! ## JS-Safe Pure UTC Time Formatting (`Qed.Time`) -/

namespace Time

structure UtcParts where
  year   : Int
  month  : Nat
  day    : Nat
  hour   : Nat
  minute : Nat
  second : Nat
deriving Repr, BEq, DecidableEq

/-- Convert Unix epoch seconds to UTC calendar components (Howard Hinnant's civil-from-days). -/
def fromUnixSec (sec : Nat) : UtcParts :=
  let days : Int := Int.ofNat (sec / 86400)
  let rem := sec % 86400
  let hour := rem / 3600
  let minute := (rem % 3600) / 60
  let second := rem % 60
  let z := days + 719468
  let era := if z ≥ 0 then z / 146097 else (z - 146096) / 146097
  let doe := (z - era * 146097).toNat
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := Int.ofNat yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let yr := if m ≤ 2 then y + 1 else y
  { year := yr, month := m, day := d, hour, minute, second }

def formatDateUtc (sec : Nat) : String :=
  let p := fromUnixSec sec; fmtYmd p.year p.month p.day

def formatIsoUtc (sec : Nat) : String :=
  let p := fromUnixSec sec; s!"{fmtYmd p.year p.month p.day}T{pad2 p.hour}:{pad2 p.minute}:{pad2 p.second}Z"

def formatUtc (sec : Nat) : String :=
  let p := fromUnixSec sec; s!"{fmtYmd p.year p.month p.day} {pad2 p.hour}:{pad2 p.minute} UTC"

def formatDuration (sec : Nat) : String :=
  if sec < 60 then s!"{sec}s"
  else if sec < 3600 then
    let m := sec / 60; let r := sec % 60
    if r == 0 then s!"{m}m" else s!"{m}m {r}s"
  else
    let h := sec / 3600; let m := (sec % 3600) / 60
    if m == 0 then s!"{h}h" else s!"{h}h {m}m"

def formatRelative (nowSec thenSec : Nat) : String :=
  if thenSec ≥ nowSec then "just now"
  else
    let diff := nowSec - thenSec
    if diff < 60 then "just now"
    else if diff < 3600 then s!"{diff / 60}m ago"
    else if diff < 86400 then s!"{diff / 3600}h ago"
    else if diff < 86400 * 30 then s!"{diff / 86400}d ago"
    else formatDateUtc thenSec

end Time

class AbsDiff (α : Type) where
  absDiff : α → α → Nat

@[inline] def absDiff {α : Type} [AbsDiff α] (a b : α) : Nat := AbsDiff.absDiff a b
@[inline] instance : AbsDiff Nat := ⟨fun a b => if a ≥ b then a - b else b - a⟩
@[inline] instance : AbsDiff Int := ⟨fun a b => (a - b).natAbs⟩
@[simp] theorem absDiff_nat (a b : Nat) : absDiff a b = if a ≥ b then a - b else b - a := rfl
@[simp] theorem absDiff_int (a b : Int) : absDiff a b = (a - b).natAbs := rfl

end Qed
