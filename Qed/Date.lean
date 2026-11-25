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

private def listStartsWith : List Char → List Char → Bool
  | _, [] => true
  | [], _ :: _ => false
  | a :: as, b :: bs => a == b && listStartsWith as bs

def startsWith (s pfx : String) : Bool := listStartsWith s.toList pfx.toList
def endsWith (s sfx : String) : Bool := listStartsWith s.toList.reverse sfx.toList.reverse

private def listContains (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | xs@(_ :: tl) => listStartsWith xs needle || listContains needle tl

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

private def splitCharAux (sep : Char) (cur : List Char) (acc : List String) : List Char → List String
  | [] => (String.ofList cur.reverse :: acc).reverse
  | c :: cs =>
      if c == sep then splitCharAux sep [] (String.ofList cur.reverse :: acc) cs
      else splitCharAux sep (c :: cur) acc cs

def splitChar (s : String) (sep : Char) : List String :=
  splitCharAux sep [] [] s.toList

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

private def parseNatAux (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: cs =>
      if '0' ≤ c && c ≤ '9' then parseNatAux (acc * 10 + (c.toNat - 48)) cs else none

def parseNat? (s : String) : Option Nat :=
  match s.toList with | [] => none | cs => parseNatAux 0 cs

def parseInt? (s : String) : Option Int :=
  match s.toList with
  | [] => none
  | '-' :: [] => none
  | '-' :: cs => (parseNatAux 0 cs).map fun n => -(Int.ofNat n)
  | cs => (parseNatAux 0 cs).map Int.ofNat

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
private theorem digitChar_ok (d : Fin 10) :
    ('0' ≤ Nat.digitChar d.val ∧ Nat.digitChar d.val ≤ '9') ∧ (Nat.digitChar d.val).toNat - 48 = d.val ∧ Nat.digitChar d.val ≠ '-' := by
  revert d; decide

private theorem toDigitsCore_ne_nil : ∀ fuel n ds, Nat.toDigitsCore 10 (fuel + 1) n ds ≠ []
  | 0, n, ds => by rw [Nat.toDigitsCore]; by_cases hq : n / 10 = 0 <;> simp [hq, Nat.toDigitsCore]
  | fuel + 1, n, ds => by
      rw [Nat.toDigitsCore]; by_cases hq : n / 10 = 0
      · simp [hq]
      · simpa [hq] using toDigitsCore_ne_nil fuel (n / 10) ((n % 10).digitChar :: ds)

private theorem toDigitsCore_noDash : ∀ fuel n ds, '-' ∉ ds → '-' ∉ Nat.toDigitsCore 10 fuel n ds
  | 0, _, ds, h => h
  | fuel + 1, n, ds, h => by
      rw [Nat.toDigitsCore]
      have hd : Nat.digitChar (n % 10) ≠ '-' := (digitChar_ok ⟨n % 10, Nat.mod_lt _ (by omega)⟩).2.2
      have hcons : '-' ∉ Nat.digitChar (n % 10) :: ds := by simp [hd.symm, h]
      by_cases hq : n / 10 = 0
      · simpa [hq] using hcons
      · simpa [hq] using toDigitsCore_noDash fuel (n / 10) _ hcons

private theorem parseNatAux_digit (acc d : Nat) (hd : d < 10) (ds : List Char) :
    Str.parseNatAux acc (Nat.digitChar d :: ds) = Str.parseNatAux (acc * 10 + d) ds := by
  have ⟨⟨h1, h2⟩, hval, _⟩ := digitChar_ok ⟨d, hd⟩
  simp [Str.parseNatAux, h1, h2, hval]

private theorem parseNatAux_toDigitsCore : ∀ fuel n ds, n ≤ fuel →
    Str.parseNatAux 0 (Nat.toDigitsCore 10 (fuel + 1) n ds) = Str.parseNatAux n ds
  | 0, n, ds, hn => by
      have hn0 : n = 0 := by omega
      subst hn0; simp [Nat.toDigitsCore, Str.parseNatAux]; rfl
  | fuel + 1, n, ds, hn => by
      rw [Nat.toDigitsCore]
      by_cases hq : n / 10 = 0
      · simp only [hq, ↓reduceIte]
        have hlt : n < 10 := by omega
        rw [parseNatAux_digit 0 (n % 10) (Nat.mod_lt _ (by omega)) ds]
        simp [Nat.mod_eq_of_lt hlt]
      · simp only [hq, ↓reduceIte]
        have hsub : n / 10 ≤ fuel := by omega
        rw [parseNatAux_toDigitsCore fuel (n / 10) _ hsub, parseNatAux_digit (n / 10) (n % 10) (Nat.mod_lt _ (by omega)) ds,
            Nat.mul_comm (n / 10) 10, Nat.div_add_mod]

private theorem parseNatAux_repZero : ∀ k xs, Str.parseNatAux 0 (List.replicate k '0' ++ xs) = Str.parseNatAux 0 xs
  | 0, _ => rfl
  | k + 1, xs => by
      simp only [List.replicate_succ, List.cons_append, Str.parseNatAux]
      exact parseNatAux_repZero k xs

private theorem padNat_noDash (w n : Nat) : '-' ∉ (padNat w n).toList := by
  unfold padNat padZero Nat.repr Nat.toDigits
  have hdig := toDigitsCore_noDash (n + 1) n [] (by simp)
  split
  · rw [String.toList_append, String.toList_ofList, String.toList_ofList, List.mem_append]
    rintro (h | h)
    · have := List.eq_of_mem_replicate h; cases this
    · exact hdig h
  · rw [String.toList_ofList]; exact hdig

private theorem parseNat?_padNat (w n : Nat) : Str.parseNat? (padNat w n) = some n := by
  unfold padNat padZero Nat.repr Nat.toDigits
  have hne := toDigitsCore_ne_nil n n []
  have hcore := parseNatAux_toDigitsCore n n [] (Nat.le_refl n)
  split
  · unfold Str.parseNat?; rw [String.toList_append, String.toList_ofList, String.toList_ofList]
    cases hEq : List.replicate (w - (String.ofList (Nat.toDigitsCore 10 (n + 1) n [])).length) '0' ++ Nat.toDigitsCore 10 (n + 1) n [] with
    | nil => exact absurd (List.append_eq_nil_iff.1 hEq).2 hne
    | cons c cs => dsimp only; rw [← hEq, parseNatAux_repZero, hcore]; rfl
  · unfold Str.parseNat?; rw [String.toList_ofList]
    cases hEq : Nat.toDigitsCore 10 (n + 1) n [] with
    | nil => exact absurd hEq hne
    | cons c cs => dsimp only; rw [← hEq, hcore]; rfl

private theorem splitCharAux_append_noDash : ∀ xs ys cur acc, '-' ∉ xs →
    Str.splitCharAux '-' cur acc (xs ++ '-' :: ys) = Str.splitCharAux '-' [] (String.ofList (cur.reverse ++ xs) :: acc) ys
  | [], ys, cur, acc, _ => by simp [Str.splitCharAux]
  | c :: xs, ys, cur, acc, hnd => by
      have hc : (c == '-') = false := beq_false_of_ne fun h => hnd (h ▸ .head _)
      have hxs : '-' ∉ xs := fun hm => hnd (.tail _ hm)
      simp only [List.cons_append, Str.splitCharAux, hc, Bool.false_eq_true, ↓reduceIte]
      rw [splitCharAux_append_noDash xs ys (c :: cur) acc hxs, List.reverse_cons, List.append_assoc, List.singleton_append]

private theorem splitCharAux_noDash : ∀ xs cur acc, '-' ∉ xs →
    Str.splitCharAux '-' cur acc xs = (String.ofList (cur.reverse ++ xs) :: acc).reverse
  | [], cur, acc, _ => by simp [Str.splitCharAux]
  | c :: xs, cur, acc, hnd => by
      have hc : (c == '-') = false := beq_false_of_ne fun h => hnd (h ▸ .head _)
      have hxs : '-' ∉ xs := fun hm => hnd (.tail _ hm)
      simp only [Str.splitCharAux, hc, Bool.false_eq_true, ↓reduceIte]
      rw [splitCharAux_noDash xs (c :: cur) acc hxs]
      simp [List.reverse_cons, List.append_assoc]

private theorem splitChar_ymd (a b c : String) (ha : '-' ∉ a.toList) (hb : '-' ∉ b.toList) (hc : '-' ∉ c.toList) :
    Str.splitChar (a ++ "-" ++ b ++ "-" ++ c) '-' = [a, b, c] := by
  unfold Str.splitChar
  have hlist : (a ++ "-" ++ b ++ "-" ++ c).toList = a.toList ++ '-' :: (b.toList ++ '-' :: c.toList) := by
    simp [String.toList_append, List.append_assoc]
  rw [hlist, splitCharAux_append_noDash a.toList _ [] [] ha,
      splitCharAux_append_noDash b.toList _ [] _ hb,
      splitCharAux_noDash c.toList [] _ hc]
  simp [String.ofList_toList]

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
      have hyr := padNat_noDash 4 (Int.negSucc k).natAbs
      have hsplit : Str.splitChar ("-" ++ padNat 4 (Int.negSucc k).natAbs ++ "-" ++ padNat 2 mo ++ "-" ++ padNat 2 dy) '-' =
          ["", padNat 4 (Int.negSucc k).natAbs, padNat 2 mo, padNat 2 dy] := by
        unfold Str.splitChar
        have hlist : ("-" ++ padNat 4 (Int.negSucc k).natAbs ++ "-" ++ padNat 2 mo ++ "-" ++ padNat 2 dy).toList =
            '-' :: ((padNat 4 (Int.negSucc k).natAbs).toList ++ '-' :: ((padNat 2 mo).toList ++ '-' :: (padNat 2 dy).toList)) := by
          simp [String.toList_append, List.append_assoc]
        rw [hlist]; simp only [Str.splitCharAux, beq_self_eq_true, ↓reduceIte]
        rw [splitCharAux_append_noDash _ _ [] _ hyr, splitCharAux_append_noDash _ _ [] _ hmo, splitCharAux_noDash _ [] _ hdy]
        simp [String.ofList_toList]
      rw [hsplit]
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
instance : DecidableEq Date := fun a b => if h : a == b then isTrue (eq_of_beq h) else isFalse fun heq => h (heq ▸ beq_self_eq_true a)
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

end Qed
