/-
  Qed.Date — a calendar date that cannot be invalid.

  `Date` carries a proof that its `month`/`day` are in range for its `year`
  (`2026-02-30` and `2026-13-01` have no `Date` value). The only ways to build one
  are the smart constructor `Date.mk?` and the ISO parser `Date.parse?`, both of
  which return `none` on an impossible date — so a `Date` in hand is evidence of a
  real calendar day, the same guarantee `Field` gives a validated string.

  Core-syntax only (no `import Lean`), so apps that use it don't pull the Lean
  elaborator into their transpiled JS bundle.
-/
import Qed.Json   -- for the Date ⟷ JSON codec below (Json imports nothing, so no cycle)

namespace Qed

/-- Gregorian leap year: divisible by 4, except centuries not divisible by 400. -/
def isLeapYear (y : Int) : Bool :=
  (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

/-- Days in `month` (1–12) of `year`; `0` for an out-of-range month. -/
def daysInMonth (year : Int) (month : Nat) : Nat :=
  match month with
  | 1  => 31 | 2  => if isLeapYear year then 29 else 28
  | 3  => 31 | 4  => 30 | 5  => 31 | 6  => 30
  | 7  => 31 | 8  => 31 | 9  => 30 | 10 => 31
  | 11 => 30 | 12 => 31
  | _  => 0

/-- A real calendar date: the `ok` field rules out impossible month/day combos. -/
structure Date where
  year  : Int
  month : Nat
  day   : Nat
  ok    : 1 ≤ month ∧ month ≤ 12 ∧ 1 ≤ day ∧ day ≤ daysInMonth year month

namespace Date

/-- Build a `Date`, or `none` if the month/day are out of range for the year. -/
def mk? (year : Int) (month day : Nat) : Option Date :=
  if h : 1 ≤ month ∧ month ≤ 12 ∧ 1 ≤ day ∧ day ≤ daysInMonth year month
  then some ⟨year, month, day, h⟩ else none

/-- Parse an ISO `YYYY-MM-DD` string; `none` on a malformed or impossible date. -/
def parse? (s : String) : Option Date :=
  match s.splitOn "-" with
  | [y, m, d] => do
      let year  ← y.toNat?        -- ISO years are non-negative
      let month ← m.toNat?
      let day   ← d.toNat?
      mk? (year : Int) month day
  | _ => none

private def padLeft (width : Nat) (s : String) : String :=
  if s.length < width then String.ofList (List.replicate (width - s.length) '0') ++ s else s

/-- Render back to ISO `YYYY-MM-DD` (the form a `<input type="date">` expects). -/
protected def toString (d : Date) : String :=
  padLeft 4 (toString d.year.toNat) ++ "-" ++
  padLeft 2 (toString d.month)      ++ "-" ++
  padLeft 2 (toString d.day)

instance : ToString Date := ⟨Date.toString⟩

/-- `a` is strictly before `b` (lexicographic on year, month, day). The basis for
    relative rules like "must be in the future" once "today" is supplied. -/
def before (a b : Date) : Bool :=
  a.year < b.year ||
    (a.year == b.year && (a.month < b.month ||
      (a.month == b.month && a.day < b.day)))

end Date

/-- Chronological order, so a refinement can read `today < d` ("d is in the future")
    or `d < today` ("d is in the past"). -/
instance : LT Date := ⟨fun a b => a.before b = true⟩
instance : LE Date := ⟨fun a b => b.before a = false⟩
instance (a b : Date) : Decidable (a < b) := inferInstanceAs (Decidable (a.before b = true))
instance (a b : Date) : Decidable (a ≤ b) := inferInstanceAs (Decidable (b.before a = false))

/-- A `Date` is JSON as its ISO `YYYY-MM-DD` string, so a `schema` field can persist
    and reload one (decoding rejects an impossible date, since `parse?` does). -/
instance : ToJson Date := ⟨fun d => .str (toString d)⟩
instance : FromJson Date :=
  ⟨fun j => match j.str? with
    | some s => (Date.parse? s).elim (.error "expected a date (YYYY-MM-DD)") .ok
    | none   => .error "expected a date string"⟩

end Qed
