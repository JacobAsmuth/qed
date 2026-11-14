import Qed.Json.Basic

namespace Qed

def isLeapYear (y : Int) : Bool :=
  (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

def daysInMonth (year : Int) (month : Nat) : Nat :=
  match month with
  | 1  => 31 | 2  => if isLeapYear year then 29 else 28
  | 3  => 31 | 4  => 30 | 5  => 31 | 6  => 30
  | 7  => 31 | 8  => 31 | 9  => 30 | 10 => 31
  | 11 => 30 | 12 => 31
  | _  => 0

structure Date where
  year  : Int
  month : Nat
  day   : Nat
  ok    : 1 ≤ month ∧ month ≤ 12 ∧ 1 ≤ day ∧ day ≤ daysInMonth year month

namespace Date

def mk? (year : Int) (month day : Nat) : Option Date :=
  if h : 1 ≤ month ∧ month ≤ 12 ∧ 1 ≤ day ∧ day ≤ daysInMonth year month
  then some ⟨year, month, day, h⟩ else none

def parse? (s : String) : Option Date :=
  match s.splitOn "-" with
  | [y, m, d] => do
      let year  ← y.toNat?
      let month ← m.toNat?
      let day   ← d.toNat?
      mk? (year : Int) month day
  | _ => none

private def padLeft (width : Nat) (s : String) : String :=
  if s.length < width then String.ofList (List.replicate (width - s.length) '0') ++ s else s

protected def toString (d : Date) : String :=
  padLeft 4 (toString d.year.toNat) ++ "-" ++
  padLeft 2 (toString d.month)      ++ "-" ++
  padLeft 2 (toString d.day)

instance : ToString Date := ⟨Date.toString⟩

def before (a b : Date) : Bool :=
  a.year < b.year ||
    (a.year == b.year && (a.month < b.month ||
      (a.month == b.month && a.day < b.day)))

end Date

instance : LT Date := ⟨fun a b => a.before b = true⟩
instance : LE Date := ⟨fun a b => b.before a = false⟩
instance (a b : Date) : Decidable (a < b) := inferInstanceAs (Decidable (a.before b = true))
instance (a b : Date) : Decidable (a ≤ b) := inferInstanceAs (Decidable (b.before a = false))

instance : ToJson Date := ⟨fun d => .str (toString d)⟩
instance : FromJson Date :=
  ⟨fun j => match j.str? with
    | some s => (Date.parse? s).elim (.error "expected a date (YYYY-MM-DD)") .ok
    | none   => .error "expected a date string"⟩

end Qed
