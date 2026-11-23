import Qed.Html
import Qed.Json.Basic

namespace Qed

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
  match s.splitOn "-" with | [y, m, d] => do mk? ((← y.toNat?) : Int) (← m.toNat?) (← d.toNat?) | _ => none
private def padLeft (w : Nat) (s : String) : String := if s.length < w then String.ofList (List.replicate (w - s.length) '0') ++ s else s
protected def toString (d : Date) : String := s!"{padLeft 4 (toString d.year.toNat)}-{padLeft 2 (toString d.month)}-{padLeft 2 (toString d.day)}"
instance : ToString Date := ⟨Date.toString⟩
@[reducible] instance : Coe Date (Html msg) := ⟨fun d => .text (toString d)⟩
def before (a b : Date) : Bool := a.year < b.year || (a.year == b.year && (a.month < b.month || (a.month == b.month && a.day < b.day)))
end Date

instance : BEq Date := ⟨fun a b => a.year == b.year && a.month == b.month && a.day == b.day⟩
instance : LawfulBEq Date where
  eq_of_beq {a b} h := by cases a; cases b; simp only [BEq.beq, Bool.and_eq_true, decide_eq_true_eq] at h; rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; rfl
  rfl := by simp [BEq.beq]
instance : LT Date := ⟨fun a b => a.before b = true⟩
instance : LE Date := ⟨fun a b => b.before a = false⟩
instance (a b : Date) : Decidable (a < b) := inferInstanceAs (Decidable (a.before b = true))
instance (a b : Date) : Decidable (a ≤ b) := inferInstanceAs (Decidable (b.before a = false))
instance : ToJson Date := ⟨fun d => .str (toString d)⟩
instance : FromJson Date := ⟨fun j => j.str?.elim (.error "expected a date string") fun s => (Date.parse? s).elim (.error "expected a date (YYYY-MM-DD)") .ok⟩

end Qed
