/-
  Qed.Form — forms where "submit enabled ⇔ provably valid" (dream-API #5).

  A field is a *refinement type*: `Refined p` is a string that carries a proof it
  satisfies the predicate `p`. The only way to build one is to pass validation,
  so a `Signup` value is *evidence* that every field is valid — an invalid form is
  unrepresentable, and a `submit` handler that takes a `Signup` can never run on
  bad data.

  The `canSubmit_iff` theorem states the UI contract: the submit button is enabled
  *exactly* when every field satisfies its spec. The "enabled" bit is the decision
  procedure for validity, so they cannot drift apart.
-/
namespace Qed

/-- A string proven to satisfy the boolean predicate `p`. -/
structure Refined (p : String → Bool) where
  val : String
  ok  : p val = true

namespace Refined

/-- Validate raw input: succeeds with evidence exactly when `p` holds. -/
def validate (p : String → Bool) (s : String) : Option (Refined p) :=
  if h : p s = true then some ⟨s, h⟩ else none

/-- Validation succeeds iff the predicate holds — the field's submit-gate. -/
@[simp] theorem validate_isSome (p : String → Bool) (s : String) :
    (validate p s).isSome = p s := by
  unfold validate; split <;> simp_all

end Refined

/-! ### An example form -/

/-- Email must contain an `@`. -/
def isEmail (s : String) : Bool := s.contains '@'

/-- Age must be a number ≥ 13. -/
def isAdult (s : String) : Bool :=
  match s.toNat? with
  | some n => decide (13 ≤ n)
  | none   => false

/-- A validated sign-up: each field carries its proof of validity. There is no
    way to build this from invalid input. -/
structure Signup where
  email : Refined isEmail
  age   : Refined isAdult

/-- Validate the whole form from raw inputs. -/
def Signup.validate (email age : String) : Option Signup := do
  let e ← Refined.validate isEmail email
  let a ← Refined.validate isAdult age
  some { email := e, age := a }

/-- Whether the submit button should be enabled for the given raw inputs. -/
def Signup.canSubmit (email age : String) : Bool :=
  (Signup.validate email age).isSome

/-- Submit is enabled *exactly* when every field is valid: the enabled-state and
    the validity spec are the same proposition. -/
theorem Signup.canSubmit_iff (email age : String) :
    Signup.canSubmit email age = true ↔ isEmail email = true ∧ isAdult age = true := by
  unfold canSubmit validate
  cases he : Refined.validate isEmail email <;>
    cases ha : Refined.validate isAdult age <;>
    simp_all [← Refined.validate_isSome]

end Qed
