/-
  Qed.Form — forms where "submit enabled ⇔ provably valid" (dream-API #5).

  A field is a *refinement type*: `Field p` is a string paired with a proof that
  the proposition `p` holds of it. The only way to build one is to pass validation,
  so a value of a form type is *evidence* that every field is valid — an invalid
  form is unrepresentable, and a `submit` handler that takes such a value can never
  run on bad data.

  Field specs are ordinary (decidable) propositions, so they compose with `∧`, `≥`,
  and the rest of Lean's logic. `Field.validate` needs a `Decidable` instance for
  the spec; writing specs as `abbrev` (reducible) lets Lean synthesise it.

  The `canSubmit_iff` theorem states the UI contract: the submit button is enabled
  *exactly* when every field satisfies its spec. The "enabled" bit is the decision
  procedure for validity, so they cannot drift apart.
-/
namespace Qed

/-- A string paired with a proof that it satisfies the proposition `p`. The only
    constructor is validation, so a `Field p` is evidence that its value is valid. -/
structure Field (p : String → Prop) where
  val : String
  ok  : p val

namespace Field

/-- Validate raw input against a decidable spec: succeeds with evidence exactly
    when `p s` holds. -/
def validate (p : String → Prop) [DecidablePred p] (s : String) : Option (Field p) :=
  if h : p s then some ⟨s, h⟩ else none

/-- Validation succeeds iff the spec holds — the field's submit-gate. -/
theorem isSome_validate (p : String → Prop) [DecidablePred p] (s : String) :
    (validate p s).isSome ↔ p s := by
  unfold validate; split <;> simp_all

end Field

/-! ### An example form

Lives in `Qed.Demo` so its field-spec names (`Email`, `MinLen`) don't collide with
the ones an application defines. It is also the form whose `canSubmit_iff` the axiom
manifest checks. -/

namespace Demo

/-- An email must contain `@` and be at least three characters. Written as `abbrev`
    so the `Decidable` instance `Field.validate` needs is inferred. -/
abbrev Email (s : String) : Prop := s.contains '@' ∧ s.length ≥ 3

/-- A field must be at least `n` characters. -/
abbrev MinLen (n : Nat) (s : String) : Prop := s.length ≥ n

/-- A validated sign-up: each field carries its proof of validity. There is no
    way to build this from invalid input. -/
structure Signup where
  email    : Field Email
  password : Field (MinLen 8)

/-- Validate the whole form from raw inputs; `none` if any field is invalid. -/
def Signup.ofRaw (email password : String) : Option Signup := do
  let email    ← Field.validate Email email
  let password ← Field.validate (MinLen 8) password
  return { email, password }

/-- Whether the submit button should be enabled for the given raw inputs. -/
def Signup.canSubmit (email password : String) : Bool :=
  (Signup.ofRaw email password).isSome

/-- Submit is enabled *exactly* when every field is valid: the enabled-state and
    the validity spec are the same proposition. -/
theorem Signup.canSubmit_iff (email password : String) :
    Signup.canSubmit email password = true ↔ Email email ∧ MinLen 8 password := by
  rw [← Field.isSome_validate Email email, ← Field.isSome_validate (MinLen 8) password,
      canSubmit, Signup.ofRaw]
  cases Field.validate Email email <;>
    cases Field.validate (MinLen 8) password <;> simp

end Demo

end Qed
