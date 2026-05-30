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

  The `form` command declares the structure, its `ofRaw` validator, its `canSubmit`
  gate, *and* the `canSubmit_iff` proof — written once, no hand proof:

      form Signup where
        email    : Email
        password : MinLen 8
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

/-! ### The `form` command

`form T where f₁ : p₁ …` (fields one per line, or `;`-separated on one line) expands
to a structure with `fieldᵢ : Field pᵢ`, an `ofRaw` that validates raw strings into
`Option T`, a `canSubmit` gate, and the proof `canSubmit … ↔ p₁ … ∧ … ∧ pₙ …`.
Core-syntax only (no `import Lean`). -/

open Lean in
syntax (name := formCmd) "form " ident " where " sepBy1IndentSemicolon(group(ident " : " term)) : command

open Lean in
macro_rules
  | `(form $t:ident where $[$fs:ident : $ps:term]*) => do
      -- `fs` stays the ident array (for output splices `$fs:ident`); `ft` is the
      -- same names as terms, for the application/proof syntax we build below.
      let ft : Array (TSyntax `term) := fs.map fun f => ⟨f.raw⟩
      let pairs := ft.zip ps
      let ofRawId     := mkIdent (Name.str t.getId "ofRaw")
      let canSubmitId := mkIdent (Name.str t.getId "canSubmit")
      let iffId       := mkIdent (Name.str t.getId "canSubmit_iff")
      -- validate calls and the two applications, prebuilt (so `$fs` is used once
      -- per splice — reusing a splice variable twice is rejected).
      let valCalls ← pairs.mapM fun (f, p) => `(Field.validate $p $f)
      let ofRawCall     ← ft.foldlM (init := (⟨ofRawId.raw⟩ : TSyntax `term))     fun acc f => `($acc $f)
      let canSubmitCall ← ft.foldlM (init := (⟨canSubmitId.raw⟩ : TSyntax `term)) fun acc f => `($acc $f)
      -- RHS conjunction: p₁ f₁ ∧ … ∧ pₙ fₙ
      let conjs ← pairs.mapM fun (f, p) => `($p $f)
      let rhs ← match conjs.toList with
        | []      => `(True)
        | c :: cs => cs.foldlM (init := c) fun acc x => `($acc ∧ $x)
      -- Proof: rewrite each spec to `(validate …).isSome`, unfold, case-split.
      let rwIso    ← pairs.mapM fun (f, p) => `(Lean.Parser.Tactic.rwRule| ← Field.isSome_validate $p $f)
      let rwUnfold ← #[canSubmitId, ofRawId].mapM fun id => `(Lean.Parser.Tactic.rwRule| $id:ident)
      let rwRules := rwIso ++ rwUnfold
      let casesTac ← pairs.foldrM (init := ← `(tactic| simp)) fun (f, p) acc =>
        `(tactic| cases Field.validate $p $f <;> $acc)
      `(structure $t where
          $[$fs:ident : Field $ps:term]*
        def $ofRawId $[($fs:ident : String)]* : Option $t := do
          $[let $fs:ident ← $valCalls:term]*
          return { $[$fs:ident],* }
        def $canSubmitId $[($fs:ident : String)]* : Bool := ($ofRawCall).isSome
        theorem $iffId $[($fs:ident : String)]* : $canSubmitCall = true ↔ $rhs := by
          rw [$rwRules,*] ; $casesTac)

/-! ### An example form

Lives in `Qed.Demo` so its field-spec names (`Email`, `MinLen`) don't collide with
the ones an application defines. Its `canSubmit_iff` is checked by the manifest. -/

namespace Demo

/-- An email must contain `@` and be at least three characters. Written as `abbrev`
    so the `Decidable` instance `Field.validate` needs is inferred. -/
abbrev Email (s : String) : Prop := s.contains '@' ∧ s.length ≥ 3

/-- A field must be at least `n` characters. -/
abbrev MinLen (n : Nat) (s : String) : Prop := s.length ≥ n

form Signup where
  email    : Email
  password : MinLen 8

end Demo

end Qed
