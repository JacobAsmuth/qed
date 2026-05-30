/-
  Qed.Form — forms whose "submit enabled ⇔ provably valid", across every HTML input.

  A field is a *typed refinement*: `Field p` (for `p : α → Prop`) is a value of type
  `α` paired with a proof that `p` holds of it. The only way to build one is to pass
  validation, so a value of a form type is *evidence* that every field is valid — an
  invalid form is unrepresentable, and a `submit` handler that takes one can never run
  on bad data.

  A control is an `Input α`: how to parse the raw DOM string into a typed `α`, an
  optional refinement on that `α`, and how to render the widget. Built-ins span the
  HTML controls — `Input.text`, `Input.nat`/`Input.int`, `Input.checkbox` (a `Bool`),
  `Input.date` (a verified `Qed.Date`), `Input.select`/`Input.radios` (one of a fixed
  set). Because the value is typed, validation is "parse, don't validate": the raw
  string is parsed to `α` first (a number, a real calendar date, …), then refined.

  The `form` command reads one declaration and generates: the editable `Draft` (raw
  strings) with `Draft.empty`, the validated structure, `parse : Draft → Option T`,
  the `canSubmit` gate, the `canSubmit_iff` proof, and a widget-aware `formView` —
  field names written once. Core-syntax only (no `import Lean`):

      form Signup where
        email : Input.text.refine Email
        age   : Input.nat.refine Adult
        agree : Input.checkbox.refine (· = true)
        plan  : Input.select [("free", "Free"), ("pro", "Pro")]
-/
import Qed.Notation
import Qed.Date

namespace Qed

/-- A value of type `α` paired with a proof it satisfies `p`. The only constructor
    is validation, so a `Field p` is evidence that its value is valid. -/
structure Field {α : Type} (p : α → Prop) where
  val : α
  ok  : p val

/-- A form control: parse the raw DOM string into a typed `α`, a (decidable)
    refinement on that value, and how to render the widget. `render` is polymorphic
    in the app's message type, so a control composes into any app. -/
structure Input (α : Type) where
  /-- Parse the raw input string; `none` when it isn't a well-formed `α`. -/
  parse  : String → Option α
  /-- The refinement the parsed value must satisfy (`fun _ => True` by default). -/
  valid  : α → Prop
  /-- Decidability of `valid`, so validation is computable. -/
  dec    : DecidablePred valid
  /-- Render the widget for the current raw value, wiring edits back through `set`. -/
  render : {msg : Type} → (raw : String) → (set : String → msg) → Html msg

namespace Input

/-- Narrow a control with a refinement: the field is valid only when the parsed
    value also satisfies `p`. Specs are decidable props (`abbrev` so the instance
    is inferred), composing with `∧`, `≥`, and the rest of Lean's logic. -/
def refine (i : Input α) (p : α → Prop) [DecidablePred p] : Input α :=
  { i with valid := p, dec := inferInstance }

/-- Run a control on raw text: parse, then check the refinement, yielding evidence
    (`Field i.valid`) exactly when both succeed. -/
def run (i : Input α) (raw : String) : Option (Field i.valid) :=
  haveI := i.dec
  match i.parse raw with
  | some a => if h : i.valid a then some ⟨a, h⟩ else none
  | none   => none

/-- Running succeeds iff the raw string parses to a value satisfying the refinement
    — the per-field characterisation behind a form's `canSubmit_iff`. -/
theorem isSome_run (i : Input α) (raw : String) :
    (i.run raw).isSome = true ↔ ∃ a, i.parse raw = some a ∧ i.valid a := by
  haveI := i.dec
  unfold Input.run
  cases hp : i.parse raw with
  | none   => simp
  | some a => by_cases hv : i.valid a <;> simp [hv]

private def toInt? (s : String) : Option Int :=
  match s.toList with
  | '-' :: ds => (String.mk ds).toNat?.map fun n => -(Int.ofNat n)
  | _         => s.toNat?.map Int.ofNat

/-! ### Built-in controls. Each fixes a value type and a widget; `refine` adds a spec. -/

/-- A single-line text field (value `String`). -/
def text : Input String where
  parse := some; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => input [value raw, onInput set]

/-- A multi-line text field (value `String`). -/
def textarea : Input String where
  parse := some; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "textarea" [value raw, onInput set]

/-- A number field parsed to a `Nat` (rejects negatives and non-numbers). -/
def nat : Input Nat where
  parse := fun s => s.toNat?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => input [type' "number", attr "min" "0", value raw, onInput set]

/-- A number field parsed to an `Int`. -/
def int : Input Int where
  parse := toInt?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => input [type' "number", value raw, onInput set]

/-- A checkbox (value `Bool`). `refine (· = true)` makes it required. -/
def checkbox : Input Bool where
  parse := fun s => some (s == "true"); valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set =>
    input [type' "checkbox", checked (raw == "true"), onCheck (fun b => set (toString b))]

/-- A date field parsed to a verified `Qed.Date` (an impossible date is rejected). -/
def date : Input Date where
  parse := Date.parse?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => input [type' "date", value raw, onInput set]

/-- A `<select>` over `(value, label)` options; the value must be one of them. -/
def select (options : List (String × String)) : Input String where
  parse := fun s => if options.any (fun o => o.1 == s) then some s else none
  valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set =>
    el "select" [value raw, onChange set]
      (options.map fun (v, lbl) => el "option" [value v] [lbl])

/-- A radio-button group named `group`, over `(value, label)` options. -/
def radios (group : String) (options : List (String × String)) : Input String where
  parse := fun s => if options.any (fun o => o.1 == s) then some s else none
  valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set =>
    el "div" [cls "qed-radios"]
      (options.map fun (v, lbl) =>
        label [] [input [type' "radio", Qed.name group, value v, checked (raw == v), onChange set], lbl])

end Input

/-! ### The `form` command

`form T where f : control …` (fields one per line, or `;`-separated) generates, from
the one declaration: `T.Draft` (raw strings) + `T.Draft.empty`, the validated `T`
(each field a `Field`), `T.parse : Draft → Option T`, `T.canSubmit`, the proof
`T.canSubmit_iff`, and `T.formView`. Core-syntax only (no `import Lean`).

Context binders after the name — `form Booking (today : Date) where …` — thread into
the validated type and every generated function, so a refinement can depend on them
(e.g. `when : Input.date.refine (fun d => today < d)` for "must be in the future").
`parse`/`canSubmit`/`formView` then take `today` as a leading argument. -/

open Lean in
syntax (name := formCmd) "form " ident ("(" ident " : " term ")")* " where "
  sepBy1IndentSemicolon(group(ident " : " term)) : command

open Lean in
macro_rules
  | `(form $t:ident $[($cbns:ident : $cbts:term)]* where $[$fs:ident : $inputs:term]*) => do
      let draftId := mkIdent (t.getId ++ `Draft)
      let emptyId := mkIdent (t.getId ++ `Draft ++ `empty)
      let parseId := mkIdent (t.getId ++ `parse)
      let canId   := mkIdent (t.getId ++ `canSubmit)
      let iffId   := mkIdent (t.getId ++ `canSubmit_iff)
      let viewId  := mkIdent (t.getId ++ `formView)
      -- Context binders (e.g. `(today : Date)`) thread into the validated type and
      -- every generated function, so a refinement may depend on them. `cbns` stays
      -- ident-typed for `$cbns:ident` splices; `cbnsT` is the same names in
      -- application position (`T today`, `parse today`, …).
      let cbnsT : Array (TSyntax `term) := cbns.map fun c => ⟨c.raw⟩
      let appTo : TSyntax `term → MacroM (TSyntax `term) := fun head =>
        cbnsT.foldlM (init := head) fun acc c => `($acc $c)
      let tApp     ← appTo ⟨t.raw⟩
      let parseApp ← appTo ⟨parseId.raw⟩
      let canApp   ← appTo ⟨canId.raw⟩
      let emptyVals ← fs.mapM fun _ => `(term| "")
      let pairs := fs.zip inputs
      -- proof RHS: conjunction of `(inputᵢ.run d.fᵢ).isSome`
      let isSomes ← pairs.mapM fun (f, inp) => `((($inp).run (d.$f:ident)).isSome)
      let rhs ← match isSomes.toList with
        | []      => `(True)
        | c :: cs => cs.foldlM (init := c) fun acc x => `($acc ∧ $x)
      let casesTac ← pairs.foldrM (init := ← `(tactic| simp)) fun (f, inp) acc =>
        `(tactic| cases ($inp).run (d.$f:ident) <;> $acc)
      -- prebuilt so each splice uses `$fs` once (reusing a splice var is rejected)
      let runCalls ← pairs.mapM fun (f, inp) => `(($inp).run (d.$f:ident))
      let rows ← pairs.mapM fun (f, inp) => do
        let nameLit := Syntax.mkStrLit (toString f.getId)
        `(term| label [cls "qed-field"]
            [ span [cls "qed-label"] [$nameLit],
              ($inp).render (d.$f:ident) (fun v => onEdit { d with $f:ident := v }) ])
      `(structure $draftId where
          $[$fs:ident : String]*
        def $emptyId : $draftId := { $[$fs:ident := $emptyVals],* }
        structure $t $[($cbns:ident : $cbts:term)]* where
          $[$fs:ident : Field ($inputs).valid]*
        def $parseId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Option $tApp := do
          $[let $fs:ident ← $runCalls:term]*
          return { $[$fs:ident],* }
        def $canId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Bool := ($parseApp d).isSome
        theorem $iffId $[($cbns:ident : $cbts:term)]* (d : $draftId) : $canApp d = true ↔ $rhs := by
          unfold $canId $parseId; $casesTac
        def $viewId {msg : Type} $[($cbns:ident : $cbts:term)]* (d : $draftId)
            (onEdit : $draftId → msg) (submit : msg) : Html msg :=
          div [cls "qed-form"]
            [ $[$rows],* ,
              button [disabled (!($parseApp d).isSome), onClick submit] "Submit" ])

/-! ### An example form

Lives in `Qed.Demo` so its field-spec names don't collide with an application's. Its
`canSubmit_iff` is checked by the axiom manifest. -/

namespace Demo

/-- An email must contain `@` and be at least three characters. `abbrev` so the
    `Decidable` instance is inferred. -/
abbrev Email (s : String) : Prop := s.contains '@' ∧ s.length ≥ 3

/-- An age must be at least 18. -/
abbrev Adult (n : Nat) : Prop := n ≥ 18

form Signup where
  email : Input.text.refine Email
  age   : Input.nat.refine Adult
  agree : Input.checkbox.refine (· = true)

end Demo

end Qed
