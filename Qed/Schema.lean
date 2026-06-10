/-
  Qed.Schema: one declaration, both directions: an editable form *and* a JSON codec,
  sharing the same field refinements.

  A field is a *typed refinement*: `Field p` (for `p : α → Prop`) is a value of type
  `α` paired with a proof that `p` holds of it. The only way to build one is to pass
  validation, so a value carrying `Field` fields is *evidence* that they are valid,
  an invalid value is unrepresentable, and a handler that takes one can never run on
  bad data, whether the value came from a form or from a parsed payload.

  A field's wire behaviour is a `Codec α`: how to parse the raw DOM string into a
  typed `α`, an optional refinement on that `α`, and how to render the widget. The
  JSON side is the value type's own `ToJson`/`FromJson`. Built-ins span the HTML
  controls, `Codec.text`, `Codec.nat`/`Codec.int`, `Codec.checkbox` (a `Bool`),
  `Codec.date` (a verified `Qed.Date`), `Codec.select`/`Codec.radios` (one of a fixed
  set), plus `Codec.json T`, a widget-less field for a nested record or a list that
  rides the JSON only (`author : Codec.json Author`, `tags : Codec.json (List Tag)`).
  Validation is "parse, don't validate": the raw string is parsed to `α` first, then
  refined.

  The `schema` command reads one declaration and generates, with the field names
  written once: the editable `Draft` (raw strings) + `Draft.empty`, the validated
  structure, `parse : Draft → Option T`, the `canSubmit` gate, the `canSubmit_iff`
  proof, a widget-aware `formView`, and the JSON codec, `toJson`/`fromJson` plus
  `decode`/`encode` (and, for a type with no context parameters, the `ToJson`/`FromJson`
  instances). A refined field decodes through its refinement in *both* directions, so
  out-of-range payload data is rejected at `decode` exactly as the form rejects it at
  submit, and that holds however the codec is spelled (a refinement factored into a
  `def` is detected by elaborating the codec, not by reading the syntax).

      schema Book where
        id      : Codec.text.jsonOnly            -- in JSON, not in the form
        title   : Codec.text.refine NonEmpty
        year    : Codec.nat.refine Year
        genre   : Codec.select [("free", "Free"), ("pro", "Pro")]
        inPrint : Codec.checkbox
-/
import Qed.Notation
import Qed.Json
import Qed.Date
import Lean

namespace Qed

/-- A value of type `α` paired with a proof it satisfies `p`. The only constructor
    is validation, so a `Field p` is evidence that its value is valid. -/
structure Field {α : Type} (p : α → Prop) where
  val : α
  ok  : p val

/-- A refined field reads as its value in display positions, so a view writes
    `b.title` where the type wants the underlying `α`; `.val` stays available (and is
    what proofs use). The proof is only ever *added* by validation, never dropped by
    accident: this is a one-way coercion out. -/
instance {α : Type} {p : α → Prop} : CoeOut (Field p) α := ⟨Field.val⟩

/-- Show a refined field as its value, so `s!"by {b.author}"` needs no `.val`. -/
instance {α : Type} {p : α → Prop} [ToString α] : ToString (Field p) :=
  ⟨fun f => toString f.val⟩

/-- A field's wire behaviour: parse the raw DOM string into a typed `α`, a (decidable)
    refinement on that value, and how to render the widget. `render` is polymorphic in
    the app's message type, so a control composes into any app. The JSON side rides the
    value type's own `ToJson`/`FromJson`, so it is not duplicated here. -/
structure Codec (α : Type) where
  /-- Parse the raw input string; `none` when it isn't a well-formed `α`. -/
  parse  : String → Option α
  /-- Render the widget for the current raw value, wiring edits back through `set`. -/
  render : {msg : Type} → (raw : String) → (set : String → msg) → Html msg
  /-- The refinement the parsed value must satisfy (`fun _ => True` by default). -/
  valid  : α → Prop
  /-- Decidability of `valid`, so validation is computable. -/
  dec    : DecidablePred valid
  /-- Whether this field appears in the form. `false` for server-owned fields (an id)
      that ride the JSON but should never be edited. -/
  inForm : Bool := true

/-- The value type a `Codec` reads, recovered from its index. Reducible, so a bare
    (unrefined) `schema` field of type `Codec.Val c` is just `α` for every purpose. -/
@[reducible] def Codec.Val {α : Type} (_ : Codec α) : Type := α

namespace Codec

/-- Narrow a control with a refinement: the field is valid only when the parsed value
    also satisfies `p`, and that check runs on *both* form submit and JSON decode.
    Specs are decidable props (`abbrev` so the instance is inferred), composing with
    `∧`, `≥`, and the rest of Lean's logic. -/
def refine (c : Codec α) (p : α → Prop) [DecidablePred p] : Codec α :=
  { c with valid := p, dec := inferInstance }

/-- Keep this field out of the form (it still rides the JSON). Use for a server-owned
    value like a record id that the client carries but never edits. -/
def jsonOnly (c : Codec α) : Codec α := { c with inForm := false }

/-- Run a control on raw text: parse, then check the refinement, yielding evidence
    (`Field c.valid`) exactly when both succeed. -/
def run (c : Codec α) (raw : String) : Option (Field c.valid) :=
  haveI := c.dec
  match c.parse raw with
  | some a => if h : c.valid a then some ⟨a, h⟩ else none
  | none   => none

/-- Running succeeds iff the raw string parses to a value satisfying the refinement
   , the per-field characterisation behind a schema's `canSubmit_iff`. -/
theorem isSome_run (c : Codec α) (raw : String) :
    (c.run raw).isSome = true ↔ ∃ a, c.parse raw = some a ∧ c.valid a := by
  haveI := c.dec
  unfold Codec.run
  cases hp : c.parse raw with
  | none   => simp
  | some a => by_cases hv : c.valid a <;> simp [hv]

/-- Decode the value at a JSON key and check the refinement, yielding evidence
    (`Field c.valid`) exactly when the value decodes *and* passes the spec, the JSON
    mirror of `run`, so a decoded record carries the same proofs a form would. -/
def fromJsonField {α} (c : Codec α) [FromJsonField α] (j : Json) (key : String) :
    Except String (Field c.valid) :=
  haveI := c.dec
  match (FromJsonField.fromField j key : Except String α) with
  | .error e => .error e
  | .ok a    => if h : c.valid a then .ok ⟨a, h⟩ else .error s!"{key}: failed validation"

private def toInt? (s : String) : Option Int :=
  match s.toList with
  | '-' :: ds => (String.ofList ds).toNat?.map fun n => -(Int.ofNat n)
  | _         => s.toNat?.map Int.ofNat

/-! ### Built-in controls. Each fixes a value type and a widget; `refine` adds a spec. -/

/-- A single-line text field (value `String`). -/
def text : Codec String where
  parse := some; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [value raw, onInput set]

/-- A multi-line text field (value `String`). -/
def textarea : Codec String where
  parse := some; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "textarea" [value raw, onInput set]

/-- A number field parsed to a `Nat` (rejects negatives and non-numbers). -/
def nat : Codec Nat where
  parse := fun s => s.toNat?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [type' "number", attr "min" "0", value raw, onInput set]

/-- A number field parsed to an `Int`. -/
def int : Codec Int where
  parse := toInt?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [type' "number", value raw, onInput set]

/-- A checkbox (value `Bool`). `refine (· = true)` makes it required. -/
def checkbox : Codec Bool where
  parse := fun s => some (s == "true"); valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set =>
    el "input" [type' "checkbox", checked (raw == "true"), onCheck (fun b => set (toString b))]

/-- A date field parsed to a verified `Qed.Date` (an impossible date is rejected). -/
def date : Codec Date where
  parse := Date.parse?; valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set => el "input" [type' "date", value raw, onInput set]

/-- A `<select>` over `(value, label)` options; the value must be one of them. -/
def select (options : List (String × String)) : Codec String where
  parse := fun s => if options.any (fun o => o.1 == s) then some s else none
  valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set =>
    el "select" [value raw, onChange set]
      (options.map fun (v, lbl) => el "option" [value v] [lbl])

/-- A radio-button group named `group`, over `(value, label)` options. -/
def radios (group : String) (options : List (String × String)) : Codec String where
  parse := fun s => if options.any (fun o => o.1 == s) then some s else none
  valid := fun _ => True; dec := fun _ => inferInstance
  render := fun raw set =>
    el "div" [cls "qed-radios"]
      (options.map fun (v, lbl) =>
        el "label" [] [el "input" [type' "radio", Qed.name group, value v, checked (raw == v), onChange set], lbl])

/-- Lift any JSON-codable type into a field that rides the JSON but has no form widget,
    for a nested record or a list, e.g. `author : Codec.json Author`,
    `tags : Codec.json (List Tag)`. The JSON side is the type's own `ToJson`/`FromJson`, so it
    nests recursively. There is no flat widget that fills a nested object, so such a field can't
    be produced from the form (`parse` yields `none`, leaving `canSubmit` false); it's for the
    decode/encode side. -/
def json (α : Type) [ToJson α] [FromJson α] : Codec α where
  parse := fun _ => none
  valid := fun _ => True; dec := fun _ => inferInstance
  render := fun _ _ => el "span" [] []
  inForm := false

end Codec

/-! ### The `schema` command

`schema T where f : control …` (fields one per line, or `;`-separated) generates, from
the one declaration: `T.Draft` (raw strings) + `T.Draft.empty`, the validated `T` (a
refined field becomes a proof-carrying `Field`, an unrefined one stays its bare value
type), `T.parse : Draft → Option T`, `T.canSubmit`, the proof `T.canSubmit_iff`,
`T.formView`, and the JSON codec `T.toJson`/`T.fromJson`/`T.decode`/`T.encode`. When `T`
has no context parameters it also gets the `ToJson T`/`FromJson T` instances (a class
instance can't quantify a runtime binder, so a context-parameterised schema exposes the
codec only as those functions, e.g. `T.decode today s`).

A field's refinement has to be *decidable* (validity is decided at runtime). The command
checks that up front and, when it isn't, reports the field and the fix, write the
predicate as `abbrev`, not `def`, instead of letting the bare `DecidablePred` synthesis
failure cascade.

Context binders after the name, `schema Booking (today : Date) where …`, thread into
the validated type and the form functions, so a refinement can depend on them (e.g.
`when : Codec.date.refine (fun d => today < d)`). A schema with context binders is
form-only: its type is indexed, so it has no `ToJson`/`FromJson` instance. -/

open Lean in
syntax (name := schemaCmd) "schema " ident ("(" ident " : " term ")")* " where "
  sepBy1IndentSemicolon(group(ident " : " term)) : command

open Lean Elab Term Meta in
/-- Decide, field by field, whether it carries a refinement, *semantically*. The codec is
    elaborated (with the schema's context binders in scope, so a refinement like
    `fun d => today < d` resolves), then we check whether its `valid` is just `fun _ => True`.
    Because this inspects the elaborated `valid`, not the surface syntax, it is robust to how
    the codec is spelled: factoring a refined codec into a `def` or aliasing `refine` still
    reports refined, so a refinement can never be silently dropped. A field whose term isn't a
    `Codec` is rejected here with a clear message (not a synth cascade). `i` walks the context
    binders, nesting one `withLocalDeclD` each, before elaborating every field under them. -/
private partial def schemaRefinedAux (cbns : Array Ident) (cbts : Array Term)
    (inputs : Array Term) (i : Nat) : TermElabM (Array Bool) := do
  if i < cbns.size then
    let bt ← elabType cbts[i]!
    withLocalDeclD cbns[i]!.getId bt fun _ => schemaRefinedAux cbns cbts inputs (i + 1)
  else
    inputs.mapM fun inp => do
      let c ← elabTermAndSynthesize inp none
      let cty ← instantiateMVars (← inferType c)
      match cty.getAppFnArgs with
      | (``Qed.Codec, #[α]) =>
          let validExpr := mkApp2 (mkConst ``Qed.Codec.valid) α c
          let trueFn := Expr.lam `x α (mkConst ``True) BinderInfo.default
          -- refined ⇔ `valid` is NOT definitionally `fun _ => True`
          pure (! (← isDefEq validExpr trueFn))
      | _ =>
          throwErrorAt inp m!"a schema field must be a `Codec` (e.g. `Codec.text`, \
            `Codec.nat.refine P`, or `Codec.json T` for a nested or list field), but this has \
            type{indentExpr cty}"

open Lean Elab Command in
private def schemaRefinedFlags (cbns : Array Ident) (cbts : Array Term) (inputs : Array Term) :
    CommandElabM (Array Bool) :=
  liftTermElabM (schemaRefinedAux cbns cbts inputs 0)

open Lean Elab Command Term in
elab_rules : command
  | `(schema $t:ident $[($cbns:ident : $cbts:term)]* where $[$fs:ident : $inputs:term]*) => do
      let draftId := mkIdent (t.getId ++ `Draft)
      let emptyId := mkIdent (t.getId ++ `Draft ++ `empty)
      let parseId := mkIdent (t.getId ++ `parse)
      let canId   := mkIdent (t.getId ++ `canSubmit)
      let iffId   := mkIdent (t.getId ++ `canSubmit_iff)
      let viewId  := mkIdent (t.getId ++ `formView)
      let decodeId := mkIdent (t.getId ++ `decode)
      let encodeId := mkIdent (t.getId ++ `encode)
      let toJsonId   := mkIdent (t.getId ++ `toJson)
      let fromJsonId := mkIdent (t.getId ++ `fromJson)
      let pairs := fs.zip inputs
      let refined ← schemaRefinedFlags cbns cbts inputs
      -- ── Friendly pre-check. Each field's refinement must be decidable, or validity can't be
      -- computed. We probe by elaborating the control in isolation and capturing (then suppressing)
      -- whatever it logs, Lean *logs* a failed instance search rather than throwing it, so a plain
      -- try/catch wouldn't see it. If the probe logged a missing `DecidablePred`, that field's
      -- refinement isn't decidable: report it and stop, before the generated code turns one missing
      -- instance into a synth pile. Any other message (e.g. a context binder not yet in scope, like
      -- `today`) is discarded here and surfaces from the real generation below, in place.
      for (f, inp) in pairs do
        let before := (← get).messages
        try liftTermElabM (discard <| elabTermAndSynthesize inp none) catch _ => pure ()
        let probeMsgs := (← get).messages.toList.drop before.toList.length
        modify fun st => { st with messages := before }
        let mut undecidable := false
        for msg in probeMsgs do
          if ((← msg.data.toString).splitOn "DecidablePred").length > 1 then undecidable := true
        if undecidable then
          throwErrorAt inp m!"schema field `{f.getId}` has a refinement that isn't decidable, so \
            validity can't be computed (no `DecidablePred` for it).\n\nThe usual cause is a \
            predicate written with `def`. Write it as an `abbrev` instead, so Lean sees it reduces \
            to a decidable check:\n    abbrev MyPredicate (x : …) : Prop := …\nIf it genuinely \
            can't be decided, give it a `DecidablePred` instance."
      -- ── Generation. Context binders (e.g. `(today : Date)`) thread into the validated type and
      -- the form functions, so a refinement may depend on them. `cbns` stays ident-typed for
      -- `$cbns:ident` splices; `cbnsT` is the same names in application position (`T today`, …).
      let cbnsT : Array (TSyntax `term) := cbns.map fun c => ⟨c.raw⟩
      let appTo : TSyntax `term → CommandElabM (TSyntax `term) := fun head =>
        cbnsT.foldlM (init := head) fun acc c => `($acc $c)
      let tApp     ← appTo ⟨t.raw⟩
      let parseApp ← appTo ⟨parseId.raw⟩
      let canApp   ← appTo ⟨canId.raw⟩
      let toJsonApp   ← appTo ⟨toJsonId.raw⟩
      let fromJsonApp ← appTo ⟨fromJsonId.raw⟩
      let emptyVals ← fs.mapM fun _ => `(term| "")
      -- Per-field shapes, keyed on whether the field is refined:
      --   structTy   the stored field type (`Field c.valid` vs the bare value type)
      --   runCall    the form-side decode of the draft string (`run` vs bare `parse`)
      --   jsonDecode the JSON-side decode at the key (`fromJsonField` vs bare `fromField`)
      --   jsonRead   reading the value back out to encode (`.val` for a refined field)
      let structTys ← (pairs.zip refined).mapM fun ((_, inp), r) =>
        if r then `(Field ($inp).valid) else `(Codec.Val $inp)
      let runCalls ← (pairs.zip refined).mapM fun ((f, inp), r) =>
        if r then `(($inp).run (d.$f:ident)) else `(($inp).parse (d.$f:ident))
      let jsonDecodes ← (pairs.zip refined).mapM fun ((f, inp), r) => do
        let keyLit := Syntax.mkStrLit (toString f.getId)
        if r then `(($inp).fromJsonField j $keyLit)
        else `((FromJsonField.fromField j $keyLit : Except String (Codec.Val $inp)))
      let jsonReads ← (pairs.zip refined).mapM fun ((f, _), r) =>
        if r then `((x.$f).val) else `(x.$f)
      let jsonPairs ← (fs.zip jsonReads).mapM fun (f, rd) =>
        let keyLit := Syntax.mkStrLit (toString f.getId); `(($keyLit, toJson $rd))
      -- proof RHS: conjunction of `(runCallᵢ).isSome`
      let isSomes ← runCalls.mapM fun rc => `(($rc).isSome)
      let rhs ← match isSomes.toList with
        | []      => `(True)
        | c :: cs => cs.foldlM (init := c) fun acc x => `($acc ∧ $x)
      let casesTac ← runCalls.foldrM (init := ← `(tactic| simp)) fun rc acc =>
        `(tactic| cases $rc:term <;> $acc)
      -- formView rows: each is included only when its control's `inForm` is set, so a
      -- `jsonOnly` field rides the JSON without showing up as a widget.
      let rowGroups ← (pairs.zip runCalls).mapM fun ((f, inp), rc) => do
        let nameLit := Syntax.mkStrLit (toString f.getId)
        let errLit  := Syntax.mkStrLit ("Please enter a valid " ++ toString f.getId)
        -- a field is shown as invalid once *touched* (raw non-empty) and its control fails to
        -- run; we surface an error message and `aria-invalid` then, not on an untouched field.
        `(term|
            (if ($inp).inForm then
              [(let bad := d.$f:ident != "" && ($rc).isNone
                el "label" [cls "qed-field", attr "aria-invalid" (if bad then "true" else "false")]
                  ([ el "span" [cls "qed-label"] [$nameLit],
                     ($inp).render (d.$f:ident) (fun v => onEdit { d with $f:ident := v }) ]
                   ++ (if bad then [el "span" [cls "qed-error"] [$errLit]] else [])))]
             else []))
      let submitBtn ← `(term| el "button" [disabled (!($parseApp d).isSome), onClick submit] "Submit")
      let viewBody ← rowGroups.foldrM (init := ← `(term| [$submitBtn])) fun g acc => `(term| $g ++ $acc)
      -- built as separate commands (not one multi-command quotation) and elaborated in dependency
      -- order, since `elabCommand` runs one command at a time.
      let formCmds : Array (TSyntax `command) := #[
        ← `(command| structure $draftId where
              $[$fs:ident : String]*),
        ← `(command| def $emptyId : $draftId := { $[$fs:ident := $emptyVals],* }),
        ← `(command| structure $t $[($cbns:ident : $cbts:term)]* where
              $[$fs:ident : $structTys]*),
        ← `(command| def $parseId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Option $tApp := do
              $[let $fs:ident ← $runCalls:term]*
              return { $[$fs:ident],* }),
        ← `(command| def $canId $[($cbns:ident : $cbts:term)]* (d : $draftId) : Bool :=
              ($parseApp d).isSome),
        ← `(command| theorem $iffId $[($cbns:ident : $cbts:term)]* (d : $draftId) :
              $canApp d = true ↔ $rhs := by unfold $canId $parseId; $casesTac),
        ← `(command| def $viewId {msg : Type} $[($cbns:ident : $cbts:term)]* (d : $draftId)
              (onEdit : $draftId → msg) (submit : msg) : Html msg :=
              el "div" [cls "qed-form"] $viewBody) ]
      -- JSON codec. `toJson`/`fromJson`/`decode`/`encode` are generated for EVERY schema, threading
      -- any context binders as leading arguments, so a context-parameterised schema still has a JSON
      -- codec (e.g. `Appt.decode today s`). Only the `ToJson`/`FromJson` *instances* are restricted to
      -- non-indexed types, since a class instance can't quantify a runtime binder.
      let jsonFnCmds : Array (TSyntax `command) := #[
        ← `(command| def $toJsonId $[($cbns:ident : $cbts:term)]* (x : $tApp) : Json :=
              Json.obj [$[$jsonPairs],*]),
        ← `(command| def $fromJsonId $[($cbns:ident : $cbts:term)]* (j : Json) : Except String $tApp := do
              $[let $fs:ident ← $jsonDecodes:term]*
              return { $[$fs:ident],* }),
        ← `(command| def $decodeId $[($cbns:ident : $cbts:term)]* (s : String) (maxDepth : Nat := 64) :
              Except String $tApp := (Json.parse s maxDepth).bind ($fromJsonApp)),
        ← `(command| def $encodeId $[($cbns:ident : $cbts:term)]* (x : $tApp) : String :=
              Json.render ($toJsonApp x)) ]
      let jsonInstCmds : Array (TSyntax `command) := #[
        ← `(command| instance : ToJson $t := ⟨$toJsonId⟩),
        ← `(command| instance : FromJson $t := ⟨$fromJsonId⟩) ]
      let cmds := formCmds ++ jsonFnCmds ++ (if cbns.isEmpty then jsonInstCmds else #[])
      for c in cmds do elabCommand c

/-! ### An example schema

Lives in `Qed.Demo` so its field-spec names don't collide with an application's. Its
`canSubmit_iff` is checked by the axiom manifest. -/

namespace Demo

/-- An email must contain `@` and be at least three characters. `abbrev` so the
    `Decidable` instance is inferred. -/
abbrev Email (s : String) : Prop := s.contains '@' ∧ s.length ≥ 3

/-- An age must be at least 18. -/
abbrev Adult (n : Nat) : Prop := n ≥ 18

schema Signup where
  email : Codec.text.refine Email
  age   : Codec.nat.refine Adult
  agree : Codec.checkbox.refine (· = true)

end Demo

end Qed
