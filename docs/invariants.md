# Invariants

An invariant is a condition that should be true after each update. Qed tries to prove this
for every message, assuming the condition was true before the update. Lean checks the proof.
If the condition is also true for the initial state, it is true after any number of updates.

```lean
invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update
```

This expands to a theorem, `∀ m msg, 0 ≤ m.count → 0 ≤ (update m msg).count`. If the
automatic proof doesn't succeed, compilation fails. Either an update breaks the rule or
Qed needs help with the proof. This checks the Lean update function; see
[how Qed works](architecture.md) for what else the app relies on.

## Why this matters for generated code

After a change to a handler, Qed checks its invariants again during compilation. A condition
such as "the quantity stays in range" specifies the requirement. The proof covers every model
and message described by the theorem. Check the rule
itself too: it needs to describe the behavior you actually care about.

`qed check` scans selected sources for `sorry`, `admit`, and `native_decide`. If an axiom
manifest exists, it rejects output containing `sorryAx` or `error:`. It does **not** enforce
an axiom whitelist or inspect every theorem. Its note about updates without invariants is
based on a source scan and can miss cases.

This is also why a `component` declaration compiles its `set` handlers to a generated `Msg` with
one named constructor per site, never to a closure: `invariant … preserved_by Name.update` reduces
over the generated cases exactly as over hand-written ones. The compiler error includes the
constructor and unresolved goal (``case `set_count_2` still needs: 0 ≤ m.count - 1``).
See `Examples/Local.lean`.

## The two forms

**Automatic.** State the property; the discharger handles it. It covers arithmetic (`omega`),
boolean/`Option` reasoning, `if`/`match` splits, and the `steps` arm normalisation.

```lean
invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update
```

**Effectful transitions** work with the same syntax, the next model is read out of the
`Model × Cmd Msg` a `transition` returns:

```lean
invariant streamSafe : (fun m => m.pending = true → 0 < m.turns.size) preserved_by transition
```

**With a proof (`:=`).** When the property needs a lemma the automation can't guess, usually one
quantified over your own collections, supply the proof. The goal is the generated theorem, so it
opens with `intro m msg h`:

```lean
invariant idsBelowNext : (fun m => ∀ r ∈ m.rows, r.id < m.nextId)
    preserved_by update := by
  intro m msg h
  cases msg <;> simp_all [update] <;> omega
```

## Lifting a contract over a list of children (`for_each`)

With parent-owned components (rendered with `<Card state={c} onMsg={.card}/>`), the child
states are elements of an array in the parent's model. With `for_each`, Qed uses the child's
invariant to check that the parent's updates preserve the rule for every child:

```lean
abbrev Card.Safe (c : Card.State) : Prop :=                 -- the child's contract, written once
  0 ≤ c.likes ∧ c.progress ≤ c.duration ∧ (c.liked → 1 ≤ c.likes)
invariant cardSafe : Card.Safe preserved_by Card.update     -- the card never breaks it

def update : Model → Msg → Model | ...                      -- tap / re-rank / dismiss / add

invariant feedSafe : cardSafe for_each cards preserved_by update
-- ⇒ machine-checks: ∀ m msg, (∀ c ∈ m.cards, Card.Safe c) → (∀ c ∈ (update m msg).cards, Card.Safe c)
```

When the declaration refers to a child invariant such as `cardSafe`, Qed infers the predicate
from that invariant. The predicate can also be specified explicitly:
`Card.Safe for_each cards preserved_by update using cardSafe`.

Qed applies a proven lemma for each supported list operation. For a keyed child message,
it uses `cardSafe`. Filtering preserves the invariant because the remaining elements were
already valid. Adding an element requires a proof that the new element is valid; updating
rows with `Array.map` requires a proof for each updated row. Sorting with `Array.sortBy`
is supported through its membership lemma. `Array.qsort` is not handled automatically.

Because `feedSafe` is itself a `∀ c ∈ cards, …` fact, it composes: a grandparent that owns several
feeds can use `invariant shellSafe : feedSafe for_each feeds preserved_by update
using feedSafe`. Lifts track where your data model nests collections, not render depth.

**When an arm can't be lifted** (a `qsort`, a raw `++` of unvalidated data, an `add` whose element
isn't provably valid), the error message includes the arm, operation, and a proof skeleton.
The `forEachLift` tactic handles the supported cases; the remaining cases need a supplied proof:

```lean
invariant feedSafe : Card.Safe for_each cards preserved_by update using cardSafe := by
  forEachLift update cardSafe Card.Safe     -- closes every arm it can; `m`/`h` are in scope
  case rank => …                            -- fill only what's left
```

The `holds_in` form checks a styling rule over the parent's view, using the child's styling
invariant for each card:

```lean
invariant cardStyled : roleHasOneOf "like" [likeOn, likeOff] holds_in Card.view
invariant feedStyled : cardStyled for_each cards holds_in view
-- ⇒ machine-checks: ∀ m, roleHasOneOf "like" […] (view m) = true   (the same theorem `holds_in` gives)
```

Qed cannot prove this automatically from `holds_in view` alone. With `for_each`, the list and
child invariant are explicit. Qed uses `cardStyled` for each card and checks the rest of the
parent view separately. The `roleHasOneOf_map` lemma establishes that changing a child view's
message type does not change the styling predicate. Any remaining goals and a
`forEachStyleLift` proof skeleton appear in the error message.

`Examples/Feed.lean` uses both state and styling invariants over a list of cards.

## Styling invariants (over the view)

Everything above is a property of the **model**, preserved across a transition. A styling rule is a
property of the **rendered view, for every model**, a different shape, so the same `invariant`
command takes a different connective, `holds_in`, in place of `preserved_by`:

```lean
invariant statusStyled : roleHasOneOf "status" [onStyle, offStyle] holds_in view
```

This expands to `∀ m, roleHasOneOf "status" [onStyle, offStyle] (view m) = true`.
For every model, elements with the `status` role must have one of the two specified styles.
The predicate finds elements by their `role` attribute:

```lean
def view (m : Model) : Html Msg :=
  <div><button role="status" {if m.on then onStyle else offStyle}>…</button></div>
```

Ready predicates (all `Html msg → Bool`, all auto-discharging):

| Predicate | Reads as |
|---|---|
| `roleHasOneOf "x" [a, b]` | every element tagged `role "x"` carries style `a` or `b` |
| `tagHasOneOf "button" [a, b]` | every `<button>` carries style `a` or `b` (no marker needed) |
| `everyElement (fun tag attrs => …)` | a custom per-element rule |

**Relating two elements.** `roleHas "x" a` is the single-element query ("the `role "x"` element
carries `a`); `both`/`either` combine queries, and `exactlyOne` packages the common XOR:

```lean
invariant savedXorEditing : exactlyOne "save" "cancel" primary secondary holds_in view
-- ≡ either (both (roleHas "save" primary) (roleHas "cancel" secondary))
--          (both (roleHas "save" secondary) (roleHas "cancel" primary))
```

The automation supports positive "has style" facts: `both (roleHas …) (roleHas …)` for AND,
`either …` for OR, and `exactlyOne` for XOR. Class names are content hashes. A positive check
can reduce to `x == x`, but proving that two hashes differ needs additional reasoning.
Negative style claims are not handled automatically.

The discharger unfolds the view and the `Qed.Notation` combinators, splits the view's `if`/`match`,
and closes each leaf, a class check reduces by `x == x`, never by hashing the class name. A violated
rule fails to compile (unsolved goal), exactly like a model invariant; the `:= proof` escape is
there for a view it can't reduce, e.g. one routed through `App.view`/`View.render` rather than a
plain `Model → Html`. (So point `holds_in` at a named `def view`.)

## When it can't close it

A failure is reported as an unsolved goal **labelled with the message constructor that breaks the
property**, plus the obligation it left open:

```
unsolved goals
case increment
h : m.count ≤ 0
⊢ m.count + 1 ≤ 0
```

The remaining goal may require a fix to the transition, a correction to the stated condition,
or an additional proof step. An invariant that is always `True` does not check the intended
behavior.

## A menu of properties

Reach for these shapes first. Each is the kind of claim worth attaching to a state change.

| Shape | Example | Reads as |
|---|---|---|
| **Bound / non-negativity** | `0 ≤ m.count` | a quantity stays in range |
| **Precondition for a state** | `m.booked.isSome → m.today.isSome` | you can't reach X without having done Y |
| **Mutual exclusion** | `¬ (m.editing ∧ m.submitting)` | editing and submitting cannot both be true |
| **Effect safety** | `m.pending = true → 0 < m.turns.size` | the data an effect needs is present before it runs |
| **Freshness** | `∀ r ∈ m.rows, r.id < m.nextId` | the next id differs from every existing id; pairwise uniqueness is a separate property |
| **Derived-field consistency** | `m.total = (m.items.map (·.price)).sum` | a cached value matches its source |

The first four usually prove automatically. The last two quantify over a collection and typically
need a one- or two-line `:=` proof (`cases msg <;> simp_all [update] <;> omega`, plus the relevant
`Array`/`List` lemma).

## Not every state change needs one

Don't reach for an invariant where there is no honest claim to make. Common cases:

- **The condition is part of the type.** A form's `submitted : Option Account` is either `none`
  or `some account`. Each refined field in `Account` includes a proof that its value satisfies
  the field's rule, so a separate invariant for those same rules is unnecessary.
  (`Examples/Signup.lean`.)
- **The property is about runtime, not the model.** "Updating a bound value preserves its DOM
  node" is a fact about the driver, checked by browser tests, not a model invariant.
  See [rendering](rendering.md).
- **External data is arbitrary by type.** A `Resource` message can deliver any state, so a claim
  like "loading ⇒ on a detail route" isn't preserved without narrower message types, a redesign,
  not an invariant. (`Examples/Users.lean`, `Examples/Bookshelf.lean`.)

A real property can also be out of reach for a mechanical reason. Extending the template's
id-bound proof to `Examples/Todo.lean` would need to handle `.sort`, which uses `Array.qsort`.
The collection automation supports `Array.sortBy`; a `qsort` proof needs additional lemmas.

## Worked examples in this repo

- `Examples/Counter.lean`, `counterSafe`, a numeric bound, automatic.
- `Examples/Booking.lean`, `bookedNeedsToday`, an `Option` precondition over nested `match`es,
  automatic.
- `Examples/Template.lean`, `idsBelowNext`, fresh-id allocation (`∀ t ∈ todos, t.id < nextId`)
  over a list edited by `.map`/`.push`, with a `:=` proof. This bound alone does not prove
  existing ids are pairwise distinct.
- `Examples/Live.lean`, `nonNegative`, a bound preserved by handlers that read the live model,
  automatic.
- `Examples/Local.lean`, `stepperSafe`, a bound on a `component`-generated update (the `set` sites
  are the cases), automatic.
- `Examples/Socket.lean`, `composerOnlyWhenOnline` (`draft ≠ "" → conn = .online`), a precondition
  on an effectful state machine, automatic. The update logic clears a stale draft on disconnect.
- `Examples/Chat.lean`, `streamSafe`, an effect-safety property on an effectful `transition`,
  automatic (the discharger uses the helper and array-size facts).
- `Examples/Badge.lean`, both forms side by side: `levelSafe` (model, `preserved_by update`) and
  `statusStyled` (styling, `roleHasOneOf … holds_in view`).

See `Qed/Invariant.lean` for the command itself.
