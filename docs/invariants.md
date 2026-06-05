# Invariants

An invariant is a fact about your model that you want to hold no matter what the user does.
You state it once; the framework proves it holds after *every* message, for *every* reachable
state — not the cases a test happened to cover. The proof is checked by Lean's kernel, so a
passing build is not "the tests are green," it is "this cannot happen."

```lean
invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update
```

This expands to a theorem — `∀ m msg, 0 ≤ m.count → 0 ≤ (update m msg).count` — and discharges
it automatically. If the property does not actually hold, the build fails; it is never quietly
accepted (no `sorry`, no skipped case).

## Why this matters for generated code

Code is cheap to produce and expensive to trust. Tests are partial and can be gamed; types rule
out "not a function," not "the total went negative." An invariant is the missing third signal:
it is **total** (covers every input and message sequence) and **un-gameable** (the kernel either
has a proof or it doesn't — and `qed check` rejects `sorry` and any axiom off the standard
whitelist, so a pass can't be faked). The claim is small and human-readable; the proof that the
code obeys it is the machine's job. Reviewing a three-line property is tractable in a way that
re-reading two hundred lines of `update` is not.

`qed check` reports every `update`/`transition` that changes state without an attached invariant,
so the gaps are visible. If you (or an agent) are changing the state of the program, you can
almost always make *some* claim about it.

## The two forms

**Automatic.** State the property; the discharger handles it. It covers arithmetic (`omega`),
boolean/`Option` reasoning, `if`/`match` splits, and the `still`/`also` effect wrappers.

```lean
invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update
```

**Effectful transitions** work with the same syntax — the next model is read out of the
`Model × Cmd Msg` a `transition` returns:

```lean
invariant streamSafe : (fun m => m.pending = true → 0 < m.turns.size) preserved_by transition
```

**With a proof (`:=`).** When the property needs a lemma the automation can't guess — usually one
quantified over your own collections — supply the proof. The goal is the generated theorem, so it
opens with `intro m msg h`:

```lean
invariant idsBelowNext : (fun m => ∀ r ∈ m.rows, r.id < m.nextId)
    preserved_by update := by
  intro m msg h
  cases msg <;> simp_all [update] <;> omega
```

## Lifting a contract over a list of children (`for_each`)

A reusable `Component` embedded with `embed` lives as a keyed array in the parent's model, and its
contract is a fact about *one* child. `for_each` lifts that to **every child in the list, across the
parent's own transition** — in one line, no proof:

```lean
abbrev Card.Safe (c : Card.Model) : Prop :=                 -- the child's contract, written once
  0 ≤ c.likes ∧ c.progress ≤ c.duration ∧ (c.liked → 1 ≤ c.likes)
invariant cardSafe : Card.Safe preserved_by Card.update     -- the card never breaks it

embed Card as card keyedBy (toString ·.id) into cards
def update : Model → Msg → Model | ...                      -- tap / re-rank / dismiss / add

invariant feedSafe : Card.Safe for_each cards preserved_by update using cardSafe
-- ⇒ machine-checks: ∀ m msg, (∀ c ∈ m.cards, Card.Safe c) → (∀ c ∈ (update m msg).cards, Card.Safe c)
```

The discharger *applies* a proven lemma per list operation — a keyed child message keeps it (that's
the child contract, named in `using`), `filter`/remove keeps it, `push`/add keeps it once the new
element is valid by construction, and **a re-rank keeps it if you sort with `Array.sortBy`** (a
verified `mergeSort` — `Array.qsort` has no membership lemma, so it can't be lifted automatically).

Because `feedSafe` is itself a `∀ c ∈ cards, …` fact, it composes: a grandparent that owns several
feeds lifts it again, one line up — `invariant shellSafe : feedSafe for_each feeds preserved_by update
using feedSafe`. Lifts track where your data model nests collections, not render depth.

**When an arm can't be lifted** (a `qsort`, a raw `++` of unvalidated data, an `add` whose element
isn't provably valid), the error names that arm, says which operation blocked it, and hands a
paste-able skeleton. `forEachLift` is the discharger as a tactic, so you finish only the one arm:

```lean
invariant feedSafe : Card.Safe for_each cards preserved_by update using cardSafe := by
  forEachLift update cardSafe Card.Safe     -- closes every arm it can; `m`/`h` are in scope
  case rank => …                            -- fill only what's left
```

The **styling** analogue is the same line with a different connective — lift a card's `holds_in`
contract to "the whole rendered view is styled, chrome and every card":

```lean
invariant cardStyled : roleHasOneOf "like" [Card.likeOn, Card.likeOff] holds_in Card.view
invariant feedStyled : roleHasOneOf "like" [Card.likeOn, Card.likeOff]
                         for_each cards holds_in view using cardStyled
-- ⇒ machine-checks: ∀ m, roleHasOneOf "like" […] (view m) = true   (the same theorem `holds_in` gives)
```

A plain `holds_in view` can't auto-discharge this — it walks into the dynamic `cards.map cardView`
list and stops. `for_each cards … using cardStyled` is exactly the missing information (which list,
which child contract): the discharger reduces the view to its chrome plus that list (a styled child
view stays styled after `embed`'s message-relabel — `roleHasOneOf_map`) and closes each card with
`cardStyled`. If the parent view has its *own* element with that role, or its shape is unusual, the
error names what's left and hands a `forEachStyleLift` skeleton — same bargain as the behavioural side.

`Examples/Feed.lean` is a TikTok-style feed that puts both lifts together end to end.

## Styling invariants (over the view)

Everything above is a property of the **model**, preserved across a transition. A styling rule is a
property of the **rendered view, for every model** — a different shape — so the same `invariant`
command takes a different connective, `holds_in`, in place of `preserved_by`:

```lean
invariant statusStyled : roleHasOneOf "status" [onStyle, offStyle] holds_in view
```

expands to a machine-checked `∀ m, roleHasOneOf "status" [onStyle, offStyle] (view m) = true` — the
status badge is shown in one of two known visual states in *every* reachable state, not the ones a
test happened to render. Tag the element with the `role` attribute and the predicate finds it:

```lean
def view (m : Model) : Html Msg :=
  div [] [ button [ role "status", if m.on then onStyle else offStyle ] [ text "…" ] ]
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

State these over *positive* "has style" facts — `both (roleHas …) (roleHas …)` for AND,
`either …` for OR, `exactlyOne` (or an `either`-of-`both`s) for XOR. That's a real constraint:
a class name is a content **hash**, so "this element does *not* have style Y" isn't provable (two
hashes can't be shown distinct), but "this element *has* style X" is (`x == x`). Phrase the rule
positively and it proves; reach for a negation and it won't (by design, not by accident).

The discharger unfolds the view and the `Qed.Notation` combinators, splits the view's `if`/`match`,
and closes each leaf — a class check reduces by `x == x`, never by hashing the class name. A violated
rule fails to compile (unsolved goal), exactly like a model invariant; the `:= proof` escape is
there for a view it can't reduce — e.g. one routed through `App.view`/`View.render` rather than a
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

That is the signal to act on: either fix the transition so the claim holds, or weaken the claim to
what the code actually guarantees. Don't reach for a vacuous claim to make it pass — an invariant
that's secretly `True` proves nothing and is worse than none, because it reads as a guarantee.

## A menu of properties

Reach for these shapes first. Each is the kind of claim worth attaching to a state change.

| Shape | Example | Reads as |
|---|---|---|
| **Bound / non-negativity** | `0 ≤ m.count` | a quantity stays in range |
| **Precondition for a state** | `m.booked.isSome → m.today.isSome` | you can't reach X without having done Y |
| **Mutual exclusion** | `¬ (m.editing ∧ m.submitting)` | two states never hold at once |
| **Effect safety** | `m.pending = true → 0 < m.turns.size` | the data an effect needs is present before it runs |
| **Freshness / unique keys** | `∀ r ∈ m.rows, r.id < m.nextId` | every allocated id is below the counter (so keys don't collide) |
| **Derived-field consistency** | `m.total = (m.items.map (·.price)).sum` | a cached value matches its source |

The first four usually prove automatically. The last two quantify over a collection and typically
need a one- or two-line `:=` proof (`cases msg <;> simp_all [update] <;> omega`, plus the relevant
`Array`/`List` lemma).

## Not every state change needs one

Don't reach for an invariant where there is no honest claim to make. Common cases:

- **The type already proves it.** A form's `submitted : Option Account` can only hold a *valid*
  `Account` because each field is proof-carrying (`canSubmit_iff`). An `invariant` restating that
  would be vacuous — the guarantee is the type. (`Examples/Signup.lean`.)
- **The property is about runtime, not the model.** "Setting a signal doesn't re-render" is a
  fact about the driver, checked by a browser test, not a model invariant. (`Examples/Signals.lean`.)
- **External data is arbitrary by type.** A `Resource` message can deliver any state, so a claim
  like "loading ⇒ on a detail route" isn't preserved without narrower message types — a redesign,
  not an invariant. (`Examples/Users.lean`, `Examples/Bookshelf.lean`.)

A real property can also be out of reach for a mechanical reason — `Examples/Todo.lean` has the
same id-uniqueness property as the template below, but its `.sort` reorders with `Array.qsort`,
and the standard library carries no lemma that `qsort` preserves membership, so the proof would
have to establish that first.

## Worked examples in this repo

- `Examples/Counter.lean` — `counterSafe`, a numeric bound, automatic.
- `Examples/Booking.lean` — `bookedNeedsToday`, an `Option` precondition over nested `match`es,
  automatic.
- `Examples/Template.lean` — `idsBelowNext`, unique keys (`∀ t ∈ todos, t.id < nextId`) over a
  list edited by `.map`/`.push`, with a `:=` proof — this is what makes the keyed diff sound.
- `Examples/Live.lean` — `nonNegative`, a bound preserved by handlers that read the live model,
  automatic.
- `Examples/Socket.lean` — `composerOnlyWhenOnline` (`draft ≠ "" → conn = .online`), a precondition
  on an effectful state machine, automatic — the guards that make it hold also clear a stale draft
  on disconnect.
- `Examples/Chat.lean` — `streamSafe`, an effect-safety property on an effectful `transition`,
  with a `:=` proof (it needs the fact that `appendLast` preserves the turn count).
- `Examples/Badge.lean` — both forms side by side: `levelSafe` (model, `preserved_by update`) and
  `statusStyled` (styling, `roleHasOneOf … holds_in view`).

See `Qed/Invariant.lean` for the command itself.
