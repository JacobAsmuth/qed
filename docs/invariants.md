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

See `Qed/Invariant.lean` for the command itself.
