# Invariants

An invariant is a rule that must hold in the initial state and after every state update. When you
declare one inside a `component`, Qed asks Lean's kernel to prove both that the initial state
satisfies the rule and that every message preserves it, assuming it held beforehand.

```lean
component Counter where
  state count : Int := 0
  invariant 0 ≤ count
  ...
```

If Qed cannot prove an initializer or handler branch, compilation fails and reports the exact
message constructor and remaining goal.

### Syntax quick reference

| What you want to check | Syntax (inside `component`) |
|------------------------|-----------------------------|
| Single state predicate | `invariant 0 ≤ count` |
| Named state predicate | `invariant counterSafe : 0 ≤ count` |
| Multiple clauses (`∧`) | `invariant inRange : 1 ≤ qty, qty ≤ 10` |
| Custom tactic proof | `invariant idsBelowNext : ∀ r ∈ rows, r.id < nextId := by ...` |
| Lifted child invariant | `invariant feedSafe : Card.cardSafe for_each cards` |
| Component view / styles | `invariant roleHasOneOf "save" [on, off]` |
| Pure helper view (`Html`) | `invariant styled : roleHasOneOf "nav" [a, b] holds_in navView` (top-level) |

Invariants check your component's state transitions and rendered HTML; see
[how Qed works](architecture.md) for how those connect to the JavaScript runtime and browser.

## Why compile-time invariants help

Whenever you add a new action or edit an existing handler, every invariant on that model is
re-checked automatically. Because `component` compiles inline handlers (like `{count -= 1}`)
into named `Msg` constructors rather than anonymous closures, generated updates get the exact
same case-by-case error reporting as hand-written reducers:

```text
case `set_count_2` still needs: 0 ≤ m.count - 1
```

Running `qed check` (or `qed build`) reinforces these proofs by verifying the compiled
`Lean.Environment` (`Js/VerifyEnv.lean`) against Lean's standard axioms—rejecting `sorry`,
`admit`, `native_decide`, custom axioms, and `partial`/`unsafe` code. `qed check` also prints a
heuristic note if it spots stateful update functions without an `invariant`, though you only
need to add invariants where there is a meaningful rule to enforce.

## Automatic vs. custom proofs

**Automatic.** Most arithmetic (`omega`), boolean, `Option`, and `if`/`match` properties prove
themselves with no tactic script:

```lean
component Counter where
  state count : Int := 0
  invariant counterSafe : 0 ≤ count
  ...
```

Both pure updates and effectful handlers (which return `(model, cmd)`) use the exact same
syntax—Qed automatically projects the next model out of `(model, cmd)`.

**Custom proof (`:= by`).** When a property quantifies over a collection (`Array` or `List`) or
relies on a domain lemma that automation cannot guess, attach a Lean tactic proof with `:= by`.
Inside a `component`, `init` is discharged automatically and `update` is in scope, so the proof
handles preservation starting with `intro m msg h`:

```lean
invariant idsBelowNext : ∀ r ∈ rows, r.id < nextId := by
  intro m msg h
  cases msg <;> simp_all [update] <;> omega
```

## Lifting invariants over child collections (`for_each`)

When a parent `collection` stores an array of child states (or a field holds `Array Card.State`),
`for_each` lifts a child's invariant across every element in the parent's array:

```lean
component Card where
  state likes : Int := 0
  state duration : Int := 10
  state progress : Int := 0
  state liked : Bool := false
  invariant cardSafe :
    0 ≤ likes ∧ progress ≤ duration ∧ (liked = true → 1 ≤ likes)
  ...

component Feed where
  collection cards : Array Card.State := #[]
  invariant feedSafe : Card.cardSafe for_each cards
  -- Checks both init and that every update preserves (∀ c ∈ cards, Card.cardSafe_pred c)
```

Qed infers the child predicate directly from `Card.cardSafe` (or you can write an explicit
predicate `Pred for_each cards using Card.cardSafe`). Because `feedSafe` is itself a
`∀ c ∈ cards, …` theorem, `for_each` composes cleanly across nested collections (e.g., a shell
owning multiple feeds).

### Supported collection operations

- **Keyed child updates:** discharged automatically using `Card.cardSafe`.
- **`Array.filter`:** preserved automatically since kept items were already valid.
- **Adding / pushing items:** Qed checks that the newly added item satisfies the child predicate.
- **`Array.map`:** Qed checks that transforming a valid item produces a valid item.
- **`Array.sortBy`:** preserved automatically via its permutation membership lemma (`Array.qsort`
  is *not* handled automatically and requires a custom lemma).

If one branch uses an unsupported operation (such as `qsort` or concatenating unvalidated
data), Qed prints a proof skeleton using `forEachLift`, which closes all supported branches so
you only fill in the remaining case:

```lean
invariant feedSafe : Card.cardSafe_pred for_each cards using Card.cardSafe := by
  forEachLift update Card.cardSafe Card.cardSafe_pred
  case rank => … -- prove only the custom branch
```

### Lifting view rules (`for_each`)

`for_each` also lifts styling invariants from a child component to a parent component:

```lean
-- Inside Card:
invariant cardStyled : roleHasOneOf "like" [likeOn, likeOff]

-- Inside Feed:
invariant feedStyled : Card.cardStyled for_each cards
```

Qed applies `Card.cardStyled` to each rendered card (invariant under `Html.map` message wrapping) and
checks the rest of the parent markup separately. If a branch needs manual help, the error message provides a `forEachStyleLift` skeleton
(see [`Examples/Feed.lean`](../Examples/Feed.lean) for both state and styling lifts in action).

## Styling invariants (over the view)

You can declare a view/styling `invariant` directly inside a `component` (like
`invariant statusStyled : roleHasOneOf "status" [onStyle, offStyle]`), or use `holds_in` at top
level for pure `Html` helper functions (`Model → Html Msg`):

```lean
def navView (active : Route) : Html Msg :=
  <div><a href="/home" {if active == .home then activeStyle else linkStyle}>Home</a></div>

invariant navStyled : everyElement … holds_in navView
```

### Built-in view predicates

| Predicate | Meaning |
|-----------|---------|
| `roleHasOneOf "x" [a, b]` | Every element with `role="x"` has style `a` or style `b`. |
| `tagHasOneOf "button" [a, b]` | Every `<button>` has style `a` or style `b` (no `role` attribute needed). |
| `everyElement (fun tag attrs => …)` | Custom boolean check applied to every element in the tree. |

### Relating multiple elements

Use `roleHas "x" a` to check a single role, combine queries with `both` (AND) or `either` (OR),
or use `exactlyOne` for mutual exclusion (XOR):

```lean
invariant savedXorEditing : exactlyOne "save" "cancel" primary secondary holds_in view
-- Equivalent to:
--   either (both (roleHas "save" primary) (roleHas "cancel" secondary))
--          (both (roleHas "save" secondary) (roleHas "cancel" primary))
```

Style class names are content hashes, so positive checks ("this element carries style `a`")
reduce cleanly by reflexivity (`x == x`). Proving *negative* claims ("this element does *not*
carry style `b`") requires showing two hashes differ and is not discharged automatically—prefer
positive alternatives like `roleHasOneOf` or `exactlyOne`.

## Reading a failed proof

When an invariant fails, Lean reports an unsolved goal labeled with the offending message case:

```text
unsolved goals
case increment
h : m.count ≤ 0
⊢ m.count + 1 ≤ 0
```

From here, one of three things is true:

1. **The handler has a bug** (for example, a missing `when` guard or state reset).
2. **The invariant is too strong or imprecise** (make sure it isn't trivially `True`, either).
3. **Automation needs a hint** (add `:= by` to supply a collection or domain lemma).

## Common invariant patterns

| Pattern | Example | Meaning |
|---------|---------|---------|
| **Bounds** | `0 ≤ m.count` | A counter or quantity stays in range. |
| **State precondition** | `m.booked.isSome → m.today.isSome` | State X cannot be reached without Y. |
| **Mutual exclusion** | `¬ (m.editing ∧ m.submitting)` | Two modes are never active at once. |
| **Effect precondition** | `m.pending = true → 0 < m.turns.size` | Data needed by an in-flight effect is present. |
| **Fresh IDs** | `∀ r ∈ m.rows, r.id < m.nextId` | Next ID exceeds all existing IDs (distinctness is separate). |
| **Cached totals** | `m.total = (m.items.map (·.price)).sum` | Derived field stays in sync with its source list. |

The first four usually prove automatically. The last two quantify over collections and
typically take a two-line `:= by` proof (`cases msg <;> simp_all [update] <;> omega` plus a
list/array lemma).

## When you don't need an invariant

Skip invariants when the guarantee already lives somewhere better:

- **Already encoded in the type:** In [`Examples/Signup.lean`](../Examples/Signup.lean),
  `submitted : Option Account` holds a schema-validated `Account` whose fields already carry
  refinement proofs. Re-stating those field rules as a model invariant is redundant.
- **Framework/driver guarantees:** Properties like "updating a bound value preserves DOM node
  identity" belong to Qed's driver proofs and browser tests (see [rendering](rendering.md)),
  not app models.
- **Unconstrained external messages:** If a message constructor carries arbitrary external data,
  no transition proof can restrict what arrives unless you narrow the message or model types
  first (as in [`Examples/Users.lean`](../Examples/Users.lean) and
  [`Examples/Bookshelf.lean`](../Examples/Bookshelf.lean)).

## Worked examples in this repo

- [`Examples/Counter.lean`](../Examples/Counter.lean) — `counterSafe`: automatic numeric bound.
- [`Examples/Booking.lean`](../Examples/Booking.lean) — `bookedNeedsToday`: automatic `Option`
  precondition across nested `match` branches.
- [`Examples/Live.lean`](../Examples/Live.lean) — `nonNegative`: automatic bound with handlers
  that read live model values.
- [`Examples/Local.lean`](../Examples/Local.lean) — `stepperSafe`: automatic bound over
  `component`-generated actions.
- [`Examples/Socket.lean`](../Examples/Socket.lean) — `composerOnlyWhenOnline`
  (`draft ≠ "" → conn = .online`): automatic state-machine precondition where disconnect clears
  stale drafts.
- [`Examples/Chat.lean`](../Examples/Chat.lean) — `streamSafe`: automatic effect-safety invariant
  on a streaming `transition`.
- [`Examples/Badge.lean`](../Examples/Badge.lean) — `levelSafe` alongside
  `statusStyled`.
- [`Examples/Template.lean`](../Examples/Template.lean) — `idsBelowNext`: custom `:= by` proof
  for fresh ID allocation over `.map` and `.push`.
- [`Examples/Feed.lean`](../Examples/Feed.lean) — `feedSafe` and `feedStyled`: `for_each` lifts
  for both state and styling across a card list.
