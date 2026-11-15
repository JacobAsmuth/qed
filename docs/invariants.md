# Invariants

An invariant is a rule that must hold after every state update. When you declare one, Qed
asks Lean's kernel to prove that every message preserves the rule, assuming it held beforehand.
If the initial state also satisfies the rule, the rule holds for every state reachable through
`update`.

```lean
invariant counterSafe (m) : 0 ≤ m.count preserved_by update
```

This generates and checks the theorem `∀ m msg, 0 ≤ m.count → 0 ≤ (update m msg).count`. If Qed
cannot prove a branch, compilation fails and reports the exact message constructor and remaining
goal.

### Syntax quick reference

| What you want to check | Syntax |
|------------------------|--------|
| One pure `update` or `transition` | `invariant safe (m) : 0 ≤ m.count preserved_by update` |
| Initial state + `update` | `invariant safe (m) : 0 ≤ m.count from init preserved_by update` |
| An `App` (`app.init` + `app.update`) | `invariant safe (m) on counterApp : 0 ≤ m.count` |
| Multiple clauses (`∧`) | `invariant inRange (m) : 1 ≤ m.qty, m.qty ≤ 10 preserved_by update` |
| Inside a `component` block | `invariant 1 ≤ qty, qty ≤ 10` |
| Rendered HTML / styles | `invariant styled : roleHasOneOf "save" [on, off] holds_in view` |

Invariants check your Lean model and view functions; see [how Qed works](architecture.md) for
how those connect to the JavaScript runtime and browser.

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
invariant counterSafe (m) : 0 ≤ m.count preserved_by update
```

Effectful `transition` functions (`Model → Msg → Model × Cmd Msg`) and `App` values use the
exact same syntax—Qed automatically projects the next model out of `(model, cmd)`:

```lean
invariant streamSafe (m) on chatApp : m.pending = true → 0 < m.turns.size
```

**Custom proof (`:= by`).** When a property quantifies over a collection (`Array` or `List`) or
relies on a domain lemma that automation cannot guess, attach a Lean tactic proof with `:= by`.
The proof goal is the generated theorem, starting with `intro m msg h`:

```lean
invariant idsBelowNext (m) : ∀ r ∈ m.rows, r.id < m.nextId
    preserved_by update := by
  intro m msg h
  cases msg <;> simp_all [update] <;> omega
```

## Lifting invariants over child collections (`for_each`)

When a parent stores an array of child states (for example, `cards : Array Card.State`),
`for_each` lifts a child's invariant across every element in the parent's array:

```lean
abbrev Card.Safe (c : Card.State) : Prop :=
  0 ≤ c.likes ∧ c.progress ≤ c.duration ∧ (c.liked → 1 ≤ c.likes)

invariant cardSafe : Card.Safe preserved_by Card.update

invariant feedSafe : cardSafe for_each cards preserved_by update
-- Checks: ∀ m msg, (∀ c ∈ m.cards, Card.Safe c) → (∀ c ∈ (update m msg).cards, Card.Safe c)
```

Qed infers `Card.Safe` directly from `cardSafe` (or you can write the predicate explicitly as
`Card.Safe for_each cards preserved_by update using cardSafe`). Because `feedSafe` is itself a
`∀ c ∈ cards, …` theorem, `for_each` composes cleanly across nested collections (e.g., a shell
owning multiple feeds).

### Supported collection operations

- **Keyed child updates:** discharged automatically using `cardSafe`.
- **`Array.filter`:** preserved automatically since kept items were already valid.
- **Adding / pushing items:** Qed checks that the newly added item satisfies `Card.Safe`.
- **`Array.map`:** Qed checks that transforming a valid item produces a valid item.
- **`Array.sortBy`:** preserved automatically via its permutation membership lemma (`Array.qsort`
  is *not* handled automatically and requires a custom lemma).

If one branch uses an unsupported operation (such as `qsort` or concatenating unvalidated
data), Qed prints a proof skeleton using `forEachLift`, which closes all supported branches so
you only fill in the remaining case:

```lean
invariant feedSafe : Card.Safe for_each cards preserved_by update using cardSafe := by
  forEachLift update cardSafe Card.Safe
  case rank => … -- prove only the custom branch
```

### Lifting view rules (`for_each … holds_in`)

`for_each` also lifts styling invariants from a child view to a parent view:

```lean
invariant cardStyled : roleHasOneOf "like" [likeOn, likeOff] holds_in Card.view
invariant feedStyled : cardStyled for_each cards holds_in view
```

Qed applies `cardStyled` to each rendered card (invariant under `Html.map` message wrapping) and
checks the rest of the parent markup separately. If a branch needs manual help, the error
message provides a `forEachStyleLift` skeleton. See [`Examples/Feed.lean`](../Examples/Feed.lean)
for both state and styling lifts in action.

## Styling invariants (over the view)

While `preserved_by` checks state transitions, `holds_in` checks a property of the **rendered
HTML for every model**:

```lean
def view (m : Model) : Html Msg :=
  <div><button role="status" {if m.on then onStyle else offStyle}>…</button></div>

invariant statusStyled : roleHasOneOf "status" [onStyle, offStyle] holds_in view
-- Checks: ∀ m, roleHasOneOf "status" [onStyle, offStyle] (view m) = true
```

Point `holds_in` at a plain `Model → Html Msg` function (such as `def view`) so Qed can unfold
the markup, split `if`/`match` branches, and verify every leaf.

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
- [`Examples/Badge.lean`](../Examples/Badge.lean) — `levelSafe` (`preserved_by`) alongside
  `statusStyled` (`holds_in`).
- [`Examples/Template.lean`](../Examples/Template.lean) — `idsBelowNext`: custom `:= by` proof
  for fresh ID allocation over `.map` and `.push`.
- [`Examples/Feed.lean`](../Examples/Feed.lean) — `feedSafe` and `feedStyled`: `for_each` lifts
  for both state and styling across a card list.
