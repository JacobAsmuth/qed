# Invariants

An invariant is a rule that must hold in the initial state and after every state update. When you
declare one inside a `component`, Qed asks Lean's kernel to prove that the initial state satisfies
the rule (including for mountable components with `prop`s), that every message preserves it, and
that SSR `Dehydrate` preserves it (`dehydrate_inv`); at runtime, `App.guardRehydrate` rejects
untrusted rehydration payloads that violate the invariant (`rehydrate_inv`).

```lean
component Counter:
  state count : Int = 0
  invariant 0 <= count
  ...
```

If Qed cannot prove an initializer or handler branch, compilation fails and reports the exact
message constructor and remaining goal.

### Syntax quick reference

| What you want to check | Syntax (inside `component`) |
|------------------------|-----------------------------|
| Single state predicate | `invariant 0 <= count` |
| Named state predicate | `invariant counterSafe: 0 <= count` |
| Chained / multi-clause | `invariant inRange: 1 <= qty <= 10` (or `1 <= qty, qty <= 10`) |
| Quantified property | `invariant all r in rows: r.id < nextId` |
| Collection queries | `invariant rows.uniqueBy(r => r.id)` · `rows.sumBy(r => r.price) == total` · `rows.countWhere(r => r.done) == n` · `events.isSortedBy(e => e.ts)` |
| Lifted child invariant | `invariant feedSafe: Card.cardSafe for_each cards` |
| Component view / styles | `invariant roleHasOneOf("save", [on, off])` |
| Multiple view rules | `invariant roleLacks("submit", danger), tagLacks("span", danger)` |
| Pure helper view (`Html`) | `invariant styled : roleHasOneOf("nav", [a, b]) holds_in navView` (top-level) |

Invariants check your component's state transitions and rendered HTML; see
[how Qed works](architecture.md) for how those connect to the JavaScript runtime and browser.

## Why compile-time invariants help

Whenever you add a new action or edit an existing handler, every invariant on that model is
re-checked automatically. Because `component` compiles inline handlers (like `{count -= 1}`)
into named `Msg` constructors rather than anonymous closures, generated updates get the exact
same case-by-case error reporting as hand-written reducers:

```text
Invariant `Counter.counterSafe` failed in `Counter.update`:
  • handler updating `count` must satisfy:  0 <= count - 1
```

Running `qed check` (or `qed build`) reinforces these proofs by verifying the compiled
`Lean.Environment` (`Js/VerifyEnv.lean`) against Lean's standard axioms—rejecting `sorry`,
`admit`, `native_decide`, custom axioms, and `partial`/`unsafe` code. `qed check` also prints a
heuristic note if it spots stateful update functions without an `invariant`, though you only
need to add invariants where there is a meaningful rule to enforce.

## Automatic vs. custom proofs

**Automatic.** Most invariants prove themselves with no tactic script—including linear arithmetic (`omega`), common nonlinear monotonicity (`price * qty <= maxPrice * maxQty`, `total / k <= maxAvg`, ring identities), booleans, `Option`, `if`/`match`, quantified collection bounds (`all r in rows: r.id < nextId`), and Qed's verified collection queries (`sumBy`, `sumByInt`, `countWhere`, `uniqueBy`, `isSortedBy`) backed by Lean 4's `grind` solver:

```lean
component SmartLedger:
  state rows       : LineItem[] = []
  state nextId     : Nat = 0
  state totalCents : Nat = 0
  state doneCount  : Nat = 0

  invariant idsAndUnique:
    (all r in rows: r.id < nextId) and rows.uniqueBy(r => r.id)
  invariant totalSynced:
    rows.sumBy(r => r.price) == totalCents
  invariant doneSynced:
    rows.countWhere(r => r.done) == doneCount and doneCount <= rows.size
  ...
```

Both pure updates and effectful handlers (which return `(model, cmd)`) use the exact same
syntax—Qed automatically projects the next model out of `(model, cmd)`.

## Full-stack client–server invariants (`requires` & `ensures`)

When a client `component` invokes a `server` `def` via `await` or `query`, Qed connects server contracts and component invariants in both directions:

- **Client `invariant` -> Server `requires`:** Component `invariant`s (as well as literals, `if` / `if let` branches, `ensure` guards, and `Field`/`Ensured` values) are automatically available as hypotheses to discharge every server parameter `requires` clause at compile time.
- **Server `ensures` -> Client `invariant`:** Server postconditions (`ensures expr`) are encoded via zero-trust `Ensured α p` (`FromProto` re-verifies `p` on untrusted bytes) and automatically unpacked into continuation hypotheses across `let x = await Server.fn(...) catch: ...` and `Cached.all` invariants on reactive `query` fields (see [`Examples/CloudBooks.lean`](../Examples/CloudBooks.lean) and [`Tests/ServerChecks.lean`](../Tests/ServerChecks.lean)).

**Custom proof (`using [lemma]` or `:= by`).** When a property depends on a custom recursive domain function or an unverified helper that automation cannot guess, pass a lemma with `using [myLemma]` or attach a Lean tactic proof with `:= by`. Inside a `component`, `init` is discharged automatically and `update` is in scope, so the proof handles preservation starting with `intro m msg h`:

```lean
invariant customGraphAcyclic: isAcyclic(nodes) := by
  intro m msg h
  cases msg <;> simp_all [update, isAcyclic_addEdge]
```

## Lifting invariants over child collections (`for_each`)

When a parent `collection` stores an array of child states (or a field holds `Card.State[]`),
`for_each` lifts a child's invariant across every element in the parent's array:

```lean
component Card:
  state likes : Int = 0
  state duration : Int = 10
  state progress : Int = 0
  state liked : Bool = false
  invariant cardSafe:
    0 <= likes and progress <= duration and (liked -> 1 <= likes)
  ...

component Feed:
  state cards : Card.State[]
  invariant feedSafe: Card.cardSafe for_each cards
  -- Checks both init and that every update preserves (∀ c ∈ cards, Card.cardSafe_pred c)
```

Qed infers the child predicate directly from `Card.cardSafe` (or you can write an explicit
predicate `Pred for_each cards using Card.cardSafe`). Because `feedSafe` is itself a
`∀ c ∈ cards, …` theorem, `for_each` composes cleanly across nested collections (e.g., a shell
owning multiple feeds).

### Supported collection operations

- **Keyed child updates:** discharged automatically using `Card.cardSafe`.
- **Element-preserving rearrangements & subsets:** `filter`, `sortBy` (verified `mergeSort`; `Array.qsort` has no membership lemma), `pop`, `reverse`, `extract`, `eraseIdx` / `eraseIdxIfInBounds`, and `swap` / `swapIfInBounds` lift automatically.
- **Adding, replacing & transforming items:** `push`, `set` / `setIfInBounds`, `append` (`++`), `map`, and `modify` check that the new or transformed element satisfies the child predicate (using `omega`, `simp_all`, nonlinear closers, and `grind`).

If one branch uses an unsupported operation (such as `qsort` or concatenating unvalidated
data), Qed prints a proof skeleton using `forEachLift`, which closes all supported branches so
you only fill in the remaining case:

```lean
invariant feedSafe: Card.cardSafe_pred for_each cards using Card.cardSafe := by
  forEachLift update Card.cardSafe Card.cardSafe_pred
  case rank => … -- prove only the custom branch
```

### Lifting view rules (`for_each`)

`for_each` also lifts styling invariants from a child component to a parent component:

```lean
-- Inside Card:
invariant cardStyled: roleHasOneOf("like", [likeOn, likeOff])

-- Inside Feed:
invariant feedStyled: Card.cardStyled for_each cards
```

Qed applies `Card.cardStyled` to each rendered card (invariant under `Html.map` message wrapping) and
checks the rest of the parent markup separately. If a branch needs manual help, the error message provides a `forEachStyleLift` skeleton
(see [`Examples/Todo.lean`](../Examples/Todo.lean) for both state and styling lifts in action).

## Styling invariants (over the view)

You can declare a view/styling `invariant` directly inside a `component` (like
`invariant statusStyled: roleHasOneOf("status", [onStyle, offStyle])`), or use `holds_in` at top
level for pure `Html` helper functions (`Model → Html Msg`):

```lean
def navView (active : Route) : Html Msg :=
  <div><a href={Route.home} {activeStyle if active == .home else linkStyle}>Home</a></div>

invariant navStyled : everyElement(…) holds_in navView
```

### Built-in view predicates

| Predicate | Meaning |
|-----------|---------|
| `roleHasOneOf("x", [a, b])` | Every element with `role="x"` has style `a` or style `b`. |
| `tagHasOneOf("button", [a, b])` | Every `<button>` has style `a` or style `b` (no `role` attribute needed). |
| `roleLacks("x", a)` | No element with `role="x"` carries style `a`. |
| `tagLacks("button", a)` | No `<button>` carries style `a` (no `role` attribute needed). |
| `everyElement((tag, attrs) => …)` | Custom boolean check applied to every element in the tree. |

### Relating multiple elements

Use `roleHas("x", a)` to check a single role, list multiple rules separated by commas (automatically combined with `both`), combine queries with `both` (AND) or `either` (OR), or use `exactlyOne` / `exactlyOneOf` for mutual exclusion (XOR):

```lean
invariant savedXorEditing: exactlyOne("save", "cancel", primary, secondary) holds_in view
-- Equivalent to:
--   either(both(roleHas("save", primary), roleHas("cancel", secondary)),
--          both(roleHas("save", secondary), roleHas("cancel", primary)))
```

Style class names use a pure kernel-reducible UTF-8 FNV-1a hash (`cssHash`), so both positive
checks (`roleHas`, `roleHasOneOf`) and negative checks (`roleLacks`, `tagLacks` — "this element does
*not* carry style `b`") reduce directly inside Lean's kernel for distinct concrete styles. Prefer
`roleHasOneOf` or `exactlyOne` when expressing positive exclusive choices.

## Reading a failed proof

When an invariant fails, Lean reports an unsolved goal labeled with the offending message case:

```text
unsolved goals
case increment
h : m.count ≤ 0
⊢ m.count + 1 ≤ 0
```

From here, one of three things is true:

1. **The handler has a bug** (for example, a missing `if` guard or state reset).
2. **The invariant is too strong or imprecise** (make sure it isn't trivially `True`, either).
3. **Automation needs a hint** (add `:= by` to supply a collection or domain lemma).

## Common invariant patterns

| Pattern | Example | Meaning |
|---------|---------|---------|
| **Bounds** | `0 <= count` or `1 <= qty <= 10` | A counter or quantity stays in range. |
| **State precondition** | `booked.isSome -> today.isSome` | State X cannot be reached without Y. |
| **Mutual exclusion** | `not (editing and submitting)` | Two modes are never active at once. |
| **Effect precondition** | `pending -> 0 < turns.size` | Data needed by an in-flight effect is present. |
| **Fresh IDs** | `all r in rows: r.id < nextId` | Next ID exceeds all existing IDs (distinctness is separate). |
| **Cached totals** | `total == (items.map(i => i.price)).sum` | Derived field stays in sync with its source list. |

The first four usually prove automatically. The last two quantify over collections and
typically take a two-line `:= by` proof (`cases msg <;> simp_all [update] <;> omega` plus a
list/array lemma).

## When you don't need an invariant

Skip invariants when the guarantee already lives somewhere better:

- **Already encoded in the type:** In [`Examples/Signup.lean`](../Examples/Signup.lean),
  `submitted : Account?` holds a schema-validated `Account` whose fields already carry
  refinement proofs. Re-stating those field rules as a model invariant is redundant.
- **Framework/driver guarantees:** Properties like "updating a bound value preserves DOM node
  identity" belong to Qed's driver proofs and browser tests (see [rendering](rendering.md)),
  not app models.
- **Unconstrained external messages:** If a message constructor carries arbitrary external data,
  no transition proof can restrict what arrives unless you narrow the message or model types
  first (as in [`Examples/Bookshelf.lean`](../Examples/Bookshelf.lean)).

## Worked examples in this repo

- [`Examples/Counter.lean`](../Examples/Counter.lean) — `counterSafe`: automatic numeric bound (`0 <= count`).
- [`Examples/Todo.lean`](../Examples/Todo.lean) — `Row.rowSafe`, `Row.rowStyled`, `rowsSafe`, and
  `rowsStyled`: `for_each` lifts for both state and scoped CSS styling across a `collection`.
- [`Examples/Chat.lean`](../Examples/Chat.lean) — `streamSafe`: automatic effect-safety invariant
  (`pending -> 0 < turns.size`) on a streaming SSE action.
- [`Examples/CloudBooks.lean`](../Examples/CloudBooks.lean) — server state, monotonicity, and auth
  invariants paired with RPC `requires`/`ensures` contracts and client `orderedMatchesSlot`.
