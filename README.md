# Qed

**A formally verified web frontend framework in Lean 4.**

Frontend bugs are where the ones you ship actually live. The missing case in a reducer. The render
that throws on an empty list. The "this can't happen" that happens in production. Every framework
asks you to trust your code is right, and hands you a type checker and a test suite to hope along
with you.

Qed makes a different bet. You write your app in [Lean](https://lean-lang.org), a proof assistant.
The same kernel mathematicians use to check proofs checks your frontend.

`qed build` transpiles your app and the whole verified framework straight to plain JavaScript. No
emscripten, no WASM, no special runtime. The output is a handful of `.mjs` files you serve anywhere.
The proofs that pass `qed check` describe the JavaScript that actually runs. If you've written Elm,
the structure will feel familiar.

```bash
curl -sSfL https://raw.githubusercontent.com/JacobAsmuth/qed/main/install.sh | sh
qed new myapp && cd myapp && qed dev      # → http://localhost:8000, live-reloading
```

## A proof assistant, in my frontend?

Two guarantees fall out before you write a single proof.

**Your `update` and `view` can't crash.** In Lean they're ordinary total functions. A missing case
in a `match`, or a render that might not terminate, isn't a warning you can mute. It's a build
error. The broken code never reaches a user, because it never reaches `dist/`.

**You can state a fact about your app and let the kernel prove it.** This is the part with no
analogue in a normal framework. Here's a counter with an invariant that its count is never negative.

```lean
structure Model where
  count : Int
deriving Repr, Inhabited

inductive Msg | increment | decrement | reset

def init : Model := { count := 0 }

def update (m : Model) : Msg → Model
  | .increment => { m with count := m.count + 1 }
  | .decrement => { m with count := if 0 < m.count then m.count - 1 else m.count }
  | .reset     => { m with count := 0 }

def app : App Model Msg := ui init update fun m =>
  div [cls "counter"] [
    button [onClick .decrement] "−",
    span   [cls "count"]        [text (toString m.count)],
    button [onClick .increment] "+",
    button [onClick .reset]     "reset"
  ]

invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update
```

That last line isn't a test, and you don't write its proof. `invariant` discharges it for you. It
checks that every message leaves the count non-negative, and the build succeeds only if that holds
for all of them. Delete the `if 0 < m.count` guard and the build fails. The error names the message
that broke the promise (`case decrement`). The same syntax covers effectful transitions, and a `:=`
clause lets you hand over a proof for the rare claim the automation can't close.

What's worth stating? Bounds, preconditions, mutual exclusion, effect safety, unique keys. See
[`docs/invariants.md`](docs/invariants.md) for more. An auto-checked invariant is a property that
can't quietly be violated. It's the "this can't happen" finally made true.

## One way to write a view

You write the view the plain way. `if`, `.map`, string interpolation, your own helpers. No `memo`,
no `key`s, no `signal`s, no `useState` to place. The framework decides, per subtree, how to apply
each change. A model value that changed is written straight at its node. A change of shape (rows
added, removed, reordered, a branch flipped) reconciles through the diff. Change the counter and
that one text node is rewritten. Nothing else.

The proof is what makes deciding for you safe. The value-update path is proven to produce the same
DOM as a full re-render, and the diff is proven correct. The cheap update can never drift from
re-rendering everything. The stale row or dropped update that a missing `key` or a misplaced `memo`
causes elsewhere isn't something you can hit here.

## Is the thing that runs the thing you proved?

A verified framework is worthless if the bytes in the browser aren't the bytes you proved things
about. Every "verified" claim has to answer this. Qed's answer: there is no hand-written runtime to
diverge from the proofs. `qed build` runs the Lean compiler's IR through a transpiler (`qedjs`) that
emits JavaScript for your app, the whole framework, and the driver that runs them.

```text
Lean app (Model, Msg, update, view, deriving/invariant; proofs auto-discharged)
   │  lake build              (the kernel checks every proof)
   ▼
qedjs  (transpiles the Lean to JavaScript: your app + the Qed framework + the driver)
   ▼
dist/app.mjs  +  runtime/qed_rt.mjs   (a small library of the Lean primitives it uses)
   ▼
runtime/qed_dom.mjs + qed_host.mjs    (the only hand-written JS: the DOM calls and the
                  event wiring; everything else is your verified Lean, as JavaScript)
```

The only JavaScript a human wrote is the thin boundary at the bottom: the actual DOM calls and event
delegation. Everything above it is verified Lean. `test/js_gate_test.mjs` runs the same probes
through native Lean and through the transpiled JS and asserts they compute exactly the same thing:
render, diff, arithmetic, JSON, routing.

## The rest of the app is data, too

The counter is the whole architecture in miniature. A real app reads JSON, validates forms, routes,
talks to a server, and keeps lists. Qed treats each the same way: push the thing that can fail into
a value the type system can see, so the failure becomes a case you handle instead of an exception
you forgot.

### JSON

`Json.parse` is a total function. Bad input comes back as an `.error` value, never an exception. It
takes a depth budget (64 by default), and a proof guarantees whatever it returns nests no deeper
than the number you gave it. A deeply nested payload can't push past your limit. `jsonStruct` writes
the structure, its `ToJson`/`FromJson`, and a `decode` that parses and decodes in one call,
recursively through nested structs:

```lean
jsonStruct User where
  name    : String
  age     : Nat              -- a Nat can't be negative: "age": -3 → .error "age: expected a non-negative integer"
  bio     : Option String    -- Option ⇒ may be missing or null, comes back `none`

#eval (User.decode body (maxDepth := 8)).map (·.name)    -- Except.ok "Ada"
#eval (User.decode body (maxDepth := 1)).map (·.name)    -- Except.error "maximum depth exceeded"
```

### Forms

A `Field p` is a value carrying a proof that the predicate `p` holds of it. The only way to build one
is to pass validation. By the time you're holding a `Signup`, every field in it is already valid, and
an invalid form is not a thing you can construct. You write the predicates as ordinary `Prop`s, and
the `form` command does the rest, including a proof that the submit gate matches the validity it
claims to enforce:

```lean
abbrev Email (s : String) : Prop := s.contains '@' ∧ s.length ≥ 3
abbrev Adult (n : Nat)    : Prop := n ≥ 18

form Signup where
  email : Input.text.refine Email
  age   : Input.nat.refine Adult                   -- parsed to a Nat first, then checked
  agree : Input.checkbox.refine (· = true)
  plan  : Input.select [("free", "Free"), ("pro", "Pro")]
```

`Signup.formView draft .edit .submit` renders the inputs and a submit button that stays disabled
until every field checks out. It marks a field `aria-invalid` once you've touched it and it still
doesn't validate.

### Routing and HTTP

`router` declares your pages and gives you a `Router` whose round-trip is proven: a URL you can print
is a URL you can parse back into the route that produced it. A `String` parameter rides the URL
verbatim. A `Nat` or `Int` parameter prints with `repr` and parses with `toNat?`/`toInt?`, and the
round-trip is still discharged automatically. `linkTo route` builds a navigation link from a route
value, not a string, so a mistyped or impossible path won't compile. The routed app hands your
transition the route already parsed, and `Cmd.getJson` does the fetch and the decode together:

```lean
router R where
  home => ""
  user (name : String) => "users"
  post (id : Nat)       => "posts"

def app : App Model Msg :=
  ui init transition (onRoute := Msg.routed) fun m =>
    formEl [onSubmit .submit] [
      input [value m.query, onInput .typeQuery],
      linkTo (R.user "ada") [] "ada"     -- a real route, checked at compile time
    ]
```

### Effects

Side effects in Qed are data, which is what keeps `update` pure and provable. An arm returns the
next model with `still`, or the next model plus a `Cmd` to run with `also`. The driver performs the
`Cmd`. Your logic never touches the network. Here's a chat that streams an LLM's reply token by
token, with no `fetch` anywhere in it. `Cmd.stream` opens the request and feeds each token back as a
`.chunk` message, so a streaming reply is, to `update`, just more messages arriving.

```lean
def transition (m : Model) : Msg → Model × Cmd Msg
  | .typed s   => still { m with draft := s }
  | .send      => also (pushTurn m) (.stream "/v1/chat/completions" (reqBody m.turns.pop) .chunk .done)
  | .chunk raw => still { m with turns := appendLast m.turns (deltaOf raw) }
  | .done      => still { m with pending := false }
```

The battery is typed and covers what you reach for: `storageSet`/`storageGet`, `pushUrl`/`back`,
`copy`/`paste`, `focus`/`scrollIntoView`, `after`/`afterKeyed` (debounce), `setTitle`, `randomInt`,
`download`/`pickFile`, `getJson`/`postJson`/`stream`, and `batch`. A WebSocket is the same shape.
`Cmd.wsOpen "feed" "/live" .received` opens one under a key, its open/close/error events arrive as
messages, and `Cmd.wsSend`/`Cmd.wsClose` address it by key. When something isn't built in (IndexedDB,
a hardware API, a third-party widget), you reach for a port. The `ports` command generates the
outbound `Cmd`s and the inbound `onPort`, and you wire the real API in a few lines of JS.

### Components, and lifting their invariants over a list

A `Component` is a self-contained `update` and `view` with its own state and message type. It's the
reusable unit you reach for in React, written the same way. Here's a feed card. Its last two lines
are its own contract: one for behavior, one for styling.

```lean
namespace Card
  structure Model where
    id    : Nat
    likes : Int
    liked : Bool
  inductive Msg | toggleLike
  def update (c : Model) : Msg → Model
    | .toggleLike => if c.liked then { c with liked := false, likes := c.likes - 1 }
                     else        { c with liked := true,  likes := c.likes + 1 }
  def likeOn  : Style := css [ color "#ff2d55" ]
  def likeOff : Style := css [ color "#8a8a8a" ]
  def view (c : Model) : Html Msg :=
    button [role "like", onClick .toggleLike, if c.liked then likeOn else likeOff] [text s!"♥ {c.likes}"]
  def component : Component Model Msg := { update, view }
  abbrev Safe (c : Model) : Prop := 0 ≤ c.likes ∧ (c.liked → 1 ≤ c.likes)
end Card

invariant cardSafe   : Card.Safe preserved_by Card.update
invariant cardStyled : roleHasOneOf "like" [Card.likeOn, Card.likeOff] holds_in Card.view
```

`embed` drops the card into a keyed list and writes the wiring for you, `cardView` and `cardUpdate`.
It routes each message back to its row by key, the identity the diff reconciles by, so a reorder
never misdelivers one.

Now the part you can't do in a normal framework. The card's contract lifts to the whole list, one
line each. `feedSafe` proves every card in the feed stays valid. `feedStyled` proves every card
renders styled. Both hold across the feed's own transitions, and the kernel discharges them with no
proof from you:

```lean
embed Card as card keyedBy (toString ·.id) into cards

def update (m : Model) : Msg → Model
  | .card k msg => cardUpdate m k msg                                 -- route a tap to one card
  | .rank       => { m with cards := m.cards.sortBy (fun a b => a.likes ≥ b.likes) }
  | .dismiss id => { m with cards := m.cards.filter (·.id != id) }

invariant feedSafe   : cardSafe   for_each cards preserved_by update  -- ∀ card, stays valid
invariant feedStyled : cardStyled for_each cards holds_in view        -- ∀ card, renders styled
```

Break the promise and the build breaks with it. Append a card you didn't validate, or sort with the
unverified `Array.qsort`, and the build fails. It names the arm and the one-line fix. `feedSafe` is
itself "every card is valid," so it composes. A screen holding several feeds lifts it again, one line
up. `Examples/Feed.lean` is the worked feed.

Some state has no business in the root model: a row's open editor, a half-typed draft, a per-widget
count. React reaches for `useState`. Qed reaches for a local component. It's keyed and driver-owned,
its state serialized by `jsonStruct`, its message type private, and it can bubble a typed value up to
its parent. The whole local store snapshots and restores through `window.qed.snapshot()` and
`.restore(json)`.

### Server-side rendering

`App.renderModel app m` renders any model to HTML with the same `view` the browser runs, and
`renderDocument` wraps it in a page the client adopts on load. With `dehydrate`/`rehydrate` it starts
from the server's model, so there's no refetch and no flash. `Examples/Bookshelf.lean` is the worked
app: a routed catalog over a `Resource (Array Book)` (a remote value as `idle | loading | ok | failed`),
a detail page, and an add-book `form` that POSTs and routes to the new book, server-rendered and
driven end to end by a browser test. Every feature above has one like it in `Examples/` and `test/`.

## Does proving things cost you speed?

No. Because the engine knows which subtrees are value-updates, a changed row's text and attributes go
straight to its node, and on the standard keyed-list benchmark that lands about at React's
update/swap/reorder numbers. The one gap is cold create of a very large list. And since the
transpiler turns Lean's tail recursion into loops, building, diffing, and walking lists run in
constant stack, so 100,000+ rows reconcile without trouble.

## Getting started

The installer grabs elan (Lean's toolchain manager) if you don't have it, drops the framework into
`~/.qed`, and puts `qed` on your PATH. There's no heavy toolchain to download. `qed build` emits
plain JavaScript. Verification isn't a separate step you have to remember. It runs inside every
build:

```bash
qed dev        # watch sources, rebuild, serve with live-reload  → localhost:8000
qed build      # production build → dist/
qed start      # serve the build            (alias: preview)
qed test       # browser test suite (if present; needs node)
qed check      # verify only: proofs + no-sorry + axiom-clean, no artifacts
qed clean      # remove build outputs
qed new APP    # scaffold a new app
qed doctor     # report which dependencies are present
```

A failed proof is a failed build. The sources are grepped for `sorry`/`admit`/`native_decide`, and
the axiom manifest runs, so a "proof" that smuggles in an axiom is caught. `npm run dev` / `build` /
`test` work too. When you're hacking on the framework itself, the in-repo `./qed` shim runs the CLI
against this checkout.

## What's next

The framework is feature-complete enough to build real apps. The remaining work is honest about its
edges:

- **Cold create of huge lists** is the one benchmark gap left versus React, and the pure string
  renderer used for SSR still recurses per element. Making both iterative is on the list.

Give it a try and state an invariant. Issues welcome at
[github.com/JacobAsmuth/qed/issues](https://github.com/JacobAsmuth/qed/issues).

## Where things live

| Path | What |
|------|------|
| `Qed/Html.lean` | The typed virtual DOM every bit of syntax becomes. |
| `Qed/Notation.lean` | The view combinators (`div`, `button`, `onClick`, …). |
| `Qed/View.lean` | The rendering model: `View` (`dyn`/`showIf`/`ifElse`/`forEach`/`dynNode`) and the `view%` lift behind `ui`; built once, then changed bindings patch (`patch_render`/`applyValues_render`). |
| `Qed/Runtime.lean` | The Elm Architecture: `App`, the `ui` builder (`still`/`also`), the `Cmd` effects + `port`/`onPort`, local components, and server-side render. |
| `Qed/Diff.lean` | The reconciler the engine uses internally: one children reconcile shared by positional and keyed, `lazy` memoization, and the `diff_apply` proof. |
| `Qed/Json.lean` | JSON parser/renderer + `jsonStruct`/`jsonCodec`, with the `parse_depth_le`/`parse_render` proofs. |
| `Qed/Router.lean` | The `Router` class (round-trip law as a field), the `router` command, `toURL`/`fromURL`. |
| `Qed/Form.lean` | `Field p`, the `Input` controls, and the `form` command (Draft + `parse` + `formView` + `canSubmit_iff`). |
| `Qed/Component.lean` | `Component`, the `embed` macro, and the `for_each` lift lemmas. |
| `Qed/Invariant.lean` | The `invariant` command (`preserved_by` / `holds_in` / `for_each`). See [`docs/invariants.md`](docs/invariants.md). |
| `Qed/Dom.lean` / `Qed/Driver.lean` | The DOM primitives (the one trusted boundary) and the impure driver. |
| `Js/Backend.lean` | The Lean IR to JavaScript transpiler. |
| `Examples/` · `test/` | Example apps and the browser tests that drive them. |

## License

MIT. See [`LICENSE`](LICENSE).
