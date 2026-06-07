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

That last line isn't a test, and you don't write its proof. It checks that every message leaves the count non-negative, and the build succeeds only if that holds
for all of them. Delete the `if 0 < m.count` guard and the build will fail with an error naming the message
that broke the invariant (`case decrement`).

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

### Schema: forms and JSON, one declaration

`Json.parse` is a total function. Bad input comes back as an `.error` value, never an exception. It
takes a depth budget (64 by default), and a proof guarantees whatever it returns nests no deeper than
the number you gave it. A deeply nested payload can't push past your limit.

A `Field p` is a value carrying a proof that the
predicate `p` holds of it; the only way to build one is to pass validation, so by the time you hold a
`Book`, every refined field in it is already valid and an invalid one is not a thing you can
construct. The `schema` command reads the declaration once and generates the editable `Draft`, the
validated structure, `parse`, the `canSubmit` gate with a proof that it matches the validity it
claims, the `formView` widgets, and the `ToJson`/`FromJson` codec with `decode`/`encode`. A field's
refinement guards *both* directions: the form rejects it at submit, and `decode` rejects it on the
wire, with the same proof.

```lean
abbrev NonEmpty (s : String) : Prop := s.length ≥ 1
abbrev Year (n : Nat) : Prop := 1 ≤ n ∧ n ≤ 2026

schema Book where
  id      : Codec.text.jsonOnly                    -- rides the JSON, never shown in the form
  title   : Codec.text.refine NonEmpty
  year    : Codec.nat.refine Year                  -- parsed to a Nat first, then checked
  inPrint : Codec.checkbox
  blurb   : Codec.text                             -- unrefined, so it stays a bare `String`
  tags    : Codec.json (List String)               -- a nested/list field rides the JSON only
```

A refined field is stored as a proof-carrying `Field` (read it with `.val`); an unrefined one stays
its bare value type, so a plain data record reads exactly as you wrote it (and an `Option` field comes
back `none` when the key is missing or null). A `Codec.json T` field is for a nested record or a list
the form doesn't edit; it rides the JSON through `T`'s own `ToJson`/`FromJson`, recursively. `Book.decode body`
parses and decodes in one call, rejecting an out-of-range `year` (or an invalid value nested inside)
the same way the form does; `Book.encode` goes the other way. Whether a field is refined is read from
the elaborated codec, not its spelling, so factoring `Codec.text.refine NonEmpty` into a named helper
keeps the validation. `Book.formView draft .edit .submit` renders the inputs and a submit button that
stays disabled until every field checks out, marking a field `aria-invalid` once you've touched it and
it still doesn't validate.

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

Side effects are data, which keeps `update` pure and provable. An arm returns the next model with
`still`, or the model plus a `Cmd` to run with `also`, and the driver performs it. Here's a chat that
streams an LLM's reply token by token, with no `fetch` in it. `Cmd.stream` feeds each token back as a
`.chunk` message, so a streaming reply is, to `update`, just more messages arriving.

```lean
def transition (m : Model) : Msg → Model × Cmd Msg
  | .typed s   => still { m with draft := s }
  | .send      => also (pushTurn m) (.stream "/v1/chat/completions" (reqBody m.turns.pop) .chunk .done)
  | .chunk raw => still { m with turns := appendLast m.turns (deltaOf raw) }
  | .done      => still { m with pending := false }
```

The typed battery covers what you reach for, from `storageGet` and `getJson` to WebSockets and
debounced timers. When something isn't built in, the `ports` escape hatch wires a real JS API in a
few lines.

### Components, and lifting their invariants over a list

A `Component` is a reusable piece of UI with its own `Model`, `Msg`, `update`, and `view`. It owns
its message type, so embedding one means relabeling its messages into the parent's, and a misrouted
event is a type error.

Here's a feed card. The last two lines are its contract, one over behavior, one over styling.

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

`cardSafe` is a model invariant: the like count never goes negative, and a liked card has at least
one like. `cardStyled` uses `holds_in`, which states a property of the view rather than the model: in
every state the card can reach, the `role "like"` element carries one of its two styles.

To place many cards in a list, `embed` generates the wiring:

```lean
embed Card as card keyedBy (toString ·.id) into cards

def update (m : Model) : Msg → Model
  | .card k msg => cardUpdate m k msg                                 -- route a tap to one card
  | .rank       => { m with cards := m.cards.sortBy (fun a b => a.likes ≥ b.likes) }
  | .dismiss id => { m with cards := m.cards.filter (·.id != id) }

invariant feedSafe   : cardSafe   for_each cards preserved_by update  -- ∀ card, stays valid
invariant feedStyled : cardStyled for_each cards holds_in view        -- ∀ card, renders styled
```

`embed` generates `cardView` and `cardUpdate`. It routes each message by key rather than list index,
so a message reaches the card it came from after the list is sorted or filtered.

`for_each` lifts a child contract to the whole list. `cardSafe for_each cards` proves `cardSafe` for
every card in `cards` across every transition `update` makes, discharged automatically. It reduces
arm by arm: a routed message is covered by the card's own contract, `dismiss` only filters, `rank`
only reorders (through the verified `Array.sortBy`), and an appended card is valid by construction.
`feedStyled` lifts the styling contract the same way, over the view.

When an arm can't preserve the contract the build fails and names it. `Array.qsort` has no membership
lemma, so a `rank` written with it won't lift, and neither will an appended card that isn't provably
valid. `feedSafe` is itself a per-element predicate ("every card is valid"), so it lifts again over a
list of feeds. `Examples/Feed.lean` is the worked example.

State that doesn't belong in the root model (a row's open editor, a half-typed draft, a per-widget
counter) goes in a local component: keyed, driver-owned, its state serialized by `schema`, its
message type private, and able to bubble a typed value to its parent. The
local store snapshots and restores through `window.qed.snapshot()` and `.restore(json)`.

### Server-side rendering

`App.renderModel app m` renders any model to HTML with the same `view` the browser runs, and
`renderDocument` wraps it in a page the client adopts on load. With `dehydrate`/`rehydrate` it starts
from the server's model, so there's no refetch and no flash. `Examples/Bookshelf.lean` is the worked
app: a routed catalog over a `Resource (Array Book)` (a remote value as `idle | loading | ok | failed`),
a detail page, and an add-book form that POSTs and routes to the new book, server-rendered and
driven end to end by a browser test. Every feature above has one like it in `Examples/` and `test/`.

## Does proving things cost you speed?

No. Because the engine knows which subtrees are value-updates, a changed row's text and attributes go
straight to its node, and on the standard keyed-list benchmark that lands about at React's
update/swap/reorder numbers. The transpiler also turns Lean's tail recursion into loops, so building,
diffing, and walking lists run in constant stack, and 100,000+ rows reconcile without trouble.

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
| `Qed/Json.lean` | JSON parser/renderer + the `ToJson`/`FromJson` classes, with the `parse_depth_le`/`parse_render` proofs. |
| `Qed/Router.lean` | The `Router` class (round-trip law as a field), the `router` command, `toURL`/`fromURL`. |
| `Qed/Schema.lean` | `Field p`, the `Codec` controls, and the `schema` command. One declaration yields the form (Draft + `parse` + `formView` + `canSubmit_iff`) and the JSON codec (`ToJson`/`FromJson` + `decode`/`encode`). |
| `Qed/Component.lean` | `Component`, the `embed` macro, and the `for_each` lift lemmas. |
| `Qed/Invariant.lean` | The `invariant` command (`preserved_by` / `holds_in` / `for_each`). See [`docs/invariants.md`](docs/invariants.md). |
| `Qed/Dom.lean` / `Qed/Driver.lean` | The DOM primitives (the one trusted boundary) and the impure driver. |
| `Js/Backend.lean` | The Lean IR to JavaScript transpiler. |
| `Examples/` · `test/` | Example apps and the browser tests that drive them. |

## License

MIT. See [`LICENSE`](LICENSE).
