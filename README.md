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
The proofs that pass `qed check` describe the JavaScript that actually runs. If you've written
React, the view syntax will feel familiar; the architecture underneath is Elm's.

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
  <div class="counter">
    <button onClick={.decrement}>−</button>
    <span class="count">{m.count}</span>
    <button onClick={.increment}>+</button>
    <button onClick={.reset}>reset</button>
  </div>

invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update
```

That last line isn't a test, and you don't write its proof. It checks that every message leaves the count non-negative, and the build succeeds only if that holds
for all of them. Delete the `if 0 < m.count` guard and the build will fail with an error naming the message
that broke the invariant (`case decrement`).

## One way to write a view

You write the view in JSX, with plain Lean in the braces: `if`, `.map`, string interpolation, your
own helpers. No `memo`, no `signal`s, no `useState` to place. The framework decides, per subtree,
how to apply each change. A model value that changed is written straight at its node. A change of shape (rows
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

A form and an API payload are usually the same data, validated twice. In Qed you declare the data
once, rules included, and `schema` generates both sides.

```lean
abbrev NonEmpty (s : String) : Prop := s.length ≥ 1
abbrev Year (n : Nat) : Prop := 1 ≤ n ∧ n ≤ 2026

schema Book where
  id      : Codec.text.jsonOnly                    -- rides the JSON, never shown in the form
  title   : Codec.text.refine NonEmpty
  year    : Codec.nat.refine Year                  -- parsed to a Nat first, then checked
  inPrint : Codec.checkbox
  blurb   : Codec.text                             -- unrefined, stays a bare `String`
  tags    : Codec.json (List String)               -- nested data rides the JSON only
```

That one declaration yields the `Book` type, the form (`Book.formView`, whose submit button stays
disabled until every field validates), and the JSON codec (`Book.decode` / `Book.encode`). A rule
like `Year` is enforced in both directions by the same proof: the form won't submit an
out-of-range year, and `decode` rejects one arriving over the wire. So a `Book` you hold is valid;
an invalid one can't be constructed. And `Json.parse` itself is total, so bad input is an `.error`
value, never an exception.

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
    <form onSubmit={.submit}>
      <input value={m.query} onInput={.typeQuery}/>
      {linkTo (R.user "ada") [] "ada"}   -- a real route, checked at compile time
    </form>
```

### Effects

Your `update` never calls `fetch`. To touch the outside world it returns a `Cmd`, a value
*describing* the effect; the driver performs it and delivers the result back as ordinary messages.
That's what keeps `update` a pure function, the thing the proofs are about.

Here's the entire logic of a chat app that streams an LLM's reply token by token. `Cmd.stream`
feeds each token back as a `.chunk` message, so to `update`, a streaming reply is just more
messages arriving:

```lean
def transition (m : Model) : Msg → Model × Cmd Msg := steps
  | .typed s   => { m with draft := s }
  | .send      => (pushTurn m, .stream "/v1/chat/completions" (reqBody m.turns.pop) .chunk .done)
  | .chunk raw => { m with turns := appendLast m.turns (deltaOf raw) }
  | .done      => { m with pending := false }
```

(`steps` is how you write an effectful transition: an arm returns the next model, or a
`(model, cmd)` pair.) The built-in commands cover what you usually reach for: HTTP, localStorage,
clipboard, timers, WebSockets. For anything else, the `ports` escape hatch wires a real JS API in
a few lines.

### Components

A component is one declaration: state fields next to the view that uses them, changed only
through `set` in its own handlers. Here's a feed card. The like handler sets two fields in one
message, and the two invariants are the card's contract, one over behavior, one over styling.

```lean
component Card where
  state id    : Nat        -- no defaults: the parent fills these in
  state likes : Int
  state liked : Bool
  view =>
    <button role="like"
      onClick={set liked (!liked), set likes (if liked then likes - 1 else likes + 1)}
      {if liked then likeOn else likeOff}>{s!"♥ {likes}"}</button>

invariant cardSafe   : (fun c => 0 ≤ c.likes ∧ (c.liked → 1 ≤ c.likes)) preserved_by Card.update
invariant cardStyled : roleHasOneOf "like" [likeOn, likeOff] holds_in Card.view
```

A handler is not a closure: each `set` compiles to an ordinary message with a named case, so
invariants work on a component exactly as they do on the app model, and breaking one fails the
build naming the handler (`case set_liked_likes …`).

Who owns a component's state is decided where you *mount* it, not in how you write it. State the
parent never reads (an open editor, a half-typed draft) stays out of your model entirely: mount
keyed instances with `<div {Editor.mount "row-7"}/>` and the framework owns it. State the parent
does read, the parent owns. The feed holds its cards in the model, `embed` wires the component
over them, and the view shows the list like any other data:

```lean
structure Model where
  cards : Array Card.State

inductive Msg | card (k : String) (msg : Card.Msg) | rank | dismiss (id : Nat)

embed Card as card keyedBy (toString ·.id) into cards     -- generates cardView, cardUpdate

def update (m : Model) : Msg → Model
  | .card k msg => cardUpdate m k msg                     -- route a tap to one card, by key
  | .rank       => { m with cards := m.cards.sortBy (fun a b => a.likes ≥ b.likes) }
  | .dismiss id => { m with cards := m.cards.filter (·.id != id) }

def view (m : Model) : Html Msg :=
  <section class="feed">
    <button onClick={.rank}>Most liked</button>
    <div class="cards">{m.cards.map fun c =>
      <article key={toString c.id}>
        {cardView c}
        <button onClick={.dismiss c.id}>✕</button>
      </article>}</div>
  </section>

invariant feedSafe   : cardSafe   for_each cards preserved_by update  -- ∀ card, stays valid
invariant feedStyled : cardStyled for_each cards holds_in view        -- ∀ card, renders styled
```

A tap inside a card routes back to that card by its key, so sorting or filtering the list can't
misdeliver it. And the two `for_each` lines lift the card's contract to the whole feed: every
card stays valid and styled, across every transition, proved automatically. An arm that can't
preserve the contract fails the build by name. `Examples/Feed.lean` and `Examples/Local.lean`
are the worked examples, including components that emit typed output up to their parent.

### Server-side rendering

You don't write any SSR code. A routed app already declares everything a server needs, its pages
(`router`) and their data (`queries`), so `qed build` emits `dist/ssr.mjs`: a request handler
built from your app. Per request it routes the URL, runs your queries server-side, renders with
the same verified `view` the browser runs, and embeds the model in the page, so the client adopts
the HTML with no refetch and no flash.

```bash
qed dev       # develop against the real thing: SSR + live reload
qed build     # dist/: the client bundle, plus ssr.mjs (the request handler)
qed start     # serve it: every route server-rendered, hydrated on load
```

Deploying stays simple. A static host still works (the same `dist/` is a complete
single-page app), and server rendering is one import away on any node or edge runtime:

```js
import render from './dist/ssr.mjs';   // (request) => Response, that's the whole API
```

`Examples/Bookshelf.lean` is the worked app, a routed catalog with a detail page and an add-book
form; its hydration test asserts a server-rendered load reaches interactive with zero API calls
from the client.

Every feature above has an example like it in `Examples/` and `test/`;
[`Examples/README.md`](Examples/README.md) orders them as a tour, one concept at a time, from the
counter to the full Bookshelf app.

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
qed dev        # watch sources, rebuild, serve (SSR) with live-reload  → localhost:8000
qed build      # production build → dist/ (client bundle + ssr.mjs)
qed start      # serve the build, server-rendered   (alias: preview)
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
| `Qed/Jsx.lean` | The JSX view syntax: `<div class="x" onClick={.tap}>…</div>`, expanded to `el "tag" [attrs] [kids]`. |
| `Qed/Notation.lean` | The attribute and event helpers (`cls`, `onClick`, `value`, …) JSX attributes expand to. |
| `Qed/View.lean` | The rendering model: `View` (`dyn`/`showIf`/`ifElse`/`forEach`/`dynNode`) and the `view%` lift behind `ui`; built once, then changed bindings patch (`patch_render`/`applyValues_render`). |
| `Qed/Runtime.lean` | The Elm Architecture: `App`, the `ui` builder, the `Cmd` effects + `port`/`onPort`, local components, and the render primitives. |
| `Qed/Ssr.lean` | The per-request SSR step `dist/ssr.mjs` loops: route, run the app's queries, render, dehydrate. |
| `Qed/Steps.lean` | The `steps` builder for effectful transitions: arms are bare models or `(model, cmd)` pairs. |
| `Qed/Diff.lean` | The reconciler the engine uses internally: one children reconcile shared by positional and keyed, `lazy` memoization, and the `diff_apply` proof. |
| `Qed/Json.lean` | JSON parser/renderer + the `ToJson`/`FromJson` classes, with the `parse_depth_le`/`parse_render` proofs. |
| `Qed/Router.lean` | The `Router` class (round-trip law as a field), the `router` command, `toURL`/`fromURL`. |
| `Qed/Schema.lean` | `Field p`, the `Codec` controls, and the `schema` command. One declaration yields the form (Draft + `parse` + `formView` + `canSubmit_iff`) and the JSON codec (`ToJson`/`FromJson` + `decode`/`encode`). |
| `Qed/Component.lean` | `Component`, the `embed` macro, the `for_each` lift lemmas, and the `component` declaration (`state`/`view`/`set`). |
| `Qed/Invariant.lean` | The `invariant` command (`preserved_by` / `holds_in` / `for_each`). See [`docs/invariants.md`](docs/invariants.md). |
| `Qed/Dom.lean` / `Qed/Driver.lean` | The DOM primitives (the one trusted boundary) and the impure driver. |
| `Js/Backend.lean` | The Lean IR to JavaScript transpiler. |
| `Examples/` · `test/` | Example apps and the browser tests that drive them. |

## License

MIT. See [`LICENSE`](LICENSE).
