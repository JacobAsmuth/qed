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
React, you already know the shape: components with state and props, written in JSX. Underneath,
every component desugars to Elm's architecture, a typed message and a pure reducer. That's what
makes the proofs possible.

```bash
curl -sSfL https://raw.githubusercontent.com/JacobAsmuth/qed/main/install.sh | sh
qed new myapp && cd myapp && qed dev      # → http://localhost:8000, live-reloading
```

## A proof assistant, in my frontend?

Two guarantees fall out before you write a single proof.

**Your app can't crash at runtime.** State transitions and views are ordinary total Lean
functions. A missing case in a `match`, or a render that might not terminate, isn't a warning you
can mute. It's a build error. The broken code never reaches a user, because it never reaches
`dist/`.

**You can state a fact about your app and let the kernel prove it.** This is the part with no
analogue in a normal framework. Here's a complete app, a counter whose count can never go
negative; `Qed.run Counter.app` is the whole browser entry.

```lean
component Counter where
  state count : Int := 0
  view =>
    <div class="counter">
      <button onClick={set count (if 0 < count then count - 1 else count)}>−</button>
      <span class="count">{count}</span>
      <button onClick={set count (count + 1)}>+</button>
      <button onClick={set count 0}>reset</button>
    </div>

invariant counterSafe : (fun s => 0 ≤ s.count) preserved_by Counter.update
```

State lives next to the view that uses it, and `set` is the only way to change it. But a handler
is not a closure mutating a cell: each `set` site becomes a constructor of a generated message
type, and a generated pure reducer (`Counter.update`) interprets it. That's Elm's architecture,
derived from the component, and it's what the invariant is stated over.

So the last line isn't a test, and you don't write its proof. It checks that every handler leaves
the count non-negative, and the build succeeds only if that holds for all of them. Delete the
`if 0 < count` guard and the build fails naming the handler that broke the invariant
(``case `set_count` still needs: 0 ≤ m.count - 1``).

Those `≤` glyphs aren't something you hunt for on the keyboard. In a Lean editor you type `\le` and
it turns into `≤` as you go, the same way `\ge \to \and \or` give you `≥ → ∧ ∨`. The comparisons and
the arrow also take plain ASCII, so `<=`, `>=`, and `->` work as written for `≤`, `≥`, and `→`.

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
Lean app (components, Model/Msg/update, invariants; proofs auto-discharged)
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

`router` declares your pages, and from that one table it proves routing round-trips: any route you
print is one you can parse back into the exact route that produced it. That proof is why `linkTo`
takes a route value, not a string. The link below can only point at a page that exists, so a
mistyped or never-declared route is a compile error, not a broken link you ship.

```lean
router R where
  home => ""
  user (name : String) => "users"
  post (id : Nat)       => "posts"
  * notFound => "404"                    -- where any unmatched URL lands

def app : App Model Msg :=
  ui init transition (onRoute := Msg.routed) fun m =>
    <form onSubmit={.submit}>
      <input value={m.query} onInput={.typeQuery}/>
      {linkTo (R.user "ada") [] "ada"}   -- a real route, checked at compile time
    </form>
```

A parameter rides the URL as one segment. A `String` goes through verbatim; a `Nat` or `Int` is
decoded when the URL parses, so `/posts/abc` never reaches your code as a `post`. The proof covers
the links your app builds, not what someone types in the address bar, so a URL that matches nothing
still has to resolve to something. Mark a route with `*` and unmatched URLs land there; leave it off
and they fall back to your first route. `onRoute` hands your transition the parsed route, and
`Cmd.getJson` does the fetch and the decode in one step.

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

Every piece of UI is the same declaration the counter at the top used. Here's a feed card. The
like handler sets two fields in one message, and the two invariants are the card's contract, one
over behavior, one over styling.

```lean
component Card where
  state id    : Nat        -- no defaults: the parent fills these in
  state likes : Int
  state liked : Bool
  key id                   -- which field identifies a card in a list
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

A component is used as a JSX tag (capitalized, the React rule), and who owns its state is
decided at the use site, not in how you write it. State the parent never reads, like an open editor
or a half-typed draft, stays out of your model entirely. `<Editor key="row-7"/>` mounts a keyed
instance the framework owns. Props seed it (`<Editor text={r.text}/>`), `onEmit={…}` receives its
typed output, and registration is automatic. State the parent does read, the parent
owns: the feed holds its cards in the model, binds each one with `state={…}`, and shows the
list like any other data:

```lean
structure Model where
  cards : Array Card.State

inductive Msg | card (k : String) (msg : Card.Msg) | rank | dismiss (id : Nat)

def update (m : Model) : Msg → Model
  | .card k msg => { m with cards := Card.updateKeyed m.cards k msg }  -- one card, by key
  | .rank       => { m with cards := m.cards.sortBy (fun a b => a.likes ≥ b.likes) }
  | .dismiss id => { m with cards := m.cards.filter (·.id != id) }

def view (m : Model) : Html Msg :=
  <section class="feed">
    <button onClick={.rank}>Most liked</button>
    <div class="cards">{m.cards.map fun c =>
      <article key={toString c.id}>
        <Card state={c} onMsg={.card}/>
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

The feed's root is the architecture written out by hand: a `Model`, a `Msg`, a reducer, exactly
what `component` generates behind the counter at the top. An app starts as one component
(`Qed.run Hello.app` is the whole program, `Examples/Hello.lean`) and graduates to an explicit
root when it needs routing, effects, or state of its own, without rewriting the components it
already has.

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
hello-world component to the full Bookshelf app.

## Does proving things cost you speed?

No. The engine already knows which subtrees are value updates, so a changed row's text and attributes
go straight to its node, no diff. On the standard keyed-list benchmark it comes out about even with
React on update, swap, and reorder. The transpiler turns Lean's tail recursion into real loops, so
building, diffing, and walking a list all run in constant stack. Even 100,000 rows reconcile without
trouble.

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
| `Qed/Component.lean` | `Component`, the `for_each` lift lemmas, and the `component` declaration (`state`/`key`/`emits`/`view`/`set`). |
| `Qed/Invariant.lean` | The `invariant` command (`preserved_by` / `holds_in` / `for_each`). See [`docs/invariants.md`](docs/invariants.md). |
| `Qed/Dom.lean` / `Qed/Driver.lean` | The DOM primitives (the one trusted boundary) and the impure driver. |
| `Js/Backend.lean` | The Lean IR to JavaScript transpiler. |
| `Examples/` · `test/` | Example apps and the browser tests that drive them. |

## License

MIT. See [`LICENSE`](LICENSE).
