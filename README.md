# Qed

**A formally-verified web frontend framework in Lean 4.**

Frontend code is where the bugs you ship actually live: the missing case in a reducer, the
render that throws on an empty list, the "this can't happen" that happens in production. Every
framework asks you to *trust* that your code is right, and the best they offer is a type checker
and a test suite that hope along with you. Qed makes a different bet. You write your app in
[Lean](https://lean-lang.org), a proof assistant, and the same kernel that mathematicians use to
check proofs checks your frontend.

`qed build` transpiles your app, and the entire verified framework, straight to plain JavaScript.
No emscripten, no WASM, no special runtime; the output is a handful of `.mjs` files you can serve anywhere.
The proofs that pass `qed check` now describe the JavaScript that actually runs. If you've written Elm, its structure will feel familiar.

```bash
curl -sSfL https://raw.githubusercontent.com/JacobAsmuth/qed/main/install.sh | sh
qed new myapp && cd myapp && qed dev      # → http://localhost:8000, live-reloading
```

## A proof assistant, in my frontend?

Two guarantees fall out before you write a single proof.

**Your `update` and `view` can't crash.** In Lean they're ordinary *total* functions. A missing
case in a `match`, or a render that might not terminate, isn't a warning you can mute, it's a
build error. The broken code never reaches a user, because it never reaches `dist/`.

**You can state a fact about your app and let the kernel prove it.** This is the part that has no
analogue in a normal framework. Below is a simple counter app with an invariant that its count is never negative.

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

That last line isn't a test, and you don't write its proof. `invariant` discharges it
automatically: it checks that *every* message leaves the count non-negative, and the build only
succeeds if that's true for all of them. Delete the `if 0 < m.count` guard and the build
fails. The error names the message that broke the promise (`case decrement`). The same
syntax covers effectful transitions, and a `:=` clause lets you hand over a proof for the rare
claim the automation can't close on its own.

What's worth stating? Bounds, preconditions, mutual exclusion, effect safety, unique keys. See
[`docs/invariants.md`](docs/invariants.md) for more examples. For many front-end developers and LLM's, an
auto-checked invariant is a property that can't quietly be violated; for you, it's the "this can't
happen" finally made true.

## One way to write a view

Look again at the counter's view. It's ordinary control flow: a list of children, and where you
need logic you reach for an `if`, a `.map`, string interpolation, a call to your own helper.
There's no template language, no JSX, and **no performance knobs.**

That last absence is deliberate, and it's the central idea of the framework. Other libraries make
you tell them how to go fast: wrap this in `memo`, give that list `key`s, pull this value into a
`signal`, hoist this into `useState`. Each knob is a place to be wrong, and being wrong is usually
silent: a stale row, a dropped focus, a re-render that didn't happen. Qed takes the decision away
from you. **You write the view the most straightforward way, and the framework decides, per
subtree, how to update it:** a model-derived value that changed gets patched straight at the node;
a change of *shape* (rows added, removed, reordered, a branch flipped) gets reconciled through the
verified diff. You never pick a strategy, and because the framework picks it, the framework can
*prove* the pick is correct.

So when the counter's text changes, nothing is diffed: the new number is written to that one text
node. When a list's rows reorder, the diff runs and the proof `diff_apply` guarantees the DOM ends
up exactly where the new view says it should. Same code, two strategies, and you wrote neither of
them down.

## Is the thing that runs the thing you proved?

A verified framework is worthless if the bytes in the browser aren't the bytes you proved things
about. This is the question every "verified" claim has to answer, and Qed's answer is that there
is no hand-written runtime to diverge from the proofs. `qed build` runs the Lean compiler's IR
through a transpiler (`qedjs`) that emits JavaScript for **your app, the whole framework, and the
driver that runs them:** the `render`, `diff`, `update`, and `view` you just read about, all of
it, as JS.

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

The only JavaScript a human wrote is the thin boundary at the bottom: the actual DOM calls and
event delegation. Everything above it is verified Lean. `test/js_gate_test.mjs` runs the
same probes through native Lean and through the transpiled JS and asserts they compute *exactly*
the same thing: render, diff, arithmetic, JSON, routing.

## The rest of the app is data, too

The counter is the whole architecture in miniature, but a real app needs to read JSON, validate
forms, route, talk to a server, and keep lists. Qed's approach to each is the same: push the thing
that can fail into a value the type system can see, so the failure becomes a case you handle
rather than an exception you forgot.

### JSON

`Json.parse` is a total function: bad input comes back as an `.error` value, never an exception.
It also takes a depth budget (64 by default), and there's a proof, `parse_depth_le`, that whatever
it returns nests no deeper than the number you gave it. A deeply-nested payload can't push past
the limit you set. `jsonStruct` writes the structure and its `ToJson`/`FromJson` from
one field list, plus a `decode` that parses and decodes in a single call, recursively through
nested structs:

```lean
jsonStruct User where
  name    : String
  age     : Nat              -- a Nat can't be negative: "age": -3 → .error "age: expected a non-negative integer"
  bio     : Option String    -- Option ⇒ may be missing or null, comes back `none`

#eval (User.decode body (maxDepth := 8)).map (·.name)    -- Except.ok "Ada"
#eval (User.decode body (maxDepth := 1)).map (·.name)    -- Except.error "maximum depth exceeded"
```

### Forms

A `Field p` is a value that carries a proof that the predicate `p` holds of it. The only way to
build one is to pass validation, so by the time you're holding a `Signup`, every field in it is
already valid, and an invalid form is not a thing you can construct. You write the predicates as
ordinary `Prop`s and the `form` command does the rest, including the `canSubmit_iff` proof that
the submit gate matches the validity it claims to enforce:

```lean
abbrev Email (s : String) : Prop := s.contains '@' ∧ s.length ≥ 3
abbrev Adult (n : Nat)    : Prop := n ≥ 18

form Signup where
  email : Input.text.refine Email
  age   : Input.nat.refine Adult                   -- parsed to a Nat first, then checked
  agree : Input.checkbox.refine (· = true)
  plan  : Input.select [("free", "Free"), ("pro", "Pro")]
```

`Signup.formView draft .edit .submit` renders the inputs and a submit button that's disabled until
every field checks out, marking a field `aria-invalid` once you've touched it and it still doesn't
validate.

### Routing and HTTP

`router` declares your pages and, with them, a `Router` whose round-trip is proven: a URL you
can print is a URL you can parse back into the route that produced it. A `String` parameter rides
the URL verbatim; a `Nat` or `Int` parameter prints with `repr` and parses with `toNat?`/`toInt?`,
and the round-trip is still discharged automatically. `linkTo route` builds a navigation link from
a route value, not a string, so a mistyped or impossible path won't compile, it'll fail to
elaborate. The routed app hands your transition the route already parsed, and `Cmd.getJson`
does the fetch and the decode together:

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

Side effects in Qed are data, which is what keeps `update` pure and therefore provable. An arm
returns the next model with `still`, or the next model plus a `Cmd` to run with `also`. The driver
performs the `Cmd`; your logic never touches the network. Here is a chat that streams an LLM's
reply token by token, with no `fetch` anywhere in it. `Cmd.stream` opens the request and feeds each
token back as a `.chunk` message, so a streaming reply is, to `update`, just more messages arriving.

```lean
def transition (m : Model) : Msg → Model × Cmd Msg
  | .typed s   => still { m with draft := s }
  | .send      => also (pushTurn m) (.stream "/v1/chat/completions" (reqBody m.turns.pop) .chunk .done)
  | .chunk raw => still { m with turns := appendLast m.turns (deltaOf raw) }
  | .done      => still { m with pending := false }
```

The battery is typed and covers what you reach for: `storageSet`/`storageGet`, `pushUrl`/`back`,
`copy`/`paste`, `focus`/`scrollIntoView`, `after`/`afterKeyed` (debounce), `setTitle`,
`randomInt`, `download`/`pickFile`, `getJson`/`postJson`/`stream`, and `batch`. A WebSocket is the
same shape. `Cmd.wsOpen "feed" "/live" .received` opens one under a key, its open/close/error
events arrive as messages, and `Cmd.wsSend`/`Cmd.wsClose` address it by key. When something isn't
built in (IndexedDB, a hardware API, a third-party widget), you reach for a port: the `ports`
command generates the outbound `Cmd`s and the inbound `onPort`, and you wire the real API in a few
lines of JS.

### Lists and components

A `Component` is a reusable `update`+`view` with its own state and message type. `embed` wires one
into a keyed list and writes the two pieces you'd otherwise write by hand: `rowView` (the row's
view with its messages stamped by key) and `rowUpdate` (which delivers a message back to the right
row). The routing is by key, the same identity the diff reconciles by, so once the list reorders,
a message still can't land on the wrong row:

```lean
embed Row as row keyedBy (fun r => toString r.id) into rows   -- generates rowView / rowUpdate

def update (m : Model) : Msg → Model
  | .row k msg => rowUpdate m k msg
  | .remove id => { m with rows := m.rows.filter (·.id != id) }
  | .sort      => { m with rows := m.rows.qsort (fun a b => compare a.text b.text == .lt) }
  | ...
```

For state that has no business in the root model (whether a row's editor is open, a half-typed
draft, a per-widget count), React reaches for `useState`; Qed reaches for a local component,
addressed by an explicit key and owned by the driver. It serializes its state with a `jsonStruct`,
keeps its message type private, and can bubble a typed value up to its parent when it has
something to report. The whole local store snapshots and restores through `window.qed.snapshot()`
/ `.restore(json)`.

### Server-side rendering

`App.renderModel app m` renders any model to HTML with the same `view` the browser runs, and
`renderDocument` wraps it in a page; the client adopts that markup on load (and, with
`dehydrate`/`rehydrate`, starts from the server's model so there's no refetch and no flash). Two
small conveniences ride along: `Resource α` (`idle | loading | ok | failed`) turns "fetch and
render the four states" into one `.view` call, and `css "…"` makes a scoped `Style` with a hashed
class name whose typo'd references are compile errors.

`Examples/Bookshelf.lean` is where these meet: a routed catalog fetching a `Resource (Array
Book)`, a detail page, and an add-book `form` that POSTs and routes to the new book, rendered on
the server by `Examples/BookshelfSSR.lean` and driven end-to-end by `test/bookshelf_test.mjs`.
Every feature above has a worked example in `Examples/` and a browser test in `test/` that drives
it.

## Does proving things cost you speed?

Verification doesn't make this slow, and the reason is the same "the framework decides" principle
from earlier. Because the engine knows which subtrees are
value-updates, a changed row's text and attributes are written straight at the node. A value-only
update is **O(changed bindings)**, with no tree walk and no diff at all. That fast path is proven
to agree with a full re-render (`patch_render`), and `qed check` enforces the proof. On the
standard keyed-list benchmark this lands at React's update/swap/reorder numbers; the one place it's
still behind is cold *create* of a very large list, which is honest compute and on the list below.

There's a subtler win in stack depth. Lean expresses iteration as tail recursion, and the
transpiler turns every tail call into a loop, so building, folding, diffing, and walking long
lists all run in constant stack, and a list of 100,000+ rows reconciles without trouble. (The
verified diff's children reconcile runs as a tail-recursive form that is proven equal to the
structural one, so `diff_apply` still describes the code that runs.)

## Getting started

The installer grabs elan (Lean's toolchain manager) if you don't have it, drops the framework into
`~/.qed`, and puts `qed` on your PATH. There's no heavy toolchain to download. `qed build` emits
plain JavaScript. Verification isn't a separate step you have to remember; it runs inside every
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

A failed proof is a failed build; the sources are grepped for `sorry`/`admit`/`native_decide`; and
the axiom manifest is run, so a "proof" that smuggles in an axiom is caught. `npm run dev` / `build`
/ `test` work too. When you're hacking on the framework itself, the in-repo `./qed` shim runs the
CLI against this checkout.

## What's next

The framework is feature-complete enough to build real apps, and the remaining work is honest
about its edges:

- **SVG**, a typed CSS-property DSL, and `Resource` auto-refetch-on-dependency are deferred
  features, not blocked ones.
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
| `Qed/Component.lean` | `Component` and the `embed` macro for repeating one per keyed row. |
| `Qed/Invariant.lean` | The `invariant … preserved_by …` command. See [`docs/invariants.md`](docs/invariants.md). |
| `Qed/Dom.lean` / `Qed/Driver.lean` | The DOM primitives (the one trusted boundary) and the impure driver. |
| `Js/Backend.lean` | The Lean IR to JavaScript transpiler. |
| `Examples/` · `test/` | Example apps and the browser tests that drive them. |
