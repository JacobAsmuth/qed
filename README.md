# Qed

**A formally-verified web frontend framework in Lean 4.**

You write your app in [Lean](https://lean-lang.org) — the state, the messages it answers, how
the state changes, and what it looks like — and `qed build` transpiles it (and the whole
verified framework) to plain JavaScript that runs in any browser. If you've written Elm, it
will feel familiar. The difference is that Lean is a proof assistant, so it can check things
about your code that other languages can only hope are true.

Two of those come for free:

- **Your `update` and `view` can't crash.** They're ordinary total functions, so a missing case
  or a render that doesn't terminate is a compile error. It never reaches a user.
- **You can state a fact about your app and let Lean prove it.** The counter below claims its
  count never goes negative. I don't test that — the kernel checks it, for every message, and I
  never write the proof by hand.

## Getting set up

```bash
curl -sSfL https://raw.githubusercontent.com/JacobAsmuth/qed/main/install.sh | sh
qed new myapp && cd myapp && qed dev
```

The installer grabs elan (Lean's toolchain manager) if you don't have it, drops the framework
into `~/.qed`, and puts `qed` on your PATH. `qed build` turns your app into plain JavaScript —
there's no heavy toolchain to download. `qed dev` serves it with live-reload, and `qed test`
drives it in a headless browser (that part needs node).

## Building things

Each snippet assumes `import Qed` and `open Qed`.

### A counter

Every Qed app is the same three pieces Elm taught us: a *model* (the state), an *update* (how a
message changes it), and a *view* (the state, drawn as HTML). `ui` ties them together.

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

def main := Qed.run app   -- the browser entry point (transpiled to JS by `qed build`)
```

Notice that the view is just ordinary control flow — an `if`, a `.map`, string interpolation,
a call to one of your own helpers. There's no template language to learn. The last line is the
interesting one: it claims the count is never negative, and `invariant` proves that holds after
every message. Try deleting the `if 0 < m.count` guard. The build stops, because the claim is no
longer true — and the error names the message that broke it (`case decrement`).

The same syntax covers effectful transitions, and a `:=` clause supplies a proof for the claims
the automation can't close on its own. [`docs/invariants.md`](docs/invariants.md) is the menu of
properties worth stating — bounds, preconditions, mutual exclusion, effect safety, unique keys.

### Reading JSON

`Json.parse` never throws. It's a total function, so bad input just comes back as an `.error`
value. It also takes a depth budget — 64 by default — and there's a proof, `parse_depth_le`,
that whatever it returns nests no deeper than the number you passed. A deeply-nested payload
can't push past the limit you set.

`jsonStruct` declares a structure and generates its `ToJson`/`FromJson` from the same field
list, plus a `decode` that parses and decodes in one call. Nested structures decode recursively,
and the depth budget rides along.

```lean
jsonStruct Address where
  city    : String
  country : String

jsonStruct User where
  name    : String
  age     : Nat              -- a Nat can't be negative: "age": -3 → .error "age: expected a non-negative integer"
  address : Address          -- nested, decoded recursively
  bio     : Option String    -- Option ⇒ may be missing or null, comes back `none`

def body : String := "{\"name\":\"Ada\",\"age\":36,\"address\":{\"city\":\"London\",\"country\":\"UK\"}}"

#eval (User.decode body (maxDepth := 8)).map (·.address.city)   -- Except.ok "London"
#eval (User.decode body (maxDepth := 1)).map (·.name)           -- Except.error "maximum depth exceeded"
```

Sometimes you don't want the whole structure — you just want one field out of a big blob. Then
reach in by hand. Every step returns an `Option`, so a wrong turn is just `none`:

```lean
def cityOf (body : String) : Option String :=
  (Json.parse body).toOption
    |>.bind (·.path? ["address", "city"])
    |>.bind (·.str?)
```

### Forms

A `Field p` is a value carrying a *proof* that `p` holds of it. The only way to build one is to
pass validation, so by the time you're holding a `Signup`, every field in it is already valid.
An invalid form isn't something you can construct.

```lean
abbrev Email (s : String) : Prop := s.contains '@' ∧ s.length ≥ 3
abbrev Adult (n : Nat)    : Prop := n ≥ 18

form Signup where
  email : Input.text.refine Email
  age   : Input.nat.refine Adult                   -- parsed to a Nat first, then checked
  agree : Input.checkbox.refine (· = true)
  plan  : Input.select [("free", "Free"), ("pro", "Pro")]

structure Model where
  draft     : Signup.Draft   -- the raw input strings
  submitted : Option Signup  -- the validated account; `some` only once every field checks out

inductive Msg
  | edit (d : Signup.Draft)  -- the form hands back the whole edited draft
  | submit

def update (m : Model) : Msg → Model
  | .edit d => { m with draft := d }
  | .submit => { m with submitted := Signup.parse m.draft }   -- `none` if anything's invalid

def view (m : Model) : Html Msg :=
  Signup.formView m.draft .edit .submit   -- the inputs plus a submit button, disabled until valid
```

`formView` marks a field `aria-invalid` and shows a message once you've edited it and it still
doesn't validate. The submit gate and its `canSubmit_iff` proof come with it.

### Routing and HTTP

`router` declares your pages and, with them, a `Router` whose round-trip is proven: a URL you
can print is a URL you can parse back to the route that produced it. `linkTo route` builds an
in-place navigation link from a route *value*, so the target is always a real route — a broken
or mistyped path won't compile — and `Cmd.getJson` does the fetch and the decode together. The
`(onRoute := …)` builder hands your transition the route already parsed, not a raw path to pick
apart.

```lean
router R where
  home => ""
  user (name : String) => "users"

jsonStruct Profile where
  name : String
  bio  : String

def transition (m : Model) : Msg → Model × Cmd Msg
  | .typeQuery s  => still { m with query := s }
  | .submit       => also m (.pushUrl (Router.toURL (R.user m.query)))
  | .routed route => match route with
      | .user name => also { m with route }
          (Cmd.getJson s!"/api/users/{name}" (fun p => .gotProfile (.ok p)) (fun e => .gotProfile (.error e)))
      | _          => still { m with route }
  | .gotProfile r => still { m with profile := r }

def app : App Model Msg :=
  ui init transition (onRoute := Msg.routed) fun m =>
    formEl [onSubmit .submit] [
      input [value m.query, onInput .typeQuery, onKeydown .key],
      linkTo (R.user "ada") [] "ada"
    ]
```

`Examples/Users.lean` is the full app; `test/users_test.mjs` drives it against a mock API.

### Effects and streaming

Side effects in Qed are data, which keeps `update` pure. An arm returns the next model with
`still`, or the next model and a `Cmd` to run with `also`. The driver is what actually performs
the `Cmd` — your logic never touches the network. So here is a chat that streams an LLM's reply
token by token, and there isn't a `fetch` anywhere in it. `Cmd.stream` opens the request and
feeds each token back as a `.chunk` message; as far as `update` is concerned, a streaming reply
is just more messages arriving.

```lean
def transition (m : Model) : Msg → Model × Cmd Msg
  | .typed s   => still { m with draft := s }
  | .send      => also (pushTurn m) (.stream "/v1/chat/completions" (reqBody m.turns.pop) .chunk .done)
  | .chunk raw => still { m with turns := appendLast m.turns (deltaOf raw) }
  | .done      => still { m with pending := false }

def app : App Model Msg := ui init transition fun m =>
  div [cls "chat"] [
    div [cls "log"] (m.turns.toList.map bubble),
    input  [value m.draft, onInput .typed, placeholder "Message…"],
    button [disabled (m.pending || m.draft.trim.isEmpty), onClick .send] "Send"
  ]
```

Qed ships typed `Cmd`s for the things you reach for most: `storageSet`/`storageGet`,
`pushUrl`/`back`, `copy`/`paste`, `focus`/`scrollIntoView`, `after` and `afterKeyed` (debounce),
`setTitle`, `randomInt`, `download`/`pickFile`, `getJson`/`postJson`/`stream`, and `batch` to run
several at once. A `Cmd` you want to run at startup goes in the `(start := …)` argument.

A WebSocket works the same way. `Cmd.wsOpen` opens one under a key you choose and routes each
frame to a message; `Cmd.wsSend`/`Cmd.wsClose` address it by that key afterwards. Its open, close,
and error events are messages too, so the connection stays behind `update` like everything else:

```lean
def transition (m : Model) : Msg → Model × Cmd Msg
  | .connect    => also m (Cmd.wsOpen "feed" "/live" .received (onOpen := .opened) (onClose := .closed))
  | .send       => also { m with draft := "" } (Cmd.wsSend "feed" m.draft)
  | .received t => still { m with log := m.log.push t }
  | .opened     => still { m with online := true }
  | .closed     => still { m with online := false }
```

When something genuinely isn't built in — IndexedDB, a hardware API, a third-party widget — you
don't patch the framework. You reach for a port. The `ports` command generates the outbound `Cmd`s
and the inbound `onPort`, and you wire the actual API up in a few lines of JS:

```lean
ports where
  saveDoc  : Doc          -- outbound: `saveDoc (d : Doc) : Cmd msg`
  docSaved : Id => .saved  -- inbound:  "docSaved" payload decoded into `Msg.saved`
```
```js
globalThis.__qed.ports["saveDoc"] = (p) => idbPut("docs", JSON.parse(p)).then((id) => __qed.send("docSaved", id));
```

`Examples/Effects.lean` exercises the battery and `Examples/Socket.lean` is a WebSocket echo
client; `test/effects_test.mjs` and `test/socket_test.mjs` drive them.

### Lists and components

A `Component` is a reusable `update`+`view` with its own state and message type. `embed` wires
one into a keyed list and writes the two pieces you'd otherwise write by hand: `rowView`, the
row's view with its messages stamped by key, and `rowUpdate`, which sends a message back to the
right row. The routing is by *key* — the same identity the diff reconciles by — so a message
can't land on the wrong row once the list reorders.

```lean
namespace Row
  structure Model where
    id   : Nat                      -- the key
    text : String
    done : Bool
  inductive Msg | toggle
  def update (m : Model) : Msg → Model
    | .toggle => { m with done := !m.done }
  def view (m : Model) : Html Msg :=
    span [cls (if m.done then "item done" else "item"), onClick .toggle] [m.text]
  def component : Component Model Msg := { update, view }
end Row

structure Model where
  rows   : Array Row.Model
  draft  : String
  nextId : Nat

inductive Msg
  | edit (s : String)
  | add
  | row (k : String) (msg : Row.Msg)
  | remove (id : Nat)
  | sort

embed Row as row keyedBy (fun r => toString r.id) into rows   -- generates rowView / rowUpdate

def update (m : Model) : Msg → Model
  | .edit s    => { m with draft := s }
  | .add       => let t := m.draft.trim
                  if t.isEmpty then m
                  else { m with rows := m.rows.push { id := m.nextId, text := t, done := false }
                                draft := "", nextId := m.nextId + 1 }
  | .row k msg => rowUpdate m k msg
  | .remove id => { m with rows := m.rows.filter (·.id != id) }
  | .sort      => { m with rows := m.rows.qsort (fun a b => compare a.text b.text == .lt) }

def app : App Model Msg := ui init update fun m =>
  div [cls "todo"] [
    div [cls "add"] [
      input  [value m.draft, onInput .edit, placeholder "What needs doing?"],
      button [onClick .add]  "Add",
      button [onClick .sort] "Sort"
    ],
    ul [cls "items"] (m.rows.map fun r =>
      li [key (toString r.id)] [
        rowView r,
        button [cls "rm", onClick (.remove r.id)] "✕"
      ])
  ]
```

`Examples/Todo.lean`; `test/todo_test.mjs` drives it in a browser.

### Local state

Some state has no business in the root model — whether a row's editor is open, a half-typed
draft, a per-widget count. React puts that in `useState`; Qed puts it in a *local component*,
addressed by an explicit key and owned by the driver. You serialize its state with a
`jsonStruct`, its message type stays private, and it can *bubble* a typed value up to its parent
when it has something to report. The whole local store snapshots and restores through
`window.qed.snapshot()` / `.restore(json)`.

```lean
namespace Widget
  jsonStruct State where
    count : Int
    note  : String
  inductive Msg | inc | dec | setNote (s : String) | report
  def update (s : State) : Msg → State × Option Int   -- the optional value is the output to bubble up
    | .inc       => ({ s with count := s.count + 1 }, none)
    | .dec       => ({ s with count := s.count - 1 }, none)
    | .setNote t => ({ s with note := t }, none)
    | .report    => (s, some s.count)
  def view (s : State) : Html Msg :=
    div [cls "widget"] [
      button [onClick .dec] "−", span [cls "count"] [text (toString s.count)], button [onClick .inc] "+",
      input  [value s.note, onInput .setNote],
      button [onClick .report] "Report ↑"
    ]
  def reg : LocalDef := LocalDef.of "widget" { count := 0, note := "" } view update
end Widget

-- in the parent view: an empty host the driver fills; `.localInit` seeds this instance from row data
div [(localMountWith "widget" (toString r.id) (fun c => some (Msg.reported r.id c)))
       .localInit ({ count := 0, note := r.label } : Widget.State)] []

def app : App Model Msg := mkApp init update (View.ofHtml view) (locals := [Widget.reg])
```

Local components nest, and their state is dropped when their host leaves the DOM.
`Examples/Local.lean`; `test/local_test.mjs` covers seeding, sibling isolation, bubbling, GC, and
snapshot/restore.

### Putting it together

`Examples/Bookshelf.lean` puts the pieces together: a routed catalog that fetches a
`Resource (Array Book)`, a detail page that fetches one `Resource Book`, and an add-book `form`
that POSTs a valid draft and routes to the new book. `test/bookshelf_test.mjs` drives the whole
flow in a browser, and `Examples/BookshelfSSR.lean` renders each route on the server.

It leans on two conveniences worth calling out.

**Remote data.** `Resource α` is `idle | loading | ok | failed`. `Resource.fetch` does the GET
and the decode and reports the result as a single message, and `.view` renders whichever of the
four states you're in:

```lean
profile.view (fun prof => p [cls "bio"] [prof.bio])
  (loading := p [] ["Loading…"]) (failed := fun e => p [cls "error"] [e])
```

**Scoped styles.** `css "…"` makes a `Style` with a hashed class name; drop `styleSheet [card, …]`
once to emit one `<style>`. A typo'd reference is a compile error:

```lean
def card : Style := css "padding: 16px; &:hover { transform: translateY(-2px) }"
div [card] [ … ]
```

**Server-side rendering.** `App.renderModel app m` renders any model to HTML using the same
`view` the browser runs, and `renderDocument` wraps it in a page. The client picks up from that
markup on load. `Examples/UsersSSR.lean` renders a route per request.

## Performance

A keyed list updates each changed row's text and attributes straight at the node (they're
signals), so a value-only update touches no diff. The update step is proven to match a full
re-render (`patch_render`), and `qed check` enforces it. `test/bench_react.mjs` measures it
head-to-head against React on the same workload (10,000 rows); the fine-grained update path
turns a value-only change into O(changed bindings) with no tree walk.

## The `qed` command

Verification isn't a separate step you have to remember. It runs inside every `build`, `dev`,
and `check`: the kernel checks your proofs (a failed proof is a failed build), the sources are
grepped for `sorry`/`admit`/`native_decide`, and the axiom manifest is run.

```bash
qed dev        # watch sources, rebuild, serve with live-reload  → localhost:8000
qed build      # production build → dist/
qed start      # serve the build            (alias: preview)
qed test       # browser test suite (if present)
qed check      # verify only: proofs + no-sorry + axiom-clean, no artifacts
qed clean      # remove build outputs
qed new APP    # scaffold a new app
qed doctor     # report which dependencies are present
```

`npm run dev` / `build` / `test` work too (see `package.json`). Hacking on the framework itself,
the in-repo `./qed` shim runs the CLI against this checkout.

## How it fits together

`qed build` turns your app **and the whole framework** — the `render`, `diff`, and `update`
you read about above, plus the driver that runs them — into JavaScript. You don't install
emscripten or anything special; the output is a handful of `.mjs` files you can serve anywhere.

```text
Lean app (Model, Msg, update, view, deriving/invariant — proofs auto-discharged)
   │  lake build              (the kernel checks every proof)
   ▼
qedjs  (transpiles the Lean to JavaScript: your app + the Qed framework + the driver)
   ▼
dist/app.mjs  +  runtime/qed_rt.mjs   (a small library of the Lean primitives it uses)
   ▼
runtime/qed_dom.mjs + qed_host.mjs    (the only hand-written JS: the DOM calls and the
                  event wiring — everything else is your verified Lean, as JavaScript)
```

So the proofs that pass `qed check` describe the code that actually runs in the browser, and
`test/js_gate_test.mjs` checks the generated JavaScript computes exactly what the Lean does.

| Path | What |
|------|------|
| `Qed/Html.lean` | The typed virtual DOM every bit of syntax becomes. |
| `Qed/Notation.lean` | The view combinators (`div`, `button`, `onClick`, …). |
| `Qed/View.lean` | The rendering model: `View` (`dyn`/`showIf`/`ifElse`/`forEach`/`dynNode`, `View.ofHtml`) and the `view%` lift behind `ui`; built once, then changed bindings patch (`patch_render`/`applyValues_render`). |
| `Qed/Runtime.lean` | The Elm Architecture: `App`, the `ui` builder (`mkApp`/`mkRoutedApp`, `still`/`also`, `ToStep`), the `Cmd` effects + `port`/`onPort`, local components, and server-side render. |
| `Qed/Diff.lean` | The reconciler the engine uses internally — one children reconcile that positional and keyed share (they differ only in how each new child is matched to an old one), `lazy` memoization — plus the `diff_apply` proof. |
| `Qed/Json.lean` | JSON parser/renderer + `jsonStruct`/`jsonCodec`, with the `parse_depth_le`/`parse_render` proofs. |
| `Qed/Router.lean` | The `Router` class (round-trip law as a field), the `router` command, `toURL`/`fromURL`. |
| `Qed/Form.lean` | `Field p`, the `Input` controls, and the `form` command (Draft + `parse` + `formView` + `canSubmit_iff`). |
| `Qed/Component.lean` | `Component` and the `embed` macro for repeating one per keyed row. |
| `Qed/Date.lean` | A calendar `Date` that can't be invalid (smart constructor + ISO parser). |
| `Qed/Render.lean` | The pure `Html` → string renderer used for SSR. |
| `Qed/Invariant.lean` | The `invariant … preserved_by …` command (pure or effectful; auto-discharged, or `:=` proof). See [`docs/invariants.md`](docs/invariants.md). |
| `Qed/Dom.lean` / `Qed/Driver.lean` | The `@[extern]` DOM primitives (the one trusted boundary) and the impure driver. |
| `Examples/` · `test/` | Example apps and the browser tests that drive them. |
| `Cli.lean` + `./qed` · `runtime/` · `scripts/axioms.lean` | The toolchain, the C/JS driver + page, and the axiom manifest `qed check` gates on. |
