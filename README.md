# Qed

**A formally-verified web frontend framework in Lean 4.**

Here's the pitch. You write your app — the state, the messages it answers, how
state changes, and what the screen looks like — as ordinary [Lean](https://lean-lang.org)
functions. Lean compiles them to WebAssembly, and the thing that ends up running in
the browser carries machine-checked guarantees. Not the "we wrote a lot of tests"
kind — the "the compiler flat-out refused to build it otherwise" kind.

I'm not a type theorist, and the good news is you don't have to be one either. What
you'll write looks a lot like Elm; Lean does the proving quietly in the background.
(If you ever catch me claiming something is proven when it isn't, open an issue and
I'll fix it.)

Two things you get without asking:

- **Your `update` and `view` can't crash.** They're total Lean functions, so a
  forgotten case, a partial match, or an accidental infinite render is a *compile*
  error — it never reaches a user. This isn't a linter being polite; the build
  simply won't hand you a binary.
- **You can state a fact about your app and have it proven.** The counter just
  below claims its count never drops below zero. We don't test that — the kernel
  checks it, for every possible message, with no proof written by hand.

## Getting set up

```bash
curl -sSfL https://raw.githubusercontent.com/JacobAsmuth/qed/main/install.sh | sh
qed new myapp && cd myapp && qed dev
```

The installer grabs elan (Lean's toolchain manager) if you don't have it, drops the
framework into `~/.qed`, builds the `qed` command, and puts it on your PATH. The
wasm toolchain and emscripten are big, so they're fetched lazily on your first
`qed build` rather than up front.

## Let's build some things

Everything below assumes you've got `import Qed` and `open Qed` at the top.

### A counter

Every Qed app is the same three pieces Elm taught us: a *model* (your state), an
*update* (how a message changes that state), and a *view* (your state, drawn as
HTML).

```lean
structure Model where
  count : Int
deriving Repr, Inhabited

inductive Msg | increment | decrement | reset
deriving Repr

def init : Model := { count := 0 }

def update (m : Model) : Msg → Model
  | .increment => { m with count := m.count + 1 }
  | .decrement => { m with count := if 0 < m.count then m.count - 1 else m.count }
  | .reset     => { m with count := 0 }

def view (m : Model) : Html Msg :=
  div [cls "counter"] [
    button [onClick .decrement] "−",       -- a plain string works — Qed wraps it in a text node
    span   [cls "count"]        [toString m.count],
    button [onClick .increment] "+",
    button [onClick .reset]     "reset"
  ]

def app : App Model Msg := sandbox init update view

-- Here's the fun part. We claim the count never goes below zero. Notice we don't
-- prove it - the `invariant` command does, for every message, no proof by hand.
-- Try deleting the `if 0 < m.count` guard above and watch the build refuse you.
invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update
```

### Reading JSON

`Json.parse` assumes the worst - it's total, so it never throws; bad input just comes back as an `.error` value.

It's also depth-bounded: every parse takes a budget (it defaults to 64), and
`parse_depth_le` proves that budget is a real ceiling - whatever comes back nests no
deeper than the number you handed in, so a hostile, deeply-nested blob can't slip past.

`jsonStruct` declares a struct and, from the same one-line field list, generates its
`ToJson`/`FromJson` *and* a `decode` (parse + decode in one call). Nested structs are
decoded recursively, and the depth budget rides along - so you set it right at the
call site:

```lean
jsonStruct Address where
  city    : String
  country : String

jsonStruct User where
  name    : String
  age     : Nat              -- a Nat can't be negative, so "age": -3 → .error "age: expected a non-negative integer"
  address : Address          -- a nested struct, decoded recursively
  bio     : Option String    -- Option ⇒ this field can be missing (or null), and comes back `none`

-- the response body — a user with a nested address, so it's two levels deep:
--   { "name": "Ada", "age": 36, "address": { "city": "London", "country": "UK" } }
def body : String := "{\"name\":\"Ada\",\"age\":36,\"address\":{\"city\":\"London\",\"country\":\"UK\"}}"

#eval (User.decode body (maxDepth := 8)).map (·.address.city)   -- Except.ok "London"  (parse + decode in one call)
#eval (User.decode body (maxDepth := 1)).map (·.name)           -- Except.error "maximum depth exceeded"
```

Sometimes you don't want the whole struct - you just want the city out of a big
blob. Reach in dynamically instead. Every step is an `Option`, so a wrong turn is
just `none`.

```lean
def cityOf (body : String) : Option String :=
  (Json.parse body).toOption
    |>.bind (·.path? ["address", "city"])   -- dig down two levels; a missing key is just `none`
    |>.bind (·.str?)                          -- "...and is it actually a string?" is the last gate
```

### Forms

A `Field p` is a value paired with a *proof* that `p` holds of it. The only way to
build one is to validate, so the moment you're holding a `Signup`, every field in it
is already known-good — an invalid form simply can't exist as a value. Which means
any handler that takes a `Signup` never has to second-guess what's inside it.

```lean
abbrev Email (s : String) : Prop := s.contains '@' ∧ s.length ≥ 3
abbrev Adult (n : Nat)    : Prop := n ≥ 18

form Signup where
  email : Input.text.refine Email
  age   : Input.nat.refine Adult                   -- parsed to a real Nat first, then checked
  agree : Input.checkbox.refine (· = true)         -- a Bool that has to be true to get through
  plan  : Input.select [("free", "Free"), ("pro", "Pro")]

structure Model where
  draft     : Signup.Draft   -- what's in the inputs right now — just strings, anything goes
  submitted : Option Signup  -- the validated account; `some` only once every field checks out

inductive Msg
  | edit (d : Signup.Draft)  -- the form hands you back the whole edited draft
  | submit

def update (m : Model) : Msg → Model
  | .edit d => { m with draft := d }
  | .submit => { m with submitted := Signup.parse m.draft }   -- `none` if anything's invalid

def view (m : Model) : Html Msg :=
  Signup.formView m.draft .edit .submit   -- the inputs, plus a submit button that's dead until valid
```

### Streaming

Side effects in Qed are just data. `update` stays a boring pure function - a
separate `effects` function says "after this message, go do that thing," and the
driver is the one that actually touches the network. So here's a chat with a live,
token-by-token LLM reply - and notice there isn't a single `fetch` in the logic.
`Cmd.stream` opens the streaming request and feeds each token back in as a `.chunk`
message, which is to say: as far as your `update` is concerned, a streaming reply is
just more messages showing up.

```lean
inductive Msg
  | typed (s : String)     -- you typed in the box
  | send                   -- you hit send
  | chunk (data : String)  -- one token just arrived from the stream
  | done                   -- the stream closed

def update (m : Model) : Msg → Model        -- still pure — Remember, no fetch lives in here
  | .typed s   => { m with draft := s }
  | .send      => …                          -- push your turn, clear the box
  | .chunk raw => { m with turns := appendLast m.turns (deltaOf raw) }   -- glue the token on
  | .done      => { m with pending := false }

def effects (m : Model) : Msg → Cmd Msg     -- this gets the model *after* update has run
  | .send => .stream "/v1/chat/completions" (reqBody m.turns.pop) .chunk .done
  | _     => .none                            -- most messages don't need to do anything

def view (m : Model) : Html Msg :=
  div [cls "chat"] [
    div [cls "log"] (m.turns.toList.map bubble),                       -- one bubble per turn
    input  [value m.draft, onInput .typed, placeholder "Message…"],    -- a controlled input
    button [disabled (m.pending || m.draft.trim.isEmpty), onClick .send] "Send"
  ]

def chatApp : App Model Msg := application init update view effects
```

### Lists and Components

A `Component` is a reusable `update`+`view` over its own state and message. Embedding
one per row used to mean four pieces of hand-written plumbing; `embed` writes three of
them for you. You still declare the one constructor Lean won't let a macro add to your
`Msg` — then `embed Row as row keyedBy … into rows` generates `rowView` (the row's view
with its messages stamped by its key) and `rowUpdate` (route a message to the matching
row). Routing is by *key*, the same stable identity the diff reconciles by, so a message
can't land on the wrong row after a sort.

```lean
namespace Row                       -- a component
  structure Model where
    id   : Nat                      -- this is the key
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
  | row (k : String) (msg : Row.Msg)   -- a message bubbling up from the row with key k
  | remove (id : Nat)
  | sort

embed Row as row keyedBy (fun r => toString r.id) into rows   -- generates rowView / rowUpdate

def update (m : Model) : Msg → Model
  | .edit s    => { m with draft := s }
  | .add       => let t := m.draft.trim
                  if t.isEmpty then m
                  else { m with rows   := m.rows.push { id := m.nextId, text := t, done := false }
                                draft  := "", nextId := m.nextId + 1 }
  | .row k msg => rowUpdate m k msg                            -- route it to that one row, by key
  | .remove id => { m with rows := m.rows.filter (·.id != id) }
  | .sort      => { m with rows := m.rows.qsort (fun a b => compare a.text b.text == .lt) }

def view (m : Model) : Html Msg :=
  div [cls "todo"] [
    div [cls "add"] [
      input  [value m.draft, onInput .edit, placeholder "What needs doing?"],
      button [onClick .add]  "Add",
      button [onClick .sort] "Sort"
    ],
    ul [cls "items"] (m.rows.map fun r =>
      li [key (toString r.id)] [               -- the key. Move this row and its DOM node tags along.
        rowView r,                             -- the row's own view, its messages stamped by key
        button [cls "rm", onClick (.remove r.id)] "✕"
      ]).toList
  ]
```

The whole app is `Examples/Todo.lean`, and `test/todo_test.mjs` drives it in a real
browser (it even checks that a row's DOM node survives a sort).

### Local state

Some state has no business in the root model — whether a row's editor is open, a
half-typed draft, a per-widget counter. React keeps it in `useState`; Qed keeps it in a
*local component*, addressed by an explicit key (not call order) and owned by the driver,
off the verified virtual DOM. Its state is serialized (a one-line `jsonStruct`), its
message type stays internal (no codec needed), and it can *bubble* a typed output up to
the parent — the one channel from a self-contained child back to `update`. Incrementing or
typing in one widget never touches the root model or its siblings, so a half-typed note
keeps its caret while the rest of the page sits still.

```lean
namespace Widget
  jsonStruct State where               -- only the state is serialized
    count : Int
    note  : String
  inductive Msg | inc | dec | setNote (s : String) | report
  def update (s : State) : Msg → State × Option Int   -- an optional OUTPUT to bubble up
    | .inc       => ({ s with count := s.count + 1 }, none)
    | .dec       => ({ s with count := s.count - 1 }, none)
    | .setNote t => ({ s with note := t }, none)
    | .report    => (s, some s.count)
  def view (s : State) : Html Msg :=
    div [cls "widget"] [
      button [onClick .dec] "−", span [cls "count"] [toString s.count], button [onClick .inc] "+",
      input  [value s.note, onInput .setNote],
      button [onClick .report] "Report ↑"
    ]
  def reg : LocalDef := LocalDef.of "widget" { count := 0, note := "" } view update
end Widget

-- in the parent view: an empty host the driver fills; a Report bubbles up to the root.
-- `.localInit` seeds THIS instance from row data — React's `useState(propValue)`.
div [(localMountWith "widget" (toString r.id) (fun c => some (Msg.reported r.id c)))
       .localInit ({ count := 0, note := r.label } : Widget.State)] []

-- and register it with the app
def app : App Model Msg := application init update view (locals := [Widget.reg])
```

Local components **nest** (a widget can embed another, which bubbles up to it), their
state is **garbage-collected** when their host leaves the DOM (unmount loses state, like
React), and the whole store **snapshots and restores** through `window.qed.snapshot()` /
`.restore(json)` — free time-travel and persistence, since it's all serialized. The whole
app is `Examples/Local.lean`; `test/local_test.mjs` drives all of it in a real browser
(seeding from props, sibling isolation, caret survival, two-level bubbling, GC, and
snapshot/restore).

### Talking to the outside world

`routed` plugs the verified `Router` into
the browser's URL bar - `link`s navigate without a reload, the back button does the
sensible thing, and the new path gets parsed back into a route. (That round-trip is
proven, by the way, so a URL you can print is a URL you can parse back.) `Cmd.getJson`
does the fetch *and* the decode in one move. And a `<form>` submits on Enter, the way
forms have since roughly 1995.

```lean
router R where
  home => ""
  user (name : String) => "users"

jsonStruct Profile where
  name : String
  bio  : String

def effects (m : Model) : Msg → Cmd Msg
  | .submit       => .pushUrl (Router.toURL (R.user m.query))   -- go to /users/<query>, no reload
  | .urlChanged _ => match m.route with
      | .user name => Cmd.getJson s!"/api/users/{name}"          -- GET it, decode it into a Profile
                        (fun p => .gotProfile (.ok p)) (fun e => .gotProfile (.error e))
      | _          => .none
  | _ => .none

def view (m : Model) : Html Msg :=
  formEl [onSubmit .submit] [
    input [value m.query, onInput .typeQuery, onKeydown .key],   -- Enter submits, Escape clears
    link "/users/ada" [] "ada"                                    -- a real link — but no page reload
  ]

def app : App Model Msg :=
  routed init update view (onUrlChange := Msg.urlChanged) (effects := effects)
```

The full app is `Examples/Users.lean`; `test/users_test.mjs` drives it against a mock
API — a deep link, link and form navigation, the back button, and the events.

### Effects, and the escape hatch

Effects are data, so `update` stays pure. Qed ships typed `Cmd`s for the things you
actually reach for — `storageSet`/`storageGet`/`storageRemove`/`storageClear`,
`pushUrl`/`replaceUrl`/`back`/`forward`, `copy`/`paste`, `focus`/`blur`/`select`/
`scrollIntoView`, `after` (the building block for debounce), `setTitle`, `randomInt`
(since a pure `update` can't roll dice), `download` and `pickFile`, plus
`getJson`/`postJson`/`stream`. `batch` runs several from one message:

```lean
def effects (m : Model) : Msg → Cmd Msg
  | .inc        => Cmd.storageSet "count" (toString m.count)        -- persist on change
  | .search q   => Cmd.afterKeyed "search" 300 (.runSearch q)       -- debounce in one line
  | .pickAvatar => Cmd.pickFile "image/*" .gotFile
  | .saveAll    => Cmd.batch [Cmd.storageSet "doc" m.doc, Cmd.setTitle "Saved"]
  | _           => .none

-- `start` runs one effect at boot (e.g. hydrate from localStorage before first paint)
def app := application init update view (effects := effects)
             (start := Cmd.storageGet "count" .loaded)
```

`afterKeyed`/`cancel` are keyed timers — scheduling a key cancels the pending one, so
debounce is a single line instead of a generation counter.

And when an effect *isn't* built in, like a hardware API, you don't
patch the framework. **Ports** are the escape hatch, and the `ports` command makes them
typed: declare channels once and it generates the outbound `Cmd`s and the inbound
`onPort` (no magic strings, no hand-rolled codecs). You wire the actual API in your own JS:

```lean
ports where
  wsSend : Command            -- outbound: `wsSend (c : Command) : Cmd msg`
  wsRecv : Event => .received  -- inbound:  "wsRecv" payload decoded into `Msg.received`

def app := application init update view (effects := effects) (onPort := some onPort)
-- effects m | .send => wsSend m.command
```
```js
const ws = new WebSocket(url);
globalThis.__qed.ports["wsSend"] = (p) => ws.send(p);
ws.onmessage = (e) => globalThis.__qed.send("wsRecv", e.data);   // → decoded → a Msg
```

The effect stays inspectable data (testable!) while reaching anything the platform
offers. The whole battery (`localStorage`, `setTitle`, `randomInt`, `pickFile`, `batch`,
`focus`, a keyed-timer debounce, and a typed-port round-trip) is `Examples/Effects.lean`,
driven in a real browser by `test/effects_test.mjs`. Local-component state has a matching
pair — `window.qed.snapshot()` / `.restore(json)` — for persistence and time-travel.

### Fine-grained view templates

`view : Model → Html Msg` rebuilds the whole tree each update and lets the diff find what
changed — simple, and fast enough to beat React on whole-list operations. But for a page
that's mostly static with a few live values, rebuilding everything to change one is wasted
work. A **`View` template** is the alternative: built into DOM once, then on update only
the model *projections* re-run, patching just the nodes whose value changed — no tree
rebuilt, nothing diffed. The value still lives in the model and `update` stays the pure
`Model → Msg → Model`; the binding is *derived*, not a side channel. You write it like an
ordinary view, and the `view%` macro lifts each `text` that reads the model into a binding:

```lean
def template : View Model Msg :=
  view% fun m =>
    div [] [
      span [] [text s!"Count: {m.count}"],           -- a bound text node
      showIf (·.loading) (p [] [text "loading…"]),    -- conditional structure
      forEach "ul" (·.rows) (·.id) row                -- a keyed list
    ]

def app := templated init update template
```

Static structure is built once; `showIf`/`forEach` reconcile through the *same verified
`diff`* when their shape changes. A keyed list goes further — each row's text is a signal,
so changing a row's value pushes straight to its node, no `childAt` and no reconcile.
Against the diff path on the same app (`test/bench_template.mjs`): a 2,000-node mostly-static
page updates **3.7× faster**, and a 10,000-row list with 1,000 rows changing **4.6× faster**
(40 ms → 8.8 ms). The honest gap to hand-written signals is that the template re-checks
every binding to *find* what changed (pure Lean has no dependency tracking), so it's a
category win over the diff, not a tie with `setSignal`. `Examples/Template.lean` is the
demo; `test/template_test.mjs` drives it in a browser.

## So what's actually happening?

Here's the trip from "I wrote some Lean" to "pixels in a browser":

```text
Lean app (Model, Msg, update, view, deriving/invariant — proofs auto-discharged)
   │  lake build         (Lean → C, in .lake/build/ir/*.c)
   ▼
emcc  (app C  +  runtime/qed_dom.c [EM_JS DOM shims]  +  prebuilt Lean wasm runtime)
   ▼
runtime/qed.js (MODULARIZE factory) + qed.wasm
   ▼
runtime/host.js:  qed_run_init() mounts;  click → qed_run_dispatch(id),
                  input → qed_run_dispatch_str(id, value), stream → chunk/done
                  → pure `update` → diff vs. previous view → patch only what changed
```

How does Qed stack up against React? `test/bench_react.mjs` runs Qed (WASM) and React
(production build) side by side. On my desktop:

| 10,000 rows, change every 10th | Qed (wasm) | React | React.memo |
|---|---|---|---|
| create | **84 ms** | 89 ms | 88 ms |
| swap two | 138 ms | **113 ms** | 112 ms |
| reorder all | 140 ms | 113 ms | **110 ms** |
| update | **0.8 ms** | 5 ms | 2 ms |

## The `qed` command

If you've used `npm` or `vite`, you already know most of these. Verification isn't a
separate step you have to remember — it runs inside every `build`/`dev`/`check`: the
Lean kernel checks your proofs (a failed proof *is* a failed build), the sources are
grepped for `sorry`/`admit`/`native_decide`, and the axiom manifest is run.

```bash
qed dev        # watch sources, rebuild, serve with live-reload  → localhost:8000
qed build      # production build → dist/ (optimized + verified)
qed start      # serve the build            (alias: preview)
qed test       # browser test suite (if present)
qed check      # verify only: proofs + no-sorry + axiom-clean, no artifacts
qed clean      # remove build outputs
qed new APP    # scaffold a new app
qed doctor     # report which dependencies are present
```

`npm run dev` / `build` / `test` / … work too (see `package.json`) if that's the
muscle memory you've got. When you're hacking on the framework itself, the in-repo
`./qed` shim runs the CLI against this checkout.

## Where everything lives

| Path | What |
|------|------|
| `Qed/Html.lean` | The core typed virtual DOM — the thing every bit of nice syntax eventually becomes. |
| `Qed/Notation.lean` | The readable view combinators (`div`, `button`, `onClick`, …). |
| `Qed/Runtime.lean` | The Elm Architecture (`App`, `sandbox`, `application`, `routed`), the `Cmd` effects (storage, navigation, clipboard, focus, `after`, `setTitle`, `randomInt`, files, `getJson`/`stream`, `batch`) and the `port`/`onPort` escape hatch, local-state components (`LocalDef`, `localMount`, `App.locals`), and the pure render-to-HTML. |
| `Qed/Invariant.lean` | The `invariant … preserved_by …` command (it discharges the proof for you). |
| `Qed/Diff.lean` | The diff/patch engine — positional reconcile (add/remove), `O(n)` keyed reconcile (reorder by `key`), and `lazy` subtree memoization — plus the `diff_apply` correctness proof. |
| `Qed/Json.lean` | The full JSON parser/renderer + `jsonStruct`/`jsonCodec`, with the `parse_depth_le` & `parse_render` proofs. |
| `Qed/Router.lean` | The `Router` class (round-trip law baked in as a field), the `router` command, and `toURL`/`fromURL` for the browser. |
| `Qed/Form.lean` | Typed refinement fields (`Field p`), the `Input` controls (text/number/checkbox/date/select/radios), and the `form` command (Draft + `parse` + `formView` + the `canSubmit_iff` proof). |
| `Qed/Date.lean` | A calendar `Date` that can't be invalid (smart constructor + ISO parser; impossible dates parse to `none`). |
| `Qed/Component.lean` | `Component` (a reusable `update`+`view`), `viewList`/`updateAt`/`updateKeyed` for repeating one per row, and the `embed` macro that writes the per-row wiring. |
| `Qed/View.lean` | Fine-grained `View` templates: `dyn`/`showIf`/`forEach`, the `templated` builder, and the `view%` auto-lift macro. Built once, then only changed bindings patch (lists update via signals). |
| `Qed/Dom.lean` | The `@[extern]` DOM primitives — the one trusted boundary. |
| `Qed/Driver.lean` | The impure browser driver (build + patch) + the `@[export]`ed entry points. |
| `Examples/` | Example programs. |
| `Cli.lean` + `./qed` | The toolchain (build/dev/test/check/…) and its shim. |
| `runtime/` | The C/JS driver, the page, and the dev server. |
| `test/` | Browser tests: counter (`browser_test.mjs`), chat (`chat_test.mjs`), form (`signup_test.mjs`), current-time (`booking_test.mjs`), dynamic list (`todo_test.mjs`), routing/http/events (`users_test.mjs`) + the mock LLM (`mock_llm.py`). |
| `scripts/axioms.lean` | The axiom manifest that `qed check`/`qed build` gate on. |
