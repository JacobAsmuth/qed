# Qed

**A formally-verified web frontend framework in Lean 4.**

You write your app — state, the messages it answers, how state changes, and the view — as
ordinary [Lean](https://lean-lang.org) functions, and Lean compiles them to WebAssembly. It
looks a lot like Elm; Lean does the proving in the background.

Two things hold by construction:

- **`update` and `view` can't crash.** They're total Lean functions, so a missing case or a
  non-terminating render is a compile error, not a runtime one.
- **You can state a fact about your app and have it proven.** The counter below claims its count
  never drops below zero — the kernel checks that for every message, with no proof written by hand.

## Getting set up

```bash
curl -sSfL https://raw.githubusercontent.com/JacobAsmuth/qed/main/install.sh | sh
qed new myapp && cd myapp && qed dev
```

The installer grabs elan (Lean's toolchain manager) if you don't have it, drops the framework
into `~/.qed`, and puts `qed` on your PATH. The wasm toolchain and emscripten are large, so
they're fetched on your first `qed build`.

## Building things

Each snippet assumes `import Qed` and `open Qed`.

### A counter

A Qed app is three pieces: a *model* (state), an *update* (how a message changes it), and a
*view*. `ui` builds the app from a view written inline.

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

def main := Qed.run app   -- the WASM entry point
```

The view is ordinary control flow — `if`/`match`, `.map`, string interpolation, your own
helpers — with no special syntax. `invariant` proves the stated property for every message;
delete the `if 0 < m.count` guard and the build refuses you.

### Reading JSON

`Json.parse` is total — it never throws; bad input comes back as `.error`. It's also
depth-bounded: every parse takes a budget (default 64), and `parse_depth_le` proves nothing
that comes back nests deeper than the number you handed in.

`jsonStruct` declares a struct and, from the same field list, generates its `ToJson`/`FromJson`
and a `decode` (parse + decode in one call). Nested structs decode recursively.

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

When you only want one field out of a blob, reach in dynamically — every step is an `Option`:

```lean
def cityOf (body : String) : Option String :=
  (Json.parse body).toOption
    |>.bind (·.path? ["address", "city"])
    |>.bind (·.str?)
```

### Forms

A `Field p` is a value paired with a *proof* that `p` holds of it. The only way to build one is
to validate, so a value of type `Signup` is evidence that every field is already valid — an
invalid form can't exist as a value.

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

`formView` also marks a field `aria-invalid` and shows a message once it's been edited and fails
to validate. The submit gate and its `canSubmit_iff` proof are generated alongside.

### Routing and HTTP

`router` declares the pages and a `Router` whose round-trip is proven (a URL you can print parses
back to the route that produced it). `link`s navigate without a reload; `Cmd.getJson` fetches and
decodes in one move. The `(onRoute := …)` builder hands your transition the *parsed* route.

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
      link "/users/ada" [] "ada"
    ]
```

`Examples/Users.lean` is the full app; `test/users_test.mjs` drives it against a mock API.

### Effects and streaming

Effects are data, so `update` stays pure: an arm returns the next model with `still`, or the
next model plus the `Cmd` it triggers with `also`. The driver runs the `Cmd`; nothing in the
logic touches the network. Here a chat streams an LLM reply token by token — `Cmd.stream` feeds
each token back in as a `.chunk` message, so a streaming reply is just more messages arriving.

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

Qed ships typed `Cmd`s for the common cases — `storageSet`/`storageGet`, `pushUrl`/`back`,
`copy`/`paste`, `focus`/`scrollIntoView`, `after` and `afterKeyed` (debounce), `setTitle`,
`randomInt`, `download`/`pickFile`, `getJson`/`postJson`/`stream` — and `batch` to run several at
once. A `Cmd` to run at boot goes in the `(start := …)` argument.

For an effect that isn't built in — a hardware API, a WebSocket — **ports** are the escape hatch.
The `ports` command generates the outbound `Cmd`s and the inbound `onPort`; you wire the API in JS:

```lean
ports where
  wsSend : Command             -- outbound: `wsSend (c : Command) : Cmd msg`
  wsRecv : Event => .received  -- inbound:  "wsRecv" payload decoded into `Msg.received`
```
```js
const ws = new WebSocket(url);
globalThis.__qed.ports["wsSend"] = (p) => ws.send(p);
ws.onmessage = (e) => globalThis.__qed.send("wsRecv", e.data);
```

`Examples/Effects.lean` exercises the whole battery; `test/effects_test.mjs` drives it.

### Lists and components

A `Component` is a reusable `update`+`view` over its own state and message. `embed` generates the
per-row wiring: `rowView` (the row's view with its messages stamped by key) and `rowUpdate`
(routing a message to the matching row). Routing is by *key* — the same identity the diff
reconciles by — so a message can't land on the wrong row after a sort.

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

State with no business in the root model — a row's open editor, a per-widget counter — goes in a
*local component*, addressed by an explicit key and owned by the driver. Its state is serialized
(a `jsonStruct`), its message type stays internal, and it can *bubble* a typed output up to the
parent. The whole local store round-trips through `window.qed.snapshot()` / `.restore(json)`.

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

`Examples/Bookshelf.lean` wires the pieces into one app: a routed catalog that fetches a
`Resource (Array Book)`, a detail page that fetches one `Resource Book`, and an add-book `form`
that POSTs a valid draft and routes to the new book. `test/bookshelf_test.mjs` drives the flow in
a browser; `Examples/BookshelfSSR.lean` renders each route server-side.

A couple of conveniences it uses:

**Remote data.** `Resource α` is `idle | loading | ok | failed`. `Resource.fetch` GETs and
decodes, reporting the outcome as one message; `.view` renders the four states:

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

**Server-side rendering.** `App.renderModel app m` renders any model to HTML with the same `view`
the browser runs, and `renderDocument` wraps it in a page; the client adopts that markup on load.
`Examples/UsersSSR.lean` renders each route per request.

## Performance

`test/bench_react.mjs` runs Qed (WASM) and React (production build) side by side. On my desktop:

| 10,000 rows, change every 10th | Qed (wasm) | React | React.memo |
|---|---|---|---|
| create | **84 ms** | 89 ms | 88 ms |
| swap two | 138 ms | **113 ms** | 112 ms |
| reorder all | 140 ms | 113 ms | **110 ms** |
| update | **0.8 ms** | 5 ms | 2 ms |

A keyed list updates each changed row's text and attributes straight at the node (they're
signals), so a value-only update touches no diff. The update step is proven to match a full
re-render (`patch_render`), and `qed check` enforces it.

## The `qed` command

Verification runs inside every `build`/`dev`/`check`: the kernel checks your proofs (a failed
proof is a failed build), the sources are grepped for `sorry`/`admit`/`native_decide`, and the
axiom manifest is run.

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

```text
Lean app (Model, Msg, update, view, deriving/invariant — proofs auto-discharged)
   │  lake build         (Lean → C, in .lake/build/ir/*.c)
   ▼
emcc  (app C  +  runtime/qed_dom.c [EM_JS DOM shims]  +  prebuilt Lean wasm runtime)
   ▼
runtime/qed.js (MODULARIZE factory) + qed.wasm
   ▼
runtime/host.js:  mounts the app; routes clicks/input/stream events to the pure `update`,
                  then patches only what the new model changed
```

| Path | What |
|------|------|
| `Qed/Html.lean` | The typed virtual DOM every bit of syntax becomes. |
| `Qed/Notation.lean` | The view combinators (`div`, `button`, `onClick`, …). |
| `Qed/View.lean` | The rendering model: `View` (`dyn`/`showIf`/`ifElse`/`forEach`/`dynNode`, `View.ofHtml`) and the `view%` lift behind `ui`; built once, then changed bindings patch (`patch_render`/`applyValues_render`). |
| `Qed/Runtime.lean` | The Elm Architecture: `App`, the `ui` builder (`mkApp`/`mkRoutedApp`, `still`/`also`, `ToStep`), the `Cmd` effects + `port`/`onPort`, local components, and server-side render. |
| `Qed/Diff.lean` | The reconciler the engine uses internally — positional and `O(n)` keyed reconcile, `lazy` memoization — plus the `diff_apply` proof. |
| `Qed/Json.lean` | JSON parser/renderer + `jsonStruct`/`jsonCodec`, with the `parse_depth_le`/`parse_render` proofs. |
| `Qed/Router.lean` | The `Router` class (round-trip law as a field), the `router` command, `toURL`/`fromURL`. |
| `Qed/Form.lean` | `Field p`, the `Input` controls, and the `form` command (Draft + `parse` + `formView` + `canSubmit_iff`). |
| `Qed/Component.lean` | `Component` and the `embed` macro for repeating one per keyed row. |
| `Qed/Date.lean` | A calendar `Date` that can't be invalid (smart constructor + ISO parser). |
| `Qed/Render.lean` | The pure `Html` → string renderer used for SSR. |
| `Qed/Invariant.lean` | The `invariant … preserved_by …` command. |
| `Qed/Dom.lean` / `Qed/Driver.lean` | The `@[extern]` DOM primitives (the one trusted boundary) and the impure driver. |
| `Examples/` · `test/` | Example apps and the browser tests that drive them. |
| `Cli.lean` + `./qed` · `runtime/` · `scripts/axioms.lean` | The toolchain, the C/JS driver + page, and the axiom manifest `qed check` gates on. |
