# Qed

**A formally-verified web frontend framework in Lean 4.**

Qed apps compile to WebAssembly and run in the browser, and because the code is
*Lean*, the running artifact carries machine-checked guarantees:

- **Total by construction.** Every `update` and `view` is an ordinary Lean
  function, so it is proven terminating and exhaustive *to compile*. Runtime
  crashes, non-exhaustive matches, and infinite render loops are rejected before
  the app ever builds.
- **Theorems about your app, discharged for you.** State a property; the
  framework generates and the kernel checks the proof. The counter below proves
  its count never drops below zero, with **no hand-written proof** — and the
  theorem depends only on Lean's core axioms (`propext`, `Quot.sound`), never
  `sorry`.

## Install

```bash
curl -sSfL https://raw.githubusercontent.com/JacobAsmuth/qed/main/install.sh | sh
qed new myapp && cd myapp && qed dev
```

The installer adds elan (the Lean toolchain manager) if it's missing, fetches the
framework into `~/.qed`, builds the `qed` CLI, and puts it on your PATH. The wasm
toolchain and emscripten are fetched on first `qed build`, not at install time.

## Examples

The snippets below assume `import Qed` and `open Qed`.

### A counter

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
    button [onClick .decrement] "−",            -- a bare string is a text child
    span   [cls "count"]        [toString m.count],
    button [onClick .increment] "+",
    button [onClick .reset]     "reset"
  ]

def app : App Model Msg := sandbox init update view

-- State the safety property; the framework proves it for every transition.
invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update
```

### Parsing JSON with errors handled

`Json.parse` is total and depth-bounded: malformed or too-deeply-nested input
returns an `.error`, it never throws. `jsonStruct` declares a structure and its
typed `ToJson`/`FromJson` in one go — the field list is written *once* — so turning
a response body into a value is a `do` block in the `Except` monad.

```lean
jsonStruct User where
  name : String
  age  : Nat                   -- a `Nat` field rejects negatives
  bio  : Option String         -- optional: absent or null ⇒ none

def decodeUser (body : String) : Except String User := do
  let json ← Json.parse body   -- .error on malformed / too-deep input
  fromJson json                -- .error "age: expected a non-negative integer" (names the field)
```

When you only need one value out of a larger payload, reach in dynamically. Every
step is an `Option`, so the wrong shape is just `none` - no exceptions:

```lean
def cityOf (body : String) : Option String :=
  (Json.parse body).toOption
    |>.bind (·.path? ["address", "city"])
    |>.bind (·.str?)
```

### A form that can't carry invalid data

```lean
abbrev Email (s : String) : Prop := s.contains '@' ∧ s.length ≥ 3
abbrev Adult (n : Nat)    : Prop := n ≥ 18

form Signup where
  email : Input.text.refine Email
  age   : Input.nat.refine Adult                  -- parsed to a Nat
  agree : Input.checkbox.refine (· = true)         -- a Bool; must be checked
  plan  : Input.select [("free", "Free"), ("pro", "Pro")]

structure Model where
  draft     : Signup.Draft           -- raw strings, generated from the fields above
  submitted : Option Signup           -- the validated account, once created

inductive Msg
  | edit (d : Signup.Draft)           -- the form hands back the whole updated draft
  | submit

def update (m : Model) : Msg → Model
  | .edit d => { m with draft := d }
  | .submit => { m with submitted := Signup.parse m.draft }   -- `some` only if valid

def view (m : Model) : Html Msg :=
  Signup.formView m.draft .edit .submit       -- inputs + a submit gated on validity
```

### A streaming LLM chat

```lean
inductive Msg
  | typed (s : String)     -- composer edited
  | send                   -- submit the draft
  | chunk (data : String)  -- one streamed SSE payload (an OpenAI delta)
  | done                   -- stream finished

def update (m : Model) : Msg → Model        -- pure: arms are plain record updates
  | .typed s   => { m with draft := s }
  | .send      => …                          -- push the user turn, clear the draft
  | .chunk raw => { m with turns := appendLast m.turns (deltaOf raw) }
  | .done      => { m with pending := false }

def effects (m : Model) : Msg → Cmd Msg     -- m is the post-update model
  | .send => .stream "/v1/chat/completions" (reqBody m.turns.pop) .chunk .done
  | _     => .none

def view (m : Model) : Html Msg :=
  div [cls "chat"] [
    div [cls "log"] (m.turns.toList.map bubble),                       -- one bubble per turn
    input  [value m.draft, onInput .typed, placeholder "Message…"],    -- controlled input
    button [disabled (m.pending || m.draft.trim.isEmpty), onClick .send] "Send"
  ]

def chatApp : App Model Msg := application init update view effects
```

### A keyed list of reusable rows

Each row is its own `Component` — its state, messages, `update`, and `view` — and
carries a `key` (like React's `key`). So add, remove, and sort move whole rows: a
row that moves keeps its DOM node, its local state, and any focus inside it.

```lean
namespace Row                       -- a self-contained row: its own state + messages
  structure Model where
    id   : Nat                      -- the row's key
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
  | row (i : Nat) (msg : Row.Msg)   -- a click inside row i
  | remove (id : Nat)
  | sort

def update (m : Model) : Msg → Model
  | .edit s    => { m with draft := s }
  | .add       => let t := m.draft.trim
                  if t.isEmpty then m
                  else { m with rows   := m.rows.push { id := m.nextId, text := t, done := false }
                                draft  := "", nextId := m.nextId + 1 }
  | .row i msg => { m with rows := Row.component.updateAt m.rows i msg }
  | .remove id => { m with rows := m.rows.filter (·.id != id) }
  | .sort      => { m with rows := m.rows.qsort (fun a b => compare a.text b.text == .lt) }

def view (m : Model) : Html Msg :=
  div [cls "todo"] [
    div [cls "add"] [
      input  [value m.draft, onInput .edit, placeholder "What needs doing?"],
      button [onClick .add]  "Add",
      button [onClick .sort] "Sort"
    ],
    ul [cls "items"] (m.rows.mapIdx fun i r =>
      li [key (toString r.id)] [               -- keyed: this row keeps its node when it moves
        (Row.component.view r).map (Msg.row i),
        button [cls "rm", onClick (.remove r.id)] "✕"
      ]).toList
  ]
```

The full app is `Examples/Todo.lean`; `test/todo_test.mjs` drives it in a browser.

### Routing, data fetching, and events

`routed` wires the verified `Router` to the URL: `link`s and back/forward navigate
without a page reload, and the new path is parsed into a route (`Router.fromURL`,
round-trip proven). `Cmd.getJson` fetches and decodes a JSON response with
`Qed.Json`. A `<form>` submits on Enter or its button (`onSubmit`), and
`onKeydown`/`onFocus`/`onBlur` round out the events.

```lean
router R where
  home => ""
  user (name : String) => "users"

jsonStruct Profile where
  name : String
  bio  : String

def effects (m : Model) : Msg → Cmd Msg
  | .submit       => .pushUrl (Router.toURL (R.user m.query))   -- navigate, no reload
  | .urlChanged _ => match m.route with
      | .user name => Cmd.getJson s!"/api/users/{name}"          -- GET + decode Profile
                        (fun p => .gotProfile (.ok p)) (fun e => .gotProfile (.error e))
      | _          => .none
  | _ => .none

def view (m : Model) : Html Msg :=
  formEl [onSubmit .submit] [
    input [value m.query, onInput .typeQuery, onKeydown .key],   -- Enter submits, Escape clears
    link "/users/ada" [] "ada"                                    -- a routed link (no reload)
  ]

def app : App Model Msg :=
  routed init update view (onUrlChange := Msg.urlChanged) (effects := effects)
```

`Examples/Users.lean` is the full app; `test/users_test.mjs` drives it against a mock
API — a deep link, link/submit navigation, back/forward, and the events.

## How it works

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

On each event the new view is diffed against the previous one and only the
changed nodes are patched — so the proven `diff_apply` theorem (above)
guarantees the DOM equals the new view, while untouched nodes keep their identity
(focus, cursor, scroll, selection all survive an update).

`update` returns `(model, Cmd)`. The driver runs the `Cmd` *after* the render:
`Cmd.stream` performs a streaming `fetch` whose Server-Sent-Events dispatch
`.chunk`/`.done` messages back through the same loop, so async stays pure data.

The only impure, unverified surface is `Qed/Dom.lean` (a handful of `@[extern]`
node primitives, incl. a streaming fetch) and its C/JS implementation in
`runtime/`. Everything above that line is pure, total Lean. Events cross back by
id and are looked up totally (`Array.get?`), so a bad event id can never crash the app.

## The `qed` CLI

The toolchain is a single command with a vocabulary web devs already know.
Verification runs as part of every `build`/`dev`/`check`: the Lean kernel checks
your proofs (a failed proof is a build error), the sources are grepped for
`sorry`/`admit`/`native_decide`, and the axiom manifest is run.

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

`npm run dev` / `build` / `test` / … work too (see `package.json`) for muscle
memory. When hacking on the framework itself, the in-repo `./qed` shim runs the
CLI against this checkout.

## Layout

| Path | What |
|------|------|
| `Qed/Html.lean` | The core typed virtual DOM — the elaboration target. |
| `Qed/Notation.lean` | Readable view combinators (`div`, `button`, `onClick`, …). |
| `Qed/Runtime.lean` | The Elm Architecture (`App`, `sandbox`, `application`, `routed`), `Cmd` effects (`stream`/`now`/`request`/`getJson`/`pushUrl`) + pure render-to-HTML. |
| `Qed/Invariant.lean` | The `invariant … preserved_by …` command (auto-proven). |
| `Qed/Diff.lean` | The diff/patch engine — positional length-general reconcile (add/remove) and keyed reconcile (reorder/remove by `key`) + the `diff_apply` correctness proof. |
| `Qed/Json.lean` | Full JSON parser/renderer + `jsonStruct`/`jsonCodec` + `parse_depth_le` & `parse_render` proofs. |
| `Qed/Router.lean` | The `Router` class (round-trip law as a field) + the `router` command (generates the route enum, `print`/`parse`, the round-trip proof, and the instance) + `toURL`/`fromURL` for the browser. |
| `Qed/Form.lean` | Typed refinement fields (`Field p`), the `Input` controls (text/number/checkbox/date/select/radios), and the `form` command (Draft + `parse` + `formView` + the `canSubmit_iff` proof). |
| `Qed/Date.lean` | A calendar `Date` that can't be invalid (smart constructor + ISO parser; impossible dates parse to `none`). |
| `Qed/Component.lean` | `Component` (a reusable `update`+`view`) + `viewList`/`updateAt` for repeating it per row. |
| `Qed/Dom.lean` | The `@[extern]` DOM node primitives (the trusted boundary). |
| `Qed/Driver.lean` | The impure browser driver (build + patch) + `@[export]`ed entry points. |
| `Examples/` | Example programs. |
| `Cli.lean` + `./qed` | The toolchain (build/dev/test/check/…) and its shim. |
| `runtime/` | C/JS driver, pages, dev server. |
| `test/` | Browser tests: counter (`browser_test.mjs`), chat screenshots (`chat_test.mjs`), form (`signup_test.mjs`), current-time (`booking_test.mjs`), dynamic list (`todo_test.mjs`), routing/http/events (`users_test.mjs`) + mock LLM (`mock_llm.py`). |
| `scripts/axioms.lean` | Axiom manifest gated by `qed check`/`qed build`. |
