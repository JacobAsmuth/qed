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

### The counter

The whole app: the state, the messages it answers, a total `update`, a typed
`view`, and one stated invariant. `lake build` rejects it unless every message is
handled, both functions terminate, and the invariant's proof discharges.

```lean
import Qed
open Qed

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

### Reading JSON, with errors handled

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
step is an `Option`, so the wrong shape is just `none` — no exceptions:

```lean
def cityOf (body : String) : Option String :=
  (Json.parse body).toOption
    |>.bind (·.path? ["address", "city"])
    |>.bind (·.str?)
```

### A form that can't carry invalid data

A field is a *typed* refinement: `Field p` (for `p : α → Prop`) is a value of type
`α` paired with a proof that `p` holds of it. Its only constructor is validation, so
a `Signup` value is itself evidence that every field is valid — an invalid form is
unrepresentable, and any handler taking one can't run on bad input.

Each field names a control: `Input.text`, `Input.nat`/`Input.int`, `Input.checkbox`
(a `Bool`), `Input.date` (a verified `Qed.Date` — `2026-02-30` parses to `none`),
`Input.select`/`Input.radios`. The value is *parsed* from the raw string first (a
number, a real calendar date), then refined with `.refine spec`. From the one
declaration, `form` generates the editable `Draft`, the validated `Signup`,
`Signup.parse : Draft → Option Signup`, the `canSubmit` gate and its `canSubmit_iff`
proof, and `Signup.formView` — so the widgets, the submit-disabled-unless-valid gate,
and the field names are written once.

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

`Examples/Signup.lean` is the full app; `test/signup_test.mjs` drives it in a real
browser — filling each control, toggling the checkbox, and asserting the submit
button enables only once every field is valid.

A rule can also depend on the **current time**. `form` takes context binders that
thread into the gate, and `Cmd.now` reads the clock into the model as data (`view`
and `update` stay pure):

```lean
form Appt (today : Date) where
  when : Input.date.refine (fun d => today < d)   -- must be after today

-- read the clock once at startup, then render the form with `today` in scope
def app : App Model Msg :=
  { init := (init, .now .gotToday), update := …, view := … }
```

`Examples/Booking.lean` is the full app; `test/booking_test.mjs` drives it against
the real clock — a past date keeps submit disabled, a future date enables it.

### Effects: a streaming LLM chat

Side effects are *data*. `update` stays a pure `Model → Msg → Model`; a separate
`effects` function maps a message to the `Cmd` to run after it, which the driver
interprets. `Cmd.stream` POSTs and reads the response as it arrives, dispatching
`.chunk` per Server-Sent-Event and `.done` at the end — so a token-by-token LLM
reply is just more messages through the same `update`. `onInput` captures the
composer text. JSON in and out goes through the verified `Qed.Json`.

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

The full app is `Examples/Chat.lean`; `test/chat_test.mjs` drives it in headless
Chromium against a mock OpenAI streaming backend (`test/mock_llm.py`) and saves a
screenshot at each stage (`qed test`).

### Reusable components, one per data row

A `Component Model Msg` bundles an `update` and a `view` over its own state and its
own message type. To repeat it per row — one box per entry in a decoded JSON array —
`viewList` renders each row and tags its messages with the row index, and `updateAt`
routes a tagged message back to that one row. A click in row 2 arrives as
`Msg.box 2 …` and updates only row 2.

```lean
jsonStruct Entry where
  name  : String
  score : Nat

namespace Box                                   -- a self-contained, reusable box
  structure Model where entry : Entry; expanded : Bool
  inductive Msg | toggle
  def update (m : Model) : Msg → Model
    | .toggle => { m with expanded := !m.expanded }
  def view (m : Model) : Html Msg :=
    div [cls (if m.expanded then "box open" else "box"), onClick .toggle]
      [ h2 [] [m.entry.name], span [cls "score"] [m.entry.score] ]   -- Nat needs no toString
  def component : Component Model Msg := { update, view }
end Box

structure Model where boxes : Array Box.Model
inductive Msg | box (i : Nat) (msg : Box.Msg)     -- a message names the row it came from

def update (m : Model) : Msg → Model
  | .box i bm => { m with boxes := Box.component.updateAt m.boxes i bm }

def view (m : Model) : Html Msg :=
  div [cls "boxes"] (Box.component.viewList m.boxes Msg.box)
```

A component lowers to ordinary `Html` through `Html.map`, so it adds no axioms and
the totality and diff/patch proofs already cover a composed view — nesting buys no
new trust assumptions. The full example, decoding a JSON array into a list of
boxes, is `Examples/Boxes.lean`.

## How it works

```
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
| `Qed/Runtime.lean` | The Elm Architecture (`App`, `sandbox`, `application`), `Cmd` effects + pure render-to-HTML. |
| `Qed/Invariant.lean` | The `invariant … preserved_by …` command (auto-proven). |
| `Qed/Diff.lean` | The diff/patch engine + the `diff_apply` correctness proof. |
| `Qed/Json.lean` | Full JSON parser/renderer + `jsonStruct`/`jsonCodec` + `parse_depth_le` & `parse_render` proofs. |
| `Qed/Router.lean` | The `Router` class (round-trip law as a field) + the `router` command (generates the route enum, `print`/`parse`, the round-trip proof, and the instance). |
| `Qed/Form.lean` | Typed refinement fields (`Field p`), the `Input` controls (text/number/checkbox/date/select/radios), and the `form` command (Draft + `parse` + `formView` + the `canSubmit_iff` proof). |
| `Qed/Date.lean` | A calendar `Date` that can't be invalid (smart constructor + ISO parser; impossible dates parse to `none`). |
| `Qed/Component.lean` | `Component` (a reusable `update`+`view`) + `viewList`/`updateAt` for repeating it per row. |
| `Qed/Dom.lean` | The `@[extern]` DOM node primitives (the trusted boundary). |
| `Qed/Driver.lean` | The impure browser driver (build + patch) + `@[export]`ed entry points. |
| `Examples/` | Example programs. |
| `Cli.lean` + `./qed` | The toolchain (build/dev/test/check/…) and its shim. |
| `runtime/` | C/JS driver, pages, dev server. |
| `test/` | Browser tests: counter (`browser_test.mjs`) + chat screenshots (`chat_test.mjs`) + mock LLM (`mock_llm.py`). |
| `scripts/axioms.lean` | Axiom manifest gated by `qed check`/`qed build`. |
