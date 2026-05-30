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

`Json.parse` assumes the worst - it's total*, so it never throws; bad input just comes back as an
honest `.error` value.

"Depth-bounded" is the part worth actually showing, since it's the kind of thing
that's easy to just claim. `parse` takes a depth budget (it defaults to 64) - nest
deeper than that and the parse bounces off instead of recursing until your stack
gives out. The `.map Json.depth` below is only there so the result prints - try it:

```lean
#eval (Json.parse "[[[]]]" (maxDepth := 3)).map Json.depth   -- Except.ok 3   (depth 3 fits a budget of 3)
#eval (Json.parse "[[[]]]" (maxDepth := 2)).map Json.depth   -- Except.error "maximum depth exceeded"
```

`parse_depth_le` proves that budget is the ceiling.
Whatever `parse s budget` accepts is guaranteed to nest no deeper than `budget` - so a
hostile, ten-thousand-level-deep blob can't slip past.

Most of the time, though, you just want to decode the thing as a struct. `jsonStruct` writes the
tedious `ToJson`/`FromJson` for you - you list the fields exactly once - so decoding a
response body is a `do` block in the `Except` monad:

```lean
jsonStruct User where
  name : String
  age  : Nat                   -- a Nat can't be negative, so "age": -3 is rejected for free
  bio  : Option String         -- Option means "this one's allowed to be missing (or null)"

def decodeUser (body : String) : Except String User := do
  let json ← Json.parse body   -- garbage or too-deeply-nested input stops right here, as an .error
  fromJson json                -- and a bad field names itself: "age: expected a non-negative integer"
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
  | row (i : Nat) (msg : Row.Msg)   -- a message bubbling up from inside row i
  | remove (id : Nat)
  | sort

def update (m : Model) : Msg → Model
  | .edit s    => { m with draft := s }
  | .add       => let t := m.draft.trim
                  if t.isEmpty then m
                  else { m with rows   := m.rows.push { id := m.nextId, text := t, done := false }
                                draft  := "", nextId := m.nextId + 1 }
  | .row i msg => { m with rows := Row.component.updateAt m.rows i msg }   -- route it to that one row
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
      li [key (toString r.id)] [               -- the key. Move this row and its DOM node tags along.
        (Row.component.view r).map (Msg.row i),  -- the row's own view, its messages stamped "row i"
        button [cls "rm", onClick (.remove r.id)] "✕"
      ]).toList
  ]
```

The whole app is `Examples/Todo.lean`, and `test/todo_test.mjs` drives it in a real
browser (it even checks that a row's DOM node survives a sort).

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

Every time something happens, Qed re-runs your `view`, diffs the new tree against
the last one, and patches *only* the bits that actually changed. Notice what that
buys you: the input you're typing in is never rebuilt, so your cursor, your text
selection, and your scroll position all survive the update. And this isn't
hand-waving — `diff_apply` is a theorem that says the patched DOM equals the new
view, exactly.

Remember the bit about `update` staying pure? It returns `(model, Cmd)`, and the
driver runs the `Cmd` *after* the render — a `Cmd.stream` kicks off a streaming
`fetch` whose events come back in as `.chunk`/`.done` messages. So "async" never
escapes being plain data flowing through the same loop.

There's exactly one impure corner in the whole thing: `Qed/Dom.lean`, a short list
of `@[extern]` calls that poke the real DOM. Everything above that line is pure,
total Lean. Even events come back across the boundary as integer ids and get looked
up safely (`Array.get?`), so a stray id can't take the app down with it.

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
| `Qed/Runtime.lean` | The Elm Architecture (`App`, `sandbox`, `application`, `routed`), the `Cmd` effects (`stream`/`now`/`request`/`getJson`/`pushUrl`), and the pure render-to-HTML. |
| `Qed/Invariant.lean` | The `invariant … preserved_by …` command (it discharges the proof for you). |
| `Qed/Diff.lean` | The diff/patch engine — positional reconcile (add/remove) and keyed reconcile (reorder by `key`) — plus the `diff_apply` correctness proof. |
| `Qed/Json.lean` | The full JSON parser/renderer + `jsonStruct`/`jsonCodec`, with the `parse_depth_le` & `parse_render` proofs. |
| `Qed/Router.lean` | The `Router` class (round-trip law baked in as a field), the `router` command, and `toURL`/`fromURL` for the browser. |
| `Qed/Form.lean` | Typed refinement fields (`Field p`), the `Input` controls (text/number/checkbox/date/select/radios), and the `form` command (Draft + `parse` + `formView` + the `canSubmit_iff` proof). |
| `Qed/Date.lean` | A calendar `Date` that can't be invalid (smart constructor + ISO parser; impossible dates parse to `none`). |
| `Qed/Component.lean` | `Component` (a reusable `update`+`view`) + `viewList`/`updateAt` for repeating one per row. |
| `Qed/Dom.lean` | The `@[extern]` DOM primitives — the one trusted boundary. |
| `Qed/Driver.lean` | The impure browser driver (build + patch) + the `@[export]`ed entry points. |
| `Examples/` | Example programs. |
| `Cli.lean` + `./qed` | The toolchain (build/dev/test/check/…) and its shim. |
| `runtime/` | The C/JS driver, the page, and the dev server. |
| `test/` | Browser tests: counter (`browser_test.mjs`), chat (`chat_test.mjs`), form (`signup_test.mjs`), current-time (`booking_test.mjs`), dynamic list (`todo_test.mjs`), routing/http/events (`users_test.mjs`) + the mock LLM (`mock_llm.py`). |
| `scripts/axioms.lean` | The axiom manifest that `qed check`/`qed build` gate on. |
