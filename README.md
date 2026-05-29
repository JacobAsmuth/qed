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

The design rule is *outside-in*: start from the most readable, maximally-proven
Lean a developer would want to write, then build whatever elaboration machinery
(macros, `deriving`, refinement types, proof automation) makes that surface real.
The macros and notation elaborate into that small typed core, so they don't change
what is proven.

## The counter, in full

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
    button [onClick .decrement] [text "−"],
    span   [cls "count"]        [text (toString m.count)],
    button [onClick .increment] [text "+"],
    button [onClick .reset]     [text "reset"]
  ]

def app : App Model Msg := sandbox init update view

-- State the safety property; the framework proves it for every transition.
invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update
```

That's the whole app. `lake build` checking it green *is* the proof that it is
total and that `counterSafe` holds.

![the counter running in a browser](runtime/counter.png)

## Proven building blocks

Beyond the runtime, Qed ships verified pieces for the things frontends actually
do. Each states a spec and the framework discharges the proof — you never write
one by hand. (Axioms below are all sound Lean foundations; none use `sorry`.)

**Verified VDOM diff/patch** (`Qed/Diff.lean`). The incremental update path is
proven identical to a full re-render, so the DOM can never drift from your view:

```lean
theorem diff_apply (a b : Html msg) : applyPatch (diff a b) a = b
```

**Depth-bounded JSON** (`Qed/Json.lean`). The developer picks a maximum nesting
depth; a hostile input can never exceed it. Termination is free (structural
recursion on a fuel counter), and the bound is a theorem:

```lean
def parse (maxDepth : Nat) (s : String) : Except String Json
theorem parse_depth_le : parse maxDepth s = .ok j → j.depth ≤ maxDepth
```

**Round-tripping routes** (`Qed/Router.lean`). The round-trip law is a *field of
the `Router` class*, so an instance cannot exist without it — no route is
unreachable, no URL fails to parse back:

```lean
inductive Route | home | about | post (slug : String) | user (name : String)
theorem Route.round_trip (r : Route) : parse (print r) = some r   -- by `cases r <;> simp`
```

**Forms where submit-enabled ⇔ valid** (`Qed/Form.lean`). Fields are refinement
types (a value carries its proof of validity), so an invalid form is
unrepresentable and the submit gate *is* the validity decision:

```lean
structure Signup where               -- can only be built from valid input
  email : Refined isEmail
  age   : Refined isAdult
theorem Signup.canSubmit_iff : canSubmit email age = true ↔ isEmail email ∧ isAdult age
```

## How it works

```
Lean app (Model, Msg, update, view, deriving/invariant — proofs auto-discharged)
   │  lake build         (Lean → C, in .lake/build/ir/*.c)
   ▼
emcc  (app C  +  runtime/qed_dom.c [EM_JS DOM shims]  +  prebuilt Lean wasm runtime)
   ▼
runtime/qed.js (MODULARIZE factory) + qed.wasm
   ▼
runtime/host.js:  qed_run_init() mounts;  DOM event → qed_run_dispatch(id)
                  → pure `update` → diff vs. previous view → patch only what changed
```

On each event the new view is diffed against the previous one and only the
changed nodes are patched — so the proven `diff_apply` theorem (see below)
guarantees the DOM equals the new view, while untouched nodes keep their identity
(focus, cursor, scroll, selection all survive an update).

The only impure, unverified surface is `Qed/Dom.lean` (a handful of `@[extern]`
node primitives) and its C/JS implementation in `runtime/`. Everything above that
line is pure, total Lean. Events cross back by id and are looked up totally
(`Array.get?`), so a bad event id can never crash the app.

## The `qed` CLI

The toolchain is a single command with a vocabulary web devs already know.
Verification runs as part of every `build`/`dev`/`check`: the Lean kernel checks
your proofs (a failed proof is a build error), the sources are grepped for
`sorry`/`admit`/`native_decide`, and the axiom manifest is run.

```bash
./qed dev      # watch sources, rebuild, serve with live-reload  → localhost:8000
./qed build    # production build → dist/ (optimized + verified)
./qed start    # serve the build            (alias: preview)
./qed test     # headless browser test suite
./qed check    # verify only: proofs + no-sorry + axiom-clean, no artifacts
./qed clean    # remove build outputs
./qed new APP  # scaffold a new app
```

`npm run dev` / `build` / `test` / … work too (see `package.json`) for muscle
memory. Prerequisites: [`elan`](https://github.com/leanprover/elan) (pins Lean
v4.15.0) and the [emscripten SDK](https://emscripten.org) at `~/emsdk`; the
`./qed` shim wires both into the environment.

## Layout

| Path | What |
|------|------|
| `Qed/Html.lean` | The core typed virtual DOM — the elaboration target. |
| `Qed/Notation.lean` | Readable view combinators (`div`, `button`, `onClick`, …). |
| `Qed/Runtime.lean` | The Elm Architecture (`App`, `sandbox`) + pure render-to-HTML. |
| `Qed/Invariant.lean` | The `invariant … preserved_by …` command (auto-proven). |
| `Qed/Diff.lean` | The diff/patch engine + the `diff_apply` correctness proof. |
| `Qed/Json.lean` | Depth-bounded JSON parser + the `parse_depth_le` proof. |
| `Qed/Router.lean` | The `Router` class (round-trip law as a field) + a route table. |
| `Qed/Form.lean` | Refinement-typed forms + the `canSubmit_iff` proof. |
| `Qed/Dom.lean` | The `@[extern]` DOM node primitives (the trusted boundary). |
| `Qed/Driver.lean` | The impure browser driver (build + patch) + `@[export]`ed entry points. |
| `Examples/Counter.lean` | The demo app (shared by both entry points). |
| `Examples/Native.lean` / `Examples/Web.lean` | Native / WASM entry points. |
| `Cli.lean` + `./qed` | The toolchain (build/dev/test/check/…) and its shim. |
| `runtime/` | C/JS driver, page, dev server. |
| `scripts/axioms.lean` | Axiom manifest gated by `qed check`/`qed build`. |

## Notable constraints

- **Lean is pinned to v4.15.0** — it is the *last* release that ships the
  prebuilt `linux_wasm32` toolchain (v4.16+ dropped it), which supplies the Lean
  runtime already compiled for wasm so we never build it ourselves.
- **`runtime/uv_stubs.c`** defines four libuv temp-file symbols that `libleanrt`
  references but the wasm toolchain doesn't bundle. A frontend never calls them;
  the stubs keep the linker strict.
- The WASM build is **emscripten, not WASI** (Lean uses C++ exceptions) and uses
  `-pthread`, so the page must be served cross-origin-isolated (see `serve.py`).

## Roadmap

**Done** (all kernel-checked, `sorry`-free — run `./qed check`):
the verified core, an end-to-end browser slice, the verified diff/patch engine,
state-machine invariants, depth-bounded JSON, round-tripping routes, and
refinement-typed forms.

**Next:**

- **`Cmd`-based effects** — async/data-fetching as data, so `update` stays pure
  and total: `update : Model → Msg → Model × Cmd Msg`, with the JS driver
  interpreting fetch/timer commands.
- **Keyed reconciliation** — extend the diff proof to matched/moved children (the
  current proof is exact for positional children).
- **`deriving Router` / `deriving Form`** — generate the instances above from the
  type alone, so even the boilerplate disappears (the proofs already auto-discharge).
