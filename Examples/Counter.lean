/-
  Tour 01 · The architecture

  The whole shape of a Qed app: a `Model` (the state), a `Msg` (every event), a pure
  total `update`, a JSX `view`, and `ui` to build the `App`. Plus the first invariant:
  state a property of the model and the build proves every transition preserves it.

  This module is only the *application*; the entry points that run it live in
  `Examples/Native.lean` (renders to stdout) and `Examples/Web.lean` (mounts in the
  browser), so the same verified `app` drives both targets.
-/
import Qed

open Qed

/-- The entire application state. -/
structure Model where
  count : Int
deriving Repr, Inhabited

/-- Every event the UI can produce. `update` must handle all of them, a missing
    case is a compile error, so the UI logic cannot "forget" an event. -/
inductive Msg where
  | increment
  | decrement
  | reset
deriving Repr

def init : Model := { count := 0 }

/-- The pure, total transition. `decrement` is guarded so the count never drops
    below zero, and the framework proves that for us just below. -/
def update (m : Model) : Msg → Model
  | .increment => { m with count := m.count + 1 }
  | .decrement => { m with count := if 0 < m.count then m.count - 1 else m.count }
  | .reset     => { m with count := 0 }

-- The view is JSX, but every event is a typed `Msg`, so a typo such as
-- `onClick={.incremnt}` would not compile. `ui` builds the app from it.
def app : App Model Msg := ui init update fun m =>
  <div class="counter">
    <button onClick={.decrement}>−</button>
    <span class="count">{m.count}</span>
    <button onClick={.increment}>+</button>
    <button onClick={.reset}>reset</button>
    -- Untracked DOM state: only the count above is bound to the model, so typing
    -- here keeps its value, focus, and cursor across every click.
    <input placeholder="type here, focus survives every click"/>
  </div>

-- State the safety property; the framework generates and machine-checks that *every*
-- transition preserves it. No proof written by hand.
invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update
