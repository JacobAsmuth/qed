/-
  The counter demo — pure Lean, total by elaboration, with a machine-checked
  state-machine invariant. This module defines only the *application*; the thin
  entry points that run it live in `Examples/Native.lean` (renders to stdout) and
  `Examples/Web.lean` (mounts in the browser), so the same verified `app` drives
  both targets.
-/
import Qed

open Qed

/-- The entire application state. -/
structure Model where
  count : Int
deriving Repr, Inhabited

/-- Every event the UI can produce. `update` must handle all of them — a missing
    case is a compile error, so the UI logic cannot "forget" an event. -/
inductive Msg where
  | increment
  | decrement
  | reset
deriving Repr

def init : Model := { count := 0 }

/-- The pure, total transition. `decrement` is guarded so the count never drops
    below zero — and the framework proves that for us just below. -/
def update (m : Model) : Msg → Model
  | .increment => { m with count := m.count + 1 }
  | .decrement => { m with count := if 0 < m.count then m.count - 1 else m.count }
  | .reset     => { m with count := 0 }

/-- The view — reads like markup, but every event is a typed `Msg`, so a typo
    such as `onClick .incremnt` would not compile. -/
def view (m : Model) : Html Msg :=
  div [] [
    div [cls "counter"] [
      button [onClick .decrement] "−",
      span   [cls "count"]        [toString m.count],
      button [onClick .increment] "+",
      button [onClick .reset]     "reset"
    ],
    -- This input is never rebuilt by an update: the diff engine only patches the
    -- count text above, so whatever you type here keeps its focus and cursor.
    input [placeholder "type here — focus survives every click"],
    -- A memoized subtree: its key never changes, so after the first render the diff
    -- skips it — the driver never touches this DOM again, no matter how you click.
    lazy "banner" (div [cls "banner", attr "id" "banner"] ["built once, then memoized"])
  ]

def app : App Model Msg := sandbox init update view

-- Dream-API #3: we state the safety property; the framework generates and
-- machine-checks that *every* transition preserves it. No proof written by hand.
invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update
