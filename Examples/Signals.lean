/-
  Signals — fine-grained reactivity, the escape hatch below the diff. An element bound
  with `signalText name` / `[signalBind name]` has its text driven by a *signal* whose
  value lives in the driver, not the model. `Cmd.setSignal name v` (or, from outside the
  app, `window.qed.setSignal(name, v)`) updates *only* the bound elements — no message,
  no `update`, no diff, no tree walk. The `renders` counter below is bumped only by the
  button, so the test can prove that setting a signal does NOT re-render the view.

  Use it for high-frequency or externally-pushed values (a clock, a socket feed, a
  progress bar) where routing through model + update + diff would be wasteful.

  Pure Lean; the browser entry is `Examples/SignalsWeb.lean`.
-/
import Qed
open Qed

namespace Signals

structure Model where
  renders : Nat        -- bumped only by `ping`, never by a signal update

def init : Model := { renders := 0 }

inductive Msg | ping

def update (m : Model) : Msg → Model
  | .ping => { m with renders := m.renders + 1 }

def app : App Model Msg := ui init update fun m =>
  div [cls "signals"] [
    div [cls "row"] ["a = ", signalText "a"],
    div [cls "row"] ["b = ", signalText "b"],
    button [attr "id" "ping", cls "ping", onClick .ping] "re-render",
    div [cls "renders", attr "id" "renders"] [text (toString m.renders)]
  ]

end Signals
