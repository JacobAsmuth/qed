/-
  Messages that read the model stay live.

  A handler's message can embed model state — `onClick (.setTo (m.n * 2))` — not just a
  constant. The driver keeps such a handler current across updates (it re-registers into the
  element's existing slot rather than baking the build-time value), so "double" always doubles
  the number on screen, not the number that was there when the page first rendered.
-/
import Qed
open Qed

namespace Live

structure Model where
  n : Int

inductive Msg
  | inc
  | setTo (v : Int)

def update (m : Model) : Msg → Model
  | .inc     => { m with n := m.n + 1 }
  | .setTo v => { n := v }

def app : App Model Msg :=
  ui { n := 0 } update fun m =>
    div [cls "live"] [
      p [cls "n"] [text (toString m.n)],
      button [cls "inc", onClick .inc] [text "+1"],
      -- these messages embed the *current* model; they must not go stale after an update
      button [cls "double", onClick (.setTo (m.n * 2))] [text "double"],
      button [cls "plus10", onClick (.setTo (m.n + 10))] [text "+10"],
      -- a DOM event with no named-helper history of its own: the event set is open, so
      -- `onDoubleClick` (= `on "dblclick"`) just works, delegated like any other.
      button [cls "reset", onDoubleClick (.setTo 0)] [text "reset (dbl-click)"]
    ]

end Live
