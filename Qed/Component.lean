/-
  Qed.Component — reusable, nestable view components.

  A `Component Model Msg` bundles a `Model → Msg → Model` transition with a
  `Model → Html Msg` view: the reusable behaviour of a self-contained piece of UI,
  with its own state and message type. Because the message type is the component's
  own, a parent embeds a child by *relabelling* the child's messages into its own
  (`Html.map`), so a click inside a child is delivered as a parent message — the
  types make a misrouted event impossible.

  The list helpers (`viewList`/`updateAt`) cover the common case of the same
  component repeated per data row (e.g. one box per entry in a decoded JSON array):
  each row's messages are tagged with the row index, so a parent message carries
  *which* row produced it.

  Everything here is pure sugar over `Html.map`; it adds no axioms and links on
  every target. A child that needs effects (`Cmd`) is not modelled yet — promote it
  with `toApp` and run it as its own application, or thread effects in the parent.
-/
import Qed.Html
import Qed.Runtime

namespace Qed

/-- A reusable piece of UI: a transition over its own state and a view producing
    its own messages. `init` is deliberately absent — a component is instantiated
    from data by its embedder (one model per row), so the starting state is the
    caller's to choose. -/
structure Component (Model : Type) (Msg : Type) where
  /-- The pure, total transition over the component's local state. -/
  update : Model → Msg → Model
  /-- The pure, total view, producing the component's own messages. -/
  view   : Model → Html Msg

namespace Component
variable {Model Msg PMsg : Type}

/-- Run a component as a standalone application (no effects). Useful for testing a
    component in isolation, or when it *is* the whole app. -/
def toApp (c : Component Model Msg) (init : Model) : App Model Msg :=
  sandbox init c.update c.view

/-- Embed a single child: render it and relabel its messages into the parent's
    `Msg` via `wrap`. The parent's transition for `wrap cm` runs `c.update` on the
    child's slice of the model. -/
def render (c : Component Model Msg) (wrap : Msg → PMsg) (m : Model) : Html PMsg :=
  (c.view m).map wrap

/-- Render the same component once per row, tagging each row's messages with its
    index: `tag i cm` is the parent message for child message `cm` from row `i`.
    The result is a child list ready to drop into `div [..] (…)`. -/
def viewList (c : Component Model Msg) (models : Array Model)
    (tag : Nat → Msg → PMsg) : List (Html PMsg) :=
  (models.mapIdx fun i m => (c.view m).map (tag i)).toList

/-- Route a child message to row `i` and run that row's transition, leaving the
    other rows untouched. The dual of `viewList` for the parent's `update`. -/
def updateAt (c : Component Model Msg) (models : Array Model) (i : Nat) (msg : Msg) :
    Array Model :=
  models.modify i (c.update · msg)

end Component
end Qed
