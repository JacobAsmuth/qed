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
    other rows untouched. The dual of `viewList` for the parent's `update`.

    *Positional*: `i` is an array index, so an in-flight message can land on the
    wrong row if the list reorders between render and dispatch. Prefer `updateKeyed`
    (routes by a stable key) for lists that sort/reorder. -/
def updateAt (c : Component Model Msg) (models : Array Model) (i : Nat) (msg : Msg) :
    Array Model :=
  models.modify i (c.update · msg)

/-- Route a child message to the row whose `key` matches `k` and run that row's
    transition, leaving the others untouched. Unlike `updateAt`, routing is by a
    stable key (the same identity the keyed `diff` reconciles by), so a message
    survives the list being sorted or filtered between render and dispatch — the
    React way of addressing a child by identity, not position. -/
def updateKeyed (c : Component Model Msg) (key : Model → String)
    (models : Array Model) (k : String) (msg : Msg) : Array Model :=
  models.map fun r => if key r == k then c.update r msg else r

end Component

/-! ### The `embed` command

`embed Child as ctor keyedBy keyFn into field` removes the per-child wiring tax of
embedding a reusable `Component` in a keyed list. Given a child *namespace* `Child`
(providing `Child.component`, `Child.Model`, `Child.Msg`) it generates, in the
current namespace:

* `ctorView   : Child.Model → Html Msg` — the child's view with its messages tagged
  by the parent constructor `Msg.ctor key`, so a child event routes back as a parent
  message carrying the row's stable key;
* `ctorUpdate : Model → String → Child.Msg → Model` — runs the child's transition on
  the row in `field` whose key matches, via `updateKeyed` (routing by key, not index,
  so a sort/filter between render and dispatch can't misroute it).

The one line the macro cannot write (Lean cannot extend an existing `inductive`) is
the parent message constructor: add `| ctor (k : String) (msg : Child.Msg)` to your
`Msg`. The `update` arm is then `| .ctor k msg => ctorUpdate m k msg`, and the view
drops to `ctorView r`. Core-syntax only (no `import Lean`), like `router`/`form`. -/
syntax (name := embedCmd)
  "embed " ident " as " ident " keyedBy " term " into " ident : command

open Lean in
macro_rules
  | `(embed $child:ident as $ctor:ident keyedBy $keyFn:term into $field:ident) => do
      let comp     := mkIdent (child.getId ++ `component)
      let childMod := mkIdent (child.getId ++ `Model)
      let childMsg := mkIdent (child.getId ++ `Msg)
      let pModel   := mkIdent `Model
      let pMsg     := mkIdent `Msg
      let pMsgCtor := mkIdent (`Msg ++ ctor.getId)
      let viewName := mkIdent (Name.mkSimple (ctor.getId.toString ++ "View"))
      let updName  := mkIdent (Name.mkSimple (ctor.getId.toString ++ "Update"))
      `(def $viewName (r : $childMod) : Html $pMsg :=
          (($comp).view r).map ($pMsgCtor ($keyFn r))
        def $updName (m : $pModel) (k : String) (msg : $childMsg) : $pModel :=
          { m with $field:ident := ($comp).updateKeyed $keyFn m.$field k msg })

end Qed
