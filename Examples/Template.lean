/-
  A `View` template demo: the same Elm-Architecture app (pure `init`/`update`), but the
  view is a `View Model Msg` *template* rather than a `Model → Html Msg` function.

  Every dynamic value is a projection of the scope — `dyn (·.name)`, `dyn (·.count)` —
  so the browser driver updates just those nodes on a change, no tree walk (the value
  still lives in the model; `update` stays pure). Structure that changes shape uses the
  two combinators: `showIf` (conditional) and `forEach` (keyed list). The list row is a
  `View Todo Msg`, scoped to its row, with a scope-bound event (`onClick' …`).

  Pure Lean; the browser entry is `Examples/TemplateWeb.lean`.
-/
import Qed
open Qed (View App templated)
open Qed.V

namespace TemplateDemo

structure Todo where
  id   : Nat
  text : String
  done : Bool
deriving Inhabited

structure Model where
  count : Nat
  name  : String
  todos : Array Todo
  nextId : Nat

def init : Model :=
  { count := 0, name := "", nextId := 3
    todos := #[{ id := 1, text := "learn Lean", done := true },
               { id := 2, text := "write a template", done := false }] }

inductive Msg
  | inc | dec
  | setName (s : String)
  | toggle (id : Nat)
  | add

def update (m : Model) : Msg → Model
  | .inc        => { m with count := m.count + 1 }
  | .dec        => { m with count := m.count - 1 }
  | .setName s  => { m with name := s }
  | .toggle id  => { m with todos := m.todos.map fun t => if t.id == id then { t with done := !t.done } else t }
  | .add        => { m with todos := m.todos.push { id := m.nextId, text := s!"item {m.nextId}", done := false },
                            nextId := m.nextId + 1 }

/-- The row template — scoped to a `Todo`. Its text reads the row (a check mark when
    done); the toggle message reads the row's id (`onClick'`). The text is a signal, so a
    toggle updates just this row's node — no diff, no `childAt`. -/
def todoRow : View Todo Msg :=
  li [onClick' (fun t => .toggle t.id)]
     [dyn (fun t => (if t.done then "✓ " else "") ++ t.text)]

def template : View Model Msg :=
  div [cls "demo"] [
    h1 [] "View template",
    -- a counter: the count is a single bound text node
    div [cls "counter"] [
      button [onClick .dec] "−",
      span [cls "count"] [dyn (fun m => toString m.count)],
      button [onClick .inc] "+"
    ],
    -- a controlled input bound to `name`, echoed live, greeting shown only when non-empty
    input [dynAttr "value" (·.name), onInput (Msg.setName ·)],
    showIf (fun m => m.name != "") (p [] [dyn (fun m => s!"Hello, {m.name}!")]),
    -- a keyed list; the container is a <ul>, each row keyed by its id
    button [onClick .add] "add todo",
    forEach "ul" (·.todos) (fun t => toString t.id) todoRow
  ]

def app : App Model Msg := templated init update template

end TemplateDemo
