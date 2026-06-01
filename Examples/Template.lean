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
open Qed (View App templated Style css styleSheet)
open Qed.V

namespace TemplateDemo

structure Todo where
  id   : Nat
  text : String
  done : Bool
  editing : Bool := false
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
  | startEdit (id : Nat)            -- enter inline-edit on a row
  | editText (id : Nat) (s : String) -- the row's controlled input fired

def update (m : Model) : Msg → Model
  | .inc        => { m with count := m.count + 1 }
  | .dec        => { m with count := m.count - 1 }
  | .setName s  => { m with name := s }
  | .toggle id  => { m with todos := m.todos.map fun t => if t.id == id then { t with done := !t.done } else t }
  | .add        => { m with todos := m.todos.push { id := m.nextId, text := s!"item {m.nextId}", done := false },
                            nextId := m.nextId + 1 }
  | .startEdit id => { m with todos := m.todos.map fun t => { t with editing := t.id == id } }
  | .editText id s => { m with todos := m.todos.map fun t => if t.id == id then { t with text := s } else t }

-- The `view%` macro lets this read like an ordinary `Model → Html` view: string
-- interpolation becomes `dyn`, a model-driven `if` becomes `ifElse`, a dynamic attribute
-- (`value m.name`, `cls (if …)`) becomes `dynAttr`, a scope-reading event (`onClick
-- (.toggle t.id)`) becomes `onClick'`, and `m.todos.map (… key …)` becomes a keyed
-- `forEach` — none of it written by hand. Each compiles to the same fine-grained core.
-- a scoped style, co-located with the view. Its class name is a hash (no global
-- collisions), and a typo'd reference (`bnner`) would be a compile error.
def banner : Style := css "padding: 7px; border-radius: 4px; &:hover { opacity: 0.9 }"

def template : View Model Msg :=
  view% fun m =>
    div [cls "demo"] [
      static (styleSheet [banner]),
      div [banner, attr "id" "styled-banner"] [text "scoped style"],
      h1 [] "View template",
      -- a counter: the count is a single bound text node
      div [cls "counter"] [
        button [onClick .dec] "−",
        span [cls "count"] [text s!"{m.count}"],
        button [onClick .inc] "+"
      ],
      -- a native `if/else` on the model → `ifElse` (fine-grained slot, reconciled on flip)
      if m.count == 0
        then p [cls "hint"] "click + to start"
        else p [cls "live"] [text s!"count is {m.count}"],
      -- a controlled input: `value m.name` → `dynAttr "value"`, echoed live; greeting on non-empty
      input [value m.name, onInput (Msg.setName ·)],
      showIf (fun m => m.name != "") (p [cls "greeting"] [text s!"Hello, {m.name}!"]),
      -- a keyed list written as a native `.map`: each row's `class` (`cls (if …)`) and text
      -- are fine-grained signals, its click reads the row id, and `key` drives reconciliation
      button [onClick .add] "add todo",
      ul [cls "todos"] (m.todos.map fun t =>
        li [key (toString t.id), cls (if t.done then "done" else ""), onClick (.toggle t.id)]
           [text t.text]),
      -- a STRUCTURAL conditional inside a row: the element itself differs by `done`
      -- (`<strong>` vs `<span>`). `view%` lifts it to `ifElse`; because the row bakes that
      -- statically, `forEach` folds a fingerprint into the row key so a toggle reconciles
      -- through the verified keyed `diff` instead of being missed by the signal path.
      ul [cls "structural"] (m.todos.map fun t =>
        li [key (toString t.id)] [
          if t.done then p [cls "is-done"] [text "done!"]
                    else span [cls "is-open"] [text t.text]
        ]),
      -- inline editing: a CONTROLLED input lives inside the row's `ifElse`. Because the
      -- branch's leaves are signals (not baked into the key), typing updates the value in
      -- place — the row is not rebuilt, so the input keeps focus and caret while you type.
      ul [cls "edit"] (m.todos.map fun t =>
        li [key (toString t.id)] [
          if t.editing
            then input [cls "editor", value t.text, onInput (Msg.editText t.id ·)]
            else span [cls "label", onClick (.startEdit t.id)] [text t.text]
        ])
    ]

def app : App Model Msg := templated init update template

end TemplateDemo
