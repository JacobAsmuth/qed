/-
  An Elm-Architecture app (pure `init`/`update`) whose view is written inline with `ui`:
  a counter, a conditional, a controlled input, keyed and keyless lists, inline editing,
  and a scoped style.

  Pure Lean; the browser entry is `Examples/TemplateWeb.lean`.
-/
import Qed
open Qed (App Style css styleSheet)
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

-- A scoped style, co-located with the view: its class name is a hash (no global collisions),
-- and a typo'd reference (`bnner`) is a compile error.
def banner : Style := css "padding: 7px; border-radius: 4px; &:hover { opacity: 0.9 }"

-- Write the view inline with ordinary control flow — `if`, `match`, `.map`, string
-- interpolation, dynamic attributes, scope-reading events. `ui` builds the app from it.
def app : App Model Msg := ui init update fun m =>
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
      -- a conditional that swaps content by the count
      if m.count == 0
        then p [cls "hint"] "click + to start"
        else p [cls "live"] [text s!"count is {m.count}"],
      -- a controlled input bound to `name`, with a greeting shown once it's non-empty
      input [value m.name, onInput (Msg.setName ·)],
      showIf (fun m => m.name != "") (p [cls "greeting"] [text s!"Hello, {m.name}!"]),
      -- a keyed list of todos: each row shows its text, toggles `done` on click
      button [onClick .add] "add todo",
      ul [cls "todos"] (m.todos.map fun t =>
        li [key (toString t.id), cls (if t.done then "done" else ""), onClick (.toggle t.id)]
           [text t.text]),
      -- a row whose element differs by state (`<p>` when done, `<span>` otherwise)
      ul [cls "structural"] (m.todos.map fun t =>
        li [key (toString t.id)] [
          if t.done then p [cls "is-done"] [text "done!"]
                    else span [cls "is-open"] [text t.text]
        ]),
      -- inline editing: an `<input>` while editing, a clickable label otherwise
      ul [cls "edit"] (m.todos.map fun t =>
        li [key (toString t.id)] [
          if t.editing
            then input [cls "editor", value t.text, onInput (Msg.editText t.id ·)]
            else span [cls "label", onClick (.startEdit t.id)] [text t.text]
        ]),
      -- a plain list (no `key`)
      ul [cls "keyless"] (m.todos.map fun t => li [] [text t.text])
    ]

end TemplateDemo
