/-
  The TODO demo — a keyed list of reusable row components.

  Each row is a self-contained `Component` (its own state, message, `update`, and
  `view`: a label you can mark done). The list embeds one per item and tags each
  row's messages with its index (`Msg.row i`), so a click routes to that row alone.
  Every row carries a `key` (its item id), so the verified `diff` (`Qed.Diff`)
  reconciles the list *by key*: add appends, remove drops one node, sort reorders —
  and a row that moves keeps the same DOM node, its local state, and any focus
  inside it.

  Pure Lean, total by construction; the browser entry is `Examples/TodoWeb.lean`.
-/
import Qed
open Qed

namespace Todo

-- A reusable row: a label plus its own local "done" state and message.
namespace Row

structure Model where
  id   : Nat            -- a stable identity, used as the reconciliation key
  text : String
  done : Bool

inductive Msg | toggle

def update (m : Model) : Msg → Model
  | .toggle => { m with done := !m.done }

def view (m : Model) : Html Msg :=
  span [cls (if m.done then "item done" else "item"), onClick .toggle] [m.text]

def component : Component Model Msg := { update, view }

end Row

/-- The whole app state: the rows, the text being typed, and the next id to hand
    out (so every row's key is unique and stable across edits). -/
structure Model where
  rows   : Array Row.Model
  draft  : String
  nextId : Nat

inductive Msg where
  | edit (s : String)            -- the text field changed
  | add                          -- append the (trimmed) draft as a new row
  | row (i : Nat) (msg : Row.Msg) -- a message from row i, carrying the row's own Msg
  | remove (id : Nat)            -- delete the row with this id
  | sort                         -- reorder the rows alphabetically

def init : Model := { rows := #[], draft := "", nextId := 0 }

def update (m : Model) : Msg → Model
  | .edit s    => { m with draft := s }
  | .add       =>
      let t := m.draft.trim
      if t.isEmpty then m
      else { m with rows   := m.rows.push { id := m.nextId, text := t, done := false }
                    draft  := ""
                    nextId := m.nextId + 1 }
  | .row i msg => { m with rows := Row.component.updateAt m.rows i msg }
  | .remove id => { m with rows := m.rows.filter (·.id != id) }
  | .sort      => { m with rows := m.rows.qsort (fun a b => compare a.text b.text == .lt) }

def view (m : Model) : Html Msg :=
  div [cls "todo"] [
    div [cls "add"] [
      input  [cls "new", value m.draft, onInput .edit, placeholder "What needs doing?"],
      button [cls "addbtn",  onClick .add]  "Add",
      button [cls "sortbtn", onClick .sort] "Sort"
    ],
    ul [cls "items"] (m.rows.mapIdx fun i r =>
      li [key (toString r.id), cls "row"] [
        (Row.component.view r).map (Msg.row i),     -- the row's own view, messages tagged row i
        button [cls "rm", onClick (.remove r.id)] "✕"
      ]).toList
  ]

def app : App Model Msg := sandbox init update view

end Todo
