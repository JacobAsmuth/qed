/-
  Tour 06 · Reusable components in a keyed list

  The TODO demo: a keyed list of reusable row components.

  Each row is an ordinary `component` declaration (a label you can mark done) whose
  state the parent owns: the list holds `Array Row.State` and renders each row with
  `<Row state={r} onMsg={.row}/>`, which tags the row's messages with its key (the
  declared `key id`), so a click routes to that row alone. Every row carries a `key`
  (its item id), so the verified `diff` (`Qed.Diff`) reconciles the list *by key*:
  add appends, remove drops one node, sort reorders, and a row that moves keeps the
  same DOM node, its local state, and any focus inside it.

  Pure Lean, total by construction; the browser entry is `Examples/TodoWeb.lean`.
-/
import Qed
open Qed

namespace Todo

-- A reusable row: a label plus its "done" state. No field defaults, so the parent
-- owns and seeds every row; `key id` declares which field identifies a row.
component Row where
  state id   : Nat
  state text : String
  state done : Bool
  key id
  view =>
    <span class={if done then "item done" else "item"} onClick={set done (!done)}>{text}</span>

/-- The whole app state: the rows, the text being typed, and the next id to hand
    out (so every row's key is unique and stable across edits). -/
structure Model where
  rows   : Array Row.State
  draft  : String
  nextId : Nat

inductive Msg where
  | edit (s : String)            -- the text field changed
  | add                          -- append the (trimmed) draft as a new row
  | row (k : String) (msg : Row.Msg) -- a message from the row with key k, carrying its own Msg
  | remove (id : Nat)            -- delete the row with this id
  | sort                         -- reorder the rows alphabetically

def init : Model := { rows := #[], draft := "", nextId := 0 }

def update (m : Model) : Msg → Model
  | .edit s    => { m with draft := s }
  | .add       =>
      let t := m.draft.trimmed
      if t.isEmpty then m
      else { m with rows   := m.rows.push { id := m.nextId, text := t, done := false }
                    draft  := ""
                    nextId := m.nextId + 1 }
  -- a row's message, delivered back to the row whose key matches (`Row.updateKeyed`
  -- routes by the declared `key id`, so a sort/filter in flight can't misroute it)
  | .row k msg => { m with rows := Row.updateKeyed m.rows k msg }
  | .remove id => { m with rows := m.rows.filter (·.id != id) }
  | .sort      => { m with rows := m.rows.qsort (fun a b => compare a.text b.text == .lt) }

def app : App Model Msg := ui init update fun m =>
  <div class="todo">
    <div class="add">
      <input class="new" value={m.draft} onInput={.edit} placeholder="What needs doing?"/>
      <button class="addbtn" onClick={.add}>Add</button>
      <button class="sortbtn" onClick={.sort}>Sort</button>
    </div>
    <ul class="items">{m.rows.map fun r =>
      <li key={toString r.id} class="row">
        <Row state={r} onMsg={.row}/> -- the parent-owned row, messages tagged by its key
        <button class="rm" onClick={.remove r.id}>✕</button>
      </li>}</ul>
  </div>

end Todo
