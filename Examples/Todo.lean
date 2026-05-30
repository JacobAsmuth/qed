/-
  The TODO demo — a keyed list that grows, shrinks, and reorders.

  A text field adds an item; a button on each row removes it; a Sort button
  reorders. Each row carries a stable `key` (its item id, like React/Vue), so the
  verified `diff` (`Qed.Diff`) reconciles the list *by key*: a removed row drops
  exactly its own node, and a row that moves (because another was removed, or the
  list was sorted) keeps the *same* DOM node — its focus, scroll, and selection
  ride along — instead of the rows below being rewritten in place. `diff_apply`
  proves the patched list equals the new `view` exactly, whichever node each key
  matched.

  Pure Lean, total by construction; the browser entry is `Examples/TodoWeb.lean`.
-/
import Qed
open Qed

namespace Todo

/-- One item, with a stable id used as its reconciliation key. -/
structure Item where
  id   : Nat
  text : String

/-- The whole app state: the text being typed, the items, and the next id to hand
    out (so every item's key is unique and stable across edits). -/
structure Model where
  draft  : String
  items  : Array Item
  nextId : Nat

inductive Msg where
  | edit (s : String)    -- the text field changed
  | add                  -- append the (trimmed) draft as a new item
  | remove (id : Nat)    -- delete the item with this id
  | sort                 -- reorder the items alphabetically

def init : Model := { draft := "", items := #[], nextId := 0 }

/-- Adding ignores blank input, clears the field, and assigns a fresh id; removing
    and sorting are total array operations that leave keys with their items. -/
def update (m : Model) : Msg → Model
  | .edit s    => { m with draft := s }
  | .add       =>
      let t := m.draft.trim
      if t.isEmpty then m
      else { m with items  := m.items.push { id := m.nextId, text := t }
                    draft  := ""
                    nextId := m.nextId + 1 }
  | .remove id => { m with items := m.items.filter (·.id != id) }
  | .sort      => { m with items := m.items.qsort (fun a b => compare a.text b.text == .lt) }

/-- One row, tagged with `key it.id` — the diff uses it to follow this item across
    removals and reorders. `remove it.id` deletes exactly this item. -/
def row (it : Item) : Html Msg :=
  li [key (toString it.id), cls "item"] [
    span   [cls "text"]                        [it.text],
    button [cls "rm", onClick (.remove it.id)] "✕"
  ]

def view (m : Model) : Html Msg :=
  div [cls "todo"] [
    div [cls "add"] [
      input  [cls "new", placeholder "What needs doing?", value m.draft, onInput .edit],
      button [cls "addbtn",  onClick .add]  "Add",
      button [cls "sortbtn", onClick .sort] "Sort"
    ],
    ul [cls "items"] (m.items.map row).toList
  ]

def app : App Model Msg := sandbox init update view

end Todo
