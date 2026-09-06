/- Tour 06 · Parent-owned child collections. Identity is declared on Row;
   collection generates the message and update arm, and Row.each keys the wrappers. -/
import Qed
open Qed

namespace Todo

component Row where
  state id : Nat
  state text : String
  state done : Bool
  key id
  action toggle => set done (!done)
  view =>
    <span class={if done then "item done" else "item"} onClick={.toggle}>{text}</span>

component Board where
  collection rows : Row
  state draft : String := ""
  state nextId : Nat := 0
  action edit => set draft
  action add when (!draft.trimmed.isEmpty) =>
    set rows (rows.push { id := nextId, text := draft.trimmed, done := false }),
    set draft "", set nextId (nextId + 1)
  action remove (id : Nat) => set rows (rows.filter (·.id != id))
  action sort => set rows (rows.qsort (fun a b => compare a.text b.text == .lt))
  view =>
    <div class="todo">
      <div class="add">
        <input class="new" value={draft} onInput={.edit} placeholder="What needs doing?"/>
        <button class="addbtn" onClick={.add}>Add</button>
        <button class="sortbtn" onClick={.sort}>Sort</button>
      </div>
      <ul class="items">{Row.each rows .rows fun r child =>
        <li class="row">
          {child}
          <button class="rm" onClick={.remove r.id}>✕</button>
        </li>}</ul>
    </div>

def app := Board.app

end Todo
