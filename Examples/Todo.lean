import Qed
open Qed

namespace Todo

component Row where
  state id : Nat
  state text : String
  state done : Bool
  key id
  action toggle => done := !done
  view =>
    <span class={if done then "item done" else "item"} onClick={.toggle}>{text}</span>

end Todo

component Todo where
  collection rows : Row
  state draft := ""
  state nextId := 0
  action add when !draft.trimmed.isEmpty =>
    let text := draft.trimmed
    rows := rows.push { id := nextId, text, done := false }
    draft := ""
    nextId += 1
  action remove (id : Nat) => rows := rows.filter (·.id != id)
  action sort => rows := rows.sortBy (fun a b => compare a.text b.text == .lt)
  view =>
    <div class="todo">
      <div class="add">
        <input class="new" bind={draft} placeholder="What needs doing?"/>
        <button class="addbtn" onClick={.add}>Add</button>
        <button class="sortbtn" onClick={.sort}>Sort</button>
      </div>
      <ul class="items">{for r in rows =>
        <li class="row">
          <Row state={r}/>
          <button class="rm" onClick={.remove r.id}>✕</button>
        </li>}</ul>
    </div>
