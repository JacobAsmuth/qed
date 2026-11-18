import Qed
open Qed

namespace Todo

def doneStyle : Style := css [ textDecoration "line-through", color (hex "888") ]
def openStyle : Style := css [ color (hex "111") ]

component Row where
  state id      : Nat
  state text    : String
  state done    : Bool
  state toggles : Nat
  key id
  action toggle => done := !done, toggles += 1
  invariant rowSafe   : done → 1 ≤ toggles
  invariant rowStyled : roleHasOneOf "item" [doneStyle, openStyle]
  view =>
    <span role="item" {if done then doneStyle else openStyle}
          class={if done then "item done" else "item"} onClick={.toggle}>{text}</span>

end Todo

component Todo where
  collection rows : Row
  state draft := ""
  state nextId := 0
  action add =>
    rows := rows.push { id := nextId, text := draft.trimmed, done := false, toggles := 0 }
    draft := ""
    nextId += 1
  action remove (id : Nat) => rows := rows.filter (·.id != id)
  action sort => rows := rows.sortBy (fun a b => compare a.text b.text == .lt)
  invariant rowsSafe   : Row.rowSafe   for_each rows
  invariant rowsStyled : Row.rowStyled for_each rows
  view =>
    <div class="todo">
      <div class="add">
        <input class="new" bind={draft} placeholder="What needs doing?"/>
        <button class="addbtn" disabled={draft.trimmed.isEmpty} onClick={.add}>Add</button>
        <button class="sortbtn" onClick={.sort}>Sort</button>
      </div>
      <ul class="items">{for r in rows =>
        <li class="row">
          <Row state={r}/>
          <button class="rm" onClick={.remove r.id}>✕</button>
        </li>}</ul>
    </div>
