import Qed
open Qed

namespace Todo

def doneStyle : Style := css [ textDecoration "line-through", color (hex "888") ]
def openStyle : Style := css [ color (hex "111") ]

component Row:
  state id      : Nat
  state text    : String
  state done    : Bool
  state toggles : Nat
  key id
  action toggle:
    done = not done
    toggles += 1
  invariant rowSafe: done -> toggles >= 1
  invariant rowStyled: roleHasOneOf("item", [doneStyle, openStyle])
  view:
    <span role="item" {doneStyle if done else openStyle}
          class={"item done" if done else "item"} onClick={.toggle}>{text}</span>

end Todo

component Todo:
  collection rows : Row
  state draft = ""
  state nextId = 0
  action add:
    rows.push(Row.State(id=nextId, text=draft.trimmed, done=false, toggles=0))
    draft = ""
    nextId += 1
  action remove(id: Nat):
    rows = rows.filter(r => r.id != id)
  action sort:
    rows = rows.sortBy((a, b) => compare(a.text, b.text) == .lt)
  invariant rowsSafe: Row.rowSafe for_each rows
  invariant rowsStyled: Row.rowStyled for_each rows
  view:
    <div class="todo">
      <div class="add">
        <input class="new" bind={draft} placeholder="What needs doing?"/>
        <button class="addbtn" disabled={draft.trimmed.isEmpty} onClick={.add}>Add</button>
        <button class="sortbtn" onClick={.sort}>Sort</button>
      </div>
      <ul class="items">{for r in rows:
        <li class="row">
          <Row state={r}/>
          <button class="rm" onClick={.remove(r.id)}>✕</button>
        </li>}</ul>
    </div>
