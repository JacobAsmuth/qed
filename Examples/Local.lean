import Qed
open Qed

namespace Local

component Stepper where
  state count : Int := 0
  state saved : Int := 0
  action decrement => count := if count ≤ 0 then 0 else count - 1
  action increment => count += 1
  action save => saved := count
  view =>
    <div class="stepper">
      <button class="dec" onClick={.decrement}>−</button>
      <span class="count">{count}</span>
      <button class="inc" onClick={.increment}>+</button>
      <button class="save" onClick={.save}>save</button>
      <span class="savedv">{saved}</span>
    </div>

invariant stepperSafe (s) : 0 ≤ s.count preserved_by Stepper.update

component Tag where
  prop label := "Pin"
  state on := false
  emits Bool
  action toggle => on := !on, send (!on)
  view =>
    <button title={label} class={if on then "pin on" else "pin"} onClick={.toggle}>
      {if on then "★ pinned" else "☆ pin"}</button>

component Widget where
  prop id : Nat
  prop label : String
  state count  : Int := 0
  state note   := ""
  state pinned := false
  emits Int
  action resetNote => note := label
  view =>
    <div class="widget">
      <span class="live-label">{label}</span>
      <div class="counter">
        <button class="dec" onClick={count -= 1}>−</button>
        <span class="count">{count}</span>
        <button class="inc" onClick={count += 1}>+</button>
      </div>
      <input class="note" bind={note} placeholder="a local note…"/>
      <button class="reset-note" onClick={.resetNote}>Reset note</button>
      <button class="report" onClick={send count}>Report ↑</button>
      <span class="pinned">{if pinned then "pinned" else ""}</span>
      <Tag key={s!"t{id}"} label={s!"{label}: {note}"} onEmit={pinned := ·}/>
    </div>

structure Row where
  id    : Nat
  label : String

structure Model where
  rows       : Array Row
  draft      : String
  nextId     : Nat
  lastReport : Option (Nat × Int)

def init : Model :=
  { rows := #[{ id := 0, label := "Alpha" }, { id := 1, label := "Beta" }]
    draft := "", nextId := 2, lastReport := none }

inductive Msg
  | edit (s : String)
  | add
  | remove (id : Nat)
  | reported (id : Nat) (count : Int)
  | rename (id : Nat)

def update (m : Model) : Msg → Model
  | .edit s        => { m with draft := s }
  | .add           =>
      let t := m.draft.trimmed
      if t.isEmpty then m
      else { m with rows   := m.rows.push { id := m.nextId, label := t }
                    draft  := ""
                    nextId := m.nextId + 1 }
  | .remove id     => { m with rows := m.rows.filter (·.id != id) }
  | .rename id     => { m with rows := m.rows.map fun r =>
      if r.id == id then { r with label := r.label ++ "!" } else r }
  | .reported id c => { m with lastReport := some (id, c) }

def widgetView (r : Row) : Html Msg :=
  <Widget key={r.id} id={r.id} label={r.label}
    initial={{ note := r.label }} onEmit={Msg.reported r.id}/>

def app : App Model Msg := ui init update fun m =>
  <div class="app">
    <h1>Local-state rows</h1>
    <div class="add">
      <input class="new" value={m.draft} onInput={.edit} placeholder="New row label"/>
      <button class="addbtn" onClick={.add}>Add row</button>
    </div>
    <div class="report">{match m.lastReport with
      | some (id, c) => s!"last report: row {id} = {c}"
      | none         => "no reports yet"}</div>
    <div class="solo"><Stepper key="s"/></div>
    <ul class="rows">{m.rows.map fun r =>
      <li key={r.id} class="row">
        <span class="label">{r.label}</span>
        {widgetView r}
        <button class="rename" onClick={.rename r.id}>Rename</button>
        <button class="rm" onClick={.remove r.id}>✕</button>
      </li>}</ul>
  </div>

end Local
