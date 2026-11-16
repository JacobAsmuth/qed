import Qed
open Qed

namespace Local

component Stepper where
  state count : Int := 0
  state saved : Int := 0
  action decrement => count := if count ≤ 0 then 0 else count - 1
  action increment => count += 1
  action save => saved := count
  invariant stepperSafe : 0 ≤ count
  view =>
    <div class="stepper">
      <button class="dec" onClick={.decrement}>−</button>
      <span class="count">{count}</span>
      <button class="inc" onClick={.increment}>+</button>
      <button class="save" onClick={.save}>save</button>
      <span class="savedv">{saved}</span>
    </div>

component Tag where
  prop label := "Pin"
  state on := false
  event onToggle (pinned : Bool)
  action toggle => on := !on, send (onToggle (!on))
  view =>
    <button title={label} class={if on then "pin on" else "pin"} onClick={.toggle}>
      {if on then "★ pinned" else "☆ pin"}</button>

component Widget where
  prop id : Nat
  prop label : String
  state count  : Int := 0
  state note   := ""
  state pinned := false
  event onReport (count : Int)
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
      <button class="report" onClick={send (onReport count)}>Report ↑</button>
      <span class="pinned">{if pinned then "pinned" else ""}</span>
      <Tag key={s!"t{id}"} label={s!"{label}: {note}"} onToggle={pinned := ·}/>
    </div>

structure Row where
  id    : Nat
  label : String

end Local

component Local where
  state rows : Array Row := #[{ id := 0, label := "Alpha" }, { id := 1, label := "Beta" }]
  state draft := ""
  state nextId := 2
  state lastReport : Option (Nat × Int) := none

  action remove (id : Nat) => rows := rows.filter (·.id != id)
  action rename (id : Nat) =>
    rows := rows.map fun r => if r.id == id then { r with label := r.label ++ "!" } else r
  action reported (id : Nat) (count : Int) => lastReport := some (id, count)
  action add =>
    let t := draft.trimmed
    if !t.isEmpty then
      rows := rows.push { id := nextId, label := t }
      draft := ""
      nextId += 1

  view =>
    <div class="app">
      <h1>Local-state rows</h1>
      <div class="add">
        <input class="new" bind={draft} placeholder="New row label"/>
        <button class="addbtn" onClick={.add}>Add row</button>
      </div>
      <div class="report">{match lastReport with
        | some (id, c) => s!"last report: row {id} = {c}"
        | none         => "no reports yet"}</div>
      <div class="solo"><Stepper key="s"/></div>
      <ul class="rows">{for r in rows =>
        <li key={r.id} class="row">
          <span class="label">{r.label}</span>
          <Widget key={r.id} id={r.id} label={r.label}
            initial={{ note := r.label }} onReport={.reported r.id}/>
          <button class="rename" onClick={.rename r.id}>Rename</button>
          <button class="rm" onClick={.remove r.id}>✕</button>
        </li>}</ul>
    </div>
