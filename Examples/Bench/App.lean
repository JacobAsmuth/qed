import Qed
open Qed

namespace BenchApp

def rowCount : Nat := 10000

structure Row where
  id    : Nat
  label : String
deriving Inhabited

def labelFor (i : Nat) : String := s!"item {i} · the quick brown fox"

end BenchApp

component BenchApp where
  state rows : Array BenchApp.Row := #[]
  action create =>
    rows := (Array.range rowCount).map fun i => { id := i + 1, label := labelFor (i + 1) }
  action update =>
    rows := rows.mapIdx fun i r => if i % 10 == 0 then { r with label := r.label ++ " !" } else r
  action swap =>
    if rows.size > 4 then
      let i := 1
      let j := rows.size - 2
      rows := (rows.set! i rows[j]!).set! j rows[i]!
  action reverse => rows := rows.reverse
  action clear => rows := #[]
  view =>
    <div>
      <div class="ops">
        <button onClick={.create}>create</button>
        <button onClick={.update}>update</button>
        <button onClick={.swap}>swap</button>
        <button onClick={.reverse}>reverse</button>
        <button onClick={.clear}>clear</button>
      </div>
      <ul id="list">{for r in rows =>
        <li key={toString r.id} class="row"><span class="lbl">{r.label}</span><span class="id">{toString r.id}</span></li>}</ul>
    </div>
