import Qed
open Qed

namespace BenchList

def n : Nat := 10000

structure Row where
  id    : Nat
  label : String
deriving Inhabited

def initRows : Array Row :=
  (Array.range n).map fun i => { id := i, label := s!"row {i}" }

end BenchList

component BenchList where
  state rows : Array BenchList.Row := BenchList.initRows
  state tick : Nat := 0
  action bump =>
    rows := rows.mapIdx fun i r => if i % 10 == 0 then { r with label := s!"row {r.id} #{tick}" } else r
    tick += 1
  view =>
    <div>
      <button onClick={.bump}>bump</button>
      <ul>{for r in rows => <li key={r.id} class="row">{r.label}</li>}</ul>
    </div>
