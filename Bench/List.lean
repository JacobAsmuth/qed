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

component BenchList:
  state rows : BenchList.Row[] = BenchList.initRows
  state tick : Nat = 0
  action bump:
    rows = rows.mapIdx((i, r) => { r with label = f"row {r.id} #{tick}" } if i % 10 == 0 else r)
    tick += 1
  view:
    <div>
      <button onClick={.bump}>bump</button>
      <ul>{for r in rows: <li key={r.id} class="row">{r.label}</li>}</ul>
    </div>
