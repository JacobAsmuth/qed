import Qed
open Qed

namespace BenchApp

structure Row where
  id       : Nat
  label    : String
  selected : Bool
deriving Inhabited

def adjectives : Array String := #[
  "pretty", "large", "big", "small", "tall", "short", "long", "handsome",
  "plain", "quaint", "clean", "elegant", "easy", "angry", "crazy", "helpful",
  "mushy", "odd", "unsightly", "adorable", "important", "inexpensive", "cheap",
  "expensive", "fancy"
]

def colours : Array String := #[
  "red", "yellow", "blue", "green", "pink", "brown", "purple", "brown",
  "white", "black", "orange"
]

def nouns : Array String := #[
  "table", "chair", "house", "bbq", "desk", "car", "pony", "cookie",
  "sandwich", "burger", "pizza", "mouse", "keyboard"
]

/-- Deterministic MINSTD LCG (`48271 * 2147483647 < 2^53`, stays in JS fast integer range). -/
def nextSeed (s : Nat) : Nat := (s * 48271) % 2147483647

structure BuildResult where
  rows   : Array Row
  nextId : Nat
  seed   : Nat
deriving Inhabited

def buildRows (count nextId seed : Nat) (acc : Array Row := #[]) : BuildResult :=
  let rec go (rem id s : Nat) (out : Array Row) : BuildResult :=
    match rem with
    | 0 => { rows := out, nextId := id, seed := s }
    | n + 1 =>
        let s1 := nextSeed s
        let s2 := nextSeed s1
        let s3 := nextSeed s2
        let adj := adjectives[s1 % adjectives.size]!
        let col := colours[s2 % colours.size]!
        let noun := nouns[s3 % nouns.size]!
        go n (id + 1) s3 (out.push { id, label := s!"{adj} {col} {noun}", selected := false })
  go count nextId seed acc

def selectRow (rows : Array Row) (prevId targetId : Nat) : Array Row :=
  let rows :=
    if prevId != 0 && prevId != targetId then
      match rows.findIdx? (fun r => r.id == prevId) with
      | some i => rows.set! i { rows[i]! with selected := false }
      | none   => rows
    else rows
  match rows.findIdx? (fun r => r.id == targetId) with
  | some i => rows.set! i { rows[i]! with selected := true }
  | none   => rows

def removeRow (rows : Array Row) (targetId : Nat) : Array Row :=
  match rows.findIdx? (fun r => r.id == targetId) with
  | some i => rows.eraseIdx! i
  | none   => rows

end BenchApp

component BenchApp:
  state rows       : BenchApp.Row[]
  state nextId     : Nat = 1
  state seed       : Nat = 1
  state selectedId : Nat = 0
  action run:
    let built = BenchApp.buildRows(1000, nextId, seed)
    rows = built.rows
    nextId = built.nextId
    seed = built.seed
    selectedId = 0
  action runLots:
    let built = BenchApp.buildRows(10000, nextId, seed)
    rows = built.rows
    nextId = built.nextId
    seed = built.seed
    selectedId = 0
  action add:
    let built = BenchApp.buildRows(1000, nextId, seed, rows)
    rows = built.rows
    nextId = built.nextId
    seed = built.seed
  action update:
    rows = rows.mapIdx((i, r) => { r with label = r.label ++ " !!!" } if i % 10 == 0 else r)
  action clear:
    rows = []
    selectedId = 0
  action swapRows:
    if rows.size > 998:
      let tmp = rows[1]
      rows[1] = rows[998]
      rows[998] = tmp
  action select(id: Nat):
    rows = BenchApp.selectRow(rows, selectedId, id)
    selectedId = id
  action remove(id: Nat):
    rows = BenchApp.removeRow(rows, id)
    if selectedId == id:
      selectedId = 0
  view:
    <div id="main">
      <div class="container">
        <div class="jumbotron">
          <div class="row">
            <div class="col-md-6"><h1>Qed (keyed)</h1></div>
            <div class="col-md-6">
              <div class="row">
                <div class="col-sm-6 smallpad"><button type="button" class="btn btn-primary btn-block" id="run" onClick={.run}>Create 1,000 rows</button></div>
                <div class="col-sm-6 smallpad"><button type="button" class="btn btn-primary btn-block" id="runlots" onClick={.runLots}>Create 10,000 rows</button></div>
                <div class="col-sm-6 smallpad"><button type="button" class="btn btn-primary btn-block" id="add" onClick={.add}>Append 1,000 rows</button></div>
                <div class="col-sm-6 smallpad"><button type="button" class="btn btn-primary btn-block" id="update" onClick={.update}>Update every 10th row</button></div>
                <div class="col-sm-6 smallpad"><button type="button" class="btn btn-primary btn-block" id="clear" onClick={.clear}>Clear</button></div>
                <div class="col-sm-6 smallpad"><button type="button" class="btn btn-primary btn-block" id="swaprows" onClick={.swapRows}>Swap Rows</button></div>
              </div>
            </div>
          </div>
        </div>
        <table class="table table-hover table-striped test-data">
          <tbody id="tbody">{for r in rows:
            <tr key={toString(r.id)} class={"danger" if r.selected else ""}>
              <td class="col-md-1">{toString(r.id)}</td>
              <td class="col-md-4"><a onClick={.select(r.id)}>{r.label}</a></td>
              <td class="col-md-1"><a onClick={.remove(r.id)}><span class="glyphicon glyphicon-remove" aria-hidden="true"></span></a></td>
              <td class="col-md-6"></td>
            </tr>}</tbody>
        </table>
        <span class="preloadicon glyphicon glyphicon-remove" aria-hidden="true"></span>
      </div>
    </div>
