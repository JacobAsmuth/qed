/-
  A keyed-list benchmark: 10,000 rows, every 10th row's text changes per update (the keys
  never change). Through the diff path this rebuilds and diffs the 10k-row tree and walks
  the DOM with a `childAt` per row; as a `View` template, `forEach` makes each row's text a
  signal, so a value-only update (keys unchanged) pushes just the changed rows with a direct
  `setSignal` — no diff, no `childAt`.

  The same `app` runs both ways: `Examples/Bench/ListWeb` (template) and
  `Examples/Bench/ListDiffWeb` (diff). Benched by `test/bench_template.mjs`.

  Pure Lean.
-/
import Qed
open Qed (View App mkApp)
open Qed.V

namespace BenchList

def n : Nat := 10000

structure Row where
  id    : Nat
  label : String
deriving Inhabited

structure Model where
  rows : Array Row
  tick : Nat
deriving Inhabited

def init : Model :=
  { rows := (Array.range n).map fun i => { id := i, label := s!"row {i}" }, tick := 0 }

inductive Msg | bump

-- change every 10th row's text; ids (keys) never change
def update (m : Model) : Msg → Model
  | .bump =>
      { rows := m.rows.mapIdx fun i r => if i % 10 == 0 then { r with label := s!"row {r.id} #{m.tick}" } else r
        tick := m.tick + 1 }

def rowT : View Row Msg := li [cls "row"] [dyn (·.label)]

def template : View Model Msg :=
  div [] [
    button [onClick .bump] "bump",          -- click id 0: the benchmark dispatches this
    forEach "ul" (·.rows) (fun r => toString r.id) rowT
  ]

def app : App Model Msg := mkApp init update template

end BenchList
