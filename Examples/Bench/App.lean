/-
  A Qed app for the head-to-head benchmark against React (`test/bench_react.mjs`). It is
  a keyed list with the standard operations: create 10k, update every 10th row, swap two,
  reorder all (reverse), clear, exposed as dispatch ids 0..4 (the op buttons render first).

  This is written the only way there is to write it: an ordinary `view`. The framework
  decides per operation how to render and update: a value-only change patches just the
  changed bindings, a shape change reconciles through the verified diff, with nothing for
  the developer to opt into. The React app in `test/react_bench.html` renders an identical
  DOM and runs the identical operations.

  Pure Lean; the browser entry is `Examples/Bench/AppWeb.lean`.
-/
import Qed
open Qed

namespace BenchApp

def rowCount : Nat := 10000

structure Row where
  id    : Nat
  label : String
deriving Inhabited

structure Model where
  rows : Array Row
deriving Inhabited

def init : Model := { rows := #[] }

inductive Msg | create | update | swap | reverse | clear

def labelFor (i : Nat) : String := s!"item {i} · the quick brown fox"

def update (m : Model) : Msg → Model
  | .create  => { rows := (Array.range rowCount).map fun i => { id := i + 1, label := labelFor (i + 1) } }
  | .update  => { m with rows := m.rows.mapIdx fun i r => if i % 10 == 0 then { r with label := r.label ++ " !" } else r }
  | .swap    =>
      if m.rows.size > 4 then
        let i := 1; let j := m.rows.size - 2
        { m with rows := (m.rows.set! i m.rows[j]!).set! j m.rows[i]! }
      else m
  | .reverse => { m with rows := m.rows.reverse }
  | .clear   => { rows := #[] }

def app : App Model Msg := ui init update fun _m =>
  <div>
    <div class="ops">
      <button onClick={.create}>create</button>
      <button onClick={.update}>update</button>
      <button onClick={.swap}>swap</button>
      <button onClick={.reverse}>reverse</button>
      <button onClick={.clear}>clear</button>
    </div>
    <ul id="list">{_m.rows.map fun r =>
      <li key={toString r.id} class="row"><span class="lbl">{r.label}</span><span class="id">{toString r.id}</span></li>}</ul>
  </div>

end BenchApp
