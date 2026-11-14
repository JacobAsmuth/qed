import Qed

open Qed

structure Model where
  count : Int
deriving Repr, Inhabited

inductive Msg where
  | increment
  | decrement
  | reset
deriving Repr

def init : Model := { count := 0 }

def update (m : Model) : Msg → Model
  | .increment => { m with count := m.count + 1 }
  | .decrement => { m with count := if 0 < m.count then m.count - 1 else m.count }
  | .reset     => { m with count := 0 }

def app : App Model Msg := ui init update fun m =>
  <div class="counter">
    <button onClick={.decrement}>−</button>
    <span class="count">{m.count}</span>
    <button onClick={.increment}>+</button>
    <button onClick={.reset}>reset</button>
    <input placeholder="type here, focus survives every click"/>
  </div>

invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update
