import Qed
open Qed

component Counter where
  state count : Int := 0
  action increment => count += 1
  action decrement => count := if 0 < count then count - 1 else count
  action reset     => count := 0
  invariant counterSafe : 0 ≤ count
  view =>
    <div class="counter">
      <button onClick={.decrement}>−</button>
      <span class="count">{count}</span>
      <button onClick={.increment}>+</button>
      <button onClick={.reset}>reset</button>
      <input placeholder="type here, focus survives every click"/>
    </div>
