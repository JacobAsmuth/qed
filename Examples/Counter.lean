import Qed
open Qed

component Counter:
  state count : Int = 0
  action increment: count += 1
  action decrement:
    if count > 0:
      count -= 1
  action reset: count = 0
  invariant counterSafe: count >= 0
  view:
    <div class="counter">
      <button onClick={.decrement}>−</button>
      <span class="count">{count}</span>
      <button onClick={.increment}>+</button>
      <button onClick={.reset}>reset</button>
      <input placeholder="type here, focus survives every click"/>
    </div>
