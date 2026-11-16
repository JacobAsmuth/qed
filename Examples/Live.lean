import Qed
open Qed

namespace Live

app LiveApp where
  state n : Int := 0
  action setTo (v : Int) => n := max 0 v
  invariant nonNegative : 0 ≤ n
  view =>
    <div class="live">
      <p class="n">{n}</p>
      <button class="inc" onClick={n += 1}>+1</button>
      <button class="double" onClick={.setTo (n * 2)}>double</button>
      <button class="plus10" onClick={.setTo (n + 10)}>+10</button>
      <button class="reset" onDoubleClick={.setTo 0}>reset (dbl-click)</button>
    </div>

def app := LiveApp.app

end Live
