import Qed
open Qed

namespace Live

structure Model where
  n : Int

inductive Msg
  | inc
  | setTo (v : Int)

def update (m : Model) : Msg → Model
  | .inc     => { m with n := m.n + 1 }
  | .setTo v => { n := max 0 v }

invariant nonNegative : (fun m => 0 ≤ m.n) preserved_by update

def app : App Model Msg :=
  ui { n := 0 } update fun m =>
    <div class="live">
      <p class="n">{m.n}</p>
      <button class="inc" onClick={.inc}>+1</button>
      <button class="double" onClick={.setTo (m.n * 2)}>double</button>
      <button class="plus10" onClick={.setTo (m.n + 10)}>+10</button>
      <button class="reset" onDoubleClick={.setTo 0}>reset (dbl-click)</button>
    </div>

end Live
