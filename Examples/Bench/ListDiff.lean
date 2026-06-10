/-
  The diff-path baseline for the keyed-list benchmark: an ordinary `Model → Html Msg`
  keyed list (real text rows, no signals), sharing `BenchList`'s model and update. Run
  through `run` with no template, this is "what Qed did before templates", the head it
  is measured against in `test/bench_template.mjs`.
-/
import Examples.Bench.List
open Qed

namespace BenchListDiff

def viewDiff (m : BenchList.Model) : Html BenchList.Msg :=
  <div>
    <button onClick={.bump}>bump</button>
    <ul>{m.rows.map fun r => <li key={toString r.id}>{r.label}</li>}</ul>
  </div>

-- The whole `Html` view as one `View.ofHtml` node: every update rebuilds it and reconciles
-- through the verified `diff`, the "before templates" baseline, now inside the one engine.
def diffApp : App BenchList.Model BenchList.Msg :=
  mkApp BenchList.init BenchList.update (View.ofHtml viewDiff)

end BenchListDiff
