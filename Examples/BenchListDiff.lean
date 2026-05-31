/-
  The diff-path baseline for the keyed-list benchmark: an ordinary `Model → Html Msg`
  keyed list (real text rows, no signals), sharing `BenchList`'s model and update. Run
  through `run` with no template, this is "what Qed did before templates" — the head it
  is measured against in `test/bench_template.mjs`.
-/
import Examples.BenchList
open Qed

namespace BenchListDiff

def viewDiff (m : BenchList.Model) : Html BenchList.Msg :=
  div [] [
    button [onClick .bump] "bump",
    ul [] (m.rows.toList.map fun r => li [key (toString r.id)] [text r.label])
  ]

def diffApp : App BenchList.Model BenchList.Msg :=
  sandbox BenchList.init BenchList.update viewDiff

end BenchListDiff
