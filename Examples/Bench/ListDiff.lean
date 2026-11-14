import Examples.Bench.List
open Qed

namespace BenchListDiff

def viewDiff (m : BenchList.Model) : Html BenchList.Msg :=
  <div>
    <button onClick={.bump}>bump</button>
    <ul>{m.rows.map fun r => <li key={toString r.id}>{r.label}</li>}</ul>
  </div>

def diffApp : App BenchList.Model BenchList.Msg :=
  mkApp BenchList.init BenchList.update (View.ofHtml viewDiff)

end BenchListDiff
