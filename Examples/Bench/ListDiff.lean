import Examples.Bench.List
open Qed

namespace BenchListDiff

def viewDiff (m : BenchList.State) : Html BenchList.Msg :=
  <div>
    <button onClick={.bump}>bump</button>
    <ul>{for r in m.rows => <li key={toString r.id}>{r.label}</li>}</ul>
  </div>

def diffApp : App BenchList.State BenchList.Msg :=
  Qed.Internal.mkApp BenchList.init (fun m msg => (BenchList.update m msg, .none)) (View.ofHtml viewDiff)

end BenchListDiff
