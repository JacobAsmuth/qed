/- Browser entry: the keyed-list benchmark as a fine-grained `View` template. -/
import Examples.Bench.List
import Qed.Driver

def main : IO Unit := Qed.run BenchList.app
