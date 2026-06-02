/- Browser entry: the keyed-list benchmark as a fine-grained `View` template. -/
import Examples.BenchList
import Qed.Driver

def main : IO Unit := Qed.run BenchList.app
