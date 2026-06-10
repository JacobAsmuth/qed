/-
  Browser entry: the scalar benchmark run as a fine-grained `View` template.
-/
import Examples.Bench.Scalar
import Qed.Driver

def main : IO Unit := Qed.run BenchScalar.app
