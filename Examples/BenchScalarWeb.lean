/-
  WASM entry: the scalar benchmark run as a fine-grained `View` template.
-/
import Examples.BenchScalar
import Qed.Driver

def main : IO Unit := Qed.run BenchScalar.app (template := some BenchScalar.template)
