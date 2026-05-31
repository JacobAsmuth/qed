/-
  WASM entry: the same scalar benchmark run through the verified diff path (no template),
  for a head-to-head against the fine-grained template in `test/bench_template.mjs`.
-/
import Examples.BenchScalar
import Qed.Driver

def main : IO Unit := Qed.run BenchScalar.app
