/-
  WASM entry point for the React head-to-head benchmark app (`test/bench_react.mjs`).
  Compiled to WASM only.
-/
import Examples.BenchApp
import Qed.Driver

def main : IO Unit := Qed.run BenchApp.app
