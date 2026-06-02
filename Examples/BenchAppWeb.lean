/-
  Browser entry point for the React head-to-head benchmark app (`test/bench_react.mjs`).
  Transpiled to JavaScript by `qed build`.
-/
import Examples.BenchApp
import Qed.Driver

def main : IO Unit := Qed.run BenchApp.app
