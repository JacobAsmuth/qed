/-
  WASM entry point for the signals demo. Compiled to WASM only.
-/
import Examples.Signals
import Qed.Driver

def main : IO Unit := Qed.run Signals.app
