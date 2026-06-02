/-
  Browser entry point for the signals demo. Transpiled to JavaScript by `qed build`.
-/
import Examples.Signals
import Qed.Driver

def main : IO Unit := Qed.run Signals.app
