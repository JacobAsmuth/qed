/-
  WASM entry point for the local-state demo. Registers `Local.app` (and its one local
  component) with the runtime; the driver mounts each row's widget into its host and
  routes the widget's events to a per-instance keyed store. Compiled to WASM only.
-/
import Examples.Local
import Qed.Driver

def main : IO Unit := Qed.run Local.app
