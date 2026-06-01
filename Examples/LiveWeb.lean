/-
  WASM entry for the live-handler regression demo. Registers `Live.app`. Compiled to WASM only.
-/
import Examples.Live
import Qed.Driver

def main : IO Unit := Qed.run Live.app
