/-
  Browser entry for the live-handler regression demo. Registers `Live.app`. Transpiled to JavaScript by `qed build`.
-/
import Examples.Live
import Qed.Driver

def main : IO Unit := Qed.run Live.app
