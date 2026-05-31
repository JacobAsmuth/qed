/-
  WASM entry point for the native-effects tour. Registers `Effects.app`; the driver
  interprets each `Cmd` (localStorage, title, timer, random, focus, file pick, batch)
  and routes inbound ports to `onPort`. Compiled to WASM only.
-/
import Examples.Effects
import Qed.Driver

def main : IO Unit := Qed.run Effects.app
