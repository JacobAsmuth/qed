/-
  WASM entry point for the signup-form demo. Registers the pure `Signup.app` with
  the runtime; the JS driver mounts it and dispatches click/input/checkbox events.
  Compiled to WASM only (it pulls in the DOM externs), never linked natively.
-/
import Examples.Signup
import Qed.Driver

def main : IO Unit := Qed.run Signup.app
