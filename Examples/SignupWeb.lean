/-
  Browser entry point for the signup-form demo. Registers the pure `Signup.app` with
  the runtime; the JS driver mounts it and dispatches click/input/checkbox events.
  transpiled to JavaScript (it uses the DOM externs).
-/
import Examples.Signup
import Qed.Driver

def main : IO Unit := Qed.run Signup.app
