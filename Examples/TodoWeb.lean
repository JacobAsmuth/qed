/-
  WASM entry point for the TODO demo. Registers the pure `Todo.app` with the
  runtime; the JS driver mounts it and dispatches click/input events, and the
  verified diff adds/removes only the rows that changed. Compiled to WASM only.
-/
import Examples.Todo
import Qed.Driver

def main : IO Unit := Qed.run Todo.app
