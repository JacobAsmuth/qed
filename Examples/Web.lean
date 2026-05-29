/-
  WASM entry point for the counter demo.

  This reuses the *exact same* `app` from `Examples.Counter` — the model,
  transition, view, and the machine-checked `counterSafe` invariant — and simply
  registers it with the runtime. `main` runs once when the WASM module is
  instantiated (performing Lean runtime init); the browser driver then calls
  `qed_init` to mount and `qed_dispatch` on each click.

  This module is only ever compiled to WASM (it uses the DOM externs), never
  linked as a native executable.
-/
import Examples.Counter
import Qed.Driver

def main : IO Unit :=
  Qed.run app
