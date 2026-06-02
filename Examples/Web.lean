/-
  Browser entry point for the counter demo.

  This reuses the *exact same* `app` from `Examples.Counter` — the model,
  transition, view, and the machine-checked `counterSafe` invariant — and simply
  registers it with the runtime. `qed build` transpiles this module (and the whole
  framework) to JavaScript; `main` runs once at boot, then the host calls `qed_init`
  to mount and `qed_dispatch` on each click.
-/
import Examples.Counter
import Qed.Driver

def main : IO Unit :=
  Qed.run app
