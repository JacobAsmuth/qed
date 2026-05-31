/-
  WASM entry point for the `View` template demo. Compiled to WASM only.
-/
import Examples.Template
import Qed.Driver

def main : IO Unit := Qed.run TemplateDemo.app (template := some TemplateDemo.template)
