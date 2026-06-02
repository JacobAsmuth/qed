/-
  Browser entry point for the `View` template demo. Transpiled to JavaScript by `qed build`.
-/
import Examples.Template
import Qed.Driver

def main : IO Unit := Qed.run TemplateDemo.app
