/-
  Server-side render of the `view%` template demo's initial #app — used by the
  template-hydration test. Same verified `render template` the browser runs.
-/
import Examples.Template
open Qed

def main : IO Unit := IO.println (App.renderInitial TemplateDemo.app)
