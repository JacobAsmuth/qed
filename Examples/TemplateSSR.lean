import Examples.Template
open Qed

def main : IO Unit := IO.println (App.renderInitial TemplateDemo.app)
