/-
  Browser entry point for the routed users demo. Registers `Users.app`; the driver
  mounts it, routes the initial URL, fetches/decodes profiles, and wires the
  form/keyboard/focus events. Transpiled to JavaScript by `qed build`.
-/
import Examples.Users
import Qed.Driver

def main : IO Unit := Qed.run Users.app
