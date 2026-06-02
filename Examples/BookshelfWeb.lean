/-
  Browser entry point for the Bookshelf demo. Registers `Bookshelf.app`; the driver
  mounts it (adopting any server-rendered markup), routes the initial URL, fetches
  and decodes the catalog/detail data, and POSTs the add-book form. Transpiled to JavaScript by `qed build`.
-/
import Examples.Bookshelf
import Qed.Driver

def main : IO Unit := Qed.run Bookshelf.app
