/-
  A thin shim exposing the counter's verified pieces for the JS driver:
  the initial model, the (transpiled) view producing an `Html`, and the
  (transpiled, total, invariant-checked) `update`. The driver in JS calls these.
-/
import Examples.Counter
open Qed

namespace CounterJs

/-- The verified view: `App.view` runs the fine-grained template's `View.render`. -/
def view (m : Model) : Html Msg := App.view app m

/-- The verified, total transition (the same one `counterSafe` is proven about). -/
def step (m : Model) (msg : Msg) : Model := update m msg

/-- The initial model. -/
def initModel : Model := init

/-- Monomorphic wrappers (so JS calls them with the value args directly, no erased
    type parameter): the verified `diff` and patch application. -/
def diff (a b : Html Msg) : Patch Msg := Qed.diff a b
def patch (p : Patch Msg) (h : Html Msg) : Html Msg := Qed.applyPatch p h

end CounterJs
