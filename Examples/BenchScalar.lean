/-
  A scalar-heavy benchmark: a page of `n` bound values where a single one changes per
  update. This is where a `View` template beats the diff path — the diff rebuilds and
  compares the whole `n`-node tree every update; the template walks its (static) bindings
  and patches the one DOM node whose projection changed, building and diffing nothing.

  The *same* `app` runs both ways: `Examples/BenchScalarWeb` runs it as a template
  (fine-grained), `Examples/BenchScalarDiffWeb` runs it through the verified diff. The
  benchmark (`test/bench_template.mjs`) times `update` for each.

  Pure Lean.
-/
import Qed
open Qed (View App mkApp)
open Qed.V

namespace BenchScalar

def n : Nat := 2000

structure Model where
  vals : Array Nat
  tick : Nat
deriving Inhabited

def init : Model := { vals := Array.replicate n 0, tick := 0 }

inductive Msg | bump

-- one in 20 cells is dynamic (a realistic mostly-static page); bump one dynamic cell
def update (m : Model) : Msg → Model
  | .bump =>
      let i := (m.tick % (n / 20)) * 20
      { vals := m.vals.set! i (m.vals.getD i 0 + 1), tick := m.tick + 1 }

def template : View Model Msg :=
  div [] [
    button [onClick .bump] "bump",          -- click id 0: the benchmark dispatches this
    div [cls "grid"]
      ((List.range n).map fun i =>
        if i % 20 == 0 then
          div [cls "cell"] [dyn (fun m => toString (m.vals.getD i 0))]
        else
          div [cls "cell"] [text s!"static cell {i}"])
  ]

def app : App Model Msg := mkApp init update template

end BenchScalar
