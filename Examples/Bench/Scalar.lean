import Qed
open Qed (View App mkApp cls onClick)
open Qed.V

namespace BenchScalar

def n : Nat := 2000

structure Model where
  vals : Array Nat
  tick : Nat
deriving Inhabited

def init : Model := { vals := Array.replicate n 0, tick := 0 }

inductive Msg | bump

def update (m : Model) : Msg → Model
  | .bump =>
      let i := (m.tick % (n / 20)) * 20
      { vals := m.vals.set! i (m.vals.getD i 0 + 1), tick := m.tick + 1 }

def template : View Model Msg :=
  el "div" [] [
    el "button" [.stat (onClick .bump)] "bump",
    el "div" [.stat (cls "grid")]
      ((List.range n).map fun i =>
        if i % 20 == 0 then
          el "div" [.stat (cls "cell")] [dyn (fun m => toString (m.vals.getD i 0))]
        else
          el "div" [.stat (cls "cell")] [text s!"static cell {i}"])
  ]

def app : App Model Msg := mkApp init update template

end BenchScalar
