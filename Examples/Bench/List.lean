import Qed
open Qed (View App mkApp cls onClick)
open Qed.V

namespace BenchList

def n : Nat := 10000

structure Row where
  id    : Nat
  label : String
deriving Inhabited

structure Model where
  rows : Array Row
  tick : Nat
deriving Inhabited

def init : Model :=
  { rows := (Array.range n).map fun i => { id := i, label := s!"row {i}" }, tick := 0 }

inductive Msg | bump

def update (m : Model) : Msg → Model
  | .bump =>
      { rows := m.rows.mapIdx fun i r => if i % 10 == 0 then { r with label := s!"row {r.id} #{m.tick}" } else r
        tick := m.tick + 1 }

def rowT : View Row Msg := el "li" [.stat (cls "row")] [dyn (·.label)]

def template : View Model Msg :=
  el "div" [] [
    el "button" [.stat (onClick .bump)] "bump",
    forEach "ul" (·.rows) (fun r => toString r.id) rowT
  ]

def app : App Model Msg := mkApp init update template

end BenchList
