/-
  A Qed app for the head-to-head benchmark against React (`test/bench_react.mjs`). It is
  a keyed list with the standard operations — create 10k, update every 10th row, swap
  two, reorder all (reverse), clear — exposed as the first five dispatch ids (the op
  buttons render first, so they are ids 0–4). The React app in `test/react_bench.html`
  renders an identical DOM and runs the identical operations.

  Pure Lean; the browser entry is `Examples/BenchAppWeb.lean`.
-/
import Qed
open Qed

namespace BenchApp

def rowCount : Nat := 10000

structure Row where
  id    : Nat
  label : String
deriving Inhabited

structure Model where
  rows      : Array Row
  useLazy   : Bool        -- toggle: wrap each row in `lazy` (memoize on its content)
  useSignal : Bool        -- toggle: render each row's value with a `signalText`

def init : Model := { rows := #[], useLazy := false, useSignal := false }

inductive Msg | create | update | swap | reverse | clear | toggle | toggleSignal

def labelFor (i : Nat) : String := s!"item {i} · the quick brown fox"

def update (m : Model) : Msg → Model
  | .create  => { m with rows := (Array.range rowCount).map fun i => { id := i + 1, label := labelFor (i + 1) } }
  | .update  => { m with rows := m.rows.mapIdx fun i r => if i % 10 == 0 then { r with label := r.label ++ " !" } else r }
  | .swap    =>
      if m.rows.size > 4 then
        let i := 1; let j := m.rows.size - 2
        { m with rows := (m.rows.set! i m.rows[j]!).set! j m.rows[i]! }
      else m
  | .reverse => { m with rows := m.rows.reverse }
  | .clear   => { m with rows := #[] }
  | .toggle       => { m with useLazy := !m.useLazy }
  | .toggleSignal => { m with useSignal := !m.useSignal }

def rowView (r : Row) : Html Msg :=
  li [key (toString r.id), cls "row"] [span [cls "lbl"] [r.label], span [cls "id"] [toString r.id]]

-- the same row, memoized: `lazy`'s key tracks the content, while the inner `li` keeps the
-- stable reconcile key. An update skips every unchanged row's subtree entirely.
def rowViewLazy (r : Row) : Html Msg := lazy s!"{r.id}:{r.label}" (rowView r)

-- the row's value as a signal: structure renders once; `setSignal "r<id>" v` updates the
-- one bound node directly, no diff at all.
def rowViewSignal (r : Row) : Html Msg :=
  li [key (toString r.id), cls "row"] [signalText s!"r{r.id}"]

def view (m : Model) : Html Msg :=
  div [] [
    div [cls "ops"] [
      button [onClick .create]  "create",
      button [onClick .update]  "update",
      button [onClick .swap]    "swap",
      button [onClick .reverse] "reverse",
      button [onClick .clear]   "clear",
      button [onClick .toggle]       "lazy",
      button [onClick .toggleSignal] "signal"
    ],
    ul [attr "id" "list"] (m.rows.map
      (fun r => if m.useSignal then rowViewSignal r else if m.useLazy then rowViewLazy r else rowView r)).toList
  ]

def app : App Model Msg := sandbox init update view

end BenchApp
