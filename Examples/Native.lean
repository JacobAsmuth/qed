/-
  Native entry point for the counter demo: renders a few reachable states to
  static HTML on stdout. A fast, browser-free sanity check that the verified
  `app` produces the markup we expect. (`lake exe counter`.)
-/
import Examples.Counter

open Qed

def main : IO Unit := do
  let render (label : String) (m : Model) : IO Unit :=
    IO.println s!"{label} (count={m.count}): {Html.renderToString (view m)}"
  let s0 := init
  let s1 := update s0 .increment
  let s2 := update s1 .increment
  let s3 := update s2 .decrement
  let s4 := update s3 .reset
  render "init " s0
  render "+1   " s1
  render "+1   " s2
  render "-1   " s3
  render "reset" s4
