import Examples.Counter

open Qed

def main : IO Unit := do
  IO.println (App.renderInitial app)
  let render (label : String) (m : Model) : IO Unit :=
    IO.eprintln s!"{label} (count={m.count}): {(app.view m).render}"
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
