/-
  Native entry point for the counter demo. Two jobs, both browser-free:

  * server-side render — emit a complete static HTML document for the app's initial state
    (`App.renderInitial` runs the *same* verified `view`/`render` the browser uses), so the
    page's first paint is the real UI and the client just mounts over it; and
  * a sanity check that a few reachable states produce the markup we expect.

  `lake exe counter` (or `./qed` native build). The static document goes to stdout.
-/
import Examples.Counter

open Qed

def main : IO Unit := do
  -- SSR: the app's initial `#app` content (stdout), from the same verified view/render the
  -- browser uses. `renderDocument "Counter" (App.renderInitial app)` wraps it in a full page.
  IO.println (App.renderInitial app)
  -- sanity (stderr): a few reachable states render as expected.
  let render (label : String) (m : Model) : IO Unit :=
    IO.eprintln s!"{label} (count={m.count}): {(view m).render}"
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
