/-
  Axiom manifest for `qed check` / `qed build`.

  The CLI runs this file with `lake env lean` and fails the build if the output
  mentions `sorryAx` (a hole) or an error. Each listed theorem must depend
  only on sound Lean axioms. Add a `#print axioms` line for each guarantee you
  want gated; apps can ship their own manifest at this path.
-/
import Qed
import Examples.Counter
import Examples.Booking
import Examples.Chat
import Examples.Template
import Examples.Live
import Examples.Socket

#print axioms counterSafe            -- state-machine invariant (numeric bound, pure)
#print axioms Booking.bookedNeedsToday -- invariant: a precondition for a state (pure, auto)
#print axioms TemplateDemo.idsBelowNext -- invariant: unique keys over .map/.push (`:=` proof)
#print axioms Live.nonNegative       -- invariant: a bound preserved by live handlers (pure, auto)
#print axioms Socket.composerOnlyWhenOnline -- invariant: precondition on an effectful state machine (auto)
#print axioms Chat.streamSafe        -- invariant: effect safety on an effectful transition (`:=` proof)
#print axioms Qed.diff_apply         -- VDOM diff/patch correctness
#print axioms Qed.diffChildren_apply -- child reconcile, any matcher (positional + keyed), any lengths
#print axioms Qed.applyValues_render -- View template value-patch = full re-render (stable structure)
#print axioms Qed.patch_render       -- View template update step = full re-render (any structure)
#print axioms Qed.parse_depth_le     -- JSON depth bound
#print axioms Qed.Route.round_trip   -- routing round-trip
#print axioms Qed.TypedRoute.round_trip  -- routing round-trip with typed Nat/Int params
#print axioms Qed.Demo.Signup.canSubmit_iff  -- form submit ⇔ valid
#print axioms Qed.parse_render     -- JSON codec round-trip (whole grammar)
