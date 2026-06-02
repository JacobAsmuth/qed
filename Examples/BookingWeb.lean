/-
  Browser entry point for the appointment-booking demo. Registers `Booking.app`; the
  driver mounts it, runs the `Cmd.now` startup effect to read the clock, and
  dispatches input/change events. Transpiled to JavaScript by `qed build`.
-/
import Examples.Booking
import Qed.Driver

def main : IO Unit := Qed.run Booking.app
