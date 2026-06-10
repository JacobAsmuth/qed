/-
  Tour 10 · Schemas with context

  A form with a rule relative to the current time.

  `schema Appt (today : Date)` threads "today" into the validated type and the gate, so
  the `when` field's refinement, `fun d => today < d` ("must be in the future"),
  depends on the clock. The app reads the clock once at startup with `Cmd.now`,
  stores `today` in the model, and only then renders the form. The submit button
  `formView` produces is disabled unless the date is genuinely after today.
-/
import Qed
open Qed

namespace Booking

schema Appt (today : Date) where
  who  : Codec.text.refine (fun s => s.length ≥ 1)   -- a non-empty name
  when : Codec.date.refine (fun d => today < d)        -- strictly after today

structure Model where
  today  : Option Date     -- none until `Cmd.now` reports it
  draft  : Appt.Draft
  booked : Option String   -- the booked appointment's name, once submitted

inductive Msg
  | gotToday (d : Date)    -- delivered by Cmd.now at startup
  | edit (d : Appt.Draft)
  | submit

def update (m : Model) : Msg → Model
  | .gotToday d => { m with today := some d }
  | .edit d     => { m with draft := d }
  | .submit     =>
      match m.today with
      | none       => m
      | some today => match Appt.parse today m.draft with
                      | some appt => { m with booked := some appt.who.val }
                      | none      => m

-- A booking can only be recorded after the clock has reported, since `.submit` does
-- nothing while `today` is `none`. Stated once, machine-checked for every message:
-- the discharger splits the nested `match`es in `.submit` on its own.
invariant bookedNeedsToday : (fun m => m.booked.isSome → m.today.isSome) preserved_by update

-- `Cmd.now` reads the clock once at startup (the `start` effect) and delivers `.gotToday`.
def app : App Model Msg :=
  ui { today := none, draft := Appt.Draft.empty, booked := none } update
    (start := Cmd.now .gotToday) fun m =>
    match m.today with
    | none       => <p class="loading">Loading today's date…</p>
    | some today =>
        -- the form's submit gate uses `today`
        <div class="app">
          <h1>Book an appointment</h1>
          {Appt.formView today m.draft .edit .submit}
          {match m.booked with
           | some who => <p class="ok">Booked for {who}</p>
           | none     => .text ""}
        </div>

end Booking
