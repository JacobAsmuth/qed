/-
  A form with a rule relative to the current time.

  `form Appt (today : Date)` threads "today" into the validated type and the gate, so
  the `when` field's refinement — `fun d => today < d` ("must be in the future") —
  depends on the clock. The app reads the clock once at startup with `Cmd.now`,
  stores `today` in the model, and only then renders the form. The submit button
  `formView` produces is disabled unless the date is genuinely after today.
-/
import Qed
open Qed

namespace Booking

form Appt (today : Date) where
  who  : Input.text.refine (fun s => s.length ≥ 1)   -- a non-empty name
  when : Input.date.refine (fun d => today < d)        -- strictly after today

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

-- `Cmd.now` reads the clock once at startup (the `start` effect) and delivers `.gotToday`.
def app : App Model Msg :=
  ui { today := none, draft := Appt.Draft.empty, booked := none } update
    (start := Cmd.now .gotToday) fun m =>
    match m.today with
    | none       => p [cls "loading"] ["Loading today's date…"]
    | some today =>
        div [cls "app"] [
          h1 [] ["Book an appointment"],
          Appt.formView today m.draft .edit .submit,    -- gate uses `today`
          match m.booked with
          | some who => p [cls "ok"] ["Booked for ", who]
          | none     => .text ""
        ]

end Booking
