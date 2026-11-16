import Qed
open Qed

namespace Booking

schema Appt (today : Date) where
  who  : String where who.length ≥ 1
  when : Date   where today < when

app BookingApp where
  state today  : Option Date := none
  state draft  := Appt.Draft.empty
  state booked : Option String := none
  start (Cmd.now .gotToday)

  action gotToday (d : Date) => today := some d
  action submit =>
    if let some t := today then
      if let some appt := Appt.parse t draft then
        booked := some appt.who

  invariant bookedNeedsToday : booked.isSome → today.isSome

  view =>
    match today with
    | none => <p class="loading">Loading today's date…</p>
    | some t =>
        <div class="app">
          <h1>Book an appointment</h1>
          {Appt.formView t draft (draft := ·) .submit}
          {if let some who := booked then <p class="ok">Booked for {who}</p>}
        </div>

def app : App BookingApp.State BookingApp.Msg := BookingApp.app

end Booking
