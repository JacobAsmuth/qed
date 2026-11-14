import Qed
open Qed

namespace Booking

schema Appt (today : Date) where
  who  : Codec.text.refine (fun s => s.length ≥ 1)
  when : Codec.date.refine (fun d => today < d)

structure Model where
  today  : Option Date
  draft  : Appt.Draft
  booked : Option String

inductive Msg
  | gotToday (d : Date)
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

invariant bookedNeedsToday : (fun m => m.booked.isSome → m.today.isSome) preserved_by update

def app : App Model Msg :=
  ui { today := none, draft := Appt.Draft.empty, booked := none } update
    (start := Cmd.now .gotToday) fun m =>
    match m.today with
    | none       => <p class="loading">Loading today's date…</p>
    | some today =>
        <div class="app">
          <h1>Book an appointment</h1>
          {Appt.formView today m.draft .edit .submit}
          {match m.booked with
           | some who => <p class="ok">Booked for {who}</p>
           | none     => .text ""}
        </div>

end Booking
