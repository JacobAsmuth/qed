import Qed
open Qed

namespace Feed

def likeOn  : Style := css [ color "#ff2d55", fontWeight "700" ]
def likeOff : Style := css [ color "#8a8a8a" ]

/-- Feed card (doc comment ends the preceding open-ended `def` before non-reserved `component`). -/
component Card where
  state id       : Nat
  state author   : String
  state likes    : Int
  state liked    : Bool
  state progress : Nat
  state duration : Nat
  key id
  view =>
    <article role="card" class="feed-card">
      <progress max={toString duration} value={toString progress}/>
      <strong>{s!"@{author}"}</strong>
      <button role="like"
        onClick={set liked (!liked), set likes (if liked then likes - 1 else likes + 1)}
        {if liked then likeOn else likeOff}>{s!"♥ {likes}"}</button>
    </article>

abbrev Card.Safe (c : Card.State) : Prop :=
  0 ≤ c.likes ∧ c.progress ≤ c.duration ∧ (c.liked → 1 ≤ c.likes)

invariant cardSafe   : Card.Safe preserved_by Card.update
invariant cardStyled : roleHasOneOf "like" [likeOn, likeOff] holds_in Card.view

structure Model where
  cards  : Array Card.State
  nextId : Nat

inductive Msg
  | card (k : String) (msg : Card.Msg)
  | rank
  | tick
  | dismiss (id : Nat)
  | append

def update (m : Model) : Msg → Model
  | .card k msg => { m with cards := Card.updateKeyed m.cards k msg }
  | .rank       => { m with cards := m.cards.sortBy (fun a b => a.likes ≥ b.likes) }
  | .tick       => { m with cards := m.cards.map fun c =>
                              { c with progress := min (c.progress + 1) c.duration } }
  | .dismiss id => { m with cards := m.cards.filter (·.id != id) }
  | .append     => { m with cards  := m.cards.push
                              { id := m.nextId, author := "new", likes := 0,
                                liked := false, progress := 0, duration := 30 }
                            nextId := m.nextId + 1 }

def view (m : Model) : Html Msg :=
  <section class="feed">
    <button class="rank" onClick={.rank}>Most liked</button>
    <button class="more" onClick={.append}>Load more</button>
    <div class="cards">{m.cards.map fun c =>
      <article key={toString c.id} class="slot">
        <Card state={c} onMsg={.card}/>
        <button class="dismiss" onClick={.dismiss c.id}>✕</button>
      </article>}</div>
  </section>

def init : Model := { cards := #[], nextId := 0 }
def app : App Model Msg := mkApp init update (View.ofHtml view)

invariant feedSafe : cardSafe for_each cards preserved_by update
invariant feedStyled : cardStyled for_each cards holds_in view

end Feed
