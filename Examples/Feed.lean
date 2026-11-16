import Qed
open Qed

namespace Feed

def likeOn  : Style := css [ color (hex "ff2d55"), fontWeight 700 ]
def likeOff : Style := css [ color (hex "8a8a8a") ]

component Card where
  state id       : Nat
  state author   : String
  state likes    : Int
  state liked    : Bool
  state progress : Nat
  state duration : Nat
  key id
  invariant cardSafe   : 0 ≤ likes, progress ≤ duration, liked → 1 ≤ likes
  invariant cardStyled : roleHasOneOf "like" [likeOn, likeOff]
  view =>
    <article role="card" class="feed-card">
      <progress max={duration} value={progress}/>
      <strong>{s!"@{author}"}</strong>
      <button role="like"
        onClick={liked := !liked, likes := if liked then likes - 1 else likes + 1}
        {if liked then likeOn else likeOff}>{s!"♥ {likes}"}</button>
    </article>

app FeedApp where
  collection cards : Card
  state nextId := 0
  action rank => cards := cards.sortBy (fun a b => a.likes ≥ b.likes)
  action tick => cards := cards.map fun c => { c with progress := min (c.progress + 1) c.duration }
  action dismiss (id : Nat) => cards := cards.filter (·.id != id)
  action append =>
    cards := cards.push { id := nextId, author := "new", likes := 0,
                          liked := false, progress := 0, duration := 30 }
    nextId += 1
  view =>
    <section class="feed">
      <button class="rank" onClick={.rank}>Most liked</button>
      <button class="more" onClick={.append}>Load more</button>
      <div class="cards">{cards.map fun c =>
        <article key={c.id} class="slot">
          <Card state={c}/>
          <button class="dismiss" onClick={.dismiss c.id}>✕</button>
        </article>}</div>
    </section>

def app := FeedApp.app

invariant feedSafe   : Card.cardSafe   for_each cards preserved_by FeedApp.update
invariant feedStyled : Card.cardStyled for_each cards holds_in FeedApp.view

end Feed
