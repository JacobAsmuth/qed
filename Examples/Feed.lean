/-
  Tour 07 · Lifting a contract over a list

  Feed: a TikTok-style scrollable feed of cards, the parent holding them as a *sorted*
  keyed list it owns. The card is an ordinary `component` declaration, rendered with
  `<Card state={c} onMsg={.card}/>`, so who owns the state is a use-site choice, not a
  different way of writing the child. Demonstrates `for_each`: the card's invariant
  lifted to "every card in the feed stays valid", across the feed's own transition
  (re-rank / tick / dismiss / load), in one line and with no proof.

  Pure Lean; the invariants are erased at runtime, so there is no browser entry; the
  guarantee is that this file *builds* (the kernel checked every lift).
-/
import Qed
open Qed

namespace Feed

/-! ## The child: one feed card -/

def likeOn  : Style := css [ color "#ff2d55", fontWeight "700" ]
def likeOff : Style := css [ color "#8a8a8a" ]

/-- One feed card. No field defaults: the parent owns and seeds every card. The like
    handler sets two fields in one message; both expressions read the same pre-update
    state. -/
component Card where
  state id       : Nat
  state author   : String
  state likes    : Int
  state liked    : Bool
  state progress : Nat        -- playback position …
  state duration : Nat        -- … never past the end
  key id
  view =>
    <article role="card" class="feed-card">
      <progress max={toString duration} value={toString progress}/>
      <strong>{s!"@{author}"}</strong>
      <button role="like"
        onClick={set liked (!liked), set likes (if liked then likes - 1 else likes + 1)}
        {if liked then likeOn else likeOff}>{s!"♥ {likes}"}</button>
    </article>

/-- The card's contract, written once. `abbrev` so it's reusable and decidable. -/
abbrev Card.Safe (c : Card.State) : Prop :=
  0 ≤ c.likes  ∧  c.progress ≤ c.duration  ∧  (c.liked → 1 ≤ c.likes)

-- ① a card is always Safe (likes ≥ 0, never past its end, "liked ⇒ counted").   auto
invariant cardSafe   : Card.Safe preserved_by Card.update
-- ② the like button always carries one of its two styles.                        auto
invariant cardStyled : roleHasOneOf "like" [likeOn, likeOff] holds_in Card.view

/-! ## The parent: a sorted feed -/

structure Model where
  cards  : Array Card.State
  nextId : Nat

inductive Msg
  | card (k : String) (msg : Card.Msg)    -- a tap inside a card, routed by key
  | rank                                   -- re-sort: most-liked first
  | tick                                   -- advance every card's playback (props flow;
                                           --   a `Cmd.every` timer would drive it live)
  | dismiss (id : Nat)                     -- swipe a card away
  | append                                 -- a fresh (valid-by-construction) card arrives

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

-- ③ EVERY card in the feed stays Safe, across taps, re-rank, tick, dismiss, append.   one line, auto
--    keyed tap → the child contract carries it; `rank` sorts (verified `sortBy`);
--    `tick` maps over the rows (the parent owns them, so it updates them directly);
--    `dismiss` only filters; `append`'s new card is Safe by construction.
invariant feedSafe : cardSafe for_each cards preserved_by update

-- ④ EVERY rendered card in the feed is correctly styled: the whole `view`, chrome and cards.
--    Same `for_each`, over the view instead of the transition; `cardStyled` closes each card.
invariant feedStyled : cardStyled for_each cards holds_in view

end Feed
