/-
  Tour 07 · Lifting a contract over a list

  Feed: a TikTok-style scrollable feed of card components, each with its own contract,
  the parent holding them as a *sorted* keyed list. Demonstrates `for_each`: a child
  component's invariant lifted to "every card in the feed stays valid", across the
  feed's own transition (re-rank / dismiss / load), in one line and with no proof.

  Pure Lean; the invariants are erased at runtime, so there is no browser entry; the
  guarantee is that this file *builds* (the kernel checked every lift).
-/
import Qed
open Qed

namespace Feed

/-! ## The child: one feed card -/
namespace Card

structure Model where
  id       : Nat
  author   : String
  likes    : Int
  liked    : Bool
  progress : Nat        -- playback position …
  duration : Nat        -- … never past the end

inductive Msg | toggleLike | tick

def update (c : Model) : Msg → Model
  | .toggleLike =>
      if c.liked then { c with liked := false, likes := c.likes - 1 }
                 else { c with liked := true,  likes := c.likes + 1 }
  | .tick       => { c with progress := min (c.progress + 1) c.duration }

def likeOn  : Style := css [ color "#ff2d55", fontWeight "700" ]
def likeOff : Style := css [ color "#8a8a8a" ]

def view (c : Model) : Html Msg :=
  <article role="card" class="feed-card">
    <progress max={toString c.duration} value={toString c.progress}/>
    <strong>{s!"@{c.author}"}</strong>
    <button role="like" onClick={.toggleLike} {if c.liked then likeOn else likeOff}>{s!"♥ {c.likes}"}</button>
  </article>

def component : Component Model Msg := { update, view }

/-- The card's contract, written once. `abbrev` so it's reusable and decidable. -/
abbrev Safe (c : Model) : Prop :=
  0 ≤ c.likes  ∧  c.progress ≤ c.duration  ∧  (c.liked → 1 ≤ c.likes)

end Card

-- ① a card is always Safe (likes ≥ 0, never past its end, "liked ⇒ counted").   auto
invariant cardSafe   : Card.Safe preserved_by Card.update
-- ② the like button always carries one of its two styles.                        auto
invariant cardStyled : roleHasOneOf "like" [Card.likeOn, Card.likeOff] holds_in Card.view

/-! ## The parent: a sorted feed -/

structure Model where
  cards  : Array Card.Model
  nextId : Nat

inductive Msg
  | card (k : String) (msg : Card.Msg)    -- a tap inside a card, routed by key
  | rank                                   -- re-sort: most-liked first
  | dismiss (id : Nat)                     -- swipe a card away
  | append                                 -- a fresh (valid-by-construction) card arrives

embed Card as card keyedBy (toString ·.id) into cards

def update (m : Model) : Msg → Model
  | .card k msg => cardUpdate m k msg
  | .rank       => { m with cards := m.cards.sortBy (fun a b => a.likes ≥ b.likes) }
  | .dismiss id => { m with cards := m.cards.filter (·.id != id) }
  | .append     => { m with cards  := m.cards.push
                              { id := m.nextId, author := "new", likes := 0,
                                liked := false, progress := 0, duration := 30 }
                            nextId := m.nextId + 1 }

def view (m : Model) : Html Msg :=
  <section class="feed">{m.cards.map fun c => cardView c}</section>

def init : Model := { cards := #[], nextId := 0 }
def app : App Model Msg := mkApp init update (View.ofHtml view)

-- ③ EVERY card in the feed stays Safe, across taps, re-rank, dismiss, append.   one line, auto
--    keyed tap → the child contract carries it; `rank` sorts (verified `sortBy`);
--    `dismiss` only filters; `append`'s new card is Safe by construction.
invariant feedSafe : cardSafe for_each cards preserved_by update

-- ④ EVERY rendered card in the feed is correctly styled: the whole `view`, chrome and cards.
--    Same `for_each`, over the view instead of the transition; `cardStyled` closes each card.
invariant feedStyled : cardStyled for_each cards holds_in view

end Feed
