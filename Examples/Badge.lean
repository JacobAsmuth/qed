/-
  Tour 04 · Styles, and proofs about styles

  Badge: a tiny app that demonstrates BOTH kinds of `invariant` under the one keyword:

    • a MODEL invariant, proven preserved by every `update`  (`preserved_by`), and
    • a STYLING invariant, proven of the rendered view for every model  (`holds_in`).

  The styling claim, "the status badge is always shown on- or off-styled", is checked for
  *every* reachable state, not the ones a test happened to render. Tag the element with `role`,
  and `roleHasOneOf … holds_in view` does the rest. Pure Lean; no proof written by hand.
-/
import Qed
open Qed

namespace Badge

-- The two mutually-exclusive visual states of the badge.
def onStyle  : Style := css [ backgroundColor (hex "0a0"), color (hex "fff"), padding (rem 1) ]
def offStyle : Style := css [ backgroundColor (hex "888"), color (hex "fff"), padding (rem 1) ]

structure Model where
  on    : Bool
  level : Int
deriving Inhabited

inductive Msg | toggle

def init : Model := { on := false, level := 0 }

def update (m : Model) : Msg → Model
  | .toggle => { on := !m.on, level := m.level + 1 }

-- A named view, so the styling invariant can refer to it (and auto-discharge). The status badge
-- is tagged `role "status"`, and its style is chosen from the two allowed ones by the model.
def view (m : Model) : Html Msg :=
  <div>
    {styleSheet [onStyle, offStyle]}
    <button role="status" onClick={.toggle} {if m.on then onStyle else offStyle}>
      {if m.on then "ON" else "OFF"}</button>
    -- a dot, deliberately styled the OPPOSITE of the status badge
    <span role="dot" {if m.on then offStyle else onStyle}>●</span>
    <span>{s!", flipped {m.level}×"}</span>
  </div>

def app : App Model Msg := ui init update fun m => view m

-- A MODEL invariant: the level never goes negative, across every transition. (`preserved_by`)
invariant levelSafe : (fun m => 0 ≤ m.level) preserved_by update

-- A STYLING invariant: the status badge always carries the on- or off-style, for every model,
-- not just the states a test rendered. Same `invariant` keyword, a different connective. (`holds_in`)
invariant statusStyled : roleHasOneOf "status" [onStyle, offStyle] holds_in view

-- A RELATIONAL styling invariant: the status badge and the dot are never on-styled at the same
-- time: exactly one of them is "on" in every state. Relates two different elements.
invariant statusAndDotOpposite : exactlyOne "status" "dot" onStyle offStyle holds_in view

end Badge
