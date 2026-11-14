import Qed
open Qed

namespace Badge

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

def view (m : Model) : Html Msg :=
  <div>
    {styleSheet [onStyle, offStyle]}
    <button role="status" onClick={.toggle} {if m.on then onStyle else offStyle}>
      {if m.on then "ON" else "OFF"}</button>
    <span role="dot" {if m.on then offStyle else onStyle}>●</span>
    <span>{s!", flipped {m.level}×"}</span>
  </div>

def app : App Model Msg := ui init update fun m => view m

invariant levelSafe (m) : 0 ≤ m.level preserved_by update
invariant statusStyled : roleHasOneOf "status" [onStyle, offStyle] holds_in view
invariant statusAndDotOpposite : exactlyOne "status" "dot" onStyle offStyle holds_in view

end Badge
