import Qed
open Qed

def onStyle  : Style := css [ backgroundColor (hex "0a0"), color (hex "fff"), padding (rem 1) ]
def offStyle : Style := css [ backgroundColor (hex "888"), color (hex "fff"), padding (rem 1) ]

component Badge where
  state on          := false
  state level : Int := 0
  invariant levelSafe            : 0 ≤ level
  invariant statusStyled         : roleHasOneOf "status" [onStyle, offStyle]
  invariant statusAndDotOpposite : exactlyOne "status" "dot" onStyle offStyle
  view =>
    <div>
      <button role="status" onClick={on := !on, level += 1} {if on then onStyle else offStyle}>
        {if on then "ON" else "OFF"}</button>
      <span role="dot" {if on then offStyle else onStyle}>●</span>
      <span>, flipped {level}×</span>
    </div>
