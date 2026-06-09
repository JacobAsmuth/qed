/-
  A WebSocket echo client: open a connection, send a line, watch it bounce back.

  The socket lives behind the same pure `update` as everything else. `Cmd.wsOpen`
  carries the lifecycle messages (open / message / close / error), `Cmd.wsSend` and
  `Cmd.wsClose` address it by the key it was opened under, and every inbound frame
  arrives as an ordinary `Msg`. The view is plain `Html`; nothing here touches JS.

  The demo connects to `/echo` on the page's own origin, so it expects an echo
  endpoint there (the `socket_test.mjs` harness serves one).
-/
import Qed
open Qed

namespace Socket

/-- The connection's state, reflected in the status line and the control buttons. -/
inductive Conn | offline | connecting | online
  deriving DecidableEq, BEq

def Conn.label : Conn → String
  | .offline    => "offline"
  | .connecting => "connecting…"
  | .online     => "online"

structure Model where
  conn  : Conn
  draft : String
  log   : Array String

inductive Msg
  | connect
  | disconnect
  | opened
  | closed
  | errored (reason : String)
  | received (text : String)
  | typed (s : String)
  | send

/-- The key this app's one socket is opened under; `wsSend`/`wsClose` use it too. -/
def echo : String := "echo"

def transition (m : Model) : Msg → Model × Cmd Msg := steps
  | .connect    =>
      ({ m with conn := .connecting, draft := "" },   -- a fresh connection starts clean
       Cmd.wsOpen echo "/echo" Msg.received
          (onOpen := Msg.opened) (onClose := Msg.closed) (onError := Msg.errored))
  | .disconnect => (m, Cmd.wsClose echo)   -- the status flips when `onClose` fires
  | .opened     => { m with conn := .online,  log := m.log.push "● connected" }
  | .closed     => { m with conn := .offline, draft := "", log := m.log.push "○ disconnected" }
  | .errored r  => { m with conn := .offline, draft := "", log := m.log.push s!"✗ {r}" }
  | .received t => { m with log := m.log.push s!"← {t}" }
  | .typed s    => if m.conn = .online then { m with draft := s } else m  -- ignore typing while offline
  | .send       =>
      let t := m.draft.trimmed
      if t.isEmpty then m
      else ({ m with draft := "", log := m.log.push s!"→ {t}" }, Cmd.wsSend echo t)

-- The composer can only hold text while we're connected: typing is ignored unless online, and
-- the draft is cleared whenever the connection drops or restarts. So a half-typed message can
-- never linger in a state from which it could never be sent.
invariant composerOnlyWhenOnline :
    (fun m => m.draft ≠ "" → m.conn = .online) preserved_by transition

def logLine (line : String) : Html Msg := div [cls "line"] [text line]

def app : App Model Msg :=
  ui { conn := .offline, draft := "", log := #[] } transition fun m =>
    div [cls "ws"] [
      div [cls "bar"] [
        span [cls "status"] [text m.conn.label],
        button [cls "connect", onClick .connect, disabled (m.conn != .offline)] "Connect",
        button [cls "disconnect", onClick .disconnect, disabled (m.conn == .offline)] "Disconnect"
      ],
      div [cls "log"] (m.log.toList.map logLine),
      div [cls "composer"] [
        input [cls "draft", value m.draft, placeholder "Echo something…",
               onInput .typed, disabled (m.conn != .online)],
        button [cls "send", onClick .send, disabled (m.conn != .online)] "Send"
      ]
    ]

end Socket
