import Qed
open Qed

namespace Socket

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

def echo : String := "echo"

def transition (m : Model) : Msg → Model × Cmd Msg := steps
  | .connect    =>
      ({ m with conn := .connecting, draft := "" },
       Cmd.wsOpen echo "/echo" Msg.received
          (onOpen := Msg.opened) (onClose := Msg.closed) (onError := Msg.errored))
  | .disconnect => (m, Cmd.wsClose echo)
  | .opened     => { m with conn := .online,  log := m.log.push "● connected" }
  | .closed     => { m with conn := .offline, draft := "", log := m.log.push "○ disconnected" }
  | .errored r  => { m with conn := .offline, draft := "", log := m.log.push s!"✗ {r}" }
  | .received t => { m with log := m.log.push s!"← {t}" }
  | .typed s    => if m.conn = .online then { m with draft := s } else m
  | .send       =>
      let t := m.draft.trimmed
      if t.isEmpty then m
      else ({ m with draft := "", log := m.log.push s!"→ {t}" }, Cmd.wsSend echo t)

invariant composerOnlyWhenOnline (m) :
  m.draft ≠ "" → m.conn = .online preserved_by transition

def logLine (line : String) : Html Msg := <div class="line">{line}</div>

def app : App Model Msg :=
  ui { conn := .offline, draft := "", log := #[] } transition fun m =>
    <div class="ws">
      <div class="bar">
        <span class="status">{m.conn.label}</span>
        <button class="connect" onClick={.connect} disabled={m.conn != .offline}>Connect</button>
        <button class="disconnect" onClick={.disconnect} disabled={m.conn == .offline}>Disconnect</button>
      </div>
      <div class="log">{m.log.map logLine}</div>
      <div class="composer">
        <input class="draft" value={m.draft} placeholder="Echo something…"
               onInput={.typed} disabled={m.conn != .online}/>
        <button class="send" onClick={.send} disabled={m.conn != .online}>Send</button>
      </div>
    </div>

end Socket
