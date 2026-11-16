import Qed
open Qed

namespace Socket

inductive Conn | offline | connecting | online
  deriving DecidableEq, BEq

def Conn.label : Conn → String
  | .offline    => "offline"
  | .connecting => "connecting…"
  | .online     => "online"

def echo : String := "echo"

component LogLine where
  prop text : String
  view => <div class="line">{text}</div>

app EchoSocket where
  state conn  : Conn         := .offline
  state draft                := ""
  state log   : Array String := #[]

  action connect =>
    conn := .connecting, draft := ""
    perform (Cmd.wsOpen echo "/echo" .received
      (onOpen := .opened) (onClose := .closed) (onError := .errored))
  action disconnect => perform (Cmd.wsClose echo)
  action opened => conn := .online, log := log.push "● connected"
  action closed => conn := .offline, draft := "", log := log.push "○ disconnected"
  action errored (r : String) => conn := .offline, draft := "", log := log.push s!"✗ {r}"
  action received (t : String) => log := log.push s!"← {t}"
  action typed (s : String) when conn = .online => draft := s
  action send when !draft.trimmed.isEmpty =>
    let t := draft.trimmed
    draft := "", log := log.push s!"→ {t}"
    perform (Cmd.wsSend echo t)

  invariant composerOnlyWhenOnline : draft ≠ "" → conn = .online

  view =>
    <div class="ws">
      <div class="bar">
        <span class="status">{conn.label}</span>
        <button class="connect" onClick={.connect} disabled={conn != .offline}>Connect</button>
        <button class="disconnect" onClick={.disconnect} disabled={conn == .offline}>Disconnect</button>
      </div>
      <div class="log">{log.map fun line => <LogLine text={line}/>}</div>
      <div class="composer">
        <input class="draft" bind={(draft, .typed)} placeholder="Echo something…"
               disabled={conn != .online}/>
        <button class="send" onClick={.send} disabled={conn != .online}>Send</button>
      </div>
    </div>

def app := EchoSocket.app

end Socket
