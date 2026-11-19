import Qed
open Qed

namespace LiveRoom

router R:
  home = "/"
  room(id: Nat) = "/rooms/:id"

schema ChatMsg:
  roomId : Nat    where roomId <= 100
  author : String where 1 <= author.length <= 64
  body   : String where 1 <= body.length <= 280

schema RoomSnapshot:
  roomId  : Nat       where roomId <= 100
  connId  : String
  online  : Nat
  history : ChatMsg[]

schema PriceTick:
  symbol : String
  price  : Nat

schema PricePing:
  action : String

external TickerWs:
  base "ws://127.0.0.1:19455"

  ws "/ticks/:symbol"
    ticks(symbol: String) -> PriceTick:
      requires 1 <= symbol.length <= 16
      reconnect fixed(120, 3)
      send(cmd: PricePing)

external RawFeedWs:
  base "ws://127.0.0.1:19455"

  ws "/raw/:tag"
    stream(tag: String) -> String:
      reconnect off
      send(msg: String)

external ProtoFeedWs:
  base "ws://127.0.0.1:19455"

  ws "/proto/:topic"
    stream(topic: String) -> Proto(PriceTick):
      reconnect fixed(70, 2)
      send(cmd: Proto(PricePing))

server Hub:
  state online      : Nat       = 0
  state totalMsgs   : Nat       = 0
  state recent      : ChatMsg[] = []
  state activeConns : String[]  = []

  invariant totalMsgs >= old(totalMsgs)
  invariant all m in recent: m.roomId <= 100

  def onlineCount() -> Nat:
    return online

  def activeConnsList() -> String[]:
    return activeConns

  def announce(roomId: Nat, text: String) -> ChatMsg!:
    requires ctx.userId != none
    requires roomId <= 100, 1 <= text.length <= 280
    ensures result.roomId == roomId
    let who = ctx.userId.getD("system")
    ensure 1 <= who.length <= 64 else fail(.invalidAuthor)
    let m = ChatMsg(roomId=roomId, author=who, body=text)
    emit room(roomId, m)
    ensure text != "ROLLBACK" else fail(.rejected)
    recent.push(m)
    totalMsgs += 1
    return m

  def broadcastAlert(text: String) -> Unit:
    emit alerts(text)
    return ()

  channel room(id: Nat) -> ChatMsg:
    requires ctx.userId != none
    requires id <= 100
    ensures event.roomId == id
    reconnect backoff(100, 2000)

    on_join -> RoomSnapshot:
      online += 1
      activeConns.push(ctx.connId)
      return RoomSnapshot(roomId=id, connId=ctx.connId, online=online, history=recent)

    on_send(body: String):
      requires 1 <= body.length <= 280
      let who = ctx.userId.getD("anon")
      if 1 <= who.length <= 64:
        let m = ChatMsg(roomId=id, author=who, body=body)
        recent.push(m)
        totalMsgs += 1
        emit room(id, m)

    on_leave:
      if online > 0:
        online -= 1
      activeConns = activeConns.filter(c => c != ctx.connId)

  channel alerts() -> String:
    on_join:
      pass
    on_leave:
      pass

def statusLabel (s : Qed.SocketStatus) : String :=
  match s with
  | .disconnected => "disconnected"
  | .connecting => "connecting"
  | .connected => "connected"
  | .reconnecting n => s!"reconnecting:{n}"
  | .failed e => s!"failed:{e}"

component LiveApp:
  session user
  route : R = .home:
    case .home:
      pass
    case .room(_):
      pass

  state onlineCount      : Nat       = 0
  state myConnId         : String    = ""
  state messages         : ChatMsg[] = []
  state lastAlert        : String    = ""
  state alertStatusCount : Nat       = 0
  state lastPrice        : Nat       = 0
  state lastRaw          : String    = ""
  state lastProtoPrice   : Nat       = 0
  state protoStatusCount : Nat       = 0
  state joinedCount      : Nat       = 0
  state extJoined        : Nat       = 0
  state draft            : String    = ""
  state symbol           : String    = "BTC"

  invariant allMsgsValidRoom:
    all m in messages: m.roomId <= 100

  subscribe chat = Hub.room(id) if let .room(id) = route, id <= 100, user.isSome:
    reconnect backoff(80, 1000)
    on_join(snap):
      onlineCount = snap.online
      myConnId = snap.connId
      messages = snap.history
      joinedCount += 1
    on_message(msg):
      messages.push(msg)

  subscribe alertFeed = Hub.alerts():
    reconnect off
    on_message(a):
      lastAlert = a
    on_status(_st):
      alertStatusCount += 1

  subscribe ticker = TickerWs.ticks(symbol) if 1 <= symbol.length <= 16:
    on_join:
      extJoined += 1
    on_message(t):
      lastPrice = t.price

  subscribe rawFeed = RawFeedWs.stream("log"):
    on_message(s):
      lastRaw = s

  subscribe protoFeed = ProtoFeedWs.stream("btc"):
    on_message(t):
      lastProtoPrice = t.price
    on_status(_st):
      protoStatusCount += 1

  action setDraft(v: String):
    draft = v

  action sendChat:
    if 1 <= draft.length <= 280:
      send chat(draft)
      draft = ""

  action pingTicker:
    send ticker(PricePing(action="ping"))

  action pingRaw:
    send rawFeed("raw-hello")

  action pingProto:
    send protoFeed(PricePing(action="proto-ping"))

  view:
    <div class="live-room">
      <nav>
        <a href={R.home} class="nav-home">Home</a>
        <a href={R.room(1)} class="nav-room-1">Room 1</a>
        <a href={R.room(2)} class="nav-room-2">Room 2</a>
      </nav>
      <p class="chat-status">{statusLabel(chat)}</p>
      <p class="alert-status">{statusLabel(alertFeed)}</p>
      <p class="alert-status-count">{alertStatusCount}</p>
      <p class="ticker-status">{statusLabel(ticker)}</p>
      <p class="raw-status">{statusLabel(rawFeed)}</p>
      <p class="proto-status">{statusLabel(protoFeed)}</p>
      <p class="proto-status-count">{protoStatusCount}</p>
      <p class="my-conn-id">{myConnId}</p>
      <p class="online-count">{onlineCount}</p>
      <p class="joined-count">{joinedCount}</p>
      <p class="ext-joined">{extJoined}</p>
      <p class="last-alert">{lastAlert}</p>
      <p class="last-price">{lastPrice}</p>
      <p class="last-raw">{lastRaw}</p>
      <p class="last-proto-price">{lastProtoPrice}</p>
      <ul class="msg-list">
        {for m in messages:
          <li class="msg-item" key={f"{m.roomId}:{m.author}:{m.body}"}>{f"[{m.roomId}] {m.author}: {m.body}"}</li>}
      </ul>
      <input class="draft-input" bind={draft} />
      <button class="send-btn" onClick={.sendChat}>Send</button>
      <button class="ping-ticker-btn" onClick={.pingTicker}>Ping Ticker</button>
      <button class="ping-raw-btn" onClick={.pingRaw}>Ping Raw</button>
      <button class="ping-proto-btn" onClick={.pingProto}>Ping Proto</button>
    </div>

fullstack App:
  server Hub
  client LiveApp
  title "LiveRoom"

end LiveRoom
