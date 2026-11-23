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

  ws "/proto/:topic"
    proto(topic: String) -> Proto(PriceTick):
      reconnect fixed(70, 2)
      send(cmd: Proto(PricePing))

server Hub:
  state online    : Nat       = 0
  state totalMsgs : Nat       = 0
  state recent    : ChatMsg[] = []

  invariant msgsMonotonic: totalMsgs >= old(totalMsgs)
  invariant roomsValid: all m in recent: m.roomId <= 100

  def onlineCount() -> Nat:
    return online

  def announce(roomId: Nat, text: String) -> ChatMsg!:
    requires ctx.userId != none
    requires roomId <= 100, 1 <= text.length <= 280
    ensures result.roomId == roomId
    let who = ctx.userId.getD("system")
    if not (1 <= who.length <= 64): return fail(.invalidAuthor)
    let m = ChatMsg(roomId=roomId, author=who, body=text)
    room.emit(roomId, m)
    if text == "ROLLBACK": return fail(.rejected)
    recent.push(m)
    totalMsgs += 1
    return m

  channel room(id: Nat) -> ChatMsg:
    requires ctx.userId != none
    requires id <= 100
    ensures event.roomId == id
    reconnect backoff(100, 2000)

    on_join -> RoomSnapshot:
      online += 1
      return RoomSnapshot(roomId=id, online=online, history=recent)

    on_send(body: String):
      requires 1 <= body.length <= 280
      let who = ctx.userId.getD("anon")
      if 1 <= who.length <= 64:
        let m = ChatMsg(roomId=id, author=who, body=body)
        recent.push(m)
        totalMsgs += 1
        room.emit(id, m)

    on_leave:
      if online > 0: online -= 1

def statusLabel : Qed.SocketStatus → String
  | .disconnected   => "disconnected"
  | .connecting     => "connecting"
  | .connected      => "connected"
  | .reconnecting n => s!"reconnecting:{n}"
  | .failed e       => s!"failed:{e}"

component LiveApp:
  session user
  route : R = .home:
    case .home:    pass
    case .room(_): pass

  state onlineCount : Nat       = 0
  state messages    : ChatMsg[] = []
  state lastPrice   : Nat       = 0
  state draft       : String    = ""
  state symbol      : String    = "BTC"

  invariant allMsgsValidRoom: all m in messages: m.roomId <= 100

  subscribe chat = Hub.room(id) if let .room(id) = route, id <= 100, user.isSome:
    reconnect backoff(80, 1000)
    on_join(snap):
      onlineCount = snap.online
      messages = snap.history
    on_message(msg):
      messages.push(msg)

  subscribe ticker = TickerWs.ticks(symbol) if 1 <= symbol.length <= 16:
    on_message(t): lastPrice = t.price

  subscribe protoFeed = TickerWs.proto("btc"):
    on_message(t): lastPrice = t.price

  action sendChat:
    if 1 <= draft.length <= 280:
      chat.send(draft)
      draft = ""

  action pingTicker:
    ticker.send(PricePing(action="ping"))

  view:
    <div class="live-room">
      <nav>
        <a href={R.home}>Home</a>
        <a href={R.room(1)}>Room 1</a>
        <a href={R.room(2)}>Room 2</a>
      </nav>
      <p class="chat-status">{statusLabel(chat)} · Online: {onlineCount} · {symbol}: {lastPrice}</p>
      <ul class="msg-list">
        {for m in messages:
          <li key={f"{m.roomId}:{m.author}:{m.body}"}>{f"[{m.roomId}] {m.author}: {m.body}"}</li>}
      </ul>
      <input class="draft-input" bind={draft} />
      <button onClick={.sendChat}>Send</button>
      <button onClick={.pingTicker}>Ping Ticker</button>
    </div>

fullstack App:
  server Hub
  client LiveApp
  title "LiveRoom"

end LiveRoom
