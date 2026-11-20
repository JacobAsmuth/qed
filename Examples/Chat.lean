import Qed
open Qed

namespace Chat

schema Turn:
  role    : String
  content : String

schema ChatReq:
  model    : String
  stream   : Bool
  messages : Turn[]

component Bubble:
  prop turn : Turn
  view: <div class={"msg user" if turn.role == "user" else "msg bot"}>{turn.content}</div>

end Chat

component Chat:
  state turns   : Turn[]
  state draft   = ""
  state pending = false

  action send:
    if not draft.trimmed.isEmpty:
      let convo = turns.push(Turn(role="user", content=draft.trimmed))
      turns = convo.push(Turn(role="assistant", content=""))
      draft = ""
      pending = true
      Cmd.streamJson("/v1/chat/completions", ChatReq(model="qed-mock", stream=true, messages=convo), .chunk, .done)
  action chunk(raw: String):
    let d = Json.pathStr(raw, "choices.0.delta.content")
    turns = turns.modify(turns.size - 1, t => { t with content = t.content ++ d })
  action done: pending = false

  invariant streamSafe: pending -> turns.size > 0

  view:
    <div class="chat">
      <div class="log">{for t in turns: <Bubble turn={t}/>}</div>
      <div class="composer">
        <input class="draft" placeholder="Message the model…" bind={draft}/>
        <button class="send" disabled={pending or draft.trimmed.isEmpty} onClick={.send}>Send</button>
      </div>
    </div>
