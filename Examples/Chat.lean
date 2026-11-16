import Qed
open Qed

namespace Chat

structure Turn where
  user? : Bool
  text  : String

def deltaOf (raw : String) : String :=
  (Json.parse raw).toOption
    |>.bind (·.get? "choices") |>.bind (·.arr?) |>.bind (·.head?)
    |>.bind (·.get? "delta")   |>.bind (·.get? "content") |>.bind (·.str?)
    |>.getD ""

def reqBody (turns : Array Turn) : String :=
  Json.render (.obj [
    ("model",    .str "qed-mock"),
    ("stream",   .bool true),
    ("messages", .arr (turns.toList.map fun t =>
      .obj [("role", .str (if t.user? then "user" else "assistant")),
            ("content", .str t.text)]))
  ])

def appendLast (turns : Array Turn) (d : String) : Array Turn :=
  turns.modify (turns.size - 1) fun t => { t with text := t.text ++ d }

component Bubble where
  prop turn : Turn
  view => <div class={if turn.user? then "msg user" else "msg bot"}>{turn.text}</div>

end Chat

component Chat where
  state turns   : Array Turn := #[]
  state draft                := ""
  state pending              := false

  action send when !draft.trimmed.isEmpty =>
    let text := draft.trimmed
    let convo := turns.push { user? := true, text }
    turns   := convo.push { user? := false, text := "" }
    draft   := ""
    pending := true
    perform (Cmd.stream "/v1/chat/completions" (reqBody convo) .chunk .done)
  action chunk (raw : String) => turns := appendLast turns (deltaOf raw)
  action done                 => pending := false

  invariant streamSafe : pending = true → 0 < turns.size

  view =>
    <div class="chat">
      <div class="log">{for t in turns => <Bubble turn={t}/>}</div>
      <div class="composer">
        <input class="draft" placeholder="Message the model…" bind={draft}/>
        <button class="send" disabled={pending || draft.trimmed.isEmpty} onClick={.send}>Send</button>
      </div>
    </div>
