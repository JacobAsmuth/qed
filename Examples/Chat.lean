import Qed
open Qed

namespace Chat

structure Turn where
  user? : Bool
  text  : String

structure Model where
  turns   : Array Turn
  draft   : String
  pending : Bool

inductive Msg
  | typed (s : String)
  | send
  | chunk (data : String)
  | done

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

def transition (m : Model) : Msg → Model × Cmd Msg := steps
  | .typed s   => { m with draft := s }
  | .send      =>
      let draft := m.draft.trimmed
      if draft.isEmpty then m else
      let convo := m.turns.push { user? := true, text := draft }
      ({ turns   := convo.push { user? := false, text := "" }
         draft   := ""
         pending := true },
       .stream "/v1/chat/completions" (reqBody convo) .chunk .done)
  | .chunk raw => { m with turns := appendLast m.turns (deltaOf raw) }
  | .done      => { m with pending := false }

invariant streamSafe : (fun m => m.pending = true → 0 < m.turns.size)
    preserved_by transition

def bubble (t : Turn) : Html Msg :=
  <div class={if t.user? then "msg user" else "msg bot"}>{t.text}</div>

def chatApp : App Model Msg :=
  ui { turns := #[], draft := "", pending := false } transition fun m =>
    <div class="chat">
      <div class="log">{m.turns.map bubble}</div>
      <div class="composer">
        <input class="draft" placeholder="Message the model…" value={m.draft} onInput={.typed}/>
        <button class="send" disabled={m.pending || m.draft.trimmed.isEmpty} onClick={.send}>Send</button>
      </div>
    </div>

end Chat
