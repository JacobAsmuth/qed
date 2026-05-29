/-
  A streaming LLM chat — the whole app is this pure Lean.

  `update` is total and returns `(model, Cmd)`: most branches just return the next
  model (it coerces to "no effect"); `send` returns a `Cmd.stream` that the driver
  runs as a streaming POST, dispatching `.chunk` per Server-Sent-Event and `.done`
  at end of stream. JSON in (request body) and out (each chunk) goes through the
  verified `Qed.Json` parser/renderer.
-/
import Qed
open Qed

namespace Chat

/-- One turn of the conversation. -/
structure Turn where
  user? : Bool        -- true for the human, false for the assistant
  text  : String

/-- The whole UI state. -/
structure Model where
  turns   : Array Turn
  draft   : String    -- the composer's text
  pending : Bool       -- a reply is currently streaming

inductive Msg
  | typed (s : String)    -- composer edited
  | send                  -- submit the draft
  | chunk (data : String) -- one streamed SSE payload (an OpenAI delta object)
  | done                  -- stream finished

/-- Extract `choices[0].delta.content` from one OpenAI stream chunk. -/
def deltaOf (raw : String) : String :=
  (Json.parse raw).toOption
    |>.bind (·.get? "choices") |>.bind (·.arr?) |>.bind (·.head?)
    |>.bind (·.get? "delta")   |>.bind (·.get? "content") |>.bind (·.str?)
    |>.getD ""

/-- The OpenAI-style request body for the conversation so far. -/
def reqBody (turns : Array Turn) : String :=
  Json.render (.obj [
    ("model",    .str "qed-mock"),
    ("stream",   .bool true),
    ("messages", .arr (turns.toList.map fun t =>
      .obj [("role", .str (if t.user? then "user" else "assistant")),
            ("content", .str t.text)]))
  ])

/-- Append streamed text onto the last (assistant) turn. -/
def appendLast (turns : Array Turn) (d : String) : Array Turn :=
  turns.modify (turns.size - 1) fun t => { t with text := t.text ++ d }

def update (m : Model) : Msg → Model × Cmd Msg
  | .typed s   => ({ m with draft := s }, .none)
  | .send      =>
      let draft := m.draft.trim
      if draft.isEmpty then (m, .none) else
      let convo := m.turns.push { user? := true, text := draft }
      ({ turns   := convo.push { user? := false, text := "" }
         draft   := ""
         pending := true },
       .stream "/v1/chat/completions" (reqBody convo) .chunk .done)
  | .chunk raw => ({ m with turns := appendLast m.turns (deltaOf raw) }, .none)
  | .done      => ({ m with pending := false }, .none)

def bubble (t : Turn) : Html Msg :=
  div [cls (if t.user? then "msg user" else "msg bot")] [t.text]

def view (m : Model) : Html Msg :=
  div [cls "chat"] [
    div [cls "log"] (m.turns.toList.map bubble),
    div [cls "composer"] [
      input [cls "draft", placeholder "Message the model…", value m.draft, onInput .typed],
      button [cls "send", disabled (m.pending || m.draft.trim.isEmpty), onClick .send] "Send"
    ]
  ]

def chatApp : App Model Msg :=
  application { turns := #[], draft := "", pending := false } update view

end Chat
