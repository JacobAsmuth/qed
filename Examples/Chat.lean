/-
  A streaming LLM chat — the whole app is this pure Lean.

  `update` is total and pure (`Model → Msg → Model`). Effects live in a separate
  `effects` function: `send` maps to a `Cmd.stream` that the driver runs as a
  streaming POST, dispatching `.chunk` per Server-Sent-Event and `.done` at end of
  stream. JSON in (request body) and out (each chunk) goes through the verified
  `Qed.Json` parser/renderer.
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

/-- One combined `transition`: each arm returns the next model (`still`) or the next model
    plus the effect it triggers (`also`). `send` builds the conversation, appends the empty
    assistant turn to stream into, and starts the streaming POST — all in one place, with no
    separate `effects` function and no reconstructing what an `update` already did. -/
def transition (m : Model) : Msg → Model × Cmd Msg
  | .typed s   => still { m with draft := s }
  | .send      =>
      let draft := m.draft.trim
      if draft.isEmpty then still m else
      let convo := m.turns.push { user? := true, text := draft }
      also { turns   := convo.push { user? := false, text := "" }
             draft   := ""
             pending := true }
           (.stream "/v1/chat/completions" (reqBody convo) .chunk .done)
  | .chunk raw => still { m with turns := appendLast m.turns (deltaOf raw) }
  | .done      => still { m with pending := false }

def bubble (t : Turn) : Html Msg :=
  div [cls (if t.user? then "msg user" else "msg bot")] [t.text]

def chatApp : App Model Msg :=
  ui { turns := #[], draft := "", pending := false } transition fun m =>
    div [cls "chat"] [
      div [cls "log"] (m.turns.toList.map bubble),
      div [cls "composer"] [
        input [cls "draft", placeholder "Message the model…", value m.draft, onInput .typed],
        button [cls "send", disabled (m.pending || m.draft.trim.isEmpty), onClick .send] "Send"
      ]
    ]

end Chat
