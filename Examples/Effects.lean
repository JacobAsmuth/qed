/-
  Native effects — a tour of the typed `Cmd`s Qed ships, the typed `ports` escape
  hatch, keyed-timer debounce, and a startup effect.

  `update` stays pure and total; every side effect is described as data in `effects`:

  * **localStorage** — the count is persisted on change and hydrated at *startup*
    (the `start` effect), so it survives a refresh.
  * **document.title**, **randomness**, **focus**, **file pick**, and **batch**.
  * **debounce** — typing in the search box schedules `afterKeyed "search"`, so only the
    last keystroke's timer survives.
  * **ports** — the `ports` command declares typed channels; "Ping" sends one to a
    userland JS handler that echoes back, decoded straight into a message. No string
    juggling, and no effect here needed a new framework constructor.

  Pure Lean, total by construction; the browser entry is `Examples/EffectsWeb.lean`.
-/
import Qed
open Qed

namespace Effects

structure Model where
  count    : Int
  title    : String     -- draft for the document title
  query    : String     -- the search box
  searches : Nat        -- how many searches actually ran (debounce proof)
  status   : String     -- a single line the test reads back

def init : Model := { count := 0, title := "", query := "", searches := 0, status := "ready" }

inductive Msg
  | inc | dec
  | loaded (v : Option String)            -- the persisted count, read at startup
  | editTitle (s : String) | applyTitle
  | roll | rolled (n : Int)
  | delayed | tick
  | ping | gotEcho (s : String)
  | pick | picked (r : Except String FilePick)
  | focusTitle
  | saveBatch
  | typeSearch (s : String) | runSearch (s : String)

-- Typed ports: `echoOut` sends a String to JS; `echoIn` decodes an inbound String into
-- `Msg.gotEcho`. The command also generates `onPort` (used by `app` below).
ports where
  echoOut : String
  echoIn  : String => .gotEcho

def update (m : Model) : Msg → Model
  | .inc         => { m with count := m.count + 1 }
  | .dec         => { m with count := m.count - 1 }
  | .loaded v    => { m with count := (v.bind (·.toInt?)).getD m.count }
  | .editTitle s => { m with title := s }
  | .rolled n    => { m with status := s!"rolled: {n}" }
  | .delayed     => { m with status := "waiting…" }
  | .tick        => { m with status := "delayed!" }
  | .gotEcho s   => { m with status := s!"echo: {s}" }
  | .picked r    => { m with status := match r with
                                       | .ok f    => s!"file: {f.name}={f.text}"
                                       | .error e => s!"file error: {e}" }
  | .saveBatch   => { m with status := "saved+titled" }
  | .typeSearch s => { m with query := s }
  | .runSearch s  => { m with status := s!"searched: {s}", searches := m.searches + 1 }
  | _            => m

-- Effects run on the POST-update model, so `count`/`query` here are already updated.
def effects (m : Model) : Msg → Cmd Msg
  | .inc | .dec   => Cmd.storageSet "count" (toString m.count)   -- persist after the change
  | .applyTitle   => Cmd.setTitle m.title
  | .roll         => Cmd.randomInt 1 6 .rolled
  | .delayed      => Cmd.after 300 .tick
  | .ping         => echoOut "ping"                              -- typed outbound port
  | .pick         => Cmd.pickFile ".txt,text/*" .picked
  | .focusTitle   => Cmd.focus "title-input"
  | .saveBatch    => Cmd.batch [Cmd.storageSet "count" (toString m.count), Cmd.setTitle "Saved!"]
  | .typeSearch s => Cmd.afterKeyed "search" 200 (.runSearch s) -- debounce: only the last survives
  | _             => .none

-- One transition: the state change (`update`) plus the effect it triggers (`effects`).
def transition (m : Model) (msg : Msg) : Model × Cmd Msg :=
  let m' := update m msg; (m', effects m' msg)

-- `start` hydrates the count from localStorage before the first render; the generated
-- `onPort` routes inbound port messages.
def app : App Model Msg :=
  ui init transition (onPort := some onPort) (start := Cmd.storageGet "count" .loaded) fun m =>
    div [cls "app"] [
      div [cls "counter"] [
        button [cls "dec", onClick .dec] "−",
        span   [cls "count", attr "id" "count"] [text (toString m.count)],
        button [cls "inc", onClick .inc] "+"
      ],
      input  [attr "id" "title-input", cls "title", value m.title, onInput .editTitle, placeholder "page title"],
      button [cls "apply",  onClick .applyTitle] "Set title",
      button [cls "roll",   onClick .roll]       "Roll d6",
      button [cls "delay",  onClick .delayed]    "Delayed",
      button [cls "ping",   onClick .ping]       "Ping",
      button [cls "pick",   onClick .pick]       "Pick file",
      button [cls "focus",  onClick .focusTitle] "Focus title",
      button [cls "save",   onClick .saveBatch]  "Save (batch)",
      input  [cls "search", value m.query, onInput .typeSearch, placeholder "debounced search"],
      span   [cls "searches", attr "id" "searches"] [text (toString m.searches)],
      div [cls "status", attr "id" "status"] [text m.status]
    ]

end Effects
