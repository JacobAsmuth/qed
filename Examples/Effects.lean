/-
  Native effects — a tour of the typed `Cmd`s Qed ships, plus the port escape hatch.

  `update` stays pure and total; every side effect is described as data in `effects`
  and interpreted by the driver:

  * **localStorage** — the count is persisted on every change and reloaded at startup,
    so it survives a page refresh.
  * **document.title**, **timer** (`after`), **randomness** (`randomInt`), **focus**,
    **file pick** (`pickFile`), and **batch** (two effects from one message).
  * **ports** — "Ping" sends to a userland JS handler the app registers on
    `globalThis.__qed.ports`, which echoes back via `__qed.send` → `onPort`. No effect
    here required a new framework constructor.

  Pure Lean, total by construction; the browser entry is `Examples/EffectsWeb.lean`.
-/
import Qed
open Qed

namespace Effects

structure Model where
  count  : Int
  title  : String     -- draft for the document title
  status : String     -- a single line the test reads back

def init : Model := { count := 0, title := "", status := "ready" }

inductive Msg
  | inc | dec
  | loaded (v : Option String)            -- the persisted count, read at startup
  | editTitle (s : String)
  | applyTitle
  | roll | rolled (n : Int)
  | delayed | tick
  | ping | gotEcho (s : String)
  | pick | picked (r : Except String FilePick)
  | focusTitle
  | saveBatch

def update (m : Model) : Msg → Model
  | .inc        => { m with count := m.count + 1 }
  | .dec        => { m with count := m.count - 1 }
  | .loaded v   => { m with count := (v.bind (·.toInt?)).getD m.count }
  | .editTitle s => { m with title := s }
  | .rolled n   => { m with status := s!"rolled: {n}" }
  | .delayed    => { m with status := "waiting…" }
  | .tick       => { m with status := "delayed!" }
  | .gotEcho s  => { m with status := s!"echo: {s}" }
  | .picked r   => { m with status := match r with
                                      | .ok f    => s!"file: {f.name}={f.text}"
                                      | .error e => s!"file error: {e}" }
  | .saveBatch  => { m with status := "saved+titled" }
  | _           => m

-- Effects run on the POST-update model, so `count` here is already the new value.
def effects (m : Model) : Msg → Cmd Msg
  | .inc | .dec => Cmd.storageSet "count" (toString m.count)   -- persist after the change
  | .applyTitle => Cmd.setTitle m.title
  | .roll       => Cmd.randomInt 1 6 .rolled
  | .delayed    => Cmd.after 300 .tick                          -- debounce/delay building block
  | .ping       => Cmd.port "echo" "ping"                       -- → userland JS, comes back via onPort
  | .pick       => Cmd.pickFile ".txt,text/*" .picked
  | .focusTitle => Cmd.focus "title-input"
  | .saveBatch  => Cmd.batch [Cmd.storageSet "count" (toString m.count), Cmd.setTitle "Saved!"]
  | _           => .none

-- The subscription side of ports: turn an inbound `__qed.send(name, payload)` into a Msg.
def onPort : String → String → Option Msg
  | "echo", payload => some (.gotEcho payload)
  | _,      _       => none

def view (m : Model) : Html Msg :=
  div [cls "app"] [
    div [cls "counter"] [
      button [cls "dec", onClick .dec] "−",
      span   [cls "count", attr "id" "count"] [toString m.count],
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
    div [cls "status", attr "id" "status"] [m.status]
  ]

-- Startup effect: load the persisted count before the first render. (`application`
-- defaults the startup effect to none, so we override `init` on the built app.)
def app : App Model Msg :=
  { application init update view (effects := effects) (onPort := some onPort) with
    init := (init, Cmd.storageGet "count" .loaded) }

end Effects
