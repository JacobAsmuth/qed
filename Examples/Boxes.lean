/-
  A reusable component repeated per row.

  `Box` is a self-contained component — its own `Model` (an entry plus a local
  `expanded` flag), its own `Msg`, `update`, and `view`. The app holds an *array*
  of boxes built from a decoded JSON array and renders one per entry; each box's
  messages are tagged with its row index (`Msg.box i`), so a click in row 2 arrives
  as `Msg.box 2 .toggle` and toggles only that row.

  Nothing here is wired to a browser entry point; it is a buildable demonstration
  of `Qed.Component`. The same `app` would mount with `Qed.run` like any other.
-/
import Qed
open Qed

namespace Boxes

-- One row's data, decoded from JSON.
jsonStruct Entry where
  name  : String
  score : Nat
  bio   : String

-- The reusable box component: local state + its own messages.
namespace Box

structure Model where
  entry    : Entry
  expanded : Bool

inductive Msg
  | toggle

/-- Build a box's initial state from one entry (collapsed). -/
def init (e : Entry) : Model := { entry := e, expanded := false }

def update (m : Model) : Msg → Model
  | .toggle => { m with expanded := !m.expanded }

def view (m : Model) : Html Msg :=
  div [cls (if m.expanded then "box open" else "box")] [
    div [cls "row", onClick .toggle] [
      h2   []            [m.entry.name],       -- String child, no wrapper
      span [cls "score"] [m.entry.score]       -- Nat coerces to a text node
    ],
    if m.expanded then p [cls "bio"] [m.entry.bio] else .text ""
  ]

/-- The component value the app embeds. -/
def component : Component Model Msg := { update, view }

end Box

/-- The whole app state: one box model per row. -/
structure Model where
  boxes : Array Box.Model

/-- A parent message names the row it came from. -/
inductive Msg
  | box (i : Nat) (msg : Box.Msg)

def update (m : Model) : Msg → Model
  | .box i bm => { m with boxes := Box.component.updateAt m.boxes i bm }

def view (m : Model) : Html Msg :=
  div [cls "boxes"] (Box.component.viewList m.boxes Msg.box)

/-- A JSON array of entries — the kind of payload a file or API would return. -/
def sampleJson : String :=
  "[ {\"name\": \"Ada\",  \"score\": 9, \"bio\": \"Wrote the first algorithm.\"},
     {\"name\": \"Alan\", \"score\": 8, \"bio\": \"Asked what machines can decide.\"},
     {\"name\": \"Grace\",\"score\": 9, \"bio\": \"Found the first bug.\"} ]"

/-- Decode the array into `Array Entry`; malformed input yields no rows. -/
def loadEntries (s : String) : Array Entry :=
  match (Json.parse s).bind (fun j => (fromJson j : Except String (Array Entry))) with
  | .ok es   => es
  | .error _ => #[]

def init : Model := { boxes := (loadEntries sampleJson).map Box.init }

def app : App Model Msg := sandbox init update view

end Boxes
