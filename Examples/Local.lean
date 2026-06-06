/-
  Local-state components — Qed's answer to React's `useState`, with the cell addressed
  by an explicit key, serialized, and owned by the driver *off* the verified virtual
  DOM. This demo exercises the whole feature:

  * **local state** — each row's `Widget` (a counter + a note) keeps state the parent
    never declares; touching one row leaves the root model and every sibling untouched.
  * **bubbling** — a `Widget`'s Report sends its count up to the root as a typed output.
  * **init-from-props** — each `Widget` is *seeded* from its row (its id, and its note
    pre-filled with the row label) via `.localInit`, React's `useState(propValue)`.
  * **nesting** — a `Widget` itself embeds a `Tag` local component (a pin toggle); the
    `Tag` bubbles its state up to its parent `Widget`, which shows it. Local components
    compose to any depth.

  Unmount GC and snapshot/restore are driver features the browser test drives directly.
  Pure Lean, total by construction; the browser entry is `Examples/LocalWeb.lean`.
-/
import Qed
open Qed

namespace Local

/-! A pin toggle nested *inside* `Widget`. It bubbles its new state up to its parent
    component (not the root) — the inner half of a two-level bubble chain. -/
namespace Tag

schema State where
  on : Codec.checkbox

inductive Msg | flip

def update (s : State) : Msg → State × Option Bool
  | .flip => ({ s with on := !s.on }, some (!s.on))   -- bubble the NEW pinned state

def view (s : State) : Html Msg :=
  button [cls (if s.on then "pin on" else "pin"), onClick .flip] [if s.on then "★ pinned" else "☆ pin"]

def reg : LocalDef := LocalDef.of "tag" { on := false } view update

end Tag

/-! A per-row widget: counter + note + a nested `Tag`. Its state is seeded from the row
    (`id`, and `note` pre-filled with the row label); `report` bubbles the count to the
    root, and `tagged` records what the nested `Tag` bubbled up. -/
namespace Widget

schema State where
  id     : Codec.nat
  count  : Codec.int
  note   : Codec.text
  pinned : Codec.checkbox

inductive Msg | inc | dec | setNote (s : String) | report | tagged (on : Bool)

def update (s : State) : Msg → State × Option Int
  | .inc       => ({ s with count := s.count + 1 }, none)
  | .dec       => ({ s with count := s.count - 1 }, none)
  | .setNote t => ({ s with note := t }, none)
  | .report    => (s, some s.count)
  | .tagged b  => ({ s with pinned := b }, none)        -- the nested Tag bubbled to us

def view (s : State) : Html Msg :=
  div [cls "widget"] [
    div [cls "counter"] [
      button [cls "dec", onClick .dec] "−",
      span   [cls "count"] [toString s.count],
      button [cls "inc", onClick .inc] "+"
    ],
    input [cls "note", value s.note, onInput .setNote, placeholder "a local note…"],
    button [cls "report", onClick .report] "Report ↑",
    span [cls "pinned"] [if s.pinned then "pinned" else ""],
    -- the nested local component: keyed by THIS widget's id (seeded from props), so two
    -- widgets' tags can't collide; its output bubbles back as `Widget.Msg.tagged`.
    div [localMountWith "tag" s!"t{s.id}" (fun on => some (Msg.tagged on))] []
  ]

def reg : LocalDef := LocalDef.of "widget" { id := 0, count := 0, note := "", pinned := false } view update

end Widget

/-- The root owns the shared list (ids + labels) and the last reported count. Per-row
    widget/tag state lives in the driver, keyed by row id. -/
structure Row where
  id    : Nat
  label : String

structure Model where
  rows       : Array Row
  draft      : String
  nextId     : Nat
  lastReport : Option (Nat × Int)

def init : Model :=
  { rows := #[{ id := 0, label := "Alpha" }, { id := 1, label := "Beta" }]
    draft := "", nextId := 2, lastReport := none }

inductive Msg
  | edit (s : String)
  | add
  | remove (id : Nat)
  | reported (id : Nat) (count : Int)

def update (m : Model) : Msg → Model
  | .edit s        => { m with draft := s }
  | .add           =>
      let t := m.draft.trimmed
      if t.isEmpty then m
      else { m with rows   := m.rows.push { id := m.nextId, label := t }
                    draft  := ""
                    nextId := m.nextId + 1 }
  | .remove id     => { m with rows := m.rows.filter (·.id != id) }
  | .reported id c => { m with lastReport := some (id, c) }

def view (m : Model) : Html Msg :=
  let report := match m.lastReport with
    | some (id, c) => s!"last report: row {id} = {c}"
    | none         => "no reports yet"
  div [cls "app"] [
    h1 [] "Local-state rows",
    div [cls "add"] [
      input  [cls "new", value m.draft, onInput .edit, placeholder "New row label"],
      button [cls "addbtn", onClick .add] "Add row"
    ],
    div [cls "report"] [report],
    ul [cls "rows"] (m.rows.map fun r =>
      li [key (toString r.id), cls "row"] [
        span [cls "label"] [r.label],
        -- the widget host, seeded from the row: id + note pre-filled with the label.
        -- a Report inside it bubbles the count up as `Msg.reported r.id`.
        div [(localMountWith "widget" (toString r.id) (fun c => some (Msg.reported r.id c))).localInit
              ({ id := r.id, count := 0, note := r.label, pinned := false } : Widget.State)] [],
        button [cls "rm", onClick (.remove r.id)] "✕"
      ]).toList
  ]

-- This view binds local-state component hosts (`localMountWith`) and computes a `let` before
-- the markup, so it goes in as an `Html` view via `View.ofHtml` (reconciled by the verified
-- diff, which preserves the local hosts) rather than the fine-grained lift.
def app : App Model Msg := mkApp init update (View.ofHtml view) (locals := [Widget.reg, Tag.reg])

end Local
