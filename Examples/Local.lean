/-
  Tour 08 · The `component` declaration

  Local-state components: Qed's answer to React's `useState`, declared with `component`,
  state next to the view that uses it, the cell addressed by an explicit key, serialized,
  and owned by the driver *off* the verified virtual DOM. This demo exercises the whole
  feature:

  * **`set`**: each distinct site becomes one first-order `Msg` constructor, interpreted
    by a generated `update` against the state at delivery time, never a closure. The
    `Stepper` proves it: `invariant … preserved_by Stepper.update` reduces arm by arm,
    and dropping its clamp fails the build naming the guilty case (`set_count`).
  * **local state**: each row's `Widget` (a counter + a note) keeps state the parent
    never declares; touching one row leaves the root model and every sibling untouched.
  * **bubbling**: a `Widget`'s Report `send`s its count up to the root as a typed output.
  * **init-from-props**: each `Widget` is *seeded* from its row (its id, and its note
    pre-filled with the row label) via `.localInit`, React's `useState(propValue)`.
  * **nesting**: a `Widget` itself hosts a `Tag` component (a pin toggle); the `Tag`
    sends its state up to its parent `Widget` (`mountWith` + a payload-form `set`),
    which shows it. Components compose to any depth.

  Unmount GC and snapshot/restore are driver features the browser test drives directly.
  Pure Lean, total by construction; the browser entry is `Examples/LocalWeb.lean`.
-/
import Qed
open Qed

namespace Local

/-- A guarded counter with a save slot. Three kinds of `set` site: an expression over the
    field itself (inc, and the clamped dec the invariant below rides on), a cross-field
    read at delivery time (`set saved count`), and the constant reset. -/
component Stepper where
  state count : Int := 0
  state saved : Int := 0
  view =>
    <div class="stepper">
      <button class="dec" onClick={set count (if count ≤ 0 then 0 else count - 1)}>−</button>
      <span class="count">{count}</span>
      <button class="inc" onClick={set count (count + 1)}>+</button>
      <button class="save" onClick={set saved count}>save</button>
      <span class="savedv">{saved}</span>
    </div>

-- The generated `update` is data with named cases, so the invariant machinery applies
-- unchanged: drop the clamp above and the build fails with "case `set_count` still
-- needs: 0 ≤ m.count - 1", the `set` site that broke it, by name.
invariant stepperSafe : (fun s => 0 ≤ s.count) preserved_by Stepper.update

/-- A pin toggle nested *inside* `Widget`: one click flips the pin and `send`s the NEW
    state up to its parent component (not the root), the inner half of a two-level
    bubble chain. -/
component Tag where
  state on : Bool := false
  emits Bool
  view =>
    <button class={if on then "pin on" else "pin"} onClick={set on (!on), send (!on)}>
      {if on then "★ pinned" else "☆ pin"}</button>

/-- A per-row widget: counter + note + a nested `Tag`. Its state is seeded from the row
    (`id`, and `note` pre-filled with the row label); Report `send`s the count to the
    root, and the nested `Tag`'s output lands in `pinned` (a payload-form `set`), keyed
    by THIS widget's id so two widgets' tags can't collide. -/
component Widget where
  state id     : Nat    := 0
  state count  : Int    := 0
  state note   : String := ""
  state pinned : Bool   := false
  emits Int
  view =>
    <div class="widget">
      <div class="counter">
        <button class="dec" onClick={set count (count - 1)}>−</button>
        <span class="count">{toString count}</span>
        <button class="inc" onClick={set count (count + 1)}>+</button>
      </div>
      <input class="note" value={note} onInput={set note} placeholder="a local note…"/>
      <button class="report" onClick={send count}>Report ↑</button>
      <span class="pinned">{if pinned then "pinned" else ""}</span>
      <div {Tag.mountWith s!"t{id}" (set pinned)}/>
    </div>

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
  let report := (match m.lastReport with
    | some (id, c) => s!"last report: row {id} = {c}"
    | none         => "no reports yet");
  <div class="app">
    <h1>Local-state rows</h1>
    <div class="add">
      <input class="new" value={m.draft} onInput={.edit} placeholder="New row label"/>
      <button class="addbtn" onClick={.add}>Add row</button>
    </div>
    <div class="report">{report}</div>
    <div class="solo" {Stepper.mount "s"}/>
    <ul class="rows">{m.rows.map fun r =>
      -- each row hosts a widget, seeded from the row: id + note pre-filled with the
      -- label. a Report inside it bubbles the count up as `Msg.reported r.id`.
      <li key={toString r.id} class="row">
        <span class="label">{r.label}</span>
        <div {(Widget.mountWith (toString r.id) (Msg.reported r.id)).localInit
              ({ id := r.id, count := 0, note := r.label, pinned := false } : Widget.State)}/>
        <button class="rm" onClick={.remove r.id}>✕</button>
      </li>}</ul>
  </div>

-- This view binds component hosts (`Widget.mountWith`) and computes a `let` before
-- the markup, so it goes in as an `Html` view via `View.ofHtml` (reconciled by the verified
-- diff, which preserves the local hosts) rather than the fine-grained lift.
def app : App Model Msg :=
  mkApp init update (View.ofHtml view) (locals := [Stepper.reg, Widget.reg, Tag.reg])

end Local
