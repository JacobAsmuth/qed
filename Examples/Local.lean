/-
  Tour 08 · The `component` declaration

  Local-state components: Qed's answer to React's `useState`, declared with `component`,
  state next to the view that uses it, the cell addressed by an explicit key, serialized,
  and owned by the driver *off* the verified virtual DOM. This demo exercises the whole
  feature:

  * **`set`**: each distinct site becomes one first-order `Msg` constructor, interpreted
    by a generated `update` against the state at delivery time, never a closure. The
    `Stepper` proves it: `invariant … preserved_by Stepper.update` reduces arm by arm,
    and dropping its clamp fails the build naming the guilty case (`decrement`).
  * **local state**: each row's `Widget` (a counter + a note) keeps state the parent
    never declares; touching one row leaves the root model and every sibling untouched.
  * **bubbling**: a `Widget`'s Report `send`s its count up to the root as a typed output
    (the tag's `onEmit={…}`).
  * **props and state**: `id` and `label` are live props; `initial` seeds the note.
    Renaming a row refreshes its label without overwriting the edited note.
  * **nesting**: a `Widget` itself hosts a `Tag` component (a pin toggle); the `Tag`
    sends its state up to its parent `Widget` (`onEmit` + a payload-form `set`),
    which shows it. Components compose to any depth, and every component a view's
    tags reach is registered automatically (no `locals := …` anywhere here).

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
  action decrement => set count (if count ≤ 0 then 0 else count - 1)
  action increment => set count (count + 1)
  action save => set saved count
  view =>
    <div class="stepper">
      <button class="dec" onClick={.decrement}>−</button>
      <span class="count">{count}</span>
      <button class="inc" onClick={.increment}>+</button>
      <button class="save" onClick={.save}>save</button>
      <span class="savedv">{saved}</span>
    </div>

-- The generated `update` is data with named cases, so the invariant machinery applies
-- unchanged: drop the clamp above and the build fails with "case `decrement` still
-- needs: 0 ≤ m.count - 1", the `set` site that broke it, by name.
invariant stepperSafe : (fun s => 0 ≤ s.count) preserved_by Stepper.update

/-- A pin toggle nested *inside* `Widget`: one click flips the pin and `send`s the NEW
    state up to its parent component (not the root), the inner half of a two-level
    bubble chain. -/
component Tag where
  prop label : String := "Pin"
  state on : Bool := false
  emits Bool
  action toggle => set on (!on), send (!on)
  view =>
    <button title={label} class={if on then "pin on" else "pin"} onClick={.toggle}>
      {if on then "★ pinned" else "☆ pin"}</button>

/-- A per-row widget: counter + note + a nested `Tag`. Its id and label are live props;
    its note starts from the row label. Report `send`s the count to the
    root, and the nested `Tag`'s output lands in `pinned` (a payload-form `set`), keyed
    by THIS widget's id so two widgets' tags can't collide. -/
component Widget where
  prop id : Nat
  prop label : String
  state count  : Int    := 0
  state note   : String := ""
  state pinned : Bool   := false
  emits Int
  action resetNote => set note label
  view =>
    <div class="widget">
      <span class="live-label">{label}</span>
      <div class="counter">
        <button class="dec" onClick={set count (count - 1)}>−</button>
        <span class="count">{toString count}</span>
        <button class="inc" onClick={set count (count + 1)}>+</button>
      </div>
      <input class="note" value={note} onInput={set note} placeholder="a local note…"/>
      <button class="reset-note" onClick={.resetNote}>Reset note</button>
      <button class="report" onClick={send count}>Report ↑</button>
      <span class="pinned">{if pinned then "pinned" else ""}</span>
      <Tag key={s!"t{id}"} label={s!"{label}: {note}"} onEmit={set pinned}/>
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
  | rename (id : Nat)

def update (m : Model) : Msg → Model
  | .edit s        => { m with draft := s }
  | .add           =>
      let t := m.draft.trimmed
      if t.isEmpty then m
      else { m with rows   := m.rows.push { id := m.nextId, label := t }
                    draft  := ""
                    nextId := m.nextId + 1 }
  | .remove id     => { m with rows := m.rows.filter (·.id != id) }
  | .rename id => { m with rows := m.rows.map fun r =>
      if r.id == id then { r with label := r.label ++ "!" } else r }
  | .reported id c => { m with lastReport := some (id, c) }

/-- Extracting a component tag into an ordinary helper keeps registration automatic. -/
def widgetView (r : Row) : Html Msg :=
  <Widget key={r.id} id={r.id} label={r.label}
    initial={{ note := r.label }} onEmit={Msg.reported r.id}/>

-- The root view goes straight into `ui`: the component tags mount the declared
-- components, and every registration they need (including the `Tag` nested inside
-- `Widget`) is collected automatically.
def app : App Model Msg := ui init update fun m =>
  <div class="app">
    <h1>Local-state rows</h1>
    <div class="add">
      <input class="new" value={m.draft} onInput={.edit} placeholder="New row label"/>
      <button class="addbtn" onClick={.add}>Add row</button>
    </div>
    <div class="report">{match m.lastReport with
      | some (id, c) => s!"last report: row {id} = {c}"
      | none         => "no reports yet"}</div>
    <div class="solo"><Stepper key="s"/></div>
    <ul class="rows">{m.rows.map fun r =>
      -- each row hosts a widget, with live props and an initial note
      -- pre-filled with the label. A Report inside it bubbles up as `Msg.reported r.id`.
      <li key={toString r.id} class="row">
        <span class="label">{r.label}</span>
        {widgetView r}
        <button class="rename" onClick={.rename r.id}>Rename</button>
        <button class="rm" onClick={.remove r.id}>✕</button>
      </li>}</ul>
  </div>

end Local
