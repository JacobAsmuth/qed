/-
  Tour 05 · The view vocabulary

  An Elm-Architecture app (pure `init`/`update`) whose view is written inline with `ui`:
  a counter, a conditional, a controlled input, keyed and keyless lists, inline editing,
  and a scoped style. Also the first hand-written invariant proof (`:= by …`), for a
  claim the automation can't guess: row ids stay unique, which is what makes the keyed
  diff sound.

  Pure Lean; the browser entry is `Examples/TemplateWeb.lean`.
-/
import Qed
open Qed

namespace TemplateDemo

structure Todo where
  id   : Nat
  text : String
  done : Bool
  editing : Bool := false
deriving Inhabited

structure Model where
  count : Nat
  name  : String
  todos : Array Todo
  nextId : Nat

def init : Model :=
  { count := 0, name := "", nextId := 3
    todos := #[{ id := 1, text := "learn Lean", done := true },
               { id := 2, text := "write a template", done := false }] }

inductive Msg
  | inc | dec
  | setName (s : String)
  | toggle (id : Nat)
  | add
  | startEdit (id : Nat)            -- enter inline-edit on a row
  | editText (id : Nat) (s : String) -- the row's controlled input fired

def update (m : Model) : Msg → Model
  | .inc        => { m with count := m.count + 1 }
  | .dec        => { m with count := m.count - 1 }
  | .setName s  => { m with name := s }
  | .toggle id  => { m with todos := m.todos.map fun t => if t.id == id then { t with done := !t.done } else t }
  | .add        => { m with todos := m.todos.push { id := m.nextId, text := s!"item {m.nextId}", done := false },
                            nextId := m.nextId + 1 }
  | .startEdit id => { m with todos := m.todos.map fun t => { t with editing := t.id == id } }
  | .editText id s => { m with todos := m.todos.map fun t => if t.id == id then { t with text := s } else t }

-- Every row's id stays below `nextId`, so ids are unique, which is exactly what makes the
-- keyed `diff` sound (no two rows ever share a reconciliation key). The edits that touch the
-- list either `map` over it (preserving each id) or `push` a fresh `nextId` and bump it; the
-- proof below discharges both with the `Array` membership lemmas the automation can't guess.
invariant idsBelowNext : (fun m => ∀ t ∈ m.todos, t.id < m.nextId)
    preserved_by update := by
  intro m msg h
  cases msg with
  | inc => simpa [update] using h
  | dec => simpa [update] using h
  | setName s => simpa [update] using h
  | add =>
      simp only [update, InvTarget.proj_id]
      intro t ht
      rcases Array.mem_push.1 ht with hmem | rfl
      · exact Nat.lt_succ_of_lt (h t hmem)
      · exact Nat.lt_succ_self _
  | toggle id =>
      simp only [update, InvTarget.proj_id]
      intro t ht
      obtain ⟨t', ht', rfl⟩ := Array.mem_map.1 ht
      first | exact h t' ht' | (split <;> exact h t' ht')
  | startEdit id =>
      simp only [update, InvTarget.proj_id]
      intro t ht
      obtain ⟨t', ht', rfl⟩ := Array.mem_map.1 ht
      first | exact h t' ht' | (split <;> exact h t' ht')
  | editText id s =>
      simp only [update, InvTarget.proj_id]
      intro t ht
      obtain ⟨t', ht', rfl⟩ := Array.mem_map.1 ht
      first | exact h t' ht' | (split <;> exact h t' ht')

-- A scoped style, co-located with the view: its class name is a hash (no global collisions),
-- and a typo'd reference (`bnner`) is a compile error.
def banner : Style := css "padding: 7px; border-radius: 4px; &:hover { opacity: 0.9 }"

-- Write the view inline in JSX with ordinary control flow: `if`, `match`, `.map`, string
-- interpolation, dynamic attributes, scope-reading events. `ui` builds the app from it.
def app : App Model Msg := ui init update fun m =>
    <div class="demo">
      {styleSheet [banner]}
      <div {banner} id="styled-banner">scoped style</div>
      <h1>View template</h1>
      {-- a counter: the count is a single bound text node
      <div class="counter">
        <button onClick={.dec}>−</button>
        <span class="count">{s!"{m.count}"}</span>
        <button onClick={.inc}>+</button>
      </div>}
      {-- a conditional that swaps content by the count
      if m.count == 0
        then <p class="hint">click + to start</p>
        else <p class="live">{s!"count is {m.count}"}</p>}
      {-- a controlled input bound to `name`, with a greeting shown once it's non-empty
      <input value={m.name} onInput={(Msg.setName ·)}/>}
      {if m.name != "" then <p class="greeting">{s!"Hello, {m.name}!"}</p> else text ""}
      {-- a keyed list of todos: each row shows its text, toggles `done` on click
      <button onClick={.add}>add todo</button>}
      <ul class="todos">{m.todos.map fun t =>
        <li key={toString t.id} class={if t.done then "done" else ""} onClick={.toggle t.id}>
          {t.text}</li>}</ul>
      {-- a row whose element differs by state (`<p>` when done, `<span>` otherwise)
      <ul class="structural">{m.todos.map fun t =>
        <li key={toString t.id}>
          {if t.done then <p class="is-done">done!</p>
                     else <span class="is-open">{t.text}</span>}
        </li>}</ul>}
      {-- inline editing: an `<input>` while editing, a clickable label otherwise
      <ul class="edit">{m.todos.map fun t =>
        <li key={toString t.id}>
          {if t.editing
            then <input class="editor" value={t.text} onInput={(Msg.editText t.id ·)}/>
            else <span class="label" onClick={.startEdit t.id}>{t.text}</span>}
        </li>}</ul>}
      {-- a plain list (no `key`)
      <ul class="keyless">{m.todos.map fun t => <li>{t.text}</li>}</ul>}
    </div>

end TemplateDemo
