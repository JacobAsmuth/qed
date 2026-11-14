import Qed
open Qed

namespace TemplateDemo

structure Todo where
  id      : Nat
  text    : String
  done    : Bool
  editing : Bool := false
deriving Inhabited

structure Model where
  count  : Nat
  name   : String
  todos  : Array Todo
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
  | startEdit (id : Nat)
  | editText (id : Nat) (s : String)

def update (m : Model) : Msg → Model
  | .inc          => { m with count := m.count + 1 }
  | .dec          => { m with count := m.count - 1 }
  | .setName s    => { m with name := s }
  | .toggle id    => { m with todos := m.todos.map fun t => if t.id == id then { t with done := !t.done } else t }
  | .add          => { m with todos := m.todos.push { id := m.nextId, text := s!"item {m.nextId}", done := false },
                              nextId := m.nextId + 1 }
  | .startEdit id => { m with todos := m.todos.map fun t => { t with editing := t.id == id } }
  | .editText id s => { m with todos := m.todos.map fun t => if t.id == id then { t with text := s } else t }

invariant idsBelowNext (m) : ∀ t ∈ m.todos, t.id < m.nextId
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
  | toggle id | startEdit id | editText id _ =>
      simp only [update, InvTarget.proj_id]
      intro t ht
      obtain ⟨t', ht', rfl⟩ := Array.mem_map.1 ht
      first | exact h t' ht' | (split <;> exact h t' ht')

def banner : Style := css "padding: 7px; border-radius: 4px; &:hover { opacity: 0.9 }"

def app : App Model Msg := ui init update fun m =>
    <div class="demo">
      {styleSheet [banner]}
      <div {banner} id="styled-banner">scoped style</div>
      <h1>View template</h1>
      <div class="counter">
        <button onClick={.dec}>−</button>
        <span class="count">{m.count}</span>
        <button onClick={.inc}>+</button>
      </div>
      {if m.count == 0
        then <p class="hint">click + to start</p>
        else <p class="live">{s!"count is {m.count}"}</p>}
      <input value={m.name} onInput={(Msg.setName ·)}/>
      {if m.name != "" then <p class="greeting">{s!"Hello, {m.name}!"}</p>}
      <button onClick={.add}>add todo</button>
      <ul class="todos">{m.todos.map fun t =>
        <li key={t.id} class={if t.done then "done" else ""} onClick={.toggle t.id}>
          {t.text}</li>}</ul>
      <ul class="structural">{m.todos.map fun t =>
        <li key={t.id}>
          {if t.done then <p class="is-done">done!</p>
                     else <span class="is-open">{t.text}</span>}
        </li>}</ul>
      <ul class="edit">{m.todos.map fun t =>
        <li key={t.id}>
          {if t.editing
            then <input class="editor" value={t.text} onInput={(Msg.editText t.id ·)}/>
            else <span class="label" onClick={.startEdit t.id}>{t.text}</span>}
        </li>}</ul>
      <ul class="keyless">{m.todos.map fun t => <li>{t.text}</li>}</ul>
    </div>

end TemplateDemo
