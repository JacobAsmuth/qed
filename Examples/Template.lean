import Qed
open Qed

namespace TemplateDemo

structure Todo where
  id      : Nat
  text    : String
  done    : Bool
  editing : Bool := false
deriving Inhabited

def banner : Style := css "padding: 7px; border-radius: 4px; &:hover { opacity: 0.9 }"

end TemplateDemo

component TemplateDemo where
  state count  : Nat := 0
  state name   := ""
  state todos  : Array Todo := #[
    { id := 1, text := "learn Lean", done := true },
    { id := 2, text := "write a template", done := false }]
  state nextId : Nat := 3

  action inc => count += 1
  action dec => count -= 1
  action toggle (id : Nat) =>
    todos := todos.map fun t => if t.id == id then { t with done := !t.done } else t
  action add =>
    todos := todos.push { id := nextId, text := s!"item {nextId}", done := false }
    nextId += 1
  action startEdit (id : Nat) =>
    todos := todos.map fun t => { t with editing := t.id == id }
  action editText (id : Nat) (s : String) =>
    todos := todos.map fun t => if t.id == id then { t with text := s } else t

  invariant idsBelowNext : ∀ t ∈ todos, t.id < nextId := by
    intro m msg h
    cases msg with
    | inc | dec | set_name _ => simpa [update] using h
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

  view =>
    <div class="demo">
      {styleSheet [banner]}
      <div {banner} id="styled-banner">scoped style</div>
      <h1>View template</h1>
      <div class="counter">
        <button onClick={.dec}>−</button>
        <span class="count">{count}</span>
        <button onClick={.inc}>+</button>
      </div>
      {if count == 0
        then <p class="hint">click + to start</p>
        else <p class="live">count is {count}</p>}
      <input bind={name}/>
      {if name != "" then <p class="greeting">Hello, {name}!</p>}
      <button onClick={.add}>add todo</button>
      <ul class="todos">{for t in todos =>
        <li key={t.id} class={if t.done then "done" else ""} onClick={.toggle t.id}>
          {t.text}</li>}</ul>
      <ul class="structural">{for t in todos =>
        <li key={t.id}>
          {if t.done then <p class="is-done">done!</p>
                     else <span class="is-open">{t.text}</span>}
        </li>}</ul>
      <ul class="edit">{for t in todos =>
        <li key={t.id}>
          {if t.editing
            then <input class="editor" value={t.text} onInput={(.editText t.id ·)}/>
            else <span class="label" onClick={.startEdit t.id}>{t.text}</span>}
        </li>}</ul>
      <ul class="keyless">{for t in todos => <li>{t.text}</li>}</ul>
    </div>
