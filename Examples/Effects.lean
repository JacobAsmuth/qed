import Qed
open Qed

component Effects where
  state count    : Int := 0
  state title          := ""
  state query          := ""
  state searches : Nat := 0
  state status         := "ready"

  start (Cmd.storageGet "count" .loaded)

  port echoOut : String
  port echoIn (s : String) => status := s!"echo: {s}"

  action inc =>
    let next := count + 1
    count := next
    perform (Cmd.storageSet "count" (toString next))
  action dec =>
    let next := count - 1
    count := next
    perform (Cmd.storageSet "count" (toString next))
  action loaded (v : Option String) =>
    count := (v.bind (·.toInt?)).getD count
  action applyTitle => perform (Cmd.setTitle title)
  action roll       => perform (Cmd.randomInt 1 6 .rolled)
  action rolled (n : Int) => status := s!"rolled: {n}"
  action delayed    => status := "waiting…", perform (Cmd.after 300 .tick)
  action tick       => status := "delayed!"
  action ping       => perform (echoOut "ping")
  action pick       => perform (Cmd.pickFile ".txt,text/*" .picked)
  action picked (r : Except String FilePick) =>
    status := match r with
      | .ok f    => s!"file: {f.name}={f.text}"
      | .error e => s!"file error: {e}"
  action focusTitle => perform (Cmd.focus "title-input")
  action saveBatch  =>
    status := "saved+titled"
    perform (.batch [.storageSet "count" (toString count), .setTitle "Saved!"])
  action typeSearch (s : String) =>
    query := s
    perform (Cmd.afterKeyed "search" 200 (.runSearch s))
  action runSearch (s : String) =>
    status := s!"searched: {s}"
    searches += 1

  view =>
    <div class="app">
      <div class="counter">
        <button class="dec" onClick={.dec}>−</button>
        <span class="count" id="count">{count}</span>
        <button class="inc" onClick={.inc}>+</button>
      </div>
      <input id="title-input" class="title" bind={title} placeholder="page title"/>
      <button class="apply" onClick={.applyTitle}>Set title</button>
      <button class="roll" onClick={.roll}>Roll d6</button>
      <button class="delay" onClick={.delayed}>Delayed</button>
      <button class="ping" onClick={.ping}>Ping</button>
      <button class="pick" onClick={.pick}>Pick file</button>
      <button class="focus" onClick={.focusTitle}>Focus title</button>
      <button class="save" onClick={.saveBatch}>Save (batch)</button>
      <input class="search" value={query} onInput={.typeSearch} placeholder="debounced search"/>
      <span class="searches" id="searches">{searches}</span>
      <div class="status" id="status">{status}</div>
    </div>
