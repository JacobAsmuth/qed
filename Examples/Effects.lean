import Qed
open Qed

namespace Effects

structure Model where
  count    : Int
  title    : String
  query    : String
  searches : Nat
  status   : String

def init : Model := { count := 0, title := "", query := "", searches := 0, status := "ready" }

inductive Msg
  | inc | dec
  | loaded (v : Option String)
  | editTitle (s : String) | applyTitle
  | roll | rolled (n : Int)
  | delayed | tick
  | ping | gotEcho (s : String)
  | pick | picked (r : Except String FilePick)
  | focusTitle
  | saveBatch
  | typeSearch (s : String) | runSearch (s : String)

ports where
  echoOut : String
  echoIn  : String => .gotEcho

def update (m : Model) : Msg → Model
  | .inc          => { m with count := m.count + 1 }
  | .dec          => { m with count := m.count - 1 }
  | .loaded v     => { m with count := (v.bind (·.toInt?)).getD m.count }
  | .editTitle s  => { m with title := s }
  | .rolled n     => { m with status := s!"rolled: {n}" }
  | .delayed      => { m with status := "waiting…" }
  | .tick         => { m with status := "delayed!" }
  | .gotEcho s    => { m with status := s!"echo: {s}" }
  | .picked r     => { m with status := match r with
                                        | .ok f    => s!"file: {f.name}={f.text}"
                                        | .error e => s!"file error: {e}" }
  | .saveBatch    => { m with status := "saved+titled" }
  | .typeSearch s => { m with query := s }
  | .runSearch s  => { m with status := s!"searched: {s}", searches := m.searches + 1 }
  | _             => m

def effects (m : Model) : Msg → Cmd Msg
  | .inc | .dec   => Cmd.storageSet "count" (toString m.count)
  | .applyTitle   => Cmd.setTitle m.title
  | .roll         => Cmd.randomInt 1 6 .rolled
  | .delayed      => Cmd.after 300 .tick
  | .ping         => echoOut "ping"
  | .pick         => Cmd.pickFile ".txt,text/*" .picked
  | .focusTitle   => Cmd.focus "title-input"
  | .saveBatch    => Cmd.batch [Cmd.storageSet "count" (toString m.count), Cmd.setTitle "Saved!"]
  | .typeSearch s => Cmd.afterKeyed "search" 200 (.runSearch s)
  | _             => .none

def transition (m : Model) (msg : Msg) : Model × Cmd Msg :=
  let m' := update m msg; (m', effects m' msg)

def app : App Model Msg :=
  ui init transition (onPort := some onPort) (start := Cmd.storageGet "count" .loaded) fun m =>
    <div class="app">
      <div class="counter">
        <button class="dec" onClick={.dec}>−</button>
        <span class="count" id="count">{m.count}</span>
        <button class="inc" onClick={.inc}>+</button>
      </div>
      <input id="title-input" class="title" value={m.title} onInput={.editTitle} placeholder="page title"/>
      <button class="apply" onClick={.applyTitle}>Set title</button>
      <button class="roll" onClick={.roll}>Roll d6</button>
      <button class="delay" onClick={.delayed}>Delayed</button>
      <button class="ping" onClick={.ping}>Ping</button>
      <button class="pick" onClick={.pick}>Pick file</button>
      <button class="focus" onClick={.focusTitle}>Focus title</button>
      <button class="save" onClick={.saveBatch}>Save (batch)</button>
      <input class="search" value={m.query} onInput={.typeSearch} placeholder="debounced search"/>
      <span class="searches" id="searches">{m.searches}</span>
      <div class="status" id="status">{m.status}</div>
    </div>

end Effects
