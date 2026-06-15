/-
  Tour 00 · Hello, world

  The smallest Qed app: one `component` declaration is the whole program. `state`
  declares the data, the view is JSX, and `set` is the only way to change anything.
  The framework generates the message type and the pure transition behind it
  (Tour 01, the counter, shows that architecture written out), and because every
  field has a default the declaration also yields `Hello.app`: the component run
  as the whole application. The browser entry (`Examples/HelloWeb.lean`) is one
  line: `Qed.run Hello.app`.
-/
import Qed
open Qed

component Hello where
  state name : String := "world"
  view =>
    <div class="hello">
      <input class="who" value={name} onInput={set name} placeholder="Your name"/>
      <h1>{s!"Hello, {name}!"}</h1>
    </div>
