import Qed
open Qed

component Hello where
  state name : String := "world"
  view =>
    <div class="hello">
      <input class="who" value={name} onInput={set name} placeholder="Your name"/>
      <h1>{s!"Hello, {name}!"}</h1>
    </div>
