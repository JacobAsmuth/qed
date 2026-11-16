import Qed
open Qed

component Hello where
  state name := "world"
  view =>
    <div class="hello">
      <input class="who" bind={name} placeholder="Your name"/>
      <h1>Hello, {name}!</h1>
    </div>
