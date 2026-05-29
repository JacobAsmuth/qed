/-
  WASM entry point for the streaming chat demo. Registers the pure `chatApp` with
  the runtime; the JS driver mounts it and dispatches click/input/stream events.
  Compiled to WASM only (it pulls in the DOM externs), never linked natively.
-/
import Examples.Chat
import Qed.Driver

def main : IO Unit := Qed.run Chat.chatApp
