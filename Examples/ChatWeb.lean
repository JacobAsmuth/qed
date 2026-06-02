/-
  Browser entry point for the streaming chat demo. Registers the pure `chatApp` with
  the runtime; the JS driver mounts it and dispatches click/input/stream events.
  transpiled to JavaScript (it uses the DOM externs).
-/
import Examples.Chat
import Qed.Driver

def main : IO Unit := Qed.run Chat.chatApp
