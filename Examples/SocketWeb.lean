/-
  WASM entry point for the WebSocket echo demo. Registers `Socket.app`; the driver
  opens the connection on `Cmd.wsOpen`, sends on `Cmd.wsSend`, and routes inbound
  frames and lifecycle events back to `update`. Compiled to WASM only.
-/
import Examples.Socket
import Qed.Driver

def main : IO Unit := Qed.run Socket.app
