namespace Qed.Cli.Watch

/-! ## OS-Native File Watcher & Dev-Event SSE Push Server (`Cli.Watch`)
    Backed by zero-dependency Rust FFI (`rust/qed_server/src/watch.rs`) using
    `inotify` on Linux and `kqueue` on macOS, plus a lightweight localhost SSE
    broadcaster so `qed dev` pushes build/reload events directly to browsers. -/

def changeLean    : UInt32 := 1
def changeCss     : UInt32 := 2
def changeRuntime : UInt32 := 4
def changeError   : UInt32 := 8

@[extern "qed_watch_open"]
opaque openRaw (projectDir : @& String) (runtimeDir : @& String) (skipDirs : @& Array String) :
    IO (Except String UInt64)

@[extern "qed_watch_wait"]
opaque waitRaw (handle : UInt64) (timeoutMs : UInt32) : IO UInt32

@[extern "qed_watch_close"]
opaque closeRaw (handle : UInt64) : IO Unit

@[extern "qed_dev_sse_start"]
opaque sseStartRaw (port : UInt16) : IO (Except String (UInt64 × UInt16))

@[extern "qed_dev_sse_publish"]
opaque ssePublishRaw (handle : UInt64) (jsonPayload : @& String) : IO Unit

@[extern "qed_dev_sse_stop"]
opaque sseStopRaw (handle : UInt64) : IO Unit

structure FileWatcher where
  handle : UInt64

structure WatchEvents where
  lean    : Bool
  css     : Bool
  runtime : Bool
  error   : Bool
  deriving Repr, BEq

def WatchEvents.any (ev : WatchEvents) : Bool :=
  ev.lean || ev.css || ev.runtime

def FileWatcher.open (projectDir : String) (runtimeDir : String := "")
    (skipDirs : Array String := #[]) : IO (Except String FileWatcher) :=
  (·.map fun handle => { handle }) <$> openRaw projectDir runtimeDir skipDirs

def FileWatcher.wait (w : FileWatcher) (timeoutMs : UInt32 := 1000) : IO WatchEvents := do
  let mask ← waitRaw w.handle timeoutMs
  return {
    lean    := (mask &&& changeLean) != 0
    css     := (mask &&& changeCss) != 0
    runtime := (mask &&& changeRuntime) != 0
    error   := (mask &&& changeError) != 0
  }

def FileWatcher.close (w : FileWatcher) : IO Unit :=
  closeRaw w.handle

structure DevSseServer where
  handle : UInt64
  port   : UInt16

def DevSseServer.url (s : DevSseServer) : String :=
  s!"http://127.0.0.1:{s.port}/events"

def DevSseServer.start (port : UInt16 := 0) : IO (Except String DevSseServer) :=
  (·.map fun (handle, port) => { handle, port }) <$> sseStartRaw port

def DevSseServer.publish (s : DevSseServer) (jsonPayload : String) : IO Unit :=
  ssePublishRaw s.handle jsonPayload

def DevSseServer.stop (s : DevSseServer) : IO Unit :=
  sseStopRaw s.handle

end Qed.Cli.Watch
