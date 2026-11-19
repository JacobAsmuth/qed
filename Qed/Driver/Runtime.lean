import Qed.Driver.Template
import Qed.Driver.Local
import Qed.Runtime.App

namespace Qed

structure SocketHandlers (msg : Type) where
  onMessage : String → msg
  onOpen    : Option msg
  onClose   : Option msg
  onError   : Option (String → msg)

structure WsMuxHandlers (msg : Type) where
  onJoin    : ByteArray → msg
  onMessage : ByteArray → msg
  onStatus  : SocketStatus → msg

structure WsExtHandlers (msg : Type) where
  onJoin    : Unit → msg
  onText    : String → msg
  onBytes   : ByteArray → msg
  onStatus  : SocketStatus → msg

private structure WsMuxSubEntry (msg : Type) where
  subId        : UInt32
  channel      : String
  params       : ByteArray
  reconnect    : Reconnect
  attempt      : Nat := 0
  pendingRetry : Bool := false
  nextAtMs     : Nat := 0
  handlers     : WsMuxHandlers msg

private structure WsMuxPool (msg : Type) where
  url      : String
  connId   : Option UInt32 := none
  isOpen   : Bool := false
  timerKey : String
  timerId  : Option Nat := none
  subs     : Std.HashMap UInt32 (WsMuxSubEntry msg) := ∅

private structure WsExtConnEntry (msg : Type) where
  subId     : UInt32
  url       : String
  isBinary  : Bool
  reconnect : Reconnect
  attempt   : Nat := 0
  connId    : Option UInt32 := none
  isOpen    : Bool := false
  closed    : Bool := false
  timerKey  : String
  timerId   : Option Nat := none
  handlers  : WsExtHandlers msg

private inductive WsConnOwner where
  | mux (url : String)
  | ext (subId : UInt32)

structure Runtime where
  mount            : IO Unit
  dispatch         : UInt32 → IO Unit
  dispatchStr      : UInt32 → String → IO Unit
  streamChunk      : UInt32 → String → IO Unit
  streamDone       : UInt32 → IO Unit
  httpDone         : UInt32 → Bool → String → IO Unit
  httpBytesDone    : UInt32 → Bool → ByteArray → IO Unit
  urlChanged       : String → IO Unit
  localDispatch    : String → UInt32 → IO Unit
  localDispatchStr : String → UInt32 → String → IO Unit
  snapshot         : IO String
  restore          : String → IO Unit
  effectDone       : UInt32 → String → IO Unit
  portRecv         : String → String → IO Unit
  wsOpen           : UInt32 → IO Unit
  wsBytes          : UInt32 → ByteArray → IO Unit
  wsText           : UInt32 → String → IO Unit
  wsClose          : UInt32 → String → Nat → IO Unit

initialize runtimeRef : IO.Ref (Option Runtime) ← IO.mkRef none

@[export qed_init]
def qedInit : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.mount
  | none    => IO.eprintln "qed: no application registered"

@[export qed_dispatch]
def qedDispatch (id : UInt32) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.dispatch id
  | none    => pure ()

@[export qed_dispatch_str]
def qedDispatchStr (id : UInt32) (s : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.dispatchStr id s
  | none    => pure ()

@[export qed_stream_chunk]
def qedStreamChunk (cid : UInt32) (chunk : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.streamChunk cid chunk
  | none    => pure ()

@[export qed_stream_done]
def qedStreamDone (did : UInt32) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.streamDone did
  | none    => pure ()

@[export qed_http_done]
def qedHttpDone (id : UInt32) (ok : UInt32) (text : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.httpDone id (ok != 0) text
  | none    => pure ()

@[export qed_http_bytes_done]
def qedHttpBytesDone (id : UInt32) (ok : UInt32) (bytes : ByteArray) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.httpBytesDone id (ok != 0) bytes
  | none    => pure ()

@[export qed_url_changed]
def qedUrlChanged (path : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.urlChanged path
  | none    => pure ()

@[export qed_local_dispatch]
def qedLocalDispatch (key : String) (id : UInt32) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.localDispatch key id
  | none    => pure ()

@[export qed_local_dispatch_str]
def qedLocalDispatchStr (key : String) (id : UInt32) (s : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.localDispatchStr key id s
  | none    => pure ()

@[export qed_local_snapshot]
def qedLocalSnapshot : IO String := do
  match ← runtimeRef.get with
  | some rt => rt.snapshot
  | none    => return "{}"

@[export qed_local_restore]
def qedLocalRestore (s : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.restore s
  | none    => pure ()

@[export qed_effect_done]
def qedEffectDone (id : UInt32) (result : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.effectDone id result
  | none    => pure ()

@[export qed_port_recv]
def qedPortRecv (name payload : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.portRecv name payload
  | none    => pure ()

@[export qed_ws_open]
def qedWsOpen (connId : UInt32) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.wsOpen connId
  | none    => pure ()

@[export qed_ws_bytes]
def qedWsBytes (connId : UInt32) (bytes : ByteArray) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.wsBytes connId bytes
  | none    => pure ()

@[export qed_ws_text]
def qedWsText (connId : UInt32) (text : String) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.wsText connId text
  | none    => pure ()

@[export qed_ws_close]
def qedWsClose (connId : UInt32) (err : String) (nowMs : Nat) : IO Unit := do
  match ← runtimeRef.get with
  | some rt => rt.wsClose connId err nowMs
  | none    => pure ()

private def trimAsciiWs (s : String) : String :=
  String.ofList (((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse)

/-- Parses complete `\n`-terminated SSE `data:` lines out of `buf`, returning `(events, remainder)`. -/
private def parseSseBuffer (buf : String) : Array String × String :=
  let rec go (acc : Array String) : List String → Array String × String
    | []      => (acc, "")
    | [rem]   => (acc, rem)
    | l :: ls =>
        let t := trimAsciiWs l
        let acc' :=
          if t.startsWith "data:" then
            let p := trimAsciiWs (String.ofList (t.toList.drop 5))
            if !p.isEmpty && p != "[DONE]" then acc.push p else acc
          else acc
        go acc' ls
  go #[] (buf.splitOn "\n")

private def wsClosedStatus : Reconnect → SocketStatus
  | .off => .disconnected
  | _    => .failed "disconnected"

private def drainPendingQueue {Msg : Type} (pendingRef : IO.Ref (Array Msg))
    (step : Msg → IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | fuel + 1 => do
      let queued ← pendingRef.get
      if queued.isEmpty then
        pure ()
      else
        pendingRef.set #[]
        for qm in queued do step qm
        drainPendingQueue pendingRef step fuel

def run (app : App Model Msg) : IO Unit := do
  let template  := app.template
  let modelRef  ← IO.mkRef app.init.1
  let vstateRef ← IO.mkRef (none : Option (VState Model Msg))
  let rootRef   ← IO.mkRef (0 : Dom.Node)
  let clickRef  ← IO.mkRef (#[] : Array Msg)
  let inputRef  ← IO.mkRef (#[] : Array (String → Msg))
  let chunkCbRef  ← IO.mkRef (#[] : Array (String → Msg))
  let streamBufRef ← IO.mkRef (∅ : Std.HashMap Nat String)
  let doneCbRef   ← IO.mkRef (#[] : Array (Nat × Msg))
  let respCbRef      ← IO.mkRef (∅ : Std.HashMap Nat (Except String String → Msg))
  let respBytesCbRef ← IO.mkRef (∅ : Std.HashMap Nat (Except String ByteArray → Msg))
  let effectCbRef    ← IO.mkRef (∅ : Std.HashMap Nat (String → Msg))
  let wsTimerCbRef   ← IO.mkRef (∅ : Std.HashMap Nat (IO Unit))
  let cbNextRef   ← IO.mkRef (0 : Nat)
  let socketCbRef ← IO.mkRef (∅ : Std.HashMap String (SocketHandlers Msg))
  let wsNextIdRef    ← IO.mkRef (1 : UInt32)
  let wsBootedRef    ← IO.mkRef false
  let wsConnOwnerRef ← IO.mkRef (∅ : Std.HashMap UInt32 WsConnOwner)
  let wsMuxSlotRef   ← IO.mkRef (∅ : Std.HashMap String UInt32)
  let wsMuxSubUrlRef ← IO.mkRef (∅ : Std.HashMap UInt32 String)
  let wsMuxPoolsRef  ← IO.mkRef (∅ : Std.HashMap String (WsMuxPool Msg))
  let wsExtSlotRef   ← IO.mkRef (∅ : Std.HashMap String UInt32)
  let wsExtEntriesRef ← IO.mkRef (∅ : Std.HashMap UInt32 (WsExtConnEntry Msg))
  let nextWsId : IO UInt32 := do
    let n ← wsNextIdRef.get
    let nxt := if n + 1 == 0 then 1 else n + 1
    wsNextIdRef.set nxt
    return n
  let cancelWsTimer (key : String) (tid? : Option Nat) : IO Unit := do
    if let some tid := tid? then wsTimerCbRef.modify (·.erase tid)
    Dom.effect "timer.cancel" key "" ""
  let scheduleWsTimer (key : String) (oldTid? : Option Nat) (delayMs : Nat) (act : IO Unit) : IO Nat := do
    if let some oldTid := oldTid? then wsTimerCbRef.modify (·.erase oldTid)
    let tid ← cbNextRef.modifyGet (fun n => (n, n + 1))
    wsTimerCbRef.modify (·.insert tid act)
    Dom.effectResult "timer.afterKeyed" key (toString delayMs) (UInt32.ofNat tid)
    return tid
  let ensureMuxConn (url : String) : IO Unit := do
    let some pool := (← wsMuxPoolsRef.get)[url]? | return
    if pool.subs.isEmpty || pool.connId.isSome then return
    cancelWsTimer pool.timerKey pool.timerId
    let cid ← nextWsId
    wsMuxPoolsRef.modify (·.insert url { pool with connId := some cid, isOpen := false, timerId := none })
    wsConnOwnerRef.modify (·.insert cid (.mux url))
    Dom.wsOpen cid url true
  let openExtConn (subId : UInt32) : IO Unit := do
    let some entry := (← wsExtEntriesRef.get)[subId]? | return
    if entry.closed || entry.connId.isSome then return
    cancelWsTimer entry.timerKey entry.timerId
    let cid ← nextWsId
    wsExtEntriesRef.modify (·.insert subId { entry with connId := some cid, isOpen := false, timerId := none })
    wsConnOwnerRef.modify (·.insert cid (.ext subId))
    Dom.wsOpen cid entry.url entry.isBinary
  let closeMuxSlot (slot : String) : IO Unit := do
    let some sid := (← wsMuxSlotRef.get)[slot]? | return
    wsMuxSlotRef.modify (·.erase slot)
    let some url := (← wsMuxSubUrlRef.get)[sid]? | return
    wsMuxSubUrlRef.modify (·.erase sid)
    let some pool := (← wsMuxPoolsRef.get)[url]? | return
    let subs' := pool.subs.erase sid
    if pool.isOpen then
      if let some cid := pool.connId then
        Dom.wsSendBytes cid (WsMuxFrame.encode (.unsub sid))
    if subs'.isEmpty then
      cancelWsTimer pool.timerKey pool.timerId
      wsMuxPoolsRef.modify (·.erase url)
      if let some cid := pool.connId then
        wsConnOwnerRef.modify (·.erase cid)
        Dom.wsClose cid
    else
      wsMuxPoolsRef.modify (·.insert url { pool with subs := subs' })
  let closeExtSlot (slot : String) : IO Unit := do
    let some sid := (← wsExtSlotRef.get)[slot]? | return
    wsExtSlotRef.modify (·.erase slot)
    let some entry := (← wsExtEntriesRef.get)[sid]? | return
    wsExtEntriesRef.modify (·.erase sid)
    cancelWsTimer entry.timerKey entry.timerId
    if let some cid := entry.connId then
      wsConnOwnerRef.modify (·.erase cid)
      Dom.wsClose cid
  let dispatchRef ← IO.mkRef (fun (_ : Msg) => (pure () : IO Unit))
  let registry : Std.HashMap String LocalDef :=
    app.locals.foldl (fun m d => m.insert d.id d) ∅
  let storeRef     ← IO.mkRef (∅ : Std.HashMap String String)
  let instancesRef ← IO.mkRef (∅ : Std.HashMap String LocalInstance)
  let ctx : LocalCtx := { registry, store := storeRef, instances := instancesRef }
  let h : Handlers Msg :=
    { click := clickRef, input := inputRef,
      mountLocal := fun k c i p b hn => localMountRoot ctx (fun m => do (← dispatchRef.get) m) k c i p b hn }
  let gcLocals : IO Unit := do
    let mut dead : Array String := #[]
    for (k, inst) in (← instancesRef.get).toList do
      unless (← Dom.isConnected inst.host) do dead := dead.push k
    for k in dead do
      instancesRef.modify (·.erase k); storeRef.modify (·.erase k)
  let renderModel : IO Unit := do
    match ← vstateRef.get with
    | none => do
        let existing ← Dom.appRoot
        if existing != (0 : Dom.Node) then
          let vst ← hydrateView h template (← modelRef.get) existing
          rootRef.set existing; vstateRef.set (some vst)
        else
          let (node, vst) ← buildView h "" template (← modelRef.get)
          Dom.mountRoot node; rootRef.set node; vstateRef.set (some vst)
    | some vst => do
        let vst' ← patchView h (← rootRef.get) 0 template (← modelRef.get) vst
        vstateRef.set (some vst')
    gcLocals
  let performLeaf : Cmd Msg → IO Unit := fun
    | .none => pure ()
    | .stream url body onChunk onDone => do
        let cs ← chunkCbRef.get; chunkCbRef.set (cs.push onChunk)
        let ds ← doneCbRef.get;  doneCbRef.set (ds.push (cs.size, onDone))
        Dom.fetchStream url body (UInt32.ofNat cs.size) (UInt32.ofNat ds.size)
    | .now onNow => do
        match Qed.Date.parse? (← Dom.today) with
        | some d => (← dispatchRef.get) (onNow d)
        | none   => pure ()
    | .request method url body onResult => do
        let id ← cbNextRef.modifyGet (fun n => (n, n + 1))
        respCbRef.modify (·.insert id onResult)
        Dom.httpSend method url body (UInt32.ofNat id)
    | .requestBytes method url body onResult => do
        let id ← cbNextRef.modifyGet (fun n => (n, n + 1))
        respBytesCbRef.modify (·.insert id onResult)
        Dom.httpSendBytes method url body (UInt32.ofNat id)
    | .pushPath url => do
        Dom.pushPath url.raw
        match app.onUrlChange with
        | some f => (← dispatchRef.get) (f url.raw)
        | none   => pure ()
    | .port name payload => Dom.portSend name payload
    | .socket key url onMessage onOpen onClose onError => do
        socketCbRef.modify (·.insert key { onMessage, onOpen, onClose, onError })
        Dom.effect "ws.open" key url ""
    | .wsMuxSub slot url channel params rec onJoin onMessage onStatus => do
        if !(← wsBootedRef.get) then return
        closeMuxSlot slot
        let sid ← nextWsId
        wsMuxSlotRef.modify (·.insert slot sid)
        wsMuxSubUrlRef.modify (·.insert sid url)
        let pool := match (← wsMuxPoolsRef.get)[url]? with
          | some p => p
          | none   => { url, timerKey := "ws-mux:" ++ url }
        let sub : WsMuxSubEntry Msg := {
          subId := sid, channel, params, reconnect := rec, handlers := { onJoin, onMessage, onStatus }
        }
        wsMuxPoolsRef.modify (·.insert url { pool with subs := pool.subs.insert sid sub })
        (← dispatchRef.get) (onStatus .connecting)
        if let some pool' := (← wsMuxPoolsRef.get)[url]? then
          if pool'.subs.contains sid then
            if pool'.isOpen then
              if let some cid := pool'.connId then
                Dom.wsSendBytes cid (WsMuxFrame.encode (.sub sid channel params))
            else if pool'.connId.isNone then
              ensureMuxConn url
    | .wsMuxSend slot payload => do
        let some sid := (← wsMuxSlotRef.get)[slot]? | return
        let some url := (← wsMuxSubUrlRef.get)[sid]? | return
        let some pool := (← wsMuxPoolsRef.get)[url]? | return
        if pool.isOpen then
          if let some cid := pool.connId then
            Dom.wsSendBytes cid (WsMuxFrame.encode (.send sid payload))
    | .wsMuxUnsub slot => do
        if (← wsBootedRef.get) then closeMuxSlot slot
    | .wsExtOpen slot url isBinary rec onJoin onText onBytes onStatus => do
        if !(← wsBootedRef.get) then return
        closeExtSlot slot
        let sid ← nextWsId
        wsExtSlotRef.modify (·.insert slot sid)
        let entry : WsExtConnEntry Msg := {
          subId := sid, url, isBinary, reconnect := rec, timerKey := s!"ws-ext:{sid}",
          handlers := { onJoin, onText, onBytes, onStatus }
        }
        wsExtEntriesRef.modify (·.insert sid entry)
        (← dispatchRef.get) (onStatus .connecting)
        openExtConn sid
    | .wsExtSendText slot text => do
        let some sid := (← wsExtSlotRef.get)[slot]? | return
        let some entry := (← wsExtEntriesRef.get)[sid]? | return
        if entry.isOpen then
          if let some cid := entry.connId then Dom.wsSendText cid text
    | .wsExtSendBytes slot payload => do
        let some sid := (← wsExtSlotRef.get)[slot]? | return
        let some entry := (← wsExtEntriesRef.get)[sid]? | return
        if entry.isOpen then
          if let some cid := entry.connId then Dom.wsSendBytes cid payload
    | .wsExtClose slot => do
        if (← wsBootedRef.get) then closeExtSlot slot
    | .fx kind a b c => Dom.effect kind a b c
    | .fxResult kind a b onResult => do
        let id ← cbNextRef.modifyGet (fun n => (n, n + 1))
        effectCbRef.modify (·.insert id onResult)
        Dom.effectResult kind a b (UInt32.ofNat id)
    | .batch _ => pure ()
  let perform : Cmd Msg → IO Unit := fun cmd => (Cmd.flatten cmd).forM performLeaf
  -- Removing a focused node during patch fires `blur` synchronously; queue re-entrant dispatches until the render finishes.
  let renderingRef ← IO.mkRef false
  let pendingRef   ← IO.mkRef (#[] : Array Msg)
  let applyOne : Msg → IO (Cmd Msg) := fun msg => do
    let (m', cmd) := app.update (← modelRef.get) msg
    modelRef.set m'
    renderingRef.set true
    try renderModel finally renderingRef.set false
    pure cmd
  let dispatchMsg : Msg → IO Unit := fun msg => do
    if (← renderingRef.get) then
      pendingRef.modify (·.push msg)
    else
      perform (← applyOne msg)
      drainPendingQueue pendingRef (fun qm => do perform (← applyOne qm)) 1024
  dispatchRef.set dispatchMsg
  let localDispatch : String → UInt32 → IO Unit := fun fullKey id => do
    match (← instancesRef.get)[fullKey]? with
    | some inst => match (← inst.handlers.click.get)[id.toNat]? with
                   | some lm => localRun ctx fullKey inst lm
                   | none    => pure ()
    | none      => pure ()
  let localDispatchStr : String → UInt32 → String → IO Unit := fun fullKey id s => do
    match (← instancesRef.get)[fullKey]? with
    | some inst => match (← inst.handlers.input.get)[id.toNat]? with
                   | some f => localRun ctx fullKey inst (f s)
                   | none   => pure ()
    | none      => pure ()
  let effectDone : UInt32 → String → IO Unit := fun id result => do
    match (← wsTimerCbRef.get)[id.toNat]? with
    | some act => wsTimerCbRef.modify (·.erase id.toNat); act
    | none =>
        match (← effectCbRef.get)[id.toNat]? with
        | some onResult => effectCbRef.modify (·.erase id.toNat); dispatchMsg (onResult result)
        | none          => pure ()
  let portRecv : String → String → IO Unit := fun name payload => do
    if name == "__ws" then
      match Json.parse payload with
      | .ok j =>
          let str (k : String) : String := ((j.get? k).bind (·.str?)).getD ""
          let key := str "key"
          match (← socketCbRef.get)[key]? with
          | some h =>
              match str "event" with
              | "message" => dispatchMsg (h.onMessage (str "data"))
              | "open"    => match h.onOpen with | some m => dispatchMsg m | none => pure ()
              | "error"   => match h.onError with | some f => dispatchMsg (f (str "data")) | none => pure ()
              | "close"   =>
                  socketCbRef.modify (·.erase key)
                  match h.onClose with | some m => dispatchMsg m | none => pure ()
              | _         => pure ()
          | none => pure ()
      | .error _ => pure ()
    else match app.onPort with
      | some f => match f name payload with | some m => dispatchMsg m | none => pure ()
      | none   => pure ()
  let snapshotLocals : IO String := do
    let members := (← storeRef.get).toList.map (fun (k, v) => (k, Json.str v))
    return Json.render (Json.obj members)
  let restoreLocals : String → IO Unit := fun s => do
    match Json.parse s with
    | .ok (.obj members) => do
        for (k, v) in members do
          match v with | .str st => storeRef.modify (·.insert k st) | _ => pure ()
        for (k, _) in (← instancesRef.get).toList do
          if let some inst := (← instancesRef.get)[k]? then
            localRerender inst ((← storeRef.get).getD k "")
    | _ => pure ()
  runtimeRef.set (some {
    mount := do
      if !app.styles.isEmpty then Dom.effect "css.inject" (renderStyleSheet app.styles) "" ""
      let st ← Dom.appState
      match (if st.isEmpty then none else app.rehydrate st) with
      | some m =>
          modelRef.set m
          renderModel
          wsBootedRef.set true
          perform (.batch [app.init.2.clientOnly, app.onHydrate m])
      | none =>
          match app.onUrlChange with
          | some f => do let p ← Dom.currentPath; dispatchMsg (f p)
          | none   => renderModel
          perform app.init.2
          wsBootedRef.set true
          perform (app.onHydrate (← modelRef.get))
    dispatch := fun id => do
      match (← clickRef.get)[id.toNat]? with
      | some msg => dispatchMsg msg
      | none     => IO.eprintln s!"qed: unknown click id {id}"
    dispatchStr := fun id s => do
      match (← inputRef.get)[id.toNat]? with
      | some f => dispatchMsg (f s)
      | none   => pure ()
    streamChunk := fun cid rawChunk => do
      let prev := (← streamBufRef.get).getD cid.toNat ""
      let (events, rem) := parseSseBuffer (prev ++ rawChunk)
      streamBufRef.modify (·.insert cid.toNat rem)
      if let some f := (← chunkCbRef.get)[cid.toNat]? then
        for ev in events do dispatchMsg (f ev)
    streamDone := fun did => do
      match (← doneCbRef.get)[did.toNat]? with
      | some (cid, msg) =>
          streamBufRef.modify (·.erase cid)
          dispatchMsg msg
      | none => pure ()
    httpDone := fun id ok text => do
      match (← respCbRef.get)[id.toNat]? with
      | some f => respCbRef.modify (·.erase id.toNat); dispatchMsg (f (if ok then .ok text else .error text))
      | none   => pure ()
    httpBytesDone := fun id ok bytes => do
      match (← respBytesCbRef.get)[id.toNat]? with
      | some f =>
          respBytesCbRef.modify (·.erase id.toNat)
          if ok then
            dispatchMsg (f (.ok bytes))
          else
            let msg := (String.fromUTF8? bytes).getD "RPC transport error"
            dispatchMsg (f (.error msg))
      | none => pure ()
    urlChanged := fun path => do
      match app.onUrlChange with
      | some f => dispatchMsg (f path)
      | none   => pure ()
    localDispatch
    localDispatchStr
    snapshot := snapshotLocals
    restore  := restoreLocals
    effectDone
    portRecv
    wsOpen := fun cid => do
      match (← wsConnOwnerRef.get)[cid]? with
      | some (.mux url) =>
          let some pool := (← wsMuxPoolsRef.get)[url]? | return
          if pool.connId != some cid then return
          let resetSubs := pool.subs.fold (init := (∅ : Std.HashMap UInt32 (WsMuxSubEntry Msg)))
            fun acc sid sub => acc.insert sid { sub with attempt := 0, pendingRetry := false, nextAtMs := 0 }
          wsMuxPoolsRef.modify (·.insert url { pool with isOpen := true, subs := resetSubs })
          for (_, sub) in resetSubs.toList do
            Dom.wsSendBytes cid (WsMuxFrame.encode (.sub sub.subId sub.channel sub.params))
      | some (.ext subId) =>
          let some entry := (← wsExtEntriesRef.get)[subId]? | return
          if entry.closed || entry.connId != some cid then return
          wsExtEntriesRef.modify (·.insert subId { entry with attempt := 0, isOpen := true })
          dispatchMsg (entry.handlers.onStatus .connected)
          dispatchMsg (entry.handlers.onJoin ())
      | none => pure ()
    wsBytes := fun cid bytes => do
      match (← wsConnOwnerRef.get)[cid]? with
      | some (.mux url) =>
          let some pool := (← wsMuxPoolsRef.get)[url]? | return
          if pool.connId != some cid then return
          match WsMuxFrame.decode bytes with
          | .ok (.joinOk sid snap) =>
              let some sub := pool.subs[sid]? | return
              let sub' := { sub with attempt := 0, pendingRetry := false, nextAtMs := 0 }
              wsMuxPoolsRef.modify (·.insert url { pool with subs := pool.subs.insert sid sub' })
              dispatchMsg (sub.handlers.onStatus .connected)
              dispatchMsg (sub.handlers.onJoin snap)
          | .ok (.event sid payload) =>
              if let some sub := pool.subs[sid]? then
                dispatchMsg (sub.handlers.onMessage payload)
          | .ok (.err sid msg) =>
              let some sub := pool.subs[sid]? | return
              wsMuxSubUrlRef.modify (·.erase sid)
              wsMuxPoolsRef.modify (·.insert url { pool with subs := pool.subs.erase sid })
              dispatchMsg (sub.handlers.onStatus (.failed msg))
          | .ok (.closed sid _) =>
              let some sub := pool.subs[sid]? | return
              wsMuxSubUrlRef.modify (·.erase sid)
              wsMuxPoolsRef.modify (·.insert url { pool with subs := pool.subs.erase sid })
              dispatchMsg (sub.handlers.onStatus .disconnected)
          | _ => pure ()
      | some (.ext subId) =>
          let some entry := (← wsExtEntriesRef.get)[subId]? | return
          if entry.closed || entry.connId != some cid then return
          dispatchMsg (entry.handlers.onBytes bytes)
      | none => pure ()
    wsText := fun cid text => do
      match (← wsConnOwnerRef.get)[cid]? with
      | some (.ext subId) =>
          let some entry := (← wsExtEntriesRef.get)[subId]? | return
          if entry.closed || entry.connId != some cid then return
          dispatchMsg (entry.handlers.onText text)
      | _ => pure ()
    wsClose := fun cid err nowMs => do
      let owner? := (← wsConnOwnerRef.get)[cid]?
      wsConnOwnerRef.modify (·.erase cid)
      match owner? with
      | some (.mux url) =>
          let some pool := (← wsMuxPoolsRef.get)[url]? | return
          if pool.connId != some cid then return
          if !err.isEmpty then
            cancelWsTimer pool.timerKey pool.timerId
            wsMuxPoolsRef.modify (·.erase url)
            for (sid, _) in pool.subs.toList do wsMuxSubUrlRef.modify (·.erase sid)
            for (_, sub) in pool.subs.toList do dispatchMsg (sub.handlers.onStatus (.failed err))
            return
          if pool.subs.isEmpty then
            cancelWsTimer pool.timerKey pool.timerId
            wsMuxPoolsRef.modify (·.erase url)
            return
          let mut keptSubs : Std.HashMap UInt32 (WsMuxSubEntry Msg) := ∅
          let mut statusMsgs : Array Msg := #[]
          let mut minDelay? : Option Nat := none
          for (sid, sub) in pool.subs.toList do
            if sub.pendingRetry && nowMs < sub.nextAtMs then
              let rem := sub.nextAtMs - nowMs
              keptSubs := keptSubs.insert sid sub
              minDelay? := some (match minDelay? with | some m => min m rem | none => rem)
            else
              match sub.reconnect.nextDelayMs sub.attempt with
              | none =>
                  wsMuxSubUrlRef.modify (·.erase sid)
                  statusMsgs := statusMsgs.push (sub.handlers.onStatus (wsClosedStatus sub.reconnect))
              | some d =>
                  let sub' := { sub with attempt := sub.attempt + 1, pendingRetry := true, nextAtMs := nowMs + d }
                  keptSubs := keptSubs.insert sid sub'
                  minDelay? := some (match minDelay? with | some m => min m d | none => d)
                  statusMsgs := statusMsgs.push (sub.handlers.onStatus (.reconnecting sub'.attempt))
          if keptSubs.isEmpty then
            cancelWsTimer pool.timerKey pool.timerId
            wsMuxPoolsRef.modify (·.erase url)
          else
            let delayMs := minDelay?.getD 0
            let tid ← scheduleWsTimer pool.timerKey pool.timerId delayMs (ensureMuxConn url)
            wsMuxPoolsRef.modify (·.insert url { pool with connId := none, isOpen := false, timerId := some tid, subs := keptSubs })
          for m in statusMsgs do dispatchMsg m
      | some (.ext subId) =>
          let some entry := (← wsExtEntriesRef.get)[subId]? | return
          if entry.closed || entry.connId != some cid then return
          if !err.isEmpty then
            cancelWsTimer entry.timerKey entry.timerId
            wsExtEntriesRef.modify (·.erase subId)
            dispatchMsg (entry.handlers.onStatus (.failed err))
            return
          match entry.reconnect.nextDelayMs entry.attempt with
          | none =>
              cancelWsTimer entry.timerKey entry.timerId
              wsExtEntriesRef.modify (·.erase subId)
              dispatchMsg (entry.handlers.onStatus (wsClosedStatus entry.reconnect))
          | some d =>
              let attempt' := entry.attempt + 1
              let tid ← scheduleWsTimer entry.timerKey entry.timerId d (openExtConn subId)
              wsExtEntriesRef.modify (·.insert subId { entry with attempt := attempt', connId := none, isOpen := false, timerId := some tid })
              dispatchMsg (entry.handlers.onStatus (.reconnecting attempt'))
      | none => pure ()
  })

end Qed
