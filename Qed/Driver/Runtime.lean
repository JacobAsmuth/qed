import Qed.Driver.Template
import Qed.Driver.Local
import Qed.Runtime.AppCore

namespace Qed

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
  dehydrate        : IO String
  effectDone       : UInt32 → String → IO Unit
  portRecv         : String → String → IO Unit
  wsOpen           : UInt32 → IO Unit
  wsBytes          : UInt32 → ByteArray → IO Unit
  wsText           : UInt32 → String → IO Unit
  wsClose          : UInt32 → String → Nat → IO Unit

initialize runtimeRef : IO.Ref (Option Runtime) ← IO.mkRef none

@[inline] private def withRuntime (fallback : IO α) (f : Runtime → IO α) : IO α := do
  match ← runtimeRef.get with | some rt => f rt | none => fallback

@[inline] private def withRuntimeUnit (f : Runtime → IO Unit) : IO Unit :=
  withRuntime (pure ()) f

@[export qed_init] def qedInit : IO Unit := withRuntime (IO.eprintln "qed: no application registered") (·.mount)
@[export qed_dispatch] def qedDispatch (id : UInt32) : IO Unit := withRuntimeUnit (·.dispatch id)
@[export qed_dispatch_str] def qedDispatchStr (id : UInt32) (s : String) : IO Unit := withRuntimeUnit (·.dispatchStr id s)
@[export qed_stream_chunk] def qedStreamChunk (cid : UInt32) (chunk : String) : IO Unit := withRuntimeUnit (·.streamChunk cid chunk)
@[export qed_stream_done] def qedStreamDone (did : UInt32) : IO Unit := withRuntimeUnit (·.streamDone did)
@[export qed_http_done] def qedHttpDone (id ok : UInt32) (text : String) : IO Unit := withRuntimeUnit (·.httpDone id (ok != 0) text)
@[export qed_http_bytes_done] def qedHttpBytesDone (id ok : UInt32) (bytes : ByteArray) : IO Unit := withRuntimeUnit (·.httpBytesDone id (ok != 0) bytes)
@[export qed_url_changed] def qedUrlChanged (path : String) : IO Unit := withRuntimeUnit (·.urlChanged path)
@[export qed_local_dispatch] def qedLocalDispatch (key : String) (id : UInt32) : IO Unit := withRuntimeUnit (·.localDispatch key id)
@[export qed_local_dispatch_str] def qedLocalDispatchStr (key : String) (id : UInt32) (s : String) : IO Unit := withRuntimeUnit (·.localDispatchStr key id s)
@[export qed_local_snapshot] def qedLocalSnapshot : IO String := withRuntime (pure "{}") (·.snapshot)
@[export qed_local_restore] def qedLocalRestore (s : String) : IO Unit := withRuntimeUnit (·.restore s)
@[export qed_dehydrate] def qedDehydrate : IO String := withRuntime (pure "") (·.dehydrate)
@[export qed_effect_done] def qedEffectDone (id : UInt32) (result : String) : IO Unit := withRuntimeUnit (·.effectDone id result)
@[export qed_port_recv] def qedPortRecv (name payload : String) : IO Unit := withRuntimeUnit (·.portRecv name payload)
@[export qed_ws_open] def qedWsOpen (connId : UInt32) : IO Unit := withRuntimeUnit (·.wsOpen connId)
@[export qed_ws_bytes] def qedWsBytes (connId : UInt32) (bytes : ByteArray) : IO Unit := withRuntimeUnit (·.wsBytes connId bytes)
@[export qed_ws_text] def qedWsText (connId : UInt32) (text : String) : IO Unit := withRuntimeUnit (·.wsText connId text)
@[export qed_ws_close] def qedWsClose (connId : UInt32) (err : String) (nowMs : Nat) : IO Unit := withRuntimeUnit (·.wsClose connId err nowMs)

/-- Parses complete `\n`-terminated SSE `data:` lines out of `buf`, returning `(events, remainder)`. -/
private def parseSseBuffer (buf : String) : Array String × String :=
  let rec go (acc : Array String) : List String → Array String × String
    | []      => (acc, "")
    | [rem]   => (acc, rem)
    | l :: ls =>
        let t := l.trimmed
        let acc' :=
          if t.startsWith "data:" then
            let p := (String.ofList (t.toList.drop 5)).trimmed
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

def defaultHttpTimeoutMs : Nat := 30000

private def httpTimerKey (id : Nat) : String :=
  s!"http:{id}"

private structure RuntimeEnv (Model Msg : Type) where
  app             : App Model Msg
  httpTimeoutMs   : Nat
  modelRef        : IO.Ref Model
  vstateRef       : IO.Ref (Option (VState Model Msg))
  rootRef         : IO.Ref Dom.Node
  clickRef        : IO.Ref (Array Msg)
  inputRef        : IO.Ref (Array (String → Msg))
  rowEvRef        : IO.Ref (Array (Nat → Nat → Option Msg))
  chunkCbRef      : IO.Ref (Array (String → Msg))
  streamBufRef    : IO.Ref (Std.HashMap Nat String)
  doneCbRef       : IO.Ref (Array (Nat × Msg))
  respCbRef       : IO.Ref (Std.HashMap Nat (Except String String → Msg))
  respBytesCbRef  : IO.Ref (Std.HashMap Nat (Except String ByteArray → Msg))
  httpTimerRef    : IO.Ref (Std.HashMap Nat Nat)
  effectCbRef     : IO.Ref (Std.HashMap Nat (String → Msg))
  wsTimerCbRef    : IO.Ref (Std.HashMap Nat (IO Unit))
  cbNextRef       : IO.Ref Nat
  wsNextIdRef     : IO.Ref UInt32
  wsBootedRef     : IO.Ref Bool
  wsConnOwnerRef  : IO.Ref (Std.HashMap UInt32 WsConnOwner)
  wsMuxSlotRef    : IO.Ref (Std.HashMap String UInt32)
  wsMuxSubUrlRef  : IO.Ref (Std.HashMap UInt32 String)
  wsMuxPoolsRef   : IO.Ref (Std.HashMap String (WsMuxPool Msg))
  wsExtSlotRef    : IO.Ref (Std.HashMap String UInt32)
  wsExtEntriesRef : IO.Ref (Std.HashMap UInt32 (WsExtConnEntry Msg))
  dispatchRef     : IO.Ref (Msg → IO Unit)
  localCtx        : LocalCtx
  handlers        : Handlers Msg
  renderingRef    : IO.Ref Bool
  pendingRef      : IO.Ref (Array Msg)

private def nextWsId (env : RuntimeEnv Model Msg) : IO UInt32 := do
  let n ← env.wsNextIdRef.get
  let nxt := if n + 1 == 0 then 1 else n + 1
  env.wsNextIdRef.set nxt
  return n

private def cancelWsTimer (env : RuntimeEnv Model Msg) (key : String) (tid? : Option Nat) : IO Unit := do
  if let some tid := tid? then env.wsTimerCbRef.modify (·.erase tid)
  Dom.effect "timer.cancel" key "" ""

private def scheduleWsTimer (env : RuntimeEnv Model Msg) (key : String) (oldTid? : Option Nat)
    (delayMs : Nat) (act : IO Unit) : IO Nat := do
  if let some oldTid := oldTid? then env.wsTimerCbRef.modify (·.erase oldTid)
  let tid ← env.cbNextRef.modifyGet (fun n => (n, n + 1))
  env.wsTimerCbRef.modify (·.insert tid act)
  Dom.effectResult "timer.afterKeyed" key (toString delayMs) (UInt32.ofNat tid)
  return tid

private def cancelHttpTimer (env : RuntimeEnv Model Msg) (id : Nat) : IO Unit := do
  if let some tid := (← env.httpTimerRef.get)[id]? then
    env.httpTimerRef.modify (·.erase id)
    cancelWsTimer env (httpTimerKey id) (some tid)

private def armHttpTimeout (env : RuntimeEnv Model Msg) (id : Nat) (onTimeout : IO Unit) : IO Unit := do
  if env.httpTimeoutMs > 0 then
    let tid ← scheduleWsTimer env (httpTimerKey id) none env.httpTimeoutMs onTimeout
    env.httpTimerRef.modify (·.insert id tid)

private def ensureMuxConn (env : RuntimeEnv Model Msg) (url : String) : IO Unit := do
  let some pool := (← env.wsMuxPoolsRef.get)[url]? | return
  if pool.subs.isEmpty || pool.connId.isSome then return
  cancelWsTimer env pool.timerKey pool.timerId
  let cid ← nextWsId env
  env.wsMuxPoolsRef.modify (·.insert url { pool with connId := some cid, isOpen := false, timerId := none })
  env.wsConnOwnerRef.modify (·.insert cid (.mux url))
  Dom.wsOpen cid url true

private def openExtConn (env : RuntimeEnv Model Msg) (subId : UInt32) : IO Unit := do
  let some entry := (← env.wsExtEntriesRef.get)[subId]? | return
  if entry.closed || entry.connId.isSome then return
  cancelWsTimer env entry.timerKey entry.timerId
  let cid ← nextWsId env
  env.wsExtEntriesRef.modify (·.insert subId { entry with connId := some cid, isOpen := false, timerId := none })
  env.wsConnOwnerRef.modify (·.insert cid (.ext subId))
  Dom.wsOpen cid entry.url entry.isBinary

private def closeMuxSlot (env : RuntimeEnv Model Msg) (slot : String) : IO Unit := do
  let some sid := (← env.wsMuxSlotRef.get)[slot]? | return
  env.wsMuxSlotRef.modify (·.erase slot)
  let some url := (← env.wsMuxSubUrlRef.get)[sid]? | return
  env.wsMuxSubUrlRef.modify (·.erase sid)
  let some pool := (← env.wsMuxPoolsRef.get)[url]? | return
  let subs' := pool.subs.erase sid
  if pool.isOpen then
    if let some cid := pool.connId then
      Dom.wsSendBytes cid (WsMuxFrame.encode (.unsub sid))
  if subs'.isEmpty then
    cancelWsTimer env pool.timerKey pool.timerId
    env.wsMuxPoolsRef.modify (·.erase url)
    if let some cid := pool.connId then
      env.wsConnOwnerRef.modify (·.erase cid)
      Dom.wsClose cid
  else
    env.wsMuxPoolsRef.modify (·.insert url { pool with subs := subs' })

private def closeExtSlot (env : RuntimeEnv Model Msg) (slot : String) : IO Unit := do
  let some sid := (← env.wsExtSlotRef.get)[slot]? | return
  env.wsExtSlotRef.modify (·.erase slot)
  let some entry := (← env.wsExtEntriesRef.get)[sid]? | return
  env.wsExtEntriesRef.modify (·.erase sid)
  cancelWsTimer env entry.timerKey entry.timerId
  if let some cid := entry.connId then
    env.wsConnOwnerRef.modify (·.erase cid)
    Dom.wsClose cid

private def gcLocals (env : RuntimeEnv Model Msg) : IO Unit := do
  let mut dead : Array String := #[]
  for (k, inst) in (← env.localCtx.instances.get).toList do
    unless (← Dom.isConnected inst.host) do dead := dead.push k
  for k in dead do
    env.localCtx.instances.modify (·.erase k)
    env.localCtx.store.modify (·.erase k)

private def renderModel (env : RuntimeEnv Model Msg) : IO Unit := do
  match ← env.vstateRef.get with
  | none => do
      let existing ← Dom.appRoot
      if existing != (0 : Dom.Node) then
        let vst ← hydrateView env.handlers env.app.template (← env.modelRef.get) existing
        env.rootRef.set existing; env.vstateRef.set (some vst)
      else
        let (node, vst) ← buildView env.handlers "" env.app.template (← env.modelRef.get)
        Dom.mountRoot node; env.rootRef.set node; env.vstateRef.set (some vst)
  | some vst => do
      let vst' ← patchView env.handlers (← env.rootRef.get) 0 env.app.template (← env.modelRef.get) vst
      env.vstateRef.set (some vst')
  gcLocals env

private def performHttp {α : Type} (env : RuntimeEnv Model Msg)
    (cbRef : IO.Ref (Std.HashMap Nat (Except String α → Msg)))
    (send : UInt32 → IO Unit) (onResult : Except String α → Msg) : IO Unit := do
  let id ← env.cbNextRef.modifyGet (fun n => (n, n + 1))
  cbRef.modify (·.insert id onResult)
  armHttpTimeout env id do
    if let some f := (← cbRef.get)[id]? then
      cbRef.modify (·.erase id)
      env.httpTimerRef.modify (·.erase id)
      Dom.effect "http.abort" (toString id) "" ""
      (← env.dispatchRef.get) (f (.error "request timeout"))
  send (UInt32.ofNat id)

private def withOpenExtConn (env : RuntimeEnv Model Msg) (slot : String) (f : UInt32 → IO Unit) : IO Unit := do
  let some sid := (← env.wsExtSlotRef.get)[slot]? | return
  let some entry := (← env.wsExtEntriesRef.get)[sid]? | return
  if entry.isOpen then
    if let some cid := entry.connId then f cid

private def performWsMuxSub (env : RuntimeEnv Model Msg) (slot url channel : String) (params : ByteArray)
    (rec : Reconnect) (onJoin onMessage : ByteArray → Msg) (onStatus : SocketStatus → Msg) : IO Unit := do
  if !(← env.wsBootedRef.get) then return
  closeMuxSlot env slot
  let sid ← nextWsId env
  env.wsMuxSlotRef.modify (·.insert slot sid)
  env.wsMuxSubUrlRef.modify (·.insert sid url)
  let pool := match (← env.wsMuxPoolsRef.get)[url]? with
    | some p => p
    | none   => { url, timerKey := "ws-mux:" ++ url }
  let sub : WsMuxSubEntry Msg := {
    subId := sid, channel, params, reconnect := rec, handlers := { onJoin, onMessage, onStatus }
  }
  env.wsMuxPoolsRef.modify (·.insert url { pool with subs := pool.subs.insert sid sub })
  (← env.dispatchRef.get) (onStatus .connecting)
  if let some pool' := (← env.wsMuxPoolsRef.get)[url]? then
    if pool'.subs.contains sid then
      if pool'.isOpen then
        if let some cid := pool'.connId then
          Dom.wsSendBytes cid (WsMuxFrame.encode (.sub sid channel params))
      else if pool'.connId.isNone then
        ensureMuxConn env url

private def performWsExtOpen (env : RuntimeEnv Model Msg) (slot url : String) (isBinary : Bool)
    (rec : Reconnect) (onJoin : Unit → Msg) (onText : String → Msg) (onBytes : ByteArray → Msg)
    (onStatus : SocketStatus → Msg) : IO Unit := do
  if !(← env.wsBootedRef.get) then return
  closeExtSlot env slot
  let sid ← nextWsId env
  env.wsExtSlotRef.modify (·.insert slot sid)
  let entry : WsExtConnEntry Msg := {
    subId := sid, url, isBinary, reconnect := rec, timerKey := s!"ws-ext:{sid}",
    handlers := { onJoin, onText, onBytes, onStatus }
  }
  env.wsExtEntriesRef.modify (·.insert sid entry)
  (← env.dispatchRef.get) (onStatus .connecting)
  openExtConn env sid

private def performLeaf (env : RuntimeEnv Model Msg) : Cmd Msg → IO Unit
  | .none => pure ()
  | .stream url body onChunk onDone => do
      let cs ← env.chunkCbRef.get; env.chunkCbRef.set (cs.push onChunk)
      let ds ← env.doneCbRef.get;  env.doneCbRef.set (ds.push (cs.size, onDone))
      Dom.fetchStream url body (UInt32.ofNat cs.size) (UInt32.ofNat ds.size)
  | .now onNow => do
      match Qed.Date.parse? (← Dom.today) with
      | some d => (← env.dispatchRef.get) (onNow d)
      | none   => pure ()
  | .request method url body onResult =>
      performHttp env env.respCbRef (Dom.httpSend method url body) onResult
  | .requestBytes method url body onResult =>
      performHttp env env.respBytesCbRef (Dom.httpSendBytes method url body) onResult
  | .pushPath url => do
      Dom.pushPath url.raw
      match env.app.onUrlChange with
      | some f => (← env.dispatchRef.get) (f url.raw)
      | none   => pure ()
  | .port name payload => Dom.portSend name payload
  | .wsMuxSub slot url channel params rec onJoin onMessage onStatus =>
      performWsMuxSub env slot url channel params rec onJoin onMessage onStatus
  | .wsMuxSend slot payload => do
      let some sid := (← env.wsMuxSlotRef.get)[slot]? | return
      let some url := (← env.wsMuxSubUrlRef.get)[sid]? | return
      let some pool := (← env.wsMuxPoolsRef.get)[url]? | return
      if pool.isOpen then
        if let some cid := pool.connId then
          Dom.wsSendBytes cid (WsMuxFrame.encode (.send sid payload))
  | .wsMuxUnsub slot => do
      if (← env.wsBootedRef.get) then closeMuxSlot env slot
  | .wsExtOpen slot url isBinary rec onJoin onText onBytes onStatus =>
      performWsExtOpen env slot url isBinary rec onJoin onText onBytes onStatus
  | .wsExtSendText slot text => withOpenExtConn env slot (Dom.wsSendText · text)
  | .wsExtSendBytes slot payload => withOpenExtConn env slot (Dom.wsSendBytes · payload)
  | .wsExtClose slot => do
      if (← env.wsBootedRef.get) then closeExtSlot env slot
  | .fx kind a b c => Dom.effect kind a b c
  | .fxResult kind a b onResult => do
      let id ← env.cbNextRef.modifyGet (fun n => (n, n + 1))
      env.effectCbRef.modify (·.insert id onResult)
      Dom.effectResult kind a b (UInt32.ofNat id)
  | .batch _ => pure ()

private def performCmd (env : RuntimeEnv Model Msg) (cmd : Cmd Msg) : IO Unit :=
  (Cmd.flatten cmd).forM (performLeaf env)

private def applyOne (env : RuntimeEnv Model Msg) (msg : Msg) : IO (Cmd Msg) := do
  let (m', cmd) := env.app.update (← env.modelRef.get) msg
  env.modelRef.set m'
  env.renderingRef.set true
  try renderModel env finally env.renderingRef.set false
  pure cmd

-- Removing a focused node during patch fires `blur` synchronously; queue re-entrant dispatches until the render finishes.
private def dispatchMsg (env : RuntimeEnv Model Msg) (msg : Msg) : IO Unit := do
  if (← env.renderingRef.get) then
    env.pendingRef.modify (·.push msg)
  else
    performCmd env (← applyOne env msg)
    drainPendingQueue env.pendingRef (fun qm => do performCmd env (← applyOne env qm)) 1024

private def handleLocalDispatch (env : RuntimeEnv Model Msg) (fullKey : String) (id : UInt32) : IO Unit := do
  match (← env.localCtx.instances.get)[fullKey]? with
  | some inst => match (← inst.handlers.click.get)[id.toNat]? with
                 | some lm => localRun env.localCtx fullKey inst lm
                 | none    => pure ()
  | none      => pure ()

private def handleLocalDispatchStr (env : RuntimeEnv Model Msg) (fullKey : String) (id : UInt32) (s : String) : IO Unit := do
  match (← env.localCtx.instances.get)[fullKey]? with
  | some inst => dispatchStrWithRows inst.handlers.input inst.handlers.rowEv (localRun env.localCtx fullKey inst) id s
  | none      => pure ()

private def handleEffectDone (env : RuntimeEnv Model Msg) (id : UInt32) (result : String) : IO Unit := do
  match (← env.wsTimerCbRef.get)[id.toNat]? with
  | some act => env.wsTimerCbRef.modify (·.erase id.toNat); act
  | none =>
      match (← env.effectCbRef.get)[id.toNat]? with
      | some onResult => env.effectCbRef.modify (·.erase id.toNat); dispatchMsg env (onResult result)
      | none          => pure ()

private def handlePortRecv (env : RuntimeEnv Model Msg) (name payload : String) : IO Unit := do
  match env.app.onPort with
  | some f => match f name payload with | some m => dispatchMsg env m | none => pure ()
  | none   => pure ()

private def handleSnapshotLocals (env : RuntimeEnv Model Msg) : IO String := do
  let members := (← env.localCtx.store.get).toList.map (fun (k, v) => (k, Json.str v))
  return Json.render (Json.obj members)

private def handleRestoreLocals (env : RuntimeEnv Model Msg) (s : String) : IO Unit := do
  match Json.parse s with
  | .ok (.obj members) => do
      for (k, v) in members do
        match v with | .str st => env.localCtx.store.modify (·.insert k st) | _ => pure ()
      for (k, _) in (← env.localCtx.instances.get).toList do
        if let some inst := (← env.localCtx.instances.get)[k]? then
          localRerender inst ((← env.localCtx.store.get).getD k "")
  | _ => pure ()

private def handleMount (env : RuntimeEnv Model Msg) : IO Unit := do
  if !env.app.styles.isEmpty then Dom.effect "css.inject" (renderStyleSheet env.app.styles) "" ""
  let st ← Dom.appState
  match (if st.isEmpty then none else env.app.rehydrate st) with
  | some m =>
      env.modelRef.set m
      renderModel env
      env.wsBootedRef.set true
      performCmd env (.batch [env.app.init.2.clientOnly, env.app.onHydrate m])
  | none =>
      match env.app.onUrlChange with
      | some f => do let p ← Dom.currentPath; dispatchMsg env (f p)
      | none   => renderModel env
      performCmd env env.app.init.2
      env.wsBootedRef.set true
      performCmd env (env.app.onHydrate (← env.modelRef.get))

private def handleDispatch (env : RuntimeEnv Model Msg) (id : UInt32) : IO Unit := do
  match (← env.clickRef.get)[id.toNat]? with
  | some msg => dispatchMsg env msg
  | none     => IO.eprintln s!"qed: unknown click id {id}"

private def handleStreamChunk (env : RuntimeEnv Model Msg) (cid : UInt32) (rawChunk : String) : IO Unit := do
  let prev := (← env.streamBufRef.get).getD cid.toNat ""
  let (events, rem) := parseSseBuffer (prev ++ rawChunk)
  env.streamBufRef.modify (·.insert cid.toNat rem)
  if let some f := (← env.chunkCbRef.get)[cid.toNat]? then
    for ev in events do dispatchMsg env (f ev)

private def handleStreamDone (env : RuntimeEnv Model Msg) (did : UInt32) : IO Unit := do
  match (← env.doneCbRef.get)[did.toNat]? with
  | some (cid, msg) =>
      env.streamBufRef.modify (·.erase cid)
      dispatchMsg env msg
  | none => pure ()

private def handleHttpResp {α : Type} (env : RuntimeEnv Model Msg)
    (cbRef : IO.Ref (Std.HashMap Nat (Except String α → Msg)))
    (id : UInt32) (res : Except String α) : IO Unit := do
  cancelHttpTimer env id.toNat
  if let some f := (← cbRef.get)[id.toNat]? then
    cbRef.modify (·.erase id.toNat)
    dispatchMsg env (f res)

private def handleHttpDone (env : RuntimeEnv Model Msg) (id : UInt32) (ok : Bool) (text : String) : IO Unit :=
  handleHttpResp env env.respCbRef id (if ok then .ok text else .error text)

private def handleHttpBytesDone (env : RuntimeEnv Model Msg) (id : UInt32) (ok : Bool) (bytes : ByteArray) : IO Unit :=
  handleHttpResp env env.respBytesCbRef id (if ok then .ok bytes else .error ((String.fromUTF8? bytes).getD "RPC transport error"))

private def handleUrlChanged (env : RuntimeEnv Model Msg) (path : String) : IO Unit := do
  match env.app.onUrlChange with
  | some f => dispatchMsg env (f path)
  | none   => pure ()

private def handleWsOpen (env : RuntimeEnv Model Msg) (cid : UInt32) : IO Unit := do
  match (← env.wsConnOwnerRef.get)[cid]? with
  | some (.mux url) =>
      let some pool := (← env.wsMuxPoolsRef.get)[url]? | return
      if pool.connId != some cid then return
      let resetSubs := pool.subs.fold (init := (∅ : Std.HashMap UInt32 (WsMuxSubEntry Msg)))
        fun acc sid sub => acc.insert sid { sub with attempt := 0, pendingRetry := false, nextAtMs := 0 }
      env.wsMuxPoolsRef.modify (·.insert url { pool with isOpen := true, subs := resetSubs })
      for (_, sub) in resetSubs.toList do
        Dom.wsSendBytes cid (WsMuxFrame.encode (.sub sub.subId sub.channel sub.params))
  | some (.ext subId) =>
      let some entry := (← env.wsExtEntriesRef.get)[subId]? | return
      if entry.closed || entry.connId != some cid then return
      env.wsExtEntriesRef.modify (·.insert subId { entry with attempt := 0, isOpen := true })
      dispatchMsg env (entry.handlers.onStatus .connected)
      dispatchMsg env (entry.handlers.onJoin ())
  | none => pure ()

private def dropMuxSub (env : RuntimeEnv Model Msg) (url : String) (pool : WsMuxPool Msg)
    (sid : UInt32) (st : SocketStatus) : IO Unit := do
  let some sub := pool.subs[sid]? | return
  env.wsMuxSubUrlRef.modify (·.erase sid)
  env.wsMuxPoolsRef.modify (·.insert url { pool with subs := pool.subs.erase sid })
  dispatchMsg env (sub.handlers.onStatus st)

private def handleWsBytes (env : RuntimeEnv Model Msg) (cid : UInt32) (bytes : ByteArray) : IO Unit := do
  match (← env.wsConnOwnerRef.get)[cid]? with
  | some (.mux url) =>
      let some pool := (← env.wsMuxPoolsRef.get)[url]? | return
      if pool.connId != some cid then return
      match WsMuxFrame.decode bytes with
      | .ok (.joinOk sid snap) =>
          let some sub := pool.subs[sid]? | return
          let sub' := { sub with attempt := 0, pendingRetry := false, nextAtMs := 0 }
          env.wsMuxPoolsRef.modify (·.insert url { pool with subs := pool.subs.insert sid sub' })
          dispatchMsg env (sub.handlers.onStatus .connected)
          dispatchMsg env (sub.handlers.onJoin snap)
      | .ok (.event sid payload) =>
          if let some sub := pool.subs[sid]? then
            dispatchMsg env (sub.handlers.onMessage payload)
      | .ok (.err sid msg) => dropMuxSub env url pool sid (.failed msg)
      | .ok (.closed sid _) => dropMuxSub env url pool sid .disconnected
      | _ => pure ()
  | some (.ext subId) =>
      let some entry := (← env.wsExtEntriesRef.get)[subId]? | return
      if entry.closed || entry.connId != some cid then return
      dispatchMsg env (entry.handlers.onBytes bytes)
  | none => pure ()

private def handleWsText (env : RuntimeEnv Model Msg) (cid : UInt32) (text : String) : IO Unit := do
  match (← env.wsConnOwnerRef.get)[cid]? with
  | some (.ext subId) =>
      let some entry := (← env.wsExtEntriesRef.get)[subId]? | return
      if entry.closed || entry.connId != some cid then return
      dispatchMsg env (entry.handlers.onText text)
  | _ => pure ()

private def handleWsCloseMux (env : RuntimeEnv Model Msg) (cid : UInt32) (url err : String) (nowMs : Nat) : IO Unit := do
  let some pool := (← env.wsMuxPoolsRef.get)[url]? | return
  if pool.connId != some cid then return
  if !err.isEmpty then
    cancelWsTimer env pool.timerKey pool.timerId
    env.wsMuxPoolsRef.modify (·.erase url)
    for (sid, _) in pool.subs.toList do env.wsMuxSubUrlRef.modify (·.erase sid)
    for (_, sub) in pool.subs.toList do dispatchMsg env (sub.handlers.onStatus (.failed err))
    return
  if pool.subs.isEmpty then
    cancelWsTimer env pool.timerKey pool.timerId
    env.wsMuxPoolsRef.modify (·.erase url)
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
          env.wsMuxSubUrlRef.modify (·.erase sid)
          statusMsgs := statusMsgs.push (sub.handlers.onStatus (wsClosedStatus sub.reconnect))
      | some d =>
          let sub' := { sub with attempt := sub.attempt + 1, pendingRetry := true, nextAtMs := nowMs + d }
          keptSubs := keptSubs.insert sid sub'
          minDelay? := some (match minDelay? with | some m => min m d | none => d)
          statusMsgs := statusMsgs.push (sub.handlers.onStatus (.reconnecting sub'.attempt))
  if keptSubs.isEmpty then
    cancelWsTimer env pool.timerKey pool.timerId
    env.wsMuxPoolsRef.modify (·.erase url)
  else
    let delayMs := minDelay?.getD 0
    let tid ← scheduleWsTimer env pool.timerKey pool.timerId delayMs (ensureMuxConn env url)
    env.wsMuxPoolsRef.modify (·.insert url { pool with connId := none, isOpen := false, timerId := some tid, subs := keptSubs })
  for m in statusMsgs do dispatchMsg env m

private def dropExtEntry (env : RuntimeEnv Model Msg) (subId : UInt32)
    (entry : WsExtConnEntry Msg) (st : SocketStatus) : IO Unit := do
  cancelWsTimer env entry.timerKey entry.timerId
  env.wsExtEntriesRef.modify (·.erase subId)
  dispatchMsg env (entry.handlers.onStatus st)

private def handleWsCloseExt (env : RuntimeEnv Model Msg) (cid subId : UInt32) (err : String) : IO Unit := do
  let some entry := (← env.wsExtEntriesRef.get)[subId]? | return
  if entry.closed || entry.connId != some cid then return
  if !err.isEmpty then
    dropExtEntry env subId entry (.failed err); return
  match entry.reconnect.nextDelayMs entry.attempt with
  | none => dropExtEntry env subId entry (wsClosedStatus entry.reconnect)
  | some d =>
      let attempt' := entry.attempt + 1
      let tid ← scheduleWsTimer env entry.timerKey entry.timerId d (openExtConn env subId)
      env.wsExtEntriesRef.modify (·.insert subId { entry with attempt := attempt', connId := none, isOpen := false, timerId := some tid })
      dispatchMsg env (entry.handlers.onStatus (.reconnecting attempt'))

private def handleWsClose (env : RuntimeEnv Model Msg) (cid : UInt32) (err : String) (nowMs : Nat) : IO Unit := do
  let owner? := (← env.wsConnOwnerRef.get)[cid]?
  env.wsConnOwnerRef.modify (·.erase cid)
  match owner? with
  | some (.mux url)   => handleWsCloseMux env cid url err nowMs
  | some (.ext subId) => handleWsCloseExt env cid subId err
  | none              => pure ()

def runWithHttpTimeout (app : App Model Msg) (httpTimeoutMs : Nat) : IO Unit := do
  let modelRef        ← IO.mkRef app.init.1
  let vstateRef       ← IO.mkRef (none : Option (VState Model Msg))
  let rootRef         ← IO.mkRef (0 : Dom.Node)
  let clickRef        ← IO.mkRef (#[] : Array Msg)
  let inputRef        ← IO.mkRef (#[] : Array (String → Msg))
  let rowEvRef        ← IO.mkRef (#[] : Array (Nat → Nat → Option Msg))
  let chunkCbRef      ← IO.mkRef (#[] : Array (String → Msg))
  let streamBufRef    ← IO.mkRef (∅ : Std.HashMap Nat String)
  let doneCbRef       ← IO.mkRef (#[] : Array (Nat × Msg))
  let respCbRef       ← IO.mkRef (∅ : Std.HashMap Nat (Except String String → Msg))
  let respBytesCbRef  ← IO.mkRef (∅ : Std.HashMap Nat (Except String ByteArray → Msg))
  let httpTimerRef    ← IO.mkRef (∅ : Std.HashMap Nat Nat)
  let effectCbRef     ← IO.mkRef (∅ : Std.HashMap Nat (String → Msg))
  let wsTimerCbRef    ← IO.mkRef (∅ : Std.HashMap Nat (IO Unit))
  let cbNextRef       ← IO.mkRef (0 : Nat)
  let wsNextIdRef     ← IO.mkRef (1 : UInt32)
  let wsBootedRef     ← IO.mkRef false
  let wsConnOwnerRef  ← IO.mkRef (∅ : Std.HashMap UInt32 WsConnOwner)
  let wsMuxSlotRef    ← IO.mkRef (∅ : Std.HashMap String UInt32)
  let wsMuxSubUrlRef  ← IO.mkRef (∅ : Std.HashMap UInt32 String)
  let wsMuxPoolsRef   ← IO.mkRef (∅ : Std.HashMap String (WsMuxPool Msg))
  let wsExtSlotRef    ← IO.mkRef (∅ : Std.HashMap String UInt32)
  let wsExtEntriesRef ← IO.mkRef (∅ : Std.HashMap UInt32 (WsExtConnEntry Msg))
  let dispatchRef     ← IO.mkRef (fun (_ : Msg) => (pure () : IO Unit))
  let registry : Std.HashMap String LocalDef :=
    app.locals.foldl (fun m d => m.insert d.id d) ∅
  let storeRef        ← IO.mkRef (∅ : Std.HashMap String String)
  let instancesRef    ← IO.mkRef (∅ : Std.HashMap String LocalInstance)
  let localCtx : LocalCtx := { registry, store := storeRef, instances := instancesRef }
  let handlers : Handlers Msg :=
    { click := clickRef, input := inputRef, rowEv := rowEvRef,
      mountLocal := fun k c i p b hn => localMountRoot localCtx (fun m => do (← dispatchRef.get) m) k c i p b hn }
  let renderingRef    ← IO.mkRef false
  let pendingRef      ← IO.mkRef (#[] : Array Msg)
  let env : RuntimeEnv Model Msg := {
    app, httpTimeoutMs, modelRef, vstateRef, rootRef, clickRef, inputRef, rowEvRef,
    chunkCbRef, streamBufRef, doneCbRef, respCbRef, respBytesCbRef, httpTimerRef,
    effectCbRef, wsTimerCbRef, cbNextRef, wsNextIdRef, wsBootedRef, wsConnOwnerRef,
    wsMuxSlotRef, wsMuxSubUrlRef, wsMuxPoolsRef, wsExtSlotRef, wsExtEntriesRef,
    dispatchRef, localCtx, handlers, renderingRef, pendingRef
  }
  dispatchRef.set (dispatchMsg env)
  runtimeRef.set (some {
    mount            := handleMount env
    dispatch         := handleDispatch env
    dispatchStr      := fun id s => dispatchStrWithRows env.inputRef env.rowEvRef (dispatchMsg env) id s
    streamChunk      := handleStreamChunk env
    streamDone       := handleStreamDone env
    httpDone         := handleHttpDone env
    httpBytesDone    := handleHttpBytesDone env
    urlChanged       := handleUrlChanged env
    localDispatch    := handleLocalDispatch env
    localDispatchStr := handleLocalDispatchStr env
    snapshot         := handleSnapshotLocals env
    restore          := handleRestoreLocals env
    dehydrate        := do return env.app.dehydrate (← env.modelRef.get)
    effectDone       := handleEffectDone env
    portRecv         := handlePortRecv env
    wsOpen           := handleWsOpen env
    wsBytes          := handleWsBytes env
    wsText           := handleWsText env
    wsClose          := handleWsClose env
  })

def run (app : App Model Msg) : IO Unit :=
  runWithHttpTimeout app defaultHttpTimeoutMs

end Qed
