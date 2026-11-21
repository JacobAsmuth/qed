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

private structure WsConn where
  url      : String
  connId   : Option UInt32 := none
  isOpen   : Bool := false
  timerKey : String
  timerId  : Option Nat := none

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
  conn : WsConn
  subs : Std.HashMap UInt32 (WsMuxSubEntry msg) := ∅

private structure WsExtConnEntry (msg : Type) where
  subId     : UInt32
  conn      : WsConn
  isBinary  : Bool
  reconnect : Reconnect
  attempt   : Nat := 0
  closed    : Bool := false
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

def defaultHttpTimeoutMs : Nat := 30000

private def httpTimerKey (id : Nat) : String :=
  s!"http:{id}"

private structure RuntimeState (Model Msg : Type) where
  model        : Model
  vstate       : Option (VState Model Msg) := none
  root         : Dom.Node := 0
  chunkCb      : Array (String → Msg) := #[]
  streamBuf    : Std.HashMap Nat String := ∅
  doneCb       : Array (Nat × Msg) := #[]
  respCb       : Std.HashMap Nat (Except String String → Msg) := ∅
  respBytesCb  : Std.HashMap Nat (Except String ByteArray → Msg) := ∅
  httpTimer    : Std.HashMap Nat Nat := ∅
  effectCb     : Std.HashMap Nat (String → Msg) := ∅
  wsTimerCb    : Std.HashMap Nat (IO Unit) := ∅
  cbNext       : Nat := 0
  wsNextId     : UInt32 := 1
  wsBooted     : Bool := false
  wsConnOwner  : Std.HashMap UInt32 WsConnOwner := ∅
  wsMuxSlot    : Std.HashMap String UInt32 := ∅
  wsMuxSubUrl  : Std.HashMap UInt32 String := ∅
  wsMuxPools   : Std.HashMap String (WsMuxPool Msg) := ∅
  wsExtSlot    : Std.HashMap String UInt32 := ∅
  wsExtEntries : Std.HashMap UInt32 (WsExtConnEntry Msg) := ∅
  dispatch     : Msg → IO Unit := fun _ => pure ()
  rendering    : Bool := false
  pending      : Array Msg := #[]

private structure RuntimeEnv (Model Msg : Type) where
  app           : App Model Msg
  httpTimeoutMs : Nat
  state         : IO.Ref (RuntimeState Model Msg)
  localCtx      : LocalCtx
  handlers      : Handlers Msg

private structure HttpCbLens (Model Msg α : Type) where
  get : RuntimeState Model Msg → Std.HashMap Nat (Except String α → Msg)
  mod : (Std.HashMap Nat (Except String α → Msg) → Std.HashMap Nat (Except String α → Msg)) →
        RuntimeState Model Msg → RuntimeState Model Msg

private def respCbLens : HttpCbLens Model Msg String :=
  { get := (·.respCb), mod := fun f st => { st with respCb := f st.respCb } }

private def respBytesCbLens : HttpCbLens Model Msg ByteArray :=
  { get := (·.respBytesCb), mod := fun f st => { st with respBytesCb := f st.respBytesCb } }

private def drainPendingQueue (stateRef : IO.Ref (RuntimeState Model Msg))
    (step : Msg → IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | fuel + 1 => do
      let queued ← stateRef.modifyGet fun st => (st.pending, { st with pending := #[] })
      if queued.isEmpty then pure ()
      else
        for qm in queued do step qm
        drainPendingQueue stateRef step fuel

private def allocCbId (env : RuntimeEnv Model Msg) : IO Nat :=
  env.state.modifyGet fun st => (st.cbNext, { st with cbNext := st.cbNext + 1 })

private def nextWsId (env : RuntimeEnv Model Msg) : IO UInt32 :=
  env.state.modifyGet fun st =>
    let n := st.wsNextId
    (n, { st with wsNextId := if n + 1 == 0 then 1 else n + 1 })

private def cancelWsTimer (env : RuntimeEnv Model Msg) (key : String) (tid? : Option Nat) : IO Unit := do
  if let some tid := tid? then env.state.modify fun st => { st with wsTimerCb := st.wsTimerCb.erase tid }
  Dom.effect "timer.cancel" key "" ""

private def scheduleWsTimer (env : RuntimeEnv Model Msg) (key : String) (oldTid? : Option Nat)
    (delayMs : Nat) (act : IO Unit) : IO Nat := do
  if let some oldTid := oldTid? then env.state.modify fun st => { st with wsTimerCb := st.wsTimerCb.erase oldTid }
  let tid ← allocCbId env
  env.state.modify fun st => { st with wsTimerCb := st.wsTimerCb.insert tid act }
  Dom.effectResult "timer.afterKeyed" key (toString delayMs) (UInt32.ofNat tid)
  return tid

private def cancelHttpTimer (env : RuntimeEnv Model Msg) (id : Nat) : IO Unit := do
  if let some tid := (← env.state.get).httpTimer[id]? then
    env.state.modify fun st => { st with httpTimer := st.httpTimer.erase id }
    cancelWsTimer env (httpTimerKey id) (some tid)

private def armHttpTimeout (env : RuntimeEnv Model Msg) (id : Nat) (onTimeout : IO Unit) : IO Unit := do
  if env.httpTimeoutMs > 0 then
    let tid ← scheduleWsTimer env (httpTimerKey id) none env.httpTimeoutMs onTimeout
    env.state.modify fun st => { st with httpTimer := st.httpTimer.insert id tid }

@[inline] private def withOpenWsConn (conn : WsConn) (f : UInt32 → IO Unit) : IO Unit := do
  if conn.isOpen then if let some cid := conn.connId then f cid

private def openWsConn (env : RuntimeEnv Model Msg) (conn : WsConn) (owner : WsConnOwner)
    (isBinary : Bool) (commit : WsConn → IO Unit) : IO Unit := do
  cancelWsTimer env conn.timerKey conn.timerId
  let cid ← nextWsId env
  commit { conn with connId := some cid, isOpen := false, timerId := none }
  env.state.modify fun st => { st with wsConnOwner := st.wsConnOwner.insert cid owner }
  Dom.wsOpen cid conn.url isBinary

private def closeWsConn (env : RuntimeEnv Model Msg) (conn : WsConn) : IO Unit := do
  cancelWsTimer env conn.timerKey conn.timerId
  if let some cid := conn.connId then
    env.state.modify fun st => { st with wsConnOwner := st.wsConnOwner.erase cid }
    Dom.wsClose cid

private def scheduleWsConnRetry (env : RuntimeEnv Model Msg) (conn : WsConn)
    (delayMs : Nat) (act : IO Unit) : IO WsConn := do
  let tid ← scheduleWsTimer env conn.timerKey conn.timerId delayMs act
  return { conn with connId := none, isOpen := false, timerId := some tid }

private def ensureMuxConn (env : RuntimeEnv Model Msg) (url : String) : IO Unit := do
  let some pool := (← env.state.get).wsMuxPools[url]? | return
  if pool.subs.isEmpty || pool.conn.connId.isSome then return
  openWsConn env pool.conn (.mux url) true fun conn' =>
    env.state.modify fun st => { st with wsMuxPools := st.wsMuxPools.insert url { pool with conn := conn' } }

private def openExtConn (env : RuntimeEnv Model Msg) (subId : UInt32) : IO Unit := do
  let some entry := (← env.state.get).wsExtEntries[subId]? | return
  if entry.closed || entry.conn.connId.isSome then return
  openWsConn env entry.conn (.ext subId) entry.isBinary fun conn' =>
    env.state.modify fun st => { st with wsExtEntries := st.wsExtEntries.insert subId { entry with conn := conn' } }

private def closeMuxSlot (env : RuntimeEnv Model Msg) (slot : String) : IO Unit := do
  let st ← env.state.get
  let some sid := st.wsMuxSlot[slot]? | return
  env.state.modify fun s => { s with wsMuxSlot := s.wsMuxSlot.erase slot }
  let some url := st.wsMuxSubUrl[sid]? | return
  env.state.modify fun s => { s with wsMuxSubUrl := s.wsMuxSubUrl.erase sid }
  let some pool := (← env.state.get).wsMuxPools[url]? | return
  let subs' := pool.subs.erase sid
  withOpenWsConn pool.conn fun cid => Dom.wsSendBytes cid (WsMuxFrame.encode (.unsub sid))
  if subs'.isEmpty then
    env.state.modify fun s => { s with wsMuxPools := s.wsMuxPools.erase url }
    closeWsConn env pool.conn
  else
    env.state.modify fun s => { s with wsMuxPools := s.wsMuxPools.insert url { pool with subs := subs' } }

private def closeExtSlot (env : RuntimeEnv Model Msg) (slot : String) : IO Unit := do
  let some sid := (← env.state.get).wsExtSlot[slot]? | return
  env.state.modify fun s => { s with wsExtSlot := s.wsExtSlot.erase slot }
  let some entry := (← env.state.get).wsExtEntries[sid]? | return
  env.state.modify fun s => { s with wsExtEntries := s.wsExtEntries.erase sid }
  closeWsConn env entry.conn

private def gcLocals (env : RuntimeEnv Model Msg) : IO Unit := do
  let mut dead : Array String := #[]
  for (k, inst) in (← env.localCtx.instances.get).toList do
    unless (← Dom.isConnected inst.host) do dead := dead.push k
  for k in dead do
    env.localCtx.instances.modify (·.erase k)
    env.localCtx.store.modify (·.erase k)

private def renderModel (env : RuntimeEnv Model Msg) : IO Unit := do
  let st ← env.state.get
  match st.vstate with
  | none => do
      let existing ← Dom.appRoot
      if existing != (0 : Dom.Node) then
        let vst ← hydrateView env.handlers env.app.template st.model existing
        env.state.modify fun s => { s with root := existing, vstate := some vst }
      else
        let (node, vst) ← buildView env.handlers "" env.app.template st.model
        Dom.mountRoot node
        env.state.modify fun s => { s with root := node, vstate := some vst }
  | some vst => do
      let vst' ← patchView env.handlers st.root 0 env.app.template st.model vst
      env.state.modify fun s => { s with vstate := some vst' }
  gcLocals env

private def performHttp {α : Type} (env : RuntimeEnv Model Msg) (lens : HttpCbLens Model Msg α)
    (send : UInt32 → IO Unit) (onResult : Except String α → Msg) : IO Unit := do
  let id ← allocCbId env
  env.state.modify (lens.mod (·.insert id onResult))
  armHttpTimeout env id do
    if let some f := (lens.get (← env.state.get))[id]? then
      env.state.modify fun st => { lens.mod (·.erase id) st with httpTimer := st.httpTimer.erase id }
      Dom.effect "http.abort" (toString id) "" ""
      (← env.state.get).dispatch (f (.error "request timeout"))
  send (UInt32.ofNat id)

private def withOpenExtConn (env : RuntimeEnv Model Msg) (slot : String) (f : UInt32 → IO Unit) : IO Unit := do
  let st ← env.state.get
  let some sid := st.wsExtSlot[slot]? | return
  let some entry := st.wsExtEntries[sid]? | return
  withOpenWsConn entry.conn f

private def performWsMuxSub (env : RuntimeEnv Model Msg) (slot url channel : String) (params : ByteArray)
    (rec : Reconnect) (onJoin onMessage : ByteArray → Msg) (onStatus : SocketStatus → Msg) : IO Unit := do
  if !(← env.state.get).wsBooted then return
  closeMuxSlot env slot
  let sid ← nextWsId env
  let sub : WsMuxSubEntry Msg := {
    subId := sid, channel, params, reconnect := rec, handlers := { onJoin, onMessage, onStatus }
  }
  env.state.modify fun st =>
    let pool := st.wsMuxPools[url]?.getD { conn := { url, timerKey := "ws-mux:" ++ url } }
    { st with
      wsMuxSlot := st.wsMuxSlot.insert slot sid
      wsMuxSubUrl := st.wsMuxSubUrl.insert sid url
      wsMuxPools := st.wsMuxPools.insert url { pool with subs := pool.subs.insert sid sub } }
  (← env.state.get).dispatch (onStatus .connecting)
  if let some pool' := (← env.state.get).wsMuxPools[url]? then
    if pool'.subs.contains sid then
      if pool'.conn.isOpen then
        withOpenWsConn pool'.conn fun cid => Dom.wsSendBytes cid (WsMuxFrame.encode (.sub sid channel params))
      else if pool'.conn.connId.isNone then
        ensureMuxConn env url

private def performWsExtOpen (env : RuntimeEnv Model Msg) (slot url : String) (isBinary : Bool)
    (rec : Reconnect) (onJoin : Unit → Msg) (onText : String → Msg) (onBytes : ByteArray → Msg)
    (onStatus : SocketStatus → Msg) : IO Unit := do
  if !(← env.state.get).wsBooted then return
  closeExtSlot env slot
  let sid ← nextWsId env
  let entry : WsExtConnEntry Msg := {
    subId := sid, conn := { url, timerKey := s!"ws-ext:{sid}" },
    isBinary, reconnect := rec, handlers := { onJoin, onText, onBytes, onStatus }
  }
  env.state.modify fun st =>
    { st with wsExtSlot := st.wsExtSlot.insert slot sid, wsExtEntries := st.wsExtEntries.insert sid entry }
  (← env.state.get).dispatch (onStatus .connecting)
  openExtConn env sid

private def performLeaf (env : RuntimeEnv Model Msg) : Cmd Msg → IO Unit
  | .none => pure ()
  | .stream url body onChunk onDone => do
      let (cid, did) ← env.state.modifyGet fun st =>
        let c := st.chunkCb.size; let d := st.doneCb.size
        ((c, d), { st with chunkCb := st.chunkCb.push onChunk, doneCb := st.doneCb.push (c, onDone) })
      Dom.fetchStream url body (UInt32.ofNat cid) (UInt32.ofNat did)
  | .now onNow => do
      if let some d := Qed.Date.parse? (← Dom.today) then (← env.state.get).dispatch (onNow d)
  | .request method url body onResult => performHttp env respCbLens (Dom.httpSend method url body) onResult
  | .requestBytes method url body onResult => performHttp env respBytesCbLens (Dom.httpSendBytes method url body) onResult
  | .pushPath url => do
      Dom.pushPath url.raw
      if let some f := env.app.onUrlChange then (← env.state.get).dispatch (f url.raw)
  | .port name payload => Dom.portSend name payload
  | .wsMuxSub slot url channel params rec onJoin onMessage onStatus =>
      performWsMuxSub env slot url channel params rec onJoin onMessage onStatus
  | .wsMuxSend slot payload => do
      let st ← env.state.get
      let some sid := st.wsMuxSlot[slot]? | return
      let some url := st.wsMuxSubUrl[sid]? | return
      let some pool := st.wsMuxPools[url]? | return
      withOpenWsConn pool.conn fun cid => Dom.wsSendBytes cid (WsMuxFrame.encode (.send sid payload))
  | .wsMuxUnsub slot => do if (← env.state.get).wsBooted then closeMuxSlot env slot
  | .wsExtOpen slot url isBinary rec onJoin onText onBytes onStatus =>
      performWsExtOpen env slot url isBinary rec onJoin onText onBytes onStatus
  | .wsExtSendText slot text => withOpenExtConn env slot (Dom.wsSendText · text)
  | .wsExtSendBytes slot payload => withOpenExtConn env slot (Dom.wsSendBytes · payload)
  | .wsExtClose slot => do if (← env.state.get).wsBooted then closeExtSlot env slot
  | .fx kind a b c => Dom.effect kind a b c
  | .fxResult kind a b onResult => do
      let id ← allocCbId env
      env.state.modify fun st => { st with effectCb := st.effectCb.insert id onResult }
      Dom.effectResult kind a b (UInt32.ofNat id)
  | .batch _ => pure ()

private def performCmd (env : RuntimeEnv Model Msg) (cmd : Cmd Msg) : IO Unit :=
  (Cmd.flatten cmd).forM (performLeaf env)

private def applyOne (env : RuntimeEnv Model Msg) (msg : Msg) : IO (Cmd Msg) := do
  let (m', cmd) := env.app.update (← env.state.get).model msg
  env.state.modify fun st => { st with model := m', rendering := true }
  try renderModel env finally env.state.modify fun st => { st with rendering := false }
  pure cmd

-- Removing a focused node during patch fires `blur` synchronously; queue re-entrant dispatches until the render finishes.
private def dispatchMsg (env : RuntimeEnv Model Msg) (msg : Msg) : IO Unit := do
  if (← env.state.get).rendering then
    env.state.modify fun st => { st with pending := st.pending.push msg }
  else
    performCmd env (← applyOne env msg)
    drainPendingQueue env.state (fun qm => do performCmd env (← applyOne env qm)) 1024

private def handleLocalDispatch (env : RuntimeEnv Model Msg) (fullKey : String) (id : UInt32) : IO Unit := do
  if let some inst := (← env.localCtx.instances.get)[fullKey]? then
    if let some lm := (← inst.handlers.click.get)[id.toNat]? then
      localRun env.localCtx fullKey inst lm

private def handleLocalDispatchStr (env : RuntimeEnv Model Msg) (fullKey : String) (id : UInt32) (s : String) : IO Unit := do
  if let some inst := (← env.localCtx.instances.get)[fullKey]? then
    dispatchStrWithRows inst.handlers.input inst.handlers.rowEv (localRun env.localCtx fullKey inst) id s

private def handleEffectDone (env : RuntimeEnv Model Msg) (id : UInt32) (result : String) : IO Unit := do
  let st ← env.state.get
  match st.wsTimerCb[id.toNat]? with
  | some act => env.state.modify fun s => { s with wsTimerCb := s.wsTimerCb.erase id.toNat }; act
  | none =>
      if let some onResult := st.effectCb[id.toNat]? then
        env.state.modify fun s => { s with effectCb := s.effectCb.erase id.toNat }
        dispatchMsg env (onResult result)

private def handlePortRecv (env : RuntimeEnv Model Msg) (name payload : String) : IO Unit := do
  if let some f := env.app.onPort then
    if let some m := f name payload then dispatchMsg env m

private def handleSnapshotLocals (env : RuntimeEnv Model Msg) : IO String := do
  let members := (← env.localCtx.store.get).toList.map (fun (k, v) => (k, Json.str v))
  return Json.render (Json.obj members)

private def handleRestoreLocals (env : RuntimeEnv Model Msg) (s : String) : IO Unit := do
  if let .ok (.obj members) := Json.parse s then
    for (k, v) in members do
      if let .str st := v then env.localCtx.store.modify (·.insert k st)
    for (k, _) in (← env.localCtx.instances.get).toList do
      if let some inst := (← env.localCtx.instances.get)[k]? then
        localRerender inst ((← env.localCtx.store.get).getD k "")

private def handleMount (env : RuntimeEnv Model Msg) : IO Unit := do
  if !env.app.styles.isEmpty then Dom.effect "css.inject" (renderStyleSheet env.app.styles) "" ""
  let st ← Dom.appState
  match (if st.isEmpty then none else env.app.rehydrate st) with
  | some m =>
      env.state.modify fun s => { s with model := m }
      renderModel env
      env.state.modify fun s => { s with wsBooted := true }
      performCmd env (.batch [env.app.init.2.clientOnly, env.app.onHydrate m])
  | none =>
      match env.app.onUrlChange with
      | some f => do let p ← Dom.currentPath; dispatchMsg env (f p)
      | none   => renderModel env
      performCmd env env.app.init.2
      env.state.modify fun s => { s with wsBooted := true }
      performCmd env (env.app.onHydrate (← env.state.get).model)

private def handleDispatch (env : RuntimeEnv Model Msg) (id : UInt32) : IO Unit := do
  match (← env.handlers.click.get)[id.toNat]? with
  | some msg => dispatchMsg env msg
  | none     => IO.eprintln s!"qed: unknown click id {id}"

private def handleStreamChunk (env : RuntimeEnv Model Msg) (cid : UInt32) (rawChunk : String) : IO Unit := do
  let st ← env.state.get
  let (events, rem) := parseSseBuffer (st.streamBuf.getD cid.toNat "" ++ rawChunk)
  env.state.modify fun s => { s with streamBuf := s.streamBuf.insert cid.toNat rem }
  if let some f := st.chunkCb[cid.toNat]? then
    for ev in events do dispatchMsg env (f ev)

private def handleStreamDone (env : RuntimeEnv Model Msg) (did : UInt32) : IO Unit := do
  if let some (cid, msg) := (← env.state.get).doneCb[did.toNat]? then
    env.state.modify fun s => { s with streamBuf := s.streamBuf.erase cid }
    dispatchMsg env msg

private def handleHttpResp {α : Type} (env : RuntimeEnv Model Msg) (lens : HttpCbLens Model Msg α)
    (id : UInt32) (res : Except String α) : IO Unit := do
  cancelHttpTimer env id.toNat
  if let some f := (lens.get (← env.state.get))[id.toNat]? then
    env.state.modify (lens.mod (·.erase id.toNat))
    dispatchMsg env (f res)

private def handleHttpDone (env : RuntimeEnv Model Msg) (id : UInt32) (ok : Bool) (text : String) : IO Unit :=
  handleHttpResp env respCbLens id (if ok then .ok text else .error text)

private def handleHttpBytesDone (env : RuntimeEnv Model Msg) (id : UInt32) (ok : Bool) (bytes : ByteArray) : IO Unit :=
  handleHttpResp env respBytesCbLens id (if ok then .ok bytes else .error ((String.fromUTF8? bytes).getD "RPC transport error"))

private def handleUrlChanged (env : RuntimeEnv Model Msg) (path : String) : IO Unit := do
  if let some f := env.app.onUrlChange then dispatchMsg env (f path)

private def handleWsOpen (env : RuntimeEnv Model Msg) (cid : UInt32) : IO Unit := do
  let st ← env.state.get
  match st.wsConnOwner[cid]? with
  | some (.mux url) =>
      let some pool := st.wsMuxPools[url]? | return
      if pool.conn.connId != some cid then return
      let resetSubs := pool.subs.fold (init := (∅ : Std.HashMap UInt32 (WsMuxSubEntry Msg)))
        fun acc sid sub => acc.insert sid { sub with attempt := 0, pendingRetry := false, nextAtMs := 0 }
      env.state.modify fun s =>
        { s with wsMuxPools := s.wsMuxPools.insert url { conn := { pool.conn with isOpen := true }, subs := resetSubs } }
      for (_, sub) in resetSubs.toList do
        Dom.wsSendBytes cid (WsMuxFrame.encode (.sub sub.subId sub.channel sub.params))
  | some (.ext subId) =>
      let some entry := st.wsExtEntries[subId]? | return
      if entry.closed || entry.conn.connId != some cid then return
      env.state.modify fun s =>
        { s with wsExtEntries := s.wsExtEntries.insert subId { entry with attempt := 0, conn := { entry.conn with isOpen := true } } }
      dispatchMsg env (entry.handlers.onStatus .connected)
      dispatchMsg env (entry.handlers.onJoin ())
  | none => pure ()

private def dropMuxSub (env : RuntimeEnv Model Msg) (url : String) (pool : WsMuxPool Msg)
    (sid : UInt32) (st : SocketStatus) : IO Unit := do
  let some sub := pool.subs[sid]? | return
  env.state.modify fun s =>
    { s with
      wsMuxSubUrl := s.wsMuxSubUrl.erase sid
      wsMuxPools := s.wsMuxPools.insert url { pool with subs := pool.subs.erase sid } }
  dispatchMsg env (sub.handlers.onStatus st)

private def handleWsBytes (env : RuntimeEnv Model Msg) (cid : UInt32) (bytes : ByteArray) : IO Unit := do
  let st ← env.state.get
  match st.wsConnOwner[cid]? with
  | some (.mux url) =>
      let some pool := st.wsMuxPools[url]? | return
      if pool.conn.connId != some cid then return
      match WsMuxFrame.decode bytes with
      | .ok (.joinOk sid snap) =>
          let some sub := pool.subs[sid]? | return
          let sub' := { sub with attempt := 0, pendingRetry := false, nextAtMs := 0 }
          env.state.modify fun s =>
            { s with wsMuxPools := s.wsMuxPools.insert url { pool with subs := pool.subs.insert sid sub' } }
          dispatchMsg env (sub.handlers.onStatus .connected)
          dispatchMsg env (sub.handlers.onJoin snap)
      | .ok (.event sid payload) =>
          if let some sub := pool.subs[sid]? then dispatchMsg env (sub.handlers.onMessage payload)
      | .ok (.err sid msg) => dropMuxSub env url pool sid (.failed msg)
      | .ok (.closed sid _) => dropMuxSub env url pool sid .disconnected
      | _ => pure ()
  | some (.ext subId) =>
      let some entry := st.wsExtEntries[subId]? | return
      if entry.closed || entry.conn.connId != some cid then return
      dispatchMsg env (entry.handlers.onBytes bytes)
  | none => pure ()

private def handleWsText (env : RuntimeEnv Model Msg) (cid : UInt32) (text : String) : IO Unit := do
  let st ← env.state.get
  if let some (.ext subId) := st.wsConnOwner[cid]? then
    let some entry := st.wsExtEntries[subId]? | return
    if entry.closed || entry.conn.connId != some cid then return
    dispatchMsg env (entry.handlers.onText text)

private def handleWsCloseMux (env : RuntimeEnv Model Msg) (cid : UInt32) (url err : String) (nowMs : Nat) : IO Unit := do
  let some pool := (← env.state.get).wsMuxPools[url]? | return
  if pool.conn.connId != some cid then return
  if !err.isEmpty || pool.subs.isEmpty then
    cancelWsTimer env pool.conn.timerKey pool.conn.timerId
    env.state.modify fun s =>
      let subUrl' := pool.subs.fold (init := s.wsMuxSubUrl) fun acc sid _ => acc.erase sid
      { s with wsMuxPools := s.wsMuxPools.erase url, wsMuxSubUrl := subUrl' }
    if !err.isEmpty then
      for (_, sub) in pool.subs.toList do dispatchMsg env (sub.handlers.onStatus (.failed err))
    return
  let mut keptSubs : Std.HashMap UInt32 (WsMuxSubEntry Msg) := ∅
  let mut statusMsgs : Array Msg := #[]
  let mut minDelay? : Option Nat := none
  let mut dropSids : Array UInt32 := #[]
  for (sid, sub) in pool.subs.toList do
    if sub.pendingRetry && nowMs < sub.nextAtMs then
      let rem := sub.nextAtMs - nowMs
      keptSubs := keptSubs.insert sid sub
      minDelay? := some (match minDelay? with | some m => min m rem | none => rem)
    else
      match sub.reconnect.nextDelayMs sub.attempt with
      | none =>
          dropSids := dropSids.push sid
          statusMsgs := statusMsgs.push (sub.handlers.onStatus (wsClosedStatus sub.reconnect))
      | some d =>
          let sub' := { sub with attempt := sub.attempt + 1, pendingRetry := true, nextAtMs := nowMs + d }
          keptSubs := keptSubs.insert sid sub'
          minDelay? := some (match minDelay? with | some m => min m d | none => d)
          statusMsgs := statusMsgs.push (sub.handlers.onStatus (.reconnecting sub'.attempt))
  if !dropSids.isEmpty then
    env.state.modify fun s =>
      { s with wsMuxSubUrl := dropSids.foldl (fun acc sid => acc.erase sid) s.wsMuxSubUrl }
  if keptSubs.isEmpty then
    cancelWsTimer env pool.conn.timerKey pool.conn.timerId
    env.state.modify fun s => { s with wsMuxPools := s.wsMuxPools.erase url }
  else
    let conn' ← scheduleWsConnRetry env pool.conn (minDelay?.getD 0) (ensureMuxConn env url)
    env.state.modify fun s => { s with wsMuxPools := s.wsMuxPools.insert url { conn := conn', subs := keptSubs } }
  for m in statusMsgs do dispatchMsg env m

private def dropExtEntry (env : RuntimeEnv Model Msg) (subId : UInt32)
    (entry : WsExtConnEntry Msg) (st : SocketStatus) : IO Unit := do
  cancelWsTimer env entry.conn.timerKey entry.conn.timerId
  env.state.modify fun s => { s with wsExtEntries := s.wsExtEntries.erase subId }
  dispatchMsg env (entry.handlers.onStatus st)

private def handleWsCloseExt (env : RuntimeEnv Model Msg) (cid subId : UInt32) (err : String) : IO Unit := do
  let some entry := (← env.state.get).wsExtEntries[subId]? | return
  if entry.closed || entry.conn.connId != some cid then return
  if !err.isEmpty then dropExtEntry env subId entry (.failed err); return
  match entry.reconnect.nextDelayMs entry.attempt with
  | none => dropExtEntry env subId entry (wsClosedStatus entry.reconnect)
  | some d =>
      let attempt' := entry.attempt + 1
      let conn' ← scheduleWsConnRetry env entry.conn d (openExtConn env subId)
      env.state.modify fun s =>
        { s with wsExtEntries := s.wsExtEntries.insert subId { entry with attempt := attempt', conn := conn' } }
      dispatchMsg env (entry.handlers.onStatus (.reconnecting attempt'))

private def handleWsClose (env : RuntimeEnv Model Msg) (cid : UInt32) (err : String) (nowMs : Nat) : IO Unit := do
  let owner? ← env.state.modifyGet fun s => (s.wsConnOwner[cid]?, { s with wsConnOwner := s.wsConnOwner.erase cid })
  match owner? with
  | some (.mux url)   => handleWsCloseMux env cid url err nowMs
  | some (.ext subId) => handleWsCloseExt env cid subId err
  | none              => pure ()

def runWithHttpTimeout (app : App Model Msg) (httpTimeoutMs : Nat) : IO Unit := do
  let state        ← IO.mkRef ({ model := app.init.1 } : RuntimeState Model Msg)
  let clickRef     ← IO.mkRef (#[] : Array Msg)
  let inputRef     ← IO.mkRef (#[] : Array (String → Msg))
  let rowEvRef     ← IO.mkRef (#[] : Array (Nat → Nat → Option Msg))
  let localCtx : LocalCtx := {
    registry  := app.locals.foldl (fun m d => m.insert d.id d) ∅
    store     := ← IO.mkRef (∅ : Std.HashMap String String)
    instances := ← IO.mkRef (∅ : Std.HashMap String LocalInstance)
  }
  let handlers : Handlers Msg := {
    click := clickRef, input := inputRef, rowEv := rowEvRef,
    mountLocal := fun k c i p b hn => localMountRoot localCtx (fun m => do (← state.get).dispatch m) k c i p b hn
  }
  let env : RuntimeEnv Model Msg := { app, httpTimeoutMs, state, localCtx, handlers }
  state.modify fun s => { s with dispatch := dispatchMsg env }
  runtimeRef.set (some {
    mount            := handleMount env
    dispatch         := handleDispatch env
    dispatchStr      := fun id s => dispatchStrWithRows env.handlers.input env.handlers.rowEv (dispatchMsg env) id s
    streamChunk      := handleStreamChunk env
    streamDone       := handleStreamDone env
    httpDone         := handleHttpDone env
    httpBytesDone    := handleHttpBytesDone env
    urlChanged       := handleUrlChanged env
    localDispatch    := handleLocalDispatch env
    localDispatchStr := handleLocalDispatchStr env
    snapshot         := handleSnapshotLocals env
    restore          := handleRestoreLocals env
    dehydrate        := do return env.app.dehydrate (← env.state.get).model
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
