import Qed.Driver.Template
import Qed.Driver.Local
import Qed.Runtime.AppCore

namespace Qed

private inductive WsSubMode (msg : Type) where
  | mux (channel : String) (params : ByteArray) (onJoin onMessage : ByteArray → msg)
  | ext (onJoin : Unit → msg) (onText : String → msg) (onBytes : ByteArray → msg)
private structure WsSub (msg : Type) where
  subId        : UInt32
  mode         : WsSubMode msg
  reconnect    : Reconnect
  attempt      : Nat := 0
  pendingRetry : Bool := false
  nextAtMs     : Nat := 0
  onStatus     : SocketStatus → msg
private structure WsPool (msg : Type) where
  url      : String
  isBinary : Bool
  isMux    : Bool
  connId   : Option UInt32 := none
  isOpen   : Bool := false
  timerId  : Option Nat := none
  subs     : Std.HashMap UInt32 (WsSub msg) := ∅

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
@[inline] private def withRuntimeUnit (f : Runtime → IO Unit) : IO Unit := withRuntime (pure ()) f
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

private def parseSseBuffer (buf : String) : Array String × String :=
  let rec go (acc : Array String) : List String → Array String × String
    | [] => (acc, "") | [rem] => (acc, rem)
    | l :: ls => let t := l.trimmed
        go (if t.startsWith "data:" then let p := (String.ofList (t.toList.drop 5)).trimmed; if !p.isEmpty && p != "[DONE]" then acc.push p else acc else acc) ls
  go #[] (buf.splitOn "\n")
private def wsClosedStatus : Reconnect → SocketStatus | .off => .disconnected | _ => .failed "disconnected"
private def resetSub (sub : WsSub Msg) : WsSub Msg := { sub with attempt := 0, pendingRetry := false, nextAtMs := 0 }
def defaultHttpTimeoutMs : Nat := 30000
private abbrev HttpCb (Msg : Type) := Sum (Except String String → Msg) (Except String ByteArray → Msg)

private structure RuntimeState (Model Msg : Type) where
  model       : Model
  vstate      : Option (VState Model Msg) := none
  root        : Dom.Node := 0
  streams     : Array ((String → Msg) × Msg × String) := #[]
  httpCb      : Std.HashMap Nat (HttpCb Msg × Option Nat) := ∅
  effectCb    : Std.HashMap Nat (String → IO Unit) := ∅
  cbNext      : Nat := 0
  wsNextId    : UInt32 := 1
  wsBooted    : Bool := false
  wsConnOwner : Std.HashMap UInt32 String := ∅
  wsSlot      : Std.HashMap String (UInt32 × String) := ∅
  wsPools     : Std.HashMap String (WsPool Msg) := ∅
  dispatch    : Msg → IO Unit := fun _ => pure ()
  rendering   : Bool := false
  pending     : Array Msg := #[]
private structure RuntimeEnv (Model Msg : Type) where
  app           : App Model Msg
  httpTimeoutMs : Nat
  state         : IO.Ref (RuntimeState Model Msg)
  localCtx      : LocalCtx
  handlers      : Handlers Msg

section RuntimeOps
variable {Model Msg : Type} (env : RuntimeEnv Model Msg)
@[inline] private def emit (m : Msg) : IO Unit := do (← env.state.get).dispatch m
@[inline] private def allocCbId : IO Nat := env.state.modifyGet fun st => (st.cbNext, { st with cbNext := st.cbNext + 1 })
@[inline] private def nextWsId : IO UInt32 :=
  env.state.modifyGet fun st => (st.wsNextId, { st with wsNextId := if st.wsNextId + 1 == 0 then 1 else st.wsNextId + 1 })
@[inline] private def putPool (k : String) (p : WsPool Msg) : IO Unit :=
  env.state.modify fun s => { s with wsPools := s.wsPools.insert k p }
private def setTimer (key : String) (oldTid? : Option Nat) (next? : Option (Nat × IO Unit) := none) : IO (Option Nat) := do
  if let some old := oldTid? then env.state.modify fun st => { st with effectCb := st.effectCb.erase old }
  match next? with
  | none => Dom.effect "timer.cancel" key "" ""; return none
  | some (ms, act) =>
      let tid ← allocCbId env
      env.state.modify fun st => { st with effectCb := st.effectCb.insert tid fun _ => act }
      Dom.effectResult "timer.afterKeyed" key (toString ms) (UInt32.ofNat tid); return some tid
private def dropPool (k : String) (p : WsPool Msg) (eraseConn : Bool := false) : IO Unit := do
  discard <| setTimer env ("ws:" ++ k) p.timerId
  env.state.modify fun s =>
    { s with wsPools := s.wsPools.erase k, wsConnOwner := if eraseConn then p.connId.elim s.wsConnOwner s.wsConnOwner.erase else s.wsConnOwner }
private def openPoolConn (poolKey : String) : IO Unit := do
  let some pool := (← env.state.get).wsPools[poolKey]? | return
  if !pool.subs.isEmpty && pool.connId.isNone then
    discard <| setTimer env ("ws:" ++ poolKey) pool.timerId
    let cid ← nextWsId env
    env.state.modify fun s =>
      { s with wsPools := s.wsPools.insert poolKey { pool with connId := some cid, isOpen := false, timerId := none },
               wsConnOwner := s.wsConnOwner.insert cid poolKey }
    Dom.wsOpen cid pool.url pool.isBinary
private def closeWsSlot (slotKey : String) : IO Unit := do
  let st ← env.state.get
  if !st.wsBooted then return
  let some (sid, poolKey) := st.wsSlot[slotKey]? | return
  env.state.modify fun s => { s with wsSlot := s.wsSlot.erase slotKey }
  let some pool := st.wsPools[poolKey]? | return
  if !pool.subs.contains sid then return
  if pool.isMux && pool.isOpen then if let some cid := pool.connId then Dom.wsSendBytes cid (WsMuxFrame.encode (.unsub sid))
  let subs' := pool.subs.erase sid
  if subs'.isEmpty then
    dropPool env poolKey pool true
    if let some cid := pool.connId then Dom.wsClose cid
  else putPool env poolKey { pool with subs := subs' }
private def withOpenSlot (slotKey : String) (f : UInt32 → UInt32 → IO Unit) : IO Unit := do
  let st ← env.state.get
  if let some (sid, poolKey) := st.wsSlot[slotKey]? then
    if let some pool := st.wsPools[poolKey]? then
      if pool.isOpen && pool.subs.contains sid then if let some cid := pool.connId then f cid sid
private def openWsSub (slotKey : String) (poolKey? : Option String) (url : String) (isBinary isMux : Bool)
    (rec : Reconnect) (mode : WsSubMode Msg) (onStatus : SocketStatus → Msg) : IO Unit := do
  if !(← env.state.get).wsBooted then return
  closeWsSlot env slotKey; let sid ← nextWsId env; let poolKey := poolKey?.getD s!"e:{sid}"
  let sub : WsSub Msg := { subId := sid, mode, reconnect := rec, onStatus }
  env.state.modify fun st =>
    let pool := st.wsPools[poolKey]?.getD { url, isBinary, isMux }
    { st with wsSlot := st.wsSlot.insert slotKey (sid, poolKey), wsPools := st.wsPools.insert poolKey { pool with subs := pool.subs.insert sid sub } }
  emit env (onStatus .connecting)
  if let some pool' := (← env.state.get).wsPools[poolKey]? then
    if pool'.subs.contains sid then
      if pool'.isOpen then
        if let (.mux ch params _ _, some cid) := (mode, pool'.connId) then Dom.wsSendBytes cid (WsMuxFrame.encode (.sub sid ch params))
      else if pool'.connId.isNone then openPoolConn env poolKey

private def renderModel : IO Unit := do
  let st ← env.state.get
  match st.vstate with
  | none =>
      let existing ← Dom.appRoot
      let (node, vst) ← if existing != (0 : Dom.Node) then Prod.mk existing <$> hydrateView env.handlers env.app.template st.model existing
        else do let r ← buildView env.handlers "" env.app.template st.model; Dom.mountRoot r.1; pure r
      env.state.modify fun s => { s with root := node, vstate := some vst }
  | some vst =>
      let vst' ← patchView env.handlers st.root 0 env.app.template st.model vst
      env.state.modify fun s => { s with vstate := some vst' }
  for (k, inst) in (← env.localCtx.instances.get).toList do
    unless (← Dom.isConnected inst.host) do env.localCtx.instances.modify (·.erase k); env.localCtx.store.modify (·.erase k)
private def performHttp (cb : HttpCb Msg) (send : UInt32 → IO Unit) : IO Unit := do
  let id ← allocCbId env
  let tid? ← if env.httpTimeoutMs == 0 then pure none else setTimer env s!"http:{id}" none (some (env.httpTimeoutMs, do
    if let some (f, _) ← env.state.modifyGet fun st => (st.httpCb[id]?, { st with httpCb := st.httpCb.erase id }) then
      Dom.effect "http.abort" (toString id) "" ""
      emit env (f.elim (· (.error "request timeout")) (· (.error "request timeout")))))
  env.state.modify fun st => { st with httpCb := st.httpCb.insert id (cb, tid?) }; send (UInt32.ofNat id)
private def performLeaf : Cmd Msg → IO Unit
  | .none | .batch _ => pure ()
  | .stream url body onChunk onDone => do
      let id ← env.state.modifyGet fun st => (st.streams.size, { st with streams := st.streams.push (onChunk, onDone, "") })
      let u := UInt32.ofNat id; Dom.fetchStream url body u u
  | .now onNow => do if let some d := Qed.Date.parse? (← Dom.today) then emit env (onNow d)
  | .request method url body onResult => performHttp env (.inl onResult) (Dom.httpSend method url body)
  | .requestBytes method url body onResult => performHttp env (.inr onResult) (Dom.httpSendBytes method url body)
  | .pushPath url => do Dom.pushPath url.raw; if let some f := env.app.onUrlChange then emit env (f url.raw)
  | .port name payload => Dom.portSend name payload
  | .wsMuxSub slot url channel params rec onJoin onMessage onStatus =>
      openWsSub env ("m:" ++ slot) (some ("m:" ++ url)) url true true rec (.mux channel params onJoin onMessage) onStatus
  | .wsMuxSend slot payload => withOpenSlot env ("m:" ++ slot) fun cid sid => Dom.wsSendBytes cid (WsMuxFrame.encode (.send sid payload))
  | .wsMuxUnsub slot => closeWsSlot env ("m:" ++ slot)
  | .wsExtOpen slot url isBinary rec onJoin onText onBytes onStatus =>
      openWsSub env ("e:" ++ slot) none url isBinary false rec (.ext onJoin onText onBytes) onStatus
  | .wsExtSendText slot text => withOpenSlot env ("e:" ++ slot) fun cid _ => Dom.wsSendText cid text
  | .wsExtSendBytes slot payload => withOpenSlot env ("e:" ++ slot) fun cid _ => Dom.wsSendBytes cid payload
  | .wsExtClose slot => closeWsSlot env ("e:" ++ slot)
  | .fx kind a b c => Dom.effect kind a b c
  | .fxResult kind a b onResult => do
      let id ← allocCbId env; env.state.modify fun st => { st with effectCb := st.effectCb.insert id fun r => emit env (onResult r) }
      Dom.effectResult kind a b (UInt32.ofNat id)
-- Removing a focused node during patch fires `blur` synchronously; queue re-entrant dispatches until render finishes.
private def dispatchMsg (msg : Msg) : IO Unit := do
  if (← env.state.get).rendering then env.state.modify fun st => { st with pending := st.pending.push msg }
  else
    let step (m : Msg) : IO Unit := do
      let (m', cmd) := env.app.update (← env.state.get).model m
      env.state.modify fun st => { st with model := m', rendering := true }
      try renderModel env finally env.state.modify fun st => { st with rendering := false }
      (Cmd.flatten cmd).forM (performLeaf env)
    let rec drain : Nat → IO Unit
      | 0 => pure ()
      | fuel + 1 => do
          let queued ← env.state.modifyGet fun st => (st.pending, { st with pending := #[] })
          if !queued.isEmpty then
            for qm in queued do step qm
            drain fuel
    step msg; drain 1024
private def handleHttpResp (id : UInt32) (res : Sum (Except String String) (Except String ByteArray)) : IO Unit := do
  let n := id.toNat
  if let some (cb, tid?) ← env.state.modifyGet fun st => (st.httpCb[n]?, { st with httpCb := st.httpCb.erase n }) then
    if tid?.isSome then discard <| setTimer env s!"http:{n}" tid?
    match cb, res with
    | .inl f, .inl r => dispatchMsg env (f r) | .inr f, .inr r => dispatchMsg env (f r) | _, _ => pure ()

private def withActivePool (cid : UInt32) (erase : Bool := false) (f : String → WsPool Msg → IO Unit) : IO Unit := do
  let key? ← if erase then env.state.modifyGet fun s => (s.wsConnOwner[cid]?, { s with wsConnOwner := s.wsConnOwner.erase cid })
             else pure (← env.state.get).wsConnOwner[cid]?
  if let some poolKey := key? then
    if let some pool := (← env.state.get).wsPools[poolKey]? then
      if pool.connId == some cid then f poolKey pool
private def handleWsOpen (cid : UInt32) : IO Unit :=
  withActivePool env cid false fun poolKey pool => do
    let resetSubs := pool.subs.fold (init := ∅) fun acc sid sub => acc.insert sid (resetSub sub)
    putPool env poolKey { pool with isOpen := true, subs := resetSubs }
    for (_, sub) in resetSubs.toList do
      match sub.mode with
      | .mux ch params _ _ => Dom.wsSendBytes cid (WsMuxFrame.encode (.sub sub.subId ch params))
      | .ext onJoin _ _    => dispatchMsg env (sub.onStatus .connected); dispatchMsg env (onJoin ())
private def handleWsBytes (cid : UInt32) (bytes : ByteArray) : IO Unit :=
  withActivePool env cid false fun poolKey pool => do
    if !pool.isMux then
      for (_, sub) in pool.subs.toList do if let .ext _ _ onBytes := sub.mode then dispatchMsg env (onBytes bytes)
      return
    let updSub (sid : UInt32) (f : WsSub Msg → Std.HashMap UInt32 (WsSub Msg) → Std.HashMap UInt32 (WsSub Msg)) (st : SocketStatus) : IO (Option (WsSub Msg)) := do
      let some sub := pool.subs[sid]? | return none
      putPool env poolKey { pool with subs := f sub pool.subs }; dispatchMsg env (sub.onStatus st); return some sub
    match WsMuxFrame.decode bytes with
    | .ok (.joinOk sid snap) =>
        if let some sub ← updSub sid (fun s m => m.insert sid (resetSub s)) .connected then
          if let .mux _ _ onJoin _ := sub.mode then dispatchMsg env (onJoin snap)
    | .ok (.event sid payload) =>
        if let some sub := pool.subs[sid]? then if let .mux _ _ _ onMsg := sub.mode then dispatchMsg env (onMsg payload)
    | .ok (.err sid msg) => discard <| updSub sid (fun _ m => m.erase sid) (.failed msg)
    | .ok (.closed sid _) => discard <| updSub sid (fun _ m => m.erase sid) .disconnected
    | _ => pure ()
private def handleWsClose (cid : UInt32) (err : String) (nowMs : Nat) : IO Unit :=
  withActivePool env cid true fun poolKey pool => do
    if !err.isEmpty then
      dropPool env poolKey pool
      for (_, sub) in pool.subs.toList do dispatchMsg env (sub.onStatus (.failed err))
      return
    let (keptSubs, statusMsgs, minDelay?) := pool.subs.fold (init := ((∅ : Std.HashMap UInt32 (WsSub Msg)), (#[] : Array Msg), (none : Option Nat)))
      fun (kept, msgs, md?) sid sub =>
        if sub.pendingRetry && nowMs < sub.nextAtMs then
          let rem := sub.nextAtMs - nowMs; (kept.insert sid sub, msgs, some (md?.elim rem (min · rem)))
        else match sub.reconnect.nextDelayMs sub.attempt with
          | none => (kept, msgs.push (sub.onStatus (wsClosedStatus sub.reconnect)), md?)
          | some d =>
              let sub' := { sub with attempt := sub.attempt + 1, pendingRetry := pool.isMux, nextAtMs := nowMs + d }
              (kept.insert sid sub', msgs.push (sub.onStatus (.reconnecting sub'.attempt)), some (md?.elim d (min · d)))
    if keptSubs.isEmpty then dropPool env poolKey pool
    else
      let tid? ← setTimer env ("ws:" ++ poolKey) pool.timerId (some (minDelay?.getD 0, openPoolConn env poolKey))
      putPool env poolKey { pool with connId := none, isOpen := false, timerId := tid?, subs := keptSubs }
    for m in statusMsgs do dispatchMsg env m
end RuntimeOps

def runWithHttpTimeout (app : App Model Msg) (httpTimeoutMs : Nat) : IO Unit := do
  let state ← IO.mkRef ({ model := app.init.1 } : RuntimeState Model Msg)
  let localCtx : LocalCtx := { registry := app.locals.foldl (fun m d => m.insert d.id d) ∅, store := ← IO.mkRef ∅, instances := ← IO.mkRef ∅ }
  let handlers ← Handlers.mkNew fun k c i p b hn => localMountRoot localCtx (fun m => do (← state.get).dispatch m) k c i p b hn
  let env : RuntimeEnv Model Msg := { app, httpTimeoutMs, state, localCtx, handlers }
  state.modify fun s => { s with dispatch := dispatchMsg env }
  let runCmd (c : Cmd Msg) := (Cmd.flatten c).forM (performLeaf env)
  let withLocal (fk : String) (f : LocalInstance → IO Unit) : IO Unit := do
    if let some inst := (← localCtx.instances.get)[fk]? then f inst
  runtimeRef.set (some {
    mount := do
      if !app.styles.isEmpty then Dom.effect "css.inject" (renderStyleSheet app.styles) "" ""
      let st ← Dom.appState
      let boot (c : Cmd Msg) : IO Unit := do state.modify fun s => { s with wsBooted := true }; runCmd c
      match (if st.isEmpty then none else app.rehydrate st) with
      | some m => state.modify fun s => { s with model := m }; renderModel env; boot (.batch [app.init.2.clientOnly, app.onHydrate m])
      | none =>
          match app.onUrlChange with | some f => dispatchMsg env (f (← Dom.currentPath)) | none => renderModel env
          runCmd app.init.2; boot (app.onHydrate (← state.get).model)
    dispatch := fun id => do
      match (← handlers.click.get)[id.toNat]? with | some msg => dispatchMsg env msg | none => IO.eprintln s!"qed: unknown click id {id}"
    dispatchStr := dispatchStrWithRows handlers.input handlers.rowEv (dispatchMsg env)
    streamChunk := fun cid rawChunk => do
      let n := cid.toNat
      if let some (f, done, buf) := (← state.get).streams[n]? then
        let (events, rem) := parseSseBuffer (buf ++ rawChunk)
        state.modify fun s => { s with streams := s.streams.setIfInBounds n (f, done, rem) }
        for ev in events do dispatchMsg env (f ev)
    streamDone := fun did => do
      let n := did.toNat
      if let some (f, msg, _) := (← state.get).streams[n]? then
        state.modify fun s => { s with streams := s.streams.setIfInBounds n (f, msg, "") }; dispatchMsg env msg
    httpDone := fun id ok text => handleHttpResp env id (.inl (if ok then .ok text else .error text))
    httpBytesDone := fun id ok bytes => handleHttpResp env id (.inr (if ok then .ok bytes else .error ((String.fromUTF8? bytes).getD "RPC transport error")))
    urlChanged := fun path => do if let some f := app.onUrlChange then dispatchMsg env (f path)
    localDispatch := fun fk id => withLocal fk fun inst => do
      if let some lm := (← inst.handlers.click.get)[id.toNat]? then localRun localCtx fk inst lm
    localDispatchStr := fun fk id s => withLocal fk fun inst => dispatchStrWithRows inst.handlers.input inst.handlers.rowEv (localRun localCtx fk inst) id s
    snapshot := do return Json.render (.obj ((← localCtx.store.get).toList.map fun (k, v) => (k, .str v)))
    restore := fun s => do
      if let .ok (.obj members) := Json.parse s then
        for (k, v) in members do if let .str st := v then localCtx.store.modify (·.insert k st)
        for (k, _) in (← localCtx.instances.get).toList do withLocal k fun inst => do localRerender inst ((← localCtx.store.get).getD k "")
    dehydrate := do return app.dehydrate (← state.get).model
    effectDone := fun id result => do
      if let some act ← state.modifyGet fun s => (s.effectCb[id.toNat]?, { s with effectCb := s.effectCb.erase id.toNat }) then act result
    portRecv := fun nm payload => do if let some f := app.onPort then if let some m := f nm payload then dispatchMsg env m
    wsOpen := handleWsOpen env
    wsBytes := handleWsBytes env
    wsText := fun cid text => withActivePool env cid false fun _ pool => do
      if !pool.isMux then for (_, sub) in pool.subs.toList do if let .ext _ onText _ := sub.mode then dispatchMsg env (onText text)
    wsClose := handleWsClose env
  })

def run (app : App Model Msg) : IO Unit := runWithHttpTimeout app defaultHttpTimeoutMs
end Qed
