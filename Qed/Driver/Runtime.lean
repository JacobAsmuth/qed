import Qed.Driver.Template
import Qed.Driver.Local
import Qed.Runtime.App

namespace Qed

structure SocketHandlers (msg : Type) where
  onMessage : String → msg
  onOpen    : Option msg
  onClose   : Option msg
  onError   : Option (String → msg)

structure Runtime where
  mount            : IO Unit
  dispatch         : UInt32 → IO Unit
  dispatchStr      : UInt32 → String → IO Unit
  streamChunk      : UInt32 → String → IO Unit
  streamDone       : UInt32 → IO Unit
  httpDone         : UInt32 → Bool → String → IO Unit
  urlChanged       : String → IO Unit
  localDispatch    : String → UInt32 → IO Unit
  localDispatchStr : String → UInt32 → String → IO Unit
  snapshot         : IO String
  restore          : String → IO Unit
  effectDone       : UInt32 → String → IO Unit
  portRecv         : String → String → IO Unit

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

def run (app : App Model Msg) : IO Unit := do
  let template  := app.template
  let modelRef  ← IO.mkRef app.init.1
  let vstateRef ← IO.mkRef (none : Option (VState Model Msg))
  let condCells : CondCells Model Msg ← IO.mkRef (#[], #[])
  let rootRef   ← IO.mkRef (0 : Dom.Node)
  let clickRef  ← IO.mkRef (#[] : Array Msg)
  let inputRef  ← IO.mkRef (#[] : Array (String → Msg))
  let chunkCbRef  ← IO.mkRef (#[] : Array (String → Msg))
  let doneCbRef   ← IO.mkRef (#[] : Array Msg)
  let respCbRef   ← IO.mkRef (∅ : Std.HashMap Nat (Except String String → Msg))
  let effectCbRef ← IO.mkRef (∅ : Std.HashMap Nat (String → Msg))
  let cbNextRef   ← IO.mkRef (0 : Nat)
  let socketCbRef ← IO.mkRef (∅ : Std.HashMap String (SocketHandlers Msg))
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
          let vst ← hydrateView h condCells template (← modelRef.get) existing
          rootRef.set existing; vstateRef.set (some vst)
        else
          let (node, vst) ← buildView h condCells "" template (← modelRef.get)
          Dom.mountRoot node; rootRef.set node; vstateRef.set (some vst)
    | some vst => patchView h condCells (← rootRef.get) 0 template (← modelRef.get) vst
    gcLocals
  let performLeaf : Cmd Msg → IO Unit := fun
    | .none => pure ()
    | .stream url body onChunk onDone => do
        let cs ← chunkCbRef.get; chunkCbRef.set (cs.push onChunk)
        let ds ← doneCbRef.get;  doneCbRef.set (ds.push onDone)
        Dom.fetchStream url body (UInt32.ofNat cs.size) (UInt32.ofNat ds.size)
    | .now onNow => do
        match Qed.Date.parse? (← Dom.today) with
        | some d => (← dispatchRef.get) (onNow d)
        | none   => pure ()
    | .request method url body onResult => do
        let id ← cbNextRef.modifyGet (fun n => (n, n + 1))
        respCbRef.modify (·.insert id onResult)
        Dom.httpSend method url body (UInt32.ofNat id)
    | .pushPath path => do
        Dom.pushPath path
        match app.onUrlChange with
        | some f => (← dispatchRef.get) (f path)
        | none   => pure ()
    | .port name payload => Dom.portSend name payload
    | .socket key url onMessage onOpen onClose onError => do
        socketCbRef.modify (·.insert key { onMessage, onOpen, onClose, onError })
        Dom.effect "ws.open" key url ""
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
      while !(← pendingRef.get).isEmpty do
        let queued ← pendingRef.get
        pendingRef.set #[]
        for qm in queued do perform (← applyOne qm)
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
      | some m => modelRef.set m; renderModel
      | none   =>
        match app.onUrlChange with
        | some f => do let p ← Dom.currentPath; dispatchMsg (f p)
        | none   => renderModel
      perform app.init.2
    dispatch := fun id => do
      match (← clickRef.get)[id.toNat]? with
      | some msg => dispatchMsg msg
      | none     => IO.eprintln s!"qed: unknown click id {id}"
    dispatchStr := fun id s => do
      match (← inputRef.get)[id.toNat]? with
      | some f => dispatchMsg (f s)
      | none   => pure ()
    streamChunk := fun cid c => do
      match (← chunkCbRef.get)[cid.toNat]? with
      | some f => dispatchMsg (f c)
      | none   => pure ()
    streamDone := fun did => do
      match (← doneCbRef.get)[did.toNat]? with
      | some msg => dispatchMsg msg
      | none     => pure ()
    httpDone := fun id ok text => do
      match (← respCbRef.get)[id.toNat]? with
      | some f => respCbRef.modify (·.erase id.toNat); dispatchMsg (f (if ok then .ok text else .error text))
      | none   => pure ()
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
  })

end Qed
