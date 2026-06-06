/-
  Qed.Runtime — The Elm Architecture core (pure, no FFI).

  An `App` is three pure, total pieces. Because they are ordinary Lean functions
  they are total by elaboration — no panics, no missed cases, no infinite render
  loops — and they are exactly the surface a developer reasons (and proves) about.

  Rendering is *also* pure: `renderNode` turns a typed `Html` into an HTML string
  plus a table mapping event-ids to messages. Nothing here touches the DOM, so
  this module links on every target; the impure driver lives in `Qed.Driver`.
-/
import Qed.Html
import Qed.Date
import Qed.Json
import Qed.Render
import Qed.View
import Qed.Router

namespace Qed

/-- An effect described as *data*, interpreted by the driver after an update so
    that `update` itself stays pure and total. `stream` POSTs `body` to `url` and
    feeds each streamed chunk to `onChunk`, then fires `onDone`. -/
inductive Cmd (msg : Type) where
  /-- Do nothing. -/
  | none
  /-- POST `body` to `url`; dispatch `onChunk c` for each streamed chunk `c`,
      then `onDone` when the stream ends. -/
  | stream (url : String) (body : String) (onChunk : String → msg) (onDone : msg)
  /-- Read the current local date from the clock and dispatch `onNow today`. Use it
      at startup to thread "today" into the model for relative date rules. -/
  | now (onNow : Date → msg)
  /-- Send an HTTP request (`method` `url` with `body`) and dispatch `onResult`
      with the response text, or an error message if the request failed or returned
      a non-2xx status. The typed `Cmd.getJson`/`Cmd.postJson` wrap this with a
      `Qed.Json` decode. -/
  | request (method url body : String) (onResult : Except String String → msg)
  /-- Push `path` to the browser URL (no reload) and route to it. Use for
      programmatic navigation; internal `link`s navigate on their own. -/
  | pushUrl (path : String)
  /-- Run several effects from one message. `update` returns a single `Cmd`, so this
      is how a transition requests more than one effect at once. -/
  | batch (cmds : List (Cmd msg))
  /-- Send `payload` to the JS port handler named `name` (`globalThis.__qed.ports[name]`).
      The userland escape hatch: an app wires any browser API (WebSocket, IndexedDB,
      …) in its own JS, and the pure core talks to it over `(name, payload)` strings —
      so a new effect never means patching the framework. Inbound goes through
      `App.onPort`. See also `Cmd.port`'s typed cousins below. -/
  | port (name payload : String)
  /-- A generic fire-and-forget native effect: the JS host runs the operation `kind`
      with up to three string arguments. The typed effects below (`storageSet`, `copy`,
      `focus`, …) are thin wrappers; this carrier keeps the core from growing a
      constructor per effect. -/
  | fx (kind a b c : String)
  /-- A generic native effect that returns a string result: the host runs `kind` with
      two arguments, then dispatches `onResult result`. Backs `storageGet`, `paste`,
      `after`, `randomInt`, `pickFile`, … -/
  | fxResult (kind a b : String) (onResult : String → msg)
  /-- Open a WebSocket to `url`, addressed by `key` (so later `wsSend`/`wsClose` find
      it). Its lifecycle dispatches messages: `onMessage data` for each frame, and the
      optional `onOpen`/`onClose`/`onError data`. Like `stream`, the callbacks are
      persistent — they fire for the life of the connection, not once. A `url` beginning
      with `/` is resolved against the page origin (`ws://`/`wss://` to match the scheme).
      Use `Cmd.wsOpen`/`Cmd.wsSend`/`Cmd.wsClose` below rather than this constructor. -/
  | socket (key url : String) (onMessage : String → msg)
           (onOpen : Option msg) (onClose : Option msg) (onError : Option (String → msg))

/-! Relabel the messages an effect will produce (functoriality in `msg`). -/
mutual
def Cmd.map (f : α → β) : Cmd α → Cmd β
  | .none                      => .none
  | .stream u b onChunk onDone => .stream u b (fun c => f (onChunk c)) (f onDone)
  | .now onNow                 => .now (fun d => f (onNow d))
  | .request m u b onResult    => .request m u b (fun r => f (onResult r))
  | .pushUrl p                 => .pushUrl p
  | .batch cmds                => .batch (Cmd.mapList f cmds)
  | .port n p                  => .port n p
  | .fx k a b c                => .fx k a b c
  | .fxResult k a b onResult   => .fxResult k a b (fun s => f (onResult s))
  | .socket key url onMsg onOpen onClose onErr =>
      .socket key url (fun d => f (onMsg d)) (onOpen.map f) (onClose.map f)
              (onErr.map (fun g d => f (g d)))
/-- Relabel each effect in a batch (mutual recursion gives termination). -/
def Cmd.mapList (f : α → β) : List (Cmd α) → List (Cmd β)
  | []      => []
  | c :: cs => Cmd.map f c :: Cmd.mapList f cs
end

mutual
/-- Expand nested `batch`es into a flat list of leaf effects, so the driver can run
    them with a simple non-recursive interpreter. -/
def Cmd.flatten : Cmd msg → List (Cmd msg)
  | .batch cmds => Cmd.flattenList cmds
  | c           => [c]
/-- Flatten each effect in a list (mutual recursion gives termination). -/
def Cmd.flattenList : List (Cmd msg) → List (Cmd msg)
  | []      => []
  | c :: cs => Cmd.flatten c ++ Cmd.flattenList cs
end

/-- Decode an HTTP response with `Qed.Json` + `FromJson`, routing a successful
    decode to `onOk` and any transport/parse/decode error to `onErr`. -/
def httpDecode [FromJson α] (onOk : α → msg) (onErr : String → msg) :
    Except String String → msg
  | .error e   => onErr e
  | .ok   body => match (Json.parse body).bind FromJson.fromJson with
                  | .ok a    => onOk a
                  | .error e => onErr e

/-- GET `url`, decode the JSON body into `α`, and dispatch `onOk`/`onErr`. -/
def Cmd.getJson [FromJson α] (url : String) (onOk : α → msg) (onErr : String → msg) : Cmd msg :=
  .request "GET" url "" (httpDecode onOk onErr)

/-- POST `body` to `url`, decode the JSON response into `α`, dispatch `onOk`/`onErr`. -/
def Cmd.postJson [FromJson α] (url body : String) (onOk : α → msg) (onErr : String → msg) : Cmd msg :=
  .request "POST" url body (httpDecode onOk onErr)

/-! ### Native effects — typed wrappers over `fx`/`fxResult`

Common browser effects as ordinary `Cmd`s an app returns from `update`/`effects`. Each
is a one-line smart constructor over the generic carrier, so the core grows API, not
constructors-and-driver-arms. For anything not covered, `Cmd.port` reaches userland JS. -/

/-! **localStorage.** `storageGet` decodes the host's JSON (`"value"` or `null`). -/
def Cmd.storageSet    (key value : String) : Cmd msg := .fx "storage.set" key value ""
def Cmd.storageRemove (key : String)       : Cmd msg := .fx "storage.remove" key "" ""
def Cmd.storageClear                       : Cmd msg := .fx "storage.clear" "" "" ""
def Cmd.storageGet (key : String) (onValue : Option String → msg) : Cmd msg :=
  .fxResult "storage.get" key "" fun s =>
    onValue (match (Json.parse s).toOption with | some (.str v) => some v | _ => Option.none)

/-! **Navigation** (`pushUrl` above pushes+routes; these re-route through the host). -/
def Cmd.replaceUrl (path : String) : Cmd msg := .fx "history.replace" path "" ""
def Cmd.back    : Cmd msg := .fx "history.back" "" "" ""
def Cmd.forward : Cmd msg := .fx "history.forward" "" "" ""

/-! **Clipboard.** -/
def Cmd.copy  (text : String)         : Cmd msg := .fx "clipboard.write" text "" ""
def Cmd.paste (onText : String → msg) : Cmd msg := .fxResult "clipboard.read" "" "" onText

/-! **Focus / scroll**, addressing an element by its `id`. -/
def Cmd.focus          (elementId : String) : Cmd msg := .fx "dom.focus" elementId "" ""
def Cmd.blur           (elementId : String) : Cmd msg := .fx "dom.blur" elementId "" ""
def Cmd.select         (elementId : String) : Cmd msg := .fx "dom.select" elementId "" ""
def Cmd.scrollIntoView (elementId : String) : Cmd msg := .fx "dom.scrollIntoView" elementId "" ""

/-! **Timer.** Dispatch `msg` after `ms` milliseconds (`setTimeout`). -/
def Cmd.after (ms : Nat) (onTick : msg) : Cmd msg := .fxResult "timer.after" (toString ms) "" fun _ => onTick

/-- A timer identified by `key`: scheduling a new one cancels the pending one with the
    same key, and `Cmd.cancel key` drops it. Debounce is one line — schedule
    `afterKeyed "search" 300 …` on every keystroke and only the last survives. -/
def Cmd.afterKeyed (key : String) (ms : Nat) (onTick : msg) : Cmd msg :=
  .fxResult "timer.afterKeyed" key (toString ms) fun _ => onTick

/-- Cancel a pending `afterKeyed` timer by its key (a no-op if none is pending). -/
def Cmd.cancel (key : String) : Cmd msg := .fx "timer.cancel" key "" ""

/-! **Document title.** -/
def Cmd.setTitle (title : String) : Cmd msg := .fx "document.title" title "" ""

/-! **Randomness** — `update` is pure, so a random draw must come from an effect.
    Dispatches a uniform integer in `[lo, hi]`. -/
def Cmd.randomInt (lo hi : Int) (onInt : Int → msg) : Cmd msg :=
  .fxResult "random.int" (toString lo) (toString hi) fun s => onInt ((s.toInt?).getD lo)

/-! **WebSockets.** A connection is addressed by a `key` you choose; open it once, then
    `wsSend`/`wsClose` it by that key. Inbound frames and lifecycle events arrive as
    messages, so the socket lives behind the same pure `update` as everything else. -/

/-- Open a WebSocket to `url` under `key`, routing each inbound frame to `onMessage`.
    `onOpen`/`onClose`/`onError` are optional lifecycle messages. A `url` starting with
    `/` is resolved against the page origin (scheme `ws`/`wss` follows `http`/`https`). -/
def Cmd.wsOpen (key url : String) (onMessage : String → msg)
    (onOpen : Option msg := Option.none) (onClose : Option msg := Option.none)
    (onError : Option (String → msg) := Option.none) : Cmd msg :=
  .socket key url onMessage onOpen onClose onError

/-- Send `data` on the socket opened under `key` (dropped if it isn't open). -/
def Cmd.wsSend (key data : String) : Cmd msg := .fx "ws.send" key data ""

/-- Close the socket opened under `key` (a no-op if there is none). -/
def Cmd.wsClose (key : String) : Cmd msg := .fx "ws.close" key "" ""

/-! **Files.** `download` saves `content` as a file; `pickFile` opens the OS picker and
    reads the chosen file's text. -/
def Cmd.download (filename mime content : String) : Cmd msg := .fx "file.download" filename mime content

/-! A file the user picked, read as text. Binary needs a data-URL variant or a port.
    Decoded by hand (not the `schema` command, which lives above this layer). -/
structure FilePick where
  name : String
  mime : String
  size : Nat
  text : String

instance : FromJson FilePick where
  fromJson j := do
    return { name := (← fromField j "name"), mime := (← fromField j "mime"),
             size := (← fromField j "size"), text := (← fromField j "text") }

def FilePick.decode (s : String) (maxDepth : Nat := 64) : Except String FilePick :=
  (Json.parse s maxDepth).bind fromJson

/-- Open the file picker (filtered by `accept`, e.g. `".json,text/*"`) and dispatch the
    chosen file decoded as a `FilePick` — or `.error` if it was cancelled or unreadable. -/
def Cmd.pickFile (accept : String) (onFile : Except String FilePick → msg) : Cmd msg :=
  .fxResult "file.pick" accept "" fun s => onFile (FilePick.decode s)

/-- Find the handler for an inbound port `name` and decode its payload. The `ports`
    command builds the handler array; an app wires it up as `onPort := some onPort`. -/
def dispatchPorts (handlers : Array (String × (String → Option msg))) (name payload : String) : Option msg :=
  match handlers.find? (fun h => h.1 == name) with
  | some h => h.2 payload
  | none   => none

/-! ### The `ports` command — typed userland effects, no strings or codecs by hand

`ports where …` declares typed message channels between the pure app and its own JS. A
channel with **no** `=>` is *outbound* — it generates a `Cmd` constructor that serializes
its payload. One **with** `=> ctor` is *inbound* — its payload is decoded and mapped to a
message, and all the inbound channels are assembled into a generated `onPort`:

    ports where
      wsSend : Command             -- outbound: `wsSend (c : Command) : Cmd msg`
      wsRecv : Event => .received   -- inbound:  "wsRecv" payload decoded into `Msg.received`

    def app := application init update view (onPort := some onPort)

The JS registers handlers on `globalThis.__qed.ports[name]` and pushes inbound with
`globalThis.__qed.send(name, payload)`. Payload types need `ToJson` (outbound) /
`FromJson` (inbound) — a `schema` gives both. -/
syntax portChan := ident " : " term (" => " term)?
syntax (name := portsCmd) "ports " "where " sepBy1IndentSemicolon(portChan) : command

open Lean in
macro_rules
  | `(ports where $[$chans:portChan]*) => do
      let mut outDefs  : Array (TSyntax `command) := #[]
      let mut inTuples : Array (TSyntax `term) := #[]
      for ch in chans do
        -- `__`-prefixed names are reserved for the framework's own channels (e.g. `__ws`,
        -- which carries WebSocket events); reject them so an app channel can't be hijacked.
        if let some nm := (ch.raw.find? (·.isIdent)).map (·.getId.toString) then
          if nm.startsWith "__" then
            Macro.throwErrorAt ch s!"ports: channel name '{nm}' is reserved (names starting with `__`)"
        match ch with
        | `(portChan| $name:ident : $ty:term => $rhs:term) =>
            -- inbound: ("name", fun p => (fromJson-decoded payload).map ctor)
            inTuples := inTuples.push (← `(($(quote name.getId.toString),
              fun p => (((Json.parse p).bind FromJson.fromJson : Except String $ty).toOption).map $rhs)))
        | `(portChan| $name:ident : $ty:term) =>
            -- outbound: a Cmd that serializes its payload onto the named port
            outDefs := outDefs.push (←
              `(def $name {m : Type} (x : $ty) : Cmd m :=
                  Cmd.port $(quote name.getId.toString) (Json.render (ToJson.toJson x))))
        | _ => Macro.throwErrorAt ch "ports: expected `name : Type` (outbound) or `name : Type => ctor` (inbound)"
      let onPortDef ← `(def $(mkIdent `onPort) : String → String → Option $(mkIdent `Msg) :=
        dispatchPorts #[$inTuples,*])
      return mkNullNode ((outDefs.push onPortDef).map (·.raw))

/-! ### Local-state components (React `useState`, keyed)

A *local* component owns state the parent never declares: the driver keeps it in a
keyed store, addressed by an explicit key (not React's fragile call-order). To stay
off the verified virtual DOM — so `Html.map`/`diff` never recurse into it and remain
total — a local component's typed `view`/`update` are erased here behind a string
boundary. The child's **state** is serialized (`ToJson`/`FromJson`); its **message**
type stays internal (wired by the driver), so it needs no codec. A child may emit a
typed **output** that the host's `bubble` maps to a parent message (`localMountWith`),
the one type-safe channel from a self-contained child back to the root `update`. -/

/-- A child message, erased to its effect on serialized state. `run currentState`
    yields the next serialized state and an optional serialized output to bubble up. -/
structure LocalMsg where
  run : String → String × Option String

/-- A registered local component, type-erased over its state/message/output. `view`
    decodes the stored state, renders the child, and replaces each child message with
    its erased `LocalMsg`. Lives as pure data in `App.locals`; the driver gives it a
    keyed store and its own event tables. Build one with `LocalDef.of`/`.ofSimple`. -/
structure LocalDef where
  /-- The registry id referenced by `localMount component …`. -/
  id   : String
  /-- The serialized initial state, used the first time an instance key is seen. -/
  init : String
  /-- Render the child from serialized state, messages erased to `LocalMsg`. -/
  view : String → Html LocalMsg

/-- A self-contained application: an initial (model, startup effect), a transition that may
    request effects, and a `View` template. The runtime always renders through the template
    (one engine); `App.view` below is its `View.render`, the spec the fine-grained driver is
    checked against. Build one with `ui`. -/
structure App (Model : Type) (Msg : Type) where
  /-- The initial model and the effect to run on start. -/
  init   : Model × Cmd Msg
  /-- The pure, total state transition, optionally requesting an effect. -/
  update : Model → Msg → Model × Cmd Msg
  /-- The view as a fine-grained template: built once, then only the bindings whose projection
      changed are patched. The `ui` builder lifts an ordinary `fun m => …` view into this. -/
  template : View Model Msg
  /-- If set, the message to fire when the browser URL changes (the new path is the argument) —
      at startup, on `link` clicks, on back/forward, and after `Cmd.pushUrl`. The routed `ui`
      builder sets it from a typed `onRoute : R → Msg`. -/
  onUrlChange : Option (String → Msg) := none
  /-- Local components (`useState`-style) this app embeds, registered by id. The driver installs
      them and routes their events to a per-instance keyed store. Empty for apps that use none. -/
  locals : List LocalDef := []
  /-- Inbound ports: when the app's JS calls `globalThis.__qed.send(name, payload)`, this turns
      it into a message (or `none` to ignore). The subscription side of `Cmd.port`. -/
  onPort : Option (String → String → Option Msg) := none
  /-- Serialize the model into the server-rendered page (SSR), so the client starts from the
      *same* model the server drew instead of re-deriving and refetching — no flash, no reload of
      data already on the page. Default `""` means "don't dehydrate" (the client starts from `init`
      / the URL). Pair with `rehydrate`; an app whose `Model` has `ToJson`/`FromJson` can use
      `Json.render ∘ toJson`. -/
  dehydrate : Model → String := fun _ => ""
  /-- Rebuild the model from the string `dehydrate` embedded. `none` (or absent state) falls back
      to the normal startup. When it returns `some`, the client adopts that model directly and does
      not re-route on mount, so the first client render equals the server's. -/
  rehydrate : String → Option Model := fun _ => none

/-- The app's view: its template rendered against the model. Server (SSR) and the fine-grained
    client driver are both checked against this one function, so they cannot drift. -/
def App.view (app : App Model Msg) (m : Model) : Html Msg := View.render app.template m

/-! ### Transitions

`update` returns the next model, optionally with an effect. A pure app's arms are ordinary
`{ m with … }` (it returns `Model`); an effectful app's arms pair the model with a `Cmd` using
the two helpers — so the effect sits next to the state change that triggers it:

    transition m
      | .typed s => still { m with draft := s }
      | .send    => also { m with pending := true } (Cmd.stream url body .chunk .done)

The `ToStep` class lets the one builder (`ui`) accept *either* return type, so there is no
pure-vs-effectful builder choice. -/

/-- A transition arm with no effect. -/
def still (m : Model) : Model × Cmd Msg := (m, .none)
/-- A transition arm that also runs `cmd` after the update. -/
def also (m : Model) (cmd : Cmd Msg) : Model × Cmd Msg := (m, cmd)

/-- A transition result the builder can normalise to `(model, cmd)`: either a bare next `Model`
    (no effect) or an explicit `Model × Cmd Msg`. The two instances never overlap (`Model` vs
    `Model × Cmd Msg`), so which one applies is determined by `update`'s return type. -/
class ToStep (Model : Type) (Msg : Type) (α : Type) where
  toStep : α → Model × Cmd Msg
instance : ToStep Model Msg Model := ⟨fun m => (m, .none)⟩
instance : ToStep Model Msg (Model × Cmd Msg) := ⟨id⟩

/-- Construct an `App` from `init`, an `update` (returning `Model` or `Model × Cmd Msg` via
    `ToStep`), and a `View` template. The `ui` builder is the front door; call this directly only
    to pass a pre-built template — a reused `view%` fragment, or `View.ofHtml` over an `Html`
    view. -/
def mkApp [ToStep Model Msg α] (init : Model) (update : Model → Msg → α)
    (template : View Model Msg) (start : Cmd Msg := .none) (locals : List LocalDef := [])
    (onPort : Option (String → String → Option Msg) := none) : App Model Msg :=
  { init := (init, start), update := fun m msg => ToStep.toStep (update m msg),
    template, locals, onPort }

/-- `mkApp` for a URL-routed app: `onRoute` is fired with the *parsed* route on every URL change
    (an unknown URL falls back to `default`, hence `[Inhabited R]`), so the app never re-parses
    the path or annotates the route type. -/
def mkRoutedApp {R : Type} [Router R] [Inhabited R] [ToStep Model Msg α]
    (init : Model) (update : Model → Msg → α) (template : View Model Msg)
    (onRoute : R → Msg) (start : Cmd Msg := .none) (locals : List LocalDef := [])
    (onPort : Option (String → String → Option Msg) := none) : App Model Msg :=
  { mkApp init update template start locals onPort with
    onUrlChange := some (fun p => onRoute ((Router.fromURL p).getD default)) }

/-! ### The `ui` builder — the one way to build an app

`ui init update fun m => <view>` builds the whole `App`. `update` may return `Model` (pure) or
`Model × Cmd Msg` (effectful, via `still`/`also`). The view is written inline and lifted to a
fine-grained template — no `view%` by hand. Capabilities are optional args, in any order, before
the `fun`:

    ui init update fun m => …                                   -- pure
    ui init transition (onRoute := Msg.route) fun m => …        -- routed (needs a `router`)
    ui init transition (start := Cmd.now .today) fun m => …
    ui init update (locals := [w.reg]) (onPort := some onPort) fun m => …

For a reused/pre-built template, call `mkApp`/`mkRoutedApp` with a `view%` fragment or
`View.ofHtml`. Core-syntax only (no `import Lean`): quotations over the existing total `view%`. -/

-- One option `(name := value)`. The name is a generic `ident` (not a keyword), so `onRoute`/
-- `start`/`locals`/`onPort` reserve no tokens; each atom is a single token (`(`, `:=`, `)`).
syntax uiOpt := "(" ident " := " term ")"
syntax (name := uiBuilder) "ui " term:max term:max (uiOpt)* " fun " ident " => " term : term

open Lean in
macro_rules
  | `(ui $init $update $[$opts:uiOpt]* fun $m => $body) => do
      let tmpl ← `(view% fun $m => $body)
      let mut routeE?   : Option (TSyntax `term) := none
      let mut queriesE? : Option (TSyntax `term) := none
      let mut startE  : TSyntax `term ← `(Qed.Cmd.none)
      let mut localsE : TSyntax `term ← `(([] : List Qed.LocalDef))
      let mut portE   : TSyntax `term ← `(none)
      for opt in opts do
        match opt with
        | `(uiOpt| ($name:ident := $e)) =>
            match name.getId with
            | `onRoute => routeE?   := some e
            | `queries => queriesE? := some e
            | `start   => startE  := e
            | `locals  => localsE := e
            | `onPort  => portE   := e
            | _ => Macro.throwErrorAt name s!"ui: unknown option '{name.getId}' (expected onRoute/start/locals/onPort/queries)"
        | _ => pure ()
      let base ← match routeE? with
        | some route =>
            `(Qed.mkRoutedApp $init $update $tmpl (onRoute := $route)
                (start := $startE) (locals := $localsE) (onPort := $portE))
        | none =>
            `(Qed.mkApp $init $update $tmpl (start := $startE) (locals := $localsE) (onPort := $portE))
      -- `queries` (auto-refetch) wraps the finished app's update; absent ⇒ the app unchanged.
      -- `withQueries` lives in `Qed.Resource` (imported by app modules, not by this one), so emit
      -- it with `mkIdent` — a bare quotation would pre-resolve `Qed.App.` as a struct projection
      -- here (where `App` exists but the method does not yet) and never find the real constant.
      match queriesE? with
      | some qs => `($(mkIdent `Qed.App.withQueries) $qs $base)
      | none    => pure base
/-- Register a local component with an output it can bubble to its parent. `update`
    returns the next state and an optional output; the output is serialized and handed
    to the host's `bubble` (see `localMountWith`). The message type `M` needs no codec
    — only the state `S` (round-tripped through the store) and the output `O`. -/
def LocalDef.of {S M O : Type} [ToJson S] [FromJson S] [ToJson O]
    (id : String) (init : S)
    (view : S → Html M) (update : S → M → S × Option O) : LocalDef :=
  let dec : String → S := fun s => ((Json.parse s).bind FromJson.fromJson).toOption.getD init
  { id   := id
    init := Json.render (ToJson.toJson init)
    view := fun s => (view (dec s)).map fun m =>
      { run := fun st =>
          let (s', o) := update (dec st) m
          (Json.render (ToJson.toJson s'), o.map fun x => Json.render (ToJson.toJson x)) } }

/-- Register a local component with no output (a self-contained widget that never
    notifies its parent). Only the state `S` needs a codec. -/
def LocalDef.ofSimple {S M : Type} [ToJson S] [FromJson S]
    (id : String) (init : S) (view : S → Html M) (update : S → M → S) : LocalDef :=
  let dec : String → S := fun s => ((Json.parse s).bind FromJson.fromJson).toOption.getD init
  { id   := id
    init := Json.render (ToJson.toJson init)
    view := fun s => (view (dec s)).map fun m =>
      { run := fun st => (Json.render (ToJson.toJson (update (dec st) m)), none) } }


/-- Mount a registered local component at instance `key`, ignoring any output: a
    self-contained `useState` cell. `key` need only be unique *within* `component`
    (the driver namespaces it by component) and stable across renders. -/
def localMount (component key : String) : Attr msg :=
  .localCell key component none (fun _ => none)

/-- Mount a registered local component at instance `key`, mapping its serialized
    output through `onOut` to an optional parent message — the type-safe way a child
    event reaches the root `update`. -/
def localMountWith {O msg : Type} [FromJson O] (component key : String)
    (onOut : O → Option msg) : Attr msg :=
  .localCell key component none fun s =>
    (((Json.parse s).bind FromJson.fromJson : Except String O)).toOption.bind onOut

/-- Seed THIS instance's initial state from parent data, overriding the component's
    registered default — React's `useState(propValue)`. Compose onto a `localMount`/
    `localMountWith`: `(localMountWith "editor" k onSave).localInit { text := r.text }`.
    It only applies the first time the key is mounted; a later re-render keeps whatever
    the user has since typed (the live state wins, exactly like a `useState` seed). -/
private def attrWithLocalInit {msg : Type} (a : Attr msg) (i : String) : Attr msg :=
  match a with
  | .localCell key comp _ bubble => .localCell key comp (some i) bubble
  | x => x

def Attr.localInit {msg S : Type} [ToJson S] (a : Attr msg) (init : S) : Attr msg :=
  attrWithLocalInit a (Json.render (ToJson.toJson init))

-- The pure `Html` → string renderer (escapeHtml / normalizeAttrs / renderAttr / renderNode /
-- `Html.render`) now lives in `Qed.Render`, below `Qed.View`, so `App` here can carry a `View`.

/-- Render a node to a string, filling each local host with its component's *initial*
    view (looked up in `locals`), so native/server-side output isn't blank where a
    local component will mount. Best-effort and `partial` — a local view is arbitrary
    and may nest — unlike the total `Html.render`. The browser driver rebuilds local
    subtrees on mount (a full `replaceChildren`), so this output never has to round-trip
    or hydrate; it is for first paint and no-JS rendering. -/
partial def renderWithLocals {m : Type} (locals : List LocalDef) : Html m → String
  | .text s => escapeHtml s
  | .lazy _ sub => renderWithLocals locals sub
  | .element tag attrs children =>
      let attrStr := (renderAttrs #[] (normalizeAttrs attrs)).1
      let local?  := attrs.findSome? (fun | .localCell _ comp init _ => some (comp, init) | _ => none)
      let childStr := match local? with
        | some (comp, init?) =>
            match locals.find? (fun d : LocalDef => d.id == comp) with
            | some ldef => renderWithLocals locals (ldef.view (init?.getD ldef.init))
            | none      => ""
        | none => String.join (children.map (renderWithLocals locals))
      s!"<{tag}{attrStr}>{childStr}</{tag}>"

/-- `Html.render`, but local hosts are filled with their initial view (see
    `renderWithLocals`). Pass the app's `locals`. -/
def Html.renderWith (locals : List LocalDef) (h : Html msg) : String := renderWithLocals locals h

/-! ### Server-side rendering

Render the app once on the server with the *same* verified `view`/`render` the browser uses,
emit that HTML into `#app`, and the client mounts over it — so first paint is the real content,
not a spinner, and search engines see the page. Because both sides are the one `view`/`render`,
the server and client output are the same function of the model, not two implementations that
can drift. (The current client mount replaces the server markup — a brief swap; flash-free
adopt-in-place hydration is a later refinement, see README.) -/

/-- The app's view at an arbitrary model as an HTML string — the per-request SSR primitive:
    a server computes the model for the request (route, fetched data) and renders it. -/
def App.renderModel (app : App Model Msg) (m : Model) : String :=
  Html.renderWith app.locals (app.view m)

/-- The app's initial view as an HTML string — its `view` at the initial model, with local
    hosts filled by their initial view. This is what a server emits into `#app`. -/
def App.renderInitial (app : App Model Msg) : String :=
  app.renderModel app.init.1

/-- Wrap rendered `#app` content in a complete static HTML document that loads the transpiled JS
    bundle, which mounts the live app over the pre-rendered markup. A non-empty `state`
    (an app's `dehydrate model`) is embedded in a `#qed-state` script so the client starts
    from the server's model instead of refetching; `</` is broken so the JSON can't close the
    script early (it stays valid JSON — `\/` is `/`). -/
def renderDocument (title : String) (appHtml : String) (script : String := "/qed.js")
    (state : String := "") : String :=
  "<!doctype html>\n<html lang=\"en\">\n<head><meta charset=\"utf-8\">"
    ++ "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">"
    ++ "<title>" ++ escapeHtml title ++ "</title></head>\n"
    ++ "<body><div id=\"app\">" ++ appHtml ++ "</div>\n"
    ++ (if state.isEmpty then ""
        else "<script id=\"qed-state\" type=\"application/json\">" ++ state.replace "</" "<\\/" ++ "</script>\n")
    ++ "<script type=\"module\" src=\"" ++ script ++ "\"></script>\n</body>\n</html>"

end Qed
