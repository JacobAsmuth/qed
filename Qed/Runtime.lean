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

/-- Relabel the messages an effect will produce (functoriality in `msg`). -/
def Cmd.map (f : α → β) : Cmd α → Cmd β
  | .none                      => .none
  | .stream u b onChunk onDone => .stream u b (fun c => f (onChunk c)) (f onDone)
  | .now onNow                 => .now (fun d => f (onNow d))
  | .request m u b onResult    => .request m u b (fun r => f (onResult r))
  | .pushUrl p                 => .pushUrl p

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

/-- A self-contained application: an initial (model, startup effect), a transition
    that may request effects, and a view. A transition returns `(nextModel, cmd)`;
    use `(m, .none)` (or just the pure `sandbox`) when there is no effect. -/
structure App (Model : Type) (Msg : Type) where
  /-- The initial model and the effect to run on start. -/
  init   : Model × Cmd Msg
  /-- The pure, total state transition, optionally requesting an effect. -/
  update : Model → Msg → Model × Cmd Msg
  /-- The pure, total render. -/
  view   : Model → Html Msg
  /-- If set, the message to fire when the browser URL changes (the new path is the
      argument) — at startup, on `link` clicks, on back/forward, and after
      `Cmd.pushUrl`. The app parses the path (e.g. `Router.fromURL`) into its route.
      Left `none` by `sandbox`/`application`; set by `routed`. -/
  onUrlChange : Option (String → Msg) := none

/-- Build an `App` with no side effects (the Elm "sandbox"). -/
def sandbox (init : Model) (update : Model → Msg → Model) (view : Model → Html Msg) :
    App Model Msg :=
  { init := (init, .none), update := fun m msg => (update m msg, .none), view }

/-- Build an `App` whose transitions may request effects (fetch, streaming, …).

    `update` stays pure (`Model → Msg → Model`), so its arms read as ordinary
    `{ m with … }` record updates. Effects are a *separate* function evaluated on
    the **updated** model: `effects m' msg` is the `Cmd` to run after a `msg`
    moved the model to `m'`. It defaults to "no effect", so an app names a `Cmd`
    only for the messages that actually have one.

    (For an effect that needs state the update discards, build the `App` directly:
    its `update : Model → Msg → Model × Cmd Msg` field gives the combined form.) -/
def application (init : Model)
    (update  : Model → Msg → Model)
    (view    : Model → Html Msg)
    (effects : Model → Msg → Cmd Msg := fun _ _ => .none) : App Model Msg :=
  { init   := (init, .none)
    update := fun m msg => let m' := update m msg; (m', effects m' msg)
    view }

/-- Build a URL-routed `App`. Same as `application`, plus `onUrlChange`: the message
    fired with the new path whenever the URL changes (startup, `link` clicks,
    back/forward, `Cmd.pushUrl`). The app parses the path into its route — typically
    `fun path => .urlChanged (Router.fromURL path)`. -/
def routed (init : Model)
    (update      : Model → Msg → Model)
    (view        : Model → Html Msg)
    (onUrlChange : String → Msg)
    (effects     : Model → Msg → Cmd Msg := fun _ _ => .none) : App Model Msg :=
  { init   := (init, .none)
    update := fun m msg => let m' := update m msg; (m', effects m' msg)
    view
    onUrlChange := some onUrlChange }

/-- Escape text/attribute values so model data cannot break out of the markup. -/
def escapeHtml (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ match c with
      | '&'  => "&amp;"
      | '<'  => "&lt;"
      | '>'  => "&gt;"
      | '"'  => "&quot;"
      | '\'' => "&#39;"
      | c    => c.toString

/-- The key an attribute occupies, if any (`onClick` occupies none). -/
def Attr.key? : Attr msg → Option String
  | .attr k _ => some k
  | .flag k _ => some k
  | _         => none

/-- Drop all but the last occurrence of each keyed attribute (last write wins,
    matching `setAttribute`); keyless attributes (`onClick`) are all kept. -/
def dedupAttrs : List (Attr msg) → List (Attr msg)
  | []        => []
  | a :: rest =>
      match a.key? with
      | none   => a :: dedupAttrs rest
      | some k => if rest.any (·.key? == some k) then dedupAttrs rest else a :: dedupAttrs rest

/-- Collapse an attribute list to a canonical form: every `cls` merged into one
    `class`, later values winning for duplicate keys. The string renderer and the
    live DOM driver both apply this, so the markup and the DOM cannot disagree. -/
def normalizeAttrs (attrs : List (Attr msg)) : List (Attr msg) :=
  let classes := (attrs.filterMap (fun | .cls c => some c | _ => none)).filter (· != "")
  let merged  := if classes.isEmpty then [] else [Attr.cls (String.intercalate " " classes)]
  merged ++ dedupAttrs (attrs.filter (fun | .cls _ => false | _ => true))

/-- Render one attribute, threading the handler table. An `onClick` is emitted as
    a `data-qed-click="<id>"` attribute, where `<id>` indexes the message that the
    JS delegation listener will dispatch back. -/
def renderAttr (hs : Array msg) : Attr msg → String × Array msg
  | .cls c     => (s!" class=\"{escapeHtml c}\"", hs)
  | .attr k v  => (s!" {k}=\"{escapeHtml v}\"", hs)
  | .flag k on => (if on then s!" {k}=\"{k}\"" else "", hs)
  | .key _     => ("", hs)   -- a reconciliation key is virtual-DOM-only; it never renders
  | .onClick m => (s!" data-qed-click=\"{hs.size}\"", hs.push m)
  | .onInput _ => ("", hs)   -- no static form; the driver wires input events
  | .onCheck _ => ("", hs)   -- (same — the driver wires checkbox change events)
  | .onKeydown _ => ("", hs) -- (same — driver wires keydown)
  | .onKeyup _   => ("", hs) -- (same — driver wires keyup)
  | .onSubmit m  => (s!" data-qed-submit=\"{hs.size}\"", hs.push m)
  | .onBlur m    => (s!" data-qed-blur=\"{hs.size}\"", hs.push m)
  | .onFocus m   => (s!" data-qed-focus=\"{hs.size}\"", hs.push m)

/-- Render a list of attributes left-to-right, threading the handler table. -/
def renderAttrs (hs : Array msg) : List (Attr msg) → String × Array msg
  | []      => ("", hs)
  | a :: as =>
      let (s1, hs1) := renderAttr hs a
      let (s2, hs2) := renderAttrs hs1 as
      (s1 ++ s2, hs2)

mutual
  /-- Render a node to HTML, accumulating the event-id ↦ message table. Pure and
      total. -/
  def renderNode (hs : Array msg) : Html msg → String × Array msg
    | .text s => (escapeHtml s, hs)
    | .element tag attrs children =>
        let (attrStr,  hs1) := renderAttrs hs (normalizeAttrs attrs)
        let (childStr, hs2) := renderChildren hs1 children
        (s!"<{tag}{attrStr}>{childStr}</{tag}>", hs2)
  /-- Render a list of children, threading the handler table. -/
  def renderChildren (hs : Array msg) : List (Html msg) → String × Array msg
    | []      => ("", hs)
    | c :: cs =>
        let (s1, hs1) := renderNode hs c
        let (s2, hs2) := renderChildren hs1 cs
        (s1 ++ s2, hs2)
end

/-- Render a node to an HTML string (model data escaped). The single renderer:
    used for native sanity checks and server-side rendering. -/
def Html.render (h : Html msg) : String := (renderNode #[] h).1

end Qed
