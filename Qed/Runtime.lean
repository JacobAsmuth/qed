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

/-- Relabel the messages an effect will produce (functoriality in `msg`). -/
def Cmd.map (f : α → β) : Cmd α → Cmd β
  | .none                      => .none
  | .stream u b onChunk onDone => .stream u b (fun c => f (onChunk c)) (f onDone)
  | .now onNow                 => .now (fun d => f (onNow d))

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
  | .onClick m => (s!" data-qed-click=\"{hs.size}\"", hs.push m)
  | .onInput _ => ("", hs)   -- no static form; the driver wires input events
  | .onCheck _ => ("", hs)   -- (same — the driver wires checkbox change events)

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
