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

namespace Qed

/-- A self-contained application: state, a transition function, and a view. -/
structure App (Model : Type) (Msg : Type) where
  /-- The initial model. -/
  init   : Model
  /-- The pure, total state transition. -/
  update : Model → Msg → Model
  /-- The pure, total render. -/
  view   : Model → Html Msg

/-- Build an `App` with no side effects (the Elm "sandbox"). -/
def sandbox (init : Model) (update : Model → Msg → Model) (view : Model → Html Msg) :
    App Model Msg :=
  { init, update, view }

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
