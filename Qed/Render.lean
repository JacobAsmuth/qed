/-
  Qed.Render — the pure `Html` → string renderer.

  Extracted from `Qed.Runtime` so it sits *below* `Qed.View`: `View.render`'s machinery
  needs `Html.render` (to fingerprint/diff opaque subtrees), and we want `App` (in
  `Runtime`) to be able to carry a `View` template — which requires `View` not to import
  `Runtime`. Everything here depends only on `Qed.Html`.

  The renderer threads a handler table `hs : Array msg`: an event attribute emits a
  `data-qed-*="<id>"` marker whose `<id>` indexes the message the JS delegation dispatches.
  `<style>`/`<script>` content is emitted verbatim (HTML raw-text elements).
-/
import Qed.Html

namespace Qed

/-- The DOM key a local-component host occupies, namespaced by component so two components
    reusing a key string never collide. -/
def localKey (component key : String) : String := component ++ "@" ++ key

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
  | .localCell key comp _ _ => (s!" data-qed-local=\"{escapeHtml (localKey comp key)}\"", hs)   -- marks the host; the driver fills it
  | .signalBind name        => (s!" data-qed-signal=\"{escapeHtml name}\"", hs)                 -- driver binds its text to the signal
  | .signalAttr _ attr value => (s!" {attr}=\"{escapeHtml value}\"", hs)                        -- driver binds this attr to the signal

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
        -- `<style>`/`<script>` are HTML "raw text" elements: their content is CDATA-like
        -- (CSS/JS), so escaping `&`/`<` would corrupt it. Emit text children verbatim.
        if tag == "style" || tag == "script" then
          let raw := String.join (children.map fun | .text s => s | _ => "")
          (s!"<{tag}{attrStr}>{raw}</{tag}>", hs1)
        else
          let (childStr, hs2) := renderChildren hs1 children
          (s!"<{tag}{attrStr}>{childStr}</{tag}>", hs2)
    | .lazy _ sub => renderNode hs sub   -- transparent for the string renderer
  /-- Render a list of children, threading the handler table. -/
  def renderChildren (hs : Array msg) : List (Html msg) → String × Array msg
    | []      => ("", hs)
    | c :: cs =>
        let (s1, hs1) := renderNode hs c
        let (s2, hs2) := renderChildren hs1 cs
        (s1 ++ s2, hs2)
end

/-- Render a node to an HTML string (model data escaped). The total renderer: a
    local host renders *empty* (the driver fills it in the browser). Used for native
    sanity checks and server-side rendering where local content isn't needed. -/
def Html.render (h : Html msg) : String := (renderNode #[] h).1

end Qed
