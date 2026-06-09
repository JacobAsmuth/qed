/-
  Qed.Notation: the readable surface for writing views.

  These are *pure sugar*: every combinator below reduces to a `Qed.Html`
  constructor, so using them costs nothing in guarantees. With the `Coe String _`
  instances in `Qed.Html`, string children need no `text` wrapper:

      button [onClick .save] "Save"
      span [cls "count"] [toString n]
-/
import Qed.Html
import Qed.Router

namespace Qed

/-- A text node, from anything `ToString`: `text m.count` needs no `toString`. Rarely
    needed at all: a bare `String`/`Nat`/`Int` child coerces to one. -/
def text [ToString α] (a : α) : Html msg := .text (toString a)

/-- Memoize a subtree by a key (React's `useMemo`/`shouldComponentUpdate` as data): when
    `key` is unchanged since the last render, the diff skips `sub`, no re-diff, no DOM
    patch. Make `key` capture exactly the inputs `sub` is built from. -/
def lazy (key : String) (sub : Html msg) : Html msg := .lazy key sub

/-- A generic element. Attributes and children default to empty so call sites
    stay terse. -/
def el (tag : String) (attrs : List (Attr msg) := []) (children : List (Html msg) := []) :
    Html msg := .element tag attrs children

/-- Common elements. Add more freely, each is a one-liner. -/
def div     (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "div" attrs children
def span    (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "span" attrs children
def button  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "button" attrs children
def p       (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "p" attrs children
def h1      (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "h1" attrs children
def h2      (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "h2" attrs children
def a       (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "a" attrs children
def ul      (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "ul" attrs children
def li      (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "li" attrs children
def header  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "header" attrs children
def nav     (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "nav" attrs children
def strong  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "strong" attrs children
def input   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "input" attrs children
def label   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "label" attrs children
def formEl  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "form" attrs children

/-- The rest of the common HTML elements. Any element is also reachable as `el "tag" …`; these are
    the named conveniences. A few names are taken, `<section>` is `sectionEl` and `<main>` is
    `mainEl` (both are reserved), `<form>` is `formEl`, and `<em>` is `el "em"` (the CSS `em` length
    owns the name). -/
-- Sectioning & layout
def sectionEl  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "section" attrs children
def article    (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "article" attrs children
def mainEl     (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "main" attrs children
def aside      (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "aside" attrs children
def footer     (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "footer" attrs children
def figure     (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "figure" attrs children
def figcaption (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "figcaption" attrs children
def address    (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "address" attrs children
-- Headings (h1/h2 are above)
def h3 (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "h3" attrs children
def h4 (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "h4" attrs children
def h5 (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "h5" attrs children
def h6 (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "h6" attrs children
-- Grouping & text
def ol         (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "ol" attrs children
def dl         (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "dl" attrs children
def dt         (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "dt" attrs children
def dd         (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "dd" attrs children
def pre        (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "pre" attrs children
def blockquote (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "blockquote" attrs children
def hr         (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "hr" attrs children
def br         (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "br" attrs children
-- Inline text semantics
def small (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "small" attrs children
def mark  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "mark" attrs children
def sub   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "sub" attrs children
def sup   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "sup" attrs children
def code  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "code" attrs children
def kbd   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "kbd" attrs children
def abbr  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "abbr" attrs children
def cite  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "cite" attrs children
def time  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "time" attrs children
def del   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "del" attrs children
def ins   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "ins" attrs children
-- Media & embedded
def img     (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "img" attrs children
def picture (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "picture" attrs children
def source  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "source" attrs children
def video   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "video" attrs children
def audio   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "audio" attrs children
def track   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "track" attrs children
def canvas  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "canvas" attrs children
def iframe  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "iframe" attrs children
-- Interactive
def details (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "details" attrs children
def summary (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "summary" attrs children
def dialog  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "dialog" attrs children
-- Form controls (the typed `schema`/`Codec` API is the higher-level way; these are the raw elements)
def select   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "select" attrs children
def option   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "option" attrs children
def optgroup (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "optgroup" attrs children
def textarea (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "textarea" attrs children
def fieldset (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "fieldset" attrs children
def legend   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "legend" attrs children
def datalist (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "datalist" attrs children
def output   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "output" attrs children
def progress (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "progress" attrs children
def meter    (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "meter" attrs children
-- Tables
def table    (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "table" attrs children
def caption  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "caption" attrs children
def colgroup (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "colgroup" attrs children
def col      (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "col" attrs children
def thead    (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "thead" attrs children
def tbody    (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "tbody" attrs children
def tfoot    (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "tfoot" attrs children
def tr       (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "tr" attrs children
def td       (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "td" attrs children
def th       (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "th" attrs children

/-- Common SVG elements. Nest them inside `svg`: the driver puts the whole `svg` subtree in the
    SVG namespace (any element, not just these, so `el "feSpotLight"` works too, see
    `Dom.childNamespace`). Set geometry with `attr` (`attr "viewBox" "0 0 100 100"`, `attr "cx"
    "50"`, `attr "d" "M0 0 L10 10"`, …); namespaced links use `attr "xlink:href" "#id"`. -/
def svg      (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "svg" attrs children
def g        (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "g" attrs children
def path     (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "path" attrs children
def circle   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "circle" attrs children
def ellipse  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "ellipse" attrs children
def line     (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "line" attrs children
def rect     (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "rect" attrs children
def polyline (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "polyline" attrs children
def polygon  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "polygon" attrs children

/-- An internal navigation link: an `<a href=path>` the driver intercepts (no full
    page reload), clicking it pushes `path` to the URL and routes to it. Pair with
    `Router.toURL` for a type-checked target, or use `linkTo` to pass the route directly. -/
def link (path : String) (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg :=
  el "a" (Attr.attr "href" path :: Attr.attr "data-qed-link" "" :: attrs) children

/-- A type-checked internal link: builds the `<a href>` from a routed value via
    `Router.toURL`, so the target can only be a real route, never a hand-typed string that
    might not parse back. The `Router.round_trip` proof then guarantees clicking it navigates
    to exactly this route. `linkTo (Route.user "ada") [cls "u"] "Ada"`. -/
def linkTo {α} [Router α] (route : α)
    (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg :=
  link (Router.toURL route) attrs children

/-- Class / arbitrary-attribute / event helpers. -/
def cls (name : String) : Attr msg := .cls name
def attr (key value : String) : Attr msg := .attr key value
/-- Tag an element with a styling `role` (a `data-role` attribute): the handle a styling
    `invariant … holds_in view` uses to say "every element with this role is styled thus".
    Pair with `roleHasOneOf`: `button [role "toggle", …] …`. -/
def role (name : String) : Attr msg := .attr "data-role" name
/-- Set an element's content from a raw markup string (React's `dangerouslySetInnerHTML`): the
    browser parses `markup` as the node's inner HTML and any child list is ignored. The escape
    hatch for markup you already have as a string, an inline SVG icon, a sanitized snippet:
    `span [rawHtml iconSvg] []`. Unescaped by design, so only pass markup you trust. -/
def rawHtml (markup : String) : Attr msg := .rawHtml markup
/-- Listen for any DOM `event`, dispatching the constant `m`, the escape hatch when no named
    helper fits (`on "wheel" .scrolled`, `on "dragover" .dragging`, …). -/
def on (event : String) (m : msg) : Attr msg := .on event m
/-- Listen for any DOM `event`, dispatching `handler payload` (the event's value/key/checked
    string), e.g. `onValue "paste" .pasted`. -/
def onValue (event : String) (handler : String → msg) : Attr msg := .onValue event handler
def onClick (m : msg) : Attr msg := .on "click" m
/-- Fire `handler currentValue` whenever the field is edited. -/
def onInput (handler : String → msg) : Attr msg := .onValue "input" handler
/-- Fire `handler selectedValue` when a `<select>` or radio changes (alias of
    `onInput`; both fire the `input` event). -/
def onChange (handler : String → msg) : Attr msg := .onValue "input" handler
/-- Fire `handler isChecked` whenever a checkbox toggles. -/
def onCheck (handler : Bool → msg) : Attr msg := .onValue "change" (fun s => handler (s == "true"))
/-- Fire `handler key` on `keydown`, where `key` is the pressed key's name
    (`"Enter"`, `"Escape"`, …). Handy for Enter-to-submit / keyboard shortcuts. -/
def onKeydown (handler : String → msg) : Attr msg := .onValue "keydown" handler
/-- Fire `handler key` on `keyup`. -/
def onKeyup (handler : String → msg) : Attr msg := .onValue "keyup" handler
/-- Fire `m` when a `<form>` is submitted; the page reload is always suppressed. -/
def onSubmit (m : msg) : Attr msg := .on "submit" m
/-- Fire `m` when the element loses focus (`blur`). -/
def onBlur (m : msg) : Attr msg := .on "blur" m
/-- Fire `m` when the element gains focus. -/
def onFocus (m : msg) : Attr msg := .on "focus" m
/-- A double-click; `on "dblclick"` under the hood. -/
def onDoubleClick (m : msg) : Attr msg := .on "dblclick" m
/-- Mouse button pressed / released over the element. -/
def onMouseDown (m : msg) : Attr msg := .on "mousedown" m
def onMouseUp (m : msg) : Attr msg := .on "mouseup" m

/-- A reconciliation key (React/Vue `key`): give each item in a repeated list a
    stable key so the diff matches a moved/removed row to its previous DOM node
    instead of reconciling positionally. Reconciliation-only; never rendered. -/
def key (k : String) : Attr msg := .key k

/-- Typed string attributes: typos in the key become compile errors. -/
def value       (v : String) : Attr msg := .attr "value" v
def placeholder (v : String) : Attr msg := .attr "placeholder" v
def name        (v : String) : Attr msg := .attr "name" v
def href        (v : String) : Attr msg := .attr "href" v
def src         (v : String) : Attr msg := .attr "src" v
def alt         (v : String) : Attr msg := .attr "alt" v
def title       (v : String) : Attr msg := .attr "title" v
def style       (v : String) : Attr msg := .attr "style" v
def type'       (v : String) : Attr msg := .attr "type" v

/-- Typed boolean attributes: present on the node *iff* the flag is `true`, so
    `disabled false` actually enables (no `disabled="false"` footgun). -/
def disabled (present : Bool) : Attr msg := .flag "disabled" present
def required (present : Bool) : Attr msg := .flag "required" present
def checked  (present : Bool) : Attr msg := .flag "checked" present
def readOnly (present : Bool) : Attr msg := .flag "readonly" present

end Qed
