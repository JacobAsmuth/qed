/-
  Qed.Notation — the readable surface for writing views.

  These are *pure sugar*: every combinator below reduces to a `Qed.Html`
  constructor, so using them costs nothing in guarantees. With the `Coe String _`
  instances in `Qed.Html`, string children need no `text` wrapper:

      button [onClick .save] "Save"
      span [cls "count"] [toString n]
-/
import Qed.Html
import Qed.Router

namespace Qed

/-- A text node. Rarely needed explicitly — a bare `String` coerces to one. -/
def text (s : String) : Html msg := .text s

/-- Memoize a subtree by a key (React's `useMemo`/`shouldComponentUpdate` as data): when
    `key` is unchanged since the last render, the diff skips `sub` — no re-diff, no DOM
    patch. Make `key` capture exactly the inputs `sub` is built from. -/
def lazy (key : String) (sub : Html msg) : Html msg := .lazy key sub

/-- A generic element. Attributes and children default to empty so call sites
    stay terse. -/
def el (tag : String) (attrs : List (Attr msg) := []) (children : List (Html msg) := []) :
    Html msg := .element tag attrs children

/-- Common elements. Add more freely — each is a one-liner. -/
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

/-- An internal navigation link: an `<a href=path>` the driver intercepts (no full
    page reload) — clicking it pushes `path` to the URL and routes to it. Pair with
    `Router.toURL` for a type-checked target, or use `linkTo` to pass the route directly. -/
def link (path : String) (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg :=
  el "a" (Attr.attr "href" path :: Attr.attr "data-qed-link" "" :: attrs) children

/-- A type-checked internal link: builds the `<a href>` from a routed value via
    `Router.toURL`, so the target can only be a real route — never a hand-typed string that
    might not parse back. The `Router.round_trip` proof then guarantees clicking it navigates
    to exactly this route. `linkTo (Route.user "ada") [cls "u"] "Ada"`. -/
def linkTo {α} [Router α] (route : α)
    (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg :=
  link (Router.toURL route) attrs children

/-- Class / arbitrary-attribute / event helpers. -/
def cls (name : String) : Attr msg := .cls name
def attr (key value : String) : Attr msg := .attr key value
/-- Listen for any DOM `event`, dispatching the constant `m` — the escape hatch when no named
    helper fits (`on "wheel" .scrolled`, `on "dragover" .dragging`, …). -/
def on (event : String) (m : msg) : Attr msg := .on event m
/-- Listen for any DOM `event`, dispatching `handler payload` (the event's value/key/checked
    string) — e.g. `onValue "paste" .pasted`. -/
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

/-- Typed string attributes — typos in the key become compile errors. -/
def value       (v : String) : Attr msg := .attr "value" v
def placeholder (v : String) : Attr msg := .attr "placeholder" v
def name        (v : String) : Attr msg := .attr "name" v
def href        (v : String) : Attr msg := .attr "href" v
def src         (v : String) : Attr msg := .attr "src" v
def alt         (v : String) : Attr msg := .attr "alt" v
def title       (v : String) : Attr msg := .attr "title" v
def style       (v : String) : Attr msg := .attr "style" v
def type'       (v : String) : Attr msg := .attr "type" v

/-- Typed boolean attributes — present on the node *iff* the flag is `true`, so
    `disabled false` actually enables (no `disabled="false"` footgun). -/
def disabled (present : Bool) : Attr msg := .flag "disabled" present
def required (present : Bool) : Attr msg := .flag "required" present
def checked  (present : Bool) : Attr msg := .flag "checked" present
def readOnly (present : Bool) : Attr msg := .flag "readonly" present

end Qed
