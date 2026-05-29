/-
  Qed.Notation — the readable surface for writing views.

  These are *pure sugar*: every combinator below reduces to a `Qed.Html`
  constructor, so using them costs nothing in guarantees. With the `Coe String _`
  instances in `Qed.Html`, string children need no `text` wrapper:

      button [onClick .save] "Save"
      span [cls "count"] [toString n]
-/
import Qed.Html

namespace Qed

/-- A text node. Rarely needed explicitly — a bare `String` coerces to one. -/
def text (s : String) : Html msg := .text s

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

/-- Class / arbitrary-attribute / event helpers. -/
def cls (name : String) : Attr msg := .cls name
def attr (key value : String) : Attr msg := .attr key value
def onClick (m : msg) : Attr msg := .onClick m
/-- Fire `handler currentValue` whenever the field is edited. -/
def onInput (handler : String → msg) : Attr msg := .onInput handler

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
def disabled (on : Bool) : Attr msg := .flag "disabled" on
def required (on : Bool) : Attr msg := .flag "required" on
def checked  (on : Bool) : Attr msg := .flag "checked" on
def readOnly (on : Bool) : Attr msg := .flag "readonly" on

end Qed
