/-
  Qed.Notation — the readable surface for writing views.

  These are *pure sugar*: every combinator below reduces to a `Qed.Html`
  constructor, so using them costs nothing in guarantees. A richer `do`-style
  block macro can be layered on later; it would elaborate to exactly these.
-/
import Qed.Html

namespace Qed

/-- A text node. -/
def text (s : String) : Html msg := .text s

/-- A generic element. Attributes and children default to empty so call sites
    stay terse. -/
def el (tag : String) (attrs : List (Attr msg) := []) (children : List (Html msg) := []) :
    Html msg := .element tag attrs children

/-- Common elements. Add more freely — each is a one-liner. -/
def div    (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "div" attrs children
def span   (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "span" attrs children
def button (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "button" attrs children
def p      (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "p" attrs children
def h1     (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "h1" attrs children
def input  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "input" attrs children
def label  (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg := el "label" attrs children

/-- Attribute helpers. -/
def cls (name : String) : Attr msg := .cls name
def attr (key value : String) : Attr msg := .attr key value
def onClick (m : msg) : Attr msg := .onClick m

end Qed
