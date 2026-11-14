import Qed.Html
import Qed.Router

namespace Qed

def text [ToString α] (a : α) : Html msg := .text (toString a)
def lazy {α msg : Type} [LawfulKey α] (f : α → Html msg) (a : α) : Html msg := f a

def el (tag : String) (attrs : List (Attr msg) := []) (children : List (Html msg) := []) :
    Html msg := .element tag attrs children

def link {α} [ToHref α] (target : α) (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg :=
  el "a" (Attr.attr "href" (ToHref.toHref target) :: Attr.attr "data-qed-link" "" :: attrs) children

def linkTo {α} [Router α] (route : α)
    (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg :=
  link route attrs children

def cls (name : String) : Attr msg := .cls name
def attr {α} [ToString α] (key : String) (value : α) : Attr msg := .attr key (toString value)
def role (name : String) : Attr msg := .attr "data-role" name
def on (event : String) (m : msg) : Attr msg := .on event m
def onValue (event : String) (handler : String → msg) : Attr msg := .onValue event handler
def onClick (m : msg) : Attr msg := .on "click" m
def onInput (handler : String → msg) : Attr msg := .onValue "input" handler
def onChange (handler : String → msg) : Attr msg := .onValue "input" handler
def onCheck (handler : Bool → msg) : Attr msg := .onValue "change" (fun s => handler (s == "true"))
def onKeydown (handler : String → msg) : Attr msg := .onValue "keydown" handler
def onKeyup (handler : String → msg) : Attr msg := .onValue "keyup" handler
def onSubmit (m : msg) : Attr msg := .on "submit" m
def onBlur (m : msg) : Attr msg := .on "blur" m
def onFocus (m : msg) : Attr msg := .on "focus" m
def onDoubleClick (m : msg) : Attr msg := .on "dblclick" m
def onMouseDown (m : msg) : Attr msg := .on "mousedown" m
def onMouseUp (m : msg) : Attr msg := .on "mouseup" m
def key {α} [ToString α] (k : α) : Attr msg := .key (toString k)

def value {α} [ToString α] (v : α) : Attr msg := .attr "value" (toString v)
def placeholder (v : String) : Attr msg := .attr "placeholder" v
def name        (v : String) : Attr msg := .attr "name" v
def href {α} [ToHref α] (v : α)   : Attr msg := .attr "href" (ToHref.toHref v)
def src {α} [ToHref α] (v : α)    : Attr msg := .attr "src" (ToHref.toHref v)
def action {α} [ToHref α] (v : α) : Attr msg := .attr "action" (ToHref.toHref v)
def alt         (v : String) : Attr msg := .attr "alt" v
def title       (v : String) : Attr msg := .attr "title" v
def style       (v : String) : Attr msg := .attr "style" v
def type'       (v : String) : Attr msg := .attr "type" v

def disabled (present : Bool) : Attr msg := .flag "disabled" present
def required (present : Bool) : Attr msg := .flag "required" present
def checked  (present : Bool) : Attr msg := .flag "checked" present
def readOnly (present : Bool) : Attr msg := .flag "readonly" present

end Qed
