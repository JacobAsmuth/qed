import Qed.Html
import Qed.Router.Basic

namespace Qed

def text [ToString α] (a : α) : Html msg := .text (toString a)
def lazy {α msg : Type} [LawfulKey α] (f : α → Html msg) (a : α) : Html msg := f a
def el (tag : String) (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg :=
  .element tag attrs children
def link {α} [ToHref α] (target : α) (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg :=
  el "a" (Attr.attr "href" (ToHref.toHref target) :: Attr.attr "data-qed-link" "" :: attrs) children
def linkTo {α} [Router α] (route : α) (attrs : List (Attr msg) := []) (children : List (Html msg) := []) : Html msg :=
  link route attrs children

def cls (name : String) : Attr msg := .cls name
def attr {α} [ToString α] (key : String) (value : α) : Attr msg := .attr key (toString value)
def role (name : String) : Attr msg := .attr "data-role" name
abbrev ariaRole (name : String) : Attr msg := attr "role" name
def on (event : String) (m : msg) : Attr msg := .on event m
def onValue (event : String) (handler : String → msg) : Attr msg := .onValue event handler
def onCheck (handler : Bool → msg) : Attr msg := .onValue "change" (fun s => handler (s == "true"))
def key {α} [ToString α] (k : α) : Attr msg := .key (toString k)
def value {α} [ToString α] (v : α) : Attr msg := .attr "value" (toString v)

local macro "def_attrs" kind:ident "[" items:("(" ident "," str ")"),* "]" : command => do
  let cmds ← items.getElems.mapM fun it => do
    let id : Lean.Ident := ⟨it.raw[1]⟩
    let lit : Lean.TSyntax `str := ⟨it.raw[3]⟩
    match kind.getId with
    | `on   => `(def $id {msg : Type} (m : msg) : Attr msg := .on $lit m)
    | `val  => `(def $id {msg : Type} (handler : String → msg) : Attr msg := .onValue $lit handler)
    | `str  => `(def $id {msg : Type} (v : String) : Attr msg := .attr $lit v)
    | _     => `(def $id {msg : Type} (present : Bool) : Attr msg := .flag $lit present)
  return ⟨Lean.mkNullNode cmds⟩

def_attrs on   [(onClick, "click"), (onSubmit, "submit"), (onBlur, "blur"), (onFocus, "focus"),
                (onDoubleClick, "dblclick"), (onMouseDown, "mousedown"), (onMouseUp, "mouseup")]
def_attrs val  [(onInput, "input"), (onChange, "input"), (onKeydown, "keydown"), (onKeyup, "keyup")]
def_attrs str  [(placeholder, "placeholder"), (name, "name"), (alt, "alt"), (title, "title"), (style, "style"), (type', "type")]
def_attrs flag [(disabled, "disabled"), (required, "required"), (checked, "checked"), (readOnly, "readonly")]

theorem ToHref.valid_attr {msg α : Type} [ToHref α] (k : String) (target : α)
    (hk : isSafeAttrName k = true) : (Attr.attr k (ToHref.toHref target) : Attr msg).valid = true := by
  simp [Attr.valid, Attr.validKeyValue, hk, ToHref.isSafeUrl_toHref]

local macro "def_url_attr " id:ident thm:ident k:str : command =>
  `(def $id {msg α : Type} [ToHref α] (v : α) : Attr msg := .attr $k (ToHref.toHref v)
    @[simp] theorem $thm {msg α : Type} [ToHref α] (v : α) : ($id v : Attr msg).valid = true :=
      ToHref.valid_attr $k v rfl)

def_url_attr href   Attr.valid_href   "href"
def_url_attr src    Attr.valid_src    "src"
def_url_attr action Attr.valid_action "action"

end Qed
