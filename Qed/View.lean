/-
  Qed.View — fine-grained reactive templates.

  A `View σ msg` is a *template*: a tree whose static parts are fixed and whose
  dynamic leaves are *projections* `σ → String` of a scope value `σ` (the model, or a
  row of a list). Unlike `view : Model → Html Msg` — re-run every frame, rebuilding
  the whole tree — a template is built once; on update only the projections re-run, so
  a value change costs O(bindings) and never walks the tree. That is fine-grained
  reactivity (SolidJS-style), but the value still lives in the model and `update` stays
  the pure `Model → Msg → Model`: the signal is *derived*, not a side channel.

  The meaning of a template is given by `render : View σ msg → σ → Html msg`, which
  evaluates it against a scope to produce an ordinary `Html`. So a template *is* its
  rendering — everything proven about `Html` (`diff_apply`) holds of `render t m`, and
  the simplest possible runtime is `view m := render t m` (the verified path, no
  fine-grained machinery). `Qed.Driver` then builds the DOM once and re-runs only the
  projections; `View.render` is the specification that fine-grained path is checked
  against (`Qed.ViewDiff`).

  Structure that *changes shape* — a conditional (`showIf`) or a keyed list
  (`keyedList`) — cannot be a projection, since a projection only changes a value, not
  the tree. Those reconcile through the existing verified `diff`: `showIf` renders an
  empty text node when false (so the slot is always present and positions stay stable),
  and `keyedList` renders a container whose children carry their derived `key`, exactly
  the keyed-reconcile shape `diff` already proves correct.
-/
import Qed.Runtime

namespace Qed

/-- A template attribute: either a `stat`ic attribute (any `Attr`), or one `bind`ed to
    the scope (`σ → Attr msg`) — which covers both a dynamic value (`value="get σ"`) and
    a dynamic event whose message reads the scope (`onClick (.toggle row.id)` inside a
    list row, where `row` is only known per item). The driver re-evaluates `bind` attrs
    on update and leaves `stat` ones alone. -/
inductive VAttr (σ : Type) (msg : Type) where
  /-- A fixed attribute (reuse every `Attr` helper; a `Coe` wraps them silently). -/
  | stat (a : Attr msg)
  /-- A scope-bound attribute, recomputed from the scope when it changes. -/
  | bind (get : σ → Attr msg)

/-- A fine-grained view template over a scope `σ`, producing messages `msg`.

    `text`/`element`/`static` are fixed structure; `dyn` is a value bound to the scope;
    `showIf`/`keyedList` are the two structural combinators (conditional, keyed list)
    that reconcile through the verified `diff` rather than as bindings. A `keyedList`'s
    `child` template is scoped to a *row* `α`, not the outer `σ` — its projections read
    the row — which is what makes per-row updates fine-grained. -/
inductive View (σ : Type) (msg : Type) where
  /-- Static text. -/
  | text (s : String)
  /-- Dynamic text bound to the scope: renders `get σ`, repatched when it changes. -/
  | dyn (get : σ → String)
  /-- An element: tag, template attributes, and template children. -/
  | element (tag : String) (attrs : List (VAttr σ msg)) (kids : List (View σ msg))
  /-- Conditional structure: render `child` when `cond σ`, else an empty text node
      (the slot stays present so sibling positions/bindings don't shift). -/
  | showIf (cond : σ → Bool) (child : View σ msg)
  /-- A keyed list: a container `tag` whose children are `rows σ` — a list of already-
      keyed `Html` rows. Built by the `forEach` combinator, which scopes each row's
      template to its own row type `α` and renders it (the per-row scope stays fully
      typed *at the combinator*, off this inductive — a nested `View α` field would be a
      non-uniform recursive occurrence the kernel rejects). Shape changes reconcile
      through the verified keyed `diff`. -/
  | keyedList (tag : String) (attrs : List (VAttr σ msg)) (rows : σ → List (Html msg))
  /-- An escape hatch: drop a fully-formed `Html` subtree into a template (e.g. to reuse
      an existing component). It is opaque to the fine-grained path — always rebuilt. -/
  | static (html : Html msg)

/-- Evaluate a template attribute against a scope. -/
def VAttr.eval (s : σ) : VAttr σ msg → Attr msg
  | .stat a  => a
  | .bind f  => f s

/-- Attach a reconciliation `key` to a rendered row (a no-op on non-elements, which
    cannot carry one). Keyed-list children render through this so the user writes the
    key *once*, as the list's `key` projection, instead of on every row. -/
def withKey (k : String) : Html msg → Html msg
  | .element t as cs => .element t (.key k :: as) cs
  | h                => h

mutual
  /-- The meaning of a template: evaluate it against a scope to an ordinary `Html`.
      Total and structural; everything `Qed.Diff` proves about `Html` therefore holds
      of `View.render t s`. -/
  def View.render : View σ msg → σ → Html msg
    | .text s,          _ => .text s
    | .dyn get,         s => .text (get s)
    | .element t as ks, s => .element t (as.map (VAttr.eval s)) (View.renderEach ks s)
    | .showIf cond ch,  s => if cond s then View.render ch s else .text ""
    | .keyedList tag as rows, s => .element tag (as.map (VAttr.eval s)) (rows s)
    | .static h,        _ => h
  /-- Render a list of sibling templates against one scope. -/
  def View.renderEach : List (View σ msg) → σ → List (Html msg)
    | [],      _ => []
    | k :: ks, s => View.render k s :: View.renderEach ks s
end

/-! ### Surface combinators

    Mirrors `Qed.Notation`, in namespace `V` so a template module `open Qed.V`s them
    without colliding with the `Html` versions. Every `Attr` helper (`cls`, `onClick`,
    …) coerces into a `VAttr` via the instance below, so attributes read identically to
    plain `Html`; `dynAttr` adds a scope-bound value. -/
namespace V

/-- Any static `Attr` is a template attribute. -/
instance : Coe (Attr msg) (VAttr σ msg) := ⟨.stat⟩

/-- Static text (a bare `String` also coerces). -/
def text (s : String) : View σ msg := .text s
/-- Dynamic text bound to the scope: `dyn (·.name)`. -/
def dyn (get : σ → String) : View σ msg := .dyn get
/-- Static attribute helpers, returning `VAttr` so dotted message notation
    (`onClick .save`) resolves without leaning on the `Attr → VAttr` coercion. Mirror of
    the `Qed.Notation` helpers; add more as needed. -/
def cls (c : String) : VAttr σ msg := .stat (.cls c)
def attr (k v : String) : VAttr σ msg := .stat (.attr k v)
def value (v : String) : VAttr σ msg := .stat (.attr "value" v)
def type' (v : String) : VAttr σ msg := .stat (.attr "type" v)
def placeholder (v : String) : VAttr σ msg := .stat (.attr "placeholder" v)
def disabled (on : Bool) : VAttr σ msg := .stat (.flag "disabled" on)
def checked (on : Bool) : VAttr σ msg := .stat (.flag "checked" on)
def onClick (m : msg) : VAttr σ msg := .stat (.onClick m)
def onSubmit (m : msg) : VAttr σ msg := .stat (.onSubmit m)
def onBlur (m : msg) : VAttr σ msg := .stat (.onBlur m)
def onFocus (m : msg) : VAttr σ msg := .stat (.onFocus m)
def onInput (h : String → msg) : VAttr σ msg := .stat (.onInput h)
def onCheck (h : Bool → msg) : VAttr σ msg := .stat (.onCheck h)
def onKeydown (h : String → msg) : VAttr σ msg := .stat (.onKeydown h)

/-- A scope-bound attribute (general form): `bindAttr (fun r => onClick (.pick r.id))`. -/
def bindAttr (get : σ → Attr msg) : VAttr σ msg := .bind get
/-- A dynamic attribute value bound to the scope: `dynAttr "value" (·.draft)`. -/
def dynAttr (name : String) (get : σ → String) : VAttr σ msg := .bind (fun s => .attr name (get s))
/-- A click whose message reads the scope: `onClick' (fun r => .pick r.id)`. -/
def onClick' (get : σ → msg) : VAttr σ msg := .bind (fun s => .onClick (get s))
/-- An input whose message reads the scope and the field value. -/
def onInput' (get : σ → String → msg) : VAttr σ msg := .bind (fun s => .onInput (get s))
/-- A checkbox whose message reads the scope and the checked state. -/
def onCheck' (get : σ → Bool → msg) : VAttr σ msg := .bind (fun s => .onCheck (get s))
/-- Drop a ready-made `Html` subtree into a template. -/
def static (h : Html msg) : View σ msg := .static h

/-- A bare string is static text. -/
instance : Coe String (View σ msg) := ⟨.text⟩
/-- …and a lone string is a one-element child list, so `button [..] "Save"` works. -/
instance : Coe String (List (View σ msg)) := ⟨fun s => [.text s]⟩

/-- A generic element. -/
def el (tag : String) (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) :
    View σ msg := .element tag attrs kids

def div    (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) : View σ msg := el "div" attrs kids
def span   (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) : View σ msg := el "span" attrs kids
def button (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) : View σ msg := el "button" attrs kids
def p      (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) : View σ msg := el "p" attrs kids
def h1     (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) : View σ msg := el "h1" attrs kids
def h2     (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) : View σ msg := el "h2" attrs kids
def ul     (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) : View σ msg := el "ul" attrs kids
def li     (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) : View σ msg := el "li" attrs kids
def label  (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) : View σ msg := el "label" attrs kids
def input  (attrs : List (VAttr σ msg) := []) (kids : List (View σ msg) := []) : View σ msg := el "input" attrs kids

/-- Render `child` only while `cond` holds (an empty slot otherwise). -/
def showIf (cond : σ → Bool) (child : View σ msg) : View σ msg := .showIf cond child

/-- A keyed list: `forEach "ul" (·.rows) (·.id) rowTemplate`. The container is `tag`;
    each item of `items σ` renders `child` scoped to *that row*, keyed by `key`. The row
    template is fully typed at its own scope `α`; `forEach` renders it per row (so the
    `View σ` tree stores only the resulting keyed `Html`). Shape changes reconcile
    through the verified keyed `diff`. -/
def forEach {α : Type} (tag : String) (items : σ → List α) (key : α → String)
    (child : View α msg) (attrs : List (VAttr σ msg) := []) : View σ msg :=
  .keyedList tag attrs (fun s => (items s).map (fun a => withKey (key a) (View.render child a)))

end V

/-- Build an `App` from a template: the view is `View.render t`, i.e. the template
    compiled to the verified `Html` path. (The browser driver makes value updates
    fine-grained; this builder's *meaning* is a full render each frame, and is what the
    fine-grained path is proven equal to.) Effects and startup mirror `application`. -/
def templated (init : Model) (update : Model → Msg → Model) (template : View Model Msg)
    (effects : Model → Msg → Cmd Msg := fun _ _ => .none)
    (locals  : List LocalDef := [])
    (onPort  : Option (String → String → Option Msg) := none)
    (start   : Cmd Msg := .none) : App Model Msg :=
  application init update (fun m => View.render template m)
    (effects := effects) (locals := locals) (onPort := onPort) (start := start)

end Qed
