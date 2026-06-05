/-
  Qed.Invariant — automatic state-machine invariant proofs.

  You state a property of the model and which transition should preserve it; the
  framework *generates and discharges* the preservation theorem for every message,
  with no hand-written proof. If the automation cannot close a goal this fails to
  compile — we never emit `sorry`, because an honest "you must prove this" beats a
  fake guarantee.

      invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update

  expands to a machine-checked

      theorem counterSafe : ∀ m msg, 0 ≤ m.count → 0 ≤ (update m msg).count

  This is the property that survives *every* reachable sequence of events — not the
  cases a test happened to cover. The claim itself is small and readable; the proof
  that the code obeys it is the machine's job.

  ## Pure or effectful — same syntax

  `preserved_by` works whether the transition is pure (`Model → Msg → Model`) or
  effectful (`Model → Msg → Model × Cmd Msg`). The next model is projected out of
  the result either way (`InvTarget.proj`), so `update` and `transition` both work:

      invariant streamSafe : (fun m => m.pending = true → 0 < m.turns.size)
        preserved_by transition

  ## When the automation can't close it

  The default discharger handles arithmetic, boolean and `Option` reasoning, and the
  `still`/`also` effect wrappers (`omega`, `simp`, case splits, `decide`). For an
  invariant that needs a lemma it can't guess — typically one quantified over your
  own collections — supply the proof after `:=`. The goal is the generated theorem
  `∀ m msg, pred m → pred (next m msg)`, so a proof opens with `intro m msg h`:

      invariant idsBelowNext : (fun m => ∀ r ∈ m.rows, r.id < m.nextId)
        preserved_by update := by
          intro m msg h
          cases msg <;> simp_all [update] <;> omega

  On failure the unsolved goal is labelled with the offending message constructor
  (Lean's `case` tag), so the error points at exactly the transition arm that breaks
  the property — the signal you (or an agent) act on: fix the update, or weaken the
  claim to what the code actually guarantees.

  Note: this file deliberately does *not* `import Lean`. `syntax`/`macro_rules` are
  core features, so the macro carries zero runtime footprint — apps that use it never
  pull the Lean elaborator into their transpiled JS bundle. The only import is `Qed.Runtime`,
  for the `still`/`also` effect wrappers the discharger unfolds; it too is `Lean`-free.
-/
import Qed.Runtime
import Qed.Style

namespace Qed

/-- Projects the next *model* out of whatever a transition returns — the model itself
    for a pure `update`, or the first component for an effectful `transition` that
    returns `Model × Cmd Msg`. This is what lets one `invariant` syntax cover both
    shapes; it is erased from the statement by `simp` before any real proof work. -/
class InvTarget (α : Type) (Model : outParam Type) where
  proj : α → Model

instance {Model : Type} : InvTarget Model Model := ⟨id⟩
instance {Model β : Type} : InvTarget (Model × β) Model := ⟨Prod.fst⟩

@[simp] theorem InvTarget.proj_id {Model : Type} (m : Model) :
    InvTarget.proj m = m := rfl
@[simp] theorem InvTarget.proj_fst {Model β : Type} (p : Model × β) :
    InvTarget.proj p = p.1 := rfl

/-- `invariant name : pred preserved_by upd` — see the module docs. The optional
    `:= proof` supplies a proof for the cases the default automation can't close. -/
syntax (name := invariantCmd)
  "invariant " ident " : " term " preserved_by " ident (" := " term)? : command

macro_rules
  | `(invariant $name:ident : $pred preserved_by $upd:ident := $pf:term) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(invariant $name:ident : $pred preserved_by $upd:ident) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        intro m msg h
        cases msg <;>
          -- Unfold the transition / effect wrappers / model projection, split every
          -- `if`/`match` the arm introduces, then close each leaf. Each alternative is
          -- all-or-nothing (`<;> done`), and the whole finisher is wrapped in `try` so an
          -- arm the automation can't close is left as an *unsolved goal* labelled with its
          -- message constructor — which fails to compile, rather than slipping through.
          (try simp_all only [$upd:ident, Qed.still, Qed.also,
                              InvTarget.proj_id, InvTarget.proj_fst]) <;>
          (try ((repeat' split) <;>
                 (first | rfl | omega | assumption | (simp_all <;> done) | trivial))))

/-! ### Styling invariants — the same `invariant`, over the view

A styling rule is a property of the rendered *view*, not a state transition, so it uses
`holds_in` where a model invariant uses `preserved_by`:

    invariant toggleStyled : roleHasOneOf "toggle" [activeStyle, inactiveStyle] holds_in view

expands to a machine-checked

    theorem toggleStyled : ∀ m, roleHasOneOf "toggle" [activeStyle, inactiveStyle] (view m) = true

— the styling holds for *every* model, not the states a test happened to render. Tag the elements
you want to constrain with the `role "…"` attribute; `roleHasOneOf` / `tagHasOneOf` are the ready
predicates and `everyElement` builds custom ones. The default discharger unfolds the view and the
`Qed.Notation` combinators, splits the view's `if`/`match`, and closes each leaf (a class check
reduces by `x == x`, never by hashing). Supply a proof after `:=` for a view it can't reduce — e.g.
one routed through `App.view`/`View.render` rather than a plain `Model → Html` function. -/

/-- The class names on an element's attribute list. -/
def attrClasses : List (Attr msg) → List String
  | []          => []
  | .cls c :: r => c :: attrClasses r
  | _ :: r      => attrClasses r

/-- The `role "…"` marker on an element's attributes, if present. -/
def attrRole : List (Attr msg) → Option String
  | []                       => none
  | .attr "data-role" v :: _ => some v
  | _ :: r                   => attrRole r

mutual
/-- `everyElement p h` — does every element in `h` satisfy `p tag attrs`? The basis for a styling
    predicate: `p` decides one element from its tag and attributes. -/
def everyElement (p : String → List (Attr msg) → Bool) : Html msg → Bool
  | .text _        => true
  | .lazy _ s      => everyElement p s
  | .element t a k => p t a && everyElementL p k
/-- `everyElement` over a list of siblings (mutual recursion gives termination). -/
def everyElementL (p : String → List (Attr msg) → Bool) : List (Html msg) → Bool
  | []     => true
  | h :: t => everyElement p h && everyElementL p t
end

/-- Does this element carry the class of one of `styles`? -/
def hasOneClass (styles : List Style) (a : List (Attr msg)) : Bool :=
  (attrClasses a).any ((styles.map (·.className)).contains ·)

/-- Every element tagged `role r` carries the class of one of `styles` — pair with the `role`
    attribute (`button [role "toggle", …] …`). The predicate for `… holds_in view`. -/
def roleHasOneOf (r : String) (styles : List Style) : Html msg → Bool :=
  everyElement (fun _ a => !(attrRole a == some r) || hasOneClass styles a)

/-- Every `<tag>` element carries the class of one of `styles` (no marker needed). -/
def tagHasOneOf (tag : String) (styles : List Style) : Html msg → Bool :=
  everyElement (fun t a => !(t == tag) || hasOneClass styles a)

/-! Relational rules — relate the styles of *different* elements. `roleHas` is the single-element
    query; `both`/`either` combine queries (AND/OR), and `exactlyOne` packages the common "exactly
    one of two is styled on" case. They are stated over *positive* "this element has this style"
    facts, which is what lets them prove with ordinary hashed class names: a positive `x == x`
    membership reduces, whereas a negative "this element does NOT have style Y" would need the two
    styles' class names to be provably distinct — which a content hash cannot give. So express
    "A on XOR B on" as `exactlyOne` (or `(A on ∧ B off) ∨ (A off ∧ B on)` by hand), never as a
    negation. -/

/-- The element(s) tagged `role r` carry exactly `style`. The single-element building block. -/
def roleHas (r : String) (style : Style) : Html msg → Bool :=
  everyElement (fun _ a => !(attrRole a == some r) || (attrClasses a).contains style.className)

/-- Both view predicates hold (AND): `both (roleHas "a" x) (roleHas "b" y)`. -/
def both (p q : Html msg → Bool) : Html msg → Bool := fun h => p h && q h
/-- Either view predicate holds (OR): `either (roleHas "a" x) (roleHas "b" y)`. -/
def either (p q : Html msg → Bool) : Html msg → Bool := fun h => p h || q h

/-- Exactly one of two role-tagged elements is styled `on`, the other `off` — e.g. "exactly one
    tab is active". The positive form `(A on ∧ B off) ∨ (A off ∧ B on)`, so it proves without the
    two styles having to be provably distinct. -/
def exactlyOne (roleA roleB : String) (on off : Style) : Html msg → Bool :=
  either (both (roleHas roleA on) (roleHas roleB off))
         (both (roleHas roleA off) (roleHas roleB on))

/-- `invariant name : pred holds_in view` — `pred : Html msg → Bool` holds of the view for every
    model. The optional `:= proof` supplies a proof the default discharger can't find. -/
syntax (name := invariantView)
  "invariant " ident " : " term " holds_in " ident (" := " term)? : command

open Lean in
macro_rules
  | `(invariant $name:ident : $pred holds_in $view:ident := $pf:term) =>
    `(theorem $name:ident : ∀ m, ($pred) ($view m) = true := $pf)
  | `(invariant $name:ident : $pred holds_in $view:ident) =>
    -- Unfold the view and every `Qed.Notation` combinator down to `Html`/`Attr` constructors,
    -- split each `if`/`match` the view introduces, and close every leaf. A leaf the automation
    -- can't reduce is left as an unsolved goal — which fails to compile, never a fake guarantee.
    -- (Maintenance: this mirror of the element/attribute helpers must list any new one.)
    `(set_option linter.unusedSimpArgs false in
      theorem $name:ident : ∀ m, ($pred) ($view m) = true := by
        intro m
        simp only [$view:ident, Qed.roleHasOneOf, Qed.tagHasOneOf, Qed.roleHas, Qed.both,
          Qed.either, Qed.exactlyOne, Qed.hasOneClass,
          Qed.everyElement, Qed.everyElementL, Qed.attrClasses, Qed.attrRole,
          Qed.text, Qed.lazy, Qed.el, Qed.div, Qed.span, Qed.button, Qed.p, Qed.h1, Qed.h2, Qed.a,
          Qed.ul, Qed.li, Qed.header, Qed.nav, Qed.strong, Qed.input, Qed.label, Qed.formEl,
          Qed.svg, Qed.g, Qed.path, Qed.circle, Qed.ellipse, Qed.line, Qed.rect, Qed.polyline,
          Qed.polygon, Qed.link, Qed.linkTo, Qed.styleSheet, Qed.theme,
          Qed.sectionEl, Qed.article, Qed.mainEl, Qed.aside, Qed.footer, Qed.figure,
          Qed.figcaption, Qed.address, Qed.h3, Qed.h4, Qed.h5, Qed.h6, Qed.ol, Qed.dl, Qed.dt,
          Qed.dd, Qed.pre, Qed.blockquote, Qed.hr, Qed.br, Qed.small, Qed.mark, Qed.sub, Qed.sup,
          Qed.code, Qed.kbd, Qed.abbr, Qed.cite, Qed.time, Qed.del, Qed.ins, Qed.img, Qed.picture,
          Qed.source, Qed.video, Qed.audio, Qed.track, Qed.canvas, Qed.iframe, Qed.details,
          Qed.summary, Qed.dialog, Qed.select, Qed.option, Qed.optgroup, Qed.textarea,
          Qed.fieldset, Qed.legend, Qed.datalist, Qed.output, Qed.progress, Qed.meter, Qed.table,
          Qed.caption, Qed.colgroup, Qed.col, Qed.thead, Qed.tbody, Qed.tfoot, Qed.tr, Qed.td,
          Qed.th,
          Qed.cls, Qed.attr, Qed.role, Qed.rawHtml, Qed.on,
          Qed.onValue, Qed.onClick, Qed.onInput, Qed.onChange, Qed.onCheck, Qed.onKeydown,
          Qed.onKeyup, Qed.onSubmit, Qed.onBlur, Qed.onFocus, Qed.onDoubleClick, Qed.onMouseDown,
          Qed.onMouseUp, Qed.key, Qed.value, Qed.placeholder, Qed.name, Qed.href, Qed.src, Qed.alt,
          Qed.title, Qed.style, Qed.type', Qed.disabled, Qed.required, Qed.checked, Qed.readOnly]
        repeat' split
        all_goals first
          | rfl
          | simp_all [Qed.everyElement, Qed.everyElementL, Qed.attrClasses, Qed.attrRole,
                      Qed.hasOneClass])

end Qed
