/-
  Qed.Invariant: automatic state-machine invariant proofs.

  You state a property of the model and which transition should preserve it; the
  framework *generates and discharges* the preservation theorem for every message,
  with no hand-written proof. If the automation cannot close a goal this fails to
  compile: we never emit `sorry`, because an honest "you must prove this" beats a
  fake guarantee.

      invariant counterSafe : (fun m => 0 ≤ m.count) preserved_by update

  expands to a machine-checked

      theorem counterSafe : ∀ m msg, 0 ≤ m.count → 0 ≤ (update m msg).count

  This is the property that survives *every* reachable sequence of events, not the
  cases a test happened to cover. The claim itself is small and readable; the proof
  that the code obeys it is the machine's job.

  ## Pure or effectful: same syntax

  `preserved_by` works whether the transition is pure (`Model → Msg → Model`) or
  effectful (`Model → Msg → Model × Cmd Msg`). The next model is projected out of
  the result either way (`InvTarget.proj`), so `update` and `transition` both work:

      invariant streamSafe : (fun m => m.pending = true → 0 < m.turns.size)
        preserved_by transition

  ## When the automation can't close it

  The default discharger handles arithmetic, boolean and `Option` reasoning, and the
  `steps` arm normalisation (`omega`, `simp`, case splits, `decide`). For an
  invariant that needs a lemma it can't guess, typically one quantified over your
  own collections, supply the proof after `:=`. The goal is the generated theorem
  `∀ m msg, pred m → pred (next m msg)`, so a proof opens with `intro m msg h`:

      invariant idsBelowNext : (fun m => ∀ r ∈ m.rows, r.id < m.nextId)
        preserved_by update := by
          intro m msg h
          cases msg <;> simp_all [update] <;> omega

  On failure the unsolved goal is labelled with the offending message constructor
  (Lean's `case` tag), so the error points at exactly the transition arm that breaks
  the property, the signal you (or an agent) act on: fix the update, or weaken the
  claim to what the code actually guarantees.

  Note on `import Lean`: this file imports Lean so the discharger can run as a real tactic
  elaborator (`qedDischargePreserved` / `qedDischargeStyling`) and, on a goal it can't close,
  report *which message broke the property and what was left to prove*, at the source span,
  so the message shows up inline in the editor, not just at `qed build`. This costs nothing at
  runtime: the transpiler emits only the closure reachable from the app's entry decls, and a
  compile-time elaborator is never reachable, so it is tree-shaken out (adding this import left
  the JS bundle byte-identical). The cost is build-time only.
-/
import Qed.Runtime
import Qed.Style
import Lean

namespace Qed

/-- Projects the next *model* out of whatever a transition returns, the model itself
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

/-- `invariant name : pred preserved_by upd`, see the module docs. The optional
    `:= proof` supplies a proof for the cases the default automation can't close. -/
syntax (name := invariantCmd)
  "invariant " ident " : " term " preserved_by " ident (" := " term)? : command

open Lean Elab Tactic

/-- The discharger behind `invariant … preserved_by`, as a tactic elaborator. It runs the
    automation, and on any message arm it can't close it reports *which* arm and *what is left to
    prove* (pinned at the invariant's name, so the editor underlines it), instead of a raw
    `unsolved goals` dump. `upd` is spliced into the unfolding simp set; `nm` names the invariant,
    for the message only. The success path is byte-for-byte the old automation, so passing
    invariants are unaffected; only the *failure* message changes. -/
elab "qedDischargePreserved" upd:ident nm:ident pred:term : tactic => do
  -- If the property is a *named* predicate (`abbrev Card.Safe …`, the way you'd package a
  -- component's contract) unfold it first, so the leaves are plain arithmetic the closers can
  -- reach. An inline `fun m => …` isn't an identifier, so this is skipped and it beta-reduces
  -- as before, passing invariants are unaffected either way.
  let predI : Ident := ⟨pred.raw⟩
  let unfoldPred ← if pred.raw.isIdent
    then `(tactic| try simp only [$predI:ident] at *)
    else `(tactic| skip)
  -- The exact automation the command used to inline: unfold the transition / effect wrappers /
  -- model projection, split each `if`/`match`, and close every leaf, each alternative
  -- all-or-nothing (`<;> done`) and wrapped in `try`, so an arm it can't close is *left* as a
  -- goal rather than throwing; we then turn whatever remains into a readable error.
  evalTactic (← `(tactic|
    (intro m msg h;
     $unfoldPred:tactic;
     cases msg <;>
       (try simp_all only [$upd:ident, Qed.ToStep.toStep_model, Qed.ToStep.toStep_pair,
                           InvTarget.proj_id, InvTarget.proj_fst]) <;>
       (try ((repeat' split) <;>
              (first | rfl | omega | assumption
                     | (simp_all <;> omega)        -- resolve a branch condition / implication, then arith
                     | (simp_all <;> done) | trivial))))))
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let mut body : MessageData := m!""
    for g in goals do
      body := body ++ (← g.withContext do
        let tag ← g.getTag
        -- pretty-print *inside* the goal's context (so its hyps resolve), then drop the `✝`
        -- daggers Lean marks cleared/inaccessible binders with, noise in a user-facing message.
        let fmt ← Meta.ppExpr (← instantiateMVars (← g.getType))
        let tgt := fmt.pretty.replace "✝" ""
        pure m!"\n  • case `{tag}` still needs:  {tgt}")
    throwErrorAt nm m!"invariant `{nm.getId}` isn't preserved by `{upd.getId}`, the automation \
      couldn't close every message.\n{body}\n\nEvery message has to leave the property true; the \
      case(s) above don't. Fix one of:\n  · guard or repair that branch of `{upd.getId}` so the \
      property still holds,\n  · weaken the property to what `{upd.getId}` actually guarantees, \
      or\n  · prove it yourself:  invariant {nm.getId} : … preserved_by {upd.getId} := by …"

macro_rules
  | `(invariant $name:ident : $pred preserved_by $upd:ident := $pf:term) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(invariant $name:ident : $pred preserved_by $upd:ident) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        qedDischargePreserved $upd $name $pred)

/-! ### Styling invariants: the same `invariant`, over the view

A styling rule is a property of the rendered *view*, not a state transition, so it uses
`holds_in` where a model invariant uses `preserved_by`:

    invariant toggleStyled : roleHasOneOf "toggle" [activeStyle, inactiveStyle] holds_in view

expands to a machine-checked

    theorem toggleStyled : ∀ m, roleHasOneOf "toggle" [activeStyle, inactiveStyle] (view m) = true
,
the styling holds for *every* model, not the states a test happened to render. Tag the elements
you want to constrain with the `role "…"` attribute; `roleHasOneOf` / `tagHasOneOf` are the ready
predicates and `everyElement` builds custom ones. The default discharger unfolds the view and the
`Qed.Notation` combinators, splits the view's `if`/`match`, and closes each leaf (a class check
reduces by `x == x`, never by hashing). Supply a proof after `:=` for a view it can't reduce, e.g.
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
/-- `everyElement p h`, does every element in `h` satisfy `p tag attrs`? The basis for a styling
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

/-- Every element tagged `role r` carries the class of one of `styles`, pair with the `role`
    attribute (`<button role="toggle" …>…</button>`). The predicate for `… holds_in view`. -/
def roleHasOneOf (r : String) (styles : List Style) : Html msg → Bool :=
  everyElement (fun _ a => !(attrRole a == some r) || hasOneClass styles a)

/-- Every `<tag>` element carries the class of one of `styles` (no marker needed). -/
def tagHasOneOf (tag : String) (styles : List Style) : Html msg → Bool :=
  everyElement (fun t a => !(t == tag) || hasOneClass styles a)

/-! Relational rules, relate the styles of *different* elements. `roleHas` is the single-element
    query; `both`/`either` combine queries (AND/OR), and `exactlyOne` packages the common "exactly
    one of two is styled on" case. They are stated over *positive* "this element has this style"
    facts, which is what lets them prove with ordinary hashed class names: a positive `x == x`
    membership reduces, whereas a negative "this element does NOT have style Y" would need the two
    styles' class names to be provably distinct, which a content hash cannot give. So express
    "A on XOR B on" as `exactlyOne` (or `(A on ∧ B off) ∨ (A off ∧ B on)` by hand), never as a
    negation. -/

/-- The element(s) tagged `role r` carry exactly `style`. The single-element building block. -/
def roleHas (r : String) (style : Style) : Html msg → Bool :=
  everyElement (fun _ a => !(attrRole a == some r) || (attrClasses a).contains style.className)

/-- Both view predicates hold (AND): `both (roleHas "a" x) (roleHas "b" y)`. -/
def both (p q : Html msg → Bool) : Html msg → Bool := fun h => p h && q h
/-- Either view predicate holds (OR): `either (roleHas "a" x) (roleHas "b" y)`. -/
def either (p q : Html msg → Bool) : Html msg → Bool := fun h => p h || q h

/-- Exactly one of two role-tagged elements is styled `on`, the other `off`, e.g. "exactly one
    tab is active". The positive form `(A on ∧ B off) ∨ (A off ∧ B on)`, so it proves without the
    two styles having to be provably distinct. -/
def exactlyOne (roleA roleB : String) (on off : Style) : Html msg → Bool :=
  either (both (roleHas roleA on) (roleHas roleB off))
         (both (roleHas roleA off) (roleHas roleB on))

/-! ### Lifting a styling contract over a list of children

A parent-owned tag (`<Child state={c} onMsg={…}/>`) renders each child as
`(Child.view c).map wrap` (it relabels the child's messages into the parent's). These lemmas say a
role/class predicate is unaffected by that relabelling, so a parent
styling invariant over a list, "every rendered card is styled", reduces to the child's `holds_in`
contract per card. Behavioural lifting (`for_each … preserved_by`) is automatic; styling lifts over a
list use these as a short `holds_in … := by …`, since the parent *view*'s shape varies too much for a
single generic discharger. `roleHasOneOf_map`/`everyElementL_mapList` are the two you reach for. -/

/-- `Attr.map` leaves the class list unchanged (it only relabels event handlers). -/
theorem attrClasses_map {α β} (f : α → β) (a : List (Attr α)) :
    attrClasses (a.map (Attr.map f)) = attrClasses a := by
  induction a with
  | nil => rfl
  | cons x xs ih => cases x <;> simp_all [attrClasses, Attr.map]

/-- `Attr.map` leaves the `role` marker unchanged. -/
theorem attrRole_map {α β} (f : α → β) (a : List (Attr α)) :
    attrRole (a.map (Attr.map f)) = attrRole a := by
  induction a with
  | nil => rfl
  | cons x xs ih => cases x
                    case attr k v => by_cases hk : k = "data-role" <;>
                                       simp [List.map, Attr.map, attrRole, hk, ih]
                    all_goals simp [List.map, Attr.map, attrRole, ih]

mutual
/-- A tag/attr-only predicate is preserved under `Html.map` (message relabelling), given it agrees on
    a relabelled attribute list, the basis for lifting styling over tag-rendered children. -/
theorem everyElement_map {α β} (f : α → β)
    {pα : String → List (Attr α) → Bool} {pβ : String → List (Attr β) → Bool}
    (hp : ∀ t a, pβ t (a.map (Attr.map f)) = pα t a) :
    (h : Html α) → everyElement pβ (h.map f) = everyElement pα h
  | .text _        => rfl
  | .lazy _ s      => everyElement_map f hp s
  | .element t a k => by simp only [Html.map, everyElement, hp, everyElementL_map f hp k]
/-- `everyElement_map` over a sibling list (mutual recursion gives termination). -/
theorem everyElementL_map {α β} (f : α → β)
    {pα : String → List (Attr α) → Bool} {pβ : String → List (Attr β) → Bool}
    (hp : ∀ t a, pβ t (a.map (Attr.map f)) = pα t a) :
    (l : List (Html α)) → everyElementL pβ (Html.mapChildren f l) = everyElementL pα l
  | []     => rfl
  | c :: cs => by simp only [Html.mapChildren, everyElementL,
                             everyElement_map f hp c, everyElementL_map f hp cs]
end

/-- `everyElementL` over a rendered list: every child of `l.map g` satisfies `p` iff every `g x`
    does, the bridge from a list of child *models* to its rendered subtree. -/
theorem everyElementL_mapList {α β} (p) (g : β → Html α) (l : List β) :
    everyElementL p (l.map g) = true ↔ ∀ x ∈ l, everyElement p (g x) = true := by
  induction l with
  | nil => simp [everyElementL]
  | cons x xs ih => simp [List.map, everyElementL, ih, Bool.and_eq_true]

/-- The styling predicate `roleHasOneOf` survives `Html.map`, so a card's contract over `Card.view`
    transfers to its tag-rendered `(Card.view c).map wrap`. The corollary you apply per card. -/
theorem roleHasOneOf_map {α β} (f : α → β) (r) (styles) (h : Html α) :
    roleHasOneOf r styles (h.map f) = roleHasOneOf r styles h :=
  everyElement_map f (fun _ _ => by simp [attrRole_map, attrClasses_map, hasOneClass]) h

/-- The per-child bridge for the styling lift: a styled child view stays styled after `Html.map`
    relabels its messages, so `everyElement Pβ ((Card.view c).map wrap) = true` follows from the
    child's `holds_in` contract. `everyElement_through_map _ _ hP childContract` closes one rendered card
    (`Pα`/`Pβ` are the same role predicate at the child's and parent's message types). -/
theorem everyElement_through_map {α β} (f : α → β) {Pα : String → List (Attr α) → Bool}
    {Pβ : String → List (Attr β) → Bool} (h : Html α)
    (hP : ∀ t a, Pβ t (a.map (Attr.map f)) = Pα t a) (hc : everyElement Pα h = true) :
    everyElement Pβ (h.map f) = true := by rw [everyElement_map f hP]; exact hc

/-- Reduce a styling goal `pred (view m) = true`: unfold the view and every `Qed.Notation`
    combinator to `Html`/`Attr` constructors, split each `if`/`match`, and close the static leaves,
    leaving any *dynamic-list* residual (`everyElementL P (cards.map …)`) for the caller. Shared by
    the plain `holds_in` discharger and the `for_each … holds_in` lift. (Maintenance: this mirror of
    the element/attribute helpers must list any new one.) -/
syntax "qedStyleReduce " ident : tactic
macro_rules
  | `(tactic| qedStyleReduce $view:ident) =>
    `(tactic|
      (simp only [$view:ident, Qed.roleHasOneOf, Qed.tagHasOneOf, Qed.roleHas, Qed.both,
         Qed.either, Qed.exactlyOne, Qed.hasOneClass,
         Qed.everyElement, Qed.everyElementL, Qed.attrClasses, Qed.attrRole,
         Qed.text, Qed.lazy, Qed.el, Qed.link, Qed.linkTo, Qed.styleSheet, Qed.theme,
         Qed.cls, Qed.attr, Qed.role, Qed.rawHtml, Qed.on,
         Qed.onValue, Qed.onClick, Qed.onInput, Qed.onChange, Qed.onCheck, Qed.onKeydown,
         Qed.onKeyup, Qed.onSubmit, Qed.onBlur, Qed.onFocus, Qed.onDoubleClick, Qed.onMouseDown,
         Qed.onMouseUp, Qed.key, Qed.value, Qed.placeholder, Qed.name, Qed.href, Qed.src, Qed.alt,
         Qed.title, Qed.style, Qed.type', Qed.disabled, Qed.required, Qed.checked, Qed.readOnly];
       repeat' split;
       all_goals (first
         | rfl
         | simp_all [Qed.everyElement, Qed.everyElementL, Qed.attrClasses, Qed.attrRole,
                     Qed.hasOneClass])))

/-- `invariant name : pred holds_in view`, `pred : Html msg → Bool` holds of the view for every
    model. The optional `:= proof` supplies a proof the default discharger can't find. -/
syntax (name := invariantView)
  "invariant " ident " : " term " holds_in " ident (" := " term)? : command

/-- The discharger behind `invariant … holds_in`, as a tactic elaborator: unfold the view and
    every `Qed.Notation` combinator down to `Html`/`Attr` constructors, split each `if`/`match`,
    and close every leaf (a class check reduces by `x == x`, never by hashing). On a leaf it can't
    reduce it reports the unmet obligation at the invariant's name instead of an `unsolved goals`
    dump. `view` is the view function; `nm` names the invariant. The success path is the old
    automation verbatim. (Maintenance: this mirror of the element/attribute helpers must list any
    new one.) -/
elab "qedDischargeStyling" view:ident nm:ident predLit:str : tactic => do
  evalTactic (← `(tactic| (intro m; qedStyleReduce $view)))
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    -- The residual goal is usually just `False` (the class check reduced away), which says nothing
    -- useful, so we quote the *rule the user wrote* instead, and only append a goal line on the
    -- rare occasion it reduced to something more telling than `False`.
    let mut body : MessageData := m!""
    for g in goals do
      body := body ++ (← g.withContext do
        let fmt ← Meta.ppExpr (← instantiateMVars (← g.getType))
        let s := (fmt.pretty.replace "✝" "").trimmed
        pure (if s == "False" then m!"" else m!"\n  • the view still has to satisfy:  {s}"))
    throwErrorAt nm m!"styling invariant `{nm.getId}` doesn't hold for every model, \
      `{predLit.getString}` is false for some `{view.getId} m`.{body}\n\nSome element the rule \
      constrains isn't carrying one of the required style classes. Check that the `role`/tag it \
      matches really gets one of the styles passed to `roleHasOneOf`/`tagHasOneOf` in every branch \
      of `{view.getId}`. If the view is routed through `App.view`/`View.render` rather than a plain \
      `Model → Html`, prove it with:  invariant {nm.getId} : … holds_in {view.getId} := by …"

open Lean in
macro_rules
  | `(invariant $name:ident : $pred holds_in $view:ident := $pf:term) =>
    `(theorem $name:ident : ∀ m, ($pred) ($view m) = true := $pf)
  | `(invariant $name:ident : $pred holds_in $view:ident) => do
    -- carry the rule's source text through to the discharger, so a failure can quote exactly
    -- what was asked for (the reduced goal alone is just `False`).
    let predStr := ((pred.raw.reprint).getD "this rule").trimmed
    `(set_option linter.unusedSimpArgs false in
      theorem $name:ident : ∀ m, ($pred) ($view m) = true := by
        qedDischargeStyling $view $name $(Syntax.mkStrLit predStr))

end Qed
