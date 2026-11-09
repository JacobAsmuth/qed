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

/-- `invariant name : pred [from init] preserved_by upd`, see the module docs. `using [lemmas]`
    hands extra simp lemmas to the automatic discharger (for a fact it cannot discover on its own);
    the optional `:= proof` supplies a full proof for cases automation cannot close. -/
syntax (name := invariantCmd)
  "invariant " ident " : " term (" from " term)? " preserved_by " ident
    (" using " "[" term,* "]")? (" := " term)? : command

open Lean Elab Tactic

/-- Names the discharger never unfolds: recursors, `match`/`casesOn` auxiliaries, equation
    lemmas, generated codecs, and other compiler internals. -/
private def qedLooksGenerated (n : Name) : Bool :=
  n.isInternalDetail ||
  (match n with
   | .str _ s =>
       ["casesOn", "recOn", "rec", "brecOn", "below", "ibelow", "noConfusion",
        "noConfusionType", "toCtorIdx", "ofNat", "print", "parse", "toSeg", "fromSeg",
        "toJson", "fromJson"].contains s
         || s.startsWith "match_" || s.startsWith "eq_" || s.startsWith "inst"
   | _ => false)

/-- A name the discharger may unfold: a user definition (same module or imported user module,
    excluding `Init`/`Std`/`Lean`/`Qed` and `Style` constants), and not compiler-generated. -/
private def qedIsHelper (env : Environment) (n : Name) : Bool :=
  let mod := match env.getModuleIdxFor? n with | some i => env.header.moduleNames[i]! | none => n
  ![`Init, `Std, `Lean, `Qed].contains mod.getRoot
    && (match env.find? n with | some (.defnInfo d) => !d.type.isConstOf ``Qed.Style | _ => false)
    && !qedLooksGenerated n

/-- Standard size/length lemmas the discharger always offers, so "stays non-empty" and
    size-bound invariants over `push`/`modify`/`set`/`pop`/`map`/`append` close on their own. -/
private def qedBoundaryLemmas : Array Name :=
  #[``Array.size_push, ``Array.size_modify, ``Array.size_set, ``Array.size_pop,
    ``Array.size_map, ``Array.size_append,
    ``List.length_cons, ``List.length_append, ``List.length_map]

/-- Unfold, in the current goal, only the same-module helpers that actually APPEAR in it
    (transitively, to a fixpoint), alongside the boundary size lemmas and any `extra` (`using`)
    lemmas. Helpers feeding fields the property never reads were projected out of the goal by the
    time this runs, so they stay folded; that keeps a failure's residual in the developer's
    vocabulary. Runs once per `cases` goal under `<;>`. The round bound is a loop backstop. -/
elab "qedUnfoldPresent" "[" extra:term,* "]" : tactic => do
  let toLemma (t : TSyntax `term) : TacticM (TSyntax `Lean.Parser.Tactic.simpLemma) :=
    `(Lean.Parser.Tactic.simpLemma| $t:term)
  -- fixed part of the simp set: framework wrappers + boundary size lemmas + the `using` lemmas
  let fixedNames := #[``Qed.ToStep.toStep_model, ``Qed.ToStep.toStep_pair,
                      ``InvTarget.proj_id, ``InvTarget.proj_fst] ++ qedBoundaryLemmas
  let fixedL := (← fixedNames.mapM (fun n => toLemma ⟨(mkIdent n).raw⟩)) ++ (← extra.getElems.mapM toLemma)
  for _ in [0:12] do
    if (← getGoals).isEmpty then return
    let env ← getEnv
    let goal ← instantiateMVars (← getMainTarget)
    let present ← (goal.getUsedConstants.filter (qedIsHelper env)).filterM
      (fun n => return (← getProjectionFnInfo? n).isNone)
    if present.isEmpty then return
    -- one combined array, spliced once (mixing several `$[…],*` with commas breaks when empty)
    let lemmas := (← present.mapM (fun n => toLemma ⟨(mkIdent n).raw⟩)) ++ fixedL
    let ok ← try
        evalTactic (← `(tactic| simp_all only [$[$lemmas],*]))
        pure true
      catch _ => pure false
    unless ok do return

syntax "qedDischargePreserved " "[" term,* "]" ident ident term:max (" from " term)? : tactic

/-- The discharger behind `invariant … preserved_by`, as a tactic elaborator. After `cases` it
    unfolds the transition and framework wrappers, then unfolds *only the helpers that appear
    under the property* (`qedUnfoldPresent`), with the boundary size lemmas and any `using` lemmas
    (`extra`), and closes each branch. On a goal it can't close it reports which arm, the residual
    (in the developer's vocabulary, since irrelevant helpers were never unfolded), and the helpers
    that case still involves, pinned at the invariant's name. -/
elab_rules : tactic
  | `(tactic| qedDischargePreserved [$[$usingL],*] $upd $nm $pred $[from $init]?) => do
    -- If the property is a *named* predicate (`abbrev Card.Safe …`) unfold it first, so the leaves
    -- are plain arithmetic the closers can reach. An inline `fun m => …` isn't an identifier, so
    -- this is skipped and it beta-reduces as before.
    let pred := match pred with | `(($p)) => p | p => p
    let predI : Ident := ⟨pred.raw⟩
    let unfoldPred ← if pred.raw.isIdent
      then `(tactic| try simp only [$predI:ident] at *)
      else `(tactic| skip)
    let toLemma (t : TSyntax `term) : TacticM (TSyntax `Lean.Parser.Tactic.simpLemma) :=
      `(Lean.Parser.Tactic.simpLemma| $t:term)
    let closerL := (← qedBoundaryLemmas.mapM (fun n => toLemma ⟨(mkIdent n).raw⟩))
                     ++ (← usingL.mapM toLemma)
    -- Unfold the transition and wrappers (projecting away fields the property ignores), then unfold
    -- only the helpers that survived into the goal, split each `if`/`match`, and close every leaf
    -- all-or-nothing (`<;> done`), wrapped in `try` so an arm it can't close is left as a goal.
    let stepTac ← `(tactic|
      (intro m msg h;
       $unfoldPred:tactic;
       cases msg <;>
         (try simp_all only [$upd:ident, Qed.ToStep.toStep_model, Qed.ToStep.toStep_pair,
                             InvTarget.proj_id, InvTarget.proj_fst]) <;>
         qedUnfoldPresent [$[$usingL],*] <;>
         (try ((repeat' split) <;>
                (first | rfl | omega | assumption
                       | (simp_all [$[$closerL],*] <;> omega)   -- branch condition / implication, then arith
                       | (simp_all [$[$closerL],*] <;> done) | trivial)))))
    match init with
    | some initT =>
        let initI : Ident := ⟨initT.raw⟩
        let unfoldInit ← if initT.raw.isIdent
          then `(tactic| try simp only [$initI:ident] at *)
          else `(tactic| skip)
        evalTactic (← `(tactic|
          (refine And.intro ?init ?step;
           case init =>
             $unfoldPred:tactic
             $unfoldInit:tactic
             qedUnfoldPresent [$[$usingL],*]
             try ((repeat' split) <;>
                    (first | rfl | decide | omega | assumption
                           | (simp_all [$[$closerL],*] <;> omega)
                           | (simp_all [$[$closerL],*] <;> decide)
                           | (simp_all [$[$closerL],*] <;> done) | trivial));
           case step => $stepTac:tactic)))
    | none =>
        evalTactic stepTac
    let goals ← getUnsolvedGoals
    unless goals.isEmpty do
      let mut body : MessageData := m!""
      for g in goals do
        body := body ++ (← g.withContext do
          let tag ← g.getTag
          -- pretty-print *inside* the goal's context (so its hyps resolve), then drop the `✝`
          -- daggers Lean marks cleared/inaccessible binders with, noise in a user-facing message.
          let ty ← instantiateMVars (← g.getType)
          let tgt := (← Meta.ppExpr ty).pretty.replace "✝" ""
          -- the same-module helpers this stuck goal still mentions (dev vocabulary, what to give a fact about)
          let env ← getEnv
          let present ← (ty.getUsedConstants.filter (qedIsHelper env)).filterM
            (fun n => return (← getProjectionFnInfo? n).isNone)
          let involves := if present.isEmpty then m!"" else m!"\n    (still involves: {present.toList})"
          pure m!"\n  • case `{tag}` still needs:  {tgt}{involves}")
      throwErrorAt nm m!"invariant `{nm.getId}` isn't preserved by `{upd.getId}`, the automation \
        couldn't close every message.\n{body}\n\nIf the property is true here, the prover is likely \
        missing a fact: supply it with `… preserved_by {upd.getId} using [yourLemma]`, or prove the \
        case with `:= by`. If a branch can actually violate the property, fix that branch of \
        `{upd.getId}`, or weaken the property to what it guarantees."

macro_rules
  | `(invariant $name:ident : $pred from $init preserved_by $upd:ident using [$_ls,*] := $pf:term) =>
    `(theorem $name:ident : ($pred) ($init) ∧ ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(invariant $name:ident : $pred from $init preserved_by $upd:ident := $pf:term) =>
    `(theorem $name:ident : ($pred) ($init) ∧ ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(invariant $name:ident : $pred from $init preserved_by $upd:ident using [$ls,*]) =>
    `(theorem $name:ident : ($pred) ($init) ∧ ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        qedDischargePreserved [$ls,*] $upd $name ($pred) from $init)
  | `(invariant $name:ident : $pred from $init preserved_by $upd:ident) =>
    `(theorem $name:ident : ($pred) ($init) ∧ ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        qedDischargePreserved [] $upd $name ($pred) from $init)
  | `(invariant $name:ident : $pred preserved_by $upd:ident using [$_ls,*] := $pf:term) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(invariant $name:ident : $pred preserved_by $upd:ident := $pf:term) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := $pf)
  | `(invariant $name:ident : $pred preserved_by $upd:ident using [$ls,*]) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        qedDischargePreserved [$ls,*] $upd $name ($pred))
  | `(invariant $name:ident : $pred preserved_by $upd:ident) =>
    `(theorem $name:ident : ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($upd m msg)) := by
        qedDischargePreserved [] $upd $name ($pred))

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

/-- Does `h` contain at least one element carrying `role r`? -/
def hasRole (r : String) (h : Html msg) : Bool :=
  !everyElement (fun _ a => !(attrRole a == some r)) h

/-- Does `h` contain at least one `<tag>` element? -/
def hasTag (tag : String) (h : Html msg) : Bool :=
  !everyElement (fun t _ => !(t == tag)) h

/-- Does this element carry the class of *exactly* one of `styles`? Filtering the element's classes
    against `styles` reduces by reflexivity (`s.className == s.className`) without unfolding `Style`
    hashes, while rejecting elements that carry zero or multiple classes from `styles`. -/
def hasOneClass (styles : List Style) (a : List (Attr msg)) : Bool :=
  let cs := attrClasses a
  (cs.filter (fun c => (styles.map (·.className)).contains c)).length == 1

/-- Every element tagged `role r` carries the class of one of `styles`, pair with the `role`
    attribute (`<button role="toggle" …>…</button>`). The predicate for `… holds_in view`. -/
def roleHasOneOf (r : String) (styles : List Style) : Html msg → Bool :=
  everyElement (fun _ a => !(attrRole a == some r) || hasOneClass styles a)

/-- Every `<tag>` element carries the class of one of `styles` (no marker needed). -/
def tagHasOneOf (tag : String) (styles : List Style) : Html msg → Bool :=
  everyElement (fun t a => !(t == tag) || hasOneClass styles a)

/-! Relational rules, relate the styles of *different* elements. `roleHas` is the single-element
    query; `both`/`either` combine queries (AND/OR), and `exactlyOne` / `exactlyOneOf` package
    mutually-exclusive groups. Every role query also requires `hasRole r` (`anyElement`), so a
    misspelled or missing role fails to compile instead of passing vacuously. -/

/-- The element(s) tagged `role r` exist and carry `style`. The single-element building block. -/
def roleHas (r : String) (style : Style) (h : Html msg) : Bool :=
  hasRole r h &&
  everyElement (fun _ a => !(attrRole a == some r) || (attrClasses a).contains style.className) h

/-- The element(s) tagged `role r` exist, carry `chosen`, and do not carry `excluded`. -/
def roleHasOnly (r : String) (chosen excluded : Style) (h : Html msg) : Bool :=
  roleHas r chosen h && roleHasOneOf r [chosen, excluded] h

/-- Both view predicates hold (AND): `both (roleHas "a" x) (roleHas "b" y)`. -/
def both (p q : Html msg → Bool) : Html msg → Bool := fun h => p h && q h
/-- Either view predicate holds (OR): `either (roleHas "a" x) (roleHas "b" y)`. -/
def either (p q : Html msg → Bool) : Html msg → Bool := fun h => p h || q h

/-- Exactly one of two role-tagged elements is styled `on` and the other `off` (and neither carries
    both styles simultaneously). -/
def exactlyOne (roleA roleB : String) (on off : Style) : Html msg → Bool :=
  either (both (roleHasOnly roleA on off) (roleHasOnly roleB off on))
         (both (roleHasOnly roleA off on) (roleHasOnly roleB on off))

/-- All role-tagged elements in `roles` exist and carry `off` (and not `on`). -/
def allRolesOff : List String → Style → Style → Html msg → Bool
  | [],      _,  _,   _ => true
  | r :: rs, on, off, h => roleHasOnly r off on h && allRolesOff rs on off h

/-- Exactly one role in `roles` is styled `on` and all others are styled `off`. -/
def exactlyOneOf (roles : List String) (on off : Style) (h : Html msg) : Bool :=
  let rec go (before : List String) : List String → Bool
    | []      => false
    | r :: rs =>
        (allRolesOff before on off h && roleHasOnly r on off h && allRolesOff rs on off h)
          || go (r :: before) rs
  go [] roles

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

/-- Unfold user view helpers that appear in the current styling goal (keeping keyed component
    `.view` boundaries intact so `for_each … holds_in` can match the child's contract). -/
elab "qedUnfoldViewHelpers" : tactic => do
  for _ in [0:6] do
    if (← getGoals).isEmpty then return
    let env ← getEnv
    let present ← ((← instantiateMVars (← getMainTarget)).getUsedConstants.filter fun n =>
        qedIsHelper env n && !(n.getString! == "view" && env.contains (n.getPrefix ++ `keyOf))).filterM
      fun n => return (← getProjectionFnInfo? n).isNone
    if present.isEmpty then return
    let lemmas ← present.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
    try evalTactic (← `(tactic| simp only [$[$lemmas],*])) catch _ => return

/-- When a view styles an `N`-ary group with `if x == .a …` per element instead of a single
    `match x`, `split` produces branches whose hypotheses constrain an enum `x` (including a
    helper/projection application like `activeSection m.route`) across its constructors.
    Generalizing and case-splitting `x` closes those branches without disturbing real failures. -/
elab "qedCloseExhaustiveEnum" : tactic => withMainContext do
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let inner := match ty with | .app (.const ``Not _) t => t | t => t
    let lhs? := match inner with
      | .app (.app (.app (.const ``Eq _) _) (.app (.app (.app (.app (.const ``BEq.beq _) _) _) lhs) _)) _ => some lhs
      | .app (.app (.app (.const ``Eq _) _) lhs) _ => some lhs
      | _ => none
    if let some lhs := lhs? then
      try
        let lhsStx ← PrettyPrinter.delab lhs
        evalTactic (← `(tactic| (generalize $lhsStx:term = _qed_enum_x at *; cases _qed_enum_x <;> (simp_all; try decide); done)))
        return
      catch _ => pure ()

/-- Reduce a styling goal `pred (view m) = true`: unfold the view, user view helpers, `View`
    template combinators, and every `Qed.Notation` combinator to `Html`/`Attr` constructors, split
    each `if`/`match`, and close the static leaves, leaving any *dynamic-list* residual
    (`everyElementL P (cards.map …)`) for the caller. -/
syntax "qedStyleReduce " ident : tactic
macro_rules
  | `(tactic| qedStyleReduce $view:ident) =>
    `(tactic|
      (try simp only [$view:ident];
       qedUnfoldViewHelpers;
       simp only [Qed.roleHasOneOf, Qed.tagHasOneOf, Qed.roleHas, Qed.roleHasOnly,
         Qed.hasRole, Qed.hasTag, Qed.both, Qed.either, Qed.exactlyOne,
         Qed.allRolesOff, Qed.exactlyOneOf, Qed.exactlyOneOf.go, Qed.hasOneClass,
         Qed.everyElement, Qed.everyElementL, Qed.attrClasses, Qed.attrRole,
         Qed.View.render, Qed.View.renderEach, Qed.View.mapScope, Qed.View.mapScopeEach,
         Qed.VAttr.eval, Qed.VAttr.mapScope, Qed.View.showIf, Qed.View.ofHtml,
         Qed.V.el, Qed.V.text, Qed.V.dyn, Qed.V.ifElse, Qed.V.showIf, Qed.V.static, Qed.V.dynNode,
         Qed.text, Qed.lazy, Qed.el, Qed.link, Qed.linkTo, Qed.styleSheet, Qed.theme,
         Qed.cls, Qed.attr, Qed.role, Qed.rawHtml, Qed.on,
         Qed.onValue, Qed.onClick, Qed.onInput, Qed.onChange, Qed.onCheck, Qed.onKeydown,
         Qed.onKeyup, Qed.onSubmit, Qed.onBlur, Qed.onFocus, Qed.onDoubleClick, Qed.onMouseDown,
         Qed.onMouseUp, Qed.key, Qed.value, Qed.placeholder, Qed.name, Qed.href, Qed.ToHref.toHref,
         Qed.src, Qed.alt, Qed.title, Qed.style, Qed.type', Qed.disabled, Qed.required,
         Qed.checked, Qed.readOnly];
       repeat' split;
       all_goals (first
         | rfl
         | decide
         | (simp_all [Qed.everyElement, Qed.everyElementL,
                      Qed.attrClasses, Qed.attrRole, Qed.hasOneClass];
            try decide;
            try omega;
            try qedCloseExhaustiveEnum))))

/-- `invariant name : pred holds_in view (assuming modelInv)?`, `pred : Html msg → Bool` holds of
    the view for every model (or every model satisfying `modelInv`). -/
syntax (name := invariantView)
  "invariant " ident " : " term " holds_in " ident (" assuming " term:max)? (" := " term)? : command

/-- The discharger behind `invariant … holds_in`, as a tactic elaborator: unfold the view and
    every `Qed.Notation` combinator down to `Html`/`Attr` constructors, verify non-vacuity for
    `roleHasOneOf`/`tagHasOneOf`, split each `if`/`match`, and close every leaf. -/
elab "qedDischargeStyling" view:ident nm:ident predLit:str : tactic => do
  evalTactic (← `(tactic| (intro m; try intro _qed_h_assume)))
  withMainContext do
    for ldecl in (← getLCtx) do
      if ldecl.userName == `_qed_h_assume then
        if let .const c _ := (← instantiateMVars ldecl.type).getAppFn then
          try evalTactic (← `(tactic| simp only [$(mkIdent c):ident] at *)) catch _ => pure ()
    if let some (_, lhs, _) := (← instantiateMVars (← getMainTarget)).eq? then
      let (fn, args) := (lhs.getAppFn, lhs.getAppArgs)
      if (fn.isConstOf ``Qed.roleHasOneOf || fn.isConstOf ``Qed.tagHasOneOf) && args.size == 4 then
        let chk := mkIdent (if fn.isConstOf ``Qed.roleHasOneOf then ``Qed.hasRole else ``Qed.hasTag)
        evalTactic (← `(tactic| (suffices $chk $(← PrettyPrinter.delab args[1]!) ($view m) = true ∧ _ from this.2; constructor)))
  evalTactic (← `(tactic| all_goals qedStyleReduce $view))
  let goals ← getUnsolvedGoals
  unless goals.isEmpty do
    let mut body : MessageData := m!""
    for g in goals do
      body := body ++ (← g.withContext do
        let fmt ← Meta.ppExpr (← instantiateMVars (← g.getType))
        let s := (fmt.pretty.replace "✝" "").trimmed
        pure (if s == "False" then m!"" else m!"\n  • the view still has to satisfy:  {s}"))
    throwErrorAt nm m!"styling invariant `{nm.getId}` doesn't hold for every model, \
      `{predLit.getString}` is false for some `{view.getId} m`.{body}\n\nSome element the rule \
      constrains isn't carrying one of the required style classes (or no element with that role/tag \
      is rendered). Check that the `role`/tag it matches exists and gets one of the styles passed \
      to `roleHasOneOf`/`tagHasOneOf` in every branch of `{view.getId}`. If the view is routed \
      through `App.view`/`View.render` rather than a plain `Model → Html`, prove it with:  \
      invariant {nm.getId} : … holds_in {view.getId} := by …"

open Lean Elab Command Term Meta Lean.PrettyPrinter in
/-- Extract the model predicate `P` from a `preserved_by` (or `from init preserved_by`) theorem. -/
def extractInvPred (id : Ident) : TermElabM (TSyntax `term) := do
  let cTy := (← getConstInfo (← realizeGlobalConstNoOverload id)).type
  let stepTy := if cTy.isAppOfArity ``And 2 then cTy.appArg! else cTy
  forallTelescope stepTy fun args _ => do
    if args.size < 2 then throwErrorAt id
      "`{id}` doesn't look like a `… preserved_by …` invariant, so its predicate can't \
       be inferred, write it explicitly (`<pred> for_each … preserved_by … using {id}`)."
    delab (← mkLambdaFVars #[args[0]!] (← inferType args[args.size - 1]!)).eta

open Lean Elab Command in
elab_rules : command
  | `(invariant $name:ident : $pred holds_in $view:ident $[assuming $assumeT]? $[ := $pf:term]?) => do
    let predStr := ((pred.raw.reprint).getD "this rule").trimmed
    let prop ← match assumeT with
      | some a =>
          let P ← if a.raw.isIdent then try liftTermElabM (extractInvPred ⟨a.raw⟩) catch _ => pure a else pure a
          `(∀ m, ($P) m → ($pred) ($view m) = true)
      | none => `(∀ m, ($pred) ($view m) = true)
    match pf with
    | some p => elabCommand (← `(theorem $name:ident : $prop := $p))
    | none   => elabCommand (← `(
        set_option linter.unusedSimpArgs false in
        theorem $name:ident : $prop := by
          qedDischargeStyling $view $name $(Syntax.mkStrLit predStr)))

end Qed
