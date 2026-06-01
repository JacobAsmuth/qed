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
import Qed.Diff
import Qed.Style

namespace Qed

/-- A template attribute: either a `stat`ic attribute (any `Attr`), or one `bind`ed to
    the scope (`σ → Attr msg`) — which covers both a dynamic value (`value="get σ"`) and
    a dynamic event whose message reads the scope (`onClick (.toggle row.id)` inside a
    list row, where `row` is only known per item). The driver re-evaluates `bind` attrs
    on update and leaves `stat` ones alone. -/
inductive VAttr (σ : Type) (msg : Type) where
  /-- A fixed attribute (reuse every `Attr` helper; a `Coe` wraps them silently). -/
  | stat (a : Attr msg)
  /-- A scope-bound attribute, recomputed from the scope when it changes (e.g. a
      scope-dependent event). The driver re-evaluates it on update. -/
  | bind (get : σ → Attr msg)
  /-- A dynamic *value* attribute `attr="get σ"`. Distinguished from `bind` so a list row
      can render it as a *signal* (`signalAttr`) — a value-only update sets it directly,
      no diff. In a scalar element it is just re-applied on update. -/
  | dynVal (attr : String) (get : σ → String)

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
  /-- Two-branch conditional: render `yes` when `cond σ`, else `no`. A flip reconciles
      through the verified `diff` (the slot is replaced), exactly as `showIf` does; while
      `cond` holds steady the active branch value-patches in place. The lift target for a
      native `if c then a else b` in a view. -/
  | ifElse (cond : σ → Bool) (yes no : View σ msg)
  /-- A keyed list: a container `tag` whose rows are produced by the `forEach` combinator
      (which scopes each row's template to its own row type `α`, off this inductive — a
      nested `View α` field would be a non-uniform recursive occurrence the kernel
      rejects). The three driver-facing projections of the model are: `keys` (the row keys
      in order — cheap, drives the structural fast/slow decision), `sigs` (every row's
      dynamic values as `(signalName, value)` — the per-row *signals* that make a
      value-only update O(changed) with no diff and no `childAt`), and `rowsHtml` (the
      keyed `Html` rows, each dynamic leaf a `signalBind` node — used to build and, on a
      *shape* change, reconcile through the verified keyed `diff`). -/
  | keyedList (tag : String) (attrs : List (VAttr σ msg))
      (keys : σ → Array String) (sigs : σ → Array (String × String))
      (rowsHtml : σ → List (Html msg))
  /-- An escape hatch: drop a fully-formed `Html` subtree into a template (e.g. to reuse
      an existing component). It is opaque to the fine-grained path — always rebuilt. -/
  | static (html : Html msg)
  /-- The scope-bound escape hatch: an arbitrary `σ → Html` subtree. Unlike `static` it
      reads the scope, so it carries anything the fine-grained combinators can't express
      (a free-form `match`, a helper call). It is never value-patched — on every update it
      reconciles through the verified `diff` (`stable` is `false` for it), so it inherits
      `diff_apply`'s guarantee. The `view%` macro emits this for view code it can't
      decompose, making "lift what we can, diff the rest" the default. -/
  | dynNode (get : σ → Html msg)

/-- Evaluate a template attribute against a scope. -/
def VAttr.eval (s : σ) : VAttr σ msg → Attr msg
  | .stat a          => a
  | .bind f          => f s
  | .dynVal attr get => .attr attr (get s)

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
    | .ifElse cond y n, s => if cond s then View.render y s else View.render n s
    | .keyedList tag as _ _ rowsHtml, s => .element tag (as.map (VAttr.eval s)) (rowsHtml s)
    | .static h,        _ => h
    | .dynNode get,     s => get s
  /-- Render a list of sibling templates against one scope. -/
  def View.renderEach : List (View σ msg) → σ → List (Html msg)
    | [],      _ => []
    | k :: ks, s => View.render k s :: View.renderEach ks s
end

/-! ### The value-patch path is a full re-render (verified)

The fine-grained driver, away from a `keyedList`, does not rebuild the tree: it walks the
template against the new scope and overwrites only the dynamic text/attributes in place.
`applyValues` is the pure model of that patch — start from the *old* rendered tree
(`render t s`) and reapply the dynamic parts at the new scope `s'`. `stable t s s'` is its
precondition, exactly the driver's value-only fast path: no `keyedList`, and no `showIf`
condition flips between `s` and `s'`. The theorem `applyValues_render` says that under
`stable`, the in-place patch reproduces a full re-render — so the non-list template path
inherits the same "the DOM equals the model's view" guarantee `diff_apply` gives the diff
path. (`keyedList` rows update through signals, outside `render`, so they are excluded.) -/

mutual
  /-- The driver's value-patch as a pure function of the old rendered tree: a `dyn` becomes
      its new text, an element re-evaluates its attributes and recurses, a non-flipping
      `showIf` recurses into the shown branch; everything else is left as built. -/
  def applyValues : View σ msg → σ → Html msg → Html msg
    | .dyn get,              s', _                       => .text (get s')
    | .element _ attrs kids, s', .element tag _ oldKids  =>
        .element tag (attrs.map (VAttr.eval s')) (applyValuesList kids s' oldKids)
    | .showIf cond child,    s', old                     => if cond s' then applyValues child s' old else old
    | .ifElse cond y n,      s', old                     => if cond s' then applyValues y s' old else applyValues n s' old
    | _,                     _,  old                     => old
  def applyValuesList : List (View σ msg) → σ → List (Html msg) → List (Html msg)
    | k :: ks, s', o :: os => applyValues k s' o :: applyValuesList ks s' os
    | _,       _,  _       => []
end

mutual
  /-- Is `t`'s structure the same at `s` and `s'` — no `keyedList`, every `showIf`
      condition unchanged — so a value patch suffices (the driver's fast-path test)? -/
  def stable : View σ msg → σ → σ → Bool
    | .element _ _ kids,  s, s' => stableList kids s s'
    | .showIf cond child, s, s' => (cond s == cond s') && stable child s s'
    | .ifElse cond y n,   s, s' => (cond s == cond s') && (if cond s then stable y s s' else stable n s s')
    | .keyedList ..,      _, _  => false
    | .dynNode _,         _, _  => false
    | _,                  _, _  => true
  def stableList : List (View σ msg) → σ → σ → Bool
    | k :: ks, s, s' => stable k s s' && stableList ks s s'
    | [],      _, _  => true
end

mutual
  /-- **Correctness:** under `stable`, patching the old rendered tree in place reproduces
      a full re-render at the new scope. -/
  theorem applyValues_render (t : View σ msg) (s s' : σ) :
      stable t s s' = true → applyValues t s' (View.render t s) = View.render t s' := by
    intro h
    cases t with
    | text c        => simp [View.render, applyValues]
    | dyn get       => simp [View.render, applyValues]
    | static hh     => simp [View.render, applyValues]
    | keyedList _ _ _ _ _ => simp [stable] at h
    | dynNode get   => simp [stable] at h
    | element tag attrs kids =>
        simp only [View.render, applyValues]
        rw [applyValuesList_render kids s s' (by simpa [stable] using h)]
    | showIf cond child =>
        simp only [stable, Bool.and_eq_true] at h
        have hc : cond s = cond s' := by simpa using h.1
        simp only [View.render, applyValues, hc]
        split
        · exact applyValues_render child s s' h.2
        · rfl
    | ifElse cond y no =>
        simp only [stable, Bool.and_eq_true] at h
        have hc : cond s = cond s' := by simpa using h.1
        have hbr := h.2; rw [hc] at hbr
        simp only [View.render, applyValues, hc]
        split <;> rename_i hcond
        · simp only [hcond, if_true] at hbr
          exact applyValues_render y s s' hbr
        · simp only [hcond, Bool.false_eq_true, if_false] at hbr
          exact applyValues_render no s s' hbr
  /-- The sibling-list analogue. -/
  theorem applyValuesList_render (ts : List (View σ msg)) (s s' : σ) :
      stableList ts s s' = true → applyValuesList ts s' (View.renderEach ts s) = View.renderEach ts s' := by
    intro h
    cases ts with
    | nil       => simp [View.renderEach, applyValuesList]
    | cons k ks =>
        simp only [stableList, Bool.and_eq_true] at h
        simp only [View.renderEach, applyValuesList]
        rw [applyValues_render k s s' h.1, applyValuesList_render ks s s' h.2]
end

/-! ### The unconditional per-subtree update step

`applyValues_render` needs `stable`. The driver's real update of any one subtree is total:
fine-grained value patch when the structure is stable, the verified `diff` otherwise. -/

/-- The complete update step for one (sub)tree: a fine-grained value patch when the shape is
    stable, else the verified `diff`. Total — defined for every `t, s, s'`. -/
def patch (t : View σ msg) (s s' : σ) (old : Html msg) : Html msg :=
  if stable t s s' then applyValues t s' old else applyPatch (diff old (View.render t s')) old

/-- **Every (sub)tree, unconditionally.** Applying the update step to the old rendered tree
    reproduces a full re-render — scalar, `ifElse`, `dynNode`, and shape change alike, with no
    `stable` precondition. The stable branch is `applyValues_render`; the rest is `diff_apply`. -/
theorem patch_render (t : View σ msg) (s s' : σ) :
    patch t s s' (View.render t s) = View.render t s' := by
  unfold patch
  split
  · rename_i hs; exact applyValues_render t s s' hs
  · exact diff_apply (View.render t s) (View.render t s')

/-! ### Structural fingerprint for fine-grained list rows

A `forEach` row whose dynamic leaves are all signals updates in place via `setSignal`. But a
row part that `renderSig` bakes *statically* — an `ifElse`/`dynNode`/nested `keyedList`, or a
`showIf` flip — is invisible to the signal path, so a change there would be silently missed.
`collectShape` fingerprints exactly those parts; `forEach` folds the fingerprint into the row's
reconciliation key, so such a change becomes a *key* change and reconciles through the verified
keyed `diff` (`diffKeyed_apply`). Rows with no such parts (`hasOpaque` is `false`) keep the
plain key and the untouched signal fast-path. -/

mutual
  /-- Does this row template contain structure `renderSig` renders statically (so a change in
      it can't be a signal and must reconcile through the key)? -/
  def View.hasOpaque : View σ msg → Bool
    | .text _           => false
    | .dyn _            => false
    | .element _ _ kids => View.hasOpaqueList kids
    | .showIf _ _       => true     -- a shown↔hidden flip is structural, not a signal
    | .ifElse ..        => true
    | .keyedList ..     => true
    | .static _         => false
    | .dynNode _        => true
  def View.hasOpaqueList : List (View σ msg) → Bool
    | []      => false
    | k :: ks => k.hasOpaque || View.hasOpaqueList ks
end

mutual
  /-- A string fingerprint of the row's statically-rendered parts: empty for the signal leaves
      (`dyn`/`dynAttr`, handled by `setSignal`), the full rendered content for the opaque parts
      (`ifElse`/`dynNode`/nested `keyedList`) and the branch selector for a `showIf`. Differs
      iff a change would be missed by the signal path — exactly when the key must change. -/
  def View.collectShape : View σ msg → σ → String
    | .text _,          _ => ""
    | .dyn _,           _ => ""
    | .element _ _ kids, s => View.collectShapeList kids s
    | .showIf cond child, s => if cond s then "1" ++ View.collectShape child s else "0"
    | .ifElse cond y no, s =>     -- only the branch SELECTOR is structural now; the branch's own
                                  -- leaves are signals, so a value change there needs no reconcile
        if cond s then "1" ++ View.collectShape y s else "0" ++ View.collectShape no s
    | .keyedList tag as _ _ rowsHtml, s =>
        "{" ++ Html.render (.element tag (as.map (VAttr.eval s)) (rowsHtml s)) ++ "}"
    | .static _,        _ => ""
    | .dynNode get,     s => "<" ++ Html.render (get s) ++ ">"
  def View.collectShapeList : List (View σ msg) → σ → String
    | [],      _ => ""
    | k :: ks, s => View.collectShape k s ++ View.collectShapeList ks s
end

/-! ### Row instrumentation for fine-grained lists

    A list row's dynamic leaves become *signals*: `collectDyn` lists a row template's
    `dyn` projections in pre-order (so each gets a stable index), and `renderSig` renders
    the row with each `dyn` as a `signalBind` node named `key#i` (its text pushed by the
    driver via `setSignal`, never through a diff). The two walk in the same pre-order, so
    index `i` names the same binding in both — that is what lets a value-only update set
    just the changed rows' signals with no `childAt` and no reconcile. -/

/-- A row's dynamic *value-attribute* projections (in attribute order). -/
def dynValGets (attrs : List (VAttr σ msg)) : List (σ → String) :=
  attrs.filterMap fun | .dynVal _ get => some get | _ => none

mutual
  /-- A row template's dynamic projections, in pre-order (index = signal suffix): an
      element's `dynVal` attributes first, then its children's `dyn` text. -/
  def View.collectDyn : View σ msg → List (σ → String)
    | .text _               => []
    | .dyn get              => [get]
    | .element _ attrs kids => dynValGets attrs ++ View.collectDynList kids
    | .showIf _ child       => View.collectDyn child
    | .ifElse _ y no        => View.collectDyn y ++ View.collectDyn no   -- both branches: a fixed
                                                                          -- index range per branch
    | .keyedList ..         => []     -- a nested list owns its own signals
    | .static _             => []
    | .dynNode _            => []     -- the diff escape hatch carries no row signals
  def View.collectDynList : List (View σ msg) → List (σ → String)
    | []      => []
    | k :: ks => View.collectDyn k ++ View.collectDynList ks
end

/-- Render a row element's attributes, turning each `dynVal` into a `signalAttr` named
    `key#n` (its value pushed by `setSignal`); static/bound attrs evaluate normally.
    Threads the binding index in the same order `collectDyn` walks (attributes first). -/
def renderSigAttrs (s : σ) (pre : String) : List (VAttr σ msg) → Nat → List (Attr msg) × Nat
  | [],        n => ([], n)
  | va :: rest, n =>
      let (a, n1) := match va with
        | .dynVal attr get => (Attr.signalAttr s!"{pre}#{n}" attr (get s), n + 1)
        | other            => (VAttr.eval s other, n)
      let (as, n2) := renderSigAttrs s pre rest n1
      (a :: as, n2)

mutual
  /-- Render a row against its data: each `dyn` a `signalBind` node `key#i`, each `dynVal`
      attribute a `signalAttr` `key#i` — all filled by `setSignal`. `n` is the running
      binding index, threaded so hidden `showIf` branches still consume their indices,
      keeping the naming identical to `collectDyn`. -/
  def View.renderSig : View σ msg → σ → String → Nat → Html msg × Nat
    | .text s,          _, _,   n => (.text s, n)
    | .dyn get,         s, pre, n => (.element "span" [.signalBind s!"{pre}#{n}"] [.text (get s)], n + 1)
    | .element tag attrs kids, s, pre, n =>
        let (attrs', n1) := renderSigAttrs s pre attrs n
        let (cs, n2) := View.renderSigList kids s pre n1
        (.element tag attrs' cs, n2)
    | .showIf cond child, s, pre, n =>
        if cond s then View.renderSig child s pre n
        else (.text "", n + (View.collectDyn child).length)
    | .ifElse cond y no, s, pre, n =>
        -- render the active branch WITH signals from its reserved index range, then reserve the
        -- inactive branch's range so leaf indices never shift across a flip (mirrors `showIf`).
        if cond s then
          let (h, n1) := View.renderSig y s pre n
          (h, n1 + (View.collectDyn no).length)
        else
          let (h, n2) := View.renderSig no s pre (n + (View.collectDyn y).length)
          (h, n2)
    | .keyedList tag as _ _ rowsHtml, s, _, n =>
        (.element tag (as.map (VAttr.eval s)) (rowsHtml s), n)   -- nested list: structure only
    | .static h,        _, _,   n => (h, n)
    | .dynNode get,     s, _,   n => (get s, n)
  def View.renderSigList : List (View σ msg) → σ → String → Nat → List (Html msg) × Nat
    | [],      _, _,   n => ([], n)
    | k :: ks, s, pre, n =>
        let (h,  n')  := View.renderSig k s pre n
        let (hs, n'') := View.renderSigList ks s pre n'
        (h :: hs, n'')
end

/-! ### Surface combinators

    Mirrors `Qed.Notation`, in namespace `V` so a template module `open Qed.V`s them
    without colliding with the `Html` versions. Every `Attr` helper (`cls`, `onClick`,
    …) coerces into a `VAttr` via the instance below, so attributes read identically to
    plain `Html`; `dynAttr` adds a scope-bound value. -/
namespace V

/-- Any static `Attr` is a template attribute. -/
instance : Coe (Attr msg) (VAttr σ msg) := ⟨.stat⟩
/-- A scoped `Style` applies its class, in a template too. -/
instance : Coe Style (VAttr σ msg) := ⟨fun s => .stat (.cls s.className)⟩

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
/-- A dynamic attribute value bound to the scope: `dynAttr "value" (·.draft)`. In a list
    row it becomes a fine-grained signal; in a scalar element it is re-applied on update. -/
def dynAttr (name : String) (get : σ → String) : VAttr σ msg := .dynVal name get
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
/-- Render `yes` while `cond` holds, else `no` (the lift target for `if … then … else …`). -/
def ifElse (cond : σ → Bool) (yes no : View σ msg) : View σ msg := .ifElse cond yes no
/-- The diff escape hatch: an arbitrary scope-dependent `Html` subtree (the lift target
    for view code the macro can't decompose). Reconciled through the verified `diff`. -/
def dynNode (get : σ → Html msg) : View σ msg := .dynNode get

/-- A keyed list: `forEach "ul" (·.rows) (·.id) rowTemplate`. The container is `tag`; each
    item of `items σ` renders `child` scoped to *that row*, keyed by `key`. Each row's
    dynamic leaves become signals named `key#i`, so the driver updates a changed row with a
    direct `setSignal` (no `childAt`, no diff); only a change in the *set/order of keys*
    reconciles through the verified keyed `diff`. The row template is fully typed at its own
    scope `α` and consumed here, off the `View σ` inductive. -/
def forEach {α : Type} (tag : String) (items : σ → Array α) (key : α → String)
    (child : View α msg) (attrs : List (VAttr σ msg) := []) (sigPrefix : String := "") : View σ msg :=
  -- the row's dynamic projections, collected once (index = signal suffix)
  let projs := View.collectDyn child
  -- the signal namespace for this list. Signals are a process-wide name→node map, so two lists
  -- over the same row keys would collide; `sigPrefix` (filled per-list by `view%`) keeps them
  -- disjoint. Defaults to "" so a lone direct `forEach` is unchanged.
  let skey : α → String := fun a => sigPrefix ++ key a
  -- the reconciliation key. If the row bakes any structure statically (`ifElse`/`dynNode`/…),
  -- fold a fingerprint of it in, so a change there reconciles through the verified keyed
  -- `diff` instead of being missed by the signal path. Plain rows keep the bare key.
  let rkey : α → String :=
    if View.hasOpaque child then (fun a => s!"{key a} {View.collectShape child a}") else key
  .keyedList tag attrs
    (fun s => (items s).map rkey)                             -- Array: the value path stays
    (fun s => (items s).flatMap fun a =>                      -- tail-safe at any list size
      (projs.mapIdx fun i p => (s!"{skey a}#{i}", p a)).toArray)  -- signals namespaced per list
    (fun s => ((items s).map fun a => withKey (rkey a) (View.renderSig child a (skey a) 0).1).toList)

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

/-! ### `view%` — write a template like an ordinary view

`view% fun m => …` lets a fine-grained template read like an ordinary `Model → Html`
view: native control flow is lifted into the reactive combinators, so the dynamic parts
need no special syntax.

    view% fun m =>
      div [cls "page"] [
        h1 [] [text s!"Hello, {m.name}"],     -- interpolation → `dyn (fun m => …)`
        if m.count == 0                         -- a model-driven `if` → `ifElse`
          then p [] "nothing yet"
          else p [] [text s!"count is {m.count}"],
        forEach "ul" (·.todos) (·.id) row       -- lists stay explicit (need a key)
      ]

What it lifts:
* `text e` whose `e` mentions `m` → `dyn (fun m => e)` (also `s!"…{m.x}…"`).
* `if c then a else b` whose `c` mentions `m`, when a branch is a view → `ifElse`.

Anything else stays as written, so attributes (`dynAttr (·.f)`) and lists (`forEach`)
keep their explicit projections, and any subtree the macro can't decompose can be dropped
in verbatim with `dynNode (fun m => …)` (reconciled by the verified `diff`). -/
open Lean in
/-- Is `m` the root of `n` (so `n` is `m` or `m.field…`)? -/
private partial def viewRootedAt (m : Name) : Name → Bool
  | n@(.str p _) => n == m || viewRootedAt m p
  | n@(.num p _) => n == m || viewRootedAt m p
  | .anonymous   => m == .anonymous

open Lean in
/-- Does this syntax mention the identifier `m` (as `m` or `m.field…`)? -/
private partial def viewMentions (m : Name) : Syntax → Bool
  | .ident _ _ n _ => viewRootedAt m n
  | .node _ _ args => args.any (viewMentions m)
  | _              => false

/-- The element/leaf formers a view is built from. Used only as a heuristic: an `if`
    branch headed by one of these (or a bare string, which coerces to text) is treated as
    a view, so a model-driven `if` in *view* position lifts to `ifElse` while one in
    *attribute* position (`cls (if … then "a" else "b")`) is left alone. A misclassification
    is only ever a type error, never wrong behavior — Lean's checker is the backstop. -/
private def viewFormers : List String :=
  ["text", "dyn", "el", "div", "span", "button", "p", "h1", "h2", "h3", "ul", "li",
   "label", "input", "a", "nav", "header", "footer", "section", "article", "strong",
   "em", "img", "formEl", "table", "thead", "tbody", "tr", "td", "th",
   "ifElse", "showIf", "forEach", "static", "dynNode"]

open Lean in
/-- The leftmost identifier in function position (`div [..] [..]` ↦ `div`). -/
private partial def headIdent? : Syntax → Option Name
  | .ident _ _ n _ => some n
  | .node _ _ args => if 0 < args.size then headIdent? args[0]! else none
  | _ => none

/-- The final string component of a name (`Qed.V.div` ↦ `"div"`). -/
private def lastStr? : Lean.Name → Option String
  | .str _ s => some s
  | _        => none

open Lean in
/-- Does this syntax look like a view (so a model-driven `if` around it is a view `if`)? -/
private def looksLikeView (stx : Syntax) : Bool :=
  if stx.isStrLit?.isSome then true
  else match headIdent? stx with
    | some n => match lastStr? n.eraseMacroScopes with
                | some s => viewFormers.contains s
                | none   => false
    | none   => false

/-- Single-backtick name literals for the syntax kinds we inspect (a `Name`, not a checked
    constant reference — so this stays usable without `import Lean`). -/
private def kApp      : Lean.Name := `Lean.Parser.Term.app
private def kParen    : Lean.Name := `Lean.Parser.Term.paren
private def kFun      : Lean.Name := `Lean.Parser.Term.fun
private def kBasicFun : Lean.Name := `Lean.Parser.Term.basicFun
private def kMatch    : Lean.Name := `Lean.Parser.Term.match
private def kList     : Lean.Name := `«term[_]»

/-- Drop a name's final component (`m.todos.map` ↦ `m.todos`). -/
private def dropLastComp : Lean.Name → Lean.Name
  | .str p _   => p
  | .num p _   => p
  | .anonymous => .anonymous

/-- A string-valued attribute helper ↦ the HTML attribute it sets. -/
private def stringAttrName? : String → Option String
  | "cls"         => some "class"
  | "value"       => some "value"
  | "placeholder" => some "placeholder"
  | "style"       => some "style"
  | "href"        => some "href"
  | "src"         => some "src"
  | "alt"         => some "alt"
  | "title"       => some "title"
  | "type'"       => some "type"
  | "name"        => some "name"
  | _             => none

/-- An event helper ↦ its scope-bound (primed) form. -/
private def eventPrime? : String → Option String
  | "onClick" => some "onClick'"
  | "onInput" => some "onInput'"
  | "onCheck" => some "onCheck'"
  | _         => none

/-- HTML container tags a `.map` may be lifted into a `forEach` over. -/
private def htmlTags : List String :=
  ["div", "span", "p", "h1", "h2", "h3", "h4", "h5", "h6", "ul", "ol", "li", "a", "nav",
   "header", "footer", "section", "article", "button", "label", "table", "thead", "tbody",
   "tfoot", "tr", "td", "th", "strong", "em", "select", "option"]

/-- An element former's tag (`ul` ↦ `"ul"`, `formEl` ↦ `"form"`), if it is a known tag. -/
private def elementTag? (n : Lean.Name) : Option String :=
  match lastStr? n.eraseMacroScopes with
  | some "formEl" => some "form"
  | some s        => if htmlTags.contains s then some s else none
  | none          => none

open Lean in
/-- View `stx` as a function application: the function syntax and its argument array. -/
private def asApp? (stx : Syntax) : Option (Syntax × Array Syntax) :=
  if stx.getKind == kApp && stx.getArgs.size == 2 then
    some (stx.getArgs[0]!, stx.getArgs[1]!.getArgs)
  else none

open Lean in
/-- Strip one layer of parentheses. -/
private def unparen (stx : Syntax) : Syntax :=
  if stx.getKind == kParen && stx.getArgs.size == 3 then stx.getArgs[1]! else stx

open Lean in
/-- View `stx` as `xs.map f`: returns `(xs, f)`, with `xs` rebuilt as an identifier that
    keeps the source position so a bound scope variable still resolves. -/
private def asMap? (stx : Syntax) : Option (Syntax × Syntax) :=
  match asApp? (unparen stx) with
  | some (fn, args) =>
      if args.size == 1 then
        match fn with
        | .ident _ _ n _ =>
            if lastStr? n.eraseMacroScopes == some "map" then
              some (mkIdentFrom fn (dropLastComp n.eraseMacroScopes), unparen args[0]!)
            else none
        | _ => none
      else none
  | none => none

open Lean in
/-- View `stx` as a single-binder lambda `fun x => body`: returns `(x, body)`. -/
private def asFun? (stx : Syntax) : Option (Syntax × Syntax) :=
  let s := unparen stx
  if s.getKind == kFun && s.getArgs.size ≥ 2 then
    let basic := s.getArgs[1]!
    if basic.getKind == kBasicFun && basic.getArgs.size ≥ 4 then
      let binders := basic.getArgs[0]!.getArgs
      if binders.size == 1 then some (binders[0]!, basic.getArgs[3]!) else none
    else none
  else none

open Lean in
/-- Is `e` a `key v` attribute? If so, return `v`. -/
private def keyArg? (e : Syntax) : Option Syntax :=
  match asApp? e with
  | some (fn, args) =>
      match fn with
      | .ident _ _ n _ =>
          if lastStr? n.eraseMacroScopes == some "key" && args.size == 1 then some args[0]! else none
      | _ => none
  | none => none

open Lean in
/-- Pull the `key` value out of a row's attribute list and return the list without it (the
    key becomes `forEach`'s projection, so it must not also sit in the row, where its free
    row variable would not resolve). `none` if there is no `key`. -/
private def extractKey (attrsList : Syntax) : MacroM (Option (Term × Term)) := do
  if attrsList.getKind != kList || attrsList.getArgs.size != 3 then return none
  let mut keyV : Option Syntax := none
  let mut kept : Array Term := #[]
  for e in attrsList.getArgs[1]!.getSepArgs do
    match keyArg? e with
    | some v => keyV := some v
    | none   => kept := kept.push ⟨e⟩
  match keyV with
  | some v => return some (⟨v⟩, ← `([$kept,*]))
  | none   => return none

open Lean in
mutual
  /-- Rewrite a view body against the current scope `m`: lift dynamic text, model-driven
      `if`s, dynamic attributes/events, `match`es, and `.map` lists; recurse elsewhere. -/
  partial def viewLift (m : Ident) (stx : Syntax) : MacroM Syntax := do
    match stx with
    | `(text $e:term) =>
        if viewMentions m.getId e then return (← `(Qed.V.dyn (fun $m => $e))) else return stx
    | `(if $c:term then $t:term else $e:term) =>
        let t' : Term := ⟨← viewLift m t⟩
        let e' : Term := ⟨← viewLift m e⟩
        if viewMentions m.getId c && (looksLikeView t' || looksLikeView e') then
          -- `if c then true else false` re-uses the original `Decidable`/`Bool` condition,
          -- so the lift works whether `c` is a `Bool` (`==`) or a decidable `Prop` (`<`).
          return (← `(Qed.V.ifElse (fun $m => if $c then true else false) $t' $e'))
        else
          return (← `(if $c then $t' else $e'))
    | _ =>
        -- a `match` on the model → the verified diff fallback (`dynNode`). Lift the arms
        -- first (so a `.map`/`if` inside an arm still becomes `forEach`/`ifElse`); the
        -- scrutinee's `m` is then closed by the `dynNode` lambda.
        if stx.getKind == kMatch && viewMentions m.getId stx then
          let lifted := stx.setArgs (← stx.getArgs.mapM (viewLift m))
          let st : Term := ⟨lifted⟩
          return (← `(Qed.V.dynNode (fun $m => Qed.View.render $st $m)))
        -- an element whose children are `xs.map (fun x => row)` → `forEach`
        if let some out ← tryForEach m stx then return out
        -- a scope-dependent attribute or event helper → `dynAttr` / `onClick'` / …
        if let some out ← tryAttr m stx then return out
        -- otherwise recurse structurally
        if stx.getArgs.isEmpty then return stx
        else return stx.setArgs (← stx.getArgs.mapM (viewLift m))

  /-- `cls (… m …)` → `dynAttr "class" (fun m => …)`, `attr k (… m …)` → `dynAttr k …`,
      `onClick (… m …)` → `onClick' (fun m => …)`, etc. (`none` if not such a helper). -/
  partial def tryAttr (m : Ident) (stx : Syntax) : MacroM (Option Syntax) := do
    let some (fn, args) := asApp? stx | return none
    match fn with
    | .ident _ _ n _ =>
        let hn := (lastStr? n.eraseMacroScopes).getD ""
        if let some an := stringAttrName? hn then
          if args.size == 1 && viewMentions m.getId args[0]! then
            let nm : Term := ⟨Syntax.mkStrLit an⟩
            let v  : Term := ⟨args[0]!⟩
            return some (← `(Qed.V.dynAttr $nm (fun $m => $v)))
        if hn == "attr" && args.size == 2 && viewMentions m.getId args[1]! then
          let k : Term := ⟨args[0]!⟩
          let v : Term := ⟨args[1]!⟩
          return some (← `(Qed.V.dynAttr $k (fun $m => $v)))
        if let some pn := eventPrime? hn then
          if args.size == 1 && viewMentions m.getId args[0]! then
            let primed := mkIdent ((`Qed.V).append (Name.mkSimple pn))
            let v : Term := ⟨args[0]!⟩
            return some (← `($primed (fun $m => $v)))
        return none
    | _ => return none

  /-- An element `el [attrs] (xs.map fun x => row)` with a keyed row → `forEach`. -/
  partial def tryForEach (m : Ident) (stx : Syntax) : MacroM (Option Syntax) := do
    let some (fnP, pargs) := asApp? stx | return none
    match fnP with
    | .ident _ _ pn _ =>
        let some tag := elementTag? pn | return none
        if pargs.size != 2 then return none
        let some (xs, funArg) := asMap? pargs[1]! | return none
        let some (binder, body) := asFun? funArg | return none
        let binderId : Ident := ⟨binder⟩
        let attrsL : Term := ⟨← viewLift m pargs[0]!⟩
        let xsT    : Term := ⟨xs⟩
        let tagL   : Term := ⟨Syntax.mkStrLit tag⟩
        -- A keyed row (an element carrying `key …`) becomes a fine-grained `forEach`. Anything
        -- else — a keyless `.map`, or a row that isn't a keyed element — degrades to a `dynNode`
        -- that renders the list as `Html` and reconciles it through the verified positional
        -- `diff`. So `.map` never fails to compile; it just isn't fine-grained without a key.
        let keyOpt ← (match asApp? body with
                      | some (_, bargs) => if bargs.size ≥ 1 then extractKey bargs[0]! else pure none
                      | none            => pure none)
        match keyOpt with
        | some (keyV, newAttrs) =>
            let body' := body.setArg 1 (body.getArgs[1]!.setArg 0 newAttrs)
            let rowL : Term := ⟨← viewLift binderId body'⟩
            -- a per-list signal namespace from this `.map`'s source position, so two lists over
            -- the same row keys don't share signal names (which are a process-wide map).
            let pos   := (stx.getPos?.map (·.byteIdx)).getD 0
            let prefT : Term := ⟨Syntax.mkStrLit (toString pos ++ "@")⟩
            return some (← `(Qed.V.forEach $tagL (fun $m => $xsT) (fun $binderId => $keyV) $rowL (attrs := $attrsL) (sigPrefix := $prefT)))
        | none =>
            let rowL : Term := ⟨← viewLift binderId body⟩
            return some (← `(Qed.V.dynNode (fun $m =>
              Qed.Html.element $tagL (($attrsL).map (Qed.VAttr.eval $m))
                (($xsT).map (fun $binderId => Qed.View.render $rowL $binderId)).toList)))
    | _ => return none
end

open Lean in
macro "view% " "fun " m:ident " => " body:term : term => do
  return ⟨← viewLift m body⟩

end Qed
