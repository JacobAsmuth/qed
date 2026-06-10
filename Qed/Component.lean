/-
  Qed.Component, reusable, nestable view components.

  A `Component Model Msg` bundles a `Model → Msg → Model` transition with a
  `Model → Html Msg` view: the reusable behaviour of a self-contained piece of UI,
  with its own state and message type. Because the message type is the component's
  own, a parent embeds a child by *relabelling* the child's messages into its own
  (`Html.map`), so a click inside a child is delivered as a parent message, the
  types make a misrouted event impossible.

  The list helpers (`viewList`/`updateAt`) cover the common case of the same
  component repeated per data row (e.g. one box per entry in a decoded JSON array):
  each row's messages are tagged with the row index, so a parent message carries
  *which* row produced it.

  Everything here is pure sugar over `Html.map`; it adds no axioms and links on
  every target. A child that needs effects (`Cmd`) is not modelled yet, promote it
  with `toApp` and run it as its own application, or thread effects in the parent.
-/
import Qed.Html
import Qed.Runtime
import Lean

namespace Qed

/-- A reusable piece of UI: a transition over its own state and a view producing
    its own messages. `init` is deliberately absent, a component is instantiated
    from data by its embedder (one model per row), so the starting state is the
    caller's to choose. -/
structure Component (Model : Type) (Msg : Type) where
  /-- The pure, total transition over the component's local state. -/
  update : Model → Msg → Model
  /-- The pure, total view, producing the component's own messages. -/
  view   : Model → Html Msg

namespace Component
variable {Model Msg PMsg : Type}

/-- Run a component as a standalone application (no effects). Useful for testing a
    component in isolation, or when it *is* the whole app. The component's `Html` view is a
    value (not inline), so it goes in as a `View.ofHtml` template. -/
def toApp (c : Component Model Msg) (init : Model) : App Model Msg :=
  mkApp init c.update (View.ofHtml c.view)

/-- Embed a single child: render it and relabel its messages into the parent's
    `Msg` via `wrap`. The parent's transition for `wrap cm` runs `c.update` on the
    child's slice of the model. -/
def render (c : Component Model Msg) (wrap : Msg → PMsg) (m : Model) : Html PMsg :=
  (c.view m).map wrap

/-- Render the same component once per row, tagging each row's messages with its
    index: `tag i cm` is the parent message for child message `cm` from row `i`.
    The result is a child list ready to drop into `<ul>{…}</ul>`. -/
def viewList (c : Component Model Msg) (models : Array Model)
    (tag : Nat → Msg → PMsg) : List (Html PMsg) :=
  (models.mapIdx fun i m => (c.view m).map (tag i)).toList

/-- Route a child message to row `i` and run that row's transition, leaving the
    other rows untouched. The dual of `viewList` for the parent's `update`.

    *Positional*: `i` is an array index, so an in-flight message can land on the
    wrong row if the list reorders between render and dispatch. Prefer `updateKeyed`
    (routes by a stable key) for lists that sort/reorder. -/
def updateAt (c : Component Model Msg) (models : Array Model) (i : Nat) (msg : Msg) :
    Array Model :=
  models.modify i (c.update · msg)

/-- Route a child message to the row whose `key` matches `k` and run that row's
    transition, leaving the others untouched. Unlike `updateAt`, routing is by a
    stable key (the same identity the keyed `diff` reconciles by), so a message
    survives the list being sorted or filtered between render and dispatch, the
    React way of addressing a child by identity, not position. -/
def updateKeyed (c : Component Model Msg) (key : Model → String)
    (models : Array Model) (k : String) (msg : Msg) : Array Model :=
  models.map fun r => if key r == k then c.update r msg else r

end Component

/-! ### The `embed` command

`embed Child as ctor keyedBy keyFn into field` removes the per-child wiring tax of
embedding a reusable `Component` in a keyed list. Given a child *namespace* `Child`
(providing `Child.component`, `Child.Model`, `Child.Msg`) it generates, in the
current namespace:

* `ctorView   : Child.Model → Html Msg`, the child's view with its messages tagged
  by the parent constructor `Msg.ctor key`, so a child event routes back as a parent
  message carrying the row's stable key;
* `ctorUpdate : Model → String → Child.Msg → Model`, runs the child's transition on
  the row in `field` whose key matches, via `updateKeyed` (routing by key, not index,
  so a sort/filter between render and dispatch can't misroute it).

The one line the macro cannot write (Lean cannot extend an existing `inductive`) is
the parent message constructor: add `| ctor (k : String) (msg : Child.Msg)` to your
`Msg`. The `update` arm is then `| .ctor k msg => ctorUpdate m k msg`, and the view
drops to `ctorView r`. Core-syntax only (no `import Lean`), like `router`. -/
syntax (name := embedCmd)
  "embed " ident " as " ident " keyedBy " term " into " ident : command

open Lean in
macro_rules
  | `(embed $child:ident as $ctor:ident keyedBy $keyFn:term into $field:ident) => do
      let comp     := mkIdent (child.getId ++ `component)
      let childMod := mkIdent (child.getId ++ `Model)
      let childMsg := mkIdent (child.getId ++ `Msg)
      let pModel   := mkIdent `Model
      let pMsg     := mkIdent `Msg
      let pMsgCtor := mkIdent (`Msg ++ ctor.getId)
      let viewName := mkIdent (Name.mkSimple (ctor.getId.toString ++ "View"))
      let updName  := mkIdent (Name.mkSimple (ctor.getId.toString ++ "Update"))
      `(def $viewName (r : $childMod) : Html $pMsg :=
          (($comp).view r).map ($pMsgCtor ($keyFn r))
        def $updName (m : $pModel) (k : String) (msg : $childMsg) : $pModel :=
          { m with $field:ident := ($comp).updateKeyed $keyFn m.$field k msg })

/-! ### Lifting an invariant over a list of children

These are the proven building blocks behind `invariant … forEach …` (see `Qed.Invariant`). Each says
a standard list operation keeps a per-element predicate `P`, so a parent invariant "every child stays
valid" reduces, arm by arm, to applying the matching lemma, rather than re-deriving the membership
reasoning every time. The keyed one (`updateKeyed_forall`) is the case `embed` introduces: routing a
child message touches one row via the child's transition, so it preserves `P` whenever the child does. -/
namespace ForEach

/-- `push` keeps `P` for every element, given it holds of the appended one (the `add` arm). -/
theorem forall_push {α} {P : α → Prop} {a : Array α} {x : α}
    (h : ∀ y ∈ a, P y) (hx : P x) : ∀ y ∈ a.push x, P y := by
  intro y hy; rw [Array.mem_push] at hy; rcases hy with hy | rfl
  · exact h y hy
  · exact hx

/-- `filter` keeps `P` for every element, it only drops elements (the `remove` arm). -/
theorem forall_filter {α} {P : α → Prop} {a : Array α} {f : α → Bool}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ a.filter f, P y := by
  intro y hy; rw [Array.mem_filter] at hy; exact h y hy.1

/-- `map g` keeps `P` for every element when `g` does, elementwise. -/
theorem forall_map {α} {P : α → Prop} {a : Array α} {g : α → α}
    (hg : ∀ y ∈ a, P (g y)) : ∀ y ∈ a.map g, P y := by
  intro y hy; rw [Array.mem_map] at hy; obtain ⟨x, hx, rfl⟩ := hy; exact hg x hx

/-- The arm `embed` introduces: delivering a child message through `updateKeyed` keeps `P` for every
    row, given the child's transition preserves `P`. Generic over the component, so a parent's keyed
    arm discharges by `exact updateKeyed_forall _ _ childInvariant h`, no per-app proof. -/
theorem updateKeyed_forall {α Msg} {P : α → Prop} (c : Component α Msg) (key : α → String)
    (hc : ∀ r m, P r → P (c.update r m))
    {a : Array α} {k : String} {msg : Msg}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ Component.updateKeyed c key a k msg, P y := by
  intro y hy; simp only [Component.updateKeyed, Array.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy; split
  · exact hc x msg (h x hx)
  · exact h x hx

/-- A verified, membership-preserving sort, for the `sort`/`rank` arm. Unlike `Array.qsort` -
    which has no membership lemma in the standard library, so `for_each` can't lift over it, this
    is `mergeSort`, which does. `le a b` means "`a` sorts before-or-equal `b`". Use it for a feed's
    re-rank and the lift discharges with no hand proof. -/
@[reducible] def _root_.Array.sortBy {α} (a : Array α) (le : α → α → Bool) : Array α := a.mergeSort le

/-- A verified sort keeps `P` for every element, it only reorders (a permutation). -/
theorem forall_sortBy {α} {P : α → Prop} {a : Array α} {le : α → α → Bool}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ a.sortBy le, P y := by
  intro y hy; simp only [Array.sortBy, Array.mem_mergeSort] at hy; exact h y hy

end ForEach

/-! ### The `component` command: state declared next to the view that uses it

`component Name where state f : T := init … view => <jsx>` is the declaration form of a
*local* component (the keyed `useState` cells of `Qed.LocalDef`): state lives next to the
view that uses it instead of threading through the root model. Inside the view, the state
fields are in scope by name, and `set` is the only way to change one:

* `set f e`, a message-valued handler (`onClick={set f e}`). `e` may mention the state
  fields; it is evaluated against the *current* state when the message is delivered, not
  when the view rendered.
* `set f`, a value handler (`onInput={set f}`): stores the incoming payload in `f`.
* `send o`, with `emits T` declared: bubble `o : T` to the parent's `mountWith` handler.
  `set f e, send o` does both in one message; a component with no `set`/`send` use for a
  field's value can still display it.

Crucially, a handler is **not** a closure. Each distinct `set` site becomes one constructor
of a generated first-order `Msg` (`set_f`, `set_f_2`, …), and a generated `update`
interprets it, so messages stay data with named cases: `invariant … preserved_by
Name.update` reduces arm by arm and names the case that broke, local state still
snapshots/restores through its JSON codec, and replay/the differential gate keep seeing
serializable messages and a pure transition.

Generated under `Name.`: `State` (+ JSON codec), `init`, `Msg`, `update`, `view`, `reg`
(the `LocalDef` to register: `ui … (locals := [Name.reg])`), and `mount` (the host
attribute: `<div {Name.mount "a"}/>`, one instance per key). With `emits T`, also
`mountWith key onOut`, where `onOut : T → msg` maps the child's output to a parent
message; inside another component's view, a payload-form `set f` is exactly such a map,
so nesting reads `<div {Child.mountWith key (set f)}/>`. Seed an instance from parent
data with `.localInit` on the mount attribute. `LocalDef`/`localMount` (Qed.Runtime) are
the substrate this elaborates onto, as `el` is to JSX, not a second authored form.

Sharp edge (the keywords are identifiers, the price of keeping `component`/`view` usable
as names): a command that *ends in an open precedence-0 term*, like `#check f`, will
swallow a following `component N where` as application arguments and fail at `where`.
A doc comment on the declaration (or any keyword-led command between) ends the term.
Components following components are fine: the `view` body is a closed max-precedence
atom. -/

open Lean Parser in
/-- The component state setter, `set f e` / `set f`, optionally bubbling an output in the
    same message: `set f e, send o`. It parses as a term so it can sit in a JSX handler
    splice, but it only *means* something inside a `component … view =>` body, where the
    elaborator replaces it with a generated `Msg` constructor. `set` stays a usable
    identifier everywhere else (non-reserved). -/
@[term_parser] def setTerm := leading_parser:maxPrec
  nonReservedSymbol "set" (includeIdent := true) >> Parser.ident >>
  optional (termParser maxPrec) >>
  optional (", " >> nonReservedSymbol "send" (includeIdent := true) >> termParser maxPrec)

open Lean Parser in
/-- The component output, `send o`: bubble `o` (the component's `emits` type) to whatever
    the parent passed to `mountWith`, leaving the state unchanged. Like `set`, it is only
    meaningful inside a `component … view =>` body. -/
@[term_parser] def sendTerm := leading_parser:maxPrec
  nonReservedSymbol "send" (includeIdent := true) >> termParser maxPrec

open Lean in
@[macro setTerm] def expandSetTermOutsideComponent : Macro := fun stx =>
  Macro.throwErrorAt stx
    "`set …` is the component state setter; it only has meaning inside a `component … view =>` body"

open Lean in
@[macro sendTerm] def expandSendTermOutsideComponent : Macro := fun stx =>
  Macro.throwErrorAt stx
    "`send …` is the component output; it only has meaning inside a `component … view =>` body"

open Lean Parser in
/-- `component Name where state f : T := init … view => <jsx>`. The keywords are matched as
    plain identifiers (`identEq`), not reserved tokens: the command category dispatches
    ident-led parsers by the ident *kind*, and `component`/`state`/`view` stay usable as
    names everywhere else (`embed` requires `Child.component`, every app has a `view`). -/
@[command_parser] def componentCmd : Parser := leading_parser
  optional Command.docComment >> atomic (identEq `component) >> ident >> " where " >>
  many (node `Qed.componentStateItem
    -- the default is max-precedence so it cannot swallow the next `state`/`emits`/`view`
    -- keyword as an application argument; parenthesize a compound default, as in a JSX splice
    (atomic (identEq `state) >> ident >> " : " >> termParser >> " := " >> termParser maxPrec)) >>
  optional (node `Qed.componentEmits (atomic (identEq `emits) >> termParser maxPrec)) >>
  -- the body is max-precedence (a JSX element is one closed atom) so that application
  -- cannot extend past it and swallow a following ident-led `component` declaration
  identEq `view >> " => " >> termParser maxPrec

/-- One `set`/`send` site collected from a `component` view: the field it sets (`none` for
    a pure `send`), the constructor it became, the set expression (`none` with a field is
    the payload form `set f`), and the sent output, if any. `key` identifies the site
    syntactically, so identical sites share one constructor. -/
private structure SetSite where
  key    : String
  field  : Option Lean.Name
  ctor   : Lean.Name
  expr?  : Option Lean.Term
  send?  : Option Lean.Term

/-- Does `n` occur as an identifier anywhere under `stx`? How the `component` elaborator
    decides which state fields a set expression (or the view body) mentions, so only those
    are bound from the model. -/
private partial def mentionsIdent (stx : Lean.Syntax) (n : Lean.Name) : Bool :=
  match stx with
  | .ident _ _ v _ => v.eraseMacroScopes == n
  | .node _ _ args => args.any (mentionsIdent · n)
  | _ => false

open Lean Elab Command in
/-- Intern a `set`/`send` site: identical sites share one constructor; fresh ones get a
    name derived from the field (`set_f`, `set_f_2`, …) or `send`/`send_2` for an output. -/
private def registerSite (sites : IO.Ref (Array SetSite)) (field : Option Name)
    (expr? send? : Option Term) : CommandElabM Name := do
  let pp : Option Term → String := fun
    | some e => e.raw.reprint.getD (toString e.raw)
    | none   => "·"
  let key := s!"{field}|{pp expr?}|{pp send?}"
  let cur ← sites.get
  match cur.find? (·.key == key) with
  | some site => return site.ctor
  | none =>
      let base := match field with
        | some f => s!"set_{f}"
        | none   => "send"
      let mut name := Name.mkSimple base
      let mut i := 2
      while cur.any (·.ctor == name) do
        name := Name.mkSimple s!"{base}_{i}"
        i := i + 1
      sites.set (cur.push { key, field, ctor := name, expr?, send? })
      return name

open Lean Elab Command in
/-- Replace every `set`/`send` site under `stx` with its `Msg` constructor (a plain ident,
    so the handler elaborates to first-order data, not a closure), collecting the sites. -/
private partial def replaceSets (fields : Array Name) (msgPath : Name) (hasEmits : Bool)
    (sites : IO.Ref (Array SetSite)) (stx : Syntax) : CommandElabM Syntax := do
  let noEmits (ref : Syntax) : CommandElabM Unit :=
    throwErrorAt ref "`send` bubbles an output, but this component declares no output type; \
      add `emits T` between the `state` fields and the `view`"
  if stx.getKind == ``setTerm then
    let fId := stx[1]
    let fname := fId.getId.eraseMacroScopes
    unless fields.contains fname do
      throwErrorAt fId "`set {fname}`: not a `state` field of this component (fields: {fields.toList})"
    let expr? : Option Term := if stx[2].getNumArgs == 1 then some ⟨stx[2][0]⟩ else none
    let send? : Option Term := if stx[3].getNumArgs == 3 then some ⟨stx[3][2]⟩ else none
    if send?.isSome && !hasEmits then noEmits stx[3]
    let ctor ← registerSite sites (some fname) expr? send?
    return mkIdent (msgPath ++ ctor)
  else if stx.getKind == ``sendTerm then
    unless hasEmits do noEmits stx
    let ctor ← registerSite sites none none (some ⟨stx[1]⟩)
    return mkIdent (msgPath ++ ctor)
  else
    match stx with
    | .node info kind args =>
        return .node info kind (← args.mapM (replaceSets fields msgPath hasEmits sites))
    | _ => return stx

open Lean Elab Command in
@[command_elab componentCmd] def elabComponentCmd : CommandElab := fun stx => do
      -- node shape: [doc?, kw, name, "where", (stateItem: [kw, f, ":", ty, ":=", default])*,
      --              (emits: [kw, ty])?, kw, "=>", body]
      let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
        if stx[0].getNumArgs == 1 then some ⟨stx[0][0]⟩ else none
      let t : Ident := ⟨stx[2]⟩
      let items := stx[4].getArgs
      let fs  : Array Ident := items.map fun it => ⟨it[1]⟩
      let tys : Array Term  := items.map fun it => ⟨it[3]⟩
      let ds  : Array Term  := items.map fun it => ⟨it[5]⟩
      let outTy? : Option Term := if stx[5].getNumArgs == 1 then some ⟨stx[5][0][1]⟩ else none
      let body : Term := ⟨stx[8]⟩
      let stateId    := mkIdent (t.getId ++ `State)
      let initId     := mkIdent (t.getId ++ `init)
      let msgId      := mkIdent (t.getId ++ `Msg)
      let updateId   := mkIdent (t.getId ++ `update)
      let viewId     := mkIdent (t.getId ++ `view)
      let regId      := mkIdent (t.getId ++ `reg)
      let mountId    := mkIdent (t.getId ++ `mount)
      let toJsonId   := mkIdent (t.getId ++ `State ++ `toJson)
      let fromJsonId := mkIdent (t.getId ++ `State ++ `fromJson)
      let fieldNames := fs.map (·.getId)
      -- the registry id: the component's full name, unique app-wide by construction
      let idLit := Syntax.mkStrLit (((← getCurrNamespace) ++ t.getId).toString)
      -- Collect the `set`/`send` sites; each becomes a `Msg` constructor reference in the body.
      let sitesRef ← IO.mkRef (#[] : Array SetSite)
      let body' : Term := ⟨← replaceSets fieldNames (t.getId ++ `Msg) outTy?.isSome sitesRef body⟩
      let sites ← sitesRef.get
      -- Msg: one first-order constructor per distinct site (the payload form `set f` takes
      -- the field's value type as its argument).
      let isPayload : SetSite → Bool := fun site => site.field.isSome && site.expr?.isNone
      let ctors ← sites.mapM fun site => do
        let cId := mkIdent site.ctor
        if isPayload site then
          let some f := site.field | throwError "component: internal"
          let some idx := fieldNames.findIdx? (· == f) | throwError "component: internal"
          `(Lean.Parser.Command.ctor| | $cId:ident (v : $(tys[idx]!)))
        else
          `(Lean.Parser.Command.ctor| | $cId:ident)
      let msgCmd ← if ctors.isEmpty then `(command| inductive $msgId)
        else `(command| inductive $msgId where $[$ctors:ctor]*)
      -- update: interpret each constructor. Set/send expressions are evaluated HERE, over
      -- the current (pre-update) state: each state field they mention is bound from `s`
      -- first. With `emits` the arms return `(state', some output / none)`.
      let arms ← sites.mapM fun site => do
        let cFull := mkIdent (t.getId ++ `Msg ++ site.ctor)
        let stateTerm : Term ← match site.field, site.expr? with
          | some f, some e => `({ s with $(mkIdent f):ident := $e })
          | some f, none   => `({ s with $(mkIdent f):ident := v })
          | none,   _      => `(s)
        let rhs0 : Term ← match outTy? with
          | none => pure stateTerm
          | some _ => match site.send? with
            | some o => `(($stateTerm, some $o))
            | none   => `(($stateTerm, none))
        let mut rhs := rhs0
        for g in fieldNames.reverse do
          let mentioned := (site.expr?.any (mentionsIdent ·.raw g)) ||
                           (site.send?.any (mentionsIdent ·.raw g))
          if mentioned then
            let gId := mkIdent g
            rhs ← `(let $gId:ident := (s.$gId:ident); $rhs)
        if isPayload site then
          `(Lean.Parser.Term.matchAltExpr| | $cFull:ident v => $rhs)
        else
          `(Lean.Parser.Term.matchAltExpr| | $cFull:ident => $rhs)
      let retTy : Term ← match outTy? with
        | some o => `($stateId × Option $o)
        | none   => `($stateId)
      let updateCmd ← if sites.isEmpty then
          `(command| def $updateId (s : $stateId) : $msgId → $retTy := fun m => nomatch m)
        else
          `(command| def $updateId (s : $stateId) : $msgId → $retTy := fun m =>
              match m with $[$arms:matchAlt]*)
      -- view: the body with set sites replaced; state fields it mentions are in scope by name.
      let mut viewBody := body'
      for g in fieldNames.reverse do
        if mentionsIdent viewBody.raw g then
          let gId := mkIdent g
          viewBody ← `(let $gId:ident := (s.$gId:ident); $viewBody)
      -- JSON codec for the state (snapshot/restore and the keyed store are strings).
      let keyLits := fs.map fun f => Syntax.mkStrLit (toString f.getId)
      let pairs ← (fs.zip keyLits).mapM fun (f, k) => `(($k, toJson (x.$f:ident)))
      let decodes ← (tys.zip keyLits).mapM fun (ty, k) =>
        `((FromJsonField.fromField j $k : Except String $ty))
      let cmds : Array (TSyntax `command) := #[
        ← `(command| structure $stateId where
              $[$fs:ident : $tys]*),
        ← `(command| def $initId : $stateId := { $[$fs:ident := $ds],* }),
        ← `(command| def $toJsonId (x : $stateId) : Json := Json.obj [$[$pairs],*]),
        ← `(command| def $fromJsonId (j : Json) : Except String $stateId := do
              $[let $fs:ident ← $decodes:term]*
              return { $[$fs:ident],* }),
        ← `(command| instance : ToJson $stateId := ⟨$toJsonId⟩),
        ← `(command| instance : FromJson $stateId := ⟨$fromJsonId⟩),
        msgCmd,
        updateCmd,
        ← `(command| def $viewId (s : $stateId) : Html $msgId := $viewBody),
        ← (match outTy? with
          | none => `(command| $[$doc?:docComment]? def $regId : LocalDef :=
              LocalDef.ofSimple $idLit $initId $viewId $updateId)
          | some _ => `(command| $[$doc?:docComment]? def $regId : LocalDef :=
              LocalDef.of $idLit $initId $viewId $updateId)),
        ← `(command| $[$doc?:docComment]? def $mountId {msg : Type} (key : String) : Attr msg :=
              localMount $idLit key) ]
      -- with `emits T`, also generate the receiving mount: the parent maps the output to
      -- one of its own messages (often a payload-form `set f` of its own)
      let cmds ← match outTy? with
        | some o => do
            let mountWithId := mkIdent (t.getId ++ `mountWith)
            pure <| cmds.push <|
              ← `(command| $[$doc?:docComment]? def $mountWithId {msg : Type}
                    (key : String) (onOut : $o → msg) : Attr msg :=
                    localMountWith $idLit key (fun out => some (onOut out)))
        | none => pure cmds
      for c in cmds do elabCommand c

end Qed
