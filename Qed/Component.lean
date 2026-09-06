/-
  Qed.Component, reusable, nestable view components.

  The authored form is the `component` command at the bottom of this file: ONE way to
  declare a component, used from a view as a JSX tag (`<Widget …/>`, see `Qed.Jsx`),
  with who owns its state decided at the use site (framework-owned keyed instances, or
  parent-owned rows bound with `state={…}`). Everything above it is the substrate that
  declaration elaborates onto.

  A `Component Model Msg` bundles a `Model → Msg → Model` transition with a
  `Model → Html Msg` view: the reusable behaviour of a self-contained piece of UI,
  with its own state and message type. Because the message type is the component's
  own, a parent embeds a child by *relabelling* the child's messages into its own
  (`Html.map`), so a click inside a child is delivered as a parent message, the
  types make a misrouted event impossible.

  Everything here is pure sugar over `Html.map`; it adds no axioms and links on
  every target. A child that needs effects (`Cmd`) is not modelled yet, run it as its
  own application (the generated `Name.app`), or thread effects in the parent.
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

/-- Embed a single child: render it and relabel its messages into the parent's
    `Msg` via `wrap`. The parent's transition for `wrap cm` runs `c.update` on the
    child's slice of the model. -/
def render (c : Component Model Msg) (wrap : Msg → PMsg) (m : Model) : Html PMsg :=
  (c.view m).map wrap

/-- Route a child message to the row whose `key` matches `k` and run that row's
    transition, leaving the others untouched. Routing is by a stable key (the same
    identity the keyed `diff` reconciles by), so a message survives the list being
    sorted or filtered between render and dispatch, the React way of addressing a
    child by identity, not position. What a declared component's generated
    `Name.updateKeyed` wraps (with the declaration's `key` baked in). -/
def updateKeyed (c : Component Model Msg) (key : Model → String)
    (models : Array Model) (k : String) (msg : Msg) : Array Model :=
  models.map fun r => if key r == k then c.update r msg else r

/-- Render a keyed collection, sharing identity with updateKeyed. A custom wrapper
    receives the row and its already-routed child; its root gets the same key. -/
def each (c : Component Model Msg) (keyOf : Model → String) (rows : Array Model)
    (route : String → Msg → PMsg)
    (wrap : Model → Html PMsg → Html PMsg := fun _ child => child) : Array (Html PMsg) :=
  rows.map fun row =>
    let k := keyOf row
    let child := wrap row (render c (route k) row)
    match child with
    | .element tag attrs children =>
        .element tag (.key k :: attrs.filter (fun | .key _ => false | _ => true)) children
    | other => .element "div" [.key k] [other]

end Component

/-! ### Lifting an invariant over a list of children

These are the proven building blocks behind `invariant … forEach …` (see `Qed.Invariant`). Each says
a standard list operation keeps a per-element predicate `P`, so a parent invariant "every child stays
valid" reduces, arm by arm, to applying the matching lemma, rather than re-deriving the membership
reasoning every time. The keyed one (`updateKeyed_forall`) is the case a parent-owned component tag
introduces: routing a child message touches one row via the child's transition, so it preserves `P`
whenever the child does. -/
namespace ForEach

/-- `push` keeps `P` for every element, given it holds of the appended one (the `add` arm). -/
theorem forall_push {α} {P : α → Prop} {a : Array α} {x : α}
    (h : ∀ y ∈ a, P y) (hx : P x) : ∀ y ∈ a.push x, P y := by
  simpa only [Array.mem_push, or_imp, forall_and, forall_eq] using And.intro h hx

/-- `filter` keeps `P` for every element, it only drops elements (the `remove` arm). -/
theorem forall_filter {α} {P : α → Prop} {a : Array α} {f : α → Bool}
    (h : ∀ y ∈ a, P y) : ∀ y ∈ a.filter f, P y := by
  simpa only [Array.mem_filter, and_imp] using fun y hy _ => h y hy

/-- `map g` keeps `P` for every element when `g` does, elementwise. -/
theorem forall_map {α} {P : α → Prop} {a : Array α} {g : α → α}
    (hg : ∀ y ∈ a, P (g y)) : ∀ y ∈ a.map g, P y := by
  intro y hy; rw [Array.mem_map] at hy; obtain ⟨x, hx, rfl⟩ := hy; exact hg x hx

/-- The arm a parent-owned component tag introduces: delivering a child message through
    `updateKeyed` keeps `P` for every row, given the child's transition preserves `P`. Generic over
    the component, so a parent's keyed arm discharges by
    `exact updateKeyed_forall _ _ childInvariant h`, no per-app proof. -/
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

/-! ### Component declarations

`component Name where` groups `state`, `prop`, and `collection` fields, an optional
`key` and `emits` clause, named `action`s, and a JSX `view`.

* `set f e` updates a state field; `set f` accepts an event payload. Chains assign
  several fields atomically. Every expression, including `send`, reads the same
  pre-update state at delivery time.
* `action save => set saved count` generates the stable constructor `Msg.save`.
  Actions may take typed parameters and an optional `when (condition)` guard.
  A false guard leaves state unchanged and emits nothing. Inline setters still work.
* `prop label : String` is immutable input, separate from `State`. Props refresh
  on parent renders; `initial={{ note := label }}` seeds local state only once.
  Defaults may be supplied on either kind of field. `set` cannot target a prop.
* `collection rows : Row` is an `Array Row.State`, defaulting to empty. It generates
  `Msg.rows key childMsg` and its keyed update arm. Row must declare `key` and have
  a state-only update. `Row.each rows .rows` keys the rendered roots; an optional
  wrapper receives the row and its routed child.

Local mounts require defaults for all state fields. Parent-owned tags use
`state={row}` and `onMsg={.row}`; their fields can omit defaults. Props are passed
as ordinary tag attributes in either mode. Components with props expose
`update props state msg`; state-only components retain `update state msg`.

Generated declarations are ordinary Lean definitions. Invariants can target
`Name.update`, with props supplied when present. Registration follows helper
functions as well as tags, including imports. See `docs/components.md`.

Keywords remain usable as identifiers. A preceding open-ended command such as
`#check f` can consume a following `component`; a doc comment ends that term. -/

open Lean Parser in
/-- The component state setter, `set f e` / `set f`, chainable over several fields and
    optionally bubbling an output, all in one message: `set f e, set g e', send o`. Every
    expression in the chain is evaluated against the same pre-update state (React's
    batched `setState` semantics). It parses as a term so it can sit in a JSX handler
    splice, but it only *means* something inside a `component … view =>` body, where the
    elaborator replaces it with a generated `Msg` constructor. `set` stays a usable
    identifier everywhere else (non-reserved). -/
@[term_parser] def setTerm := leading_parser:maxPrec
  nonReservedSymbol "set" (includeIdent := true) >> Parser.ident >>
  optional (checkColGt >> termParser maxPrec) >>
  many (node `Qed.setMore
    (atomic (", " >> nonReservedSymbol "set" (includeIdent := true)) >> Parser.ident >>
     optional (checkColGt >> termParser maxPrec))) >>
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
    ident-led parsers by the ident *kind*, and `component`/`state`/`key`/`view` stay usable
    as names everywhere else (tags expand to `Child.component`, every app has a `view`,
    `key` is a JSX attribute). -/
@[command_parser] def componentCmd : Parser := leading_parser
  optional Command.docComment >> atomic (identEq `component) >> ident >> " where " >>
  -- `manyIndent`, exactly like `structure` fields: the saved column makes a field's TYPE
  -- term stop at the next `state`/`emits`/`view` line (an application argument must be
  -- indented past the field's own column), which is what lets the default be optional
  manyIndent (node `Qed.componentStateItem
    -- a field without a default makes the component parent-owned-only (no `mount`, the
    -- parent seeds every instance). The default is max-precedence so it cannot swallow
    -- what follows on the same line; parenthesize a compound default, as in a JSX splice
    ((atomic (identEq `state) <|> atomic (identEq `prop) <|> atomic (identEq `collection)) >> ident >> " : " >> termParser >>
     optional (" := " >> termParser maxPrec))) >>
  -- `key f`: the state field that identifies a row when the parent owns a list of these
  -- (the reconciliation/routing key a `state={…}` tag uses). Generates `keyOf`/`updateKeyed`.
  optional (node `Qed.componentKey (atomic (identEq `key) >> ident)) >>
  optional (node `Qed.componentEmits (atomic (identEq `emits) >> termParser maxPrec)) >>
  -- the body is max-precedence (a JSX element is one closed atom) so that application
  -- cannot extend past it and swallow a following ident-led `component` declaration
  manyIndent (node `Qed.componentAction (atomic (identEq `action) >> ident >> many (node `Qed.componentActionParam ("(" >> ident >> " : " >> termParser >> ")")) >> optional (atomic (identEq `when) >> termParser maxPrec) >> " => " >> termParser maxPrec)) >>
  identEq `view >> " => " >> termParser maxPrec

/-- One `set`/`send` site collected from a `component` view: the fields it sets with
    their expressions (`none` for the payload form `set f`; empty for a pure `send`), the
    constructor it became, and the sent output, if any. `key` identifies the site
    syntactically, so identical sites share one constructor. -/
private structure SetSite where
  key     : String
  assigns : Array (Lean.Name × Option Lean.Term)
  ctor    : Lean.Name
  send?   : Option Lean.Term
  params  : Array (Lean.Ident × Lean.Term) := #[]
  guard?  : Option Lean.Term := none

/-- Does `n` occur as an identifier anywhere under `stx`? How the `component` elaborator
    decides which state fields a set expression (or the view body) mentions, so only those
    are bound from the model. -/
private partial def mentionsIdent (stx : Lean.Syntax) (n : Lean.Name) : Bool :=
  match stx with
  | .ident _ _ v _ => n.isPrefixOf v.eraseMacroScopes
  | .node _ _ args => args.any (mentionsIdent · n)
  | _ => false

open Lean Elab Command in
/-- Intern a `set`/`send` site: identical sites share one constructor; fresh ones get a
    name derived from the fields (`set_f`, `set_f_g`, `set_f_2`, …) or `send`/`send_2`
    for a pure output. -/
private def registerSite (sites : IO.Ref (Array SetSite))
    (assigns : Array (Name × Option Term)) (send? : Option Term) : CommandElabM Name := do
  let pp : Option Term → String := fun
    | some e => e.raw.reprint.getD (toString e.raw)
    | none   => "·"
  let key := String.intercalate "|" (assigns.toList.map fun (f, e?) => s!"{f}={pp e?}")
    ++ s!"|{pp send?}"
  let cur ← sites.get
  match cur.find? (·.key == key) with
  | some site => return site.ctor
  | none =>
      let base := if assigns.isEmpty then "send"
        else "set_" ++ String.intercalate "_" (assigns.toList.map (toString ·.1))
      let mut name := Name.mkSimple base
      let mut i := 2
      while cur.any (·.ctor == name) do
        name := Name.mkSimple s!"{base}_{i}"
        i := i + 1
      sites.set (cur.push { key, assigns, ctor := name, send? })
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
    -- collect the chain: the leading `set f e?` plus every `, set g e?` continuation
    let mut assigns : Array (Name × Option Term) := #[]
    let pairs := #[(stx[1], stx[2])] ++ stx[3].getArgs.map fun more => (more[2], more[3])
    for (fId, eOpt) in pairs do
      let fname := fId.getId.eraseMacroScopes
      unless fields.contains fname do
        throwErrorAt fId "`set {fname}`: not a `state` field of this component (fields: {fields.toList})"
      if assigns.any (·.1 == fname) then
        throwErrorAt fId "`set {fname}`: this handler already sets `{fname}`"
      let expr? : Option Term := if eOpt.getNumArgs == 1 then some ⟨eOpt[0]⟩ else none
      if expr?.isNone && assigns.any (·.2.isNone) then
        throwErrorAt fId "`set {fname}`: only one payload-form `set` (no expression) per \
          handler, there is just one incoming value to store"
      assigns := assigns.push (fname, expr?)
    let send? : Option Term := if stx[4].getNumArgs == 3 then some ⟨stx[4][2]⟩ else none
    if send?.isSome && !hasEmits then noEmits stx[4]
    let ctor ← registerSite sites assigns send?
    return mkIdent (msgPath ++ ctor)
  else if stx.getKind == ``sendTerm then
    unless hasEmits do noEmits stx
    let ctor ← registerSite sites #[] (some ⟨stx[1]⟩)
    return mkIdent (msgPath ++ ctor)
  else
    match stx with
    | .node info kind args =>
        return .node info kind (← args.mapM (replaceSets fields msgPath hasEmits sites))
    | _ => return stx

open Lean Elab Command in
@[command_elab componentCmd] def elabComponentCmd : CommandElab := fun stx => do
      -- node shape: [doc?, kw, name, "where", (stateItem: [kw, f, ":", ty, (":=", default)?])*,
      --              (key: [kw, f])?, (emits: [kw, ty])?, actions*, kw, "=>", body]
      let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
        if stx[0].getNumArgs == 1 then some ⟨stx[0][0]⟩ else none
      let t : Ident := ⟨stx[2]⟩
      let allItems := stx[4].getArgs
      let propItems := allItems.filter (fun it => it[0].getId == `prop)
      let collections := allItems.filter (fun it => it[0].getId == `collection)
      let items := allItems.filter (fun it => it[0].getId != `prop)
      let fs  : Array Ident := items.map fun it => ⟨it[1]⟩
      let tys : Array Term ← items.mapM fun it =>
        if it[0].getId == `collection then
          `(Array $(mkIdent (it[3].getId ++ `State)))
        else pure ⟨it[3]⟩
      let ds : Array (Option Term) ← items.mapM fun it =>
        if it[4].getNumArgs == 2 then pure (some ⟨it[4][1]⟩)
        else if it[0].getId == `collection then return some (← `(#[]))
        else pure none
      let pfs : Array Ident := propItems.map fun it => ⟨it[1]⟩
      let ptys : Array Term := propItems.map fun it => ⟨it[3]⟩
      let propsId := mkIdent (t.getId ++ `Props)
      let hasProps := !propItems.isEmpty
      let keyF?  : Option Ident := if stx[5].getNumArgs == 1 then some ⟨stx[5][0][1]⟩ else none
      let outTy? : Option Term  := if stx[6].getNumArgs == 1 then some ⟨stx[6][0][1]⟩ else none
      let body : Term := ⟨stx[10]⟩
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
      let allNames := fieldNames ++ pfs.map (·.getId)
      if allNames.toList.eraseDups.length != allNames.size then
        throwErrorAt t "component fields must have distinct names"
      if let some kf := keyF? then
        unless fieldNames.contains kf.getId.eraseMacroScopes do
          throwErrorAt kf "`key {kf.getId}`: not a `state` field of this component (fields: {fieldNames.toList})"
        if outTy?.isSome then
          throwErrorAt kf "`key` marks the row identity for parent-owned use (`state=\{…}`), \
            and a parent-owned child's `emits` output would have no receiver; drop one of the two"
      -- the registry id: the component's full name, unique app-wide by construction
      let idLit := Syntax.mkStrLit (((← getCurrNamespace) ++ t.getId).toString)
      -- Collect the `set`/`send` sites; each becomes a `Msg` constructor reference in the body.
      let sitesRef ← IO.mkRef (#[] : Array SetSite)
      for a in stx[7].getArgs do
        let name := a[1].getId
        if (← sitesRef.get).any (·.ctor == name) || collections.any (·[1].getId == name) then
          throwErrorAt a[1] "duplicate action name `{name}`"
        let before ← sitesRef.get
        let actionRef ← IO.mkRef (#[] : Array SetSite)
        let _ ← replaceSets fieldNames (t.getId ++ `Msg) outTy?.isSome actionRef a[5]
        let actionSites ← actionRef.get
        unless actionSites.size == 1 && (a[5].getKind == ``setTerm || a[5].getKind == ``sendTerm) do
          throwErrorAt a[5] "an action must be a `set`/`send` chain"
        let some site := actionSites[0]? | throwErrorAt a "empty action"
        let params : Array (Ident × Term) := a[2].getArgs.map fun p => (⟨p[1]⟩, ⟨p[3]⟩)
        if !params.isEmpty && site.assigns.any (·.2.isNone) then
          throwErrorAt a "use an explicit set value in an action with parameters"
        let names := params.map (·.1.getId)
        if names.toList.eraseDups.length != names.size || names.any allNames.contains then
          throwErrorAt a "action parameters must be distinct and must not shadow fields"
        let guard? : Option Term := if a[3].getNumArgs == 2 then some ⟨a[3][1]⟩ else none
        sitesRef.set (before.push { site with ctor := name, key := s!"action:{name}", params, guard? })
      let body' : Term := ⟨← replaceSets fieldNames (t.getId ++ `Msg) outTy?.isSome sitesRef body⟩
      let sites ← sitesRef.get
      -- Msg: one first-order constructor per distinct site (the payload form `set f` takes
      -- the field's value type as its argument).
      let isPayload : SetSite → Bool := fun site => site.assigns.any (·.2.isNone)
      let mut ctors ← sites.mapM fun site => do
        let cId := mkIdent site.ctor
        if !site.params.isEmpty then
          let ids := site.params.map (·.1)
          let ts := site.params.map (·.2)
          `(Lean.Parser.Command.ctor| | $cId:ident $[($ids:ident : $ts)]*)
        else match site.assigns.find? (·.2.isNone) with
        | some (f, _) =>
          let some idx := fieldNames.findIdx? (· == f) | throwError "component: internal"
          `(Lean.Parser.Command.ctor| | $cId:ident (v : $(tys[idx]!)))
        | none =>
          `(Lean.Parser.Command.ctor| | $cId:ident)
      for col in collections do
        let nm := mkIdent col[1].getId
        let cm := mkIdent (col[3].getId ++ `Msg)
        ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $nm:ident (key : String) (msg : $cm)))
      let msgCmd ← if ctors.isEmpty then `(command| inductive $msgId)
        else `(command| inductive $msgId where $[$ctors:ctor]*)
      -- update: interpret each constructor. Set/send expressions are evaluated HERE, over
      -- the current (pre-update) state: each state field they mention is bound from `s`
      -- first. With `emits` the arms return `(state', some output / none)`.
      let mut arms ← sites.mapM fun site => do
        let cFull := mkIdent (t.getId ++ `Msg ++ site.ctor)
        let stateTerm : Term ←
          if site.assigns.isEmpty then `(s)
          else do
            let fIds := site.assigns.map fun (f, _) => mkIdent f
            let vals ← site.assigns.mapM fun (_, e?) => match e? with
              | some e => pure e
              | none   => `(v)
            `({ s with $[$fIds:ident := $vals],* })
        let rhs0 : Term ← match outTy? with
          | none => pure stateTerm
          | some _ => match site.send? with
            | some o => `(($stateTerm, some $o))
            | none   => `(($stateTerm, none))
        let mut rhs := rhs0
        if let some guard := site.guard? then
          let unchanged ← if outTy?.isSome then `((s, none)) else `(s)
          rhs ← `(if $guard then $rhs else $unchanged)
        for g in allNames.reverse do
          let mentioned := (site.assigns.any fun (_, e?) => e?.any (mentionsIdent ·.raw g)) ||
                           (site.send?.any (mentionsIdent ·.raw g)) ||
                           (site.guard?.any (mentionsIdent ·.raw g))
          if mentioned then
            let gId := mkIdent g
            if fieldNames.contains g then
              rhs ← `(let $gId:ident := (s.$gId:ident); $rhs)
            else rhs ← `(let $gId:ident := (p.$gId:ident); $rhs)
        if !site.params.isEmpty then
          let ids : Array Term := site.params.map (fun p => ⟨p.1.raw⟩)
          `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $ids* => $rhs)
        else if isPayload site then
          `(Lean.Parser.Term.matchAltExpr| | $cFull:ident v => $rhs)
        else
          `(Lean.Parser.Term.matchAltExpr| | $cFull:ident => $rhs)
      for col in collections do
        let nm := mkIdent col[1].getId
        let ctor := mkIdent (t.getId ++ `Msg ++ col[1].getId)
        let upd := mkIdent (col[3].getId ++ `updateKeyed)
        let next ← `({ s with $nm:ident := $upd s.$nm:ident k msg })
        let rhs ← if outTy?.isSome then `(($next, none)) else pure next
        arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $ctor k msg => $rhs))
      let retTy : Term ← match outTy? with
        | some o => `($stateId × Option $o)
        | none   => `($stateId)
      let updateBody ← if arms.isEmpty then `(fun m => nomatch m)
        else `(fun m => match m with $[$arms:matchAlt]*)
      let updateCmd ← if hasProps then
          `(command| def $updateId (p : $propsId) (s : $stateId) : $msgId → $retTy := $updateBody)
        else `(command| def $updateId (s : $stateId) : $msgId → $retTy := $updateBody)
      -- view: the body with set sites replaced; state fields it mentions are in scope by name.
      let mut viewBody := body'
      for g in allNames.reverse do
        if mentionsIdent viewBody.raw g then
          let gId := mkIdent g
          if fieldNames.contains g then
            viewBody ← `(let $gId:ident := (s.$gId:ident); $viewBody)
          else viewBody ← `(let $gId:ident := (p.$gId:ident); $viewBody)
      -- JSON codec for the state (snapshot/restore and the keyed store are strings).
      let keyLits := fs.map fun f => Syntax.mkStrLit (toString f.getId)
      let pairs ← (fs.zip keyLits).mapM fun (f, k) => `(($k, toJson (x.$f:ident)))
      let decodes ← (tys.zip keyLits).mapM fun (ty, k) =>
        `((FromJsonField.fromField j $k : Except String $ty))
      let propFields ← propItems.mapM fun it => do
        let f : Ident := ⟨it[1]⟩
        let ty : Term := ⟨it[3]⟩
        if it[4].getNumArgs == 2 then
          let d : Term := ⟨it[4][1]⟩
          `(Lean.Parser.Command.structExplicitBinder| ($f : $ty := $d))
        else `(Lean.Parser.Command.structExplicitBinder| ($f : $ty))
      let stateFields ← ((fs.zip tys).zip ds).mapM fun ((f, ty), d?) =>
        match d? with
        | some d => `(Lean.Parser.Command.structExplicitBinder| ($f : $ty := $d))
        | none => `(Lean.Parser.Command.structExplicitBinder| ($f : $ty))
      let mut cmds : Array (TSyntax `command) := #[
        ← `(command| structure $propsId where $[$propFields:structExplicitBinder]*),
        ← `(command| structure $stateId where $[$stateFields:structExplicitBinder]*),
        msgCmd,
        updateCmd,
        ← (if hasProps then
          `(command| def $viewId (p : $propsId) (s : $stateId) : Html $msgId := $viewBody)
        else `(command| def $viewId (s : $stateId) : Html $msgId := $viewBody)) ]
      if outTy?.isNone then
        let renderId := mkIdent (t.getId ++ `render)
        let rendered ← if hasProps then `($viewId p s) else `($viewId s)
        cmds := cmds.push (← `(command| def $renderId {parentMsg : Type}
          (p : $propsId) (route : $msgId → parentMsg) (s : $stateId) : Html parentMsg :=
          ($rendered).map route))
        if hasProps then
          let compId := mkIdent (t.getId ++ `component)
          cmds := cmds.push (← `(command| def $compId (p : $propsId) : Component $stateId $msgId :=
            { update := $updateId p, view := $viewId p }))
          if let some kf := keyF? then
            let keyId := mkIdent (t.getId ++ `keyOf)
            let updId := mkIdent (t.getId ++ `updateKeyed)
            let eachId := mkIdent (t.getId ++ `each)
            cmds := cmds ++ #[
              ← `(command| def $keyId (s : $stateId) : String := toString s.$kf:ident),
              ← `(command| def $updId (p : $propsId) (rows : Array $stateId) (k : String)
                (msg : $msgId) : Array $stateId := Component.updateKeyed ($compId p) $keyId rows k msg),
              ← `(command| def $eachId {parentMsg : Type} (p : $propsId) (rows : Array $stateId)
                (route : String → $msgId → parentMsg)
                (wrap : $stateId → Html parentMsg → Html parentMsg := fun _ child => child)
                : Array (Html parentMsg) := Component.each ($compId p) $keyId rows route wrap)]
      -- without `emits` the update is `State → Msg → State`, so the declaration is also a
      -- `Component`: a `state={…}` tag mounts it into a parent-owned keyed list with no
      -- extra code
      if outTy?.isNone && !hasProps then
        let compId := mkIdent (t.getId ++ `component)
        cmds := cmds.push <|
          ← `(command| $[$doc?:docComment]? def $compId : Component $stateId $msgId :=
                { update := $updateId, view := $viewId })
        -- `key f` names the row identity once: `keyOf` is the routing/reconciliation key a
        -- `state={…}` tag tags messages with, and `updateKeyed` delivers one back to its row
        if let some kf := keyF? then
          let keyOfId       := mkIdent (t.getId ++ `keyOf)
          let updateKeyedId := mkIdent (t.getId ++ `updateKeyed)
          let eachId := mkIdent (t.getId ++ `each)
          let kfId          := mkIdent kf.getId.eraseMacroScopes
          cmds := cmds ++ #[
            ← `(command| def $keyOfId (s : $stateId) : String := toString s.$kfId),
            ← `(command| def $updateKeyedId (rows : Array $stateId) (k : String)
                  (msg : $msgId) : Array $stateId :=
                  Component.updateKeyed $compId $keyOfId rows k msg),
            ← `(command| def $eachId {parentMsg : Type} (rows : Array $stateId)
                (route : String → $msgId → parentMsg)
                (wrap : $stateId → Html parentMsg → Html parentMsg := fun _ child => child)
                : Array (Html parentMsg) := Component.each $compId $keyOfId rows route wrap)]
      -- the framework-owned mount (`reg`/`mount`) needs an `init` and a serializable state,
      -- so it exists only when every field has a default; without one the component is
      -- parent-owned-only and the parent seeds every instance
      do
        let pk := pfs.map fun f => Syntax.mkStrLit (toString f.getId)
        let pp ← (pfs.zip pk).mapM fun (f, k) => `(($k, toJson (x.$f:ident)))
        let pd ← (ptys.zip pk).mapM fun (ty, k) => `((FromJsonField.fromField j $k : Except String $ty))
        cmds := cmds ++ #[
          ← `(command| instance : ToJson $propsId := ⟨fun x => Json.obj [$[$pp],*]⟩),
          ← `(command| instance : FromJson $propsId := ⟨fun j => do
            $[let $pfs:ident ← $pd:term]*
            return { $[$pfs:ident],* }⟩)]
      cmds := cmds ++ #[
          ← `(command| def $toJsonId (x : $stateId) : Json := Json.obj [$[$pairs],*]),
          ← `(command| def $fromJsonId (j : Json) : Except String $stateId := do
                $[let $fs:ident ← $decodes:term]*
                return { $[$fs:ident],* }),
          ← `(command| instance : ToJson $stateId := ⟨$toJsonId⟩),
          ← `(command| instance : FromJson $stateId := ⟨$fromJsonId⟩)]
      if ds.all (·.isSome) then
        let dsT := ds.filterMap id
        cmds := cmds ++ #[
          ← `(command| def $initId : $stateId := { $[$fs:ident := $dsT],* }),
          ← (if hasProps then
              match outTy? with
              | none => `(command| def $regId : LocalDef :=
                  LocalDef.ofProps $idLit $initId $viewId (fun p s m => ($updateId p s m, (none : Option Bool))))
              | some _ => `(command| def $regId : LocalDef :=
                  LocalDef.ofProps $idLit $initId $viewId $updateId)
            else match outTy? with
            | none => `(command| $[$doc?:docComment]? def $regId : LocalDef :=
                LocalDef.ofSimple $idLit $initId $viewId $updateId)
            | some _ => `(command| $[$doc?:docComment]? def $regId : LocalDef :=
                LocalDef.of $idLit $initId $viewId $updateId)),
          ← `(command| $[$doc?:docComment]? def $mountId {msg : Type} (key : String) : Attr msg :=
                localMount $idLit key) ]
        -- with `emits T`, also generate the receiving mount: the parent maps the output to
        -- one of its own messages (often a payload-form `set f` of its own)
        if let some o := outTy? then
          let mountWithId := mkIdent (t.getId ++ `mountWith)
          cmds := cmds.push <|
            ← `(command| $[$doc?:docComment]? def $mountWithId {msg : Type}
                  (key : String) (onOut : $o → msg) : Attr msg :=
                  localMountWith $idLit key (fun out => some (onOut out)))
      -- `regs`: the registrations this component's view needs, its own `reg` (when
      -- mountable) plus, transitively, those of every component tag in its view. `ui`
      -- and the generated `app` collect these automatically, no `locals := […]` by hand.
      let regsId    := mkIdent (t.getId ++ `regs)
      let mountable := ds.all (·.isSome)
      let own : Term ← if mountable then `([$regId]) else `(([] : List LocalDef))
      cmds := cmds.push (← `(command| def $regsId : List LocalDef :=
        LocalDef.dedupe ($own ++ localRegistrations $viewId)))
      -- with every field defaulted and no `emits`, the component can BE the whole app:
      -- `def app := Name.app` is a complete program (state → model, the generated
      -- update → transition, nested tags registered)
      if mountable && outTy?.isNone && !hasProps then
        let appId := mkIdent (t.getId ++ `app)
        cmds := cmds.push <|
          ← `(command| $[$doc?:docComment]? def $appId : App $stateId $msgId :=
                withLocalRegistry (mkApp $initId $updateId (View.ofHtml $viewId) (locals := $regsId)))
      for c in cmds do elabCommand c

end Qed
