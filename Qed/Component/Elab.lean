import Qed.Component.Core
import Qed.Runtime
import Qed.Jsx
import Qed.Invariant.View
import Lean

namespace Qed

open Lean Parser in
@[term_parser] def setTerm := leading_parser:maxPrec
  nonReservedSymbol "set" (includeIdent := true) >> Parser.ident >>
  optional (checkColGt >> termParser maxPrec) >>
  many (node `Qed.setMore
    (atomic (", " >> nonReservedSymbol "set" (includeIdent := true)) >> Parser.ident >>
     optional (checkColGt >> termParser maxPrec))) >>
  optional (", " >> nonReservedSymbol "send" (includeIdent := true) >> termParser maxPrec)

open Lean Parser in
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
def compFieldClause : Parser := leading_parser
  withPosition (
    (atomic (identEq `state) <|> atomic (identEq `prop) <|> atomic (identEq `collection)) >>
    ident >>
    optional (" : " >> termParser) >>
    optional (" := " >> termParser))

open Lean Parser in
def compKeyClause : Parser := leading_parser
  withPosition (atomic (identEq `key) >> ident)

open Lean Parser in
def compEmitsClause : Parser := leading_parser
  withPosition (atomic (identEq `emits) >> termParser)

open Lean Parser in
def actionLetStmt : Parser := leading_parser
  withPosition ("let " >> ident >> optional (" : " >> termParser) >> " := " >> termParser)

open Lean Parser in
def actionAssignStmt : Parser := leading_parser
  withPosition (atomic (ident >> (symbol ":=" <|> symbol "+=" <|> symbol "-=")) >> termParser)

open Lean Parser in
def actionSetStmt : Parser := leading_parser
  withPosition (
    atomic (nonReservedSymbol "set" (includeIdent := true)) >> ident >>
    optional (checkColGt >> termParser maxPrec))

open Lean Parser in
def actionSendStmt : Parser := leading_parser
  withPosition (
    atomic (nonReservedSymbol "send" (includeIdent := true)) >> checkColGt >> termParser)

open Lean Parser in
def actionStmt : Parser :=
  actionLetStmt <|> actionAssignStmt <|> actionSetStmt <|> actionSendStmt

open Lean Parser in
def compActionClause : Parser := leading_parser
  withPosition (
    atomic (identEq `action) >> ident >>
    many (node `Qed.componentActionParam ("(" >> ident >> " : " >> termParser >> ")")) >>
    optional (atomic (identEq `when) >> termParser) >> " => " >>
    checkColGt >> actionStmt >>
    many (atomic (optional "," >> checkColGt >> actionStmt)))

open Lean Parser in
def compInvName : Parser := leading_parser
  ident >> " : "

open Lean Parser in
def compInvariantClause : Parser := leading_parser
  withPosition (
    "invariant " >>
    optional (atomic compInvName) >>
    sepBy1 termParser "," >>
    optional (" holds_in " >> identEq `view >> optional (" assuming " >> termParser maxPrec)) >>
    optional (" using " >> "[" >> sepBy termParser "," >> "]") >>
    optional (" := " >> termParser))

open Lean Parser in
def compClause : Parser :=
  compFieldClause <|> compKeyClause <|> compEmitsClause <|> compActionClause <|> compInvariantClause

open Lean Parser in
@[command_parser] def componentCmd : Parser := leading_parser
  optional Command.docComment >>
  withPosition (
    "component " >> ident >> " where " >>
    many (checkColGt >> compClause) >>
    checkColGt >> identEq `view >> " => " >> checkColGt >> termParser >>
    many (checkColGt >> compInvariantClause))

private structure SetSite where
  key     : String
  lets    : Array (Lean.Ident × Option Lean.Term × Lean.Term) := #[]
  assigns : Array (Lean.Name × Option Lean.Term)
  ctor    : Lean.Name
  send?   : Option Lean.Term
  params  : Array (Lean.Ident × Lean.Term) := #[]
  guard?  : Option Lean.Term := none

private def isCdot (stx : Lean.Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Term.cdot || (stx.reprint.getD "").trimmed == "·"

private def atomStr : Lean.Syntax → String
  | .node _ _ #[.atom _ v] => v
  | .atom _ v              => v
  | _                      => ""

private partial def mentionsIdent (stx : Lean.Syntax) (n : Lean.Name) : Bool :=
  match stx with
  | .ident _ _ v _ => n.isPrefixOf v.eraseMacroScopes
  | .node _ _ args => args.any (mentionsIdent · n)
  | _ => false

open Lean Elab Command in
private def desugarAssign (fname : Name) (op : String) (rhs : Term) : CommandElabM Term := do
  let fIdent := mkIdent fname
  match op with
  | ":=" => pure rhs
  | "+=" => `($fIdent + ($rhs))
  | "-=" => `($fIdent - ($rhs))
  | _    => throwErrorAt rhs s!"unknown assignment operator '{op}'"

open Lean Elab Command in
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
private partial def replaceSets (fields : Array Name) (msgPath : Name) (hasEmits : Bool)
    (sites : IO.Ref (Array SetSite)) (stx : Syntax) : CommandElabM Syntax := do
  let noEmits (ref : Syntax) : CommandElabM Unit :=
    throwErrorAt ref "`send` bubbles an output, but this component declares no output type; \
      add `emits T` between the `state` fields and the `view`"
  if stx.getKind == ``setTerm then
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
    return mkIdent (msgPath ++ (← registerSite sites assigns send?))
  else if stx.getKind == ``sendTerm then
    unless hasEmits do noEmits stx
    return mkIdent (msgPath ++ (← registerSite sites #[] (some ⟨stx[1]⟩)))
  else if stx.getKind == ``Qed.Jsx.attrValAssign then
    let mut assigns : Array (Name × Option Term) := #[]
    let moreItems := stx[4].getArgs.map fun m =>
      let it := if m.getKind == `Qed.Jsx.jsxAssignItem then m else m[m.getNumArgs - 1]!
      (it[0], atomStr it[1], (⟨it[2]⟩ : Term))
    let allItems := #[(stx[1], atomStr stx[2], (⟨stx[3]⟩ : Term))] ++ moreItems
    for (fId, op, rhs) in allItems do
      let fname := fId.getId.eraseMacroScopes
      unless fields.contains fname do
        throwErrorAt fId "`{fname}`: not a `state` field of this component (fields: {fields.toList})"
      if assigns.any (·.1 == fname) then
        throwErrorAt fId "`{fname}`: this handler already updates `{fname}`"
      if op == ":=" && isCdot rhs.raw then
        if assigns.any (·.2.isNone) then
          throwErrorAt fId "`{fname} := ·`: only one `·` placeholder per handler"
        assigns := assigns.push (fname, none)
      else
        let val ← desugarAssign fname op rhs
        assigns := assigns.push (fname, some val)
    let send? : Option Term := if stx[5].getNumArgs == 3 then some ⟨stx[5][2]⟩ else none
    if send?.isSome && !hasEmits then noEmits stx[5]
    let ctor ← registerSite sites assigns send?
    return Syntax.node .none ``Qed.Jsx.attrValExpr #[stx[0], mkIdent (msgPath ++ ctor), stx[6]]
  else if stx.getKind == ``Qed.Jsx.attrNamed && atomStr stx[0] == "bind" &&
      stx[1].getNumArgs == 2 && stx[1][1].getKind == ``Qed.Jsx.attrValExpr then
    let inner := stx[1][1]
    if inner[1].getKind == ``Qed.Jsx.jsxTermExpr && inner[1][0].isIdent then
      let fId : Ident := ⟨inner[1][0]⟩
      let fname := fId.getId.eraseMacroScopes
      unless fields.contains fname do
        throwErrorAt fId "`bind=\{{fname}}`: not a `state` field of this component (fields: {fields.toList})"
      let ctor ← registerSite sites #[(fname, none)] none
      let pairT ← `(($fId, $(mkIdent (msgPath ++ ctor))))
      let inner' := Syntax.node .none ``Qed.Jsx.attrValExpr #[inner[0], pairT.raw, inner[2]]
      let valNode' := Syntax.node .none stx[1].getKind #[stx[1][0], inner']
      return Syntax.node .none stx.getKind #[stx[0], valNode']
    else
      let args' ← stx.getArgs.mapM (replaceSets fields msgPath hasEmits sites)
      return Syntax.node .none stx.getKind args'
  else
    match stx with
    | .node info kind args =>
        return .node info kind (← args.mapM (replaceSets fields msgPath hasEmits sites))
    | _ => return stx

open Lean Elab Command in
private structure ComponentSpec where
  doc?        : Option (TSyntax ``Lean.Parser.Command.docComment)
  t           : Ident
  collections : Array (Ident × Ident)
  fs          : Array Ident
  optTys      : Array (Option Term)
  tys         : Array Term := #[]
  ds          : Array (Option Term)
  pfs         : Array Ident
  optPtys     : Array (Option Term)
  ptys        : Array Term := #[]
  pds         : Array (Option Term)
  hasProps    : Bool
  keyF?       : Option Ident
  outTy?      : Option Term
  actions     : Array Syntax
  invariants  : Array Syntax
  body        : Term
  fieldNames  : Array Name
  allNames    : Array Name

open Lean Elab Command in
private def parseComponentSpec (stx : Syntax) : CommandElabM ComponentSpec := do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if stx[0].getNumArgs == 1 then some ⟨stx[0][0]⟩ else none
  let t : Ident := ⟨stx[2]⟩
  let clauses := stx[4].getArgs
  let mut fs          : Array Ident := #[]
  let mut optTys      : Array (Option Term) := #[]
  let mut ds          : Array (Option Term) := #[]
  let mut pfs         : Array Ident := #[]
  let mut optPtys     : Array (Option Term) := #[]
  let mut pds         : Array (Option Term) := #[]
  let mut collections : Array (Ident × Ident) := #[]
  let mut keyF?       : Option Ident := none
  let mut outTy?      : Option Term := none
  let mut actions     : Array Syntax := #[]
  let mut invariants  : Array Syntax := #[]
  for cl in clauses do
    let k := cl.getKind
    if k == ``compFieldClause then
      let role := cl[0].getId
      let fId : Ident := ⟨cl[1]⟩
      let ty? : Option Term := if cl[2].getNumArgs == 2 then some ⟨cl[2][1]⟩ else none
      let d?  : Option Term := if cl[3].getNumArgs == 2 then some ⟨cl[3][1]⟩ else none
      if role == `prop then
        if ty?.isNone && d?.isNone then
          throwErrorAt fId s!"`prop {fId.getId}` needs a type (`: Type`), a default (`:= value`), or both"
        pfs := pfs.push fId
        optPtys := optPtys.push ty?
        pds := pds.push d?
      else if role == `collection then
        let some colTy := ty? | throwErrorAt fId s!"`collection {fId.getId}` requires `: ChildComponent`"
        unless colTy.raw.isIdent do
          throwErrorAt colTy "`collection` target must be a child component name"
        let childId : Ident := ⟨colTy.raw⟩
        collections := collections.push (fId, childId)
        fs := fs.push fId
        optTys := optTys.push (some (← `(Array $(mkIdent (childId.getId ++ `State)))))
        ds := ds.push (some (← (match d? with | some d => pure d | none => `(#[]))))
      else
        if ty?.isNone && d?.isNone then
          throwErrorAt fId s!"`state {fId.getId}` needs a type (`: Type`), a default (`:= value`), or both"
        fs := fs.push fId
        optTys := optTys.push ty?
        ds := ds.push d?
    else if k == ``compKeyClause then
      if keyF?.isSome then throwErrorAt cl "duplicate `key` clause in component"
      keyF? := some ⟨cl[1]⟩
    else if k == ``compEmitsClause then
      if outTy?.isSome then throwErrorAt cl "duplicate `emits` clause in component"
      outTy? := some ⟨cl[1]⟩
    else if k == ``compActionClause then
      actions := actions.push cl
    else if k == ``compInvariantClause then
      invariants := invariants.push cl
  invariants := invariants ++ stx[8].getArgs
  let hasProps := !pfs.isEmpty
  let body : Term := ⟨stx[7]⟩
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
  return { doc?, t, collections, fs, optTys, ds, pfs, optPtys, pds,
           hasProps, keyF?, outTy?, actions, invariants, body, fieldNames, allNames }

open Lean Elab Command in
private def collectSitesAndRewriteBody (spec : ComponentSpec) :
    CommandElabM (Array SetSite × Term) := do
  let noEmits (ref : Syntax) : CommandElabM Unit :=
    throwErrorAt ref "`send` bubbles an output, but this component declares no output type; \
      add `emits T` between the `state` fields and the `view`"
  let sitesRef ← IO.mkRef (#[] : Array SetSite)
  for a in spec.actions do
    let name := a[1].getId
    if (← sitesRef.get).any (·.ctor == name) || spec.collections.any (·.1.getId == name) then
      throwErrorAt a[1] "duplicate action name `{name}`"
    let params : Array (Ident × Term) := a[2].getArgs.map fun p => (⟨p[1]⟩, ⟨p[3]⟩)
    let pNames := params.map (·.1.getId)
    if pNames.toList.eraseDups.length != pNames.size || pNames.any spec.allNames.contains then
      throwErrorAt a "action parameters must be distinct and must not shadow fields"
    let guard? : Option Term := if a[3].getNumArgs == 2 then some ⟨a[3][1]⟩ else none
    let restStmts := a[6].getArgs.map fun m =>
      if m.getKind == nullKind then m[m.getNumArgs - 1]! else m
    let stmts := #[a[5]] ++ restStmts
    let mut lets : Array (Ident × Option Term × Term) := #[]
    let mut assigns : Array (Name × Option Term) := #[]
    let mut send? : Option Term := none
    for s in stmts do
      let sk := s.getKind
      if sk == ``actionLetStmt then
        let lId : Ident := ⟨s[1]⟩
        let lTy? : Option Term := if s[2].getNumArgs == 2 then some ⟨s[2][1]⟩ else none
        let lVal : Term := ⟨s[4]⟩
        lets := lets.push (lId, lTy?, lVal)
      else if sk == ``actionAssignStmt then
        let fId : Ident := ⟨s[0]⟩
        let fname := fId.getId.eraseMacroScopes
        unless spec.fieldNames.contains fname do
          throwErrorAt fId "`{fname}`: not a `state` field of this component (fields: {spec.fieldNames.toList})"
        if assigns.any (·.1 == fname) then
          throwErrorAt fId "`{fname}`: this handler already updates `{fname}`"
        let op := atomStr s[1]
        if op == ":=" && isCdot s[2] then
          if assigns.any (·.2.isNone) then
            throwErrorAt fId "`{fname} := ·`: only one `·` placeholder per handler"
          assigns := assigns.push (fname, none)
        else
          let val ← desugarAssign fname op ⟨s[2]⟩
          assigns := assigns.push (fname, some val)
      else if sk == ``actionSetStmt then
        let fId : Ident := ⟨s[1]⟩
        let fname := fId.getId.eraseMacroScopes
        unless spec.fieldNames.contains fname do
          throwErrorAt fId "`set {fname}`: not a `state` field of this component (fields: {spec.fieldNames.toList})"
        if assigns.any (·.1 == fname) then
          throwErrorAt fId "`set {fname}`: this handler already sets `{fname}`"
        let expr? : Option Term := if s[2].getNumArgs == 1 then some ⟨s[2][0]⟩ else none
        if expr?.isNone && assigns.any (·.2.isNone) then
          throwErrorAt fId "`set {fname}`: only one payload-form `set` (no expression) per \
            handler, there is just one incoming value to store"
        assigns := assigns.push (fname, expr?)
      else if sk == ``actionSendStmt then
        unless spec.outTy?.isSome do noEmits s
        if send?.isSome then
          throwErrorAt s "duplicate `send` in action; an action emits at most one output"
        send? := some ⟨s[1]⟩
    if assigns.isEmpty && send?.isNone then
      throwErrorAt a "an action must update state or send an output"
    if !params.isEmpty && assigns.any (·.2.isNone) then
      throwErrorAt a "use an explicit set value in an action with parameters"
    let cur ← sitesRef.get
    sitesRef.set (cur.push {
      key := s!"action:{name}", lets, assigns, ctor := name, send?, params, guard? })
  let body' : Term := ⟨← replaceSets spec.fieldNames (spec.t.getId ++ `Msg) spec.outTy?.isSome sitesRef spec.body⟩
  return (← sitesRef.get, body')

open Lean Elab Command in
private def bindMentionedFields (spec : ComponentSpec) (shouldBind : Name → Bool)
    (body : Term) : CommandElabM Term := do
  let mut out := body
  for g in spec.allNames.reverse do
    if shouldBind g then
      let gId := mkIdent g
      if spec.fieldNames.contains g then
        out ← `(let $gId:ident := (s.$gId:ident); $out)
      else
        out ← `(let $gId:ident := (p.$gId:ident); $out)
  return out

open Lean Elab Command in
private def mkPropsBinders (spec : ComponentSpec) :
    CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  if spec.hasProps then
    let propsId := mkIdent (spec.t.getId ++ `Props)
    return #[← `(bracketedBinder| (p : $propsId))]
  else return #[]

open Lean Elab Command in
private def mkStructFields (ids : Array Ident) (tys : Array (Option Term)) (ds : Array (Option Term)) :
    CommandElabM (Array (TSyntax ``Lean.Parser.Command.structExplicitBinder)) :=
  ((ids.zip tys).zip ds).mapM fun ((f, ty?), d?) =>
    match ty?, d? with
    | some ty, some d => `(Lean.Parser.Command.structExplicitBinder| ($f : $ty := $d))
    | some ty, none   => `(Lean.Parser.Command.structExplicitBinder| ($f : $ty))
    | none,    some d => `(Lean.Parser.Command.structExplicitBinder| ($f := $d))
    | none,    none   => throwErrorAt f s!"field `{f.getId}` needs a type or default value"

open Lean Elab Command Meta in
private def resolveStructFieldTypes (compName structKind : Name)
    (ids : Array Ident) (optTys : Array (Option Term)) : CommandElabM (Array Term) := do
  let ns ← getCurrNamespace
  let env ← getEnv
  (ids.zip optTys).mapM fun (f, ty?) => do
    match ty? with
    | some ty => return ty
    | none =>
        let projName := ns ++ compName ++ structKind ++ f.getId
        let some info := env.find? projName
          | throwErrorAt f s!"could not infer type of `{f.getId}`; add an explicit `: Type`"
        liftTermElabM <| forallTelescope info.type fun _ cod =>
          PrettyPrinter.delab cod

open Lean Elab Command in
private def elabStructsAndResolveTypes (spec : ComponentSpec) : CommandElabM ComponentSpec := do
  let propsId := mkIdent (spec.t.getId ++ `Props)
  let stateId := mkIdent (spec.t.getId ++ `State)
  let propFields  ← mkStructFields spec.pfs spec.optPtys spec.pds
  let stateFields ← mkStructFields spec.fs spec.optTys spec.ds
  elabCommand (← `(command| structure $propsId where $[$propFields:structExplicitBinder]*))
  elabCommand (← `(command| structure $stateId where $[$stateFields:structExplicitBinder]*))
  let ptys ← resolveStructFieldTypes spec.t.getId `Props spec.pfs spec.optPtys
  let tys  ← resolveStructFieldTypes spec.t.getId `State spec.fs spec.optTys
  return { spec with ptys, tys }

open Lean Elab Command in
private def mkMsgAndUpdateCmds (spec : ComponentSpec) (sites : Array SetSite) :
    CommandElabM (TSyntax `command × TSyntax `command) := do
  let stateId  := mkIdent (spec.t.getId ++ `State)
  let msgId    := mkIdent (spec.t.getId ++ `Msg)
  let updateId := mkIdent (spec.t.getId ++ `update)
  let mut ctors ← sites.mapM fun site => do
    let cId := mkIdent site.ctor
    if !site.params.isEmpty then
      let ids := site.params.map (·.1)
      let ts := site.params.map (·.2)
      `(Lean.Parser.Command.ctor| | $cId:ident $[($ids:ident : $ts)]*)
    else match site.assigns.find? (·.2.isNone) with
    | some (f, _) =>
      let some idx := spec.fieldNames.findIdx? (· == f) | throwError "component: internal"
      `(Lean.Parser.Command.ctor| | $cId:ident (v : $(spec.tys[idx]!)))
    | none =>
      `(Lean.Parser.Command.ctor| | $cId:ident)
  for (colField, colChild) in spec.collections do
    let nm := mkIdent colField.getId
    let cm := mkIdent (colChild.getId ++ `Msg)
    ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $nm:ident (key : String) (msg : $cm)))
  let msgCmd ← if ctors.isEmpty then `(command| inductive $msgId)
    else `(command| inductive $msgId where $[$ctors:ctor]*)
  let mut arms ← sites.mapM fun site => do
    let cFull := mkIdent (spec.t.getId ++ `Msg ++ site.ctor)
    let stateTerm : Term ←
      if site.assigns.isEmpty then `(s)
      else do
        let fIds := site.assigns.map fun (f, _) => mkIdent f
        let vals ← site.assigns.mapM fun (_, e?) => e?.getDM `(v)
        `({ s with $[$fIds:ident := $vals],* })
    let rhs0 : Term ← match spec.outTy? with
      | none   => pure stateTerm
      | some _ => match site.send? with
        | some o => `(($stateTerm, some $o))
        | none   => `(($stateTerm, none))
    let mut core := rhs0
    for (lId, lTy?, lVal) in site.lets.reverse do
      core ← match lTy? with
        | some ty => `(let $lId:ident : $ty := $lVal; $core)
        | none    => `(let $lId:ident := $lVal; $core)
    let mut rhs := core
    if let some guard := site.guard? then
      let unchanged ← if spec.outTy?.isSome then `((s, none)) else `(s)
      rhs ← `(if $guard then $rhs else $unchanged)
    rhs ← bindMentionedFields spec (fun g =>
      (site.lets.any fun (_, ty?, v) => mentionsIdent v.raw g || ty?.any (mentionsIdent ·.raw g)) ||
      (site.assigns.any fun (_, e?) => e?.any (mentionsIdent ·.raw g)) ||
      (site.send?.any (mentionsIdent ·.raw g)) ||
      (site.guard?.any (mentionsIdent ·.raw g))) rhs
    if !site.params.isEmpty then
      let ids : Array Term := site.params.map (fun p => ⟨p.1.raw⟩)
      `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $ids* => $rhs)
    else if site.assigns.any (·.2.isNone) then
      `(Lean.Parser.Term.matchAltExpr| | $cFull:ident v => $rhs)
    else
      `(Lean.Parser.Term.matchAltExpr| | $cFull:ident => $rhs)
  for (colField, colChild) in spec.collections do
    let nm := mkIdent colField.getId
    let ctor := mkIdent (spec.t.getId ++ `Msg ++ colField.getId)
    let upd := mkIdent (colChild.getId ++ `updateKeyed)
    let next ← `({ s with $nm:ident := $upd s.$nm:ident k msg })
    let rhs ← if spec.outTy?.isSome then `(($next, none)) else pure next
    arms := arms.push (← `(Lean.Parser.Term.matchAltExpr| | $ctor k msg => $rhs))
  let retTy : Term ← match spec.outTy? with
    | some o => `($stateId × Option $o)
    | none   => `($stateId)
  let updateBody ← if arms.isEmpty then `(fun m => nomatch m)
    else `(fun m => match m with $[$arms:matchAlt]*)
  let pBinders ← mkPropsBinders spec
  let updateCmd ← `(command| def $updateId $[$pBinders:bracketedBinder]* (s : $stateId) : $msgId → $retTy := $updateBody)
  return (msgCmd, updateCmd)

open Lean Elab Command in
private def mkViewCmds (spec : ComponentSpec) (body' : Term)
    (msgCmd updateCmd : TSyntax `command) : CommandElabM (Array (TSyntax `command)) := do
  let doc?     := spec.doc?
  let propsId  := mkIdent (spec.t.getId ++ `Props)
  let stateId  := mkIdent (spec.t.getId ++ `State)
  let msgId    := mkIdent (spec.t.getId ++ `Msg)
  let updateId := mkIdent (spec.t.getId ++ `update)
  let viewId   := mkIdent (spec.t.getId ++ `view)
  let viewBody ← bindMentionedFields spec (mentionsIdent body'.raw) body'
  let pBinders ← mkPropsBinders spec
  let mut cmds : Array (TSyntax `command) := #[
    msgCmd,
    updateCmd,
    ← `(command| def $viewId $[$pBinders:bracketedBinder]* (s : $stateId) : Html $msgId := $viewBody) ]
  if spec.outTy?.isNone then
    let renderId    := mkIdent (spec.t.getId ++ `render)
    let renderTagId := mkIdent (spec.t.getId ++ `renderTag)
    let compId      := mkIdent (spec.t.getId ++ `toComponent)
    let rendered ← if spec.hasProps then `($viewId p s) else `($viewId s)
    let updExpr  ← if spec.hasProps then `($updateId p) else `($updateId)
    let viewExpr ← if spec.hasProps then `($viewId p) else `($viewId)
    let compExpr ← if spec.hasProps then `($compId p) else `($compId)
    cmds := cmds ++ #[
      ← `(command| def $renderId {parentMsg : Type} $[$pBinders:bracketedBinder]*
            (route : $msgId → parentMsg) (s : $stateId) : Html parentMsg := ($rendered).map route),
      ← (match spec.keyF? with
        | some kf =>
          let kfId := mkIdent kf.getId.eraseMacroScopes
          `(command| def $renderTagId {parentMsg : Type} (p : $propsId)
              (route : String → $msgId → parentMsg) (s : $stateId)
              (k : String := toString s.$kfId) : Html parentMsg := ($rendered).map (route k))
        | none =>
          `(command| def $renderTagId {parentMsg : Type} (p : $propsId)
              (route : $msgId → parentMsg) (s : $stateId) : Html parentMsg := ($rendered).map route)),
      ← `(command| $[$doc?:docComment]? def $compId $[$pBinders:bracketedBinder]*
            : Component $stateId $msgId := { update := $updExpr, view := $viewExpr }) ]
    if let some kf := spec.keyF? then
      let keyOfId       := mkIdent (spec.t.getId ++ `keyOf)
      let updateKeyedId := mkIdent (spec.t.getId ++ `updateKeyed)
      let eachId        := mkIdent (spec.t.getId ++ `each)
      let kfId          := mkIdent kf.getId.eraseMacroScopes
      cmds := cmds ++ #[
        ← `(command| def $keyOfId (s : $stateId) : String := toString s.$kfId),
        ← `(command| def $updateKeyedId $[$pBinders:bracketedBinder]*
              (rows : Array $stateId) (k : String) (msg : $msgId) : Array $stateId :=
              Component.updateKeyed $compExpr $keyOfId rows k msg),
        ← `(command| def $eachId {parentMsg : Type} $[$pBinders:bracketedBinder]*
              (rows : Array $stateId) (route : String → $msgId → parentMsg)
              (wrap : $stateId → Html parentMsg → Html parentMsg := fun _ child => child)
              : Array (Html parentMsg) := Component.each $compExpr $keyOfId rows route wrap) ]
  return cmds

open Lean Elab Command in
private def mkCodecAndMountCmds (spec : ComponentSpec) (idLit : StrLit) :
    CommandElabM (Array (TSyntax `command)) := do
  let doc?       := spec.doc?
  let fs         := spec.fs
  let pfs        := spec.pfs
  let propsId    := mkIdent (spec.t.getId ++ `Props)
  let stateId    := mkIdent (spec.t.getId ++ `State)
  let initId     := mkIdent (spec.t.getId ++ `init)
  let msgId      := mkIdent (spec.t.getId ++ `Msg)
  let updateId   := mkIdent (spec.t.getId ++ `update)
  let viewId     := mkIdent (spec.t.getId ++ `view)
  let regId      := mkIdent (spec.t.getId ++ `reg)
  let mountId    := mkIdent (spec.t.getId ++ `mount)
  let toJsonId   := mkIdent (spec.t.getId ++ `State ++ `toJson)
  let fromJsonId := mkIdent (spec.t.getId ++ `State ++ `fromJson)
  let mkCodecParts (ids : Array Ident) (tys : Array Term) := do
    let ks := ids.map fun f => Syntax.mkStrLit (toString f.getId)
    let enc ← (ids.zip ks).mapM fun (f, k) => `(($k, toJson (x.$f:ident)))
    let dec ← (tys.zip ks).mapM fun (ty, k) => `((FromJsonField.fromField j $k : Except String $ty))
    return (enc, dec)
  let (pairs, decodes) ← mkCodecParts fs spec.tys
  let (pp, pd)         ← mkCodecParts pfs spec.ptys
  let propsToJsonId   := mkIdent (spec.t.getId ++ `Props ++ `instToJson)
  let propsFromJsonId := mkIdent (spec.t.getId ++ `Props ++ `instFromJson)
  let stateToJsonId   := mkIdent (spec.t.getId ++ `State ++ `instToJson)
  let stateFromJsonId := mkIdent (spec.t.getId ++ `State ++ `instFromJson)
  let mut cmds : Array (TSyntax `command) := #[
    ← `(command| instance $propsToJsonId:ident : ToJson $propsId := ⟨fun x => Json.obj [$[$pp],*]⟩),
    ← `(command| instance $propsFromJsonId:ident : FromJson $propsId := ⟨fun j => do
      $[let $pfs:ident ← $pd:term]*
      return { $[$pfs:ident],* }⟩),
    ← `(command| def $toJsonId (x : $stateId) : Json := Json.obj [$[$pairs],*]),
    ← `(command| def $fromJsonId (j : Json) : Except String $stateId := do
          $[let $fs:ident ← $decodes:term]*
          return { $[$fs:ident],* }),
    ← `(command| instance $stateToJsonId:ident : ToJson $stateId := ⟨$toJsonId⟩),
    ← `(command| instance $stateFromJsonId:ident : FromJson $stateId := ⟨$fromJsonId⟩)]
  let mountable := spec.ds.all (·.isSome)
  if mountable then
    let dsT := spec.ds.filterMap id
    cmds := cmds ++ #[
      ← `(command| def $initId : $stateId := { $[$fs:ident := $dsT],* }),
      ← (if spec.hasProps then
          match spec.outTy? with
          | none => `(command| def $regId : LocalDef :=
              LocalDef.ofProps $idLit $initId $viewId (fun p s m => ($updateId p s m, (none : Option Bool))))
          | some _ => `(command| def $regId : LocalDef :=
              LocalDef.ofProps $idLit $initId $viewId $updateId)
        else match spec.outTy? with
        | none => `(command| $[$doc?:docComment]? def $regId : LocalDef :=
            LocalDef.ofSimple $idLit $initId $viewId $updateId)
        | some _ => `(command| $[$doc?:docComment]? def $regId : LocalDef :=
            LocalDef.of $idLit $initId $viewId $updateId)),
      ← `(command| $[$doc?:docComment]? def $mountId {msg : Type} (key : String) : Attr msg :=
            localMount $idLit key) ]
    if let some o := spec.outTy? then
      let mountWithId := mkIdent (spec.t.getId ++ `mountWith)
      cmds := cmds.push <|
        ← `(command| $[$doc?:docComment]? def $mountWithId {msg : Type}
              (key : String) (onOut : $o → msg) : Attr msg :=
              localMountWith $idLit key (fun out => some (onOut out)))
  let regsId := mkIdent (spec.t.getId ++ `regs)
  let own : Term ← if mountable then `([$regId]) else `(([] : List LocalDef))
  cmds := cmds.push (← `(command| def $regsId : List LocalDef :=
    LocalDef.dedupe ($own ++ localRegistrations $viewId)))
  if mountable && spec.outTy?.isNone && !spec.hasProps then
    let appId := mkIdent (spec.t.getId ++ `app)
    cmds := cmds.push <|
      ← `(command| $[$doc?:docComment]? def $appId : App $stateId $msgId :=
            withLocalRegistry (mkApp $initId $updateId (View.ofHtml $viewId) (locals := $regsId)))
  return cmds

open Lean Elab Command in
private def freshCompInvIdent (ref : Syntax) (compId : Name) : CommandElabM Ident := do
  let env ← getEnv
  let ns ← getCurrNamespace
  let base := compId ++ `inv
  if !env.contains (ns ++ base) then
    return mkIdentFrom ref base
  let mut idx := 2
  let mut cand := compId ++ Name.mkSimple s!"inv_{idx}"
  while env.contains (ns ++ cand) do
    idx := idx + 1
    cand := compId ++ Name.mkSimple s!"inv_{idx}"
  return mkIdentFrom ref cand

open Lean Elab Command Term in
private def isViewPred (msgId : Ident) (pred : Term) : CommandElabM Bool := do
  let saved ← get
  try
    let ok ← liftTermElabM do
      let preCount := (← Core.getMessageLog).toList.length
      let expected ← elabType (← `(Html $msgId → Bool))
      let _ ← elabTermEnsuringType pred expected
      synthesizeSyntheticMVarsNoPostponing
      let newMsgs := (← Core.getMessageLog).toList.drop preCount
      return newMsgs.all (·.severity != .error)
    modify fun _ => saved
    return ok
  catch _ =>
    modify fun _ => saved
    return false

open Lean Elab Command in
private def elabInlineInvariants (spec : ComponentSpec) : CommandElabM Unit := do
  let propsId  := mkIdent (spec.t.getId ++ `Props)
  let stateId  := mkIdent (spec.t.getId ++ `State)
  let initId   := mkIdent (spec.t.getId ++ `init)
  let msgId    := mkIdent (spec.t.getId ++ `Msg)
  let updateId := mkIdent (spec.t.getId ++ `update)
  let viewId   := mkIdent (spec.t.getId ++ `view)
  let mountable := spec.ds.all (·.isSome)
  for invStx in spec.invariants do
    let invId ← match invStx[1].find? (·.isIdent) with
      | some idStx => pure (mkIdentFrom idStx (spec.t.getId ++ idStx.getId))
      | none       => freshCompInvIdent invStx spec.t.getId
    let clauses : Array Term := invStx[2].getSepArgs.map (⟨·⟩)
    let hasHoldsIn := invStx[3].getNumArgs > 0
    let assume? : Option Term :=
      if hasHoldsIn && invStx[3][2].getNumArgs == 2 then some ⟨invStx[3][2][1]⟩ else none
    let using? : Option (Array Term) :=
      if invStx[4].getNumArgs == 4 then some (invStx[4][2].getSepArgs.map (⟨·⟩)) else none
    let pf? : Option Term :=
      if invStx[5].getNumArgs == 2 then some ⟨invStx[5][1]⟩ else none
    let autoView ← if !hasHoldsIn && clauses.size == 1 && using?.isNone &&
        !spec.allNames.any (mentionsIdent clauses[0]!.raw) then
      isViewPred msgId clauses[0]!
    else pure false
    if hasHoldsIn || autoView then
      if clauses.size != 1 then
        throwErrorAt invStx[2] "a view styling invariant takes a single styling rule"
      let vPred := clauses[0]!
      if spec.hasProps then
        let predStr := (vPred.raw.reprint.getD "this rule").trimmed
        let helperViewId ← freshCompInvIdent invStx (spec.t.getId ++ `viewAt)
        match pf? with
        | some pf =>
            elabCommand (← `(theorem $invId:ident (p : $propsId) : ∀ m, ($vPred) ($viewId p m) = true := $pf))
        | none =>
            elabCommand (← `(
              set_option linter.unusedSimpArgs false in
              theorem $invId:ident (p : $propsId) : ∀ m, ($vPred) ($viewId p m) = true := by
                let $helperViewId := $viewId p
                change ∀ m, ($vPred) ($helperViewId m) = true
                qedDischargeStyling $helperViewId $invId $(Syntax.mkStrLit predStr)))
      else
        let cmd ← match assume?, pf? with
          | some a, some pf => `(invariant $invId : $vPred holds_in $viewId assuming $a := $pf)
          | none,   some pf => `(invariant $invId : $vPred holds_in $viewId := $pf)
          | some a, none    => `(invariant $invId : $vPred holds_in $viewId assuming $a)
          | none,   none    => `(invariant $invId : $vPred holds_in $viewId)
        elabCommand cmd
    else
      let conj ← mkConjBody clauses
      let bodyWithFields ← bindMentionedFields spec (mentionsIdent conj.raw) conj
      let pred ← `(fun (s : $stateId) => $bodyWithFields)
      if spec.hasProps then
        let usingL := using?.getD #[]
        match pf? with
        | some pf =>
            elabCommand (← `(theorem $invId:ident (p : $propsId) :
              ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($updateId p m msg)) := $pf))
        | none =>
            elabCommand (← `(theorem $invId:ident (p : $propsId) :
              ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($updateId p m msg)) := by
                qedDischargePreserved [$[$usingL],*] ($updateId p) $invId ($pred)))
      else if mountable then
        let cmd ← match using?, pf? with
          | some ls, some pf => `(invariant $invId : $pred from $initId preserved_by $updateId using [$[$ls],*] := $pf)
          | none,    some pf => `(invariant $invId : $pred from $initId preserved_by $updateId := $pf)
          | some ls, none    => `(invariant $invId : $pred from $initId preserved_by $updateId using [$[$ls],*])
          | none,    none    => `(invariant $invId : $pred from $initId preserved_by $updateId)
        elabCommand cmd
      else
        let cmd ← match using?, pf? with
          | some ls, some pf => `(invariant $invId : $pred preserved_by $updateId using [$[$ls],*] := $pf)
          | none,    some pf => `(invariant $invId : $pred preserved_by $updateId := $pf)
          | some ls, none    => `(invariant $invId : $pred preserved_by $updateId using [$[$ls],*])
          | none,    none    => `(invariant $invId : $pred preserved_by $updateId)
        elabCommand cmd

open Lean Elab Command in
@[command_elab componentCmd] def elabComponentCmd : CommandElab := fun stx => do
  let rawSpec ← parseComponentSpec stx
  let idLit := Syntax.mkStrLit (((← getCurrNamespace) ++ rawSpec.t.getId).toString)
  let (sites, body') ← collectSitesAndRewriteBody rawSpec
  let spec ← elabStructsAndResolveTypes rawSpec
  let (msgCmd, updateCmd) ← mkMsgAndUpdateCmds spec sites
  let coreCmds ← mkViewCmds spec body' msgCmd updateCmd
  let mountCmds ← mkCodecAndMountCmds spec idLit
  for c in coreCmds ++ mountCmds do
    elabCommand c
  elabInlineInvariants spec

end Qed
