import Qed.Component.Core
import Qed.Runtime
import Qed.Resource
import Qed.Jsx
import Qed.Schema
import Qed.Invariant.ForEach
import Lean

namespace Qed

/-! ## Persistent Component Registry (`componentRegistry`) -/

inductive CompMountKind | pureView | stateful deriving Inhabited, BEq, Repr

structure CompEventSig where
  name  : Lean.Name
  arity : Nat
deriving Inhabited, Repr

structure ComponentInfo where
  fullName    : Lean.Name
  kind        : CompMountKind
  hasProps    : Bool
  propNames   : Array Lean.Name
  slotNames   : Array Lean.Name
  bindNames   : Array Lean.Name
  hasChildren : Bool
  events      : Array CompEventSig
  hasOut      : Bool := false
  hasEffects  : Bool := false
  hasStart    : Bool := false
  mountable   : Bool := true
  hasLocalDef : Bool := false
  rootTag?    : Option String
deriving Inhabited

initialize componentRegistry :
    Lean.SimplePersistentEnvExtension ComponentInfo (Lean.NameMap ComponentInfo) ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays =>
      arrays.foldl (fun acc arr => arr.foldl (fun m info => m.insert info.fullName info) acc) {}
    addEntryFn := fun m info => m.insert info.fullName info
  }

open Lean in
def lookupComponent? (cName : Name) : CoreM (Option ComponentInfo) := do
  let env ← getEnv
  let reg := componentRegistry.getState env
  let ns ← getCurrNamespace
  if let some info := reg.find? (ns ++ cName) then return some info
  if let some info := reg.find? cName then return some info
  for (fullView, _) in ResolveName.resolveGlobalName env {} ns (← getOpenDecls) (cName ++ `view) do
    if let some info := reg.find? fullView.getPrefix then return some info
  return none

/-! ## Component & App Surface Syntax -/

declare_syntax_cat compStmt

section CompParsers
open Lean Parser

private def sendKw : Parser :=
  nonReservedSymbol "send" (includeIdent := true)

private def actionParam : Parser :=
  node `Qed.componentActionParam ("(" >> ident >> " : " >> termParser >> ")")

@[term_parser] def sendTerm := leading_parser:maxPrec sendKw >> termParser maxPrec

@[term_parser] def fieldSetterTerm := leading_parser:maxPrec
  atomic ("(" >> Parser.ident >> " := ") >> symbol "·" >> ")"

@[macro sendTerm] def expandSendTermOutsideComponent : Macro := fun stx =>
  Macro.throwErrorAt stx "`send …` is the component output; it only has meaning inside a `component … view =>` body"
@[macro fieldSetterTerm] def expandFieldSetterOutsideComponent : Macro := fun stx =>
  Macro.throwErrorAt stx "`(field := ·)` is a component field setter; it only has meaning inside a `component` body"

def compStmtSeq : Parser :=
  node `Qed.compStmtSeq
    (checkColGt >> categoryParser `compStmt 0 >>
     many (atomic (optional "," >> checkColGt >> categoryParser `compStmt 0)))

def compMatchAlt : Parser := leading_parser
  withPosition ("| " >> sepBy1 termParser "," >> " => " >> compStmtSeq)

@[compStmt_parser] def actionNoopStmt : Parser := leading_parser withPosition (atomic ("(" >> ")"))
@[compStmt_parser] def actionReturnStmt : Parser := leading_parser withPosition (atomic (symbol "return"))
@[compStmt_parser] def actionLetStmt : Parser := leading_parser
  withPosition ("let " >> ident >> optional (" : " >> termParser) >> " := " >> termParser)
@[compStmt_parser] def actionPerformStmt : Parser := leading_parser
  withPosition (atomic (nonReservedSymbol "perform" (includeIdent := true)) >> checkColGt >> termParser)
@[compStmt_parser] def actionSendStmt : Parser := leading_parser
  withPosition (atomic sendKw >> checkColGt >> termParser)
@[compStmt_parser] def actionIfLetStmt : Parser := leading_parser
  withPosition (atomic ("if " >> "let ") >> termParser >> " := " >> termParser >> " then " >>
                compStmtSeq >> optional (atomic (checkColGe >> "else ") >> compStmtSeq))
@[compStmt_parser] def actionIfStmt : Parser := leading_parser
  withPosition ("if " >> notFollowedBy (symbol "let") "let" >>
                optional (atomic (ident >> " : ")) >> termParser >> " then " >>
                compStmtSeq >> optional (atomic (checkColGe >> "else ") >> compStmtSeq))
@[compStmt_parser] def actionMatchStmt : Parser := leading_parser
  withPosition ("match " >> sepBy1 termParser "," >> " with" >> many1 (checkColGe >> compMatchAlt))
@[compStmt_parser] def actionAssignStmt : Parser := leading_parser
  withPosition (atomic (ident >> (symbol ":=" <|> symbol "+=" <|> symbol "-=")) >> termParser)

def compFieldClause : Parser := leading_parser
  withPosition (
    (atomic (identEq `state) <|> atomic (identEq `ephemeral) <|>
     atomic (identEq `prop) <|> atomic (identEq `bind) <|>
     atomic (identEq `slot) <|> atomic (identEq `collection)) >>
    ident >> optional (" : " >> termParser) >> optional (" := " >> termParser))
def compChildrenClause : Parser := leading_parser withPosition (atomic (identEq `children))
def compKeyClause      : Parser := leading_parser withPosition (atomic (identEq `key) >> ident)
def compEventClause    : Parser := leading_parser
  withPosition (atomic (identEq `event) >> ident >> many actionParam)
def compStartClause    : Parser := leading_parser
  withPosition (atomic (identEq `start) >> checkColGt >> termParser)
def compRouteClause    : Parser := leading_parser
  withPosition (atomic (identEq `route) >> optional ident >> " : " >> termParser >> " := " >> termParser >>
                many (checkColGt >> compMatchAlt))
def compPortOutClause  : Parser := leading_parser
  withPosition (atomic (identEq `port >> ident >> " : ") >> termParser)
def compPortInClause   : Parser := leading_parser
  withPosition (atomic (identEq `port >> ident >> "(") >> ident >> " : " >> termParser >> ")" >>
                optional (atomic (identEq `when) >> termParser) >> " => " >> compStmtSeq)
def compQueryClause    : Parser := leading_parser
  withPosition (
    atomic (identEq `query >> ident >> " : ") >> withPosition termParser >>
    checkColGt >>
    withPosition (identEq `key >> " := " >> withPosition termParser >>
                  checkColGe >> identEq `url >> " := " >> withPosition termParser))
def compActionClause   : Parser := leading_parser
  withPosition (atomic (identEq `action) >> ident >> many actionParam >>
                optional (atomic (identEq `when) >> termParser) >> " => " >> compStmtSeq)
def compInvName : Parser := leading_parser ident >> " : "
def compForEachInvClause : Parser := leading_parser
  withPosition (
    atomic ("invariant " >> optional (atomic compInvName) >> termParser >> " for_each " >> ident) >>
    optional (" holds_in " >> identEq `view) >>
    optional (" using " >> ident) >>
    optional (" := " >> termParser))
def compInvariantClause : Parser := leading_parser
  withPosition (
    "invariant " >> optional (atomic compInvName) >> sepBy1 termParser "," >>
    optional (" holds_in " >> identEq `view >> optional (" assuming " >> termParser maxPrec)) >>
    optional (" using " >> "[" >> sepBy termParser "," >> "]") >>
    optional (" := " >> termParser))
def compInvAny : Parser := compForEachInvClause <|> compInvariantClause

def compClause : Parser :=
  compFieldClause <|> compChildrenClause <|> compKeyClause <|>
  compEventClause <|> compStartClause <|> compRouteClause <|>
  compPortOutClause <|> compPortInClause <|> compQueryClause <|>
  compActionClause <|> compInvAny

@[command_parser] def componentCmd : Parser := leading_parser
  optional Command.docComment >>
  withPosition (
    "component " >>
    ident >> " where " >>
    many (checkColGt >> compClause) >>
    checkColGt >> identEq `view >> " => " >> checkColGt >> termParser >>
    many (checkColGt >> compInvAny))

end CompParsers

/-! ## Internal Elaboration Helpers -/

section CompElab
open Lean Elab Command

private structure FieldDecl where
  id   : Ident
  ty?  : Option Term := none
  def? : Option Term := none
  ty   : Term := ⟨.missing⟩

private structure EventDecl where
  id     : Ident
  params : Array (Ident × Term)

private structure SlotDecl where
  id   : Ident
  def? : Option Term

private structure RouteDecl where
  field : Ident
  ty    : Term
  init  : Term
  alts  : Array Syntax

private structure OutArm where
  ctor    : Name
  arity   : Nat
  handler : Term

private structure HoistedSub where
  fieldId   : Ident
  ctorName  : Name
  info      : ComponentInfo
  dataProps : Array (Ident × Term)
  onEmit?   : Option Term
  outArms   : Array OutArm

private structure SetSite where
  key     : String
  ctor    : Name
  params  : Array (Ident × Term) := #[]
  guard?  : Option Term := none
  assigns : Array (Name × Option Term) := #[]
  send?   : Option Term := none
  stmts?  : Option (Array Syntax) := none

private def isCdot (stx : Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Term.cdot || (stx.reprint.getD "").trimmed == "·"

private def atomStr : Syntax → String := Qed.Jsx.tokenVal
private def asTerm (s : Syntax) : Term := ⟨s⟩

private partial def mentionsIdent (stx : Syntax) (n : Name) : Bool :=
  match stx with
  | .ident _ _ v _ => n.isPrefixOf v.eraseMacroScopes
  | .node _ _ args => args.any (mentionsIdent · n)
  | _ => false

private def unpackSeq (seqStx : Syntax) : Array Syntax :=
  if seqStx.getKind == `Qed.compStmtSeq then
    #[seqStx[0]] ++ seqStx[1].getArgs.map fun m => m[m.getNumArgs - 1]!
  else #[seqStx]

private partial def hasPerformNode (stx : Syntax) : Bool :=
  stx.getKind == ``actionPerformStmt || stx.getArgs.any hasPerformNode

private partial def hasReturnStmt (stx : Syntax) : Bool :=
  stx.getKind == ``actionReturnStmt || stx.getArgs.any hasReturnStmt

private def staticRootTag? (body : Syntax) : Option String :=
  if body.getKind == ``Qed.Jsx.jsxTerm then
    let el := body[0]
    if el.getKind == ``Qed.Jsx.selfClosing || el.getKind == ``Qed.Jsx.withChildren then
      let tag := atomStr el[1]
      if !tag.isEmpty && !tag.front.isUpper then some tag else none
    else none
  else none

private def mkJsxAttrValNode (val : Term) : Syntax :=
  Syntax.node .none ``Qed.Jsx.attrValExpr
    #[Syntax.atom .none "{", Syntax.node .none ``Qed.Jsx.jsxTermExpr #[val.raw], Syntax.atom .none "}"]

private def mkJsxAttrExpr (name : String) (val : Term) : Syntax :=
  Syntax.node .none ``Qed.Jsx.attrNamed
    #[Syntax.node .none `Qed.Jsx.jsxName #[Syntax.atom .none name],
      Syntax.node .none nullKind #[Syntax.atom .none "=", mkJsxAttrValNode val]]

private def rebuildJsxEl (stx : Syntax) (attrs : Array Syntax) (kids? : Option Syntax) : Syntax :=
  let aNode := Syntax.node .none nullKind attrs
  match kids? with
  | none    => Syntax.node .none stx.getKind #[stx[0], stx[1], aNode, stx[3]]
  | some kn => Syntax.node .none stx.getKind #[stx[0], stx[1], aNode, stx[3], kn, stx[5], stx[6]]

private def mkOutMatchTerm (baseName : Name) (totalCtors : Nat) (arms : Array OutArm) (outVar : Ident) :
    MacroM Term := do
  let mut alts ← arms.mapM fun arm => do
    let oCtor := mkIdent (baseName ++ `Out ++ arm.ctor)
    let argIds := (List.range arm.arity).toArray.map fun i => mkIdent (Name.mkSimple s!"_a{i}")
    let patTerms : Array Term := argIds.map (⟨·.raw⟩)
    let callH ← argIds.foldlM (init := arm.handler) fun acc id => `($acc $id:ident)
    `(Lean.Parser.Term.matchAltExpr| | $oCtor $patTerms* => some ($callH))
  if arms.size < totalCtors then
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | _ => none))
  `(match $outVar:ident with $[$alts:matchAlt]*)

private def desugarAssign (fname : Name) (op : String) (rhs : Term) : CommandElabM Term := do
  let fIdent := mkIdent fname
  match op with
  | ":=" => pure rhs
  | "+=" => `($fIdent + ($rhs))
  | "-=" => `($fIdent - ($rhs))
  | _    => throwErrorAt rhs s!"unknown assignment operator '{op}'"

private def registerSite (sites : IO.Ref (Array SetSite))
    (assigns : Array (Name × Option Term)) (send? : Option Term) : CommandElabM Name := do
  let pp : Option Term → String := fun | some e => e.raw.reprint.getD (toString e.raw) | none => "·"
  let key := String.intercalate "|" (assigns.toList.map fun (f, e?) => s!"{f}={pp e?}") ++ s!"|{pp send?}"
  let cur ← sites.get
  if let some site := cur.find? (·.key == key) then return site.ctor
  let base := if assigns.isEmpty then "send"
    else "set_" ++ String.intercalate "_" (assigns.toList.map (toString ·.1))
  let mut name := Name.mkSimple base
  let mut i := 2
  while cur.any (·.ctor == name) do
    name := Name.mkSimple s!"{base}_{i}"
    i := i + 1
  sites.set (cur.push { key, assigns, ctor := name, send? })
  return name

private structure RewriteCtx where
  stateFields : Array Name
  bindFields  : Array Name
  actionNames : Array Name := #[]
  inPerform   : Bool := false
  isPureComp  : Bool
  msgPath     : Name
  hasOut      : Bool
  collections : Array (Ident × Ident)
  wrapMsg?    : Option Ident := none
  sites       : IO.Ref (Array SetSite)
  hoisted     : IO.Ref (Array HoistedSub)
  allowHoist  : Bool := false

private def wrapUnaryMsg (wrap? : Option Ident) (fn : Term) : CommandElabM Term := do
  match wrap? with | some w => `(fun _v => $w ($fn _v)) | none => pure fn

private def mkSetterHandler (ctx : RewriteCtx) (fname : Name) : CommandElabM Term := do
  if ctx.isPureComp && ctx.bindFields.contains fname then
    return ← `(p.$(mkIdent (Name.mkSimple s!"set_{fname}")):ident)
  if ctx.bindFields.contains fname then
    let outCtor := mkIdent (ctx.msgPath.getPrefix ++ `Out ++ Name.mkSimple s!"set_{fname}")
    let emitId  := mkIdent (ctx.msgPath ++ `_emit)
    return ← match ctx.wrapMsg? with
      | some w => `(fun v => $w ($emitId ($outCtor v)))
      | none   => `(fun v => $emitId ($outCtor v))
  let ctor ← registerSite ctx.sites #[(fname, none)] none
  wrapUnaryMsg ctx.wrapMsg? ⟨mkIdent (ctx.msgPath ++ ctor)⟩

private def mkSiteExpr (ctx : RewriteCtx) (assigns : Array (Name × Option Term))
    (send? : Option Term) : CommandElabM Term := do
  if ctx.isPureComp then
    if let #[(fname, val?)] := assigns then
      if ctx.bindFields.contains fname && send?.isNone then
        let sf := mkIdent (Name.mkSimple s!"set_{fname}")
        return ← match val? with | some v => `(p.$sf:ident $v) | none => `(p.$sf:ident)
  let mut stAssigns : Array (Name × Option Term) := #[]
  let mut bindSend? : Option Term := send?
  let mut bindDotField? : Option Name := none
  for (fn, val?) in assigns do
    if ctx.bindFields.contains fn then
      let outCtor := mkIdent (ctx.msgPath.getPrefix ++ `Out ++ Name.mkSimple s!"set_{fn}")
      match val? with
      | some v => bindSend? := some (← `($outCtor $v))
      | none   => bindDotField? := some fn
    else
      stAssigns := stAssigns.push (fn, val?)
  if let some bfn := bindDotField? then
    if stAssigns.isEmpty && bindSend?.isNone then return ← mkSetterHandler ctx bfn
  let ctor ← registerSite ctx.sites stAssigns bindSend?
  let cid : Term := ⟨mkIdent (ctx.msgPath ++ ctor)⟩
  if stAssigns.any (·.2.isNone) then wrapUnaryMsg ctx.wrapMsg? cid
  else match ctx.wrapMsg? with | some w => `($w $cid) | none => pure cid

private def checkMutableField (ctx : RewriteCtx) (ref : Syntax) (prefixMsg : String) (fname : Name) :
    CommandElabM Unit := do
  unless (ctx.stateFields ++ ctx.bindFields).contains fname do
    throwErrorAt ref "{prefixMsg}: not a `state` field of this component (fields: {ctx.stateFields.toList})"

private def pushHandlerAssign (ctx : RewriteCtx) (assigns : Array (Name × Option Term))
    (fId : Syntax) (expr? : Option Term) :
    CommandElabM (Array (Name × Option Term)) := do
  let fname := fId.getId.eraseMacroScopes
  checkMutableField ctx fId s!"`{fname}`" fname
  if assigns.any (·.1 == fname) then
    throwErrorAt fId s!"`{fname}`: this handler already updates `{fname}`"
  if expr?.isNone && assigns.any (·.2.isNone) then
    throwErrorAt fId s!"`{fname} := ·`: only one `·` placeholder per handler"
  return assigns.push (fname, expr?)

private def noEmitsErr (ref : Syntax) : CommandElabM Unit :=
  throwErrorAt ref "`send` bubbles an output, but this component declares no output event; add `event name` between the `state` fields and the `view`"

private def unitEvents : List String :=
  ["onClick", "onSubmit", "onBlur", "onFocus", "onDoubleClick", "onMouseDown", "onMouseUp"]
private def strEvents : List String := ["onInput", "onChange", "onKeydown", "onKeyup"]

private def wrapEventAttr (vNode : Syntax) (arity : Nat) (msgTy : Ident)
    (wrapMsg? : Option Ident) : CommandElabM Term := do
  let vT ← liftMacroM <| Qed.Jsx.expandAttrVal vNode (`(""))
  let mut evTy : Term := msgTy
  for _ in [0:arity] do evTy ← `(_ → $evTy)
  let mut typedV : Term ← `(($vT : $evTy))
  if let some w := wrapMsg? then
    let argIds := (List.range arity).toArray.map fun i => mkIdent (Name.mkSimple s!"_ea{i}")
    if argIds.isEmpty then
      typedV ← `($w $typedV)
    else
      let appV ← argIds.foldlM (init := typedV) fun acc arg => `($acc $arg)
      let wrapped ← `($w $appV)
      typedV ← argIds.foldrM (init := wrapped) fun arg acc => `(fun $arg => $acc)
  return typedV

private def injectAutoKey (bodyStx : Syntax) (compFullName : Name) (bindId : Ident) :
    CommandElabM Syntax := do
  if bodyStx.getKind == ``Qed.Jsx.jsxTermExpr && bodyStx[0].getKind == ``Qed.Jsx.jsxTerm then
    let el := bodyStx[0][0]
    let ek := el.getKind
    if ek == ``Qed.Jsx.selfClosing || ek == ``Qed.Jsx.withChildren then
      let attrs := el[2].getArgs
      let hasKey := attrs.any fun a => a.getKind == ``Qed.Jsx.attrNamed && atomStr a[0] == "key"
      if !hasKey then
        let keyVal ← `($(mkIdent (compFullName ++ `keyOf)) $bindId)
        let kids? := if ek == ``Qed.Jsx.withChildren then some el[4] else none
        let el' := rebuildJsxEl el (attrs.push (mkJsxAttrExpr "key" keyVal)) kids?
        let jsx' := Syntax.node .none ``Qed.Jsx.jsxTerm #[el']
        return Syntax.node .none ``Qed.Jsx.jsxTermExpr #[jsx']
  return bodyStx

private partial def rewriteIn (ctx : RewriteCtx) (inLambda : Bool) (stx : Syntax) : CommandElabM Syntax := do
  let parseOptSend (opt : Syntax) : CommandElabM (Option Term) := do
    if opt.getNumArgs != 3 then return none
    unless ctx.hasOut do noEmitsErr opt
    some <$> asTerm <$> rewriteIn ctx inLambda opt[2]
  let k := stx.getKind
  if k == ``Lean.Parser.Term.fun then
    return Syntax.node .none k (← stx.getArgs.mapM (rewriteIn ctx true))
  else if k == ``Qed.Jsx.jsxFor then
    let bindId : Ident := ⟨stx[1]⟩
    let collRaw := stx[3]
    let collRewritten ← rewriteIn ctx inLambda collRaw
    let mut bodyRewritten ← rewriteIn ctx true stx[5]
    if collRaw.isIdent then
      let colName := collRaw.getId.eraseMacroScopes
      if let some (_, childCompId) := ctx.collections.find? (·.1.getId == colName) then
        if let some cInfo ← liftCoreM (lookupComponent? childCompId.getId) then
          if (← liftCoreM getEnv).contains (cInfo.fullName ++ `keyOf) then
            bodyRewritten ← injectAutoKey bodyRewritten cInfo.fullName bindId
    return Syntax.node .none k #[stx[0], stx[1], stx[2], collRewritten, stx[4], bodyRewritten]
  else if k == ``actionPerformStmt then
    return Syntax.node .none k #[stx[0], ← rewriteIn { ctx with inPerform := true } inLambda stx[1]]
  else if ctx.inPerform && k == ``Lean.Parser.Term.dotIdent then
    let actId := stx[1].getId.eraseMacroScopes
    return if ctx.actionNames.contains actId then mkIdentFrom stx (ctx.msgPath ++ actId) else stx
  else if k == ``fieldSetterTerm then
    let fname := stx[1].getId.eraseMacroScopes
    checkMutableField ctx stx[1] s!"`({fname} := ·)`" fname
    return (← mkSetterHandler ctx fname).raw
  else if k == ``Lean.Parser.Term.namedArgument && stx.getNumArgs ≥ 4 && isCdot stx[3] then
    let fname := stx[1].getId.eraseMacroScopes
    if (ctx.stateFields ++ ctx.bindFields).contains fname then
      return (← mkSetterHandler ctx fname).raw
    return Syntax.node .none k (← stx.getArgs.mapM (rewriteIn ctx inLambda))
  else if k == ``sendTerm then
    unless ctx.hasOut do noEmitsErr stx
    return (← mkSiteExpr ctx #[] (some ⟨← rewriteIn ctx inLambda stx[1]⟩)).raw
  else if k == ``Qed.Jsx.attrValAssign then
    let mut assigns := #[]
    let more := stx[4].getArgs.map fun m =>
      let it := if m.getKind == `Qed.Jsx.jsxAssignItem then m else m[m.getNumArgs - 1]!
      (it[0], atomStr it[1], it[2])
    for (fId, op, rhsRaw) in #[(stx[1], atomStr stx[2], stx[3])] ++ more do
      let fname := fId.getId.eraseMacroScopes
      let expr? ← if op == ":=" && isCdot rhsRaw then pure none
        else some <$> desugarAssign fname op ⟨← rewriteIn ctx inLambda rhsRaw⟩
      assigns ← pushHandlerAssign ctx assigns fId expr?
    return mkJsxAttrValNode (← mkSiteExpr ctx assigns (← parseOptSend stx[5]))
  else if k == ``Qed.Jsx.attrNamed && (atomStr stx[0]).startsWith "bind" &&
      stx[1].getNumArgs == 2 && stx[1][1].getKind == ``Qed.Jsx.attrValExpr then
    let attrName := atomStr stx[0]
    let inner := stx[1][1]
    if (attrName == "bind" || attrName.startsWith "bind:") &&
        inner[1].getKind == ``Qed.Jsx.jsxTermExpr && inner[1][0].isIdent then
      let fId : Ident := ⟨inner[1][0]⟩
      let fname := fId.getId.eraseMacroScopes
      checkMutableField ctx fId s!"`{attrName}=\{{fname}}`" fname
      let pairT ← `(($fId, $(← mkSetterHandler ctx fname)))
      return Syntax.node .none stx.getKind #[stx[0], Syntax.node .none stx[1].getKind #[stx[1][0], mkJsxAttrValNode pairT]]
    return Syntax.node .none k (← stx.getArgs.mapM (rewriteIn ctx inLambda))
  else if k == ``Qed.Jsx.selfClosing || k == ``Qed.Jsx.withChildren then
    let tag := atomStr stx[1]
    let kids? ← if k == ``Qed.Jsx.withChildren then some <$> rewriteIn ctx inLambda stx[4] else pure none
    if tag.isEmpty || !tag.front.isUpper then
      let mut newAttrs : Array Syntax := #[]
      for a in stx[2].getArgs do
        let wasAssign := a.getKind == ``Qed.Jsx.attrNamed && a[1].getNumArgs == 2 &&
          a[1][1].getKind == ``Qed.Jsx.attrValAssign
        let a' ← rewriteIn ctx inLambda a
        if let some w := ctx.wrapMsg? then
          if !wasAssign && a'.getKind == ``Qed.Jsx.attrNamed && a'[1].getNumArgs == 2 &&
              a'[1][1].getKind == ``Qed.Jsx.attrValExpr then
            let aname := atomStr a'[0]
            let msgTy := mkIdent ctx.msgPath
            let vT ← liftMacroM <| Qed.Jsx.expandAttrVal a'[1] (`(""))
            let wrapped? : Option Term ←
              if unitEvents.contains aname then some <$> `($w ($vT : $msgTy))
              else if strEvents.contains aname then some <$> `(fun _s => $w (($vT : String → $msgTy) _s))
              else if aname == "onCheck" then some <$> `(fun _b => $w (($vT : Bool → $msgTy) _b))
              else pure none
            newAttrs := newAttrs.push (match wrapped? with | some wt => mkJsxAttrExpr aname wt | none => a')
          else newAttrs := newAttrs.push a'
        else newAttrs := newAttrs.push a'
      return rebuildJsxEl stx newAttrs kids?
    let rewrittenAttrs ← stx[2].getArgs.mapM (rewriteIn ctx inLambda)
    if tag == "Await" then
      return rebuildJsxEl stx rewrittenAttrs kids?
    let attrNames := rewrittenAttrs.filterMap fun a =>
      if a.getKind == ``Qed.Jsx.attrNamed then some (atomStr a[0]) else none
    let hasState := attrNames.contains "state"
    let cName := (tag.splitOn ".").foldl Name.str Name.anonymous
    if hasState && !attrNames.contains "onMsg" then
      let matching := ctx.collections.filter fun (_, colChild) =>
        colChild.getId == cName || colChild.getId.getString! == cName.getString!
      if matching.size == 1 then
        let colCtor := mkIdent (ctx.msgPath ++ matching[0]!.1.getId)
        let routeExpr : Term ← match ctx.wrapMsg? with
          | some w => `(fun k m => $w ($colCtor k m))
          | none   => pure ⟨colCtor⟩
        return rebuildJsxEl stx (rewrittenAttrs.push (mkJsxAttrExpr "onMsg" routeExpr)) kids?
    if ctx.allowHoist && !hasState then
      if let some cInfo ← liftCoreM (lookupComponent? cName) then
        let mustHoist := !cInfo.hasLocalDef || attrNames.any (·.startsWith "bind:") ||
          cInfo.hasChildren || !cInfo.slotNames.isEmpty
        if cInfo.kind == .stateful && cInfo.mountable &&
            (mustHoist || (!inLambda && !attrNames.contains "key" && !attrNames.contains "initial")) then
          if inLambda && mustHoist then
            throwErrorAt stx s!"<{tag}> uses effects, slots, children, or `bind:` and cannot be dynamically mounted inside a loop lambda; hoist its state into the parent or use `collection`"
          let curH ← ctx.hoisted.get
          let subName := Name.mkSimple s!"_sub_{curH.size}"
          let subFieldId := mkIdentFrom stx subName
          let mut dataProps : Array (Ident × Term) := #[]
          let mut onEmit?   : Option Term := none
          let mut outArms   : Array OutArm := #[]
          let mut keptAttrs : Array Syntax := #[]
          for a in rewrittenAttrs do
            if a.getKind == ``Qed.Jsx.attrNamed then
              let aname := atomStr a[0]
              let vT : Term ← if a[1].getNumArgs == 0 then `(Bool.true)
                else liftMacroM <| Qed.Jsx.expandAttrVal a[1] (`(""))
              if aname == "onEmit" then
                onEmit? := some vT
              else if let some ev := cInfo.events.find? (·.name.toString == aname) then
                outArms := outArms.push { ctor := ev.name, arity := ev.arity, handler := vT }
              else if aname.startsWith "bind:" then
                let bStr := (aname.drop 5).toString
                let valPart ← `(($vT).1)
                dataProps := dataProps.push (mkIdentFrom a[0] (Name.mkSimple bStr), valPart)
                outArms := outArms.push { ctor := Name.mkSimple s!"set_{bStr}", arity := 1, handler := ← `(($vT).2) }
                keptAttrs := keptAttrs.push (mkJsxAttrExpr bStr valPart)
              else
                let pId := mkIdentFrom a[0] (Name.mkSimple aname)
                if cInfo.propNames.contains pId.getId then dataProps := dataProps.push (pId, vT)
                keptAttrs := keptAttrs.push a
            else
              keptAttrs := keptAttrs.push a
          ctx.hoisted.set (curH.push {
            fieldId := subFieldId, ctorName := subName, info := cInfo, dataProps, onEmit?, outArms })
          let subRoute ← wrapUnaryMsg ctx.wrapMsg? ⟨mkIdent (ctx.msgPath ++ subName)⟩
          return rebuildJsxEl stx (keptAttrs.push (mkJsxAttrExpr "_hoist" (← `(($subRoute, $subFieldId))))) kids?
    let evList : Array (String × Nat) ← do
      if let some cInfo ← liftCoreM (lookupComponent? cName) then
        pure (cInfo.events.map fun sig => (sig.name.toString, sig.arity))
      else if tag.endsWith ".Form" && ctx.wrapMsg?.isSome then
        if (← liftCoreM (lookupSchemaForm? cName)).isSome then pure #[("onSubmit", 0)] else pure #[]
      else pure #[]
    if !evList.isEmpty then
      let msgTy := mkIdent ctx.msgPath
      let attrs' ← rewrittenAttrs.mapM fun a => do
        if a.getKind == ``Qed.Jsx.attrNamed && a[1].getNumArgs == 2 &&
            a[1][1].getKind == ``Qed.Jsx.attrValExpr then
          let aname := atomStr a[0]
          if let some (_, arity) := evList.find? (·.1 == aname) then
            return mkJsxAttrExpr aname (← wrapEventAttr a[1] arity msgTy ctx.wrapMsg?)
        return a
      return rebuildJsxEl stx attrs' kids?
    return rebuildJsxEl stx rewrittenAttrs kids?
  else
    match stx with
    | .node info kind args => return .node info kind (← args.mapM (rewriteIn ctx inLambda))
    | _ => return stx

/-! ## Component Specification Parsing -/

private structure PortOutDecl where
  id : Ident
  ty : Term

private structure PortInDecl where
  id     : Ident
  argId  : Ident
  argTy  : Term
  guard? : Option Term
  body   : Syntax

private structure QueryDecl where
  id      : Ident
  ty      : Term
  keyExpr : Term
  urlExpr : Term

private def QueryDecl.ctorName (q : QueryDecl) : Name :=
  Name.mkSimple s!"_query_{q.id.getId}"

private structure ComponentSpec where
  doc?            : Option (TSyntax ``Lean.Parser.Command.docComment)
  t               : Ident
  collections     : Array (Ident × Ident)
  states          : Array FieldDecl
  ephemeralFields : Array Ident
  props           : Array FieldDecl
  binds           : Array FieldDecl
  slots           : Array SlotDecl
  hasChildren     : Bool
  events          : Array EventDecl
  hasProps        : Bool
  keyF?           : Option Ident
  outTy?          : Option Term
  route?          : Option RouteDecl
  starts          : Array Term
  portOuts        : Array PortOutDecl := #[]
  portIns         : Array PortInDecl := #[]
  queries         : Array QueryDecl := #[]
  actions         : Array Syntax
  invariants      : Array Syntax
  body            : Term
  hoisted         : Array HoistedSub := #[]
  hasEffects      : Bool := false

private def ComponentSpec.fieldNames (s : ComponentSpec) : Array Name := s.states.map (·.id.getId)
private def ComponentSpec.propNames  (s : ComponentSpec) : Array Name := s.props.map (·.id.getId)
private def ComponentSpec.bindNames  (s : ComponentSpec) : Array Name := s.binds.map (·.id.getId)
private def ComponentSpec.allNames   (s : ComponentSpec) : Array Name :=
  (s.fieldNames ++ s.propNames ++ s.bindNames).toList.eraseDups.toArray
private def ComponentSpec.mountable  (s : ComponentSpec) : Bool := s.states.all (·.def?.isSome)
private def ComponentSpec.hasSlotsOrKids (s : ComponentSpec) : Bool := !s.slots.isEmpty || s.hasChildren

private def parseComponentSpec (stx : Syntax) : CommandElabM ComponentSpec := do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if stx[0].getNumArgs == 1 then some ⟨stx[0][0]⟩ else none
  let t : Ident := ⟨stx[2]⟩
  let mut states          : Array FieldDecl := #[]
  let mut ephemeralFields : Array Ident := #[]
  let mut props           : Array FieldDecl := #[]
  let mut binds           : Array FieldDecl := #[]
  let mut slots           : Array SlotDecl := #[]
  let mut hasChildren     : Bool := false
  let mut events          : Array EventDecl := #[]
  let mut collections     : Array (Ident × Ident) := #[]
  let mut keyF?           : Option Ident := none
  let mut route?          : Option RouteDecl := none
  let mut starts          : Array Term := #[]
  let mut portOuts        : Array PortOutDecl := #[]
  let mut portIns         : Array PortInDecl := #[]
  let mut queries         : Array QueryDecl := #[]
  let mut actions         : Array Syntax := #[]
  let mut invariants      : Array Syntax := #[]
  let requireTyOrDef (role : Name) (fId : Ident) (ty? d? : Option Term) : CommandElabM Unit := do
    if ty?.isNone && d?.isNone then
      throwErrorAt fId s!"`{role} {fId.getId}` needs a type (`: Type`), a default (`:= value`), or both"
  for cl in stx[4].getArgs do
    let k := cl.getKind
    if k == ``compFieldClause then
      let role := cl[0].getId
      let fId : Ident := ⟨cl[1]⟩
      let ty? : Option Term := if cl[2].getNumArgs == 2 then some ⟨cl[2][1]⟩ else none
      let d?  : Option Term := if cl[3].getNumArgs == 2 then some ⟨cl[3][1]⟩ else none
      match role with
      | `slot => slots := slots.push { id := fId, def? := d? }
      | `prop => requireTyOrDef role fId ty? d?; props := props.push { id := fId, ty?, def? := d? }
      | `bind => requireTyOrDef role fId ty? d?; binds := binds.push { id := fId, ty?, def? := d? }
      | `collection =>
          let some colTy := ty? | throwErrorAt fId s!"`collection {fId.getId}` requires `: ChildComponent`"
          unless colTy.raw.isIdent do throwErrorAt colTy "`collection` target must be a child component name"
          let childId : Ident := ⟨colTy.raw⟩
          collections := collections.push (fId, childId)
          states := states.push {
            id := fId, ty? := some (← `(Array $(mkIdent (childId.getId ++ `State)))),
            def? := some (← d?.getDM `(#[])) }
      | _ =>
          requireTyOrDef role fId ty? d?
          states := states.push { id := fId, ty?, def? := d? }
          if role == `ephemeral then ephemeralFields := ephemeralFields.push fId
    else if k == ``compChildrenClause then
      hasChildren := true
    else if k == ``compKeyClause then
      if keyF?.isSome then throwErrorAt cl "duplicate `key` clause in component"
      keyF? := some ⟨cl[1]⟩
    else if k == ``compEventClause then
      events := events.push { id := ⟨cl[1]⟩, params := cl[2].getArgs.map fun p => (⟨p[1]⟩, ⟨p[3]⟩) }
    else if k == ``compStartClause then
      starts := starts.push ⟨cl[1]⟩
    else if k == ``compRouteClause then
      if route?.isSome then throwErrorAt cl "duplicate `route` clause in component"
      let rField : Ident := if cl[1].getNumArgs == 1 then ⟨cl[1][0]⟩ else mkIdentFrom cl `route
      let rTy : Term := ⟨cl[3]⟩; let rInit : Term := ⟨cl[5]⟩
      route? := some { field := rField, ty := rTy, init := rInit, alts := cl[6].getArgs }
      states := states.push { id := rField, ty? := some rTy, def? := some rInit }
    else if k == ``compPortOutClause || k == ``compPortInClause then
      let pId : Ident := ⟨cl[1]⟩
      if pId.getId.toString.startsWith "__" then
        throwErrorAt pId s!"port name '{pId.getId}' is reserved (names starting with `__`)"
      if k == ``compPortOutClause then
        portOuts := portOuts.push { id := pId, ty := ⟨cl[3]⟩ }
      else
        let g? := if cl[7].getNumArgs == 2 then some ⟨cl[7][1]⟩ else none
        portIns := portIns.push { id := pId, argId := ⟨cl[3]⟩, argTy := ⟨cl[5]⟩, guard? := g?, body := cl[9] }
    else if k == ``compQueryClause then
      let qId : Ident := ⟨cl[1]⟩; let qTy : Term := ⟨cl[3]⟩
      states := states.push { id := qId, ty? := some (← `(Cached $qTy)), def? := some (← `({})) }
      queries := queries.push { id := qId, ty := qTy, keyExpr := ⟨cl[6]⟩, urlExpr := ⟨cl[9]⟩ }
    else if k == ``compActionClause then
      actions := actions.push cl
    else if k == ``compInvariantClause || k == ``compForEachInvClause then
      invariants := invariants.push cl
  invariants := invariants ++ stx[8].getArgs
  let fieldNames := states.map (·.id.getId)
  let allDeclNames := fieldNames ++ props.map (·.id.getId) ++ binds.map (·.id.getId) ++
    slots.map (·.id.getId) ++ events.map (·.id.getId) ++ portOuts.map (·.id.getId)
  if allDeclNames.toList.eraseDups.length != allDeclNames.size then
    throwErrorAt t "component fields and events must have distinct names"
  let outTy? : Option Term :=
    if !events.isEmpty || !binds.isEmpty then some (mkIdent (t.getId ++ `Out)) else none
  if let some kf := keyF? then
    unless fieldNames.contains kf.getId.eraseMacroScopes do
      throwErrorAt kf "`key {kf.getId}`: not a `state` field of this component (fields: {fieldNames.toList})"
    if outTy?.isSome then
      throwErrorAt kf "`key` marks the row identity for parent-owned use, and a parent-owned child's `event` output would have no receiver; drop one of the two"
  return { doc?, t, collections, states, ephemeralFields, props, binds, slots, hasChildren, events,
           hasProps := !props.isEmpty || !binds.isEmpty, keyF?, outTy?,
           route?, starts, portOuts, portIns, queries, actions, invariants, body := ⟨stx[7]⟩ }

/-! ## Shared Structure, Binder & Registry Helpers -/

private def mkStructBinder (f : FieldDecl) : CommandElabM (TSyntax ``Lean.Parser.Command.structExplicitBinder) :=
  match f.ty?, f.def? with
  | some ty, some d => `(Lean.Parser.Command.structExplicitBinder| ($(f.id) : $ty := $d))
  | some ty, none   => `(Lean.Parser.Command.structExplicitBinder| ($(f.id) : $ty))
  | none,    some d => `(Lean.Parser.Command.structExplicitBinder| ($(f.id) := $d))
  | none,    none   => throwErrorAt f.id s!"field `{f.id.getId}` needs a type or default value"

private def resolveBindTy (bd : FieldDecl) : CommandElabM Term := do
  match bd.ty?, bd.def? with
  | some ty, _ => pure ty
  | none, some d => `(type_of% $d)
  | none, none => throwErrorAt bd.id s!"`bind {bd.id.getId}` needs a type or default"

private def freshCompInvIdent (ref : Syntax) (compId : Name) : CommandElabM Ident := do
  let env ← getEnv; let ns ← getCurrNamespace
  let base := compId ++ `inv
  if !env.contains (ns ++ base) then return mkIdentFrom ref base
  let mut idx := 2
  while env.contains (ns ++ compId ++ Name.mkSimple s!"inv_{idx}") do idx := idx + 1
  return mkIdentFrom ref (compId ++ Name.mkSimple s!"inv_{idx}")

private def resolveInvIdent (invStx : Syntax) (compId : Name) : CommandElabM Ident :=
  match invStx[1].find? (·.isIdent) with
  | some idStx => pure (mkIdentFrom idStx (compId ++ idStx.getId))
  | none       => freshCompInvIdent invStx compId

private def mkBaseCompInfo (spec : ComponentSpec) (kind : CompMountKind) (hasProps : Bool) :
    CommandElabM ComponentInfo := do
  return {
    fullName    := (← getCurrNamespace) ++ spec.t.getId
    kind, hasProps
    propNames   := spec.propNames
    slotNames   := spec.slots.map (·.id.getId)
    bindNames   := spec.bindNames
    hasChildren := spec.hasChildren
    events      := spec.events.map fun e => { name := e.id.getId, arity := e.params.size }
    rootTag?    := staticRootTag? spec.body.raw
  }

/-! ## Pure View Component Elaboration (`CompMountKind.pureView`) -/

private def elabPureComponent (spec : ComponentSpec) (body' : Term) : CommandElabM Unit := do
  let doc?    := spec.doc?
  let tId     := spec.t.getId
  let propsId := mkIdent (tId ++ `Props)
  let viewId  := mkIdent (tId ++ `view)
  let msgV    := mkIdent `msg
  let mut pBinders ← spec.props.mapM mkStructBinder
  let mut propReadNames := spec.propNames
  for sl in spec.slots do
    propReadNames := propReadNames.push sl.id.getId
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder|
      ($(sl.id) : Html $msgV := $(← sl.def?.getDM `(Qed.Html.empty)))))
  for bd in spec.binds do
    propReadNames := propReadNames.push bd.id.getId
    let bTy ← resolveBindTy bd
    let setF := mkIdentFrom bd.id (Name.mkSimple s!"set_{bd.id.getId}")
    pBinders := pBinders.push (← mkStructBinder { bd with ty? := some bTy })
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder| ($setF : $bTy → $msgV)))
  for ev in spec.events do
    propReadNames := propReadNames.push ev.id.getId
    let evTy ← ev.params.foldrM (init := (⟨msgV.raw⟩ : Term)) fun (_, pTy) acc => `($pTy → $acc)
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder| ($(ev.id) : $evTy)))
  if spec.hasChildren then
    propReadNames := propReadNames.push `children
    pBinders := pBinders.push (← `(Lean.Parser.Command.structExplicitBinder| ($(mkIdent `children) : List (Html $msgV) := [])))
  elabCommand (← `(command| structure $propsId ($msgV : Type) where $[$pBinders:structExplicitBinder]*))
  let mut viewBody := body'
  for g in propReadNames.reverse do
    if mentionsIdent viewBody.raw g then
      let gId := mkIdent g
      viewBody ← `(let $gId:ident := (p.$gId:ident); $viewBody)
  let needsProps := !pBinders.isEmpty
  let viewBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ←
    if needsProps then pure #[← `(bracketedBinder| {$msgV : Type}), ← `(bracketedBinder| (p : $propsId $msgV))]
    else pure #[← `(bracketedBinder| {$msgV : Type})]
  elabCommand (← `(command| $[$doc?:docComment]? @[inline] def $viewId $[$viewBinders:bracketedBinder]* : Html $msgV := $viewBody))
  for invStx in spec.invariants do
    if invStx.getKind == ``compForEachInvClause then
      throwErrorAt invStx "a pure component has no local state; `for_each` applies to stateful components"
    let invId ← resolveInvIdent invStx tId
    let clauses : Array Term := invStx[2].getSepArgs.map (⟨·⟩)
    if clauses.size != 1 then
      throwErrorAt invStx "a pure component has no local state; only single-clause view styling invariants apply"
    let vPred := clauses[0]!
    let predStr := (vPred.raw.reprint.getD "this rule").trimmed
    let vCall ← if needsProps then `($viewId p) else `(($viewId : Html $msgV))
    let pf? : Option Term := if invStx[5].getNumArgs == 2 then some ⟨invStx[5][1]⟩ else none
    let rhs ← pf?.getDM `(by
      let _qed_hv := fun (_ : Unit) => $vCall
      suffices ∀ u, ($vPred) (_qed_hv u) = true from this ()
      qedDischargeStyling _qed_hv $invId $(Syntax.mkStrLit predStr))
    elabCommand (← `(command| set_option linter.unusedSimpArgs false in
      theorem $invId:ident $[$viewBinders:bracketedBinder]* : ($vPred) $vCall = true := $rhs))
  let info ← mkBaseCompInfo spec .pureView needsProps
  modifyEnv fun env => componentRegistry.addEntry env info

/-! ## Stateful & Effectful Component Elaboration (`CompMountKind.stateful`) -/

private def collectSitesAndRewriteStateful (spec : ComponentSpec) :
    CommandElabM (Array SetSite × Option RouteDecl × Array QueryDecl × Array Term × Term × Array HoistedSub) := do
  let sitesRef   ← IO.mkRef (#[] : Array SetSite)
  let hoistedRef ← IO.mkRef (#[] : Array HoistedSub)
  let baseCtx : RewriteCtx := {
    stateFields := spec.fieldNames, bindFields := spec.bindNames,
    actionNames := spec.actions.map (·[1].getId) ++ spec.portIns.map (·.id.getId),
    isPureComp := false, msgPath := spec.t.getId ++ `Msg, hasOut := spec.outTy?.isSome,
    collections := spec.collections, sites := sitesRef, hoisted := hoistedRef
  }
  for a in spec.actions do
    let name := a[1].getId
    if (← sitesRef.get).any (·.ctor == name) || spec.collections.any (·.1.getId == name) then
      throwErrorAt a[1] "duplicate action name `{name}`"
    let params : Array (Ident × Term) := a[2].getArgs.map fun p => (⟨p[1]⟩, ⟨p[3]⟩)
    let pNames := params.map (·.1.getId)
    if pNames.toList.eraseDups.length != pNames.size || pNames.any spec.allNames.contains then
      throwErrorAt a "action parameters must be distinct and must not shadow fields"
    let guard? ← if a[3].getNumArgs == 2 then some <$> asTerm <$> rewriteIn baseCtx false a[3][1] else pure none
    let stmts := unpackSeq (← rewriteIn baseCtx false a[5])
    let mut dummyAssigns : Array (Name × Option Term) := #[]
    for s in stmts do
      if s.getKind == ``actionAssignStmt && atomStr s[1] == ":=" && isCdot s[2] then
        dummyAssigns ← pushHandlerAssign baseCtx dummyAssigns s[0] none
    if !params.isEmpty && !dummyAssigns.isEmpty then
      throwErrorAt a "use an explicit set value in an action with parameters"
    let cur ← sitesRef.get
    sitesRef.set (cur.push {
      key := s!"action:{name}", ctor := name, params, guard?, assigns := dummyAssigns, stmts? := some stmts })
  for p in spec.portIns do
    let name := p.id.getId
    if (← sitesRef.get).any (·.ctor == name) || spec.collections.any (·.1.getId == name) then
      throwErrorAt p.id "duplicate port/action name `{name}`"
    if spec.allNames.contains p.argId.getId then
      throwErrorAt p.argId "port parameter must not shadow fields"
    let guard? ← p.guard?.mapM fun g => asTerm <$> rewriteIn baseCtx false g.raw
    let stmts := unpackSeq (← rewriteIn baseCtx false p.body)
    let cur ← sitesRef.get
    sitesRef.set (cur.push {
      key := s!"port:{name}", ctor := name, params := #[(p.argId, p.argTy)], guard?, stmts? := some stmts })
  let route'? ← spec.route?.mapM fun rd => do
    let alts' ← rd.alts.mapM fun alt => do
      pure (Syntax.node .none alt.getKind #[alt[0], alt[1], alt[2], ← rewriteIn baseCtx false alt[3]])
    pure { rd with alts := alts' }
  let queries' ← spec.queries.mapM fun q => do
    let k' ← asTerm <$> rewriteIn baseCtx false q.keyExpr.raw
    let u' ← asTerm <$> rewriteIn baseCtx false q.urlExpr.raw
    pure { q with keyExpr := k', urlExpr := u' }
  let starts' ← spec.starts.mapM fun st => asTerm <$> rewriteIn { baseCtx with inPerform := true } false st.raw
  let viewCtx := { baseCtx with
    allowHoist := true
    wrapMsg?   := if spec.hasSlotsOrKids then some (mkIdent `_wrap) else none }
  let body' : Term := ⟨← rewriteIn viewCtx false spec.body⟩
  return (← sitesRef.get, route'?, queries', starts', body', ← hoistedRef.get)

private def bindMentionedFields (spec : ComponentSpec) (shouldBind : Name → Bool)
    (body : Term) : CommandElabM Term := do
  let mut out := body
  for po in spec.portOuts.reverse do
    if shouldBind po.id.getId then
      let poId := mkIdent po.id.getId
      out ← `(let $poId:ident := $(mkIdent (spec.t.getId ++ po.id.getId)); $out)
  for ev in spec.events.reverse do
    if shouldBind ev.id.getId then
      let evId := mkIdent ev.id.getId
      out ← `(let $evId:ident := $(mkIdent (spec.t.getId ++ `Out ++ ev.id.getId)); $out)
  for g in spec.allNames.reverse do
    if shouldBind g then
      let gId := mkIdent g
      out ← if spec.fieldNames.contains g then `(let $gId:ident := (s.$gId:ident); $out)
            else `(let $gId:ident := (p.$gId:ident); $out)
  return out

private def mkPropsBinders (spec : ComponentSpec) :
    CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  if spec.hasProps then return #[← `(bracketedBinder| (p : $(mkIdent (spec.t.getId ++ `Props))))]
  else return #[]

private def resolveStructFieldTypes (compName structKind : Name)
    (decls : Array FieldDecl) : CommandElabM (Array FieldDecl) := do
  let ns ← getCurrNamespace; let env ← getEnv
  decls.mapM fun d => do
    let resolved ← match d.ty? with
      | some ty => pure ty
      | none =>
          let some info := env.find? (ns ++ compName ++ structKind ++ d.id.getId)
            | throwErrorAt d.id s!"could not infer type of `{d.id.getId}`; add an explicit `: Type`"
          liftTermElabM <| Meta.forallTelescope info.type fun _ cod => PrettyPrinter.delab cod
    return { d with ty := resolved }

private def elabStructsAndResolveTypes (spec : ComponentSpec) (hoisted : Array HoistedSub) :
    CommandElabM ComponentSpec := do
  if spec.outTy?.isSome then
    let outId := mkIdent (spec.t.getId ++ `Out)
    let evCtors ← spec.events.mapM fun ev => do
      let pIds := ev.params.map (·.1); let pTys := ev.params.map (·.2)
      `(Lean.Parser.Command.ctor| | $(mkIdent ev.id.getId):ident $[($pIds:ident : $pTys)]*)
    let bdCtors ← spec.binds.mapM fun bd => do
      let setC := mkIdent (Name.mkSimple s!"set_{bd.id.getId}")
      `(Lean.Parser.Command.ctor| | $setC:ident (v : $(← resolveBindTy bd)))
    elabCommand (← `(command| inductive $outId where $[$(evCtors ++ bdCtors):ctor]*))
  let allProps := spec.props ++ spec.binds
  let allStates := spec.states ++ hoisted.map fun h => {
    id := h.fieldId, ty? := some (mkIdent (h.info.fullName ++ `State)),
    def? := some (mkIdent (h.info.fullName ++ `init)) }
  let propsId := mkIdent (spec.t.getId ++ `Props)
  let stateId := mkIdent (spec.t.getId ++ `State)
  elabCommand (← `(command| structure $propsId where $[$(← allProps.mapM mkStructBinder):structExplicitBinder]*))
  elabCommand (← `(command| structure $stateId where $[$(← allStates.mapM mkStructBinder):structExplicitBinder]*))
  let resolvedProps  ← resolveStructFieldTypes spec.t.getId `Props allProps
  let resolvedStates ← resolveStructFieldTypes spec.t.getId `State allStates
  let resolvedBinds  := spec.binds.map fun bd =>
    { bd with ty := (resolvedProps.find? (·.id.getId == bd.id.getId)).map (·.ty) |>.getD bd.ty }
  return { spec with states := resolvedStates, props := resolvedProps, binds := resolvedBinds, hoisted }

private def mkCmdBatch (cmds : Array Term) : CommandElabM Term := do
  if cmds.isEmpty then `(Qed.Cmd.none)
  else if cmds.size == 1 then return cmds[0]!
  else `(Qed.Cmd.batch [$[$cmds],*])

private def mkUpdateRet (spec : ComponentSpec) (sTerm : Term) (out? : Option Term)
    (cmds : Array Term) : CommandElabM Term := do
  let oVal ← match out? with | some o => `(some $o) | none => `(none)
  match spec.outTy?.isSome, spec.hasEffects with
  | false, false => return sTerm
  | true,  false => `(($sTerm, $oVal))
  | false, true  => `(($sTerm, $(← mkCmdBatch cmds)))
  | true,  true  => `(($sTerm, $oVal, $(← mkCmdBatch cmds)))

private def unpackRetTuple (hasOut hasEffects : Bool) (v : Ident) :
    CommandElabM (Term × Option Term × Option Term) := do
  let sE ← if !hasOut && !hasEffects then `($v:ident) else `(($v:ident).1)
  let oE? ← if !hasOut then pure none
    else if hasEffects then some <$> `(($v:ident).2.1) else some <$> `(($v:ident).2)
  let cE? ← if !hasEffects then pure none
    else if hasOut then some <$> `(($v:ident).2.2) else some <$> `(($v:ident).2)
  return (sE, oE?, cE?)

private def mkHoistedPropsTerm (h : HoistedSub) : CommandElabM Term := do
  let fIds := h.dataProps.map (·.1); let fVals := h.dataProps.map (·.2)
  `(({ $[$fIds:ident := $fVals],* } : $(mkIdent (h.info.fullName ++ `Props))))

private def flushAssigns (sBase : Term) (assigns : Array (Name × Option Term)) : CommandElabM Term := do
  if assigns.isEmpty then return sBase
  let fIds := assigns.map (mkIdent ·.1)
  let vals ← assigns.mapM (·.2.getDM `(v))
  `({ $sBase with $[$fIds:ident := $vals],* })

private partial def compileStmts (spec : ComponentSpec) (sBase : Term)
    (assigns : Array (Name × Option Term)) (out? : Option Term) (cmds : Array Term)
    (stmts : List Syntax) : CommandElabM Term := do
  match stmts with
  | [] => mkUpdateRet spec (← flushAssigns sBase assigns) out? cmds
  | s :: rest =>
      let sk := s.getKind
      if sk == ``actionNoopStmt then
        compileStmts spec sBase assigns out? cmds rest
      else if sk == ``actionReturnStmt then
        mkUpdateRet spec (← flushAssigns sBase assigns) out? cmds
      else if sk == ``actionLetStmt then
        let lId : Ident := ⟨s[1]⟩; let lVal : Term := ⟨s[4]⟩
        let cont ← compileStmts spec sBase assigns out? cmds rest
        if s[2].getNumArgs == 2 then
          let lTy : Term := ⟨s[2][1]⟩
          `(let $lId:ident : $lTy := $lVal; $cont)
        else `(let $lId:ident := $lVal; $cont)
      else if sk == ``actionAssignStmt then
        let fId : Ident := ⟨s[0]⟩
        let fname := fId.getId.eraseMacroScopes
        let expr? : Option Term ←
          if atomStr s[1] == ":=" && isCdot s[2] then pure none
          else some <$> desugarAssign fname (atomStr s[1]) ⟨s[2]⟩
        if spec.bindNames.contains fname then
          if out?.isSome then throwErrorAt s "duplicate output in action"
          let outCtor := mkIdent (spec.t.getId ++ `Out ++ Name.mkSimple s!"set_{fname}")
          let oTerm ← `($outCtor $(← expr?.getDM `(v)))
          return ← compileStmts spec sBase assigns (some oTerm) cmds rest
        unless spec.fieldNames.contains fname do
          throwErrorAt fId "`{fname}`: not a `state` field of this component (fields: {spec.fieldNames.toList})"
        if assigns.any (·.1 == fname) then
          throwErrorAt fId "`{fname}`: this handler already updates `{fname}`"
        compileStmts spec sBase (assigns.push (fname, expr?)) out? cmds rest
      else if sk == ``actionSendStmt then
        unless spec.outTy?.isSome do noEmitsErr s
        if out?.isSome then throwErrorAt s "duplicate `send` in action; an action emits at most one output"
        compileStmts spec sBase assigns (some ⟨s[1]⟩) cmds rest
      else if sk == ``actionPerformStmt then
        compileStmts spec sBase assigns out? (cmds.push ⟨s[1]⟩) rest
      else if sk == ``actionIfStmt || sk == ``actionIfLetStmt || sk == ``actionMatchStmt then
        let passTail := !rest.isEmpty && hasReturnStmt s
        let sFlushed ← flushAssigns sBase assigns
        let preId := mkIdent `_qedPre
        let (brBase, wrapPre) := if passTail && !assigns.isEmpty then ((preId : Term), true) else (sFlushed, false)
        let tailStmts := if passTail then rest else []
        let compileBranch (seq : Array Syntax) := compileStmts spec brBase #[] out? cmds (seq.toList ++ tailStmts)
        let compileOptElse (opt : Syntax) :=
          compileBranch (if opt.getNumArgs == 2 then unpackSeq opt[1] else #[])
        let branchTerm ←
          if sk == ``actionIfStmt then
            let cond : Term := ⟨s[2]⟩
            let tT ← compileBranch (unpackSeq s[4]); let eT ← compileOptElse s[5]
            if s[1].getNumArgs > 0 then
              let hId : Ident := ⟨s[1][0]⟩
              `(if $hId:ident : $cond then $tT else $eT)
            else `(if $cond then $tT else $eT)
          else if sk == ``actionIfLetStmt then
            let pat : Term := ⟨s[2]⟩; let scrut : Term := ⟨s[4]⟩
            `(if let $pat := $scrut then $(← compileBranch (unpackSeq s[6])) else $(← compileOptElse s[7]))
          else
            let scruts : Array Term := s[1].getSepArgs.map (⟨·⟩)
            let alts ← s[3].getArgs.mapM fun alt => do
              let pats : Array Term := alt[1].getSepArgs.map (⟨·⟩)
              `(Lean.Parser.Term.matchAltExpr| | $[$pats:term],* => $(← compileBranch (unpackSeq alt[3])))
            `(match $[$scruts:term],* with $[$alts:matchAlt]*)
        if passTail then
          let mut br := branchTerm
          if wrapPre then
            for (fn, _) in assigns.reverse do
              if tailStmts.any (mentionsIdent · fn) then
                let fId := mkIdent fn
                br ← `(let $fId:ident := ($preId).$fId:ident; $br)
            br ← `(let $preId:ident := $sFlushed; $br)
          return br
        if rest.isEmpty then return branchTerm
        let brId := mkIdent `_qedBr
        let (sNext, oNext, cOpt) ← unpackRetTuple spec.outTy?.isSome spec.hasEffects brId
        let cNext := match cOpt with | some c => #[c] | none => #[]
        let tail ← match oNext with
          | none => compileStmts spec sNext #[] none cNext rest
          | some oExpr =>
              let oVal := mkIdent `_qedOut
              `(match $oExpr:term with
                | none => $(← compileStmts spec sNext #[] none cNext rest)
                | some $oVal:ident => $(← compileStmts spec sNext #[] (some ⟨oVal.raw⟩) cNext rest))
        let mut rebound := tail
        for fn in spec.fieldNames.reverse do
          if rest.any (mentionsIdent · fn) then
            let fId := mkIdent fn
            rebound ← `(let $fId:ident := ($sNext).$fId:ident; $rebound)
        `(let $brId:ident := $branchTerm; $rebound)
      else
        throwErrorAt s "unsupported statement in component action"

private def mkMsgAndUpdateCmds (spec : ComponentSpec) (sites : Array SetSite) :
    CommandElabM (Array (TSyntax `command)) := do
  let tId      := spec.t.getId
  let stateId  := mkIdent (tId ++ `State)
  let msgId    := mkIdent (tId ++ `Msg)
  let updateId := mkIdent (tId ++ `update)
  let mut ctors ← sites.mapM fun site => do
    let cId := mkIdent site.ctor
    if !site.params.isEmpty then
      let ids := site.params.map (·.1); let ts := site.params.map (·.2)
      `(Lean.Parser.Command.ctor| | $cId:ident $[($ids:ident : $ts)]*)
    else match site.assigns.find? (·.2.isNone) with
    | some (f, _) =>
        let some d := (spec.states ++ spec.props).find? (·.id.getId == f)
          | throwError s!"component: internal unknown field `{f}`"
        `(Lean.Parser.Command.ctor| | $cId:ident (v : $(d.ty)))
    | none => `(Lean.Parser.Command.ctor| | $cId:ident)
  if let some rd := spec.route? then
    ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $(mkIdent `_onRoute):ident (_r : $(rd.ty))))
  if spec.outTy?.isSome then
    ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $(mkIdent `_emit):ident (_o : $(mkIdent (tId ++ `Out)))))
  for (colField, colChild) in spec.collections do
    ctors := ctors.push (← `(Lean.Parser.Command.ctor|
      | $(mkIdent colField.getId):ident (key : String) (msg : $(mkIdent (colChild.getId ++ `Msg)))))
  for q in spec.queries do
    let qCtor := mkIdent q.ctorName
    ctors := ctors.push (← `(Lean.Parser.Command.ctor|
      | $qCtor:ident (key : String) (res : Resource $(q.ty))))
  for h in spec.hoisted do
    ctors := ctors.push (← `(Lean.Parser.Command.ctor|
      | $(mkIdent h.ctorName):ident (msg : $(mkIdent (h.info.fullName ++ `Msg)))))
  let msgCmd ← if ctors.isEmpty then `(command| inductive $msgId)
    else `(command| inductive $msgId where $[$ctors:ctor]*)
  let mut outCmds : Array (TSyntax `command) := #[msgCmd]
  for po in spec.portOuts do
    let poName := mkIdent (tId ++ po.id.getId)
    let poLit := Syntax.mkStrLit po.id.getId.toString
    outCmds := outCmds.push (← `(command| def $poName (x : $(po.ty)) : Cmd $msgId :=
      Cmd.port $poLit (Json.render (ToJson.toJson x))))
  if spec.outTy?.isSome then
    outCmds := outCmds.push (← `(command|
      instance : Coe $(mkIdent (tId ++ `Out)) $msgId := ⟨$(mkIdent (tId ++ `Msg ++ `_emit))⟩))
  let unchanged ← mkUpdateRet spec (← `(s)) none #[]
  let mut ownArms ← sites.mapM fun site => do
    let cFull := mkIdent (tId ++ `Msg ++ site.ctor)
    let mut rhs ← (match site.stmts? with
      | some stmts => do
          let isPureNoop := stmts.all fun st =>
            ![``actionAssignStmt, ``actionSendStmt, ``actionPerformStmt,
              ``actionIfStmt, ``actionIfLetStmt, ``actionMatchStmt, ``actionNoopStmt].contains st.getKind
          if isPureNoop then throwErrorAt stmts[0]! "an action must update state, perform an effect, or send an output"
          compileStmts spec (← `(s)) #[] none #[] stmts.toList
      | none => do mkUpdateRet spec (← flushAssigns (← `(s)) site.assigns) site.send? #[])
    if let some guard := site.guard? then rhs ← `(if $guard then $rhs else $unchanged)
    rhs ← bindMentionedFields spec (fun g =>
      (site.stmts?.any (·.any (mentionsIdent · g))) ||
      (site.assigns.any fun (_, e?) => e?.any (mentionsIdent ·.raw g)) ||
      (site.send?.any (mentionsIdent ·.raw g)) ||
      (site.guard?.any (mentionsIdent ·.raw g))) rhs
    if !site.params.isEmpty then
      let ids : Array Term := site.params.map (⟨·.1.raw⟩)
      `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $ids* => $rhs)
    else if site.assigns.any (·.2.isNone) then `(Lean.Parser.Term.matchAltExpr| | $cFull:ident v => $rhs)
    else `(Lean.Parser.Term.matchAltExpr| | $cFull:ident => $rhs)
  if let some rd := spec.route? then
    let cFull := mkIdent (tId ++ `Msg ++ `_onRoute)
    let rVal := mkIdent `_r
    let sWithR ← `({ s with $(rd.field):ident := $rVal:ident })
    let mut rhs ← (if rd.alts.isEmpty then mkUpdateRet spec sWithR none #[]
      else do
        let alts ← rd.alts.mapM fun alt => do
          let pats : Array Term := alt[1].getSepArgs.map (⟨·⟩)
          `(Lean.Parser.Term.matchAltExpr| | $[$pats:term],* =>
              $(← compileStmts spec sWithR #[] none #[] (unpackSeq alt[3]).toList))
        `(match $rVal:ident with $[$alts:matchAlt]*))
    rhs ← bindMentionedFields spec (fun g => g != rd.field.getId && mentionsIdent rhs.raw g) rhs
    rhs ← `(let $(mkIdent rd.field.getId):ident := $rVal:ident; $rhs)
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr| | $cFull:ident $rVal:ident => $rhs))
  if spec.outTy?.isSome then
    let oVar := mkIdent `_o
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | $(mkIdent (tId ++ `Msg ++ `_emit)):ident $oVar:ident => $(← mkUpdateRet spec (← `(s)) (some ⟨oVar.raw⟩) #[])))
  for (colField, colChild) in spec.collections do
    let nm := mkIdent colField.getId
    let next ← `({ s with $nm:ident := $(mkIdent (colChild.getId ++ `updateKeyed)) s.$nm:ident k msg })
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | $(mkIdent (tId ++ `Msg ++ colField.getId)) k msg => $(← mkUpdateRet spec next none #[])))
  for q in spec.queries do
    let qNm := q.id
    let qCtor := mkIdent (tId ++ `Msg ++ q.ctorName)
    let keyBound ← bindMentionedFields spec (mentionsIdent q.keyExpr.raw) q.keyExpr
    let next ← `({ s with $qNm:ident := (s.$qNm:ident).put _qk _qr $keyBound })
    ownArms := ownArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | $qCtor:ident _qk _qr => $(← mkUpdateRet spec next none #[])))
  let retTy : Term ← match spec.outTy?, spec.hasEffects with
    | none,   false => `($stateId)
    | some o, false => `($stateId × Option $o)
    | none,   true  => `($stateId × Cmd $msgId)
    | some o, true  => `($stateId × Option $o × Cmd $msgId)
  let pBinders ← mkPropsBinders spec
  if spec.hoisted.isEmpty then
    let updateBody ← if ownArms.isEmpty then `(fun m => nomatch m) else `(fun m => match m with $[$ownArms:matchAlt]*)
    return outCmds.push (← `(command| def $updateId $[$pBinders:bracketedBinder]* (s : $stateId) : $msgId → $retTy := $updateBody))
  let stepOwnId := mkIdent (tId ++ `stepOwn)
  let subNoopArms ← spec.hoisted.mapM fun h =>
    `(Lean.Parser.Term.matchAltExpr| | $(mkIdent (tId ++ `Msg ++ h.ctorName)) _ => $unchanged)
  outCmds := outCmds.push (← `(command| def $stepOwnId $[$pBinders:bracketedBinder]* (s : $stateId) : $msgId → $retTy :=
    fun m => match m with $[$(ownArms ++ subNoopArms):matchAlt]*))
  let callStepOwn (sArg mArg : Term) : CommandElabM Term :=
    if spec.hasProps then `($stepOwnId p $sArg $mArg) else `($stepOwnId $sArg $mArg)
  let mut fullArms ← spec.hoisted.mapM fun h => do
    let subCtor := mkIdent (tId ++ `Msg ++ h.ctorName)
    let cUpd := mkIdent (h.info.fullName ++ `update)
    let subF := h.fieldId; let cmVar := mkIdent `_cm; let crVar := mkIdent `_cr; let s1Var := mkIdent `_s1
    let cCall ← if h.info.hasProps then `($cUpd $(← mkHoistedPropsTerm h) s.$subF:ident $cmVar:ident)
      else `($cUpd s.$subF:ident $cmVar:ident)
    let (csExpr, coExpr?, rawC?) ← unpackRetTuple h.info.hasOut h.info.hasEffects crVar
    let ccExpr? ← rawC?.mapM fun rc => `(Cmd.map $subCtor $rc)
    let noOutRet ← mkUpdateRet spec ⟨s1Var.raw⟩ none (match ccExpr? with | some c => #[c] | none => #[])
    let afterSub : Term ← match coExpr? with
      | none => pure noOutRet
      | some coE =>
          let outVar := mkIdent `_co
          let mapOutToMsg? : Option Term ←
            if let some onE := h.onEmit? then some <$> `(some ($onE $outVar:ident))
            else if !h.outArms.isEmpty then
              some <$> (liftMacroM <| mkOutMatchTerm h.info.fullName
                (h.info.events.size + h.info.bindNames.size) h.outArms outVar)
            else pure none
          match mapOutToMsg? with
          | none => pure noOutRet
          | some pmOpt =>
              let pmVar := mkIdent `_pm
              let stepCall ← callStepOwn ⟨s1Var.raw⟩ ⟨pmVar.raw⟩
              let mergedStep ← match ccExpr?, spec.hasEffects with
                | some cc, true =>
                    let srVar := mkIdent `_sr
                    if spec.outTy?.isSome then
                      `(let $srVar:ident := $stepCall; (($srVar:ident).1, ($srVar:ident).2.1, Cmd.batch [$cc, ($srVar:ident).2.2]))
                    else `(let $srVar:ident := $stepCall; (($srVar:ident).1, Cmd.batch [$cc, ($srVar:ident).2]))
                | _, _ => pure stepCall
              `(match $coE:term with
                | none => $noOutRet
                | some $outVar:ident => match $pmOpt:term with
                  | none => $noOutRet
                  | some $pmVar:ident => $mergedStep)
    let mut armBody ← `(let $crVar:ident := $cCall; let $s1Var:ident := { s with $subF:ident := $csExpr }; $afterSub)
    armBody ← bindMentionedFields spec (mentionsIdent armBody.raw) armBody
    `(Lean.Parser.Term.matchAltExpr| | $subCtor $cmVar:ident => $armBody)
  if !ownArms.isEmpty then
    let otherVar := mkIdent `_m
    fullArms := fullArms.push (← `(Lean.Parser.Term.matchAltExpr| | $otherVar:ident => $(← callStepOwn (← `(s)) ⟨otherVar.raw⟩)))
  let updateBody ← if fullArms.isEmpty then `(fun m => nomatch m) else `(fun m => match m with $[$fullArms:matchAlt]*)
  return outCmds.push (← `(command| def $updateId $[$pBinders:bracketedBinder]* (s : $stateId) : $msgId → $retTy := $updateBody))

private def mkViewCmds (spec : ComponentSpec) (body' : Term)
    (msgAndUpdateCmds : Array (TSyntax `command)) : CommandElabM (Array (TSyntax `command)) := do
  let doc?     := spec.doc?
  let tId      := spec.t.getId
  let propsId  := mkIdent (tId ++ `Props)
  let stateId  := mkIdent (tId ++ `State)
  let msgId    := mkIdent (tId ++ `Msg)
  let updateId := mkIdent (tId ++ `update)
  let viewId   := mkIdent (tId ++ `view)
  let renderId := mkIdent (tId ++ `render)
  let pBinders ← mkPropsBinders spec
  let mut cmds := msgAndUpdateCmds
  if spec.hasSlotsOrKids then
    let pMsg := mkIdent `_msg; let wrapId := mkIdent `_wrap
    let mut slotBinders ← spec.slots.mapM fun sl => do
      `(bracketedBinder| ($(sl.id) : Html $pMsg := $(← sl.def?.getDM `(Qed.Html.empty))))
    if spec.hasChildren then
      slotBinders := slotBinders.push (← `(bracketedBinder| ($(mkIdent `children) : List (Html $pMsg) := [])))
    let renderBody ← bindMentionedFields spec (mentionsIdent body'.raw) body'
    cmds := cmds.push (← `(command| def $renderId {$pMsg : Type} $[$pBinders:bracketedBinder]* ($wrapId : $msgId → $pMsg)
        (s : $stateId) $[$slotBinders:bracketedBinder]* : Html $pMsg := $renderBody))
    let viewCall ← if spec.hasProps then `($renderId p id s) else `($renderId id s)
    return cmds.push (← `(command| def $viewId $[$pBinders:bracketedBinder]* (s : $stateId) : Html $msgId := $viewCall))
  let viewBody ← bindMentionedFields spec (mentionsIdent body'.raw) body'
  cmds := cmds.push (← `(command| def $viewId $[$pBinders:bracketedBinder]* (s : $stateId) : Html $msgId := $viewBody))
  let rendered ← if spec.hasProps then `($viewId p s) else `($viewId s)
  cmds := cmds.push (← `(command| def $renderId {parentMsg : Type} $[$pBinders:bracketedBinder]*
      (route : $msgId → parentMsg) (s : $stateId) : Html parentMsg := ($rendered).map route))
  if spec.outTy?.isNone && !spec.hasEffects then
    let renderTagId := mkIdent (tId ++ `renderTag)
    let compId      := mkIdent (tId ++ `toComponent)
    let appOptP (fn : Ident) := if spec.hasProps then `($fn p) else `($fn)
    let compExpr ← appOptP compId
    cmds := cmds ++ #[
      ← (match spec.keyF? with
        | some kf =>
          `(command| def $renderTagId {parentMsg : Type} (p : $propsId)
              (route : String → $msgId → parentMsg) (s : $stateId)
              (k : String := toString s.$(mkIdent kf.getId.eraseMacroScopes)) : Html parentMsg := ($rendered).map (route k))
        | none =>
          `(command| def $renderTagId {parentMsg : Type} (p : $propsId)
              (route : $msgId → parentMsg) (s : $stateId) : Html parentMsg := ($rendered).map route)),
      ← `(command| $[$doc?:docComment]? def $compId $[$pBinders:bracketedBinder]*
            : Component $stateId $msgId := { update := $(← appOptP updateId), view := $(← appOptP viewId) }) ]
    if let some kf := spec.keyF? then
      let keyOfId := mkIdent (tId ++ `keyOf)
      cmds := cmds ++ #[
        ← `(command| def $keyOfId (s : $stateId) : String := toString s.$(mkIdent kf.getId.eraseMacroScopes)),
        ← `(command| def $(mkIdent (tId ++ `updateKeyed)) $[$pBinders:bracketedBinder]*
              (rows : Array $stateId) (k : String) (msg : $msgId) : Array $stateId :=
              Component.updateKeyed $compExpr $keyOfId rows k msg) ]
  return cmds

private def canSynthJson (fromCls : Name) (tyTerm : Term) : CommandElabM Bool :=
  liftTermElabM do
    try
      let ty ← Term.elabType tyTerm
      return ((← Meta.trySynthInstance (← Meta.mkAppM ``ToJson #[ty])) matches .some _) &&
             ((← Meta.trySynthInstance (← Meta.mkAppM fromCls #[ty])) matches .some _)
    catch _ => return false

private def mkCodecAndMountCmds (spec : ComponentSpec) (starts' : Array Term) (idLit : StrLit) :
    CommandElabM (Array (TSyntax `command) × Bool × Bool) := do
  let doc?       := spec.doc?
  let tId        := spec.t.getId
  let fs         := spec.states.map (·.id)
  let stateId    := mkIdent (tId ++ `State)
  let initId     := mkIdent (tId ++ `init)
  let startCmdId := mkIdent (tId ++ `startCmd)
  let msgId      := mkIdent (tId ++ `Msg)
  let updateId   := mkIdent (tId ++ `update)
  let viewId     := mkIdent (tId ++ `view)
  let regId      := mkIdent (tId ++ `reg)
  let regsId     := mkIdent (tId ++ `regs)
  let mut cmds : Array (TSyntax `command) := #[]
  if spec.mountable then
    let dsT := spec.states.filterMap (·.def?)
    cmds := cmds.push (← `(command| def $initId : $stateId := { $[$fs:ident := $dsT],* }))
  let hoistedStarts := spec.hoisted.filter (·.info.hasStart)
  let hasStart := !starts'.isEmpty || !hoistedStarts.isEmpty
  if hasStart then
    let pBinders ← mkPropsBinders spec
    let subStarts ← hoistedStarts.mapM fun h => do
      let cStart := mkIdent (h.info.fullName ++ `startCmd)
      let call ← if h.info.hasProps then `($cStart $(← mkHoistedPropsTerm h)) else `($cStart)
      `(Cmd.map $(mkIdent (tId ++ `Msg ++ h.ctorName)) $call)
    let mut startBody ← mkCmdBatch (starts' ++ subStarts)
    if spec.mountable then
      startBody ← bindMentionedFields spec (mentionsIdent startBody.raw) startBody
      if mentionsIdent startBody.raw `s then
        startBody ← `(let s := $initId; $startBody)
    cmds := cmds.push (← `(command| def $startCmdId $[$pBinders:bracketedBinder]* : Cmd $msgId := $startBody))
  let outCtorSpecs : Array (Name × Array (Ident × Term)) :=
    spec.events.map (fun ev => (ev.id.getId, ev.params)) ++
    spec.binds.map (fun bd => (Name.mkSimple s!"set_{bd.id.getId}", #[(mkIdent `v, bd.ty)]))
  let propsOk ← spec.props.allM (canSynthJson ``FromJsonField ·.ty)
  let stateOk ← spec.states.allM (canSynthJson ``FromJsonField ·.ty)
  let outJsonOk ←
    if spec.outTy?.isSome then outCtorSpecs.allM fun (_, ps) => ps.allM (canSynthJson ``FromJsonField ·.2)
    else pure true
  let canEmitCodecs := propsOk && stateOk
  if canEmitCodecs then
    let mkStructJsonCmds (sName : Name) (decls : Array FieldDecl) := do
      let sId := mkIdent sName; let ids := decls.map (·.id)
      let enc ← decls.mapM fun d => `(($(Syntax.mkStrLit d.id.getId.toString), toJson (x.$(d.id):ident)))
      let dec ← decls.mapM fun d => `((FromJsonField.fromField j $(Syntax.mkStrLit d.id.getId.toString) : Except String $(d.ty)))
      pure #[
        ← `(command| instance $(mkIdent (sName ++ `instToJson)):ident : ToJson $sId := ⟨fun x => Json.obj [$[$enc],*]⟩),
        ← `(command| instance $(mkIdent (sName ++ `instFromJson)):ident : FromJson $sId := ⟨fun j => do
              $[let $ids:ident ← $dec:term]*
              return { $[$ids:ident],* }⟩) ]
    cmds := cmds ++ (← mkStructJsonCmds (tId ++ `Props) spec.props) ++ (← mkStructJsonCmds (tId ++ `State) spec.states)
  if spec.outTy?.isSome && outJsonOk then
    let outId := mkIdent (tId ++ `Out)
    let encAlts ← outCtorSpecs.mapM fun (cName, ps) => do
      let cId := mkIdent (tId ++ `Out ++ cName)
      let pIds := ps.map (·.1); let pTerms : Array Term := pIds.map (⟨·.raw⟩)
      let kvPairs ← (List.range pIds.size).toArray.mapM fun i =>
        `(($(Syntax.mkStrLit (toString i)), toJson $(pIds[i]!):ident))
      let allPairs := #[← `(("t", Json.str $(Syntax.mkStrLit cName.toString)))] ++ kvPairs
      `(Lean.Parser.Term.matchAltExpr| | $cId $pTerms* => Json.obj [$[$allPairs],*])
    let mut decBody : Term ← `(Except.error "unknown Out tag")
    for (cName, ps) in outCtorSpecs.reverse do
      let cId := mkIdent (tId ++ `Out ++ cName)
      let pIds := ps.map (·.1); let pTerms : Array Term := pIds.map (⟨·.raw⟩)
      let decSteps ← (List.range ps.size).toArray.mapM fun i =>
        `((FromJsonField.fromField j $(Syntax.mkStrLit (toString i)) : Except String $(ps[i]!.2)))
      let okBr ← `(do
        $[let $pIds:ident ← $decSteps:term]*
        return ($cId $pTerms*))
      decBody ← `(if tag == $(Syntax.mkStrLit cName.toString) then $okBr else $decBody)
    cmds := cmds ++ #[
      ← `(command| instance : ToJson $outId := ⟨fun o => match o with $[$encAlts:matchAlt]*⟩),
      ← `(command| instance : FromJson $outId := ⟨fun j => do
            let tag ← (FromJsonField.fromField j "t" : Except String String)
            $decBody:term⟩) ]
  let hasLocalDef := spec.mountable && !spec.hasEffects && !spec.hasSlotsOrKids && canEmitCodecs && outJsonOk
  if hasLocalDef then
    cmds := cmds ++ #[
      ← (if spec.hasProps then
          if spec.outTy?.isNone then `(command| def $regId : LocalDef :=
            LocalDef.ofProps $idLit $initId $viewId (fun p s m => ($updateId p s m, (none : Option Bool))))
          else `(command| def $regId : LocalDef := LocalDef.ofProps $idLit $initId $viewId $updateId)
        else if spec.outTy?.isNone then `(command| $[$doc?:docComment]? def $regId : LocalDef :=
          LocalDef.ofSimple $idLit $initId $viewId $updateId)
        else `(command| $[$doc?:docComment]? def $regId : LocalDef :=
          LocalDef.of $idLit $initId $viewId $updateId)),
      ← `(command| $[$doc?:docComment]? def $(mkIdent (tId ++ `mount)) {msg : Type} (key : String) : Attr msg :=
            localMount $idLit key) ]
    if let some o := spec.outTy? then
      cmds := cmds ++ #[
        ← `(command| $[$doc?:docComment]? def $(mkIdent (tId ++ `mountWith)) {msg : Type}
              (key : String) (onOut : $o → msg) : Attr msg :=
              localMountWith $idLit key (fun out => some (onOut out))),
        ← `(command| def $(mkIdent (tId ++ `mountWithOpt)) {msg : Type}
              (key : String) (onOut : $o → Option msg) : Attr msg :=
              localMountWith $idLit key onOut) ]
  let own : Term ← if hasLocalDef then `([$regId]) else `(([] : List LocalDef))
  cmds := cmds.push (← `(command| def $regsId : List LocalDef :=
    LocalDef.dedupe ($own ++ localRegistrations $viewId)))
  if spec.mountable && spec.outTy?.isNone && !spec.hasProps && !spec.hasSlotsOrKids then
    let startArg : Term ← if hasStart then `($startCmdId) else `(Qed.Cmd.none)
    let onPortArg : Term ← if spec.portIns.isEmpty then `(Option.none) else do
      let onPortId := mkIdent (tId ++ `onPort)
      let inTuples ← spec.portIns.mapM fun p => do
        let pLit := Syntax.mkStrLit p.id.getId.toString
        let pCtor := mkIdent (tId ++ `Msg ++ p.id.getId)
        `(($pLit, fun raw => (((Json.parse raw).bind FromJson.fromJson : Except String $(p.argTy)).toOption).map $pCtor))
      cmds := cmds.push (← `(command| def $onPortId : String → String → Option $msgId :=
        dispatchPorts #[$inTuples,*]))
      `(some $onPortId)
    let baseApp : Term ← match spec.route? with
      | some _ => `(mkRoutedApp $initId $updateId (View.ofHtml $viewId)
          (onRoute := $(mkIdent (tId ++ `Msg ++ `_onRoute))) (start := $startArg) (locals := $regsId) (onPort := $onPortArg))
      | none   => `(mkApp $initId $updateId (View.ofHtml $viewId) (start := $startArg) (locals := $regsId) (onPort := $onPortArg))
    let dehydApp : Term ← if spec.ephemeralFields.isEmpty then `(withAutoDehydrate $initId $baseApp)
      else `(App.withDehydrate (Dehydrate.except $initId [$[$spec.ephemeralFields:ident],*]) $baseApp)
    let finalApp : Term ← if spec.queries.isEmpty then pure dehydApp else do
      let qTerms ← spec.queries.mapM fun q => do
        let qNm := q.id
        let qCtor := mkIdent (tId ++ `Msg ++ q.ctorName)
        let keyBound ← bindMentionedFields spec (mentionsIdent q.keyExpr.raw) q.keyExpr
        `(Resource.query
            (key := fun (s : $stateId) => $keyBound)
            (url := $(q.urlExpr))
            (got := $qCtor)
            (get := fun (s : $stateId) => s.$qNm:ident)
            (set := fun c (s : $stateId) => { s with $qNm:ident := c }))
      `(App.withQueries [$[$qTerms],*] $dehydApp)
    cmds := cmds.push (← `(command| $[$doc?:docComment]? def $(mkIdent (tId ++ `app)) : App $stateId $msgId :=
      withLocalRegistry $finalApp))
  return (cmds, hasStart, hasLocalDef)

/-! ## Inline Invariant Elaboration -/

private def isViewPred (msgId : Ident) (pred : Term) : CommandElabM Bool := do
  let saved ← get
  try
    let ok ← liftTermElabM do
      let preCount := (← Core.getMessageLog).toList.length
      let expected ← Term.elabType (← `(Html $msgId → Bool))
      let _ ← Term.elabTermEnsuringType pred expected
      Term.synthesizeSyntheticMVarsNoPostponing
      return ((← Core.getMessageLog).toList.drop preCount).all (·.severity != .error)
    modify fun _ => saved
    return ok
  catch _ =>
    modify fun _ => saved
    return false

private def elabInlineInvariants (spec : ComponentSpec) : CommandElabM Unit := do
  let tId      := spec.t.getId
  let propsId  := mkIdent (tId ++ `Props)
  let stateId  := mkIdent (tId ++ `State)
  let initId   := mkIdent (tId ++ `init)
  let msgId    := mkIdent (tId ++ `Msg)
  let updateId := mkIdent (tId ++ `update)
  let viewId   := mkIdent (tId ++ `view)
  for invStx in spec.invariants do
    if invStx.getKind == ``compForEachInvClause then
      let invId ← resolveInvIdent invStx tId
      let pred : Term := ⟨invStx[2]⟩
      let colField : Ident := ⟨invStx[4]⟩
      let hasHoldsIn := invStx[5].getNumArgs > 0
      let using? : Option Ident := if invStx[6].getNumArgs == 2 then some ⟨invStx[6][1]⟩ else none
      let pf? : Option Term := if invStx[7].getNumArgs == 2 then some ⟨invStx[7][1]⟩ else none
      let probeId? := using?.or (if pred.raw.isIdent then some ⟨pred.raw⟩ else none)
      let isStyled ← if hasHoldsIn then pure true
        else match probeId? with
        | some pid =>
            liftTermElabM do
              try
                let cn ← realizeGlobalConstNoOverload pid
                Meta.forallTelescope (← getConstInfo cn).type fun _ body => return body.eq?.isSome
              catch _ => return false
        | none => pure false
      let (predToEmit, usingToEmit?) ← match using?, pf? with
        | some u, _ => pure (pred, some u)
        | none, some _ =>
            unless pred.raw.isIdent do
              throwErrorAt invStx "specify `using <ChildInvariant>` when proving a custom predicate"
            let childInv : Ident := ⟨pred.raw⟩
            let ep ← if isStyled then
              liftTermElabM do
                let cn ← realizeGlobalConstNoOverload childInv
                Meta.forallTelescope (← getConstInfo cn).type fun _ body => do
                  let some lhs := body.eq?.map (·.2.1) | throwErrorAt childInv
                    "`{childInv}` doesn't look like a `… holds_in …` invariant"
                  PrettyPrinter.delab lhs.appFn!
            else liftTermElabM (extractInvPred childInv)
            pure (ep, some childInv)
        | none, none =>
            unless pred.raw.isIdent do
              throwErrorAt invStx "specify `using <ChildInvariant>` for an inline `for_each` predicate"
            pure (pred, none)
      match isStyled, usingToEmit? with
      | true,  some u => elabCommand (← `(invariant $invId : $predToEmit for_each $colField holds_in $viewId using $u $[:= $pf?]?))
      | true,  none   =>
          let pid : Ident := ⟨predToEmit.raw⟩
          elabCommand (← `(invariant $invId : $pid for_each $colField holds_in $viewId))
      | false, some u => elabCommand (← `(invariant $invId : $predToEmit for_each $colField preserved_by $updateId using $u $[:= $pf?]?))
      | false, none   =>
          let pid : Ident := ⟨predToEmit.raw⟩
          elabCommand (← `(invariant $invId : $pid for_each $colField preserved_by $updateId))
      continue
    let invId ← resolveInvIdent invStx tId
    let clauses : Array Term := invStx[2].getSepArgs.map (⟨·⟩)
    let hasHoldsIn := invStx[3].getNumArgs > 0
    let assume? : Option Term :=
      if hasHoldsIn && invStx[3][2].getNumArgs == 2 then some ⟨invStx[3][2][1]⟩ else none
    let using? : Option (Array Term) :=
      if invStx[4].getNumArgs == 4 then some (invStx[4][2].getSepArgs.map (⟨·⟩)) else none
    let pf? : Option Term := if invStx[5].getNumArgs == 2 then some ⟨invStx[5][1]⟩ else none
    let autoView ← if !hasHoldsIn && clauses.size == 1 && using?.isNone &&
        !spec.allNames.any (mentionsIdent clauses[0]!.raw) then
      isViewPred msgId clauses[0]!
    else pure false
    if hasHoldsIn || autoView then
      if clauses.size != 1 then throwErrorAt invStx[2] "a view styling invariant takes a single styling rule"
      let vPred := clauses[0]!
      if spec.hasProps then
        let predStr := (vPred.raw.reprint.getD "this rule").trimmed
        let rhs ← pf?.getDM `(by
          let _qed_hv := $viewId p
          change ∀ m, ($vPred) (_qed_hv m) = true
          qedDischargeStyling _qed_hv $invId $(Syntax.mkStrLit predStr))
        elabCommand (← `(command| set_option linter.unusedSimpArgs false in
          theorem $invId:ident (p : $propsId) : ∀ m, ($vPred) ($viewId p m) = true := $rhs))
      else
        elabCommand (← `(invariant $invId : $vPred holds_in $viewId $[assuming $assume?]? $[ := $pf?]?))
    else
      let conj ← mkConjBody clauses
      let pred ← `(fun (s : $stateId) => $(← bindMentionedFields spec (mentionsIdent conj.raw) conj))
      let usingL := using?.getD #[]
      if spec.hasProps then
        let rhs ← pf?.getDM `(by qedDischargePreserved [$[$usingL],*] ($updateId p) $invId ($pred))
        elabCommand (← `(theorem $invId:ident (p : $propsId) :
          ∀ m msg, ($pred) m → ($pred) (InvTarget.proj ($updateId p m msg)) := $rhs))
      else
        let stepPf? ← pf?.mapM fun pf =>
          if spec.mountable then
            `(by exact ⟨by first | rfl | decide | (simp [$initId:ident]; decide) | (simp [$initId:ident]; omega), $pf⟩)
          else pure pf
        let initOpt? : Option Term := if spec.mountable then some initId else none
        elabCommand (← `(invariant $invId : $pred $[from $initOpt?]? preserved_by $updateId using [$[$usingL],*] $[ := $stepPf?]?))

private def withOpenNs {α : Type} (ns : Name) (k : CommandElabM α) : CommandElabM α := do
  if (← getEnv).isNamespace ns then
    withScope (fun sc => { sc with openDecls := .simple ns [] :: sc.openDecls }) k
  else k

@[command_elab componentCmd] def elabComponentCmd : CommandElab := fun stx => do
  let compNs := (← getCurrNamespace) ++ stx[2].getId
  withOpenNs compNs do
    let rawSpec ← parseComponentSpec stx
    if rawSpec.states.isEmpty && rawSpec.actions.isEmpty && rawSpec.keyF?.isNone &&
        rawSpec.starts.isEmpty &&
        rawSpec.portOuts.isEmpty && rawSpec.portIns.isEmpty && rawSpec.queries.isEmpty then
      let sitesRef ← IO.mkRef #[]
      let hoistedRef ← IO.mkRef #[]
      let rCtx : RewriteCtx := {
        stateFields := #[], bindFields := rawSpec.bindNames, isPureComp := true,
        msgPath := rawSpec.t.getId ++ `Msg, hasOut := false, collections := #[],
        sites := sitesRef, hoisted := hoistedRef, allowHoist := true }
      let body' : Term := ⟨← rewriteIn rCtx false rawSpec.body⟩
      if (← hoistedRef.get).isEmpty then
        return ← elabPureComponent rawSpec body'
    let idLit := Syntax.mkStrLit compNs.toString
    let (sites, route'?, queries', starts', body', hoisted) ← collectSitesAndRewriteStateful rawSpec
    let ownHasEffects :=
      !starts'.isEmpty ||
      !rawSpec.portOuts.isEmpty || !rawSpec.portIns.isEmpty || !queries'.isEmpty ||
      sites.any (fun s => s.stmts?.any (·.any hasPerformNode)) ||
      (route'?.any fun rd => rd.alts.any hasPerformNode) ||
      hoisted.any (·.info.hasEffects)
    let spec ← elabStructsAndResolveTypes { rawSpec with route? := route'?, queries := queries', hasEffects := ownHasEffects } hoisted
    let coreCmds ← mkViewCmds spec body' (← mkMsgAndUpdateCmds spec sites)
    for c in coreCmds do elabCommand c
    let (mountCmds, hasStart, hasLocalDef) ← mkCodecAndMountCmds spec starts' idLit
    for c in mountCmds do elabCommand c
    withOpenNs compNs (elabInlineInvariants spec)
    let baseInfo ← mkBaseCompInfo spec .stateful spec.hasProps
    modifyEnv fun env => componentRegistry.addEntry env { baseInfo with
      hasOut := spec.outTy?.isSome, hasEffects := spec.hasEffects,
      hasStart, mountable := spec.mountable, hasLocalDef }

/-! ## JSX `<Component …>…</Component>` Term Elaborator (`elabQedCompTerm`) -/

open Term in
private def checkParentNesting (ref : Syntax) (pPath compLabel childTag : String) : TermElabM Unit := do
  if let some (ptag, pctx) := Qed.Jsx.ctxOfPath pPath then
    if (stepHtmlCtx pctx childTag).isNone then
      let what := if compLabel == childTag then s!"<{childTag}>" else s!"<{compLabel}> (root <{childTag}>)"
      throwErrorAt ref s!"invalid HTML5 nesting: {what} is not allowed inside <{ptag}> (browsers rewrite this tree during HTML parsing, causing hydration mismatch)"

open Term in
@[term_elab Qed.Jsx.qedCompTerm] def elabQedCompTerm : TermElab := fun stx expectedType? => do
  let tag := (⟨stx[1]⟩ : TSyntax `str).getString
  let pPath := (⟨stx[2]⟩ : TSyntax `str).getString
  let posNum := (⟨stx[3]⟩ : TSyntax `num).getNat
  let propNodes := stx[5].getSepArgs
  let kidsT : Term := ⟨stx[7]⟩
  let hasKids := !(kidsT.raw.getKind == `«term[_]» && kidsT.raw[1].getArgs.isEmpty)
  let cName := (tag.splitOn ".").foldl Name.str Name.anonymous
  let info? ← lookupComponent? cName
  let baseName := match info? with | some info => info.fullName | none => cName
  let cId (sub : Name) : Term := ⟨mkIdentFrom stx (baseName ++ sub)⟩
  let checkInlineComp (info : ComponentInfo) : TermElabM Unit := do
    if let some rtag := info.rootTag? then checkParentNesting stx pPath tag rtag
    if hasKids && !info.hasChildren then
      throwErrorAt stx s!"<{tag}> does not declare `children`; add `children` to `component {tag}` or write `<{tag} …/>`"
  let finishWithKey (key? : Option Term) (call : Term) : TermElabM Expr := do
    elabTerm (← match key? with | some k => `(Qed.withKey (toString $k) $call) | none => pure call) expectedType?

  if info?.isNone && tag.endsWith ".Form" then
    if let some sInfo ← lookupSchemaForm? cName then
      if hasKids then
        throwErrorAt stx s!"<{tag}> takes no children; write it self-closing (<{tag} …/>)"
      checkParentNesting stx pPath tag "div"
      let mut key?    : Option Term := none
      let mut bind?   : Option Term := none
      let mut submit? : Option Term := none
      let mut ctxVals : Std.HashMap Name Term := {}
      let mut ctxArg? : Option Term := none
      for p in propNodes do
        let nm := (⟨p[0]⟩ : TSyntax `str).getString
        let v : Term := ⟨p[2]⟩
        if nm == "key" then key? := some v
        else if nm == "bind" then bind? := some v
        else if nm == "onSubmit" then submit? := some v
        else if nm == "ctx" && sInfo.ctxBinders.size == 1 then ctxArg? := some v
        else
          let bName := Name.mkSimple nm
          if sInfo.ctxBinders.contains bName then
            ctxVals := ctxVals.insert bName v
          else
            throwErrorAt p[0] s!"<{tag}>: unknown attribute `{nm}`"
      let some b := bind?
        | throwErrorAt stx s!"<{tag}> requires `bind=\{draft}`"
      let dVal ← `(($b).1)
      let onEditVal ← `(($b).2)
      let some submitVal := submit?
        | throwErrorAt stx s!"<{tag}> requires `onSubmit=\{.submit}`"
      let mut ctxArgs : Array Term := #[]
      for b in sInfo.ctxBinders do
        if let some v := ctxVals[b]? then
          ctxArgs := ctxArgs.push v
        else if let some v := ctxArg? then
          ctxArgs := ctxArgs.push v
        else
          throwErrorAt stx s!"<{tag}> requires context attribute `{b}=\{…}`" ++
            (if sInfo.ctxBinders.size == 1 then " (or `ctx={…}`)" else "")
      let mut callT : Term := ⟨mkIdentFrom stx sInfo.formViewName⟩
      for ca in ctxArgs do
        callT ← `($callT $ca)
      callT ← `($callT $dVal $onEditVal $submitVal)
      return ← finishWithKey key? callT

  if let some info := info? then
    if info.kind == .pureView then
      checkInlineComp info
      let mut key? : Option Term := none
      let mut fids : Array Ident := #[]
      let mut vals : Array Term  := #[]
      for p in propNodes do
        let nm := (⟨p[0]⟩ : TSyntax `str).getString
        let v : Term := ⟨p[2]⟩
        if nm == "key" then key? := some v
        else if nm.startsWith "bind:" then
          let bStr := (nm.drop 5).toString
          fids := fids.push (mkIdentFrom p[0] (Name.mkSimple bStr))
          vals := vals.push (← `(($v).1))
          fids := fids.push (mkIdentFrom p[0] (Name.mkSimple s!"set_{bStr}"))
          vals := vals.push (← `(($v).2))
        else
          fids := fids.push (mkIdentFrom p[0] (Name.mkSimple nm))
          vals := vals.push v
      if hasKids then fids := fids.push (mkIdentFrom stx `children); vals := vals.push kidsT
      let callT ← if info.hasProps then
        `($(cId `view) ({ $[$fids:ident := $vals],* } : $(cId `Props) _))
      else `($(cId `view))
      return ← finishWithKey key? callT

  let mut props    : Array (Syntax × String × Term) := #[]
  let mut key?     : Option Term := none
  let mut state?   : Option Term := none
  let mut initial? : Option Term := none
  let mut onMsg?   : Option Term := none
  let mut onEmit?  : Option Term := none
  let mut hoist?   : Option Term := none
  for p in propNodes do
    let nm := (⟨p[0]⟩ : TSyntax `str).getString
    let v : Term := ⟨p[2]⟩
    match nm with
    | "key"     => key?     := some v
    | "state"   => state?   := some v
    | "initial" => initial? := some v
    | "onMsg"   => onMsg?   := some v
    | "onEmit"  => onEmit?  := some v
    | "_hoist"  => hoist?   := some v
    | _         => props    := props.push (p[0], nm, v)

  if let some hPair := hoist? then
    let some info := info? | throwErrorAt stx s!"internal: missing ComponentInfo for hoisted <{tag}>"
    checkInlineComp info
    let mut dataFids : Array Ident := #[]
    let mut dataVals : Array Term  := #[]
    let mut slotArgs : Array (TSyntax ``Lean.Parser.Term.argument) := #[]
    for (ref, nm, v) in props do
      let id := mkIdentFrom ref (Name.mkSimple nm)
      if info.slotNames.contains id.getId then
        slotArgs := slotArgs.push (← `(Lean.Parser.Term.argument| ($id:ident := $v)))
      else
        dataFids := dataFids.push id; dataVals := dataVals.push v
    if hasKids then
      slotArgs := slotArgs.push (← `(Lean.Parser.Term.argument| ($(mkIdentFrom stx `children):ident := $kidsT)))
    let wrapA ← `(Lean.Parser.Term.argument| ($hPair).1)
    let subSA ← `(Lean.Parser.Term.argument| ($hPair).2)
    let baseArgs ← if info.hasProps then
      let propRec ← `(({ $[$dataFids:ident := $dataVals],* } : $(cId `Props)))
      pure #[← `(Lean.Parser.Term.argument| $propRec:term), wrapA, subSA]
    else pure #[wrapA, subSA]
    let renderCall : Term := ⟨Syntax.node .none ``Lean.Parser.Term.app
      #[(cId `render).raw, Syntax.node .none nullKind ((baseArgs ++ slotArgs).map (·.raw))]⟩
    return ← finishWithKey key? renderCall

  if hasKids then
    throwErrorAt stx s!"<{tag}>: a component tag renders the component's own view, so it takes no children; write it self-closing (<{tag} …/>) or declare `children` on `{tag}`"

  let evSigs := match info? with | some i => i.events | none => #[]
  let mut dataProps : Array (Syntax × String × Term) := #[]
  let mut evArms    : Array OutArm := #[]
  for (ref, nm, v) in props do
    if nm.startsWith "bind:" then
      let bStr := (nm.drop 5).toString
      dataProps := dataProps.push (ref, bStr, ← `(($v).1))
      evArms := evArms.push { ctor := Name.mkSimple s!"set_{bStr}", arity := 1, handler := ← `(($v).2) }
    else if let some sig := evSigs.find? (·.name.toString == nm) then
      evArms := evArms.push { ctor := sig.name, arity := sig.arity, handler := v }
    else
      dataProps := dataProps.push (ref, nm, v)

  let fids := dataProps.map fun (ref, n, _) => mkIdentFrom ref (Name.mkSimple n)
  let vals := dataProps.map (·.2.2)
  let propValues ← `(({ $[$fids:ident := $vals],* } : $(cId `Props)))

  if let some st := state? then
    if initial?.isSome then throwErrorAt stx "`initial` seeds local state; it cannot accompany `state`"
    if onEmit?.isSome || !evArms.isEmpty then
      throwErrorAt stx s!"<{tag} state=…>: a parent-owned component routes every event through onMsg, it has no separate emit channel"
    let some route := onMsg?
      | throwErrorAt stx s!"<{tag} state=…> needs onMsg=…: the parent Msg constructor `(k : String) (msg : {tag}.Msg)` its events route through"
    let resT ← match key? with
      | some k => `(Qed.withKey (toString $k) ($(cId `renderTag) $propValues $route $st (toString $k)))
      | none   => `($(cId `renderTag) $propValues $route $st)
    return ← elabTerm resT expectedType?

  if onMsg?.isSome then
    throwErrorAt stx s!"<{tag}>: onMsg routes a parent-owned row; bind one with state=…, or receive outputs with onEmit=…"
  if let some info := info? then
    if !info.hasLocalDef then
      throwErrorAt stx s!"<{tag}> uses effects, slots, children, or non-JSON props and cannot be mounted via `LocalDef`; mount `<{tag} …/>` directly inside a parent `component` view so Qed hoists it"
  checkParentNesting stx pPath "div" "div"
  let keyT : Term ← match key? with | some k => `(toString $k) | none => pure ⟨Syntax.mkStrLit s!"@{posNum}"⟩
  let mountBase : Term ←
    if let some h := onEmit? then
      `($(cId `mountWith) $keyT (fun out => $h out))
    else if !evArms.isEmpty then
      let outVar := mkIdent `_out
      let totalOutCtors := (info?.map fun i => i.events.size + i.bindNames.size).getD 999
      let mTerm ← liftMacroM <| mkOutMatchTerm baseName totalOutCtors evArms outVar
      `($(cId `mountWithOpt) $keyT (fun $outVar:ident => $mTerm))
    else
      `($(cId `mount) $keyT)
  let mountBase ← match initial? with
    | none      => pure mountBase
    | some seed => `(Qed.Attr.localInit $mountBase ($seed : $(cId `State)))
  let mountT ← `(Qed.Attr.localProps $mountBase $propValues)
  elabTerm (← `(Qed.el "div" [Qed.key $keyT, $mountT] [])) expectedType?

end CompElab
end Qed
