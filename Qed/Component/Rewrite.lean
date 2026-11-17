import Qed.Component.Syntax
import Qed.Resource
import Qed.Schema

namespace Qed
section CompElab
open Lean Elab Command

/-! ## Component Spec Structures & Rewriting -/

structure FieldDecl where
  id   : Ident
  ty?  : Option Term := none
  def? : Option Term := none
  ty   : Term := ⟨.missing⟩

structure EventDecl where
  id     : Ident
  params : Array (Ident × Term)

structure SlotDecl where
  id   : Ident
  def? : Option Term

structure RouteDecl where
  field : Ident
  ty    : Term
  init  : Term
  alts  : Array Syntax

structure HoistedSub where
  fieldId   : Ident
  ctorName  : Name
  info      : ComponentInfo
  dataProps : Array (Ident × Term)
  outArms   : Array OutArm

structure SetSite where
  key     : String
  ctor    : Name
  params  : Array (Ident × Term) := #[]
  guard?  : Option Term := none
  assigns : Array (Name × Option Term) := #[]
  send?   : Option Term := none
  stmts?  : Option (Array Syntax) := none

structure PortOutDecl where
  id : Ident
  ty : Term

structure PortInDecl where
  id     : Ident
  argId  : Ident
  argTy  : Term
  guard? : Option Term
  body   : Syntax

structure QueryDecl where
  id      : Ident
  ty      : Term
  keyExpr : Term
  urlExpr : Term

def QueryDecl.ctorName (q : QueryDecl) : Name :=
  Name.mkSimple s!"_query_{q.id.getId}"

structure ComponentSpec where
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

def ComponentSpec.fieldNames (s : ComponentSpec) : Array Name := s.states.map (·.id.getId)
def ComponentSpec.propNames  (s : ComponentSpec) : Array Name := s.props.map (·.id.getId)
def ComponentSpec.bindNames  (s : ComponentSpec) : Array Name := s.binds.map (·.id.getId)
def ComponentSpec.allNames   (s : ComponentSpec) : Array Name :=
  (s.fieldNames ++ s.propNames ++ s.bindNames).toList.eraseDups.toArray
def ComponentSpec.mountable  (s : ComponentSpec) : Bool := s.states.all (·.def?.isSome)
def ComponentSpec.hasSlotsOrKids (s : ComponentSpec) : Bool := !s.slots.isEmpty || s.hasChildren

def mkBaseCompInfo (spec : ComponentSpec) (kind : CompMountKind) (hasProps : Bool) :
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

def desugarAssign (fname : Name) (op : String) (rhs : Term) : CommandElabM Term := do
  let fIdent := mkIdent fname
  match op with
  | ":=" => pure rhs
  | "+=" => `($fIdent + ($rhs))
  | "-=" => `($fIdent - ($rhs))
  | _    => throwErrorAt rhs s!"unknown assignment operator '{op}'"

def registerSite (sites : IO.Ref (Array SetSite))
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

structure RewriteCtx where
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

def wrapUnaryMsg (wrap? : Option Ident) (fn : Term) : CommandElabM Term := do
  match wrap? with | some w => `(fun _v => $w ($fn _v)) | none => pure fn

def mkSetterHandler (ctx : RewriteCtx) (fname : Name) : CommandElabM Term := do
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

def mkSiteExpr (ctx : RewriteCtx) (assigns : Array (Name × Option Term))
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

def checkMutableField (ctx : RewriteCtx) (ref : Syntax) (prefixMsg : String) (fname : Name) :
    CommandElabM Unit := do
  unless (ctx.stateFields ++ ctx.bindFields).contains fname do
    throwErrorAt ref "{prefixMsg}: not a `state` field of this component (fields: {ctx.stateFields.toList})"

def pushHandlerAssign (ctx : RewriteCtx) (assigns : Array (Name × Option Term))
    (fId : Syntax) (expr? : Option Term) :
    CommandElabM (Array (Name × Option Term)) := do
  let fname := fId.getId.eraseMacroScopes
  checkMutableField ctx fId s!"`{fname}`" fname
  if assigns.any (·.1 == fname) then
    throwErrorAt fId s!"`{fname}`: this handler already updates `{fname}`"
  if expr?.isNone && assigns.any (·.2.isNone) then
    throwErrorAt fId s!"`{fname} := ·`: only one `·` placeholder per handler"
  return assigns.push (fname, expr?)

def noEmitsErr (ref : Syntax) : CommandElabM Unit :=
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

private def rewriteLowerElement (ctx : RewriteCtx) (stx : Syntax)
    (rewrittenPairs : Array (Bool × Syntax)) (kids? : Option Syntax) : CommandElabM Syntax := do
  let some w := ctx.wrapMsg? | return rebuildJsxEl stx (rewrittenPairs.map (·.2)) kids?
  let msgTy := mkIdent ctx.msgPath
  let newAttrs ← rewrittenPairs.mapM fun (wasAssign, a') => do
    if !wasAssign && a'.getKind == ``Qed.Jsx.attrNamed && a'[1].getNumArgs == 2 &&
        a'[1][1].getKind == ``Qed.Jsx.attrValExpr then
      let aname := atomStr a'[0]
      let vT ← liftMacroM <| Qed.Jsx.expandAttrVal a'[1] (`(""))
      let wrapped? : Option Term ←
        if unitEvents.contains aname then some <$> `($w ($vT : $msgTy))
        else if strEvents.contains aname then some <$> `(fun _s => $w (($vT : String → $msgTy) _s))
        else if aname == "onCheck" then some <$> `(fun _b => $w (($vT : Bool → $msgTy) _b))
        else pure none
      return match wrapped? with | some wt => mkJsxAttrExpr aname wt | none => a'
    return a'
  return rebuildJsxEl stx newAttrs kids?

private def rewriteUpperElement (ctx : RewriteCtx) (inLambda : Bool) (stx : Syntax)
    (tag : String) (rewrittenAttrs : Array Syntax) (kids? : Option Syntax) : CommandElabM Syntax := do
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
        let mut outArms   : Array OutArm := #[]
        let mut keptAttrs : Array Syntax := #[]
        for a in rewrittenAttrs do
          if a.getKind == ``Qed.Jsx.attrNamed then
            let aname := atomStr a[0]
            let vT : Term ← if a[1].getNumArgs == 0 then `(Bool.true)
              else liftMacroM <| Qed.Jsx.expandAttrVal a[1] (`(""))
            if let some ev := cInfo.events.find? (·.name.toString == aname) then
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
          fieldId := subFieldId, ctorName := subName, info := cInfo, dataProps, outArms })
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

partial def rewriteIn (ctx : RewriteCtx) (inLambda : Bool) (stx : Syntax) : CommandElabM Syntax := do
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
      let rewrittenPairs ← stx[2].getArgs.mapM fun a => do
        let wasAssign := a.getKind == ``Qed.Jsx.attrNamed && a[1].getNumArgs == 2 &&
          a[1][1].getKind == ``Qed.Jsx.attrValAssign
        return (wasAssign, ← rewriteIn ctx inLambda a)
      return ← rewriteLowerElement ctx stx rewrittenPairs kids?
    let rewrittenAttrs ← stx[2].getArgs.mapM (rewriteIn ctx inLambda)
    return ← rewriteUpperElement ctx inLambda stx tag rewrittenAttrs kids?
  else
    match stx with
    | .node info kind args => return .node info kind (← args.mapM (rewriteIn ctx inLambda))
    | _ => return stx

/-! ## Component Specification Parsing -/

private structure SpecParseAcc where
  states          : Array FieldDecl := #[]
  ephemeralFields : Array Ident := #[]
  props           : Array FieldDecl := #[]
  binds           : Array FieldDecl := #[]
  slots           : Array SlotDecl := #[]
  hasChildren     : Bool := false
  events          : Array EventDecl := #[]
  collections     : Array (Ident × Ident) := #[]
  keyF?           : Option Ident := none
  route?          : Option RouteDecl := none
  starts          : Array Term := #[]
  portOuts        : Array PortOutDecl := #[]
  portIns         : Array PortInDecl := #[]
  queries         : Array QueryDecl := #[]
  actions         : Array Syntax := #[]
  invariants      : Array Syntax := #[]

private def requireTyOrDef (role : Name) (fId : Ident) (ty? d? : Option Term) : CommandElabM Unit := do
  if ty?.isNone && d?.isNone then
    throwErrorAt fId s!"`{role} {fId.getId}` needs a type (`: Type`), a default (`:= value`), or both"

private def parseCompClause (acc : SpecParseAcc) (cl : Syntax) : CommandElabM SpecParseAcc := do
  let k := cl.getKind
  if k == ``compFieldClause then
    let role := cl[0].getId
    let fId : Ident := ⟨cl[1]⟩
    let ty? : Option Term := if cl[2].getNumArgs == 2 then some ⟨cl[2][1]⟩ else none
    let d?  : Option Term := if cl[3].getNumArgs == 2 then some ⟨cl[3][1]⟩ else none
    match role with
    | `slot => return { acc with slots := acc.slots.push { id := fId, def? := d? } }
    | `prop =>
        requireTyOrDef role fId ty? d?
        return { acc with props := acc.props.push { id := fId, ty?, def? := d? } }
    | `bind =>
        requireTyOrDef role fId ty? d?
        return { acc with binds := acc.binds.push { id := fId, ty?, def? := d? } }
    | `collection =>
        let some colTy := ty? | throwErrorAt fId s!"`collection {fId.getId}` requires `: ChildComponent`"
        unless colTy.raw.isIdent do throwErrorAt colTy "`collection` target must be a child component name"
        let childId : Ident := ⟨colTy.raw⟩
        let fTy ← `(Array $(mkIdent (childId.getId ++ `State)))
        let fDef ← d?.getDM `(#[])
        return { acc with
          collections := acc.collections.push (fId, childId)
          states := acc.states.push { id := fId, ty? := some fTy, def? := some fDef } }
    | _ =>
        requireTyOrDef role fId ty? d?
        let eph := if role == `ephemeral then acc.ephemeralFields.push fId else acc.ephemeralFields
        return { acc with
          states := acc.states.push { id := fId, ty?, def? := d? }
          ephemeralFields := eph }
  else if k == ``compChildrenClause then
    return { acc with hasChildren := true }
  else if k == ``compKeyClause then
    if acc.keyF?.isSome then throwErrorAt cl "duplicate `key` clause in component"
    return { acc with keyF? := some ⟨cl[1]⟩ }
  else if k == ``compEventClause then
    return { acc with events := acc.events.push { id := ⟨cl[1]⟩, params := cl[2].getArgs.map fun p => (⟨p[1]⟩, ⟨p[3]⟩) } }
  else if k == ``compStartClause then
    return { acc with starts := acc.starts.push ⟨cl[1]⟩ }
  else if k == ``compRouteClause then
    if acc.route?.isSome then throwErrorAt cl "duplicate `route` clause in component"
    let rField : Ident := if cl[1].getNumArgs == 1 then ⟨cl[1][0]⟩ else mkIdentFrom cl `route
    let rTy : Term := ⟨cl[3]⟩; let rInit : Term := ⟨cl[5]⟩
    return { acc with
      route? := some { field := rField, ty := rTy, init := rInit, alts := cl[6].getArgs }
      states := acc.states.push { id := rField, ty? := some rTy, def? := some rInit } }
  else if k == ``compPortOutClause || k == ``compPortInClause then
    let pId : Ident := ⟨cl[1]⟩
    if pId.getId.toString.startsWith "__" then
      throwErrorAt pId s!"port name '{pId.getId}' is reserved (names starting with `__`)"
    if k == ``compPortOutClause then
      return { acc with portOuts := acc.portOuts.push { id := pId, ty := ⟨cl[3]⟩ } }
    else
      let g? := if cl[7].getNumArgs == 2 then some ⟨cl[7][1]⟩ else none
      return { acc with portIns := acc.portIns.push { id := pId, argId := ⟨cl[3]⟩, argTy := ⟨cl[5]⟩, guard? := g?, body := cl[9] } }
  else if k == ``compQueryClause then
    let qId : Ident := ⟨cl[1]⟩; let qTy : Term := ⟨cl[3]⟩
    let qStateTy ← `(Cached $qTy)
    let qStateDef ← `({})
    return { acc with
      states := acc.states.push { id := qId, ty? := some qStateTy, def? := some qStateDef }
      queries := acc.queries.push { id := qId, ty := qTy, keyExpr := ⟨cl[6]⟩, urlExpr := ⟨cl[9]⟩ } }
  else if k == ``compActionClause then
    return { acc with actions := acc.actions.push cl }
  else if k == ``compInvariantClause || k == ``compForEachInvClause then
    return { acc with invariants := acc.invariants.push cl }
  else
    return acc

def parseComponentSpec (stx : Syntax) : CommandElabM ComponentSpec := do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if stx[0].getNumArgs == 1 then some ⟨stx[0][0]⟩ else none
  let t : Ident := ⟨stx[2]⟩
  let mut acc : SpecParseAcc := {}
  for cl in stx[4].getArgs do
    acc ← parseCompClause acc cl
  let invariants := acc.invariants ++ stx[8].getArgs
  let fieldNames := acc.states.map (·.id.getId)
  let allDeclNames := fieldNames ++ acc.props.map (·.id.getId) ++ acc.binds.map (·.id.getId) ++
    acc.slots.map (·.id.getId) ++ acc.events.map (·.id.getId) ++ acc.portOuts.map (·.id.getId)
  if allDeclNames.toList.eraseDups.length != allDeclNames.size then
    throwErrorAt t "component fields and events must have distinct names"
  let outTy? : Option Term :=
    if !acc.events.isEmpty || !acc.binds.isEmpty then some (mkIdent (t.getId ++ `Out)) else none
  if let some kf := acc.keyF? then
    unless fieldNames.contains kf.getId.eraseMacroScopes do
      throwErrorAt kf "`key {kf.getId}`: not a `state` field of this component (fields: {fieldNames.toList})"
    if outTy?.isSome then
      throwErrorAt kf "`key` marks the row identity for parent-owned use, and a parent-owned child's `event` output would have no receiver; drop one of the two"
  return {
    doc?, t,
    collections := acc.collections, states := acc.states, ephemeralFields := acc.ephemeralFields,
    props := acc.props, binds := acc.binds, slots := acc.slots, hasChildren := acc.hasChildren,
    events := acc.events, hasProps := !acc.props.isEmpty || !acc.binds.isEmpty,
    keyF? := acc.keyF?, outTy?, route? := acc.route?, starts := acc.starts,
    portOuts := acc.portOuts, portIns := acc.portIns, queries := acc.queries,
    actions := acc.actions, invariants, body := ⟨stx[7]⟩
  }

def collectSitesAndRewriteStateful (spec : ComponentSpec) :
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

end CompElab
end Qed
