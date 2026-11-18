import Qed.Component.Syntax
import Qed.Resource
import Qed.Schema

namespace Qed
section CompElab
open Lean Elab Command

syntax (name := qedCheckRpcCallTerm) "qedCheckRpcCall% " ident ident "[" term,* "]" term : term

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
  sessionField?   : Option Ident := none
  usedRpcs        : Array (String × String) := #[]

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
  usedRpcs    : IO.Ref (Array (String × String))
  contCounter : IO.Ref Nat

def recordUsedRpc (ref : IO.Ref (Array (String × String))) (srv : String) (m : String) : IO Unit := do
  let cur ← ref.get
  unless cur.contains (srv, m) do
    ref.set (cur.push (srv, m))

def checkRecordRpcIdent (ctx : RewriteCtx) (id : Name) : CommandElabM Unit := do
  let shouldCheck := ctx.inPerform || match id.eraseMacroScopes with | .str p _ => !p.isAnonymous | _ => false
  if shouldCheck then
    let openDecls := (← getScope).openDecls
    if let some (srvInfo, mInfo) := lookupServerMethod? (← getEnv) (← getCurrNamespace) openDecls id then
      recordUsedRpc ctx.usedRpcs srvInfo.shortName mInfo.name

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
  else if stx.isIdent then
    checkRecordRpcIdent ctx stx.getId
    return stx
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
  sessionField?   : Option Ident := none

private def requireTyOrDef (role : Name) (fId : Ident) (ty? d? : Option Term) : CommandElabM Unit := do
  if ty?.isNone && d?.isNone then
    throwErrorAt fId s!"`{role} {fId.getId}` needs a type (`: Type`), a default (`:= value`), or both"

private def parseCompClause (acc : SpecParseAcc) (cl : Syntax) : CommandElabM SpecParseAcc := do
  let k := cl.getKind
  if k == ``compSessionClause then
    if acc.sessionField?.isSome then
      throwErrorAt cl "duplicate `session` clause in component"
    let sfId : Ident := ⟨cl[1]⟩
    let sfTy : Term ← if cl[2].getNumArgs == 2 then pure ⟨cl[2][1]⟩ else `(Option String)
    let sfDef : Term ← `(none)
    return { acc with
      sessionField? := some sfId
      states := acc.states.push { id := sfId, ty? := some sfTy, def? := some sfDef } }
  else if k == ``compFieldClause then
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
    actions := acc.actions, invariants, body := ⟨stx[7]⟩,
    sessionField? := acc.sessionField?
  }

private def packSeq (refStx : Syntax) (stmts : Array Syntax) : Syntax :=
  let info := SourceInfo.fromRef refStx
  if stmts.isEmpty then
    Syntax.node info ``actionNoopStmt #[Syntax.atom info "(", Syntax.atom info ")"]
  else
    let tail := stmts.toList.drop 1 |>.toArray.map fun st => Syntax.node info nullKind #[st]
    Syntax.node info `Qed.compStmtSeq #[stmts[0]!, Syntax.node info nullKind tail]

private partial def collectPatIds (stx : Syntax) : Array Name :=
  match stx with
  | .ident _ _ v _ =>
      let vn := v.eraseMacroScopes
      if vn.isAtomic && vn.toString != "_" && !vn.toString.front.isUpper then #[vn] else #[]
  | .node _ k args =>
      if k == ``Lean.Parser.Term.dotIdent || k == ``Lean.Parser.Term.hole then #[]
      else if k == ``Lean.Parser.Term.app && args.size ≥ 2 then collectPatIds args[1]!
      else args.flatMap collectPatIds
  | _ => #[]

private inductive CatchPatKind
  | wildcard
  | dotTag (tag : String) (binder? : Option Term)

private def classifyCatchAlt (validTags : Array String) (isOption : Bool) (alt : Syntax) :
    CommandElabM (CatchPatKind × Array Syntax) := do
  let pats := alt[1].getSepArgs
  if pats.size != 1 then
    throwErrorAt alt "each `catch` arm must match a single pattern (`| .tag => ...`, `| .tag err => ...`, `| .failed err => ...`, or `| _ => ...`)"
  let pat := pats[0]!
  let body := unpackSeq alt[3]
  if pat.getKind == ``Lean.Parser.Term.hole then
    return (.wildcard, body)
  let checkTag (tagRef : Syntax) (tag : String) (binder? : Option Term) : CommandElabM (CatchPatKind × Array Syntax) := do
    if tag == "failed" then
      return (.dotTag "failed" binder?, body)
    if tag == "none" then
      unless isOption do
        throwErrorAt tagRef "`.none` catch arm is only valid when the awaited RPC returns an `Option` (`T?`)"
      if binder?.isSome then
        throwErrorAt tagRef "`.none` takes no error message argument"
      return (.dotTag "none" none, body)
    unless validTags.contains tag do
      let validStr := if validTags.isEmpty then ".failed" else
        String.intercalate ", " (validTags.toList.map (s!".{·}") ++ [".failed"])
      throwErrorAt tagRef s!"unknown error tag `.{tag}` in `catch` (valid patterns: {validStr})"
    return (.dotTag tag binder?, body)
  if pat.getKind == ``Lean.Parser.Term.dotIdent then
    return ← checkTag pat pat[1].getId.toString none
  if pat.getKind == ``Lean.Parser.Term.app && pat[0].getKind == ``Lean.Parser.Term.dotIdent then
    let args := pat[1].getArgs
    if args.size == 1 then
      let b : Term := ⟨args[0]!⟩
      unless b.raw.isIdent || b.raw.getKind == ``Lean.Parser.Term.hole do
        throwErrorAt b "error message pattern in `catch` must be an identifier or `_`"
      return ← checkTag pat[0] pat[0][1].getId.toString (some b)
  throwErrorAt pat "unsupported `catch` pattern; expected `.tag`, `.tag msg`, `.failed err`, `.none`, or `_`"

private def inferAwaitBinderTy? (mInfo : ServerMethodInfo) (hasCatchNone : Bool) :
    CommandElabM (Option Term) := do
  if mInfo.outcomeConst == .anonymous then return none
  let savedMsgs := (← get).messages
  try
    liftTermElabM do
      let some (.defnInfo dinfo) := (← getEnv).find? mInfo.outcomeConst | return none
      Meta.lambdaTelescope dinfo.value fun _ body => do
        let mut ty ← Meta.whnf body
        if ty.isAppOfArity ``Qed.RpcOutcome 2 || ty.isAppOfArity ``Qed.RpcSimpleOutcome 1 then
          ty ← Meta.whnf ty.appArg!
        if mInfo.isOption && ty.isAppOfArity ``Option 1 then
          let optInner ← Meta.whnf ty.appArg!
          let unwrapped := if optInner.isAppOfArity ``Qed.Ensured 2 then optInner.appFn!.appArg! else optInner
          if hasCatchNone then
            ty := unwrapped
          else
            ty ← Meta.mkAppM ``Option #[unwrapped]
        else if ty.isAppOfArity ``Qed.Ensured 2 then
          ty := ty.appFn!.appArg!
        if ty.hasLooseBVars then return none
        return some (← PrettyPrinter.delab ty)
  catch _ =>
    modify fun s => { s with messages := savedMsgs }
    return none

private partial def stmtContainsAwait (st : Syntax) : Bool :=
  let k := st.getKind
  k == ``actionLetAwaitStmt || k == ``actionAssignAwaitStmt || st.getArgs.any stmtContainsAwait

private def resolveRpcForAwait (ctx : RewriteCtx) (rpcId : Ident) (argCount : Nat) :
    CommandElabM (ServerInfo × ServerMethodInfo) := do
  let openDecls := (← getScope).openDecls
  let some (srvInfo, mInfo) := lookupServerMethod? (← getEnv) (← getCurrNamespace) openDecls rpcId.getId
    | throwErrorAt rpcId s!"unknown server RPC `{rpcId.getId}` in `await`"
  if argCount != mInfo.paramCount then
    throwErrorAt rpcId s!"`{rpcId.getId}` expects {mInfo.paramCount} argument(s), got {argCount}"
  recordUsedRpc ctx.usedRpcs srvInfo.shortName mInfo.name
  return (srvInfo, mInfo)

private partial def liftAwaitStmts (ctx : RewriteCtx) (outerParams : Array (Ident × Term))
    (localLetNames : Array Name) (stmts : Array Syntax) : CommandElabM (Array Syntax) := do
  go outerParams localLetNames stmts.toList
where
  go (outerParams : Array (Ident × Term)) (localNames : Array Name) : List Syntax → CommandElabM (Array Syntax)
  | [] => return #[]
  | st :: rest => do
      let info := SourceInfo.fromRef st
      let mkLetSt (id : Ident) (ty? : Option Term) (rhs : Syntax) : Syntax :=
        let tyNode := match ty? with
          | some ty => Syntax.node info nullKind #[Syntax.atom info ":", ty.raw]
          | none    => Syntax.node info nullKind #[]
        Syntax.node info ``actionLetStmt #[Syntax.atom info "let ", id, tyNode, Syntax.atom info ":=", rhs]
      let k := st.getKind
      if k == ``actionLetStmt then
        let lId : Ident := ⟨st[1]⟩
        let ln := lId.getId.eraseMacroScopes
        let (outer', locals') ←
          if st[2].getNumArgs == 2 then
            pure (outerParams.filter (·.1.getId.eraseMacroScopes != ln) |>.push (lId, ⟨st[2][1]⟩), localNames)
          else
            pure (outerParams.filter (·.1.getId.eraseMacroScopes != ln), localNames.push ln)
        let tail ← go outer' locals' rest
        return #[st] ++ tail

      if k == ``actionAssignAwaitStmt then
        let fId := st[0]
        let fname := fId.getId.eraseMacroScopes
        checkMutableField ctx fId s!"`{fname} := await ...`" fname
        let rpcId : Ident := ⟨st[3]⟩
        let rawArgs : Array Term := st[5].getSepArgs.map (⟨·⟩)
        let (srvInfo, mInfo) ← resolveRpcForAwait ctx rpcId rawArgs.size
        let setterCtor ← registerSite ctx.sites #[(fname, none)] none
        let cbTerm : Term := mkIdentFrom st (ctx.msgPath ++ setterCtor)
        let srvId := mkIdentFrom rpcId srvInfo.serverName
        let methId := mkIdentFrom rpcId (Name.mkSimple mInfo.name)
        let loadingRHS ← `(Qed.Resource.loading)
        let assignSt := Syntax.node info ``actionAssignStmt #[fId, Syntax.atom info ":=", loadingRHS.raw]
        let callTerm ← `(qedCheckRpcCall% $srvId:ident $methId:ident [$[$rawArgs:term],*] $cbTerm)
        let perfSt := Syntax.node info ``actionPerformStmt #[Syntax.atom info "perform", callTerm.raw]
        let tail ← go outerParams localNames rest
        return #[assignSt, perfSt] ++ tail

      if k == ``actionLetAwaitStmt then
        let xId : Ident := ⟨st[1]⟩
        let optTy? : Option Term := if st[2].getNumArgs == 2 then some ⟨st[2][1]⟩ else none
        let rpcId : Ident := ⟨st[5]⟩
        let rawArgs : Array Term := st[7].getSepArgs.map (⟨·⟩)
        let (srvInfo, mInfo) ← resolveRpcForAwait ctx rpcId rawArgs.size
        let catchAlts := if st[9].getNumArgs == 2 then st[9][1].getArgs else #[]
        let parsedCatch ← catchAlts.mapM (classifyCatchAlt mInfo.domainErrTags mInfo.isOption)

        let hasWildcard := parsedCatch.any fun (pk, _) => pk matches .wildcard
        let hasTag (t : String) := parsedCatch.any fun (pk, _) =>
          match pk with | .dotTag t' _ => t' == t | _ => false
        unless mInfo.domainErrTags.isEmpty || hasWildcard do
          let missing := mInfo.domainErrTags.filter (!hasTag ·)
          unless missing.isEmpty do
            let missStr := String.intercalate ", " (missing.toList.map (s!".{·}"))
            throwErrorAt st s!"`await {rpcId.getId}(...)` has unhandled domain error(s): {missStr}; handle them with `catch | .tag => ...`"

        let restArr := rest.toArray
        let capturedOuter := outerParams.filter fun (pId, _) =>
          let pn := pId.getId.eraseMacroScopes
          restArr.any (mentionsIdent · pn) ||
          catchAlts.any (mentionsIdent · pn) ||
          rawArgs.any (mentionsIdent ·.raw pn)

        let kIdx ← ctx.contCounter.get
        ctx.contCounter.set (kIdx + 1)
        let contCtor := Name.mkSimple s!"_cont_{kIdx}"

        let mut contParams : Array (Ident × Term) := capturedOuter
        let mut callArgs : Array Term := capturedOuter.map (⟨·.1.raw⟩)
        let mut preLetStmts : Array Syntax := #[]
        let mut ensArgs : Array Term := #[]
        let mut rpcCallArgs : Array Term := #[]

        for (argT, i) in rawArgs.zipIdx do
          let mentionsUncaptured :=
            ctx.stateFields.any (mentionsIdent argT.raw) ||
            ctx.bindFields.any (mentionsIdent argT.raw) ||
            localNames.any (mentionsIdent argT.raw)
          if mInfo.hasEnsures && mentionsUncaptured then
            let tmpId := mkIdentFrom argT.raw (Name.mkSimple s!"_rpcArg_{kIdx}_{i}")
            let paramTyId := mkIdentFrom argT.raw mInfo.paramTypeConsts[i]!
            preLetStmts := preLetStmts.push (mkLetSt tmpId (some paramTyId) argT.raw)
            contParams := contParams.push (tmpId, paramTyId)
            callArgs := callArgs.push tmpId
            ensArgs := ensArgs.push tmpId
            rpcCallArgs := rpcCallArgs.push tmpId
          else
            ensArgs := ensArgs.push argT
            rpcCallArgs := rpcCallArgs.push argT

        let outTyTerm : Term ← do
          let outId := mkIdentFrom rpcId mInfo.outcomeConst
          if mInfo.hasEnsures then
            ensArgs.foldlM (init := (outId : Term)) fun acc a => `($acc $a)
          else
            pure (outId : Term)
        let outVarId := mkIdentFrom st (Name.mkSimple s!"_qedOut_{kIdx}")
        contParams := contParams.push (outVarId, outTyTerm)

        let catchHasNone := parsedCatch.any fun (pk, _) => pk matches .dotTag "none" _
        let xBinderTy? ← match optTy? with
          | some t => pure (some t)
          | none   => inferAwaitBinderTy? mInfo catchHasNone
        let xn := xId.getId.eraseMacroScopes
        let nextOuter := match xBinderTy? with
          | some xTy => (outerParams.filter (·.1.getId.eraseMacroScopes != xn)).push (xId, xTy)
          | none     => outerParams.filter (·.1.getId.eraseMacroScopes != xn)
        let nextLocals := if xBinderTy?.isSome then localNames else localNames.push xn
        let restLifted ← go nextOuter nextLocals rest

        let mut okBody := restLifted
        if let some oTy := optTy? then
          okBody := #[mkLetSt xId (some oTy) xId] ++ okBody

        let outcomePrefix := if mInfo.domainErrTags.isEmpty then `Qed.RpcSimpleOutcome else `Qed.RpcOutcome
        let okCtor := mkIdent (outcomePrefix ++ `ok)
        let okPat : Term ←
          if mInfo.isOption && !catchHasNone && mInfo.hasEnsures then
            let optVar := mkIdentFrom xId (Name.mkSimple s!"_qedOpt_{kIdx}")
            okBody := #[mkLetSt xId none (← `(($optVar).map Qed.Ensured.val)).raw] ++ okBody
            `($okCtor $optVar:ident)
          else
            let inner ← if mInfo.hasEnsures then `(Qed.Ensured.mk $xId:ident $(mkIdent `_qed_ens)) else pure (xId : Term)
            if mInfo.isOption && catchHasNone then `($okCtor (some $inner)) else `($okCtor $inner)

        let mkMatchAltStx (patT : Term) (bStmts : Array Syntax) : Syntax :=
          Syntax.node info ``compMatchAlt
            #[Syntax.atom info "| ", Syntax.node info nullKind #[patT.raw], Syntax.atom info " => ", packSeq st bStmts]

        let mut matchAlts : Array Syntax := #[mkMatchAltStx okPat okBody]
        let mut wildcardAlts : Array Syntax := #[]
        let mut coveredFailed := false
        let mut coveredNone := false
        for (pk, bodyRaw) in parsedCatch do
          let mut bOuter := outerParams
          let mut bLocals := localNames
          match pk with
          | .wildcard =>
              let bLifted ← go bOuter bLocals bodyRaw.toList
              wildcardAlts := wildcardAlts.push (mkMatchAltStx (← `(_)) bLifted)
          | .dotTag tag bOpt? =>
              if let some b := bOpt? then
                if b.raw.isIdent then
                  let bn := b.raw.getId.eraseMacroScopes
                  bOuter := (bOuter.filter (·.1.getId.eraseMacroScopes != bn)).push (⟨b.raw⟩, ← `(String))
              let bLifted ← go bOuter bLocals bodyRaw.toList
              let patTerm : Term ←
                if tag == "failed" then
                  coveredFailed := true
                  let msgPat ← bOpt?.getDM `(_)
                  `($(mkIdent (outcomePrefix ++ `failed)) $msgPat)
                else if tag == "none" then
                  coveredNone := true
                  `($(mkIdent (outcomePrefix ++ `ok)) none)
                else
                  let tagDot : Term := ⟨Syntax.node info ``Lean.Parser.Term.dotIdent #[Syntax.atom info ".", mkIdentFrom st (Name.mkSimple tag)]⟩
                  let msgPat ← bOpt?.getDM `(_)
                  `($(mkIdent (outcomePrefix ++ `err)) $tagDot $msgPat)
              matchAlts := matchAlts.push (mkMatchAltStx patTerm bLifted)
        matchAlts := matchAlts ++ wildcardAlts
        if wildcardAlts.isEmpty && (!coveredFailed || (mInfo.isOption && !coveredNone)) then
          matchAlts := matchAlts.push (mkMatchAltStx (← `(_)) #[Syntax.node info ``actionNoopStmt #[Syntax.atom info "(", Syntax.atom info ")"]])

        let matchSt := Syntax.node info ``actionMatchStmt
          #[Syntax.atom info "match", Syntax.node info nullKind #[outVarId], Syntax.atom info " with ",
            Syntax.node info nullKind matchAlts]
        let curSites ← ctx.sites.get
        ctx.sites.set (curSites.push {
          key := s!"cont:{contCtor}"
          ctor := contCtor
          params := contParams
          stmts? := some #[matchSt]
        })

        let cbCtor := mkIdentFrom st (ctx.msgPath ++ contCtor)
        let cbTerm ← callArgs.foldlM (init := (cbCtor : Term)) fun acc a => `($acc $a)
        let srvId := mkIdentFrom rpcId srvInfo.serverName
        let methId := mkIdentFrom rpcId (Name.mkSimple mInfo.name)
        let callTerm ← `(qedCheckRpcCall% $srvId:ident $methId:ident [$[$rpcCallArgs:term],*] $cbTerm)
        let perfSt := Syntax.node info ``actionPerformStmt #[Syntax.atom info "perform", callTerm.raw]
        return preLetStmts.push perfSt

      if (k == ``actionIfStmt || k == ``actionIfLetStmt || k == ``actionMatchStmt) && stmtContainsAwait st then
        unless rest.isEmpty || hasReturnStmt st do
          throwErrorAt st "statements after an `if`/`match` containing `await` are not supported unless the branch `return`s; move trailing statements inside the branches"
        let tailIfReturn := if hasReturnStmt st then rest else []
        let liftOptElse (eNode : Syntax) : CommandElabM Syntax := do
          if eNode.getNumArgs == 2 then
            let eLifted ← go outerParams localNames ((unpackSeq eNode[1]).toList ++ tailIfReturn)
            pure (Syntax.node eNode.getHeadInfo eNode.getKind #[eNode[0], packSeq st eLifted])
          else
            pure eNode
        if k == ``actionIfStmt then
          let tLifted ← go outerParams localNames ((unpackSeq st[4]).toList ++ tailIfReturn)
          let eOpt ← liftOptElse st[5]
          return #[Syntax.node info k #[st[0], st[1], st[2], st[3], packSeq st tLifted, eOpt]]
        else if k == ``actionIfLetStmt then
          let pIds := collectPatIds st[2]
          let tLocals := localNames ++ pIds.filter fun n => !(outerParams.any (·.1.getId.eraseMacroScopes == n))
          let tLifted ← go outerParams tLocals ((unpackSeq st[6]).toList ++ tailIfReturn)
          let eOpt ← liftOptElse st[7]
          return #[Syntax.node info k #[st[0], st[1], st[2], st[3], st[4], st[5], packSeq st tLifted, eOpt]]
        else
          let alts' ← st[3].getArgs.mapM fun alt => do
            let pIds := alt[1].getSepArgs.flatMap collectPatIds
            let aLocals := localNames ++ pIds.filter fun n => !(outerParams.any (·.1.getId.eraseMacroScopes == n))
            let aLifted ← go outerParams aLocals ((unpackSeq alt[3]).toList ++ tailIfReturn)
            pure (Syntax.node alt.getHeadInfo alt.getKind #[alt[0], alt[1], alt[2], packSeq st aLifted])
          return #[Syntax.node info k #[st[0], st[1], st[2], Syntax.node st[3].getHeadInfo st[3].getKind alts']]

      let tail ← go outerParams localNames rest
      return #[st] ++ tail

def collectSitesAndRewriteStateful (spec : ComponentSpec) :
    CommandElabM (Array SetSite × Option RouteDecl × Array QueryDecl × Array Term × Term × Array HoistedSub × Array (String × String)) := do
  let sitesRef    ← IO.mkRef (#[] : Array SetSite)
  let hoistedRef  ← IO.mkRef (#[] : Array HoistedSub)
  let usedRpcsRef ← IO.mkRef (#[] : Array (String × String))
  let contCtrRef  ← IO.mkRef (0 : Nat)
  let baseCtx : RewriteCtx := {
    stateFields := spec.fieldNames, bindFields := spec.bindNames,
    actionNames := spec.actions.map (·[1].getId) ++ spec.portIns.map (·.id.getId),
    isPureComp := false, msgPath := spec.t.getId ++ `Msg, hasOut := spec.outTy?.isSome,
    collections := spec.collections, sites := sitesRef, hoisted := hoistedRef,
    usedRpcs := usedRpcsRef, contCounter := contCtrRef
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
    let stmtsRaw := unpackSeq (← rewriteIn baseCtx false a[5])
    let stmts ← liftAwaitStmts baseCtx params #[] stmtsRaw
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
    let stmtsRaw := unpackSeq (← rewriteIn baseCtx false p.body)
    let stmts ← liftAwaitStmts baseCtx #[(p.argId, p.argTy)] #[] stmtsRaw
    let cur ← sitesRef.get
    sitesRef.set (cur.push {
      key := s!"port:{name}", ctor := name, params := #[(p.argId, p.argTy)], guard?, stmts? := some stmts })
  let route'? ← spec.route?.mapM fun rd => do
    let alts' ← rd.alts.mapM fun alt => do
      let rwBody ← rewriteIn baseCtx false alt[3]
      let patIds := alt[1].getSepArgs.flatMap collectPatIds
      let lifted ← liftAwaitStmts baseCtx #[] patIds (unpackSeq rwBody)
      pure (Syntax.node .none alt.getKind #[alt[0], alt[1], alt[2], packSeq alt lifted])
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
  return (← sitesRef.get, route'?, queries', starts', body', ← hoistedRef.get, ← usedRpcsRef.get)

end CompElab
end Qed
