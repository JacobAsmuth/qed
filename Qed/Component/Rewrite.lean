import Qed.Component.Syntax
import Qed.Resource
import Qed.Schema

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

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

structure ResetFormSub where
  ctorName   : Name
  draftField : Ident
  schemaName : Name
  parseCall  : Term
  resetCond  : Term
  handler    : Term

structure SetSite where
  key      : String
  ctor     : Name
  params   : Array (Ident × Term) := #[]
  whenPat? : Option (Term × Term) := none
  guard?   : Option Term := none
  assigns  : Array (Name × Option Term) := #[]
  send?    : Option Term := none
  stmts?   : Option (Array Syntax) := none

structure PortOutDecl where
  id : Ident
  ty : Term

structure PortInDecl where
  id       : Ident
  argId    : Ident
  argTy    : Term
  whenPat? : Option (Syntax × Syntax) := none
  guards   : Array Syntax := #[]
  body     : Syntax

structure RpcQuerySpec where
  rpcRef        : Ident
  srvInfo       : ServerInfo
  mInfo         : ServerMethodInfo
  args          : Array Term
  whenPat?      : Option (Term × Term × Array Name)
  whenGuards    : Array Term
  hasMsgEnsured : Bool
deriving Inhabited

inductive QuerySource where
  | url (keyExpr : Term) (urlExpr : Term)
  | rpc (spec : RpcQuerySpec)
deriving Inhabited

structure QueryDecl where
  id     : Ident
  ty     : Term
  msgTy  : Term
  source : QuerySource
deriving Inhabited

def QueryDecl.ctorName (q : QueryDecl) : Name :=
  Name.mkSimple s!"_query_{q.id.getId}"

def lowerCompExpr (mode : Qed.Lang.ExprMode) (stx : Syntax) : CommandElabM Term := do
  if mode == .val then
    return (← liftMacroM (Qed.Jsx.expandJsxExpr "" none (`(())) stx)).1
  else
    liftMacroM (Qed.Lang.lowerSimpleQedExpr mode stx)

def lowerCompGuards (guards : Array Syntax) : CommandElabM (Option Term) := do
  if guards.isEmpty then return none
  let ts ← guards.mapM (lowerCompExpr .propGuard)
  match ts.toList with
  | []      => return none
  | c :: cs => some <$> cs.foldlM (init := c) fun acc x => `($acc ∧ $x)

def parseCompWhen (optWhen : Syntax) : Option (Syntax × Syntax) × Array Syntax :=
  if optWhen.getNumArgs == 1 then
    let wBody := optWhen[0][1]
    if wBody.getKind == ``compWhenLet then
      let gs := if wBody[4].getNumArgs == 2 then wBody[4][1].getSepArgs else #[]
      (some (wBody[1], wBody[3]), gs)
    else
      (none, wBody.getSepArgs)
  else
    (none, #[])

def inferAwaitBinderTy? (mInfo : ServerMethodInfo) (hasCatchNone : Bool) :
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
          ty ← if hasCatchNone then pure unwrapped else Meta.mkAppM ``Option #[unwrapped]
        else if ty.isAppOfArity ``Qed.Ensured 2 then
          ty := ty.appFn!.appArg!
        if ty.hasLooseBVars then return none
        return some (← PrettyPrinter.delab ty)
  catch _ =>
    modify fun s => { s with messages := savedMsgs }
    return none

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
  starts          : Array Syntax
  portOuts        : Array PortOutDecl := #[]
  portIns         : Array PortInDecl := #[]
  queries         : Array QueryDecl := #[]
  actions         : Array Syntax
  invariants      : Array Syntax
  body            : Syntax
  hoisted         : Array HoistedSub := #[]
  resetForms      : Array ResetFormSub := #[]
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
    rootTag?    := staticRootTag? spec.body
  }

def desugarAssign (fname : Name) (op : String) (rhs : Term) : CommandElabM Term := do
  let fIdent := mkIdent fname
  match op with
  | "="  => pure rhs
  | "+=" => `(Qed.Lang.QedVal.val $fIdent + Qed.Lang.QedVal.val ($rhs))
  | "-=" => `(Qed.Lang.QedVal.val $fIdent - Qed.Lang.QedVal.val ($rhs))
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
  formDrafts  : IO.Ref (Array FieldDecl)
  resetForms  : IO.Ref (Array ResetFormSub)
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
    throwErrorAt fId s!"`{fname} = ·`: only one `·` placeholder per handler"
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
  if bodyStx.getKind == ``Qed.Jsx.qedExprJsx then
    let el := bodyStx[0]
    let ek := el.getKind
    if ek == ``Qed.Jsx.selfClosing || ek == ``Qed.Jsx.withChildren then
      let attrs := el[2].getArgs
      let hasKey := attrs.any fun a => a.getKind == ``Qed.Jsx.attrNamed && atomStr a[0] == "key"
      if !hasKey then
        let keyVal ← `($(mkIdent (compFullName ++ `keyOf)) $bindId)
        let kids? := if ek == ``Qed.Jsx.withChildren then some el[4] else none
        let el' := rebuildJsxEl el (attrs.push (mkJsxAttrExpr "key" keyVal)) kids?
        return Syntax.node .none ``Qed.Jsx.qedExprJsx #[el']
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

private def isSomeCdot (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx
  u.getKind == ``qedCall &&
  u[0].getKind == ``qedIdent && u[0][0].getId.eraseMacroScopes == `some &&
  u[2].getSepArgs.size == 1 && u[2].getSepArgs[0]!.getKind == ``qedCallArgPos &&
  isCdot u[2].getSepArgs[0]![0]

private def rewriteUpperElement (ctx : RewriteCtx) (inLambda : Bool) (stx : Syntax)
    (tag : String) (rewrittenPairs : Array (Bool × Syntax)) (kids? : Option Syntax)
    (origBindField? : Option Ident := none) : CommandElabM Syntax := do
  let rewrittenAttrs := rewrittenPairs.map (·.2)
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
  let mut pairs := rewrittenPairs
  if tag.endsWith ".Form" then
    if let some sInfo ← liftCoreM (lookupSchemaForm? cName) then
      let schemaFull := sInfo.fullName.getPrefix
      let hasBind := attrNames.contains "bind"
      let mut draftField? := origBindField?
      if !hasBind then
        unless ctx.allowHoist do
          throwErrorAt stx s!"<{tag}> requires `bind=\{draft}` here"
        if inLambda then
          throwErrorAt stx s!"<{tag}> without `bind=` hoists internal draft state and cannot be mounted inside a loop lambda; declare `state draft = ...` and pass `bind=\{draft}`"
        let curFD ← ctx.formDrafts.get
        let fName := Name.mkSimple s!"_form_{curFD.size}"
        let fId := mkIdentFrom stx fName
        let draftTy := mkIdentFrom stx (`_root_ ++ schemaFull ++ `Draft)
        let draftEmpty := mkIdentFrom stx (`_root_ ++ schemaFull ++ `Draft ++ `empty)
        ctx.formDrafts.set (curFD.push { id := fId, ty? := some draftTy, def? := some draftEmpty, ty := draftTy })
        let editCtor ← registerSite ctx.sites #[(fName, none)] none
        let editFn ← wrapUnaryMsg ctx.wrapMsg? ⟨mkIdent (ctx.msgPath ++ editCtor)⟩
        pairs := pairs.push (false, mkJsxAttrExpr "bind" (← `(($fId, $editFn))))
        draftField? := some fId
      if let some (_, resetAttr) := pairs.find? fun (_, a) => a.getKind == ``Qed.Jsx.attrNamed && atomStr a[0] == "reset" then
        unless ctx.allowHoist do
          throwErrorAt resetAttr s!"<{tag}>: `reset` is only supported inside a `component` view"
        if inLambda then
          throwErrorAt stx s!"<{tag}> with `reset` cannot be mounted inside a loop lambda"
        let some dfId := draftField?
          | throwErrorAt stx s!"<{tag} reset>: `reset` requires either omitted `bind` or `bind=\{stateField}`"
        if hasBind && !ctx.stateFields.contains dfId.getId.eraseMacroScopes then
          throwErrorAt stx s!"<{tag} reset>: `reset` requires `bind=\{stateField}` to refer to a `state` field"
        let resetCond : Term ←
          if resetAttr[1].getNumArgs == 0 then `(Bool.true)
          else liftMacroM <| Qed.Jsx.expandAttrVal resetAttr[1] (`(Bool.true))
        let some (_, subAttr) := pairs.find? fun (_, a) => a.getKind == ``Qed.Jsx.attrNamed && atomStr a[0] == "onSubmit"
          | throwErrorAt stx s!"<{tag}> requires `onSubmit=\{...}`"
        unless subAttr[1].getNumArgs == 2 do
          throwErrorAt subAttr s!"<{tag}>: `onSubmit` requires a value"
        let subVal ← liftMacroM <| Qed.Jsx.expandAttrVal subAttr[1] (`(""))
        let handler ← `(($subVal : _ → $(mkIdent ctx.msgPath)))
        let mut ctxProps : Array (Syntax × String × Term) := #[]
        for (_, a) in pairs do
          if a.getKind == ``Qed.Jsx.attrNamed && a[1].getNumArgs == 2 then
            let nm := atomStr a[0]
            if !["key", "bind", "reset", "onSubmit"].contains nm then
              ctxProps := ctxProps.push (a[0], nm, ← liftMacroM <| Qed.Jsx.expandAttrVal a[1] (`("")))
        let ctxArgs ← liftMacroM <| resolveSchemaCtxArgs stx tag sInfo.ctxBinders ctxProps (checkUnknown := false)
        let parseCall ← ctxArgs.foldlM (init := (mkIdent (`_root_ ++ schemaFull ++ `parse) : Term)) fun acc ca => `($acc $ca)
        let curRF ← ctx.resetForms.get
        let ctorName := Name.mkSimple s!"_form_reset_{curRF.size}"
        ctx.resetForms.set (curRF.push { ctorName, draftField := dfId, schemaName := schemaFull, parseCall, resetCond, handler })
        let cid : Term := ⟨mkIdent (ctx.msgPath ++ ctorName)⟩
        let resetMsg ← match ctx.wrapMsg? with | some w => `($w $cid) | none => pure cid
        let resetSub ← `(fun _ => $resetMsg)
        let finalAttrs := pairs.filterMap fun (_, a) =>
          if a.getKind == ``Qed.Jsx.attrNamed then
            let nm := atomStr a[0]
            if nm == "reset" then none
            else if nm == "onSubmit" then some (mkJsxAttrExpr "onSubmit" resetSub)
            else some a
          else some a
        return rebuildJsxEl stx finalAttrs kids?
  let evList : Array (String × Nat) ← do
    if let some cInfo ← liftCoreM (lookupComponent? cName) then
      pure (cInfo.events.map fun sig => (sig.name.toString, sig.arity))
    else if tag.endsWith ".Form" && ctx.wrapMsg?.isSome then
      if (← liftCoreM (lookupSchemaForm? cName)).isSome then pure #[("onSubmit", 1)] else pure #[]
    else pure #[]
  if !evList.isEmpty then
    let msgTy := mkIdent ctx.msgPath
    let attrs' ← pairs.mapM fun (wasAssign, a) => do
      if !wasAssign && a.getKind == ``Qed.Jsx.attrNamed && a[1].getNumArgs == 2 &&
          a[1][1].getKind == ``Qed.Jsx.attrValExpr then
        let aname := atomStr a[0]
        if let some (_, arity) := evList.find? (·.1 == aname) then
          return mkJsxAttrExpr aname (← wrapEventAttr a[1] arity msgTy ctx.wrapMsg?)
      return a
    return rebuildJsxEl stx attrs' kids?
  return rebuildJsxEl stx (pairs.map (·.2)) kids?

partial def rewriteIn (ctx : RewriteCtx) (inLambda : Bool) (stx : Syntax) : CommandElabM Syntax := do
  let parseOptSend (opt : Syntax) : CommandElabM (Option Term) := do
    if opt.getNumArgs != 3 then return none
    unless ctx.hasOut do noEmitsErr opt
    let rw ← rewriteIn ctx inLambda opt[2]
    some <$> lowerCompExpr .val rw
  let k := stx.getKind
  if k == ``qedRawTerm then
    return stx
  else if k == ``qedLam1 || k == ``qedLamN then
    return Syntax.node .none k (← stx.getArgs.mapM (rewriteIn ctx true))
  else if k == ``qedExprFor then
    let bindId : Ident := ⟨stx[1]⟩
    let collRaw := stx[3]
    let collRewritten ← rewriteIn ctx inLambda collRaw
    let mut bodyRewritten ← rewriteIn ctx true stx[5]
    if collRaw.getKind == ``qedIdent then
      let colName := collRaw[0].getId.eraseMacroScopes
      if let some (_, childCompId) := ctx.collections.find? (·.1.getId == colName) then
        if let some cInfo ← liftCoreM (lookupComponent? childCompId.getId) then
          if (← liftCoreM getEnv).contains (cInfo.fullName ++ `keyOf) then
            bodyRewritten ← injectAutoKey bodyRewritten cInfo.fullName bindId
    return Syntax.node .none k #[stx[0], stx[1], stx[2], collRewritten, stx[4], bodyRewritten]
  else if k == ``qedStmtPerform then
    return Syntax.node .none k #[stx[0], ← rewriteIn { ctx with inPerform := true } inLambda stx[1]]
  else if ctx.inPerform && k == ``qedDotIdent then
    let actId := stx[1].getId.eraseMacroScopes
    if ctx.actionNames.contains actId then
      return mkRawExpr (mkIdentFrom stx (ctx.msgPath ++ actId))
    else return stx
  else if k == ``qedFieldSetter then
    let fname := stx[1].getId.eraseMacroScopes
    checkMutableField ctx stx[1] s!"`({fname} = ·)`" fname
    return mkRawExpr (← mkSetterHandler ctx fname)
  else if k == ``qedSendExpr then
    unless ctx.hasOut do noEmitsErr stx
    let rw ← rewriteIn ctx inLambda stx[1]
    let argT ← lowerCompExpr .val rw
    return mkRawExpr (← mkSiteExpr ctx #[] (some argT))
  else if k == ``Qed.Jsx.attrValAssign then
    let mut assigns := #[]
    let more := stx[4].getArgs.map fun m =>
      let it := if m.getKind == `Qed.Jsx.jsxAssignItem then m else m[m.getNumArgs - 1]!
      (it[0], atomStr it[1], it[2])
    let op0 := atomStr stx[2]
    if more.isEmpty && stx[5].getNumArgs != 3 && op0 == "=" && isSomeCdot stx[3] then
      let fId := stx[1]
      let fname := fId.getId.eraseMacroScopes
      checkMutableField ctx fId s!"`{fname}`" fname
      let setter ← mkSiteExpr ctx #[(fname, none)] none
      return mkJsxAttrValNode (← `(fun _v => $setter (some _v)))
    for (fId, op, rhsRaw) in #[(stx[1], op0, stx[3])] ++ more do
      let fname := fId.getId.eraseMacroScopes
      let expr? ← if op == "=" && isCdot rhsRaw then pure none
        else do
          let rw ← rewriteIn ctx inLambda rhsRaw
          let rhsT ← lowerCompExpr .val rw
          some <$> desugarAssign fname op rhsT
      assigns ← pushHandlerAssign ctx assigns fId expr?
    return mkJsxAttrValNode (← mkSiteExpr ctx assigns (← parseOptSend stx[5]))
  else if k == ``Qed.Jsx.attrNamed && (atomStr stx[0]).startsWith "bind" &&
      stx[1].getNumArgs == 2 && stx[1][1].getKind == ``Qed.Jsx.attrValExpr then
    let attrName := atomStr stx[0]
    let inner := stx[1][1]
    if (attrName == "bind" || attrName.startsWith "bind:") &&
        inner[1].getKind == ``qedIdent then
      let fId : Ident := ⟨inner[1][0]⟩
      let fname := fId.getId.eraseMacroScopes
      checkMutableField ctx fId s!"`{attrName}=\{{fname}}`" fname
      let pairT ← `(($fId, $(← mkSetterHandler ctx fname)))
      return Syntax.node .none stx.getKind #[stx[0], Syntax.node .none stx[1].getKind #[stx[1][0], mkJsxAttrValNode pairT]]
    return Syntax.node .none k (← stx.getArgs.mapM (rewriteIn ctx inLambda))
  else if k == ``Qed.Jsx.selfClosing || k == ``Qed.Jsx.withChildren then
    let tag := atomStr stx[1]
    let kids? ← if k == ``Qed.Jsx.withChildren then some <$> rewriteIn ctx inLambda stx[4] else pure none
    let rawAttrs := stx[2].getArgs
    let isForm := !tag.isEmpty && tag.front.isUpper && tag.endsWith ".Form"
    let hasReset := isForm && rawAttrs.any fun a =>
      a.getKind == ``Qed.Jsx.attrNamed && atomStr a[0] == "reset"
    let origBindField? : Option Ident :=
      if isForm then rawAttrs.findSome? fun a =>
        if a.getKind == ``Qed.Jsx.attrNamed && atomStr a[0] == "bind" &&
            a[1].getNumArgs == 2 && a[1][1].getKind == ``Qed.Jsx.attrValExpr then
          let inner := a[1][1][1]
          if inner.getKind == ``qedIdent then some ⟨inner[0]⟩ else none
        else none
      else none
    let rewrittenPairs ← rawAttrs.mapM fun a => do
      let wasAssign := a.getKind == ``Qed.Jsx.attrNamed && a[1].getNumArgs == 2 &&
        a[1][1].getKind == ``Qed.Jsx.attrValAssign
      let aCtx := if hasReset && a.getKind == ``Qed.Jsx.attrNamed && atomStr a[0] == "onSubmit" then
        { ctx with wrapMsg? := none } else ctx
      return (wasAssign, ← rewriteIn aCtx inLambda a)
    if tag.isEmpty || !tag.front.isUpper then
      return ← rewriteLowerElement ctx stx rewrittenPairs kids?
    return ← rewriteUpperElement ctx inLambda stx tag rewrittenPairs kids? origBindField?
  else if k == ``qedIdent then
    checkRecordRpcIdent ctx stx[0].getId
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
  starts          : Array Syntax := #[]
  portOuts        : Array PortOutDecl := #[]
  portIns         : Array PortInDecl := #[]
  queries         : Array QueryDecl := #[]
  actions         : Array Syntax := #[]
  invariants      : Array Syntax := #[]
  sessionField?   : Option Ident := none
  rawStateTys     : Array (Ident × Option Syntax) := #[]

private def requireTyOrDef (role : Name) (fId : Ident) (ty? d? : Option Term) : CommandElabM Unit := do
  if ty?.isNone && d?.isNone then
    throwErrorAt fId s!"`{role} {fId.getId}` needs a type (`: Type`), a default (`= value`), or both"

private def parseCompClause (acc : SpecParseAcc) (cl : Syntax) : CommandElabM SpecParseAcc := do
  let k := cl.getKind
  if k == ``compSessionClause then
    if acc.sessionField?.isSome then
      throwErrorAt cl "duplicate `session` clause in component"
    let sfId : Ident := ⟨cl[1]⟩
    let sfTy : Term ← if cl[2].getNumArgs == 2 then liftMacroM (return (← lowerQedType cl[2][1] false).1) else `(Option String)
    let sfDef : Term ← `(none)
    return { acc with
      sessionField? := some sfId
      states := acc.states.push { id := sfId, ty? := some sfTy, def? := some sfDef }
      rawStateTys := acc.rawStateTys.push (sfId, none) }
  else if k == ``compFieldClause then
    let role := cl[0].getId
    let fId : Ident := ⟨cl[1]⟩
    let rawTy? : Option Syntax := if cl[2].getNumArgs == 2 then some cl[2][1] else none
    let ty? : Option Term ← rawTy?.mapM fun rt => liftMacroM (return (← lowerQedType rt false).1)
    let d?  : Option Term ← if cl[3].getNumArgs == 2 then some <$> lowerCompExpr .val cl[3][1] else pure none
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
          states := acc.states.push { id := fId, ty? := some fTy, def? := some fDef }
          rawStateTys := acc.rawStateTys.push (fId, none) }
    | _ =>
        requireTyOrDef role fId ty? d?
        let eph := if role == `ephemeral then acc.ephemeralFields.push fId else acc.ephemeralFields
        return { acc with
          states := acc.states.push { id := fId, ty?, def? := d? }
          rawStateTys := acc.rawStateTys.push (fId, rawTy?)
          ephemeralFields := eph }
  else if k == ``compChildrenClause then
    return { acc with hasChildren := true }
  else if k == ``compKeyClause then
    if acc.keyF?.isSome then throwErrorAt cl "duplicate `key` clause in component"
    return { acc with keyF? := some ⟨cl[1]⟩ }
  else if k == ``compEventClause then
    let rawParams := if cl[2].getNumArgs == 3 then cl[2][1].getSepArgs else #[]
    let params ← rawParams.mapM fun p => return (⟨p[0]⟩, ← liftMacroM (return (← lowerQedType p[2] false).1))
    return { acc with events := acc.events.push { id := ⟨cl[1]⟩, params } }
  else if k == ``compStartClause then
    return { acc with starts := acc.starts.push cl[1] }
  else if k == ``compRouteClause then
    if acc.route?.isSome then throwErrorAt cl "duplicate `route` clause in component"
    let rField : Ident := if cl[1].getNumArgs == 1 then ⟨cl[1][0]⟩ else mkIdentFrom cl `route
    let rTy : Term ← liftMacroM (return (← lowerQedType cl[3] false).1)
    let rInit : Term ← lowerCompExpr .val cl[5]
    let rAlts : Array Syntax := if cl[6].getNumArgs == 2 then cl[6][1].getArgs else #[]
    return { acc with
      route? := some { field := rField, ty := rTy, init := rInit, alts := rAlts }
      states := acc.states.push { id := rField, ty? := some rTy, def? := some rInit }
      rawStateTys := acc.rawStateTys.push (rField, none) }
  else if k == ``compPortOutClause || k == ``compPortInClause then
    let pId : Ident := ⟨cl[1]⟩
    if pId.getId.toString.startsWith "__" then
      throwErrorAt pId s!"port name '{pId.getId}' is reserved (names starting with `__`)"
    if k == ``compPortOutClause then
      return { acc with portOuts := acc.portOuts.push { id := pId, ty := ← liftMacroM (return (← lowerQedType cl[3] false).1) } }
    else
      let (wPat?, wGuards) := parseCompWhen cl[7]
      return { acc with portIns := acc.portIns.push {
        id := pId, argId := ⟨cl[3]⟩,
        argTy := ← liftMacroM (return (← lowerQedType cl[5] false).1),
        whenPat? := wPat?, guards := wGuards, body := cl[9] } }
  else if k == ``compRpcQueryClause then
    let qId : Ident := ⟨cl[1]⟩
    let explicitTy? : Option Term ← if cl[2].getNumArgs == 2 then some <$> liftMacroM (return (← lowerQedType cl[2][1] false).1) else pure none
    let rpcId : Ident := ⟨cl[4]⟩
    let rawArgs : Array Term ← cl[6].getSepArgs.mapM (lowerCompExpr .val)
    let (rawPat?, rawGuards) := parseCompWhen cl[8]
    let whenPat? ← rawPat?.mapM fun (p, s) => do
      return (← liftMacroM (lowerQedPat p), ← lowerCompExpr .val s, collectQedPatIds p)
    let whenGuards ← rawGuards.mapM (lowerCompExpr .propGuard)
    let env ← getEnv
    let some (srvInfo, mInfo) := lookupServerMethod? env (← getCurrNamespace) (← getScope).openDecls rpcId.getId
      | throwErrorAt rpcId s!"unknown server RPC `{rpcId.getId}` in `query`"
    if rawArgs.size != mInfo.paramCount then
      throwErrorAt rpcId s!"`{rpcId.getId}` expects {mInfo.paramCount} argument(s), got {rawArgs.size}"
    unless mInfo.isReadOnly do
      throwErrorAt rpcId s!"reactive `query {qId.getId}` cannot call mutating server RPC `{srvInfo.shortName}.{mInfo.name}`; `query` only permits read-only server functions"
    let qTy ← match explicitTy? with
      | some ty => pure ty
      | none =>
          let some ty ← inferAwaitBinderTy? mInfo true
            | throwErrorAt qId s!"cannot infer type for `query {qId.getId}`; annotate it as `query {qId.getId} : Type = ...`"
          pure ty
    let (msgTy, hasMsgEnsured) ← match if explicitTy?.isNone then mInfo.ensPredConst else none with
      | some ensConst =>
          let qv := mkIdent `_qr_v
          let qpIds := (Array.range mInfo.paramCount).map fun i => mkIdent (.mkSimple s!"_qp_{i}")
          let ensApp ← (qpIds.push qv).foldlM (init := (mkIdent ensConst : Term)) fun acc x => `($acc $x)
          let exBody ← (qpIds.zip mInfo.paramTypeConsts).foldrM (init := ensApp) fun (pId, pTy) acc =>
            `(∃ ($pId:ident : $(mkIdent pTy)), $acc)
          pure (← `(Qed.Ensured $qTy (fun ($qv:ident : $qTy) => $exBody)), true)
      | none => pure (qTy, false)
    let qStateTy ← `(Cached $qTy)
    let qStateDef ← `({})
    return { acc with
      states := acc.states.push { id := qId, ty? := some qStateTy, def? := some qStateDef }
      rawStateTys := acc.rawStateTys.push (qId, none)
      queries := acc.queries.push {
        id := qId, ty := qTy, msgTy,
        source := .rpc { rpcRef := rpcId, srvInfo, mInfo, args := rawArgs, whenPat?, whenGuards, hasMsgEnsured }
      } }
  else if k == ``compQueryClause then
    let qId : Ident := ⟨cl[1]⟩
    let qTy : Term ← liftMacroM (return (← lowerQedType cl[3] false).1)
    let keyE ← lowerCompExpr .val cl[7]
    let urlE ← lowerCompExpr .val cl[10]
    let qStateTy ← `(Cached $qTy)
    let qStateDef ← `({})
    return { acc with
      states := acc.states.push { id := qId, ty? := some qStateTy, def? := some qStateDef }
      rawStateTys := acc.rawStateTys.push (qId, none)
      queries := acc.queries.push { id := qId, ty := qTy, msgTy := qTy, source := .url keyE urlE } }
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
  let resolvedStates ← if acc.keyF?.isNone then
    (acc.states.zip acc.rawStateTys).mapM fun (f, (_, rawTy?)) => do
      let def? ← match f.def?, rawTy? with
        | none, some rty => liftMacroM (Qed.Lang.inferQedTypeDefault? rty)
        | d, _           => pure d
      return { f with def? }
  else pure acc.states
  let invariants := acc.invariants ++ stx[8].getArgs
  let fieldNames := resolvedStates.map (·.id.getId)
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
  if !acc.queries.isEmpty && (!acc.props.isEmpty || !acc.binds.isEmpty || !acc.slots.isEmpty ||
      acc.hasChildren || !acc.events.isEmpty || resolvedStates.any (·.def?.isNone)) then
    throwErrorAt acc.queries[0]!.id "reactive `query` is only supported on top-level mountable application components"
  return {
    doc?, t,
    collections := acc.collections, states := resolvedStates, ephemeralFields := acc.ephemeralFields,
    props := acc.props, binds := acc.binds, slots := acc.slots, hasChildren := acc.hasChildren,
    events := acc.events, hasProps := !acc.props.isEmpty || !acc.binds.isEmpty,
    keyF? := acc.keyF?, outTy?, route? := acc.route?, starts := acc.starts,
    portOuts := acc.portOuts, portIns := acc.portIns, queries := acc.queries,
    actions := acc.actions, invariants, body := stx[7],
    sessionField? := acc.sessionField?
  }

/-! ## Continuation-Lifting for Client `await` / `catch` -/

private def packSuite (refStx : Syntax) (stmts : Array Syntax) : Syntax :=
  let info := SourceInfo.fromRef refStx
  let body := if stmts.isEmpty then
    #[Syntax.node info ``qedStmtPass #[Syntax.atom info "pass"]]
  else stmts
  Syntax.node info `Qed.Lang.suite #[Syntax.node info nullKind body]

private def mkPatIdent (info : SourceInfo) (nm : Name) (args : Array Syntax := #[]) : Syntax :=
  let sepArgs := args.foldl (init := #[]) fun acc a =>
    if acc.isEmpty then #[a] else (acc.push (Syntax.atom info ",")).push a
  let argsOpt := if args.isEmpty then Syntax.node info nullKind #[]
    else Syntax.node info nullKind #[Syntax.atom info "(", Syntax.node info nullKind sepArgs, Syntax.atom info ")"]
  Syntax.node info ``qedPatIdent #[mkIdent nm, argsOpt]

private def mkPatDot (info : SourceInfo) (tag : Name) : Syntax :=
  Syntax.node info ``qedPatDot #[Syntax.atom info ".", mkIdent tag, Syntax.node info nullKind #[]]

private def mkPatWild (info : SourceInfo) : Syntax :=
  Syntax.node info ``qedPatWild #[Syntax.atom info "_"]

private inductive CatchPatKind
  | wildcard
  | dotTag (tag : String) (binder? : Option Syntax)

private def classifyCatchCase (validTags : Array String) (isOption : Bool) (cStx : Syntax) :
    CommandElabM (CatchPatKind × Array Syntax) := do
  let pats := cStx[1].getSepArgs
  if pats.size != 1 then
    throwErrorAt cStx "each `catch` case must match a single pattern (`case .tag:`, `case .tag(err):`, `case .failed(err):`, or `case _:`)"
  let pat := pats[0]!
  let body := suiteStmts cStx[3]
  if pat.getKind == ``qedPatWild then
    return (.wildcard, body)
  let checkTag (tagRef : Syntax) (tag : String) (binder? : Option Syntax) : CommandElabM (CatchPatKind × Array Syntax) := do
    if tag == "failed" then
      return (.dotTag "failed" binder?, body)
    if tag == "none" then
      unless isOption do
        throwErrorAt tagRef "`.none` catch case is only valid when the awaited RPC returns an `Option` (`T?`)"
      if binder?.isSome then
        throwErrorAt tagRef "`.none` takes no error message argument"
      return (.dotTag "none" none, body)
    unless validTags.contains tag do
      let validStr := if validTags.isEmpty then ".failed" else
        String.intercalate ", " (validTags.toList.map (s!".{·}") ++ [".failed"])
      throwErrorAt tagRef s!"unknown error tag `.{tag}` in `catch` (valid patterns: {validStr})"
    return (.dotTag tag binder?, body)
  if pat.getKind == ``qedPatDot then
    let tag := pat[1].getId.toString
    if pat[2].getNumArgs == 3 then
      let args := pat[2][1].getSepArgs
      if args.size == 1 then
        let b := args[0]!
        unless b.getKind == ``qedPatWild || (b.getKind == ``qedPatIdent && b[1].getNumArgs == 0) do
          throwErrorAt b "error message pattern in `catch` must be an identifier or `_`"
        return ← checkTag pat tag (some b)
      else
        throwErrorAt pat "unsupported `catch` pattern; expected `.tag`, `.tag(msg)`, `.failed(err)`, `.none`, or `_`"
    else
      return ← checkTag pat tag none
  throwErrorAt pat "unsupported `catch` pattern; expected `.tag`, `.tag(msg)`, `.failed(err)`, `.none`, or `_`"

private partial def stmtContainsAwait (st : Syntax) : Bool :=
  let k := st.getKind
  (k == ``qedStmtLet && (unwrapParens1 st[4]).getKind == ``qedAwait) ||
  (k == ``qedStmtAssign && (unwrapParens1 st[2]).getKind == ``qedAwait) ||
  st.getArgs.any stmtContainsAwait

private def resolveRpcForAwait (ctx : RewriteCtx) (rpcId : Ident) (argCount : Nat) :
    CommandElabM (ServerInfo × ServerMethodInfo) := do
  let openDecls := (← getScope).openDecls
  let some (srvInfo, mInfo) := lookupServerMethod? (← getEnv) (← getCurrNamespace) openDecls rpcId.getId
    | throwErrorAt rpcId s!"unknown server RPC `{rpcId.getId}` in `await`"
  if argCount != mInfo.paramCount then
    throwErrorAt rpcId s!"`{rpcId.getId}` expects {mInfo.paramCount} argument(s), got {argCount}"
  recordUsedRpc ctx.usedRpcs srvInfo.shortName mInfo.name
  return (srvInfo, mInfo)

private def unpackAwaitCall (ref : Syntax) (awaitExpr : Syntax) : CommandElabM (Ident × Array Syntax) := do
  let inner := unwrapParens1 awaitExpr[1]
  unless inner.getKind == ``qedCall && inner[0].getKind == ``qedIdent do
    throwErrorAt ref "`await` expects a server RPC call `Server.method(args...)`"
  let rawArgs := inner[2].getSepArgs
  let argExprs ← rawArgs.mapM fun a => do
    unless a.getKind == ``qedCallArgPos do
      throwErrorAt a "RPC `await` calls take positional arguments"
    pure a[0]
  return (⟨inner[0][0]⟩, argExprs)

private partial def liftAwaitStmts (ctx : RewriteCtx) (outerParams : Array (Ident × Term))
    (localLetNames : Array Name) (stmts : Array Syntax) : CommandElabM (Array Syntax) := do
  go outerParams localLetNames stmts.toList
where
  go (outerParams : Array (Ident × Term)) (localNames : Array Name) : List Syntax → CommandElabM (Array Syntax)
  | [] => return #[]
  | st :: rest => do
      let info := SourceInfo.fromRef st
      let mkLetRawSt (id : Ident) (ty? : Option Term) (rhsExpr : Syntax) : Syntax :=
        let tyNode := match ty? with
          | some ty => Syntax.node info nullKind #[Syntax.atom info ":", Syntax.node info ``qedTypeAtom #[mkIdentFrom ty ty.raw.getId, Syntax.node info nullKind #[]]]
          | none    => Syntax.node info nullKind #[]
        Syntax.node info ``qedStmtLet #[Syntax.atom info "let", id, tyNode, Syntax.atom info "=", rhsExpr, Syntax.node info nullKind #[]]
      let k := st.getKind

      if k == ``qedStmtAssign && (unwrapParens1 st[2]).getKind == ``qedAwait then
        unless st[0].getKind == ``qedIdent && atomStr st[1] == "=" do
          throwErrorAt st "`field = await ...` requires a simple state field on the left-hand side"
        let fId : Ident := ⟨st[0][0]⟩
        let fname := fId.getId.eraseMacroScopes
        checkMutableField ctx fId s!"`{fname} = await ...`" fname
        let (rpcId, rawArgStxs) ← unpackAwaitCall st (unwrapParens1 st[2])
        let rawArgs ← rawArgStxs.mapM (lowerCompExpr .val)
        let (srvInfo, mInfo) ← resolveRpcForAwait ctx rpcId rawArgs.size
        let setterCtor ← registerSite ctx.sites #[(fname, none)] none
        let cbTerm : Term := mkIdentFrom st (ctx.msgPath ++ setterCtor)
        let srvId := mkIdentFrom rpcId srvInfo.serverName
        let methId := mkIdentFrom rpcId (Name.mkSimple mInfo.name)
        let loadingExpr := mkRawExpr (← `(Qed.Resource.loading))
        let assignSt := Syntax.node info ``qedStmtAssign #[st[0], Syntax.atom info "=", loadingExpr]
        let callTerm ← `(qedCheckRpcCall% $srvId:ident $methId:ident [$[$rawArgs:term],*] $cbTerm)
        let perfSt := Syntax.node info ``qedStmtPerform #[Syntax.atom info "perform", mkRawExpr callTerm]
        let tail ← go outerParams localNames rest
        return #[assignSt, perfSt] ++ tail

      if k == ``qedStmtLet && (unwrapParens1 st[4]).getKind == ``qedAwait then
        let xId : Ident := if st[1].isIdent then ⟨st[1]⟩ else mkIdentFrom st `_qedAwaitRes
        let optTy? : Option Term ← if st[2].getNumArgs == 2 then some <$> liftMacroM (return (← lowerQedType st[2][1] false).1) else pure none
        let (rpcId, rawArgStxs) ← unpackAwaitCall st (unwrapParens1 st[4])
        let rawArgs ← rawArgStxs.mapM (lowerCompExpr .val)
        let (srvInfo, mInfo) ← resolveRpcForAwait ctx rpcId rawArgs.size
        let catchCases : Array Syntax ←
          if st[5].getNumArgs == 1 then
            let cNode := st[5][0][1]
            if cNode.getKind == `Qed.Lang.catchArms then pure cNode[1].getArgs
            else throwErrorAt cNode "in client components, use `catch:` with `case .tag: ...` arms"
          else pure #[]
        let parsedCatch ← catchCases.mapM (classifyCatchCase mInfo.domainErrTags mInfo.isOption)

        let hasWildcard := parsedCatch.any fun (pk, _) => pk matches .wildcard
        let hasTag (t : String) := parsedCatch.any fun (pk, _) =>
          match pk with | .dotTag t' _ => t' == t | _ => false
        unless mInfo.domainErrTags.isEmpty || hasWildcard do
          let missing := mInfo.domainErrTags.filter (!hasTag ·)
          unless missing.isEmpty do
            let missStr := String.intercalate ", " (missing.toList.map (s!".{·}"))
            throwErrorAt st s!"`await {rpcId.getId}(...)` has unhandled domain error(s): {missStr}; handle them with `catch: case .tag: ...`"

        let restArr := rest.toArray
        let capturedOuter := outerParams.filter fun (pId, _) =>
          let pn := pId.getId.eraseMacroScopes
          restArr.any (mentionsIdent · pn) ||
          catchCases.any (mentionsIdent · pn) ||
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
            preLetStmts := preLetStmts.push (mkLetRawSt tmpId (some paramTyId) (mkRawExpr argT))
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
          let typedExpr ← `(($xId:ident : $oTy))
          okBody := #[mkLetRawSt xId none (mkRawExpr typedExpr)] ++ okBody

        let outcomePrefix := if mInfo.domainErrTags.isEmpty then `Qed.RpcSimpleOutcome else `Qed.RpcOutcome
        let okCtorName := outcomePrefix ++ `ok
        let okPat : Syntax ←
          if mInfo.isOption && !catchHasNone && mInfo.hasEnsures then
            let optVar := mkIdentFrom xId (Name.mkSimple s!"_qedOpt_{kIdx}")
            let mapped ← `(($optVar).map Qed.Ensured.val)
            okBody := #[mkLetRawSt xId none (mkRawExpr mapped)] ++ okBody
            pure (mkPatIdent info okCtorName #[mkPatIdent info optVar.getId])
          else
            let inner := if mInfo.hasEnsures then
              mkPatIdent info `Qed.Ensured.mk #[mkPatIdent info xId.getId, mkPatIdent info `_qed_ens]
            else mkPatIdent info xId.getId
            let arg := if mInfo.isOption && catchHasNone then mkPatIdent info `some #[inner] else inner
            pure (mkPatIdent info okCtorName #[arg])

        let mkCaseStx (patS : Syntax) (bStmts : Array Syntax) : Syntax :=
          Syntax.node info ``qedStmtCase
            #[Syntax.atom info "case", Syntax.node info nullKind #[patS], Syntax.atom info ":", packSuite st bStmts]

        let mut matchCases : Array Syntax := #[mkCaseStx okPat okBody]
        let mut wildcardCases : Array Syntax := #[]
        let mut coveredFailed := false
        let mut coveredNone := false
        for (pk, bodyRaw) in parsedCatch do
          let mut bOuter := outerParams
          let bLocals := localNames
          match pk with
          | .wildcard =>
              let bLifted ← go bOuter bLocals bodyRaw.toList
              wildcardCases := wildcardCases.push (mkCaseStx (mkPatWild info) bLifted)
          | .dotTag tag bOpt? =>
              if let some b := bOpt? then
                if b.getKind == ``qedPatIdent then
                  let bid : Ident := ⟨b[0]⟩
                  let bn := bid.getId.eraseMacroScopes
                  bOuter := (bOuter.filter (·.1.getId.eraseMacroScopes != bn)).push (bid, ← `(String))
              let bLifted ← go bOuter bLocals bodyRaw.toList
              let msgPat := bOpt?.getD (mkPatWild info)
              let patS : Syntax :=
                if tag == "failed" then
                  mkPatIdent info (outcomePrefix ++ `failed) #[msgPat]
                else if tag == "none" then
                  mkPatIdent info okCtorName #[mkPatIdent info `none]
                else
                  mkPatIdent info (outcomePrefix ++ `err) #[mkPatDot info (Name.mkSimple tag), msgPat]
              if tag == "failed" then coveredFailed := true
              if tag == "none" then coveredNone := true
              matchCases := matchCases.push (mkCaseStx patS bLifted)
        matchCases := matchCases ++ wildcardCases
        if wildcardCases.isEmpty && (!coveredFailed || (mInfo.isOption && !coveredNone)) then
          matchCases := matchCases.push (mkCaseStx (mkPatWild info) #[Syntax.node info ``qedStmtPass #[Syntax.atom info "pass"]])

        let scrutNode := Syntax.node info ``qedIdent #[outVarId.raw]
        let matchSt := Syntax.node info ``qedStmtMatch
          #[Syntax.atom info "match", Syntax.node info nullKind #[scrutNode], Syntax.atom info ":",
            Syntax.node info nullKind matchCases]
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
        let perfSt := Syntax.node info ``qedStmtPerform #[Syntax.atom info "perform", mkRawExpr callTerm]
        return preLetStmts.push perfSt

      if k == ``qedStmtLet then
        let (outer', locals') ←
          if st[1].isIdent then
            let lId : Ident := ⟨st[1]⟩
            let ln := lId.getId.eraseMacroScopes
            if st[2].getNumArgs == 2 then
              let tyT ← liftMacroM (return (← lowerQedType st[2][1] false).1)
              pure (outerParams.filter (·.1.getId.eraseMacroScopes != ln) |>.push (lId, tyT), localNames)
            else
              pure (outerParams.filter (·.1.getId.eraseMacroScopes != ln), localNames.push ln)
          else pure (outerParams, localNames)
        let tail ← go outer' locals' rest
        return #[st] ++ tail

      if (k == ``qedStmtIf || k == ``qedStmtIfLet || k == ``qedStmtMatch) && stmtContainsAwait st then
        unless rest.isEmpty || hasReturnStmt st do
          throwErrorAt st "statements after an `if`/`match` containing `await` are not supported unless the branch `return`s; move trailing statements inside the branches"
        let tailIfReturn := if hasReturnStmt st then rest else []
        let liftOptElse (eNode : Syntax) : CommandElabM Syntax := do
          if eNode.getNumArgs == 3 then
            let eLifted ← go outerParams localNames ((suiteStmts eNode[2]).toList ++ tailIfReturn)
            pure (Syntax.node eNode.getHeadInfo eNode.getKind #[eNode[0], eNode[1], packSuite st eLifted])
          else
            pure eNode
        if k == ``qedStmtIf then
          let tLifted ← go outerParams localNames ((suiteStmts st[3]).toList ++ tailIfReturn)
          let elifs' ← st[4].getArgs.mapM fun el => do
            let elLifted ← go outerParams localNames ((suiteStmts el[3]).toList ++ tailIfReturn)
            pure (Syntax.node el.getHeadInfo el.getKind #[el[0], el[1], el[2], packSuite st elLifted])
          let eOpt ← liftOptElse st[5]
          return #[Syntax.node info k #[st[0], st[1], st[2], packSuite st tLifted, Syntax.node info nullKind elifs', eOpt]]
        else if k == ``qedStmtIfLet then
          let pIds := collectQedPatIds st[2]
          let tLocals := localNames ++ pIds.filter fun n => !(outerParams.any (·.1.getId.eraseMacroScopes == n))
          let tLifted ← go outerParams tLocals ((suiteStmts st[6]).toList ++ tailIfReturn)
          let eOpt ← liftOptElse st[7]
          return #[Syntax.node info k #[st[0], st[1], st[2], st[3], st[4], st[5], packSuite st tLifted, eOpt]]
        else
          let cases' ← st[3].getArgs.mapM fun c => do
            let pIds := c[1].getSepArgs.flatMap collectQedPatIds
            let aLocals := localNames ++ pIds.filter fun n => !(outerParams.any (·.1.getId.eraseMacroScopes == n))
            let aLifted ← go outerParams aLocals ((suiteStmts c[3]).toList ++ tailIfReturn)
            pure (Syntax.node c.getHeadInfo c.getKind #[c[0], c[1], c[2], packSuite st aLifted])
          return #[Syntax.node info k #[st[0], st[1], st[2], Syntax.node st[3].getHeadInfo st[3].getKind cases']]

      let tail ← go outerParams localNames rest
      return #[st] ++ tail

def collectSitesAndRewriteStateful (spec : ComponentSpec) :
    CommandElabM (Array SetSite × Option RouteDecl × Array QueryDecl × Array Term × Term × Array HoistedSub × Array FieldDecl × Array ResetFormSub × Array (String × String)) := do
  let sitesRef      ← IO.mkRef (#[] : Array SetSite)
  let hoistedRef    ← IO.mkRef (#[] : Array HoistedSub)
  let formDraftsRef ← IO.mkRef (#[] : Array FieldDecl)
  let resetFormsRef ← IO.mkRef (#[] : Array ResetFormSub)
  let usedRpcsRef   ← IO.mkRef (#[] : Array (String × String))
  let contCtrRef    ← IO.mkRef (0 : Nat)
  let baseCtx : RewriteCtx := {
    stateFields := spec.fieldNames, bindFields := spec.bindNames,
    actionNames := spec.actions.map (·[1].getId) ++ spec.portIns.map (·.id.getId),
    isPureComp := false, msgPath := spec.t.getId ++ `Msg, hasOut := spec.outTy?.isSome,
    collections := spec.collections, sites := sitesRef, hoisted := hoistedRef,
    formDrafts := formDraftsRef, resetForms := resetFormsRef,
    usedRpcs := usedRpcsRef, contCounter := contCtrRef
  }
  for a in spec.actions do
    let name := a[1].getId
    if (← sitesRef.get).any (·.ctor == name) || spec.collections.any (·.1.getId == name) then
      throwErrorAt a[1] "duplicate action name `{name}`"
    let rawParams := if a[2].getNumArgs == 3 then a[2][1].getSepArgs else #[]
    let params : Array (Ident × Term) ← rawParams.mapM fun p =>
      return (⟨p[0]⟩, ← liftMacroM (return (← lowerQedType p[2] false).1))
    let pNames := params.map (·.1.getId)
    if pNames.toList.eraseDups.length != pNames.size || pNames.any spec.allNames.contains then
      throwErrorAt a "action parameters must be distinct and must not shadow fields"
    let (rawWPat?, rawWGuards) := parseCompWhen a[3]
    let whenPat? ← rawWPat?.mapM fun (p, s) => do
      let sRw ← rewriteIn baseCtx false s
      return (← liftMacroM (lowerQedPat p), ← lowerCompExpr .val sRw)
    let guardsRw ← rawWGuards.mapM (rewriteIn baseCtx false)
    let guard? ← lowerCompGuards guardsRw
    let stmtsRaw := suiteStmts (← rewriteIn baseCtx false a[5])
    let stmts ← liftAwaitStmts baseCtx params #[] stmtsRaw
    let mut dummyAssigns : Array (Name × Option Term) := #[]
    for s in stmts do
      if s.getKind == ``qedStmtAssign && s[0].getKind == ``qedIdent && atomStr s[1] == "=" && isCdot s[2] then
        dummyAssigns ← pushHandlerAssign baseCtx dummyAssigns s[0][0] none
    if !params.isEmpty && !dummyAssigns.isEmpty then
      throwErrorAt a "use an explicit set value in an action with parameters"
    let cur ← sitesRef.get
    sitesRef.set (cur.push {
      key := s!"action:{name}", ctor := name, params, whenPat?, guard?, assigns := dummyAssigns, stmts? := some stmts })
  for p in spec.portIns do
    let name := p.id.getId
    if (← sitesRef.get).any (·.ctor == name) || spec.collections.any (·.1.getId == name) then
      throwErrorAt p.id "duplicate port/action name `{name}`"
    if spec.allNames.contains p.argId.getId then
      throwErrorAt p.argId "port parameter must not shadow fields"
    let whenPat? ← p.whenPat?.mapM fun (pat, s) => do
      let sRw ← rewriteIn baseCtx false s
      return (← liftMacroM (lowerQedPat pat), ← lowerCompExpr .val sRw)
    let guardsRw ← p.guards.mapM (rewriteIn baseCtx false)
    let guard? ← lowerCompGuards guardsRw
    let stmtsRaw := suiteStmts (← rewriteIn baseCtx false p.body)
    let stmts ← liftAwaitStmts baseCtx #[(p.argId, p.argTy)] #[] stmtsRaw
    let cur ← sitesRef.get
    sitesRef.set (cur.push {
      key := s!"port:{name}", ctor := name, params := #[(p.argId, p.argTy)], whenPat?, guard?, stmts? := some stmts })
  let route'? ← spec.route?.mapM fun rd => do
    let alts' ← rd.alts.mapM fun alt => do
      let rwBody ← rewriteIn baseCtx false alt[3]
      let patIds := alt[1].getSepArgs.flatMap collectQedPatIds
      let lifted ← liftAwaitStmts baseCtx #[] patIds (suiteStmts rwBody)
      pure (Syntax.node .none alt.getKind #[alt[0], alt[1], alt[2], packSuite alt lifted])
    pure { rd with alts := alts' }
  let queries' ← spec.queries.mapM fun q => do
    match q.source with
    | .url k u =>
        pure { q with source := .url k u }
    | .rpc rspec =>
        recordUsedRpc usedRpcsRef rspec.srvInfo.shortName rspec.mInfo.name
        pure { q with source := .rpc rspec }
  let starts' ← spec.starts.mapM fun st => do
    let rw ← rewriteIn { baseCtx with inPerform := true } false st
    lowerCompExpr .val rw
  let viewCtx := { baseCtx with
    allowHoist := true
    wrapMsg?   := if spec.hasSlotsOrKids then some (mkIdent `_wrap) else none }
  let bodyRw ← rewriteIn viewCtx false spec.body
  let body' ← lowerCompExpr .val bodyRw
  return (← sitesRef.get, route'?, queries', starts', body', ← hoistedRef.get, ← formDraftsRef.get, ← resetFormsRef.get, ← usedRpcsRef.get)

end CompElab
end Qed
