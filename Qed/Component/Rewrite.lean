import Qed.Component.Syntax
import Qed.Resource.Basic
import Qed.Socket.Basic
import Qed.Server.Registry
import Qed.Schema.Registry

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

syntax (name := qedCheckRpcCallTerm) "qedCheckRpcCall% " ident ident "[" term,* "]" term : term
syntax (name := qedCheckPredictTerm) "qedCheckPredict% " ident ident "[" term,* "]" term : term
syntax (name := qedCheckChanSubTerm) "qedCheckChanSub% " ident "[" term,* "]" str "(" term "," term "," term "," term ")" : term
syntax (name := qedCheckChanSendTerm) "qedCheckChanSend% " ident "[" term,* "]" str : term

/-! ## Component Spec Structures & Rewriting -/

structure FieldDecl where
  id     : Ident
  ty?    : Option Term := none
  def?   : Option Term := none
  ty     : Term := ⟨.missing⟩
  rawTy? : Option Syntax := none

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
  key     : String
  ctor    : Name
  params  : Array (Ident × Term) := #[]
  assigns : Array (Name × Option Term) := #[]
  send?   : Option Term := none
  stmts?  : Option (Array Syntax) := none

structure PortOutDecl where
  id : Ident
  ty : Term

structure PortInDecl where
  id    : Ident
  argId : Ident
  argTy : Term
  body  : Syntax

structure RpcQuerySpec where
  rpcRef        : Ident
  srvInfo       : ServerInfo
  mInfo         : ServerMethodInfo
  args          : Array Term
  whenPat?      : Option (Term × Term × Array Name)
  whenGuards    : Array Term
  hasMsgEnsured : Bool
deriving Inhabited

structure QueryDecl where
  id     : Ident
  ty     : Term
  msgTy  : Term
  rpc    : RpcQuerySpec
deriving Inhabited

def QueryDecl.ctorName (q : QueryDecl) : Name :=
  Name.mkSimple s!"_query_{q.id.getId}"

def lowerCompExpr (mode : Qed.Lang.ExprMode) (stx : Syntax) : CommandElabM Term := do
  if mode == .val then
    return (← liftMacroM (Qed.Jsx.expandJsxExpr "" none (`(())) stx)).1
  else
    liftMacroM (Qed.Lang.lowerSimpleQedExpr mode stx)

def lowerPosCallArgs (ref : Syntax) (callDesc : String) (expectedArity? : Option Nat)
    (rawArgs : Array Syntax) (lowerArg : Syntax → CommandElabM Term := lowerCompExpr .val) :
    CommandElabM (Array Term) := do
  if let some n := expectedArity? then
    if rawArgs.size != n then
      throwErrorAt ref s!"`{callDesc}` expects {n} argument(s), got {rawArgs.size}"
  rawArgs.mapM fun ra => do
    unless ra.getKind == ``qedCallArgPos do
      throwErrorAt ra s!"named arguments are not supported in `{callDesc}`"
    lowerArg (ra.getArg 0)

def mkPortSendTerm (compName : Name) (exprStx : Syntax) (targetId : Ident) (portName : Name)
    (rawArgs : Array Syntax) (lowerArg : Syntax → CommandElabM Term := lowerCompExpr .val) :
    CommandElabM Term := do
  let argTs ← lowerPosCallArgs exprStx s!"{portName}.send(...)" (some 1) rawArgs lowerArg
  `($(mkIdentFrom targetId (compName ++ portName)) $(argTs[0]!))

def parseCompIfCond (optCond : Syntax) : Option (Syntax × Syntax) × Array Syntax :=
  if optCond.getNumArgs == 1 then
    let cBody := ((optCond.getArg 0).getArg 1)
    if cBody.getKind == ``compIfLet then
      let gs := if (cBody.getArg 4).getNumArgs == 2 then ((cBody.getArg 4).getArg 1).getSepArgs else #[]
      (some ((cBody.getArg 1), (cBody.getArg 3)), gs)
    else
      (none, cBody.getSepArgs)
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
        let isEnsOrField (e : Expr) : Bool := e.isAppOfArity ``Qed.Ensured 2 || e.isAppOfArity ``Qed.Field 2
        if mInfo.isOption && ty.isAppOfArity ``Option 1 then
          let optInner ← Meta.whnf ty.appArg!
          let unwrapped := if isEnsOrField optInner then optInner.appFn!.appArg! else optInner
          ty ← if hasCatchNone then pure unwrapped else Meta.mkAppM ``Option #[unwrapped]
        else if isEnsOrField ty then
          ty := ty.appFn!.appArg!
        if ty.hasLooseBVars then return none
        return some (← PrettyPrinter.delab ty)
  catch _ =>
    modify fun s => { s with messages := savedMsgs }
    return none

structure SubDecl where
  id           : Ident
  chanRef      : Ident
  chInfo       : Qed.ChannelInfo
  args         : Array Term
  whenPat?     : Option (Term × Term × Array Name) := none
  whenGuards   : Array Term := #[]
  reconnect    : Qed.Reconnect
  onJoin?      : Option (Option Syntax × Array Syntax) := none
  onMsg?       : Option (Syntax × Array Syntax) := none
  onStatus?    : Option (Syntax × Array Syntax) := none
  msgEvTy      : Term
  hasMsgEnsured: Bool := false

def SubDecl.joinCtor   (s : SubDecl) : Name := Name.mkSimple s!"_wsJoin_{s.id.getId}"
def SubDecl.msgCtor    (s : SubDecl) : Name := Name.mkSimple s!"_wsMsg_{s.id.getId}"
def SubDecl.statusCtor (s : SubDecl) : Name := Name.mkSimple s!"_wsStatus_{s.id.getId}"

inductive PredictBody where
  | expr  (stx : Syntax)
  | block (stmts : Array Syntax)
deriving Inhabited

structure SpecResolveSite where
  resCtor        : Name
  txIdParam      : Ident
  capturedParams : Array (Ident × Term)
  predParam      : Ident
  outParam       : Ident
  mInfo          : ServerMethodInfo
  catchHasNone   : Bool
  contCtor       : Name
  confirmCtor?   : Option Name := none
  rollbackCtor?  : Option Name := none
  catchCtor?     : Option Name := none
  callRef        : Syntax

structure SpecDispatchNode where
  ref          : Syntax
  preCtor?     : Option Name := none
  preArgs      : Array Term := #[]
  capturedArgs : Array Term := #[]
  rpcArgs      : Array Term := #[]
  hoistDefs    : Array (Ident × Term × Term) := #[]
  srvInfo      : ServerInfo
  mInfo        : ServerMethodInfo
  catchHasNone : Bool
  predValTy    : Term
  innerEnsTy?  : Option Term := none
  predBody     : PredictBody
  contCtor     : Name
  resCtor      : Name
deriving Inhabited

inductive EnsuredWrapKind | plain | ensured | optEnsured deriving DecidableEq

def ensuredWrapKind (mInfo : ServerMethodInfo) (catchHasNone : Bool) : EnsuredWrapKind :=
  if !mInfo.hasEnsures then .plain
  else if mInfo.isOption && !catchHasNone then .optEnsured
  else .ensured

structure SpecDispatchArm where
  ctor   : Name
  params : Array (Ident × Term) := #[]
  stmts  : Array Syntax

structure ComponentSpec where
  doc?            : Option (TSyntax ``Lean.Parser.Command.docComment) := none
  t               : Ident
  collections     : Array (Ident × Ident) := #[]
  states          : Array FieldDecl := #[]
  ephemeralFields : Array Ident := #[]
  props           : Array FieldDecl := #[]
  binds           : Array FieldDecl := #[]
  slots           : Array SlotDecl := #[]
  hasChildren     : Bool := false
  events          : Array EventDecl := #[]
  hasProps        : Bool := false
  keyF?           : Option Ident := none
  outTy?          : Option Term := none
  route?          : Option RouteDecl := none
  starts          : Array Syntax := #[]
  portOuts        : Array PortOutDecl := #[]
  portIns         : Array PortInDecl := #[]
  queries         : Array QueryDecl := #[]
  subscriptions   : Array SubDecl := #[]
  actions         : Array Syntax := #[]
  invariants      : Array Syntax := #[]
  body            : Syntax := .missing
  hoisted         : Array HoistedSub := #[]
  resetForms      : Array ResetFormSub := #[]
  hasEffects      : Bool := false
  sessionField?   : Option Ident := none
  usedRpcs        : Array (String × String) := #[]
  usedChannels    : Array (String × String) := #[]
  styles          : Array Syntax := #[]
  stylesheets     : Array String := #[]
  themes          : Array Ident := #[]
  headClause?     : Option Syntax := none
  specDispatches  : Array SpecDispatchArm := #[]
  specNodes       : Array SpecDispatchNode := #[]
  specResolves    : Array SpecResolveSite := #[]

def ComponentSpec.hasSpeculative (s : ComponentSpec) : Bool := !s.specResolves.isEmpty

def ComponentSpec.fieldNames (s : ComponentSpec) : Array Name := s.states.map (·.id.getId)
def ComponentSpec.propNames  (s : ComponentSpec) : Array Name := s.props.map (·.id.getId)
def ComponentSpec.bindNames  (s : ComponentSpec) : Array Name := s.binds.map (·.id.getId)
def ComponentSpec.allNames   (s : ComponentSpec) : Array Name :=
  (s.fieldNames ++ s.propNames ++ s.bindNames).toList.eraseDups.toArray
def ComponentSpec.mountable  (s : ComponentSpec) : Bool := s.states.all (·.def?.isSome)
def ComponentSpec.hasSlotsOrKids (s : ComponentSpec) : Bool := !s.slots.isEmpty || s.hasChildren
def ComponentSpec.id (s : ComponentSpec) (sub : Name) : Ident := mkIdent (s.t.getId ++ sub)
def ComponentSpec.msgCtor (s : ComponentSpec) (c : Name) : Ident := mkIdent (s.t.getId ++ `Msg ++ c)
def ComponentSpec.outCtor (s : ComponentSpec) (c : Name) : Ident := mkIdent (s.t.getId ++ `Out ++ c)
def ComponentSpec.stateId  (s : ComponentSpec) : Ident := s.id `State
def ComponentSpec.msgId    (s : ComponentSpec) : Ident := s.id `Msg
def ComponentSpec.propsId  (s : ComponentSpec) : Ident := s.id `Props
def ComponentSpec.initId   (s : ComponentSpec) : Ident := s.id `init
def ComponentSpec.updateId (s : ComponentSpec) : Ident := s.id `update
def ComponentSpec.viewId   (s : ComponentSpec) : Ident := s.id `view

def resolveServerRpc (rpcId : Ident) (argCount : Nat) (ctxDesc : String) :
    CommandElabM (ServerInfo × ServerMethodInfo) := do
  let some (srvInfo, mInfo) := lookupServerMethod? (← getEnv) (← getCurrNamespace) (← getScope).openDecls rpcId.getId
    | throwErrorAt rpcId s!"unknown server RPC `{rpcId.getId}` in `{ctxDesc}`"
  if argCount != mInfo.paramCount then
    throwErrorAt rpcId s!"`{rpcId.getId}` expects {mInfo.paramCount} argument(s), got {argCount}"
  return (srvInfo, mInfo)

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
  let pp : Option Term → String := fun | some e => e.raw.reprint.getD (toString e.raw) | none => "_"
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
  compName       : Name := .anonymous
  stateFields    : Array Name
  bindFields     : Array Name
  propNames      : Array Name := #[]
  eventNames     : Array Name := #[]
  subNames       : Array Name := #[]
  portOutNames   : Array Name := #[]
  actionNames    : Array Name := #[]
  inPerform      : Bool := false
  isPureComp     : Bool
  msgPath        : Name
  hasOut         : Bool
  collections    : Array (Ident × Ident)
  wrapMsg?       : Option Ident := none
  sites          : IO.Ref (Array SetSite)
  hoisted        : IO.Ref (Array HoistedSub)
  formDrafts     : IO.Ref (Array FieldDecl)
  resetForms     : IO.Ref (Array ResetFormSub)
  allowHoist     : Bool := false
  usedRpcs       : IO.Ref (Array (String × String))
  contCounter    : IO.Ref Nat
  specDispatches : IO.Ref (Array SpecDispatchArm)
  specNodes      : IO.Ref (Array SpecDispatchNode)
  specResolves   : IO.Ref (Array SpecResolveSite)

def mkRewriteCtx (spec : ComponentSpec) (isPureComp : Bool) (allowHoist : Bool := false) :
    CommandElabM RewriteCtx := do
  return {
    compName       := if isPureComp then .anonymous else spec.t.getId
    stateFields    := if isPureComp then #[] else spec.fieldNames
    bindFields     := spec.bindNames
    propNames      := spec.propNames
    eventNames     := if isPureComp then #[] else spec.events.map (·.id.getId)
    subNames       := if isPureComp then #[] else spec.subscriptions.map (·.id.getId)
    portOutNames   := if isPureComp then #[] else spec.portOuts.map (·.id.getId)
    actionNames    := if isPureComp then #[] else spec.actions.map (·[1].getId) ++ spec.portIns.map (·.id.getId)
    isPureComp
    msgPath        := spec.t.getId ++ `Msg
    hasOut         := if isPureComp then false else spec.outTy?.isSome
    collections    := if isPureComp then #[] else spec.collections
    allowHoist
    sites          := ← IO.mkRef #[]
    hoisted        := ← IO.mkRef #[]
    formDrafts     := ← IO.mkRef #[]
    resetForms     := ← IO.mkRef #[]
    usedRpcs       := ← IO.mkRef #[]
    contCounter    := ← IO.mkRef 0
    specDispatches := ← IO.mkRef #[]
    specNodes      := ← IO.mkRef #[]
    specResolves   := ← IO.mkRef #[]
  }

def lowerLetStmt (st : Syntax) (lowerVal : Syntax → CommandElabM Term) (cont : Term) :
    CommandElabM Term := do
  let rhsT ← lowerVal (st.getArg 4)
  if (st.getArg 1).isIdent then
    let lId : Ident := ⟨(st.getArg 1)⟩
    match ← lowerOptType (st.getArg 2) with
    | some lTy => `(let $lId:ident : $lTy := $rhsT; $cont)
    | none     => `(let $lId:ident := $rhsT; $cont)
  else `(let _ := $rhsT; $cont)

syntax (name := qedCompSetAtStx) "qedCompSetAt(" ident ", " term ", " term ")" : term

open Lean Meta Elab Term in
@[term_elab qedCompSetAtStx]
def elabQedCompSetAt : TermElab := fun stx expectedType? => do
  let fId : Ident := ⟨stx.getArg 1⟩
  let idxStx : Term := ⟨stx.getArg 3⟩
  let valStx : Term := ⟨stx.getArg 5⟩
  let arrExpr ← elabTerm fId none
  synthesizeSyntheticMVarsNoPostponing
  let arrTy ← whnf (← instantiateMVars (← inferType arrExpr))
  if arrTy.isAppOfArity `Qed.Dict 2 then
    let setId := mkIdentFrom stx `Qed.Dict.set
    elabTerm (← `($setId $fId $idxStx $valStx)) expectedType?
  else
    elabTerm (← `(($fId).set $idxStx $valStx (by first | get_elem_tactic | (simp (config := { zetaDelta := false }) only [$fId:ident, Array.size_set, Array.size_push] <;> omega)))) expectedType?

def lowerArraySetExpr (fIdent : Ident) (idxT rhsT cont : Term) : CommandElabM Term :=
  `(let $fIdent:ident := qedCompSetAt($fIdent, $idxT, $rhsT); $cont)

def lowerControlFlowStmt (st : Syntax) (lowerVal : Syntax → CommandElabM Term)
    (lowerBranch : Array Syntax → CommandElabM Term) : CommandElabM Term := do
  let k := st.getKind
  if k == ``qedStmtIf then
    let cond ← lowerCompExpr .propGuard (st.getArg 1)
    let tT ← lowerBranch (suiteStmts (st.getArg 3))
    let eT ← lowerBranch ((desugarElifs (st.getArg 4).getArgs (st.getArg 5)).getD #[])
    `(if $(mkIdent `_qedIf):ident : $cond then $tT else $eT)
  else if k == ``qedStmtIfLet then
    let pat ← liftMacroM (lowerQedPat (st.getArg 2))
    let scrut ← lowerVal (st.getArg 4)
    let tT ← lowerBranch (suiteStmts (st.getArg 6))
    let eT ← lowerBranch (if (st.getArg 7).getNumArgs == 3 then suiteStmts ((st.getArg 7).getArg 2) else #[])
    `(match $(mkIdent `_qedIfLet):ident : $scrut:term with | $pat:term => $tT | _ => $eT)
  else
    let scruts ← (st.getArg 1).getSepArgs.mapM lowerVal
    let alts ← (st.getArg 3).getArgs.mapM fun alt => do
      let pats ← (alt.getArg 1).getSepArgs.mapM fun p => liftMacroM (lowerQedPat p)
      `(Lean.Parser.Term.matchAltExpr| | $[$pats:term],* => $(← lowerBranch (suiteStmts (alt.getArg 3))))
    `(match $[$scruts:term],* with $[$alts:matchAlt]*)

private def mkEnsuredExistentialTy (valTy : Term) (ensConst : Name) (paramCount : Nat)
    (paramTypeConsts : Array Name) (valVar : Name) (paramPfx : String) : CommandElabM Term := do
  let vId := mkIdent valVar
  let pIds := (Array.range paramCount).map fun i => mkIdent (.mkSimple s!"{paramPfx}{i}")
  let ensApp ← Qed.Lang.mkAppTerms (mkIdent ensConst) ((pIds.push vId).map (⟨·.raw⟩))
  let exBody ← (pIds.zip paramTypeConsts).foldrM (init := ensApp) fun (pId, pTy) acc =>
    `(∃ ($pId:ident : $(mkIdent pTy)), $acc)
  `(Qed.Ensured $valTy (fun ($vId:ident : $valTy) => $exBody))

def recordUsedRpc (ref : IO.Ref (Array (String × String))) (srv : String) (m : String) : IO Unit :=
  ref.modify (pushUnique · (srv, m))

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

def formatStateFieldList (fields : Array Name) : String :=
  if fields.isEmpty then "this component has no `state` fields"
  else s!"`state` fields: {String.intercalate ", " (fields.toList.map fun n => s!"`{n}`")}"

def throwNotMutableStateField (ref : Syntax) (prefixMsg : String) (fname : Name)
    (stateFields propNames : Array Name) : CommandElabM Unit := do
  let lead := if prefixMsg == s!"`{fname}`" then s!"`{fname}`" else s!"{prefixMsg}: `{fname}`"
  if propNames.contains fname then
    throwErrorAt ref s!"{lead} is a read-only `prop` and cannot be assigned ({formatStateFieldList stateFields})"
  else
    let hint := Qed.Diag.didYouMean fname.toString (stateFields.toList.map toString)
    throwErrorAt ref s!"{lead} is not a `state` field of this component{hint} ({formatStateFieldList stateFields})"

def checkMutableField (ctx : RewriteCtx) (ref : Syntax) (prefixMsg : String) (fname : Name) :
    CommandElabM Unit := do
  unless (ctx.stateFields ++ ctx.bindFields).contains fname do
    throwNotMutableStateField ref prefixMsg fname ctx.stateFields ctx.propNames

def pushHandlerAssign (ctx : RewriteCtx) (assigns : Array (Name × Option Term))
    (fId : Syntax) (expr? : Option Term) :
    CommandElabM (Array (Name × Option Term)) := do
  let fname := fId.getId.eraseMacroScopes
  checkMutableField ctx fId s!"`{fname}`" fname
  if assigns.any (·.1 == fname) then
    throwErrorAt fId s!"`{fname}`: this handler already updates `{fname}`"
  if expr?.isNone && assigns.any (·.2.isNone) then
    throwErrorAt fId s!"`{fname} = _`: only one `_` placeholder per handler"
  return assigns.push (fname, expr?)

def noEmitsErr (ref : Syntax) : CommandElabM Unit :=
  throwErrorAt ref "`.emit(...)` bubbles an output, but this component declares no output event; add `event name` between the `state` fields and the `view`"

private def unitEvents : List String :=
  ["onClick", "onSubmit", "onBlur", "onFocus", "onDoubleClick", "onMouseDown", "onMouseUp"]
private def strEvents : List String := ["onInput", "onChange", "onKeydown", "onKeyup"]

private def wrapEventAttr (vNode : Syntax) (argTys : Array Term) (msgTy : Ident)
    (wrapMsg? : Option Ident) : CommandElabM Term := do
  let vT ← liftMacroM <| Qed.Jsx.expandAttrVal vNode (`(""))
  let evTy ← argTys.foldrM (init := (msgTy : Term)) fun aTy acc => `($aTy → $acc)
  let mut typedV : Term ← `(($vT : $evTy))
  if let some w := wrapMsg? then
    if argTys.isEmpty then typedV ← `($w $typedV)
    else
      let argIds := (List.range argTys.size).toArray.map fun i => mkIdent (Name.mkSimple s!"_ea{i}")
      let wrapped ← `($w $(← Qed.Lang.mkAppTerms typedV (argIds.map (⟨·.raw⟩))))
      typedV ← argIds.foldrM (init := wrapped) fun arg acc => `(fun $arg => $acc)
  return typedV

private def wrapEventAttrs (pairs : Array (Bool × Syntax)) (msgTy : Ident) (wrapMsg? : Option Ident)
    (lookupArgTys : String → CommandElabM (Option (Array Term))) : CommandElabM (Array Syntax) :=
  pairs.mapM fun (wasAssign, a') => do
    if !wasAssign then
      if let some (_, aname, valNode) := matchAttrValExpr? a' then
        if let some argTys ← lookupArgTys aname then
          return mkJsxAttrExpr aname (← wrapEventAttr valNode argTys msgTy wrapMsg?)
    return a'

private def injectAutoKey (bodyStx : Syntax) (compFullName : Name) (bindId : Ident) :
    CommandElabM Syntax := do
  if bodyStx.getKind == ``Qed.Jsx.qedExprJsx then
    let el := (bodyStx.getArg 0)
    let ek := el.getKind
    if ek == ``Qed.Jsx.selfClosing || ek == ``Qed.Jsx.withChildren then
      let attrs := (el.getArg 2).getArgs
      let hasKey := attrs.any fun a => (matchNamedAttr? a).any (·.2.1 == "key")
      if !hasKey then
        let keyVal ← `($(mkIdent (compFullName ++ `keyOf)) $bindId)
        let kids? := if ek == ``Qed.Jsx.withChildren then some (el.getArg 4) else none
        let el' := rebuildJsxEl el (attrs.push (mkJsxAttrExpr "key" keyVal)) kids?
        return Syntax.node .none ``Qed.Jsx.qedExprJsx #[el']
  return bodyStx

private def rewriteLowerElement (ctx : RewriteCtx) (stx : Syntax)
    (rewrittenPairs : Array (Bool × Syntax)) (kids? : Option Syntax) : CommandElabM Syntax := do
  let some _ := ctx.wrapMsg? | return rebuildJsxEl stx (rewrittenPairs.map (·.2)) kids?
  let newAttrs ← wrapEventAttrs rewrittenPairs (mkIdent ctx.msgPath) ctx.wrapMsg? fun aname => do
    if unitEvents.contains aname then pure (some #[])
    else if strEvents.contains aname then pure (some #[← `(String)])
    else if aname == "onCheck" then pure (some #[← `(Bool)])
    else pure none
  return rebuildJsxEl stx newAttrs kids?

private def isSomePlaceholder (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx
  u.getKind == ``qedCall &&
  (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId.eraseMacroScopes == `some &&
  (u.getArg 2).getSepArgs.size == 1 && (u.getArg 2).getSepArgs[0]!.getKind == ``qedCallArgPos &&
  isPlaceholder (u.getArg 2).getSepArgs[0]![0]

private def rewriteHoistedChild (ctx : RewriteCtx) (inLambda : Bool) (stx : Syntax)
    (tag : String) (cInfo : ComponentInfo) (attrNames : Array String)
    (rewrittenAttrs : Array Syntax) (kids? : Option Syntax) : CommandElabM (Option Syntax) := do
  let mustHoist := !cInfo.hasLocalDef || attrNames.any (·.startsWith "bind:") ||
    cInfo.hasChildren || !cInfo.slotNames.isEmpty
  unless cInfo.kind == .stateful && cInfo.mountable &&
      (mustHoist || (!inLambda && !attrNames.contains "key" && !attrNames.contains "initial")) do
    return none
  if inLambda && mustHoist then
    throwErrorAt stx s!"<{tag}> uses effects, `Html` props, `children`, or `bind:` and cannot be dynamically mounted inside a loop lambda; hoist its state into the parent or use `collection`"
  let curH ← ctx.hoisted.get
  let subName := Name.mkSimple s!"_sub_{curH.size}"
  let subFieldId := mkIdentFrom stx subName
  let mut dataProps : Array (Ident × Term) := #[]
  let mut outArms   : Array OutArm := #[]
  let mut keptAttrs : Array Syntax := #[]
  for a in rewrittenAttrs do
    if let some (nameRef, aname, valNode) := matchNamedAttr? a then
      let vT : Term ← if valNode.getNumArgs == 0 then `(Bool.true)
        else liftMacroM <| Qed.Jsx.expandAttrVal valNode (`(""))
      if let some ev := cInfo.events.find? (·.name.toString == aname) then
        outArms := outArms.push { ctor := ev.name, arity := ev.arity, handler := vT }
      else if let some (bStr, valPart, setPart) ← liftMacroM (unpackBindProp aname vT) then
        dataProps := dataProps.push (mkIdentFrom nameRef (Name.mkSimple bStr), valPart)
        outArms := outArms.push { ctor := Name.mkSimple s!"set_{bStr}", arity := 1, handler := setPart }
        keptAttrs := keptAttrs.push (mkJsxAttrExpr bStr valPart)
      else
        let pId := mkIdentFrom nameRef (Name.mkSimple aname)
        if cInfo.propNames.contains pId.getId then dataProps := dataProps.push (pId, vT)
        keptAttrs := keptAttrs.push a
    else
      keptAttrs := keptAttrs.push a
  ctx.hoisted.set (curH.push {
    fieldId := subFieldId, ctorName := subName, info := cInfo, dataProps, outArms })
  let subRoute ← wrapUnaryMsg ctx.wrapMsg? ⟨mkIdent (ctx.msgPath ++ subName)⟩
  return some (rebuildJsxEl stx (keptAttrs.push (mkJsxAttrExpr "_hoist" (← `(($subRoute, $subFieldId))))) kids?)

private def rewriteSchemaFormElement (ctx : RewriteCtx) (inLambda : Bool) (stx : Syntax)
    (tag : String) (sInfo : SchemaFormInfo) (attrNames : Array String)
    (rewrittenPairs : Array (Bool × Syntax)) (kids? : Option Syntax)
    (origBindField? : Option Ident) : CommandElabM (Sum Syntax (Array (Bool × Syntax))) := do
  let schemaFull := sInfo.fullName.getPrefix
  let hasBind := attrNames.contains "bind"
  let mut pairs := rewrittenPairs
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
  if let some (_, resetAttr) := pairs.find? fun (_, a) => (matchNamedAttr? a).any (·.2.1 == "reset") then
    unless ctx.allowHoist do
      throwErrorAt resetAttr s!"<{tag}>: `reset` is only supported inside a `component` view"
    if inLambda then
      throwErrorAt stx s!"<{tag}> with `reset` cannot be mounted inside a loop lambda"
    let some dfId := draftField?
      | throwErrorAt stx s!"<{tag} reset>: `reset` requires either omitted `bind` or `bind=\{stateField}`"
    if hasBind && !ctx.stateFields.contains dfId.getId.eraseMacroScopes then
      throwErrorAt stx s!"<{tag} reset>: `reset` requires `bind=\{stateField}` to refer to a `state` field"
    let resetCond : Term ←
      if (resetAttr.getArg 1).getNumArgs == 0 then `(Bool.true)
      else liftMacroM <| Qed.Jsx.expandAttrVal (resetAttr.getArg 1) (`(Bool.true))
    let some (_, subAttr) := pairs.find? fun (_, a) => (matchNamedAttr? a).any (·.2.1 == "onSubmit")
      | throwErrorAt stx s!"<{tag}> requires `onSubmit=\{...}`"
    unless (subAttr.getArg 1).getNumArgs == 2 do
      throwErrorAt subAttr s!"<{tag}>: `onSubmit` requires a value"
    let subVal ← liftMacroM <| Qed.Jsx.expandAttrVal (subAttr.getArg 1) (`(""))
    let handler ← `(($subVal : _ → $(mkIdent ctx.msgPath)))
    let mut ctxProps : Array (Syntax × String × Term) := #[]
    for (_, a) in pairs do
      if let some (nameRef, nm, valNode) := matchNamedAttr? a then
        if valNode.getNumArgs == 2 && !["key", "bind", "reset", "onSubmit"].contains nm then
          ctxProps := ctxProps.push (nameRef, nm, ← liftMacroM <| Qed.Jsx.expandAttrVal valNode (`("")))
    let ctxArgs ← liftMacroM <| resolveSchemaCtxArgs stx tag sInfo.ctxBinders ctxProps (checkUnknown := false)
    let parseCall ← Qed.Lang.mkAppTerms (mkIdent (`_root_ ++ schemaFull ++ `parse)) ctxArgs
    let curRF ← ctx.resetForms.get
    let ctorName := Name.mkSimple s!"_form_reset_{curRF.size}"
    ctx.resetForms.set (curRF.push { ctorName, draftField := dfId, schemaName := schemaFull, parseCall, resetCond, handler })
    let cid : Term := ⟨mkIdent (ctx.msgPath ++ ctorName)⟩
    let resetMsg ← match ctx.wrapMsg? with | some w => `($w $cid) | none => pure cid
    let resetSub ← `(fun _ => $resetMsg)
    let finalAttrs := pairs.filterMap fun (_, a) =>
      match matchNamedAttr? a with
      | some (_, "reset", _)    => none
      | some (_, "onSubmit", _) => some (mkJsxAttrExpr "onSubmit" resetSub)
      | _                       => some a
    return .inl (rebuildJsxEl stx finalAttrs kids?)
  return .inr pairs

private def rewriteUpperElement (ctx : RewriteCtx) (inLambda : Bool) (stx : Syntax)
    (tag : String) (rewrittenPairs : Array (Bool × Syntax)) (kids? : Option Syntax)
    (origBindField? : Option Ident := none) : CommandElabM Syntax := do
  let rewrittenAttrs := rewrittenPairs.map (·.2)
  if tag == "Await" then
    return rebuildJsxEl stx rewrittenAttrs kids?
  let attrNames := rewrittenAttrs.filterMap fun a => (matchNamedAttr? a).map (·.2.1)
  let hasState := attrNames.contains "state"
  let cName := tag.toName
  if hasState && !attrNames.contains "onMsg" then
    let matching := ctx.collections.filter fun (_, colChild) =>
      colChild.getId == cName || colChild.getId.getString! == cName.getString!
    if matching.size == 1 then
      let colCtor := mkIdent (ctx.msgPath ++ matching[0]!.1.getId)
      let routeExpr : Term ← match ctx.wrapMsg? with
        | some w => `(fun k m => $w ($colCtor k m))
        | none   => pure ⟨colCtor⟩
      return rebuildJsxEl stx (rewrittenAttrs.push (mkJsxAttrExpr "onMsg" routeExpr)) kids?
  let cInfo? ← liftCoreM (lookupComponent? cName)
  if ctx.allowHoist && !hasState then
    if let some cInfo := cInfo? then
      if let some hoistedStx ← rewriteHoistedChild ctx inLambda stx tag cInfo attrNames rewrittenAttrs kids? then
        return hoistedStx
  let sInfo? ← if tag.endsWith ".Form" then liftCoreM (lookupSchemaForm? cName) else pure none
  let mut pairs := rewrittenPairs
  if let some sInfo := sInfo? then
    match ← rewriteSchemaFormElement ctx inLambda stx tag sInfo attrNames pairs kids? origBindField? with
    | .inl doneStx => return doneStx
    | .inr pairs'  => pairs := pairs'
  let evList : Array (String × Nat) :=
    if let some cInfo := cInfo? then cInfo.events.map fun sig => (sig.name.toString, sig.arity)
    else if sInfo?.isSome && ctx.wrapMsg?.isSome then #[("onSubmit", 1)]
    else #[]
  if !evList.isEmpty then
    let attrs' ← wrapEventAttrs pairs (mkIdent ctx.msgPath) ctx.wrapMsg? fun aname => do
      match evList.find? (·.1 == aname) with
      | some (_, arity) => some <$> (List.range arity).toArray.mapM fun _ => `(_)
      | none            => pure none
    return rebuildJsxEl stx attrs' kids?
  return rebuildJsxEl stx (pairs.map (·.2)) kids?

partial def rewriteIn (ctx : RewriteCtx) (inLambda : Bool) (stx : Syntax) : CommandElabM Syntax := do
  let lowerEmitCall (ref : Syntax) (evId : Ident) (rawArgs : Array Syntax) : CommandElabM Term := do
    let evName := evId.getId.eraseMacroScopes
    unless ctx.eventNames.contains evName do
      unless ctx.hasOut do noEmitsErr ref
      throwErrorAt evId s!"unknown `event` `{evName}` in `{evName}.emit(...)`"
    let argTerms ← lowerPosCallArgs ref s!"{evName}.emit(...)" none rawArgs
      (fun e => do lowerCompExpr .val (← rewriteIn ctx inLambda e))
    Qed.Lang.mkAppTerms (mkIdentFrom evId (ctx.compName ++ `Out ++ evName)) argTerms
  let parseOptEmit (opt : Syntax) : CommandElabM (Option Term) := do
    if opt.getNumArgs != 2 then return none
    let emStx := opt.getArg 1
    let some (evId, "emit", rawArgs) := matchIdentMethodCall? emStx
      | throwErrorAt emStx "expected `<event>.emit(...)` after `;` in inline JSX handler"
    some <$> lowerEmitCall emStx evId rawArgs
  let k := stx.getKind
  if k == ``qedRawTerm then
    return stx
  else if k == ``qedLam1 || k == ``qedLamN then
    return Syntax.node .none k (← stx.getArgs.mapM (rewriteIn ctx true))
  else if k == ``qedExprFor then
    let patStx := stx.getArg 1
    let collRaw := (stx.getArg 3)
    let collRewritten ← rewriteIn ctx inLambda collRaw
    let mut bodyRewritten ← rewriteIn ctx true (stx.getArg 5)
    if collRaw.getKind == ``qedIdent && patStx.getKind == ``qedPatIdent && (patStx.getArg 1).getNumArgs == 0 then
      let bindId : Ident := ⟨patStx.getArg 0⟩
      let colName := (collRaw.getArg 0).getId.eraseMacroScopes
      if let some (_, childCompId) := ctx.collections.find? (·.1.getId == colName) then
        if let some cInfo ← liftCoreM (lookupComponent? childCompId.getId) then
          if (← liftCoreM getEnv).contains (cInfo.fullName ++ `keyOf) then
            bodyRewritten ← injectAutoKey bodyRewritten cInfo.fullName bindId
    return Syntax.node .none k #[(stx.getArg 0), patStx, (stx.getArg 2), collRewritten, (stx.getArg 4), bodyRewritten]
  else if k == ``qedStmtExpr then
    let e := stx.getArg 0
    let isHandleOrPush :=
      isCollMutExpr e ||
      (match matchIdentMethodCall? e with
      | some (id, "emit", _) => ctx.eventNames.contains id.getId.eraseMacroScopes
      | some (id, "send", _) =>
          let nm := id.getId.eraseMacroScopes
          ctx.subNames.contains nm || ctx.portOutNames.contains nm
      | _ => false)
    let eCtx := if isHandleOrPush then ctx else { ctx with inPerform := true }
    return Syntax.node stx.getHeadInfo k #[← rewriteIn eCtx inLambda e]
  else if ctx.inPerform && k == ``qedDotIdent then
    let actId := (stx.getArg 1).getId.eraseMacroScopes
    if ctx.actionNames.contains actId then
      return mkRawExpr (mkIdentFrom stx (ctx.msgPath ++ actId))
    else return stx
  else if k == ``qedFieldSetter then
    let fname := (stx.getArg 1).getId.eraseMacroScopes
    checkMutableField ctx (stx.getArg 1) s!"`({fname} = _)`" fname
    return mkRawExpr (← mkSetterHandler ctx fname)
  else if k == ``qedCall then
    match matchIdentMethodCall? stx with
    | some (poId, "send", rawArgs) =>
        if ctx.inPerform && ctx.portOutNames.contains poId.getId.eraseMacroScopes then
          return mkRawExpr (← mkPortSendTerm ctx.compName stx poId poId.getId.eraseMacroScopes rawArgs
            (fun e => do lowerCompExpr .val (← rewriteIn ctx inLambda e)))
    | some (evId, "emit", rawArgs) =>
        if ctx.allowHoist && !ctx.isPureComp && ctx.eventNames.contains evId.getId.eraseMacroScopes then
          return mkRawExpr (← mkSiteExpr ctx #[] (some (← lowerEmitCall stx evId rawArgs)))
    | _ => pure ()
    return Syntax.node stx.getHeadInfo k (← stx.getArgs.mapM (rewriteIn ctx inLambda))
  else if k == ``Qed.Jsx.attrValAssign then
    let mut assigns := #[]
    let more := (stx.getArg 4).getArgs.map fun m =>
      let it := if m.getKind == `Qed.Jsx.jsxAssignItem then m else m[m.getNumArgs - 1]!
      ((it.getArg 0), atomStr (it.getArg 1), (it.getArg 2))
    let op0 := atomStr (stx.getArg 2)
    if more.isEmpty && (stx.getArg 5).getNumArgs == 0 && op0 == "=" && isSomePlaceholder (stx.getArg 3) then
      let fId := (stx.getArg 1)
      let fname := fId.getId.eraseMacroScopes
      checkMutableField ctx fId s!"`{fname}`" fname
      let setter ← mkSiteExpr ctx #[(fname, none)] none
      return mkJsxAttrValNode (← `(fun _v => $setter (some _v)))
    for (fId, op, rhsRaw) in #[((stx.getArg 1), op0, (stx.getArg 3))] ++ more do
      let fname := fId.getId.eraseMacroScopes
      let expr? ← if op == "=" && isPlaceholder rhsRaw then pure none
        else do
          let rw ← rewriteIn ctx inLambda rhsRaw
          let rhsT ← lowerCompExpr .val rw
          some <$> desugarAssign fname op rhsT
      assigns ← pushHandlerAssign ctx assigns fId expr?
    return mkJsxAttrValNode (← mkSiteExpr ctx assigns (← parseOptEmit (stx.getArg 5)))
  else if let some (_, attrName, valNode) := matchAttrValExpr? stx then
    let inner := valNode.getArg 1
    if (attrName == "bind" || attrName.startsWith "bind:") && (inner.getArg 1).getKind == ``qedIdent then
      let fId : Ident := ⟨((inner.getArg 1).getArg 0)⟩
      let fname := fId.getId.eraseMacroScopes
      checkMutableField ctx fId s!"`{attrName}=\{{fname}}`" fname
      let pairT ← `(($fId, $(← mkSetterHandler ctx fname)))
      return Syntax.node .none stx.getKind #[(stx.getArg 0), Syntax.node .none valNode.getKind #[(valNode.getArg 0), mkJsxAttrValNode pairT]]
    return Syntax.node .none k (← stx.getArgs.mapM (rewriteIn ctx inLambda))
  else if k == ``Qed.Jsx.selfClosing || k == ``Qed.Jsx.withChildren then
    let tag := atomStr (stx.getArg 1)
    let kids? ← if k == ``Qed.Jsx.withChildren then some <$> rewriteIn ctx inLambda (stx.getArg 4) else pure none
    let rawAttrs := (stx.getArg 2).getArgs
    let isForm := !tag.isEmpty && tag.front.isUpper && tag.endsWith ".Form"
    let hasReset := isForm && rawAttrs.any fun a => (matchNamedAttr? a).any (·.2.1 == "reset")
    let origBindField? : Option Ident :=
      if isForm then rawAttrs.findSome? fun a => do
        let (_, "bind", valNode) ← matchAttrValExpr? a | none
        let inner := (valNode.getArg 1).getArg 1
        if inner.getKind == ``qedIdent then some ⟨inner.getArg 0⟩ else none
      else none
    let rewrittenPairs ← rawAttrs.mapM fun a => do
      let wasAssign := (matchNamedAttr? a).any fun (_, _, v) => v.getNumArgs == 2 && (v.getArg 1).getKind == ``Qed.Jsx.attrValAssign
      let aCtx := if hasReset && (matchNamedAttr? a).any (·.2.1 == "onSubmit") then { ctx with wrapMsg? := none } else ctx
      return (wasAssign, ← rewriteIn aCtx inLambda a)
    if tag.isEmpty || !tag.front.isUpper then
      return ← rewriteLowerElement ctx stx rewrittenPairs kids?
    return ← rewriteUpperElement ctx inLambda stx tag rewrittenPairs kids? origBindField?
  else if k == ``qedIdent then
    checkRecordRpcIdent ctx (stx.getArg 0).getId
    return stx
  else
    match stx with
    | .node info kind args => return .node info kind (← args.mapM (rewriteIn ctx inLambda))
    | _ => return stx

/-! ## Component Specification Parsing -/

private def requireTyOrDef (role : Name) (fId : Ident) (ty? d? : Option Term) : CommandElabM Unit := do
  if ty?.isNone && d?.isNone then
    throwErrorAt fId s!"`{role} {fId.getId}` needs a type (`: Type`), a default (`= value`), or both"

private def parseCallArgsAndCond (argsStx condStx : Syntax) :
    CommandElabM (Array Term × Option (Term × Term × Array Name) × Array Term) := do
  let rawArgs : Array Term ← argsStx.getSepArgs.mapM (lowerCompExpr .val)
  let (rawPat?, rawGuards) := parseCompIfCond condStx
  let whenPat? ← rawPat?.mapM fun (p, s) => do
    return (← liftMacroM (lowerQedPat p), ← lowerCompExpr .val s, collectQedPatIds p)
  let whenGuards ← rawGuards.mapM (lowerCompExpr .propGuard)
  return (rawArgs, whenPat?, whenGuards)

private def parseRpcQueryClause (acc : ComponentSpec) (cl : Syntax) : CommandElabM ComponentSpec := do
  let qId : Ident := ⟨(cl.getArg 1)⟩
  let explicitTy? ← lowerOptType (cl.getArg 2)
  let rpcId : Ident := ⟨(cl.getArg 4)⟩
  let (rawArgs, whenPat?, whenGuards) ← parseCallArgsAndCond (cl.getArg 6) (cl.getArg 8)
  let (srvInfo, mInfo) ← resolveServerRpc rpcId rawArgs.size "query"
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
        pure (← mkEnsuredExistentialTy qTy ensConst mInfo.paramCount mInfo.paramTypeConsts `_qr_v "_qp_", true)
    | none => pure (qTy, false)
  let qStateTy ← `(Cached $qTy)
  let qStateDef ← `({})
  return { acc with
    states := acc.states.push { id := qId, ty? := some qStateTy, def? := some qStateDef }
    queries := acc.queries.push {
      id := qId, ty := qTy, msgTy,
      rpc := { rpcRef := rpcId, srvInfo, mInfo, args := rawArgs, whenPat?, whenGuards, hasMsgEnsured }
    } }

private def parseSubscribeClause (acc : ComponentSpec) (cl : Syntax) : CommandElabM ComponentSpec := do
  let subId : Ident := ⟨(cl.getArg 1)⟩
  let chanId : Ident := ⟨(cl.getArg 3)⟩
  let (rawArgs, whenPat?, whenGuards) ← parseCallArgsAndCond (cl.getArg 5) (cl.getArg 7)
  let env ← getEnv
  let some chInfo := Qed.lookupChannel? env (← getCurrNamespace) (← getScope).openDecls chanId.getId
    | throwErrorAt chanId s!"unknown WebSocket channel `{chanId.getId}` in `subscribe`"
  if rawArgs.size != chInfo.paramCount then
    throwErrorAt chanId s!"channel `{chanId.getId}` expects {chInfo.paramCount} argument(s), got {rawArgs.size}"
  let mut recPolicy := chInfo.defaultReconnect
  let mut hasRec := false
  let mut onJoin? : Option (Option Syntax × Array Syntax) := none
  let mut onMsg? : Option (Syntax × Array Syntax) := none
  let mut onStatus? : Option (Syntax × Array Syntax) := none
  if (cl.getArg 8).getNumArgs == 2 then
    for h in ((cl.getArg 8).getArg 1).getArgs do
      match h.getKind with
      | .str (.str .anonymous "Qed") "compSubReconnect" =>
        if hasRec then throwErrorAt h s!"duplicate `reconnect` in `subscribe {subId.getId}`"
        hasRec := true
        recPolicy ← liftMacroM <| Qed.parseReconnectExpr (h.getArg 1)
      | .str (.str .anonymous "Qed") "compSubOnJoin" =>
        if onJoin?.isSome then throwErrorAt h s!"duplicate `on_join` in `subscribe {subId.getId}`"
        let binder? := if (h.getArg 1).getNumArgs == 3 then some ((h.getArg 1).getArg 1) else none
        if binder?.isSome && !chInfo.hasJoinSnapshot then
          throwErrorAt h s!"channel `{chanId.getId}` does not return an `on_join` snapshot; write `on_join:` without a parameter"
        onJoin? := some (binder?, suiteStmts (h.getArg 3))
      | .str (.str .anonymous "Qed") "compSubOnMsg" =>
        if onMsg?.isSome then throwErrorAt h s!"duplicate `on_message` in `subscribe {subId.getId}`"
        onMsg? := some ((h.getArg 2), suiteStmts (h.getArg 5))
      | .str (.str .anonymous "Qed") "compSubOnStatus" =>
        if onStatus?.isSome then throwErrorAt h s!"duplicate `on_status` in `subscribe {subId.getId}`"
        onStatus? := some ((h.getArg 2), suiteStmts (h.getArg 5))
      | _ => throwErrorAt h s!"unexpected handler in `subscribe {subId.getId}`"
  let evTyTerm : Term := mkIdentFrom chanId chInfo.eventTypeConst
  let (msgEvTy, hasMsgEnsured) ← match chInfo.ensPredConst with
    | some ensConst =>
        pure (← mkEnsuredExistentialTy evTyTerm ensConst chInfo.paramCount chInfo.paramTypeConsts `_ws_ev "_wp_", true)
    | none => pure (evTyTerm, false)
  let statusTy ← `(Qed.SocketStatus)
  let statusDef ← `(Qed.SocketStatus.disconnected)
  return { acc with
    states := acc.states.push { id := subId, ty? := some statusTy, def? := some statusDef }
    subscriptions := acc.subscriptions.push {
      id := subId, chanRef := chanId, chInfo, args := rawArgs,
      whenPat?, whenGuards, reconnect := recPolicy,
      onJoin?, onMsg?, onStatus?, msgEvTy, hasMsgEnsured
    } }

private def parseCompClause (acc : ComponentSpec) (cl : Syntax) : CommandElabM ComponentSpec := do
  match cl.getKind with
  | .str (.str .anonymous "Qed") s =>
    match s with
    | "compSessionClause" =>
      if acc.sessionField?.isSome then throwErrorAt cl "duplicate `session` clause in component"
      let sfId : Ident := ⟨(cl.getArg 1)⟩
      let sfTy ← (← lowerOptType (cl.getArg 2)).getDM `(Option String)
      return { acc with
        sessionField? := some sfId
        states := acc.states.push { id := sfId, ty? := some sfTy, def? := some (← `(none)) } }
    | "compFieldClause" =>
      let role := (cl.getArg 0).getId
      let fId : Ident := ⟨(cl.getArg 1)⟩
      let rawTy? : Option Syntax := if (cl.getArg 2).getNumArgs == 2 then some ((cl.getArg 2).getArg 1) else none
      let isHtmlProp := role == `prop && match rawTy? with
        | some rt => rt.getKind == ``qedTypeAtom &&
            ((rt.getArg 0).getId.eraseMacroScopes == `Html || (rt.getArg 0).getId.eraseMacroScopes == `Qed.Html) &&
            (rt.getArg 1).getArgs.isEmpty
        | none => false
      let ty? : Option Term ← if isHtmlProp then pure none else rawTy?.mapM lowerTypeStx
      let d?  : Option Term ← if (cl.getArg 3).getNumArgs == 2 then some <$> lowerCompExpr .val ((cl.getArg 3).getArg 1) else pure none
      match role with
      | `prop =>
          if isHtmlProp then
            if fId.getId.eraseMacroScopes == `children then
              throwErrorAt fId "`children` is implicitly available whenever `view:` references `\{children}`; remove `prop children : Html`"
            return { acc with slots := acc.slots.push { id := fId, def? := d? } }
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
            states := acc.states.push { id := fId, ty?, def? := d?, rawTy? }
            ephemeralFields := eph }
    | "compKeyClause" =>
      if acc.keyF?.isSome then throwErrorAt cl "duplicate `key` clause in component"
      return { acc with keyF? := some ⟨(cl.getArg 1)⟩ }
    | "compEventClause" =>
      return { acc with events := acc.events.push { id := ⟨(cl.getArg 1)⟩, params := ← parseParamList (cl.getArg 2) } }
    | "compStartClause" => return { acc with starts := acc.starts.push (cl.getArg 1) }
    | "compRouteClause" =>
      if acc.route?.isSome then throwErrorAt cl "duplicate `route` clause in component"
      let rField : Ident := if (cl.getArg 1).getNumArgs == 1 then ⟨((cl.getArg 1).getArg 0)⟩ else mkIdentFrom cl `route
      let rTy ← lowerTypeStx (cl.getArg 3)
      let rInit ← lowerCompExpr .val (cl.getArg 5)
      let rAlts : Array Syntax := if (cl.getArg 6).getNumArgs == 2 then ((cl.getArg 6).getArg 1).getArgs else #[]
      return { acc with
        route? := some { field := rField, ty := rTy, init := rInit, alts := rAlts }
        states := acc.states.push { id := rField, ty? := some rTy, def? := some rInit } }
    | "compPortOutClause" | "compPortInClause" =>
      let pId : Ident := ⟨(cl.getArg 1)⟩
      if pId.getId.toString.startsWith "__" then
        throwErrorAt pId s!"port name '{pId.getId}' is reserved (names starting with `__`)"
      if s == "compPortOutClause" then
        return { acc with portOuts := acc.portOuts.push { id := pId, ty := ← lowerTypeStx (cl.getArg 3) } }
      else
        return { acc with portIns := acc.portIns.push {
          id := pId, argId := ⟨(cl.getArg 3)⟩, argTy := ← lowerTypeStx (cl.getArg 5), body := (cl.getArg 8) } }
    | "compRpcQueryClause" => parseRpcQueryClause acc cl
    | "compSubscribeClause" => parseSubscribeClause acc cl
    | "compStyleClause" => return { acc with styles := acc.styles.push cl }
    | "compStylesheetClause" =>
      let rawPath := (⟨(cl.getArg 1)⟩ : TSyntax `str).getString
      let normPath := if rawPath.startsWith "/" || rawPath.startsWith "http://" || rawPath.startsWith "https://"
                      then rawPath else "/" ++ rawPath
      unless isSafeUrl normPath do
        throwErrorAt (cl.getArg 1) s!"unsafe stylesheet URL `{rawPath}`: must be a root-relative path (e.g. `\"/app.css\"` or `\"app.css\"`) or `https://`/`http://` URL"
      return { acc with stylesheets := acc.stylesheets.push normPath }
    | "compThemeClause" => return { acc with themes := acc.themes.push ⟨(cl.getArg 1)⟩ }
    | "compHeadClause" =>
      if acc.headClause?.isSome then throwErrorAt cl "duplicate `head:` clause in component"
      return { acc with headClause? := some cl }
    | "compActionClause" => return { acc with actions := acc.actions.push cl }
    | "compInvariantClause" | "compForEachInvClause" | "compExampleClause" =>
        return { acc with invariants := acc.invariants.push cl }
    | _ => return acc
  | _ => return acc

def checkTopLevelMountable (spec : ComponentSpec) (ref : Syntax) (featureDesc : String) :
    CommandElabM Unit := do
  let mut blockers : Array String := #[]
  if !spec.props.isEmpty || !spec.slots.isEmpty then blockers := blockers.push "`prop`"
  if !spec.binds.isEmpty then blockers := blockers.push "`bind`"
  if spec.hasChildren then blockers := blockers.push "`children`"
  if !spec.events.isEmpty then blockers := blockers.push "`event`"
  let uninit := spec.states.filter (·.def?.isNone)
  if !uninit.isEmpty then
    blockers := blockers.push s!"uninitialized `state` ({String.intercalate ", " (uninit.toList.map fun f => s!"`{f.id.getId}`")})"
  if !blockers.isEmpty then
    throwErrorAt ref s!"{featureDesc} is only supported on top-level mountable components, but `{spec.t.getId}` declares {String.intercalate ", " blockers.toList}"

def parseComponentSpec (stx : Syntax) : CommandElabM ComponentSpec := do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if (stx.getArg 0).getNumArgs == 1 then some ⟨((stx.getArg 0).getArg 0)⟩ else none
  let t : Ident := ⟨(stx.getArg 2)⟩
  let bodyStx := stx.getArg 7
  let mut acc : ComponentSpec := { doc?, t, body := bodyStx }
  for cl in (stx.getArg 4).getArgs do
    acc ← parseCompClause acc cl
  let resolvedStates ← if acc.keyF?.isNone then
    acc.states.mapM fun f => do
      let def? ← match f.def?, f.rawTy? with
        | none, some rty => liftMacroM (Qed.Lang.inferQedTypeDefault? rty)
        | d, _           => pure d
      return { f with def? }
  else pure acc.states
  let fieldNames := resolvedStates.map (·.id.getId)
  let allDeclNames := fieldNames ++ acc.props.map (·.id.getId) ++ acc.binds.map (·.id.getId) ++
    acc.slots.map (·.id.getId) ++ acc.events.map (·.id.getId) ++ acc.portOuts.map (·.id.getId)
  let mut seenDecls : Array Name := #[]
  for dn in allDeclNames do
    if seenDecls.contains dn then
      throwErrorAt t s!"duplicate declaration name `{dn}` in component `{t.getId}`; state fields, props, binds, events, and ports must have distinct names"
    seenDecls := seenDecls.push dn
  let hasChildren := !allDeclNames.contains `children && hasFreeIdent `children bodyStx
  let outTy? : Option Term :=
    if !acc.events.isEmpty || !acc.binds.isEmpty then some (mkIdent (t.getId ++ `Out)) else none
  if let some kf := acc.keyF? then
    unless fieldNames.contains kf.getId.eraseMacroScopes do
      throwErrorAt kf s!"`key {kf.getId}`: `{kf.getId}` is not a `state` field of `{t.getId}` ({formatStateFieldList fieldNames})"
    if outTy?.isSome then
      throwErrorAt kf "`key` marks the row identity for parent-owned use, and a parent-owned child's `event` output would have no receiver; drop one of the two"
  let spec : ComponentSpec := { acc with
    states := resolvedStates, hasChildren, outTy?,
    hasProps := !acc.props.isEmpty || !acc.binds.isEmpty,
    invariants := acc.invariants ++ (stx.getArg 8).getArgs }
  if let some q0 := spec.queries[0]? then
    checkTopLevelMountable spec q0.id s!"reactive `query {q0.id.getId}`"
  else if let some s0 := spec.subscriptions[0]? then
    checkTopLevelMountable spec s0.id s!"reactive `subscribe {s0.id.getId}`"
  return spec

def bindMentionedFields (spec : ComponentSpec) (shouldBind : Name → Bool)
    (body : Term) : CommandElabM Term := do
  let mut out := body
  for po in spec.portOuts.reverse do
    if shouldBind po.id.getId then
      let poId := mkIdent po.id.getId
      out ← `(let $poId:ident := $(mkIdent (spec.t.getId ++ po.id.getId)); $out)
  for ev in spec.events.reverse do
    if shouldBind ev.id.getId then
      let evId := mkIdent ev.id.getId
      out ← `(let $evId:ident := $(spec.outCtor ev.id.getId); $out)
  for g in spec.allNames.reverse do
    if shouldBind g then
      let gId := mkIdent g
      out ← if spec.fieldNames.contains g then `(let $gId:ident := (s.$gId:ident); $out)
            else `(let $gId:ident := (p.$gId:ident); $out)
  return out

def lowerMutStmt? (spec : ComponentSpec) (s : Syntax) (strict : Bool) :
    CommandElabM (Option (Name × (Term → CommandElabM Term))) := do
  let checkField (fId : Ident) (fname : Name) : CommandElabM Unit := do
    if strict then
      unless spec.fieldNames.contains fname do
        throwNotMutableStateField fId s!"`{fname}`" fname spec.fieldNames spec.propNames
  let sk := s.getKind
  if sk == ``qedStmtAssign then
    let op := atomStr (s.getArg 1)
    if (s.getArg 0).getKind == ``qedIdent then
      let fId : Ident := ⟨(s.getArg 0).getArg 0⟩
      let fname := fId.getId.eraseMacroScopes
      checkField fId fname
      let valT ← if strict && op == "=" && isPlaceholder (s.getArg 2) then `(v)
                 else desugarAssign fname op (← lowerCompExpr .val (s.getArg 2))
      let fIdent := mkIdent fname
      return some (fname, fun cont => `(let $fIdent:ident := $valT; $cont))
    else if (s.getArg 0).getKind == ``qedIndex && ((s.getArg 0).getArg 0).getKind == ``qedIdent && op == "=" then
      let fId : Ident := ⟨((s.getArg 0).getArg 0).getArg 0⟩
      let fname := fId.getId.eraseMacroScopes
      checkField fId fname
      let idxT ← lowerCompExpr .val ((s.getArg 0).getArg 2)
      let rhsT ← lowerCompExpr .val (s.getArg 2)
      return some (fname, fun cont => lowerArraySetExpr (mkIdent fname) idxT rhsT cont)
    else if strict then
      let lhsStr := stxSnippet (s.getArg 0)
      let what := if lhsStr.isEmpty then "" else s!" `{lhsStr} {op} ...`"
      throwErrorAt s s!"unsupported assignment{what} in component action; expected `field = val`, `field += val`, `field -= val`, or `arr[i] = val`"
    else return none
  else if sk == ``qedStmtExpr then
    let exprStx := s.getArg 0
    let mutCall? :=
      (matchPushCall? exprStx).map (fun (t, a) => (t, a, true, "push", "array", "items.push(x)")) <|>
      (matchRemoveCall? exprStx).map (fun (t, a) => (t, a, false, "remove", "dictionary", "scores.remove(k)"))
    let some (targetStx, argStx, isPush, meth, kindLabel, exStr) := mutCall? | return none
    unless targetStx.getKind == ``qedIdent do
      if strict then
        let tgtStr := stxSnippet targetStx
        let got := if tgtStr.isEmpty then "" else s!", got `{tgtStr}.{meth}(...)`"
        throwErrorAt targetStx s!"{kindLabel} `.{meth}(...)` in component actions requires a simple `state` field (e.g. `{exStr}`){got}"
      return none
    let fId : Ident := ⟨targetStx.getArg 0⟩
    let fname := fId.getId.eraseMacroScopes
    checkField fId fname
    let argT ← lowerCompExpr .val argStx
    let fIdent := mkIdent fname
    let updT ← if isPush then `(($fIdent).push $argT) else `(($fIdent).remove $argT)
    return some (fname, fun cont => `(let $fIdent:ident := $updT; $cont))
  else return none

end CompElab
end Qed
