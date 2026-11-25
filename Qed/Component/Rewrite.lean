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
syntax (name := qedCheckChanSubTerm) "qedCheckChanSub% " ident "[" term,* "]" term:max "(" term "," term "," term "," term ")" : term
syntax (name := qedCheckChanSendTerm) "qedCheckChanSend% " ident "[" term,* "]" str : term

/-! ## Component Spec Structures & Rewriting -/

structure FieldDecl where mk :: (id : Ident) (ty? def? : Option Term := none) (ty : Term := ⟨.missing⟩) (rawTy? : Option Syntax := none)
structure EventDecl where mk :: (id : Ident) (params : Array (Ident × Term))
structure SlotDecl  where mk :: (id : Ident) (def? : Option Term)
structure RouteDecl where mk :: (field : Ident) (ty init : Term) (alts : Array Syntax)
structure CompFnDecl where mk ::
  (id : Ident) (params : Array (Ident × Term)) (retTy? : Option Term := none)
  (stmts : Array Syntax := #[]) (capturedFields : Array Name := #[]) (rawParamTys : Array Syntax := #[])
def CompFnDecl.isPure (f : CompFnDecl) : Bool := f.retTy?.isSome
def CompFnDecl.isMut  (f : CompFnDecl) : Bool := f.retTy?.isNone

inductive ViewGuard where
  | ifCond (cond : Syntax) (isThen : Bool)
  | ifLet (pat scrut : Syntax) (isThen : Bool)
  | matchArm (scruts : Array Syntax) (allArmPats : Array (Array (Array Syntax))) (activeIdx : Nat)

structure HoistedSub where mk ::
  (fieldId : Ident) (ctorName : Name) (info : ComponentInfo) (dataProps : Array (Ident × Term))
  (outArms : Array OutArm) (keyExpr? : Option Term := none) (guards : Array ViewGuard := #[])
def HoistedSub.hasLifecycle (h : HoistedSub) : Bool := h.keyExpr?.isSome || !h.guards.isEmpty
structure ResetFormSub where mk :: (ctorName : Name) (draftField : Ident) (schemaName : Name) (parseCall resetCond handler : Term)
structure SiteAssign where mk :: (field : Name) (path : Array Name := #[]) (val? : Option Term := none) deriving Inhabited
structure SetSite where mk :: (key : String) (ctor : Name) (params : Array (Ident × Term) := #[]) (assigns : Array SiteAssign := #[]) (send? : Option Term := none) (stmts? : Option (Array Syntax) := none)
structure PortOutDecl where mk :: (id : Ident) (ty : Term)
structure PortInDecl  where mk :: (id argId : Ident) (argTy : Term) (body : Syntax)

structure RpcQuerySpec where mk ::
  (rpcRef : Ident) (srvInfo : ServerInfo) (mInfo : ServerMethodInfo) (args : Array Term)
  (whenPat? : Option (Term × Term × Array Name)) (whenGuards : Array Term) (hasMsgEnsured : Bool)
deriving Inhabited

structure QueryDecl where mk :: (id : Ident) (ty msgTy : Term) (rpc : RpcQuerySpec) deriving Inhabited
def QueryDecl.ctorName (q : QueryDecl) : Name := Name.mkSimple s!"_query_{q.id.getId}"

structure SubDecl where mk ::
  (id chanRef : Ident) (chInfo : Qed.ChannelInfo) (args : Array Term)
  (whenPat? : Option (Term × Term × Array Name) := none) (whenGuards : Array Term := #[]) (reconnect : Qed.Reconnect)
  (onJoin? : Option (Option Syntax × Array Syntax) := none) (onMsg? onStatus? : Option (Syntax × Array Syntax) := none)
  (msgEvTy : Term) (hasMsgEnsured : Bool := false)

def SubDecl.ctor (s : SubDecl) (k : String) : Name := Name.mkSimple s!"_ws{k}_{s.id.getId}"

inductive PredictBody where | expr (stx : Syntax) | block (stmts : Array Syntax) deriving Inhabited
inductive EnsuredWrapKind | plain | ensured | optEnsured deriving DecidableEq

def ensuredWrapKind (mInfo : ServerMethodInfo) (catchHasNone : Bool) : EnsuredWrapKind :=
  if !mInfo.hasEnsures then .plain else if mInfo.isOption && !catchHasNone then .optEnsured else .ensured

structure SpecResolveSite where mk ::
  (resCtor : Name) (txIdParam : Ident) (capturedParams : Array (Ident × Term)) (predParam outParam : Ident)
  (mInfo : ServerMethodInfo) (catchHasNone : Bool) (contCtor : Name)
  (confirmCtor? rollbackCtor? catchCtor? : Option Name := none) (callRef : Syntax)

structure SpecDispatchNode where mk ::
  (ref : Syntax) (preCtor? : Option Name := none) (preArgs capturedArgs rpcArgs : Array Term := #[])
  (hoistDefs : Array (Ident × Term × Term) := #[]) (srvInfo : ServerInfo) (mInfo : ServerMethodInfo)
  (catchHasNone : Bool) (predValTy : Term) (innerEnsTy? : Option Term := none) (predBody : PredictBody) (contCtor resCtor : Name)
deriving Inhabited

structure SpecDispatchArm where mk :: (ctor : Name) (params : Array (Ident × Term) := #[]) (stmts : Array Syntax)

structure ComponentSpec where mk ::
  (doc? : Option (TSyntax ``Lean.Parser.Command.docComment) := none) (t : Ident)
  (collections : Array (Ident × Ident) := #[]) (states props binds : Array FieldDecl := #[])
  (ephemeralFields : Array Ident := #[]) (slots : Array SlotDecl := #[]) (hasChildren : Bool := false)
  (events : Array EventDecl := #[]) (keyF? sessionField? : Option Ident := none) (outTy? : Option Term := none)
  (route? : Option RouteDecl := none) (starts actions invariants styles : Array Syntax := #[])
  (fns : Array CompFnDecl := #[])
  (portOuts : Array PortOutDecl := #[]) (portIns : Array PortInDecl := #[])
  (queries : Array QueryDecl := #[]) (subscriptions : Array SubDecl := #[])
  (body : Syntax := .missing) (hoisted : Array HoistedSub := #[]) (resetForms : Array ResetFormSub := #[])
  (hasEffects : Bool := false) (usedRpcs usedChannels : Array (String × String) := #[])
  (stylesheets : Array String := #[]) (themes : Array Ident := #[]) (headClause? : Option Syntax := none)
  (specDispatches : Array SpecDispatchArm := #[]) (specNodes : Array SpecDispatchNode := #[]) (specResolves : Array SpecResolveSite := #[])

def ComponentSpec.hasProps            (s : ComponentSpec) : Bool := !s.props.isEmpty || !s.binds.isEmpty
def ComponentSpec.hasSpeculative      (s : ComponentSpec) : Bool := !s.specResolves.isEmpty
def ComponentSpec.hasAnyQueries       (s : ComponentSpec) : Bool := !s.queries.isEmpty || s.hoisted.any (·.info.hasQueries)
def ComponentSpec.hasAnySubscriptions (s : ComponentSpec) : Bool := !s.subscriptions.isEmpty || s.hoisted.any (·.info.hasSubscriptions)
def ComponentSpec.hasAnySession       (s : ComponentSpec) : Bool := s.sessionField?.isSome || s.hoisted.any (·.info.hasSession)
def ComponentSpec.effectiveSessionField? (s : ComponentSpec) : Option Ident :=
  s.sessionField?.orElse fun _ => if s.hoisted.any (·.info.hasSession) then some (mkIdent `_qed_session) else none
def ComponentSpec.pureFns             (s : ComponentSpec) : Array CompFnDecl := s.fns.filter CompFnDecl.isPure
def ComponentSpec.mutFns              (s : ComponentSpec) : Array CompFnDecl := s.fns.filter CompFnDecl.isMut
def ComponentSpec.pureMutFnNames      (s : ComponentSpec) : Array Name :=
  let evNames := s.events.map (·.id.getId)
  s.mutFns.foldl (init := #[]) fun acc f =>
    if f.stmts.any (hasEffectStmt evNames · acc) then acc else acc.push f.id.getId.eraseMacroScopes
def ComponentSpec.fieldNames     (s : ComponentSpec) : Array Name := s.states.map (·.id.getId)
def ComponentSpec.propNames      (s : ComponentSpec) : Array Name := s.props.map (·.id.getId)
def ComponentSpec.bindNames      (s : ComponentSpec) : Array Name := s.binds.map (·.id.getId)
def ComponentSpec.allNames       (s : ComponentSpec) : Array Name := (s.fieldNames ++ s.propNames ++ s.bindNames).toList.eraseDups.toArray
def ComponentSpec.mountable      (s : ComponentSpec) : Bool := s.states.all (·.def?.isSome)
def ComponentSpec.hasSlotsOrKids (s : ComponentSpec) : Bool := !s.slots.isEmpty || s.hasChildren
def ComponentSpec.id       (s : ComponentSpec) (sub : Name) : Ident := mkIdent (s.t.getId ++ sub)
def ComponentSpec.msgCtor  (s : ComponentSpec) (c : Name)   : Ident := mkIdent (s.t.getId ++ `Msg ++ c)
def ComponentSpec.outCtor  (s : ComponentSpec) (c : Name)   : Ident := mkIdent (s.t.getId ++ `Out ++ c)
def ComponentSpec.stateId  (s : ComponentSpec) : Ident := s.id `State
def ComponentSpec.msgId    (s : ComponentSpec) : Ident := s.id `Msg
def ComponentSpec.propsId  (s : ComponentSpec) : Ident := s.id `Props
def ComponentSpec.initId   (s : ComponentSpec) : Ident := s.id `init
def ComponentSpec.updateId (s : ComponentSpec) : Ident := s.id `update
def ComponentSpec.viewId   (s : ComponentSpec) : Ident := s.id `view

def lowerCompExpr (mode : Qed.Lang.ExprMode) (stx : Syntax) : CommandElabM Term :=
  if mode == .val then do return (← liftMacroM (Qed.Jsx.expandJsxExpr "" none (`(())) stx)).1
  else liftMacroM (Qed.Lang.lowerSimpleQedExpr mode stx)

def lowerPosCallArgs (ref : Syntax) (callDesc : String) (expectedArity? : Option Nat)
    (rawArgs : Array Syntax) (lowerArg : Syntax → CommandElabM Term := lowerCompExpr .val) : CommandElabM (Array Term) := do
  if let some n := expectedArity? then
    if rawArgs.size != n then throwErrorAt ref s!"`{callDesc}` expects {n} argument(s), got {rawArgs.size}"
  rawArgs.mapM fun ra => do
    unless ra.getKind == ``qedCallArgPos do throwErrorAt ra s!"named arguments are not supported in `{callDesc}`"
    lowerArg (ra.getArg 0)

def mkPortSendTerm (compName : Name) (exprStx : Syntax) (targetId : Ident) (portName : Name)
    (rawArgs : Array Syntax) (lowerArg : Syntax → CommandElabM Term := lowerCompExpr .val) : CommandElabM Term := do
  let argTs ← lowerPosCallArgs exprStx s!"{portName}.send(...)" (some 1) rawArgs lowerArg
  `($(mkIdentFrom targetId (compName ++ portName)) $(argTs[0]!))

def parseCompIfCond (optCond : Syntax) : Option (Syntax × Syntax) × Array Syntax :=
  if optCond.getNumArgs != 1 then (none, #[]) else
  let cBody := (optCond.getArg 0).getArg 1
  if cBody.getKind == ``compIfLet then
    (some (cBody.getArg 1, cBody.getArg 3), if (cBody.getArg 4).getNumArgs == 2 then ((cBody.getArg 4).getArg 1).getSepArgs else #[])
  else (none, cBody.getSepArgs)

def inferAwaitBinderTy? (mInfo : ServerMethodInfo) (hasCatchNone : Bool) : CommandElabM (Option Term) := do
  if mInfo.outcomeConst == .anonymous then return none
  let savedMsgs := (← get).messages
  try liftTermElabM do
    let some (.defnInfo dinfo) := (← getEnv).find? mInfo.outcomeConst | return none
    Meta.lambdaTelescope dinfo.value fun _ body => do
      let mut ty ← Meta.whnf body
      if ty.isAppOfArity ``Qed.RpcOutcome 2 || ty.isAppOfArity ``Qed.RpcSimpleOutcome 1 then ty ← Meta.whnf ty.appArg!
      let unwrap (e : Expr) := if e.isAppOfArity ``Qed.Ensured 2 || e.isAppOfArity ``Qed.Field 2 then e.appFn!.appArg! else e
      if mInfo.isOption && ty.isAppOfArity ``Option 1 then
        let u := unwrap (← Meta.whnf ty.appArg!)
        ty ← if hasCatchNone then pure u else Meta.mkAppM ``Option #[u]
      else ty := unwrap ty
      if ty.hasLooseBVars then return none else return some (← PrettyPrinter.delab ty)
  catch _ => modify fun s => { s with messages := savedMsgs }; return none

def resolveServerRpc (rpcId : Ident) (argCount : Nat) (ctxDesc : String) : CommandElabM (ServerInfo × ServerMethodInfo) := do
  let some (srvInfo, mInfo) := lookupServerMethod? (← getEnv) (← getCurrNamespace) (← getScope).openDecls rpcId.getId
    | throwErrorAt rpcId s!"unknown server RPC `{rpcId.getId}` in `{ctxDesc}`"
  if argCount != mInfo.paramCount then throwErrorAt rpcId s!"`{rpcId.getId}` expects {mInfo.paramCount} argument(s), got {argCount}"
  return (srvInfo, mInfo)

def mkBaseCompInfo (spec : ComponentSpec) (kind : CompMountKind) (hasProps : Bool) : CommandElabM ComponentInfo := do
  return {
    fullName := (← getCurrNamespace) ++ spec.t.getId, kind, hasProps,
    propNames := spec.propNames, slotNames := spec.slots.map (·.id.getId), bindNames := spec.bindNames,
    hasChildren := spec.hasChildren, events := spec.events.map fun e => .mk e.id.getId e.params.size,
    rootTag? := staticRootTag? spec.body }

def splitDottedFieldName (fId : Syntax) : Name × Array Name :=
  match fId.getId.eraseMacroScopes.components with
  | [] => (.anonymous, #[])
  | root :: rest => (root, rest.toArray)

partial def parseCompLVal? (stx : Syntax) : Option (Syntax × Name × Array Name) :=
  let k := stx.getKind
  if k == ``qedIdent then
    let (root, rest) := splitDottedFieldName (stx.getArg 0)
    if root.isAnonymous then none else some (stx.getArg 0, root, rest)
  else if k == ``qedProj then
    match parseCompLVal? (stx.getArg 0) with
    | some (ref, root, path) => some (ref, root, path.push (stx.getArg 2).getId.eraseMacroScopes)
    | none => none
  else none

@[noinline]
partial def buildRecordUpdateFrom (cur : Term) (path : Array Name) (mkLeaf : Term → CommandElabM Term) (idx : Nat := 0) : CommandElabM Term := do
  if h : idx < path.size then
    let fId := mkIdent path[idx]
    let inner ← buildRecordUpdateFrom (← `(($cur).$fId:ident)) path mkLeaf (idx + 1)
    `({ $cur with $fId:ident := $inner })
  else mkLeaf cur

@[noinline]
def desugarAssignPath (fname : Name) (path : Array Name) (op : String) (rhs : Term) : CommandElabM Term := do
  let cur ← Qed.Server.foldProjTerms rhs.raw ⟨(mkIdent fname).raw⟩ path.toList
  match op with
  | "="  => pure rhs | "+=" => `(Qed.Lang.QedVal.val $cur + Qed.Lang.QedVal.val ($rhs))
  | "-=" => `(Qed.Lang.QedVal.val $cur - Qed.Lang.QedVal.val ($rhs)) | _ => throwErrorAt rhs s!"unknown assignment operator '{op}'"

/-! ## Unified Single-Ref Rewrite Accumulator & Context -/

structure RewriteAccum where mk ::
  (sites : Array SetSite := #[]) (hoisted : Array HoistedSub := #[]) (formDrafts : Array FieldDecl := #[])
  (resetForms : Array ResetFormSub := #[]) (usedRpcs : Array (String × String) := #[]) (contCounter : Nat := 0)
  (specDispatches : Array SpecDispatchArm := #[]) (specNodes : Array SpecDispatchNode := #[]) (specResolves : Array SpecResolveSite := #[])

structure RewriteCtx where mk ::
  (spec : ComponentSpec) (isPureComp : Bool) (inPerform : Bool := false) (allowHoist : Bool := false)
  (wrapMsg? : Option Ident := none) (guards : Array ViewGuard := #[]) (accum : IO.Ref RewriteAccum)

def RewriteCtx.stateFields (c : RewriteCtx) : Array Name := if c.isPureComp then #[] else c.spec.fieldNames
private def RewriteCtx.hasEv      (c : RewriteCtx) (n : Name) : Bool := !c.isPureComp && c.spec.events.any (·.id.getId == n)
private def RewriteCtx.hasSub     (c : RewriteCtx) (n : Name) : Bool := !c.isPureComp && c.spec.subscriptions.any (·.id.getId == n)
private def RewriteCtx.hasQuery   (c : RewriteCtx) (n : Name) : Bool := !c.isPureComp && c.spec.queries.any (·.id.getId == n)
private def RewriteCtx.hasPortOut (c : RewriteCtx) (n : Name) : Bool := !c.isPureComp && c.spec.portOuts.any (·.id.getId == n)
private def RewriteCtx.hasAct     (c : RewriteCtx) (n : Name) : Bool := !c.isPureComp && (c.spec.actions.any (·[1].getId == n) || c.spec.portIns.any (·.id.getId == n))

def mkRewriteCtx (spec : ComponentSpec) (isPureComp : Bool) (allowHoist : Bool := false) : CommandElabM RewriteCtx := do
  return .mk spec isPureComp false allowHoist none #[] (← IO.mkRef {})

private def registerKeyedSite (accum : IO.Ref RewriteAccum) (key base : String) (mkSite : Name → SetSite) : CommandElabM Name := do
  let cur := (← accum.get).sites
  if let some site := cur.find? (·.key == key) then return site.ctor
  let mut name := Name.mkSimple base; let mut i := 2
  while cur.any (·.ctor == name) do name := Name.mkSimple s!"{base}_{i}"; i := i + 1
  accum.modify fun a => { a with sites := a.sites.push (mkSite name) }
  return name

def registerSite (accum : IO.Ref RewriteAccum) (assigns : Array SiteAssign) (send? : Option Term) : CommandElabM Name := do
  let pp : Option Term → String := fun | some e => e.raw.reprint.getD (toString e.raw) | none => "_"
  let fmtPath (a : SiteAssign) := if a.path.isEmpty then toString a.field else String.intercalate "." (toString a.field :: a.path.toList.map toString)
  let key := String.intercalate "|" (assigns.toList.map fun a => s!"{fmtPath a}={pp a.val?}") ++ s!"|{pp send?}"
  let base := if assigns.isEmpty then "send" else "set_" ++ String.intercalate "_" (assigns.toList.map fun a => String.intercalate "_" (toString a.field :: a.path.toList.map toString))
  registerKeyedSite accum key base fun ctor => { key, assigns, ctor, send? }

def recordUsedRpc (accum : IO.Ref RewriteAccum) (srv m : String) : IO Unit :=
  accum.modify fun a => { a with usedRpcs := pushUnique a.usedRpcs (srv, m) }

def lowerLetStmt (st : Syntax) (lowerVal : Syntax → CommandElabM Term) (cont : Term) : CommandElabM Term := do
  let rhsT ← lowerVal (st.getArg 4)
  if (st.getArg 1).isIdent then
    let lId : Ident := ⟨st.getArg 1⟩
    match ← lowerOptType (st.getArg 2) with
    | some lTy => `(let $lId:ident : $lTy := $rhsT; $cont) | none => `(let $lId:ident := $rhsT; $cont)
  else `(let _ := $rhsT; $cont)

syntax (name := qedCompSetAtStx) "qedCompSetAt(" ident ", " term ", " term ")" : term

open Lean Meta Elab Term in
@[term_elab qedCompSetAtStx] def elabQedCompSetAt : TermElab := fun stx expectedType? => do
  let (fId, idxStx, valStx) : Ident × Term × Term := (⟨stx.getArg 1⟩, ⟨stx.getArg 3⟩, ⟨stx.getArg 5⟩)
  let arrExpr ← elabTerm fId none; synthesizeSyntheticMVarsNoPostponing
  if (← whnf (← instantiateMVars (← inferType arrExpr))).isAppOfArity `Qed.Dict 2 then
    elabTerm (← `($(mkIdentFrom stx `Qed.Dict.set) $fId $idxStx $valStx)) expectedType?
  else
    elabTerm (← `(($fId).set $idxStx $valStx (by first | get_elem_tactic | (simp (config := { zetaDelta := false }) only [$fId:ident, Array.size_set, Array.size_push] <;> omega) | (simp (config := { zetaDelta := true }) only [Array.size_set, Array.size_push] <;> omega)))) expectedType?

def lowerControlFlowStmt (st : Syntax) (lowerVal : Syntax → CommandElabM Term)
    (lowerBranch : Array Syntax → CommandElabM Term) : CommandElabM Term := do
  let k := st.getKind
  if k == ``qedStmtIf then
    let (cond, tT, eT) := (← lowerCompExpr .propGuard (st.getArg 1), ← lowerBranch (suiteStmts (st.getArg 3)), ← lowerBranch ((desugarElifs (st.getArg 4).getArgs (st.getArg 5)).getD #[]))
    `(if $(mkIdent `_qedIf):ident : $cond then $tT else $eT)
  else if k == ``qedStmtIfLet then
    let (pat, scrut, tT, eT) := (← liftMacroM (lowerQedPat (st.getArg 2)), ← lowerVal (st.getArg 4), ← lowerBranch (suiteStmts (st.getArg 6)), ← lowerBranch ((extractElseSuite (st.getArg 7)).getD #[]))
    `(match $(mkIdent `_qedIfLet):ident : $scrut:term with | $pat:term => $tT | _ => $eT)
  else
    let scruts ← (st.getArg 1).getSepArgs.mapM lowerVal
    let alts ← (st.getArg 3).getArgs.mapM fun alt => do
      mkMatchAltFromAlts (← liftMacroM (lowerCasePatAlts (alt.getArg 1))) (← lowerBranch (suiteStmts (alt.getArg 3)))
    `(match $[$scruts:term],* with $[$alts:matchAlt]*)

private def wrapEnsuredMsgTy (valTy : Term) (ensConst? : Option Name) (paramCount : Nat)
    (paramTypeConsts : Array Name) (valVar : Name) (paramPfx : String) : CommandElabM (Term × Bool) := do
  let some ensConst := ensConst? | return (valTy, false)
  let vId := mkIdent valVar; let pIds := (Array.range paramCount).map fun i => mkIdent (.mkSimple s!"{paramPfx}{i}")
  let ensApp ← Qed.Lang.mkAppTerms (mkIdent ensConst) ((pIds.push vId).map (⟨·.raw⟩))
  let exBody ← (pIds.zip paramTypeConsts).foldrM (init := ensApp) fun (pId, pTy) acc => `(∃ ($pId:ident : $(mkIdent pTy)), $acc)
  return (← `(Qed.Ensured $valTy (fun ($vId:ident : $valTy) => $exBody)), true)

private def checkRecordRpcIdent (ctx : RewriteCtx) (id : Name) : CommandElabM Unit := do
  if ctx.inPerform || (match id.eraseMacroScopes with | .str p _ => !p.isAnonymous | _ => false) then
    if let some (srvInfo, mInfo) := lookupServerMethod? (← getEnv) (← getCurrNamespace) (← getScope).openDecls id then
      recordUsedRpc ctx.accum srvInfo.shortName mInfo.name

private def wrapMsgArity (wrap? : Option Ident) (arity : Nat) (fn : Term) : CommandElabM Term := do
  let some w := wrap? | return fn
  if arity == 0 then `($w $fn) else
  let argIds := (Array.range arity).map fun i => mkIdent (Name.mkSimple s!"_ea{i}")
  let wrapped ← `($w $(← Qed.Lang.mkAppTerms fn (argIds.map (⟨·.raw⟩))))
  argIds.foldrM (init := wrapped) fun arg acc => `(fun $arg => $acc)

private def expandAttrValM (valNode : Syntax) (fallback : Term) : CommandElabM Term :=
  liftMacroM <| Qed.Jsx.expandAttrVal valNode (pure fallback)

def mkSetterHandler (ctx : RewriteCtx) (fname : Name) (path : Array Name := #[]) : CommandElabM Term := do
  if ctx.spec.bindNames.contains fname then
    let sf := mkIdent (bindSetName fname)
    if path.isEmpty && ctx.isPureComp then return ← `(p.$sf:ident)
    let valT ← if path.isEmpty then `(v) else buildRecordUpdateFrom ⟨(mkIdent fname).raw⟩ path (fun _ => `(v))
    if ctx.isPureComp then return ← `(fun v => p.$sf:ident $valT)
    let call ← wrapMsgArity ctx.wrapMsg? 0 (← `($(ctx.spec.msgCtor `_emit) ($(ctx.spec.outCtor (bindSetName fname)) $valT)))
    return ← `(fun v => $call)
  wrapMsgArity ctx.wrapMsg? 1 ⟨ctx.spec.msgCtor (← registerSite ctx.accum #[.mk fname path none] none)⟩

def mkSiteExpr (ctx : RewriteCtx) (assigns : Array SiteAssign) (send? : Option Term) : CommandElabM Term := do
  let wrapVal (a : SiteAssign) (v : Term) : CommandElabM Term :=
    if a.path.isEmpty then pure v else buildRecordUpdateFrom ⟨(mkIdent a.field).raw⟩ a.path (fun _ => pure v)
  if ctx.isPureComp then
    if let #[a] := assigns then
      if ctx.spec.bindNames.contains a.field && send?.isNone then
        return ← match a.val? with
          | none => mkSetterHandler ctx a.field a.path
          | some v => do `(p.$(mkIdent (bindSetName a.field)):ident $(← wrapVal a v))
  let mut stAssigns : Array SiteAssign := #[]; let mut bindSend? := send?; let mut bindDot? : Option (Name × Array Name) := none
  for a in assigns do
    if ctx.spec.bindNames.contains a.field then
      match a.val? with
      | some v => bindSend? := some (← `($(ctx.spec.outCtor (bindSetName a.field)) $(← wrapVal a v)))
      | none => bindDot? := some (a.field, a.path)
    else stAssigns := stAssigns.push a
  if let some (bfn, bpath) := bindDot? then if stAssigns.isEmpty && bindSend?.isNone then return ← mkSetterHandler ctx bfn bpath
  let cid : Term := ⟨ctx.spec.msgCtor (← registerSite ctx.accum stAssigns bindSend?)⟩
  wrapMsgArity ctx.wrapMsg? (if stAssigns.any (·.val?.isNone) then 1 else 0) cid

def formatStateFieldList (fields : Array Name) : String :=
  if fields.isEmpty then "this component has no `state` fields"
  else s!"`state` fields: {String.intercalate ", " (fields.toList.map fun n => s!"`{n}`")}"

def throwNotMutableStateField (ref : Syntax) (prefixMsg : String) (fname : Name) (stateFields propNames : Array Name) : CommandElabM Unit := do
  let lead := if prefixMsg == s!"`{fname}`" then s!"`{fname}`" else s!"{prefixMsg}: `{fname}`"
  if propNames.contains fname then throwErrorAt ref s!"{lead} is a read-only `prop` and cannot be assigned ({formatStateFieldList stateFields})"
  else throwErrorAt ref s!"{lead} is not a `state` field of this component{Qed.Diag.didYouMean fname.toString (stateFields.toList.map toString)} ({formatStateFieldList stateFields})"

def checkMutableField (ctx : RewriteCtx) (ref : Syntax) (prefixMsg : String) (fname : Name) : CommandElabM Unit := do
  unless ctx.stateFields.contains fname || ctx.spec.bindNames.contains fname do
    throwNotMutableStateField ref prefixMsg fname ctx.stateFields ctx.spec.propNames

def pushHandlerAssign (ctx : RewriteCtx) (assigns : Array SiteAssign) (fId : Syntax) (expr? : Option Term) : CommandElabM (Array SiteAssign) := do
  let (fname, path) := splitDottedFieldName fId
  checkMutableField ctx fId s!"`{fname}`" fname
  if assigns.any (fun a => a.field == fname && a.path == path) then throwErrorAt fId s!"`{fId.getId.eraseMacroScopes}`: this handler already updates `{fId.getId.eraseMacroScopes}`"
  if expr?.isNone && assigns.any (·.val?.isNone) then throwErrorAt fId s!"`{fId.getId.eraseMacroScopes} = _`: only one `_` placeholder per handler"
  return assigns.push (.mk fname path expr?)

def noEmitsErr (ref : Syntax) : CommandElabM Unit :=
  throwErrorAt ref "`.emit(...)` bubbles an output, but this component declares no output event; add `event name` between the `state` fields and the `view`"

private def unitEvents : List String := ["onClick", "onSubmit", "onBlur", "onFocus", "onDoubleClick", "onMouseDown", "onMouseUp"]
private def strEvents  : List String := ["onInput", "onChange", "onKeydown", "onKeyup"]

private def wrapEventAttrs (pairs : Array (Bool × Syntax)) (msgTy : Ident) (wrapMsg? : Option Ident)
    (lookupArgTys : String → CommandElabM (Option (Array Term))) : CommandElabM (Array Syntax) :=
  pairs.mapM fun (wasAssign, a') => do
    if !wasAssign then
      if let some (_, aname, valNode) := matchAttrValExpr? a' then
        if let some argTys ← lookupArgTys aname then
          let evTy ← argTys.foldrM (init := (msgTy : Term)) fun aTy acc => `($aTy → $acc)
          return mkJsxAttrExpr aname (← wrapMsgArity wrapMsg? argTys.size (← `(($(← expandAttrValM valNode (← `(""))) : $evTy))))
    return a'

private def injectAutoKey (bodyStx : Syntax) (compFullName : Name) (bindId : Ident) : CommandElabM Syntax := do
  if bodyStx.getKind == ``Qed.Jsx.qedExprJsx then
    let el := bodyStx.getArg 0; let ek := el.getKind
    if ek == ``Qed.Jsx.selfClosing || ek == ``Qed.Jsx.withChildren then
      let attrs := (el.getArg 2).getArgs
      if !attrs.any (attrNamed "key") then
        let kids? := if ek == ``Qed.Jsx.withChildren then some (el.getArg 4) else none
        return Syntax.node .none ``Qed.Jsx.qedExprJsx #[rebuildJsxEl el (attrs.push (mkJsxAttrExpr "key" (← `($(mkIdent (compFullName ++ `keyOf)) $bindId)))) kids?]
  return bodyStx

private def isSomePlaceholder (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx
  u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId.eraseMacroScopes == `some &&
  (u.getArg 2).getSepArgs.size == 1 && (u.getArg 2).getSepArgs[0]!.getKind == ``qedCallArgPos && isPlaceholder (u.getArg 2).getSepArgs[0]![0]

private def rewriteHoistedChild (ctx : RewriteCtx) (inLambda : Bool) (stx : Syntax) (tag : String)
    (cInfo : ComponentInfo) (attrNames : Array String) (rewrittenAttrs : Array Syntax) (kids? : Option Syntax) : CommandElabM (Option Syntax) := do
  let mustHoist := !cInfo.hasLocalDef || cInfo.hasSession || attrNames.any (·.startsWith "bind:") || cInfo.hasChildren || !cInfo.slotNames.isEmpty
  unless cInfo.kind == .stateful && cInfo.mountable && (mustHoist || (!inLambda && !attrNames.contains "key" && !attrNames.contains "initial")) do return none
  if inLambda && mustHoist then
    throwErrorAt stx s!"<{tag}> uses effects, `Html` props, `children`, or `bind:` and cannot be dynamically mounted inside a loop lambda; hoist its state into the parent or use `collection`"
  let subName := Name.mkSimple s!"_sub_{(← ctx.accum.get).hoisted.size}"; let subFieldId := mkIdentFrom stx subName
  let mut dataProps : Array (Ident × Term) := #[]; let mut outArms : Array OutArm := #[]; let mut keptAttrs : Array Syntax := #[]
  let mut keyExpr? : Option Term := none
  for a in rewrittenAttrs do
    if let some (nameRef, aname, valNode) := matchNamedAttr? a then
      let vT : Term ← if valNode.getNumArgs == 0 then `(Bool.true) else expandAttrValM valNode (← `(""))
      if aname == "key" then
        keyExpr? := some vT
        keptAttrs := keptAttrs.push a
      else if let some ev := cInfo.events.find? (·.name.toString == aname) then outArms := outArms.push (.mk ev.name ev.arity vT)
      else if let some (bStr, valPart, setPart) ← liftMacroM (unpackBindProp aname vT) then
        let bNm := Name.mkSimple bStr
        dataProps := dataProps.push (mkIdentFrom nameRef bNm, valPart)
        outArms := outArms.push (.mk (bindSetName bNm) 1 setPart); keptAttrs := keptAttrs.push (mkJsxAttrExpr bStr valPart)
      else
        let pId := mkIdentFrom nameRef (Name.mkSimple aname)
        if cInfo.propNames.contains pId.getId then dataProps := dataProps.push (pId, vT)
        keptAttrs := keptAttrs.push a
    else keptAttrs := keptAttrs.push a
  ctx.accum.modify fun a => { a with hoisted := a.hoisted.push (.mk subFieldId subName cInfo dataProps outArms keyExpr? ctx.guards) }
  let subRoute ← wrapMsgArity ctx.wrapMsg? 1 ⟨ctx.spec.msgCtor subName⟩
  return some (rebuildJsxEl stx (keptAttrs.push (mkJsxAttrExpr "_hoist" (← `(($subRoute, $subFieldId))))) kids?)

private def rewriteSchemaFormElement (ctx : RewriteCtx) (inLambda : Bool) (stx : Syntax) (tag : String) (sInfo : SchemaFormInfo)
    (attrNames : Array String) (rewrittenPairs : Array (Bool × Syntax)) (kids? : Option Syntax) (origBindField? : Option Ident) :
    CommandElabM (Sum Syntax (Array (Bool × Syntax))) := do
  let (schemaFull, hasBind) := (sInfo.fullName.getPrefix, attrNames.contains "bind")
  let mut pairs := rewrittenPairs; let mut draftField? := origBindField?
  if !hasBind then
    unless ctx.allowHoist do throwErrorAt stx s!"<{tag}> requires `bind=\{draft}` here"
    if inLambda then throwErrorAt stx s!"<{tag}> without `bind=` hoists internal draft state and cannot be mounted inside a loop lambda; declare `state draft = ...` and pass `bind=\{draft}`"
    let fName := Name.mkSimple s!"_form_{(← ctx.accum.get).formDrafts.size}"; let fId := mkIdentFrom stx fName
    let draftTy := mkIdentFrom stx (`_root_ ++ schemaFull ++ `Draft)
    ctx.accum.modify fun a => { a with formDrafts := a.formDrafts.push (.mk fId (some draftTy) (some (mkIdentFrom stx (`_root_ ++ schemaFull ++ `Draft ++ `empty))) draftTy none) }
    let editFn ← wrapMsgArity ctx.wrapMsg? 1 ⟨ctx.spec.msgCtor (← registerSite ctx.accum #[.mk fName #[] none] none)⟩
    pairs := pairs.push (false, mkJsxAttrExpr "bind" (← `(($fId, $editFn)))); draftField? := some fId
  let findAttr (nm : String) := pairs.find? (attrNamed nm ·.2)
  if let some (_, resetAttr) := findAttr "reset" then
    unless ctx.allowHoist do throwErrorAt resetAttr s!"<{tag}>: `reset` is only supported inside a `component` view"
    if inLambda then throwErrorAt stx s!"<{tag}> with `reset` cannot be mounted inside a loop lambda"
    let some dfId := draftField? | throwErrorAt stx s!"<{tag} reset>: `reset` requires either omitted `bind` or `bind=\{stateField}`"
    if hasBind && !ctx.stateFields.contains dfId.getId.eraseMacroScopes then throwErrorAt stx s!"<{tag} reset>: `reset` requires `bind=\{stateField}` to refer to a `state` field"
    let resetCond : Term ← if (resetAttr.getArg 1).getNumArgs == 0 then `(Bool.true) else expandAttrValM (resetAttr.getArg 1) (← `(Bool.true))
    let some (_, subAttr) := findAttr "onSubmit" | throwErrorAt stx s!"<{tag}> requires `onSubmit=\{...}`"
    unless (subAttr.getArg 1).getNumArgs == 2 do throwErrorAt subAttr s!"<{tag}>: `onSubmit` requires a value"
    let handler ← `(($(← expandAttrValM (subAttr.getArg 1) (← `(""))) : _ → $(ctx.spec.msgId)))
    let ctxProps ← pairs.filterMapM fun (_, a) => do
      let some (ref, nm, vn) := matchNamedAttr? a | return none
      if vn.getNumArgs == 2 && !["key", "bind", "reset", "onSubmit"].contains nm then return some (ref, nm, ← expandAttrValM vn (← `(""))) else return none
    let parseCall ← Qed.Lang.mkAppTerms (mkIdent (`_root_ ++ schemaFull ++ `parse)) (← liftMacroM <| resolveSchemaCtxArgs stx tag sInfo.ctxBinders ctxProps (checkUnknown := false))
    let ctorName := Name.mkSimple s!"_form_reset_{(← ctx.accum.get).resetForms.size}"
    ctx.accum.modify fun a => { a with resetForms := a.resetForms.push (.mk ctorName dfId schemaFull parseCall resetCond handler) }
    let resetSub ← `(fun _ => $(← wrapMsgArity ctx.wrapMsg? 0 ⟨ctx.spec.msgCtor ctorName⟩))
    let finalAttrs := pairs.filterMap fun (_, a) => match matchNamedAttr? a with
      | some (_, "reset", _) => none | some (_, "onSubmit", _) => some (mkJsxAttrExpr "onSubmit" resetSub) | _ => some a
    return .inl (rebuildJsxEl stx finalAttrs kids?)
  return .inr pairs

private def rewriteUpperElement (ctx : RewriteCtx) (inLambda : Bool) (stx : Syntax) (tag : String)
    (rewrittenPairs : Array (Bool × Syntax)) (kids? : Option Syntax) (origBindField? : Option Ident := none) : CommandElabM Syntax := do
  let rewrittenAttrs := rewrittenPairs.map (·.2)
  if tag == "Await" then return rebuildJsxEl stx rewrittenAttrs kids?
  let attrNames := rewrittenAttrs.filterMap fun a => (matchNamedAttr? a).map (·.2.1)
  let (hasState, cName) := (attrNames.contains "state", tag.toName)
  if !ctx.isPureComp && hasState && !attrNames.contains "onMsg" then
    let matching := ctx.spec.collections.filter fun (_, colChild) => colChild.getId == cName || colChild.getId.getString! == cName.getString!
    if matching.size == 1 then
      return rebuildJsxEl stx (rewrittenAttrs.push (mkJsxAttrExpr "onMsg" (← wrapMsgArity ctx.wrapMsg? 2 ⟨ctx.spec.msgCtor matching[0]!.1.getId⟩))) kids?
  let cInfo? ← liftCoreM (lookupComponent? cName)
  if ctx.allowHoist && !hasState then
    if let some cInfo := cInfo? then
      if let some hoistedStx ← rewriteHoistedChild ctx inLambda stx tag cInfo attrNames rewrittenAttrs kids? then return hoistedStx
  let sInfo? ← if tag.endsWith ".Form" then liftCoreM (lookupSchemaForm? cName) else pure none
  let mut pairs := rewrittenPairs
  if let some sInfo := sInfo? then
    match ← rewriteSchemaFormElement ctx inLambda stx tag sInfo attrNames pairs kids? origBindField? with
    | .inl doneStx => return doneStx | .inr pairs' => pairs := pairs'
  if !ctx.isPureComp then
    let evList : Array (String × Nat) :=
      if let some cInfo := cInfo? then cInfo.events.map fun sig => (sig.name.toString, sig.arity)
      else if sInfo?.isSome && ctx.wrapMsg?.isSome then #[("onSubmit", 1)] else #[]
    if !evList.isEmpty then
      let attrs' ← wrapEventAttrs pairs ctx.spec.msgId ctx.wrapMsg? fun aname => do
        match evList.find? (·.1 == aname) with | some (_, arity) => some <$> (Array.range arity).mapM fun _ => `(_) | none => pure none
      return rebuildJsxEl stx attrs' kids?
  return rebuildJsxEl stx (pairs.map (·.2)) kids?

partial def rewriteIn (ctx : RewriteCtx) (inLambda : Bool) (stx : Syntax) : CommandElabM Syntax := do
  let lowerEmitCall (ref : Syntax) (evId : Ident) (rawArgs : Array Syntax) : CommandElabM Term := do
    let evName := evId.getId.eraseMacroScopes
    unless ctx.hasEv evName do
      unless !ctx.isPureComp && ctx.spec.outTy?.isSome do noEmitsErr ref
      throwErrorAt evId s!"unknown `event` `{evName}` in `{evName}.emit(...)`"
    let argTerms ← lowerPosCallArgs ref s!"{evName}.emit(...)" none rawArgs (fun e => do lowerCompExpr .val (← rewriteIn ctx inLambda e))
    Qed.Lang.mkAppTerms (mkIdentFrom evId (ctx.spec.t.getId ++ `Out ++ evName)) argTerms
  let k := stx.getKind
  if k == ``qedRawTerm then return stx
  else if k == ``qedLam1 || k == ``qedLamN then return Syntax.node .none k (← stx.getArgs.mapM (rewriteIn ctx true))
  else if k == ``qedExprFor then
    let (patStx, collRaw) := (stx.getArg 1, stx.getArg 3)
    let collRewritten ← rewriteIn ctx inLambda collRaw; let mut bodyRewritten ← rewriteIn ctx true (stx.getArg 5)
    if !ctx.isPureComp && collRaw.getKind == ``qedIdent && patStx.getKind == ``qedPatIdent && (patStx.getArg 1).getNumArgs == 0 then
      if let some (_, childCompId) := ctx.spec.collections.find? (·.1.getId == (collRaw.getArg 0).getId.eraseMacroScopes) then
        if let some cInfo ← liftCoreM (lookupComponent? childCompId.getId) then
          if (← liftCoreM getEnv).contains (cInfo.fullName ++ `keyOf) then
            bodyRewritten ← injectAutoKey bodyRewritten cInfo.fullName ⟨patStx.getArg 0⟩
    return Syntax.node .none k #[stx.getArg 0, patStx, stx.getArg 2, collRewritten, stx.getArg 4, bodyRewritten]
  else if k == ``qedExprIf then
    let cond' ← rewriteIn ctx inLambda (stx.getArg 1)
    let then' ← rewriteIn { ctx with guards := ctx.guards.push (.ifCond cond' true) } inLambda (stx.getArg 3)
    let optE := stx.getArg 4
    let optE' ← if optE.getNumArgs == 3 then
        let e' ← rewriteIn { ctx with guards := ctx.guards.push (.ifCond cond' false) } inLambda (optE.getArg 2)
        pure (setStxArg optE 2 e')
      else pure optE
    return Syntax.node stx.getHeadInfo k #[stx.getArg 0, cond', stx.getArg 2, then', optE']
  else if k == ``qedTernary then
    let cond' ← rewriteIn ctx inLambda (stx.getArg 2)
    let then' ← rewriteIn { ctx with guards := ctx.guards.push (.ifCond cond' true) } inLambda (stx.getArg 0)
    let optE := stx.getArg 3
    let optE' ← if optE.getNumArgs == 2 then
        let e' ← rewriteIn { ctx with guards := ctx.guards.push (.ifCond cond' false) } inLambda (optE.getArg 1)
        pure (setStxArg optE 1 e')
      else pure optE
    return Syntax.node stx.getHeadInfo k #[then', stx.getArg 1, cond', optE']
  else if k == ``qedExprIfLet then
    let pat := stx.getArg 2; let scrut' ← rewriteIn ctx inLambda (stx.getArg 4)
    let then' ← rewriteIn { ctx with guards := ctx.guards.push (.ifLet pat scrut' true) } inLambda (stx.getArg 6)
    let optE := stx.getArg 7
    let optE' ← if optE.getNumArgs == 3 then
        let e' ← rewriteIn { ctx with guards := ctx.guards.push (.ifLet pat scrut' false) } inLambda (optE.getArg 2)
        pure (setStxArg optE 2 e')
      else pure optE
    return Syntax.node stx.getHeadInfo k #[stx.getArg 0, stx.getArg 1, pat, stx.getArg 3, scrut', stx.getArg 5, then', optE']
  else if k == ``qedExprMatch then
    let scrutsNode := stx.getArg 1
    let scrutsNode' ← rewriteIn ctx inLambda scrutsNode
    let scrutsRewritten := scrutsNode'.getSepArgs
    let casesNode := stx.getArg 3
    let rawCases := casesNode.getArgs
    let allArmPats := rawCases.map fun c => extractCasePatAlts (c.getArg 1)
    let cases' ← rawCases.zipIdx.mapM fun (c, idx) => do
      let b' ← rewriteIn { ctx with guards := ctx.guards.push (.matchArm scrutsRewritten allArmPats idx) } inLambda (c.getArg 3)
      pure (setStxArg c 3 b')
    return Syntax.node stx.getHeadInfo k #[stx.getArg 0, scrutsNode', stx.getArg 2, Syntax.node casesNode.getHeadInfo casesNode.getKind cases']
  else if k == ``qedStmtExpr then
    let e := stx.getArg 0
    let isHandleOrPush := isCollMutExpr e || isPlainCallTo (ctx.spec.mutFns.map (·.id.getId.eraseMacroScopes)) e || match matchIdentMethodCall? e with
      | some (id, "emit", _) => ctx.hasEv id.getId.eraseMacroScopes
      | some (id, "send", _) => let nm := id.getId.eraseMacroScopes; ctx.hasSub nm || ctx.hasPortOut nm
      | some (id, m, _) => ["refetch", "invalidate", "update", "set"].contains m && ctx.hasQuery id.getId.eraseMacroScopes
      | _ => false
    return Syntax.node stx.getHeadInfo k #[← rewriteIn (if isHandleOrPush then ctx else { ctx with inPerform := true }) inLambda e]
  else if ctx.inPerform && k == ``qedDotIdent then
    let actId := (stx.getArg 1).getId.eraseMacroScopes
    return if ctx.hasAct actId then mkRawExpr (mkIdentFrom stx (ctx.spec.t.getId ++ `Msg ++ actId)) else stx
  else if k == ``qedFieldSetter then
    let (fname, path) := splitDottedFieldName (stx.getArg 1)
    checkMutableField ctx (stx.getArg 1) s!"`({(stx.getArg 1).getId.eraseMacroScopes} = _)`" fname
    return mkRawExpr (← mkSetterHandler ctx fname path)
  else if k == ``qedCall then
    match matchIdentMethodCall? stx with
    | some (poId, "send", rawArgs) =>
        if ctx.inPerform && ctx.hasPortOut poId.getId.eraseMacroScopes then
          return mkRawExpr (← mkPortSendTerm ctx.spec.t.getId stx poId poId.getId.eraseMacroScopes rawArgs (fun e => do lowerCompExpr .val (← rewriteIn ctx inLambda e)))
    | some (evId, "emit", rawArgs) =>
        if ctx.allowHoist && ctx.hasEv evId.getId.eraseMacroScopes then
          return mkRawExpr (← mkSiteExpr ctx #[] (some (← lowerEmitCall stx evId rawArgs)))
    | some (qId, qMeth, rawArgs) =>
        if ctx.allowHoist && (qMeth == "refetch" || qMeth == "invalidate") && rawArgs.isEmpty && ctx.hasQuery qId.getId.eraseMacroScopes then
          let qNm := qId.getId.eraseMacroScopes
          let key := s!"qctrl:{qNm}.{qMeth}"
          let ctor ← registerKeyedSite ctx.accum key s!"q_{qNm}_{qMeth}" fun ctor =>
            { key, ctor, stmts? := some #[Syntax.node stx.getHeadInfo ``qedStmtExpr #[stx]] }
          return mkRawExpr (← wrapMsgArity ctx.wrapMsg? 0 ⟨ctx.spec.msgCtor ctor⟩)
    | _ => pure ()
    if (stx.getArg 0).getKind == ``qedIdent then
      let calleeId : Ident := ⟨(stx.getArg 0).getArg 0⟩
      let cn := calleeId.getId.eraseMacroScopes
      if let some pfn := ctx.spec.pureFns.find? (·.id.getId.eraseMacroScopes == cn) then
        let argTs ← lowerPosCallArgs stx s!"{cn}(...)" (some pfn.params.size) (stx.getArg 2).getSepArgs
          (fun e => do lowerCompExpr .val (← rewriteIn ctx inLambda e))
        let capTs : Array Term := pfn.capturedFields.map fun fn => ⟨(mkIdentFrom calleeId fn).raw⟩
        return mkRawExpr (← Qed.Lang.mkAppTerms (mkIdentFrom calleeId (ctx.spec.t.getId ++ pfn.id.getId)) (capTs ++ argTs))
    return Syntax.node stx.getHeadInfo k (← stx.getArgs.mapM (rewriteIn ctx inLambda))
  else if k == ``Qed.Jsx.attrValAssign then
    let more := (stx.getArg 4).getArgs.map fun m =>
      let it := if m.getKind == `Qed.Jsx.jsxAssignItem then m else m[m.getNumArgs - 1]!; (it.getArg 0, atomStr (it.getArg 1), it.getArg 2)
    let op0 := atomStr (stx.getArg 2)
    if more.isEmpty && (stx.getArg 5).getNumArgs == 0 && op0 == "=" && isSomePlaceholder (stx.getArg 3) then
      let fId := stx.getArg 1; let (fname, path) := splitDottedFieldName fId; checkMutableField ctx fId s!"`{fname}`" fname
      return mkJsxAttrValNode (← `(fun _v => $(← mkSiteExpr ctx #[.mk fname path none] none) (some _v)))
    let mut assigns := #[]
    for (fId, op, rhsRaw) in #[(stx.getArg 1, op0, stx.getArg 3)] ++ more do
      let (fname, path) := splitDottedFieldName fId
      let expr? ← if op == "=" && isPlaceholder rhsRaw then pure none else some <$> desugarAssignPath fname path op (← lowerCompExpr .val (← rewriteIn ctx inLambda rhsRaw))
      assigns ← pushHandlerAssign ctx assigns fId expr?
    let emit? ← if (stx.getArg 5).getNumArgs != 2 then pure none else do
      let emStx := (stx.getArg 5).getArg 1
      let some (evId, "emit", rawArgs) := matchIdentMethodCall? emStx | throwErrorAt emStx "expected `<event>.emit(...)` after `;` in inline JSX handler"
      some <$> lowerEmitCall emStx evId rawArgs
    return mkJsxAttrValNode (← mkSiteExpr ctx assigns emit?)
  else if let some (_, attrName, valNode) := matchAttrValExpr? stx then
    let inner := valNode.getArg 1
    if attrName == "bind" || attrName.startsWith "bind:" then
      if let some (fRef, fname, path) := parseCompLVal? (inner.getArg 1) then
        checkMutableField ctx fRef s!"`{attrName}=\{{stxSnippet (inner.getArg 1)}}`" fname
        let readTerm ← Qed.Server.foldProjTerms fRef ⟨(mkIdentFrom fRef fname).raw⟩ path.toList
        return Syntax.node .none stx.getKind #[stx.getArg 0, Syntax.node .none valNode.getKind #[valNode.getArg 0, mkJsxAttrValNode (← `(($readTerm, $(← mkSetterHandler ctx fname path))))]]
    return Syntax.node .none k (← stx.getArgs.mapM (rewriteIn ctx inLambda))
  else if k == ``Qed.Jsx.selfClosing || k == ``Qed.Jsx.withChildren then
    let tag := atomStr (stx.getArg 1)
    let kids? ← if k == ``Qed.Jsx.withChildren then some <$> rewriteIn ctx inLambda (stx.getArg 4) else pure none
    let rawAttrs := (stx.getArg 2).getArgs
    let isForm := !tag.isEmpty && tag.front.isUpper && tag.endsWith ".Form"
    let hasReset := isForm && rawAttrs.any (attrNamed "reset")
    let origBindField? : Option Ident := if !isForm then none else rawAttrs.findSome? fun a => do
      let (_, "bind", valNode) ← matchAttrValExpr? a | none
      let inner := (valNode.getArg 1).getArg 1; if inner.getKind == ``qedIdent then some ⟨inner.getArg 0⟩ else none
    let rewrittenPairs ← rawAttrs.mapM fun a => do
      let wasAssign := (matchNamedAttr? a).any fun (_, _, v) => v.getNumArgs == 2 && (v.getArg 1).getKind == ``Qed.Jsx.attrValAssign
      let aCtx := if hasReset && attrNamed "onSubmit" a then { ctx with wrapMsg? := none } else ctx
      return (wasAssign, ← rewriteIn aCtx inLambda a)
    if tag.isEmpty || !tag.front.isUpper then
      let some _ := ctx.wrapMsg? | return rebuildJsxEl stx (rewrittenPairs.map (·.2)) kids?
      let newAttrs ← wrapEventAttrs rewrittenPairs ctx.spec.msgId ctx.wrapMsg? fun aname => do
        if unitEvents.contains aname then pure (some #[]) else if strEvents.contains aname then pure (some #[← `(String)])
        else if aname == "onCheck" then pure (some #[← `(Bool)]) else pure none
      return rebuildJsxEl stx newAttrs kids?
    return ← rewriteUpperElement ctx inLambda stx tag rewrittenPairs kids? origBindField?
  else if k == ``qedIdent then checkRecordRpcIdent ctx (stx.getArg 0).getId; return stx
  else match stx with | .node info kind args => return .node info kind (← args.mapM (rewriteIn ctx inLambda)) | _ => return stx

/-! ## Component Specification Parsing -/

private def rejectDup (ref : Syntax) (isDup : Bool) (msg : String) : CommandElabM Unit := if isDup then throwErrorAt ref msg else pure ()
private def requireTyOrDef (role : Name) (fId : Ident) (ty? d? : Option Term) : CommandElabM Unit :=
  if ty?.isNone && d?.isNone then throwErrorAt fId s!"`{role} {fId.getId}` needs a type (`: Type`), a default (`= value`), or both" else pure ()

private def parseCallArgsAndCond (argsStx condStx : Syntax) : CommandElabM (Array Term × Option (Term × Term × Array Name) × Array Term) := do
  let rawArgs ← argsStx.getSepArgs.mapM (lowerCompExpr .val); let (rawPat?, rawGuards) := parseCompIfCond condStx
  let whenPat? ← rawPat?.mapM fun (p, s) => return (← liftMacroM (lowerQedPat p), ← lowerCompExpr .val s, collectQedPatIds p)
  return (rawArgs, whenPat?, ← rawGuards.mapM (lowerCompExpr .propGuard))

private def parseRpcQueryClause (acc : ComponentSpec) (cl : Syntax) : CommandElabM ComponentSpec := do
  let (qId, explicitTy?, rpcId) := ((⟨cl.getArg 1⟩ : Ident), ← lowerOptType (cl.getArg 2), (⟨cl.getArg 4⟩ : Ident))
  let (rawArgs, whenPat?, whenGuards) ← parseCallArgsAndCond (cl.getArg 6) (cl.getArg 8)
  let (srvInfo, mInfo) ← resolveServerRpc rpcId rawArgs.size "query"
  unless mInfo.isReadOnly do throwErrorAt rpcId s!"reactive `query {qId.getId}` cannot call mutating server RPC `{srvInfo.shortName}.{mInfo.name}`; `query` only permits read-only server functions"
  let qTy ← explicitTy?.getDM do
    let some ty ← inferAwaitBinderTy? mInfo true | throwErrorAt qId s!"cannot infer type for `query {qId.getId}`; annotate it as `query {qId.getId} : Type = ...`"
    pure ty
  let (msgTy, hasMsgEnsured) ← wrapEnsuredMsgTy qTy (if explicitTy?.isNone then mInfo.ensPredConst else none) mInfo.paramCount mInfo.paramTypeConsts `_qr_v "_qp_"
  return { acc with
    states  := acc.states.push { id := qId, ty? := some (← `(Cached $qTy)), def? := some (← `({})) }
    queries := acc.queries.push (.mk qId qTy msgTy (.mk rpcId srvInfo mInfo rawArgs whenPat? whenGuards hasMsgEnsured)) }

private def parseSubscribeClause (acc : ComponentSpec) (cl : Syntax) : CommandElabM ComponentSpec := do
  let (subId, chanId) : Ident × Ident := (⟨cl.getArg 1⟩, ⟨cl.getArg 3⟩)
  let (rawArgs, whenPat?, whenGuards) ← parseCallArgsAndCond (cl.getArg 5) (cl.getArg 7)
  let some chInfo := Qed.lookupChannel? (← getEnv) (← getCurrNamespace) (← getScope).openDecls chanId.getId
    | throwErrorAt chanId s!"unknown WebSocket channel `{chanId.getId}` in `subscribe`"
  if rawArgs.size != chInfo.paramCount then throwErrorAt chanId s!"channel `{chanId.getId}` expects {chInfo.paramCount} argument(s), got {rawArgs.size}"
  let mut recPolicy := chInfo.defaultReconnect; let mut hasRec := false
  let mut onJoin? : Option (Option Syntax × Array Syntax) := none
  let mut onMsg? : Option (Syntax × Array Syntax) := none; let mut onStatus? : Option (Syntax × Array Syntax) := none
  if (cl.getArg 8).getNumArgs == 2 then
    for h in ((cl.getArg 8).getArg 1).getArgs do match h.getKind with
      | `Qed.compSubReconnect => rejectDup h hasRec s!"duplicate `reconnect` in `subscribe {subId.getId}`"; hasRec := true; recPolicy ← liftMacroM <| Qed.parseReconnectExpr (h.getArg 1)
      | `Qed.compSubOnJoin =>
          rejectDup h onJoin?.isSome s!"duplicate `on_join` in `subscribe {subId.getId}`"
          let binder? := if (h.getArg 1).getNumArgs == 3 then some ((h.getArg 1).getArg 1) else none
          if binder?.isSome && !chInfo.hasJoinSnapshot then throwErrorAt h s!"channel `{chanId.getId}` does not return an `on_join` snapshot; write `on_join:` without a parameter"
          onJoin? := some (binder?, suiteStmts (h.getArg 3))
      | `Qed.compSubOnMsg    => rejectDup h onMsg?.isSome s!"duplicate `on_message` in `subscribe {subId.getId}`"; onMsg? := some (h.getArg 2, suiteStmts (h.getArg 5))
      | `Qed.compSubOnStatus => rejectDup h onStatus?.isSome s!"duplicate `on_status` in `subscribe {subId.getId}`"; onStatus? := some (h.getArg 2, suiteStmts (h.getArg 5))
      | _ => throwErrorAt h s!"unexpected handler in `subscribe {subId.getId}`"
  let (msgEvTy, hasMsgEnsured) ← wrapEnsuredMsgTy (mkIdentFrom chanId chInfo.eventTypeConst) chInfo.ensPredConst chInfo.paramCount chInfo.paramTypeConsts `_ws_ev "_wp_"
  return { acc with
    states := acc.states.push { id := subId, ty? := some (← `(Qed.SocketStatus)), def? := some (← `(Qed.SocketStatus.disconnected)) }
    subscriptions := acc.subscriptions.push (.mk subId chanId chInfo rawArgs whenPat? whenGuards recPolicy onJoin? onMsg? onStatus? msgEvTy hasMsgEnsured) }

private def parseCompClause (acc : ComponentSpec) (cl : Syntax) : CommandElabM ComponentSpec := do
  match cl.getKind with
  | `Qed.compSessionClause =>
      rejectDup cl acc.sessionField?.isSome "duplicate `session` clause in component"
      let sfId : Ident := ⟨cl.getArg 1⟩; let sfTy ← (← lowerOptType (cl.getArg 2)).getDM `(Option String)
      return { acc with sessionField? := some sfId, states := acc.states.push { id := sfId, ty? := some sfTy, def? := some (← `(none)) } }
  | `Qed.compFieldClause =>
      let (role, fId) := ((cl.getArg 0).getId, (⟨cl.getArg 1⟩ : Ident))
      let rawTy? := if (cl.getArg 2).getNumArgs == 2 then some ((cl.getArg 2).getArg 1) else none
      let isHtmlProp := role == `prop && rawTy?.any fun rt => rt.getKind == ``qedTypeAtom && [`Html, `Qed.Html].contains ((rt.getArg 0).getId.eraseMacroScopes) && (rt.getArg 1).getArgs.isEmpty
      let ty? ← if isHtmlProp then pure none else rawTy?.mapM lowerTypeStx
      let d?  ← if (cl.getArg 3).getNumArgs == 2 then some <$> lowerCompExpr .val ((cl.getArg 3).getArg 1) else pure none
      match role with
      | `prop =>
          if isHtmlProp then
            if fId.getId.eraseMacroScopes == `children then throwErrorAt fId "`children` is implicitly available whenever `view:` references `\{children}`; remove `prop children : Html`"
            return { acc with slots := acc.slots.push (.mk fId d?) }
          requireTyOrDef role fId ty? d?; return { acc with props := acc.props.push { id := fId, ty?, def? := d? } }
      | `bind => requireTyOrDef role fId ty? d?; return { acc with binds := acc.binds.push { id := fId, ty?, def? := d? } }
      | `collection =>
          let some colTy := ty? | throwErrorAt fId s!"`collection {fId.getId}` requires `: ChildComponent`"
          unless colTy.raw.isIdent do throwErrorAt colTy "`collection` target must be a child component name"
          let childId : Ident := ⟨colTy.raw⟩
          return { acc with collections := acc.collections.push (fId, childId)
                            states := acc.states.push { id := fId, ty? := some (← `(Array $(mkIdent (childId.getId ++ `State)))), def? := some (← d?.getDM `(#[])) } }
      | _ => requireTyOrDef role fId ty? d?
             return { acc with states := acc.states.push { id := fId, ty?, def? := d?, rawTy? }
                               ephemeralFields := if role == `ephemeral then acc.ephemeralFields.push fId else acc.ephemeralFields }
  | `Qed.compKeyClause   => rejectDup cl acc.keyF?.isSome "duplicate `key` clause in component"; return { acc with keyF? := some ⟨cl.getArg 1⟩ }
  | `Qed.compEventClause => return { acc with events := acc.events.push (.mk ⟨cl.getArg 1⟩ (← parseParamList (cl.getArg 2))) }
  | `Qed.compStartClause => return { acc with starts := acc.starts.push (cl.getArg 1) }
  | `Qed.compRouteClause =>
      rejectDup cl acc.route?.isSome "duplicate `route` clause in component"
      let rField : Ident := if (cl.getArg 1).getNumArgs == 1 then ⟨(cl.getArg 1).getArg 0⟩ else mkIdentFrom cl `route
      let (rTy, rInit) := (← lowerTypeStx (cl.getArg 3), ← lowerCompExpr .val (cl.getArg 5))
      let rAlts := if (cl.getArg 6).getNumArgs == 2 then ((cl.getArg 6).getArg 1).getArgs else #[]
      return { acc with route? := some (.mk rField rTy rInit rAlts), states := acc.states.push { id := rField, ty? := some rTy, def? := some rInit } }
  | `Qed.compPortOutClause | `Qed.compPortInClause =>
      let pId : Ident := ⟨cl.getArg 1⟩
      if pId.getId.toString.startsWith "__" then throwErrorAt pId s!"port name '{pId.getId}' is reserved (names starting with `__`)"
      if cl.getKind == `Qed.compPortOutClause then return { acc with portOuts := acc.portOuts.push (.mk pId (← lowerTypeStx (cl.getArg 3))) }
      else return { acc with portIns := acc.portIns.push (.mk pId ⟨cl.getArg 3⟩ (← lowerTypeStx (cl.getArg 5)) (cl.getArg 8)) }
  | `Qed.compRpcQueryClause => parseRpcQueryClause acc cl
  | `Qed.compSubscribeClause => parseSubscribeClause acc cl
  | `Qed.compStyleClause => return { acc with styles := acc.styles.push cl }
  | `Qed.compStylesheetClause =>
      let rawPath := (⟨cl.getArg 1⟩ : TSyntax `str).getString
      let normPath := if rawPath.startsWith "/" || rawPath.startsWith "http://" || rawPath.startsWith "https://" then rawPath else "/" ++ rawPath
      unless isSafeUrl normPath do throwErrorAt (cl.getArg 1) s!"unsafe stylesheet URL `{rawPath}`: must be a root-relative path (e.g. `\"/app.css\"` or `\"app.css\"`) or `https://`/`http://` URL"
      return { acc with stylesheets := acc.stylesheets.push normPath }
  | `Qed.compThemeClause => return { acc with themes := acc.themes.push ⟨cl.getArg 1⟩ }
  | `Qed.compHeadClause  => rejectDup cl acc.headClause?.isSome "duplicate `head:` clause in component"; return { acc with headClause? := some cl }
  | `Qed.compFnClause =>
      let fnId : Ident := ⟨cl.getArg 1⟩
      let params ← parseParamList (cl.getArg 2)
      let rawParamTys := if (cl.getArg 2).getNumArgs == 3 then ((cl.getArg 2).getArg 1).getSepArgs.map (·.getArg 2) else #[]
      let retTy? ← if (cl.getArg 3).getNumArgs == 2 then some <$> lowerTypeStx ((cl.getArg 3).getArg 1) else pure none
      return { acc with fns := acc.fns.push (.mk fnId params retTy? (suiteStmts (cl.getArg 5)) #[] rawParamTys) }
  | `Qed.compActionClause => return { acc with actions := acc.actions.push cl }
  | `Qed.compInvariantClause | `Qed.compForEachInvClause | `Qed.compExampleClause => return { acc with invariants := acc.invariants.push cl }
  | _ => return acc

def checkTopLevelMountable (spec : ComponentSpec) (ref : Syntax) (featureDesc : String) : CommandElabM Unit := do
  let uninit := spec.states.filter (·.def?.isNone)
  let blockers := #[
    (!spec.props.isEmpty || !spec.slots.isEmpty, "`prop`"), (!spec.binds.isEmpty, "`bind`"),
    (spec.hasChildren, "`children`"), (!spec.events.isEmpty, "`event`"),
    (!uninit.isEmpty, s!"uninitialized `state` ({String.intercalate ", " (uninit.toList.map fun f => s!"`{f.id.getId}`")})")
  ].filterMap fun (c, s) => if c then some s else none
  if !blockers.isEmpty then
    throwErrorAt ref s!"{featureDesc} is only supported on top-level mountable components, but `{spec.t.getId}` declares {String.intercalate ", " blockers.toList}"

def parseComponentSpec (stx : Syntax) : CommandElabM ComponentSpec := do
  let doc? := if (stx.getArg 0).getNumArgs == 1 then some ⟨(stx.getArg 0).getArg 0⟩ else none
  let (t, bodyStx) := ((⟨stx.getArg 2⟩ : Ident), stx.getArg 7)
  let acc ← (stx.getArg 4).getArgs.foldlM (init := { doc?, t, body := bodyStx }) parseCompClause
  let resolvedStates ← if acc.keyF?.isSome then pure acc.states else acc.states.mapM fun f => do
    let def? ← match f.def?, f.rawTy? with | none, some rty => liftMacroM (Qed.Lang.inferQedTypeDefault? rty) | d, _ => pure d
    return { f with def? }
  let fieldNames := resolvedStates.map (·.id.getId)
  let allDeclNames := fieldNames ++ acc.props.map (·.id.getId) ++ acc.binds.map (·.id.getId) ++
    acc.slots.map (·.id.getId) ++ acc.events.map (·.id.getId) ++ acc.portOuts.map (·.id.getId) ++ acc.fns.map (·.id.getId)
  discard <| allDeclNames.foldlM (init := (#[] : Array Name)) fun seen dn => do
    if seen.contains dn then throwErrorAt t s!"duplicate declaration name `{dn}` in component `{t.getId}`; state fields, props, binds, events, ports, and `fn` helpers must have distinct names"
    return seen.push dn
  let actionNames := acc.actions.map (·[1].getId) ++ acc.portIns.map (·.id.getId)
  for f in acc.fns do
    if actionNames.contains f.id.getId then
      throwErrorAt f.id s!"`fn {f.id.getId}` conflicts with action/port `{f.id.getId}` in component `{t.getId}`"
  let outTy? : Option Term := if !acc.events.isEmpty || !acc.binds.isEmpty then some (mkIdent (t.getId ++ `Out)) else none
  if let some kf := acc.keyF? then
    unless fieldNames.contains kf.getId.eraseMacroScopes do throwErrorAt kf s!"`key {kf.getId}`: `{kf.getId}` is not a `state` field of `{t.getId}` ({formatStateFieldList fieldNames})"
    if outTy?.isSome then throwErrorAt kf "`key` marks the row identity for parent-owned use, and a parent-owned child's `event` output would have no receiver; drop one of the two"
  let baseAllNames := (fieldNames ++ acc.props.map (·.id.getId) ++ acc.binds.map (·.id.getId)).toList.eraseDups.toArray
  let mut resolvedFns : Array CompFnDecl := #[]
  for f in acc.fns do
    if f.isPure then
      let pNames := f.params.map (·.1.getId.eraseMacroScopes)
      let mut caps := baseAllNames.filter fun n => !pNames.contains n && f.stmts.any (mentionsIdent · n)
      for prev in resolvedFns do
        if prev.isPure && f.stmts.any (mentionsIdent · prev.id.getId.eraseMacroScopes) then
          for c in prev.capturedFields do
            if !pNames.contains c then caps := pushUnique caps c
      resolvedFns := resolvedFns.push { f with capturedFields := caps }
    else resolvedFns := resolvedFns.push f
  let spec : ComponentSpec := { acc with
    states := resolvedStates, fns := resolvedFns,
    hasChildren := !allDeclNames.contains `children && hasFreeIdent `children bodyStx,
    outTy?, invariants := acc.invariants ++ (stx.getArg 8).getArgs }
  let uninit := spec.states.filter (·.def?.isNone)
  if !uninit.isEmpty then
    if let some q0 := spec.queries[0]? then
      throwErrorAt q0.id s!"reactive `query {q0.id.getId}` requires all `state` fields on `{spec.t.getId}` to have default values"
    else if let some s0 := spec.subscriptions[0]? then
      throwErrorAt s0.id s!"reactive `subscribe {s0.id.getId}` requires all `state` fields on `{spec.t.getId}` to have default values"
  return spec

def bindMentionedFields (spec : ComponentSpec) (shouldBind : Name → Bool) (body : Term) : CommandElabM Term := do
  let mut out := body
  for po in spec.portOuts.reverse do if shouldBind po.id.getId then out ← `(let $(mkIdent po.id.getId):ident := $(spec.id po.id.getId); $out)
  for ev in spec.events.reverse do if shouldBind ev.id.getId then out ← `(let $(mkIdent ev.id.getId):ident := $(spec.outCtor ev.id.getId); $out)
  for g in spec.allNames.reverse do if shouldBind g then
    let gId := mkIdent g
    out ← if spec.fieldNames.contains g then `(let $gId:ident := (s.$gId:ident); $out) else `(let $gId:ident := (p.$gId:ident); $out)
  return out

def lowerMutStmt? (spec : ComponentSpec) (s : Syntax) (strict : Bool) : CommandElabM (Option (Name × (Term → CommandElabM Term))) := do
  let checkField (ref : Syntax) (fname : Name) : CommandElabM Name := do
    if strict && !spec.fieldNames.contains fname then throwNotMutableStateField ref s!"`{fname}`" fname spec.fieldNames spec.propNames
    pure fname
  let mkBind (fname : Name) (rhs : Term) : Option (Name × (Term → CommandElabM Term)) :=
    some (fname, fun cont => `(let $(mkIdent fname):ident := $rhs; $cont))
  let sk := s.getKind
  if sk == ``qedStmtAssign then
    let (lhs, op, rhsRaw) := (s.getArg 0, atomStr (s.getArg 1), s.getArg 2)
    if let some (ref, fname, path) := parseCompLVal? lhs then
      let fname ← checkField ref fname
      let leafValT ← if strict && op == "=" && isPlaceholder rhsRaw then `(v) else desugarAssignPath fname path op (← lowerCompExpr .val rhsRaw)
      let fullValT ← if path.isEmpty then pure leafValT else buildRecordUpdateFrom ⟨(mkIdent fname).raw⟩ path (fun _ => pure leafValT)
      return mkBind fname fullValT
    else if let (true, some (ref, fname, path)) := (lhs.getKind == ``qedIndex && op == "=", parseCompLVal? (lhs.getArg 0)) then
      let fname ← checkField ref fname; let idxT ← lowerCompExpr .val (lhs.getArg 2); let rhsT ← lowerCompExpr .val rhsRaw
      if path.isEmpty then return mkBind fname (← `(qedCompSetAt($(mkIdent fname), $idxT, $rhsT)))
      let upd ← buildRecordUpdateFrom ⟨(mkIdent fname).raw⟩ path fun curArr => do
        let tmpArr := mkIdent `_qedArr
        `(let $tmpArr:ident := $curArr; qedCompSetAt($tmpArr, $idxT, $rhsT))
      return mkBind fname upd
    else if strict then
      let lhsStr := stxSnippet lhs
      throwErrorAt s s!"unsupported assignment{if lhsStr.isEmpty then "" else s!" `{lhsStr} {op} ...`"} in component action; expected `field = val`, `field.sub = val`, `field += val`, `field -= val`, or `arr[i] = val`"
    else return none
  else if sk == ``qedStmtExpr then
    let e := s.getArg 0
    let mutCall? := (matchPushCall? e).map (fun (t, a) => (t, a, true, "push", "array", "items.push(x)")) <|>
                    (matchRemoveCall? e).map (fun (t, a) => (t, a, false, "remove", "dictionary", "scores.remove(k)"))
    let some (targetStx, argStx, isPush, meth, kindLabel, exStr) := mutCall? | return none
    let some (ref, fname, path) := parseCompLVal? targetStx | do
      if strict then
        let tgtStr := stxSnippet targetStx
        throwErrorAt targetStx s!"{kindLabel} `.{meth}(...)` in component actions requires a `state` field path (e.g. `{exStr}`){if tgtStr.isEmpty then "" else s!", got `{tgtStr}.{meth}(...)`"}"
      return none
    let fname ← checkField ref fname; let argT ← lowerCompExpr .val argStx
    let fullValT ← buildRecordUpdateFrom ⟨(mkIdent fname).raw⟩ path fun cur =>
      if isPush then `(($cur).push $argT) else `(($cur).remove $argT)
    return mkBind fname fullValT
  else return none

end CompElab
end Qed
