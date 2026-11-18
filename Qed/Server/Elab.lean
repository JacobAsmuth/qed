import Lean
import Qed.Proto
import Qed.Resource
import Qed.Ssr
import Qed.Runtime.Cmd
import Qed.Component.Syntax
import Qed.Server.Core
import Qed.Server.Syntax
import Qed.Server.External
import Qed.Server.Invariant

namespace Qed.Server
open Qed.Lang

/-! ## Compile-Time Unhandled-Error Guards (`srvEnsureUnit` & `srvRejectUnhandledErr`) -/

syntax (name := srvEnsureUnitStx) "srvEnsureUnit(" term ")" : term
syntax (name := srvRejectErrStx)  "srvRejectUnhandledErr(" term ")" : term

open Lean Meta Elab Term in
@[term_elab srvEnsureUnitStx]
def elabSrvEnsureUnit : TermElab := fun stx _ => do
  let inner : Term := ⟨stx[1]⟩
  let e ← elabTerm inner none
  synthesizeSyntheticMVarsNoPostponing
  let ty ← whnf (← inferType e)
  if ty.isAppOf ``Except || ty.isAppOf ``Option then
    throwErrorAt stx m!"unhandled fallible or optional expression of type `{← ppExpr ty}`; append `?` to propagate or `catch` to handle"
  ensureHasType (mkConst ``Unit) e

open Lean Meta Elab Term in
@[term_elab srvRejectErrStx]
def elabSrvRejectErr : TermElab := fun stx expectedType? => do
  let inner : Term := ⟨stx[1]⟩
  let e ← elabTerm inner expectedType?
  synthesizeSyntheticMVarsNoPostponing
  let ty ← whnf (← inferType e)
  if ty.isAppOfArity ``Except 2 then
    let errTy ← whnf (ty.getAppArgs[0]!)
    if errTy.isConstOf ``ApiError then
      throwErrorAt stx m!"unhandled fallible `T!` value of type `{← ppExpr ty}`; append `?` to propagate errors or use `catch` to recover"
  return e

/-! ## Persistent Registries (`serverRegistry` & `fullstackRegistry`) -/

export Qed (ServerMethodInfo ServerInfo serverRegistry)

structure FullstackInfo where
  fullstackName : Lean.Name
  serverName    : Lean.Name
  clientName    : Lean.Name
  title         : String
deriving Inhabited, Repr

initialize fullstackRegistry :
    Lean.SimplePersistentEnvExtension FullstackInfo (Lean.NameMap FullstackInfo) ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays =>
      arrays.foldl (fun acc arr => arr.foldl (fun m info => m.insert info.fullstackName info) acc) {}
    addEntryFn := fun m info => m.insert info.fullstackName info
  }

/-! ## Expression & Statement Lowering Context -/

private inductive StateAccessRule where
  | pureStep (stateVar : Lean.Ident) (overrides : Array (String × Lean.Ident) := #[])
  | invariantProp (curVar oldVar : Lean.Ident) (inOld : Bool)
  | forbidAsyncOutsideAtomic
  | forbidInRequires
  | forbidInEnsures
  | statelessServer

private structure LowerCtx where
  fnName       : String
  stateFields  : Array String
  envVars      : Array String
  locals       : Array String
  stateRule    : StateAccessRule
  allowAwait   : Bool
  allowUnwrap  : Bool
  hasFallible  : Bool
  isOption     : Bool
  innerOptTy?  : Option Lean.Term
  forbidCtxEnv : Bool := false
  domainErrTy? : Option Lean.Term := none

private inductive HoistedStep where
  | awaitUnwrap (ref : Lean.Syntax) (tmp : Lean.Ident) (callTerm : Lean.Term)
  | pureUnwrap  (ref : Lean.Syntax) (tmp : Lean.Ident) (valTerm : Lean.Term)

private structure LowerState where
  nextId       : Nat := 0
  stateRead    : Bool := false
  mutated      : Array String := #[]
  extRoots     : Array Lean.Name := #[]
  usedOld      : Bool := false
  hoisted      : Array HoistedStep := #[]

private abbrev LowerM := StateRefT LowerState Lean.Elab.Command.CommandElabM

private def freshIdent (prefixStr : String) : LowerM Lean.Ident := do
  let st ← get
  modify fun s => { s with nextId := s.nextId + 1 }
  return Lean.mkIdent (Lean.Name.mkSimple s!"{prefixStr}{st.nextId}")

private def recordMutated (f : String) : LowerM Unit := do
  modify fun s =>
    if s.mutated.contains f then s else { s with mutated := s.mutated.push f }

private def recordExtRoot (n : Lean.Name) : LowerM Unit := do
  modify fun s =>
    if s.extRoots.contains n then s else { s with extRoots := s.extRoots.push n }

/-! ## Static AST Queries (`exprHasAwait`, `blockHasAwait`, `allPathsReturn`) -/

partial def exprHasAwait (stx : Lean.Syntax) : Bool :=
  if stx.getKind == ``qedAwait then true
  else stx.getArgs.any exprHasAwait

partial def stmtHasAwait (stx : Lean.Syntax) : Bool :=
  exprHasAwait stx

def blockHasAwait (stmts : Array Lean.Syntax) : Bool :=
  stmts.any stmtHasAwait

partial def exprCallsOld (stx : Lean.Syntax) : Bool :=
  if stx.getKind == ``qedCall then
    let callee := stx[0]
    if callee.getKind == ``qedIdent && callee[0].getId == `old then true
    else stx.getArgs.any exprCallsOld
  else
    stx.getArgs.any exprCallsOld

private def ensureElseToReturnStmt (ref : Lean.Syntax) (elseNode : Lean.Syntax) : Lean.Syntax :=
  let info := Lean.SourceInfo.fromRef ref
  if elseNode.getKind == Lean.nullKind && elseNode.getNumArgs == 2 && elseNode[0]!.isAtom then
    Lean.Syntax.node info ``qedStmtReturn #[elseNode[0]!, elseNode[1]!]
  else
    Lean.Syntax.node info ``qedStmtReturn #[Lean.Syntax.atom info "return", Lean.Syntax.node info Lean.nullKind #[elseNode]]

mutual
  partial def stmtAlwaysReturns (stx : Lean.Syntax) : Bool :=
    let k := stx.getKind
    if k == ``qedStmtReturn || k == ``qedStmtReturnAtomic then true
    else if k == ``qedStmtAtomic then blockAlwaysReturns (suiteStmts stx[2])
    else if k == ``qedStmtIf then
      match desugarElifs stx[4].getArgs stx[5] with
      | some elseStmts => blockAlwaysReturns (suiteStmts stx[3]) && blockAlwaysReturns elseStmts
      | none           => false
    else if k == ``qedStmtIfLet then
      match extractElseSuite stx[7] with
      | some elseStmts => blockAlwaysReturns (suiteStmts stx[6]) && blockAlwaysReturns elseStmts
      | none           => false
    else if k == ``qedStmtMatch then
      let cases := stx[3].getArgs
      !cases.isEmpty && cases.all fun c => blockAlwaysReturns (suiteStmts c[3])
    else
      false

  partial def blockAlwaysReturns (stmts : Array Lean.Syntax) : Bool :=
    stmts.any stmtAlwaysReturns
end

mutual
  partial def exprHasUnwrap (stx : Lean.Syntax) : Bool :=
    let k := stx.getKind
    if k == ``qedUnwrap then true
    else if k == ``qedDotIdent then false
    else if k == ``qedIdent then stx[0].getId.toString.endsWith "?"
    else if k == ``qedLam1 || k == ``qedLamN || k == ``qedAllIn || k == ``qedAnyIn || k == ``qedAllVars then false
    else stx.getArgs.any exprHasUnwrap

  partial def stmtMayReturnEarly (stx : Lean.Syntax) : Bool :=
    let k := stx.getKind
    if k == ``qedStmtReturn || k == ``qedStmtReturnAtomic || k == ``qedStmtEnsure then true
    else if k == ``qedStmtAtomic || k == ``qedStmtLetAtomic then true
    else if k == ``qedStmtLet then
      stx[5].getNumArgs == 1 || exprHasUnwrap stx[4]
    else if k == ``qedStmtIf then
      exprHasUnwrap stx[1] || blockMayReturnEarly (suiteStmts stx[3]) ||
        ((desugarElifs stx[4].getArgs stx[5]).map blockMayReturnEarly |>.getD false)
    else if k == ``qedStmtIfLet then
      exprHasUnwrap stx[4] || blockMayReturnEarly (suiteStmts stx[6]) ||
        ((extractElseSuite stx[7]).map blockMayReturnEarly |>.getD false)
    else if k == ``qedStmtMatch then
      stx[1].getSepArgs.any exprHasUnwrap ||
        stx[3].getArgs.any fun c => blockMayReturnEarly (suiteStmts c[3])
    else
      exprHasUnwrap stx

  partial def blockMayReturnEarly (stmts : Array Lean.Syntax) : Bool :=
    stmts.any stmtMayReturnEarly
end

/-! ## Expression Lowering (`lowerExpr`) -/

open Lean Elab Command in
private def peelIdentTrailingQ (id : Ident) : (Ident × Nat) :=
  let raw := id.getId.toString
  let chars := raw.toList
  let qCount := (chars.reverse.takeWhile (· == '?')).length
  if qCount == 0 then
    (id, 0)
  else
    let baseStr := String.ofList (chars.take (chars.length - qCount))
    let baseName := (baseStr.splitOn ".").foldl (fun acc seg => Name.str acc seg) .anonymous
    (mkIdentFrom id baseName, qCount)

open Lean Elab Command in
private def checkStateRead (ref : Syntax) (ctx : LowerCtx) (field : String) : LowerM Ident := do
  match ctx.stateRule with
  | .pureStep sv _ =>
      modify fun s => { s with stateRead := true }
      return sv
  | .invariantProp curV oldV inOld =>
      return if inOld then oldV else curV
  | .forbidAsyncOutsideAtomic =>
      throwErrorAt ref s!"cannot access server state `{field}` outside an `atomic` block in `{ctx.fnName}` because `{ctx.fnName}` uses `await` (prevents TOCTOU data races across suspension points)"
  | .forbidInRequires =>
      throwErrorAt ref s!"`requires` precondition in `{ctx.fnName}` cannot reference mutable server state `{field}`; check `{field}` inside the function body instead"
  | .forbidInEnsures =>
      throwErrorAt ref s!"`ensures` postcondition in `{ctx.fnName}` cannot reference mutable server state `{field}`; state postconditions on `result` and parameters only"
  | .statelessServer =>
      throwErrorAt ref s!"unknown identifier `{field}`"

open Lean Elab Command in
private def resolveStateFieldBase (ref : Syntax) (ctx : LowerCtx) (field : Name) : LowerM Term := do
  let fStr := field.toString
  let sv ← checkStateRead ref ctx fStr
  match ctx.stateRule with
  | .pureStep _ ovs =>
      if let some (_, ovId) := ovs.find? (·.1 == fStr) then
        return ⟨mkIdentFrom ref ovId.getId⟩
      else
        let fid := mkIdentFrom ref field
        `(($sv).$fid:ident)
  | _ =>
      let fid := mkIdentFrom ref field
      `(($sv).$fid:ident)

open Lean Elab Command in
private def foldProjections (ref : Syntax) (base : Term) (fields : List Name) : LowerM Term := do
  let mut acc := base
  for f in fields do
    let fId := mkIdentFrom ref f
    acc ← `(($acc).$fId:ident)
  return acc

open Lean Elab Command in
private def resolveDottedIdent (ref : Syntax) (ctx : LowerCtx) (id : Ident) : LowerM Term := do
  let comps := id.getId.components
  match comps with
  | [] => throwErrorAt ref "empty identifier"
  | [single] =>
      let s := single.toString
      if s == "true" then return ← `(true)
      else if s == "false" then return ← `(false)
      else if s == "none" then return ← `(none)
      else if ctx.locals.contains s then
        return ⟨mkIdentFrom ref single⟩
      else if s == "ctx" then
        if ctx.forbidCtxEnv then
          throwErrorAt ref s!"`ensures` postcondition in `{ctx.fnName}` cannot reference `ctx` because client decoders re-verify `ensures` on the wire"
        return ⟨mkIdentFrom ref single⟩
      else if ctx.stateFields.contains s then
        resolveStateFieldBase ref ctx single
      else if ctx.envVars.contains s then
        if ctx.forbidCtxEnv then
          throwErrorAt ref s!"`ensures` postcondition in `{ctx.fnName}` cannot reference `env` binding `{s}` because client decoders re-verify `ensures` on the wire"
        return ⟨mkIdentFrom ref single⟩
      else
        return ⟨id⟩
  | root :: rest =>
      let rStr := root.toString
      if ctx.locals.contains rStr then
        let base : Term := ⟨mkIdentFrom ref root⟩
        foldProjections ref base rest
      else if rStr == "ctx" || ctx.envVars.contains rStr then
        if ctx.forbidCtxEnv then
          throwErrorAt ref s!"`ensures` postcondition in `{ctx.fnName}` cannot reference `{rStr}` because client decoders re-verify `ensures` on the wire"
        let base : Term := ⟨mkIdentFrom ref root⟩
        foldProjections ref base rest
      else if ctx.stateFields.contains rStr then
        let base ← resolveStateFieldBase ref ctx root
        foldProjections ref base rest
      else
        recordExtRoot root
        return ⟨id⟩

open Lean Elab Command in
private def hoistPureUnwraps (ref : Syntax) (ctx : LowerCtx) (qCount : Nat) (term0 : Term) : LowerM Term := do
  if qCount == 0 then return term0
  unless ctx.allowUnwrap do
    throwErrorAt ref s!"operator `?` cannot be used here in `{ctx.fnName}` (return type must be `T!` or `T?`, and `?` cannot appear inside lambdas or invariants)"
  let mut term := term0
  for _ in [0:qCount] do
    let tmp ← freshIdent "_srvUnw"
    modify fun s => { s with hoisted := s.hoisted.push (.pureUnwrap ref tmp term) }
    term := ⟨tmp⟩
  return term

open Lean Elab Command in
private abbrev SrvExprM := ReaderT LowerCtx LowerM

open Lean Elab Command in
private def mkSrvLowerHooks (recGo : ExprMode → Syntax → SrvExprM Term) : LowerHooks SrvExprM := {
  lowerIdent := fun stx id mode => do
    let ctx ← read
    let (cleanId, qCount) := peelIdentTrailingQ id
    let term ← liftM <| hoistPureUnwraps stx ctx qCount (← resolveDottedIdent stx ctx cleanId)
    liftMacroM (finishTermMode mode term)
  lowerProj := fun stx objT fld mode => do
    let ctx ← read
    let (cleanFld, qCount) := peelIdentTrailingQ fld
    let term ← liftM <| hoistPureUnwraps stx ctx qCount (← `(($objT).$cleanFld:ident))
    liftMacroM (finishTermMode mode term)
  lowerIndex := fun _ arrT idxT mode => do
    let elem ← `(srvGetElem($arrT, $idxT))
    liftMacroM (finishTermMode mode elem)
  lowerCall := fun stx calleeStx rawArgs mode go => do
    let ctx ← read
    if calleeStx.getKind == ``qedIdent && calleeStx[0].getId == `old then
      match ctx.stateRule with
      | .invariantProp curV oldV _ =>
          if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then
            throwErrorAt stx "`old(...)` expects exactly one positional expression argument"
          modify fun s => { s with usedOld := true }
          return some (← withReader (fun c => { c with stateRule := .invariantProp curV oldV true }) (go mode rawArgs[0]![0]))
      | _ => throwErrorAt stx "`old(...)` may only be used inside `invariant` declarations"
    if calleeStx.getKind == ``qedIdent && calleeStx[0].getId == `fail then
      if rawArgs.any (·.getKind == ``qedCallArgNamed) then
        throwErrorAt stx "`fail(...)` takes positional arguments `fail(.tag)`, `fail(.tag, msg)`, `fail(msg)`, or `fail(code, msg)`"
      if (rawArgs.size == 1 || rawArgs.size == 2) && (unwrapParens1 rawArgs[0]![0]).getKind == ``qedDotIdent then
        let uDot := unwrapParens1 rawArgs[0]![0]
        let tagId : Ident := ⟨uDot[1]⟩
        let some errTy := ctx.domainErrTy?
          | throwErrorAt stx "internal error: missing inferred domain error type for `fail(.tag)`"
        let msgTerm ← if rawArgs.size == 2 then go .val rawArgs[1]![0] else pure (Syntax.mkStrLit tagId.getId.toString)
        let dotNode : Term := ⟨Syntax.node (.fromRef uDot) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef uDot) ".", tagId.raw]⟩
        return some (← `(Qed.Server.mkFailDom (ε := $errTy) ($dotNode : $errTy) $msgTerm))
      if ctx.domainErrTy?.isSome then
        throwErrorAt stx "cannot mix typed `fail(.tag)` and untyped `fail(...)` inside the same function; use `fail(.tag, msg)`"
      if rawArgs.size == 1 then
        return some (← `(Qed.Server.mkFail1 $(← go .val rawArgs[0]![0])))
      else if rawArgs.size == 2 then
        return some (← `(Qed.Server.mkFail2 $(← go .val rawArgs[0]![0]) $(← go .val rawArgs[1]![0])))
      else
        throwErrorAt stx "`fail(...)` expects `(.tag)`, `(.tag, msg)`, `(message)`, or `(code, message)`"
    return none
  lowerUnwrap := fun stx innerRaw mode => do
    let ctx ← read
    unless ctx.allowUnwrap do
      throwErrorAt stx s!"operator `?` cannot be used here in `{ctx.fnName}` (return type must be `T!` or `T?`, and `?` cannot appear inside lambdas or invariants)"
    let inner := unwrapParens1 innerRaw
    if inner.getKind == ``qedAwait then
      unless ctx.allowAwait do
        throwErrorAt inner "`await` cannot be used inside an `atomic` block, lambda, `requires`, or `invariant`; perform external I/O outside `atomic`"
      let callTerm ← recGo .val inner[1]
      let tmp ← liftM <| freshIdent "_srvAw"
      modify fun s => { s with hoisted := s.hoisted.push (.awaitUnwrap stx tmp callTerm) }
      liftMacroM (finishTermMode mode ⟨tmp⟩)
    else
      let v ← recGo .val innerRaw
      let term ← liftM <| hoistPureUnwraps stx ctx 1 v
      liftMacroM (finishTermMode mode term)
  lowerAwait := fun stx argRaw mode => do
    let ctx ← read
    unless ctx.allowAwait do
      throwErrorAt stx "`await` cannot be used inside an `atomic` block, lambda, `requires`, or `invariant`; perform external I/O outside `atomic`"
    let inner := unwrapParens1 argRaw
    if inner.getKind == ``qedUnwrap then
      unless ctx.allowUnwrap do
        throwErrorAt stx s!"operator `?` cannot be used in `{ctx.fnName}` because its return type is neither fallible (`T!`) nor optional (`T?`); handle the `await` error with `let x = await ... catch err:`"
      let callTerm ← recGo .val inner[0]
      let tmp ← liftM <| freshIdent "_srvAw"
      modify fun s => { s with hoisted := s.hoisted.push (.awaitUnwrap stx tmp callTerm) }
      liftMacroM (finishTermMode mode ⟨tmp⟩)
    else
      throwErrorAt stx "unhandled fallible `await` expression; append `?` to propagate errors or use `let x = await ... catch err:` to handle them inline"
  lowerSend := fun ref _ _ => throwErrorAt ref "`send` is only supported in client `component`s"
  lowerFieldSetter := fun ref _ => throwErrorAt ref "`(field = ·)` is only supported in client `component`s"
  lowerJsx := fun ref _ => throwErrorAt ref s!"unsupported server expression syntax ({ref.getKind})"
  lowerArrElem := fun t => `(srvAutoField($t))
  wrapNamedField := fun t => `(srvAutoField($t))
  lowerType := fun t => liftMacroM (return (← lowerQedType t false).1)
  lowerPat := fun p => liftMacroM (lowerQedPat p)
  withLocals := fun names k =>
    withReader (fun c => { c with locals := c.locals ++ names, allowAwait := false, allowUnwrap := false }) k
  useDirectArray := true
  allowOptElse := false
  optElseFallback := `(())
  freshIdent := fun pfx => liftM <| freshIdent pfx
  throwErr := fun ref msg => throwErrorAt ref msg
}

open Lean Elab Command in
private partial def lowerExprM (mode : ExprMode) (stx : Syntax) : SrvExprM Term :=
  lowerQedExpr (mkSrvLowerHooks lowerExprM) mode stx

open Lean Elab Command in
def lowerExpr (ctx : LowerCtx) (mode : ExprMode) (stx : Syntax) : LowerM Term :=
  (lowerExprM mode stx).run ctx

open Lean Elab Command in
private def lowerExprCollectingHoists (ctx : LowerCtx) (mode : ExprMode) (stx : Syntax) :
    LowerM (Term × Array HoistedStep) := do
  let saved := (← get).hoisted
  modify fun s => { s with hoisted := #[] }
  let term ← lowerExpr ctx mode stx
  let steps := (← get).hoisted
  modify fun s => { s with hoisted := saved }
  return (term, steps)

/-! ## LValue Mutation Path Parsing & Functional Lens Construction -/

private inductive LValStep where
  | field (id : Lean.Ident)
  | index (idxTerm : Lean.Term)

open Lean Elab Command in
private partial def parseLValPath (ctx : LowerCtx) (stx : Syntax) :
    LowerM (Ident × Array LValStep) := do
  let k := stx.getKind
  if k == ``qedIdent then
    let comps := stx[0].getId.components
    match comps with
    | [] => throwErrorAt stx "invalid assignment target"
    | root :: rest =>
        let rStr := root.toString
        unless ctx.stateFields.contains rStr do
          if ctx.locals.contains rStr || ctx.envVars.contains rStr || rStr == "ctx" then
            throwErrorAt stx s!"cannot mutate `{rStr}`: parameters, `env` bindings, and `let` bindings are immutable; only `state` fields may be mutated"
          else
            throwErrorAt stx s!"cannot mutate unknown state field `{rStr}`"
        let _ ← checkStateRead stx ctx rStr
        recordMutated rStr
        let steps := rest.toArray.map fun f => LValStep.field (mkIdentFrom stx f)
        return (mkIdentFrom stx root, steps)
  else if k == ``qedProj then
    let (rootId, prevSteps) ← parseLValPath ctx stx[0]
    let fldId : Ident := ⟨stx[2]⟩
    return (rootId, prevSteps.push (.field fldId))
  else if k == ``qedIndex then
    let (rootId, prevSteps) ← parseLValPath ctx stx[0]
    let idxTerm ← lowerExpr ctx .val stx[2]
    return (rootId, prevSteps.push (.index idxTerm))
  else
    throwErrorAt stx "invalid mutation target; expected `stateField`, `stateField.sub`, or `stateField[i].sub`"

open Lean Elab Command in
private partial def withUpdatedPathCPS (steps : Array LValStep) (idx : Nat) (curVal : Term)
    (mkLeafNew : Term → LowerM Term) (k : Term → LowerM Term) : LowerM Term := do
  if h : idx < steps.size then
    match steps[idx] with
    | .field fid =>
        let child ← `(($curVal).$fid:ident)
        withUpdatedPathCPS steps (idx + 1) child mkLeafNew fun updatedChild => do
          let updatedStruct ← `({ $curVal with $fid:ident := srvAutoField($updatedChild) })
          k updatedStruct
    | .index idxT =>
        let elemId ← freshIdent "_elem"
        let hElemId ← freshIdent "_srvEqElem"
        let body ← withUpdatedPathCPS steps (idx + 1) ⟨elemId⟩ mkLeafNew fun updatedElem => do
          let setTerm ← `(srvSetElem($curVal, $idxT, $updatedElem))
          k setTerm
        `(Qed.Server.srvLetEq (srvGetElem($curVal, $idxT)) (fun $elemId:ident $hElemId:ident => $body))
  else
    let leafNew ← mkLeafNew curVal
    k leafNew

open Lean Elab Command in
private def getPureOverrides (ctx : LowerCtx) : Array (String × Ident) :=
  match ctx.stateRule with
  | .pureStep _ ovs => ovs
  | _ => #[]

open Lean Elab Command in
private def setPureOverride (ctx : LowerCtx) (sCur : Ident) (fld : String) (vId : Ident) : LowerCtx :=
  let ovs := (getPureOverrides ctx).filter (·.1 != fld)
  { ctx with stateRule := .pureStep sCur (ovs.push (fld, vId)) }

open Lean Elab Command in
private def materializeState (sCur : Ident) (overrides : Array (String × Ident)) : CommandElabM Term := do
  if overrides.isEmpty then
    `(($sCur))
  else
    let fIds : Array Ident := overrides.map fun p => mkIdent (Name.mkSimple p.1)
    let fVars : Array Term := overrides.map fun p => ⟨p.2.raw⟩
    `({ $sCur with $[$fIds:ident := $fVars:term],* })

/-! ## Return Value Auto-Lifting & Hoist Wrapping -/

open Lean Elab Command in
private def isFailCall (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx
  u.getKind == ``qedCall && u[0].getKind == ``qedIdent && u[0][0].getId == `fail

open Lean Elab Command in
private def wrapOkValue (ctx : LowerCtx) (valTerm : Term) : CommandElabM Term := do
  if let some innerTy := ctx.innerOptTy? then
    if valTerm.raw.isIdent && valTerm.raw.getId.eraseMacroScopes == `none then
      `(Except.ok (none : Option $innerTy))
    else
      `(Except.ok (Qed.Server.SrvLiftOpt.liftOpt (Inner := $innerTy) $valTerm))
  else
    `(Except.ok (srvAutoField($valTerm)))

open Lean Elab Command in
private def errTyOf (ctx : LowerCtx) : CommandElabM Term :=
  match ctx.domainErrTy? with
  | some et => `(Qed.Server.SrvFailure $et)
  | none    => `(Qed.Server.ApiError)

open Lean Elab Command in
private def wrapHoistsPure (ctx : LowerCtx) (s₀ : Ident) (matState : Term)
    (steps : Array HoistedStep) (body : Term) : LowerM Term := do
  let errTy ← liftM <| errTyOf ctx
  steps.foldrM (init := body) fun step acc => do
    match step with
    | .awaitUnwrap ref _ _ =>
        throwErrorAt ref "`await` cannot appear inside a pure/atomic block"
    | .pureUnwrap _ tmp valTerm =>
        if !ctx.hasFallible then
          if let some innerTy := ctx.innerOptTy? then
            return ← `(match Qed.Server.SrvUnwrapOpt.unwrapOpt (Inner := $innerTy) $valTerm with
              | Except.error (Except.ok none) => ($matState, some (Except.ok none))
              | Except.error (Except.error _e) => ($s₀, some (Except.error _e))
              | Except.ok $tmp:ident => $acc)
        `(match Qed.Server.SrvUnwrap.unwrap (E := $errTy) $valTerm with
          | Except.error _e => ($s₀, some (Except.error _e))
          | Except.ok $tmp:ident => $acc)

open Lean Elab Command in
private def mkAsyncUnwrapMatch (ctx : LowerCtx) (tmp : Ident) (valTerm acc : Term) : CommandElabM Term := do
  if !ctx.hasFallible then
    if let some innerTy := ctx.innerOptTy? then
      return ← `(match Qed.Server.SrvUnwrapOpt.unwrapOpt (Inner := $innerTy) $valTerm with
        | Except.error _early => Pure.pure (some _early)
        | Except.ok $tmp:ident => $acc)
  let errTy ← errTyOf ctx
  `(match Qed.Server.SrvUnwrap.unwrap (E := $errTy) $valTerm with
    | Except.error _e => Pure.pure (some (Except.error _e))
    | Except.ok $tmp:ident => $acc)

open Lean Elab Command in
private def wrapHoistsAsync (ctx : LowerCtx)
    (steps : Array HoistedStep) (body : Term) : LowerM Term := do
  steps.foldrM (init := body) fun step acc => do
    match step with
    | .awaitUnwrap _ tmp callTerm =>
        let rawTmp ← freshIdent "_srvRaw"
        `($callTerm >>= fun $rawTmp:ident => $(← liftM <| mkAsyncUnwrapMatch ctx tmp ⟨rawTmp⟩ acc))
    | .pureUnwrap _ tmp valTerm =>
        liftM <| mkAsyncUnwrapMatch ctx tmp valTerm acc

open Lean Elab Command in
private def bindOptIdent (xStx : Syntax) (val cont : Term) : CommandElabM Term :=
  if xStx.isIdent then
    let xId : Ident := ⟨xStx⟩
    `(let $xId:ident := $val; $cont)
  else
    `(let _ := $val; $cont)

open Lean Elab Command in
private def bindSrvLetEq (xStx : Syntax) (val cont : Term) : LowerM Term := do
  let xId ← if xStx.isIdent then pure ⟨xStx⟩ else freshIdent "_srvDiscard"
  let hEq ← freshIdent "_srvEq"
  `(Qed.Server.srvLetEq $val (fun $xId:ident $hEq:ident => $cont))

open Lean Elab Command in
private def pushOptLocal (ctx : LowerCtx) (xStx : Syntax) : LowerCtx :=
  if xStx.isIdent then { ctx with locals := ctx.locals.push xStx.getId.toString } else ctx

open Lean Elab Command in
private def isBareUnwrapExpr (allowAwait : Bool) (eStx : Syntax) : Bool :=
  let u := unwrapParens1 eStx
  u.getKind == ``qedUnwrap ||
  (allowAwait && u.getKind == ``qedAwait && (unwrapParens1 u[1]).getKind == ``qedUnwrap) ||
  (eStx.getKind == ``qedIdent && eStx[0].getId.toString.endsWith "?") ||
  (eStx.getKind == ``qedProj && eStx[2].getId.toString.endsWith "?")

/-! ## Pure Statement Block Lowering (`lowerPureBlock` — for Sync `def`s & `atomic:` Blocks) -/

open Lean Elab Command in
private partial def lowerCatchFallback? (ctx : LowerCtx) (stmts : Array Syntax) : LowerM (Option Term) := do
  if stmts.isEmpty then
    return none
  else if stmts.size == 1 && stmts[0]!.getKind == ``qedStmtExpr then
    let eStx := stmts[0]![0]
    if exprHasAwait eStx || exprHasUnwrap eStx || (matchPushCall? eStx).isSome then return none
    let (eTerm, steps) ← lowerExprCollectingHoists { ctx with allowAwait := false } .val eStx
    if !steps.isEmpty then return none
    some <$> `(srvAutoField($eTerm))
  else if stmts[0]!.getKind == ``qedStmtLet && stmts[0]![5].getNumArgs == 0 then
    let st := stmts[0]!
    let rhsStx := st[4]
    if exprHasAwait rhsStx || exprHasUnwrap rhsStx then return none
    let (rhsTerm, steps) ← lowerExprCollectingHoists { ctx with allowAwait := false } .val rhsStx
    if !steps.isEmpty then return none
    let checkedRhs ← `(srvRejectUnhandledErr($rhsTerm))
    let some tailTerm ← lowerCatchFallback? (pushOptLocal ctx st[1]) (stmts.extract 1 stmts.size)
      | return none
    some <$> liftM (bindOptIdent st[1] checkedRhs tailTerm)
  else
    return none

open Lean Elab Command in
private def lowerMatchScrutineesAndAlts (ctx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (lowerArm : LowerCtx → Array Syntax → LowerM Term) : LowerM (Term × Array HoistedStep) := do
  let mut scrutTerms : Array Term := #[]
  let mut allSteps : Array HoistedStep := #[]
  for sc in stmt[1].getSepArgs do
    let (st, ss) ← lowerExprCollectingHoists ctx .val sc
    scrutTerms := scrutTerms.push st
    allSteps := allSteps ++ ss
  let cases := stmt[3].getArgs
  let allRet := cases.all fun c => blockAlwaysReturns (suiteStmts c[3])
  let alts ← cases.mapM fun c => do
    let pats ← c[1].getSepArgs.mapM fun p => liftMacroM (lowerQedPat p)
    let pIds := (c[1].getSepArgs.flatMap collectQedPatIds).map (·.toString)
    let cBody ← lowerArm { ctx with locals := ctx.locals ++ pIds } (suiteStmts c[3] ++ if allRet then #[] else rest)
    `(Lean.Parser.Term.matchAltExpr| | $[$pats:term],* => $cBody)
  return (← `(match $[$scrutTerms:term],* with $[$alts:matchAlt]*), allSteps)

open Lean Elab Command in
partial def lowerPureBlock (ctx : LowerCtx) (inAtomic : Bool) (s₀ sCur : Ident)
    (stmts : Array Syntax) : LowerM Term := do
  let curOverrides := getPureOverrides ctx
  let matCur ← liftM <| materializeState sCur curOverrides
  if stmts.isEmpty then
    return ← `(($matCur, none))
  let stmt := stmts[0]!
  let rest := stmts.extract 1 stmts.size
  let k := stmt.getKind
  let pCtx := { ctx with
    stateRule := if ctx.stateFields.isEmpty then .statelessServer else .pureStep sCur curOverrides
    allowAwait := false }

  let lowerPureBranch (thenCtx : LowerCtx) (thenStmts : Array Syntax)
      (elseStmts? : Option (Array Syntax)) (allowPureLetJoin : Bool)
      (mkBranch : Term → Term → CommandElabM Term) : LowerM Term := do
    let thenRet := blockAlwaysReturns thenStmts
    let elseRet := elseStmts?.map blockAlwaysReturns |>.getD false
    let lowerElseOpt (es? : Option (Array Syntax)) : LowerM Term :=
      match es? with
      | some es => lowerPureBlock pCtx inAtomic s₀ sCur es
      | none    => `(($matCur, none))
    if rest.isEmpty then
      liftM =<< (mkBranch <$> lowerPureBlock thenCtx inAtomic s₀ sCur thenStmts <*> lowerElseOpt elseStmts?)
    else if thenRet && !elseRet then
      liftM =<< (mkBranch <$> lowerPureBlock thenCtx inAtomic s₀ sCur thenStmts
                          <*> lowerPureBlock pCtx inAtomic s₀ sCur ((elseStmts?.getD #[]) ++ rest))
    else if !thenRet && elseRet then
      liftM =<< (mkBranch <$> lowerPureBlock thenCtx inAtomic s₀ sCur (thenStmts ++ rest)
                          <*> lowerPureBlock pCtx inAtomic s₀ sCur (elseStmts?.getD #[]))
    else
      let br ← liftM =<< (mkBranch <$> lowerPureBlock thenCtx inAtomic s₀ sCur thenStmts <*> lowerElseOpt elseStmts?)
      let sNext ← freshIdent "_s"
      let joinCtx := { pCtx with stateRule := if ctx.stateFields.isEmpty then .statelessServer else .pureStep sNext #[] }
      let cont ← lowerPureBlock joinCtx inAtomic s₀ sNext rest
      if allowPureLetJoin && !blockMayReturnEarly thenStmts && !(elseStmts?.map blockMayReturnEarly |>.getD false) then
        let hJoin ← freshIdent "_srvEq"
        `(Qed.Server.srvLetEq (($br).1) (fun $sNext:ident $hJoin:ident => $cont))
      else
        `(Qed.Server.srvSeq $br (fun $sNext:ident => $cont))

  if k == ``qedStmtPass then
    lowerPureBlock pCtx inAtomic s₀ sCur rest

  else if k == ``qedStmtAtomic || k == ``qedStmtLetAtomic || k == ``qedStmtReturnAtomic then
    if inAtomic then throwErrorAt stmt "nested `atomic` blocks are forbidden"
    else if ctx.stateFields.isEmpty then throwErrorAt stmt "`atomic` is only valid in a `server` with `state` declarations"
    else throwErrorAt stmt s!"redundant `atomic` block: `{ctx.fnName}` has no `await` calls, so it already executes atomically"

  else if k == ``qedStmtEnsure then
    let (condTerm, steps) ← lowerExprCollectingHoists pCtx .propGuard stmt[1]
    let hGuard ← freshIdent "_srvG"
    let elseRetStmt := ensureElseToReturnStmt stmt stmt[3]
    let thenBranch ← lowerPureBlock pCtx inAtomic s₀ sCur rest
    let elseBranch ← lowerPureBlock pCtx inAtomic s₀ sCur #[elseRetStmt]
    wrapHoistsPure pCtx s₀ matCur steps (← `(if $hGuard:ident : $condTerm then $thenBranch else $elseBranch))

  else if k == ``qedStmtReturn then
    if stmt[1].getNumArgs == 0 then
      `(($matCur, some $(← wrapOkValue pCtx (← `(())))))
    else
      let retExpr := stmt[1][0]
      if exprHasAwait retExpr && !(unwrapParens1 retExpr).isOfKind ``qedUnwrap then
        throwErrorAt retExpr "`await` cannot be used inside a synchronous or `atomic` block"
      if isFailCall retExpr then
        unless pCtx.hasFallible do
          throwErrorAt retExpr s!"`fail(...)` can only be returned from a fallible `T!` function (`{pCtx.fnName}` is not declared `-> ...!`)"
        let (errTerm, steps) ← lowerExprCollectingHoists pCtx .val retExpr
        wrapHoistsPure pCtx s₀ matCur steps (← `(($s₀, some (Except.error $errTerm))))
      else
        let (valTerm, steps) ← lowerExprCollectingHoists pCtx .val retExpr
        wrapHoistsPure pCtx s₀ matCur steps (← `(($matCur, some $(← wrapOkValue pCtx valTerm))))

  else if k == ``qedStmtLet then
    let xStx := stmt[1]
    let rhsStx := stmt[4]
    if stmt[5].getNumArgs == 1 then
      let catchNode := stmt[5][0][1]
      if catchNode.getKind == `Qed.Lang.catchArms then
        throwErrorAt catchNode "multi-arm `catch: case ...` is for client components; in server functions use `catch err:`"
      let binderStx := catchNode[0]
      let catchStmts := suiteStmts catchNode[2]
      if rhsStx.getKind == ``qedAwait then
        throwErrorAt rhsStx "`await` cannot be used inside a synchronous or `atomic` block"
      let (rhsTerm, steps) ← lowerExprCollectingHoists pCtx .val rhsStx
      let errId : Ident := if binderStx.isIdent then ⟨binderStx⟩ else mkIdent `_srvCatchErr
      let catchCtx := pushOptLocal pCtx binderStx
      let okTerm ← lowerPureBlock (pushOptLocal pCtx xStx) inAtomic s₀ sCur rest
      if let some fbTerm ← lowerCatchFallback? catchCtx catchStmts then
        let okValId ← freshIdent "_catchOk"
        let valMatch ← `(match Qed.Server.SrvUnwrap.unwrap (E := Qed.Server.ApiError) $rhsTerm with
          | Except.error $errId:ident => $fbTerm | Except.ok $okValId:ident => $okValId)
        wrapHoistsPure pCtx s₀ matCur steps (← bindSrvLetEq xStx valMatch okTerm)
      else
        unless blockAlwaysReturns catchStmts do
          throwErrorAt stmt "the `catch` block must either `return` on all paths or end with a fallback value expression"
        let catchTerm ← lowerPureBlock catchCtx inAtomic s₀ sCur catchStmts
        let bindId : Ident := if xStx.isIdent then ⟨xStx⟩ else mkIdent `_srvDiscard
        wrapHoistsPure pCtx s₀ matCur steps (← `(match Qed.Server.SrvUnwrap.unwrap (E := Qed.Server.ApiError) $rhsTerm with
          | Except.error $errId:ident => $catchTerm | Except.ok $bindId:ident => $okTerm))
    else
      let (rhsTerm, steps) ← lowerExprCollectingHoists pCtx .val rhsStx
      let checkedRhs ← if steps.isEmpty then `(srvRejectUnhandledErr($rhsTerm)) else pure rhsTerm
      let cont ← lowerPureBlock (pushOptLocal pCtx xStx) inAtomic s₀ sCur rest
      wrapHoistsPure pCtx s₀ matCur steps (← bindSrvLetEq xStx checkedRhs cont)

  else if k == ``qedStmtAssign || (k == ``qedStmtExpr && (matchPushCall? stmt[0]).isSome) then
    let lowerPureMutation (lvalStx : Syntax) (steps : Array HoistedStep)
        (mkLeaf : Array LValStep → Term → LowerM Term) : LowerM Term := do
      let (rootField, pathSteps) ← parseLValPath pCtx lvalStx
      let curRoot ← resolveStateFieldBase lvalStx pCtx rootField.getId
      let fNext ← freshIdent s!"_fld_{rootField.getId}_"
      let hFNext ← freshIdent "_srvEq"
      let cont ← lowerPureBlock (setPureOverride pCtx sCur rootField.getId.toString fNext) inAtomic s₀ sCur rest
      let chain ← withUpdatedPathCPS pathSteps 0 curRoot (mkLeaf pathSteps) fun updatedRaw => do
        let updatedRoot ← if pathSteps.isEmpty then `(srvTypedAs(($sCur).$rootField:ident, $updatedRaw)) else pure updatedRaw
        `(Qed.Server.srvLetEq $updatedRoot (fun $fNext:ident $hFNext:ident => $cont))
      wrapHoistsPure pCtx s₀ matCur steps chain
    if k == ``qedStmtAssign then
      let opStr := (stmt[1].reprint.getD "=").trimAscii.toString
      let (rhsTerm, steps) ← lowerExprCollectingHoists pCtx .val stmt[2]
      lowerPureMutation stmt[0] steps fun pathSteps curLeaf => do
        let val ←
          if opStr == "=" then pure rhsTerm
          else if opStr == "+=" then `(Qed.Lang.QedVal.val $curLeaf + Qed.Lang.QedVal.val $rhsTerm)
          else if opStr == "-=" then `(Qed.Lang.QedVal.val $curLeaf - Qed.Lang.QedVal.val $rhsTerm)
          else throwErrorAt stmt[1] s!"unsupported assignment operator `{opStr}`"
        if pathSteps.isEmpty then `(srvAutoField($val)) else pure val
    else
      let some (targetStx, elemStx) := matchPushCall? stmt[0] | unreachable!
      let (elemTerm, steps) ← lowerExprCollectingHoists pCtx .val elemStx
      lowerPureMutation targetStx steps fun _ curArr =>
        `(($curArr).push (srvAutoField($elemTerm)))

  else if k == ``qedStmtExpr then
    let eStx := stmt[0]
    let (eTerm, steps) ← lowerExprCollectingHoists pCtx .val eStx
    let cont ← lowerPureBlock pCtx inAtomic s₀ sCur rest
    let valTerm ← if isBareUnwrapExpr false eStx then pure eTerm else `(srvEnsureUnit($eTerm))
    let xId ← freshIdent "_srvDiscard"
    let hEq ← freshIdent "_srvEq"
    let body ← `(Qed.Server.srvLetEq $valTerm (fun $xId:ident $hEq:ident => $cont))
    wrapHoistsPure pCtx s₀ matCur steps body

  else if k == ``qedStmtIf then
    let (condTerm, steps) ← lowerExprCollectingHoists pCtx .propGuard stmt[1]
    let hGuard ← freshIdent "_srvG"
    let br ← lowerPureBranch pCtx (suiteStmts stmt[3]) (desugarElifs stmt[4].getArgs stmt[5]) true
      fun t e => `(if $hGuard:ident : $condTerm then $t else $e)
    wrapHoistsPure pCtx s₀ matCur steps br

  else if k == ``qedStmtIfLet then
    let patStx := stmt[2]
    let patTerm ← liftMacroM (lowerQedPat patStx)
    let patIds := (collectQedPatIds patStx).map (·.toString)
    let (scrutTerm, steps) ← lowerExprCollectingHoists pCtx .val stmt[4]
    let thenCtx := { pCtx with locals := pCtx.locals ++ patIds }
    let br ← lowerPureBranch thenCtx (suiteStmts stmt[6]) (extractElseSuite stmt[7]) false
      fun t e => `(match $scrutTerm:term with | $patTerm => $t | _ => $e)
    wrapHoistsPure pCtx s₀ matCur steps br

  else if k == ``qedStmtMatch then
    let (matchT, allSteps) ← lowerMatchScrutineesAndAlts pCtx stmt rest (lowerPureBlock · inAtomic s₀ sCur)
    wrapHoistsPure pCtx s₀ matCur allSteps matchT

  else
    throwErrorAt stmt s!"unsupported statement in `{ctx.fnName}` ({k})"

/-! ## Stateless Pure/Async & Stateful Async Block Lowering (`lowerAsyncBlock`) -/

open Lean Elab Command in
private def lowerScopedAtomicBody (stmt : Syntax) (atomCtx : LowerCtx) (stateTyTerm? : Option Term)
    (atomStmts : Array Syntax) : LowerM (Term × Ident × Term × Bool) := do
  let some stateTyTerm := stateTyTerm?
    | throwErrorAt stmt "`atomic` is only valid in a `server` with `state` declarations"
  if blockHasAwait atomStmts then
    throwErrorAt stmt "cannot use `await` inside an `atomic` block; perform external I/O outside `atomic` so shared locks never span network calls"
  let s0Id ← freshIdent "_sAtom"
  let savedMut := (← get).mutated
  modify fun s => { s with mutated := #[] }
  let atomBody ← lowerPureBlock atomCtx (inAtomic := true) s0Id s0Id atomStmts
  let atomMut := (← get).mutated
  modify fun s => { s with mutated := savedMut ++ atomMut.filter (!savedMut.contains ·) }
  return (stateTyTerm, s0Id, atomBody, atomMut.isEmpty)

open Lean Elab Command in
partial def lowerAsyncBlock (ctx : LowerCtx) (stateTyTerm? : Option Term) (stmts : Array Syntax) :
    LowerM Term := do
  if stmts.isEmpty then
    return ← `(Pure.pure none)
  let stmt := stmts[0]!
  let rest := stmts.extract 1 stmts.size
  let k := stmt.getKind
  let aCtx := { ctx with
    stateRule := if ctx.stateFields.isEmpty then .statelessServer else .forbidAsyncOutsideAtomic
    allowAwait := true }

  let lowerAsyncBranch (thenCtx : LowerCtx) (thenStmts : Array Syntax)
      (elseStmts? : Option (Array Syntax)) (mkBranch : Term → Term → CommandElabM Term) : LowerM Term := do
    let thenRet := blockAlwaysReturns thenStmts
    let elseRet := elseStmts?.map blockAlwaysReturns |>.getD false
    let lowerElseOpt (es? : Option (Array Syntax)) : LowerM Term :=
      match es? with
      | some es => lowerAsyncBlock aCtx stateTyTerm? es
      | none    => `(Pure.pure none)
    if rest.isEmpty then
      liftM =<< (mkBranch <$> lowerAsyncBlock thenCtx stateTyTerm? thenStmts <*> lowerElseOpt elseStmts?)
    else if thenRet && !elseRet then
      liftM =<< (mkBranch <$> lowerAsyncBlock thenCtx stateTyTerm? thenStmts
                          <*> lowerAsyncBlock aCtx stateTyTerm? ((elseStmts?.getD #[]) ++ rest))
    else if !thenRet && elseRet then
      liftM =<< (mkBranch <$> lowerAsyncBlock thenCtx stateTyTerm? (thenStmts ++ rest)
                          <*> lowerAsyncBlock aCtx stateTyTerm? (elseStmts?.getD #[]))
    else
      let br ← liftM =<< (mkBranch <$> lowerAsyncBlock thenCtx stateTyTerm? thenStmts <*> lowerElseOpt elseStmts?)
      let cont ← lowerAsyncBlock aCtx stateTyTerm? rest
      `(Qed.Server.srvSeqM $br (fun _ => $cont))

  if k == ``qedStmtPass then
    lowerAsyncBlock aCtx stateTyTerm? rest

  else if k == ``qedStmtAtomic then
    let (stateTyTerm, s0Id, atomBody, readOnly) ← lowerScopedAtomicBody stmt aCtx stateTyTerm? (suiteStmts stmt[2])
    let earlyId ← freshIdent "_atomEarly"
    let cont ← lowerAsyncBlock aCtx stateTyTerm? rest
    let runCall ← if readOnly then
      `(Qed.Server.MonadAtomic.runAtomicRead (fun ($s0Id:ident : $stateTyTerm) => ($atomBody).2))
    else
      `(Qed.Server.MonadAtomic.runAtomic (fun ($s0Id:ident : $stateTyTerm) => Qed.Server.srvAtomicCommit $s0Id $atomBody))
    `($runCall >>= fun $earlyId:ident => match $earlyId:ident with | some _r => Pure.pure (some _r) | none => $cont)

  else if k == ``qedStmtReturnAtomic then
    let atomStmts := suiteStmts stmt[3]
    unless blockAlwaysReturns atomStmts do
      throwErrorAt stmt "`return atomic:` block must `return` a value on every path"
    let (stateTyTerm, s0Id, atomBody, readOnly) ← lowerScopedAtomicBody stmt aCtx stateTyTerm? atomStmts
    let resId ← freshIdent "_atomRet"
    let runCall ← if readOnly then
      `(Qed.Server.MonadAtomic.runAtomicRead (fun ($s0Id:ident : $stateTyTerm) => (Qed.Server.srvFinish $s0Id $atomBody).2))
    else
      `(Qed.Server.MonadAtomic.runAtomic (fun ($s0Id:ident : $stateTyTerm) => Qed.Server.srvFinish $s0Id $atomBody))
    `($runCall >>= fun $resId:ident => Pure.pure (some $resId))

  else if k == ``qedStmtLetAtomic then
    let xId : Ident := ⟨stmt[1]⟩
    let atomStmts := suiteStmts stmt[5]
    unless blockAlwaysReturns atomStmts do
      throwErrorAt stmt s!"`let {xId.getId} = atomic:` block must `return` a value on every path"
    let letAtomCtx := { aCtx with innerOptTy? := none, isOption := false }
    let (stateTyTerm, s0Id, atomBody, readOnly) ← lowerScopedAtomicBody stmt letAtomCtx stateTyTerm? atomStmts
    let resId ← freshIdent "_atomRes"
    let cont ← lowerAsyncBlock (pushOptLocal aCtx stmt[1]) stateTyTerm? rest
    let runCall ← if readOnly then
      `(Qed.Server.MonadAtomic.runAtomicRead (fun ($s0Id:ident : $stateTyTerm) => (Qed.Server.srvFinish $s0Id $atomBody).2))
    else
      `(Qed.Server.MonadAtomic.runAtomic (fun ($s0Id:ident : $stateTyTerm) => Qed.Server.srvFinish $s0Id $atomBody))
    `($runCall >>= fun $resId:ident => match $resId:ident with
        | Except.error _e => Pure.pure (some (Except.error _e)) | Except.ok $xId:ident => $cont)

  else if k == ``qedStmtEnsure then
    let (condTerm, steps) ← lowerExprCollectingHoists aCtx .propGuard stmt[1]
    let hGuard ← freshIdent "_srvG"
    let elseRetStmt := ensureElseToReturnStmt stmt stmt[3]
    let thenBranch ← lowerAsyncBlock aCtx stateTyTerm? rest
    let elseBranch ← lowerAsyncBlock aCtx stateTyTerm? #[elseRetStmt]
    wrapHoistsAsync aCtx steps (← `(if $hGuard:ident : $condTerm then $thenBranch else $elseBranch))

  else if k == ``qedStmtReturn then
    if stmt[1].getNumArgs == 0 then
      `(Pure.pure (some $(← wrapOkValue aCtx (← `(())))))
    else
      let retExpr := stmt[1][0]
      let uRet := unwrapParens1 retExpr
      if uRet.getKind == ``qedAwait && !(unwrapParens1 uRet[1]).isOfKind ``qedUnwrap then
        unless aCtx.hasFallible do
          throwErrorAt retExpr s!"`return await ...` without `catch` requires `{aCtx.fnName}` to have a fallible `T!` return type"
        let (callTerm, steps) ← lowerExprCollectingHoists aCtx .val uRet[1]
        let rawId ← freshIdent "_retAw"
        let errTy ← liftM <| errTyOf aCtx
        let leaf ← match aCtx.innerOptTy? with
          | some innerTy =>
              `($callTerm >>= fun $rawId:ident => Pure.pure (some (match $rawId:ident with
                | Except.ok _v => Except.ok (Qed.Server.SrvLiftOpt.liftOpt (Inner := $innerTy) _v)
                | Except.error _e => Except.error (Qed.Server.SrvErr.ofApi (E := $errTy) _e))))
          | none =>
              `($callTerm >>= fun $rawId:ident => Pure.pure (some (Qed.Server.SrvUnwrap.unwrap (E := $errTy) $rawId)))
        wrapHoistsAsync aCtx steps leaf
      else if isFailCall retExpr then
        unless aCtx.hasFallible do
          throwErrorAt retExpr s!"`fail(...)` can only be returned from a fallible `T!` function (`{aCtx.fnName}` is not declared `-> ...!`)"
        let (errTerm, steps) ← lowerExprCollectingHoists aCtx .val retExpr
        wrapHoistsAsync aCtx steps (← `(Pure.pure (some (Except.error $errTerm))))
      else
        let (valTerm, steps) ← lowerExprCollectingHoists aCtx .val retExpr
        wrapHoistsAsync aCtx steps (← `(Pure.pure (some $(← wrapOkValue aCtx valTerm))))

  else if k == ``qedStmtLet then
    let xStx := stmt[1]
    let rhsRaw := stmt[4]
    if stmt[5].getNumArgs == 1 then
      let catchNode := stmt[5][0][1]
      if catchNode.getKind == `Qed.Lang.catchArms then
        throwErrorAt catchNode "multi-arm `catch: case ...` is for client components; in server functions use `catch err:`"
      let rhsStx := unwrapParens1 rhsRaw
      let binderStx := catchNode[0]
      let catchStmts := suiteStmts catchNode[2]
      let errId : Ident := if binderStx.isIdent then ⟨binderStx⟩ else mkIdent `_srvCatchErr
      let catchCtx := pushOptLocal aCtx binderStx
      let okTerm ← lowerAsyncBlock (pushOptLocal aCtx xStx) stateTyTerm? rest
      let (scrutTerm, steps, awaitCall?) : Term × Array HoistedStep × Option (Term × Ident) ←
        if rhsStx.getKind == ``qedAwait then
          let (callTerm, steps) ← lowerExprCollectingHoists aCtx .val rhsStx[1]
          let rawId ← freshIdent "_catchAw"
          pure ((⟨rawId⟩ : Term), steps, some (callTerm, rawId))
        else
          let (rhsTerm, steps) ← lowerExprCollectingHoists aCtx .val rhsStx
          pure (rhsTerm, steps, none)
      let innerTerm ←
        if let some fbTerm ← lowerCatchFallback? catchCtx catchStmts then
          let okValId ← freshIdent "_catchOk"
          let valMatch ← `(match Qed.Server.SrvUnwrap.unwrap (E := Qed.Server.ApiError) $scrutTerm with
            | Except.error $errId:ident => $fbTerm | Except.ok $okValId:ident => $okValId)
          liftM <| bindOptIdent xStx valMatch okTerm
        else
          unless blockAlwaysReturns catchStmts do
            throwErrorAt stmt "the `catch` block must either `return` on all paths or end with a fallback value expression"
          let catchTerm ← lowerAsyncBlock catchCtx stateTyTerm? catchStmts
          let bindId : Ident := if xStx.isIdent then ⟨xStx⟩ else mkIdent `_srvDiscard
          `(match Qed.Server.SrvUnwrap.unwrap (E := Qed.Server.ApiError) $scrutTerm with
            | Except.error $errId:ident => $catchTerm | Except.ok $bindId:ident => $okTerm)
      let awaitedTerm ← match awaitCall? with
        | some (callTerm, rawId) => `($callTerm >>= fun $rawId:ident => $innerTerm)
        | none                   => pure innerTerm
      wrapHoistsAsync aCtx steps awaitedTerm
    else
      let (rhsTerm, steps) ← lowerExprCollectingHoists aCtx .val rhsRaw
      let checkedRhs ← if steps.isEmpty then `(srvRejectUnhandledErr($rhsTerm)) else pure rhsTerm
      let cont ← lowerAsyncBlock (pushOptLocal aCtx xStx) stateTyTerm? rest
      wrapHoistsAsync aCtx steps (← liftM <| bindOptIdent xStx checkedRhs cont)

  else if k == ``qedStmtAssign then
    let _ ← parseLValPath aCtx stmt[0]
    throwErrorAt stmt "unexpected state mutation outside `atomic`"

  else if k == ``qedStmtExpr then
    let eStx := stmt[0]
    if let some (targetStx, _) := matchPushCall? eStx then
      let _ ← parseLValPath aCtx targetStx
      throwErrorAt stmt "unexpected state `.push(...)` outside `atomic`"
    else
      let (eTerm, steps) ← lowerExprCollectingHoists aCtx .val eStx
      let cont ← lowerAsyncBlock aCtx stateTyTerm? rest
      let body ← if isBareUnwrapExpr true eStx then `(let _ := $eTerm; $cont) else `(let _ : Unit := srvEnsureUnit($eTerm); $cont)
      wrapHoistsAsync aCtx steps body

  else if k == ``qedStmtIf then
    let (condTerm, steps) ← lowerExprCollectingHoists aCtx .propGuard stmt[1]
    let hGuard ← freshIdent "_srvG"
    let br ← lowerAsyncBranch aCtx (suiteStmts stmt[3]) (desugarElifs stmt[4].getArgs stmt[5])
      fun t e => `(if $hGuard:ident : $condTerm then $t else $e)
    wrapHoistsAsync aCtx steps br

  else if k == ``qedStmtIfLet then
    let patStx := stmt[2]
    let patTerm ← liftMacroM (lowerQedPat patStx)
    let patIds := (collectQedPatIds patStx).map (·.toString)
    let (scrutTerm, steps) ← lowerExprCollectingHoists aCtx .val stmt[4]
    let thenCtx := { aCtx with locals := aCtx.locals ++ patIds }
    let br ← lowerAsyncBranch thenCtx (suiteStmts stmt[6]) (extractElseSuite stmt[7])
      fun t e => `(match $scrutTerm:term with | $patTerm => $t | _ => $e)
    wrapHoistsAsync aCtx steps br

  else if k == ``qedStmtMatch then
    let (matchT, allSteps) ← lowerMatchScrutineesAndAlts aCtx stmt rest (lowerAsyncBlock · stateTyTerm?)
    wrapHoistsAsync aCtx allSteps matchT

  else
    throwErrorAt stmt s!"unsupported async statement in `{ctx.fnName}` ({k})"

/-! ## `server` Command Elaborator -/

private structure ParsedEnvDecl where
  ref      : Lean.Syntax
  ident    : Lean.Ident
  osKey    : String
  default? : Option String

private structure ParsedStateDecl where
  ref      : Lean.Syntax
  ident    : Lean.Ident
  ty       : ParsedSrvType
  initStx  : Lean.Syntax

private structure ParsedMutInv where
  ref      : Lean.Syntax
  fieldId  : Lean.Ident
  condStx  : Lean.Syntax
  label    : String

private structure ParsedInv where
  ref      : Lean.Syntax
  exprStx  : Lean.Syntax
  isTwoSt  : Bool
  label    : String

private structure ParsedFnParam where
  ident    : Lean.Ident
  ty       : ParsedSrvType
  tyTerm   : Lean.Term

open Lean Elab Command in
private def buildTupleType (tys : Array Term) : CommandElabM Term := do
  if tys.isEmpty then `(Unit)
  else if tys.size == 1 then return tys[0]!
  else
    let mut acc := tys.back!
    for revIdx in [1:tys.size] do
      acc ← `($(tys[tys.size - 1 - revIdx]!) × $acc)
    return acc

open Lean Elab Command in
private def extractTupleProjections (reqVar : Ident) (n : Nat) : CommandElabM (Array Term) := do
  if n == 0 then return #[]
  else if n == 1 then return #[⟨reqVar.raw⟩]
  else
    let mut out : Array Term := #[]
    let mut cur : Term := ⟨reqVar.raw⟩
    for i in [0:n] do
      if i + 1 < n then
        out := out.push (← `(($cur).1))
        cur ← `(($cur).2)
      else
        out := out.push cur
    return out

open Lean Elab Command in
private def computeInnerOptTerm? (retTy : ParsedSrvType) : CommandElabM (Option Term) := do
  let nonErrMods := retTy.mods.filter (· != .fallible)
  if nonErrMods.back? == some .option then
    let innerParsed : ParsedSrvType := {
      retTy with mods := nonErrMods.extract 0 (nonErrMods.size - 1)
    }
    some <$> liftMacroM innerParsed.toPayloadTerm
  else
    return none

open Lean Elab Command in
private def filterNewWarnings (arr : Lean.PersistentArray Lean.Message) (priorSize : Nat) :
    Lean.PersistentArray Lean.Message :=
  let lst := arr.toList
  let before := lst.take priorSize
  let after := (lst.drop priorSize).filter (·.severity != .warning)
  (before ++ after).foldl (fun acc m => acc.push m) {}

open Lean Elab Command in
private def hasNewErrors (log : Lean.MessageLog) (priorRep priorUnrep : Nat) : Bool :=
  (log.reported.toList.drop priorRep).any (·.severity == .error) ||
  (log.unreported.toList.drop priorUnrep).any (·.severity == .error)

open Lean Elab Command in
private def elabServerStateCmds (priorRep priorUnrep : Nat) (stateId initStateId stateInvId invInitId : Ident)
    (stateDecls : Array ParsedStateDecl) (invs : Array ParsedInv)
    (stateFieldNames envVarNames : Array String) : CommandElabM Bool := do
  let mut stFieldIds : Array Ident := #[]
  let mut stFieldTys : Array Term := #[]
  let mut stInitVals : Array Term := #[]
  for sd in stateDecls do
    let fty ← liftMacroM sd.ty.toPayloadTerm
    let initCtx : LowerCtx := {
      fnName := "initState", stateFields := #[], envVars := #[], locals := #[]
      stateRule := .statelessServer, allowAwait := false, allowUnwrap := false
      hasFallible := false, isOption := false, innerOptTy? := none
    }
    let (initTerm, _) ← (lowerExpr initCtx .val sd.initStx).run {}
    stFieldIds := stFieldIds.push sd.ident
    stFieldTys := stFieldTys.push fty
    stInitVals := stInitVals.push (← `(srvAutoField($initTerm)))
  elabCommand (← `(command|
    structure $stateId where
      $[$stFieldIds:ident : $stFieldTys:term]*))
  elabCommand (← `(command|
    def $initStateId : $stateId := { $[$stFieldIds:ident := $stInitVals:term],* }))
  if hasNewErrors (← get).messages priorRep priorUnrep then return false

  let sParam := mkIdent `_s
  let sOldDummy := mkIdent `_sOld
  let mut singleProps : Array Term := #[]
  for inv in invs do
    if !inv.isTwoSt then
      let invCtx : LowerCtx := {
        fnName := "invariant", stateFields := stateFieldNames, envVars := envVarNames, locals := #[]
        stateRule := .invariantProp sParam sOldDummy false
        allowAwait := false, allowUnwrap := false
        hasFallible := false, isOption := false, innerOptTy? := none
      }
      let (pTerm, _) ← (lowerExpr invCtx .propInv inv.exprStx).run {}
      singleProps := singleProps.push pTerm
  let invBody ← match singleProps.toList with
    | []      => `(True)
    | p :: ps => ps.foldlM (init := p) fun acc q => `($acc ∧ $q)
  elabCommand (← `(command|
    def $stateInvId ($sParam:ident : $stateId) : Prop := $invBody))
  elabCommand (← `(command|
    theorem $invInitId : $stateInvId $initStateId := by
      qedSrvProveStep [$stateInvId, $initStateId] "initState" "initial state"))
  return !hasNewErrors (← get).messages priorRep priorUnrep

private structure ParsedServerBlock where
  envDecls   : Array ParsedEnvDecl
  stateDecls : Array ParsedStateDecl
  mutInvs    : Array ParsedMutInv
  invs       : Array ParsedInv
  fnClauses  : Array Lean.Syntax

open Lean Elab Command in
private def parseServerClauses (srvIdent : Ident) (srvName : Name) (clauses : Array Lean.Syntax) :
    CommandElabM ParsedServerBlock := do
  let mut envDecls   : Array ParsedEnvDecl := #[]
  let mut stateDecls : Array ParsedStateDecl := #[]
  let mut mutInvs    : Array ParsedMutInv := #[]
  let mut invs       : Array ParsedInv := #[]
  let mut fnClauses  : Array Syntax := #[]
  for c in clauses do
    let k := c.getKind
    if k == ``srvEnvClause then
      let id : Ident := ⟨c[1]⟩
      let osKey := (⟨c[3]⟩ : TSyntax `str).getString
      let def? := if c[4].getNumArgs == 2 then some ((⟨c[4][1]⟩ : TSyntax `str).getString) else none
      if envDecls.any (·.ident.getId == id.getId) then
        throwErrorAt id s!"duplicate `env {id.getId}` in `server {srvName}`"
      envDecls := envDecls.push { ref := c, ident := id, osKey, default? := def? }
    else if k == ``srvStateClause then
      let id : Ident := ⟨c[1]⟩
      let ty ← liftMacroM <| ParsedSrvType.parse c[3]
      liftMacroM <| ty.validate (allowFallible := false) s!"state field `{id.getId}`"
      if stateDecls.any (·.ident.getId == id.getId) || envDecls.any (·.ident.getId == id.getId) then
        throwErrorAt id s!"duplicate declaration `{id.getId}` in `server {srvName}`"
      let initStx : Syntax ←
        if c[4].getNumArgs == 2 then
          pure c[4][1]
        else if ty.mods.back? == some .array then
          pure (Syntax.node (.fromRef c) ``qedArrLit
            #[Syntax.atom (.fromRef c) "[", Syntax.node (.fromRef c) Lean.nullKind #[], Syntax.atom (.fromRef c) "]"])
        else if ty.mods.back? == some .option then
          pure (Syntax.node (.fromRef c) ``qedIdent #[mkIdentFrom c `none])
        else
          throwErrorAt id s!"state field `{id.getId}` requires an initial value `= ...`"
      stateDecls := stateDecls.push { ref := c, ident := id, ty, initStx }
    else if k == ``srvInvMutatingClause then
      let fid : Ident := ⟨c[2]⟩
      let cond := c[4]
      let lbl := s!"mutating {fid.getId} requires {(cond.reprint.getD "").trimAscii.toString}"
      mutInvs := mutInvs.push { ref := c, fieldId := fid, condStx := cond, label := lbl }
    else if k == ``srvInvClause then
      for e in c[1].getSepArgs do
        let lbl := (e.reprint.getD "invariant").trimAscii.toString
        invs := invs.push { ref := c, exprStx := e, isTwoSt := exprCallsOld e, label := lbl }
    else if k == ``srvFnClause then
      fnClauses := fnClauses.push c
    else
      throwErrorAt c "unexpected clause in `server` block"
  if fnClauses.isEmpty then
    throwErrorAt srvIdent s!"`server {srvName}` must declare at least one `def`"
  let hasState := !stateDecls.isEmpty
  if !hasState && (!invs.isEmpty || !mutInvs.isEmpty) then
    throwErrorAt srvIdent s!"`server {srvName}` declares `invariant`s but has no `state` fields"
  for mi in mutInvs do
    unless stateDecls.any (·.ident.getId == mi.fieldId.getId) do
      throwErrorAt mi.fieldId s!"`invariant mutating {mi.fieldId.getId}` does not match any `state` field of `{srvName}`"
  return { envDecls, stateDecls, mutInvs, invs, fnClauses }

section
open Lean Elab Command

private def buildPropConj (props : Array Term) : CommandElabM Term := do
  match props.toList with
  | []      => `(True)
  | p :: ps => ps.foldlM (init := p) fun acc q => `($acc ∧ $q)

private partial def splitSrvAnd (stx : Syntax) : Array Syntax :=
  let u := unwrapParens1 stx
  if u.getKind == ``qedAnd then splitSrvAnd u[0] ++ splitSrvAnd u[2]
  else #[u]

private partial def scanCtxEnv (envVars : Array String) (locals : Array String) (stx : Syntax) : Bool × Bool :=
  let k := stx.getKind
  if k == ``qedIdent then
    match stx[0].getId.components with
    | [] => (false, false)
    | root :: _ =>
        let r := root.toString
        if locals.contains r then (false, false)
        else if r == "ctx" then (true, false)
        else if envVars.contains r then (false, true)
        else (false, false)
  else if k == ``qedProj then
    scanCtxEnv envVars locals stx[0]
  else if k == ``qedLam1 then
    let b := if stx[0].isIdent then #[stx[0].getId.toString] else #[]
    scanCtxEnv envVars (locals ++ b) stx[2]
  else if k == ``qedLamN then
    let ps := stx[1].getSepArgs.filterMap fun b => if b.isIdent then some b.getId.toString else none
    scanCtxEnv envVars (locals ++ ps) stx[4]
  else if k == ``qedAllIn || k == ``qedAnyIn then
    let (c1, e1) := scanCtxEnv envVars locals stx[3]
    let (c2, e2) := scanCtxEnv envVars (locals.push stx[1].getId.toString) stx[5]
    (c1 || c2, e1 || e2)
  else if k == ``qedAllVars then
    let ps := stx[1].getSepArgs.map (·.getId.toString)
    scanCtxEnv envVars (locals ++ ps) stx[3]
  else
    stx.getArgs.foldl (fun (ac, ae) ch =>
      let (c, e) := scanCtxEnv envVars locals ch
      (ac || c, ae || e)) (false, false)

private def isAuthReqExpr (stx : Syntax) : Bool :=
  let s := stx.reprint.getD ""
  s.contains "ctx.userId" || s.contains "ctx.isAuthenticated" || s.contains "ctx.bearerToken"

private partial def scanFailCallsAux (stx : Syntax) (tags : Array Ident) (hasPlain : Bool) :
    CommandElabM (Array Ident × Bool) := do
  if stx.getKind == ``qedCall && stx[0].getKind == ``qedIdent && stx[0][0].getId == `fail then
    let rawArgs := stx[2].getSepArgs
    if (rawArgs.size == 1 || rawArgs.size == 2) && (unwrapParens1 rawArgs[0]![0]).getKind == ``qedDotIdent then
      let tagId : Ident := ⟨(unwrapParens1 rawArgs[0]![0])[1]⟩
      let tags' := if tags.any (·.getId == tagId.getId) then tags else tags.push tagId
      if rawArgs.size == 2 then
        scanFailCallsAux rawArgs[1]! tags' hasPlain
      else
        return (tags', hasPlain)
    else
      let mut curTags := tags
      let mut curPlain := true
      for arg in rawArgs do
        let (t', p') ← scanFailCallsAux arg curTags curPlain
        curTags := t'; curPlain := p'
      return (curTags, curPlain)
  else
    let mut curTags := tags
    let mut curPlain := hasPlain
    for ch in stx.getArgs do
      let (t', p') ← scanFailCallsAux ch curTags curPlain
      curTags := t'; curPlain := p'
    return (curTags, curPlain)

private def scanBodyFailTags (stmts : Array Syntax) : CommandElabM (Array Ident × Bool) := do
  let mut tags : Array Ident := #[]
  let mut hasPlain := false
  for st in stmts do
    let (t', p') ← scanFailCallsAux st tags hasPlain
    tags := t'; hasPlain := p'
  return (tags, hasPlain)

private def elabDomainErrorType (srvName : Name) (fnIdent : Ident) (tagIdents : Array Ident) :
    CommandElabM Ident := do
  let errTypeId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId ++ `Error)
  let mkDotTerm (tid : Ident) : Term :=
    ⟨Syntax.node (.fromRef tid) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef tid) ".", tid]⟩
  let ctors ← tagIdents.mapM fun tid =>
    `(Lean.Parser.Command.ctor| | $tid:ident)
  elabCommand (← `(command|
    inductive $errTypeId where
      $[$ctors:ctor]*
    deriving Inhabited, DecidableEq, Repr))
  let toStrAlts ← tagIdents.mapM fun tid => do
    let tLit := Syntax.mkStrLit tid.getId.toString
    `(Lean.Parser.Term.matchAltExpr| | $(mkDotTerm tid) => $tLit)
  let fromJsonAlts ← tagIdents.mapM fun tid => do
    let tLit := Syntax.mkStrLit tid.getId.toString
    `(Lean.Parser.Term.matchAltExpr| | Qed.Json.str $tLit => Except.ok $(mkDotTerm tid))
  let fromJsonFail ← `(Lean.Parser.Term.matchAltExpr| | _ => Except.error "invalid RPC error tag")
  let fromJsonAltsAll := fromJsonAlts.push fromJsonFail
  let toProtoAlts ← tagIdents.zipIdx.mapM fun (tid, i) => do
    let iLit := Syntax.mkNumLit (toString i)
    `(Lean.Parser.Term.matchAltExpr| | $(mkDotTerm tid) => Qed.Proto.WireVal.varint $iLit)
  let fromProtoAlts ← tagIdents.zipIdx.mapM fun (tid, i) => do
    let iLit := Syntax.mkNumLit (toString i)
    `(Lean.Parser.Term.matchAltExpr| | Qed.Proto.WireVal.varint $iLit => Except.ok $(mkDotTerm tid))
  let fromProtoFail ← `(Lean.Parser.Term.matchAltExpr| | _ => Except.error "protobuf: invalid RPC error tag")
  let fromProtoAltsAll := fromProtoAlts.push fromProtoFail
  elabCommand (← `(command| instance : ToString $errTypeId where toString e := match e with $[$toStrAlts:matchAlt]*))
  elabCommand (← `(command| instance : Qed.ToJson $errTypeId := ⟨fun e => Qed.Json.str (toString e)⟩))
  elabCommand (← `(command| instance : Qed.FromJson $errTypeId where fromJson j := match j with $[$fromJsonAltsAll:matchAlt]*))
  elabCommand (← `(command|
    instance : Qed.LawfulJson $errTypeId where
      depthBound := 0
      depth_toJson _ := Nat.le_refl 0
      fromJson_toJson e := by cases e <;> rfl))
  elabCommand (← `(command| instance : Qed.NonNullJson $errTypeId := ⟨nofun⟩))
  elabCommand (← `(command| instance : Qed.ToProto $errTypeId where toProtoVal e := match e with $[$toProtoAlts:matchAlt]*))
  elabCommand (← `(command| instance : Qed.FromProto $errTypeId where fromProtoVal w := match w with $[$fromProtoAltsAll:matchAlt]*))
  elabCommand (← `(command| instance : Qed.LawfulProto $errTypeId := Qed.LawfulProto.ofScalar (by intro e; cases e <;> rfl)))
  return errTypeId

end

open Lean Elab Command in
private def elabServerDispatchCmds (srvIdent stateId initStateId stateInvId invInitId : Ident)
    (srvName fullSrvName : Name) (srvShort : String) (hasState : Bool)
    (envDecls : Array ParsedEnvDecl) (allExtRoots : Array Name)
    (methodInfos : Array ServerMethodInfo) (dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (ctxId reqBytesId : Ident) : CommandElabM Unit := do
  let srvNm := srvName
  if hasState then
    let linThmId := mkIdentFrom srvIdent (srvNm ++ `concurrent_linearizable)
    elabCommand (← `(command|
      theorem $linThmId {Out : Type}
          (st : Qed.Server.MultiCoreState $stateId Out)
          (hsched : Qed.Server.MultiCoreSchedule $stateInvId ⟨$initStateId, []⟩ st) :
          $stateInvId st.shared :=
        Qed.Server.concurrent_schedule_preserves_inv $stateInvId $initStateId st $invInitId hsched))

  let extMap := externalRegistry.getState (← getEnv)
  let mut reqSecrets : Array String := #[]
  for ed in envDecls do
    if ed.default?.isNone && !reqSecrets.contains ed.osKey then
      reqSecrets := reqSecrets.push ed.osKey
  let mut usedExts : Array (String × String) := #[]
  let currNs ← getCurrNamespace
  for root in allExtRoots do
    let cand1 := currNs ++ root
    let info? := (extMap.find? cand1).orElse fun _ => extMap.find? root
    if let some extInfo := info? then
      let sStr := root.toString
      unless usedExts.any (·.1 == sStr) do
        usedExts := usedExts.push (sStr, extInfo.baseOrigin)
      for sec in extInfo.secrets do
        unless reqSecrets.contains sec do
          reqSecrets := reqSecrets.push sec

  let secretsId := mkIdentFrom srvIdent (srvNm ++ `secrets)
  let secLits : Array Term := reqSecrets.map (Syntax.mkStrLit ·)
  elabCommand (← `(command| def $secretsId : Array String := #[$[$secLits],*]))

  let readOnlyId := mkIdentFrom srvIdent (srvNm ++ `readOnlyMethods)
  let roLits : Array Term := (methodInfos.filter (·.isReadOnly)).map (Syntax.mkStrLit ·.name)
  elabCommand (← `(command| def $readOnlyId : Array String := #[$[$roLits],*]))

  let methodsId := mkIdentFrom srvIdent (srvNm ++ `methods)
  let mLits : Array Term := methodInfos.map (Syntax.mkStrLit ·.name)
  elabCommand (← `(command| def $methodsId : List String := [$[$mLits],*]))

  let methodVar := mkIdent `method
  let notFoundArm ← `(Lean.Parser.Term.matchAltExpr|
    | _ => Pure.pure (Except.error (Qed.Server.ApiError.notFound ("unknown RPC method: " ++ $methodVar))))
  let allArms := dispatchArms.push notFoundArm
  let matchMethodTerm ← `(match $methodVar:ident with $[$allArms:matchAlt]*)
  let fullDispatchBody ← envDecls.foldrM (init := matchMethodTerm) fun ed acc => do
    let eid := ed.ident
    let keyLit := Syntax.mkStrLit ed.osKey
    match ed.default? with
    | some defVal =>
        let defLit := Syntax.mkStrLit defVal
        `(Qed.Server.MonadServer.readEnv $keyLit >>= fun _envOpt =>
            let $eid:ident : String := _envOpt.getD $defLit
            $acc)
    | none =>
        let missingMsg := Syntax.mkStrLit s!"missing required environment variable `{ed.osKey}`"
        `(Qed.Server.MonadServer.readEnv $keyLit >>= fun _envOpt =>
            match _envOpt with
            | some $eid:ident => $acc
            | none => Pure.pure (Except.error (Qed.Server.ApiError.internal $missingMsg)))

  let dispatchId := mkIdentFrom srvIdent (srvNm ++ `dispatchM)
  if hasState then
    elabCommand (← `(command|
      def $dispatchId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m]
          [Qed.Server.MonadAtomic $stateId m]
          ($ctxId:ident : Qed.Server.RequestCtx) ($methodVar:ident : String) ($reqBytesId:ident : ByteArray) :
          m (Except Qed.Server.ApiError ByteArray) :=
        $fullDispatchBody))
  else
    elabCommand (← `(command|
      def $dispatchId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m]
          ($ctxId:ident : Qed.Server.RequestCtx) ($methodVar:ident : String) ($reqBytesId:ident : ByteArray) :
          m (Except Qed.Server.ApiError ByteArray) :=
        $fullDispatchBody))

  modifyEnv fun env => serverRegistry.addEntry env {
    serverName := fullSrvName
    shortName := srvShort
    hasState
    secrets := reqSecrets
    envVars := envDecls.map fun e => (e.ident.getId.toString, e.osKey, e.default?)
    externalServices := usedExts
    methods := methodInfos
  }

open Lean Elab Command in
private def elabServerFnInvariants (priorRep priorUnrep : Nat) (isAsync : Bool)
    (srvName : Name) (fnStr : String) (fnIdent stateId stateInvId targetId : Ident)
    (allBinderIds : Array Ident) (allBinderTys : Array Term) (targetCall : Term)
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (stateFieldNames envVarNames : Array String) : CommandElabM Bool := do
  let fnLit := Syntax.mkStrLit fnStr
  let sOldId := mkIdent (if isAsync then `_sOld else `_s0)
  let sNewId := mkIdent `_sNew
  let emitTwoInv (twoIdx : Nat) (inv : ParsedInv) : CommandElabM Bool := do
    let twoCtx : LowerCtx := {
      fnName := "invariant", stateFields := stateFieldNames, envVars := envVarNames, locals := #[]
      stateRule := .invariantProp sNewId sOldId false
      allowAwait := false, allowUnwrap := false, hasFallible := false, isOption := false, innerOptTy? := none
    }
    let relProp := (← (lowerExpr twoCtx .propInv inv.exprStx).run {}).1
    let twoThmId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter s!"_twoInv{twoIdx}")
    let twoLbl := Syntax.mkStrLit inv.label
    if isAsync then
      elabCommand (← `(command|
        theorem $twoThmId $[($allBinderIds:ident : $allBinderTys:term)]* :
            Qed.Server.ProgPreservesStepRel $stateInvId
              (fun ($sOldId:ident $sNewId:ident : $stateId) => $relProp)
              ($targetCall : Qed.Server.ThreadProg $stateId _) := by
          qedSrvProveAsync $targetId [$stateInvId] $fnLit $twoLbl))
    else
      elabCommand (← `(command|
        theorem $twoThmId ($sOldId:ident : $stateId) $[($allBinderIds:ident : $allBinderTys:term)]*
            (_hInv : $stateInvId $sOldId) :
            Qed.Server.srvWithNewState (($targetCall).1) (fun ($sNewId:ident : $stateId) => $relProp) := by
          qedSrvProveStep [$stateInvId, $targetId] $fnLit $twoLbl))
    return !hasNewErrors (← get).messages priorRep priorUnrep

  let emitMutInv (mutIdx : Nat) (mi : ParsedMutInv) : CommandElabM Bool := do
    let miCtx : LowerCtx := {
      fnName := fnStr, stateFields := #[], envVars := envVarNames, locals := #[]
      stateRule := .statelessServer, allowAwait := false, allowUnwrap := false
      hasFallible := false, isOption := false, innerOptTy? := none
    }
    let miProp := (← (lowerExpr miCtx .propInv mi.condStx).run {}).1
    let fldId := mi.fieldId
    let miThmId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter s!"_mutInv{mutIdx}")
    let miLbl := Syntax.mkStrLit mi.label
    if isAsync then
      elabCommand (← `(command|
        theorem $miThmId $[($allBinderIds:ident : $allBinderTys:term)]* :
            Qed.Server.ProgPreservesStepRel $stateInvId
              (fun ($sOldId:ident $sNewId:ident : $stateId) => ($sNewId).$fldId:ident = ($sOldId).$fldId:ident ∨ $miProp)
              ($targetCall : Qed.Server.ThreadProg $stateId _) := by
          qedSrvProveAsync $targetId [$stateInvId] $fnLit $miLbl))
    else
      elabCommand (← `(command|
        theorem $miThmId ($sOldId:ident : $stateId) $[($allBinderIds:ident : $allBinderTys:term)]*
            (_hInv : $stateInvId $sOldId) :
            (($targetCall).1).$fldId:ident = ($sOldId).$fldId:ident ∨ $miProp := by
          qedSrvProveStep [$stateInvId, $targetId] $fnLit $miLbl))
    return !hasNewErrors (← get).messages priorRep priorUnrep

  let mut twoIdx := 0
  for inv in invs do
    if inv.isTwoSt then
      unless (← emitTwoInv twoIdx inv) do return false
      twoIdx := twoIdx + 1
  for (mi, mutIdx) in mutInvs.zipIdx do
    unless (← emitMutInv mutIdx mi) do return false
  return true

open Lean Elab Command in
private structure FnEnsSpec where
  ensId    : Ident
  postFn   : Term → CommandElabM Term
  labelStr : String

open Lean Elab Command in
private def elabServerPureFn (priorRep priorUnrep : Nat)
    (srvName : Name) (fnStr : String) (fnIdent stateId stateInvId : Ident)
    (allBinderIds : Array Ident) (allBinderTys : Array Term) (callArgs : Array Term)
    (payloadTerm errTyTerm : Term) (baseCtx : LowerCtx) (bodyStmts : Array Lean.Syntax)
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (stateFieldNames envVarNames : Array String)
    (ensSpec? : Option FnEnsSpec) :
    CommandElabM (Option (Term × Bool × Array Name)) := do
  let s0Id := mkIdent `_s0
  let fnLit := Syntax.mkStrLit fnStr
  let (pureBody, lSt) ← (lowerPureBlock baseCtx (inAtomic := false) s0Id s0Id bodyStmts).run {}
  let isReadOnly := lSt.mutated.isEmpty
  let stepId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_step")
  elabCommand (← `(command|
    def $stepId ($s0Id:ident : $stateId) $[($allBinderIds:ident : $allBinderTys:term)]* :
        $stateId × Except $errTyTerm $payloadTerm :=
      Qed.Server.srvFinish $s0Id $pureBody))
  if hasNewErrors (← get).messages priorRep priorUnrep then return none

  let stepCall ← allBinderIds.foldlM (init := ← `($stepId $s0Id)) fun acc id => `($acc $id)
  if isReadOnly then
    let roThmId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_readOnly")
    let roLbl := Syntax.mkStrLit s!"{fnStr} read-only state preservation"
    elabCommand (← `(command|
      theorem $roThmId ($s0Id:ident : $stateId) $[($allBinderIds:ident : $allBinderTys:term)]* :
          ($stepCall).1 = $s0Id := by
        qedSrvProveStep [$stepId] $fnLit $roLbl))
    if hasNewErrors (← get).messages priorRep priorUnrep then return none
  else
    let invThmId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_inv")
    elabCommand (← `(command|
      theorem $invThmId ($s0Id:ident : $stateId) $[($allBinderIds:ident : $allBinderTys:term)]*
          (_hInv : $stateInvId $s0Id) :
          $stateInvId ($stepCall).1 := by
        qedSrvProveStep [$stateInvId, $stepId] $fnLit "StateInv"))
    if hasNewErrors (← get).messages priorRep priorUnrep then return none
    unless (← elabServerFnInvariants priorRep priorUnrep false srvName fnStr fnIdent stateId stateInvId
        stepId allBinderIds allBinderTys stepCall invs mutInvs stateFieldNames envVarNames) do
      return none

  if let some ensSpec := ensSpec? then
    let ensId := ensSpec.ensId
    let ensThmId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_ensures")
    let postGoal ← ensSpec.postFn (← `(($stepCall).2))
    let ensLbl := Syntax.mkStrLit s!"ensures: {ensSpec.labelStr}"
    elabCommand (← `(command|
      theorem $ensThmId ($s0Id:ident : $stateId) $[($allBinderIds:ident : $allBinderTys:term)]*
          (_hInv : $stateInvId $s0Id) :
          $postGoal := by
        qedSrvProveStep [$stateInvId, $stepId, $ensId] $fnLit $ensLbl))
    if hasNewErrors (← get).messages priorRep priorUnrep then return none

  let snapCall ← callArgs.foldlM (init := ← `($stepId _sSnap)) fun acc a => `($acc $a)
  let runExpr ← if isReadOnly then
    `(Qed.Server.MonadAtomic.runAtomicRead (fun (_sSnap : $stateId) => ($snapCall).2))
  else
    `(Qed.Server.MonadAtomic.runAtomic (fun (_sSnap : $stateId) => $snapCall))
  return some (runExpr, isReadOnly, lSt.extRoots)

open Lean Elab Command in
private def elabAsyncEnsuresThm (priorRep priorUnrep : Nat)
    (srvName : Name) (fnStr : String) (fnIdent handlerId : Ident)
    (stateInvTerm stateTyTerm payloadTerm errTyTerm : Term)
    (allBinderIds : Array Ident) (allBinderTys : Array Term)
    (hCall : Term) (extraUnfoldIds : Array Ident) (ensSpec : FnEnsSpec) :
    CommandElabM Bool := do
  let ensThmId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_ensures")
  let outVar := mkIdent `_srvOut
  let postBody ← ensSpec.postFn ⟨outVar.raw⟩
  let ensLbl := Syntax.mkStrLit s!"ensures: {ensSpec.labelStr}"
  let fnLit := Syntax.mkStrLit fnStr
  let unfoldIds := extraUnfoldIds.push ensSpec.ensId
  elabCommand (← `(command|
    theorem $ensThmId $[($allBinderIds:ident : $allBinderTys:term)]* :
        Qed.Server.ProgEnsures $stateInvTerm
          (fun ($outVar:ident : Except $errTyTerm $payloadTerm) => $postBody)
          ($hCall : Qed.Server.ThreadProg $stateTyTerm _) := by
      qedSrvProveAsyncEnsures $handlerId [$[$unfoldIds],*] $fnLit $ensLbl))
  return !hasNewErrors (← get).messages priorRep priorUnrep

open Lean Elab Command in
private def elabServerAsyncFn (priorRep priorUnrep : Nat)
    (srvName : Name) (fnStr : String) (fnIdent stateId stateInvId : Ident)
    (allBinderIds : Array Ident) (allBinderTys : Array Term) (callArgs : Array Term)
    (payloadTerm errTyTerm : Term) (baseCtx : LowerCtx) (bodyStmts : Array Lean.Syntax)
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (stateFieldNames envVarNames : Array String)
    (ensSpec? : Option FnEnsSpec) :
    CommandElabM (Option (Term × Bool × Array Name)) := do
  let stateTyTerm : Term := ⟨stateId.raw⟩
  let fnLit := Syntax.mkStrLit fnStr
  let (asyncBody, lSt) ← (lowerAsyncBlock baseCtx (some stateTyTerm) bodyStmts).run {}
  let isReadOnly := lSt.mutated.isEmpty
  let handlerId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_handler")
  elabCommand (← `(command|
    def $handlerId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m]
        [Qed.Server.MonadAtomic $stateId m]
        $[($allBinderIds:ident : $allBinderTys:term)]* :
        m (Except $errTyTerm $payloadTerm) :=
      Qed.Server.srvFinishM $asyncBody))
  if hasNewErrors (← get).messages priorRep priorUnrep then return none

  let hCall ← allBinderIds.foldlM (init := ← `($handlerId)) fun acc id => `($acc $id)
  let asyncInvId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_inv")
  elabCommand (← `(command|
    theorem $asyncInvId $[($allBinderIds:ident : $allBinderTys:term)]* :
        Qed.Server.ProgPreservesInv $stateInvId
          ($hCall : Qed.Server.ThreadProg $stateId _) := by
      qedSrvProveAsync $handlerId [$stateInvId] $fnLit "StateInv"))
  if hasNewErrors (← get).messages priorRep priorUnrep then return none
  unless (← elabServerFnInvariants priorRep priorUnrep true srvName fnStr fnIdent stateId stateInvId
      handlerId allBinderIds allBinderTys hCall invs mutInvs stateFieldNames envVarNames) do
    return none

  if let some ensSpec := ensSpec? then
    unless (← elabAsyncEnsuresThm priorRep priorUnrep srvName fnStr fnIdent handlerId
        stateInvId stateId payloadTerm errTyTerm allBinderIds allBinderTys hCall #[stateInvId] ensSpec) do
      return none

  let hApp ← callArgs.foldlM (init := ← `($handlerId)) fun acc a => `($acc $a)
  return some (hApp, isReadOnly, lSt.extRoots)

open Lean Elab Command in
private def elabServerCmdCore (priorRep priorUnrep : Nat) : CommandElab := fun stx => do
  let srvIdent : Ident := ⟨stx[1]⟩
  let srvName := srvIdent.getId
  let srvShort := srvName.toString
  let currNs ← getCurrNamespace
  let fullSrvName := currNs ++ srvName
  let parsed ← parseServerClauses srvIdent srvName stx[3].getArgs
  let envDecls := parsed.envDecls
  let stateDecls := parsed.stateDecls
  let mutInvs := parsed.mutInvs
  let invs := parsed.invs
  let fnClauses := parsed.fnClauses

  let hasState := !stateDecls.isEmpty
  let stateFieldNames := stateDecls.map (·.ident.getId.toString)
  let envVarNames := envDecls.map (·.ident.getId.toString)
  let envIdents := envDecls.map (·.ident)
  let envStrType ← `(String)
  let envTypes := envDecls.map fun _ => envStrType

  -- 1. Emit `<S>.State`, `<S>.initState`, `<S>.StateInv`, and `<S>.inv_init` if stateful
  let stateId := mkIdentFrom srvIdent (srvName ++ `State)
  let initStateId := mkIdentFrom srvIdent (srvName ++ `initState)
  let stateInvId := mkIdentFrom srvIdent (srvName ++ `StateInv)
  let invInitId := mkIdentFrom srvIdent (srvName ++ `inv_init)

  if hasState then
    unless (← elabServerStateCmds priorRep priorUnrep stateId initStateId stateInvId invInitId
        stateDecls invs stateFieldNames envVarNames) do
      return

  -- 2. Elaborate each `fn`: step/handler + invariants + ensures + client RPC stub + dispatcher arm
  let mut methodInfos : Array ServerMethodInfo := #[]
  let mut allExtRoots : Array Name := #[]
  let mut dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]
  let ctxId := mkIdent `ctx
  let reqBytesId := mkIdent `reqBytes

  for fc in fnClauses do
    let fnIdent : Ident := ⟨fc[1]⟩
    let fnStr := fnIdent.getId.toString
    if methodInfos.any (·.name == fnStr) then
      throwErrorAt fnIdent s!"duplicate function `{fnStr}` in `server {srvName}`"

    let contractLines := fc[8].getArgs
    let mut reqExprs : Array Syntax := #[]
    let mut ensExprs : Array Syntax := #[]
    for cl in contractLines do
      if cl.getKind == ``srvRequiresLine then reqExprs := reqExprs ++ cl[1].getSepArgs
      else if cl.getKind == ``srvEnsuresLine then ensExprs := ensExprs ++ cl[1].getSepArgs
      else throwErrorAt cl "unexpected contract clause in `def`"

    let rawParams := fc[3].getSepArgs
    let mut fnParams : Array ParsedFnParam := #[]
    let mut paramNames : Array String := #[]
    for rp in rawParams do
      let pid : Ident := ⟨rp[0]⟩
      let pstr := pid.getId.toString
      if pstr == "ctx" then
        throwErrorAt pid "`ctx` is already implicitly available as `RequestCtx` in every server function"
      if !ensExprs.isEmpty && pstr == "result" then
        throwErrorAt pid "`result` is reserved inside `ensures` postconditions; rename this parameter"
      if paramNames.contains pstr || envVarNames.contains pstr || stateFieldNames.contains pstr then
        throwErrorAt pid s!"parameter `{pstr}` shadows an existing parameter, `env`, or `state` binding"
      let pty ← liftMacroM <| ParsedSrvType.parse rp[2]
      liftMacroM <| pty.validate (allowFallible := false) s!"parameter `{pstr}`"
      let ptyTerm ← liftMacroM pty.toPayloadTerm
      paramNames := paramNames.push pstr
      fnParams := fnParams.push { ident := pid, ty := pty, tyTerm := ptyTerm }

    let retTy ← liftMacroM <| ParsedSrvType.parse fc[6]
    liftMacroM <| retTy.validate (allowFallible := true) s!"return type of `{fnStr}`"
    let payloadTerm ← liftMacroM retTy.toPayloadTerm
    let innerOpt? ← computeInnerOptTerm? retTy
    let isUnitPayload := (retTy.mods.filter (· != .fallible)).isEmpty && retTy.baseIdent.getId == `Unit

    let bodyStmts := fc[9].getArgs
    if !isUnitPayload && !blockAlwaysReturns bodyStmts then
      throwErrorAt fnIdent s!"missing `return` on fallthrough path of `{fnStr}`"

    -- Scan `fail(.tag)` calls & emit `<S>.<fn>.Error` if typed domain errors are used
    let (domainTagIdents, hasPlainFail) ← scanBodyFailTags bodyStmts
    if !domainTagIdents.isEmpty && hasPlainFail then
      throwErrorAt fnIdent s!"cannot mix typed `fail(.tag)` and untyped `fail(\"...\")` inside `{fnStr}`; use `fail(.tag, msg)` for all domain failures"
    if !domainTagIdents.isEmpty && !retTy.hasFallible then
      throwErrorAt fnIdent s!"`fail(.tag)` can only be returned from a fallible `T!` function (`{fnStr}` is not declared `-> ...!`)"

    let errTypeId? : Option Ident ←
      if domainTagIdents.isEmpty then pure none
      else some <$> elabDomainErrorType srvName fnIdent domainTagIdents
    if hasNewErrors (← get).messages priorRep priorUnrep then return

    let domainErrTyTerm? : Option Term := errTypeId?.map (⟨·.raw⟩)
    let errTyTerm : Term ← match domainErrTyTerm? with
      | some et => `(Qed.Server.SrvFailure $et)
      | none    => `(Qed.Server.ApiError)

    let pIdents := fnParams.map (·.ident)
    let pTyTerms := fnParams.map (·.tyTerm)

    -- Lower `requires` preconditions (parameters + `env` + `ctx` only — never `state`!)
    -- Also extract client-side parameter preconditions & auth requirements.
    let mut reqPropTerms : Array Term := #[]
    let mut reqHypIds    : Array Ident := #[]
    let mut reqHypTys    : Array Term := #[]
    let mut reqLabels    : Array String := #[]
    let mut clientReqProps : Array Term := #[]
    let mut clientReqLabels : Array String := #[]
    let mut requiresAuth : Bool := false
    for idx in [0:reqExprs.size] do
      let rExpr := reqExprs[idx]!
      if exprHasAwait rExpr then
        throwErrorAt rExpr "`requires` precondition cannot contain `await`"
      let reqCtx : LowerCtx := {
        fnName := fnStr, stateFields := stateFieldNames, envVars := envVarNames, locals := paramNames
        stateRule := .forbidInRequires, allowAwait := false, allowUnwrap := false
        hasFallible := false, isOption := false, innerOptTy? := none
      }
      let (pTerm, rSt) ← (lowerExpr reqCtx .propGuard rExpr).run {}
      allExtRoots := allExtRoots ++ rSt.extRoots.filter (!allExtRoots.contains ·)
      let hId := mkIdent (Name.mkSimple s!"_hReq{idx}")
      reqPropTerms := reqPropTerms.push pTerm
      reqHypIds := reqHypIds.push hId
      reqHypTys := reqHypTys.push pTerm
      reqLabels := reqLabels.push ((rExpr.reprint.getD "requires").trimAscii.toString)

      for conj in splitSrvAnd rExpr do
        let (mentionsCtx, mentionsEnv) := scanCtxEnv envVarNames paramNames conj
        if mentionsCtx && !mentionsEnv && isAuthReqExpr conj then
          requiresAuth := true
        else if !mentionsCtx && !mentionsEnv then
          let cliReqCtx : LowerCtx := {
            fnName := fnStr, stateFields := stateFieldNames, envVars := #[], locals := paramNames
            stateRule := .forbidInRequires, allowAwait := false, allowUnwrap := false
            hasFallible := false, isOption := false, innerOptTy? := none, forbidCtxEnv := true
          }
          let (pTerm, _) ← (lowerExpr cliReqCtx .propInv conj).run {}
          clientReqProps := clientReqProps.push pTerm
          clientReqLabels := clientReqLabels.push ((conj.reprint.getD "requires").trimAscii.toString)

    let clientReqId? : Option Ident ←
      if clientReqProps.isEmpty then pure none
      else
        let cid := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_req")
        let reqConj ← buildPropConj clientReqProps
        elabCommand (← `(command|
          set_option linter.unusedVariables false in
          @[simp] abbrev $cid $[($pIdents:ident : $pTyTerms:term)]* : Prop := $reqConj))
        pure (some cid)

    -- Lower `ensures` postconditions (parameters + `result` only — never `state`, `ctx`, or `env`!)
    let mut ensProps : Array Term := #[]
    let mut ensLabels : Array String := #[]
    for eExpr in ensExprs do
      if exprHasAwait eExpr then
        throwErrorAt eExpr "`ensures` postcondition cannot contain `await`"
      let ensCtx : LowerCtx := {
        fnName := fnStr, stateFields := stateFieldNames, envVars := envVarNames,
        locals := paramNames.push "result", stateRule := .forbidInEnsures,
        allowAwait := false, allowUnwrap := false, hasFallible := false,
        isOption := false, innerOptTy? := none, forbidCtxEnv := true
      }
      let (pTerm, _) ← (lowerExpr ensCtx .propInv eExpr).run {}
      ensProps := ensProps.push pTerm
      ensLabels := ensLabels.push ((eExpr.reprint.getD "ensures").trimAscii.toString)

    let ensSpec? : Option FnEnsSpec ←
      if ensProps.isEmpty then pure none
      else
        let ensId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_ens")
        let resTyTerm := innerOpt?.getD payloadTerm
        let resIdent := mkIdent `result
        let ensConj ← buildPropConj ensProps
        elabCommand (← `(command|
          set_option linter.unusedVariables false in
          @[simp] abbrev $ensId $[($pIdents:ident : $pTyTerms:term)]* ($resIdent:ident : $resTyTerm) : Prop :=
            $ensConj))
        if hasNewErrors (← get).messages priorRep priorUnrep then return
        let postFn : Term → CommandElabM Term := fun outTerm => do
          let ensApp ← pIdents.foldlM (init := ← `($ensId)) fun acc p => `($acc $p)
          if innerOpt?.isSome then
            `(Qed.Server.srvEnsPostOpt ($ensApp) $outTerm)
          else
            `(Qed.Server.srvEnsPost ($ensApp) $outTerm)
        pure (some { ensId, postFn, labelStr := String.intercalate " && " ensLabels.toList })

    let hasAwait := blockHasAwait bodyStmts
    let allowUnwrap := retTy.hasFallible || innerOpt?.isSome
    let baseCtx : LowerCtx := {
      fnName := fnStr
      stateFields := stateFieldNames
      envVars := envVarNames
      locals := paramNames
      stateRule := if hasState then .pureStep (mkIdent `_s0) else .statelessServer
      allowAwait := hasAwait
      allowUnwrap := allowUnwrap
      hasFallible := retTy.hasFallible
      isOption := innerOpt?.isSome
      innerOptTy? := innerOpt?
      domainErrTy? := domainErrTyTerm?
    }

    let allBinderIds := envIdents ++ #[ctxId] ++ pIdents ++ reqHypIds
    let ctxTyTerm ← `(Qed.Server.RequestCtx)
    let allBinderTys := envTypes ++ #[ctxTyTerm] ++ pTyTerms ++ reqHypTys

    let mut isReadOnly := true
    let reqTupleTy ← buildTupleType pTyTerms
    let reqVar := mkIdent `_reqVal
    let projs ← extractTupleProjections reqVar pTyTerms.size
    let callArgs : Array Term := envIdents.map (⟨·.raw⟩) ++ #[⟨ctxId.raw⟩] ++ projs ++ reqHypIds.map (⟨·.raw⟩)
    let fnLit := Syntax.mkStrLit fnStr

    let mkDispatchArm (runExpr : Term) : CommandElabM (TSyntax ``Lean.Parser.Term.matchAltExpr) := do
      let initGuarded ←
        if domainErrTyTerm?.isSome then
          `($runExpr >>= fun _fnRes => Pure.pure ((Qed.Server.SrvFailure.toWire _fnRes).map Qed.Proto.encode))
        else
          `($runExpr >>= fun _fnRes => Pure.pure (_fnRes.map Qed.Proto.encode))
      let mut guardedRun := initGuarded
      for revIdx in [0:reqPropTerms.size] do
        let ri := reqPropTerms.size - 1 - revIdx
        let rCond := reqPropTerms[ri]!
        let rHyp := reqHypIds[ri]!
        let rLbl := reqLabels[ri]!
        let rMsg := Syntax.mkStrLit s!"precondition failed: {rLbl}"
        let errCtor : Term ←
          if rLbl.contains "ctx.userId" || rLbl.contains "ctx.bearerToken" || rLbl.contains "ctx.isAuthenticated" then
            `(Qed.Server.ApiError.unauthorized $rMsg)
          else
            `(Qed.Server.ApiError.badRequest $rMsg)
        guardedRun ← `(if $rHyp:ident : $rCond then $guardedRun else Pure.pure (Except.error $errCtor))
      let bindProjBody ← (pIdents.zip projs).foldrM (init := guardedRun) fun (pid, prj) acc =>
        `(let $pid:ident := $prj; $acc)
      `(Lean.Parser.Term.matchAltExpr|
        | $fnLit =>
            match Qed.Proto.decode (α := $reqTupleTy) $reqBytesId with
            | Except.error _decErr => Pure.pure (Except.error (Qed.Server.ApiError.badRequest _decErr))
            | Except.ok $reqVar:ident => $bindProjBody)

    if hasState && !hasAwait then
      let some (runExpr, ro, extRoots) ← elabServerPureFn priorRep priorUnrep
          srvName fnStr fnIdent stateId stateInvId
          allBinderIds allBinderTys callArgs payloadTerm errTyTerm baseCtx bodyStmts
          invs mutInvs stateFieldNames envVarNames ensSpec? | return
      isReadOnly := ro
      allExtRoots := allExtRoots ++ extRoots.filter (!allExtRoots.contains ·)
      dispatchArms := dispatchArms.push (← mkDispatchArm runExpr)

    else if hasState && hasAwait then
      let some (hApp, ro, extRoots) ← elabServerAsyncFn priorRep priorUnrep
          srvName fnStr fnIdent stateId stateInvId
          allBinderIds allBinderTys callArgs payloadTerm errTyTerm baseCtx bodyStmts
          invs mutInvs stateFieldNames envVarNames ensSpec? | return
      isReadOnly := ro
      allExtRoots := allExtRoots ++ extRoots.filter (!allExtRoots.contains ·)
      dispatchArms := dispatchArms.push (← mkDispatchArm hApp)

    else
      let (statelessBody, lSt) ← (lowerAsyncBlock baseCtx none bodyStmts).run {}
      allExtRoots := allExtRoots ++ lSt.extRoots.filter (!allExtRoots.contains ·)
      let handlerId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_handler")
      elabCommand (← `(command|
        def $handlerId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m]
            $[($allBinderIds:ident : $allBinderTys:term)]* :
            m (Except $errTyTerm $payloadTerm) :=
          Qed.Server.srvFinishM $statelessBody))
      if hasNewErrors (← get).messages priorRep priorUnrep then return

      let hCall ← allBinderIds.foldlM (init := ← `($handlerId)) fun acc a => `($acc $a)
      if let some ensSpec := ensSpec? then
        unless (← elabAsyncEnsuresThm priorRep priorUnrep srvName fnStr fnIdent handlerId
            (← `(fun _ : Unit => True)) (← `(Unit)) payloadTerm errTyTerm
            allBinderIds allBinderTys hCall #[] ensSpec) do
          return

      let hApp ← callArgs.foldlM (init := ← `($handlerId)) fun acc a => `($acc $a)
      dispatchArms := dispatchArms.push (← mkDispatchArm hApp)

    -- Emit client-safe parameter aliases, `<S>.<fn>_Outcome`, internal `<S>._rpc_<fn>`, and checked `<S>.<fn>`
    let mut paramTypeConsts : Array Name := #[]
    for (pTy, i) in pTyTerms.zipIdx do
      let pTyId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter s!"_Param_{i}")
      elabCommand (← `(command| abbrev $pTyId : Type := $pTy))
      paramTypeConsts := paramTypeConsts.push (fullSrvName ++ fnIdent.getId.appendAfter s!"_Param_{i}")

    let ensPayloadTerm : Term ← match ensSpec?, innerOpt? with
      | some ensSpec, some innerTy =>
          let ensApp ← pIdents.foldlM (init := ← `($(ensSpec.ensId))) fun acc p => `($acc $p)
          `(Option (Qed.Ensured $innerTy ($ensApp)))
      | some ensSpec, none         =>
          let ensApp ← pIdents.foldlM (init := ← `($(ensSpec.ensId))) fun acc p => `($acc $p)
          `(Qed.Ensured $payloadTerm ($ensApp))
      | none, _                    => pure payloadTerm
    let clientWireRespTerm : Term ← match errTypeId? with
      | some errId => `(Except (Qed.RpcDomainError $errId) $ensPayloadTerm)
      | none       => pure ensPayloadTerm

    let outcomeId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_Outcome")
    let outcomeRhs : Term ← match errTypeId? with
      | some errId => `(Qed.RpcOutcome $errId $ensPayloadTerm)
      | none       => `(Qed.RpcSimpleOutcome $ensPayloadTerm)
    if ensSpec?.isSome then
      elabCommand (← `(command|
        set_option linter.unusedVariables false in
        abbrev $outcomeId $[($pIdents:ident : $pTyTerms:term)]* : Type := $outcomeRhs))
    else
      elabCommand (← `(command|
        abbrev $outcomeId : Type := $outcomeRhs))

    let rawRpcId := mkIdentFrom fnIdent (srvName ++ Name.mkSimple s!"_rpc_{fnStr}")
    let clientFnId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId)
    let rpcUrlLit := Syntax.mkStrLit s!"/_qed/rpc/{srvShort}/{fnStr}"
    let reqTupleVal ← liftMacroM <| buildTupleVal (pIdents.map (⟨·.raw⟩))
    elabCommand (← `(command|
      def $rawRpcId {msg cb : Type} $[($pIdents:ident : $pTyTerms:term)]*
          (onDone : cb) [Qed.RpcCallback $clientWireRespTerm msg cb] : Qed.Cmd msg :=
        Qed.Cmd.rpc (req := $reqTupleTy) (resp := $clientWireRespTerm)
          $rpcUrlLit $reqTupleVal (Qed.RpcCallback.adapt (α := $clientWireRespTerm) onDone)))

    let rawApp ← pIdents.foldlM (init := ← `($rawRpcId)) fun acc p => `($acc $p)
    let clientFnBody ← `($rawApp onDone)
    let reqBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ← match clientReqId? with
      | some reqId =>
          let reqApp ← pIdents.foldlM (init := ← `($reqId)) fun acc p => `($acc $p)
          let b ← `(bracketedBinder| (_hReq : $reqApp := by qedProveRpcReq))
          pure #[b]
      | none => pure #[]
    elabCommand (← `(command|
      set_option linter.unusedVariables false in
      def $clientFnId {msg cb : Type} $[($pIdents:ident : $pTyTerms:term)]*
          (onDone : cb) [Qed.RpcCallback $clientWireRespTerm msg cb]
          $[$reqBinders]* : Qed.Cmd msg :=
        $clientFnBody))

    methodInfos := methodInfos.push {
      name := fnStr
      paramNames := fnParams.map (·.ident.getId)
      paramCount := fnParams.size
      isReadOnly
      isAsync := hasAwait
      isFallible := retTy.hasFallible
      isOption := innerOpt?.isSome
      hasClientReq := clientReqId?.isSome
      requiresAuth
      clientReqConst := clientReqId?.map fun _ => fullSrvName ++ fnIdent.getId.appendAfter "_req"
      clientReqLabel := String.intercalate " && " clientReqLabels.toList
      hasEnsures := ensSpec?.isSome
      ensPredConst := ensSpec?.map fun _ => fullSrvName ++ fnIdent.getId.appendAfter "_ens"
      domainErrTags := domainTagIdents.map (·.getId.toString)
      errTypeConst := errTypeId?.map fun _ => fullSrvName ++ fnIdent.getId ++ `Error
      rawRpcConst := fullSrvName ++ Name.mkSimple s!"_rpc_{fnStr}"
      outcomeConst := fullSrvName ++ fnIdent.getId.appendAfter "_Outcome"
      paramTypeConsts
    }

  elabServerDispatchCmds srvIdent stateId initStateId stateInvId invInitId
    srvName fullSrvName srvShort hasState envDecls allExtRoots methodInfos dispatchArms ctxId reqBytesId

open Lean Elab Command in
private def rollbackFailedServer (savedEnv : Environment)
    (priorRep priorUnrep : Nat) (priorKinds : Lean.NameSet) : CommandElabM Unit := do
  setEnv savedEnv
  modify fun s =>
    let m := s.messages
    { s with messages := {
        reported    := filterNewWarnings m.reported priorRep
        unreported  := filterNewWarnings m.unreported priorUnrep
        loggedKinds := priorKinds
      } }

open Lean Elab Command in
@[command_elab serverCmd]
def elabServerCmd : CommandElab := fun stx => do
  let savedEnv ← getEnv
  let priorLog := (← get).messages
  let priorRep := priorLog.reported.size
  let priorUnrep := priorLog.unreported.size
  let priorKinds := priorLog.loggedKinds
  try
    withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) do
      elabServerCmdCore priorRep priorUnrep stx
  catch ex =>
    rollbackFailedServer savedEnv priorRep priorUnrep priorKinds
    throw ex
  if hasNewErrors (← get).messages priorRep priorUnrep then
    rollbackFailedServer savedEnv priorRep priorUnrep priorKinds

/-! ## `fullstack` Command Elaborator & Endpoint Closure Verification -/

private def modRootOf (env : Lean.Environment) (n : Lean.Name) : Lean.Name :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames.getD idx.toNat Lean.Name.anonymous).getRoot
  | none     => Lean.Name.anonymous

private def collectReachableDefns (env : Lean.Environment) :
    Nat → List Lean.Name → Std.HashSet Lean.Name → Std.HashSet Lean.Name
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, n :: rest, seen =>
      if seen.contains n then
        collectReachableDefns env fuel rest seen
      else
        let seen' := seen.insert n
        let root := modRootOf env n
        if root == `Init || root == `Std || root == `Lean || root == `Lake then
          collectReachableDefns env fuel rest seen'
        else
          match env.find? n with
          | some (.defnInfo d) =>
              collectReachableDefns env fuel (d.value.getUsedConstants.toList ++ rest) seen'
          | _ =>
              collectReachableDefns env fuel rest seen'

open Lean Elab Command in
private def verifyFullstackRpcClosure (env : Environment) (fsName : Name) (srvInfo : ServerInfo)
    (cliIdent : Ident) (resolvedCli : Name) : CommandElabM Unit := do
  let srvMap := serverRegistry.getState env
  let mut rpcConstMap : NameMap (ServerInfo × ServerMethodInfo) := {}
  for (_, otherSrv) in srvMap do
    for mInfo in otherSrv.methods do
      if mInfo.rawRpcConst != .anonymous then
        rpcConstMap := rpcConstMap.insert mInfo.rawRpcConst (otherSrv, mInfo)
      rpcConstMap := rpcConstMap.insert (otherSrv.serverName ++ Name.mkSimple mInfo.name) (otherSrv, mInfo)
  let visited := collectReachableDefns env 300000 [resolvedCli] {}
  for n in visited do
    if let some (otherSrv, mInfo) := rpcConstMap.find? n then
      if otherSrv.serverName != srvInfo.serverName then
        throwErrorAt cliIdent s!"`fullstack {fsName}` mounts `server {srvInfo.shortName}`, but client `{cliIdent.getId}` calls RPC `{otherSrv.shortName}.{mInfo.name}` on unmounted server `{otherSrv.shortName}`"
    let root := modRootOf env n
    if root != `Qed && root != `Js && root != `Cli then
      if let some (.defnInfo d) := env.find? n then
        let badRef ← IO.mkRef (none : Option String)
        d.value.forEach fun sub => do
          if (← badRef.get).isNone then
            if let .lit (.strVal s) := sub then
              if s.startsWith "/_qed/rpc/" then
                let rest := (s.drop 10).toString
                match rest.splitOn "/" with
                | [srvPart, methodPart] =>
                    if srvPart != srvInfo.shortName || !(srvInfo.methods.any (·.name == methodPart)) then
                      badRef.set (some s)
                | _ => badRef.set (some s)
        if let some url ← badRef.get then
          let avail := String.intercalate ", " (srvInfo.methods.toList.map (·.name))
          throwErrorAt cliIdent s!"`fullstack {fsName}` mounts `server {srvInfo.shortName}` (methods: [{avail}]), but client `{cliIdent.getId}` targets invalid RPC endpoint `{url}`"

open Lean Elab Command in
@[command_elab fullstackCmd]
def elabFullstackCmd : CommandElab := fun stx => do
  let fsIdent : Ident := ⟨stx[1]⟩
  let fsName := fsIdent.getId
  let currNs ← getCurrNamespace
  let fullFsName := currNs ++ fsName
  let clauses := stx[3].getArgs

  let mut srvIdent? : Option Ident := none
  let mut cliIdent? : Option Ident := none
  let mut title?    : Option String := none

  for c in clauses do
    let k := c.getKind
    if k == ``fsServerClause then
      if srvIdent?.isSome then throwErrorAt c "duplicate `server` clause in `fullstack`"
      srvIdent? := some ⟨c[1]⟩
    else if k == ``fsClientClause then
      if cliIdent?.isSome then throwErrorAt c "duplicate `client` clause in `fullstack`"
      cliIdent? := some ⟨c[1]⟩
    else if k == ``fsTitleClause then
      if title?.isSome then throwErrorAt c "duplicate `title` clause in `fullstack`"
      title? := some ((⟨c[1]⟩ : TSyntax `str).getString)
    else
      throwErrorAt c "unexpected clause in `fullstack` block"

  let some srvIdent := srvIdent?
    | throwErrorAt fsIdent s!"`fullstack {fsName}` must specify `server <ServerName>`"
  let some cliIdent := cliIdent?
    | throwErrorAt fsIdent s!"`fullstack {fsName}` must specify `client <AppName>`"

  let env ← getEnv
  let srvMap := serverRegistry.getState env
  let candSrv1 := currNs ++ srvIdent.getId
  let some srvInfo := (srvMap.find? candSrv1).orElse (fun _ => srvMap.find? srvIdent.getId)
    | throwErrorAt srvIdent s!"unknown `server` `{srvIdent.getId}` in `fullstack {fsName}`"

  -- Validate that `client` resolves to a `Qed.App _ _` value (or a `component`/`app` owning `.app`)
  let cliTarget : Ident :=
    if env.contains (currNs ++ cliIdent.getId ++ `app) || env.contains (cliIdent.getId ++ `app) then
      mkIdentFrom cliIdent (cliIdent.getId ++ `app)
    else cliIdent
  let resolvedCli ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo cliTarget
  let appCheckId := mkIdentFrom fsIdent (fsName ++ `clientApp)
  elabCommand (← `(command| abbrev $appCheckId := $cliTarget))

  let cliCompName :=
    if resolvedCli.getString! == "app" then resolvedCli.getPrefix else resolvedCli
  verifyFullstackRpcClosure env fsName srvInfo cliIdent resolvedCli

  if env.contains (cliCompName ++ `usedRpcs) then
    let usedRpcsId := mkIdentFrom cliIdent (cliCompName ++ `usedRpcs)
    let srvMethodsId := mkIdentFrom srvIdent (srvInfo.serverName ++ `methods)
    let srvShortLit := Syntax.mkStrLit srvInfo.shortName
    let epThmId := mkIdentFrom fsIdent (fsName ++ `rpc_endpoints_valid)
    let ssrClosureId := mkIdentFrom fsIdent (fsName ++ `ssr_rpc_closure_complete)
    elabCommand (← `(command|
      theorem $epThmId :
          ∀ ep ∈ $usedRpcsId, ep.1 = $srvShortLit ∧ ep.2 ∈ $srvMethodsId := by
        decide))
    elabCommand (← `(command|
      theorem $ssrClosureId
          (dispatchMethod : String → ByteArray → Except String ByteArray)
          (ep : String × String) (hep : ep ∈ $usedRpcsId) (reqBody : ByteArray) :
          Qed.ssrDispatchRpc $srvShortLit $srvMethodsId dispatchMethod "POST"
              ("/_qed/rpc/" ++ ep.1 ++ "/" ++ ep.2) reqBody =
            dispatchMethod ep.2 reqBody :=
        Qed.ssr_rpc_closure_complete $srvShortLit $srvMethodsId $usedRpcsId $epThmId
          dispatchMethod (by decide) (by decide) ep hep reqBody))

  let pageTitle := title?.getD (fsName.toString)
  let titleId := mkIdentFrom fsIdent (fsName ++ `title)
  elabCommand (← `(command| def $titleId : String := $(Syntax.mkStrLit pageTitle)))

  modifyEnv fun e => fullstackRegistry.addEntry e {
    fullstackName := fullFsName
    serverName := srvInfo.serverName
    clientName := resolvedCli
    title := pageTitle
  }

end Qed.Server
