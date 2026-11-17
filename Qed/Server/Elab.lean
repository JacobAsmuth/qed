import Lean
import Qed.Proto
import Qed.Resource
import Qed.Runtime.Cmd
import Qed.Server.Core
import Qed.Server.Syntax
import Qed.Server.External
import Qed.Server.Invariant

namespace Qed.Server

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

structure ServerMethodInfo where
  name       : String
  paramCount : Nat
  isReadOnly : Bool
  isAsync    : Bool
  isFallible : Bool
  isOption   : Bool
deriving Inhabited, Repr

structure ServerInfo where
  serverName       : Lean.Name
  shortName        : String
  hasState         : Bool
  secrets          : Array String
  envVars          : Array (String × String × Option String)
  externalServices : Array (String × String)
  methods          : Array ServerMethodInfo
deriving Inhabited

initialize serverRegistry :
    Lean.SimplePersistentEnvExtension ServerInfo (Lean.NameMap ServerInfo) ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays =>
      arrays.foldl (fun acc arr => arr.foldl (fun m info => m.insert info.serverName info) acc) {}
    addEntryFn := fun m info => m.insert info.serverName info
  }

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

private inductive ExprMode where
  | val
  | boolCond
  | propInv
deriving BEq, DecidableEq

private inductive StateAccessRule where
  | pureStep (stateVar : Lean.Ident)
  | invariantProp (curVar oldVar : Lean.Ident) (inOld : Bool)
  | forbidAsyncOutsideAtomic
  | forbidInRequires
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
  if stx.getKind == ``srvAwait then true
  else stx.getArgs.any exprHasAwait

partial def stmtHasAwait (stx : Lean.Syntax) : Bool :=
  exprHasAwait stx

def blockHasAwait (stmts : Array Lean.Syntax) : Bool :=
  stmts.any stmtHasAwait

partial def exprCallsOld (stx : Lean.Syntax) : Bool :=
  if stx.getKind == ``srvCall then
    let callee := stx[0]
    if callee.getKind == ``srvIdent && callee[0].getId == `old then true
    else stx.getArgs.any exprCallsOld
  else
    stx.getArgs.any exprCallsOld

private def extractElseStmts (optElse : Lean.Syntax) : Option (Array Lean.Syntax) :=
  if optElse.getNumArgs == 2 then
    let body := optElse[1]
    if body.isOfKind Lean.nullKind then some body.getArgs else some #[body]
  else
    none

mutual
  partial def stmtAlwaysReturns (stx : Lean.Syntax) : Bool :=
    let k := stx.getKind
    if k == ``srvStmtReturn then true
    else if k == ``srvStmtAtomic then blockAlwaysReturns stx[1].getArgs
    else if k == ``srvStmtIf then
      match extractElseStmts stx[3] with
      | some elseStmts => blockAlwaysReturns stx[2].getArgs && blockAlwaysReturns elseStmts
      | none           => false
    else if k == ``srvStmtIfLet then
      match extractElseStmts stx[6] with
      | some elseStmts => blockAlwaysReturns stx[5].getArgs && blockAlwaysReturns elseStmts
      | none           => false
    else
      false

  partial def blockAlwaysReturns (stmts : Array Lean.Syntax) : Bool :=
    stmts.any stmtAlwaysReturns
end

mutual
  partial def exprHasUnwrap (stx : Lean.Syntax) : Bool :=
    let k := stx.getKind
    if k == ``srvUnwrap then true
    else if k == ``srvIdent then stx[0].getId.toString.endsWith "?"
    else if k == ``srvLam1 || k == ``srvLamN || k == ``srvForall then false
    else stx.getArgs.any exprHasUnwrap

  partial def stmtMayReturnEarly (stx : Lean.Syntax) : Bool :=
    let k := stx.getKind
    if k == ``srvStmtReturn then true
    else if k == ``srvStmtLetCatch then true
    else if k == ``srvStmtAtomic || k == ``srvStmtLetAtomic then true
    else if k == ``srvStmtIf then
      exprHasUnwrap stx[1] || blockMayReturnEarly stx[2].getArgs ||
        ((extractElseStmts stx[3]).map blockMayReturnEarly |>.getD false)
    else if k == ``srvStmtIfLet then
      exprHasUnwrap stx[4] || blockMayReturnEarly stx[5].getArgs ||
        ((extractElseStmts stx[6]).map blockMayReturnEarly |>.getD false)
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
  | .pureStep sv =>
      modify fun s => { s with stateRead := true }
      return sv
  | .invariantProp curV oldV inOld =>
      return if inOld then oldV else curV
  | .forbidAsyncOutsideAtomic =>
      throwErrorAt ref s!"cannot access server state `{field}` outside an `atomic` block in `{ctx.fnName}` because `{ctx.fnName}` uses `await` (prevents TOCTOU data races across suspension points)"
  | .forbidInRequires =>
      throwErrorAt ref s!"`requires` precondition in `{ctx.fnName}` cannot reference mutable server state `{field}`; check `{field}` inside the function body instead"
  | .statelessServer =>
      throwErrorAt ref s!"unknown identifier `{field}`"

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
      else if ctx.locals.contains s || s == "ctx" then
        return ⟨mkIdentFrom ref single⟩
      else if ctx.stateFields.contains s then
        let sv ← checkStateRead ref ctx s
        let fid := mkIdentFrom ref single
        return ← `(($sv).$fid:ident)
      else if ctx.envVars.contains s then
        return ⟨mkIdentFrom ref single⟩
      else
        return ⟨id⟩
  | root :: rest =>
      let rStr := root.toString
      if ctx.locals.contains rStr || rStr == "ctx" || ctx.envVars.contains rStr then
        let base : Term := ⟨mkIdentFrom ref root⟩
        foldProjections ref base rest
      else if ctx.stateFields.contains rStr then
        let sv ← checkStateRead ref ctx rStr
        let fid := mkIdentFrom ref root
        let base ← `(($sv).$fid:ident)
        foldProjections ref base rest
      else
        recordExtRoot root
        return ⟨id⟩

open Lean Elab Command in
private partial def unwrapParens1 (stx : Syntax) : Syntax :=
  if stx.getKind == ``srvParen && stx[1].getSepArgs.size == 1 then
    unwrapParens1 stx[1].getSepArgs[0]!
  else
    stx

open Lean Elab Command in
private def isPlainLiteralOrCtor (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx
  let k := u.getKind
  if k == ``srvLitNum || k == ``srvLitSci || k == ``srvLitStr || k == ``srvLitChar || k == ``srvArrLit then
    true
  else if k == ``srvIdent then
    let s := u[0].getId.toString
    s == "true" || s == "false" || s == "none"
  else
    false

open Lean Elab Command in
private def isNoneStx (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx
  u.getKind == ``srvIdent && u[0].getId.toString == "none"

open Lean Elab Command in
private def buildTupleVal (vals : Array Term) : CommandElabM Term := do
  if vals.isEmpty then `(())
  else if vals.size == 1 then return vals[0]!
  else
    let mut acc := vals.back!
    for revIdx in [1:vals.size] do
      acc ← `(($(vals[vals.size - 1 - revIdx]!), $acc))
    return acc

open Lean Elab Command in
private def finishTermMode (mode : ExprMode) (t : Term) : CommandElabM Term :=
  if mode == .propInv then `($t = true) else return t

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
partial def lowerExpr (ctx : LowerCtx) (mode : ExprMode) (stx : Syntax) : LowerM Term := do
  let lowerValOp (s : Syntax) : LowerM Term := do
    let t ← lowerExpr ctx .val s
    if isPlainLiteralOrCtor s then return t else `(Qed.Server.SrvVal.val $t)
  let k := stx.getKind
  if k == ``srvLitNum || k == ``srvLitSci || k == ``srvLitStr || k == ``srvLitChar then
    return ⟨stx[0]⟩
  else if k == ``srvInterp then
    let mut parts : Array Term := #[]
    for ch in stx[1].getArgs do
      if let some litStr := ch.isInterpolatedStrLit? then
        if !litStr.isEmpty then parts := parts.push (Syntax.mkStrLit litStr)
      else
        parts := parts.push (← `(toString (Qed.Server.SrvVal.val $(← lowerExpr ctx .val ch))))
    match parts.toList with
    | []      => return Syntax.mkStrLit ""
    | p :: ps => ps.foldlM (init := p) fun acc q => `($acc ++ $q)
  else if k == ``srvArrLit then
    let elems ← stx[1].getSepArgs.mapM fun e => do `(srvAutoField($(← lowerExpr ctx .val e)))
    `(#[$[$elems],*])
  else if k == ``srvParen then
    let elems := stx[1].getSepArgs
    if elems.size == 1 then lowerExpr ctx mode elems[0]!
    else liftM <| buildTupleVal (← elems.mapM (lowerExpr ctx .val))
  else if k == ``srvIdent then
    let (cleanId, qCount) := peelIdentTrailingQ ⟨stx[0]⟩
    let term ← hoistPureUnwraps stx ctx qCount (← resolveDottedIdent stx ctx cleanId)
    liftM <| finishTermMode mode term
  else if k == ``srvUnwrap then
    unless ctx.allowUnwrap do
      throwErrorAt stx s!"operator `?` cannot be used here in `{ctx.fnName}` (return type must be `T!` or `T?`, and `?` cannot appear inside lambdas or invariants)"
    let inner := unwrapParens1 stx[0]
    if inner.getKind == ``srvAwait then
      unless ctx.allowAwait do
        throwErrorAt inner "`await` cannot be used inside an `atomic` block, lambda, `requires`, or `invariant`; perform external I/O outside `atomic`"
      let callTerm ← lowerExpr ctx .val inner[1]
      let tmp ← freshIdent "_srvAw"
      modify fun s => { s with hoisted := s.hoisted.push (.awaitUnwrap stx tmp callTerm) }
      liftM <| finishTermMode mode ⟨tmp⟩
    else
      let term ← hoistPureUnwraps stx ctx 1 (← lowerExpr ctx .val stx[0])
      liftM <| finishTermMode mode term
  else if k == ``srvAwait then
    unless ctx.allowAwait do
      throwErrorAt stx "`await` cannot be used inside an `atomic` block, lambda, `requires`, or `invariant`; perform external I/O outside `atomic`"
    let inner := unwrapParens1 stx[1]
    if inner.getKind == ``srvUnwrap then
      unless ctx.allowUnwrap do
        throwErrorAt stx s!"operator `?` cannot be used in `{ctx.fnName}` because its return type is neither fallible (`T!`) nor optional (`T?`); handle the `await` error with `let x = await ... catch err`"
      let callTerm ← lowerExpr ctx .val inner[0]
      let tmp ← freshIdent "_srvAw"
      modify fun s => { s with hoisted := s.hoisted.push (.awaitUnwrap stx tmp callTerm) }
      liftM <| finishTermMode mode ⟨tmp⟩
    else
      throwErrorAt stx "unhandled fallible `await` expression; append `?` to propagate errors or use `let x = await ... catch err` to handle them inline"
  else if k == ``srvIndex then
    let elem ← `(srvGetElem($(← lowerExpr ctx .val stx[0]), $(← lowerExpr ctx .val stx[2])))
    liftM <| finishTermMode mode elem
  else if k == ``srvProj then
    let objTerm ← lowerExpr ctx .val stx[0]
    let (cleanFld, qCount) := peelIdentTrailingQ ⟨stx[2]⟩
    let term ← hoistPureUnwraps stx ctx qCount (← `(($objTerm).$cleanFld:ident))
    liftM <| finishTermMode mode term
  else if k == ``srvCall then
    let calleeStx := stx[0]
    let rawArgs := stx[2].getSepArgs
    if calleeStx.getKind == ``srvIdent && calleeStx[0].getId == `old then
      match ctx.stateRule with
      | .invariantProp curV oldV _ =>
          if rawArgs.size != 1 || rawArgs[0]!.getKind != ``srvCallArgPos then
            throwErrorAt stx "`old(...)` expects exactly one positional expression argument"
          modify fun s => { s with usedOld := true }
          return ← lowerExpr { ctx with stateRule := .invariantProp curV oldV true } mode rawArgs[0]![0]
      | _ => throwErrorAt stx "`old(...)` may only be used inside `invariant` declarations"
    if calleeStx.getKind == ``srvIdent && calleeStx[0].getId == `fail then
      if rawArgs.any (·.getKind == ``srvCallArgNamed) then
        throwErrorAt stx "`fail(...)` takes positional arguments `fail(msg)` or `fail(code, msg)`"
      if rawArgs.size == 1 then
        return ← `(Qed.Server.mkFail1 $(← lowerExpr ctx .val rawArgs[0]![0]))
      else if rawArgs.size == 2 then
        return ← `(Qed.Server.mkFail2 $(← lowerExpr ctx .val rawArgs[0]![0]) $(← lowerExpr ctx .val rawArgs[1]![0]))
      else
        throwErrorAt stx "`fail(...)` expects `(message)` or `(code, message)`"
    if !rawArgs.isEmpty && rawArgs.any (·.getKind == ``srvCallArgNamed) then
      unless rawArgs.all (·.getKind == ``srvCallArgNamed) do
        throwErrorAt stx "cannot mix named (`field = val`) and positional arguments in the same constructor call"
      let tyTerm ← lowerExpr ctx .val calleeStx
      let fIds : Array Ident := rawArgs.map (⟨·[0]⟩)
      let fVals ← rawArgs.mapM fun a => lowerExpr ctx .val a[2]
      return ← `(({ $[$fIds:ident := srvAutoField($fVals:term)],* } : $tyTerm))
    let calleeTerm ← lowerExpr ctx .val calleeStx
    let callRes ← rawArgs.foldlM (init := calleeTerm) fun acc a => do `($acc $(← lowerExpr ctx .val a[0]))
    liftM <| finishTermMode mode callRes
  else if k == ``srvNot then
    if mode == .propInv then `(¬ ($(← lowerExpr ctx .propInv stx[1])))
    else `(!($(← lowerExpr ctx .boolCond stx[1])))
  else if k == ``srvNeg then
    `(-($(← lowerValOp stx[1])))
  else if k == ``srvMul || k == ``srvDiv || k == ``srvMod || k == ``srvAdd || k == ``srvSub || k == ``srvCat then
    let a ← lowerValOp stx[0]; let b ← lowerValOp stx[2]
    if k == ``srvMul then `(($a) * ($b))
    else if k == ``srvDiv then `(($a) / ($b))
    else if k == ``srvMod then `(($a) % ($b))
    else if k == ``srvAdd then `(($a) + ($b))
    else if k == ``srvSub then `(($a) - ($b))
    else `(($a) ++ ($b))
  else if k == ``srvEq || k == ``srvNe then
    let (lhsStx, rhsStx) := if isNoneStx stx[0] && !isNoneStx stx[2] then (stx[2], stx[0]) else (stx[0], stx[2])
    let a ← lowerValOp lhsStx; let b ← lowerValOp rhsStx
    if k == ``srvEq then
      if mode == .propInv then `(($a) = ($b)) else `(($a) == ($b))
    else
      if mode == .propInv then `(($a) ≠ ($b)) else `(($a) != ($b))
  else if k == ``srvLe || k == ``srvGe || k == ``srvLt || k == ``srvGt then
    let a ← lowerValOp stx[0]; let b ← lowerValOp stx[2]
    let p ←
      if k == ``srvLe then `(($a) ≤ ($b))
      else if k == ``srvGe then `(($a) ≥ ($b))
      else if k == ``srvLt then `(($a) < ($b))
      else `(($a) > ($b))
    if mode == .propInv then return p else `(decide ($p))
  else if k == ``srvAnd || k == ``srvOr then
    if mode == .propInv then
      let a ← lowerExpr ctx .propInv stx[0]; let b ← lowerExpr ctx .propInv stx[2]
      if k == ``srvAnd then `($a ∧ $b) else `($a ∨ $b)
    else
      let a ← lowerExpr ctx .boolCond stx[0]; let b ← lowerExpr ctx .boolCond stx[2]
      if k == ``srvAnd then `($a && $b) else `($a || $b)
  else if k == ``srvLam1 || k == ``srvLamN then
    let pIds : Array Ident := if k == ``srvLam1 then #[⟨stx[0]⟩] else stx[1].getSepArgs.map (⟨·⟩)
    let bodyStx := if k == ``srvLam1 then stx[2] else stx[4]
    let lamCtx := { ctx with locals := ctx.locals ++ pIds.map (·.getId.toString), allowAwait := false, allowUnwrap := false }
    let body ← lowerExpr lamCtx .val bodyStx
    pIds.foldrM (init := body) fun pid acc => `(fun $pid:ident => $acc)
  else if k == ``srvForall then
    let bId : Ident := ⟨stx[1]⟩
    let arrTerm ← lowerExpr ctx .val stx[3]
    let innerCtx := { ctx with locals := ctx.locals.push bId.getId.toString, allowAwait := false, allowUnwrap := false }
    if mode == .propInv then `(∀ $bId:ident ∈ $arrTerm, $(← lowerExpr innerCtx .propInv stx[5]))
    else `(($arrTerm).all (fun $bId:ident => $(← lowerExpr innerCtx .boolCond stx[5])))
  else
    throwErrorAt stx s!"unsupported server expression syntax ({k})"

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
  if k == ``srvIdent then
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
  else if k == ``srvProj then
    let (rootId, prevSteps) ← parseLValPath ctx stx[0]
    let fldId : Ident := ⟨stx[2]⟩
    return (rootId, prevSteps.push (.field fldId))
  else if k == ``srvIndex then
    let (rootId, prevSteps) ← parseLValPath ctx stx[0]
    let idxTerm ← lowerExpr ctx .val stx[2]
    return (rootId, prevSteps.push (.index idxTerm))
  else
    throwErrorAt stx "invalid mutation target; expected `stateField`, `stateField.sub`, or `stateField[i].sub`"

open Lean Elab Command in
private def readPathTerm (sCur : Ident) (rootField : Ident) (steps : Array LValStep) :
    CommandElabM Term := do
  let mut cur ← `(($sCur).$rootField:ident)
  for st in steps do
    match st with
    | .field fid   => cur ← `(($cur).$fid:ident)
    | .index idxT  => cur ← `(srvGetElem($cur, $idxT))
  return cur

open Lean Elab Command in
private def buildUpdatedState (sCur : Ident) (rootField : Ident) (steps : Array LValStep)
    (leafNewTerm : Term) : CommandElabM Term := do
  if steps.isEmpty then
    return ← `({ $sCur with $rootField:ident := srvAutoField($leafNewTerm) })
  let rec go (idx : Nat) (container : Term) : CommandElabM Term := do
    if h : idx < steps.size then
      match steps[idx] with
      | .field fid =>
          let child ← `(($container).$fid:ident)
          let updatedChild ← go (idx + 1) child
          `({ $container with $fid:ident := srvAutoField($updatedChild) })
      | .index idxT =>
          let elem ← `(srvGetElem($container, $idxT))
          let updatedElem ← go (idx + 1) elem
          `(srvSetElem($container, $idxT, $updatedElem))
    else
      pure leafNewTerm
  let rootContainer ← `(($sCur).$rootField:ident)
  let updatedRoot ← go 0 rootContainer
  `({ $sCur with $rootField:ident := $updatedRoot })

open Lean Elab Command in
/-- Checks whether a bare statement expression is `target.push(elem)`. -/
private def matchPushCall? (stx : Syntax) : Option (Syntax × Syntax) :=
  if stx.getKind != ``srvCall then
    none
  else
    let args := stx[2].getSepArgs
    if args.size != 1 || args[0]!.getKind != ``srvCallArgPos then
      none
    else
      let callee := stx[0]
      let elemStx := args[0]![0]
      if callee.getKind == ``srvProj && callee[2].getId == `push then
        some (callee[0], elemStx)
      else if callee.getKind == ``srvIdent then
        let comps := callee[0].getId.components
        if comps.length ≥ 2 && comps.getLast? == some `push then
          let prefixComps := comps.take (comps.length - 1)
          let prefixName := prefixComps.foldl (fun acc seg => acc ++ seg) .anonymous
          let prefixIdent := mkIdentFrom callee prefixName
          let synthNode := Syntax.node (.fromRef callee) ``srvIdent #[prefixIdent.raw]
          some (synthNode, elemStx)
        else
          none
      else
        none

/-! ## Return Value Auto-Lifting & Hoist Wrapping -/

open Lean Elab Command in
private def isFailCall (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx
  u.getKind == ``srvCall && u[0].getKind == ``srvIdent && u[0][0].getId == `fail

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
private def wrapHoistsPure (ctx : LowerCtx) (s₀ sCur : Ident)
    (steps : Array HoistedStep) (body : Term) : LowerM Term := do
  steps.foldrM (init := body) fun step acc => do
    match step with
    | .awaitUnwrap ref _ _ =>
        throwErrorAt ref "`await` cannot appear inside a pure/atomic block"
    | .pureUnwrap _ tmp valTerm =>
        if !ctx.hasFallible then
          if let some innerTy := ctx.innerOptTy? then
            return ← `(match Qed.Server.SrvUnwrapOpt.unwrapOpt (Inner := $innerTy) $valTerm with
              | Except.error (Except.ok none) => ($sCur, some (Except.ok none))
              | Except.error (Except.error _e) => ($s₀, some (Except.error _e))
              | Except.ok $tmp:ident => $acc)
        `(match Qed.Server.SrvUnwrapErr.unwrapErr $valTerm with
          | Except.error _e => ($s₀, some (Except.error _e))
          | Except.ok $tmp:ident => $acc)

open Lean Elab Command in
private def mkAsyncUnwrapMatch (ctx : LowerCtx) (tmp : Ident) (valTerm acc : Term) : CommandElabM Term := do
  if !ctx.hasFallible then
    if let some innerTy := ctx.innerOptTy? then
      return ← `(match Qed.Server.SrvUnwrapOpt.unwrapOpt (Inner := $innerTy) $valTerm with
        | Except.error _early => Pure.pure (some _early)
        | Except.ok $tmp:ident => $acc)
  `(match Qed.Server.SrvUnwrapErr.unwrapErr $valTerm with
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
private def pushOptLocal (ctx : LowerCtx) (xStx : Syntax) : LowerCtx :=
  if xStx.isIdent then { ctx with locals := ctx.locals.push xStx.getId.toString } else ctx

open Lean Elab Command in
private def isBareUnwrapExpr (allowAwait : Bool) (eStx : Syntax) : Bool :=
  let u := unwrapParens1 eStx
  u.getKind == ``srvUnwrap ||
  (allowAwait && u.getKind == ``srvAwait && (unwrapParens1 u[1]).getKind == ``srvUnwrap) ||
  (eStx.getKind == ``srvIdent && eStx[0].getId.toString.endsWith "?") ||
  (eStx.getKind == ``srvProj && eStx[2].getId.toString.endsWith "?")

/-! ## Pure Statement Block Lowering (`lowerPureBlock` — for Sync `fn`s & `atomic` Blocks) -/

open Lean Elab Command in
/-- If a `catch` block consists of zero or more pure `let` bindings followed by a trailing
    expression `fallbackExpr` (rather than `return ...`), lowers it to a pure fallback value term
    so `let x = ... catch err` recovers `x` inline without exiting the enclosing `fn`. -/
private partial def lowerCatchFallback? (ctx : LowerCtx) (stmts : Array Syntax) : LowerM (Option Term) := do
  if stmts.isEmpty then
    return none
  else if stmts.size == 1 && stmts[0]!.getKind == ``srvStmtExpr then
    let eStx := stmts[0]![0]
    if exprHasAwait eStx || exprHasUnwrap eStx || (matchPushCall? eStx).isSome then return none
    let (eTerm, steps) ← lowerExprCollectingHoists { ctx with allowAwait := false } .val eStx
    if !steps.isEmpty then return none
    some <$> `(srvAutoField($eTerm))
  else if stmts[0]!.getKind == ``srvStmtLet then
    let st := stmts[0]!
    let rhsStx := st[3]
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
partial def lowerPureBlock (ctx : LowerCtx) (inAtomic : Bool) (s₀ sCur : Ident)
    (stmts : Array Syntax) : LowerM Term := do
  if stmts.isEmpty then
    return ← `(($sCur, none))
  let stmt := stmts[0]!
  let rest := stmts.extract 1 stmts.size
  let k := stmt.getKind
  let pCtx := { ctx with stateRule := if ctx.stateFields.isEmpty then .statelessServer else .pureStep sCur, allowAwait := false }

  let lowerPureBranch (thenCtx : LowerCtx) (thenStmts : Array Syntax)
      (elseStmts? : Option (Array Syntax)) (allowPureLetJoin : Bool)
      (mkBranch : Term → Term → CommandElabM Term) : LowerM Term := do
    let thenRet := blockAlwaysReturns thenStmts
    let elseRet := elseStmts?.map blockAlwaysReturns |>.getD false
    let lowerElseOpt (es? : Option (Array Syntax)) : LowerM Term :=
      match es? with
      | some es => lowerPureBlock pCtx inAtomic s₀ sCur es
      | none    => `(($sCur, none))
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
      let cont ← lowerPureBlock pCtx inAtomic s₀ sNext rest
      if allowPureLetJoin && !blockMayReturnEarly thenStmts && !(elseStmts?.map blockMayReturnEarly |>.getD false) then
        `(let $sNext:ident := ($br).1; $cont)
      else
        `(Qed.Server.srvSeq $br (fun $sNext:ident => $cont))

  if k == ``srvStmtAtomic || k == ``srvStmtLetAtomic then
    if inAtomic then throwErrorAt stmt "nested `atomic` blocks are forbidden"
    else if ctx.stateFields.isEmpty then throwErrorAt stmt "`atomic` is only valid in a `server` with `state` declarations"
    else throwErrorAt stmt s!"redundant `atomic` block: `{ctx.fnName}` has no `await` calls, so it already executes atomically"

  else if k == ``srvStmtReturn then
    if stmt[1].getNumArgs == 0 then
      `(($sCur, some $(← wrapOkValue pCtx (← `(())))))
    else
      let retExpr := stmt[1][0]
      if exprHasAwait retExpr && !(unwrapParens1 retExpr).isOfKind ``srvUnwrap then
        throwErrorAt retExpr "`await` cannot be used inside a synchronous or `atomic` block"
      if isFailCall retExpr then
        unless pCtx.hasFallible do
          throwErrorAt retExpr s!"`fail(...)` can only be returned from a fallible `T!` function (`{pCtx.fnName}` is not declared `-> ...!`)"
        let (errTerm, steps) ← lowerExprCollectingHoists pCtx .val retExpr
        wrapHoistsPure pCtx s₀ sCur steps (← `(($s₀, some (Except.error $errTerm))))
      else
        let (valTerm, steps) ← lowerExprCollectingHoists pCtx .val retExpr
        wrapHoistsPure pCtx s₀ sCur steps (← `(($sCur, some $(← wrapOkValue pCtx valTerm))))

  else if k == ``srvStmtLet then
    let (rhsTerm, steps) ← lowerExprCollectingHoists pCtx .val stmt[3]
    let checkedRhs ← if steps.isEmpty then `(srvRejectUnhandledErr($rhsTerm)) else pure rhsTerm
    let cont ← lowerPureBlock (pushOptLocal pCtx stmt[1]) inAtomic s₀ sCur rest
    wrapHoistsPure pCtx s₀ sCur steps (← liftM <| bindOptIdent stmt[1] checkedRhs cont)

  else if k == ``srvStmtLetCatch then
    let xStx := stmt[1]
    let rhsStx := stmt[3]
    let binderStx := stmt[5]
    let catchStmts := stmt[6].getArgs
    if rhsStx.getKind == ``srvAwait then
      throwErrorAt rhsStx "`await` cannot be used inside a synchronous or `atomic` block"
    let (rhsTerm, steps) ← lowerExprCollectingHoists pCtx .val rhsStx
    let errId : Ident := if binderStx.isIdent then ⟨binderStx⟩ else mkIdent `_srvCatchErr
    let catchCtx := pushOptLocal pCtx binderStx
    let okTerm ← lowerPureBlock (pushOptLocal pCtx xStx) inAtomic s₀ sCur rest
    if let some fbTerm ← lowerCatchFallback? catchCtx catchStmts then
      let okValId ← freshIdent "_catchOk"
      let valMatch ← `(match Qed.Server.SrvUnwrapErr.unwrapErr $rhsTerm with
        | Except.error $errId:ident => $fbTerm | Except.ok $okValId:ident => $okValId)
      wrapHoistsPure pCtx s₀ sCur steps (← liftM <| bindOptIdent xStx valMatch okTerm)
    else
      unless blockAlwaysReturns catchStmts do
        throwErrorAt stmt "the `catch` block must either `return` on all paths or end with a fallback value expression"
      let catchTerm ← lowerPureBlock catchCtx inAtomic s₀ sCur catchStmts
      let bindId : Ident := if xStx.isIdent then ⟨xStx⟩ else mkIdent `_srvDiscard
      wrapHoistsPure pCtx s₀ sCur steps (← `(match Qed.Server.SrvUnwrapErr.unwrapErr $rhsTerm with
        | Except.error $errId:ident => $catchTerm | Except.ok $bindId:ident => $okTerm))

  else if k == ``srvStmtAssign then
    let opStr := (stmt[1].reprint.getD "=").trimAscii.toString
    let (rhsTerm, steps) ← lowerExprCollectingHoists pCtx .val stmt[2]
    let (rootField, pathSteps) ← parseLValPath pCtx stmt[0]
    let leafNew ←
      if opStr == "=" then pure rhsTerm
      else if opStr == "+=" || opStr == "-=" then
        let curLeaf ← liftM <| readPathTerm sCur rootField pathSteps
        if opStr == "+=" then `(Qed.Server.SrvVal.val $curLeaf + Qed.Server.SrvVal.val $rhsTerm)
        else `(Qed.Server.SrvVal.val $curLeaf - Qed.Server.SrvVal.val $rhsTerm)
      else throwErrorAt stmt[1] s!"unsupported assignment operator `{opStr}`"
    let updatedState ← liftM <| buildUpdatedState sCur rootField pathSteps leafNew
    let sNext ← freshIdent "_s"
    let cont ← lowerPureBlock pCtx inAtomic s₀ sNext rest
    wrapHoistsPure pCtx s₀ sCur steps (← `(let $sNext:ident := $updatedState; $cont))

  else if k == ``srvStmtExpr then
    let eStx := stmt[0]
    if let some (targetStx, elemStx) := matchPushCall? eStx then
      let (elemTerm, steps) ← lowerExprCollectingHoists pCtx .val elemStx
      let (rootField, pathSteps) ← parseLValPath pCtx targetStx
      let curArr ← liftM <| readPathTerm sCur rootField pathSteps
      let updatedState ← liftM <| buildUpdatedState sCur rootField pathSteps (← `(($curArr).push (srvAutoField($elemTerm))))
      let sNext ← freshIdent "_s"
      let cont ← lowerPureBlock pCtx inAtomic s₀ sNext rest
      wrapHoistsPure pCtx s₀ sCur steps (← `(let $sNext:ident := $updatedState; $cont))
    else
      let (eTerm, steps) ← lowerExprCollectingHoists pCtx .val eStx
      let cont ← lowerPureBlock pCtx inAtomic s₀ sCur rest
      let body ← if isBareUnwrapExpr false eStx then `(let _ := $eTerm; $cont) else `(let _ : Unit := srvEnsureUnit($eTerm); $cont)
      wrapHoistsPure pCtx s₀ sCur steps body

  else if k == ``srvStmtIf then
    let (condTerm, steps) ← lowerExprCollectingHoists pCtx .boolCond stmt[1]
    let hGuard ← freshIdent "_srvG"
    let br ← lowerPureBranch pCtx stmt[2].getArgs (extractElseStmts stmt[3]) true
      fun t e => `(if $hGuard:ident : ($condTerm) = true then $t else $e)
    wrapHoistsPure pCtx s₀ sCur steps br

  else if k == ``srvStmtIfLet then
    let xId : Ident := ⟨stmt[2]⟩
    let (optTerm, steps) ← lowerExprCollectingHoists pCtx .val stmt[4]
    let br ← lowerPureBranch (pushOptLocal pCtx stmt[2]) stmt[5].getArgs (extractElseStmts stmt[6]) false
      fun t e => `(match $optTerm:term with | some $xId:ident => $t | none => $e)
    wrapHoistsPure pCtx s₀ sCur steps br

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

  if k == ``srvStmtAtomic then
    let (stateTyTerm, s0Id, atomBody, readOnly) ← lowerScopedAtomicBody stmt aCtx stateTyTerm? stmt[1].getArgs
    let earlyId ← freshIdent "_atomEarly"
    let cont ← lowerAsyncBlock aCtx stateTyTerm? rest
    let runCall ← if readOnly then
      `(Qed.Server.MonadAtomic.runAtomicRead (fun ($s0Id:ident : $stateTyTerm) => ($atomBody).2))
    else
      `(Qed.Server.MonadAtomic.runAtomic (fun ($s0Id:ident : $stateTyTerm) => Qed.Server.srvAtomicCommit $s0Id $atomBody))
    `($runCall >>= fun $earlyId:ident => match $earlyId:ident with | some _r => Pure.pure (some _r) | none => $cont)

  else if k == ``srvStmtLetAtomic then
    let xId : Ident := ⟨stmt[1]⟩
    let atomStmts := stmt[4].getArgs
    unless blockAlwaysReturns atomStmts do
      throwErrorAt stmt s!"`let {xId.getId} = atomic` block must `return` a value on every path"
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

  else if k == ``srvStmtReturn then
    if stmt[1].getNumArgs == 0 then
      `(Pure.pure (some $(← wrapOkValue aCtx (← `(())))))
    else
      let retExpr := stmt[1][0]
      let uRet := unwrapParens1 retExpr
      if uRet.getKind == ``srvAwait && !(unwrapParens1 uRet[1]).isOfKind ``srvUnwrap then
        unless aCtx.hasFallible do
          throwErrorAt retExpr s!"`return await ...` without `catch` requires `{aCtx.fnName}` to have a fallible `T!` return type"
        let (callTerm, steps) ← lowerExprCollectingHoists aCtx .val uRet[1]
        let rawId ← freshIdent "_retAw"
        let leaf ← match aCtx.innerOptTy? with
          | some innerTy => `($callTerm >>= fun $rawId:ident => Pure.pure (some (($rawId:ident).map (Qed.Server.SrvLiftOpt.liftOpt (Inner := $innerTy)))))
          | none         => `($callTerm >>= fun $rawId:ident => Pure.pure (some $rawId))
        wrapHoistsAsync aCtx steps leaf
      else if isFailCall retExpr then
        unless aCtx.hasFallible do
          throwErrorAt retExpr s!"`fail(...)` can only be returned from a fallible `T!` function (`{aCtx.fnName}` is not declared `-> ...!`)"
        let (errTerm, steps) ← lowerExprCollectingHoists aCtx .val retExpr
        wrapHoistsAsync aCtx steps (← `(Pure.pure (some (Except.error $errTerm))))
      else
        let (valTerm, steps) ← lowerExprCollectingHoists aCtx .val retExpr
        wrapHoistsAsync aCtx steps (← `(Pure.pure (some $(← wrapOkValue aCtx valTerm))))

  else if k == ``srvStmtLet then
    let (rhsTerm, steps) ← lowerExprCollectingHoists aCtx .val stmt[3]
    let checkedRhs ← if steps.isEmpty then `(srvRejectUnhandledErr($rhsTerm)) else pure rhsTerm
    let cont ← lowerAsyncBlock (pushOptLocal aCtx stmt[1]) stateTyTerm? rest
    wrapHoistsAsync aCtx steps (← liftM <| bindOptIdent stmt[1] checkedRhs cont)

  else if k == ``srvStmtLetCatch then
    let xStx := stmt[1]
    let rhsStx := unwrapParens1 stmt[3]
    let binderStx := stmt[5]
    let catchStmts := stmt[6].getArgs
    let errId : Ident := if binderStx.isIdent then ⟨binderStx⟩ else mkIdent `_srvCatchErr
    let catchCtx := pushOptLocal aCtx binderStx
    let okTerm ← lowerAsyncBlock (pushOptLocal aCtx xStx) stateTyTerm? rest
    let (scrutTerm, steps, awaitCall?) : Term × Array HoistedStep × Option (Term × Ident) ←
      if rhsStx.getKind == ``srvAwait then
        let (callTerm, steps) ← lowerExprCollectingHoists aCtx .val rhsStx[1]
        let rawId ← freshIdent "_catchAw"
        pure ((⟨rawId⟩ : Term), steps, some (callTerm, rawId))
      else
        let (rhsTerm, steps) ← lowerExprCollectingHoists aCtx .val rhsStx
        pure (rhsTerm, steps, none)
    let innerTerm ←
      if let some fbTerm ← lowerCatchFallback? catchCtx catchStmts then
        let okValId ← freshIdent "_catchOk"
        let valMatch ← `(match Qed.Server.SrvUnwrapErr.unwrapErr $scrutTerm with
          | Except.error $errId:ident => $fbTerm | Except.ok $okValId:ident => $okValId)
        liftM <| bindOptIdent xStx valMatch okTerm
      else
        unless blockAlwaysReturns catchStmts do
          throwErrorAt stmt "the `catch` block must either `return` on all paths or end with a fallback value expression"
        let catchTerm ← lowerAsyncBlock catchCtx stateTyTerm? catchStmts
        let bindId : Ident := if xStx.isIdent then ⟨xStx⟩ else mkIdent `_srvDiscard
        `(match Qed.Server.SrvUnwrapErr.unwrapErr $scrutTerm with
          | Except.error $errId:ident => $catchTerm | Except.ok $bindId:ident => $okTerm)
    let awaitedTerm ← match awaitCall? with
      | some (callTerm, rawId) => `($callTerm >>= fun $rawId:ident => $innerTerm)
      | none                   => pure innerTerm
    wrapHoistsAsync aCtx steps awaitedTerm

  else if k == ``srvStmtAssign then
    let _ ← parseLValPath aCtx stmt[0]
    throwErrorAt stmt "unexpected state mutation outside `atomic`"

  else if k == ``srvStmtExpr then
    let eStx := stmt[0]
    if let some (targetStx, _) := matchPushCall? eStx then
      let _ ← parseLValPath aCtx targetStx
      throwErrorAt stmt "unexpected state `.push(...)` outside `atomic`"
    else
      let (eTerm, steps) ← lowerExprCollectingHoists aCtx .val eStx
      let cont ← lowerAsyncBlock aCtx stateTyTerm? rest
      let body ← if isBareUnwrapExpr true eStx then `(let _ := $eTerm; $cont) else `(let _ : Unit := srvEnsureUnit($eTerm); $cont)
      wrapHoistsAsync aCtx steps body

  else if k == ``srvStmtIf then
    let (condTerm, steps) ← lowerExprCollectingHoists aCtx .boolCond stmt[1]
    let hGuard ← freshIdent "_srvG"
    let br ← lowerAsyncBranch aCtx stmt[2].getArgs (extractElseStmts stmt[3])
      fun t e => `(if $hGuard:ident : ($condTerm) = true then $t else $e)
    wrapHoistsAsync aCtx steps br

  else if k == ``srvStmtIfLet then
    let xId : Ident := ⟨stmt[2]⟩
    let (optTerm, steps) ← lowerExprCollectingHoists aCtx .val stmt[4]
    let br ← lowerAsyncBranch (pushOptLocal aCtx stmt[2]) stmt[5].getArgs (extractElseStmts stmt[6])
      fun t e => `(match $optTerm:term with | some $xId:ident => $t | none => $e)
    wrapHoistsAsync aCtx steps br

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
      stateDecls := stateDecls.push { ref := c, ident := id, ty, initStx := c[5] }
    else if k == ``srvInvMutatingClause then
      let fid : Ident := ⟨c[2]⟩
      let cond := c[4]
      let lbl := s!"mutating {fid.getId} requires {(cond.reprint.getD "").trimAscii.toString}"
      mutInvs := mutInvs.push { ref := c, fieldId := fid, condStx := cond, label := lbl }
    else if k == ``srvInvClause then
      let e := c[1]
      let lbl := (e.reprint.getD "invariant").trimAscii.toString
      invs := invs.push { ref := c, exprStx := e, isTwoSt := exprCallsOld e, label := lbl }
    else if k == ``srvFnClause then
      fnClauses := fnClauses.push c
    else
      throwErrorAt c "unexpected clause in `server` block"
  if fnClauses.isEmpty then
    throwErrorAt srvIdent s!"`server {srvName}` must declare at least one `fn`"
  let hasState := !stateDecls.isEmpty
  if !hasState && (!invs.isEmpty || !mutInvs.isEmpty) then
    throwErrorAt srvIdent s!"`server {srvName}` declares `invariant`s but has no `state` fields"
  for mi in mutInvs do
    unless stateDecls.any (·.ident.getId == mi.fieldId.getId) do
      throwErrorAt mi.fieldId s!"`invariant mutating {mi.fieldId.getId}` does not match any `state` field of `{srvName}`"
  return { envDecls, stateDecls, mutInvs, invs, fnClauses }

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
            let $sNewId:ident := ($targetCall).1
            $relProp := by
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
private def elabServerPureFn (priorRep priorUnrep : Nat)
    (srvName : Name) (fnStr : String) (fnIdent stateId stateInvId : Ident)
    (allBinderIds : Array Ident) (allBinderTys : Array Term) (callArgs : Array Term)
    (payloadTerm : Term) (baseCtx : LowerCtx) (bodyStmts : Array Lean.Syntax)
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (stateFieldNames envVarNames : Array String) :
    CommandElabM (Option (Term × Bool × Array Name)) := do
  let s0Id := mkIdent `_s0
  let fnLit := Syntax.mkStrLit fnStr
  let (pureBody, lSt) ← (lowerPureBlock baseCtx (inAtomic := false) s0Id s0Id bodyStmts).run {}
  let isReadOnly := lSt.mutated.isEmpty
  let stepId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_step")
  elabCommand (← `(command|
    def $stepId ($s0Id:ident : $stateId) $[($allBinderIds:ident : $allBinderTys:term)]* :
        $stateId × Except Qed.Server.ApiError $payloadTerm :=
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

  let snapCall ← callArgs.foldlM (init := ← `($stepId _sSnap)) fun acc a => `($acc $a)
  let runExpr ← if isReadOnly then
    `(Qed.Server.MonadAtomic.runAtomicRead (fun (_sSnap : $stateId) => ($snapCall).2))
  else
    `(Qed.Server.MonadAtomic.runAtomic (fun (_sSnap : $stateId) => $snapCall))
  return some (runExpr, isReadOnly, lSt.extRoots)

open Lean Elab Command in
private def elabServerAsyncFn (priorRep priorUnrep : Nat)
    (srvName : Name) (fnStr : String) (fnIdent stateId stateInvId : Ident)
    (allBinderIds : Array Ident) (allBinderTys : Array Term) (callArgs : Array Term)
    (payloadTerm : Term) (baseCtx : LowerCtx) (bodyStmts : Array Lean.Syntax)
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (stateFieldNames envVarNames : Array String) :
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
        m (Except Qed.Server.ApiError $payloadTerm) :=
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

  let hApp ← callArgs.foldlM (init := ← `($handlerId)) fun acc a => `($acc $a)
  return some (hApp, isReadOnly, lSt.extRoots)

open Lean Elab Command in
private def elabServerCmdCore (priorRep priorUnrep : Nat) : CommandElab := fun stx => do
  let srvIdent : Ident := ⟨stx[1]⟩
  let srvName := srvIdent.getId
  let srvShort := srvName.toString
  let currNs ← getCurrNamespace
  let fullSrvName := currNs ++ srvName
  let parsed ← parseServerClauses srvIdent srvName stx[2].getArgs
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

  -- 2. Elaborate each `fn`: step/handler + invariants + client RPC stub + dispatcher arm
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

    let rawParams := fc[3].getSepArgs
    let mut fnParams : Array ParsedFnParam := #[]
    let mut paramNames : Array String := #[]
    for rp in rawParams do
      let pid : Ident := ⟨rp[0]⟩
      let pstr := pid.getId.toString
      if pstr == "ctx" then
        throwErrorAt pid "`ctx` is already implicitly available as `RequestCtx` in every server function"
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

    let reqLines := fc[7].getArgs
    let bodyStmts := fc[8].getArgs
    if !isUnitPayload && !blockAlwaysReturns bodyStmts then
      throwErrorAt fnIdent s!"missing `return` on fallthrough path of `{fnStr}`"

    -- Lower `requires` preconditions (parameters + `env` + `ctx` only — never `state`!)
    let mut reqBoolTerms : Array Term := #[]
    let mut reqHypIds    : Array Ident := #[]
    let mut reqHypTys    : Array Term := #[]
    let mut reqLabels    : Array String := #[]
    for idx in [0:reqLines.size] do
      let rl := reqLines[idx]!
      let rExpr := rl[1]
      if exprHasAwait rExpr then
        throwErrorAt rExpr "`requires` precondition cannot contain `await`"
      let reqCtx : LowerCtx := {
        fnName := fnStr, stateFields := stateFieldNames, envVars := envVarNames, locals := paramNames
        stateRule := .forbidInRequires, allowAwait := false, allowUnwrap := false
        hasFallible := false, isOption := false, innerOptTy? := none
      }
      let (bTerm, rSt) ← (lowerExpr reqCtx .boolCond rExpr).run {}
      allExtRoots := allExtRoots ++ rSt.extRoots.filter (!allExtRoots.contains ·)
      let hId := mkIdent (Name.mkSimple s!"_hReq{idx}")
      let hTy ← `(($bTerm) = true)
      reqBoolTerms := reqBoolTerms.push bTerm
      reqHypIds := reqHypIds.push hId
      reqHypTys := reqHypTys.push hTy
      reqLabels := reqLabels.push ((rExpr.reprint.getD "requires").trimAscii.toString)

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
    }

    let pIdents := fnParams.map (·.ident)
    let pTyTerms := fnParams.map (·.tyTerm)
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
      let mut guardedRun ← `($runExpr >>= fun _fnRes => Pure.pure (_fnRes.map Qed.Proto.encode))
      for revIdx in [0:reqBoolTerms.size] do
        let ri := reqBoolTerms.size - 1 - revIdx
        let rCond := reqBoolTerms[ri]!
        let rHyp := reqHypIds[ri]!
        let rLbl := reqLabels[ri]!
        let rMsg := Syntax.mkStrLit s!"precondition failed: {rLbl}"
        let errCtor : Term ←
          if rLbl.contains "ctx.userId" || rLbl.contains "ctx.bearerToken" || rLbl.contains "ctx.isAuthenticated" then
            `(Qed.Server.ApiError.unauthorized $rMsg)
          else
            `(Qed.Server.ApiError.badRequest $rMsg)
        guardedRun ← `(if $rHyp:ident : ($rCond) = true then $guardedRun else Pure.pure (Except.error $errCtor))
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
          allBinderIds allBinderTys callArgs payloadTerm baseCtx bodyStmts
          invs mutInvs stateFieldNames envVarNames | return
      isReadOnly := ro
      allExtRoots := allExtRoots ++ extRoots.filter (!allExtRoots.contains ·)
      dispatchArms := dispatchArms.push (← mkDispatchArm runExpr)

    else if hasState && hasAwait then
      let some (hApp, ro, extRoots) ← elabServerAsyncFn priorRep priorUnrep
          srvName fnStr fnIdent stateId stateInvId
          allBinderIds allBinderTys callArgs payloadTerm baseCtx bodyStmts
          invs mutInvs stateFieldNames envVarNames | return
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
            m (Except Qed.Server.ApiError $payloadTerm) :=
          Qed.Server.srvFinishM $statelessBody))
      if hasNewErrors (← get).messages priorRep priorUnrep then return

      let hApp ← callArgs.foldlM (init := ← `($handlerId)) fun acc a => `($acc $a)
      dispatchArms := dispatchArms.push (← mkDispatchArm hApp)

    -- Emit typed client RPC stub `<S>.<fn>` (compiles cleanly to JS via `qedjs` with zero server secret/state refs!)
    let clientFnId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId)
    let rpcUrlLit := Syntax.mkStrLit s!"/_qed/rpc/{srvShort}/{fnStr}"
    let reqTupleVal ← buildTupleVal (pIdents.map (⟨·.raw⟩))
    elabCommand (← `(command|
      def $clientFnId {msg cb : Type} $[($pIdents:ident : $pTyTerms:term)]*
          (onDone : cb) [Qed.RpcCallback $payloadTerm msg cb] : Qed.Cmd msg :=
        Qed.Cmd.rpc (req := $reqTupleTy) (resp := $payloadTerm)
          $rpcUrlLit $reqTupleVal (Qed.RpcCallback.adapt (α := $payloadTerm) onDone)))

    methodInfos := methodInfos.push {
      name := fnStr
      paramCount := fnParams.size
      isReadOnly
      isAsync := hasAwait
      isFallible := retTy.hasFallible
      isOption := innerOpt?.isSome
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

/-! ## `fullstack` Command Elaborator -/

open Lean Elab Command in
@[command_elab fullstackCmd]
def elabFullstackCmd : CommandElab := fun stx => do
  let fsIdent : Ident := ⟨stx[1]⟩
  let fsName := fsIdent.getId
  let currNs ← getCurrNamespace
  let fullFsName := currNs ++ fsName
  let clauses := stx[2].getArgs

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
