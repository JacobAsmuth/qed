import Lean
import Qed.Proto
import Qed.Server.Core
import Qed.Server.Syntax
import Qed.Server.Registry
import Qed.Server.Db.QueryLower

namespace Qed.Server
open Qed.Lang

/-! ## Compile-Time Unhandled-Error Guards (`srvEnsureUnit` & `srvRejectUnhandledErr`) -/

syntax (name := srvEnsureUnitStx) "srvEnsureUnit(" term ")" : term
syntax (name := srvRejectErrStx)  "srvRejectUnhandledErr(" term ")" : term

open Lean Meta Elab Term in
@[term_elab srvEnsureUnitStx]
def elabSrvEnsureUnit : TermElab := fun stx _ => do
  let inner : Term := ⟨(stx.getArg 1)⟩
  let e ← elabTerm inner none
  synthesizeSyntheticMVarsNoPostponing
  let ty ← whnf (← inferType e)
  if ty.isAppOf ``Except || ty.isAppOf ``Option then
    throwErrorAt stx m!"unhandled fallible or optional expression of type `{← ppExpr ty}`; append `?` to propagate or `catch` to handle"
  ensureHasType (mkConst ``Unit) e

open Lean Meta Elab Term in
@[term_elab srvRejectErrStx]
def elabSrvRejectErr : TermElab := fun stx expectedType? => do
  let inner : Term := ⟨(stx.getArg 1)⟩
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

inductive StateAccessRule where
  | pureStep (stateVar : Lean.Ident) (overrides : Array (String × Lean.Ident) := #[])
  | invariantProp (curVar oldVar : Lean.Ident) (inOld : Bool)
  | forbidAsyncOutsideAtomic
  | forbidInRequires
  | forbidInEnsures
  | statelessServer

structure SrvChanSig where
  name       : String
  mkEmitId   : Lean.Ident
  paramCount : Nat
  hasEnsures : Bool

structure LowerCtx where
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
  channels         : Array SrvChanSig := #[]
  emitAcc?         : Option Lean.Ident := none
  wrapReturnSumInl : Bool := false
  dbs              : Array (String × DatabaseInfo) := #[]
  activeDbTx?      : Option (String × Lean.Ident) := none
  isHttpRoute      : Bool := false
  isStreamRoute    : Bool := false

inductive HoistedStep where
  | awaitUnwrap (ref : Lean.Syntax) (tmp : Lean.Ident) (callTerm : Lean.Term)
  | pureUnwrap  (ref : Lean.Syntax) (tmp : Lean.Ident) (valTerm : Lean.Term)

structure LowerState where
  nextId       : Nat := 0
  stateRead    : Bool := false
  mutated      : Array String := #[]
  dbWrite      : Bool := false
  extRoots     : Array Lean.Name := #[]
  usedOld      : Bool := false
  hoisted      : Array HoistedStep := #[]

abbrev LowerM := StateRefT LowerState Lean.Elab.Command.CommandElabM

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

private def matchTxStmt? (stx : Lean.Syntax) : Option (Lean.Syntax × String × Array Lean.Syntax) :=
  if stx.getKind == ``qedStmtDbTransaction then
    let dotStx := stx.getArg 0
    let idNode := if dotStx.isIdent then dotStx else dotStx.getArg 0
    let aliasName := match idNode.getId.eraseMacroScopes with
      | .str (.str .anonymous a) "transaction" => a
      | _ => ""
    some (dotStx, aliasName, suiteStmts (stx.getArg 2))
  else none

/-- Matches `setCookie(...)` or `clearCookie(...)`. Returns `(isClear, rawArgs)`. -/
private def matchSetCookieStmt? (stx : Lean.Syntax) : Option (Bool × Array Lean.Syntax) := do
  guard (stx.getKind == ``qedStmtExpr)
  let e := unwrapParens1 (stx.getArg 0)
  guard (e.getKind == ``qedCall)
  let callee := e.getArg 0
  let rawArgs := (e.getArg 2).getSepArgs
  match Db.extractDottedChain? callee with
  | some ["setCookie"]   => some (false, rawArgs)
  | some ["clearCookie"] => some (true, rawArgs)
  | _ => none

/-- Matches `send(...)` SSE event emission statements inside `stream` routes. -/
private def matchSseSendStmt? (stx : Lean.Syntax) : Option (Array Lean.Syntax) := do
  guard (stx.getKind == ``qedStmtExpr)
  let e := unwrapParens1 (stx.getArg 0)
  guard (e.getKind == ``qedCall)
  let callee := e.getArg 0
  let rawArgs := (e.getArg 2).getSepArgs
  match Db.extractDottedChain? callee with
  | some ["send"] => some rawArgs
  | _ => none

partial def exprHasAwait (stx : Lean.Syntax) : Bool :=
  if stx.getKind == ``qedAwait then true
  else stx.getArgs.any exprHasAwait

partial def stmtHasAwait (stx : Lean.Syntax) : Bool :=
  if (matchTxStmt? stx).isSome || (matchSetCookieStmt? stx).isSome || (matchSseSendStmt? stx).isSome then true
  else exprHasAwait stx || stx.getArgs.any stmtHasAwait

def blockHasAwait (stmts : Array Lean.Syntax) : Bool :=
  stmts.any stmtHasAwait

private def matchSrvEmitStmt? (stx : Lean.Syntax) : Option (Lean.Ident × Array Lean.Syntax) := do
  guard (stx.getKind == ``qedStmtExpr)
  let (chId, meth, rawArgs) ← matchIdentMethodCall? (stx.getArg 0)
  guard (meth == "emit")
  return (chId, rawArgs)

partial def stmtHasEmit (stx : Lean.Syntax) : Bool :=
  if (matchSrvEmitStmt? stx).isSome then true
  else stx.getArgs.any stmtHasEmit

def blockHasEmit (stmts : Array Lean.Syntax) : Bool :=
  stmts.any stmtHasEmit

partial def exprCallsOld (stx : Lean.Syntax) : Bool :=
  if stx.getKind == ``qedCall then
    let callee := (stx.getArg 0)
    if callee.getKind == ``qedIdent && (callee.getArg 0).getId == `old then true
    else stx.getArgs.any exprCallsOld
  else
    stx.getArgs.any exprCallsOld

mutual
  partial def stmtAlwaysReturns (stx : Lean.Syntax) : Bool :=
    let k := stx.getKind
    if k == ``qedStmtReturn then true
    else if k == ``qedStmtAtomic then blockAlwaysReturns (suiteStmts (stx.getArg 2))
    else if let some (_, _, txStmts) := matchTxStmt? stx then blockAlwaysReturns txStmts
    else if k == ``qedStmtIf then
      match desugarElifs (stx.getArg 4).getArgs (stx.getArg 5) with
      | some elseStmts => blockAlwaysReturns (suiteStmts (stx.getArg 3)) && blockAlwaysReturns elseStmts
      | none           => false
    else if k == ``qedStmtIfLet then
      match extractElseSuite (stx.getArg 7) with
      | some elseStmts => blockAlwaysReturns (suiteStmts (stx.getArg 6)) && blockAlwaysReturns elseStmts
      | none           => false
    else if k == ``qedStmtMatch then
      let cases := (stx.getArg 3).getArgs
      !cases.isEmpty && cases.all fun c => blockAlwaysReturns (suiteStmts (c.getArg 3))
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
    else if k == ``qedIdent then (stx.getArg 0).getId.toString.endsWith "?"
    else if k == ``qedLam1 || k == ``qedLamN || k == ``qedAllIn || k == ``qedAnyIn || k == ``qedAllVars then false
    else stx.getArgs.any exprHasUnwrap

  partial def stmtMayReturnEarly (stx : Lean.Syntax) : Bool :=
    let k := stx.getKind
    if k == ``qedStmtReturn then true
    else if k == ``qedStmtAtomic then true
    else if (matchTxStmt? stx).isSome then true
    else if k == ``qedStmtLet then
      (stx.getArg 5).getNumArgs > 0 || exprHasUnwrap (stx.getArg 4)
    else if k == ``qedStmtIf then
      exprHasUnwrap (stx.getArg 1) || blockMayReturnEarly (suiteStmts (stx.getArg 3)) ||
        ((desugarElifs (stx.getArg 4).getArgs (stx.getArg 5)).map blockMayReturnEarly |>.getD false)
    else if k == ``qedStmtIfLet then
      exprHasUnwrap (stx.getArg 4) || blockMayReturnEarly (suiteStmts (stx.getArg 6)) ||
        ((extractElseSuite (stx.getArg 7)).map blockMayReturnEarly |>.getD false)
    else if k == ``qedStmtMatch then
      (stx.getArg 1).getSepArgs.any exprHasUnwrap ||
        (stx.getArg 3).getArgs.any fun c => blockMayReturnEarly (suiteStmts (c.getArg 3))
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
        if rest.isEmpty then return ⟨id⟩
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
private partial def lowerJsonPayload (go : ExprMode → Syntax → SrvExprM Term) (stx : Syntax) : SrvExprM Term := do
  let u := unwrapParens1 stx
  if u.getKind == ``qedRecLit && (u.getArg 1).getNumArgs != 2 then
    let fields := (u.getArg 2).getSepArgs
    let pairs ← fields.mapM fun f => do
      let kLit := Syntax.mkStrLit (f.getArg 0).getId.eraseMacroScopes.toString
      let vJson ← lowerJsonPayload go (f.getArg 2)
      `(($kLit, $vJson))
    `(Qed.Json.obj [$[$pairs],*])
  else if u.getKind == ``qedArrLit then
    let elems := (u.getArg 1).getSepArgs
    let jElems ← elems.mapM (lowerJsonPayload go)
    `(Qed.Json.arr [$[$jElems],*])
  else
    let v ← go .val stx
    `(Qed.toJson $v)

open Lean Elab Command in
private def lowerSrvCallHook (stx calleeStx : Syntax) (rawArgs : Array Syntax) (mode : ExprMode)
    (go : ExprMode → Syntax → SrvExprM Term) : SrvExprM (Option Term) := do
  let ctx ← read
  if !ctx.dbs.isEmpty then
    if let some chain := Db.extractDottedChain? calleeStx then
      if let some aliasName := chain.head? then
        if let some (_, dbInfo) := ctx.dbs.find? (·.1 == aliasName) then
          let lowerVal (e : Syntax) : SrvExprM Term := go .val e
          let lowerValWithLocal (loc : String) (e : Syntax) : SrvExprM Term :=
            withReader (fun c => { c with locals := c.locals.push loc }) (go .val e)
          let txIdTerm? : Option Term := match ctx.activeDbTx? with
            | some (txAlias, txId) => if txAlias == aliasName then some ⟨txId.raw⟩ else none
            | none => none
          let (dbTerm, isWrite) ← Db.lowerDbCall lowerVal lowerValWithLocal ctx.fnName dbInfo stx chain rawArgs txIdTerm?
          if isWrite then
            modify fun s => { s with dbWrite := true }
          return some dbTerm
  if calleeStx.getKind == ``qedIdent && (calleeStx.getArg 0).getId == `old then
    match ctx.stateRule with
    | .invariantProp curV oldV _ =>
        if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then
          throwErrorAt stx "`old(...)` expects exactly one positional expression argument"
        modify fun s => { s with usedOld := true }
        return some (← withReader (fun c => { c with stateRule := .invariantProp curV oldV true }) (go mode rawArgs[0]![0]))
    | _ => throwErrorAt stx "`old(...)` may only be used inside `invariant` declarations"
  if calleeStx.getKind == ``qedIdent && (calleeStx.getArg 0).getId == `fail then
    if rawArgs.any (·.getKind == ``qedCallArgNamed) then
      throwErrorAt stx "`fail(...)` takes positional arguments `fail(.tag)`, `fail(.tag, msg)`, `fail(msg)`, or `fail(code, msg)`"
    if (rawArgs.size == 1 || rawArgs.size == 2) && (unwrapParens1 rawArgs[0]![0]).getKind == ``qedDotIdent then
      let uDot := unwrapParens1 rawArgs[0]![0]
      let tagId : Ident := ⟨(uDot.getArg 1)⟩
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
  if ctx.isHttpRoute && calleeStx.getKind == ``qedIdent then
    let fnName := (calleeStx.getArg 0).getId.eraseMacroScopes.toString
    let shadowed := ctx.locals.contains fnName || ctx.stateFields.contains fnName || ctx.envVars.contains fnName
    if !shadowed && (fnName == "text" || fnName == "json" || fnName == "html" || fnName == "bytes" || fnName == "redirect") then
      let mut posArgs : Array Syntax := #[]
      let mut statusStx? : Option Syntax := none
      for a in rawArgs do
        let k := a.getKind
        if k == ``qedCallArgPos then posArgs := posArgs.push (a.getArg 0)
        else if k == ``qedCallArgNamed then
          let key := (a.getArg 0).getId.eraseMacroScopes.toString
          if key == "status" then statusStx? := some (a.getArg 2)
          else throwErrorAt a s!"unknown argument `{key}` in `{fnName}(...)` (supported named argument: `status`)"
        else throwErrorAt a s!"unexpected argument in `{fnName}(...)`"
      if fnName == "bytes" then
        if posArgs.size != 2 then
          throwErrorAt stx "`bytes(contentType, body[, status = 200])` expects a content type and body"
        let ctT ← go .val posArgs[0]!
        let bodyT ← go .val posArgs[1]!
        let stT ← match statusStx? with
          | some s => go .val s
          | none   => liftM (show CommandElabM Term from `((200 : Nat)))
        return some (← `(Qed.Server.HttpResponse.bytes $ctT $bodyT $stT))
      else
        if posArgs.size != 1 then
          throwErrorAt stx s!"`{fnName}(...)` expects one positional argument (and optional `status = ...`)"
        let defaultStatus : Nat := if fnName == "redirect" then 302 else 200
        let stT ← match statusStx? with
          | some s => go .val s
          | none   => let lit := Syntax.mkNumLit (toString defaultStatus); liftM (show CommandElabM Term from `(($lit : Nat)))
        match fnName with
        | "text"     => let argT ← go .val posArgs[0]!; return some (← `(Qed.Server.HttpResponse.text $argT $stT))
        | "json"     => let jT ← lowerJsonPayload go posArgs[0]!; return some (← `(Qed.Server.HttpResponse.jsonOf $jT $stT))
        | "html"     => let argT ← go .val posArgs[0]!; return some (← `(Qed.Server.HttpResponse.html $argT $stT))
        | "redirect" => let argT ← go .val posArgs[0]!; return some (← `(Qed.Server.HttpResponse.redirect $argT $stT))
        | _          => pure ()
  return none

open Lean Elab Command in
private def lowerSrvUnwrapHook (recGo : ExprMode → Syntax → SrvExprM Term)
    (stx innerRaw : Syntax) (mode : ExprMode) : SrvExprM Term := do
  let ctx ← read
  unless ctx.allowUnwrap do
    throwErrorAt stx s!"operator `?` cannot be used here in `{ctx.fnName}` (return type must be `T!` or `T?`, and `?` cannot appear inside lambdas or invariants)"
  let inner := unwrapParens1 innerRaw
  if inner.getKind == ``qedAwait then
    unless ctx.allowAwait do
      throwErrorAt inner "`await` cannot be used inside an `atomic` block, lambda, `requires`, or `invariant`; perform external I/O outside `atomic`"
    let callTerm ← recGo .val (inner.getArg 1)
    let tmp ← liftM <| freshIdent "_srvAw"
    modify fun s => { s with hoisted := s.hoisted.push (.awaitUnwrap stx tmp callTerm) }
    liftMacroM (finishTermMode mode ⟨tmp⟩)
  else
    let v ← recGo .val innerRaw
    let term ← liftM <| hoistPureUnwraps stx ctx 1 v
    liftMacroM (finishTermMode mode term)

open Lean Elab Command in
private def lowerSrvAwaitHook (recGo : ExprMode → Syntax → SrvExprM Term)
    (stx argRaw : Syntax) (mode : ExprMode) : SrvExprM Term := do
  let ctx ← read
  unless ctx.allowAwait do
    throwErrorAt stx "`await` cannot be used inside an `atomic` block, lambda, `requires`, or `invariant`; perform external I/O outside `atomic`"
  let inner := unwrapParens1 argRaw
  if inner.getKind == ``qedUnwrap then
    unless ctx.allowUnwrap do
      throwErrorAt stx s!"operator `?` cannot be used in `{ctx.fnName}` because its return type is neither fallible (`T!`) nor optional (`T?`); handle the `await` error with `let x = await ... catch err:`"
    let callTerm ← recGo .val (inner.getArg 0)
    let tmp ← liftM <| freshIdent "_srvAw"
    modify fun s => { s with hoisted := s.hoisted.push (.awaitUnwrap stx tmp callTerm) }
    liftMacroM (finishTermMode mode ⟨tmp⟩)
  else
    throwErrorAt stx "unhandled fallible `await` expression; append `?` to propagate errors or use `let x = await ... catch err:` to handle them inline"

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
  lowerCall := lowerSrvCallHook
  lowerUnwrap := lowerSrvUnwrapHook recGo
  lowerAwait := lowerSrvAwaitHook recGo
  lowerFieldSetter := fun ref fid => throwErrorAt ref s!"`({fid.getId} = _)` is a client `component` field setter and is not supported in `server` functions"
  lowerJsx := fun ref _ =>
    if ref.getKind.toString.contains "Jsx" then
      throwErrorAt ref "JSX elements are only supported in client `component` views, not in `server` functions"
    else
      let sn := stxSnippet ref
      let what := if sn.isEmpty then s!"({ref.getKind})" else s!" `{sn}`"
      throwErrorAt ref s!"unsupported expression{what} in `server` function"
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
    let comps := (stx.getArg 0).getId.components
    match comps with
    | [] => throwErrorAt stx "invalid assignment target"
    | root :: rest =>
        let rStr := root.toString
        unless ctx.stateFields.contains rStr do
          if ctx.locals.contains rStr || ctx.envVars.contains rStr || rStr == "ctx" then
            throwErrorAt stx s!"cannot mutate `{rStr}`: parameters, `env` bindings, `ctx`, and `let` bindings are immutable; only `state` fields may be mutated"
          else
            let avail := if ctx.stateFields.isEmpty then "this server declares no `state` fields"
              else s!"`state` fields: {String.intercalate ", " (ctx.stateFields.toList.map fun f => s!"`{f}`")}"
            throwErrorAt stx s!"cannot mutate unknown state field `{rStr}` ({avail})"
        let _ ← checkStateRead stx ctx rStr
        recordMutated rStr
        let steps := rest.toArray.map fun f => LValStep.field (mkIdentFrom stx f)
        return (mkIdentFrom stx root, steps)
  else if k == ``qedProj then
    let (rootId, prevSteps) ← parseLValPath ctx (stx.getArg 0)
    let fldId : Ident := ⟨(stx.getArg 2)⟩
    return (rootId, prevSteps.push (.field fldId))
  else if k == ``qedIndex then
    let (rootId, prevSteps) ← parseLValPath ctx (stx.getArg 0)
    let idxTerm ← lowerExpr ctx .val (stx.getArg 2)
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
  u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId == `fail

open Lean Elab Command in
private def wrapOkValue (ctx : LowerCtx) (valTerm : Term) : CommandElabM Term := do
  let inner ← if let some innerTy := ctx.innerOptTy? then
    if valTerm.raw.isIdent && valTerm.raw.getId.eraseMacroScopes == `none then
      `((none : Option $innerTy))
    else
      `(Qed.Server.SrvLiftOpt.liftOpt (Inner := $innerTy) $valTerm)
  else
    `(srvAutoField($valTerm))
  if ctx.wrapReturnSumInl then
    `(Except.ok (Sum.inl $inner))
  else
    `(Except.ok $inner)

open Lean Elab Command in
private def errTyOf (ctx : LowerCtx) : CommandElabM Term :=
  match ctx.domainErrTy? with
  | some et => `(Qed.Server.SrvFailure $et)
  | none    => `(Qed.Server.ApiError)

open Lean Elab Command in
private def mkPureLeaf (ctx : LowerCtx) (stTerm optTerm : Term) : CommandElabM Term :=
  match ctx.emitAcc? with
  | some esId => `(($stTerm, $esId, $optTerm))
  | none      => `(($stTerm, $optTerm))

open Lean Elab Command in
private def mkPureErrLeaf (ctx : LowerCtx) (s₀ : Ident) (errTerm : Term) : CommandElabM Term :=
  match ctx.emitAcc? with
  | some _ => `(($s₀, ([] : List Qed.Server.WsEmit), some (Except.error $errTerm)))
  | none   => `(($s₀, some (Except.error $errTerm)))

open Lean Elab Command in
private def lowerEmitCall (ctx : LowerCtx) (stmt : Syntax) (chId : Ident) (rawArgs : Array Syntax) :
    LowerM (Term × Array HoistedStep) := do
  let chanNameStr := chId.getId.eraseMacroScopes.toString
  let some chSig := ctx.channels.find? (·.name == chanNameStr)
    | let avail := String.intercalate ", " (ctx.channels.toList.map (·.name))
      throwErrorAt chId s!"unknown WebSocket `channel` `{chanNameStr}` in `.emit(...)` (declared channels: [{avail}])"
  if rawArgs.size != chSig.paramCount + 1 then
    throwErrorAt stmt s!"`{chanNameStr}.emit(...)` expects {chSig.paramCount + 1} argument(s) ({chSig.paramCount} channel param(s) + 1 event), got {rawArgs.size}"
  let mut argTerms : Array Term := #[]
  let mut allSteps : Array HoistedStep := #[]
  for ra in rawArgs do
    unless ra.getKind == ``qedCallArgPos do
      throwErrorAt ra s!"named arguments are not supported in `{chanNameStr}.emit(...)`"
    let (at_, ss) ← lowerExprCollectingHoists ctx .val (ra.getArg 0)
    argTerms := argTerms.push at_
    allSteps := allSteps ++ ss
  let paramTerms := argTerms.extract 0 chSig.paramCount
  let evTerm := argTerms[chSig.paramCount]!
  let mut call ← paramTerms.foldlM (init := (chSig.mkEmitId : Term)) fun acc a => `($acc $a)
  call ← `($call (srvAutoField($evTerm)))
  if chSig.hasEnsures then
    call ← `($call (srvAutoEmit(True)))
  return (call, allSteps)

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
            let okNone ← liftM <| mkPureLeaf ctx matState (← `(some (Except.ok none)))
            let errLeaf ← liftM <| mkPureErrLeaf ctx s₀ (← `(_e))
            return ← `(match Qed.Server.SrvUnwrapOpt.unwrapOpt (Inner := $innerTy) $valTerm with
              | Except.error (Except.ok none) => $okNone
              | Except.error (Except.error _e) => $errLeaf
              | Except.ok $tmp:ident => $acc)
        let errLeaf ← liftM <| mkPureErrLeaf ctx s₀ (← `(_e))
        `(match Qed.Server.SrvUnwrap.unwrap (E := $errTy) $valTerm with
          | Except.error _e => $errLeaf
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
  (allowAwait && u.getKind == ``qedAwait && (unwrapParens1 (u.getArg 1)).getKind == ``qedUnwrap) ||
  (eStx.getKind == ``qedIdent && (eStx.getArg 0).getId.toString.endsWith "?") ||
  (eStx.getKind == ``qedProj && (eStx.getArg 2).getId.toString.endsWith "?")

/-! ## Pure Statement Block Lowering (`lowerPureBlock` — for Sync `def`s & `atomic:` Blocks) -/

open Lean Elab Command in
private partial def lowerCatchFallback? (ctx : LowerCtx) (stmts : Array Syntax) : LowerM (Option Term) := do
  if stmts.isEmpty then
    return none
  else if stmts.size == 1 && stmts[0]!.getKind == ``qedStmtExpr then
    let eStx := stmts[0]![0]
    if exprHasAwait eStx || exprHasUnwrap eStx || (matchPushCall? eStx).isSome || (matchSrvEmitStmt? stmts[0]!).isSome then return none
    let (eTerm, steps) ← lowerExprCollectingHoists { ctx with allowAwait := false } .val eStx
    if !steps.isEmpty then return none
    some <$> `(srvAutoField($eTerm))
  else if stmts[0]!.getKind == ``qedStmtLet && stmts[0]![5].getNumArgs == 0 then
    let st := stmts[0]!
    let rhsStx := (st.getArg 4)
    if exprHasAwait rhsStx || exprHasUnwrap rhsStx then return none
    let (rhsTerm, steps) ← lowerExprCollectingHoists { ctx with allowAwait := false } .val rhsStx
    if !steps.isEmpty then return none
    let checkedRhs ← `(srvRejectUnhandledErr($rhsTerm))
    let some tailTerm ← lowerCatchFallback? (pushOptLocal ctx (st.getArg 1)) (stmts.extract 1 stmts.size)
      | return none
    some <$> liftM (bindOptIdent (st.getArg 1) checkedRhs tailTerm)
  else
    return none

open Lean Elab Command in
private def lowerMatchScrutineesAndAlts (ctx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (lowerArm : LowerCtx → Array Syntax → LowerM Term) : LowerM (Term × Array HoistedStep) := do
  let mut scrutTerms : Array Term := #[]
  let mut allSteps : Array HoistedStep := #[]
  for sc in (stmt.getArg 1).getSepArgs do
    let (st, ss) ← lowerExprCollectingHoists ctx .val sc
    scrutTerms := scrutTerms.push st
    allSteps := allSteps ++ ss
  let cases := (stmt.getArg 3).getArgs
  let allRet := cases.all fun c => blockAlwaysReturns (suiteStmts (c.getArg 3))
  let alts ← cases.mapM fun c => do
    let pats ← (c.getArg 1).getSepArgs.mapM fun p => liftMacroM (lowerQedPat p)
    let pIds := ((c.getArg 1).getSepArgs.flatMap collectQedPatIds).map (·.toString)
    let cBody ← lowerArm { ctx with locals := ctx.locals ++ pIds } (suiteStmts (c.getArg 3) ++ if allRet then #[] else rest)
    `(Lean.Parser.Term.matchAltExpr| | $[$pats:term],* => $cBody)
  return (← `(match $[$scrutTerms:term],* with $[$alts:matchAlt]*), allSteps)

open Lean Elab Command in
private def extractSrvLetCatch? (clausesNode : Syntax) : LowerM (Option Syntax) := do
  let mut catchOpt? : Option Syntax := none
  for cl in clausesNode.getArgs do
    let ck := cl.getKind
    if ck == `Qed.Lang.letCatch then
      if catchOpt?.isSome then
        throwErrorAt cl "duplicate `catch` clause on `let`"
      catchOpt? := some (cl.getArg 1)
    else if ck == `Qed.Lang.letPredictBlock || ck == `Qed.Lang.letPredictExpr ||
            ck == `Qed.Lang.letOnConfirm || ck == `Qed.Lang.letRollback then
      throwErrorAt cl "`predict`, `on_confirm`, and `rollback` are only supported on client `component` `await` calls, not in `server` functions"
  return catchOpt?

open Lean Elab Command in
private def rejectSrvAssignPredict (stmt : Syntax) : LowerM Unit := do
  if stmt.getKind == ``qedStmtAssign && stmt.getNumArgs > 3 && (stmt.getArg 3).getNumArgs > 0 then
    throwErrorAt ((stmt.getArg 3).getArg 0) "`predict` is only supported on client `component` `await` calls, not in `server` functions"

open Lean Elab Command in
private def lowerCatchBody (stmt : Syntax) (catchCtx : LowerCtx) (xStx : Syntax)
    (errId : Ident) (scrutTerm okTerm : Term) (catchStmts : Array Syntax)
    (bindFallback : Syntax → Term → Term → LowerM Term)
    (lowerCatchBlock : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  if let some fbTerm ← lowerCatchFallback? catchCtx catchStmts then
    let okValId ← freshIdent "_catchOk"
    let valMatch ← `(match Qed.Server.SrvUnwrap.unwrap (E := Qed.Server.ApiError) $scrutTerm with
      | Except.error $errId:ident => $fbTerm | Except.ok $okValId:ident => $okValId)
    bindFallback xStx valMatch okTerm
  else
    unless blockAlwaysReturns catchStmts do
      throwErrorAt stmt "the `catch` block must either `return` on all paths or end with a fallback value expression"
    let catchTerm ← lowerCatchBlock catchCtx catchStmts
    let bindId : Ident := if xStx.isIdent then ⟨xStx⟩ else mkIdent `_srvDiscard
    `(match Qed.Server.SrvUnwrap.unwrap (E := Qed.Server.ApiError) $scrutTerm with
      | Except.error $errId:ident => $catchTerm | Except.ok $bindId:ident => $okTerm)

open Lean Elab Command in
private def lowerBranchCore (rest : Array Syntax) (thenCtx elseCtx : LowerCtx)
    (thenStmts : Array Syntax) (elseStmts? : Option (Array Syntax))
    (lowerBlock : LowerCtx → Array Syntax → LowerM Term)
    (emptyElse : LowerM Term)
    (mkBranch : Term → Term → CommandElabM Term)
    (joinRest : Term → LowerM Term) : LowerM Term := do
  let thenRet := blockAlwaysReturns thenStmts
  let elseRet := elseStmts?.map blockAlwaysReturns |>.getD false
  let lowerElseOpt (es? : Option (Array Syntax)) : LowerM Term :=
    match es? with
    | some es => lowerBlock elseCtx es
    | none    => emptyElse
  if rest.isEmpty then
    liftM =<< (mkBranch <$> lowerBlock thenCtx thenStmts <*> lowerElseOpt elseStmts?)
  else if thenRet && !elseRet then
    liftM =<< (mkBranch <$> lowerBlock thenCtx thenStmts <*> lowerBlock elseCtx ((elseStmts?.getD #[]) ++ rest))
  else if !thenRet && elseRet then
    liftM =<< (mkBranch <$> lowerBlock thenCtx (thenStmts ++ rest) <*> lowerBlock elseCtx (elseStmts?.getD #[]))
  else
    let br ← liftM =<< (mkBranch <$> lowerBlock thenCtx thenStmts <*> lowerElseOpt elseStmts?)
    joinRest br

open Lean Elab Command in
private def lowerPureBranch (pCtx : LowerCtx) (sCur : Ident) (matCur : Term)
    (rest thenStmts : Array Syntax) (thenCtx : LowerCtx)
    (elseStmts? : Option (Array Syntax)) (allowPureLetJoin : Bool)
    (mkBranch : Term → Term → CommandElabM Term)
    (recPure : LowerCtx → Ident → Array Syntax → LowerM Term) : LowerM Term :=
  lowerBranchCore rest thenCtx pCtx thenStmts elseStmts?
    (recPure · sCur)
    (do liftM <| mkPureLeaf pCtx matCur (← `(none)))
    mkBranch
    fun br => do
      let sNext ← freshIdent "_s"
      match pCtx.emitAcc? with
      | some _ =>
          let esNext ← freshIdent "_es"
          let joinCtx := { pCtx with
            stateRule := if pCtx.stateFields.isEmpty then .statelessServer else .pureStep sNext #[]
            emitAcc? := some esNext }
          let cont ← recPure joinCtx sNext rest
          `(Qed.Server.srvEmitSeq $br (fun $sNext:ident $esNext:ident => $cont))
      | none =>
          let joinCtx := { pCtx with stateRule := if pCtx.stateFields.isEmpty then .statelessServer else .pureStep sNext #[] }
          let cont ← recPure joinCtx sNext rest
          if allowPureLetJoin && !blockMayReturnEarly thenStmts && !(elseStmts?.map blockMayReturnEarly |>.getD false) then
            let hJoin ← freshIdent "_srvEq"
            `(Qed.Server.srvLetEq (($br : _ × Option Unit).1) (fun $sNext:ident $hJoin:ident => $cont))
          else
            `(Qed.Server.srvSeq $br (fun $sNext:ident => $cont))

open Lean Elab Command in
private def lowerPureReturn (pCtx : LowerCtx) (s₀ : Ident) (matCur : Term) (stmt : Syntax) : LowerM Term := do
  if (stmt.getArg 1).getNumArgs == 0 then
    liftM <| mkPureLeaf pCtx matCur (← `(some $(← wrapOkValue pCtx (← `(())))))
  else
    let retExpr := (stmt.getArg 1).getArg 0
    if exprHasAwait retExpr && !(unwrapParens1 retExpr).isOfKind ``qedUnwrap then
      throwErrorAt retExpr "`await` cannot be used inside a synchronous or `atomic` block"
    if isFailCall retExpr then
      unless pCtx.hasFallible do
        throwErrorAt retExpr s!"`fail(...)` can only be returned from a fallible `T!` function (`{pCtx.fnName}` is not declared `-> ...!`)"
      let (errTerm, steps) ← lowerExprCollectingHoists pCtx .val retExpr
      wrapHoistsPure pCtx s₀ matCur steps (← liftM <| mkPureErrLeaf pCtx s₀ errTerm)
    else
      let (valTerm, steps) ← lowerExprCollectingHoists pCtx .val retExpr
      wrapHoistsPure pCtx s₀ matCur steps (← liftM <| mkPureLeaf pCtx matCur (← `(some $(← wrapOkValue pCtx valTerm))))

open Lean Elab Command in
private def lowerPureLet (pCtx : LowerCtx) (s₀ sCur : Ident) (matCur : Term)
    (stmt : Syntax) (rest : Array Syntax)
    (recPure : LowerCtx → Ident → Array Syntax → LowerM Term) : LowerM Term := do
  let xStx := stmt.getArg 1
  let rhsStx := stmt.getArg 4
  if let some catchNode ← extractSrvLetCatch? (stmt.getArg 5) then
    if catchNode.getKind == `Qed.Lang.catchArms then
      throwErrorAt catchNode "multi-arm `catch: case ...` is for client components; in server functions use `catch err:`"
    let binderStx := catchNode.getArg 0
    let catchStmts := suiteStmts (catchNode.getArg 2)
    if rhsStx.getKind == ``qedAwait then
      throwErrorAt rhsStx "`await` cannot be used inside a synchronous or `atomic` block"
    let (rhsTerm, steps) ← lowerExprCollectingHoists pCtx .val rhsStx
    let errId : Ident := if binderStx.isIdent then ⟨binderStx⟩ else mkIdent `_srvCatchErr
    let catchCtx := pushOptLocal pCtx binderStx
    let okTerm ← recPure (pushOptLocal pCtx xStx) sCur rest
    let body ← lowerCatchBody stmt catchCtx xStx errId rhsTerm okTerm catchStmts
      bindSrvLetEq (recPure · sCur)
    wrapHoistsPure pCtx s₀ matCur steps body
  else
    let (rhsTerm, steps) ← lowerExprCollectingHoists pCtx .val rhsStx
    let checkedRhs ← if steps.isEmpty then `(srvRejectUnhandledErr($rhsTerm)) else pure rhsTerm
    let cont ← recPure (pushOptLocal pCtx xStx) sCur rest
    wrapHoistsPure pCtx s₀ matCur steps (← bindSrvLetEq xStx checkedRhs cont)

open Lean Elab Command in
private def lowerPureMutationStmt (pCtx : LowerCtx) (s₀ sCur : Ident) (matCur : Term)
    (stmt : Syntax) (rest : Array Syntax)
    (recPure : LowerCtx → Ident → Array Syntax → LowerM Term) : LowerM Term := do
  rejectSrvAssignPredict stmt
  let lowerMut (lvalStx : Syntax) (steps : Array HoistedStep)
      (mkLeaf : Array LValStep → Term → LowerM Term) : LowerM Term := do
    let (rootField, pathSteps) ← parseLValPath pCtx lvalStx
    let curRoot ← resolveStateFieldBase lvalStx pCtx rootField.getId
    let fNext ← freshIdent s!"_fld_{rootField.getId}_"
    let hFNext ← freshIdent "_srvEq"
    let cont ← recPure (setPureOverride pCtx sCur rootField.getId.toString fNext) sCur rest
    let chain ← withUpdatedPathCPS pathSteps 0 curRoot (mkLeaf pathSteps) fun updatedRaw => do
      let updatedRoot ← if pathSteps.isEmpty then `(srvTypedAs(($sCur).$rootField:ident, $updatedRaw)) else pure updatedRaw
      `(Qed.Server.srvLetEq $updatedRoot (fun $fNext:ident $hFNext:ident => $cont))
    wrapHoistsPure pCtx s₀ matCur steps chain
  if stmt.getKind == ``qedStmtAssign then
    let opStr := ((stmt.getArg 1).reprint.getD "=").trimAscii.toString
    let (rhsTerm, steps) ← lowerExprCollectingHoists pCtx .val (stmt.getArg 2)
    lowerMut (stmt.getArg 0) steps fun pathSteps curLeaf => do
      let val ←
        if opStr == "=" then pure rhsTerm
        else if opStr == "+=" then `(Qed.Lang.QedVal.val $curLeaf + Qed.Lang.QedVal.val $rhsTerm)
        else if opStr == "-=" then `(Qed.Lang.QedVal.val $curLeaf - Qed.Lang.QedVal.val $rhsTerm)
        else throwErrorAt (stmt.getArg 1) s!"unsupported assignment operator `{opStr}`"
      if pathSteps.isEmpty then `(srvAutoField($val)) else pure val
  else
    let some (targetStx, elemStx) := matchPushCall? (stmt.getArg 0) | unreachable!
    let (elemTerm, steps) ← lowerExprCollectingHoists pCtx .val elemStx
    lowerMut targetStx steps fun _ curArr =>
      `(($curArr).push (srvAutoField($elemTerm)))

open Lean Elab Command in
partial def lowerPureBlock (ctx : LowerCtx) (inAtomic : Bool) (s₀ sCur : Ident)
    (stmts : Array Syntax) : LowerM Term := do
  let curOverrides := getPureOverrides ctx
  let matCur ← liftM <| materializeState sCur curOverrides
  if stmts.isEmpty then
    return ← liftM <| mkPureLeaf ctx matCur (← `(none))
  let stmt := stmts[0]!
  let rest := stmts.extract 1 stmts.size
  let k := stmt.getKind
  let pCtx := { ctx with
    stateRule := if ctx.stateFields.isEmpty then .statelessServer else .pureStep sCur curOverrides
    allowAwait := false }
  let recPure := fun c s st => lowerPureBlock c inAtomic s₀ s st
  if k == ``qedStmtPass then
    recPure pCtx sCur rest
  else if let some (chId, rawArgs) := matchSrvEmitStmt? stmt then
    let some esId := pCtx.emitAcc?
      | throwErrorAt stmt "internal error: `emit` accumulator not initialized"
    let (emitTerm, steps) ← lowerEmitCall pCtx stmt chId rawArgs
    let esNext ← freshIdent "_es"
    let cont ← recPure { pCtx with emitAcc? := some esNext } sCur rest
    let body ← `(let $esNext:ident : List Qed.Server.WsEmit := $esId ++ [$emitTerm]; $cont)
    wrapHoistsPure pCtx s₀ matCur steps body
  else if k == `Qed.Server.atomicExport then
    let expTerm : Term := ⟨stmt.getArg 0⟩
    let wrapped ← if pCtx.wrapReturnSumInl then `(Except.ok (Sum.inr $expTerm)) else `(Except.ok $expTerm)
    liftM <| mkPureLeaf pCtx matCur (← `(some $wrapped))
  else if k == ``qedStmtAtomic then
    if inAtomic then throwErrorAt stmt "nested `atomic` blocks are forbidden"
    else if ctx.stateFields.isEmpty then throwErrorAt stmt "`atomic` is only valid in a `server` with `state` declarations"
    else throwErrorAt stmt s!"redundant `atomic` block: `{ctx.fnName}` has no `await` calls, so it already executes atomically"
  else if (matchTxStmt? stmt).isSome then
    throwErrorAt stmt "cannot start a database `transaction` inside an `atomic:` block; run database transactions outside `atomic:`"
  else if (matchSetCookieStmt? stmt).isSome then
    throwErrorAt stmt "cannot call `setCookie`/`clearCookie` inside an `atomic:` block; emit cookies outside `atomic:`"
  else if (matchSseSendStmt? stmt).isSome then
    throwErrorAt stmt "cannot call `send(...)` inside an `atomic:` block; emit SSE events outside `atomic:`"
  else if k == ``qedStmtReturn then
    lowerPureReturn pCtx s₀ matCur stmt
  else if k == ``qedStmtLet then
    lowerPureLet pCtx s₀ sCur matCur stmt rest recPure
  else if k == ``qedStmtAssign || (k == ``qedStmtExpr && (matchPushCall? (stmt.getArg 0)).isSome) then
    lowerPureMutationStmt pCtx s₀ sCur matCur stmt rest recPure
  else if k == ``qedStmtExpr then
    let eStx := stmt.getArg 0
    let (eTerm, steps) ← lowerExprCollectingHoists pCtx .val eStx
    let cont ← recPure pCtx sCur rest
    let valTerm ← if isBareUnwrapExpr false eStx then pure eTerm else `(srvEnsureUnit($eTerm))
    let xId ← freshIdent "_srvDiscard"
    let hEq ← freshIdent "_srvEq"
    let body ← `(Qed.Server.srvLetEq $valTerm (fun $xId:ident $hEq:ident => $cont))
    wrapHoistsPure pCtx s₀ matCur steps body
  else if k == ``qedStmtIf then
    let (condTerm, steps) ← lowerExprCollectingHoists pCtx .propGuard (stmt.getArg 1)
    let hGuard ← freshIdent "_srvG"
    let br ← lowerPureBranch pCtx sCur matCur rest (suiteStmts (stmt.getArg 3)) pCtx
      (desugarElifs (stmt.getArg 4).getArgs (stmt.getArg 5)) true
      (fun t e => `(if $hGuard:ident : $condTerm then $t else $e)) recPure
    wrapHoistsPure pCtx s₀ matCur steps br
  else if k == ``qedStmtIfLet then
    let patStx := stmt.getArg 2
    let patTerm ← liftMacroM (lowerQedPat patStx)
    let patIds := (collectQedPatIds patStx).map (·.toString)
    let (scrutTerm, steps) ← lowerExprCollectingHoists pCtx .val (stmt.getArg 4)
    let thenCtx := { pCtx with locals := pCtx.locals ++ patIds }
    let hMatch ← freshIdent "_srvM"
    let br ← lowerPureBranch pCtx sCur matCur rest (suiteStmts (stmt.getArg 6)) thenCtx
      (extractElseSuite (stmt.getArg 7)) false
      (fun t e => `(match $hMatch:ident : $scrutTerm:term with | $patTerm => $t | _ => $e)) recPure
    wrapHoistsPure pCtx s₀ matCur steps br
  else if k == ``qedStmtMatch then
    let (matchT, allSteps) ← lowerMatchScrutineesAndAlts pCtx stmt rest (recPure · sCur)
    wrapHoistsPure pCtx s₀ matCur allSteps matchT
  else
    let sn := stxSnippet stmt
    let what := if sn.isEmpty then s!"({k})" else s!" `{sn}`"
    throwErrorAt stmt s!"unsupported statement{what} in server function `{ctx.fnName}`"

/-! ## Stateless Pure/Async & Stateful Async Block Lowering (`lowerAsyncBlock`) -/

private partial def stxMentionsName (name : String) (stx : Lean.Syntax) : Bool :=
  match stx with
  | .ident _ _ v _ =>
      match v.eraseMacroScopes.components with
      | root :: _ => root.toString == name
      | [] => false
  | .node _ _ args => args.any (stxMentionsName name)
  | _ => false

private partial def stmtHasNonFailReturn (stx : Lean.Syntax) : Bool :=
  let k := stx.getKind
  if k == ``qedStmtReturn then
    (stx.getArg 1).getNumArgs == 0 || !isFailCall ((stx.getArg 1).getArg 0)
  else stx.getArgs.any stmtHasNonFailReturn

private def collectAtomicExports (atomStmts rest : Array Lean.Syntax) : Array Lean.Ident := Id.run do
  let mut ids : Array Lean.Ident := #[]
  for s in atomStmts do
    if s.getKind == ``qedStmtLet && (s.getArg 1).isIdent then
      let id : Lean.Ident := ⟨s.getArg 1⟩
      let nm := id.getId.eraseMacroScopes.toString
      if rest.any (stxMentionsName nm) then
        ids := ids.filter (·.getId.eraseMacroScopes.toString != nm) |>.push id
  ids

open Lean Elab Command in
private def mkAtomicExportTuple (ids : Array Ident) : CommandElabM Term := do
  let ts : Array Term := ids.map (⟨·.raw⟩)
  ts.foldrM (init := ts.back!) (start := ts.size - 1) fun a acc => `(($a, $acc))

open Lean Elab Command in
private def lowerScopedAtomicBody (stmt : Syntax) (atomCtx : LowerCtx) (stateTyTerm? : Option Term)
    (atomStmts : Array Syntax) : LowerM (Term × Ident × Term × Bool × Bool) := do
  let some stateTyTerm := stateTyTerm?
    | throwErrorAt stmt "`atomic` is only valid in a `server` with `state` declarations"
  if blockHasAwait atomStmts then
    throwErrorAt stmt "cannot use `await` inside an `atomic` block; perform external I/O outside `atomic` so shared locks never span network calls"
  let s0Id ← freshIdent "_sAtom"
  let hasEmit := blockHasEmit atomStmts
  let es0Id ← freshIdent "_es0"
  let savedMut := (← get).mutated
  modify fun s => { s with mutated := #[] }
  let bodyCtx := if hasEmit then { atomCtx with emitAcc? := some es0Id } else atomCtx
  let rawAtomBody ← lowerPureBlock bodyCtx (inAtomic := true) s0Id s0Id atomStmts
  let atomBody ← if hasEmit then
    `(let $es0Id:ident : List Qed.Server.WsEmit := []; $rawAtomBody)
  else
    pure rawAtomBody
  let atomMut := (← get).mutated
  modify fun s => { s with mutated := savedMut ++ atomMut.filter (!savedMut.contains ·) }
  return (stateTyTerm, s0Id, atomBody, atomMut.isEmpty, hasEmit)

open Lean Elab Command in
private def emitAtomicRun (s0Id : Ident) (stateTyTerm atomBody : Term)
    (readOnly hasEmit isFinish : Bool) (onResult : Term → CommandElabM Term) : LowerM Term := do
  if hasEmit then
    let pairId ← freshIdent "_atomPair"
    let runCall ←
      if isFinish then
        if readOnly then
          `(Qed.Server.MonadAtomic.runAtomicRead (fun ($s0Id:ident : $stateTyTerm) => (Qed.Server.srvFinishEmit $s0Id $atomBody).2))
        else
          `(Qed.Server.MonadAtomic.runAtomic (fun ($s0Id:ident : $stateTyTerm) => Qed.Server.srvFinishEmit $s0Id $atomBody))
      else
        if readOnly then
          `(Qed.Server.MonadAtomic.runAtomicRead (fun ($s0Id:ident : $stateTyTerm) => (Qed.Server.srvAtomicCommitEmit $s0Id $atomBody).2))
        else
          `(Qed.Server.MonadAtomic.runAtomic (fun ($s0Id:ident : $stateTyTerm) => Qed.Server.srvAtomicCommitEmit $s0Id $atomBody))
    `($runCall >>= fun $pairId:ident =>
        Qed.Server.flushWsEmits ($pairId).2 >>= fun _ =>
        $(← liftM <| onResult (← `(($pairId).1))))
  else
    let resId ← freshIdent "_atomRes"
    let runCall ←
      if isFinish then
        if readOnly then
          `(Qed.Server.MonadAtomic.runAtomicRead (fun ($s0Id:ident : $stateTyTerm) => (Qed.Server.srvFinish $s0Id $atomBody).2))
        else
          `(Qed.Server.MonadAtomic.runAtomic (fun ($s0Id:ident : $stateTyTerm) => Qed.Server.srvFinish $s0Id $atomBody))
      else
        if readOnly then
          `(Qed.Server.MonadAtomic.runAtomicRead (fun ($s0Id:ident : $stateTyTerm) => ($atomBody).2))
        else
          `(Qed.Server.MonadAtomic.runAtomic (fun ($s0Id:ident : $stateTyTerm) => Qed.Server.srvAtomicCommit $s0Id $atomBody))
    `($runCall >>= fun $resId:ident => $(← liftM <| onResult ⟨resId.raw⟩))

open Lean Elab Command in
private def lowerAtomicStmt (aCtx : LowerCtx) (stateTyTerm? : Option Term)
    (stmt : Syntax) (rest : Array Syntax)
    (lowerRest : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let atomStmts := suiteStmts (stmt.getArg 2)
  if blockAlwaysReturns atomStmts then
    let (stateTyTerm, s0Id, atomBody, readOnly, hasEmit) ← lowerScopedAtomicBody stmt aCtx stateTyTerm? atomStmts
    emitAtomicRun s0Id stateTyTerm atomBody readOnly hasEmit true fun res => `(Pure.pure (some $res))
  else
    let exportedIds := collectAtomicExports atomStmts rest
    if !exportedIds.isEmpty then
      let hasEarlyOk := atomStmts.any stmtHasNonFailReturn
      let expTuple ← liftM <| mkAtomicExportTuple exportedIds
      let exportStmt := Syntax.node (.fromRef stmt) `Qed.Server.atomicExport #[expTuple.raw]
      let atomCtx :=
        if hasEarlyOk then { aCtx with wrapReturnSumInl := true }
        else { aCtx with innerOptTy? := none, isOption := false }
      let (stateTyTerm, s0Id, atomBody, readOnly, hasEmit) ←
        lowerScopedAtomicBody stmt atomCtx stateTyTerm? (atomStmts.push exportStmt)
      let contCtx := { aCtx with locals := aCtx.locals ++ exportedIds.map (·.getId.eraseMacroScopes.toString) }
      let cont ← lowerRest contCtx rest
      emitAtomicRun s0Id stateTyTerm atomBody readOnly hasEmit true fun res =>
        if hasEarlyOk then
          `(match $res:term with
            | Except.error _e => Pure.pure (some (Except.error _e))
            | Except.ok (Sum.inl _v) => Pure.pure (some (Except.ok _v))
            | Except.ok (Sum.inr $expTuple:term) => $cont)
        else
          `(match $res:term with
            | Except.error _e => Pure.pure (some (Except.error _e))
            | Except.ok $expTuple:term => $cont)
    else
      let (stateTyTerm, s0Id, atomBody, readOnly, hasEmit) ← lowerScopedAtomicBody stmt aCtx stateTyTerm? atomStmts
      let cont ← lowerRest aCtx rest
      emitAtomicRun s0Id stateTyTerm atomBody readOnly hasEmit false fun early =>
        `(match $early:term with | some _r => Pure.pure (some _r) | none => $cont)

open Lean Elab Command in
private def lowerAsyncReturn (aCtx : LowerCtx) (stmt : Syntax) : LowerM Term := do
  if (stmt.getArg 1).getNumArgs == 0 then
    `(Pure.pure (some $(← wrapOkValue aCtx (← `(())))))
  else
    let retExpr := (stmt.getArg 1).getArg 0
    let uRet := unwrapParens1 retExpr
    if uRet.getKind == ``qedAwait && !(unwrapParens1 (uRet.getArg 1)).isOfKind ``qedUnwrap then
      unless aCtx.hasFallible do
        throwErrorAt retExpr s!"`return await ...` without `catch` requires `{aCtx.fnName}` to have a fallible `T!` return type"
      let (callTerm, steps) ← lowerExprCollectingHoists aCtx .val (uRet.getArg 1)
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

open Lean Elab Command in
private def lowerAsyncLet (aCtx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (recAsync : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let xStx := stmt.getArg 1
  let rhsRaw := stmt.getArg 4
  if let some catchNode ← extractSrvLetCatch? (stmt.getArg 5) then
    if catchNode.getKind == `Qed.Lang.catchArms then
      throwErrorAt catchNode "multi-arm `catch: case ...` is for client components; in server functions use `catch err:`"
    let rhsStx := unwrapParens1 rhsRaw
    let binderStx := catchNode.getArg 0
    let catchStmts := suiteStmts (catchNode.getArg 2)
    let errId : Ident := if binderStx.isIdent then ⟨binderStx⟩ else mkIdent `_srvCatchErr
    let catchCtx := pushOptLocal aCtx binderStx
    let okTerm ← recAsync (pushOptLocal aCtx xStx) rest
    let (scrutTerm, steps, awaitCall?) : Term × Array HoistedStep × Option (Term × Ident) ←
      if rhsStx.getKind == ``qedAwait then
        let (callTerm, steps) ← lowerExprCollectingHoists aCtx .val (rhsStx.getArg 1)
        let rawId ← freshIdent "_catchAw"
        pure ((⟨rawId⟩ : Term), steps, some (callTerm, rawId))
      else
        let (rhsTerm, steps) ← lowerExprCollectingHoists aCtx .val rhsStx
        pure (rhsTerm, steps, none)
    let innerTerm ← lowerCatchBody stmt catchCtx xStx errId scrutTerm okTerm catchStmts
      (fun x v c => liftM <| bindOptIdent x v c) recAsync
    let awaitedTerm ← match awaitCall? with
      | some (callTerm, rawId) => `($callTerm >>= fun $rawId:ident => $innerTerm)
      | none                   => pure innerTerm
    wrapHoistsAsync aCtx steps awaitedTerm
  else
    let (rhsTerm, steps) ← lowerExprCollectingHoists aCtx .val rhsRaw
    let checkedRhs ← if steps.isEmpty then `(srvRejectUnhandledErr($rhsTerm)) else pure rhsTerm
    let cont ← recAsync (pushOptLocal aCtx xStx) rest
    wrapHoistsAsync aCtx steps (← liftM <| bindOptIdent xStx checkedRhs cont)

open Lean Elab Command in
private def lowerSetCookieCall (ctx : LowerCtx) (stmt : Syntax) (isClear : Bool) (rawArgs : Array Syntax) :
    LowerM (Term × Array HoistedStep) := do
  let mut posArgs : Array Syntax := #[]
  let mut namedArgs : Array (String × Syntax) := #[]
  for a in rawArgs do
    let k := a.getKind
    if k == ``qedCallArgPos then posArgs := posArgs.push (a.getArg 0)
    else if k == ``qedCallArgNamed then
      namedArgs := namedArgs.push ((a.getArg 0).getId.eraseMacroScopes.toString, a.getArg 2)
    else throwErrorAt a "unexpected argument in `setCookie`/`clearCookie`"
  let findN (k : String) : Option Syntax := (namedArgs.find? (·.1 == k)).map Prod.snd
  let mut allSteps : Array HoistedStep := #[]
  if isClear then
    let some nameStx := posArgs[0]? |>.orElse (fun _ => findN "name")
      | throwErrorAt stmt "`clearCookie(name[, path = \"/\"])` requires a cookie name"
    let (nameT, s1) ← lowerExprCollectingHoists ctx .val nameStx
    allSteps := allSteps ++ s1
    let pathT ← match findN "path" |>.orElse (fun _ => posArgs[1]?) with
      | some pStx =>
          let (pt, s2) ← lowerExprCollectingHoists ctx .val pStx
          allSteps := allSteps ++ s2
          pure pt
      | none => liftM (show CommandElabM Term from `("/"))
    return (← liftM (show CommandElabM Term from `(Qed.Server.SetCookie.clear $nameT $pathT)), allSteps)
  else
    let validCookieKeys : List String := ["name", "value", "path", "httpOnly", "secure", "sameSite", "maxAge", "domain"]
    for (k, _) in namedArgs do
      unless validCookieKeys.contains k do
        let hint := Qed.Diag.didYouMean k validCookieKeys
        throwErrorAt stmt s!"unknown argument `{k}` in `setCookie(...)`{hint} (supported: {String.intercalate ", " validCookieKeys})"
    let some nameStx := posArgs[0]? |>.orElse (fun _ => findN "name")
      | throwErrorAt stmt "`setCookie(name, value, ...)` requires a cookie name"
    let some valStx := posArgs[1]? |>.orElse (fun _ => findN "value")
      | throwErrorAt stmt "`setCookie(name, value, ...)` requires a cookie value"
    let (nameT, s1) ← lowerExprCollectingHoists ctx .val nameStx
    let (valT, s2) ← lowerExprCollectingHoists ctx .val valStx
    allSteps := allSteps ++ s1 ++ s2
    let pathT ← match findN "path" with
      | some s => let (t, hs) ← lowerExprCollectingHoists ctx .val s; allSteps := allSteps ++ hs; pure t
      | none   => liftM (show CommandElabM Term from `("/"))
    let httpOnlyT ← match findN "httpOnly" with
      | some s => let (t, hs) ← lowerExprCollectingHoists ctx .val s; allSteps := allSteps ++ hs; pure t
      | none   => liftM (show CommandElabM Term from `(true))
    let secureT ← match findN "secure" with
      | some s => let (t, hs) ← lowerExprCollectingHoists ctx .val s; allSteps := allSteps ++ hs; pure t
      | none   => liftM (show CommandElabM Term from `(false))
    let sameSiteT ← match findN "sameSite" with
      | some s => let (t, hs) ← lowerExprCollectingHoists ctx .val s; allSteps := allSteps ++ hs; pure t
      | none   => liftM (show CommandElabM Term from `(Qed.Server.SameSite.lax))
    let maxAgeT ← match findN "maxAge" with
      | some s =>
          let (t, hs) ← lowerExprCollectingHoists ctx .val s
          allSteps := allSteps ++ hs
          liftM (show CommandElabM Term from `(some ($t : Nat)))
      | none => liftM (show CommandElabM Term from `(none))
    let domT ← match findN "domain" with
      | some s =>
          let (t, hs) ← lowerExprCollectingHoists ctx .val s
          allSteps := allSteps ++ hs
          liftM (show CommandElabM Term from `(some ($t : String)))
      | none => liftM (show CommandElabM Term from `(none))
    let cTerm ← liftM (show CommandElabM Term from `({
      name := $nameT, value := $valT, path := $pathT,
      httpOnly := $httpOnlyT, sameSite := ($sameSiteT : Qed.Server.SameSite),
      secure := $secureT, maxAge? := $maxAgeT, domain? := $domT
      : Qed.Server.SetCookie }))
    return (cTerm, allSteps)

open Lean Elab Command in
private def lowerSseSendCall (ctx : LowerCtx) (stmt : Syntax) (rawArgs : Array Syntax) :
    LowerM (Term × Array HoistedStep) := do
  unless ctx.isStreamRoute do
    throwErrorAt stmt "`send(...)` is only available inside `stream \"/...\":` routes"
  let mut posArgs : Array Syntax := #[]
  let mut namedArgs : Array (String × Syntax) := #[]
  for a in rawArgs do
    let k := a.getKind
    if k == ``qedCallArgPos then posArgs := posArgs.push (a.getArg 0)
    else if k == ``qedCallArgNamed then
      namedArgs := namedArgs.push ((a.getArg 0).getId.eraseMacroScopes.toString, a.getArg 2)
    else throwErrorAt a "unexpected argument in `send(...)`"
  let validKeys : List String := ["data", "event", "id", "retry"]
  for (k, _) in namedArgs do
    unless validKeys.contains k do
      let hint := Qed.Diag.didYouMean k validKeys
      throwErrorAt stmt s!"unknown argument `{k}` in `send(...)`{hint} (supported: {String.intercalate ", " validKeys})"
  let findN (k : String) : Option Syntax := (namedArgs.find? (·.1 == k)).map Prod.snd
  let some dataStx := posArgs[0]? |>.orElse (fun _ => findN "data")
    | throwErrorAt stmt "`send(data[, event = ..., id = ..., retry = ...])` requires an event data string"
  if posArgs.size > 1 then
    throwErrorAt stmt "`send(...)` takes one positional `data` argument; pass `event = ...`, `id = ...`, or `retry = ...` as named arguments"
  let mut allSteps : Array HoistedStep := #[]
  let (dataT, s1) ← lowerExprCollectingHoists ctx .val dataStx
  allSteps := allSteps ++ s1
  let eventT ← match findN "event" with
    | some s =>
        let (t, hs) ← lowerExprCollectingHoists ctx .val s
        allSteps := allSteps ++ hs
        liftM (show CommandElabM Term from `(some ($t : String)))
    | none => liftM (show CommandElabM Term from `(none))
  let idT ← match findN "id" with
    | some s =>
        let (t, hs) ← lowerExprCollectingHoists ctx .val s
        allSteps := allSteps ++ hs
        liftM (show CommandElabM Term from `(some ($t : String)))
    | none => liftM (show CommandElabM Term from `(none))
  let retryT ← match findN "retry" with
    | some s =>
        let (t, hs) ← lowerExprCollectingHoists ctx .val s
        allSteps := allSteps ++ hs
        liftM (show CommandElabM Term from `(some ($t : Nat)))
    | none => liftM (show CommandElabM Term from `(none))
  let evTerm ← liftM (show CommandElabM Term from `({
    data := $dataT, event := $eventT, id := $idT, retry := $retryT
    : Qed.Server.SseEvent }))
  return (evTerm, allSteps)

open Lean Elab Command in
private def lowerTxStmt (aCtx : LowerCtx) (stmt aliasRef : Syntax) (aliasName : String)
    (txStmts rest : Array Syntax)
    (recAsync : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let some (_, dbInfo) := aCtx.dbs.find? (·.1 == aliasName)
    | let avail := String.intercalate ", " (aCtx.dbs.toList.map Prod.fst)
      throwErrorAt aliasRef s!"unknown database alias `{aliasName}` in `transaction` (declared `use` databases: [{avail}])"
  if let some (curAlias, _) := aCtx.activeDbTx? then
    throwErrorAt stmt s!"nested database transactions are not supported (already inside `{curAlias}.transaction:`)"
  let txId ← freshIdent "_dbTxId"
  let cfgId := mkIdentFrom aliasRef dbInfo.configConst
  let txCtx := { aCtx with activeDbTx? := some (aliasName, txId) }
  let bodyTerm ← recAsync txCtx txStmts
  let txRun ← `(Qed.Server.dbRunTx $cfgId (fun ($txId:ident : UInt64) => $bodyTerm))
  modify fun s => { s with dbWrite := true }
  if rest.isEmpty || blockAlwaysReturns txStmts then
    return txRun
  else
    let cont ← recAsync aCtx rest
    `(Qed.Server.srvSeqM $txRun (fun _ => $cont))

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
  let recAsync := fun c st => lowerAsyncBlock c stateTyTerm? st
  let lowerAsyncBranch (thenCtx : LowerCtx) (thenStmts : Array Syntax)
      (elseStmts? : Option (Array Syntax)) (mkBranch : Term → Term → CommandElabM Term) : LowerM Term :=
    lowerBranchCore rest thenCtx aCtx thenStmts elseStmts?
      recAsync `(Pure.pure none) mkBranch
      fun br => do
        let cont ← recAsync aCtx rest
        `(Qed.Server.srvSeqM $br (fun _ => $cont))
  if k == ``qedStmtPass then
    recAsync aCtx rest
  else if let some (chId, rawArgs) := matchSrvEmitStmt? stmt then
    let (emitTerm, steps) ← lowerEmitCall aCtx stmt chId rawArgs
    let evId ← freshIdent "_wsEv"
    let cont ← recAsync aCtx rest
    let body ← `(let $evId:ident := $emitTerm;
      Qed.Server.MonadServer.wsBroadcast ($evId).topic ($evId).payload >>= fun _ => $cont)
    wrapHoistsAsync aCtx steps body
  else if let some (isClear, rawArgs) := matchSetCookieStmt? stmt then
    let (cookieTerm, steps) ← lowerSetCookieCall aCtx stmt isClear rawArgs
    let cont ← recAsync aCtx rest
    let body ← `(Qed.Server.MonadServer.setCookie $cookieTerm >>= fun _ => $cont)
    wrapHoistsAsync aCtx steps body
  else if let some rawArgs := matchSseSendStmt? stmt then
    let (evTerm, steps) ← lowerSseSendCall aCtx stmt rawArgs
    let cont ← recAsync aCtx rest
    let body ← `(Qed.Server.MonadServer.sendSse $evTerm >>= fun _ => $cont)
    wrapHoistsAsync aCtx steps body
  else if let some (aliasRef, aliasName, txStmts) := matchTxStmt? stmt then
    lowerTxStmt aCtx stmt aliasRef aliasName txStmts rest recAsync
  else if k == ``qedStmtAtomic then
    lowerAtomicStmt aCtx stateTyTerm? stmt rest recAsync
  else if k == ``qedStmtReturn then
    lowerAsyncReturn aCtx stmt
  else if k == ``qedStmtLet then
    lowerAsyncLet aCtx stmt rest recAsync
  else if k == ``qedStmtAssign then
    rejectSrvAssignPredict stmt
    let _ ← parseLValPath aCtx (stmt.getArg 0)
    throwErrorAt stmt s!"cannot mutate server state outside an `atomic:` block in `{ctx.fnName}` because `{ctx.fnName}` uses `await`"
  else if k == ``qedStmtExpr then
    let eStx := stmt.getArg 0
    if let some (targetStx, _) := matchPushCall? eStx then
      let _ ← parseLValPath aCtx targetStx
      throwErrorAt stmt s!"cannot call `.push(...)` on server state outside an `atomic:` block in `{ctx.fnName}` because `{ctx.fnName}` uses `await`"
    else
      let (eTerm, steps) ← lowerExprCollectingHoists aCtx .val eStx
      let cont ← recAsync aCtx rest
      let body ← if isBareUnwrapExpr true eStx then `(let _ := $eTerm; $cont) else `(let _ : Unit := srvEnsureUnit($eTerm); $cont)
      wrapHoistsAsync aCtx steps body
  else if k == ``qedStmtIf then
    let (condTerm, steps) ← lowerExprCollectingHoists aCtx .propGuard (stmt.getArg 1)
    let hGuard ← freshIdent "_srvG"
    let br ← lowerAsyncBranch aCtx (suiteStmts (stmt.getArg 3)) (desugarElifs (stmt.getArg 4).getArgs (stmt.getArg 5))
      fun t e => `(if $hGuard:ident : $condTerm then $t else $e)
    wrapHoistsAsync aCtx steps br
  else if k == ``qedStmtIfLet then
    let patStx := stmt.getArg 2
    let patTerm ← liftMacroM (lowerQedPat patStx)
    let patIds := (collectQedPatIds patStx).map (·.toString)
    let (scrutTerm, steps) ← lowerExprCollectingHoists aCtx .val (stmt.getArg 4)
    let thenCtx := { aCtx with locals := aCtx.locals ++ patIds }
    let hMatch ← freshIdent "_srvM"
    let br ← lowerAsyncBranch thenCtx (suiteStmts (stmt.getArg 6)) (extractElseSuite (stmt.getArg 7))
      fun t e => `(match $hMatch:ident : $scrutTerm:term with | $patTerm => $t | _ => $e)
    wrapHoistsAsync aCtx steps br
  else if k == ``qedStmtMatch then
    let (matchT, allSteps) ← lowerMatchScrutineesAndAlts aCtx stmt rest recAsync
    wrapHoistsAsync aCtx allSteps matchT
  else
    let sn := stxSnippet stmt
    let what := if sn.isEmpty then s!"({k})" else s!" `{sn}`"
    throwErrorAt stmt s!"unsupported statement{what} in async server function `{ctx.fnName}`"


end Qed.Server
