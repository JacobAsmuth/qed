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
  title         : String
deriving Inhabited, Repr

initialize fullstackRegistry :
    Lean.SimplePersistentEnvExtension FullstackInfo (Lean.NameMap FullstackInfo) ←
  Qed.Diag.mkNameMapExt (·.fullstackName)

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
  fnName           : String
  stateFields      : Array String := #[]
  envVars          : Array String := #[]
  locals           : Array String := #[]
  stateRule        : StateAccessRule := .statelessServer
  allowAwait       : Bool := false
  allowUnwrap      : Bool := false
  hasFallible      : Bool := false
  innerOptTy?      : Option Lean.Term := none
  forbidCtxEnv     : Bool := false
  domainErrTy?     : Option Lean.Term := none
  channels         : Array SrvChanSig := #[]
  emitAcc?         : Option Lean.Ident := none
  wrapReturnSumInl : Bool := false
  dbs              : Array (String × DatabaseInfo) := #[]
  activeDbTx?      : Option (String × Lean.Ident) := none
  isHttpRoute      : Bool := false
  isStreamRoute    : Bool := false

inductive HoistedStep where
  | awaitUnwrap (ref : Lean.Syntax) (tmp : Lean.Ident) (callTerm : Lean.Term)
  | pureUnwrap  (tmp : Lean.Ident) (valTerm : Lean.Term)

structure LowerState where
  nextId       : Nat := 0
  mutated      : Array String := #[]
  dbWrite      : Bool := false
  extRoots     : Array Lean.Name := #[]
  hoisted      : Array HoistedStep := #[]

abbrev LowerM := StateRefT LowerState Lean.Elab.Command.CommandElabM

private def freshIdent (prefixStr : String) : LowerM Lean.Ident := do
  let st ← get
  modify fun s => { s with nextId := s.nextId + 1 }
  return Lean.mkIdent (Lean.Name.mkSimple s!"{prefixStr}{st.nextId}")

private def recordMutated (f : String) : LowerM Unit :=
  modify fun s => { s with mutated := pushUnique s.mutated f }

private def recordExtRoot (n : Lean.Name) : LowerM Unit :=
  modify fun s => { s with extRoots := pushUnique s.extRoots n }

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

private def matchNamedStmtCall? (stx : Lean.Syntax) : Option (String × Array Lean.Syntax) := do
  guard (stx.getKind == ``qedStmtExpr)
  let e := unwrapParens1 (stx.getArg 0)
  guard (e.getKind == ``qedCall)
  match extractDottedChain? (e.getArg 0) with
  | some [nm] => some (nm, (e.getArg 2).getSepArgs)
  | _ => none

/-- Matches `setCookie(...)` or `clearCookie(...)`. Returns `(isClear, rawArgs)`. -/
private def matchSetCookieStmt? (stx : Lean.Syntax) : Option (Bool × Array Lean.Syntax) :=
  match matchNamedStmtCall? stx with
  | some ("setCookie", args)   => some (false, args)
  | some ("clearCookie", args) => some (true, args)
  | _ => none

/-- Matches `send(...)` SSE event emission statements inside `stream` routes. -/
private def matchSseSendStmt? (stx : Lean.Syntax) : Option (Array Lean.Syntax) :=
  match matchNamedStmtCall? stx with
  | some ("send", args) => some args
  | _ => none

private def matchSrvEmitStmt? (stx : Lean.Syntax) : Option (Lean.Ident × Array Lean.Syntax) := do
  guard (stx.getKind == ``qedStmtExpr)
  let (chId, meth, rawArgs) ← matchIdentMethodCall? (stx.getArg 0)
  guard (meth == "emit")
  return (chId, rawArgs)

private def blockHas (p : Lean.Syntax → Bool) (stmts : Array Lean.Syntax) : Bool :=
  stmts.any (stxAny p)

def exprHasAwait (stx : Lean.Syntax) : Bool :=
  stxAny (·.getKind == ``qedAwait) stx

def blockHasAwait (stmts : Array Lean.Syntax) : Bool :=
  blockHas (fun s =>
    s.getKind == ``qedAwait || (matchTxStmt? s).isSome ||
    (matchSetCookieStmt? s).isSome || (matchSseSendStmt? s).isSome) stmts

def blockHasEmit (stmts : Array Lean.Syntax) : Bool :=
  blockHas (fun s => (matchSrvEmitStmt? s).isSome) stmts

def blockHasAtomic (stmts : Array Lean.Syntax) : Bool :=
  blockHas (·.getKind == ``qedStmtAtomic) stmts

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

def ensureUnitReturn (ref : Lean.Syntax) (stmts : Array Lean.Syntax) : Array Lean.Syntax :=
  if blockAlwaysReturns stmts then stmts
  else
    let info := Lean.SourceInfo.fromRef ref
    stmts.push (Lean.Syntax.node info ``qedStmtReturn #[Lean.Syntax.atom info "return", Lean.Syntax.node info Lean.nullKind #[]])

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

section ExprLowering
open Lean Elab Command

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

private def checkStateRead (ref : Syntax) (ctx : LowerCtx) (field : String) : LowerM Ident := do
  match ctx.stateRule with
  | .pureStep sv _ => return sv
  | .invariantProp curV oldV inOld => return if inOld then oldV else curV
  | .forbidAsyncOutsideAtomic =>
      throwErrorAt ref s!"cannot access server state `{field}` outside an `atomic` block in `{ctx.fnName}` because `{ctx.fnName}` uses `await` (prevents TOCTOU data races across suspension points)"
  | .forbidInRequires =>
      throwErrorAt ref s!"`requires` precondition in `{ctx.fnName}` cannot reference mutable server state `{field}`; check `{field}` inside the function body instead"
  | .forbidInEnsures =>
      throwErrorAt ref s!"`ensures` postcondition in `{ctx.fnName}` cannot reference mutable server state `{field}`; state postconditions on `result` and parameters only"
  | .statelessServer =>
      throwErrorAt ref s!"unknown identifier `{field}`"

private def resolveStateFieldBase (ref : Syntax) (ctx : LowerCtx) (field : Name) : LowerM Term := do
  let sv ← checkStateRead ref ctx field.toString
  if let .pureStep _ ovs := ctx.stateRule then
    if let some (_, ovId) := ovs.find? (·.1 == field.toString) then
      return ⟨mkIdentFrom ref ovId.getId⟩
  `(($sv).$(mkIdentFrom ref field):ident)

private def resolveDottedIdent (ref : Syntax) (ctx : LowerCtx) (id : Ident) : LowerM Term := do
  match id.getId.components with
  | [] => throwErrorAt ref "empty identifier"
  | root :: rest =>
      let rStr := root.toString
      if rest.isEmpty && rStr == "true" then `(true)
      else if rest.isEmpty && rStr == "false" then `(false)
      else if rest.isEmpty && rStr == "none" then `(none)
      else if ctx.locals.contains rStr then
        foldProjTerms ref ⟨mkIdentFrom ref root⟩ rest
      else if rStr == "ctx" || ctx.envVars.contains rStr then
        if ctx.forbidCtxEnv then
          let what := if rest.isEmpty && rStr != "ctx" then s!"`env` binding `{rStr}`" else s!"`{rStr}`"
          throwErrorAt ref s!"`ensures` postcondition in `{ctx.fnName}` cannot reference {what} because client decoders re-verify `ensures` on the wire"
        foldProjTerms ref ⟨mkIdentFrom ref root⟩ rest
      else if ctx.stateFields.contains rStr then
        let base ← resolveStateFieldBase ref ctx root
        foldProjTerms ref base rest
      else
        if !rest.isEmpty then recordExtRoot root
        return ⟨id⟩

private def checkAllowUnwrap (ref : Syntax) (ctx : LowerCtx)
    (msg : String := s!"operator `?` cannot be used here in `{ctx.fnName}` (return type must be `T!` or `T?`, and `?` cannot appear inside lambdas or invariants)") :
    CommandElabM Unit := do
  unless ctx.allowUnwrap do throwErrorAt ref msg

private def hoistPureUnwraps (ref : Syntax) (ctx : LowerCtx) (qCount : Nat) (term0 : Term) : LowerM Term := do
  if qCount == 0 then return term0
  liftM <| checkAllowUnwrap ref ctx
  let mut term := term0
  for _ in [0:qCount] do
    let tmp ← freshIdent "_srvUnw"
    modify fun s => { s with hoisted := s.hoisted.push (.pureUnwrap tmp term) }
    term := ⟨tmp⟩
  return term

private abbrev SrvExprM := ReaderT LowerCtx LowerM

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

private def lowerSrvCallHook (stx calleeStx : Syntax) (rawArgs : Array Syntax) (mode : ExprMode)
    (go : ExprMode → Syntax → SrvExprM Term) : SrvExprM (Option Term) := do
  let ctx ← read
  if !ctx.dbs.isEmpty then
    if let some chain := extractDottedChain? calleeStx then
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
      let (posArgs, namedArgs) ← splitCallArgs fnName rawArgs (some ["status"])
      let stT ← match findNamedArg? namedArgs "status" with
        | some s => go .val s
        | none   => liftM (show CommandElabM Term from `(($(quote (if fnName == "redirect" then 302 else 200)) : Nat)))
      if fnName == "bytes" then
        if posArgs.size != 2 then
          throwErrorAt stx "`bytes(contentType, body[, status = 200])` expects a content type and body"
        return some (← `(Qed.Server.HttpResponse.bytes $(← go .val posArgs[0]!) $(← go .val posArgs[1]!) $stT))
      if posArgs.size != 1 then
        throwErrorAt stx s!"`{fnName}(...)` expects one positional argument (and optional `status = ...`)"
      let argT ← if fnName == "json" then lowerJsonPayload go posArgs[0]! else go .val posArgs[0]!
      let ctor := mkIdent <| match fnName with
        | "text" => `Qed.Server.HttpResponse.text | "json" => `Qed.Server.HttpResponse.jsonOf
        | "html" => `Qed.Server.HttpResponse.html | _ => `Qed.Server.HttpResponse.redirect
      return some (← `($ctor $argT $stT))
  return none

private def checkAllowAwait (ref : Syntax) : SrvExprM Unit := do
  unless (← read).allowAwait do
    throwErrorAt ref "`await` cannot be used inside an `atomic` block, lambda, `requires`, or `invariant`; perform external I/O outside `atomic`"

private def hoistAwaitUnwrap (recGo : ExprMode → Syntax → SrvExprM Term)
    (stx awaitRef callStx : Syntax) (mode : ExprMode) : SrvExprM Term := do
  checkAllowAwait awaitRef
  let callTerm ← recGo .val callStx
  let tmp ← liftM <| freshIdent "_srvAw"
  modify fun s => { s with hoisted := s.hoisted.push (.awaitUnwrap stx tmp callTerm) }
  liftMacroM (finishTermMode mode ⟨tmp⟩)

private def lowerSrvUnwrapHook (recGo : ExprMode → Syntax → SrvExprM Term)
    (stx innerRaw : Syntax) (mode : ExprMode) : SrvExprM Term := do
  let ctx ← read
  liftM <| checkAllowUnwrap stx ctx
  let inner := unwrapParens1 innerRaw
  if inner.getKind == ``qedAwait then
    hoistAwaitUnwrap recGo stx inner (inner.getArg 1) mode
  else
    let term ← liftM <| hoistPureUnwraps stx ctx 1 (← recGo .val innerRaw)
    liftMacroM (finishTermMode mode term)

private def lowerSrvAwaitHook (recGo : ExprMode → Syntax → SrvExprM Term)
    (stx argRaw : Syntax) (mode : ExprMode) : SrvExprM Term := do
  checkAllowAwait stx
  let inner := unwrapParens1 argRaw
  if inner.getKind == ``qedUnwrap then
    let ctx ← read
    liftM <| checkAllowUnwrap stx ctx
      s!"operator `?` cannot be used in `{ctx.fnName}` because its return type is neither fallible (`T!`) nor optional (`T?`); handle the `await` error with `let x = await ... catch err:`"
    hoistAwaitUnwrap recGo stx stx (inner.getArg 0) mode
  else
    throwErrorAt stx "unhandled fallible `await` expression; append `?` to propagate errors or use `let x = await ... catch err:` to handle them inline"

private def mkSrvLowerHooks (recGo : ExprMode → Syntax → SrvExprM Term) : LowerHooks SrvExprM :=
  { LowerHooks.mkDefault (fun ref msg => throwErrorAt ref msg) with
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
      liftMacroM (finishTermMode mode (← `(srvGetElem($arrT, $idxT))))
    lowerCall := lowerSrvCallHook
    lowerUnwrap := lowerSrvUnwrapHook recGo
    lowerAwait := lowerSrvAwaitHook recGo
    lowerArrElem := fun t => `(srvAutoField($t))
    wrapNamedField := fun t => `(srvAutoField($t))
    lowerType := fun t => liftMacroM (return (← lowerQedType t false).1)
    lowerPat := fun p => liftMacroM (lowerQedPat p)
    withLocals := fun names k =>
      withReader (fun c => { c with locals := c.locals ++ names, allowAwait := false, allowUnwrap := false }) k
    useDirectArray := true
    freshIdent := fun pfx => liftM <| freshIdent pfx }

private partial def lowerExprM (mode : ExprMode) (stx : Syntax) : SrvExprM Term :=
  lowerQedExpr (mkSrvLowerHooks lowerExprM) mode stx

def lowerExpr (ctx : LowerCtx) (mode : ExprMode) (stx : Syntax) : LowerM Term :=
  (lowerExprM mode stx).run ctx

private def withCollectedHoists {α : Type} (act : LowerM α) : LowerM (α × Array HoistedStep) := do
  let saved := (← get).hoisted
  modify fun s => { s with hoisted := #[] }
  let res ← act
  let steps := (← get).hoisted
  modify fun s => { s with hoisted := saved }
  return (res, steps)

private def lowerExprCollectingHoists (ctx : LowerCtx) (mode : ExprMode) (stx : Syntax) :
    LowerM (Term × Array HoistedStep) :=
  withCollectedHoists (lowerExpr ctx mode stx)

/-! ## LValue Mutation Path Parsing & Functional Lens Construction -/

private inductive LValStep where
  | field (id : Lean.Ident)
  | index (idxTerm : Lean.Term)

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

private def getPureOverrides (ctx : LowerCtx) : Array (String × Ident) :=
  match ctx.stateRule with
  | .pureStep _ ovs => ovs
  | _ => #[]

private def setPureOverride (ctx : LowerCtx) (sCur : Ident) (fld : String) (vId : Ident) : LowerCtx :=
  let ovs := (getPureOverrides ctx).filter (·.1 != fld)
  { ctx with stateRule := .pureStep sCur (ovs.push (fld, vId)) }

private def materializeState (sCur : Ident) (overrides : Array (String × Ident)) : CommandElabM Term := do
  if overrides.isEmpty then
    `(($sCur))
  else
    let fIds : Array Ident := overrides.map fun p => mkIdent (Name.mkSimple p.1)
    let fVars : Array Term := overrides.map fun p => ⟨p.2.raw⟩
    `({ $sCur with $[$fIds:ident := $fVars:term],* })

/-! ## Return Value Auto-Lifting & Hoist Wrapping -/

private def isFailCall (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx
  u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId == `fail

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

private def errTyOf (ctx : LowerCtx) : CommandElabM Term :=
  match ctx.domainErrTy? with
  | some et => `(Qed.Server.SrvFailure $et)
  | none    => `(Qed.Server.ApiError)

private def mkPureLeaf (ctx : LowerCtx) (stTerm optTerm : Term) : CommandElabM Term :=
  match ctx.emitAcc? with
  | some esId => `(($stTerm, $esId, $optTerm))
  | none      => `(($stTerm, $optTerm))

private def mkPureErrLeaf (ctx : LowerCtx) (s₀ : Ident) (errTerm : Term) : CommandElabM Term :=
  match ctx.emitAcc? with
  | some _ => `(($s₀, ([] : List Qed.Server.WsEmit), some (Except.error $errTerm)))
  | none   => `(($s₀, some (Except.error $errTerm)))

private def lowerEmitCall (ctx : LowerCtx) (stmt : Syntax) (chId : Ident) (rawArgs : Array Syntax) :
    LowerM (Term × Array HoistedStep) := do
  let chanNameStr := chId.getId.eraseMacroScopes.toString
  let some chSig := ctx.channels.find? (·.name == chanNameStr)
    | let avail := String.intercalate ", " (ctx.channels.toList.map (·.name))
      throwErrorAt chId s!"unknown WebSocket `channel` `{chanNameStr}` in `.emit(...)` (declared channels: [{avail}])"
  if rawArgs.size != chSig.paramCount + 1 then
    throwErrorAt stmt s!"`{chanNameStr}.emit(...)` expects {chSig.paramCount + 1} argument(s) ({chSig.paramCount} channel param(s) + 1 event), got {rawArgs.size}"
  let (argTerms, allSteps) ← withCollectedHoists <| rawArgs.mapM fun ra => do
    unless ra.getKind == ``qedCallArgPos do
      throwErrorAt ra s!"named arguments are not supported in `{chanNameStr}.emit(...)`"
    lowerExpr ctx .val (ra.getArg 0)
  let paramTerms := argTerms.extract 0 chSig.paramCount
  let evTerm := argTerms[chSig.paramCount]!
  let mut call ← mkAppTerms (chSig.mkEmitId : Term) paramTerms
  call ← `($call (srvAutoField($evTerm)))
  if chSig.hasEnsures then
    call ← `($call (srvAutoEmit(True)))
  return (call, allSteps)

end ExprLowering

private inductive BlockMode where
  | pure  (inAtomic : Bool) (s₀ sCur : Lean.Ident) (matCur : Lean.Term)
  | async (stateTyTerm? : Option Lean.Term)

section BlockLowering
open Lean Elab Command

private def mkOkLeaf (mode : BlockMode) (ctx : LowerCtx) (valTerm : Term) : CommandElabM Term := do
  let ok ← wrapOkValue ctx valTerm
  match mode with
  | .pure _ _ _ matCur => mkPureLeaf ctx matCur (← `(some $ok))
  | .async _           => `(Pure.pure (some $ok))

private def mkErrLeaf (mode : BlockMode) (ctx : LowerCtx) (errTerm : Term) : CommandElabM Term :=
  match mode with
  | .pure _ s₀ _ _ => mkPureErrLeaf ctx s₀ errTerm
  | .async _       => `(Pure.pure (some (Except.error $errTerm)))

private def mkEmptyLeaf (mode : BlockMode) (ctx : LowerCtx) : CommandElabM Term :=
  match mode with
  | .pure _ _ _ matCur => do mkPureLeaf ctx matCur (← `(none))
  | .async _           => `(Pure.pure none)

private def wrapUnwrapStep (mode : BlockMode) (ctx : LowerCtx) (tmp : Ident) (valTerm acc : Term) :
    CommandElabM Term := do
  if !ctx.hasFallible then
    if let some innerTy := ctx.innerOptTy? then
      match mode with
      | .pure _ s₀ _ matCur =>
          let okNone ← mkPureLeaf ctx matCur (← `(some (Except.ok none)))
          let errLeaf ← mkPureErrLeaf ctx s₀ (← `(_e))
          return ← `(match Qed.Server.SrvUnwrapOpt.unwrapOpt (Inner := $innerTy) $valTerm with
            | Except.error (Except.ok none) => $okNone
            | Except.error (Except.error _e) => $errLeaf
            | Except.ok $tmp:ident => $acc)
      | .async _ =>
          return ← `(match Qed.Server.SrvUnwrapOpt.unwrapOpt (Inner := $innerTy) $valTerm with
            | Except.error _early => Pure.pure (some _early)
            | Except.ok $tmp:ident => $acc)
  let errTy ← errTyOf ctx
  let errLeaf ← mkErrLeaf mode ctx (← `(_e))
  `(match Qed.Server.SrvUnwrap.unwrap (E := $errTy) $valTerm with
    | Except.error _e => $errLeaf
    | Except.ok $tmp:ident => $acc)

private def wrapHoists (mode : BlockMode) (ctx : LowerCtx)
    (steps : Array HoistedStep) (body : Term) : LowerM Term :=
  steps.foldrM (init := body) fun step acc => do
    match step, mode with
    | .awaitUnwrap ref _ _, .pure .. =>
        throwErrorAt ref "`await` cannot appear inside a pure/atomic block"
    | .awaitUnwrap _ tmp callTerm, .async _ =>
        let rawTmp ← freshIdent "_srvRaw"
        `($callTerm >>= fun $rawTmp:ident => $(← liftM <| wrapUnwrapStep mode ctx tmp ⟨rawTmp⟩ acc))
    | .pureUnwrap tmp valTerm, _ =>
        liftM <| wrapUnwrapStep mode ctx tmp valTerm acc

private def bindOptIdent (xStx : Syntax) (val cont : Term) : CommandElabM Term :=
  if xStx.isIdent then
    let xId : Ident := ⟨xStx⟩
    `(let $xId:ident := $val; $cont)
  else
    `(let _ := $val; $cont)

private def bindSrvLetEq (xStx : Syntax) (val cont : Term) : LowerM Term := do
  let xId ← if xStx.isIdent then pure ⟨xStx⟩ else freshIdent "_srvDiscard"
  let hEq ← freshIdent "_srvEq"
  `(Qed.Server.srvLetEq $val (fun $xId:ident $hEq:ident => $cont))

private def bindLet (mode : BlockMode) (xStx : Syntax) (val cont : Term) : LowerM Term :=
  match mode with
  | .pure .. => bindSrvLetEq xStx val cont
  | .async _ => liftM <| bindOptIdent xStx val cont

private def pushOptLocal (ctx : LowerCtx) (xStx : Syntax) : LowerCtx :=
  if xStx.isIdent then { ctx with locals := ctx.locals.push xStx.getId.toString } else ctx

private def isBareUnwrapExpr (allowAwait : Bool) (eStx : Syntax) : Bool :=
  let u := unwrapParens1 eStx
  u.getKind == ``qedUnwrap ||
  (allowAwait && u.getKind == ``qedAwait && (unwrapParens1 (u.getArg 1)).getKind == ``qedUnwrap) ||
  (eStx.getKind == ``qedIdent && (eStx.getArg 0).getId.toString.endsWith "?") ||
  (eStx.getKind == ``qedProj && (eStx.getArg 2).getId.toString.endsWith "?")

/-! ## Unified Pure & Async Statement Block Lowering (`lowerBlock`) -/

private partial def lowerCatchFallback? (ctx : LowerCtx) (stmts : Array Syntax) : LowerM (Option Term) := do
  if stmts.isEmpty then
    return none
  else if stmts.size == 1 && stmts[0]!.getKind == ``qedStmtExpr then
    let eStx := stmts[0]![0]
    if exprHasAwait eStx || exprHasUnwrap eStx || (matchPushCall? eStx).isSome || (matchRemoveCall? eStx).isSome || (matchSrvEmitStmt? stmts[0]!).isSome then return none
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

private def lowerMatchScrutineesAndAlts (ctx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (lowerArm : LowerCtx → Array Syntax → LowerM Term) : LowerM (Term × Array HoistedStep) := do
  let (scrutTerms, allSteps) ← withCollectedHoists <| (stmt.getArg 1).getSepArgs.mapM (lowerExpr ctx .val)
  let cases := (stmt.getArg 3).getArgs
  let allRet := cases.all fun c => blockAlwaysReturns (suiteStmts (c.getArg 3))
  let alts ← cases.mapM fun c => do
    let pats ← (c.getArg 1).getSepArgs.mapM fun p => liftMacroM (lowerQedPat p)
    let pIds := ((c.getArg 1).getSepArgs.flatMap collectQedPatIds).map (·.toString)
    let cBody ← lowerArm { ctx with locals := ctx.locals ++ pIds } (suiteStmts (c.getArg 3) ++ if allRet then #[] else rest)
    `(Lean.Parser.Term.matchAltExpr| | $[$pats:term],* => $cBody)
  return (← `(match $[$scrutTerms:term],* with $[$alts:matchAlt]*), allSteps)

private def extractSrvLetCatch? (clausesNode : Syntax) : LowerM (Option Syntax) := do
  let mut catchOpt? : Option Syntax := none
  for cl in clausesNode.getArgs do
    let ck := cl.getKind
    if ck == `Qed.Lang.letCatch then
      if catchOpt?.isSome then throwErrorAt cl "duplicate `catch` clause on `let`"
      catchOpt? := some (cl.getArg 1)
    else if ck == `Qed.Lang.letPredictBlock || ck == `Qed.Lang.letPredictExpr ||
            ck == `Qed.Lang.letOnConfirm || ck == `Qed.Lang.letRollback then
      throwErrorAt cl "`predict`, `on_confirm`, and `rollback` are only supported on client `component` `await` calls, not in `server` functions"
  return catchOpt?

private def rejectSrvAssignPredict (stmt : Syntax) : LowerM Unit := do
  if stmt.getKind == ``qedStmtAssign && stmt.getNumArgs > 3 && (stmt.getArg 3).getNumArgs > 0 then
    throwErrorAt ((stmt.getArg 3).getArg 0) "`predict` is only supported on client `component` `await` calls, not in `server` functions"

private def lowerCatchBody (stmt : Syntax) (catchCtx : LowerCtx) (xStx : Syntax)
    (errId : Ident) (scrutTerm okTerm : Term) (catchStmts : Array Syntax)
    (bindFallback : Syntax → Term → Term → LowerM Term)
    (lowerCatchBlock : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let mkUnwrapMatch (errBody : Term) (okId : Ident) (okBody : Term) : CommandElabM Term :=
    `(match Qed.Server.SrvUnwrap.unwrap (E := Qed.Server.ApiError) $scrutTerm with
      | Except.error $errId:ident => $errBody | Except.ok $okId:ident => $okBody)
  if let some fbTerm ← lowerCatchFallback? catchCtx catchStmts then
    let okValId ← freshIdent "_catchOk"
    bindFallback xStx (← liftM <| mkUnwrapMatch fbTerm okValId ⟨okValId.raw⟩) okTerm
  else
    unless blockAlwaysReturns catchStmts do
      throwErrorAt stmt "the `catch` block must either `return` on all paths or end with a fallback value expression"
    let bindId : Ident := if xStx.isIdent then ⟨xStx⟩ else mkIdent `_srvDiscard
    liftM <| mkUnwrapMatch (← lowerCatchBlock catchCtx catchStmts) bindId okTerm

private def lowerBranch (mode : BlockMode) (ctx : LowerCtx)
    (rest thenStmts : Array Syntax) (thenCtx : LowerCtx)
    (elseStmts? : Option (Array Syntax)) (allowPureLetJoin : Bool)
    (mkBranch : Term → Term → CommandElabM Term)
    (recSame : LowerCtx → Array Syntax → LowerM Term)
    (recWithState : LowerCtx → Ident → Array Syntax → LowerM Term) : LowerM Term := do
  let thenRet := blockAlwaysReturns thenStmts
  let elseRet := elseStmts?.map blockAlwaysReturns |>.getD false
  let lowerElseOpt (es? : Option (Array Syntax)) : LowerM Term :=
    match es? with
    | some es => recSame ctx es
    | none    => liftM <| mkEmptyLeaf mode ctx
  if rest.isEmpty then
    liftM =<< (mkBranch <$> recSame thenCtx thenStmts <*> lowerElseOpt elseStmts?)
  else if thenRet && !elseRet then
    liftM =<< (mkBranch <$> recSame thenCtx thenStmts <*> recSame ctx ((elseStmts?.getD #[]) ++ rest))
  else if !thenRet && elseRet then
    liftM =<< (mkBranch <$> recSame thenCtx (thenStmts ++ rest) <*> recSame ctx (elseStmts?.getD #[]))
  else
    let br ← liftM =<< (mkBranch <$> recSame thenCtx thenStmts <*> lowerElseOpt elseStmts?)
    match mode with
    | .pure .. =>
        let sNext ← freshIdent "_s"
        let baseJoinCtx := { ctx with stateRule := if ctx.stateFields.isEmpty then .statelessServer else .pureStep sNext #[] }
        match ctx.emitAcc? with
        | some _ =>
            let esNext ← freshIdent "_es"
            let cont ← recWithState { baseJoinCtx with emitAcc? := some esNext } sNext rest
            `(Qed.Server.srvEmitSeq $br (fun $sNext:ident $esNext:ident => $cont))
        | none =>
            let cont ← recWithState baseJoinCtx sNext rest
            if allowPureLetJoin && !blockMayReturnEarly thenStmts && !(elseStmts?.map blockMayReturnEarly |>.getD false) then
              let hJoin ← freshIdent "_srvEq"
              `(Qed.Server.srvLetEq (($br : _ × Option Unit).1) (fun $sNext:ident $hJoin:ident => $cont))
            else
              `(Qed.Server.srvSeq $br (fun $sNext:ident => $cont))
    | .async _ =>
        let cont ← recSame ctx rest
        `(Qed.Server.srvSeqM $br (fun _ => $cont))

private def lowerReturn (mode : BlockMode) (ctx : LowerCtx) (stmt : Syntax) : LowerM Term := do
  if (stmt.getArg 1).getNumArgs == 0 then
    liftM <| mkOkLeaf mode ctx (← `(()))
  else
    let retExpr := (stmt.getArg 1).getArg 0
    let uRet := unwrapParens1 retExpr
    match mode with
    | .pure .. =>
        if exprHasAwait retExpr && !uRet.isOfKind ``qedUnwrap then
          throwErrorAt retExpr "`await` cannot be used inside a synchronous or `atomic` block"
    | .async _ =>
        if uRet.getKind == ``qedAwait && !(unwrapParens1 (uRet.getArg 1)).isOfKind ``qedUnwrap then
          unless ctx.hasFallible do
            throwErrorAt retExpr s!"`return await ...` without `catch` requires `{ctx.fnName}` to have a fallible `T!` return type"
          let (callTerm, steps) ← lowerExprCollectingHoists ctx .val (uRet.getArg 1)
          let rawId ← freshIdent "_retAw"
          let errTy ← liftM <| errTyOf ctx
          let leaf ← match ctx.innerOptTy? with
            | some innerTy =>
                `($callTerm >>= fun $rawId:ident => Pure.pure (some (match $rawId:ident with
                  | Except.ok _v => Except.ok (Qed.Server.SrvLiftOpt.liftOpt (Inner := $innerTy) _v)
                  | Except.error _e => Except.error (Qed.Server.SrvErr.ofApi (E := $errTy) _e))))
            | none =>
                `($callTerm >>= fun $rawId:ident => Pure.pure (some (Qed.Server.SrvUnwrap.unwrap (E := $errTy) $rawId)))
          return ← wrapHoists mode ctx steps leaf
    let isFail := isFailCall retExpr
    if isFail && !ctx.hasFallible then
      throwErrorAt retExpr s!"`fail(...)` can only be returned from a fallible `T!` function (`{ctx.fnName}` is not declared `-> ...!`)"
    let (term, steps) ← lowerExprCollectingHoists ctx .val retExpr
    wrapHoists mode ctx steps (← liftM <| (if isFail then mkErrLeaf else mkOkLeaf) mode ctx term)

private def lowerLet (mode : BlockMode) (ctx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (recBlock : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let xStx := stmt.getArg 1
  let rhsRaw := stmt.getArg 4
  if let some catchNode ← extractSrvLetCatch? (stmt.getArg 5) then
    if catchNode.getKind == `Qed.Lang.catchArms then
      throwErrorAt catchNode "multi-arm `catch: case ...` is for client components; in server functions use `catch err:`"
    let rhsStx := unwrapParens1 rhsRaw
    let binderStx := catchNode.getArg 0
    let catchStmts := suiteStmts (catchNode.getArg 2)
    let errId : Ident := if binderStx.isIdent then ⟨binderStx⟩ else mkIdent `_srvCatchErr
    let catchCtx := pushOptLocal ctx binderStx
    let okTerm ← recBlock (pushOptLocal ctx xStx) rest
    let (scrutTerm, steps, awaitCall?) : Term × Array HoistedStep × Option (Term × Ident) ←
      if rhsStx.getKind == ``qedAwait then
        match mode with
        | .pure .. => throwErrorAt rhsRaw "`await` cannot be used inside a synchronous or `atomic` block"
        | .async _ =>
            let (callTerm, steps) ← lowerExprCollectingHoists ctx .val (rhsStx.getArg 1)
            let rawId ← freshIdent "_catchAw"
            pure ((⟨rawId⟩ : Term), steps, some (callTerm, rawId))
      else
        let (rhsTerm, steps) ← lowerExprCollectingHoists ctx .val rhsStx
        pure (rhsTerm, steps, none)
    let innerTerm ← lowerCatchBody stmt catchCtx xStx errId scrutTerm okTerm catchStmts (bindLet mode) recBlock
    let awaitedTerm ← match awaitCall? with
      | some (callTerm, rawId) => `($callTerm >>= fun $rawId:ident => $innerTerm)
      | none                   => pure innerTerm
    wrapHoists mode ctx steps awaitedTerm
  else
    let (rhsTerm, steps) ← lowerExprCollectingHoists ctx .val rhsRaw
    let checkedRhs ← if steps.isEmpty then `(srvRejectUnhandledErr($rhsTerm)) else pure rhsTerm
    let cont ← recBlock (pushOptLocal ctx xStx) rest
    wrapHoists mode ctx steps (← bindLet mode xStx checkedRhs cont)

private def lowerPureMutationStmt (mode : BlockMode) (pCtx : LowerCtx) (sCur : Ident)
    (stmt : Syntax) (rest : Array Syntax)
    (recPure : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  rejectSrvAssignPredict stmt
  let lowerMut (lvalStx : Syntax) (steps : Array HoistedStep)
      (mkLeaf : Array LValStep → Term → LowerM Term) : LowerM Term := do
    let (rootField, pathSteps) ← parseLValPath pCtx lvalStx
    let curRoot ← resolveStateFieldBase lvalStx pCtx rootField.getId
    let fNext ← freshIdent s!"_fld_{rootField.getId}_"
    let hFNext ← freshIdent "_srvEq"
    let cont ← recPure (setPureOverride pCtx sCur rootField.getId.toString fNext) rest
    let chain ← withUpdatedPathCPS pathSteps 0 curRoot (mkLeaf pathSteps) fun updatedRaw => do
      let updatedRoot ← if pathSteps.isEmpty then `(srvTypedAs(($sCur).$rootField:ident, $updatedRaw)) else pure updatedRaw
      `(Qed.Server.srvLetEq $updatedRoot (fun $fNext:ident $hFNext:ident => $cont))
    wrapHoists mode pCtx steps chain
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
  else if let some (targetStx, elemStx) := matchPushCall? (stmt.getArg 0) then
    let (elemTerm, steps) ← lowerExprCollectingHoists pCtx .val elemStx
    lowerMut targetStx steps fun _ curArr => `(($curArr).push (srvAutoField($elemTerm)))
  else
    let some (targetStx, keyStx) := matchRemoveCall? (stmt.getArg 0) | unreachable!
    let (keyTerm, steps) ← lowerExprCollectingHoists pCtx .val keyStx
    lowerMut targetStx steps fun _ curDict => `(Qed.Dict.remove $curDict $keyTerm)

private def stmtHasNonFailReturn (stx : Syntax) : Bool :=
  stxAny (fun s => s.getKind == ``qedStmtReturn &&
    ((s.getArg 1).getNumArgs == 0 || !isFailCall ((s.getArg 1).getArg 0))) stx

private def collectAtomicExports (atomStmts rest : Array Syntax) : Array Ident := Id.run do
  let mut ids : Array Ident := #[]
  for s in atomStmts do
    if s.getKind == ``qedStmtLet && (s.getArg 1).isIdent then
      let id : Ident := ⟨s.getArg 1⟩
      let nm := id.getId.eraseMacroScopes.toString
      if rest.any (stxMentionsVar nm) then
        ids := ids.filter (·.getId.eraseMacroScopes.toString != nm) |>.push id
  ids

private def lowerScopedAtomicBody (stmt : Syntax) (atomCtx : LowerCtx) (stateTyTerm? : Option Term)
    (atomStmts : Array Syntax)
    (lowerPure : LowerCtx → Ident → Ident → Array Syntax → LowerM Term) :
    LowerM (Term × Ident × Term × Bool × Bool) := do
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
  let rawAtomBody ← lowerPure bodyCtx s0Id s0Id atomStmts
  let atomBody ← if hasEmit then `(let $es0Id:ident : List Qed.Server.WsEmit := []; $rawAtomBody) else pure rawAtomBody
  let atomMut := (← get).mutated
  modify fun s => { s with mutated := savedMut ++ atomMut.filter (!savedMut.contains ·) }
  return (stateTyTerm, s0Id, atomBody, atomMut.isEmpty, hasEmit)

private def emitAtomicRun (s0Id : Ident) (stateTyTerm atomBody : Term)
    (readOnly hasEmit isFinish : Bool) (onResult : Term → LowerM Term) : LowerM Term := do
  let committed ← match isFinish, hasEmit, readOnly with
    | true,  true,  _     => `(Qed.Server.srvFinishEmit $s0Id $atomBody)
    | false, true,  _     => `(Qed.Server.srvAtomicCommitEmit $s0Id $atomBody)
    | true,  false, _     => `(Qed.Server.srvFinish $s0Id $atomBody)
    | false, false, true  => pure atomBody
    | false, false, false => `(Qed.Server.srvAtomicCommit $s0Id $atomBody)
  let runCall ← if readOnly then
      `(Qed.Server.MonadAtomic.runAtomicRead (fun ($s0Id:ident : $stateTyTerm) => ($committed).2))
    else
      `(Qed.Server.MonadAtomic.runAtomic (fun ($s0Id:ident : $stateTyTerm) => $committed))
  if hasEmit then
    let pairId ← freshIdent "_atomPair"
    `($runCall >>= fun $pairId:ident =>
        Qed.Server.flushWsEmits ($pairId).2 >>= fun _ =>
        $(← onResult (← `(($pairId).1))))
  else
    let resId ← freshIdent "_atomRes"
    `($runCall >>= fun $resId:ident => $(← onResult ⟨resId.raw⟩))

private def lowerAtomicStmt (aCtx : LowerCtx) (stateTyTerm? : Option Term)
    (stmt : Syntax) (rest : Array Syntax)
    (lowerPure : LowerCtx → Ident → Ident → Array Syntax → LowerM Term)
    (lowerRest : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let atomStmts := suiteStmts (stmt.getArg 2)
  let alwaysRet := blockAlwaysReturns atomStmts
  let exportedIds := if alwaysRet then #[] else collectAtomicExports atomStmts rest
  let (atomCtx, bodyStmts, isFinish, onResult) :
      (LowerCtx × Array Syntax × Bool × (Term → LowerM Term)) ←
    if alwaysRet then
      pure (aCtx, atomStmts, true, fun res => `(Pure.pure (some $res)))
    else if !exportedIds.isEmpty then
      let hasEarlyOk := atomStmts.any stmtHasNonFailReturn
      let expTuple ← buildTupleVal (exportedIds.map (⟨·.raw⟩))
      let exportStmt := Syntax.node (.fromRef stmt) `Qed.Server.atomicExport #[expTuple.raw]
      let ctx' := if hasEarlyOk then { aCtx with wrapReturnSumInl := true } else { aCtx with innerOptTy? := none }
      pure (ctx', atomStmts.push exportStmt, true, fun res => do
        let cont ← lowerRest { aCtx with locals := aCtx.locals ++ exportedIds.map (·.getId.eraseMacroScopes.toString) } rest
        if hasEarlyOk then
          `(match $res:term with
            | Except.error _e => Pure.pure (some (Except.error _e))
            | Except.ok (Sum.inl _v) => Pure.pure (some (Except.ok _v))
            | Except.ok (Sum.inr $expTuple:term) => $cont)
        else
          `(match $res:term with
            | Except.error _e => Pure.pure (some (Except.error _e))
            | Except.ok $expTuple:term => $cont))
    else
      pure (aCtx, atomStmts, false, fun early => do
        let cont ← lowerRest aCtx rest
        `(match $early:term with | some _r => Pure.pure (some _r) | none => $cont))
  let (stateTyTerm, s0Id, atomBody, readOnly, hasEmit) ← lowerScopedAtomicBody stmt atomCtx stateTyTerm? bodyStmts lowerPure
  emitAtomicRun s0Id stateTyTerm atomBody readOnly hasEmit isFinish onResult

private def lowerOptArg (ctx : LowerCtx) (arg? : Option Syntax)
    (wrap : Term → CommandElabM Term) (default : CommandElabM Term) : LowerM Term := do
  match arg? with
  | some s => liftM (wrap (← lowerExpr ctx .val s))
  | none   => liftM default

private def lowerOptSomeArg (ctx : LowerCtx) (namedArgs : Array (String × Syntax))
    (k : String) (ty : CommandElabM Term) : LowerM Term :=
  lowerOptArg ctx (findNamedArg? namedArgs k) (fun t => do `(some ($t : $(← ty)))) `(none)

private def lowerSetCookieCall (ctx : LowerCtx) (stmt : Syntax) (isClear : Bool) (rawArgs : Array Syntax) :
    LowerM (Term × Array HoistedStep) := withCollectedHoists do
  let validKeys := if isClear then none else some ["name", "value", "path", "httpOnly", "secure", "sameSite", "maxAge", "domain"]
  let (posArgs, namedArgs) ← splitCallArgs (if isClear then "clearCookie" else "setCookie") rawArgs validKeys (errRef := stmt)
  let findN := findNamedArg? namedArgs
  let optVal (k : String) (d : CommandElabM Term) : LowerM Term := lowerOptArg ctx (findN k) pure d
  if isClear then
    let some nameStx := posArgs[0]? |>.orElse (fun _ => findN "name")
      | throwErrorAt stmt "`clearCookie(name[, path = \"/\"])` requires a cookie name"
    `(Qed.Server.SetCookie.clear $(← lowerExpr ctx .val nameStx)
        $(← lowerOptArg ctx ((findN "path").orElse (fun _ => posArgs[1]?)) pure `("/")))
  else
    let some nameStx := posArgs[0]? |>.orElse (fun _ => findN "name")
      | throwErrorAt stmt "`setCookie(name, value, ...)` requires a cookie name"
    let some valStx := posArgs[1]? |>.orElse (fun _ => findN "value")
      | throwErrorAt stmt "`setCookie(name, value, ...)` requires a cookie value"
    `({
      name := $(← lowerExpr ctx .val nameStx), value := $(← lowerExpr ctx .val valStx),
      path := $(← optVal "path" `("/")), httpOnly := $(← optVal "httpOnly" `(true)),
      sameSite := ($(← optVal "sameSite" `(Qed.Server.SameSite.lax)) : Qed.Server.SameSite),
      secure := $(← optVal "secure" `(false)),
      maxAge? := $(← lowerOptSomeArg ctx namedArgs "maxAge" `(Nat)),
      domain? := $(← lowerOptSomeArg ctx namedArgs "domain" `(String))
      : Qed.Server.SetCookie })

private def lowerSseSendCall (ctx : LowerCtx) (stmt : Syntax) (rawArgs : Array Syntax) :
    LowerM (Term × Array HoistedStep) := withCollectedHoists do
  unless ctx.isStreamRoute do
    throwErrorAt stmt "`send(...)` is only available inside `stream \"/...\":` routes"
  let (posArgs, namedArgs) ← splitCallArgs "send" rawArgs (some ["data", "event", "id", "retry"]) (errRef := stmt)
  let some dataStx := posArgs[0]? |>.orElse (fun _ => findNamedArg? namedArgs "data")
    | throwErrorAt stmt "`send(data[, event = ..., id = ..., retry = ...])` requires an event data string"
  if posArgs.size > 1 then
    throwErrorAt stmt "`send(...)` takes one positional `data` argument; pass `event = ...`, `id = ...`, or `retry = ...` as named arguments"
  `({
    data := $(← lowerExpr ctx .val dataStx),
    event := $(← lowerOptSomeArg ctx namedArgs "event" `(String)),
    id := $(← lowerOptSomeArg ctx namedArgs "id" `(String)),
    retry := $(← lowerOptSomeArg ctx namedArgs "retry" `(Nat))
    : Qed.Server.SseEvent })

private def lowerTxStmt (aCtx : LowerCtx) (stmt aliasRef : Syntax) (aliasName : String)
    (txStmts rest : Array Syntax) (recAsync : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let some (_, dbInfo) := aCtx.dbs.find? (·.1 == aliasName)
    | let avail := String.intercalate ", " (aCtx.dbs.toList.map Prod.fst)
      throwErrorAt aliasRef s!"unknown database alias `{aliasName}` in `transaction` (declared `use` databases: [{avail}])"
  if let some (curAlias, _) := aCtx.activeDbTx? then
    throwErrorAt stmt s!"nested database transactions are not supported (already inside `{curAlias}.transaction:`)"
  let txId ← freshIdent "_dbTxId"
  let cfgId := mkIdentFrom aliasRef dbInfo.configConst
  let bodyTerm ← recAsync { aCtx with activeDbTx? := some (aliasName, txId) } txStmts
  let txRun ← `(Qed.Server.dbRunTx $cfgId (fun ($txId:ident : UInt64) => $bodyTerm))
  modify fun s => { s with dbWrite := true }
  if rest.isEmpty || blockAlwaysReturns txStmts then return txRun
  else `(Qed.Server.srvSeqM $txRun (fun _ => $(← recAsync aCtx rest)))

private partial def lowerBlock (isPure : Bool) (inAtomic : Bool) (s₀ sCur : Ident)
    (stateTyTerm? : Option Term) (ctx : LowerCtx) (stmts : Array Syntax) : LowerM Term := do
  let curOverrides := getPureOverrides ctx
  let mode ← if isPure then
      pure (BlockMode.pure inAtomic s₀ sCur (← liftM <| materializeState sCur curOverrides))
    else
      pure (BlockMode.async stateTyTerm?)
  if stmts.isEmpty then return ← liftM <| mkEmptyLeaf mode ctx
  let stmt := stmts[0]!
  let rest := stmts.extract 1 stmts.size
  let k := stmt.getKind
  let bCtx := if isPure then
      { ctx with
        stateRule := if ctx.stateFields.isEmpty then .statelessServer else .pureStep sCur curOverrides
        allowAwait := false }
    else
      { ctx with
        stateRule := if ctx.stateFields.isEmpty then .statelessServer else .forbidAsyncOutsideAtomic
        allowAwait := true }
  let recSame := fun c st => lowerBlock isPure inAtomic s₀ sCur stateTyTerm? c st
  let recWithState := fun c s st => lowerBlock isPure inAtomic s₀ s stateTyTerm? c st
  let recAtomicPure := fun c s0 s st => lowerBlock true true s0 s none c st
  if k == ``qedStmtPass then
    recSame bCtx rest
  else if let some (chId, rawArgs) := matchSrvEmitStmt? stmt then
    let (emitTerm, steps) ← lowerEmitCall bCtx stmt chId rawArgs
    let body ← match mode with
      | .pure .. =>
          let some esId := bCtx.emitAcc?
            | throwErrorAt stmt "internal error: `emit` accumulator not initialized"
          let esNext ← freshIdent "_es"
          let cont ← recSame { bCtx with emitAcc? := some esNext } rest
          `(let $esNext:ident : List Qed.Server.WsEmit := $esId ++ [$emitTerm]; $cont)
      | .async _ =>
          let evId ← freshIdent "_wsEv"
          let cont ← recSame bCtx rest
          `(let $evId:ident := $emitTerm;
            Qed.Server.MonadServer.wsBroadcast ($evId).topic ($evId).payload >>= fun _ => $cont)
    wrapHoists mode bCtx steps body
  else if k == `Qed.Server.atomicExport && isPure then
    let expTerm : Term := ⟨stmt.getArg 0⟩
    let wrapped ← if bCtx.wrapReturnSumInl then `(Except.ok (Sum.inr $expTerm)) else `(Except.ok $expTerm)
    let .pure _ _ _ matCur := mode | unreachable!
    liftM <| mkPureLeaf bCtx matCur (← `(some $wrapped))
  else if let some (isClear, rawArgs) := matchSetCookieStmt? stmt then
    if isPure then throwErrorAt stmt "cannot call `setCookie`/`clearCookie` inside an `atomic:` block; emit cookies outside `atomic:`"
    let (argT, steps) ← lowerSetCookieCall bCtx stmt isClear rawArgs
    wrapHoists mode bCtx steps (← `(Qed.Server.MonadServer.setCookie $argT >>= fun _ => $(← recSame bCtx rest)))
  else if let some rawArgs := matchSseSendStmt? stmt then
    if isPure then throwErrorAt stmt "cannot call `send(...)` inside an `atomic:` block; emit SSE events outside `atomic:`"
    let (argT, steps) ← lowerSseSendCall bCtx stmt rawArgs
    wrapHoists mode bCtx steps (← `(Qed.Server.MonadServer.sendSse $argT >>= fun _ => $(← recSame bCtx rest)))
  else if let some (aliasRef, aliasName, txStmts) := matchTxStmt? stmt then
    if isPure then
      throwErrorAt stmt "cannot start a database `transaction` inside an `atomic:` block; run database transactions outside `atomic:`"
    lowerTxStmt bCtx stmt aliasRef aliasName txStmts rest recSame
  else if k == ``qedStmtAtomic then
    if isPure then
      if inAtomic then throwErrorAt stmt "nested `atomic` blocks are forbidden"
      else if ctx.stateFields.isEmpty then throwErrorAt stmt "`atomic` is only valid in a `server` with `state` declarations"
      else throwErrorAt stmt s!"redundant `atomic` block: `{ctx.fnName}` has no `await` calls, so it already executes atomically"
    else
      lowerAtomicStmt bCtx stateTyTerm? stmt rest recAtomicPure recSame
  else if k == ``qedStmtReturn then
    lowerReturn mode bCtx stmt
  else if k == ``qedStmtLet then
    lowerLet mode bCtx stmt rest recSame
  else if k == ``qedStmtAssign || (k == ``qedStmtExpr && ((matchPushCall? (stmt.getArg 0)).isSome || (matchRemoveCall? (stmt.getArg 0)).isSome)) then
    if isPure then
      lowerPureMutationStmt mode bCtx sCur stmt rest recSame
    else
      if k == ``qedStmtAssign then rejectSrvAssignPredict stmt
      let targetStx := if k == ``qedStmtAssign then stmt.getArg 0
        else (matchPushCall? (stmt.getArg 0) |>.orElse fun _ => matchRemoveCall? (stmt.getArg 0)).map Prod.fst |>.getD (stmt.getArg 0)
      let _ ← parseLValPath bCtx targetStx
      throwErrorAt stmt s!"cannot mutate server state outside an `atomic:` block in `{ctx.fnName}` because `{ctx.fnName}` uses `await`"
  else if k == ``qedStmtExpr then
    let eStx := stmt.getArg 0
    let (eTerm, steps) ← lowerExprCollectingHoists bCtx .val eStx
    let cont ← recSame bCtx rest
    let valTerm ← if isBareUnwrapExpr (!isPure) eStx then pure eTerm else `(srvEnsureUnit($eTerm))
    wrapHoists mode bCtx steps (← bindLet mode Syntax.missing valTerm cont)
  else if k == ``qedStmtIf then
    let (condTerm, steps) ← lowerExprCollectingHoists bCtx .propGuard (stmt.getArg 1)
    let hGuard ← freshIdent "_srvG"
    let br ← lowerBranch mode bCtx rest (suiteStmts (stmt.getArg 3)) bCtx
      (desugarElifs (stmt.getArg 4).getArgs (stmt.getArg 5)) isPure
      (fun t e => `(if $hGuard:ident : $condTerm then $t else $e)) recSame recWithState
    wrapHoists mode bCtx steps br
  else if k == ``qedStmtIfLet then
    let patStx := stmt.getArg 2
    let patTerm ← liftMacroM (lowerQedPat patStx)
    let patIds := (collectQedPatIds patStx).map (·.toString)
    let (scrutTerm, steps) ← lowerExprCollectingHoists bCtx .val (stmt.getArg 4)
    let thenCtx := { bCtx with locals := bCtx.locals ++ patIds }
    let hMatch ← freshIdent "_srvM"
    let br ← lowerBranch mode bCtx rest (suiteStmts (stmt.getArg 6)) thenCtx
      (extractElseSuite (stmt.getArg 7)) false
      (fun t e => `(match $hMatch:ident : $scrutTerm:term with | $patTerm => $t | _ => $e)) recSame recWithState
    wrapHoists mode bCtx steps br
  else if k == ``qedStmtMatch then
    let (matchT, allSteps) ← lowerMatchScrutineesAndAlts bCtx stmt rest recSame
    wrapHoists mode bCtx allSteps matchT
  else
    let sn := stxSnippet stmt
    let what := if sn.isEmpty then s!"({k})" else s!" `{sn}`"
    let kindStr := if isPure then "server" else "async server"
    throwErrorAt stmt s!"unsupported statement{what} in {kindStr} function `{ctx.fnName}`"

def lowerPureBlock (ctx : LowerCtx) (inAtomic : Bool) (s₀ sCur : Ident) (stmts : Array Syntax) : LowerM Term :=
  lowerBlock true inAtomic s₀ sCur none ctx stmts

def lowerAsyncBlock (ctx : LowerCtx) (stateTyTerm? : Option Term) (stmts : Array Syntax) : LowerM Term :=
  lowerBlock false false (mkIdent `_unused) (mkIdent `_unused) stateTyTerm? ctx stmts

end BlockLowering

end Qed.Server
