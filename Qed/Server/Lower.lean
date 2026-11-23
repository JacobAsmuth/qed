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

section Guards
open Lean Meta Elab Term

@[term_elab srvEnsureUnitStx]
def elabSrvEnsureUnit : TermElab := fun stx _ => do
  let e ← elabTerm (stx.getArg 1) none; synthesizeSyntheticMVarsNoPostponing
  let ty ← whnf (← inferType e)
  if ty.isAppOf ``Except || ty.isAppOf ``Option then
    throwErrorAt stx m!"unhandled fallible or optional expression of type `{← ppExpr ty}`; append `?` to propagate or `catch` to handle"
  ensureHasType (mkConst ``Unit) e

@[term_elab srvRejectErrStx]
def elabSrvRejectErr : TermElab := fun stx expectedType? => do
  let e ← elabTerm (stx.getArg 1) expectedType?; synthesizeSyntheticMVarsNoPostponing
  let ty ← whnf (← inferType e)
  if ty.isAppOfArity ``Except 2 then
    if (← whnf ty.getAppArgs[0]!).isConstOf ``ApiError then
      throwErrorAt stx m!"unhandled fallible `T!` value of type `{← ppExpr ty}`; append `?` to propagate errors or use `catch` to recover"
  return e

end Guards

/-! ## Persistent Registries & Lowering State -/

export Qed (ServerMethodInfo ServerInfo serverRegistry)

structure FullstackInfo where
  fullstackName : Lean.Name
  serverName    : Lean.Name
  title         : String
deriving Inhabited, Repr

initialize fullstackRegistry : Lean.SimplePersistentEnvExtension FullstackInfo (Lean.NameMap FullstackInfo) ← Qed.Diag.mkNameMapExt (·.fullstackName)

inductive StateAccessRule where
  | pureStep (stateVar : Lean.Ident) (overrides : Array (String × Lean.Ident) := #[])
  | invariantProp (curVar oldVar : Lean.Ident) (inOld : Bool)
  | forbidAsyncOutsideAtomic | forbidInRequires | forbidInEnsures | statelessServer

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
  nextId   : Nat := 0
  mutated  : Array String := #[]
  dbWrite  : Bool := false
  extRoots : Array Lean.Name := #[]
  hoisted  : Array HoistedStep := #[]

abbrev LowerM := StateRefT LowerState Lean.Elab.Command.CommandElabM

private def freshIdent (pfx : String) : LowerM Lean.Ident := do
  let n := (← get).nextId; modify fun s => { s with nextId := n + 1 }
  return Lean.mkIdent (Lean.Name.mkSimple s!"{pfx}{n}")

private def recordMutated (f : String) : LowerM Unit := modify fun s => { s with mutated := pushUnique s.mutated f }
private def recordExtRoot (n : Lean.Name) : LowerM Unit := modify fun s => { s with extRoots := pushUnique s.extRoots n }

/-! ## Static AST Queries -/

private def matchTxStmt? (stx : Lean.Syntax) : Option (Lean.Syntax × String × Array Lean.Syntax) :=
  if stx.getKind == ``qedStmtDbTransaction then
    let dotStx := stx.getArg 0; let idNode := if dotStx.isIdent then dotStx else dotStx.getArg 0
    let aliasName := match idNode.getId.eraseMacroScopes with | .str (.str .anonymous a) "transaction" => a | _ => ""
    some (dotStx, aliasName, suiteStmts (stx.getArg 2))
  else none

private def matchNamedStmtCall? (stx : Lean.Syntax) : Option (String × Array Lean.Syntax) := do
  guard (stx.getKind == ``qedStmtExpr)
  let e := unwrapParens1 (stx.getArg 0); guard (e.getKind == ``qedCall)
  match extractDottedChain? (e.getArg 0) with | some [nm] => some (nm, (e.getArg 2).getSepArgs) | _ => none

private def matchSrvEmitStmt? (stx : Lean.Syntax) : Option (Lean.Ident × Array Lean.Syntax) := do
  guard (stx.getKind == ``qedStmtExpr)
  let (chId, meth, rawArgs) ← matchIdentMethodCall? (stx.getArg 0)
  guard (meth == "emit"); return (chId, rawArgs)

def exprHasAwait (stx : Lean.Syntax) : Bool := stxAny (·.getKind == ``qedAwait) stx
def blockHasAwait (stmts : Array Lean.Syntax) : Bool :=
  stmts.any (stxAny fun s => s.getKind == ``qedAwait || (matchTxStmt? s).isSome ||
    (matchNamedStmtCall? s).any fun (nm, _) => nm == "setCookie" || nm == "clearCookie" || nm == "send")
def blockHasEmit (stmts : Array Lean.Syntax) : Bool := stmts.any (stxAny fun s => (matchSrvEmitStmt? s).isSome)
def blockHasAtomic (stmts : Array Lean.Syntax) : Bool := stmts.any (stxAny (·.getKind == ``qedStmtAtomic))

mutual
  partial def stmtAlwaysReturns (stx : Lean.Syntax) : Bool :=
    let k := stx.getKind
    if k == ``qedStmtReturn then true
    else if k == ``qedStmtAtomic then blockAlwaysReturns (suiteStmts (stx.getArg 2))
    else if let some (_, _, tx) := matchTxStmt? stx then blockAlwaysReturns tx
    else if k == ``qedStmtIf then (desugarElifs (stx.getArg 4).getArgs (stx.getArg 5)).any fun e => blockAlwaysReturns (suiteStmts (stx.getArg 3)) && blockAlwaysReturns e
    else if k == ``qedStmtIfLet then (extractElseSuite (stx.getArg 7)).any fun e => blockAlwaysReturns (suiteStmts (stx.getArg 6)) && blockAlwaysReturns e
    else if k == ``qedStmtMatch then let cs := (stx.getArg 3).getArgs; !cs.isEmpty && cs.all fun c => blockAlwaysReturns (suiteStmts (c.getArg 3))
    else false
  partial def blockAlwaysReturns (stmts : Array Lean.Syntax) : Bool := stmts.any stmtAlwaysReturns
end

def ensureUnitReturn (ref : Lean.Syntax) (stmts : Array Lean.Syntax) : Array Lean.Syntax :=
  if blockAlwaysReturns stmts then stmts
  else let i := Lean.SourceInfo.fromRef ref; stmts.push (Lean.Syntax.node i ``qedStmtReturn #[Lean.Syntax.atom i "return", Lean.Syntax.node i Lean.nullKind #[]])

mutual
  partial def exprHasUnwrap (stx : Lean.Syntax) : Bool :=
    let k := stx.getKind
    if k == ``qedUnwrap then true
    else if k == ``qedDotIdent || k == ``qedLam1 || k == ``qedLamN || k == ``qedAllIn || k == ``qedAnyIn || k == ``qedAllVars then false
    else if k == ``qedIdent then (stx.getArg 0).getId.toString.endsWith "?"
    else stx.getArgs.any exprHasUnwrap
  partial def stmtMayReturnEarly (stx : Lean.Syntax) : Bool :=
    let k := stx.getKind
    if k == ``qedStmtReturn || k == ``qedStmtAtomic || (matchTxStmt? stx).isSome then true
    else if k == ``qedStmtLet then (stx.getArg 5).getNumArgs > 0 || exprHasUnwrap (stx.getArg 4)
    else if k == ``qedStmtIf then exprHasUnwrap (stx.getArg 1) || blockMayReturnEarly (suiteStmts (stx.getArg 3)) || (desugarElifs (stx.getArg 4).getArgs (stx.getArg 5)).any blockMayReturnEarly
    else if k == ``qedStmtIfLet then exprHasUnwrap (stx.getArg 4) || blockMayReturnEarly (suiteStmts (stx.getArg 6)) || (extractElseSuite (stx.getArg 7)).any blockMayReturnEarly
    else if k == ``qedStmtMatch then (stx.getArg 1).getSepArgs.any exprHasUnwrap || (stx.getArg 3).getArgs.any fun c => blockMayReturnEarly (suiteStmts (c.getArg 3))
    else exprHasUnwrap stx
  partial def blockMayReturnEarly (stmts : Array Lean.Syntax) : Bool := stmts.any stmtMayReturnEarly
end

/-! ## Expression Lowering (`lowerExpr`) -/

section ExprLowering
open Lean Elab Command

private def peelIdentTrailingQ (id : Ident) : Ident × Nat :=
  let cs := id.getId.toString.toList; let q := (cs.reverse.takeWhile (· == '?')).length
  if q == 0 then (id, 0) else (mkIdentFrom id (((String.ofList (cs.take (cs.length - q))).splitOn ".").foldl Name.str .anonymous), q)

private def checkStateRead (ref : Syntax) (ctx : LowerCtx) (field : String) : LowerM Ident := do
  match ctx.stateRule with
  | .pureStep sv _ => return sv
  | .invariantProp curV oldV inOld => return if inOld then oldV else curV
  | .forbidAsyncOutsideAtomic => throwErrorAt ref s!"cannot access server state `{field}` outside an `atomic` block in `{ctx.fnName}` because `{ctx.fnName}` uses `await` (prevents TOCTOU data races across suspension points)"
  | .forbidInRequires => throwErrorAt ref s!"`requires` precondition in `{ctx.fnName}` cannot reference mutable server state `{field}`; check `{field}` inside the function body instead"
  | .forbidInEnsures => throwErrorAt ref s!"`ensures` postcondition in `{ctx.fnName}` cannot reference mutable server state `{field}`; state postconditions on `result` and parameters only"
  | .statelessServer => throwErrorAt ref s!"unknown identifier `{field}`"

private def resolveStateFieldBase (ref : Syntax) (ctx : LowerCtx) (field : Name) : LowerM Term := do
  let sv ← checkStateRead ref ctx field.toString
  if let .pureStep _ ovs := ctx.stateRule then
    if let some (_, ovId) := ovs.find? (·.1 == field.toString) then return ⟨mkIdentFrom ref ovId.getId⟩
  `(($sv).$(mkIdentFrom ref field):ident)

private def resolveDottedIdent (ref : Syntax) (ctx : LowerCtx) (id : Ident) : LowerM Term := do
  match id.getId.components with
  | [] => throwErrorAt ref "empty identifier"
  | root :: rest =>
      let rStr := root.toString
      if rest.isEmpty && rStr == "true" then `(true)
      else if rest.isEmpty && rStr == "false" then `(false)
      else if rest.isEmpty && rStr == "none" then `(none)
      else if ctx.locals.contains rStr then foldProjTerms ref ⟨mkIdentFrom ref root⟩ rest
      else if rStr == "ctx" || ctx.envVars.contains rStr then
        if ctx.forbidCtxEnv then
          let what := if rest.isEmpty && rStr != "ctx" then s!"`env` binding `{rStr}`" else s!"`{rStr}`"
          throwErrorAt ref s!"`ensures` postcondition in `{ctx.fnName}` cannot reference {what} because client decoders re-verify `ensures` on the wire"
        foldProjTerms ref ⟨mkIdentFrom ref root⟩ rest
      else if ctx.stateFields.contains rStr then foldProjTerms ref (← resolveStateFieldBase ref ctx root) rest
      else do
        if !rest.isEmpty then recordExtRoot root
        return ⟨id⟩

private def checkAllowUnwrap (ref : Syntax) (ctx : LowerCtx)
    (msg : String := s!"operator `?` cannot be used here in `{ctx.fnName}` (return type must be `T!` or `T?`, and `?` cannot appear inside lambdas or invariants)") : CommandElabM Unit := do
  unless ctx.allowUnwrap do throwErrorAt ref msg

private def hoistPureUnwraps (ref : Syntax) (ctx : LowerCtx) (qCount : Nat) (term0 : Term) : LowerM Term := do
  if qCount == 0 then return term0
  liftM <| checkAllowUnwrap ref ctx
  let mut term := term0
  for _ in [0:qCount] do
    let tmp ← freshIdent "_srvUnw"; modify fun s => { s with hoisted := s.hoisted.push (.pureUnwrap tmp term) }; term := ⟨tmp⟩
  return term

private abbrev SrvExprM := ReaderT LowerCtx LowerM

private partial def lowerJsonPayload (go : ExprMode → Syntax → SrvExprM Term) (stx : Syntax) : SrvExprM Term := do
  let u := unwrapParens1 stx
  if u.getKind == ``qedRecLit && (u.getArg 1).getNumArgs != 2 then
    let pairs ← (u.getArg 2).getSepArgs.mapM fun f => do `(($(Syntax.mkStrLit (f.getArg 0).getId.eraseMacroScopes.toString), $(← lowerJsonPayload go (f.getArg 2))))
    `(Qed.Json.obj [$[$pairs],*])
  else if u.getKind == ``qedArrLit then `(Qed.Json.arr [$(← (u.getArg 1).getSepArgs.mapM (lowerJsonPayload go)),*])
  else `(Qed.toJson $(← go .val stx))

@[noinline]
private def lowerSrvCallHook (stx calleeStx : Syntax) (rawArgs : Array Syntax) (mode : ExprMode) (go : ExprMode → Syntax → SrvExprM Term) : SrvExprM (Option Term) := do
  let ctx ← read
  if !ctx.dbs.isEmpty then
    if let some chain := extractDottedChain? calleeStx then
      if let some aliasName := chain.head? then
        if let some (_, dbInfo) := ctx.dbs.find? (·.1 == aliasName) then
          let txIdTerm? := ctx.activeDbTx?.bind fun (a, tid) => if a == aliasName then some ⟨tid.raw⟩ else none
          let (dbTerm, isWrite) ← Db.lowerDbCall (go .val) (fun loc e => withReader (fun c => { c with locals := c.locals.push loc }) (go .val e)) ctx.fnName dbInfo stx chain rawArgs txIdTerm?
          if isWrite then modify fun s => { s with dbWrite := true }
          return some dbTerm
  if calleeStx.getKind == ``qedIdent then
    let cname := (calleeStx.getArg 0).getId.eraseMacroScopes
    if cname == `old then
      match ctx.stateRule with
      | .invariantProp curV oldV _ =>
          if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then throwErrorAt stx "`old(...)` expects exactly one positional expression argument"
          return some (← withReader (fun c => { c with stateRule := .invariantProp curV oldV true }) (go mode rawArgs[0]![0]))
      | _ => throwErrorAt stx "`old(...)` may only be used inside `invariant` declarations"
    if cname == `fail then
      if rawArgs.any (·.getKind == ``qedCallArgNamed) then throwErrorAt stx "`fail(...)` takes positional arguments `fail(.tag)`, `fail(.tag, msg)`, `fail(msg)`, or `fail(code, msg)`"
      if (rawArgs.size == 1 || rawArgs.size == 2) && (unwrapParens1 rawArgs[0]![0]).getKind == ``qedDotIdent then
        let uDot := unwrapParens1 rawArgs[0]![0]; let tagId : Ident := ⟨uDot.getArg 1⟩
        let some errTy := ctx.domainErrTy? | throwErrorAt stx "internal error: missing inferred domain error type for `fail(.tag)`"
        let msgTerm ← if rawArgs.size == 2 then go .val rawArgs[1]![0] else pure (Syntax.mkStrLit tagId.getId.toString)
        let dotNode : Term := ⟨Syntax.node (.fromRef uDot) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef uDot) ".", tagId.raw]⟩
        return some (← `(Qed.Server.mkFailDom (ε := $errTy) ($dotNode : $errTy) $msgTerm))
      if ctx.domainErrTy?.isSome then throwErrorAt stx "cannot mix typed `fail(.tag)` and untyped `fail(...)` inside the same function; use `fail(.tag, msg)`"
      if rawArgs.size == 1 then return some (← `(Qed.Server.mkFail1 $(← go .val rawArgs[0]![0])))
      if rawArgs.size == 2 then return some (← `(Qed.Server.mkFail2 $(← go .val rawArgs[0]![0]) $(← go .val rawArgs[1]![0])))
      throwErrorAt stx "`fail(...)` expects `(.tag)`, `(.tag, msg)`, `(message)`, or `(code, message)`"
    if ctx.isHttpRoute then
      let fnName := cname.toString
      if !(ctx.locals.contains fnName || ctx.stateFields.contains fnName || ctx.envVars.contains fnName) then
        if let some (_, ctorNm, defSt) := [("text", `Qed.Server.HttpResponse.text, 200), ("json", `Qed.Server.HttpResponse.jsonOf, 200),
            ("html", `Qed.Server.HttpResponse.html, 200), ("redirect", `Qed.Server.HttpResponse.redirect, 302), ("bytes", `Qed.Server.HttpResponse.bytes, 200)].find? (·.1 == fnName) then
          let (posArgs, namedArgs) ← splitCallArgs fnName rawArgs (some ["status"])
          let stT ← match findNamedArg? namedArgs "status" with | some s => go .val s | none => liftM (show CommandElabM Term from `(($(quote defSt) : Nat)))
          if fnName == "bytes" then
            if posArgs.size != 2 then throwErrorAt stx "`bytes(contentType, body[, status = 200])` expects a content type and body"
            return some (← `(Qed.Server.HttpResponse.bytes $(← go .val posArgs[0]!) $(← go .val posArgs[1]!) $stT))
          if posArgs.size != 1 then throwErrorAt stx s!"`{fnName}(...)` expects one positional argument (and optional `status = ...`)"
          let argT ← if fnName == "json" then lowerJsonPayload go posArgs[0]! else go .val posArgs[0]!
          return some (← `($(mkIdent ctorNm) $argT $stT))
  return none

private def checkAllowAwait (ref : Syntax) : SrvExprM Unit := do
  unless (← read).allowAwait do throwErrorAt ref "`await` cannot be used inside an `atomic` block, lambda, `requires`, or `invariant`; perform external I/O outside `atomic`"

private def hoistAwaitUnwrap (recGo : ExprMode → Syntax → SrvExprM Term) (stx awaitRef callStx : Syntax) (mode : ExprMode) : SrvExprM Term := do
  checkAllowAwait awaitRef
  let callTerm ← recGo .val callStx; let tmp ← liftM <| freshIdent "_srvAw"
  modify fun s => { s with hoisted := s.hoisted.push (.awaitUnwrap stx tmp callTerm) }
  liftMacroM (finishTermMode mode ⟨tmp⟩)

private def mkSrvLowerHooks (recGo : ExprMode → Syntax → SrvExprM Term) : LowerHooks SrvExprM :=
  { LowerHooks.mkDefault (fun ref msg => throwErrorAt ref msg) with
    lowerIdent := fun stx id mode => do let ctx ← read; let (cid, q) := peelIdentTrailingQ id; liftMacroM (finishTermMode mode (← liftM <| hoistPureUnwraps stx ctx q (← resolveDottedIdent stx ctx cid)))
    lowerProj := fun stx objT fld mode => do let ctx ← read; let (cf, q) := peelIdentTrailingQ fld; liftMacroM (finishTermMode mode (← liftM <| hoistPureUnwraps stx ctx q (← `(($objT).$cf:ident))))
    lowerIndex := fun _ arrT idxT mode => do liftMacroM (finishTermMode mode (← `(srvGetElem($arrT, $idxT))))
    lowerCall := lowerSrvCallHook
    lowerUnwrap := fun stx innerRaw mode => do
      let ctx ← read; liftM <| checkAllowUnwrap stx ctx; let inner := unwrapParens1 innerRaw
      if inner.getKind == ``qedAwait then hoistAwaitUnwrap recGo stx inner (inner.getArg 1) mode
      else liftMacroM (finishTermMode mode (← liftM <| hoistPureUnwraps stx ctx 1 (← recGo .val innerRaw)))
    lowerAwait := fun stx argRaw mode => do
      checkAllowAwait stx; let inner := unwrapParens1 argRaw
      if inner.getKind == ``qedUnwrap then
        let ctx ← read
        liftM <| checkAllowUnwrap stx ctx s!"operator `?` cannot be used in `{ctx.fnName}` because its return type is neither fallible (`T!`) nor optional (`T?`); handle the `await` error with `let x = await ... catch err:`"
        hoistAwaitUnwrap recGo stx stx (inner.getArg 0) mode
      else throwErrorAt stx "unhandled fallible `await` expression; append `?` to propagate errors or use `let x = await ... catch err:` to handle them inline"
    lowerArrElem := fun t => `(srvAutoField($t))
    wrapNamedField := fun t => `(srvAutoField($t))
    lowerType := fun t => liftMacroM (return (← lowerQedType t false).1)
    lowerPat := fun p => liftMacroM (lowerQedPat p)
    withLocals := fun names k => withReader (fun c => { c with locals := c.locals ++ names, allowAwait := false, allowUnwrap := false }) k
    useDirectArray := true
    freshIdent := fun pfx => liftM <| freshIdent pfx }

private partial def lowerExprM (mode : ExprMode) (stx : Syntax) : SrvExprM Term := lowerQedExpr (mkSrvLowerHooks lowerExprM) mode stx
@[noinline] def lowerExpr (ctx : LowerCtx) (mode : ExprMode) (stx : Syntax) : LowerM Term := (lowerExprM mode stx).run ctx

private def withCollectedHoists {α : Type} (act : LowerM α) : LowerM (α × Array HoistedStep) := do
  let saved := (← get).hoisted; modify fun s => { s with hoisted := #[] }
  let res ← act; let steps := (← get).hoisted; modify fun s => { s with hoisted := saved }; return (res, steps)

private def lowerExprCollectingHoists (ctx : LowerCtx) (mode : ExprMode) (stx : Syntax) : LowerM (Term × Array HoistedStep) :=
  withCollectedHoists (lowerExpr ctx mode stx)

/-! ## LValue Mutation Path Parsing & Functional Lens Construction -/

private inductive LValStep where | field (id : Lean.Ident) | index (idxTerm : Lean.Term)

private partial def parseLValPath (ctx : LowerCtx) (stx : Syntax) : LowerM (Ident × Array LValStep) := do
  let k := stx.getKind
  if k == ``qedIdent then
    match (stx.getArg 0).getId.components with
    | [] => throwErrorAt stx "invalid assignment target"
    | root :: rest =>
        let rStr := root.toString
        unless ctx.stateFields.contains rStr do
          if ctx.locals.contains rStr || ctx.envVars.contains rStr || rStr == "ctx" then
            throwErrorAt stx s!"cannot mutate `{rStr}`: parameters, `env` bindings, `ctx`, and `let` bindings are immutable; only `state` fields may be mutated"
          let avail := if ctx.stateFields.isEmpty then "this server declares no `state` fields" else s!"`state` fields: {String.intercalate ", " (ctx.stateFields.toList.map fun f => s!"`{f}`")}"
          throwErrorAt stx s!"cannot mutate unknown state field `{rStr}` ({avail})"
        let _ ← checkStateRead stx ctx rStr; recordMutated rStr
        return (mkIdentFrom stx root, rest.toArray.map (LValStep.field <| mkIdentFrom stx ·))
  else if k == ``qedProj then let (r, ps) ← parseLValPath ctx (stx.getArg 0); return (r, ps.push (.field ⟨stx.getArg 2⟩))
  else if k == ``qedIndex then let (r, ps) ← parseLValPath ctx (stx.getArg 0); return (r, ps.push (.index (← lowerExpr ctx .val (stx.getArg 2))))
  else throwErrorAt stx "invalid mutation target; expected `stateField`, `stateField.sub`, or `stateField[i].sub`"

private partial def withUpdatedPathCPS (steps : Array LValStep) (idx : Nat) (curVal : Term)
    (mkLeafNew : Term → LowerM Term) (k : Term → LowerM Term) : LowerM Term := do
  if h : idx < steps.size then
    match steps[idx] with
    | .field fid => withUpdatedPathCPS steps (idx + 1) (← `(($curVal).$fid:ident)) mkLeafNew fun ch => do k (← `({ $curVal with $fid:ident := srvAutoField($ch) }))
    | .index idxT =>
        let elemId ← freshIdent "_elem"; let hElemId ← freshIdent "_srvEqElem"
        let body ← withUpdatedPathCPS steps (idx + 1) ⟨elemId⟩ mkLeafNew fun el => do k (← `(srvSetElem($curVal, $idxT, $el)))
        `(Qed.Server.srvLetEq (srvGetElem($curVal, $idxT)) (fun $elemId:ident $hElemId:ident => $body))
  else k (← mkLeafNew curVal)

private def getPureOverrides (ctx : LowerCtx) : Array (String × Ident) := match ctx.stateRule with | .pureStep _ ovs => ovs | _ => #[]
private def setPureOverride (ctx : LowerCtx) (sCur : Ident) (fld : String) (vId : Ident) : LowerCtx :=
  { ctx with stateRule := .pureStep sCur ((getPureOverrides ctx).filter (·.1 != fld) |>.push (fld, vId)) }
private def materializeState (sCur : Ident) (ovs : Array (String × Ident)) : CommandElabM Term := do
  if ovs.isEmpty then `(($sCur))
  else let fIds := ovs.map fun p => mkIdent (Name.mkSimple p.1); let fVars : Array Term := ovs.map (⟨·.2.raw⟩); `({ $sCur with $[$fIds:ident := $fVars:term],* })

/-! ## Return Value Auto-Lifting, Atomic Runner & Hoist Wrapping -/

private def isFailCall (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx; u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId == `fail

private def wrapOkValue (ctx : LowerCtx) (valTerm : Term) : CommandElabM Term := do
  let inner ← match ctx.innerOptTy? with
    | some innerTy => if valTerm.raw.isIdent && valTerm.raw.getId.eraseMacroScopes == `none then `((none : Option $innerTy)) else `(Qed.Server.SrvLiftOpt.liftOpt (Inner := $innerTy) $valTerm)
    | none => `(srvAutoField($valTerm))
  if ctx.wrapReturnSumInl then `(Except.ok (Sum.inl $inner)) else `(Except.ok $inner)

private def errTyOf (ctx : LowerCtx) : CommandElabM Term := match ctx.domainErrTy? with | some et => `(Qed.Server.SrvFailure $et) | none => `(Qed.Server.ApiError)
private def mkPureLeaf (ctx : LowerCtx) (stTerm optTerm : Term) : CommandElabM Term := match ctx.emitAcc? with | some esId => `(($stTerm, $esId, $optTerm)) | none => `(($stTerm, $optTerm))
private def mkPureErrLeaf (ctx : LowerCtx) (s₀ : Ident) (errTerm : Term) : CommandElabM Term :=
  match ctx.emitAcc? with | some _ => `(($s₀, ([] : List Qed.Server.WsEmit), some (Except.error $errTerm))) | none => `(($s₀, some (Except.error $errTerm)))

@[noinline]
private def lowerEmitCall (ctx : LowerCtx) (stmt : Syntax) (chId : Ident) (rawArgs : Array Syntax) : LowerM (Term × Array HoistedStep) := do
  let chStr := chId.getId.eraseMacroScopes.toString
  let some chSig := ctx.channels.find? (·.name == chStr)
    | throwErrorAt chId s!"unknown WebSocket `channel` `{chStr}` in `.emit(...)` (declared channels: [{String.intercalate ", " (ctx.channels.toList.map (·.name))}])"
  if rawArgs.size != chSig.paramCount + 1 then
    throwErrorAt stmt s!"`{chStr}.emit(...)` expects {chSig.paramCount + 1} argument(s) ({chSig.paramCount} channel param(s) + 1 event), got {rawArgs.size}"
  let (argTerms, allSteps) ← withCollectedHoists <| rawArgs.mapM fun ra => do
    unless ra.getKind == ``qedCallArgPos do throwErrorAt ra s!"named arguments are not supported in `{chStr}.emit(...)`"
    lowerExpr ctx .val (ra.getArg 0)
  let mut call ← mkAppTerms (chSig.mkEmitId : Term) (argTerms.extract 0 chSig.paramCount)
  call ← `($call (srvAutoField($(argTerms[chSig.paramCount]!))))
  if chSig.hasEnsures then call ← `($call (srvAutoEmit(True)))
  return (call, allSteps)

@[noinline]
def mkAtomicRunTerm (s0Id : Ident) (stateTyTerm committed : Term) (readOnly hasEmit : Bool)
    (onResult? : Option (Ident × (Term → CommandElabM Term)) := none) : CommandElabM Term := do
  let runCall ← if readOnly then `(Qed.Server.MonadAtomic.runAtomicRead (fun ($s0Id:ident : $stateTyTerm) => ($committed).2))
    else `(Qed.Server.MonadAtomic.runAtomic (fun ($s0Id:ident : $stateTyTerm) => $committed))
  match hasEmit, onResult? with
  | true, some (pairId, onRes) => `($runCall >>= fun $pairId:ident => Qed.Server.flushWsEmits ($pairId).2 >>= fun _ => $(← onRes (← `(($pairId).1))))
  | true, none => `($runCall >>= fun _emitPair => Qed.Server.flushWsEmits (_emitPair).2 >>= fun _ => Pure.pure (_emitPair).1)
  | false, some (resId, onRes) => `($runCall >>= fun $resId:ident => $(← onRes ⟨resId.raw⟩))
  | false, none => pure runCall

end ExprLowering

private inductive BlockMode where
  | pure  (inAtomic : Bool) (s₀ sCur : Lean.Ident) (matCur : Lean.Term)
  | async (stateTyTerm? : Option Lean.Term)

section BlockLowering
open Lean Elab Command

private def mkOkLeaf (mode : BlockMode) (ctx : LowerCtx) (valTerm : Term) : CommandElabM Term := do
  let ok ← wrapOkValue ctx valTerm
  match mode with | .pure _ _ _ m => mkPureLeaf ctx m (← `(some $ok)) | .async _ => `(Pure.pure (some $ok))
private def mkErrLeaf (mode : BlockMode) (ctx : LowerCtx) (errTerm : Term) : CommandElabM Term :=
  match mode with | .pure _ s₀ _ _ => mkPureErrLeaf ctx s₀ errTerm | .async _ => `(Pure.pure (some (Except.error $errTerm)))
private def mkEmptyLeaf (mode : BlockMode) (ctx : LowerCtx) : CommandElabM Term :=
  match mode with | .pure _ _ _ m => do mkPureLeaf ctx m (← `(none)) | .async _ => `(Pure.pure none)

@[noinline]
private def wrapUnwrapStep (mode : BlockMode) (ctx : LowerCtx) (tmp : Ident) (valTerm acc : Term) : CommandElabM Term := do
  if !ctx.hasFallible then
    if let some innerTy := ctx.innerOptTy? then
      match mode with
      | .pure _ s₀ _ m =>
          return ← `(match Qed.Server.SrvUnwrapOpt.unwrapOpt (Inner := $innerTy) $valTerm with
            | Except.error (Except.ok none) => $(← mkPureLeaf ctx m (← `(some (Except.ok none))))
            | Except.error (Except.error _e) => $(← mkPureErrLeaf ctx s₀ (← `(_e))) | Except.ok $tmp:ident => $acc)
      | .async _ => return ← `(match Qed.Server.SrvUnwrapOpt.unwrapOpt (Inner := $innerTy) $valTerm with | Except.error _early => Pure.pure (some _early) | Except.ok $tmp:ident => $acc)
  `(match Qed.Server.SrvUnwrap.unwrap (E := $(← errTyOf ctx)) $valTerm with | Except.error _e => $(← mkErrLeaf mode ctx (← `(_e))) | Except.ok $tmp:ident => $acc)

@[noinline]
private def wrapHoists (mode : BlockMode) (ctx : LowerCtx) (steps : Array HoistedStep) (body : Term) : LowerM Term :=
  steps.foldrM (init := body) fun step acc => do
    match step, mode with
    | .awaitUnwrap ref _ _, .pure .. => throwErrorAt ref "`await` cannot appear inside a pure/atomic block"
    | .awaitUnwrap _ tmp callTerm, .async _ =>
        let rawTmp ← freshIdent "_srvRaw"
        `($callTerm >>= fun $rawTmp:ident => $(← liftM <| wrapUnwrapStep mode ctx tmp ⟨rawTmp⟩ acc))
    | .pureUnwrap tmp valTerm, _ => liftM <| wrapUnwrapStep mode ctx tmp valTerm acc

private def bindOptIdent (xStx : Syntax) (val cont : Term) : CommandElabM Term :=
  if xStx.isIdent then let xId : Ident := ⟨xStx⟩; `(let $xId:ident := $val; $cont) else `(let _ := $val; $cont)

@[noinline]
private def bindLet (mode : BlockMode) (xStx : Syntax) (val cont : Term) : LowerM Term := do
  match mode with
  | .pure .. =>
      let xId ← if xStx.isIdent then pure ⟨xStx⟩ else freshIdent "_srvDiscard"
      `(Qed.Server.srvLetEq $val (fun $xId:ident $(← freshIdent "_srvEq"):ident => $cont))
  | .async _ => liftM <| bindOptIdent xStx val cont

private def pushOptLocal (ctx : LowerCtx) (xStx : Syntax) : LowerCtx := if xStx.isIdent then { ctx with locals := ctx.locals.push xStx.getId.toString } else ctx

private def isBareUnwrapExpr (allowAwait : Bool) (eStx : Syntax) : Bool :=
  let u := unwrapParens1 eStx
  u.getKind == ``qedUnwrap || (allowAwait && u.getKind == ``qedAwait && (unwrapParens1 (u.getArg 1)).getKind == ``qedUnwrap) ||
  (eStx.getKind == ``qedIdent && (eStx.getArg 0).getId.toString.endsWith "?") || (eStx.getKind == ``qedProj && (eStx.getArg 2).getId.toString.endsWith "?")

/-! ## Unified Pure & Async Statement Block Lowering (`lowerBlock`) -/

private partial def lowerCatchFallback? (ctx : LowerCtx) (stmts : Array Syntax) : LowerM (Option Term) := do
  let lowerPureNoHoist (eStx : Syntax) : LowerM (Option Term) := do
    if exprHasAwait eStx || exprHasUnwrap eStx then return none
    let (t, steps) ← lowerExprCollectingHoists { ctx with allowAwait := false } .val eStx
    return if steps.isEmpty then some t else none
  if stmts.isEmpty then return none
  else if stmts.size == 1 && stmts[0]!.getKind == ``qedStmtExpr then
    let eStx := stmts[0]![0]
    if (matchPushCall? eStx).isSome || (matchRemoveCall? eStx).isSome || (matchSrvEmitStmt? stmts[0]!).isSome then return none
    let some eTerm ← lowerPureNoHoist eStx | return none
    some <$> `(srvAutoField($eTerm))
  else if stmts[0]!.getKind == ``qedStmtLet && stmts[0]![5].getNumArgs == 0 then
    let st := stmts[0]!
    let some rhsTerm ← lowerPureNoHoist (st.getArg 4) | return none
    let some tailTerm ← lowerCatchFallback? (pushOptLocal ctx (st.getArg 1)) (stmts.extract 1 stmts.size) | return none
    some <$> liftM (bindOptIdent (st.getArg 1) (← `(srvRejectUnhandledErr($rhsTerm))) tailTerm)
  else return none

@[noinline]
private def lowerMatchScrutineesAndAlts (ctx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (lowerArm : LowerCtx → Array Syntax → LowerM Term) : LowerM (Term × Array HoistedStep) := do
  let (scrutTerms, allSteps) ← withCollectedHoists <| (stmt.getArg 1).getSepArgs.mapM (lowerExpr ctx .val)
  let cases := (stmt.getArg 3).getArgs; let allRet := cases.all fun c => blockAlwaysReturns (suiteStmts (c.getArg 3))
  let alts ← cases.mapM fun c => do
    let pats ← (c.getArg 1).getSepArgs.mapM fun p => liftMacroM (lowerQedPat p)
    let pIds := ((c.getArg 1).getSepArgs.flatMap collectQedPatIds).map (·.toString)
    `(Lean.Parser.Term.matchAltExpr| | $[$pats:term],* => $(← lowerArm { ctx with locals := ctx.locals ++ pIds } (suiteStmts (c.getArg 3) ++ if allRet then #[] else rest)))
  return (← `(match $[$scrutTerms:term],* with $[$alts:matchAlt]*), allSteps)

private def extractSrvLetCatch? (clausesNode : Syntax) : LowerM (Option Syntax) := do
  let mut catchOpt? : Option Syntax := none
  for cl in clausesNode.getArgs do
    let ck := cl.getKind
    if ck == `Qed.Lang.letCatch then
      if catchOpt?.isSome then throwErrorAt cl "duplicate `catch` clause on `let`"
      catchOpt? := some (cl.getArg 1)
    else if ck == `Qed.Lang.letPredictBlock || ck == `Qed.Lang.letPredictExpr || ck == `Qed.Lang.letOnConfirm || ck == `Qed.Lang.letRollback then
      throwErrorAt cl "`predict`, `on_confirm`, and `rollback` are only supported on client `component` `await` calls, not in `server` functions"
  return catchOpt?

private def rejectSrvAssignPredict (stmt : Syntax) : LowerM Unit := do
  if stmt.getKind == ``qedStmtAssign && stmt.getNumArgs > 3 && (stmt.getArg 3).getNumArgs > 0 then
    throwErrorAt ((stmt.getArg 3).getArg 0) "`predict` is only supported on client `component` `await` calls, not in `server` functions"

@[noinline]
private def lowerBranch (mode : BlockMode) (ctx : LowerCtx) (rest thenStmts : Array Syntax) (thenCtx : LowerCtx)
    (elseStmts? : Option (Array Syntax)) (allowPureLetJoin : Bool) (mkBranch : Term → Term → CommandElabM Term)
    (recSame : LowerCtx → Array Syntax → LowerM Term) (recWithState : LowerCtx → Ident → Array Syntax → LowerM Term) : LowerM Term := do
  let thenRet := blockAlwaysReturns thenStmts; let elseRet := elseStmts?.any blockAlwaysReturns
  let lowerElseOpt := elseStmts?.elim (liftM <| mkEmptyLeaf mode ctx) (recSame ctx)
  if rest.isEmpty then liftM =<< (mkBranch <$> recSame thenCtx thenStmts <*> lowerElseOpt)
  else if thenRet && !elseRet then liftM =<< (mkBranch <$> recSame thenCtx thenStmts <*> recSame ctx ((elseStmts?.getD #[]) ++ rest))
  else if !thenRet && elseRet then liftM =<< (mkBranch <$> recSame thenCtx (thenStmts ++ rest) <*> recSame ctx (elseStmts?.getD #[]))
  else
    let br ← liftM =<< (mkBranch <$> recSame thenCtx thenStmts <*> lowerElseOpt)
    match mode with
    | .pure .. =>
        let sNext ← freshIdent "_s"
        let baseJoinCtx := { ctx with stateRule := if ctx.stateFields.isEmpty then .statelessServer else .pureStep sNext #[] }
        match ctx.emitAcc? with
        | some _ => let esNext ← freshIdent "_es"; `(Qed.Server.srvEmitSeq $br (fun $sNext:ident $esNext:ident => $(← recWithState { baseJoinCtx with emitAcc? := some esNext } sNext rest)))
        | none =>
            let cont ← recWithState baseJoinCtx sNext rest
            if allowPureLetJoin && !blockMayReturnEarly thenStmts && !(elseStmts?.any blockMayReturnEarly) then
              `(Qed.Server.srvLetEq (($br : _ × Option Unit).1) (fun $sNext:ident $(← freshIdent "_srvEq"):ident => $cont))
            else `(Qed.Server.srvSeq $br (fun $sNext:ident => $cont))
    | .async _ => `(Qed.Server.srvSeqM $br (fun _ => $(← recSame ctx rest)))

@[noinline]
private def lowerReturn (mode : BlockMode) (ctx : LowerCtx) (stmt : Syntax) : LowerM Term := do
  if (stmt.getArg 1).getNumArgs == 0 then liftM <| mkOkLeaf mode ctx (← `(()))
  else
    let retExpr := (stmt.getArg 1).getArg 0; let uRet := unwrapParens1 retExpr
    match mode with
    | .pure .. => if exprHasAwait retExpr && !uRet.isOfKind ``qedUnwrap then throwErrorAt retExpr "`await` cannot be used inside a synchronous or `atomic` block"
    | .async _ =>
        if uRet.getKind == ``qedAwait && !(unwrapParens1 (uRet.getArg 1)).isOfKind ``qedUnwrap then
          unless ctx.hasFallible do throwErrorAt retExpr s!"`return await ...` without `catch` requires `{ctx.fnName}` to have a fallible `T!` return type"
          let (callTerm, steps) ← lowerExprCollectingHoists ctx .val (uRet.getArg 1); let rawId ← freshIdent "_retAw"; let errTy ← liftM <| errTyOf ctx
          let leaf ← match ctx.innerOptTy? with
            | some innerTy => `($callTerm >>= fun $rawId:ident => Pure.pure (some (match $rawId:ident with | Except.ok _v => Except.ok (Qed.Server.SrvLiftOpt.liftOpt (Inner := $innerTy) _v) | Except.error _e => Except.error (Qed.Server.SrvErr.ofApi (E := $errTy) _e))))
            | none => `($callTerm >>= fun $rawId:ident => Pure.pure (some (Qed.Server.SrvUnwrap.unwrap (E := $errTy) $rawId)))
          return ← wrapHoists mode ctx steps leaf
    let isFail := isFailCall retExpr
    if isFail && !ctx.hasFallible then throwErrorAt retExpr s!"`fail(...)` can only be returned from a fallible `T!` function (`{ctx.fnName}` is not declared `-> ...!`)"
    let (term, steps) ← lowerExprCollectingHoists ctx .val retExpr
    wrapHoists mode ctx steps (← liftM <| (if isFail then mkErrLeaf else mkOkLeaf) mode ctx term)

@[noinline]
private def lowerLet (mode : BlockMode) (ctx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (recBlock : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let xStx := stmt.getArg 1; let rhsRaw := stmt.getArg 4
  if let some catchNode ← extractSrvLetCatch? (stmt.getArg 5) then
    if catchNode.getKind == `Qed.Lang.catchArms then throwErrorAt catchNode "multi-arm `catch: case ...` is for client components; in server functions use `catch err:`"
    let rhsStx := unwrapParens1 rhsRaw; let binderStx := catchNode.getArg 0; let catchStmts := suiteStmts (catchNode.getArg 2)
    let errId : Ident := if binderStx.isIdent then ⟨binderStx⟩ else mkIdent `_srvCatchErr
    let catchCtx := pushOptLocal ctx binderStx; let okTerm ← recBlock (pushOptLocal ctx xStx) rest
    let (scrutTerm, steps, awaitCall?) : Term × Array HoistedStep × Option (Term × Ident) ←
      if rhsStx.getKind == ``qedAwait then
        match mode with
        | .pure .. => throwErrorAt rhsRaw "`await` cannot be used inside a synchronous or `atomic` block"
        | .async _ => let (c, s) ← lowerExprCollectingHoists ctx .val (rhsStx.getArg 1); let r ← freshIdent "_catchAw"; pure (⟨r⟩, s, some (c, r))
      else let (r, s) ← lowerExprCollectingHoists ctx .val rhsStx; pure (r, s, none)
    let mkUnwrapMatch (errBody : Term) (okId : Ident) (okBody : Term) : CommandElabM Term :=
      `(match Qed.Server.SrvUnwrap.unwrap (E := Qed.Server.ApiError) $scrutTerm with | Except.error $errId:ident => $errBody | Except.ok $okId:ident => $okBody)
    let innerTerm ← if let some fbTerm ← lowerCatchFallback? catchCtx catchStmts then
        let okValId ← freshIdent "_catchOk"; bindLet mode xStx (← liftM <| mkUnwrapMatch fbTerm okValId ⟨okValId.raw⟩) okTerm
      else
        unless blockAlwaysReturns catchStmts do throwErrorAt stmt "the `catch` block must either `return` on all paths or end with a fallback value expression"
        liftM <| mkUnwrapMatch (← recBlock catchCtx catchStmts) (if xStx.isIdent then ⟨xStx⟩ else mkIdent `_srvDiscard) okTerm
    let awaitedTerm ← match awaitCall? with | some (c, r) => `($c >>= fun $r:ident => $innerTerm) | none => pure innerTerm
    wrapHoists mode ctx steps awaitedTerm
  else
    let (rhsTerm, steps) ← lowerExprCollectingHoists ctx .val rhsRaw
    let checkedRhs ← if steps.isEmpty then `(srvRejectUnhandledErr($rhsTerm)) else pure rhsTerm
    wrapHoists mode ctx steps (← bindLet mode xStx checkedRhs (← recBlock (pushOptLocal ctx xStx) rest))

@[noinline]
private def lowerPureMutationStmt (mode : BlockMode) (pCtx : LowerCtx) (sCur : Ident) (stmt : Syntax) (rest : Array Syntax)
    (recPure : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  rejectSrvAssignPredict stmt
  let lowerMut (lvalStx : Syntax) (steps : Array HoistedStep) (mkLeaf : Array LValStep → Term → LowerM Term) : LowerM Term := do
    let (rootField, pathSteps) ← parseLValPath pCtx lvalStx; let curRoot ← resolveStateFieldBase lvalStx pCtx rootField.getId
    let fNext ← freshIdent s!"_fld_{rootField.getId}_"; let hFNext ← freshIdent "_srvEq"
    let cont ← recPure (setPureOverride pCtx sCur rootField.getId.toString fNext) rest
    let chain ← withUpdatedPathCPS pathSteps 0 curRoot (mkLeaf pathSteps) fun updatedRaw => do
      let updatedRoot ← if pathSteps.isEmpty then `(srvTypedAs(($sCur).$rootField:ident, $updatedRaw)) else pure updatedRaw
      `(Qed.Server.srvLetEq $updatedRoot (fun $fNext:ident $hFNext:ident => $cont))
    wrapHoists mode pCtx steps chain
  if stmt.getKind == ``qedStmtAssign then
    let opStr := ((stmt.getArg 1).reprint.getD "=").trimAscii.toString; let (rhsTerm, steps) ← lowerExprCollectingHoists pCtx .val (stmt.getArg 2)
    lowerMut (stmt.getArg 0) steps fun pathSteps curLeaf => do
      let val ← match opStr with
        | "=" => pure rhsTerm
        | "+=" => `(Qed.Lang.QedVal.val $curLeaf + Qed.Lang.QedVal.val $rhsTerm)
        | "-=" => `(Qed.Lang.QedVal.val $curLeaf - Qed.Lang.QedVal.val $rhsTerm)
        | _ => throwErrorAt (stmt.getArg 1) s!"unsupported assignment operator `{opStr}`"
      if pathSteps.isEmpty then `(srvAutoField($val)) else pure val
  else if let some (targetStx, elemStx) := matchPushCall? (stmt.getArg 0) then
    let (elemTerm, steps) ← lowerExprCollectingHoists pCtx .val elemStx; lowerMut targetStx steps fun _ curArr => `(($curArr).push (srvAutoField($elemTerm)))
  else
    let some (targetStx, keyStx) := matchRemoveCall? (stmt.getArg 0) | unreachable!
    let (keyTerm, steps) ← lowerExprCollectingHoists pCtx .val keyStx; lowerMut targetStx steps fun _ curDict => `(Qed.Dict.remove $curDict $keyTerm)

@[noinline]
private def lowerAtomicStmt (aCtx : LowerCtx) (stateTyTerm? : Option Term) (stmt : Syntax) (rest : Array Syntax)
    (lowerPure : LowerCtx → Ident → Ident → Array Syntax → LowerM Term) (lowerRest : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let atomStmts := suiteStmts (stmt.getArg 2); let alwaysRet := blockAlwaysReturns atomStmts
  let exportedIds := if alwaysRet then #[] else atomStmts.foldl (init := #[]) fun ids s =>
    if s.getKind == ``qedStmtLet && (s.getArg 1).isIdent then
      let id : Ident := ⟨s.getArg 1⟩; let nm := id.getId.eraseMacroScopes.toString
      if rest.any (stxMentionsVar nm) then ids.filter (·.getId.eraseMacroScopes.toString != nm) |>.push id else ids
    else ids
  let (atomCtx, bodyStmts, isFinish, mkOnResult) : LowerCtx × Array Syntax × Bool × (Term → LowerM Term) ←
    if alwaysRet then pure (aCtx, atomStmts, true, fun res => `(Pure.pure (some $res)))
    else if !exportedIds.isEmpty then
      let hasEarlyOk := atomStmts.any (stxAny fun s => s.getKind == ``qedStmtReturn && ((s.getArg 1).getNumArgs == 0 || !isFailCall ((s.getArg 1).getArg 0)))
      let expTuple ← buildTupleVal (exportedIds.map (⟨·.raw⟩))
      let exportStmt := Syntax.node (.fromRef stmt) `Qed.Server.atomicExport #[expTuple.raw]
      pure (if hasEarlyOk then { aCtx with wrapReturnSumInl := true } else { aCtx with innerOptTy? := none }, atomStmts.push exportStmt, true, fun res => do
        let cont ← lowerRest { aCtx with locals := aCtx.locals ++ exportedIds.map (·.getId.eraseMacroScopes.toString) } rest
        if hasEarlyOk then `(match $res:term with | Except.error _e => Pure.pure (some (Except.error _e)) | Except.ok (Sum.inl _v) => Pure.pure (some (Except.ok _v)) | Except.ok (Sum.inr $expTuple:term) => $cont)
        else `(match $res:term with | Except.error _e => Pure.pure (some (Except.error _e)) | Except.ok $expTuple:term => $cont))
    else pure (aCtx, atomStmts, false, fun early => do `(match $early:term with | some _r => Pure.pure (some _r) | none => $(← lowerRest aCtx rest)))
  let some stateTyTerm := stateTyTerm? | throwErrorAt stmt "`atomic` is only valid in a `server` with `state` declarations"
  if blockHasAwait bodyStmts then throwErrorAt stmt "cannot use `await` inside an `atomic` block; perform external I/O outside `atomic` so shared locks never span network calls"
  let s0Id ← freshIdent "_sAtom"; let hasEmit := blockHasEmit bodyStmts; let es0Id ← freshIdent "_es0"
  let savedMut := (← get).mutated; modify fun s => { s with mutated := #[] }
  let rawAtomBody ← lowerPure (if hasEmit then { atomCtx with emitAcc? := some es0Id } else atomCtx) s0Id s0Id bodyStmts
  let atomBody ← if hasEmit then `(let $es0Id:ident : List Qed.Server.WsEmit := []; $rawAtomBody) else pure rawAtomBody
  let atomMut := (← get).mutated; modify fun s => { s with mutated := savedMut ++ atomMut.filter (!savedMut.contains ·) }
  let readOnly := atomMut.isEmpty
  let committed ← match isFinish, hasEmit, readOnly with
    | true, true, _ => `(Qed.Server.srvFinishEmit $s0Id $atomBody) | false, true, _ => `(Qed.Server.srvAtomicCommitEmit $s0Id $atomBody)
    | true, false, _ => `(Qed.Server.srvFinish $s0Id $atomBody) | false, false, true => pure atomBody | false, false, false => `(Qed.Server.srvAtomicCommit $s0Id $atomBody)
  let bindId ← freshIdent (if hasEmit then "_atomPair" else "_atomRes")
  let resTerm ← if hasEmit then `(($bindId).1) else pure ⟨bindId.raw⟩
  let onResBody ← mkOnResult resTerm
  liftM <| mkAtomicRunTerm s0Id stateTyTerm committed readOnly hasEmit (some (bindId, fun _ => pure onResBody))

@[noinline]
private def lowerSideEffectCall (ctx : LowerCtx) (stmt : Syntax) (fn : String) (rawArgs : Array Syntax) : LowerM (Name × Term × Array HoistedStep) := do
  let optSome (named : Array (String × Syntax)) (k : String) (ty : CommandElabM Term) : LowerM Term :=
    match findNamedArg? named k with | some s => do `(some ($(← lowerExpr ctx .val s) : $(← liftM ty))) | none => `(none)
  if fn == "send" then
    unless ctx.isStreamRoute do throwErrorAt stmt "`send(...)` is only available inside `stream \"/...\":` routes"
    let (argT, steps) ← withCollectedHoists do
      let (pos, named) ← splitCallArgs "send" rawArgs (some ["data", "event", "id", "retry"]) (errRef := stmt)
      let some dataStx := pos[0]? |>.orElse (fun _ => findNamedArg? named "data") | throwErrorAt stmt "`send(data[, event = ..., id = ..., retry = ...])` requires an event data string"
      if pos.size > 1 then throwErrorAt stmt "`send(...)` takes one positional `data` argument; pass `event = ...`, `id = ...`, or `retry = ...` as named arguments"
      `({ data := $(← lowerExpr ctx .val dataStx), event := $(← optSome named "event" `(String)), id := $(← optSome named "id" `(String)), retry := $(← optSome named "retry" `(Nat)) : Qed.Server.SseEvent })
    return (`Qed.Server.MonadServer.sendSse, argT, steps)
  let isClear := fn == "clearCookie"
  let (argT, steps) ← withCollectedHoists do
    let (pos, named) ← splitCallArgs fn rawArgs (if isClear then none else some ["name", "value", "path", "httpOnly", "secure", "sameSite", "maxAge", "domain"]) (errRef := stmt)
    let findN := findNamedArg? named
    let optVal (k : String) (d : CommandElabM Term) : LowerM Term := match findN k with | some s => lowerExpr ctx .val s | none => liftM d
    let some nameStx := pos[0]? |>.orElse (fun _ => findN "name")
      | throwErrorAt stmt (if isClear then "`clearCookie(name[, path = \"/\"])` requires a cookie name" else "`setCookie(name, value, ...)` requires a cookie name")
    if isClear then
      let pathT ← match (findN "path").orElse (fun _ => pos[1]?) with | some s => lowerExpr ctx .val s | none => `("/")
      `(Qed.Server.SetCookie.clear $(← lowerExpr ctx .val nameStx) $pathT)
    else
      let some valStx := pos[1]? |>.orElse (fun _ => findN "value") | throwErrorAt stmt "`setCookie(name, value, ...)` requires a cookie value"
      `({ name := $(← lowerExpr ctx .val nameStx), value := $(← lowerExpr ctx .val valStx), path := $(← optVal "path" `("/")),
          httpOnly := $(← optVal "httpOnly" `(true)), sameSite := ($(← optVal "sameSite" `(Qed.Server.SameSite.lax)) : Qed.Server.SameSite),
          secure := $(← optVal "secure" `(false)), maxAge? := $(← optSome named "maxAge" `(Nat)), domain? := $(← optSome named "domain" `(String)) : Qed.Server.SetCookie })
  return (`Qed.Server.MonadServer.setCookie, argT, steps)

@[noinline]
private def lowerTxStmt (aCtx : LowerCtx) (stmt aliasRef : Syntax) (aliasName : String) (txStmts rest : Array Syntax)
    (recAsync : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let some (_, dbInfo) := aCtx.dbs.find? (·.1 == aliasName)
    | throwErrorAt aliasRef s!"unknown database alias `{aliasName}` in `transaction` (declared `use` databases: [{String.intercalate ", " (aCtx.dbs.toList.map Prod.fst)}])"
  if let some (curAlias, _) := aCtx.activeDbTx? then throwErrorAt stmt s!"nested database transactions are not supported (already inside `{curAlias}.transaction:`)"
  let txId ← freshIdent "_dbTxId"; let bodyTerm ← recAsync { aCtx with activeDbTx? := some (aliasName, txId) } txStmts
  let txRun ← `(Qed.Server.dbRunTx $(mkIdentFrom aliasRef dbInfo.configConst) (fun ($txId:ident : UInt64) => $bodyTerm))
  modify fun s => { s with dbWrite := true }
  if rest.isEmpty || blockAlwaysReturns txStmts then return txRun else `(Qed.Server.srvSeqM $txRun (fun _ => $(← recAsync aCtx rest)))

private partial def lowerBlock (isPure inAtomic : Bool) (s₀ sCur : Ident) (stateTyTerm? : Option Term)
    (ctx : LowerCtx) (stmts : Array Syntax) : LowerM Term := do
  let curOverrides := getPureOverrides ctx
  let mode ← if isPure then pure (BlockMode.pure inAtomic s₀ sCur (← liftM <| materializeState sCur curOverrides)) else pure (BlockMode.async stateTyTerm?)
  if stmts.isEmpty then return ← liftM <| mkEmptyLeaf mode ctx
  let stmt := stmts[0]!; let rest := stmts.extract 1 stmts.size; let k := stmt.getKind
  let bCtx := { ctx with stateRule := if ctx.stateFields.isEmpty then .statelessServer else if isPure then .pureStep sCur curOverrides else .forbidAsyncOutsideAtomic, allowAwait := !isPure }
  let recSame := fun c st => lowerBlock isPure inAtomic s₀ sCur stateTyTerm? c st
  let recWithState := fun c s st => lowerBlock isPure inAtomic s₀ s stateTyTerm? c st
  if k == ``qedStmtPass then recSame bCtx rest
  else if let some (chId, rawArgs) := matchSrvEmitStmt? stmt then
    let (emitTerm, steps) ← lowerEmitCall bCtx stmt chId rawArgs
    let body ← match mode with
      | .pure .. =>
          let some esId := bCtx.emitAcc? | throwErrorAt stmt "internal error: `emit` accumulator not initialized"
          let esNext ← freshIdent "_es"
          `(let $esNext:ident : List Qed.Server.WsEmit := $esId ++ [$emitTerm]; $(← recSame { bCtx with emitAcc? := some esNext } rest))
      | .async _ =>
          let evId ← freshIdent "_wsEv"
          `(let $evId:ident := $emitTerm; Qed.Server.MonadServer.wsBroadcast ($evId).topic ($evId).payload >>= fun _ => $(← recSame bCtx rest))
    wrapHoists mode bCtx steps body
  else if k == `Qed.Server.atomicExport && isPure then
    let expTerm : Term := ⟨stmt.getArg 0⟩
    let wrapped ← if bCtx.wrapReturnSumInl then `(Except.ok (Sum.inr $expTerm)) else `(Except.ok $expTerm)
    let .pure _ _ _ matCur := mode | unreachable!
    liftM <| mkPureLeaf bCtx matCur (← `(some $wrapped))
  else if let some (fn, rawArgs) := (matchNamedStmtCall? stmt).filter fun (n, _) => n == "setCookie" || n == "clearCookie" || n == "send" then
    if isPure then throwErrorAt stmt (if fn == "send" then "cannot call `send(...)` inside an `atomic:` block; emit SSE events outside `atomic:`" else "cannot call `setCookie`/`clearCookie` inside an `atomic:` block; emit cookies outside `atomic:`")
    let (effNm, argT, steps) ← lowerSideEffectCall bCtx stmt fn rawArgs
    wrapHoists mode bCtx steps (← `($(mkIdent effNm) $argT >>= fun _ => $(← recSame bCtx rest)))
  else if let some (aliasRef, aliasName, txStmts) := matchTxStmt? stmt then
    if isPure then throwErrorAt stmt "cannot start a database `transaction` inside an `atomic:` block; run database transactions outside `atomic:`"
    lowerTxStmt bCtx stmt aliasRef aliasName txStmts rest recSame
  else if k == ``qedStmtAtomic then
    if isPure then
      if inAtomic then throwErrorAt stmt "nested `atomic` blocks are forbidden"
      else if ctx.stateFields.isEmpty then throwErrorAt stmt "`atomic` is only valid in a `server` with `state` declarations"
      else throwErrorAt stmt s!"redundant `atomic` block: `{ctx.fnName}` has no `await` calls, so it already executes atomically"
    else lowerAtomicStmt bCtx stateTyTerm? stmt rest (fun c s0 s st => lowerBlock true true s0 s none c st) recSame
  else if k == ``qedStmtReturn then lowerReturn mode bCtx stmt
  else if k == ``qedStmtLet then lowerLet mode bCtx stmt rest recSame
  else if let some targetStx := (if k == ``qedStmtAssign then some (stmt.getArg 0) else if k == ``qedStmtExpr then ((matchPushCall? (stmt.getArg 0)).orElse fun _ => matchRemoveCall? (stmt.getArg 0)).map Prod.fst else none) then
    if isPure then lowerPureMutationStmt mode bCtx sCur stmt rest recSame
    else
      rejectSrvAssignPredict stmt; let _ ← parseLValPath bCtx targetStx
      throwErrorAt stmt s!"cannot mutate server state outside an `atomic:` block in `{ctx.fnName}` because `{ctx.fnName}` uses `await`"
  else if k == ``qedStmtExpr then
    let eStx := stmt.getArg 0; let (eTerm, steps) ← lowerExprCollectingHoists bCtx .val eStx
    let valTerm ← if isBareUnwrapExpr (!isPure) eStx then pure eTerm else `(srvEnsureUnit($eTerm))
    wrapHoists mode bCtx steps (← bindLet mode Syntax.missing valTerm (← recSame bCtx rest))
  else if k == ``qedStmtIf then
    let (condTerm, steps) ← lowerExprCollectingHoists bCtx .propGuard (stmt.getArg 1); let hGuard ← freshIdent "_srvG"
    wrapHoists mode bCtx steps (← lowerBranch mode bCtx rest (suiteStmts (stmt.getArg 3)) bCtx (desugarElifs (stmt.getArg 4).getArgs (stmt.getArg 5)) isPure
      (fun t e => `(if $hGuard:ident : $condTerm then $t else $e)) recSame recWithState)
  else if k == ``qedStmtIfLet then
    let patStx := stmt.getArg 2; let patTerm ← liftMacroM (lowerQedPat patStx)
    let (scrutTerm, steps) ← lowerExprCollectingHoists bCtx .val (stmt.getArg 4); let hMatch ← freshIdent "_srvM"
    wrapHoists mode bCtx steps (← lowerBranch mode bCtx rest (suiteStmts (stmt.getArg 6)) { bCtx with locals := bCtx.locals ++ (collectQedPatIds patStx).map (·.toString) }
      (extractElseSuite (stmt.getArg 7)) false (fun t e => `(match $hMatch:ident : $scrutTerm:term with | $patTerm => $t | _ => $e)) recSame recWithState)
  else if k == ``qedStmtMatch then
    let (matchT, allSteps) ← lowerMatchScrutineesAndAlts bCtx stmt rest recSame; wrapHoists mode bCtx allSteps matchT
  else
    let sn := stxSnippet stmt
    throwErrorAt stmt s!"unsupported statement{if sn.isEmpty then s!"({k})" else s!" `{sn}`"} in {if isPure then "server" else "async server"} function `{ctx.fnName}`"

def lowerPureBlock (ctx : LowerCtx) (inAtomic : Bool) (s₀ sCur : Ident) (stmts : Array Syntax) : LowerM Term := lowerBlock true inAtomic s₀ sCur none ctx stmts
def lowerAsyncBlock (ctx : LowerCtx) (stateTyTerm? : Option Term) (stmts : Array Syntax) : LowerM Term := lowerBlock false false (mkIdent `_unused) (mkIdent `_unused) stateTyTerm? ctx stmts

end BlockLowering
end Qed.Server
