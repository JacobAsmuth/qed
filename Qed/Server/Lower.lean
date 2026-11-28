import Lean
import Qed.Server.Core
import Qed.Server.Syntax
import Qed.Server.Registry
import Qed.Server.Db.QueryLower

namespace Qed.Server
open Qed.Lang

/-! ## Compile-Time Unhandled-Error Guards (`srvEnsureUnit` & `srvRejectUnhandledErr`) -/

syntax (name := srvEnsureUnitStx) "srvEnsureUnit(" term ")" : term
syntax (name := srvRejectErrStx)  "srvRejectUnhandledErr(" term ")" : term
syntax (name := srvAwaitPlainStx) "srvAwaitPlain(" term ")" : term

section Guards
open Lean Meta Elab Term

private def isApiErrExcept (ty : Expr) : MetaM Bool := do
  if ty.isAppOfArity ``Except 2 then return (← whnf ty.getAppArgs[0]!).isConstOf ``ApiError
  return false

private def elabGuardTerm (stx : Syntax) (expectedType? : Option Expr) : TermElabM (Expr × Expr) := do
  let e ← elabTerm (stx.getArg 1) expectedType?; synthesizeSyntheticMVarsNoPostponing
  return (e, ← whnf (← inferType e))

@[term_elab srvEnsureUnitStx] def elabSrvEnsureUnit : TermElab := fun stx _ => do
  let (e, ty) ← elabGuardTerm stx none
  if ty.isAppOf ``Except || ty.isAppOf ``Option then
    throwErrorAt stx m!"unhandled fallible or optional expression of type `{← ppExpr ty}`; append `?` to propagate or `catch` to handle"
  ensureHasType (mkConst ``Unit) e

@[term_elab srvRejectErrStx] def elabSrvRejectErr : TermElab := fun stx expectedType? => do
  let (e, ty) ← elabGuardTerm stx expectedType?
  if ← isApiErrExcept ty then
    throwErrorAt stx m!"unhandled fallible `T!` value of type `{← ppExpr ty}`; append `?` to propagate errors or use `catch` to recover"
  return e

@[term_elab srvAwaitPlainStx] def elabSrvAwaitPlain : TermElab := fun stx expectedType? => do
  let (e, ty) ← elabGuardTerm stx expectedType?
  if let some inner := ty.getAppArgs.back? then
    if ← isApiErrExcept (← whnf inner) then
      throwErrorAt stx "unhandled fallible `await` expression; append `?` to propagate errors or use `let x = await ... catch err:` to handle them inline"
  return e

end Guards

/-! ## Persistent Registries & Lowering State -/

export Qed (ServerMethodInfo ServerInfo serverRegistry)

inductive StateAccessRule where
  | pureStep (stateVar : Lean.Ident) (overrides : Array (String × Lean.Ident) := #[])
  | invariantProp (curVar oldVar : Lean.Ident) (inOld : Bool)
  | forbidAsyncOutsideAtomic | forbidInRequires | forbidInEnsures | statelessServer

structure SrvChanSig where
  name : String
  mkEmitId : Lean.Ident
  paramCount : Nat
  hasEnsures : Bool

structure SrvHelperSig where
  name : String
  defId : Lean.Ident
  minParamCount : Nat
  paramCount : Nat
  isMonadic : Bool
  isFallible : Bool := true
  takesAtomic : Bool
  takesEnvs : Bool := true
  takesCtx : Bool := true
  mutatesState : Bool
  dbWrite : Bool
  hasCookieOp : Bool := false

structure LowerCtx where
  fnName : String
  stateFields : Array String := #[]
  envVars : Array String := #[]
  envIdents : Array Lean.Ident := #[]
  locals : Array String := #[]
  stateRule : StateAccessRule := .statelessServer
  allowAwait : Bool := false
  allowUnwrap : Bool := false
  hasFallible : Bool := false
  innerOptTy? : Option Lean.Term := none
  forbidCtxEnv : Bool := false
  domainErrTy? : Option Lean.Term := none
  channels : Array SrvChanSig := #[]
  helpers : Array SrvHelperSig := #[]
  emitAcc? : Option Lean.Ident := none
  wrapReturnSumInl : Bool := false
  dbs : Array (String × DatabaseInfo) := #[]
  services : Array (String × ServiceInfo) := #[]
  ctxTerm? : Option Lean.Term := none
  activeDbTx? : Option (String × Lean.Ident) := none
  txDbAliases : Array (String × DatabaseInfo × Lean.Term) := #[]
  isHttpRoute : Bool := false
  isStreamRoute : Bool := false
  mutLocals : Array Lean.Ident := #[]
  loopMuts? : Option (Array Lean.Ident) := none

inductive HoistedStep where
  | awaitUnwrap (ref : Lean.Syntax) (tmp : Lean.Ident) (callTerm : Lean.Term)
  | awaitPlain  (ref : Lean.Syntax) (tmp : Lean.Ident) (callTerm : Lean.Term)
  | pureUnwrap  (tmp : Lean.Ident) (valTerm : Lean.Term)

structure LowerState where
  nextId : Nat := 0
  mutated : Array String := #[]
  dbWrite : Bool := false
  hasCookieOp : Bool := false
  extRoots : Array Lean.Name := #[]
  hoisted : Array HoistedStep := #[]

abbrev LowerM := StateRefT LowerState Lean.Elab.Command.CommandElabM

private inductive LValStep where | field (id : Lean.Ident) | index (idxTerm : Lean.Term)
private inductive BlockMode where | pure (inAtomic : Bool) (s₀ sCur : Lean.Ident) | async (stateTyTerm? : Option Lean.Term) | infallibleAsync

@[noinline] private def lowerErr {α : Type} (ref : Lean.Syntax) (msg : String) : LowerM α := Lean.throwErrorAt ref msg
@[noinline] private def foldlLower {α β : Type} (xs : Array α) (init : β) (f : β → α → LowerM β) : LowerM β :=
  let rec go : Nat → β → LowerM β | 0, acc => pure acc | r + 1, acc => do let i := xs.size - (r + 1); if h : i < xs.size then go r (← f acc xs[i]) else pure acc
  go xs.size init
@[noinline] private def foldrLower {α β : Type} (xs : Array α) (init : β) (f : α → β → LowerM β) : LowerM β :=
  let rec go : Nat → β → LowerM β | 0, acc => pure acc | j + 1, acc => do if h : j < xs.size then go j (← f xs[j] acc) else pure acc
  go xs.size init
@[noinline] private def mapLower {α β : Type} (xs : Array α) (f : α → LowerM β) : LowerM (Array β) :=
  foldlLower xs (Array.mkEmpty xs.size) fun acc x => return acc.push (← f x)

private def freshIdent (pfx : String) : LowerM Lean.Ident := do
  let n := (← get).nextId; modify fun s => { s with nextId := n + 1 }
  return Lean.mkIdent (Lean.Name.mkSimple s!"{pfx}{n}")

/-! ## Static AST Queries -/

private def matchTxStmt? (stx : Lean.Syntax) : Option (Lean.Syntax × String × Option Lean.Ident × Array Lean.Syntax) :=
  if stx.getKind == ``qedStmtDbTransaction then
    let dotStx := stx.getArg 0; let idNode := if dotStx.isIdent then dotStx else dotStx.getArg 0
    let aliasName := match idNode.getId.eraseMacroScopes with | .str (.str .anonymous a) "transaction" => a | _ => ""
    let optAs := stx.getArg 1
    some (dotStx, aliasName, if optAs.getNumArgs == 2 then some ⟨optAs.getArg 1⟩ else none, suiteStmts (stx.getArg 3))
  else none

private def matchNamedStmtCall? (stx : Lean.Syntax) : Option (String × Array Lean.Syntax) := do
  guard (stx.getKind == ``qedStmtExpr)
  let e := unwrapParens1 (stx.getArg 0); guard (e.getKind == ``qedCall)
  match extractDottedChain? (e.getArg 0) with | some [nm] => some (nm, (e.getArg 2).getSepArgs) | _ => none

private def matchSrvEmitStmt? (stx : Lean.Syntax) : Option (Lean.Ident × Array Lean.Syntax) := do
  guard (stx.getKind == ``qedStmtExpr)
  let (chId, meth, rawArgs) ← matchIdentMethodCall? (stx.getArg 0); guard (meth == "emit"); return (chId, rawArgs)

def exprHasAwait (stx : Lean.Syntax) : Bool := stxAny (·.getKind == ``qedAwait) stx
def blockHasAwait (stmts : Array Lean.Syntax) : Bool :=
  stmts.any (stxAny fun s => s.getKind == ``qedAwait || (matchTxStmt? s).isSome ||
    (matchNamedStmtCall? s).any fun (nm, _) => nm == "setCookie" || nm == "clearCookie" || nm == "send")
def blockHasEmit (stmts : Array Lean.Syntax) : Bool := stmts.any (stxAny fun s => (matchSrvEmitStmt? s).isSome)
def blockHasAtomic (stmts : Array Lean.Syntax) : Bool := stmts.any (stxAny (·.getKind == ``qedStmtAtomic))

private def stmtChildSuites (stx : Lean.Syntax) : Array Lean.Syntax × Array (Array Lean.Name × Array Lean.Syntax) :=
  match stx.getKind with
  | ``qedStmtIf => (#[stx.getArg 1], #[(#[], suiteStmts (stx.getArg 3))] ++ (desugarElifs (stx.getArg 4).getArgs (stx.getArg 5)).elim #[] fun es => #[(#[], es)])
  | ``qedStmtIfLet => (#[stx.getArg 4], #[(collectQedPatIds (stx.getArg 2), suiteStmts (stx.getArg 6))] ++ (desugarElifs (stx.getArg 7).getArgs (stx.getArg 8)).elim #[] fun es => #[(#[], es)])
  | ``qedStmtMatch => ((stx.getArg 1).getSepArgs, (stx.getArg 3).getArgs.map fun c => (collectCasePatIds (extractCasePatAlts (c.getArg 1)), suiteStmts (c.getArg 3)))
  | ``qedStmtFor => (#[stx.getArg 3], #[(collectLetBinderIds (stx.getArg 1), suiteStmts (stx.getArg 5))])
  | ``qedStmtAtomic => (#[], #[(#[], suiteStmts (stx.getArg 2))])
  | ``qedStmtDbTransaction => (#[], #[(#[], suiteStmts (stx.getArg 3))])
  | ``qedStmtLetElse => (#[stx.getArg 3], #[(#[], extractLetElseStmts stx)])
  | _ => (#[], #[])

mutual
  partial def stmtAlwaysTerminates (allowLoopExit : Bool) (stx : Lean.Syntax) : Bool :=
    match stx.getKind with
    | ``qedStmtReturn => true | ``qedStmtBreak | ``qedStmtContinue => allowLoopExit
    | ``qedStmtAtomic => blockAlwaysTerminates allowLoopExit (suiteStmts (stx.getArg 2))
    | ``qedStmtDbTransaction => blockAlwaysTerminates false (suiteStmts (stx.getArg 3))
    | ``qedStmtIf | ``qedStmtIfLet => let ss := (stmtChildSuites stx).2; ss.size == 2 && ss.all fun (_, bs) => blockAlwaysTerminates allowLoopExit bs
    | ``qedStmtMatch => let ss := (stmtChildSuites stx).2; !ss.isEmpty && ss.all fun (_, bs) => blockAlwaysTerminates allowLoopExit bs
    | _ => false
  partial def blockAlwaysTerminates (allowLoopExit : Bool) (stmts : Array Lean.Syntax) : Bool := stmts.any (stmtAlwaysTerminates allowLoopExit)
end
abbrev blockAlwaysReturns := blockAlwaysTerminates false

def ensureUnitReturn (ref : Lean.Syntax) (stmts : Array Lean.Syntax) : Array Lean.Syntax :=
  if blockAlwaysReturns stmts then stmts
  else let i := Lean.SourceInfo.fromRef ref; stmts.push (Lean.Syntax.node i ``qedStmtReturn #[Lean.Syntax.atom i "return", Lean.Syntax.node i Lean.nullKind #[]])

private def knownQMethodSet : Std.HashSet String :=
  #["toNat?", "toInt?", "head?", "back?", "getLast?", "get?", "find?", "findIdx?", "findSome?", "indexOf?",
    "str?", "nat?", "int?", "bool?", "num?", "arr?", "obj?", "strAt?", "natAt?", "intAt?", "boolAt?", "pathStr?",
    "parse?", "decode?", "decodeUrl?", "decodeString?", "fromUTF8?", "fromIso?", "parseNat?", "parseInt?",
    "lookup?", "getElem?", "maxAge?", "ofString?", "sqlIdent?"].foldl (·.insert ·) {}

private def leafOfDottedStr (s : String) : String := match s.splitOn "." |>.reverse with | h :: _ => h | [] => s

partial def exprHasUnwrapWith (knownQ boundLocals : Std.HashSet String) (stx : Lean.Syntax) : Bool :=
  match stx.getKind with
  | ``qedUnwrap => true | ``qedDotIdent | ``qedLam1 | ``qedLamN | ``qedAllIn | ``qedAnyIn | ``qedAllVars | ``qedAnyVars => false
  | ``qedIdent => let s := (stx.getArg 0).getId.toString; s.endsWith "?" && !knownQ.contains (leafOfDottedStr s) && !boundLocals.contains s
  | ``qedProj => ((stx.getArg 2).isIdent && let f := (stx.getArg 2).getId.toString; f.endsWith "?" && !knownQ.contains f) || exprHasUnwrapWith knownQ boundLocals (stx.getArg 0)
  | _ => stx.getArgs.any (exprHasUnwrapWith knownQ boundLocals)

def exprHasUnwrap (stx : Lean.Syntax) : Bool := exprHasUnwrapWith knownQMethodSet {} stx

mutual
  partial def stmtMayReturnEarly (stx : Lean.Syntax) : Bool :=
    match stx.getKind with
    | ``qedStmtReturn | ``qedStmtAtomic | ``qedStmtDbTransaction | ``qedStmtLetElse => true
    | ``qedStmtLet => (stx.getArg 5).getNumArgs > 0 || exprHasUnwrap (stx.getArg 4)
    | ``qedStmtIf | ``qedStmtIfLet | ``qedStmtMatch => let (es, suites) := stmtChildSuites stx; es.any exprHasUnwrap || suites.any fun (_, bs) => blockMayReturnEarly bs
    | _ => exprHasUnwrap stx
  partial def blockMayReturnEarly (stmts : Array Lean.Syntax) : Bool := stmts.any stmtMayReturnEarly
end

/-! ## Expression Lowering (`lowerExpr`) -/

section ExprLowering
open Lean Elab Command

private initialize importedQNamesCache : IO.Ref (Name × Std.HashSet String) ← IO.mkRef (.anonymous, {})

private def userQLeaf? (env : Environment) (n : Name) : Option String :=
  match n with
  | .str _ leaf => if leaf.endsWith "?" && !Qed.Diag.isToolchainRoot (Qed.Diag.modRootOf env n env.header.mainModule) (includeQed := true) then some leaf else none
  | _ => none

def getKnownQLeafNames : CommandElabM (Std.HashSet String) := do
  let env ← getEnv; let mod := env.header.mainModule; let (cMod, impSet) ← importedQNamesCache.get
  let base ← if cMod == mod then pure impSet else do
    let s := env.constants.map₁.fold (init := knownQMethodSet) fun acc n _ => match userQLeaf? env n with | some l => acc.insert l | none => acc
    importedQNamesCache.set (mod, s); pure s
  return env.constants.map₂.foldl (init := base) fun acc n _ => match userQLeaf? env n with | some l => acc.insert l | none => acc

private partial def stmtsHaveUnwrapAux (knownQ bound : Std.HashSet String) (stmts : Array Syntax) (i : Nat) : Bool :=
  if h : i < stmts.size then
    let st := stmts[i]; let hasE := exprHasUnwrapWith knownQ bound
    let addIds (ns : Array Name) (b : Std.HashSet String) := ns.foldl (fun acc n => acc.insert n.toString) b
    let (selfHas, nextBound) := match st.getKind with
      | ``qedStmtLet => (hasE (st.getArg 4) || hasE (st.getArg 5), addIds (collectLetBinderIds (st.getArg 1)) bound)
      | ``qedStmtLetMut => (hasE (st.getArg 5), bound.insert (st.getArg 2).getId.eraseMacroScopes.toString)
      | ``qedStmtLetElse | ``qedStmtIf | ``qedStmtIfLet | ``qedStmtMatch | ``qedStmtFor | ``qedStmtAtomic | ``qedStmtDbTransaction =>
          let (es, suites) := stmtChildSuites st
          (es.any hasE || suites.any fun (ids, bs) => stmtsHaveUnwrapAux knownQ (addIds ids bound) bs 0,
           if st.getKind == ``qedStmtLetElse then addIds (collectQedPatIds (st.getArg 1)) bound else bound)
      | _ => (hasE st, bound)
    selfHas || stmtsHaveUnwrapAux knownQ nextBound stmts (i + 1)
  else false

def stmtsHaveUnwrapM (initLocals : Array String) (stmts : Array Syntax) : CommandElabM Bool := do
  return stmtsHaveUnwrapAux (← getKnownQLeafNames) (initLocals.foldl (·.insert ·) {}) stmts 0

private def peelTrailingQ (knownQ : Std.HashSet String) (isBound : String → Bool) (id : Ident) : Ident × Nat :=
  let rec go : List Char → Nat → List Char × Nat
    | '?' :: rest, q => let cand := String.ofList ('?' :: rest).reverse; if knownQ.contains (leafOfDottedStr cand) || isBound cand then ('?' :: rest, q) else go rest (q + 1)
    | rev, q => (rev, q)
  let (revBase, q) := go id.getId.toString.toList.reverse 0
  if q == 0 then (id, 0) else (mkIdentFrom id ((String.ofList revBase.reverse |>.splitOn ".").foldl Name.str .anonymous), q)

private def checkStateRead (ref : Syntax) (ctx : LowerCtx) (field : String) : LowerM Ident :=
  match ctx.stateRule with
  | .pureStep sv _ => return sv
  | .invariantProp curV oldV inOld => return if inOld then oldV else curV
  | .forbidAsyncOutsideAtomic => lowerErr ref s!"cannot access server state `{field}` outside an `atomic` block in `{ctx.fnName}` because `{ctx.fnName}` uses `await` (prevents TOCTOU data races across suspension points)"
  | .forbidInRequires => lowerErr ref s!"`requires` precondition in `{ctx.fnName}` cannot reference mutable server state `{field}`; check `{field}` inside the function body instead"
  | .forbidInEnsures => lowerErr ref s!"`ensures` postcondition in `{ctx.fnName}` cannot reference mutable server state `{field}`; state postconditions on `result` and parameters only"
  | .statelessServer => lowerErr ref s!"unknown identifier `{field}`"

private def resolveStateFieldBase (qctx : PureQuotCtx) (ref : Syntax) (ctx : LowerCtx) (field : Name) : LowerM Term := do
  let sv ← checkStateRead ref ctx field.toString
  if let .pureStep _ ovs := ctx.stateRule then if let some (_, ovId) := ovs.find? (·.1 == field.toString) then return ⟨mkIdentFrom ref ovId.getId⟩
  return qctx.runPure `(($sv).$(mkIdentFrom ref field):ident)

@[noinline] private def resolveDottedIdent (qctx : PureQuotCtx) (ref : Syntax) (ctx : LowerCtx) (id : Ident) : LowerM Term := do
  match id.getId.components with
  | [] => lowerErr ref "empty identifier"
  | root :: rest =>
      let rStr := root.toString
      if rest.isEmpty && (rStr == "true" || rStr == "false" || rStr == "none") then
        return mkCIdent (if rStr == "true" then ``Bool.true else if rStr == "false" then ``Bool.false else `Option.none)
      else if ctx.locals.contains rStr then return qctx.runPure (foldProjTerms ref ⟨mkIdentFrom ref root⟩ rest)
      else if rStr == "ctx" || ctx.envVars.contains rStr then
        if ctx.forbidCtxEnv then
          lowerErr ref s!"`ensures` postcondition in `{ctx.fnName}` cannot reference {if rest.isEmpty && rStr != "ctx" then s!"`env` binding `{rStr}`" else s!"`{rStr}`"} because client decoders re-verify `ensures` on the wire"
        return qctx.runPure (foldProjTerms ref ⟨mkIdentFrom ref root⟩ rest)
      else if ctx.stateFields.contains rStr then
        return qctx.runPure (foldProjTerms ref (← resolveStateFieldBase qctx ref ctx root) rest)
      else do
        if !rest.isEmpty then modify fun s => { s with extRoots := pushUnique s.extRoots root }
        return ⟨id⟩

private def checkAllowUnwrap (ref : Syntax) (ctx : LowerCtx)
    (msg : String := s!"operator `?` cannot be used here in `{ctx.fnName}` (return type must be `T!` or `T?`, and `?` cannot appear inside lambdas or invariants)") : LowerM Unit := do
  unless ctx.allowUnwrap do lowerErr ref msg

private def hoistPureUnwraps (ref : Syntax) (ctx : LowerCtx) (qCount : Nat) (term0 : Term) : LowerM Term := do
  if qCount == 0 then return term0
  checkAllowUnwrap ref ctx
  let rec go : Nat → Term → LowerM Term
    | 0, t => pure t
    | n + 1, t => do let tmp ← freshIdent "_srvUnw"; modify fun s => { s with hoisted := s.hoisted.push (.pureUnwrap tmp t) }; go n ⟨tmp⟩
  go qCount term0

private abbrev SrvExprM := ReaderT (LowerCtx × PureQuotCtx) LowerM
@[noinline] private def exprErr {α : Type} (ref : Syntax) (msg : String) : SrvExprM α := liftM (lowerErr ref msg)
@[noinline] private def mapSrvExpr {α β : Type} (xs : Array α) (f : α → SrvExprM β) : SrvExprM (Array β) := fun r => mapLower xs (f · r)

@[noinline] private partial def lowerJsonPayload (go : ExprMode → Syntax → SrvExprM Term) (stx : Syntax) : SrvExprM Term := do
  let qctx := (← read).2; let u := unwrapParens1 stx
  if u.getKind == ``qedRecLit && (u.getArg 1).getNumArgs != 2 then
    let pairs ← mapSrvExpr (u.getArg 2).getSepArgs fun f => do
      let op := (f.getArg 1).getAtomVal; if op != "=" then exprErr f s!"`{op}` is not allowed inside a JSON object literal"
      return qctx.runPure (Db.mkPairTerm (Syntax.mkStrLit (f.getArg 0).getId.eraseMacroScopes.toString) (← lowerJsonPayload go (f.getArg 2)))
    return qctx.runPure do Db.mkAppC `Qed.Json.obj #[← Db.mkListTerm pairs]
  else if u.getKind == ``qedArrLit then
    let elems ← mapSrvExpr (u.getArg 1).getSepArgs (lowerJsonPayload go)
    return qctx.runPure do Db.mkAppC `Qed.Json.arr #[← Db.mkListTerm elems]
  else return qctx.runPure (Db.mkAppC `Qed.ToJson.toJson #[← go .val stx])

@[noinline] private def lowerCheckedCall (stx : Syntax) (rawArgs : Array Syntax) (go : ExprMode → Syntax → SrvExprM Term)
    (kindLabel arityLabel dispName : String) (forbidInEnsures : Bool) (minP maxP : Nat)
    (dbWrite hasCookieOp mutatesState : Bool) (extRoot? : Option Name) (fnTerm : Term) (preArgs : Array Term) : SrvExprM Term := do
  let (ctx, qctx) ← read
  if ctx.forbidCtxEnv && forbidInEnsures then exprErr stx s!"{kindLabel} `{dispName}` cannot be called inside `ensures` or client-checked `requires`"
  if rawArgs.any (·.getKind == ``qedCallArgNamed) then exprErr stx s!"named arguments are not supported when calling {kindLabel} `{dispName}`"
  if rawArgs.size < minP || rawArgs.size > maxP then
    exprErr stx s!"{arityLabel} `{dispName}` expects {if minP == maxP then s!"{maxP}" else s!"{minP}..{maxP}"} argument(s), got {rawArgs.size}"
  let argTerms ← mapSrvExpr rawArgs fun ra => go .val (ra.getArg 0)
  if dbWrite || hasCookieOp || mutatesState || extRoot?.isSome then
    modify fun s => { s with
      dbWrite := s.dbWrite || dbWrite, hasCookieOp := s.hasCookieOp || hasCookieOp,
      mutated := if mutatesState then pushUnique s.mutated "__helper__" else s.mutated,
      extRoots := extRoot?.elim s.extRoots (pushUnique s.extRoots) }
  return qctx.runPure (mkAppTermsPure fnTerm (preArgs ++ argTerms))

private def ctxHasIdent (ctx : LowerCtx) (s : String) : Bool := ctx.locals.contains s || ctx.stateFields.contains s || ctx.envVars.contains s

@[noinline] private def lowerFailCall (stx : Syntax) (rawArgs : Array Syntax) (go : ExprMode → Syntax → SrvExprM Term) : SrvExprM Term := do
  let (ctx, qctx) ← read
  if rawArgs.any (·.getKind == ``qedCallArgNamed) then exprErr stx "`fail(...)` takes positional arguments `fail(.tag)`, `fail(.tag, msg)`, `fail(msg)`, or `fail(code, msg)`"
  if (rawArgs.size == 1 || rawArgs.size == 2) && (unwrapParens1 rawArgs[0]![0]).getKind == ``qedDotIdent then
    let uDot := unwrapParens1 rawArgs[0]![0]; let tagId : Ident := ⟨uDot.getArg 1⟩
    let some errTy := ctx.domainErrTy? | exprErr stx "internal error: missing inferred domain error type for `fail(.tag)`"
    let msgTerm ← if rawArgs.size == 2 then go .val rawArgs[1]![0] else pure (Syntax.mkStrLit tagId.getId.toString)
    let dotNode : Term := ⟨Syntax.node (.fromRef uDot) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef uDot) ".", tagId.raw]⟩
    return qctx.runPure `(Qed.Server.mkFailDom (ε := $errTy) ($dotNode : $errTy) $msgTerm)
  if ctx.domainErrTy?.isSome then exprErr stx "cannot mix typed `fail(.tag)` and untyped `fail(...)` inside the same function; use `fail(.tag, msg)`"
  if rawArgs.size == 1 then return qctx.runPure (Db.mkAppC `Qed.Server.mkFail1 #[← go .val rawArgs[0]![0]])
  if rawArgs.size == 2 then return qctx.runPure (Db.mkAppC `Qed.Server.mkFail2 #[← go .val rawArgs[0]![0], ← go .val rawArgs[1]![0]])
  exprErr stx "`fail(...)` expects `(.tag)`, `(.tag, msg)`, `(message)`, or `(code, message)`"

private def httpRespSpecs : Array (String × Name × Nat) := #[
  ("text", `Qed.Server.HttpResponse.text, 200), ("json", `Qed.Server.HttpResponse.jsonOf, 200),
  ("html", `Qed.Server.HttpResponse.html, 200), ("redirect", `Qed.Server.HttpResponse.redirect, 302), ("bytes", `Qed.Server.HttpResponse.bytes, 200)]

@[noinline] private def lowerHttpRespCall (stx : Syntax) (cstr : String) (ctorNm : Name) (defSt : Nat) (rawArgs : Array Syntax)
    (go : ExprMode → Syntax → SrvExprM Term) : SrvExprM Term := do
  let qctx := (← read).2; let (posArgs, namedArgs) ← splitCallArgs cstr rawArgs (some ["status"])
  let stT ← match findNamedArg? namedArgs "status" with | some s => go .val s | none => pure (Syntax.mkNumLit (toString defSt))
  if cstr == "bytes" then
    if posArgs.size != 2 then exprErr stx "`bytes(contentType, body[, status = 200])` expects a content type and body"
    return qctx.runPure (Db.mkAppC `Qed.Server.HttpResponse.bytes #[← go .val posArgs[0]!, ← go .val posArgs[1]!, stT])
  if posArgs.size != 1 then exprErr stx s!"`{cstr}(...)` expects one positional argument (and optional `status = ...`)"
  return qctx.runPure (Db.mkAppC ctorNm #[← (if cstr == "json" then lowerJsonPayload go posArgs[0]! else go .val posArgs[0]!), stT])

@[noinline] private def lowerSrvCallHook (stx calleeStx : Syntax) (rawArgs : Array Syntax) (mode : ExprMode) (go : ExprMode → Syntax → SrvExprM Term) : SrvExprM (Option Term) := do
  let (ctx, qctx) ← read
  if let some chain := extractDottedChain? calleeStx then if let some aliasName := chain.head? then
    let dbHit? : Option (DatabaseInfo × Option Term) := match ctx.txDbAliases.find? (·.1 == aliasName) with
      | some (_, dbi, txT) => some (dbi, some txT)
      | none => (ctx.dbs.find? (·.1 == aliasName)).map fun (_, dbi) => (dbi, ctx.activeDbTx?.bind fun (a, tid) => if a == aliasName then some ⟨tid.raw⟩ else none)
    if let some (dbInfo, txIdTerm?) := dbHit? then
      let stRef ← liftM (show LowerM (IO.Ref LowerState) from fun ref => pure ref)
      let (dbTerm, isWrite) ← liftM <| Db.lowerDbCall
        (fun locs e => ((go .val e).run ({ ctx with locals := ctx.locals ++ locs }, qctx)) stRef)
        ctx.fnName dbInfo stx chain rawArgs txIdTerm? (fun t => `(srvAutoField($t))) ctx.ctxTerm?
      if isWrite then modify fun s => { s with dbWrite := true }
      return some dbTerm
    if chain.length == 2 && !ctxHasIdent ctx aliasName then
      let methName := chain[1]!
      if aliasName == "Db" && methName == "postgres" then
        let (posArgs, namedArgs) ← splitCallArgs "Db.postgres" rawArgs (some ["ssrf_guard", "name"])
        if posArgs.size < 1 || posArgs.size > 2 then
          exprErr stx "`Db.postgres(url[, ssrf_guard = true][, name = \"dynamic_pg\"])` expects a PostgreSQL URL"
        let urlT ← go .val posArgs[0]!
        let ssrfT ← match findNamedArg? namedArgs "ssrf_guard" with
          | some s => go .val s
          | none => if let some p1 := posArgs[1]? then go .val p1 else pure (mkCIdent `Bool.true)
        let nameT ← match findNamedArg? namedArgs "name" with
          | some s => go .val s
          | none => pure (Syntax.mkStrLit "dynamic_pg")
        return some (qctx.runPure (Db.mkAppC `Qed.Server.Db.PgHandle.connect #[urlT, ssrfT, nameT]))
      let svcOpt? : Option (ServiceInfo × Bool) ← match ctx.services.find? (·.1 == aliasName) with
        | some (_, si) => pure (some (si, false))
        | none => pure ((lookupService? (← getEnv) (← getCurrNamespace) (← getOpenDecls) (Name.mkSimple aliasName)).map (·, true))
      if let some (svcInfo, isDirect) := svcOpt? then
        let some m := svcInfo.methods.find? (·.name == methName)
          | exprErr stx s!"service `{svcInfo.shortName}` has no method `{methName}`{Qed.Diag.didYouMean methName (svcInfo.methods.toList.map (·.name))}"
        let preArgs : Array Term := if m.takesCtx then #[ctx.ctxTerm?.getD ⟨(mkIdent `ctx).raw⟩] else #[]
        return some (← lowerCheckedCall stx rawArgs go (if m.isMonadic then "monadic service method" else "service method") "service method"
          s!"{svcInfo.shortName}.{methName}" m.isMonadic m.minParamCount m.paramCount m.dbWrite m.hasCookieOp false
          (if isDirect then some (Name.mkSimple aliasName) else none) (mkIdentFrom stx m.defConst : Term) preArgs)
  if calleeStx.getKind == ``qedIdent then
    let cname := (calleeStx.getArg 0).getId.eraseMacroScopes
    if cname == `old then
      match ctx.stateRule with
      | .invariantProp curV oldV _ =>
          if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then exprErr stx "`old(...)` expects exactly one positional expression argument"
          return some (← withReader (fun (c, q) => ({ c with stateRule := .invariantProp curV oldV true }, q)) (go mode rawArgs[0]![0]))
      | _ => exprErr stx "`old(...)` may only be used inside `invariant` declarations"
    if cname == `fail then return some (← lowerFailCall stx rawArgs go)
    let cstr := cname.toString
    if !ctxHasIdent ctx cstr then
      if let some hSig := ctx.helpers.find? (·.name == cstr) then
        let envArgs : Array Term := if hSig.takesEnvs then ctx.envIdents.map (⟨·.raw⟩) else #[]
        let ctxArgs : Array Term := if hSig.takesCtx then #[ctx.ctxTerm?.getD ⟨(mkIdent `ctx).raw⟩] else #[]
        return some (← lowerCheckedCall stx rawArgs go "server helper" "helper" cstr true
          hSig.minParamCount hSig.paramCount hSig.dbWrite hSig.hasCookieOp hSig.mutatesState none (hSig.defId : Term) (envArgs ++ ctxArgs))
      if ctx.isHttpRoute then if let some (_, ctorNm, defSt) := httpRespSpecs.find? (·.1 == cstr) then
        return some (← lowerHttpRespCall stx cstr ctorNm defSt rawArgs go)
  return none

private def hoistAwait (recGo : ExprMode → Syntax → SrvExprM Term) (stx awaitRef callStx : Syntax) (isUnwrap : Bool) (mode : ExprMode) : SrvExprM Term := do
  let (ctx, qctx) ← read
  unless ctx.allowAwait do exprErr awaitRef "`await` cannot be used inside an `atomic` block, lambda, `requires`, or `invariant`; perform external I/O outside `atomic`"
  let callTerm ← recGo .val callStx; let tmp ← liftM <| freshIdent "_srvAw"
  modify fun s => { s with hoisted := s.hoisted.push (if isUnwrap then .awaitUnwrap stx tmp callTerm else .awaitPlain stx tmp callTerm) }
  return qctx.runPure (finishTermMode mode ⟨tmp⟩)

@[noinline] private def mkSrvLowerHooks (recGo : ExprMode → Syntax → SrvExprM Term) : LowerHooks SrvExprM :=
  { LowerHooks.mkDefault (fun ref msg => exprErr ref msg) with
    lowerIdent := fun stx id mode => do
      let (ctx, qctx) ← read; let (cid, q) := peelTrailingQ (← liftM (m := CommandElabM) getKnownQLeafNames) (ctxHasIdent ctx) id
      return qctx.runPure (finishTermMode mode (← liftM <| hoistPureUnwraps stx ctx q (← resolveDottedIdent qctx stx ctx cid)))
    lowerProj := fun stx objT fld mode => do
      let (ctx, qctx) ← read
      if fld.isIdent then
        let (cf, q) := peelTrailingQ (← liftM (m := CommandElabM) getKnownQLeafNames) (fun _ => false) ⟨fld⟩
        return qctx.runPure (finishTermMode mode (← liftM <| hoistPureUnwraps stx ctx q (qctx.runPure `(($objT).$cf:ident))))
      else return qctx.runPure (finishTermMode mode (qctx.runPure (mkProjTermPure objT fld)))
    lowerIndex := fun _ arrT idxT mode => do return (← read).2.runPure (finishTermMode mode (← `(srvGetElem($arrT, $idxT))))
    lowerCall := lowerSrvCallHook
    lowerUnwrap := fun stx innerRaw mode => do
      let (ctx, qctx) ← read; liftM <| checkAllowUnwrap stx ctx; let inner := unwrapParens1 innerRaw
      if inner.getKind == ``qedAwait then hoistAwait recGo stx inner (inner.getArg 1) true mode
      else return qctx.runPure (finishTermMode mode (← liftM <| hoistPureUnwraps stx ctx 1 (← recGo .val innerRaw)))
    lowerAwait := fun stx argRaw mode => do
      let inner := unwrapParens1 argRaw
      if inner.getKind == ``qedUnwrap then
        let ctx := (← read).1
        liftM <| checkAllowUnwrap stx ctx s!"operator `?` cannot be used in `{ctx.fnName}` because its return type is neither fallible (`T!`) nor optional (`T?`); handle the `await` error with `let x = await ... catch err:`"
        hoistAwait recGo stx stx (inner.getArg 0) true mode
      else hoistAwait recGo stx stx argRaw false mode
    lowerArrElem := fun t => do return (← read).2.runPure `(srvAutoField($t))
    wrapNamedField := fun t => do return (← read).2.runPure `(srvAutoField($t))
    lowerType := fun t => liftM (m := CommandElabM) (liftMacroM (return (← lowerQedType t false).1))
    lowerPat := fun p => liftM (m := CommandElabM) (liftMacroM (lowerQedPat p))
    withLocals := fun names k => withReader (fun (c, q) => ({ c with locals := c.locals ++ names, allowAwait := false, allowUnwrap := false }, q)) k
    useDirectArray := false
    freshIdent := fun pfx => liftM <| freshIdent pfx }

private partial def lowerExprM (mode : ExprMode) (stx : Syntax) : SrvExprM Term := lowerQedExpr (mkSrvLowerHooks lowerExprM) mode stx

@[noinline] def lowerExpr (ctx : LowerCtx) (mode : ExprMode) (stx : Syntax) : LowerM Term := do
  (lowerExprM mode stx).run (ctx, ← liftM Lang.getPureQuotCtxCmd)

private def withCollectedHoists {α : Type} (act : LowerM α) : LowerM (α × Array HoistedStep) := do
  let saved := (← get).hoisted; modify fun s => { s with hoisted := #[] }
  let res ← act; let steps := (← get).hoisted; modify fun s => { s with hoisted := saved }; return (res, steps)

/-! ## LValue Mutation Path Parsing & Pure Quotation Builders -/

private partial def parseLValPath (qctx : PureQuotCtx) (ctx : LowerCtx) (stx : Syntax) : LowerM (Ident × Array LValStep) := do
  match stx.getKind with
  | ``qedIdent =>
      match (stx.getArg 0).getId.components with
      | [] => lowerErr stx "invalid assignment target"
      | root :: rest =>
          let rStr := root.toString
          unless ctx.stateFields.contains rStr do
            if ctx.locals.contains rStr || ctx.envVars.contains rStr || rStr == "ctx" then
              lowerErr stx s!"cannot mutate `{rStr}`: parameters, `env` bindings, `ctx`, and `let` bindings are immutable; only `state` fields may be mutated"
            let avail := if ctx.stateFields.isEmpty then "this server declares no `state` fields" else s!"`state` fields: {String.intercalate ", " (ctx.stateFields.toList.map fun f => s!"`{f}`")}"
            lowerErr stx s!"cannot mutate unknown state field `{rStr}` ({avail})"
          let _ ← checkStateRead stx ctx rStr; modify fun s => { s with mutated := pushUnique s.mutated rStr }
          return (mkIdentFrom stx root, rest.toArray.map (LValStep.field <| mkIdentFrom stx ·))
  | ``qedProj =>
      unless (stx.getArg 2).isIdent do lowerErr stx "cannot mutate a tuple projection"
      let (r, ps) ← parseLValPath qctx ctx (stx.getArg 0); return (r, ps.push (.field ⟨stx.getArg 2⟩))
  | ``qedIndex =>
      if (stx.getArg 4).getNumArgs == 0 then
        let (r, ps) ← parseLValPath qctx ctx (stx.getArg 0); return (r, ps.push (.index (← (lowerExprM .val (stx.getArg 2)).run (ctx, qctx))))
      else lowerErr stx "invalid mutation target; expected `stateField`, `stateField.sub`, or `stateField[i].sub`"
  | _ => lowerErr stx "invalid mutation target; expected `stateField`, `stateField.sub`, or `stateField[i].sub`"

@[noinline] private partial def withUpdatedPathCPS (qctx : PureQuotCtx) (steps : Array LValStep) (idx : Nat) (curVal : Term)
    (mkLeafNew : Term → LowerM Term) (k : Term → LowerM Term) : LowerM Term := do
  if h : idx < steps.size then
    match steps[idx] with
    | .field fid =>
        withUpdatedPathCPS qctx steps (idx + 1) (qctx.runPure `(($curVal).$fid:ident)) mkLeafNew fun ch =>
          k (qctx.runPure `({ $curVal with $fid:ident := srvAutoField($ch) }))
    | .index idxT =>
        let elemId ← freshIdent "_elem"; let hElemId ← freshIdent "_srvEqElem"
        let body ← withUpdatedPathCPS qctx steps (idx + 1) ⟨elemId⟩ mkLeafNew fun el => k (qctx.runPure `(srvSetElem($curVal, $idxT, $el)))
        return qctx.runPure `(Qed.Server.srvLetEq (srvGetElem($curVal, $idxT)) (fun $elemId:ident $hElemId:ident => $body))
  else k (← mkLeafNew curVal)

private def pureOvs (ctx : LowerCtx) : Array (String × Ident) := match ctx.stateRule with | .pureStep _ ovs => ovs | _ => #[]
private def materializeState (sCur : Ident) (ovs : Array (String × Ident)) : PureQuotM Term := do
  if ovs.isEmpty then pure sCur
  else let fIds := ovs.map fun p => mkIdent (Name.mkSimple p.1); let fVars : Array Term := ovs.map (⟨·.2.raw⟩); `({ $sCur with $[$fIds:ident := $fVars:term],* })

private def mkPureLeaf (ctx : LowerCtx) (stTerm optTerm : Term) : PureQuotM Term := do
  match ctx.emitAcc? with | some esId => Db.mkPairTerm stTerm (← Db.mkPairTerm esId optTerm) | none => Db.mkPairTerm stTerm optTerm

private def mkPureErrLeaf (ctx : LowerCtx) (s₀ : Ident) (errTerm : Term) : PureQuotM Term := do
  let optErr ← Db.mkOptTerm (some (← Db.mkAppC ``Except.error #[errTerm]))
  match ctx.emitAcc? with
  | some _ => Db.mkPairTerm s₀ (← Db.mkPairTerm (← `(([] : List Qed.Server.WsEmit))) optErr)
  | none => Db.mkPairTerm s₀ optErr

private def wrapLoopStep (isPure : Bool) (lm : Array Ident) (ctor : Name) (val? : Option Term := none) : PureQuotM Term := do
  let stPack ← mkMutPack lm.toList
  let step ← Db.mkAppC ctor (match val? with | some v => #[stPack, v] | none => #[stPack])
  if isPure then pure step else Db.mkAppC ``Pure.pure #[step]

private def wrapLoopRet (mode : BlockMode) (ctx : LowerCtx) (val : Term) (pureLeaf : Term → PureQuotM Term) : PureQuotM Term :=
  match ctx.loopMuts? with
  | some lm => wrapLoopStep (mode matches .pure ..) lm ``Qed.QedLoopStep.ret (some val)
  | none => match mode with | .pure .. => pureLeaf val | .async _ => do Db.mkAppC ``Pure.pure #[← Db.mkOptTerm (some val)] | .infallibleAsync => Db.mkAppC ``Pure.pure #[val]

private def mkOkLeaf (mode : BlockMode) (ctx : LowerCtx) (valTerm : Term) (isUnitEmpty : Bool := false) : PureQuotM Term := do
  let ok ← match mode with
    | .infallibleAsync => if isUnitEmpty then pure valTerm else `(srvAutoField($valTerm))
    | _ => do
        let inner ← match ctx.innerOptTy? with
          | some innerTy => if valTerm.raw.isIdent && let n := valTerm.raw.getId.eraseMacroScopes; n == `none || n == `Option.none then `((none : Option $innerTy)) else `(Qed.Server.SrvLiftOpt.liftOpt (Inner := $innerTy) $valTerm)
          | none => `(srvAutoField($valTerm))
        let payload ← if ctx.wrapReturnSumInl then Db.mkAppC ``Sum.inl #[inner] else pure inner
        Db.mkAppC ``Except.ok #[payload]
  wrapLoopRet mode ctx ok fun v => do match mode with | .pure _ _ sCur => mkPureLeaf ctx (← materializeState sCur (pureOvs ctx)) (← Db.mkOptTerm (some v)) | _ => pure v

private def mkErrLeaf (mode : BlockMode) (ctx : LowerCtx) (errTerm : Term) : PureQuotM Term := do
  wrapLoopRet mode ctx (← Db.mkAppC ``Except.error #[errTerm]) fun _ => match mode with | .pure _ s₀ _ => mkPureErrLeaf ctx s₀ errTerm | _ => unreachable!

private def mkEmptyLeaf (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) : LowerM Term := do
  if let some lm := ctx.loopMuts? then return qctx.runPure (wrapLoopStep (mode matches .pure ..) lm ``Qed.QedLoopStep.next)
  match mode with
  | .pure _ _ sCur => return qctx.runPure do mkPureLeaf ctx (← materializeState sCur (pureOvs ctx)) (mkCIdent `Option.none)
  | .async _ => return qctx.runPure (Db.mkAppC ``Pure.pure #[mkCIdent `Option.none])
  | .infallibleAsync => lowerErr Syntax.missing s!"missing `return` on fallthrough path of `{ctx.fnName}`"

@[noinline] private def lowerEmitCall (qctx : PureQuotCtx) (ctx : LowerCtx) (stmt : Syntax) (chId : Ident) (rawArgs : Array Syntax) : LowerM (Term × Array HoistedStep) := do
  let chStr := chId.getId.eraseMacroScopes.toString
  let some chSig := ctx.channels.find? (·.name == chStr)
    | lowerErr chId s!"unknown WebSocket `channel` `{chStr}` in `.emit(...)` (declared channels: [{String.intercalate ", " (ctx.channels.toList.map (·.name))}])"
  if rawArgs.size != chSig.paramCount + 1 then
    lowerErr stmt s!"`{chStr}.emit(...)` expects {chSig.paramCount + 1} argument(s) ({chSig.paramCount} channel param(s) + 1 event), got {rawArgs.size}"
  let (argTerms, allSteps) ← withCollectedHoists <| mapLower rawArgs fun ra => do
    unless ra.getKind == ``qedCallArgPos do lowerErr ra s!"named arguments are not supported in `{chStr}.emit(...)`"
    (lowerExprM .val (ra.getArg 0)).run (ctx, qctx)
  return (qctx.runPure do
    let args := argTerms.extract 0 chSig.paramCount |>.push (← `(srvAutoField($(argTerms[chSig.paramCount]!))))
    let args ← if chSig.hasEnsures then pure (args.push (← `(srvAutoEmit(True)))) else pure args
    mkAppTermsPure (chSig.mkEmitId : Term) args, allSteps)

@[noinline] def mkAtomicRunTerm (s0Id : Ident) (stateTyTerm committed : Term) (readOnly hasEmit : Bool)
    (onResult? : Option (Ident × (Term → CommandElabM Term)) := none) : CommandElabM Term := do
  let qctx ← Lang.getPureQuotCtxCmd
  let onBody? ← match hasEmit, onResult? with
    | true, some (pairId, onRes) => some <$> onRes (qctx.runPure `(($pairId).1))
    | false, some (resId, onRes) => some <$> onRes ⟨resId.raw⟩
    | _, none => pure none
  return qctx.runPure do
    let runCall ← if readOnly then `(Qed.Server.MonadAtomic.runAtomicRead (fun ($s0Id:ident : $stateTyTerm) => ($committed).2))
      else `(Qed.Server.MonadAtomic.runAtomic (fun ($s0Id:ident : $stateTyTerm) => $committed))
    match hasEmit, onResult?, onBody? with
    | true, some (pairId, _), some r => `($runCall >>= fun $pairId:ident => Qed.Server.flushWsEmits ($pairId).2 >>= fun _ => $r)
    | true, _, _ => `($runCall >>= fun _emitPair => Qed.Server.flushWsEmits (_emitPair).2 >>= fun _ => Pure.pure (_emitPair).1)
    | false, some (resId, _), some r => `($runCall >>= fun $resId:ident => $r)
    | false, _, _ => pure runCall

end ExprLowering

section BlockLowering
open Lean Elab Command

@[noinline] private def wrapUnwrapStep (mode : BlockMode) (ctx : LowerCtx) (tmp : Ident) (valTerm acc : Term) : PureQuotM Term := do
  let (eId, earlyId) := (mkIdent `_e, mkIdent `_early)
  if !ctx.hasFallible then if let some innerTy := ctx.innerOptTy? then
    let scrut ← `(Qed.Server.SrvUnwrapOpt.unwrapOpt (Inner := $innerTy) $valTerm)
    if let some lm := ctx.loopMuts? then
      return ← `(match $scrut:term with | Except.error $earlyId:ident => $(← wrapLoopStep (mode matches .pure ..) lm ``Qed.QedLoopStep.ret (some earlyId)) | Except.ok $tmp:ident => $acc)
    match mode with
    | .pure _ s₀ sCur =>
        let noneLeaf ← mkPureLeaf ctx (← materializeState sCur (pureOvs ctx)) (← Db.mkOptTerm (some (← Db.mkAppC ``Except.ok #[mkCIdent `Option.none])))
        return ← `(match $scrut:term with | Except.error (Except.ok none) => $noneLeaf | Except.error (Except.error $eId:ident) => $(← mkPureErrLeaf ctx s₀ eId) | Except.ok $tmp:ident => $acc)
    | .async _ => return ← `(match $scrut:term with | Except.error _early => Pure.pure (some _early) | Except.ok $tmp:ident => $acc)
    | .infallibleAsync => unreachable!
  let errTy ← match ctx.domainErrTy? with | some et => Db.mkAppC `Qed.Server.SrvFailure #[et] | none => pure (mkCIdent `Qed.Server.ApiError)
  `(match Qed.Server.SrvUnwrap.unwrap (E := $errTy) $valTerm with | Except.error $eId:ident => $(← mkErrLeaf mode ctx eId) | Except.ok $tmp:ident => $acc)

@[noinline] private def wrapHoists (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) (steps : Array HoistedStep) (body : Term) : LowerM Term :=
  foldrLower steps body fun step acc => do
    match step, mode with
    | .awaitUnwrap ref _ _, .pure .. | .awaitPlain ref _ _, .pure .. => lowerErr ref "`await` cannot appear inside a pure/atomic block"
    | .awaitUnwrap ref _ _, .infallibleAsync => lowerErr ref "operator `?` cannot be used in an infallible function; declare its return type `-> T!` or use `catch`"
    | .pureUnwrap _ _, .infallibleAsync => lowerErr Syntax.missing "operator `?` cannot be used in an infallible function"
    | .awaitUnwrap _ tmp callTerm, .async _ =>
        let rawTmp ← freshIdent "_srvRaw"
        return qctx.runPure do `($callTerm >>= fun $rawTmp:ident => $(← wrapUnwrapStep mode ctx tmp ⟨rawTmp⟩ acc))
    | .awaitPlain _ tmp callTerm, .async _ | .awaitPlain _ tmp callTerm, .infallibleAsync =>
        return qctx.runPure `((srvAwaitPlain($callTerm)) >>= fun $tmp:ident => $acc)
    | .pureUnwrap tmp valTerm, _ => return qctx.runPure (wrapUnwrapStep mode ctx tmp valTerm acc)

private def lowerOptTypeNode (optNode : Syntax) : LowerM (Option Term) :=
  if optNode.getNumArgs == 2 then some <$> liftMacroM (return (← lowerQedType (optNode.getArg 1) false).1) else pure none

@[noinline] private def bindLet (qctx : PureQuotCtx) (mode : BlockMode) (xStx : Syntax) (ty? : Option Term) (val cont : Term) : LowerM Term := do
  match mode with
  | .pure .. =>
      let hEq ← freshIdent "_srvEq"
      let (bindId, body) ← if xStx.isIdent then pure (⟨xStx⟩, cont)
        else if xStx.getKind == ``qedLetPatTuple then
          let tupId ← freshIdent "_srvTup"; let pat ← liftMacroM (lowerLetBinderPat xStx)
          pure (tupId, qctx.runPure `(let $pat:term := $tupId:ident; $cont))
        else pure (← freshIdent "_srvDiscard", cont)
      return qctx.runPure do
        let tv ← match ty? with | some ty => `(($val : $ty)) | none => pure val
        `(Qed.Server.srvLetEq $tv (fun $bindId:ident $hEq:ident => $body))
  | .async _ | .infallibleAsync => return qctx.runPure (mkLetBindTerm xStx ty? val cont)

private def pushPatLocals (ctx : LowerCtx) (patIds : Array Name) : LowerCtx :=
  if patIds.isEmpty then ctx else
  { ctx with locals := ctx.locals ++ patIds.map (·.toString), mutLocals := ctx.mutLocals.filter fun m => !patIds.contains m.getId.eraseMacroScopes }

private def isBareUnwrapExpr (allowAwait : Bool) (knownQ : Std.HashSet String) (ctx : LowerCtx) (eStx : Syntax) : Bool :=
  let u := unwrapParens1 eStx
  u.getKind == ``qedUnwrap || (allowAwait && u.getKind == ``qedAwait && (unwrapParens1 (u.getArg 1)).getKind == ``qedUnwrap) ||
  (eStx.getKind == ``qedIdent && let s := (eStx.getArg 0).getId.toString; s.endsWith "?" && !knownQ.contains (leafOfDottedStr s) && !ctxHasIdent ctx s) ||
  (eStx.getKind == ``qedProj && (eStx.getArg 2).isIdent && let f := (eStx.getArg 2).getId.toString; f.endsWith "?" && !knownQ.contains f)

/-! ## Unified Pure & Async Statement Block Lowering (`lowerBlock`) -/

@[noinline] private partial def lowerCatchFallback? (qctx : PureQuotCtx) (ctx : LowerCtx) (stmts : Array Syntax) : LowerM (Option Term) := do
  let knownQ ← liftM getKnownQLeafNames; let bound := (ctx.locals ++ ctx.stateFields ++ ctx.envVars).foldl (·.insert ·) {}
  let lowerPureNoHoist (eStx : Syntax) : LowerM (Option Term) := do
    if exprHasAwait eStx || exprHasUnwrapWith knownQ bound eStx then return none
    let (t, steps) ← withCollectedHoists ((lowerExprM .val eStx).run ({ ctx with allowAwait := false }, qctx))
    return if steps.isEmpty then some t else none
  if stmts.isEmpty then return none
  else if stmts.size == 1 && stmts[0]!.getKind == ``qedStmtExpr then
    let eStx := stmts[0]![0]
    if (matchPushCall? eStx).isSome || (matchRemoveCall? eStx).isSome || (matchSrvEmitStmt? stmts[0]!).isSome then return none
    let some eTerm ← lowerPureNoHoist eStx | return none
    return some (qctx.runPure `(srvAutoField($eTerm)))
  else if stmts[0]!.getKind == ``qedStmtLet && stmts[0]![5].getNumArgs == 0 then
    let st := stmts[0]!
    let some rhsTerm ← lowerPureNoHoist (st.getArg 4) | return none
    let ty? ← lowerOptTypeNode (st.getArg 2)
    let some tailTerm ← lowerCatchFallback? qctx (pushPatLocals ctx (collectLetBinderIds (st.getArg 1))) (stmts.extract 1 stmts.size) | return none
    return some (qctx.runPure (mkLetBindTerm (st.getArg 1) ty? (← `(srvRejectUnhandledErr($rhsTerm))) tailTerm))
  else return none

@[noinline] private def lowerMatchScrutineesAndAlts (qctx : PureQuotCtx) (ctx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (lowerArm : LowerCtx → Array Syntax → LowerM Term) : LowerM (Term × Array HoistedStep) := do
  let (scrutTerms, allSteps) ← withCollectedHoists <| mapLower (stmt.getArg 1).getSepArgs fun s => (lowerExprM .val s).run (ctx, qctx)
  let termCheck := blockAlwaysTerminates ctx.loopMuts?.isSome
  let alts ← mapLower (stmt.getArg 3).getArgs fun c => do
    let altTerms ← liftMacroM (lowerCasePatAlts (c.getArg 1))
    let pIds := collectCasePatIds (extractCasePatAlts (c.getArg 1)); let cStmts := suiteStmts (c.getArg 3)
    return qctx.runPure (mkMatchAltFromAlts altTerms (← lowerArm (pushPatLocals ctx pIds) (if termCheck cStmts then cStmts else cStmts ++ rest)))
  return (qctx.runPure `(match $[$scrutTerms:term],* with $[$alts:matchAlt]*), allSteps)

private def extractSrvLetCatch? (clausesNode : Syntax) : LowerM (Option Syntax) :=
  foldlLower clausesNode.getArgs none fun catchOpt? cl => do
    match cl.getKind with
    | `Qed.Lang.letCatch =>
        if catchOpt?.isSome then lowerErr cl "duplicate `catch` clause on `let`"
        return some (cl.getArg 1)
    | `Qed.Lang.letPredictBlock | `Qed.Lang.letPredictExpr | `Qed.Lang.letOnConfirm | `Qed.Lang.letRollback =>
        lowerErr cl "`predict`, `on_confirm`, and `rollback` are only supported on client `component` `await` calls, not in `server` functions"
    | _ => return catchOpt?

private def rejectSrvAssignPredict (stmt : Syntax) : LowerM Unit := do
  if stmt.getKind == ``qedStmtAssign && stmt.getNumArgs > 3 && (stmt.getArg 3).getNumArgs > 0 then
    lowerErr ((stmt.getArg 3).getArg 0) "`predict` is only supported on client `component` `await` calls, not in `server` functions"

@[noinline] private def lowerBranch (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) (rest thenStmts : Array Syntax) (thenCtx : LowerCtx)
    (elseStmts? : Option (Array Syntax)) (allowPureLetJoin : Bool) (mkBranch : Term → Term → PureQuotM Term)
    (recSame : LowerCtx → Array Syntax → LowerM Term) (recWithState : LowerCtx → Ident → Array Syntax → LowerM Term) : LowerM Term := do
  let termCheck := blockAlwaysTerminates ctx.loopMuts?.isSome
  let (thenRet, elseRet) := (termCheck thenStmts, elseStmts?.any termCheck)
  let lowerElseOpt := elseStmts?.elim (mkEmptyLeaf qctx mode ctx) (recSame ctx)
  if rest.isEmpty || (mode matches .infallibleAsync) || ctx.loopMuts?.isSome || !ctx.mutLocals.isEmpty || thenRet != elseRet then
    let tT ← recSame thenCtx (if !rest.isEmpty && !thenRet then thenStmts ++ rest else thenStmts)
    let eT ← if !rest.isEmpty && !elseRet then recSame ctx ((elseStmts?.getD #[]) ++ rest) else lowerElseOpt
    return qctx.runPure (mkBranch tT eT)
  let br := qctx.runPure (mkBranch (← recSame thenCtx thenStmts) (← lowerElseOpt))
  match mode with
  | .pure .. =>
      let sNext ← freshIdent "_s"
      let baseJoinCtx := { ctx with stateRule := if ctx.stateFields.isEmpty then .statelessServer else .pureStep sNext #[] }
      match ctx.emitAcc? with
      | some _ =>
          let esNext ← freshIdent "_es"; let cont ← recWithState { baseJoinCtx with emitAcc? := some esNext } sNext rest
          return qctx.runPure do Db.mkAppC `Qed.Server.srvEmitSeq #[br, ← `(fun $sNext:ident $esNext:ident => $cont)]
      | none =>
          let cont ← recWithState baseJoinCtx sNext rest
          if allowPureLetJoin && !blockMayReturnEarly thenStmts && !(elseStmts?.any blockMayReturnEarly) then
            return qctx.runPure `(Qed.Server.srvLetEq (($br : _ × Option Unit).1) (fun $sNext:ident $(← freshIdent "_srvEq"):ident => $cont))
          else return qctx.runPure do Db.mkAppC `Qed.Server.srvSeq #[br, ← `(fun $sNext:ident => $cont)]
  | .async _ => let cont ← recSame ctx rest; return qctx.runPure do Db.mkAppC `Qed.Server.srvSeqM #[br, ← `(fun _ => $cont)]
  | .infallibleAsync => unreachable!

@[noinline] private def lowerReturn (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) (stmt : Syntax) : LowerM Term := do
  if (stmt.getArg 1).getNumArgs == 0 then return qctx.runPure (mkOkLeaf mode ctx (mkCIdent ``Unit.unit) (isUnitEmpty := true))
  let retExpr := (stmt.getArg 1).getArg 0; let uRet := unwrapParens1 retExpr
  match mode with
  | .pure .. => if exprHasAwait retExpr && !uRet.isOfKind ``qedUnwrap then lowerErr retExpr "`await` cannot be used inside a synchronous or `atomic` block"
  | .infallibleAsync => pure ()
  | .async _ =>
      if uRet.getKind == ``qedAwait && !(unwrapParens1 (uRet.getArg 1)).isOfKind ``qedUnwrap && ctx.hasFallible then
        let (callTerm, steps) ← withCollectedHoists ((lowerExprM .val (uRet.getArg 1)).run (ctx, qctx)); let rawId ← freshIdent "_retAw"
        return ← wrapHoists qctx mode ctx steps <| qctx.runPure do
          let errTy ← match ctx.domainErrTy? with | some et => Db.mkAppC `Qed.Server.SrvFailure #[et] | none => pure (mkCIdent `Qed.Server.ApiError)
          let liftCall ← `(Qed.Server.SrvRetAwait.liftRet (E := $errTy) $rawId)
          let innerRes ← match ctx.innerOptTy? with
            | some innerTy => `(match $liftCall:term with | Except.ok _v => Except.ok (Qed.Server.SrvLiftOpt.liftOpt (Inner := $innerTy) _v) | Except.error _e => Except.error _e)
            | none => pure liftCall
          let wrappedRes ← match ctx.loopMuts? with | none => Db.mkOptTerm (some innerRes) | some lm => wrapLoopStep true lm ``Qed.QedLoopStep.ret (some innerRes)
          `($callTerm >>= fun $rawId:ident => Pure.pure $wrappedRes)
  let isFail := uRet.getKind == ``qedCall && (uRet.getArg 0).getKind == ``qedIdent && ((uRet.getArg 0).getArg 0).getId == `fail
  if isFail && !ctx.hasFallible then lowerErr retExpr s!"`fail(...)` can only be returned from a fallible `T!` function (`{ctx.fnName}` is not declared `-> ...!`)"
  let (term, steps) ← withCollectedHoists ((lowerExprM .val retExpr).run (ctx, qctx))
  wrapHoists qctx mode ctx steps (qctx.runPure <| if isFail then mkErrLeaf mode ctx term else mkOkLeaf mode ctx term)

@[noinline] private def lowerLetCore (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (recBlock : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let xStx := stmt.getArg 1; let ty? ← lowerOptTypeNode (stmt.getArg 2); let rhsRaw := stmt.getArg 4
  let nextCtx := pushPatLocals ctx (collectLetBinderIds xStx)
  if let some catchNode ← extractSrvLetCatch? (stmt.getArg 5) then
    if catchNode.getKind == `Qed.Lang.catchArms then lowerErr catchNode "multi-arm `catch: case ...` is for client components; in server/service functions use `catch err:`"
    let rhsStx := unwrapParens1 rhsRaw; let binderStx := catchNode.getArg 0; let catchStmts := suiteStmts (catchNode.getArg 2)
    let errId : Ident := if binderStx.isIdent then ⟨binderStx⟩ else mkIdent `_srvCatchErr
    let catchCtx := pushPatLocals ctx (collectLetBinderIds binderStx); let okTerm ← recBlock nextCtx rest
    let (scrutTerm, steps, awaitCall?) : Term × Array HoistedStep × Option (Term × Ident) ←
      if rhsStx.getKind == ``qedAwait then
        if mode matches .pure .. then lowerErr rhsRaw "`await` cannot be used inside a synchronous or `atomic` block"
        let (c, s) ← withCollectedHoists ((lowerExprM .val (rhsStx.getArg 1)).run (ctx, qctx)); let r ← freshIdent "_catchAw"; pure (⟨r⟩, s, some (c, r))
      else let (r, s) ← withCollectedHoists ((lowerExprM .val rhsStx).run (ctx, qctx)); pure (r, s, none)
    let mkUnwrap (errBody okPat okBody : Term) : Term :=
      qctx.runPure `(match Qed.Server.SrvUnwrap.unwrap (E := Qed.Server.ApiError) $scrutTerm with | Except.error $errId:ident => $errBody | Except.ok $okPat:term => $okBody)
    let innerTerm ← if let some fbTerm ← lowerCatchFallback? qctx catchCtx catchStmts then
        let okValId ← freshIdent "_catchOk"; bindLet qctx mode xStx ty? (mkUnwrap fbTerm ⟨okValId.raw⟩ ⟨okValId.raw⟩) okTerm
      else
        unless blockAlwaysTerminates ctx.loopMuts?.isSome catchStmts do
          lowerErr stmt (if ctx.loopMuts?.isSome then "the `catch` block must end with `return`, `break`, `continue`, or a fallback value expression" else "the `catch` block must either `return` on all paths or end with a fallback value expression")
        let errBody ← recBlock catchCtx catchStmts
        match ty? with
        | some ty => let okValId ← freshIdent "_catchOk"; pure <| mkUnwrap errBody ⟨okValId.raw⟩ (qctx.runPure (mkLetBindTerm xStx (some ty) ⟨okValId.raw⟩ okTerm))
        | none =>
            let okPat ← if xStx.isIdent then pure ⟨xStx⟩ else if xStx.getKind == ``qedLetPatTuple then liftMacroM (lowerLetBinderPat xStx) else pure ⟨(mkIdent `_srvDiscard).raw⟩
            pure <| mkUnwrap errBody okPat okTerm
    wrapHoists qctx mode ctx steps (match awaitCall? with | some (c, r) => qctx.runPure `($c >>= fun $r:ident => $innerTerm) | none => innerTerm)
  else
    let (rhsTerm, steps) ← withCollectedHoists ((lowerExprM .val rhsRaw).run (ctx, qctx))
    let checkedRhs := if steps.isEmpty then qctx.runPure `(srvRejectUnhandledErr($rhsTerm)) else rhsTerm
    wrapHoists qctx mode ctx steps (← bindLet qctx mode xStx ty? checkedRhs (← recBlock nextCtx rest))

@[noinline] private def lowerPureMutationStmt (qctx : PureQuotCtx) (mode : BlockMode) (pCtx : LowerCtx) (sCur : Ident) (stmt : Syntax) (rest : Array Syntax)
    (recPure : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  rejectSrvAssignPredict stmt
  let (lvalStx, steps, mkLeaf) : Syntax × Array HoistedStep × (Array LValStep → Term → LowerM Term) ←
    if stmt.getKind == ``qedStmtAssign then
      let opStr := ((stmt.getArg 1).reprint.getD "=").trimAscii.toString
      let (rhsTerm, steps) ← withCollectedHoists ((lowerExprM .val (stmt.getArg 2)).run (pCtx, qctx))
      pure (stmt.getArg 0, steps, fun pathSteps curLeaf => do
        let val ← match applyAssignOpPure qctx (stmt.getArg 1) opStr curLeaf rhsTerm with
          | .ok t => pure t | .error (ref, msg) => lowerErr ref msg
        return if pathSteps.isEmpty then qctx.runPure `(srvAutoField($val)) else val)
    else if let some (targetStx, elemStx) := matchPushCall? (stmt.getArg 0) then
      let (elemTerm, steps) ← withCollectedHoists ((lowerExprM .val elemStx).run (pCtx, qctx))
      pure (targetStx, steps, fun _ curArr => pure <| qctx.runPure `(($curArr).push (srvAutoField($elemTerm))))
    else
      let some (targetStx, keyStx) := matchRemoveCall? (stmt.getArg 0) | unreachable!
      let (keyTerm, steps) ← withCollectedHoists ((lowerExprM .val keyStx).run (pCtx, qctx))
      pure (targetStx, steps, fun _ curDict => pure <| qctx.runPure (Db.mkAppC `Qed.Dict.remove #[curDict, keyTerm]))
  let (rootField, pathSteps) ← parseLValPath qctx pCtx lvalStx; let curRoot ← resolveStateFieldBase qctx lvalStx pCtx rootField.getId
  let fNext ← freshIdent s!"_fld_{rootField.getId}_"; let hFNext ← freshIdent "_srvEq"
  let fldStr := rootField.getId.toString
  let cont ← recPure { pCtx with stateRule := .pureStep sCur ((pureOvs pCtx).filter (·.1 != fldStr) |>.push (fldStr, fNext)) } rest
  let chain ← withUpdatedPathCPS qctx pathSteps 0 curRoot (mkLeaf pathSteps) fun updatedRaw =>
    return qctx.runPure do
      let updatedRoot ← if pathSteps.isEmpty then `(srvTypedAs(($sCur).$rootField:ident, $updatedRaw)) else pure updatedRaw
      `(Qed.Server.srvLetEq $updatedRoot (fun $fNext:ident $hFNext:ident => $cont))
  wrapHoists qctx mode pCtx steps chain

@[noinline] private def lowerAtomicStmt (qctx : PureQuotCtx) (aCtx : LowerCtx) (stateTyTerm? : Option Term) (stmt : Syntax) (rest : Array Syntax)
    (lowerPure : LowerCtx → Ident → Ident → Array Syntax → LowerM Term) (lowerRest : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let atomStmts := suiteStmts (stmt.getArg 2); let alwaysRet := blockAlwaysReturns atomStmts
  let exportedIds := if alwaysRet then #[] else atomStmts.foldl (init := #[]) fun ids s =>
    if s.getKind == ``qedStmtLet then (collectLetBinderIds (s.getArg 1)).foldl (init := ids) fun acc nm =>
      let sNm := nm.toString; if rest.any (stxMentionsVar sNm) then acc.filter (·.getId.eraseMacroScopes.toString != sNm) |>.push (mkIdentFrom s nm) else acc
    else ids
  let mkLoopRet (retTerm : Term) : PureQuotM Term := wrapLoopRet (.async none) aCtx retTerm (fun _ => unreachable!)
  let baseAtomCtx := { aCtx with loopMuts? := none }
  let (atomCtx, bodyStmts, isFinish, mkOnResult) : LowerCtx × Array Syntax × Bool × (Term → LowerM Term) ←
    if alwaysRet then pure (baseAtomCtx, atomStmts, true, fun res => pure <| qctx.runPure (mkLoopRet res))
    else if !exportedIds.isEmpty then
      let hasEarlyOk := atomStmts.any (stxAny fun s => s.getKind == ``qedStmtReturn && ((s.getArg 1).getNumArgs == 0 || !((unwrapParens1 (s.getArg 1)[0]).getKind == ``qedCall && ((unwrapParens1 (s.getArg 1)[0]).getArg 0).getKind == ``qedIdent && (((unwrapParens1 (s.getArg 1)[0]).getArg 0).getArg 0).getId == `fail)))
      let expTuple := qctx.runPure (buildTupleVal (exportedIds.map (⟨·.raw⟩)))
      pure (if hasEarlyOk then { baseAtomCtx with wrapReturnSumInl := true } else { baseAtomCtx with innerOptTy? := none },
        atomStmts.push (Syntax.node (.fromRef stmt) `Qed.Server.atomicExport #[expTuple.raw]), true, fun res => do
          let cont ← lowerRest { aCtx with locals := aCtx.locals ++ exportedIds.map (·.getId.eraseMacroScopes.toString) } rest
          return qctx.runPure do
            let (eId, vId) := (mkIdent `_e, mkIdent `_v)
            let errRet ← mkLoopRet (← Db.mkAppC ``Except.error #[eId])
            if hasEarlyOk then
              let okRet ← mkLoopRet (← Db.mkAppC ``Except.ok #[vId])
              `(match $res:term with | Except.error $eId:ident => $errRet | Except.ok (Sum.inl $vId:ident) => $okRet | Except.ok (Sum.inr $expTuple:term) => $cont)
            else `(match $res:term with | Except.error $eId:ident => $errRet | Except.ok $expTuple:term => $cont))
    else pure (baseAtomCtx, atomStmts, false, fun early => do
      let cont ← lowerRest aCtx rest
      return qctx.runPure do let rId := mkIdent `_r; `(match $early:term with | some $rId:ident => $(← mkLoopRet rId) | none => $cont))
  let some stateTyTerm := stateTyTerm? | lowerErr stmt "`atomic` is only valid in a `server` with `state` declarations"
  if blockHasAwait bodyStmts then lowerErr stmt "cannot use `await` inside an `atomic` block; perform external I/O outside `atomic` so shared locks never span network calls"
  let s0Id ← freshIdent "_sAtom"; let hasEmit := blockHasEmit bodyStmts; let es0Id ← freshIdent "_es0"
  let savedMut := (← get).mutated; modify fun s => { s with mutated := #[] }
  let rawAtomBody ← lowerPure (if hasEmit then { atomCtx with emitAcc? := some es0Id } else atomCtx) s0Id s0Id bodyStmts
  let atomMut := (← get).mutated; modify fun s => { s with mutated := savedMut ++ atomMut.filter (!savedMut.contains ·) }
  let readOnly := atomMut.isEmpty
  let committed := qctx.runPure do
    let atomBody ← if hasEmit then `(let $es0Id:ident : List Qed.Server.WsEmit := []; $rawAtomBody) else pure rawAtomBody
    match isFinish, hasEmit, readOnly with
    | true, true, _ => Db.mkAppC `Qed.Server.srvFinishEmit #[s0Id, atomBody]
    | false, true, _ => Db.mkAppC `Qed.Server.srvAtomicCommitEmit #[s0Id, atomBody]
    | true, false, _ => Db.mkAppC `Qed.Server.srvFinish #[s0Id, atomBody]
    | false, false, true => pure atomBody
    | false, false, false => Db.mkAppC `Qed.Server.srvAtomicCommit #[s0Id, atomBody]
  let bindId ← freshIdent (if hasEmit then "_atomPair" else "_atomRes")
  let onResBody ← mkOnResult (if hasEmit then qctx.runPure `(($bindId).1) else ⟨bindId.raw⟩)
  liftM <| mkAtomicRunTerm s0Id stateTyTerm committed readOnly hasEmit (some (bindId, fun _ => pure onResBody))

@[noinline] private def lowerOptArg (qctx : PureQuotCtx) (ctx : LowerCtx) (named : Array (String × Syntax)) (k : String)
    (defTerm : Term) (someTy? : Option Name := none) : LowerM Term :=
  match findNamedArg? named k with
  | some s => do
      let v ← (lowerExprM .val s).run (ctx, qctx)
      return match someTy? with | some tyNm => qctx.runPure do Db.mkOptTerm (some (← `(($v : $(mkCIdent tyNm))))) | none => v
  | none => pure defTerm

@[noinline] private def lowerSideEffectCall (qctx : PureQuotCtx) (ctx : LowerCtx) (stmt : Syntax) (fn : String) (rawArgs : Array Syntax) : LowerM (Name × Term × Array HoistedStep) := do
  let noneT := mkCIdent `Option.none
  if fn == "send" then
    unless ctx.isStreamRoute do lowerErr stmt "`send(...)` is only available inside `stream \"/...\":` routes"
    let (argT, steps) ← withCollectedHoists do
      let (pos, named) ← splitCallArgs "send" rawArgs (some ["data", "event", "id", "retry"]) (errRef := stmt)
      let some dataStx := pos[0]? |>.orElse (fun _ => findNamedArg? named "data") | lowerErr stmt "`send(data[, event = ..., id = ..., retry = ...])` requires an event data string"
      if pos.size > 1 then lowerErr stmt "`send(...)` takes one positional `data` argument; pass `event = ...`, `id = ...`, or `retry = ...` as named arguments"
      let dT ← (lowerExprM .val dataStx).run (ctx, qctx)
      return qctx.runPure (Db.mkAppC `Qed.Server.SseEvent.mk #[dT,
        ← lowerOptArg qctx ctx named "event" noneT (some ``String),
        ← lowerOptArg qctx ctx named "id" noneT (some ``String),
        ← lowerOptArg qctx ctx named "retry" noneT (some ``Nat)])
    return (`Qed.Server.MonadServer.sendSse, argT, steps)
  let isClear := fn == "clearCookie"
  let (argT, steps) ← withCollectedHoists do
    let (pos, named) ← splitCallArgs fn rawArgs (if isClear then none else some ["name", "value", "path", "httpOnly", "secure", "sameSite", "maxAge", "domain"]) (errRef := stmt)
    let some nameStx := pos[0]? |>.orElse (fun _ => findNamedArg? named "name")
      | lowerErr stmt (if isClear then "`clearCookie(name[, path = \"/\"])` requires a cookie name" else "`setCookie(name, value, ...)` requires a cookie name")
    let nT ← (lowerExprM .val nameStx).run (ctx, qctx)
    if isClear then
      let pathT ← match (findNamedArg? named "path").orElse (fun _ => pos[1]?) with | some s => (lowerExprM .val s).run (ctx, qctx) | none => pure (Syntax.mkStrLit "/")
      return qctx.runPure (Db.mkAppC `Qed.Server.SetCookie.clear #[nT, pathT])
    let some valStx := pos[1]? |>.orElse (fun _ => findNamedArg? named "value") | lowerErr stmt "`setCookie(name, value, ...)` requires a cookie value"
    let vT ← (lowerExprM .val valStx).run (ctx, qctx)
    let pT ← lowerOptArg qctx ctx named "path" (Syntax.mkStrLit "/")
    let hoT ← lowerOptArg qctx ctx named "httpOnly" (mkCIdent ``Bool.true)
    let ssT ← lowerOptArg qctx ctx named "sameSite" (mkCIdent `Qed.Server.SameSite.lax)
    let secT ← lowerOptArg qctx ctx named "secure" (mkCIdent ``Bool.false)
    let maT ← lowerOptArg qctx ctx named "maxAge" noneT (some ``Nat)
    let domT ← lowerOptArg qctx ctx named "domain" noneT (some ``String)
    return qctx.runPure do Db.mkAppC `Qed.Server.SetCookie.mk #[nT, vT, pT, hoT, ← `(($ssT : Qed.Server.SameSite)), secT, maT, domT]
  modify fun s => { s with hasCookieOp := true }
  return (`Qed.Server.MonadServer.setCookie, argT, steps)

@[noinline] private def lowerTxStmt (qctx : PureQuotCtx) (aCtx : LowerCtx) (stmt aliasRef : Syntax) (aliasName : String) (txVar? : Option Ident) (txStmts rest : Array Syntax)
    (recAsync : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let some (_, dbInfo) := aCtx.dbs.find? (·.1 == aliasName)
    | lowerErr aliasRef s!"unknown database alias `{aliasName}` in `transaction` (declared `use` databases: [{String.intercalate ", " (aCtx.dbs.toList.map Prod.fst)}])"
  if let some (curAlias, _) := aCtx.activeDbTx? then lowerErr stmt s!"nested database transactions are not supported (already inside `{curAlias}.transaction:`)"
  let txId ← freshIdent "_dbTxId"
  let (innerCtx, wrapTxVar) ← match txVar? with
    | none => pure ({ aCtx with activeDbTx? := some (aliasName, txId), loopMuts? := none }, fun b => b)
    | some tv =>
        let tvName := tv.getId.eraseMacroScopes.toString
        if aCtx.dbs.any (·.1 == tvName) || aCtx.txDbAliases.any (·.1 == tvName) then lowerErr tv s!"transaction variable `{tvName}` collides with an existing database alias"
        let txTagLit := Syntax.mkStrLit dbInfo.dbName.toString
        pure ({ aCtx with activeDbTx? := some (aliasName, txId), txDbAliases := aCtx.txDbAliases.push (tvName, dbInfo, ⟨txId.raw⟩), locals := aCtx.locals.push tvName, loopMuts? := none },
          fun b => qctx.runPure `(let $tv:ident : Qed.Server.Db.DbTx $txTagLit := Qed.Server.Db.DbTx.mk $txId; $b))
  let bodyTerm := wrapTxVar (← recAsync innerCtx txStmts)
  let restTerm? ← if aCtx.loopMuts?.isSome || !(rest.isEmpty || blockAlwaysReturns txStmts) then some <$> recAsync aCtx rest else pure none
  return qctx.runPure do
    let txRun ← Db.mkAppC `Qed.Server.dbRunTx #[mkIdentFrom aliasRef dbInfo.configConst, ← `(fun ($txId:ident : UInt64) => $bodyTerm)]
    match aCtx.loopMuts?, restTerm? with
    | some lm, some rt => let txRetId := mkIdent `_txRet; `($txRun >>= fun | Option.some $txRetId:ident => $(← wrapLoopStep false lm ``Qed.QedLoopStep.ret (some txRetId)) | Option.none => $rt)
    | none, some rt => Db.mkAppC `Qed.Server.srvSeqM #[txRun, ← `(fun _ => $rt)]
    | _, _ => pure txRun

@[noinline] private def lowerSrvForFoldCore (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (recBlock : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let binderStx := stmt.getArg 1; let iterStx := stmt.getArg 3; let bodyStmts := suiteStmts (stmt.getArg 5)
  if let some badInv := (forSuiteInvs (stmt.getArg 5))[0]? then
    lowerErr badInv "loop `invariant` clauses are only supported in pure `fn` functions"
  for bNm in collectLetBinderIds binderStx do
    if ctx.mutLocals.any (·.getId.eraseMacroScopes == bNm) then lowerErr binderStx s!"`for` loop variable `{bNm}` shadows mutable variable `{bNm}`; use a different loop variable name"
  let (iterTerm, steps) ← withCollectedHoists ((lowerExprM .val iterStx).run (ctx, qctx))
  let mutated := collectMutatedIds bodyStmts; let usedMuts := ctx.mutLocals.filter fun m => mutated.contains m.getId.eraseMacroScopes
  let (stParam, resSt, resRet, retValId) := (← freshIdent "_srvLoopSt", ← freshIdent "_srvLoopStOut", ← freshIdent "_srvLoopRetOut", ← freshIdent "_srvLoopRet")
  let bodyInner ← recBlock { pushPatLocals ctx (collectLetBinderIds binderStx) with loopMuts? := some usedMuts } bodyStmts
  let restTerm ← recBlock ctx rest; let isRange := isRangeCallExpr iterStx; let isPure := mode matches .pure ..
  let fullTerm := qctx.runPure do
    let initSt ← mkMutPack usedMuts.toList; let bodyWithUnpack ← wrapMutUnpack stParam usedMuts.toList bodyInner
    let lam ← mkForLoopLamPure "_srvElem" stParam binderStx bodyWithUnpack
    let someArm ← wrapLoopRet mode ctx ⟨retValId.raw⟩ fun v => do match mode with | .pure _ _ sCur => mkPureLeaf ctx (← materializeState sCur (pureOvs ctx)) (← Db.mkOptTerm (some v)) | _ => pure v
    let afterLoop ← wrapMutUnpack resSt usedMuts.toList (← `(match $resRet:ident with | Option.some $retValId:ident => $someArm | Option.none => $restTerm))
    if isPure then
      let call ← Db.mkAppC (if isRange then ``Qed.qedForRange else ``Qed.qedForFold) #[iterTerm, initSt, lam]
      `(let ($resSt:ident, $resRet:ident) := $call; $afterLoop)
    else
      let call ← if isRange then Db.mkAppC `Qed.Server.srvForRangeM #[iterTerm, initSt, lam]
        else Db.mkAppC `Qed.Server.srvForFoldM #[← Db.mkAppC ``Qed.QedIterable.toList #[iterTerm], initSt, lam]
      `($call >>= fun ($resSt:ident, $resRet:ident) => $afterLoop)
  wrapHoists qctx mode ctx steps fullTerm

@[noinline] private def lowerAssignOrExprStmt (qctx : PureQuotCtx) (mode : BlockMode) (bCtx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (recSame : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  if let some act := tryMatchLocalMut? bCtx.mutLocals stmt then
    rejectSrvAssignPredict stmt
    let (rhsTerm, steps) ← withCollectedHoists ((lowerExprM .val act.rhsSyntax).run (bCtx, qctx))
    let newVal ← liftMacroM (applyLocalMutRhs act rhsTerm); let lId := act.targetIdent; let cont ← recSame bCtx rest
    return ← wrapHoists qctx mode bCtx steps (qctx.runPure `(let $lId:ident := $newVal; $cont))
  let (isPure, isInf) := (mode matches .pure .., mode matches .infallibleAsync)
  if !isInf then
    if let some (chId, rawArgs) := matchSrvEmitStmt? stmt then
      let (emitTerm, steps) ← lowerEmitCall qctx bCtx stmt chId rawArgs
      let body ← match mode with
        | .pure .. =>
            let some esId := bCtx.emitAcc? | lowerErr stmt "internal error: `emit` accumulator not initialized"
            let esNext ← freshIdent "_es"; let cont ← recSame { bCtx with emitAcc? := some esNext } rest
            pure <| qctx.runPure `(let $esNext:ident : List Qed.Server.WsEmit := $esId ++ [$emitTerm]; $cont)
        | .async _ =>
            let evId ← freshIdent "_wsEv"; let cont ← recSame bCtx rest
            pure <| qctx.runPure `(let $evId:ident := $emitTerm; Qed.Server.MonadServer.wsBroadcast ($evId).topic ($evId).payload >>= fun _ => $cont)
        | .infallibleAsync => unreachable!
      return ← wrapHoists qctx mode bCtx steps body
    if let some (fn, rawArgs) := (matchNamedStmtCall? stmt).filter fun (n, _) => n == "setCookie" || n == "clearCookie" || n == "send" then
      if isPure then lowerErr stmt (if fn == "send" then "cannot call `send(...)` inside an `atomic:` block; emit SSE events outside `atomic:`" else "cannot call `setCookie`/`clearCookie` inside an `atomic:` block; emit cookies outside `atomic:`")
      let (effNm, argT, steps) ← lowerSideEffectCall qctx bCtx stmt fn rawArgs; let cont ← recSame bCtx rest
      return ← wrapHoists qctx mode bCtx steps (qctx.runPure `($(mkCIdent effNm) $argT >>= fun _ => $cont))
    let targetStx? := if stmt.getKind == ``qedStmtAssign then some (stmt.getArg 0)
      else ((matchPushCall? (stmt.getArg 0)).orElse fun _ => matchRemoveCall? (stmt.getArg 0)).map Prod.fst
    if let some targetStx := targetStx? then
      match mode with
      | .pure _ _ sCur =>
          if bCtx.loopMuts?.isSome then lowerErr stmt "cannot mutate server `state` field inside a synchronous `for` loop; mutate a `let mut` local or wrap server mutations in `atomic:`"
          return ← lowerPureMutationStmt qctx mode bCtx sCur stmt rest recSame
      | _ =>
          rejectSrvAssignPredict stmt; let _ ← parseLValPath qctx bCtx targetStx
          lowerErr stmt s!"cannot mutate server state outside an `atomic:` block in `{bCtx.fnName}` because `{bCtx.fnName}` uses `await`"
  let eStx := stmt.getArg 0; let (eTerm, steps) ← withCollectedHoists ((lowerExprM .val eStx).run (bCtx, qctx))
  let valTerm := if !isInf && isBareUnwrapExpr (!isPure) (← liftM getKnownQLeafNames) bCtx eStx then eTerm else qctx.runPure `(srvEnsureUnit($eTerm))
  wrapHoists qctx mode bCtx steps (← bindLet qctx mode Syntax.missing none valTerm (← recSame bCtx rest))

@[noinline] private partial def lowerBlockGo (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) (stmts : Array Syntax) : LowerM Term := do
  if stmts.isEmpty then return ← mkEmptyLeaf qctx mode ctx
  let (isPure, isInf) := (mode matches .pure .., mode matches .infallibleAsync)
  let stmt := stmts[0]!; let rest := stmts.extract 1 stmts.size; let k := stmt.getKind
  let bCtx := if isInf then ctx else { ctx with stateRule := if ctx.stateFields.isEmpty then .statelessServer else match mode with | .pure _ _ sCur => .pureStep sCur (pureOvs ctx) | _ => .forbidAsyncOutsideAtomic, allowAwait := !isPure }
  let recSame := fun c st => lowerBlockGo qctx mode c st
  let recWithState := fun c s st => lowerBlockGo qctx (match mode with | .pure inAtomic s₀ _ => .pure inAtomic s₀ s | other => other) c st
  match k with
  | ``qedStmtPass => recSame bCtx rest
  | ``qedStmtBreak =>
      let some lm := bCtx.loopMuts? | lowerErr stmt "`break` can only be used inside a `for` loop"
      return qctx.runPure (wrapLoopStep isPure lm ``Qed.QedLoopStep.breakLoop)
  | ``qedStmtContinue =>
      let some _ := bCtx.loopMuts? | lowerErr stmt "`continue` can only be used inside a `for` loop"
      mkEmptyLeaf qctx mode bCtx
  | ``qedStmtLetMut =>
      let lId : Ident := ⟨stmt.getArg 2⟩; let nm := lId.getId.eraseMacroScopes
      if bCtx.mutLocals.any (·.getId.eraseMacroScopes == nm) then lowerErr lId s!"mutable variable `{nm}` is already declared in this scope; update it with `{nm} = ...`"
      let (rhsTerm, steps) ← withCollectedHoists ((lowerExprM .val (stmt.getArg 5)).run (bCtx, qctx))
      let checkedRhs := if steps.isEmpty then qctx.runPure `(srvRejectUnhandledErr($rhsTerm)) else rhsTerm
      let cont ← recSame { bCtx with locals := bCtx.locals.push nm.toString, mutLocals := bCtx.mutLocals.push lId } rest
      let ty? ← lowerOptTypeNode (stmt.getArg 3)
      wrapHoists qctx mode bCtx steps (qctx.runPure <| match ty? with | some lTy => `(let $lId:ident : $lTy := $checkedRhs; $cont) | none => `(let $lId:ident := $checkedRhs; $cont))
  | ``qedStmtReturn => lowerReturn qctx mode bCtx stmt
  | ``qedStmtLet => lowerLetCore qctx mode bCtx stmt rest recSame
  | ``qedStmtLetElse =>
      let patStx := stmt.getArg 1; let patTerm ← liftMacroM (lowerQedPat patStx)
      let (scrutTerm, steps) ← withCollectedHoists ((lowerExprM .val (stmt.getArg 3)).run (bCtx, qctx)); let elseStmts := extractLetElseStmts stmt
      unless blockAlwaysTerminates bCtx.loopMuts?.isSome elseStmts do
        lowerErr stmt (if bCtx.loopMuts?.isSome then "guard `let ... = ... else` branch must `return`, `break`, or `continue` on all paths" else "guard `let ... = ... else` branch must `return` on all paths")
      let hMatch ← freshIdent "_srvM"; let thenT ← recSame (pushPatLocals bCtx (collectQedPatIds patStx)) rest; let elseT ← recSame bCtx elseStmts
      wrapHoists qctx mode bCtx steps (qctx.runPure `(match $hMatch:ident : $scrutTerm:term with | $patTerm => $thenT | _ => $elseT))
  | ``qedStmtIf =>
      let (condTerm, steps) ← withCollectedHoists ((lowerExprM .propGuard (stmt.getArg 1)).run (bCtx, qctx)); let hGuard ← freshIdent "_srvG"
      wrapHoists qctx mode bCtx steps (← lowerBranch qctx mode bCtx rest (suiteStmts (stmt.getArg 3)) bCtx (desugarElifs (stmt.getArg 4).getArgs (stmt.getArg 5)) isPure
        (fun t e => `(if $hGuard:ident : $condTerm then $t else $e)) recSame recWithState)
  | ``qedStmtIfLet =>
      let patStx := stmt.getArg 2; let patTerm ← liftMacroM (lowerQedPat patStx)
      let (scrutTerm, steps) ← withCollectedHoists ((lowerExprM .val (stmt.getArg 4)).run (bCtx, qctx)); let hMatch ← freshIdent "_srvM"
      wrapHoists qctx mode bCtx steps (← lowerBranch qctx mode bCtx rest (suiteStmts (stmt.getArg 6)) (pushPatLocals bCtx (collectQedPatIds patStx))
        (desugarElifs (stmt.getArg 7).getArgs (stmt.getArg 8)) false (fun t e => `(match $hMatch:ident : $scrutTerm:term with | $patTerm => $t | _ => $e)) recSame recWithState)
  | ``qedStmtMatch =>
      let (matchT, allSteps) ← lowerMatchScrutineesAndAlts qctx bCtx stmt rest recSame; wrapHoists qctx mode bCtx allSteps matchT
  | ``qedStmtFor => lowerSrvForFoldCore qctx mode bCtx stmt rest recSame
  | ``qedStmtAssign | ``qedStmtExpr => lowerAssignOrExprStmt qctx mode bCtx stmt rest recSame
  | ``qedStmtDbTransaction =>
      if isInf then lowerErr stmt s!"unsupported statement `{stxSnippet stmt}` in infallible async function `{ctx.fnName}`"
      if isPure then lowerErr stmt "cannot start a database `transaction` inside an `atomic:` block; run database transactions outside `atomic:`"
      let some (aliasRef, aliasName, txVar?, txStmts) := matchTxStmt? stmt | unreachable!
      lowerTxStmt qctx bCtx stmt aliasRef aliasName txVar? txStmts rest recSame
  | ``qedStmtAtomic =>
      match mode with
      | .pure inAtomic .. =>
          if inAtomic then lowerErr stmt "nested `atomic` blocks are forbidden"
          else if ctx.stateFields.isEmpty then lowerErr stmt "`atomic` is only valid in a `server` with `state` declarations"
          else lowerErr stmt s!"redundant `atomic` block: `{ctx.fnName}` has no `await` calls, so it already executes atomically"
      | .async stateTyTerm? => lowerAtomicStmt qctx bCtx stateTyTerm? stmt rest (fun c s0 s st => lowerBlockGo qctx (.pure true s0 s) c st) recSame
      | .infallibleAsync => lowerErr stmt s!"unsupported statement `{stxSnippet stmt}` in infallible async function `{ctx.fnName}`"
  | `Qed.Server.atomicExport =>
      let .pure _ _ sCur := mode | unreachable!
      let expTerm : Term := ⟨stmt.getArg 0⟩
      return qctx.runPure do
        let payload ← if bCtx.wrapReturnSumInl then Db.mkAppC ``Sum.inr #[expTerm] else pure expTerm
        mkPureLeaf bCtx (← materializeState sCur (pureOvs ctx)) (← Db.mkOptTerm (some (← Db.mkAppC ``Except.ok #[payload])))
  | _ =>
      let sn := stxSnippet stmt
      lowerErr stmt s!"unsupported statement{if sn.isEmpty then s!"({k})" else s!" `{sn}`"} in {if isPure then "server" else if isInf then "infallible async" else "async server"} function `{ctx.fnName}`"

private def lowerBlock (mode : BlockMode) (ctx : LowerCtx) (stmts : Array Syntax) : LowerM Term := do
  lowerBlockGo (← liftM Lang.getPureQuotCtxCmd) mode ctx stmts

def lowerPureBlock (ctx : LowerCtx) (inAtomic : Bool) (s₀ sCur : Ident) (stmts : Array Syntax) : LowerM Term := lowerBlock (.pure inAtomic s₀ sCur) ctx stmts
def lowerAsyncBlock (ctx : LowerCtx) (stateTyTerm? : Option Term) (stmts : Array Syntax) : LowerM Term := lowerBlock (.async stateTyTerm?) ctx stmts
def lowerInfallibleAsyncBlock (ctx : LowerCtx) (stmts : Array Syntax) : LowerM Term := lowerBlock .infallibleAsync ctx stmts

end BlockLowering
end Qed.Server
