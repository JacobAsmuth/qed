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

private inductive BlockKind where
  | pure (inAtomic : Bool) (s₀ sCur : Lean.Ident)
  | async (stateTyTerm? : Option Lean.Term)
  | infallibleAsync

private inductive BlockMode where
  | pure (inAtomic : Bool) (s₀ sCur : Lean.Ident) (matCur : Lean.Term)
  | async (stateTyTerm? : Option Lean.Term)
  | infallibleAsync

private def BlockMode.isPure : BlockMode → Bool | .pure .. => true | _ => false
private def BlockMode.isInf : BlockMode → Bool | .infallibleAsync => true | _ => false

@[noinline] private def runMacro {α : Type} (m : Lean.MacroM α) : LowerM α := Lean.Elab.liftMacroM m

private def freshIdent (pfx : String) : LowerM Lean.Ident := do
  let n := (← get).nextId; modify fun s => { s with nextId := n + 1 }
  return Lean.mkIdent (Lean.Name.mkSimple s!"{pfx}{n}")

private def recordMutated (f : String) : LowerM Unit := modify fun s => { s with mutated := pushUnique s.mutated f }
private def recordExtRoot (n : Lean.Name) : LowerM Unit := modify fun s => { s with extRoots := pushUnique s.extRoots n }

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
  | ``qedStmtIf =>
      (#[stx.getArg 1], #[(#[], suiteStmts (stx.getArg 3))] ++ (desugarElifs (stx.getArg 4).getArgs (stx.getArg 5)).elim #[] fun es => #[(#[], es)])
  | ``qedStmtIfLet =>
      (#[stx.getArg 4], #[(collectQedPatIds (stx.getArg 2), suiteStmts (stx.getArg 6))] ++ (extractElseSuite (stx.getArg 7)).elim #[] fun es => #[(#[], es)])
  | ``qedStmtMatch =>
      ((stx.getArg 1).getSepArgs, (stx.getArg 3).getArgs.map fun c => (collectCasePatIds (extractCasePatAlts (c.getArg 1)), suiteStmts (c.getArg 3)))
  | ``qedStmtFor =>
      let bStx := stx.getArg 1
      (#[stx.getArg 3], #[(if bStx.isIdent then #[bStx.getId.eraseMacroScopes] else #[], suiteStmts (stx.getArg 5))])
  | ``qedStmtAtomic => (#[], #[(#[], suiteStmts (stx.getArg 2))])
  | ``qedStmtDbTransaction => (#[], #[(#[], suiteStmts (stx.getArg 3))])
  | ``qedStmtLetElse => (#[stx.getArg 3], #[(#[], extractLetElseStmts stx)])
  | _ => (#[], #[])

mutual
  partial def stmtAlwaysTerminates (allowLoopExit : Bool) (stx : Lean.Syntax) : Bool :=
    match stx.getKind with
    | ``qedStmtReturn => true
    | ``qedStmtBreak | ``qedStmtContinue => allowLoopExit
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
    "lookup?", "getElem?", "maxAge?"].foldl (·.insert ·) {}

private def leafOfDottedStr (s : String) : String := match s.splitOn "." |>.reverse with | h :: _ => h | [] => s

partial def exprHasUnwrapWith (knownQ boundLocals : Std.HashSet String) (stx : Lean.Syntax) : Bool :=
  match stx.getKind with
  | ``qedUnwrap => true
  | ``qedDotIdent | ``qedLam1 | ``qedLamN | ``qedAllIn | ``qedAnyIn | ``qedAllVars => false
  | ``qedIdent => let s := (stx.getArg 0).getId.toString; s.endsWith "?" && !knownQ.contains (leafOfDottedStr s) && !boundLocals.contains s
  | ``qedProj => let f := (stx.getArg 2).getId.toString; (f.endsWith "?" && !knownQ.contains f) || exprHasUnwrapWith knownQ boundLocals (stx.getArg 0)
  | _ => stx.getArgs.any (exprHasUnwrapWith knownQ boundLocals)

def exprHasUnwrap (stx : Lean.Syntax) : Bool := exprHasUnwrapWith knownQMethodSet {} stx

mutual
  partial def stmtMayReturnEarly (stx : Lean.Syntax) : Bool :=
    match stx.getKind with
    | ``qedStmtReturn | ``qedStmtAtomic | ``qedStmtDbTransaction | ``qedStmtLetElse => true
    | ``qedStmtLet => (stx.getArg 5).getNumArgs > 0 || exprHasUnwrap (stx.getArg 4)
    | ``qedStmtIf | ``qedStmtIfLet | ``qedStmtMatch =>
        let (es, suites) := stmtChildSuites stx; es.any exprHasUnwrap || suites.any fun (_, bs) => blockMayReturnEarly bs
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
  | .forbidAsyncOutsideAtomic => throwErrorAt ref s!"cannot access server state `{field}` outside an `atomic` block in `{ctx.fnName}` because `{ctx.fnName}` uses `await` (prevents TOCTOU data races across suspension points)"
  | .forbidInRequires => throwErrorAt ref s!"`requires` precondition in `{ctx.fnName}` cannot reference mutable server state `{field}`; check `{field}` inside the function body instead"
  | .forbidInEnsures => throwErrorAt ref s!"`ensures` postcondition in `{ctx.fnName}` cannot reference mutable server state `{field}`; state postconditions on `result` and parameters only"
  | .statelessServer => throwErrorAt ref s!"unknown identifier `{field}`"

private def resolveStateFieldBase (qctx : PureQuotCtx) (ref : Syntax) (ctx : LowerCtx) (field : Name) : LowerM Term := do
  let sv ← checkStateRead ref ctx field.toString
  if let .pureStep _ ovs := ctx.stateRule then if let some (_, ovId) := ovs.find? (·.1 == field.toString) then return ⟨mkIdentFrom ref ovId.getId⟩
  return Db.runQuot qctx `(($sv).$(mkIdentFrom ref field):ident)

@[noinline] private def resolveDottedIdent (qctx : PureQuotCtx) (ref : Syntax) (ctx : LowerCtx) (id : Ident) : LowerM Term := do
  match id.getId.components with
  | [] => throwErrorAt ref "empty identifier"
  | root :: rest =>
      let rStr := root.toString
      if rest.isEmpty && (rStr == "true" || rStr == "false" || rStr == "none") then
        return Db.runQuot qctx (if rStr == "true" then `(true) else if rStr == "false" then `(false) else `(none))
      else if ctx.locals.contains rStr then return Db.runQuot qctx (foldProjTerms ref ⟨mkIdentFrom ref root⟩ rest)
      else if rStr == "ctx" || ctx.envVars.contains rStr then
        if ctx.forbidCtxEnv then
          let what := if rest.isEmpty && rStr != "ctx" then s!"`env` binding `{rStr}`" else s!"`{rStr}`"
          throwErrorAt ref s!"`ensures` postcondition in `{ctx.fnName}` cannot reference {what} because client decoders re-verify `ensures` on the wire"
        return Db.runQuot qctx (foldProjTerms ref ⟨mkIdentFrom ref root⟩ rest)
      else if ctx.stateFields.contains rStr then
        return Db.runQuot qctx (foldProjTerms ref (← resolveStateFieldBase qctx ref ctx root) rest)
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

private abbrev SrvExprM := ReaderT (LowerCtx × PureQuotCtx) LowerM
private def readCtx : SrvExprM LowerCtx := return (← read).1
private def readQ : SrvExprM PureQuotCtx := return (← read).2

@[noinline] private partial def lowerJsonPayload (go : ExprMode → Syntax → SrvExprM Term) (stx : Syntax) : SrvExprM Term := do
  let qctx ← readQ; let u := unwrapParens1 stx
  if u.getKind == ``qedRecLit && (u.getArg 1).getNumArgs != 2 then
    let pairs ← (u.getArg 2).getSepArgs.mapM fun f => do
      let op := (f.getArg 1).getAtomVal; if op != "=" then throwErrorAt f s!"`{op}` is not allowed inside a JSON object literal"
      return Db.runQuot qctx `(($(Syntax.mkStrLit (f.getArg 0).getId.eraseMacroScopes.toString), $(← lowerJsonPayload go (f.getArg 2))))
    return Db.runQuot qctx `(Qed.Json.obj [$[$pairs],*])
  else if u.getKind == ``qedArrLit then
    let elems ← (u.getArg 1).getSepArgs.mapM (lowerJsonPayload go); return Db.runQuot qctx `(Qed.Json.arr [$elems,*])
  else return Db.runQuot qctx `(Qed.toJson $(← go .val stx))

@[noinline] private def lowerCheckedCall (stx : Syntax) (rawArgs : Array Syntax) (go : ExprMode → Syntax → SrvExprM Term)
    (kindLabel arityLabel dispName : String) (forbidInEnsures : Bool) (minP maxP : Nat)
    (dbWrite hasCookieOp mutatesState : Bool) (extRoot? : Option Name) (fnTerm : Term) (preArgs : Array Term) : SrvExprM Term := do
  let (ctx, qctx) ← read
  if ctx.forbidCtxEnv && forbidInEnsures then throwErrorAt stx s!"{kindLabel} `{dispName}` cannot be called inside `ensures` or client-checked `requires`"
  if rawArgs.any (·.getKind == ``qedCallArgNamed) then throwErrorAt stx s!"named arguments are not supported when calling {kindLabel} `{dispName}`"
  if rawArgs.size < minP || rawArgs.size > maxP then
    throwErrorAt stx s!"{arityLabel} `{dispName}` expects {if minP == maxP then s!"{maxP}" else s!"{minP}..{maxP}"} argument(s), got {rawArgs.size}"
  let argTerms ← rawArgs.mapM fun ra => go .val (ra.getArg 0)
  if dbWrite then modify fun s => { s with dbWrite := true }
  if hasCookieOp then modify fun s => { s with hasCookieOp := true }
  if mutatesState then recordMutated "__helper__"
  if let some root := extRoot? then recordExtRoot root
  return Db.runQuot qctx (mkAppTerms fnTerm (preArgs ++ argTerms))

private def ctxHasIdent (ctx : LowerCtx) (s : String) : Bool :=
  ctx.locals.contains s || ctx.stateFields.contains s || ctx.envVars.contains s

@[noinline] private def lowerFailCall (stx : Syntax) (rawArgs : Array Syntax) (go : ExprMode → Syntax → SrvExprM Term) : SrvExprM Term := do
  let (ctx, qctx) ← read
  if rawArgs.any (·.getKind == ``qedCallArgNamed) then throwErrorAt stx "`fail(...)` takes positional arguments `fail(.tag)`, `fail(.tag, msg)`, `fail(msg)`, or `fail(code, msg)`"
  if (rawArgs.size == 1 || rawArgs.size == 2) && (unwrapParens1 rawArgs[0]![0]).getKind == ``qedDotIdent then
    let uDot := unwrapParens1 rawArgs[0]![0]; let tagId : Ident := ⟨uDot.getArg 1⟩
    let some errTy := ctx.domainErrTy? | throwErrorAt stx "internal error: missing inferred domain error type for `fail(.tag)`"
    let msgTerm ← if rawArgs.size == 2 then go .val rawArgs[1]![0] else pure (Syntax.mkStrLit tagId.getId.toString)
    let dotNode : Term := ⟨Syntax.node (.fromRef uDot) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef uDot) ".", tagId.raw]⟩
    return Db.runQuot qctx `(Qed.Server.mkFailDom (ε := $errTy) ($dotNode : $errTy) $msgTerm)
  if ctx.domainErrTy?.isSome then throwErrorAt stx "cannot mix typed `fail(.tag)` and untyped `fail(...)` inside the same function; use `fail(.tag, msg)`"
  if rawArgs.size == 1 then return Db.runQuot qctx `(Qed.Server.mkFail1 $(← go .val rawArgs[0]![0]))
  if rawArgs.size == 2 then return Db.runQuot qctx `(Qed.Server.mkFail2 $(← go .val rawArgs[0]![0]) $(← go .val rawArgs[1]![0]))
  throwErrorAt stx "`fail(...)` expects `(.tag)`, `(.tag, msg)`, `(message)`, or `(code, message)`"

private def httpRespSpecs : Array (String × Name × Nat) := #[
  ("text", `Qed.Server.HttpResponse.text, 200), ("json", `Qed.Server.HttpResponse.jsonOf, 200),
  ("html", `Qed.Server.HttpResponse.html, 200), ("redirect", `Qed.Server.HttpResponse.redirect, 302), ("bytes", `Qed.Server.HttpResponse.bytes, 200)]

@[noinline] private def lowerHttpRespCall (stx : Syntax) (cstr : String) (ctorNm : Name) (defSt : Nat) (rawArgs : Array Syntax)
    (go : ExprMode → Syntax → SrvExprM Term) : SrvExprM Term := do
  let qctx ← readQ
  let (posArgs, namedArgs) ← splitCallArgs cstr rawArgs (some ["status"])
  let stT ← match findNamedArg? namedArgs "status" with | some s => go .val s | none => pure (Db.runQuot qctx `(($(quote defSt) : Nat)))
  if cstr == "bytes" then
    if posArgs.size != 2 then throwErrorAt stx "`bytes(contentType, body[, status = 200])` expects a content type and body"
    return Db.runQuot qctx `(Qed.Server.HttpResponse.bytes $(← go .val posArgs[0]!) $(← go .val posArgs[1]!) $stT)
  if posArgs.size != 1 then throwErrorAt stx s!"`{cstr}(...)` expects one positional argument (and optional `status = ...`)"
  let argT ← if cstr == "json" then lowerJsonPayload go posArgs[0]! else go .val posArgs[0]!
  return Db.runQuot qctx `($(mkIdent ctorNm) $argT $stT)

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
      let svcOpt? : Option (ServiceInfo × Bool) ← match ctx.services.find? (·.1 == aliasName) with
        | some (_, si) => pure (some (si, false))
        | none => pure ((lookupService? (← getEnv) (← getCurrNamespace) (← getOpenDecls) (Name.mkSimple aliasName)).map (·, true))
      if let some (svcInfo, isDirect) := svcOpt? then
        let some m := svcInfo.methods.find? (·.name == methName)
          | throwErrorAt stx s!"service `{svcInfo.shortName}` has no method `{methName}`{Qed.Diag.didYouMean methName (svcInfo.methods.toList.map (·.name))}"
        let preArgs : Array Term := if m.takesCtx then #[ctx.ctxTerm?.getD ⟨(mkIdent `ctx).raw⟩] else #[]
        return some (← lowerCheckedCall stx rawArgs go (if m.isMonadic then "monadic service method" else "service method") "service method"
          s!"{svcInfo.shortName}.{methName}" m.isMonadic m.minParamCount m.paramCount m.dbWrite m.hasCookieOp false
          (if isDirect then some (Name.mkSimple aliasName) else none) (mkIdentFrom stx m.defConst : Term) preArgs)
  if calleeStx.getKind == ``qedIdent then
    let cname := (calleeStx.getArg 0).getId.eraseMacroScopes
    if cname == `old then
      match ctx.stateRule with
      | .invariantProp curV oldV _ =>
          if rawArgs.size != 1 || rawArgs[0]!.getKind != ``qedCallArgPos then throwErrorAt stx "`old(...)` expects exactly one positional expression argument"
          return some (← withReader (fun (c, q) => ({ c with stateRule := .invariantProp curV oldV true }, q)) (go mode rawArgs[0]![0]))
      | _ => throwErrorAt stx "`old(...)` may only be used inside `invariant` declarations"
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

private def checkAllowAwait (ref : Syntax) : SrvExprM Unit := do
  unless (← readCtx).allowAwait do throwErrorAt ref "`await` cannot be used inside an `atomic` block, lambda, `requires`, or `invariant`; perform external I/O outside `atomic`"

private def hoistAwaitUnwrap (recGo : ExprMode → Syntax → SrvExprM Term) (stx awaitRef callStx : Syntax) (mode : ExprMode) : SrvExprM Term := do
  checkAllowAwait awaitRef
  let callTerm ← recGo .val callStx; let tmp ← liftM <| freshIdent "_srvAw"
  modify fun s => { s with hoisted := s.hoisted.push (.awaitUnwrap stx tmp callTerm) }
  return Db.runQuot (← readQ) (finishTermMode mode ⟨tmp⟩)

@[noinline] private def mkSrvLowerHooks (recGo : ExprMode → Syntax → SrvExprM Term) : LowerHooks SrvExprM :=
  { LowerHooks.mkDefault (fun ref msg => throwErrorAt ref msg) with
    lowerIdent := fun stx id mode => do
      let (ctx, qctx) ← read; let (cid, q) := peelTrailingQ (← liftM (m := CommandElabM) getKnownQLeafNames) (ctxHasIdent ctx) id
      return Db.runQuot qctx (finishTermMode mode (← liftM <| hoistPureUnwraps stx ctx q (← resolveDottedIdent qctx stx ctx cid)))
    lowerProj := fun stx objT fld mode => do
      let (ctx, qctx) ← read; let (cf, q) := peelTrailingQ (← liftM (m := CommandElabM) getKnownQLeafNames) (fun _ => false) fld
      return Db.runQuot qctx (finishTermMode mode (← liftM <| hoistPureUnwraps stx ctx q (Db.runQuot qctx `(($objT).$cf:ident))))
    lowerIndex := fun _ arrT idxT mode => do return Db.runQuot (← readQ) (finishTermMode mode (← `(srvGetElem($arrT, $idxT))))
    lowerCall := lowerSrvCallHook
    lowerUnwrap := fun stx innerRaw mode => do
      let (ctx, qctx) ← read; liftM <| checkAllowUnwrap stx ctx; let inner := unwrapParens1 innerRaw
      if inner.getKind == ``qedAwait then hoistAwaitUnwrap recGo stx inner (inner.getArg 1) mode
      else return Db.runQuot qctx (finishTermMode mode (← liftM <| hoistPureUnwraps stx ctx 1 (← recGo .val innerRaw)))
    lowerAwait := fun stx argRaw mode => do
      checkAllowAwait stx; let inner := unwrapParens1 argRaw
      if inner.getKind == ``qedUnwrap then
        let ctx ← readCtx
        liftM <| checkAllowUnwrap stx ctx s!"operator `?` cannot be used in `{ctx.fnName}` because its return type is neither fallible (`T!`) nor optional (`T?`); handle the `await` error with `let x = await ... catch err:`"
        hoistAwaitUnwrap recGo stx stx (inner.getArg 0) mode
      else
        let callTerm ← recGo .val argRaw; let tmp ← liftM <| freshIdent "_srvAw"
        modify fun s => { s with hoisted := s.hoisted.push (.awaitPlain stx tmp callTerm) }
        return Db.runQuot (← readQ) (finishTermMode mode ⟨tmp⟩)
    lowerArrElem := fun t => do return Db.runQuot (← readQ) `(srvAutoField($t))
    wrapNamedField := fun t => do return Db.runQuot (← readQ) `(srvAutoField($t))
    lowerType := fun t => liftM <| runMacro (return (← lowerQedType t false).1)
    lowerPat := fun p => liftM <| runMacro (lowerQedPat p)
    withLocals := fun names k => withReader (fun (c, q) => ({ c with locals := c.locals ++ names, allowAwait := false, allowUnwrap := false }, q)) k
    useDirectArray := false
    freshIdent := fun pfx => liftM <| freshIdent pfx }

private partial def lowerExprM (mode : ExprMode) (stx : Syntax) : SrvExprM Term := lowerQedExpr (mkSrvLowerHooks lowerExprM) mode stx

@[noinline] def lowerExpr (ctx : LowerCtx) (mode : ExprMode) (stx : Syntax) : LowerM Term := do
  (lowerExprM mode stx).run (ctx, ← liftM Db.getPureQuotCtx)

private def lowerExprQ (qctx : PureQuotCtx) (ctx : LowerCtx) (mode : ExprMode) (stx : Syntax) : LowerM Term := (lowerExprM mode stx).run (ctx, qctx)

private def withCollectedHoists {α : Type} (act : LowerM α) : LowerM (α × Array HoistedStep) := do
  let saved := (← get).hoisted; modify fun s => { s with hoisted := #[] }
  let res ← act; let steps := (← get).hoisted; modify fun s => { s with hoisted := saved }; return (res, steps)

private def lowerExprCollectingHoists (qctx : PureQuotCtx) (ctx : LowerCtx) (mode : ExprMode) (stx : Syntax) : LowerM (Term × Array HoistedStep) :=
  withCollectedHoists (lowerExprQ qctx ctx mode stx)

/-! ## LValue Mutation Path Parsing & Functional Lens Construction -/

private partial def parseLValPath (qctx : PureQuotCtx) (ctx : LowerCtx) (stx : Syntax) : LowerM (Ident × Array LValStep) := do
  match stx.getKind with
  | ``qedIdent =>
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
  | ``qedProj => let (r, ps) ← parseLValPath qctx ctx (stx.getArg 0); return (r, ps.push (.field ⟨stx.getArg 2⟩))
  | ``qedIndex =>
      if (stx.getArg 4).getNumArgs == 0 then
        let (r, ps) ← parseLValPath qctx ctx (stx.getArg 0); return (r, ps.push (.index (← lowerExprQ qctx ctx .val (stx.getArg 2))))
      else throwErrorAt stx "invalid mutation target; expected `stateField`, `stateField.sub`, or `stateField[i].sub`"
  | _ => throwErrorAt stx "invalid mutation target; expected `stateField`, `stateField.sub`, or `stateField[i].sub`"

@[noinline] private partial def withUpdatedPathCPS (qctx : PureQuotCtx) (steps : Array LValStep) (idx : Nat) (curVal : Term)
    (mkLeafNew : Term → LowerM Term) (k : Term → LowerM Term) : LowerM Term := do
  if h : idx < steps.size then
    match steps[idx] with
    | .field fid =>
        withUpdatedPathCPS qctx steps (idx + 1) (Db.runQuot qctx `(($curVal).$fid:ident)) mkLeafNew fun ch =>
          k (Db.runQuot qctx `({ $curVal with $fid:ident := srvAutoField($ch) }))
    | .index idxT =>
        let elemId ← freshIdent "_elem"; let hElemId ← freshIdent "_srvEqElem"
        let body ← withUpdatedPathCPS qctx steps (idx + 1) ⟨elemId⟩ mkLeafNew fun el => k (Db.runQuot qctx `(srvSetElem($curVal, $idxT, $el)))
        return Db.runQuot qctx `(Qed.Server.srvLetEq (srvGetElem($curVal, $idxT)) (fun $elemId:ident $hElemId:ident => $body))
  else k (← mkLeafNew curVal)

private def getPureOverrides (ctx : LowerCtx) : Array (String × Ident) := match ctx.stateRule with | .pureStep _ ovs => ovs | _ => #[]
private def setPureOverride (ctx : LowerCtx) (sCur : Ident) (fld : String) (vId : Ident) : LowerCtx :=
  { ctx with stateRule := .pureStep sCur ((getPureOverrides ctx).filter (·.1 != fld) |>.push (fld, vId)) }
private def materializeState (sCur : Ident) (ovs : Array (String × Ident)) : PureQuotM Term := do
  if ovs.isEmpty then `(($sCur))
  else let fIds := ovs.map fun p => mkIdent (Name.mkSimple p.1); let fVars : Array Term := ovs.map (⟨·.2.raw⟩); `({ $sCur with $[$fIds:ident := $fVars:term],* })

/-! ## Pure Quotation Leaf / Loop / Atomic Builders -/

private def isFailCall (stx : Syntax) : Bool :=
  let u := unwrapParens1 stx; u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId == `fail

@[noinline] private def wrapOkValue (ctx : LowerCtx) (valTerm : Term) : PureQuotM Term := do
  let inner ← match ctx.innerOptTy? with
    | some innerTy => if valTerm.raw.isIdent && valTerm.raw.getId.eraseMacroScopes == `none then `((none : Option $innerTy)) else `(Qed.Server.SrvLiftOpt.liftOpt (Inner := $innerTy) $valTerm)
    | none => `(srvAutoField($valTerm))
  if ctx.wrapReturnSumInl then `(Except.ok (Sum.inl $inner)) else `(Except.ok $inner)

private def errTyOf (ctx : LowerCtx) : PureQuotM Term := match ctx.domainErrTy? with | some et => `(Qed.Server.SrvFailure $et) | none => `(Qed.Server.ApiError)
private def mkPureLeaf (ctx : LowerCtx) (stTerm optTerm : Term) : PureQuotM Term := match ctx.emitAcc? with | some esId => `(($stTerm, $esId, $optTerm)) | none => `(($stTerm, $optTerm))
private def mkPureErrLeaf (ctx : LowerCtx) (s₀ : Ident) (errTerm : Term) : PureQuotM Term :=
  match ctx.emitAcc? with | some _ => `(($s₀, ([] : List Qed.Server.WsEmit), some (Except.error $errTerm))) | none => `(($s₀, some (Except.error $errTerm)))

private def wrapLoopStep (isPure : Bool) (lm : Array Ident) (ctor : Name) (val? : Option Term := none) : PureQuotM Term := do
  let stPack ← mkMutPack lm.toList
  let step ← match val? with | some v => `($(mkCIdent ctor) $stPack $v) | none => `($(mkCIdent ctor) $stPack)
  if isPure then pure step else `(Pure.pure $step)

private def wrapLoopRet (mode : BlockMode) (ctx : LowerCtx) (val : Term) (pureLeaf : Term → PureQuotM Term) : PureQuotM Term :=
  match ctx.loopMuts? with
  | some lm => wrapLoopStep mode.isPure lm ``Qed.QedLoopStep.ret (some val)
  | none => match mode with | .pure .. => pureLeaf val | .async _ => `(Pure.pure (some $val)) | .infallibleAsync => `(Pure.pure $val)

private def mkOkLeaf (mode : BlockMode) (ctx : LowerCtx) (valTerm : Term) (isUnitEmpty : Bool := false) : PureQuotM Term := do
  let ok ← match mode with | .infallibleAsync => if isUnitEmpty then pure valTerm else `(srvAutoField($valTerm)) | _ => wrapOkValue ctx valTerm
  wrapLoopRet mode ctx ok fun v => do match mode with | .pure _ _ _ m => mkPureLeaf ctx m (← `(some $v)) | _ => pure v

private def mkErrLeaf (mode : BlockMode) (ctx : LowerCtx) (errTerm : Term) : PureQuotM Term := do
  wrapLoopRet mode ctx (← `(Except.error $errTerm)) fun _ => match mode with | .pure _ s₀ _ _ => mkPureErrLeaf ctx s₀ errTerm | _ => unreachable!

private def mkEmptyLeaf (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) : CommandElabM Term := do
  if let some lm := ctx.loopMuts? then return Db.runQuot qctx (wrapLoopStep mode.isPure lm ``Qed.QedLoopStep.next)
  match mode with
  | .pure _ _ _ m => return Db.runQuot qctx (mkPureLeaf ctx m (← `(none)))
  | .async _ => return Db.runQuot qctx `(Pure.pure none)
  | .infallibleAsync => throwError s!"missing `return` on fallthrough path of `{ctx.fnName}`"

@[noinline] private def lowerEmitCall (qctx : PureQuotCtx) (ctx : LowerCtx) (stmt : Syntax) (chId : Ident) (rawArgs : Array Syntax) : LowerM (Term × Array HoistedStep) := do
  let chStr := chId.getId.eraseMacroScopes.toString
  let some chSig := ctx.channels.find? (·.name == chStr)
    | throwErrorAt chId s!"unknown WebSocket `channel` `{chStr}` in `.emit(...)` (declared channels: [{String.intercalate ", " (ctx.channels.toList.map (·.name))}])"
  if rawArgs.size != chSig.paramCount + 1 then
    throwErrorAt stmt s!"`{chStr}.emit(...)` expects {chSig.paramCount + 1} argument(s) ({chSig.paramCount} channel param(s) + 1 event), got {rawArgs.size}"
  let (argTerms, allSteps) ← withCollectedHoists <| rawArgs.mapM fun ra => do
    unless ra.getKind == ``qedCallArgPos do throwErrorAt ra s!"named arguments are not supported in `{chStr}.emit(...)`"
    lowerExprQ qctx ctx .val (ra.getArg 0)
  return (Db.runQuot qctx do
    let mut call ← mkAppTerms (chSig.mkEmitId : Term) (argTerms.extract 0 chSig.paramCount)
    call ← `($call (srvAutoField($(argTerms[chSig.paramCount]!))))
    if chSig.hasEnsures then `($call (srvAutoEmit(True))) else pure call, allSteps)

@[noinline] def mkAtomicRunTerm (s0Id : Ident) (stateTyTerm committed : Term) (readOnly hasEmit : Bool)
    (onResult? : Option (Ident × (Term → CommandElabM Term)) := none) : CommandElabM Term := do
  let qctx ← Db.getPureQuotCtx
  let runCall := Db.runQuot qctx <| if readOnly then `(Qed.Server.MonadAtomic.runAtomicRead (fun ($s0Id:ident : $stateTyTerm) => ($committed).2))
    else `(Qed.Server.MonadAtomic.runAtomic (fun ($s0Id:ident : $stateTyTerm) => $committed))
  match hasEmit, onResult? with
  | true, some (pairId, onRes) => let r ← onRes (Db.runQuot qctx `(($pairId).1)); return Db.runQuot qctx `($runCall >>= fun $pairId:ident => Qed.Server.flushWsEmits ($pairId).2 >>= fun _ => $r)
  | true, none => return Db.runQuot qctx `($runCall >>= fun _emitPair => Qed.Server.flushWsEmits (_emitPair).2 >>= fun _ => Pure.pure (_emitPair).1)
  | false, some (resId, onRes) => let r ← onRes ⟨resId.raw⟩; return Db.runQuot qctx `($runCall >>= fun $resId:ident => $r)
  | false, none => pure runCall

end ExprLowering

section BlockLowering
open Lean Elab Command

@[noinline] private def wrapUnwrapStep (mode : BlockMode) (ctx : LowerCtx) (tmp : Ident) (valTerm acc : Term) : PureQuotM Term := do
  if !ctx.hasFallible then if let some innerTy := ctx.innerOptTy? then
    if let some lm := ctx.loopMuts? then
      let earlyLeaf ← wrapLoopStep mode.isPure lm ``Qed.QedLoopStep.ret (some (← `(_early)))
      return ← `(match Qed.Server.SrvUnwrapOpt.unwrapOpt (Inner := $innerTy) $valTerm with | Except.error _early => $earlyLeaf | Except.ok $tmp:ident => $acc)
    match mode with
    | .pure _ s₀ _ m =>
        return ← `(match Qed.Server.SrvUnwrapOpt.unwrapOpt (Inner := $innerTy) $valTerm with
          | Except.error (Except.ok none) => $(← mkPureLeaf ctx m (← `(some (Except.ok none))))
          | Except.error (Except.error _e) => $(← mkPureErrLeaf ctx s₀ (← `(_e))) | Except.ok $tmp:ident => $acc)
    | .async _ => return ← `(match Qed.Server.SrvUnwrapOpt.unwrapOpt (Inner := $innerTy) $valTerm with | Except.error _early => Pure.pure (some _early) | Except.ok $tmp:ident => $acc)
    | .infallibleAsync => unreachable!
  `(match Qed.Server.SrvUnwrap.unwrap (E := $(← errTyOf ctx)) $valTerm with | Except.error _e => $(← mkErrLeaf mode ctx (← `(_e))) | Except.ok $tmp:ident => $acc)

@[noinline] private def wrapHoists (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) (steps : Array HoistedStep) (body : Term) : LowerM Term :=
  steps.foldrM (init := body) fun step acc => do
    match step, mode with
    | .awaitUnwrap ref _ _, .pure .. | .awaitPlain ref _ _, .pure .. => throwErrorAt ref "`await` cannot appear inside a pure/atomic block"
    | .awaitUnwrap ref _ _, .infallibleAsync => throwErrorAt ref "operator `?` cannot be used in an infallible function; declare its return type `-> T!` or use `catch`"
    | .pureUnwrap _ _, .infallibleAsync => throwError "operator `?` cannot be used in an infallible function"
    | .awaitUnwrap _ tmp callTerm, .async _ =>
        let rawTmp ← freshIdent "_srvRaw"
        return Db.runQuot qctx do `($callTerm >>= fun $rawTmp:ident => $(← wrapUnwrapStep mode ctx tmp ⟨rawTmp⟩ acc))
    | .awaitPlain _ tmp callTerm, .async _ | .awaitPlain _ tmp callTerm, .infallibleAsync =>
        return Db.runQuot qctx `((srvAwaitPlain($callTerm)) >>= fun $tmp:ident => $acc)
    | .pureUnwrap tmp valTerm, _ => return Db.runQuot qctx (wrapUnwrapStep mode ctx tmp valTerm acc)

private def lowerOptTypeNode (optNode : Syntax) : LowerM (Option Term) :=
  if optNode.getNumArgs == 2 then some <$> runMacro (return (← lowerQedType (optNode.getArg 1) false).1) else pure none

@[noinline] private def bindLet (qctx : PureQuotCtx) (mode : BlockMode) (xStx : Syntax) (ty? : Option Term) (val cont : Term) : LowerM Term := do
  match mode with
  | .pure .. =>
      let hEq ← freshIdent "_srvEq"
      let tv := Db.runQuot qctx <| match ty? with | some ty => `(($val : $ty)) | none => pure val
      if xStx.isIdent then return Db.runQuot qctx `(Qed.Server.srvLetEq $tv (fun $(⟨xStx⟩):ident $hEq:ident => $cont))
      else if xStx.getKind == ``qedLetPatTuple then
        let tupId ← freshIdent "_srvTup"; let pat ← runMacro (lowerLetBinderPat xStx)
        return Db.runQuot qctx `(Qed.Server.srvLetEq $tv (fun $tupId:ident $hEq:ident => let $pat:term := $tupId:ident; $cont))
      else return Db.runQuot qctx `(Qed.Server.srvLetEq $tv (fun $(← freshIdent "_srvDiscard"):ident $hEq:ident => $cont))
  | .async _ | .infallibleAsync => return Db.runQuot qctx (mkLetBindTerm xStx ty? val cont)

private def pushPatLocals (ctx : LowerCtx) (patIds : Array Name) : LowerCtx :=
  { ctx with locals := ctx.locals ++ patIds.map (·.toString), mutLocals := ctx.mutLocals.filter fun m => !patIds.contains m.getId.eraseMacroScopes }

private def pushOptLocal (ctx : LowerCtx) (xStx : Syntax) : LowerCtx :=
  let ids := collectLetBinderIds xStx; if ids.isEmpty then ctx else pushPatLocals ctx ids

private def isBareUnwrapExpr (allowAwait : Bool) (knownQ : Std.HashSet String) (ctx : LowerCtx) (eStx : Syntax) : Bool :=
  let u := unwrapParens1 eStx
  u.getKind == ``qedUnwrap || (allowAwait && u.getKind == ``qedAwait && (unwrapParens1 (u.getArg 1)).getKind == ``qedUnwrap) ||
  (eStx.getKind == ``qedIdent && let s := (eStx.getArg 0).getId.toString; s.endsWith "?" && !knownQ.contains (leafOfDottedStr s) && !ctxHasIdent ctx s) ||
  (eStx.getKind == ``qedProj && let f := (eStx.getArg 2).getId.toString; f.endsWith "?" && !knownQ.contains f)

/-! ## Unified Pure & Async Statement Block Lowering (`lowerBlock`) -/

@[noinline] private partial def lowerCatchFallback? (qctx : PureQuotCtx) (ctx : LowerCtx) (stmts : Array Syntax) : LowerM (Option Term) := do
  let knownQ ← liftM getKnownQLeafNames; let bound := (ctx.locals ++ ctx.stateFields ++ ctx.envVars).foldl (·.insert ·) {}
  let lowerPureNoHoist (eStx : Syntax) : LowerM (Option Term) := do
    if exprHasAwait eStx || exprHasUnwrapWith knownQ bound eStx then return none
    let (t, steps) ← lowerExprCollectingHoists qctx { ctx with allowAwait := false } .val eStx
    return if steps.isEmpty then some t else none
  if stmts.isEmpty then return none
  else if stmts.size == 1 && stmts[0]!.getKind == ``qedStmtExpr then
    let eStx := stmts[0]![0]
    if (matchPushCall? eStx).isSome || (matchRemoveCall? eStx).isSome || (matchSrvEmitStmt? stmts[0]!).isSome then return none
    let some eTerm ← lowerPureNoHoist eStx | return none
    return some (Db.runQuot qctx `(srvAutoField($eTerm)))
  else if stmts[0]!.getKind == ``qedStmtLet && stmts[0]![5].getNumArgs == 0 then
    let st := stmts[0]!
    let some rhsTerm ← lowerPureNoHoist (st.getArg 4) | return none
    let ty? ← lowerOptTypeNode (st.getArg 2)
    let some tailTerm ← lowerCatchFallback? qctx (pushOptLocal ctx (st.getArg 1)) (stmts.extract 1 stmts.size) | return none
    return some (Db.runQuot qctx (mkLetBindTerm (st.getArg 1) ty? (← `(srvRejectUnhandledErr($rhsTerm))) tailTerm))
  else return none

@[noinline] private def lowerMatchScrutineesAndAlts (qctx : PureQuotCtx) (ctx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (lowerArm : LowerCtx → Array Syntax → LowerM Term) : LowerM (Term × Array HoistedStep) := do
  let (scrutTerms, allSteps) ← withCollectedHoists <| (stmt.getArg 1).getSepArgs.mapM (lowerExprQ qctx ctx .val)
  let termCheck := blockAlwaysTerminates ctx.loopMuts?.isSome
  let alts ← (stmt.getArg 3).getArgs.mapM fun c => do
    let altTerms ← runMacro (lowerCasePatAlts (c.getArg 1))
    let pIds := collectCasePatIds (extractCasePatAlts (c.getArg 1)); let cStmts := suiteStmts (c.getArg 3)
    return Db.runQuot qctx (mkMatchAltFromAlts altTerms (← lowerArm (pushPatLocals ctx pIds) (if termCheck cStmts then cStmts else cStmts ++ rest)))
  return (Db.runQuot qctx `(match $[$scrutTerms:term],* with $[$alts:matchAlt]*), allSteps)

private def extractSrvLetCatch? (clausesNode : Syntax) : LowerM (Option Syntax) := do
  let mut catchOpt? : Option Syntax := none
  for cl in clausesNode.getArgs do match cl.getKind with
    | `Qed.Lang.letCatch => do
        if catchOpt?.isSome then throwErrorAt cl "duplicate `catch` clause on `let`"
        catchOpt? := some (cl.getArg 1)
    | `Qed.Lang.letPredictBlock | `Qed.Lang.letPredictExpr | `Qed.Lang.letOnConfirm | `Qed.Lang.letRollback =>
        throwErrorAt cl "`predict`, `on_confirm`, and `rollback` are only supported on client `component` `await` calls, not in `server` functions"
    | _ => pure ()
  return catchOpt?

private def rejectSrvAssignPredict (stmt : Syntax) : LowerM Unit := do
  if stmt.getKind == ``qedStmtAssign && stmt.getNumArgs > 3 && (stmt.getArg 3).getNumArgs > 0 then
    throwErrorAt ((stmt.getArg 3).getArg 0) "`predict` is only supported on client `component` `await` calls, not in `server` functions"

@[noinline] private def lowerBranch (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) (rest thenStmts : Array Syntax) (thenCtx : LowerCtx)
    (elseStmts? : Option (Array Syntax)) (allowPureLetJoin : Bool) (mkBranch : Term → Term → PureQuotM Term)
    (recSame : LowerCtx → Array Syntax → LowerM Term) (recWithState : LowerCtx → Ident → Array Syntax → LowerM Term) : LowerM Term := do
  let termCheck := blockAlwaysTerminates ctx.loopMuts?.isSome
  let (thenRet, elseRet) := (termCheck thenStmts, elseStmts?.any termCheck)
  let mkBr (t e : Term) : Term := Db.runQuot qctx (mkBranch t e)
  let lowerElseOpt := elseStmts?.elim (liftM <| mkEmptyLeaf qctx mode ctx) (recSame ctx)
  if rest.isEmpty then return mkBr (← recSame thenCtx thenStmts) (← lowerElseOpt)
  else if mode.isInf || ctx.loopMuts?.isSome || !ctx.mutLocals.isEmpty then
    return mkBr (← recSame thenCtx (if thenRet then thenStmts else thenStmts ++ rest))
                (← recSame ctx (if elseRet then elseStmts?.getD #[] else (elseStmts?.getD #[]) ++ rest))
  else if thenRet && !elseRet then return mkBr (← recSame thenCtx thenStmts) (← recSame ctx ((elseStmts?.getD #[]) ++ rest))
  else if !thenRet && elseRet then return mkBr (← recSame thenCtx (thenStmts ++ rest)) (← recSame ctx (elseStmts?.getD #[]))
  else
    let br := mkBr (← recSame thenCtx thenStmts) (← lowerElseOpt)
    match mode with
    | .pure .. =>
        let sNext ← freshIdent "_s"
        let baseJoinCtx := { ctx with stateRule := if ctx.stateFields.isEmpty then .statelessServer else .pureStep sNext #[] }
        match ctx.emitAcc? with
        | some _ =>
            let esNext ← freshIdent "_es"; let cont ← recWithState { baseJoinCtx with emitAcc? := some esNext } sNext rest
            return Db.runQuot qctx `(Qed.Server.srvEmitSeq $br (fun $sNext:ident $esNext:ident => $cont))
        | none =>
            let cont ← recWithState baseJoinCtx sNext rest
            if allowPureLetJoin && !blockMayReturnEarly thenStmts && !(elseStmts?.any blockMayReturnEarly) then
              return Db.runQuot qctx `(Qed.Server.srvLetEq (($br : _ × Option Unit).1) (fun $sNext:ident $(← freshIdent "_srvEq"):ident => $cont))
            else return Db.runQuot qctx `(Qed.Server.srvSeq $br (fun $sNext:ident => $cont))
    | .async _ => return Db.runQuot qctx `(Qed.Server.srvSeqM $br (fun _ => $(← recSame ctx rest)))
    | .infallibleAsync => unreachable!

@[noinline] private def lowerReturn (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) (stmt : Syntax) : LowerM Term := do
  if (stmt.getArg 1).getNumArgs == 0 then return Db.runQuot qctx (mkOkLeaf mode ctx (← `(())) (isUnitEmpty := true))
  let retExpr := (stmt.getArg 1).getArg 0; let uRet := unwrapParens1 retExpr
  match mode with
  | .pure .. => if exprHasAwait retExpr && !uRet.isOfKind ``qedUnwrap then throwErrorAt retExpr "`await` cannot be used inside a synchronous or `atomic` block"
  | .infallibleAsync => pure ()
  | .async _ =>
      if uRet.getKind == ``qedAwait && !(unwrapParens1 (uRet.getArg 1)).isOfKind ``qedUnwrap && ctx.hasFallible then
        let (callTerm, steps) ← lowerExprCollectingHoists qctx ctx .val (uRet.getArg 1); let rawId ← freshIdent "_retAw"
        return ← wrapHoists qctx mode ctx steps <| Db.runQuot qctx do
          let errTy ← errTyOf ctx
          let innerRes ← match ctx.innerOptTy? with
            | some innerTy => `(match Qed.Server.SrvRetAwait.liftRet (E := $errTy) $rawId with | Except.ok _v => Except.ok (Qed.Server.SrvLiftOpt.liftOpt (Inner := $innerTy) _v) | Except.error _e => Except.error _e)
            | none => `(Qed.Server.SrvRetAwait.liftRet (E := $errTy) $rawId)
          let wrappedRes ← match ctx.loopMuts? with | none => `(some ($innerRes)) | some lm => wrapLoopStep true lm ``Qed.QedLoopStep.ret (some innerRes)
          `($callTerm >>= fun $rawId:ident => Pure.pure $wrappedRes)
  let isFail := isFailCall retExpr
  if isFail && !ctx.hasFallible then throwErrorAt retExpr s!"`fail(...)` can only be returned from a fallible `T!` function (`{ctx.fnName}` is not declared `-> ...!`)"
  let (term, steps) ← lowerExprCollectingHoists qctx ctx .val retExpr
  wrapHoists qctx mode ctx steps (Db.runQuot qctx <| if isFail then mkErrLeaf mode ctx term else mkOkLeaf mode ctx term)

@[noinline] private def lowerLetCore (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (recBlock : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let xStx := stmt.getArg 1; let ty? ← lowerOptTypeNode (stmt.getArg 2); let rhsRaw := stmt.getArg 4
  if let some catchNode ← extractSrvLetCatch? (stmt.getArg 5) then
    if catchNode.getKind == `Qed.Lang.catchArms then throwErrorAt catchNode "multi-arm `catch: case ...` is for client components; in server/service functions use `catch err:`"
    let rhsStx := unwrapParens1 rhsRaw; let binderStx := catchNode.getArg 0; let catchStmts := suiteStmts (catchNode.getArg 2)
    let errId : Ident := if binderStx.isIdent then ⟨binderStx⟩ else mkIdent `_srvCatchErr
    let catchCtx := pushOptLocal ctx binderStx; let okTerm ← recBlock (pushOptLocal ctx xStx) rest
    let (scrutTerm, steps, awaitCall?) : Term × Array HoistedStep × Option (Term × Ident) ←
      if rhsStx.getKind == ``qedAwait then
        if mode.isPure then throwErrorAt rhsRaw "`await` cannot be used inside a synchronous or `atomic` block"
        let (c, s) ← lowerExprCollectingHoists qctx ctx .val (rhsStx.getArg 1); let r ← freshIdent "_catchAw"; pure (⟨r⟩, s, some (c, r))
      else let (r, s) ← lowerExprCollectingHoists qctx ctx .val rhsStx; pure (r, s, none)
    let mkUnwrap (errBody okPat okBody : Term) : Term :=
      Db.runQuot qctx `(match Qed.Server.SrvUnwrap.unwrap (E := Qed.Server.ApiError) $scrutTerm with | Except.error $errId:ident => $errBody | Except.ok $okPat:term => $okBody)
    let innerTerm ← if let some fbTerm ← lowerCatchFallback? qctx catchCtx catchStmts then
        let okValId ← freshIdent "_catchOk"; bindLet qctx mode xStx ty? (mkUnwrap fbTerm ⟨okValId.raw⟩ ⟨okValId.raw⟩) okTerm
      else
        unless blockAlwaysTerminates ctx.loopMuts?.isSome catchStmts do
          throwErrorAt stmt (if ctx.loopMuts?.isSome then "the `catch` block must end with `return`, `break`, `continue`, or a fallback value expression" else "the `catch` block must either `return` on all paths or end with a fallback value expression")
        let errBody ← recBlock catchCtx catchStmts
        match ty? with
        | some ty => let okValId ← freshIdent "_catchOk"; pure <| mkUnwrap errBody ⟨okValId.raw⟩ (Db.runQuot qctx (mkLetBindTerm xStx (some ty) ⟨okValId.raw⟩ okTerm))
        | none =>
            let okPat ← if xStx.isIdent then pure ⟨xStx⟩ else if xStx.getKind == ``qedLetPatTuple then runMacro (lowerLetBinderPat xStx) else pure ⟨(mkIdent `_srvDiscard).raw⟩
            pure <| mkUnwrap errBody okPat okTerm
    wrapHoists qctx mode ctx steps (match awaitCall? with | some (c, r) => Db.runQuot qctx `($c >>= fun $r:ident => $innerTerm) | none => innerTerm)
  else
    let (rhsTerm, steps) ← lowerExprCollectingHoists qctx ctx .val rhsRaw
    let checkedRhs := if steps.isEmpty then Db.runQuot qctx `(srvRejectUnhandledErr($rhsTerm)) else rhsTerm
    wrapHoists qctx mode ctx steps (← bindLet qctx mode xStx ty? checkedRhs (← recBlock (pushOptLocal ctx xStx) rest))

@[noinline] private def lowerPureMutationStmt (qctx : PureQuotCtx) (mode : BlockMode) (pCtx : LowerCtx) (sCur : Ident) (stmt : Syntax) (rest : Array Syntax)
    (recPure : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  rejectSrvAssignPredict stmt
  let (lvalStx, steps, mkLeaf) : Syntax × Array HoistedStep × (Array LValStep → Term → LowerM Term) ←
    if stmt.getKind == ``qedStmtAssign then
      let opStr := ((stmt.getArg 1).reprint.getD "=").trimAscii.toString
      let (rhsTerm, steps) ← lowerExprCollectingHoists qctx pCtx .val (stmt.getArg 2)
      pure (stmt.getArg 0, steps, fun pathSteps curLeaf => do
        let val ← match opStr with
          | "=" => pure rhsTerm | "+=" => pure <| Db.runQuot qctx `(Qed.Lang.QedVal.val $curLeaf + Qed.Lang.QedVal.val $rhsTerm)
          | "-=" => pure <| Db.runQuot qctx `(Qed.Lang.QedVal.val $curLeaf - Qed.Lang.QedVal.val $rhsTerm)
          | _ => throwErrorAt (stmt.getArg 1) s!"unsupported assignment operator `{opStr}`"
        return if pathSteps.isEmpty then Db.runQuot qctx `(srvAutoField($val)) else val)
    else if let some (targetStx, elemStx) := matchPushCall? (stmt.getArg 0) then
      let (elemTerm, steps) ← lowerExprCollectingHoists qctx pCtx .val elemStx
      pure (targetStx, steps, fun _ curArr => pure <| Db.runQuot qctx `(($curArr).push (srvAutoField($elemTerm))))
    else
      let some (targetStx, keyStx) := matchRemoveCall? (stmt.getArg 0) | unreachable!
      let (keyTerm, steps) ← lowerExprCollectingHoists qctx pCtx .val keyStx
      pure (targetStx, steps, fun _ curDict => pure <| Db.runQuot qctx `(Qed.Dict.remove $curDict $keyTerm))
  let (rootField, pathSteps) ← parseLValPath qctx pCtx lvalStx; let curRoot ← resolveStateFieldBase qctx lvalStx pCtx rootField.getId
  let fNext ← freshIdent s!"_fld_{rootField.getId}_"; let hFNext ← freshIdent "_srvEq"
  let cont ← recPure (setPureOverride pCtx sCur rootField.getId.toString fNext) rest
  let chain ← withUpdatedPathCPS qctx pathSteps 0 curRoot (mkLeaf pathSteps) fun updatedRaw =>
    return Db.runQuot qctx do
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
  let mkLoopAwareRet (retTerm : Term) : PureQuotM Term := wrapLoopRet (.async none) aCtx retTerm (fun _ => unreachable!)
  let baseAtomCtx := { aCtx with loopMuts? := none }
  let (atomCtx, bodyStmts, isFinish, mkOnResult) : LowerCtx × Array Syntax × Bool × (Term → LowerM Term) ←
    if alwaysRet then pure (baseAtomCtx, atomStmts, true, fun res => pure <| Db.runQuot qctx (mkLoopAwareRet res))
    else if !exportedIds.isEmpty then
      let hasEarlyOk := atomStmts.any (stxAny fun s => s.getKind == ``qedStmtReturn && ((s.getArg 1).getNumArgs == 0 || !isFailCall ((s.getArg 1).getArg 0)))
      let expTuple := Db.runQuot qctx (buildTupleVal (exportedIds.map (⟨·.raw⟩)))
      pure (if hasEarlyOk then { baseAtomCtx with wrapReturnSumInl := true } else { baseAtomCtx with innerOptTy? := none },
        atomStmts.push (Syntax.node (.fromRef stmt) `Qed.Server.atomicExport #[expTuple.raw]), true, fun res => do
          let cont ← lowerRest { aCtx with locals := aCtx.locals ++ exportedIds.map (·.getId.eraseMacroScopes.toString) } rest
          return Db.runQuot qctx do
            let errRet ← mkLoopAwareRet (← `(Except.error _e))
            if hasEarlyOk then
              `(match $res:term with | Except.error _e => $errRet | Except.ok (Sum.inl _v) => $(← mkLoopAwareRet (← `(Except.ok _v))) | Except.ok (Sum.inr $expTuple:term) => $cont)
            else `(match $res:term with | Except.error _e => $errRet | Except.ok $expTuple:term => $cont))
    else pure (baseAtomCtx, atomStmts, false, fun early => do
      let cont ← lowerRest aCtx rest
      return Db.runQuot qctx do `(match $early:term with | some _r => $(← mkLoopAwareRet (← `(_r))) | none => $cont))
  let some stateTyTerm := stateTyTerm? | throwErrorAt stmt "`atomic` is only valid in a `server` with `state` declarations"
  if blockHasAwait bodyStmts then throwErrorAt stmt "cannot use `await` inside an `atomic` block; perform external I/O outside `atomic` so shared locks never span network calls"
  let s0Id ← freshIdent "_sAtom"; let hasEmit := blockHasEmit bodyStmts; let es0Id ← freshIdent "_es0"
  let savedMut := (← get).mutated; modify fun s => { s with mutated := #[] }
  let rawAtomBody ← lowerPure (if hasEmit then { atomCtx with emitAcc? := some es0Id } else atomCtx) s0Id s0Id bodyStmts
  let atomMut := (← get).mutated; modify fun s => { s with mutated := savedMut ++ atomMut.filter (!savedMut.contains ·) }
  let readOnly := atomMut.isEmpty
  let committed := Db.runQuot qctx do
    let atomBody ← if hasEmit then `(let $es0Id:ident : List Qed.Server.WsEmit := []; $rawAtomBody) else pure rawAtomBody
    match isFinish, hasEmit, readOnly with
    | true, true, _ => `(Qed.Server.srvFinishEmit $s0Id $atomBody) | false, true, _ => `(Qed.Server.srvAtomicCommitEmit $s0Id $atomBody)
    | true, false, _ => `(Qed.Server.srvFinish $s0Id $atomBody) | false, false, true => pure atomBody | false, false, false => `(Qed.Server.srvAtomicCommit $s0Id $atomBody)
  let bindId ← freshIdent (if hasEmit then "_atomPair" else "_atomRes")
  let onResBody ← mkOnResult (if hasEmit then Db.runQuot qctx `(($bindId).1) else ⟨bindId.raw⟩)
  liftM <| mkAtomicRunTerm s0Id stateTyTerm committed readOnly hasEmit (some (bindId, fun _ => pure onResBody))

@[noinline] private def lowerOptNamedArg (qctx : PureQuotCtx) (ctx : LowerCtx) (named : Array (String × Syntax)) (k : String)
    (defVal : PureQuotM Term) (someTy? : Option (PureQuotM Term) := none) : LowerM Term :=
  match findNamedArg? named k with
  | some s => do let v ← lowerExprQ qctx ctx .val s; return Db.runQuot qctx do match someTy? with | some ty => `(some ($v : $(← ty))) | none => pure v
  | none => return Db.runQuot qctx defVal

@[noinline] private def lowerSideEffectCall (qctx : PureQuotCtx) (ctx : LowerCtx) (stmt : Syntax) (fn : String) (rawArgs : Array Syntax) : LowerM (Name × Term × Array HoistedStep) := do
  if fn == "send" then
    unless ctx.isStreamRoute do throwErrorAt stmt "`send(...)` is only available inside `stream \"/...\":` routes"
    let (argT, steps) ← withCollectedHoists do
      let (pos, named) ← splitCallArgs "send" rawArgs (some ["data", "event", "id", "retry"]) (errRef := stmt)
      let some dataStx := pos[0]? |>.orElse (fun _ => findNamedArg? named "data") | throwErrorAt stmt "`send(data[, event = ..., id = ..., retry = ...])` requires an event data string"
      if pos.size > 1 then throwErrorAt stmt "`send(...)` takes one positional `data` argument; pass `event = ...`, `id = ...`, or `retry = ...` as named arguments"
      let (dT, eT, iT, rT) := (← lowerExprQ qctx ctx .val dataStx,
        ← lowerOptNamedArg qctx ctx named "event" `(none) (some `(String)),
        ← lowerOptNamedArg qctx ctx named "id" `(none) (some `(String)),
        ← lowerOptNamedArg qctx ctx named "retry" `(none) (some `(Nat)))
      return Db.runQuot qctx `({ data := $dT, event := $eT, id := $iT, retry := $rT : Qed.Server.SseEvent })
    return (`Qed.Server.MonadServer.sendSse, argT, steps)
  let isClear := fn == "clearCookie"
  let (argT, steps) ← withCollectedHoists do
    let (pos, named) ← splitCallArgs fn rawArgs (if isClear then none else some ["name", "value", "path", "httpOnly", "secure", "sameSite", "maxAge", "domain"]) (errRef := stmt)
    let some nameStx := pos[0]? |>.orElse (fun _ => findNamedArg? named "name")
      | throwErrorAt stmt (if isClear then "`clearCookie(name[, path = \"/\"])` requires a cookie name" else "`setCookie(name, value, ...)` requires a cookie name")
    if isClear then
      let pathT ← match (findNamedArg? named "path").orElse (fun _ => pos[1]?) with | some s => lowerExprQ qctx ctx .val s | none => pure <| Db.runQuot qctx `("/")
      return Db.runQuot qctx `(Qed.Server.SetCookie.clear $(← lowerExprQ qctx ctx .val nameStx) $pathT)
    else
      let some valStx := pos[1]? |>.orElse (fun _ => findNamedArg? named "value") | throwErrorAt stmt "`setCookie(name, value, ...)` requires a cookie value"
      let (nT, vT) := (← lowerExprQ qctx ctx .val nameStx, ← lowerExprQ qctx ctx .val valStx)
      let pT ← lowerOptNamedArg qctx ctx named "path" `("/"); let hoT ← lowerOptNamedArg qctx ctx named "httpOnly" `(true)
      let ssT ← lowerOptNamedArg qctx ctx named "sameSite" `(Qed.Server.SameSite.lax); let secT ← lowerOptNamedArg qctx ctx named "secure" `(false)
      let maT ← lowerOptNamedArg qctx ctx named "maxAge" `(none) (some `(Nat)); let domT ← lowerOptNamedArg qctx ctx named "domain" `(none) (some `(String))
      return Db.runQuot qctx `({ name := $nT, value := $vT, path := $pT, httpOnly := $hoT, sameSite := ($ssT : Qed.Server.SameSite), secure := $secT, maxAge? := $maT, domain? := $domT : Qed.Server.SetCookie })
  modify fun s => { s with hasCookieOp := true }
  return (`Qed.Server.MonadServer.setCookie, argT, steps)

@[noinline] private def lowerTxStmt (qctx : PureQuotCtx) (aCtx : LowerCtx) (stmt aliasRef : Syntax) (aliasName : String) (txVar? : Option Ident) (txStmts rest : Array Syntax)
    (recAsync : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let some (_, dbInfo) := aCtx.dbs.find? (·.1 == aliasName)
    | throwErrorAt aliasRef s!"unknown database alias `{aliasName}` in `transaction` (declared `use` databases: [{String.intercalate ", " (aCtx.dbs.toList.map Prod.fst)}])"
  if let some (curAlias, _) := aCtx.activeDbTx? then throwErrorAt stmt s!"nested database transactions are not supported (already inside `{curAlias}.transaction:`)"
  let txId ← freshIdent "_dbTxId"
  let (innerCtx, wrapTxVar) ← match txVar? with
    | none => pure ({ aCtx with activeDbTx? := some (aliasName, txId), loopMuts? := none }, fun b => b)
    | some tv =>
        let tvName := tv.getId.eraseMacroScopes.toString
        if aCtx.dbs.any (·.1 == tvName) || aCtx.txDbAliases.any (·.1 == tvName) then throwErrorAt tv s!"transaction variable `{tvName}` collides with an existing database alias"
        let txTagLit := Syntax.mkStrLit dbInfo.dbName.toString
        pure ({ aCtx with activeDbTx? := some (aliasName, txId), txDbAliases := aCtx.txDbAliases.push (tvName, dbInfo, ⟨txId.raw⟩), locals := aCtx.locals.push tvName, loopMuts? := none },
          fun b => Db.runQuot qctx `(let $tv:ident : Qed.Server.Db.DbTx $txTagLit := Qed.Server.Db.DbTx.mk $txId; $b))
  let bodyTerm := wrapTxVar (← recAsync innerCtx txStmts)
  let txRun := Db.runQuot qctx `(Qed.Server.dbRunTx $(mkIdentFrom aliasRef dbInfo.configConst) (fun ($txId:ident : UInt64) => $bodyTerm))
  match aCtx.loopMuts? with
  | some lm =>
      let restTerm ← recAsync aCtx rest
      return Db.runQuot qctx do `($txRun >>= fun | Option.some _txRet => $(← wrapLoopStep false lm ``Qed.QedLoopStep.ret (some (← `(_txRet)))) | Option.none => $restTerm)
  | none => if rest.isEmpty || blockAlwaysReturns txStmts then return txRun else return Db.runQuot qctx `(Qed.Server.srvSeqM $txRun (fun _ => $(← recAsync aCtx rest)))

@[noinline] private def lowerSrvLetMutStmt (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (recBlock : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let lId : Ident := ⟨stmt.getArg 2⟩; let nm := lId.getId.eraseMacroScopes
  if ctx.mutLocals.any (·.getId.eraseMacroScopes == nm) then throwErrorAt lId s!"mutable variable `{nm}` is already declared in this scope; update it with `{nm} = ...`"
  let (rhsTerm, steps) ← lowerExprCollectingHoists qctx ctx .val (stmt.getArg 5)
  let checkedRhs := if steps.isEmpty then Db.runQuot qctx `(srvRejectUnhandledErr($rhsTerm)) else rhsTerm
  let cont ← recBlock { ctx with locals := ctx.locals.push nm.toString, mutLocals := ctx.mutLocals.push lId } rest
  let ty? ← lowerOptTypeNode (stmt.getArg 3)
  let bound := Db.runQuot qctx <| match ty? with | some lTy => `(let $lId:ident : $lTy := $checkedRhs; $cont) | none => `(let $lId:ident := $checkedRhs; $cont)
  wrapHoists qctx mode ctx steps bound

@[noinline] private def lowerSrvLocalMutStmt (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) (stmt : Syntax) (act : LocalMutAction) (rest : Array Syntax)
    (recBlock : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  rejectSrvAssignPredict stmt
  let (rhsTerm, steps) ← lowerExprCollectingHoists qctx ctx .val act.rhsSyntax
  let newVal ← runMacro (applyLocalMutRhs act rhsTerm); let lId := act.targetIdent; let cont ← recBlock ctx rest
  wrapHoists qctx mode ctx steps (Db.runQuot qctx `(let $lId:ident := $newVal; $cont))

@[noinline] private def lowerSrvForFoldCore (qctx : PureQuotCtx) (mode : BlockMode) (ctx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (recBlock : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let binderStx := stmt.getArg 1; let iterStx := stmt.getArg 3; let bodyStmts := suiteStmts (stmt.getArg 5)
  if binderStx.isIdent then
    let bNm := binderStx.getId.eraseMacroScopes
    if ctx.mutLocals.any (·.getId.eraseMacroScopes == bNm) then throwErrorAt binderStx s!"`for` loop variable `{bNm}` shadows mutable variable `{bNm}`; use a different loop variable name"
  let (iterTerm, steps) ← lowerExprCollectingHoists qctx ctx .val iterStx
  let mutated := collectMutatedIds bodyStmts; let usedMuts := ctx.mutLocals.filter fun m => mutated.contains m.getId.eraseMacroScopes
  let (stParam, resSt, resRet, retValId) := (← freshIdent "_srvLoopSt", ← freshIdent "_srvLoopStOut", ← freshIdent "_srvLoopRetOut", ← freshIdent "_srvLoopRet")
  let bodyInner ← recBlock { pushOptLocal ctx binderStx with loopMuts? := some usedMuts } bodyStmts
  let restTerm ← recBlock ctx rest; let isRange := isRangeCallExpr iterStx
  let fullTerm := Db.runQuot qctx do
    let initSt ← mkMutPack usedMuts.toList; let bodyWithUnpack ← wrapMutUnpack stParam usedMuts.toList bodyInner
    let lam ← if binderStx.isIdent then `(fun $stParam:ident $(⟨binderStx⟩):ident => $bodyWithUnpack) else `(fun $stParam:ident _ => $bodyWithUnpack)
    let someArm ← wrapLoopRet mode ctx ⟨retValId.raw⟩ fun v => do match mode with | .pure _ _ _ m => mkPureLeaf ctx m (← `(Option.some $v)) | _ => pure v
    let afterLoop ← wrapMutUnpack resSt usedMuts.toList (← `(match $resRet:ident with | Option.some $retValId:ident => $someArm | Option.none => $restTerm))
    if mode.isPure then
      `(let ($resSt:ident, $resRet:ident) := $(← if isRange then `(Qed.qedForRange $iterTerm $initSt $lam) else `(Qed.qedForFold $iterTerm $initSt $lam)); $afterLoop)
    else
      `($(← if isRange then `(Qed.Server.srvForRangeM $iterTerm $initSt $lam) else `(Qed.Server.srvForFoldM (Qed.QedIterable.toList $iterTerm) $initSt $lam)) >>= fun ($resSt:ident, $resRet:ident) => $afterLoop)
  wrapHoists qctx mode ctx steps fullTerm

@[noinline] private def lowerEmitStmt (qctx : PureQuotCtx) (mode : BlockMode) (bCtx : LowerCtx) (stmt : Syntax) (chId : Ident) (rawArgs rest : Array Syntax)
    (recSame : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let (emitTerm, steps) ← lowerEmitCall qctx bCtx stmt chId rawArgs
  let body ← match mode with
    | .pure .. =>
        let some esId := bCtx.emitAcc? | throwErrorAt stmt "internal error: `emit` accumulator not initialized"
        let esNext ← freshIdent "_es"; let cont ← recSame { bCtx with emitAcc? := some esNext } rest
        pure <| Db.runQuot qctx `(let $esNext:ident : List Qed.Server.WsEmit := $esId ++ [$emitTerm]; $cont)
    | .async _ =>
        let evId ← freshIdent "_wsEv"; let cont ← recSame bCtx rest
        pure <| Db.runQuot qctx `(let $evId:ident := $emitTerm; Qed.Server.MonadServer.wsBroadcast ($evId).topic ($evId).payload >>= fun _ => $cont)
    | .infallibleAsync => unreachable!
  wrapHoists qctx mode bCtx steps body

@[noinline] private def lowerLetElseStmt (qctx : PureQuotCtx) (mode : BlockMode) (bCtx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (recSame : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let patStx := stmt.getArg 1; let patTerm ← runMacro (lowerQedPat patStx)
  let (scrutTerm, steps) ← lowerExprCollectingHoists qctx bCtx .val (stmt.getArg 3); let elseStmts := extractLetElseStmts stmt
  unless blockAlwaysTerminates bCtx.loopMuts?.isSome elseStmts do
    throwErrorAt stmt (if bCtx.loopMuts?.isSome then "guard `let ... = ... else` branch must `return`, `break`, or `continue` on all paths" else "guard `let ... = ... else` branch must `return` on all paths")
  let hMatch ← freshIdent "_srvM"
  let thenTerm ← recSame (pushPatLocals bCtx (collectQedPatIds patStx)) rest; let elseTerm ← recSame bCtx elseStmts
  wrapHoists qctx mode bCtx steps (Db.runQuot qctx `(match $hMatch:ident : $scrutTerm:term with | $patTerm => $thenTerm | _ => $elseTerm))

@[noinline] private def lowerIfOrIfLetStmt (qctx : PureQuotCtx) (mode : BlockMode) (bCtx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (recSame : LowerCtx → Array Syntax → LowerM Term) (recWithState : LowerCtx → Ident → Array Syntax → LowerM Term) : LowerM Term := do
  if stmt.getKind == ``qedStmtIf then
    let (condTerm, steps) ← lowerExprCollectingHoists qctx bCtx .propGuard (stmt.getArg 1); let hGuard ← freshIdent "_srvG"
    wrapHoists qctx mode bCtx steps (← lowerBranch qctx mode bCtx rest (suiteStmts (stmt.getArg 3)) bCtx (desugarElifs (stmt.getArg 4).getArgs (stmt.getArg 5)) mode.isPure
      (fun t e => `(if $hGuard:ident : $condTerm then $t else $e)) recSame recWithState)
  else
    let patStx := stmt.getArg 2; let patTerm ← runMacro (lowerQedPat patStx)
    let (scrutTerm, steps) ← lowerExprCollectingHoists qctx bCtx .val (stmt.getArg 4); let hMatch ← freshIdent "_srvM"
    wrapHoists qctx mode bCtx steps (← lowerBranch qctx mode bCtx rest (suiteStmts (stmt.getArg 6)) (pushPatLocals bCtx (collectQedPatIds patStx))
      (extractElseSuite (stmt.getArg 7)) false (fun t e => `(match $hMatch:ident : $scrutTerm:term with | $patTerm => $t | _ => $e)) recSame recWithState)

@[noinline] private def lowerExprStmt (qctx : PureQuotCtx) (mode : BlockMode) (bCtx : LowerCtx) (stmt : Syntax) (rest : Array Syntax)
    (recSame : LowerCtx → Array Syntax → LowerM Term) : LowerM Term := do
  let eStx := stmt.getArg 0; let (eTerm, steps) ← lowerExprCollectingHoists qctx bCtx .val eStx
  let valTerm := if !mode.isInf && isBareUnwrapExpr (!mode.isPure) (← liftM getKnownQLeafNames) bCtx eStx then eTerm else Db.runQuot qctx `(srvEnsureUnit($eTerm))
  wrapHoists qctx mode bCtx steps (← bindLet qctx mode Syntax.missing none valTerm (← recSame bCtx rest))

private def matchStateMutTarget? (stmt : Syntax) : Option Syntax :=
  if stmt.getKind == ``qedStmtAssign then some (stmt.getArg 0)
  else if stmt.getKind == ``qedStmtExpr then ((matchPushCall? (stmt.getArg 0)).orElse fun _ => matchRemoveCall? (stmt.getArg 0)).map Prod.fst
  else none

@[noinline] private partial def lowerBlockGo (qctx : PureQuotCtx) (kind : BlockKind) (ctx : LowerCtx) (stmts : Array Syntax) : LowerM Term := do
  let curOverrides := getPureOverrides ctx
  let mode : BlockMode := match kind with
    | .pure inAtomic s₀ sCur => .pure inAtomic s₀ sCur (Db.runQuot qctx (materializeState sCur curOverrides))
    | .async stateTyTerm? => .async stateTyTerm? | .infallibleAsync => .infallibleAsync
  let (isPure, isInf) := (mode.isPure, mode.isInf)
  if stmts.isEmpty then return ← liftM <| mkEmptyLeaf qctx mode ctx
  let stmt := stmts[0]!; let rest := stmts.extract 1 stmts.size; let k := stmt.getKind
  let bCtx := if isInf then ctx else { ctx with stateRule := if ctx.stateFields.isEmpty then .statelessServer else match kind with | .pure _ _ sCur => .pureStep sCur curOverrides | _ => .forbidAsyncOutsideAtomic, allowAwait := !isPure }
  let recSame := fun c st => lowerBlockGo qctx kind c st
  let recWithState := fun c s st => lowerBlockGo qctx (match kind with | .pure inAtomic s₀ _ => .pure inAtomic s₀ s | other => other) c st
  if k == ``qedStmtPass then recSame bCtx rest
  else if k == ``qedStmtBreak then
    let some lm := bCtx.loopMuts? | throwErrorAt stmt "`break` can only be used inside a `for` loop"
    return Db.runQuot qctx (wrapLoopStep isPure lm ``Qed.QedLoopStep.breakLoop)
  else if k == ``qedStmtContinue then
    let some _ := bCtx.loopMuts? | throwErrorAt stmt "`continue` can only be used inside a `for` loop"
    liftM <| mkEmptyLeaf qctx mode bCtx
  else if k == ``qedStmtLetMut then lowerSrvLetMutStmt qctx mode bCtx stmt rest recSame
  else if let some act := tryMatchLocalMut? bCtx.mutLocals stmt then lowerSrvLocalMutStmt qctx mode bCtx stmt act rest recSame
  else if let some (chId, rawArgs) := if !isInf then matchSrvEmitStmt? stmt else none then lowerEmitStmt qctx mode bCtx stmt chId rawArgs rest recSame
  else if k == `Qed.Server.atomicExport && isPure then
    let expTerm : Term := ⟨stmt.getArg 0⟩
    let .pure _ _ _ matCur := mode | unreachable!
    return Db.runQuot qctx do
      let wrapped ← if bCtx.wrapReturnSumInl then `(Except.ok (Sum.inr $expTerm)) else `(Except.ok $expTerm)
      mkPureLeaf bCtx matCur (← `(some $wrapped))
  else if let some (fn, rawArgs) := if !isInf then (matchNamedStmtCall? stmt).filter fun (n, _) => n == "setCookie" || n == "clearCookie" || n == "send" else none then
    if isPure then throwErrorAt stmt (if fn == "send" then "cannot call `send(...)` inside an `atomic:` block; emit SSE events outside `atomic:`" else "cannot call `setCookie`/`clearCookie` inside an `atomic:` block; emit cookies outside `atomic:`")
    let (effNm, argT, steps) ← lowerSideEffectCall qctx bCtx stmt fn rawArgs; let cont ← recSame bCtx rest
    wrapHoists qctx mode bCtx steps (Db.runQuot qctx `($(mkIdent effNm) $argT >>= fun _ => $cont))
  else if let some (aliasRef, aliasName, txVar?, txStmts) := if !isInf then matchTxStmt? stmt else none then
    if isPure then throwErrorAt stmt "cannot start a database `transaction` inside an `atomic:` block; run database transactions outside `atomic:`"
    lowerTxStmt qctx bCtx stmt aliasRef aliasName txVar? txStmts rest recSame
  else if !isInf && k == ``qedStmtAtomic then
    match kind with
    | .pure inAtomic .. =>
      if inAtomic then throwErrorAt stmt "nested `atomic` blocks are forbidden"
      else if ctx.stateFields.isEmpty then throwErrorAt stmt "`atomic` is only valid in a `server` with `state` declarations"
      else throwErrorAt stmt s!"redundant `atomic` block: `{ctx.fnName}` has no `await` calls, so it already executes atomically"
    | .async stateTyTerm? => lowerAtomicStmt qctx bCtx stateTyTerm? stmt rest (fun c s0 s st => lowerBlockGo qctx (.pure true s0 s) c st) recSame
    | .infallibleAsync => unreachable!
  else if k == ``qedStmtReturn then lowerReturn qctx mode bCtx stmt
  else if k == ``qedStmtLet then lowerLetCore qctx mode bCtx stmt rest recSame
  else if k == ``qedStmtLetElse then lowerLetElseStmt qctx mode bCtx stmt rest recSame
  else if let some targetStx := if !isInf then matchStateMutTarget? stmt else none then
    match kind with
    | .pure _ _ sCur =>
      if bCtx.loopMuts?.isSome then throwErrorAt stmt "cannot mutate server `state` field inside a synchronous `for` loop; mutate a `let mut` local or wrap server mutations in `atomic:`"
      lowerPureMutationStmt qctx mode bCtx sCur stmt rest recSame
    | _ =>
      rejectSrvAssignPredict stmt; let _ ← parseLValPath qctx bCtx targetStx
      throwErrorAt stmt s!"cannot mutate server state outside an `atomic:` block in `{ctx.fnName}` because `{ctx.fnName}` uses `await`"
  else if k == ``qedStmtExpr then lowerExprStmt qctx mode bCtx stmt rest recSame
  else if k == ``qedStmtIf || k == ``qedStmtIfLet then lowerIfOrIfLetStmt qctx mode bCtx stmt rest recSame recWithState
  else if k == ``qedStmtMatch then
    let (matchT, allSteps) ← lowerMatchScrutineesAndAlts qctx bCtx stmt rest recSame; wrapHoists qctx mode bCtx allSteps matchT
  else if k == ``qedStmtFor then lowerSrvForFoldCore qctx mode bCtx stmt rest recSame
  else
    let sn := stxSnippet stmt
    throwErrorAt stmt s!"unsupported statement{if sn.isEmpty then s!"({k})" else s!" `{sn}`"} in {if isPure then "server" else if isInf then "infallible async" else "async server"} function `{ctx.fnName}`"

private def lowerBlock (kind : BlockKind) (ctx : LowerCtx) (stmts : Array Syntax) : LowerM Term := do
  lowerBlockGo (← liftM Db.getPureQuotCtx) kind ctx stmts

def lowerPureBlock (ctx : LowerCtx) (inAtomic : Bool) (s₀ sCur : Ident) (stmts : Array Syntax) : LowerM Term := lowerBlock (.pure inAtomic s₀ sCur) ctx stmts
def lowerAsyncBlock (ctx : LowerCtx) (stateTyTerm? : Option Term) (stmts : Array Syntax) : LowerM Term := lowerBlock (.async stateTyTerm?) ctx stmts
def lowerInfallibleAsyncBlock (ctx : LowerCtx) (stmts : Array Syntax) : LowerM Term := lowerBlock .infallibleAsync ctx stmts

end BlockLowering
end Qed.Server
