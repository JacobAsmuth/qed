import Qed.Server.Lower
import Qed.Schema.Codec
import Qed.Schema.Registry

namespace Qed.Server
open Qed.Lang

/-! ## `server` Command Elaborator: Context & Shared Builders (`SrvElabCtx` / `SrvElabM`) -/

structure ParsedEnvDecl where
  ident    : Lean.Ident
  osKey    : String
  default? : Option String := none
  isSecret : Bool := false

abbrev ParsedStateDecl := Lean.Ident × Lean.Term × Option Lean.Syntax × Option Lean.Term
abbrev ParsedMutInv    := Lean.Ident × Lean.Syntax × String
abbrev ParsedInv       := Lean.Syntax × Bool × String

structure ParsedServerBlock where
  dbDecls                : Array (Lean.Ident × DatabaseInfo) := #[]
  serviceDecls           : Array (Lean.Ident × ServiceInfo) := #[]
  authDecl?              : Option (Lean.Ident × AuthInfo) := none
  envDecls               : Array ParsedEnvDecl := #[]
  stateDecls             : Array ParsedStateDecl := #[]
  mutInvs                : Array ParsedMutInv := #[]
  invs                   : Array ParsedInv := #[]
  routesAuthInvs         : Array (Lean.Ident × String × Array String) := #[]
  rpcsAuthInvs           : Array (Lean.Ident × Array String) := #[]
  noSecretsInvs          : Array Lean.Ident := #[]
  helperClauses          : Array Lean.Syntax := #[]
  beforeClause?          : Option Lean.Syntax := none
  fnClauses              : Array Lean.Syntax := #[]
  chanClauses            : Array Lean.Syntax := #[]
  httpClauses            : Array Lean.Syntax := #[]
  jobClauses             : Array Lean.Syntax := #[]
  onCreateAccountClause? : Option Lean.Syntax := none
  onSignInClause?        : Option Lean.Syntax := none
  exampleClauses         : Array Lean.Syntax := #[]

structure SrvElabCtx where
  priorRep          : Nat
  priorUnrep        : Nat
  srvIdent          : Lean.Ident
  srvName           : Lean.Name
  fullSrvName       : Lean.Name
  hasState          : Bool
  dbDecls           : Array (Lean.Ident × DatabaseInfo)
  serviceDecls      : Array (Lean.Ident × ServiceInfo) := #[]
  authDecl?         : Option (Lean.Ident × AuthInfo)
  envDecls          : Array ParsedEnvDecl
  stateFieldNames   : Array String
  envVarNames       : Array String
  invs              : Array ParsedInv
  mutInvs           : Array ParsedMutInv
  chanSigs          : Array SrvChanSig := #[]
  helpers           : Array SrvHelperSig := #[]
  statefulHelperIds : Array Lean.Ident := #[]
  deferredProofs    : IO.Ref (Array (Lean.Elab.Command.CommandElabM Bool))
  extRootsRef       : IO.Ref (Array Lean.Name)

abbrev SrvElabM := ReaderT SrvElabCtx Lean.Elab.Command.CommandElabM

structure ParsedFnParams where
  idents         : Array Lean.Ident := #[]
  tyTerms        : Array Lean.Term := #[]
  defBinders     : Array (Lean.TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
  names          : Array String := #[]
  minParamCount  : Nat := 0
  hasExplicitCtx : Bool := false
  defaultExprs   : Array Lean.Syntax := #[]
  txParams       : Array (Lean.Ident × DatabaseInfo) := #[]

structure LoweredAuthBind where
  binderId   : Lean.Ident
  binderName : String
  extraIds   : Array Lean.Ident
  extraTys   : Array Lean.Term
  authInfo?  : Option AuthInfo

structure LoweredRequires where
  authBind?       : Option LoweredAuthBind := none
  reqPropTerms    : Array Lean.Term
  reqHypIds       : Array Lean.Ident
  reqLabels       : Array String
  requiresAuth    : Bool
  clientReqId?    : Option Lean.Ident
  clientReqConst? : Option Lean.Name
  clientReqLabel  : String

structure FnEnsSpec where
  ensId    : Lean.Ident
  postFn   : Lean.Term → PureQuotM Lean.Term
  labelStr : String
  tac?     : Option (Lean.TSyntax ``Lean.Parser.Tactic.tacticSeq) := none

structure ElabHandlerRes where
  runExpr      : Lean.Term
  targetId     : Lean.Ident
  isAsync      : Bool
  allBinderIds : Array Lean.Ident
  allBinderTys : Array Lean.Term
  mutatesState : Bool
  dbWrite      : Bool
  hasEmit      : Bool
  hasCookieOp  : Bool := false

private def singleInvLabelStr (invs : Array ParsedInv) : String :=
  let ss := ((invs.filter (!·.2.1)).toList.map (·.2.2)).eraseDups
  if ss.isEmpty then "StateInv" else String.intercalate ", " ss

section SrvHelpers
open Lean Elab Command

def SrvElabCtx.subId (c : SrvElabCtx) (s : Name) (ref : Ident := c.srvIdent) : Ident := mkIdentFrom ref (c.srvName ++ s)
def SrvElabCtx.fnSubId (c : SrvElabCtx) (id : Ident) (suf : String) : Ident := mkIdentFrom id (c.srvName ++ id.getId.appendAfter suf)
def SrvElabCtx.stateId (c : SrvElabCtx) : Ident := c.subId `State
def SrvElabCtx.stateInvId (c : SrvElabCtx) : Ident := c.subId `StateInv
def SrvElabCtx.ctxId (_ : SrvElabCtx) : Ident := mkIdent `ctx
def SrvElabCtx.envIdents (c : SrvElabCtx) : Array Ident := c.envDecls.map (·.ident)
def SrvElabCtx.envBinderTysPure (c : SrvElabCtx) : PureQuotM (Array Term) := mapPQ c.envDecls fun e => if e.isSecret then `(Qed.Secret) else `(String)
def SrvElabCtx.atomicBindersPure (c : SrvElabCtx) : PureQuotM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  if c.hasState then pure #[← `(bracketedBinder| [Qed.Server.MonadAtomic $(c.stateId) m])] else pure #[]

@[noinline] def srvErrAt {α : Type} (ref : Syntax) (msg : String) : SrvElabM α := liftM <| errAt ref msg
@[noinline] def runSrvPQ {α : Type} (k : PureQuotM α) : SrvElabM α := liftM <| runPQ k
@[noinline] def liftSrvMacro {α : Type} (m : MacroM α) : SrvElabM α := liftM <| liftMacroCmd m
@[noinline] def foldlSrv {α β : Type} (xs : Array α) (init : β) (f : β → α → SrvElabM β) : SrvElabM β :=
  let rec go : Nat → β → SrvElabM β | 0, acc => pure acc | r + 1, acc => do let i := xs.size - (r + 1); if h : i < xs.size then go r (← f acc xs[i]) else pure acc
  go xs.size init
@[noinline] def mapSrv {α β : Type} (xs : Array α) (f : α → SrvElabM β) : SrvElabM (Array β) := foldlSrv xs (Array.mkEmpty xs.size) fun acc x => return acc.push (← f x)
@[noinline] def foldOptSrv {α β : Type} (xs : Array α) (init : β) (f : β → α → SrvElabM (Option β)) : SrvElabM (Option β) :=
  let rec go : Nat → β → SrvElabM (Option β)
    | 0, acc => pure (some acc)
    | r + 1, acc => do let i := xs.size - (r + 1); if h : i < xs.size then match ← f acc xs[i] with | some acc' => go r acc' | none => return none else return some acc
  go xs.size init
@[noinline] def elabSrvCmd (cmd : TSyntax `command) : SrvElabM Unit := liftM <| elabCommand cmd
@[noinline] def elabSrvCmds (cmds : Array (TSyntax `command)) : SrvElabM Unit := liftM <| foldlCmd cmds () fun _ c => elabCommand c
@[noinline] def elabSrvPure (k : PureQuotM (TSyntax `command)) : SrvElabM Unit := liftM <| elabPureCmd k
@[noinline] def elabSrvPureCmds (k : PureQuotM (Array (TSyntax `command))) : SrvElabM Unit := liftM <| elabPureCmds k

def filterNewWarnings (arr : PersistentArray Message) (priorSize : Nat) : PersistentArray Message :=
  let lst := arr.toList
  ((lst.take priorSize) ++ (lst.drop priorSize).filter (·.severity != .warning)).foldl (·.push ·) {}
def hasNewErrors (log : MessageLog) (priorRep priorUnrep : Nat) : Bool :=
  (log.reported.toList.drop priorRep).any (·.severity == .error) || (log.unreported.toList.drop priorUnrep).any (·.severity == .error)
def hasSrvErrors : SrvElabM Bool := do let c ← read; return hasNewErrors (← get).messages c.priorRep c.priorUnrep
def recordSrvExtRoots (roots : Array Name) : SrvElabM Unit := do (← read).extRootsRef.modify fun acc => roots.foldl pushUnique acc
def deferSrvProof (act : CommandElabM Bool) : SrvElabM Unit := do (← read).deferredProofs.modify (·.push act)
@[noinline] def deferSrvCmd (cmd : TSyntax `command) : SrvElabM Unit := do
  let c ← read; deferSrvProof do elabCommand cmd; return !hasNewErrors (← get).messages c.priorRep c.priorUnrep
@[noinline] def deferSrvPure (k : PureQuotM (TSyntax `command)) : SrvElabM Unit := do deferSrvCmd (← runSrvPQ k)

def mkBaseLowerCtx (fnName : String) (locals : Array String) (allowAwait allowUnwrap hasFallible : Bool)
    (innerOptTy? : Option Term := none) (domainErrTy? : Option Term := none) (isHttpRoute := false) (isStreamRoute := false)
    (includeDbs := true) (ctxTerm? : Option Term := none) (txParams : Array (Ident × DatabaseInfo) := #[]) : SrvElabM LowerCtx := do
  let c ← read
  let txDbAliases ← if txParams.isEmpty then pure #[] else runSrvPQ <| mapPQ txParams fun (pid, dbi) => do return (pid.getId.eraseMacroScopes.toString, dbi, ← `(($pid).id))
  return { fnName, stateFields := c.stateFieldNames, envVars := c.envVarNames, envIdents := c.envIdents, locals,
           stateRule := if c.hasState then .pureStep (mkIdent `_s0) else .statelessServer, allowAwait, allowUnwrap, hasFallible,
           innerOptTy?, domainErrTy?, channels := c.chanSigs, helpers := c.helpers,
           dbs := if includeDbs then c.dbDecls.map fun (a, i) => (a.getId.toString, i) else #[],
           services := c.serviceDecls.map fun (a, i) => (a.getId.toString, i), ctxTerm?, txDbAliases, isHttpRoute, isStreamRoute }

@[noinline] def mkProtoDecodeBindPure (bytesVar tupleVar : Ident) (tupleTy : Term) (pIdents : Array Ident) (projs : Array Term) (body : Term) : PureQuotM Term := do
  let bound ← foldrPQ (pIdents.zip projs) body fun (pid, prj) acc => `(let $pid:ident := $prj; $acc)
  `(match Qed.Proto.decode (α := $tupleTy) $bytesVar with
    | Except.error _decErr => Pure.pure (Except.error (Qed.Server.ApiError.badRequest _decErr))
    | Except.ok $tupleVar:ident => $bound)

def checkSrvParamName (ctxLabel : String) (pid : Ident) (reserved seen extraShadow : Array String := #[]) (allowExplicitCtx := false) : SrvElabM String := do
  let c ← read; let pstr := pid.getId.toString
  if pstr == "ctx" && !allowExplicitCtx then srvErrAt pid s!"`ctx` is already implicitly available as `RequestCtx` in {ctxLabel}"
  if reserved.contains pstr then srvErrAt pid s!"`{pstr}` is reserved inside {ctxLabel}; rename this parameter"
  if seen.contains pstr then srvErrAt pid s!"duplicate parameter `{pstr}` in {ctxLabel}"
  if extraShadow.contains pstr then srvErrAt pid s!"parameter `{pstr}` shadows an existing binding in {ctxLabel}; rename the parameter"
  if c.envVarNames.contains pstr then srvErrAt pid s!"parameter `{pstr}` in {ctxLabel} shadows `env`/`secret` binding `{pstr}`; rename the parameter"
  if c.stateFieldNames.contains pstr then srvErrAt pid s!"parameter `{pstr}` in {ctxLabel} shadows server `state` field `{pstr}`; rename the parameter"
  return pstr

@[noinline] private def mkFnParamBinderPure (pid : Ident) (baseTy : Term) (txDbName? : Option String) (defT? : Option Term) :
    PureQuotM (Term × TSyntax `Lean.Parser.Term.bracketedBinder) := do
  let tyTerm ← match txDbName? with | some dn => `(Qed.Server.Db.DbTx $(Syntax.mkStrLit dn)) | none => pure baseTy
  return (tyTerm, ← match defT? with | some dt => `(bracketedBinder| ($pid:ident : $tyTerm := srvAutoField($dt))) | none => `(bracketedBinder| ($pid:ident : $tyTerm)))

@[noinline] private def parseOneFnParam (ctxLabel tyDescPrefix : String) (reserved extraShadow : Array String) (allowDefaults allowExplicitCtx : Bool)
    (acc : ParsedFnParams × Bool) (rp : Syntax) : SrvElabM (ParsedFnParams × Bool) := do
  let (pp, seenDefault) := acc; let c ← read; let pid : Ident := ⟨rp.getArg 0⟩
  let pstr ← checkSrvParamName ctxLabel pid reserved pp.names extraShadow allowExplicitCtx
  let optDef := rp.getArg 3
  if !allowDefaults && optDef.getNumArgs == 2 then srvErrAt optDef s!"default parameter values are only supported on `fn` declarations, not in {ctxLabel}"
  let pty ← liftSrvMacro (lowerSrvType (rp.getArg 2) false s!"{tyDescPrefix} `{pstr}`")
  if !allowDefaults then
    return ({ pp with idents := pp.idents.push pid, tyTerms := pp.tyTerms.push pty.term, names := pp.names.push pstr, minParamCount := pp.minParamCount + 1 }, false)
  let txDb? ← if pty.mods.isEmpty && !pty.isProto && !pty.isForm then
      match pty.baseName with
      | .str pre "Tx" => match (c.dbDecls.find? (·.1.getId.eraseMacroScopes == pre)).map Prod.snd with
          | some d => pure (some d) | none => pure (lookupDatabase? (← getEnv) (← getCurrNamespace) (← getOpenDecls) pre)
      | _ => pure none
    else pure none
  let (seenDef', minPC, defExprs, defT?) ← if optDef.getNumArgs == 2 then
      let dExpr := optDef.getArg 1
      let (defT, dSt) ← liftM <| (lowerExpr { fnName := ctxLabel, envVars := c.envVarNames, locals := pp.names, stateRule := .statelessServer } .val dExpr).run {}
      recordSrvExtRoots dSt.extRoots; pure (true, pp.minParamCount, pp.defaultExprs.push dExpr, some defT)
    else
      if seenDefault then srvErrAt pid s!"non-default parameter `{pstr}` cannot follow a parameter with a default value in {ctxLabel}"
      pure (false, pp.minParamCount + 1, pp.defaultExprs, none)
  let (tyTerm, binder) ← runSrvPQ (mkFnParamBinderPure pid pty.term (txDb?.map (·.dbName.toString)) defT?)
  return ({ idents := pp.idents.push pid, tyTerms := pp.tyTerms.push tyTerm, defBinders := pp.defBinders.push binder,
            names := pp.names.push pstr, minParamCount := minPC, hasExplicitCtx := pp.hasExplicitCtx || pstr == "ctx",
            defaultExprs := defExprs, txParams := txDb?.elim pp.txParams (pp.txParams.push ⟨pid, ·⟩) }, seenDef')

@[noinline] def parseSrvFnParams (ctxLabel tyDescPrefix : String) (rawParams : Array Syntax)
    (reserved extraShadow : Array String := #[]) (allowExplicitCtx := false) : SrvElabM ParsedFnParams := do
  return (← foldlSrv rawParams ({}, false) (parseOneFnParam ctxLabel tyDescPrefix reserved extraShadow true allowExplicitCtx)).1

@[noinline] def parseSrvParams (ctxLabel tyDescPrefix : String) (rawParams : Array Syntax) (reserved extraShadow : Array String := #[]) :
    SrvElabM (Array Ident × Array Term × Array String) := do
  let pp := (← foldlSrv rawParams ({}, false) (parseOneFnParam ctxLabel tyDescPrefix reserved extraShadow false false)).1
  return (pp.idents, pp.tyTerms, pp.names)

def lowerSrvExpr (ctx : LowerCtx) (mode : ExprMode) (stx : Syntax) : SrvElabM Term := return (← liftM <| (lowerExpr ctx mode stx).run {}).1

@[noinline] def elabServerStateCmds (stateDecls : Array ParsedStateDecl) : SrvElabM Bool := do
  let c ← read; let (stFieldIds, stFieldTys) := (stateDecls.map (·.1), stateDecls.map (·.2.1))
  let stInitRaw ← mapSrv stateDecls fun (_, _, initStx?, defT?) =>
    match initStx?, defT? with | some stx, _ => lowerSrvExpr { fnName := "initState" } .val stx | none, some dt => pure dt | none, none => unreachable!
  let (initId, invInitId) := (c.subId `initState, c.subId `inv_init)
  elabSrvPureCmds do
    let stInitVals ← mapPQ stInitRaw fun t => `(srvAutoField($t))
    return #[← `(command| structure $(c.stateId) where $[$stFieldIds:ident : $stFieldTys:term]*),
             ← `(command| @[noinline] def $initId : $(c.stateId) := { $[$stFieldIds:ident := $stInitVals:term],* })]
  if (← hasSrvErrors) then return false
  let sParam := mkIdent `_s
  let invTerms ← mapSrv (c.invs.filter (!·.2.1)) fun (e, _, _) =>
    lowerSrvExpr { fnName := "invariant", stateFields := c.stateFieldNames, envVars := c.envVarNames, stateRule := .invariantProp sParam (mkIdent `_sOld) false } .propInv e
  elabSrvPureCmds do
    let invBody ← Qed.mkConjBody invTerms (ascribeProp := false)
    return #[← `(command| def $(c.stateInvId) ($sParam:ident : $(c.stateId)) : Prop := $invBody),
             ← `(command| theorem $invInitId : $(c.stateInvId) $initId := by qedSrvProveStep [$(c.stateInvId), $initId] "initState" $(Syntax.mkStrLit ("init: " ++ singleInvLabelStr c.invs)))]
  return !(← hasSrvErrors)

partial def unwrapDocClause (c : Syntax) : Option (TSyntax ``Lean.Parser.Command.docComment) × Syntax :=
  if c.getKind == ``srvDocClause then let (inner?, body) := unwrapDocClause (c.getArg 1); (inner?.orElse fun _ => some ⟨c.getArg 0⟩, body) else (none, c)

private def parseExceptList (optStx : Syntax) : Array String :=
  if optStx.getNumArgs == 4 then (optStx.getArg 2).getSepArgs.map fun s => (⟨s⟩ : TSyntax `str).getString else #[]

private def checkUniqueDecl (b : ParsedServerBlock) (blockKind : String) (srvName : Name) (id : Ident) : CommandElabM Unit := do
  let nm := id.getId
  if b.dbDecls.any (·.1.getId == nm) || b.serviceDecls.any (·.1.getId == nm) || b.authDecl?.any (·.1.getId == nm) ||
     b.envDecls.any (·.ident.getId == nm) || b.stateDecls.any (·.1.getId == nm) then
    errAt id s!"duplicate declaration `{nm}` in `{blockKind} {srvName}`"

private def checkUniqueInv (seen : Array Name) (blockKind : String) (srvName : Name) (nameId : Ident) : CommandElabM (Array Name) := do
  if seen.contains nameId.getId then errAt nameId s!"duplicate invariant `{nameId.getId}` in `{blockKind} {srvName}`"
  return seen.push nameId.getId

@[noinline] private def parseUseClause (srvName : Name) (isService : Bool) (b : ParsedServerBlock) (c : Syntax) : CommandElabM ParsedServerBlock := do
  let aliasRaw := c.getArg 1; let aliasId : Ident := if aliasRaw.isIdent then ⟨aliasRaw⟩ else mkIdentFrom aliasRaw `auth
  let refId : Ident := ⟨c.getArg 3⟩; checkUniqueDecl b (if isService then "service" else "server") srvName aliasId
  let (env, currNs, openDecls) := (← getEnv, ← getCurrNamespace, ← getOpenDecls)
  if let some dbInfo := Qed.Server.lookupDatabase? env currNs openDecls refId.getId then return { b with dbDecls := b.dbDecls.push (aliasId, dbInfo) }
  if let some svcInfo := Qed.Server.lookupService? env currNs openDecls refId.getId then return { b with serviceDecls := b.serviceDecls.push (aliasId, svcInfo) }
  if !isService then if let some authInfo := Qed.Server.lookupAuth? env currNs openDecls refId.getId then
    if b.authDecl?.isSome then errAt refId s!"`server {srvName}` can declare at most one `use ... : <auth>` provider"
    return { b with authDecl? := some (aliasId, authInfo) }
  if (Qed.Diag.lookupNameMapExt? Qed.Server.failedServiceRegistry env currNs openDecls refId.getId).isSome then
    errAt refId s!"referenced `service {refId.getId}` failed to elaborate earlier"
  errAt refId (if isService then s!"unknown `database` or `service` `{refId.getId}` in `use {aliasId.getId} : {refId.getId}` (`service` blocks cannot bind `auth` directly; pass `ctx` or user values instead)"
    else s!"unknown `database`, `service`, or `auth` `{refId.getId}` in `use {aliasId.getId} : {refId.getId}`")

@[noinline] private def parseServerOnlyClause (srvName : Name) (b : ParsedServerBlock) (seenInv : Array Name) (rawC c : Syntax) : CommandElabM (ParsedServerBlock × Array Name) := do
  match c.getKind with
  | ``srvInvRoutesAuthClause => let id : Ident := ⟨c.getArg 1⟩; return ({ b with routesAuthInvs := b.routesAuthInvs.push (id, (⟨c.getArg 4⟩ : TSyntax `str).getString, parseExceptList (c.getArg 5)) }, ← checkUniqueInv seenInv "server" srvName id)
  | ``srvInvRpcsAuthClause => let id : Ident := ⟨c.getArg 1⟩; return ({ b with rpcsAuthInvs := b.rpcsAuthInvs.push (id, parseExceptList (c.getArg 4)) }, ← checkUniqueInv seenInv "server" srvName id)
  | ``srvStateClause =>
      let id : Ident := ⟨c.getArg 1⟩; let ty ← liftMacroCmd (lowerSrvType (c.getArg 3) false s!"state field `{id.getId}`"); checkUniqueDecl b "server" srvName id
      let (initStx?, defT?) ← if (c.getArg 4).getNumArgs == 2 then pure (some ((c.getArg 4).getArg 1), none)
        else match ← liftMacroCmd (inferQedTypeDefault? (c.getArg 3)) with | some dt => pure (none, some dt) | none => errAt id s!"state field `{id.getId}` requires an initial value `= ...`"
      return ({ b with stateDecls := b.stateDecls.push (id, ty.term, initStx?, defT?) }, seenInv)
  | ``srvInvMutatingClause => let id : Ident := ⟨c.getArg 1⟩; return ({ b with mutInvs := b.mutInvs.push (⟨c.getArg 4⟩, c.getArg 6, s!"mutating:{id.getId}") }, ← checkUniqueInv seenInv "server" srvName id)
  | ``srvInvClause => let id : Ident := ⟨c.getArg 1⟩; return ({ b with invs := b.invs ++ (c.getArg 3).getSepArgs.map fun e => (e, exprCallsOld e, id.getId.toString) }, ← checkUniqueInv seenInv "server" srvName id)
  | ``srvBeforeClause => if b.beforeClause?.isSome then errAt c s!"duplicate `before` middleware in `server {srvName}`" else return ({ b with beforeClause? := some c }, seenInv)
  | ``srvFnClause => return ({ b with fnClauses := b.fnClauses.push rawC }, seenInv)
  | ``srvChannelClause => return ({ b with chanClauses := b.chanClauses.push c }, seenInv)
  | ``srvHttpRouteClause | ``srvStreamClause => return ({ b with httpClauses := b.httpClauses.push c }, seenInv)
  | ``srvJobClause => return ({ b with jobClauses := b.jobClauses.push c }, seenInv)
  | ``srvOnCreateAccountClause => if b.onCreateAccountClause?.isSome then errAt c s!"duplicate `onCreateAccount` hook in `server {srvName}`" else return ({ b with onCreateAccountClause? := some c }, seenInv)
  | ``srvOnSignInClause => if b.onSignInClause?.isSome then errAt c s!"duplicate `onSignIn` hook in `server {srvName}`" else return ({ b with onSignInClause? := some c }, seenInv)
  | _ => errAt c "unexpected clause in `server` block"

@[noinline] private def parseOneServerClause (srvName : Name) (isService : Bool) (acc : ParsedServerBlock × Array Name) (rawC : Syntax) : CommandElabM (ParsedServerBlock × Array Name) := do
  let (b, seenInv) := acc; let blockKind := if isService then "service" else "server"
  let (_, c) := unwrapDocClause rawC
  match c.getKind with
  | ``srvDbClause => return (← parseUseClause srvName isService b c, seenInv)
  | ``srvEnvClause | ``srvSecretClause =>
      let isSecret := c.getKind == ``srvSecretClause; let id : Ident := ⟨c.getArg 1⟩; let osKey := (⟨c.getArg 3⟩ : TSyntax `str).getString
      if isSecret then unless isValidEnvVarName osKey do errAt (c.getArg 3) s!"invalid secret environment variable name `{osKey}`: must be non-empty and contain only ASCII letters, digits, or `_`"
      checkUniqueDecl b blockKind srvName id
      let def? := if !isSecret && (c.getArg 4).getNumArgs == 2 then some (⟨(c.getArg 4).getArg 1⟩ : TSyntax `str).getString else none
      return ({ b with envDecls := b.envDecls.push { ident := id, osKey, default? := def?, isSecret } }, seenInv)
  | ``srvHelperFnClause => return ({ b with helperClauses := b.helperClauses.push rawC }, seenInv)
  | ``srvInvNoSecretsClause =>
      let id : Ident := ⟨c.getArg 1⟩; return ({ b with noSecretsInvs := b.noSecretsInvs.push id }, ← checkUniqueInv seenInv blockKind srvName id)
  | ``srvExampleClause => return ({ b with exampleClauses := b.exampleClauses.push rawC }, seenInv)
  | _ =>
      if isService then errAt c s!"only `use`, `env`, `secret`, `fn`, `example`, and `invariant ... : no_required_secrets` declarations are allowed in stateless `service {srvName}`"
      parseServerOnlyClause srvName b seenInv rawC c

@[noinline] def parseServerClauses (srvIdent : Ident) (srvName : Name) (clauses : Array Syntax) (isService : Bool := false) : CommandElabM ParsedServerBlock := do
  let (b, _) ← foldlCmd clauses ({}, #[]) (parseOneServerClause srvName isService)
  if isService then
    if b.helperClauses.isEmpty then errAt srvIdent s!"`service {srvName}` must declare at least one `fn`"
    return b
  if let some c := b.onCreateAccountClause? then if b.authDecl?.isNone then errAt c s!"`onCreateAccount` in `server {srvName}` requires `use auth : <Auth>`"
  if let some c := b.onSignInClause? then if b.authDecl?.isNone then errAt c s!"`onSignIn` in `server {srvName}` requires `use auth : <Auth>`"
  if b.fnClauses.isEmpty && b.chanClauses.isEmpty && b.httpClauses.isEmpty && b.jobClauses.isEmpty && b.onCreateAccountClause?.isNone && b.onSignInClause?.isNone then
    errAt srvIdent s!"`server {srvName}` must declare at least one `rpc`, `channel`, `http`, `stream`, `every` job, or auth hook"
  if b.stateDecls.isEmpty && (!b.invs.isEmpty || !b.mutInvs.isEmpty) then errAt srvIdent s!"`server {srvName}` declares `invariant`s but has no `state` fields"
  if let some (fldId, _, _) := b.mutInvs.find? fun (f, _, _) => !b.stateDecls.any (·.1.getId == f.getId) then
    errAt fldId s!"`invariant mutating {fldId.getId}` does not match any `state` field of `{srvName}` (`state` fields: {String.intercalate ", " (b.stateDecls.toList.map fun s => s!"`{s.1.getId}`")})"
  return b

partial def scanCtxEnv (envVars locals : Array String) (stx : Syntax) : Bool × Bool :=
  match stx.getKind with
  | ``qedIdent => match (stx.getArg 0).getId.components with
      | root :: _ => let r := root.toString; if locals.contains r then (false, false) else (r == "ctx", envVars.contains r) | [] => (false, false)
  | ``qedProj => scanCtxEnv envVars locals (stx.getArg 0)
  | ``qedLam1 => scanCtxEnv envVars (locals ++ if (stx.getArg 0).isIdent then #[(stx.getArg 0).getId.toString] else #[]) (stx.getArg 2)
  | ``qedLamN => scanCtxEnv envVars (locals ++ (stx.getArg 1).getSepArgs.filterMap fun b => if b.isIdent then some b.getId.toString else none) (stx.getArg 4)
  | ``qedAllIn | ``qedAnyIn =>
      let (c1, e1) := scanCtxEnv envVars locals (stx.getArg 3); let (c2, e2) := scanCtxEnv envVars (locals.push (stx.getArg 1).getId.toString) (stx.getArg 5); (c1 || c2, e1 || e2)
  | ``qedAllVars => scanCtxEnv envVars (locals ++ (stx.getArg 1).getSepArgs.map fun b => (qedAllVarIdent b).getId.toString) (stx.getArg 3)
  | _ => stx.getArgs.foldl (fun (ac, ae) ch => let (c, e) := scanCtxEnv envVars locals ch; (ac || c, ae || e)) (false, false)

def isAuthReqLabel (s : String) : Bool := s.contains "ctx.userId" || s.contains "ctx.isAuthenticated" || s.contains "ctx.bearerToken"

@[noinline] def wrapReqsPure (reqProps : Array Term) (reqHIds : Array Ident) (reqLbls : Array String) (inner : Term) (pureWrap : Bool := true) : PureQuotM Term :=
  foldrPQ (reqProps.zip (reqHIds.zip reqLbls)) inner fun (prop, hid, rLbl) g => do
    let rMsg := Syntax.mkStrLit s!"precondition failed: {rLbl}"
    let errCtor : Term ←
      if isAuthReqLabel rLbl then `(Qed.Server.ApiError.unauthorized $rMsg)
      else if rLbl.contains "ctx.hasClaim" || rLbl.contains "ctx.claim" || rLbl.contains "ctx.isSession" || rLbl.contains "ctx.authMethod" || rLbl.contains "emailVerified" then `(Qed.Server.ApiError.forbidden $rMsg)
      else `(Qed.Server.ApiError.badRequest $rMsg)
    let errTerm ← if pureWrap then `(Pure.pure (Except.error $errCtor)) else `(Except.error $errCtor)
    `(if $hid:ident : $prop then $g else $errTerm)

def LoweredRequires.allBinderIds (r : LoweredRequires) : Array Ident := (r.authBind?.map (·.extraIds) |>.getD #[]) ++ r.reqHypIds
def LoweredRequires.allBinderTys (r : LoweredRequires) : Array Term := (r.authBind?.map (·.extraTys) |>.getD #[]) ++ r.reqPropTerms
def LoweredRequires.allBinderArgs (r : LoweredRequires) : Array Term := r.allBinderIds.map (⟨·.raw⟩)
def LoweredRequires.extraLocals (r : LoweredRequires) : Array String := r.authBind?.map (fun ab => #[ab.binderName]) |>.getD #[]

@[noinline] def wrapAuthAndReqsPure (reqs : LoweredRequires) (inner : Term) (pureWrap : Bool := true) : PureQuotM Term := do
  let body ← wrapReqsPure reqs.reqPropTerms reqs.reqHypIds reqs.reqLabels inner pureWrap
  let some ab := reqs.authBind? | return body
  let ctxId := mkIdent `ctx
  let errTerm (msg : String) : PureQuotM Term := do let e ← `(Qed.Server.ApiError.unauthorized $(Syntax.mkStrLit msg)); if pureWrap then `(Pure.pure (Except.error $e)) else `(Except.error $e)
  let (unauthErr, badLenErr, uId, hEq, hNe, hLen) := (← errTerm "authentication required", ← errTerm "invalid user id length", ab.binderId, ab.extraIds[1]!, ab.extraIds[2]!, ab.extraIds[3]!)
  let uidExpr : Term ← if ab.authInfo?.isSome then `(($uId).id) else pure ⟨uId.raw⟩
  let lenGuarded ← `(if $hLen:ident : 1 ≤ ($uidExpr).length ∧ ($uidExpr).length ≤ 128 then $body else $badLenErr)
  match ab.authInfo? with
  | some authInfo =>
      let hFrom := mkIdent `_hFromCtx
      `(match $hFrom:ident : $(mkIdentFrom uId (authInfo.authName ++ `fromCtx)) $ctxId with
        | Option.none => $unauthErr
        | Option.some $uId:ident =>
            have $hEq:ident : Option.some (($uId).id) = ($ctxId).userId := $(mkIdentFrom uId (authInfo.authName ++ `fromCtx_userId)) $ctxId $uId $hFrom
            have $hNe:ident : ($ctxId).userId ≠ Option.none := (by intro _hN; rw [_hN] at $hEq:ident; cases $hEq:ident)
            $lenGuarded)
  | none =>
      let hUid := mkIdent `_hUidCtx
      `(match $hUid:ident : ($ctxId).userId with
        | Option.none => $unauthErr
        | Option.some $uId:ident => have $hEq:ident : Option.some $uId = ($ctxId).userId := ($hUid).symm; have $hNe:ident : ($ctxId).userId ≠ Option.none := (by rw [$hUid:ident]; simp); $lenGuarded)

private def matchAuthRequireExpr? (stx : Syntax) (hasAuthDecl : Bool) : CommandElabM (Option Ident) := do
  let u := unwrapParens1 stx
  if u.getKind == ``qedIdent && (u.getArg 0).getId.eraseMacroScopes == `auth then return some (mkIdentFrom u (if hasAuthDecl then `user else `uid))
  if u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId.eraseMacroScopes == `auth then
    let args := (u.getArg 2).getSepArgs
    if args.size == 1 && args[0]!.getKind == ``qedCallArgPos then
      let a := unwrapParens1 (args[0]!.getArg 0)
      if a.getKind == ``qedIdent && (a.getArg 0).getId.eraseMacroScopes.isAtomic then return some ⟨a.getArg 0⟩
    errAt stx "`requires auth(...)` expects a single identifier binder (e.g. `requires auth(user)`)"
  return none

@[noinline] private def mkAuthExtraTysPure (ctxId uId : Ident) (authInfo? : Option AuthInfo) : PureQuotM (Array Term) := do
  let (uTy, uidExpr) : Term × Term ← match authInfo? with | some ai => pure (← `($(mkIdentFrom uId (ai.authName ++ `User))), ← `(($uId).id)) | none => pure (← `(String), ⟨uId.raw⟩)
  return #[uTy, ← `(Option.some $uidExpr = ($ctxId).userId), ← `(($ctxId).userId ≠ Option.none), ← `(1 ≤ ($uidExpr).length ∧ ($uidExpr).length ≤ 128)]

private abbrev ReqFoldAcc := Array Term × Array Ident × Array String × Array Term × Array String × Bool

@[noinline] private def lowerOneReqExpr (fnLabel hypPrefix : String) (serverLocals clientLocals excludedClientVars : Array String)
    (authBind? : Option LoweredAuthBind) (trackAuth : Bool) (acc : ReqFoldAcc) (rExprIdx : Syntax × Nat) : SrvElabM ReqFoldAcc := do
  let ((rExpr, idx), (props, hIds, labels, cliProps, cliLabels, reqAuth)) := (rExprIdx, acc); let c ← read
  if exprHasAwait rExpr then srvErrAt rExpr "`requires` precondition cannot contain `await`"
  let (pTerm, rSt) ← liftM <| (lowerExpr { fnName := fnLabel, stateFields := c.stateFieldNames, envVars := c.envVarNames, envIdents := c.envIdents, locals := serverLocals, stateRule := .forbidInRequires } .propGuard rExpr).run {}
  recordSrvExtRoots rSt.extRoots
  let acc0 : ReqFoldAcc := (props.push pTerm, hIds.push (mkIdent (Name.mkSimple s!"{hypPrefix}{idx}")), labels.push ((rExpr.reprint.getD "requires").trimAscii.toString), cliProps, cliLabels, reqAuth)
  foldlSrv (splitAndStx rExpr) acc0 fun (ps, hs, ls, cps, cls, ra) conj => do
    let (mCtx, mEnv) := scanCtxEnv c.envVarNames serverLocals conj
    let mAuth := authBind?.any fun ab => (scanCtxEnv #[ab.binderName] clientLocals conj).2
    let rep := conj.reprint.getD ""
    if trackAuth && (mCtx || mAuth) && !mEnv && (isAuthReqLabel rep || rep.contains "ctx.isSession") then return (ps, hs, ls, cps, cls, true)
    if !mCtx && !mEnv && !mAuth && (excludedClientVars.isEmpty || !(scanCtxEnv excludedClientVars clientLocals conj).2) then
      let cp ← lowerSrvExpr { fnName := fnLabel, stateFields := c.stateFieldNames, locals := clientLocals, stateRule := .forbidInRequires, forbidCtxEnv := true } .propInv conj
      return (ps, hs, ls, cps.push cp, cls.push (if rep.isEmpty then "requires" else rep.trimAscii.toString), ra)
    return (ps, hs, ls, cps, cls, ra)

@[noinline] def elabRequiresClauses (refIdent : Ident) (itemName : Name) (fnLabel hypPrefix reqSuffix : String)
    (serverLocals clientLocals : Array String) (clientBindIds : Array Ident) (clientBindTys : Array Term)
    (reqExprs : Array Syntax) (excludedClientVars : Array String := #[]) (trackAuth : Bool := true) : SrvElabM LoweredRequires := do
  let c ← read
  let (authBind?, filteredReqs) ← foldlSrv reqExprs (none, #[]) fun (ab?, fs) rExpr => do
    if let some uId ← liftM <| matchAuthRequireExpr? rExpr c.authDecl?.isSome then
      if ab?.isSome then srvErrAt rExpr s!"duplicate `requires auth` in `{fnLabel}`"
      let uStr ← checkSrvParamName s!"`requires auth` in `{fnLabel}`" uId (extraShadow := serverLocals)
      let extraIds := #[uId, mkIdent (Name.mkSimple s!"{hypPrefix}_authEq"), mkIdent (Name.mkSimple s!"{hypPrefix}_authNe"), mkIdent (Name.mkSimple s!"{hypPrefix}_authLen")]
      let ai? := c.authDecl?.map Prod.snd
      return (some { binderId := uId, binderName := uStr, extraIds, extraTys := ← runSrvPQ (mkAuthExtraTysPure c.ctxId uId ai?), authInfo? := ai? }, fs)
    return (ab?, fs.push rExpr)
  let sLocs := authBind?.elim serverLocals (serverLocals.push ·.binderName)
  let exVars := authBind?.elim excludedClientVars (excludedClientVars.push ·.binderName)
  let (props, hIds, labels, cliProps, cliLabels, reqAuth) ←
    foldlSrv filteredReqs.zipIdx (#[], #[], #[], #[], #[], authBind?.isSome) (lowerOneReqExpr fnLabel hypPrefix sLocs clientLocals exVars authBind? trackAuth)
  let (clientReqId?, clientReqConst?) ← if cliProps.isEmpty then pure (none, none) else do
    let leaf := itemName.appendAfter reqSuffix; let cid := c.subId leaf refIdent
    elabSrvPure do noUnusedVarsPure (← `(command| @[simp] abbrev $cid $[($clientBindIds:ident : $clientBindTys:term)]* : Prop := $(← Qed.mkConjBody cliProps (ascribeProp := false))))
    pure (some cid, some (c.fullSrvName ++ leaf))
  return { authBind?, reqPropTerms := props, reqHypIds := hIds, reqLabels := labels, requiresAuth := reqAuth,
           clientReqId?, clientReqConst?, clientReqLabel := String.intercalate " && " cliLabels.toList }

@[noinline] def elabEnsuresAbbrev (ownerIdent : Ident) (fnLabel : String) (binderName : Name)
    (paramNames : Array String) (pIdents : Array Ident) (pTyTerms : Array Term) (resTyTerm : Term) (ensExprs : Array Syntax) :
    SrvElabM (Option (Option (Ident × Name × String))) := do
  if ensExprs.isEmpty then return some none
  let c ← read
  let ensCtx : LowerCtx := { fnName := fnLabel, stateFields := c.stateFieldNames, envVars := c.envVarNames, locals := paramNames.push binderName.toString, stateRule := .forbidInEnsures, forbidCtxEnv := true }
  let ensProps ← mapSrv ensExprs fun e => do
    if exprHasAwait e then srvErrAt e "`ensures` postcondition cannot contain `await`"
    lowerSrvExpr ensCtx .propInv e
  let leaf := ownerIdent.getId.appendAfter "_ens"; let ensId := c.subId leaf ownerIdent
  elabSrvPure do noUnusedVarsPure (← `(command| @[simp] abbrev $ensId $[($pIdents:ident : $pTyTerms:term)]* ($(mkIdent binderName):ident : $resTyTerm) : Prop := $(← Qed.mkConjBody ensProps (ascribeProp := false))))
  if (← hasSrvErrors) then return none
  return some (some (ensId, c.fullSrvName ++ leaf, String.intercalate " && " (ensExprs.toList.map fun e => (e.reprint.getD "ensures").trimAscii.toString)))

private partial def scanFailCallsAux (stx : Syntax) (tags : Array Ident) (hasPlain : Bool) : Array Ident × Bool :=
  if stx.getKind == ``qedCall && (stx.getArg 0).getKind == ``qedIdent && ((stx.getArg 0).getArg 0).getId == `fail then
    let rawArgs := (stx.getArg 2).getSepArgs
    if (rawArgs.size == 1 || rawArgs.size == 2) && (unwrapParens1 rawArgs[0]![0]).getKind == ``qedDotIdent then
      let tagId : Ident := ⟨(unwrapParens1 rawArgs[0]![0])[1]⟩
      let tags' := if tags.any (·.getId == tagId.getId) then tags else tags.push tagId
      if rawArgs.size == 2 then scanFailCallsAux rawArgs[1]! tags' hasPlain else (tags', hasPlain)
    else rawArgs.foldl (init := (tags, true)) fun (t, p) a => scanFailCallsAux a t p
  else stx.getArgs.foldl (init := (tags, hasPlain)) fun (t, p) ch => scanFailCallsAux ch t p

def scanBodyFailTags (stmts : Array Syntax) : Array Ident × Bool := stmts.foldl (init := (#[], false)) fun (t, p) st => scanFailCallsAux st t p

@[noinline] def elabDomainErrorType (fnIdent : Ident) (tagIdents : Array Ident) : SrvElabM Ident := do
  let c ← read; let errTypeId := c.subId (fnIdent.getId ++ `Error) fnIdent
  elabSrvPure do
    let ctors ← mapPQ tagIdents fun tid => `(Lean.Parser.Command.ctor| | $tid:ident)
    `(command| inductive $errTypeId where $[$ctors:ctor]* deriving Inhabited, DecidableEq, Repr)
  elabSrvPureCmds (Qed.mkUnitEnumCodecCmdsPure errTypeId (tagIdents.map fun tid => (tid.getId, tid.getId.toString)))
  return errTypeId

private abbrev SecExtAcc := Array String × Array String × Array (String × String) × Array Name × Array (String × String × Option String)

private def mergeSvcIntoAcc (acc : SecExtAcc) (si : ServiceInfo) : SecExtAcc :=
  let (rS, oS, ex, dbs, envs) := acc
  (si.secrets.foldl pushUnique rS, si.ownSecrets.foldl pushUnique oS,
   si.externalServices.foldl (fun a x => if a.any (·.1 == x.1) then a else a.push x) ex,
   si.databases.foldl pushUnique dbs, si.envVars.foldl (fun a x => if a.any (·.2.1 == x.2.1) then a else a.push x) envs)

@[noinline] def collectServerSecretsAndExts : SrvElabM SecExtAcc := do
  let c ← read; let (env, currNs, openDecls) := (← getEnv, ← getCurrNamespace, ← getOpenDecls)
  let mut acc : SecExtAcc := (#[], #[], #[], c.dbDecls.map (·.2.configConst), c.envDecls.map fun e => (e.ident.getId.toString, e.osKey, e.default?))
  acc := c.dbDecls.foldl (init := acc) fun (r, o, ex, d, en) (_, dbi) =>
    let es := dbi.envSpecs; if !dbi.hasDevFallback && es.prod == es.staging && es.prod == es.preview then (dbi.secrets.foldl pushUnique r, o, ex, d, en) else (r, o, ex, d, en)
  acc := c.envDecls.foldl (init := acc) fun (r, o, ex, d, en) e => if e.default?.isNone then (pushUnique r e.osKey, pushUnique o e.osKey, ex, d, en) else (r, o, ex, d, en)
  if let some (_, ai) := c.authDecl? then if !ai.spec.isManaged then acc := (ai.secrets.foldl pushUnique acc.1, acc.2)
  acc := c.serviceDecls.foldl (init := acc) fun a (_, si) => mergeSvcIntoAcc a si
  return (← c.extRootsRef.get).foldl (init := acc) fun a root =>
    if let some ei := Qed.Diag.lookupNameMapExt? externalRegistry env currNs openDecls root then
      let sStr := root.toString; let (r, o, ex, d, en) := a
      (ei.secrets.foldl pushUnique r, ei.secrets.foldl pushUnique o, if ex.any (·.1 == sStr) then ex else ex.push (sStr, ei.baseOrigin), d, en)
    else if let some si := lookupService? env currNs openDecls root then mergeSvcIntoAcc a si else a

@[noinline] private def wrapOneEnvDeclPure (e : ParsedEnvDecl) (acc : Term × Option Term) : PureQuotM (Term × Option Term) := do
  let (accRun, accPf?) := acc; let (eid, keyLit, useBeta) := (e.ident, Syntax.mkStrLit e.osKey, accPf?.isSome)
  let bindVal (ty rhs body : Term) : PureQuotM Term := if useBeta then `((fun ($eid:ident : $ty) => $body) $rhs) else `(let $eid:ident : $ty := $rhs; $body)
  let errP (msg : String) : PureQuotM Term := `(Pure.pure (Except.error (Qed.Server.ApiError.internal $(Syntax.mkStrLit msg))))
  let optPf (mk : Term → PureQuotM Term) : PureQuotM (Option Term) := match accPf? with | some pf => some <$> mk pf | none => pure none
  let (runBody, pfBody?) ← if e.isSecret then
      let errT ← errP s!"missing required secret `{e.osKey}`"
      let okRun ← bindVal (← `(Qed.Secret)) (← `(Qed.Secret.ofString _secRaw)) accRun
      pure (← `(match _envOpt with | some _secRaw => if _secRaw.isEmpty then $errT else $okRun | none => $errT),
            ← optPf fun pf => `(match _envOpt with | some _secRaw => if _secRaw.isEmpty then Qed.Server.ProgSpec.pure_class _ trivial else (fun ($eid:ident : Qed.Secret) => $pf) (Qed.Secret.ofString _secRaw) | none => Qed.Server.ProgSpec.pure_class _ trivial))
    else match e.default? with
      | some defVal =>
          let dLit := Syntax.mkStrLit defVal
          pure (← bindVal (← `(String)) (← `(_envOpt.getD $dLit)) accRun, ← optPf fun pf => `((fun ($eid:ident : String) => $pf) (_envOpt.getD $dLit)))
      | none =>
          let errT ← errP s!"missing required environment variable `{e.osKey}`"
          pure (← `(match _envOpt with | some $eid:ident => $accRun | none => $errT),
                ← optPf fun pf => `(match _envOpt with | some $eid:ident => $pf | none => Qed.Server.ProgSpec.pure_class _ trivial))
  return (← `(Qed.Server.MonadServer.readEnv $keyLit >>= fun _envOpt => $runBody),
          ← match pfBody? with | some pb => some <$> `(Qed.Server.ProgSpec.safeIO_bind (Qed.Server.MonadServer.readEnv $keyLit) fun _envOpt => $pb) | none => pure none)

@[noinline] def wrapWithEnvDeclsPure (envDecls : Array ParsedEnvDecl) (innerRun : Term) (innerProof? : Option Term := none) : PureQuotM (Term × Option Term) :=
  foldrPQ envDecls (innerRun, innerProof?) wrapOneEnvDeclPure

@[noinline] private def mkDispatchDefPure (c : SrvElabCtx) (defLeaf : Name) (atomicBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (paramIds : Array Ident) (paramTys : Array Term) (retTy bodyTerm : Term) : PureQuotM (TSyntax `command) := do
  noUnusedVarsPure (← `(command| def $(c.subId defLeaf) {m : Type → Type} [Monad m] [Qed.Server.MonadServer m] $[$atomicBinders:bracketedBinder]* ($(c.ctxId):ident : Qed.Server.RequestCtx) $[($paramIds:ident : $paramTys:term)]* :
    m (Except Qed.Server.ApiError $retTy) := $((← wrapWithEnvDeclsPure c.envDecls bodyTerm).1)))

@[noinline] private def mkAuthHookDispatchPure (c : SrvElabCtx) (atomicBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (authInfo : AuthInfo) (onCreateRun? onSignInRun? : Option Term) : PureQuotM (TSyntax `command) := do
  let (hkVar, uVar, hFC, hA, hAE, okU) := (mkIdent `hookKind, mkIdent `_authUser, mkIdent `_hFromCtx, mkIdent `_hAuth, mkIdent `_hAuthEq, ← `(Pure.pure (Except.ok ())))
  mkDispatchDefPure c `authHookM atomicBinders #[hkVar] #[← `(UInt8)] (← `(Unit)) (← `(
    match $hFC:ident : $(mkIdentFrom c.srvIdent (authInfo.authName ++ `fromCtx)) $(c.ctxId) with
    | Option.none => Pure.pure (Except.error (Qed.Server.ApiError.unauthorized "missing authenticated user"))
    | Option.some $uVar:ident =>
        have $hAE:ident : Option.some (($uVar).id) = ($(c.ctxId)).userId := $(mkIdentFrom c.srvIdent (authInfo.authName ++ `fromCtx_userId)) $(c.ctxId) $uVar $hFC
        have $hA:ident : ($(c.ctxId)).userId ≠ Option.none := by intro _hNone; rw [_hNone] at $hAE:ident; cases $hAE:ident
        match $hkVar:ident with | (0 : UInt8) => $(onCreateRun?.getD okU) | (1 : UInt8) => $(onSignInRun?.getD okU) | _ => $okU))

@[noinline] private def mkServerDispatchCmdsPure (c : SrvElabCtx) (methodInfos : Array ServerMethodInfo) (reqSecrets : Array String)
    (dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr)) (chanNames : Array String)
    (wsDispatchArms wsProjectArms httpDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (onCreateRun? onSignInRun? : Option Term) : PureQuotM (Array (TSyntax `command)) := do
  let mkLits (ss : Array String) : Array Term := ss.map (Syntax.mkStrLit ·)
  let mut cmds : Array (TSyntax `command) := #[]
  if c.hasState then cmds := cmds.push (← `(command|
    theorem $(c.subId `concurrent_linearizable) {Out : Type} (st : Qed.Server.MultiCoreState $(c.stateId) Out) (hsched : Qed.Server.MultiCoreSchedule $(c.stateInvId) ⟨$(c.subId `initState), []⟩ st) :
        $(c.stateInvId) st.shared := Qed.Server.concurrent_schedule_preserves_inv $(c.stateInvId) $(c.subId `initState) st $(c.subId `inv_init) hsched))
  let atomicBs ← c.atomicBindersPure; let (strTy, bytesTy, u8Ty) := (← `(String), ← `(ByteArray), ← `(UInt8))
  let (mVar, wsKVar, wsCVar, wsPVar, wsPayVar, hMVar, hPVar) := (mkIdent `method, mkIdent `wsKind, mkIdent `wsChannel, mkIdent `wsParams, mkIdent `wsPayload, mkIdent `httpMethod, mkIdent `httpPath)
  cmds := cmds ++ #[
    ← mkStrArrDefPure (c.subId `secrets) reqSecrets, ← mkMarkerThmPure (c.subId `_qed_server_marker),
    ← mkStrArrDefPure (c.subId `readOnlyMethods) ((methodInfos.filter (·.isReadOnly)).map (·.name)),
    ← `(command| @[noinline] def $(c.subId `methods) : List String := [$(mkLits (methodInfos.map (·.name))),*]),
    ← `(command| @[noinline] def $(c.subId `channels) : List String := [$(mkLits chanNames),*]),
    ← mkDispatchDefPure c `dispatchM atomicBs #[mVar, mkIdent `reqBytes] #[strTy, bytesTy] bytesTy
      (← `(match $mVar:ident with $[$(dispatchArms.push (← `(Lean.Parser.Term.matchAltExpr| | _ => Pure.pure (Except.error (Qed.Server.ApiError.notFound ("unknown RPC method: " ++ $mVar)))))):matchAlt]*))]
  if !chanNames.isEmpty then cmds := cmds.push (← mkDispatchDefPure c `wsDispatchM atomicBs #[wsKVar, wsCVar, wsPVar, wsPayVar] #[u8Ty, strTy, bytesTy, bytesTy] bytesTy
    (← `(match $wsKVar:ident, $wsCVar:ident with $[$(wsDispatchArms.push (← `(Lean.Parser.Term.matchAltExpr| | _, _ => Pure.pure (Except.error (Qed.Server.ApiError.notFound ("unknown WebSocket channel: " ++ $wsCVar)))))):matchAlt]*)))
  if !wsProjectArms.isEmpty then cmds := cmds.push (← noUnusedVarsPure (← `(command|
    @[noinline] def $(c.subId `wsProject) ($(c.ctxId):ident : Qed.Server.RequestCtx) ($wsCVar:ident : String) ($wsPVar:ident : ByteArray) ($wsPayVar:ident : ByteArray) : Qed.Server.WsProjectOut :=
      match $wsCVar:ident with $[$(wsProjectArms.push (← `(Lean.Parser.Term.matchAltExpr| | _ => Qed.Server.WsProjectOut.passthrough))):matchAlt]*)))
  if !httpDispatchArms.isEmpty then cmds := cmds.push (← mkDispatchDefPure c `httpDispatchM atomicBs #[hMVar, hPVar] #[strTy, strTy] (← `(Option Qed.Server.HttpResponse))
    (← `(match $hMVar:ident, $hPVar:ident with $[$(httpDispatchArms.push (← `(Lean.Parser.Term.matchAltExpr| | _, _ => Pure.pure (Except.ok none)))):matchAlt]*)))
  if let some (_, ai) := c.authDecl? then if onCreateRun?.isSome || onSignInRun?.isSome then
    cmds := cmds.push (← mkAuthHookDispatchPure c atomicBs ai onCreateRun? onSignInRun?)
  return cmds

@[noinline] def elabServerDispatchCmds (methodInfos : Array ServerMethodInfo) (dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (chanNames : Array String) (wsDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (wsProjectArms httpDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]) (jobNames : Array String := #[])
    (onCreateRun? onSignInRun? : Option Term := none) : SrvElabM Unit := do
  let c ← read; let (reqSecrets, ownSecrets, usedExts, allDbs, allEnvs) ← collectServerSecretsAndExts
  elabSrvPureCmds (mkServerDispatchCmdsPure c methodInfos reqSecrets dispatchArms chanNames wsDispatchArms wsProjectArms httpDispatchArms onCreateRun? onSignInRun?)
  modifyEnv fun env => serverRegistry.addEntry env {
    serverName := c.fullSrvName, shortName := c.srvName.toString, hasState := c.hasState, secrets := reqSecrets, ownSecrets,
    envVars := allEnvs, externalServices := usedExts, methods := methodInfos, channels := chanNames, jobs := jobNames, databases := allDbs,
    authName? := c.authDecl?.map (·.2.authName), authConfig? := c.authDecl?.map (·.2.configConst),
    hasOnCreateAccount := onCreateRun?.isSome, hasOnSignIn := onSignInRun?.isSome, hasHttpRoutes := !httpDispatchArms.isEmpty, hasWsProject := !wsProjectArms.isEmpty }

@[noinline] private def mkStepRelInvCmdPure (c : SrvElabCtx) (isAsync : Bool) (fnIdent targetId sOldId sNewId : Ident)
    (fnLit : StrLit) (allBinderIds : Array Ident) (allBinderTys : Array Term) (targetCall : Term)
    (suffix lbl : String) (relOrFld : Sum Term (Ident × Term)) : PureQuotM (TSyntax `command) := do
  let (thmId, lblLit, invUnfolds) := (c.fnSubId fnIdent suffix, Syntax.mkStrLit lbl, #[c.stateInvId] ++ c.statefulHelperIds)
  let (aRel, pGoal) ← match relOrFld with
    | .inl relProp => pure (relProp, ← `(Qed.Server.srvWithNewState (($targetCall).1) (fun ($sNewId:ident : $(c.stateId)) => $relProp)))
    | .inr (fldId, miProp) => pure (← `(($sNewId).$fldId:ident = ($sOldId).$fldId:ident ∨ $miProp), ← `((($targetCall).1).$fldId:ident = ($sOldId).$fldId:ident ∨ $miProp))
  if isAsync then
    `(command| theorem $thmId $[($allBinderIds:ident : $allBinderTys:term)]* :
        Qed.Server.ProgPreservesStepRel $(c.stateInvId) (fun ($sOldId:ident $sNewId:ident : $(c.stateId)) => $aRel) ($targetCall : Qed.Server.ThreadProg $(c.stateId) _) := by qedSrvProveAsync $targetId [$[$invUnfolds],*] $fnLit $lblLit)
  else
    `(command| theorem $thmId ($sOldId:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]* (_hInv : $(c.stateInvId) $sOldId) : $pGoal := by qedSrvProveStep [$(c.stateInvId), $targetId] $fnLit $lblLit)

@[noinline] def elabServerFnInvariants (isAsync : Bool) (fnStr : String) (fnIdent targetId : Ident)
    (allBinderIds : Array Ident) (allBinderTys : Array Term) (targetCall : Term) : SrvElabM Bool := do
  let c ← read; let (fnLit, sOldId, sNewId) := (Syntax.mkStrLit fnStr, mkIdent (if isAsync then `_sOld else `_s0), mkIdent `_sNew)
  let (ok1, _) ← foldlSrv c.invs (true, 0) fun (ok, i) (exprStx, isTwoSt, lbl) => do
    if !ok || !isTwoSt then return (ok, i)
    let rel ← lowerSrvExpr { fnName := "invariant", stateFields := c.stateFieldNames, envVars := c.envVarNames, stateRule := .invariantProp sNewId sOldId false } .propInv exprStx
    elabSrvPure (mkStepRelInvCmdPure c isAsync fnIdent targetId sOldId sNewId fnLit allBinderIds allBinderTys targetCall s!"_twoInv{i}" lbl (.inl rel))
    return (!(← hasSrvErrors), i + 1)
  if !ok1 then return false
  foldlSrv c.mutInvs.zipIdx true fun ok ((fldId, condStx, lbl), i) => do
    if !ok then return false
    let mi ← lowerSrvExpr { fnName := fnStr, envVars := c.envVarNames } .propInv condStx
    elabSrvPure (mkStepRelInvCmdPure c isAsync fnIdent targetId sOldId sNewId fnLit allBinderIds allBinderTys targetCall s!"_mutInv{i}" lbl (.inr (fldId, mi)))
    return !(← hasSrvErrors)

@[noinline] def mkEnsProofTacPure (asyncTarget? : Option Ident) (unfoldIds : Array Ident) (fnLit : StrLit) (labelStr : String)
    (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : PureQuotM (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
  match asyncTarget?, tac? with
  | none, some ts     => `(Lean.Parser.Tactic.tacticSeq| qedSrvPrepStep [$[$unfoldIds],*]; first | done | ($ts))
  | none, none        => `(Lean.Parser.Tactic.tacticSeq| qedSrvProveStep [$[$unfoldIds],*] $fnLit $(Syntax.mkStrLit s!"ensures: {labelStr}"))
  | some tid, some ts => `(Lean.Parser.Tactic.tacticSeq| qedSrvPrepAsyncEnsures $tid [$[$unfoldIds],*]; first | done | ($ts))
  | some tid, none    => `(Lean.Parser.Tactic.tacticSeq| qedSrvProveAsyncEnsures $tid [$[$unfoldIds],*] $fnLit $(Syntax.mkStrLit s!"ensures: {labelStr}"))

private def deferInvProofs (isA : Bool) (fnStr : String) (fnIdent targetId : Ident) (allBinderIds : Array Ident) (allBinderTys : Array Term) (targetCall : Term) (invCmd : Command) : SrvElabM Unit := do
  let c ← read
  deferSrvProof do
    elabCommand invCmd
    if hasNewErrors (← get).messages c.priorRep c.priorUnrep then return false
    (elabServerFnInvariants isA fnStr fnIdent targetId allBinderIds allBinderTys targetCall).run c

def ElabHandlerRes.isReadOnly (r : ElabHandlerRes) : Bool := !r.mutatesState && !r.dbWrite

@[noinline] private def mkPureHandlerCmdsPure (c : SrvElabCtx) (fnStr : String) (fnIdent stepId s0Id es0Id : Ident)
    (allBinderIds : Array Ident) (allBinderTys callArgs : Array Term) (payloadTerm errTyTerm pureBody : Term)
    (isReadOnly hasEmit : Bool) (ensSpec? : Option FnEnsSpec) : PureQuotM (Command × Term × Command × Option Command × Term) := do
  let (fnLit, singleInvLbl, invThmId, sSnap) := (Syntax.mkStrLit fnStr, Syntax.mkStrLit (singleInvLabelStr c.invs), c.fnSubId fnIdent "_inv", mkIdent `_sSnap)
  let (stepRetTy, stepBody) ← if hasEmit then
      pure (← `($(c.stateId) × (Except $errTyTerm $payloadTerm × List Qed.Server.WsEmit)), ← `(Qed.Server.srvFinishEmit $s0Id (let $es0Id:ident : List Qed.Server.WsEmit := []; $pureBody)))
    else pure (← `($(c.stateId) × Except $errTyTerm $payloadTerm), ← `(Qed.Server.srvFinish $s0Id $pureBody))
  let defCmd ← noUnusedVarsPure (← `(command| @[noinline] def $stepId ($s0Id:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]* : $stepRetTy := $stepBody))
  let stepCall ← mkAppTerms (← `($stepId $s0Id)) (allBinderIds.map (⟨·.raw⟩))
  let invOrRoCmd ← if isReadOnly then
      `(command| theorem $(c.fnSubId fnIdent "_readOnly") ($s0Id:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]* : ($stepCall).1 = $s0Id := by qedSrvProveStep [$stepId] $fnLit $(Syntax.mkStrLit s!"{fnStr} read-only state preservation"))
    else `(command| theorem $invThmId ($s0Id:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]* (_hInv : $(c.stateInvId) $s0Id) : $(c.stateInvId) ($stepCall).1 := by qedSrvProveStep [$(c.stateInvId), $stepId] $fnLit $singleInvLbl)
  let ensCmd? ← match ensSpec? with
    | none => pure none
    | some ens =>
        let postGoal ← ens.postFn (← if hasEmit then `(($stepCall).2.1) else `(($stepCall).2))
        let ensTac ← mkEnsProofTacPure none #[c.stateInvId, stepId, ens.ensId] fnLit ens.labelStr ens.tac?
        some <$> `(command| theorem $(c.fnSubId fnIdent "_ensures") ($s0Id:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]* (_hInv : $(c.stateInvId) $s0Id) : $postGoal := by $ensTac)
  return (defCmd, stepCall, invOrRoCmd, ensCmd?, ← mkAppTerms (← `($stepId $sSnap)) callArgs)

@[noinline] private def mkAsyncHandlerCmdsPure (c : SrvElabCtx) (fnStr : String) (fnIdent handlerId : Ident)
    (allBinderIds : Array Ident) (allBinderTys callArgs : Array Term) (payloadTerm errTyTerm asyncBody : Term)
    (ensSpec? : Option FnEnsSpec) : PureQuotM (Command × Term × Option Command × Option Command × Term) := do
  let (fnLit, singleInvLbl, invThmId, atomicBs) := (Syntax.mkStrLit fnStr, Syntax.mkStrLit (singleInvLabelStr c.invs), c.fnSubId fnIdent "_inv", ← c.atomicBindersPure)
  let defCmd ← noUnusedVarsPure (← `(command| @[noinline] def $handlerId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m] $[$atomicBs:bracketedBinder]* $[($allBinderIds:ident : $allBinderTys:term)]* : m (Except $errTyTerm $payloadTerm) := Qed.Server.srvFinishM $asyncBody))
  let hCall ← mkAppTerms handlerId (allBinderIds.map (⟨·.raw⟩))
  let invCmd? ← if !c.hasState then pure none else do
    let invUnfolds := #[c.stateInvId] ++ c.statefulHelperIds
    some <$> `(command| theorem $invThmId $[($allBinderIds:ident : $allBinderTys:term)]* : Qed.Server.ProgPreservesInv $(c.stateInvId) ($hCall : Qed.Server.ThreadProg $(c.stateId) _) := by qedSrvProveAsync $handlerId [$[$invUnfolds],*] $fnLit $singleInvLbl)
  let ensCmd? ← match ensSpec? with
    | none => pure none
    | some ens =>
        let (invT, tyT, extra) ← if c.hasState then pure (⟨c.stateInvId.raw⟩, ⟨c.stateId.raw⟩, #[c.stateInvId]) else pure (← `(fun _ : Unit => True), ← `(Unit), #[])
        let outVar := mkIdent `_srvOut; let postBody ← ens.postFn ⟨outVar.raw⟩
        let ensTac ← mkEnsProofTacPure (some handlerId) (extra ++ c.statefulHelperIds |>.push ens.ensId) fnLit ens.labelStr ens.tac?
        some <$> `(command| theorem $(c.fnSubId fnIdent "_ensures") $[($allBinderIds:ident : $allBinderTys:term)]* : Qed.Server.ProgEnsures $invT (fun ($outVar:ident : Except $errTyTerm $payloadTerm) => $postBody) ($hCall : Qed.Server.ThreadProg $tyT _) := by $ensTac)
  return (defCmd, hCall, invCmd?, ensCmd?, ← mkAppTerms handlerId callArgs)

@[noinline] def elabServerHandler (isAsync : Bool) (fnStr : String) (fnIdent : Ident)
    (extraBinderIds : Array Ident) (extraBinderTys extraCallArgs : Array Term) (payloadTerm errTyTerm : Term)
    (baseCtx : LowerCtx) (bodyStmts : Array Syntax) (ensSpec? : Option FnEnsSpec) (ctxArg? : Option Term := none) : SrvElabM (Option ElabHandlerRes) := do
  let c ← read
  let (allBinderIds, allBinderTys, callArgs) ← runSrvPQ do
    return (c.envIdents ++ #[c.ctxId] ++ extraBinderIds, (← c.envBinderTysPure) ++ #[← `(Qed.Server.RequestCtx)] ++ extraBinderTys,
            c.envIdents.map (⟨·.raw⟩) ++ #[ctxArg?.getD ⟨c.ctxId.raw⟩] ++ extraCallArgs)
  let hasEmit := blockHasEmit bodyStmts
  if c.hasState && !isAsync then
    let (s0Id, es0Id, stepId) := (mkIdent `_s0, mkIdent `_es0, c.fnSubId fnIdent "_step")
    let (pureBody, lSt) ← liftM <| (lowerPureBlock (if hasEmit then { baseCtx with emitAcc? := some es0Id } else baseCtx) false s0Id s0Id bodyStmts).run {}
    recordSrvExtRoots lSt.extRoots; let isReadOnly := lSt.mutated.isEmpty
    let (defCmd, stepCall, invOrRoCmd, ensCmd?, stepSnapCall) ← runSrvPQ (mkPureHandlerCmdsPure c fnStr fnIdent stepId s0Id es0Id allBinderIds allBinderTys callArgs payloadTerm errTyTerm pureBody isReadOnly hasEmit ensSpec?)
    elabSrvCmd defCmd; if (← hasSrvErrors) then return none
    if isReadOnly then deferSrvCmd invOrRoCmd else deferInvProofs false fnStr fnIdent stepId allBinderIds allBinderTys stepCall invOrRoCmd
    if let some ec := ensCmd? then deferSrvCmd ec
    return some { runExpr := ← liftM <| mkAtomicRunTerm (mkIdent `_sSnap) ⟨c.stateId.raw⟩ stepSnapCall isReadOnly hasEmit, targetId := stepId, isAsync := false, allBinderIds, allBinderTys, mutatesState := !isReadOnly, dbWrite := lSt.dbWrite, hasEmit, hasCookieOp := lSt.hasCookieOp }
  else
    let handlerId := c.fnSubId fnIdent "_handler"
    let (asyncBody, lSt) ← liftM <| (lowerAsyncBlock baseCtx (if c.hasState then some ⟨c.stateId.raw⟩ else none) bodyStmts).run {}
    recordSrvExtRoots lSt.extRoots
    let (defCmd, hCall, invCmd?, ensCmd?, runExpr) ← runSrvPQ (mkAsyncHandlerCmdsPure c fnStr fnIdent handlerId allBinderIds allBinderTys callArgs payloadTerm errTyTerm asyncBody ensSpec?)
    elabSrvCmd defCmd; if (← hasSrvErrors) then return none
    if let some ic := invCmd? then deferInvProofs true fnStr fnIdent handlerId allBinderIds allBinderTys hCall ic
    if let some ec := ensCmd? then deferSrvCmd ec
    return some { runExpr, targetId := handlerId, isAsync := true, allBinderIds, allBinderTys, mutatesState := !lSt.mutated.isEmpty, dbWrite := lSt.dbWrite, hasEmit, hasCookieOp := lSt.hasCookieOp }

end SrvHelpers
end Qed.Server
