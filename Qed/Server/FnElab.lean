import Qed.Server.Lower
import Qed.Schema.Codec
import Qed.Schema.Registry

namespace Qed.Server
open Qed.Lang

/-! ## `server` Command Elaborator: Context & Shared Builders (`SrvElabCtx` / `SrvElabM`) -/

structure ParsedEnvDecl where
  (ident : Lean.Ident) (osKey : String) (default? : Option String := none) (isSecret : Bool := false)

abbrev ParsedStateDecl := Lean.Ident × Lean.Term × Option Lean.Syntax × Option Lean.Term
abbrev ParsedMutInv    := Lean.Ident × Lean.Syntax × String
abbrev ParsedInv       := Lean.Syntax × Bool × String

structure ParsedServerBlock where
  (dbDecls : Array (Lean.Ident × DatabaseInfo) := #[]) (serviceDecls : Array (Lean.Ident × ServiceInfo) := #[])
  (authDecl? : Option (Lean.Ident × AuthInfo) := none) (envDecls : Array ParsedEnvDecl := #[])
  (stateDecls : Array ParsedStateDecl := #[]) (mutInvs : Array ParsedMutInv := #[]) (invs : Array ParsedInv := #[])
  (rawInvs : Array (Lean.Ident × Array Lean.Syntax) := #[]) (metaInvs : Array (Lean.Ident × Array Lean.Syntax) := #[])
  (helperClauses fnClauses chanClauses httpClauses jobClauses exampleClauses : Array Lean.Syntax := #[])
  (beforeClause? onCreateAccountClause? onSignInClause? : Option Lean.Syntax := none)

structure SrvElabCtx where
  (priorRep priorUnrep : Nat) (srvIdent : Lean.Ident) (srvName fullSrvName : Lean.Name) (hasState : Bool)
  (dbDecls : Array (Lean.Ident × DatabaseInfo)) (serviceDecls : Array (Lean.Ident × ServiceInfo) := #[])
  (authDecl? : Option (Lean.Ident × AuthInfo)) (envDecls : Array ParsedEnvDecl)
  (stateFieldNames envVarNames : Array String) (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
  (chanSigs : Array SrvChanSig := #[]) (helpers : Array SrvHelperSig := #[]) (statefulHelperIds : Array Lean.Ident := #[])
  (deferredProofs : IO.Ref (Array (Lean.Elab.Command.CommandElabM Bool))) (extRootsRef : IO.Ref (Array Lean.Name))

abbrev SrvElabM := ReaderT SrvElabCtx Lean.Elab.Command.CommandElabM

structure ParsedFnParams where
  (idents : Array Lean.Ident := #[]) (tyTerms : Array Lean.Term := #[])
  (defBinders : Array (Lean.TSyntax `Lean.Parser.Term.bracketedBinder) := #[]) (names : Array String := #[])
  (minParamCount : Nat := 0) (hasExplicitCtx : Bool := false)
  (defaultExprs : Array Lean.Syntax := #[]) (txParams : Array (Lean.Ident × DatabaseInfo) := #[])

structure LoweredAuthBind where
  (binderId : Lean.Ident) (binderName : String) (extraIds : Array Lean.Ident) (extraTys : Array Lean.Term) (authInfo? : Option AuthInfo)

structure LoweredRequires where
  (authBind? : Option LoweredAuthBind := none) (reqPropTerms : Array Lean.Term) (reqHypIds : Array Lean.Ident)
  (reqLabels : Array String) (requiresAuth : Bool) (clientReqId? : Option Lean.Ident)
  (clientReqConst? : Option Lean.Name) (clientReqLabel : String)

structure FnEnsSpec where
  (ensId : Lean.Ident) (postFn : Lean.Term → PureQuotM Lean.Term) (labelStr : String) (tac? : Option (Lean.TSyntax ``Lean.Parser.Tactic.tacticSeq) := none)

structure ElabHandlerRes where
  (runExpr : Lean.Term) (targetId : Lean.Ident) (isAsync : Bool)
  (allBinderIds : Array Lean.Ident) (allBinderTys : Array Lean.Term)
  (mutatesState dbWrite hasEmit : Bool) (hasCookieOp : Bool := false)

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
def SrvElabCtx.envBinderTysPure (c : SrvElabCtx) : PureQuotM (Array Term) :=
  pure <| c.envDecls.map fun e => mkCIdent (if e.isSecret then ``Qed.Secret else ``String)
def SrvElabCtx.atomicBindersPure (c : SrvElabCtx) : PureQuotM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  if c.hasState then pure #[← `(bracketedBinder| [Qed.Server.MonadAtomic $(c.stateId) m])] else pure #[]
@[noinline] def mkStrListDefPure (id : Ident) (xs : Array String) : PureQuotM (TSyntax `command) := do
  mkDefValPure id #[] (← mkAppC ``List #[mkCIdent ``String]) (← mkListLitPure (xs.map (Syntax.mkStrLit ·)))

@[noinline] def srvErrAt {α : Type} (ref : Syntax) (msg : String) : SrvElabM α := liftM <| errAt ref msg
@[noinline] def runSrvPQ {α : Type} (k : PureQuotM α) : SrvElabM α := liftM <| runPQ k
@[noinline] def liftSrvMacro {α : Type} (m : MacroM α) : SrvElabM α := liftM <| liftMacroCmd m
@[noinline] def foldlSrv {α β : Type} (xs : Array α) (init : β) (f : β → α → SrvElabM β) : SrvElabM β := xs.foldlM f init
@[noinline] def mapSrv {α β : Type} (xs : Array α) (f : α → SrvElabM β) : SrvElabM (Array β) := xs.mapM f
@[noinline] def foldOptSrv {α β : Type} (xs : Array α) (init : β) (f : β → α → SrvElabM (Option β)) : SrvElabM (Option β) :=
  xs.foldlM (init := some init) fun acc? x => match acc? with | some acc => f acc x | none => pure none
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
  if !allowDefaults then return ({ pp with idents := pp.idents.push pid, tyTerms := pp.tyTerms.push pty.term, names := pp.names.push pstr, minParamCount := pp.minParamCount + 1 }, false)
  let txDb? ← match pty.mods.isEmpty && !pty.isProto && !pty.isForm, pty.baseName with
    | true, .str pre "Tx" => match (c.dbDecls.find? (·.1.getId.eraseMacroScopes == pre)).map Prod.snd with
        | some d => pure (some d) | none => pure (lookupDatabase? (← getEnv) (← getCurrNamespace) (← getOpenDecls) pre)
    | _, _ => pure none
  let (seenDef', minPC, defExprs, defT?) ← if optDef.getNumArgs == 2 then
      let dExpr := optDef.getArg 1
      let (defT, dSt) ← liftM <| (lowerExpr { fnName := ctxLabel, envVars := c.envVarNames, locals := pp.names, stateRule := .statelessServer } .val dExpr).run {}
      recordSrvExtRoots dSt.extRoots; pure (true, pp.minParamCount, pp.defaultExprs.push dExpr, some defT)
    else if seenDefault then srvErrAt pid s!"non-default parameter `{pstr}` cannot follow a parameter with a default value in {ctxLabel}"
    else pure (false, pp.minParamCount + 1, pp.defaultExprs, none)
  let (tyTerm, binder) ← runSrvPQ (mkFnParamBinderPure pid pty.term (txDb?.map (·.dbName.toString)) defT?)
  return ({ idents := pp.idents.push pid, tyTerms := pp.tyTerms.push tyTerm, defBinders := pp.defBinders.push binder, names := pp.names.push pstr,
            minParamCount := minPC, hasExplicitCtx := pp.hasExplicitCtx || pstr == "ctx", defaultExprs := defExprs, txParams := txDb?.elim pp.txParams (pp.txParams.push ⟨pid, ·⟩) }, seenDef')

@[noinline] def parseSrvFnParams (ctxLabel tyDescPrefix : String) (rawParams : Array Syntax) (reserved extraShadow : Array String := #[]) (allowExplicitCtx := false) : SrvElabM ParsedFnParams :=
  Prod.fst <$> foldlSrv rawParams ({}, false) (parseOneFnParam ctxLabel tyDescPrefix reserved extraShadow true allowExplicitCtx)
@[noinline] def parseSrvParams (ctxLabel tyDescPrefix : String) (rawParams : Array Syntax) (reserved extraShadow : Array String := #[]) : SrvElabM (Array Ident × Array Term × Array String) := do
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
  | ``srvStateClause =>
      let id : Ident := ⟨c.getArg 1⟩; let ty ← liftMacroCmd (lowerSrvType (c.getArg 3) false s!"state field `{id.getId}`"); checkUniqueDecl b "server" srvName id
      let (initStx?, defT?) ← if (c.getArg 4).getNumArgs == 2 then pure (some ((c.getArg 4).getArg 1), none)
        else match ← liftMacroCmd (inferQedTypeDefault? (c.getArg 3)) with | some dt => pure (none, some dt) | none => errAt id s!"state field `{id.getId}` requires an initial value `= ...`"
      return ({ b with stateDecls := b.stateDecls.push (id, ty.term, initStx?, defT?) }, seenInv)
  | ``srvInvMutatingClause => let id : Ident := ⟨c.getArg 1⟩; return ({ b with mutInvs := b.mutInvs.push (⟨c.getArg 4⟩, c.getArg 6, s!"mutating:{id.getId}") }, ← checkUniqueInv seenInv "server" srvName id)
  | ``srvBeforeClause => return ({ b with beforeClause? := ← setOptOnce b.beforeClause? c s!"`before` middleware in `server {srvName}`" (pure c) }, seenInv)
  | ``srvFnClause => return ({ b with fnClauses := b.fnClauses.push rawC }, seenInv)
  | ``srvChannelClause => return ({ b with chanClauses := b.chanClauses.push c }, seenInv)
  | ``srvHttpRouteClause | ``srvStreamClause => return ({ b with httpClauses := b.httpClauses.push c }, seenInv)
  | ``srvJobClause => return ({ b with jobClauses := b.jobClauses.push c }, seenInv)
  | ``srvOnCreateAccountClause => return ({ b with onCreateAccountClause? := ← setOptOnce b.onCreateAccountClause? c s!"`onCreateAccount` hook in `server {srvName}`" (pure c) }, seenInv)
  | ``srvOnSignInClause => return ({ b with onSignInClause? := ← setOptOnce b.onSignInClause? c s!"`onSignIn` hook in `server {srvName}`" (pure c) }, seenInv)
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
  | ``srvInvClause =>
      let id : Ident := ⟨c.getArg 1⟩
      return ({ b with rawInvs := b.rawInvs.push (id, (c.getArg 3).getSepArgs) }, ← checkUniqueInv seenInv blockKind srvName id)
  | ``srvExampleClause => return ({ b with exampleClauses := b.exampleClauses.push rawC }, seenInv)
  | _ =>
      if isService then errAt c s!"only `use`, `env`, `secret`, `fn`, `example`, and `invariant` declarations are allowed in stateless `service {srvName}`"
      parseServerOnlyClause srvName b seenInv rawC c

@[noinline] def parseServerClauses (srvIdent : Ident) (srvName : Name) (clauses : Array Syntax) (isService : Bool := false) : CommandElabM ParsedServerBlock := do
  let (b0, _) ← foldlCmd clauses ({}, #[]) (parseOneServerClause srvName isService)
  if isService then
    if b0.helperClauses.isEmpty then errAt srvIdent s!"`service {srvName}` must declare at least one `fn`"
    return { b0 with metaInvs := b0.rawInvs }
  let stateNames := b0.stateDecls.map (·.1.getId.toString)
  let metaNames : Array String := #["secrets", "rpcs", "routes"]
  let b := b0.rawInvs.foldl (init := b0) fun acc (invId, exprs) =>
    if exprs.all fun e => !exprCallsOld e && !exprMentionsAnyIdent stateNames e && exprMentionsAnyIdent metaNames e then
      { acc with metaInvs := acc.metaInvs.push (invId, exprs) }
    else
      { acc with invs := acc.invs ++ exprs.map fun e => (e, exprCallsOld e, invId.getId.toString) }
  for (c?, lbl) in [(b.onCreateAccountClause?, "onCreateAccount"), (b.onSignInClause?, "onSignIn")] do
    if let some c := c? then if b.authDecl?.isNone then errAt c s!"`{lbl}` in `server {srvName}` requires `use auth : <Auth>`"
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
  | ``qedLamN => scanCtxEnv envVars (locals ++ (stx.getArg 1).getSepArgs.flatMap fun p => (collectLetBinderIds (p.getArg 0)).map (·.toString)) (stx.getArg 4)
  | ``qedAllIn | ``qedAnyIn =>
      let (c1, e1) := scanCtxEnv envVars locals (stx.getArg 3)
      let (c2, e2) := scanCtxEnv envVars (locals ++ (collectLetBinderIds (stx.getArg 1)).map (·.toString)) (stx.getArg 5)
      (c1 || c2, e1 || e2)
  | ``qedAllVars | ``qedAnyVars => scanCtxEnv envVars (locals ++ (stx.getArg 1).getSepArgs.map fun b => (qedAllVarIdent b).getId.toString) (stx.getArg 3)
  | _ => stx.getArgs.foldl (fun (ac, ae) ch => let (c, e) := scanCtxEnv envVars locals ch; (ac || c, ae || e)) (false, false)

def isAuthReqLabel (s : String) : Bool := s.contains "ctx.userId" || s.contains "ctx.isAuthenticated" || s.contains "ctx.bearerToken"

@[noinline] def wrapReqsPure (reqProps : Array Term) (reqHIds : Array Ident) (reqLbls : Array String) (inner : Term) (pureWrap : Bool := true) : PureQuotM Term :=
  foldrPQ (reqProps.zip (reqHIds.zip reqLbls)) inner fun (prop, hid, rLbl) g => do
    let ctor := if isAuthReqLabel rLbl then ``Qed.Server.ApiError.unauthorized
      else if ["ctx.hasClaim", "ctx.claim", "ctx.isSession", "ctx.authMethod", "emailVerified"].any (rLbl.contains ·) then ``Qed.Server.ApiError.forbidden
      else ``Qed.Server.ApiError.badRequest
    let errT ← mkPureErr ctor (Syntax.mkStrLit s!"precondition failed: {rLbl}") pureWrap
    `(if $hid:ident : $prop then $g else $errT)

def LoweredRequires.allBinderIds (r : LoweredRequires) : Array Ident := (r.authBind?.map (·.extraIds) |>.getD #[]) ++ r.reqHypIds
def LoweredRequires.allBinderTys (r : LoweredRequires) : Array Term := (r.authBind?.map (·.extraTys) |>.getD #[]) ++ r.reqPropTerms
def LoweredRequires.allBinderArgs (r : LoweredRequires) : Array Term := r.allBinderIds.map (⟨·.raw⟩)
def LoweredRequires.extraLocals (r : LoweredRequires) : Array String := r.authBind?.map (fun ab => #[ab.binderName]) |>.getD #[]

@[noinline] def wrapAuthUserPure (ctxId uId hEq hNe : Ident) (authInfo? : Option AuthInfo)
    (unauthMsg : String) (pureWrap : Bool) (body : Term) (hLen? : Option Ident := none) : PureQuotM Term := do
  let unauthErr ← mkPureErr ``Qed.Server.ApiError.unauthorized (Syntax.mkStrLit unauthMsg) pureWrap
  let uidExpr : Term ← if authInfo?.isSome then `(($uId).id) else pure ⟨uId.raw⟩
  let inner ← match hLen? with
    | none => pure body
    | some hLen => do
        let badLen ← mkPureErr ``Qed.Server.ApiError.unauthorized (Syntax.mkStrLit "invalid user id length") pureWrap
        `(if $hLen:ident : 1 ≤ ($uidExpr).length ∧ ($uidExpr).length ≤ 128 then $body else $badLen)
  match authInfo? with
  | some ai =>
      let hFrom := mkIdent `_hFromCtx
      `(match $hFrom:ident : $(mkIdentFrom uId (ai.authName ++ `fromCtx)) $ctxId with
        | Option.none => $unauthErr
        | Option.some $uId:ident =>
            have $hEq:ident : Option.some (($uId).id) = ($ctxId).userId := $(mkIdentFrom uId (ai.authName ++ `fromCtx_userId)) $ctxId $uId $hFrom
            have $hNe:ident : ($ctxId).userId ≠ Option.none := (by intro _hN; rw [_hN] at $hEq:ident; cases $hEq:ident)
            $inner)
  | none =>
      let hUid := mkIdent `_hUidCtx
      `(match $hUid:ident : ($ctxId).userId with
        | Option.none => $unauthErr
        | Option.some $uId:ident => have $hEq:ident : Option.some $uId = ($ctxId).userId := ($hUid).symm; have $hNe:ident : ($ctxId).userId ≠ Option.none := (by rw [$hUid:ident]; simp); $inner)

@[noinline] def wrapAuthAndReqsPure (reqs : LoweredRequires) (inner : Term) (pureWrap : Bool := true) : PureQuotM Term := do
  let body ← wrapReqsPure reqs.reqPropTerms reqs.reqHypIds reqs.reqLabels inner pureWrap
  let some ab := reqs.authBind? | return body
  wrapAuthUserPure (mkIdent `ctx) ab.binderId ab.extraIds[1]! ab.extraIds[2]! ab.authInfo? "authentication required" pureWrap body (some ab.extraIds[3]!)

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

@[noinline] def mkAuthExtraTysPure (ctxId uId : Ident) (authInfo? : Option AuthInfo) (includeLen : Bool := true) : PureQuotM (Array Term) := do
  let (uTy, uidExpr) : Term × Term ← match authInfo? with | some ai => pure (mkIdentFrom uId (ai.authName ++ `User), ← `(($uId).id)) | none => pure (mkCIdent ``String, ⟨uId.raw⟩)
  let base := #[uTy, ← `(Option.some $uidExpr = ($ctxId).userId), ← `(($ctxId).userId ≠ Option.none)]
  if includeLen then return base.push (← `(1 ≤ ($uidExpr).length ∧ ($uidExpr).length ≤ 128)) else return base

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
  let bindVal (ty rhs body : Term) : PureQuotM Term := if useBeta then `((fun ($eid:ident : $ty) => $body) $rhs) else mkLetBindTerm eid.raw (some ty) rhs body
  let errP (msg : String) := mkPureErr ``Qed.Server.ApiError.internal (Syntax.mkStrLit msg)
  let pfTriv : PureQuotM Term := `(Qed.Server.ProgSpec.pure_class _ trivial)
  let optPf (mk : Term → PureQuotM Term) : PureQuotM (Option Term) := match accPf? with | some pf => some <$> mk pf | none => pure none
  let (runBody, pfBody?) ← if e.isSecret then
      let secRawId := mkIdent `_secRaw
      let (errT, okRun) := (← errP s!"missing required secret `{e.osKey}`", ← bindVal (mkCIdent ``Qed.Secret) (← mkAppC ``Qed.Secret.ofString #[secRawId]) accRun)
      pure (← `(match _envOpt with | some $secRawId:ident => if ($secRawId).isEmpty then $errT else $okRun | none => $errT),
            ← optPf fun pf => do let t ← pfTriv; `(match _envOpt with | some $secRawId:ident => if ($secRawId).isEmpty then $t else (fun ($eid:ident : Qed.Secret) => $pf) (Qed.Secret.ofString $secRawId) | none => $t))
    else match e.default? with
      | some defVal =>
          let dVal ← `(_envOpt.getD $(Syntax.mkStrLit defVal))
          pure (← bindVal (mkCIdent ``String) dVal accRun, ← optPf fun pf => `((fun ($eid:ident : String) => $pf) $dVal))
      | none =>
          let errT ← errP s!"missing required environment variable `{e.osKey}`"
          pure (← `(match _envOpt with | some $eid:ident => $accRun | none => $errT),
                ← optPf fun pf => do `(match _envOpt with | some $eid:ident => $pf | none => $(← pfTriv)))
  let readCall ← mkAppC ``Qed.Server.MonadServer.readEnv #[keyLit]
  return (← `($readCall >>= fun _envOpt => $runBody),
          ← match pfBody? with | some pb => some <$> `(Qed.Server.ProgSpec.safeIO_bind $readCall fun _envOpt => $pb) | none => pure none)

@[noinline] def wrapWithEnvDeclsPure (envDecls : Array ParsedEnvDecl) (innerRun : Term) (innerProof? : Option Term := none) : PureQuotM (Term × Option Term) :=
  foldrPQ envDecls (innerRun, innerProof?) wrapOneEnvDeclPure

@[noinline] private def mkDispatchDefPure (c : SrvElabCtx) (defLeaf : Name) (atomicBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (paramIds : Array Ident) (paramTys : Array Term) (retTy bodyTerm : Term) : PureQuotM (TSyntax `command) := do
  let pBs ← mkTypedBindersPure (#[c.ctxId] ++ paramIds) (#[mkCIdent ``Qed.Server.RequestCtx] ++ paramTys)
  noUnusedVarsPure (← `(command| @[noinline, nospecialize] def $(c.subId defLeaf) {m : Type → Type} [Monad m] [Qed.Server.MonadServer m] $[$atomicBinders:bracketedBinder]* $[$pBs:bracketedBinder]* :
    m (Except Qed.Server.ApiError $retTy) := $((← wrapWithEnvDeclsPure c.envDecls bodyTerm).1)))

@[noinline] private def mkMatchFb1Pure (scrut : Ident) (arms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr)) (fb : Term) : PureQuotM Term := do
  `(match $scrut:ident with $[$(arms.push (← `(Lean.Parser.Term.matchAltExpr| | _ => $fb))):matchAlt]*)
@[noinline] private def mkMatchFb2Pure (s1 s2 : Ident) (arms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr)) (fb : Term) : PureQuotM Term := do
  `(match $s1:ident, $s2:ident with $[$(arms.push (← `(Lean.Parser.Term.matchAltExpr| | _, _ => $fb))):matchAlt]*)

@[noinline] private def mkServerDispatchCmdsPure (c : SrvElabCtx) (methodInfos : Array ServerMethodInfo) (reqSecrets : Array String)
    (dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr)) (chanNames : Array String)
    (wsDispatchArms wsProjectArms httpDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (httpRoutes : Array (String × String × Bool))
    (onCreateRun? onSignInRun? : Option Term) : PureQuotM (Array (TSyntax `command)) := do
  let mut cmds : Array (TSyntax `command) := #[]
  if c.hasState then cmds := cmds.push (← `(command|
    theorem $(c.subId `concurrent_linearizable) {Out : Type} (st : Qed.Server.MultiCoreState $(c.stateId) Out) (hsched : Qed.Server.MultiCoreSchedule $(c.stateInvId) ⟨$(c.subId `initState), []⟩ st) :
        $(c.stateInvId) st.shared := Qed.Server.concurrent_schedule_preserves_inv $(c.stateInvId) $(c.subId `initState) st $(c.subId `inv_init) hsched))
  let (atomicBs, strTy, bytesTy, u8Ty) := (← c.atomicBindersPure, mkCIdent ``String, mkCIdent ``ByteArray, mkCIdent ``UInt8)
  let (mVar, wsKVar, wsCVar, wsPVar, wsPayVar, hMVar, hPVar) := (mkIdent `method, mkIdent `wsKind, mkIdent `wsChannel, mkIdent `wsParams, mkIdent `wsPayload, mkIdent `httpMethod, mkIdent `httpPath)
  let rpcMetaTs ← mapPQ methodInfos fun m => mkAppC ``Qed.Server.RpcMeta.mk #[Syntax.mkStrLit m.name, quote m.requiresAuth, quote m.isReadOnly]
  let routeMetaTs ← mapPQ httpRoutes fun (m, p, reqA) => mkAppC ``Qed.Server.RouteMeta.mk #[Syntax.mkStrLit m, Syntax.mkStrLit p, quote reqA]
  cmds := cmds ++ #[
    ← mkStrArrDefPure (c.subId `secrets) reqSecrets, ← mkMarkerThmPure (c.subId `_qed_server_marker),
    ← mkStrArrDefPure (c.subId `readOnlyMethods) ((methodInfos.filter (·.isReadOnly)).map (·.name)),
    ← `(command| def $(c.subId `rpcs) : Array Qed.Server.RpcMeta := #[$[$rpcMetaTs:term],*]),
    ← `(command| def $(c.subId `routes) : Array Qed.Server.RouteMeta := #[$[$routeMetaTs:term],*]),
    ← mkStrListDefPure (c.subId `methods) (methodInfos.map (·.name)), ← mkStrListDefPure (c.subId `channels) chanNames,
    ← mkDispatchDefPure c `dispatchM atomicBs #[mVar, mkIdent `reqBytes] #[strTy, bytesTy] bytesTy
      (← mkMatchFb1Pure mVar dispatchArms (← mkPureErr ``Qed.Server.ApiError.notFound (← `("unknown RPC method: " ++ $mVar))))]
  if !chanNames.isEmpty then
    cmds := cmds.push (← mkDispatchDefPure c `wsDispatchM atomicBs #[wsKVar, wsCVar, wsPVar, wsPayVar] #[u8Ty, strTy, bytesTy, bytesTy] bytesTy
      (← mkMatchFb2Pure wsKVar wsCVar wsDispatchArms (← mkPureErr ``Qed.Server.ApiError.notFound (← `("unknown WebSocket channel: " ++ $wsCVar)))))
  if !wsProjectArms.isEmpty then cmds := cmds.push (← noUnusedVarsPure (← `(command|
    @[noinline] def $(c.subId `wsProject) ($(c.ctxId):ident : Qed.Server.RequestCtx) ($wsCVar:ident : String) ($wsPVar:ident : ByteArray) ($wsPayVar:ident : ByteArray) : Qed.Server.WsProjectOut :=
      $(← mkMatchFb1Pure wsCVar wsProjectArms (mkCIdent ``Qed.Server.WsProjectOut.passthrough)))))
  if !httpDispatchArms.isEmpty then
    cmds := cmds.push (← mkDispatchDefPure c `httpDispatchM atomicBs #[hMVar, hPVar] #[strTy, strTy] (← mkAppC ``Option #[mkCIdent ``Qed.Server.HttpResponse])
      (← mkMatchFb2Pure hMVar hPVar httpDispatchArms (← mkPureOk (mkCIdent ``Option.none))))
  if let some (_, ai) := c.authDecl? then if onCreateRun?.isSome || onSignInRun?.isSome then
    let (hkVar, okU) := (mkIdent `hookKind, ← mkPureOk (mkCIdent ``Unit.unit))
    let body ← wrapAuthUserPure c.ctxId (mkIdentFrom c.srvIdent `_authUser) (mkIdent `_hAuthEq) (mkIdent `_hAuth) (some ai) "missing authenticated user" true
      (← `(match $hkVar:ident with | (0 : UInt8) => $(onCreateRun?.getD okU) | (1 : UInt8) => $(onSignInRun?.getD okU) | _ => $okU))
    cmds := cmds.push (← mkDispatchDefPure c `authHookM atomicBs #[hkVar] #[u8Ty] (mkCIdent ``Unit) body)
  return cmds

@[noinline] def elabServerDispatchCmds (methodInfos : Array ServerMethodInfo) (dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (chanNames : Array String) (wsDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (wsProjectArms httpDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[])
    (httpRoutes : Array (String × String × Bool) := #[]) (jobNames : Array String := #[])
    (onCreateRun? onSignInRun? : Option Term := none) : SrvElabM Unit := do
  let c ← read; let (reqSecrets, ownSecrets, usedExts, allDbs, allEnvs) ← collectServerSecretsAndExts
  elabSrvPureCmds (mkServerDispatchCmdsPure c methodInfos reqSecrets dispatchArms chanNames wsDispatchArms wsProjectArms httpDispatchArms httpRoutes onCreateRun? onSignInRun?)
  modifyEnv fun env => serverRegistry.addEntry env {
    serverName := c.fullSrvName, shortName := c.srvName.toString, hasState := c.hasState, secrets := reqSecrets, ownSecrets,
    envVars := allEnvs, externalServices := usedExts, methods := methodInfos, channels := chanNames, jobs := jobNames, databases := allDbs,
    authName? := c.authDecl?.map (·.2.authName), authConfig? := c.authDecl?.map (·.2.configConst),
    hasOnCreateAccount := onCreateRun?.isSome, hasOnSignIn := onSignInRun?.isSome, hasHttpRoutes := !httpDispatchArms.isEmpty, hasWsProject := !wsProjectArms.isEmpty }

@[noinline] private def mkStepRelInvCmdPure (c : SrvElabCtx) (isAsync : Bool) (fnIdent targetId sOldId sNewId : Ident)
    (fnLit : StrLit) (allBinderIds : Array Ident) (allBinderTys : Array Term) (targetCall : Term)
    (suffix lbl : String) (relOrFld : Sum Term (Ident × Term)) : PureQuotM (TSyntax `command) := do
  let (thmId, lblLit, allBs) := (c.fnSubId fnIdent suffix, Syntax.mkStrLit lbl, ← mkTypedBindersPure allBinderIds allBinderTys)
  let (aRel, pGoal) ← match relOrFld with
    | .inl relProp => pure (relProp, ← mkAppC ``Qed.Server.srvWithNewState #[← `(($targetCall).1), ← `(fun ($sNewId:ident : $(c.stateId)) => $relProp)])
    | .inr (fldId, miProp) => pure (← `(($sNewId).$fldId:ident = ($sOldId).$fldId:ident ∨ $miProp), ← `((($targetCall).1).$fldId:ident = ($sOldId).$fldId:ident ∨ $miProp))
  if isAsync then
    let invUnfolds := #[c.stateInvId] ++ c.statefulHelperIds
    let progT ← mkAscribePure targetCall (← mkAppC ``Qed.Server.ThreadProg #[c.stateId, ← `(_)])
    mkSrvThmPure thmId allBs (← mkAppC ``Qed.Server.ProgPreservesStepRel #[c.stateInvId, ← `(fun ($sOldId:ident $sNewId:ident : $(c.stateId)) => $aRel), progT])
      (← `(Lean.Parser.Tactic.tacticSeq| qedSrvProveAsync $targetId [$[$invUnfolds],*] $fnLit $lblLit))
  else
    let bs := #[← `(bracketedBinder| ($sOldId:ident : $(c.stateId)))] ++ allBs ++ #[← `(bracketedBinder| (_hInv : $(c.stateInvId) $sOldId))]
    mkSrvThmPure thmId bs pGoal (← `(Lean.Parser.Tactic.tacticSeq| qedSrvProveStep [$(c.stateInvId), $targetId] $fnLit $lblLit))

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

@[noinline] private def mkHandlerCmdsPure (c : SrvElabCtx) (isPureStep : Bool) (fnStr : String) (fnIdent targetId s0Id es0Id : Ident)
    (allBinderIds : Array Ident) (allBinderTys callArgs : Array Term) (payloadTerm errTyTerm rawBody : Term)
    (isReadOnly hasEmit : Bool) (ensSpec? : Option FnEnsSpec) : PureQuotM (Command × Term × Option Command × Option Command × Term) := do
  let (fnLit, singleInvLbl, invThmId, allBs, bArgs) := (Syntax.mkStrLit fnStr, Syntax.mkStrLit (singleInvLabelStr c.invs), c.fnSubId fnIdent "_inv", ← mkTypedBindersPure allBinderIds allBinderTys, allBinderIds.map (⟨·.raw⟩))
  let excTy ← mkAppC ``Except #[errTyTerm, payloadTerm]
  let (defCmd, targetCall, invCmd?, callExpr, ensBs, ensAsync?, ensUnfolds, mkEnsGoal) ← if isPureStep then
      let (stepRetTy, stepBody) ← if hasEmit then
          pure (← mkAppC ``Prod #[c.stateId, ← mkAppC ``Prod #[excTy, ← mkAppC ``List #[mkCIdent ``Qed.Server.WsEmit]]],
                ← `(Qed.Server.srvFinishEmit $s0Id (let $es0Id:ident : List Qed.Server.WsEmit := []; $rawBody)))
        else pure (← mkAppC ``Prod #[c.stateId, excTy], ← mkAppC ``Qed.Server.srvFinish #[s0Id, rawBody])
      let s0B ← `(bracketedBinder| ($s0Id:ident : $(c.stateId)))
      let (preBs, invBs) := (#[s0B] ++ allBs, #[s0B] ++ allBs ++ #[← `(bracketedBinder| (_hInv : $(c.stateInvId) $s0Id))])
      let stepCall ← mkAppTermsPure (← `($targetId $s0Id)) bArgs
      let invCmd ← if isReadOnly then mkSrvThmPure (c.fnSubId fnIdent "_readOnly") preBs (← `(($stepCall).1 = $s0Id)) (← `(Lean.Parser.Tactic.tacticSeq| qedSrvProveStep [$targetId] $fnLit $(Syntax.mkStrLit s!"{fnStr} read-only state preservation")))
        else mkSrvThmPure invThmId invBs (← mkAppTermsPure c.stateInvId #[← `(($stepCall).1)]) (← `(Lean.Parser.Tactic.tacticSeq| qedSrvProveStep [$(c.stateInvId), $targetId] $fnLit $singleInvLbl))
      pure (← mkDefValPure targetId preBs stepRetTy stepBody true, stepCall, some invCmd, ← mkAppTermsPure (← `($targetId $(mkIdent `_sSnap))) callArgs,
            invBs, none, #[c.stateInvId, targetId], fun (ens : FnEnsSpec) => do ens.postFn (← if hasEmit then `(($stepCall).2.1) else `(($stepCall).2)))
    else
      let defCmd ← noUnusedVarsPure (← `(command| @[noinline, nospecialize] def $targetId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m] $[$(← c.atomicBindersPure):bracketedBinder]* $[$allBs:bracketedBinder]* : m $excTy := $(← mkAppC ``Qed.Server.srvFinishM #[rawBody])))
      let hCall ← mkAppTermsPure targetId bArgs
      let invCmd? ← if !c.hasState then pure none else do
        let invUnfolds := #[c.stateInvId] ++ c.statefulHelperIds
        some <$> mkSrvThmPure invThmId allBs (← mkAppC ``Qed.Server.ProgPreservesInv #[c.stateInvId, ← mkAscribePure hCall (← mkAppC ``Qed.Server.ThreadProg #[c.stateId, ← `(_)])])
          (← `(Lean.Parser.Tactic.tacticSeq| qedSrvProveAsync $targetId [$[$invUnfolds],*] $fnLit $singleInvLbl))
      let (invT, tyT, extra) ← if c.hasState then pure ((c.stateInvId : Term), (c.stateId : Term), #[c.stateInvId]) else pure (← `(fun _ : Unit => True), mkCIdent ``Unit, #[])
      pure (defCmd, hCall, invCmd?, ← mkAppTermsPure targetId callArgs, allBs, some targetId, extra ++ c.statefulHelperIds, fun (ens : FnEnsSpec) => do
        let outVar := mkIdent `_srvOut
        mkAppC ``Qed.Server.ProgEnsures #[invT, ← `(fun ($outVar:ident : $excTy) => $(← ens.postFn outVar)), ← mkAscribePure hCall (← mkAppC ``Qed.Server.ThreadProg #[tyT, ← `(_)])])
  let ensCmd? ← match ensSpec? with
    | none => pure none
    | some ens => some <$> mkSrvThmPure (c.fnSubId fnIdent "_ensures") ensBs (← mkEnsGoal ens) (← mkEnsProofTacPure ensAsync? (ensUnfolds.push ens.ensId) fnLit ens.labelStr ens.tac?)
  return (defCmd, targetCall, invCmd?, ensCmd?, callExpr)

@[noinline] def elabServerHandler (isAsync : Bool) (fnStr : String) (fnIdent : Ident)
    (extraBinderIds : Array Ident) (extraBinderTys extraCallArgs : Array Term) (payloadTerm errTyTerm : Term)
    (baseCtx : LowerCtx) (bodyStmts : Array Syntax) (ensSpec? : Option FnEnsSpec) (ctxArg? : Option Term := none) : SrvElabM (Option ElabHandlerRes) := do
  let c ← read
  let (allBinderIds, allBinderTys, callArgs) ← runSrvPQ do
    return (c.envIdents ++ #[c.ctxId] ++ extraBinderIds, (← c.envBinderTysPure) ++ #[mkCIdent ``Qed.Server.RequestCtx] ++ extraBinderTys,
            c.envIdents.map (⟨·.raw⟩) ++ #[ctxArg?.getD ⟨c.ctxId.raw⟩] ++ extraCallArgs)
  let (hasEmit, isPureStep) := (blockHasEmit bodyStmts, c.hasState && !isAsync)
  let (s0Id, es0Id, targetId) := (mkIdent `_s0, mkIdent `_es0, c.fnSubId fnIdent (if isPureStep then "_step" else "_handler"))
  let (rawBody, lSt) ← liftM <| (if isPureStep then lowerPureBlock (if hasEmit then { baseCtx with emitAcc? := some es0Id } else baseCtx) false s0Id s0Id bodyStmts
    else lowerAsyncBlock baseCtx (if c.hasState then some ⟨c.stateId.raw⟩ else none) bodyStmts).run {}
  recordSrvExtRoots lSt.extRoots; let isReadOnly := lSt.mutated.isEmpty
  let (defCmd, targetCall, invCmd?, ensCmd?, callExpr) ← runSrvPQ (mkHandlerCmdsPure c isPureStep fnStr fnIdent targetId s0Id es0Id allBinderIds allBinderTys callArgs payloadTerm errTyTerm rawBody isReadOnly hasEmit ensSpec?)
  elabSrvCmd defCmd; if (← hasSrvErrors) then return none
  if let some ic := invCmd? then
    if isPureStep && isReadOnly then deferSrvCmd ic else deferInvProofs (!isPureStep) fnStr fnIdent targetId allBinderIds allBinderTys targetCall ic
  if let some ec := ensCmd? then deferSrvCmd ec
  let runExpr ← if isPureStep then liftM <| mkAtomicRunTerm (mkIdent `_sSnap) ⟨c.stateId.raw⟩ callExpr isReadOnly hasEmit else pure callExpr
  return some { runExpr, targetId, isAsync := !isPureStep, allBinderIds, allBinderTys, mutatesState := !isReadOnly, dbWrite := lSt.dbWrite, hasEmit, hasCookieOp := lSt.hasCookieOp }

end SrvHelpers
end Qed.Server
