import Qed.Server.Lower

namespace Qed.Server
open Qed.Lang

/-! ## `server` Command Elaborator — Context & Shared Builders (`SrvElabCtx` / `SrvElabM`) -/

structure ParsedEnvDecl where
  ident    : Lean.Ident
  osKey    : String
  default? : Option String := none
  isSecret : Bool := false

abbrev ParsedStateDecl := Lean.Ident × Lean.Term × Option Lean.Syntax × Option Lean.Term
abbrev ParsedMutInv    := Lean.Ident × Lean.Syntax × String
abbrev ParsedInv       := Lean.Syntax × Bool × String

structure ParsedServerBlock where
  dbDecls                : Array (Lean.Ident × DatabaseInfo)
  serviceDecls           : Array (Lean.Ident × ServiceInfo) := #[]
  authDecl?              : Option (Lean.Ident × AuthInfo) := none
  envDecls               : Array ParsedEnvDecl
  stateDecls             : Array ParsedStateDecl
  mutInvs                : Array ParsedMutInv
  invs                   : Array ParsedInv
  helperClauses          : Array Lean.Syntax := #[]
  beforeClause?          : Option Lean.Syntax := none
  fnClauses              : Array Lean.Syntax
  chanClauses            : Array Lean.Syntax
  httpClauses            : Array Lean.Syntax := #[]
  jobClauses             : Array Lean.Syntax := #[]
  onCreateAccountClause? : Option Lean.Syntax := none
  onSignInClause?        : Option Lean.Syntax := none
  routesAuthInvs         : Array (Lean.Ident × String × Array String) := #[]
  rpcsAuthInvs           : Array (Lean.Ident × Array String) := #[]
  noSecretsInvs          : Array Lean.Ident := #[]
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
def SrvElabCtx.envBinderTys (c : SrvElabCtx) : CommandElabM (Array Term) :=
  c.envDecls.mapM fun e => if e.isSecret then `(Qed.Secret) else `(String)
def SrvElabCtx.atomicBinders (c : SrvElabCtx) : CommandElabM (Array (TSyntax `Lean.Parser.Term.bracketedBinder)) := do
  if c.hasState then pure #[← `(bracketedBinder| [Qed.Server.MonadAtomic $(c.stateId) m])] else pure #[]

def elabSrvCmd (cmd : Syntax) : SrvElabM Unit := liftM <| elabCommand cmd
def elabSrvCmds (cmds : Array Syntax) : SrvElabM Unit := for cmd in cmds do liftM <| elabCommand cmd

def filterNewWarnings (arr : PersistentArray Message) (priorSize : Nat) : PersistentArray Message :=
  let lst := arr.toList
  ((lst.take priorSize) ++ (lst.drop priorSize).filter (·.severity != .warning)).foldl (·.push ·) {}

def hasNewErrors (log : MessageLog) (priorRep priorUnrep : Nat) : Bool :=
  (log.reported.toList.drop priorRep).any (·.severity == .error) || (log.unreported.toList.drop priorUnrep).any (·.severity == .error)

def hasSrvErrors : SrvElabM Bool := do let c ← read; return hasNewErrors (← get).messages c.priorRep c.priorUnrep
def recordSrvExtRoots (roots : Array Name) : SrvElabM Unit := do (← read).extRootsRef.modify fun acc => roots.foldl pushUnique acc
def deferSrvProof (act : CommandElabM Bool) : SrvElabM Unit := do (← read).deferredProofs.modify (·.push act)

def deferSrvCmd (cmd : TSyntax `command) : SrvElabM Unit := do
  let c ← read; deferSrvProof do elabCommand cmd; return !hasNewErrors (← get).messages c.priorRep c.priorUnrep

def mkBaseLowerCtx (fnName : String) (locals : Array String) (allowAwait allowUnwrap hasFallible : Bool)
    (innerOptTy? : Option Term := none) (domainErrTy? : Option Term := none)
    (isHttpRoute := false) (isStreamRoute := false) (includeDbs := true) (ctxTerm? : Option Term := none)
    (txParams : Array (Ident × DatabaseInfo) := #[]) : SrvElabM LowerCtx := do
  let c ← read
  let txDbAliases ← txParams.mapM fun (pid, dbi) => do
    return (pid.getId.eraseMacroScopes.toString, dbi, ← `(($pid).id))
  return {
    fnName, stateFields := c.stateFieldNames, envVars := c.envVarNames, envIdents := c.envIdents, locals,
    stateRule := if c.hasState then .pureStep (mkIdent `_s0) else .statelessServer,
    allowAwait, allowUnwrap, hasFallible, innerOptTy?, domainErrTy?, channels := c.chanSigs, helpers := c.helpers,
    dbs := if includeDbs then c.dbDecls.map fun (a, i) => (a.getId.toString, i) else #[],
    services := c.serviceDecls.map fun (a, i) => (a.getId.toString, i),
    ctxTerm?, txDbAliases, isHttpRoute, isStreamRoute }

def mkProtoDecodeBind (bytesVar tupleVar : Ident) (tupleTy : Term) (pIdents : Array Ident) (projs : Array Term) (body : Term) : CommandElabM Term := do
  let bound ← (pIdents.zip projs).foldrM (init := body) fun (pid, prj) acc => `(let $pid:ident := $prj; $acc)
  `(match Qed.Proto.decode (α := $tupleTy) $bytesVar with
    | Except.error _decErr => Pure.pure (Except.error (Qed.Server.ApiError.badRequest _decErr))
    | Except.ok $tupleVar:ident => $bound)

def checkSrvParamName (ctxLabel : String) (pid : Ident) (reserved seen extraShadow : Array String := #[]) (allowExplicitCtx := false) : SrvElabM String := do
  let c ← read; let pstr := pid.getId.toString
  if pstr == "ctx" && !allowExplicitCtx then throwErrorAt pid s!"`ctx` is already implicitly available as `RequestCtx` in {ctxLabel}"
  if reserved.contains pstr then throwErrorAt pid s!"`{pstr}` is reserved inside {ctxLabel}; rename this parameter"
  if seen.contains pstr then throwErrorAt pid s!"duplicate parameter `{pstr}` in {ctxLabel}"
  if extraShadow.contains pstr then throwErrorAt pid s!"parameter `{pstr}` shadows an existing binding in {ctxLabel}; rename the parameter"
  if c.envVarNames.contains pstr then throwErrorAt pid s!"parameter `{pstr}` in {ctxLabel} shadows `env`/`secret` binding `{pstr}`; rename the parameter"
  if c.stateFieldNames.contains pstr then throwErrorAt pid s!"parameter `{pstr}` in {ctxLabel} shadows server `state` field `{pstr}`; rename the parameter"
  return pstr

def parseSrvParams (ctxLabel tyDescPrefix : String) (rawParams : Array Syntax) (reserved extraShadow : Array String := #[]) :
    SrvElabM (Array Ident × Array Term × Array String) := do
  let mut idents : Array Ident := #[]; let mut tyTerms : Array Term := #[]; let mut names : Array String := #[]
  for rp in rawParams do
    let pid : Ident := ⟨rp.getArg 0⟩; let pstr ← checkSrvParamName ctxLabel pid reserved names extraShadow
    if (rp.getArg 3).getNumArgs == 2 then
      throwErrorAt (rp.getArg 3) s!"default parameter values are only supported on `fn` declarations, not in {ctxLabel}"
    let pty ← liftMacroM <| lowerSrvType (rp.getArg 2) false s!"{tyDescPrefix} `{pstr}`"
    idents := idents.push pid; tyTerms := tyTerms.push pty.term; names := names.push pstr
  return (idents, tyTerms, names)

structure ParsedFnParams where
  idents         : Array Ident
  tyTerms        : Array Term
  defBinders     : Array (TSyntax `Lean.Parser.Term.bracketedBinder)
  names          : Array String
  minParamCount  : Nat
  hasExplicitCtx : Bool
  defaultExprs   : Array Syntax
  txParams       : Array (Ident × DatabaseInfo) := #[]

def parseSrvFnParams (ctxLabel tyDescPrefix : String) (rawParams : Array Syntax)
    (reserved extraShadow : Array String := #[]) (allowExplicitCtx := false) : SrvElabM ParsedFnParams := do
  let c ← read
  let mut idents : Array Ident := #[]; let mut tyTerms : Array Term := #[]; let mut names : Array String := #[]
  let mut defBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
  let mut minParamCount : Nat := 0; let mut seenDefault := false; let mut hasExplicitCtx := false
  let mut defaultExprs : Array Syntax := #[]; let mut txParams : Array (Ident × DatabaseInfo) := #[]
  for rp in rawParams do
    let pid : Ident := ⟨rp.getArg 0⟩
    let pstr ← checkSrvParamName ctxLabel pid reserved names extraShadow allowExplicitCtx
    if pstr == "ctx" then hasExplicitCtx := true
    let tyStx := rp.getArg 2
    let pty ← liftMacroM <| lowerSrvType tyStx false s!"{tyDescPrefix} `{pstr}`"
    let mut tyTerm := pty.term
    if pty.mods.isEmpty && !pty.isProto && !pty.isForm then
      if let .str pre "Tx" := pty.baseName then
        let dbInfo? : Option DatabaseInfo ←
          match c.dbDecls.find? (fun (al, _) => al.getId.eraseMacroScopes == pre) with
          | some (_, dbi) => pure (some dbi)
          | none => pure (lookupDatabase? (← getEnv) (← getCurrNamespace) (← getOpenDecls) pre)
        if let some dbi := dbInfo? then
          tyTerm ← `(Qed.Server.Db.DbTx $(Syntax.mkStrLit dbi.dbName.toString))
          txParams := txParams.push (pid, dbi)
    let optDef := rp.getArg 3
    if optDef.getNumArgs == 2 then
      seenDefault := true
      let dExpr := optDef.getArg 1
      defaultExprs := defaultExprs.push dExpr
      let (defT, dSt) ← liftM <| (lowerExpr { fnName := ctxLabel, envVars := c.envVarNames, locals := names, stateRule := .statelessServer } .val dExpr).run {}
      recordSrvExtRoots dSt.extRoots
      defBinders := defBinders.push (← `(bracketedBinder| ($pid:ident : $tyTerm := srvAutoField($defT))))
    else
      if seenDefault then throwErrorAt pid s!"non-default parameter `{pstr}` cannot follow a parameter with a default value in {ctxLabel}"
      minParamCount := minParamCount + 1
      defBinders := defBinders.push (← `(bracketedBinder| ($pid:ident : $tyTerm)))
    idents := idents.push pid; tyTerms := tyTerms.push tyTerm; names := names.push pstr
  return { idents, tyTerms, defBinders, names, minParamCount, hasExplicitCtx, defaultExprs, txParams }

private def lowerSrvExpr (ctx : LowerCtx) (mode : ExprMode) (stx : Syntax) : SrvElabM Term := return (← liftM <| (lowerExpr ctx mode stx).run {}).1

@[noinline]
def elabServerStateCmds (stateDecls : Array ParsedStateDecl) : SrvElabM Bool := do
  let c ← read; let (stFieldIds, stFieldTys) := (stateDecls.map (·.1), stateDecls.map (·.2.1))
  let stInitVals ← stateDecls.mapM fun (_, _, initStx?, defT?) => do
    let initTerm ← match initStx?, defT? with | some stx, _ => lowerSrvExpr { fnName := "initState" } .val stx | none, some dt => pure dt | none, none => unreachable!
    `(srvAutoField($initTerm))
  let (initId, invInitId) := (c.subId `initState, c.subId `inv_init)
  elabSrvCmds #[
    ← `(command| structure $(c.stateId) where $[$stFieldIds:ident : $stFieldTys:term]*),
    ← `(command| @[noinline] def $initId : $(c.stateId) := { $[$stFieldIds:ident := $stInitVals:term],* })]
  if (← hasSrvErrors) then return false
  let sParam := mkIdent `_s
  let invCtx : LowerCtx := { fnName := "invariant", stateFields := c.stateFieldNames, envVars := c.envVarNames, stateRule := .invariantProp sParam (mkIdent `_sOld) false }
  let invBody ← Qed.mkConjBody (← (c.invs.filter (!·.2.1)).mapM fun (e, _, _) => lowerSrvExpr invCtx .propInv e) (ascribeProp := false)
  elabSrvCmds #[
    ← `(command| def $(c.stateInvId) ($sParam:ident : $(c.stateId)) : Prop := $invBody),
    ← `(command| theorem $invInitId : $(c.stateInvId) $initId := by
        qedSrvProveStep [$(c.stateInvId), $initId] "initState" $(Syntax.mkStrLit ("init: " ++ singleInvLabelStr c.invs)))]
  return !(← hasSrvErrors)

partial def unwrapDocClause (c : Syntax) : Option (TSyntax ``Lean.Parser.Command.docComment) × Syntax :=
  if c.getKind == ``srvDocClause then
    let (inner?, body) := unwrapDocClause (c.getArg 1)
    (inner?.orElse fun _ => some ⟨c.getArg 0⟩, body)
  else (none, c)

@[noinline]
def parseServerClauses (srvIdent : Ident) (srvName : Name) (clauses : Array Syntax) (isService : Bool := false) : CommandElabM ParsedServerBlock := do
  let blockKind := if isService then "service" else "server"
  let mut dbDecls : Array (Ident × DatabaseInfo) := #[]; let mut serviceDecls : Array (Ident × ServiceInfo) := #[]
  let mut authDecl? : Option (Ident × AuthInfo) := none
  let mut envDecls : Array ParsedEnvDecl := #[]; let mut stateDecls : Array ParsedStateDecl := #[]
  let mut mutInvs : Array ParsedMutInv := #[]; let mut invs : Array ParsedInv := #[]; let mut seenInvNames : Array Name := #[]
  let mut helperClauses : Array Syntax := #[]; let mut beforeClause? : Option Syntax := none
  let mut fnClauses : Array Syntax := #[]; let mut chanClauses : Array Syntax := #[]; let mut httpClauses : Array Syntax := #[]; let mut jobClauses : Array Syntax := #[]
  let mut onCreateAccountClause? : Option Syntax := none; let mut onSignInClause? : Option Syntax := none
  let mut routesAuthInvs : Array (Ident × String × Array String) := #[]
  let mut rpcsAuthInvs : Array (Ident × Array String) := #[]
  let mut noSecretsInvs : Array Ident := #[]
  let mut exampleClauses : Array Syntax := #[]
  for rawC in clauses do
    let (_, c) := unwrapDocClause rawC
    let k := c.getKind
    let hasDecl (nm : Name) := dbDecls.any (·.1.getId == nm) || serviceDecls.any (·.1.getId == nm) || authDecl?.any (·.1.getId == nm) || envDecls.any (·.ident.getId == nm) || stateDecls.any (·.1.getId == nm)
    if k == ``srvDbClause then
      let aliasRaw := c.getArg 1; let aliasId : Ident := if aliasRaw.isIdent then ⟨aliasRaw⟩ else mkIdentFrom aliasRaw `auth
      let refId : Ident := ⟨c.getArg 3⟩
      if hasDecl aliasId.getId then throwErrorAt aliasId s!"duplicate declaration `{aliasId.getId}` in `{blockKind} {srvName}`"
      let (env, currNs, openDecls) := (← getEnv, ← getCurrNamespace, ← getOpenDecls)
      if let some dbInfo := Qed.Server.lookupDatabase? env currNs openDecls refId.getId then dbDecls := dbDecls.push (aliasId, dbInfo)
      else if let some svcInfo := Qed.Server.lookupService? env currNs openDecls refId.getId then serviceDecls := serviceDecls.push (aliasId, svcInfo)
      else if !isService then
        if let some authInfo := Qed.Server.lookupAuth? env currNs openDecls refId.getId then
          if authDecl?.isSome then throwErrorAt refId s!"`server {srvName}` can declare at most one `use ... : <auth>` provider"
          authDecl? := some (aliasId, authInfo)
        else if (Qed.Diag.lookupNameMapExt? Qed.Server.failedServiceRegistry env currNs openDecls refId.getId).isSome then
          throwErrorAt refId s!"referenced `service {refId.getId}` failed to elaborate earlier"
        else throwErrorAt refId s!"unknown `database`, `service`, or `auth` `{refId.getId}` in `use {aliasId.getId} : {refId.getId}`"
      else if (Qed.Diag.lookupNameMapExt? Qed.Server.failedServiceRegistry env currNs openDecls refId.getId).isSome then
        throwErrorAt refId s!"referenced `service {refId.getId}` failed to elaborate earlier"
      else throwErrorAt refId s!"unknown `database` or `service` `{refId.getId}` in `use {aliasId.getId} : {refId.getId}` (`service` blocks cannot bind `auth` directly; pass `ctx` or user values instead)"
    else if k == ``srvEnvClause then
      let id : Ident := ⟨c.getArg 1⟩; let osKey := (⟨c.getArg 3⟩ : TSyntax `str).getString
      let def? := if (c.getArg 4).getNumArgs == 2 then some (⟨(c.getArg 4).getArg 1⟩ : TSyntax `str).getString else none
      if hasDecl id.getId then throwErrorAt id s!"duplicate declaration `{id.getId}` in `{blockKind} {srvName}`"
      envDecls := envDecls.push { ident := id, osKey, default? := def?, isSecret := false }
    else if k == ``srvSecretClause then
      let id : Ident := ⟨c.getArg 1⟩; let osKey := (⟨c.getArg 3⟩ : TSyntax `str).getString
      unless isValidEnvVarName osKey do throwErrorAt (c.getArg 3) s!"invalid secret environment variable name `{osKey}`: must be non-empty and contain only ASCII letters, digits, or `_`"
      if hasDecl id.getId then throwErrorAt id s!"duplicate declaration `{id.getId}` in `{blockKind} {srvName}`"
      envDecls := envDecls.push { ident := id, osKey, default? := none, isSecret := true }
    else if k == ``srvHelperFnClause then helperClauses := helperClauses.push rawC
    else if k == ``srvInvNoSecretsClause then
      let nameId : Ident := ⟨c.getArg 1⟩
      if seenInvNames.contains nameId.getId then throwErrorAt nameId s!"duplicate invariant `{nameId.getId}` in `{blockKind} {srvName}`"
      seenInvNames := seenInvNames.push nameId.getId
      noSecretsInvs := noSecretsInvs.push nameId
    else if k == ``srvExampleClause then exampleClauses := exampleClauses.push rawC
    else if isService then
      throwErrorAt c s!"only `use`, `env`, `secret`, `fn`, `example`, and `invariant ... : no_required_secrets` declarations are allowed in stateless `service {srvName}`"
    else if k == ``srvInvRoutesAuthClause then
      let nameId : Ident := ⟨c.getArg 1⟩
      if seenInvNames.contains nameId.getId then throwErrorAt nameId s!"duplicate invariant `{nameId.getId}` in `server {srvName}`"
      seenInvNames := seenInvNames.push nameId.getId
      let pfxStr := (⟨c.getArg 4⟩ : TSyntax `str).getString
      let excOpt := c.getArg 5
      let excs := if excOpt.getNumArgs == 4 then (excOpt.getArg 2).getSepArgs.map fun s => (⟨s⟩ : TSyntax `str).getString else #[]
      routesAuthInvs := routesAuthInvs.push (nameId, pfxStr, excs)
    else if k == ``srvInvRpcsAuthClause then
      let nameId : Ident := ⟨c.getArg 1⟩
      if seenInvNames.contains nameId.getId then throwErrorAt nameId s!"duplicate invariant `{nameId.getId}` in `server {srvName}`"
      seenInvNames := seenInvNames.push nameId.getId
      let excOpt := c.getArg 4
      let excs := if excOpt.getNumArgs == 4 then (excOpt.getArg 2).getSepArgs.map fun s => (⟨s⟩ : TSyntax `str).getString else #[]
      rpcsAuthInvs := rpcsAuthInvs.push (nameId, excs)
    else if k == ``srvStateClause then
      let id : Ident := ⟨c.getArg 1⟩; let ty ← liftMacroM <| lowerSrvType (c.getArg 3) false s!"state field `{id.getId}`"
      if hasDecl id.getId then throwErrorAt id s!"duplicate declaration `{id.getId}` in `server {srvName}`"
      let (initStx?, defaultTerm?) ← if (c.getArg 4).getNumArgs == 2 then pure (some ((c.getArg 4).getArg 1), none)
        else match ← liftMacroM (inferQedTypeDefault? (c.getArg 3)) with | some dt => pure (none, some dt) | none => throwErrorAt id s!"state field `{id.getId}` requires an initial value `= ...`"
      stateDecls := stateDecls.push (id, ty.term, initStx?, defaultTerm?)
    else if k == ``srvInvMutatingClause || k == ``srvInvClause then
      let nameId : Ident := ⟨c.getArg 1⟩
      if seenInvNames.contains nameId.getId then throwErrorAt nameId s!"duplicate invariant `{nameId.getId}` in `server {srvName}`"
      seenInvNames := seenInvNames.push nameId.getId
      if k == ``srvInvMutatingClause then mutInvs := mutInvs.push (⟨c.getArg 4⟩, c.getArg 6, s!"mutating:{nameId.getId}")
      else for e in (c.getArg 3).getSepArgs do invs := invs.push (e, exprCallsOld e, nameId.getId.toString)
    else if k == ``srvBeforeClause then
      if beforeClause?.isSome then throwErrorAt c s!"duplicate `before` middleware in `server {srvName}`"
      beforeClause? := some c
    else if k == ``srvFnClause then fnClauses := fnClauses.push rawC
    else if k == ``srvChannelClause then chanClauses := chanClauses.push c
    else if k == ``srvHttpRouteClause || k == ``srvStreamClause then httpClauses := httpClauses.push c
    else if k == ``srvJobClause then jobClauses := jobClauses.push c
    else if k == ``srvOnCreateAccountClause then
      if onCreateAccountClause?.isSome then throwErrorAt c s!"duplicate `onCreateAccount` hook in `server {srvName}`"
      onCreateAccountClause? := some c
    else if k == ``srvOnSignInClause then
      if onSignInClause?.isSome then throwErrorAt c s!"duplicate `onSignIn` hook in `server {srvName}`"
      onSignInClause? := some c
    else throwErrorAt c "unexpected clause in `server` block"
  if isService then
    if helperClauses.isEmpty then throwErrorAt srvIdent s!"`service {srvName}` must declare at least one `fn`"
    return { dbDecls, serviceDecls, authDecl? := none, envDecls, stateDecls := #[], mutInvs := #[], invs := #[], helperClauses, fnClauses := #[], chanClauses := #[], noSecretsInvs, exampleClauses }
  for (hookNm, hook?) in #[("onCreateAccount", onCreateAccountClause?), ("onSignIn", onSignInClause?)] do
    if let some c := hook? then if authDecl?.isNone then throwErrorAt c s!"`{hookNm}` in `server {srvName}` requires `use auth : <Auth>`"
  if fnClauses.isEmpty && chanClauses.isEmpty && httpClauses.isEmpty && jobClauses.isEmpty && onCreateAccountClause?.isNone && onSignInClause?.isNone then
    throwErrorAt srvIdent s!"`server {srvName}` must declare at least one `rpc`, `channel`, `http`, `stream`, `every` job, or auth hook"
  if stateDecls.isEmpty && (!invs.isEmpty || !mutInvs.isEmpty) then throwErrorAt srvIdent s!"`server {srvName}` declares `invariant`s but has no `state` fields"
  for (fldId, _, _) in mutInvs do
    unless stateDecls.any (·.1.getId == fldId.getId) do
      throwErrorAt fldId s!"`invariant mutating {fldId.getId}` does not match any `state` field of `{srvName}` (`state` fields: {String.intercalate ", " (stateDecls.toList.map fun s => s!"`{s.1.getId}`")})"
  return { dbDecls, serviceDecls, authDecl?, envDecls, stateDecls, mutInvs, invs, helperClauses, beforeClause?, fnClauses, chanClauses, httpClauses, jobClauses, onCreateAccountClause?, onSignInClause?, routesAuthInvs, rpcsAuthInvs, noSecretsInvs, exampleClauses }

partial def scanCtxEnv (envVars locals : Array String) (stx : Syntax) : Bool × Bool :=
  let k := stx.getKind
  if k == ``qedIdent then
    match (stx.getArg 0).getId.components with
    | root :: _ => let r := root.toString; if locals.contains r then (false, false) else (r == "ctx", envVars.contains r)
    | [] => (false, false)
  else if k == ``qedProj then scanCtxEnv envVars locals (stx.getArg 0)
  else if k == ``qedLam1 then scanCtxEnv envVars (locals ++ if (stx.getArg 0).isIdent then #[(stx.getArg 0).getId.toString] else #[]) (stx.getArg 2)
  else if k == ``qedLamN then scanCtxEnv envVars (locals ++ (stx.getArg 1).getSepArgs.filterMap fun b => if b.isIdent then some b.getId.toString else none) (stx.getArg 4)
  else if k == ``qedAllIn || k == ``qedAnyIn then
    let (c1, e1) := scanCtxEnv envVars locals (stx.getArg 3); let (c2, e2) := scanCtxEnv envVars (locals.push (stx.getArg 1).getId.toString) (stx.getArg 5); (c1 || c2, e1 || e2)
  else if k == ``qedAllVars then scanCtxEnv envVars (locals ++ (stx.getArg 1).getSepArgs.map fun b => (qedAllVarIdent b).getId.toString) (stx.getArg 3)
  else stx.getArgs.foldl (fun (ac, ae) ch => let (c, e) := scanCtxEnv envVars locals ch; (ac || c, ae || e)) (false, false)

def isAuthReqLabel (s : String) : Bool := s.contains "ctx.userId" || s.contains "ctx.isAuthenticated" || s.contains "ctx.bearerToken"

@[noinline]
def wrapReqs (reqProps : Array Term) (reqHIds : Array Ident) (reqLbls : Array String) (inner : Term) (pureWrap : Bool := true) : CommandElabM Term := do
  let mut g := inner
  for revIdx in [0:reqProps.size] do
    let ri := reqProps.size - 1 - revIdx; let rLbl := reqLbls[ri]!; let rMsg := Syntax.mkStrLit s!"precondition failed: {rLbl}"
    let errCtor : Term ←
      if isAuthReqLabel rLbl then `(Qed.Server.ApiError.unauthorized $rMsg)
      else if rLbl.contains "ctx.hasClaim" || rLbl.contains "ctx.claim" || rLbl.contains "ctx.isSession" || rLbl.contains "ctx.authMethod" || rLbl.contains "emailVerified" then
        `(Qed.Server.ApiError.forbidden $rMsg)
      else `(Qed.Server.ApiError.badRequest $rMsg)
    let errTerm ← if pureWrap then `(Pure.pure (Except.error $errCtor)) else `(Except.error $errCtor)
    g ← `(if $(reqHIds[ri]!):ident : $(reqProps[ri]!) then $g else $errTerm)
  return g

structure LoweredAuthBind where
  binderId   : Lean.Ident
  binderName : String
  extraIds   : Array Lean.Ident
  extraTys   : Array Lean.Term
  authInfo?  : Option AuthInfo

structure LoweredRequires where
  authBind?       : Option LoweredAuthBind := none
  reqPropTerms    : Array Term
  reqHypIds       : Array Ident
  reqLabels       : Array String
  requiresAuth    : Bool
  clientReqId?    : Option Ident
  clientReqConst? : Option Name
  clientReqLabel  : String

def LoweredRequires.allBinderIds (r : LoweredRequires) : Array Ident :=
  (r.authBind?.map (·.extraIds) |>.getD #[]) ++ r.reqHypIds
def LoweredRequires.allBinderTys (r : LoweredRequires) : Array Term :=
  (r.authBind?.map (·.extraTys) |>.getD #[]) ++ r.reqPropTerms
def LoweredRequires.allBinderArgs (r : LoweredRequires) : Array Term :=
  r.allBinderIds.map (⟨·.raw⟩)
def LoweredRequires.extraLocals (r : LoweredRequires) : Array String :=
  r.authBind?.map (fun ab => #[ab.binderName]) |>.getD #[]

@[noinline]
def wrapAuthAndReqs (reqs : LoweredRequires) (inner : Term) (pureWrap : Bool := true) : CommandElabM Term := do
  let body ← wrapReqs reqs.reqPropTerms reqs.reqHypIds reqs.reqLabels inner pureWrap
  let some ab := reqs.authBind? | return body
  let ctxId := mkIdent `ctx
  let errTerm (msg : String) : CommandElabM Term := do
    let e ← `(Qed.Server.ApiError.unauthorized $(Syntax.mkStrLit msg))
    if pureWrap then `(Pure.pure (Except.error $e)) else `(Except.error $e)
  let unauthErr ← errTerm "authentication required"
  let badLenErr ← errTerm "invalid user id length"
  let uId := ab.binderId; let hEq := ab.extraIds[1]!; let hNe := ab.extraIds[2]!; let hLen := ab.extraIds[3]!
  let uidExpr : Term ← if ab.authInfo?.isSome then `(($uId).id) else pure ⟨uId.raw⟩
  let lenGuarded ← `(if $hLen:ident : 1 ≤ ($uidExpr).length ∧ ($uidExpr).length ≤ 128 then $body else $badLenErr)
  match ab.authInfo? with
  | some authInfo =>
      let hFrom := mkIdent `_hFromCtx
      let fromCtxId := mkIdentFrom uId (authInfo.authName ++ `fromCtx)
      let fromCtxUidId := mkIdentFrom uId (authInfo.authName ++ `fromCtx_userId)
      `(match $hFrom:ident : $fromCtxId $ctxId with
        | Option.none => $unauthErr
        | Option.some $uId:ident =>
            have $hEq:ident : Option.some (($uId).id) = ($ctxId).userId := $fromCtxUidId $ctxId $uId $hFrom
            have $hNe:ident : ($ctxId).userId ≠ Option.none := (by intro _hN; rw [_hN] at $hEq:ident; cases $hEq:ident)
            $lenGuarded)
  | none =>
      let hUid := mkIdent `_hUidCtx
      `(match $hUid:ident : ($ctxId).userId with
        | Option.none => $unauthErr
        | Option.some $uId:ident =>
            have $hEq:ident : Option.some $uId = ($ctxId).userId := ($hUid).symm
            have $hNe:ident : ($ctxId).userId ≠ Option.none := (by rw [$hUid:ident]; simp)
            $lenGuarded)

private def matchAuthRequireExpr? (stx : Syntax) (hasAuthDecl : Bool) : CommandElabM (Option Ident) := do
  let u := unwrapParens1 stx
  if u.getKind == ``qedIdent && (u.getArg 0).getId.eraseMacroScopes == `auth then
    return some (mkIdentFrom u (if hasAuthDecl then `user else `uid))
  else if u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId.eraseMacroScopes == `auth then
    let args := (u.getArg 2).getSepArgs
    if args.size == 1 && args[0]!.getKind == ``qedCallArgPos then
      let a := unwrapParens1 (args[0]!.getArg 0)
      if a.getKind == ``qedIdent && (a.getArg 0).getId.eraseMacroScopes.isAtomic then
        return some ⟨a.getArg 0⟩
    throwErrorAt stx "`requires auth(...)` expects a single identifier binder (e.g. `requires auth(user)`)"
  return none

@[noinline]
def elabRequiresClauses (refIdent : Ident) (itemName : Name) (fnLabel hypPrefix reqSuffix : String)
    (serverLocals clientLocals : Array String) (clientBindIds : Array Ident) (clientBindTys : Array Term)
    (reqExprs : Array Syntax) (excludedClientVars : Array String := #[]) (trackAuth : Bool := true) : SrvElabM LoweredRequires := do
  let c ← read
  let mut authBind? : Option LoweredAuthBind := none
  let mut filteredReqs : Array Syntax := #[]
  for rExpr in reqExprs do
    if let some uId ← liftM <| matchAuthRequireExpr? rExpr c.authDecl?.isSome then
      if authBind?.isSome then throwErrorAt rExpr s!"duplicate `requires auth` in `{fnLabel}`"
      let uStr ← checkSrvParamName s!"`requires auth` in `{fnLabel}`" uId (extraShadow := serverLocals)
      let (hEq, hNe, hLen) := (mkIdent (Name.mkSimple s!"{hypPrefix}_authEq"), mkIdent (Name.mkSimple s!"{hypPrefix}_authNe"), mkIdent (Name.mkSimple s!"{hypPrefix}_authLen"))
      let extraIds := #[uId, hEq, hNe, hLen]
      let (uTy, uidExpr) : Term × Term ← match c.authDecl? with
        | some (_, ai) => pure (← `($(mkIdentFrom uId (ai.authName ++ `User))), ← `(($uId).id))
        | none => pure (← `(String), ⟨uId.raw⟩)
      let extraTys : Array Term := #[uTy, ← `(Option.some $uidExpr = ($(c.ctxId)).userId),
        ← `(($(c.ctxId)).userId ≠ Option.none), ← `(1 ≤ ($uidExpr).length ∧ ($uidExpr).length ≤ 128)]
      authBind? := some { binderId := uId, binderName := uStr, extraIds, extraTys, authInfo? := c.authDecl?.map Prod.snd }
    else filteredReqs := filteredReqs.push rExpr
  let serverLocals' := match authBind? with | some ab => serverLocals.push ab.binderName | none => serverLocals
  let excludedClientVars' := match authBind? with | some ab => excludedClientVars.push ab.binderName | none => excludedClientVars
  let mut reqPropTerms : Array Term := #[]; let mut reqHypIds : Array Ident := #[]; let mut reqLabels : Array String := #[]
  let mut clientReqProps : Array Term := #[]; let mut clientReqLabels : Array String := #[]; let mut requiresAuth := authBind?.isSome
  for (rExpr, idx) in filteredReqs.zipIdx do
    if exprHasAwait rExpr then throwErrorAt rExpr "`requires` precondition cannot contain `await`"
    let (pTerm, rSt) ← liftM <| (lowerExpr { fnName := fnLabel, stateFields := c.stateFieldNames, envVars := c.envVarNames, envIdents := c.envIdents, locals := serverLocals', stateRule := .forbidInRequires } .propGuard rExpr).run {}
    recordSrvExtRoots rSt.extRoots
    reqPropTerms := reqPropTerms.push pTerm; reqHypIds := reqHypIds.push (mkIdent (Name.mkSimple s!"{hypPrefix}{idx}"))
    reqLabels := reqLabels.push ((rExpr.reprint.getD "requires").trimAscii.toString)
    for conj in splitAndStx rExpr do
      let (mentionsCtx, mentionsEnv) := scanCtxEnv c.envVarNames serverLocals' conj
      let mentionsAuthVar := match authBind? with | some ab => (scanCtxEnv #[ab.binderName] clientLocals conj).2 | none => false
      if trackAuth && (mentionsCtx || mentionsAuthVar) && !mentionsEnv && (isAuthReqLabel (conj.reprint.getD "") || (conj.reprint.getD "").contains "ctx.isSession") then requiresAuth := true
      else if !mentionsCtx && !mentionsEnv && !mentionsAuthVar && (excludedClientVars'.isEmpty || !(scanCtxEnv excludedClientVars' clientLocals conj).2) then
        clientReqProps := clientReqProps.push (← lowerSrvExpr { fnName := fnLabel, stateFields := c.stateFieldNames, locals := clientLocals, stateRule := .forbidInRequires, forbidCtxEnv := true } .propInv conj)
        clientReqLabels := clientReqLabels.push ((conj.reprint.getD "requires").trimAscii.toString)
  let (clientReqId?, clientReqConst?) ← if clientReqProps.isEmpty then pure (none, none) else do
    let leaf := itemName.appendAfter reqSuffix; let cid := c.subId leaf refIdent
    let reqConj ← Qed.mkConjBody clientReqProps (ascribeProp := false)
    elabSrvCmd (← `(command| set_option linter.unusedVariables false in @[simp] abbrev $cid $[($clientBindIds:ident : $clientBindTys:term)]* : Prop := $reqConj))
    pure (some cid, some (c.fullSrvName ++ leaf))
  return { authBind?, reqPropTerms, reqHypIds, reqLabels, requiresAuth, clientReqId?, clientReqConst?, clientReqLabel := String.intercalate " && " clientReqLabels.toList }

@[noinline]
def elabEnsuresAbbrev (ownerIdent : Ident) (fnLabel : String) (binderName : Name)
    (paramNames : Array String) (pIdents : Array Ident) (pTyTerms : Array Term) (resTyTerm : Term) (ensExprs : Array Syntax) :
    SrvElabM (Option (Option (Ident × Name × String))) := do
  if ensExprs.isEmpty then return some none
  let c ← read
  let ensCtx : LowerCtx := { fnName := fnLabel, stateFields := c.stateFieldNames, envVars := c.envVarNames, locals := paramNames.push binderName.toString, stateRule := .forbidInEnsures, forbidCtxEnv := true }
  let ensProps ← ensExprs.mapM fun e => do
    if exprHasAwait e then throwErrorAt e "`ensures` postcondition cannot contain `await`"
    lowerSrvExpr ensCtx .propInv e
  let leaf := ownerIdent.getId.appendAfter "_ens"; let ensId := c.subId leaf ownerIdent
  let ensConj ← Qed.mkConjBody ensProps (ascribeProp := false)
  elabSrvCmd (← `(command| set_option linter.unusedVariables false in @[simp] abbrev $ensId $[($pIdents:ident : $pTyTerms:term)]* ($(mkIdent binderName):ident : $resTyTerm) : Prop := $ensConj))
  if (← hasSrvErrors) then return none
  return some (some (ensId, c.fullSrvName ++ leaf, String.intercalate " && " (ensExprs.toList.map fun e => (e.reprint.getD "ensures").trimAscii.toString)))

private partial def scanFailCallsAux (stx : Syntax) (tags : Array Ident) (hasPlain : Bool) : CommandElabM (Array Ident × Bool) := do
  if stx.getKind == ``qedCall && (stx.getArg 0).getKind == ``qedIdent && ((stx.getArg 0).getArg 0).getId == `fail then
    let rawArgs := (stx.getArg 2).getSepArgs
    if (rawArgs.size == 1 || rawArgs.size == 2) && (unwrapParens1 rawArgs[0]![0]).getKind == ``qedDotIdent then
      let tagId : Ident := ⟨(unwrapParens1 rawArgs[0]![0])[1]⟩
      let tags' := if tags.any (·.getId == tagId.getId) then tags else tags.push tagId
      if rawArgs.size == 2 then scanFailCallsAux rawArgs[1]! tags' hasPlain else return (tags', hasPlain)
    else rawArgs.foldlM (init := (tags, true)) fun (t, p) a => scanFailCallsAux a t p
  else stx.getArgs.foldlM (init := (tags, hasPlain)) fun (t, p) ch => scanFailCallsAux ch t p

def scanBodyFailTags (stmts : Array Syntax) : CommandElabM (Array Ident × Bool) := stmts.foldlM (init := (#[], false)) fun (t, p) st => scanFailCallsAux st t p

private def mkDotTerm (tid : Ident) : Term := ⟨Syntax.node (.fromRef tid) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef tid) ".", tid]⟩

@[noinline]
private def elabDomJsonInsts (errTypeId : Ident) (tagIdents : Array Ident) : CommandElabM Unit := do
  let toStrAlts ← tagIdents.mapM fun tid => `(Lean.Parser.Term.matchAltExpr| | $(mkDotTerm tid) => $(Syntax.mkStrLit tid.getId.toString))
  let fromJsonAlts := (← tagIdents.mapM fun tid => `(Lean.Parser.Term.matchAltExpr| | Qed.Json.str $(Syntax.mkStrLit tid.getId.toString) => Except.ok $(mkDotTerm tid))).push
    (← `(Lean.Parser.Term.matchAltExpr| | _ => Except.error "invalid RPC error tag"))
  let cmds : Array Syntax := #[
    ← `(command| instance : ToString $errTypeId where toString e := match e with $[$toStrAlts:matchAlt]*),
    ← `(command| instance : Qed.ToJson $errTypeId := ⟨fun e => Qed.Json.str (toString e)⟩),
    ← `(command| instance : Qed.FromJson $errTypeId where fromJson j := match j with $[$fromJsonAlts:matchAlt]*),
    ← `(command| instance : Qed.LawfulJson $errTypeId where depthBound := 0; depth_toJson _ := Nat.le_refl 0; fromJson_toJson e := by cases e <;> rfl),
    ← `(command| instance : Qed.NonNullJson $errTypeId := ⟨nofun⟩)]
  for cmd in cmds do elabCommand cmd

@[noinline]
private def elabDomProtoInsts (errTypeId : Ident) (tagIdents : Array Ident) : CommandElabM Unit := do
  let toProtoAlts ← tagIdents.zipIdx.mapM fun (tid, i) => `(Lean.Parser.Term.matchAltExpr| | $(mkDotTerm tid) => Qed.Proto.WireVal.varint $(Syntax.mkNumLit (toString i)))
  let fromProtoAlts := (← tagIdents.zipIdx.mapM fun (tid, i) => `(Lean.Parser.Term.matchAltExpr| | Qed.Proto.WireVal.varint $(Syntax.mkNumLit (toString i)) => Except.ok $(mkDotTerm tid))).push
    (← `(Lean.Parser.Term.matchAltExpr| | _ => Except.error "protobuf: invalid RPC error tag"))
  let cmds : Array Syntax := #[
    ← `(command| instance : Qed.ToProto $errTypeId where toProtoVal e := match e with $[$toProtoAlts:matchAlt]*),
    ← `(command| instance : Qed.FromProto $errTypeId where fromProtoVal w := match w with $[$fromProtoAlts:matchAlt]*),
    ← `(command| instance : Qed.LawfulProto $errTypeId := Qed.LawfulProto.ofScalar (by intro e; cases e <;> rfl))]
  for cmd in cmds do elabCommand cmd

@[noinline]
def elabDomainErrorType (fnIdent : Ident) (tagIdents : Array Ident) : SrvElabM Ident := do
  let c ← read; let errTypeId := c.subId (fnIdent.getId ++ `Error) fnIdent
  let ctors ← tagIdents.mapM fun tid => `(Lean.Parser.Command.ctor| | $tid:ident)
  elabSrvCmd (← `(command| inductive $errTypeId where $[$ctors:ctor]* deriving Inhabited, DecidableEq, Repr))
  liftM <| elabDomJsonInsts errTypeId tagIdents
  liftM <| elabDomProtoInsts errTypeId tagIdents
  return errTypeId

def collectServerSecretsAndExts :
    SrvElabM (Array String × Array String × Array (String × String) × Array Name × Array (String × String × Option String)) := do
  let c ← read; let (env, currNs, openDecls) := (← getEnv, ← getCurrNamespace, ← getOpenDecls)
  let mut reqSecrets : Array String := #[]; let mut ownSecrets : Array String := #[]
  let mut allDbs : Array Name := c.dbDecls.map (·.2.configConst)
  let mut allEnvs : Array (String × String × Option String) := c.envDecls.map fun e => (e.ident.getId.toString, e.osKey, e.default?)
  for (_, dbi) in c.dbDecls do
    let es := dbi.envSpecs
    if !dbi.hasDevFallback && es.prod == es.staging && es.prod == es.preview then reqSecrets := dbi.secrets.foldl pushUnique reqSecrets
  for e in c.envDecls do
    if e.default?.isNone then reqSecrets := pushUnique reqSecrets e.osKey; ownSecrets := pushUnique ownSecrets e.osKey
  if let some (_, ai) := c.authDecl? then if !ai.spec.isManaged then reqSecrets := ai.secrets.foldl pushUnique reqSecrets
  let mut usedExts : Array (String × String) := #[]
  let mergeSvc (si : ServiceInfo) (reqS ownS : Array String) (exts : Array (String × String)) (dbs : Array Name) (envs : Array (String × String × Option String)) :=
    let reqS' := si.secrets.foldl pushUnique reqS
    let ownS' := si.ownSecrets.foldl pushUnique ownS
    let exts' := si.externalServices.foldl (fun acc x => if acc.any (·.1 == x.1) then acc else acc.push x) exts
    let dbs' := si.databases.foldl pushUnique dbs
    let envs' := si.envVars.foldl (fun acc x => if acc.any (·.2.1 == x.2.1) then acc else acc.push x) envs
    (reqS', ownS', exts', dbs', envs')
  for (_, si) in c.serviceDecls do
    (reqSecrets, ownSecrets, usedExts, allDbs, allEnvs) := mergeSvc si reqSecrets ownSecrets usedExts allDbs allEnvs
  for root in ← c.extRootsRef.get do
    if let some extInfo := Qed.Diag.lookupNameMapExt? externalRegistry env currNs openDecls root then
      let sStr := root.toString
      unless usedExts.any (·.1 == sStr) do usedExts := usedExts.push (sStr, extInfo.baseOrigin)
      reqSecrets := extInfo.secrets.foldl pushUnique reqSecrets; ownSecrets := extInfo.secrets.foldl pushUnique ownSecrets
    else if let some svcInfo := lookupService? env currNs openDecls root then
      (reqSecrets, ownSecrets, usedExts, allDbs, allEnvs) := mergeSvc svcInfo reqSecrets ownSecrets usedExts allDbs allEnvs
  return (reqSecrets, ownSecrets, usedExts, allDbs, allEnvs)

@[noinline]
def wrapWithEnvDecls (envDecls : Array ParsedEnvDecl) (innerRun : Term) (innerProof? : Option Term := none) : CommandElabM (Term × Option Term) :=
  envDecls.foldrM (init := (innerRun, innerProof?)) fun e (accRun, accPf?) => do
    let eid := e.ident; let keyLit := Syntax.mkStrLit e.osKey
    if e.isSecret then
      let missingMsg := Syntax.mkStrLit s!"missing required secret `{e.osKey}`"
      let run' ← if accPf?.isSome then
          `(Qed.Server.MonadServer.readEnv $keyLit >>= fun _envOpt => match _envOpt with
            | some _secRaw => if _secRaw.isEmpty then Pure.pure (Except.error (Qed.Server.ApiError.internal $missingMsg))
                else (fun ($eid:ident : Qed.Secret) => $accRun) (Qed.Secret.ofString _secRaw)
            | none => Pure.pure (Except.error (Qed.Server.ApiError.internal $missingMsg)))
        else
          `(Qed.Server.MonadServer.readEnv $keyLit >>= fun _envOpt => match _envOpt with
            | some _secRaw => if _secRaw.isEmpty then Pure.pure (Except.error (Qed.Server.ApiError.internal $missingMsg))
                else let $eid:ident : Qed.Secret := Qed.Secret.ofString _secRaw; $accRun
            | none => Pure.pure (Except.error (Qed.Server.ApiError.internal $missingMsg)))
      let pf'? ← accPf?.mapM fun pf =>
        `(Qed.Server.ProgSpec.safeIO_bind (Qed.Server.MonadServer.readEnv $keyLit) fun _envOpt => match _envOpt with
          | some _secRaw => if _secRaw.isEmpty then Qed.Server.ProgSpec.pure_class _ trivial
              else (fun ($eid:ident : Qed.Secret) => $pf) (Qed.Secret.ofString _secRaw)
          | none => Qed.Server.ProgSpec.pure_class _ trivial)
      pure (run', pf'?)
    else match e.default? with
    | some defVal =>
        let defLit := Syntax.mkStrLit defVal
        let run' ← if accPf?.isSome then `(Qed.Server.MonadServer.readEnv $keyLit >>= fun _envOpt => (fun ($eid:ident : String) => $accRun) (_envOpt.getD $defLit))
          else `(Qed.Server.MonadServer.readEnv $keyLit >>= fun _envOpt => let $eid:ident : String := _envOpt.getD $defLit; $accRun)
        let pf'? ← accPf?.mapM fun pf => `(Qed.Server.ProgSpec.safeIO_bind (Qed.Server.MonadServer.readEnv $keyLit) fun _envOpt => (fun ($eid:ident : String) => $pf) (_envOpt.getD $defLit))
        pure (run', pf'?)
    | none =>
        let missingMsg := Syntax.mkStrLit s!"missing required environment variable `{e.osKey}`"
        let run' ← `(Qed.Server.MonadServer.readEnv $keyLit >>= fun _envOpt => match _envOpt with | some $eid:ident => $accRun | none => Pure.pure (Except.error (Qed.Server.ApiError.internal $missingMsg)))
        let pf'? ← accPf?.mapM fun pf => `(Qed.Server.ProgSpec.safeIO_bind (Qed.Server.MonadServer.readEnv $keyLit) fun _envOpt => match _envOpt with | some $eid:ident => $pf | none => Qed.Server.ProgSpec.pure_class _ trivial)
        pure (run', pf'?)

@[noinline]
private def elabDispatchDef (defLeaf : Name) (atomicBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (paramIds : Array Ident) (paramTys : Array Term) (retTy bodyTerm : Term) : SrvElabM Unit := do
  let c ← read; let fullBody := (← liftM <| wrapWithEnvDecls c.envDecls bodyTerm).1; let defId := c.subId defLeaf
  elabSrvCmd (← `(command|
    set_option linter.unusedVariables false in
    def $defId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m] $[$atomicBinders:bracketedBinder]* ($(c.ctxId):ident : Qed.Server.RequestCtx) $[($paramIds:ident : $paramTys:term)]* :
        m (Except Qed.Server.ApiError $retTy) := $fullBody))

@[noinline]
private def elabServerMetaCmds (methodInfos : Array ServerMethodInfo) (chanNames reqSecrets : Array String) : SrvElabM Unit := do
  let c ← read
  if c.hasState then
    let (linId, initId, invInitId) := (c.subId `concurrent_linearizable, c.subId `initState, c.subId `inv_init)
    elabSrvCmd (← `(command|
      theorem $linId {Out : Type} (st : Qed.Server.MultiCoreState $(c.stateId) Out) (hsched : Qed.Server.MultiCoreSchedule $(c.stateInvId) ⟨$initId, []⟩ st) :
          $(c.stateInvId) st.shared := Qed.Server.concurrent_schedule_preserves_inv $(c.stateInvId) $initId st $invInitId hsched))
  let mkLits (ss : Array String) : Array Term := ss.map (Syntax.mkStrLit ·)
  let (secId, mrkId, roId, mthId, chId) := (c.subId `secrets, c.subId `_qed_server_marker, c.subId `readOnlyMethods, c.subId `methods, c.subId `channels)
  elabSrvCmds #[
    ← `(command| @[noinline] def $secId : Array String := #[$(mkLits reqSecrets),*]),
    ← `(command| theorem $mrkId : True := True.intro),
    ← `(command| @[noinline] def $roId : Array String := #[$(mkLits ((methodInfos.filter (·.isReadOnly)).map (·.name))),*]),
    ← `(command| @[noinline] def $mthId : List String := [$(mkLits (methodInfos.map (·.name))),*]),
    ← `(command| @[noinline] def $chId : List String := [$(mkLits chanNames),*])]

@[noinline]
private def elabServerAuthHookDispatch (atomicBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (authInfo : AuthInfo) (onCreateRun? onSignInRun? : Option Term) : SrvElabM Unit := do
  let c ← read; let (hookKindVar, authUserVar, hFromCtxVar, hAuthId, hAuthEqId) := (mkIdent `hookKind, mkIdent `_authUser, mkIdent `_hFromCtx, mkIdent `_hAuth, mkIdent `_hAuthEq)
  let emptyOk ← `(Pure.pure (Except.ok ()))
  elabDispatchDef `authHookM atomicBinders #[hookKindVar] #[← `(UInt8)] (← `(Unit)) (← `(
    match $hFromCtxVar:ident : $(mkIdentFrom c.srvIdent (authInfo.authName ++ `fromCtx)) $(c.ctxId) with
    | Option.none => Pure.pure (Except.error (Qed.Server.ApiError.unauthorized "missing authenticated user"))
    | Option.some $authUserVar:ident =>
        have $hAuthEqId:ident : Option.some (($authUserVar).id) = ($(c.ctxId)).userId := $(mkIdentFrom c.srvIdent (authInfo.authName ++ `fromCtx_userId)) $(c.ctxId) $authUserVar $hFromCtxVar
        have $hAuthId:ident : ($(c.ctxId)).userId ≠ Option.none := by intro _hNone; rw [_hNone] at $hAuthEqId:ident; cases $hAuthEqId:ident
        match $hookKindVar:ident with | (0 : UInt8) => $(onCreateRun?.getD emptyOk) | (1 : UInt8) => $(onSignInRun?.getD emptyOk) | _ => Pure.pure (Except.ok ())))

@[noinline]
def elabServerDispatchCmds (methodInfos : Array ServerMethodInfo) (dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (chanNames : Array String) (wsDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (wsProjectArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[])
    (httpDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[]) (jobNames : Array String := #[])
    (onCreateRun? : Option Term := none) (onSignInRun? : Option Term := none) : SrvElabM Unit := do
  let c ← read; let (reqSecrets, ownSecrets, usedExts, allDbs, allEnvs) ← collectServerSecretsAndExts
  elabServerMetaCmds methodInfos chanNames reqSecrets
  let atomicBinders ← liftM c.atomicBinders; let (strTy, bytesTy, u8Ty) := (← `(String), ← `(ByteArray), ← `(UInt8))
  let methodVar := mkIdent `method
  elabDispatchDef `dispatchM atomicBinders #[methodVar, mkIdent `reqBytes] #[strTy, bytesTy] bytesTy
    (← `(match $methodVar:ident with $[$(dispatchArms.push (← `(Lean.Parser.Term.matchAltExpr| | _ => Pure.pure (Except.error (Qed.Server.ApiError.notFound ("unknown RPC method: " ++ $methodVar)))))):matchAlt]*))
  if !chanNames.isEmpty then
    let (wsKindVar, wsChanVar, wsParamsVar, wsPayloadVar) := (mkIdent `wsKind, mkIdent `wsChannel, mkIdent `wsParams, mkIdent `wsPayload)
    elabDispatchDef `wsDispatchM atomicBinders #[wsKindVar, wsChanVar, wsParamsVar, wsPayloadVar] #[u8Ty, strTy, bytesTy, bytesTy] bytesTy
      (← `(match $wsKindVar:ident, $wsChanVar:ident with $[$(wsDispatchArms.push (← `(Lean.Parser.Term.matchAltExpr| | _, _ => Pure.pure (Except.error (Qed.Server.ApiError.notFound ("unknown WebSocket channel: " ++ $wsChanVar)))))):matchAlt]*))
  if !wsProjectArms.isEmpty then
    let (wsChanVar, wsParamsVar, wsPayloadVar) := (mkIdent `wsChannel, mkIdent `wsParams, mkIdent `wsPayload)
    let fallback ← `(Lean.Parser.Term.matchAltExpr| | _ => Qed.Server.WsProjectOut.passthrough)
    elabSrvCmd (← `(command|
      set_option linter.unusedVariables false in
      @[noinline] def $(c.subId `wsProject) ($(c.ctxId):ident : Qed.Server.RequestCtx) ($wsChanVar:ident : String) ($wsParamsVar:ident : ByteArray) ($wsPayloadVar:ident : ByteArray) : Qed.Server.WsProjectOut :=
        match $wsChanVar:ident with $[$(wsProjectArms.push fallback):matchAlt]*))
  if !httpDispatchArms.isEmpty then
    let (httpMethodVar, httpPathVar) := (mkIdent `httpMethod, mkIdent `httpPath)
    elabDispatchDef `httpDispatchM atomicBinders #[httpMethodVar, httpPathVar] #[strTy, strTy] (← `(Option Qed.Server.HttpResponse))
      (← `(match $httpMethodVar:ident, $httpPathVar:ident with $[$(httpDispatchArms.push (← `(Lean.Parser.Term.matchAltExpr| | _, _ => Pure.pure (Except.ok none)))):matchAlt]*))
  if let some (_, ai) := c.authDecl? then if onCreateRun?.isSome || onSignInRun?.isSome then elabServerAuthHookDispatch atomicBinders ai onCreateRun? onSignInRun?
  modifyEnv fun env => serverRegistry.addEntry env {
    serverName := c.fullSrvName, shortName := c.srvName.toString, hasState := c.hasState, secrets := reqSecrets, ownSecrets,
    envVars := allEnvs, externalServices := usedExts,
    methods := methodInfos, channels := chanNames, jobs := jobNames, databases := allDbs,
    authName? := c.authDecl?.map (·.2.authName), authConfig? := c.authDecl?.map (·.2.configConst),
    hasOnCreateAccount := onCreateRun?.isSome, hasOnSignIn := onSignInRun?.isSome,
    hasHttpRoutes := !httpDispatchArms.isEmpty, hasWsProject := !wsProjectArms.isEmpty }

@[noinline]
def elabServerFnInvariants (isAsync : Bool) (fnStr : String) (fnIdent targetId : Ident)
    (allBinderIds : Array Ident) (allBinderTys : Array Term) (targetCall : Term) : SrvElabM Bool := do
  let c ← read; let fnLit := Syntax.mkStrLit fnStr
  let sOldId := mkIdent (if isAsync then `_sOld else `_s0); let sNewId := mkIdent `_sNew
  let emitStepRelInv (suffix lbl : String) (asyncRel pureGoal : Term) : SrvElabM Bool := do
    let thmId := c.fnSubId fnIdent suffix; let lblLit := Syntax.mkStrLit lbl
    let invUnfolds := #[c.stateInvId] ++ c.statefulHelperIds
    elabSrvCmd <| ← if isAsync then
      `(command| theorem $thmId $[($allBinderIds:ident : $allBinderTys:term)]* :
          Qed.Server.ProgPreservesStepRel $(c.stateInvId) (fun ($sOldId:ident $sNewId:ident : $(c.stateId)) => $asyncRel) ($targetCall : Qed.Server.ThreadProg $(c.stateId) _) := by
          qedSrvProveAsync $targetId [$[$invUnfolds],*] $fnLit $lblLit)
    else
      `(command| theorem $thmId ($sOldId:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]* (_hInv : $(c.stateInvId) $sOldId) : $pureGoal := by
          qedSrvProveStep [$(c.stateInvId), $targetId] $fnLit $lblLit)
    return !(← hasSrvErrors)
  let mut twoIdx := 0
  for (exprStx, isTwoSt, lbl) in c.invs do
    if isTwoSt then
      let relProp ← lowerSrvExpr { fnName := "invariant", stateFields := c.stateFieldNames, envVars := c.envVarNames, stateRule := .invariantProp sNewId sOldId false } .propInv exprStx
      unless (← emitStepRelInv s!"_twoInv{twoIdx}" lbl relProp (← `(Qed.Server.srvWithNewState (($targetCall).1) (fun ($sNewId:ident : $(c.stateId)) => $relProp)))) do return false
      twoIdx := twoIdx + 1
  for ((fldId, condStx, lbl), mutIdx) in c.mutInvs.zipIdx do
    let miProp ← lowerSrvExpr { fnName := fnStr, envVars := c.envVarNames } .propInv condStx
    unless (← emitStepRelInv s!"_mutInv{mutIdx}" lbl (← `(($sNewId).$fldId:ident = ($sOldId).$fldId:ident ∨ $miProp)) (← `((($targetCall).1).$fldId:ident = ($sOldId).$fldId:ident ∨ $miProp))) do return false
  return true

structure FnEnsSpec where
  ensId    : Ident
  postFn   : Term → CommandElabM Term
  labelStr : String
  tac?     : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq) := none

def mkStepEnsProofTac (unfoldIds : Array Ident) (fnLit : StrLit) (labelStr : String)
    (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : CommandElabM (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
  match tac? with
  | some ts => `(Lean.Parser.Tactic.tacticSeq| qedSrvPrepStep [$[$unfoldIds],*]; first | done | ($ts))
  | none    => `(Lean.Parser.Tactic.tacticSeq| qedSrvProveStep [$[$unfoldIds],*] $fnLit $(Syntax.mkStrLit s!"ensures: {labelStr}"))

def mkAsyncEnsProofTac (targetId : Ident) (unfoldIds : Array Ident) (fnLit : StrLit) (labelStr : String)
    (tac? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : CommandElabM (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
  match tac? with
  | some ts => `(Lean.Parser.Tactic.tacticSeq| qedSrvPrepAsyncEnsures $targetId [$[$unfoldIds],*]; first | done | ($ts))
  | none    => `(Lean.Parser.Tactic.tacticSeq| qedSrvProveAsyncEnsures $targetId [$[$unfoldIds],*] $fnLit $(Syntax.mkStrLit s!"ensures: {labelStr}"))

private def deferInvProofs (isA : Bool) (fnStr : String) (fnIdent targetId : Ident)
    (allBinderIds : Array Ident) (allBinderTys : Array Term) (targetCall : Term) (invCmd : Command) : SrvElabM Unit := do
  let c ← read
  deferSrvProof do
    elabCommand invCmd
    if hasNewErrors (← get).messages c.priorRep c.priorUnrep then return false
    (elabServerFnInvariants isA fnStr fnIdent targetId allBinderIds allBinderTys targetCall).run c

structure ElabHandlerRes where
  runExpr      : Term
  targetId     : Ident
  isAsync      : Bool
  allBinderIds : Array Ident
  allBinderTys : Array Term
  mutatesState : Bool
  dbWrite      : Bool
  hasEmit      : Bool
  hasCookieOp  : Bool := false

def ElabHandlerRes.isReadOnly (r : ElabHandlerRes) : Bool := !r.mutatesState && !r.dbWrite

@[noinline]
private def elabPureHandler (fnStr : String) (fnIdent invThmId : Ident) (fnLit singleInvLbl : StrLit)
    (allBinderIds : Array Ident) (allBinderTys callArgs : Array Term) (payloadTerm errTyTerm : Term)
    (baseCtx : LowerCtx) (bodyStmts : Array Syntax) (hasEmit : Bool) (ensSpec? : Option FnEnsSpec) : SrvElabM (Option ElabHandlerRes) := do
  let c ← read; let (s0Id, es0Id) := (mkIdent `_s0, mkIdent `_es0)
  let (pureBody, lSt) ← liftM <| (lowerPureBlock (if hasEmit then { baseCtx with emitAcc? := some es0Id } else baseCtx) false s0Id s0Id bodyStmts).run {}
  recordSrvExtRoots lSt.extRoots; let isReadOnly := lSt.mutated.isEmpty; let stepId := c.fnSubId fnIdent "_step"
  let (stepRetTy, stepBody) ← if hasEmit then
      pure (← `($(c.stateId) × (Except $errTyTerm $payloadTerm × List Qed.Server.WsEmit)), ← `(Qed.Server.srvFinishEmit $s0Id (let $es0Id:ident : List Qed.Server.WsEmit := []; $pureBody)))
    else pure (← `($(c.stateId) × Except $errTyTerm $payloadTerm), ← `(Qed.Server.srvFinish $s0Id $pureBody))
  elabSrvCmd (← `(command| set_option linter.unusedVariables false in @[noinline] def $stepId ($s0Id:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]* : $stepRetTy := $stepBody))
  if (← hasSrvErrors) then return none
  let stepCall ← mkAppTerms (← `($stepId $s0Id)) (allBinderIds.map (⟨·.raw⟩))
  if isReadOnly then
    deferSrvCmd (← `(command| theorem $(c.fnSubId fnIdent "_readOnly") ($s0Id:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]* :
      ($stepCall).1 = $s0Id := by qedSrvProveStep [$stepId] $fnLit $(Syntax.mkStrLit s!"{fnStr} read-only state preservation")))
  else deferInvProofs false fnStr fnIdent stepId allBinderIds allBinderTys stepCall (← `(command| theorem $invThmId ($s0Id:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]* (_hInv : $(c.stateInvId) $s0Id) :
      $(c.stateInvId) ($stepCall).1 := by qedSrvProveStep [$(c.stateInvId), $stepId] $fnLit $singleInvLbl))
  if let some ens := ensSpec? then
    let postGoal ← liftM <| ens.postFn (← if hasEmit then `(($stepCall).2.1) else `(($stepCall).2))
    let ensTac ← liftM <| mkStepEnsProofTac #[c.stateInvId, stepId, ens.ensId] fnLit ens.labelStr ens.tac?
    deferSrvCmd (← `(command| theorem $(c.fnSubId fnIdent "_ensures") ($s0Id:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]* (_hInv : $(c.stateInvId) $s0Id) :
      $postGoal := by $ensTac))
  let sSnap := mkIdent `_sSnap
  return some { runExpr := ← liftM <| mkAtomicRunTerm sSnap ⟨c.stateId.raw⟩ (← mkAppTerms (← `($stepId $sSnap)) callArgs) isReadOnly hasEmit,
                targetId := stepId, isAsync := false, allBinderIds, allBinderTys,
                mutatesState := !isReadOnly, dbWrite := lSt.dbWrite, hasEmit, hasCookieOp := lSt.hasCookieOp }

@[noinline]
private def elabAsyncHandler (fnStr : String) (fnIdent invThmId : Ident) (fnLit singleInvLbl : StrLit)
    (allBinderIds : Array Ident) (allBinderTys callArgs : Array Term) (payloadTerm errTyTerm : Term)
    (baseCtx : LowerCtx) (bodyStmts : Array Syntax) (hasEmit : Bool) (ensSpec? : Option FnEnsSpec) : SrvElabM (Option ElabHandlerRes) := do
  let c ← read
  let (asyncBody, lSt) ← liftM <| (lowerAsyncBlock baseCtx (if c.hasState then some ⟨c.stateId.raw⟩ else none) bodyStmts).run {}
  recordSrvExtRoots lSt.extRoots
  let handlerId := c.fnSubId fnIdent "_handler"; let atomicBinders ← liftM c.atomicBinders
  elabSrvCmd (← `(command| set_option linter.unusedVariables false in @[noinline] def $handlerId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m] $[$atomicBinders:bracketedBinder]* $[($allBinderIds:ident : $allBinderTys:term)]* :
    m (Except $errTyTerm $payloadTerm) := Qed.Server.srvFinishM $asyncBody))
  if (← hasSrvErrors) then return none
  let hCall ← mkAppTerms handlerId (allBinderIds.map (⟨·.raw⟩))
  if c.hasState then
    let invUnfolds := #[c.stateInvId] ++ c.statefulHelperIds
    deferInvProofs true fnStr fnIdent handlerId allBinderIds allBinderTys hCall (← `(command| theorem $invThmId $[($allBinderIds:ident : $allBinderTys:term)]* :
      Qed.Server.ProgPreservesInv $(c.stateInvId) ($hCall : Qed.Server.ThreadProg $(c.stateId) _) := by qedSrvProveAsync $handlerId [$[$invUnfolds],*] $fnLit $singleInvLbl))
  if let some ens := ensSpec? then
    let (invT, tyT, extra) ← if c.hasState then pure (⟨c.stateInvId.raw⟩, ⟨c.stateId.raw⟩, #[c.stateInvId]) else pure (← `(fun _ : Unit => True), ← `(Unit), #[])
    let outVar := mkIdent `_srvOut; let postBody ← liftM <| ens.postFn ⟨outVar.raw⟩; let unfoldIds := extra ++ c.statefulHelperIds |>.push ens.ensId
    let ensTac ← liftM <| mkAsyncEnsProofTac handlerId unfoldIds fnLit ens.labelStr ens.tac?
    deferSrvCmd (← `(command| theorem $(c.fnSubId fnIdent "_ensures") $[($allBinderIds:ident : $allBinderTys:term)]* :
      Qed.Server.ProgEnsures $invT (fun ($outVar:ident : Except $errTyTerm $payloadTerm) => $postBody) ($hCall : Qed.Server.ThreadProg $tyT _) := by $ensTac))
  return some { runExpr := ← mkAppTerms handlerId callArgs,
                targetId := handlerId, isAsync := true, allBinderIds, allBinderTys,
                mutatesState := !lSt.mutated.isEmpty, dbWrite := lSt.dbWrite, hasEmit, hasCookieOp := lSt.hasCookieOp }

def elabServerHandler (isAsync : Bool) (fnStr : String) (fnIdent : Ident)
    (extraBinderIds : Array Ident) (extraBinderTys extraCallArgs : Array Term)
    (payloadTerm errTyTerm : Term) (baseCtx : LowerCtx) (bodyStmts : Array Syntax)
    (ensSpec? : Option FnEnsSpec) (ctxArg? : Option Term := none) : SrvElabM (Option ElabHandlerRes) := do
  let c ← read; let envTys ← liftM c.envBinderTys
  let allBinderIds := c.envIdents ++ #[c.ctxId] ++ extraBinderIds
  let allBinderTys := envTys ++ #[← `(Qed.Server.RequestCtx)] ++ extraBinderTys
  let callArgs : Array Term := c.envIdents.map (⟨·.raw⟩) ++ #[ctxArg?.getD ⟨c.ctxId.raw⟩] ++ extraCallArgs
  let (invThmId, fnLit, singleInvLbl, hasEmit) := (c.fnSubId fnIdent "_inv", Syntax.mkStrLit fnStr, Syntax.mkStrLit (singleInvLabelStr c.invs), blockHasEmit bodyStmts)
  (if c.hasState && !isAsync then elabPureHandler else elabAsyncHandler)
    fnStr fnIdent invThmId fnLit singleInvLbl allBinderIds allBinderTys callArgs payloadTerm errTyTerm baseCtx bodyStmts hasEmit ensSpec?

end SrvHelpers
end Qed.Server
