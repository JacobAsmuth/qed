import Qed.Server.Lower

namespace Qed.Server
open Qed.Lang

/-! ## `server` Command Elaborator — Context & Shared Builders (`SrvElabCtx` / `SrvElabM`) -/

structure ParsedEnvDecl where
  ref      : Lean.Syntax
  ident    : Lean.Ident
  osKey    : String
  default? : Option String

structure ParsedStateDecl where
  ref          : Lean.Syntax
  ident        : Lean.Ident
  tyTerm       : Lean.Term
  initStx?     : Option Lean.Syntax
  defaultTerm? : Option Lean.Term

structure ParsedMutInv where
  ref      : Lean.Syntax
  name     : Lean.Ident
  fieldId  : Lean.Ident
  condStx  : Lean.Syntax
  label    : String

structure ParsedInv where
  ref      : Lean.Syntax
  name     : Lean.Ident
  exprStx  : Lean.Syntax
  isTwoSt  : Bool
  label    : String

structure ParsedDbDecl where
  ref        : Lean.Syntax
  aliasIdent : Lean.Ident
  dbRefIdent : Lean.Ident
  info       : DatabaseInfo

structure ParsedAuthDecl where
  ref          : Lean.Syntax
  aliasIdent   : Lean.Ident
  authRefIdent : Lean.Ident
  info         : AuthInfo

structure ParsedServerBlock where
  dbDecls                 : Array ParsedDbDecl
  authDecl?               : Option ParsedAuthDecl := none
  envDecls                : Array ParsedEnvDecl
  stateDecls              : Array ParsedStateDecl
  mutInvs                 : Array ParsedMutInv
  invs                    : Array ParsedInv
  fnClauses               : Array Lean.Syntax
  chanClauses             : Array Lean.Syntax
  httpClauses             : Array Lean.Syntax := #[]
  jobClauses              : Array Lean.Syntax := #[]
  onCreateAccountClause?  : Option Lean.Syntax := none
  onSignInClause?         : Option Lean.Syntax := none

structure SrvElabCtx where
  priorRep        : Nat
  priorUnrep      : Nat
  srvIdent        : Lean.Ident
  srvName         : Lean.Name
  fullSrvName     : Lean.Name
  srvShort        : String
  hasState        : Bool
  stateId         : Lean.Ident
  initStateId     : Lean.Ident
  stateInvId      : Lean.Ident
  invInitId       : Lean.Ident
  ctxId           : Lean.Ident
  reqBytesId      : Lean.Ident
  dbDecls         : Array ParsedDbDecl
  dbBindings      : Array (String × DatabaseInfo)
  authDecl?       : Option ParsedAuthDecl
  envDecls        : Array ParsedEnvDecl
  envIdents       : Array Lean.Ident
  envTypes        : Array Lean.Term
  stateFieldNames : Array String
  envVarNames     : Array String
  invs            : Array ParsedInv
  mutInvs         : Array ParsedMutInv
  chanSigs        : Array SrvChanSig := #[]
  deferredProofs  : IO.Ref (Array (Lean.Elab.Command.CommandElabM Bool))
  extRootsRef     : IO.Ref (Array Lean.Name)

abbrev SrvElabM := ReaderT SrvElabCtx Lean.Elab.Command.CommandElabM

private def singleInvLabelStr (invs : Array ParsedInv) : String :=
  let ss := ((invs.filter (!·.isTwoSt)).toList.map (·.label)).eraseDups
  if ss.isEmpty then "StateInv" else String.intercalate ", " ss

section SrvHelpers
open Lean Elab Command

def filterNewWarnings (arr : PersistentArray Message) (priorSize : Nat) :
    PersistentArray Message :=
  let lst := arr.toList
  ((lst.take priorSize) ++ (lst.drop priorSize).filter (·.severity != .warning)).foldl (·.push ·) {}

def hasNewErrors (log : MessageLog) (priorRep priorUnrep : Nat) : Bool :=
  (log.reported.toList.drop priorRep).any (·.severity == .error) ||
  (log.unreported.toList.drop priorUnrep).any (·.severity == .error)

def hasSrvErrors : SrvElabM Bool := do
  let c ← read
  return hasNewErrors (← get).messages c.priorRep c.priorUnrep

def recordSrvExtRoots (roots : Array Name) : SrvElabM Unit := do
  (← read).extRootsRef.modify fun acc => acc ++ roots.filter (!acc.contains ·)

def deferSrvProof (act : CommandElabM Bool) : SrvElabM Unit := do
  (← read).deferredProofs.modify (·.push act)

def deferSrvCmd (cmd : TSyntax `command) : SrvElabM Unit := do
  let c ← read
  deferSrvProof do
    elabCommand cmd
    return !hasNewErrors (← get).messages c.priorRep c.priorUnrep

def mkBaseLowerCtx (fnName : String) (locals : Array String) (allowAwait allowUnwrap hasFallible : Bool)
    (innerOptTy? : Option Term := none) (domainErrTy? : Option Term := none)
    (isHttpRoute := false) (isStreamRoute := false) (includeDbs := true) : SrvElabM LowerCtx := do
  let c ← read
  return {
    fnName, stateFields := c.stateFieldNames, envVars := c.envVarNames, locals
    stateRule := if c.hasState then .pureStep (mkIdent `_s0) else .statelessServer
    allowAwait, allowUnwrap, hasFallible, isOption := innerOptTy?.isSome, innerOptTy?, domainErrTy?
    channels := c.chanSigs, dbs := if includeDbs then c.dbBindings else #[]
    isHttpRoute, isStreamRoute
  }

def extractTupleProjections (reqVar : Ident) (n : Nat) : CommandElabM (Array Term) := do
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

def mkProtoDecodeBind (bytesVar tupleVar : Ident) (tupleTy : Term)
    (pIdents : Array Ident) (projs : Array Term) (body : Term) : CommandElabM Term := do
  let bound ← (pIdents.zip projs).foldrM (init := body) fun (pid, prj) acc =>
    `(let $pid:ident := $prj; $acc)
  `(match Qed.Proto.decode (α := $tupleTy) $bytesVar with
    | Except.error _decErr => Pure.pure (Except.error (Qed.Server.ApiError.badRequest _decErr))
    | Except.ok $tupleVar:ident => $bound)

def checkSrvParamName (ctxLabel : String) (pid : Ident)
    (reserved seen extraShadow : Array String := #[]) : SrvElabM String := do
  let c ← read
  let pstr := pid.getId.toString
  if pstr == "ctx" then
    throwErrorAt pid s!"`ctx` is already implicitly available as `RequestCtx` in {ctxLabel}"
  if reserved.contains pstr then
    throwErrorAt pid s!"`{pstr}` is reserved inside {ctxLabel}; rename this parameter"
  if seen.contains pstr then
    throwErrorAt pid s!"duplicate parameter `{pstr}` in {ctxLabel}"
  if extraShadow.contains pstr then
    throwErrorAt pid s!"parameter `{pstr}` shadows an existing binding in {ctxLabel}; rename the parameter"
  if c.envVarNames.contains pstr then
    throwErrorAt pid s!"parameter `{pstr}` in {ctxLabel} shadows server `env` binding `{pstr}`; rename the parameter"
  if c.stateFieldNames.contains pstr then
    throwErrorAt pid s!"parameter `{pstr}` in {ctxLabel} shadows server `state` field `{pstr}`; rename the parameter"
  return pstr

def parseSrvParams (ctxLabel tyDescPrefix : String) (rawParams : Array Syntax)
    (reserved extraShadow : Array String := #[]) :
    SrvElabM (Array Ident × Array Term × Array String) := do
  let mut idents : Array Ident := #[]
  let mut tyTerms : Array Term := #[]
  let mut names : Array String := #[]
  for rp in rawParams do
    let pid : Ident := ⟨rp.getArg 0⟩
    let pstr ← checkSrvParamName ctxLabel pid reserved names extraShadow
    let pty ← liftMacroM <| lowerSrvType (rp.getArg 2) (allowFallible := false) s!"{tyDescPrefix} `{pstr}`"
    idents := idents.push pid
    tyTerms := tyTerms.push pty.term
    names := names.push pstr
  return (idents, tyTerms, names)

def elabServerStateCmds (stateDecls : Array ParsedStateDecl) : SrvElabM Bool := do
  let c ← read
  let mut stFieldIds : Array Ident := #[]
  let mut stFieldTys : Array Term := #[]
  let mut stInitVals : Array Term := #[]
  let initCtx : LowerCtx := {
    fnName := "initState", stateFields := #[], envVars := #[], locals := #[]
    stateRule := .statelessServer, allowAwait := false, allowUnwrap := false
    hasFallible := false, isOption := false, innerOptTy? := none
  }
  for sd in stateDecls do
    let initTerm ← match sd.initStx?, sd.defaultTerm? with
      | some stx, _ => pure (← liftM <| (lowerExpr initCtx .val stx).run {}).1
      | none, some dt => pure dt
      | none, none => unreachable!
    stFieldIds := stFieldIds.push sd.ident
    stFieldTys := stFieldTys.push sd.tyTerm
    stInitVals := stInitVals.push (← `(srvAutoField($initTerm)))
  liftM <| elabCommand (← `(command|
    structure $(c.stateId) where
      $[$stFieldIds:ident : $stFieldTys:term]*))
  liftM <| elabCommand (← `(command|
    def $(c.initStateId) : $(c.stateId) := { $[$stFieldIds:ident := $stInitVals:term],* }))
  if (← hasSrvErrors) then return false

  let sParam := mkIdent `_s
  let sOldDummy := mkIdent `_sOld
  let mut singleProps : Array Term := #[]
  for inv in c.invs do
    if !inv.isTwoSt then
      let invCtx : LowerCtx := {
        fnName := "invariant", stateFields := c.stateFieldNames, envVars := c.envVarNames, locals := #[]
        stateRule := .invariantProp sParam sOldDummy false
        allowAwait := false, allowUnwrap := false, hasFallible := false, isOption := false, innerOptTy? := none
      }
      let (pTerm, _) ← liftM <| (lowerExpr invCtx .propInv inv.exprStx).run {}
      singleProps := singleProps.push pTerm
  let invBody ← liftM <| buildPropConj singleProps
  let initInvLbl := Syntax.mkStrLit ("init: " ++ singleInvLabelStr c.invs)
  liftM <| elabCommand (← `(command|
    def $(c.stateInvId) ($sParam:ident : $(c.stateId)) : Prop := $invBody))
  liftM <| elabCommand (← `(command|
    theorem $(c.invInitId) : $(c.stateInvId) $(c.initStateId) := by
      qedSrvProveStep [$(c.stateInvId), $(c.initStateId)] "initState" $initInvLbl))
  return !(← hasSrvErrors)

def parseServerClauses (srvIdent : Ident) (srvName : Name) (clauses : Array Syntax) :
    CommandElabM ParsedServerBlock := do
  let mut dbDecls     : Array ParsedDbDecl := #[]
  let mut authDecl?   : Option ParsedAuthDecl := none
  let mut envDecls    : Array ParsedEnvDecl := #[]
  let mut stateDecls  : Array ParsedStateDecl := #[]
  let mut mutInvs     : Array ParsedMutInv := #[]
  let mut invs        : Array ParsedInv := #[]
  let mut seenInvNames : Array Name := #[]
  let mut fnClauses   : Array Syntax := #[]
  let mut chanClauses : Array Syntax := #[]
  let mut httpClauses : Array Syntax := #[]
  let mut jobClauses  : Array Syntax := #[]
  let mut onCreateAccountClause? : Option Syntax := none
  let mut onSignInClause?        : Option Syntax := none
  for c in clauses do
    let k := c.getKind
    if k == ``srvDbClause then
      let aliasRaw := c.getArg 1
      let aliasId : Ident := if aliasRaw.isIdent then ⟨aliasRaw⟩ else mkIdentFrom aliasRaw `auth
      let refId : Ident := ⟨(c.getArg 3)⟩
      if dbDecls.any (·.aliasIdent.getId == aliasId.getId) ||
         authDecl?.any (·.aliasIdent.getId == aliasId.getId) ||
         envDecls.any (·.ident.getId == aliasId.getId) ||
         stateDecls.any (·.ident.getId == aliasId.getId) then
        throwErrorAt aliasId s!"duplicate declaration `{aliasId.getId}` in `server {srvName}`"
      let env ← getEnv
      let currNs ← getCurrNamespace
      let openDecls ← getOpenDecls
      if let some dbInfo := Qed.Server.lookupDatabase? env currNs openDecls refId.getId then
        dbDecls := dbDecls.push { ref := c, aliasIdent := aliasId, dbRefIdent := refId, info := dbInfo }
      else if let some authInfo := Qed.Server.lookupAuth? env currNs openDecls refId.getId then
        if authDecl?.isSome then
          throwErrorAt refId s!"`server {srvName}` can declare at most one `use ... : <auth>` provider"
        authDecl? := some { ref := c, aliasIdent := aliasId, authRefIdent := refId, info := authInfo }
      else
        throwErrorAt refId s!"unknown `database` or `auth` `{refId.getId}` in `use {aliasId.getId} : {refId.getId}`"
    else if k == ``srvEnvClause then
      let id : Ident := ⟨(c.getArg 1)⟩
      let osKey := (⟨(c.getArg 3)⟩ : TSyntax `str).getString
      let def? := if (c.getArg 4).getNumArgs == 2 then some ((⟨((c.getArg 4).getArg 1)⟩ : TSyntax `str).getString) else none
      if envDecls.any (·.ident.getId == id.getId) then
        throwErrorAt id s!"duplicate `env {id.getId}` in `server {srvName}`"
      envDecls := envDecls.push { ref := c, ident := id, osKey, default? := def? }
    else if k == ``srvStateClause then
      let id : Ident := ⟨(c.getArg 1)⟩
      let ty ← liftMacroM <| lowerSrvType (c.getArg 3) (allowFallible := false) s!"state field `{id.getId}`"
      if stateDecls.any (·.ident.getId == id.getId) || envDecls.any (·.ident.getId == id.getId) then
        throwErrorAt id s!"duplicate declaration `{id.getId}` in `server {srvName}`"
      let (initStx?, defaultTerm?) ←
        if (c.getArg 4).getNumArgs == 2 then pure (some ((c.getArg 4).getArg 1), none)
        else match ← liftMacroM (inferQedTypeDefault? (c.getArg 3)) with
          | some dt => pure (none, some dt)
          | none    => throwErrorAt id s!"state field `{id.getId}` requires an initial value `= ...`"
      stateDecls := stateDecls.push { ref := c, ident := id, tyTerm := ty.term, initStx?, defaultTerm? }
    else if k == ``srvInvMutatingClause then
      let nameId : Ident := ⟨(c.getArg 1)⟩
      if seenInvNames.contains nameId.getId then
        throwErrorAt nameId s!"duplicate invariant `{nameId.getId}` in `server {srvName}`"
      seenInvNames := seenInvNames.push nameId.getId
      mutInvs := mutInvs.push {
        ref := c, name := nameId, fieldId := ⟨c.getArg 4⟩, condStx := c.getArg 6, label := s!"mutating:{nameId.getId}"
      }
    else if k == ``srvInvClause then
      let nameId : Ident := ⟨(c.getArg 1)⟩
      if seenInvNames.contains nameId.getId then
        throwErrorAt nameId s!"duplicate invariant `{nameId.getId}` in `server {srvName}`"
      seenInvNames := seenInvNames.push nameId.getId
      for e in (c.getArg 3).getSepArgs do
        invs := invs.push { ref := c, name := nameId, exprStx := e, isTwoSt := exprCallsOld e, label := nameId.getId.toString }
    else if k == ``srvFnClause then fnClauses := fnClauses.push c
    else if k == ``srvChannelClause then chanClauses := chanClauses.push c
    else if k == ``srvHttpRouteClause || k == ``srvStreamClause then httpClauses := httpClauses.push c
    else if k == ``srvJobClause then jobClauses := jobClauses.push c
    else if k == ``srvOnCreateAccountClause then
      if onCreateAccountClause?.isSome then throwErrorAt c s!"duplicate `onCreateAccount` hook in `server {srvName}`"
      onCreateAccountClause? := some c
    else if k == ``srvOnSignInClause then
      if onSignInClause?.isSome then throwErrorAt c s!"duplicate `onSignIn` hook in `server {srvName}`"
      onSignInClause? := some c
    else
      throwErrorAt c "unexpected clause in `server` block"
  if let some c := onCreateAccountClause? then
    if authDecl?.isNone then throwErrorAt c s!"`onCreateAccount` in `server {srvName}` requires `use auth : <Auth>`"
  if let some c := onSignInClause? then
    if authDecl?.isNone then throwErrorAt c s!"`onSignIn` in `server {srvName}` requires `use auth : <Auth>`"
  if fnClauses.isEmpty && chanClauses.isEmpty && httpClauses.isEmpty && jobClauses.isEmpty &&
     onCreateAccountClause?.isNone && onSignInClause?.isNone then
    throwErrorAt srvIdent s!"`server {srvName}` must declare at least one `def`, `channel`, `http`, `stream`, `every` job, or auth hook"
  let hasState := !stateDecls.isEmpty
  if !hasState && (!invs.isEmpty || !mutInvs.isEmpty) then
    throwErrorAt srvIdent s!"`server {srvName}` declares `invariant`s but has no `state` fields"
  for mi in mutInvs do
    unless stateDecls.any (·.ident.getId == mi.fieldId.getId) do
      let avail := String.intercalate ", " (stateDecls.toList.map fun s => s!"`{s.ident.getId}`")
      throwErrorAt mi.fieldId s!"`invariant mutating {mi.fieldId.getId}` does not match any `state` field of `{srvName}` (`state` fields: {avail})"
  return { dbDecls, authDecl?, envDecls, stateDecls, mutInvs, invs, fnClauses, chanClauses, httpClauses, jobClauses, onCreateAccountClause?, onSignInClause? }

partial def splitSrvAnd (stx : Syntax) : Array Syntax :=
  let u := unwrapParens1 stx
  if u.getKind == ``qedAnd then splitSrvAnd (u.getArg 0) ++ splitSrvAnd (u.getArg 2) else #[u]

partial def scanCtxEnv (envVars : Array String) (locals : Array String) (stx : Syntax) : Bool × Bool :=
  let k := stx.getKind
  if k == ``qedIdent then
    match (stx.getArg 0).getId.components with
    | root :: _ =>
        let r := root.toString
        if locals.contains r then (false, false)
        else if r == "ctx" then (true, false)
        else if envVars.contains r then (false, true)
        else (false, false)
    | [] => (false, false)
  else if k == ``qedProj then scanCtxEnv envVars locals (stx.getArg 0)
  else if k == ``qedLam1 then
    let b := if (stx.getArg 0).isIdent then #[(stx.getArg 0).getId.toString] else #[]
    scanCtxEnv envVars (locals ++ b) (stx.getArg 2)
  else if k == ``qedLamN then
    let ps := (stx.getArg 1).getSepArgs.filterMap fun b => if b.isIdent then some b.getId.toString else none
    scanCtxEnv envVars (locals ++ ps) (stx.getArg 4)
  else if k == ``qedAllIn || k == ``qedAnyIn then
    let (c1, e1) := scanCtxEnv envVars locals (stx.getArg 3)
    let (c2, e2) := scanCtxEnv envVars (locals.push (stx.getArg 1).getId.toString) (stx.getArg 5)
    (c1 || c2, e1 || e2)
  else if k == ``qedAllVars then
    scanCtxEnv envVars (locals ++ (stx.getArg 1).getSepArgs.map (·.getId.toString)) (stx.getArg 3)
  else
    stx.getArgs.foldl (fun (ac, ae) ch => let (c, e) := scanCtxEnv envVars locals ch; (ac || c, ae || e)) (false, false)

def isAuthReqLabel (s : String) : Bool :=
  s.contains "ctx.userId" || s.contains "ctx.isAuthenticated" || s.contains "ctx.bearerToken"

def wrapReqs (reqProps : Array Term) (reqHIds : Array Ident) (reqLbls : Array String) (inner : Term) :
    CommandElabM Term := do
  let mut g := inner
  for revIdx in [0:reqProps.size] do
    let ri := reqProps.size - 1 - revIdx
    let rCond := reqProps[ri]!
    let rHyp := reqHIds[ri]!
    let rLbl := reqLbls[ri]!
    let rMsg := Syntax.mkStrLit s!"precondition failed: {rLbl}"
    let errCtor : Term ←
      if isAuthReqLabel rLbl then `(Qed.Server.ApiError.unauthorized $rMsg)
      else if rLbl.contains "ctx.hasClaim" || rLbl.contains "ctx.claim" then `(Qed.Server.ApiError.forbidden $rMsg)
      else `(Qed.Server.ApiError.badRequest $rMsg)
    g ← `(if $rHyp:ident : $rCond then $g else Pure.pure (Except.error $errCtor))
  return g

structure LoweredRequires where
  reqPropTerms    : Array Term
  reqHypIds       : Array Ident
  reqHypTys       : Array Term
  reqLabels       : Array String
  requiresAuth    : Bool
  clientReqId?    : Option Ident
  clientReqConst? : Option Name
  clientReqLabel  : String

def elabRequiresClauses (refIdent : Ident) (itemName : Name)
    (fnLabel hypPrefix reqSuffix : String)
    (serverLocals clientLocals : Array String)
    (clientBindIds : Array Ident) (clientBindTys : Array Term)
    (reqExprs : Array Syntax) (excludedClientVars : Array String := #[])
    (trackAuth : Bool := true) : SrvElabM LoweredRequires := do
  let c ← read
  let mut reqPropTerms : Array Term := #[]
  let mut reqHypIds : Array Ident := #[]
  let mut reqHypTys : Array Term := #[]
  let mut reqLabels : Array String := #[]
  let mut clientReqProps : Array Term := #[]
  let mut clientReqLabels : Array String := #[]
  let mut requiresAuth := false
  for idx in [0:reqExprs.size] do
    let rExpr := reqExprs[idx]!
    if exprHasAwait rExpr then throwErrorAt rExpr "`requires` precondition cannot contain `await`"
    let reqCtx : LowerCtx := {
      fnName := fnLabel, stateFields := c.stateFieldNames, envVars := c.envVarNames, locals := serverLocals
      stateRule := .forbidInRequires, allowAwait := false, allowUnwrap := false
      hasFallible := false, isOption := false, innerOptTy? := none
    }
    let (pTerm, rSt) ← liftM <| (lowerExpr reqCtx .propGuard rExpr).run {}
    recordSrvExtRoots rSt.extRoots
    reqPropTerms := reqPropTerms.push pTerm
    reqHypIds := reqHypIds.push (mkIdent (Name.mkSimple s!"{hypPrefix}{idx}"))
    reqHypTys := reqHypTys.push pTerm
    reqLabels := reqLabels.push ((rExpr.reprint.getD "requires").trimAscii.toString)
    for conj in splitSrvAnd rExpr do
      let (mentionsCtx, mentionsEnv) := scanCtxEnv c.envVarNames serverLocals conj
      if trackAuth && mentionsCtx && !mentionsEnv && isAuthReqLabel (conj.reprint.getD "") then
        requiresAuth := true
      else if !mentionsCtx && !mentionsEnv then
        if excludedClientVars.isEmpty || !(scanCtxEnv excludedClientVars clientLocals conj).2 then
          let cliReqCtx : LowerCtx := {
            fnName := fnLabel, stateFields := c.stateFieldNames, envVars := #[], locals := clientLocals
            stateRule := .forbidInRequires, allowAwait := false, allowUnwrap := false
            hasFallible := false, isOption := false, innerOptTy? := none, forbidCtxEnv := true
          }
          let (cpTerm, _) ← liftM <| (lowerExpr cliReqCtx .propInv conj).run {}
          clientReqProps := clientReqProps.push cpTerm
          clientReqLabels := clientReqLabels.push ((conj.reprint.getD "requires").trimAscii.toString)
  let (clientReqId?, clientReqConst?) ←
    if clientReqProps.isEmpty then pure (none, none)
    else
      let leaf := itemName.appendAfter reqSuffix
      let cid := mkIdentFrom refIdent (c.srvName ++ leaf)
      let reqConj ← liftM <| buildPropConj clientReqProps
      liftM <| elabCommand (← `(command|
        set_option linter.unusedVariables false in
        @[simp] abbrev $cid $[($clientBindIds:ident : $clientBindTys:term)]* : Prop := $reqConj))
      pure (some cid, some (c.fullSrvName ++ leaf))
  return {
    reqPropTerms, reqHypIds, reqHypTys, reqLabels, requiresAuth,
    clientReqId?, clientReqConst?,
    clientReqLabel := String.intercalate " && " clientReqLabels.toList
  }

def elabEnsuresAbbrev (ownerIdent : Ident) (fnLabel : String) (binderName : Name)
    (paramNames : Array String) (pIdents : Array Ident) (pTyTerms : Array Term)
    (resTyTerm : Term) (ensExprs : Array Syntax) :
    SrvElabM (Option (Option (Ident × Name × String))) := do
  if ensExprs.isEmpty then return some none
  let c ← read
  let mut ensProps : Array Term := #[]
  let mut ensLabels : Array String := #[]
  for eExpr in ensExprs do
    if exprHasAwait eExpr then throwErrorAt eExpr "`ensures` postcondition cannot contain `await`"
    let ensCtx : LowerCtx := {
      fnName := fnLabel, stateFields := c.stateFieldNames, envVars := c.envVarNames,
      locals := paramNames.push binderName.toString, stateRule := .forbidInEnsures,
      allowAwait := false, allowUnwrap := false, hasFallible := false,
      isOption := false, innerOptTy? := none, forbidCtxEnv := true
    }
    let (pTerm, _) ← liftM <| (lowerExpr ensCtx .propInv eExpr).run {}
    ensProps := ensProps.push pTerm
    ensLabels := ensLabels.push ((eExpr.reprint.getD "ensures").trimAscii.toString)
  let leaf := ownerIdent.getId.appendAfter "_ens"
  let ensId := mkIdentFrom ownerIdent (c.srvName ++ leaf)
  let resIdent := mkIdent binderName
  let ensConj ← liftM <| buildPropConj ensProps
  liftM <| elabCommand (← `(command|
    set_option linter.unusedVariables false in
    @[simp] abbrev $ensId $[($pIdents:ident : $pTyTerms:term)]* ($resIdent:ident : $resTyTerm) : Prop :=
      $ensConj))
  if (← hasSrvErrors) then return none
  return some (some (ensId, c.fullSrvName ++ leaf, String.intercalate " && " ensLabels.toList))

private partial def scanFailCallsAux (stx : Syntax) (tags : Array Ident) (hasPlain : Bool) :
    CommandElabM (Array Ident × Bool) := do
  if stx.getKind == ``qedCall && (stx.getArg 0).getKind == ``qedIdent && ((stx.getArg 0).getArg 0).getId == `fail then
    let rawArgs := (stx.getArg 2).getSepArgs
    if (rawArgs.size == 1 || rawArgs.size == 2) && (unwrapParens1 rawArgs[0]![0]).getKind == ``qedDotIdent then
      let tagId : Ident := ⟨(unwrapParens1 rawArgs[0]![0])[1]⟩
      let tags' := if tags.any (·.getId == tagId.getId) then tags else tags.push tagId
      if rawArgs.size == 2 then scanFailCallsAux rawArgs[1]! tags' hasPlain else return (tags', hasPlain)
    else
      rawArgs.foldlM (init := (tags, true)) fun (t, p) arg => scanFailCallsAux arg t p
  else
    stx.getArgs.foldlM (init := (tags, hasPlain)) fun (t, p) ch => scanFailCallsAux ch t p

def scanBodyFailTags (stmts : Array Syntax) : CommandElabM (Array Ident × Bool) :=
  stmts.foldlM (init := (#[], false)) fun (t, p) st => scanFailCallsAux st t p

private def mkErrDotTerm (tid : Ident) : Term :=
  ⟨Syntax.node (.fromRef tid) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef tid) ".", tid]⟩

def elabDomainErrorType (fnIdent : Ident) (tagIdents : Array Ident) : SrvElabM Ident := do
  let c ← read
  let errTypeId := mkIdentFrom fnIdent (c.srvName ++ fnIdent.getId ++ `Error)
  let ctors ← tagIdents.mapM fun tid => `(Lean.Parser.Command.ctor| | $tid:ident)
  liftM <| elabCommand (← `(command|
    inductive $errTypeId where
      $[$ctors:ctor]*
    deriving Inhabited, DecidableEq, Repr))
  let toStrAlts ← tagIdents.mapM fun tid =>
    `(Lean.Parser.Term.matchAltExpr| | $(mkErrDotTerm tid) => $(Syntax.mkStrLit tid.getId.toString))
  let fromJsonAlts := (← tagIdents.mapM fun tid =>
    `(Lean.Parser.Term.matchAltExpr| | Qed.Json.str $(Syntax.mkStrLit tid.getId.toString) => Except.ok $(mkErrDotTerm tid))).push
    (← `(Lean.Parser.Term.matchAltExpr| | _ => Except.error "invalid RPC error tag"))
  let toProtoAlts ← tagIdents.zipIdx.mapM fun (tid, i) =>
    `(Lean.Parser.Term.matchAltExpr| | $(mkErrDotTerm tid) => Qed.Proto.WireVal.varint $(Syntax.mkNumLit (toString i)))
  let fromProtoAlts := (← tagIdents.zipIdx.mapM fun (tid, i) =>
    `(Lean.Parser.Term.matchAltExpr| | Qed.Proto.WireVal.varint $(Syntax.mkNumLit (toString i)) => Except.ok $(mkErrDotTerm tid))).push
    (← `(Lean.Parser.Term.matchAltExpr| | _ => Except.error "protobuf: invalid RPC error tag"))
  for cmd in #[
    ← `(command| instance : ToString $errTypeId where toString e := match e with $[$toStrAlts:matchAlt]*),
    ← `(command| instance : Qed.ToJson $errTypeId := ⟨fun e => Qed.Json.str (toString e)⟩),
    ← `(command| instance : Qed.FromJson $errTypeId where fromJson j := match j with $[$fromJsonAlts:matchAlt]*),
    ← `(command| instance : Qed.LawfulJson $errTypeId where depthBound := 0; depth_toJson _ := Nat.le_refl 0; fromJson_toJson e := by cases e <;> rfl),
    ← `(command| instance : Qed.NonNullJson $errTypeId := ⟨nofun⟩),
    ← `(command| instance : Qed.ToProto $errTypeId where toProtoVal e := match e with $[$toProtoAlts:matchAlt]*),
    ← `(command| instance : Qed.FromProto $errTypeId where fromProtoVal w := match w with $[$fromProtoAlts:matchAlt]*),
    ← `(command| instance : Qed.LawfulProto $errTypeId := Qed.LawfulProto.ofScalar (by intro e; cases e <;> rfl))
  ] do liftM <| elabCommand cmd
  return errTypeId

private def collectServerSecretsAndExts : SrvElabM (Array String × Array (String × String)) := do
  let c ← read
  let env ← getEnv
  let currNs ← getCurrNamespace
  let openDecls ← getOpenDecls
  let allExtRoots ← c.extRootsRef.get
  let mut reqSecrets : Array String := #[]
  let pushSec (s : String) (arr : Array String) := if arr.contains s then arr else arr.push s
  for dbd in c.dbDecls do
    if !dbd.info.hasDevFallback then reqSecrets := dbd.info.secrets.foldl (fun a s => pushSec s a) reqSecrets
  for ed in c.envDecls do
    if ed.default?.isNone then reqSecrets := pushSec ed.osKey reqSecrets
  if let some ad := c.authDecl? then
    reqSecrets := ad.info.secrets.foldl (fun a s => pushSec s a) reqSecrets
  let mut usedExts : Array (String × String) := #[]
  for root in allExtRoots do
    if let some extInfo := Qed.Diag.lookupNameMapExt? externalRegistry env currNs openDecls root then
      let sStr := root.toString
      unless usedExts.any (·.1 == sStr) do usedExts := usedExts.push (sStr, extInfo.baseOrigin)
      reqSecrets := extInfo.secrets.foldl (fun a s => pushSec s a) reqSecrets
  return (reqSecrets, usedExts)

/-- Wraps `innerRun` (and optionally a `ProgPreservesInv` proof) with `readEnv` bindings for `envDecls`. -/
def wrapWithEnvDecls (envDecls : Array ParsedEnvDecl)
    (innerRun : Term) (innerProof? : Option Term := none) : CommandElabM (Term × Option Term) :=
  envDecls.foldrM (init := (innerRun, innerProof?)) fun ed (accRun, accPf?) => do
    let eid := ed.ident
    let keyLit := Syntax.mkStrLit ed.osKey
    match ed.default? with
    | some defVal =>
        let defLit := Syntax.mkStrLit defVal
        let run' ← if accPf?.isSome then
            `(Qed.Server.MonadServer.readEnv $keyLit >>= fun _envOpt =>
              (fun ($eid:ident : String) => $accRun) (_envOpt.getD $defLit))
          else
            `(Qed.Server.MonadServer.readEnv $keyLit >>= fun _envOpt =>
              let $eid:ident : String := _envOpt.getD $defLit
              $accRun)
        let pf'? ← accPf?.mapM fun pf =>
          `(Qed.Server.progPreservesInv_readEnv_default $keyLit $defLit
              (fun ($eid:ident : String) => $accRun) (fun ($eid:ident : String) => $pf))
        pure (run', pf'?)
    | none =>
        let missingMsg := Syntax.mkStrLit s!"missing required environment variable `{ed.osKey}`"
        let run' ← `(Qed.Server.MonadServer.readEnv $keyLit >>= fun _envOpt =>
          match _envOpt with
          | some $eid:ident => $accRun
          | none => Pure.pure (Except.error (Qed.Server.ApiError.internal $missingMsg)))
        let pf'? ← accPf?.mapM fun pf =>
          `(Qed.Server.progPreservesInv_readEnv_required $keyLit $missingMsg
              (fun ($eid:ident : String) => $accRun) (fun ($eid:ident : String) => $pf))
        pure (run', pf'?)

private def elabDispatchDef (defLeaf : Name)
    (atomicBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (paramIds : Array Ident) (paramTys : Array Term) (retTy bodyTerm : Term) : SrvElabM Unit := do
  let c ← read
  let fullBody := (← liftM <| wrapWithEnvDecls c.envDecls bodyTerm).1
  let defId := mkIdentFrom c.srvIdent (c.srvName ++ defLeaf)
  liftM <| elabCommand (← `(command|
    set_option linter.unusedVariables false in
    def $defId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m]
        $[$atomicBinders:bracketedBinder]*
        ($(c.ctxId):ident : Qed.Server.RequestCtx) $[($paramIds:ident : $paramTys:term)]* :
        m (Except Qed.Server.ApiError $retTy) :=
      $fullBody))

def elabServerDispatchCmds
    (methodInfos : Array ServerMethodInfo) (dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (chanNames : Array String) (wsDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (httpDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr) := #[])
    (jobNames : Array String := #[])
    (onCreateRun? : Option Term := none) (onSignInRun? : Option Term := none) : SrvElabM Unit := do
  let c ← read
  if c.hasState then
    let linThmId := mkIdentFrom c.srvIdent (c.srvName ++ `concurrent_linearizable)
    liftM <| elabCommand (← `(command|
      theorem $linThmId {Out : Type}
          (st : Qed.Server.MultiCoreState $(c.stateId) Out)
          (hsched : Qed.Server.MultiCoreSchedule $(c.stateInvId) ⟨$(c.initStateId), []⟩ st) :
          $(c.stateInvId) st.shared :=
        Qed.Server.concurrent_schedule_preserves_inv $(c.stateInvId) $(c.initStateId) st $(c.invInitId) hsched))

  let (reqSecrets, usedExts) ← collectServerSecretsAndExts
  let mkStrArr (ss : Array String) : Array Term := ss.map (Syntax.mkStrLit ·)
  for cmd in #[
    ← `(command| def $(mkIdentFrom c.srvIdent (c.srvName ++ `secrets)) : Array String := #[$(mkStrArr reqSecrets),*]),
    ← `(command| theorem $(mkIdentFrom c.srvIdent (c.srvName ++ `_qed_server_marker)) : True := True.intro),
    ← `(command| def $(mkIdentFrom c.srvIdent (c.srvName ++ `readOnlyMethods)) : Array String := #[$(mkStrArr ((methodInfos.filter (·.isReadOnly)).map (·.name))),*]),
    ← `(command| def $(mkIdentFrom c.srvIdent (c.srvName ++ `methods)) : List String := [$(mkStrArr (methodInfos.map (·.name))),*]),
    ← `(command| def $(mkIdentFrom c.srvIdent (c.srvName ++ `channels)) : List String := [$(mkStrArr chanNames),*])
  ] do liftM <| elabCommand cmd

  let atomicBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ←
    if c.hasState then pure #[← `(bracketedBinder| [Qed.Server.MonadAtomic $(c.stateId) m])] else pure #[]
  let strTy ← `(String); let bytesTy ← `(ByteArray); let u8Ty ← `(UInt8)

  let methodVar := mkIdent `method
  let rpcArms := dispatchArms.push (← `(Lean.Parser.Term.matchAltExpr|
    | _ => Pure.pure (Except.error (Qed.Server.ApiError.notFound ("unknown RPC method: " ++ $methodVar)))))
  elabDispatchDef `dispatchM atomicBinders #[methodVar, c.reqBytesId] #[strTy, bytesTy] bytesTy
    (← `(match $methodVar:ident with $[$rpcArms:matchAlt]*))

  if !chanNames.isEmpty then
    let (wsKindVar, wsChanVar, wsParamsVar, wsPayloadVar) := (mkIdent `wsKind, mkIdent `wsChannel, mkIdent `wsParams, mkIdent `wsPayload)
    let wsArms := wsDispatchArms.push (← `(Lean.Parser.Term.matchAltExpr|
      | _, _ => Pure.pure (Except.error (Qed.Server.ApiError.notFound ("unknown WebSocket channel: " ++ $wsChanVar)))))
    elabDispatchDef `wsDispatchM atomicBinders #[wsKindVar, wsChanVar, wsParamsVar, wsPayloadVar] #[u8Ty, strTy, bytesTy, bytesTy] bytesTy
      (← `(match $wsKindVar:ident, $wsChanVar:ident with $[$wsArms:matchAlt]*))

  if !httpDispatchArms.isEmpty then
    let (httpMethodVar, httpPathVar) := (mkIdent `httpMethod, mkIdent `httpPath)
    let httpArms := httpDispatchArms.push (← `(Lean.Parser.Term.matchAltExpr| | _, _ => Pure.pure (Except.ok none)))
    elabDispatchDef `httpDispatchM atomicBinders #[httpMethodVar, httpPathVar] #[strTy, strTy]
      (← `(Option Qed.Server.HttpResponse))
      (← `(match $httpMethodVar:ident, $httpPathVar:ident with $[$httpArms:matchAlt]*))

  if let some authDecl := c.authDecl? then
    if onCreateRun?.isSome || onSignInRun?.isSome then
      let hookKindVar := mkIdent `hookKind
      let (authUserVar, hFromCtxVar, hAuthId, hAuthEqId) := (mkIdent `_authUser, mkIdent `_hFromCtx, mkIdent `_hAuth, mkIdent `_hAuthEq)
      let fromCtxId := mkIdentFrom c.srvIdent (authDecl.info.authName ++ `fromCtx)
      let fromCtxUserIdThm := mkIdentFrom c.srvIdent (authDecl.info.authName ++ `fromCtx_userId)
      let createBody ← match onCreateRun? with | some t => pure t | none => `(Pure.pure (Except.ok ()))
      let signInBody ← match onSignInRun? with | some t => pure t | none => `(Pure.pure (Except.ok ()))
      let authBody ← `(
        match $hFromCtxVar:ident : $fromCtxId $(c.ctxId) with
        | Option.none => Pure.pure (Except.error (Qed.Server.ApiError.unauthorized "missing authenticated user"))
        | Option.some $authUserVar:ident =>
            have $hAuthEqId:ident : Option.some (($authUserVar).id) = ($(c.ctxId)).userId :=
              $fromCtxUserIdThm $(c.ctxId) $authUserVar $hFromCtxVar
            have $hAuthId:ident : ($(c.ctxId)).userId ≠ Option.none := by
              intro _hNone; rw [_hNone] at $hAuthEqId:ident; cases $hAuthEqId:ident
            match $hookKindVar:ident with
            | (0 : UInt8) => $createBody
            | (1 : UInt8) => $signInBody
            | _           => Pure.pure (Except.ok ()))
      elabDispatchDef `authHookM atomicBinders #[hookKindVar] #[u8Ty] (← `(Unit)) authBody

  modifyEnv fun env => serverRegistry.addEntry env {
    serverName := c.fullSrvName, shortName := c.srvShort, hasState := c.hasState
    secrets := reqSecrets
    envVars := c.envDecls.map fun e => (e.ident.getId.toString, e.osKey, e.default?)
    externalServices := usedExts, methods := methodInfos, channels := chanNames, jobs := jobNames
    databases := c.dbDecls.map (·.info.configConst)
    authName? := c.authDecl?.map (·.info.authName)
    authConfig? := c.authDecl?.map (·.info.configConst)
    hasOnCreateAccount := onCreateRun?.isSome, hasOnSignIn := onSignInRun?.isSome
    hasHttpRoutes := !httpDispatchArms.isEmpty
  }

def elabServerFnInvariants (isAsync : Bool) (fnStr : String) (fnIdent targetId : Ident)
    (allBinderIds : Array Ident) (allBinderTys : Array Term) (targetCall : Term) : SrvElabM Bool := do
  let c ← read
  let fnLit := Syntax.mkStrLit fnStr
  let sOldId := mkIdent (if isAsync then `_sOld else `_s0)
  let sNewId := mkIdent `_sNew
  let emitStepRelInv (suffix lbl : String) (asyncRel pureGoal : Term) : SrvElabM Bool := do
    let thmId := mkIdentFrom fnIdent (c.srvName ++ fnIdent.getId.appendAfter suffix)
    let lblLit := Syntax.mkStrLit lbl
    if isAsync then
      liftM <| elabCommand (← `(command|
        theorem $thmId $[($allBinderIds:ident : $allBinderTys:term)]* :
            Qed.Server.ProgPreservesStepRel $(c.stateInvId)
              (fun ($sOldId:ident $sNewId:ident : $(c.stateId)) => $asyncRel)
              ($targetCall : Qed.Server.ThreadProg $(c.stateId) _) := by
          qedSrvProveAsync $targetId [$(c.stateInvId)] $fnLit $lblLit))
    else
      liftM <| elabCommand (← `(command|
        theorem $thmId ($sOldId:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]*
            (_hInv : $(c.stateInvId) $sOldId) : $pureGoal := by
          qedSrvProveStep [$(c.stateInvId), $targetId] $fnLit $lblLit))
    return !(← hasSrvErrors)
  let mut twoIdx := 0
  for inv in c.invs do
    if inv.isTwoSt then
      let twoCtx : LowerCtx := {
        fnName := "invariant", stateFields := c.stateFieldNames, envVars := c.envVarNames, locals := #[]
        stateRule := .invariantProp sNewId sOldId false
        allowAwait := false, allowUnwrap := false, hasFallible := false, isOption := false, innerOptTy? := none
      }
      let relProp := (← liftM <| (lowerExpr twoCtx .propInv inv.exprStx).run {}).1
      let pureGoal ← `(Qed.Server.srvWithNewState (($targetCall).1) (fun ($sNewId:ident : $(c.stateId)) => $relProp))
      unless (← emitStepRelInv s!"_twoInv{twoIdx}" inv.label relProp pureGoal) do return false
      twoIdx := twoIdx + 1
  for (mi, mutIdx) in c.mutInvs.zipIdx do
    let miCtx : LowerCtx := {
      fnName := fnStr, stateFields := #[], envVars := c.envVarNames, locals := #[]
      stateRule := .statelessServer, allowAwait := false, allowUnwrap := false
      hasFallible := false, isOption := false, innerOptTy? := none
    }
    let miProp := (← liftM <| (lowerExpr miCtx .propInv mi.condStx).run {}).1
    let fldId := mi.fieldId
    let asyncRel ← `(($sNewId).$fldId:ident = ($sOldId).$fldId:ident ∨ $miProp)
    let pureGoal ← `((($targetCall).1).$fldId:ident = ($sOldId).$fldId:ident ∨ $miProp)
    unless (← emitStepRelInv s!"_mutInv{mutIdx}" mi.label asyncRel pureGoal) do return false
  return true

structure FnEnsSpec where
  ensId    : Ident
  postFn   : Term → CommandElabM Term
  labelStr : String

def elabAsyncEnsuresThm (fnStr : String) (fnIdent handlerId : Ident)
    (stateInvTerm stateTyTerm payloadTerm errTyTerm : Term)
    (allBinderIds : Array Ident) (allBinderTys : Array Term)
    (hCall : Term) (extraUnfoldIds : Array Ident) (ensSpec : FnEnsSpec) : SrvElabM Bool := do
  let c ← read
  let ensThmId := mkIdentFrom fnIdent (c.srvName ++ fnIdent.getId.appendAfter "_ensures")
  let outVar := mkIdent `_srvOut
  let postBody ← liftM <| ensSpec.postFn ⟨outVar.raw⟩
  let ensLbl := Syntax.mkStrLit s!"ensures: {ensSpec.labelStr}"
  let fnLit := Syntax.mkStrLit fnStr
  let unfoldIds := extraUnfoldIds.push ensSpec.ensId
  liftM <| elabCommand (← `(command|
    theorem $ensThmId $[($allBinderIds:ident : $allBinderTys:term)]* :
        Qed.Server.ProgEnsures $stateInvTerm
          (fun ($outVar:ident : Except $errTyTerm $payloadTerm) => $postBody)
          ($hCall : Qed.Server.ThreadProg $stateTyTerm _) := by
      qedSrvProveAsyncEnsures $handlerId [$[$unfoldIds],*] $fnLit $ensLbl))
  return !(← hasSrvErrors)

/-- Elaborates a server handler (stateful pure, stateful async, or stateless) and schedules its
    invariant/`ensures` proofs. Returns `(runExpr, isReadOnly, hasEmit)`. -/
def elabServerHandler (isAsync : Bool) (fnStr : String) (fnIdent : Ident)
    (allBinderIds : Array Ident) (allBinderTys : Array Term) (callArgs : Array Term)
    (payloadTerm errTyTerm : Term) (baseCtx : LowerCtx) (bodyStmts : Array Syntax)
    (ensSpec? : Option FnEnsSpec) : SrvElabM (Option (Term × Bool × Bool)) := do
  let c ← read
  let fnLit := Syntax.mkStrLit fnStr
  let hasEmit := blockHasEmit bodyStmts
  if c.hasState && !isAsync then
    let s0Id := mkIdent `_s0
    let es0Id := mkIdent `_es0
    let pureCtx := if hasEmit then { baseCtx with emitAcc? := some es0Id } else baseCtx
    let (pureBody, lSt) ← liftM <| (lowerPureBlock pureCtx (inAtomic := false) s0Id s0Id bodyStmts).run {}
    recordSrvExtRoots lSt.extRoots
    let isReadOnly := lSt.mutated.isEmpty
    let stepId := mkIdentFrom fnIdent (c.srvName ++ fnIdent.getId.appendAfter "_step")
    if hasEmit then
      liftM <| elabCommand (← `(command|
        set_option linter.unusedVariables false in
        def $stepId ($s0Id:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]* :
            $(c.stateId) × (Except $errTyTerm $payloadTerm × List Qed.Server.WsEmit) :=
          Qed.Server.srvFinishEmit $s0Id (let $es0Id:ident : List Qed.Server.WsEmit := []; $pureBody)))
    else
      liftM <| elabCommand (← `(command|
        set_option linter.unusedVariables false in
        def $stepId ($s0Id:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]* :
            $(c.stateId) × Except $errTyTerm $payloadTerm :=
          Qed.Server.srvFinish $s0Id $pureBody))
    if (← hasSrvErrors) then return none

    let stepCall ← allBinderIds.foldlM (init := ← `($stepId $s0Id)) fun acc id => `($acc $id)
    if isReadOnly then
      let roThmId := mkIdentFrom fnIdent (c.srvName ++ fnIdent.getId.appendAfter "_readOnly")
      let roLbl := Syntax.mkStrLit s!"{fnStr} read-only state preservation"
      deferSrvCmd (← `(command|
        theorem $roThmId ($s0Id:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]* :
            ($stepCall).1 = $s0Id := by
          qedSrvProveStep [$stepId] $fnLit $roLbl))
    else
      let invThmId := mkIdentFrom fnIdent (c.srvName ++ fnIdent.getId.appendAfter "_inv")
      let singleInvLbl := Syntax.mkStrLit (singleInvLabelStr c.invs)
      let invCmd ← `(command|
        theorem $invThmId ($s0Id:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]*
            (_hInv : $(c.stateInvId) $s0Id) :
            $(c.stateInvId) ($stepCall).1 := by
          qedSrvProveStep [$(c.stateInvId), $stepId] $fnLit $singleInvLbl)
      deferSrvProof do
        elabCommand invCmd
        if hasNewErrors (← get).messages c.priorRep c.priorUnrep then return false
        (elabServerFnInvariants false fnStr fnIdent stepId allBinderIds allBinderTys stepCall).run c

    if let some ensSpec := ensSpec? then
      let ensId := ensSpec.ensId
      let ensThmId := mkIdentFrom fnIdent (c.srvName ++ fnIdent.getId.appendAfter "_ensures")
      let outProj ← if hasEmit then `(($stepCall).2.1) else `(($stepCall).2)
      let postGoal ← liftM <| ensSpec.postFn outProj
      let ensLbl := Syntax.mkStrLit s!"ensures: {ensSpec.labelStr}"
      deferSrvCmd (← `(command|
        theorem $ensThmId ($s0Id:ident : $(c.stateId)) $[($allBinderIds:ident : $allBinderTys:term)]*
            (_hInv : $(c.stateInvId) $s0Id) : $postGoal := by
          qedSrvProveStep [$(c.stateInvId), $stepId, $ensId] $fnLit $ensLbl))

    let snapCall ← callArgs.foldlM (init := ← `($stepId _sSnap)) fun acc a => `($acc $a)
    let rawRun ← if isReadOnly then
      `(Qed.Server.MonadAtomic.runAtomicRead (fun (_sSnap : $(c.stateId)) => ($snapCall).2))
    else
      `(Qed.Server.MonadAtomic.runAtomic (fun (_sSnap : $(c.stateId)) => $snapCall))
    let runExpr ← if hasEmit then
      `($rawRun >>= fun _emitPair => Qed.Server.flushWsEmits (_emitPair).2 >>= fun _ => Pure.pure (_emitPair).1)
    else pure rawRun
    return some (runExpr, isReadOnly, hasEmit)
  else
    let stateTyTerm? : Option Term := if c.hasState then some ⟨c.stateId.raw⟩ else none
    let (asyncBody, lSt) ← liftM <| (lowerAsyncBlock baseCtx stateTyTerm? bodyStmts).run {}
    recordSrvExtRoots lSt.extRoots
    let isReadOnly := lSt.mutated.isEmpty && !lSt.dbWrite
    let handlerId := mkIdentFrom fnIdent (c.srvName ++ fnIdent.getId.appendAfter "_handler")
    let atomicBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ←
      if c.hasState then pure #[← `(bracketedBinder| [Qed.Server.MonadAtomic $(c.stateId) m])] else pure #[]
    liftM <| elabCommand (← `(command|
      set_option linter.unusedVariables false in
      def $handlerId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m]
          $[$atomicBinders:bracketedBinder]*
          $[($allBinderIds:ident : $allBinderTys:term)]* :
          m (Except $errTyTerm $payloadTerm) :=
        Qed.Server.srvFinishM $asyncBody))
    if (← hasSrvErrors) then return none

    let hCall ← allBinderIds.foldlM (init := ← `($handlerId)) fun acc id => `($acc $id)
    if c.hasState then
      let asyncInvId := mkIdentFrom fnIdent (c.srvName ++ fnIdent.getId.appendAfter "_inv")
      let singleInvLbl := Syntax.mkStrLit (singleInvLabelStr c.invs)
      let invCmd ← `(command|
        theorem $asyncInvId $[($allBinderIds:ident : $allBinderTys:term)]* :
            Qed.Server.ProgPreservesInv $(c.stateInvId)
              ($hCall : Qed.Server.ThreadProg $(c.stateId) _) := by
          qedSrvProveAsync $handlerId [$(c.stateInvId)] $fnLit $singleInvLbl)
      deferSrvProof do
        elabCommand invCmd
        if hasNewErrors (← get).messages c.priorRep c.priorUnrep then return false
        (elabServerFnInvariants true fnStr fnIdent handlerId allBinderIds allBinderTys hCall).run c

    if let some ensSpec := ensSpec? then
      let (invT, tyT, extra) ← if c.hasState then pure (⟨c.stateInvId.raw⟩, ⟨c.stateId.raw⟩, #[c.stateInvId])
        else pure (← `(fun _ : Unit => True), ← `(Unit), #[])
      deferSrvProof <| (elabAsyncEnsuresThm fnStr fnIdent handlerId invT tyT payloadTerm errTyTerm
        allBinderIds allBinderTys hCall extra ensSpec).run c

    let hApp ← callArgs.foldlM (init := ← `($handlerId)) fun acc a => `($acc $a)
    return some (hApp, isReadOnly, hasEmit)

end SrvHelpers

end Qed.Server
