import Qed.Server.Lower

namespace Qed.Server
open Qed.Lang

/-! ## `server` Command Elaborator -/

structure ParsedEnvDecl where
  ref      : Lean.Syntax
  ident    : Lean.Ident
  osKey    : String
  default? : Option String

structure ParsedStateDecl where
  ref      : Lean.Syntax
  ident    : Lean.Ident
  ty       : ParsedSrvType
  initStx  : Lean.Syntax

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

private def singleInvLabelStr (invs : Array ParsedInv) : String :=
  let ss := ((invs.filter (!·.isTwoSt)).toList.map (·.label)).eraseDups
  if ss.isEmpty then "StateInv" else String.intercalate ", " ss

structure ParsedFnParam where
  ident    : Lean.Ident
  ty       : ParsedSrvType
  tyTerm   : Lean.Term

open Lean Elab Command in
def buildTupleType (tys : Array Term) : CommandElabM Term := do
  if tys.isEmpty then `(Unit)
  else if tys.size == 1 then return tys[0]!
  else
    let mut acc := tys.back!
    for revIdx in [1:tys.size] do
      acc ← `($(tys[tys.size - 1 - revIdx]!) × $acc)
    return acc

open Lean Elab Command in
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

open Lean Elab Command in
def computeInnerOptTerm? (retTy : ParsedSrvType) : CommandElabM (Option Term) := do
  let nonErrMods := retTy.mods.filter (· != .fallible)
  if nonErrMods.back? == some .option then
    let innerParsed : ParsedSrvType := {
      retTy with mods := nonErrMods.extract 0 (nonErrMods.size - 1)
    }
    some <$> liftMacroM innerParsed.toPayloadTerm
  else
    return none

open Lean Elab Command in
def filterNewWarnings (arr : Lean.PersistentArray Lean.Message) (priorSize : Nat) :
    Lean.PersistentArray Lean.Message :=
  let lst := arr.toList
  let before := lst.take priorSize
  let after := (lst.drop priorSize).filter (·.severity != .warning)
  (before ++ after).foldl (fun acc m => acc.push m) {}

open Lean Elab Command in
def hasNewErrors (log : Lean.MessageLog) (priorRep priorUnrep : Nat) : Bool :=
  (log.reported.toList.drop priorRep).any (·.severity == .error) ||
  (log.unreported.toList.drop priorUnrep).any (·.severity == .error)

open Lean Elab Command in
def elabServerStateCmds (priorRep priorUnrep : Nat) (stateId initStateId stateInvId invInitId : Ident)
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
  let invBody ← buildPropConj singleProps
  let singleInvStr := singleInvLabelStr invs
  let initInvLbl := Syntax.mkStrLit ("init: " ++ singleInvStr)
  elabCommand (← `(command|
    def $stateInvId ($sParam:ident : $stateId) : Prop := $invBody))
  elabCommand (← `(command|
    theorem $invInitId : $stateInvId $initStateId := by
      qedSrvProveStep [$stateInvId, $initStateId] "initState" $initInvLbl))
  return !hasNewErrors (← get).messages priorRep priorUnrep

structure ParsedDbDecl where
  ref        : Lean.Syntax
  aliasIdent : Lean.Ident
  dbRefIdent : Lean.Ident
  info       : DatabaseInfo

structure ParsedServerBlock where
  dbDecls     : Array ParsedDbDecl
  envDecls    : Array ParsedEnvDecl
  stateDecls  : Array ParsedStateDecl
  mutInvs     : Array ParsedMutInv
  invs        : Array ParsedInv
  fnClauses   : Array Lean.Syntax
  chanClauses : Array Lean.Syntax

open Lean Elab Command in
def parseServerClauses (srvIdent : Ident) (srvName : Name) (clauses : Array Lean.Syntax) :
    CommandElabM ParsedServerBlock := do
  let mut dbDecls     : Array ParsedDbDecl := #[]
  let mut envDecls    : Array ParsedEnvDecl := #[]
  let mut stateDecls  : Array ParsedStateDecl := #[]
  let mut mutInvs     : Array ParsedMutInv := #[]
  let mut invs        : Array ParsedInv := #[]
  let mut seenInvNames : Array Name := #[]
  let mut fnClauses   : Array Syntax := #[]
  let mut chanClauses : Array Syntax := #[]
  for c in clauses do
    let k := c.getKind
    if k == ``srvDbClause then
      let aliasId : Ident := ⟨(c.getArg 1)⟩
      let dbRefId : Ident := ⟨(c.getArg 3)⟩
      if dbDecls.any (·.aliasIdent.getId == aliasId.getId) ||
         envDecls.any (·.ident.getId == aliasId.getId) ||
         stateDecls.any (·.ident.getId == aliasId.getId) then
        throwErrorAt aliasId s!"duplicate declaration `{aliasId.getId}` in `server {srvName}`"
      let env ← getEnv
      let some dbInfo := Qed.Server.lookupDatabase? env (← getCurrNamespace) (← getOpenDecls) dbRefId.getId
        | throwErrorAt dbRefId s!"unknown `database` `{dbRefId.getId}` in `use {aliasId.getId} : {dbRefId.getId}`"
      dbDecls := dbDecls.push { ref := c, aliasIdent := aliasId, dbRefIdent := dbRefId, info := dbInfo }
    else if k == ``srvEnvClause then
      let id : Ident := ⟨(c.getArg 1)⟩
      let osKey := (⟨(c.getArg 3)⟩ : TSyntax `str).getString
      let def? := if (c.getArg 4).getNumArgs == 2 then some ((⟨((c.getArg 4).getArg 1)⟩ : TSyntax `str).getString) else none
      if envDecls.any (·.ident.getId == id.getId) then
        throwErrorAt id s!"duplicate `env {id.getId}` in `server {srvName}`"
      envDecls := envDecls.push { ref := c, ident := id, osKey, default? := def? }
    else if k == ``srvStateClause then
      let id : Ident := ⟨(c.getArg 1)⟩
      let ty ← liftMacroM <| ParsedSrvType.parse (c.getArg 3)
      liftMacroM <| ty.validate (allowFallible := false) s!"state field `{id.getId}`"
      if stateDecls.any (·.ident.getId == id.getId) || envDecls.any (·.ident.getId == id.getId) then
        throwErrorAt id s!"duplicate declaration `{id.getId}` in `server {srvName}`"
      let initStx : Syntax ←
        if (c.getArg 4).getNumArgs == 2 then
          pure ((c.getArg 4).getArg 1)
        else if ty.mods.back? == some .array then
          pure (Syntax.node (.fromRef c) ``qedArrLit
            #[Syntax.atom (.fromRef c) "[", Syntax.node (.fromRef c) Lean.nullKind #[], Syntax.atom (.fromRef c) "]"])
        else if ty.mods.back? == some .option then
          pure (Syntax.node (.fromRef c) ``qedIdent #[mkIdentFrom c `none])
        else
          throwErrorAt id s!"state field `{id.getId}` requires an initial value `= ...`"
      stateDecls := stateDecls.push { ref := c, ident := id, ty, initStx }
    else if k == ``srvInvMutatingClause then
      let nameId : Ident := ⟨(c.getArg 1)⟩
      if seenInvNames.contains nameId.getId then
        throwErrorAt nameId s!"duplicate invariant `{nameId.getId}` in `server {srvName}`"
      seenInvNames := seenInvNames.push nameId.getId
      let fid : Ident := ⟨(c.getArg 4)⟩
      let cond := (c.getArg 6)
      let lbl := s!"mutating:{nameId.getId}"
      mutInvs := mutInvs.push { ref := c, name := nameId, fieldId := fid, condStx := cond, label := lbl }
    else if k == ``srvInvClause then
      let nameId : Ident := ⟨(c.getArg 1)⟩
      if seenInvNames.contains nameId.getId then
        throwErrorAt nameId s!"duplicate invariant `{nameId.getId}` in `server {srvName}`"
      seenInvNames := seenInvNames.push nameId.getId
      for e in (c.getArg 3).getSepArgs do
        invs := invs.push { ref := c, name := nameId, exprStx := e, isTwoSt := exprCallsOld e, label := nameId.getId.toString }
    else if k == ``srvFnClause then
      fnClauses := fnClauses.push c
    else if k == ``srvChannelClause then
      chanClauses := chanClauses.push c
    else
      throwErrorAt c "unexpected clause in `server` block"
  if fnClauses.isEmpty && chanClauses.isEmpty then
    throwErrorAt srvIdent s!"`server {srvName}` must declare at least one `def` or `channel`"
  let hasState := !stateDecls.isEmpty
  if !hasState && (!invs.isEmpty || !mutInvs.isEmpty) then
    throwErrorAt srvIdent s!"`server {srvName}` declares `invariant`s but has no `state` fields"
  for mi in mutInvs do
    unless stateDecls.any (·.ident.getId == mi.fieldId.getId) do
      let avail := String.intercalate ", " (stateDecls.toList.map fun s => s!"`{s.ident.getId}`")
      throwErrorAt mi.fieldId s!"`invariant mutating {mi.fieldId.getId}` does not match any `state` field of `{srvName}` (`state` fields: {avail})"
  return { dbDecls, envDecls, stateDecls, mutInvs, invs, fnClauses, chanClauses }

section
open Lean Elab Command

partial def splitSrvAnd (stx : Syntax) : Array Syntax :=
  let u := unwrapParens1 stx
  if u.getKind == ``qedAnd then splitSrvAnd (u.getArg 0) ++ splitSrvAnd (u.getArg 2)
  else #[u]

partial def scanCtxEnv (envVars : Array String) (locals : Array String) (stx : Syntax) : Bool × Bool :=
  let k := stx.getKind
  if k == ``qedIdent then
    match (stx.getArg 0).getId.components with
    | [] => (false, false)
    | root :: _ =>
        let r := root.toString
        if locals.contains r then (false, false)
        else if r == "ctx" then (true, false)
        else if envVars.contains r then (false, true)
        else (false, false)
  else if k == ``qedProj then
    scanCtxEnv envVars locals (stx.getArg 0)
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
    let ps := (stx.getArg 1).getSepArgs.map (·.getId.toString)
    scanCtxEnv envVars (locals ++ ps) (stx.getArg 3)
  else
    stx.getArgs.foldl (fun (ac, ae) ch =>
      let (c, e) := scanCtxEnv envVars locals ch
      (ac || c, ae || e)) (false, false)

def isAuthReqLabel (s : String) : Bool :=
  s.contains "ctx.userId" || s.contains "ctx.isAuthenticated" || s.contains "ctx.bearerToken"

def isAuthReqExpr (stx : Syntax) : Bool :=
  isAuthReqLabel (stx.reprint.getD "")

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
      if isAuthReqLabel rLbl then
        `(Qed.Server.ApiError.unauthorized $rMsg)
      else
        `(Qed.Server.ApiError.badRequest $rMsg)
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
  extRoots        : Array Name

def elabRequiresClauses (refIdent : Ident) (srvName fullSrvName itemName : Name)
    (fnLabel hypPrefix reqSuffix : String)
    (stateFieldNames envVarNames serverLocals clientLocals : Array String)
    (clientBindIds : Array Ident) (clientBindTys : Array Term)
    (reqExprs : Array Syntax) (excludedClientVars : Array String := #[])
    (trackAuth : Bool := true) : CommandElabM LoweredRequires := do
  let mut reqPropTerms : Array Term := #[]
  let mut reqHypIds : Array Ident := #[]
  let mut reqHypTys : Array Term := #[]
  let mut reqLabels : Array String := #[]
  let mut clientReqProps : Array Term := #[]
  let mut clientReqLabels : Array String := #[]
  let mut requiresAuth := false
  let mut extRoots : Array Name := #[]
  for idx in [0:reqExprs.size] do
    let rExpr := reqExprs[idx]!
    if exprHasAwait rExpr then
      throwErrorAt rExpr "`requires` precondition cannot contain `await`"
    let reqCtx : LowerCtx := {
      fnName := fnLabel, stateFields := stateFieldNames, envVars := envVarNames, locals := serverLocals
      stateRule := .forbidInRequires, allowAwait := false, allowUnwrap := false
      hasFallible := false, isOption := false, innerOptTy? := none
    }
    let (pTerm, rSt) ← (lowerExpr reqCtx .propGuard rExpr).run {}
    extRoots := extRoots ++ rSt.extRoots.filter (!extRoots.contains ·)
    let hId := mkIdent (Name.mkSimple s!"{hypPrefix}{idx}")
    reqPropTerms := reqPropTerms.push pTerm
    reqHypIds := reqHypIds.push hId
    reqHypTys := reqHypTys.push pTerm
    reqLabels := reqLabels.push ((rExpr.reprint.getD "requires").trimAscii.toString)
    for conj in splitSrvAnd rExpr do
      let (mentionsCtx, mentionsEnv) := scanCtxEnv envVarNames serverLocals conj
      if trackAuth && mentionsCtx && !mentionsEnv && isAuthReqExpr conj then
        requiresAuth := true
      else if !mentionsCtx && !mentionsEnv then
        let mentionsExcl := !excludedClientVars.isEmpty && (scanCtxEnv excludedClientVars clientLocals conj).2
        if !mentionsExcl then
          let cliReqCtx : LowerCtx := {
            fnName := fnLabel, stateFields := stateFieldNames, envVars := #[], locals := clientLocals
            stateRule := .forbidInRequires, allowAwait := false, allowUnwrap := false
            hasFallible := false, isOption := false, innerOptTy? := none, forbidCtxEnv := true
          }
          let (cpTerm, _) ← (lowerExpr cliReqCtx .propInv conj).run {}
          clientReqProps := clientReqProps.push cpTerm
          clientReqLabels := clientReqLabels.push ((conj.reprint.getD "requires").trimAscii.toString)
  let (clientReqId?, clientReqConst?) ←
    if clientReqProps.isEmpty then pure (none, none)
    else
      let leaf := itemName.appendAfter reqSuffix
      let cid := mkIdentFrom refIdent (srvName ++ leaf)
      let reqConj ← buildPropConj clientReqProps
      elabCommand (← `(command|
        set_option linter.unusedVariables false in
        @[simp] abbrev $cid $[($clientBindIds:ident : $clientBindTys:term)]* : Prop := $reqConj))
      pure (some cid, some (fullSrvName ++ leaf))
  return {
    reqPropTerms, reqHypIds, reqHypTys, reqLabels, requiresAuth,
    clientReqId?, clientReqConst?,
    clientReqLabel := String.intercalate " && " clientReqLabels.toList,
    extRoots
  }

def elabStatelessHandler (priorRep priorUnrep : Nat) (refIdent : Ident)
    (srvName handlerLeaf : Name) (allBinderIds : Array Ident) (allBinderTys : Array Term)
    (callArgs : Array Term) (retTyTerm errTyTerm : Term) (baseCtx : LowerCtx)
    (bodyStmts : Array Syntax) : CommandElabM (Option (Ident × Term × Term × Array Name × Bool)) := do
  let (statelessBody, lSt) ← (lowerAsyncBlock baseCtx none bodyStmts).run {}
  let handlerId := mkIdentFrom refIdent (srvName ++ handlerLeaf.appendAfter "_handler")
  elabCommand (← `(command|
    set_option linter.unusedVariables false in
    def $handlerId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m]
        $[($allBinderIds:ident : $allBinderTys:term)]* :
        m (Except $errTyTerm $retTyTerm) :=
      Qed.Server.srvFinishM $statelessBody))
  if hasNewErrors (← get).messages priorRep priorUnrep then return none
  let hCall ← allBinderIds.foldlM (init := ← `($handlerId)) fun acc a => `($acc $a)
  let hApp ← callArgs.foldlM (init := ← `($handlerId)) fun acc a => `($acc $a)
  return some (handlerId, hCall, hApp, lSt.extRoots, lSt.dbWrite)

private partial def scanFailCallsAux (stx : Syntax) (tags : Array Ident) (hasPlain : Bool) :
    CommandElabM (Array Ident × Bool) := do
  if stx.getKind == ``qedCall && (stx.getArg 0).getKind == ``qedIdent && ((stx.getArg 0).getArg 0).getId == `fail then
    let rawArgs := (stx.getArg 2).getSepArgs
    if (rawArgs.size == 1 || rawArgs.size == 2) && (unwrapParens1 rawArgs[0]![0]).getKind == ``qedDotIdent then
      let tagId : Ident := ⟨(unwrapParens1 rawArgs[0]![0])[1]⟩
      let tags' := if tags.any (·.getId == tagId.getId) then tags else tags.push tagId
      if rawArgs.size == 2 then
        scanFailCallsAux rawArgs[1]! tags' hasPlain
      else
        return (tags', hasPlain)
    else
      let mut curTags := tags
      let mut curPlain := true
      for arg in rawArgs do
        let (t', p') ← scanFailCallsAux arg curTags curPlain
        curTags := t'; curPlain := p'
      return (curTags, curPlain)
  else
    let mut curTags := tags
    let mut curPlain := hasPlain
    for ch in stx.getArgs do
      let (t', p') ← scanFailCallsAux ch curTags curPlain
      curTags := t'; curPlain := p'
    return (curTags, curPlain)

def scanBodyFailTags (stmts : Array Syntax) : CommandElabM (Array Ident × Bool) := do
  let mut tags : Array Ident := #[]
  let mut hasPlain := false
  for st in stmts do
    let (t', p') ← scanFailCallsAux st tags hasPlain
    tags := t'; hasPlain := p'
  return (tags, hasPlain)

private def mkErrDotTerm (tid : Ident) : Term :=
  ⟨Syntax.node (.fromRef tid) ``Lean.Parser.Term.dotIdent #[Syntax.atom (.fromRef tid) ".", tid]⟩

private def elabDomainErrorJsonInsts (errTypeId : Ident) (tagIdents : Array Ident) : CommandElabM Unit := do
  let toStrAlts ← tagIdents.mapM fun tid => do
    let tLit := Syntax.mkStrLit tid.getId.toString
    `(Lean.Parser.Term.matchAltExpr| | $(mkErrDotTerm tid) => $tLit)
  let fromJsonAlts ← tagIdents.mapM fun tid => do
    let tLit := Syntax.mkStrLit tid.getId.toString
    `(Lean.Parser.Term.matchAltExpr| | Qed.Json.str $tLit => Except.ok $(mkErrDotTerm tid))
  let fromJsonAltsAll := fromJsonAlts.push (← `(Lean.Parser.Term.matchAltExpr| | _ => Except.error "invalid RPC error tag"))
  elabCommand (← `(command| instance : ToString $errTypeId where toString e := match e with $[$toStrAlts:matchAlt]*))
  elabCommand (← `(command| instance : Qed.ToJson $errTypeId := ⟨fun e => Qed.Json.str (toString e)⟩))
  elabCommand (← `(command| instance : Qed.FromJson $errTypeId where fromJson j := match j with $[$fromJsonAltsAll:matchAlt]*))
  elabCommand (← `(command|
    instance : Qed.LawfulJson $errTypeId where
      depthBound := 0
      depth_toJson _ := Nat.le_refl 0
      fromJson_toJson e := by cases e <;> rfl))
  elabCommand (← `(command| instance : Qed.NonNullJson $errTypeId := ⟨nofun⟩))

private def elabDomainErrorProtoInsts (errTypeId : Ident) (tagIdents : Array Ident) : CommandElabM Unit := do
  let toProtoAlts ← tagIdents.zipIdx.mapM fun (tid, i) => do
    let iLit := Syntax.mkNumLit (toString i)
    `(Lean.Parser.Term.matchAltExpr| | $(mkErrDotTerm tid) => Qed.Proto.WireVal.varint $iLit)
  let fromProtoAlts ← tagIdents.zipIdx.mapM fun (tid, i) => do
    let iLit := Syntax.mkNumLit (toString i)
    `(Lean.Parser.Term.matchAltExpr| | Qed.Proto.WireVal.varint $iLit => Except.ok $(mkErrDotTerm tid))
  let fromProtoAltsAll := fromProtoAlts.push (← `(Lean.Parser.Term.matchAltExpr| | _ => Except.error "protobuf: invalid RPC error tag"))
  elabCommand (← `(command| instance : Qed.ToProto $errTypeId where toProtoVal e := match e with $[$toProtoAlts:matchAlt]*))
  elabCommand (← `(command| instance : Qed.FromProto $errTypeId where fromProtoVal w := match w with $[$fromProtoAltsAll:matchAlt]*))
  elabCommand (← `(command| instance : Qed.LawfulProto $errTypeId := Qed.LawfulProto.ofScalar (by intro e; cases e <;> rfl)))

def elabDomainErrorType (srvName : Name) (fnIdent : Ident) (tagIdents : Array Ident) :
    CommandElabM Ident := do
  let errTypeId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId ++ `Error)
  let ctors ← tagIdents.mapM fun tid =>
    `(Lean.Parser.Command.ctor| | $tid:ident)
  elabCommand (← `(command|
    inductive $errTypeId where
      $[$ctors:ctor]*
    deriving Inhabited, DecidableEq, Repr))
  elabDomainErrorJsonInsts errTypeId tagIdents
  elabDomainErrorProtoInsts errTypeId tagIdents
  return errTypeId

end

open Lean Elab Command in
private def collectServerSecretsAndExts (dbDecls : Array ParsedDbDecl)
    (envDecls : Array ParsedEnvDecl) (allExtRoots : Array Name) :
    CommandElabM (Array String × Array (String × String)) := do
  let extMap := externalRegistry.getState (← getEnv)
  let mut reqSecrets : Array String := #[]
  for dbd in dbDecls do
    if !dbd.info.hasDevFallback then
      for sec in dbd.info.secrets do
        unless reqSecrets.contains sec do
          reqSecrets := reqSecrets.push sec
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
  return (reqSecrets, usedExts)

open Lean Elab Command in
private def wrapDispatchWithEnvDecls (envDecls : Array ParsedEnvDecl) (innerTerm : Term) :
    CommandElabM Term :=
  envDecls.foldrM (init := innerTerm) fun ed acc => do
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

open Lean Elab Command in
private def elabServerWsDispatchCmd (srvIdent ctxId : Ident) (srvName : Name)
    (envDecls : Array ParsedEnvDecl) (atomicBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder))
    (wsDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr)) : CommandElabM Unit := do
  let wsKindVar := mkIdent `wsKind
  let wsChanVar := mkIdent `wsChannel
  let wsParamsVar := mkIdent `wsParams
  let wsPayloadVar := mkIdent `wsPayload
  let wsNotFoundArm ← `(Lean.Parser.Term.matchAltExpr|
    | _, _ => Pure.pure (Except.error (Qed.Server.ApiError.notFound ("unknown WebSocket channel: " ++ $wsChanVar))))
  let allWsArms := wsDispatchArms.push wsNotFoundArm
  let wsMatchTerm ← `(match $wsKindVar:ident, $wsChanVar:ident with $[$allWsArms:matchAlt]*)
  let fullWsBody ← wrapDispatchWithEnvDecls envDecls wsMatchTerm
  let wsDispatchId := mkIdentFrom srvIdent (srvName ++ `wsDispatchM)
  elabCommand (← `(command|
    set_option linter.unusedVariables false in
    def $wsDispatchId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m]
        $[$atomicBinders:bracketedBinder]*
        ($ctxId:ident : Qed.Server.RequestCtx) ($wsKindVar:ident : UInt8) ($wsChanVar:ident : String)
        ($wsParamsVar:ident : ByteArray) ($wsPayloadVar:ident : ByteArray) :
        m (Except Qed.Server.ApiError ByteArray) :=
      $fullWsBody))

open Lean Elab Command in
def elabServerDispatchCmds (srvIdent stateId initStateId stateInvId invInitId : Ident)
    (srvName fullSrvName : Name) (srvShort : String) (hasState : Bool)
    (dbDecls : Array ParsedDbDecl)
    (envDecls : Array ParsedEnvDecl) (allExtRoots : Array Name)
    (methodInfos : Array ServerMethodInfo) (dispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (chanNames : Array String) (wsDispatchArms : Array (TSyntax ``Lean.Parser.Term.matchAltExpr))
    (ctxId reqBytesId : Ident) : CommandElabM Unit := do
  if hasState then
    let linThmId := mkIdentFrom srvIdent (srvName ++ `concurrent_linearizable)
    elabCommand (← `(command|
      theorem $linThmId {Out : Type}
          (st : Qed.Server.MultiCoreState $stateId Out)
          (hsched : Qed.Server.MultiCoreSchedule $stateInvId ⟨$initStateId, []⟩ st) :
          $stateInvId st.shared :=
        Qed.Server.concurrent_schedule_preserves_inv $stateInvId $initStateId st $invInitId hsched))

  let (reqSecrets, usedExts) ← collectServerSecretsAndExts dbDecls envDecls allExtRoots

  let secretsId := mkIdentFrom srvIdent (srvName ++ `secrets)
  let secLits : Array Term := reqSecrets.map (Syntax.mkStrLit ·)
  elabCommand (← `(command| def $secretsId : Array String := #[$[$secLits],*]))

  let markerId := mkIdentFrom srvIdent (srvName ++ `_qed_server_marker)
  elabCommand (← `(command| theorem $markerId : True := True.intro))

  let readOnlyId := mkIdentFrom srvIdent (srvName ++ `readOnlyMethods)
  let roLits : Array Term := (methodInfos.filter (·.isReadOnly)).map (Syntax.mkStrLit ·.name)
  elabCommand (← `(command| def $readOnlyId : Array String := #[$[$roLits],*]))

  let methodsId := mkIdentFrom srvIdent (srvName ++ `methods)
  let mLits : Array Term := methodInfos.map (Syntax.mkStrLit ·.name)
  elabCommand (← `(command| def $methodsId : List String := [$[$mLits],*]))

  let channelsId := mkIdentFrom srvIdent (srvName ++ `channels)
  let chLits : Array Term := chanNames.map (Syntax.mkStrLit ·)
  elabCommand (← `(command| def $channelsId : List String := [$[$chLits],*]))

  let methodVar := mkIdent `method
  let notFoundArm ← `(Lean.Parser.Term.matchAltExpr|
    | _ => Pure.pure (Except.error (Qed.Server.ApiError.notFound ("unknown RPC method: " ++ $methodVar))))
  let allArms := dispatchArms.push notFoundArm
  let matchMethodTerm ← `(match $methodVar:ident with $[$allArms:matchAlt]*)
  let fullDispatchBody ← wrapDispatchWithEnvDecls envDecls matchMethodTerm

  let atomicBinders : Array (TSyntax `Lean.Parser.Term.bracketedBinder) ←
    if hasState then pure #[← `(bracketedBinder| [Qed.Server.MonadAtomic $stateId m])]
    else pure #[]

  let dispatchId := mkIdentFrom srvIdent (srvName ++ `dispatchM)
  elabCommand (← `(command|
    def $dispatchId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m]
        $[$atomicBinders:bracketedBinder]*
        ($ctxId:ident : Qed.Server.RequestCtx) ($methodVar:ident : String) ($reqBytesId:ident : ByteArray) :
        m (Except Qed.Server.ApiError ByteArray) :=
      $fullDispatchBody))

  if !chanNames.isEmpty then
    elabServerWsDispatchCmd srvIdent ctxId srvName envDecls atomicBinders wsDispatchArms

  modifyEnv fun env => serverRegistry.addEntry env {
    serverName := fullSrvName
    shortName := srvShort
    hasState
    secrets := reqSecrets
    envVars := envDecls.map fun e => (e.ident.getId.toString, e.osKey, e.default?)
    externalServices := usedExts
    methods := methodInfos
    channels := chanNames
    databases := dbDecls.map (·.info.configConst)
  }

open Lean Elab Command in
def elabServerFnInvariants (priorRep priorUnrep : Nat) (isAsync : Bool)
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
            Qed.Server.srvWithNewState (($targetCall).1) (fun ($sNewId:ident : $stateId) => $relProp) := by
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
structure FnEnsSpec where
  ensId    : Ident
  postFn   : Term → CommandElabM Term
  labelStr : String

open Lean Elab Command in
def elabServerPureFn (priorRep priorUnrep : Nat)
    (srvName : Name) (fnStr : String) (fnIdent stateId stateInvId : Ident)
    (allBinderIds : Array Ident) (allBinderTys : Array Term) (callArgs : Array Term)
    (payloadTerm errTyTerm : Term) (baseCtx : LowerCtx) (bodyStmts : Array Lean.Syntax)
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (stateFieldNames envVarNames : Array String)
    (ensSpec? : Option FnEnsSpec)
    (deferredProofs : IO.Ref (Array (CommandElabM Bool))) :
    CommandElabM (Option (Term × Bool × Array Name)) := do
  let s0Id := mkIdent `_s0
  let fnLit := Syntax.mkStrLit fnStr
  let hasEmit := blockHasEmit bodyStmts
  let es0Id := mkIdent `_es0
  let pureCtx := if hasEmit then { baseCtx with emitAcc? := some es0Id } else baseCtx
  let (pureBody, lSt) ← (lowerPureBlock pureCtx (inAtomic := false) s0Id s0Id bodyStmts).run {}
  let isReadOnly := lSt.mutated.isEmpty
  let stepId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_step")
  if hasEmit then
    elabCommand (← `(command|
      set_option linter.unusedVariables false in
      def $stepId ($s0Id:ident : $stateId) $[($allBinderIds:ident : $allBinderTys:term)]* :
          $stateId × (Except $errTyTerm $payloadTerm × List Qed.Server.WsEmit) :=
        Qed.Server.srvFinishEmit $s0Id (let $es0Id:ident : List Qed.Server.WsEmit := []; $pureBody)))
  else
    elabCommand (← `(command|
      set_option linter.unusedVariables false in
      def $stepId ($s0Id:ident : $stateId) $[($allBinderIds:ident : $allBinderTys:term)]* :
          $stateId × Except $errTyTerm $payloadTerm :=
        Qed.Server.srvFinish $s0Id $pureBody))
  if hasNewErrors (← get).messages priorRep priorUnrep then return none

  let stepCall ← allBinderIds.foldlM (init := ← `($stepId $s0Id)) fun acc id => `($acc $id)
  if isReadOnly then
    let roThmId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_readOnly")
    let roLbl := Syntax.mkStrLit s!"{fnStr} read-only state preservation"
    let cmd ← `(command|
      theorem $roThmId ($s0Id:ident : $stateId) $[($allBinderIds:ident : $allBinderTys:term)]* :
          ($stepCall).1 = $s0Id := by
        qedSrvProveStep [$stepId] $fnLit $roLbl)
    deferredProofs.modify (·.push do elabCommand cmd; return !hasNewErrors (← get).messages priorRep priorUnrep)
  else
    let invThmId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_inv")
    let singleInvLbl := Syntax.mkStrLit (singleInvLabelStr invs)
    let invCmd ← `(command|
      theorem $invThmId ($s0Id:ident : $stateId) $[($allBinderIds:ident : $allBinderTys:term)]*
          (_hInv : $stateInvId $s0Id) :
          $stateInvId ($stepCall).1 := by
        qedSrvProveStep [$stateInvId, $stepId] $fnLit $singleInvLbl)
    deferredProofs.modify (·.push do
      elabCommand invCmd
      if hasNewErrors (← get).messages priorRep priorUnrep then return false
      elabServerFnInvariants priorRep priorUnrep false srvName fnStr fnIdent stateId stateInvId
        stepId allBinderIds allBinderTys stepCall invs mutInvs stateFieldNames envVarNames)

  if let some ensSpec := ensSpec? then
    let ensId := ensSpec.ensId
    let ensThmId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_ensures")
    let outProj ← if hasEmit then `(($stepCall).2.1) else `(($stepCall).2)
    let postGoal ← ensSpec.postFn outProj
    let ensLbl := Syntax.mkStrLit s!"ensures: {ensSpec.labelStr}"
    let ensCmd ← `(command|
      theorem $ensThmId ($s0Id:ident : $stateId) $[($allBinderIds:ident : $allBinderTys:term)]*
          (_hInv : $stateInvId $s0Id) :
          $postGoal := by
        qedSrvProveStep [$stateInvId, $stepId, $ensId] $fnLit $ensLbl)
    deferredProofs.modify (·.push do elabCommand ensCmd; return !hasNewErrors (← get).messages priorRep priorUnrep)

  let snapCall ← callArgs.foldlM (init := ← `($stepId _sSnap)) fun acc a => `($acc $a)
  let rawRun ← if isReadOnly then
    `(Qed.Server.MonadAtomic.runAtomicRead (fun (_sSnap : $stateId) => ($snapCall).2))
  else
    `(Qed.Server.MonadAtomic.runAtomic (fun (_sSnap : $stateId) => $snapCall))
  let runExpr ← if hasEmit then
    `($rawRun >>= fun _emitPair => Qed.Server.flushWsEmits (_emitPair).2 >>= fun _ => Pure.pure (_emitPair).1)
  else
    pure rawRun
  return some (runExpr, isReadOnly, lSt.extRoots)

open Lean Elab Command in
def elabAsyncEnsuresThm (priorRep priorUnrep : Nat)
    (srvName : Name) (fnStr : String) (fnIdent handlerId : Ident)
    (stateInvTerm stateTyTerm payloadTerm errTyTerm : Term)
    (allBinderIds : Array Ident) (allBinderTys : Array Term)
    (hCall : Term) (extraUnfoldIds : Array Ident) (ensSpec : FnEnsSpec) :
    CommandElabM Bool := do
  let ensThmId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_ensures")
  let outVar := mkIdent `_srvOut
  let postBody ← ensSpec.postFn ⟨outVar.raw⟩
  let ensLbl := Syntax.mkStrLit s!"ensures: {ensSpec.labelStr}"
  let fnLit := Syntax.mkStrLit fnStr
  let unfoldIds := extraUnfoldIds.push ensSpec.ensId
  elabCommand (← `(command|
    theorem $ensThmId $[($allBinderIds:ident : $allBinderTys:term)]* :
        Qed.Server.ProgEnsures $stateInvTerm
          (fun ($outVar:ident : Except $errTyTerm $payloadTerm) => $postBody)
          ($hCall : Qed.Server.ThreadProg $stateTyTerm _) := by
      qedSrvProveAsyncEnsures $handlerId [$[$unfoldIds],*] $fnLit $ensLbl))
  return !hasNewErrors (← get).messages priorRep priorUnrep

open Lean Elab Command in
def elabServerAsyncFn (priorRep priorUnrep : Nat)
    (srvName : Name) (fnStr : String) (fnIdent stateId stateInvId : Ident)
    (allBinderIds : Array Ident) (allBinderTys : Array Term) (callArgs : Array Term)
    (payloadTerm errTyTerm : Term) (baseCtx : LowerCtx) (bodyStmts : Array Lean.Syntax)
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (stateFieldNames envVarNames : Array String)
    (ensSpec? : Option FnEnsSpec)
    (deferredProofs : IO.Ref (Array (CommandElabM Bool))) :
    CommandElabM (Option (Term × Bool × Array Name)) := do
  let stateTyTerm : Term := ⟨stateId.raw⟩
  let fnLit := Syntax.mkStrLit fnStr
  let (asyncBody, lSt) ← (lowerAsyncBlock baseCtx (some stateTyTerm) bodyStmts).run {}
  let isReadOnly := lSt.mutated.isEmpty && !lSt.dbWrite
  let handlerId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_handler")
  elabCommand (← `(command|
    set_option linter.unusedVariables false in
    def $handlerId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m]
        [Qed.Server.MonadAtomic $stateId m]
        $[($allBinderIds:ident : $allBinderTys:term)]* :
        m (Except $errTyTerm $payloadTerm) :=
      Qed.Server.srvFinishM $asyncBody))
  if hasNewErrors (← get).messages priorRep priorUnrep then return none

  let hCall ← allBinderIds.foldlM (init := ← `($handlerId)) fun acc id => `($acc $id)
  let asyncInvId := mkIdentFrom fnIdent (srvName ++ fnIdent.getId.appendAfter "_inv")
  let singleInvLbl := Syntax.mkStrLit (singleInvLabelStr invs)
  let invCmd ← `(command|
    theorem $asyncInvId $[($allBinderIds:ident : $allBinderTys:term)]* :
        Qed.Server.ProgPreservesInv $stateInvId
          ($hCall : Qed.Server.ThreadProg $stateId _) := by
      qedSrvProveAsync $handlerId [$stateInvId] $fnLit $singleInvLbl)
  deferredProofs.modify (·.push do
    elabCommand invCmd
    if hasNewErrors (← get).messages priorRep priorUnrep then return false
    elabServerFnInvariants priorRep priorUnrep true srvName fnStr fnIdent stateId stateInvId
      handlerId allBinderIds allBinderTys hCall invs mutInvs stateFieldNames envVarNames)

  if let some ensSpec := ensSpec? then
    deferredProofs.modify (·.push do
      elabAsyncEnsuresThm priorRep priorUnrep srvName fnStr fnIdent handlerId
        stateInvId stateId payloadTerm errTyTerm allBinderIds allBinderTys hCall #[stateInvId] ensSpec)

  let hApp ← callArgs.foldlM (init := ← `($handlerId)) fun acc a => `($acc $a)
  return some (hApp, isReadOnly, lSt.extRoots)


end Qed.Server
