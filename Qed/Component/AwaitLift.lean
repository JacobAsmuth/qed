import Qed.Component.Rewrite

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

/-! ## Continuation-Lifting for Client `await` / `catch` -/

private def packSuite (refStx : Syntax) (stmts : Array Syntax) : Syntax :=
  let info := SourceInfo.fromRef refStx
  let body := if stmts.isEmpty then
    #[Syntax.node info ``qedStmtPass #[Syntax.atom info "pass"]]
  else stmts
  Syntax.node info `Qed.Lang.suite #[Syntax.node info nullKind body]

private def mkPatIdent (info : SourceInfo) (nm : Name) (args : Array Syntax := #[]) : Syntax :=
  let sepArgs := args.foldl (init := #[]) fun acc a =>
    if acc.isEmpty then #[a] else (acc.push (Syntax.atom info ",")).push a
  let argsOpt := if args.isEmpty then Syntax.node info nullKind #[]
    else Syntax.node info nullKind #[Syntax.atom info "(", Syntax.node info nullKind sepArgs, Syntax.atom info ")"]
  Syntax.node info ``qedPatIdent #[mkIdent nm, argsOpt]

private def mkPatDot (info : SourceInfo) (tag : Name) : Syntax :=
  Syntax.node info ``qedPatDot #[Syntax.atom info ".", mkIdent tag, Syntax.node info nullKind #[]]

private def mkPatWild (info : SourceInfo) : Syntax :=
  Syntax.node info ``qedPatWild #[Syntax.atom info "_"]

private inductive CatchPatKind
  | wildcard
  | dotTag (tag : String) (binder? : Option Syntax)

private def classifyCatchCase (validTags : Array String) (isOption : Bool) (cStx : Syntax) :
    CommandElabM (CatchPatKind × Array Syntax) := do
  let pats := (cStx.getArg 1).getSepArgs
  if pats.size != 1 then
    throwErrorAt cStx "each `catch` case must match a single pattern (`case .tag:`, `case .tag(err):`, `case .failed(err):`, or `case _:`)"
  let pat := pats[0]!
  let body := suiteStmts (cStx.getArg 3)
  if pat.getKind == ``qedPatWild then
    return (.wildcard, body)
  let checkTag (tagRef : Syntax) (tag : String) (binder? : Option Syntax) : CommandElabM (CatchPatKind × Array Syntax) := do
    if tag == "failed" then
      return (.dotTag "failed" binder?, body)
    if tag == "none" then
      unless isOption do
        throwErrorAt tagRef "`.none` catch case is only valid when the awaited RPC returns an `Option` (`T?`)"
      if binder?.isSome then
        throwErrorAt tagRef "`.none` takes no error message argument"
      return (.dotTag "none" none, body)
    unless validTags.contains tag do
      let validList := validTags.toList.map (s!".{·}") ++ (if isOption then [".none"] else []) ++ [".failed"]
      let validStr := String.intercalate ", " validList
      throwErrorAt tagRef s!"unknown error tag `.{tag}` in `catch` (valid patterns: {validStr})"
    return (.dotTag tag binder?, body)
  if pat.getKind == ``qedPatDot then
    let tag := (pat.getArg 1).getId.toString
    if (pat.getArg 2).getNumArgs == 3 then
      let args := ((pat.getArg 2).getArg 1).getSepArgs
      if args.size == 1 then
        let b := args[0]!
        unless b.getKind == ``qedPatWild || (b.getKind == ``qedPatIdent && (b.getArg 1).getNumArgs == 0) do
          throwErrorAt b "error message pattern in `catch` must be an identifier or `_`"
        return ← checkTag pat tag (some b)
      else
        throwErrorAt pat "unsupported `catch` pattern; expected `.tag`, `.tag(msg)`, `.failed(err)`, `.none`, or `_`"
    else
      return ← checkTag pat tag none
  throwErrorAt pat "unsupported `catch` pattern; expected `.tag`, `.tag(msg)`, `.failed(err)`, `.none`, or `_`"

private def stmtContainsAwait (st : Syntax) : Bool := stxAny isAwaitStmt st

private def resolveRpcForAwait (ctx : RewriteCtx) (rpcId : Ident) (argCount : Nat) :
    CommandElabM (ServerInfo × ServerMethodInfo) := do
  let openDecls := (← getScope).openDecls
  let some (srvInfo, mInfo) := lookupServerMethod? (← getEnv) (← getCurrNamespace) openDecls rpcId.getId
    | throwErrorAt rpcId s!"unknown server RPC `{rpcId.getId}` in `await`"
  if argCount != mInfo.paramCount then
    throwErrorAt rpcId s!"`{rpcId.getId}` expects {mInfo.paramCount} argument(s), got {argCount}"
  recordUsedRpc ctx.usedRpcs srvInfo.shortName mInfo.name
  return (srvInfo, mInfo)

private def unpackAwaitCall (ref : Syntax) (awaitExpr : Syntax) : CommandElabM (Ident × Array Term) := do
  let inner := unwrapParens1 (awaitExpr.getArg 1)
  unless inner.getKind == ``qedCall && (inner.getArg 0).getKind == ``qedIdent do
    let sn := stxSnippet inner
    let got := if sn.isEmpty then "" else s!", got `{sn}`"
    throwErrorAt ref s!"`await` expects a server RPC call `Server.method(args...)`{got}"
  let argTerms ← lowerPosCallArgs ref "await ..." none (inner.getArg 2).getSepArgs
  return (⟨((inner.getArg 0).getArg 0)⟩, argTerms)

private structure ParsedLetClauses where
  predict?   : Option (Syntax × PredictBody) := none
  onConfirm? : Option (Syntax × Array Syntax) := none
  rollback?  : Option (Syntax × Option Syntax × Array Syntax) := none
  catch?     : Option (Syntax × Syntax) := none

private def parsePredictClauseNode (cl : Syntax) : CommandElabM (Syntax × PredictBody) := do
  let ck := cl.getKind
  if ck == `Qed.Lang.letPredictBlock then
    return (cl, .block (suiteStmts (cl.getArg 2)))
  else if ck == `Qed.Lang.letPredictExpr then
    return (cl, .expr (cl.getArg 1))
  else
    throwErrorAt cl "internal: unexpected `predict` clause node"

private def parseLetClauses (clausesNode : Syntax) : CommandElabM ParsedLetClauses := do
  let mut acc : ParsedLetClauses := {}
  for cl in clausesNode.getArgs do
    let ck := cl.getKind
    if ck == `Qed.Lang.letPredictBlock || ck == `Qed.Lang.letPredictExpr then
      if acc.predict?.isSome then
        throwErrorAt cl "duplicate `predict` clause on `await`"
      acc := { acc with predict? := some (← parsePredictClauseNode cl) }
    else if ck == `Qed.Lang.letOnConfirm then
      if acc.onConfirm?.isSome then
        throwErrorAt cl "duplicate `on_confirm` clause on `await`"
      acc := { acc with onConfirm? := some (cl, suiteStmts (cl.getArg 2)) }
    else if ck == `Qed.Lang.letRollback then
      if acc.rollback?.isSome then
        throwErrorAt cl "duplicate `rollback` clause on `await`"
      let binder? : Option Syntax := if (cl.getArg 1).getNumArgs == 3 then some ((cl.getArg 1).getArg 1) else none
      acc := { acc with rollback? := some (cl, binder?, suiteStmts (cl.getArg 3)) }
    else if ck == `Qed.Lang.letCatch then
      if acc.catch?.isSome then
        throwErrorAt cl "duplicate `catch` clause on `await`"
      acc := { acc with catch? := some (cl, (cl.getArg 1)) }
  if let some (ocRef, _) := acc.onConfirm? then
    unless acc.predict?.isSome do
      throwErrorAt ocRef "`on_confirm` requires a `predict` clause on the same `await`"
  if let some (rbRef, _, _) := acc.rollback? then
    unless acc.predict?.isSome do
      throwErrorAt rbRef "`rollback` requires a `predict` clause on the same `await`"
  return acc

private def forEachControlSubSuite (st : Syntax) (f : Array Syntax → CommandElabM Unit) : CommandElabM Unit := do
  let k := st.getKind
  if k == ``qedStmtIf then
    f (suiteStmts (st.getArg 3))
    for el in (st.getArg 4).getArgs do f (suiteStmts (el.getArg 3))
    if let some es := extractElseSuite (st.getArg 5) then f es
  else if k == ``qedStmtIfLet then
    f (suiteStmts (st.getArg 6))
    if let some es := extractElseSuite (st.getArg 7) then f es
  else if k == ``qedStmtMatch then
    for c in (st.getArg 3).getArgs do f (suiteStmts (c.getArg 3))

private partial def checkPureSpecCont (ctx : RewriteCtx) (stmts : Array Syntax) : CommandElabM Unit := do
  for st in stmts do
    let k := st.getKind
    if k == ``qedStmtExpr && (matchPushCall? (st.getArg 0)).isNone && (matchRemoveCall? (st.getArg 0)).isNone then
      throwErrorAt st "cannot run side effects or emit events inside a speculative continuation after `predict` (side effects cannot be rolled back); move it into `on_confirm:`"
    else if isAwaitStmt st then
      throwErrorAt st "cannot `await` inside a speculative continuation after `predict`; move sequential `await` calls into `on_confirm:`"
    else if k == ``qedStmtAssign && (st.getArg 0).getKind == ``qedIdent then
      let fname := ((st.getArg 0).getArg 0).getId.eraseMacroScopes
      if ctx.bindFields.contains fname then
        throwErrorAt st s!"cannot assign `bind` field `{fname}` inside a speculative continuation after `predict` (emits an output event); move it into `on_confirm:`"
    else
      forEachControlSubSuite st (checkPureSpecCont ctx)

private partial def checkPurePredictBlock (stmts : Array Syntax) : CommandElabM Unit := do
  for st in stmts do
    let k := st.getKind
    if k == ``qedStmtAssign then
      throwErrorAt st "`predict:` computes a predicted server response and cannot mutate state or perform side effects"
    else if k == ``qedStmtExpr then
      if (matchPushCall? (st.getArg 0)).isSome || (matchRemoveCall? (st.getArg 0)).isSome then
        throwErrorAt st "`predict:` computes a predicted server response and cannot mutate state with `.push(...)`/`.remove(...)`"
      else if (matchIdentMethodCall? (st.getArg 0)).any fun (_, m, _) => m == "send" || m == "emit" then
        throwErrorAt st "`predict:` computes a predicted server response and cannot mutate state or perform side effects"
      else
        throwErrorAt st "unexpected bare expression in `predict:`; use `return <expr>` to return a predicted response"
    else if k == ``qedStmtLet then
      if (unwrapParens1 (st.getArg 4)).getKind == ``qedAwait then
        throwErrorAt st "cannot use `await` inside a `predict:` block"
      if (st.getArg 5).getNumArgs > 0 then
        throwErrorAt ((st.getArg 5).getArg 0) "cannot attach `predict`/`on_confirm`/`rollback`/`catch` clauses inside a `predict:` block"
    else if k == ``qedStmtReturn then
      if (st.getArg 1).getNumArgs == 0 then
        throwErrorAt st "`return` inside `predict:` must return a predicted value"
    else
      forEachControlSubSuite st checkPurePredictBlock

private def stmtHasStateMutation (st : Syntax) : Bool :=
  let k := st.getKind
  k == ``qedStmtAssign || k == ``qedStmtExpr ||
  k == ``qedStmtIf || k == ``qedStmtIfLet || k == ``qedStmtMatch

private def mkLetRawSt (info : SourceInfo) (id : Ident) (ty? : Option Term) (rhsExpr : Syntax) : Syntax :=
  let tyNode := match ty? with
    | some ty => Syntax.node info nullKind #[Syntax.atom info ":", Syntax.node info ``qedTypeAtom #[mkIdentFrom ty ty.raw.getId, Syntax.node info nullKind #[]]]
    | none    => Syntax.node info nullKind #[]
  Syntax.node info ``qedStmtLet #[Syntax.atom info "let", id, tyNode, Syntax.atom info "=", rhsExpr, Syntax.node info nullKind #[]]

private def mkPassSt (info : SourceInfo) : Syntax :=
  Syntax.node info ``qedStmtPass #[Syntax.atom info "pass"]

private def mkCaseStx (st : Syntax) (patS : Syntax) (bStmts : Array Syntax) : Syntax :=
  let info := SourceInfo.fromRef st
  Syntax.node info ``qedStmtCase
    #[Syntax.atom info "case", Syntax.node info nullKind #[patS], Syntax.atom info ":", packSuite st bStmts]

private def mkMatchStx (st : Syntax) (scrutId : Ident) (cases : Array Syntax) : Syntax :=
  let info := SourceInfo.fromRef st
  let scrut := Syntax.node info ``qedIdent #[scrutId.raw]
  Syntax.node info ``qedStmtMatch
    #[Syntax.atom info "match", Syntax.node info nullKind #[scrut], Syntax.atom info ":",
      Syntax.node info nullKind cases]

private def checkExhaustiveCatch (st : Syntax) (rpcId : Ident) (mInfo : ServerMethodInfo)
    (parsedCatch : Array (CatchPatKind × Array Syntax)) : CommandElabM Unit := do
  let hasWildcard := parsedCatch.any fun (pk, _) => pk matches .wildcard
  let hasTag (t : String) := parsedCatch.any fun (pk, _) =>
    match pk with | .dotTag t' _ => t' == t | _ => false
  unless mInfo.domainErrTags.isEmpty || hasWildcard do
    let missing := mInfo.domainErrTags.filter (!hasTag ·)
    unless missing.isEmpty do
      let missStr := String.intercalate ", " (missing.toList.map (s!".{·}"))
      throwErrorAt st s!"`await {rpcId.getId}(...)` has unhandled domain error(s): {missStr}; handle them with `catch: case .{missing[0]!}: ...`"

private def shadowOuter (outer : Array (Ident × Term)) (id : Ident) (ty? : Option Term) :
    Array (Ident × Term) :=
  let nm := id.getId.eraseMacroScopes
  let filtered := outer.filter (·.1.getId.eraseMacroScopes != nm)
  match ty? with | some ty => filtered.push (id, ty) | none => filtered

private def hoistEnsuresArgs (ctx : RewriteCtx) (info : SourceInfo) (kIdx : Nat)
    (mInfo : ServerMethodInfo) (rawArgs : Array Term) (localNames : Array Name)
    (capturedOuter : Array (Ident × Term)) :
    Array (Ident × Term) × Array Term × Array Syntax × Array Term × Array (Ident × Term × Term) := Id.run do
  let mut capturedParams := capturedOuter
  let mut callArgs : Array Term := capturedOuter.map (⟨·.1.raw⟩)
  let mut preLetStmts : Array Syntax := #[]
  let mut rpcCallArgs : Array Term := #[]
  let mut hoistDefs : Array (Ident × Term × Term) := #[]
  for (argT, i) in rawArgs.zipIdx do
    let mentionsUncaptured :=
      ctx.stateFields.any (mentionsIdent argT.raw) ||
      ctx.bindFields.any (mentionsIdent argT.raw) ||
      localNames.any (mentionsIdent argT.raw)
    if mInfo.hasEnsures && mentionsUncaptured then
      let tmpId := mkIdentFrom argT.raw (Name.mkSimple s!"_rpcArg_{kIdx}_{i}")
      let paramTyId := mkIdentFrom argT.raw mInfo.paramTypeConsts[i]!
      preLetStmts := preLetStmts.push (mkLetRawSt info tmpId (some paramTyId) (mkRawExpr argT))
      capturedParams := capturedParams.push (tmpId, paramTyId)
      callArgs := callArgs.push tmpId
      rpcCallArgs := rpcCallArgs.push tmpId
      hoistDefs := hoistDefs.push (tmpId, paramTyId, argT)
    else
      rpcCallArgs := rpcCallArgs.push argT
  (capturedParams, callArgs, preLetStmts, rpcCallArgs, hoistDefs)

private def mkOutcomeTy (rpcId : Ident) (mInfo : ServerMethodInfo) (ensArgs : Array Term) :
    CommandElabM Term := do
  let outId := mkIdentFrom rpcId mInfo.outcomeConst
  if mInfo.hasEnsures then Qed.Lang.mkAppTerms outId ensArgs else pure outId

private structure PreparedAwait where
  kIdx           : Nat
  catchHasNone   : Bool
  capturedParams : Array (Ident × Term)
  callArgs       : Array Term
  preLetStmts    : Array Syntax
  rpcCallArgs    : Array Term
  hoistDefs      : Array (Ident × Term × Term)
  outTyTerm      : Term
  xBinderTy?     : Option Term

private def prepareAwaitCall (ctx : RewriteCtx) (st : Syntax) (rpcId : Ident)
    (optTy? : Option Term) (rawArgs : Array Term) (mInfo : ServerMethodInfo)
    (parsedCatch : Array (CatchPatKind × Array Syntax))
    (outerParams : Array (Ident × Term)) (localNames : Array Name)
    (captureStmts : Array Syntax) : CommandElabM PreparedAwait := do
  let info := SourceInfo.fromRef st
  checkExhaustiveCatch st rpcId mInfo parsedCatch
  let catchHasNone := parsedCatch.any fun (pk, _) => pk matches .dotTag "none" _
  let capturedOuter := outerParams.filter fun (pId, _) =>
    let pn := pId.getId.eraseMacroScopes
    captureStmts.any (mentionsIdent · pn) || rawArgs.any (mentionsIdent ·.raw pn)
  let kIdx ← ctx.contCounter.get
  ctx.contCounter.set (kIdx + 1)
  let (capturedParams, callArgs, preLetStmts, rpcCallArgs, hoistDefs) :=
    hoistEnsuresArgs ctx info kIdx mInfo rawArgs localNames capturedOuter
  let outTyTerm ← mkOutcomeTy rpcId mInfo rpcCallArgs
  let xBinderTy? ← match optTy? with
    | some t => pure (some t)
    | none   => inferAwaitBinderTy? mInfo catchHasNone
  return { kIdx, catchHasNone, capturedParams, callArgs, preLetStmts,
           rpcCallArgs, hoistDefs, outTyTerm, xBinderTy? }

private def mkOkPatAndBody (st : Syntax) (kIdx : Nat) (xId : Ident) (optTy? : Option Term)
    (mInfo : ServerMethodInfo) (catchHasNone : Bool) (bodyIn : Array Syntax) :
    CommandElabM (Syntax × Array Syntax) := do
  let info := SourceInfo.fromRef st
  let okCtorName := (if mInfo.domainErrTags.isEmpty then `Qed.RpcSimpleOutcome else `Qed.RpcOutcome) ++ `ok
  let mut okBody := bodyIn
  if let some oTy := optTy? then
    okBody := #[mkLetRawSt info xId none (mkRawExpr (← `(($xId:ident : $oTy))))] ++ okBody
  match ensuredWrapKind mInfo catchHasNone with
  | .optEnsured =>
      let optVar := mkIdentFrom xId (Name.mkSimple s!"_qedOpt_{kIdx}")
      okBody := #[mkLetRawSt info xId none (mkRawExpr (← `(($optVar).map Qed.Ensured.val)))] ++ okBody
      return (mkPatIdent info okCtorName #[mkPatIdent info optVar.getId], okBody)
  | wrap =>
      let inner := if wrap == .ensured then
        mkPatIdent info `Qed.Ensured.mk #[mkPatIdent info xId.getId, mkPatIdent info `_qed_ens]
      else mkPatIdent info xId.getId
      let arg := if mInfo.isOption && catchHasNone then mkPatIdent info `some #[inner] else inner
      return (mkPatIdent info okCtorName #[arg], okBody)

private def mkRpcPerformStmt (ctx : RewriteCtx) (st : Syntax) (rpcId : Ident)
    (srvInfo : ServerInfo) (mInfo : ServerMethodInfo) (contCtor : Name)
    (callArgs rpcCallArgs : Array Term) : CommandElabM Syntax := do
  let info := SourceInfo.fromRef st
  let cbTerm ← Qed.Lang.mkAppTerms (mkIdentFrom st (ctx.msgPath ++ contCtor)) callArgs
  let srvId := mkIdentFrom rpcId srvInfo.serverName
  let methId := mkIdentFrom rpcId (Name.mkSimple mInfo.name)
  let callTerm ← `(qedCheckRpcCall% $srvId:ident $methId:ident [$[$rpcCallArgs:term],*] $cbTerm)
  return Syntax.node info ``qedStmtExpr #[mkRawExpr callTerm]

private abbrev LiftRecFn :=
  Array (Ident × Term) → Array (Ident × Term) → Array Name → Array Syntax →
    CommandElabM (Array Syntax × Option (Array Syntax))

private def buildCatchArms (liftRec : LiftRecFn) (st : Syntax) (mInfo : ServerMethodInfo)
    (parsedCatch : Array (CatchPatKind × Array Syntax))
    (armOuterBase : Array (Ident × Term)) (localNames : Array Name)
    (forCtorParams : Array (Ident × Term)) :
    CommandElabM (Array Syntax × Array Syntax × Bool × Bool) := do
  let info := SourceInfo.fromRef st
  let outcomePrefix := if mInfo.domainErrTags.isEmpty then `Qed.RpcSimpleOutcome else `Qed.RpcOutcome
  let okCtorName := outcomePrefix ++ `ok
  let mut arms : Array Syntax := #[]
  let mut wildArms : Array Syntax := #[]
  let mut covFailed := false
  let mut covNone := false
  for (pk, bodyRaw) in parsedCatch do
    let mut bOuter := armOuterBase
    match pk with
    | .wildcard =>
        let (bLifted, _) ← liftRec forCtorParams bOuter localNames bodyRaw
        wildArms := wildArms.push (mkCaseStx st (mkPatWild info) bLifted)
    | .dotTag tag bOpt? =>
        if let some b := bOpt? then
          if b.getKind == ``qedPatIdent then
            bOuter := shadowOuter bOuter ⟨b.getArg 0⟩ (some (← `(String)))
        let (bLifted, _) ← liftRec forCtorParams bOuter localNames bodyRaw
        let msgPat := bOpt?.getD (mkPatWild info)
        let patS : Syntax :=
          if tag == "failed" then
            mkPatIdent info (outcomePrefix ++ `failed) #[msgPat]
          else if tag == "none" then
            mkPatIdent info okCtorName #[mkPatIdent info `none]
          else
            mkPatIdent info (outcomePrefix ++ `err) #[mkPatDot info (Name.mkSimple tag), msgPat]
        if tag == "failed" then covFailed := true
        if tag == "none" then covNone := true
        arms := arms.push (mkCaseStx st patS bLifted)
  return (arms, wildArms, covFailed, covNone)

private def registerAwaitContSite (ctx : RewriteCtx) (liftRec : LiftRecFn)
    (st : Syntax) (prep : PreparedAwait) (xId : Ident) (optTy? : Option Term)
    (rpcId : Ident) (srvInfo : ServerInfo) (mInfo : ServerMethodInfo)
    (parsedCatch : Array (CatchPatKind × Array Syntax))
    (outerParams : Array (Ident × Term)) (localNames : Array Name)
    (mkOkStmts : Array (Ident × Term) → CommandElabM (Array Syntax × Option (Array Syntax))) :
    CommandElabM Syntax := do
  let info := SourceInfo.fromRef st
  let contCtor := Name.mkSimple s!"_cont_{prep.kIdx}"
  let outVarId := mkIdentFrom st (Name.mkSimple s!"_qedOut_{prep.kIdx}")
  let contParams := prep.capturedParams.push (outVarId, prep.outTyTerm)
  let (okStmts, restCls?) ← mkOkStmts contParams
  let (okPat, okBody) ← mkOkPatAndBody st prep.kIdx xId optTy? mInfo prep.catchHasNone okStmts
  let (catchArms, wildArms, covFailed, covNone) ←
    buildCatchArms liftRec st mInfo parsedCatch outerParams localNames contParams
  let mut matchCases := #[mkCaseStx st okPat okBody] ++ catchArms ++ wildArms
  if wildArms.isEmpty && (!covFailed || (mInfo.isOption && !covNone)) then
    matchCases := matchCases.push (mkCaseStx st (mkPatWild info) #[mkPassSt info])
  ctx.sites.modify (·.push {
    key := s!"cont:{contCtor}", ctor := contCtor, params := contParams,
    stmts? := some #[mkMatchStx st outVarId matchCases]
  })
  if let some restCls := restCls? then
    ctx.specDispatches.modify (·.push {
      ctor := contCtor, params := contParams,
      stmts := #[mkMatchStx st outVarId #[mkCaseStx st okPat restCls, mkCaseStx st (mkPatWild info) #[mkPassSt info]]]
    })
  mkRpcPerformStmt ctx st rpcId srvInfo mInfo contCtor prep.callArgs prep.rpcCallArgs

private def liftPredictedAwait (ctx : RewriteCtx) (actionParams : Array (Ident × Term))
    (liftRec : LiftRecFn)
    (st : Syntax) (xId : Ident) (optTy? : Option Term)
    (rpcId : Ident) (rawArgs : Array Term) (srvInfo : ServerInfo) (mInfo : ServerMethodInfo)
    (predBody : PredictBody)
    (onConfirm? : Option (Syntax × Array Syntax))
    (rollback? : Option (Syntax × Option Syntax × Array Syntax))
    (parsedCatch : Array (CatchPatKind × Array Syntax))
    (catchCasesForCapture : Array Syntax)
    (outerParams : Array (Ident × Term)) (localNames : Array Name)
    (preStmts : Array Syntax) (unpredPreStmts : Array Syntax)
    (rest : List Syntax) : CommandElabM (Array Syntax × Option (Array Syntax)) := do
  let info := SourceInfo.fromRef st
  let restArr := rest.toArray
  checkPureSpecCont ctx restArr
  match predBody with
  | .block pStmts => checkPurePredictBlock pStmts
  | .expr _ => pure ()
  let onConfirmStmts := onConfirm?.map (·.2) |>.getD #[]
  let rollbackStmts := rollback?.map (·.2.2) |>.getD #[]
  let prep ← prepareAwaitCall ctx st rpcId optTy? rawArgs mInfo parsedCatch outerParams localNames
    (restArr ++ onConfirmStmts ++ rollbackStmts ++ catchCasesForCapture)
  let some rawValTy := prep.xBinderTy?
    | throwErrorAt st s!"cannot infer response type for predicted `await {rpcId.getId}(...)`; add a type annotation `let {xId.getId} : Type = await ...`"
  let wrapKind := ensuredWrapKind mInfo prep.catchHasNone
  let innerEnsTy? : Option Term ←
    if wrapKind == .optEnsured then inferAwaitBinderTy? mInfo true else pure none
  let contPayloadTy : Term ← match wrapKind with
    | .plain => pure rawValTy
    | .ensured | .optEnsured =>
        let some ensConst := mInfo.ensPredConst
          | throwErrorAt st "internal: missing server `ensures` predicate in `predict`"
        let ensApp ← Qed.Lang.mkAppTerms (mkIdent ensConst) prep.rpcCallArgs
        if wrapKind == .optEnsured then `(Option (Qed.Ensured $(innerEnsTy?.getD rawValTy) ($ensApp)))
        else `(Qed.Ensured $rawValTy ($ensApp))

  let mkUnpackedBody (valVarId : Ident) (binder? : Option Ident) (bodyStmts : Array Syntax) :
      CommandElabM (Array Syntax) := do
    let mut stmtsOut := if bodyStmts.isEmpty then #[mkPassSt info] else bodyStmts
    match wrapKind with
    | .optEnsured =>
        if let some bId := binder? then
          stmtsOut := #[mkLetRawSt info bId none (mkRawExpr (← `(($valVarId).map Qed.Ensured.val)))] ++ stmtsOut
        return stmtsOut
    | .ensured =>
        let bPat := match binder? with | some bId => mkPatIdent info bId.getId | none => mkPatWild info
        let pat := mkPatIdent info `Qed.Ensured.mk #[bPat, mkPatIdent info `_qed_ens]
        return #[mkMatchStx st valVarId #[mkCaseStx st pat stmtsOut]]
    | .plain =>
        if let some bId := binder? then
          if bId.getId.eraseMacroScopes != valVarId.getId.eraseMacroScopes then
            stmtsOut := #[mkLetRawSt info bId none (Syntax.node info ``qedIdent #[valVarId.raw])] ++ stmtsOut
        return stmtsOut

  let kIdx := prep.kIdx
  let preCtor? : Option Name ←
    if preStmts.any stmtHasStateMutation then
      let preCtor := Name.mkSimple s!"_specPre_{kIdx}"
      ctx.sites.modify (·.push { key := s!"specPre:{preCtor}", ctor := preCtor, params := actionParams, stmts? := some preStmts })
      pure (some preCtor)
    else pure none

  let specContCtor := Name.mkSimple s!"_specCont_{kIdx}"
  let specValId := mkIdentFrom st (Name.mkSimple s!"_specVal_{kIdx}")
  let mut contBodyStmts := restArr
  if let some oTy := optTy? then
    contBodyStmts := #[mkLetRawSt info xId none (mkRawExpr (← `(($xId:ident : $oTy))))] ++ contBodyStmts
  ctx.sites.modify (·.push {
    key := s!"specCont:{specContCtor}", ctor := specContCtor,
    params := prep.capturedParams.push (specValId, contPayloadTy),
    stmts? := some (← mkUnpackedBody specValId (some xId) contBodyStmts)
  })

  let nextOuter := shadowOuter outerParams xId (some rawValTy)

  let regSubBranch (pfx valPfx : String) (bId? : Option Ident) (bOuter : Array (Ident × Term))
      (bStmts : Array Syntax) : CommandElabM Name := do
    let ctor := Name.mkSimple s!"_{pfx}_{kIdx}"
    let valId := mkIdentFrom st (Name.mkSimple s!"_{valPfx}_{kIdx}")
    let bParams := prep.capturedParams.push (valId, contPayloadTy)
    let (lifted, cls?) ← liftRec bParams bOuter localNames bStmts
    ctx.sites.modify (·.push {
      key := s!"{pfx}:{ctor}", ctor, params := bParams,
      stmts? := some (← mkUnpackedBody valId bId? lifted)
    })
    if let some cls := cls? then
      ctx.specDispatches.modify (·.push { ctor, params := bParams, stmts := cls })
    return ctor

  let confirmCtor? ← onConfirm?.mapM fun (_, ocStmts) =>
    regSubBranch "specConfirm" "specConfVal" (some xId) nextOuter ocStmts
  let rollbackCtor? ← rollback?.mapM fun (_, rbBinder?, rbStmts) => do
    let (rbBinderId?, rbOuter) := match rbBinder? with
      | some bStx =>
          if bStx.isIdent then
            let bId : Ident := ⟨bStx⟩
            (some bId, shadowOuter outerParams bId (some rawValTy))
          else (none, outerParams)
      | none => (none, outerParams)
    regSubBranch "specRollback" "specRbVal" rbBinderId? rbOuter rbStmts

  let catchCtor? : Option Name ←
    if parsedCatch.isEmpty then pure none
    else
      let cCtor := Name.mkSimple s!"_specCatch_{kIdx}"
      let cOutId := mkIdentFrom st (Name.mkSimple s!"_specCatchOut_{kIdx}")
      let cParams := prep.capturedParams.push (cOutId, prep.outTyTerm)
      let (cArms, cWilds, _, _) ← buildCatchArms liftRec st mInfo parsedCatch outerParams localNames cParams
      let allCatchCases := cArms ++ cWilds ++ (if cWilds.isEmpty then #[mkCaseStx st (mkPatWild info) #[mkPassSt info]] else #[])
      ctx.sites.modify (·.push {
        key := s!"specCatch:{cCtor}", ctor := cCtor, params := cParams,
        stmts? := some #[mkMatchStx st cOutId allCatchCases]
      })
      pure (some cCtor)

  let specResCtor := Name.mkSimple s!"_specRes_{kIdx}"
  let txIdParam := mkIdentFrom st (Name.mkSimple s!"_specTxId_{kIdx}")
  let predParam := mkIdentFrom st (Name.mkSimple s!"_specPred_{kIdx}")
  let outParam := mkIdentFrom st (Name.mkSimple s!"_specOut_{kIdx}")
  let resParams : Array (Ident × Term) :=
    #[(txIdParam, ← `(Nat))] ++ prep.capturedParams ++ #[(predParam, rawValTy), (outParam, prep.outTyTerm)]
  ctx.sites.modify (·.push { key := s!"specRes:{specResCtor}", ctor := specResCtor, params := resParams, stmts? := some #[mkPassSt info] })
  ctx.specResolves.modify (·.push {
    resCtor := specResCtor, txIdParam, capturedParams := prep.capturedParams, predParam,
    outParam, mInfo, catchHasNone := prep.catchHasNone,
    contCtor := specContCtor, confirmCtor?, rollbackCtor?, catchCtor?, callRef := st
  })

  let fbPerfSt ← registerAwaitContSite ctx liftRec st prep xId optTy? rpcId srvInfo mInfo
    parsedCatch outerParams localNames fun fbParams => do
      let (ocFbLifted, _) ← if onConfirmStmts.isEmpty then pure (#[], none)
        else liftRec fbParams nextOuter localNames onConfirmStmts
      return (restArr ++ ocFbLifted, none)
  let dispNode : SpecDispatchNode := {
    ref := st, preCtor?, preArgs := actionParams.map (⟨·.1.raw⟩),
    capturedArgs := prep.callArgs, rpcArgs := prep.rpcCallArgs, hoistDefs := prep.hoistDefs,
    srvInfo, mInfo, catchHasNone := prep.catchHasNone, predValTy := rawValTy, innerEnsTy?, predBody,
    contCtor := specContCtor, resCtor := specResCtor
  }
  let nodeIdx := (← ctx.specNodes.get).size
  ctx.specNodes.modify (·.push dispNode)
  return (unpredPreStmts ++ prep.preLetStmts.push fbPerfSt, some #[mkSpecDispatchMarker info nodeIdx])

private partial def liftAwaitStmts (ctx : RewriteCtx)
    (actionParams : Array (Ident × Term))
    (outerParams : Array (Ident × Term))
    (localLetNames : Array Name) (stmts : Array Syntax)
    (initPreStmts : Array Syntax := #[]) : CommandElabM (Array Syntax × Option (Array Syntax)) := do
  let liftRec : LiftRecFn := fun ap op ln ss => liftAwaitStmts ctx ap op ln ss
  let rec go (outerParams : Array (Ident × Term)) (localNames : Array Name)
      (preStmts : Array Syntax) : List Syntax → CommandElabM (Array Syntax × Option (Array Syntax))
  | [] => return (#[], none)
  | st :: rest => do
      let info := SourceInfo.fromRef st
      let k := st.getKind

      if k == ``qedStmtAssign && (unwrapParens1 (st.getArg 2)).getKind == ``qedAwait then
        let op := atomStr (st.getArg 1)
        if op != "=" then
          throwErrorAt (st.getArg 1) s!"`await` assignment requires `=`, not `{op}` (use `let v = await ...` then update the field)"
        unless (st.getArg 0).getKind == ``qedIdent do
          let lhsStr := stxSnippet (st.getArg 0)
          let got := if lhsStr.isEmpty then "" else s!", got `{lhsStr}`"
          throwErrorAt (st.getArg 0) s!"`field = await ...` requires a simple `Resource` state field on the left-hand side{got}"
        let fId : Ident := ⟨((st.getArg 0).getArg 0)⟩
        let fname := fId.getId.eraseMacroScopes
        checkMutableField ctx fId s!"`{fname} = await ...`" fname
        let (rpcId, rawArgs) ← unpackAwaitCall st (unwrapParens1 (st.getArg 2))
        let (srvInfo, mInfo) ← resolveRpcForAwait ctx rpcId rawArgs.size
        let mkResAssign (rhs : Term) : Syntax :=
          Syntax.node info ``qedStmtAssign #[(st.getArg 0), Syntax.atom info "=", mkRawExpr rhs, Syntax.node info nullKind #[]]
        if st.getNumArgs > 3 && (st.getArg 3).getNumArgs == 1 then
          let (_, predBody) ← parsePredictClauseNode ((st.getArg 3).getArg 0)
          let xId := mkIdentFrom st `_qedResPred
          let errId := mkIdentFrom st `_qedResErr
          let errPat := mkPatIdent info errId.getId
          let okAssign := mkResAssign (← `(Qed.Resource.ok $xId))
          let failAssign := mkResAssign (← `(Qed.Resource.failed $errId))
          let notFoundAssign := mkResAssign (← `(Qed.Resource.failed "Not found"))
          let loadAssign := mkResAssign (← `(Qed.Resource.loading))
          let mut parsedCatch : Array (CatchPatKind × Array Syntax) :=
            mInfo.domainErrTags.map fun tag => (.dotTag tag (some errPat), #[failAssign])
          if mInfo.isOption then
            parsedCatch := parsedCatch.push (.dotTag "none" none, #[notFoundAssign])
          parsedCatch := parsedCatch.push (.dotTag "failed" (some errPat), #[failAssign])
          return ← liftPredictedAwait ctx actionParams liftRec st xId none rpcId rawArgs srvInfo mInfo predBody
            none none parsedCatch #[] outerParams localNames preStmts #[loadAssign] (okAssign :: rest)
        let setterCtor ← registerSite ctx.sites #[(fname, none)] none
        let assignSt := mkResAssign (← `(Qed.Resource.loading))
        let perfSt ← mkRpcPerformStmt ctx st rpcId srvInfo mInfo setterCtor #[] rawArgs
        let (tail, tailCls?) ← go outerParams localNames (preStmts ++ #[assignSt, perfSt]) rest
        return (#[assignSt, perfSt] ++ tail, tailCls?)

      if k == ``qedStmtAssign && st.getNumArgs > 3 && (st.getArg 3).getNumArgs > 0 then
        throwErrorAt ((st.getArg 3).getArg 0) "`predict` can only be used on an `await` server RPC call"

      if k == ``qedStmtLet && (unwrapParens1 (st.getArg 4)).getKind == ``qedAwait then
        let xId : Ident := if (st.getArg 1).isIdent then ⟨(st.getArg 1)⟩ else mkIdentFrom st `_qedAwaitRes
        let optTy? ← lowerOptType (st.getArg 2)
        let (rpcId, rawArgs) ← unpackAwaitCall st (unwrapParens1 (st.getArg 4))
        let (srvInfo, mInfo) ← resolveRpcForAwait ctx rpcId rawArgs.size
        let clauses ← parseLetClauses (st.getArg 5)
        let catchCases : Array Syntax ← match clauses.catch? with
          | some (_, cNode) =>
              if cNode.getKind == `Qed.Lang.catchArms then pure (cNode.getArg 1).getArgs
              else throwErrorAt cNode "in client components, use `catch:` with `case .tag: ...` arms"
          | none => pure #[]
        let parsedCatch ← catchCases.mapM (classifyCatchCase mInfo.domainErrTags mInfo.isOption)

        if let some (_, predBody) := clauses.predict? then
          return ← liftPredictedAwait ctx actionParams liftRec st xId optTy? rpcId rawArgs srvInfo mInfo predBody
            clauses.onConfirm? clauses.rollback? parsedCatch catchCases
            outerParams localNames preStmts #[] rest

        let restArr := rest.toArray
        let prep ← prepareAwaitCall ctx st rpcId optTy? rawArgs mInfo parsedCatch outerParams localNames
          (restArr ++ catchCases)
        let nextOuter := shadowOuter outerParams xId prep.xBinderTy?
        let nextLocals := if prep.xBinderTy?.isSome then localNames else localNames.push xId.getId.eraseMacroScopes
        let perfSt ← registerAwaitContSite ctx liftRec st prep xId optTy? rpcId srvInfo mInfo
          parsedCatch outerParams localNames fun contParams =>
            liftAwaitStmts ctx contParams nextOuter nextLocals restArr
        return (prep.preLetStmts.push perfSt, none)

      if k == ``qedStmtLet then
        if (st.getArg 5).getNumArgs > 0 then
          throwErrorAt ((st.getArg 5).getArg 0) "`predict`, `on_confirm`, `rollback`, and `catch` can only be used on an `await` server RPC call"
        let (outer', locals') ←
          if (st.getArg 1).isIdent then
            let lId : Ident := ⟨(st.getArg 1)⟩
            let optTy? ← lowerOptType (st.getArg 2)
            pure (shadowOuter outerParams lId optTy?,
              if optTy?.isSome then localNames else localNames.push lId.getId.eraseMacroScopes)
          else pure (outerParams, localNames)
        let (tail, tailCls?) ← go outer' locals' (preStmts.push st) rest
        return (#[st] ++ tail, tailCls?.map (#[st] ++ ·))

      if k == ``qedStmtReturn then
        return (#[st], none)

      if (k == ``qedStmtIf || k == ``qedStmtIfLet || k == ``qedStmtMatch) &&
          (stmtContainsAwait st || (hasReturnStmt st && rest.any stmtContainsAwait)) then
        unless rest.isEmpty || hasReturnStmt st do
          throwErrorAt st "statements after an `if`/`match` containing `await` are not supported unless the branch `return`s; move trailing statements inside the branches"
        let tailIfReturn := if hasReturnStmt st then rest else []
        let setArg (n : Syntax) (i : Nat) (v : Syntax) : Syntax :=
          Syntax.node n.getHeadInfo n.getKind (n.getArgs.set! i v)
        let packOptElse : Option (Array Syntax) → Syntax
          | some cs => Syntax.node info nullKind #[Syntax.atom info "else", Syntax.atom info ":", packSuite st cs]
          | none    => Syntax.node info nullKind #[]
        let liftBranch (extraLocals : Array Name) (bodyStmts : Array Syntax) :=
          go outerParams (localNames ++ extraLocals.filter fun n => !(outerParams.any (·.1.getId.eraseMacroScopes == n)))
            preStmts (bodyStmts.toList ++ tailIfReturn)
        let liftNode (node : Syntax) (bodyIdx : Nat) (extraLocals : Array Name := #[]) := do
          let (bL, bC?) ← liftBranch extraLocals (suiteStmts (node.getArg bodyIdx))
          pure (setArg node bodyIdx (packSuite st bL), setArg node bodyIdx (packSuite st (bC?.getD #[])), bC?.isSome)
        let liftOptElse (eNode : Syntax) : CommandElabM (Syntax × Option (Array Syntax)) := do
          if eNode.getNumArgs == 3 then
            let (eL, eC?) ← liftBranch #[] (suiteStmts (eNode.getArg 2))
            pure (setArg eNode 2 (packSuite st eL), eC?)
          else if !tailIfReturn.isEmpty then
            let (eL, eC?) ← liftBranch #[] #[]
            pure (packOptElse (some eL), eC?)
          else pure (eNode, none)
        if k == ``qedStmtIf then
          let (tL, tC?) ← liftBranch #[] (suiteStmts (st.getArg 3))
          let elRes ← (st.getArg 4).getArgs.mapM (liftNode · 3)
          let (eOpt, eC?) ← liftOptElse (st.getArg 5)
          let mkIf (t : Array Syntax) (els : Array Syntax) (e : Syntax) :=
            setArg (setArg (setArg st 3 (packSuite st t)) 4 (Syntax.node info nullKind els)) 5 e
          let cls? := if tC?.isNone && !elRes.any (·.2.2) && eC?.isNone then none
            else some #[mkIf (tC?.getD #[]) (elRes.map (·.2.1)) (packOptElse eC?)]
          return (#[mkIf tL (elRes.map (·.1)) eOpt], cls?)
        else if k == ``qedStmtIfLet then
          let (tL, tC?) ← liftBranch (collectQedPatIds (st.getArg 2)) (suiteStmts (st.getArg 6))
          let (eOpt, eC?) ← liftOptElse (st.getArg 7)
          let mkIfL (t : Array Syntax) (e : Syntax) := setArg (setArg st 6 (packSuite st t)) 7 e
          let cls? := if tC?.isNone && eC?.isNone then none else some #[mkIfL (tC?.getD #[]) (packOptElse eC?)]
          return (#[mkIfL tL eOpt], cls?)
        else
          let cRes ← (st.getArg 3).getArgs.mapM fun c => liftNode c 3 ((c.getArg 1).getSepArgs.flatMap collectQedPatIds)
          let mkM (cs : Array Syntax) := setArg st 3 (Syntax.node (st.getArg 3).getHeadInfo (st.getArg 3).getKind cs)
          let cls? := if !cRes.any (·.2.2) then none else some #[mkM (cRes.map (·.2.1))]
          return (#[mkM (cRes.map (·.1))], cls?)

      let (tail, tailCls?) ← go outerParams localNames (preStmts.push st) rest
      return (#[st] ++ tail, tailCls?.map (#[st] ++ ·))
  go outerParams localLetNames initPreStmts stmts.toList

private def registerActionOrPort (spec : ComponentSpec) (baseCtx : RewriteCtx)
    (kindPrefix dupLabel conflictLabel : String) (nameRef errRef : Syntax) (name : Name)
    (params : Array (Ident × Term)) (bodyStx : Syntax) (checkPlaceholders : Bool) :
    CommandElabM Unit := do
  if (← baseCtx.sites.get).any (·.ctor == name) then
    throwErrorAt nameRef s!"duplicate {dupLabel} name `{name}`"
  if spec.collections.any (·.1.getId == name) then
    throwErrorAt nameRef s!"{conflictLabel} name `{name}` conflicts with `collection {name}`"
  let stmtsRaw := suiteStmts (← rewriteIn baseCtx false bodyStx)
  let (stmts, dispCls?) ← liftAwaitStmts baseCtx params params #[] stmtsRaw
  if let some dispStmts := dispCls? then
    baseCtx.specDispatches.modify (·.push { ctor := name, params, stmts := dispStmts })
  let mut dummyAssigns : Array (Name × Option Term) := #[]
  if checkPlaceholders then
    for s in stmts do
      if s.getKind == ``qedStmtAssign && (s.getArg 0).getKind == ``qedIdent && atomStr (s.getArg 1) == "=" && isPlaceholder (s.getArg 2) then
        dummyAssigns ← pushHandlerAssign baseCtx dummyAssigns ((s.getArg 0).getArg 0) none
    if !params.isEmpty && !dummyAssigns.isEmpty then
      throwErrorAt errRef s!"action `{name}` declares explicit parameter(s) and cannot use the `_` placeholder; assign explicitly (e.g. `{dummyAssigns[0]!.1} = {params[0]!.1.getId}`)"
  baseCtx.sites.modify (·.push {
    key := s!"{kindPrefix}:{name}", ctor := name, params, assigns := dummyAssigns, stmts? := some stmts })

structure RewriteResult where
  sites          : Array SetSite
  route?         : Option RouteDecl
  starts         : Array Term
  body           : Term
  hoisted        : Array HoistedSub
  formDrafts     : Array FieldDecl
  resetForms     : Array ResetFormSub
  usedRpcs       : Array (String × String)
  specDispatches : Array SpecDispatchArm
  specNodes      : Array SpecDispatchNode
  specResolves   : Array SpecResolveSite

def collectSitesAndRewriteStateful (spec : ComponentSpec) : CommandElabM RewriteResult := do
  let baseCtx ← mkRewriteCtx spec false
  for a in spec.actions do
    let name := (a.getArg 1).getId
    let params ← parseParamList (a.getArg 2)
    let mut seenP : Array Name := #[]
    for (pId, _) in params do
      let pn := pId.getId
      if seenP.contains pn then
        throwErrorAt pId s!"duplicate parameter `{pn}` in action `{name}`"
      if spec.allNames.contains pn then
        throwErrorAt pId s!"parameter `{pn}` in action `{name}` shadows a component field; rename the parameter"
      seenP := seenP.push pn
    registerActionOrPort spec baseCtx "action" "action" "action" (a.getArg 1) a name params (a.getArg 4) true
  for p in spec.portIns do
    let name := p.id.getId
    if spec.allNames.contains p.argId.getId then
      throwErrorAt p.argId s!"port parameter `{p.argId.getId}` on `port {name}` shadows a component field; rename the parameter"
    registerActionOrPort spec baseCtx "port" "port/action" "port" p.id p.id name #[(p.argId, p.argTy)] p.body false
  let route'? ← spec.route?.mapM fun rd => do
    let rParamId := mkIdent `_r
    let rParams := #[(rParamId, rd.ty)]
    let rFieldAssign := Syntax.node .none ``qedStmtAssign
      #[Syntax.node .none ``qedIdent #[rd.field.raw], Syntax.atom .none "=",
        Syntax.node .none ``qedIdent #[rParamId.raw], Syntax.node .none nullKind #[]]
    let mut alts' : Array Syntax := #[]
    let mut altCls : Array (Syntax × Option (Array Syntax)) := #[]
    for alt in rd.alts do
      let rwBody ← rewriteIn baseCtx false (alt.getArg 3)
      let patIds := (alt.getArg 1).getSepArgs.flatMap collectQedPatIds
      let (lifted, altC?) ← liftAwaitStmts baseCtx rParams #[] patIds (suiteStmts rwBody) (initPreStmts := #[rFieldAssign])
      alts' := alts'.push (Syntax.node .none alt.getKind #[(alt.getArg 0), (alt.getArg 1), (alt.getArg 2), packSuite alt lifted])
      altCls := altCls.push (alt, altC?)
    if altCls.any (·.2.isSome) then
      let clsCases := altCls.map fun (alt, ac?) =>
        Syntax.node .none alt.getKind #[(alt.getArg 0), (alt.getArg 1), (alt.getArg 2), packSuite alt (ac?.getD #[])]
      baseCtx.specDispatches.modify (·.push {
        ctor := `_onRoute
        params := rParams
        stmts := #[rFieldAssign, mkMatchStx rd.field rParamId clsCases]
      })
    pure { rd with alts := alts' }
  for q in spec.queries do
    recordUsedRpc baseCtx.usedRpcs q.rpc.srvInfo.shortName q.rpc.mInfo.name
  let starts ← spec.starts.mapM fun st => do
    lowerCompExpr .val (← rewriteIn { baseCtx with inPerform := true } false st)
  let viewCtx := { baseCtx with
    allowHoist := true
    wrapMsg?   := if spec.hasSlotsOrKids then some (mkIdent `_wrap) else none }
  let body ← lowerCompExpr .val (← rewriteIn viewCtx false spec.body)
  return {
    sites := ← baseCtx.sites.get, route? := route'?, starts, body,
    hoisted := ← baseCtx.hoisted.get, formDrafts := ← baseCtx.formDrafts.get,
    resetForms := ← baseCtx.resetForms.get, usedRpcs := ← baseCtx.usedRpcs.get,
    specDispatches := ← baseCtx.specDispatches.get, specNodes := ← baseCtx.specNodes.get,
    specResolves := ← baseCtx.specResolves.get
  }

end CompElab
end Qed
