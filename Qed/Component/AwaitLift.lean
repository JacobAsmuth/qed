import Qed.Component.Rewrite

namespace Qed
section CompElab
open Lean Elab Command Qed.Lang

/-! ## Continuation-Lifting for Client `await` / `catch` -/

private def outcomePrefix (mInfo : ServerMethodInfo) : Name := if mInfo.domainErrTags.isEmpty then `Qed.RpcSimpleOutcome else `Qed.RpcOutcome
private def mkPatIdent (i : SourceInfo) (nm : Name) (args : Array Syntax := #[]) : Syntax :=
  let sep := args.foldl (init := #[]) fun acc a => if acc.isEmpty then #[a] else (acc.push (Syntax.atom i ",")).push a
  Syntax.node i ``qedPatIdent #[mkIdent nm, if args.isEmpty then Syntax.node i nullKind #[] else Syntax.node i nullKind #[Syntax.atom i "(", Syntax.node i nullKind sep, Syntax.atom i ")"]]
private def mkPatDot (i : SourceInfo) (tag : Name) : Syntax := Syntax.node i ``qedPatDot #[Syntax.atom i ".", mkIdent tag, Syntax.node i nullKind #[]]
private def mkPatWild (i : SourceInfo) : Syntax := Syntax.node i ``qedPatWild #[Syntax.atom i "_"]
private def mkTypedLetStmt (info : SourceInfo) (varId : Ident) (rawTy? : Option Syntax) (rhsExpr : Syntax) : Syntax :=
  let tyNode := match rawTy? with | some tyStx => Syntax.node info nullKind #[Syntax.atom info ":", tyStx] | none => Syntax.node info nullKind #[]
  Syntax.node info ``qedStmtLet #[Syntax.atom info "let", varId.raw, tyNode, Syntax.atom info "=", rhsExpr, Syntax.node info nullKind #[]]
private def mkLetRawSt (i : SourceInfo) (id : Ident) (ty? : Option Term) (rhsExpr : Syntax) : Syntax :=
  mkTypedLetStmt i id (ty?.map fun (ty : Term) => Syntax.node i ``qedTypeAtom #[mkIdentFrom ty ty.raw.getId, Syntax.node i nullKind #[]]) rhsExpr
private def mkCaseStx (st patS : Syntax) (bStmts : Array Syntax) : Syntax :=
  let i := SourceInfo.fromRef st; Syntax.node i ``qedStmtCase #[Syntax.atom i "case", Syntax.node i nullKind #[patS], Syntax.atom i ":", packSuite st bStmts]
private def mkWildPassCase (st : Syntax) : Syntax := let i := SourceInfo.fromRef st; mkCaseStx st (mkPatWild i) #[mkPassSt i]
private def mkMatchStx (st : Syntax) (scrutId : Ident) (cases : Array Syntax) : Syntax :=
  let i := SourceInfo.fromRef st
  Syntax.node i ``qedStmtMatch #[Syntax.atom i "match", Syntax.node i nullKind #[Syntax.node i ``qedIdent #[scrutId.raw]], Syntax.atom i ":", Syntax.node i nullKind cases]

private inductive CatchPatKind | wildcard | dotTag (tag : String) (binder? : Option Syntax)

private structure ParsedLetClauses where mk ::
  (predict? : Option (Syntax × PredictBody) := none) (onConfirm? : Option (Syntax × Array Syntax) := none)
  (rollback? : Option (Syntax × Option Syntax × Array Syntax) := none) (catch? : Option (Syntax × Syntax) := none)

private structure AwaitCallCtx where mk ::
  (st : Syntax) (xId : Ident) (optTy? : Option Term) (rpcId : Ident) (rawArgs : Array Term)
  (srvInfo : ServerInfo) (mInfo : ServerMethodInfo) (parsedCatch : Array (CatchPatKind × Array Syntax))
  (outerParams : Array (Ident × Term)) (localNames : Array Name)

private structure PreparedAwait where mk ::
  (kIdx : Nat) (catchHasNone : Bool) (capturedParams : Array (Ident × Term)) (callArgs : Array Term)
  (preLetStmts : Array Syntax) (rpcCallArgs : Array Term) (hoistDefs : Array (Ident × Term × Term))
  (outTyTerm : Term) (xBinderTy? : Option Term)

structure RewriteResult where mk ::
  (accum : RewriteAccum) (route? : Option RouteDecl) (starts : Array Term) (body : Term)
  (fns : Array CompFnDecl) (subscriptions : Array SubDecl)

private def classifyCatchCase (validTags : Array String) (isOption : Bool) (cStx : Syntax) : CommandElabM (Array (CatchPatKind × Array Syntax)) := do
  let body := suiteStmts (cStx.getArg 3)
  let checkTag (tagRef : Syntax) (tag : String) (binder? : Option Syntax) : CommandElabM (CatchPatKind × Array Syntax) := do
    if tag == "failed" then return (.dotTag "failed" binder?, body)
    if tag == "none" then
      unless isOption do throwErrorAt tagRef "`.none` catch case is only valid when the awaited RPC returns an `Option` (`T?`)"
      if binder?.isSome then throwErrorAt tagRef "`.none` takes no error message argument"
      return (.dotTag "none" none, body)
    unless validTags.contains tag do
      let validList := validTags.toList.map (s!".{·}") ++ (if isOption then [".none"] else []) ++ [".failed"]
      throwErrorAt tagRef s!"unknown error tag `.{tag}` in `catch` (valid patterns: {String.intercalate ", " validList})"
    return (.dotTag tag binder?, body)
  Lang.mapCmd (extractCasePatAlts (cStx.getArg 1)) fun pats => do
    if pats.size != 1 then throwErrorAt cStx "each `catch` case must match a single pattern (`case .tag:`, `case .tag(err):`, `case .failed(err):`, or `case _:`)"
    let pat := pats[0]!
    if pat.getKind == ``qedPatWild then return (.wildcard, body)
    if pat.getKind == ``qedPatDot then
      let tag := (pat.getArg 1).getId.toString
      if (pat.getArg 2).getNumArgs != 3 then return ← checkTag pat tag none
      let args := ((pat.getArg 2).getArg 1).getSepArgs
      if args.size == 1 then
        let b := args[0]!
        unless b.getKind == ``qedPatWild || (b.getKind == ``qedPatIdent && (b.getArg 1).getNumArgs == 0) do
          throwErrorAt b "error message pattern in `catch` must be an identifier or `_`"
        return ← checkTag pat tag (some b)
    throwErrorAt pat "unsupported `catch` pattern; expected `.tag`, `.tag(msg)`, `.failed(err)`, `.none`, or `_`"

private def stmtContainsAwait (st : Syntax) : Bool := stxAny isAwaitStmt st

private def resolveAwaitRpc (ctx : RewriteCtx) (ref awaitExpr : Syntax) : CommandElabM (Ident × Array Term × ServerInfo × ServerMethodInfo) := do
  let inner := unwrapParens1 (awaitExpr.getArg 1)
  unless inner.getKind == ``qedCall && (inner.getArg 0).getKind == ``qedIdent do
    let sn := stxSnippet inner; throwErrorAt ref s!"`await` expects a server RPC call `Server.method(args...)`{if sn.isEmpty then "" else s!", got `{sn}`"}"
  let rpcId : Ident := ⟨(inner.getArg 0).getArg 0⟩
  let rawArgs ← lowerPosCallArgs ref "await ..." none (inner.getArg 2).getSepArgs
  let (srvInfo, mInfo) ← resolveServerRpc rpcId rawArgs.size "await"
  recordUsedRpc ctx.accum srvInfo.shortName mInfo.name
  return (rpcId, rawArgs, srvInfo, mInfo)

private def parsePredictClauseNode (cl : Syntax) : CommandElabM (Syntax × PredictBody) := match cl.getKind with
  | `Qed.Lang.letPredictBlock => pure (cl, .block (suiteStmts (cl.getArg 2)))
  | `Qed.Lang.letPredictExpr  => pure (cl, .expr (cl.getArg 1))
  | _                         => throwErrorAt cl "internal: unexpected `predict` clause node"

private def parseLetClauses (clausesNode : Syntax) : CommandElabM ParsedLetClauses := do
  let dup {α} (cl : Syntax) (lbl : String) (cur : Option α) : CommandElabM Unit :=
    if cur.isSome then throwErrorAt cl s!"duplicate `{lbl}` clause on `await`" else pure ()
  let acc ← Lang.foldlCmd clausesNode.getArgs ({} : ParsedLetClauses) fun acc cl => do
    match cl.getKind with
    | `Qed.Lang.letPredictBlock | `Qed.Lang.letPredictExpr => dup cl "predict" acc.predict?; return { acc with predict? := some (← parsePredictClauseNode cl) }
    | `Qed.Lang.letOnConfirm => dup cl "on_confirm" acc.onConfirm?; return { acc with onConfirm? := some (cl, suiteStmts (cl.getArg 2)) }
    | `Qed.Lang.letRollback  => dup cl "rollback" acc.rollback?; return { acc with rollback? := some (cl, if (cl.getArg 1).getNumArgs == 3 then some ((cl.getArg 1).getArg 1) else none, suiteStmts (cl.getArg 3)) }
    | `Qed.Lang.letCatch     => dup cl "catch" acc.catch?; return { acc with catch? := some (cl, cl.getArg 1) }
    | _ => return acc
  for (lbl, ref?) in #[("on_confirm", acc.onConfirm?.map (·.1)), ("rollback", acc.rollback?.map (·.1))] do
    if let some ref := ref? then unless acc.predict?.isSome do throwErrorAt ref s!"`{lbl}` requires a `predict` clause on the same `await`"
  return acc

private partial def checkPureSpecStmts (ctx : RewriteCtx) (isPredict : Bool) (stmts : Array Syntax) : CommandElabM Unit := do
  let pureMut := if isPredict then #[] else ctx.spec.pureMutFnNames
  Lang.foldlCmd stmts () fun _ st => do
    match isPredict, st.getKind with
    | true, ``qedStmtAssign => throwErrorAt st "`predict:` computes a predicted server response and cannot mutate state or perform side effects"
    | true, ``qedStmtExpr =>
        if isCollMutExpr (st.getArg 0) then throwErrorAt st "`predict:` computes a predicted server response and cannot mutate state with `.push(...)`/`.remove(...)`"
        else if (matchIdentMethodCall? (st.getArg 0)).any fun (_, m, _) => m == "send" || m == "emit" then throwErrorAt st "`predict:` computes a predicted server response and cannot mutate state or perform side effects"
        else throwErrorAt st "unexpected bare expression in `predict:`; use `return <expr>` to return a predicted response"
    | true, ``qedStmtLet =>
        if (unwrapParens1 (st.getArg 4)).getKind == ``qedAwait then throwErrorAt st "cannot use `await` inside a `predict:` block"
        if (st.getArg 5).getNumArgs > 0 then throwErrorAt ((st.getArg 5).getArg 0) "cannot attach `predict`/`on_confirm`/`rollback`/`catch` clauses inside a `predict:` block"
    | true, ``qedStmtReturn => if (st.getArg 1).getNumArgs == 0 then throwErrorAt st "`return` inside `predict:` must return a predicted value"
    | false, ``qedStmtExpr =>
        if !isCollMutExpr (st.getArg 0) && !isPlainCallTo pureMut (st.getArg 0) then
          throwErrorAt st "cannot run side effects or emit events inside a speculative continuation after `predict` (side effects cannot be rolled back); move it into `on_confirm:`"
    | false, k =>
        if isAwaitStmt st then throwErrorAt st "cannot `await` inside a speculative continuation after `predict`; move sequential `await` calls into `on_confirm:`"
        else if k == ``qedStmtAssign && (st.getArg 0).getKind == ``qedIdent then
          let fname := ((st.getArg 0).getArg 0).getId.eraseMacroScopes
          if ctx.spec.bindNames.contains fname then throwErrorAt st s!"cannot assign `bind` field `{fname}` inside a speculative continuation after `predict` (emits an output event); move it into `on_confirm:`"
        else forEachControlSubSuite st (checkPureSpecStmts ctx false)
    | true, _ => forEachControlSubSuite st (checkPureSpecStmts ctx true)

private def stmtHasStateMutation (st : Syntax) : Bool := [``qedStmtAssign, ``qedStmtExpr, ``qedStmtIf, ``qedStmtIfLet, ``qedStmtMatch].contains st.getKind
private def shadowOuter (outer : Array (Ident × Term)) (id : Ident) (ty? : Option Term) : Array (Ident × Term) :=
  let f := outer.filter (·.1.getId.eraseMacroScopes != id.getId.eraseMacroScopes)
  match ty? with | some ty => f.push (id, ty) | none => f

@[noinline] private def prepareAwaitCall (ctx : RewriteCtx) (ac : AwaitCallCtx) (captureStmts : Array Syntax) : CommandElabM PreparedAwait := do
  let info := SourceInfo.fromRef ac.st
  let hasTag (t : String) := ac.parsedCatch.any fun (pk, _) => match pk with | .dotTag t' _ => t' == t | _ => false
  unless ac.mInfo.domainErrTags.isEmpty || ac.parsedCatch.any (fun (pk, _) => pk matches .wildcard) do
    let missing := ac.mInfo.domainErrTags.filter (!hasTag ·)
    unless missing.isEmpty do
      throwErrorAt ac.st s!"`await {ac.rpcId.getId}(...)` has unhandled domain error(s): {String.intercalate ", " (missing.toList.map (s!".{·}"))}; handle them with `catch: case .{missing[0]!}: ...`"
  let catchHasNone := hasTag "none"
  let capturedOuter := ac.outerParams.filter fun (pId, _) =>
    let pn := pId.getId.eraseMacroScopes; captureStmts.any (mentionsIdent · pn) || ac.rawArgs.any (mentionsIdent ·.raw pn)
  let kIdx ← ctx.accum.modifyGet fun a => (a.contCounter, { a with contCounter := a.contCounter + 1 })
  let (capturedParams, callArgs, preLetStmts, rpcCallArgs, hoistDefs) :=
    ac.rawArgs.zipIdx.foldl (init := (capturedOuter, capturedOuter.map (⟨·.1.raw⟩ : _ → Term), (#[] : Array Syntax), (#[] : Array Term), (#[] : Array (Ident × Term × Term))))
      fun (cp, ca, pl, ra, hd) (argT, i) =>
        if ac.mInfo.hasEnsures && (ctx.stateFields.any (mentionsIdent argT.raw) || ctx.spec.bindNames.any (mentionsIdent argT.raw) || ac.localNames.any (mentionsIdent argT.raw)) then
          let (tmpId, paramTyId) := (mkIdentFrom argT.raw (Name.mkSimple s!"_rpcArg_{kIdx}_{i}"), mkIdentFrom argT.raw ac.mInfo.paramTypeConsts[i]!)
          (cp.push (tmpId, paramTyId), ca.push tmpId, pl.push (mkLetRawSt info tmpId (some paramTyId) (mkRawExpr argT)), ra.push tmpId, hd.push (tmpId, paramTyId, argT))
        else (cp, ca, pl, ra.push argT, hd)
  let outId := mkIdentFrom ac.rpcId ac.mInfo.outcomeConst
  let outTyTerm ← if ac.mInfo.hasEnsures then Lang.runPQ (mkAppTermsPure outId rpcCallArgs) else pure outId
  let xBinderTy? ← match ac.optTy? with | some t => pure (some t) | none => inferAwaitBinderTy? ac.mInfo catchHasNone
  return .mk kIdx catchHasNone capturedParams callArgs preLetStmts rpcCallArgs hoistDefs outTyTerm xBinderTy?

private def mkMapEnsuredLetPure (info : SourceInfo) (bId vId : Ident) : PureQuotM Syntax := do
  pure (mkLetRawSt info bId none (mkRawExpr (← `(($vId).map Qed.Ensured.val))))

private def prependOptTyPure (info : SourceInfo) (xId : Ident) (optTy? : Option Term) (body : Array Syntax) : PureQuotM (Array Syntax) := do
  match optTy? with | some oTy => pure (#[mkLetRawSt info xId none (mkRawExpr (← `(($xId:ident : $oTy))))] ++ body) | none => pure body

@[noinline] private def mkOkPatAndBodyPure (ac : AwaitCallCtx) (prep : PreparedAwait) (bodyIn : Array Syntax) : PureQuotM (Syntax × Array Syntax) := do
  let info := SourceInfo.fromRef ac.st; let okCtor := outcomePrefix ac.mInfo ++ `ok
  let okBody ← prependOptTyPure info ac.xId ac.optTy? bodyIn
  match ensuredWrapKind ac.mInfo prep.catchHasNone with
  | .optEnsured =>
      let optVar := mkIdentFrom ac.xId (Name.mkSimple s!"_qedOpt_{prep.kIdx}")
      return (mkPatIdent info okCtor #[mkPatIdent info optVar.getId], #[← mkMapEnsuredLetPure info ac.xId optVar] ++ okBody)
  | wrap =>
      let inner := if wrap == .ensured then mkPatIdent info `Qed.Ensured.mk #[mkPatIdent info ac.xId.getId, mkPatIdent info `_qed_ens] else mkPatIdent info ac.xId.getId
      return (mkPatIdent info okCtor #[if ac.mInfo.isOption && prep.catchHasNone then mkPatIdent info `some #[inner] else inner], okBody)

@[noinline] private def mkRpcPerformStmt (ctx : RewriteCtx) (st : Syntax) (rpcId : Ident) (srvInfo : ServerInfo)
    (mInfo : ServerMethodInfo) (contCtor : Name) (callArgs rpcCallArgs : Array Term) : CommandElabM Syntax := do
  let callTerm ← withRef rpcId <| Lang.runPQ do
    let cbTerm ← mkAppTermsPure (mkIdentFrom st (ctx.spec.t.getId ++ `Msg ++ contCtor)) callArgs
    `(qedCheckRpcCall% $(mkIdentFrom rpcId srvInfo.serverName):ident $(mkIdentFrom rpcId (Name.mkSimple mInfo.name)):ident [$[$rpcCallArgs:term],*] $cbTerm)
  return Syntax.node (SourceInfo.fromRef st) ``qedStmtExpr #[mkRawExpr callTerm]

private abbrev LiftRecFn := Array (Ident × Term) → Array (Ident × Term) → Array Name → Array Syntax → CommandElabM (Array Syntax × Option (Array Syntax))

@[noinline] private def buildCatchArms (liftRec : LiftRecFn) (ac : AwaitCallCtx) (forCtorParams : Array (Ident × Term)) :
    CommandElabM (Array Syntax × Array Syntax × Bool × Bool) := do
  let info := SourceInfo.fromRef ac.st; let pfx := outcomePrefix ac.mInfo; let strTy ← Lang.runPQ `(String)
  Lang.foldlCmd ac.parsedCatch (#[], #[], false, false) fun (arms, wildArms, covFailed, covNone) (pk, bodyRaw) => do
    match pk with
    | .wildcard =>
        let (bLifted, _) ← liftRec forCtorParams ac.outerParams ac.localNames bodyRaw
        return (arms, wildArms.push (mkCaseStx ac.st (mkPatWild info) bLifted), covFailed, covNone)
    | .dotTag tag bOpt? =>
        let bOuter := match bOpt? with
          | some b => if b.getKind == ``qedPatIdent then shadowOuter ac.outerParams ⟨b.getArg 0⟩ (some strTy) else ac.outerParams
          | none   => ac.outerParams
        let (bLifted, _) ← liftRec forCtorParams bOuter ac.localNames bodyRaw
        let msgPat := bOpt?.getD (mkPatWild info)
        let patS := if tag == "failed" then mkPatIdent info (pfx ++ `failed) #[msgPat]
          else if tag == "none" then mkPatIdent info (pfx ++ `ok) #[mkPatIdent info `none]
          else mkPatIdent info (pfx ++ `err) #[mkPatDot info (Name.mkSimple tag), msgPat]
        return (arms.push (mkCaseStx ac.st patS bLifted), wildArms, covFailed || tag == "failed", covNone || tag == "none")

private def pushSite (ctx : RewriteCtx) (keyPfx : String) (ctor : Name) (params : Array (Ident × Term)) (stmts : Array Syntax)
    (assigns : Array SiteAssign := #[]) : IO Unit :=
  ctx.accum.modify fun a => { a with sites := a.sites.push { key := s!"{keyPfx}:{ctor}", ctor, params, assigns, stmts? := some stmts } }

private def pushSpecDisp (ctx : RewriteCtx) (ctor : Name) (params : Array (Ident × Term)) (stmts : Array Syntax) : IO Unit :=
  ctx.accum.modify fun a => { a with specDispatches := a.specDispatches.push (.mk ctor params stmts) }

@[noinline] private def registerAwaitContSite (ctx : RewriteCtx) (liftRec : LiftRecFn) (ac : AwaitCallCtx) (prep : PreparedAwait)
    (mkOkStmts : Array (Ident × Term) → CommandElabM (Array Syntax × Option (Array Syntax))) : CommandElabM Syntax := do
  let contCtor := Name.mkSimple s!"_cont_{prep.kIdx}"; let outVarId := mkIdentFrom ac.st (Name.mkSimple s!"_qedOut_{prep.kIdx}")
  let contParams := prep.capturedParams.push (outVarId, prep.outTyTerm)
  let (okStmts, restCls?) ← mkOkStmts contParams
  let (okPat, okBody) ← Lang.runPQ (mkOkPatAndBodyPure ac prep okStmts)
  let (catchArms, wildArms, covFailed, covNone) ← buildCatchArms liftRec ac contParams
  let tail := if wildArms.isEmpty && (!covFailed || (ac.mInfo.isOption && !covNone)) then #[mkWildPassCase ac.st] else #[]
  pushSite ctx "cont" contCtor contParams #[mkMatchStx ac.st outVarId (#[mkCaseStx ac.st okPat okBody] ++ catchArms ++ wildArms ++ tail)]
  if let some restCls := restCls? then pushSpecDisp ctx contCtor contParams #[mkMatchStx ac.st outVarId #[mkCaseStx ac.st okPat restCls, mkWildPassCase ac.st]]
  mkRpcPerformStmt ctx ac.st ac.rpcId ac.srvInfo ac.mInfo contCtor prep.callArgs prep.rpcCallArgs

private def mkUnpackedBodyPure (st : Syntax) (wrapKind : EnsuredWrapKind) (valVarId : Ident) (binder? : Option Ident) (bodyStmts : Array Syntax) : PureQuotM (Array Syntax) := do
  let info := SourceInfo.fromRef st; let out := if bodyStmts.isEmpty then #[mkPassSt info] else bodyStmts
  match wrapKind, binder? with
  | .optEnsured, some bId => return #[← mkMapEnsuredLetPure info bId valVarId] ++ out
  | .ensured, _ => return #[mkMatchStx st valVarId #[mkCaseStx st (mkPatIdent info `Qed.Ensured.mk #[binder?.map (mkPatIdent info ·.getId) |>.getD (mkPatWild info), mkPatIdent info `_qed_ens]) out]]
  | .plain, some bId => return if bId.getId.eraseMacroScopes != valVarId.getId.eraseMacroScopes then #[mkLetRawSt info bId none (Syntax.node info ``qedIdent #[valVarId.raw])] ++ out else out
  | _, none => return out

@[noinline] private def liftPredictedAwait (ctx : RewriteCtx) (actionParams : Array (Ident × Term)) (liftRec : LiftRecFn) (ac : AwaitCallCtx)
    (predBody : PredictBody) (onConfirm? : Option (Syntax × Array Syntax)) (rollback? : Option (Syntax × Option Syntax × Array Syntax))
    (catchCasesForCapture preStmts unpredPreStmts : Array Syntax) (rest : List Syntax) : CommandElabM (Array Syntax × Option (Array Syntax)) := do
  let info := SourceInfo.fromRef ac.st; let restArr := rest.toArray
  checkPureSpecStmts ctx false restArr
  if let .block pStmts := predBody then checkPureSpecStmts ctx true pStmts
  let (onConfirmStmts, rollbackStmts) := (onConfirm?.map (·.2) |>.getD #[], rollback?.map (·.2.2) |>.getD #[])
  let prep ← prepareAwaitCall ctx ac (restArr ++ onConfirmStmts ++ rollbackStmts ++ catchCasesForCapture)
  let some rawValTy := prep.xBinderTy?
    | throwErrorAt ac.st s!"cannot infer response type for predicted `await {ac.rpcId.getId}(...)`; add a type annotation `let {ac.xId.getId} : Type = await ...`"
  let wrapKind := ensuredWrapKind ac.mInfo prep.catchHasNone
  let innerEnsTy? ← if wrapKind == .optEnsured then inferAwaitBinderTy? ac.mInfo true else pure none
  if wrapKind != .plain && ac.mInfo.ensPredConst.isNone then throwErrorAt ac.st "internal: missing server `ensures` predicate in `predict`"
  let kIdx := prep.kIdx; let mkNm (p : String) := Name.mkSimple s!"_{p}_{kIdx}"; let mkId (p : String) := mkIdentFrom ac.st (mkNm p)
  let (specContCtor, specValId) := (mkNm "specCont", mkId "specVal")
  let (contPayloadTy, natTy, specContBody) ← Lang.runPQ do
    let ty ← match wrapKind, ac.mInfo.ensPredConst with
      | .optEnsured, some ec => `(Option (Qed.Ensured $(innerEnsTy?.getD rawValTy) ($(← mkAppTermsPure (mkIdent ec) prep.rpcCallArgs))))
      | .ensured, some ec    => `(Qed.Ensured $rawValTy ($(← mkAppTermsPure (mkIdent ec) prep.rpcCallArgs)))
      | _, _                 => pure rawValTy
    return (ty, ← `(Nat), ← mkUnpackedBodyPure ac.st wrapKind specValId (some ac.xId) (← prependOptTyPure info ac.xId ac.optTy? restArr))
  let preCtor? : Option Name ← if preStmts.any stmtHasStateMutation then let c := mkNm "specPre"; pushSite ctx "specPre" c actionParams preStmts; pure (some c) else pure none
  pushSite ctx "specCont" specContCtor (prep.capturedParams.push (specValId, contPayloadTy)) specContBody
  let nextOuter := shadowOuter ac.outerParams ac.xId (some rawValTy)
  let regSubBranch (pfx valPfx : String) (bId? : Option Ident) (bOuter : Array (Ident × Term)) (bStmts : Array Syntax) : CommandElabM Name := do
    let (ctor, valId) := (mkNm pfx, mkId valPfx); let bParams := prep.capturedParams.push (valId, contPayloadTy)
    let (lifted, cls?) ← liftRec bParams bOuter ac.localNames bStmts
    pushSite ctx pfx ctor bParams (← Lang.runPQ (mkUnpackedBodyPure ac.st wrapKind valId bId? lifted))
    if let some cls := cls? then pushSpecDisp ctx ctor bParams cls
    return ctor
  let confirmCtor? ← onConfirm?.mapM fun (_, ocStmts) => regSubBranch "specConfirm" "specConfVal" (some ac.xId) nextOuter ocStmts
  let rollbackCtor? ← rollback?.mapM fun (_, rbBinder?, rbStmts) => do
    let (rbId?, rbOuter) := match rbBinder? with
      | some bStx => if bStx.isIdent then let bId : Ident := ⟨bStx⟩; (some bId, shadowOuter ac.outerParams bId (some rawValTy)) else (none, ac.outerParams)
      | none => (none, ac.outerParams)
    regSubBranch "specRollback" "specRbVal" rbId? rbOuter rbStmts
  let catchCtor? : Option Name ← if ac.parsedCatch.isEmpty then pure none else do
    let (cCtor, cOutId) := (mkNm "specCatch", mkId "specCatchOut"); let cParams := prep.capturedParams.push (cOutId, prep.outTyTerm)
    let (cArms, cWilds, _, _) ← buildCatchArms liftRec ac cParams
    pushSite ctx "specCatch" cCtor cParams #[mkMatchStx ac.st cOutId (cArms ++ cWilds ++ (if cWilds.isEmpty then #[mkWildPassCase ac.st] else #[]))]
    pure (some cCtor)
  let (specResCtor, txIdParam, predParam, outParam) := (mkNm "specRes", mkId "specTxId", mkId "specPred", mkId "specOut")
  pushSite ctx "specRes" specResCtor (#[(txIdParam, natTy)] ++ prep.capturedParams ++ #[(predParam, rawValTy), (outParam, prep.outTyTerm)]) #[mkPassSt info]
  ctx.accum.modify fun a => { a with specResolves := a.specResolves.push (.mk specResCtor txIdParam prep.capturedParams predParam outParam ac.mInfo prep.catchHasNone specContCtor confirmCtor? rollbackCtor? catchCtor? ac.st) }
  let fbPerfSt ← registerAwaitContSite ctx liftRec ac prep fun fbParams => do
    let (ocFbLifted, _) ← if onConfirmStmts.isEmpty then pure (#[], none) else liftRec fbParams nextOuter ac.localNames onConfirmStmts
    return (restArr ++ ocFbLifted, none)
  let nodeIdx ← ctx.accum.modifyGet fun a => (a.specNodes.size, { a with specNodes := a.specNodes.push (.mk ac.st preCtor? (actionParams.map (⟨·.1.raw⟩)) prep.callArgs prep.rpcCallArgs prep.hoistDefs ac.srvInfo ac.mInfo prep.catchHasNone rawValTy innerEnsTy? predBody specContCtor specResCtor) })
  return (unpredPreStmts ++ prep.preLetStmts.push fbPerfSt, some #[mkSpecDispatchMarker info nodeIdx])

@[noinline] private def liftOneAwait (ctx : RewriteCtx) (actionParams outerParams : Array (Ident × Term)) (localNames : Array Name)
    (liftRec : LiftRecFn) (goCont : Array Syntax → List Syntax → CommandElabM (Array Syntax × Option (Array Syntax)))
    (isAssign : Bool) (preStmts : Array Syntax) (st : Syntax) (rest : List Syntax) : CommandElabM (Array Syntax × Option (Array Syntax)) := do
  let info := SourceInfo.fromRef st
  if isAssign then
    let op := atomStr (st.getArg 1)
    if op != "=" then throwErrorAt (st.getArg 1) s!"`await` assignment requires `=`, not `{op}` (use `let v = await ...` then update the field)"
    let some (fRef, fname, path) := parseCompLVal? (st.getArg 0) | do
      let sn := stxSnippet (st.getArg 0)
      throwErrorAt (st.getArg 0) s!"`field = await ...` requires a `Resource` state field path on the left-hand side{if sn.isEmpty then "" else s!", got `{sn}`"}"
    checkMutableField ctx fRef s!"`{fname} = await ...`" fname
    let (rpcId, rawArgs, srvInfo, mInfo) ← resolveAwaitRpc ctx st (unwrapParens1 (st.getArg 2))
    let mkResAssign (rhs : Term) : Syntax := Syntax.node info ``qedStmtAssign #[st.getArg 0, Syntax.atom info "=", mkRawExpr rhs, Syntax.node info nullKind #[]]
    if st.getNumArgs > 3 && (st.getArg 3).getNumArgs == 1 then
      let (_, predBody) ← parsePredictClauseNode ((st.getArg 3).getArg 0)
      let (xId, errId) := (mkIdentFrom st `_qedResPred, mkIdentFrom st `_qedResErr); let errPat := mkPatIdent info errId.getId
      let (failT, notFoundT, loadingT, okT) ← Lang.runPQ do return (← `(Qed.Resource.failed $errId), ← `(Qed.Resource.failed "Not found"), ← `(Qed.Resource.loading), ← `(Qed.Resource.ok $xId))
      let (failAssign, notFoundAssign) := (mkResAssign failT, mkResAssign notFoundT)
      let parsedCatch := mInfo.domainErrTags.map (fun tag => (.dotTag tag (some errPat), #[failAssign])) ++
        (if mInfo.isOption then #[(.dotTag "none" none, #[notFoundAssign])] else #[]) ++ #[(.dotTag "failed" (some errPat), #[failAssign])]
      return ← liftPredictedAwait ctx actionParams liftRec (.mk st xId none rpcId rawArgs srvInfo mInfo parsedCatch outerParams localNames)
        predBody none none #[] preStmts #[mkResAssign loadingT] (mkResAssign okT :: rest)
    let assignSt := mkResAssign (← Lang.runPQ `(Qed.Resource.loading))
    let perfSt ← mkRpcPerformStmt ctx st rpcId srvInfo mInfo (← registerSite ctx.accum #[.mk fname path none] none) #[] rawArgs
    let (tail, tailCls?) ← goCont (preStmts ++ #[assignSt, perfSt]) rest
    return (#[assignSt, perfSt] ++ tail, tailCls?)
  let bStx := st.getArg 1; let isTuple := bStx.getKind == ``qedLetPatTuple
  let xId : Ident := if bStx.isIdent then ⟨bStx⟩ else mkIdentFrom st `_qedAwaitRes
  let optTy? ← lowerOptType (st.getArg 2)
  let (rpcId, rawArgs, srvInfo, mInfo) ← resolveAwaitRpc ctx st (unwrapParens1 (st.getArg 4))
  let clauses ← parseLetClauses (st.getArg 5)
  let catchCases : Array Syntax ← match clauses.catch? with
    | some (_, cNode) => if cNode.getKind == `Qed.Lang.catchArms then pure (cNode.getArg 1).getArgs else throwErrorAt cNode "in client components, use `catch:` with `case .tag: ...` arms"
    | none => pure #[]
  let parsedCatch ← Lang.foldlCmd catchCases #[] fun acc c => return acc ++ (← classifyCatchCase mInfo.domainErrTags mInfo.isOption c)
  let ac : AwaitCallCtx := .mk st xId optTy? rpcId rawArgs srvInfo mInfo parsedCatch outerParams localNames
  let rest' := if isTuple then Syntax.node info ``qedStmtLet #[Syntax.atom info "let", bStx, Syntax.node info nullKind #[], Syntax.atom info "=", Syntax.node info ``qedIdent #[xId.raw], Syntax.node info nullKind #[]] :: rest else rest
  if let some (_, predBody) := clauses.predict? then
    return ← liftPredictedAwait ctx actionParams liftRec ac predBody clauses.onConfirm? clauses.rollback? catchCases preStmts #[] rest'
  let restArr := rest'.toArray; let prep ← prepareAwaitCall ctx ac (restArr ++ catchCases)
  let (nextOuter, nextLocals) := (shadowOuter outerParams xId prep.xBinderTy?, if prep.xBinderTy?.isSome then localNames else localNames.push xId.getId.eraseMacroScopes)
  return (prep.preLetStmts.push (← registerAwaitContSite ctx liftRec ac prep (liftRec · nextOuter nextLocals restArr)), none)

@[noinline] private partial def liftAwaitStmts (ctx : RewriteCtx) (actionParams outerParams : Array (Ident × Term))
    (localLetNames : Array Name) (stmts : Array Syntax) (initPreStmts : Array Syntax := #[]) : CommandElabM (Array Syntax × Option (Array Syntax)) := do
  let liftRec : LiftRecFn := liftAwaitStmts ctx
  let rec go (outerParams : Array (Ident × Term)) (localNames : Array Name) (preStmts : Array Syntax) : List Syntax → CommandElabM (Array Syntax × Option (Array Syntax))
  | [] => return (#[], none)
  | st :: rest => do
      let pushAndGo (o' : Array (Ident × Term)) (l' : Array Name) := do
        let (tail, tailCls?) ← go o' l' (preStmts.push st) rest
        return (#[st] ++ tail, tailCls?.map (#[st] ++ ·))
      match st.getKind with
      | ``qedStmtAssign =>
          if (unwrapParens1 (st.getArg 2)).getKind == ``qedAwait then liftOneAwait ctx actionParams outerParams localNames liftRec (go outerParams localNames) true preStmts st rest
          else if st.getNumArgs > 3 && (st.getArg 3).getNumArgs > 0 then throwErrorAt ((st.getArg 3).getArg 0) "`predict` can only be used on an `await` server RPC call"
          else pushAndGo outerParams localNames
      | ``qedStmtLet =>
          if (unwrapParens1 (st.getArg 4)).getKind == ``qedAwait then liftOneAwait ctx actionParams outerParams localNames liftRec (go outerParams localNames) false preStmts st rest
          else
            if (st.getArg 5).getNumArgs > 0 then throwErrorAt ((st.getArg 5).getArg 0) "`predict`, `on_confirm`, `rollback`, and `catch` can only be used on an `await` server RPC call"
            let bStx := st.getArg 1
            let (outer', locals') ← if bStx.isIdent then
              let lId : Ident := ⟨bStx⟩; let optTy? ← lowerOptType (st.getArg 2)
              pure (shadowOuter outerParams lId optTy?, if optTy?.isSome then localNames else localNames.push lId.getId.eraseMacroScopes)
            else
              let bIds := collectLetBinderIds bStx
              pure (bIds.foldl (init := outerParams) fun acc nm => acc.filter (·.1.getId.eraseMacroScopes != nm), localNames ++ bIds)
            pushAndGo outer' locals'
      | ``qedStmtReturn => return (#[st], none)
      | ``qedStmtIf | ``qedStmtIfLet | ``qedStmtMatch =>
          if stmtContainsAwait st || (hasReturnStmt st && rest.any stmtContainsAwait) then
            unless rest.isEmpty || hasReturnStmt st do
              throwErrorAt st "statements after an `if`/`match` containing `await` are not supported unless the branch `return`s; move trailing statements inside the branches"
            let tailIfReturn := if hasReturnStmt st then rest else []
            let liftBranch (extraLocals : Array Name) (bodyStmts : Array Syntax) :=
              go outerParams (localNames ++ extraLocals.filter fun n => !outerParams.any (·.1.getId.eraseMacroScopes == n)) preStmts (bodyStmts.toList ++ tailIfReturn)
            if let some (stL, stC?) ← mapControlSubSuites st (!tailIfReturn.isEmpty) liftBranch then return (#[stL], stC?.map (#[·]))
          pushAndGo outerParams localNames
      | _ => pushAndGo outerParams localNames
  go outerParams localLetNames initPreStmts stmts.toList

private partial def collectDirectMutFnCalls (mutNames : Array Name) (stx : Syntax) : Array Name :=
  if stx.getKind == ``qedStmtExpr then
    let u := unwrapParens1 (stx.getArg 0)
    if u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent then
      let cn := ((u.getArg 0).getArg 0).getId.eraseMacroScopes; if mutNames.contains cn then #[cn] else #[]
    else #[]
  else stx.getArgs.foldl (init := #[]) fun acc ch => (collectDirectMutFnCalls mutNames ch).foldl pushUnique acc

private partial def checkAsyncFnCycles (fnMap : Std.HashMap Name CompFnDecl) (edges : Std.HashMap Name (Array Name))
    (visiting visited : Std.HashSet Name) (cur : Name) : CommandElabM (Std.HashSet Name) := do
  if visiting.contains cur then throwErrorAt ((fnMap[cur]?.map (·.id.raw)).getD Syntax.missing) s!"recursive `await` call cycle in component `fn {cur}`"
  if visited.contains cur then return visited
  let vis ← Lang.foldlCmd (edges[cur]?.getD #[]) visited fun v nxt => checkAsyncFnCycles fnMap edges (visiting.insert cur) v nxt
  return vis.insert cur

@[noinline] private partial def inlineAsyncMutFns (asyncMap : Std.HashMap Name CompFnDecl) (cntRef : IO.Ref Nat)
    (fuel : Nat) (stmts : Array Syntax) : CommandElabM (Array Syntax) := do
  if asyncMap.isEmpty then return stmts
  Lang.foldlCmd stmts.zipIdx #[] fun out (st, i) => do
    let info := SourceInfo.fromRef st
    if st.getKind == ``qedStmtExpr then
      let u := unwrapParens1 (st.getArg 0)
      if u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent then
        let cn := ((u.getArg 0).getArg 0).getId.eraseMacroScopes
        if let some mfn := asyncMap[cn]? then
          if fuel == 0 then throwErrorAt st s!"`fn {cn}` expansion exceeded depth limit"
          let rawArgs := (u.getArg 2).getSepArgs
          if rawArgs.size != mfn.params.size then throwErrorAt st s!"`{cn}(...)` expects {mfn.params.size} argument(s), got {rawArgs.size}"
          Lang.foldlCmd rawArgs () fun _ ra => unless ra.getKind == ``qedCallArgPos do throwErrorAt ra s!"named arguments are not supported in `{cn}(...)`"
          if i + 1 < stmts.size && mfn.stmts.any hasReturnStmt then throwErrorAt st s!"cannot have trailing statements after calling async `fn {cn}` which uses `return`"
          let callIdx ← cntRef.modifyGet fun n => (n, n + 1)
          let argTmps := (Array.range rawArgs.size).map fun j => mkIdentFrom st (Name.mkSimple s!"_fnArg_{callIdx}_{j}")
          let tmpLets := rawArgs.zipIdx.map fun (ra, j) => mkTypedLetStmt info argTmps[j]! mfn.rawParamTys[j]? (ra.getArg 0)
          let paramLets := mfn.params.zipIdx.map fun ((pId, _), j) => mkTypedLetStmt info pId mfn.rawParamTys[j]? (Syntax.node info ``qedIdent #[argTmps[j]!.raw])
          return out ++ tmpLets ++ paramLets ++ (← inlineAsyncMutFns asyncMap cntRef (fuel - 1) mfn.stmts)
      return out.push st
    if let some (st', _) ← mapControlSubSuites st false (fun _ ss => return (← inlineAsyncMutFns asyncMap cntRef fuel ss, none)) then return out.push st'
    return out.push st

@[noinline] private def registerActionOrPort (spec : ComponentSpec) (baseCtx : RewriteCtx) (asyncMap : Std.HashMap Name CompFnDecl) (cntRef : IO.Ref Nat)
    (kindPrefix dupLabel conflictLabel : String) (nameRef errRef : Syntax) (name : Name)
    (params : Array (Ident × Term)) (bodyStx : Syntax) (checkPlaceholders : Bool) : CommandElabM Unit := do
  if (← baseCtx.accum.get).sites.any (·.ctor == name) then throwErrorAt nameRef s!"duplicate {dupLabel} name `{name}`"
  if spec.collections.any (·.1.getId == name) then throwErrorAt nameRef s!"{conflictLabel} name `{name}` conflicts with `collection {name}`"
  let expanded ← inlineAsyncMutFns asyncMap cntRef 32 (suiteStmts (← rewriteIn baseCtx false bodyStx))
  let (stmts, dispCls?) ← liftAwaitStmts baseCtx params params #[] expanded
  if let some dispStmts := dispCls? then pushSpecDisp baseCtx name params dispStmts
  let dummyAssigns ← if !checkPlaceholders then pure #[] else do
    let ds ← Lang.foldlCmd stmts #[] fun acc s =>
      if s.getKind == ``qedStmtAssign && (s.getArg 0).getKind == ``qedIdent && atomStr (s.getArg 1) == "=" && isPlaceholder (s.getArg 2) then
        pushHandlerAssign baseCtx acc ((s.getArg 0).getArg 0) none
      else pure acc
    if !params.isEmpty && !ds.isEmpty then
      throwErrorAt errRef s!"action `{name}` declares explicit parameter(s) and cannot use the `_` placeholder; assign explicitly (e.g. `{ds[0]!.field} = {params[0]!.1.getId}`)"
    pure ds
  pushSite baseCtx kindPrefix name params stmts dummyAssigns

private def checkCompParams (spec : ComponentSpec) (kindLabel : String) (ownerName : Name) (params : Array (Ident × Term)) : CommandElabM Unit := do
  discard <| Lang.foldlCmd params (#[] : Array Name) fun seen (pId, _) => do
    let pn := pId.getId
    if seen.contains pn then throwErrorAt pId s!"duplicate parameter `{pn}` in {kindLabel} `{ownerName}`"
    if spec.allNames.contains pn then throwErrorAt pId s!"parameter `{pn}` in {kindLabel} `{ownerName}` shadows a component field; rename the parameter"
    pure (seen.push pn)

@[noinline] def collectSitesAndRewriteStateful (spec : ComponentSpec) : CommandElabM RewriteResult := do
  let baseCtx ← mkRewriteCtx spec false
  let allRwFns ← Lang.mapCmd spec.fns fun f => do
    checkCompParams spec "fn" f.id.getId f.params
    let stmts' ← Lang.mapCmd f.stmts (rewriteIn baseCtx false)
    if f.isPure && stmts'.any stmtContainsAwait then
      throwErrorAt f.id s!"cannot use `await` inside pure component `fn {f.id.getId}`; remove `-> ReturnType` for an async mutating helper, or perform `await` in the calling `action`"
    return { f with stmts := stmts' }
  let mutFnNames := (allRwFns.filter CompFnDecl.isMut).map (·.id.getId.eraseMacroScopes)
  let (fnMap, edges, asyncMap0) := allRwFns.foldl (init := ({}, {}, {})) fun (fm, ed, am) f =>
    if !f.isMut then (fm, ed, am) else
    let nm := f.id.getId.eraseMacroScopes
    let es := f.stmts.foldl (init := #[]) fun acc s => (collectDirectMutFnCalls mutFnNames s).foldl pushUnique acc
    (fm.insert nm f, ed.insert nm es, if f.stmts.any stmtContainsAwait then am.insert nm f else am)
  let rec closeAsync (am : Std.HashMap Name CompFnDecl) : Nat → Std.HashMap Name CompFnDecl
    | 0 => am
    | fuel + 1 =>
        let (am', changed) := mutFnNames.foldl (init := (am, false)) fun (acc, ch) nm =>
          if !acc.contains nm && (edges[nm]?.getD #[]).any acc.contains then
            match fnMap[nm]? with | some f => (acc.insert nm f, true) | none => (acc, ch)
          else (acc, ch)
        if changed then closeAsync am' fuel else am'
  let asyncMap := closeAsync asyncMap0 (mutFnNames.size + 1)
  discard <| Lang.foldlCmd mutFnNames ({} : Std.HashSet Name) fun vis nm => if asyncMap.contains nm then checkAsyncFnCycles fnMap edges {} vis nm else pure vis
  let rwFns := allRwFns.filter fun f => !(f.isMut && asyncMap.contains f.id.getId.eraseMacroScopes)
  let cntRef ← IO.mkRef 0
  Lang.foldlCmd spec.actions () fun _ a => do
    let name := (a.getArg 1).getId; let params ← parseParamList (a.getArg 2)
    checkCompParams spec "action" name params
    registerActionOrPort spec baseCtx asyncMap cntRef "action" "action" "action" (a.getArg 1) a name params (a.getArg 4) true
  Lang.foldlCmd spec.portIns () fun _ p => do
    if spec.allNames.contains p.argId.getId then throwErrorAt p.argId s!"port parameter `{p.argId.getId}` on `port {p.id.getId}` shadows a component field; rename the parameter"
    registerActionOrPort spec baseCtx asyncMap cntRef "port" "port/action" "port" p.id p.id p.id.getId #[(p.argId, p.argTy)] p.body false
  let route'? ← spec.route?.mapM fun rd => do
    let (rParamId, rParams) := (mkIdent `_r, #[(mkIdent `_r, rd.ty)])
    let rFieldAssign := Syntax.node .none ``qedStmtAssign #[Syntax.node .none ``qedIdent #[rd.field.raw], Syntax.atom .none "=", Syntax.node .none ``qedIdent #[rParamId.raw], Syntax.node .none nullKind #[]]
    let altPairs ← Lang.mapCmd rd.alts fun alt => do
      let expanded ← inlineAsyncMutFns asyncMap cntRef 32 (suiteStmts (← rewriteIn baseCtx false (alt.getArg 3)))
      let (lifted, altC?) ← liftAwaitStmts baseCtx rParams #[] (collectCasePatIds (extractCasePatAlts (alt.getArg 1))) expanded (initPreStmts := #[rFieldAssign])
      pure (setStxArg alt 3 (packSuite alt lifted), alt, altC?)
    if altPairs.any (·.2.2.isSome) then
      pushSpecDisp baseCtx `_onRoute rParams #[rFieldAssign, mkMatchStx rd.field rParamId (altPairs.map fun (_, alt, ac?) => setStxArg alt 3 (packSuite alt (ac?.getD #[])))]
    pure { rd with alts := altPairs.map (·.1) }
  let rwSubBranch (ss : Array Syntax) : CommandElabM (Array Syntax) := do
    let ss' ← Lang.mapCmd ss (rewriteIn baseCtx false)
    Lang.foldlCmd ss' () fun _ s => if let some bad := (collectDirectMutFnCalls mutFnNames s).find? asyncMap.contains then throwErrorAt s s!"cannot call async `fn {bad}` inside a `subscribe` handler" else pure ()
    return ss'
  let rwSubs ← Lang.mapCmd spec.subscriptions fun sub => return { sub with
    onJoin? := ← sub.onJoin?.mapM fun (b?, ss) => return (b?, ← rwSubBranch ss)
    onMsg? := ← sub.onMsg?.mapM fun (b, ss) => return (b, ← rwSubBranch ss)
    onStatus? := ← sub.onStatus?.mapM fun (b, ss) => return (b, ← rwSubBranch ss) }
  let starts' ← Lang.mapCmd spec.starts fun s => do lowerCompExpr .val (← rewriteIn { baseCtx with inPerform := true } false s)
  let body' ← lowerCompExpr .val (← rewriteIn { baseCtx with allowHoist := true, wrapMsg? := if spec.hasSlotsOrKids then some (mkIdent `_wrap) else none } false spec.body)
  return .mk (← baseCtx.accum.get) route'? starts' body' rwFns rwSubs

end CompElab
end Qed
