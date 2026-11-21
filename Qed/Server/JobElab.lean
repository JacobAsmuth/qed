import Qed.Server.FnElab
import Qed.Server.Jobs

namespace Qed.Server
open Qed.Lang

/-! ## `server` `every <duration> <name>:` Background Job Elaborator -/

private def ensureJobUnitReturn (ref : Lean.Syntax) (stmts : Array Lean.Syntax) : Array Lean.Syntax :=
  if blockAlwaysReturns stmts then stmts
  else
    let info := Lean.SourceInfo.fromRef ref
    stmts.push (Lean.Syntax.node info ``qedStmtReturn #[Lean.Syntax.atom info "return", Lean.Syntax.node info Lean.nullKind #[]])

private partial def stmtHasAtomic (stx : Lean.Syntax) : Bool :=
  stx.getKind == ``qedStmtAtomic || stx.getArgs.any stmtHasAtomic

private def blockHasAtomic (stmts : Array Lean.Syntax) : Bool :=
  stmts.any stmtHasAtomic

open Lean Elab Command in
private def parseJobDurationMs (numStx unitStx : Syntax) (jobStr : String) : CommandElabM Nat := do
  let n := (⟨numStx⟩ : TSyntax `num).getNat
  let unitStr := unitStx.getId.eraseMacroScopes.toString
  let unit ← match unitStr with
    | "ms" => pure DurationUnit.ms
    | "s"  => pure DurationUnit.s
    | "m"  => pure DurationUnit.m
    | "h"  => pure DurationUnit.h
    | _    =>
        throwErrorAt unitStx s!"unknown duration unit `{unitStr}` in `every {n}{unitStr} {jobStr}`; supported units are `ms`, `s`, `m`, `h`"
  let ms := durationToMs n unit
  if ms == 0 then
    throwErrorAt numStx s!"background job `{jobStr}` interval must be positive (got `{n}{unitStr}`)"
  return ms

open Lean Elab Command in
private def wrapJobWithEnvDecls (envDecls : Array ParsedEnvDecl)
    (innerRun : Term) (innerProof? : Option Term) : CommandElabM (Term × Option Term) :=
  envDecls.foldrM (init := (innerRun, innerProof?)) fun ed (accRun, accPf?) => do
    let eid := ed.ident
    let keyLit := Syntax.mkStrLit ed.osKey
    match ed.default? with
    | some defVal =>
        let defLit := Syntax.mkStrLit defVal
        let run' ← `(Qed.Server.MonadServer.readEnv $keyLit >>= fun _envOpt =>
          (fun ($eid:ident : String) => $accRun) (_envOpt.getD $defLit))
        let pf'? ← accPf?.mapM fun pf =>
          `(Qed.Server.progPreservesInv_readEnv_default $keyLit $defLit
              (fun ($eid:ident : String) => $accRun)
              (fun ($eid:ident : String) => $pf))
        pure (run', pf'?)
    | none =>
        let missingMsg := Syntax.mkStrLit s!"missing required environment variable `{ed.osKey}`"
        let run' ← `(Qed.Server.MonadServer.readEnv $keyLit >>= fun _envOpt =>
          match _envOpt with
          | some $eid:ident => $accRun
          | none => Pure.pure (Except.error (Qed.Server.ApiError.internal $missingMsg)))
        let pf'? ← accPf?.mapM fun pf =>
          `(Qed.Server.progPreservesInv_readEnv_required $keyLit $missingMsg
              (fun ($eid:ident : String) => $accRun)
              (fun ($eid:ident : String) => $pf))
        pure (run', pf'?)

open Lean Elab Command in
/-- Elaborates all `every <dur> <name>:` clauses in a `server` block, verifying every job
    against all server invariants (single-state, `old(...)` two-state, `mutating`, and
    race-free `atomic:` rules around `await`) and emitting `<Server>.jobs` / `<Server>.verifiedJobs`. -/
def elabServerJobs (priorRep priorUnrep : Nat)
    (srvIdent : Ident) (srvName : Name) (hasState : Bool)
    (stateId stateInvId ctxId : Ident)
    (envDecls : Array ParsedEnvDecl) (envIdents : Array Ident) (envTypes : Array Term)
    (stateFieldNames envVarNames : Array String)
    (dbBindings : Array (String × DatabaseInfo))
    (invs : Array ParsedInv) (mutInvs : Array ParsedMutInv)
    (chanSigs : Array SrvChanSig) (existingMethods : Array ServerMethodInfo)
    (jobClauses : Array Syntax)
    (deferredProofs : IO.Ref (Array (CommandElabM Bool))) :
    CommandElabM (Option (Array String × Array Name)) := do
  if jobClauses.isEmpty then return some (#[], #[])
  let mut jobNames : Array String := #[]
  let mut allExtRoots : Array Name := #[]
  let mut runtimeJobTerms : Array Term := #[]
  let mut verifiedJobTerms : Array Term := #[]
  let payloadTerm ← `(Unit)
  let errTyTerm ← `(Qed.Server.ApiError)
  let allBinderIds := envIdents ++ #[ctxId]
  let allBinderTys := envTypes ++ #[← `(Qed.Server.RequestCtx)]
  let emptyCtxTerm ← `(({} : Qed.Server.RequestCtx))
  let callArgs : Array Term := envIdents.map (⟨·.raw⟩) ++ #[emptyCtxTerm]

  for jc in jobClauses do
    let numStx := jc.getArg 1
    let unitStx := jc.getArg 2
    let jobIdent : Ident := ⟨jc.getArg 3⟩
    let jobStr := jobIdent.getId.toString
    if existingMethods.any (·.name == jobStr) || jobNames.contains jobStr then
      throwErrorAt jobIdent s!"duplicate job or method name `{jobStr}` in `server {srvName}`"
    let intervalMs ← parseJobDurationMs numStx unitStx jobStr
    let bodyStmts := ensureJobUnitReturn jobIdent (suiteStmts (jc.getArg 5))
    let hasAwait := blockHasAwait bodyStmts
    let hasAtomic := blockHasAtomic bodyStmts
    let hasEmit := blockHasEmit bodyStmts
    let isAsyncJob := hasState && (hasAwait || hasAtomic)
    let baseCtx : LowerCtx := {
      fnName := jobStr, stateFields := stateFieldNames, envVars := envVarNames, locals := #[]
      stateRule := if hasState then .pureStep (mkIdent `_s0) else .statelessServer
      allowAwait := isAsyncJob, allowUnwrap := true
      hasFallible := true, isOption := false, innerOptTy? := none
      domainErrTy? := none, channels := chanSigs, dbs := dbBindings
    }
    let (runExpr, proofExpr?, bodyExtRoots) ←
      if isAsyncJob then
        let some (hApp, _isRO, er) ← elabServerAsyncFn priorRep priorUnrep srvName jobStr jobIdent
            stateId stateInvId allBinderIds allBinderTys callArgs payloadTerm errTyTerm baseCtx
            bodyStmts invs mutInvs stateFieldNames envVarNames none deferredProofs | return none
        let invThmId := mkIdentFrom jobIdent (srvName ++ jobIdent.getId.appendAfter "_inv")
        let pfApp ← callArgs.foldlM (init := ← `($invThmId)) fun acc a => `($acc $a)
        pure (hApp, some pfApp, er)
      else if hasState then
        let some (pureRun, isRO, er) ← elabServerPureFn priorRep priorUnrep srvName jobStr jobIdent
            stateId stateInvId allBinderIds allBinderTys callArgs payloadTerm errTyTerm baseCtx
            bodyStmts invs mutInvs stateFieldNames envVarNames none deferredProofs | return none
        let pfTerm ← if isRO then
          if hasEmit then `(Qed.Server.progPreservesInv_of_pureStepReadEmit _)
          else `(Qed.Server.progPreservesInv_of_pureStepRead _)
        else
          let invThmId := mkIdentFrom jobIdent (srvName ++ jobIdent.getId.appendAfter "_inv")
          let invApp ← callArgs.foldlM (init := ← `($invThmId _s)) fun acc a => `($acc $a)
          if hasEmit then
            `(Qed.Server.progPreservesInv_of_pureStepEmit _ (fun _s _h => $invApp _h))
          else
            `(Qed.Server.progPreservesInv_of_pureStep _ (fun _s _h => $invApp _h))
        pure (pureRun, some pfTerm, er)
      else
        let some (_handlerId, _hCall, hApp, er, _hasDbWrite) ←
            elabStatelessHandler priorRep priorUnrep jobIdent srvName jobIdent.getId
              allBinderIds allBinderTys callArgs payloadTerm errTyTerm baseCtx bodyStmts | return none
        pure (hApp, none, er)

    let (wrappedRun, wrappedPf?) ← wrapJobWithEnvDecls envDecls runExpr proofExpr?
    let nameLit := Syntax.mkStrLit jobStr
    let msLit := Syntax.mkNumLit (toString intervalMs)
    let posPf ← `(by decide)
    if hasState then
      let rtTerm ← `({ name := $nameLit, intervalMs := $msLit, intervalPos := $posPf,
                       runM := fun {m} [Monad m] [Qed.Server.MonadServer m] [Qed.Server.MonadAtomic $stateId m] => $wrappedRun
                       : Qed.Server.ServerJob $stateId })
      runtimeJobTerms := runtimeJobTerms.push rtTerm
      if let some pf := wrappedPf? then
        let vTerm ← `({ name := $nameLit, intervalMs := $msLit, intervalPos := $posPf,
                        runM := fun {m} [Monad m] [Qed.Server.MonadServer m] [Qed.Server.MonadAtomic $stateId m] => $wrappedRun,
                        preserves := $pf
                        : Qed.Server.VerifiedJob $stateId $stateInvId })
        verifiedJobTerms := verifiedJobTerms.push vTerm
    else
      let rtTerm ← `({ name := $nameLit, intervalMs := $msLit, intervalPos := $posPf,
                       runM := fun {m} [Monad m] [Qed.Server.MonadServer m] => $wrappedRun
                       : Qed.Server.StatelessJob })
      runtimeJobTerms := runtimeJobTerms.push rtTerm

    jobNames := jobNames.push jobStr
    allExtRoots := allExtRoots ++ bodyExtRoots.filter (!allExtRoots.contains ·)

  let jobsId := mkIdentFrom srvIdent (srvName ++ `jobs)
  let jobNamesId := mkIdentFrom srvIdent (srvName ++ `jobNames)
  let nameLits : Array Term := jobNames.map fun s => (Syntax.mkStrLit s : Term)
  elabCommand (← `(command| def $jobNamesId : List String := [$[$nameLits],*]))
  if hasState then
    elabCommand (← `(command|
      def $jobsId : Array (Qed.Server.ServerJob $stateId) := #[$[$runtimeJobTerms],*]))
    let verifiedJobsId := mkIdentFrom srvIdent (srvName ++ `verifiedJobs)
    deferredProofs.modify (·.push do
      elabCommand (← `(command|
        def $verifiedJobsId : Array (Qed.Server.VerifiedJob $stateId $stateInvId) := #[$[$verifiedJobTerms],*]))
      return !hasNewErrors (← get).messages priorRep priorUnrep)
  else
    elabCommand (← `(command|
      def $jobsId : Array Qed.Server.StatelessJob := #[$[$runtimeJobTerms],*]))
  return some (jobNames, allExtRoots)

end Qed.Server
