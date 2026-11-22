import Qed.Server.FnElab
import Qed.Server.Jobs

namespace Qed.Server
open Qed.Lang

/-! ## `server` `every <duration> <name>:` Background Job Elaborator -/

section JobElab
open Lean Elab Command

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

/-- Elaborates all `every <dur> <name>:` clauses in a `server` block, verifying every job
    against all server invariants (single-state, `old(...)` two-state, `mutating`, and
    race-free `atomic:` rules around `await`) and emitting `<Server>.jobs` / `<Server>.verifiedJobs`. -/
def elabServerJobs (existingMethods : Array ServerMethodInfo) (jobClauses : Array Syntax) :
    SrvElabM (Option (Array String)) := do
  if jobClauses.isEmpty then return some #[]
  let c ← read
  let mut jobNames : Array String := #[]
  let mut runtimeJobTerms : Array Term := #[]
  let mut verifiedJobTerms : Array Term := #[]
  let payloadTerm ← `(Unit)
  let errTyTerm ← `(Qed.Server.ApiError)
  let emptyCtx ← `(({} : Qed.Server.RequestCtx))
  let callArgs : Array Term := c.envIdents.map (⟨·.raw⟩) ++ #[emptyCtx]

  for jc in jobClauses do
    let jobIdent : Ident := ⟨jc.getArg 3⟩
    let jobStr := jobIdent.getId.toString
    if existingMethods.any (·.name == jobStr) || jobNames.contains jobStr then
      throwErrorAt jobIdent s!"duplicate job or method name `{jobStr}` in `server {c.srvName}`"
    let intervalMs ← liftM <| parseJobDurationMs (jc.getArg 1) (jc.getArg 2) jobStr
    let bodyStmts := ensureUnitReturn jobIdent (suiteStmts (jc.getArg 5))
    let isAsyncJob := c.hasState && (blockHasAwait bodyStmts || blockHasAtomic bodyStmts)
    let baseCtx ← mkBaseLowerCtx jobStr #[] isAsyncJob true true
    let some (runExpr, isRO, hasEmit) ← elabServerHandler isAsyncJob jobStr jobIdent
        #[] #[] #[] payloadTerm errTyTerm baseCtx bodyStmts none (ctxArg? := some emptyCtx) | return none
    let proofExpr? : Option Term ←
      if !c.hasState then pure none
      else if isAsyncJob then
        let invThmId := mkIdentFrom jobIdent (c.srvName ++ jobIdent.getId.appendAfter "_inv")
        some <$> mkAppTerms invThmId callArgs
      else if isRO then
        some <$> if hasEmit then `(Qed.Server.progPreservesInv_of_pureStepReadEmit _)
          else `(Qed.Server.progPreservesInv_of_pureStepRead _)
      else
        let invThmId := mkIdentFrom jobIdent (c.srvName ++ jobIdent.getId.appendAfter "_inv")
        let invApp ← mkAppTerms (← `($invThmId _s)) callArgs
        some <$> if hasEmit then `(Qed.Server.progPreservesInv_of_pureStepEmit _ (fun _s _h => $invApp _h))
          else `(Qed.Server.progPreservesInv_of_pureStep _ (fun _s _h => $invApp _h))

    let (wrappedRun, wrappedPf?) ← liftM <| wrapWithEnvDecls c.envDecls runExpr proofExpr?
    let nameLit := Syntax.mkStrLit jobStr
    let msLit := Syntax.mkNumLit (toString intervalMs)
    let posPf ← `(by decide)
    if c.hasState then
      let runMTerm ← `(fun {m} [Monad m] [Qed.Server.MonadServer m] [Qed.Server.MonadAtomic $(c.stateId) m] => $wrappedRun)
      runtimeJobTerms := runtimeJobTerms.push (← `({
        name := $nameLit, intervalMs := $msLit, intervalPos := $posPf, runM := $runMTerm
        : Qed.Server.ServerJob $(c.stateId) }))
      if let some pf := wrappedPf? then
        verifiedJobTerms := verifiedJobTerms.push (← `({
          name := $nameLit, intervalMs := $msLit, intervalPos := $posPf, runM := $runMTerm, preserves := $pf
          : Qed.Server.VerifiedJob $(c.stateId) $(c.stateInvId) }))
    else
      runtimeJobTerms := runtimeJobTerms.push (← `({
        name := $nameLit, intervalMs := $msLit, intervalPos := $posPf,
        runM := fun {m} [Monad m] [Qed.Server.MonadServer m] => $wrappedRun
        : Qed.Server.StatelessJob }))
    jobNames := jobNames.push jobStr

  let jobsId := mkIdentFrom c.srvIdent (c.srvName ++ `jobs)
  let jobNamesId := mkIdentFrom c.srvIdent (c.srvName ++ `jobNames)
  let nameLits : Array Term := jobNames.map (Syntax.mkStrLit ·)
  liftM <| elabCommand (← `(command| def $jobNamesId : List String := [$[$nameLits],*]))
  if c.hasState then
    liftM <| elabCommand (← `(command|
      def $jobsId : Array (Qed.Server.ServerJob $(c.stateId)) := #[$[$runtimeJobTerms],*]))
    let verifiedJobsId := mkIdentFrom c.srvIdent (c.srvName ++ `verifiedJobs)
    deferSrvCmd (← `(command|
      def $verifiedJobsId : Array (Qed.Server.VerifiedJob $(c.stateId) $(c.stateInvId)) := #[$[$verifiedJobTerms],*]))
  else
    liftM <| elabCommand (← `(command|
      def $jobsId : Array Qed.Server.StatelessJob := #[$[$runtimeJobTerms],*]))
  return some jobNames

end JobElab

end Qed.Server
