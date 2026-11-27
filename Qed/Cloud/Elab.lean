import Qed.Cloud.Gcp
import Qed.Server.Registry

namespace Qed.Cloud

/-! ## `deploy` Block Surface Syntax & Elaborator (`Qed.Cloud.Elab`) -/

declare_syntax_cat deployClause
declare_syntax_cat deployPreviewClause

section DeployParsers
open Lean Parser Qed.Lang

private def kwP (kw : Name) (p : Parser) : Parser :=
  withPosition (atomic (identEq kw) >> p)

def deployUnitLit : Parser :=
  node `Qed.Cloud.unitLit (numLit >> checkNoWsBefore "expected unit suffix without space" >> ident)

@[deployPreviewClause_parser] def deployPreviewOnPrClause : Parser := leading_parser kwP `on_pr (identEq `true <|> identEq `false)
@[deployPreviewClause_parser] def deployPreviewSubdomainClause : Parser := leading_parser kwP `subdomain strLit
@[deployPreviewClause_parser] def deployPreviewDomainClause : Parser := leading_parser kwP `domain strLit
@[deployPreviewClause_parser] def deployPreviewProtectionClause : Parser := leading_parser kwP `protection (identEq `team_only <|> identEq `anyone <|> symbol "public")
@[deployPreviewClause_parser] def deployPreviewTtlClause : Parser := leading_parser kwP `ttl deployUnitLit

@[deployClause_parser] def deployAppClause : Parser := leading_parser kwP `app ident
@[deployClause_parser] def deployRegionsClause : Parser := leading_parser kwP `regions ("[" >> sepBy1 ident "," >> "]")
@[deployClause_parser] def deployDomainClause : Parser := leading_parser kwP `domain strLit
@[deployClause_parser] def deployComputeClause : Parser := leading_parser kwP `compute ident
@[deployClause_parser] def deployTimeoutClause : Parser := leading_parser kwP `timeout deployUnitLit
@[deployClause_parser] def deployPreviewBlockClause : Parser := leading_parser
  kwP `preview (":" >> checkColGt "expected indented `preview:` clauses" >> many1Indent (categoryParser `deployPreviewClause 0))
@[deployClause_parser] def deployInvClause : Parser := leading_parser
  withPosition ("invariant " >> ident >> ":" >> sepBy1 (categoryParser `qedExpr 0) ",")

@[command_parser] def deployCmd : Parser := leading_parser
  withPosition ("deploy " >> ident >> ":" >> checkColGt "expected indented `deploy` clauses" >> many1Indent (categoryParser `deployClause 0))

end DeployParsers

open Lean Elab Command Qed.Lang Qed.Server

/-! ## Persistent `deploy` Registry & `deploy` Command Elaborator -/

structure DeployInfo where
  deployName : Lean.Name
  specConst  : Lean.Name
  spec       : DeploySpec
deriving Inhabited, Repr

initialize deployRegistry : Lean.SimplePersistentEnvExtension DeployInfo (Lean.NameMap DeployInfo) ←
  Qed.Diag.mkNameMapExt (·.deployName)

@[noinline] private def parseDurationUnit (stx : Syntax) : CommandElabM Nat := do
  let (n, unit) := ((⟨stx.getArg 0⟩ : TSyntax `num).getNat, (stx.getArg 1).getId.eraseMacroScopes.toString.toLower)
  match unit with
  | "s" | "sec" => return n | "m" | "min" => return n * 60 | "h" | "hr" => return n * 3600 | "d" | "day" => return n * 86400
  | _ => throwErrorAt stx s!"invalid duration unit `{n}{unit}` (expected `s`, `m`, `h`, or `d`, e.g. `60s`, `5m`, `7d`)"

private def regionTerm (r : GcpRegion) : Term := mkIdent (`Qed.Cloud.GcpRegion ++ Name.mkSimple (r.toString.replace "-" "_"))
private def computeTerm (t : ComputeTier) : Term := mkIdent (`Qed.Cloud.ComputeTier ++ Name.mkSimple t.toString)

@[noinline] private def deploySpecToTerm (d : DeploySpec) : CommandElabM Term := do
  let regTms : Array Term := d.regions.toArray.map regionTerm
  let hostTm : Term ← match d.preview.host? with
    | none => `(Option.none) | some (.exact h) => `(Option.some (Qed.Cloud.HostPattern.exact $(quote h)))
    | some (.wildcard s) => `(Option.some (Qed.Cloud.HostPattern.wildcard $(quote s)))
  let protTm : Term := mkIdent (match d.preview.protection with | .team_only => `Qed.Cloud.PreviewProtection.team_only | .pub => `Qed.Cloud.PreviewProtection.pub)
  `(({ name := $(quote d.name), appName := $(quote d.appName), regions := [$[$regTms:term],*], domain? := $(quote d.domain?),
       compute := $(computeTerm d.compute), timeoutSec? := $(quote d.timeoutSec?),
       preview := { enabled := $(quote d.preview.enabled), subdomain? := $(quote d.preview.subdomain?), host? := $hostTm, protection := $protTm, ttlSec := $(quote d.preview.ttlSec) }
    } : Qed.Cloud.DeploySpec))

private def deploySpecFields : Array (String × Name) := #[("compute", `compute), ("timeout_sec", `timeoutSec?), ("regions", `regions), ("domain", `domain?)]
private def previewFieldAliases : Array (String × Name) := #[
  ("enabled", `enabled), ("on_pr", `enabled), ("subdomain", `subdomain?), ("subdomain?", `subdomain?),
  ("host", `host?), ("host?", `host?), ("domain", `host?), ("protection", `protection), ("ttl_sec", `ttlSec), ("ttlSec", `ttlSec)]

@[noinline] private def lowerDeployInvExpr (specId : Ident) (stx : Syntax) : CommandElabM Term := do
  let fail (ref : Syntax) (msg : String) : ReaderT (Array String) CommandElabM Term := throwErrorAt ref msg
  let hooks : LowerHooks (ReaderT (Array String) CommandElabM) := { LowerHooks.mkDefault fail with
    withLocals := fun names act => withReader (· ++ names) act
    lowerIdent := fun ref id mode => do
      let locals ← read
      match id.getId.eraseMacroScopes.components with
      | [] => throwErrorAt ref "empty identifier in deploy invariant"
      | root :: rest =>
          let rs := root.toString
          if locals.contains rs then foldProjTerms ref (mkIdentFrom ref root) rest
          else if rs == "preview" then
            match rest with
            | [] => `(($specId).preview)
            | f :: more =>
                let fs := f.toString
                if fs == "ttl" then throwErrorAt ref "use `preview.ttl_sec` (in seconds) inside deploy invariants"
                let some (_, fn) := previewFieldAliases.find? (·.1 == fs)
                  | throwErrorAt ref s!"unknown `preview` field `{fs}` in deploy invariant{Qed.Diag.didYouMean fs ["enabled", "subdomain", "host", "protection", "ttl_sec"]}"
                foldProjTerms ref (← `(($specId).preview.$(mkIdentFrom ref fn):ident)) more
          else if let some (_, fld) := deploySpecFields.find? (·.1 == rs) then foldProjTerms ref (← `(($specId).$(mkIdentFrom ref fld):ident)) rest
          else if !rest.isEmpty then foldProjTerms ref (mkIdentFrom ref root) rest
          else match rs with
            | "true" => if mode == .propInv then `(True) else `(true) | "false" => if mode == .propInv then `(False) else `(false)
            | "none" => `(Option.none) | "team_only" => `(Qed.Cloud.PreviewProtection.team_only) | "anyone" | "pub" => `(Qed.Cloud.PreviewProtection.pub)
            | "timeout" => throwErrorAt ref "use `timeout_sec` (Option Nat, in seconds) inside deploy invariants"
            | _ => if let some t := ComputeTier.parse? rs then pure (computeTerm t)
                   else if let some r := GcpRegion.parse? rs then pure (regionTerm r) else pure (mkIdentFrom ref root) }
  (lowerQedExpr hooks .propInv stx).run #[]

private structure ParsedDeploy where
  seenTop     : Array Name := #[]
  appIdent?   : Option Ident := none
  regions?    : Option (List GcpRegion) := none
  regionsRef? : Option Syntax := none
  domain?     : Option String := none
  domainRef?  : Option Syntax := none
  compute?    : Option ComputeTier := none
  timeoutSec? : Option Nat := none
  timeoutRef? : Option Syntax := none
  preview     : PreviewSpec := {}
  previewRef? : Option Syntax := none
  invs        : Array (Ident × Array Syntax) := #[]

@[noinline] private def parsePreviewBlock (depShort : String) (block : Syntax) : CommandElabM PreviewSpec := do
  let mut preview : PreviewSpec := {}
  let mut seen : Array Name := #[]
  let mut rawPreviewDomain? : Option (Syntax × String) := none
  for pc in (block.getArg 2).getArgs do
    let pk := pc.getKind
    if seen.contains pk then throwErrorAt pc s!"duplicate clause in `preview:` of `deploy {depShort}`"
    seen := seen.push pk
    if pk == ``deployPreviewOnPrClause then preview := { preview with enabled := (pc.getArg 1).getId.eraseMacroScopes == `true }
    else if pk == ``deployPreviewSubdomainClause || pk == ``deployPreviewDomainClause then
      if seen.contains ``deployPreviewSubdomainClause && seen.contains ``deployPreviewDomainClause then
        throwErrorAt pc s!"cannot specify both `subdomain` and `domain` in `preview:` of `deploy {depShort}`"
      let s := (⟨pc.getArg 1⟩ : TSyntax `str).getString
      if pk == ``deployPreviewSubdomainClause then preview := { preview with subdomain? := some s, host? := none }
      else rawPreviewDomain? := some (pc.getArg 1, s)
    else if pk == ``deployPreviewProtectionClause then
      let arg := pc.getArg 1
      preview := { preview with protection := if arg.getAtomVal == "public" || arg.getId.eraseMacroScopes == `anyone then .pub else .team_only }
    else if pk == ``deployPreviewTtlClause then preview := { preview with ttlSec := ← parseDurationUnit (pc.getArg 1) }
    else throwErrorAt pc "unexpected clause in `preview:`"
  if let some (dRef, rawDom) := rawPreviewDomain? then
    let hp? := HostPattern.parse? rawDom
    if preview.enabled && hp?.isNone then
      throwErrorAt dRef s!"`deploy {depShort}`: invalid preview `domain` `{rawDom}` (expected RFC 1123 host or `*.example.com`)"
    preview := { preview with host? := hp?, subdomain? := none }
  return preview

@[noinline, command_elab deployCmd]
def elabDeployCmd : CommandElab := fun stx => do
  let depIdent : Ident := ⟨stx.getArg 1⟩; let depName := depIdent.getId.eraseMacroScopes
  let (currNs, depShort) := (← getCurrNamespace, depName.toString); let fullDepName := currNs ++ depName
  let mut p : ParsedDeploy := {}

  for c in (stx.getArg 3).getArgs do
    let k := c.getKind
    if k != ``deployInvClause then
      if p.seenTop.contains k then throwErrorAt c s!"duplicate clause in `deploy {depShort}`"
      p := { p with seenTop := p.seenTop.push k }
    if k == ``deployAppClause then p := { p with appIdent? := some ⟨c.getArg 1⟩ }
    else if k == ``deployRegionsClause then
      let mut regs : Array GcpRegion := #[]
      for rId in (c.getArg 2).getSepArgs do
        let rs := rId.getId.eraseMacroScopes.toString
        let some r := GcpRegion.parse? rs | throwErrorAt rId s!"unknown GCP region `{rs}`{Qed.Diag.didYouMean rs GcpRegion.allNames} (supported: {", ".intercalate GcpRegion.allNames})"
        if regs.contains r then throwErrorAt rId s!"duplicate region `{rs}` in `deploy {depShort}`"
        regs := regs.push r
      p := { p with regions? := some regs.toList, regionsRef? := some c }
    else if k == ``deployDomainClause then
      p := { p with domain? := some (⟨c.getArg 1⟩ : TSyntax `str).getString, domainRef? := some (c.getArg 1) }
    else if k == ``deployComputeClause then
      let tId := c.getArg 1; let ts := tId.getId.eraseMacroScopes.toString
      let some tier := ComputeTier.parse? ts | throwErrorAt tId s!"unknown `compute` tier `{ts}`{Qed.Diag.didYouMean ts ComputeTier.allNames} (supported: {", ".intercalate ComputeTier.allNames})"
      p := { p with compute? := some tier }
    else if k == ``deployTimeoutClause then
      p := { p with timeoutSec? := some (← parseDurationUnit (c.getArg 1)), timeoutRef? := some (c.getArg 1) }
    else if k == ``deployPreviewBlockClause then
      p := { p with preview := ← parsePreviewBlock depShort c, previewRef? := some c }
    else if k == ``deployInvClause then
      let invId : Ident := ⟨c.getArg 1⟩; let leaf := invId.getId.eraseMacroScopes
      if leaf == `spec || leaf == `spec_valid then throwErrorAt invId s!"invariant name `{leaf}` is reserved in `deploy {depShort}`"
      if p.invs.any (·.1.getId.eraseMacroScopes == leaf) then throwErrorAt invId s!"duplicate invariant `{leaf}` in `deploy {depShort}`"
      p := { p with invs := p.invs.push (invId, (c.getArg 3).getSepArgs) }
    else throwErrorAt c s!"unexpected clause in `deploy {depShort}`"

  let some appIdent := p.appIdent? | throwErrorAt depIdent s!"`deploy {depShort}` must specify `app <FullstackOrServerOrComponent>`"
  let (env, openDecls) := (← getEnv, ← getOpenDecls)
  let fsInfo? := Qed.Diag.lookupNameMapExt? fullstackRegistry env currNs openDecls appIdent.getId (some `title)
  let srvInfo? : Option Qed.ServerInfo := match fsInfo? with
    | some fi => (serverRegistry.getState env).find? fi.serverName
    | none    => Qed.Diag.lookupNameMapExt? serverRegistry env currNs openDecls appIdent.getId (some `secrets)
  let resolvedAppName ← match fsInfo?, srvInfo? with
    | some fi, some _ => pure fi.fullstackName.toString | none, some si => pure si.serverName.toString
    | _, none =>
        let some resolved ← (try some <$> liftCoreM (realizeGlobalConstNoOverloadWithInfo (resolveAppTargetIdent env currNs appIdent)) catch _ => pure none)
          | throwErrorAt appIdent s!"unknown `app` `{appIdent.getId}` in `deploy {depShort}` (expected a `fullstack`, `server`, or `component` name)"
        pure resolved.toString
  let spec : DeploySpec := { name := depShort, appName := resolvedAppName, regions := p.regions?.getD [.us_central1], domain? := p.domain?, compute := p.compute?.getD .standard, timeoutSec? := p.timeoutSec?, preview := p.preview }
  if let .error (sec, err) := spec.validateSectioned then
    throwErrorAt (match sec with | .regions => p.regionsRef?.getD depIdent | .timeout => p.timeoutRef?.getD depIdent | .domain => p.domainRef?.getD depIdent | .preview => p.previewRef?.getD depIdent) err

  let failIf (ref : Syntax) (bad : Bool) (msg : String) : CommandElabM Unit := if bad then throwErrorAt ref s!"`deploy {depShort}`: {msg}" else pure ()
  if let some srvInfo := srvInfo? then
    failIf (p.regionsRef?.getD depIdent) (srvInfo.hasState && spec.regions.length > 1)
      s!"server `{srvInfo.shortName}` uses in-memory `state`, which can only run in a single region (`regions.length = 1`) to preserve `atomic:` and state invariants.\n\nHint: Deploy to a single region, or move mutable state into a `database` block to deploy multi-region."
    if !srvInfo.channels.isEmpty then if let some t := spec.timeoutSec? then
      failIf (p.timeoutRef?.getD depIdent) (t < 60) s!"server `{srvInfo.shortName}` declares WebSocket `channel`s, which require `timeout` >= `60s` on Cloud Run (got `{t}s`; omit `timeout` for the 3600s WebSocket default)."
    for (nm, osKey, def?) in srvInfo.envVars do
      if let some d := def? then failIf depIdent (isLocalhostUrl d) s!"server `{srvInfo.shortName}` `env {nm}` (`{osKey}`) has a loopback default (`{d}`), which must not ship to production."
    for db in (Qed.Server.databaseRegistry.getState env).toList.filterMap (fun (_, di) => if srvInfo.databases.contains di.configConst then some di else none) do
      failIf depIdent db.envSpecs.prod.isEphemeral s!"database `{db.shortName}` uses ephemeral SQLite in `prod`, which loses all data when Cloud Run recycles containers.\n\nHint: Use `managed postgres` (or BYO `postgres` / `turso` / `d1`) for production."
      failIf depIdent db.envSpecs.staging.isEphemeral s!"database `{db.shortName}` uses ephemeral SQLite in `staging`, which is forbidden on Cloud Run."
      for e in DeployEnv.all do for sr in (db.envSpecs.get e).secrets do
        failIf depIdent (!sr.allowedIn e) s!"database `{db.shortName}` binds pinned secret `{sr.envVar}` into `{e}`, violating environment secret isolation."
    if let some ai := srvInfo.authName?.bind (Qed.Server.authRegistry.getState env).find? then
      failIf (p.previewRef?.getD depIdent) (ai.spec.isManaged && spec.preview.enabled && spec.preview.protection == .pub)
        s!"`auth {ai.shortName}` uses `managed` auth (which enables the persona-switcher Preview IdP on previews), so `preview:` cannot set `protection public`.\n\nHint: Set `protection team_only` inside `preview:`."
      if let some issDef := ai.spec.issuerDefault? then
        failIf depIdent (isLocalhostUrl issDef) s!"`auth {ai.shortName}` has a loopback `issuer` default (`{issDef}`), which must not ship to production.\n\nHint: Switch to `managed [...]` or remove the `?? \"{issDef}\"` fallback for production deployments."

  let specId := mkIdentFrom depIdent (depName ++ `spec)
  elabCommand (← `(command| theorem $(mkIdentFrom depIdent (depName ++ `_qed_deploy_marker)) : True := True.intro))
  elabCommand (← `(command| @[noinline] def $specId : Qed.Cloud.DeploySpec := $(← deploySpecToTerm spec)))
  elabCommand (← `(command| theorem $(mkIdentFrom depIdent (depName ++ `spec_valid)) : ($specId).validate.isOk = true := by decide))
  for (invId, exprs) in p.invs do
    let combined ← liftMacroM <| Qed.mkConjBody (← exprs.mapM (lowerDeployInvExpr specId)) (ascribeProp := false)
    liftTermElabM <| discard <| Term.elabTermEnsuringType combined (some (mkSort Level.zero))
    let invLeaf := invId.getId.eraseMacroScopes; let thmId := mkIdentFrom invId (depName ++ invLeaf)
    let savedEnv ← getEnv; let savedMsgs ← modifyGet fun s => (s.messages, { s with messages := {} })
    let ok ← try elabCommand (← `(command| set_option Elab.async false in theorem $thmId : $combined := by first | decide | (simp [$specId:ident] <;> omega))); pure !(← get).messages.hasErrors catch _ => pure false
    if ok then modify fun s => { s with messages := savedMsgs ++ s.messages }
    else setEnv savedEnv; modify fun s => { s with messages := savedMsgs }; throwErrorAt invId s!"deploy invariant `{depShort}.{invLeaf}` failed to prove"
  modifyEnv fun e => deployRegistry.addEntry e { deployName := fullDepName, specConst := fullDepName ++ `spec, spec }

end Qed.Cloud
