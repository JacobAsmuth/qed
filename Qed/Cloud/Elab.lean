import Qed.Cloud.Gcp
import Qed.Server.Registry
import Qed.Verify.Core

namespace Qed.Cloud

/-! ## `deploy` Block Surface Syntax & Elaborator (`Qed.Cloud.Elab`) -/

declare_syntax_cat deployClause
declare_syntax_cat deployPreviewClause

section DeployParsers
open Lean Parser Qed.Lang
private def clauseP (k kw : Name) (p : Parser) : Parser := node k (withPosition (atomic (identEq kw) >> p))
def deployUnitLit : Parser := node `Qed.Cloud.unitLit (numLit >> checkNoWsBefore "expected unit suffix without space" >> ident)
def deployPreviewOnPrClause : Parser := clauseP `Qed.Cloud.deployPreviewOnPrClause `on_pr (identEq `true <|> identEq `false)
def deployPreviewSubdomainClause : Parser := clauseP `Qed.Cloud.deployPreviewSubdomainClause `subdomain strLit
def deployPreviewDomainClause : Parser := clauseP `Qed.Cloud.deployPreviewDomainClause `domain strLit
def deployPreviewProtectionClause : Parser := clauseP `Qed.Cloud.deployPreviewProtectionClause `protection (identEq `team_only <|> symbol "public")
def deployPreviewTtlClause : Parser := clauseP `Qed.Cloud.deployPreviewTtlClause `ttl deployUnitLit
@[deployPreviewClause_parser] def deployPreviewClauseP : Parser := opaqueP (
  deployPreviewOnPrClause <|> deployPreviewSubdomainClause <|> deployPreviewDomainClause <|> deployPreviewProtectionClause <|> deployPreviewTtlClause)
def deployAppClause : Parser := clauseP `Qed.Cloud.deployAppClause `app ident
def deployRegionsClause : Parser := clauseP `Qed.Cloud.deployRegionsClause `regions ("[" >> commaSep1 ident >> "]")
def deployDomainClause : Parser := clauseP `Qed.Cloud.deployDomainClause `domain strLit
def deployComputeClause : Parser := clauseP `Qed.Cloud.deployComputeClause `compute ident
def deployTimeoutClause : Parser := clauseP `Qed.Cloud.deployTimeoutClause `timeout deployUnitLit
def deployPreviewBlockClause : Parser := clauseP `Qed.Cloud.deployPreviewBlockClause `preview (":" >> checkColGt "expected indented `preview:` clauses" >> many1Indent (categoryParser `deployPreviewClause 0))
def deployInvClause : Parser := node `Qed.Cloud.deployInvClause (withPosition (atomic (identEq `invariant >> ident >> ":") >> sepBy1 (categoryParser `qedExpr 0) "," >> qedOptProof))
@[deployClause_parser] def deployClauseP : Parser := opaqueP (
  deployAppClause <|> deployRegionsClause <|> deployDomainClause <|> deployComputeClause <|> deployTimeoutClause <|> deployPreviewBlockClause <|> deployInvClause)
@[command_parser] def deployCmd : Parser := opaqueP (node `Qed.Cloud.deployCmd
  (optional Command.docComment >> withPosition (atomic (identEq `deploy >> ident >> ":") >> checkColGt "expected indented `deploy` clauses" >> many1Indent (categoryParser `deployClause 0))))
end DeployParsers

open Lean Elab Command Qed.Lang Qed.Server

structure DeployInfo where
  (deployName specConst : Lean.Name) (spec : DeploySpec)
deriving Inhabited

initialize deployRegistry : Lean.SimplePersistentEnvExtension DeployInfo (Lean.NameMap DeployInfo) ←
  Qed.Diag.mkNameMapExt (·.deployName)

@[noinline] private def parseDurationUnit (stx : Syntax) : CommandElabM Nat := do
  let (n, unit) := ((⟨stx.getArg 0⟩ : TSyntax `num).getNat, (stx.getArg 1).getId.eraseMacroScopes.toString.toLower)
  match unit with
  | "s" | "sec" => return n | "m" | "min" => return n * 60 | "h" | "hr" => return n * 3600 | "d" | "day" => return n * 86400
  | _ => throwErrorAt stx s!"invalid duration unit `{n}{unit}` (expected `s`, `m`, `h`, or `d`, e.g. `60s`, `5m`, `7d`)"

private def regionTerm (r : GcpRegion) : Term := mkIdent (`Qed.Cloud.GcpRegion ++ Name.mkSimple (r.toString.replace "-" "_"))
private def computeTerm (t : ComputeTier) : Term := mkIdent (`Qed.Cloud.ComputeTier ++ Name.mkSimple t.toString)

private def optTerm {α : Type} (f : α → Term) : Option α → PureQuotM Term
  | none => `(Option.none) | some v => `(Option.some $(f v))

@[noinline] private def mkDeployHeaderCmdsPure (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (depIdent : Ident) (depName : Name) (d : DeploySpec) : PureQuotM (Array Command) := do
  let (specId, regTms) := (mkIdentFrom depIdent (depName ++ `spec), d.regions.toArray.map regionTerm)
  let hostTm ← match d.preview.host? with
    | none => `(Option.none) | some (.exact h) => `(Option.some (Qed.Cloud.HostPattern.exact $(Syntax.mkStrLit h)))
    | some (.wildcard s) => `(Option.some (Qed.Cloud.HostPattern.wildcard $(Syntax.mkStrLit s)))
  let protTm := mkIdent (match d.preview.protection with | .team_only => `Qed.Cloud.PreviewProtection.team_only | .pub => `Qed.Cloud.PreviewProtection.pub)
  let domTm ← optTerm (fun s => (Syntax.mkStrLit s : Term)) d.domain?; let toTm ← optTerm (fun n => (Syntax.mkNumLit (toString n) : Term)) d.timeoutSec?
  let subTm ← optTerm (fun s => (Syntax.mkStrLit s : Term)) d.preview.subdomain?; let enTm := mkIdent (if d.preview.enabled then ``true else ``false)
  let specTm ← `(({
      name := $(Syntax.mkStrLit d.name), appName := $(Syntax.mkStrLit d.appName), regions := [$[$regTms:term],*], domain? := $domTm,
      compute := $(computeTerm d.compute), timeoutSec? := $toTm,
      preview := { enabled := $enTm, subdomain? := $subTm, host? := $hostTm, protection := $protTm, ttlSec := $(Syntax.mkNumLit (toString d.preview.ttlSec)) }
    } : Qed.Cloud.DeploySpec))
  return #[← Lang.mkMarkerThmPure (mkIdentFrom depIdent (depName ++ `_qed_deploy_marker)),
    ← `(command| $[$doc?:docComment]? @[noinline] def $specId : Qed.Cloud.DeploySpec := $specTm),
    ← `(command| theorem $(mkIdentFrom depIdent (depName ++ `spec_valid)) : ($specId).validate.isOk = true := by decide)]

private def parseNamedEnum {α : Type} (ref : Syntax) (label : String) (parse? : String → Option α) (allNames : List String) : CommandElabM α := do
  let s := ref.getId.eraseMacroScopes.toString
  let some v := parse? s | throwErrorAt ref s!"unknown {label} `{s}`{Qed.Diag.didYouMean s allNames} (supported: {", ".intercalate allNames})"
  return v

private structure ParsedDeploy where
  (seenTop : Array Name := #[]) (appIdent? : Option Ident := none) (regions? : Option (List GcpRegion) := none)
  (regionsRef? domainRef? timeoutRef? previewRef? : Option Syntax := none) (domain? : Option String := none)
  (compute? : Option ComputeTier := none) (timeoutSec? : Option Nat := none) (preview : PreviewSpec := {})
  (invs : Array (Ident × Array Syntax × Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) := #[])

@[noinline] private def parsePreviewBlock (depShort : String) (block : Syntax) : CommandElabM PreviewSpec := do
  let (preview, _, rawPreviewDomain?) ← Lang.foldlCmd (block.getArg 2).getArgs (({} : PreviewSpec), (#[] : Array Name), (none : Option (Syntax × String))) fun (preview, seen, rawDom?) pc => do
    let pk := pc.getKind
    if seen.contains pk then throwErrorAt pc s!"duplicate clause in `preview:` of `deploy {depShort}`"
    let seen := seen.push pk
    match pk with
    | ``deployPreviewOnPrClause => return ({ preview with enabled := (pc.getArg 1).getId.eraseMacroScopes == `true }, seen, rawDom?)
    | ``deployPreviewSubdomainClause | ``deployPreviewDomainClause =>
      if seen.contains ``deployPreviewSubdomainClause && seen.contains ``deployPreviewDomainClause then
        throwErrorAt pc s!"cannot specify both `subdomain` and `domain` in `preview:` of `deploy {depShort}`"
      let s := (⟨pc.getArg 1⟩ : TSyntax `str).getString
      if pk == ``deployPreviewSubdomainClause then return ({ preview with subdomain? := some s, host? := none }, seen, rawDom?)
      else return (preview, seen, some (pc.getArg 1, s))
    | ``deployPreviewProtectionClause =>
      return ({ preview with protection := if (pc.getArg 1).getAtomVal == "public" then .pub else .team_only }, seen, rawDom?)
    | ``deployPreviewTtlClause => return ({ preview with ttlSec := ← parseDurationUnit (pc.getArg 1) }, seen, rawDom?)
    | _ => throwErrorAt pc "unexpected clause in `preview:`"
  if let some (dRef, rawDom) := rawPreviewDomain? then
    let hp? := HostPattern.parse? rawDom
    if preview.enabled && hp?.isNone then throwErrorAt dRef s!"`deploy {depShort}`: invalid preview `domain` `{rawDom}` (expected RFC 1123 host or `*.example.com`)"
    return { preview with host? := hp?, subdomain? := none }
  return preview

@[noinline, command_elab deployCmd]
def elabDeployCmd : CommandElab := fun stx => do
  let doc? := extractOptDoc (stx.getArg 0)
  let depIdent : Ident := ⟨stx.getArg 2⟩; let depName := depIdent.getId.eraseMacroScopes
  let (currNs, depShort) := (← getCurrNamespace, depName.toString); let fullDepName := currNs ++ depName
  let p ← Lang.foldlCmd (stx.getArg 4).getArgs ({} : ParsedDeploy) fun p c => do
    let k := c.getKind
    let p ← if k != ``deployInvClause then
        if p.seenTop.contains k then throwErrorAt c s!"duplicate clause in `deploy {depShort}`"
        pure { p with seenTop := p.seenTop.push k }
      else pure p
    match k with
    | ``deployAppClause => return { p with appIdent? := some ⟨c.getArg 1⟩ }
    | ``deployRegionsClause =>
      let regs ← Lang.foldlCmd (c.getArg 2).getSepArgs (#[] : Array GcpRegion) fun regs rId => do
        let r ← parseNamedEnum rId "GCP region" GcpRegion.parse? GcpRegion.allNames
        if regs.contains r then throwErrorAt rId s!"duplicate region `{rId.getId.eraseMacroScopes}` in `deploy {depShort}`"
        return regs.push r
      return { p with regions? := some regs.toList, regionsRef? := some c }
    | ``deployDomainClause => return { p with domain? := some (⟨c.getArg 1⟩ : TSyntax `str).getString, domainRef? := some (c.getArg 1) }
    | ``deployComputeClause => return { p with compute? := some (← parseNamedEnum (c.getArg 1) "`compute` tier" ComputeTier.parse? ComputeTier.allNames) }
    | ``deployTimeoutClause => return { p with timeoutSec? := some (← parseDurationUnit (c.getArg 1)), timeoutRef? := some (c.getArg 1) }
    | ``deployPreviewBlockClause => return { p with preview := ← parsePreviewBlock depShort c, previewRef? := some c }
    | ``deployInvClause =>
      let invId : Ident := ⟨c.getArg 1⟩; let leaf := invId.getId.eraseMacroScopes
      if leaf == `spec || leaf == `spec_valid then throwErrorAt invId s!"invariant name `{leaf}` is reserved in `deploy {depShort}`"
      if p.invs.any (·.1.getId.eraseMacroScopes == leaf) then throwErrorAt invId s!"duplicate invariant `{leaf}` in `deploy {depShort}`"
      return { p with invs := p.invs.push (invId, (c.getArg 3).getSepArgs, Qed.Lang.parseOptTacSeq (c.getArg 4)) }
    | _ => throwErrorAt c s!"unexpected clause in `deploy {depShort}`"
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
    Lang.foldlCmd srvInfo.envVars () fun () (nm, osKey, def?) =>
      if let some d := def? then failIf depIdent (isLocalhostUrl d) s!"server `{srvInfo.shortName}` `env {nm}` (`{osKey}`) has a loopback default (`{d}`), which must not ship to production." else pure ()
    let dbs := ((Qed.Server.databaseRegistry.getState env).toList.filterMap fun (_, di) => if srvInfo.databases.contains di.configConst then some di else none).toArray
    Lang.foldlCmd dbs () fun () db => do
      failIf depIdent db.envSpecs.prod.isEphemeral s!"database `{db.shortName}` uses ephemeral SQLite in `prod`, which loses all data when Cloud Run recycles containers.\n\nHint: Use `managed postgres` (or BYO `postgres` / `turso` / `d1`) for production."
      failIf depIdent db.envSpecs.staging.isEphemeral s!"database `{db.shortName}` uses ephemeral SQLite in `staging`, which is forbidden on Cloud Run."
      Lang.foldlCmd DeployEnv.all.toArray () fun () e =>
        Lang.foldlCmd (db.envSpecs.get e).secrets.toArray () fun () sr =>
          failIf depIdent (!sr.allowedIn e) s!"database `{db.shortName}` binds pinned secret `{sr.envVar}` into `{e}`, violating environment secret isolation."
    if let some ai := srvInfo.authName?.bind (Qed.Server.authRegistry.getState env).find? then
      failIf (p.previewRef?.getD depIdent) (ai.spec.isManaged && spec.preview.enabled && spec.preview.protection == .pub)
        s!"`auth {ai.shortName}` uses `managed` auth (which enables the persona-switcher Preview IdP on previews), so `preview:` cannot set `protection public`.\n\nHint: Set `protection team_only` inside `preview:`."
      if let some issDef := ai.spec.issuerDefault? then
        failIf depIdent (isLocalhostUrl issDef) s!"`auth {ai.shortName}` has a loopback `issuer` default (`{issDef}`), which must not ship to production.\n\nHint: Switch to `managed [...]` or remove the `?? \"{issDef}\"` fallback for production deployments."
  Lang.elabPureCmds (mkDeployHeaderCmdsPure doc? depIdent depName spec)
  if !p.invs.isEmpty then
    let specCId : Term := mkCIdent (fullDepName ++ `spec)
    let (compT, toT, regT, domT, prevT) ← Lang.runPQ do
      return (← `(($specCId).compute), ← `(($specCId).timeoutSec?), ← `(($specCId).regions), ← `(($specCId).domain?), ← `(($specCId).preview))
    let aliases : Array (String × Term) :=
      #[("spec", specCId), ("compute", compT), ("timeout_sec", toT), ("regions", regT), ("domain", domT), ("preview", prevT),
        ("team_only", mkCIdent `Qed.Cloud.PreviewProtection.team_only)] ++
      ComputeTier.all.toArray.map (fun t => (t.toString, computeTerm t)) ++
      GcpRegion.all.toArray.map (fun r => (r.toString.replace "-" "_", regionTerm r))
    let unfolds := #[fullDepName ++ `spec]
    Lang.foldlCmd p.invs () fun () (invId, exprs, tac?) => do
      let pf? ← match tac? with | some ts => some <$> Lang.runPQ `(by $ts) | none => pure none
      Qed.Verify.Core.elabStaticMetaInv depShort (fullDepName ++ invId.getId.eraseMacroScopes) aliases unfolds invId exprs pf?
  modifyEnv fun e => deployRegistry.addEntry e { deployName := fullDepName, specConst := fullDepName ++ `spec, spec }

end Qed.Cloud
