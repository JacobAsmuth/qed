import Lean
import Qed.Lang
import Qed.Cloud.Env
import Qed.Cloud.Gcp
import Qed.Cloud.Syntax
import Qed.Server.Lower
import Qed.Server.Registry

namespace Qed.Cloud

open Lean Elab Command Qed.Lang Qed.Server

/-! ## Persistent `deploy` Registry (`deployRegistry`) -/

structure DeployInfo where
  deployName : Lean.Name
  specConst  : Lean.Name
  spec       : DeploySpec
deriving Inhabited, Repr

initialize deployRegistry :
    Lean.SimplePersistentEnvExtension DeployInfo (Lean.NameMap DeployInfo) ←
  Qed.Diag.mkNameMapExt (·.deployName)

/-! ## Dedicated Duration Unit Parser (`60s`, `5m`, `24h`, `7d`) -/

private def parseDurationUnit (stx : Syntax) : CommandElabM Nat := do
  let n := (⟨stx.getArg 0⟩ : TSyntax `num).getNat
  let unit := (stx.getArg 1).getId.eraseMacroScopes.toString.toLower
  match unit with
  | "s" | "sec" => return n
  | "m" | "min" => return n * 60
  | "h" | "hr"  => return n * 3600
  | "d" | "day" => return n * 86400
  | _ => throwErrorAt stx s!"invalid duration unit `{n}{unit}` (expected `s`, `m`, `h`, or `d`, e.g. `60s`, `5m`, `7d`)"

/-! ## Term Builders for `DeploySpec` -/

private def regionTerm (r : GcpRegion) : Term :=
  mkIdent (`Qed.Cloud.GcpRegion ++ Name.mkSimple (r.toString.replace "-" "_"))

private def computeTerm (t : ComputeTier) : Term :=
  mkIdent (`Qed.Cloud.ComputeTier ++ Name.mkSimple t.toString)

private def deploySpecToTerm (d : DeploySpec) : CommandElabM Term := do
  let regTms : Array Term := d.regions.toArray.map regionTerm
  let hostTm : Term ← match d.preview.host? with
    | none             => `(Option.none)
    | some (.exact h)  => `(Option.some (Qed.Cloud.HostPattern.exact $(quote h)))
    | some (.wildcard s) => `(Option.some (Qed.Cloud.HostPattern.wildcard $(quote s)))
  let protTm : Term := mkIdent <| match d.preview.protection with
    | .team_only => `Qed.Cloud.PreviewProtection.team_only
    | .pub       => `Qed.Cloud.PreviewProtection.pub
  `(({
    name        := $(quote d.name)
    appName     := $(quote d.appName)
    regions     := [$[$regTms:term],*]
    domain?     := $(quote d.domain?)
    compute     := $(computeTerm d.compute)
    timeoutSec? := $(quote d.timeoutSec?)
    preview     := {
      enabled    := $(quote d.preview.enabled)
      subdomain? := $(quote d.preview.subdomain?)
      host?      := $hostTm
      protection := $protTm
      ttlSec     := $(quote d.preview.ttlSec)
    }
  } : Qed.Cloud.DeploySpec))

/-! ## Lowering Inline `deploy` Invariant Expressions -/

private def deploySpecFields : Array (String × Name) := #[
  ("compute", `compute), ("timeout_sec", `timeoutSec?), ("regions", `regions), ("domain", `domain?)
]

private def lowerDeployInvExpr (specId : Ident) (stx : Syntax) : CommandElabM Term := do
  let fail (ref : Syntax) (msg : String) : ReaderT (Array String) CommandElabM Term :=
    throwErrorAt ref msg
  let mapPreviewField (ref : Syntax) (f : String) : ReaderT (Array String) CommandElabM Name :=
    match f with
    | "enabled"   | "on_pr"       => return `enabled
    | "subdomain" | "subdomain?"  => return `subdomain?
    | "host" | "host?" | "domain" => return `host?
    | "protection"                => return `protection
    | "ttl_sec"   | "ttlSec"      => return `ttlSec
    | "ttl" => throwErrorAt ref "use `preview.ttl_sec` (in seconds) inside deploy invariants"
    | _ =>
        let valid := ["enabled", "subdomain", "host", "protection", "ttl_sec"]
        throwErrorAt ref s!"unknown `preview` field `{f}` in deploy invariant{Qed.Diag.didYouMean f valid}"
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
                let fn ← mapPreviewField ref f.toString
                foldProjTerms ref (← `(($specId).preview.$(mkIdentFrom ref fn):ident)) more
          else if let some (_, fld) := deploySpecFields.find? (·.1 == rs) then
            foldProjTerms ref (← `(($specId).$(mkIdentFrom ref fld):ident)) rest
          else if rest.isEmpty then
            if rs == "true" then if mode == .propInv then `(True) else `(true)
            else if rs == "false" then if mode == .propInv then `(False) else `(false)
            else if rs == "none" then `(Option.none)
            else if rs == "team_only" then `(Qed.Cloud.PreviewProtection.team_only)
            else if rs == "anyone" || rs == "pub" then `(Qed.Cloud.PreviewProtection.pub)
            else if rs == "timeout" then throwErrorAt ref "use `timeout_sec` (Option Nat, in seconds) inside deploy invariants"
            else if let some tier := ComputeTier.parse? rs then pure (computeTerm tier)
            else if let some reg := GcpRegion.parse? rs then pure (regionTerm reg)
            else pure (mkIdentFrom ref root)
          else foldProjTerms ref (mkIdentFrom ref root) rest
  }
  (lowerQedExpr hooks .propInv stx).run #[]

/-! ## `deploy` Command Elaborator -/

@[command_elab deployCmd]
def elabDeployCmd : CommandElab := fun stx => do
  let depIdent : Ident := ⟨stx.getArg 1⟩
  let depName := depIdent.getId.eraseMacroScopes
  let depShort := depName.toString
  let currNs ← getCurrNamespace
  let fullDepName := currNs ++ depName

  let mut seenTop     : Array Name := #[]
  let mut appIdent?   : Option Ident := none
  let mut regions?    : Option (List GcpRegion) := none
  let mut regionsRef? : Option Syntax := none
  let mut domain?     : Option String := none
  let mut domainRef?  : Option Syntax := none
  let mut compute?    : Option ComputeTier := none
  let mut timeoutSec? : Option Nat := none
  let mut timeoutRef? : Option Syntax := none
  let mut preview     : PreviewSpec := {}
  let mut previewRef? : Option Syntax := none
  let mut invs        : Array (Ident × Array Syntax) := #[]

  for c in (stx.getArg 3).getArgs do
    let k := c.getKind
    if k != ``deployInvClause then
      if seenTop.contains k then
        throwErrorAt c s!"duplicate clause in `deploy {depShort}`"
      seenTop := seenTop.push k
    if k == ``deployAppClause then
      appIdent? := some ⟨c.getArg 1⟩
    else if k == ``deployRegionsClause then
      regionsRef? := some c
      let mut regs : Array GcpRegion := #[]
      for rId in (c.getArg 2).getSepArgs do
        let rs := rId.getId.eraseMacroScopes.toString
        let some r := GcpRegion.parse? rs
          | throwErrorAt rId s!"unknown GCP region `{rs}`{Qed.Diag.didYouMean rs GcpRegion.allNames} (supported: {String.intercalate ", " GcpRegion.allNames})"
        if regs.contains r then throwErrorAt rId s!"duplicate region `{rs}` in `deploy {depShort}`"
        regs := regs.push r
      regions? := some regs.toList
    else if k == ``deployDomainClause then
      domain? := some (⟨c.getArg 1⟩ : TSyntax `str).getString
      domainRef? := some (c.getArg 1)
    else if k == ``deployComputeClause then
      let tId := c.getArg 1
      let ts := tId.getId.eraseMacroScopes.toString
      let some tier := ComputeTier.parse? ts
        | throwErrorAt tId s!"unknown `compute` tier `{ts}`{Qed.Diag.didYouMean ts ComputeTier.allNames} (supported: {String.intercalate ", " ComputeTier.allNames})"
      compute? := some tier
    else if k == ``deployTimeoutClause then
      timeoutSec? := some (← parseDurationUnit (c.getArg 1))
      timeoutRef? := some (c.getArg 1)
    else if k == ``deployPreviewBlockClause then
      previewRef? := some c
      let mut seen : Array Name := #[]
      let mut rawPreviewDomain? : Option (Syntax × String) := none
      for pc in (c.getArg 2).getArgs do
        let pk := pc.getKind
        if seen.contains pk then
          throwErrorAt pc s!"duplicate clause in `preview:` of `deploy {depShort}`"
        seen := seen.push pk
        if pk == ``deployPreviewOnPrClause then
          preview := { preview with enabled := (pc.getArg 1).getId.eraseMacroScopes == `true }
        else if pk == ``deployPreviewSubdomainClause || pk == ``deployPreviewDomainClause then
          if seen.contains ``deployPreviewSubdomainClause && seen.contains ``deployPreviewDomainClause then
            throwErrorAt pc s!"cannot specify both `subdomain` and `domain` in `preview:` of `deploy {depShort}`"
          let s := (⟨pc.getArg 1⟩ : TSyntax `str).getString
          if pk == ``deployPreviewSubdomainClause then
            preview := { preview with subdomain? := some s, host? := none }
          else
            rawPreviewDomain? := some (pc.getArg 1, s)
        else if pk == ``deployPreviewProtectionClause then
          let arg := pc.getArg 1
          let isPub := arg.getAtomVal == "public" || arg.getId.eraseMacroScopes == `anyone
          preview := { preview with protection := if isPub then .pub else .team_only }
        else if pk == ``deployPreviewTtlClause then
          preview := { preview with ttlSec := ← parseDurationUnit (pc.getArg 1) }
        else
          throwErrorAt pc s!"unexpected clause in `preview:`"
      if let some (dRef, rawDom) := rawPreviewDomain? then
        let hp? := HostPattern.parse? rawDom
        if preview.enabled && hp?.isNone then
          throwErrorAt dRef s!"`deploy {depShort}`: invalid preview `domain` `{rawDom}` (expected RFC 1123 host or `*.example.com`)"
        preview := { preview with host? := hp?, subdomain? := none }
    else if k == ``deployInvClause then
      let invId : Ident := ⟨c.getArg 1⟩
      let leaf := invId.getId.eraseMacroScopes
      if leaf == `spec || leaf == `spec_valid then
        throwErrorAt invId s!"invariant name `{leaf}` is reserved in `deploy {depShort}`"
      if invs.any (fun (id, _) => id.getId.eraseMacroScopes == leaf) then
        throwErrorAt invId s!"duplicate invariant `{leaf}` in `deploy {depShort}`"
      invs := invs.push (invId, (c.getArg 3).getSepArgs)
    else
      throwErrorAt c s!"unexpected clause in `deploy {depShort}`"

  let some appIdent := appIdent?
    | throwErrorAt depIdent s!"`deploy {depShort}` must specify `app <FullstackOrServerOrComponent>`"

  let env ← getEnv
  let openDecls ← getOpenDecls

  -- Resolve target `fullstack`, `server`, or standalone `component`
  let fsInfo? := Qed.Diag.lookupNameMapExt? fullstackRegistry env currNs openDecls appIdent.getId (some `title)
  let srvInfo? : Option Qed.ServerInfo := match fsInfo? with
    | some fi => (serverRegistry.getState env).find? fi.serverName
    | none    => Qed.Diag.lookupNameMapExt? serverRegistry env currNs openDecls appIdent.getId (some `secrets)

  let resolvedAppName ←
    match fsInfo?, srvInfo? with
    | some fi, some _ => pure fi.fullstackName.toString
    | none, some si   => pure si.serverName.toString
    | _, none =>
        let compTarget := resolveAppTargetIdent env currNs appIdent
        match ← (try some <$> liftCoreM (realizeGlobalConstNoOverloadWithInfo compTarget) catch _ => pure none) with
        | some resolved => pure resolved.toString
        | none =>
            throwErrorAt appIdent s!"unknown `app` `{appIdent.getId}` in `deploy {depShort}` (expected a `fullstack`, `server`, or `component` name)"

  let spec : DeploySpec := {
    name        := depShort
    appName     := resolvedAppName
    regions     := regions?.getD [.us_central1]
    domain?
    compute     := compute?.getD .standard
    timeoutSec?
    preview
  }

  -- 1. Section-targeted DeploySpec validation (RFC 1123 hostnames, prod/preview disjointness, timeout range)
  if let .error (sec, err) := spec.validateSectioned then
    let ref := match sec with
      | .regions => regionsRef?.getD depIdent
      | .timeout => timeoutRef?.getD depIdent
      | .domain  => domainRef?.getD depIdent
      | .preview => previewRef?.getD depIdent
    throwErrorAt ref err

  -- 2. Automatic Qed-specific cross-checks when a `server` is mounted
  if let some srvInfo := srvInfo? then
    -- Stateful servers automatically pin `maxInstances = 1` in `compileInfra`; only multi-region is disallowed.
    if srvInfo.hasState && spec.regions.length > 1 then
      throwErrorAt (regionsRef?.getD depIdent)
        s!"`deploy {depShort}`: server `{srvInfo.shortName}` uses in-memory `state`, which can only run in a single region (`regions.length = 1`) to preserve `atomic:` and state invariants.\n\nHint: Deploy to a single region, or move mutable state into a `database` block to deploy multi-region."

    if !srvInfo.channels.isEmpty then
      if let some t := spec.timeoutSec? then
        if t < 60 then
          throwErrorAt (timeoutRef?.getD depIdent)
            s!"`deploy {depShort}`: server `{srvInfo.shortName}` declares WebSocket `channel`s, which require `timeout` >= `60s` on Cloud Run (got `{t}s`; omit `timeout` for the 3600s WebSocket default)."

    for (nm, osKey, def?) in srvInfo.envVars do
      if let some d := def? then
        if isLocalhostUrl d then
          throwErrorAt depIdent
            s!"`deploy {depShort}`: server `{srvInfo.shortName}` `env {nm}` (`{osKey}`) has a loopback default (`{d}`), which must not ship to production."

    let dbReg := Qed.Server.databaseRegistry.getState env
    let attachedDbs : List Qed.Server.DatabaseInfo :=
      dbReg.toList.filterMap fun (_, di) =>
        if srvInfo.databases.contains di.configConst then some di else none
    for db in attachedDbs do
      if db.envSpecs.prod.isEphemeral then
        throwErrorAt depIdent
          s!"`deploy {depShort}`: database `{db.shortName}` uses ephemeral SQLite in `prod`, which loses all data when Cloud Run recycles containers.\n\nHint: Use `managed postgres` (or BYO `postgres` / `turso` / `d1`) for production."
      if db.envSpecs.staging.isEphemeral then
        throwErrorAt depIdent
          s!"`deploy {depShort}`: database `{db.shortName}` uses ephemeral SQLite in `staging`, which is forbidden on Cloud Run."
      for e in DeployEnv.all do
        for sr in (db.envSpecs.get e).secrets do
          if !sr.allowedIn e then
            throwErrorAt depIdent
              s!"`deploy {depShort}`: database `{db.shortName}` binds pinned secret `{sr.envVar}` into `{e}`, violating environment secret isolation."

    let authReg := Qed.Server.authRegistry.getState env
    if let some an := srvInfo.authName? then
      if let some ai := authReg.find? an then
        if ai.spec.isManaged && spec.preview.enabled && spec.preview.protection == .pub then
          throwErrorAt (previewRef?.getD depIdent)
            s!"`deploy {depShort}`: `auth {ai.shortName}` uses `managed` auth (which enables the persona-switcher Preview IdP on previews), so `preview:` cannot set `protection public`.\n\nHint: Set `protection team_only` inside `preview:`."
        if let some issDef := ai.spec.issuerDefault? then
          if isLocalhostUrl issDef then
            throwErrorAt depIdent
              s!"`deploy {depShort}`: `auth {ai.shortName}` has a loopback `issuer` default (`{issDef}`), which must not ship to production.\n\nHint: Switch to `managed [...]` or remove the `?? \"{issDef}\"` fallback for production deployments."

  -- 3. Generate leak-gate marker, `<Deploy>.spec`, kernel-checked `<Deploy>.spec_valid`, and user `invariant`s
  let markerId := mkIdentFrom depIdent (depName ++ `_qed_deploy_marker)
  let specId := mkIdentFrom depIdent (depName ++ `spec)
  let validId := mkIdentFrom depIdent (depName ++ `spec_valid)
  let specTm ← deploySpecToTerm spec
  elabCommand (← `(command| theorem $markerId : True := True.intro))
  elabCommand (← `(command| def $specId : Qed.Cloud.DeploySpec := $specTm))
  elabCommand (← `(command| theorem $validId : ($specId).validate.isOk = true := by decide))

  for (invId, exprs) in invs do
    let propTms ← exprs.mapM (lowerDeployInvExpr specId)
    let combined ← liftMacroM <| Qed.mkConjBody propTms (ascribeProp := false)
    liftTermElabM <| discard <| Term.elabTermEnsuringType combined (some (mkSort Level.zero))
    let invLeaf := invId.getId.eraseMacroScopes
    let thmId := mkIdentFrom invId (depName ++ invLeaf)
    let savedEnv ← getEnv
    let savedMsgs ← modifyGet fun s => (s.messages, { s with messages := {} })
    let ok ← do
      try
        elabCommand (← `(command|
          set_option Elab.async false in
          theorem $thmId : $combined := by first | decide | (simp [$specId:ident] <;> omega)))
        pure !(← get).messages.hasErrors
      catch _ => pure false
    if ok then
      modify fun s => { s with messages := savedMsgs ++ s.messages }
    else
      setEnv savedEnv
      modify fun s => { s with messages := savedMsgs }
      throwErrorAt invId s!"deploy invariant `{depShort}.{invLeaf}` failed to prove"

  modifyEnv fun e => deployRegistry.addEntry e {
    deployName := fullDepName
    specConst  := fullDepName ++ `spec
    spec
  }

end Qed.Cloud
