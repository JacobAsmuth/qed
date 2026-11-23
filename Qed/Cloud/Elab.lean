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

private def regionToTerm : GcpRegion → CommandElabM Term
  | .us_central1     => `(Qed.Cloud.GcpRegion.us_central1)
  | .us_east1        => `(Qed.Cloud.GcpRegion.us_east1)
  | .us_east4        => `(Qed.Cloud.GcpRegion.us_east4)
  | .us_west1        => `(Qed.Cloud.GcpRegion.us_west1)
  | .europe_west1    => `(Qed.Cloud.GcpRegion.europe_west1)
  | .europe_west4    => `(Qed.Cloud.GcpRegion.europe_west4)
  | .asia_east1      => `(Qed.Cloud.GcpRegion.asia_east1)
  | .asia_northeast1 => `(Qed.Cloud.GcpRegion.asia_northeast1)

private def computeToTerm : ComputeTier → CommandElabM Term
  | .standard    => `(Qed.Cloud.ComputeTier.standard)
  | .performance => `(Qed.Cloud.ComputeTier.performance)
  | .large       => `(Qed.Cloud.ComputeTier.large)
  | .xlarge      => `(Qed.Cloud.ComputeTier.xlarge)

private def deploySpecToTerm (d : DeploySpec) : CommandElabM Term := do
  let regTms ← d.regions.toArray.mapM regionToTerm
  let optTerm {α : Type} (f : α → CommandElabM Term) : Option α → CommandElabM Term
    | none   => `(Option.none)
    | some v => do `(Option.some $(← f v))
  let hpToTm : HostPattern → CommandElabM Term
    | .exact h    => `(Qed.Cloud.HostPattern.exact $(Syntax.mkStrLit h))
    | .wildcard s => `(Qed.Cloud.HostPattern.wildcard $(Syntax.mkStrLit s))
  let protTm : Term ← match d.preview.protection with
    | .team_only => `(Qed.Cloud.PreviewProtection.team_only)
    | .pub       => `(Qed.Cloud.PreviewProtection.pub)
  let mkN (n : Nat) : Term := Syntax.mkNumLit (toString n)
  let optStr : Option String → CommandElabM Term := optTerm fun s => pure (Syntax.mkStrLit s : Term)
  let optNat : Option Nat → CommandElabM Term := optTerm fun n => pure (mkN n)
  `(({
    name        := $(Syntax.mkStrLit d.name)
    appName     := $(Syntax.mkStrLit d.appName)
    regions     := [$[$regTms:term],*]
    domain?     := $(← optStr d.domain?)
    compute     := $(← computeToTerm d.compute)
    timeoutSec? := $(← optNat d.timeoutSec?)
    preview     := {
      enabled    := $(quote d.preview.enabled)
      subdomain? := $(← optStr d.preview.subdomain?)
      host?      := $(← optTerm hpToTm d.preview.host?)
      protection := $protTm
      ttlSec     := $(mkN d.preview.ttlSec)
    }
  } : Qed.Cloud.DeploySpec))

/-! ## Lowering Inline `deploy` Invariant Expressions -/

private def lowerDeployInvExpr (specId : Ident) (stx : Syntax) : CommandElabM Term := do
  let fail (ref : Syntax) (msg : String) : ReaderT (Array String) CommandElabM Term :=
    throwErrorAt ref msg
  let foldProjs (ref : Syntax) (base : Term) (fs : List Name) : ReaderT (Array String) CommandElabM Term :=
    fs.foldlM (init := base) fun acc f => `(($acc).$(mkIdentFrom ref f):ident)
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
      let comps := id.getId.eraseMacroScopes.components
      match comps with
      | [] => throwErrorAt ref "empty identifier in deploy invariant"
      | [single] =>
          let s := single.toString
          if locals.contains s then return mkIdentFrom ref single
          else if s == "true" then if mode == .propInv then `(True) else `(true)
          else if s == "false" then if mode == .propInv then `(False) else `(false)
          else if s == "none" then `(Option.none)
          else if s == "team_only" then `(Qed.Cloud.PreviewProtection.team_only)
          else if s == "anyone" || s == "pub" then `(Qed.Cloud.PreviewProtection.pub)
          else if s == "compute" then `(($specId).compute)
          else if s == "timeout_sec" then `(($specId).timeoutSec?)
          else if s == "timeout" then throwErrorAt ref "use `timeout_sec` (Option Nat, in seconds) inside deploy invariants"
          else if s == "preview" then `(($specId).preview)
          else if s == "regions" then `(($specId).regions)
          else if s == "domain" then `(($specId).domain?)
          else if let some tier := ComputeTier.parse? s then liftM (computeToTerm tier)
          else if let some reg := GcpRegion.parse? s then liftM (regionToTerm reg)
          else return mkIdentFrom ref single
      | root :: rest =>
          let rs := root.toString
          if locals.contains rs then foldProjs ref (mkIdentFrom ref root) rest
          else if rs == "preview" then
            match rest with
            | f :: more =>
                let fn ← mapPreviewField ref f.toString
                foldProjs ref (← `(($specId).preview.$(mkIdentFrom ref fn):ident)) more
            | [] => `(($specId).preview)
          else if rs == "compute"     then foldProjs ref (← `(($specId).compute)) rest
          else if rs == "timeout_sec" then foldProjs ref (← `(($specId).timeoutSec?)) rest
          else if rs == "regions"     then foldProjs ref (← `(($specId).regions)) rest
          else if rs == "domain"      then foldProjs ref (← `(($specId).domain?)) rest
          else foldProjs ref (mkIdentFrom ref root) rest
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
  let clauses := (stx.getArg 3).getArgs

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

  for c in clauses do
    let k := c.getKind
    if k == ``deployAppClause then
      if appIdent?.isSome then throwErrorAt c s!"duplicate `app` clause in `deploy {depShort}`"
      appIdent? := some ⟨c.getArg 1⟩
    else if k == ``deployRegionsClause then
      if regions?.isSome then throwErrorAt c s!"duplicate `regions` clause in `deploy {depShort}`"
      regionsRef? := some c
      let mut regs : Array GcpRegion := #[]
      for rId in (c.getArg 2).getSepArgs do
        let rs := rId.getId.eraseMacroScopes.toString
        match GcpRegion.parse? rs with
        | some r =>
            if regs.contains r then throwErrorAt rId s!"duplicate region `{rs}` in `deploy {depShort}`"
            regs := regs.push r
        | none =>
            throwErrorAt rId s!"unknown GCP region `{rs}`{Qed.Diag.didYouMean rs GcpRegion.allNames} (supported: {String.intercalate ", " GcpRegion.allNames})"
      regions? := some regs.toList
    else if k == ``deployDomainClause then
      if domain?.isSome then throwErrorAt c s!"duplicate `domain` clause in `deploy {depShort}`"
      domain? := some (⟨c.getArg 1⟩ : TSyntax `str).getString
      domainRef? := some (c.getArg 1)
    else if k == ``deployComputeClause then
      if compute?.isSome then throwErrorAt c s!"duplicate `compute` clause in `deploy {depShort}`"
      let tId := c.getArg 1
      let ts := tId.getId.eraseMacroScopes.toString
      match ComputeTier.parse? ts with
      | some tier => compute? := some tier
      | none =>
          throwErrorAt tId s!"unknown `compute` tier `{ts}`{Qed.Diag.didYouMean ts ComputeTier.allNames} (supported: {String.intercalate ", " ComputeTier.allNames})"
    else if k == ``deployTimeoutClause then
      if timeoutSec?.isSome then throwErrorAt c s!"duplicate `timeout` clause in `deploy {depShort}`"
      timeoutSec? := some (← parseDurationUnit (c.getArg 1))
      timeoutRef? := some (c.getArg 1)
    else if k == ``deployPreviewBlockClause then
      if previewRef?.isSome then throwErrorAt c s!"duplicate `preview:` block in `deploy {depShort}`"
      previewRef? := some c
      let mut seen : Array Name := #[]
      let mut rawPreviewDomain? : Option (Syntax × String) := none
      for pc in (c.getArg 2).getArgs do
        let pk := pc.getKind
        if seen.contains pk then
          throwErrorAt pc s!"duplicate clause in `preview:` of `deploy {depShort}`"
        seen := seen.push pk
        if pk == ``deployPreviewOnPrClause then
          let bStr := (pc.getArg 1).getId.eraseMacroScopes.toString
          preview := { preview with enabled := bStr == "true" }
        else if pk == ``deployPreviewSubdomainClause then
          if rawPreviewDomain?.isSome then
            throwErrorAt pc s!"cannot specify both `subdomain` and `domain` in `preview:` of `deploy {depShort}`"
          preview := { preview with subdomain? := some (⟨pc.getArg 1⟩ : TSyntax `str).getString, host? := none }
        else if pk == ``deployPreviewDomainClause then
          if seen.contains ``deployPreviewSubdomainClause then
            throwErrorAt pc s!"cannot specify both `subdomain` and `domain` in `preview:` of `deploy {depShort}`"
          rawPreviewDomain? := some (pc.getArg 1, (⟨pc.getArg 1⟩ : TSyntax `str).getString)
        else if pk == ``deployPreviewProtectionClause then
          let arg := pc.getArg 1
          let isPub := arg.getAtomVal == "public" || arg.getId.eraseMacroScopes == `anyone
          preview := { preview with protection := if isPub then .pub else .team_only }
        else if pk == ``deployPreviewTtlClause then
          preview := { preview with ttlSec := ← parseDurationUnit (pc.getArg 1) }
        else
          throwErrorAt pc s!"unexpected clause in `preview:`"
      if let some (dRef, rawDom) := rawPreviewDomain? then
        if preview.enabled then
          let some hp := HostPattern.parse? rawDom
            | throwErrorAt dRef s!"`deploy {depShort}`: invalid preview `domain` `{rawDom}` (expected RFC 1123 host or `*.example.com`)"
          preview := { preview with host? := some hp, subdomain? := none }
        else
          preview := { preview with host? := HostPattern.parse? rawDom, subdomain? := none }
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
        let compTarget : Ident :=
          if env.contains (currNs ++ appIdent.getId ++ `app) || env.contains (appIdent.getId ++ `app) then
            mkIdentFrom appIdent (appIdent.getId ++ `app)
          else appIdent
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
