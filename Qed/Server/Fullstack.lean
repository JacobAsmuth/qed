import Qed.Server.Elab
import Qed.Ssr
import Qed.Socket
import Qed.Component.Syntax

namespace Qed.Server
open Qed.Lang

/-! ## `fullstack` Command Elaborator & Endpoint Closure Verification -/

private def collectReachableDefns (env : Lean.Environment) :
    Nat → List Lean.Name → Std.HashSet Lean.Name → Except Lean.Name (Std.HashSet Lean.Name)
  | _, [], seen => .ok seen
  | 0, n :: _, _ => .error n
  | fuel + 1, n :: rest, seen =>
      if seen.contains n then
        collectReachableDefns env fuel rest seen
      else
        let seen' := seen.insert n
        if Qed.Diag.isToolchainRoot (Qed.Diag.modRootOf env n) then
          collectReachableDefns env fuel rest seen'
        else
          match env.find? n with
          | some (.defnInfo d) =>
              collectReachableDefns env fuel (d.value.getUsedConstants.toList ++ rest) seen'
          | _ =>
              collectReachableDefns env fuel rest seen'

open Lean Elab Command in
private def verifyFullstackRpcClosure (env : Environment) (fsName : Name) (srvInfo : ServerInfo)
    (cliIdent : Ident) (resolvedCli : Name) : CommandElabM Unit := do
  let srvMap := serverRegistry.getState env
  let mut rpcConstMap : NameMap (ServerInfo × ServerMethodInfo) := {}
  for (_, otherSrv) in srvMap do
    for mInfo in otherSrv.methods do
      if mInfo.rawRpcConst != .anonymous then
        rpcConstMap := rpcConstMap.insert mInfo.rawRpcConst (otherSrv, mInfo)
      rpcConstMap := rpcConstMap.insert (otherSrv.serverName ++ Name.mkSimple mInfo.name) (otherSrv, mInfo)
  let visited ← match collectReachableDefns env 300000 [resolvedCli] {} with
    | .ok s => pure s
    | .error pending =>
        throwErrorAt cliIdent s!"`fullstack {fsName}`: RPC endpoint closure analysis exceeded fuel limit while inspecting `{pending}`"
  let chMap := Qed.channelRegistry.getState env
  let mut fsChanConstMap : NameMap Qed.ChannelInfo := {}
  for (_, chInfo) in chMap do
    match chInfo.kind with
    | .fullstack _ _ _ =>
        if chInfo.subHelperConst != .anonymous then
          fsChanConstMap := fsChanConstMap.insert chInfo.subHelperConst chInfo
        if chInfo.sendHelperConst != .anonymous then
          fsChanConstMap := fsChanConstMap.insert chInfo.sendHelperConst chInfo
    | .external .. => pure ()
  for n in visited do
    if let some chInfo := fsChanConstMap.find? n then
      if chInfo.ownerName != srvInfo.serverName then
        throwErrorAt cliIdent s!"`fullstack {fsName}` mounts `server {srvInfo.shortName}`, but client `{cliIdent.getId}` subscribes to WebSocket channel `{chInfo.ownerShort}.{chInfo.channelName}` on unmounted server `{chInfo.ownerShort}`"
    if let some (otherSrv, mInfo) := rpcConstMap.find? n then
      if otherSrv.serverName != srvInfo.serverName then
        throwErrorAt cliIdent s!"`fullstack {fsName}` mounts `server {srvInfo.shortName}`, but client `{cliIdent.getId}` calls RPC `{otherSrv.shortName}.{mInfo.name}` on unmounted server `{otherSrv.shortName}`"
    let root := Qed.Diag.modRootOf env n
    if root != `Qed && root != `Js && root != `Cli then
      if let some (.defnInfo d) := env.find? n then
        let badRef ← IO.mkRef (none : Option String)
        d.value.forEach fun sub => do
          if (← badRef.get).isNone then
            if let .lit (.strVal s) := sub then
              if s.startsWith "/_qed/rpc/" then
                let rest := (s.drop 10).toString
                match rest.splitOn "/" with
                | [srvPart, methodPart] =>
                    if srvPart != srvInfo.shortName || !(srvInfo.methods.any (·.name == methodPart)) then
                      badRef.set (some s)
                | _ => badRef.set (some s)
        if let some url ← badRef.get then
          let avail := String.intercalate ", " (srvInfo.methods.toList.map (·.name))
          throwErrorAt cliIdent s!"`fullstack {fsName}` mounts `server {srvInfo.shortName}` (methods: [{avail}]), but client `{cliIdent.getId}` targets invalid RPC endpoint `{url}`"

open Lean Elab Command in
@[command_elab fullstackCmd]
def elabFullstackCmd : CommandElab := fun stx => do
  let fsIdent : Ident := ⟨(stx.getArg 1)⟩
  let fsName := fsIdent.getId
  let currNs ← getCurrNamespace
  let fullFsName := currNs ++ fsName
  let clauses := (stx.getArg 3).getArgs

  let mut srvIdent? : Option Ident := none
  let mut cliIdent? : Option Ident := none
  let mut title?    : Option String := none

  for c in clauses do
    let k := c.getKind
    if k == ``fsServerClause then
      if srvIdent?.isSome then throwErrorAt c "duplicate `server` clause in `fullstack`"
      srvIdent? := some ⟨(c.getArg 1)⟩
    else if k == ``fsClientClause then
      if cliIdent?.isSome then throwErrorAt c "duplicate `client` clause in `fullstack`"
      cliIdent? := some ⟨(c.getArg 1)⟩
    else if k == ``fsTitleClause then
      if title?.isSome then throwErrorAt c "duplicate `title` clause in `fullstack`"
      title? := some ((⟨(c.getArg 1)⟩ : TSyntax `str).getString)
    else
      throwErrorAt c "unexpected clause in `fullstack` block"

  let some srvIdent := srvIdent?
    | throwErrorAt fsIdent s!"`fullstack {fsName}` must specify `server <ServerName>`"
  let some cliIdent := cliIdent?
    | throwErrorAt fsIdent s!"`fullstack {fsName}` must specify `client <AppName>`"

  let env ← getEnv
  let some srvInfo := Qed.Diag.lookupNameMapExt? serverRegistry env currNs (← getOpenDecls) srvIdent.getId
    | throwErrorAt srvIdent s!"unknown `server` `{srvIdent.getId}` in `fullstack {fsName}`"

  -- Validate that `client` resolves to a `Qed.App _ _` value (or a `component`/`app` owning `.app`)
  let cliTarget := resolveAppTargetIdent env currNs cliIdent
  let resolvedCli ← try
      liftCoreM <| realizeGlobalConstNoOverloadWithInfo cliTarget
    catch _ =>
      if let some _ ← liftCoreM (Qed.lookupComponent? cliIdent.getId) then
        throwErrorAt cliIdent s!"component `{cliIdent.getId}` in `fullstack {fsName}` is not a top-level mountable app (remove `prop`, `bind`, `children`, `event`, and uninitialized `state` fields)"
      else
        throwErrorAt cliIdent s!"unknown `client` `{cliIdent.getId}` in `fullstack {fsName}`; specify a top-level `component` or `Qed.App` value"
  let appCheckId := mkIdentFrom fsIdent (fsName ++ `clientApp)
  elabCommand (← `(command| abbrev $appCheckId := $cliTarget))

  let cliCompName :=
    if resolvedCli.getString! == "app" then resolvedCli.getPrefix else resolvedCli
  verifyFullstackRpcClosure env fsName srvInfo cliIdent resolvedCli

  if env.contains (cliCompName ++ `usedRpcs) then
    let usedRpcsId := mkIdentFrom cliIdent (cliCompName ++ `usedRpcs)
    let srvMethodsId := mkIdentFrom srvIdent (srvInfo.serverName ++ `methods)
    let srvShortLit := Syntax.mkStrLit srvInfo.shortName
    let epThmId := mkIdentFrom fsIdent (fsName ++ `rpc_endpoints_valid)
    let ssrClosureId := mkIdentFrom fsIdent (fsName ++ `ssr_rpc_closure_complete)
    elabCommand (← `(command|
      theorem $epThmId :
          ∀ ep ∈ $usedRpcsId, ep.1 = $srvShortLit ∧ ep.2 ∈ $srvMethodsId := by
        decide))
    elabCommand (← `(command|
      theorem $ssrClosureId
          (dispatchMethod : String → ByteArray → Except String ByteArray)
          (ep : String × String) (hep : ep ∈ $usedRpcsId) (reqBody : ByteArray) :
          Qed.ssrDispatchRpc $srvShortLit $srvMethodsId dispatchMethod "POST"
              ("/_qed/rpc/" ++ ep.1 ++ "/" ++ ep.2) reqBody =
            dispatchMethod ep.2 reqBody :=
        Qed.ssr_rpc_closure_complete $srvShortLit $srvMethodsId $usedRpcsId $epThmId
          dispatchMethod (by decide) (by decide) ep hep reqBody))

  if env.contains (cliCompName ++ `usedChannels) then
    let usedChsId := mkIdentFrom cliIdent (cliCompName ++ `usedChannels)
    let srvChsId := mkIdentFrom srvIdent (srvInfo.serverName ++ `channels)
    let srvShortLit := Syntax.mkStrLit srvInfo.shortName
    let wsThmId := mkIdentFrom fsIdent (fsName ++ `ws_endpoints_valid)
    elabCommand (← `(command|
      theorem $wsThmId :
          ∀ ch ∈ $usedChsId, ch.1 = $srvShortLit ∧ ch.2 ∈ $srvChsId := by
        decide))

  let pageTitle := title?.getD (fsName.toString)
  let titleId := mkIdentFrom fsIdent (fsName ++ `title)
  elabCommand (← `(command| def $titleId : String := $(Syntax.mkStrLit pageTitle)))

  modifyEnv fun e => fullstackRegistry.addEntry e {
    fullstackName := fullFsName
    serverName := srvInfo.serverName
    title := pageTitle
  }

/-! ## `qedServerMain <FullstackName>` Entrypoint Generator -/

syntax (name := qedServerMainCmd) "qedServerMain " ident : command

open Lean Elab Command in
@[command_elab qedServerMainCmd]
def elabQedServerMain : CommandElab := fun stx => do
  let fsIdent : Ident := ⟨stx[1]⟩
  let env ← getEnv
  let currNs ← getCurrNamespace
  let some fsInfo := (Qed.Diag.lookupNameMapExt? fullstackRegistry env currNs (← getOpenDecls) fsIdent.getId).orElse (fun _ =>
      (fullstackRegistry.getState env).toList.findSome? fun (k, v) =>
        if k.getString! == fsIdent.getId.toString then some v else none)
    | throwErrorAt fsIdent s!"unknown `fullstack` declaration `{fsIdent.getId}`"
  let srvMap := serverRegistry.getState env
  let some srvInfo := srvMap.find? fsInfo.serverName
    | throwErrorAt fsIdent s!"internal error: `server` `{fsInfo.serverName}` not found in registry"
  let srvId (leaf : Name) := mkIdentFrom fsIdent (srvInfo.serverName ++ leaf)
  let cliAppId := mkIdentFrom fsIdent (fsInfo.fullstackName ++ `clientApp)
  let asyncNames : Array Term := srvInfo.methods.filterMap fun m => if m.isAsync then some (Syntax.mkStrLit m.name) else none
  let dbCfgIds : Array Ident := srvInfo.databases.map (mkIdentFrom fsIdent ·)
  let optId (id? : Option Ident) : CommandElabM Term := match id? with | some id => `(Option.some $id:ident) | none => `(Option.none)
  let primaryDbArg ← optId dbCfgIds[0]?
  let authArg ← optId (srvInfo.authConfig?.map (mkIdentFrom fsIdent ·))
  let hookFlagsArg ← `(($(quote srvInfo.hasOnCreateAccount), $(quote srvInfo.hasOnSignIn)))
  let initStateArg : Term ← if srvInfo.hasState then pure (srvId `initState : Term) else `((() : Unit))
  let jobsArg : Term ← if srvInfo.jobs.isEmpty then `(#[]) else
    if srvInfo.hasState then pure (srvId `jobs : Term) else `(($(srvId `jobs)).map Qed.Server.StatelessJob.toUnitJob)
  let wrapHandler (id : Ident) : CommandElabM Term :=
    `(fun {m} [Monad m] [Qed.Server.MonadServer m] [Qed.Server.MonadAtomic _ m] => $id)
  let optHandler (enabled : Bool) (id : Ident) : CommandElabM Term :=
    if enabled then do `(some $(← wrapHandler id)) else `(none)
  let runnerCall ← `($(mkIdent `Qed.Server.Native.runStatefulFullstack) $cliAppId $(quote fsInfo.title)
      $(quote srvInfo.shortName) $initStateArg $(srvId `secrets) $(← wrapHandler (srvId `dispatchM))
      port staticDir devMode numWorkers $(← optHandler (!srvInfo.channels.isEmpty) (srvId `wsDispatchM))
      (some #[$asyncNames,*]) $(← optHandler srvInfo.hasHttpRoutes (srvId `httpDispatchM)) $jobsArg $authArg
      $(← optHandler (srvInfo.hasOnCreateAccount || srvInfo.hasOnSignIn) (srvId `authHookM)) $hookFlagsArg $primaryDbArg)
  let initDbCheck ← if dbCfgIds.isEmpty then `(pure true) else `($(mkIdent `Qed.Server.Native.initDatabases) #[$[$dbCfgIds:ident],*])
  let parseCliCall ← `($(mkIdent `Qed.Server.Native.parseServerCliArgs) args)
  elabCommand (← `(command|
    def $(mkIdent `main):ident (args : List String) : IO UInt32 := do
      let (staticDir, port, devMode, numWorkers) ← $parseCliCall:term
      if !(← $initDbCheck) then return 1
      $runnerCall:term))

end Qed.Server
