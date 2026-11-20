import Lean
import Qed.Lang
import Qed.Server.Ensured
import Qed.Socket.Basic

namespace Qed

/-! ## Persistent Server RPC Metadata Registry (`serverRegistry`) -/

structure ServerMethodInfo where
  name            : String
  paramNames      : Array Lean.Name := #[]
  paramCount      : Nat
  isReadOnly      : Bool
  isAsync         : Bool
  isFallible      : Bool
  isOption        : Bool
  hasClientReq    : Bool := false
  requiresAuth    : Bool := false
  clientReqConst  : Option Lean.Name := none
  clientReqLabel  : String := ""
  hasEnsures      : Bool := false
  ensPredConst    : Option Lean.Name := none
  domainErrTags   : Array String := #[]
  errTypeConst    : Option Lean.Name := none
  rawRpcConst     : Lean.Name := .anonymous
  outcomeConst    : Lean.Name := .anonymous
  paramTypeConsts : Array Lean.Name := #[]
deriving Inhabited, Repr

structure ServerInfo where
  serverName       : Lean.Name
  shortName        : String
  hasState         : Bool
  secrets          : Array String
  envVars          : Array (String × String × Option String)
  externalServices : Array (String × String)
  methods          : Array ServerMethodInfo
  channels         : Array String := #[]
deriving Inhabited

initialize serverRegistry :
    Lean.SimplePersistentEnvExtension ServerInfo (Lean.NameMap ServerInfo) ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays =>
      arrays.foldl (fun acc arr => arr.foldl (fun m info => m.insert info.serverName info) acc) {}
    addEntryFn := fun m info => m.insert info.serverName info
  }

/-- Resolves a `Server.fn` reference from a component (`Catalog.order`, `CloudBooks.Catalog.order`,
    or an `open Catalog` method name) against `serverRegistry`. -/
def lookupServerMethod? (env : Lean.Environment) (currNs : Lean.Name)
    (openDecls : List Lean.OpenDecl) (callName : Lean.Name) :
    Option (ServerInfo × ServerMethodInfo) :=
  let reg := serverRegistry.getState env
  let resolved := Lean.ResolveName.resolveGlobalName env {} currNs openDecls callName
  let byResolved := resolved.findSome? fun (fullConst, _) =>
    reg.toList.findSome? fun (_, srvInfo) =>
      srvInfo.methods.findSome? fun mInfo =>
        let pubConst := srvInfo.serverName ++ Lean.Name.mkSimple mInfo.name
        if fullConst == pubConst || fullConst == mInfo.rawRpcConst then some (srvInfo, mInfo)
        else none
  byResolved.orElse fun _ =>
    match callName with
    | .str srvPart mStr =>
        let srvClean := srvPart.eraseMacroScopes
        let cand1 := currNs ++ srvClean
        let srv? := (reg.find? cand1).orElse (fun _ => reg.find? srvClean)
          |>.orElse (fun _ => reg.toList.findSome? fun (_, info) =>
            if info.shortName == srvClean.toString then some info else none)
        srv?.bind fun srvInfo =>
          (srvInfo.methods.find? (·.name == mStr)).map (srvInfo, ·)
    | _ => none


/-! ## Unified Channel Registry (Fullstack `server` `channel` + 3rd-Party `external` `ws`) -/

inductive ExtWsCodec where
  | json
  | proto
  | text
  | bytes
deriving Inhabited, DecidableEq, Repr

inductive ChannelKind where
  | fullstack (serverName : Lean.Name) (serverShort : String) (wsPath : String)
  | external  (serviceName : Lean.Name) (isBinary : Bool) (eventCodec : ExtWsCodec) (sendCodec : ExtWsCodec)
deriving Inhabited, DecidableEq, Repr

structure ChannelInfo where
  fullName            : Lean.Name
  ownerName           : Lean.Name
  ownerShort          : String
  channelName         : String
  kind                : ChannelKind
  paramNames          : Array Lean.Name := #[]
  paramCount          : Nat := 0
  paramTypeConsts     : Array Lean.Name := #[]
  eventTypeConst      : Lean.Name := .anonymous
  hasJoinSnapshot     : Bool := false
  joinTypeConst       : Lean.Name := .anonymous
  hasSend             : Bool := false
  sendParamNames      : Array Lean.Name := #[]
  sendParamCount      : Nat := 0
  sendParamTypeConsts : Array Lean.Name := #[]
  sendReqConst        : Option Lean.Name := none
  sendReqLabel        : String := ""
  requiresAuth        : Bool := false
  clientReqConst      : Option Lean.Name := none
  clientReqLabel      : String := ""
  hasEnsures          : Bool := false
  ensPredConst        : Option Lean.Name := none
  defaultReconnect    : Reconnect := .defaultPolicy
  keyHelperConst      : Lean.Name := .anonymous
  subHelperConst      : Lean.Name := .anonymous
  sendHelperConst     : Lean.Name := .anonymous
  unsubHelperConst    : Lean.Name := .anonymous
deriving Inhabited, Repr

initialize channelRegistry :
    Lean.SimplePersistentEnvExtension ChannelInfo (Lean.NameMap ChannelInfo) ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays =>
      arrays.foldl (fun acc arr => arr.foldl (fun m info => m.insert info.fullName info) acc) {}
    addEntryFn := fun m info => m.insert info.fullName info
  }

/-- Resolves a `<Server>.<chan>` or `<External>.<chan>` channel reference from a component
    against `channelRegistry`. -/
def lookupChannel? (env : Lean.Environment) (currNs : Lean.Name)
    (openDecls : List Lean.OpenDecl) (callName : Lean.Name) :
    Option ChannelInfo :=
  let reg := channelRegistry.getState env
  let cand1 := currNs ++ callName
  if let some info := reg.find? cand1 then some info
  else if let some info := reg.find? callName then some info
  else
    let resolved := Lean.ResolveName.resolveGlobalName env {} currNs openDecls (callName.appendAfter "_sub")
    let byResolved := resolved.findSome? fun (fullConst, _) =>
      reg.toList.findSome? fun (_, info) =>
        if info.subHelperConst == fullConst then some info else none
    byResolved.orElse fun _ =>
      match callName with
      | .str ownerPart chStr =>
          let ownerClean := ownerPart.eraseMacroScopes
          reg.toList.findSome? fun (_, info) =>
            if info.channelName == chStr &&
               (info.ownerShort == ownerClean.toString ||
                info.ownerName == currNs ++ ownerClean ||
                info.ownerName == ownerClean) then
              some info
            else none
      | _ => none

/-! ## Shared `reconnect` Policy Parser (`off` / `fixed(...)` / `backoff(...)`) -/

section ReconnectParser
open Lean Qed.Lang

private def parseNatLitArg (stx : Syntax) : MacroM Nat := do
  let u := unwrapParens1 stx
  if u.getKind == ``qedLitNum then
    return (⟨(u.getArg 0)⟩ : TSyntax `num).getNat
  else
    Macro.throwErrorAt stx "expected a non-negative integer millisecond/retry literal in `reconnect` policy"

private def parseOptNatLitArg (stx : Syntax) : MacroM (Option Nat) := do
  let u := unwrapParens1 stx
  if u.getKind == ``qedIdent && (u.getArg 0).getId == `none then return none
  else if u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId == `some then
    let args := (u.getArg 2).getSepArgs
    if args.size == 1 && args[0]!.getKind == ``qedCallArgPos then
      return some (← parseNatLitArg args[0]![0])
    else Macro.throwErrorAt stx "expected `some(<nat>)` or `<nat>`"
  else
    return some (← parseNatLitArg u)

/-- Parses `off`, `fixed(delayMs[, maxRetries])`, or `backoff(initialMs, maxMs[, maxRetries])`
    (with optional named `maxRetries=...`) into a `Qed.Reconnect` value. -/
def parseReconnectExpr (exprStx : Syntax) : MacroM Reconnect := do
  let u := unwrapParens1 exprStx
  if u.getKind == ``qedIdent then
    let nm := (u.getArg 0).getId.eraseMacroScopes
    if nm == `off || nm == `none then return .off
    else if nm == `default || nm == `backoff then return .defaultPolicy
    else Macro.throwErrorAt u s!"unknown `reconnect` policy `{nm}`; use `off`, `fixed(ms[, max])`, or `backoff(initMs, maxMs[, max])`"
  else if u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent then
    let fn := ((u.getArg 0).getArg 0).getId.eraseMacroScopes
    let rawArgs := (u.getArg 2).getSepArgs
    let mut posArgs : Array Syntax := #[]
    let mut maxRet? : Option (Option Nat) := none
    for a in rawArgs do
      if a.getKind == ``qedCallArgNamed then
        let k := (a.getArg 0).getId.eraseMacroScopes
        if k == `maxRetries || k == `max then
          maxRet? := some (← parseOptNatLitArg (a.getArg 2))
        else
          Macro.throwErrorAt a s!"unknown `reconnect` named argument `{k}`; expected `maxRetries`"
      else if a.getKind == ``qedCallArgPos then
        posArgs := posArgs.push (a.getArg 0)
      else
        Macro.throwErrorAt a "unexpected argument in `reconnect` policy"
    if fn == `fixed then
      if posArgs.size == 1 then
        return .fixed (← parseNatLitArg posArgs[0]!) (maxRet?.getD none)
      else if posArgs.size == 2 && maxRet?.isNone then
        return .fixed (← parseNatLitArg posArgs[0]!) (← parseOptNatLitArg posArgs[1]!)
      else
        Macro.throwErrorAt u "`reconnect fixed(...)` expects 1 or 2 arguments: `fixed(delayMs)` or `fixed(delayMs, maxRetries)`"
    else if fn == `backoff then
      if posArgs.size == 0 then
        return .backoff 250 30000 (maxRet?.getD none)
      else if posArgs.size == 2 then
        let initMs ← parseNatLitArg posArgs[0]!
        let maxMs ← parseNatLitArg posArgs[1]!
        if maxMs < initMs then
          Macro.throwErrorAt u s!"`reconnect backoff({initMs}, {maxMs})` requires `initialMs <= maxMs`"
        return .backoff initMs maxMs (maxRet?.getD none)
      else if posArgs.size == 3 && maxRet?.isNone then
        let initMs ← parseNatLitArg posArgs[0]!
        let maxMs ← parseNatLitArg posArgs[1]!
        if maxMs < initMs then
          Macro.throwErrorAt u s!"`reconnect backoff({initMs}, {maxMs})` requires `initialMs <= maxMs`"
        return .backoff initMs maxMs (← parseOptNatLitArg posArgs[2]!)
      else
        Macro.throwErrorAt u "`reconnect backoff(...)` expects `backoff(initialMs, maxMs)` or `backoff(initialMs, maxMs, maxRetries)`"
    else
      Macro.throwErrorAt u s!"unknown `reconnect` policy `{fn}`; use `off`, `fixed(...)`, or `backoff(...)`"
  else
    Macro.throwErrorAt u "expected `reconnect` policy: `off`, `fixed(ms[, max])`, or `backoff(initMs, maxMs[, max])`"

def Reconnect.toSyntaxTerm (r : Reconnect) : MacroM Term := do
  match r with
  | .off => `(Qed.Reconnect.off)
  | .fixed d none =>
      let dLit := Syntax.mkNumLit (toString d)
      `(Qed.Reconnect.fixed $dLit none)
  | .fixed d (some m) =>
      let dLit := Syntax.mkNumLit (toString d)
      let mLit := Syntax.mkNumLit (toString m)
      `(Qed.Reconnect.fixed $dLit (some $mLit))
  | .backoff i mx none =>
      let iLit := Syntax.mkNumLit (toString i)
      let mxLit := Syntax.mkNumLit (toString mx)
      `(Qed.Reconnect.backoff $iLit $mxLit none)
  | .backoff i mx (some m) =>
      let iLit := Syntax.mkNumLit (toString i)
      let mxLit := Syntax.mkNumLit (toString mx)
      let mLit := Syntax.mkNumLit (toString m)
      `(Qed.Reconnect.backoff $iLit $mxLit (some $mLit))

end ReconnectParser

end Qed
