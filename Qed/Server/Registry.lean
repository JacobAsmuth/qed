import Lean
import Qed.Diag
import Qed.Lang
import Qed.Cloud.Env
import Qed.Auth.Core
import Qed.Server.Ensured
import Qed.Socket.Basic

namespace Qed

@[simp] theorem QedVal.val_ensured {α : Type} {p : α → Prop} (e : Ensured α p) :
    Qed.Lang.QedVal.val e = Field.val e := rfl

/-! ## Persistent Server & Channel Metadata Registries -/

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
  rawRpcConst     : Lean.Name := .anonymous
  outcomeConst    : Lean.Name := .anonymous
  paramTypeConsts : Array Lean.Name := #[]
deriving Inhabited, Repr

structure ServerInfo where
  serverName         : Lean.Name
  shortName          : String
  hasState           : Bool
  secrets            : Array String
  ownSecrets         : Array String := #[]
  envVars            : Array (String × String × Option String)
  externalServices   : Array (String × String)
  methods            : Array ServerMethodInfo
  channels           : Array String := #[]
  jobs               : Array String := #[]
  databases          : Array Lean.Name := #[]
  authName?          : Option Lean.Name := none
  authConfig?        : Option Lean.Name := none
  hasOnCreateAccount : Bool := false
  hasOnSignIn        : Bool := false
  hasHttpRoutes      : Bool := false
  hasWsProject       : Bool := false
deriving Inhabited

initialize serverRegistry : Lean.SimplePersistentEnvExtension ServerInfo (Lean.NameMap ServerInfo) ← Qed.Diag.mkNameMapExt (·.serverName)
initialize failedServerRegistry : Lean.SimplePersistentEnvExtension Lean.Name (Lean.NameMap Lean.Name) ← Qed.Diag.mkNameMapExt id

def lookupServerMethod? (env : Lean.Environment) (currNs : Lean.Name) (openDecls : List Lean.OpenDecl) (callName : Lean.Name) :
    Option (ServerInfo × ServerMethodInfo) :=
  let reg := serverRegistry.getState env
  ((Lean.ResolveName.resolveGlobalName env {} currNs openDecls callName).findSome? fun (fc, _) =>
    reg.toList.findSome? fun (_, srv) => srv.methods.findSome? fun m =>
      if fc == srv.serverName ++ Lean.Name.mkSimple m.name || fc == m.rawRpcConst then some (srv, m) else none).orElse fun _ =>
    match callName with
    | .str srvPart mStr =>
        let s := srvPart.eraseMacroScopes
        ((reg.find? (currNs ++ s)).orElse (fun _ => reg.find? s) |>.orElse (fun _ => reg.toList.findSome? fun (_, i) => if i.shortName == s.toString then some i else none)).bind fun srv =>
          (srv.methods.find? (·.name == mStr)).map (srv, ·)
    | _ => none

inductive ExtWsCodec where | json | proto | text | bytes deriving Inhabited, DecidableEq, Repr

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

def ChannelInfo.mkDefault (ownerName : Lean.Name) (ownerShort : String) (chName : Lean.Name) (kind : ChannelKind)
    (paramNames paramTypeConsts : Array Lean.Name) (defaultReconnect : Reconnect) : ChannelInfo :=
  let sub (s : String) := ownerName ++ chName.appendAfter s
  { fullName := ownerName ++ chName, ownerName, ownerShort, channelName := chName.toString, kind,
    paramNames, paramCount := paramNames.size, paramTypeConsts, defaultReconnect,
    eventTypeConst := sub "_Event", keyHelperConst := sub "_key", subHelperConst := sub "_sub", unsubHelperConst := sub "_unsub" }

initialize channelRegistry : Lean.SimplePersistentEnvExtension ChannelInfo (Lean.NameMap ChannelInfo) ← Qed.Diag.mkNameMapExt (·.fullName)

def lookupChannel? (env : Lean.Environment) (currNs : Lean.Name) (openDecls : List Lean.OpenDecl) (callName : Lean.Name) : Option ChannelInfo :=
  let reg := channelRegistry.getState env
  (reg.find? (currNs ++ callName)).orElse (fun _ => reg.find? callName)
  |>.orElse (fun _ => (Lean.ResolveName.resolveGlobalName env {} currNs openDecls (callName.appendAfter "_sub")).findSome? fun (fc, _) =>
      reg.toList.findSome? fun (_, i) => if i.subHelperConst == fc then some i else none)
  |>.orElse fun _ => match callName with
    | .str ownerPart chStr =>
        let o := ownerPart.eraseMacroScopes
        reg.toList.findSome? fun (_, i) => if i.channelName == chStr && (i.ownerShort == o.toString || i.ownerName == currNs ++ o || i.ownerName == o) then some i else none
    | _ => none

/-! ## Shared `reconnect` Policy Parser -/

section ReconnectParser
open Lean Qed.Lang

private def parseNatLitArg (stx : Syntax) : MacroM Nat := do
  let u := unwrapParens1 stx
  if u.getKind == ``qedLitNum then return (⟨u.getArg 0⟩ : TSyntax `num).getNat
  else Macro.throwErrorAt stx "expected a non-negative integer millisecond/retry literal in `reconnect` policy"

private def parseOptNatLitArg (stx : Syntax) : MacroM (Option Nat) := do
  let u := unwrapParens1 stx
  if u.getKind == ``qedIdent && (u.getArg 0).getId == `none then return none
  else if u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId == `some then
    let args := (u.getArg 2).getSepArgs
    if args.size == 1 && args[0]!.getKind == ``qedCallArgPos then some <$> parseNatLitArg args[0]![0]
    else Macro.throwErrorAt stx "expected `some(<nat>)` or `<nat>`"
  else some <$> parseNatLitArg u

def parseReconnectExpr (exprStx : Syntax) : MacroM Reconnect := do
  let u := unwrapParens1 exprStx
  if u.getKind == ``qedIdent then
    match (u.getArg 0).getId.eraseMacroScopes with
    | `off | `none => return .off
    | `default | `backoff => return .defaultPolicy
    | nm => Macro.throwErrorAt u s!"unknown `reconnect` policy `{nm}`; use `off`, `fixed(ms[, max])`, or `backoff(initMs, maxMs[, max])`"
  else if u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent then
    let fn := ((u.getArg 0).getArg 0).getId.eraseMacroScopes
    let (pos, named) ← splitCallArgsMacro "reconnect" (u.getArg 2).getSepArgs (some ["maxRetries", "max"])
    let maxRet? ← named.foldlM (init := none) fun _ (_, v) => some <$> parseOptNatLitArg v
    let getMax (i : Nat) := if pos.size == i + 1 then parseOptNatLitArg pos[i]! else pure (maxRet?.getD none)
    match fn with
    | `fixed =>
        if pos.size == 1 || (pos.size == 2 && maxRet?.isNone) then return .fixed (← parseNatLitArg pos[0]!) (← getMax 1)
        Macro.throwErrorAt u "`reconnect fixed(...)` expects 1 or 2 arguments: `fixed(delayMs)` or `fixed(delayMs, maxRetries)`"
    | `backoff =>
        if pos.size == 0 then return .backoff 250 30000 (maxRet?.getD none)
        if pos.size == 2 || (pos.size == 3 && maxRet?.isNone) then
          let initMs ← parseNatLitArg pos[0]!; let maxMs ← parseNatLitArg pos[1]!
          if maxMs < initMs then Macro.throwErrorAt u s!"`reconnect backoff({initMs}, {maxMs})` requires `initialMs <= maxMs`"
          return .backoff initMs maxMs (← getMax 2)
        Macro.throwErrorAt u "`reconnect backoff(...)` expects `backoff(initialMs, maxMs)` or `backoff(initialMs, maxMs, maxRetries)`"
    | _ => Macro.throwErrorAt u s!"unknown `reconnect` policy `{fn}`; use `off`, `fixed(...)`, or `backoff(...)`"
  else Macro.throwErrorAt u "expected `reconnect` policy: `off`, `fixed(ms[, max])`, or `backoff(initMs, maxMs[, max])`"

def Reconnect.toSyntaxTerm : Reconnect → MacroM Term
  | .off => `(Qed.Reconnect.off)
  | .fixed d m? => `(Qed.Reconnect.fixed $(quote d) $(quote m?))
  | .backoff i mx m? => `(Qed.Reconnect.backoff $(quote i) $(quote mx) $(quote m?))

end ReconnectParser

namespace Server

/-! ## Persistent `external`, `database` & `auth` Registries and Shared Helpers -/

structure ExternalServiceInfo where
  serviceName : Lean.Name
  baseOrigin  : String
  secrets     : Array String
  methods     : Array Lean.Name
deriving Inhabited

initialize externalRegistry : Lean.SimplePersistentEnvExtension ExternalServiceInfo (Lean.NameMap ExternalServiceInfo) ← Qed.Diag.mkNameMapExt (·.serviceName)

private def reservedEnvNames : List String := [
  "QED_DEPLOY_ENV", "PORT", "HOST", "PATH", "GOOGLE_APPLICATION_CREDENTIALS", "QED_INSECURE_SKIP_TLS_VERIFY",
  "QED_CA_CERT_FILE", "QED_GCP_TOKEN_URL", "QED_CSP", "QED_RPC_ALLOWED_ORIGINS", "QED_WS_ALLOWED_ORIGINS",
  "QED_AUTH_SECRET", "QED_AUTH_SECRET_PREV", "QED_AUTH_REQUIRE_EXP", "QED_HOST", "QED_WORKERS",
  "QED_BLOCKING_THREADS", "QED_RATE_LIMIT_RPS", "QED_RATE_LIMIT_BURST"]

private def isReservedEnvVarName (s : String) : Bool :=
  let u := s.toUpper
  reservedEnvNames.contains u || ["K_", "LD_", "SSL_CERT_", "CLOUD_RUN_", "QED_EXT_"].any (u.startsWith ·)

def isValidEnvVarName (s : String) : Bool :=
  let isA (c : Char) := ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || c == '_'
  match s.toList with
  | [] => false
  | first :: rest => s.length <= 128 && isA first && rest.all (fun c => isA c || ('0' ≤ c && c ≤ '9')) && !isReservedEnvVarName s

def exprCallsOld (stx : Lean.Syntax) : Bool :=
  Qed.Lang.stxAny (fun s => s.getKind == ``Qed.Lang.qedCall && (s.getArg 0).getKind == ``Qed.Lang.qedIdent && ((s.getArg 0).getArg 0).getId.eraseMacroScopes == `old) stx

structure DbEncKeyInfo where
  keyEnv    : String
  fallback? : Option String := none
  isBytes   : Bool := false
  prevKeys  : List (String × Option String) := []
deriving Inhabited, Repr

structure DbColumnInfo where
  name         : String
  isPrimaryKey : Bool := false
  isImmutable  : Bool := false
  isUnique     : Bool := false
  isNullable   : Bool := false
  isNat        : Bool := false
  isInt        : Bool := false
  refs?        : Option (String × String) := none
  encKey?      : Option DbEncKeyInfo := none
deriving Inhabited, Repr

structure DbTableInfo where
  tableName            : String
  rowTypeConst         : Lean.Name
  columns              : Array DbColumnInfo
  hasMeta              : Bool := false
  hasReadPolicy        : Bool := false
  hasInsertPolicy      : Bool := false
  hasUpdatePolicy      : Bool := false
  hasDeletePolicy      : Bool := false
  hasCrossReadPolicy   : Bool := false
  hasCrossInsertPolicy : Bool := false
  hasCrossUpdatePolicy : Bool := false
  hasCrossDeletePolicy : Bool := false
  hasTransInv          : Bool := false
  readPolicyLabel      : String := ""
  insertPolicyLabel    : String := ""
  updatePolicyLabel    : String := ""
  deletePolicyLabel    : String := ""
deriving Inhabited, Repr

structure DatabaseInfo where
  dbName            : Lean.Name
  shortName         : String
  configConst       : Lean.Name
  ensureSchemaConst : Lean.Name
  snapTypeConst?    : Option Lean.Name := none
  secrets           : Array String
  hasDevFallback    : Bool := false
  isManaged         : Bool := false
  envSpecs          : Qed.Cloud.EnvMap Qed.Cloud.DbEnvSpec := Qed.Cloud.EnvMap.ofDefault (.byoSqlite "")
  tables            : Array DbTableInfo
deriving Inhabited, Repr

initialize databaseRegistry : Lean.SimplePersistentEnvExtension DatabaseInfo (Lean.NameMap DatabaseInfo) ← Qed.Diag.mkNameMapExt (·.dbName)
abbrev lookupDatabase? (env : Lean.Environment) (currNs : Lean.Name) (openDecls : List Lean.OpenDecl) (dbRef : Lean.Name) : Option DatabaseInfo :=
  Qed.Diag.lookupNameMapExt? databaseRegistry env currNs openDecls dbRef (some `config)

structure AuthInfo where
  authName    : Lean.Name
  shortName   : String
  configConst : Lean.Name
  secrets     : Array String := #[]
  spec        : Qed.Auth.OidcAuthSpec := default
deriving Inhabited, Repr

initialize authRegistry : Lean.SimplePersistentEnvExtension AuthInfo (Lean.NameMap AuthInfo) ← Qed.Diag.mkNameMapExt (·.authName)
abbrev lookupAuth? (env : Lean.Environment) (currNs : Lean.Name) (openDecls : List Lean.OpenDecl) (authRef : Lean.Name) : Option AuthInfo :=
  Qed.Diag.lookupNameMapExt? authRegistry env currNs openDecls authRef (some `config)

structure ServiceMethodInfo where
  name          : String
  defConst      : Lean.Name
  minParamCount : Nat
  paramCount    : Nat
  isMonadic     : Bool
  isFallible    : Bool
  takesCtx      : Bool := false
  dbWrite       : Bool := false
  hasCookieOp   : Bool := false
  hasEnsures    : Bool := false
deriving Inhabited, Repr

structure ServiceInfo where
  serviceName      : Lean.Name
  shortName        : String
  secrets          : Array String := #[]
  ownSecrets       : Array String := #[]
  envVars          : Array (String × String × Option String) := #[]
  externalServices : Array (String × String) := #[]
  databases        : Array Lean.Name := #[]
  methods          : Array ServiceMethodInfo := #[]
deriving Inhabited

initialize serviceRegistry : Lean.SimplePersistentEnvExtension ServiceInfo (Lean.NameMap ServiceInfo) ← Qed.Diag.mkNameMapExt (·.serviceName)
initialize failedServiceRegistry : Lean.SimplePersistentEnvExtension Lean.Name (Lean.NameMap Lean.Name) ← Qed.Diag.mkNameMapExt id
abbrev lookupService? (env : Lean.Environment) (currNs : Lean.Name) (openDecls : List Lean.OpenDecl) (svcRef : Lean.Name) : Option ServiceInfo :=
  Qed.Diag.lookupNameMapExt? serviceRegistry env currNs openDecls svcRef (some `_qed_service_marker)

def findNamedArg? (named : Array (String × Lean.Syntax)) (key : String) : Option Lean.Syntax := (named.find? (·.1 == key)).map Prod.snd

section SyntaxHelpers
open Lean

def foldProjTerms {m : Type → Type} [Monad m] [MonadQuotation m] (ref : Syntax) (base : Term) (fs : List Name) : m Term :=
  fs.foldlM (init := base) fun acc f => `(($acc).$(mkIdentFrom ref f):ident)

def mkBoolConj {m : Type → Type} [Monad m] [MonadQuotation m] (terms : Array Term) : m Term :=
  match terms.toList with | [] => `(true) | t :: rest => rest.foldlM (init := t) fun acc x => `($acc && $x)

def resolveAppTargetIdent (env : Environment) (currNs : Name) (id : Ident) : Ident :=
  if env.contains (currNs ++ id.getId ++ `app) || env.contains (id.getId ++ `app) then mkIdentFrom id (id.getId ++ `app) else id

def mkWsDecodeCb {m : Type → Type} [Monad m] [MonadQuotation m] (onOk onStatus : Ident) (mkDec : Ident → m Term) : m Term := do
  let a := mkIdent `_wsMsg
  `(fun $a:ident => match $(← mkDec a):term with | Except.ok v => $onOk v | Except.error e => $onStatus (Qed.SocketStatus.failed e))

end SyntaxHelpers

open Lean Elab Command in
def elabParamTypeAbbrevs (refIdent : Ident) (ownerName fullOwnerName itemName : Name) (suffix : String) (tyTerms : Array Term) : CommandElabM (Array Name) :=
  tyTerms.zipIdx.mapM fun (pTy, i) => do
    let leaf := itemName.appendAfter s!"{suffix}{i}"
    elabCommand (← `(command| abbrev $(mkIdentFrom refIdent (ownerName ++ leaf)) : Type := $pTy))
    return fullOwnerName ++ leaf

open Lean Meta in
simproc_decl qedReduceStrLen (String.length _) := fun e => do
  let some (Expr.lit (Literal.strVal s)) := e.getAppArgs[0]? | return .continue
  let charTy := mkConst ``Char
  let cs := s.toList.foldr (fun c acc => mkApp2 (mkApp (mkConst ``List.cons [0]) charTy) (mkApp (mkConst ``Char.ofNat) (mkNatLit c.toNat)) acc) (mkApp (mkConst ``List.nil [0]) charTy)
  let nExpr := mkNatLit s.length
  return .done { expr := nExpr, proof? := some (← mkEqTrans (mkApp (mkConst ``String.length_ofList) cs) (← mkEqRefl nExpr)) }

end Server
end Qed
