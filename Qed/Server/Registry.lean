import Lean
import Qed.Diag
import Qed.Lang
import Qed.Cloud.Env
import Qed.Auth.Core
import Qed.Field
import Qed.Socket.Basic

namespace Qed

@[simp] theorem QedVal.val_ensured {α : Type} {p : α → Prop} (e : Ensured α p) :
    Qed.Lang.QedVal.val e = Field.val e := rfl

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
deriving Inhabited

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

def lookupServerMethod? (env : Lean.Environment) (currNs : Lean.Name) (openDecls : List Lean.OpenDecl) (callName : Lean.Name) : Option (ServerInfo × ServerMethodInfo) :=
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

inductive ExtWsCodec where | json | proto | text | bytes deriving Inhabited, DecidableEq
inductive ChannelKind where
  | fullstack (serverName : Lean.Name) (serverShort : String) (wsPath : String)
  | external  (serviceName : Lean.Name) (isBinary : Bool) (eventCodec : ExtWsCodec) (sendCodec : ExtWsCodec)
deriving Inhabited, DecidableEq

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
deriving Inhabited

def ChannelInfo.mkDefault (ownerName : Lean.Name) (ownerShort : String) (chName : Lean.Name) (kind : ChannelKind)
    (paramNames paramTypeConsts : Array Lean.Name) (defaultReconnect : Reconnect) : ChannelInfo :=
  let sub (s : String) := ownerName ++ chName.appendAfter s
  { fullName := ownerName ++ chName, ownerName, ownerShort, channelName := chName.toString, kind, paramNames, paramCount := paramNames.size,
    paramTypeConsts, defaultReconnect, eventTypeConst := sub "_Event", keyHelperConst := sub "_key", subHelperConst := sub "_sub", unsubHelperConst := sub "_unsub" }

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

section ReconnectParser
open Lean Qed.Lang

private def parseNatLitArg (stx : Syntax) : MacroM Nat :=
  let u := unwrapParens1 stx
  if u.getKind == ``qedLitNum then pure (⟨u.getArg 0⟩ : TSyntax `num).getNat
  else Macro.throwErrorAt stx "expected a non-negative integer millisecond/retry literal in `reconnect` policy"

private def parseOptNatLitArg (stx : Syntax) : MacroM (Option Nat) :=
  let u := unwrapParens1 stx
  if u.getKind == ``qedIdent && (u.getArg 0).getId == `none then pure none
  else if u.getKind == ``qedCall && (u.getArg 0).getKind == ``qedIdent && ((u.getArg 0).getArg 0).getId == `some then
    let args := (u.getArg 2).getSepArgs
    if args.size == 1 && args[0]!.getKind == ``qedCallArgPos then some <$> parseNatLitArg args[0]![0]
    else Macro.throwErrorAt stx "expected `some(<nat>)` or `<nat>`"
  else some <$> parseNatLitArg u

def parseReconnectExpr (exprStx : Syntax) : MacroM Reconnect := do
  let u := unwrapParens1 exprStx
  if u.getKind == ``qedIdent then
    match (u.getArg 0).getId.eraseMacroScopes with
    | `off | `none => return .off | `default | `backoff => return .defaultPolicy
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
          let (initMs, maxMs) := (← parseNatLitArg pos[0]!, ← parseNatLitArg pos[1]!)
          if maxMs < initMs then Macro.throwErrorAt u s!"`reconnect backoff({initMs}, {maxMs})` requires `initialMs <= maxMs`"
          return .backoff initMs maxMs (← getMax 2)
        Macro.throwErrorAt u "`reconnect backoff(...)` expects `backoff(initialMs, maxMs)` or `backoff(initialMs, maxMs, maxRetries)`"
    | _ => Macro.throwErrorAt u s!"unknown `reconnect` policy `{fn}`; use `off`, `fixed(...)`, or `backoff(...)`"
  else Macro.throwErrorAt u "expected `reconnect` policy: `off`, `fixed(ms[, max])`, or `backoff(initMs, maxMs[, max])`"

def Reconnect.toSyntaxTerm : Reconnect → MacroM Term
  | .off => `(Qed.Reconnect.off) | .fixed d m? => `(Qed.Reconnect.fixed $(quote d) $(quote m?))
  | .backoff i mx m? => `(Qed.Reconnect.backoff $(quote i) $(quote mx) $(quote m?))

end ReconnectParser

namespace Server

structure ExternalServiceInfo where
  serviceName : Lean.Name
  baseOrigin  : String
  secrets     : Array String
  methods     : Array Lean.Name
deriving Inhabited
initialize externalRegistry : Lean.SimplePersistentEnvExtension ExternalServiceInfo (Lean.NameMap ExternalServiceInfo) ← Qed.Diag.mkNameMapExt (·.serviceName)

def exprCallsOld (stx : Lean.Syntax) : Bool :=
  Qed.Lang.stxAny (fun s => s.getKind == ``Qed.Lang.qedCall && (s.getArg 0).getKind == ``Qed.Lang.qedIdent && ((s.getArg 0).getArg 0).getId.eraseMacroScopes == `old) stx

structure DbEncKeyInfo where
  keyEnv    : String
  fallback? : Option String := none
  isBytes   : Bool := false
  prevKeys  : List (String × Option String) := []
deriving Inhabited

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
deriving Inhabited

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
deriving Inhabited

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
deriving Inhabited
initialize databaseRegistry : Lean.SimplePersistentEnvExtension DatabaseInfo (Lean.NameMap DatabaseInfo) ← Qed.Diag.mkNameMapExt (·.dbName)
abbrev lookupDatabase? (env : Lean.Environment) (currNs : Lean.Name) (openDecls : List Lean.OpenDecl) (dbRef : Lean.Name) : Option DatabaseInfo :=
  Qed.Diag.lookupNameMapExt? databaseRegistry env currNs openDecls dbRef (some `config)

structure AuthInfo where
  authName    : Lean.Name
  shortName   : String
  configConst : Lean.Name
  secrets     : Array String := #[]
  spec        : Qed.Auth.OidcAuthSpec := default
deriving Inhabited
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
deriving Inhabited

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

structure FullstackInfo where
  fullstackName : Lean.Name
  serverName    : Lean.Name
  title         : String
deriving Inhabited
initialize fullstackRegistry : Lean.SimplePersistentEnvExtension FullstackInfo (Lean.NameMap FullstackInfo) ← Qed.Diag.mkNameMapExt (·.fullstackName)
def findNamedArg? (named : Array (String × Lean.Syntax)) (key : String) : Option Lean.Syntax := (named.find? (·.1 == key)).map Prod.snd

section SyntaxHelpers
open Lean Elab Command

@[noinline, nospecialize] def foldProjTerms {m : Type → Type} [Monad m] [MonadQuotation m] (ref : Syntax) (base : Term) (fs : List Name) : m Term :=
  fs.foldlM (init := base) fun acc f => `(($acc).$(mkIdentFrom ref f):ident)
@[noinline, nospecialize] def mkBoolConj {m : Type → Type} [Monad m] [MonadQuotation m] (terms : Array Term) : m Term :=
  match terms.toList with | [] => `(true) | t :: rest => rest.foldlM (init := t) fun acc x => `($acc && $x)
def resolveAppTargetIdent (env : Environment) (currNs : Name) (id : Ident) : Ident :=
  if env.contains (currNs ++ id.getId ++ `app) || env.contains (id.getId ++ `app) then mkIdentFrom id (id.getId ++ `app) else id

@[noinline] def errAt {α : Type} (ref : Syntax) (msg : String) : CommandElabM α := throwErrorAt ref msg
@[noinline] def runPQ {α : Type} (k : PureQuotM α) : CommandElabM α := runPureQuot k
@[noinline] def liftMacroCmd {α : Type} (m : MacroM α) : CommandElabM α := liftMacroM m
@[noinline] def foldlPQ {α β : Type} (xs : Array α) (init : β) (f : β → α → PureQuotM β) : PureQuotM β :=
  let rec go : Nat → β → PureQuotM β | 0, acc => pure acc | r + 1, acc => do let i := xs.size - (r + 1); if h : i < xs.size then go r (← f acc xs[i]) else pure acc
  go xs.size init
@[noinline] def foldrPQ {α β : Type} (xs : Array α) (init : β) (f : α → β → PureQuotM β) : PureQuotM β :=
  let rec go : Nat → β → PureQuotM β | 0, acc => pure acc | j + 1, acc => do if h : j < xs.size then go j (← f xs[j] acc) else pure acc
  go xs.size init
@[noinline] def mapPQ {α β : Type} (xs : Array α) (f : α → PureQuotM β) : PureQuotM (Array β) := foldlPQ xs (Array.mkEmpty xs.size) fun acc x => return acc.push (← f x)
@[noinline] def mapIdxPQ {α β : Type} (xs : Array α) (f : α → Nat → PureQuotM β) : PureQuotM (Array β) :=
  let rec go : Nat → Array β → PureQuotM (Array β) | 0, acc => pure acc | r + 1, acc => do let i := xs.size - (r + 1); if h : i < xs.size then go r (acc.push (← f xs[i] i)) else pure acc
  go xs.size (Array.mkEmpty xs.size)
@[noinline] def foldlCmd {α β : Type} (xs : Array α) (init : β) (f : β → α → CommandElabM β) : CommandElabM β :=
  let rec go : Nat → β → CommandElabM β | 0, acc => pure acc | r + 1, acc => do let i := xs.size - (r + 1); if h : i < xs.size then go r (← f acc xs[i]) else pure acc
  go xs.size init
@[noinline] def mapCmd {α β : Type} (xs : Array α) (f : α → CommandElabM β) : CommandElabM (Array β) := foldlCmd xs (Array.mkEmpty xs.size) fun acc x => return acc.push (← f x)
@[noinline] def elabPureCmd (k : PureQuotM (TSyntax `command)) : CommandElabM Unit := do elabCommand (← runPQ k)
@[noinline] def elabPureCmds (k : PureQuotM (Array (TSyntax `command))) : CommandElabM Unit := do foldlCmd (← runPQ k) () fun _ c => elabCommand c
@[noinline] def noUnusedVarsPure (cmd : TSyntax `command) : PureQuotM (TSyntax `command) := `(command| set_option linter.unusedVariables false in $cmd)
@[noinline] def mkMarkerThmPure (id : Ident) : PureQuotM (TSyntax `command) := `(command| theorem $id : True := True.intro)
@[noinline] def mkStrArrDefPure (id : Ident) (xs : Array String) : PureQuotM (TSyntax `command) := do
  let lits : Array Term := xs.map (Syntax.mkStrLit ·); `(command| @[noinline] def $id : Array String := #[$[$lits],*])
@[noinline] def mkWsDecodeCb (onOk onStatus : Ident) (mkDec : Ident → PureQuotM Term) : PureQuotM Term := do
  let a := mkIdent `_wsMsg; `(fun $a:ident => match $(← mkDec a):term with | Except.ok v => $onOk v | Except.error e => $onStatus (Qed.SocketStatus.failed e))

@[noinline] def elabParamTypeAbbrevs (refIdent : Ident) (ownerName fullOwnerName itemName : Name) (suffix : String) (tyTerms : Array Term) : CommandElabM (Array Name) := do
  elabPureCmds <| mapIdxPQ tyTerms fun pTy i => `(command| abbrev $(mkIdentFrom refIdent (ownerName ++ itemName.appendAfter s!"{suffix}{i}")) : Type := $pTy)
  return (Array.range tyTerms.size).map fun i => fullOwnerName ++ itemName.appendAfter s!"{suffix}{i}"

structure WsClientSpec where
  refIdent    : Ident
  ownerName   : Name
  chName      : Name
  pIdents     : Array Ident
  pTyTerms    : Array Term
  evTyTerm?   : Option Term := none
  joinAbbrev? : Option Term := none
  joinCbTy    : Term
  wireEvTy    : Term
  keyBody     : Term
  subBody     : Term
  unsubBody   : Term
  sendSpec?   : Option (Array Ident × Array Term × Term) := none

@[noinline] def elabWsClientCommon (s : WsClientSpec) : CommandElabM Unit := elabPureCmds do
  let mkCh (suf : String) := mkIdentFrom s.refIdent (s.ownerName ++ s.chName.appendAfter suf)
  let (slotId, recId, onJoinId, onMsgId, onStatusId, cmdTy, pIds, pTys) := (mkIdent `slot, mkIdent `rec, mkIdent `onJoin, mkIdent `onMsg, mkIdent `onStatus, mkCIdent `Qed.Cmd, s.pIdents, s.pTyTerms)
  let mut cmds : Array (TSyntax `command) := #[]
  if let some evTy := s.evTyTerm? then cmds := cmds.push (← `(command| abbrev $(mkCh "_Event") : Type := $evTy))
  if let some jTy := s.joinAbbrev? then cmds := cmds.push (← `(command| abbrev $(mkCh "_Join") : Type := $jTy))
  cmds := cmds ++ #[
    ← `(command| def $(mkCh "_key") $[($pIds:ident : $pTys:term)]* : String := $(s.keyBody)),
    ← noUnusedVarsPure (← `(command| def $(mkCh "_sub") {msg : Type} ($slotId:ident : String) $[($pIds:ident : $pTys:term)]*
      ($recId:ident : Qed.Reconnect) ($onJoinId:ident : $(s.joinCbTy) → msg) ($onMsgId:ident : $(s.wireEvTy) → msg) ($onStatusId:ident : Qed.SocketStatus → msg) : $cmdTy msg := $(s.subBody))),
    ← `(command| def $(mkCh "_unsub") {msg : Type} ($slotId:ident : String) : $cmdTy msg := $(s.unsubBody))]
  if let some (spIds, spTys, sendBody) := s.sendSpec? then
    cmds := cmds.push (← `(command| def $(mkCh "_send") {msg : Type} ($slotId:ident : String) $[($spIds:ident : $spTys:term)]* : $cmdTy msg := $sendBody))
  return cmds

end SyntaxHelpers

open Lean Meta in
simproc_decl qedReduceStrLen (String.length _) := fun e => do
  let some (Expr.lit (Literal.strVal s)) := e.getAppArgs[0]? | return .continue
  let charTy := mkConst ``Char
  let cs := s.toList.foldr (fun c acc => mkApp2 (mkApp (mkConst ``List.cons [0]) charTy) (mkApp (mkConst ``Char.ofNat) (mkNatLit c.toNat)) acc) (mkApp (mkConst ``List.nil [0]) charTy)
  let nExpr := mkNatLit s.length
  return .done { expr := nExpr, proof? := some (← mkEqTrans (mkApp (mkConst ``String.length_ofList) cs) (← mkEqRefl nExpr)) }

end Server
end Qed
