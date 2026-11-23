import Lean
import Qed.Runtime.Cmd
import Qed.Server.Registry
import Qed.Server.Core
import Qed.Server.Syntax

namespace Qed.Server

/-! ## Runtime Wire Execution Helpers for `external` & `Webhook` -/

private def mergeHeaders (defaults custom : List (String × String)) : List (String × String) :=
  let sanitizedCustom := custom.map fun (k, v) => (sanitizeHeader k, sanitizeHeader v)
  let customLower := sanitizedCustom.map fun (k, _) => k.toLower
  let keptDefaults := defaults.filter fun (k, _) => !customLower.contains k.toLower
  keptDefaults ++ sanitizedCustom

private def checkHttpOk (resp : OutboundResp) : Except ApiError OutboundResp :=
  if 200 ≤ resp.status && resp.status < 300 then
    .ok resp
  else
    let msg := (String.fromUTF8? resp.body).getD "external HTTP error"
    .error { code := resp.status.toNat, message := if msg.isEmpty then s!"HTTP {resp.status}" else msg }

@[specialize]
def execExternalRaw {m : Type → Type} [Monad m] [MonadServer m]
    (serviceName baseOrigin method : String)
    (parts : List PathPart) (query : List (String × QueryVal))
    (defaultHeaders customHeaders : List (String × String))
    (body : ByteArray) (auth : AuthSpec) : m (Except ApiError OutboundResp) := do
  match buildExternalSuffix parts query with
  | .error e => return .error e
  | .ok sfx  =>
      let req : OutboundReq := {
        serviceName
        baseOrigin
        method
        pathAndQuery := "/" ++ sfx
        headers := mergeHeaders defaultHeaders customHeaders
        body
        auth
        ssrfGuard := false
      }
      let res ← MonadServer.httpCall req
      return res.bind checkHttpOk

instance {σ : Type} (svc base method : String) (parts : List PathPart) (query : List (String × QueryVal))
    (defHdrs custHdrs : List (String × String)) (body : ByteArray) (auth : AuthSpec) :
    SafeIO (execExternalRaw (m := ThreadProg σ) svc base method parts query defHdrs custHdrs body auth) where
  noAtomic := by
    unfold execExternalRaw
    cases buildExternalSuffix parts query with
    | error e => exact .pure (Except.error e)
    | ok sfx  => exact .io (.httpCall _) _ fun res => .pure (res.bind checkHttpOk)

@[specialize]
def decodeRespBytes (res : Except ApiError OutboundResp) : Except ApiError Bytes :=
  res.map (·.body)

@[specialize]
def decodeRespUnit (res : Except ApiError OutboundResp) : Except ApiError Unit :=
  res.map fun _ => ()

@[specialize]
def decodeRespString (res : Except ApiError OutboundResp) : Except ApiError String :=
  res.bind fun r => (String.fromUTF8? r.body).elim (.error (ApiError.internal "external API returned invalid UTF-8")) .ok

@[specialize]
def decodeRespProto {α : Type} [FromProto α] (res : Except ApiError OutboundResp) : Except ApiError α :=
  res.bind fun r => (Proto.decode (α := α) r.body).mapError fun e => ApiError.internal s!"external protobuf decode failed: {e}"

@[specialize]
def decodeRespJson {α : Type} [FromJson α] (res : Except ApiError OutboundResp) : Except ApiError α :=
  (decodeRespString res).bind fun raw =>
    ((Json.parse raw 128).bind (FromJson.fromJson (α := α))).mapError fun e =>
      ApiError.internal s!"external JSON decode failed: {e}"

/-! ## Built-In SSRF-Guarded Dynamic `Webhook` Client -/

namespace Webhook

private def splitHttpsOriginAndPath (raw : String) : String × String :=
  let afterScheme := String.ofList (raw.toList.drop 8)
  match afterScheme.splitOn "/" with
  | []        => (raw, "/")
  | host :: rest =>
      let origin := "https://" ++ host
      let path := if rest.isEmpty then "/" else "/" ++ String.intercalate "/" rest
      (origin, path)

@[specialize]
private def postRaw {m : Type → Type} [Monad m] [MonadServer m]
    (url : WebhookUrl) (headers : List (String × String)) (body : Bytes) : m (Except ApiError OutboundResp) := do
  let (origin, path) := splitHttpsOriginAndPath url.raw
  let res ← MonadServer.httpCall {
    serviceName := "Webhook", baseOrigin := origin, method := "POST", pathAndQuery := path
    headers, body, auth := .none, ssrfGuard := true
  }
  return res.bind checkHttpOk

@[specialize]
def postJson {Payload Resp : Type} {m : Type → Type} [Monad m] [MonadServer m]
    [ToJson Payload] [FromJson Resp]
    (url : WebhookUrl) (payload : Payload) : m (Except ApiError Resp) := do
  decodeRespJson <$> postRaw url [("Content-Type", "application/json"), ("Accept", "application/json")]
    (Json.render (toJson payload)).toUTF8

@[specialize]
def postBytes {m : Type → Type} [Monad m] [MonadServer m]
    (url : WebhookUrl) (mime : String) (body : Bytes) : m (Except ApiError Bytes) := do
  decodeRespBytes <$> postRaw url [("Content-Type", sanitizeHeader mime)] body

instance {σ Payload Resp : Type} [ToJson Payload] [FromJson Resp]
    (url : WebhookUrl) (payload : Payload) :
    SafeIO (postJson (Payload := Payload) (Resp := Resp) (m := ThreadProg σ) url payload) where
  noAtomic := by unfold postJson postRaw; exact .io (.httpCall _) _ fun res => .pure (decodeRespJson (res.bind checkHttpOk))

instance {σ : Type} (url : WebhookUrl) (mime : String) (body : Bytes) :
    SafeIO (postBytes (m := ThreadProg σ) url mime body) where
  noAtomic := by unfold postBytes postRaw; exact .io (.httpCall _) _ fun res => .pure (decodeRespBytes (res.bind checkHttpOk))

end Webhook

/-! ## `external` Command Elaborator -/

private inductive UrlSegSpec where
  | lit (s : String)
  | singleParam (name : String)
  | multiParam (name : String)

private inductive QueryValSpec where
  | lit (s : String)
  | param (name : String)

section ExternalElab
open Lean Elab Command

private def parseUrlTemplate (ref : Lean.Syntax) (tmpl : String) :
    CommandElabM (Array UrlSegSpec × Array (String × QueryValSpec) × Array String) := do
  if tmpl.contains '#' then
    throwErrorAt ref "external endpoint URL template must not contain `#` fragments"
  if !tmpl.startsWith "/" then
    throwErrorAt ref s!"external endpoint path `{tmpl}` must start with `/`"
  let qParts := tmpl.splitOn "?"
  if qParts.length > 2 then
    throwErrorAt ref s!"external endpoint path `{tmpl}` has multiple `?` query delimiters"
  let rawPath := qParts.headD ""
  let rawQuery := qParts.getD 1 ""
  let mut segSpecs : Array UrlSegSpec := #[]
  let phRef ← IO.mkRef (#[] : Array String)
  let addPlaceholder (raw kindDesc : String) : CommandElabM (String × Bool) := do
    let rest := String.ofList (raw.toList.drop 1)
    let isMulti := rest.endsWith "*"
    let pname := if isMulti then String.ofList (rest.toList.take (rest.length - 1)) else rest
    if pname.isEmpty then throwErrorAt ref s!"empty {kindDesc} placeholder in `{tmpl}`"
    if (← phRef.get).contains pname then throwErrorAt ref s!"duplicate placeholder `:{pname}` in `{tmpl}`"
    phRef.modify (·.push pname)
    return (pname, isMulti)
  for seg in (rawPath.splitOn "/").filter (· != "") do
    if seg.startsWith ":" then
      let (pname, isMulti) ← addPlaceholder seg "`:`"
      segSpecs := segSpecs.push (if isMulti then .multiParam pname else .singleParam pname)
    else
      if seg == "." || seg == ".." || !seg.toList.all isSafeSegChar then
        throwErrorAt ref s!"invalid static URL path segment `{seg}` in `{tmpl}`"
      segSpecs := segSpecs.push (.lit seg)
  let mut querySpecs : Array (String × QueryValSpec) := #[]
  if !rawQuery.isEmpty then
    for pair in (rawQuery.splitOn "&").filter (· != "") do
      match pair.splitOn "=" with
      | [k, v] =>
          if k.isEmpty then throwErrorAt ref s!"empty query parameter key in `{tmpl}`"
          if v.startsWith ":" then
            let (pname, _) ← addPlaceholder v "query"
            querySpecs := querySpecs.push (k, .param pname)
          else querySpecs := querySpecs.push (k, .lit v)
      | [k] => querySpecs := querySpecs.push (k, .lit "")
      | _ => throwErrorAt ref s!"malformed query parameter `{pair}` in `{tmpl}`"
  return (segSpecs, querySpecs, ← phRef.get)

private structure ParsedExtParam where
  ref        : Lean.Syntax
  headerKey? : Option String
  ident      : Lean.Ident
  ty         : Qed.Lang.LoweredQedType

private def parseExternalClauses (svcIdent : Ident) (svcName : Name) (clauses : Array Syntax) :
    CommandElabM (String × AuthSpec × Array Syntax × Array Syntax) := do
  let mut baseOrigin? : Option (Syntax × String) := none
  let mut authSpec : AuthSpec := .none
  let mut hasAuth := false
  let mut epClauses : Array Syntax := #[]
  let mut wsClauses : Array Syntax := #[]
  for c in clauses do
    let k := c.getKind
    if k == ``extBaseClause then
      if baseOrigin?.isSome then
        throwErrorAt c s!"duplicate `base` clause in `external {svcName}`"
      let strStx : TSyntax `str := ⟨(c.getArg 1)⟩
      let rawBase := strStx.getString
      let trimmed := if rawBase.endsWith "/" then
        String.ofList (rawBase.toList.take (rawBase.length - 1))
      else rawBase
      unless isValidWsBaseOrigin trimmed do
        throwErrorAt c s!"invalid `base` URL `{rawBase}`: expected pinned `https://`, `http://`, `wss://`, or `ws://` origin without `?`, `#`, `@`, or `\\`"
      baseOrigin? := some (c, trimmed)
    else if k == ``extAuthBearer || k == ``extAuthHeader || k == ``extAuthGcp then
      if hasAuth then throwErrorAt c s!"duplicate `auth` clause in `external {svcName}`"
      hasAuth := true
      let checkEnv (stx : Syntax) : CommandElabM String := do
        let v := (⟨stx⟩ : TSyntax `str).getString
        unless isValidEnvVarName v do
          throwErrorAt stx s!"invalid secret environment variable name `{v}`: must be non-empty and contain only ASCII letters, digits, or `_`"
        return v
      if k == ``extAuthBearer then
        authSpec := .bearerSecret (← checkEnv (c.getArg 5))
      else if k == ``extAuthHeader then
        let hdrName := (⟨(c.getArg 3)⟩ : TSyntax `str).getString
        if hdrName.isEmpty then throwErrorAt (c.getArg 3) "header name cannot be empty"
        authSpec := .headerSecret hdrName (← checkEnv (c.getArg 7))
      else
        let scope := if (c.getArg 7).getNumArgs == 2 then (⟨((c.getArg 7).getArg 1)⟩ : TSyntax `str).getString
                     else "https://www.googleapis.com/auth/cloud-platform"
        authSpec := .gcpServiceAccount (← checkEnv (c.getArg 5)) scope
    else if k == ``extEndpointClause then
      epClauses := epClauses.push c
    else if k == ``extWsClause then
      wsClauses := wsClauses.push c
    else
      throwErrorAt c "unexpected clause in `external` block"
  let some (baseRef, baseOrigin) := baseOrigin?
    | throwErrorAt svcIdent s!"`external {svcName}` must declare `base \"https://...\"` or `base \"wss://...\"`"
  if epClauses.isEmpty && wsClauses.isEmpty then
    throwErrorAt svcIdent s!"`external {svcName}` must declare at least one HTTP endpoint or `ws` channel"
  if !epClauses.isEmpty && !isValidBaseOrigin baseOrigin then
    throwErrorAt baseRef s!"`external {svcName}` declares HTTP endpoints, so `base` must use `https://` or `http://` (got `{baseOrigin}`)"
  if !wsClauses.isEmpty && hasAuth then
    throwErrorAt svcIdent s!"`external {svcName}` declares client-usable `ws` channels and cannot attach server `auth` secrets; split server-authenticated HTTP endpoints into a separate `external` block"
  return (baseOrigin, authSpec, epClauses, wsClauses)

private def buildExternalCallCmds (fullFnId baseId : Ident) (svcStrLit verbLit : StrLit)
    (pIdents : Array Ident) (pTyTerms : Array Term) (retPayloadTerm : Term)
    (pathTerms queryTerms defHdrTerms customHdrTerms : Array Term)
    (bodyTerm authTerm decodeCall : Term) : CommandElabM Unit := do
  let fnCmd ← `(command|
    @[specialize]
    def $fullFnId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m]
        $[($pIdents:ident : $pTyTerms:term)]* : m (Except Qed.Server.ApiError $retPayloadTerm) := do
      let rawRes ← Qed.Server.execExternalRaw $svcStrLit $baseId $verbLit
        [$[$pathTerms],*] [$[$queryTerms],*]
        [$[$defHdrTerms],*] [$[$customHdrTerms],*]
        $bodyTerm $authTerm
      return $decodeCall)
  elabCommand fnCmd
  let fullFnCall ← Qed.Lang.mkAppTerms (← `($fullFnId)) (pIdents.map (⟨·.raw⟩))
  let safeInstCmd ← `(command|
    instance {_σ : Type} $[($pIdents:ident : $pTyTerms:term)]* :
        Qed.Server.SafeIO ($fullFnCall : Qed.Server.ThreadProg _σ (Except Qed.Server.ApiError $retPayloadTerm)) where
      noAtomic := by
        unfold $fullFnId
        exact (inferInstance : Qed.Server.SafeIO _).noAtomic)
  elabCommand safeInstCmd

private def lowerUrlParts (ref : Syntax) (segSpecs : Array UrlSegSpec)
    (querySpecs : Array (String × QueryValSpec)) (paramIdents : Array Ident) :
    CommandElabM (Array Term × Array Term) := do
  let paramSegTerm (pn : String) : CommandElabM Term := do
    let some pid := paramIdents.find? (·.getId.toString == pn)
      | throwErrorAt ref "internal missing URL param"
    `(Qed.RouteParam.toSeg $pid)
  let pathTerms ← segSpecs.mapM fun
    | .lit s          => `(Qed.Server.PathPart.lit $(Syntax.mkStrLit s))
    | .singleParam pn => do `(Qed.Server.PathPart.seg $(← paramSegTerm pn))
    | .multiParam pn  => do `(Qed.Server.PathPart.multiSeg $(← paramSegTerm pn))
  let queryTerms ← querySpecs.mapM fun (qk, qv) => do
    let qkLit := Syntax.mkStrLit qk
    match qv with
    | .lit s    => `(($qkLit, Qed.Server.QueryVal.lit $(Syntax.mkStrLit s)))
    | .param pn => do `(($qkLit, Qed.Server.QueryVal.param $(← paramSegTerm pn)))
  return (pathTerms, queryTerms)

private def parseTypedParams (ctxLabel : String) (rawParams : Array Syntax)
    (allowHeader := false) (paramKind := "parameter") : CommandElabM (Array ParsedExtParam) := do
  let mut out : Array ParsedExtParam := #[]
  let mut seen : Array String := #[]
  for rp in rawParams do
    let pk := rp.getKind
    let (hk?, pid, tyNode) ←
      if allowHeader && pk == ``extParamHeader then
        pure (some (⟨rp.getArg 2⟩ : TSyntax `str).getString, (⟨rp.getArg 4⟩ : Ident), rp.getArg 6)
      else if !allowHeader || pk == ``extParamPlain then
        pure (none, (⟨rp.getArg 0⟩ : Ident), rp.getArg 2)
      else throwErrorAt rp "invalid endpoint parameter"
    let pstr := pid.getId.toString
    if seen.contains pstr then throwErrorAt pid s!"duplicate {paramKind} `{pstr}` in {ctxLabel}"
    seen := seen.push pstr
    let pty ← liftMacroM <| lowerSrvType tyNode false s!"{paramKind} `{pstr}`"
    out := out.push { ref := rp, headerKey? := hk?, ident := pid, ty := pty }
  return out

private def classifyExtWsCodec (ty : Qed.Lang.LoweredQedType) : Qed.ExtWsCodec :=
  if ty.isProto then .proto
  else
    let b := ty.baseName.toString
    if ty.mods.isEmpty && (b == "Bytes" || b == "ByteArray") then .bytes
    else if ty.mods.isEmpty && b == "String" then .text
    else .json

private def isUnitExtType (ty : Qed.Lang.LoweredQedType) : Bool :=
  !ty.isProto && ty.mods.isEmpty && ty.baseName == `Unit

private def lowerExtBodyAndDecode (bodyParam? : Option ParsedExtParam) (retTy : Qed.Lang.LoweredQedType) :
    CommandElabM (Term × Array Term × Term × Term) := do
  let retPayloadTerm := retTy.term
  let (acceptHdr, decodeCall) ←
    if isUnitExtType retTy then pure (none, ← `(Qed.Server.decodeRespUnit rawRes))
    else match classifyExtWsCodec retTy with
      | .proto => pure (some ("Accept", "application/x-protobuf"), ← `(Qed.Server.decodeRespProto (α := $retPayloadTerm) rawRes))
      | .bytes => pure (none, ← `(Qed.Server.decodeRespBytes rawRes))
      | .text  => pure (none, ← `(Qed.Server.decodeRespString rawRes))
      | .json  => pure (some ("Accept", "application/json"), ← `(Qed.Server.decodeRespJson (α := $retPayloadTerm) rawRes))
  let (bodyTerm, ctHdr) ← match bodyParam? with
    | none => pure (← `(ByteArray.empty), (none : Option (String × String)))
    | some bp =>
        if isUnitExtType bp.ty then pure (← `(ByteArray.empty), none)
        else match classifyExtWsCodec bp.ty with
          | .proto => pure (← `(Qed.Proto.encode $(bp.ident)), some ("Content-Type", "application/x-protobuf"))
          | .bytes => pure (← `(($(bp.ident) : ByteArray)), some ("Content-Type", "application/octet-stream"))
          | .text | .json => pure (← `((Qed.Json.render (Qed.toJson $(bp.ident))).toUTF8), some ("Content-Type", "application/json"))
  let defHdrTerms ← (#[ctHdr, acceptHdr].filterMap id).mapM fun (k, v) =>
    `(($(Syntax.mkStrLit k), $(Syntax.mkStrLit v)))
  return (bodyTerm, defHdrTerms, retPayloadTerm, decodeCall)

private def elabExternalEndpoint (svcName : Name) (svcStrLit : StrLit) (baseId : Ident)
    (authTerm : Term) (methodNames : Array Name) (ep : Syntax) : CommandElabM Name := do
  let httpVerbRaw := (ep.getArg 0).getId.toString.toUpper
  let urlTmpl := (⟨(ep.getArg 1)⟩ : TSyntax `str).getString
  let fnIdent : Ident := ⟨(ep.getArg 2)⟩
  let fnName := fnIdent.getId
  if methodNames.contains fnName then
    throwErrorAt fnIdent s!"duplicate endpoint `{fnName}` in `external {svcName}`"
  let parsedParams ← parseTypedParams s!"endpoint `{fnName}`" (ep.getArg 4).getSepArgs (allowHeader := true)
  let retTy ← liftMacroM <| lowerSrvType (ep.getArg 7) false
    "external endpoint return types (external calls are automatically fallible at `await`; write `-> T` instead of `-> T!`)"
  let (segSpecs, querySpecs, placeholders) ← parseUrlTemplate (ep.getArg 1) urlTmpl
  for ph in placeholders do
    unless parsedParams.any (fun p => p.headerKey?.isNone && p.ident.getId.toString == ph) do
      throwErrorAt (ep.getArg 1) s!"URL placeholder `:{ph}` has no matching parameter `{ph}` in `{fnName}`"
  let mut bodyParam? : Option ParsedExtParam := none
  for p in parsedParams do
    if p.headerKey?.isNone && !placeholders.contains p.ident.getId.toString then
      if httpVerbRaw == "GET" || httpVerbRaw == "DELETE" then
        throwErrorAt p.ref s!"parameter `{p.ident.getId}` on `{httpVerbRaw}` endpoint `{fnName}` is not referenced as `:{p.ident.getId}` in `{urlTmpl}`"
      if let some prev := bodyParam? then
        throwErrorAt p.ref s!"endpoint `{fnName}` has multiple request body parameters (`{prev.ident.getId}` and `{p.ident.getId}`); bundle them into a `schema` type"
      bodyParam? := some p
  let pIdents := parsedParams.map (·.ident)
  let pTyTerms := parsedParams.map (·.ty.term)
  let urlParamIdents := (parsedParams.filter (·.headerKey?.isNone)).map (·.ident)
  let (pathTerms, queryTerms) ← lowerUrlParts (ep.getArg 1) segSpecs querySpecs urlParamIdents
  let customHdrTerms ← (parsedParams.filterMap fun p => p.headerKey?.map (·, p.ident)).mapM fun (hk, pid) =>
    `(($(Syntax.mkStrLit hk), Qed.RouteParam.toSeg $pid))
  let (bodyTerm, defHdrTerms, retPayloadTerm, decodeCall) ← lowerExtBodyAndDecode bodyParam? retTy
  let fullFnId := mkIdentFrom fnIdent (svcName ++ fnName)
  buildExternalCallCmds fullFnId baseId svcStrLit (Syntax.mkStrLit httpVerbRaw)
    pIdents pTyTerms retPayloadTerm pathTerms queryTerms defHdrTerms customHdrTerms
    bodyTerm authTerm decodeCall
  return fnName

private structure ParsedExtWsClauses where
  reqExprs     : Array Lean.Syntax
  sendParams   : Array ParsedExtParam
  sendReqExprs : Array Lean.Syntax
  hasSend      : Bool
  recPolicy    : Qed.Reconnect

private def parseExtWsSubClauses (chName : Name) (optBody : Syntax) :
    CommandElabM ParsedExtWsClauses := do
  let mut reqExprs : Array Syntax := #[]
  let mut sendParams : Array ParsedExtParam := #[]
  let mut sendReqExprs : Array Syntax := #[]
  let mut hasSend := false
  let mut recPolicy : Qed.Reconnect := .defaultPolicy
  let mut hasRec := false
  if optBody.getNumArgs == 2 then
    for sub in (optBody.getArg 1).getArgs do
      let sk := sub.getKind
      if sk == ``extWsReqClause then
        reqExprs := reqExprs ++ ((sub.getArg 0).getArg 1).getSepArgs
      else if sk == ``extWsReconnectClause then
        if hasRec then throwErrorAt sub s!"duplicate `reconnect` clause in `ws {chName}`"
        hasRec := true
        recPolicy ← liftMacroM <| Qed.parseReconnectExpr (sub.getArg 1)
      else if sk == ``extWsSendClause then
        if hasSend then throwErrorAt sub s!"duplicate `send` clause in `ws {chName}`"
        hasSend := true
        sendParams ← parseTypedParams s!"`ws {chName}`" (sub.getArg 2).getSepArgs (paramKind := "send parameter")
        if (sub.getArg 4).getNumArgs == 2 then
          sendReqExprs := ((sub.getArg 4).getArg 1).getArgs.flatMap fun srl => (srl.getArg 1).getSepArgs
      else
        throwErrorAt sub s!"unexpected clause in `ws {chName}`"
  return { reqExprs, sendParams, sendReqExprs, hasSend, recPolicy }

private def emitExtWsSubAndUnsub (chIdent baseId : Ident) (svcName chName : Name)
    (pIdents : Array Ident) (pTyTerms : Array Term) (evTyTerm : Term)
    (evCodec : Qed.ExtWsCodec) (isBinary : Bool)
    (pathTerms queryTerms : Array Term) : CommandElabM Unit := do
  let keyId := mkIdentFrom chIdent (svcName ++ chName.appendAfter "_key")
  elabCommand (← `(command|
    def $keyId $[($pIdents:ident : $pTyTerms:term)]* : String :=
      (Qed.Server.buildExternalWsUrl $baseId [$[$pathTerms],*] [$[$queryTerms],*]).toOption.getD ""))
  let (subId, slotId, recId, onJoinId, onMsgId, onStatusId) :=
    (mkIdentFrom chIdent (svcName ++ chName.appendAfter "_sub"),
     mkIdent `slot, mkIdent `rec, mkIdent `onJoin, mkIdent `onMsg, mkIdent `onStatus)
  let keyApp ← Qed.Lang.mkAppTerms keyId (pIdents.map (⟨·.raw⟩))
  let isBinTerm : Term := quote isBinary
  let mkUnexpected (kind : String) : CommandElabM Term :=
    `(fun _ => $onStatusId (Qed.SocketStatus.failed $(Syntax.mkStrLit s!"unexpected {kind} WebSocket frame")))
  let mkDecodeCb := mkWsDecodeCb onMsgId onStatusId
  let (onTextTerm, onBytesTerm) ← match evCodec with
    | .text  => pure (← `($onMsgId), ← mkUnexpected "binary")
    | .json  => pure (← mkDecodeCb fun r => `((Qed.Json.parse $r 128).bind (Qed.FromJson.fromJson (α := $evTyTerm))), ← mkUnexpected "binary")
    | .bytes => pure (← mkUnexpected "text", ← `($onMsgId))
    | .proto => pure (← mkUnexpected "text", ← mkDecodeCb fun bs => `(Qed.Proto.decode (α := $evTyTerm) $bs))
  elabCommand (← `(command|
    set_option linter.unusedVariables false in
    def $subId {msg : Type} ($slotId:ident : String) $[($pIdents:ident : $pTyTerms:term)]*
        ($recId:ident : Qed.Reconnect) ($onJoinId:ident : Unit → msg) ($onMsgId:ident : $evTyTerm → msg)
        ($onStatusId:ident : Qed.SocketStatus → msg) : Qed.Cmd msg :=
      let url := $keyApp
      if url.isEmpty then Qed.Cmd.none
      else Qed.Cmd.wsExtOpen $slotId url $isBinTerm $recId $onJoinId $onTextTerm $onBytesTerm $onStatusId))
  let unsubId := mkIdentFrom chIdent (svcName ++ chName.appendAfter "_unsub")
  elabCommand (← `(command|
    def $unsubId {msg : Type} ($slotId:ident : String) : Qed.Cmd msg :=
      Qed.Cmd.wsExtClose $slotId))

private structure ExtWsSendInfo where
  sendCodec           : Qed.ExtWsCodec := .json
  sendParamTypeConsts : Array Lean.Name := #[]
  sendReqConst?       : Option Lean.Name := none
  sendReqLabel        : String := ""
  sendHelperConst     : Lean.Name := .anonymous

private def elabExtReqPred (chIdent : Ident) (svcName fullSvcName chName : Name) (suffix : String)
    (pIdents : Array Ident) (pTyTerms : Array Term) (reqExprs : Array Syntax) :
    CommandElabM (Option Name × String) := do
  if reqExprs.isEmpty then return (none, "")
  let props ← reqExprs.mapM fun e => liftMacroM <| Qed.Lang.lowerSimpleQedExpr .propInv e
  let conj ← Qed.mkConjBody props (ascribeProp := false)
  let reqId := mkIdentFrom chIdent (svcName ++ chName.appendAfter suffix)
  elabCommand (← `(command|
    set_option linter.unusedVariables false in
    @[simp] abbrev $reqId $[($pIdents:ident : $pTyTerms:term)]* : Prop := $conj))
  let lbl := String.intercalate " && " (reqExprs.toList.map fun e => (e.reprint.getD "requires").trimAscii.toString)
  return (some (fullSvcName ++ chName.appendAfter suffix), lbl)

private def emitExtWsSend (chIdent : Ident) (svcName fullSvcName chName : Name)
    (sendParams : Array ParsedExtParam) (sendReqExprs : Array Syntax) :
    CommandElabM ExtWsSendInfo := do
  let some sp := sendParams[0]? | return {}
  let (spId, spTyTerm) := (sp.ident, sp.ty.term)
  let sendCodec := classifyExtWsCodec sp.ty
  let sendParamTypeConsts ← elabParamTypeAbbrevs chIdent svcName fullSvcName chName "_SendParam_" #[spTyTerm]
  let (sendReqConst?, sendReqLabel) ← elabExtReqPred chIdent svcName fullSvcName chName "_send_req" #[spId] #[spTyTerm] sendReqExprs
  let slotId := mkIdent `slot
  let sendId := mkIdentFrom chIdent (svcName ++ chName.appendAfter "_send")
  let sendBody : Term ← match sendCodec with
    | .text  => `(Qed.Cmd.wsExtSendText $slotId $spId)
    | .json  => `(Qed.Cmd.wsExtSendText $slotId (Qed.Json.render (Qed.toJson $spId)))
    | .bytes => `(Qed.Cmd.wsExtSendBytes $slotId $spId)
    | .proto => `(Qed.Cmd.wsExtSendBytes $slotId (Qed.Proto.encode $spId))
  elabCommand (← `(command|
    def $sendId {msg : Type} ($slotId:ident : String) ($spId:ident : $spTyTerm) : Qed.Cmd msg :=
      $sendBody))
  return {
    sendCodec, sendParamTypeConsts, sendReqConst?, sendReqLabel
    sendHelperConst := fullSvcName ++ chName.appendAfter "_send"
  }

private def elabExternalWsChannel (svcName fullSvcName : Name) (svcNameStr : String) (baseId : Ident)
    (existingNames : Array Name) (wsStx : Syntax) : CommandElabM Name := do
  let urlTmpl := (⟨(wsStx.getArg 1)⟩ : TSyntax `str).getString
  let chIdent : Ident := ⟨(wsStx.getArg 2)⟩
  let chName := chIdent.getId
  if existingNames.contains chName then
    throwErrorAt chIdent s!"duplicate channel/endpoint `{chName}` in `external {svcName}`"
  let parsedParams ← parseTypedParams s!"`ws {chName}`" (wsStx.getArg 4).getSepArgs
  let pIdents := parsedParams.map (·.ident)
  let pTyTerms := parsedParams.map (·.ty.term)
  let seenP := pIdents.map (·.getId.toString)
  let evTy ← liftMacroM <| lowerSrvType (wsStx.getArg 7) false s!"event type of `ws {chName}`"
  let evTyTerm := evTy.term
  let evCodec := classifyExtWsCodec evTy
  let isBinary := evCodec == .proto || evCodec == .bytes
  let (segSpecs, querySpecs, placeholders) ← parseUrlTemplate (wsStx.getArg 1) urlTmpl
  for ph in placeholders do
    unless seenP.contains ph do
      throwErrorAt (wsStx.getArg 1) s!"WebSocket URL placeholder `:{ph}` has no matching parameter `{ph}` in `{chName}`"
  for p in pIdents do
    unless placeholders.contains p.getId.toString do
      throwErrorAt p s!"parameter `{p.getId}` on `ws {chName}` is not referenced as `:{p.getId}` in `{urlTmpl}`"
  let subClauses ← parseExtWsSubClauses chName (wsStx.getArg 8)
  if subClauses.hasSend && subClauses.sendParams.size != 1 then
    throwErrorAt chIdent s!"3rd-party `ws {chName}` `send(...)` expects a single payload parameter (bundle multiple fields into a `schema`)"
  let (pathTerms, queryTerms) ← lowerUrlParts (wsStx.getArg 1) segSpecs querySpecs pIdents
  let evAbbrevId := mkIdentFrom chIdent (svcName ++ chName.appendAfter "_Event")
  elabCommand (← `(command| abbrev $evAbbrevId : Type := $evTyTerm))
  let paramTypeConsts ← elabParamTypeAbbrevs chIdent svcName fullSvcName chName "_Param_" pTyTerms
  let (reqConst?, reqLabel) ← elabExtReqPred chIdent svcName fullSvcName chName "_req" pIdents pTyTerms subClauses.reqExprs
  emitExtWsSubAndUnsub chIdent baseId svcName chName pIdents pTyTerms evTyTerm evCodec isBinary pathTerms queryTerms
  let sendInfo ← emitExtWsSend chIdent svcName fullSvcName chName subClauses.sendParams subClauses.sendReqExprs
  modifyEnv fun env => Qed.channelRegistry.addEntry env {
    ChannelInfo.mkDefault fullSvcName svcNameStr chName
      (.external fullSvcName isBinary evCodec sendInfo.sendCodec)
      (pIdents.map (·.getId)) paramTypeConsts subClauses.recPolicy with
    hasSend := subClauses.hasSend, sendParamCount := subClauses.sendParams.size
    sendParamTypeConsts := sendInfo.sendParamTypeConsts
    sendReqConst := sendInfo.sendReqConst?, sendReqLabel := sendInfo.sendReqLabel
    clientReqConst := reqConst?, clientReqLabel := reqLabel
    sendHelperConst := sendInfo.sendHelperConst
  }
  return chName

@[command_elab externalCmd]
def elabExternalCmd : CommandElab := fun stx => do
  let svcIdent : Ident := ⟨(stx.getArg 1)⟩
  let svcName := svcIdent.getId
  let svcNameStr := svcName.toString
  let (baseOrigin, authSpec, epClauses, wsClauses) ← parseExternalClauses svcIdent svcName (stx.getArg 3).getArgs
  let fullSvcName := (← getCurrNamespace) ++ svcName
  let secretsList := authSpec.requiredSecrets.toArray
  let baseId := mkIdentFrom svcIdent (svcName ++ `baseUrl)
  let authTerm : Term ← match authSpec with
    | .none => `(Qed.Server.AuthSpec.none)
    | .bearerSecret v => `(Qed.Server.AuthSpec.bearerSecret $(quote v))
    | .headerSecret h v => `(Qed.Server.AuthSpec.headerSecret $(quote h) $(quote v))
    | .gcpServiceAccount v sc => `(Qed.Server.AuthSpec.gcpServiceAccount $(quote v) $(quote sc))
  for cmd in #[
    ← `(command| def $baseId : String := $(quote baseOrigin)),
    ← `(command| def $(mkIdentFrom svcIdent (svcName ++ `secrets)) : Array String := $(quote secretsList)),
    ← `(command| theorem $(mkIdentFrom svcIdent (svcName ++ `_qed_external_marker)) : True := True.intro)
  ] do elabCommand cmd
  let mut methodNames : Array Name := #[]
  for ep in epClauses do
    methodNames := methodNames.push (← elabExternalEndpoint svcName (Syntax.mkStrLit svcNameStr) baseId authTerm methodNames ep)
  for ws in wsClauses do
    methodNames := methodNames.push (← elabExternalWsChannel svcName fullSvcName svcNameStr baseId methodNames ws)
  modifyEnv fun env => externalRegistry.addEntry env {
    serviceName := fullSvcName, baseOrigin, secrets := secretsList, methods := methodNames.map (fullSvcName ++ ·)
  }

end ExternalElab

end Qed.Server
