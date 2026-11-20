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
def decodeRespString (res : Except ApiError OutboundResp) : Except ApiError String := do
  let resp ← res
  match String.fromUTF8? resp.body with
  | some s => .ok s
  | none   => .error (ApiError.internal "external API returned invalid UTF-8")

@[specialize]
def decodeRespProto {α : Type} [FromProto α] (res : Except ApiError OutboundResp) : Except ApiError α := do
  let resp ← res
  match Proto.decode (α := α) resp.body with
  | .ok v    => .ok v
  | .error e => .error (ApiError.internal s!"external protobuf decode failed: {e}")

@[specialize]
def decodeRespJson {α : Type} [FromJson α] (res : Except ApiError OutboundResp) : Except ApiError α := do
  let resp ← res
  match String.fromUTF8? resp.body with
  | none     => .error (ApiError.internal "external JSON response is not valid UTF-8")
  | some raw =>
      match (Json.parse raw 128).bind (FromJson.fromJson (α := α)) with
      | .ok v    => .ok v
      | .error e => .error (ApiError.internal s!"external JSON decode failed: {e}")

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

/-! ## Persistent `external` Service Registry (for Transitive Secret Validation) -/

structure ExternalServiceInfo where
  serviceName : Lean.Name
  baseOrigin  : String
  secrets     : Array String
  methods     : Array Lean.Name
deriving Inhabited

initialize externalRegistry :
    Lean.SimplePersistentEnvExtension ExternalServiceInfo (Lean.NameMap ExternalServiceInfo) ←
  Lean.registerSimplePersistentEnvExtension {
    addImportedFn := fun arrays =>
      arrays.foldl (fun acc arr => arr.foldl (fun m info => m.insert info.serviceName info) acc) {}
    addEntryFn := fun m info => m.insert info.serviceName info
  }

/-! ## `external` Command Elaborator -/

private inductive UrlSegSpec where
  | lit (s : String)
  | singleParam (name : String)
  | multiParam (name : String)

private inductive QueryValSpec where
  | lit (s : String)
  | param (name : String)

private def isValidEnvVarName (s : String) : Bool :=
  !s.isEmpty && s.toList.all fun c =>
    ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '_'

open Lean Elab Command in
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
  let mut placeholders : Array String := #[]
  for seg in (rawPath.splitOn "/").filter (· != "") do
    if seg.startsWith ":" then
      let rest := String.ofList (seg.toList.drop 1)
      let isMulti := rest.endsWith "*"
      let pname := if isMulti then String.ofList (rest.toList.take (rest.length - 1)) else rest
      if pname.isEmpty then
        throwErrorAt ref s!"empty `:` placeholder in `{tmpl}`"
      if placeholders.contains pname then
        throwErrorAt ref s!"duplicate placeholder `:{pname}` in `{tmpl}`"
      placeholders := placeholders.push pname
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
          if k.isEmpty then
            throwErrorAt ref s!"empty query parameter key in `{tmpl}`"
          if v.startsWith ":" then
            let rest := String.ofList (v.toList.drop 1)
            let pname := if rest.endsWith "*" then String.ofList (rest.toList.take (rest.length - 1)) else rest
            if pname.isEmpty then
              throwErrorAt ref s!"empty query placeholder in `{tmpl}`"
            if placeholders.contains pname then
              throwErrorAt ref s!"duplicate placeholder `:{pname}` in `{tmpl}`"
            placeholders := placeholders.push pname
            querySpecs := querySpecs.push (k, .param pname)
          else
            querySpecs := querySpecs.push (k, .lit v)
      | [k] =>
          querySpecs := querySpecs.push (k, .lit "")
      | _ =>
          throwErrorAt ref s!"malformed query parameter `{pair}` in `{tmpl}`"
  return (segSpecs, querySpecs, placeholders)

private structure ParsedExtParam where
  ref        : Lean.Syntax
  headerKey? : Option String
  ident      : Lean.Ident
  ty         : ParsedSrvType

open Lean Elab Command in
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

open Lean Elab Command in
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
  let fullFnCall ← pIdents.foldlM (init := ← `($fullFnId))
    fun acc pid => `($acc $pid)
  let safeInstCmd ← `(command|
    instance {_σ : Type} $[($pIdents:ident : $pTyTerms:term)]* :
        Qed.Server.SafeIO ($fullFnCall : Qed.Server.ThreadProg _σ (Except Qed.Server.ApiError $retPayloadTerm)) where
      noAtomic := by
        unfold $fullFnId
        exact (inferInstance : Qed.Server.SafeIO _).noAtomic)
  elabCommand safeInstCmd

open Lean Elab Command in
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

open Lean Elab Command in
private def elabExternalEndpoint (svcName : Name) (svcStrLit : StrLit) (baseId : Ident)
    (authTerm : Term) (methodNames : Array Name) (ep : Syntax) : CommandElabM Name := do
  let httpVerbRaw := (ep.getArg 0).getId.toString.toUpper
  let urlTmpl := (⟨(ep.getArg 1)⟩ : TSyntax `str).getString
  let fnIdent : Ident := ⟨(ep.getArg 2)⟩
  let fnName := fnIdent.getId
  if methodNames.contains fnName then
    throwErrorAt fnIdent s!"duplicate endpoint `{fnName}` in `external {svcName}`"
  let rawParams := (ep.getArg 4).getSepArgs
  let mut parsedParams : Array ParsedExtParam := #[]
  let mut seenParamNames : Array String := #[]
  for rp in rawParams do
    let pk := rp.getKind
    let (hk?, pid, tyNode) ←
      if pk == ``extParamHeader then pure (some (⟨(rp.getArg 2)⟩ : TSyntax `str).getString, (⟨(rp.getArg 4)⟩ : Ident), (rp.getArg 6))
      else if pk == ``extParamPlain then pure (none, (⟨(rp.getArg 0)⟩ : Ident), (rp.getArg 2))
      else throwErrorAt rp "invalid endpoint parameter"
    let pty ← liftMacroM <| ParsedSrvType.parse tyNode
    liftMacroM <| pty.validate (allowFallible := false) s!"parameter `{pid.getId}`"
    let pstr := pid.getId.toString
    if seenParamNames.contains pstr then throwErrorAt pid s!"duplicate parameter `{pstr}` in endpoint `{fnName}`"
    seenParamNames := seenParamNames.push pstr
    parsedParams := parsedParams.push { ref := rp, headerKey? := hk?, ident := pid, ty := pty }
  let retTy ← liftMacroM <| ParsedSrvType.parse (ep.getArg 7)
  liftMacroM <| retTy.validate (allowFallible := false)
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
  let pTyTerms ← parsedParams.mapM fun p => liftMacroM p.ty.toPayloadTerm
  let urlParamIdents := (parsedParams.filter (·.headerKey?.isNone)).map (·.ident)
  let (pathTerms, queryTerms) ← lowerUrlParts (ep.getArg 1) segSpecs querySpecs urlParamIdents
  let mut customHdrTerms : Array Term := #[]
  for p in parsedParams do
    if let some hk := p.headerKey? then
      customHdrTerms := customHdrTerms.push
        (← `(($(Syntax.mkStrLit hk), Qed.RouteParam.toSeg $(p.ident))))
  let baseRetStr := retTy.baseIdent.getId.toString
  let acceptHdr : Option (String × String) :=
    if retTy.isProto then some ("Accept", "application/x-protobuf")
    else if retTy.mods.isEmpty && (baseRetStr == "Bytes" || baseRetStr == "ByteArray" || baseRetStr == "Unit" || baseRetStr == "String") then none
    else some ("Accept", "application/json")
  let (bodyTerm, ctHdr) ← match bodyParam? with
    | none => pure (← `(ByteArray.empty), (none : Option (String × String)))
    | some bp =>
        let bBase := bp.ty.baseIdent.getId.toString
        if bp.ty.isProto then
          pure (← `(Qed.Proto.encode $(bp.ident)), some ("Content-Type", "application/x-protobuf"))
        else if bp.ty.mods.isEmpty && (bBase == "Bytes" || bBase == "ByteArray") then
          pure (← `(($(bp.ident) : ByteArray)), some ("Content-Type", "application/octet-stream"))
        else if bp.ty.mods.isEmpty && bBase == "Unit" then
          pure (← `(ByteArray.empty), none)
        else
          pure (← `((Qed.Json.render (Qed.toJson $(bp.ident))).toUTF8), some ("Content-Type", "application/json"))
  let mut defHdrTerms : Array Term := #[]
  if let some (k, v) := ctHdr then
    defHdrTerms := defHdrTerms.push (← `(($(Syntax.mkStrLit k), $(Syntax.mkStrLit v))))
  if let some (k, v) := acceptHdr then
    defHdrTerms := defHdrTerms.push (← `(($(Syntax.mkStrLit k), $(Syntax.mkStrLit v))))
  let retPayloadTerm ← liftMacroM retTy.toPayloadTerm
  let decodeCall : Term ←
    if retTy.isProto then
      `(Qed.Server.decodeRespProto (α := $retPayloadTerm) rawRes)
    else if retTy.mods.isEmpty && (baseRetStr == "Bytes" || baseRetStr == "ByteArray") then
      `(Qed.Server.decodeRespBytes rawRes)
    else if retTy.mods.isEmpty && baseRetStr == "Unit" then
      `(Qed.Server.decodeRespUnit rawRes)
    else if retTy.mods.isEmpty && baseRetStr == "String" then
      `(Qed.Server.decodeRespString rawRes)
    else
      `(Qed.Server.decodeRespJson (α := $retPayloadTerm) rawRes)
  let fullFnId := mkIdentFrom fnIdent (svcName ++ fnName)
  buildExternalCallCmds fullFnId baseId svcStrLit (Syntax.mkStrLit httpVerbRaw)
    pIdents pTyTerms retPayloadTerm pathTerms queryTerms defHdrTerms customHdrTerms
    bodyTerm authTerm decodeCall
  return fnName

open Lean Elab Command in
private def classifyExtWsCodec (ty : ParsedSrvType) : Qed.ExtWsCodec :=
  if ty.isProto then .proto
  else
    let b := ty.baseIdent.getId.toString
    if ty.mods.isEmpty && (b == "Bytes" || b == "ByteArray") then .bytes
    else if ty.mods.isEmpty && b == "String" then .text
    else .json

open Lean Elab Command in
def buildPropConj (ps : Array Term) : CommandElabM Term := do
  match ps.toList with
  | [] => `(True)
  | p :: rest => rest.foldlM (init := p) fun acc q => `($acc ∧ $q)

open Lean Elab Command in
def elabParamTypeAbbrevs (refIdent : Ident) (ownerName fullOwnerName itemName : Name)
    (suffix : String) (tyTerms : Array Term) : CommandElabM (Array Name) := do
  let mut consts : Array Name := #[]
  for (pTy, i) in tyTerms.zipIdx do
    let leaf := itemName.appendAfter s!"{suffix}{i}"
    let pTyId := mkIdentFrom refIdent (ownerName ++ leaf)
    elabCommand (← `(command| abbrev $pTyId : Type := $pTy))
    consts := consts.push (fullOwnerName ++ leaf)
  return consts

open Lean Elab Command in
private def elabExternalWsChannel (svcName fullSvcName : Name) (svcNameStr : String) (baseId : Ident)
    (existingNames : Array Name) (wsStx : Syntax) : CommandElabM Name := do
  let urlTmpl := (⟨(wsStx.getArg 1)⟩ : TSyntax `str).getString
  let chIdent : Ident := ⟨(wsStx.getArg 2)⟩
  let chName := chIdent.getId
  let chStr := chName.toString
  if existingNames.contains chName then
    throwErrorAt chIdent s!"duplicate channel/endpoint `{chName}` in `external {svcName}`"
  let rawParams := (wsStx.getArg 4).getSepArgs
  let mut pIdents : Array Ident := #[]
  let mut pTyTerms : Array Term := #[]
  let mut seenP : Array String := #[]
  for rp in rawParams do
    let pid : Ident := ⟨(rp.getArg 0)⟩
    let pstr := pid.getId.toString
    if seenP.contains pstr then throwErrorAt pid s!"duplicate parameter `{pstr}` in `ws {chName}`"
    seenP := seenP.push pstr
    let pty ← liftMacroM <| ParsedSrvType.parse (rp.getArg 2)
    liftMacroM <| pty.validate (allowFallible := false) s!"parameter `{pstr}`"
    pIdents := pIdents.push pid
    pTyTerms := pTyTerms.push (← liftMacroM pty.toPayloadTerm)

  let evTy ← liftMacroM <| ParsedSrvType.parse (wsStx.getArg 7)
  liftMacroM <| evTy.validate (allowFallible := false) s!"event type of `ws {chName}`"
  let evTyTerm ← liftMacroM evTy.toPayloadTerm
  let evCodec := classifyExtWsCodec evTy
  let isBinary := evCodec == .proto || evCodec == .bytes

  let (segSpecs, querySpecs, placeholders) ← parseUrlTemplate (wsStx.getArg 1) urlTmpl
  for ph in placeholders do
    unless seenP.contains ph do
      throwErrorAt (wsStx.getArg 1) s!"WebSocket URL placeholder `:{ph}` has no matching parameter `{ph}` in `{chName}`"
  for p in pIdents do
    unless placeholders.contains p.getId.toString do
      throwErrorAt p s!"parameter `{p.getId}` on `ws {chName}` is not referenced as `:{p.getId}` in `{urlTmpl}`"

  let mut reqExprs : Array Syntax := #[]
  let mut sendParams : Array (Ident × ParsedSrvType × Term) := #[]
  let mut sendReqExprs : Array Syntax := #[]
  let mut hasSend := false
  let mut recPolicy : Qed.Reconnect := .defaultPolicy
  let mut hasRec := false

  if (wsStx.getArg 8).getNumArgs == 2 then
    for sub in ((wsStx.getArg 8).getArg 1).getArgs do
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
        let mut seenSp : Array String := #[]
        for srp in (sub.getArg 2).getSepArgs do
          let spid : Ident := ⟨(srp.getArg 0)⟩
          let spstr := spid.getId.toString
          if seenSp.contains spstr then throwErrorAt spid s!"duplicate send parameter `{spstr}` in `ws {chName}`"
          seenSp := seenSp.push spstr
          let spty ← liftMacroM <| ParsedSrvType.parse (srp.getArg 2)
          liftMacroM <| spty.validate (allowFallible := false) s!"send parameter `{spstr}`"
          sendParams := sendParams.push (spid, spty, ← liftMacroM spty.toPayloadTerm)
        if (sub.getArg 4).getNumArgs == 2 then
          for srl in ((sub.getArg 4).getArg 1).getArgs do
            sendReqExprs := sendReqExprs ++ (srl.getArg 1).getSepArgs
      else
        throwErrorAt sub s!"unexpected clause in `ws {chName}`"

  if hasSend && sendParams.size != 1 then
    throwErrorAt chIdent s!"3rd-party `ws {chName}` `send(...)` expects a single payload parameter (bundle multiple fields into a `schema`)"

  let (pathTerms, queryTerms) ← lowerUrlParts (wsStx.getArg 1) segSpecs querySpecs pIdents

  -- Emit `<Svc>.<ch>_Event` & param type aliases
  let evAbbrevId := mkIdentFrom chIdent (svcName ++ chName.appendAfter "_Event")
  elabCommand (← `(command| abbrev $evAbbrevId : Type := $evTyTerm))
  let paramTypeConsts ← elabParamTypeAbbrevs chIdent svcName fullSvcName chName "_Param_" pTyTerms

  -- Emit `<Svc>.<ch>_req` if `requires` present
  let mut reqConst? : Option Name := none
  let mut reqLabel := ""
  if !reqExprs.isEmpty then
    let reqProps ← reqExprs.mapM fun e => liftMacroM <| Qed.Lang.lowerSimpleQedExpr .propInv e
    let reqConj ← buildPropConj reqProps
    let reqId := mkIdentFrom chIdent (svcName ++ chName.appendAfter "_req")
    elabCommand (← `(command|
      set_option linter.unusedVariables false in
      @[simp] abbrev $reqId $[($pIdents:ident : $pTyTerms:term)]* : Prop := $reqConj))
    reqConst? := some (fullSvcName ++ chName.appendAfter "_req")
    reqLabel := String.intercalate " && " (reqExprs.toList.map fun e => (e.reprint.getD "requires").trimAscii.toString)

  -- Emit `<Svc>.<ch>_key` (origin-pinned WS URL)
  let keyId := mkIdentFrom chIdent (svcName ++ chName.appendAfter "_key")
  elabCommand (← `(command|
    def $keyId $[($pIdents:ident : $pTyTerms:term)]* : String :=
      (Qed.Server.buildExternalWsUrl $baseId [$[$pathTerms],*] [$[$queryTerms],*]).toOption.getD ""))

  -- Emit `<Svc>.<ch>_sub`
  let subId := mkIdentFrom chIdent (svcName ++ chName.appendAfter "_sub")
  let slotId := mkIdent `slot
  let recId := mkIdent `rec
  let onJoinId := mkIdent `onJoin
  let onMsgId := mkIdent `onMsg
  let onStatusId := mkIdent `onStatus
  let keyApp ← pIdents.foldlM (init := (keyId : Term)) fun acc p => `($acc $p)
  let isBinTerm : Term ← if isBinary then `(true) else `(false)
  let (onTextTerm, onBytesTerm) ← match evCodec with
    | .text  => pure (← `($onMsgId), ← `(fun _ => $onStatusId (Qed.SocketStatus.failed "unexpected binary WebSocket frame")))
    | .json  => pure (
        ← `(fun raw =>
              match (Qed.Json.parse raw 128).bind (Qed.FromJson.fromJson (α := $evTyTerm)) with
              | Except.ok v    => $onMsgId v
              | Except.error e => $onStatusId (Qed.SocketStatus.failed e)),
        ← `(fun _ => $onStatusId (Qed.SocketStatus.failed "unexpected binary WebSocket frame")))
    | .bytes => pure (← `(fun _ => $onStatusId (Qed.SocketStatus.failed "unexpected text WebSocket frame")), ← `($onMsgId))
    | .proto => pure (
        ← `(fun _ => $onStatusId (Qed.SocketStatus.failed "unexpected text WebSocket frame")),
        ← `(fun bs =>
              match Qed.Proto.decode (α := $evTyTerm) bs with
              | Except.ok v    => $onMsgId v
              | Except.error e => $onStatusId (Qed.SocketStatus.failed e)))
  elabCommand (← `(command|
    set_option linter.unusedVariables false in
    def $subId {msg : Type} ($slotId:ident : String) $[($pIdents:ident : $pTyTerms:term)]*
        ($recId:ident : Qed.Reconnect) ($onJoinId:ident : Unit → msg) ($onMsgId:ident : $evTyTerm → msg)
        ($onStatusId:ident : Qed.SocketStatus → msg) : Qed.Cmd msg :=
      let url := $keyApp
      if url.isEmpty then Qed.Cmd.none
      else Qed.Cmd.wsExtOpen $slotId url $isBinTerm $recId $onJoinId $onTextTerm $onBytesTerm $onStatusId))

  -- Emit `<Svc>.<ch>_unsub`
  let unsubId := mkIdentFrom chIdent (svcName ++ chName.appendAfter "_unsub")
  elabCommand (← `(command|
    def $unsubId {msg : Type} ($slotId:ident : String) : Qed.Cmd msg :=
      Qed.Cmd.wsExtClose $slotId))

  -- Emit `<Svc>.<ch>_send` & `_send_req` if `send(...)` declared
  let mut sendCodec : Qed.ExtWsCodec := .json
  let mut sendParamNames : Array Name := #[]
  let mut sendParamTypeConsts : Array Name := #[]
  let mut sendReqConst? : Option Name := none
  let mut sendReqLabel := ""
  let mut sendHelperConst : Name := .anonymous
  if let some (spId, spTy, spTyTerm) := sendParams[0]? then
    sendCodec := classifyExtWsCodec spTy
    sendParamNames := #[spId.getId]
    let spAbbrevId := mkIdentFrom chIdent (svcName ++ chName.appendAfter "_SendParam_0")
    elabCommand (← `(command| abbrev $spAbbrevId : Type := $spTyTerm))
    sendParamTypeConsts := #[fullSvcName ++ chName.appendAfter "_SendParam_0"]
    if !sendReqExprs.isEmpty then
      let sProps ← sendReqExprs.mapM fun e => liftMacroM <| Qed.Lang.lowerSimpleQedExpr .propInv e
      let sConj ← buildPropConj sProps
      let sReqId := mkIdentFrom chIdent (svcName ++ chName.appendAfter "_send_req")
      elabCommand (← `(command|
        set_option linter.unusedVariables false in
        @[simp] abbrev $sReqId ($spId:ident : $spTyTerm) : Prop := $sConj))
      sendReqConst? := some (fullSvcName ++ chName.appendAfter "_send_req")
      sendReqLabel := String.intercalate " && " (sendReqExprs.toList.map fun e => (e.reprint.getD "requires").trimAscii.toString)
    let sendId := mkIdentFrom chIdent (svcName ++ chName.appendAfter "_send")
    let sendBody : Term ← match sendCodec with
      | .text  => `(Qed.Cmd.wsExtSendText $slotId $spId)
      | .json  => `(Qed.Cmd.wsExtSendText $slotId (Qed.Json.render (Qed.toJson $spId)))
      | .bytes => `(Qed.Cmd.wsExtSendBytes $slotId $spId)
      | .proto => `(Qed.Cmd.wsExtSendBytes $slotId (Qed.Proto.encode $spId))
    elabCommand (← `(command|
      def $sendId {msg : Type} ($slotId:ident : String) ($spId:ident : $spTyTerm) : Qed.Cmd msg :=
        $sendBody))
    sendHelperConst := fullSvcName ++ chName.appendAfter "_send"

  modifyEnv fun env => Qed.channelRegistry.addEntry env {
    fullName := fullSvcName ++ chName
    ownerName := fullSvcName
    ownerShort := svcNameStr
    channelName := chStr
    kind := .external fullSvcName isBinary evCodec sendCodec
    paramNames := pIdents.map (·.getId)
    paramCount := pIdents.size
    paramTypeConsts
    eventTypeConst := fullSvcName ++ chName.appendAfter "_Event"
    hasJoinSnapshot := false
    joinTypeConst := .anonymous
    hasSend
    sendParamNames
    sendParamCount := sendParams.size
    sendParamTypeConsts
    sendReqConst := sendReqConst?
    sendReqLabel
    requiresAuth := false
    clientReqConst := reqConst?
    clientReqLabel := reqLabel
    hasEnsures := false
    ensPredConst := none
    defaultReconnect := recPolicy
    keyHelperConst := fullSvcName ++ chName.appendAfter "_key"
    subHelperConst := fullSvcName ++ chName.appendAfter "_sub"
    sendHelperConst
    unsubHelperConst := fullSvcName ++ chName.appendAfter "_unsub"
  }
  return chName

open Lean Elab Command in
@[command_elab externalCmd]
def elabExternalCmd : CommandElab := fun stx => do
  let svcIdent : Ident := ⟨(stx.getArg 1)⟩
  let svcName := svcIdent.getId
  let svcNameStr := svcName.toString
  let (baseOrigin, authSpec, epClauses, wsClauses) ← parseExternalClauses svcIdent svcName (stx.getArg 3).getArgs
  let currNs ← getCurrNamespace
  let fullSvcName := currNs ++ svcName
  let secretsList := authSpec.requiredSecrets.toArray
  let secretsLits : Array Term := secretsList.map (Syntax.mkStrLit ·)
  let baseId := mkIdentFrom svcIdent (svcName ++ `baseUrl)
  let secretsId := mkIdentFrom svcIdent (svcName ++ `secrets)
  let baseLit := Syntax.mkStrLit baseOrigin
  let svcStrLit := Syntax.mkStrLit svcNameStr
  let authTerm : Term ← match authSpec with
    | .none => `(Qed.Server.AuthSpec.none)
    | .bearerSecret v => `(Qed.Server.AuthSpec.bearerSecret $(Syntax.mkStrLit v))
    | .headerSecret h v => `(Qed.Server.AuthSpec.headerSecret $(Syntax.mkStrLit h) $(Syntax.mkStrLit v))
    | .gcpServiceAccount v sc => `(Qed.Server.AuthSpec.gcpServiceAccount $(Syntax.mkStrLit v) $(Syntax.mkStrLit sc))
  elabCommand (← `(command| def $baseId : String := $baseLit))
  elabCommand (← `(command| def $secretsId : Array String := #[$[$secretsLits],*]))
  let markerId := mkIdentFrom svcIdent (svcName ++ `_qed_external_marker)
  elabCommand (← `(command| theorem $markerId : True := True.intro))
  let mut methodNames : Array Name := #[]
  for ep in epClauses do
    methodNames := methodNames.push (← elabExternalEndpoint svcName svcStrLit baseId authTerm methodNames ep)
  for ws in wsClauses do
    methodNames := methodNames.push (← elabExternalWsChannel svcName fullSvcName svcNameStr baseId methodNames ws)
  modifyEnv fun env => externalRegistry.addEntry env {
    serviceName := fullSvcName
    baseOrigin
    secrets := secretsList
    methods := methodNames.map (fullSvcName ++ ·)
  }

end Qed.Server
