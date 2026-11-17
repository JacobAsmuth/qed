import Lean
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
    | ok sfx  => exact .httpCall _ _ fun res => .pure (res.bind checkHttpOk)

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
  noAtomic := by unfold postJson postRaw; exact .httpCall _ _ fun res => .pure (decodeRespJson (res.bind checkHttpOk))

instance {σ : Type} (url : WebhookUrl) (mime : String) (body : Bytes) :
    SafeIO (postBytes (m := ThreadProg σ) url mime body) where
  noAtomic := by unfold postBytes postRaw; exact .httpCall _ _ fun res => .pure (decodeRespBytes (res.bind checkHttpOk))

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
    CommandElabM (String × AuthSpec × Array Syntax) := do
  let mut baseOrigin? : Option String := none
  let mut authSpec : AuthSpec := .none
  let mut hasAuth := false
  let mut epClauses : Array Syntax := #[]
  for c in clauses do
    let k := c.getKind
    if k == ``extBaseClause then
      if baseOrigin?.isSome then
        throwErrorAt c s!"duplicate `base` clause in `external {svcName}`"
      let strStx : TSyntax `str := ⟨c[1]⟩
      let rawBase := strStx.getString
      let trimmed := if rawBase.endsWith "/" then
        String.ofList (rawBase.toList.take (rawBase.length - 1))
      else rawBase
      unless isValidBaseOrigin trimmed do
        throwErrorAt c s!"invalid `base` URL `{rawBase}`: expected pinned `https://host...` or `http://host...` without `?`, `#`, `@`, or `\\`"
      baseOrigin? := some trimmed
    else if k == ``extAuthBearer || k == ``extAuthHeader || k == ``extAuthGcp then
      if hasAuth then throwErrorAt c s!"duplicate `auth` clause in `external {svcName}`"
      hasAuth := true
      let checkEnv (stx : Syntax) : CommandElabM String := do
        let v := (⟨stx⟩ : TSyntax `str).getString
        unless isValidEnvVarName v do throwErrorAt stx s!"invalid secret environment variable name `{v}`"
        return v
      if k == ``extAuthBearer then
        authSpec := .bearerSecret (← checkEnv c[5])
      else if k == ``extAuthHeader then
        let hdrName := (⟨c[3]⟩ : TSyntax `str).getString
        if hdrName.isEmpty then throwErrorAt c[3] "header name cannot be empty"
        authSpec := .headerSecret hdrName (← checkEnv c[7])
      else
        let scope := if c[7].getNumArgs == 2 then (⟨c[7][1]⟩ : TSyntax `str).getString
                     else "https://www.googleapis.com/auth/cloud-platform"
        authSpec := .gcpServiceAccount (← checkEnv c[5]) scope
    else if k == ``extEndpointClause then
      epClauses := epClauses.push c
    else
      throwErrorAt c "unexpected clause in `external` block"
  let some baseOrigin := baseOrigin?
    | throwErrorAt svcIdent s!"`external {svcName}` must declare `base \"https://...\"`"
  if epClauses.isEmpty then
    throwErrorAt svcIdent s!"`external {svcName}` must declare at least one endpoint"
  return (baseOrigin, authSpec, epClauses)

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
private def elabExternalEndpoint (svcName : Name) (svcStrLit : StrLit) (baseId : Ident)
    (authTerm : Term) (methodNames : Array Name) (ep : Syntax) : CommandElabM Name := do
  let httpVerbRaw := ep[0].getId.toString.toUpper
  let urlTmpl := (⟨ep[1]⟩ : TSyntax `str).getString
  let fnIdent : Ident := ⟨ep[2]⟩
  let fnName := fnIdent.getId
  if methodNames.contains fnName then
    throwErrorAt fnIdent s!"duplicate endpoint `{fnName}` in `external {svcName}`"
  let rawParams := ep[4].getSepArgs
  let mut parsedParams : Array ParsedExtParam := #[]
  let mut seenParamNames : Array String := #[]
  for rp in rawParams do
    let pk := rp.getKind
    let (hk?, pid, tyNode) ←
      if pk == ``extParamHeader then pure (some (⟨rp[2]⟩ : TSyntax `str).getString, (⟨rp[4]⟩ : Ident), rp[6])
      else if pk == ``extParamPlain then pure (none, (⟨rp[0]⟩ : Ident), rp[2])
      else throwErrorAt rp "invalid endpoint parameter"
    let pty ← liftMacroM <| ParsedSrvType.parse tyNode
    liftMacroM <| pty.validate (allowFallible := false) s!"parameter `{pid.getId}`"
    let pstr := pid.getId.toString
    if seenParamNames.contains pstr then throwErrorAt pid s!"duplicate parameter `{pstr}`"
    seenParamNames := seenParamNames.push pstr
    parsedParams := parsedParams.push { ref := rp, headerKey? := hk?, ident := pid, ty := pty }
  let retTy ← liftMacroM <| ParsedSrvType.parse ep[7]
  liftMacroM <| retTy.validate (allowFallible := false)
    "external endpoint return types (external calls are automatically fallible at `await`; write `-> T` instead of `-> T!`)"
  let (segSpecs, querySpecs, placeholders) ← parseUrlTemplate ep[1] urlTmpl
  for ph in placeholders do
    unless parsedParams.any (fun p => p.headerKey?.isNone && p.ident.getId.toString == ph) do
      throwErrorAt ep[1] s!"URL placeholder `:{ph}` has no matching parameter `{ph}` in `{fnName}`"
  let mut bodyParam? : Option ParsedExtParam := none
  for p in parsedParams do
    if p.headerKey?.isNone && !placeholders.contains p.ident.getId.toString then
      if httpVerbRaw == "GET" || httpVerbRaw == "DELETE" then
        throwErrorAt p.ref s!"parameter `{p.ident.getId}` on `{httpVerbRaw}` endpoint `{fnName}` is not referenced as `:{p.ident.getId}` in `{urlTmpl}`"
      if bodyParam?.isSome then
        throwErrorAt p.ref s!"endpoint `{fnName}` has multiple request body parameters; bundle fields into a `schema` type"
      bodyParam? := some p
  let pIdents := parsedParams.map (·.ident)
  let pTyTerms ← parsedParams.mapM fun p => liftMacroM p.ty.toPayloadTerm
  let paramSegTerm (pn : String) : CommandElabM Term := do
    let some p := parsedParams.find? (·.ident.getId.toString == pn)
      | throwErrorAt ep[1] "internal missing URL param"
    `(Qed.RouteParam.toSeg $(p.ident))
  let pathTerms ← segSpecs.mapM fun
    | .lit s          => `(Qed.Server.PathPart.lit $(Syntax.mkStrLit s))
    | .singleParam pn => do `(Qed.Server.PathPart.seg $(← paramSegTerm pn))
    | .multiParam pn  => do `(Qed.Server.PathPart.multiSeg $(← paramSegTerm pn))
  let queryTerms ← querySpecs.mapM fun (qk, qv) => do
    let qkLit := Syntax.mkStrLit qk
    match qv with
    | .lit s    => `(($qkLit, Qed.Server.QueryVal.lit $(Syntax.mkStrLit s)))
    | .param pn => do `(($qkLit, Qed.Server.QueryVal.param $(← paramSegTerm pn)))
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
@[command_elab externalCmd]
def elabExternalCmd : CommandElab := fun stx => do
  let svcIdent : Ident := ⟨stx[1]⟩
  let svcName := svcIdent.getId
  let svcNameStr := svcName.toString
  let (baseOrigin, authSpec, epClauses) ← parseExternalClauses svcIdent svcName stx[2].getArgs
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
  let mut methodNames : Array Name := #[]
  for ep in epClauses do
    methodNames := methodNames.push (← elabExternalEndpoint svcName svcStrLit baseId authTerm methodNames ep)
  modifyEnv fun env => externalRegistry.addEntry env {
    serviceName := fullSvcName
    baseOrigin
    secrets := secretsList
    methods := methodNames.map (fullSvcName ++ ·)
  }

end Qed.Server
