import Lean
import Qed.Runtime.Cmd
import Qed.Schema.Registry
import Qed.Server.Registry
import Qed.Server.Core
import Qed.Server.Syntax

namespace Qed.Server

/-! ## Runtime Wire Execution Helpers for `external` & `Webhook` -/

private def mergeHeaders (defaults custom : List (String × String)) : List (String × String) :=
  let sc := custom.map fun (k, v) => (sanitizeHeader k, sanitizeHeader v)
  let cl := sc.map (·.1.toLower)
  defaults.filter (fun (k, _) => !cl.contains k.toLower) ++ sc

private def checkHttpOk (okStatuses : List UInt32 := []) (resp : OutboundResp) : Except ApiError OutboundResp :=
  let ok := if okStatuses.isEmpty then 200 ≤ resp.status && resp.status < 300 else okStatuses.contains resp.status
  if ok then .ok resp
  else let msg := (String.fromUTF8? resp.body).getD "external HTTP error"
       .error { code := resp.status.toNat, message := if msg.isEmpty then s!"HTTP {resp.status}" else msg }

@[specialize]
def execExternalRaw {m : Type → Type} [Monad m] [MonadServer m] (serviceName baseOrigin method : String)
    (parts : List PathPart) (query : List (String × QueryVal)) (defaultHeaders customHeaders : List (String × String))
    (body : ByteArray) (auth : AuthSpec) (ssrfGuard : Bool := true) (okStatuses : List UInt32 := []) : m (Except ApiError OutboundResp) := do
  match buildExternalSuffix parts query with
  | .error e => return .error e
  | .ok sfx => return (← MonadServer.httpCall { serviceName, baseOrigin, method, pathAndQuery := "/" ++ sfx, headers := mergeHeaders defaultHeaders customHeaders, body, auth, ssrfGuard }).bind (checkHttpOk okStatuses)

instance {σ : Type} (svc base method : String) (parts : List PathPart) (query : List (String × QueryVal))
    (defHdrs custHdrs : List (String × String)) (body : ByteArray) (auth : AuthSpec)
    (ssrfGuard : Bool) (okStatuses : List UInt32) :
    SafeIO (execExternalRaw (m := ThreadProg σ) svc base method parts query defHdrs custHdrs body auth ssrfGuard okStatuses) where
  noAtomic := by
    unfold execExternalRaw
    cases buildExternalSuffix parts query with
    | error e => exact .pure (Except.error e)
    | ok sfx => exact .io (.httpCall _) _ fun res => .pure (res.bind (checkHttpOk okStatuses))

@[specialize] def decodeRespBytes (res : Except ApiError OutboundResp) : Except ApiError Bytes := res.map (·.body)
@[specialize] def decodeRespUnit (res : Except ApiError OutboundResp) : Except ApiError Unit := res.map fun _ => ()
@[specialize] def decodeRespString (res : Except ApiError OutboundResp) : Except ApiError String :=
  res.bind fun r => (String.fromUTF8? r.body).elim (.error (ApiError.internal "external API returned invalid UTF-8")) .ok
@[specialize] def decodeRespProto {α : Type} [FromProto α] (res : Except ApiError OutboundResp) : Except ApiError α :=
  res.bind fun r => (Proto.decode (α := α) r.body).mapError fun e => ApiError.internal s!"external protobuf decode failed: {e}"
private def isAllWsBytesAux (s : String) (i : Nat) : Nat → Bool
  | 0 => true
  | fuel + 1 =>
      if h : i < s.utf8ByteSize then
        let b := s.getUTF8Byte ⟨i⟩ h
        if b == 32 || b == 9 || b == 10 || b == 13 then isAllWsBytesAux s (i + 1) fuel else false
      else true

private def isAllWsBytes (s : String) : Bool := isAllWsBytesAux s 0 s.utf8ByteSize

@[specialize] def decodeRespJson {α : Type} [FromJson α] (res : Except ApiError OutboundResp) : Except ApiError α :=
  (decodeRespString res).bind fun raw =>
    let payload := if isAllWsBytes raw then "{}" else raw
    ((Json.parse payload 128).bind (FromJson.fromJson (α := α))).mapError fun e => ApiError.internal s!"external JSON decode failed: {e}"

namespace Webhook

private def splitHttpsOriginAndPath (raw : String) : String × String :=
  match Qed.Str.splitChar (String.ofList (raw.toList.drop 8)) '/' with
  | [] => (raw, "/")
  | host :: rest => ("https://" ++ host, if rest.isEmpty then "/" else "/" ++ String.intercalate "/" rest)

@[specialize]
def postRaw {m : Type → Type} [Monad m] [MonadServer m] (url : WebhookUrl) (headers : List (String × String)) (body : Bytes) : m (Except ApiError OutboundResp) := do
  let (origin, path) := splitHttpsOriginAndPath url.raw
  return (← MonadServer.httpCall { serviceName := "Webhook", baseOrigin := origin, method := "POST", pathAndQuery := path, headers, body, auth := .none, ssrfGuard := true }).bind checkHttpOk

@[specialize]
def postJson {Payload Resp : Type} {m : Type → Type} [Monad m] [MonadServer m] [ToJson Payload] [FromJson Resp] (url : WebhookUrl) (payload : Payload) : m (Except ApiError Resp) := do
  let res ← postRaw url [("Content-Type", "application/json"), ("Accept", "application/json")] (Json.render (toJson payload)).toUTF8
  return decodeRespJson res

@[specialize]
def postBytes {m : Type → Type} [Monad m] [MonadServer m] (url : WebhookUrl) (mime : String) (body : Bytes) : m (Except ApiError Bytes) := do
  let res ← postRaw url [("Content-Type", sanitizeHeader mime)] body
  return decodeRespBytes res

instance {σ Payload Resp : Type} [ToJson Payload] [FromJson Resp] (url : WebhookUrl) (payload : Payload) :
    SafeIO (postJson (Payload := Payload) (Resp := Resp) (m := ThreadProg σ) url payload) where
  noAtomic := by unfold postJson postRaw; exact .io (.httpCall _) _ fun res => .pure (decodeRespJson (res.bind checkHttpOk))

instance {σ : Type} (url : WebhookUrl) (mime : String) (body : Bytes) : SafeIO (postBytes (m := ThreadProg σ) url mime body) where
  noAtomic := by unfold postBytes postRaw; exact .io (.httpCall _) _ fun res => .pure (decodeRespBytes (res.bind checkHttpOk))

theorem progEffSpec_postRaw {σ : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {EffOk : ServerEffect → Prop} {Post : Except ApiError OutboundResp → Prop}
    (url : WebhookUrl) (headers : List (String × String)) (body : Bytes)
    (hHttp : ∀ req, EffOk (.httpCall req)) (hPost : ∀ r, Post r) :
    ProgEffSpec Inv A Step EffOk Post (postRaw (m := ThreadProg σ) url headers body) :=
  .io (.httpCall _) _ (hHttp _) fun res => .pure _ (hPost (res.bind checkHttpOk))

theorem progEffSpec_postJson {σ Payload Resp : Type} [ToJson Payload] [FromJson Resp]
    {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {EffOk : ServerEffect → Prop} {Post : Except ApiError Resp → Prop}
    (url : WebhookUrl) (payload : Payload)
    (hHttp : ∀ req, EffOk (.httpCall req)) (hPost : ∀ r, Post r) :
    ProgEffSpec Inv A Step EffOk Post (postJson (Payload := Payload) (Resp := Resp) (m := ThreadProg σ) url payload) :=
  (progEffSpec_postRaw url _ _ hHttp fun _ => trivial).bind fun res _ => .pure _ (hPost (decodeRespJson res))

theorem progEffSpec_postBytes {σ : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {EffOk : ServerEffect → Prop} {Post : Except ApiError Bytes → Prop}
    (url : WebhookUrl) (mime : String) (body : Bytes)
    (hHttp : ∀ req, EffOk (.httpCall req)) (hPost : ∀ r, Post r) :
    ProgEffSpec Inv A Step EffOk Post (postBytes (m := ThreadProg σ) url mime body) :=
  (progEffSpec_postRaw url _ _ hHttp fun _ => trivial).bind fun res _ => .pure _ (hPost (decodeRespBytes res))

end Webhook

/-! ## `external` Command Elaborator -/

private inductive UrlSegPiece where | lit (s : String) | param (name : String) deriving Inhabited
private inductive UrlSegSpec where | lit (s : String) | singleParam (name : String) | multiParam (name : String) | compound (pieces : Array UrlSegPiece)
private inductive QueryValSpec where | lit (s : String) | param (name : String)

private inductive ExtParamKind where | plain | header (wireName : String) | query (wireName : String) deriving BEq

private structure ParsedExtParam where
  ref   : Lean.Syntax
  kind  : ExtParamKind
  ident : Lean.Ident
  ty    : Qed.Lang.LoweredQedType

section ExternalElab
open Lean Elab Command

@[noinline]
private def parseUrlTemplate (ref : Syntax) (tmpl : String) : CommandElabM (Array UrlSegSpec × Array (String × QueryValSpec) × Array String) := do
  if tmpl.contains '#' then throwErrorAt ref "external endpoint URL template must not contain `#` fragments"
  if !tmpl.startsWith "/" then throwErrorAt ref s!"external endpoint path `{tmpl}` must start with `/`"
  let qParts := tmpl.splitOn "?"
  if qParts.length > 2 then throwErrorAt ref s!"external endpoint path `{tmpl}` has multiple `?` query delimiters"
  let mut segSpecs : Array UrlSegSpec := #[]; let mut querySpecs : Array (String × QueryValSpec) := #[]
  let phRef ← IO.mkRef (#[] : Array String)
  let registerPh (raw kindDesc : String) (allowWildcard : Bool) : CommandElabM (String × Bool) := do
    let isMulti := raw.endsWith "*"
    if isMulti && !allowWildcard then throwErrorAt ref s!"wildcard placeholder `*{raw}` is not allowed in {kindDesc} in `{tmpl}`"
    let pname := if isMulti then String.ofList (raw.toList.take (raw.length - 1)) else raw
    if pname.isEmpty then throwErrorAt ref s!"empty {kindDesc} placeholder in `{tmpl}`"
    if (← phRef.get).contains pname then throwErrorAt ref s!"duplicate placeholder `{pname}` in `{tmpl}`"
    phRef.modify (·.push pname); return (pname, isMulti)
  let parseBraceSeg (seg : String) : CommandElabM UrlSegSpec := do
    let mut pieces : Array UrlSegPiece := #[]
    let mut curLit : Array Char := #[]
    let mut curPh : Array Char := #[]
    let mut inBrace := false
    let mut wildName? : Option String := none
    for c in seg.toList do
      if inBrace then
        if c == '{' then throwErrorAt ref s!"nested `\{` in URL path segment `{seg}` of `{tmpl}`"
        else if c == '}' then
          let raw := String.ofList curPh.toList
          let (pn, isMulti) ← registerPh raw "`{...}`" true
          if isMulti then wildName? := some pn
          pieces := pieces.push (.param pn); curPh := #[]; inBrace := false
        else curPh := curPh.push c
      else
        if c == '}' then throwErrorAt ref s!"unmatched `}` in URL path segment `{seg}` of `{tmpl}`"
        else if c == '{' then
          if !curLit.isEmpty then
            let lit := String.ofList curLit.toList
            unless lit.toList.all isSafeLitSegChar do throwErrorAt ref s!"invalid static URL path text `{lit}` in `{tmpl}`"
            pieces := pieces.push (.lit lit); curLit := #[]
          inBrace := true
        else curLit := curLit.push c
    if inBrace then throwErrorAt ref s!"unclosed `\{` in URL path segment `{seg}` of `{tmpl}`"
    if !curLit.isEmpty then
      let lit := String.ofList curLit.toList
      unless lit.toList.all isSafeLitSegChar do throwErrorAt ref s!"invalid static URL path text `{lit}` in `{tmpl}`"
      pieces := pieces.push (.lit lit)
    if let some wn := wildName? then
      if pieces.size != 1 then throwErrorAt ref s!"multi-segment wildcard `\{{wn}*}` must occupy an entire path segment in `{tmpl}`"
      return .multiParam wn
    if pieces.size == 1 then match pieces[0]! with
      | .lit s =>
          if s == "." || s == ".." then throwErrorAt ref s!"invalid static URL path segment `{seg}` in `{tmpl}`"
          return .lit s
      | .param pn => return .singleParam pn
    else return .compound pieces
  for seg in ((qParts.headD "").splitOn "/").filter (· != "") do
    if seg.contains '{' || seg.contains '}' then
      segSpecs := segSpecs.push (← parseBraceSeg seg)
    else if seg.startsWith ":" then
      let (pn, m) ← registerPh (String.ofList (seg.toList.drop 1)) "`:`" true
      segSpecs := segSpecs.push (if m then .multiParam pn else .singleParam pn)
    else
      if seg == "." || seg == ".." || !seg.toList.all isSafeLitSegChar then throwErrorAt ref s!"invalid static URL path segment `{seg}` in `{tmpl}`"
      segSpecs := segSpecs.push (.lit seg)
  for pair in ((qParts.getD 1 "").splitOn "&").filter (· != "") do
    match pair.splitOn "=" with
    | [k, v] =>
        if k.isEmpty then throwErrorAt ref s!"empty query parameter key in `{tmpl}`"
        let qv ←
          if v.startsWith ":" then do pure (.param (← registerPh (String.ofList (v.toList.drop 1)) "query" false).1)
          else if v.startsWith "{" && v.endsWith "}" && v.length >= 2 then do
            pure (.param (← registerPh (String.ofList ((v.toList.drop 1).take (v.length - 2))) "query" false).1)
          else pure (.lit v)
        querySpecs := querySpecs.push (k, qv)
    | [k] => querySpecs := querySpecs.push (k, .lit "")
    | _ => throwErrorAt ref s!"malformed query parameter `{pair}` in `{tmpl}`"
  return (segSpecs, querySpecs, ← phRef.get)

private inductive BaseVarDomain where
  | unitEnum (tyIdent : Lean.Ident) (wireVals : Array String)
  | strList  (allowed : Array String)

private structure BaseTemplateVar where
  ref    : Lean.Syntax
  ident  : Lean.Ident
  name   : String
  domain : BaseVarDomain

private structure ParsedBaseSpec where
  ref            : Lean.Syntax
  rawTemplate    : String
  pieces         : Array UrlSegPiece
  vars           : Array BaseTemplateVar
  allowedOrigins : Array String

private def ParsedBaseSpec.isStatic (b : ParsedBaseSpec) : Bool := b.vars.isEmpty
private def ParsedBaseSpec.isTotal  (b : ParsedBaseSpec) : Bool := b.vars.all fun v => match v.domain with | .unitEnum .. => true | .strList .. => false

@[noinline]
private def parseBaseTemplatePieces (ref : Syntax) (tmpl : String) : CommandElabM (Array UrlSegPiece × Array String) := do
  let mut pieces : Array UrlSegPiece := #[]; let mut vars : Array String := #[]
  let mut curLit : Array Char := #[]; let mut curVar : Array Char := #[]; let mut inBrace := false
  for c in tmpl.toList do
    if inBrace then
      if c == '{' then throwErrorAt ref s!"nested `\{` in `base` URL template `{tmpl}`"
      else if c == '}' then
        let vn := String.ofList curVar.toList
        if vn.isEmpty then throwErrorAt ref s!"empty `\{}` placeholder in `base` URL template `{tmpl}`"
        if vars.contains vn then throwErrorAt ref s!"duplicate placeholder `\{{vn}}` in `base` URL template `{tmpl}`"
        vars := vars.push vn; pieces := pieces.push (.param vn); curVar := #[]; inBrace := false
      else curVar := curVar.push c
    else
      if c == '}' then throwErrorAt ref s!"unmatched `}` in `base` URL template `{tmpl}`"
      else if c == '{' then
        if !curLit.isEmpty then pieces := pieces.push (.lit (String.ofList curLit.toList)); curLit := #[]
        inBrace := true
      else curLit := curLit.push c
  if inBrace then throwErrorAt ref s!"unclosed `\{` in `base` URL template `{tmpl}`"
  if !curLit.isEmpty then pieces := pieces.push (.lit (String.ofList curLit.toList))
  return (pieces, vars)

private def expandBaseOrigins (ref : Syntax) (svcName : Name) (pieces : Array UrlSegPiece) (vars : Array BaseTemplateVar) :
    CommandElabM (Array String) := do
  let mut acc : Array (Array (String × String)) := #[#[]]
  for v in vars do
    let vals := match v.domain with | .unitEnum _ ws => ws | .strList ws => ws
    if acc.size * vals.size > 256 then
      throwErrorAt ref s!"`external {svcName}` `base` allowlist exceeds maximum of 256 origin combinations"
    let mut next : Array (Array (String × String)) := #[]
    for env in acc do for val in vals do next := next.push (env.push (v.name, val))
    acc := next
  return acc.map fun env =>
    pieces.foldl (init := "") fun s pc =>
      match pc with
      | .lit l => s ++ l
      | .param pn => s ++ (env.find? (·.1 == pn) |>.map Prod.snd |>.getD "")

@[noinline]
private def parseExternalClauses (svcIdent : Ident) (svcName : Name) (clauses : Array Syntax) :
    CommandElabM (ParsedBaseSpec × AuthSpec × Bool × Array Syntax × Array Syntax) := do
  let mut baseSpec? : Option ParsedBaseSpec := none; let mut authSpec : AuthSpec := .none
  let mut hasAuth := false; let mut ssrfGuard? : Option Bool := none
  let mut epClauses : Array Syntax := #[]; let mut wsClauses : Array Syntax := #[]
  for c in clauses do
    let k := c.getKind
    if k == ``extBaseClause then
      if baseSpec?.isSome then throwErrorAt c s!"duplicate `base` clause in `external {svcName}`"
      let rawBase := (⟨c.getArg 1⟩ : TSyntax `str).getString
      let trimmed := if rawBase.endsWith "/" then String.ofList (rawBase.toList.take (rawBase.length - 1)) else rawBase
      let optWhere := c.getArg 2
      let (pieces, phNames) ← parseBaseTemplatePieces (c.getArg 1) trimmed
      if optWhere.getNumArgs == 0 then
        if let some pn := phNames[0]? then
          throwErrorAt c s!"`base` URL placeholder `\{{pn}}` in `external {svcName}` has no matching `where {pn} : Enum` or `where {pn} in [...]` allowlist"
        unless isValidWsBaseOrigin trimmed do throwErrorAt c s!"invalid `base` URL `{rawBase}`: expected pinned `https://`, `http://`, `wss://`, or `ws://` origin without `?`, `#`, `@`, or `\\`"
        baseSpec? := some { ref := c, rawTemplate := trimmed, pieces := #[.lit trimmed], vars := #[], allowedOrigins := #[trimmed] }
      else
        if phNames.isEmpty then throwErrorAt optWhere s!"`base \"{rawBase}\" where ...` has no `\{var}` placeholders in the base URL"
        let rawWheres := (optWhere.getArg 1).getSepArgs
        let mut vars : Array BaseTemplateVar := #[]
        for w in rawWheres do
          let wk := w.getKind
          if wk == `Qed.Server.extBaseWhereEnum then
            let vId : Ident := ⟨w.getArg 0⟩; let vName := vId.getId.eraseMacroScopes.toString
            let tyId : Ident := ⟨w.getArg 2⟩
            if vars.any (·.name == vName) then throwErrorAt vId s!"duplicate `where` constraint for `{vName}` in `base` of `external {svcName}`"
            let some uInfo := Qed.lookupUnitEnum? (← getEnv) (← getCurrNamespace) (← getOpenDecls) tyId.getId
              | throwErrorAt tyId s!"type `{tyId.getId}` in `base ... where {vName} : {tyId.getId}` must be a unit `enum` (without variant payloads)"
            if uInfo.variants.isEmpty then throwErrorAt tyId s!"enum `{tyId.getId}` has no variants"
            vars := vars.push { ref := w, ident := vId, name := vName, domain := .unitEnum tyId uInfo.variants }
          else if wk == `Qed.Server.extBaseWhereIn then
            let vId : Ident := ⟨w.getArg 0⟩; let vName := vId.getId.eraseMacroScopes.toString
            if vars.any (·.name == vName) then throwErrorAt vId s!"duplicate `where` constraint for `{vName}` in `base` of `external {svcName}`"
            let mut vals : Array String := #[]
            for sStx in (w.getArg 3).getSepArgs do
              let sVal := (⟨sStx⟩ : TSyntax `str).getString
              if sVal.isEmpty then throwErrorAt sStx s!"empty string literal in `where {vName} in [...]` of `external {svcName}`"
              if vals.contains sVal then throwErrorAt sStx s!"duplicate value `{sVal}` in `where {vName} in [...]` of `external {svcName}`"
              vals := vals.push sVal
            vars := vars.push { ref := w, ident := vId, name := vName, domain := .strList vals }
          else throwErrorAt w s!"unexpected `where` item in `base` of `external {svcName}`"
        for pn in phNames do
          unless vars.any (·.name == pn) do throwErrorAt c s!"`base` URL placeholder `\{{pn}}` in `external {svcName}` has no matching `where {pn} : Enum` or `where {pn} in [...]` allowlist"
        for v in vars do
          unless phNames.contains v.name do throwErrorAt v.ref s!"`where` variable `{v.name}` is not referenced as `\{{v.name}}` in `base \"{rawBase}\"`"
        let allowedOrigins ← expandBaseOrigins c svcName pieces vars
        for orig in allowedOrigins do
          unless isValidWsBaseOrigin orig do
            throwErrorAt c s!"invalid expanded `base` origin `{orig}` in `external {svcName}`: every allowed origin must be a valid `https://`, `http://`, `wss://`, or `ws://` origin without `?`, `#`, `@`, or `\\`"
        baseSpec? := some { ref := c, rawTemplate := trimmed, pieces, vars, allowedOrigins }
    else if k == ``extSsrfGuardClause then
      if ssrfGuard?.isSome then throwErrorAt c s!"duplicate `ssrf_guard` clause in `external {svcName}`"
      let optVal := c.getArg 1
      let enabled := if optVal.getNumArgs == 1 then (optVal.getArg 0).getId.eraseMacroScopes != `false else true
      ssrfGuard? := some enabled
    else if k == ``extAuthBearer || k == ``extAuthHeader || k == ``extAuthGcp || k == ``extAuthGcpMeta then
      if hasAuth then throwErrorAt c s!"duplicate `auth` clause in `external {svcName}`"
      hasAuth := true
      let checkEnv (stx : Syntax) : CommandElabM String := do
        let v := (⟨stx⟩ : TSyntax `str).getString
        unless isValidEnvVarName v do throwErrorAt stx s!"invalid secret environment variable name `{v}`: must be non-empty and contain only ASCII letters, digits, or `_`"
        return v
      if k == ``extAuthBearer then authSpec := .bearerSecret (← checkEnv (c.getArg 5))
      else if k == ``extAuthHeader then
        let hdrName := (⟨c.getArg 3⟩ : TSyntax `str).getString
        if hdrName.isEmpty then throwErrorAt (c.getArg 3) "header name cannot be empty"
        authSpec := .headerSecret hdrName (← checkEnv (c.getArg 7))
      else if k == ``extAuthGcp then
        authSpec := .gcpServiceAccount (← checkEnv (c.getArg 5)) (if (c.getArg 7).getNumArgs == 2 then (⟨(c.getArg 7).getArg 1⟩ : TSyntax `str).getString else "https://www.googleapis.com/auth/cloud-platform")
      else
        let aud? : Option String := if (c.getArg 2).getNumArgs == 3 then some (⟨(c.getArg 2).getArg 1⟩ : TSyntax `str).getString else none
        authSpec := .gcpMetadata aud?
    else if k == ``extEndpointClause then epClauses := epClauses.push c
    else if k == ``extWsClause then wsClauses := wsClauses.push c
    else throwErrorAt c "unexpected clause in `external` block"
  let some baseSpec := baseSpec? | throwErrorAt svcIdent s!"`external {svcName}` must declare `base \"https://...\"` or `base \"wss://...\"`"
  if epClauses.isEmpty && wsClauses.isEmpty then throwErrorAt svcIdent s!"`external {svcName}` must declare at least one HTTP endpoint or `ws` channel"
  if ssrfGuard?.isSome && epClauses.isEmpty then throwErrorAt svcIdent s!"`ssrf_guard` in `external {svcName}` applies to server-side HTTP endpoints"
  if !epClauses.isEmpty then
    for orig in baseSpec.allowedOrigins do
      unless isValidBaseOrigin orig do
        throwErrorAt baseSpec.ref s!"`external {svcName}` declares HTTP endpoints, so every allowed `base` origin must use `https://` or `http://` (got `{orig}`)"
  if !wsClauses.isEmpty && !baseSpec.isStatic then
    throwErrorAt baseSpec.ref s!"multi-origin `base ... where ...` in `external {svcName}` is only supported for HTTP endpoints (not client `ws` channels)"
  if !wsClauses.isEmpty && hasAuth then throwErrorAt svcIdent s!"`external {svcName}` declares client-usable `ws` channels and cannot attach server `auth` secrets; split server-authenticated HTTP endpoints into a separate `external` block"
  return (baseSpec, authSpec, ssrfGuard?.getD true, epClauses, wsClauses)

private def lowerUrlParts (ref : Syntax) (segSpecs : Array UrlSegSpec) (querySpecs : Array (String × QueryValSpec)) (paramIdents : Array Ident) :
    CommandElabM (Array Term × Array Term) := do
  let findParam (pn : String) : CommandElabM Ident := do
    let some pid := paramIdents.find? (·.getId.toString == pn) | throwErrorAt ref "internal missing URL param"
    return pid
  let paramSeg (pn : String) : CommandElabM Term := do `(Qed.RouteParam.toSeg $(← findParam pn))
  let pathTerms ← segSpecs.mapM fun
    | .lit s => `(Qed.Server.PathPart.lit $(Syntax.mkStrLit s))
    | .singleParam pn => do `(Qed.Server.PathPart.seg $(← paramSeg pn))
    | .multiParam pn => do `(Qed.Server.PathPart.multiSeg $(← paramSeg pn))
    | .compound pieces => do
        let pTerms ← pieces.mapM fun
          | .lit s => `(Qed.Server.SegPiece.lit $(Syntax.mkStrLit s))
          | .param pn => do `(Qed.Server.SegPiece.param $(← paramSeg pn))
        `(Qed.Server.PathPart.compound [$[$pTerms],*])
  let queryTerms ← querySpecs.mapM fun (qk, qv) => do
    match qv with
    | .lit s => `(($(Syntax.mkStrLit qk), Qed.Server.QueryVal.lit $(Syntax.mkStrLit s)))
    | .param pn => do `(($(Syntax.mkStrLit qk), Qed.Server.ToQueryVal.toQueryVal $(← findParam pn)))
  return (pathTerms, queryTerms)

private def parseTypedParams (ctxLabel : String) (rawParams : Array Syntax) (allowExtKinds := false) (paramKind := "parameter") : CommandElabM (Array ParsedExtParam) := do
  let mut out : Array ParsedExtParam := #[]; let mut seen : Array String := #[]
  for rp in rawParams do
    let pk := rp.getKind
    let (kind, pid, tyNode) ←
      if allowExtKinds && pk == ``extParamHeader then pure (.header (⟨rp.getArg 2⟩ : TSyntax `str).getString, (⟨rp.getArg 4⟩ : Ident), rp.getArg 6)
      else if allowExtKinds && pk == ``extParamQuery then
        let pid : Ident := ⟨rp.getArg 2⟩
        let wireName := if (rp.getArg 1).getNumArgs == 3 then (⟨(rp.getArg 1).getArg 1⟩ : TSyntax `str).getString else pid.getId.toString
        if wireName.isEmpty then throwErrorAt rp s!"query parameter wire name cannot be empty in {ctxLabel}"
        pure (.query wireName, pid, rp.getArg 4)
      else if !allowExtKinds || pk == ``extParamPlain then pure (.plain, (⟨rp.getArg 0⟩ : Ident), rp.getArg 2)
      else throwErrorAt rp "invalid endpoint parameter"
    let pstr := pid.getId.toString
    if seen.contains pstr then throwErrorAt pid s!"duplicate {paramKind} `{pstr}` in {ctxLabel}"
    seen := seen.push pstr
    out := out.push { ref := rp, kind, ident := pid, ty := ← liftMacroM <| lowerSrvType tyNode false s!"{paramKind} `{pstr}`" }
  return out

private def classifyExtWsCodec (ty : Qed.Lang.LoweredQedType) : Qed.ExtWsCodec :=
  if ty.isProto then .proto else if ty.mods.isEmpty && (ty.baseName == `Bytes || ty.baseName == `ByteArray) then .bytes
  else if ty.mods.isEmpty && ty.baseName == `String then .text else .json

private def isUnitExtType (ty : Qed.Lang.LoweredQedType) : Bool := !ty.isProto && !ty.isForm && ty.mods.isEmpty && ty.baseName == `Unit

theorem validOrigin_of_ok {s orig : String} (hs : isValidBaseOrigin s = true)
    (h : (Except.ok s : Except ApiError String) = .ok orig) : isValidBaseOrigin orig = true := by
  cases h; exact hs

theorem validOrigin_of_ite {P : Prop} [Decidable P] {a b : Except ApiError String} {orig : String}
    (ha : a = .ok orig → isValidBaseOrigin orig = true)
    (hb : b = .ok orig → isValidBaseOrigin orig = true)
    (h : (if P then a else b) = .ok orig) : isValidBaseOrigin orig = true := by
  by_cases hp : P
  · simp only [hp, ↓reduceIte] at h; exact ha h
  · simp only [hp, ↓reduceIte] at h; exact hb h

@[noinline]
private def elabBaseOriginResolver (svcIdent : Ident) (svcName : Name) (baseSpec : ParsedBaseSpec) : CommandElabM (Option Ident) := do
  if baseSpec.isStatic then return none
  let allowedId := mkIdentFrom svcIdent (svcName ++ `allowedBaseOrigins)
  let resolveId := mkIdentFrom svcIdent (svcName ++ `resolveBaseOrigin)
  let validId := mkIdentFrom svcIdent (svcName ++ `resolveBaseOrigin_valid)
  elabCommand (← `(command| @[noinline] def $allowedId : Array String := $(quote baseSpec.allowedOrigins)))
  let vIds : Array Ident := baseSpec.vars.map (·.ident)
  let vIdTerms : Array Term := vIds.map (⟨·.raw⟩)
  let vTys : Array Term ← baseSpec.vars.mapM fun v => match v.domain with
    | .unitEnum tyId _ => pure ⟨tyId.raw⟩
    | .strList _ => `(String)
  let mkConcatTerm (subst : Array (String × String)) : CommandElabM Term := do
    let mut parts : Array (Sum String Term) := #[]
    for pc in baseSpec.pieces do
      let item : Sum String Term ← match pc with
        | .lit s => pure (.inl s)
        | .param pn =>
            match subst.find? (·.1 == pn) with
            | some (_, val) => pure (.inl val)
            | none =>
                let vId := baseSpec.vars.find? (·.name == pn) |>.map (·.ident) |>.getD (mkIdent (Name.mkSimple pn))
                pure (.inr (← `(Qed.StringEnum.toWire $vId)))
      match parts.back?, item with
      | some (.inl prev), .inl cur => parts := parts.pop.push (.inl (prev ++ cur))
      | _, _ => parts := parts.push item
    let partTerms : Array Term := parts.map fun | .inl s => (Syntax.mkStrLit s : Term) | .inr t => t
    match partTerms.toList with
    | [] => pure (Syntax.mkStrLit "" : Term)
    | p :: ps => ps.foldlM (init := p) fun acc x => `($acc ++ $x)
  let enumVIds := baseSpec.vars.filterMap fun v => match v.domain with | .unitEnum .. => some v.ident | .strList _ => none
  let casesTacs ← enumVIds.mapM fun eId => `(tactic| all_goals cases $eId:ident)
  if baseSpec.isTotal then
    let bodyT ← mkConcatTerm #[]
    elabCommand (← `(command| def $resolveId $[($vIds:ident : $vTys:term)]* : String := $bodyT))
    elabCommand (← `(command|
      theorem $validId $[($vIds:ident : $vTys:term)]* : Qed.Server.isValidBaseOrigin ($resolveId $vIdTerms*) = true := by
        unfold $resolveId
        $[$casesTacs:tactic]*
        all_goals decide))
  else
    let strVars := baseSpec.vars.filter fun v => match v.domain with | .strList _ => true | .unitEnum .. => false
    let origId := mkIdent `_orig; let hId := mkIdent `_h
    let rec buildBranch (idx : Nat) (subst : Array (String × String)) : CommandElabM (Term × Term) := do
      if h : idx < strVars.size then
        let sv := strVars[idx]
        let .strList allowed := sv.domain | unreachable!
        let errMsg := Syntax.mkStrLit s!"disallowed value for `{sv.name}` in `external {svcName}` base URL"
        let initErr ← `(Except.error (Qed.Server.ApiError.badRequest $errMsg))
        let initPf ← `(fun _he => by cases _he)
        allowed.foldrM (init := (initErr, initPf)) fun val (accTerm, accPf) => do
          let (okArm, okPf) ← buildBranch (idx + 1) (subst.push (sv.name, val))
          let t' ← `(if $(sv.ident) == $(Syntax.mkStrLit val) then $okArm else $accTerm)
          let pf' ← `(Qed.Server.validOrigin_of_ite $okPf $accPf)
          pure (t', pf')
      else
        let cTerm ← mkConcatTerm subst
        let decPf ← if casesTacs.isEmpty then `(by decide) else `(by $[$casesTacs:tactic];*; all_goals decide)
        let leafPf ← `(Qed.Server.validOrigin_of_ok (s := $cTerm) $decPf)
        pure (← `(Except.ok $cTerm), leafPf)
    let (bodyT, bodyPf) ← buildBranch 0 #[]
    elabCommand (← `(command| def $resolveId $[($vIds:ident : $vTys:term)]* : Except Qed.Server.ApiError String := $bodyT))
    elabCommand (← `(command|
      theorem $validId $[($vIds:ident : $vTys:term)]* ($origId:ident : String) ($hId:ident : $resolveId $vIdTerms* = Except.ok $origId) :
          Qed.Server.isValidBaseOrigin $origId = true := $bodyPf $hId))
  return some resolveId

@[noinline]
private def elabExternalEndpoint (svcName : Name) (svcStrLit : StrLit) (baseId : Ident) (baseSpec : ParsedBaseSpec)
    (resolveBaseId? : Option Ident) (authTerm : Term) (ssrfGuard : Bool) (methodNames : Array Name) (ep : Syntax) : CommandElabM Name := do
  let httpVerbRaw := (ep.getArg 0).getId.toString.toUpper; let urlTmpl := (⟨ep.getArg 1⟩ : TSyntax `str).getString
  let fnIdent : Ident := ⟨ep.getArg 2⟩; let fnName := fnIdent.getId
  if methodNames.contains fnName then throwErrorAt fnIdent s!"duplicate endpoint `{fnName}` in `external {svcName}`"
  let parsedParams ← parseTypedParams s!"endpoint `{fnName}`" (ep.getArg 4).getSepArgs true
  let retTy ← liftMacroM <| lowerSrvType (ep.getArg 7) false "external endpoint return types (external calls are automatically fallible at `await`; write `-> T` instead of `-> T!`)"
  if retTy.isForm then throwErrorAt (ep.getArg 7) "`Form(T)` is only supported for HTTP request body parameters, not response types"
  let okStatusList ← if (ep.getArg 8).getNumArgs == 4 then
      ((ep.getArg 8).getArg 2).getSepArgs.mapM fun nStx => do
        let n := (⟨nStx⟩ : TSyntax `num).getNat
        unless 100 ≤ n && n < 600 do throwErrorAt nStx s!"HTTP status code `{n}` in `ok [...]` must be between 100 and 599"
        pure (n.toUInt32)
    else pure #[]
  let (segSpecs, querySpecs, placeholders) ← parseUrlTemplate (ep.getArg 1) urlTmpl
  let baseVarNames := baseSpec.vars.map (·.name)
  let mut baseArgIdents : Array Ident := #[]
  for bv in baseSpec.vars do
    let some bp := parsedParams.find? fun p => p.kind == .plain && p.ident.getId.toString == bv.name
      | throwErrorAt fnIdent s!"`base` URL placeholder `\{{bv.name}}` in `external {svcName}` requires a matching parameter `{bv.name}` on endpoint `{fnName}`"
    match bv.domain with
    | .strList _ =>
        unless bp.ty.mods.isEmpty && !bp.ty.isProto && !bp.ty.isForm && bp.ty.baseName == `String do
          throwErrorAt bp.ref s!"`base` allowlist parameter `{bv.name}` on `{fnName}` must have type `String`"
    | .unitEnum tyId _ =>
        if bp.ty.isForm || bp.ty.isProto || !bp.ty.mods.isEmpty then
          throwErrorAt bp.ref s!"`base` enum parameter `{bv.name}` on `{fnName}` must have type `{tyId.getId}`"
    baseArgIdents := baseArgIdents.push bp.ident
  for ph in placeholders do
    unless parsedParams.any fun p => p.kind == .plain && p.ident.getId.toString == ph do
      throwErrorAt (ep.getArg 1) s!"URL placeholder `{ph}` has no matching plain parameter `{ph}` in `{fnName}`"
  let mut bodyParam? : Option ParsedExtParam := none
  for p in parsedParams do
    match p.kind with
    | .header _ | .query _ =>
        if p.ty.isForm then throwErrorAt p.ref "`Form(T)` is only supported for HTTP request body parameters"
    | .plain =>
        let pNm := p.ident.getId.toString
        if !placeholders.contains pNm && !baseVarNames.contains pNm then
          if httpVerbRaw == "GET" || httpVerbRaw == "DELETE" then throwErrorAt p.ref s!"parameter `{p.ident.getId}` on `{httpVerbRaw}` endpoint `{fnName}` is not referenced as `:{p.ident.getId}` or `\{{p.ident.getId}}` in `{urlTmpl}` (or mark it `query`)"
          if let some prev := bodyParam? then throwErrorAt p.ref s!"endpoint `{fnName}` has multiple request body parameters (`{prev.ident.getId}` and `{p.ident.getId}`); bundle them into a `schema` type"
          bodyParam? := some p
        else if p.ty.isForm then
          throwErrorAt p.ref "`Form(T)` cannot be used as a URL path or query placeholder"
  let (pIdents, pTyTerms) := (parsedParams.map (·.ident), parsedParams.map (·.ty.term))
  let (pathTerms, tmplQueryTerms) ← lowerUrlParts (ep.getArg 1) segSpecs querySpecs ((parsedParams.filter (·.kind == .plain)).map (·.ident))
  let paramQueryTerms ← (parsedParams.filterMap fun p => match p.kind with | .query qk => some (qk, p.ident) | _ => none).mapM fun (qk, pid) =>
    `(($(Syntax.mkStrLit qk), Qed.Server.ToQueryVal.toQueryVal $pid))
  let queryTerms := tmplQueryTerms ++ paramQueryTerms
  let customHdrOptTerms ← (parsedParams.filterMap fun p => match p.kind with | .header hk => some (hk, p.ident) | _ => none).mapM fun (hk, pid) =>
    `((Qed.Server.ToHeaderVal.toHeaderVal? $pid).map fun _hv => ($(Syntax.mkStrLit hk), _hv))
  let customHdrsTerm ← if customHdrOptTerms.isEmpty then `(([] : List (String × String))) else `(List.filterMap id [$[$customHdrOptTerms],*])
  let retPayloadTerm := retTy.term
  let (acceptHdr, decodeCall) ← if isUnitExtType retTy then pure (none, ← `(Qed.Server.decodeRespUnit rawRes)) else match classifyExtWsCodec retTy with
    | .proto => pure (some ("Accept", "application/x-protobuf"), ← `(Qed.Server.decodeRespProto (α := $retPayloadTerm) rawRes))
    | .bytes => pure (none, ← `(Qed.Server.decodeRespBytes rawRes))
    | .text  => pure (none, ← `(Qed.Server.decodeRespString rawRes))
    | .json  => pure (some ("Accept", "application/json"), ← `(Qed.Server.decodeRespJson (α := $retPayloadTerm) rawRes))
  let (bodyTerm, ctHdr) ← match bodyParam? with
    | none => pure (← `(ByteArray.empty), (none : Option (String × String)))
    | some bp =>
        if bp.ty.isForm then pure (← `(Qed.Server.encodeFormBodyOf $(bp.ident)), some ("Content-Type", "application/x-www-form-urlencoded"))
        else if isUnitExtType bp.ty then pure (← `(ByteArray.empty), none) else match classifyExtWsCodec bp.ty with
          | .proto => pure (← `(Qed.Proto.encode $(bp.ident)), some ("Content-Type", "application/x-protobuf"))
          | .bytes => pure (← `(($(bp.ident) : ByteArray)), some ("Content-Type", "application/octet-stream"))
          | .text | .json => pure (← `((Qed.Json.render (Qed.toJson $(bp.ident))).toUTF8), some ("Content-Type", "application/json"))
  let defHdrTerms ← (#[ctHdr, acceptHdr].filterMap id).mapM fun (k, v) => `(($(Syntax.mkStrLit k), $(Syntax.mkStrLit v)))
  let okTerms ← okStatusList.mapM fun code => `(($(quote code.toNat) : UInt32))
  let fullFnId := mkIdentFrom fnIdent (svcName ++ fnName)
  let mkExecCall (originExpr : Term) : CommandElabM Term := `(do
    let rawRes ← Qed.Server.execExternalRaw $svcStrLit $originExpr $(Syntax.mkStrLit httpVerbRaw) [$[$pathTerms],*] [$[$queryTerms],*] [$[$defHdrTerms],*] $customHdrsTerm $bodyTerm $authTerm $(quote ssrfGuard) [$[$okTerms],*]
    return $decodeCall)
  let (fnBody, safeIoTac) : Term × TSyntax ``Lean.Parser.Tactic.tacticSeq ← match resolveBaseId? with
    | none => pure (← mkExecCall ⟨baseId.raw⟩, ← `(Lean.Parser.Tactic.tacticSeq| unfold $fullFnId; exact (inferInstance : Qed.Server.SafeIO _).noAtomic))
    | some resId =>
        let resCall ← Qed.Lang.mkAppTerms ⟨resId.raw⟩ (baseArgIdents.map (⟨·.raw⟩))
        if baseSpec.isTotal then
          pure (← mkExecCall resCall, ← `(Lean.Parser.Tactic.tacticSeq| unfold $fullFnId; exact (inferInstance : Qed.Server.SafeIO _).noAtomic))
        else
          let okCall ← mkExecCall (← `(_baseOrig))
          let bodyT ← `(match $resCall:term with
            | Except.error _baseErr => Pure.pure (Except.error _baseErr)
            | Except.ok _baseOrig => $okCall)
          let tac ← `(Lean.Parser.Tactic.tacticSeq|
            unfold $fullFnId
            cases ($resCall : Except Qed.Server.ApiError String) with
            | error _baseErr => exact Qed.Server.NoAtomic.pure (Except.error _baseErr)
            | ok _baseOrig => exact (inferInstance : Qed.Server.SafeIO _).noAtomic)
          pure (bodyT, tac)
  elabCommand (← `(command|
    @[specialize] def $fullFnId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m] $[($pIdents:ident : $pTyTerms:term)]* :
        m (Except Qed.Server.ApiError $retPayloadTerm) := $fnBody))
  let fullFnCall ← Qed.Lang.mkAppTerms (← `($fullFnId)) (pIdents.map (⟨·.raw⟩))
  elabCommand (← `(command|
    instance {_σ : Type} $[($pIdents:ident : $pTyTerms:term)]* : Qed.Server.SafeIO ($fullFnCall : Qed.Server.ThreadProg _σ (Except Qed.Server.ApiError $retPayloadTerm)) where
      noAtomic := by $safeIoTac))
  return fnName

private def elabExtReqPred (chIdent : Ident) (svcName fullSvcName chName : Name) (suffix : String)
    (pIdents : Array Ident) (pTyTerms : Array Term) (reqExprs : Array Syntax) : CommandElabM (Option Name × String) := do
  if reqExprs.isEmpty then return (none, "")
  let props ← reqExprs.mapM fun e => liftMacroM <| Qed.Lang.lowerSimpleQedExpr .propInv e
  let conj ← Qed.mkConjBody props (ascribeProp := false)
  let predId := mkIdentFrom chIdent (svcName ++ chName.appendAfter suffix)
  elabCommand (← `(command| set_option linter.unusedVariables false in @[simp] abbrev $predId $[($pIdents:ident : $pTyTerms:term)]* : Prop := $conj))
  return (some (fullSvcName ++ chName.appendAfter suffix), String.intercalate " && " (reqExprs.toList.map fun e => (e.reprint.getD "requires").trimAscii.toString))

@[noinline]
private def elabExternalWsChannel (svcName fullSvcName : Name) (svcNameStr : String) (baseId : Ident) (existingNames : Array Name) (wsStx : Syntax) : CommandElabM Name := do
  let urlTmpl := (⟨wsStx.getArg 1⟩ : TSyntax `str).getString; let chIdent : Ident := ⟨wsStx.getArg 2⟩; let chName := chIdent.getId
  if existingNames.contains chName then throwErrorAt chIdent s!"duplicate channel/endpoint `{chName}` in `external {svcName}`"
  let parsedParams ← parseTypedParams s!"`ws {chName}`" (wsStx.getArg 4).getSepArgs
  let (pIdents, pTyTerms) := (parsedParams.map (·.ident), parsedParams.map (·.ty.term)); let seenP := pIdents.map (·.getId.toString)
  let evTy ← liftMacroM <| lowerSrvType (wsStx.getArg 7) false s!"event type of `ws {chName}`"
  if evTy.isForm then throwErrorAt (wsStx.getArg 7) "`Form(T)` is only supported for HTTP request body parameters"
  let evTyTerm := evTy.term; let evCodec := classifyExtWsCodec evTy; let isBinary := evCodec == .proto || evCodec == .bytes
  let (segSpecs, querySpecs, placeholders) ← parseUrlTemplate (wsStx.getArg 1) urlTmpl
  for ph in placeholders do unless seenP.contains ph do throwErrorAt (wsStx.getArg 1) s!"WebSocket URL placeholder `:{ph}` has no matching parameter `{ph}` in `{chName}`"
  for p in pIdents do unless placeholders.contains p.getId.toString do throwErrorAt p s!"parameter `{p.getId}` on `ws {chName}` is not referenced as `:{p.getId}` in `{urlTmpl}`"
  let mut reqExprs : Array Syntax := #[]; let mut sendParams : Array ParsedExtParam := #[]; let mut sendReqExprs : Array Syntax := #[]
  let mut hasSend := false; let mut recPolicy : Qed.Reconnect := .defaultPolicy; let mut hasRec := false
  if (wsStx.getArg 8).getNumArgs == 2 then
    for sub in ((wsStx.getArg 8).getArg 1).getArgs do
      let sk := sub.getKind
      if sk == ``extWsReqClause then reqExprs := reqExprs ++ ((sub.getArg 0).getArg 1).getSepArgs
      else if sk == ``extWsReconnectClause then
        if hasRec then throwErrorAt sub s!"duplicate `reconnect` clause in `ws {chName}`"
        hasRec := true; recPolicy ← liftMacroM <| Qed.parseReconnectExpr (sub.getArg 1)
      else if sk == ``extWsSendClause then
        if hasSend then throwErrorAt sub s!"duplicate `send` clause in `ws {chName}`"
        hasSend := true; sendParams ← parseTypedParams s!"`ws {chName}`" (sub.getArg 2).getSepArgs false "send parameter"
        if (sub.getArg 4).getNumArgs == 2 then sendReqExprs := ((sub.getArg 4).getArg 1).getArgs.flatMap fun srl => (srl.getArg 1).getSepArgs
      else throwErrorAt sub s!"unexpected clause in `ws {chName}`"
  if hasSend && sendParams.size != 1 then throwErrorAt chIdent s!"3rd-party `ws {chName}` `send(...)` expects a single payload parameter (bundle multiple fields into a `schema`)"
  let (pathTerms, queryTerms) ← lowerUrlParts (wsStx.getArg 1) segSpecs querySpecs pIdents
  let mkCh (s : String) := mkIdentFrom chIdent (svcName ++ chName.appendAfter s)
  let (evId, keyId, subId, unsubId, slotId, recId, onJoinId, onMsgId, onStatusId) :=
    (mkCh "_Event", mkCh "_key", mkCh "_sub", mkCh "_unsub", mkIdent `slot, mkIdent `rec, mkIdent `onJoin, mkIdent `onMsg, mkIdent `onStatus)
  elabCommand (← `(command| abbrev $evId : Type := $evTyTerm))
  let paramTypeConsts ← elabParamTypeAbbrevs chIdent svcName fullSvcName chName "_Param_" pTyTerms
  let (reqConst?, reqLabel) ← elabExtReqPred chIdent svcName fullSvcName chName "_req" pIdents pTyTerms reqExprs
  elabCommand (← `(command| def $keyId $[($pIdents:ident : $pTyTerms:term)]* : String := (Qed.Server.buildExternalWsUrl $baseId [$[$pathTerms],*] [$[$queryTerms],*]).toOption.getD ""))
  let mkUnexp (kind : String) : CommandElabM Term := `(fun _ => $onStatusId (Qed.SocketStatus.failed $(Syntax.mkStrLit s!"unexpected {kind} WebSocket frame")))
  let (onTextT, onBytesT) ← match evCodec with
    | .text  => pure (← `($onMsgId), ← mkUnexp "binary")
    | .json  => pure (← mkWsDecodeCb onMsgId onStatusId fun r => `((Qed.Json.parse $r 128).bind (Qed.FromJson.fromJson (α := $evTyTerm))), ← mkUnexp "binary")
    | .bytes => pure (← mkUnexp "text", ← `($onMsgId))
    | .proto => pure (← mkUnexp "text", ← mkWsDecodeCb onMsgId onStatusId fun bs => `(Qed.Proto.decode (α := $evTyTerm) $bs))
  let keyApp ← Qed.Lang.mkAppTerms keyId (pIdents.map (⟨·.raw⟩))
  elabCommand (← `(command|
    set_option linter.unusedVariables false in
    def $subId {msg : Type} ($slotId:ident : String) $[($pIdents:ident : $pTyTerms:term)]*
        ($recId:ident : Qed.Reconnect) ($onJoinId:ident : Unit → msg) ($onMsgId:ident : $evTyTerm → msg) ($onStatusId:ident : Qed.SocketStatus → msg) : Qed.Cmd msg :=
      let url := $keyApp; if url.isEmpty then Qed.Cmd.none else Qed.Cmd.wsExtOpen $slotId url $(quote isBinary) $recId $onJoinId $onTextT $onBytesT $onStatusId))
  elabCommand (← `(command| def $unsubId {msg : Type} ($slotId:ident : String) : Qed.Cmd msg := Qed.Cmd.wsExtClose $slotId))
  let mut sendCodec : Qed.ExtWsCodec := .json; let mut sendParamTypeConsts : Array Name := #[]
  let mut sendReqConst? : Option Name := none; let mut sendReqLabel := ""; let mut sendHelperConst : Name := .anonymous
  if let some sp := sendParams[0]? then
    if sp.ty.isForm then throwErrorAt sp.ref "`Form(T)` is only supported for HTTP request body parameters"
    let (spId, spTyTerm) := (sp.ident, sp.ty.term); sendCodec := classifyExtWsCodec sp.ty
    sendParamTypeConsts ← elabParamTypeAbbrevs chIdent svcName fullSvcName chName "_SendParam_" #[spTyTerm]
    let (sr?, sl) ← elabExtReqPred chIdent svcName fullSvcName chName "_send_req" #[spId] #[spTyTerm] sendReqExprs
    sendReqConst? := sr?; sendReqLabel := sl; sendHelperConst := fullSvcName ++ chName.appendAfter "_send"
    let sendBody : Term ← match sendCodec with
      | .text => `(Qed.Cmd.wsExtSendText $slotId $spId) | .json => `(Qed.Cmd.wsExtSendText $slotId (Qed.Json.render (Qed.toJson $spId)))
      | .bytes => `(Qed.Cmd.wsExtSendBytes $slotId $spId) | .proto => `(Qed.Cmd.wsExtSendBytes $slotId (Qed.Proto.encode $spId))
    let sendId := mkCh "_send"
    elabCommand (← `(command| def $sendId {msg : Type} ($slotId:ident : String) ($spId:ident : $spTyTerm) : Qed.Cmd msg := $sendBody))
  modifyEnv fun env => Qed.channelRegistry.addEntry env {
    ChannelInfo.mkDefault fullSvcName svcNameStr chName (.external fullSvcName isBinary evCodec sendCodec) (pIdents.map (·.getId)) paramTypeConsts recPolicy with
    hasSend, sendParamCount := sendParams.size, sendParamTypeConsts, sendReqConst := sendReqConst?, sendReqLabel,
    clientReqConst := reqConst?, clientReqLabel := reqLabel, sendHelperConst }
  return chName

@[noinline, command_elab externalCmd]
def elabExternalCmd : CommandElab := fun stx => do
  let svcIdent : Ident := ⟨stx.getArg 2⟩; let svcName := svcIdent.getId; let svcNameStr := svcName.toString
  let (baseSpec, authSpec, ssrfGuard, epClauses, wsClauses) ← parseExternalClauses svcIdent svcName (stx.getArg 4).getArgs
  let baseOrigin := baseSpec.rawTemplate
  let fullSvcName := (← getCurrNamespace) ++ svcName; let secretsList := authSpec.requiredSecrets.toArray
  let (baseId, secId, mrkId) := (mkIdentFrom svcIdent (svcName ++ `baseUrl), mkIdentFrom svcIdent (svcName ++ `secrets), mkIdentFrom svcIdent (svcName ++ `_qed_external_marker))
  let authTerm : Term ← match authSpec with
    | .none => `(Qed.Server.AuthSpec.none) | .bearerSecret v => `(Qed.Server.AuthSpec.bearerSecret $(quote v))
    | .headerSecret h v => `(Qed.Server.AuthSpec.headerSecret $(quote h) $(quote v))
    | .gcpServiceAccount v sc => `(Qed.Server.AuthSpec.gcpServiceAccount $(quote v) $(quote sc))
    | .gcpMetadata aud? => `(Qed.Server.AuthSpec.gcpMetadata $(quote aud?))
  let hdrCmds : Array Syntax := #[
    ← if secretsList.isEmpty then `(command| def $baseId : String := $(quote baseOrigin)) else `(command| @[noinline] def $baseId : String := $(quote baseOrigin)),
    ← `(command| @[noinline] def $secId : Array String := $(quote secretsList)),
    ← `(command| theorem $mrkId : True := True.intro)]
  for cmd in hdrCmds do elabCommand cmd
  let resolveBaseId? ← elabBaseOriginResolver svcIdent svcName baseSpec
  let mut methodNames : Array Name := #[]
  for ep in epClauses do methodNames := methodNames.push (← elabExternalEndpoint svcName (Syntax.mkStrLit svcNameStr) baseId baseSpec resolveBaseId? authTerm ssrfGuard methodNames ep)
  for ws in wsClauses do methodNames := methodNames.push (← elabExternalWsChannel svcName fullSvcName svcNameStr baseId methodNames ws)
  modifyEnv fun env => externalRegistry.addEntry env { serviceName := fullSvcName, baseOrigin, secrets := secretsList, methods := methodNames.map (fullSvcName ++ ·) }

end ExternalElab
end Qed.Server
