import Lean
import Qed.Runtime.Cmd
import Qed.Schema.Registry
import Qed.Verify.Core
import Qed.Server.Registry
import Qed.Server.Core
import Qed.Server.Syntax

namespace Qed.Server

/-! ## Runtime Wire Execution Helpers for `external` & `Webhook` -/

private def mergeHeaders (defaults custom : List (String × String)) : List (String × String) :=
  let sc := custom.map fun (k, v) => (sanitizeHeader k, sanitizeHeader v); let cl := sc.map (·.1.toLower)
  defaults.filter (fun (k, _) => !cl.contains k.toLower) ++ sc

private def checkHttpOk (okStatuses : List UInt32 := []) (resp : OutboundResp) : Except ApiError OutboundResp :=
  if (if okStatuses.isEmpty then 200 ≤ resp.status && resp.status < 300 else okStatuses.contains resp.status) then .ok resp
  else let msg := (String.fromUTF8? resp.body).getD "external HTTP error"
       .error { code := resp.status.toNat, message := if msg.isEmpty then s!"HTTP {resp.status}" else msg }

@[specialize] def execExternalRaw {m : Type → Type} [Monad m] [MonadServer m] (serviceName baseOrigin method : String)
    (parts : List PathPart) (query : List (String × QueryVal)) (defaultHeaders customHeaders : List (String × String))
    (body : ByteArray) (auth : AuthSpec) (ssrfGuard : Bool := true) (okStatuses : List UInt32 := []) : m (Except ApiError OutboundResp) := do
  match buildExternalSuffix parts query with
  | .error e => return .error e
  | .ok sfx => return (← MonadServer.httpCall { serviceName, baseOrigin, method, pathAndQuery := "/" ++ sfx, headers := mergeHeaders defaultHeaders customHeaders, body, auth, ssrfGuard }).bind (checkHttpOk okStatuses)

section ExternalSpecs
variable {σ β : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop} {EffOk : ServerEffect → Prop}
  (svc base method : String) (parts : List PathPart) (query : List (String × QueryVal))
  (defHdrs custHdrs : List (String × String)) (body : ByteArray) (auth : AuthSpec) (ssrfGuard : Bool) (okStatuses : List UInt32)

theorem progEffSpec_execExternalRaw {Post : Except ApiError OutboundResp → Prop} (hEff : ∀ req, EffOk (.httpCall req)) (hPost : ∀ r, Post r) :
    ProgEffSpec Inv A Step EffOk Post (execExternalRaw (m := ThreadProg σ) svc base method parts query defHdrs custHdrs body auth ssrfGuard okStatuses) := by
  unfold execExternalRaw; cases buildExternalSuffix parts query with
  | error _ => exact .pure _ (hPost _) | ok _ => exact .io (.httpCall _) _ (hEff _) fun _ => .pure _ (hPost _)

theorem progEffSpec_execExternalRaw_bind {Post : β → Prop} {k : Except ApiError OutboundResp → ThreadProg σ β}
    (hEff : ∀ req, EffOk (.httpCall req)) (hk : ∀ r, ProgEffSpec Inv A Step EffOk Post (k r)) :
    ProgEffSpec Inv A Step EffOk Post (execExternalRaw (m := ThreadProg σ) svc base method parts query defHdrs custHdrs body auth ssrfGuard okStatuses >>= k) :=
  (progEffSpec_execExternalRaw svc base method parts query defHdrs custHdrs body auth ssrfGuard okStatuses hEff fun _ => trivial).bind fun r _ => hk r

instance : SafeIO (execExternalRaw (m := ThreadProg σ) svc base method parts query defHdrs custHdrs body auth ssrfGuard okStatuses) :=
  ⟨progEffSpec_execExternalRaw svc base method parts query defHdrs custHdrs body auth ssrfGuard okStatuses (fun _ => trivial) (fun _ => trivial)⟩
end ExternalSpecs

@[specialize] def decodeRespBytes (res : Except ApiError OutboundResp) : Except ApiError Bytes := res.map (·.body)
@[specialize] def decodeRespUnit (res : Except ApiError OutboundResp) : Except ApiError Unit := res.map fun _ => ()
@[specialize] def decodeRespString (res : Except ApiError OutboundResp) : Except ApiError String :=
  res.bind fun r => (String.fromUTF8? r.body).elim (.error (ApiError.internal "external API returned invalid UTF-8")) .ok
@[specialize] def decodeRespProto {α : Type} [FromProto α] (res : Except ApiError OutboundResp) : Except ApiError α :=
  res.bind fun r => (Proto.decode (α := α) r.body).mapError fun e => ApiError.internal s!"external protobuf decode failed: {e}"
@[specialize] def decodeRespJson {α : Type} [FromJson α] (res : Except ApiError OutboundResp) : Except ApiError α :=
  (decodeRespString res).bind fun raw =>
    ((Json.parse (if raw.toList.all Char.isWhitespace then "{}" else raw) 128).bind (FromJson.fromJson (α := α))).mapError fun e => ApiError.internal s!"external JSON decode failed: {e}"

namespace Webhook

private def splitHttpsOriginAndPath (raw : String) : String × String :=
  match Qed.Str.splitChar (String.ofList (raw.toList.drop 8)) '/' with
  | [] => (raw, "/") | host :: rest => ("https://" ++ host, if rest.isEmpty then "/" else "/" ++ String.intercalate "/" rest)

@[specialize] def postRaw {m : Type → Type} [Monad m] [MonadServer m] (url : WebhookUrl) (headers : List (String × String)) (body : Bytes) : m (Except ApiError OutboundResp) := do
  let (origin, path) := splitHttpsOriginAndPath url.raw
  return (← MonadServer.httpCall { serviceName := "Webhook", baseOrigin := origin, method := "POST", pathAndQuery := path, headers, body, auth := .none, ssrfGuard := true }).bind checkHttpOk

section WebhookSpecs
variable {σ β : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop} {EffOk : ServerEffect → Prop}
  (url : WebhookUrl) (headers : List (String × String)) (body : Bytes)

theorem progEffSpec_postRaw {Post : Except ApiError OutboundResp → Prop} (hEff : ∀ req, EffOk (.httpCall req)) (hPost : ∀ r, Post r) :
    ProgEffSpec Inv A Step EffOk Post (postRaw (m := ThreadProg σ) url headers body) := .io (.httpCall _) _ (hEff _) fun _ => .pure _ (hPost _)

theorem progEffSpec_postRaw_bind {Post : β → Prop} {k : Except ApiError OutboundResp → ThreadProg σ β}
    (hEff : ∀ req, EffOk (.httpCall req)) (hk : ∀ r, ProgEffSpec Inv A Step EffOk Post (k r)) :
    ProgEffSpec Inv A Step EffOk Post (postRaw (m := ThreadProg σ) url headers body >>= k) :=
  (progEffSpec_postRaw url headers body hEff fun _ => trivial).bind fun r _ => hk r
end WebhookSpecs

@[specialize] def postJson {Payload Resp : Type} {m : Type → Type} [Monad m] [MonadServer m] [ToJson Payload] [FromJson Resp] (url : WebhookUrl) (payload : Payload) : m (Except ApiError Resp) :=
  decodeRespJson <$> postRaw url [("Content-Type", "application/json"), ("Accept", "application/json")] (Json.render (toJson payload)).toUTF8
@[specialize] def postBytes {m : Type → Type} [Monad m] [MonadServer m] (url : WebhookUrl) (mime : String) (body : Bytes) : m (Except ApiError Bytes) :=
  decodeRespBytes <$> postRaw url [("Content-Type", sanitizeHeader mime)] body

instance {σ Payload Resp : Type} [ToJson Payload] [FromJson Resp] (url : WebhookUrl) (payload : Payload) :
    SafeIO (postJson (Payload := Payload) (Resp := Resp) (m := ThreadProg σ) url payload) :=
  ⟨progEffSpec_postRaw_bind url _ _ (fun _ => trivial) fun _ => .pure _ trivial⟩
instance {σ : Type} (url : WebhookUrl) (mime : String) (body : Bytes) : SafeIO (postBytes (m := ThreadProg σ) url mime body) :=
  ⟨progEffSpec_postRaw_bind url _ _ (fun _ => trivial) fun _ => .pure _ trivial⟩

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
private inductive BaseVarDomain where
  | unitEnum (tyIdent : Lean.Ident) (wireVals : Array String) | strList (allowed : Array String)
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
private def ParsedBaseSpec.isTotal (b : ParsedBaseSpec) : Bool := b.vars.all fun v => match v.domain with | .unitEnum .. => true | .strList .. => false

theorem validOrigin_of_ok {s orig : String} (hs : isValidBaseOrigin s = true) (h : (Except.ok s : Except ApiError String) = .ok orig) : isValidBaseOrigin orig = true := by
  cases h; exact hs
theorem validOrigin_of_ite {P : Prop} [Decidable P] {a b : Except ApiError String} {orig : String}
    (ha : a = .ok orig → isValidBaseOrigin orig = true) (hb : b = .ok orig → isValidBaseOrigin orig = true) (h : (if P then a else b) = .ok orig) : isValidBaseOrigin orig = true := by
  by_cases hp : P <;> (simp only [hp, ↓reduceIte] at h; first | exact ha h | exact hb h)

section ExternalElab
open Lean Elab Command

@[noinline] private def parseBraceTemplate {α : Type} (ref : Syntax) (src ctxDesc : String) (init : α)
    (onLit : String → CommandElabM Unit) (onPh : α → String → CommandElabM (String × α)) : CommandElabM (Array UrlSegPiece × α) :=
  let flushLit (buf : List Char) (ps : Array UrlSegPiece) : CommandElabM (Array UrlSegPiece) := do
    if buf.isEmpty then return ps else let lit := String.ofList buf.reverse; onLit lit; return ps.push (.lit lit)
  let rec go (cs : List Char) (inBrace : Bool) (buf : List Char) (ps : Array UrlSegPiece) (st : α) : CommandElabM (Array UrlSegPiece × α) := do
    match cs with
    | [] => if inBrace then errAt ref s!"unclosed `\{` in {ctxDesc}" else return (← flushLit buf ps, st)
    | c :: rest =>
        if inBrace then
          if c == '{' then errAt ref s!"nested `\{` in {ctxDesc}"
          else if c == '}' then let (pn, st') ← onPh st (String.ofList buf.reverse); go rest false [] (ps.push (.param pn)) st'
          else go rest true (c :: buf) ps st
        else if c == '}' then errAt ref s!"unmatched `}` in {ctxDesc}"
        else if c == '{' then go rest true [] (← flushLit buf ps) st
        else go rest false (c :: buf) ps st
  go src.toList false [] #[] init

@[noinline] private def registerUrlPh (ref : Syntax) (tmpl raw kindDesc : String) (allowWildcard : Bool) (phs : Array String) : CommandElabM (String × Bool × Array String) := do
  let isMulti := raw.endsWith "*"
  if isMulti && !allowWildcard then errAt ref s!"wildcard placeholder `*{raw}` is not allowed in {kindDesc} in `{tmpl}`"
  let pname := if isMulti then String.ofList (raw.toList.take (raw.length - 1)) else raw
  if pname.isEmpty then errAt ref s!"empty {kindDesc} placeholder in `{tmpl}`"
  if phs.contains pname then errAt ref s!"duplicate placeholder `{pname}` in `{tmpl}`"
  return (pname, isMulti, phs.push pname)

@[noinline] private def parseUrlSeg (ref : Syntax) (tmpl : String) (acc : Array UrlSegSpec × Array String) (seg : String) : CommandElabM (Array UrlSegSpec × Array String) := do
  let (segSpecs, phs) := acc
  if seg.contains '{' || seg.contains '}' then
    let (pieces, (phs', wild?)) ← parseBraceTemplate ref seg s!"URL path segment `{seg}` of `{tmpl}`" (phs, (none : Option String))
      (fun lit => unless lit.toList.all isSafeLitSegChar do errAt ref s!"invalid static URL path text `{lit}` in `{tmpl}`")
      (fun (cur, w?) raw => do let (pn, m, cur') ← registerUrlPh ref tmpl raw "`{...}`" true cur; return (pn, (cur', if m then some pn else w?)))
    if let some wn := wild? then
      if pieces.size != 1 then errAt ref s!"multi-segment wildcard `\{{wn}*}` must occupy an entire path segment in `{tmpl}`"
      return (segSpecs.push (.multiParam wn), phs')
    if pieces.size == 1 then match pieces[0]! with
      | .lit s => if s == "." || s == ".." then errAt ref s!"invalid static URL path segment `{seg}` in `{tmpl}`" else return (segSpecs.push (.lit s), phs')
      | .param pn => return (segSpecs.push (.singleParam pn), phs')
    return (segSpecs.push (.compound pieces), phs')
  if seg.startsWith ":" then
    let (pn, m, phs') ← registerUrlPh ref tmpl (String.ofList (seg.toList.drop 1)) "`:`" true phs
    return (segSpecs.push (if m then .multiParam pn else .singleParam pn), phs')
  if seg == "." || seg == ".." || !seg.toList.all isSafeLitSegChar then errAt ref s!"invalid static URL path segment `{seg}` in `{tmpl}`"
  return (segSpecs.push (.lit seg), phs)

@[noinline] private def parseUrlTemplate (ref : Syntax) (tmpl : String) : CommandElabM (Array UrlSegSpec × Array (String × QueryValSpec) × Array String) := do
  if tmpl.contains '#' then errAt ref "external endpoint URL template must not contain `#` fragments"
  if !tmpl.startsWith "/" then errAt ref s!"external endpoint path `{tmpl}` must start with `/`"
  let qParts := tmpl.splitOn "?"
  if qParts.length > 2 then errAt ref s!"external endpoint path `{tmpl}` has multiple `?` query delimiters"
  let (segSpecs, phs1) ← foldlCmd (((qParts.headD "").splitOn "/").filter (· != "")).toArray (#[], #[]) (parseUrlSeg ref tmpl)
  let (querySpecs, phs2) ← foldlCmd (((qParts.getD 1 "").splitOn "&").filter (· != "")).toArray (#[], phs1) fun (qs, phs) pair => do
    match pair.splitOn "=" with
    | [k, v] =>
        if k.isEmpty then errAt ref s!"empty query parameter key in `{tmpl}`"
        let ph? := if v.startsWith ":" then some (String.ofList (v.toList.drop 1))
          else if v.startsWith "{" && v.endsWith "}" && v.length >= 2 then some (String.ofList ((v.toList.drop 1).take (v.length - 2))) else none
        let (qv, phs') ← match ph? with | some raw => let (pn, _, p') ← registerUrlPh ref tmpl raw "query" false phs; pure (.param pn, p') | none => pure (.lit v, phs)
        return (qs.push (k, qv), phs')
    | [k] => return (qs.push (k, .lit ""), phs)
    | _ => errAt ref s!"malformed query parameter `{pair}` in `{tmpl}`"
  return (segSpecs, querySpecs, phs2)

@[noinline] private def parseBaseWhereItem (svcName : Name) (vars : Array BaseTemplateVar) (w : Syntax) : CommandElabM (Array BaseTemplateVar) := do
  let wk := w.getKind
  if wk != ``extBaseWhereEnum && wk != ``extBaseWhereIn then errAt w s!"unexpected `where` item in `base` of `external {svcName}`"
  let vId : Ident := ⟨w.getArg 0⟩; let vName := vId.getId.eraseMacroScopes.toString
  if vars.any (·.name == vName) then errAt vId s!"duplicate `where` constraint for `{vName}` in `base` of `external {svcName}`"
  let domain ← if wk == ``extBaseWhereEnum then
      let tyId : Ident := ⟨w.getArg 2⟩
      let some uInfo := Qed.lookupUnitEnum? (← getEnv) (← getCurrNamespace) (← getOpenDecls) tyId.getId
        | errAt tyId s!"type `{tyId.getId}` in `base ... where {vName} : {tyId.getId}` must be a unit `enum` (without variant payloads)"
      if uInfo.variants.isEmpty then errAt tyId s!"enum `{tyId.getId}` has no variants"
      pure (.unitEnum tyId uInfo.variants)
    else .strList <$> foldlCmd (w.getArg 3).getSepArgs #[] fun vs sStx => do
      let sVal := (⟨sStx⟩ : TSyntax `str).getString
      if sVal.isEmpty then errAt sStx s!"empty string literal in `where {vName} in [...]` of `external {svcName}`"
      if vs.contains sVal then errAt sStx s!"duplicate value `{sVal}` in `where {vName} in [...]` of `external {svcName}`"
      return vs.push sVal
  return vars.push { ref := w, ident := vId, name := vName, domain }

@[noinline] private def parseBaseClause (svcName : Name) (c : Syntax) : CommandElabM ParsedBaseSpec := do
  let rawBase := (⟨c.getArg 1⟩ : TSyntax `str).getString
  let trimmed := if rawBase.endsWith "/" then String.ofList (rawBase.toList.take (rawBase.length - 1)) else rawBase
  let (pieces, phNames) ← parseBraceTemplate (c.getArg 1) trimmed s!"`base` URL template `{trimmed}`" (#[] : Array String) (fun _ => pure ()) fun cur vn => do
    if vn.isEmpty then errAt (c.getArg 1) s!"empty `\{}` placeholder in `base` URL template `{trimmed}`"
    if cur.contains vn then errAt (c.getArg 1) s!"duplicate placeholder `\{{vn}}` in `base` URL template `{trimmed}`"
    return (vn, cur.push vn)
  let optWhere := c.getArg 2
  if optWhere.getNumArgs == 0 then
    if let some pn := phNames[0]? then errAt c s!"`base` URL placeholder `\{{pn}}` in `external {svcName}` has no matching `where {pn} : Enum` or `where {pn} in [...]` allowlist"
    unless isValidWsBaseOrigin trimmed do errAt c s!"invalid `base` URL `{rawBase}`: expected pinned `https://`, `http://`, `wss://`, or `ws://` origin without `?`, `#`, `@`, or `\\`"
    return { ref := c, rawTemplate := trimmed, pieces := #[.lit trimmed], vars := #[], allowedOrigins := #[trimmed] }
  if phNames.isEmpty then errAt optWhere s!"`base \"{rawBase}\" where ...` has no `\{var}` placeholders in the base URL"
  let vars ← foldlCmd (optWhere.getArg 1).getSepArgs #[] (parseBaseWhereItem svcName)
  if let some pn := phNames.find? fun pn => !vars.any (·.name == pn) then errAt c s!"`base` URL placeholder `\{{pn}}` in `external {svcName}` has no matching `where {pn} : Enum` or `where {pn} in [...]` allowlist"
  if let some v := vars.find? fun v => !phNames.contains v.name then errAt v.ref s!"`where` variable `{v.name}` is not referenced as `\{{v.name}}` in `base \"{rawBase}\"`"
  let envs ← foldlCmd vars (#[#[]] : Array (Array (String × String))) fun acc v => do
    let vals := match v.domain with | .unitEnum _ ws | .strList ws => ws
    if acc.size * vals.size > 256 then errAt c s!"`external {svcName}` `base` allowlist exceeds maximum of 256 origin combinations"
    return acc.flatMap fun env => vals.map fun val => env.push (v.name, val)
  let allowedOrigins := envs.map fun env => pieces.foldl (init := "") fun s pc =>
    match pc with | .lit l => s ++ l | .param pn => s ++ (env.find? (·.1 == pn) |>.map Prod.snd |>.getD "")
  if let some orig := allowedOrigins.find? (!isValidWsBaseOrigin ·) then
    errAt c s!"invalid expanded `base` origin `{orig}` in `external {svcName}`: every allowed origin must be a valid `https://`, `http://`, `wss://`, or `ws://` origin without `?`, `#`, `@`, or `\\`"
  return { ref := c, rawTemplate := trimmed, pieces, vars, allowedOrigins }

@[noinline] private def parseAuthClause (c : Syntax) : CommandElabM AuthSpec := do
  let checkEnv (stx : Syntax) : CommandElabM String := do
    let v := (⟨stx⟩ : TSyntax `str).getString
    unless isValidEnvVarName v do errAt stx s!"invalid secret environment variable name `{v}`: must be non-empty and contain only ASCII letters, digits, or `_`"
    return v
  match c.getKind with
  | ``extAuthBearer => return .bearerSecret (← checkEnv (c.getArg 5))
  | ``extAuthHeader =>
      let hdrName := (⟨c.getArg 3⟩ : TSyntax `str).getString
      if hdrName.isEmpty then errAt (c.getArg 3) "header name cannot be empty"
      return .headerSecret hdrName (← checkEnv (c.getArg 7))
  | ``extAuthGcp => return .gcpServiceAccount (← checkEnv (c.getArg 5)) (if (c.getArg 7).getNumArgs == 2 then (⟨(c.getArg 7).getArg 1⟩ : TSyntax `str).getString else "https://www.googleapis.com/auth/cloud-platform")
  | _ => return .gcpMetadata (if (c.getArg 2).getNumArgs == 3 then some (⟨(c.getArg 2).getArg 1⟩ : TSyntax `str).getString else none)

@[noinline] private def parseExternalClauses (svcIdent : Ident) (svcName : Name) (clauses : Array Syntax) :
    CommandElabM (ParsedBaseSpec × AuthSpec × Bool × Array Syntax × Array Syntax) := do
  let (base?, auth?, ssrf?, eps, ws) ← foldlCmd clauses (none, none, none, #[], #[]) fun (b?, a?, s?, eps, ws) c => do
    match c.getKind with
    | ``extBaseClause => if b?.isSome then errAt c s!"duplicate `base` clause in `external {svcName}`" else return (some (← parseBaseClause svcName c), a?, s?, eps, ws)
    | ``extSsrfGuardClause => if s?.isSome then errAt c s!"duplicate `ssrf_guard` clause in `external {svcName}`" else let ov := c.getArg 1; return (b?, a?, some (if ov.getNumArgs == 1 then (ov.getArg 0).getId.eraseMacroScopes != `false else true), eps, ws)
    | ``extAuthBearer | ``extAuthHeader | ``extAuthGcp | ``extAuthGcpMeta => if a?.isSome then errAt c s!"duplicate `auth` clause in `external {svcName}`" else return (b?, some (← parseAuthClause c), s?, eps, ws)
    | ``extEndpointClause => return (b?, a?, s?, eps.push c, ws)
    | ``extWsClause => return (b?, a?, s?, eps, ws.push c)
    | _ => errAt c "unexpected clause in `external` block"
  let some baseSpec := base? | errAt svcIdent s!"`external {svcName}` must declare `base \"https://...\"` or `base \"wss://...\"`"
  if eps.isEmpty && ws.isEmpty then errAt svcIdent s!"`external {svcName}` must declare at least one HTTP endpoint or `ws` channel"
  if ssrf?.isSome && eps.isEmpty then errAt svcIdent s!"`ssrf_guard` in `external {svcName}` applies to server-side HTTP endpoints"
  if !eps.isEmpty then if let some orig := baseSpec.allowedOrigins.find? (!isValidBaseOrigin ·) then
    errAt baseSpec.ref s!"`external {svcName}` declares HTTP endpoints, so every allowed `base` origin must use `https://` or `http://` (got `{orig}`)"
  if !ws.isEmpty && !baseSpec.vars.isEmpty then errAt baseSpec.ref s!"multi-origin `base ... where ...` in `external {svcName}` is only supported for HTTP endpoints (not client `ws` channels)"
  if !ws.isEmpty && auth?.isSome then errAt svcIdent s!"`external {svcName}` declares client-usable `ws` channels and cannot attach server `auth` secrets; split server-authenticated HTTP endpoints into a separate `external` block"
  return (baseSpec, auth?.getD .none, ssrf?.getD true, eps, ws)

@[noinline] private def lowerUrlPartsPure (segSpecs : Array UrlSegSpec) (querySpecs : Array (String × QueryValSpec)) (paramIdents : Array Ident) : PureQuotM (Array Term × Array Term) := do
  let findParam (pn : String) : Ident := paramIdents.find? (·.getId.toString == pn) |>.getD (mkIdent (Name.mkSimple pn))
  let paramSeg (pn : String) : PureQuotM Term := `(Qed.RouteParam.toSeg $(findParam pn))
  let pathTerms ← mapPQ segSpecs fun
    | .lit s => `(Qed.Server.PathPart.lit $(Syntax.mkStrLit s))
    | .singleParam pn => do `(Qed.Server.PathPart.seg $(← paramSeg pn))
    | .multiParam pn => do `(Qed.Server.PathPart.multiSeg $(← paramSeg pn))
    | .compound pieces => do
        let pTerms ← mapPQ pieces fun | .lit s => `(Qed.Server.SegPiece.lit $(Syntax.mkStrLit s)) | .param pn => do `(Qed.Server.SegPiece.param $(← paramSeg pn))
        `(Qed.Server.PathPart.compound [$[$pTerms],*])
  let queryTerms ← mapPQ querySpecs fun (qk, qv) => match qv with
    | .lit s => `(($(Syntax.mkStrLit qk), Qed.Server.QueryVal.lit $(Syntax.mkStrLit s)))
    | .param pn => `(($(Syntax.mkStrLit qk), Qed.Server.ToQueryVal.toQueryVal $(findParam pn)))
  return (pathTerms, queryTerms)

@[noinline] private def parseTypedParams (ctxLabel : String) (rawParams : Array Syntax) (allowExtKinds := false) (paramKind := "parameter") : CommandElabM (Array ParsedExtParam) :=
  foldlCmd rawParams #[] fun out rp => do
    let pk := rp.getKind
    let (kind, pid, tyNode) ←
      if allowExtKinds && pk == ``extParamHeader then pure (.header (⟨rp.getArg 2⟩ : TSyntax `str).getString, (⟨rp.getArg 4⟩ : Ident), rp.getArg 6)
      else if allowExtKinds && pk == ``extParamQuery then
        let pid : Ident := ⟨rp.getArg 2⟩
        let wireName := if (rp.getArg 1).getNumArgs == 3 then (⟨(rp.getArg 1).getArg 1⟩ : TSyntax `str).getString else pid.getId.toString
        if wireName.isEmpty then errAt rp s!"query parameter wire name cannot be empty in {ctxLabel}"
        pure (.query wireName, pid, rp.getArg 4)
      else if !allowExtKinds || pk == ``extParamPlain then pure (.plain, (⟨rp.getArg 0⟩ : Ident), rp.getArg 2)
      else errAt rp "invalid endpoint parameter"
    let pstr := pid.getId.toString
    if out.any (·.ident.getId.toString == pstr) then errAt pid s!"duplicate {paramKind} `{pstr}` in {ctxLabel}"
    return out.push { ref := rp, kind, ident := pid, ty := ← liftMacroCmd (lowerSrvType tyNode false s!"{paramKind} `{pstr}`") }

private def classifyExtWsCodec (ty : Qed.Lang.LoweredQedType) : Qed.ExtWsCodec :=
  if ty.isProto then .proto else if ty.mods.isEmpty && (ty.baseName == `Bytes || ty.baseName == `ByteArray) then .bytes
  else if ty.mods.isEmpty && ty.baseName == `String then .text else .json
private def isUnitExtType (ty : Qed.Lang.LoweredQedType) : Bool := !ty.isProto && !ty.isForm && ty.mods.isEmpty && ty.baseName == `Unit

@[noinline] private def mkBaseConcatPure (baseSpec : ParsedBaseSpec) (subst : Array (String × String)) : PureQuotM Term := do
  let parts ← foldlPQ baseSpec.pieces (#[] : Array (Sum String Term)) fun ps pc => do
    let item : Sum String Term ← match pc with
      | .lit s => pure (.inl s)
      | .param pn => match subst.find? (·.1 == pn) with
          | some (_, val) => pure (.inl val)
          | none => pure (.inr (← `(Qed.StringEnum.toWire $(baseSpec.vars.find? (·.name == pn) |>.map (·.ident) |>.getD (mkIdent (Name.mkSimple pn))))))
    return match ps.back?, item with | some (.inl prev), .inl cur => ps.pop.push (.inl (prev ++ cur)) | _, _ => ps.push item
  let ts : Array Term := parts.map fun | .inl s => (Syntax.mkStrLit s : Term) | .inr t => t
  if h : 0 < ts.size then foldlPQ (ts.extract 1 ts.size) ts[0] fun acc x => `($acc ++ $x) else pure (Syntax.mkStrLit "" : Term)

@[noinline] private def mkBaseResolverCmdsPure (svcIdent : Ident) (svcName : Name) (baseSpec : ParsedBaseSpec) :
    PureQuotM (Ident × Array (TSyntax `command) × TSyntax `command) := do
  let mkS (leaf : Name) := mkIdentFrom svcIdent (svcName ++ leaf)
  let (allowedId, resolveId, validId) := (mkS `allowedBaseOrigins, mkS `resolveBaseOrigin, mkS `resolveBaseOrigin_valid)
  let vIds := baseSpec.vars.map (·.ident); let vIdTerms : Array Term := vIds.map (⟨·.raw⟩)
  let vTys ← mapPQ baseSpec.vars fun v => match v.domain with | .unitEnum tyId _ => pure ⟨tyId.raw⟩ | .strList _ => `(String)
  let casesTacs ← mapPQ (baseSpec.vars.filterMap fun v => match v.domain with | .unitEnum .. => some v.ident | .strList .. => none) fun eId => `(tactic| all_goals cases $eId:ident)
  let allowCmd ← mkStrArrDefPure allowedId baseSpec.allowedOrigins
  if baseSpec.isTotal then
    let bodyT ← mkBaseConcatPure baseSpec #[]
    return (resolveId, #[allowCmd, ← `(command| def $resolveId $[($vIds:ident : $vTys:term)]* : String := $bodyT)],
      ← `(command| theorem $validId $[($vIds:ident : $vTys:term)]* : Qed.Server.isValidBaseOrigin ($resolveId $vIdTerms*) = true := by unfold $resolveId; $[$casesTacs:tactic]*; all_goals qedCloseGroundKernel))
  let strVars := baseSpec.vars.filter fun v => match v.domain with | .strList _ => true | .unitEnum .. => false
  let rec buildBranch (idx : Nat) (subst : Array (String × String)) : PureQuotM (Term × Term) := do
    if h : idx < strVars.size then
      let sv := strVars[idx]; let allowed := match sv.domain with | .strList a => a | .unitEnum .. => #[]
      let initErr ← `(Except.error (Qed.Server.ApiError.badRequest $(Syntax.mkStrLit s!"disallowed value for `{sv.name}` in `external {svcName}` base URL")))
      foldrPQ allowed (initErr, ← `(fun _he => by cases _he)) fun val (accT, accPf) => do
        let (okT, okPf) ← buildBranch (idx + 1) (subst.push (sv.name, val))
        return (← `(if $(sv.ident) == $(Syntax.mkStrLit val) then $okT else $accT), ← `(Qed.Server.validOrigin_of_ite $okPf $accPf))
    else
      let cTerm ← mkBaseConcatPure baseSpec subst
      let decPf ← if casesTacs.isEmpty then `(by qedCloseGroundKernel) else `(by $[$casesTacs:tactic];*; all_goals qedCloseGroundKernel)
      return (← `(Except.ok $cTerm), ← `(Qed.Server.validOrigin_of_ok (s := $cTerm) $decPf))
  let (bodyT, bodyPf) ← buildBranch 0 #[]
  let (origId, hId) := (mkIdent `_orig, mkIdent `_h)
  return (resolveId, #[allowCmd, ← `(command| def $resolveId $[($vIds:ident : $vTys:term)]* : Except Qed.Server.ApiError String := $bodyT)],
    ← `(command| theorem $validId $[($vIds:ident : $vTys:term)]* ($origId:ident : String) ($hId:ident : $resolveId $vIdTerms* = Except.ok $origId) : Qed.Server.isValidBaseOrigin $origId = true := $bodyPf $hId))

@[noinline] private def mkExtCodecsPure (retTy : Qed.Lang.LoweredQedType) (bodyParam? : Option ParsedExtParam) :
    PureQuotM (Option (String × String) × Term × Term × Option (String × String)) := do
  let rT := retTy.term
  let (accH, dec) ← if isUnitExtType retTy then pure (none, ← `(Qed.Server.decodeRespUnit rawRes)) else match classifyExtWsCodec retTy with
    | .proto => pure (some ("Accept", "application/x-protobuf"), ← `(Qed.Server.decodeRespProto (α := $rT) rawRes))
    | .bytes => pure (none, ← `(Qed.Server.decodeRespBytes rawRes))
    | .text  => pure (none, ← `(Qed.Server.decodeRespString rawRes))
    | .json  => pure (some ("Accept", "application/json"), ← `(Qed.Server.decodeRespJson (α := $rT) rawRes))
  let (bodyT, ctH) ← match bodyParam? with
    | none => pure (← `(ByteArray.empty), none)
    | some bp =>
        if bp.ty.isForm then pure (← `(Qed.Server.encodeFormBodyOf $(bp.ident)), some ("Content-Type", "application/x-www-form-urlencoded"))
        else if isUnitExtType bp.ty then pure (← `(ByteArray.empty), none)
        else match classifyExtWsCodec bp.ty with
          | .proto => pure (← `(Qed.Proto.encode $(bp.ident)), some ("Content-Type", "application/x-protobuf"))
          | .bytes => pure (← `(($(bp.ident) : ByteArray)), some ("Content-Type", "application/octet-stream"))
          | .text | .json => pure (← `((Qed.Json.render (Qed.toJson $(bp.ident))).toUTF8), some ("Content-Type", "application/json"))
  return (accH, dec, bodyT, ctH)

@[noinline] private def mkExtEndpointCmdsPure (svcName : Name) (svcStrLit : StrLit) (baseId fnIdent : Ident) (baseSpec : ParsedBaseSpec)
    (resolveBaseId? : Option Ident) (baseArgIdents : Array Ident) (authTerm : Term) (ssrfGuard : Bool) (httpVerbRaw : String)
    (parsedParams : Array ParsedExtParam) (segSpecs : Array UrlSegSpec) (querySpecs : Array (String × QueryValSpec))
    (retTy : Qed.Lang.LoweredQedType) (bodyParam? : Option ParsedExtParam) (okStatusList : Array UInt32) : PureQuotM (Array (TSyntax `command)) := do
  let (pIdents, pTyTerms) := (parsedParams.map (·.ident), parsedParams.map (·.ty.term))
  let (pathTerms, tmplQ) ← lowerUrlPartsPure segSpecs querySpecs ((parsedParams.filter (·.kind == .plain)).map (·.ident))
  let paramQ ← mapPQ (parsedParams.filterMap fun p => match p.kind with | .query qk => some (qk, p.ident) | _ => none) fun (qk, pid) =>
    `(($(Syntax.mkStrLit qk), Qed.Server.ToQueryVal.toQueryVal $pid))
  let queryTerms := tmplQ ++ paramQ
  let customHdrOpts ← mapPQ (parsedParams.filterMap fun p => match p.kind with | .header hk => some (hk, p.ident) | _ => none) fun (hk, pid) =>
    `((Qed.Server.ToHeaderVal.toHeaderVal? $pid).map fun _hv => ($(Syntax.mkStrLit hk), _hv))
  let customHdrsTerm ← if customHdrOpts.isEmpty then `(([] : List (String × String))) else `(List.filterMap id [$[$customHdrOpts],*])
  let (acceptHdr, decodeCall, bodyTerm, ctHdr) ← mkExtCodecsPure retTy bodyParam?
  let defHdrTerms ← mapPQ (#[ctHdr, acceptHdr].filterMap id) fun (k, v) => `(($(Syntax.mkStrLit k), $(Syntax.mkStrLit v)))
  let okTerms ← mapPQ okStatusList fun code => `(($(quote code.toNat) : UInt32))
  let (fullFnId, retPayloadTerm) := (mkIdentFrom fnIdent (svcName ++ fnIdent.getId), retTy.term)
  let mkExecCall (originExpr : Term) : PureQuotM Term := `(do
    let rawRes ← Qed.Server.execExternalRaw $svcStrLit $originExpr $(Syntax.mkStrLit httpVerbRaw) [$[$pathTerms],*] [$[$queryTerms],*] [$[$defHdrTerms],*] $customHdrsTerm $bodyTerm $authTerm $(quote ssrfGuard) [$[$okTerms],*]
    return $decodeCall)
  let resCall? ← match resolveBaseId? with | some resId => some <$> Qed.Lang.mkAppTerms ⟨resId.raw⟩ (baseArgIdents.map (⟨·.raw⟩)) | none => pure none
  let (fnBody, safeIoTac) : Term × TSyntax ``Lean.Parser.Tactic.tacticSeq ← match resCall?, baseSpec.isTotal with
    | some resCall, false =>
        let okCall ← mkExecCall (← `(_baseOrig))
        pure (← `(match $resCall:term with | Except.error _baseErr => Pure.pure (Except.error _baseErr) | Except.ok _baseOrig => $okCall),
          ← `(Lean.Parser.Tactic.tacticSeq| unfold $fullFnId; cases ($resCall : Except Qed.Server.ApiError String) with | error _baseErr => exact Qed.Server.NoAtomic.pure (Except.error _baseErr) | ok _baseOrig => exact (inferInstance : Qed.Server.SafeIO _).noAtomic))
    | _, _ => pure (← mkExecCall (resCall?.getD ⟨baseId.raw⟩), ← `(Lean.Parser.Tactic.tacticSeq| unfold $fullFnId; exact (inferInstance : Qed.Server.SafeIO _).noAtomic))
  let fullFnCall ← Qed.Lang.mkAppTerms (← `($fullFnId)) (pIdents.map (⟨·.raw⟩))
  return #[
    ← `(command| @[specialize] def $fullFnId {m : Type → Type} [Monad m] [Qed.Server.MonadServer m] $[($pIdents:ident : $pTyTerms:term)]* : m (Except Qed.Server.ApiError $retPayloadTerm) := $fnBody),
    ← `(command| instance {_σ : Type} $[($pIdents:ident : $pTyTerms:term)]* : Qed.Server.SafeIO ($fullFnCall : Qed.Server.ThreadProg _σ (Except Qed.Server.ApiError $retPayloadTerm)) where noAtomic := by $safeIoTac)]

@[noinline] private def elabExternalEndpoint (svcName : Name) (svcStrLit : StrLit) (baseId : Ident) (baseSpec : ParsedBaseSpec)
    (resolveBaseId? : Option Ident) (authTerm : Term) (ssrfGuard : Bool) (methodNames : Array Name) (ep : Syntax) : CommandElabM (Array Name) := do
  let httpVerbRaw := (ep.getArg 0).getId.toString.toUpper; let urlTmpl := (⟨ep.getArg 1⟩ : TSyntax `str).getString
  let fnIdent : Ident := ⟨ep.getArg 2⟩; let fnName := fnIdent.getId
  if methodNames.contains fnName then errAt fnIdent s!"duplicate endpoint `{fnName}` in `external {svcName}`"
  let parsedParams ← parseTypedParams s!"endpoint `{fnName}`" (ep.getArg 4).getSepArgs true
  let retTy ← liftMacroCmd (lowerSrvType (ep.getArg 7) false "external endpoint return types (external calls are automatically fallible at `await`; write `-> T` instead of `-> T!`)")
  if retTy.isForm then errAt (ep.getArg 7) "`Form(T)` is only supported for HTTP request body parameters, not response types"
  let okStatusList ← if (ep.getArg 8).getNumArgs == 4 then mapCmd ((ep.getArg 8).getArg 2).getSepArgs fun nStx => do
      let n := (⟨nStx⟩ : TSyntax `num).getNat
      unless 100 ≤ n && n < 600 do errAt nStx s!"HTTP status code `{n}` in `ok [...]` must be between 100 and 599"
      pure n.toUInt32
    else pure #[]
  let (segSpecs, querySpecs, placeholders) ← parseUrlTemplate (ep.getArg 1) urlTmpl
  let baseArgIdents ← mapCmd baseSpec.vars fun bv => do
    let some bp := parsedParams.find? fun p => p.kind == .plain && p.ident.getId.toString == bv.name
      | errAt fnIdent s!"`base` URL placeholder `\{{bv.name}}` in `external {svcName}` requires a matching parameter `{bv.name}` on endpoint `{fnName}`"
    match bv.domain with
    | .strList _ => unless bp.ty.mods.isEmpty && !bp.ty.isProto && !bp.ty.isForm && bp.ty.baseName == `String do errAt bp.ref s!"`base` allowlist parameter `{bv.name}` on `{fnName}` must have type `String`"
    | .unitEnum tyId _ => if bp.ty.isForm || bp.ty.isProto || !bp.ty.mods.isEmpty then errAt bp.ref s!"`base` enum parameter `{bv.name}` on `{fnName}` must have type `{tyId.getId}`"
    return bp.ident
  if let some ph := placeholders.find? fun ph => !parsedParams.any fun p => p.kind == .plain && p.ident.getId.toString == ph then
    errAt (ep.getArg 1) s!"URL placeholder `{ph}` has no matching plain parameter `{ph}` in `{fnName}`"
  let baseVarNames := baseSpec.vars.map (·.name)
  let bodyParam? ← foldlCmd parsedParams none fun bp? p => do
    match p.kind with
    | .header _ | .query _ =>
        if p.ty.isForm then errAt p.ref "`Form(T)` is only supported for HTTP request body parameters"
        return bp?
    | .plain =>
        let pNm := p.ident.getId.toString
        if !placeholders.contains pNm && !baseVarNames.contains pNm then
          if httpVerbRaw == "GET" || httpVerbRaw == "DELETE" then errAt p.ref s!"parameter `{p.ident.getId}` on `{httpVerbRaw}` endpoint `{fnName}` is not referenced as `:{p.ident.getId}` or `\{{p.ident.getId}}` in `{urlTmpl}` (or mark it `query`)"
          if let some prev := bp? then errAt p.ref s!"endpoint `{fnName}` has multiple request body parameters (`{prev.ident.getId}` and `{p.ident.getId}`); bundle them into a `schema` type"
          return some p
        if p.ty.isForm then errAt p.ref "`Form(T)` cannot be used as a URL path or query placeholder"
        return bp?
  elabPureCmds (mkExtEndpointCmdsPure svcName svcStrLit baseId fnIdent baseSpec resolveBaseId? baseArgIdents authTerm ssrfGuard httpVerbRaw parsedParams segSpecs querySpecs retTy bodyParam? okStatusList)
  return methodNames.push fnName

@[noinline] private def elabExtReqPred (chIdent : Ident) (svcName fullSvcName chName : Name) (suffix : String)
    (pIdents : Array Ident) (pTyTerms : Array Term) (reqExprs : Array Syntax) : CommandElabM (Option Name × String) := do
  if reqExprs.isEmpty then return (none, "")
  let props ← mapCmd reqExprs fun e => liftMacroCmd (Qed.Lang.lowerSimpleQedExpr .propInv e)
  elabPureCmd do
    let conj ← Qed.mkConjBody props (ascribeProp := false)
    noUnusedVarsPure (← `(command| @[simp] abbrev $(mkIdentFrom chIdent (svcName ++ chName.appendAfter suffix)) $[($pIdents:ident : $pTyTerms:term)]* : Prop := $conj))
  return (some (fullSvcName ++ chName.appendAfter suffix), String.intercalate " && " (reqExprs.toList.map fun e => (e.reprint.getD "requires").trimAscii.toString))

@[noinline] private def mkExtWsClientSpecPure (chIdent baseId : Ident) (svcName chName : Name) (pIdents : Array Ident) (pTyTerms : Array Term)
    (segSpecs : Array UrlSegSpec) (querySpecs : Array (String × QueryValSpec)) (evTyTerm : Term) (evCodec : Qed.ExtWsCodec)
    (isBinary : Bool) (sendInfo? : Option (Ident × Term × Qed.ExtWsCodec)) : PureQuotM WsClientSpec := do
  let (pathTerms, queryTerms) ← lowerUrlPartsPure segSpecs querySpecs pIdents
  let (slotId, recId, onJoinId, onMsgId, onStatusId) := (mkIdent `slot, mkIdent `rec, mkIdent `onJoin, mkIdent `onMsg, mkIdent `onStatus)
  let mkUnexp (kind : String) : PureQuotM Term := `(fun _ => $onStatusId (Qed.SocketStatus.failed $(Syntax.mkStrLit s!"unexpected {kind} WebSocket frame")))
  let (onTextT, onBytesT) ← match evCodec with
    | .text  => pure (← `($onMsgId), ← mkUnexp "binary")
    | .json  => pure (← mkWsDecodeCb onMsgId onStatusId fun r => `((Qed.Json.parse $r 128).bind (Qed.FromJson.fromJson (α := $evTyTerm))), ← mkUnexp "binary")
    | .bytes => pure (← mkUnexp "text", ← `($onMsgId))
    | .proto => pure (← mkUnexp "text", ← mkWsDecodeCb onMsgId onStatusId fun bs => `(Qed.Proto.decode (α := $evTyTerm) $bs))
  let keyApp ← Qed.Lang.mkAppTerms (mkIdentFrom chIdent (svcName ++ chName.appendAfter "_key")) (pIdents.map (⟨·.raw⟩))
  let sendSpec? ← match sendInfo? with
    | none => pure none
    | some (spId, spTyTerm, sc) =>
        let sendBody : Term ← match sc with
          | .text => `(Qed.Cmd.wsExtSendText $slotId $spId) | .json => `(Qed.Cmd.wsExtSendText $slotId (Qed.Json.render (Qed.toJson $spId)))
          | .bytes => `(Qed.Cmd.wsExtSendBytes $slotId $spId) | .proto => `(Qed.Cmd.wsExtSendBytes $slotId (Qed.Proto.encode $spId))
        pure (some (#[spId], #[spTyTerm], sendBody))
  return { refIdent := chIdent, ownerName := svcName, chName, pIdents, pTyTerms, evTyTerm? := some evTyTerm, joinCbTy := ← `(Unit), wireEvTy := evTyTerm,
           keyBody := ← `((Qed.Server.buildExternalWsUrl $baseId [$[$pathTerms],*] [$[$queryTerms],*]).toOption.getD ""),
           subBody := ← `(let url := $keyApp; if url.isEmpty then Qed.Cmd.none else Qed.Cmd.wsExtOpen $slotId url $(quote isBinary) $recId $onJoinId $onTextT $onBytesT $onStatusId),
           unsubBody := ← `(Qed.Cmd.wsExtClose $slotId), sendSpec? }

@[noinline] private def elabExternalWsChannel (svcName fullSvcName : Name) (svcNameStr : String) (baseId : Ident) (existingNames : Array Name) (wsStx : Syntax) : CommandElabM (Array Name) := do
  let urlTmpl := (⟨wsStx.getArg 1⟩ : TSyntax `str).getString; let chIdent : Ident := ⟨wsStx.getArg 2⟩; let chName := chIdent.getId
  if existingNames.contains chName then errAt chIdent s!"duplicate channel/endpoint `{chName}` in `external {svcName}`"
  let parsedParams ← parseTypedParams s!"`ws {chName}`" (wsStx.getArg 4).getSepArgs
  let (pIdents, pTyTerms) := (parsedParams.map (·.ident), parsedParams.map (·.ty.term)); let seenP := pIdents.map (·.getId.toString)
  let evTy ← liftMacroCmd (lowerSrvType (wsStx.getArg 7) false s!"event type of `ws {chName}`")
  if evTy.isForm then errAt (wsStx.getArg 7) "`Form(T)` is only supported for HTTP request body parameters"
  let evCodec := classifyExtWsCodec evTy; let isBinary := evCodec == .proto || evCodec == .bytes
  let (segSpecs, querySpecs, placeholders) ← parseUrlTemplate (wsStx.getArg 1) urlTmpl
  if let some ph := placeholders.find? (!seenP.contains ·) then errAt (wsStx.getArg 1) s!"WebSocket URL placeholder `:{ph}` has no matching parameter `{ph}` in `{chName}`"
  if let some p := pIdents.find? fun p => !placeholders.contains p.getId.toString then errAt p s!"parameter `{p.getId}` on `ws {chName}` is not referenced as `:{p.getId}` in `{urlTmpl}`"
  let (reqExprs, sendParams, sendReqExprs, hasSend, recPolicy, _) ←
    foldlCmd (if (wsStx.getArg 8).getNumArgs == 2 then ((wsStx.getArg 8).getArg 1).getArgs else #[]) (#[], #[], #[], false, .defaultPolicy, false) fun (re, sp, sre, hs, rp, hr) sub => do
      match sub.getKind with
      | ``srvRequiresLine => return (re ++ (sub.getArg 1).getSepArgs, sp, sre, hs, rp, hr)
      | ``extWsReconnectClause => if hr then errAt sub s!"duplicate `reconnect` clause in `ws {chName}`" else return (re, sp, sre, hs, ← liftMacroCmd (Qed.parseReconnectExpr (sub.getArg 1)), true)
      | ``extWsSendClause =>
          if hs then errAt sub s!"duplicate `send` clause in `ws {chName}`"
          return (re, ← parseTypedParams s!"`ws {chName}`" (sub.getArg 2).getSepArgs false "send parameter", if (sub.getArg 4).getNumArgs == 2 then ((sub.getArg 4).getArg 1).getArgs.flatMap fun srl => (srl.getArg 1).getSepArgs else #[], true, rp, hr)
      | _ => errAt sub s!"unexpected clause in `ws {chName}`"
  if hasSend && sendParams.size != 1 then errAt chIdent s!"3rd-party `ws {chName}` `send(...)` expects a single payload parameter (bundle multiple fields into a `schema`)"
  let paramTypeConsts ← elabParamTypeAbbrevs chIdent svcName fullSvcName chName "_Param_" pTyTerms
  let (reqConst?, reqLabel) ← elabExtReqPred chIdent svcName fullSvcName chName "_req" pIdents pTyTerms reqExprs
  let (sendCodec, sendParamTypeConsts, sendReqConst?, sendReqLabel, sendHelperConst, sendInfo?) ← match sendParams[0]? with
    | none => pure (Qed.ExtWsCodec.json, #[], none, "", .anonymous, none)
    | some sp =>
        if sp.ty.isForm then errAt sp.ref "`Form(T)` is only supported for HTTP request body parameters"
        let (spId, spTyTerm, sc) := (sp.ident, sp.ty.term, classifyExtWsCodec sp.ty)
        let sptc ← elabParamTypeAbbrevs chIdent svcName fullSvcName chName "_SendParam_" #[spTyTerm]
        let (sr?, sl) ← elabExtReqPred chIdent svcName fullSvcName chName "_send_req" #[spId] #[spTyTerm] sendReqExprs
        pure (sc, sptc, sr?, sl, fullSvcName ++ chName.appendAfter "_send", some (spId, spTyTerm, sc))
  elabWsClientCommon (← runPQ (mkExtWsClientSpecPure chIdent baseId svcName chName pIdents pTyTerms segSpecs querySpecs evTy.term evCodec isBinary sendInfo?))
  modifyEnv fun env => Qed.channelRegistry.addEntry env {
    ChannelInfo.mkDefault fullSvcName svcNameStr chName (.external fullSvcName isBinary evCodec sendCodec) (pIdents.map (·.getId)) paramTypeConsts recPolicy with
    hasSend, sendParamCount := sendParams.size, sendParamTypeConsts, sendReqConst := sendReqConst?, sendReqLabel,
    clientReqConst := reqConst?, clientReqLabel := reqLabel, sendHelperConst }
  return existingNames.push chName

@[noinline] private def mkExternalHeaderPure (svcIdent : Ident) (svcName : Name) (baseOrigin : String) (secretsList : Array String) (authSpec : AuthSpec) :
    PureQuotM (Ident × Term × Array (TSyntax `command)) := do
  let mkS (leaf : Name) := mkIdentFrom svcIdent (svcName ++ leaf)
  let baseId := mkS `baseUrl
  let authTerm : Term ← match authSpec with
    | .none => `(Qed.Server.AuthSpec.none) | .bearerSecret v => `(Qed.Server.AuthSpec.bearerSecret $(quote v))
    | .headerSecret h v => `(Qed.Server.AuthSpec.headerSecret $(quote h) $(quote v))
    | .gcpServiceAccount v sc => `(Qed.Server.AuthSpec.gcpServiceAccount $(quote v) $(quote sc))
    | .gcpMetadata aud? => `(Qed.Server.AuthSpec.gcpMetadata $(quote aud?))
  let baseCmd ← if secretsList.isEmpty then `(command| def $baseId : String := $(quote baseOrigin)) else `(command| @[noinline] def $baseId : String := $(quote baseOrigin))
  return (baseId, authTerm, #[baseCmd, ← mkStrArrDefPure (mkS `secrets) secretsList, ← mkMarkerThmPure (mkS `_qed_external_marker)])

@[noinline, command_elab externalCmd] def elabExternalCmd : CommandElab := fun stx => do
  let svcIdent : Ident := ⟨stx.getArg 2⟩; let (svcName, svcNameStr) := (svcIdent.getId, svcIdent.getId.toString)
  let (baseSpec, authSpec, ssrfGuard, epClauses, wsClauses) ← parseExternalClauses svcIdent svcName (stx.getArg 4).getArgs
  let (baseOrigin, fullSvcName, secretsList) := (baseSpec.rawTemplate, (← getCurrNamespace) ++ svcName, authSpec.requiredSecrets.toArray)
  let (baseId, authTerm, hdrCmds) ← runPQ (mkExternalHeaderPure svcIdent svcName baseOrigin secretsList authSpec)
  foldlCmd hdrCmds () fun _ c => elabCommand c
  let (resolveBaseId?, validCmd?) ← if baseSpec.vars.isEmpty then pure (none, none) else do
    let (resId, defCmds, validCmd) ← runPQ (mkBaseResolverCmdsPure svcIdent svcName baseSpec)
    foldlCmd defCmds () fun _ c => elabCommand c; pure (some resId, some validCmd)
  let m1 ← foldlCmd epClauses #[] (elabExternalEndpoint svcName (Syntax.mkStrLit svcNameStr) baseId baseSpec resolveBaseId? authTerm ssrfGuard)
  let methods ← foldlCmd wsClauses m1 (elabExternalWsChannel svcName fullSvcName svcNameStr baseId)
  if let some vc := validCmd? then elabCommand vc
  modifyEnv fun env => externalRegistry.addEntry env { serviceName := fullSvcName, baseOrigin, secrets := secretsList, methods := methods.map (fullSvcName ++ ·) }

end ExternalElab
end Qed.Server
