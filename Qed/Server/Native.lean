import Lean
import Qed.Ssr
import Qed.Server.Core
import Qed.Server.Elab
import Qed.Server.Net
import Qed.Server.Http
import Qed.Server.Prim

namespace Qed.Server.Native

open Qed.Server.Net
open Qed.Server.Http

/-! ## Unified CSRF & CSWSH Origin / Fetch-Metadata Verification -/

/-- True iff `headers` carries a single `Content-Type` header whose media type is
    `application/x-protobuf` (ignoring optional parameters such as `; charset=...`). -/
def isProtobufContentType (headers : List (String × String)) : Bool :=
  match headers.filter fun (k, _) => k.toLower == "content-type" with
  | [(_, v)] => (trimWs ((v.splitOn ";").headD "")).toLower == "application/x-protobuf"
  | _ => false

/-- True iff `origin` has an `http://` or `https://` scheme and its authority matches `host`
    (case-insensitive, rejecting `null`, paths, and empty hosts). -/
def isOriginMatchingHost (origin host : String) : Bool :=
  let h := trimWs host
  if h.isEmpty then false
  else
    let o := trimWs origin
    let oLow := o.toLower
    let afterScheme? : Option String :=
      if oLow.startsWith "http://" then some (String.ofList (o.toList.drop 7))
      else if oLow.startsWith "https://" then some (String.ofList (o.toList.drop 8))
      else none
    match afterScheme? with
    | none => false
    | some rest =>
        let auth := stripTrailingSlashes rest
        !auth.isEmpty && !auth.contains '/' && auth.toLower == h.toLower

/-- True iff `origin` matches `*` or an entry in the comma-separated allowlist `allowed`. -/
def isOriginExplicitlyAllowed (allowed origin : String) : Bool :=
  let a := trimWs allowed
  if a.isEmpty then false
  else if a == "*" then true
  else
    let o := (trimWs origin).toLower
    !o.isEmpty && (a.splitOn ",").any fun entry => (trimWs entry).toLower == o

private def checkOriginAndFetchSite (headers : List (String × String))
    (allowedOrigins? : Option String) (allowEmptyOrigin : Bool) (label : String) :
    Except (Nat × String) Unit := do
  let origins := headers.filterMap fun (k, v) => if k.toLower == "origin" then some v else none
  let hosts   := headers.filterMap fun (k, v) => if k.toLower == "host" then some v else none
  let sfsList := headers.filterMap fun (k, v) => if k.toLower == "sec-fetch-site" then some v else none
  if origins.length > 1 || hosts.length > 1 || sfsList.length > 1 then
    throw (400, "duplicate origin or fetch-metadata header")
  let allowed? := allowedOrigins?.bind fun s => let t := trimWs s; if t.isEmpty then none else some t
  let originExplicitOk := match origins, allowed? with
    | [orig], some allow => isOriginExplicitlyAllowed allow orig
    | _, _               => false
  match origins with
  | [orig] =>
      let origTrim := trimWs orig
      if !(allowEmptyOrigin && origTrim.isEmpty) then
        let ok := match allowed? with
          | some allow => isOriginExplicitlyAllowed allow origTrim
          | none       => match hosts with | [h] => isOriginMatchingHost origTrim h | _ => false
        if !ok then throw (403, s!"cross-origin {label} rejected")
  | _ => pure ()
  match sfsList with
  | [sfs] =>
      let s := (trimWs sfs).toLower
      if s != "same-origin" && s != "none" && !originExplicitOk then
        throw (403, s!"cross-site {label} rejected")
  | _ => pure ()

/-- CSRF defense-in-depth for `POST /_qed/rpc/...`:
    1. Rejects duplicate `Origin`, `Host`, or `Sec-Fetch-Site` headers (400).
    2. Requires same-origin match with `Host` (or `QED_RPC_ALLOWED_ORIGINS`) when `Origin` is present (403).
    3. Rejects cross-site `Sec-Fetch-Site` unless explicitly allowed (403).
    4. Requires `Content-Type: application/x-protobuf` (415). -/
def checkRpcCsrf (headers : List (String × String)) (allowedOrigins? : Option String) :
    Except (Nat × String) Unit := do
  checkOriginAndFetchSite headers allowedOrigins? false "RPC"
  if !isProtobufContentType headers then
    throw (415, "RPC requires Content-Type: application/x-protobuf")

/-- CSWSH defense for RFC 6455 WebSocket upgrades on `/_qed/ws/<Server>`. -/
def checkWsOrigin (headers : List (String × String)) (allowedOrigins? : Option String) :
    Except (Nat × String) Unit :=
  checkOriginAndFetchSite headers allowedOrigins? true "WebSocket upgrade"

/-! ## Total Outbound HTTP/1.1 Client (Verified URL, Wire Formatting, Parsing, Chunked & SSRF) -/

private def maxRespBodyBytes : Nat := 256 * 1024 * 1024

/-- Generic fuel-bounded outbound socket reader; `check buf` returns `.ok (some v)` when done,
    `.ok none` to read another chunk, or `.error msg` to abort. `onEof` handles clean EOF. -/
private def readLoop {α : Type} (handle : UInt64) (chunkSz : UInt32)
    (check : ByteArray → Except String (Option α))
    (onEof : ByteArray → Except String α)
    (buf : ByteArray) : Nat → IO (Except String α)
  | 0 => return .error "HTTP read limit exceeded"
  | fuel + 1 => do
      match check buf with
      | .error e      => return .error e
      | .ok (some v)  => return .ok v
      | .ok none      =>
          match ← Prim.outboundReadSome handle chunkSz with
          | .error e    => return .error e
          | .ok chunk   =>
              if chunk.isEmpty then return onEof buf
              else readLoop handle chunkSz check onEof (buf ++ chunk) fuel

private def readUntilCrlfCrlf (handle : UInt64) : IO (Except String (ByteArray × Nat)) :=
  readLoop handle 8192
    (fun buf =>
      if let some pos := findCrlfCrlf buf then .ok (some (buf, pos))
      else if buf.size > maxReqHdrBytes then .error "HTTP response headers too large"
      else .ok none)
    (fun _ => .error "unexpected EOF in HTTP response headers")
    ByteArray.empty 4096

private def readAtLeast (handle : UInt64) (buf : ByteArray) (target : Nat) : IO (Except String ByteArray) :=
  readLoop handle 16384
    (fun b => if b.size >= target then .ok (some b) else .ok none)
    (fun _ => .error "truncated HTTP response body")
    buf 65536

private def readUntilEof (handle : UInt64) (buf : ByteArray) : IO (Except String ByteArray) :=
  readLoop handle 16384
    (fun b => if b.size > maxRespBodyBytes then .error "HTTP response body too large" else .ok none)
    .ok buf 65536

private def readCrlfLine (handle : UInt64) (buf : ByteArray) : IO (Except String (String × ByteArray)) :=
  readLoop handle 4096
    (fun b =>
      if let some pos := findCrlf b 0 then
        match String.fromUTF8? (b.extract 0 pos) with
        | some line => .ok (some (line, b.extract (pos + 2) b.size))
        | none      => .error "invalid UTF-8 in chunked framing"
      else if b.size > 4096 then .error "chunked header line too long"
      else .ok none)
    (fun _ => .error "unexpected EOF in chunked framing")
    buf 256

private def drainChunkTrailers (handle : UInt64) (rx : ByteArray) :
    Nat → IO (Except String Bool)
  | 0 => return .error "too many chunked trailers"
  | fuel + 1 => do
      match ← readCrlfLine handle rx with
      | .error e => return .error e
      | .ok (line, rest) =>
          if line.isEmpty then return .ok rest.isEmpty
          else drainChunkTrailers handle rest fuel

private def readChunkedBody (handle : UInt64) (rx out : ByteArray) :
    Nat → IO (Except String (ByteArray × Bool))
  | 0 => return .error "chunked response exceeded max chunks"
  | fuel + 1 => do
      match ← readCrlfLine handle rx with
      | .error e => return .error e
      | .ok (szLine, afterLine) =>
          let some sz := parseHexSize szLine maxRespBodyBytes
            | return .error "invalid chunk size"
          if sz == 0 then
            match ← drainChunkTrailers handle afterLine 256 with
            | .error e  => return .error e
            | .ok clean => return .ok (out, clean)
          else if out.size + sz > maxRespBodyBytes then
            return .error "chunked HTTP response body too large"
          else
            match ← readAtLeast handle afterLine (sz + 2) with
            | .error e => return .error e
            | .ok full =>
                if h : sz + 1 < full.size then
                  if full[sz]'(by omega) != 13 || full[sz + 1] != 10 then
                    return .error "missing CRLF after chunk data"
                  readChunkedBody handle (full.extract (sz + 2) full.size) (out ++ full.extract 0 sz) fuel
                else
                  return .error "truncated chunk data"

private def execHttpAttempt (method : String) (u : ParsedUrl) (wireReq : ByteArray)
    (ssrfGuard : Bool) : Nat → IO (Except String (Nat × ByteArray × Array (String × String)))
  | 0 => return .error "HTTP call failed"
  | attemptsLeft + 1 => do
      let acq ← Prim.outboundAcquire (if u.isTls then 1 else 0) u.host u.port
        (if ssrfGuard then 1 else 0) isBlockedIpBytes
      let (handleNat, reusedNat) ← match acq with
        | .ok p    => pure p
        | .error e => return .error e
      let handle := UInt64.ofNat handleNat
      let wasReused := reusedNat != 0
      match ← Prim.outboundWriteAll handle wireReq with
      | .error e =>
          Prim.outboundRelease handle 0
          if wasReused && attemptsLeft > 0 then execHttpAttempt method u wireReq ssrfGuard attemptsLeft
          else return .error e
      | .ok () =>
          match ← readUntilCrlfCrlf handle with
          | .error e =>
              Prim.outboundRelease handle 0
              if wasReused && attemptsLeft > 0 then execHttpAttempt method u wireReq ssrfGuard attemptsLeft
              else return .error e
          | .ok (rxBuf, hdrEnd) =>
              match parseHttpResponseHead (rxBuf.extract 0 hdrEnd) with
              | .error e =>
                  Prim.outboundRelease handle 0
                  return .error e
              | .ok head =>
                  let initBody := rxBuf.extract (hdrEnd + 4) rxBuf.size
                  let baseReuse := !head.connClose && !ssrfGuard
                  let bodyRes : Except String (ByteArray × Bool) ←
                    if method == "HEAD" || head.status == 204 || head.status == 304 then
                      pure (Except.ok (ByteArray.empty, baseReuse && initBody.isEmpty))
                    else if head.isChunked then
                      (·.map fun (b, clean) => (b, baseReuse && clean)) <$> readChunkedBody handle initBody ByteArray.empty 65536
                    else if let some cl := head.contentLen then
                      if cl > maxRespBodyBytes then pure (Except.error "Content-Length too large")
                      else (·.map fun full => (full.extract 0 cl, baseReuse && full.size == cl)) <$> readAtLeast handle initBody cl
                    else
                      (·.map fun b => (b, false)) <$> readUntilEof handle initBody
                  match bodyRes with
                  | .error e =>
                      Prim.outboundRelease handle 0
                      return .error e
                  | .ok (respBody, canReuse) =>
                      Prim.outboundRelease handle (if canReuse then 1 else 0)
                      return .ok (head.status, respBody, head.headers)

def execHttpCall (method url : String) (headers : Array (String × String))
    (body : ByteArray) (ssrfGuard : Bool) :
    IO (Except String (Nat × ByteArray × Array (String × String))) := do
  let u ← match parseHttpUrl url with
    | .ok p    => pure p
    | .error e => return .error e
  let wireReq ← match formatOutboundRequest method u headers body with
    | .ok w    => pure w
    | .error e => return .error e
  execHttpAttempt method u wireReq ssrfGuard 2

/-! ## GCP RS256 OAuth2 Token Exchange (Total Lean + Verified `base64UrlEncode`) -/

private structure GcpTokenCacheEntry where
  clientEmail : String
  scope       : String
  tokenUrl    : String
  accessToken : String
  expiresAt   : Nat

private def gcpCacheLookup (entries : Array GcpTokenCacheEntry)
    (email scope tokenUrl : String) (nowSec : Nat) : Option String :=
  entries.findSome? fun e =>
    if e.expiresAt > nowSec + 60 && e.clientEmail == email &&
       e.scope == scope && e.tokenUrl == tokenUrl then
      some e.accessToken
    else none

private def gcpCacheInsert (entries : Array GcpTokenCacheEntry)
    (entry : GcpTokenCacheEntry) : Array GcpTokenCacheEntry :=
  let filtered := entries.filter fun e =>
    !(e.clientEmail == entry.clientEmail && e.scope == entry.scope && e.tokenUrl == entry.tokenUrl)
  if filtered.size < 8 then
    filtered.push entry
  else
    let evictIdx := (List.range filtered.size).foldl (init := 0) fun best i =>
      if h1 : i < filtered.size then
        if h2 : best < filtered.size then
          if filtered[i].expiresAt < filtered[best].expiresAt then i else best
        else i
      else best
    if h : evictIdx < filtered.size then filtered.set evictIdx entry
    else filtered

/-- Mints an RS256-signed JWT using verified `Qed.Json` + total `Net.base64UrlEncode` and exchanges
    (caching in a thread-safe `StateBox` when provided) an OAuth2 Bearer access token for `scope`. -/
def fetchGcpBearerToken (cache? : Option (Prim.StateBox (Array GcpTokenCacheEntry)))
    (saJson scope : String) : IO (Except String String) := do
  let j ← match Json.parse saJson with
    | .ok v    => pure v
    | .error e => return .error s!"invalid GCP service account JSON: {e}"
  let some clientEmail := (j.get? "client_email").bind (·.str?)
    | return .error "GCP service account JSON missing `client_email`"
  let some privateKey := (j.get? "private_key").bind (·.str?)
    | return .error "GCP service account JSON missing `private_key`"
  let envTokUrl? := (← Prim.getEnv "QED_GCP_TOKEN_URL").bind fun s =>
    let t := trimWs s; if t.isEmpty then none else some t
  let tokenUri := match envTokUrl? with
    | some u => u
    | none   => ((j.get? "token_uri").bind (·.str?)).getD "https://oauth2.googleapis.com/token"
  let nowSec := ((← Prim.nowMs).toNat) / 1000
  if let some cache := cache? then
    if let some cached ← Prim.atomicRead cache (gcpCacheLookup · clientEmail scope tokenUri nowSec) then
      return .ok cached
  let jwtHdr := Json.render (.obj [("alg", .str "RS256"), ("typ", .str "JWT")])
  let claims := Json.render (.obj [
    ("iss",   .str clientEmail),
    ("scope", .str scope),
    ("aud",   .str tokenUri),
    ("iat",   .num ⟨Int.ofNat nowSec, 0⟩),
    ("exp",   .num ⟨Int.ofNat (nowSec + 3600), 0⟩)
  ])
  let signingInput := base64UrlEncode jwtHdr.toUTF8 ++ "." ++ base64UrlEncode claims.toUTF8
  let sigBytes ← match ← Prim.rsaSha256Sign privateKey signingInput.toUTF8 with
    | .ok b    => pure b
    | .error e => return .error e
  let formBody :=
    "grant_type=urn%3Aietf%3Aparams%3Aoauth%3Agrant-type%3Ajwt-bearer&assertion=" ++
    signingInput ++ "." ++ base64UrlEncode sigBytes
  let (status, respBody, _) ← match ← execHttpCall "POST" tokenUri
      #[("Content-Type", "application/x-www-form-urlencoded")] formBody.toUTF8 false with
    | .ok r    => pure r
    | .error e => return .error e
  let some respStr := String.fromUTF8? respBody
    | return .error "invalid UTF-8 in GCP OAuth2 response"
  if status < 200 || status >= 300 then
    return .error s!"OAuth2 HTTP {status}: {String.ofList (respStr.toList.take 400)}"
  let rj ← match Json.parse respStr with
    | .ok v    => pure v
    | .error e => return .error s!"invalid JSON in GCP OAuth2 response: {e}"
  let some accessToken := (rj.get? "access_token").bind (·.str?)
    | return .error "GCP OAuth2 response missing `access_token`"
  let expiresIn : Nat := match rj.get? "expires_in" with
    | some (.num n) =>
        if n.exponent == 0 && n.mantissa > 0 then min n.mantissa.toNat (86400 * 365) else 3600
    | _ => 3600
  if let some cache := cache? then
    let nowAfter := ((← Prim.nowMs).toNat) / 1000
    let entry : GcpTokenCacheEntry := {
      clientEmail, scope, tokenUrl := tokenUri, accessToken, expiresAt := nowAfter + expiresIn
    }
    Prim.atomicModify cache fun cur => (gcpCacheInsert cur entry, ())
  return .ok accessToken

/-! ## Constant-Time HMAC Session & Bearer Token Verification -/

private def constTimeXorLoop (a b : ByteArray) (i : Nat) (acc : UInt8) : UInt8 :=
  if h : i < a.size then
    if hb : i < b.size then
      constTimeXorLoop a b (i + 1) (acc ||| (a[i] ^^^ b[i]))
    else 1
  else acc
termination_by a.size - i

def constTimeEqBytes (a b : ByteArray) : Bool :=
  if a.size != b.size then false
  else constTimeXorLoop a b 0 0 == 0

def signUserToken (secret userId : String) : IO String := do
  let mac ← Prim.hmacSha256 secret.toUTF8 userId.toUTF8
  return userId ++ "." ++ Proto.encodeHex mac

def verifyUserToken (secret token : String) : IO (Option String) := do
  match (token.splitOn ".").reverse with
  | [] | [_] => return none
  | sigHex :: revUidParts =>
      let uid := String.intercalate "." revUidParts.reverse
      if uid.isEmpty || sigHex.length != 64 then return none
      match Proto.decodeHex sigHex with
      | .error _ => return none
      | .ok sigBytes =>
          let expected ← Prim.hmacSha256 secret.toUTF8 uid.toUTF8
          return if constTimeEqBytes sigBytes expected then some uid else none

/-! ## Inbound `RequestCtx` Extraction -/

private def parseCookiePairs (raw : String) : List (String × String) :=
  (raw.splitOn ";").foldl (fun acc seg =>
    let t := trimWs seg
    if t.isEmpty then acc
    else
      match t.splitOn "=" with
      | []       => acc
      | [k]      => acc ++ [(trimWs k, "")]
      | k :: vs  => acc ++ [(trimWs k, trimWs (String.intercalate "=" vs))]) []

private def extractBearer (authHdr : String) : Option String :=
  let t := trimWs authHdr
  if t.length > 7 && (String.ofList (t.toList.take 7)).toLower == "bearer " then
    let tok := trimWs (String.ofList (t.toList.drop 7))
    if tok.isEmpty then none else some tok
  else none

def buildRequestCtx (headers : Array (String × String)) (clientIp : String) : IO RequestCtx := do
  let hdrList := headers.toList
  let cookies := hdrList.foldl (fun acc (k, v) =>
    if k.toLower == "cookie" then acc ++ parseCookiePairs v else acc) []
  let bearer? := hdrList.findSome? fun (k, v) =>
    if k.toLower == "authorization" then extractBearer v else none
  let sessionCookie? := (cookies.find? fun (k, _) => k == "qed_session").map Prod.snd
  let authSecret? ← Prim.getEnv "QED_AUTH_SECRET"
  let userId? ← match authSecret? with
    | some sec =>
        if sec.isEmpty then pure none
        else match bearer?.orElse (fun _ => sessionCookie?) with
          | some tok => verifyUserToken sec tok
          | none     => pure none
    | none => pure none
  return { headers := hdrList, cookies, bearerToken := bearer?, userId := userId?, clientIp }

/-! ## Native `MonadServer IO` & `MonadAtomic σ IO` Instances -/

private def resolveBaseOrigin (req : OutboundReq) : IO String := do
  if req.serviceName == "Webhook" || req.ssrfGuard then
    return stripTrailingSlashes req.baseOrigin
  for key in ["QED_EXT_" ++ req.serviceName.toUpper ++ "_BASE", "QED_EXT_" ++ req.serviceName ++ "_BASE"] do
    if let some ov ← Prim.getEnv key then
      let t := stripTrailingSlashes (trimWs ov)
      if !t.isEmpty then return t
  return stripTrailingSlashes req.baseOrigin

private def requireSecretEnv (envVar : String) : IO (Except ApiError String) := do
  match ← Prim.getEnv envVar with
  | some tok =>
      if tok.isEmpty then return .error (ApiError.internal s!"secret environment variable `{envVar}` is empty")
      else return .ok tok
  | none =>
      return .error (ApiError.internal s!"missing secret environment variable `{envVar}`")

private def resolveAuthHeaders (gcpCache? : Option (Prim.StateBox (Array GcpTokenCacheEntry)))
    (spec : AuthSpec) : IO (Except ApiError (List (String × String))) := do
  match spec with
  | .none => return .ok []
  | .bearerSecret envVar =>
      return (← requireSecretEnv envVar).map fun tok => [("Authorization", "Bearer " ++ sanitizeHeader tok)]
  | .headerSecret hdrName envVar =>
      return (← requireSecretEnv envVar).map fun tok => [(sanitizeHeader hdrName, sanitizeHeader tok)]
  | .gcpServiceAccount envVar scope =>
      match ← requireSecretEnv envVar with
      | .error e => return .error e
      | .ok saJson =>
          match ← fetchGcpBearerToken gcpCache? saJson scope with
          | .ok accessToken => return .ok [("Authorization", "Bearer " ++ sanitizeHeader accessToken)]
          | .error errMsg   => return .error (ApiError.internal s!"GCP OAuth2 token exchange failed: {errMsg}")

@[implicit_reducible]
def mkNativeServerInst (gcpCache? : Option (Prim.StateBox (Array GcpTokenCacheEntry))) : MonadServer IO where
  httpCall req := do
    match ← resolveAuthHeaders gcpCache? req.auth with
    | .error e => return .error e
    | .ok authHdrs =>
        let base ← resolveBaseOrigin req
        let fullUrl := base ++ req.pathAndQuery
        let sanitizedReqHdrs := req.headers.map fun (k, v) => (sanitizeHeader k, sanitizeHeader v)
        let allHdrs := (sanitizedReqHdrs ++ authHdrs).toArray
        match ← execHttpCall req.method fullUrl allHdrs req.body req.ssrfGuard with
        | .error transportErr =>
            return .error (ApiError.internal s!"external HTTP transport error ({req.serviceName}): {transportErr}")
        | .ok (status, respBody, respHdrs) =>
            return .ok { status := status.toUInt32, body := respBody, headers := respHdrs.toList }
  readEnv := Prim.getEnv
  nowMs := Prim.nowMs
  randomHex := Prim.randomHex
  hmacSha256 := Prim.hmacSha256
  wsBroadcast := Prim.wsBroadcast

instance : MonadServer IO := mkNativeServerInst none

@[implicit_reducible]
def withStateBox {σ : Type} (box : Prim.StateBox σ) : MonadAtomic σ IO where
  runAtomic     := Prim.atomicModify box
  runAtomicRead := Prim.atomicRead box

/-! ## Fail-Closed Startup Secret Check -/

def verifyRequiredSecrets (secrets : Array String) : IO Bool := do
  secrets.foldlM (init := true) fun ok name => do
    match ← requireSecretEnv name with
    | .ok _    => return ok
    | .error _ =>
        IO.eprintln s!"✗ missing required secret `{name}` (set `{name}` before starting the server)"
        return false

/-! ## Full-Stack Native Server Runner (Verified HTTP/1.1 + Static + RFC 6455 WS + SSR) -/

private def devReloadSnippet : String :=
  "<script>(function(){let v=null;setInterval(async()=>{try{const t=await (await fetch('/__build_id',{cache:'no-store'})).text();if(v&&v!==t)location.reload();v=t;}catch(e){}},700)})()</script>\n</body>"

private def injectDevReload (htmlBytes : ByteArray) : ByteArray :=
  match String.fromUTF8? htmlBytes with
  | some html => (html.replace "</body>" devReloadSnippet).toUTF8
  | none      => htmlBytes

private structure WsFragState where
  active : Bool := false
  opcode : UInt8 := 0
  buf    : ByteArray := ByteArray.empty

private def handleMuxPayload
    (wsDispatchFn : RequestCtx → UInt8 → String → ByteArray → ByteArray → IO (Except ApiError ByteArray))
    (ctx : RequestCtx) (rawFrame : ByteArray)
    (subs : Array (Nat × String × ByteArray)) :
    IO (ByteArray × Array (Nat × String × ByteArray) × Array Prim.WsSubOp) := do
  let dropSub (sid : Nat) (arr : Array (Nat × String × ByteArray)) := arr.filter fun (s, _, _) => s != sid
  let errWire (sid : UInt32) (msg : String) := encodeWsFrame 0x02 (WsMuxFrame.encode (.err sid msg))
  match WsMuxFrame.decode rawFrame with
  | .error errMsg =>
      if h : 5 ≤ rawFrame.size then
        let sid : UInt32 :=
          ((rawFrame[1]'(by omega)).toUInt32 <<< 24) ||| ((rawFrame[2]'(by omega)).toUInt32 <<< 16) |||
          ((rawFrame[3]'(by omega)).toUInt32 <<< 8) ||| (rawFrame[4]'(by omega)).toUInt32
        return (errWire sid errMsg, subs, #[])
      else
        return (ByteArray.empty, subs, #[])
  | .ok (.sub sid ch params) =>
      if ch.isEmpty || ch.utf8ByteSize > 256 then
        return (errWire sid "invalid channel name length", subs, #[])
      let oldSub? := subs.find? fun (s, _, _) => s == sid.toNat
      let subsNoOld := dropSub sid.toNat subs
      if let some (_, oldCh, oldParams) := oldSub? then
        discard <| wsDispatchFn ctx 3 oldCh oldParams ByteArray.empty
      let remOps := if oldSub?.isSome then #[Prim.WsSubOp.removeSub sid.toNat] else #[]
      if subsNoOld.size >= 64 then
        return (errWire sid "too many subscriptions on connection", subsNoOld, remOps)
      match ← wsDispatchFn ctx 1 ch params ByteArray.empty with
      | .ok snapBytes =>
          let topic := ch ++ ":" ++ Proto.encodeHex params
          let wire := encodeWsFrame 0x02 (WsMuxFrame.encode (.joinOk sid snapBytes))
          return (wire, subsNoOld.push (sid.toNat, ch, params), #[.addSub sid.toNat topic ch params])
      | .error e =>
          return (errWire sid e.message, subsNoOld, remOps)
  | .ok (.unsub sid) =>
      if let some (_, ch, params) := subs.find? fun (s, _, _) => s == sid.toNat then
        discard <| wsDispatchFn ctx 3 ch params ByteArray.empty
        return (ByteArray.empty, dropSub sid.toNat subs, #[.removeSub sid.toNat])
      else return (ByteArray.empty, subs, #[])
  | .ok (.send sid payload) =>
      if let some (_, ch, params) := subs.find? fun (s, _, _) => s == sid.toNat then
        discard <| wsDispatchFn ctx 2 ch params payload
      return (ByteArray.empty, subs, #[])
  | .ok _ => return (ByteArray.empty, subs, #[])

private def stepWsRxLoop
    (wsDispatchFn : RequestCtx → UInt8 → String → ByteArray → ByteArray → IO (Except ApiError ByteArray))
    (ctx : RequestCtx) (rx : ByteArray) (off : Nat) (frag : WsFragState)
    (subs : Array (Nat × String × ByteArray)) (outWire : ByteArray) (ops : Array Prim.WsSubOp) :
    IO (Prim.WsStepOut WsFragState) := do
  match decodeWsFrame rx off with
  | .needMore =>
      return { consumed := off, outWire, closeFlag := 0, fragState := frag, subOps := ops }
  | .protocolErr code =>
      return { consumed := rx.size, outWire := outWire ++ encodeWsCloseFrame code,
               closeFlag := 1, fragState := frag, subOps := ops }
  | .frame fin opcode payload consumed =>
      if _ : consumed = 0 then
        return { consumed := off, outWire, closeFlag := 0, fragState := frag, subOps := ops }
      else
      let nextOff := off + consumed
      let (close, frag', subs', outWire', ops') ←
        if opcode == 0x08 then
          pure (true, frag, subs, outWire ++ encodeWsCloseFrame 1000, ops)
        else if opcode == 0x09 then
          pure (false, frag, subs, outWire ++ encodeWsFrame 0x0A payload, ops)
        else if opcode == 0x0A then
          pure (false, frag, subs, outWire, ops)
        else if opcode == 0x01 || opcode == 0x02 then
          if frag.active then
            pure (true, frag, subs, outWire ++ encodeWsCloseFrame 1002, ops)
          else if fin then
            let (w', s', o') ← if opcode == 0x02 then handleMuxPayload wsDispatchFn ctx payload subs else pure (ByteArray.empty, subs, #[])
            pure (false, frag, s', outWire ++ w', ops ++ o')
          else
            pure (false, { active := true, opcode, buf := payload }, subs, outWire, ops)
        else if opcode == 0x00 then
          if !frag.active then
            pure (true, frag, subs, outWire ++ encodeWsCloseFrame 1002, ops)
          else if frag.buf.size + payload.size > maxWsMsgBytes then
            pure (true, {}, subs, outWire ++ encodeWsCloseFrame 1009, ops)
          else
            let combined := frag.buf ++ payload
            if fin then
              let (w', s', o') ← if frag.opcode == 0x02 then handleMuxPayload wsDispatchFn ctx combined subs else pure (ByteArray.empty, subs, #[])
              pure (false, {}, s', outWire ++ w', ops ++ o')
            else
              pure (false, { frag with buf := combined }, subs, outWire, ops)
        else
          pure (true, frag, subs, outWire ++ encodeWsCloseFrame 1002, ops)
      if !close ∧ nextOff < rx.size then
        stepWsRxLoop wsDispatchFn ctx rx nextOff frag' subs' outWire' ops'
      else
        return { consumed := nextOff, outWire := outWire', closeFlag := if close then 1 else 0,
                 fragState := frag', subOps := ops' }
termination_by rx.size - off

def runFullstackWithDispatch {Model Msg : Type}
    (app : Qed.App Model Msg)
    (title : String)
    (serverShortName : String)
    (requiredSecrets : Array String)
    (dispatchFn : RequestCtx → String → ByteArray → IO (Except ApiError ByteArray))
    (port : UInt16)
    (staticDir : String)
    (devMode : Bool := false)
    (numWorkers : UInt32 := 0)
    (wsDispatchFn? : Option (RequestCtx → UInt8 → String → ByteArray → ByteArray → IO (Except ApiError ByteArray)) := none) : IO UInt32 := do
  if !(← verifyRequiredSecrets requiredSecrets) then
    return 1
  let staticDirFd ← Prim.openStaticDir staticDir
  let rpcPrefix := "/_qed/rpc/" ++ serverShortName ++ "/"
  let wsPath := "/_qed/ws/" ++ serverShortName

  let dispatchAppReq (req : ParsedReqHead) (body : ByteArray) (clientIp : String) : IO ByteArray := do
    if let some st := classifyStaticPath req.method req.target devMode then
      let headFlag : UInt8 := if st.isHead then 1 else 0
      if let some (fsize, fbytes) ← Prim.readStaticFile staticDirFd st.relPath headFlag then
        let head := formatHttpResponseHead 200 st.mime fsize req.keepAlive st.noStore
        return if st.isHead then head else head ++ fbytes
      else if st.isBuildId then
        return formatHttpResponse 200 st.mime "0".toUTF8 st.isHead req.keepAlive true
    let pathOnly := (req.target.splitOn "?").headD req.target
    let isHead := req.method == "HEAD"
    let (status, ctype, respBody) ←
      if req.method == "GET" && pathOnly == "/_qed/health" then
        pure (200, "application/json", "{\"ok\":true}".toUTF8)
      else do
        let ctx ← buildRequestCtx req.headers clientIp
        if req.method == "POST" && pathOnly.startsWith rpcPrefix then
          let allowedOrigins? ← Prim.getEnv "QED_RPC_ALLOWED_ORIGINS"
          match checkRpcCsrf ctx.headers allowedOrigins? with
          | .error (code, msg) => pure (code, "text/plain; charset=utf-8", msg.toUTF8)
          | .ok () =>
              let rpcMethod := String.ofList (pathOnly.toList.drop rpcPrefix.length)
              match ← dispatchFn ctx rpcMethod body with
              | .ok respBytes => pure (200, "application/x-protobuf", respBytes)
              | .error apiErr => pure (apiErr.httpStatus.toNat, "text/plain; charset=utf-8", apiErr.message.toUTF8)
        else if (req.method == "GET" || isHead) && !pathOnly.startsWith "/_qed/" then
          let ssrDispatchBytes : String → String → ByteArray → IO (Except String ByteArray) :=
            fun reqMethod url reqBody => do
              let uPath := (url.splitOn "?").headD url
              if reqMethod == "POST" && uPath.startsWith rpcPrefix then
                let mName := String.ofList (uPath.toList.drop rpcPrefix.length)
                match ← dispatchFn ctx mName reqBody with
                | .ok bs   => return .ok bs
                | .error e => return .error e.message
              else
                return .error s!"SSR unknown binary RPC endpoint: {url}"
          let rawHtml ← app.ssrRenderNativeBytes req.target title ssrDispatchBytes (sessionUser := ctx.userId)
          let finalHtml := if devMode then injectDevReload rawHtml else rawHtml
          pure (200, "text/html; charset=utf-8", finalHtml)
        else
          pure (404, "text/plain; charset=utf-8", "not found".toUTF8)
    return formatHttpResponse status ctype respBody isHead req.keepAlive false

  let onHead (headBytes : ByteArray) (clientIp : String) : IO (Prim.HttpHeadAction ParsedReqHead RequestCtx) := do
    match parseRequestHead headBytes with
    | .error (code, msg) =>
        return .doneClose (formatErrorResponse code msg)
    | .ok req =>
        let pathOnly := (req.target.splitOn "?").headD req.target
        if wsDispatchFn?.isSome && req.method == "GET" && pathOnly == wsPath &&
           (req.upgrade?.map String.toLower == some "websocket") then
          if !req.isHttp11 || (req.conn?.map (containsCI · "upgrade") != some true) ||
             req.wsVer? != some "13" then
            return .doneClose (formatErrorResponse 400 "invalid WebSocket upgrade headers")
          let some acceptB64 := req.wsKey?.bind wsComputeAccept
            | return .doneClose (formatErrorResponse 400 "invalid Sec-WebSocket-Key")
          let allowedOrigins? ← Prim.getEnv "QED_WS_ALLOWED_ORIGINS"
          match checkWsOrigin req.headers.toList allowedOrigins? with
          | .error (code, msg) => return .doneClose (formatErrorResponse code msg)
          | .ok () =>
              let baseCtx ← buildRequestCtx req.headers clientIp
              let cid ← Prim.randomHex 12
              return .wsUpgrade (formatWsUpgradeResponse acceptB64) { baseCtx with connId := "ws-" ++ cid }
        if req.contentLen == 0 then
          let wire ← dispatchAppReq req ByteArray.empty clientIp
          return if req.keepAlive then .doneKeepAlive wire else .doneClose wire
        else
          return if req.keepAlive then .needBodyKeep req.contentLen req else .needBodyClose req.contentLen req

  let onWsBytes (ctx : RequestCtx) (rx : ByteArray) (frag : WsFragState)
      (subs : Array (Nat × String × ByteArray)) : IO (Prim.WsStepOut WsFragState) := do
    match wsDispatchFn? with
    | some wsDispatchFn => stepWsRxLoop wsDispatchFn ctx rx 0 frag subs ByteArray.empty #[]
    | none => return { consumed := rx.size, outWire := ByteArray.empty, closeFlag := 1, fragState := frag, subOps := #[] }

  let onWsLeave (ctx : RequestCtx) (ch : String) (params : ByteArray) : IO Unit := do
    if let some wsDispatchFn := wsDispatchFn? then
      discard <| wsDispatchFn ctx 3 ch params ByteArray.empty

  Prim.serveNative port numWorkers ({} : WsFragState) onHead dispatchAppReq onWsBytes onWsLeave

def runStatefulFullstack {σ Model Msg : Type}
    (app : Qed.App Model Msg) (title serverShortName : String)
    (initState : σ) (requiredSecrets : Array String)
    (dispatchM : {m : Type → Type} → [Monad m] → [MonadServer m] → [MonadAtomic σ m] →
        RequestCtx → String → ByteArray → m (Except ApiError ByteArray))
    (port : UInt16) (staticDir : String) (devMode : Bool := false) (numWorkers : UInt32 := 0)
    (wsDispatchM? : Option ({m : Type → Type} → [Monad m] → [MonadServer m] → [MonadAtomic σ m] →
        RequestCtx → UInt8 → String → ByteArray → ByteArray → m (Except ApiError ByteArray)) := none) : IO UInt32 := do
  let box ← Prim.mkStateBox initState
  let gcpCache ← Prim.mkStateBox (#[] : Array GcpTokenCacheEntry)
  let srvInst : MonadServer IO := mkNativeServerInst (some gcpCache)
  let atomicInst : MonadAtomic σ IO := withStateBox box
  runFullstackWithDispatch app title serverShortName requiredSecrets
    (fun ctx mName reqBytes => @dispatchM IO _ srvInst atomicInst ctx mName reqBytes)
    port staticDir devMode numWorkers
    (wsDispatchM?.map fun wsM ctx kind ch params payload => @wsM IO _ srvInst atomicInst ctx kind ch params payload)

def runStatelessFullstack {Model Msg : Type}
    (app : Qed.App Model Msg) (title serverShortName : String)
    (requiredSecrets : Array String)
    (dispatchM : {m : Type → Type} → [Monad m] → [MonadServer m] →
        RequestCtx → String → ByteArray → m (Except ApiError ByteArray))
    (port : UInt16) (staticDir : String) (devMode : Bool := false) (numWorkers : UInt32 := 0)
    (wsDispatchM? : Option ({m : Type → Type} → [Monad m] → [MonadServer m] →
        RequestCtx → UInt8 → String → ByteArray → ByteArray → m (Except ApiError ByteArray)) := none) : IO UInt32 := do
  let gcpCache ← Prim.mkStateBox (#[] : Array GcpTokenCacheEntry)
  let srvInst : MonadServer IO := mkNativeServerInst (some gcpCache)
  runFullstackWithDispatch app title serverShortName requiredSecrets
    (fun ctx mName reqBytes => @dispatchM IO _ srvInst ctx mName reqBytes)
    port staticDir devMode numWorkers
    (wsDispatchM?.map fun wsM ctx kind ch params payload => @wsM IO _ srvInst ctx kind ch params payload)

/-! ## `qedServerMain <FullstackName>` Entrypoint Generator -/

syntax (name := qedServerMainCmd) "qedServerMain " ident : command

open Lean Elab Command in
@[command_elab qedServerMainCmd]
def elabQedServerMain : CommandElab := fun stx => do
  let fsIdent : Ident := ⟨stx[1]⟩
  let env ← getEnv
  let currNs ← getCurrNamespace
  let fsMap := fullstackRegistry.getState env
  let cand1 := currNs ++ fsIdent.getId
  let some fsInfo := (fsMap.find? cand1).orElse (fun _ =>
      fsMap.toList.findSome? fun (k, v) =>
        if k == fsIdent.getId || k.getString! == fsIdent.getId.toString then some v else none)
    | throwErrorAt fsIdent s!"unknown `fullstack` declaration `{fsIdent.getId}`"
  let srvMap := serverRegistry.getState env
  let some srvInfo := srvMap.find? fsInfo.serverName
    | throwErrorAt fsIdent s!"internal error: `server` `{fsInfo.serverName}` not found in registry"
  let cliAppId := mkIdentFrom fsIdent (fsInfo.fullstackName ++ `clientApp)
  let titleLit := Syntax.mkStrLit fsInfo.title
  let shortLit := Syntax.mkStrLit srvInfo.shortName
  let secretsId := mkIdentFrom fsIdent (srvInfo.serverName ++ `secrets)
  let dispatchId := mkIdentFrom fsIdent (srvInfo.serverName ++ `dispatchM)
  let wsDispatchId := mkIdentFrom fsIdent (srvInfo.serverName ++ `wsDispatchM)
  let hasWs := !srvInfo.channels.isEmpty
  let mainId := mkIdent `main
  let runnerCall ← if srvInfo.hasState then
    let initStateId := mkIdentFrom fsIdent (srvInfo.serverName ++ `initState)
    let wsArg ← if hasWs then
      `(some (fun {m} [Monad m] [Qed.Server.MonadServer m] [Qed.Server.MonadAtomic _ m] => $wsDispatchId))
    else `(none)
    `(Qed.Server.Native.runStatefulFullstack
        $cliAppId $titleLit $shortLit $initStateId $secretsId
        (fun {m} [Monad m] [Qed.Server.MonadServer m] [Qed.Server.MonadAtomic _ m] => $dispatchId)
        port staticDir devMode numWorkers $wsArg)
  else
    let wsArg ← if hasWs then
      `(some (fun {m} [Monad m] [Qed.Server.MonadServer m] => $wsDispatchId))
    else `(none)
    `(Qed.Server.Native.runStatelessFullstack
        $cliAppId $titleLit $shortLit $secretsId
        (fun {m} [Monad m] [Qed.Server.MonadServer m] => $dispatchId)
        port staticDir devMode numWorkers $wsArg)
  elabCommand (← `(command|
    def $mainId:ident (args : List String) : IO UInt32 := do
      let staticDir := args[0]?.getD "dist"
      let envPort ← Qed.Server.Prim.getEnv "PORT"
      let port := ((args[1]?.getD (envPort.getD "8000")).toNat?.getD 8000).toUInt16
      let devMode := args.contains "--dev"
      let numWorkers := (((← Qed.Server.Prim.getEnv "QED_WORKERS").bind String.toNat?).getD 0).toUInt32
      $runnerCall:term))

end Qed.Server.Native
