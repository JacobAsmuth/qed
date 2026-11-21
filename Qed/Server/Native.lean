import Qed.Ssr
import Qed.Server.Core
import Qed.Server.Jobs
import Qed.Server.Net
import Qed.Server.Http
import Qed.Server.Prim
import Qed.Server.Db.HttpSql
import Qed.Server.Db.PgWire
import Qed.Auth.Oidc

namespace Qed.Server.Native

open Qed.Server.Net
open Qed.Server.Http

/-! ## Unified CSRF & CSWSH Origin / Fetch-Metadata Verification -/

/-- True iff `origin` has an `http://` or `https://` scheme and its authority matches `host`
    (case-insensitive, rejecting `null`, paths, and empty hosts). -/
def isOriginMatchingHost (origin host : String) : Bool :=
  let h := trimWs host
  if h.isEmpty then false
  else
    let o := trimWs origin
    let authStart : Nat :=
      if startsWithCI o "http://" then 7
      else if startsWithCI o "https://" then 8
      else 0
    if authStart == 0 then false
    else
      let rec scanEnd (j : Nat) (hj : j ≤ o.utf8ByteSize) : Nat :=
        if _ : authStart < j then
          if o.getUTF8Byte ⟨j - 1⟩ (show j - 1 < o.utf8ByteSize by omega) == 47 then
            scanEnd (j - 1) (by omega)
          else j
        else authStart
      termination_by j
      let authEnd := scanEnd o.utf8ByteSize (Nat.le_refl _)
      authStart < authEnd && !hasByteInRange o authStart authEnd 47 &&
        eqCIRange o authStart authEnd h 0 h.utf8ByteSize

/-- True iff `origin` matches `*` or an entry in the comma-separated allowlist `allowed`. -/
def isOriginExplicitlyAllowed (allowed origin : String) : Bool :=
  let a := trimWs allowed
  if a.isEmpty then false
  else if a == "*" then true
  else
    let o := (trimWs origin).toLower
    !o.isEmpty && (a.splitOn ",").any fun entry => (trimWs entry).toLower == o

private def checkOriginAndFetchSiteParsed (origin? host? secFetchSite? : Option String)
    (dupAny : Bool) (allowedOrigins? : Option String) (allowEmptyOrigin : Bool) (label : String) :
    Except (Nat × String) Unit := do
  if dupAny then
    throw (400, "duplicate origin or fetch-metadata header")
  if origin?.isSome || secFetchSite?.isSome then
    let allowed? := allowedOrigins?.bind fun s => let t := trimWs s; if t.isEmpty then none else some t
    let originExplicitOk := match origin?, allowed? with
      | some orig, some allow => isOriginExplicitlyAllowed allow orig
      | _, _                  => false
    if let some orig := origin? then
      let origTrim := trimWs orig
      if !(allowEmptyOrigin && origTrim.isEmpty) then
        let ok := match allowed? with
          | some allow => isOriginExplicitlyAllowed allow origTrim
          | none       => match host? with | some h => isOriginMatchingHost origTrim h | none => false
        if !ok then throw (403, s!"cross-origin {label} rejected")
    if let some sfs := secFetchSite? then
      let s := trimWs sfs
      if !eqCI s "same-origin" && !eqCI s "none" && !originExplicitOk then
        throw (403, s!"cross-site {label} rejected")

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

private def compactRx (buf : ByteArray) (off : Nat) : ByteArray × Nat :=
  if off >= buf.size then (ByteArray.empty, 0)
  else if off >= 65536 then (buf.extract off buf.size, 0)
  else (buf, off)

private def readCrlfLineAt (handle : UInt64) (buf : ByteArray) (off : Nat) :
    IO (Except String (String × ByteArray × Nat)) :=
  readLoop handle 4096
    (fun b =>
      if let some pos := findCrlf b off then
        match String.fromUTF8? (b.extract off pos) with
        | some line => .ok (some (line, b, pos + 2))
        | none      => .error "invalid UTF-8 in chunked framing"
      else if b.size - off > 4096 then .error "chunked header line too long"
      else .ok none)
    (fun _ => .error "unexpected EOF in chunked framing")
    buf 256

private def drainChunkTrailers (handle : UInt64) (rx : ByteArray) (off : Nat) :
    Nat → IO (Except String Bool)
  | 0 => return .error "too many chunked trailers"
  | fuel + 1 => do
      match ← readCrlfLineAt handle rx off with
      | .error e => return .error e
      | .ok (line, rx1, off1) =>
          if line.isEmpty then return .ok (off1 >= rx1.size)
          else drainChunkTrailers handle rx1 off1 fuel

private def readChunkedBody (handle : UInt64) (rx : ByteArray) (off : Nat) (out : ByteArray) :
    Nat → IO (Except String (ByteArray × Bool))
  | 0 => return .error "chunked response exceeded max chunks"
  | fuel + 1 => do
      let (rx0, off0) := compactRx rx off
      match ← readCrlfLineAt handle rx0 off0 with
      | .error e => return .error e
      | .ok (szLine, rx1, off1) =>
          let some sz := parseHexSize szLine maxRespBodyBytes
            | return .error "invalid chunk size"
          if sz == 0 then
            match ← drainChunkTrailers handle rx1 off1 256 with
            | .error e  => return .error e
            | .ok clean => return .ok (out, clean)
          else if out.size + sz > maxRespBodyBytes then
            return .error "chunked HTTP response body too large"
          else
            match ← readAtLeast handle rx1 (off1 + sz + 2) with
            | .error e => return .error e
            | .ok full =>
                if h : off1 + sz + 1 < full.size then
                  if full[off1 + sz]'(by omega) != 13 || full[off1 + sz + 1] != 10 then
                    return .error "missing CRLF after chunk data"
                  let out' := full.copySlice off1 out out.size sz
                  readChunkedBody handle full (off1 + sz + 2) out' fuel
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
      let canRetry := wasReused && isIdempotentHttpMethod method && attemptsLeft > 0
      match ← Prim.outboundWriteAll handle wireReq with
      | .error e =>
          Prim.outboundRelease handle 0
          if canRetry then execHttpAttempt method u wireReq ssrfGuard attemptsLeft
          else return .error e
      | .ok () =>
          match ← readUntilCrlfCrlf handle with
          | .error e =>
              Prim.outboundRelease handle 0
              if canRetry then execHttpAttempt method u wireReq ssrfGuard attemptsLeft
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
                      (·.map fun (b, clean) => (b, baseReuse && clean)) <$> readChunkedBody handle initBody 0 ByteArray.empty 65536
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

/-! ## Constant-Time HMAC Session & Bearer Token Verification (Expiring `v1` + Rotation) -/

/-- Mints an expiring `v1.<expSec>.<userId>.<hmacHex>` session token signed with HMAC-SHA256. -/
def signUserToken (secret userId : String) (ttlSec : Nat := 86400) : IO String := do
  let nowSec := ((← Prim.nowMs).toNat) / 1000
  let expSec := nowSec + ttlSec
  let payload := s!"v1.{expSec}.{userId}"
  let mac ← Prim.hmacSha256 secret.toUTF8 payload.toUTF8
  return s!"{payload}.{Proto.encodeHex mac}"

/-- Verifies either an expiring `v1.<expSec>.<userId>.<hmacHex>` token or (unless
    `requireExpiring` is true) a legacy `<userId>.<hmacHex>` token using Rust's constant-time
    `hmac::Mac::verify_slice` across active + rotated secrets. -/
def verifyUserTokenWithNow (secrets : List String) (token : String) (nowSec : Nat)
    (requireExpiring : Bool := false) : IO (Option String) := do
  if secrets.isEmpty then return none
  match (token.splitOn ".").reverse with
  | [] | [_] => return none
  | sigHex :: revPrefixParts =>
      if sigHex.length != 64 then return none
      let sigBytes ← match Proto.decodeHex sigHex with
        | .error _ => return none
        | .ok b    => pure b
      let prefixParts := revPrefixParts.reverse
      let payload := String.intercalate "." prefixParts
      match prefixParts with
      | "v1" :: expStr :: uidParts =>
          let uid := String.intercalate "." uidParts
          if uid.isEmpty then return none
          let some expSec := parseStrictU64 expStr 18446744073709551615 | return none
          if nowSec >= expSec then return none
          return if ← Qed.Auth.Oidc.anySecretVerify secrets payload.toUTF8 sigBytes then some uid else none
      | _ =>
          if requireExpiring || payload.isEmpty then return none
          return if ← Qed.Auth.Oidc.anySecretVerify secrets payload.toUTF8 sigBytes then some payload else none

def verifyUserToken (secret token : String) (requireExpiring : Bool := false) : IO (Option String) := do
  if secret.isEmpty then return none
  let nowSec := ((← Prim.nowMs).toNat) / 1000
  verifyUserTokenWithNow [secret] token nowSec requireExpiring

/-! ## Startup-Cached Server Config & Inbound `RequestCtx` Extraction -/

structure ServerConfig where
  authSecrets        : List String := []
  requireExpiring    : Bool := false
  rpcAllowedOrigins? : Option String := none
  wsAllowedOrigins?  : Option String := none
  bindHost           : String := "0.0.0.0"
  csp?               : Option String := some defaultCsp

private def loadNonEmptyEnv (name : String) : IO (Option String) := do
  match ← Prim.getEnv name with
  | some v => let t := trimWs v; return if t.isEmpty then none else some t
  | none   => return none

def loadServerConfig (devMode : Bool) : IO ServerConfig := do
  let secCur?  ← Prim.getEnv "QED_AUTH_SECRET"
  let secPrev? ← Prim.getEnv "QED_AUTH_SECRET_PREV"
  let secrets  := ([secCur?, secPrev?].filterMap id).filter (!·.isEmpty)
  let reqExp   := (← loadNonEmptyEnv "QED_AUTH_REQUIRE_EXP") == some "1"
  let rpcOrig? ← loadNonEmptyEnv "QED_RPC_ALLOWED_ORIGINS"
  let wsOrig?  ← loadNonEmptyEnv "QED_WS_ALLOWED_ORIGINS"
  let host?    ← loadNonEmptyEnv "QED_HOST"
  let bindHost ← match host? with
    | some h => pure h
    | none   => match ← loadNonEmptyEnv "HOST" with
        | some h => pure h
        | none   => pure (if devMode then "127.0.0.1" else "0.0.0.0")
  let csp? ← match ← loadNonEmptyEnv "QED_CSP" with
    | some v =>
        let lv := v.toLower
        if lv == "off" || lv == "none" || lv == "disabled" then pure none
        else pure (some (sanitizeHeader v))
    | none => pure (some defaultCsp)
  return {
    authSecrets        := secrets
    requireExpiring    := reqExp
    rpcAllowedOrigins? := rpcOrig?
    wsAllowedOrigins?  := wsOrig?
    bindHost           := bindHost
    csp?               := csp?
  }

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

/-! ## Unified Native Database Dispatcher (SQLite, PostgreSQL v3 Wire & HTTP SQL) -/

private inductive ResolvedDbTransport where
  | sqlite   (path : String)
  | postgres (url : String)
  | httpSql  (url : String) (bearer? : Option String)
  | d1       (accountId dbId token : String)
  | turso    (url token : String)

private def stripSqliteScheme (u : String) : String :=
  if u.startsWith "sqlite://" then String.ofList (u.toList.drop 9)
  else if u.startsWith "sqlite:" then String.ofList (u.toList.drop 7)
  else if u.startsWith "file:" then String.ofList (u.toList.drop 5)
  else u

private def resolveUrlString (u : String) (token? : Option String) : Except String ResolvedDbTransport :=
  let t := trimWs u
  if t.startsWith "postgres://" || t.startsWith "postgresql://" then
    .ok (.postgres t)
  else if t.startsWith "sqlite:" || t.startsWith "file:" || t == ":memory:" ||
          t.endsWith ".db" || t.endsWith ".sqlite" || t.endsWith ".sqlite3" then
    .ok (.sqlite (stripSqliteScheme t))
  else if t.startsWith "http://" || t.startsWith "https://" then
    .ok (.httpSql t token?)
  else
    .error s!"unrecognized database URL scheme: `{t}` (expected postgres://, sqlite://, or https://)"

private def requireEnv (envVar label : String) (default? : Option String := none) : IO (Except String String) := do
  match (← loadNonEmptyEnv envVar).orElse (fun _ => default?) with
  | some v => return .ok v
  | none   => return .error s!"missing {label} `{envVar}`"

private def resolveDbEndpoint (ep : Db.DbEndpoint) : IO (Except String ResolvedDbTransport) := do
  match ep with
  | .urlEnv envVar =>
      match ← requireEnv envVar "database URL environment variable" with
      | .error e => return .error e
      | .ok u    => return resolveUrlString u (← loadNonEmptyEnv (envVar ++ "_TOKEN"))
  | .postgresEnv envVar =>
      return (← requireEnv envVar "PostgreSQL URL environment variable").map .postgres
  | .postgresUrl url => return .ok (.postgres (trimWs url))
  | .sqlitePath path => return .ok (.sqlite (stripSqliteScheme path))
  | .sqliteEnv envVar def? =>
      return (← requireEnv envVar "SQLite path environment variable" def?).map (fun p => .sqlite (stripSqliteScheme p))
  | .cloudflareD1 accEnv accDef? dbEnv dbDef? tokSecret =>
      match ← requireEnv accEnv "Cloudflare account env" accDef?,
            ← requireEnv dbEnv "Cloudflare D1 database env" dbDef?,
            ← requireEnv tokSecret "Cloudflare D1 token secret" with
      | .ok acc, .ok db, .ok tok => return .ok (.d1 acc db tok)
      | .error e, _, _ | _, .error e, _ | _, _, .error e => return .error e
  | .turso urlEnv tokSecret =>
      match ← requireEnv urlEnv "Turso URL env", ← requireEnv tokSecret "Turso token secret" with
      | .ok u, .ok tok => return .ok (.turso u tok)
      | .error e, _ | _, .error e => return .error e
  | .httpSql urlEnv tokSecret? =>
      match ← requireEnv urlEnv "HTTP SQL URL env" with
      | .error e => return .error e
      | .ok u =>
          let tok? ← match tokSecret? with | some ts => loadNonEmptyEnv ts | none => pure none
          return .ok (.httpSql u tok?)

private def resolveDbConfig (cfg : Db.DbConfig) : IO (Except ApiError ResolvedDbTransport) := do
  match ← resolveDbEndpoint cfg.endpoint with
  | .ok tr => return .ok tr
  | .error primaryErr =>
      match cfg.devFallback? with
      | some fb =>
          match ← resolveDbEndpoint fb with
          | .ok tr => return .ok tr
          | .error fbErr => return .error (ApiError.internal s!"database `{cfg.name}` unavailable: {primaryErr} (fallback: {fbErr})")
      | none =>
          return .error (ApiError.internal s!"database `{cfg.name}` unavailable: {primaryErr}")

private def d1QueryUrl (acc db : String) : String :=
  s!"https://api.cloudflare.com/client/v4/accounts/{Qed.encodeSeg acc}/d1/database/{Qed.encodeSeg db}/query"

private def tursoPipelineUrl (baseUrl : String) : String :=
  stripTrailingSlashes baseUrl ++ "/v2/pipeline"

private def execHttpSqlRaw (url : String) (bearer? : Option String) (body : ByteArray) :
    IO (Except ApiError String) := do
  let baseHdrs : Array (String × String) := #[("Content-Type", "application/json"), ("Accept", "application/json")]
  let hdrs := match bearer? with
    | some tok => baseHdrs.push ("Authorization", "Bearer " ++ sanitizeHeader tok)
    | none     => baseHdrs
  match ← execHttpCall "POST" url hdrs body false with
  | .error e => return .error (ApiError.internal s!"HTTP SQL transport error: {e}")
  | .ok (status, respBody, _) =>
      let txt := (String.fromUTF8? respBody).getD ""
      if 200 ≤ status && status < 300 then return .ok txt
      else return .error (ApiError.internal s!"HTTP SQL error {status}: {txt}")

private def execHttpTransportStmt (tr : ResolvedDbTransport) (sql : String) (params : Array Db.SqlVal) :
    IO (Except ApiError String) :=
  match tr with
  | .httpSql url bearer? => execHttpSqlRaw url bearer? (Db.HttpSql.encodeGenericQueryBody sql params .sqlite)
  | .d1 acc db tok       => execHttpSqlRaw (d1QueryUrl acc db) (some tok) (Db.HttpSql.encodeD1QueryBody sql params)
  | .turso baseUrl tok   => execHttpSqlRaw (tursoPipelineUrl baseUrl) (some tok) (Db.HttpSql.encodeTursoPipelineBody sql params)
  | _                    => return .error (ApiError.internal "unexpected non-HTTP SQL transport")

private def execRawOnTransport (tr : ResolvedDbTransport) (sqlSqlite sqlPg : String)
    (params : Array Db.SqlVal) (d1Cols : List String) (sqlHttp? : Option String := none)
    (decodeErrPrefix? : Option String := none) : IO (Except ApiError Db.DbResult) := do
  let sqlH := sqlHttp?.getD sqlSqlite
  let mapDec (defaultPfx : String) (r : Except String Db.DbResult) : Except ApiError Db.DbResult :=
    r.mapError fun e => ApiError.internal s!"{decodeErrPrefix?.getD defaultPfx}: {e}"
  match tr with
  | .sqlite path =>
      return (← Prim.sqliteExec path sqlSqlite params).mapError ApiError.internal
  | .postgres url =>
      return (← Db.PgWire.execParameterized url sqlPg params).mapError ApiError.internal
  | .httpSql _ _ | .d1 _ _ _ | .turso _ _ =>
      match ← execHttpTransportStmt tr sqlH params with
      | .error e => return .error e
      | .ok raw  =>
          match tr with
          | .httpSql _ _ => return mapDec "HTTP SQL result decode failed" (Db.decodeTaggedResultJson raw)
          | .d1 _ _ _    => return mapDec "Cloudflare D1 result decode failed" (Db.HttpSql.decodeD1Response raw d1Cols)
          | _            => return mapDec "Turso result decode failed" (Db.HttpSql.decodeTursoResponse raw)

private def execDdlOnTransport (tr : ResolvedDbTransport) (sqliteStmts : List String)
    (pgDdl : String) : IO (Except ApiError Unit) := do
  match tr with
  | .sqlite path =>
      return (← Prim.sqliteDdl path (String.intercalate ";\n" sqliteStmts)).mapError ApiError.internal
  | .postgres url =>
      return (← Db.PgWire.execDdl url pgDdl).mapError ApiError.internal
  | .httpSql _ _ | .d1 _ _ _ | .turso _ _ =>
      for stmt in sqliteStmts do
        if let .error e ← execHttpTransportStmt tr stmt #[] then return .error e
      return .ok ()

private def rowStrAt (row : Db.DbRow) (idx : Nat) : Option String :=
  match row[idx]? with
  | some (.text s) => some s
  | _ => none

private def introspectSqliteTable (path : String) (tbl : Db.TableSchema) :
    IO (Except ApiError (Bool × List String × List String)) := do
  let colRes ← match ← Prim.sqliteExec path ("PRAGMA table_info(" ++ tbl.name.quoteIdent ++ ")") #[] with
    | .error e => return .error (ApiError.internal s!"sqlite table introspection failed: {e}")
    | .ok r    => pure r
  if colRes.rows.isEmpty then return .ok (false, [], [])
  let cols := colRes.rows.toList.filterMap fun r => rowStrAt r 1
  match ← Prim.sqliteExec path ("PRAGMA index_list(" ++ tbl.name.quoteIdent ++ ")") #[] with
  | .error e   => return .error (ApiError.internal s!"sqlite index introspection failed: {e}")
  | .ok idxRes => return .ok (true, cols, idxRes.rows.toList.filterMap fun r => rowStrAt r 1)

private def introspectPostgresTable (url : String) (tbl : Db.TableSchema) :
    IO (Except String (Bool × List String × List String)) := do
  let colSql := "SELECT column_name FROM information_schema.columns WHERE table_schema = current_schema() AND table_name = $1"
  let colRes ← match ← Db.PgWire.execParameterized url colSql #[.text tbl.name.raw] with
    | .error e => return .error e
    | .ok r    => pure r
  if colRes.rows.isEmpty then return .ok (false, [], [])
  let cols := colRes.rows.toList.filterMap fun r => rowStrAt r 0
  let idxSql := "SELECT indexname FROM pg_indexes WHERE schemaname = current_schema() AND tablename = $1"
  let idxs := match ← Db.PgWire.execParameterized url idxSql #[.text tbl.name.raw] with
    | .error _   => []
    | .ok idxRes => idxRes.rows.toList.filterMap fun r => rowStrAt r 0
  return .ok (true, cols, idxs)

private def applyMigrationSteps (dialect : Db.SqlDialect) (steps : List Db.MigrationStep)
    (runDdl : String → IO (Except String Unit)) : IO (Except ApiError (List Db.MigrationStep)) := do
  match Db.verifyMigrationSafe steps with
  | .error e => return .error (ApiError.internal e)
  | .ok () =>
      let ddl := Db.renderMigrationDdl dialect steps
      if !ddl.isEmpty then
        if let .error e ← runDdl ddl then return .error (ApiError.internal e)
      return .ok steps

/-- Idempotently initializes and applies verified additive schema migrations (`createTable`,
    safe `addColumn`, `createIndex`) for all tables in `cfg`, returning the applied steps. -/
def migrateDatabase (cfg : Db.DbConfig) : IO (Except ApiError (List Db.MigrationStep)) := do
  if cfg.tables.isEmpty then return .ok []
  match ← resolveDbConfig cfg with
  | .error e => return .error e
  | .ok (.sqlite path) =>
      let mut allSteps : List Db.MigrationStep := []
      for tbl in cfg.tables do
        match ← introspectSqliteTable path tbl with
        | .error e => return .error e
        | .ok (exists_, cols, idxs) => allSteps := allSteps ++ Db.diffTableSchema cols idxs tbl exists_
      applyMigrationSteps .sqlite allSteps (Prim.sqliteDdl path)
  | .ok (.postgres url) =>
      let mut allSteps : List Db.MigrationStep := []
      let mut introspectOk := true
      for tbl in cfg.tables do
        if introspectOk then
          match ← introspectPostgresTable url tbl with
          | .error _ => introspectOk := false
          | .ok (exists_, cols, idxs) => allSteps := allSteps ++ Db.diffTableSchema cols idxs tbl exists_
      if introspectOk then
        applyMigrationSteps .postgres allSteps (Db.PgWire.execDdl url)
      else
        return (← Db.PgWire.execDdl url (Db.renderDatabaseDdl .postgres cfg.tables))
          |>.map (fun () => cfg.tables.map .createTable) |>.mapError ApiError.internal
  | .ok tr =>
      let stmts := cfg.tables.flatMap (·.renderDdlStatements .sqlite)
      return (← execDdlOnTransport tr stmts "").map fun () => cfg.tables.map .createTable

private def execNativeDbDdl (cfg : Db.DbConfig) : IO (Except ApiError Unit) :=
  return (← migrateDatabase cfg).map fun _ => ()

/-- Active pinned PostgreSQL transaction connections keyed by monotonic transaction ID. -/
initialize pgTxBox : IO.Ref (UInt64 × Std.HashMap UInt64 Db.PgWire.PgConn) ←
  IO.mkRef (1, {})

private def popPgTx (txId : UInt64) : IO (Option Db.PgWire.PgConn) :=
  pgTxBox.modifyGet fun (nextId, m) =>
    match m[txId]? with
    | some c => (some c, (nextId, m.erase txId))
    | none   => (none, (nextId, m))

private def withTxTransport {α : Type} (cfg : Db.DbConfig)
    (onSqlite : String → IO (Except ApiError α))
    (onPg : String → IO (Except ApiError α)) : IO (Except ApiError α) := do
  match ← resolveDbConfig cfg with
  | .error e            => return .error e
  | .ok (.sqlite path)  => onSqlite path
  | .ok (.postgres url) => onPg url
  | .ok _ => return .error (ApiError.internal "multi-statement transactions require SQLite or PostgreSQL transport")

private def finishPgTx (conn : Db.PgWire.PgConn) (cmd : String) : IO (Except ApiError Unit) := do
  let (res, conn') ← Db.PgWire.execSimpleOnConn conn cmd
  match res with
  | .ok cFinal => Db.PgWire.releaseConn cFinal; return .ok ()
  | .error e   => Db.PgWire.releaseConn { conn' with healthy := false }
                  return .error (ApiError.internal s!"postgres {cmd} failed: {e}")

private def execNativeDbTxBegin (cfg : Db.DbConfig) : IO (Except ApiError UInt64) :=
  withTxTransport cfg
    (fun path => return (← Prim.sqliteTxBegin path).mapError ApiError.internal)
    (fun url => do
      let p ← match Db.PgWire.parsePgUrl url with | .ok p => pure p | .error e => return .error (ApiError.internal e)
      match ← Db.PgWire.acquireConn p with
      | .error e => return .error (ApiError.internal e)
      | .ok (conn, _) =>
          let (res, conn') ← Db.PgWire.execSimpleOnConn conn "BEGIN"
          match res with
          | .error e =>
              Db.PgWire.releaseConn { conn' with healthy := false }
              return .error (ApiError.internal s!"postgres BEGIN failed: {e}")
          | .ok cReady =>
              return .ok (← pgTxBox.modifyGet fun (nextId, m) => (nextId, (nextId + 1, m.insert nextId cReady))))

private def execNativeDbTxExec (cfg : Db.DbConfig) (txId : UInt64) (q : Db.SqlQuery) :
    IO (Except ApiError Db.DbResult) :=
  withTxTransport cfg
    (fun _ => do
      let (sql, params) := q.compile .sqlite
      return (← Prim.sqliteTxExec txId sql params).mapError ApiError.internal)
    (fun _ => do
      let some conn ← popPgTx txId
        | return .error (ApiError.internal "unknown or closed PostgreSQL transaction")
      let (sql, params) := q.compile .postgres
      let (res, conn') ← Db.PgWire.execOnConn conn sql params
      match res with
      | .ok (dbRes, cNext) =>
          pgTxBox.modify fun (nextId, m) => (nextId, m.insert txId cNext)
          return .ok dbRes
      | .error e =>
          if conn'.healthy then pgTxBox.modify fun (nextId, m) => (nextId, m.insert txId conn')
          else Db.PgWire.releaseConn conn'
          return .error (ApiError.internal e))

private def execNativeDbTxCommit (cfg : Db.DbConfig) (txId : UInt64) : IO (Except ApiError Unit) :=
  withTxTransport cfg
    (fun _ => return (← Prim.sqliteTxCommit txId).mapError ApiError.internal)
    (fun _ => do
      let some conn ← popPgTx txId
        | return .error (ApiError.internal "unknown or closed PostgreSQL transaction")
      finishPgTx conn "COMMIT")

private def execNativeDbTxRollback (cfg : Db.DbConfig) (txId : UInt64) : IO Unit := do
  match ← resolveDbConfig cfg with
  | .ok (.sqlite _)   => Prim.sqliteTxRollback txId
  | .ok (.postgres _) => if let some conn ← popPgTx txId then discard <| finishPgTx conn "ROLLBACK"
  | _                 => pure ()

private def execNativeDbQuery (cfg : Db.DbConfig) (q : Db.SqlQuery) : IO (Except ApiError Db.DbResult) := do
  match ← resolveDbConfig cfg with
  | .error e => return .error e
  | .ok tr =>
      match tr with
      | .postgres _ =>
          let (sqlPg, paramsPg) := q.compile .postgres
          execRawOnTransport tr "" sqlPg paramsPg []
      | _ =>
          let (sqlSq, paramsSq) := q.compile .sqlite
          execRawOnTransport tr sqlSq "" paramsSq (Db.HttpSql.queryExpectedCols q)

@[implicit_reducible]
def mkNativeServerInst (gcpCache? : Option (Prim.StateBox (Array GcpTokenCacheEntry)))
    (cookieSink? : Option (IO.Ref (Array SetCookie)) := none)
    (sseSink? : Option (IO.Ref (Array SseEvent)) := none) : MonadServer IO where
  exec
    | .httpCall req => do
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
    | .dbExec cfg q         => execNativeDbQuery cfg q
    | .dbExecDdl cfg        => execNativeDbDdl cfg
    | .dbTxBegin cfg        => execNativeDbTxBegin cfg
    | .dbTxExec cfg tid q   => execNativeDbTxExec cfg tid q
    | .dbTxCommit cfg tid   => execNativeDbTxCommit cfg tid
    | .dbTxRollback cfg tid => execNativeDbTxRollback cfg tid
    | .setCookie c          => if let some ref := cookieSink? then ref.modify (·.push c) else pure ()
    | .sendSse ev           => if let some ref := sseSink? then ref.modify (·.push ev) else pure ()
    | .readEnv v            => Prim.getEnv v
    | .nowMs                => Prim.nowMs
    | .randomHex n          => Prim.randomHex n
    | .hmacSha256 key msg   => Prim.hmacSha256 key msg
    | .wsBroadcast t p      => Prim.wsBroadcast t p

instance : MonadServer IO := mkNativeServerInst none none

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

/-- Initializes declared database schemas (`CREATE TABLE IF NOT EXISTS ...`) idempotently at server boot. -/
def initDatabases (dbs : Array Db.DbConfig) : IO Bool := do
  dbs.foldlM (init := true) fun ok cfg => do
    match ← execNativeDbDdl cfg with
    | .ok () => return ok
    | .error e =>
        IO.eprintln s!"✗ database `{cfg.name}` initialization failed: {e.message}"
        return false

private def authUsersDdlSqlite : String :=
  "CREATE TABLE IF NOT EXISTS \"_qed_auth_users\" (\"sub\" TEXT PRIMARY KEY, \"created_at\" INTEGER NOT NULL)"

private def authUsersDdlPostgres : String :=
  "CREATE TABLE IF NOT EXISTS \"_qed_auth_users\" (\"sub\" TEXT PRIMARY KEY, \"created_at\" BIGINT NOT NULL)"

private def ensureAuthUsersTable (cfg : Db.DbConfig) : IO (Except ApiError Unit) := do
  match ← resolveDbConfig cfg with
  | .error e => return .error e
  | .ok tr   => execDdlOnTransport tr [authUsersDdlSqlite] authUsersDdlPostgres

/-- Atomically claims a first-time OIDC subject in `_qed_auth_users` (DB-backed when a database is attached,
    falling back to an atomic in-memory set otherwise). Returns `true` iff this is a brand-new user. -/
private def claimAuthUser (primaryDb? : Option Db.DbConfig) (memSeen : Prim.StateBox (Std.HashSet String))
    (sub : String) : IO (Except ApiError Bool) := do
  match primaryDb? with
  | none =>
      let isNew ← Prim.atomicModify memSeen fun s =>
        if s.contains sub then (s, false) else (s.insert sub, true)
      return .ok isNew
  | some cfg =>
      let nowMs := (← Prim.nowMs).toNat
      let params : Array Db.SqlVal := #[.text sub, .int (Int.ofNat nowMs)]
      match ← resolveDbConfig cfg with
      | .error e => return .error e
      | .ok tr =>
          let sqlSq := "INSERT OR IGNORE INTO \"_qed_auth_users\" (\"sub\", \"created_at\") VALUES (?1, ?2)"
          let sqlHttp := sqlSq ++ " RETURNING \"sub\""
          let sqlPg := "INSERT INTO \"_qed_auth_users\" (\"sub\", \"created_at\") VALUES ($1, $2) ON CONFLICT (\"sub\") DO NOTHING RETURNING \"sub\""
          match ← execRawOnTransport tr sqlSq sqlPg params ["sub"] (some sqlHttp) (some "auth user claim decode failed") with
          | .error e => return .error e
          | .ok res  => return .ok (match tr with
              | .sqlite _   => res.affected > 0
              | .postgres _ => !res.rows.isEmpty
              | _           => !res.rows.isEmpty || res.affected > 0)

/-- Releases a claimed OIDC subject if `onCreateAccount` fails so a subsequent retry re-runs account creation. -/
private def releaseAuthUser (primaryDb? : Option Db.DbConfig) (memSeen : Prim.StateBox (Std.HashSet String))
    (sub : String) : IO Unit := do
  match primaryDb? with
  | none =>
      Prim.atomicModify memSeen fun s => (s.erase sub, ())
  | some cfg =>
      if let .ok tr ← resolveDbConfig cfg then
        discard <| execRawOnTransport tr
          "DELETE FROM \"_qed_auth_users\" WHERE \"sub\" = ?1"
          "DELETE FROM \"_qed_auth_users\" WHERE \"sub\" = $1"
          #[.text sub] []

/-! ## Full-Stack Native Server Runner (Verified HTTP/1.1 + Static + RFC 6455 WS + SSR) -/

private def devReloadSnippet : String :=
  "<script type=\"module\" src=\"/qed_dev.mjs\"></script>\n</body>"

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

private def loadHostScript (staticDirFd : Prim.StaticDir) (devMode : Bool) : IO String := do
  if devMode then return "/qed_host.mjs"
  match ← Prim.readStaticFile staticDirFd "qed_manifest.json" 0 with
  | none => return "/qed_host.mjs"
  | some (_, _, bytes) =>
      match String.fromUTF8? bytes with
      | none => return "/qed_host.mjs"
      | some raw =>
          match Json.parse raw with
          | .ok j =>
              match (j.get? "host").bind (·.str?) with
              | some h => if isSafeUrl h then return h else return "/qed_host.mjs"
              | none   => return "/qed_host.mjs"
          | .error _ => return "/qed_host.mjs"

private def stripQuery (target : String) : String :=
  match findByte target 0 63 with
  | some q => String.Pos.Raw.extract target ⟨0⟩ ⟨q⟩
  | none   => target

private def dropPrefixBytes (s : String) (byteLen : Nat) : String :=
  if byteLen >= s.utf8ByteSize then "" else String.Pos.Raw.extract s ⟨byteLen⟩ ⟨s.utf8ByteSize⟩

private def isProtobufMediaType (v : String) : Bool :=
  let head := match findByte v 0 59 with
    | some semi => String.Pos.Raw.extract v ⟨0⟩ ⟨semi⟩
    | none      => v
  eqCI (trimWs head) "application/x-protobuf"

private def checkRpcCsrfReq (req : ParsedReqHead) (allowedOrigins? : Option String) :
    Except (Nat × String) Unit := do
  checkOriginAndFetchSiteParsed req.origin? req.host? req.secFetchSite?
    (req.dupOrigin || req.dupSfs) allowedOrigins? false "RPC"
  if req.dupCt || !req.contentType?.any isProtobufMediaType then
    throw (415, "RPC requires Content-Type: application/x-protobuf")

private def extractQuery (target : String) : String :=
  match findByte target 0 63 with
  | some q =>
      if q + 1 >= target.utf8ByteSize then ""
      else String.Pos.Raw.extract target ⟨q + 1⟩ ⟨target.utf8ByteSize⟩
  | none => ""

private def resolveAuthPrincipal (cfg : ServerConfig) (oidcRt? : Option Qed.Auth.Oidc.OidcRuntime)
    (bearer? : Option String) (cookies : List (String × String)) :
    IO (Option String × List (String × String)) := do
  let nowSec := ((← Prim.nowMs).toNat) / 1000
  -- 1. If an OIDC runtime is configured and a 3-segment Bearer JWT is supplied, verify via JWKS.
  if let (some rt, some tok) := (oidcRt?, bearer?) then
    if (tok.splitOn ".").length == 3 then
      match ← Qed.Auth.Oidc.verifyOidcJwt execHttpCall rt tok with
      | .ok jc   => return (some jc.sub, jc.flatClaims)
      | .error _ => return (none, [])
  -- 2. Check `qed_session` cookie for v2 OIDC-signed claim cookies (using OIDC or server secrets).
  let sessionSecrets := match oidcRt? with
    | some rt => if !rt.cfg.sessionSecrets.isEmpty then rt.cfg.sessionSecrets else cfg.authSecrets
    | none    => cfg.authSecrets
  let sessionCookie? := if cookies.isEmpty then none else (cookies.find? fun (k, _) => k == "qed_session").map Prod.snd
  if let some tok := bearer?.orElse (fun _ => sessionCookie?) then
    if tok.startsWith "v2." then
      if let some p ← Qed.Auth.Oidc.verifySessionCookieV2 sessionSecrets tok nowSec then
        return (some p.userId, p.claims)
      else
        return (none, [])
    if !sessionSecrets.isEmpty then
      let uid? ← verifyUserTokenWithNow sessionSecrets tok nowSec cfg.requireExpiring
      return (uid?, [])
  return (none, [])

private def buildRequestCtxReq (cfg : ServerConfig) (req : ParsedReqHead) (clientIp : String)
    (body : ByteArray := ByteArray.empty)
    (oidcRt? : Option Qed.Auth.Oidc.OidcRuntime := none) : IO RequestCtx := do
  let hdrList := req.headers.toList
  let cookies :=
    if !req.hasCookie then []
    else hdrList.foldl (fun acc (k, v) =>
      if eqCI k "cookie" then acc ++ parseCookiePairs v else acc) []
  let bearer? := req.auth?.bind extractBearer
  let (userId?, claims) ← resolveAuthPrincipal cfg oidcRt? bearer? cookies
  let queryStr := extractQuery req.target
  let bodyStr := if body.isEmpty then "" else (String.fromUTF8? body).getD ""
  return {
    headers := hdrList, cookies, bearerToken := bearer?, userId := userId?, claims,
    clientIp, query := queryStr, body := bodyStr
  }

private structure WireVariants where
  headKA    : ByteArray
  headClose : ByteArray
  fullKA    : ByteArray
  fullClose : ByteArray

private def WireVariants.build (mime : String) (body : ByteArray) (etag cacheCtrl : String)
    (hdrs : List (String × String)) : WireVariants :=
  let hKA := formatHttpResponseHead 200 mime body.size true false (some etag) (some cacheCtrl) hdrs
  let hCl := formatHttpResponseHead 200 mime body.size false false (some etag) (some cacheCtrl) hdrs
  { headKA := hKA, headClose := hCl, fullKA := hKA ++ body, fullClose := hCl ++ body }

private def WireVariants.pick (w : WireVariants) (isHead keepAlive : Bool) : ByteArray :=
  if isHead then (if keepAlive then w.headKA else w.headClose)
  else (if keepAlive then w.fullKA else w.fullClose)

private structure CachedStaticAsset where
  etag  : String
  plain : WireVariants
  gzip? : Option WireVariants := none

private def CachedStaticAsset.serve (c : CachedStaticAsset) (req : ParsedReqHead)
    (isHead keepAlive : Bool) : ByteArray :=
  if req.hasIfNoneMatch && etagMatchesIfNoneMatch req.headers c.etag then
    formatNotModifiedResponse c.etag keepAlive
  else
    (if req.acceptsGzip then c.gzip?.getD c.plain else c.plain).pick isHead keepAlive

private def cookieHeaders (cookies : List SetCookie) : List (String × String) :=
  cookies.map fun c => ("Set-Cookie", c.render)

private def isSsrRedirectStatus (status : Nat) : Bool :=
  status == 301 || status == 302 || status == 303 || status == 307 || status == 308

private def maybeGzipResponse (status : Nat) (contentType : String) (body : ByteArray)
    (isHead keepAlive noStore acceptsGzip compressible : Bool)
    (etag? : Option String := none) (cacheCtrl? : Option String := none)
    (extraHeaders : List (String × String) := []) (contentLen : Nat := body.size) : IO ByteArray := do
  if !isHead && acceptsGzip && compressible && body.size >= 256 then
    let gz ← Prim.gzipCompress body
    if !gz.isEmpty && gz.size < body.size then
      let hdrs :=
        if extraHeaders.any (fun (k, _) => eqCI k "vary") then
          ("Content-Encoding", "gzip") :: extraHeaders
        else
          ("Content-Encoding", "gzip") :: ("Vary", "Accept-Encoding") :: extraHeaders
      return formatHttpResponseHead status contentType gz.size keepAlive noStore etag? cacheCtrl? hdrs ++ gz
  let head := formatHttpResponseHead status contentType contentLen keepAlive noStore etag? cacheCtrl? extraHeaders
  return if isHead then head else head ++ body

private def serveStaticAsset (staticDirFd : Prim.StaticDir)
    (assetCache? : Option (Prim.StateBox (Std.HashMap String CachedStaticAsset)))
    (req : ParsedReqHead) (st : StaticTarget) (devMode : Bool) : IO ByteArray := do
  let cacheable := assetCache?.isSome && !devMode && !st.noStore && isContentHashedAsset st.relPath
  if cacheable then
    if let some assetCache := assetCache? then
      if let some hit ← Prim.atomicRead assetCache (fun m => m[st.relPath]?) then
        return hit.serve req st.isHead req.keepAlive
  let compressible := isCompressibleMime st.mime
  let headFlag : UInt8 := if st.isHead && !cacheable then 1 else 0
  if let some (fsize, mtimeMs, fbytes) ← Prim.readStaticFile staticDirFd st.relPath headFlag then
    if !st.noStore then
      let etag := s!"W/\"{fsize}-{mtimeMs}\""
      let cacheCtrl :=
        if isContentHashedAsset st.relPath then "public, max-age=31536000, immutable"
        else "public, max-age=0, must-revalidate"
      let varyHdrs : List (String × String) := if compressible then [("Vary", "Accept-Encoding")] else []
      if cacheable && fsize <= 2 * 1024 * 1024 then
        let gzip? ←
          if compressible && fsize >= 256 then do
            let gz ← Prim.gzipCompress fbytes
            if !gz.isEmpty && gz.size < fsize then
              pure (some (WireVariants.build st.mime gz etag cacheCtrl [("Content-Encoding", "gzip"), ("Vary", "Accept-Encoding")]))
            else pure none
          else pure none
        let entry : CachedStaticAsset := {
          etag, plain := WireVariants.build st.mime fbytes etag cacheCtrl varyHdrs, gzip?
        }
        if let some assetCache := assetCache? then
          Prim.atomicModify assetCache fun m =>
            ((if m.size < 64 then m.insert st.relPath entry else m), ())
        return entry.serve req st.isHead req.keepAlive
      if req.hasIfNoneMatch && etagMatchesIfNoneMatch req.headers etag then
        return formatNotModifiedResponse etag req.keepAlive
      return ← maybeGzipResponse 200 st.mime fbytes st.isHead req.keepAlive false req.acceptsGzip compressible
        (some etag) (some cacheCtrl) varyHdrs fsize
    else
      return ← maybeGzipResponse 200 st.mime fbytes st.isHead req.keepAlive true req.acceptsGzip compressible
        none none [] fsize
  else if st.isBuildId then
    let fallback := if st.relPath == "__dev_status" then "{\"id\":\"0\",\"status\":\"ok\"}".toUTF8 else "0".toUTF8
    return formatHttpResponse 200 st.mime fallback st.isHead req.keepAlive true
  else
    return formatHttpResponse 404 "text/plain; charset=utf-8" "not found".toUTF8 st.isHead req.keepAlive false

private def formatCustomHttpResponse (resp : HttpResponse) (extraCookies : Array SetCookie)
    (csp? : Option String) (req : ParsedReqHead) (isHead : Bool) : IO ByteArray := do
  let allCookies := extraCookies.toList ++ resp.cookies
  let isHtml := startsWithCI resp.contentType "text/html"
  let isSse := startsWithCI resp.contentType "text/event-stream"
  let cspHdrs :=
    if isHtml && !resp.headers.any (fun (k, _) => eqCI k "content-security-policy") then
      match csp? with | some p => [("Content-Security-Policy", p)] | none => []
    else []
  let baseHdrs := resp.headers ++ cspHdrs ++ cookieHeaders allCookies
  maybeGzipResponse resp.status resp.contentType resp.body isHead req.keepAlive false
    req.acceptsGzip (!isSse && isCompressibleMime resp.contentType) (extraHeaders := baseHdrs)

private structure HttpLoopCtx where
  cfg         : ServerConfig
  staticDirFd : Prim.StaticDir
  healthKA    : ByteArray
  healthClose : ByteArray
  htmlCspHdrs : List (String × String)

private def serveHttpLoop (staticDir : String) (port : UInt16) (devMode : Bool) (numWorkers : UInt32)
    (setup : HttpLoopCtx → IO (
      (ParsedReqHead → String → String → Nat → IO (Prim.HttpHeadAction ParsedReqHead RequestCtx)) ×
      (ParsedReqHead → ByteArray → String → IO ByteArray) ×
      (RequestCtx → ByteArray → WsFragState → Array (Nat × String × ByteArray) → IO (Prim.WsStepOut WsFragState)) ×
      (RequestCtx → String → ByteArray → IO Unit))) : IO UInt32 := do
  let cfg ← loadServerConfig devMode
  let staticDirFd ← Prim.openStaticDir staticDir
  let healthKA := formatHttpResponse 200 "application/json" "{\"ok\":true}".toUTF8 false true false
  let healthClose := formatHttpResponse 200 "application/json" "{\"ok\":true}".toUTF8 false false false
  let htmlCspHdrs : List (String × String) :=
    match cfg.csp? with | some p => [("Content-Security-Policy", p)] | none => []
  let (onParsedHead, onBody, onWsBytes, onWsLeave) ←
    setup { cfg, staticDirFd, healthKA, healthClose, htmlCspHdrs }
  let onHead (headBytes : ByteArray) (clientIp : String) (inline : Nat) : IO (Prim.HttpHeadAction ParsedReqHead RequestCtx) := do
    match parseRequestHead headBytes with
    | .error (code, msg) => return .doneClose (formatErrorResponse code msg)
    | .ok req =>
        let pathOnly := stripQuery req.target
        if req.method == "GET" && pathOnly == "/_qed/health" && req.contentLen == 0 then
          return if req.keepAlive then .doneKeepAlive healthKA else .doneClose healthClose
        onParsedHead req clientIp pathOnly inline
  Prim.serveNative cfg.bindHost port numWorkers ({} : WsFragState) onHead onBody onWsBytes onWsLeave

private def finishHeadWire (req : ParsedReqHead) (wire : ByteArray) : Prim.HttpHeadAction ParsedReqHead RequestCtx :=
  if req.keepAlive then .doneKeepAlive wire else .doneClose wire

private def closedWsBytes (_ : RequestCtx) (rx : ByteArray) (frag : WsFragState)
    (_ : Array (Nat × String × ByteArray)) : IO (Prim.WsStepOut WsFragState) :=
  pure { consumed := rx.size, outWire := ByteArray.empty, closeFlag := 1, fragState := frag, subOps := #[] }

private structure FullstackConfig where
  title            : String
  serverShortName  : String
  requiredSecrets  : Array String
  dispatchFn       : RequestCtx → String → ByteArray → IO (Except ApiError ByteArray × Array SetCookie)
  port             : UInt16
  staticDir        : String
  devMode          : Bool := false
  numWorkers       : UInt32 := 0
  wsDispatchFn?    : Option (RequestCtx → UInt8 → String → ByteArray → ByteArray → IO (Except ApiError ByteArray)) := none
  blockingMethods? : Option (Array String) := none
  httpDispatchFn?  : Option (RequestCtx → String → String → IO (Except ApiError (Option HttpResponse) × Array SetCookie)) := none
  jobs             : Array IoJob := #[]
  authSpec?        : Option Qed.Auth.OidcAuthSpec := none
  authHookFn?      : Option (RequestCtx → UInt8 → IO (Except ApiError Unit × Array SetCookie)) := none
  authHookFlags    : Bool × Bool := (false, false)
  primaryDb?       : Option Db.DbConfig := none

private def withCookieSink {α : Type} (gcpCache : Prim.StateBox (Array GcpTokenCacheEntry))
    (f : MonadServer IO → IO α) : IO (α × Array SetCookie) := do
  let cookieRef ← IO.mkRef (#[] : Array SetCookie)
  let res ← f (mkNativeServerInst (some gcpCache) (some cookieRef))
  return (res, ← cookieRef.get)

private def runFullstackCore {Model Msg : Type} (app : Qed.App Model Msg) (fc : FullstackConfig) : IO UInt32 := do
  if !(← verifyRequiredSecrets fc.requiredSecrets) then return 1
  let (hasOnCreateAccount, hasOnSignIn) := fc.authHookFlags
  if hasOnCreateAccount then
    if let some dbCfg := fc.primaryDb? then
      if let .error e ← ensureAuthUsersTable dbCfg then
        IO.eprintln s!"✗ failed to initialize `_qed_auth_users` table: {e.message}"
        return 1
  serveHttpLoop fc.staticDir fc.port fc.devMode fc.numWorkers fun loop => do
    let cfg := loop.cfg
    let oidcRt? ← match fc.authSpec? with
      | some spec => Qed.Auth.Oidc.initOidcRuntime spec cfg.authSecrets fc.devMode
      | none      => pure none
    let memSeenAuthUsers ← Prim.mkStateBox (∅ : Std.HashSet String)
    let hostScript ← loadHostScript loop.staticDirFd fc.devMode
    let rpcPrefix := "/_qed/rpc/" ++ fc.serverShortName ++ "/"
    let rpcPrefixBytes := rpcPrefix.utf8ByteSize
    let wsPath := "/_qed/ws/" ++ fc.serverShortName
    let assetCache ← Prim.mkStateBox (∅ : Std.HashMap String CachedStaticAsset)
    let docShell := mkPrebuiltDocShell fc.title hostScript (renderStyleSheet app.styles) app.stylesheets

    let dispatchAppReqWith (req : ParsedReqHead) (body : ByteArray) (clientIp pathOnly : String)
        (staticTarget? : Option StaticTarget) : IO ByteArray := do
      let isHead := req.method == "HEAD"
      if req.method == "GET" && pathOnly == "/_qed/health" then
        return if req.keepAlive then loop.healthKA else loop.healthClose
      if let some st := staticTarget? then
        if isContentHashedAsset st.relPath then
          return ← serveStaticAsset loop.staticDirFd (some assetCache) req st fc.devMode
      let ctx ← buildRequestCtxReq cfg req clientIp body oidcRt?
      if pathOnly.startsWith "/_qed/auth/" then
        if let some rt := oidcRt? then
          if req.method == "POST" && pathOnly == rt.cfg.logoutPath then
            match checkOriginAndFetchSiteParsed req.origin? req.host? req.secFetchSite?
                (req.dupOrigin || req.dupSfs) cfg.rpcAllowedOrigins? false "auth logout" with
            | .error (code, msg) =>
                return formatHttpResponse code "text/plain; charset=utf-8" msg.toUTF8 isHead req.keepAlive false
            | .ok () => pure ()
          let onAuthCallback? : Option (String → List (String × String) → IO (Except (Nat × String) (Array SetCookie))) :=
            fc.authHookFn?.map fun hookFn => fun sub filteredClaims => do
              let hookCtx : RequestCtx := { ctx with userId := some sub, claims := filteredClaims }
              let mut outCookies : Array SetCookie := #[]
              if hasOnCreateAccount then
                match ← claimAuthUser fc.primaryDb? memSeenAuthUsers sub with
                | .error e => return .error (e.httpStatus.toNat, e.message)
                | .ok true =>
                    let (cRes, cCookies) ← hookFn hookCtx 0
                    match cRes with
                    | .error e =>
                        releaseAuthUser fc.primaryDb? memSeenAuthUsers sub
                        return .error (e.httpStatus.toNat, e.message)
                    | .ok () => outCookies := outCookies ++ cCookies
                | .ok false => pure ()
              if hasOnSignIn then
                let (sRes, sCookies) ← hookFn hookCtx 1
                match sRes with
                | .error e => return .error (e.httpStatus.toNat, e.message)
                | .ok () => outCookies := outCookies ++ sCookies
              return .ok outCookies
          if let some authResp ← Qed.Auth.Oidc.handleAuthRoute execHttpCall rt req
              pathOnly ctx.query ctx.cookies ctx.userId ctx.claims isHead onAuthCallback? then
            return authResp
      if req.method == "POST" && pathOnly.startsWith rpcPrefix then
        match checkRpcCsrfReq req cfg.rpcAllowedOrigins? with
        | .error (code, msg) =>
            return formatHttpResponse code "text/plain; charset=utf-8" msg.toUTF8 isHead req.keepAlive false
        | .ok () =>
            let (res, cookies) ← fc.dispatchFn ctx (dropPrefixBytes pathOnly rpcPrefixBytes) body
            match res with
            | .ok respBytes =>
                if cookies.isEmpty then return formatOkProtoResponse respBytes isHead req.keepAlive
                else return formatHttpResponse 200 "application/x-protobuf" respBytes isHead req.keepAlive false (extraHeaders := cookieHeaders cookies.toList)
            | .error apiErr =>
                return formatHttpResponse apiErr.httpStatus.toNat "text/plain; charset=utf-8" apiErr.message.toUTF8 isHead req.keepAlive false (extraHeaders := cookieHeaders cookies.toList)
      if !pathOnly.startsWith "/_qed/" then
        if let some httpDispatchFn := fc.httpDispatchFn? then
          let (hRes, cookies) ← httpDispatchFn ctx (if isHead then "GET" else req.method) pathOnly
          match hRes with
          | .error apiErr =>
              return formatHttpResponse apiErr.httpStatus.toNat "text/plain; charset=utf-8" apiErr.message.toUTF8 isHead req.keepAlive false (extraHeaders := cookieHeaders cookies.toList)
          | .ok (some resp) =>
              return ← formatCustomHttpResponse resp cookies cfg.csp? req isHead
          | .ok none => pure ()
      if let some st := staticTarget? then
        return ← serveStaticAsset loop.staticDirFd (some assetCache) req st fc.devMode
      if (req.method == "GET" || isHead) && !pathOnly.startsWith "/_qed/" then
        let ssrDispatchBytes (reqMethod url : String) (reqBody : ByteArray) : IO (Except String ByteArray) := do
          let uPath := stripQuery url
          if reqMethod == "POST" && uPath.startsWith rpcPrefix then
            let (r, _) ← fc.dispatchFn ctx (dropPrefixBytes uPath rpcPrefixBytes) reqBody
            return r.mapError (·.message)
          else
            return .error s!"SSR unknown binary RPC endpoint: {url}"
        let (ssrStatus, headMeta, rawHtml) ← app.ssrRenderNativeWithStatus docShell fc.title hostScript req.target ssrDispatchBytes
          (sessionUser := ctx.userId)
        let finalHtml := if fc.devMode then injectDevReload rawHtml else rawHtml
        let redirectHdrs : List (String × String) :=
          if isSsrRedirectStatus ssrStatus then
            match headMeta.redirect.orElse (fun _ => headMeta.canonical) with
            | some loc => if isSafeUrl loc then [("Location", sanitizeHeader loc)] else []
            | none     => []
          else []
        return ← maybeGzipResponse ssrStatus "text/html; charset=utf-8" finalHtml isHead req.keepAlive false
          req.acceptsGzip true (extraHeaders := redirectHdrs ++ loop.htmlCspHdrs ++ [("Vary", "Accept-Encoding")])
      else
        return formatHttpResponse 404 "text/plain; charset=utf-8" "not found".toUTF8 isHead req.keepAlive false

    let dispatchAppReq (req : ParsedReqHead) (body : ByteArray) (clientIp : String) : IO ByteArray :=
      let staticTarget? :=
        if req.method == "GET" || req.method == "HEAD" then classifyStaticPath req.method req.target fc.devMode else none
      dispatchAppReqWith req body clientIp (stripQuery req.target) staticTarget?

    let hasBlockingMethods : Bool := fc.blockingMethods?.map (!·.isEmpty) |>.getD true
    let methodMayBlock (rpcMethod : String) : Bool := fc.blockingMethods?.map (·.contains rpcMethod) |>.getD true

    let onParsedHead (req : ParsedReqHead) (clientIp pathOnly : String) (inline : Nat) : IO (Prim.HttpHeadAction ParsedReqHead RequestCtx) := do
      if fc.wsDispatchFn?.isSome && req.method == "GET" && pathOnly == wsPath &&
         req.upgrade?.any (eqCI · "websocket") then
        if !req.isHttp11 || (req.conn?.map (containsCI · "upgrade") != some true) || req.wsVer? != some "13" then
          return .doneClose (formatErrorResponse 400 "invalid WebSocket upgrade headers")
        let some acceptB64 := req.wsKey?.bind wsComputeAccept
          | return .doneClose (formatErrorResponse 400 "invalid Sec-WebSocket-Key")
        match checkOriginAndFetchSiteParsed req.origin? req.host? req.secFetchSite?
            (req.dupOrigin || req.dupSfs) cfg.wsAllowedOrigins? true "WebSocket upgrade" with
        | .error (code, msg) => return .doneClose (formatErrorResponse code msg)
        | .ok () =>
            let baseCtx ← buildRequestCtxReq cfg req clientIp ByteArray.empty oidcRt?
            return .wsUpgrade (formatWsUpgradeResponse acceptB64) { baseCtx with connId := "ws-" ++ (← Prim.randomHex 12) }
      let isGetOrHead := req.method == "GET" || req.method == "HEAD"
      let staticTarget? := if isGetOrHead then classifyStaticPath req.method req.target fc.devMode else none
      if inline != 0 then
        if let some st := staticTarget? then
          if !fc.devMode && !st.noStore && isContentHashedAsset st.relPath then
            if let some hit ← Prim.atomicRead assetCache (fun m => m[st.relPath]?) then
              return finishHeadWire req (hit.serve req st.isHead req.keepAlive)
          return .deferHead
        if oidcRt?.isSome && (pathOnly.startsWith "/_qed/auth/" || req.auth?.isSome) then return .deferHead
        if fc.httpDispatchFn?.isSome && !pathOnly.startsWith "/_qed/" then return .deferHead
        if hasBlockingMethods then
          if req.method == "POST" && pathOnly.startsWith rpcPrefix then
            if methodMayBlock (dropPrefixBytes pathOnly rpcPrefixBytes) then return .deferHead
          else if isGetOrHead && !pathOnly.startsWith "/_qed/" then return .deferHead
      if req.contentLen == 0 then
        return finishHeadWire req (← dispatchAppReqWith req ByteArray.empty clientIp pathOnly staticTarget?)
      else
        return if req.keepAlive then .needBodyKeep req.contentLen req else .needBodyClose req.contentLen req

    let onWsBytes := match fc.wsDispatchFn? with
      | some wsDispatchFn => fun ctx rx frag subs => stepWsRxLoop wsDispatchFn ctx rx 0 frag subs ByteArray.empty #[]
      | none              => closedWsBytes
    let onWsLeave (ctx : RequestCtx) (ch : String) (params : ByteArray) : IO Unit := do
      if let some wsDispatchFn := fc.wsDispatchFn? then discard <| wsDispatchFn ctx 3 ch params ByteArray.empty

    let _jobTasks ← if fc.jobs.isEmpty then pure #[] else spawnServerJobs fc.jobs
    return (onParsedHead, dispatchAppReq, onWsBytes, onWsLeave)

def runStatefulFullstack {σ Model Msg : Type}
    (app : Qed.App Model Msg) (title serverShortName : String)
    (initState : σ) (requiredSecrets : Array String)
    (dispatchM : {m : Type → Type} → [Monad m] → [MonadServer m] → [MonadAtomic σ m] →
        RequestCtx → String → ByteArray → m (Except ApiError ByteArray))
    (port : UInt16) (staticDir : String) (devMode : Bool := false) (numWorkers : UInt32 := 0)
    (wsDispatchM? : Option ({m : Type → Type} → [Monad m] → [MonadServer m] → [MonadAtomic σ m] →
        RequestCtx → UInt8 → String → ByteArray → ByteArray → m (Except ApiError ByteArray)) := none)
    (blockingMethods? : Option (Array String) := none)
    (httpDispatchM? : Option ({m : Type → Type} → [Monad m] → [MonadServer m] → [MonadAtomic σ m] →
        RequestCtx → String → String → m (Except ApiError (Option HttpResponse))) := none)
    (jobs : Array (ServerJob σ) := #[])
    (authSpec? : Option Qed.Auth.OidcAuthSpec := none)
    (authHookM? : Option ({m : Type → Type} → [Monad m] → [MonadServer m] → [MonadAtomic σ m] →
        RequestCtx → UInt8 → m (Except ApiError Unit)) := none)
    (authHookFlags : Bool × Bool := (false, false))
    (primaryDb? : Option Db.DbConfig := none) : IO UInt32 := do
  let box ← Prim.mkStateBox initState
  let gcpCache ← Prim.mkStateBox (#[] : Array GcpTokenCacheEntry)
  let wsSrvInst : MonadServer IO := mkNativeServerInst (some gcpCache) none
  let atomicInst : MonadAtomic σ IO := withStateBox box
  runFullstackCore app {
    title, serverShortName, requiredSecrets, port, staticDir, devMode, numWorkers,
    blockingMethods?, authSpec?, authHookFlags, primaryDb?,
    dispatchFn := fun ctx mName reqBytes =>
      withCookieSink gcpCache fun srv => @dispatchM IO _ srv atomicInst ctx mName reqBytes,
    wsDispatchFn? := wsDispatchM?.map fun wsM ctx kind ch params payload =>
      @wsM IO _ wsSrvInst atomicInst ctx kind ch params payload,
    httpDispatchFn? := httpDispatchM?.map fun httpM ctx method path => do
      let cookieRef ← IO.mkRef (#[] : Array SetCookie)
      let sseRef ← IO.mkRef (#[] : Array SseEvent)
      let res ← @httpM IO _ (mkNativeServerInst (some gcpCache) (some cookieRef) (some sseRef)) atomicInst ctx method path
      let sseEvs ← sseRef.get
      let res' := match res with
        | .ok (some resp) =>
            if !sseEvs.isEmpty && startsWithCI resp.contentType "text/event-stream" then
              .ok (some { resp with body := SseEvent.formatStream sseEvs.toList })
            else .ok (some resp)
        | other => other
      return (res', ← cookieRef.get),
    jobs := jobs.map (·.toIoJob wsSrvInst atomicInst),
    authHookFn? := authHookM?.map fun hookM ctx kind =>
      withCookieSink gcpCache fun srv => @hookM IO _ srv atomicInst ctx kind
  }

def runStatelessFullstack {Model Msg : Type}
    (app : Qed.App Model Msg) (title serverShortName : String)
    (requiredSecrets : Array String)
    (dispatchM : {m : Type → Type} → [Monad m] → [MonadServer m] →
        RequestCtx → String → ByteArray → m (Except ApiError ByteArray))
    (port : UInt16) (staticDir : String) (devMode : Bool := false) (numWorkers : UInt32 := 0)
    (wsDispatchM? : Option ({m : Type → Type} → [Monad m] → [MonadServer m] →
        RequestCtx → UInt8 → String → ByteArray → ByteArray → m (Except ApiError ByteArray)) := none)
    (blockingMethods? : Option (Array String) := none)
    (httpDispatchM? : Option ({m : Type → Type} → [Monad m] → [MonadServer m] →
        RequestCtx → String → String → m (Except ApiError (Option HttpResponse))) := none)
    (jobs : Array StatelessJob := #[])
    (authSpec? : Option Qed.Auth.OidcAuthSpec := none)
    (authHookM? : Option ({m : Type → Type} → [Monad m] → [MonadServer m] →
        RequestCtx → UInt8 → m (Except ApiError Unit)) := none)
    (authHookFlags : Bool × Bool := (false, false))
    (primaryDb? : Option Db.DbConfig := none) : IO UInt32 :=
  runStatefulFullstack (σ := Unit) app title serverShortName () requiredSecrets
    (fun {m} [Monad m] [MonadServer m] [MonadAtomic Unit m] => @dispatchM m _ _)
    port staticDir devMode numWorkers
    (wsDispatchM?.map fun f => fun {m} [Monad m] [MonadServer m] [MonadAtomic Unit m] => @f m _ _)
    blockingMethods?
    (httpDispatchM?.map fun f => fun {m} [Monad m] [MonadServer m] [MonadAtomic Unit m] => @f m _ _)
    (jobs.map fun j => {
      name := j.name, intervalMs := j.intervalMs, intervalPos := j.intervalPos,
      runM := fun {m} [Monad m] [MonadServer m] [MonadAtomic Unit m] => @j.runM m _ _
    })
    authSpec?
    (authHookM?.map fun f => fun {m} [Monad m] [MonadServer m] [MonadAtomic Unit m] => @f m _ _)
    authHookFlags primaryDb?

/-- Serves a standalone `Qed.App` (`component` or `Qed.run`) with native in-memory SSR and static asset serving. -/
def runStandaloneApp {Model Msg : Type} (app : Qed.App Model Msg) (title : String)
    (args : List String) : IO UInt32 := do
  let staticDir := args.getD 0 "dist"
  let port : UInt16 := ((args.getD 1 "8000").toNat?.getD 8000).toUInt16
  let devMode := args.contains "--dev"
  let numWorkers : UInt32 := (((← Prim.getEnv "QED_WORKERS").bind String.toNat?).getD 0).toUInt32
  runFullstackCore app {
    title, serverShortName := "_app", requiredSecrets := #[], port, staticDir, devMode, numWorkers,
    dispatchFn := fun _ _ _ => pure (.error (ApiError.notFound "no RPC server configured"), #[]),
    blockingMethods? := some #[]
  }

/-- Serves a static/SPA directory using Qed's native Rust/Lean HTTP/1.1 server (no Node.js or Python). -/
def runStaticDir (staticDir : String) (port : UInt16) (devMode : Bool := false) : IO UInt32 :=
  serveHttpLoop staticDir port devMode 1 fun loop => do
    let dispatchReq (req : ParsedReqHead) (_body : ByteArray) (_clientIp : String) : IO ByteArray := do
      let isHead := req.method == "HEAD"
      if req.method != "GET" && !isHead then
        return formatHttpResponse 405 "text/plain; charset=utf-8" "method not allowed".toUTF8 isHead req.keepAlive false
      if let some st := classifyStaticPath req.method req.target devMode then
        return ← serveStaticAsset loop.staticDirFd none req st devMode
      match ← Prim.readStaticFile loop.staticDirFd "index.html" (if isHead then 1 else 0) with
      | some (fsize, _, bytes) =>
          return ← maybeGzipResponse 200 "text/html; charset=utf-8" bytes isHead req.keepAlive true
            req.acceptsGzip true (extraHeaders := loop.htmlCspHdrs ++ [("Vary", "Accept-Encoding")]) (contentLen := fsize)
      | none =>
          return formatHttpResponse 404 "text/plain; charset=utf-8" "not found".toUTF8 isHead req.keepAlive false
    let onParsedHead (req : ParsedReqHead) (_ _ : String) (_ : Nat) := do
      return finishHeadWire req (← dispatchReq req ByteArray.empty "")
    return (onParsedHead, dispatchReq, closedWsBytes, fun _ _ _ => pure ())

end Qed.Server.Native
