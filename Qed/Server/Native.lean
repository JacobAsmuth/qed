import Qed.Ssr
import Qed.Server.Core
import Qed.Server.Net
import Qed.Server.Http
import Qed.Server.Prim
import Qed.Server.Db.HttpSql
import Qed.Server.Db.PgWire
import Qed.Auth.Oidc

namespace Qed.Server.Native
open Qed.Server.Net
open Qed.Server.Http
open Qed.Auth.Oidc (nowSec loadNonEmptyEnv)

/-! ## Unified CSRF & CSWSH Origin / Fetch-Metadata Verification -/

def isOriginMatchingHost (origin host : String) : Bool :=
  let h := trimWs host
  if h.isEmpty then false
  else
    let o := trimWs origin
    let authStart : Nat := if startsWithCI o "http://" then 7 else if startsWithCI o "https://" then 8 else 0
    if authStart == 0 then false
    else
      let rec scanEnd (j : Nat) (hj : j ≤ o.utf8ByteSize) : Nat :=
        if _ : authStart < j then if o.getUTF8Byte ⟨j - 1⟩ (show j - 1 < o.utf8ByteSize by omega) == 47 then scanEnd (j - 1) (by omega) else j else authStart
      termination_by j
      let authEnd := scanEnd o.utf8ByteSize (Nat.le_refl _)
      authStart < authEnd && !hasByteInRange o authStart authEnd 47 && eqCIRange o authStart authEnd h 0 h.utf8ByteSize

def isOriginExplicitlyAllowed (allowed origin : String) : Bool :=
  let a := trimWs allowed
  if a.isEmpty then false else if a == "*" then true
  else let o := (trimWs origin).toLower; !o.isEmpty && (a.splitOn ",").any fun entry => (trimWs entry).toLower == o

private def checkOriginAndFetchSite (req : ParsedReqHead) (allowedOrigins? : Option String) (allowEmptyOrigin : Bool) (label : String) :
    Except (Nat × String) Unit := do
  if req.dupOrigin || req.dupSfs then throw (400, "duplicate origin or fetch-metadata header")
  if req.origin?.isSome || req.secFetchSite?.isSome then
    let allowed? := allowedOrigins?.bind fun s => let t := trimWs s; if t.isEmpty then none else some t
    let originExplicitOk := match req.origin?, allowed? with | some orig, some allow => isOriginExplicitlyAllowed allow orig | _, _ => false
    if let some orig := req.origin? then
      let origTrim := trimWs orig
      if !(allowEmptyOrigin && origTrim.isEmpty) && !(match allowed? with | some allow => isOriginExplicitlyAllowed allow origTrim | none => req.host?.any (isOriginMatchingHost origTrim ·)) then
        throw (403, s!"cross-origin {label} rejected")
    if let some sfs := req.secFetchSite? then
      let s := trimWs sfs; if !eqCI s "same-origin" && !eqCI s "none" && !originExplicitOk then throw (403, s!"cross-site {label} rejected")

/-! ## Total Outbound HTTP/1.1 Client -/

private def maxRespBodyBytes : Nat := 256 * 1024 * 1024
private def readLoop {α : Type} (handle : UInt64) (chunkSz : UInt32) (check : ByteArray → Nat → Except String (Option α))
    (onEof : ByteArray → Except String α) (buf : ByteArray) (fuel : Nat) (nextScan : ByteArray → Nat → Nat := fun _ s => s) (scanFrom : Nat := 0) : IO (Except String α) :=
  match fuel with
  | 0 => return .error "HTTP read limit exceeded"
  | fuel + 1 => do
      match check buf scanFrom with
      | .error e => return .error e | .ok (some v) => return .ok v
      | .ok none => match ← Prim.outboundReadSome handle chunkSz with
          | .error e => return .error e
          | .ok chunk => if chunk.isEmpty then return onEof buf else readLoop handle chunkSz check onEof (buf ++ chunk) fuel nextScan (nextScan buf scanFrom)
private def readUntilCrlfCrlf (handle : UInt64) : IO (Except String (ByteArray × Nat)) :=
  readLoop handle 8192 (fun b sf => if let some pos := findCrlfCrlf b sf then .ok (some (b, pos)) else if b.size > maxReqHdrBytes then .error "HTTP response headers too large" else .ok none)
    (fun _ => .error "unexpected EOF in HTTP response headers") ByteArray.empty 4096 (fun b _ => b.size - 3)
private def readAtLeast (handle : UInt64) (buf : ByteArray) (target : Nat) : IO (Except String ByteArray) :=
  readLoop handle 16384 (fun b _ => if b.size >= target then .ok (some b) else .ok none) (fun _ => .error "truncated HTTP response body") buf 65536
private def readUntilEof (handle : UInt64) (buf : ByteArray) : IO (Except String ByteArray) :=
  readLoop handle 16384 (fun b _ => if b.size > maxRespBodyBytes then .error "HTTP response body too large" else .ok none) .ok buf 65536
private def readCrlfLineAt (handle : UInt64) (buf : ByteArray) (off : Nat) : IO (Except String (String × ByteArray × Nat)) :=
  readLoop handle 4096 (fun b _ => if let some pos := findCrlf b off then
      (String.fromUTF8? (b.extract off pos)).elim (.error "invalid UTF-8 in chunked framing") fun line => .ok (some (line, b, pos + 2))
      else if b.size - off > 4096 then .error "chunked header line too long" else .ok none)
    (fun _ => .error "unexpected EOF in chunked framing") buf 256
private def drainChunkTrailers (handle : UInt64) (rx : ByteArray) (off : Nat) : Nat → ExceptT String IO Bool
  | 0 => throw "too many chunked trailers"
  | fuel + 1 => do let (line, rx1, off1) ← liftE (readCrlfLineAt handle rx off); if line.isEmpty then return off1 >= rx1.size else drainChunkTrailers handle rx1 off1 fuel
private def readChunkedBody (handle : UInt64) (rx : ByteArray) (off : Nat) (out : ByteArray) : Nat → ExceptT String IO (ByteArray × Bool)
  | 0 => throw "chunked response exceeded max chunks"
  | fuel + 1 => do
      let (rx0, off0) := if off >= rx.size then (ByteArray.empty, 0) else if off >= 65536 then (rx.extract off rx.size, 0) else (rx, off)
      let (szLine, rx1, off1) ← liftE (readCrlfLineAt handle rx0 off0)
      let some sz := parseHexSize szLine maxRespBodyBytes | throw "invalid chunk size"
      if sz == 0 then return (out, ← drainChunkTrailers handle rx1 off1 256)
      else if out.size + sz > maxRespBodyBytes then throw "chunked HTTP response body too large"
      else
        let full ← liftE (readAtLeast handle rx1 (off1 + sz + 2))
        if h : off1 + sz + 1 < full.size then
          if full[off1 + sz]'(by omega) != 13 || full[off1 + sz + 1] != 10 then throw "missing CRLF after chunk data"
          readChunkedBody handle full (off1 + sz + 2) (full.copySlice off1 out out.size sz false) fuel
        else throw "truncated chunk data"
private def execHttpAttempt (method : String) (u : ParsedUrl) (wireReq : ByteArray) (ssrfGuard : Bool) :
    Nat → IO (Except String (Nat × ByteArray × Array (String × String)))
  | 0 => return .error "HTTP call failed"
  | attemptsLeft + 1 => do
      let (handleNat, reusedNat) ← match ← Prim.outboundAcquire (if u.isTls then 1 else 0) u.host u.port (if ssrfGuard then 1 else 0) isBlockedIpBytes with
        | .ok p => pure p | .error e => return .error e
      let handle := UInt64.ofNat handleNat
      match ← ExceptT.run (do liftE (Prim.outboundWriteAll handle wireReq); liftE (readUntilCrlfCrlf handle)) with
      | .error e =>
          Prim.outboundRelease handle 0
          if reusedNat != 0 && isIdempotentHttpMethod method && attemptsLeft > 0 then execHttpAttempt method u wireReq ssrfGuard attemptsLeft else return .error e
      | .ok (rxBuf, hdrEnd) =>
          let res : Except String (Nat × ByteArray × Array (String × String) × Bool) ← ExceptT.run do
            let head ← liftP (parseHttpResponseHead (rxBuf.extract 0 hdrEnd))
            let initBody := rxBuf.extract (hdrEnd + 4) rxBuf.size; let baseReuse := !head.connClose
            let (respBody, canReuse) ←
              if method == "HEAD" || head.status == 204 || head.status == 304 then pure (ByteArray.empty, baseReuse && initBody.isEmpty)
              else if head.isChunked then let (b, clean) ← readChunkedBody handle initBody 0 ByteArray.empty 65536; pure (b, baseReuse && clean)
              else if let some cl := head.contentLen then
                if cl > maxRespBodyBytes then throw "Content-Length too large"
                let full ← liftE (readAtLeast handle initBody cl)
                pure (if full.size == cl then full else full.extract 0 cl, baseReuse && full.size == cl)
              else pure (← liftE (readUntilEof handle initBody), false)
            return (head.status, respBody, head.headers, canReuse)
          match res with
          | .error e => Prim.outboundRelease handle 0; return .error e
          | .ok (st, b, h, reuse) => Prim.outboundRelease handle (if reuse then 1 else 0); return .ok (st, b, h)
def execHttpCall (method url : String) (headers : Array (String × String)) (body : ByteArray) (ssrfGuard : Bool) :
    IO (Except String (Nat × ByteArray × Array (String × String))) :=
  ExceptT.run do let u ← liftP (parseHttpUrl url); liftE (execHttpAttempt method u (← liftP (formatOutboundRequest method u headers body)) ssrfGuard 2)

/-! ## GCP RS256 OAuth2 Token Exchange -/

private structure GcpTokenCacheEntry where
  clientEmail : String
  scope       : String
  tokenUrl    : String
  accessToken : String
  expiresAt   : Nat
private def gcpCacheInsert (entries : Array GcpTokenCacheEntry) (entry : GcpTokenCacheEntry) : Array GcpTokenCacheEntry :=
  let filtered := entries.filter fun e => !(e.clientEmail == entry.clientEmail && e.scope == entry.scope && e.tokenUrl == entry.tokenUrl)
  if filtered.size < 8 then filtered.push entry
  else
    let evictIdx := (List.range filtered.size).foldl (init := 0) fun best i =>
      if h1 : i < filtered.size then (if h2 : best < filtered.size then if filtered[i].expiresAt < filtered[best].expiresAt then i else best else i) else best
    if h : evictIdx < filtered.size then filtered.set evictIdx entry else filtered
private def isAllowedGcpTokenEndpoint (u : ParsedUrl) : Bool :=
  u.isTls && u.port == 443 && match u.host.toLower, u.pathAndQuery with
  | "oauth2.googleapis.com", "/token" | "www.googleapis.com", "/oauth2/v4/token"
  | "www.googleapis.com", "/oauth2/v3/token" | "accounts.google.com", "/o/oauth2/token" => true | _, _ => false

def fetchGcpBearerToken (cache? : Option (Prim.StateBox (Array GcpTokenCacheEntry)))
    (saJson scopeOrAudience : String) (isIdToken : Bool := false) (ssrfGuard : Bool := true) : IO (Except String String) :=
  ExceptT.run do
    let j ← liftP ((Json.parse saJson).mapError (s!"invalid GCP service account JSON: {·}"))
    let some clientEmail := j.strAt? "client_email" | throw "GCP service account JSON missing `client_email`"
    let some privateKey := j.strAt? "private_key" | throw "GCP service account JSON missing `private_key`"
    let tokenUri := ((← loadNonEmptyEnv "QED_GCP_TOKEN_URL").orElse fun _ => j.strAt? "token_uri").getD "https://oauth2.googleapis.com/token"
    if ssrfGuard then
      if !tokenUri.startsWith "https://" || tokenUri.contains '#' then throw s!"GCP token_uri `{tokenUri}` must be a canonical https:// Google OAuth2 token endpoint"
      if !isAllowedGcpTokenEndpoint (← liftP (parseHttpUrl tokenUri)) then throw s!"GCP token_uri `{tokenUri}` is not an allowed Google OAuth2 token endpoint"
    let now ← nowSec
    if !isIdToken then if let some cache := cache? then
      if let some cached ← liftIO (Prim.atomicRead cache fun es => es.findSome? fun e =>
          if e.expiresAt > now + 60 && e.clientEmail == clientEmail && e.scope == scopeOrAudience && e.tokenUrl == tokenUri then some e.accessToken else none) then
        return cached
    let jwtHdr := Json.render (.obj [("alg", .str "RS256"), ("typ", .str "JWT")])
    let claims := Json.render (.obj [("iss", .str clientEmail), (if isIdToken then "target_audience" else "scope", .str scopeOrAudience),
      ("aud", .str tokenUri), ("iat", .num ⟨Int.ofNat now, 0⟩), ("exp", .num ⟨Int.ofNat (now + if isIdToken then 300 else 3600), 0⟩)])
    let signingInput := base64UrlEncode jwtHdr.toUTF8 ++ "." ++ base64UrlEncode claims.toUTF8
    let formBody := "grant_type=urn%3Aietf%3Aparams%3Aoauth%3Agrant-type%3Ajwt-bearer&assertion=" ++ signingInput ++ "." ++ base64UrlEncode (← liftE (Prim.rsaSha256Sign privateKey signingInput.toUTF8))
    let rj ← liftE (Qed.Auth.Oidc.execJsonHttp execHttpCall "POST" tokenUri
      #[("Content-Type", "application/x-www-form-urlencoded")] formBody.toUTF8 ssrfGuard (if isIdToken then "GCP OIDC" else "GCP OAuth2"))
    let respField := if isIdToken then "id_token" else "access_token"
    let some tok := rj.strAt? respField | throw s!"GCP token response missing `{respField}`"
    if !isIdToken then if let some cache := cache? then
      let expiresIn := match rj.natAt? "expires_in" with | some n => if n > 0 then min n (86400 * 365) else 3600 | none => 3600
      let entry : GcpTokenCacheEntry := { clientEmail, scope := scopeOrAudience, tokenUrl := tokenUri, accessToken := tok, expiresAt := (← nowSec) + expiresIn }
      liftIO (Prim.atomicModify cache fun cur => (gcpCacheInsert cur entry, ()))
    return tok

/-! ## Constant-Time HMAC Token Verification & Startup-Cached Server Config -/

private def isReservedTokenTag (tag : String) : Bool :=
  match tag.toList with | 'v' :: d :: rest | 't' :: 'x' :: d :: rest | 'o' :: 't' :: d :: rest => d.isDigit && rest.all Char.isDigit | _ => false
def verifyUserTokenWithNow (secrets : List String) (token : String) (now : Nat) (requireExpiring : Bool := false) : IO (Option String) := do
  if secrets.isEmpty then return none
  match (token.splitOn ".").reverse with
  | [] | [_] => return none
  | sigHex :: revPrefixParts =>
      if sigHex.length != 64 then return none
      let .ok sigBytes := Proto.decodeHex sigHex | return none
      let prefixParts := revPrefixParts.reverse; let payload := String.intercalate "." prefixParts
      let candidate? : Option String := match prefixParts with
        | "v1" :: expStr :: uidParts =>
            let uid := String.intercalate "." uidParts
            if uid.isEmpty then none else (parseStrictU64 expStr 18446744073709551615).bind fun expSec => if now < expSec then some uid else none
        | "v1" :: _ | [] => none
        | head :: _ => if requireExpiring || payload.isEmpty || payload.contains '\x00' || payload.startsWith "qed-tx:" || isReservedTokenTag head then none else some payload
      let some uid := candidate? | return none
      return if ← Qed.Auth.Oidc.anySecretVerify secrets payload.toUTF8 sigBytes then some uid else none

structure ServerConfig where
  authSecrets        : List String := []
  requireExpiring    : Bool := false
  rpcAllowedOrigins? : Option String := none
  wsAllowedOrigins?  : Option String := none
  bindHost           : String := "0.0.0.0"
  csp?               : Option String := some defaultCsp

def loadServerConfig (devMode : Bool) : IO ServerConfig := do
  let secrets := ([← Prim.getEnv "QED_AUTH_SECRET", ← Prim.getEnv "QED_AUTH_SECRET_PREV"].filterMap id).filter (!·.isEmpty)
  let bindHost ← match ← loadNonEmptyEnv "QED_HOST" with
    | some h => pure h | none => (·.getD (if devMode then "127.0.0.1" else "0.0.0.0")) <$> loadNonEmptyEnv "HOST"
  let csp? := match ← loadNonEmptyEnv "QED_CSP" with
    | some v => let lv := v.toLower; if lv == "off" || lv == "none" || lv == "disabled" then none else some (sanitizeHeader v) | none => some defaultCsp
  return { authSecrets := secrets, requireExpiring := (← loadNonEmptyEnv "QED_AUTH_REQUIRE_EXP") == some "1",
           rpcAllowedOrigins? := ← loadNonEmptyEnv "QED_RPC_ALLOWED_ORIGINS", wsAllowedOrigins? := ← loadNonEmptyEnv "QED_WS_ALLOWED_ORIGINS", bindHost, csp? }

private def parseCookiePairs (raw : String) : List (String × String) :=
  (raw.splitOn ";").filterMap fun seg =>
    let t := trimWs seg; if t.isEmpty then none
    else match t.splitOn "=" with | [] => none | [k] => some (trimWs k, "") | k :: vs => some (trimWs k, trimWs (String.intercalate "=" vs))
private def extractBearer (authHdr : String) : Option String :=
  let t := trimWs authHdr
  if startsWithCI t "bearer " then let tok := trimWs (String.Pos.Raw.extract t ⟨7⟩ ⟨t.utf8ByteSize⟩); if tok.isEmpty then none else some tok else none

/-! ## Native `MonadServer IO`, Database Transports & Transactions -/

private def mapApi {α : Type} (x : IO (Except String α)) : IO (Except ApiError α) := (·.mapError ApiError.internal) <$> x
private def liftApi {α : Type} (x : IO (Except String α)) : ExceptT ApiError IO α := liftE (mapApi x)
private def resolveBaseOrigin (req : OutboundReq) : IO String := do
  if req.serviceName == "Webhook" || req.ssrfGuard then return stripTrailingSlashes req.baseOrigin
  for key in ["QED_EXT_" ++ req.serviceName.toUpper ++ "_BASE", "QED_EXT_" ++ req.serviceName ++ "_BASE"] do
    if let some ov ← Prim.getEnv key then let t := stripTrailingSlashes (trimWs ov); if !t.isEmpty then return t
  return stripTrailingSlashes req.baseOrigin
private def requireSecretEnv (envVar : String) : IO (Except ApiError String) := do
  match ← Prim.getEnv envVar with
  | some tok => return if tok.isEmpty then .error (ApiError.internal s!"secret environment variable `{envVar}` is empty") else .ok tok
  | none => return .error (ApiError.internal s!"missing secret environment variable `{envVar}`")
private def resolveAuthHeaders (gcpCache? : Option (Prim.StateBox (Array GcpTokenCacheEntry))) (spec : AuthSpec) (ssrfGuard : Bool := true) :
    IO (Except ApiError (List (String × String))) := do
  match spec with
  | .none => return .ok []
  | .bearerSecret envVar => return (← requireSecretEnv envVar).map fun tok => [("Authorization", "Bearer " ++ sanitizeHeader tok)]
  | .headerSecret hdrName envVar => return (← requireSecretEnv envVar).map fun tok => [(sanitizeHeader hdrName, sanitizeHeader tok)]
  | .gcpServiceAccount envVar scope => ExceptT.run do
      let saJson ← liftE (requireSecretEnv envVar)
      let tok ← liftE ((·.mapError fun e => ApiError.internal s!"GCP OAuth2 token exchange failed: {e}") <$> fetchGcpBearerToken gcpCache? saJson scope (ssrfGuard := ssrfGuard))
      return [("Authorization", "Bearer " ++ sanitizeHeader tok)]
private inductive ResolvedDbTransport where
  | sqlite (path : String) | postgres (url : String) | httpSql (url : String) (bearer? : Option String)
  | d1 (accountId dbId token : String) | turso (url token : String)
private def stripSqliteScheme (u : String) : String :=
  match [("sqlite://", 9), ("sqlite:", 7), ("file:", 5)].find? fun (p, _) => u.startsWith p with
  | some (_, n) => String.ofList (u.toList.drop n) | none => u
private def requireEnv (envVar label : String) (default? : Option String := none) : IO (Except String String) := do
  return ((← loadNonEmptyEnv envVar).orElse fun _ => default?).elim (.error s!"missing {label} `{envVar}`") .ok
private def resolveDbEndpoint (ep : Db.DbEndpoint) : IO (Except String ResolvedDbTransport) := ExceptT.run do
  let reqEnv (v l : String) (d : Option String := none) := liftE (requireEnv v l d)
  match ep with
  | .urlEnv envVar =>
      let t := trimWs (← reqEnv envVar "database URL environment variable"); let tok? ← loadNonEmptyEnv (envVar ++ "_TOKEN")
      if t.startsWith "postgres://" || t.startsWith "postgresql://" then return .postgres t
      else if t.startsWith "sqlite:" || t.startsWith "file:" || t == ":memory:" || t.endsWith ".db" || t.endsWith ".sqlite" || t.endsWith ".sqlite3" then return .sqlite (stripSqliteScheme t)
      else if t.startsWith "http://" || t.startsWith "https://" then return .httpSql t tok?
      else throw s!"unrecognized database URL scheme: `{t}` (expected postgres://, sqlite://, or https://)"
  | .postgresEnv v => .postgres <$> reqEnv v "PostgreSQL URL environment variable"
  | .postgresUrl url => return .postgres (trimWs url) | .sqlitePath path => return .sqlite (stripSqliteScheme path)
  | .sqliteEnv v def? => (.sqlite ∘ stripSqliteScheme) <$> reqEnv v "SQLite path environment variable" def?
  | .cloudflareD1 aE aD dE dD tS => return .d1 (← reqEnv aE "Cloudflare account env" aD) (← reqEnv dE "Cloudflare D1 database env" dD) (← reqEnv tS "Cloudflare D1 token secret")
  | .turso uE tS => return .turso (← reqEnv uE "Turso URL env") (← reqEnv tS "Turso token secret")
  | .httpSql uE tS? => return .httpSql (← reqEnv uE "HTTP SQL URL env") (← liftIO (tS?.bindM loadNonEmptyEnv))
  | .managedPostgres dbName _ => .postgres <$> reqEnv (Qed.Cloud.managedPostgresSecretVar dbName) "managed PostgreSQL secret"
private def resolveDbConfigCore (rawDeployEnv? : Option String) (onCloudRun : Bool) (cfg : Db.DbConfig) : IO (Except ApiError ResolvedDbTransport) := do
  match rawDeployEnv? with
  | some rawEnv => match Qed.Cloud.DeployEnv.parse? (trimWs rawEnv) with
      | none => return .error (ApiError.internal s!"invalid QED_DEPLOY_ENV `{rawEnv}` (expected dev, preview, staging, or prod)")
      | some env => return (← resolveDbEndpoint (cfg.endpointForEnv env)).mapError fun e => ApiError.internal s!"database `{cfg.name}` unavailable for env `{env}`: {e}"
  | none => match ← resolveDbEndpoint cfg.endpoint with
      | .ok tr => return .ok tr
      | .error primaryErr =>
          if onCloudRun then return .error (ApiError.internal s!"database `{cfg.name}` unavailable on Cloud Run (fail-closed, no dev fallback): {primaryErr}")
          match cfg.devFallback? with
          | some fb => return (← resolveDbEndpoint fb).mapError fun fbErr => ApiError.internal s!"database `{cfg.name}` unavailable: {primaryErr} (fallback: {fbErr})"
          | none => return .error (ApiError.internal s!"database `{cfg.name}` unavailable: {primaryErr}")
private def loadDeployEnvFlags : IO (Option String × Bool) := do
  let rawDeployEnv? ← Prim.getEnv "QED_DEPLOY_ENV"
  let onCloudRun ← if rawDeployEnv?.isNone then (·.isSome) <$> loadNonEmptyEnv "K_SERVICE" else pure false
  return (rawDeployEnv?, onCloudRun)
private abbrev DbCfgKey := Db.DbEndpoint × Option Db.DbEndpoint × Option (Qed.Cloud.EnvMap Db.DbEndpoint)
private def dbCfgKey (c : Db.DbConfig) : DbCfgKey := (c.endpoint, c.devFallback?, c.envEndpoints?)
private structure DbResolveCache where
  rawDeployEnv? : Option String
  onCloudRun    : Bool
  primary?      : Option (String × DbCfgKey × ResolvedDbTransport)
  byName        : Prim.StateBox (Std.HashMap String (DbCfgKey × ResolvedDbTransport))
private def mkDbResolveCache (primaryDb? : Option Db.DbConfig) : IO DbResolveCache := do
  let (rawDeployEnv?, onCloudRun) ← loadDeployEnvFlags
  let byName ← Prim.mkStateBox (∅ : Std.HashMap String (DbCfgKey × ResolvedDbTransport))
  let primary? ← primaryDb?.bindM fun cfg => do
    match ← resolveDbConfigCore rawDeployEnv? onCloudRun cfg with | .ok tr => pure (some (cfg.name, dbCfgKey cfg, tr)) | .error _ => pure none
  return { rawDeployEnv?, onCloudRun, primary?, byName }
private def resolveDbConfig (cfg : Db.DbConfig) (cache? : Option DbResolveCache := none) : IO (Except ApiError ResolvedDbTransport) := do
  match cache? with
  | none => let (r, c) ← loadDeployEnvFlags; resolveDbConfigCore r c cfg
  | some cache =>
      let key := dbCfgKey cfg
      if let some (pName, pKey, pTr) := cache.primary? then if cfg.name == pName && pKey == key then return .ok pTr
      if let some (hKey, hTr) ← Prim.atomicRead cache.byName (·[cfg.name]?) then if hKey == key then return .ok hTr
      match ← resolveDbConfigCore cache.rawDeployEnv? cache.onCloudRun cfg with
      | .ok tr => Prim.atomicModify cache.byName fun m => ((if m.size < 32 then m.insert cfg.name (key, tr) else m), ()); return .ok tr
      | .error e => return .error e

private def execHttpSqlRaw (url : String) (bearer? : Option String) (body : ByteArray) : IO (Except ApiError String) := do
  let baseHdrs := #[("Content-Type", "application/json"), ("Accept", "application/json")]
  let hdrs := bearer?.elim baseHdrs fun tok => baseHdrs.push ("Authorization", "Bearer " ++ sanitizeHeader tok)
  match ← execHttpCall "POST" url hdrs body false with
  | .error e => return .error (ApiError.internal s!"HTTP SQL transport error: {e}")
  | .ok (status, respBody, _) =>
      let txt := (String.fromUTF8? respBody).getD ""
      return if 200 ≤ status && status < 300 then .ok txt else .error (ApiError.internal s!"HTTP SQL error {status}: {txt}")
private def execHttpTransportStmt (tr : ResolvedDbTransport) (sql : String) (params : Array Db.SqlVal) : IO (Except ApiError String) :=
  match tr with
  | .httpSql url bearer? => execHttpSqlRaw url bearer? (Db.HttpSql.encodeGenericQueryBody sql params .sqlite)
  | .d1 acc db tok => execHttpSqlRaw s!"https://api.cloudflare.com/client/v4/accounts/{Qed.encodeSeg acc}/d1/database/{Qed.encodeSeg db}/query" (some tok) (Db.HttpSql.encodeD1QueryBody sql params)
  | .turso baseUrl tok => execHttpSqlRaw (stripTrailingSlashes baseUrl ++ "/v2/pipeline") (some tok) (Db.HttpSql.encodeTursoPipelineBody sql params)
  | _ => return .error (ApiError.internal "unexpected non-HTTP SQL transport")
private def execRawOnTransport (tr : ResolvedDbTransport) (sqlSqlite sqlPg : String) (params : Array Db.SqlVal)
    (d1Cols : List String) (sqlHttp? : Option String := none) (decodeErrPrefix? : Option String := none) : IO (Except ApiError Db.DbResult) := do
  let mapDec (defPfx : String) (r : Except String Db.DbResult) := r.mapError fun e => ApiError.internal s!"{decodeErrPrefix?.getD defPfx}: {e}"
  match tr with
  | .sqlite path => mapApi (Prim.sqliteExec path sqlSqlite params)
  | .postgres url => mapApi (Db.PgWire.execParameterized url sqlPg params)
  | .httpSql _ _ | .d1 _ _ _ | .turso _ _ => ExceptT.run do
      let raw ← liftE (execHttpTransportStmt tr (sqlHttp?.getD sqlSqlite) params)
      liftP <| match tr with
        | .httpSql _ _ => mapDec "HTTP SQL result decode failed" (Db.decodeTaggedResultJson raw)
        | .d1 _ _ _ => mapDec "Cloudflare D1 result decode failed" (Db.HttpSql.decodeD1Response raw d1Cols)
        | _ => mapDec "Turso result decode failed" (Db.HttpSql.decodeTursoResponse raw)
private def execDdlOnTransport (tr : ResolvedDbTransport) (sqliteStmts : List String) (pgDdl : String) : IO (Except ApiError Unit) := do
  match tr with
  | .sqlite path => mapApi (Prim.sqliteDdl path (String.intercalate ";\n" sqliteStmts))
  | .postgres url => mapApi (Db.PgWire.execDdl url pgDdl)
  | .httpSql _ _ | .d1 _ _ _ | .turso _ _ =>
      for stmt in sqliteStmts do if let .error e ← execHttpTransportStmt tr stmt #[] then return .error e
      return .ok ()

private def introspectTable (runQ : String → IO (Except String Db.DbResult)) (colSql idxSql : String) (colIdx : Nat) (ignoreIdxErr : Bool) :
    IO (Except String (Bool × List String × List String)) :=
  let getCol (r : Db.DbRow) := match r[colIdx]? with | some (.text s) => some s | _ => none
  ExceptT.run do
    let colRes ← liftE (runQ colSql)
    if colRes.rows.isEmpty then return (false, [], [])
    let idxs ← match ← liftIO (runQ idxSql) with | .ok r => pure (r.rows.toList.filterMap getCol) | .error e => if ignoreIdxErr then pure [] else throw e
    return (true, colRes.rows.toList.filterMap getCol, idxs)
private def applyMigrationSteps (dialect : Db.SqlDialect) (steps : List Db.MigrationStep) (runDdl : String → IO (Except String Unit)) :
    IO (Except ApiError (List Db.MigrationStep)) :=
  mapApi <| ExceptT.run do
    liftP (Db.verifyMigrationSafe steps)
    let ddl := Db.renderMigrationDdl dialect steps
    if !ddl.isEmpty then liftE (runDdl ddl)
    return steps

def migrateDatabase (cfg : Db.DbConfig) : IO (Except ApiError (List Db.MigrationStep)) := ExceptT.run do
  if cfg.tables.isEmpty then return []
  match ← liftE (resolveDbConfig cfg) with
  | .sqlite path =>
      let mut allSteps : List Db.MigrationStep := []
      for tbl in cfg.tables do
        let (ex, cols, idxs) ← liftE ((·.mapError fun e => ApiError.internal s!"sqlite introspection failed: {e}") <$>
          introspectTable (Prim.sqliteExec path · #[]) ("PRAGMA table_info(" ++ tbl.name.quoteIdent ++ ")") ("PRAGMA index_list(" ++ tbl.name.quoteIdent ++ ")") 1 false)
        allSteps := allSteps ++ Db.diffTableSchema cols idxs tbl ex
      liftE (applyMigrationSteps .sqlite allSteps (Prim.sqliteDdl path))
  | .postgres url =>
      let mut allSteps : List Db.MigrationStep := []; let mut ok := true
      let colSql := "SELECT column_name FROM information_schema.columns WHERE table_schema = current_schema() AND table_name = $1"
      let idxSql := "SELECT indexname FROM pg_indexes WHERE schemaname = current_schema() AND tablename = $1"
      for tbl in cfg.tables do
        if ok then match ← introspectTable (Db.PgWire.execParameterized url · #[.text tbl.name.raw]) colSql idxSql 0 true with
          | .error _ => ok := false | .ok (ex, cols, idxs) => allSteps := allSteps ++ Db.diffTableSchema cols idxs tbl ex
      if ok then
        let steps ← liftE (applyMigrationSteps .postgres allSteps (Db.PgWire.execDdl url))
        let chkDdl := Db.renderDatabaseCheckDdl cfg.tables
        if !chkDdl.isEmpty then liftApi (Db.PgWire.execDdl url chkDdl)
        return steps
      else
        liftApi (Db.PgWire.execDdl url (Db.renderDatabaseDdl .postgres cfg.tables))
        let chkDdl := Db.renderDatabaseCheckDdl cfg.tables
        if !chkDdl.isEmpty then liftApi (Db.PgWire.execDdl url chkDdl)
        return cfg.tables.map .createTable
  | tr => liftE (execDdlOnTransport tr (cfg.tables.flatMap (·.renderDdlStatements .sqlite)) ""); return cfg.tables.map .createTable

initialize pgTxBox : IO.Ref (UInt64 × Std.HashMap UInt64 Db.PgWire.PgConn) ← IO.mkRef (1, {})
private def popPgTx (txId : UInt64) : IO (Option Db.PgWire.PgConn) :=
  pgTxBox.modifyGet fun (n, m) => match m[txId]? with | some c => (some c, (n, m.erase txId)) | none => (none, (n, m))
private def putPgTx (txId : UInt64) (c : Db.PgWire.PgConn) : IO Unit := pgTxBox.modify fun (n, m) => (n, m.insert txId c)
private def withPgTx {α : Type} (txId : UInt64) (f : Db.PgWire.PgConn → IO (Except ApiError α)) : IO (Except ApiError α) := do
  let some conn ← popPgTx txId | return .error (ApiError.internal "unknown or closed PostgreSQL transaction")
  f conn
private def withTxTransport {α : Type} (dbCache? : Option DbResolveCache) (cfg : Db.DbConfig)
    (onSqlite onPg : String → IO (Except ApiError α)) : IO (Except ApiError α) := ExceptT.run do
  match ← liftE (resolveDbConfig cfg dbCache?) with
  | .sqlite p => liftE (onSqlite p) | .postgres u => liftE (onPg u)
  | _ => throw (ApiError.internal "multi-statement transactions require SQLite or PostgreSQL transport")
private def finishPgTx (conn : Db.PgWire.PgConn) (cmd : String) : IO (Except ApiError Unit) := do
  let (res, conn') ← Db.PgWire.execSimpleOnConn conn cmd
  match res with
  | .ok cFinal => Db.PgWire.releaseConn cFinal; return .ok ()
  | .error e => Db.PgWire.releaseConn { conn' with healthy := false }; return .error (ApiError.internal s!"postgres {cmd} failed: {e}")

private def runAead (op : ByteArray → ByteArray → ByteArray → IO (Except String ByteArray))
    (keyEnv : String) (fallback? : Option String) (aad data : ByteArray) : IO (Except ApiError ByteArray) := do
  match (← loadNonEmptyEnv keyEnv).orElse fun _ => fallback?.bind fun s => if s.isEmpty then none else some s with
  | some k => mapApi (op k.toUTF8 aad data)
  | none => return .error (ApiError.internal s!"missing required encryption key `{keyEnv}`")

@[implicit_reducible]
private def mkNativeServerInstWith (gcpCache? : Option (Prim.StateBox (Array GcpTokenCacheEntry)))
    (cookieSink? : Option (IO.Ref (Array SetCookie)) := none) (sseSink? : Option (IO.Ref (Array SseEvent)) := none)
    (dbCache? : Option DbResolveCache := none) (ssrfGuard : Bool := true) : MonadServer IO where
  exec
    | .httpCall req => ExceptT.run do
        let authHdrs ← liftE (resolveAuthHeaders gcpCache? req.auth ssrfGuard)
        let allHdrs := (req.headers.map (fun (k, v) => (sanitizeHeader k, sanitizeHeader v)) ++ authHdrs).toArray
        let (st, respBody, respHdrs) ← liftE ((·.mapError fun e => ApiError.internal s!"external HTTP transport error ({req.serviceName}): {e}") <$>
          execHttpCall req.method ((← resolveBaseOrigin req) ++ req.pathAndQuery) allHdrs req.body req.ssrfGuard)
        return { status := st.toUInt32, body := respBody, headers := respHdrs.toList }
    | .dbExec cfg q => ExceptT.run do match ← liftE (resolveDbConfig cfg dbCache?) with
        | tr@(.postgres _) => let (sqlPg, pPg) := q.compile .postgres; liftE (execRawOnTransport tr "" sqlPg pPg [])
        | tr => let (sqlSq, pSq) := q.compile .sqlite; liftE (execRawOnTransport tr sqlSq "" pSq (Db.HttpSql.queryExpectedCols q))
    | .dbExecDdl cfg => (·.map fun _ => ()) <$> migrateDatabase cfg
    | .dbTxBegin cfg => withTxTransport dbCache? cfg (mapApi ∘ Prim.sqliteTxBegin) fun url => mapApi <| ExceptT.run do
        let (conn, _) ← liftE (Db.PgWire.acquireConn (← liftP (Db.PgWire.parsePgUrl url)))
        let (res, conn') ← Db.PgWire.execSimpleOnConn conn "BEGIN"
        match res with
        | .error e => Db.PgWire.releaseConn { conn' with healthy := false }; throw s!"postgres BEGIN failed: {e}"
        | .ok cReady => pgTxBox.modifyGet fun (n, m) => (n, (n + 1, m.insert n cReady))
    | .dbTxExec cfg tid q => withTxTransport dbCache? cfg
        (fun _ => let (s, p) := q.compile .sqlite; mapApi (Prim.sqliteTxExec tid s p))
        (fun _ => withPgTx tid fun conn => do
          let (s, p) := q.compile .postgres; let (res, conn') ← Db.PgWire.execOnConn conn s p
          match res with
          | .ok (dbRes, cNext) => putPgTx tid cNext; return .ok dbRes
          | .error e => (if conn'.healthy then putPgTx tid conn' else Db.PgWire.releaseConn conn'); return .error (ApiError.internal e))
    | .dbTxCommit cfg tid => withTxTransport dbCache? cfg (fun _ => mapApi (Prim.sqliteTxCommit tid)) (fun _ => withPgTx tid (finishPgTx · "COMMIT"))
    | .dbTxRollback cfg tid => do match ← resolveDbConfig cfg dbCache? with
        | .ok (.sqlite _) => Prim.sqliteTxRollback tid
        | .ok (.postgres _) => if let some conn ← popPgTx tid then discard <| finishPgTx conn "ROLLBACK"
        | _ => pure ()
    | .setCookie c => if let some ref := cookieSink? then ref.modify (·.push c) else pure ()
    | .sendSse ev => if let some ref := sseSink? then ref.modify (·.push ev) else pure ()
    | .readEnv v => Prim.getEnv v | .nowMs => Prim.nowMs | .randomHex n => Prim.randomHex n
    | .hmacSha256 key msg => Prim.hmacSha256 key msg | .wsBroadcast t p => Prim.wsBroadcast t p
    | .aeadEncrypt kEnv fb aad pt => runAead Prim.aeadEncrypt kEnv fb aad pt
    | .aeadDecrypt kEnv fb aad ct => runAead Prim.aeadDecrypt kEnv fb aad ct

@[implicit_reducible]
def mkNativeServerInst (gcpCache? : Option (Prim.StateBox (Array GcpTokenCacheEntry)))
    (cookieSink? : Option (IO.Ref (Array SetCookie)) := none) (sseSink? : Option (IO.Ref (Array SseEvent)) := none) : MonadServer IO :=
  mkNativeServerInstWith gcpCache? cookieSink? sseSink? none
instance : MonadServer IO := mkNativeServerInst none none
@[implicit_reducible]
def withStateBox {σ : Type} (box : Prim.StateBox σ) : MonadAtomic σ IO where
  runAtomic := Prim.atomicModify box; runAtomicRead := Prim.atomicRead box

/-! ## Startup Checks & Auth User Tracking -/

private def checkAllStartup {α β ε : Type} (xs : Array α) (run : α → IO (Except ε β)) (errMsg : α → ε → String) : IO Bool :=
  xs.foldlM (init := true) fun ok x => do match ← run x with | .ok _ => return ok | .error e => IO.eprintln (errMsg x e); return false
def verifyRequiredSecrets (secrets : Array String) : IO Bool :=
  checkAllStartup secrets requireSecretEnv fun name _ => s!"✗ missing required secret `{name}` (set `{name}` before starting the server)"
def initDatabases (dbs : Array Db.DbConfig) : IO Bool :=
  checkAllStartup dbs (fun cfg => (·.map fun _ => ()) <$> migrateDatabase cfg) fun cfg e => s!"✗ database `{cfg.name}` initialization failed: {e.message}"

private def ensureAuthUsersTable (cfg : Db.DbConfig) : IO (Except ApiError Unit) := ExceptT.run do
  let ddl (intTy : String) := s!"CREATE TABLE IF NOT EXISTS \"_qed_auth_users\" (\"sub\" TEXT PRIMARY KEY, \"created_at\" {intTy} NOT NULL)"
  liftE (execDdlOnTransport (← liftE (resolveDbConfig cfg)) [ddl "INTEGER"] (ddl "BIGINT"))
private def claimAuthUser (primaryDb? : Option Db.DbConfig) (memSeen : Prim.StateBox (Std.HashSet String)) (sub : String) : IO (Except ApiError Bool) :=
  ExceptT.run do match primaryDb? with
    | none => liftIO (Prim.atomicModify memSeen fun s => if s.contains sub then (s, false) else (s.insert sub, true))
    | some cfg =>
        let tr ← liftE (resolveDbConfig cfg)
        let sqlSq := "INSERT OR IGNORE INTO \"_qed_auth_users\" (\"sub\", \"created_at\") VALUES (?1, ?2)"
        let sqlPg := "INSERT INTO \"_qed_auth_users\" (\"sub\", \"created_at\") VALUES ($1, $2) ON CONFLICT (\"sub\") DO NOTHING RETURNING \"sub\""
        let res ← liftE (execRawOnTransport tr sqlSq sqlPg #[.text sub, .int (Int.ofNat (← Prim.nowMs).toNat)] ["sub"] (some (sqlSq ++ " RETURNING \"sub\"")) (some "auth user claim decode failed"))
        return match tr with | .sqlite _ => res.affected > 0 | .postgres _ => !res.rows.isEmpty | _ => !res.rows.isEmpty || res.affected > 0
private def releaseAuthUser (primaryDb? : Option Db.DbConfig) (memSeen : Prim.StateBox (Std.HashSet String)) (sub : String) : IO Unit := do
  match primaryDb? with
  | none => Prim.atomicModify memSeen fun s => (s.erase sub, ())
  | some cfg => if let .ok tr ← resolveDbConfig cfg then
      discard <| execRawOnTransport tr "DELETE FROM \"_qed_auth_users\" WHERE \"sub\" = ?1" "DELETE FROM \"_qed_auth_users\" WHERE \"sub\" = $1" #[.text sub] []

/-! ## Full-Stack Native Server Runner (HTTP/1.1 + Static + RFC 6455 WS + SSR) -/

private abbrev WsDispatchFn := RequestCtx → UInt8 → String → ByteArray → ByteArray → IO (Except ApiError ByteArray)
private abbrev WsSubs := Array (Nat × String × ByteArray)
private structure WsFragState where
  active : Bool := false
  opcode : UInt8 := 0
  buf    : ByteArray := ByteArray.empty

private def handleMuxPayload (wsDispatchFn : WsDispatchFn) (ctx : RequestCtx) (rawFrame : ByteArray) (subs : WsSubs) :
    IO (ByteArray × WsSubs × Array Prim.WsSubOp) := do
  let findSub (sid : UInt32) := subs.find? fun (s, _, _) => s == sid.toNat
  let dropSub (sid : Nat) (arr : WsSubs) := arr.filter fun (s, _, _) => s != sid
  let errWire (sid : UInt32) (msg : String) := encodeWsFrame 0x02 (WsMuxFrame.encode (.err sid msg))
  match WsMuxFrame.decode rawFrame with
  | .error errMsg => return ((readU32BE rawFrame 1).elim ByteArray.empty fun s => errWire (UInt32.ofNat s) errMsg, subs, #[])
  | .ok (.sub sid ch params) =>
      if ch.isEmpty || ch.utf8ByteSize > 256 then return (errWire sid "invalid channel name length", subs, #[])
      let oldSub? := findSub sid; let subsNoOld := dropSub sid.toNat subs
      if let some (_, oldCh, oldParams) := oldSub? then discard <| wsDispatchFn ctx 3 oldCh oldParams ByteArray.empty
      let remOps := if oldSub?.isSome then #[Prim.WsSubOp.removeSub sid.toNat] else #[]
      if subsNoOld.size >= 64 then return (errWire sid "too many subscriptions on connection", subsNoOld, remOps)
      match ← wsDispatchFn ctx 1 ch params ByteArray.empty with
      | .ok snap => return (encodeWsFrame 0x02 (WsMuxFrame.encode (.joinOk sid snap)), subsNoOld.push (sid.toNat, ch, params), #[.addSub sid.toNat (ch ++ ":" ++ Proto.encodeHex params) ch params])
      | .error e => return (errWire sid e.message, subsNoOld, remOps)
  | .ok (.unsub sid) =>
      if let some (_, ch, params) := findSub sid then
        discard <| wsDispatchFn ctx 3 ch params ByteArray.empty; return (ByteArray.empty, dropSub sid.toNat subs, #[.removeSub sid.toNat])
      return (ByteArray.empty, subs, #[])
  | .ok (.send sid payload) =>
      if let some (_, ch, params) := findSub sid then discard <| wsDispatchFn ctx 2 ch params payload
      return (ByteArray.empty, subs, #[])
  | .ok _ => return (ByteArray.empty, subs, #[])

private def stepWsRxLoop (wsDispatchFn : WsDispatchFn) (ctx : RequestCtx) (rx : ByteArray) (off : Nat) (frag : WsFragState)
    (subs : WsSubs) (outWire : ByteArray) (ops : Array Prim.WsSubOp) : IO (Prim.WsStepOut WsFragState) := do
  let mkOut (c : Nat) (w : ByteArray) (cl : Nat) (f := frag) (o := ops) : Prim.WsStepOut WsFragState := { consumed := c, outWire := w, closeFlag := cl, fragState := f, subOps := o }
  match decodeWsFrame rx off with
  | .needMore => return mkOut off outWire 0
  | .protocolErr code => return mkOut rx.size (outWire ++ encodeWsCloseFrame code) 1
  | .frame fin opcode payload consumed =>
      if _ : consumed = 0 then return mkOut off outWire 0
      else
      let nextOff := off + consumed
      let closeWith (code : UInt16) (f := frag) := pure (true, f, subs, outWire ++ encodeWsCloseFrame code, ops)
      let dispatchMsg (op : UInt8) (data : ByteArray) (f : WsFragState) := do
        let (w', s', o') ← if op == 0x02 then handleMuxPayload wsDispatchFn ctx data subs else pure (ByteArray.empty, subs, #[])
        pure (false, f, s', outWire ++ w', ops ++ o')
      let (close, frag', subs', outWire', ops') ←
        if opcode == 0x08 then closeWith 1000
        else if opcode == 0x09 then pure (false, frag, subs, outWire ++ encodeWsFrame 0x0A payload, ops)
        else if opcode == 0x0A then pure (false, frag, subs, outWire, ops)
        else if opcode == 0x01 || opcode == 0x02 then
          if frag.active then closeWith 1002 else if fin then dispatchMsg opcode payload frag else pure (false, { active := true, opcode, buf := payload }, subs, outWire, ops)
        else if opcode == 0x00 then
          if !frag.active then closeWith 1002 else if frag.buf.size + payload.size > maxWsMsgBytes then closeWith 1009 {}
          else let combined := frag.buf ++ payload; if fin then dispatchMsg frag.opcode combined {} else pure (false, { frag with buf := combined }, subs, outWire, ops)
        else closeWith 1002
      if !close ∧ nextOff < rx.size then stepWsRxLoop wsDispatchFn ctx rx nextOff frag' subs' outWire' ops'
      else return mkOut nextOff outWire' (if close then 1 else 0) frag' ops'
termination_by rx.size - off

private def stripQuery (target : String) : String := (findByte target 0 63).elim target fun q => String.Pos.Raw.extract target ⟨0⟩ ⟨q⟩
private def dropPrefixBytes (s : String) (byteLen : Nat) : String := if byteLen >= s.utf8ByteSize then "" else String.Pos.Raw.extract s ⟨byteLen⟩ ⟨s.utf8ByteSize⟩
private def resolveAuthPrincipal (cfg : ServerConfig) (oidcRt? : Option Qed.Auth.Oidc.OidcRuntime)
    (bearer? : Option String) (cookies : List (String × String)) : IO (Option String × List (String × String)) := do
  if let (some rt, some tok) := (oidcRt?, bearer?) then
    if (tok.splitOn ".").length == 3 then
      return match ← Qed.Auth.Oidc.verifyOidcJwt execHttpCall rt tok with | .ok jc => (some jc.sub, jc.flatClaims) | .error _ => (none, [])
  let sessionSecrets := match oidcRt? with | some rt => if !rt.cfg.sessionSecrets.isEmpty then rt.cfg.sessionSecrets else cfg.authSecrets | none => cfg.authSecrets
  if let some tok := bearer?.orElse (fun _ => cookies.lookup "qed_session") then
    let now ← nowSec
    if tok.startsWith "tx1." then return (none, [])
    if tok.startsWith "v2." then return (← Qed.Auth.Oidc.verifySessionCookieV2 sessionSecrets tok now).elim (none, []) fun p => (some p.userId, p.claims)
    if !sessionSecrets.isEmpty then return (← verifyUserTokenWithNow sessionSecrets tok now cfg.requireExpiring, [])
  return (none, [])
private def buildRequestCtxReq (cfg : ServerConfig) (req : ParsedReqHead) (clientIp : String)
    (body : ByteArray := ByteArray.empty) (oidcRt? : Option Qed.Auth.Oidc.OidcRuntime := none) : IO RequestCtx := do
  let hdrList := req.headers.toList
  let cookies := if !req.hasCookie then [] else hdrList.foldl (fun acc (k, v) => if eqCI k "cookie" then acc ++ parseCookiePairs v else acc) []
  let bearer? := req.auth?.bind extractBearer
  let (userId?, claims) ← resolveAuthPrincipal cfg oidcRt? bearer? cookies
  let query := (findByte req.target 0 63).elim "" fun q => if q + 1 >= req.target.utf8ByteSize then "" else String.Pos.Raw.extract req.target ⟨q + 1⟩ ⟨req.target.utf8ByteSize⟩
  return { headers := hdrList, cookies, bearerToken := bearer?, userId := userId?, claims, clientIp, query,
           body := if body.isEmpty then "" else (String.fromUTF8? body).getD "" }

private structure WireVariants where
  headKA    : ByteArray
  headClose : ByteArray
  fullKA    : ByteArray
  fullClose : ByteArray
private def WireVariants.build (mime : String) (body : ByteArray) (etag cacheCtrl : String) (hdrs : List (String × String)) : WireVariants :=
  let h (ka : Bool) := formatHttpResponseHead 200 mime body.size ka false (some etag) (some cacheCtrl) hdrs
  let hKA := h true; let hCl := h false; { headKA := hKA, headClose := hCl, fullKA := hKA ++ body, fullClose := hCl ++ body }
private def WireVariants.pick (w : WireVariants) (isHead keepAlive : Bool) : ByteArray :=
  if isHead then (if keepAlive then w.headKA else w.headClose) else (if keepAlive then w.fullKA else w.fullClose)
private structure CachedStaticAsset where
  etag  : String
  plain : WireVariants
  gzip? : Option WireVariants := none
private def CachedStaticAsset.serve (c : CachedStaticAsset) (req : ParsedReqHead) (isHead keepAlive : Bool) : ByteArray :=
  if req.hasIfNoneMatch && etagMatchesIfNoneMatch req.headers c.etag then formatNotModifiedResponse c.etag keepAlive
  else (if req.acceptsGzip then c.gzip?.getD c.plain else c.plain).pick isHead keepAlive

private def cookieHeaders (cookies : List SetCookie) : List (String × String) := cookies.map fun c => ("Set-Cookie", c.render)
private def tryGzip (body : ByteArray) (compressible : Bool) : IO (Option ByteArray) := do
  if compressible && body.size >= 256 then let gz ← Prim.gzipCompress body; if !gz.isEmpty && gz.size < body.size then return some gz
  return none
private def maybeGzipResponse (status : Nat) (contentType : String) (body : ByteArray) (isHead keepAlive noStore acceptsGzip compressible : Bool)
    (etag? cacheCtrl? : Option String := none) (extraHeaders : List (String × String) := []) (contentLen : Nat := body.size) : IO ByteArray := do
  if !isHead && acceptsGzip then
    if let some gz ← tryGzip body compressible then
      let hdrs := ("Content-Encoding", "gzip") :: (if extraHeaders.any (fun (k, _) => eqCI k "vary") then extraHeaders else ("Vary", "Accept-Encoding") :: extraHeaders)
      return formatHttpResponseHead status contentType gz.size keepAlive noStore etag? cacheCtrl? hdrs ++ gz
  let head := formatHttpResponseHead status contentType contentLen keepAlive noStore etag? cacheCtrl? extraHeaders
  return if isHead then head else head ++ body

private def serveStaticAsset (staticDirFd : Prim.StaticDir) (assetCache? : Option (Prim.StateBox (Std.HashMap String CachedStaticAsset)))
    (req : ParsedReqHead) (st : StaticTarget) (devMode : Bool) : IO ByteArray := do
  let cacheable := assetCache?.isSome && !devMode && !st.noStore && isContentHashedAsset st.relPath
  if cacheable then if let some assetCache := assetCache? then
    if let some hit ← Prim.atomicRead assetCache (·[st.relPath]?) then return hit.serve req st.isHead req.keepAlive
  let compressible := isCompressibleMime st.mime
  if let some (fsize, mtimeMs, fbytes) ← Prim.readStaticFile staticDirFd st.relPath (if st.isHead && !cacheable then 1 else 0) then
    let sendFile (noStore : Bool) (etag? cc? : Option String) (hdrs : List (String × String)) :=
      maybeGzipResponse 200 st.mime fbytes st.isHead req.keepAlive noStore req.acceptsGzip compressible etag? cc? hdrs fsize
    if !st.noStore then
      let etag := s!"W/\"{fsize}-{mtimeMs}\""; let varyHdrs := if compressible then [("Vary", "Accept-Encoding")] else []
      let cacheCtrl := if isContentHashedAsset st.relPath then "public, max-age=31536000, immutable" else "public, max-age=0, must-revalidate"
      if cacheable && fsize <= 2 * 1024 * 1024 then
        let gzip? := (← tryGzip fbytes compressible).map fun gz => WireVariants.build st.mime gz etag cacheCtrl [("Content-Encoding", "gzip"), ("Vary", "Accept-Encoding")]
        let entry : CachedStaticAsset := { etag, plain := WireVariants.build st.mime fbytes etag cacheCtrl varyHdrs, gzip? }
        if let some assetCache := assetCache? then Prim.atomicModify assetCache fun m => ((if m.size < 64 then m.insert st.relPath entry else m), ())
        return entry.serve req st.isHead req.keepAlive
      if req.hasIfNoneMatch && etagMatchesIfNoneMatch req.headers etag then return formatNotModifiedResponse etag req.keepAlive
      return ← sendFile false (some etag) (some cacheCtrl) varyHdrs
    else return ← sendFile true none none []
  else if st.isBuildId then
    return formatHttpResponse 200 st.mime (if st.relPath == "__dev_status" then "{\"id\":\"0\",\"status\":\"ok\"}".toUTF8 else "0".toUTF8) st.isHead req.keepAlive true
  else if st.relPath == "favicon.ico" then
    return formatNoContentResponse req.keepAlive (some "public, max-age=86400")
  else return formatTextResponse 404 "not found" st.isHead req.keepAlive

private structure HttpLoopCtx where
  cfg         : ServerConfig
  staticDirFd : Prim.StaticDir
  healthKA    : ByteArray
  healthClose : ByteArray
  htmlCspHdrs : List (String × String)
private def serveHttpLoop (staticDir : String) (port : UInt16) (devMode : Bool) (numWorkers : UInt32)
    (setup : HttpLoopCtx → IO ((ParsedReqHead → String → String → Nat → IO (Prim.HttpHeadAction ParsedReqHead RequestCtx)) ×
      (ParsedReqHead → ByteArray → String → IO ByteArray) ×
      (RequestCtx → ByteArray → WsFragState → WsSubs → IO (Prim.WsStepOut WsFragState)) ×
      (RequestCtx → String → ByteArray → IO Unit) ×
      Option (RequestCtx → String → ByteArray → ByteArray → WsProjectOut))) : IO UInt32 := do
  let cfg ← loadServerConfig devMode; let staticDirFd ← Prim.openStaticDir staticDir
  let mkHealth (ka : Bool) := formatHttpResponse 200 "application/json" "{\"ok\":true}".toUTF8 false ka false
  let healthKA := mkHealth true; let healthClose := mkHealth false
  let (onParsedHead, onBody, onWsBytes, onWsLeave, onWsProject) ← setup { cfg, staticDirFd, healthKA, healthClose, htmlCspHdrs := cfg.csp?.elim [] fun p => [("Content-Security-Policy", p)] }
  let onHead (headBytes : ByteArray) (clientIp : String) (inline : Nat) : IO (Prim.HttpHeadAction ParsedReqHead RequestCtx) := do
    match parseRequestHead headBytes with
    | .error (code, msg) => return .doneClose (formatErrorResponse code msg)
    | .ok req =>
        let pathOnly := stripQuery req.target
        if req.method == "GET" && pathOnly == "/_qed/health" && req.contentLen == 0 then return if req.keepAlive then .doneKeepAlive healthKA else .doneClose healthClose
        onParsedHead req clientIp pathOnly inline
  Prim.serveNative cfg.bindHost port numWorkers ({} : WsFragState) onHead onBody onWsBytes onWsLeave onWsProject
private def finishHeadWire (req : ParsedReqHead) (wire : ByteArray) : Prim.HttpHeadAction ParsedReqHead RequestCtx :=
  if req.keepAlive then .doneKeepAlive wire else .doneClose wire
private def closedWsBytes (_ : RequestCtx) (rx : ByteArray) (frag : WsFragState) (_ : WsSubs) :
    IO (Prim.WsStepOut WsFragState) := pure { consumed := rx.size, outWire := ByteArray.empty, closeFlag := 1, fragState := frag, subOps := #[] }

private structure FullstackConfig where
  title            : String
  serverShortName  : String
  requiredSecrets  : Array String
  dispatchFn       : RequestCtx → String → ByteArray → IO (Except ApiError ByteArray × Array SetCookie)
  port             : UInt16
  staticDir        : String
  devMode          : Bool := false
  numWorkers       : UInt32 := 0
  wsDispatchFn?    : Option WsDispatchFn := none
  blockingMethods? : Option (Array String) := none
  httpDispatchFn?  : Option (RequestCtx → String → String → IO (Except ApiError (Option HttpResponse) × Array SetCookie)) := none
  jobs             : Array IoJob := #[]
  authSpec?        : Option Qed.Auth.OidcAuthSpec := none
  authHookFn?      : Option (RequestCtx → UInt8 → IO (Except ApiError Unit × Array SetCookie)) := none
  authHookFlags    : Bool × Bool := (false, false)
  primaryDb?       : Option Db.DbConfig := none
  wsProjectFn?     : Option (RequestCtx → String → ByteArray → ByteArray → WsProjectOut) := none

private def runFullstackCore {Model Msg : Type} (app : Qed.App Model Msg) (fc : FullstackConfig) : IO UInt32 := do
  let activeEnv? := (← Prim.getEnv "QED_DEPLOY_ENV").bind fun s => Qed.Cloud.DeployEnv.parse? (trimWs s)
  let mut reqSecrets := fc.requiredSecrets
  if let some spec := fc.authSpec? then
    if spec.isManaged && !fc.devMode && activeEnv? != some .dev && activeEnv? != some .preview then
      if let some sec := spec.clientSecretEnv? then if !reqSecrets.contains sec then reqSecrets := reqSecrets.push sec
  if !(← verifyRequiredSecrets reqSecrets) then return 1
  let (hasOnCreateAccount, hasOnSignIn) := fc.authHookFlags
  if hasOnCreateAccount then if let some dbCfg := fc.primaryDb? then
    if let .error e ← ensureAuthUsersTable dbCfg then IO.eprintln s!"✗ failed to initialize `_qed_auth_users` table: {e.message}"; return 1
  serveHttpLoop fc.staticDir fc.port fc.devMode fc.numWorkers fun loop => do
    let cfg := loop.cfg
    let oidcRt? ← fc.authSpec?.bindM fun spec => Qed.Auth.Oidc.initOidcRuntime spec cfg.authSecrets fc.devMode
    let htmlSecHdrs : List (String × String) :=
      if oidcRt?.any (·.cfg.googleOneTapEnabled) && cfg.csp? == some defaultCsp then
        [("Content-Security-Policy",
          "default-src 'self'; script-src 'self' https://accounts.google.com/gsi/client; style-src 'self' 'unsafe-inline' https://accounts.google.com/gsi/style; frame-src 'self' https://accounts.google.com/gsi/; connect-src 'self' https://accounts.google.com/gsi/; object-src 'none'; base-uri 'self'; frame-ancestors 'none'"),
         ("Cross-Origin-Opener-Policy", "same-origin-allow-popups")]
      else loop.htmlCspHdrs
    let memSeenAuthUsers ← Prim.mkStateBox (∅ : Std.HashSet String)
    let hostScript ← if fc.devMode then pure "/qed_host.mjs" else do
      let h? := (← Prim.readStaticFile loop.staticDirFd "qed_manifest.json" 0).bind fun (_, _, bytes) =>
        (String.fromUTF8? bytes).bind fun raw => (Json.parse raw).toOption.bind fun j => (j.strAt? "host").filter isSafeUrl
      pure (h?.getD "/qed_host.mjs")
    let rpcPrefix := "/_qed/rpc/" ++ fc.serverShortName ++ "/"; let rpcPrefixBytes := rpcPrefix.utf8ByteSize
    let wsPath := "/_qed/ws/" ++ fc.serverShortName; let assetCache ← Prim.mkStateBox (∅ : Std.HashMap String CachedStaticAsset)
    let docShell := mkPrebuiltDocShell fc.title hostScript (renderStyleSheet app.styles) app.stylesheets

    let dispatchAppReqWith (req : ParsedReqHead) (body : ByteArray) (clientIp pathOnly : String) (staticTarget? : Option StaticTarget) : IO ByteArray := do
      let isHead := req.method == "HEAD"
      let textResp (code : Nat) (msg : String) (hdrs : List (String × String) := []) := formatTextResponse code msg isHead req.keepAlive hdrs
      let apiErrResp (e : ApiError) (cs : Array SetCookie) := textResp e.httpStatus.toNat e.message (cookieHeaders cs.toList)
      let serveStatic (st : StaticTarget) := serveStaticAsset loop.staticDirFd (some assetCache) req st fc.devMode
      if req.method == "GET" && pathOnly == "/_qed/health" then return if req.keepAlive then loop.healthKA else loop.healthClose
      if let some st := staticTarget? then if isContentHashedAsset st.relPath then return ← serveStatic st
      let ctx ← buildRequestCtxReq cfg req clientIp body oidcRt?
      if pathOnly.startsWith "/_qed/auth/" then if let some rt := oidcRt? then
        if ((req.method == "POST" || req.method == "GET") && pathOnly == rt.cfg.logoutPath) || (req.method == "POST" && pathOnly == "/_qed/auth/onetap") then
          if let .error (code, msg) := checkOriginAndFetchSite req cfg.rpcAllowedOrigins? false "auth endpoint" then return textResp code msg
        let onAuthCallback? := fc.authHookFn?.map fun hookFn sub filteredClaims => ExceptT.run do
          let hookCtx : RequestCtx := { ctx with userId := some sub, claims := filteredClaims }
          let runHook (kind : UInt8) (onErr : IO Unit := pure ()) : ExceptT (Nat × String) IO (Array SetCookie) := do
            let (hRes, hCookies) ← hookFn hookCtx kind
            match hRes with | .ok () => return hCookies | .error e => onErr; throw (e.httpStatus.toNat, e.message)
          let mut outCookies : Array SetCookie := #[]
          if hasOnCreateAccount then
            if ← liftE ((·.mapError fun e => (e.httpStatus.toNat, e.message)) <$> claimAuthUser fc.primaryDb? memSeenAuthUsers sub) then
              outCookies := outCookies ++ (← runHook 0 (releaseAuthUser fc.primaryDb? memSeenAuthUsers sub))
          if hasOnSignIn then outCookies := outCookies ++ (← runHook 1)
          return outCookies
        if let some authResp ← Qed.Auth.Oidc.handleAuthRoute execHttpCall rt req pathOnly ctx.query ctx.cookies ctx.userId ctx.claims isHead onAuthCallback? body then return authResp
      if req.method == "POST" && pathOnly.startsWith rpcPrefix then
        let isProtoCt (v : String) := eqCI (trimWs ((findByte v 0 59).elim v fun s => String.Pos.Raw.extract v ⟨0⟩ ⟨s⟩)) "application/x-protobuf"
        let csrfRes : Except (Nat × String) Unit := do
          checkOriginAndFetchSite req cfg.rpcAllowedOrigins? false "RPC"
          if req.dupCt || !req.contentType?.any isProtoCt then throw (415, "RPC requires Content-Type: application/x-protobuf")
        match csrfRes with
        | .error (code, msg) => return textResp code msg
        | .ok () =>
            let (res, cookies) ← fc.dispatchFn ctx (dropPrefixBytes pathOnly rpcPrefixBytes) body
            match res with
            | .ok respBytes =>
                if cookies.isEmpty then return formatOkProtoResponse respBytes isHead req.keepAlive
                else return formatHttpResponse 200 "application/x-protobuf" respBytes isHead req.keepAlive false (extraHeaders := cookieHeaders cookies.toList)
            | .error apiErr => return apiErrResp apiErr cookies
      if !pathOnly.startsWith "/_qed/" then if let some httpDispatchFn := fc.httpDispatchFn? then
        let (hRes, cookies) ← httpDispatchFn ctx (if isHead then "GET" else req.method) pathOnly
        match hRes with
        | .error apiErr => return apiErrResp apiErr cookies
        | .ok (some resp) =>
            let cspHdrs := if startsWithCI resp.contentType "text/html" && !resp.headers.any (fun (k, _) => eqCI k "content-security-policy") then htmlSecHdrs else []
            return ← maybeGzipResponse resp.status resp.contentType resp.body isHead req.keepAlive false req.acceptsGzip
              (!startsWithCI resp.contentType "text/event-stream" && isCompressibleMime resp.contentType)
              (extraHeaders := resp.headers ++ cspHdrs ++ cookieHeaders (cookies.toList ++ resp.cookies))
        | .ok none => pure ()
      if let some st := staticTarget? then return ← serveStatic st
      if (req.method == "GET" || isHead) && !pathOnly.startsWith "/_qed/" then
        let ssrDispatchBytes (reqMethod url : String) (reqBody : ByteArray) : IO (Except String ByteArray) := do
          let uPath := stripQuery url
          if reqMethod == "POST" && uPath.startsWith rpcPrefix then return (← fc.dispatchFn ctx (dropPrefixBytes uPath rpcPrefixBytes) reqBody).1.mapError (·.message)
          return .error s!"SSR unknown binary RPC endpoint: {url}"
        let (ssrStatus, headMeta, rawHtml) ← app.ssrRenderNativeWithStatus docShell fc.title hostScript req.target ssrDispatchBytes (sessionUser := ctx.userId)
        let finalHtml := if !fc.devMode then rawHtml else (String.fromUTF8? rawHtml).elim rawHtml fun h => (h.replace "</body>" "<script type=\"module\" src=\"/qed_dev.mjs\"></script>\n</body>").toUTF8
        let redirectHdrs := if ssrStatus ∈ [301, 302, 303, 307, 308] then
          (headMeta.redirect.orElse fun _ => headMeta.canonical).elim [] fun loc => if isSafeUrl loc then [("Location", sanitizeHeader loc)] else [] else []
        return ← maybeGzipResponse ssrStatus "text/html; charset=utf-8" finalHtml isHead req.keepAlive false req.acceptsGzip true
          (extraHeaders := redirectHdrs ++ htmlSecHdrs ++ [("Vary", "Accept-Encoding")])
      else return textResp 404 "not found"

    let dispatchAppReq (req : ParsedReqHead) (body : ByteArray) (clientIp : String) : IO ByteArray :=
      dispatchAppReqWith req body clientIp (stripQuery req.target) (if req.method == "GET" || req.method == "HEAD" then classifyStaticPath req.method req.target fc.devMode else none)
    let hasBlockingMethods := fc.blockingMethods?.map (!·.isEmpty) |>.getD true
    let onParsedHead (req : ParsedReqHead) (clientIp pathOnly : String) (inline : Nat) : IO (Prim.HttpHeadAction ParsedReqHead RequestCtx) := do
      if fc.wsDispatchFn?.isSome && req.method == "GET" && pathOnly == wsPath && req.upgrade?.any (eqCI · "websocket") then
        if !req.isHttp11 || (req.conn?.map (containsCI · "upgrade") != some true) || req.wsVer? != some "13" then return .doneClose (formatErrorResponse 400 "invalid WebSocket upgrade headers")
        let some acceptB64 := req.wsKey?.bind wsComputeAccept | return .doneClose (formatErrorResponse 400 "invalid Sec-WebSocket-Key")
        match checkOriginAndFetchSite req cfg.wsAllowedOrigins? true "WebSocket upgrade" with
        | .error (code, msg) => return .doneClose (formatErrorResponse code msg)
        | .ok () =>
            if inline != 0 && oidcRt?.isSome && req.auth?.isSome then return .deferHead
            let baseCtx ← buildRequestCtxReq cfg req clientIp ByteArray.empty oidcRt?
            return .wsUpgrade (formatWsUpgradeResponse acceptB64) { baseCtx with connId := "ws-" ++ (← Prim.randomHex 12) }
      let isGetOrHead := req.method == "GET" || req.method == "HEAD"
      let staticTarget? := if isGetOrHead then classifyStaticPath req.method req.target fc.devMode else none
      if inline != 0 then
        let deferBody := if req.keepAlive then .deferBodyKeep req.contentLen req else .deferBodyClose req.contentLen req
        if let some st := staticTarget? then
          if !fc.devMode && !st.noStore && isContentHashedAsset st.relPath then
            if let some hit ← Prim.atomicRead assetCache (·[st.relPath]?) then return finishHeadWire req (hit.serve req st.isHead req.keepAlive)
          return deferBody
        if (oidcRt?.isSome && (pathOnly.startsWith "/_qed/auth/" || req.auth?.isSome)) || (fc.httpDispatchFn?.isSome && !pathOnly.startsWith "/_qed/") then return deferBody
        if hasBlockingMethods then
          if req.method == "POST" && pathOnly.startsWith rpcPrefix then
            if fc.blockingMethods?.map (·.contains (dropPrefixBytes pathOnly rpcPrefixBytes)) |>.getD true then return deferBody
          else if isGetOrHead && !pathOnly.startsWith "/_qed/" then return deferBody
      if req.contentLen == 0 then return finishHeadWire req (← dispatchAppReqWith req ByteArray.empty clientIp pathOnly staticTarget?)
      else return if req.keepAlive then .needBodyKeep req.contentLen req else .needBodyClose req.contentLen req
    let onWsBytes := fc.wsDispatchFn?.elim closedWsBytes fun fn ctx rx frag subs => stepWsRxLoop fn ctx rx 0 frag subs ByteArray.empty #[]
    let onWsLeave (ctx : RequestCtx) (ch : String) (params : ByteArray) : IO Unit := do if let some fn := fc.wsDispatchFn? then discard <| fn ctx 3 ch params ByteArray.empty
    let _ ← if fc.jobs.isEmpty then pure #[] else spawnServerJobs fc.jobs
    return (onParsedHead, dispatchAppReq, onWsBytes, onWsLeave, fc.wsProjectFn?)
private abbrev SrvHandlerM (σ : Type) (F : (Type → Type) → Type) := {m : Type → Type} → [Monad m] → [MonadServer m] → [MonadAtomic σ m] → F m

def runStatefulFullstack {σ Model Msg : Type} (app : Qed.App Model Msg) (title serverShortName : String) (initState : σ) (requiredSecrets : Array String)
    (dispatchM : SrvHandlerM σ fun m => RequestCtx → String → ByteArray → m (Except ApiError ByteArray)) (port : UInt16) (staticDir : String) (devMode : Bool := false) (numWorkers : UInt32 := 0)
    (wsDispatchM? : Option (SrvHandlerM σ fun m => RequestCtx → UInt8 → String → ByteArray → ByteArray → m (Except ApiError ByteArray)) := none) (blockingMethods? : Option (Array String) := none)
    (httpDispatchM? : Option (SrvHandlerM σ fun m => RequestCtx → String → String → m (Except ApiError (Option HttpResponse))) := none) (jobs : Array (ServerJob σ) := #[])
    (authSpec? : Option Qed.Auth.OidcAuthSpec := none) (authHookM? : Option (SrvHandlerM σ fun m => RequestCtx → UInt8 → m (Except ApiError Unit)) := none)
    (authHookFlags : Bool × Bool := (false, false)) (primaryDb? : Option Db.DbConfig := none)
    (wsProjectFn? : Option (RequestCtx → String → ByteArray → ByteArray → WsProjectOut) := none) : IO UInt32 := do
  let box ← Prim.mkStateBox initState; let gcpCache ← Prim.mkStateBox (#[] : Array GcpTokenCacheEntry); let dbCache ← mkDbResolveCache primaryDb?
  let gcpSsrfGuard := !devMode; let wsSrvInst := mkNativeServerInstWith (some gcpCache) none none (some dbCache) gcpSsrfGuard; let atomicInst := withStateBox box
  let withCookies {α : Type} (sseRef? : Option (IO.Ref (Array SseEvent)) := none) (f : MonadServer IO → IO α) : IO (α × Array SetCookie) := do
    let cRef ← IO.mkRef (#[] : Array SetCookie)
    return (← f (mkNativeServerInstWith (some gcpCache) (some cRef) sseRef? (some dbCache) gcpSsrfGuard), ← cRef.get)
  runFullstackCore app {
    title, serverShortName, requiredSecrets, port, staticDir, devMode, numWorkers, blockingMethods?, authSpec?, authHookFlags, primaryDb?, wsProjectFn?,
    dispatchFn := fun ctx mName reqBytes => withCookies none fun srv => @dispatchM IO _ srv atomicInst ctx mName reqBytes,
    wsDispatchFn? := wsDispatchM?.map fun wsM ctx kind ch params payload => @wsM IO _ wsSrvInst atomicInst ctx kind ch params payload,
    httpDispatchFn? := httpDispatchM?.map fun httpM ctx method path => do
      let sseRef ← IO.mkRef (#[] : Array SseEvent)
      let (res, cookies) ← withCookies (some sseRef) fun srv => @httpM IO _ srv atomicInst ctx method path
      let sseEvs ← sseRef.get
      return (match res with
        | .ok (some resp) => .ok (some (if !sseEvs.isEmpty && startsWithCI resp.contentType "text/event-stream" then { resp with body := SseEvent.formatStream sseEvs.toList } else resp))
        | other => other, cookies),
    jobs := jobs.map (·.toIoJob wsSrvInst atomicInst),
    authHookFn? := authHookM?.map fun hookM ctx kind => withCookies none fun srv => @hookM IO _ srv atomicInst ctx kind
  }

def parseServerCliArgs (args : List String) : IO (String × UInt16 × Bool × UInt32) := do
  let portStr ← match args[1]? with | some p => pure p | none => (·.getD "8000") <$> Prim.getEnv "PORT"
  let numWorkers := (((← Prim.getEnv "QED_WORKERS").bind String.toNat?).getD 0).toUInt32
  return (args[0]?.getD "dist", (portStr.toNat?.getD 8000).toUInt16, args.contains "--dev", numWorkers)
def runStandaloneApp {Model Msg : Type} (app : Qed.App Model Msg) (title : String) (args : List String) : IO UInt32 := do
  let (staticDir, port, devMode, numWorkers) ← parseServerCliArgs args
  runFullstackCore app { title, serverShortName := "_app", requiredSecrets := #[], port, staticDir, devMode, numWorkers,
                         dispatchFn := fun _ _ _ => pure (.error (ApiError.notFound "no RPC server configured"), #[]), blockingMethods? := some #[] }
def runStaticDir (staticDir : String) (port : UInt16) (devMode : Bool := false) : IO UInt32 :=
  serveHttpLoop staticDir port devMode 1 fun loop => do
    let dispatchReq (req : ParsedReqHead) (_ : ByteArray) (_ : String) : IO ByteArray := do
      let isHead := req.method == "HEAD"
      if req.method != "GET" && !isHead then return formatTextResponse 405 "method not allowed" isHead req.keepAlive
      if let some st := classifyStaticPath req.method req.target devMode then return ← serveStaticAsset loop.staticDirFd none req st devMode
      match ← Prim.readStaticFile loop.staticDirFd "index.html" (if isHead then 1 else 0) with
      | some (fsize, _, bytes) => maybeGzipResponse 200 "text/html; charset=utf-8" bytes isHead req.keepAlive true req.acceptsGzip true (extraHeaders := loop.htmlCspHdrs ++ [("Vary", "Accept-Encoding")]) (contentLen := fsize)
      | none => return formatTextResponse 404 "not found" isHead req.keepAlive
    return (fun req _ _ _ => finishHeadWire req <$> dispatchReq req ByteArray.empty "", dispatchReq, closedWsBytes, fun _ _ _ => pure (), none)
end Qed.Server.Native
