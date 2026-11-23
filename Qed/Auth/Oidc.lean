import Qed.Auth.Core
import Qed.Server.Core
import Qed.Server.Net
import Qed.Server.Http
import Qed.Server.Prim

namespace Qed.Auth.Oidc

open Qed.Auth
open Qed.Server
open Qed.Server.Net
open Qed.Server.Http

/-! ## Native OIDC / JWKS Verifier & Auth Code + PKCE (`S256`) BFF Runtime (`Qed.Auth.Oidc`)
    Server-only module (blocked from client JS bundles by `Js.VerifyEnv.clientLeakReason?`).
    Reuses Qed's verified outbound HTTP/1.1 client and `ring` RS256/ES256 JWK verification. -/

abbrev HttpExecFn :=
  String → String → Array (String × String) → ByteArray → Bool →
    IO (Except String (Nat × ByteArray × Array (String × String)))

structure OidcDiscovery where
  issuer                : String
  authorizationEndpoint : String
  tokenEndpoint         : String
  jwksUri               : String
  fetchedAtSec          : Nat
deriving Inhabited, Repr

structure OidcCacheState where
  discovery?      : Option OidcDiscovery := none
  jwks            : Array JwkKey := #[]
  jwksFetchedAt   : Nat := 0
  lastMissRefresh : Nat := 0
deriving Inhabited

structure ResolvedOidcConfig where
  name            : String
  issuer          : String
  audience        : String
  clientId        : String
  clientSecret?   : Option String := none
  sessionSecrets  : List String := []
  sessionTtlSec   : Nat := 86400
  loginPath       : String := "/_qed/auth/login"
  callbackPath    : String := "/_qed/auth/callback"
  logoutPath      : String := "/_qed/auth/logout"
  mePath          : String := "/_qed/auth/me"
  claimNames      : List String := []
  devMode         : Bool := false
deriving Inhabited, Repr

structure OidcRuntime where
  cfg   : ResolvedOidcConfig
  cache : Prim.StateBox OidcCacheState

private def isLocalDevIssuer (issuer : String) : Bool :=
  issuer.startsWith "http://127.0.0.1:" || issuer.startsWith "http://localhost:" ||
  issuer == "http://127.0.0.1" || issuer == "http://localhost"

def nowSec : IO Nat := return (← Prim.nowMs).toNat / 1000

private def ResolvedOidcConfig.ssrfGuard (cfg : ResolvedOidcConfig) : Bool :=
  !(cfg.devMode && isLocalDevIssuer cfg.issuer)

def loadNonEmptyEnv (envName : String) : IO (Option String) := do
  return (← Prim.getEnv envName).bind fun v => let t := trimWs v; if t.isEmpty then none else some t

private def resolveEnvWithDefault (envName : String) (default? : Option String) : IO (Option String) := do
  return (← loadNonEmptyEnv envName).orElse fun _ => default?

/-- Resolves an `OidcAuthSpec` from OS environment variables at server boot.
    In `devMode`, synthesizes an ephemeral CSPRNG cookie-signing key if `QED_AUTH_SECRET` is unset. -/
def initOidcRuntime (spec : OidcAuthSpec) (baseSecrets : List String) (devMode : Bool) :
    IO (Option OidcRuntime) := do
  let some rawIss ← resolveEnvWithDefault spec.issuerEnv spec.issuerDefault? | return none
  let issuer := stripTrailingSlashes (trimWs rawIss)
  if issuer.isEmpty then return none
  let audience := (← resolveEnvWithDefault spec.audienceEnv spec.audienceDefault?).getD spec.name
  let clientId := (← spec.clientIdEnv?.bindM fun e => resolveEnvWithDefault e spec.clientIdDefault?).orElse
    (fun _ => spec.clientIdDefault?) |>.getD audience
  let clientSecret? ← spec.clientSecretEnv?.bindM (resolveEnvWithDefault · none)
  let sessionSecrets ←
    if !baseSecrets.isEmpty then pure baseSecrets
    else if devMode then pure [← Prim.randomHex 32]
    else pure []
  return some {
    cfg := {
      name := spec.name, issuer, audience, clientId, clientSecret?, sessionSecrets
      sessionTtlSec := if spec.sessionTtlSec == 0 then 86400 else spec.sessionTtlSec
      loginPath := spec.loginPath, callbackPath := spec.callbackPath
      logoutPath := spec.logoutPath, mePath := spec.mePath
      claimNames := spec.claims.map (·.name), devMode
    }
    cache := ← Prim.mkStateBox ({} : OidcCacheState)
  }

/-! ### Cryptographic JWK Verification (`RS256` & `ES256` via `ring`) -/

def verifyJwkSignature (key : JwkKey) (signingInput : String) (sig : ByteArray) : IO Bool := do
  match key with
  | .rsa _ nBytes eBytes =>
      Prim.rsaJwkVerify nBytes eBytes signingInput.toUTF8 sig
  | .ecP256 _ xBytes yBytes =>
      Prim.ecP256JwkVerify xBytes yBytes signingInput.toUTF8 sig

private abbrev OidcM := ExceptT String IO

private def verifyParsedJwtWithKeys (cfg : OidcValidationCfg) (keys : Array JwkKey)
    (parsed : CompactJwt) (now : Nat) : OidcM (VerifiedClaims cfg now) := do
  let some key := findMatchingJwk keys parsed.header.alg parsed.header.kid?
    | throw "jwt: no matching signing key in JWKS"
  if !(← verifyJwkSignature key parsed.signingInput parsed.signature) then
    throw "jwt: invalid cryptographic signature"
  let claims ← liftP (parseJwtClaims parsed.payloadJson)
  liftP (validateJwtClaims cfg now parsed.header.alg claims)

/-- Verifies a compact JWT against an explicit set of JWK keys + strict `OidcValidationCfg`.
    Pure claim validation (`alg` allowlist, `iss`, `aud`, `exp`, `nbf`, `sub`, `nonce`) plus
    `ring` RS256/ES256 signature verification. -/
def verifyJwtWithKeys (cfg : OidcValidationCfg) (keys : Array JwkKey)
    (token : String) (now : Nat) : IO (Except String (VerifiedClaims cfg now)) :=
  ExceptT.run do
    verifyParsedJwtWithKeys cfg keys (← liftP (parseCompactJwt token)) now

/-! ### OIDC Discovery & JWKS Caching (with Safe Key-Rotation Refresh) -/

/-- Executes an outbound HTTP request and parses a 2xx UTF-8 JSON response body. -/
def execJsonHttp (httpExec : HttpExecFn) (method url : String)
    (headers : Array (String × String) := #[("Accept", "application/json")])
    (body : ByteArray := ByteArray.empty) (ssrfGuard : Bool := true)
    (label : String := s!"oidc endpoint `{url}`") : IO (Except String Json) := do
  match ← httpExec method url headers body ssrfGuard with
  | .error e => return .error s!"HTTP error calling {label}: {e}"
  | .ok (status, respBody, _) =>
      let some raw := String.fromUTF8? respBody
        | return .error s!"{label} returned non-UTF-8 body"
      if status < 200 || status >= 300 then
        let detail := if raw.isEmpty then "" else s!": {String.ofList (raw.toList.take 400)}"
        return .error s!"{label} returned HTTP {status}{detail}"
      return (Json.parse raw).mapError (s!"invalid JSON from {label}: {·}")

def fetchDiscovery (httpExec : HttpExecFn) (rt : OidcRuntime) (force : Bool := false) :
    IO (Except String OidcDiscovery) :=
  ExceptT.run do
    let now ← nowSec
    if !force then
      if let some cached ← liftIO (Prim.atomicRead rt.cache (·.discovery?)) then
        if now < cached.fetchedAtSec + 300 then return cached
    let j ← liftE (execJsonHttp httpExec "GET" (rt.cfg.issuer ++ "/.well-known/openid-configuration") (ssrfGuard := rt.cfg.ssrfGuard))
    let iss := (Db.jsonStrAt j "issuer").map (stripTrailingSlashes ∘ trimWs) |>.getD rt.cfg.issuer
    if iss != rt.cfg.issuer then
      throw s!"oidc discovery issuer mismatch: expected `{rt.cfg.issuer}`, got `{iss}`"
    let some jwksUri := Db.jsonStrAt j "jwks_uri"
      | throw "oidc discovery missing `jwks_uri`"
    let disc : OidcDiscovery := {
      issuer := iss
      authorizationEndpoint := (Db.jsonStrAt j "authorization_endpoint").getD (rt.cfg.issuer ++ "/authorize")
      tokenEndpoint := (Db.jsonStrAt j "token_endpoint").getD (rt.cfg.issuer ++ "/token")
      jwksUri
      fetchedAtSec := now
    }
    liftIO (Prim.atomicModify rt.cache fun st => ({ st with discovery? := some disc }, ()))
    return disc

def fetchJwks (httpExec : HttpExecFn) (rt : OidcRuntime) (force : Bool := false) :
    IO (Except String (Array JwkKey)) :=
  ExceptT.run do
    let now ← nowSec
    if !force then
      let (keys, fetchedAt) ← liftIO (Prim.atomicRead rt.cache fun st => (st.jwks, st.jwksFetchedAt))
      if !keys.isEmpty && now < fetchedAt + 300 then return keys
    let disc ← liftE (fetchDiscovery httpExec rt force)
    let j ← liftE (execJsonHttp httpExec "GET" disc.jwksUri (ssrfGuard := rt.cfg.ssrfGuard))
    let keys := parseJwks j
    if keys.isEmpty then
      throw "oidc JWKS contained no supported RS256/ES256 signing keys"
    liftIO (Prim.atomicModify rt.cache fun st =>
      ({ st with jwks := keys, jwksFetchedAt := now, lastMissRefresh := if force then now else st.lastMissRefresh }, ()))
    return keys

/-- Verifies a Bearer/ID JWT against the runtime's OIDC issuer + JWKS cache, performing at most
    one rate-limited cache refresh on an unknown `kid` (supporting zero-downtime key rotation). -/
def verifyOidcJwt (httpExec : HttpExecFn) (rt : OidcRuntime) (token : String)
    (expectedNonce? : Option String := none) : IO (Except String JwtClaims) :=
  ExceptT.run do
    let parsed ← liftP (parseCompactJwt token)
    let keys0 ← liftE (fetchJwks httpExec rt false)
    let now ← nowSec
    let keys ←
      match findMatchingJwk keys0 parsed.header.alg parsed.header.kid? with
      | some _ => pure keys0
      | none =>
          if now >= (← liftIO (Prim.atomicRead rt.cache (·.lastMissRefresh))) + 10 then
            match ← liftIO (fetchJwks httpExec rt true) with
            | .ok ks2  => pure ks2
            | .error _ => pure keys0
          else pure keys0
    let vcfg : OidcValidationCfg := {
      issuer := rt.cfg.issuer, audience := rt.cfg.audience, clockSkewSec := 60, expectedNonce?
    }
    let vc ← verifyParsedJwtWithKeys vcfg keys parsed now
    return vc.claims

/-! ### Signed `v2` Session Cookie & Short-Lived PKCE Transaction Cookie -/

def anySecretVerify (secrets : List String) (payload sigBytes : ByteArray) : IO Bool := do
  for sec in secrets do
    if ← Prim.hmacSha256Verify sec.toUTF8 payload sigBytes then
      return true
  return false

private def signHmacEnvelope (secret tag : String) (expSec : Nat) (b64 : String) : IO String := do
  let body := s!"{tag}.{expSec}.{b64}"
  let mac ← Prim.hmacSha256 secret.toUTF8 body.toUTF8
  return s!"{body}.{Proto.encodeHex mac}"

private def verifyHmacEnvelope (secrets : List String) (tag raw : String) (nowSec : Nat) :
    IO (Option String) := do
  if secrets.isEmpty then return none
  match raw.splitOn "." with
  | [t, expStr, b64, sigHex] =>
      if t != tag || sigHex.length != 64 then return none
      let some expSec := parseStrictU64 expStr 18446744073709551615 | return none
      if nowSec >= expSec then return none
      let .ok sigBytes := Proto.decodeHex sigHex | return none
      let body := s!"{tag}.{expStr}.{b64}"
      if !(← anySecretVerify secrets body.toUTF8 sigBytes) then return none
      return some b64
  | _ => return none

/-- Mints an expiring `v2.<expSec>.<b64urlPayload>.<hmacHex>` session cookie carrying verified claims. -/
def signSessionCookieV2 (secret : String) (payload : SessionPayloadV2) (ttlSec : Nat := 86400) :
    IO String := do
  signHmacEnvelope secret "v2" ((← nowSec) + ttlSec) (encodeSessionPayloadV2 payload)

/-- Verifies a `v2.<expSec>.<b64urlPayload>.<hmacHex>` cookie in constant time across active/rotated secrets. -/
def verifySessionCookieV2 (secrets : List String) (token : String) (nowSec : Nat) :
    IO (Option SessionPayloadV2) := do
  let some b64 ← verifyHmacEnvelope secrets "v2" token nowSec | return none
  return (decodeSessionPayloadV2 b64).toOption

private structure AuthTxCookie where
  state        : String
  nonce        : String
  codeVerifier : String
  returnTo     : String
  redirectUri  : String

private def signAuthTxCookie (secret : String) (tx : AuthTxCookie) (nowSec : Nat) : IO String := do
  let j := Json.obj [
    ("state", .str tx.state), ("nonce", .str tx.nonce), ("verifier", .str tx.codeVerifier),
    ("returnTo", .str tx.returnTo), ("redirectUri", .str tx.redirectUri)
  ]
  signHmacEnvelope secret "tx1" (nowSec + 600) (base64UrlEncode (Json.render j).toUTF8)

private def verifyAuthTxCookie (secrets : List String) (raw : String) (nowSec : Nat) :
    IO (Option AuthTxCookie) := do
  let some b64 ← verifyHmacEnvelope secrets "tx1" raw nowSec | return none
  let .ok bs := base64UrlDecode b64 | return none
  let some js := String.fromUTF8? bs | return none
  let .ok j := Json.parse js | return none
  let some state := Db.jsonStrAt j "state" | return none
  let some nonce := Db.jsonStrAt j "nonce" | return none
  let some verifier := Db.jsonStrAt j "verifier" | return none
  let returnTo := sanitizeReturnTo (Db.jsonStrAt j "returnTo")
  let some redirectUri := Db.jsonStrAt j "redirectUri" | return none
  return some { state, nonce, codeVerifier := verifier, returnTo, redirectUri }

private def mkHardenedCookie (name value : String) (maxAge : Nat) (devMode : Bool) : SetCookie :=
  { name, value, path := "/", maxAge? := some maxAge, httpOnly := true, secure := !devMode, sameSite := .lax }

private def inferOriginFromReq (req : ParsedReqHead) (devMode : Bool) : String :=
  let host := (req.host?.map trimWs).getD "127.0.0.1:8000"
  let isLocal := host.startsWith "127.0.0.1" || host.startsWith "localhost"
  let scheme := if devMode || isLocal then "http" else "https"
  s!"{scheme}://{host}"

private def filterSessionClaims (claimNames : List String) (c : JwtClaims) : List (String × String) :=
  let base := c.flatClaims.filter fun (k, _) =>
    k == "email" || k == "email_verified" || k == "name" || claimNames.contains k
  let withEmail := match c.email? with
    | some e => if base.any (·.1 == "email") then base else base ++ [("email", e)]
    | none   => base
  let withVer := if withEmail.any (·.1 == "email_verified") then withEmail
    else withEmail ++ [("email_verified", if c.emailVerified then "true" else "false")]
  withVer

/-! ### Built-In OIDC Auth Endpoints (`/_qed/auth/login`, `/callback`, `/logout`, `/me`) -/

/-- Handles `/_qed/auth/login`, `/_qed/auth/callback`, `/_qed/auth/logout`, and `/_qed/auth/me`.
    Returns `some wireResponse` if the path matched an auth route, or `none` otherwise. -/
def handleAuthRoute (httpExec : HttpExecFn) (rt : OidcRuntime) (req : ParsedReqHead)
    (pathOnly queryStr : String) (cookies : List (String × String))
    (resolvedUser? : Option String) (resolvedClaims : List (String × String))
    (isHead : Bool)
    (onCallbackAuthenticated? : Option (String → List (String × String) → IO (Except (Nat × String) (Array SetCookie))) := none) :
    IO (Option ByteArray) := do
  let cfg := rt.cfg
  let redirectResp (loc : String) (hdrs : List (String × String)) : ByteArray :=
    formatHttpResponse 302 "text/plain; charset=utf-8" ByteArray.empty isHead req.keepAlive true
      (extraHeaders := ("Location", loc) :: hdrs)
  let runRoute (m : ExceptT (Nat × String) IO ByteArray) : IO (Option ByteArray) := do
    match ← m.run with
    | .ok resp          => return some resp
    | .error (st, msg)  => return some (formatTextResponse st msg isHead req.keepAlive)
  let requireSignKey : ExceptT (Nat × String) IO String :=
    match cfg.sessionSecrets.head? with
    | some k => pure k
    | none   => throw (500, "auth error: QED_AUTH_SECRET is not configured")
  let liftErr {α : Type} (st : Nat) (x : IO (Except String α)) (fmt : String → String := id) :
      ExceptT (Nat × String) IO α :=
    ExceptT.mk ((·.mapError fun e => (st, fmt e)) <$> x)
  let setCookieHdrs (cs : List SetCookie) : List (String × String) := cs.map fun c => ("Set-Cookie", c.render)
  let fetchDiscOr502 := liftErr 502 (fetchDiscovery httpExec rt false)
  if req.method == "GET" && pathOnly == cfg.loginPath then
    runRoute do
      let signKey ← requireSignKey
      let disc ← fetchDiscOr502
      let returnTo := sanitizeReturnTo ((parseQueryParams queryStr).lookup "returnTo")
      let state ← Prim.randomHex 24
      let nonce ← Prim.randomHex 24
      let codeVerifier ← Prim.randomHex 32
      let codeChallenge := base64UrlEncode (← Prim.sha256 codeVerifier.toUTF8)
      let redirectUri := inferOriginFromReq req cfg.devMode ++ cfg.callbackPath
      let txVal ← signAuthTxCookie signKey { state, nonce, codeVerifier, returnTo, redirectUri } (← nowSec)
      let txCookie := mkHardenedCookie "qed_auth_tx" txVal 600 cfg.devMode
      let authQuery := encodeFormBody [
        ("response_type", "code"), ("client_id", cfg.clientId), ("redirect_uri", redirectUri),
        ("scope", "openid email profile"), ("state", state), ("nonce", nonce),
        ("code_challenge", codeChallenge), ("code_challenge_method", "S256")
      ]
      let sep := if disc.authorizationEndpoint.contains "?" then "&" else "?"
      return redirectResp (sanitizeHeader (disc.authorizationEndpoint ++ sep ++ authQuery)) (setCookieHdrs [txCookie])

  else if req.method == "GET" && pathOnly == cfg.callbackPath then
    runRoute do
      let signKey ← requireSignKey
      let qParams := parseQueryParams queryStr
      let some code := qParams.lookup "code" | throw (400, "auth callback missing `code`")
      let some state := qParams.lookup "state" | throw (400, "auth callback missing `state`")
      let some rawTx := cookies.lookup "qed_auth_tx" | throw (400, "auth callback missing transaction cookie")
      let some tx ← verifyAuthTxCookie cfg.sessionSecrets rawTx (← nowSec)
        | throw (400, "auth callback invalid or expired transaction cookie")
      if state != tx.state then throw (403, "auth callback state mismatch")
      let disc ← fetchDiscOr502
      let formPairsBase := [
        ("grant_type", "authorization_code"), ("code", code), ("redirect_uri", tx.redirectUri),
        ("client_id", cfg.clientId), ("code_verifier", tx.codeVerifier)
      ]
      let formPairs := match cfg.clientSecret? with
        | some cs => formPairsBase ++ [("client_secret", cs)]
        | none    => formPairsBase
      let tokJson ← liftErr 502 (execJsonHttp httpExec "POST" disc.tokenEndpoint
        #[("Content-Type", "application/x-www-form-urlencoded"), ("Accept", "application/json")]
        (encodeFormBody formPairs).toUTF8 cfg.ssrfGuard "oidc token endpoint")
      let some idToken := Db.jsonStrAt tokJson "id_token"
        | throw (502, "oidc token response missing `id_token`")
      let claims ← liftErr 401 (verifyOidcJwt httpExec rt idToken (expectedNonce? := some tx.nonce))
        (s!"oidc id_token verification failed: {·}")
      let sessPayload : SessionPayloadV2 := {
        userId := claims.sub
        claims := filterSessionClaims cfg.claimNames claims
      }
      let extraHookCookies ← match onCallbackAuthenticated? with
        | some onAuth => setCookieHdrs <$> Array.toList <$> ExceptT.mk (onAuth sessPayload.userId sessPayload.claims)
        | none => pure []
      let sessTok ← signSessionCookieV2 signKey sessPayload cfg.sessionTtlSec
      let sessCookie := mkHardenedCookie "qed_session" sessTok cfg.sessionTtlSec cfg.devMode
      let hdrs := setCookieHdrs [SetCookie.clear "qed_auth_tx" "/", sessCookie] ++ extraHookCookies
      return redirectResp (sanitizeReturnTo (some tx.returnTo)) hdrs

  else if (req.method == "POST" || req.method == "GET") && pathOnly == cfg.logoutPath then
    let hdrs := setCookieHdrs [SetCookie.clear "qed_session" "/", SetCookie.clear "qed_auth_tx" "/"]
    match (parseQueryParams queryStr).lookup "returnTo" with
    | some rawRt => return some (redirectResp (sanitizeReturnTo (some rawRt)) hdrs)
    | none => return some (formatHttpResponse 200 "application/json" "{\"ok\":true}".toUTF8 isHead req.keepAlive true (extraHeaders := hdrs))

  else if (req.method == "GET" || isHead) && pathOnly == cfg.mePath then
    match resolvedUser? with
    | some uid =>
        let claimsObj := Json.obj (resolvedClaims.map fun (k, v) => (k, Json.str v))
        let body := Json.render (Json.obj [
          ("authenticated", .bool true), ("id", .str uid), ("claims", claimsObj)
        ])
        return some (formatHttpResponse 200 "application/json" body.toUTF8 isHead req.keepAlive true)
    | none =>
        return some (formatHttpResponse 401 "application/json" "{\"authenticated\":false}".toUTF8 isHead req.keepAlive true)

  else
    return none

end Qed.Auth.Oidc
