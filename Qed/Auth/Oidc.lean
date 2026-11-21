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

private def trimStr (s : String) : String :=
  s.trimAscii.toString

private def stripTrailingSlash (s : String) : String :=
  let t := trimStr s
  if t.endsWith "/" && t.length > 1 then
    String.ofList (t.toList.dropLast)
  else t

private def isLocalDevIssuer (issuer : String) : Bool :=
  issuer.startsWith "http://127.0.0.1:" || issuer.startsWith "http://localhost:" ||
  issuer == "http://127.0.0.1" || issuer == "http://localhost"

private def resolveEnvWithDefault (envName : String) (default? : Option String) : IO (Option String) := do
  match ← Prim.getEnv envName with
  | some v =>
      let t := trimStr v
      if !t.isEmpty then return some t
      else return default?
  | none => return default?

/-- Resolves an `OidcAuthSpec` from OS environment variables at server boot.
    In `devMode`, synthesizes an ephemeral CSPRNG cookie-signing key if `QED_AUTH_SECRET` is unset. -/
def initOidcRuntime (spec : OidcAuthSpec) (baseSecrets : List String) (devMode : Bool) :
    IO (Option OidcRuntime) := do
  let some rawIss ← resolveEnvWithDefault spec.issuerEnv spec.issuerDefault?
    | return none
  let issuer := stripTrailingSlash rawIss
  if issuer.isEmpty then return none
  let audience := (← resolveEnvWithDefault spec.audienceEnv spec.audienceDefault?).getD spec.name
  let clientId ← match spec.clientIdEnv? with
    | some envName => do pure ((← resolveEnvWithDefault envName spec.clientIdDefault?).getD audience)
    | none         => pure (spec.clientIdDefault?.getD audience)
  let clientSecret? ← match spec.clientSecretEnv? with
    | some envName => resolveEnvWithDefault envName none
    | none         => pure none
  let sessionSecrets ←
    if !baseSecrets.isEmpty then pure baseSecrets
    else if devMode then
      let eph ← Prim.randomHex 32
      pure [eph]
    else pure []
  let cache ← Prim.mkStateBox ({} : OidcCacheState)
  return some {
    cfg := {
      name := spec.name
      issuer
      audience
      clientId
      clientSecret?
      sessionSecrets
      sessionTtlSec := if spec.sessionTtlSec == 0 then 86400 else spec.sessionTtlSec
      loginPath := spec.loginPath
      callbackPath := spec.callbackPath
      logoutPath := spec.logoutPath
      mePath := spec.mePath
      claimNames := spec.claims.map (·.name)
      devMode
    }
    cache
  }

/-! ### Cryptographic JWK Verification (`RS256` & `ES256` via `ring`) -/

def verifyJwkSignature (key : JwkKey) (signingInput : String) (sig : ByteArray) : IO Bool := do
  match key with
  | .rsa _ nBytes eBytes =>
      Prim.rsaJwkVerify nBytes eBytes signingInput.toUTF8 sig
  | .ecP256 _ xBytes yBytes =>
      Prim.ecP256JwkVerify xBytes yBytes signingInput.toUTF8 sig

/-- Verifies a compact JWT against an explicit set of JWK keys + strict `OidcValidationCfg`.
    Pure claim validation (`alg` allowlist, `iss`, `aud`, `exp`, `nbf`, `sub`, `nonce`) plus
    `ring` RS256/ES256 signature verification. -/
def verifyJwtWithKeys (cfg : OidcValidationCfg) (keys : Array JwkKey)
    (token : String) (nowSec : Nat) : IO (Except String (VerifiedClaims cfg nowSec)) := do
  let parsed ← match parseCompactJwt token with
    | .ok p    => pure p
    | .error e => return .error e
  let some key := findMatchingJwk keys parsed.header.alg parsed.header.kid?
    | return .error "jwt: no matching signing key in JWKS"
  let sigOk ← verifyJwkSignature key parsed.signingInput parsed.signature
  if !sigOk then
    return .error "jwt: invalid cryptographic signature"
  let claims ← match parseJwtClaims parsed.payloadJson with
    | .ok c    => pure c
    | .error e => return .error e
  return validateJwtClaims cfg nowSec parsed.header.alg claims

/-! ### OIDC Discovery & JWKS Caching (with Safe Key-Rotation Refresh) -/

private def fetchJsonUrl (httpExec : HttpExecFn) (url : String) (ssrfGuard : Bool) :
    IO (Except String Json) := do
  match ← httpExec "GET" url #[("Accept", "application/json")] ByteArray.empty ssrfGuard with
  | .error e => return .error s!"oidc HTTP error fetching `{url}`: {e}"
  | .ok (status, body, _) =>
      if status < 200 || status >= 300 then
        return .error s!"oidc endpoint `{url}` returned HTTP {status}"
      let some raw := String.fromUTF8? body
        | return .error s!"oidc endpoint `{url}` returned non-UTF-8 body"
      return Json.parse raw

def fetchDiscovery (httpExec : HttpExecFn) (rt : OidcRuntime) (force : Bool := false) :
    IO (Except String OidcDiscovery) := do
  let nowSec := ((← Prim.nowMs).toNat) / 1000
  if !force then
    if let some cached ← Prim.atomicRead rt.cache (·.discovery?) then
      if nowSec < cached.fetchedAtSec + 300 then
        return .ok cached
  let discUrl := rt.cfg.issuer ++ "/.well-known/openid-configuration"
  let ssrfGuard := !(rt.cfg.devMode && isLocalDevIssuer rt.cfg.issuer)
  let j ← match ← fetchJsonUrl httpExec discUrl ssrfGuard with
    | .ok v    => pure v
    | .error e => return .error e
  let iss := ((j.get? "issuer").bind (·.str?)).map stripTrailingSlash |>.getD rt.cfg.issuer
  if iss != rt.cfg.issuer then
    return .error s!"oidc discovery issuer mismatch: expected `{rt.cfg.issuer}`, got `{iss}`"
  let some jwksUri := (j.get? "jwks_uri").bind (·.str?)
    | return .error "oidc discovery missing `jwks_uri`"
  let authEp := ((j.get? "authorization_endpoint").bind (·.str?)).getD (rt.cfg.issuer ++ "/authorize")
  let tokEp  := ((j.get? "token_endpoint").bind (·.str?)).getD (rt.cfg.issuer ++ "/token")
  let disc : OidcDiscovery := {
    issuer := iss
    authorizationEndpoint := authEp
    tokenEndpoint := tokEp
    jwksUri
    fetchedAtSec := nowSec
  }
  Prim.atomicModify rt.cache fun st => ({ st with discovery? := some disc }, ())
  return .ok disc

def fetchJwks (httpExec : HttpExecFn) (rt : OidcRuntime) (force : Bool := false) :
    IO (Except String (Array JwkKey)) := do
  let nowSec := ((← Prim.nowMs).toNat) / 1000
  if !force then
    let (keys, fetchedAt) ← Prim.atomicRead rt.cache fun st => (st.jwks, st.jwksFetchedAt)
    if !keys.isEmpty && nowSec < fetchedAt + 300 then
      return .ok keys
  let disc ← match ← fetchDiscovery httpExec rt force with
    | .ok d    => pure d
    | .error e => return .error e
  let ssrfGuard := !(rt.cfg.devMode && isLocalDevIssuer rt.cfg.issuer)
  let j ← match ← fetchJsonUrl httpExec disc.jwksUri ssrfGuard with
    | .ok v    => pure v
    | .error e => return .error e
  let keys := parseJwks j
  if keys.isEmpty then
    return .error "oidc JWKS contained no supported RS256/ES256 signing keys"
  Prim.atomicModify rt.cache fun st =>
    ({ st with jwks := keys, jwksFetchedAt := nowSec, lastMissRefresh := if force then nowSec else st.lastMissRefresh }, ())
  return .ok keys

/-- Verifies a Bearer/ID JWT against the runtime's OIDC issuer + JWKS cache, performing at most
    one rate-limited cache refresh on an unknown `kid` (supporting zero-downtime key rotation). -/
def verifyOidcJwt (httpExec : HttpExecFn) (rt : OidcRuntime) (token : String)
    (expectedNonce? : Option String := none) : IO (Except String JwtClaims) := do
  let parsed ← match parseCompactJwt token with
    | .ok p    => pure p
    | .error e => return .error e
  let keys0 ← match ← fetchJwks httpExec rt false with
    | .ok ks   => pure ks
    | .error e => return .error e
  let nowSec := ((← Prim.nowMs).toNat) / 1000
  let keys ←
    match findMatchingJwk keys0 parsed.header.alg parsed.header.kid? with
    | some _ => pure keys0
    | none =>
        let lastRefresh ← Prim.atomicRead rt.cache (·.lastMissRefresh)
        if nowSec >= lastRefresh + 10 then
          match ← fetchJwks httpExec rt true with
          | .ok ks2 => pure ks2
          | .error _ => pure keys0
        else
          pure keys0
  let vcfg : OidcValidationCfg := {
    issuer := rt.cfg.issuer
    audience := rt.cfg.audience
    clockSkewSec := 60
    expectedNonce? := expectedNonce?
  }
  match ← verifyJwtWithKeys vcfg keys token nowSec with
  | .ok vc   => return .ok vc.claims
  | .error e => return .error e

/-! ### Signed `v2` Session Cookie & Short-Lived PKCE Transaction Cookie -/

private def anySecretVerify (secrets : List String) (payload sigBytes : ByteArray) : IO Bool := do
  for sec in secrets do
    if ← Prim.hmacSha256Verify sec.toUTF8 payload sigBytes then
      return true
  return false

private def parseNatStrict (s : String) : Option Nat :=
  if s.isEmpty || s.length > 20 then none
  else if s.toList.all fun c => '0' ≤ c && c ≤ '9' then s.toNat?
  else none

/-- Mints an expiring `v2.<expSec>.<b64urlPayload>.<hmacHex>` session cookie carrying verified claims. -/
def signSessionCookieV2 (secret : String) (payload : SessionPayloadV2) (ttlSec : Nat := 86400) :
    IO String := do
  let nowSec := ((← Prim.nowMs).toNat) / 1000
  let expSec := nowSec + ttlSec
  let b64 := encodeSessionPayloadV2 payload
  let body := s!"v2.{expSec}.{b64}"
  let mac ← Prim.hmacSha256 secret.toUTF8 body.toUTF8
  return s!"{body}.{Proto.encodeHex mac}"

/-- Verifies a `v2.<expSec>.<b64urlPayload>.<hmacHex>` cookie in constant time across active/rotated secrets. -/
def verifySessionCookieV2 (secrets : List String) (token : String) (nowSec : Nat) :
    IO (Option SessionPayloadV2) := do
  if secrets.isEmpty then return none
  match token.splitOn "." with
  | ["v2", expStr, b64, sigHex] =>
      if sigHex.length != 64 then return none
      let some expSec := parseNatStrict expStr | return none
      if nowSec >= expSec then return none
      let sigBytes ← match Proto.decodeHex sigHex with
        | .ok b    => pure b
        | .error _ => return none
      let body := s!"v2.{expStr}.{b64}"
      if !(← anySecretVerify secrets body.toUTF8 sigBytes) then
        return none
      match decodeSessionPayloadV2 b64 with
      | .ok p    => return some p
      | .error _ => return none
  | _ => return none

private structure AuthTxCookie where
  state        : String
  nonce        : String
  codeVerifier : String
  returnTo     : String
  redirectUri  : String

private def signAuthTxCookie (secret : String) (tx : AuthTxCookie) (nowSec : Nat) : IO String := do
  let expSec := nowSec + 600
  let j := Json.obj [
    ("state", .str tx.state),
    ("nonce", .str tx.nonce),
    ("verifier", .str tx.codeVerifier),
    ("returnTo", .str tx.returnTo),
    ("redirectUri", .str tx.redirectUri)
  ]
  let b64 := base64UrlEncode (Json.render j).toUTF8
  let body := s!"tx1.{expSec}.{b64}"
  let mac ← Prim.hmacSha256 secret.toUTF8 body.toUTF8
  return s!"{body}.{Proto.encodeHex mac}"

private def verifyAuthTxCookie (secrets : List String) (raw : String) (nowSec : Nat) :
    IO (Option AuthTxCookie) := do
  if secrets.isEmpty then return none
  match raw.splitOn "." with
  | ["tx1", expStr, b64, sigHex] =>
      if sigHex.length != 64 then return none
      let some expSec := parseNatStrict expStr | return none
      if nowSec >= expSec then return none
      let sigBytes ← match Proto.decodeHex sigHex with
        | .ok b    => pure b
        | .error _ => return none
      let body := s!"tx1.{expStr}.{b64}"
      if !(← anySecretVerify secrets body.toUTF8 sigBytes) then return none
      let bs ← match base64UrlDecode b64 with
        | .ok b    => pure b
        | .error _ => return none
      let some js := String.fromUTF8? bs | return none
      let j ← match Json.parse js with
        | .ok v    => pure v
        | .error _ => return none
      let some state := (j.get? "state").bind (·.str?) | return none
      let some nonce := (j.get? "nonce").bind (·.str?) | return none
      let some verifier := (j.get? "verifier").bind (·.str?) | return none
      let returnTo := sanitizeReturnTo ((j.get? "returnTo").bind (·.str?))
      let some redirectUri := (j.get? "redirectUri").bind (·.str?) | return none
      return some { state, nonce, codeVerifier := verifier, returnTo, redirectUri }
  | _ => return none

private def mkHardenedCookie (name value : String) (maxAge : Nat) (devMode : Bool) : SetCookie :=
  {
    name
    value
    path := "/"
    maxAge? := some maxAge
    httpOnly := true
    secure := !devMode
    sameSite := .lax
  }

private def inferOriginFromReq (req : ParsedReqHead) (devMode : Bool) : String :=
  let host := (req.host?.map trimStr).getD "127.0.0.1:8000"
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
    (isHead : Bool) : IO (Option ByteArray) := do
  let cfg := rt.cfg
  if req.method == "GET" && pathOnly == cfg.loginPath then
    let some signKey := cfg.sessionSecrets.head?
      | return some (formatHttpResponse 500 "text/plain; charset=utf-8"
          "auth error: QED_AUTH_SECRET is not configured".toUTF8 isHead req.keepAlive false)
    let disc ← match ← fetchDiscovery httpExec rt false with
      | .ok d => pure d
      | .error e =>
          return some (formatHttpResponse 502 "text/plain; charset=utf-8" e.toUTF8 isHead req.keepAlive false)
    let qParams := parseQueryParams queryStr
    let returnTo := sanitizeReturnTo ((qParams.find? (·.1 == "returnTo")).map Prod.snd)
    let state ← Prim.randomHex 24
    let nonce ← Prim.randomHex 24
    let codeVerifier ← Prim.randomHex 32
    let challengeHash ← Prim.sha256 codeVerifier.toUTF8
    let codeChallenge := base64UrlEncode challengeHash
    let redirectUri := inferOriginFromReq req cfg.devMode ++ cfg.callbackPath
    let nowSec := ((← Prim.nowMs).toNat) / 1000
    let txVal ← signAuthTxCookie signKey { state, nonce, codeVerifier, returnTo, redirectUri } nowSec
    let txCookie := mkHardenedCookie "qed_auth_tx" txVal 600 cfg.devMode
    let authQuery := encodeFormBody [
      ("response_type", "code"),
      ("client_id", cfg.clientId),
      ("redirect_uri", redirectUri),
      ("scope", "openid email profile"),
      ("state", state),
      ("nonce", nonce),
      ("code_challenge", codeChallenge),
      ("code_challenge_method", "S256")
    ]
    let sep := if disc.authorizationEndpoint.contains "?" then "&" else "?"
    let loc := disc.authorizationEndpoint ++ sep ++ authQuery
    let hdrs := [("Location", sanitizeHeader loc), ("Set-Cookie", txCookie.render)]
    return some (formatHttpResponse 302 "text/plain; charset=utf-8" ByteArray.empty isHead req.keepAlive true (extraHeaders := hdrs))

  else if req.method == "GET" && pathOnly == cfg.callbackPath then
    let some signKey := cfg.sessionSecrets.head?
      | return some (formatHttpResponse 500 "text/plain; charset=utf-8"
          "auth error: QED_AUTH_SECRET is not configured".toUTF8 isHead req.keepAlive false)
    let qParams := parseQueryParams queryStr
    let some code := (qParams.find? (·.1 == "code")).map Prod.snd
      | return some (formatHttpResponse 400 "text/plain; charset=utf-8"
          "auth callback missing `code`".toUTF8 isHead req.keepAlive false)
    let some state := (qParams.find? (·.1 == "state")).map Prod.snd
      | return some (formatHttpResponse 400 "text/plain; charset=utf-8"
          "auth callback missing `state`".toUTF8 isHead req.keepAlive false)
    let some rawTx := (cookies.find? (·.1 == "qed_auth_tx")).map Prod.snd
      | return some (formatHttpResponse 400 "text/plain; charset=utf-8"
          "auth callback missing transaction cookie".toUTF8 isHead req.keepAlive false)
    let nowSec := ((← Prim.nowMs).toNat) / 1000
    let some tx ← verifyAuthTxCookie cfg.sessionSecrets rawTx nowSec
      | return some (formatHttpResponse 400 "text/plain; charset=utf-8"
          "auth callback invalid or expired transaction cookie".toUTF8 isHead req.keepAlive false)
    if state != tx.state then
      return some (formatHttpResponse 403 "text/plain; charset=utf-8"
        "auth callback state mismatch".toUTF8 isHead req.keepAlive false)
    let disc ← match ← fetchDiscovery httpExec rt false with
      | .ok d => pure d
      | .error e =>
          return some (formatHttpResponse 502 "text/plain; charset=utf-8" e.toUTF8 isHead req.keepAlive false)
    let formPairsBase := [
      ("grant_type", "authorization_code"),
      ("code", code),
      ("redirect_uri", tx.redirectUri),
      ("client_id", cfg.clientId),
      ("code_verifier", tx.codeVerifier)
    ]
    let formPairs := match cfg.clientSecret? with
      | some cs => formPairsBase ++ [("client_secret", cs)]
      | none    => formPairsBase
    let formBody := encodeFormBody formPairs
    let ssrfGuard := !(cfg.devMode && isLocalDevIssuer cfg.issuer)
    let tokRes ← httpExec "POST" disc.tokenEndpoint
      #[("Content-Type", "application/x-www-form-urlencoded"), ("Accept", "application/json")]
      formBody.toUTF8 ssrfGuard
    let tokJson ← match tokRes with
      | .error e =>
          return some (formatHttpResponse 502 "text/plain; charset=utf-8"
            s!"oidc token exchange failed: {e}".toUTF8 isHead req.keepAlive false)
      | .ok (st, body, _) =>
          if st < 200 || st >= 300 then
            return some (formatHttpResponse 502 "text/plain; charset=utf-8"
              s!"oidc token endpoint returned HTTP {st}".toUTF8 isHead req.keepAlive false)
          match (String.fromUTF8? body).bind (fun s => (Json.parse s).toOption) with
          | some j => pure j
          | none   =>
              return some (formatHttpResponse 502 "text/plain; charset=utf-8"
                "oidc token endpoint returned invalid JSON".toUTF8 isHead req.keepAlive false)
    let some idToken := (tokJson.get? "id_token").bind (·.str?)
      | return some (formatHttpResponse 502 "text/plain; charset=utf-8"
          "oidc token response missing `id_token`".toUTF8 isHead req.keepAlive false)
    let claims ← match ← verifyOidcJwt httpExec rt idToken (expectedNonce? := some tx.nonce) with
      | .ok c => pure c
      | .error e =>
          return some (formatHttpResponse 401 "text/plain; charset=utf-8"
            s!"oidc id_token verification failed: {e}".toUTF8 isHead req.keepAlive false)
    let sessPayload : SessionPayloadV2 := {
      userId := claims.sub
      claims := filterSessionClaims cfg.claimNames claims
    }
    let sessTok ← signSessionCookieV2 signKey sessPayload cfg.sessionTtlSec
    let sessCookie := mkHardenedCookie "qed_session" sessTok cfg.sessionTtlSec cfg.devMode
    let clearTx := SetCookie.clear "qed_auth_tx" "/"
    let safeLoc := sanitizeReturnTo (some tx.returnTo)
    let hdrs := [
      ("Location", safeLoc),
      ("Set-Cookie", clearTx.render),
      ("Set-Cookie", sessCookie.render)
    ]
    return some (formatHttpResponse 302 "text/plain; charset=utf-8" ByteArray.empty isHead req.keepAlive true (extraHeaders := hdrs))

  else if (req.method == "POST" || req.method == "GET") && pathOnly == cfg.logoutPath then
    let clearSess := SetCookie.clear "qed_session" "/"
    let clearTx := SetCookie.clear "qed_auth_tx" "/"
    let qParams := parseQueryParams queryStr
    match (qParams.find? (·.1 == "returnTo")).map Prod.snd with
    | some rawRt =>
        let safeLoc := sanitizeReturnTo (some rawRt)
        let hdrs := [
          ("Location", safeLoc),
          ("Set-Cookie", clearSess.render),
          ("Set-Cookie", clearTx.render)
        ]
        return some (formatHttpResponse 302 "text/plain; charset=utf-8" ByteArray.empty isHead req.keepAlive true (extraHeaders := hdrs))
    | none =>
        let hdrs := [("Set-Cookie", clearSess.render), ("Set-Cookie", clearTx.render)]
        return some (formatHttpResponse 200 "application/json" "{\"ok\":true}".toUTF8 isHead req.keepAlive true (extraHeaders := hdrs))

  else if (req.method == "GET" || isHead) && pathOnly == cfg.mePath then
    match resolvedUser? with
    | some uid =>
        let claimsObj := Json.obj (resolvedClaims.map fun (k, v) => (k, Json.str v))
        let body := Json.render (Json.obj [
          ("authenticated", .bool true),
          ("id", .str uid),
          ("claims", claimsObj)
        ])
        return some (formatHttpResponse 200 "application/json" body.toUTF8 isHead req.keepAlive true)
    | none =>
        return some (formatHttpResponse 401 "application/json" "{\"authenticated\":false}".toUTF8 isHead req.keepAlive true)

  else
    return none

end Qed.Auth.Oidc
