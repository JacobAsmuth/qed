import Qed.Auth.Core
import Qed.Server.Core
import Qed.Server.Net
import Qed.Server.Http
import Qed.Server.Prim

namespace Qed.Auth.Oidc

open Qed.Auth Qed.Server Qed.Server.Net Qed.Server.Http

/-! ## Native OIDC / JWKS Verifier & Auth Code + PKCE (`S256`) BFF Runtime (`Qed.Auth.Oidc`) -/

abbrev HttpExecFn :=
  String → String → Array (String × String) → ByteArray → Bool → IO (Except String (Nat × ByteArray × Array (String × String)))

structure OidcDiscovery where
  issuer : String
  authorizationEndpoint : String
  tokenEndpoint : String
  jwksUri : String
  fetchedAtSec : Nat
deriving Inhabited, Repr

structure OidcCacheState where
  discovery? : Option OidcDiscovery := none
  jwks : Array JwkKey := #[]
  jwksFetchedAt : Nat := 0
  lastMissRefresh : Nat := 0
deriving Inhabited

structure ResolvedOidcConfig where
  name : String
  issuer : String
  audience : String
  clientId : String
  clientSecret? : Option String := none
  sessionSecrets : List String := []
  sessionTtlSec : Nat := 86400
  loginPath : String := "/_qed/auth/login"
  callbackPath : String := "/_qed/auth/callback"
  logoutPath : String := "/_qed/auth/logout"
  mePath : String := "/_qed/auth/me"
  claimNames : List String := []
  devMode : Bool := false
deriving Inhabited, Repr

def ResolvedOidcConfig.googleOneTapEnabled (cfg : ResolvedOidcConfig) : Bool :=
  cfg.issuer == "https://accounts.google.com" && !cfg.clientId.isEmpty

structure OidcRuntime where
  cfg   : ResolvedOidcConfig
  cache : Prim.StateBox OidcCacheState

def nowSec : IO Nat := return (← Prim.nowMs).toNat / 1000

private def ResolvedOidcConfig.ssrfGuard (cfg : ResolvedOidcConfig) : Bool :=
  !(cfg.devMode && ["http://127.0.0.1", "http://localhost"].any fun p => cfg.issuer == p || cfg.issuer.startsWith (p ++ ":"))

def loadNonEmptyEnv (envName : String) : IO (Option String) := do
  return (← Prim.getEnv envName).bind fun v => let t := trimWs v; if t.isEmpty then none else some t

private def resolveEnvWithDefault (envName : String) (default? : Option String) : IO (Option String) := do
  return (← loadNonEmptyEnv envName).orElse fun _ => default?

/-- Resolves an `OidcAuthSpec` from OS environment variables at server boot. -/
def initOidcRuntime (spec : OidcAuthSpec) (baseSecrets : List String) (devMode : Bool) : IO (Option OidcRuntime) := do
  let some rawIss ← resolveEnvWithDefault spec.issuerEnv spec.issuerDefault? | return none
  let issuer := stripTrailingSlashes (trimWs rawIss)
  if issuer.isEmpty then return none
  let audience := (← resolveEnvWithDefault spec.audienceEnv spec.audienceDefault?).getD spec.name
  let clientId := ((← spec.clientIdEnv?.bindM (resolveEnvWithDefault · spec.clientIdDefault?)).orElse fun _ => spec.clientIdDefault?).getD audience
  let clientSecret? ← spec.clientSecretEnv?.bindM (resolveEnvWithDefault · none)
  let sessionSecrets ← if !baseSecrets.isEmpty then pure baseSecrets else if devMode then pure [← Prim.randomHex 32] else pure []
  return some {
    cfg := {
      name := spec.name, issuer, audience, clientId, clientSecret?, sessionSecrets,
      sessionTtlSec := if spec.sessionTtlSec == 0 then 86400 else spec.sessionTtlSec,
      loginPath := spec.loginPath, callbackPath := spec.callbackPath, logoutPath := spec.logoutPath, mePath := spec.mePath,
      claimNames := spec.claims.map (·.name), devMode },
    cache := ← Prim.mkStateBox ({} : OidcCacheState) }

/-! ### Cryptographic JWK Verification (`RS256` & `ES256` via `ring`) -/

def verifyJwkSignature (key : JwkKey) (signingInput : String) (sig : ByteArray) : IO Bool :=
  match key with | .rsa _ n e => Prim.rsaJwkVerify n e signingInput.toUTF8 sig | .ecP256 _ x y => Prim.ecP256JwkVerify x y signingInput.toUTF8 sig

private def verifyParsedJwtWithKeys (cfg : OidcValidationCfg) (keys : Array JwkKey) (parsed : CompactJwt) (now : Nat) :
    ExceptT String IO (VerifiedClaims cfg now) := do
  let some key := findMatchingJwk keys parsed.header.alg parsed.header.kid? | throw "jwt: no matching signing key in JWKS"
  if !(← verifyJwkSignature key parsed.signingInput parsed.signature) then throw "jwt: invalid cryptographic signature"
  liftP (validateJwtClaims cfg now parsed.header.alg (← liftP (parseJwtClaims parsed.payloadJson)))

def verifyJwtWithKeys (cfg : OidcValidationCfg) (keys : Array JwkKey) (token : String) (now : Nat) :
    IO (Except String (VerifiedClaims cfg now)) :=
  ExceptT.run do verifyParsedJwtWithKeys cfg keys (← liftP (parseCompactJwt token)) now

/-! ### OIDC Discovery & JWKS Caching -/

def execJsonHttp (httpExec : HttpExecFn) (method url : String) (headers : Array (String × String) := #[("Accept", "application/json")])
    (body : ByteArray := ByteArray.empty) (ssrfGuard : Bool := true) (label : String := s!"oidc endpoint `{url}`") : IO (Except String Json) := do
  match ← httpExec method url headers body ssrfGuard with
  | .error e => return .error s!"HTTP error calling {label}: {e}"
  | .ok (status, respBody, _) =>
      let some raw := String.fromUTF8? respBody | return .error s!"{label} returned non-UTF-8 body"
      if status < 200 || status >= 300 then
        return .error s!"{label} returned HTTP {status}{if raw.isEmpty then "" else s!": {String.ofList (raw.toList.take 400)}"}"
      return (Json.parse raw).mapError (s!"invalid JSON from {label}: {·}")

def fetchDiscovery (httpExec : HttpExecFn) (rt : OidcRuntime) (force : Bool := false) : IO (Except String OidcDiscovery) :=
  ExceptT.run do
    let now ← nowSec
    if !force then if let some c ← liftIO (Prim.atomicRead rt.cache (·.discovery?)) then if now < c.fetchedAtSec + 300 then return c
    let j ← liftE (execJsonHttp httpExec "GET" (rt.cfg.issuer ++ "/.well-known/openid-configuration") (ssrfGuard := rt.cfg.ssrfGuard))
    let iss := ((j.strAt? "issuer").map (stripTrailingSlashes ∘ trimWs)).getD rt.cfg.issuer
    if iss != rt.cfg.issuer then throw s!"oidc discovery issuer mismatch: expected `{rt.cfg.issuer}`, got `{iss}`"
    let some jwksUri := j.strAt? "jwks_uri" | throw "oidc discovery missing `jwks_uri`"
    let disc : OidcDiscovery := {
      issuer := iss, jwksUri, fetchedAtSec := now,
      authorizationEndpoint := j.strAtD "authorization_endpoint" (rt.cfg.issuer ++ "/authorize"),
      tokenEndpoint := j.strAtD "token_endpoint" (rt.cfg.issuer ++ "/token") }
    liftIO (Prim.atomicModify rt.cache fun st => ({ st with discovery? := some disc }, ()))
    return disc

def fetchJwks (httpExec : HttpExecFn) (rt : OidcRuntime) (force : Bool := false) : IO (Except String (Array JwkKey)) :=
  ExceptT.run do
    let now ← nowSec
    if !force then
      let (keys, fetchedAt) ← liftIO (Prim.atomicRead rt.cache fun st => (st.jwks, st.jwksFetchedAt))
      if !keys.isEmpty && now < fetchedAt + 300 then return keys
    let disc ← liftE (fetchDiscovery httpExec rt force)
    let keys := parseJwks (← liftE (execJsonHttp httpExec "GET" disc.jwksUri (ssrfGuard := rt.cfg.ssrfGuard)))
    if keys.isEmpty then throw "oidc JWKS contained no supported RS256/ES256 signing keys"
    liftIO (Prim.atomicModify rt.cache fun st => ({ st with jwks := keys, jwksFetchedAt := now, lastMissRefresh := if force then now else st.lastMissRefresh }, ()))
    return keys

def verifyOidcJwt (httpExec : HttpExecFn) (rt : OidcRuntime) (token : String) (expectedNonce? : Option String := none) : IO (Except String JwtClaims) :=
  ExceptT.run do
    let (parsed, keys0, now) := (← liftP (parseCompactJwt token), ← liftE (fetchJwks httpExec rt false), ← nowSec)
    let keys ← match findMatchingJwk keys0 parsed.header.alg parsed.header.kid? with
      | some _ => pure keys0
      | none   => if now >= (← liftIO (Prim.atomicRead rt.cache (·.lastMissRefresh))) + 10 then
                    (·.toOption.getD keys0) <$> liftIO (fetchJwks httpExec rt true) else pure keys0
    return (← verifyParsedJwtWithKeys { issuer := rt.cfg.issuer, audience := rt.cfg.audience, clockSkewSec := 60, expectedNonce? } keys parsed now).claims

/-! ### Signed `v2` Session Cookie & Short-Lived PKCE Transaction Cookie -/

def anySecretVerify (secrets : List String) (payload sigBytes : ByteArray) : IO Bool :=
  secrets.anyM fun sec => Prim.hmacSha256Verify sec.toUTF8 payload sigBytes

private def envelopeSigningKey (secret tag : String) : IO ByteArray :=
  if tag == "tx1" then Prim.hmacSha256 secret.toUTF8 "qed-tx-subkey-v1".toUTF8
  else if tag == "ot1" then Prim.hmacSha256 secret.toUTF8 "qed-ot-subkey-v1".toUTF8
  else pure secret.toUTF8

private def envelopeMacInput (tag body : String) : ByteArray :=
  if tag == "tx1" then s!"qed-tx\x00{body}".toUTF8
  else if tag == "ot1" then s!"qed-ot\x00{body}".toUTF8
  else body.toUTF8

private def signHmacEnvelope (secret tag : String) (expSec : Nat) (b64 : String) : IO String := do
  let body := s!"{tag}.{expSec}.{b64}"
  return s!"{body}.{Proto.encodeHex (← Prim.hmacSha256 (← envelopeSigningKey secret tag) (envelopeMacInput tag body))}"

private def verifyHmacEnvelope (secrets : List String) (tag raw : String) (nowSec : Nat) : IO (Option String) := do
  if secrets.isEmpty then return none
  match raw.splitOn "." with
  | [t, expStr, b64, sigHex] =>
      if t != tag || sigHex.length != 64 then return none
      let some expSec := parseStrictU64 expStr 18446744073709551615 | return none
      if nowSec >= expSec then return none
      let .ok sigBytes := Proto.decodeHex sigHex | return none
      let macIn := envelopeMacInput tag s!"{tag}.{expStr}.{b64}"
      if !(← secrets.anyM fun sec => do Prim.hmacSha256Verify (← envelopeSigningKey sec tag) macIn sigBytes) then return none
      return some b64
  | _ => return none

def signSessionCookieV2 (secret : String) (payload : SessionPayloadV2) (ttlSec : Nat := 86400) : IO String := do
  signHmacEnvelope secret "v2" ((← nowSec) + ttlSec) (encodeSessionPayloadV2 payload)

def verifySessionCookieV2 (secrets : List String) (token : String) (nowSec : Nat) : IO (Option SessionPayloadV2) := do
  return (← verifyHmacEnvelope secrets "v2" token nowSec).bind fun b64 => (decodeSessionPayloadV2 b64).toOption

private structure AuthTxCookie where
  state : String
  nonce : String
  codeVerifier : String
  returnTo : String
  redirectUri : String

private def signAuthTxCookie (secret : String) (tx : AuthTxCookie) (nowSec : Nat) : IO String :=
  signHmacEnvelope secret "tx1" (nowSec + 600) <| base64UrlEncode (Json.render <| Json.obj [
    ("state", .str tx.state), ("nonce", .str tx.nonce), ("verifier", .str tx.codeVerifier),
    ("returnTo", .str tx.returnTo), ("redirectUri", .str tx.redirectUri)]).toUTF8

private def verifyAuthTxCookie (secrets : List String) (raw : String) (nowSec : Nat) : IO (Option AuthTxCookie) := do
  let some b64 ← verifyHmacEnvelope secrets "tx1" raw nowSec | return none
  let .ok j := decodeBase64UrlJson b64 "tx" | return none
  return do
    some {
      state := ← j.strAt? "state", nonce := ← j.strAt? "nonce", codeVerifier := ← j.strAt? "verifier",
      returnTo := sanitizeReturnTo (j.strAt? "returnTo"), redirectUri := ← j.strAt? "redirectUri" }

private def mkHardenedCookie (name value : String) (maxAge : Nat) (devMode : Bool) : SetCookie :=
  { name, value, path := "/", maxAge? := some maxAge, httpOnly := true, secure := !devMode, sameSite := .lax }

private def filterSessionClaims (claimNames : List String) (c : JwtClaims) : List (String × String) :=
  let addMissing (xs : List (String × String)) (k v : String) := if xs.any (·.1 == k) then xs else xs ++ [(k, v)]
  let base := c.flatClaims.filter fun (k, _) => k == "email" || k == "name" || (k != "email_verified" && claimNames.contains k)
  let withEmail := c.email?.elim base (addMissing base "email")
  withEmail ++ [("email_verified", if c.emailVerified then "true" else "false")]

/-! ### Built-In OIDC Auth Endpoints (`/_qed/auth/login`, `/callback`, `/logout`, `/me`, `/onetap`) -/

def handleAuthRoute (httpExec : HttpExecFn) (rt : OidcRuntime) (req : ParsedReqHead)
    (pathOnly queryStr : String) (cookies : List (String × String))
    (resolvedUser? : Option String) (resolvedClaims : List (String × String)) (isHead : Bool)
    (onCallbackAuthenticated? : Option (String → List (String × String) → IO (Except (Nat × String) (Array SetCookie))) := none)
    (reqBody : ByteArray := ByteArray.empty) :
    IO (Option ByteArray) := do
  let cfg := rt.cfg
  let jsonResp (st : Nat) (body : String) (hdrs : List (String × String) := []) :=
    formatHttpResponse st "application/json" body.toUTF8 isHead req.keepAlive true (extraHeaders := hdrs)
  let redirectResp (loc : String) (hdrs : List (String × String)) :=
    formatHttpResponse 302 "text/plain; charset=utf-8" ByteArray.empty isHead req.keepAlive true (extraHeaders := ("Location", loc) :: hdrs)
  let runRoute (m : ExceptT (Nat × String) IO ByteArray) : IO (Option ByteArray) := do
    match ← m.run with | .ok resp => return some resp | .error (st, msg) => return some (formatTextResponse st msg isHead req.keepAlive)
  let requireSignKey : ExceptT (Nat × String) IO String :=
    cfg.sessionSecrets.head?.elim (throw (500, "auth error: QED_AUTH_SECRET is not configured")) pure
  let liftErr {α : Type} (st : Nat) (x : IO (Except String α)) (fmt : String → String := id) : ExceptT (Nat × String) IO α :=
    ExceptT.mk ((·.mapError fun e => (st, fmt e)) <$> x)
  let setCookieHdrs (cs : List SetCookie) := cs.map fun c => ("Set-Cookie", c.render)
  let issueSessionHdrs (signKey clearCookieName : String) (claims : JwtClaims) : ExceptT (Nat × String) IO (List (String × String)) := do
    let sessPayload : SessionPayloadV2 := { userId := claims.sub, claims := filterSessionClaims cfg.claimNames claims }
    let extraHookCookies ← match onCallbackAuthenticated? with
      | some onAuth => setCookieHdrs <$> Array.toList <$> ExceptT.mk (onAuth sessPayload.userId sessPayload.claims) | none => pure []
    let sessTok ← signSessionCookieV2 signKey sessPayload cfg.sessionTtlSec
    return setCookieHdrs [SetCookie.clear clearCookieName "/", mkHardenedCookie "qed_session" sessTok cfg.sessionTtlSec cfg.devMode] ++ extraHookCookies

  if req.method == "GET" && pathOnly == cfg.loginPath then
    runRoute do
      let (signKey, disc) := (← requireSignKey, ← liftErr 502 (fetchDiscovery httpExec rt false))
      let returnTo := sanitizeReturnTo ((parseQueryParams queryStr).lookup "returnTo")
      let (state, nonce, codeVerifier) := (← Prim.randomHex 24, ← Prim.randomHex 24, ← Prim.randomHex 32)
      let host := (req.host?.map trimWs).getD "127.0.0.1:8000"
      let scheme := if cfg.devMode || host.startsWith "127.0.0.1" || host.startsWith "localhost" then "http" else "https"
      let redirectUri := s!"{scheme}://{host}{cfg.callbackPath}"
      let txVal ← signAuthTxCookie signKey { state, nonce, codeVerifier, returnTo, redirectUri } (← nowSec)
      let authQuery := encodeFormBody [
        ("response_type", "code"), ("client_id", cfg.clientId), ("redirect_uri", redirectUri), ("scope", "openid email profile"),
        ("state", state), ("nonce", nonce), ("code_challenge", base64UrlEncode (← Prim.sha256 codeVerifier.toUTF8)), ("code_challenge_method", "S256")]
      return redirectResp (sanitizeHeader (disc.authorizationEndpoint ++ (if disc.authorizationEndpoint.contains "?" then "&" else "?") ++ authQuery))
        (setCookieHdrs [mkHardenedCookie "qed_auth_tx" txVal 600 cfg.devMode])

  else if req.method == "GET" && pathOnly == cfg.callbackPath then
    runRoute do
      let signKey ← requireSignKey; let qParams := parseQueryParams queryStr
      let some code := qParams.lookup "code" | throw (400, "auth callback missing `code`")
      let some state := qParams.lookup "state" | throw (400, "auth callback missing `state`")
      let some rawTx := cookies.lookup "qed_auth_tx" | throw (400, "auth callback missing transaction cookie")
      let some tx ← verifyAuthTxCookie cfg.sessionSecrets rawTx (← nowSec) | throw (400, "auth callback invalid or expired transaction cookie")
      if state != tx.state then throw (403, "auth callback state mismatch")
      let disc ← liftErr 502 (fetchDiscovery httpExec rt false)
      let formPairs := [("grant_type", "authorization_code"), ("code", code), ("redirect_uri", tx.redirectUri),
        ("client_id", cfg.clientId), ("code_verifier", tx.codeVerifier)] ++ cfg.clientSecret?.elim [] fun cs => [("client_secret", cs)]
      let tokJson ← liftErr 502 (execJsonHttp httpExec "POST" disc.tokenEndpoint
        #[("Content-Type", "application/x-www-form-urlencoded"), ("Accept", "application/json")] (encodeFormBody formPairs).toUTF8 cfg.ssrfGuard "oidc token endpoint")
      let some idToken := tokJson.strAt? "id_token" | throw (502, "oidc token response missing `id_token`")
      let claims ← liftErr 401 (verifyOidcJwt httpExec rt idToken (expectedNonce? := some tx.nonce)) (s!"oidc id_token verification failed: {·}")
      return redirectResp (sanitizeReturnTo (some tx.returnTo)) (← issueSessionHdrs signKey "qed_auth_tx" claims)

  else if req.method == "GET" && pathOnly == "/_qed/auth/onetap" then
    if resolvedUser?.isSome || !cfg.googleOneTapEnabled then
      return some (jsonResp 200 "{\"enabled\":false}" [("Cache-Control", "no-store")])
    runRoute do
      let signKey ← requireSignKey
      let nonce ← Prim.randomHex 24
      let cookieVal ← signHmacEnvelope signKey "ot1" ((← nowSec) + 600) (base64UrlEncode nonce.toUTF8)
      let body := Json.render (Json.obj [("enabled", .bool true), ("clientId", .str cfg.clientId), ("nonce", .str nonce)])
      return jsonResp 200 body (("Cache-Control", "no-store") :: setCookieHdrs [mkHardenedCookie "qed_onetap_nonce" cookieVal 600 cfg.devMode])

  else if req.method == "POST" && pathOnly == "/_qed/auth/onetap" then
    if !cfg.googleOneTapEnabled then return some (jsonResp 404 "{\"error\":\"Google One Tap not enabled\"}")
    runRoute do
      let signKey ← requireSignKey
      let some rawNonceCookie := cookies.lookup "qed_onetap_nonce" | throw (400, "missing One Tap nonce cookie")
      let some nonceB64 ← verifyHmacEnvelope cfg.sessionSecrets "ot1" rawNonceCookie (← nowSec) | throw (400, "invalid or expired One Tap nonce cookie")
      let .ok nonceBytes := base64UrlDecode nonceB64 | throw (400, "corrupt One Tap nonce cookie")
      let some expectedNonce := String.fromUTF8? nonceBytes | throw (400, "corrupt One Tap nonce cookie")
      let some bodyStr := String.fromUTF8? reqBody | throw (400, "invalid UTF-8 body")
      let .ok bodyJson := Json.parse bodyStr | throw (400, "invalid JSON body")
      let some credential := bodyJson.strAt? "credential" | throw (400, "missing `credential`")
      let claims ← liftErr 401 (verifyOidcJwt httpExec rt credential (expectedNonce? := some expectedNonce)) (s!"Google One Tap verification failed: {·}")
      return jsonResp 200 "{\"ok\":true}" (("Cache-Control", "no-store") :: (← issueSessionHdrs signKey "qed_onetap_nonce" claims))

  else if (req.method == "POST" || req.method == "GET") && pathOnly == cfg.logoutPath then
    let hdrs := setCookieHdrs [SetCookie.clear "qed_session" "/", SetCookie.clear "qed_auth_tx" "/"]
    return some <| match (parseQueryParams queryStr).lookup "returnTo" with
      | some rawRt => redirectResp (sanitizeReturnTo (some rawRt)) hdrs | none => jsonResp 200 "{\"ok\":true}" hdrs

  else if (req.method == "GET" || isHead) && pathOnly == cfg.mePath then
    return some <| match resolvedUser? with
      | some uid => jsonResp 200 (Json.render (Json.obj [("authenticated", .bool true), ("id", .str uid), ("claims", Json.obj (resolvedClaims.map fun (k, v) => (k, .str v)))]))
      | none => jsonResp 401 "{\"authenticated\":false}"

  else return none

end Qed.Auth.Oidc
