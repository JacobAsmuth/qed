import Qed.Auth.Core
import Qed.Server.Core
import Qed.Server.Net
import Qed.Server.Http
import Qed.Server.Prim

namespace Qed.Auth.Oidc
open Qed.Auth Qed.Server Qed.Server.Net Qed.Server.Http

/-! ## Native OIDC / JWKS Verifier & Auth Code + PKCE (`S256`) BFF Runtime -/

abbrev HttpExecFn := String → String → Array (String × String) → ByteArray → Bool → IO (Except String (Nat × ByteArray × Array (String × String)))

structure OidcDiscovery where
  (issuer authorizationEndpoint tokenEndpoint jwksUri : String) (fetchedAtSec : Nat)
deriving Inhabited

structure OidcCacheState where
  (discovery? : Option OidcDiscovery := none) (jwks : Array JwkKey := #[]) (jwksFetchedAt lastMissRefresh : Nat := 0)
deriving Inhabited

structure ResolvedOidcConfig where
  (name issuer audience clientId : String) (clientSecret? : Option String := none)
  (sessionSecrets : List String := []) (sessionTtlSec : Nat := 86400)
  (loginPath : String := "/_qed/auth/login") (callbackPath : String := "/_qed/auth/callback")
  (logoutPath : String := "/_qed/auth/logout") (mePath : String := "/_qed/auth/me")
  (claimNames : List String := []) (devMode : Bool := false)
deriving Inhabited

def ResolvedOidcConfig.googleOneTapEnabled (cfg : ResolvedOidcConfig) : Bool := cfg.issuer == "https://accounts.google.com" && !cfg.clientId.isEmpty
private def ResolvedOidcConfig.ssrfGuard (cfg : ResolvedOidcConfig) : Bool :=
  !(cfg.devMode && ["http://127.0.0.1", "http://localhost"].any fun p => cfg.issuer == p || cfg.issuer.startsWith (p ++ ":"))

structure OidcRuntime where (cfg : ResolvedOidcConfig) (cache : Prim.StateBox OidcCacheState)

abbrev nowSec : IO Nat := Prim.nowSec
def loadNonEmptyEnv (envName : String) : IO (Option String) := do return (← Prim.getEnv envName).bind fun v => let t := trimWs v; if t.isEmpty then none else some t
def resolveEnvWithDefault (envName : String) (default? : Option String) : IO (Option String) := do return (← loadNonEmptyEnv envName).orElse fun _ => default?

def initOidcRuntime (spec : OidcAuthSpec) (baseSecrets : List String) (devMode : Bool) : IO (Option OidcRuntime) := do
  let some rawIss ← resolveEnvWithDefault spec.issuerEnv spec.issuerDefault? | return none
  let issuer := stripTrailingSlashes (trimWs rawIss); if issuer.isEmpty then return none
  let audience := (← resolveEnvWithDefault spec.audienceEnv spec.audienceDefault?).getD spec.name
  let clientId := ((← spec.clientIdEnv?.bindM (resolveEnvWithDefault · spec.clientIdDefault?)).orElse fun _ => spec.clientIdDefault?).getD audience
  let clientSecret? ← spec.clientSecretEnv?.bindM (resolveEnvWithDefault · none)
  let sessionSecrets ← if !baseSecrets.isEmpty then pure baseSecrets else if devMode then pure [← Prim.randomHex 32] else pure []
  return some {
    cfg := { name := spec.name, issuer, audience, clientId, clientSecret?, sessionSecrets, sessionTtlSec := if spec.sessionTtlSec == 0 then 86400 else spec.sessionTtlSec,
             loginPath := spec.loginPath, callbackPath := spec.callbackPath, logoutPath := spec.logoutPath, mePath := spec.mePath, claimNames := spec.claims.map (·.name), devMode },
    cache := ← Prim.mkStateBox ({} : OidcCacheState) }

def verifyJwkSignature (key : JwkKey) (signingInput : String) (sig : ByteArray) : IO Bool :=
  match key with | .rsa _ n e => Prim.rsaJwkVerify n e signingInput.toUTF8 sig | .ecP256 _ x y => Prim.ecP256JwkVerify x y signingInput.toUTF8 sig
private def verifyParsedJwtWithKeys (cfg : OidcValidationCfg) (keys : Array JwkKey) (parsed : CompactJwt) (now : Nat) : IO (Except String (VerifiedClaims cfg now)) := do
  let some key := findMatchingJwk keys parsed.header.alg parsed.header.kid? | return .error "jwt: no matching signing key in JWKS"
  if !(← verifyJwkSignature key parsed.signingInput parsed.signature) then return .error "jwt: invalid cryptographic signature"
  return (parseJwtClaims parsed.payloadJson).bind (validateJwtClaims cfg now parsed.header.alg)
def verifyJwtWithKeys (cfg : OidcValidationCfg) (keys : Array JwkKey) (token : String) (now : Nat) : IO (Except String (VerifiedClaims cfg now)) :=
  match parseCompactJwt token with | .error e => pure (.error e) | .ok p => verifyParsedJwtWithKeys cfg keys p now

structure HttpJsonOpts where
  (headers : Array (String × String) := #[("Accept", "application/json")]) (body : ByteArray := ByteArray.empty)
  (ssrfGuard : Bool := true) (okStatus : Nat → Bool := fun st => 200 ≤ st && st < 300)
  (allowEmptyBody : Bool := false) (requireUtf8 : Bool := true)
  (fmtTransportErr : String → String → String := fun url e => s!"HTTP error calling `{url}`: {e}")
  (fmtStatusErr : String → Nat → String → String := fun url st raw => s!"`{url}` returned HTTP {st}{if raw.isEmpty then "" else s!": {raw}"}")
  (fmtJsonErr : String → Nat → String → String := fun url _ e => s!"invalid JSON from `{url}`: {e}")
  (fmtNonUtf8Err : String → String := fun url => s!"`{url}` returned non-UTF-8 body")

def execJsonHttpStatusWith (httpExec : HttpExecFn) (method url : String) (opts : HttpJsonOpts := {}) : IO (Except String (Nat × Json)) := do
  match ← httpExec method url opts.headers opts.body opts.ssrfGuard with
  | .error e => return .error (opts.fmtTransportErr url e)
  | .ok (status, respBody, _) =>
      let raw ← match String.fromUTF8? respBody with | some s => pure s | none => if opts.requireUtf8 then return .error (opts.fmtNonUtf8Err url) else pure ""
      if !opts.okStatus status then return .error (opts.fmtStatusErr url status raw)
      let trimmed := trimWs raw; if opts.allowEmptyBody && trimmed.isEmpty then return .ok (status, .obj [])
      return (Json.parse trimmed).map (status, ·) |>.mapError (opts.fmtJsonErr url status)

def execJsonHttp (httpExec : HttpExecFn) (method url : String) (headers : Array (String × String) := #[("Accept", "application/json")])
    (body : ByteArray := ByteArray.empty) (ssrfGuard : Bool := true) (label : String := s!"oidc endpoint `{url}`") : IO (Except String Json) :=
  (·.map Prod.snd) <$> execJsonHttpStatusWith httpExec method url {
    headers, body, ssrfGuard, fmtTransportErr := fun _ e => s!"HTTP error calling {label}: {e}",
    fmtStatusErr := fun _ st raw => s!"{label} returned HTTP {st}{if raw.isEmpty then "" else s!": {String.ofList (raw.toList.take 400)}"}",
    fmtJsonErr := fun _ _ e => s!"invalid JSON from {label}: {e}", fmtNonUtf8Err := fun _ => s!"{label} returned non-UTF-8 body" }

private def cachedTtl {α : Type} (rt : OidcRuntime) (force : Bool) (readHit : OidcCacheState → Option (α × Nat))
    (fetch : Nat → IO (Except String α)) (store : α → Nat → OidcCacheState → OidcCacheState) : IO (Except String α) := do
  let now ← nowSec
  if !force then if let some (v, ts) ← Prim.atomicRead rt.cache readHit then if now < ts + 300 then return .ok v
  match ← fetch now with | .error e => return .error e | .ok v => Prim.atomicModify rt.cache fun st => (store v now st, ()); return .ok v

def fetchDiscovery (httpExec : HttpExecFn) (rt : OidcRuntime) (force : Bool := false) : IO (Except String OidcDiscovery) :=
  cachedTtl rt force (fun st => st.discovery?.map fun c => (c, c.fetchedAtSec)) (fun now => do
    match ← execJsonHttp httpExec "GET" (rt.cfg.issuer ++ "/.well-known/openid-configuration") (ssrfGuard := rt.cfg.ssrfGuard) with
    | .error e => return .error e
    | .ok j =>
        let iss := ((j.strAt? "issuer").map (stripTrailingSlashes ∘ trimWs)).getD rt.cfg.issuer
        if iss != rt.cfg.issuer then return .error s!"oidc discovery issuer mismatch: expected `{rt.cfg.issuer}`, got `{iss}`"
        let some jwksUri := j.strAt? "jwks_uri" | return .error "oidc discovery missing `jwks_uri`"
        return .ok { issuer := iss, jwksUri, fetchedAtSec := now, authorizationEndpoint := j.strAtD "authorization_endpoint" (rt.cfg.issuer ++ "/authorize"), tokenEndpoint := j.strAtD "token_endpoint" (rt.cfg.issuer ++ "/token") })
    (fun disc _ st => { st with discovery? := some disc })

def fetchJwks (httpExec : HttpExecFn) (rt : OidcRuntime) (force : Bool := false) : IO (Except String (Array JwkKey)) :=
  cachedTtl rt force (fun st => if st.jwks.isEmpty then none else some (st.jwks, st.jwksFetchedAt)) (fun _ => do
    match ← fetchDiscovery httpExec rt force with
    | .error e => return .error e
    | .ok disc => match ← execJsonHttp httpExec "GET" disc.jwksUri (ssrfGuard := rt.cfg.ssrfGuard) with
        | .error e => return .error e
        | .ok j => let keys := parseJwks j; return if keys.isEmpty then .error "oidc JWKS contained no supported RS256/ES256 signing keys" else .ok keys)
    (fun keys now st => { st with jwks := keys, jwksFetchedAt := now, lastMissRefresh := if force then now else st.lastMissRefresh })

def verifyOidcJwt (httpExec : HttpExecFn) (rt : OidcRuntime) (token : String) (expectedNonce? : Option String := none) : IO (Except String JwtClaims) := do
  let parsed ← match parseCompactJwt token with | .ok p => pure p | .error e => return .error e
  let keys0 ← match ← fetchJwks httpExec rt false with | .ok k => pure k | .error e => return .error e
  let now ← nowSec
  let keys ← match findMatchingJwk keys0 parsed.header.alg parsed.header.kid? with
    | some _ => pure keys0
    | none => if now >= (← Prim.atomicRead rt.cache (·.lastMissRefresh)) + 10 then (·.toOption.getD keys0) <$> fetchJwks httpExec rt true else pure keys0
  (·.map (·.claims)) <$> verifyParsedJwtWithKeys { issuer := rt.cfg.issuer, audience := rt.cfg.audience, clockSkewSec := 60, expectedNonce? } keys parsed now

def anySecretVerify (secrets : List String) (payload sigBytes : ByteArray) : IO Bool := secrets.anyM fun sec => Prim.hmacSha256Verify sec.toUTF8 payload sigBytes
def decodeHexSig (sigHex : String) : Option ByteArray := if sigHex.length == 64 then (Proto.decodeHex sigHex).toOption else none
def checkNotExpired (expStr : String) (nowSec : Nat) : Bool := (parseStrictU64 expStr 18446744073709551615).any (nowSec < ·)

private def envelopeTagInfo : String → Option (String × String)
  | "tx1" => some ("qed-tx-subkey-v1", "qed-tx\x00") | "ot1" => some ("qed-ot-subkey-v1", "qed-ot\x00") | _ => none
private def envelopeSigningKey (secret tag : String) : IO ByteArray :=
  match envelopeTagInfo tag with | some (subkey, _) => Prim.hmacSha256 secret.toUTF8 subkey.toUTF8 | none => pure secret.toUTF8
private def envelopeMacInput (tag body : String) : ByteArray :=
  match envelopeTagInfo tag with | some (_, pfx) => (pfx ++ body).toUTF8 | none => body.toUTF8
private def signHmacEnvelope (secret tag : String) (expSec : Nat) (b64 : String) : IO String := do
  let body := s!"{tag}.{expSec}.{b64}"; return s!"{body}.{Proto.encodeHex (← Prim.hmacSha256 (← envelopeSigningKey secret tag) (envelopeMacInput tag body))}"

def verifyHmacEnvelope (secrets : List String) (tag raw : String) (nowSec : Nat) : IO (Option String) := do
  if secrets.isEmpty then return none
  match raw.splitOn "." with
  | [t, expStr, b64, sigHex] =>
      if t != tag || !checkNotExpired expStr nowSec then return none
      let some sigBytes := decodeHexSig sigHex | return none
      let macIn := envelopeMacInput tag s!"{tag}.{expStr}.{b64}"
      if !(← secrets.anyM fun sec => do Prim.hmacSha256Verify (← envelopeSigningKey sec tag) macIn sigBytes) then return none
      return some b64
  | _ => return none

def signSessionCookieV2 (secret : String) (payload : SessionPayloadV2) (ttlSec : Nat := 86400) : IO String := do signHmacEnvelope secret "v2" ((← nowSec) + ttlSec) (encodeSessionPayloadV2 payload)
def verifySessionCookieV2 (secrets : List String) (token : String) (nowSec : Nat) : IO (Option SessionPayloadV2) := do return (← verifyHmacEnvelope secrets "v2" token nowSec).bind fun b64 => (decodeSessionPayloadV2 b64).toOption

private def mkHardenedCookie (name value : String) (maxAge : Nat) (devMode : Bool) : SetCookie := { name, value, path := "/", maxAge? := some maxAge, httpOnly := true, secure := !devMode, sameSite := .lax }
private def filterSessionClaims (claimNames : List String) (c : JwtClaims) : List (String × String) :=
  let base := c.flatClaims.filter fun (k, _) => k == "email" || k == "name" || (k != "email_verified" && claimNames.contains k)
  let withEmail := c.email?.elim base fun e => if base.any (·.1 == "email") then base else base ++ [("email", e)]
  withEmail ++ [("email_verified", if c.emailVerified then "true" else "false")]

@[noinline] def handleAuthRoute (httpExec : HttpExecFn) (rt : OidcRuntime) (req : ParsedReqHead) (pathOnly queryStr : String)
    (cookies : List (String × String)) (resolvedUser? : Option String) (resolvedClaims : List (String × String)) (isHead : Bool)
    (onCallbackAuthenticated? : Option (String → List (String × String) → IO (Except (Nat × String) (Array SetCookie))) := none)
    (reqBody : ByteArray := ByteArray.empty) : IO (Option ByteArray) := do
  let cfg := rt.cfg
  let jsonResp (st : Nat) (body : String) (hdrs : List (String × String) := []) := formatHttpResponse st "application/json" body.toUTF8 isHead req.keepAlive true (extraHeaders := hdrs)
  let redirectResp (loc : String) (hdrs : List (String × String)) := formatHttpResponse 302 "text/plain; charset=utf-8" ByteArray.empty isHead req.keepAlive true (extraHeaders := ("Location", loc) :: hdrs)
  let runRoute (m : ExceptT (Nat × String) IO ByteArray) : IO (Option ByteArray) := do
    match ← m.run with | .ok resp => return some resp | .error (st, msg) => return some (formatTextResponse st msg isHead req.keepAlive)
  let requireSignKey : ExceptT (Nat × String) IO String := cfg.sessionSecrets.head?.elim (throw (500, "auth error: QED_AUTH_SECRET is not configured")) pure
  let liftErr {α : Type} (st : Nat) (x : IO (Except String α)) (fmt : String → String := id) : ExceptT (Nat × String) IO α := ExceptT.mk ((·.mapError fun e => (st, fmt e)) <$> x)
  let reqOpt {α : Type} (st : Nat) (msg : String) (o : Option α) : ExceptT (Nat × String) IO α := o.elim (throw (st, msg)) pure
  let verifyAndIssue (signKey clearCookie tok nonce errPfx : String) : ExceptT (Nat × String) IO (List (String × String)) := do
    let claims ← liftErr 401 (verifyOidcJwt httpExec rt tok (expectedNonce? := some nonce)) (s!"{errPfx}: {·}")
    let sessPayload : SessionPayloadV2 := { userId := claims.sub, claims := filterSessionClaims cfg.claimNames claims }
    let extraHookCookies ← match onCallbackAuthenticated? with | some onAuth => setCookieHeaders <$> Array.toList <$> ExceptT.mk (onAuth sessPayload.userId sessPayload.claims) | none => pure []
    let sessTok ← signSessionCookieV2 signKey sessPayload cfg.sessionTtlSec
    return setCookieHeaders [SetCookie.clear clearCookie "/", mkHardenedCookie "qed_session" sessTok cfg.sessionTtlSec cfg.devMode] ++ extraHookCookies
  let signEnvCookie (signKey tag cookieName : String) (payload : ByteArray) : ExceptT (Nat × String) IO (List (String × String)) := do
    let v ← signHmacEnvelope signKey tag ((← nowSec) + 600) (base64UrlEncode payload)
    return setCookieHeaders [mkHardenedCookie cookieName v 600 cfg.devMode]
  let readEnvCookie (tag cookieName missingMsg invalidMsg : String) : ExceptT (Nat × String) IO String := do
    let raw ← reqOpt 400 missingMsg (cookies.lookup cookieName)
    reqOpt 400 invalidMsg (← verifyHmacEnvelope cfg.sessionSecrets tag raw (← nowSec))
  if req.method == "GET" && pathOnly == cfg.loginPath then
    runRoute do
      let (signKey, disc) := (← requireSignKey, ← liftErr 502 (fetchDiscovery httpExec rt false))
      let (returnTo, state, nonce, codeVerifier) := (sanitizeReturnTo ((parseQueryParams queryStr).lookup "returnTo"), ← Prim.randomHex 24, ← Prim.randomHex 24, ← Prim.randomHex 32)
      let host := (req.host?.map trimWs).getD "127.0.0.1:8000"
      let redirectUri := s!"{if cfg.devMode || host.startsWith "127.0.0.1" || host.startsWith "localhost" then "http" else "https"}://{host}{cfg.callbackPath}"
      let txJson := Json.render (.obj [("state", .str state), ("nonce", .str nonce), ("verifier", .str codeVerifier), ("returnTo", .str returnTo), ("redirectUri", .str redirectUri)])
      let authQuery := encodeFormBody [("response_type", "code"), ("client_id", cfg.clientId), ("redirect_uri", redirectUri), ("scope", "openid email profile"),
        ("state", state), ("nonce", nonce), ("code_challenge", base64UrlEncode (← Prim.sha256 codeVerifier.toUTF8)), ("code_challenge_method", "S256")]
      return redirectResp (sanitizeHeader (disc.authorizationEndpoint ++ (if disc.authorizationEndpoint.contains "?" then "&" else "?") ++ authQuery)) (← signEnvCookie signKey "tx1" "qed_auth_tx" txJson.toUTF8)
  else if req.method == "GET" && pathOnly == cfg.callbackPath then
    runRoute do
      let (signKey, qParams, badTx) := (← requireSignKey, parseQueryParams queryStr, "auth callback invalid or expired transaction cookie")
      let code ← reqOpt 400 "auth callback missing `code`" (qParams.lookup "code"); let state ← reqOpt 400 "auth callback missing `state`" (qParams.lookup "state")
      let txB64 ← readEnvCookie "tx1" "qed_auth_tx" "auth callback missing transaction cookie" badTx
      let txJ ← reqOpt 400 badTx (decodeBase64UrlJson txB64 "tx").toOption
      let (txState, txNonce, txVer, txRedir) ← reqOpt 400 badTx (do some (← txJ.strAt? "state", ← txJ.strAt? "nonce", ← txJ.strAt? "verifier", ← txJ.strAt? "redirectUri"))
      if state != txState then throw (403, "auth callback state mismatch")
      let disc ← liftErr 502 (fetchDiscovery httpExec rt false)
      let formPairs := [("grant_type", "authorization_code"), ("code", code), ("redirect_uri", txRedir), ("client_id", cfg.clientId), ("code_verifier", txVer)] ++ cfg.clientSecret?.elim [] fun cs => [("client_secret", cs)]
      let tokJson ← liftErr 502 (execJsonHttp httpExec "POST" disc.tokenEndpoint #[("Content-Type", "application/x-www-form-urlencoded"), ("Accept", "application/json")] (encodeFormBody formPairs).toUTF8 cfg.ssrfGuard "oidc token endpoint")
      let idToken ← reqOpt 502 "oidc token response missing `id_token`" (tokJson.strAt? "id_token")
      return redirectResp (sanitizeReturnTo (txJ.strAt? "returnTo")) (← verifyAndIssue signKey "qed_auth_tx" idToken txNonce "oidc id_token verification failed")
  else if req.method == "GET" && pathOnly == "/_qed/auth/onetap" then
    if resolvedUser?.isSome || !cfg.googleOneTapEnabled then return some (jsonResp 200 "{\"enabled\":false}" [("Cache-Control", "no-store")])
    runRoute do
      let (signKey, nonce) := (← requireSignKey, ← Prim.randomHex 24)
      return jsonResp 200 (Json.render (Json.obj [("enabled", .bool true), ("clientId", .str cfg.clientId), ("nonce", .str nonce)])) (("Cache-Control", "no-store") :: (← signEnvCookie signKey "ot1" "qed_onetap_nonce" nonce.toUTF8))
  else if req.method == "POST" && pathOnly == "/_qed/auth/onetap" then
    if !cfg.googleOneTapEnabled then return some (jsonResp 404 "{\"error\":\"Google One Tap not enabled\"}")
    runRoute do
      let signKey ← requireSignKey
      let nonceB64 ← readEnvCookie "ot1" "qed_onetap_nonce" "missing One Tap nonce cookie" "invalid or expired One Tap nonce cookie"
      let expectedNonce ← reqOpt 400 "corrupt One Tap nonce cookie" ((base64UrlDecode nonceB64).toOption.bind String.fromUTF8?)
      let bodyJson ← reqOpt 400 "invalid JSON body" ((String.fromUTF8? reqBody).bind fun s => (Json.parse s).toOption)
      let credential ← reqOpt 400 "missing `credential`" (bodyJson.strAt? "credential")
      return jsonResp 200 "{\"ok\":true}" (("Cache-Control", "no-store") :: (← verifyAndIssue signKey "qed_onetap_nonce" credential expectedNonce "Google One Tap verification failed"))
  else if (req.method == "POST" || req.method == "GET") && pathOnly == cfg.logoutPath then
    let hdrs := setCookieHeaders [SetCookie.clear "qed_session" "/", SetCookie.clear "qed_auth_tx" "/"]
    return some <| match (parseQueryParams queryStr).lookup "returnTo" with | some rawRt => redirectResp (sanitizeReturnTo (some rawRt)) hdrs | none => jsonResp 200 "{\"ok\":true}" hdrs
  else if (req.method == "GET" || isHead) && pathOnly == cfg.mePath then
    return some <| resolvedUser?.elim (jsonResp 401 "{\"authenticated\":false}") fun uid =>
      jsonResp 200 (Json.render (Json.obj [("authenticated", .bool true), ("id", .str uid), ("claims", Json.obj (resolvedClaims.map fun (k, v) => (k, .str v)))]))
  else return none

end Qed.Auth.Oidc
