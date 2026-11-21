import Qed.Auth.Core
import Qed.Render
import Qed.Server.Http
import Qed.Server.Prim

namespace Qed.Cli.DevAuth

open Qed.Auth
open Qed.Server
open Qed.Server.Http

/-! ## Built-In Local Dev OIDC Identity Provider (`Cli.DevAuth`)
    Started automatically by `qed dev` (or via `qed dev-auth [port]`) when an app declares
    an `auth` block and `QED_AUTH_ISSUER` is not already configured.
    - Generates an ephemeral ECDSA P-256 (`ES256`) keypair via `ring` at startup.
    - Serves standard `/.well-known/openid-configuration`, `/jwks.json`, `/authorize`
      (interactive persona/role switcher + `?auto=1` fast mode), and `/token` (PKCE `S256`
      verification + real ES256-signed OIDC `id_token`).
    - Lives strictly inside `Cli/` and is never linked into production `dist/server` binaries. -/

structure DevAuthCode where
  code          : String
  clientId      : String
  redirectUri   : String
  nonce         : String
  codeChallenge : String
  sub           : String
  email         : String
  emailVerified : Bool
  role          : String
  orgId         : String
  expiresAtSec  : Nat
deriving Inhabited

structure DevAuthKeypair where
  kid      : String := "qed-dev-1"
  pkcs8Der : ByteArray
  xB64     : String
  yB64     : String

/-- Mints a real RFC 7519 `ES256`-signed OIDC `id_token` using the ephemeral P-256 keypair. -/
def signDevIdToken (kp : DevAuthKeypair) (issuer sub aud nonce email role orgId : String)
    (emailVerified : Bool) (ttlSec : Nat := 3600) : IO (Except String String) := do
  let nowSec := ((← Prim.nowMs).toNat) / 1000
  let expSec := nowSec + ttlSec
  let hdrJson := Qed.Json.obj [
    ("alg", .str "ES256"),
    ("typ", .str "JWT"),
    ("kid", .str kp.kid)
  ]
  let baseClaims : List (String × Qed.Json) := [
    ("iss", .str issuer),
    ("sub", .str sub),
    ("aud", .str aud),
    ("exp", .num ⟨Int.ofNat expSec, 0⟩),
    ("iat", .num ⟨Int.ofNat nowSec, 0⟩),
    ("email", .str email),
    ("email_verified", .bool emailVerified),
    ("role", .str role)
  ]
  let withNonce := if nonce.isEmpty then baseClaims else baseClaims ++ [("nonce", .str nonce)]
  let withOrg := if orgId.isEmpty then withNonce else withNonce ++ [("orgId", .str orgId)]
  let hdrB64 := base64UrlEncode (Qed.Json.render hdrJson).toUTF8
  let payB64 := base64UrlEncode (Qed.Json.render (.obj withOrg)).toUTF8
  let signingInput := hdrB64 ++ "." ++ payB64
  match ← Prim.ecP256Sign kp.pkcs8Der signingInput.toUTF8 with
  | .error e => return .error e
  | .ok sig  => return .ok (signingInput ++ "." ++ base64UrlEncode sig)

def renderDevAuthorizePage (issuer clientId redirectUri state nonce codeChallenge : String) : String :=
  let hClient := Qed.escapeHtml clientId
  let hRedir  := Qed.escapeHtml redirectUri
  let hState  := Qed.escapeHtml state
  let hNonce  := Qed.escapeHtml nonce
  let hChal   := Qed.escapeHtml codeChallenge
  let hIss    := Qed.escapeHtml issuer
  "<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">" ++
  "<title>Qed Dev Auth — Local OIDC Sign In</title>" ++
  "<style>" ++
  "body{margin:0;min-height:100vh;display:grid;place-items:center;background:#0f172a;color:#e2e8f0;font:14px/1.5 ui-sans-serif,system-ui,sans-serif}" ++
  ".card{width:min(440px,92vw);background:#1e293b;border:1px solid #334155;border-radius:14px;padding:24px;box-shadow:0 20px 50px rgba(0,0,0,.45)}" ++
  "h1{margin:0 0 4px;font-size:18px;color:#f8fafc}.sub{margin:0 0 16px;color:#94a3b8;font-size:12px}" ++
  ".presets{display:grid;grid-template-columns:repeat(3,1fr);gap:8px;margin-bottom:16px}" ++
  ".preset{background:#0f172a;color:#cbd5e1;border:1px solid #334155;border-radius:8px;padding:8px;cursor:pointer;font-size:12px}" ++
  ".preset:hover{border-color:#38bdf8;color:#fff}" ++
  "label{display:block;margin:10px 0 4px;font-size:12px;color:#cbd5e1}" ++
  "input,select{width:100%;box-sizing:border-box;padding:8px 10px;border-radius:8px;border:1px solid #475569;background:#0f172a;color:#f8fafc;font:inherit}" ++
  ".row{display:flex;align-items:center;gap:8px;margin-top:12px}.row input{width:auto}" ++
  "button[type=submit]{margin-top:16px;width:100%;padding:10px;border:0;border-radius:8px;background:#2563eb;color:#fff;font-weight:600;cursor:pointer}" ++
  "button[type=submit]:hover{background:#1d4ed8}" ++
  "</style></head><body><div class=\"card\">" ++
  "<h1>Qed Local Dev Auth (OIDC)</h1>" ++
  s!"<p class=\"sub\">Issuer: {hIss} · Client: {hClient} · ES256 + PKCE S256</p>" ++
  "<div class=\"presets\">" ++
  "<button type=\"button\" class=\"preset\" onclick=\"pick('usr_admin','alice@dev.local','admin','org_acme')\">Admin<br><small>alice</small></button>" ++
  "<button type=\"button\" class=\"preset\" onclick=\"pick('usr_editor','carol@dev.local','editor','org_acme')\">Editor<br><small>carol</small></button>" ++
  "<button type=\"button\" class=\"preset\" onclick=\"pick('usr_member','bob@dev.local','member','org_beta')\">Member<br><small>bob</small></button>" ++
  "</div>" ++
  "<form method=\"POST\" action=\"/authorize\">" ++
  s!"<input type=\"hidden\" name=\"client_id\" value=\"{hClient}\">" ++
  s!"<input type=\"hidden\" name=\"redirect_uri\" value=\"{hRedir}\">" ++
  s!"<input type=\"hidden\" name=\"state\" value=\"{hState}\">" ++
  s!"<input type=\"hidden\" name=\"nonce\" value=\"{hNonce}\">" ++
  s!"<input type=\"hidden\" name=\"code_challenge\" value=\"{hChal}\">" ++
  "<label>User ID (`sub`)</label><input id=\"sub\" name=\"sub\" value=\"usr_admin\" required>" ++
  "<label>Email</label><input id=\"email\" name=\"email\" value=\"alice@dev.local\">" ++
  "<label>Role claim</label><input id=\"role\" name=\"role\" value=\"admin\">" ++
  "<label>Org ID claim</label><input id=\"orgId\" name=\"orgId\" value=\"org_acme\">" ++
  "<label class=\"row\"><input type=\"checkbox\" name=\"verified\" value=\"1\" checked> Email verified</label>" ++
  "<button type=\"submit\">Sign in as Dev Persona</button></form>" ++
  "<script>function pick(s,e,r,o){document.getElementById('sub').value=s;document.getElementById('email').value=e;document.getElementById('role').value=r;document.getElementById('orgId').value=o;}</script>" ++
  "</div></body></html>"

private def isLocalCallbackUri (uri : String) : Bool :=
  (uri.startsWith "http://127.0.0.1:" || uri.startsWith "http://localhost:") &&
  !uri.contains "\r" && !uri.contains "\n"

private def stripQ (target : String) : String × String :=
  match target.splitOn "?" with
  | []      => ("/", "")
  | [p]     => (p, "")
  | p :: qs => (p, String.intercalate "?" qs)

private def lookupParam (ps : List (String × String)) (k : String) (fallback : String := "") : String :=
  ((ps.find? (·.1 == k)).map Prod.snd).getD fallback

private def parseOAuthParams (ps : List (String × String)) : String × String × String × String × String :=
  (lookupParam ps "client_id" "qed-app", lookupParam ps "redirect_uri",
   lookupParam ps "state", lookupParam ps "nonce", lookupParam ps "code_challenge")

private def parsePersona (ps : List (String × String)) (defaultOrg : String := "org_acme")
    (checkboxVerified : Bool := false) : String × String × String × String × Bool :=
  (lookupParam ps "sub" "usr_admin", lookupParam ps "email" "alice@dev.local",
   lookupParam ps "role" "admin", lookupParam ps "orgId" defaultOrg,
   if checkboxVerified then lookupParam ps "verified" != "" else lookupParam ps "verified" "1" != "0")

/-- Starts the ephemeral local Dev OIDC Identity Provider on `127.0.0.1:<port>`. -/
def runDevAuthServer (port : UInt16) : IO UInt32 := do
  let (pkcs8Der, pubX, pubY) ← match ← Prim.ecP256Keygen with
    | .ok triple => pure triple
    | .error e   => IO.eprintln s!"qed dev-auth: keygen failed: {e}"; return 1
  let kp : DevAuthKeypair := {
    kid := "qed-dev-1"
    pkcs8Der
    xB64 := base64UrlEncode pubX
    yB64 := base64UrlEncode pubY
  }
  let issuer := s!"http://127.0.0.1:{port}"
  let codesBox ← Prim.mkStateBox (#[] : Array DevAuthCode)

  let discoveryBody := (Qed.Json.render (Qed.Json.obj [
    ("issuer", .str issuer),
    ("authorization_endpoint", .str (issuer ++ "/authorize")),
    ("token_endpoint", .str (issuer ++ "/token")),
    ("jwks_uri", .str (issuer ++ "/jwks.json")),
    ("response_types_supported", .arr [.str "code"]),
    ("subject_types_supported", .arr [.str "public"]),
    ("id_token_signing_alg_values_supported", .arr [.str "ES256"]),
    ("code_challenge_methods_supported", .arr [.str "S256"])
  ])).toUTF8

  let jwksBody := (Qed.Json.render (Qed.Json.obj [
    ("keys", .arr [
      Qed.Json.obj [
        ("kty", .str "EC"),
        ("crv", .str "P-256"),
        ("alg", .str "ES256"),
        ("use", .str "sig"),
        ("kid", .str kp.kid),
        ("x", .str kp.xB64),
        ("y", .str kp.yB64)
      ]
    ])
  ])).toUTF8

  let healthBody := "{\"ok\":true,\"mode\":\"dev-oidc\"}".toUTF8

  let issueCodeAndRedirect (clientId redirectUri state nonce codeChallenge sub email role orgId : String)
      (verified keepAlive isHead : Bool) : IO ByteArray := do
    if !isLocalCallbackUri redirectUri then
      return formatHttpResponse 400 "text/plain; charset=utf-8"
        "dev-auth: redirect_uri must target localhost or 127.0.0.1".toUTF8 isHead keepAlive false
    let code ← Prim.randomHex 20
    let nowSec := ((← Prim.nowMs).toNat) / 1000
    let entry : DevAuthCode := {
      code, clientId, redirectUri, nonce, codeChallenge
      sub := if sub.isEmpty then "usr_dev" else sub
      email, emailVerified := verified, role, orgId
      expiresAtSec := nowSec + 300
    }
    Prim.atomicModify codesBox fun arr =>
      let live := arr.filter (·.expiresAtSec > nowSec)
      let trimmed := if live.size >= 128 then live.extract (live.size - 127) live.size else live
      (trimmed.push entry, ())
    let sep := if redirectUri.contains "?" then "&" else "?"
    let loc := redirectUri ++ sep ++ encodeFormBody [("code", code), ("state", state)]
    return formatHttpResponse 302 "text/plain; charset=utf-8" ByteArray.empty isHead keepAlive true
      (extraHeaders := [("Location", sanitizeHeader loc)])

  let dispatchReq (req : ParsedReqHead) (body : ByteArray) (_clientIp : String) : IO ByteArray := do
    let isHead := req.method == "HEAD"
    let (pathOnly, queryStr) := stripQ req.target
    let jsonResp (status : Nat) (b : ByteArray) : ByteArray :=
      formatHttpResponse status "application/json" b isHead req.keepAlive true
    let mintTokenResp (sub aud nonce email role orgId : String) (verified : Bool) : IO ByteArray := do
      match ← signDevIdToken kp issuer sub aud nonce email role orgId verified with
      | .error e => return jsonResp 500 (Qed.Json.render (.obj [("error", .str e)])).toUTF8
      | .ok tok  =>
          let resp := Qed.Json.render (.obj [
            ("token_type", .str "Bearer"), ("id_token", .str tok),
            ("access_token", .str tok), ("expires_in", .num ⟨3600, 0⟩)
          ])
          return jsonResp 200 resp.toUTF8
    if (req.method == "GET" || isHead) && pathOnly == "/_qed/health" then
      return jsonResp 200 healthBody
    else if (req.method == "GET" || isHead) && pathOnly == "/.well-known/openid-configuration" then
      return jsonResp 200 discoveryBody
    else if (req.method == "GET" || isHead) && pathOnly == "/jwks.json" then
      return jsonResp 200 jwksBody
    else if req.method == "GET" && pathOnly == "/authorize" then
      let q := parseQueryParams queryStr
      let (clientId, redirectUri, state, nonce, chal) := parseOAuthParams q
      if lookupParam q "auto" == "1" then
        let (sub, email, role, orgId, verified) := parsePersona q
        return ← issueCodeAndRedirect clientId redirectUri state nonce chal sub email role orgId verified req.keepAlive isHead
      let html := renderDevAuthorizePage issuer clientId redirectUri state nonce chal
      return formatHttpResponse 200 "text/html; charset=utf-8" html.toUTF8 isHead req.keepAlive true
    else if req.method == "POST" && pathOnly == "/authorize" then
      let form := parseQueryParams ((String.fromUTF8? body).getD "")
      let (clientId, redirectUri, state, nonce, chal) := parseOAuthParams form
      let (sub, email, role, orgId, verified) := parsePersona form "" true
      return ← issueCodeAndRedirect clientId redirectUri state nonce chal sub email role orgId verified req.keepAlive isHead
    else if req.method == "POST" && pathOnly == "/token" then
      let form := parseQueryParams ((String.fromUTF8? body).getD "")
      let grant := lookupParam form "grant_type"
      if grant == "direct_dev_token" then
        -- Dev/test convenience minting an ES256 Bearer JWT directly from this IdP
        let aud := lookupParam form "audience" (lookupParam form "client_id" "qed-app")
        let (sub, email, role, orgId, verified) := parsePersona form
        return ← mintTokenResp sub aud "" email role orgId verified
      if grant != "authorization_code" then
        return jsonResp 400 "{\"error\":\"unsupported_grant_type\"}".toUTF8
      let code := lookupParam form "code"
      let verifier := lookupParam form "code_verifier"
      let clientId := lookupParam form "client_id"
      let redirectUri := lookupParam form "redirect_uri"
      let nowSec := ((← Prim.nowMs).toNat) / 1000
      let found? ← Prim.atomicModify codesBox fun arr =>
        match arr.find? (·.code == code) with
        | some c => (arr.filter (·.code != code), some c)
        | none   => (arr, none)
      let some entry := found?
        | return jsonResp 400 "{\"error\":\"invalid_grant\",\"error_description\":\"unknown or already used code\"}".toUTF8
      if nowSec >= entry.expiresAtSec || entry.clientId != clientId || entry.redirectUri != redirectUri then
        return jsonResp 400 "{\"error\":\"invalid_grant\",\"error_description\":\"code mismatch or expired\"}".toUTF8
      if !entry.codeChallenge.isEmpty then
        let digest ← Prim.sha256 verifier.toUTF8
        if base64UrlEncode digest != entry.codeChallenge then
          return jsonResp 400 "{\"error\":\"invalid_grant\",\"error_description\":\"PKCE S256 verification failed\"}".toUTF8
      return ← mintTokenResp entry.sub entry.clientId entry.nonce entry.email entry.role entry.orgId entry.emailVerified
    else
      return formatHttpResponse 404 "text/plain; charset=utf-8" "not found".toUTF8 isHead req.keepAlive true

  let onHead (headBytes : ByteArray) (clientIp : String) (_inline : Nat) :
      IO (Prim.HttpHeadAction ParsedReqHead Unit) := do
    match parseRequestHead headBytes with
    | .error (code, msg) => return .doneClose (formatErrorResponse code msg)
    | .ok req =>
        if req.contentLen == 0 then
          let wire ← dispatchReq req ByteArray.empty clientIp
          return if req.keepAlive then .doneKeepAlive wire else .doneClose wire
        else
          return if req.keepAlive then .needBodyKeep req.contentLen req else .needBodyClose req.contentLen req

  let onWsBytes (_ : Unit) (rx : ByteArray) (frag : Unit) (_ : Array (Nat × String × ByteArray)) :=
    pure { consumed := rx.size, outWire := ByteArray.empty, closeFlag := 1, fragState := frag, subOps := #[] : Prim.WsStepOut Unit }

  Prim.serveNative "127.0.0.1" port 1 () onHead dispatchReq onWsBytes (fun _ _ _ => pure ())

end Qed.Cli.DevAuth
