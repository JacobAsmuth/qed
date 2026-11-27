import Qed.Auth.Core
import Qed.Render
import Qed.Server.Http
import Qed.Server.Prim
namespace Qed.Cli.DevAuth
open Qed.Auth Qed.Server Qed.Server.Http

/-! ## Built-In Local Dev OIDC Identity Provider (`Cli.DevAuth`) -/

structure DevAuthCode where
  (code clientId redirectUri nonce codeChallenge sub email role orgId : String)
  emailVerified : Bool
  expiresAtSec  : Nat
deriving Inhabited

structure DevAuthKeypair where
  kid      : String := "qed-dev-1"
  pkcs8Der : ByteArray
  (xB64 yB64 : String)

def signDevIdToken (kp : DevAuthKeypair) (issuer sub aud nonce email role orgId : String)
    (emailVerified : Bool) (ttlSec : Nat := 3600) : IO (Except String String) := do
  let now ← Prim.nowSec
  let hdr := Qed.Json.obj [("alg", .str "ES256"), ("typ", .str "JWT"), ("kid", .str kp.kid)]
  let claims : List (String × Qed.Json) := [("iss", .str issuer), ("sub", .str sub), ("aud", .str aud),
    ("exp", .num ⟨Int.ofNat (now + ttlSec), 0⟩), ("iat", .num ⟨Int.ofNat now, 0⟩), ("email", .str email),
    ("email_verified", .bool emailVerified), ("role", .str role)] ++
    (if nonce.isEmpty then [] else [("nonce", .str nonce)]) ++ (if orgId.isEmpty then [] else [("orgId", .str orgId)])
  let signingInput := base64UrlEncode (Qed.Json.render hdr).toUTF8 ++ "." ++ base64UrlEncode (Qed.Json.render (.obj claims)).toUTF8
  return (← Prim.ecP256Sign kp.pkcs8Der signingInput.toUTF8).map fun sig => signingInput ++ "." ++ base64UrlEncode sig

def renderDevAuthorizePage (issuer clientId redirectUri state nonce codeChallenge : String) : String :=
  let (esc, tagMap) := (Qed.escapeHtml, fun {α} (xs : List α) (f : α → String) => String.join (xs.map f))
  let presetHtml := tagMap [("Admin", "alice", "usr_admin", "alice@dev.local", "admin", "org_acme"),
    ("Editor", "carol", "usr_editor", "carol@dev.local", "editor", "org_acme"), ("Member", "bob", "usr_member", "bob@dev.local", "member", "org_beta")]
    fun (lbl, nick, s, e, r, o) => s!"<button type=\"button\" class=\"preset\" onclick=\"pick('{s}','{e}','{r}','{o}')\">{lbl}<br><small>{nick}</small></button>"
  let hiddenHtml := tagMap [("client_id", clientId), ("redirect_uri", redirectUri), ("state", state), ("nonce", nonce), ("code_challenge", codeChallenge)]
    fun (k, v) => s!"<input type=\"hidden\" name=\"{k}\" value=\"{esc v}\">"
  let fieldHtml := tagMap [("User ID (`sub`)", "sub", "usr_admin", " required"), ("Email", "email", "alice@dev.local", ""), ("Role claim", "role", "admin", ""), ("Org ID claim", "orgId", "org_acme", "")]
    fun (lbl, id, v, req) => s!"<label>{lbl}</label><input id=\"{id}\" name=\"{id}\" value=\"{v}\"{req}>"
  "<!doctype html>\n<html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"><title>Qed Dev Auth: Local OIDC Sign In</title><style>" ++
  "body{margin:0;min-height:100vh;display:grid;place-items:center;background:#0f172a;color:#e2e8f0;font:14px/1.5 ui-sans-serif,system-ui,sans-serif}.card{width:min(440px,92vw);background:#1e293b;border:1px solid #334155;border-radius:14px;padding:24px;box-shadow:0 20px 50px rgba(0,0,0,.45)}h1{margin:0 0 4px;font-size:18px;color:#f8fafc}.sub{margin:0 0 16px;color:#94a3b8;font-size:12px}.presets{display:grid;grid-template-columns:repeat(3,1fr);gap:8px;margin-bottom:16px}.preset{background:#0f172a;color:#cbd5e1;border:1px solid #334155;border-radius:8px;padding:8px;cursor:pointer;font-size:12px}.preset:hover{border-color:#38bdf8;color:#fff}label{display:block;margin:10px 0 4px;font-size:12px;color:#cbd5e1}input,select{width:100%;box-sizing:border-box;padding:8px 10px;border-radius:8px;border:1px solid #475569;background:#0f172a;color:#f8fafc;font:inherit}.row{display:flex;align-items:center;gap:8px;margin-top:12px}.row input{width:auto}button[type=submit]{margin-top:16px;width:100%;padding:10px;border:0;border-radius:8px;background:#2563eb;color:#fff;font-weight:600;cursor:pointer}button[type=submit]:hover{background:#1d4ed8}" ++
  s!"</style></head><body><div class=\"card\"><h1>Qed Local Dev Auth (OIDC)</h1><p class=\"sub\">Issuer: {esc issuer} · Client: {esc clientId} · ES256 + PKCE S256</p><div class=\"presets\">{presetHtml}</div><form method=\"POST\" action=\"/authorize\">{hiddenHtml}{fieldHtml}<label class=\"row\"><input type=\"checkbox\" name=\"verified\" value=\"1\" checked> Email verified</label><button type=\"submit\">Sign in as Dev Persona</button></form><script>function pick(s,e,r,o)\{['sub','email','role','orgId'].forEach((k,i)=>document.getElementById(k).value=[s,e,r,o][i]);}</script></div></body></html>"

private def paramD (ps : List (String × String)) (k d : String := "") : String := (ps.lookup k).getD d
private def parsePersona (ps : List (String × String)) (defaultOrg : String := "org_acme") (checkboxVerified : Bool := false) :=
  (paramD ps "sub" "usr_admin", paramD ps "email" "alice@dev.local", paramD ps "role" "admin",
   paramD ps "orgId" defaultOrg, if checkboxVerified then paramD ps "verified" != "" else paramD ps "verified" "1" != "0")

def runDevAuthServer (port : UInt16) : IO UInt32 := do
  let (pkcs8Der, pubX, pubY) ← match ← Prim.ecP256Keygen with | .ok t => pure t | .error e => IO.eprintln s!"qed dev-auth: keygen failed: {e}"; return 1
  let kp : DevAuthKeypair := { pkcs8Der, xB64 := base64UrlEncode pubX, yB64 := base64UrlEncode pubY }
  let (issuer, codesBox, jBytes) := (s!"http://127.0.0.1:{port}", ← Prim.mkStateBox (#[] : Array DevAuthCode), fun j : Qed.Json => (Qed.Json.render j).toUTF8)
  let staticGets := [
    ("/_qed/health", "{\"ok\":true,\"mode\":\"dev-oidc\"}".toUTF8),
    ("/.well-known/openid-configuration", jBytes (.obj [
      ("issuer", .str issuer), ("authorization_endpoint", .str (issuer ++ "/authorize")), ("token_endpoint", .str (issuer ++ "/token")),
      ("jwks_uri", .str (issuer ++ "/jwks.json")), ("response_types_supported", .arr [.str "code"]), ("subject_types_supported", .arr [.str "public"]),
      ("id_token_signing_alg_values_supported", .arr [.str "ES256"]), ("code_challenge_methods_supported", .arr [.str "S256"])])),
    ("/jwks.json", jBytes (.obj [("keys", .arr [.obj [("kty", .str "EC"), ("crv", .str "P-256"), ("alg", .str "ES256"), ("use", .str "sig"), ("kid", .str kp.kid), ("x", .str kp.xB64), ("y", .str kp.yB64)]])]))]
  let dispatchReq (req : ParsedReqHead) (body : ByteArray) (_clientIp : String) : IO ByteArray := do
    let isHead := req.method == "HEAD"
    let (pathOnly, queryStr) := match req.target.splitOn "?" with | p :: qs => (p, "?".intercalate qs) | [] => (req.target, "")
    let resp (st : Nat) (ct : String) (b : ByteArray) (extra : List (String × String) := []) := formatHttpResponse st ct b isHead req.keepAlive true (extraHeaders := extra)
    let jsonResp (st : Nat) (b : ByteArray) := resp st "application/json" b
    let jsonErr (code : String) (desc? : Option String := none) (st : Nat := 400) := jsonResp st (jBytes (.obj (("error", .str code) :: desc?.elim [] fun d => [("error_description", .str d)])))
    let mintTokenResp (sub aud nonce email role orgId : String) (verified : Bool) : IO ByteArray := do
      match ← signDevIdToken kp issuer sub aud nonce email role orgId verified with
      | .error e => return jsonErr e none 500 | .ok tok => return jsonResp 200 (jBytes (.obj [("token_type", .str "Bearer"), ("id_token", .str tok), ("access_token", .str tok), ("expires_in", .num ⟨3600, 0⟩)]))
    if req.method == "GET" || isHead then if let some b := staticGets.lookup pathOnly then return jsonResp 200 b
    let formBody (_ : Unit) := parseQueryParams ((String.fromUTF8? body).getD "")
    match req.method, pathOnly with
    | "GET", "/authorize" | "POST", "/authorize" =>
      let isPost := req.method == "POST"; let ps := if isPost then formBody () else parseQueryParams queryStr
      let (clientId, redirectUri, state, nonce, codeChallenge) := (paramD ps "client_id" "qed-app", paramD ps "redirect_uri", paramD ps "state", paramD ps "nonce", paramD ps "code_challenge")
      if isPost || paramD ps "auto" == "1" then
        if !((redirectUri.startsWith "http://127.0.0.1:" || redirectUri.startsWith "http://localhost:") && !redirectUri.contains "\r" && !redirectUri.contains "\n") then
          return formatHttpResponse 400 "text/plain; charset=utf-8" "dev-auth: redirect_uri must target localhost or 127.0.0.1".toUTF8 isHead req.keepAlive false
        let (sub, email, role, orgId, verified) := if isPost then parsePersona ps "" true else parsePersona ps
        let (code, now) := (← Prim.randomHex 20, ← Prim.nowSec)
        let entry : DevAuthCode := { code, clientId, redirectUri, nonce, codeChallenge, email, role, orgId, emailVerified := verified, sub := if sub.isEmpty then "usr_dev" else sub, expiresAtSec := now + 300 }
        Prim.atomicModify codesBox fun arr => let live := arr.filter (·.expiresAtSec > now); ((if live.size >= 128 then live.extract (live.size - 127) live.size else live).push entry, ())
        return resp 302 "text/plain; charset=utf-8" ByteArray.empty [("Location", sanitizeHeader (redirectUri ++ (if redirectUri.contains "?" then "&" else "?") ++ encodeFormBody [("code", code), ("state", state)]))]
      return resp 200 "text/html; charset=utf-8" (renderDevAuthorizePage issuer clientId redirectUri state nonce codeChallenge).toUTF8
    | "POST", "/token" =>
      let form := formBody (); let grant := paramD form "grant_type"
      if grant == "direct_dev_token" then
        let (sub, email, role, orgId, verified) := parsePersona form
        return ← mintTokenResp sub (paramD form "audience" (paramD form "client_id" "qed-app")) "" email role orgId verified
      if grant != "authorization_code" then return jsonErr "unsupported_grant_type"
      let (code, now) := (paramD form "code", ← Prim.nowSec)
      let some entry ← Prim.atomicModify codesBox fun arr => match arr.find? (·.code == code) with | some c => (arr.filter (·.code != code), some c) | none => (arr, none)
        | return jsonErr "invalid_grant" (some "unknown or already used code")
      if now >= entry.expiresAtSec || entry.clientId != paramD form "client_id" || entry.redirectUri != paramD form "redirect_uri" then return jsonErr "invalid_grant" (some "code mismatch or expired")
      if !entry.codeChallenge.isEmpty then
        if base64UrlEncode (← Prim.sha256 (paramD form "code_verifier").toUTF8) != entry.codeChallenge then return jsonErr "invalid_grant" (some "PKCE S256 verification failed")
      return ← mintTokenResp entry.sub entry.clientId entry.nonce entry.email entry.role entry.orgId entry.emailVerified
    | _, _ => return resp 404 "text/plain; charset=utf-8" "not found".toUTF8
  let onHead (headBytes : ByteArray) (clientIp : String) (_inline : Nat) : IO (Prim.HttpHeadAction ParsedReqHead Unit) := do
    match parseRequestHead headBytes with
    | .error (code, msg) => return .doneClose (formatErrorResponse code msg)
    | .ok req => if req.contentLen == 0 then let wire ← dispatchReq req ByteArray.empty clientIp; return if req.keepAlive then .doneKeepAlive wire else .doneClose wire
                 else return if req.keepAlive then .needBodyKeep req.contentLen req else .needBodyClose req.contentLen req
  Prim.serveNative "127.0.0.1" port 1 () onHead dispatchReq
    (fun _ rx frag _ => pure { consumed := rx.size, outWire := ByteArray.empty, closeFlag := 1, fragState := frag, subOps := #[] : Prim.WsStepOut Unit }) (fun _ _ _ => pure ()) none

end Qed.Cli.DevAuth
