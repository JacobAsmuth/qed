import Qed.Base64
import Qed.Json.Lawful
import Qed.Router.Basic

namespace Qed.Auth

/-! ## Pure, Total, Kernel-Verified OIDC / JWT / JWKS Core (`Qed.Auth.Core`) -/

abbrev base64UrlEncode : ByteArray → String := Qed.Base64.encodeUrl
abbrev base64UrlDecode : String → Except String ByteArray := Qed.Base64.decodeUrl

def decodeBase64UrlJson (b64 what : String) : Except String Json := do
  let bs ← (base64UrlDecode b64).mapError (s!"{what}: invalid base64url: {·}")
  let some raw := String.fromUTF8? bs | .error s!"{what}: invalid UTF-8"
  (Json.parse raw).mapError (s!"{what}: invalid JSON: {·}")

inductive JwtAlg where | rs256 | es256 deriving Inhabited, DecidableEq
def parseJwtAlg : String → Option JwtAlg | "RS256" => some .rs256 | "ES256" => some .es256 | _ => none
theorem parseJwtAlg_rejects_none : parseJwtAlg "none" = none := rfl
theorem parseJwtAlg_rejects_hs256 : parseJwtAlg "HS256" = none := rfl

inductive JwkKey where | rsa (kid : String) (nBytes eBytes : ByteArray) | ecP256 (kid : String) (xBytes yBytes : ByteArray) deriving Inhabited
def JwkKey.kid : JwkKey → String | .rsa k _ _ | .ecP256 k _ _ => k
def JwkKey.alg : JwkKey → JwtAlg | .rsa _ _ _ => .rs256 | .ecP256 _ _ _ => .es256

def parseJwk (j : Json) : Option JwkKey := do
  let kty ← j.strAt? "kty"
  if let some u := j.strAt? "use" then guard (u == "sig")
  let kid := j.strAtD "kid"; let b64 (k : String) := (j.strAt? k).bind fun s => (base64UrlDecode s).toOption
  match kty with
  | "RSA" => let n ← b64 "n"; let e ← b64 "e"; guard (n.size >= 128 && !e.isEmpty); some (.rsa kid n e)
  | "EC"  => guard (j.strAt? "crv" == some "P-256"); let x ← b64 "x"; let y ← b64 "y"; guard (x.size == 32 && y.size == 32); some (.ecP256 kid x y)
  | _ => none
def parseJwks (j : Json) : Array JwkKey := ((j.arrAt "keys").filterMap parseJwk).toArray
def findMatchingJwk (keys : Array JwkKey) (alg : JwtAlg) (kid? : Option String) : Option JwkKey :=
  match kid? with
  | some kid => keys.find? fun k => k.alg == alg && k.kid == kid
  | none => let compat := keys.filter (·.alg == alg); if compat.size == 1 then compat[0]? else none

structure JwtHeader where (alg : JwtAlg) (kid? typ? : Option String := none) deriving Inhabited
structure CompactJwt where (signingInput : String) (signature : ByteArray) (header : JwtHeader) (payloadJson : Json)

def splitCompactJwt (token : String) : Except String (String × String × String) :=
  match token.splitOn "." with
  | [h, p, s] => if h.isEmpty || p.isEmpty || s.isEmpty then .error "jwt: empty segment" else .ok (h, p, s)
  | _ => .error "jwt: expected 3 dot-separated segments"
def parseJwtHeader (j : Json) : Except String JwtHeader := do
  let some algStr := j.strAt? "alg" | .error "jwt: missing `alg` header"
  let some alg := parseJwtAlg algStr | .error s!"jwt: disallowed algorithm `{algStr}` (only RS256 and ES256 are accepted)"
  .ok { alg, kid? := j.strAt? "kid", typ? := j.strAt? "typ" }
def parseCompactJwt (token : String) : Except String CompactJwt := do
  let (hB64, pB64, sB64) ← splitCompactJwt token
  let header ← parseJwtHeader (← decodeBase64UrlJson hB64 "jwt header")
  .ok { signingInput := hB64 ++ "." ++ pB64, signature := ← base64UrlDecode sB64, header, payloadJson := ← decodeBase64UrlJson pB64 "jwt payload" }

private def jsonToClaimString : Json → Option String
  | .str s => some s | .bool b => some (if b then "true" else "false")
  | .num n => some (if n.exponent == 0 then toString n.mantissa else Json.render (.num n)) | _ => none

structure JwtClaims where
  (iss sub : String) (aud : List String) (exp : Nat) (nbf? iat? : Option Nat := none)
  (nonce? email? : Option String := none) (emailVerified : Bool := false) (flatClaims : List (String × String) := [])
deriving Inhabited

def JwtClaims.claim (c : JwtClaims) (key : String) : Option String := Qed.lookupClaim c.flatClaims key
def parseJwtClaims (j : Json) : Except String JwtClaims := do
  let some iss := j.strAt? "iss" | .error "jwt: missing `iss` claim"
  let some sub := j.strAt? "sub" | .error "jwt: missing `sub` claim"
  let aud := match j.get? "aud" with | some (.str s) => [s] | some (.arr xs) => xs.filterMap (·.str?) | _ => []
  let some exp := j.natAt? "exp" | .error "jwt: missing or invalid `exp` claim"
  let emailVerified := (j.boolAt? "email_verified").getD false
  let rawFlat := match j with | .obj fs => fs.filterMap fun (k, v) => if k == "email_verified" then none else (jsonToClaimString v).map (k, ·) | _ => []
  .ok { iss, sub, aud, exp, nbf? := j.natAt? "nbf", iat? := j.natAt? "iat", nonce? := j.strAt? "nonce",
        email? := j.strAt? "email", emailVerified, flatClaims := rawFlat ++ [("email_verified", if emailVerified then "true" else "false")] }

structure OidcValidationCfg where
  (issuer audience : String) (clockSkewSec : Nat := 60) (expectedNonce? : Option String := none)
deriving Inhabited

structure VerifiedClaims (cfg : OidcValidationCfg) (nowSec : Nat) where
  (claims : JwtClaims) (alg : JwtAlg) (hIss : claims.iss = cfg.issuer) (hAud : cfg.audience ∈ claims.aud)
  (hNotExpired : nowSec < claims.exp + cfg.clockSkewSec) (hNbf : ∀ n, claims.nbf? = some n → n ≤ nowSec + cfg.clockSkewSec)
  (hSub : claims.sub ≠ "") (hNonce : ∀ en, cfg.expectedNonce? = some en → claims.nonce? = some en)

section JwtValidation
variable (cfg : OidcValidationCfg) (nowSec : Nat) (alg : JwtAlg) (c : JwtClaims)

def validateJwtClaims : Except String (VerifiedClaims cfg nowSec) :=
  if hIss : c.iss = cfg.issuer then
    if hAud : cfg.audience ∈ c.aud then
      if hExp : nowSec < c.exp + cfg.clockSkewSec then
        if hSub : c.sub ≠ "" then
          if hNbf : c.nbf?.all (· ≤ nowSec + cfg.clockSkewSec) then
            let hNbfPf : ∀ n, c.nbf? = some n → n ≤ nowSec + cfg.clockSkewSec := fun n hn => by simp [hn] at hNbf; exact hNbf
            match hNonceCase : cfg.expectedNonce? with
            | none => .ok ⟨c, alg, hIss, hAud, hExp, hNbfPf, hSub, fun _ h => by rw [hNonceCase] at h; cases h⟩
            | some en => if hNm : c.nonce? = some en then .ok ⟨c, alg, hIss, hAud, hExp, hNbfPf, hSub, fun _ h => by rw [hNonceCase] at h; cases h; exact hNm⟩ else .error "jwt: nonce mismatch"
          else .error "jwt: token not yet valid (`nbf`)"
        else .error "jwt: empty `sub` claim"
      else .error "jwt: token expired"
    else .error "jwt: audience mismatch"
  else .error "jwt: issuer mismatch"

private theorem validateJwtClaims_err_of (hf : ∀ vc : VerifiedClaims cfg nowSec, vc.claims = c → False) : (validateJwtClaims cfg nowSec alg c).isOk = false := by
  cases h : validateJwtClaims cfg nowSec alg c with
  | error _ => rfl
  | ok vc =>
      exfalso; apply hf vc; unfold validateJwtClaims at h
      repeat' ((try dsimp only at h); split at h <;> try cases h)
      all_goals rfl

theorem validateJwtClaims_rejects_expired (h : ¬ (nowSec < c.exp + cfg.clockSkewSec)) : (validateJwtClaims cfg nowSec alg c).isOk = false := validateJwtClaims_err_of cfg nowSec alg c fun vc hc => h (hc ▸ vc.hNotExpired)
theorem validateJwtClaims_rejects_wrong_issuer (h : c.iss ≠ cfg.issuer) : (validateJwtClaims cfg nowSec alg c).isOk = false := validateJwtClaims_err_of cfg nowSec alg c fun vc hc => h (hc ▸ vc.hIss)
theorem validateJwtClaims_rejects_wrong_audience (h : cfg.audience ∉ c.aud) : (validateJwtClaims cfg nowSec alg c).isOk = false := validateJwtClaims_err_of cfg nowSec alg c fun vc hc => h (hc ▸ vc.hAud)
theorem validateJwtClaims_rejects_empty_sub (h : c.sub = "") : (validateJwtClaims cfg nowSec alg c).isOk = false := validateJwtClaims_err_of cfg nowSec alg c fun vc hc => vc.hSub (hc ▸ h)
end JwtValidation

def isSafeReturnTo (s : String) : Bool :=
  match s.toList with
  | '/' :: '/' :: _ | '/' :: '\\' :: _ => false
  | '/' :: rest => rest.all fun c => c != '\\' && c != '\r' && c != '\n' && c != '\x00' && decide (32 ≤ c.toNat ∧ c.toNat ≠ 127)
  | _ => false
def sanitizeReturnTo (raw? : Option String) : String := match raw? with | some s => if isSafeReturnTo s then s else "/" | none => "/"
theorem isSafeReturnTo_root : isSafeReturnTo "/" = true := by decide
theorem isSafeReturnTo_rejects_protocol_relative : isSafeReturnTo "//evil.com" = false := by decide
theorem isSafeReturnTo_rejects_javascript : isSafeReturnTo "javascript:alert(1)" = false := by decide
theorem sanitizeReturnTo_safe (raw? : Option String) : isSafeReturnTo (sanitizeReturnTo raw?) = true := by
  unfold sanitizeReturnTo; cases raw? with | none => exact isSafeReturnTo_root | some s => dsimp only; split <;> simp_all [isSafeReturnTo_root]

structure SessionPayloadV2 where (userId : String) (claims : List (String × String) := []) deriving Inhabited, BEq
instance : Repr SessionPayloadV2 where reprPrec p _ := s!"\{ userId := {repr p.userId}, claims := {repr p.claims} }"

def encodeSessionPayloadV2 (p : SessionPayloadV2) : String :=
  base64UrlEncode (Json.render (Json.obj [("sub", .str p.userId), ("claims", Json.obj (p.claims.map fun (k, v) => (k, .str v)))])).toUTF8
def decodeSessionPayloadV2 (b64 : String) : Except String SessionPayloadV2 := do
  let j ← decodeBase64UrlJson b64 "session"
  let some uid := j.strAt? "sub" | .error "session: missing `sub`"
  if uid.isEmpty then .error "session: empty `sub`"
  else .ok { userId := uid, claims := match j.get? "claims" with | some (.obj kvs) => kvs.filterMap fun (k, v) => v.str?.map (k, ·) | _ => [] }

abbrev parseQueryParams : String → List (String × String) := Qed.parseQueryParams
abbrev encodeFormBody : List (String × String) → String := Qed.encodeFormBody
def mkAuthActionUrl (pfx : String) (returnTo : Qed.HrefTarget := Qed.HrefTarget.root) : Qed.Url :=
  (Qed.Url.parse? (pfx ++ Qed.encodeSeg (sanitizeReturnTo (some returnTo.raw)))).getD Qed.Url.root

structure AuthClaimSpec where (name typeName : String) (defaultValue : String := "") deriving Inhabited

structure OidcAuthSpec where
  (name : String) (isManaged : Bool := false)
  (issuerEnv : String := "QED_AUTH_ISSUER") (issuerDefault? : Option String := none)
  (audienceEnv : String := "QED_AUTH_AUDIENCE") (audienceDefault? : Option String := none)
  (clientIdEnv? : Option String := some "QED_AUTH_CLIENT_ID") (clientIdDefault? clientSecretEnv? : Option String := none)
  (providers : List String := []) (sessionTtlSec : Nat := 86400)
  (loginPath : String := "/_qed/auth/login") (callbackPath : String := "/_qed/auth/callback")
  (logoutPath : String := "/_qed/auth/logout") (mePath : String := "/_qed/auth/me") (claims : List AuthClaimSpec := [])
deriving Inhabited

def parseBoolClaim (raw? : Option String) (defaultVal : Bool := false) : Bool := match raw? with | some "true" | some "1" => true | some "false" | some "0" => false | _ => defaultVal
def parseNatClaim (raw? : Option String) (defaultVal : Nat := 0) : Nat := (raw?.bind String.toNat?).getD defaultVal
def parseIntClaim (raw? : Option String) (defaultVal : Int := 0) : Int := (raw?.bind String.toInt?).getD defaultVal
theorem option_map_eq_some_elim {α β : Type} {o : Option α} {f : α → β} {b : β} {P : Prop} (h : o.map f = some b) (k : ∀ a, o = some a → f a = b → P) : P := by
  cases o with | none => cases h | some a => cases h; exact k a rfl rfl

end Qed.Auth
