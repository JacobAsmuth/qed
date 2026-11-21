import Qed.Base64
import Qed.Json
import Qed.Proto
import Qed.Html
import Qed.Router.Basic

namespace Qed.Auth

/-! ## Pure, Total, Kernel-Verified OIDC / JWT / JWKS Core (`Qed.Auth.Core`)
    Implements RFC 7519 (JWT), RFC 7517 (JWK/JWKS), RFC 7636 (PKCE), and safe redirect
    validation in pure, total Lean 4 with kernel-checked security invariants:
    - Structurally forbids `alg: "none"` and symmetric `HS256` key-confusion attacks.
    - Enforces `iss`, `aud`, `exp`, `nbf`, `nonce`, and non-empty `sub` via `VerifiedClaims`.
    - Proves OAuth `returnTo` paths are strictly root-relative and CRLF/scheme-free. -/

/-! ### Verified RFC 4648 Base64URL (Unpadded) -/

abbrev toUrlChar : Char → Char := Qed.Base64.toUrlChar
abbrev fromUrlChar : Char → Char := Qed.Base64.fromUrlChar

theorem fromUrlChar_toUrlChar (c : Char) (h1 : c ≠ '-') (h2 : c ≠ '_') :
    fromUrlChar (toUrlChar c) = c := by
  by_cases hp : c = '+'
  · subst hp; rfl
  · by_cases hs : c = '/'
    · subst hs; rfl
    · simp [toUrlChar, fromUrlChar, Qed.Base64.toUrlChar, Qed.Base64.fromUrlChar]

/-- Encodes bytes to RFC 4648 unpadded Base64URL (used for JWS, JWK, and PKCE S256). -/
abbrev base64UrlEncode : ByteArray → String := Qed.Base64.encodeUrl

/-- Decodes RFC 4648 Base64URL (padded or unpadded) into raw bytes. -/
abbrev base64UrlDecode : String → Except String ByteArray := Qed.Base64.decodeUrl

/-! ### Strict Asymmetric JWT Algorithm Allowlist (Zero `alg: none` / `HS256` Confusion) -/

/-- Permitted OIDC JWS signature algorithms: strictly asymmetric public-key algorithms. -/
inductive JwtAlg where
  | rs256
  | es256
deriving Inhabited, DecidableEq, Repr

def JwtAlg.toString : JwtAlg → String
  | .rs256 => "RS256"
  | .es256 => "ES256"

def parseJwtAlg : String → Option JwtAlg
  | "RS256" => some .rs256
  | "ES256" => some .es256
  | _       => none

theorem parseJwtAlg_rejects_none : parseJwtAlg "none" = none := rfl
theorem parseJwtAlg_rejects_None : parseJwtAlg "None" = none := rfl
theorem parseJwtAlg_rejects_NONE : parseJwtAlg "NONE" = none := rfl
theorem parseJwtAlg_rejects_hs256 : parseJwtAlg "HS256" = none := rfl
theorem parseJwtAlg_rejects_hs384 : parseJwtAlg "HS384" = none := rfl
theorem parseJwtAlg_rejects_hs512 : parseJwtAlg "HS512" = none := rfl
theorem parseJwtAlg_rejects_empty : parseJwtAlg "" = none := rfl

/-! ### RFC 7517 JWK & JWKS Parsing -/

inductive JwkKey where
  | rsa    (kid : String) (nBytes eBytes : ByteArray)
  | ecP256 (kid : String) (xBytes yBytes : ByteArray)
deriving Inhabited

def JwkKey.kid : JwkKey → String
  | .rsa k _ _    => k
  | .ecP256 k _ _ => k

def JwkKey.alg : JwkKey → JwtAlg
  | .rsa _ _ _    => .rs256
  | .ecP256 _ _ _ => .es256

def parseJwk (j : Json) : Option JwkKey := do
  let kty ← (j.get? "kty").bind (·.str?)
  -- Reject encryption-only keys (`use: "enc"`).
  if let some useStr := (j.get? "use").bind (·.str?) then
    if useStr != "sig" then none
  let kid := ((j.get? "kid").bind (·.str?)).getD ""
  if kty == "RSA" then
    let nStr ← (j.get? "n").bind (·.str?)
    let eStr ← (j.get? "e").bind (·.str?)
    let nBytes ← (base64UrlDecode nStr).toOption
    let eBytes ← (base64UrlDecode eStr).toOption
    if nBytes.size >= 128 && !eBytes.isEmpty then
      some (.rsa kid nBytes eBytes)
    else none
  else if kty == "EC" then
    let crv ← (j.get? "crv").bind (·.str?)
    if crv != "P-256" then none
    let xStr ← (j.get? "x").bind (·.str?)
    let yStr ← (j.get? "y").bind (·.str?)
    let xBytes ← (base64UrlDecode xStr).toOption
    let yBytes ← (base64UrlDecode yStr).toOption
    if xBytes.size == 32 && yBytes.size == 32 then
      some (.ecP256 kid xBytes yBytes)
    else none
  else
    none

def parseJwks (j : Json) : Array JwkKey :=
  match j.get? "keys" with
  | some (.arr items) =>
      items.foldl (init := #[]) fun acc item =>
        match parseJwk item with
        | some k => acc.push k
        | none   => acc
  | _ => #[]

def findMatchingJwk (keys : Array JwkKey) (alg : JwtAlg) (kid? : Option String) : Option JwkKey :=
  match kid? with
  | some kid =>
      keys.find? fun k => k.alg == alg && k.kid == kid
  | none =>
      let compat := keys.filter fun k => k.alg == alg
      if compat.size == 1 then compat[0]? else none

/-! ### RFC 7519 JWT Parsing & Kernel-Verified Claim Validation -/

structure JwtHeader where
  alg  : JwtAlg
  kid? : Option String := none
  typ? : Option String := none
deriving Inhabited, DecidableEq, Repr

structure CompactJwt where
  headerB64    : String
  payloadB64   : String
  signingInput : String
  signature    : ByteArray
  header       : JwtHeader
  payloadJson  : Json

def splitCompactJwt (token : String) : Except String (String × String × String) :=
  match token.splitOn "." with
  | [h, p, s] =>
      if h.isEmpty || p.isEmpty || s.isEmpty then
        .error "jwt: empty segment"
      else
        .ok (h, p, s)
  | _ => .error "jwt: expected 3 dot-separated segments"

def parseJwtHeader (j : Json) : Except String JwtHeader := do
  let some algStr := (j.get? "alg").bind (·.str?)
    | .error "jwt: missing `alg` header"
  let some alg := parseJwtAlg algStr
    | .error s!"jwt: disallowed algorithm `{algStr}` (only RS256 and ES256 are accepted)"
  let kid? := (j.get? "kid").bind (·.str?)
  let typ? := (j.get? "typ").bind (·.str?)
  .ok { alg, kid?, typ? }

def parseCompactJwt (token : String) : Except String CompactJwt := do
  let (hB64, pB64, sB64) ← splitCompactJwt token
  let hBytes ← base64UrlDecode hB64
  let pBytes ← base64UrlDecode pB64
  let sig    ← base64UrlDecode sB64
  let some hStr := String.fromUTF8? hBytes
    | .error "jwt: invalid UTF-8 in header"
  let some pStr := String.fromUTF8? pBytes
    | .error "jwt: invalid UTF-8 in payload"
  let hJson ← Json.parse hStr
  let pJson ← Json.parse pStr
  let header ← parseJwtHeader hJson
  .ok {
    headerB64    := hB64
    payloadB64   := pB64
    signingInput := hB64 ++ "." ++ pB64
    signature    := sig
    header
    payloadJson  := pJson
  }

private def jsonToClaimString : Json → Option String
  | .str s  => some s
  | .bool b => some (if b then "true" else "false")
  | .num n  => if n.exponent == 0 then some (toString n.mantissa) else some (Json.render (.num n))
  | _       => none

private def extractFlatClaims : Json → List (String × String)
  | .obj fields =>
      fields.foldl (init := []) fun acc (k, v) =>
        match jsonToClaimString v with
        | some s => acc ++ [(k, s)]
        | none   => acc
  | _ => []

private def jsonToNatOpt : Json → Option Nat
  | .num n => if n.exponent == 0 && n.mantissa >= 0 then some n.mantissa.toNat else none
  | _      => none

private def parseAudField : Json → List String
  | .str s  => [s]
  | .arr xs => xs.foldl (init := []) fun acc x => match x with | .str s => acc ++ [s] | _ => acc
  | _       => []

structure JwtClaims where
  iss           : String
  sub           : String
  aud           : List String
  exp           : Nat
  nbf?          : Option Nat := none
  iat?          : Option Nat := none
  nonce?        : Option String := none
  email?        : Option String := none
  emailVerified : Bool := false
  flatClaims    : List (String × String) := []
deriving Inhabited, DecidableEq, Repr

def JwtClaims.claim (c : JwtClaims) (key : String) : Option String :=
  let direct := (c.flatClaims.find? fun (k, _) => k == key).map Prod.snd
  if direct.isSome then direct
  else if key == "verified" then
    (c.flatClaims.find? fun (k, _) => k == "email_verified").map Prod.snd
  else none

def parseJwtClaims (j : Json) : Except String JwtClaims := do
  let some iss := (j.get? "iss").bind (·.str?)
    | .error "jwt: missing `iss` claim"
  let some sub := (j.get? "sub").bind (·.str?)
    | .error "jwt: missing `sub` claim"
  let aud := match j.get? "aud" with | some v => parseAudField v | none => []
  let some exp := (j.get? "exp").bind jsonToNatOpt
    | .error "jwt: missing or invalid `exp` claim"
  let nbf? := (j.get? "nbf").bind jsonToNatOpt
  let iat? := (j.get? "iat").bind jsonToNatOpt
  let nonce? := (j.get? "nonce").bind (·.str?)
  let email? := (j.get? "email").bind (·.str?)
  let emailVerified := match (j.get? "email_verified") with | some (.bool b) => b | _ => false
  .ok {
    iss, sub, aud, exp, nbf?, iat?, nonce?, email?, emailVerified
    flatClaims := extractFlatClaims j
  }

structure OidcValidationCfg where
  issuer         : String
  audience       : String
  clockSkewSec   : Nat := 60
  expectedNonce? : Option String := none
deriving Inhabited, DecidableEq, Repr

/-- Proof-carrying verified JWT claims: can only be constructed after passing issuer,
    audience, expiry, not-before, non-empty subject, and optional nonce validation. -/
structure VerifiedClaims (cfg : OidcValidationCfg) (nowSec : Nat) where
  claims      : JwtClaims
  alg         : JwtAlg
  hIss        : claims.iss = cfg.issuer
  hAud        : cfg.audience ∈ claims.aud
  hNotExpired : nowSec < claims.exp + cfg.clockSkewSec
  hNbf        : ∀ n, claims.nbf? = some n → n ≤ nowSec + cfg.clockSkewSec
  hSub        : claims.sub ≠ ""
  hNonce      : ∀ en, cfg.expectedNonce? = some en → claims.nonce? = some en

def validateJwtClaims (cfg : OidcValidationCfg) (nowSec : Nat) (alg : JwtAlg) (c : JwtClaims) :
    Except String (VerifiedClaims cfg nowSec) :=
  if hIss : c.iss = cfg.issuer then
    if hAud : cfg.audience ∈ c.aud then
      if hExp : nowSec < c.exp + cfg.clockSkewSec then
        if hSub : c.sub ≠ "" then
          match hNbfCase : c.nbf? with
          | some n =>
              if hNbfLe : n ≤ nowSec + cfg.clockSkewSec then
                match hNonceCase : cfg.expectedNonce? with
                | none =>
                    .ok ⟨c, alg, hIss, hAud, hExp,
                      (fun m hm => by rw [hNbfCase] at hm; cases hm; exact hNbfLe),
                      hSub, (fun _ h => by rw [hNonceCase] at h; cases h)⟩
                | some en =>
                    if hNm : c.nonce? = some en then
                      .ok ⟨c, alg, hIss, hAud, hExp,
                        (fun m hm => by rw [hNbfCase] at hm; cases hm; exact hNbfLe),
                        hSub, (fun _ h => by rw [hNonceCase] at h; cases h; exact hNm)⟩
                    else .error "jwt: nonce mismatch"
              else .error "jwt: token not yet valid (`nbf`)"
          | none =>
              match hNonceCase : cfg.expectedNonce? with
              | none =>
                  .ok ⟨c, alg, hIss, hAud, hExp,
                    (fun _ hm => by rw [hNbfCase] at hm; cases hm),
                    hSub, (fun _ h => by rw [hNonceCase] at h; cases h)⟩
              | some en =>
                  if hNm : c.nonce? = some en then
                    .ok ⟨c, alg, hIss, hAud, hExp,
                      (fun _ hm => by rw [hNbfCase] at hm; cases hm),
                      hSub, (fun _ h => by rw [hNonceCase] at h; cases h; exact hNm)⟩
                  else .error "jwt: nonce mismatch"
        else .error "jwt: empty `sub` claim"
      else .error "jwt: token expired"
    else .error "jwt: audience mismatch"
  else .error "jwt: issuer mismatch"

theorem validateJwtClaims_rejects_expired (cfg : OidcValidationCfg) (nowSec : Nat) (alg : JwtAlg) (c : JwtClaims)
    (hExp : ¬ (nowSec < c.exp + cfg.clockSkewSec)) :
    (validateJwtClaims cfg nowSec alg c).isOk = false := by
  unfold validateJwtClaims
  by_cases h1 : c.iss = cfg.issuer
  · simp only [dif_pos h1]
    by_cases h2 : cfg.audience ∈ c.aud
    · simp only [dif_pos h2, dif_neg hExp]; rfl
    · simp only [dif_neg h2]; rfl
  · simp only [dif_neg h1]; rfl

theorem validateJwtClaims_rejects_wrong_issuer (cfg : OidcValidationCfg) (nowSec : Nat) (alg : JwtAlg) (c : JwtClaims)
    (hNe : c.iss ≠ cfg.issuer) :
    (validateJwtClaims cfg nowSec alg c).isOk = false := by
  unfold validateJwtClaims
  rw [dif_neg hNe]; rfl

theorem validateJwtClaims_rejects_wrong_audience (cfg : OidcValidationCfg) (nowSec : Nat) (alg : JwtAlg) (c : JwtClaims)
    (hNotIn : cfg.audience ∉ c.aud) :
    (validateJwtClaims cfg nowSec alg c).isOk = false := by
  unfold validateJwtClaims
  by_cases h1 : c.iss = cfg.issuer
  · simp only [dif_pos h1, dif_neg hNotIn]; rfl
  · simp only [dif_neg h1]; rfl

theorem validateJwtClaims_rejects_empty_sub (cfg : OidcValidationCfg) (nowSec : Nat) (alg : JwtAlg) (c : JwtClaims)
    (hEmpty : c.sub = "") :
    (validateJwtClaims cfg nowSec alg c).isOk = false := by
  unfold validateJwtClaims
  by_cases h1 : c.iss = cfg.issuer
  · simp only [dif_pos h1]
    by_cases h2 : cfg.audience ∈ c.aud
    · simp only [dif_pos h2]
      by_cases h3 : nowSec < c.exp + cfg.clockSkewSec
      · have hne : ¬ (c.sub ≠ "") := fun h => h hEmpty
        simp only [dif_pos h3, dif_neg hne]; rfl
      · simp only [dif_neg h3]; rfl
    · simp only [dif_neg h2]; rfl
  · simp only [dif_neg h1]; rfl

/-! ### Safe Post-Login Redirect Validation (`isSafeReturnTo`, Zero Open Redirects) -/

private def isSafeReturnToChar (c : Char) : Bool :=
  c != '\\' && c != '\r' && c != '\n' && c != '\x00' &&
  decide (32 ≤ c.toNat ∧ c.toNat ≠ 127)

/-- True iff `s` is a strictly root-relative path (`/foo?a=1#b`): starts with `/`,
    is not protocol-relative (`//`), contains no backslashes, control chars, or CRLF. -/
def isSafeReturnTo (s : String) : Bool :=
  match s.toList with
  | '/' :: '/' :: _  => false
  | '/' :: '\\' :: _ => false
  | '/' :: rest      => rest.all isSafeReturnToChar
  | _                => false

def sanitizeReturnTo (raw? : Option String) : String :=
  match raw? with
  | some s => if isSafeReturnTo s then s else "/"
  | none   => "/"

theorem isSafeReturnTo_root : isSafeReturnTo "/" = true := by decide
theorem isSafeReturnTo_rejects_protocol_relative : isSafeReturnTo "//evil.com" = false := by decide
theorem isSafeReturnTo_rejects_https : isSafeReturnTo "https://evil.com" = false := by decide
theorem isSafeReturnTo_rejects_javascript : isSafeReturnTo "javascript:alert(1)" = false := by decide
theorem isSafeReturnTo_rejects_backslash : isSafeReturnTo "/\\evil.com" = false := by decide
theorem isSafeReturnTo_rejects_crlf : isSafeReturnTo "/ok\r\nSet-Cookie: x=1" = false := by decide

theorem sanitizeReturnTo_safe (raw? : Option String) :
    isSafeReturnTo (sanitizeReturnTo raw?) = true := by
  unfold sanitizeReturnTo
  cases raw? with
  | none => exact isSafeReturnTo_root
  | some s =>
      by_cases h : isSafeReturnTo s = true
      · simp [h]
      · simp [h, isSafeReturnTo_root]

/-! ### Signed `v2` Session Cookie Payload Codec (Carrying Verified User ID + Claims) -/

structure SessionPayloadV2 where
  userId : String
  claims : List (String × String) := []
deriving Inhabited, DecidableEq, Repr

def encodeSessionPayloadV2 (p : SessionPayloadV2) : String :=
  let claimObj := Json.obj (p.claims.map fun (k, v) => (k, Json.str v))
  let j := Json.obj [("sub", Json.str p.userId), ("claims", claimObj)]
  base64UrlEncode (Json.render j).toUTF8

def decodeSessionPayloadV2 (b64 : String) : Except String SessionPayloadV2 := do
  let bs ← base64UrlDecode b64
  let some raw := String.fromUTF8? bs
    | .error "session: invalid UTF-8"
  let j ← Json.parse raw
  let some uid := (j.get? "sub").bind (·.str?)
    | .error "session: missing `sub`"
  if uid.isEmpty then .error "session: empty `sub`"
  else
    let claims := match j.get? "claims" with
      | some (.obj kvs) =>
          kvs.foldl (init := []) fun acc (k, v) =>
            match v with | .str s => acc ++ [(k, s)] | _ => acc
      | _ => []
    .ok { userId := uid, claims }

/-! ### URL Query / Form-URLEncoded Helpers (Pure, Total) -/

abbrev urlEncodeComponent : String → String := Qed.encodeSeg

def urlDecodeComponent (s : String) : String :=
  (String.fromUTF8? (Qed.decodeBytes (s.replace "+" " ").toList .empty)).getD s

def parseQueryParams (q : String) : List (String × String) :=
  let trimmed := if q.startsWith "?" then String.ofList (q.toList.drop 1) else q
  if trimmed.isEmpty then []
  else
    (trimmed.splitOn "&").foldl (init := []) fun acc pair =>
      if pair.isEmpty then acc
      else match pair.splitOn "=" with
        | []       => acc
        | [k]      => acc ++ [(urlDecodeComponent k, "")]
        | k :: vs  => acc ++ [(urlDecodeComponent k, urlDecodeComponent (String.intercalate "=" vs))]

def encodeFormBody (pairs : List (String × String)) : String :=
  String.intercalate "&" (pairs.map fun (k, v) => urlEncodeComponent k ++ "=" ++ urlEncodeComponent v)

/-! ### Declarative `auth` Runtime Specification (`OidcAuthSpec`) -/

structure AuthClaimSpec where
  name         : String
  typeName     : String -- "String" | "Bool" | "Nat" | "Int" | "Option String"
  defaultValue : String := ""
deriving Inhabited, DecidableEq, Repr

/-- Server-side OIDC configuration generated by an `auth <Name>:` block.
    Never bundled into client JS (`Js.VerifyEnv.clientLeakReason?`). -/
structure OidcAuthSpec where
  name             : String
  issuerEnv        : String := "QED_AUTH_ISSUER"
  issuerDefault?   : Option String := none
  audienceEnv      : String := "QED_AUTH_AUDIENCE"
  audienceDefault? : Option String := none
  clientIdEnv?     : Option String := some "QED_AUTH_CLIENT_ID"
  clientIdDefault? : Option String := none
  clientSecretEnv? : Option String := none
  providers        : List String := []
  sessionTtlSec    : Nat := 86400
  loginPath        : String := "/_qed/auth/login"
  callbackPath     : String := "/_qed/auth/callback"
  logoutPath       : String := "/_qed/auth/logout"
  mePath           : String := "/_qed/auth/me"
  claims           : List AuthClaimSpec := []
deriving Inhabited, DecidableEq, Repr

/-- Typed claim extraction helper for generated `<Auth>.User` decoders and server policies. -/
def parseBoolClaim (raw? : Option String) (defaultVal : Bool := false) : Bool :=
  match raw? with
  | some "true" | some "1" => true
  | some "false" | some "0" => false
  | _ => defaultVal

def parseNatClaim (raw? : Option String) (defaultVal : Nat := 0) : Nat :=
  (raw?.bind String.toNat?).getD defaultVal

def parseIntClaim (raw? : Option String) (defaultVal : Int := 0) : Int :=
  (raw?.bind String.toInt?).getD defaultVal

end Qed.Auth
