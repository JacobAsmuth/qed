import Qed.Json.Lawful
import Qed.Proto
import Qed.Router.Basic
import Qed.Collection

namespace Qed.Server

/-! ## Structured Server Errors (`ApiError` & `fail`) -/

structure ApiError where
  code    : Nat := 400
  message : String
deriving Inhabited, DecidableEq, Repr

namespace ApiError

def badRequest   (msg : String) : ApiError := { code := 400, message := msg }
def unauthorized (msg : String := "unauthorized") : ApiError := { code := 401, message := msg }
def forbidden    (msg : String := "forbidden") : ApiError := { code := 403, message := msg }
def notFound     (msg : String := "not found") : ApiError := { code := 404, message := msg }
def internal     (msg : String) : ApiError := { code := 500, message := msg }

def httpStatus (e : ApiError) : UInt32 :=
  if 400 ≤ e.code && e.code < 600 then e.code.toUInt32 else 400

instance : ToString ApiError := ⟨fun e => e.message⟩

instance : ToJson ApiError where
  toJson e := toJson (e.code, e.message)

instance : FromJson ApiError where
  fromJson j := (FromJson.fromJson (α := Nat × String) j).map fun p => ApiError.mk p.1 p.2

instance : LawfulJson ApiError where
  depthBound := LawfulJson.depthBound (Nat × String)
  depth_toJson e := LawfulJson.depth_toJson (e.code, e.message)
  fromJson_toJson e := by
    rcases e with ⟨c, m⟩
    change (FromJson.fromJson (toJson (c, m)) : Except String (Nat × String)).map
      (fun p => ApiError.mk p.1 p.2) = .ok (ApiError.mk c m)
    rw [LawfulJson.fromJson_toJson (c, m)]
    rfl

instance : NonNullJson ApiError := ⟨nofun⟩

instance : ToProto ApiError   := .ofEquiv fun e => (e.code, e.message)
instance : FromProto ApiError := .ofEquiv fun p : Nat × String => ApiError.mk p.1 p.2
instance : LawfulProto ApiError := .ofEquiv (fun e => (e.code, e.message)) (fun p => ApiError.mk p.1 p.2) (fun ⟨_, _⟩ => rfl)

end ApiError

/-! ## Request Context (`RequestCtx`) -/

structure RequestCtx where
  headers     : List (String × String) := []
  cookies     : List (String × String) := []
  bearerToken : Option String := none
  userId      : Option String := none
  clientIp    : String := "127.0.0.1"
  connId      : String := ""
deriving Inhabited, DecidableEq, Repr

namespace RequestCtx

def header (ctx : RequestCtx) (name : String) : Option String :=
  let target := name.toLower
  (ctx.headers.find? fun (k, _) => k.toLower == target).map Prod.snd

def cookie (ctx : RequestCtx) (name : String) : Option String :=
  (ctx.cookies.find? fun (k, _) => k == name).map Prod.snd

def isAuthenticated (ctx : RequestCtx) : Bool :=
  ctx.userId.isSome || ctx.bearerToken.isSome

end RequestCtx

/-! ## Validated HTTPS Webhook URLs (`WebhookUrl`) -/

abbrev isValidWebhookUrl (s : String) : Bool :=
  s.startsWith "https://" &&
  decide (8 < s.length) &&
  !s.startsWith "https:///" &&
  s.toList.all (fun c => isSafeUrlChar c && c != '\\' && decide (32 < c.toNat ∧ c.toNat ≠ 127))

structure WebhookUrl where
  raw   : String
  valid : isValidWebhookUrl raw = true
deriving DecidableEq, Repr

instance : ToString WebhookUrl := ⟨WebhookUrl.raw⟩

instance : ToJson WebhookUrl where
  toJson u := toJson u.raw

instance : FromJson WebhookUrl where
  fromJson j := do
    let s ← (FromJson.fromJson j : Except String String)
    if h : isValidWebhookUrl s = true then .ok (WebhookUrl.mk s h)
    else .error "invalid WebhookUrl: must be a well-formed https:// URL"

instance : LawfulJson WebhookUrl where
  depthBound := 0
  depth_toJson _ := Nat.le_refl 0
  fromJson_toJson u := by
    rcases u with ⟨raw, hv⟩
    change (FromJson.fromJson (toJson raw) : Except String String).bind
      (fun s => if h : isValidWebhookUrl s = true then .ok (WebhookUrl.mk s h) else .error _) =
        .ok (WebhookUrl.mk raw hv)
    rw [LawfulJson.fromJson_toJson raw]
    dsimp only [bind, Except.bind]
    rw [dif_pos hv]

instance : NonNullJson WebhookUrl := ⟨nofun⟩

instance : ToProto WebhookUrl where
  toProtoVal u := ToProto.toProtoVal u.raw

instance : FromProto WebhookUrl where
  fromProtoVal w := do
    let s ← FromProto.fromProtoVal (α := String) w
    if h : isValidWebhookUrl s = true then .ok (WebhookUrl.mk s h)
    else .error "invalid WebhookUrl: must be a well-formed https:// URL"

instance : LawfulProto WebhookUrl :=
  .ofScalar fun ⟨raw, hv⟩ => by
    change (FromProto.fromProtoVal (ToProto.toProtoVal raw) : Except String String).bind
      (fun s => if h : isValidWebhookUrl s = true then .ok (WebhookUrl.mk s h) else .error _) =
        .ok (WebhookUrl.mk raw hv)
    rw [LawfulProto.fromProtoVal_toProtoVal raw]
    dsimp only [bind, Except.bind]
    rw [dif_pos hv]

/-! ## CRLF Header Injection Closure (`sanitizeHeader` & `header_no_crlf`) -/

@[inline] def isSafeHeaderChar (c : Char) : Bool :=
  let n := c.toNat
  32 ≤ n && n ≠ 127

def sanitizeHeader (s : String) : String :=
  String.ofList (s.toList.filter isSafeHeaderChar)

theorem header_no_crlf (s : String) :
    ∀ c ∈ (sanitizeHeader s).toList, c ≠ '\r' ∧ c ≠ '\n' ∧ c ≠ '\x00' := by
  intro c hc
  unfold sanitizeHeader at hc
  rw [String.toList_ofList, List.mem_filter] at hc
  rcases hc with ⟨_, hsafe⟩
  unfold isSafeHeaderChar at hsafe
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsafe
  refine ⟨?_, ?_, ?_⟩ <;> (intro heq; subst heq; simp at hsafe)

/-! ## SSRF Origin-Pinning & Path-Traversal Closure (`external_url_preserves_origin`) -/

abbrev isSafeSegChar : Char → Bool := Qed.isPctEncodedChar

@[inline] def isSafeExtSuffixChar (c : Char) : Bool :=
  isSafeSegChar c || c == '/' || c == '?' || c == '&' || c == '=' || c == ':' || c == '+' || c == ','

abbrev pctEncode : String → String := Qed.encodeSeg

theorem pctEncode_safe (s : String) :
    (pctEncode s).toList.all isSafeSegChar = true :=
  Qed.encodeSeg_pct s

theorem isSafeExtSuffixChar_no_smuggle {c : Char} (h : isSafeExtSuffixChar c = true) :
    c ≠ '#' ∧ c ≠ '\\' ∧ c ≠ '\r' ∧ c ≠ '\n' ∧ c ≠ '\x00' ∧ c ≠ '@' := by
  unfold isSafeExtSuffixChar isSafeSegChar Qed.isPctEncodedChar at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro heq; subst heq; simp at h)

private theorem safeSeg_implies_extSuffix {s : String} (h : s.toList.all isSafeSegChar = true) :
    s.toList.all isSafeExtSuffixChar = true := by
  rw [List.all_eq_true] at h ⊢
  intro c hc
  unfold isSafeExtSuffixChar
  simp [h c hc]

private def rawSingleSeg (s : String) : String :=
  if s == "." then "%2E" else if s == ".." then "%2E%2E" else pctEncode s

private theorem rawSingleSeg_safe (s : String) :
    (rawSingleSeg s).toList.all isSafeSegChar = true := by
  unfold rawSingleSeg
  by_cases h1 : s == "."
  · simp [h1]; decide
  · by_cases h2 : s == ".."
    · simp [h1, h2]; decide
    · simp [h1, h2, pctEncode_safe]

/-- Encodes a single `:param` URL segment, rejecting empty segments and neutralizing `.` / `..`. -/
def encodeSingleSeg (s : String) : Except ApiError String :=
  let enc := rawSingleSeg s
  if enc.isEmpty || enc == "." || enc == ".." then
    .error (ApiError.badRequest "URL path segment cannot be empty or dot-traversal")
  else
    .ok enc

theorem encodeSingleSeg_safe {s out : String} (h : encodeSingleSeg s = .ok out) :
    out ≠ "" ∧ out ≠ "." ∧ out ≠ ".." ∧ out.toList.all isSafeSegChar = true := by
  unfold encodeSingleSeg at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i hbad
    injection h with h; subst h
    simp only [Bool.or_eq_true, String.isEmpty_iff, beq_iff_eq, not_or] at hbad
    exact ⟨hbad.1.1, hbad.1.2, hbad.2, rawSingleSeg_safe s⟩

private def encodeMultiSegList : List String → Except ApiError String
  | [] => .error (ApiError.badRequest "multi-segment URL path cannot be empty")
  | [seg] =>
      if seg.isEmpty || seg == "." || seg == ".." then
        .error (ApiError.badRequest "invalid multi-segment URL path component")
      else
        encodeSingleSeg seg
  | seg :: s2 :: rest =>
      if seg.isEmpty || seg == "." || seg == ".." then
        .error (ApiError.badRequest "invalid multi-segment URL path component")
      else do
        let headEnc ← encodeSingleSeg seg
        let tailEnc ← encodeMultiSegList (s2 :: rest)
        return headEnc ++ "/" ++ tailEnc

private theorem encodeMultiSegList_safe :
    ∀ (segs : List String) (out : String),
      encodeMultiSegList segs = .ok out →
      out.toList.all isSafeExtSuffixChar = true
  | [], _, h => by unfold encodeMultiSegList at h; contradiction
  | [seg], _, h => by
      unfold encodeMultiSegList at h
      split at h
      · contradiction
      · exact safeSeg_implies_extSuffix (encodeSingleSeg_safe h).2.2.2
  | seg :: s2 :: rest, _, h => by
      unfold encodeMultiSegList at h
      split at h
      · contradiction
      · dsimp only [bind, Except.bind, pure, Except.pure] at h
        cases h1 : encodeSingleSeg seg with
        | error _ => rw [h1] at h; contradiction
        | ok hd =>
            rw [h1] at h
            dsimp only at h
            cases h2 : encodeMultiSegList (s2 :: rest) with
            | error _ => rw [h2] at h; contradiction
            | ok tl =>
                rw [h2] at h
                injection h with h; subst h
                have hhd := safeSeg_implies_extSuffix (encodeSingleSeg_safe h1).2.2.2
                have htl := encodeMultiSegList_safe (s2 :: rest) tl h2
                have hsl : isSafeExtSuffixChar '/' = true := rfl
                simp [String.toList_append, hhd, htl, hsl]

/-- Encodes a `:path*` slash-delimited path while rejecting empty, `.`, and `..` traversal segments. -/
def encodeMultiSeg (s : String) : Except ApiError String :=
  let trimmed := match s.toList with
    | '/' :: cs => String.ofList cs
    | _         => s
  encodeMultiSegList (trimmed.splitOn "/")

theorem encodeMultiSeg_safe {s out : String} (h : encodeMultiSeg s = .ok out) :
    out.toList.all isSafeExtSuffixChar = true :=
  encodeMultiSegList_safe _ out h

inductive PathPart where
  | lit (seg : String)
  | seg (val : String)
  | multiSeg (val : String)
deriving Inhabited, DecidableEq, Repr

inductive QueryVal where
  | lit (val : String)
  | param (val : String)
deriving Inhabited, DecidableEq, Repr

def isValidBaseOrigin (base : String) : Bool :=
  (base.startsWith "https://" || base.startsWith "http://") &&
  !base.endsWith "/" &&
  base.toList.all (fun c =>
    isSafeUrlChar c && c != '?' && c != '#' && c != '\\' && c != '@' &&
    decide (32 < c.toNat ∧ c.toNat ≠ 127))

def isValidWsBaseOrigin (base : String) : Bool :=
  (base.startsWith "wss://" || base.startsWith "ws://" ||
   base.startsWith "https://" || base.startsWith "http://") &&
  !base.endsWith "/" &&
  base.toList.all (fun c =>
    isSafeUrlChar c && c != '?' && c != '#' && c != '\\' && c != '@' &&
    decide (32 < c.toNat ∧ c.toNat ≠ 127))

def toWsOrigin (base : String) : String :=
  if base.startsWith "https://" then "wss://" ++ String.ofList (base.toList.drop 8)
  else if base.startsWith "http://" then "ws://" ++ String.ofList (base.toList.drop 7)
  else base

private def renderPathParts : List PathPart → Except ApiError (List String)
  | [] => .ok []
  | .lit s :: rest =>
      if !s.isEmpty && s != "." && s != ".." && s.toList.all isSafeSegChar then do
        let tl ← renderPathParts rest
        return s :: tl
      else
        .error (ApiError.internal "invalid static path literal in external endpoint")
  | .seg v :: rest => do
      let hd ← encodeSingleSeg v
      let tl ← renderPathParts rest
      return hd :: tl
  | .multiSeg v :: rest => do
      let hd ← encodeMultiSeg v
      let tl ← renderPathParts rest
      return hd :: tl

private theorem renderPathParts_safe :
    ∀ (ps : List PathPart) (segs : List String),
      renderPathParts ps = .ok segs →
      ∀ seg ∈ segs, seg.toList.all isSafeExtSuffixChar = true
  | [], _, h => by
      injection h with h; subst h; intro _ hm; exact False.elim (List.not_mem_nil hm)
  | .lit s :: rest, _, h => by
      unfold renderPathParts at h
      split at h
      · rename_i hok
        dsimp only [bind, Except.bind, pure, Except.pure] at h
        cases hr : renderPathParts rest with
        | error _ => rw [hr] at h; contradiction
        | ok tl =>
            rw [hr] at h; injection h with h; subst h
            intro seg hm
            rcases List.mem_cons.1 hm with rfl | htl
            · simp only [Bool.and_eq_true] at hok
              exact safeSeg_implies_extSuffix hok.2
            · exact renderPathParts_safe rest tl hr seg htl
      · contradiction
  | .seg v :: rest, _, h => by
      unfold renderPathParts at h
      dsimp only [bind, Except.bind, pure, Except.pure] at h
      cases h1 : encodeSingleSeg v with
      | error _ => rw [h1] at h; contradiction
      | ok hd =>
          rw [h1] at h; dsimp only at h
          cases hr : renderPathParts rest with
          | error _ => rw [hr] at h; contradiction
          | ok tl =>
              rw [hr] at h; injection h with h; subst h
              intro seg hm
              rcases List.mem_cons.1 hm with rfl | htl
              · exact safeSeg_implies_extSuffix (encodeSingleSeg_safe h1).2.2.2
              · exact renderPathParts_safe rest tl hr seg htl
  | .multiSeg v :: rest, _, h => by
      unfold renderPathParts at h
      dsimp only [bind, Except.bind, pure, Except.pure] at h
      cases h1 : encodeMultiSeg v with
      | error _ => rw [h1] at h; contradiction
      | ok hd =>
          rw [h1] at h; dsimp only at h
          cases hr : renderPathParts rest with
          | error _ => rw [hr] at h; contradiction
          | ok tl =>
              rw [hr] at h; injection h with h; subst h
              intro seg hm
              rcases List.mem_cons.1 hm with rfl | htl
              · exact encodeMultiSeg_safe h1
              · exact renderPathParts_safe rest tl hr seg htl

private def joinDelim (sep : Char) : List String → String
  | []      => ""
  | [s]     => s
  | s :: ss => s ++ String.singleton sep ++ joinDelim sep ss

private theorem joinDelim_safe {sep : Char} (hsep : isSafeExtSuffixChar sep = true) :
    ∀ (ss : List String),
      (∀ s ∈ ss, s.toList.all isSafeExtSuffixChar = true) →
      (joinDelim sep ss).toList.all isSafeExtSuffixChar = true
  | [], _ => rfl
  | [s], hs => hs s (by simp)
  | s₁ :: s₂ :: rest, hs => by
      have ih := joinDelim_safe hsep (s₂ :: rest) (fun x hx => hs x (by simp [hx]))
      simp [joinDelim, String.toList_append, hs s₁ (by simp), hsep, ih]

private def renderQueryPairs : List (String × QueryVal) → List String
  | [] => []
  | (k, v) :: rest =>
      let raw := match v with | .lit r | .param r => r
      (pctEncode k ++ "=" ++ pctEncode raw) :: renderQueryPairs rest

private theorem renderQueryPairs_safe :
    ∀ (qs : List (String × QueryVal)) (p : String),
      p ∈ renderQueryPairs qs → p.toList.all isSafeExtSuffixChar = true
  | [], _, hm => False.elim (List.not_mem_nil hm)
  | (k, v) :: rest, p, hm => by
      simp only [renderQueryPairs, List.mem_cons] at hm
      rcases hm with rfl | htl
      · have hk := safeSeg_implies_extSuffix (pctEncode_safe k)
        have heq : isSafeExtSuffixChar '=' = true := rfl
        cases v <;> simp [String.toList_append, hk, heq, safeSeg_implies_extSuffix (pctEncode_safe _)]
      · exact renderQueryPairs_safe rest p htl

/-- Builds the relative `/path?query` suffix (without leading `/`) for an `external` endpoint. -/
def buildExternalSuffix (parts : List PathPart) (query : List (String × QueryVal)) :
    Except ApiError String := do
  let segs ← renderPathParts parts
  let pathStr := joinDelim '/' segs
  if query.isEmpty then
    return pathStr
  else
    return pathStr ++ "?" ++ joinDelim '&' (renderQueryPairs query)

theorem buildExternalSuffix_safe {parts : List PathPart} {query : List (String × QueryVal)} {sfx : String}
    (h : buildExternalSuffix parts query = .ok sfx) :
    sfx.toList.all isSafeExtSuffixChar = true := by
  unfold buildExternalSuffix at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  cases hr : renderPathParts parts with
  | error _ => rw [hr] at h; contradiction
  | ok segs =>
      rw [hr] at h; dsimp only at h
      have hpath := joinDelim_safe (sep := '/') rfl segs (renderPathParts_safe parts segs hr)
      by_cases hq : query.isEmpty
      · simp [hq] at h; subst h; exact hpath
      · simp [hq] at h; subst h
        have hqchar : isSafeExtSuffixChar '?' = true := rfl
        have hamp := joinDelim_safe (sep := '&') rfl (renderQueryPairs query) (renderQueryPairs_safe query)
        simp [String.toList_append, hpath, hqchar, hamp]

/-- Builds a complete SSRF-pinned outbound URL `base ++ "/" ++ suffix` for an `external` endpoint. -/
def buildExternalUrl (base : String) (parts : List PathPart) (query : List (String × QueryVal)) :
    Except ApiError String := do
  let sfx ← buildExternalSuffix parts query
  return (base ++ "/") ++ sfx

/-- SSRF Origin-Pinning & Path-Traversal Closure Theorem:
    Every URL produced by `buildExternalUrl` strictly begins with `base ++ "/"` (preserving scheme,
    host, port, and base path prefix regardless of untrusted `:param` or `:path*` values) and its
    dynamic suffix contains zero `#`, `\`, `@`, `\r`, `\n`, or NUL smuggling characters. -/
theorem external_url_preserves_origin
    (base : String) (parts : List PathPart) (query : List (String × QueryVal)) (url : String)
    (h : buildExternalUrl base parts query = .ok url) :
    url.startsWith (base ++ "/") = true ∧
    ∃ sfx : String,
      url = (base ++ "/") ++ sfx ∧
      (∀ c ∈ sfx.toList, c ≠ '#' ∧ c ≠ '\\' ∧ c ≠ '\r' ∧ c ≠ '\n' ∧ c ≠ '\x00' ∧ c ≠ '@') := by
  unfold buildExternalUrl at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  cases hs : buildExternalSuffix parts query with
  | error _ => rw [hs] at h; contradiction
  | ok sfx =>
      rw [hs] at h; injection h with h; subst h
      refine ⟨by simp [String.startsWith], sfx, rfl, ?_⟩
      have hsfx := buildExternalSuffix_safe hs
      rw [List.all_eq_true] at hsfx
      intro c hc
      exact isSafeExtSuffixChar_no_smuggle (hsfx c hc)

/-- Builds an SSRF/origin-pinned WebSocket URL `toWsOrigin base ++ "/" ++ suffix` for a 3rd-party `external` `ws` channel. -/
def buildExternalWsUrl (base : String) (parts : List PathPart) (query : List (String × QueryVal)) :
    Except ApiError String :=
  buildExternalUrl (toWsOrigin base) parts query

/-- 3rd-Party WebSocket Origin-Pinning & Path-Traversal Closure Theorem. -/
theorem external_ws_url_preserves_origin
    (base : String) (parts : List PathPart) (query : List (String × QueryVal)) (url : String)
    (h : buildExternalWsUrl base parts query = .ok url) :
    url.startsWith (toWsOrigin base ++ "/") = true ∧
    ∃ sfx : String,
      url = (toWsOrigin base ++ "/") ++ sfx ∧
      (∀ c ∈ sfx.toList, c ≠ '#' ∧ c ≠ '\\' ∧ c ≠ '\r' ∧ c ≠ '\n' ∧ c ≠ '\x00' ∧ c ≠ '@') :=
  external_url_preserves_origin (toWsOrigin base) parts query url h

/-! ## External Auth Specs, Outbound HTTP & `MonadServer` / `MonadAtomic` -/

inductive AuthSpec where
  | none
  | bearerSecret (envVar : String)
  | headerSecret (headerName envVar : String)
  | gcpServiceAccount (envVar scope : String)
deriving Inhabited, DecidableEq, Repr

namespace AuthSpec

def requiredSecrets : AuthSpec → List String
  | .none                     => []
  | .bearerSecret v           => [v]
  | .headerSecret _ v         => [v]
  | .gcpServiceAccount v _    => [v]

end AuthSpec

structure OutboundReq where
  serviceName  : String
  baseOrigin   : String
  method       : String
  pathAndQuery : String
  headers      : List (String × String)
  body         : ByteArray
  auth         : AuthSpec := .none
  ssrfGuard    : Bool := false
deriving Inhabited

structure OutboundResp where
  status  : UInt32
  body    : ByteArray
  headers : List (String × String) := []
deriving Inhabited

class MonadServer (m : Type → Type) where
  httpCall    : OutboundReq → m (Except ApiError OutboundResp)
  readEnv     : String → m (Option String)
  nowMs       : m UInt64
  randomHex   : UInt32 → m String
  hmacSha256  : ByteArray → ByteArray → m ByteArray
  wsBroadcast : String → ByteArray → m Unit

structure WsEmit where
  topic   : String
  payload : ByteArray
deriving Inhabited, DecidableEq

@[specialize]
def flushWsEmits {m : Type → Type} [Monad m] [MonadServer m] : List WsEmit → m Unit
  | []      => pure ()
  | e :: es => do
      MonadServer.wsBroadcast e.topic e.payload
      flushWsEmits es

class MonadAtomic (σ : Type) (m : Type → Type) where
  runAtomic     : {α : Type} → (σ → σ × α) → m α
  runAtomicRead : {α : Type} → (σ → α) → m α := fun f => runAtomic (fun s => (s, f s))

/-! ## Proof-Driven `rdlock` Optimization Witness (`readOnly_preserves_state`) -/

/-- Witness theorem justifying shared multi-core `pthread_rwlock_rdlock` execution for any
    `server` handler that never mutates `state`: lifting a pure reader `f : σ → RequestCtx → α → β`
    into a state transition `(s, f s ctx a)` is guaranteed to leave `s` bit-identical (`s' = s`). -/
@[simp] theorem readOnly_preserves_state {σ α β : Type}
    (f : σ → RequestCtx → α → β) (s : σ) (ctx : RequestCtx) (a : α) :
    (s, f s ctx a).1 = s := rfl

/-! ## Multi-Core Interleaved Linearizability Model & Proof (`concurrent_schedule_preserves_inv`) -/

/-- Non-stateful external/OS I/O commands available to a server handler thread. -/
inductive ServerEffect : Type where
  | httpCall    (req : OutboundReq)
  | readEnv     (v : String)
  | nowMs
  | randomHex   (n : UInt32)
  | hmacSha256  (key msg : ByteArray)
  | wsBroadcast (t : String) (p : ByteArray)

/-- Response payload type returned by each `ServerEffect`. -/
def ServerEffect.Resp : ServerEffect → Type
  | .httpCall _      => Except ApiError OutboundResp
  | .readEnv _       => Option String
  | .nowMs           => UInt64
  | .randomHex _     => String
  | .hmacSha256 _ _  => ByteArray
  | .wsBroadcast _ _ => Unit

/-- Effect tree of a server handler thread executing non-blocking external I/O interleaved with
    single-step `atomic` shared-state transitions on `σ`. Notice `σ` is unreachable during
    `io` (`httpCall`, `readEnv`, `nowMs`, `randomHex`, `hmacSha256`, `wsBroadcast`) steps. -/
inductive ThreadProg (σ : Type) (α : Type) : Type where
  | pure   : α → ThreadProg σ α
  | io     : (eff : ServerEffect) → (eff.Resp → ThreadProg σ α) → ThreadProg σ α
  | atomic : (σ → σ) → (σ → ThreadProg σ α) → ThreadProg σ α

namespace ThreadProg

def bind {σ α β : Type} : ThreadProg σ α → (α → ThreadProg σ β) → ThreadProg σ β
  | .pure a,         k => k a
  | .io eff f,       k => .io eff (fun r => bind (f r) k)
  | .atomic st next, k => .atomic st (fun s => bind (next s) k)

instance {σ : Type} : Monad (ThreadProg σ) where
  pure := .pure
  bind := ThreadProg.bind

instance {σ : Type} : MonadServer (ThreadProg σ) where
  httpCall req       := .io (.httpCall req) .pure
  readEnv v          := .io (.readEnv v) .pure
  nowMs              := .io .nowMs .pure
  randomHex n        := .io (.randomHex n) .pure
  hmacSha256 key msg := .io (.hmacSha256 key msg) .pure
  wsBroadcast t p    := .io (.wsBroadcast t p) .pure

instance {σ : Type} : MonadAtomic σ (ThreadProg σ) where
  runAtomic f     := .atomic (fun s => (f s).1) (fun s => .pure (f s).2)
  runAtomicRead f := .atomic id (fun s => .pure (f s))

end ThreadProg

@[simp] theorem threadProg_pure_bind {σ α β : Type} (a : α) (k : α → ThreadProg σ β) :
    ((Pure.pure a : ThreadProg σ α) >>= k) = k a := rfl

@[simp] theorem threadProg_pure_bind' {σ α β : Type} (a : α) (k : α → ThreadProg σ β) :
    (ThreadProg.pure a >>= k) = k a := rfl

@[simp] theorem threadProg_bind_assoc {σ α β γ : Type}
    (p : ThreadProg σ α) (f : α → ThreadProg σ β) (g : β → ThreadProg σ γ) :
    ((p >>= f) >>= g) = (p >>= fun x => f x >>= g) := by
  change ThreadProg.bind (ThreadProg.bind p f) g = ThreadProg.bind p (fun x => ThreadProg.bind (f x) g)
  induction p with
  | pure a => rfl
  | io _ _ ih => exact congrArg _ (funext ih)
  | atomic _ _ ih => exact congrArg _ (funext ih)

/-- General two-state transition invariant across an async `ThreadProg`: every `atomic` step `s ↦ st s`
    may assume `Inv s` and must satisfy `Rel s (st s)` (covering single-state `Inv`, `old(...)`
    conservation/monotonicity laws, and `mutating <field> requires <cond>` access-control rules). -/
inductive ProgPreservesStepRel {σ α : Type} (Inv : σ → Prop) (Rel : σ → σ → Prop) :
    ThreadProg σ α → Prop where
  | pure (a : α) :
      ProgPreservesStepRel Inv Rel (.pure a)
  | io (eff : ServerEffect) (k : eff.Resp → ThreadProg σ α) :
      (∀ r, ProgPreservesStepRel Inv Rel (k r)) → ProgPreservesStepRel Inv Rel (.io eff k)
  | atomic (st : σ → σ) (next : σ → ThreadProg σ α) :
      (∀ s, Inv s → Rel s (st s)) →
      (∀ s, Inv s → ProgPreservesStepRel Inv Rel (next s)) →
      ProgPreservesStepRel Inv Rel (.atomic st next)

/-- Single-state invariant preservation across an async `ThreadProg`. -/
abbrev ProgPreservesInv {σ α : Type} (Inv : σ → Prop) (p : ThreadProg σ α) : Prop :=
  ProgPreservesStepRel Inv (fun _ s' => Inv s') p

theorem progPreservesStepRel_of_const {σ α : Type} {Inv : σ → Prop} {Rel : σ → σ → Prop}
    (p : ThreadProg σ α) (h : ∀ s s', Rel s s') :
    ProgPreservesStepRel Inv Rel p := by
  induction p with
  | pure a => exact .pure a
  | io _ _ ih => exact .io _ _ ih
  | atomic _ _ ih => exact .atomic _ _ (fun s _ => h s _) (fun s _ => ih s)

theorem progPreservesStepRel_bind {σ α β : Type} {Inv : σ → Prop} {Rel : σ → σ → Prop}
    {p : ThreadProg σ α} {k : α → ThreadProg σ β}
    (hp : ProgPreservesStepRel Inv Rel p)
    (hk : ∀ a, ProgPreservesStepRel Inv Rel (k a)) :
    ProgPreservesStepRel Inv Rel (p >>= k) := by
  change ProgPreservesStepRel Inv Rel (ThreadProg.bind p k)
  induction hp with
  | pure a => exact hk a
  | io _ _ _ ih => exact .io _ _ ih
  | atomic st _ hst _ ih => exact .atomic st _ hst ih

theorem progPreservesStepRel_runAtomic {σ α : Type} {Inv : σ → Prop} {Rel : σ → σ → Prop}
    (step : σ → σ × α)
    (hstep : ∀ s, Inv s → Rel s (step s).1) :
    ProgPreservesStepRel Inv Rel (MonadAtomic.runAtomic (m := ThreadProg σ) step) :=
  .atomic _ _ hstep (fun s _ => .pure (step s).2)

theorem progPreservesStepRel_runAtomicRead {σ α : Type} {Inv : σ → Prop} {Rel : σ → σ → Prop}
    (f : σ → α)
    (hrefl : ∀ s, Inv s → Rel s s) :
    ProgPreservesStepRel Inv Rel (MonadAtomic.runAtomicRead (m := ThreadProg σ) f) :=
  .atomic _ _ hrefl (fun s _ => .pure (f s))

theorem runAtomic_bind_preservesStepRel {σ α β : Type} {Inv : σ → Prop} {Rel : σ → σ → Prop}
    (step : σ → σ × α) {k : α → ThreadProg σ β}
    (hk : ∀ a, ProgPreservesStepRel Inv Rel (k a))
    (hstep : ∀ s, Inv s → Rel s (step s).1) :
    ProgPreservesStepRel Inv Rel (MonadAtomic.runAtomic (m := ThreadProg σ) step >>= k) :=
  progPreservesStepRel_bind (progPreservesStepRel_runAtomic step hstep) hk

theorem runAtomicRead_bind_preservesStepRel {σ α β : Type} {Inv : σ → Prop} {Rel : σ → σ → Prop}
    (f : σ → α) {k : α → ThreadProg σ β}
    (hk : ∀ a, ProgPreservesStepRel Inv Rel (k a))
    (hrefl : ∀ s, Inv s → Rel s s) :
    ProgPreservesStepRel Inv Rel (MonadAtomic.runAtomicRead (m := ThreadProg σ) f >>= k) :=
  progPreservesStepRel_bind (progPreservesStepRel_runAtomicRead f hrefl) hk

/-- Snapshot of a multi-core server running arbitrarily many concurrent worker threads alongside
    shared heap state `shared : σ`. -/
structure MultiCoreState (σ Out : Type) where
  shared  : σ
  threads : List (ThreadProg σ Out)

/-- Non-deterministic multi-core OS + network scheduler transition. -/
inductive MultiCoreStep {σ Out : Type} (Inv : σ → Prop) :
    MultiCoreState σ Out → MultiCoreState σ Out → Prop where
  | spawn (s : σ) (ts : List (ThreadProg σ Out)) (p : ThreadProg σ Out) :
      ProgPreservesInv Inv p →
      MultiCoreStep Inv ⟨s, ts⟩ ⟨s, p :: ts⟩
  | reap (s : σ) (pre post : List (ThreadProg σ Out)) (out : Out) :
      MultiCoreStep Inv ⟨s, pre ++ .pure out :: post⟩ ⟨s, pre ++ post⟩
  | stepIo (s : σ) (pre post : List (ThreadProg σ Out))
      (eff : ServerEffect) (k : eff.Resp → ThreadProg σ Out) (resp : eff.Resp) :
      MultiCoreStep Inv ⟨s, pre ++ .io eff k :: post⟩ ⟨s, pre ++ k resp :: post⟩
  | stepAtomic (s : σ) (pre post : List (ThreadProg σ Out))
      (st : σ → σ) (next : σ → ThreadProg σ Out) :
      MultiCoreStep Inv ⟨s, pre ++ .atomic st next :: post⟩
                        ⟨st s, pre ++ next s :: post⟩

/-- Multi-step multi-core execution schedule starting from `init`. -/
inductive MultiCoreSchedule {σ Out : Type} (Inv : σ → Prop) :
    MultiCoreState σ Out → MultiCoreState σ Out → Prop where
  | refl (st : MultiCoreState σ Out) :
      MultiCoreSchedule Inv st st
  | step {st₁ st₂ st₃ : MultiCoreState σ Out} :
      MultiCoreSchedule Inv st₁ st₂ →
      MultiCoreStep Inv st₂ st₃ →
      MultiCoreSchedule Inv st₁ st₃

private theorem pool_replace_mid {α : Type} {P : α → Prop} {pre post : List α} {x y : α}
    (hpool : ∀ q ∈ pre ++ x :: post, P q) (hy : P y) :
    ∀ q ∈ pre ++ y :: post, P q := by
  intro q hq
  rcases List.mem_append.1 hq with hpre | hcons
  · exact hpool q (List.mem_append_left _ hpre)
  · rcases List.mem_cons.1 hcons with rfl | hpost
    · exact hy
    · exact hpool q (List.mem_append_right _ (List.mem_cons_of_mem _ hpost))

private theorem step_preserves_inv_and_pool {σ Out : Type} {Inv : σ → Prop}
    {st₁ st₂ : MultiCoreState σ Out}
    (hstep : MultiCoreStep Inv st₁ st₂)
    (hinv : Inv st₁.shared)
    (hpool : ∀ p ∈ st₁.threads, ProgPreservesInv Inv p) :
    Inv st₂.shared ∧ (∀ p ∈ st₂.threads, ProgPreservesInv Inv p) := by
  have mid {x : ThreadProg σ Out} {pre post} (hp : ∀ p ∈ pre ++ x :: post, ProgPreservesInv Inv p) :
      ProgPreservesInv Inv x := hp x (List.mem_append_right _ (List.mem_cons_self ..))
  cases hstep with
  | spawn s ts p hp =>
      exact ⟨hinv, fun q hq => (List.mem_cons.1 hq).elim (· ▸ hp) (hpool q)⟩
  | reap s pre post out =>
      refine ⟨hinv, fun q hq => ?_⟩
      rcases List.mem_append.1 hq with hpre | hpost
      · exact hpool q (List.mem_append_left _ hpre)
      · exact hpool q (List.mem_append_right _ (List.mem_cons_of_mem _ hpost))
  | stepIo s pre post eff k resp =>
      cases mid hpool with | io _ _ hk => exact ⟨hinv, pool_replace_mid hpool (hk resp)⟩
  | stepAtomic s pre post st next =>
      cases mid hpool with | atomic _ _ hst hnext => exact ⟨hst s hinv, pool_replace_mid hpool (hnext s hinv)⟩

/-- Multi-Core Linearizability Theorem:
    If `Inv s₀` holds at server boot and every spawned RPC handler thread preserves `Inv` across
    each of its `atomic` blocks (`ProgPreservesInv Inv`), then `Inv` holds at **every** reachable
    global server state across **all** multi-core OS thread schedules, network interleavings, and
    external API failures. -/
theorem concurrent_schedule_preserves_inv {σ Out : Type}
    (Inv : σ → Prop) (s₀ : σ) (st : MultiCoreState σ Out)
    (hinit : Inv s₀)
    (hsched : MultiCoreSchedule Inv ⟨s₀, []⟩ st) :
    Inv st.shared := by
  suffices hboth : Inv st.shared ∧ (∀ p ∈ st.threads, ProgPreservesInv Inv p) from hboth.1
  induction hsched with
  | refl => exact ⟨hinit, fun _ hm => False.elim (List.not_mem_nil hm)⟩
  | step _ hstep ih => exact step_preserves_inv_and_pool hstep ih.1 ih.2

/-- Witness that a `ThreadProg` performs only external/env/clock/crypto I/O and zero `.atomic` transitions. -/
inductive NoAtomic {σ α : Type} : ThreadProg σ α → Prop where
  | pure (a : α) : NoAtomic (.pure a)
  | io (eff : ServerEffect) (k : eff.Resp → ThreadProg σ α) :
      (∀ r, NoAtomic (k r)) → NoAtomic (.io eff k)

class SafeIO {σ α : Type} (p : ThreadProg σ α) : Prop where
  noAtomic : NoAtomic p

instance {σ α : Type} (a : α) : SafeIO (Pure.pure (f := ThreadProg σ) a) := ⟨.pure a⟩
instance {σ α : Type} (a : α) : SafeIO (ThreadProg.pure (σ := σ) a) := ⟨.pure a⟩
instance {σ : Type} (req : OutboundReq) : SafeIO (MonadServer.httpCall (m := ThreadProg σ) req) :=
  ⟨.io _ _ .pure⟩
instance {σ : Type} (v : String) : SafeIO (MonadServer.readEnv (m := ThreadProg σ) v) :=
  ⟨.io _ _ .pure⟩
instance {σ : Type} : SafeIO (MonadServer.nowMs (m := ThreadProg σ)) :=
  ⟨.io _ _ .pure⟩
instance {σ : Type} (n : UInt32) : SafeIO (MonadServer.randomHex (m := ThreadProg σ) n) :=
  ⟨.io _ _ .pure⟩
instance {σ : Type} (key msg : ByteArray) : SafeIO (MonadServer.hmacSha256 (m := ThreadProg σ) key msg) :=
  ⟨.io _ _ .pure⟩
instance {σ : Type} (t : String) (p : ByteArray) : SafeIO (MonadServer.wsBroadcast (m := ThreadProg σ) t p) :=
  ⟨.io _ _ .pure⟩

theorem noAtomic_bind {σ α β : Type} {p : ThreadProg σ α} {k : α → ThreadProg σ β}
    (hp : NoAtomic p) (hk : ∀ a, NoAtomic (k a)) : NoAtomic (p >>= k) := by
  change NoAtomic (ThreadProg.bind p k)
  induction hp with
  | pure a => exact hk a
  | io _ _ _ ih => exact .io _ _ ih

instance {σ α β : Type} (p : ThreadProg σ α) (k : α → ThreadProg σ β)
    [hp : SafeIO p] [hk : ∀ a, SafeIO (k a)] : SafeIO (p >>= k) where
  noAtomic := noAtomic_bind hp.noAtomic (fun a => (hk a).noAtomic)

theorem noAtomic_flushWsEmits {σ : Type} : ∀ es : List WsEmit, NoAtomic (flushWsEmits (m := ThreadProg σ) es)
  | [] => .pure ()
  | e :: es => noAtomic_bind (.io (.wsBroadcast e.topic e.payload) _ .pure) (fun _ => noAtomic_flushWsEmits es)

instance {σ : Type} (es : List WsEmit) : SafeIO (flushWsEmits (m := ThreadProg σ) es) :=
  ⟨noAtomic_flushWsEmits es⟩

theorem safeIO_preservesStepRel {σ α : Type} {Inv : σ → Prop} {Rel : σ → σ → Prop}
    (p : ThreadProg σ α) [hp : SafeIO p] :
    ProgPreservesStepRel Inv Rel p := by
  induction hp.noAtomic with
  | pure a => exact .pure a
  | io _ _ _ ih => exact .io _ _ ih

theorem safeIO_bind_preservesStepRel {σ α β : Type} {Inv : σ → Prop} {Rel : σ → σ → Prop}
    (p : ThreadProg σ α) [SafeIO p] {k : α → ThreadProg σ β}
    (hk : ∀ a, ProgPreservesStepRel Inv Rel (k a)) :
    ProgPreservesStepRel Inv Rel (p >>= k) :=
  progPreservesStepRel_bind (safeIO_preservesStepRel p) hk

/-! ## Inferred Domain Errors (`SrvFailure`) & Async Postcondition Proofs (`ProgEnsures`) -/

/-- Server-side failure combining transport/infrastructure `ApiError`s with inferred typed
    application-level domain failures `fail(.tag)`. -/
inductive SrvFailure (ε : Type) where
  | api    (err : ApiError)
  | domain (tag : ε) (message : String)
deriving Inhabited, DecidableEq, Repr

/-- Translates internal transactional `Except (SrvFailure ε) α` into wire-level
    `Except ApiError (Except (RpcDomainError ε) α)`: domain errors serialize inside a `200 OK`
    Protobuf payload while transport/auth errors remain HTTP error statuses. -/
def SrvFailure.toWire {ε α : Type} :
    Except (SrvFailure ε) α → Except ApiError (Except (RpcDomainError ε) α)
  | .ok a                  => .ok (.ok a)
  | .error (.domain t msg) => .ok (.error ⟨t, msg⟩)
  | .error (.api err)      => .error err

/-- Postcondition judgment for an async `ThreadProg`: every `.pure a` return value must satisfy
    `Post a`, assuming shared server state satisfies `Inv` at each `atomic` boundary. -/
inductive ProgEnsures {σ α : Type} (Inv : σ → Prop) (Post : α → Prop) : ThreadProg σ α → Prop where
  | pure (a : α) :
      Post a → ProgEnsures Inv Post (.pure a)
  | io (eff : ServerEffect) (k : eff.Resp → ThreadProg σ α) :
      (∀ r, ProgEnsures Inv Post (k r)) → ProgEnsures Inv Post (.io eff k)
  | atomic (st : σ → σ) (next : σ → ThreadProg σ α) :
      (∀ s, Inv s → ProgEnsures Inv Post (next s)) →
      ProgEnsures Inv Post (.atomic st next)

theorem progEnsures_pure {σ α : Type} {Inv : σ → Prop} {Post : α → Prop}
    (a : α) (ha : Post a) :
    ProgEnsures Inv Post (Pure.pure a) :=
  .pure a ha

theorem progEnsures_bind {σ α β : Type} {Inv : σ → Prop} {Q : α → Prop} {Post : β → Prop}
    {p : ThreadProg σ α} {k : α → ThreadProg σ β}
    (hp : ProgEnsures Inv Q p)
    (hk : ∀ a, Q a → ProgEnsures Inv Post (k a)) :
    ProgEnsures Inv Post (p >>= k) := by
  change ProgEnsures Inv Post (ThreadProg.bind p k)
  induction hp with
  | pure a ha => exact hk a ha
  | io _ _ _ ih => exact .io _ _ ih
  | atomic st _ _ ih => exact .atomic st _ ih

theorem safeIO_ensures_true {σ α : Type} {Inv : σ → Prop}
    (p : ThreadProg σ α) [hp : SafeIO p] :
    ProgEnsures Inv (fun _ => True) p := by
  induction hp.noAtomic with
  | pure a => exact .pure a trivial
  | io _ _ _ ih => exact .io _ _ ih

theorem safeIO_bind_ensures {σ α β : Type} {Inv : σ → Prop} {Post : β → Prop}
    (p : ThreadProg σ α) [SafeIO p] {k : α → ThreadProg σ β}
    (hk : ∀ a, ProgEnsures Inv Post (k a)) :
    ProgEnsures Inv Post (p >>= k) :=
  progEnsures_bind (safeIO_ensures_true p) (fun a _ => hk a)

theorem progEnsures_runAtomic {σ α : Type} {Inv : σ → Prop} {Post : α → Prop}
    (step : σ → σ × α)
    (hstep : ∀ s, Inv s → Post (step s).2) :
    ProgEnsures Inv Post (MonadAtomic.runAtomic (m := ThreadProg σ) step) :=
  .atomic _ (fun s => .pure (step s).2) (fun s hs => .pure _ (hstep s hs))

theorem progEnsures_runAtomicRead {σ α : Type} {Inv : σ → Prop} {Post : α → Prop}
    (f : σ → α)
    (hf : ∀ s, Inv s → Post (f s)) :
    ProgEnsures Inv Post (MonadAtomic.runAtomicRead (m := ThreadProg σ) f) :=
  .atomic id (fun s => .pure (f s)) (fun s hs => .pure _ (hf s hs))

theorem runAtomic_bind_ensures {σ α β : Type} {Inv : σ → Prop} {Post : β → Prop}
    (step : σ → σ × α) {k : α → ThreadProg σ β}
    (hk : ∀ s, Inv s → ProgEnsures Inv Post (k (step s).2)) :
    ProgEnsures Inv Post (MonadAtomic.runAtomic (m := ThreadProg σ) step >>= k) :=
  .atomic (fun s => (step s).1) (fun s => k (step s).2) hk

theorem runAtomicRead_bind_ensures {σ α β : Type} {Inv : σ → Prop} {Post : β → Prop}
    (f : σ → α) {k : α → ThreadProg σ β}
    (hk : ∀ s, Inv s → ProgEnsures Inv Post (k (f s))) :
    ProgEnsures Inv Post (MonadAtomic.runAtomicRead (m := ThreadProg σ) f >>= k) :=
  .atomic id (fun s => k (f s)) hk

/-- Multi-core scheduler state tracking a target RPC thread alongside arbitrary concurrent
    `Inv`-preserving background handlers. -/
structure TrackedMultiCoreState (σ Tgt Out : Type) where
  shared : σ
  target : ThreadProg σ Tgt
  others : List (ThreadProg σ Out)

inductive TrackedMultiCoreStep {σ Tgt Out : Type} (Inv : σ → Prop) :
    TrackedMultiCoreState σ Tgt Out → TrackedMultiCoreState σ Tgt Out → Prop where
  | stepOther {s₁ s₂ : σ} {os₁ os₂ : List (ThreadProg σ Out)} (t : ThreadProg σ Tgt) :
      MultiCoreStep Inv ⟨s₁, os₁⟩ ⟨s₂, os₂⟩ →
      TrackedMultiCoreStep Inv ⟨s₁, t, os₁⟩ ⟨s₂, t, os₂⟩
  | stepTargetIo (s : σ) (os : List (ThreadProg σ Out))
      (eff : ServerEffect) (k : eff.Resp → ThreadProg σ Tgt) (resp : eff.Resp) :
      TrackedMultiCoreStep Inv ⟨s, .io eff k, os⟩ ⟨s, k resp, os⟩
  | stepTargetAtomic (s : σ) (os : List (ThreadProg σ Out))
      (st : σ → σ) (next : σ → ThreadProg σ Tgt) :
      TrackedMultiCoreStep Inv ⟨s, .atomic st next, os⟩ ⟨st s, next s, os⟩

inductive TrackedMultiCoreSchedule {σ Tgt Out : Type} (Inv : σ → Prop) :
    TrackedMultiCoreState σ Tgt Out → TrackedMultiCoreState σ Tgt Out → Prop where
  | refl (st : TrackedMultiCoreState σ Tgt Out) :
      TrackedMultiCoreSchedule Inv st st
  | step {st₁ st₂ st₃ : TrackedMultiCoreState σ Tgt Out} :
      TrackedMultiCoreSchedule Inv st₁ st₂ →
      TrackedMultiCoreStep Inv st₂ st₃ →
      TrackedMultiCoreSchedule Inv st₁ st₃

private theorem trackedStep_preserves {σ Tgt Out : Type} {Inv : σ → Prop} {Post : Tgt → Prop}
    {st₁ st₂ : TrackedMultiCoreState σ Tgt Out}
    (hstep : TrackedMultiCoreStep Inv st₁ st₂)
    (hinv : Inv st₁.shared)
    (htinv : ProgPreservesInv Inv st₁.target)
    (htens : ProgEnsures Inv Post st₁.target)
    (hopool : ∀ p ∈ st₁.others, ProgPreservesInv Inv p) :
    Inv st₂.shared ∧ ProgPreservesInv Inv st₂.target ∧ ProgEnsures Inv Post st₂.target ∧
      (∀ p ∈ st₂.others, ProgPreservesInv Inv p) := by
  cases hstep with
  | stepOther t hs =>
      let ⟨hinv', hopool'⟩ := step_preserves_inv_and_pool hs hinv hopool
      exact ⟨hinv', htinv, htens, hopool'⟩
  | stepTargetIo s os eff k resp =>
      cases htinv with | io _ _ hk1 =>
      cases htens with | io _ _ hk2 => exact ⟨hinv, hk1 resp, hk2 resp, hopool⟩
  | stepTargetAtomic s os st next =>
      cases htinv with | atomic _ _ hst hnext1 =>
      cases htens with | atomic _ _ hnext2 => exact ⟨hst s hinv, hnext1 s hinv, hnext2 s hinv, hopool⟩

/-- Multi-Core Concurrent Postcondition Theorem:
    If `Inv s₀` holds at server boot, `tgt₀` preserves `Inv` (`ProgPreservesInv Inv tgt₀`) and
    satisfies `ProgEnsures Inv Post tgt₀`, then whenever `tgt₀` finishes with `.pure out` under
    **any** interleaving with arbitrarily many concurrent `Inv`-preserving background threads and
    external API responses, `Inv st.shared` and `Post out` both hold unconditionally. -/
theorem concurrent_schedule_ensures {σ Tgt Out : Type}
    (Inv : σ → Prop) (Post : Tgt → Prop) (s₀ : σ) (tgt₀ : ThreadProg σ Tgt)
    (st : TrackedMultiCoreState σ Tgt Out)
    (hinit : Inv s₀)
    (htinv : ProgPreservesInv Inv tgt₀)
    (htens : ProgEnsures Inv Post tgt₀)
    (hsched : TrackedMultiCoreSchedule Inv ⟨s₀, tgt₀, []⟩ st) :
    Inv st.shared ∧ ∀ out, st.target = .pure out → Post out := by
  suffices h : Inv st.shared ∧ ProgPreservesInv Inv st.target ∧ ProgEnsures Inv Post st.target ∧
      (∀ p ∈ st.others, ProgPreservesInv Inv p) by
    refine ⟨h.1, fun out hout => ?_⟩
    rw [hout] at h
    cases h.2.2.1 with | pure _ hp => exact hp
  induction hsched with
  | refl => exact ⟨hinit, htinv, htens, fun _ hm => False.elim (List.not_mem_nil hm)⟩
  | step _ hstep ih => exact trackedStep_preserves hstep ih.1 ih.2.1 ih.2.2.1 ih.2.2.2

/-! ## Control-Flow Combinators & Auto-Lifting Helpers (`@[reducible]` for Zero-Cost Proofs & C Codegen) -/

/-- Index conversion allowing both `Nat` and `Fin n` to index `Array`s uniformly across mutations. -/
class SrvIdx (ι : Type) where
  toNat : ι → Nat

@[inline] instance : SrvIdx Nat := ⟨id⟩
@[inline] instance {n : Nat} : SrvIdx (Fin n) := ⟨Fin.val⟩

@[simp] theorem SrvIdx.toNat_nat (i : Nat) : SrvIdx.toNat i = i := rfl
@[simp] theorem SrvIdx.toNat_fin {n : Nat} (i : Fin n) : SrvIdx.toNat i = i.val := rfl

/-- Auto-lifts plain values `v : T` to `some v` in `T?` functions while keeping `Option T` un-nested. -/
class SrvLiftOpt (α : Type) (Inner : Type) where
  liftOpt : α → Option Inner

@[inline] instance {Inner : Type} : SrvLiftOpt (Option Inner) Inner := ⟨id⟩
@[inline] instance (priority := low) {Inner : Type} : SrvLiftOpt Inner Inner := ⟨Option.some⟩

@[simp] theorem SrvLiftOpt.liftOpt_opt {Inner : Type} (x : Option Inner) :
    SrvLiftOpt.liftOpt x = x := rfl
@[simp] theorem SrvLiftOpt.liftOpt_val {Inner : Type} (x : Inner) :
    SrvLiftOpt.liftOpt (Inner := Inner) x = some x := rfl

/-- Overloaded `fail(...)` builder supporting `fail("msg")`, `fail(code, "msg")`, and `fail(.tag, "msg")`. -/
def mkFail1 (msg : String) : ApiError := ApiError.badRequest msg
def mkFail2 (code : Nat) (msg : String) : ApiError := { code, message := msg }
def mkFailDom {ε : Type} (tag : ε) (msg : String) : SrvFailure ε := .domain tag msg

/-- Uniform API-error lifting for `ApiError` and inferred `SrvFailure ε`. -/
class SrvErr (E : Type) where
  ofApi : ApiError → E

@[reducible] instance : SrvErr ApiError := ⟨id⟩
@[reducible] instance {ε : Type} : SrvErr (SrvFailure ε) := ⟨SrvFailure.api⟩

/-- Unwraps `Except (SrvFailure ε)`, `Except ApiError`, `Except String`, or `Option` for `?` and `catch`. -/
class SrvUnwrap (E : Type) (W : Type) (Val : outParam Type) where
  unwrap : W → Except E Val

@[reducible] instance {E α : Type} : SrvUnwrap E (Except E α) α where
  unwrap := id

@[reducible] instance {ε α : Type} : SrvUnwrap (SrvFailure ε) (Except ApiError α) α where
  unwrap
    | .ok a    => .ok a
    | .error e => .error (.api e)

@[reducible] instance {E α : Type} [SrvErr E] : SrvUnwrap E (Except String α) α where
  unwrap
    | .ok a    => .ok a
    | .error e => .error (SrvErr.ofApi (ApiError.badRequest e))

@[reducible] instance {E α : Type} [SrvErr E] : SrvUnwrap E (Option α) α where
  unwrap
    | some a => .ok a
    | none   => .error (SrvErr.ofApi (ApiError.notFound "optional value was empty"))

/-- Unwraps `Option α` or `Except ApiError α` inside `T?` functions (`none` exits cleanly as `.ok none`). -/
class SrvUnwrapOpt (W : Type) (Inner : Type) (Val : outParam Type) where
  unwrapOpt : W → Except (Except ApiError (Option Inner)) Val

@[reducible] instance {Inner α : Type} : SrvUnwrapOpt (Option α) Inner α where
  unwrapOpt
    | some a => .ok a
    | none   => .error (.ok none)

@[reducible] instance {Inner α : Type} : SrvUnwrapOpt (Except ApiError α) Inner α where
  unwrapOpt
    | .ok a    => .ok a
    | .error e => .error (.error e)

/-- Pure statement sequencing with early `return` short-circuiting. -/
@[inline]
def srvSeq {σ ρ : Type} (first : σ × Option ρ) (next : σ → σ × Option ρ) : σ × Option ρ :=
  match first with
  | (s', none)   => next s'
  | (s', some r) => (s', some r)

@[simp] theorem srvSeq_none {σ ρ : Type} (s : σ) (next : σ → σ × Option ρ) :
    srvSeq (s, none) next = next s := rfl

@[simp] theorem srvSeq_some {σ ρ : Type} (s : σ) (r : ρ) (next : σ → σ × Option ρ) :
    srvSeq (s, some r) next = (s, some r) := rfl

/-- Transactional finalizer: commits `s'` on `.ok`, rolls back to entry state `s₀` on `.error`. -/
@[inline]
def srvFinish {E σ α : Type} [SrvErr E] (s₀ : σ) (res : σ × Option (Except E α)) : σ × Except E α :=
  match res with
  | (s', some (.ok v))    => (s', .ok v)
  | (_,  some (.error e)) => (s₀, .error e)
  | (_,  none)            => (s₀, .error (SrvErr.ofApi (ApiError.internal "unreachable missing return")))

@[simp] theorem srvFinish_ok {E σ α : Type} [SrvErr E] (s₀ s' : σ) (v : α) :
    srvFinish (E := E) s₀ (s', some (.ok v)) = (s', .ok v) := rfl

@[simp] theorem srvFinish_err {E σ α : Type} [SrvErr E] (s₀ s' : σ) (e : E) :
    srvFinish (E := E) (α := α) s₀ (s', some (.error e)) = (s₀, .error e) := rfl

@[simp] theorem srvFinish_none {E σ α : Type} [SrvErr E] (s₀ s' : σ) :
    srvFinish (E := E) s₀ (s', (none : Option (Except E α))) =
      (s₀, .error (SrvErr.ofApi (ApiError.internal "unreachable missing return"))) := rfl

/-- Transactional finalizer for `atomic` statement blocks: commits `s'` on `none`/`some (.ok v)`, rolls back to `s₀` on `some (.error e)`. -/
@[inline]
def srvAtomicCommit {E σ α : Type} (s₀ : σ) (res : σ × Option (Except E α)) :
    σ × Option (Except E α) :=
  match res with
  | (s', none)                  => (s', none)
  | (s', some (Except.ok v))    => (s', some (Except.ok v))
  | (_,  some (Except.error e)) => (s₀, some (Except.error e))

@[simp] theorem srvAtomicCommit_none {E σ α : Type} (s₀ s' : σ) :
    srvAtomicCommit (E := E) (α := α) s₀ (s', none) = (s', none) := rfl

@[simp] theorem srvAtomicCommit_ok {E σ α : Type} (s₀ s' : σ) (v : α) :
    srvAtomicCommit (E := E) s₀ (s', some (Except.ok v)) = (s', some (Except.ok v)) := rfl

@[simp] theorem srvAtomicCommit_err {E σ α : Type} (s₀ s' : σ) (e : E) :
    srvAtomicCommit (E := E) (α := α) s₀ (s', some (Except.error e)) = (s₀, some (Except.error e)) := rfl

/-! ## Transactional WebSocket Emit Combinators & No-Phantom-Broadcast Theorems -/

/-- Pure statement sequencing carrying an outbound WebSocket emit buffer alongside state `σ`. -/
@[inline]
def srvEmitSeq {σ ρ : Type} (first : σ × List WsEmit × Option ρ)
    (next : σ → List WsEmit → σ × List WsEmit × Option ρ) : σ × List WsEmit × Option ρ :=
  match first with
  | (s', es, none)   => next s' es
  | (s', es, some r) => (s', es, some r)

@[simp] theorem srvEmitSeq_none {σ ρ : Type} (s : σ) (es : List WsEmit)
    (next : σ → List WsEmit → σ × List WsEmit × Option ρ) :
    srvEmitSeq (s, es, none) next = next s es := rfl

@[simp] theorem srvEmitSeq_some {σ ρ : Type} (s : σ) (es : List WsEmit) (r : ρ)
    (next : σ → List WsEmit → σ × List WsEmit × Option ρ) :
    srvEmitSeq (s, es, some r) next = (s, es, some r) := rfl

/-- Transactional finalizer for emit-bearing pure server handlers:
    commits `(s', es)` on `.ok`, and rolls back BOTH state (`s₀`) AND emits (`[]`) on `.error`. -/
@[inline]
def srvFinishEmit {E σ α : Type} [SrvErr E] (s₀ : σ)
    (res : σ × List WsEmit × Option (Except E α)) : σ × (Except E α × List WsEmit) :=
  match res with
  | (s', es, some (.ok v))    => (s', .ok v, es)
  | (_,  _,  some (.error e)) => (s₀, .error e, [])
  | (_,  _,  none)            => (s₀, .error (SrvErr.ofApi (ApiError.internal "unreachable missing return")), [])

@[simp] theorem srvFinishEmit_ok {E σ α : Type} [SrvErr E] (s₀ s' : σ) (es : List WsEmit) (v : α) :
    srvFinishEmit (E := E) s₀ (s', es, some (.ok v)) = (s', .ok v, es) := rfl

@[simp] theorem srvFinishEmit_err {E σ α : Type} [SrvErr E] (s₀ s' : σ) (es : List WsEmit) (e : E) :
    srvFinishEmit (E := E) (α := α) s₀ (s', es, some (.error e)) = (s₀, .error e, []) := rfl

@[simp] theorem srvFinishEmit_none {E σ α : Type} [SrvErr E] (s₀ s' : σ) (es : List WsEmit) :
    srvFinishEmit (E := E) s₀ (s', es, (none : Option (Except E α))) =
      (s₀, .error (SrvErr.ofApi (ApiError.internal "unreachable missing return")), []) := rfl

/-- No-Phantom-Broadcast Theorem: any rolled-back transaction emits strictly zero WebSocket events. -/
theorem srvFinishEmit_err_no_emits {E σ α : Type} [SrvErr E] (s₀ s' : σ) (es : List WsEmit) (e : E) :
    (srvFinishEmit (E := E) (α := α) s₀ (s', es, some (.error e))).2.2 = [] := rfl

/-- Transactional finalizer for emit-bearing `atomic:` blocks inside async handlers:
    discards both state mutations and accumulated emits on `.error`. -/
@[inline]
def srvAtomicCommitEmit {E σ α : Type} (s₀ : σ)
    (res : σ × List WsEmit × Option (Except E α)) : σ × (Option (Except E α) × List WsEmit) :=
  match res with
  | (s', es, none)                  => (s', none, es)
  | (s', es, some (Except.ok v))    => (s', some (Except.ok v), es)
  | (_,  _,  some (Except.error e)) => (s₀, some (Except.error e), [])

@[simp] theorem srvAtomicCommitEmit_none {E σ α : Type} (s₀ s' : σ) (es : List WsEmit) :
    srvAtomicCommitEmit (E := E) (α := α) s₀ (s', es, none) = (s', none, es) := rfl

@[simp] theorem srvAtomicCommitEmit_ok {E σ α : Type} (s₀ s' : σ) (es : List WsEmit) (v : α) :
    srvAtomicCommitEmit (E := E) s₀ (s', es, some (Except.ok v)) = (s', some (Except.ok v), es) := rfl

@[simp] theorem srvAtomicCommitEmit_err {E σ α : Type} (s₀ s' : σ) (es : List WsEmit) (e : E) :
    srvAtomicCommitEmit (E := E) (α := α) s₀ (s', es, some (Except.error e)) = (s₀, some (Except.error e), []) := rfl

/-- No-Phantom-Broadcast Theorem for `atomic:` blocks inside async handlers. -/
theorem srvAtomicCommitEmit_err_no_emits {E σ α : Type} (s₀ s' : σ) (es : List WsEmit) (e : E) :
    (srvAtomicCommitEmit (E := E) (α := α) s₀ (s', es, some (Except.error e))).2.2 = [] := rfl

/-- Effectful statement sequencing for `await`-containing handlers. -/
@[inline, specialize]
def srvSeqM {m : Type → Type} [Monad m] {ρ : Type}
    (first : m (Option ρ)) (next : Unit → m (Option ρ)) : m (Option ρ) := do
  match ← first with
  | some r => return some r
  | none   => next ()

@[inline, specialize]
def srvFinishM {E : Type} [SrvErr E] {m : Type → Type} [Monad m] {α : Type}
    (res : m (Option (Except E α))) : m (Except E α) := do
  match ← res with
  | some r => return r
  | none   => return .error (SrvErr.ofApi (ApiError.internal "unreachable missing return"))

/-! ## Opaque Equality-Abstracted SSA Stepping (`srvLetEq`) -/

/-- Continuation-passing equality binder keeping intermediate state updates opaque (`cdecl` + `hx : x = val`)
    so bounds checks and invariant leaves never suffer `zetaDelta` term-size blowup. -/
@[inline]
def srvLetEq {α β : Type} (val : α) (k : (x : α) → x = val → β) : β :=
  k val rfl

theorem srvLetEq_elim {α β : Type} (P : β → Prop) (val : α) (k : (x : α) → x = val → β)
    (hk : ∀ (x : α) (hx : x = val), P (k x hx)) : P (srvLetEq val k) :=
  hk val rfl

@[simp] theorem srvFinish_srvLetEq {E σ α γ : Type} [SrvErr E] (s₀ : σ) (val : γ)
    (k : (x : γ) → x = val → σ × Option (Except E α)) :
    srvFinish s₀ (srvLetEq val k) = srvLetEq val (fun x hx => srvFinish s₀ (k x hx)) := rfl

@[simp] theorem srvAtomicCommit_srvLetEq {E σ α γ : Type} (s₀ : σ) (val : γ)
    (k : (x : γ) → x = val → σ × Option (Except E α)) :
    srvAtomicCommit s₀ (srvLetEq val k) = srvLetEq val (fun x hx => srvAtomicCommit s₀ (k x hx)) := rfl

@[simp] theorem srvSeq_srvLetEq {σ ρ γ : Type} (val : γ)
    (k : (x : γ) → x = val → σ × Option ρ) (next : σ → σ × Option ρ) :
    srvSeq (srvLetEq val k) next = srvLetEq val (fun x hx => srvSeq (k x hx) next) := rfl

@[simp] theorem srvFinishEmit_srvLetEq {E σ α γ : Type} [SrvErr E] (s₀ : σ) (val : γ)
    (k : (x : γ) → x = val → σ × List WsEmit × Option (Except E α)) :
    srvFinishEmit s₀ (srvLetEq val k) = srvLetEq val (fun x hx => srvFinishEmit s₀ (k x hx)) := rfl

@[simp] theorem srvAtomicCommitEmit_srvLetEq {E σ α γ : Type} (s₀ : σ) (val : γ)
    (k : (x : γ) → x = val → σ × List WsEmit × Option (Except E α)) :
    srvAtomicCommitEmit s₀ (srvLetEq val k) = srvLetEq val (fun x hx => srvAtomicCommitEmit s₀ (k x hx)) := rfl

@[simp] theorem srvEmitSeq_srvLetEq {σ ρ γ : Type} (val : γ)
    (k : (x : γ) → x = val → σ × List WsEmit × Option ρ)
    (next : σ → List WsEmit → σ × List WsEmit × Option ρ) :
    srvEmitSeq (srvLetEq val k) next = srvLetEq val (fun x hx => srvEmitSeq (k x hx) next) := rfl

@[simp] theorem prod_fst_srvLetEq {α β γ : Type} (val : γ)
    (k : (x : γ) → x = val → α × β) :
    (srvLetEq val k).1 = srvLetEq val (fun x hx => (k x hx).1) := rfl

@[simp] theorem prod_snd_srvLetEq {α β γ : Type} (val : γ)
    (k : (x : γ) → x = val → α × β) :
    (srvLetEq val k).2 = srvLetEq val (fun x hx => (k x hx).2) := rfl

@[reducible, inline]
def srvGetAt {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) : α :=
  xs[i]'h

@[simp] theorem srvGetAt_eq {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) :
    srvGetAt xs i h = xs[i]'h := rfl

@[inline]
def srvWithNewState {σ : Type} (sNew : σ) (P : σ → Prop) : Prop := P sNew

@[simp] theorem srvWithNewState_srvLetEq {σ γ : Type} (val : γ)
    (k : (x : γ) → x = val → σ) (P : σ → Prop) :
    srvWithNewState (srvLetEq val k) P = srvLetEq val (fun x hx => srvWithNewState (k x hx) P) := rfl

theorem srvWithNewState_apply {σ : Type} (s : σ) (P : σ → Prop) :
    srvWithNewState s P = P s := rfl

@[inline]
def srvEnsPost {ε α : Type} (P : α → Prop) : Except ε α → Prop
  | .ok r    => P r
  | .error _ => True

@[simp] theorem srvEnsPost_ok {ε α : Type} (P : α → Prop) (r : α) :
    srvEnsPost (ε := ε) P (.ok r) = P r := rfl

@[simp] theorem srvEnsPost_err {ε α : Type} (P : α → Prop) (e : ε) :
    srvEnsPost P (.error e) = True := rfl

@[simp] theorem srvEnsPost_srvLetEq {ε α γ : Type} (P : α → Prop) (val : γ)
    (k : (x : γ) → x = val → Except ε α) :
    srvEnsPost P (srvLetEq val k) = srvLetEq val (fun x hx => srvEnsPost P (k x hx)) := rfl

@[inline]
def srvEnsPostOpt {ε α : Type} (P : α → Prop) : Except ε (Option α) → Prop
  | .ok (some r) => P r
  | _            => True

@[simp] theorem srvEnsPostOpt_some {ε α : Type} (P : α → Prop) (r : α) :
    srvEnsPostOpt (ε := ε) P (.ok (some r)) = P r := rfl

@[simp] theorem srvEnsPostOpt_none {ε α : Type} (P : α → Prop) :
    srvEnsPostOpt (ε := ε) P (.ok none) = True := rfl

@[simp] theorem srvEnsPostOpt_err {ε α : Type} (P : α → Prop) (e : ε) :
    srvEnsPostOpt P (.error e) = True := rfl

@[simp] theorem srvEnsPostOpt_srvLetEq {ε α γ : Type} (P : α → Prop) (val : γ)
    (k : (x : γ) → x = val → Except ε (Option α)) :
    srvEnsPostOpt P (srvLetEq val k) = srvLetEq val (fun x hx => srvEnsPostOpt P (k x hx)) := rfl

theorem getElem_congr_arr {α : Type} {xs ys : Array α} {j : Nat}
    (heq : ys = xs) (hj : j < ys.size) :
    ys[j]'hj = xs[j]'(heq ▸ hj) := by
  cases heq; rfl

theorem srvGetAt_congr_arr {α : Type} {xs ys : Array α} {j : Nat}
    (heq : ys = xs) (hj : j < ys.size) :
    srvGetAt ys j hj = xs[j]'(heq ▸ hj) := by
  cases heq; rfl

end Qed.Server
