import Qed.Json
import Qed.Proto
import Qed.Router
import Qed.Schema
import Qed.Resource

/-! ## Safe Array Indexing, Membership & Conservation Helpers -/

def Array.findIndex {α : Type} (xs : Array α) (p : α → Bool) : Option (Fin xs.size) :=
  Array.findFinIdx? p xs

def Array.sumBy {α : Type} (xs : Array α) (f : α → Nat) : Nat :=
  (xs.toList.map f).sum

@[simp] theorem Array.sumBy_empty {α : Type} (f : α → Nat) :
    (#[ ] : Array α).sumBy f = 0 := rfl

@[simp] theorem Array.sumBy_push {α : Type} (xs : Array α) (f : α → Nat) (v : α) :
    (xs.push v).sumBy f = xs.sumBy f + f v := by
  unfold Array.sumBy
  simp

private theorem list_sum_map_set {α : Type} (f : α → Nat) :
    ∀ (l : List α) (i : Nat) (v : α) (h : i < l.length),
      ((l.set i v).map f).sum + f l[i] = (l.map f).sum + f v
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => by
      simp [List.set]
      omega
  | _ :: xs, i + 1, v, h => by
      have hi : i < xs.length := Nat.lt_of_succ_lt_succ h
      have ih := list_sum_map_set f xs i v hi
      simp only [List.set, List.map_cons, List.sum_cons, List.getElem_cons_succ]
      omega

theorem Array.sumBy_set {α : Type} (xs : Array α) (f : α → Nat) (i : Nat) (v : α) (h : i < xs.size) :
    (xs.set i v h).sumBy f + f xs[i] = xs.sumBy f + f v := by
  unfold Array.sumBy
  rw [Array.toList_set]
  exact list_sum_map_set f xs.toList i v h

@[simp] theorem Array.forall_push {α : Type} {P : α → Prop} {xs : Array α} {v : α} :
    (∀ x ∈ xs.push v, P x) ↔ (∀ x ∈ xs, P x) ∧ P v := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (Array.mem_push.2 (.inl hx)),
           h v (Array.mem_push.2 (.inr rfl))⟩
  · rintro ⟨hxs, hv⟩ x hx
    rcases Array.mem_push.1 hx with hmem | rfl
    · exact hxs x hmem
    · exact hv

theorem Array.forall_set {α : Type} {P : α → Prop} {xs : Array α} {i : Nat} {v : α}
    (h : i < xs.size) (hxs : ∀ x ∈ xs, P x) (hv : P v) :
    ∀ x ∈ xs.set i v h, P x := by
  intro x hx
  rw [Array.mem_def, Array.toList_set] at hx
  rcases List.mem_or_eq_of_mem_set hx with hmem | rfl
  · exact hxs x (Array.mem_def.2 hmem)
  · exact hv

theorem Array.forall_elem {α : Type} {P : α → Prop} {xs : Array α} {i : Nat}
    (h : i < xs.size) (hxs : ∀ x ∈ xs, P x) : P xs[i] :=
  hxs xs[i] (Array.getElem_mem h)

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

theorem isSafeSegChar_no_inject {c : Char} (h : isSafeSegChar c = true) :
    c ≠ '/' ∧ c ≠ '?' ∧ c ≠ '#' ∧ c ≠ '\\' ∧ c ≠ '\r' ∧ c ≠ '\n' ∧ c ≠ '\x00' := by
  unfold isSafeSegChar Qed.isPctEncodedChar at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro heq; subst heq; simp at h)

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
  httpCall   : OutboundReq → m (Except ApiError OutboundResp)
  readEnv    : String → m (Option String)
  nowMs      : m UInt64
  randomHex  : UInt32 → m String
  hmacSha256 : ByteArray → ByteArray → m ByteArray

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

/-- Effect tree of a server handler thread executing non-blocking external I/O interleaved with
    single-step `atomic` shared-state transitions on `σ`. Notice `σ` is unreachable during
    `httpCall`, `readEnv`, `nowMs`, `randomHex`, and `hmacSha256` steps. -/
inductive ThreadProg (σ : Type) (α : Type) : Type where
  | pure       : α → ThreadProg σ α
  | httpCall   : OutboundReq → (Except ApiError OutboundResp → ThreadProg σ α) → ThreadProg σ α
  | readEnv    : String → (Option String → ThreadProg σ α) → ThreadProg σ α
  | nowMs      : (UInt64 → ThreadProg σ α) → ThreadProg σ α
  | randomHex  : UInt32 → (String → ThreadProg σ α) → ThreadProg σ α
  | hmacSha256 : ByteArray → ByteArray → (ByteArray → ThreadProg σ α) → ThreadProg σ α
  | atomic     : (σ → σ) → (σ → ThreadProg σ α) → ThreadProg σ α

namespace ThreadProg

def bind {σ α β : Type} : ThreadProg σ α → (α → ThreadProg σ β) → ThreadProg σ β
  | .pure a,             k => k a
  | .httpCall req f,     k => .httpCall req (fun r => bind (f r) k)
  | .readEnv v f,        k => .readEnv v (fun r => bind (f r) k)
  | .nowMs f,            k => .nowMs (fun r => bind (f r) k)
  | .randomHex n f,      k => .randomHex n (fun r => bind (f r) k)
  | .hmacSha256 key m f, k => .hmacSha256 key m (fun r => bind (f r) k)
  | .atomic st next,     k => .atomic st (fun s => bind (next s) k)

instance {σ : Type} : Monad (ThreadProg σ) where
  pure := .pure
  bind := ThreadProg.bind

instance {σ : Type} : MonadServer (ThreadProg σ) where
  httpCall req       := .httpCall req .pure
  readEnv v          := .readEnv v .pure
  nowMs              := .nowMs .pure
  randomHex n        := .randomHex n .pure
  hmacSha256 key msg := .hmacSha256 key msg .pure

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
  | httpCall _ _ ih => exact congrArg _ (funext ih)
  | readEnv _ _ ih => exact congrArg _ (funext ih)
  | nowMs _ ih => exact congrArg _ (funext ih)
  | randomHex _ _ ih => exact congrArg _ (funext ih)
  | hmacSha256 _ _ _ ih => exact congrArg _ (funext ih)
  | atomic _ _ ih => exact congrArg _ (funext ih)

/-- General two-state transition invariant across an async `ThreadProg`: every `atomic` step `s ↦ st s`
    may assume `Inv s` and must satisfy `Rel s (st s)` (covering single-state `Inv`, `old(...)`
    conservation/monotonicity laws, and `mutating <field> requires <cond>` access-control rules). -/
inductive ProgPreservesStepRel {σ α : Type} (Inv : σ → Prop) (Rel : σ → σ → Prop) :
    ThreadProg σ α → Prop where
  | pure (a : α) :
      ProgPreservesStepRel Inv Rel (.pure a)
  | httpCall (req : OutboundReq) (k : Except ApiError OutboundResp → ThreadProg σ α) :
      (∀ r, ProgPreservesStepRel Inv Rel (k r)) → ProgPreservesStepRel Inv Rel (.httpCall req k)
  | readEnv (v : String) (k : Option String → ThreadProg σ α) :
      (∀ r, ProgPreservesStepRel Inv Rel (k r)) → ProgPreservesStepRel Inv Rel (.readEnv v k)
  | nowMs (k : UInt64 → ThreadProg σ α) :
      (∀ r, ProgPreservesStepRel Inv Rel (k r)) → ProgPreservesStepRel Inv Rel (.nowMs k)
  | randomHex (n : UInt32) (k : String → ThreadProg σ α) :
      (∀ r, ProgPreservesStepRel Inv Rel (k r)) → ProgPreservesStepRel Inv Rel (.randomHex n k)
  | hmacSha256 (key msg : ByteArray) (k : ByteArray → ThreadProg σ α) :
      (∀ r, ProgPreservesStepRel Inv Rel (k r)) → ProgPreservesStepRel Inv Rel (.hmacSha256 key msg k)
  | atomic (st : σ → σ) (next : σ → ThreadProg σ α) :
      (∀ s, Inv s → Rel s (st s)) →
      (∀ s, Inv s → ProgPreservesStepRel Inv Rel (next s)) →
      ProgPreservesStepRel Inv Rel (.atomic st next)

/-- Single-state invariant preservation across an async `ThreadProg`. -/
abbrev ProgPreservesInv {σ α : Type} (Inv : σ → Prop) (p : ThreadProg σ α) : Prop :=
  ProgPreservesStepRel Inv (fun _ s' => Inv s') p

theorem progPreservesStepRel_to_inv {σ α : Type} {Inv : σ → Prop} {p : ThreadProg σ α}
    (h : ProgPreservesStepRel Inv (fun _ s' => Inv s') p) : ProgPreservesInv Inv p := h

theorem progPreservesStepRel_bind {σ α β : Type} {Inv : σ → Prop} {Rel : σ → σ → Prop}
    {p : ThreadProg σ α} {k : α → ThreadProg σ β}
    (hp : ProgPreservesStepRel Inv Rel p)
    (hk : ∀ a, ProgPreservesStepRel Inv Rel (k a)) :
    ProgPreservesStepRel Inv Rel (p >>= k) := by
  change ProgPreservesStepRel Inv Rel (ThreadProg.bind p k)
  induction hp with
  | pure a => exact hk a
  | httpCall _ _ _ ih | readEnv _ _ _ ih | nowMs _ _ ih | randomHex _ _ _ ih | hmacSha256 _ _ _ _ ih =>
      first | exact .httpCall _ _ ih | exact .readEnv _ _ ih | exact .nowMs _ ih
            | exact .randomHex _ _ ih | exact .hmacSha256 _ _ _ ih
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
  | stepHttp (s : σ) (pre post : List (ThreadProg σ Out))
      (req : OutboundReq) (k : Except ApiError OutboundResp → ThreadProg σ Out)
      (resp : Except ApiError OutboundResp) :
      MultiCoreStep Inv ⟨s, pre ++ .httpCall req k :: post⟩ ⟨s, pre ++ k resp :: post⟩
  | stepEnv (s : σ) (pre post : List (ThreadProg σ Out))
      (v : String) (k : Option String → ThreadProg σ Out) (val : Option String) :
      MultiCoreStep Inv ⟨s, pre ++ .readEnv v k :: post⟩ ⟨s, pre ++ k val :: post⟩
  | stepNow (s : σ) (pre post : List (ThreadProg σ Out))
      (k : UInt64 → ThreadProg σ Out) (t : UInt64) :
      MultiCoreStep Inv ⟨s, pre ++ .nowMs k :: post⟩ ⟨s, pre ++ k t :: post⟩
  | stepRand (s : σ) (pre post : List (ThreadProg σ Out))
      (n : UInt32) (k : String → ThreadProg σ Out) (hex : String) :
      MultiCoreStep Inv ⟨s, pre ++ .randomHex n k :: post⟩ ⟨s, pre ++ k hex :: post⟩
  | stepHmac (s : σ) (pre post : List (ThreadProg σ Out))
      (key msg : ByteArray) (k : ByteArray → ThreadProg σ Out) (mac : ByteArray) :
      MultiCoreStep Inv ⟨s, pre ++ .hmacSha256 key msg k :: post⟩ ⟨s, pre ++ k mac :: post⟩
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
  | stepHttp s pre post req k resp =>
      cases mid hpool with | httpCall _ _ hk => exact ⟨hinv, pool_replace_mid hpool (hk resp)⟩
  | stepEnv s pre post v k val =>
      cases mid hpool with | readEnv _ _ hk => exact ⟨hinv, pool_replace_mid hpool (hk val)⟩
  | stepNow s pre post k t =>
      cases mid hpool with | nowMs _ hk => exact ⟨hinv, pool_replace_mid hpool (hk t)⟩
  | stepRand s pre post n k hex =>
      cases mid hpool with | randomHex _ _ hk => exact ⟨hinv, pool_replace_mid hpool (hk hex)⟩
  | stepHmac s pre post key msg k mac =>
      cases mid hpool with | hmacSha256 _ _ _ hk => exact ⟨hinv, pool_replace_mid hpool (hk mac)⟩
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
  | httpCall (req : OutboundReq) (k : Except ApiError OutboundResp → ThreadProg σ α) :
      (∀ r, NoAtomic (k r)) → NoAtomic (.httpCall req k)
  | readEnv (v : String) (k : Option String → ThreadProg σ α) :
      (∀ r, NoAtomic (k r)) → NoAtomic (.readEnv v k)
  | nowMs (k : UInt64 → ThreadProg σ α) :
      (∀ r, NoAtomic (k r)) → NoAtomic (.nowMs k)
  | randomHex (n : UInt32) (k : String → ThreadProg σ α) :
      (∀ r, NoAtomic (k r)) → NoAtomic (.randomHex n k)
  | hmacSha256 (key msg : ByteArray) (k : ByteArray → ThreadProg σ α) :
      (∀ r, NoAtomic (k r)) → NoAtomic (.hmacSha256 key msg k)

class SafeIO {σ α : Type} (p : ThreadProg σ α) : Prop where
  noAtomic : NoAtomic p

instance {σ α : Type} (a : α) : SafeIO (Pure.pure (f := ThreadProg σ) a) := ⟨.pure a⟩
instance {σ α : Type} (a : α) : SafeIO (ThreadProg.pure (σ := σ) a) := ⟨.pure a⟩
instance {σ : Type} (req : OutboundReq) : SafeIO (MonadServer.httpCall (m := ThreadProg σ) req) :=
  ⟨.httpCall req _ (fun r => .pure r)⟩
instance {σ : Type} (v : String) : SafeIO (MonadServer.readEnv (m := ThreadProg σ) v) :=
  ⟨.readEnv v _ (fun r => .pure r)⟩
instance {σ : Type} : SafeIO (MonadServer.nowMs (m := ThreadProg σ)) :=
  ⟨.nowMs _ (fun r => .pure r)⟩
instance {σ : Type} (n : UInt32) : SafeIO (MonadServer.randomHex (m := ThreadProg σ) n) :=
  ⟨.randomHex n _ (fun r => .pure r)⟩
instance {σ : Type} (key msg : ByteArray) : SafeIO (MonadServer.hmacSha256 (m := ThreadProg σ) key msg) :=
  ⟨.hmacSha256 key msg _ (fun r => .pure r)⟩

theorem noAtomic_bind {σ α β : Type} {p : ThreadProg σ α} {k : α → ThreadProg σ β}
    (hp : NoAtomic p) (hk : ∀ a, NoAtomic (k a)) : NoAtomic (p >>= k) := by
  change NoAtomic (ThreadProg.bind p k)
  induction hp with
  | pure a => exact hk a
  | httpCall _ _ _ ih => exact .httpCall _ _ ih
  | readEnv _ _ _ ih => exact .readEnv _ _ ih
  | nowMs _ _ ih => exact .nowMs _ ih
  | randomHex _ _ _ ih => exact .randomHex _ _ ih
  | hmacSha256 _ _ _ _ ih => exact .hmacSha256 _ _ _ ih

instance {σ α β : Type} (p : ThreadProg σ α) (k : α → ThreadProg σ β)
    [hp : SafeIO p] [hk : ∀ a, SafeIO (k a)] : SafeIO (p >>= k) where
  noAtomic := noAtomic_bind hp.noAtomic (fun a => (hk a).noAtomic)

theorem safeIO_preservesStepRel {σ α : Type} {Inv : σ → Prop} {Rel : σ → σ → Prop}
    (p : ThreadProg σ α) [hp : SafeIO p] :
    ProgPreservesStepRel Inv Rel p := by
  induction hp.noAtomic with
  | pure a => exact .pure a
  | httpCall _ _ _ ih => exact .httpCall _ _ ih
  | readEnv _ _ _ ih => exact .readEnv _ _ ih
  | nowMs _ _ ih => exact .nowMs _ ih
  | randomHex _ _ _ ih => exact .randomHex _ _ ih
  | hmacSha256 _ _ _ _ ih => exact .hmacSha256 _ _ _ ih

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
  | httpCall (req : OutboundReq) (k : Except ApiError OutboundResp → ThreadProg σ α) :
      (∀ r, ProgEnsures Inv Post (k r)) → ProgEnsures Inv Post (.httpCall req k)
  | readEnv (v : String) (k : Option String → ThreadProg σ α) :
      (∀ r, ProgEnsures Inv Post (k r)) → ProgEnsures Inv Post (.readEnv v k)
  | nowMs (k : UInt64 → ThreadProg σ α) :
      (∀ r, ProgEnsures Inv Post (k r)) → ProgEnsures Inv Post (.nowMs k)
  | randomHex (n : UInt32) (k : String → ThreadProg σ α) :
      (∀ r, ProgEnsures Inv Post (k r)) → ProgEnsures Inv Post (.randomHex n k)
  | hmacSha256 (key msg : ByteArray) (k : ByteArray → ThreadProg σ α) :
      (∀ r, ProgEnsures Inv Post (k r)) → ProgEnsures Inv Post (.hmacSha256 key msg k)
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
  | httpCall _ _ _ ih | readEnv _ _ _ ih | nowMs _ _ ih | randomHex _ _ _ ih | hmacSha256 _ _ _ _ ih =>
      first | exact .httpCall _ _ ih | exact .readEnv _ _ ih | exact .nowMs _ ih
            | exact .randomHex _ _ ih | exact .hmacSha256 _ _ _ ih
  | atomic st _ _ ih => exact .atomic st _ ih

theorem safeIO_ensures_true {σ α : Type} {Inv : σ → Prop}
    (p : ThreadProg σ α) [hp : SafeIO p] :
    ProgEnsures Inv (fun _ => True) p := by
  induction hp.noAtomic with
  | pure a => exact .pure a trivial
  | httpCall _ _ _ ih => exact .httpCall _ _ ih
  | readEnv _ _ _ ih => exact .readEnv _ _ ih
  | nowMs _ _ ih => exact .nowMs _ ih
  | randomHex _ _ _ ih => exact .randomHex _ _ ih
  | hmacSha256 _ _ _ _ ih => exact .hmacSha256 _ _ _ ih

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
  | stepTargetHttp (s : σ) (os : List (ThreadProg σ Out))
      (req : OutboundReq) (k : Except ApiError OutboundResp → ThreadProg σ Tgt)
      (resp : Except ApiError OutboundResp) :
      TrackedMultiCoreStep Inv ⟨s, .httpCall req k, os⟩ ⟨s, k resp, os⟩
  | stepTargetEnv (s : σ) (os : List (ThreadProg σ Out))
      (v : String) (k : Option String → ThreadProg σ Tgt) (val : Option String) :
      TrackedMultiCoreStep Inv ⟨s, .readEnv v k, os⟩ ⟨s, k val, os⟩
  | stepTargetNow (s : σ) (os : List (ThreadProg σ Out))
      (k : UInt64 → ThreadProg σ Tgt) (tm : UInt64) :
      TrackedMultiCoreStep Inv ⟨s, .nowMs k, os⟩ ⟨s, k tm, os⟩
  | stepTargetRand (s : σ) (os : List (ThreadProg σ Out))
      (n : UInt32) (k : String → ThreadProg σ Tgt) (hex : String) :
      TrackedMultiCoreStep Inv ⟨s, .randomHex n k, os⟩ ⟨s, k hex, os⟩
  | stepTargetHmac (s : σ) (os : List (ThreadProg σ Out))
      (key msg : ByteArray) (k : ByteArray → ThreadProg σ Tgt) (mac : ByteArray) :
      TrackedMultiCoreStep Inv ⟨s, .hmacSha256 key msg k, os⟩ ⟨s, k mac, os⟩
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
  | stepTargetHttp s os req k resp =>
      cases htinv with | httpCall _ _ hk1 =>
      cases htens with | httpCall _ _ hk2 => exact ⟨hinv, hk1 resp, hk2 resp, hopool⟩
  | stepTargetEnv s os v k val =>
      cases htinv with | readEnv _ _ hk1 =>
      cases htens with | readEnv _ _ hk2 => exact ⟨hinv, hk1 val, hk2 val, hopool⟩
  | stepTargetNow s os k tm =>
      cases htinv with | nowMs _ hk1 =>
      cases htens with | nowMs _ hk2 => exact ⟨hinv, hk1 tm, hk2 tm, hopool⟩
  | stepTargetRand s os n k hex =>
      cases htinv with | randomHex _ _ hk1 =>
      cases htens with | randomHex _ _ hk2 => exact ⟨hinv, hk1 hex, hk2 hex, hopool⟩
  | stepTargetHmac s os key msg k mac =>
      cases htinv with | hmacSha256 _ _ _ hk1 =>
      cases htens with | hmacSha256 _ _ _ hk2 => exact ⟨hinv, hk1 mac, hk2 mac, hopool⟩
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

end Qed.Server
