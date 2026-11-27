import Qed.Field
import Qed.Json.Lawful
import Qed.Proto
import Qed.Dict
import Qed.Router.Basic
import Qed.Collection
import Qed.Server.Db.Core

namespace Qed.Server

/-! ## Structured Server Errors (`ApiError`) & Request Context (`RequestCtx`) -/

structure ApiError where
  code    : Nat := 400
  message : String
deriving Inhabited, DecidableEq, Repr

namespace ApiError
def badRequest   (msg : String) : ApiError := ⟨400, msg⟩
def unauthorized (msg : String := "unauthorized") : ApiError := ⟨401, msg⟩
def forbidden    (msg : String := "forbidden") : ApiError := ⟨403, msg⟩
def notFound     (msg : String := "not found") : ApiError := ⟨404, msg⟩
def internal     (msg : String) : ApiError := ⟨500, msg⟩
def httpStatus   (e : ApiError) : UInt32 := if 400 ≤ e.code && e.code < 600 then e.code.toUInt32 else 400
def wireMessage  (e : ApiError) (devMode : Bool) : String :=
  if !devMode && 500 ≤ e.httpStatus.toNat then "internal server error" else e.message
theorem wireMessage_prod_5xx (e : ApiError) (h : 500 ≤ e.httpStatus.toNat) :
    e.wireMessage false = "internal server error" := by
  simp [wireMessage, h]
instance : ToString ApiError := ⟨(·.message)⟩
instance : LawfulJson ApiError := .ofEquiv (fun e => (e.code, e.message)) (fun p => ⟨p.1, p.2⟩) (fun ⟨_, _⟩ => rfl)
instance : NonNullJson ApiError := ⟨nofun⟩
instance : LawfulProto ApiError := .ofEquiv (fun e => (e.code, e.message)) (fun p => ⟨p.1, p.2⟩) (fun ⟨_, _⟩ => rfl)
end ApiError

inductive AuthMethod where
  | none
  | session
  | bearer
  | oidcJwt
deriving Inhabited, DecidableEq, Repr

structure RequestCtx where
  headers     : List (String × String) := []
  cookies     : List (String × String) := []
  bearerToken : Option String := none
  userId      : Option String := none
  claims      : List (String × String) := []
  authMethod  : AuthMethod := .none
  clientIp    : String := "127.0.0.1"
  connId      : String := ""
  query       : String := ""
  body        : String := ""
  isSystem    : Bool := false
deriving Inhabited, DecidableEq, Repr

namespace RequestCtx
def header (ctx : RequestCtx) (name : String) : Option String :=
  let target := name.toLower; (ctx.headers.find? fun (k, _) => k.toLower == target).map Prod.snd
def cookie (ctx : RequestCtx) (name : String) : Option String := ctx.cookies.lookup name
def claim (ctx : RequestCtx) (name : String) : Option String :=
  (ctx.claims.lookup name).orElse fun _ => if name == "verified" then ctx.claims.lookup "email_verified" else none
def hasClaim (ctx : RequestCtx) (name expected : String) : Bool := ctx.claim name == some expected
def isAuthenticated (ctx : RequestCtx) : Bool := ctx.userId.isSome
def isSession (ctx : RequestCtx) : Bool := ctx.userId.isSome && ctx.authMethod == .session
def emailVerified (ctx : RequestCtx) : Bool := ctx.claim "email_verified" == some "true"
def queryParams (ctx : RequestCtx) : List (String × String) := Qed.parseQueryParams ctx.query
def queryParam (ctx : RequestCtx) (key : String) : Option String := ctx.queryParams.lookup key
def parseJson (ctx : RequestCtx) (α : Type) [FromJson α] (maxDepth : Nat := 64) : Except ApiError α :=
  ((Json.parse ctx.body maxDepth).bind FromJson.fromJson).mapError fun e => ApiError.badRequest s!"invalid JSON body: {e}"
end RequestCtx

/-! ## Validated HTTPS Webhook URLs & CRLF Header / Cookie Injection Closure -/

abbrev isValidWebhookUrl (s : String) : Bool :=
  Qed.Str.startsWith s "https://" && Qed.isSafeUrl s && s.toList.all fun c => c != '\\'
abbrev WebhookUrl := Qed.Field (fun s : String => isValidWebhookUrl s = true)
@[match_pattern] abbrev WebhookUrl.make (raw : String) (valid : isValidWebhookUrl raw = true := by decide) : WebhookUrl := Qed.Field.mk raw valid
@[inline] def WebhookUrl.parse? (raw : String) : Option WebhookUrl := Qed.Field.parse? (fun s => isValidWebhookUrl s = true) raw
@[inline] def WebhookUrl.parse (raw : String) : Except String WebhookUrl := Qed.Field.parse (fun s => isValidWebhookUrl s = true) "invalid WebhookUrl: expected safe https:// URL" raw
abbrev WebhookUrl.raw (u : WebhookUrl) : String := u.val
abbrev WebhookUrl.valid (u : WebhookUrl) : isValidWebhookUrl u.raw = true := u.ok

theorem WebhookUrl.isSafeUrl (u : WebhookUrl) : Qed.isSafeUrl u.raw = true := by
  have h := u.valid; simp only [isValidWebhookUrl, Bool.and_eq_true] at h; exact h.1.2

instance : Qed.ToHref WebhookUrl := ⟨fun u => ⟨u.raw, u.isSafeUrl⟩⟩

@[inline] def isSafeHeaderChar (c : Char) : Bool := let n := c.toNat; 32 ≤ n && n ≠ 127
def sanitizeHeader (s : String) : String := String.ofList (s.toList.filter isSafeHeaderChar)
def defaultCsp : String :=
  "default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline'; object-src 'none'; base-uri 'self'; frame-ancestors 'none'"

private abbrev NoCrlf (s : String) : Prop := ∀ c ∈ s.toList, c ≠ '\r' ∧ c ≠ '\n' ∧ c ≠ '\x00'
private theorem filter_no_crlf (p : Char → Bool) (hp : p '\r' = false ∧ p '\n' = false ∧ p '\x00' = false) (s : String) :
    NoCrlf (String.ofList (s.toList.filter p)) := by
  intro c hc; rw [String.toList_ofList, List.mem_filter] at hc
  refine ⟨?_, ?_, ?_⟩ <;> (intro heq; subst heq; simp [hp] at hc)
theorem header_no_crlf (s : String) : ∀ c ∈ (sanitizeHeader s).toList, c ≠ '\r' ∧ c ≠ '\n' ∧ c ≠ '\x00' :=
  filter_no_crlf isSafeHeaderChar (by decide) s

inductive SameSite where | lax | strict | none deriving Inhabited, DecidableEq, Repr
def SameSite.render : SameSite → String | .lax => "Lax" | .strict => "Strict" | .none => "None"
@[inline] def isSafeCookieAtomChar (c : Char) : Bool := let n := c.toNat; 33 ≤ n && n ≠ 127 && c ≠ ';' && c ≠ '=' && c ≠ ',' && c ≠ '"'
@[inline] def isSafeCookieValChar  (c : Char) : Bool := let n := c.toNat; 32 ≤ n && n ≠ 127 && c ≠ ';'
def sanitizeCookieName (s : String) : String := String.ofList (s.toList.filter isSafeCookieAtomChar)
def sanitizeCookieVal  (s : String) : String := String.ofList (s.toList.filter isSafeCookieValChar)

structure SetCookie where
  name     : String
  value    : String
  path     : String := "/"
  httpOnly : Bool := true
  sameSite : SameSite := .lax
  secure   : Bool := false
  maxAge?  : Option Nat := none
  domain?  : Option String := none
deriving Inhabited, DecidableEq, Repr

namespace SetCookie
def mkSafe (name value : String) (maxAge? : Option Nat := none) (secure : Bool := false)
    (httpOnly : Bool := true) (sameSite : SameSite := .lax) (path : String := "/") : SetCookie :=
  { name, value, path, httpOnly, sameSite, secure, maxAge? }
def clear (name : String) (path : String := "/") : SetCookie :=
  { name, value := "", path, httpOnly := true, sameSite := .lax, maxAge? := some 0 }
def render (c : SetCookie) : String :=
  let pth := sanitizeCookieVal (if c.path.isEmpty then "/" else c.path)
  let dom := match c.domain? with
    | some d => let sd := sanitizeCookieVal d; if sd.isEmpty then "" else "; Domain=" ++ sd | none => ""
  let age := match c.maxAge? with | some n => "; Max-Age=" ++ toString n | none => ""
  sanitizeCookieName c.name ++ "=" ++ sanitizeCookieVal c.value ++ "; Path=" ++ pth ++
    dom ++ age ++ (if c.secure then "; Secure" else "") ++
    (if c.httpOnly then "; HttpOnly" else "") ++ "; SameSite=" ++ c.sameSite.render

private theorem noCrlfApp {a b : String} (ha : NoCrlf a) (hb : NoCrlf b) : NoCrlf (a ++ b) := fun c hc =>
  (List.mem_append.1 (String.toList_append ▸ hc)).elim (ha c) (hb c)
private theorem noCrlfIte (b : Bool) {t e : String} (ht : NoCrlf t) (he : NoCrlf e) : NoCrlf (if b then t else e) := by cases b <;> assumption
private theorem noCrlfLit (s : String) (h : s.toList.all (fun c => c != '\r' && c != '\n' && c != '\x00') = true) : NoCrlf s := by
  intro c hc; have := (List.all_eq_true.1 h) c hc; simp only [Bool.and_eq_true, bne_iff_ne] at this; exact ⟨this.1.1, this.1.2, this.2⟩
private theorem nat_toString_no_crlf (n : Nat) : NoCrlf (toString n) := fun c hc =>
  let hb := Qed.Server.Db.nat_toString_digits n c hc
  ⟨fun h => absurd (h ▸ hb) (by decide), fun h => absurd (h ▸ hb) (by decide), fun h => absurd (h ▸ hb) (by decide)⟩
local infixl:65 " ++ᶜ " => noCrlfApp

theorem render_no_crlf (c : SetCookie) : ∀ ch ∈ c.render.toList, ch ≠ '\r' ∧ ch ≠ '\n' ∧ ch ≠ '\x00' := by
  rcases c with ⟨name, val, path, ho, ss, sec, age, dom⟩
  unfold SetCookie.render; dsimp only
  have hVal (s : String) : NoCrlf (sanitizeCookieVal s) := filter_no_crlf isSafeCookieValChar (by decide) s
  have hDom : NoCrlf (match dom with | some d => let sd := sanitizeCookieVal d; if sd.isEmpty then "" else "; Domain=" ++ sd | none => "") := by
    cases dom with | none => exact noCrlfLit "" rfl | some d => exact noCrlfIte _ (noCrlfLit "" rfl) (noCrlfLit "; Domain=" rfl ++ᶜ hVal d)
  have hAge : NoCrlf (match age with | some n => "; Max-Age=" ++ toString n | none => "") := by
    cases age with | none => exact noCrlfLit "" rfl | some n => exact noCrlfLit "; Max-Age=" rfl ++ᶜ nat_toString_no_crlf n
  exact filter_no_crlf isSafeCookieAtomChar (by decide) name ++ᶜ noCrlfLit "=" rfl ++ᶜ hVal val ++ᶜ noCrlfLit "; Path=" rfl ++ᶜ hVal _ ++ᶜ
    hDom ++ᶜ hAge ++ᶜ noCrlfIte sec (noCrlfLit "; Secure" rfl) (noCrlfLit "" rfl) ++ᶜ
    noCrlfIte ho (noCrlfLit "; HttpOnly" rfl) (noCrlfLit "" rfl) ++ᶜ
    noCrlfLit "; SameSite=" rfl ++ᶜ (show NoCrlf ss.render by cases ss <;> exact noCrlfLit _ rfl)
end SetCookie

/-! ## SSE Events & Custom HTTP Responses -/

structure SseEvent where
  data  : String
  event : Option String := none
  id    : Option String := none
  retry : Option Nat := none
deriving Inhabited, DecidableEq, Repr

namespace SseEvent
def msg (data : String) (event : Option String := none) (id : Option String := none) (retry : Option Nat := none) : SseEvent :=
  { data, event, id, retry }
def render (ev : SseEvent) : String :=
  let line (k : String) (v? : Option String) := (v?.map (s!"{k}: {·}\n")).getD ""
  let cleanData := ev.data.replace "\r\n" "\n" |>.replace "\r" "\n"
  line "event" (ev.event.map sanitizeHeader) ++ line "id" (ev.id.map sanitizeHeader) ++
    line "retry" (ev.retry.map toString) ++ String.join ((cleanData.splitOn "\n").map ("data: " ++ · ++ "\n")) ++ "\n"
def formatStream (events : List SseEvent) : ByteArray := (String.join (events.map SseEvent.render)).toUTF8
end SseEvent

structure HttpResponse where
  status      : Nat := 200
  contentType : String := "text/plain; charset=utf-8"
  body        : ByteArray := ByteArray.empty
  headers     : List (String × String) := []
  cookies     : List SetCookie := []
deriving Inhabited

namespace HttpResponse
def bytes (contentType : String) (body : ByteArray) (status : Nat := 200)
    (headers : List (String × String) := []) (cookies : List SetCookie := []) : HttpResponse :=
  { status, contentType, body, headers, cookies }
local macro "respStr " n:ident ct:str : command =>
  `(def $n (body : String) (status : Nat := 200) (headers : List (String × String) := []) (cookies : List SetCookie := []) : HttpResponse :=
      bytes $ct body.toUTF8 status headers cookies)
respStr text "text/plain; charset=utf-8"
respStr json "application/json; charset=utf-8"
respStr html "text/html; charset=utf-8"
def jsonOf {α : Type} [ToJson α] (val : α) (status : Nat := 200) (headers : List (String × String) := []) (cookies : List SetCookie := []) : HttpResponse :=
  json (Json.render (toJson val)) status headers cookies
def redirect (location : Qed.HrefTarget) (status : Nat := 302) (cookies : List SetCookie := []) : HttpResponse :=
  bytes "text/plain; charset=utf-8" ByteArray.empty status [("Location", sanitizeHeader location.raw)] cookies
def sse (events : List SseEvent) (headers : List (String × String) := []) (cookies : List SetCookie := []) : HttpResponse :=
  bytes "text/event-stream; charset=utf-8" (SseEvent.formatStream events) 200 ([("Cache-Control", "no-cache"), ("X-Accel-Buffering", "no")] ++ headers) cookies
end HttpResponse

/-! ## SSRF Origin-Pinning & Path-Traversal Closure (`external_url_preserves_origin`) -/

abbrev isSafeSegChar : Char → Bool := Qed.isPctEncodedChar
@[inline] def isSafeLitSegChar (c : Char) : Bool := isSafeSegChar c || c == ':'
@[inline] def isSafeExtSuffixChar (c : Char) : Bool :=
  isSafeSegChar c || c == '/' || c == '?' || c == '&' || c == '=' || c == ':' || c == '+' || c == ','
abbrev pctEncode : String → String := Qed.encodeSeg
theorem pctEncode_safe (s : String) : (pctEncode s).toList.all isSafeSegChar = true := Qed.encodeSeg_pct s
theorem isSafeExtSuffixChar_no_smuggle {c : Char} (h : isSafeExtSuffixChar c = true) :
    c ≠ '#' ∧ c ≠ '\\' ∧ c ≠ '\r' ∧ c ≠ '\n' ∧ c ≠ '\x00' ∧ c ≠ '@' := by
  unfold isSafeExtSuffixChar isSafeSegChar Qed.isPctEncodedChar at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro heq; subst heq; simp at h)
private theorem safeSeg_implies_extSuffix {s : String} (h : s.toList.all isSafeSegChar = true) :
    s.toList.all isSafeExtSuffixChar = true :=
  List.all_eq_true.2 fun c hc => by simp [isSafeExtSuffixChar, List.all_eq_true.1 h c hc]
private theorem safeLitSeg_implies_extSuffix {s : String} (h : s.toList.all isSafeLitSegChar = true) :
    s.toList.all isSafeExtSuffixChar = true :=
  List.all_eq_true.2 fun c hc => by
    have h' := List.all_eq_true.1 h c hc
    simp only [isSafeLitSegChar, isSafeExtSuffixChar, Bool.or_eq_true] at h' ⊢
    rcases h' with h1 | h2
    · simp [h1]
    · simp [h2]

private def rawSingleSeg (s : String) : String := if s == "." then "%2E" else if s == ".." then "%2E%2E" else pctEncode s
def encodeSingleSeg (s : String) : Except ApiError String :=
  let enc := rawSingleSeg s
  if enc.isEmpty || enc == "." || enc == ".." then .error (ApiError.badRequest "URL path segment cannot be empty or dot-traversal") else .ok enc
theorem encodeSingleSeg_safe {s out : String} (h : encodeSingleSeg s = .ok out) :
    out ≠ "" ∧ out ≠ "." ∧ out ≠ ".." ∧ out.toList.all isSafeSegChar = true := by
  unfold encodeSingleSeg at h; dsimp only at h; split at h
  · contradiction
  · rename_i hbad; injection h with h; subst h; simp only [Bool.or_eq_true, String.isEmpty_iff, beq_iff_eq, not_or] at hbad
    refine ⟨hbad.1.1, hbad.1.2, hbad.2, ?_⟩
    unfold rawSingleSeg; split <;> first | decide | (split <;> first | decide | exact pctEncode_safe s)

private theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by cases x with | error _ => cases h | ok a => exact ⟨a, rfl, h⟩
private theorem list_mapM_except_all {α β ε : Type} {f : α → Except ε β} {P : β → Prop}
    (hf : ∀ a b, f a = .ok b → P b) {xs : List α} {ys : List β} (h : xs.mapM f = .ok ys) : ∀ y ∈ ys, P y := by
  let rec go : ∀ (l : List α) (acc r : List β), (∀ y ∈ acc, P y) → List.mapM.loop f l acc = .ok r → ∀ y ∈ r, P y
    | [], acc, _, hacc, h => by injection h with h; subst h; exact fun y hy => hacc y (List.mem_reverse.1 hy)
    | x :: l, acc, r, hacc, h => let ⟨b, hx, hrest⟩ := except_bind_ok h; go l (b :: acc) r (fun y hy => (List.mem_cons.1 hy).elim (· ▸ hf x b hx) (hacc y)) hrest
  exact go xs [] ys (fun _ hm => nomatch hm) h
private def joinDelim (sep : Char) : List String → String
  | [] => "" | [s] => s | s :: ss => s ++ String.singleton sep ++ joinDelim sep ss
private theorem joinDelim_safe {sep : Char} (hsep : isSafeExtSuffixChar sep = true) :
    ∀ (ss : List String), (∀ s ∈ ss, s.toList.all isSafeExtSuffixChar = true) → (joinDelim sep ss).toList.all isSafeExtSuffixChar = true
  | [], _ => rfl | [s], hs => hs s (by simp)
  | s₁ :: s₂ :: rest, hs => by simp [joinDelim, String.toList_append, hs s₁ (by simp), hsep, joinDelim_safe hsep (s₂ :: rest) (fun x hx => hs x (by simp [hx]))]

private def encodeMultiSegElem (seg : String) : Except ApiError String :=
  if seg.isEmpty || seg == "." || seg == ".." then .error (ApiError.badRequest "invalid multi-segment URL path component") else encodeSingleSeg seg
def encodeMultiSeg (s : String) : Except ApiError String := do
  let trimmed := match s.toList with | '/' :: cs => String.ofList cs | _ => s
  let segs ← match trimmed.splitOn "/" with | [] => .error (ApiError.badRequest "multi-segment URL path cannot be empty") | xs => xs.mapM encodeMultiSegElem
  return joinDelim '/' segs
theorem encodeMultiSeg_safe {s out : String} (h : encodeMultiSeg s = .ok out) : out.toList.all isSafeExtSuffixChar = true := by
  unfold encodeMultiSeg at h; dsimp only at h; split at h
  · cases h
  · rcases except_bind_ok h with ⟨segs, hm, hret⟩; cases hret
    refine joinDelim_safe (sep := '/') rfl segs (list_mapM_except_all (fun _ _ hab => ?_) hm)
    unfold encodeMultiSegElem at hab; split at hab <;> first | cases hab | exact safeSeg_implies_extSuffix (encodeSingleSeg_safe hab).2.2.2

inductive SegPiece where | lit (s : String) | param (val : String) deriving Inhabited, DecidableEq, Repr
inductive PathPart where | lit (seg : String) | seg (val : String) | multiSeg (val : String) | compound (pieces : List SegPiece) deriving Inhabited, DecidableEq, Repr
inductive QueryVal where | lit (val : String) | param (val : String) | omit deriving Inhabited, DecidableEq, Repr

class ToQueryVal (α : Type) where
  toQueryVal : α → QueryVal
instance (priority := low) {α : Type} [RouteParam α] : ToQueryVal α := ⟨fun a => .param (RouteParam.toSeg a)⟩
instance : ToQueryVal Bool := ⟨fun b => .param (if b then "true" else "false")⟩
instance {α : Type} [ToQueryVal α] : ToQueryVal (Option α) := ⟨fun | some a => ToQueryVal.toQueryVal a | none => .omit⟩

class ToHeaderVal (α : Type) where
  toHeaderVal? : α → Option String
instance (priority := low) {α : Type} [RouteParam α] : ToHeaderVal α := ⟨fun a => some (RouteParam.toSeg a)⟩
instance : ToHeaderVal Bool := ⟨fun b => some (if b then "true" else "false")⟩
instance {α : Type} [ToHeaderVal α] : ToHeaderVal (Option α) := ⟨fun | some a => ToHeaderVal.toHeaderVal? a | none => none⟩

mutual
  def jsonToFormFields (pfx : String) : Json → List (String × String)
    | .null => []
    | .bool b => if pfx.isEmpty then [] else [(pfx, if b then "true" else "false")]
    | .num n => if pfx.isEmpty then [] else [(pfx, String.ofList (Json.renderNumL n))]
    | .str s => if pfx.isEmpty then [] else [(pfx, s)]
    | .arr es => jsonArrToFormFields pfx 0 es
    | .obj ms => jsonObjToFormFields pfx ms
  def jsonArrToFormFields (pfx : String) (idx : Nat) : List Json → List (String × String)
    | [] => []
    | e :: es =>
        let key := if pfx.isEmpty then toString idx else pfx ++ "[" ++ toString idx ++ "]"
        jsonToFormFields key e ++ jsonArrToFormFields pfx (idx + 1) es
  def jsonObjToFormFields (pfx : String) : List (String × Json) → List (String × String)
    | [] => []
    | (k, v) :: ms =>
        let key := if pfx.isEmpty then k else pfx ++ "[" ++ k ++ "]"
        jsonToFormFields key v ++ jsonObjToFormFields pfx ms
end

class ToFormFields (α : Type) where
  toFormFields : α → List (String × String)
instance : ToFormFields (List (String × String)) := ⟨id⟩
instance : ToFormFields (Array (String × String)) := ⟨Array.toList⟩
instance : ToFormFields (Qed.Dict String String) := ⟨fun d => d.entriesList⟩
instance (priority := low) {α : Type} [ToJson α] : ToFormFields α := ⟨fun a => jsonToFormFields "" (toJson a)⟩

def encodeFormBodyOf {α : Type} [ToFormFields α] (val : α) : ByteArray :=
  (Qed.encodeFormBody (ToFormFields.toFormFields val)).toUTF8

private def hasValidOriginBody (base : String) : Bool :=
  base.toList.getLast? != some '/' && base.toList.all fun c => isSafeUrlChar c && c != '?' && c != '#' && c != '\\' && c != '@' && decide (32 < c.toNat ∧ c.toNat ≠ 127)
def isValidBaseOrigin (base : String) : Bool := (Qed.Str.startsWith base "https://" || Qed.Str.startsWith base "http://") && hasValidOriginBody base
def isValidWsBaseOrigin (base : String) : Bool :=
  (Qed.Str.startsWith base "wss://" || Qed.Str.startsWith base "ws://" || Qed.Str.startsWith base "https://" || Qed.Str.startsWith base "http://") && hasValidOriginBody base
def toWsOrigin (base : String) : String :=
  if base.startsWith "https://" then "wss://" ++ String.ofList (base.toList.drop 8)
  else if base.startsWith "http://" then "ws://" ++ String.ofList (base.toList.drop 7) else base

private def concatStrings : List String → String
  | [] => "" | s :: ss => s ++ concatStrings ss
private theorem concatStrings_safe {ss : List String} (hs : ∀ s ∈ ss, s.toList.all isSafeExtSuffixChar = true) :
    (concatStrings ss).toList.all isSafeExtSuffixChar = true := by
  induction ss with
  | nil => rfl
  | cons s rest ih => simp [concatStrings, String.toList_append, hs s (by simp), ih (fun x hx => hs x (by simp [hx]))]
private def renderSegPiece : SegPiece → Except ApiError String
  | .lit s => if s.toList.all isSafeLitSegChar then .ok s else .error (ApiError.internal "invalid static path literal in external endpoint")
  | .param v => encodeSingleSeg v
private def renderPathPart : PathPart → Except ApiError String
  | .lit s => if !s.isEmpty && s != "." && s != ".." && s.toList.all isSafeLitSegChar then .ok s else .error (ApiError.internal "invalid static path literal in external endpoint")
  | .seg v => encodeSingleSeg v | .multiSeg v => encodeMultiSeg v
  | .compound ps => do
      let joined := concatStrings (← ps.mapM renderSegPiece)
      if joined.isEmpty || joined == "." || joined == ".." then .error (ApiError.badRequest "URL path segment cannot be empty or dot-traversal") else .ok joined
private def renderQueryPairs : List (String × QueryVal) → List String
  | [] => []
  | (_, .omit) :: rest => renderQueryPairs rest
  | (k, .lit r) :: rest | (k, .param r) :: rest => (pctEncode k ++ "=" ++ pctEncode r) :: renderQueryPairs rest
private theorem renderQueryPairs_safe : ∀ (qs : List (String × QueryVal)) (p : String), p ∈ renderQueryPairs qs → p.toList.all isSafeExtSuffixChar = true
  | [], _, hm => nomatch hm
  | (_, .omit) :: rest, p, hm => renderQueryPairs_safe rest p hm
  | (k, .lit r) :: rest, p, hm => (List.mem_cons.1 hm).elim
      (fun heq => by subst heq; have hk := safeSeg_implies_extSuffix (pctEncode_safe k); have heq' : isSafeExtSuffixChar '=' = true := rfl
                     simp [String.toList_append, hk, heq', safeSeg_implies_extSuffix (pctEncode_safe r)])
      (renderQueryPairs_safe rest p)
  | (k, .param r) :: rest, p, hm => (List.mem_cons.1 hm).elim
      (fun heq => by subst heq; have hk := safeSeg_implies_extSuffix (pctEncode_safe k); have heq' : isSafeExtSuffixChar '=' = true := rfl
                     simp [String.toList_append, hk, heq', safeSeg_implies_extSuffix (pctEncode_safe r)])
      (renderQueryPairs_safe rest p)

def buildExternalSuffix (parts : List PathPart) (query : List (String × QueryVal)) : Except ApiError String := do
  let pathStr := joinDelim '/' (← parts.mapM renderPathPart)
  let qPairs := renderQueryPairs query
  return if qPairs.isEmpty then pathStr else pathStr ++ "?" ++ joinDelim '&' qPairs
theorem buildExternalSuffix_safe {parts : List PathPart} {query : List (String × QueryVal)} {sfx : String}
    (h : buildExternalSuffix parts query = .ok sfx) : sfx.toList.all isSafeExtSuffixChar = true := by
  unfold buildExternalSuffix at h; rcases except_bind_ok h with ⟨segs, hr, hret⟩
  have hsegs : ∀ seg ∈ segs, seg.toList.all isSafeExtSuffixChar = true := list_mapM_except_all (fun p seg hp => by
    cases p with
    | lit s => dsimp only [renderPathPart] at hp; split at hp <;> first
        | (rename_i hok; injection hp with hp; subst hp; simp only [Bool.and_eq_true] at hok; exact safeLitSeg_implies_extSuffix hok.2) | contradiction
    | seg _ => exact safeSeg_implies_extSuffix (encodeSingleSeg_safe hp).2.2.2
    | multiSeg _ => exact encodeMultiSeg_safe hp
    | compound ps =>
        dsimp only [renderPathPart] at hp; rcases except_bind_ok hp with ⟨pcs, hpcs, hjoin⟩
        split at hjoin
        · cases hjoin
        · injection hjoin with hjoin; subst hjoin
          refine concatStrings_safe (list_mapM_except_all (fun pc rendered hpc => by
            cases pc with
            | lit s => dsimp only [renderSegPiece] at hpc; split at hpc <;> first
                | (rename_i hok; injection hpc with hpc; subst hpc; exact safeLitSeg_implies_extSuffix hok) | contradiction
            | param _ => exact safeSeg_implies_extSuffix (encodeSingleSeg_safe hpc).2.2.2) hpcs)) hr
  have hpath := joinDelim_safe (sep := '/') rfl segs hsegs
  by_cases hq : (renderQueryPairs query).isEmpty <;> (simp [hq, pure, Except.pure] at hret; subst hret)
  · exact hpath
  · have hqchar : isSafeExtSuffixChar '?' = true := rfl
    simp [String.toList_append, hpath, hqchar, joinDelim_safe (sep := '&') rfl _ (renderQueryPairs_safe query)]

def buildExternalUrl (base : String) (parts : List PathPart) (query : List (String × QueryVal)) : Except ApiError String := do
  return (base ++ "/") ++ (← buildExternalSuffix parts query)
theorem external_url_preserves_origin (base : String) (parts : List PathPart) (query : List (String × QueryVal)) (url : String)
    (h : buildExternalUrl base parts query = .ok url) :
    url.startsWith (base ++ "/") = true ∧
    ∃ sfx : String, url = (base ++ "/") ++ sfx ∧ (∀ c ∈ sfx.toList, c ≠ '#' ∧ c ≠ '\\' ∧ c ≠ '\r' ∧ c ≠ '\n' ∧ c ≠ '\x00' ∧ c ≠ '@') := by
  rcases except_bind_ok h with ⟨sfx, hs, hret⟩; injection hret with hret; subst hret
  exact ⟨by simp, sfx, rfl, fun c hc => isSafeExtSuffixChar_no_smuggle (List.all_eq_true.1 (buildExternalSuffix_safe hs) c hc)⟩
def buildExternalWsUrl (base : String) (parts : List PathPart) (query : List (String × QueryVal)) : Except ApiError String :=
  buildExternalUrl (toWsOrigin base) parts query
theorem external_ws_url_preserves_origin (base : String) (parts : List PathPart) (query : List (String × QueryVal)) (url : String)
    (h : buildExternalWsUrl base parts query = .ok url) :
    url.startsWith (toWsOrigin base ++ "/") = true ∧
    ∃ sfx : String, url = (toWsOrigin base ++ "/") ++ sfx ∧ (∀ c ∈ sfx.toList, c ≠ '#' ∧ c ≠ '\\' ∧ c ≠ '\r' ∧ c ≠ '\n' ∧ c ≠ '\x00' ∧ c ≠ '@') :=
  external_url_preserves_origin (toWsOrigin base) parts query url h

/-! ## External Auth Specs, Outbound HTTP & `MonadServer` / `MonadAtomic` -/

inductive AuthSpec where
  | none | bearerSecret (envVar : String) | headerSecret (headerName envVar : String)
  | gcpServiceAccount (envVar scope : String) | gcpMetadata (audience? : Option String := none)
deriving Inhabited, DecidableEq, Repr
def AuthSpec.requiredSecrets : AuthSpec → List String
  | .none | .gcpMetadata _ => [] | .bearerSecret v | .headerSecret _ v | .gcpServiceAccount v _ => [v]

structure OutboundReq where
  serviceName  : String
  baseOrigin   : String
  method       : String
  pathAndQuery : String
  headers      : List (String × String)
  body         : ByteArray
  auth         : AuthSpec := .none
  ssrfGuard    : Bool := true
deriving Inhabited, DecidableEq

def OutboundReq.url (r : OutboundReq) : String := r.baseOrigin ++ r.pathAndQuery
def OutboundReq.bodyStr (r : OutboundReq) : String := (String.fromUTF8? r.body).getD ""

structure OutboundResp where
  status  : UInt32
  body    : ByteArray
  headers : List (String × String) := []
deriving Inhabited, DecidableEq

inductive ServerEffect : Type where
  | httpCall (req : OutboundReq) | dbExec (cfg : Db.DbConfig) (q : Db.SqlQuery) | dbExecDdl (cfg : Db.DbConfig)
  | dbTxBegin (cfg : Db.DbConfig) | dbTxExec (cfg : Db.DbConfig) (txId : UInt64) (q : Db.SqlQuery)
  | dbTxCommit (cfg : Db.DbConfig) (txId : UInt64) | dbTxRollback (cfg : Db.DbConfig) (txId : UInt64)
  | setCookie (cookie : SetCookie) | sendSse (ev : SseEvent) | readEnv (v : String) | nowMs
  | randomHex (n : UInt32) | randomBytes (n : UInt32) | hmacSha256 (key msg : ByteArray)
  | sha256 (data : ByteArray) | constEq (a b : ByteArray) | wsBroadcast (t : String) (p : ByteArray)
  | aeadEncrypt (keyEnv : String) (fallback? : Option String) (aad pt : ByteArray)
  | aeadDecrypt (keyEnv : String) (fallback? : Option String) (aad ct : ByteArray)

@[reducible] def ServerEffect.Resp : ServerEffect → Type
  | .httpCall _ => Except ApiError OutboundResp | .dbExec _ _ | .dbTxExec _ _ _ => Except ApiError Db.DbResult
  | .dbExecDdl _ | .dbTxCommit _ _ => Except ApiError Unit | .dbTxBegin _ => Except ApiError UInt64
  | .dbTxRollback _ _ | .setCookie _ | .sendSse _ | .wsBroadcast _ _ => Unit
  | .readEnv _ => Option String | .nowMs => UInt64 | .randomHex _ => String | .randomBytes _ => ByteArray
  | .hmacSha256 _ _ | .sha256 _ => ByteArray | .constEq _ _ => Bool
  | .aeadEncrypt _ _ _ _ | .aeadDecrypt _ _ _ _ => Except ApiError ByteArray

class MonadServer (m : Type → Type) where exec : (eff : ServerEffect) → m eff.Resp

namespace MonadServer
local macro "srvEff2 " n1:ident bs1:bracketedBinder* " : " r1:term " => " e1:term " ; "
                       n2:ident bs2:bracketedBinder* " : " r2:term " => " e2:term : command =>
  `(@[reducible, inline] def $n1 {m : Type → Type} [MonadServer m] $bs1* : m $r1 := exec $e1
    @[reducible, inline] def $n2 {m : Type → Type} [MonadServer m] $bs2* : m $r2 := exec $e2)
srvEff2 httpCall (req : OutboundReq) : Except ApiError OutboundResp => .httpCall req ; dbExec (cfg : Db.DbConfig) (q : Db.SqlQuery) : Except ApiError Db.DbResult => .dbExec cfg q
srvEff2 dbExecDdl (cfg : Db.DbConfig) : Except ApiError Unit => .dbExecDdl cfg ; dbTxBegin (cfg : Db.DbConfig) : Except ApiError UInt64 => .dbTxBegin cfg
srvEff2 dbTxExec (cfg : Db.DbConfig) (txId : UInt64) (q : Db.SqlQuery) : Except ApiError Db.DbResult => .dbTxExec cfg txId q ; dbTxCommit (cfg : Db.DbConfig) (txId : UInt64) : Except ApiError Unit => .dbTxCommit cfg txId
srvEff2 dbTxRollback (cfg : Db.DbConfig) (txId : UInt64) : Unit => .dbTxRollback cfg txId ; setCookie (c : SetCookie) : Unit => .setCookie c
srvEff2 sendSse (ev : SseEvent) : Unit => .sendSse ev ; readEnv (v : String) : Option String => .readEnv v
srvEff2 nowMs : UInt64 => .nowMs ; randomHex (n : UInt32) : String => .randomHex n
srvEff2 randomBytes (n : UInt32) : ByteArray => .randomBytes n ; hmacSha256 (key msg : ByteArray) : ByteArray => .hmacSha256 key msg
srvEff2 sha256 (data : ByteArray) : ByteArray => .sha256 data ; constEq (a b : ByteArray) : Bool => .constEq a b
srvEff2 wsBroadcast (t : String) (p : ByteArray) : Unit => .wsBroadcast t p ; aeadEncrypt (keyEnv : String) (fallback? : Option String) (aad pt : ByteArray) : Except ApiError ByteArray => .aeadEncrypt keyEnv fallback? aad pt
@[reducible, inline] def aeadDecrypt {m : Type → Type} [MonadServer m] (keyEnv : String) (fallback? : Option String) (aad ct : ByteArray) : m (Except ApiError ByteArray) := exec (.aeadDecrypt keyEnv fallback? aad ct)
end MonadServer

structure WsEmit where
  topic   : String
  payload : ByteArray
deriving Inhabited, DecidableEq

/-- Per-subscriber WebSocket broadcast projection result (`Option (Option ByteArray)` ABI for FFI):
    `none` = passthrough raw payload, `some (some bytes)` = send projected bytes, `some none` = drop. -/
abbrev WsProjectOut := Option (Option ByteArray)
namespace WsProjectOut
@[inline] def passthrough : WsProjectOut := none
@[inline] def send (payload : ByteArray) : WsProjectOut := some (some payload)
@[inline] def drop : WsProjectOut := some none
end WsProjectOut

@[specialize] def flushWsEmits {m : Type → Type} [Monad m] [MonadServer m] : List WsEmit → m Unit
  | [] => pure () | e :: es => MonadServer.wsBroadcast e.topic e.payload >>= fun _ => flushWsEmits es

class MonadAtomic (σ : Type) (m : Type → Type) where
  runAtomic     : {α : Type} → (σ → σ × α) → m α
  runAtomicRead : {α : Type} → (σ → α) → m α := fun f => runAtomic (fun s => (s, f s))

@[simp] theorem readOnly_preserves_state {σ α β : Type} (f : σ → RequestCtx → α → β) (s : σ) (ctx : RequestCtx) (a : α) : (s, f s ctx a).1 = s := rfl

/-! ## Multi-Core Interleaved Linearizability Model & Unified `ProgSpec` Algebra -/

inductive ThreadProg (σ α : Type) : Type where
  | pure   : α → ThreadProg σ α
  | io     : (eff : ServerEffect) → (eff.Resp → ThreadProg σ α) → ThreadProg σ α
  | atomic : (σ → σ) → (σ → ThreadProg σ α) → ThreadProg σ α

namespace ThreadProg
def bind {σ α β : Type} : ThreadProg σ α → (α → ThreadProg σ β) → ThreadProg σ β
  | .pure a, k => k a | .io eff f, k => .io eff (fun r => bind (f r) k) | .atomic st next, k => .atomic st (fun s => bind (next s) k)
instance {σ : Type} : Monad (ThreadProg σ) where pure := .pure; bind := ThreadProg.bind
instance {σ : Type} : MonadServer (ThreadProg σ) := ⟨fun eff => .io eff .pure⟩
instance {σ : Type} : MonadAtomic σ (ThreadProg σ) where
  runAtomic f := .atomic (fun s => (f s).1) (fun s => .pure (f s).2)
  runAtomicRead f := .atomic id (fun s => .pure (f s))
end ThreadProg

section ThreadProgSpecs
variable {σ α β γ : Type} {Inv Inv₁ Inv₂ : σ → Prop} {A A₁ A₂ : Prop} {Step Rel S₁ S₂ : σ → σ → Prop} {Q : α → Prop} {Post : β → Prop}

@[simp] theorem threadProg_pure_bind  (a : α) (k : α → ThreadProg σ β) : ((Pure.pure a : ThreadProg σ α) >>= k) = k a := rfl
@[simp] theorem threadProg_pure_bind' (a : α) (k : α → ThreadProg σ β) : (ThreadProg.pure a >>= k) = k a := rfl
@[simp] theorem threadProg_bind_assoc (p : ThreadProg σ α) (f : α → ThreadProg σ β) (g : β → ThreadProg σ γ) :
    ((p >>= f) >>= g) = (p >>= fun x => f x >>= g) := by
  change ThreadProg.bind (ThreadProg.bind p f) g = ThreadProg.bind p (fun x => ThreadProg.bind (f x) g)
  induction p with | pure _ => rfl | io _ _ ih | atomic _ _ ih => exact congrArg _ (funext ih)

inductive ProgSpec {σ α : Type} (Inv : σ → Prop) (AllowAtomic : Prop) (Step : σ → σ → Prop) (Post : α → Prop) : ThreadProg σ α → Prop where
  | pure (a : α) : Post a → ProgSpec Inv AllowAtomic Step Post (.pure a)
  | io (eff : ServerEffect) (k : eff.Resp → ThreadProg σ α) : (∀ r, ProgSpec Inv AllowAtomic Step Post (k r)) → ProgSpec Inv AllowAtomic Step Post (.io eff k)
  | atomic (st : σ → σ) (next : σ → ThreadProg σ α) :
      AllowAtomic → (∀ s, Inv s → Step s (st s)) → (∀ s, Inv s → ProgSpec Inv AllowAtomic Step Post (next s)) → ProgSpec Inv AllowAtomic Step Post (.atomic st next)

theorem ProgSpec.bind {p : ThreadProg σ α} {k : α → ThreadProg σ β}
    (hp : ProgSpec Inv A Step Q p) (hk : ∀ a, Q a → ProgSpec Inv A Step Post (k a)) : ProgSpec Inv A Step Post (p >>= k) := by
  change ProgSpec Inv A Step Post (ThreadProg.bind p k)
  induction hp with | pure a ha => exact hk a ha | io _ _ _ ih => exact .io _ _ ih | atomic st _ ha hst _ ih => exact .atomic st _ ha hst ih

theorem ProgSpec.mono {P₁ P₂ : α → Prop} {p : ThreadProg σ α} (hp : ProgSpec Inv₁ A₁ S₁ P₁ p)
    (hA : A₁ → A₂) (hInv : ∀ s, Inv₂ s → Inv₁ s) (hS : A₁ → ∀ s s', Inv₂ s → S₁ s s' → S₂ s s') (hP : ∀ a, P₁ a → P₂ a) :
    ProgSpec Inv₂ A₂ S₂ P₂ p := by
  induction hp with
  | pure a ha => exact .pure a (hP a ha) | io _ _ _ ih => exact .io _ _ ih
  | atomic st _ ha hst _ ih => exact .atomic st _ (hA ha) (fun s hs => hS ha s _ hs (hst s (hInv s hs))) (fun s hs => ih s (hInv s hs))

theorem ProgSpec.pure_class (a : α) (ha : Q a) : ProgSpec Inv A Step Q (Pure.pure a) := .pure a ha
theorem ProgSpec.runAtomic (step : σ → σ × α) (hstep : ∀ s, Inv s → Step s (step s).1) (hpost : ∀ s, Inv s → Q (step s).2) : ProgSpec Inv True Step Q (MonadAtomic.runAtomic (m := ThreadProg σ) step) := .atomic _ _ trivial hstep (fun s hs => .pure _ (hpost s hs))
theorem ProgSpec.runAtomicRead (f : σ → α) (hrefl : ∀ s, Inv s → Step s s) (hpost : ∀ s, Inv s → Q (f s)) : ProgSpec Inv True Step Q (MonadAtomic.runAtomicRead (m := ThreadProg σ) f) := .atomic id _ trivial hrefl (fun s hs => .pure _ (hpost s hs))
theorem ProgSpec.runAtomic_bind (step : σ → σ × α) {k : α → ThreadProg σ β} (hk : ∀ s, Inv s → ProgSpec Inv True Step Post (k (step s).2)) (hstep : ∀ s, Inv s → Step s (step s).1) : ProgSpec Inv True Step Post (MonadAtomic.runAtomic (m := ThreadProg σ) step >>= k) := .atomic (fun s => (step s).1) (fun s => k (step s).2) trivial hstep hk
theorem ProgSpec.runAtomicRead_bind (f : σ → α) {k : α → ThreadProg σ β} (hk : ∀ s, Inv s → ProgSpec Inv True Step Post (k (f s))) (hrefl : ∀ s, Inv s → Step s s) : ProgSpec Inv True Step Post (MonadAtomic.runAtomicRead (m := ThreadProg σ) f >>= k) := .atomic id (fun s => k (f s)) trivial hrefl hk
theorem ProgSpec.runAtomic_bind_val (step : σ → σ × α) {k : α → ThreadProg σ β} (hk : ∀ a, ProgSpec Inv True Step Post (k a)) (hstep : ∀ s, Inv s → Step s (step s).1) : ProgSpec Inv True Step Post (MonadAtomic.runAtomic (m := ThreadProg σ) step >>= k) := ProgSpec.runAtomic_bind step (fun s _ => hk (step s).2) hstep
theorem ProgSpec.runAtomicRead_bind_val (f : σ → α) {k : α → ThreadProg σ β} (hk : ∀ a, ProgSpec Inv True Step Post (k a)) (hrefl : ∀ s, Inv s → Step s s) : ProgSpec Inv True Step Post (MonadAtomic.runAtomicRead (m := ThreadProg σ) f >>= k) := ProgSpec.runAtomicRead_bind f (fun s _ => hk (f s)) hrefl

abbrev ProgPreservesStepRel (Inv : σ → Prop) (Rel : σ → σ → Prop) (p : ThreadProg σ α) : Prop := ProgSpec Inv True Rel (fun _ => True) p
abbrev ProgPreservesInv (Inv : σ → Prop) (p : ThreadProg σ α) : Prop := ProgPreservesStepRel Inv (fun _ s' => Inv s') p
abbrev ProgEnsures (Inv : σ → Prop) (Post : α → Prop) (p : ThreadProg σ α) : Prop := ProgSpec Inv True (fun _ _ => True) Post p
abbrev NoAtomic (p : ThreadProg σ α) : Prop := ProgSpec (fun _ : σ => True) False (fun _ _ => True) (fun _ => True) p
theorem NoAtomic.pure (a : α) : NoAtomic (σ := σ) (.pure a) := ProgSpec.pure a trivial
theorem NoAtomic.io (eff : ServerEffect) (k : eff.Resp → ThreadProg σ α) (hk : ∀ r, NoAtomic (k r)) : NoAtomic (.io eff k) := ProgSpec.io eff k hk
theorem ProgSpec.of_noAtomic {p : ThreadProg σ α} (h : NoAtomic p) : ProgSpec Inv A Step (fun _ => True) p := h.mono False.elim (fun _ _ => trivial) (fun h => h.elim) (fun _ _ => trivial)
theorem progPreservesStepRel_of_const (p : ThreadProg σ α) (h : ∀ s s', Rel s s') : ProgPreservesStepRel Inv Rel p := by
  induction p with | pure a => exact .pure a trivial | io _ _ ih => exact .io _ _ ih | atomic _ _ ih => exact .atomic _ _ trivial (fun s _ => h s _) (fun s _ => ih s)

@[reducible] def ServerEffect.isHttp : ServerEffect → Bool
  | .httpCall _ => true | _ => false

@[reducible] def ServerEffect.isDecrypt : ServerEffect → Bool
  | .aeadDecrypt _ _ _ _ => true | _ => false

@[reducible] def ServerEffect.isCrypto : ServerEffect → Bool
  | .hmacSha256 _ _ | .sha256 _ | .constEq _ _ | .aeadEncrypt _ _ _ _ | .aeadDecrypt _ _ _ _ => true | _ => false

@[reducible] def ServerEffect.isDbWrite : ServerEffect → Bool
  | .dbExec _ q | .dbTxExec _ _ q => q.isWrite
  | .dbExecDdl _ => true
  | _ => false

inductive ProgEffSpec {σ α : Type} (Inv : σ → Prop) (AllowAtomic : Prop) (Step : σ → σ → Prop)
    (EffOk : ServerEffect → Prop) (Post : α → Prop) : ThreadProg σ α → Prop where
  | pure (a : α) : Post a → ProgEffSpec Inv AllowAtomic Step EffOk Post (.pure a)
  | io (eff : ServerEffect) (k : eff.Resp → ThreadProg σ α) :
      EffOk eff → (∀ r, ProgEffSpec Inv AllowAtomic Step EffOk Post (k r)) →
      ProgEffSpec Inv AllowAtomic Step EffOk Post (.io eff k)
  | atomic (st : σ → σ) (next : σ → ThreadProg σ α) :
      AllowAtomic → (∀ s, Inv s → Step s (st s)) →
      (∀ s, Inv s → ProgEffSpec Inv AllowAtomic Step EffOk Post (next s)) →
      ProgEffSpec Inv AllowAtomic Step EffOk Post (.atomic st next)

theorem ProgEffSpec.bind {EffOk : ServerEffect → Prop} {p : ThreadProg σ α} {k : α → ThreadProg σ β}
    (hp : ProgEffSpec Inv A Step EffOk Q p) (hk : ∀ a, Q a → ProgEffSpec Inv A Step EffOk Post (k a)) :
    ProgEffSpec Inv A Step EffOk Post (p >>= k) := by
  change ProgEffSpec Inv A Step EffOk Post (ThreadProg.bind p k)
  induction hp with
  | pure a ha => exact hk a ha
  | io eff _ heff _ ih => exact .io eff _ heff ih
  | atomic st _ ha hst _ ih => exact .atomic st _ ha hst ih

theorem ProgEffSpec.mono {Eff₁ Eff₂ : ServerEffect → Prop} {P₁ P₂ : α → Prop} {p : ThreadProg σ α}
    (hp : ProgEffSpec Inv₁ A₁ S₁ Eff₁ P₁ p)
    (hA : A₁ → A₂) (hInv : ∀ s, Inv₂ s → Inv₁ s) (hS : A₁ → ∀ s s', Inv₂ s → S₁ s s' → S₂ s s')
    (hEff : ∀ e, Eff₁ e → Eff₂ e) (hP : ∀ a, P₁ a → P₂ a) :
    ProgEffSpec Inv₂ A₂ S₂ Eff₂ P₂ p := by
  induction hp with
  | pure a ha => exact .pure a (hP a ha)
  | io eff _ heff _ ih => exact .io eff _ (hEff eff heff) ih
  | atomic st _ ha hst _ ih => exact .atomic st _ (hA ha) (fun s hs => hS ha s _ hs (hst s (hInv s hs))) (fun s hs => ih s (hInv s hs))

theorem ProgEffSpec.pure_class {EffOk : ServerEffect → Prop} (a : α) (ha : Q a) :
    ProgEffSpec Inv A Step EffOk Q (Pure.pure a) := .pure a ha
theorem ProgEffSpec.exec {EffOk : ServerEffect → Prop} (eff : ServerEffect) {R : eff.Resp → Prop} (heff : EffOk eff)
    (hpost : ∀ r, R r) : ProgEffSpec Inv A Step EffOk R (MonadServer.exec (m := ThreadProg σ) eff) :=
  .io eff _ heff fun r => .pure r (hpost r)
theorem ProgEffSpec.exec_bind {EffOk : ServerEffect → Prop} (eff : ServerEffect) {k : eff.Resp → ThreadProg σ β}
    (heff : EffOk eff) (hk : ∀ r, ProgEffSpec Inv A Step EffOk Post (k r)) :
    ProgEffSpec Inv A Step EffOk Post (MonadServer.exec (m := ThreadProg σ) eff >>= k) :=
  .io eff k heff hk
theorem ProgEffSpec.runAtomic {EffOk : ServerEffect → Prop} (step : σ → σ × α)
    (hstep : ∀ s, Inv s → Step s (step s).1) (hpost : ∀ s, Inv s → Q (step s).2) :
    ProgEffSpec Inv True Step EffOk Q (MonadAtomic.runAtomic (m := ThreadProg σ) step) :=
  .atomic _ _ trivial hstep (fun s hs => .pure _ (hpost s hs))
theorem ProgEffSpec.runAtomicRead {EffOk : ServerEffect → Prop} (f : σ → α)
    (hrefl : ∀ s, Inv s → Step s s) (hpost : ∀ s, Inv s → Q (f s)) :
    ProgEffSpec Inv True Step EffOk Q (MonadAtomic.runAtomicRead (m := ThreadProg σ) f) :=
  .atomic id _ trivial hrefl (fun s hs => .pure _ (hpost s hs))
theorem ProgEffSpec.runAtomic_bind {EffOk : ServerEffect → Prop} (step : σ → σ × α) {k : α → ThreadProg σ β}
    (hk : ∀ s, Inv s → ProgEffSpec Inv True Step EffOk Post (k (step s).2)) (hstep : ∀ s, Inv s → Step s (step s).1) :
    ProgEffSpec Inv True Step EffOk Post (MonadAtomic.runAtomic (m := ThreadProg σ) step >>= k) :=
  .atomic (fun s => (step s).1) (fun s => k (step s).2) trivial hstep hk
theorem ProgEffSpec.runAtomicRead_bind {EffOk : ServerEffect → Prop} (f : σ → α) {k : α → ThreadProg σ β}
    (hk : ∀ s, Inv s → ProgEffSpec Inv True Step EffOk Post (k (f s))) (hrefl : ∀ s, Inv s → Step s s) :
    ProgEffSpec Inv True Step EffOk Post (MonadAtomic.runAtomicRead (m := ThreadProg σ) f >>= k) :=
  .atomic id (fun s => k (f s)) trivial hrefl hk

abbrev ProgAllowsEff (EffOk : ServerEffect → Prop) (p : ThreadProg σ α) : Prop :=
  ProgEffSpec (fun _ => True) True (fun _ _ => True) EffOk (fun _ => True) p
abbrev ProgEnsuresEff (Inv : σ → Prop) (EffOk : ServerEffect → Prop) (Post : α → Prop) (p : ThreadProg σ α) : Prop :=
  ProgEffSpec Inv True (fun _ _ => True) EffOk Post p
abbrev ProgNoHttp (p : ThreadProg σ α) : Prop := ProgAllowsEff (fun e => e.isHttp = false) p
abbrev ProgNoDecrypt (p : ThreadProg σ α) : Prop := ProgAllowsEff (fun e => e.isDecrypt = false) p
abbrev ProgNoCrypto (p : ThreadProg σ α) : Prop := ProgAllowsEff (fun e => e.isCrypto = false) p
abbrev ProgNoDbWrite (p : ThreadProg σ α) : Prop := ProgAllowsEff (fun e => e.isDbWrite = false) p

class SafeIO {σ α : Type} (p : ThreadProg σ α) : Prop where noAtomic : NoAtomic p
instance (a : α) : SafeIO (Pure.pure (f := ThreadProg σ) a) := ⟨.pure a⟩
instance (a : α) : SafeIO (ThreadProg.pure (σ := σ) a) := ⟨.pure a⟩
instance (eff : ServerEffect) : @SafeIO σ (no_index eff.Resp) (MonadServer.exec (m := ThreadProg σ) eff) := ⟨.io eff _ .pure⟩
theorem noAtomic_bind {p : ThreadProg σ α} {k : α → ThreadProg σ β} (hp : NoAtomic p) (hk : ∀ a, NoAtomic (k a)) : NoAtomic (p >>= k) := hp.bind fun a _ => hk a
instance (p : ThreadProg σ α) (k : α → ThreadProg σ β) [hp : SafeIO p] [hk : ∀ a, SafeIO (k a)] : SafeIO (p >>= k) := ⟨noAtomic_bind hp.noAtomic fun a => (hk a).noAtomic⟩
theorem noAtomic_flushWsEmits : ∀ es : List WsEmit, NoAtomic (flushWsEmits (m := ThreadProg σ) es)
  | [] => .pure () | e :: es => noAtomic_bind (.io (.wsBroadcast e.topic e.payload) _ .pure) fun _ => noAtomic_flushWsEmits es
instance (es : List WsEmit) : SafeIO (flushWsEmits (m := ThreadProg σ) es) := ⟨noAtomic_flushWsEmits es⟩

/-! ### Verified Server Helpers (`newId`, `mintBearerToken`, `hashBearerToken`) -/

abbrev BoundedId := Qed.Field (fun s : String => 1 ≤ s.length ∧ s.length ≤ 128)

def newId {m : Type → Type} [Monad m] [MonadServer m] (pfx : String := "") (bytes : UInt32 := 12) :
    m (Except ApiError BoundedId) :=
  MonadServer.randomHex bytes >>= fun rnd =>
    let raw := if pfx.isEmpty then rnd else pfx ++ "_" ++ rnd
    Pure.pure (if h : 1 ≤ raw.length ∧ raw.length ≤ 128 then .ok ⟨raw, h⟩ else .error (ApiError.internal "generated identifier length out of bounds (1..128)"))

theorem noAtomic_newId (pfx : String) (bytes : UInt32) : NoAtomic (newId (m := ThreadProg σ) pfx bytes) :=
  noAtomic_bind (.io (.randomHex bytes) _ .pure) fun _ => .pure _
instance (pfx : String) (bytes : UInt32) : SafeIO (newId (m := ThreadProg σ) pfx bytes) := ⟨noAtomic_newId pfx bytes⟩

def mintBearerToken {m : Type → Type} [Monad m] [MonadServer m] (userId : String) (ttlSec : Nat := 86400 * 30)
    (secretEnv : String := "QED_AUTH_SECRET") : m (Except ApiError String) :=
  if userId.isEmpty || userId.contains '\x00' then Pure.pure (.error (ApiError.badRequest "invalid user id for bearer token"))
  else MonadServer.readEnv secretEnv >>= fun sec? =>
    match sec? with
    | none => Pure.pure (.error (ApiError.internal s!"missing required secret `{secretEnv}`"))
    | some sec =>
        if sec.isEmpty then Pure.pure (.error (ApiError.internal s!"secret `{secretEnv}` is empty"))
        else MonadServer.nowMs >>= fun now =>
          MonadServer.randomHex 16 >>= fun jti =>
            let payload := "v3." ++ toString (now.toNat / 1000 + ttlSec) ++ "." ++ jti ++ "." ++ userId
            MonadServer.hmacSha256 sec.toUTF8 payload.toUTF8 >>= fun sig =>
              Pure.pure (.ok (payload ++ "." ++ Proto.encodeHex sig))

theorem noAtomic_mintBearerToken (userId : String) (ttlSec : Nat) (secretEnv : String) :
    NoAtomic (mintBearerToken (m := ThreadProg σ) userId ttlSec secretEnv) := by
  unfold mintBearerToken; split
  · exact .pure _
  · refine noAtomic_bind (.io (.readEnv secretEnv) _ .pure) fun r => ?_
    cases r with
    | none => exact .pure _
    | some sec =>
        by_cases h : sec.isEmpty
        · simp only [h, ↓reduceIte]; exact .pure _
        · simp only [h, Bool.false_eq_true, ↓reduceIte]
          exact noAtomic_bind (.io .nowMs _ .pure) fun _ =>
            noAtomic_bind (.io (.randomHex 16) _ .pure) fun _ =>
              noAtomic_bind (.io (.hmacSha256 _ _) _ .pure) fun _ => .pure _
instance (userId : String) (ttlSec : Nat) (secretEnv : String) : SafeIO (mintBearerToken (m := ThreadProg σ) userId ttlSec secretEnv) :=
  ⟨noAtomic_mintBearerToken userId ttlSec secretEnv⟩

def hashBearerToken {m : Type → Type} [Monad m] [MonadServer m] (token : String) : m (Except ApiError String) :=
  MonadServer.hmacSha256 "qed-token-fingerprint-v1".toUTF8 token.toUTF8 >>= fun mac =>
    Pure.pure (.ok (Proto.encodeHex mac))

theorem noAtomic_hashBearerToken (token : String) : NoAtomic (hashBearerToken (m := ThreadProg σ) token) :=
  noAtomic_bind (.io (.hmacSha256 _ _) _ .pure) fun _ => .pure _
instance (token : String) : SafeIO (hashBearerToken (m := ThreadProg σ) token) := ⟨noAtomic_hashBearerToken token⟩

theorem ProgSpec.safeIO_bind (p : ThreadProg σ α) [hp : SafeIO p] {k : α → ThreadProg σ β} (hk : ∀ a, ProgSpec Inv A Step Post (k a)) :
    ProgSpec Inv A Step Post (p >>= k) := (ProgSpec.of_noAtomic hp.noAtomic).bind fun a _ => hk a
theorem ProgSpec.of_safeIO (p : ThreadProg σ α) [hp : SafeIO p] : ProgSpec Inv A Step (fun _ => True) p :=
  ProgSpec.of_noAtomic hp.noAtomic
theorem safeIO_preservesStepRel (p : ThreadProg σ α) [hp : SafeIO p] : ProgPreservesStepRel Inv Rel p := ProgSpec.of_noAtomic hp.noAtomic
theorem safeIO_bind_preservesStepRel (p : ThreadProg σ α) [SafeIO p] {k : α → ThreadProg σ β} (hk : ∀ a, ProgPreservesStepRel Inv Rel (k a)) :
    ProgPreservesStepRel Inv Rel (p >>= k) := ProgSpec.safeIO_bind p hk

class SafeIOEnsures {σ α : Type} (p : ThreadProg σ α) (Q : outParam (α → Prop)) : Prop where
  noAtomic : NoAtomic p
  ensures  : ∀ {Inv : σ → Prop}, ProgEnsures Inv Q p
instance (priority := low) {p : ThreadProg σ α} [h : SafeIOEnsures p Q] : SafeIO p := ⟨h.noAtomic⟩
theorem safeIOEnsures_bind (p : ThreadProg σ α) [h : SafeIOEnsures p Q] {k : α → ThreadProg σ β} (hk : ∀ a, Q a → ProgEnsures Inv Post (k a)) :
    ProgEnsures Inv Post (p >>= k) := h.ensures.bind hk
theorem safeIOEnsures_final {Post : α → Prop} (p : ThreadProg σ α) [h : SafeIOEnsures p Q] (himp : ∀ a, Q a → Post a) :
    ProgEnsures Inv Post p := h.ensures.mono id (fun _ h => h) (fun _ _ _ _ h => h) himp
end ThreadProgSpecs

/-! ## Multi-Core Schedule & Linearizability Proofs -/

section MultiCore
variable {σ Tgt Out : Type} {Inv : σ → Prop}

structure MultiCoreState (σ Out : Type) where
  shared  : σ
  threads : List (ThreadProg σ Out)

inductive MultiCoreStep {σ Out : Type} (Inv : σ → Prop) : MultiCoreState σ Out → MultiCoreState σ Out → Prop where
  | spawn (s : σ) (ts : List (ThreadProg σ Out)) (p : ThreadProg σ Out) : ProgPreservesInv Inv p → MultiCoreStep Inv ⟨s, ts⟩ ⟨s, p :: ts⟩
  | reap (s : σ) (pre post : List (ThreadProg σ Out)) (out : Out) : MultiCoreStep Inv ⟨s, pre ++ .pure out :: post⟩ ⟨s, pre ++ post⟩
  | stepIo (s : σ) (pre post : List (ThreadProg σ Out)) (eff : ServerEffect) (k : eff.Resp → ThreadProg σ Out) (resp : eff.Resp) :
      MultiCoreStep Inv ⟨s, pre ++ .io eff k :: post⟩ ⟨s, pre ++ k resp :: post⟩
  | stepAtomic (s : σ) (pre post : List (ThreadProg σ Out)) (st : σ → σ) (next : σ → ThreadProg σ Out) :
      MultiCoreStep Inv ⟨s, pre ++ .atomic st next :: post⟩ ⟨st s, pre ++ next s :: post⟩

inductive Schedule {S : Type} (Step : S → S → Prop) : S → S → Prop where
  | refl (st : S) : Schedule Step st st
  | step {st₁ st₂ st₃ : S} : Schedule Step st₁ st₂ → Step st₂ st₃ → Schedule Step st₁ st₃
theorem Schedule.preserves {S : Type} {Step : S → S → Prop} {P : S → Prop} {st₁ st₂ : S}
    (h : Schedule Step st₁ st₂) (hinit : P st₁) (hstep : ∀ {a b}, Step a b → P a → P b) : P st₂ := by
  induction h with | refl => exact hinit | step _ hs ih => exact hstep hs ih
abbrev MultiCoreSchedule {σ Out : Type} (Inv : σ → Prop) := Schedule (@MultiCoreStep σ Out Inv)

private theorem pool_replace_mid {α : Type} {P : α → Prop} {pre post : List α} {x y : α}
    (hpool : ∀ q ∈ pre ++ x :: post, P q) (hy : P y) : ∀ q ∈ pre ++ y :: post, P q := fun q hq =>
  (List.mem_append.1 hq).elim (fun h => hpool q (List.mem_append_left _ h)) fun h =>
    (List.mem_cons.1 h).elim (· ▸ hy) fun h2 => hpool q (List.mem_append_right _ (List.mem_cons_of_mem _ h2))

private theorem step_preserves_inv_and_pool {st₁ st₂ : MultiCoreState σ Out}
    (hstep : MultiCoreStep Inv st₁ st₂) (hinv : Inv st₁.shared) (hpool : ∀ p ∈ st₁.threads, ProgPreservesInv Inv p) :
    Inv st₂.shared ∧ (∀ p ∈ st₂.threads, ProgPreservesInv Inv p) := by
  have mid {x : ThreadProg σ Out} {pre post} (hp : ∀ p ∈ pre ++ x :: post, ProgPreservesInv Inv p) : ProgPreservesInv Inv x :=
    hp x (List.mem_append_right _ (List.mem_cons_self ..))
  cases hstep with
  | spawn _ _ _ hp => exact ⟨hinv, fun q hq => (List.mem_cons.1 hq).elim (· ▸ hp) (hpool q)⟩
  | reap _ _ _ _ => exact ⟨hinv, fun q hq => (List.mem_append.1 hq).elim
      (fun h => hpool q (List.mem_append_left _ h)) (fun h => hpool q (List.mem_append_right _ (List.mem_cons_of_mem _ h)))⟩
  | stepIo _ _ _ _ _ resp => cases mid hpool with | io _ _ hk => exact ⟨hinv, pool_replace_mid hpool (hk resp)⟩
  | stepAtomic s _ _ _ _ => cases mid hpool with | atomic _ _ _ hst hnext => exact ⟨hst s hinv, pool_replace_mid hpool (hnext s hinv)⟩

theorem concurrent_schedule_preserves_inv (Inv : σ → Prop) (s₀ : σ) (st : MultiCoreState σ Out)
    (hinit : Inv s₀) (hsched : MultiCoreSchedule Inv ⟨s₀, []⟩ st) : Inv st.shared :=
  (hsched.preserves (P := fun s => Inv s.shared ∧ ∀ p ∈ s.threads, ProgPreservesInv Inv p)
    ⟨hinit, fun _ hm => nomatch hm⟩ (fun hstep ih => step_preserves_inv_and_pool hstep ih.1 ih.2)).1

structure TrackedMultiCoreState (σ Tgt Out : Type) where
  shared : σ
  target : ThreadProg σ Tgt
  others : List (ThreadProg σ Out)

inductive TrackedMultiCoreStep {σ Tgt Out : Type} (Inv : σ → Prop) :
    TrackedMultiCoreState σ Tgt Out → TrackedMultiCoreState σ Tgt Out → Prop where
  | stepOther {s₁ s₂ : σ} {os₁ os₂ : List (ThreadProg σ Out)} (t : ThreadProg σ Tgt) : MultiCoreStep Inv ⟨s₁, os₁⟩ ⟨s₂, os₂⟩ → TrackedMultiCoreStep Inv ⟨s₁, t, os₁⟩ ⟨s₂, t, os₂⟩
  | stepTargetIo (s : σ) (os : List (ThreadProg σ Out)) (eff : ServerEffect) (k : eff.Resp → ThreadProg σ Tgt) (resp : eff.Resp) : TrackedMultiCoreStep Inv ⟨s, .io eff k, os⟩ ⟨s, k resp, os⟩
  | stepTargetAtomic (s : σ) (os : List (ThreadProg σ Out)) (st : σ → σ) (next : σ → ThreadProg σ Tgt) : TrackedMultiCoreStep Inv ⟨s, .atomic st next, os⟩ ⟨st s, next s, os⟩
abbrev TrackedMultiCoreSchedule {σ Tgt Out : Type} (Inv : σ → Prop) := Schedule (@TrackedMultiCoreStep σ Tgt Out Inv)

theorem concurrent_schedule_ensures (Inv : σ → Prop) (Post : Tgt → Prop)
    (s₀ : σ) (tgt₀ : ThreadProg σ Tgt) (st : TrackedMultiCoreState σ Tgt Out)
    (hinit : Inv s₀) (htinv : ProgPreservesInv Inv tgt₀) (htens : ProgEnsures Inv Post tgt₀)
    (hsched : TrackedMultiCoreSchedule Inv ⟨s₀, tgt₀, []⟩ st) : Inv st.shared ∧ ∀ out, st.target = .pure out → Post out := by
  have h := hsched.preserves
    (P := fun s => Inv s.shared ∧ ProgPreservesInv Inv s.target ∧ ProgEnsures Inv Post s.target ∧ ∀ p ∈ s.others, ProgPreservesInv Inv p)
    ⟨hinit, htinv, htens, fun _ hm => nomatch hm⟩ fun hstep ⟨hinv, ht1, ht2, hop⟩ => by
      cases hstep with
      | stepOther _ hs => let ⟨hi', ho'⟩ := step_preserves_inv_and_pool hs hinv hop; exact ⟨hi', ht1, ht2, ho'⟩
      | stepTargetIo _ _ _ _ resp => cases ht1 with | io _ _ hk1 => cases ht2 with | io _ _ hk2 => exact ⟨hinv, hk1 resp, hk2 resp, hop⟩
      | stepTargetAtomic s _ _ _ => cases ht1 with | atomic _ _ _ hst hn1 => cases ht2 with | atomic _ _ _ _ hn2 => exact ⟨hst s hinv, hn1 s hinv, hn2 s hinv, hop⟩
  exact ⟨h.1, fun out hout => by cases hout ▸ h.2.2.1 with | pure _ hp => exact hp⟩
end MultiCore

/-! ## Verified Scheduled / Background Server Jobs -/

inductive DurationUnit where | ms | s | m | h deriving Inhabited, DecidableEq, Repr
def durationToMs (n : Nat) : DurationUnit → Nat | .ms => n | .s => n * 1000 | .m => n * 60000 | .h => n * 3600000

structure JobMeta where
  name        : String
  intervalMs  : Nat
  intervalPos : 0 < intervalMs
structure ServerJob (σ : Type) extends JobMeta where
  runM      : {m : Type → Type} → [Monad m] → [MonadServer m] → [MonadAtomic σ m] → m (Except ApiError Unit)
  runWorkM? : Option ({m : Type → Type} → [Monad m] → [MonadServer m] → [MonadAtomic σ m] → m (Except ApiError Bool)) := none
structure VerifiedJob (σ : Type) (Inv : σ → Prop) extends ServerJob σ where
  preserves : ProgPreservesInv Inv (runM (m := ThreadProg σ))
structure StatelessJob extends JobMeta where
  runM      : {m : Type → Type} → [Monad m] → [MonadServer m] → m (Except ApiError Unit)
  runWorkM? : Option ({m : Type → Type} → [Monad m] → [MonadServer m] → m (Except ApiError Bool)) := none
structure IoJob extends JobMeta where
  runOnce     : IO (Except ApiError Unit)
  runWorkOnce : IO (Except ApiError Bool) := runOnce.map fun | .ok () => .ok false | .error e => .error e

def StatelessJob.toUnitJob (j : StatelessJob) : ServerJob Unit :=
  { j.toJobMeta with
    runM := fun {m} [Monad m] [MonadServer m] [MonadAtomic Unit m] => @j.runM m _ _
    runWorkM? := j.runWorkM?.map fun rw => fun {m} [Monad m] [MonadServer m] [MonadAtomic Unit m] => @rw m _ _ }
def ServerJob.toIoJob {σ : Type} (srvInst : MonadServer IO) (atomicInst : MonadAtomic σ IO) (j : ServerJob σ) : IoJob :=
  { j.toJobMeta with
    runOnce := @j.runM IO _ srvInst atomicInst
    runWorkOnce := match j.runWorkM? with
      | some rw => @rw IO _ srvInst atomicInst
      | none => (@j.runM IO _ srvInst atomicInst).map fun | .ok () => .ok false | .error e => .error e }
def StatelessJob.toIoJob (srvInst : MonadServer IO) (j : StatelessJob) : IoJob :=
  { j.toJobMeta with
    runOnce := @j.runM IO _ srvInst
    runWorkOnce := match j.runWorkM? with
      | some rw => @rw IO _ srvInst
      | none => (@j.runM IO _ srvInst).map fun | .ok () => .ok false | .error e => .error e }
theorem verifiedJob_spawn_step {σ : Type} {Inv : σ → Prop} (j : VerifiedJob σ Inv) (s : σ) (ts : List (ThreadProg σ (Except ApiError Unit))) :
    MultiCoreStep Inv ⟨s, ts⟩ ⟨s, j.runM (m := ThreadProg σ) :: ts⟩ := .spawn s ts (j.runM (m := ThreadProg σ)) j.preserves

def defaultMaxJobTicks : Nat := 1000000000000
def runWorkJobLoop (name : String) (intervalMs : UInt32) (runWorkOnce : IO (Except ApiError Bool))
    (stopFlag? : Option (IO.Ref Bool) := none) (sleepFirst : Bool := true) : Nat → IO Unit
  | 0 => pure ()
  | fuel + 1 => do
      let stopped : IO Bool := match stopFlag? with | some f => f.get | none => pure false
      if ← stopped then return ()
      if sleepFirst then
        IO.sleep intervalMs
        if ← stopped then return ()
      match ← runWorkOnce with
      | .ok true => runWorkJobLoop name intervalMs runWorkOnce stopFlag? false fuel
      | .ok false => runWorkJobLoop name intervalMs runWorkOnce stopFlag? true fuel
      | .error e =>
          IO.eprintln s!"[qed job `{name}`] error: {e.message}"
          runWorkJobLoop name intervalMs runWorkOnce stopFlag? true fuel
def runJobLoop (name : String) (intervalMs : UInt32) (runOnce : IO (Except ApiError Unit)) (stopFlag? : Option (IO.Ref Bool) := none) (fuel : Nat) : IO Unit :=
  runWorkJobLoop name intervalMs (runOnce.map fun | .ok () => .ok false | .error e => .error e) stopFlag? true fuel
def spawnServerJobs (jobs : Array IoJob) (stopFlag? : Option (IO.Ref Bool) := none) (maxTicks : Nat := defaultMaxJobTicks) :
    IO (Array (Task (Except IO.Error Unit))) :=
  jobs.mapM fun job => IO.asTask (prio := .dedicated) (runWorkJobLoop job.name (min job.intervalMs 2147483647).toUInt32 job.runWorkOnce stopFlag? true maxTicks)
abbrev runServerJobs := @spawnServerJobs

private def drainOneJobOnce (name : String) (runWorkOnce : IO (Except ApiError Bool)) : Nat → IO Bool
  | 0 => pure true
  | fuel + 1 => do
      match ← runWorkOnce with
      | .ok true => drainOneJobOnce name runWorkOnce fuel
      | .ok false => pure true
      | .error e => IO.eprintln s!"[qed job `{name}`] error: {e.message}"; pure false

/-- Runs each job once (or until a `-> Bool` job returns `false` / drains its queue). Returns `true` if no job errored. -/
def runJobsOnce (jobs : Array IoJob) (maxIterPerJob : Nat := 10000) : IO Bool := do
  let mut allOk := true
  for job in jobs do
    let ok ← drainOneJobOnce job.name job.runWorkOnce maxIterPerJob
    if !ok then allOk := false
  return allOk

/-! ## Inferred Domain Errors, Control-Flow Combinators & Opaque SSA Stepping (`srvLetEq`) -/

inductive SrvFailure (ε : Type) where
  | api (err : ApiError) | domain (tag : ε) (message : String)
deriving Inhabited, DecidableEq, Repr
def SrvFailure.toWire {ε α : Type} : Except (SrvFailure ε) α → Except ApiError (Except (RpcDomainError ε) α)
  | .ok a => .ok (.ok a) | .error (.domain t msg) => .ok (.error ⟨t, msg⟩) | .error (.api err) => .error err

class SrvIdx (ι : Type) where toNat : ι → Nat
@[inline] instance : SrvIdx Nat := ⟨id⟩
@[inline] instance {n : Nat} : SrvIdx (Fin n) := ⟨Fin.val⟩
@[simp] theorem SrvIdx.toNat_nat (i : Nat) : SrvIdx.toNat i = i := rfl
@[simp] theorem SrvIdx.toNat_fin {n : Nat} (i : Fin n) : SrvIdx.toNat i = i.val := rfl

class SrvLiftOpt (α Inner : Type) where liftOpt : α → Option Inner
@[inline] instance {Inner : Type} : SrvLiftOpt (Option Inner) Inner := ⟨id⟩
@[inline] instance (priority := low) {Inner : Type} : SrvLiftOpt Inner Inner := ⟨Option.some⟩
@[simp] theorem SrvLiftOpt.liftOpt_opt {Inner : Type} (x : Option Inner) : SrvLiftOpt.liftOpt x = x := rfl
@[simp] theorem SrvLiftOpt.liftOpt_val {Inner : Type} (x : Inner) : SrvLiftOpt.liftOpt (Inner := Inner) x = some x := rfl

def mkFail1 (msg : String) : ApiError := ApiError.badRequest msg
def mkFail2 (code : Nat) (msg : String) : ApiError := ⟨code, msg⟩
def mkFailDom {ε : Type} (tag : ε) (msg : String) : SrvFailure ε := .domain tag msg

class SrvErr (E : Type) where ofApi : ApiError → E
@[reducible] instance : SrvErr ApiError := ⟨id⟩
@[reducible] instance {ε : Type} : SrvErr (SrvFailure ε) := ⟨SrvFailure.api⟩

class SrvUnwrap (E W : Type) (Val : outParam Type) where unwrap : W → Except E Val
@[reducible] instance {E α : Type} : SrvUnwrap E (Except E α) α := ⟨id⟩
@[reducible] instance {ε α : Type} : SrvUnwrap (SrvFailure ε) (Except ApiError α) α := ⟨fun | .ok a => .ok a | .error e => .error (.api e)⟩
@[reducible] instance {E α : Type} [SrvErr E] : SrvUnwrap E (Except String α) α := ⟨fun | .ok a => .ok a | .error e => .error (SrvErr.ofApi (ApiError.badRequest e))⟩
@[reducible] instance {E α : Type} [SrvErr E] : SrvUnwrap E (Option α) α := ⟨fun | some a => .ok a | none => .error (SrvErr.ofApi (ApiError.notFound "optional value was empty"))⟩

class SrvUnwrapOpt (W Inner : Type) (Val : outParam Type) where unwrapOpt : W → Except (Except ApiError (Option Inner)) Val
@[reducible] instance {Inner α : Type} : SrvUnwrapOpt (Option α) Inner α := ⟨fun | some a => .ok a | none => .error (.ok none)⟩
@[reducible] instance {Inner α : Type} : SrvUnwrapOpt (Except ApiError α) Inner α := ⟨fun | .ok a => .ok a | .error e => .error (.error e)⟩

class SrvRetAwait (E W : Type) (Val : outParam Type) where liftRet : W → Except E Val
@[reducible] instance {E W Val : Type} [SrvUnwrap E W Val] : SrvRetAwait E W Val := ⟨SrvUnwrap.unwrap⟩
@[reducible] instance (priority := low) {E α : Type} : SrvRetAwait E α α := ⟨Except.ok⟩

@[simp] theorem srvUnwrap_srvFailure_ok_iff {ε α : Type} (x : Except ApiError α) (a : α) : (SrvUnwrap.unwrap (E := SrvFailure ε) x = Except.ok a) = (x = Except.ok a) := propext (by cases x <;> simp [SrvUnwrap.unwrap])
@[simp] theorem srvUnwrap_str_ok_iff {E α : Type} [SrvErr E] (x : Except String α) (a : α) : (SrvUnwrap.unwrap (E := E) x = Except.ok a) = (x = Except.ok a) := propext (by cases x <;> simp [SrvUnwrap.unwrap])
@[simp] theorem srvUnwrap_opt_ok_iff {E α : Type} [SrvErr E] (x : Option α) (a : α) : (SrvUnwrap.unwrap (E := E) x = Except.ok a) = (x = some a) := propext (by cases x <;> simp [SrvUnwrap.unwrap])
@[inline] def srvLetEq {α β : Type} (val : α) (k : (x : α) → x = val → β) : β := k val rfl
theorem srvLetEq_elim {α β : Type} (P : β → Prop) (val : α) (k : (x : α) → x = val → β) (hk : ∀ (x : α) (hx : x = val), P (k x hx)) : P (srvLetEq val k) := hk val rfl

@[inline] def srvSeq {σ ρ : Type} (first : σ × Option ρ) (next : σ → σ × Option ρ) : σ × Option ρ := match first with | (s', none) => next s' | r => r
@[inline] def srvFinish {E σ α : Type} [SrvErr E] (s₀ : σ) (res : σ × Option (Except E α)) : σ × Except E α :=
  match res with
  | (s', some (.ok v)) => (s', .ok v) | (_, some (.error e)) => (s₀, .error e)
  | (_, none) => (s₀, .error (SrvErr.ofApi (ApiError.internal "unreachable missing return")))
@[inline] def srvAtomicCommit {E σ α : Type} (s₀ : σ) (res : σ × Option (Except E α)) : σ × Option (Except E α) :=
  match res with | (_, some (.error e)) => (s₀, some (.error e)) | r => r
@[inline] def srvEmitSeq {σ ρ : Type} (first : σ × List WsEmit × Option ρ) (next : σ → List WsEmit → σ × List WsEmit × Option ρ) :
    σ × List WsEmit × Option ρ := match first with | (s', es, none) => next s' es | r => r
@[inline] def srvFinishEmit {E σ α : Type} [SrvErr E] (s₀ : σ) (res : σ × List WsEmit × Option (Except E α)) : σ × (Except E α × List WsEmit) :=
  match res with
  | (s', es, some (.ok v)) => (s', .ok v, es) | (_, _, some (.error e)) => (s₀, .error e, [])
  | (_, _, none) => (s₀, .error (SrvErr.ofApi (ApiError.internal "unreachable missing return")), [])
@[inline] def srvAtomicCommitEmit {E σ α : Type} (s₀ : σ) (res : σ × List WsEmit × Option (Except E α)) : σ × (Option (Except E α) × List WsEmit) :=
  match res with | (s', es, none) => (s', none, es) | (s', es, some (.ok v)) => (s', some (.ok v), es) | (_, _, some (.error e)) => (s₀, some (.error e), [])

@[inline, specialize] def srvSeqM {m : Type → Type} [Monad m] {ρ : Type} (first : m (Option ρ)) (next : Unit → m (Option ρ)) : m (Option ρ) := do
  match ← first with | some r => return some r | none => next ()
@[inline, specialize] def srvFinishM {E : Type} [SrvErr E] {m : Type → Type} [Monad m] {α : Type} (res : m (Option (Except E α))) : m (Except E α) := do
  match ← res with | some r => return r | none => return .error (SrvErr.ofApi (ApiError.internal "unreachable missing return"))

def srvForEachM {E α β : Type} {m : Type → Type} [Monad m]
    (xs : List α) (body : α → m (Option (Except E β))) : m (Option (Except E β)) :=
  match xs with
  | [] => pure none
  | x :: rest =>
      body x >>= fun
        | some r => pure (some r)
        | none => srvForEachM rest body

@[simp] theorem srvForEachM_nil {E α β : Type} {m : Type → Type} [Monad m]
    (body : α → m (Option (Except E β))) : srvForEachM ([] : List α) body = pure none := rfl

theorem noAtomic_srvForEachM {σ E α β : Type} (body : α → ThreadProg σ (Option (Except E β)))
    (hb : ∀ x, NoAtomic (body x)) : ∀ xs : List α, NoAtomic (srvForEachM xs body)
  | [] => .pure none
  | x :: rest => noAtomic_bind (hb x) fun
      | some r => .pure (some r)
      | none => noAtomic_srvForEachM body hb rest

instance {σ E α β : Type} (xs : List α) (body : α → ThreadProg σ (Option (Except E β)))
    [hb : ∀ x, SafeIO (body x)] : SafeIO (srvForEachM xs body) :=
  ⟨noAtomic_srvForEachM body (fun x => (hb x).noAtomic) xs⟩

theorem progEffSpec_srvForEachM {σ E α β : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {EffOk : ServerEffect → Prop} {Post : Option (Except E β) → Prop}
    (body : α → ThreadProg σ (Option (Except E β)))
    (hNone : Post none)
    (xs : List α) (hb : ∀ x ∈ xs, ProgEffSpec Inv A Step EffOk Post (body x)) :
    ProgEffSpec Inv A Step EffOk Post (srvForEachM xs body) := by
  induction xs with
  | nil => exact .pure none hNone
  | cons x rest ih =>
      exact (hb x (List.mem_cons_self ..)).bind fun
        | some r, hr => .pure (some r) hr
        | none, _ => ih (fun y hy => hb y (List.mem_cons_of_mem x hy))

theorem progEffSpec_srvForEachM_bind {σ E α β γ : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {EffOk : ServerEffect → Prop} {Post : γ → Prop}
    (xs : List α) (body : α → ThreadProg σ (Option (Except E β)))
    {k : Option (Except E β) → ThreadProg σ γ}
    (hNone : ProgEffSpec Inv A Step EffOk Post (k none))
    (hb : ∀ x ∈ xs, ProgEffSpec Inv A Step EffOk
      (fun r => match r with | some v => ProgEffSpec Inv A Step EffOk Post (k (some v)) | none => True) (body x)) :
    ProgEffSpec Inv A Step EffOk Post (srvForEachM xs body >>= k) := by
  induction xs with
  | nil => simpa [srvForEachM, threadProg_pure_bind] using hNone
  | cons x rest ih =>
      change ProgEffSpec Inv A Step EffOk Post ((body x >>= fun | some r => pure (some r) | none => srvForEachM rest body) >>= k)
      rw [threadProg_bind_assoc]
      exact (hb x (List.mem_cons_self ..)).bind fun
        | some v, hv => by simpa [threadProg_pure_bind] using hv
        | none, _ => ih (fun y hy => hb y (List.mem_cons_of_mem x hy))

theorem progSpec_srvForEachM {σ E α β : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {Post : Option (Except E β) → Prop} (body : α → ThreadProg σ (Option (Except E β)))
    (hNone : Post none) (xs : List α) (hb : ∀ x ∈ xs, ProgSpec Inv A Step Post (body x)) :
    ProgSpec Inv A Step Post (srvForEachM xs body) := by
  induction xs with
  | nil => exact .pure none hNone
  | cons x rest ih =>
      exact (hb x (List.mem_cons_self ..)).bind fun
        | some r, hr => .pure (some r) hr
        | none, _ => ih (fun y hy => hb y (List.mem_cons_of_mem x hy))

theorem progSpec_srvForEachM_bind {σ E α β γ : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {Post : γ → Prop} (xs : List α) (body : α → ThreadProg σ (Option (Except E β)))
    {k : Option (Except E β) → ThreadProg σ γ} (hNone : ProgSpec Inv A Step Post (k none))
    (hb : ∀ x ∈ xs, ProgSpec Inv A Step
      (fun r => match r with | some v => ProgSpec Inv A Step Post (k (some v)) | none => True) (body x)) :
    ProgSpec Inv A Step Post (srvForEachM xs body >>= k) := by
  induction xs with
  | nil => simpa [srvForEachM, threadProg_pure_bind] using hNone
  | cons x rest ih =>
      change ProgSpec Inv A Step Post ((body x >>= fun | some r => pure (some r) | none => srvForEachM rest body) >>= k)
      rw [threadProg_bind_assoc]
      exact (hb x (List.mem_cons_self ..)).bind fun
        | some v, hv => by simpa [threadProg_pure_bind] using hv
        | none, _ => ih (fun y hy => hb y (List.mem_cons_of_mem x hy))

def srvForFoldM {σS ρ α : Type} {m : Type → Type} [Monad m]
    (xs : List α) (st : σS) (body : σS → α → m (Qed.QedLoopStep σS ρ)) : m (σS × Option ρ) :=
  match xs with
  | [] => pure (st, none)
  | x :: rest =>
      body st x >>= fun
        | .next st' => srvForFoldM rest st' body
        | .breakLoop st' => pure (st', none)
        | .ret st' r => pure (st', some r)

def srvForRangeAuxM {σS ρ : Type} {m : Type → Type} [Monad m]
    (cur step : Nat) : Nat → σS → (σS → Nat → m (Qed.QedLoopStep σS ρ)) → m (σS × Option ρ)
  | 0, st, _ => pure (st, none)
  | k + 1, st, body =>
      body st cur >>= fun
        | .next st' => srvForRangeAuxM (cur + step) step k st' body
        | .breakLoop st' => pure (st', none)
        | .ret st' r => pure (st', some r)

def srvForRangeM {σS ρ : Type} {m : Type → Type} [Monad m]
    (r : Qed.QedRange) (st : σS) (body : σS → Nat → m (Qed.QedLoopStep σS ρ)) : m (σS × Option ρ) :=
  srvForRangeAuxM r.start r.step r.count st body

theorem srvForRangeAuxM_eq_srvForFoldM {σS ρ : Type} {m : Type → Type} [Monad m]
    (step : Nat) (body : σS → Nat → m (Qed.QedLoopStep σS ρ)) :
    ∀ (k cur : Nat) (st : σS), srvForRangeAuxM cur step k st body = srvForFoldM (Qed.QedRange.toListAux cur step k) st body
  | 0, _, _ => rfl
  | k + 1, cur, st => by
      simp only [srvForRangeAuxM, Qed.QedRange.toListAux, srvForFoldM]
      congr 1; funext res; cases res with
      | next st' => exact srvForRangeAuxM_eq_srvForFoldM step body k (cur + step) st'
      | breakLoop _ | ret _ _ => rfl

theorem srvForRangeM_eq_srvForFoldM {σS ρ : Type} {m : Type → Type} [Monad m]
    (r : Qed.QedRange) (st : σS) (body : σS → Nat → m (Qed.QedLoopStep σS ρ)) :
    srvForRangeM r st body = srvForFoldM r.toList st body :=
  srvForRangeAuxM_eq_srvForFoldM r.step body r.count r.start st

theorem noAtomic_srvForFoldM {σ σS ρ α : Type} (body : σS → α → ThreadProg σ (Qed.QedLoopStep σS ρ))
    (hb : ∀ s x, NoAtomic (body s x)) : ∀ (xs : List α) (st : σS), NoAtomic (srvForFoldM xs st body)
  | [], st => .pure (st, none)
  | x :: rest, st => noAtomic_bind (hb st x) fun
      | .next st' => noAtomic_srvForFoldM body hb rest st'
      | .breakLoop st' => .pure (st', none)
      | .ret st' r => .pure (st', some r)

instance {σ σS ρ α : Type} (xs : List α) (st : σS) (body : σS → α → ThreadProg σ (Qed.QedLoopStep σS ρ))
    [hb : ∀ s x, SafeIO (body s x)] : SafeIO (srvForFoldM xs st body) :=
  ⟨noAtomic_srvForFoldM body (fun s x => (hb s x).noAtomic) xs st⟩

theorem noAtomic_srvForRangeM {σ σS ρ : Type} (r : Qed.QedRange) (st : σS)
    (body : σS → Nat → ThreadProg σ (Qed.QedLoopStep σS ρ))
    (hb : ∀ s i, NoAtomic (body s i)) : NoAtomic (srvForRangeM r st body) := by
  rw [srvForRangeM_eq_srvForFoldM]; exact noAtomic_srvForFoldM body hb r.toList st

instance {σ σS ρ : Type} (r : Qed.QedRange) (st : σS) (body : σS → Nat → ThreadProg σ (Qed.QedLoopStep σS ρ))
    [hb : ∀ s i, SafeIO (body s i)] : SafeIO (srvForRangeM r st body) :=
  ⟨noAtomic_srvForRangeM r st body (fun s i => (hb s i).noAtomic)⟩

theorem progSpec_srvForFoldM {σ σS ρ α : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {Post : σS × Option ρ → Prop} (body : σS → α → ThreadProg σ (Qed.QedLoopStep σS ρ))
    (hDone : ∀ st, Post (st, none)) (xs : List α) (st : σS)
    (hb : ∀ st' x, x ∈ xs → ProgSpec Inv A Step
      (fun r => match r with | .next _ | .breakLoop _ => True | .ret s' v => Post (s', some v)) (body st' x)) :
    ProgSpec Inv A Step Post (srvForFoldM xs st body) := by
  induction xs generalizing st with
  | nil => exact .pure (st, none) (hDone st)
  | cons x rest ih =>
      exact (hb st x (List.mem_cons_self ..)).bind fun
        | .next st', _ => ih st' (fun s' y hy => hb s' y (List.mem_cons_of_mem x hy))
        | .breakLoop st', _ => .pure (st', none) (hDone st')
        | .ret st' v, hv => .pure (st', some v) hv

theorem progSpec_srvForFoldM_bind {σ σS ρ α γ : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {Post : γ → Prop} (xs : List α) (st : σS) (body : σS → α → ThreadProg σ (Qed.QedLoopStep σS ρ))
    {k : σS × Option ρ → ThreadProg σ γ} (hDone : ∀ st', ProgSpec Inv A Step Post (k (st', none)))
    (hb : ∀ st' x, x ∈ xs → ProgSpec Inv A Step
      (fun r => match r with | .next _ | .breakLoop _ => True | .ret s' v => ProgSpec Inv A Step Post (k (s', some v))) (body st' x)) :
    ProgSpec Inv A Step Post (srvForFoldM xs st body >>= k) := by
  induction xs generalizing st with
  | nil => simpa [srvForFoldM, threadProg_pure_bind] using hDone st
  | cons x rest ih =>
      change ProgSpec Inv A Step Post ((body st x >>= fun | .next st' => srvForFoldM rest st' body | .breakLoop st' => pure (st', none) | .ret st' r => pure (st', some r)) >>= k)
      rw [threadProg_bind_assoc]
      exact (hb st x (List.mem_cons_self ..)).bind fun
        | .next st', _ => ih st' (fun s' y hy => hb s' y (List.mem_cons_of_mem x hy))
        | .breakLoop st', _ => by simpa [threadProg_pure_bind] using hDone st'
        | .ret st' v, hv => by simpa [threadProg_pure_bind] using hv

theorem progSpec_srvForRangeM {σ σS ρ : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {Post : σS × Option ρ → Prop} (body : σS → Nat → ThreadProg σ (Qed.QedLoopStep σS ρ))
    (hDone : ∀ st, Post (st, none)) (r : Qed.QedRange) (st : σS)
    (hb : ∀ st' i, r.start ≤ i → i < r.stop → ProgSpec Inv A Step
      (fun res => match res with | .next _ | .breakLoop _ => True | .ret s' v => Post (s', some v)) (body st' i)) :
    ProgSpec Inv A Step Post (srvForRangeM r st body) := by
  rw [srvForRangeM_eq_srvForFoldM]
  exact progSpec_srvForFoldM body hDone r.toList st fun st' i hi => let hbnd := r.mem_toList_bounds hi; hb st' i hbnd.1 hbnd.2

theorem progSpec_srvForRangeM_bind {σ σS ρ γ : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {Post : γ → Prop} (r : Qed.QedRange) (st : σS) (body : σS → Nat → ThreadProg σ (Qed.QedLoopStep σS ρ))
    {k : σS × Option ρ → ThreadProg σ γ} (hDone : ∀ st', ProgSpec Inv A Step Post (k (st', none)))
    (hb : ∀ st' i, r.start ≤ i → i < r.stop → ProgSpec Inv A Step
      (fun res => match res with | .next _ | .breakLoop _ => True | .ret s' v => ProgSpec Inv A Step Post (k (s', some v))) (body st' i)) :
    ProgSpec Inv A Step Post (srvForRangeM r st body >>= k) := by
  rw [srvForRangeM_eq_srvForFoldM]
  exact progSpec_srvForFoldM_bind r.toList st body hDone fun st' i hi => let hbnd := r.mem_toList_bounds hi; hb st' i hbnd.1 hbnd.2

theorem progEffSpec_srvForFoldM {σ σS ρ α : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {EffOk : ServerEffect → Prop} {Post : σS × Option ρ → Prop}
    (body : σS → α → ThreadProg σ (Qed.QedLoopStep σS ρ))
    (hDone : ∀ st, Post (st, none)) (xs : List α) (st : σS)
    (hb : ∀ st' x, x ∈ xs → ProgEffSpec Inv A Step EffOk
      (fun r => match r with | .next _ | .breakLoop _ => True | .ret s' v => Post (s', some v)) (body st' x)) :
    ProgEffSpec Inv A Step EffOk Post (srvForFoldM xs st body) := by
  induction xs generalizing st with
  | nil => exact .pure (st, none) (hDone st)
  | cons x rest ih =>
      exact (hb st x (List.mem_cons_self ..)).bind fun
        | .next st', _ => ih st' (fun s' y hy => hb s' y (List.mem_cons_of_mem x hy))
        | .breakLoop st', _ => .pure (st', none) (hDone st')
        | .ret st' v, hv => .pure (st', some v) hv

theorem progEffSpec_srvForFoldM_bind {σ σS ρ α γ : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {EffOk : ServerEffect → Prop} {Post : γ → Prop}
    (xs : List α) (st : σS) (body : σS → α → ThreadProg σ (Qed.QedLoopStep σS ρ))
    {k : σS × Option ρ → ThreadProg σ γ} (hDone : ∀ st', ProgEffSpec Inv A Step EffOk Post (k (st', none)))
    (hb : ∀ st' x, x ∈ xs → ProgEffSpec Inv A Step EffOk
      (fun r => match r with | .next _ | .breakLoop _ => True | .ret s' v => ProgEffSpec Inv A Step EffOk Post (k (s', some v))) (body st' x)) :
    ProgEffSpec Inv A Step EffOk Post (srvForFoldM xs st body >>= k) := by
  induction xs generalizing st with
  | nil => simpa [srvForFoldM, threadProg_pure_bind] using hDone st
  | cons x rest ih =>
      change ProgEffSpec Inv A Step EffOk Post ((body st x >>= fun | .next st' => srvForFoldM rest st' body | .breakLoop st' => pure (st', none) | .ret st' r => pure (st', some r)) >>= k)
      rw [threadProg_bind_assoc]
      exact (hb st x (List.mem_cons_self ..)).bind fun
        | .next st', _ => ih st' (fun s' y hy => hb s' y (List.mem_cons_of_mem x hy))
        | .breakLoop st', _ => by simpa [threadProg_pure_bind] using hDone st'
        | .ret st' v, hv => by simpa [threadProg_pure_bind] using hv

theorem progEffSpec_srvForRangeM {σ σS ρ : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {EffOk : ServerEffect → Prop} {Post : σS × Option ρ → Prop}
    (body : σS → Nat → ThreadProg σ (Qed.QedLoopStep σS ρ))
    (hDone : ∀ st, Post (st, none)) (r : Qed.QedRange) (st : σS)
    (hb : ∀ st' i, r.start ≤ i → i < r.stop → ProgEffSpec Inv A Step EffOk
      (fun res => match res with | .next _ | .breakLoop _ => True | .ret s' v => Post (s', some v)) (body st' i)) :
    ProgEffSpec Inv A Step EffOk Post (srvForRangeM r st body) := by
  rw [srvForRangeM_eq_srvForFoldM]
  exact progEffSpec_srvForFoldM body hDone r.toList st fun st' i hi => let hbnd := r.mem_toList_bounds hi; hb st' i hbnd.1 hbnd.2

theorem progEffSpec_srvForRangeM_bind {σ σS ρ γ : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    {EffOk : ServerEffect → Prop} {Post : γ → Prop}
    (r : Qed.QedRange) (st : σS) (body : σS → Nat → ThreadProg σ (Qed.QedLoopStep σS ρ))
    {k : σS × Option ρ → ThreadProg σ γ} (hDone : ∀ st', ProgEffSpec Inv A Step EffOk Post (k (st', none)))
    (hb : ∀ st' i, r.start ≤ i → i < r.stop → ProgEffSpec Inv A Step EffOk
      (fun res => match res with | .next _ | .breakLoop _ => True | .ret s' v => ProgEffSpec Inv A Step EffOk Post (k (s', some v))) (body st' i)) :
    ProgEffSpec Inv A Step EffOk Post (srvForRangeM r st body >>= k) := by
  rw [srvForRangeM_eq_srvForFoldM]
  exact progEffSpec_srvForFoldM_bind r.toList st body hDone fun st' i hi => let hbnd := r.mem_toList_bounds hi; hb st' i hbnd.1 hbnd.2
@[inline, specialize] def dbRunTx {E : Type} [SrvErr E] {m : Type → Type} [Monad m] [MonadServer m] {α : Type}
    (cfg : Db.DbConfig) (body : UInt64 → m (Option (Except E α))) : m (Option (Except E α)) := do
  match ← MonadServer.dbTxBegin cfg with
  | .error e => return some (.error (SrvErr.ofApi e))
  | .ok txId =>
      match ← body txId with
      | some (.error e) => MonadServer.dbTxRollback cfg txId; return some (.error e)
      | res => match ← MonadServer.dbTxCommit cfg txId with
          | .ok () => return res
          | .error e => MonadServer.dbTxRollback cfg txId; return some (.error (SrvErr.ofApi e))

@[reducible, inline] def srvGetAt {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) : α := xs[i]'h
@[inline] def srvWithNewState {σ : Type} (sNew : σ) (P : σ → Prop) : Prop := P sNew
@[inline] def srvEnsPost {ε α : Type} (P : α → Prop) : Except ε α → Prop | .ok r => P r | .error _ => True
@[inline] def srvEnsPostOpt {ε α : Type} (P : α → Prop) : Except ε (Option α) → Prop | .ok (some r) => P r | _ => True
@[inline] def srvEnsErrPost {ε α : Type} (P : ε → Prop) : Except ε α → Prop | .ok _ => True | .error e => P e
@[inline] def srvEnsFails {ε α : Type} : Except ε α → Prop | .ok _ => False | .error _ => True
@[inline] def srvEnsFailsCode {α : Type} (code : Nat) : Except ApiError α → Prop | .ok _ => False | .error e => e.code = code

section SrvStepSimps
variable {E ε σ α β γ ρ : Type}

local macro "letEq2L " n1:ident bs1:bracketedBinder* " | " r1:term " | " f1:term " ; "
                       n2:ident bs2:bracketedBinder* " | " r2:term " | " f2:term : command =>
  `(@[simp] theorem $n1 $bs1* (val : γ) (k : (x : γ) → x = val → $r1) : $f1 (srvLetEq val k) = srvLetEq val (fun x hx => $f1 (k x hx)) := rfl
    @[simp] theorem $n2 $bs2* (val : γ) (k : (x : γ) → x = val → $r2) : $f2 (srvLetEq val k) = srvLetEq val (fun x hx => $f2 (k x hx)) := rfl)
local macro "letEqR " n:ident bs:bracketedBinder* " | " ret:term " | " a:ident " : " aty:term " | " f:term : command =>
  `(@[simp] theorem $n $bs* (val : γ) (k : (x : γ) → x = val → $ret) ($a : $aty) : $f (srvLetEq val k) $a = srvLetEq val (fun x hx => $f (k x hx) $a) := rfl)
local macro "simp3 " n1:ident bs1:bracketedBinder* " : " t1:term " ; " n2:ident bs2:bracketedBinder* " : " t2:term " ; " n3:ident bs3:bracketedBinder* " : " t3:term : command =>
  `(@[simp] theorem $n1 $bs1* : $t1 := rfl
    @[simp] theorem $n2 $bs2* : $t2 := rfl
    @[simp] theorem $n3 $bs3* : $t3 := rfl)
local macro "simp2 " n1:ident bs1:bracketedBinder* " : " t1:term " ; " n2:ident bs2:bracketedBinder* " : " t2:term : command =>
  `(@[simp] theorem $n1 $bs1* : $t1 := rfl
    @[simp] theorem $n2 $bs2* : $t2 := rfl)

simp2 srvSeq_none (s : σ) (next : σ → σ × Option ρ) : srvSeq (s, none) next = next s ; srvSeq_some (s : σ) (r : ρ) (next : σ → σ × Option ρ) : srvSeq (s, some r) next = (s, some r)
simp2 srvEmitSeq_none (s : σ) (es : List WsEmit) (next : σ → List WsEmit → σ × List WsEmit × Option ρ) : srvEmitSeq (s, es, none) next = next s es ; srvEmitSeq_some (s : σ) (es : List WsEmit) (r : ρ) (next : σ → List WsEmit → σ × List WsEmit × Option ρ) : srvEmitSeq (s, es, some r) next = (s, es, some r)
simp3 srvFinish_ok [SrvErr E] (s₀ s' : σ) (v : α) : srvFinish (E := E) s₀ (s', some (.ok v)) = (s', .ok v) ; srvFinish_err [SrvErr E] (s₀ s' : σ) (e : E) : srvFinish (E := E) (α := α) s₀ (s', some (.error e)) = (s₀, .error e) ; srvFinish_none [SrvErr E] (s₀ s' : σ) : srvFinish (E := E) s₀ (s', (none : Option (Except E α))) = (s₀, .error (SrvErr.ofApi (ApiError.internal "unreachable missing return")))
simp3 srvAtomicCommit_none (s₀ s' : σ) : srvAtomicCommit (E := E) (α := α) s₀ (s', none) = (s', none) ; srvAtomicCommit_ok (s₀ s' : σ) (v : α) : srvAtomicCommit (E := E) s₀ (s', some (.ok v)) = (s', some (.ok v)) ; srvAtomicCommit_err (s₀ s' : σ) (e : E) : srvAtomicCommit (E := E) (α := α) s₀ (s', some (.error e)) = (s₀, some (.error e))
simp3 srvFinishEmit_ok [SrvErr E] (s₀ s' : σ) (es : List WsEmit) (v : α) : srvFinishEmit (E := E) s₀ (s', es, some (.ok v)) = (s', .ok v, es) ; srvFinishEmit_err [SrvErr E] (s₀ s' : σ) (es : List WsEmit) (e : E) : srvFinishEmit (E := E) (α := α) s₀ (s', es, some (.error e)) = (s₀, .error e, []) ; srvFinishEmit_none [SrvErr E] (s₀ s' : σ) (es : List WsEmit) : srvFinishEmit (E := E) s₀ (s', es, (none : Option (Except E α))) = (s₀, .error (SrvErr.ofApi (ApiError.internal "unreachable missing return")), [])
simp3 srvAtomicCommitEmit_none (s₀ s' : σ) (es : List WsEmit) : srvAtomicCommitEmit (E := E) (α := α) s₀ (s', es, none) = (s', none, es) ; srvAtomicCommitEmit_ok (s₀ s' : σ) (es : List WsEmit) (v : α) : srvAtomicCommitEmit (E := E) s₀ (s', es, some (.ok v)) = (s', some (.ok v), es) ; srvAtomicCommitEmit_err (s₀ s' : σ) (es : List WsEmit) (e : E) : srvAtomicCommitEmit (E := E) (α := α) s₀ (s', es, some (.error e)) = (s₀, some (.error e), [])
simp3 srvGetAt_eq (xs : Array α) (i : Nat) (h : i < xs.size) : srvGetAt xs i h = xs[i]'h ; srvEnsPost_ok (P : α → Prop) (r : α) : srvEnsPost (ε := ε) P (.ok r) = P r ; srvEnsPost_err (P : α → Prop) (e : ε) : srvEnsPost P (.error e) = True
simp3 srvEnsPostOpt_some (P : α → Prop) (r : α) : srvEnsPostOpt (ε := ε) P (.ok (some r)) = P r ; srvEnsPostOpt_none (P : α → Prop) : srvEnsPostOpt (ε := ε) P (.ok none) = True ; srvEnsPostOpt_err (P : α → Prop) (e : ε) : srvEnsPostOpt P (.error e) = True
simp2 srvEnsErrPost_ok (P : ε → Prop) (r : α) : srvEnsErrPost P (.ok r) = True ; srvEnsErrPost_err (P : ε → Prop) (e : ε) : srvEnsErrPost (α := α) P (.error e) = P e
simp2 srvEnsFails_ok (r : α) : srvEnsFails (ε := ε) (.ok r) = False ; srvEnsFails_err (e : ε) : srvEnsFails (α := α) (.error e) = True
simp2 srvEnsFailsCode_ok (c : Nat) (r : α) : srvEnsFailsCode c (.ok r) = False ; srvEnsFailsCode_err (c : Nat) (e : ApiError) : srvEnsFailsCode (α := α) c (.error e) = (e.code = c)
theorem srvFinishEmit_err_no_emits [SrvErr E] (s₀ s' : σ) (es : List WsEmit) (e : E) : (srvFinishEmit (E := E) (α := α) s₀ (s', es, some (.error e))).2.2 = [] := rfl
theorem srvAtomicCommitEmit_err_no_emits (s₀ s' : σ) (es : List WsEmit) (e : E) : (srvAtomicCommitEmit (E := E) (α := α) s₀ (s', es, some (.error e))).2.2 = [] := rfl
theorem srvWithNewState_apply (s : σ) (P : σ → Prop) : srvWithNewState s P = P s := rfl

letEq2L srvFinish_srvLetEq [SrvErr E] (s₀ : σ) | σ × Option (Except E α) | srvFinish s₀ ; srvAtomicCommit_srvLetEq (s₀ : σ) | σ × Option (Except E α) | srvAtomicCommit s₀
letEq2L srvFinishEmit_srvLetEq [SrvErr E] (s₀ : σ) | σ × List WsEmit × Option (Except E α) | srvFinishEmit s₀ ; srvAtomicCommitEmit_srvLetEq (s₀ : σ) | σ × List WsEmit × Option (Except E α) | srvAtomicCommitEmit s₀
letEq2L prod_fst_srvLetEq | α × β | Prod.fst ; prod_snd_srvLetEq | α × β | Prod.snd
letEq2L srvEnsPost_srvLetEq (P : α → Prop) | Except ε α | srvEnsPost P ; srvEnsPostOpt_srvLetEq (P : α → Prop) | Except ε (Option α) | srvEnsPostOpt P
letEq2L srvEnsErrPost_srvLetEq (P : ε → Prop) | Except ε α | srvEnsErrPost P ; srvEnsFails_srvLetEq | Except ε α | srvEnsFails
@[simp] theorem srvEnsFailsCode_srvLetEq (c : Nat) (val : γ) (k : (x : γ) → x = val → Except ApiError α) : srvEnsFailsCode c (srvLetEq val k) = srvLetEq val (fun x hx => srvEnsFailsCode c (k x hx)) := rfl
letEqR srvSeq_srvLetEq | σ × Option ρ | next : σ → σ × Option ρ | srvSeq
letEqR srvEmitSeq_srvLetEq | σ × List WsEmit × Option ρ | next : σ → List WsEmit → σ × List WsEmit × Option ρ | srvEmitSeq
letEqR srvWithNewState_srvLetEq | σ | P : σ → Prop | srvWithNewState

@[simp] theorem srvEnsPostOpt_ok_iff (P : α → Prop) (o : Option α) : srvEnsPostOpt (ε := ε) P (.ok o) = (∀ r, o = some r → P r) := propext (by cases o <;> simp [srvEnsPostOpt])
theorem getElem_congr_arr {xs ys : Array α} {j : Nat} (heq : ys = xs) (hj : j < ys.size) : ys[j]'hj = xs[j]'(heq ▸ hj) := by cases heq; rfl
theorem srvGetAt_congr_arr {xs ys : Array α} {j : Nat} (heq : ys = xs) (hj : j < ys.size) : srvGetAt ys j hj = xs[j]'(heq ▸ hj) := getElem_congr_arr heq hj
end SrvStepSimps

end Qed.Server

/-! ## Server-Safe Standard Intrinsics (`Qed.Secret`, `Qed.Crypto`, `Qed.Time`, `Qed.Random`) -/

namespace Qed

/-- Redacted secret string wrapper. Intentionally omits `ToJson`, `ToProto`, `ToSql`, and `ToQueryVal`
    instances so secrets cannot accidentally leak into wire responses, SQL queries, or logs. -/
structure Secret where
  private mk ::
  private raw : String
deriving DecidableEq

namespace Secret
@[inline] def ofString (s : String) : Secret := ⟨s⟩
@[inline] def expose (s : Secret) : String := s.raw
@[inline] def toUTF8 (s : Secret) : ByteArray := s.raw.toUTF8
@[inline] def isEmpty (s : Secret) : Bool := s.raw.isEmpty
instance : ToString Secret := ⟨fun _ => "<redacted>"⟩
instance : Repr Secret := ⟨fun _ _ => "<redacted>"⟩
end Secret

class ToBytes (α : Type) where
  toBytes : α → ByteArray
@[inline] instance : ToBytes ByteArray := ⟨id⟩
@[inline] instance : ToBytes String := ⟨String.toUTF8⟩
@[inline] instance : ToBytes Secret := ⟨Secret.toUTF8⟩

namespace Crypto
open Qed.Server

def hmacSha256 {α β : Type} [ToBytes α] [ToBytes β] {m : Type → Type} [MonadServer m] (key : α) (msg : β) : m ByteArray :=
  MonadServer.hmacSha256 (ToBytes.toBytes key) (ToBytes.toBytes msg)

def hmacSha256Hex {α β : Type} [ToBytes α] [ToBytes β] {m : Type → Type} [Monad m] [MonadServer m] (key : α) (msg : β) : m String :=
  MonadServer.hmacSha256 (ToBytes.toBytes key) (ToBytes.toBytes msg) >>= fun mac => Pure.pure (Proto.encodeHex mac)

def constEq {α β : Type} [ToBytes α] [ToBytes β] {m : Type → Type} [MonadServer m] (a : α) (b : β) : m Bool :=
  MonadServer.constEq (ToBytes.toBytes a) (ToBytes.toBytes b)

def sha256 {α : Type} [ToBytes α] {m : Type → Type} [MonadServer m] (data : α) : m ByteArray :=
  MonadServer.sha256 (ToBytes.toBytes data)

def sha256Hex {α : Type} [ToBytes α] {m : Type → Type} [Monad m] [MonadServer m] (data : α) : m String :=
  MonadServer.sha256 (ToBytes.toBytes data) >>= fun h => Pure.pure (Proto.encodeHex h)

instance {σ α β : Type} [ToBytes α] [ToBytes β] (key : α) (msg : β) : SafeIO (hmacSha256 (m := ThreadProg σ) key msg) :=
  ⟨.io (.hmacSha256 _ _) _ .pure⟩
instance {σ α β : Type} [ToBytes α] [ToBytes β] (key : α) (msg : β) : SafeIO (hmacSha256Hex (m := ThreadProg σ) key msg) :=
  ⟨noAtomic_bind (.io (.hmacSha256 _ _) _ .pure) fun _ => .pure _⟩
instance {σ α β : Type} [ToBytes α] [ToBytes β] (a : α) (b : β) : SafeIO (constEq (m := ThreadProg σ) a b) :=
  ⟨.io (.constEq _ _) _ .pure⟩
instance {σ α : Type} [ToBytes α] (data : α) : SafeIO (sha256 (m := ThreadProg σ) data) :=
  ⟨.io (.sha256 _) _ .pure⟩
instance {σ α : Type} [ToBytes α] (data : α) : SafeIO (sha256Hex (m := ThreadProg σ) data) :=
  ⟨noAtomic_bind (.io (.sha256 _) _ .pure) fun _ => .pure _⟩
end Crypto

namespace Time
open Qed.Server

def nowMs {m : Type → Type} [Monad m] [MonadServer m] : m Nat :=
  MonadServer.nowMs >>= fun ms => Pure.pure ms.toNat

def nowSec {m : Type → Type} [Monad m] [MonadServer m] : m Nat :=
  MonadServer.nowMs >>= fun ms => Pure.pure (ms.toNat / 1000)

instance {σ : Type} : SafeIO (nowMs (m := ThreadProg σ)) :=
  ⟨noAtomic_bind (.io .nowMs _ .pure) fun _ => .pure _⟩
instance {σ : Type} : SafeIO (nowSec (m := ThreadProg σ)) :=
  ⟨noAtomic_bind (.io .nowMs _ .pure) fun _ => .pure _⟩
end Time

namespace Random
open Qed.Server

def hex {m : Type → Type} [MonadServer m] (numBytes : Nat) : m String :=
  MonadServer.randomHex numBytes.toUInt32

def bytes {m : Type → Type} [MonadServer m] (numBytes : Nat) : m ByteArray :=
  MonadServer.randomBytes numBytes.toUInt32

def formatUuidV4 (bs : ByteArray) : String :=
  let getB (i : Nat) : UInt8 := if h : i < bs.size then bs[i] else 0
  let b6 := (getB 6 &&& 0x0f) ||| 0x40
  let b8 := (getB 8 &&& 0x3f) ||| 0x80
  let hex2 (b : UInt8) : String := String.ofList [hexDigitLower (b.toNat / 16), hexDigitLower (b.toNat % 16)]
  hex2 (getB 0) ++ hex2 (getB 1) ++ hex2 (getB 2) ++ hex2 (getB 3) ++ "-" ++
  hex2 (getB 4) ++ hex2 (getB 5) ++ "-" ++
  hex2 b6 ++ hex2 (getB 7) ++ "-" ++
  hex2 b8 ++ hex2 (getB 9) ++ "-" ++
  hex2 (getB 10) ++ hex2 (getB 11) ++ hex2 (getB 12) ++ hex2 (getB 13) ++ hex2 (getB 14) ++ hex2 (getB 15)

def uuid {m : Type → Type} [Monad m] [MonadServer m] : m String :=
  MonadServer.randomBytes 16 >>= fun bs => Pure.pure (formatUuidV4 bs)

instance {σ : Type} (n : Nat) : SafeIO (hex (m := ThreadProg σ) n) := ⟨.io (.randomHex _) _ .pure⟩
instance {σ : Type} (n : Nat) : SafeIO (bytes (m := ThreadProg σ) n) := ⟨.io (.randomBytes _) _ .pure⟩
instance {σ : Type} : SafeIO (uuid (m := ThreadProg σ)) :=
  ⟨noAtomic_bind (.io (.randomBytes 16) _ .pure) fun _ => .pure _⟩
end Random

end Qed
