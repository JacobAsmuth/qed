import Qed.Server.Net
namespace Qed.Server.Http
open Qed.Server.Net

def maxReqHdrBytes  : Nat := 65536
def maxReqBodyBytes : Nat := 32 * 1024 * 1024
def maxReqHeaders   : Nat := 96
def maxWsMsgBytes   : Nat := 4 * 1024 * 1024

structure ReqHdrMeta where
  (keepAlive : Bool) (headers : Array (String × String))
  (upgrade? conn? wsKey? wsVer? host? origin? : Option String := none) (dupOrigin : Bool := false)
  (secFetchSite? : Option String := none) (dupSfs : Bool := false) (contentType? : Option String := none)
  (dupCt hasCookie : Bool := false) (auth? : Option String := none) (hasIfNoneMatch acceptsGzip : Bool := false)

structure ParsedReqHead extends ReqHdrMeta where (method target : String) (isHttp11 : Bool) (contentLen : Nat)
private structure HdrFoldState extends ReqHdrMeta where (contentLen? : Option Nat) (hostCount : Nat)

@[inline] private def isHostHeader (k : String) : Bool := k.utf8ByteSize == 4 && (k == "Host" || k == "host" || k.toLower == "host")
private theorem isHostHeader_imp_toLower (k : String) (h : isHostHeader k = true) : (k.toLower == "host") = true := by
  unfold isHostHeader at h; simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h.2 with (h1 | h2) | h3
  · rw [beq_iff_eq.1 h1]; exact beq_iff_eq.2 (by unfold String.toLower; apply String.ext; simp [Char.toLower]; decide)
  · rw [beq_iff_eq.1 h2]; exact beq_iff_eq.2 (by unfold String.toLower; apply String.ext; simp [Char.toLower])
  · exact h3

private def acceptEncodingHasGzip (v : String) : Bool :=
  (Qed.Str.splitChar v ',').any fun item => match Qed.Str.splitChar item ';' with
    | tok :: params => eqCI (trimWs tok) "gzip" && !(params.any fun p => match Qed.Str.splitChar p '=' with
        | [k, qv] => let lq := trimWs qv; eqCI (trimWs k) "q" && (lq == "0" || lq == "0.0" || lq == "0.00" || lq == "0.000") | _ => false)
    | [] => false
private def setOnce (cur : Option String) (dup : Bool) (v : String) : Option String × Bool := if cur.isSome then (cur, true) else (some v, dup)
private def parseOtherHeader (k v : String) (st : HdrFoldState) : HdrFoldState :=
  let st := { st with headers := st.headers.push (k, v) }
  match k.utf8ByteSize with
  | 6  => if eqCI k "origin" then let (origin?, dupOrigin) := setOnce st.origin? st.dupOrigin v; { st with origin?, dupOrigin } else if eqCI k "cookie" then { st with hasCookie := true } else st
  | 7  => if eqCI k "upgrade" then { st with upgrade? := some v } else st
  | 10 => if eqCI k "connection" then { st with keepAlive := if containsCI v "close" then false else if containsCI v "keep-alive" then true else st.keepAlive, conn? := some v } else st
  | 12 => if eqCI k "content-type" then let (contentType?, dupCt) := setOnce st.contentType? st.dupCt v; { st with contentType?, dupCt } else st
  | 13 => if eqCI k "authorization" then (if st.auth?.isNone then { st with auth? := some v } else st) else if eqCI k "if-none-match" then { st with hasIfNoneMatch := true } else st
  | 14 => if eqCI k "sec-fetch-site" then let (secFetchSite?, dupSfs) := setOnce st.secFetchSite? st.dupSfs v; { st with secFetchSite?, dupSfs } else st
  | 15 => if eqCI k "accept-encoding" && acceptEncodingHasGzip v then { st with acceptsGzip := true } else st
  | 17 => if eqCI k "sec-websocket-key" then { st with wsKey? := some v } else st
  | 21 => if eqCI k "sec-websocket-version" then { st with wsVer? := some v } else st
  | _  => st
private theorem parseOtherHeader_invariants (k v : String) (st : HdrFoldState) :
    (parseOtherHeader k v st).contentLen? = st.contentLen? ∧ (parseOtherHeader k v st).hostCount = st.hostCount ∧
    (parseOtherHeader k v st).headers = st.headers.push (k, v) := by
  unfold parseOtherHeader; dsimp only; split <;> repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩
def parseOneHeaderLine (line : String) (st : HdrFoldState) : Except (Nat × String) HdrFoldState :=
  match splitHeaderKv line with
  | none => .error (400, "malformed header")
  | some (k, v) =>
      if !isValidHttpToken k then .error (400, "invalid header name")
      else if eqCI k "transfer-encoding" then .error (501, "Transfer-Encoding not supported")
      else if st.headers.size >= maxReqHeaders then .error (431, "too many headers")
      else if isHostHeader k then
        if v.isEmpty || hasCtlOrCrlf v false then .error (400, "invalid Host header")
        else if st.hostCount >= 1 then .error (400, "duplicate Host header")
        else .ok { st with hostCount := st.hostCount + 1, host? := some v, headers := st.headers.push (k, v) }
      else if eqCI k "content-length" then match parseStrictU64 v 18446744073709551615 with
        | none => .error (400, "invalid Content-Length")
        | some cl => if st.contentLen?.any (· != cl) then .error (400, "conflicting Content-Length headers")
            else if cl > maxReqBodyBytes then .error (413, "payload too large")
            else .ok { st with contentLen? := some cl, headers := st.headers.push (k, v) }
      else .ok (parseOtherHeader k v st)
private def parseHdrLines (lines : Array String) (idx : Nat) (st : HdrFoldState) : Except (Nat × String) HdrFoldState :=
  if h : idx < lines.size then match parseOneHeaderLine lines[idx] st with | .error e => .error e | .ok st' => parseHdrLines lines (idx + 1) st' else .ok st
termination_by lines.size - idx
@[inline] private def eqBytesAt (s : String) (off : Nat) (lit : String) : Bool :=
  if h : off + lit.utf8ByteSize ≤ s.utf8ByteSize then
    let rec go (k : Nat) : Bool := if hk : k < lit.utf8ByteSize then if s.getUTF8Byte ⟨off + k⟩ (show off + k < s.utf8ByteSize by omega) == lit.getUTF8Byte ⟨k⟩ hk then go (k + 1) else false else true
    termination_by lit.utf8ByteSize - k; go 0
  else false
private def parseReqLine (line : String) : Except (Nat × String) (String × String × Bool) := do
  let bad := (400, "malformed request line")
  let some sp1 := findByte line 0 32 | throw bad
  let some sp2 := findByte line (sp1 + 1) 32 | throw bad
  if (findByte line (sp2 + 1) 32).isSome || sp1 == 0 || sp2 <= sp1 + 1 then throw bad
  let isVer (v : String) := line.utf8ByteSize - (sp2 + 1) == 8 && eqBytesAt line (sp2 + 1) v
  let isHttp11 := isVer "HTTP/1.1"; if !isHttp11 && !isVer "HTTP/1.0" then throw (400, "unsupported HTTP version")
  let target := if sp2 == sp1 + 2 && eqBytesAt line (sp1 + 1) "/" then "/" else String.Pos.Raw.extract line ⟨sp1 + 1⟩ ⟨sp2⟩
  if sp1 == 3 && eqBytesAt line 0 "GET" then return ("GET", target, isHttp11)
  if sp1 == 4 && eqBytesAt line 0 "POST" then return ("POST", target, isHttp11)
  let method := String.Pos.Raw.extract line ⟨0⟩ ⟨sp1⟩; if !isValidHttpToken method then throw bad else return (method, target, isHttp11)
def parseRequestHead (headBytes : ByteArray) : Except (Nat × String) ParsedReqHead :=
  if headBytes.size > maxReqHdrBytes then .error (431, "request headers too large")
  else match splitCrlfLines headBytes with
    | .error e => .error (400, e)
    | .ok lines => if h0 : lines.size = 0 then .error (400, "malformed request line")
        else match parseReqLine (lines[0]'(by omega)) with
          | .error e => .error e
          | .ok (method, target, isHttp11) => match parseHdrLines lines 1 { keepAlive := isHttp11, contentLen? := none, hostCount := 0, headers := Array.mkEmpty 12 } with
              | .error e => .error e
              | .ok st => if isHttp11 && st.hostCount != 1 then .error (400, "missing Host header") else .ok { st.toReqHdrMeta with method, target, isHttp11, contentLen := st.contentLen?.getD 0 }

theorem parseRequestHead_rejects_nul (headBytes : ByteArray) (hnul : byteArrayContains headBytes 0 = true) : ∃ e, parseRequestHead headBytes = .error e := by
  unfold parseRequestHead; by_cases hsz : headBytes.size > maxReqHdrBytes
  · exact ⟨(431, "request headers too large"), by simp [hsz]⟩
  · rcases splitCrlfLines_rejects_nul headBytes hnul with ⟨errMsg, hsplit⟩; exact ⟨(400, errMsg), by simp [hsz, hsplit]⟩
theorem parseOneHeaderLine_rejects_bad_name (line k v : String) (st : HdrFoldState) (hkv : splitHeaderKv line = some (k, v)) (hbad : isValidHttpToken k = false) :
    parseOneHeaderLine line st = .error (400, "invalid header name") := by simp [parseOneHeaderLine, hkv, hbad]
private theorem parseOneHeaderLine_ok_spec (line : String) (st st' : HdrFoldState) (hok : parseOneHeaderLine line st = .ok st') :
    ((∀ cl, st.contentLen? = some cl → cl ≤ maxReqBodyBytes) → ∀ cl, st'.contentLen? = some cl → cl ≤ maxReqBodyBytes) ∧
    (st'.hostCount = st.hostCount ∨ (st'.hostCount = st.hostCount + 1 ∧ ∃ k v, (k, v) ∈ st'.headers.toList ∧ k.toLower == "host")) ∧
    (∀ p ∈ st.headers.toList, p ∈ st'.headers.toList) := by
  revert hok; fun_cases parseOneHeaderLine line st <;> (intro hok; cases hok)
  · rename_i k v _ _ _ _ hhost _ _
    exact ⟨id, Or.inr ⟨rfl, k, v, by simp [Array.toList_push], isHostHeader_imp_toLower k hhost⟩, fun p hp => by simp [Array.toList_push, hp]⟩
  · exact ⟨fun _ _ hc => by cases hc; omega, Or.inl rfl, fun p hp => by simp [Array.toList_push, hp]⟩
  · rename_i k v _ _ _ _ _ _; have hinv := parseOtherHeader_invariants k v st
    exact ⟨fun h => hinv.1 ▸ h, Or.inl hinv.2.1, fun p hp => by rw [hinv.2.2]; simp [Array.toList_push, hp]⟩
private theorem parseHdrLines_inv (P : HdrFoldState → Prop) (hstep : ∀ line st st', P st → parseOneHeaderLine line st = .ok st' → P st')
    (lines : Array String) (idx : Nat) (st st' : HdrFoldState) (hinit : P st) (hok : parseHdrLines lines idx st = .ok st') : P st' := by
  unfold parseHdrLines at hok; split at hok
  · cases h1 : parseOneHeaderLine lines[idx] st with
    | error _ => simp [h1] at hok
    | ok stMid => simp only [h1] at hok; exact parseHdrLines_inv P hstep lines (idx + 1) stMid st' (hstep _ _ _ hinit h1) hok
  · simp only [Except.ok.injEq] at hok; subst hok; exact hinit
termination_by lines.size - idx
private theorem parseRequestHead_ok_elim (headBytes : ByteArray) (req : ParsedReqHead) (hok : parseRequestHead headBytes = .ok req) :
    ∃ (lines : Array String) (st : HdrFoldState),
      parseHdrLines lines 1 { keepAlive := req.isHttp11, contentLen? := none, hostCount := 0, headers := Array.mkEmpty 12 } = .ok st ∧
      (req.isHttp11 = true → st.hostCount = 1) ∧ req.contentLen = st.contentLen?.getD 0 ∧ req.headers = st.headers := by
  revert hok; fun_cases parseRequestHead headBytes <;> (intro hok; cases hok)
  rename_i hmiss; refine ⟨_, _, ‹_›, ?_, rfl, rfl⟩; intro h11; simp at hmiss; exact hmiss h11
theorem parseRequestHead_http11_has_host (headBytes : ByteArray) (req : ParsedReqHead) (hok : parseRequestHead headBytes = .ok req) (h11 : req.isHttp11 = true) :
    ∃ k v, (k, v) ∈ req.headers.toList ∧ k.toLower == "host" := by
  rcases parseRequestHead_ok_elim headBytes req hok with ⟨lines, st, hfold, hhost, _, hhdrs⟩; rw [hhdrs]
  refine parseHdrLines_inv (fun s => s.hostCount > 0 → ∃ k v, (k, v) ∈ s.headers.toList ∧ k.toLower == "host")
    (fun line s s' hinv hstep hpos => ?_) lines 1 _ st (by intro h; simp at h) hfold (by have := hhost h11; omega)
  have ⟨_, hhc, hmono⟩ := parseOneHeaderLine_ok_spec line s s' hstep
  rcases hhc with heq | ⟨_, k, v, hmem, hk⟩
  · rw [heq] at hpos; rcases hinv hpos with ⟨k, v, hmem, hk⟩; exact ⟨k, v, hmono _ hmem, hk⟩
  · exact ⟨k, v, hmem, hk⟩
theorem parseRequestHead_contentLen_le (headBytes : ByteArray) (req : ParsedReqHead) (hok : parseRequestHead headBytes = .ok req) : req.contentLen ≤ maxReqBodyBytes := by
  rcases parseRequestHead_ok_elim headBytes req hok with ⟨lines, st, hfold, _, hcl, _⟩; rw [hcl]
  have hb := parseHdrLines_inv (fun s => ∀ cl, s.contentLen? = some cl → cl ≤ maxReqBodyBytes)
    (fun line s s' hinv hstep => (parseOneHeaderLine_ok_spec line s s' hstep).1 hinv) lines 1 _ st (by intro _ h; cases h) hfold
  cases hc : st.contentLen? with | none => simp [maxReqBodyBytes] | some cl => simpa [hc] using hb cl hc

def statusReason : Nat → String
  | 200 => "OK" | 201 => "Created" | 204 => "No Content" | 301 => "Moved Permanently" | 302 => "Found" | 304 => "Not Modified"
  | 400 => "Bad Request" | 401 => "Unauthorized" | 403 => "Forbidden" | 404 => "Not Found" | 405 => "Method Not Allowed"
  | 413 => "Payload Too Large" | 415 => "Unsupported Media Type" | 429 => "Too Many Requests" | 431 => "Request Header Fields Too Large"
  | 500 => "Internal Server Error" | 501 => "Not Implemented" | 503 => "Service Unavailable" | _ => "OK"
def safeContentType (ct : String) : String := if hasCtlOrCrlf ct false then "application/octet-stream" else ct
theorem safeContentType_no_crlf (ct : String) : hasCtlOrCrlf (safeContentType ct) false = false := by
  unfold safeContentType; split
  · decide
  · rename_i h; simpa using h
def isCompressibleMime (mime : String) : Bool :=
  ["text/", "application/javascript", "application/json", "application/manifest+json", "application/xml", "image/svg+xml"].any (startsWithCI mime ·)
private def formatRespFrame (status : Nat) (bodyHdrs : String) (keepAlive : Bool) (etag? cacheControl? : Option String := none) (extraHeaders : List (String × String) := []) : ByteArray :=
  let code := if status >= 100 && status <= 599 then status else 500
  let optH (k : String) (o : Option String) := o.elim "" fun v => if hasCtlOrCrlf v false then "" else s!"{k}: {v}\r\n"
  let extra := extraHeaders.foldl (init := "") fun acc (k, v) => if isValidHttpToken k && !hasCtlOrCrlf v false then acc ++ k ++ ": " ++ v ++ "\r\n" else acc
  (s!"HTTP/1.1 {code} {statusReason code}\r\n{bodyHdrs}X-Content-Type-Options: nosniff\r\n" ++ optH "ETag" etag? ++ optH "Cache-Control" cacheControl? ++ extra ++ s!"Connection: {if keepAlive then "keep-alive" else "close"}\r\n\r\n").toUTF8
def formatHttpResponseHead (status : Nat) (contentType : String) (contentLen : Nat) (keepAlive noStore : Bool) (etag? cacheControl? : Option String := none) (extraHeaders : List (String × String) := []) : ByteArray :=
  formatRespFrame status s!"Content-Type: {safeContentType contentType}\r\nContent-Length: {contentLen}\r\n" keepAlive etag? (cacheControl?.orElse fun _ => if noStore then some "no-store" else none) extraHeaders
def formatNotModifiedResponse (etag : String) (keepAlive : Bool) : ByteArray := formatRespFrame 304 "" keepAlive (some etag) (some "public, max-age=0, must-revalidate")
def formatNoContentResponse (keepAlive : Bool) (cacheControl? : Option String := none) : ByteArray := formatRespFrame 204 "" keepAlive none cacheControl?
private def stripWeakPrefix (s : String) : String := let t := trimOws s; if t.startsWith "W/" then String.ofList (t.toList.drop 2) else t
def etagMatchesIfNoneMatch (headers : Array (String × String)) (etag : String) : Bool :=
  let target := stripWeakPrefix etag
  headers.any fun (k, v) => k.toLower == "if-none-match" && (v.splitOn ",").any fun item => let t := trimOws item; t == "*" || stripWeakPrefix t == target
def formatHttpResponse (status : Nat) (contentType : String) (body : ByteArray) (headOnly keepAlive noStore : Bool) (etag? cacheControl? : Option String := none) (extraHeaders : List (String × String) := []) : ByteArray :=
  let head := formatHttpResponseHead status contentType body.size keepAlive noStore etag? cacheControl? extraHeaders; if headOnly then head else head ++ body
private def okProtoHeadPrefix : ByteArray := "HTTP/1.1 200 OK\r\nContent-Type: application/x-protobuf\r\nContent-Length: ".toUTF8
private def okHeadTailKA      : ByteArray := "\r\nX-Content-Type-Options: nosniff\r\nConnection: keep-alive\r\n\r\n".toUTF8
private def okHeadTailClose   : ByteArray := "\r\nX-Content-Type-Options: nosniff\r\nConnection: close\r\n\r\n".toUTF8
@[inline] private def appendByteSlice (dst src : ByteArray) : ByteArray := src.copySlice 0 dst dst.size src.size false
def formatOkProtoResponse (body : ByteArray) (headOnly keepAlive : Bool) : ByteArray :=
  let (tail, n) := (if keepAlive then okHeadTailKA else okHeadTailClose, body.size)
  let out := appendByteSlice (ByteArray.emptyWithCapacity (okProtoHeadPrefix.size + 10 + tail.size + if headOnly then 0 else n)) okProtoHeadPrefix
  let out := if n < 10 then out.push (UInt8.ofNat (48 + n)) else if n < 100 then (out.push (UInt8.ofNat (48 + n / 10))).push (UInt8.ofNat (48 + n % 10)) else appendByteSlice out (toString n).toUTF8
  let out := appendByteSlice out tail; if headOnly then out else appendByteSlice out body
def formatTextResponse (status : Nat) (msg : String) (isHead keepAlive : Bool) (extraHeaders : List (String × String) := []) : ByteArray :=
  formatHttpResponse status "text/plain; charset=utf-8" msg.toUTF8 isHead keepAlive false (extraHeaders := extraHeaders)
def formatErrorResponse (status : Nat) (msg : String) : ByteArray := formatTextResponse status msg false false
def formatWsUpgradeResponse (acceptB64 : String) : ByteArray := s!"HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: {acceptB64}\r\n\r\n".toUTF8
def setCookieHeaders (cookies : List SetCookie) : List (String × String) := cookies.map fun c => ("Set-Cookie", c.render)

structure StaticTarget where (relPath mime : String) (isHead noStore isBuildId : Bool) deriving BEq

def guessMimeType (path : String) : Option String :=
  match (path.splitOn ".").reverse with
  | ext :: _ :: _ => match ext.toLower with
      | "mjs" | "js" => some "text/javascript; charset=utf-8" | "css" => some "text/css; charset=utf-8" | "html" => some "text/html; charset=utf-8"
      | "json" | "map" => some "application/json; charset=utf-8" | "webmanifest" => some "application/manifest+json; charset=utf-8" | "xml" => some "application/xml; charset=utf-8"
      | "pdf" => some "application/pdf" | "svg" => some "image/svg+xml" | "png" => some "image/png" | "jpg" | "jpeg" => some "image/jpeg"
      | "gif" => some "image/gif" | "webp" => some "image/webp" | "avif" => some "image/avif" | "ico" => some "image/x-icon" | "wasm" => some "application/wasm"
      | "woff2" => some "font/woff2" | "woff" => some "font/woff" | "ttf" => some "font/ttf" | "otf" => some "font/otf" | "mp4" => some "video/mp4"
      | "webm" => some "video/webm" | "mp3" => some "audio/mpeg" | "ogg" => some "audio/ogg" | "txt" => some "text/plain; charset=utf-8" | _ => none
  | _ => none
private def lastPathSeg (s : String) : String := (Qed.Str.splitChar s '/').reverse.headD s
def isBlockedStaticName (pathOnly : String) : Bool := let b := lastPathSeg pathOnly; eqCI b "qed_deploy.json" || eqCI b "qed_manifest.json"
def classifyStaticPath (method target : String) (devMode : Bool) : Option StaticTarget :=
  let isHead := method == "HEAD"
  if method != "GET" && !isHead then none
  else if target == "/" || ((findByte target 0 46).isNone && !(devMode && (target == "/__build_id" || target == "/__dev_status"))) then none
  else
    let pathOnly := (target.splitOn "?").headD target
    if pathOnly.isEmpty || pathOnly.utf8ByteSize >= 2048 || !pathOnly.startsWith "/" ||
       pathOnly.contains '\\' || pathOnly.contains '\x00' || pathOnly.startsWith "/_qed/" || (pathOnly.splitOn "..").length > 1 then none
    else
      let relPath := String.ofList (pathOnly.toList.drop 1)
      if relPath.isEmpty || relPath.startsWith "/" || (relPath.splitOn "/").any (fun seg => seg.isEmpty || seg == ".") || isBlockedStaticName pathOnly then none
      else if devMode && pathOnly == "/__build_id" then some { relPath, mime := "text/plain; charset=utf-8", isHead, noStore := true, isBuildId := true }
      else if devMode && pathOnly == "/__dev_status" then some { relPath, mime := "application/json; charset=utf-8", isHead, noStore := true, isBuildId := true }
      else (guessMimeType pathOnly).map fun mime => { relPath, mime, isHead, noStore := devMode, isBuildId := false }
def isContentHashedAsset (relPath : String) : Bool :=
  match (Qed.Str.splitChar (lastPathSeg relPath) '.').reverse with
  | ext :: hash :: stem :: _ => !stem.isEmpty && ["mjs", "MJS", "js", "JS", "css", "CSS"].contains ext && hash.length >= 8 && hash.length <= 16 && hash.toList.all fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')
  | _ => false
theorem isContentHashedAsset_hashed : isContentHashedAsset "app.0123456789ab.mjs" = true := by simp [isContentHashedAsset, lastPathSeg, Qed.Str.splitChar, Qed.Str.splitCharAux]; decide
theorem isContentHashedAsset_plain  : isContentHashedAsset "app.mjs" = false := by simp [isContentHashedAsset, lastPathSeg, Qed.Str.splitChar, Qed.Str.splitCharAux]
theorem classifyStaticPath_rejects_dotdot (method target : String) (devMode : Bool) (h : (((target.splitOn "?").headD target).splitOn "..").length > 1) : classifyStaticPath method target devMode = none := by
  unfold classifyStaticPath; by_cases hm : method != "GET" && !(method == "HEAD")
  · simp [hm]
  · simp only [hm, ↓reduceIte, Bool.false_eq_true]; split
    · rfl
    · simp only [List.headD_eq_head?_getD] at h; simp; intro _ _ _ _ _ _ hle; omega

private def rotl32 (x n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))
private def sha1Expand (w : Array UInt32) (i : Nat) : Nat → Array UInt32
  | 0 => w | k + 1 => let g idx := w.getD idx 0; sha1Expand (w.push (rotl32 (g (i - 3) ^^^ g (i - 8) ^^^ g (i - 14) ^^^ g (i - 16)) 1)) (i + 1) k
private def sha1Rounds (w : Array UInt32) (i : Nat) (a b c d e : UInt32) : Nat → UInt32 × UInt32 × UInt32 × UInt32 × UInt32
  | 0 => (a, b, c, d, e)
  | k + 1 =>
      let (f, kc) : UInt32 × UInt32 := if i < 20 then ((b &&& c) ||| ((~~~b) &&& d), 0x5A827999) else if i < 40 then (b ^^^ c ^^^ d, 0x6ED9EBA1)
        else if i < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), 0x8F1BBCDC) else (b ^^^ c ^^^ d, 0xCA62C1D6)
      sha1Rounds w (i + 1) (rotl32 a 5 + f + e + kc + w.getD i 0) a (rotl32 b 30) c d k
private def sha1Blocks (padded : ByteArray) (off : Nat) (h0 h1 h2 h3 h4 : UInt32) : Nat → UInt32 × UInt32 × UInt32 × UInt32 × UInt32
  | 0 => (h0, h1, h2, h3, h4)
  | k + 1 =>
      let (a, b, c, d, e) := sha1Rounds (sha1Expand ((Array.range 16).map fun i => UInt32.ofNat ((readU32BE padded (off + i * 4)).getD 0)) 16 64) 0 h0 h1 h2 h3 h4 80
      sha1Blocks padded (off + 64) (h0 + a) (h1 + b) (h2 + c) (h3 + d) (h4 + e) k
def sha1 (msg : ByteArray) : ByteArray :=
  let (bitLen, rem) : UInt64 × Nat := ((UInt64.ofNat msg.size) * 8, (msg.size + 1) % 64)
  let padded := pushU32BE (pushU32BE (ByteArray.mk (msg.data.push 0x80 ++ Array.replicate (if rem <= 56 then 56 - rem else 120 - rem) 0)) (bitLen >>> 32).toNat) bitLen.toNat
  let (h0, h1, h2, h3, h4) := sha1Blocks padded 0 0x67452301 0xEFCDAB89 0x98BADCFE 0x10325476 0xC3D2E1F0 (padded.size / 64)
  pushU32BE (pushU32BE (pushU32BE (pushU32BE (pushU32BE ByteArray.empty h0.toNat) h1.toNat) h2.toNat) h3.toNat) h4.toNat
def wsComputeAccept (secKey : String) : Option String :=
  let k := trimOws secKey
  if k.isEmpty || k.utf8ByteSize > 64 || hasCtlOrCrlf k false || k.contains ' ' then none else some (base64Encode (sha1 (k ++ "258EAFA5-E914-47DA-95CA-C5AB0DC85B11").toUTF8))
theorem sha1_size (msg : ByteArray) : (sha1 msg).size = 20 := by unfold sha1; simp only [pushU32BE, pushU16BE, ByteArray.size_push]; rfl
theorem base64Encode_rfc6455_accept : base64Encode (ByteArray.mk #[0xb3,0x7a,0x4f,0x2c,0xc0,0x62,0x4f,0x16,0x90,0xf6,0x46,0x06,0xcf,0x38,0x59,0x45,0xb2,0xbe,0xc4,0xea]) = "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=" := rfl

inductive WsFrameStep where | needMore | frame (fin : Bool) (opcode : UInt8) (payload : ByteArray) (consumed : Nat) | protocolErr (closeCode : UInt16)
private def unmaskPayload (buf : ByteArray) (dataOff plen : Nat) (hbound : dataOff + plen ≤ buf.size) (m0 m1 m2 m3 : UInt8) : ByteArray :=
  if plen == 0 then ByteArray.empty
  else
    let rec go (idx : Nat) (a b c d : UInt8) (out : ByteArray) : ByteArray := if _ : idx < dataOff + plen then go (idx + 1) b c d a (out.push ((buf[idx]'(by omega)) ^^^ a)) else out
    termination_by dataOff + plen - idx; go dataOff m0 m1 m2 m3 (ByteArray.emptyWithCapacity plen)
def decodeWsFrame (buf : ByteArray) (offset : Nat) (maxMsgBytes : Nat := maxWsMsgBytes) : WsFrameStep :=
  if h2 : offset + 2 ≤ buf.size then
    let (b0, b1) := (buf[offset]'(by omega), buf[offset + 1]'(by omega)); let (fin, opcode) := ((b0 &&& 0x80) != 0, b0 &&& 0x0F)
    if ((b0 >>> 4) &&& 0x07) != 0 || (b1 &&& 0x80) == 0 then .protocolErr 1002
    else
      let len7 := (b1 &&& 0x7F).toNat
      let hdr? : Option (Except UInt16 (Nat × Nat)) :=
        if len7 < 126 then some (.ok (2, len7))
        else if len7 == 126 then (readU16BE buf (offset + 2)).map fun p => .ok (4, p)
        else match readU32BE buf (offset + 2), readU32BE buf (offset + 6) with
          | some hi, some lo => if (hi &&& 0x80000000) != 0 then some (.error 1002) else some (.ok (10, (hi <<< 32) ||| lo)) | _, _ => none
      match hdr? with
      | none => .needMore | some (.error code) => .protocolErr code
      | some (.ok (hdrLen, plen)) =>
          if opcode >= 0x08 && (plen > 125 || !fin) then .protocolErr 1002 else if plen > maxMsgBytes then .protocolErr 1009
          else if htot : offset + (hdrLen + 4 + plen) ≤ buf.size then
            let m := offset + hdrLen
            .frame fin opcode (unmaskPayload buf (m + 4) plen (by omega) (buf[m]'(by omega)) (buf[m + 1]'(by omega)) (buf[m + 2]'(by omega)) (buf[m + 3]'(by omega))) (hdrLen + 4 + plen)
          else .needMore
  else .needMore
def encodeWsFrame (opcode : UInt8) (payload : ByteArray) : ByteArray :=
  let (b0, n) : UInt8 × Nat := (0x80 ||| (opcode &&& 0x0F), payload.size)
  let mk (hdr : Nat) (b1 : UInt8) := ((ByteArray.emptyWithCapacity (hdr + n)).push b0).push b1
  let out := if n < 126 then mk 2 (UInt8.ofNat n) else if n ≤ 65535 then pushU16BE (mk 4 126) n else pushU32BE (pushU32BE (mk 10 127) (n >>> 32)) n
  if n == 0 then out else appendByteSlice out payload
def encodeWsCloseFrame (code : UInt16) : ByteArray := encodeWsFrame 0x08 (pushU16BE ByteArray.empty code.toNat)
theorem decodeWsFrame_rejects_unmasked (b0 b1 : UInt8) (rest : Array UInt8) (hunmasked : (b1 &&& 0x80) = 0) :
    decodeWsFrame (ByteArray.mk (#[b0, b1] ++ rest)) 0 = .protocolErr 1002 := by simp only [decodeWsFrame, ByteArray.getElem_eq_getElem_data]; simp [ByteArray.size, -ByteArray.size_data, hunmasked]
theorem decodeWsFrame_rejects_rsv (b0 b1 : UInt8) (rest : Array UInt8) (hrsv : ((b0 >>> 4) &&& 0x07) ≠ 0) :
    decodeWsFrame (ByteArray.mk (#[b0, b1] ++ rest)) 0 = .protocolErr 1002 := by simp only [decodeWsFrame, ByteArray.getElem_eq_getElem_data]; simp [ByteArray.size, -ByteArray.size_data, hrsv]
end Qed.Server.Http
