import Qed.Server.Net

namespace Qed.Server.Http

open Qed.Server.Net

/-! ## Protocol Limits -/

def maxReqHdrBytes  : Nat := 65536
def maxReqBodyBytes : Nat := 32 * 1024 * 1024
def maxReqHeaders   : Nat := 96
def maxWsMsgBytes   : Nat := 4 * 1024 * 1024

/-! ## Inbound HTTP/1.1 Request Head Parser -/

structure ParsedReqHead where
  method         : String
  target         : String
  isHttp11       : Bool
  keepAlive      : Bool
  contentLen     : Nat
  headers        : Array (String × String)
  upgrade?       : Option String
  conn?          : Option String
  wsKey?         : Option String
  wsVer?         : Option String
  host?          : Option String := none
  origin?        : Option String := none
  dupOrigin      : Bool := false
  secFetchSite?  : Option String := none
  dupSfs         : Bool := false
  contentType?   : Option String := none
  dupCt          : Bool := false
  hasCookie      : Bool := false
  auth?          : Option String := none
  hasIfNoneMatch : Bool := false
  acceptsGzip    : Bool := false

private structure HdrFoldState where
  keepAlive      : Bool
  contentLen?    : Option Nat
  hostCount      : Nat
  headers        : Array (String × String)
  upgrade?       : Option String
  conn?          : Option String
  wsKey?         : Option String
  wsVer?         : Option String
  host?          : Option String := none
  origin?        : Option String := none
  dupOrigin      : Bool := false
  secFetchSite?  : Option String := none
  dupSfs         : Bool := false
  contentType?   : Option String := none
  dupCt          : Bool := false
  hasCookie      : Bool := false
  auth?          : Option String := none
  hasIfNoneMatch : Bool := false
  acceptsGzip    : Bool := false

@[inline] private def isHostHeader (k : String) : Bool :=
  k.utf8ByteSize == 4 && (k == "Host" || k == "host" || k.toLower == "host")

private theorem isHostHeader_imp_toLower (k : String) (h : isHostHeader k = true) :
    (k.toLower == "host") = true := by
  unfold isHostHeader at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  rcases h.2 with (h1 | h2) | h3
  · rw [beq_iff_eq.1 h1]
    have : "Host".toLower = "host" := by
      unfold String.toLower; apply String.ext; simp [Char.toLower]; decide
    simp [this]
  · rw [beq_iff_eq.1 h2]
    have : "host".toLower = "host" := by
      unfold String.toLower; apply String.ext; simp [Char.toLower]
    simp [this]
  · exact h3

private def acceptEncodingHasGzip (v : String) : Bool :=
  (v.splitOn ",").any fun item =>
    match item.splitOn ";" with
    | [] => false
    | tok :: params =>
        if !eqCI (trimWs tok) "gzip" then false
        else
          !(params.any fun p =>
            match p.splitOn "=" with
            | [k, qv] =>
                let lk := (trimWs k).toLower
                let lq := trimWs qv
                lk == "q" && (lq == "0" || lq == "0.0" || lq == "0.00" || lq == "0.000")
            | _ => false)

private def parseOtherHeader (k v : String) (st : HdrFoldState) : HdrFoldState :=
  let headers := st.headers.push (k, v)
  match k.utf8ByteSize with
  | 6 =>
      if eqCI k "origin" then
        if st.origin?.isSome then { st with headers, dupOrigin := true }
        else { st with headers, origin? := some v }
      else if eqCI k "cookie" then { st with headers, hasCookie := true }
      else { st with headers }
  | 7 =>
      if eqCI k "upgrade" then { st with headers, upgrade? := some v } else { st with headers }
  | 10 =>
      if eqCI k "connection" then
        let keepAlive :=
          if containsCI v "close" then false
          else if containsCI v "keep-alive" then true
          else st.keepAlive
        { st with headers, keepAlive, conn? := some v }
      else { st with headers }
  | 12 =>
      if eqCI k "content-type" then
        if st.contentType?.isSome then { st with headers, dupCt := true }
        else { st with headers, contentType? := some v }
      else { st with headers }
  | 13 =>
      if eqCI k "authorization" then
        if st.auth?.isNone then { st with headers, auth? := some v } else { st with headers }
      else if eqCI k "if-none-match" then { st with headers, hasIfNoneMatch := true }
      else { st with headers }
  | 14 =>
      if eqCI k "sec-fetch-site" then
        if st.secFetchSite?.isSome then { st with headers, dupSfs := true }
        else { st with headers, secFetchSite? := some v }
      else { st with headers }
  | 15 =>
      if eqCI k "accept-encoding" && acceptEncodingHasGzip v then
        { st with headers, acceptsGzip := true }
      else { st with headers }
  | 17 =>
      if eqCI k "sec-websocket-key" then { st with headers, wsKey? := some v } else { st with headers }
  | 21 =>
      if eqCI k "sec-websocket-version" then { st with headers, wsVer? := some v } else { st with headers }
  | _ => { st with headers }

private theorem parseOtherHeader_invariants (k v : String) (st : HdrFoldState) :
    (parseOtherHeader k v st).contentLen? = st.contentLen? ∧
    (parseOtherHeader k v st).hostCount = st.hostCount ∧
    (parseOtherHeader k v st).headers = st.headers.push (k, v) := by
  unfold parseOtherHeader
  dsimp only
  split <;> repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

def parseOneHeaderLine (line : String) (st : HdrFoldState) :
    Except (Nat × String) HdrFoldState :=
  match splitHeaderKv line with
  | none => .error (400, "malformed header")
  | some (k, v) =>
      if !isValidHttpToken k then
        .error (400, "invalid header name")
      else if eqCI k "transfer-encoding" then
        .error (501, "Transfer-Encoding not supported")
      else if st.headers.size >= maxReqHeaders then
        .error (431, "too many headers")
      else if isHostHeader k then
        if v.isEmpty || hasCtlOrCrlf v false then
          .error (400, "invalid Host header")
        else if st.hostCount >= 1 then
          .error (400, "duplicate Host header")
        else
          .ok { st with hostCount := st.hostCount + 1, host? := some v, headers := st.headers.push (k, v) }
      else if eqCI k "content-length" then
        match parseStrictU64 v 18446744073709551615 with
        | none => .error (400, "invalid Content-Length")
        | some cl =>
            match st.contentLen? with
            | some prev =>
                if prev ≠ cl then .error (400, "conflicting Content-Length headers")
                else if cl > maxReqBodyBytes then .error (413, "payload too large")
                else .ok { st with headers := st.headers.push (k, v) }
            | none =>
                if cl > maxReqBodyBytes then .error (413, "payload too large")
                else .ok { st with contentLen? := some cl, headers := st.headers.push (k, v) }
      else
        .ok (parseOtherHeader k v st)

private def parseHdrLines (lines : Array String) (idx : Nat) (st : HdrFoldState) :
    Except (Nat × String) HdrFoldState :=
  if h : idx < lines.size then
    match parseOneHeaderLine lines[idx] st with
    | .error e => .error e
    | .ok st'  => parseHdrLines lines (idx + 1) st'
  else
    .ok st
termination_by lines.size - idx

@[inline] private def eqBytesAt (s : String) (off : Nat) (lit : String) : Bool :=
  if off + lit.utf8ByteSize > s.utf8ByteSize then false
  else
    let rec go (k : Nat) : Bool :=
      if hk : k < lit.utf8ByteSize then
        if hs : off + k < s.utf8ByteSize then
          if s.getUTF8Byte ⟨off + k⟩ hs == lit.getUTF8Byte ⟨k⟩ hk then go (k + 1) else false
        else false
      else true
    termination_by lit.utf8ByteSize - k
    go 0

private def parseReqLine (line : String) : Except (Nat × String) (String × String × Bool) :=
  match findByte line 0 32 with
  | none => .error (400, "malformed request line")
  | some sp1 =>
      match findByte line (sp1 + 1) 32 with
      | none => .error (400, "malformed request line")
      | some sp2 =>
          if (findByte line (sp2 + 1) 32).isSome then .error (400, "malformed request line")
          else
            let verStart := sp2 + 1
            let isHttp11 := line.utf8ByteSize - verStart == 8 && eqBytesAt line verStart "HTTP/1.1"
            let isHttp10 := !isHttp11 && line.utf8ByteSize - verStart == 8 && eqBytesAt line verStart "HTTP/1.0"
            if !isHttp11 && !isHttp10 then .error (400, "unsupported HTTP version")
            else if sp1 == 0 || sp2 <= sp1 + 1 then .error (400, "malformed request line")
            else
              let target :=
                if sp2 == sp1 + 2 && eqBytesAt line (sp1 + 1) "/" then "/"
                else String.Pos.Raw.extract line ⟨sp1 + 1⟩ ⟨sp2⟩
              if sp1 == 3 && eqBytesAt line 0 "GET" then .ok ("GET", target, isHttp11)
              else if sp1 == 4 && eqBytesAt line 0 "POST" then .ok ("POST", target, isHttp11)
              else
                let method := String.Pos.Raw.extract line ⟨0⟩ ⟨sp1⟩
                if !isValidHttpToken method then .error (400, "malformed request line")
                else .ok (method, target, isHttp11)

/-- Strict RFC 9112 inbound HTTP/1.1 request header parser (bytes before `\r\n\r\n`).
    Rejects NUL bytes, bare CR/LF, invalid UTF-8, invalid header token names (whitespace before
    `:`), missing/duplicate `Host` on HTTP/1.1 (400), `Transfer-Encoding` (501), conflicting or
    oversized `Content-Length` (400/413), and >96 headers (431). -/
def parseRequestHead (headBytes : ByteArray) : Except (Nat × String) ParsedReqHead :=
  if headBytes.size > maxReqHdrBytes then
    .error (431, "request headers too large")
  else
    match splitCrlfLines headBytes with
    | .error e => .error (400, e)
    | .ok lines =>
        if h0 : lines.size = 0 then
          .error (400, "malformed request line")
        else
          match parseReqLine (lines[0]'(by omega)) with
          | .error e => .error e
          | .ok (method, target, isHttp11) =>
              let initSt : HdrFoldState := {
                keepAlive := isHttp11, contentLen? := none, hostCount := 0, headers := Array.mkEmpty 12,
                upgrade? := none, conn? := none, wsKey? := none, wsVer? := none
              }
              match parseHdrLines lines 1 initSt with
              | .error e => .error e
              | .ok st =>
                  if isHttp11 && st.hostCount != 1 then
                    .error (400, "missing Host header")
                  else
                    .ok {
                      method, target, isHttp11
                      keepAlive      := st.keepAlive
                      contentLen     := st.contentLen?.getD 0
                      headers        := st.headers
                      upgrade?       := st.upgrade?
                      conn?          := st.conn?
                      wsKey?         := st.wsKey?
                      wsVer?         := st.wsVer?
                      host?          := st.host?
                      origin?        := st.origin?
                      dupOrigin      := st.dupOrigin
                      secFetchSite?  := st.secFetchSite?
                      dupSfs         := st.dupSfs
                      contentType?   := st.contentType?
                      dupCt          := st.dupCt
                      hasCookie      := st.hasCookie
                      auth?          := st.auth?
                      hasIfNoneMatch := st.hasIfNoneMatch
                      acceptsGzip    := st.acceptsGzip
                    }

theorem parseRequestHead_rejects_nul (headBytes : ByteArray)
    (hnul : byteArrayContains headBytes 0 = true) :
    ∃ e, parseRequestHead headBytes = .error e := by
  unfold parseRequestHead
  by_cases hsz : headBytes.size > maxReqHdrBytes
  · exact ⟨(431, "request headers too large"), by simp [hsz]⟩
  · rcases splitCrlfLines_rejects_nul headBytes hnul with ⟨errMsg, hsplit⟩
    exact ⟨(400, errMsg), by simp [hsz, hsplit]⟩

theorem parseOneHeaderLine_rejects_bad_name (line k v : String) (st : HdrFoldState)
    (hkv : splitHeaderKv line = some (k, v)) (hbad : isValidHttpToken k = false) :
    parseOneHeaderLine line st = .error (400, "invalid header name") := by
  unfold parseOneHeaderLine
  simp [hkv, hbad]

private theorem parseOneHeaderLine_ok_spec (line : String) (st st' : HdrFoldState)
    (hok : parseOneHeaderLine line st = .ok st') :
    ((∀ cl, st.contentLen? = some cl → cl ≤ maxReqBodyBytes) →
      ∀ cl, st'.contentLen? = some cl → cl ≤ maxReqBodyBytes) ∧
    (st'.hostCount = st.hostCount ∨
      (st'.hostCount = st.hostCount + 1 ∧ ∃ k v, (k, v) ∈ st'.headers.toList ∧ k.toLower == "host")) ∧
    (∀ p ∈ st.headers.toList, p ∈ st'.headers.toList) := by
  unfold parseOneHeaderLine at hok
  cases hs : splitHeaderKv line with
  | none => simp [hs] at hok
  | some kv =>
      simp only [hs] at hok
      by_cases htok : isValidHttpToken kv.1
      · simp only [htok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        by_cases hte : eqCI kv.1 "transfer-encoding"
        · simp [hte] at hok
        · by_cases hmax : st.headers.size >= maxReqHeaders
          · simp [hte, hmax] at hok
          · by_cases hhost : isHostHeader kv.1
            · simp only [hte, hmax, hhost, ↓reduceIte, Bool.false_eq_true] at hok
              split at hok
              · cases hok
              · split at hok
                · cases hok
                · simp only [Except.ok.injEq] at hok; subst hok
                  refine ⟨id, Or.inr ⟨rfl, kv.1, kv.2, ?_, isHostHeader_imp_toLower kv.1 hhost⟩, ?_⟩
                  · simp [Array.toList_push]
                  · intro p hp; simp [Array.toList_push, hp]
            · by_cases hcl : eqCI kv.1 "content-length"
              · simp only [hte, hmax, hhost, hcl, ↓reduceIte, Bool.false_eq_true] at hok
                cases hp : parseStrictU64 kv.2 18446744073709551615 with
                | none => simp [hp] at hok
                | some cl =>
                    simp only [hp] at hok
                    cases hprev : st.contentLen? with
                    | some prev =>
                        simp only [hprev] at hok
                        by_cases hne : prev ≠ cl
                        · simp [hne] at hok
                        · by_cases hbig : maxReqBodyBytes < cl
                          · simp [hne, hbig] at hok
                          · simp only [hne, hbig, ↓reduceIte, Except.ok.injEq] at hok
                            subst hok
                            refine ⟨fun hinit c hc => hinit c hc, Or.inl rfl, ?_⟩
                            intro p hp; simp [Array.toList_push, hp]
                    | none =>
                        simp only [hprev] at hok
                        by_cases hbig : maxReqBodyBytes < cl
                        · simp [hbig] at hok
                        · simp only [hbig, ↓reduceIte, Except.ok.injEq] at hok
                          subst hok
                          refine ⟨fun _ c hc => by simp only [Option.some.injEq] at hc; omega, Or.inl rfl, ?_⟩
                          intro p hp; simp [Array.toList_push, hp]
              · simp only [hte, hmax, hhost, hcl, ↓reduceIte, Bool.false_eq_true, Except.ok.injEq] at hok
                subst hok
                have hinv := parseOtherHeader_invariants kv.1 kv.2 st
                refine ⟨fun hinit => by rw [hinv.1]; exact hinit, Or.inl hinv.2.1, ?_⟩
                rw [hinv.2.2]
                intro p hp; simp [Array.toList_push, hp]
      · simp [htok] at hok

private theorem parseHdrLines_inv (P : HdrFoldState → Prop)
    (hstep : ∀ line st st', P st → parseOneHeaderLine line st = .ok st' → P st')
    (lines : Array String) (idx : Nat) (st st' : HdrFoldState)
    (hinit : P st) (hok : parseHdrLines lines idx st = .ok st') : P st' := by
  unfold parseHdrLines at hok
  split at hok
  · cases h1 : parseOneHeaderLine lines[idx] st with
    | error e => simp [h1] at hok
    | ok stMid =>
        simp only [h1] at hok
        exact parseHdrLines_inv P hstep lines (idx + 1) stMid st' (hstep lines[idx] st stMid hinit h1) hok
  · simp only [Except.ok.injEq] at hok
    subst hok; exact hinit
termination_by lines.size - idx

private theorem parseRequestHead_ok_elim (headBytes : ByteArray) (req : ParsedReqHead)
    (hok : parseRequestHead headBytes = .ok req) :
    ∃ (lines : Array String) (st : HdrFoldState),
      let initSt : HdrFoldState := {
        keepAlive := req.isHttp11, contentLen? := none, hostCount := 0, headers := Array.mkEmpty 12,
        upgrade? := none, conn? := none, wsKey? := none, wsVer? := none
      }
      parseHdrLines lines 1 initSt = .ok st ∧
      (req.isHttp11 = true → st.hostCount = 1) ∧
      req.contentLen = st.contentLen?.getD 0 ∧
      req.headers = st.headers := by
  unfold parseRequestHead at hok
  by_cases hsz : headBytes.size > maxReqHdrBytes
  · simp [hsz] at hok
  · simp only [hsz, ↓reduceIte] at hok
    cases hsp : splitCrlfLines headBytes with
    | error e => simp [hsp] at hok
    | ok lines =>
        simp only [hsp] at hok
        by_cases h0 : lines.size = 0
        · simp [h0] at hok
        · simp only [h0, ↓reduceDIte] at hok
          cases hreq : parseReqLine (lines[0]'(by omega)) with
          | error e => simp [hreq] at hok
          | ok mti =>
              rcases mti with ⟨m, t, is11⟩
              simp only [hreq] at hok
              let initSt : HdrFoldState := {
                keepAlive := is11, contentLen? := none, hostCount := 0, headers := Array.mkEmpty 12,
                upgrade? := none, conn? := none, wsKey? := none, wsVer? := none
              }
              cases hfold : parseHdrLines lines 1 initSt with
              | error e => simp only [initSt, hfold] at hok; cases hok
              | ok st =>
                  simp only [initSt, hfold] at hok
                  by_cases hmiss : (is11 && st.hostCount != 1) = true
                  · simp [hmiss] at hok
                  · simp only [hmiss, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hok
                    subst hok
                    refine ⟨lines, st, hfold, ?_, rfl, rfl⟩
                    intro h11; simp at hmiss; exact hmiss h11

theorem parseRequestHead_http11_has_host (headBytes : ByteArray) (req : ParsedReqHead)
    (hok : parseRequestHead headBytes = .ok req) (h11 : req.isHttp11 = true) :
    ∃ k v, (k, v) ∈ req.headers.toList ∧ k.toLower == "host" := by
  rcases parseRequestHead_ok_elim headBytes req hok with ⟨lines, st, hfold, hhost, _, hhdrs⟩
  rw [hhdrs]
  refine parseHdrLines_inv
    (fun s => s.hostCount > 0 → ∃ k v, (k, v) ∈ s.headers.toList ∧ k.toLower == "host")
    (fun line s s' hinv hstep hpos => ?_)
    lines 1 _ st (by intro h; simp at h) hfold (by have := hhost h11; omega)
  have ⟨_, hhc, hmono⟩ := parseOneHeaderLine_ok_spec line s s' hstep
  rcases hhc with heq | ⟨_, k, v, hmem, hk⟩
  · rw [heq] at hpos
    rcases hinv hpos with ⟨k, v, hmem, hk⟩
    exact ⟨k, v, hmono _ hmem, hk⟩
  · exact ⟨k, v, hmem, hk⟩

theorem parseRequestHead_contentLen_le (headBytes : ByteArray) (req : ParsedReqHead)
    (hok : parseRequestHead headBytes = .ok req) :
    req.contentLen ≤ maxReqBodyBytes := by
  rcases parseRequestHead_ok_elim headBytes req hok with ⟨lines, st, hfold, _, hcl, _⟩
  rw [hcl]
  have hb := parseHdrLines_inv
    (fun s => ∀ cl, s.contentLen? = some cl → cl ≤ maxReqBodyBytes)
    (fun line s s' hinv hstep => (parseOneHeaderLine_ok_spec line s s' hstep).1 hinv)
    lines 1 _ st (by intro _ h; cases h) hfold
  cases hc : st.contentLen? with
  | none => simp [maxReqBodyBytes]
  | some cl => simpa [hc] using hb cl hc

/-! ## HTTP/1.1 Response Formatting -/

def statusReason (code : Nat) : String :=
  match code with
  | 200 => "OK"
  | 201 => "Created"
  | 204 => "No Content"
  | 301 => "Moved Permanently"
  | 302 => "Found"
  | 304 => "Not Modified"
  | 400 => "Bad Request"
  | 401 => "Unauthorized"
  | 403 => "Forbidden"
  | 404 => "Not Found"
  | 405 => "Method Not Allowed"
  | 413 => "Payload Too Large"
  | 415 => "Unsupported Media Type"
  | 429 => "Too Many Requests"
  | 431 => "Request Header Fields Too Large"
  | 500 => "Internal Server Error"
  | 501 => "Not Implemented"
  | 503 => "Service Unavailable"
  | _   => "OK"

def safeContentType (ct : String) : String :=
  if hasCtlOrCrlf ct false then "application/octet-stream" else ct

theorem safeContentType_no_crlf (ct : String) :
    hasCtlOrCrlf (safeContentType ct) false = false := by
  unfold safeContentType
  split
  · decide
  · rename_i h; simpa using h

/-- Default strict Content-Security-Policy enabled on HTML responses because Qed statically proves
    zero inline `<script>` tags and zero inline `on*` event handler attributes. -/
def defaultCsp : String :=
  "default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline'; object-src 'none'; base-uri 'self'; frame-ancestors 'none'"

/-- True iff `mime` is a text/script/markup/JSON/SVG media type eligible for gzip compression. -/
def isCompressibleMime (mime : String) : Bool :=
  startsWithCI mime "text/" ||
  startsWithCI mime "application/javascript" ||
  startsWithCI mime "application/json" ||
  startsWithCI mime "application/manifest+json" ||
  startsWithCI mime "application/xml" ||
  startsWithCI mime "image/svg+xml"

private def renderExtraHeaders (extraHeaders : List (String × String)) : String :=
  extraHeaders.foldl (init := "") fun acc (k, v) =>
    if isValidHttpToken k && !hasCtlOrCrlf v false then
      acc ++ k ++ ": " ++ v ++ "\r\n"
    else acc

def formatHttpResponseHead (status : Nat) (contentType : String) (contentLen : Nat)
    (keepAlive noStore : Bool) (etag? : Option String := none)
    (cacheControl? : Option String := none)
    (extraHeaders : List (String × String) := []) : ByteArray :=
  let code := if status >= 100 && status <= 599 then status else 500
  let ct := safeContentType contentType
  let conn := if keepAlive then "keep-alive" else "close"
  let cache := match cacheControl? with
    | some cc => if hasCtlOrCrlf cc false then "" else s!"Cache-Control: {cc}\r\n"
    | none    => if noStore then "Cache-Control: no-store\r\n" else ""
  let etag := match etag? with
    | some et => if hasCtlOrCrlf et false then "" else s!"ETag: {et}\r\n"
    | none    => ""
  let extra := renderExtraHeaders extraHeaders
  (s!"HTTP/1.1 {code} {statusReason code}\r\n" ++
   s!"Content-Type: {ct}\r\n" ++
   s!"Content-Length: {contentLen}\r\n" ++
   "X-Content-Type-Options: nosniff\r\n" ++
   etag ++
   cache ++
   extra ++
   s!"Connection: {conn}\r\n\r\n").toUTF8

def formatNotModifiedResponse (etag : String) (keepAlive : Bool) : ByteArray :=
  let conn := if keepAlive then "keep-alive" else "close"
  let etagLine := if hasCtlOrCrlf etag false then "" else s!"ETag: {etag}\r\n"
  ("HTTP/1.1 304 Not Modified\r\n" ++
   "X-Content-Type-Options: nosniff\r\n" ++
   etagLine ++
   "Cache-Control: public, max-age=0, must-revalidate\r\n" ++
   s!"Connection: {conn}\r\n\r\n").toUTF8

private def stripWeakPrefix (s : String) : String :=
  let t := trimOws s
  if t.startsWith "W/" then String.ofList (t.toList.drop 2) else t

/-- RFC 9110 §13.1.2 weak ETag comparison against all `If-None-Match` request headers. -/
def etagMatchesIfNoneMatch (headers : Array (String × String)) (etag : String) : Bool :=
  let target := stripWeakPrefix etag
  headers.any fun (k, v) =>
    if k.toLower != "if-none-match" then false
    else
      (v.splitOn ",").any fun item =>
        let t := trimOws item
        t == "*" || stripWeakPrefix t == target

def formatHttpResponse (status : Nat) (contentType : String) (body : ByteArray)
    (headOnly keepAlive noStore : Bool) (etag? : Option String := none)
    (cacheControl? : Option String := none)
    (extraHeaders : List (String × String) := []) : ByteArray :=
  let head := formatHttpResponseHead status contentType body.size keepAlive noStore etag? cacheControl? extraHeaders
  if headOnly then head else head ++ body

private def okProtoHeadPrefix : ByteArray :=
  "HTTP/1.1 200 OK\r\nContent-Type: application/x-protobuf\r\nContent-Length: ".toUTF8

private def okHtmlHeadPrefix : ByteArray :=
  "HTTP/1.1 200 OK\r\nContent-Type: text/html; charset=utf-8\r\nContent-Length: ".toUTF8

private def okHeadTailKA : ByteArray :=
  "\r\nX-Content-Type-Options: nosniff\r\nConnection: keep-alive\r\n\r\n".toUTF8

private def okHeadTailClose : ByteArray :=
  "\r\nX-Content-Type-Options: nosniff\r\nConnection: close\r\n\r\n".toUTF8

@[inline] private def appendByteSlice (dst src : ByteArray) : ByteArray :=
  src.copySlice 0 dst dst.size src.size false

private def pushNatAsciiBytes (buf : ByteArray) (n : Nat) : ByteArray :=
  if n < 10 then buf.push (UInt8.ofNat (48 + n))
  else if n < 100 then
    (buf.push (UInt8.ofNat (48 + n / 10))).push (UInt8.ofNat (48 + n % 10))
  else if n < 1000 then
    ((buf.push (UInt8.ofNat (48 + n / 100))).push (UInt8.ofNat (48 + (n / 10) % 10))).push (UInt8.ofNat (48 + n % 10))
  else if n < 10000 then
    (((buf.push (UInt8.ofNat (48 + n / 1000))).push (UInt8.ofNat (48 + (n / 100) % 10))).push
      (UInt8.ofNat (48 + (n / 10) % 10))).push (UInt8.ofNat (48 + n % 10))
  else
    appendByteSlice buf (toString n).toUTF8

/-- Single-allocation HTTP/1.1 `200 OK` response builder for pre-validated static content types. -/
private def formatFast200 (headPrefix body : ByteArray) (headOnly keepAlive : Bool) : ByteArray :=
  let tail := if keepAlive then okHeadTailKA else okHeadTailClose
  let cap := headPrefix.size + 10 + tail.size + (if headOnly then 0 else body.size)
  let out := ByteArray.emptyWithCapacity cap
  let out := appendByteSlice out headPrefix
  let out := pushNatAsciiBytes out body.size
  let out := appendByteSlice out tail
  if headOnly then out else appendByteSlice out body

def formatOkProtoResponse (body : ByteArray) (headOnly keepAlive : Bool) : ByteArray :=
  formatFast200 okProtoHeadPrefix body headOnly keepAlive

def formatOkHtmlResponse (body : ByteArray) (headOnly keepAlive : Bool) : ByteArray :=
  formatFast200 okHtmlHeadPrefix body headOnly keepAlive

def formatErrorResponse (status : Nat) (msg : String) : ByteArray :=
  formatHttpResponse status "text/plain; charset=utf-8" msg.toUTF8 false false false

def formatWsUpgradeResponse (acceptB64 : String) : ByteArray :=
  (s!"HTTP/1.1 101 Switching Protocols\r\n" ++
   s!"Upgrade: websocket\r\n" ++
   s!"Connection: Upgrade\r\n" ++
   s!"Sec-WebSocket-Accept: {acceptB64}\r\n\r\n").toUTF8

/-! ## Static Asset Path & MIME Policy -/

structure StaticTarget where
  relPath   : String
  mime      : String
  isHead    : Bool
  noStore   : Bool
  isBuildId : Bool
deriving Repr, DecidableEq

def guessMimeType (path : String) : Option String :=
  match (path.splitOn ".").reverse with
  | ext :: _ :: _ =>
      match ext.toLower with
      | "mjs" | "js"  => some "text/javascript; charset=utf-8"
      | "css"         => some "text/css; charset=utf-8"
      | "html"        => some "text/html; charset=utf-8"
      | "json" | "map" => some "application/json; charset=utf-8"
      | "webmanifest" => some "application/manifest+json; charset=utf-8"
      | "xml"         => some "application/xml; charset=utf-8"
      | "pdf"         => some "application/pdf"
      | "svg"         => some "image/svg+xml"
      | "png"         => some "image/png"
      | "jpg" | "jpeg" => some "image/jpeg"
      | "gif"         => some "image/gif"
      | "webp"        => some "image/webp"
      | "avif"        => some "image/avif"
      | "ico"         => some "image/x-icon"
      | "wasm"        => some "application/wasm"
      | "woff2"       => some "font/woff2"
      | "woff"        => some "font/woff"
      | "ttf"         => some "font/ttf"
      | "otf"         => some "font/otf"
      | "mp4"         => some "video/mp4"
      | "webm"        => some "video/webm"
      | "mp3"         => some "audio/mpeg"
      | "ogg"         => some "audio/ogg"
      | "txt"         => some "text/plain; charset=utf-8"
      | _             => none
  | _ => none

def classifyStaticPath (method target : String) (devMode : Bool) : Option StaticTarget :=
  let isHead := method == "HEAD"
  if method != "GET" && !isHead then none
  else if target == "/" || ((findByte target 0 46).isNone && !(devMode && (target == "/__build_id" || target == "/__dev_status"))) then none
  else
    let pathOnly := (target.splitOn "?").headD target
    if pathOnly.isEmpty || pathOnly.utf8ByteSize >= 2048 || !pathOnly.startsWith "/" ||
       pathOnly.contains '\\' || pathOnly.contains '\x00' ||
       pathOnly.startsWith "/_qed/" || (pathOnly.splitOn "..").length > 1 then
      none
    else
      let relPath := String.ofList (pathOnly.toList.drop 1)
      if relPath.isEmpty || relPath.startsWith "/" then none
      else if devMode && pathOnly == "/__build_id" then
        some { relPath, mime := "text/plain; charset=utf-8", isHead, noStore := true, isBuildId := true }
      else if devMode && pathOnly == "/__dev_status" then
        some { relPath, mime := "application/json; charset=utf-8", isHead, noStore := true, isBuildId := true }
      else
        match guessMimeType pathOnly with
        | some mime => some { relPath, mime, isHead, noStore := devMode, isBuildId := false }
        | none      => none

private def isLowerHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

private def splitCharList (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
      let rest := splitCharList sep cs
      if c == sep then [] :: rest
      else match rest with
        | [] => [[c]]
        | h :: t => (c :: h) :: t

private def isHashedExt : List Char → Bool
  | ['m', 'j', 's'] | ['M', 'J', 'S']
  | ['j', 's']      | ['J', 'S']
  | ['c', 's', 's'] | ['C', 'S', 'S'] => true
  | _ => false

/-- True iff `relPath` has a content-hashed JS/CSS filename (`<stem>.<8..16 hex>.(mjs|js|css)`),
    eligible for `Cache-Control: public, max-age=31536000, immutable`. -/
def isContentHashedAsset (relPath : String) : Bool :=
  let base := match (splitCharList '/' relPath.toList).reverse with | b :: _ => b | [] => relPath.toList
  match (splitCharList '.' base).reverse with
  | ext :: hash :: stem :: _ =>
      !stem.isEmpty && isHashedExt ext &&
      hash.length >= 8 && hash.length <= 16 && hash.all isLowerHexChar
  | _ => false

theorem isContentHashedAsset_hashed :
    isContentHashedAsset "app.0123456789ab.mjs" = true := by rfl

theorem isContentHashedAsset_plain :
    isContentHashedAsset "app.mjs" = false := by rfl

theorem classifyStaticPath_rejects_dotdot (method target : String) (devMode : Bool)
    (h : (((target.splitOn "?").headD target).splitOn "..").length > 1) :
    classifyStaticPath method target devMode = none := by
  unfold classifyStaticPath
  by_cases hm : method != "GET" && !(method == "HEAD")
  · simp [hm]
  · simp only [hm, ↓reduceIte, Bool.false_eq_true]
    split
    · rfl
    · have hgt : 1 < (((target.splitOn "?").headD target).splitOn "..").length := h
      simp only [List.headD_eq_head?_getD] at hgt
      simp; intro _ _ _ _ _ _ hle; omega

/-! ## Pure Total SHA-1 & RFC 6455 `Sec-WebSocket-Accept` -/

private def rotl32 (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

private def beU32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32

private def pushBeU32Arr (out : Array UInt8) (v : UInt32) : Array UInt8 :=
  (((out.push ((v >>> 24).toUInt8))
    |>.push ((v >>> 16).toUInt8))
    |>.push ((v >>> 8).toUInt8))
    |>.push v.toUInt8

private def sha1Expand (w : Array UInt32) (i : Nat) : Nat → Array UInt32
  | 0 => w
  | k + 1 =>
      let g (idx : Nat) : UInt32 := if h : idx < w.size then w[idx] else 0
      let v := rotl32 (g (i - 3) ^^^ g (i - 8) ^^^ g (i - 14) ^^^ g (i - 16)) 1
      sha1Expand (w.push v) (i + 1) k

private def sha1Rounds (w : Array UInt32) (i : Nat) (a b c d e : UInt32) :
    Nat → UInt32 × UInt32 × UInt32 × UInt32 × UInt32
  | 0 => (a, b, c, d, e)
  | k + 1 =>
      let (f, kc) : UInt32 × UInt32 :=
        if i < 20 then ((b &&& c) ||| ((~~~b) &&& d), 0x5A827999)
        else if i < 40 then (b ^^^ c ^^^ d, 0x6ED9EBA1)
        else if i < 60 then ((b &&& c) ||| (b &&& d) ||| (c &&& d), 0x8F1BBCDC)
        else (b ^^^ c ^^^ d, 0xCA62C1D6)
      let wi := if hi : i < w.size then w[i] else 0
      let tmp := rotl32 a 5 + f + e + kc + wi
      sha1Rounds w (i + 1) tmp a (rotl32 b 30) c d k

private def sha1Block (h0 h1 h2 h3 h4 : UInt32) (blk : Array UInt8) (off : Nat) :
    UInt32 × UInt32 × UInt32 × UInt32 × UInt32 :=
  let g (k : Nat) : UInt8 := if hk : k < blk.size then blk[k] else 0
  let w0 : Array UInt32 := (Array.range 16).map fun i =>
    let p := off + i * 4
    beU32 (g p) (g (p + 1)) (g (p + 2)) (g (p + 3))
  let w := sha1Expand w0 16 64
  let (a, b, c, d, e) := sha1Rounds w 0 h0 h1 h2 h3 h4 80
  (h0 + a, h1 + b, h2 + c, h3 + d, h4 + e)

private def sha1Blocks (padded : Array UInt8) (off : Nat) (h0 h1 h2 h3 h4 : UInt32) :
    Nat → UInt32 × UInt32 × UInt32 × UInt32 × UInt32
  | 0 => (h0, h1, h2, h3, h4)
  | k + 1 =>
      let (h0', h1', h2', h3', h4') := sha1Block h0 h1 h2 h3 h4 padded off
      sha1Blocks padded (off + 64) h0' h1' h2' h3' h4' k

/-- Pure total FIPS 180-4 SHA-1 hash (used solely for RFC 6455 `Sec-WebSocket-Accept`). -/
def sha1 (msg : ByteArray) : ByteArray :=
  let n := msg.data.size
  let bitLen : UInt64 := (UInt64.ofNat n) * 8
  let rem := (n + 1) % 64
  let zeros := if rem <= 56 then 56 - rem else 120 - rem
  let padded : Array UInt8 :=
    let b1 := msg.data.push 0x80 ++ Array.replicate zeros 0
    pushBeU32Arr (pushBeU32Arr b1 ((bitLen >>> 32).toUInt32)) bitLen.toUInt32
  let (h0, h1, h2, h3, h4) := sha1Blocks padded 0 0x67452301 0xEFCDAB89 0x98BADCFE 0x10325476 0xC3D2E1F0 (padded.size / 64)
  ByteArray.mk (pushBeU32Arr (pushBeU32Arr (pushBeU32Arr (pushBeU32Arr (pushBeU32Arr #[] h0) h1) h2) h3) h4)

/-- Computes RFC 6455 §4.2.2 `Sec-WebSocket-Accept` in pure Lean. -/
def wsComputeAccept (secKey : String) : Option String :=
  let k := trimOws secKey
  if k.isEmpty || k.utf8ByteSize > 64 || hasCtlOrCrlf k false || k.contains ' ' then none
  else some (base64Encode (sha1 (k ++ "258EAFA5-E914-47DA-95CA-C5AB0DC85B11").toUTF8))

theorem sha1_size (msg : ByteArray) : (sha1 msg).size = 20 := by
  unfold sha1
  simp only [ByteArray.size, pushBeU32Arr, Array.size_push]
  rfl

theorem base64Encode_rfc6455_accept :
    base64Encode (ByteArray.mk #[
      0xb3, 0x7a, 0x4f, 0x2c, 0xc0, 0x62, 0x4f, 0x16, 0x90, 0xf6,
      0x46, 0x06, 0xcf, 0x38, 0x59, 0x45, 0xb2, 0xbe, 0xc4, 0xea
    ]) = "s3pPLMBiTxaQ9kYGzzhZRbK+xOo=" := by
  rfl

/-! ## RFC 6455 WebSocket Frame Codec -/

inductive WsFrameStep where
  | needMore
  | frame (fin : Bool) (opcode : UInt8) (payload : ByteArray) (consumed : Nat)
  | protocolErr (closeCode : UInt16)

private def unmaskPayload (data : Array UInt8) (dataOff plen : Nat) (hbound : dataOff + plen ≤ data.size)
    (m0 m1 m2 m3 : UInt8) : ByteArray :=
  let rec go (i : Nat) (out : Array UInt8) : Array UInt8 :=
    if h : i < plen then
      let b := data[dataOff + i]'(by omega)
      let m := match i &&& 3 with | 0 => m0 | 1 => m1 | 2 => m2 | _ => m3
      go (i + 1) (out.push (b ^^^ m))
    else out
  termination_by plen - i
  ByteArray.mk (go 0 (Array.mkEmpty plen))

/-- Decodes one client-to-server RFC 6455 frame from `buf` starting at `offset`, enforcing
    `RSV == 0`, client masking, non-fragmented control frames (`≤ 125` bytes), and `maxMsgBytes`. -/
def decodeWsFrame (buf : ByteArray) (offset : Nat) (maxMsgBytes : Nat := maxWsMsgBytes) : WsFrameStep :=
  let d := buf.data
  if h2 : offset + 2 ≤ d.size then
    let b0 := d[offset]'(by omega)
    let b1 := d[offset + 1]'(by omega)
    let fin := (b0 &&& 0x80) != 0
    let rsv := (b0 >>> 4) &&& 0x07
    let opcode := b0 &&& 0x0F
    let masked := (b1 &&& 0x80) != 0
    if rsv != 0 || !masked then
      .protocolErr 1002
    else
      let len7 := (b1 &&& 0x7F).toNat
      let hdr? : Option (Except UInt16 (Nat × Nat)) :=
        if len7 < 126 then
          some (.ok (2, len7))
        else if len7 == 126 then
          if h4 : offset + 4 ≤ d.size then
            let p := ((d[offset + 2]'(by omega)).toNat <<< 8) ||| (d[offset + 3]'(by omega)).toNat
            some (.ok (4, p))
          else none
        else
          if h10 : offset + 10 ≤ d.size then
            let p0 := d[offset + 2]'(by omega)
            if (p0 &&& 0x80) != 0 then some (.error 1002)
            else
              let p :=
                ((p0.toNat) <<< 56) |||
                ((d[offset + 3]'(by omega)).toNat <<< 48) |||
                ((d[offset + 4]'(by omega)).toNat <<< 40) |||
                ((d[offset + 5]'(by omega)).toNat <<< 32) |||
                ((d[offset + 6]'(by omega)).toNat <<< 24) |||
                ((d[offset + 7]'(by omega)).toNat <<< 16) |||
                ((d[offset + 8]'(by omega)).toNat <<< 8) |||
                (d[offset + 9]'(by omega)).toNat
              some (.ok (10, p))
          else none
      match hdr? with
      | none => .needMore
      | some (.error code) => .protocolErr code
      | some (.ok (hdrLen, plen)) =>
          if opcode >= 0x08 && (plen > 125 || !fin) then
            .protocolErr 1002
          else if plen > maxMsgBytes then
            .protocolErr 1009
          else
            let frameTotal := hdrLen + 4 + plen
            if htot : offset + frameTotal ≤ d.size then
              let mOff := offset + hdrLen
              let m0 := d[mOff]'(by omega)
              let m1 := d[mOff + 1]'(by omega)
              let m2 := d[mOff + 2]'(by omega)
              let m3 := d[mOff + 3]'(by omega)
              .frame fin opcode (unmaskPayload d (mOff + 4) plen (by omega) m0 m1 m2 m3) frameTotal
            else
              .needMore
  else
    .needMore

/-- Encodes an unmasked server-to-client RFC 6455 frame (`FIN = 1`). -/
def encodeWsFrame (opcode : UInt8) (payload : ByteArray) : ByteArray :=
  let b0 : UInt8 := 0x80 ||| (opcode &&& 0x0F)
  let n := payload.size
  let hdr :=
    if n < 126 then
      ByteArray.mk #[b0, UInt8.ofNat n]
    else if n ≤ 65535 then
      ByteArray.mk #[b0, 126, UInt8.ofNat ((n >>> 8) &&& 0xFF), UInt8.ofNat (n &&& 0xFF)]
    else
      let u := UInt64.ofNat n
      ByteArray.mk #[
        b0, 127,
        ((u >>> 56).toUInt8), ((u >>> 48).toUInt8), ((u >>> 40).toUInt8), ((u >>> 32).toUInt8),
        ((u >>> 24).toUInt8), ((u >>> 16).toUInt8), ((u >>> 8).toUInt8), u.toUInt8
      ]
  hdr ++ payload

def encodeWsCloseFrame (code : UInt16) : ByteArray :=
  encodeWsFrame 0x08 (ByteArray.mk #[(code >>> 8).toUInt8, code.toUInt8])

theorem decodeWsFrame_rejects_unmasked (b0 b1 : UInt8) (rest : Array UInt8)
    (hunmasked : (b1 &&& 0x80) = 0) :
    decodeWsFrame (ByteArray.mk (#[b0, b1] ++ rest)) 0 = .protocolErr 1002 := by
  unfold decodeWsFrame
  simp [hunmasked]

theorem decodeWsFrame_rejects_rsv (b0 b1 : UInt8) (rest : Array UInt8)
    (hrsv : ((b0 >>> 4) &&& 0x07) ≠ 0) :
    decodeWsFrame (ByteArray.mk (#[b0, b1] ++ rest)) 0 = .protocolErr 1002 := by
  unfold decodeWsFrame
  simp [hrsv]

end Qed.Server.Http
