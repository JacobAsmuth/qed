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
  method     : String
  target     : String
  isHttp11   : Bool
  keepAlive  : Bool
  contentLen : Nat
  headers    : Array (String × String)
  upgrade?   : Option String
  conn?      : Option String
  wsKey?     : Option String
  wsVer?     : Option String

private structure HdrFoldState where
  keepAlive   : Bool
  contentLen? : Option Nat
  hostCount   : Nat
  headers     : Array (String × String)
  upgrade?    : Option String
  conn?       : Option String
  wsKey?      : Option String
  wsVer?      : Option String

def parseOneHeaderLine (line : String) (st : HdrFoldState) :
    Except (Nat × String) HdrFoldState :=
  match splitHeaderKv line with
  | none => .error (400, "malformed header")
  | some (k, v) =>
      if !isValidHttpToken k then
        .error (400, "invalid header name")
      else
        let kl := k.toLower
        if kl == "transfer-encoding" then
          .error (501, "Transfer-Encoding not supported")
        else if st.headers.size >= maxReqHeaders then
          .error (431, "too many headers")
        else if kl == "host" then
          if v.isEmpty || hasCtlOrCrlf v false then
            .error (400, "invalid Host header")
          else if st.hostCount >= 1 then
            .error (400, "duplicate Host header")
          else
            .ok { st with hostCount := st.hostCount + 1, headers := st.headers.push (k, v) }
        else if kl == "content-length" then
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
          let keepAlive' :=
            if kl == "connection" then
              if containsCI v "close" then false
              else if containsCI v "keep-alive" then true
              else st.keepAlive
            else st.keepAlive
          .ok { st with
            keepAlive := keepAlive'
            headers   := st.headers.push (k, v)
            conn?     := if kl == "connection" then some v else st.conn?
            upgrade?  := if kl == "upgrade" then some v else st.upgrade?
            wsKey?    := if kl == "sec-websocket-key" then some v else st.wsKey?
            wsVer?    := if kl == "sec-websocket-version" then some v else st.wsVer?
          }

private def parseHdrLines (lines : Array String) (idx : Nat) (st : HdrFoldState) :
    Except (Nat × String) HdrFoldState :=
  if h : idx < lines.size then
    match parseOneHeaderLine lines[idx] st with
    | .error e => .error e
    | .ok st'  => parseHdrLines lines (idx + 1) st'
  else
    .ok st
termination_by lines.size - idx

private def parseReqLine (line : String) : Except (Nat × String) (String × String × Bool) :=
  match line.splitOn " " with
  | [method, target, httpVer] =>
      if method.isEmpty || !isValidHttpToken method || target.isEmpty then .error (400, "malformed request line")
      else
        let isHttp11 := httpVer == "HTTP/1.1"
        if !isHttp11 && httpVer != "HTTP/1.0" then .error (400, "unsupported HTTP version")
        else .ok (method, target, isHttp11)
  | _ => .error (400, "malformed request line")

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
                keepAlive := isHttp11, contentLen? := none, hostCount := 0, headers := #[],
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
                      keepAlive  := st.keepAlive
                      contentLen := st.contentLen?.getD 0
                      headers    := st.headers
                      upgrade?   := st.upgrade?
                      conn?      := st.conn?
                      wsKey?     := st.wsKey?
                      wsVer?     := st.wsVer?
                    }

theorem parseRequestHead_rejects_nul (headBytes : ByteArray)
    (hnul : byteArrayContains headBytes 0 = true) :
    ∃ e, parseRequestHead headBytes = .error e := by
  unfold parseRequestHead
  by_cases hsz : headBytes.size > maxReqHdrBytes
  · exact ⟨(431, "request headers too large"), by simp [hsz]⟩
  · have hsplit : splitCrlfLines headBytes = .error "invalid NUL byte in headers" := by
      unfold splitCrlfLines; simp [hnul]
    exact ⟨(400, "invalid NUL byte in headers"), by simp [hsz, hsplit]⟩

theorem parseOneHeaderLine_rejects_bad_name (line k v : String) (st : HdrFoldState)
    (hkv : splitHeaderKv line = some (k, v)) (hbad : isValidHttpToken k = false) :
    parseOneHeaderLine line st = .error (400, "invalid header name") := by
  unfold parseOneHeaderLine
  simp [hkv, hbad]

private theorem parseOneHeaderLine_contentLen_le (line : String) (st st' : HdrFoldState)
    (hinit : ∀ cl, st.contentLen? = some cl → cl ≤ maxReqBodyBytes)
    (hok : parseOneHeaderLine line st = .ok st') :
    ∀ cl, st'.contentLen? = some cl → cl ≤ maxReqBodyBytes := by
  unfold parseOneHeaderLine at hok
  cases hs : splitHeaderKv line with
  | none => simp [hs] at hok
  | some kv =>
      simp only [hs] at hok
      by_cases htok : isValidHttpToken kv.1
      · simp only [htok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        by_cases hte : kv.1.toLower == "transfer-encoding"
        · simp [hte] at hok
        · by_cases hmax : st.headers.size >= maxReqHeaders
          · simp [hte, hmax] at hok
          · by_cases hhost : kv.1.toLower == "host"
            · simp only [hte, hmax, hhost, ↓reduceIte, Bool.false_eq_true] at hok
              split at hok
              · cases hok
              · split at hok
                · cases hok
                · simp only [Except.ok.injEq] at hok; subst hok; exact hinit
            · by_cases hcl : kv.1.toLower == "content-length"
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
                            intro c hc; simp only [Option.some.injEq] at hc
                            exact hinit c (by rw [hprev, hc])
                    | none =>
                        simp only [hprev] at hok
                        by_cases hbig : maxReqBodyBytes < cl
                        · simp [hbig] at hok
                        · simp only [hbig, ↓reduceIte, Except.ok.injEq] at hok
                          subst hok
                          intro c hc; simp only [Option.some.injEq] at hc; omega
              · simp only [hte, hmax, hhost, hcl, ↓reduceIte, Bool.false_eq_true, Except.ok.injEq] at hok
                subst hok; exact hinit
      · simp [htok] at hok

private theorem parseHdrLines_contentLen_le (lines : Array String) (idx : Nat) (st st' : HdrFoldState)
    (hinit : ∀ cl, st.contentLen? = some cl → cl ≤ maxReqBodyBytes)
    (hok : parseHdrLines lines idx st = .ok st') :
    ∀ cl, st'.contentLen? = some cl → cl ≤ maxReqBodyBytes := by
  unfold parseHdrLines at hok
  split at hok
  · cases hstep : parseOneHeaderLine lines[idx] st with
    | error e => simp [hstep] at hok
    | ok stMid =>
        simp only [hstep] at hok
        exact parseHdrLines_contentLen_le lines (idx + 1) stMid st'
          (parseOneHeaderLine_contentLen_le lines[idx] st stMid hinit hstep) hok
  · simp only [Except.ok.injEq] at hok
    subst hok; exact hinit
termination_by lines.size - idx

private theorem parseOneHeaderLine_hostCount_step (line : String) (st st' : HdrFoldState)
    (hok : parseOneHeaderLine line st = .ok st') :
    st'.hostCount = st.hostCount ∨
    (st'.hostCount = st.hostCount + 1 ∧ ∃ k v, (k, v) ∈ st'.headers.toList ∧ k.toLower == "host") := by
  unfold parseOneHeaderLine at hok
  cases hs : splitHeaderKv line with
  | none => simp [hs] at hok
  | some kv =>
      simp only [hs] at hok
      by_cases htok : isValidHttpToken kv.1
      · simp only [htok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        by_cases hte : kv.1.toLower == "transfer-encoding"
        · simp [hte] at hok
        · by_cases hmax : st.headers.size >= maxReqHeaders
          · simp [hte, hmax] at hok
          · by_cases hhost : kv.1.toLower == "host"
            · simp only [hte, hmax, hhost, ↓reduceIte, Bool.false_eq_true] at hok
              split at hok
              · cases hok
              · split at hok
                · cases hok
                · simp only [Except.ok.injEq] at hok; subst hok
                  right
                  refine ⟨rfl, kv.1, kv.2, ?_, hhost⟩
                  simp [Array.toList_push]
            · by_cases hcl : kv.1.toLower == "content-length"
              · simp only [hte, hmax, hhost, hcl, ↓reduceIte, Bool.false_eq_true] at hok
                cases hp : parseStrictU64 kv.2 18446744073709551615 with
                | none => simp [hp] at hok
                | some cl =>
                    simp only [hp] at hok
                    cases hprev : st.contentLen? with
                    | some prev =>
                        simp only [hprev] at hok
                        split at hok
                        · cases hok
                        · split at hok
                          · cases hok
                          · simp only [Except.ok.injEq] at hok; subst hok; left; rfl
                    | none =>
                        simp only [hprev] at hok
                        split at hok
                        · cases hok
                        · simp only [Except.ok.injEq] at hok; subst hok; left; rfl
              · simp only [hte, hmax, hhost, hcl, ↓reduceIte, Bool.false_eq_true, Except.ok.injEq] at hok
                subst hok; left; rfl
      · simp [htok] at hok

private theorem parseOneHeaderLine_headers_mono (line : String) (st st' : HdrFoldState)
    (hok : parseOneHeaderLine line st = .ok st') :
    ∀ p ∈ st.headers.toList, p ∈ st'.headers.toList := by
  unfold parseOneHeaderLine at hok
  cases hs : splitHeaderKv line with
  | none => simp [hs] at hok
  | some kv =>
      simp only [hs] at hok
      by_cases htok : isValidHttpToken kv.1
      · simp only [htok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok
        by_cases hte : kv.1.toLower == "transfer-encoding"
        · simp [hte] at hok
        · by_cases hmax : st.headers.size >= maxReqHeaders
          · simp [hte, hmax] at hok
          · by_cases hhost : kv.1.toLower == "host"
            · simp only [hte, hmax, hhost, ↓reduceIte, Bool.false_eq_true] at hok
              split at hok
              · cases hok
              · split at hok
                · cases hok
                · simp only [Except.ok.injEq] at hok; subst hok
                  intro p hp; simp [Array.toList_push, hp]
            · by_cases hcl : kv.1.toLower == "content-length"
              · simp only [hte, hmax, hhost, hcl, ↓reduceIte, Bool.false_eq_true] at hok
                cases hp : parseStrictU64 kv.2 18446744073709551615 with
                | none => simp [hp] at hok
                | some cl =>
                    simp only [hp] at hok
                    cases hprev : st.contentLen? with
                    | some prev =>
                        simp only [hprev] at hok
                        split at hok
                        · cases hok
                        · split at hok
                          · cases hok
                          · simp only [Except.ok.injEq] at hok; subst hok
                            intro p hp; simp [Array.toList_push, hp]
                    | none =>
                        simp only [hprev] at hok
                        split at hok
                        · cases hok
                        · simp only [Except.ok.injEq] at hok; subst hok
                          intro p hp; simp [Array.toList_push, hp]
              · simp only [hte, hmax, hhost, hcl, ↓reduceIte, Bool.false_eq_true, Except.ok.injEq] at hok
                subst hok; intro p hp; simp [Array.toList_push, hp]
      · simp [htok] at hok

private theorem parseHdrLines_host_of_pos (lines : Array String) (idx : Nat) (st st' : HdrFoldState)
    (hinv : st.hostCount > 0 → ∃ k v, (k, v) ∈ st.headers.toList ∧ k.toLower == "host")
    (hok : parseHdrLines lines idx st = .ok st') :
    st'.hostCount > 0 → ∃ k v, (k, v) ∈ st'.headers.toList ∧ k.toLower == "host" := by
  unfold parseHdrLines at hok
  split at hok
  · cases hstep : parseOneHeaderLine lines[idx] st with
    | error e => simp [hstep] at hok
    | ok stMid =>
        simp only [hstep] at hok
        have hmid : stMid.hostCount > 0 → ∃ k v, (k, v) ∈ stMid.headers.toList ∧ k.toLower == "host" := by
          intro hpos
          rcases parseOneHeaderLine_hostCount_step lines[idx] st stMid hstep with heq | ⟨_, k, v, hmem, hk⟩
          · rw [heq] at hpos
            rcases hinv hpos with ⟨k, v, hmem, hk⟩
            exact ⟨k, v, parseOneHeaderLine_headers_mono lines[idx] st stMid hstep _ hmem, hk⟩
          · exact ⟨k, v, hmem, hk⟩
        exact parseHdrLines_host_of_pos lines (idx + 1) stMid st' hmid hok
  · simp only [Except.ok.injEq] at hok
    subst hok; exact hinv
termination_by lines.size - idx

theorem parseRequestHead_http11_has_host (headBytes : ByteArray) (req : ParsedReqHead)
    (hok : parseRequestHead headBytes = .ok req) (h11 : req.isHttp11 = true) :
    ∃ k v, (k, v) ∈ req.headers.toList ∧ k.toLower == "host" := by
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
                keepAlive := is11, contentLen? := none, hostCount := 0, headers := #[],
                upgrade? := none, conn? := none, wsKey? := none, wsVer? := none
              }
              cases hfold : parseHdrLines lines 1 initSt with
              | error e => simp [initSt, hfold] at hok
              | ok st =>
                  simp only [initSt, hfold] at hok
                  by_cases hmiss : (is11 && st.hostCount != 1) = true
                  · simp [hmiss] at hok
                  · simp only [hmiss, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hok
                    subst hok
                    simp only at h11
                    have hc1 : st.hostCount = 1 := by
                      simp [h11] at hmiss
                      exact hmiss
                    exact parseHdrLines_host_of_pos lines 1 initSt st (by intro h; simp [initSt] at h) hfold (by omega)

theorem parseRequestHead_contentLen_le (headBytes : ByteArray) (req : ParsedReqHead)
    (hok : parseRequestHead headBytes = .ok req) :
    req.contentLen ≤ maxReqBodyBytes := by
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
                keepAlive := is11, contentLen? := none, hostCount := 0, headers := #[],
                upgrade? := none, conn? := none, wsKey? := none, wsVer? := none
              }
              cases hfold : parseHdrLines lines 1 initSt with
              | error e => simp [initSt, hfold] at hok
              | ok st =>
                  simp only [initSt, hfold] at hok
                  by_cases hmiss : (is11 && st.hostCount != 1) = true
                  · simp [hmiss] at hok
                  · simp only [hmiss, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hok
                    subst hok
                    have hb := parseHdrLines_contentLen_le lines 1 initSt st (by intro cl h; cases h) hfold
                    cases hcl : st.contentLen? with
                    | none => simp [maxReqBodyBytes]
                    | some cl => simpa [hcl] using hb cl hcl

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
  · rfl
  · rename_i h; simpa using h

def formatHttpResponseHead (status : Nat) (contentType : String) (contentLen : Nat)
    (keepAlive noStore : Bool) (etag? : Option String := none)
    (cacheControl? : Option String := none) : ByteArray :=
  let code := if status >= 100 && status <= 599 then status else 500
  let ct := safeContentType contentType
  let conn := if keepAlive then "keep-alive" else "close"
  let cache := match cacheControl? with
    | some cc => if hasCtlOrCrlf cc false then "" else s!"Cache-Control: {cc}\r\n"
    | none    => if noStore then "Cache-Control: no-store\r\n" else ""
  let etag := match etag? with
    | some et => if hasCtlOrCrlf et false then "" else s!"ETag: {et}\r\n"
    | none    => ""
  (s!"HTTP/1.1 {code} {statusReason code}\r\n" ++
   s!"Content-Type: {ct}\r\n" ++
   s!"Content-Length: {contentLen}\r\n" ++
   "X-Content-Type-Options: nosniff\r\n" ++
   etag ++
   cache ++
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
    (cacheControl? : Option String := none) : ByteArray :=
  let head := formatHttpResponseHead status contentType body.size keepAlive noStore etag? cacheControl?
  if headOnly then head else head ++ body

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
    have hgt : 1 < (((target.splitOn "?").headD target).splitOn "..").length := h
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

private def unmaskPayload (data : Array UInt8) (dataOff plen : Nat) (m0 m1 m2 m3 : UInt8) : ByteArray :=
  let rec go (i : Nat) (out : Array UInt8) : Array UInt8 :=
    if h : i < plen then
      let b := if hk : dataOff + i < data.size then data[dataOff + i] else 0
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
              .frame fin opcode (unmaskPayload d (mOff + 4) plen m0 m1 m2 m3) frameTotal
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
