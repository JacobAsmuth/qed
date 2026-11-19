import Qed.Server.Core

namespace Qed.Server.Net

/-! ## Shared Byte, ASCII & HTTP/1.1 Framing Primitives -/

private def trimBy (p : Char → Bool) (s : String) : String :=
  String.ofList (((s.toList.dropWhile p).reverse.dropWhile p).reverse)

def trimWs (s : String) : String := trimBy Char.isWhitespace s

def trimOws (s : String) : String := trimBy (fun c => c == ' ' || c == '\t') s

def stripTrailingSlashes (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (· == '/')).reverse)

def containsCI (haystack needle : String) : Bool :=
  let n := needle.toLower
  !n.isEmpty && (haystack.toLower.splitOn n).length > 1

def byteArrayContains (ba : ByteArray) (target : UInt8) : Bool :=
  let rec go (i : Nat) : Bool :=
    if h : i < ba.size then
      if ba[i] == target then true else go (i + 1)
    else false
  termination_by ba.size - i
  go 0

def findCrlf (ba : ByteArray) (start : Nat) : Option Nat :=
  let rec go (i : Nat) : Option Nat :=
    if h : i + 1 < ba.size then
      if ba[i] == 13 && ba[i + 1] == 10 then some i else go (i + 1)
    else none
  termination_by ba.size - i
  go start

def findCrlfCrlf (ba : ByteArray) (start : Nat := 0) : Option Nat :=
  let rec go (i : Nat) : Option Nat :=
    if h : i + 3 < ba.size then
      if ba[i] == 13 && ba[i + 1] == 10 && ba[i + 2] == 13 && ba[i + 3] == 10 then some i
      else go (i + 1)
    else none
  termination_by ba.size - i
  go start

def hasCtlOrCrlf (s : String) (allowTab : Bool) : Bool :=
  s.toList.any fun c =>
    let n := c.toNat
    n == 13 || n == 10 || n == 127 || (n < 32 && !(allowTab && n == 9))

def isValidHttpToken (s : String) : Bool :=
  let cs := s.toList
  !cs.isEmpty && cs.all fun c =>
    let n := c.toNat
    n > 32 && n < 127 && !("()<>@,;:\\\"/[]?={}".contains c)

def parseStrictU64 (s : String) (maxVal : Nat) : Option Nat :=
  let cs := (trimOws s).toList
  if cs.isEmpty then none
  else
    let rec go (acc : Nat) : List Char → Option Nat
      | [] => some acc
      | c :: rest =>
          if '0' ≤ c && c ≤ '9' then
            let d := c.toNat - '0'.toNat
            if acc > (maxVal - d) / 10 then none
            else go (acc * 10 + d) rest
          else none
    go 0 cs

def parseHexSize (s : String) (maxVal : Nat := 268435456) : Option Nat :=
  let raw := match s.splitOn ";" with | h :: _ => h | [] => ""
  let cs := (trimOws raw).toList
  if cs.isEmpty then none
  else
    let rec go (acc : Nat) : List Char → Option Nat
      | [] => some acc
      | c :: rest =>
          let d? : Option Nat :=
            if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
            else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
            else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
            else none
          match d? with
          | none => none
          | some d =>
              if acc > (maxVal - d) / 16 then none
              else go (acc * 16 + d) rest
    go 0 cs

/-- Splits an HTTP header block (bytes before `\r\n\r\n`) into strict CRLF-delimited lines,
    rejecting NUL bytes, bare CR, bare LF, and invalid UTF-8. -/
def splitCrlfLines (ba : ByteArray) : Except String (Array String) :=
  if byteArrayContains ba 0 then
    .error "invalid NUL byte in headers"
  else
    let rec go (i lineStart : Nat) (acc : Array String) : Except String (Array String) :=
      if h : i < ba.size then
        let b := ba[i]
        if b == 10 then
          .error "bare LF in headers"
        else if b == 13 then
          if h2 : i + 1 < ba.size then
            if ba[i + 1] == 10 then
              match String.fromUTF8? (ba.extract lineStart i) with
              | some line => go (i + 2) (i + 2) (acc.push line)
              | none      => .error "invalid UTF-8 in headers"
            else .error "bare CR in headers"
          else .error "bare CR in headers"
        else
          go (i + 1) lineStart acc
      else
        if lineStart < ba.size then
          match String.fromUTF8? (ba.extract lineStart ba.size) with
          | some line => .ok (acc.push line)
          | none      => .error "invalid UTF-8 in headers"
        else .ok acc
    termination_by ba.size - i
    go 0 0 #[]

def splitHeaderKv (line : String) : Option (String × String) :=
  match line.splitOn ":" with
  | [] | [_] => none
  | k :: rest =>
      let v := String.intercalate ":" rest
      some (k, trimOws v)

/-! ## Formally Verified SSRF IP CIDR Policy (`isBlockedIpBytes`) -/

/-- Blocks non-globally-routable IPv4 CIDRs: `0.0.0.0/8`, `10.0.0.0/8`, `100.64.0.0/10` (CGNAT),
    `127.0.0.0/8` (loopback), `169.254.0.0/16` (link-local & cloud metadata), `172.16.0.0/12`,
    `192.168.0.0/16`, and `224.0.0.0/3` (multicast & reserved). -/
def isBlockedIpv4 (b0 b1 _b2 _b3 : UInt8) : Bool :=
  b0 == 0 || b0 == 10 || (b0 == 100 && (b1 &&& 0xC0) == 64) || b0 == 127 ||
  (b0 == 169 && b1 == 254) || (b0 == 172 && (b1 &&& 0xF0) == 16) ||
  (b0 == 192 && b1 == 168) || b0 >= 224

private def allZeroRange (data : Array UInt8) (lo : Nat) : Nat → Bool
  | 0 => true
  | k + 1 =>
      if h : lo < data.size then
        data[lo] == 0 && allZeroRange data (lo + 1) k
      else false

/-- Total SSRF IP blocklist over raw 4-byte IPv4 or 16-byte IPv6 addresses (fail-closed on any
    unexpected length). Also blocks IPv4-mapped (`::ffff:0:0/96`), IPv4-compatible (`::/96`),
    NAT64 (`64:ff9b::/96`), ULA (`fc00::/7`), link-local (`fe80::/10`), and multicast (`ff00::/8`). -/
def isBlockedIpBytes (addr : ByteArray) : Bool :=
  let d := addr.data
  if h4 : d.size = 4 then
    isBlockedIpv4 (d[0]'(by omega)) (d[1]'(by omega)) (d[2]'(by omega)) (d[3]'(by omega))
  else if h16 : d.size = 16 then
    let b0  := d[0]'(by omega)
    let b1  := d[1]'(by omega)
    let b2  := d[2]'(by omega)
    let b3  := d[3]'(by omega)
    let b10 := d[10]'(by omega)
    let b11 := d[11]'(by omega)
    let b12 := d[12]'(by omega)
    let b13 := d[13]'(by omega)
    let b14 := d[14]'(by omega)
    let b15 := d[15]'(by omega)
    if allZeroRange d 0 12 then
      (b12 == 0 && b13 == 0 && b14 == 0 && b15 <= 1) || isBlockedIpv4 b12 b13 b14 b15
    else if (b0 &&& 0xFE) == 0xFC then true
    else if b0 == 0xFE && (b1 &&& 0xC0) == 0x80 then true
    else if b0 == 0xFF then true
    else if allZeroRange d 0 10 && b10 == 0xFF && b11 == 0xFF then
      isBlockedIpv4 b12 b13 b14 b15
    else if b0 == 0x00 && b1 == 0x64 && b2 == 0xFF && b3 == 0x9B && allZeroRange d 4 8 then
      isBlockedIpv4 b12 b13 b14 b15
    else false
  else
    true

theorem isBlockedIpBytes_loopback_v4 (b1 b2 b3 : UInt8) :
    isBlockedIpBytes (ByteArray.mk #[127, b1, b2, b3]) = true := by
  simp [isBlockedIpBytes, isBlockedIpv4]

theorem isBlockedIpBytes_metadata_v4 (b2 b3 : UInt8) :
    isBlockedIpBytes (ByteArray.mk #[169, 254, b2, b3]) = true := by
  simp [isBlockedIpBytes, isBlockedIpv4]

theorem isBlockedIpBytes_rfc1918_10 (b1 b2 b3 : UInt8) :
    isBlockedIpBytes (ByteArray.mk #[10, b1, b2, b3]) = true := by
  simp [isBlockedIpBytes, isBlockedIpv4]

theorem isBlockedIpBytes_loopback_v6 :
    isBlockedIpBytes (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]) = true := by
  rfl

theorem isBlockedIpBytes_v4mapped_metadata :
    isBlockedIpBytes (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xFF, 0xFF, 169, 254, 169, 254]) = true := by
  rfl

theorem isBlockedIpBytes_nat64_metadata :
    isBlockedIpBytes (ByteArray.mk #[0, 0x64, 0xFF, 0x9B, 0, 0, 0, 0, 0, 0, 0, 0, 169, 254, 169, 254]) = true := by
  rfl

theorem isBlockedIpBytes_badLen (addr : ByteArray) (h4 : addr.size ≠ 4) (h16 : addr.size ≠ 16) :
    isBlockedIpBytes addr = true := by
  simp [isBlockedIpBytes, h4, h16]

/-! ## Unified RFC 4648 Base64 & Base64URL Encoder -/

def isBase64UrlChar (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '-' || c == '_'

def b64Char (urlSafe : Bool) (n : Nat) : Char :=
  if n < 26 then Char.ofNat (65 + n)
  else if n < 52 then Char.ofNat (97 + (n - 26))
  else if n < 62 then Char.ofNat (48 + (n - 52))
  else if n == 62 then (if urlSafe then '-' else '+')
  else (if urlSafe then '_' else '/')

private theorem char_ofNat_toNat_small (m : Nat) (hm : m < 128) :
    (Char.ofNat m).toNat = m := by
  have hv : m.isValidChar := by simp [Nat.isValidChar]; omega
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

private theorem b64UrlChar_safe (n : Nat) : isBase64UrlChar (b64Char true n) = true := by
  unfold b64Char isBase64UrlChar
  by_cases h1 : n < 26
  · have hval := char_ofNat_toNat_small (65 + n) (by omega)
    simp only [h1, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    left; left; left; left
    exact ⟨by change (65 : Nat) ≤ (Char.ofNat (65 + n)).toNat; omega,
           by change (Char.ofNat (65 + n)).toNat ≤ (90 : Nat); omega⟩
  · by_cases h2 : n < 52
    · have hval := char_ofNat_toNat_small (97 + (n - 26)) (by omega)
      simp only [h1, h2, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      left; left; left; right
      exact ⟨by change (97 : Nat) ≤ (Char.ofNat (97 + (n - 26))).toNat; omega,
             by change (Char.ofNat (97 + (n - 26))).toNat ≤ (122 : Nat); omega⟩
    · by_cases h3 : n < 62
      · have hval := char_ofNat_toNat_small (48 + (n - 52)) (by omega)
        simp only [h1, h2, h3, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        left; left; right
        exact ⟨by change (48 : Nat) ≤ (Char.ofNat (48 + (n - 52))).toNat; omega,
               by change (Char.ofNat (48 + (n - 52))).toNat ≤ (57 : Nat); omega⟩
      · by_cases h4 : n == 62
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]

private def base64Loop (urlSafe pad : Bool) (d : Array UInt8) (i : Nat) (acc : String) : Nat → String
  | 0 => acc
  | fuel + 1 =>
      if h2 : i + 2 < d.size then
        let v := ((d[i]'(by omega)).toNat <<< 16) ||| ((d[i + 1]'(by omega)).toNat <<< 8) ||| (d[i + 2]'(by omega)).toNat
        let acc' := ((((acc.push (b64Char urlSafe ((v >>> 18) &&& 0x3F)))
          |>.push (b64Char urlSafe ((v >>> 12) &&& 0x3F)))
          |>.push (b64Char urlSafe ((v >>> 6) &&& 0x3F)))
          |>.push (b64Char urlSafe (v &&& 0x3F)))
        base64Loop urlSafe pad d (i + 3) acc' fuel
      else if h1 : i + 1 < d.size then
        let v := ((d[i]'(by omega)).toNat <<< 16) ||| ((d[i + 1]'(by omega)).toNat <<< 8)
        let acc' := (((acc.push (b64Char urlSafe ((v >>> 18) &&& 0x3F)))
          |>.push (b64Char urlSafe ((v >>> 12) &&& 0x3F)))
          |>.push (b64Char urlSafe ((v >>> 6) &&& 0x3F)))
        if pad then acc'.push '=' else acc'
      else if h0 : i < d.size then
        let v := (d[i]'(by omega)).toNat <<< 16
        let acc' := ((acc.push (b64Char urlSafe ((v >>> 18) &&& 0x3F)))
          |>.push (b64Char urlSafe ((v >>> 12) &&& 0x3F)))
        if pad then (acc'.push '=').push '=' else acc'
      else
        acc

/-- RFC 4648 §4 standard Base64 encoding with `=` padding. -/
def base64Encode (bs : ByteArray) : String :=
  base64Loop false true bs.data 0 "" (bs.data.size / 3 + 1)

/-- RFC 4648 §5 Base64URL encoding without padding. -/
def base64UrlEncode (bs : ByteArray) : String :=
  base64Loop true false bs.data 0 "" (bs.data.size / 3 + 1)

private theorem base64UrlLoop_safe (d : Array UInt8) (i : Nat) (acc : String) (fuel : Nat)
    (hacc : acc.toList.all isBase64UrlChar = true) :
    (base64Loop true false d i acc fuel).toList.all isBase64UrlChar = true := by
  induction fuel generalizing i acc with
  | zero => exact hacc
  | succ fuel ih =>
      unfold base64Loop
      split
      · exact ih (i + 3) _ (by simp [String.toList_push, hacc, b64UrlChar_safe])
      · split
        · simp [String.toList_push, hacc, b64UrlChar_safe]
        · split
          · simp [String.toList_push, hacc, b64UrlChar_safe]
          · exact hacc

theorem base64UrlEncode_safe (bs : ByteArray) :
    (base64UrlEncode bs).toList.all isBase64UrlChar = true :=
  base64UrlLoop_safe bs.data 0 "" (bs.data.size / 3 + 1) rfl

/-! ## Outbound HTTP/1.1 URL Parser, Request Serializer & Response Head Parser -/

structure ParsedUrl where
  isTls        : Bool
  host         : String
  isIpv6       : Bool
  port         : UInt16
  pathAndQuery : String
deriving Repr, DecidableEq

private def parsePortU16 (s : String) : Option UInt16 := do
  let n ← parseStrictU64 s 65535
  if n == 0 then none else some (UInt16.ofNat n)

private def splitAuthorityAndPath (rest : String) : Option (String × String) :=
  let cs := rest.toList
  let rec go (authRev : List Char) : List Char → Option (String × String)
    | [] => some (String.ofList authRev.reverse, "/")
    | '#' :: _ => none
    | '?' :: tail => some (String.ofList authRev.reverse, "/?" ++ String.ofList tail)
    | '/' :: tail => some (String.ofList authRev.reverse, "/" ++ String.ofList tail)
    | c :: tail => go (c :: authRev) tail
  go [] cs

def parseHttpUrl (url : String) : Except String ParsedUrl := do
  if hasCtlOrCrlf url false || url.contains ' ' then
    throw s!"invalid outbound HTTP URL: {url}"
  let (isTls, defaultPort, rest) ←
    if url.startsWith "https://" then
      pure (true, (443 : UInt16), String.ofList (url.toList.drop 8))
    else if url.startsWith "http://" then
      pure (false, (80 : UInt16), String.ofList (url.toList.drop 7))
    else
      throw s!"unsupported URL scheme: {url}"
  let some (auth, path) := splitAuthorityAndPath rest
    | throw s!"invalid URL authority: {url}"
  if auth.isEmpty || auth.utf8ByteSize >= 256 || auth.contains '@' then
    throw s!"invalid URL authority: {url}"
  if auth.startsWith "[" then
    match auth.splitOn "]" with
    | [left, right] =>
        let host := String.ofList (left.toList.drop 1)
        if host.isEmpty then throw s!"empty IPv6 host: {url}"
        let port ←
          if right.isEmpty then pure defaultPort
          else if right.startsWith ":" then
            match parsePortU16 (String.ofList (right.toList.drop 1)) with
            | some p => pure p
            | none   => throw s!"invalid URL port: {url}"
          else throw s!"invalid IPv6 authority: {url}"
        return { isTls, host, isIpv6 := true, port, pathAndQuery := path }
    | _ => throw s!"malformed IPv6 authority: {url}"
  else
    let parts := auth.splitOn ":"
    match parts.reverse with
    | [h] =>
        if h.isEmpty then throw s!"empty URL host: {url}"
        return { isTls, host := h, isIpv6 := false, port := defaultPort, pathAndQuery := path }
    | portStr :: hostRev =>
        let host := String.intercalate ":" hostRev.reverse
        if host.isEmpty then throw s!"empty URL host: {url}"
        let some p := parsePortU16 portStr | throw s!"invalid URL port: {url}"
        return { isTls, host, isIpv6 := false, port := p, pathAndQuery := path }
    | [] => throw s!"empty URL authority: {url}"

/-- Serializes a validated outbound HTTP/1.1 request wire buffer, rejecting invalid method tokens
    and CRLF/control header injection. -/
def formatOutboundRequest (method : String) (u : ParsedUrl)
    (headers : Array (String × String)) (body : ByteArray) : Except String ByteArray := do
  if !isValidHttpToken method then
    throw "invalid outbound HTTP method"
  for (k, v) in headers do
    if !isValidHttpToken k || hasCtlOrCrlf v true then
      throw "invalid outbound HTTP header (CRLF/control chars)"
  let defaultPort := (u.isTls && u.port == 443) || (!u.isTls && u.port == 80)
  let hostHdr := (if u.isIpv6 then s!"[{u.host}]" else u.host) ++
    (if defaultPort then "" else s!":{u.port}")
  let mut head :=
    s!"{method} {u.pathAndQuery} HTTP/1.1\r\n" ++
    s!"Host: {hostHdr}\r\n" ++
    s!"Connection: keep-alive\r\n" ++
    s!"Content-Length: {body.size}\r\n"
  for (k, v) in headers do
    let kl := k.toLower
    if kl != "host" && kl != "content-length" && kl != "connection" then
      head := head ++ s!"{k}: {v}\r\n"
  head := head ++ "\r\n"
  return head.toUTF8 ++ body

structure ParsedRespHead where
  status     : Nat
  headers    : Array (String × String)
  isChunked  : Bool
  connClose  : Bool
  contentLen : Option Nat

private def parseStatusCode (s : String) : Option Nat :=
  match s.toList with
  | d0 :: d1 :: d2 :: rest =>
      let okDelim := match rest with | [] | ' ' :: _ | '\t' :: _ => true | _ => false
      if okDelim && '1' ≤ d0 && d0 ≤ '9' && '0' ≤ d1 && d1 ≤ '9' && '0' ≤ d2 && d2 ≤ '9' then
        some ((d0.toNat - '0'.toNat) * 100 + (d1.toNat - '0'.toNat) * 10 + (d2.toNat - '0'.toNat))
      else none
  | _ => none

/-- Parses a raw outbound HTTP/1.1 response header block (bytes before `\r\n\r\n`). -/
def parseHttpResponseHead (headBytes : ByteArray) : Except String ParsedRespHead := do
  let lines ← splitCrlfLines headBytes
  if h0 : lines.size = 0 then
    throw "empty HTTP response status line"
  else
    let statusLine := lines[0]'(by omega)
    if !statusLine.startsWith "HTTP/" then
      throw "invalid HTTP status line"
    let status ← match statusLine.splitOn " " with
      | _ :: codeRest :: _ =>
          match parseStatusCode codeRest with
          | some sc => pure sc
          | none    => throw "invalid HTTP status code"
      | _ => throw "invalid HTTP status line"
    let mut hdrs : Array (String × String) := #[]
    let mut isChunked := false
    let mut connClose := false
    let mut contentLen? : Option Nat := none
    for idx in [1:lines.size] do
      if h : idx < lines.size then
        if let some (k, v) := splitHeaderKv lines[idx] then
          let kl := k.toLower
          if kl == "content-length" then
            let some cl := parseStrictU64 v (256 * 1024 * 1024)
              | throw "invalid Content-Length in HTTP response"
            if let some prev := contentLen? then
              if prev != cl then throw "conflicting Content-Length in HTTP response"
            contentLen? := some cl
          else if kl == "transfer-encoding" && containsCI v "chunked" then
            isChunked := true
          else if kl == "connection" && containsCI v "close" then
            connClose := true
          hdrs := hdrs.push (k, v)
    return { status, headers := hdrs, isChunked, connClose, contentLen := contentLen? }

end Qed.Server.Net
