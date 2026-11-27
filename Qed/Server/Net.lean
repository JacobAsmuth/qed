import Qed.Base64
import Qed.Server.Core

namespace Qed.Server.Net

/-! ## Shared Byte, ASCII & HTTP/1.1 Framing Primitives -/

@[inline] private def isOwsByte (b : UInt8) : Bool := b == 32 || b == 9
@[inline] private def isAsciiWsByte (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 13

@[inline] private def rtrimPos (p : UInt8 → Bool) (s : String) (lo : Nat) (j : Nat) (hj : j ≤ s.utf8ByteSize) : Nat :=
  if _ : lo < j then if p (s.getUTF8Byte ⟨j - 1⟩ (show j - 1 < s.utf8ByteSize by omega)) then rtrimPos p s lo (j - 1) (by omega) else j else j
termination_by j

@[inline] private def trimRangeBytes (p : UInt8 → Bool) (s : String) (lo0 hi0 : Nat) : Nat × Nat :=
  let hiCap := min hi0 s.utf8ByteSize
  let rec scanLo (i : Nat) : Nat :=
    if h : i < hiCap then if p (s.getUTF8Byte ⟨i⟩ (Nat.lt_of_lt_of_le h (Nat.min_le_right _ _))) then scanLo (i + 1) else i else i
  termination_by min hi0 s.utf8ByteSize - i
  let lo := scanLo lo0
  (lo, rtrimPos p s lo hiCap (Nat.min_le_right _ _))

@[inline] private def trimBy (p : UInt8 → Bool) (s : String) : String :=
  let (lo, hi) := trimRangeBytes p s 0 s.utf8ByteSize
  if lo == 0 && hi == s.utf8ByteSize then s else String.Pos.Raw.extract s ⟨lo⟩ ⟨hi⟩
def trimWs  (s : String) : String := trimBy isAsciiWsByte s
def trimOws (s : String) : String := trimBy isOwsByte s
def stripTrailingSlashes (s : String) : String :=
  let hi := rtrimPos (· == 47) s 0 s.utf8ByteSize (Nat.le_refl _)
  if hi == s.utf8ByteSize then s else String.Pos.Raw.extract s ⟨0⟩ ⟨hi⟩

@[inline] def asciiLowerByte (b : UInt8) : UInt8 := if b >= 65 && b <= 90 then b ||| 32 else b

@[inline] def eqCIRange (a : String) (aLo aHi : Nat) (b : String) (bLo bHi : Nat) : Bool :=
  let len := aHi - aLo
  if h : aLo ≤ aHi ∧ bLo ≤ bHi ∧ len = bHi - bLo ∧ aHi ≤ a.utf8ByteSize ∧ bHi ≤ b.utf8ByteSize then
    let rec go (k : Nat) : Bool :=
      if hk : k < len then
        if asciiLowerByte (a.getUTF8Byte ⟨aLo + k⟩ (show aLo + k < a.utf8ByteSize by omega)) ==
           asciiLowerByte (b.getUTF8Byte ⟨bLo + k⟩ (show bLo + k < b.utf8ByteSize by omega)) then go (k + 1) else false
      else true
    termination_by aHi - aLo - k
    go 0
  else false

@[inline] def eqCI (a b : String) : Bool := a.utf8ByteSize == b.utf8ByteSize && eqCIRange a 0 a.utf8ByteSize b 0 b.utf8ByteSize
@[inline] def startsWithCI (s pfx : String) : Bool := s.utf8ByteSize ≥ pfx.utf8ByteSize && eqCIRange s 0 pfx.utf8ByteSize pfx 0 pfx.utf8ByteSize

@[inline] def findByteInRange (s : String) (start hi : Nat) (target : UInt8) : Option Nat :=
  let hiCap := min hi s.utf8ByteSize
  let rec go (i : Nat) : Option Nat :=
    if h : i < hiCap then if s.getUTF8Byte ⟨i⟩ (Nat.lt_of_lt_of_le h (Nat.min_le_right _ _)) == target then some i else go (i + 1) else none
  termination_by min hi s.utf8ByteSize - i
  go start
@[inline] def findByte (s : String) (start : Nat) (target : UInt8) : Option Nat := findByteInRange s start s.utf8ByteSize target
@[inline] def hasByteInRange (s : String) (lo hi : Nat) (target : UInt8) : Bool := (findByteInRange s lo hi target).isSome

def containsCI (haystack needle : String) : Bool :=
  let nLen := needle.utf8ByteSize
  if nLen == 0 || haystack.utf8ByteSize < nLen then false
  else
    let rec go (i : Nat) : Bool :=
      if _ : i + nLen ≤ haystack.utf8ByteSize ∧ i < haystack.utf8ByteSize then
        if eqCIRange haystack i (i + nLen) needle 0 nLen then true else go (i + 1) else false
    termination_by haystack.utf8ByteSize - i
    go 0

/-! ## Shared Big-Endian Binary Helpers -/

def pushU16BE (ba : ByteArray) (n : Nat) : ByteArray := (ba.push (UInt8.ofNat ((n >>> 8) &&& 0xFF))).push (UInt8.ofNat (n &&& 0xFF))
def pushU32BE (ba : ByteArray) (n : Nat) : ByteArray := pushU16BE (pushU16BE ba (n >>> 16)) n
def readU16BE (ba : ByteArray) (off : Nat) : Option Nat :=
  if h : off + 1 < ba.size then some (((ba[off]'(by omega)).toNat <<< 8) ||| (ba[off + 1]'h).toNat) else none
def readU32BE (ba : ByteArray) (off : Nat) : Option Nat :=
  if h : off + 3 < ba.size then
    some (((ba[off]'(by omega)).toNat <<< 24) ||| ((ba[off + 1]'(by omega)).toNat <<< 16) |||
          ((ba[off + 2]'(by omega)).toNat <<< 8) ||| (ba[off + 3]'h).toNat)
  else none

def byteArrayContains (ba : ByteArray) (target : UInt8) : Bool :=
  let rec go (i : Nat) : Bool := if h : i < ba.size then if ba[i] == target then true else go (i + 1) else false
  termination_by ba.size - i
  go 0
def findCrlf (ba : ByteArray) (start : Nat) : Option Nat :=
  let rec go (i : Nat) : Option Nat := if h : i + 1 < ba.size then if ba[i] == 13 && ba[i + 1] == 10 then some i else go (i + 1) else none
  termination_by ba.size - i
  go start
def findCrlfCrlf (ba : ByteArray) (start : Nat := 0) : Option Nat :=
  let rec go (i : Nat) : Option Nat :=
    if h : i + 3 < ba.size then if ba[i] == 13 && ba[i + 1] == 10 && ba[i + 2] == 13 && ba[i + 3] == 10 then some i else go (i + 1) else none
  termination_by ba.size - i
  go start

private def anyUtf8ByteLoop (s : String) (p : UInt8 → Bool) (i : Nat) : Nat → Bool
  | 0 => false
  | fuel + 1 => if h : i < s.utf8ByteSize then if p (s.getUTF8Byte ⟨i⟩ h) then true else anyUtf8ByteLoop s p (i + 1) fuel else false
@[inline] private def anyUtf8Byte (s : String) (p : UInt8 → Bool) : Bool := anyUtf8ByteLoop s p 0 s.utf8ByteSize
def hasCtlOrCrlf (s : String) (allowTab : Bool) : Bool :=
  anyUtf8Byte s fun b => b == 13 || b == 10 || b == 127 || (b < 32 && !(allowTab && b == 9))
@[inline] private def isTokenByte (b : UInt8) : Bool :=
  b > 32 && b < 127 &&
  !(b == 40 || b == 41 || b == 60 || b == 62 || b == 64 || b == 44 || b == 59 || b == 58 ||
    b == 92 || b == 34 || b == 47 || b == 91 || b == 93 || b == 63 || b == 61 || b == 123 || b == 125)
def isValidHttpToken (s : String) : Bool := s.utf8ByteSize > 0 && !anyUtf8Byte s (!isTokenByte ·)

def parseStrictU64 (s : String) (maxVal : UInt64) : Option Nat :=
  let (lo, hi0) := trimRangeBytes isOwsByte s 0 s.utf8ByteSize; let hi := min hi0 s.utf8ByteSize
  if lo >= hi then none
  else
    let rec go (i : Nat) (acc : UInt64) : Option Nat :=
      if h : i < hi then
        let b := s.getUTF8Byte ⟨i⟩ (Nat.lt_of_lt_of_le h (Nat.min_le_right _ _))
        if b >= 48 && b <= 57 then
          let d : UInt64 := (b - 48).toUInt64; if acc > (maxVal - d) / 10 then none else go (i + 1) (acc * 10 + d)
        else none
      else some acc.toNat
    termination_by min hi0 s.utf8ByteSize - i
    go lo 0
def parseHexSize (s : String) (maxVal : Nat := 268435456) : Option Nat :=
  let cs := (trimOws ((s.splitOn ";").headD "")).toList
  if cs.isEmpty then none else cs.foldlM (init := 0) fun acc c => do
    let d ← Qed.hexVal c; if acc > (maxVal - d) / 16 then none else some (acc * 16 + d)

private def splitCrlfLinesGo (s : String) (i lineStart : Nat) (acc : Array String) : Except String (Array String) :=
  if h : i < s.utf8ByteSize then
    let b := s.getUTF8Byte ⟨i⟩ h
    if b == 0 then .error "invalid NUL byte in headers" else if b == 10 then .error "bare LF in headers"
    else if b == 13 then
      if h2 : i + 1 < s.utf8ByteSize then
        if s.getUTF8Byte ⟨i + 1⟩ h2 == 10 then splitCrlfLinesGo s (i + 2) (i + 2) (acc.push (String.Pos.Raw.extract s ⟨lineStart⟩ ⟨i⟩))
        else .error "bare CR in headers"
      else .error "bare CR in headers"
    else splitCrlfLinesGo s (i + 1) lineStart acc
  else .ok (if lineStart < s.utf8ByteSize then acc.push (String.Pos.Raw.extract s ⟨lineStart⟩ ⟨s.utf8ByteSize⟩) else acc)
termination_by s.utf8ByteSize - i
def splitCrlfLines (ba : ByteArray) : Except String (Array String) :=
  (String.fromUTF8? ba).elim (.error "invalid UTF-8 in headers") (splitCrlfLinesGo · 0 0 (Array.mkEmpty 12))
private theorem byteArrayContains_go_eq (ba : ByteArray) (target : UInt8) (i : Nat) :
    byteArrayContains.go ba target i = true → ∃ k, i ≤ k ∧ ∃ (hk : k < ba.size), ba[k]'hk = target := by
  fun_induction byteArrayContains.go ba target i with
  | case1 i h hhit => exact fun _ => ⟨i, Nat.le_refl _, h, beq_iff_eq.1 hhit⟩
  | case2 i _ _ ih => exact fun ht => let ⟨k, hle, hk, heq⟩ := ih ht; ⟨k, by omega, hk, heq⟩
  | case3 _ _ => intro h; cases h
private theorem splitCrlfLinesGo_rejects_nul (s : String) (i lineStart : Nat) (acc : Array String)
    (k : Nat) (hle : i ≤ k) (hk : k < s.utf8ByteSize) (hz : s.getUTF8Byte ⟨k⟩ hk = 0) :
    ∃ e, splitCrlfLinesGo s i lineStart acc = .error e := by
  fun_induction splitCrlfLinesGo s i lineStart acc with
  | case1 | case2 | case4 | case5 => exact ⟨_, rfl⟩
  | case3 i _ _ _ b hb0 _ _ _ hb10' ih =>
      have : k ≠ i := fun heq => hb0 (by subst heq; simp [b, hz])
      have : k ≠ i + 1 := fun heq => by subst heq; exact absurd ((beq_iff_eq.1 hb10').symm.trans hz) (by decide)
      exact ih (by omega)
  | case6 i _ _ _ b hb0 _ _ ih => exact ih (by have : k ≠ i := fun heq => hb0 (by subst heq; simp [b, hz]); omega)
  | case7 _ _ _ hge => exact absurd (Nat.lt_of_le_of_lt hle hk) hge
theorem splitCrlfLines_rejects_nul (ba : ByteArray) (hnul : byteArrayContains ba 0 = true) :
    ∃ e, splitCrlfLines ba = .error e := by
  unfold splitCrlfLines; cases hf : String.fromUTF8? ba with
  | none => exact ⟨_, rfl⟩
  | some s =>
      have hba : s.toByteArray = ba := by unfold String.fromUTF8? at hf; split at hf <;> cases hf; rfl
      rcases byteArrayContains_go_eq ba 0 0 hnul with ⟨k, _, hk, hz⟩
      have hk' : k < s.utf8ByteSize := by rw [← String.size_toByteArray, hba]; exact hk
      exact splitCrlfLinesGo_rejects_nul s 0 0 _ k (Nat.zero_le _) hk' (by change s.toByteArray[k] = 0; subst hba; exact hz)
def splitHeaderKv (line : String) : Option (String × String) :=
  (findByte line 0 58).map fun cIdx =>
    let (lo, hi) := trimRangeBytes isOwsByte line (cIdx + 1) line.utf8ByteSize
    (String.Pos.Raw.extract line ⟨0⟩ ⟨cIdx⟩, String.Pos.Raw.extract line ⟨lo⟩ ⟨hi⟩)

/-! ## Formally Verified SSRF IP CIDR Policy (`isBlockedIpBytes`) -/

def isBlockedIpv4 (b0 b1 b2 _b3 : UInt8) : Bool :=
  b0 == 0 || b0 == 10 || (b0 == 100 && (b1 &&& 0xC0) == 64) || b0 == 127 || (b0 == 169 && b1 == 254) ||
  (b0 == 172 && (b1 &&& 0xF0) == 16) || (b0 == 192 && b1 == 0 && (b2 == 0 || b2 == 2)) || (b0 == 192 && b1 == 168) ||
  (b0 == 198 && (b1 &&& 0xFE) == 18) || (b0 == 198 && b1 == 51 && b2 == 100) || (b0 == 203 && b1 == 0 && b2 == 113) || b0 >= 224
private def allZeroRange (addr : ByteArray) (lo : Nat) : Nat → Bool
  | 0 => true | k + 1 => if h : lo < addr.size then addr[lo] == 0 && allZeroRange addr (lo + 1) k else false
def isBlockedIpBytes (addr : ByteArray) : Bool :=
  if h4 : addr.size = 4 then isBlockedIpv4 (addr[0]'(by omega)) (addr[1]'(by omega)) (addr[2]'(by omega)) (addr[3]'(by omega))
  else if h16 : addr.size = 16 then
    let b (i : Fin 16) : UInt8 := addr[i.val]'(by omega)
    let (b0, b1, b2, b3, b12, b13, b14, b15) := (b 0, b 1, b 2, b 3, b 12, b 13, b 14, b 15)
    let isNat64Pfx := b0 == 0x00 && b1 == 0x64 && b2 == 0xFF && b3 == 0x9B
    if allZeroRange addr 0 12 then (b12 == 0 && b13 == 0 && b14 == 0 && b15 <= 1) || isBlockedIpv4 b12 b13 b14 b15
    else if (b0 &&& 0xFE) == 0xFC || (b0 == 0xFE && ((b1 &&& 0xC0) == 0x80 || (b1 &&& 0xC0) == 0xC0)) ||
            b0 == 0xFF || (b0 == 0x01 && b1 == 0x00 && allZeroRange addr 2 6) || (b0 == 0x20 && b1 == 0x02) ||
            (b0 == 0x20 && b1 == 0x01 && ((b2 == 0x0D && b3 == 0xB8) || (b2 == 0x00 && b3 == 0x00))) ||
            (isNat64Pfx && b 4 == 0x00 && b 5 == 0x01) then true
    else if (allZeroRange addr 0 10 && b 10 == 0xFF && b 11 == 0xFF) || (isNat64Pfx && allZeroRange addr 4 8) then
      isBlockedIpv4 b12 b13 b14 b15
    else false
  else true
private theorem isBlockedIpBytes_v4 (b0 b1 b2 b3 : UInt8) : isBlockedIpBytes (ByteArray.mk #[b0, b1, b2, b3]) = isBlockedIpv4 b0 b1 b2 b3 := by
  simp only [isBlockedIpBytes, ByteArray.getElem_eq_getElem_data]; simp [ByteArray.size, -ByteArray.size_data]
theorem isBlockedIpBytes_loopback_v4 (b1 b2 b3 : UInt8) : isBlockedIpBytes (ByteArray.mk #[127, b1, b2, b3]) = true := by rw [isBlockedIpBytes_v4]; simp [isBlockedIpv4]
theorem isBlockedIpBytes_metadata_v4 (b2 b3 : UInt8) : isBlockedIpBytes (ByteArray.mk #[169, 254, b2, b3]) = true := by rw [isBlockedIpBytes_v4]; simp [isBlockedIpv4]
theorem isBlockedIpBytes_rfc1918_10 (b1 b2 b3 : UInt8) : isBlockedIpBytes (ByteArray.mk #[10, b1, b2, b3]) = true := by rw [isBlockedIpBytes_v4]; simp [isBlockedIpv4]
theorem isBlockedIpBytes_testnet_v4 (b3 : UInt8) : isBlockedIpBytes (ByteArray.mk #[192, 0, 2, b3]) = true := by rw [isBlockedIpBytes_v4]; simp [isBlockedIpv4]
theorem isBlockedIpBytes_benchmark_v4 (b2 b3 : UInt8) : isBlockedIpBytes (ByteArray.mk #[198, 18, b2, b3]) = true := by rw [isBlockedIpBytes_v4]; simp [isBlockedIpv4]
theorem isBlockedIpBytes_loopback_v6 : isBlockedIpBytes (ByteArray.mk #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]) = true := rfl
theorem isBlockedIpBytes_v4mapped_metadata : isBlockedIpBytes (ByteArray.mk #[0,0,0,0,0,0,0,0,0,0,0xFF,0xFF,169,254,169,254]) = true := rfl
theorem isBlockedIpBytes_nat64_metadata : isBlockedIpBytes (ByteArray.mk #[0,0x64,0xFF,0x9B,0,0,0,0,0,0,0,0,169,254,169,254]) = true := rfl
theorem isBlockedIpBytes_nat64_local_v6 : isBlockedIpBytes (ByteArray.mk #[0,0x64,0xFF,0x9B,0,1,0,0,0,0,0,0,10,0,0,1]) = true := rfl
theorem isBlockedIpBytes_6to4_v6 : isBlockedIpBytes (ByteArray.mk #[0x20,0x02,169,254,169,254,0,0,0,0,0,0,0,0,0,1]) = true := rfl
theorem isBlockedIpBytes_teredo_v6 : isBlockedIpBytes (ByteArray.mk #[0x20,0x01,0,0,0,0,0,0,0,0,0,0,0,0,0,1]) = true := rfl
theorem isBlockedIpBytes_badLen (addr : ByteArray) (h4 : addr.size ≠ 4) (h16 : addr.size ≠ 16) : isBlockedIpBytes addr = true := by simp [isBlockedIpBytes, h4, h16]

abbrev base64Encode : ByteArray → String := Qed.Base64.encode
theorem base64UrlEncode_safe (bs : ByteArray) : (Qed.Base64.encodeUrl bs).toList.all Qed.Base64.isUrlChar = true := Qed.Base64.encodeUrl_safe bs

/-! ## Outbound HTTP/1.1 URL Parser, Request Serializer & Response Head Parser -/

structure ParsedUrl where (isTls : Bool) (host : String) (isIpv6 : Bool) (port : UInt16) (pathAndQuery : String)

private def parsePortU16 (s : String) : Option UInt16 := do let n ← parseStrictU64 s 65535; if n == 0 then none else some (UInt16.ofNat n)
private def splitAuthorityAndPathGo (authRev : List Char) : List Char → Option (String × String)
  | [] => some (String.ofList authRev.reverse, "/") | '#' :: _ => none
  | '?' :: tail => some (String.ofList authRev.reverse, String.ofList ('/' :: '?' :: tail.takeWhile (· != '#')))
  | '/' :: tail => some (String.ofList authRev.reverse, String.ofList ('/' :: tail.takeWhile (· != '#')))
  | c :: tail => splitAuthorityAndPathGo (c :: authRev) tail
private theorem not_mem_takeWhile_ne_hash : ∀ cs : List Char, '#' ∉ cs.takeWhile (· != '#')
  | [] => by simp
  | c :: rest => by
      simp only [List.takeWhile]; split
      · rename_i h; simp only [List.mem_cons, not_or]; exact ⟨fun heq => by subst heq; simp at h, not_mem_takeWhile_ne_hash rest⟩
      · simp
private theorem splitAuthorityAndPathGo_no_hash (authRev cs : List Char) (auth path : String)
    (h : splitAuthorityAndPathGo authRev cs = some (auth, path)) : '#' ∉ path.toList := by
  fun_induction splitAuthorityAndPathGo authRev cs with
  | case1 => cases h; decide | case2 => cases h | case3 | case4 => cases h; simp [not_mem_takeWhile_ne_hash] | case5 _ _ _ _ _ _ ih => exact ih h

def isIdempotentHttpMethod (method : String) : Bool := method == "GET" || method == "HEAD" || method == "PUT" || method == "DELETE" || method == "OPTIONS"

def parseHostPort (url auth : String) (defaultPort : UInt16) : Except String (String × Bool × UInt16) := do
  if auth.isEmpty || auth.utf8ByteSize >= 256 || auth.contains '@' || auth.contains '\\' then throw s!"invalid URL authority: {url}"
  let (host, isIpv6, portStr?) ←
    if auth.startsWith "[" then match auth.splitOn "]" with
      | [left, right] =>
          let h := String.ofList (left.toList.drop 1)
          if right.isEmpty then pure (h, true, none) else if right.startsWith ":" then pure (h, true, some (String.ofList (right.toList.drop 1)))
          else throw s!"invalid IPv6 authority: {url}"
      | _ => throw s!"malformed IPv6 authority: {url}"
    else match auth.splitOn ":" with | [h] => pure (h, false, none) | [h, p] => pure (h, false, some p) | _ => throw s!"invalid URL authority: {url}"
  if host.isEmpty then throw s!"empty URL host: {url}"
  return (host, isIpv6, ← portStr?.elim (pure defaultPort) fun ps => (parsePortU16 ps).elim (.error s!"invalid URL port: {url}") .ok)

def parseHttpUrl (url : String) : Except String ParsedUrl :=
  if hasCtlOrCrlf url false || url.contains ' ' then .error s!"invalid outbound HTTP URL: {url}"
  else
    let scheme? := if url.startsWith "https://" then some (true, (443 : UInt16), 8) else if url.startsWith "http://" then some (false, (80 : UInt16), 7) else none
    match scheme? with
    | none => .error s!"unsupported URL scheme: {url}"
    | some (isTls, defPort, dropLen) => match splitAuthorityAndPathGo [] (url.toList.drop dropLen) with
        | some (auth, path) => (parseHostPort url auth defPort).map fun (host, isIpv6, port) => { isTls, host, isIpv6, port, pathAndQuery := path }
        | none => .error s!"invalid URL authority: {url}"

theorem parseHttpUrl_no_fragment (url : String) (u : ParsedUrl) (h : parseHttpUrl url = .ok u) : '#' ∉ u.pathAndQuery.toList := by
  unfold parseHttpUrl at h; split at h <;> try cases h
  dsimp only at h; split at h <;> try cases h
  split at h <;> try cases h
  rename_i hsp; dsimp only [Except.map] at h; split at h <;> try cases h
  exact splitAuthorityAndPathGo_no_hash [] _ _ _ hsp

def formatOutboundRequest (method : String) (u : ParsedUrl) (headers : Array (String × String)) (body : ByteArray) :
    Except String ByteArray := do
  if !isValidHttpToken method then throw "invalid outbound HTTP method"
  if u.host.isEmpty || hasCtlOrCrlf u.host false || u.host.contains ' ' || u.port == 0 ||
     !u.pathAndQuery.startsWith "/" || hasCtlOrCrlf u.pathAndQuery false || u.pathAndQuery.contains ' ' then
    throw "invalid outbound HTTP URL fields"
  if headers.any fun (k, v) => !isValidHttpToken k || hasCtlOrCrlf v true then throw "invalid outbound HTTP header (CRLF/control chars)"
  let defaultPort := (u.isTls && u.port == 443) || (!u.isTls && u.port == 80)
  let hostHdr := (if u.isIpv6 then s!"[{u.host}]" else u.host) ++ (if defaultPort then "" else s!":{u.port}")
  let head := headers.foldl (init := s!"{method} {u.pathAndQuery} HTTP/1.1\r\nHost: {hostHdr}\r\nConnection: keep-alive\r\nContent-Length: {body.size}\r\n") fun acc (k, v) =>
    if eqCI k "host" || eqCI k "content-length" || eqCI k "connection" || eqCI k "transfer-encoding" then acc else acc ++ s!"{k}: {v}\r\n"
  return (head ++ "\r\n").toUTF8 ++ body

structure ParsedRespHead where
  (status : Nat) (headers : Array (String × String)) (isChunked connClose : Bool) (contentLen : Option Nat)
private def parseStatusCode (s : String) : Option Nat :=
  match s.toList with
  | d0 :: d1 :: d2 :: rest =>
      if (match rest with | [] | ' ' :: _ | '\t' :: _ => true | _ => false) &&
         '1' ≤ d0 && d0 ≤ '9' && '0' ≤ d1 && d1 ≤ '9' && '0' ≤ d2 && d2 ≤ '9' then
        some ((d0.toNat - 48) * 100 + (d1.toNat - 48) * 10 + (d2.toNat - 48)) else none
  | _ => none
private def parseRespHdrLines (lines : Array String) (status : Nat) (idx : Nat) (hdrs : Array (String × String))
    (isChunked connClose : Bool) (contentLen? : Option Nat) : Except String ParsedRespHead :=
  if h : idx < lines.size then
    match splitHeaderKv lines[idx] with
    | none => parseRespHdrLines lines status (idx + 1) hdrs isChunked connClose contentLen?
    | some (k, v) =>
        if eqCI k "content-length" then
          match parseStrictU64 v (256 * 1024 * 1024) with
          | none => .error "invalid Content-Length in HTTP response"
          | some cl =>
              if contentLen?.any (· != cl) then .error "conflicting Content-Length in HTTP response"
              else parseRespHdrLines lines status (idx + 1) (hdrs.push (k, v)) isChunked connClose (some cl)
        else
          let ch := isChunked || (eqCI k "transfer-encoding" && containsCI v "chunked")
          let cc := connClose || (eqCI k "connection" && containsCI v "close")
          parseRespHdrLines lines status (idx + 1) (hdrs.push (k, v)) ch cc contentLen?
  else .ok { status, headers := hdrs, isChunked, connClose, contentLen := contentLen? }
termination_by lines.size - idx
def parseHttpResponseHead (headBytes : ByteArray) : Except String ParsedRespHead := do
  let lines ← splitCrlfLines headBytes
  if h0 : lines.size = 0 then throw "empty HTTP response status line"
  else
    let statusLine := lines[0]'(by omega)
    if !statusLine.startsWith "HTTP/" then throw "invalid HTTP status line"
    let status ← match statusLine.splitOn " " with
      | _ :: codeRest :: _ => (parseStatusCode codeRest).elim (.error "invalid HTTP status code") .ok
      | _ => throw "invalid HTTP status line"
    parseRespHdrLines lines status 1 (Array.mkEmpty (lines.size - 1)) false false none
@[inline] def liftE  {ε α : Type} (x : IO (Except ε α)) : ExceptT ε IO α := ExceptT.mk x
@[inline] def liftP  {ε α : Type} (x : Except ε α)      : ExceptT ε IO α := ExceptT.mk (pure x)
@[inline] def liftIO {ε α : Type} (x : IO α)            : ExceptT ε IO α := liftM x
end Qed.Server.Net
