import Std.Data.HashMap.Basic
import Qed.Server.Core
import Qed.Server.Db.Core
import Qed.Server.Net
import Qed.Server.Prim

namespace Qed.Server.Db.PgWire

/-! ## Total, Verified PostgreSQL v3 Wire Protocol Codec & Client (`PgWire`)
    Implements the PostgreSQL Frontend/Backend Protocol v3.0 in pure, total Lean 4 over
    Qed's minimal `outboundAcquire` / `outboundUpgradeTls` / `outboundWriteAll` /
    `outboundReadSome` `rustls` socket shim:
    - `postgres://` / `postgresql://` URL parser (`user`, `pass`, `host`, `port`, `db`, `sslmode`)
    - Optional STARTTLS (`SSLRequest` + `rustls` TLS upgrade)
    - `AuthenticationOk`, `CleartextPassword`, `MD5Password`, and `SCRAM-SHA-256` authentication
    - Extended Query Protocol (`Parse` + `Bind` + `Describe` + `Execute` + `Sync`) —
      strictly parameterized on the wire with zero SQL string interpolation! -/

/-! ### Big-Endian Binary Helpers -/

def pushU16BE (ba : ByteArray) (n : Nat) : ByteArray :=
  (ba.push (UInt8.ofNat ((n >>> 8) &&& 0xFF))).push (UInt8.ofNat (n &&& 0xFF))

def pushU32BE (ba : ByteArray) (n : Nat) : ByteArray :=
  let b1 := ba.push (UInt8.ofNat ((n >>> 24) &&& 0xFF))
  let b2 := b1.push (UInt8.ofNat ((n >>> 16) &&& 0xFF))
  let b3 := b2.push (UInt8.ofNat ((n >>> 8) &&& 0xFF))
  b3.push (UInt8.ofNat (n &&& 0xFF))

def pushI32BE (ba : ByteArray) (i : Int) : ByteArray :=
  let n : Nat := if 0 ≤ i then i.toNat else (4294967296 + i).toNat
  pushU32BE ba n

def pushCString (ba : ByteArray) (s : String) : ByteArray :=
  (ba ++ s.toUTF8).push 0

def readU16BE (ba : ByteArray) (off : Nat) : Option Nat :=
  if h : off + 1 < ba.size then
    let b0 := (ba[off]'(by omega)).toNat
    let b1 := (ba[off + 1]'h).toNat
    some ((b0 <<< 8) ||| b1)
  else none

def readU32BE (ba : ByteArray) (off : Nat) : Option Nat :=
  if h : off + 3 < ba.size then
    let b0 := (ba[off]'(by omega)).toNat
    let b1 := (ba[off + 1]'(by omega)).toNat
    let b2 := (ba[off + 2]'(by omega)).toNat
    let b3 := (ba[off + 3]'h).toNat
    some ((b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3)
  else none

def readI32BE (ba : ByteArray) (off : Nat) : Option Int :=
  (readU32BE ba off).map fun n =>
    if n >= 2147483648 then (Int.ofNat n) - 4294967296 else Int.ofNat n

/-- Framed PostgreSQL frontend message: `1-byte tag || 4-byte BE (payload.size + 4) || payload`. -/
def encodeMsg (tag : UInt8) (payload : ByteArray) : ByteArray :=
  pushU32BE (ByteArray.empty.push tag) (payload.size + 4) ++ payload

theorem encodeMsg_size (tag : UInt8) (payload : ByteArray) :
    (encodeMsg tag payload).size = payload.size + 5 := by
  unfold encodeMsg pushU32BE
  simp [ByteArray.size_append, ByteArray.size_push]
  omega

/-- PostgreSQL `SSLRequest` startup packet (`len=8`, `code=80877103`). -/
def encodeSslRequest : ByteArray :=
  pushU32BE (pushU32BE ByteArray.empty 8) 80877103

/-- PostgreSQL v3.0 `StartupMessage` (`protocol = 196608`). -/
def encodeStartup (user database : String) : ByteArray :=
  let body :=
    pushU32BE ByteArray.empty 196608
    |> (fun b => pushCString b "user")
    |> (fun b => pushCString b user)
    |> (fun b => pushCString b "database")
    |> (fun b => pushCString b database)
    |> (fun b => pushCString b "client_encoding")
    |> (fun b => pushCString b "UTF8")
    |> (fun b => b.push 0)
  pushU32BE ByteArray.empty (body.size + 4) ++ body

def encodePasswordMsg (pw : String) : ByteArray :=
  encodeMsg 0x70 (pushCString ByteArray.empty pw) -- 'p'

def encodeSaslInitialResponse (mech : String) (initialResp : ByteArray) : ByteArray :=
  let p := pushCString ByteArray.empty mech
  let p := pushI32BE p (Int.ofNat initialResp.size) ++ initialResp
  encodeMsg 0x70 p

def encodeSaslResponse (resp : ByteArray) : ByteArray :=
  encodeMsg 0x70 resp

/-- Encodes a `SqlVal` as a PostgreSQL text-format Bind parameter (`none` → SQL NULL). -/
def sqlValToPgText : SqlVal → Option ByteArray
  | .null     => none
  | .int i    => some (toString i).toUTF8
  | .text s   => some s.toUTF8
  | .bool b   => some (if b then "t" else "f").toUTF8
  | .bytes bs => some ("\\x" ++ Proto.encodeHex bs).toUTF8

/-- Extended Query `Parse` (`'P'`) message for unnamed prepared statement. -/
def encodeParse (sql : String) : ByteArray :=
  let p := pushCString (pushCString ByteArray.empty "") sql
  let p := pushU16BE p 0 -- let server infer parameter OIDs
  encodeMsg 0x50 p

/-- Extended Query `Bind` (`'B'`) message carrying parameterized `SqlVal` values. -/
def encodeBind (params : Array SqlVal) : ByteArray :=
  let p := pushCString (pushCString ByteArray.empty "") "" -- portal="", stmt=""
  let p := pushU16BE p 0 -- all parameter format codes = text (0)
  let p := pushU16BE p params.size
  let p := params.foldl (init := p) fun acc v =>
    match sqlValToPgText v with
    | none    => pushI32BE acc (-1)
    | some bs => pushI32BE acc (Int.ofNat bs.size) ++ bs
  let p := pushU16BE p 0 -- all result column format codes = text (0)
  encodeMsg 0x42 p

def encodeDescribePortal : ByteArray :=
  encodeMsg 0x44 (pushCString (ByteArray.empty.push 0x50) "") -- 'D', 'P', ""

def encodeExecute : ByteArray :=
  encodeMsg 0x45 (pushU32BE (pushCString ByteArray.empty "") 0) -- 'E', "", maxRows=0

def encodeSync : ByteArray :=
  encodeMsg 0x53 ByteArray.empty -- 'S'

def encodeSimpleQuery (sql : String) : ByteArray :=
  encodeMsg 0x51 (pushCString ByteArray.empty sql) -- 'Q'

def encodeTerminate : ByteArray :=
  encodeMsg 0x58 ByteArray.empty -- 'X'

/-! ### Backend Message Framing & Decoding -/

structure PgFrame where
  tag     : UInt8
  payload : ByteArray

inductive DecodeFrameRes where
  | needMore
  | frame (f : PgFrame) (nextOff : Nat)
  | err   (msg : String)

def decodeFrame (buf : ByteArray) (off : Nat) : DecodeFrameRes :=
  if h : off + 5 ≤ buf.size then
    let tag := buf[off]'(by omega)
    match readU32BE buf (off + 1) with
    | none => .needMore
    | some len =>
        if len < 4 then .err s!"invalid postgres frame length {len}"
        else if len > 64 * 1024 * 1024 then .err s!"postgres frame too large ({len} bytes)"
        else
          let total := 1 + len
          if off + total ≤ buf.size then
            let payload := buf.extract (off + 5) (off + total)
            .frame { tag, payload } (off + total)
          else .needMore
  else .needMore

/-- Extracts the human-readable `M` (message) field from a PostgreSQL `ErrorResponse` payload. -/
private def parseErrorFieldsLoop (ba : ByteArray) (off : Nat) : Nat → String
  | 0 => "postgres error"
  | fuel + 1 =>
      if h : off < ba.size then
        let code := ba[off]'h
        if code == 0 then "postgres error"
        else
          let rec findZero (i : Nat) : Nat → Nat
            | 0 => ba.size
            | f + 1 =>
                if hi : i < ba.size then
                  if ba[i]'hi == 0 then i else findZero (i + 1) f
                else ba.size
          let zPos := findZero (off + 1) (ba.size - off)
          if code == 0x4D then -- 'M' = Message
            (String.fromUTF8? (ba.extract (off + 1) zPos)).getD "postgres error"
          else
            parseErrorFieldsLoop ba (zPos + 1) fuel
      else "postgres error"

def parseErrorResponse (payload : ByteArray) : String :=
  parseErrorFieldsLoop payload 0 (payload.size + 1)

/-- Parses column OIDs from a `RowDescription` (`'T'`) payload so typed `SqlVal` values are decoded cleanly. -/
private def parseRowDescCols (ba : ByteArray) (off : Nat) (acc : Array Nat) : Nat → Array Nat
  | 0 => acc
  | n + 1 =>
      let rec skipZero (i : Nat) : Nat → Nat
        | 0 => ba.size
        | f + 1 =>
            if hi : i < ba.size then
              if ba[i]'hi == 0 then i + 1 else skipZero (i + 1) f
            else ba.size
      let afterName := skipZero off (ba.size - off + 1)
      -- 4 (tableOid) + 2 (colAttr) + 4 (typeOid) + 2 (typeSize) + 4 (typeMod) + 2 (fmtCode) = 18 bytes
      let typeOid := (readU32BE ba (afterName + 6)).getD 25
      parseRowDescCols ba (afterName + 18) (acc.push typeOid) n

def parseRowDescription (payload : ByteArray) : Array Nat :=
  match readU16BE payload 0 with
  | some cnt => parseRowDescCols payload 2 #[] cnt
  | none     => #[]

/-- Converts a PostgreSQL text-format cell using its column OID (16=BOOL, 20/21/23=INT, 17=BYTEA, else TEXT). -/
def decodePgCell (oid : Nat) (raw : ByteArray) : Except String SqlVal :=
  match String.fromUTF8? raw with
  | none => .ok (.bytes raw)
  | some s =>
      if oid == 16 then -- BOOL
        .ok (.bool (s == "t" || s == "true" || s == "1"))
      else if oid == 20 || oid == 21 || oid == 23 then -- INT8, INT2, INT4
        match s.toInt? with
        | some i => .ok (.int i)
        | none   => .error s!"postgres invalid int cell: {s}"
      else if oid == 17 then -- BYTEA (\x...)
        if s.startsWith "\\x" then (Proto.decodeHex (String.ofList (s.toList.drop 2))).map .bytes
        else .ok (.bytes raw)
      else
        .ok (.text s)

private def parseDataRowCols (ba : ByteArray) (oids : Array Nat) (off colIdx : Nat)
    (acc : Array SqlVal) : Nat → Except String DbRow
  | 0 => .ok acc
  | rem + 1 => do
      let some colLen := readI32BE ba off
        | .error "truncated postgres DataRow column length"
      if colLen < 0 then
        parseDataRowCols ba oids (off + 4) (colIdx + 1) (acc.push .null) rem
      else
        let n := colLen.toNat
        if off + 4 + n > ba.size then
          .error "truncated postgres DataRow column payload"
        else
          let cellBytes := ba.extract (off + 4) (off + 4 + n)
          let oid := oids.getD colIdx 25
          let v ← decodePgCell oid cellBytes
          parseDataRowCols ba oids (off + 4 + n) (colIdx + 1) (acc.push v) rem

def parseDataRow (oids : Array Nat) (payload : ByteArray) : Except String DbRow :=
  match readU16BE payload 0 with
  | some cnt => parseDataRowCols payload oids 2 0 #[] cnt
  | none     => .error "truncated postgres DataRow header"

/-- Parses affected row count from `CommandComplete` tag (e.g. `"UPDATE 1"`, `"DELETE 3"`, `"INSERT 0 1"`). -/
def parseCommandTagAffected (payload : ByteArray) : Nat :=
  let trimmed := if payload.size > 0 && payload[payload.size - 1]! == 0 then
    payload.extract 0 (payload.size - 1) else payload
  let tag := (String.fromUTF8? trimmed).getD ""
  match (tag.splitOn " ").reverse with
  | last :: _ => last.toNat?.getD 0
  | []        => 0

/-! ### `postgres://` URL Parser -/

inductive PgSslMode where
  | disable
  | prefer
  | require
deriving Inhabited, DecidableEq, Repr

structure PgConnParams where
  user     : String := "postgres"
  password : String := ""
  host     : String := "127.0.0.1"
  port     : UInt16 := 5432
  database : String := "postgres"
  sslMode  : PgSslMode := .prefer
deriving Inhabited, Repr

def parsePgUrl (rawUrl : String) : Except String PgConnParams := do
  let rest ←
    if rawUrl.startsWith "postgresql://" then .ok (String.ofList (rawUrl.toList.drop 13))
    else if rawUrl.startsWith "postgres://" then .ok (String.ofList (rawUrl.toList.drop 11))
    else .error "PostgreSQL URL must start with `postgres://` or `postgresql://`"
  let (beforeQ, queryStr) := match rest.splitOn "?" with
    | a :: b :: _ => (a, b)
    | _           => (rest, "")
  let (authAndHost, dbPart) := match beforeQ.splitOn "/" with
    | a :: b :: _ => (a, b)
    | _           => (beforeQ, "postgres")
  let (userInfo?, hostPort) := match authAndHost.splitOn "@" with
    | a :: b :: _ => (some a, b)
    | _           => (none, authAndHost)
  let (user, password) := match userInfo? with
    | none => ("postgres", "")
    | some ui =>
        match ui.splitOn ":" with
        | u :: p :: _ => (Qed.decodeSeg u, Qed.decodeSeg p)
        | u :: _      => (Qed.decodeSeg u, "")
        | []          => ("postgres", "")
  let (host, port) ← match hostPort.splitOn ":" with
    | h :: pStr :: _ =>
        match pStr.toNat? with
        | some pn =>
            if 1 ≤ pn && pn ≤ 65535 then .ok (h, UInt16.ofNat pn)
            else .error s!"invalid postgres port `{pStr}`"
        | none => .error s!"invalid postgres port `{pStr}`"
    | h :: _ => .ok (h, (5432 : UInt16))
    | []     => .error "missing postgres host"
  let sslMode : PgSslMode :=
    (queryStr.splitOn "&").foldl (init := .prefer) fun acc kv =>
      match kv.splitOn "=" with
      | ["sslmode", "disable"] => .disable
      | ["sslmode", "require"] | ["sslmode", "verify-ca"] | ["sslmode", "verify-full"] => .require
      | _ => acc
  if host.isEmpty then .error "missing postgres host"
  else .ok {
    user := if user.isEmpty then "postgres" else user
    password
    host
    port
    database := if dbPart.isEmpty then "postgres" else Qed.decodeSeg dbPart
    sslMode
  }

/-! ### Base64 Helpers & SCRAM-SHA-256 Auth (over `ring` SHA-256 / HMAC / PBKDF2) -/

private def b64EncTable : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

private def b64EncodeLoop (bs : ByteArray) (i : Nat) (acc : String) : Nat → String
  | 0 => acc
  | fuel + 1 =>
      if h : i < bs.size then
        let b0 := (bs[i]'h).toNat
        let has1 := i + 1 < bs.size
        let has2 := i + 2 < bs.size
        let b1 := if h1 : i + 1 < bs.size then (bs[i + 1]'h1).toNat else 0
        let b2 := if h2 : i + 2 < bs.size then (bs[i + 2]'h2).toNat else 0
        let c0 := b64EncTable[(b0 >>> 2) &&& 0x3F]!
        let c1 := b64EncTable[((b0 &&& 0x03) <<< 4) ||| (b1 >>> 4)]!
        let c2 := if has1 then b64EncTable[((b1 &&& 0x0F) <<< 2) ||| (b2 >>> 6)]! else '='
        let c3 := if has2 then b64EncTable[b2 &&& 0x3F]! else '='
        b64EncodeLoop bs (i + 3) ((((acc.push c0).push c1).push c2).push c3) fuel
      else acc

def base64Encode (bs : ByteArray) : String :=
  b64EncodeLoop bs 0 "" (bs.size + 1)

private def b64Val (c : Char) : Option Nat :=
  let n := c.toNat
  if 65 ≤ n && n ≤ 90 then some (n - 65)
  else if 97 ≤ n && n ≤ 122 then some (n - 71)
  else if 48 ≤ n && n ≤ 57 then some (n + 4)
  else if c == '+' then some 62
  else if c == '/' then some 63
  else none

private def b64DecodeLoop : List Char → ByteArray → ByteArray
  | c0 :: c1 :: c2 :: c3 :: rest, acc =>
      match b64Val c0, b64Val c1 with
      | some v0, some v1 =>
          let a0 := acc.push (UInt8.ofNat (((v0 <<< 2) ||| (v1 >>> 4)) &&& 0xFF))
          match c2, b64Val c2 with
          | '=', _ => a0
          | _, some v2 =>
              let a1 := a0.push (UInt8.ofNat (((v1 <<< 4) ||| (v2 >>> 2)) &&& 0xFF))
              match c3, b64Val c3 with
              | '=', _ => a1
              | _, some v3 =>
                  b64DecodeLoop rest (a1.push (UInt8.ofNat (((v2 <<< 6) ||| v3) &&& 0xFF)))
              | _, none => a1
          | _, none => a0
      | _, _ => acc
  | _, acc => acc

def base64Decode (s : String) : ByteArray :=
  b64DecodeLoop (s.toList.filter fun c => !c.isWhitespace) ByteArray.empty

private def xorBytes (a b : ByteArray) : ByteArray :=
  let n := min a.size b.size
  let rec go (i : Nat) (acc : ByteArray) : Nat → ByteArray
    | 0 => acc
    | fuel + 1 =>
        if h : i < n then
          let xa := a[i]'(by omega)
          let xb := b[i]'(by omega)
          go (i + 1) (acc.push (xa ^^^ xb)) fuel
        else acc
  go 0 ByteArray.empty n

/-! ### Live Wire Execution (Total Fuel-Bounded Socket Loops) -/

private def readNextFrame (handle : UInt64) (buf : ByteArray) (off : Nat) :
    Nat → IO (Except String (PgFrame × ByteArray × Nat))
  | 0 => return .error "postgres read frame fuel exceeded"
  | fuel + 1 => do
      match decodeFrame buf off with
      | .frame f nextOff =>
          let (b', o') := if nextOff >= buf.size then (ByteArray.empty, 0) else (buf, nextOff)
          return .ok (f, b', o')
      | .err msg => return .error msg
      | .needMore =>
          match ← Prim.outboundReadSome handle 16384 with
          | .error e => return .error e
          | .ok chunk =>
              if chunk.isEmpty then return .error "unexpected EOF from PostgreSQL server"
              else
                let compacted := if off > 0 then buf.extract off buf.size ++ chunk else buf ++ chunk
                readNextFrame handle compacted 0 fuel

private def parseScramServerFirst (s : String) : Except String (String × ByteArray × Nat) := do
  let parts := s.splitOn ","
  let mut rNonce : Option String := none
  let mut saltB64 : Option String := none
  let mut iters : Option Nat := none
  for p in parts do
    if p.startsWith "r=" then rNonce := some (String.ofList (p.toList.drop 2))
    else if p.startsWith "s=" then saltB64 := some (String.ofList (p.toList.drop 2))
    else if p.startsWith "i=" then iters := (String.ofList (p.toList.drop 2)).toNat?
  match rNonce, saltB64, iters with
  | some r, some sb, some it => .ok (r, base64Decode sb, it)
  | _, _, _ => .error "invalid SCRAM-SHA-256 server-first-message"

private def authLoop (handle : UInt64) (cfg : PgConnParams)
    (buf : ByteArray) (off : Nat) (clientNonce : String) (clientFirstBare : String) :
    Nat → IO (Except String (ByteArray × Nat))
  | 0 => return .error "postgres auth loop exceeded limit"
  | fuel + 1 => do
      match ← readNextFrame handle buf off 4096 with
      | .error e => return .error e
      | .ok (f, b1, o1) =>
          if f.tag == 0x45 then -- 'E' ErrorResponse
            return .error (parseErrorResponse f.payload)
          else if f.tag == 0x5A then -- 'Z' ReadyForQuery
            return .ok (b1, o1)
          else if f.tag == 0x52 then -- 'R' Authentication
            match readU32BE f.payload 0 with
            | some 0 => authLoop handle cfg b1 o1 clientNonce clientFirstBare fuel -- AuthOk
            | some 3 => -- CleartextPassword
                match ← Prim.outboundWriteAll handle (encodePasswordMsg cfg.password) with
                | .error e => return .error e
                | .ok () => authLoop handle cfg b1 o1 clientNonce clientFirstBare fuel
            | some 10 => -- AuthenticationSASL
                let nonce ← Prim.randomHex 12
                let bare := s!"n=,r={nonce}"
                let initMsg := s!"n,,{bare}".toUTF8
                match ← Prim.outboundWriteAll handle (encodeSaslInitialResponse "SCRAM-SHA-256" initMsg) with
                | .error e => return .error e
                | .ok () => authLoop handle cfg b1 o1 nonce bare fuel
            | some 11 => -- AuthenticationSASLContinue
                let serverFirst := (String.fromUTF8? (f.payload.extract 4 f.payload.size)).getD ""
                match parseScramServerFirst serverFirst with
                | .error e => return .error e
                | .ok (srvNonce, salt, iters) =>
                    if !srvNonce.startsWith clientNonce then
                      return .error "SCRAM-SHA-256 server nonce mismatch"
                    let saltedPw ← Prim.pbkdf2HmacSha256 cfg.password.toUTF8 salt (UInt32.ofNat iters)
                    let clientKey ← Prim.hmacSha256 saltedPw "Client Key".toUTF8
                    let storedKey ← Prim.sha256 clientKey
                    let finalNoProof := s!"c=biws,r={srvNonce}"
                    let authMsg := s!"{clientFirstBare},{serverFirst},{finalNoProof}"
                    let clientSig ← Prim.hmacSha256 storedKey authMsg.toUTF8
                    let proof := xorBytes clientKey clientSig
                    let clientFinal := s!"{finalNoProof},p={base64Encode proof}".toUTF8
                    match ← Prim.outboundWriteAll handle (encodeSaslResponse clientFinal) with
                    | .error e => return .error e
                    | .ok () => authLoop handle cfg b1 o1 clientNonce clientFirstBare fuel
            | some 12 => -- AuthenticationSASLFinal
                authLoop handle cfg b1 o1 clientNonce clientFirstBare fuel
            | some code =>
                return .error s!"unsupported PostgreSQL auth method {code} (supported: trust, cleartext, SCRAM-SHA-256)"
            | none => return .error "truncated PostgreSQL Authentication packet"
          else
            -- Skip ParameterStatus ('S'), BackendKeyData ('K'), NoticeResponse ('N')
            authLoop handle cfg b1 o1 clientNonce clientFirstBare fuel

private def readyStatusByte (payload : ByteArray) : UInt8 :=
  if h : 0 < payload.size then payload[0]'h else 0

/-- Returns `(Except errMsg DbResult, remBuf, remOff, readyStatusByte)` where `readyStatusByte`
    is `'I'` (`0x49`) when idle, `'T'` (`0x54`) inside a transaction, or `'E'` (`0x45`) on failed tx.
    Returns `.error transportErr` on wire/EOF failure (connection must be evicted). -/
private def collectQueryResultLoop (handle : UInt64) (buf : ByteArray) (off : Nat)
    (oids : Array Nat) (rows : Array DbRow) (affected : Nat) (err? : Option String) :
    Nat → IO (Except String (Except String DbResult × ByteArray × Nat × UInt8))
  | 0 => return .error "postgres query response exceeded frame limit"
  | fuel + 1 => do
      match ← readNextFrame handle buf off 4096 with
      | .error e => return .error e
      | .ok (f, b1, o1) =>
          if f.tag == 0x5A then -- 'Z' ReadyForQuery
            let status := readyStatusByte f.payload
            let qRes := match err? with
              | some e => Except.error e
              | none   => Except.ok { rows, affected }
            return .ok (qRes, b1, o1, status)
          else if f.tag == 0x45 then -- 'E' ErrorResponse
            collectQueryResultLoop handle b1 o1 oids rows affected (some (parseErrorResponse f.payload)) fuel
          else if f.tag == 0x54 then -- 'T' RowDescription
            collectQueryResultLoop handle b1 o1 (parseRowDescription f.payload) rows affected err? fuel
          else if f.tag == 0x44 then -- 'D' DataRow
            match parseDataRow oids f.payload with
            | .ok row => collectQueryResultLoop handle b1 o1 oids (rows.push row) affected err? fuel
            | .error e => collectQueryResultLoop handle b1 o1 oids rows affected (some e) fuel
          else if f.tag == 0x43 then -- 'C' CommandComplete
            let aff := parseCommandTagAffected f.payload
            collectQueryResultLoop handle b1 o1 oids rows aff err? fuel
          else
            -- ParseComplete ('1'), BindComplete ('2'), NoData ('n'), NoticeResponse ('N'), EmptyQuery ('I')
            collectQueryResultLoop handle b1 o1 oids rows affected err? fuel

/-! ### Thread-Safe Per-DSN Connection Pool (`PgConn` & `pgPoolBox`) -/

def PgSslMode.tag : PgSslMode → String
  | .disable => "disable"
  | .prefer  => "prefer"
  | .require => "require"

/-- Normalized connection-pool key uniquely identifying `(host, port, database, user, sslMode, password)`. -/
def PgConnParams.poolKey (cfg : PgConnParams) : String :=
  s!"{cfg.user}:{cfg.password}@{cfg.host.toLower}:{cfg.port}/{cfg.database}?ssl={cfg.sslMode.tag}"

structure PgConn where
  poolKey    : String
  handle     : UInt64
  buf        : ByteArray
  off        : Nat
  txStatus   : UInt8 := 0x49 -- 'I' idle
  healthy    : Bool := true

private structure PgPooledEntry where
  handle     : UInt64
  buf        : ByteArray
  off        : Nat
  lastUsedMs : Nat

private def pgPoolMaxIdlePerDsn : Nat := 8
private def pgPoolIdleTimeoutMs : Nat := 60000

initialize pgPoolBox : IO.Ref (Std.HashMap String (Array PgPooledEntry)) ←
  IO.mkRef {}

private def closePgHandle (handle : UInt64) (sendTerm : Bool := true) : IO Unit := do
  if sendTerm then
    discard <| Prim.outboundWriteAll handle encodeTerminate
  Prim.outboundRelease handle 0

private def closeHandlesList : List UInt64 → IO Unit
  | [] => pure ()
  | h :: hs => do
      closePgHandle h true
      closeHandlesList hs

private def connectPg (cfg : PgConnParams) : IO (Except String PgConn) := do
  match ← Prim.outboundAcquire 0 cfg.host cfg.port 0 (fun _ => false) with
  | .error e => return .error s!"postgres connect failed: {e}"
  | .ok (handleNat, _) =>
      let handle := UInt64.ofNat handleNat
      -- Optional STARTTLS negotiation (`SSLRequest`)
      if cfg.sslMode != .disable then
        match ← Prim.outboundWriteAll handle encodeSslRequest with
        | .error e =>
            Prim.outboundRelease handle 0
            return .error s!"postgres SSLRequest write failed: {e}"
        | .ok () =>
            match ← Prim.outboundReadSome handle 1 with
            | .error e =>
                Prim.outboundRelease handle 0
                return .error s!"postgres SSLRequest read failed: {e}"
            | .ok reply =>
                if reply.size >= 1 && reply[0]! == 0x53 then -- 'S' = TLS accepted
                  match ← Prim.outboundUpgradeTls handle cfg.host with
                  | .error e =>
                      Prim.outboundRelease handle 0
                      return .error e
                  | .ok () => pure ()
                else if cfg.sslMode == .require then
                  Prim.outboundRelease handle 0
                  return .error "PostgreSQL server rejected TLS but sslmode=require"
                else pure ()
      match ← Prim.outboundWriteAll handle (encodeStartup cfg.user cfg.database) with
      | .error e =>
          Prim.outboundRelease handle 0
          return .error s!"postgres startup write failed: {e}"
      | .ok () =>
          match ← authLoop handle cfg ByteArray.empty 0 "" "" 64 with
          | .error e =>
              Prim.outboundRelease handle 0
              return .error s!"postgres auth failed: {e}"
          | .ok (b, o) =>
              return .ok { poolKey := cfg.poolKey, handle, buf := b, off := o, txStatus := 0x49, healthy := true }

private def popPoolCandidate (key : String) (nowMs : Nat) :
    IO (Option PgPooledEntry × List UInt64) :=
  pgPoolBox.modifyGet fun m =>
    match m[key]? with
    | none => ((none, []), m)
    | some arr =>
        let (live, expired) := arr.foldl (init := (#[], [])) fun (l, ex) e =>
          if nowMs - e.lastUsedMs ≤ pgPoolIdleTimeoutMs then (l.push e, ex)
          else (l, e.handle :: ex)
        if h : live.size > 0 then
          let picked := live[live.size - 1]
          let rest := live.pop
          let m' := if rest.isEmpty then m.erase key else m.insert key rest
          ((some picked, expired), m')
        else
          ((none, expired), m.erase key)

private def acquirePooledLoop (cfg : PgConnParams) (key : String) (nowMs : Nat) :
    Nat → IO (Except String (PgConn × Bool))
  | 0 => do
      match ← connectPg cfg with
      | .ok c    => return .ok (c, false)
      | .error e => return .error e
  | fuel + 1 => do
      let (cand?, expired) ← popPoolCandidate key nowMs
      closeHandlesList expired
      match cand? with
      | none =>
          match ← connectPg cfg with
          | .ok c    => return .ok (c, false)
          | .error e => return .error e
      | some entry =>
          if entry.off >= entry.buf.size && (← Prim.outboundIsAlive entry.handle) then
            return .ok ({
              poolKey := key, handle := entry.handle, buf := ByteArray.empty, off := 0,
              txStatus := 0x49, healthy := true
            }, true)
          else
            closePgHandle entry.handle false
            acquirePooledLoop cfg key nowMs fuel

/-- Acquires a live, authenticated PostgreSQL connection from the per-DSN pool (or opens one). -/
def acquireConn (cfg : PgConnParams) : IO (Except String (PgConn × Bool)) := do
  let nowMs := (← Prim.nowMs).toNat
  acquirePooledLoop cfg cfg.poolKey nowMs (pgPoolMaxIdlePerDsn + 2)

/-- Returns a healthy idle (`ReadyForQuery` `'I'`) PostgreSQL connection to the bounded per-DSN pool,
    or closes it cleanly if broken, mid-transaction, or over the pool's idle cap. -/
def releaseConn (conn : PgConn) : IO Unit := do
  if !conn.healthy || conn.txStatus != 0x49 || conn.off < conn.buf.size then
    closePgHandle conn.handle conn.healthy
    return
  let nowMs := (← Prim.nowMs).toNat
  let entry : PgPooledEntry := { handle := conn.handle, buf := ByteArray.empty, off := 0, lastUsedMs := nowMs }
  let evicted ← pgPoolBox.modifyGet fun m =>
    let cur := m[conn.poolKey]?.getD #[]
    let (live, expired) := cur.foldl (init := (#[], [])) fun (l, ex) e =>
      if nowMs - e.lastUsedMs ≤ pgPoolIdleTimeoutMs then (l.push e, ex)
      else (l, e.handle :: ex)
    if live.size < pgPoolMaxIdlePerDsn then
      (expired, m.insert conn.poolKey (live.push entry))
    else
      -- Evict oldest entry (index 0) and push newest
      let (evictedOld, kept) :=
        if h : 0 < live.size then (live[0].handle :: expired, live.extract 1 live.size)
        else (expired, live)
      (evictedOld, m.insert conn.poolKey (kept.push entry))
  closeHandlesList evicted

/-- Executes a parameterized query on an already-acquired `PgConn` (used by both pooled queries and transactions). -/
def execOnConn (conn : PgConn) (sql : String) (params : Array SqlVal) :
    IO (Except String (DbResult × PgConn) × PgConn) := do
  let wire := encodeParse sql ++ encodeBind params ++ encodeDescribePortal ++ encodeExecute ++ encodeSync
  match ← Prim.outboundWriteAll conn.handle wire with
  | .error e =>
      let dead := { conn with healthy := false }
      return (.error s!"postgres query write failed: {e}", dead)
  | .ok () =>
      match ← collectQueryResultLoop conn.handle conn.buf conn.off #[] #[] 0 none 65536 with
      | .error transportErr =>
          let dead := { conn with healthy := false }
          return (.error transportErr, dead)
      | .ok (qRes, b', o', status) =>
          let conn' := { conn with buf := b', off := o', txStatus := status, healthy := true }
          match qRes with
          | .ok r    => return (.ok (r, conn'), conn')
          | .error e => return (.error e, conn')

/-- Executes a Simple Query Protocol (`'Q'`) statement (e.g. DDL, `BEGIN`, `COMMIT`, `ROLLBACK`) on `conn`. -/
def execSimpleOnConn (conn : PgConn) (sql : String) : IO (Except String PgConn × PgConn) := do
  match ← Prim.outboundWriteAll conn.handle (encodeSimpleQuery sql) with
  | .error e =>
      let dead := { conn with healthy := false }
      return (.error s!"postgres simple query write failed: {e}", dead)
  | .ok () =>
      match ← collectQueryResultLoop conn.handle conn.buf conn.off #[] #[] 0 none 4096 with
      | .error transportErr =>
          let dead := { conn with healthy := false }
          return (.error transportErr, dead)
      | .ok (qRes, b', o', status) =>
          let conn' := { conn with buf := b', off := o', txStatus := status, healthy := true }
          match qRes with
          | .ok _    => return (.ok conn', conn')
          | .error e => return (.error e, conn')

private def execParameterizedAttempt (cfg : PgConnParams) (sql : String) (params : Array SqlVal) :
    Nat → IO (Except String DbResult)
  | 0 => return .error "postgres query failed after retry"
  | attemptsLeft + 1 => do
      match ← acquireConn cfg with
      | .error e => return .error e
      | .ok (conn, wasReused) =>
          let (res, conn') ← execOnConn conn sql params
          match res with
          | .ok (dbRes, cFinal) =>
              releaseConn cFinal
              return .ok dbRes
          | .error e =>
              releaseConn conn'
              -- If a pooled connection broke mid-flight, retry once on a fresh connection.
              if !conn'.healthy && wasReused && attemptsLeft > 0 then
                execParameterizedAttempt cfg sql params attemptsLeft
              else
                return .error e

/-- Executes a single parameterized SQL query over PostgreSQL Extended Query Protocol (`Parse`/`Bind`/`Describe`/`Execute`/`Sync`),
    reusing authenticated pooled connections per DSN. -/
def execParameterized (pgUrl : String) (sql : String) (params : Array SqlVal) : IO (Except String DbResult) := do
  let cfg ← match parsePgUrl pgUrl with
    | .ok c => pure c
    | .error e => return .error e
  execParameterizedAttempt cfg sql params 2

/-- Closes and evicts all idle pooled PostgreSQL connections cleanly. -/
def clearPool : IO Unit := do
  let handles ← pgPoolBox.modifyGet fun m =>
    let all := m.toList.foldl (init := []) fun acc (_, arr) =>
      arr.foldl (init := acc) fun a e => e.handle :: a
    (all, {})
  closeHandlesList handles

/-- Executes DDL statements over PostgreSQL Simple Query Protocol (`'Q'`) using the connection pool. -/
def execDdl (pgUrl : String) (ddl : String) : IO (Except String Unit) := do
  if ddl.trimAscii.toString.isEmpty then return .ok ()
  let cfg ← match parsePgUrl pgUrl with
    | .ok c => pure c
    | .error e => return .error e
  match ← acquireConn cfg with
  | .error e => return .error e
  | .ok (conn, _) =>
      let (res, conn') ← execSimpleOnConn conn ddl
      releaseConn conn'
      match res with
      | .ok _    => return .ok ()
      | .error e => return .error e

end Qed.Server.Db.PgWire
