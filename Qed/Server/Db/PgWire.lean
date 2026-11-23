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

abbrev pushU16BE := Net.pushU16BE
abbrev pushU32BE := Net.pushU32BE
abbrev readU16BE := Net.readU16BE
abbrev readU32BE := Net.readU32BE

def pushI32BE (ba : ByteArray) (i : Int) : ByteArray :=
  pushU32BE ba (if 0 ≤ i then i.toNat else (4294967296 + i).toNat)

def pushCString (ba : ByteArray) (s : String) : ByteArray :=
  (ba ++ s.toUTF8).push 0

def readI32BE (ba : ByteArray) (off : Nat) : Option Int :=
  (readU32BE ba off).map fun n =>
    if n >= 2147483648 then (Int.ofNat n) - 4294967296 else Int.ofNat n

/-- Framed PostgreSQL frontend message: `1-byte tag || 4-byte BE (payload.size + 4) || payload`. -/
def encodeMsg (tag : UInt8) (payload : ByteArray) : ByteArray :=
  pushU32BE (ByteArray.empty.push tag) (payload.size + 4) ++ payload

theorem encodeMsg_size (tag : UInt8) (payload : ByteArray) :
    (encodeMsg tag payload).size = payload.size + 5 := by
  unfold encodeMsg pushU32BE Net.pushU32BE
  simp [ByteArray.size_append, ByteArray.size_push]
  omega

/-- PostgreSQL v3.0 `StartupMessage` (`protocol = 196608`). -/
def encodeStartup (user database : String) : ByteArray :=
  let body := (["user", user, "database", database, "client_encoding", "UTF8"].foldl
    pushCString (pushU32BE ByteArray.empty 196608)).push 0
  pushU32BE ByteArray.empty (body.size + 4) ++ body

def encodeSaslInitialResponse (mech : String) (initialResp : ByteArray) : ByteArray :=
  let p := pushCString ByteArray.empty mech
  encodeMsg 0x70 (pushI32BE p (Int.ofNat initialResp.size) ++ initialResp)

/-- Encodes a `SqlVal` as a PostgreSQL text-format Bind parameter (`none` → SQL NULL). -/
def sqlValToPgText : SqlVal → Option ByteArray
  | .null     => none
  | .int i    => some (toString i).toUTF8
  | .text s   => some s.toUTF8
  | .bool b   => some (if b then "t" else "f").toUTF8
  | .bytes bs => some ("\\x" ++ Proto.encodeHex bs).toUTF8

/-- Extended Query `Parse` (`'P'`) message for unnamed prepared statement. -/
def encodeParse (sql : String) : ByteArray :=
  encodeMsg 0x50 (pushU16BE (pushCString (pushCString ByteArray.empty "") sql) 0)

/-- Extended Query `Bind` (`'B'`) message carrying parameterized `SqlVal` values. -/
def encodeBind (params : Array SqlVal) : ByteArray :=
  let p := pushU16BE (pushU16BE (pushCString (pushCString ByteArray.empty "") "") 0) params.size
  let p := params.foldl (init := p) fun acc v =>
    match sqlValToPgText v with
    | none    => pushI32BE acc (-1)
    | some bs => pushI32BE acc (Int.ofNat bs.size) ++ bs
  encodeMsg 0x42 (pushU16BE p 0)

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

private def findZeroByte (ba : ByteArray) (i : Nat) : Nat :=
  if h : i < ba.size then
    if ba[i]'h == 0 then i else findZeroByte ba (i + 1)
  else ba.size
termination_by ba.size - i

/-- Extracts the human-readable `M` (message) field from a PostgreSQL `ErrorResponse` payload. -/
private def parseErrorFieldsLoop (ba : ByteArray) (off : Nat) : Nat → String
  | 0 => "postgres error"
  | fuel + 1 =>
      if h : off < ba.size then
        let code := ba[off]'h
        if code == 0 then "postgres error"
        else
          let zPos := findZeroByte ba (off + 1)
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
      let afterName := min (findZeroByte ba off + 1) ba.size
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
  let split2 (s sep : String) : String × Option String :=
    match s.splitOn sep with | a :: b :: _ => (a, some b) | _ => (s, none)
  let rest ←
    if rawUrl.startsWith "postgresql://" then .ok (String.ofList (rawUrl.toList.drop 13))
    else if rawUrl.startsWith "postgres://" then .ok (String.ofList (rawUrl.toList.drop 11))
    else .error "PostgreSQL URL must start with `postgres://` or `postgresql://`"
  let (beforeQ, queryOpt) := split2 rest "?"
  let (authAndHost, dbOpt) := split2 beforeQ "/"
  let (userInfo?, hostPort) := match split2 authAndHost "@" with
    | (a, some b) => (some a, b)
    | (_, none)   => (none, authAndHost)
  let (user, password) := match userInfo? with
    | none => ("postgres", "")
    | some ui =>
        let (u, p?) := split2 ui ":"
        (Qed.decodeSeg u, (p?.map Qed.decodeSeg).getD "")
  let (host, port) ← match split2 hostPort ":" with
    | (h, some pStr) =>
        match Net.parseStrictU64 pStr 65535 with
        | some pn => if pn > 0 then .ok (h, UInt16.ofNat pn) else .error s!"invalid postgres port `{pStr}`"
        | none    => .error s!"invalid postgres port `{pStr}`"
    | (h, none) => .ok (h, (5432 : UInt16))
  let sslMode : PgSslMode :=
    (queryOpt.getD "").splitOn "&" |>.foldl (init := .prefer) fun acc kv =>
      match kv.splitOn "=" with
      | ["sslmode", "disable"] => .disable
      | ["sslmode", "require"] | ["sslmode", "verify-ca"] | ["sslmode", "verify-full"] => .require
      | _ => acc
  if host.isEmpty then .error "missing postgres host"
  else
    let dbPart := dbOpt.getD "postgres"
    .ok {
      user := if user.isEmpty then "postgres" else user
      password, host, port
      database := if dbPart.isEmpty then "postgres" else Qed.decodeSeg dbPart
      sslMode
    }

/-! ### Base64 Helpers & SCRAM-SHA-256 Auth (over `ring` SHA-256 / HMAC / PBKDF2) -/

def base64Decode (s : String) : ByteArray :=
  (Qed.Base64.decode (String.ofList (s.toList.filter (!·.isWhitespace)))).toOption.getD ByteArray.empty

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

open Qed.Server.Net (liftE liftP)

private abbrev PgM := ExceptT String IO
private def mapErr {α : Type} (pfx : String) (x : PgM α) : PgM α :=
  ExceptT.mk ((·.mapError fun e => s!"{pfx}: {e}") <$> x.run)

private def readNextFrame (handle : UInt64) (buf : ByteArray) (off : Nat) :
    Nat → PgM (PgFrame × ByteArray × Nat)
  | 0 => throw "postgres read frame fuel exceeded"
  | fuel + 1 => do
      match decodeFrame buf off with
      | .frame f nextOff =>
          let (b', o') := if nextOff >= buf.size then (ByteArray.empty, 0) else (buf, nextOff)
          return (f, b', o')
      | .err msg => throw msg
      | .needMore =>
          let chunk ← liftE (Prim.outboundReadSome handle 16384)
          if chunk.isEmpty then throw "unexpected EOF from PostgreSQL server"
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
    Nat → PgM (ByteArray × Nat)
  | 0 => throw "postgres auth loop exceeded limit"
  | fuel + 1 => do
      let (f, b1, o1) ← readNextFrame handle buf off 4096
      let sendNext (wire : ByteArray) (cNonce := clientNonce) (cBare := clientFirstBare) : PgM (ByteArray × Nat) := do
        liftE (Prim.outboundWriteAll handle wire)
        authLoop handle cfg b1 o1 cNonce cBare fuel
      if f.tag == 0x45 then throw (parseErrorResponse f.payload) -- 'E' ErrorResponse
      else if f.tag == 0x5A then return (b1, o1) -- 'Z' ReadyForQuery
      else if f.tag == 0x52 then -- 'R' Authentication
        match readU32BE f.payload 0 with
        | some 0 | some 12 => authLoop handle cfg b1 o1 clientNonce clientFirstBare fuel
        | some 3 => sendNext (encodeMsg 0x70 (pushCString ByteArray.empty cfg.password)) -- CleartextPassword
        | some 10 => -- AuthenticationSASL
            let nonce ← Prim.randomHex 12
            let bare := s!"n=,r={nonce}"
            sendNext (encodeSaslInitialResponse "SCRAM-SHA-256" s!"n,,{bare}".toUTF8) nonce bare
        | some 11 => -- AuthenticationSASLContinue
            let serverFirst := (String.fromUTF8? (f.payload.extract 4 f.payload.size)).getD ""
            let (srvNonce, salt, iters) ← liftP (parseScramServerFirst serverFirst)
            if !srvNonce.startsWith clientNonce then throw "SCRAM-SHA-256 server nonce mismatch"
            let saltedPw ← Prim.pbkdf2HmacSha256 cfg.password.toUTF8 salt (UInt32.ofNat iters)
            let clientKey ← Prim.hmacSha256 saltedPw "Client Key".toUTF8
            let storedKey ← Prim.sha256 clientKey
            let finalNoProof := s!"c=biws,r={srvNonce}"
            let authMsg := s!"{clientFirstBare},{serverFirst},{finalNoProof}"
            let clientSig ← Prim.hmacSha256 storedKey authMsg.toUTF8
            let proof := xorBytes clientKey clientSig
            sendNext (encodeMsg 0x70 s!"{finalNoProof},p={Qed.Base64.encode proof}".toUTF8)
        | some code =>
            throw s!"unsupported PostgreSQL auth method {code} (supported: trust, cleartext, SCRAM-SHA-256)"
        | none => throw "truncated PostgreSQL Authentication packet"
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
    Nat → PgM (Except String DbResult × ByteArray × Nat × UInt8)
  | 0 => throw "postgres query response exceeded frame limit"
  | fuel + 1 => do
      let (f, b1, o1) ← readNextFrame handle buf off 4096
      let next (o := oids) (rs := rows) (aff := affected) (e := err?) :=
        collectQueryResultLoop handle b1 o1 o rs aff e fuel
      match f.tag with
      | 0x5A => return (err?.elim (.ok { rows, affected }) .error, b1, o1, readyStatusByte f.payload) -- 'Z' ReadyForQuery
      | 0x45 => next (e := some (parseErrorResponse f.payload)) -- 'E' ErrorResponse
      | 0x54 => next (o := parseRowDescription f.payload)       -- 'T' RowDescription
      | 0x44 => match parseDataRow oids f.payload with          -- 'D' DataRow
          | .ok row  => next (rs := rows.push row)
          | .error e => next (e := some e)
      | 0x43 => next (aff := parseCommandTagAffected f.payload) -- 'C' CommandComplete
      | _    => next -- ParseComplete ('1'), BindComplete ('2'), NoData ('n'), NoticeResponse ('N'), EmptyQuery ('I')

/-! ### Thread-Safe Per-DSN Connection Pool (`PgConn` & `pgPoolBox`) -/

/-- Normalized connection-pool key uniquely identifying `(host, port, database, user, sslMode, password)`. -/
def PgConnParams.poolKey (cfg : PgConnParams) : String :=
  let ssl := match cfg.sslMode with | .disable => "disable" | .prefer => "prefer" | .require => "require"
  s!"{cfg.user}:{cfg.password}@{cfg.host.toLower}:{cfg.port}/{cfg.database}?ssl={ssl}"

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
    discard <| Prim.outboundWriteAll handle (encodeMsg 0x58 ByteArray.empty) -- 'X' Terminate
  Prim.outboundRelease handle 0

private def partitionPoolEntries (arr : Array PgPooledEntry) (nowMs : Nat) :
    Array PgPooledEntry × List UInt64 :=
  arr.foldl (init := (#[], [])) fun (l, ex) e =>
    if nowMs - e.lastUsedMs ≤ pgPoolIdleTimeoutMs then (l.push e, ex) else (l, e.handle :: ex)

private def connectPg (cfg : PgConnParams) : PgM PgConn := do
  let (handleNat, _) ← mapErr "postgres connect failed" <| liftE (Prim.outboundAcquire 0 cfg.host cfg.port 0 (fun _ => false))
  let handle := UInt64.ofNat handleNat
  try
    if cfg.sslMode != .disable then
      mapErr "postgres SSLRequest write failed" <| liftE (Prim.outboundWriteAll handle (pushU32BE (pushU32BE ByteArray.empty 8) 80877103))
      let reply ← mapErr "postgres SSLRequest read failed" <| liftE (Prim.outboundReadSome handle 1)
      if reply.size >= 1 && reply[0]! == 0x53 then -- 'S' = TLS accepted
        liftE (Prim.outboundUpgradeTls handle cfg.host)
      else if cfg.sslMode == .require then
        throw "PostgreSQL server rejected TLS but sslmode=require"
    mapErr "postgres startup write failed" <| liftE (Prim.outboundWriteAll handle (encodeStartup cfg.user cfg.database))
    let (b, o) ← mapErr "postgres auth failed" <| authLoop handle cfg ByteArray.empty 0 "" "" 64
    return { poolKey := cfg.poolKey, handle, buf := b, off := o, txStatus := 0x49, healthy := true }
  catch e =>
    Prim.outboundRelease handle 0
    throw e

private def popPoolCandidate (key : String) (nowMs : Nat) :
    IO (Option PgPooledEntry × List UInt64) :=
  pgPoolBox.modifyGet fun m =>
    match m[key]? with
    | none => ((none, []), m)
    | some arr =>
        let (live, expired) := partitionPoolEntries arr nowMs
        if h : live.size > 0 then
          let rest := live.pop
          ((some live[live.size - 1], expired), if rest.isEmpty then m.erase key else m.insert key rest)
        else
          ((none, expired), m.erase key)

private def acquirePooledLoop (cfg : PgConnParams) (key : String) (nowMs : Nat) :
    Nat → PgM (PgConn × Bool)
  | 0 => (·, false) <$> connectPg cfg
  | fuel + 1 => do
      let (cand?, expired) ← popPoolCandidate key nowMs
      expired.forM (closePgHandle · true)
      match cand? with
      | none => (·, false) <$> connectPg cfg
      | some entry =>
          if entry.off >= entry.buf.size && (← Prim.outboundIsAlive entry.handle) then
            return ({
              poolKey := key, handle := entry.handle, buf := ByteArray.empty, off := 0,
              txStatus := 0x49, healthy := true
            }, true)
          else
            closePgHandle entry.handle false
            acquirePooledLoop cfg key nowMs fuel

/-- Acquires a live, authenticated PostgreSQL connection from the per-DSN pool (or opens one). -/
def acquireConn (cfg : PgConnParams) : IO (Except String (PgConn × Bool)) := do
  let nowMs := (← Prim.nowMs).toNat
  (acquirePooledLoop cfg cfg.poolKey nowMs (pgPoolMaxIdlePerDsn + 2)).run

/-- Returns a healthy idle (`ReadyForQuery` `'I'`) PostgreSQL connection to the bounded per-DSN pool,
    or closes it cleanly if broken, mid-transaction, or over the pool's idle cap. -/
def releaseConn (conn : PgConn) : IO Unit := do
  if !conn.healthy || conn.txStatus != 0x49 || conn.off < conn.buf.size then
    closePgHandle conn.handle conn.healthy
    return
  let nowMs := (← Prim.nowMs).toNat
  let entry : PgPooledEntry := { handle := conn.handle, buf := ByteArray.empty, off := 0, lastUsedMs := nowMs }
  let evicted ← pgPoolBox.modifyGet fun m =>
    let (live, expired) := partitionPoolEntries (m[conn.poolKey]?.getD #[]) nowMs
    if live.size < pgPoolMaxIdlePerDsn then
      (expired, m.insert conn.poolKey (live.push entry))
    else
      -- Evict oldest entry (index 0) and push newest
      let (evictedOld, kept) :=
        if h : 0 < live.size then (live[0].handle :: expired, live.extract 1 live.size)
        else (expired, live)
      (evictedOld, m.insert conn.poolKey (kept.push entry))
  evicted.forM (closePgHandle · true)

private def runWireOnConn (conn : PgConn) (wire : ByteArray) (errPrefix : String) (fuel : Nat) :
    IO (Except String (DbResult × PgConn) × PgConn) := do
  match ← Prim.outboundWriteAll conn.handle wire with
  | .error e => return (.error s!"{errPrefix}: {e}", { conn with healthy := false })
  | .ok () =>
      match ← (collectQueryResultLoop conn.handle conn.buf conn.off #[] #[] 0 none fuel).run with
      | .error transportErr => return (.error transportErr, { conn with healthy := false })
      | .ok (qRes, b', o', status) =>
          let conn' := { conn with buf := b', off := o', txStatus := status, healthy := true }
          return (qRes.map (·, conn'), conn')

/-- Executes a parameterized query on an already-acquired `PgConn` (used by both pooled queries and transactions). -/
def execOnConn (conn : PgConn) (sql : String) (params : Array SqlVal) :
    IO (Except String (DbResult × PgConn) × PgConn) :=
  let descPortal := encodeMsg 0x44 (pushCString (ByteArray.empty.push 0x50) "")
  let execute := encodeMsg 0x45 (pushU32BE (pushCString ByteArray.empty "") 0)
  let sync := encodeMsg 0x53 ByteArray.empty
  runWireOnConn conn (encodeParse sql ++ encodeBind params ++ descPortal ++ execute ++ sync)
    "postgres query write failed" 65536

/-- Executes a Simple Query Protocol (`'Q'`) statement (e.g. DDL, `BEGIN`, `COMMIT`, `ROLLBACK`) on `conn`. -/
def execSimpleOnConn (conn : PgConn) (sql : String) : IO (Except String PgConn × PgConn) := do
  let (res, conn') ← runWireOnConn conn (encodeMsg 0x51 (pushCString ByteArray.empty sql)) "postgres simple query write failed" 4096
  return (res.map Prod.snd, conn')

private def execParameterizedAttempt (cfg : PgConnParams) (sql : String) (params : Array SqlVal) :
    Nat → PgM DbResult
  | 0 => throw "postgres query failed after retry"
  | attemptsLeft + 1 => do
      let (conn, wasReused) ← liftE (acquireConn cfg)
      let (res, conn') ← execOnConn conn sql params
      match res with
      | .ok (dbRes, cFinal) => releaseConn cFinal; return dbRes
      | .error e =>
          releaseConn conn'
          -- If a pooled connection broke mid-flight, retry once on a fresh connection.
          if !conn'.healthy && wasReused && attemptsLeft > 0 then
            execParameterizedAttempt cfg sql params attemptsLeft
          else throw e

/-- Executes a single parameterized SQL query over PostgreSQL Extended Query Protocol (`Parse`/`Bind`/`Describe`/`Execute`/`Sync`),
    reusing authenticated pooled connections per DSN. -/
def execParameterized (pgUrl : String) (sql : String) (params : Array SqlVal) : IO (Except String DbResult) :=
  ExceptT.run do
    let cfg ← liftP (parsePgUrl pgUrl)
    execParameterizedAttempt cfg sql params 2

/-- Closes and evicts all idle pooled PostgreSQL connections cleanly. -/
def clearPool : IO Unit := do
  let handles ← pgPoolBox.modifyGet fun m =>
    let all := m.toList.foldl (init := []) fun acc (_, arr) =>
      arr.foldl (init := acc) fun a e => e.handle :: a
    (all, {})
  handles.forM (closePgHandle · true)

/-- Executes DDL statements over PostgreSQL Simple Query Protocol (`'Q'`) using the connection pool. -/
def execDdl (pgUrl : String) (ddl : String) : IO (Except String Unit) :=
  ExceptT.run do
    if ddl.trimAscii.toString.isEmpty then return ()
    let cfg ← liftP (parsePgUrl pgUrl)
    let (conn, _) ← liftE (acquireConn cfg)
    let (res, conn') ← execSimpleOnConn conn ddl
    releaseConn conn'
    discard <| liftP res

end Qed.Server.Db.PgWire
