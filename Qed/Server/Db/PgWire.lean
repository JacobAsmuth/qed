import Std.Data.HashMap.Basic
import Qed.Server.Core
import Qed.Server.Db.Core
import Qed.Server.Net
import Qed.Server.Prim

namespace Qed.Server.Db.PgWire

/-! ## Total, Verified PostgreSQL v3 Wire Protocol Codec & Pooled Client (`PgWire`) -/

abbrev pushU16BE := Net.pushU16BE
abbrev pushU32BE := Net.pushU32BE
abbrev readU16BE := Net.readU16BE
abbrev readU32BE := Net.readU32BE
def pushI32BE (ba : ByteArray) (i : Int) : ByteArray := pushU32BE ba (if 0 ≤ i then i.toNat else (4294967296 + i).toNat)
def pushCString (ba : ByteArray) (s : String) : ByteArray := (ba ++ s.toUTF8).push 0
def readI32BE (ba : ByteArray) (off : Nat) : Option Int :=
  (readU32BE ba off).map fun n => if n >= 2147483648 then (Int.ofNat n) - 4294967296 else Int.ofNat n
def encodeMsg (tag : UInt8) (payload : ByteArray) : ByteArray := pushU32BE (ByteArray.empty.push tag) (payload.size + 4) ++ payload
theorem encodeMsg_size (tag : UInt8) (payload : ByteArray) : (encodeMsg tag payload).size = payload.size + 5 := by
  unfold encodeMsg pushU32BE Net.pushU32BE Net.pushU16BE; simp [ByteArray.size_append, ByteArray.size_push]; omega
def encodeStartup (user database : String) : ByteArray :=
  let body := (["user", user, "database", database, "client_encoding", "UTF8"].foldl pushCString (pushU32BE ByteArray.empty 196608)).push 0
  pushU32BE ByteArray.empty (body.size + 4) ++ body
def encodeSaslInitialResponse (mech : String) (initialResp : ByteArray) : ByteArray :=
  encodeMsg 0x70 (pushI32BE (pushCString ByteArray.empty mech) (Int.ofNat initialResp.size) ++ initialResp)
def sqlValToPgText : SqlVal → Option ByteArray
  | .null => none | .int i => some (toString i).toUTF8 | .text s => some s.toUTF8
  | .bool b => some (if b then "t" else "f").toUTF8 | .bytes bs => some ("\\x" ++ Proto.encodeHex bs).toUTF8
def encodeParse (sql : String) : ByteArray := encodeMsg 0x50 (pushU16BE (pushCString (pushCString ByteArray.empty "") sql) 0)
def encodeBind (params : Array SqlVal) : ByteArray :=
  let p0 := pushU16BE (pushU16BE (pushCString (pushCString ByteArray.empty "") "") 0) params.size
  let p := params.foldl (init := p0) fun acc v => match sqlValToPgText v with
    | none => pushI32BE acc (-1) | some bs => pushI32BE acc (Int.ofNat bs.size) ++ bs
  encodeMsg 0x42 (pushU16BE p 0)

/-! ### Backend Message Framing & Decoding -/

structure PgFrame where
  tag     : UInt8
  payload : ByteArray
inductive DecodeFrameRes where | needMore | frame (f : PgFrame) (nextOff : Nat) | err (msg : String)

def decodeFrame (buf : ByteArray) (off : Nat) : DecodeFrameRes :=
  if h : off + 5 ≤ buf.size then
    match readU32BE buf (off + 1) with
    | none => .needMore
    | some len =>
        if len < 4 then .err s!"invalid postgres frame length {len}"
        else if len > 64 * 1024 * 1024 then .err s!"postgres frame too large ({len} bytes)"
        else if off + 1 + len ≤ buf.size then .frame { tag := buf[off]'(by omega), payload := buf.extract (off + 5) (off + 1 + len) } (off + 1 + len)
        else .needMore
  else .needMore
private def findZeroByte (ba : ByteArray) (i : Nat) : Nat :=
  if h : i < ba.size then if ba[i]'h == 0 then i else findZeroByte ba (i + 1) else ba.size
termination_by ba.size - i
def parseErrorResponse (payload : ByteArray) : String :=
  let finish (msg? sqlstate? : Option String) : String :=
    match sqlstate?, msg? with
    | some c, some m => s!"[{c}] {m}" | none, some m => m
    | some c, none => s!"postgres error [{c}]" | none, none => "postgres error"
  let rec go (off : Nat) (msg? sqlstate? : Option String) : Nat → String
    | 0 => finish msg? sqlstate?
    | fuel + 1 => if h : off < payload.size then
        let code := payload[off]'h
        if code == 0 then finish msg? sqlstate?
        else let zPos := findZeroByte payload (off + 1)
             let txt? := String.fromUTF8? (payload.extract (off + 1) zPos)
             if code == 0x4D then go (zPos + 1) (txt?.orElse fun _ => msg?) sqlstate? fuel
             else if code == 0x43 then go (zPos + 1) msg? (txt?.orElse fun _ => sqlstate?) fuel
             else go (zPos + 1) msg? sqlstate? fuel
      else finish msg? sqlstate?
  go 0 none none (payload.size + 1)
def parseRowDescription (payload : ByteArray) : Array Nat :=
  let rec go (off : Nat) (acc : Array Nat) : Nat → Array Nat
    | 0 => acc | n + 1 => let afterName := min (findZeroByte payload off + 1) payload.size
                          go (afterName + 18) (acc.push ((readU32BE payload (afterName + 6)).getD 25)) n
  (readU16BE payload 0).map (go 2 #[]) |>.getD #[]
def decodePgCell (oid : Nat) (raw : ByteArray) : Except String SqlVal :=
  match String.fromUTF8? raw with
  | none => .ok (.bytes raw)
  | some s =>
      if oid == 16 then .ok (.bool (s == "t" || s == "true" || s == "1"))
      else if oid == 20 || oid == 21 || oid == 23 then (s.toInt?).elim (.error s!"postgres invalid int cell: {s}") (.ok ∘ .int)
      else if oid == 17 then if s.startsWith "\\x" then (Proto.decodeHex (String.ofList (s.toList.drop 2))).map .bytes else .ok (.bytes raw)
      else .ok (.text s)
def parseDataRow (oids : Array Nat) (payload : ByteArray) : Except String DbRow :=
  let rec go (off colIdx : Nat) (acc : Array SqlVal) : Nat → Except String DbRow
    | 0 => .ok acc
    | rem + 1 => do
        let some colLen := readI32BE payload off | .error "truncated postgres DataRow column length"
        if colLen < 0 then go (off + 4) (colIdx + 1) (acc.push .null) rem
        else let n := colLen.toNat
             if off + 4 + n > payload.size then .error "truncated postgres DataRow column payload"
             else go (off + 4 + n) (colIdx + 1) (acc.push (← decodePgCell (oids.getD colIdx 25) (payload.extract (off + 4) (off + 4 + n)))) rem
  (readU16BE payload 0).elim (.error "truncated postgres DataRow header") (go 2 0 #[])
def parseCommandTag (payload : ByteArray) : String :=
  let trimmed := if payload.size > 0 && payload[payload.size - 1]! == 0 then payload.extract 0 (payload.size - 1) else payload
  (String.fromUTF8? trimmed).getD ""

/-! ### `postgres://` URL Parser & SCRAM-SHA-256 Auth -/

inductive PgSslMode where | disable | prefer | require deriving Inhabited, DecidableEq, Repr
structure PgConnParams where
  user      : String := "postgres"
  password  : String := ""
  host      : String := "127.0.0.1"
  port      : UInt16 := 5432
  database  : String := "postgres"
  sslMode   : PgSslMode := .prefer
  ssrfGuard : Bool := false
deriving Inhabited, Repr

def parsePgUrl (rawUrl : String) : Except String PgConnParams := do
  let split2 (s sep : String) : String × Option String := match s.splitOn sep with | a :: b :: _ => (a, some b) | _ => (s, none)
  let rest ←
    if rawUrl.startsWith "postgresql://" then .ok (String.Pos.Raw.extract rawUrl ⟨13⟩ ⟨rawUrl.utf8ByteSize⟩)
    else if rawUrl.startsWith "postgres://" then .ok (String.Pos.Raw.extract rawUrl ⟨11⟩ ⟨rawUrl.utf8ByteSize⟩)
    else .error "PostgreSQL URL must start with `postgres://` or `postgresql://`"
  let (beforeQ, queryOpt) := split2 rest "?"; let (authAndHost, dbOpt) := split2 beforeQ "/"
  let (userInfo?, hostPort) := match split2 authAndHost "@" with | (a, some b) => (some a, b) | (_, none) => (none, authAndHost)
  let (user, password) := match userInfo? with
    | none => ("postgres", "") | some ui => let (u, p?) := split2 ui ":"; (Qed.decodeSeg u, (p?.map Qed.decodeSeg).getD "")
  let (host, port) ← match split2 hostPort ":" with
    | (h, some pStr) => match Net.parseStrictU64 pStr 65535 with
        | some pn => if pn > 0 then .ok (h, UInt16.ofNat pn) else .error s!"invalid postgres port `{pStr}`"
        | none    => .error s!"invalid postgres port `{pStr}`"
    | (h, none) => .ok (h, (5432 : UInt16))
  let sslMode : PgSslMode := (queryOpt.getD "").splitOn "&" |>.foldl (init := .prefer) fun acc kv => match kv.splitOn "=" with
    | ["sslmode", "disable"] => .disable | ["sslmode", "require"] | ["sslmode", "verify-ca"] | ["sslmode", "verify-full"] => .require | _ => acc
  if host.isEmpty then .error "missing postgres host"
  else
    let dbPart := dbOpt.getD "postgres"
    .ok { user := if user.isEmpty then "postgres" else user, password, host, port,
          database := if dbPart.isEmpty then "postgres" else Qed.decodeSeg dbPart, sslMode }

def base64Decode (s : String) : ByteArray :=
  (Qed.Base64.decode (String.ofList (s.toList.filter (!·.isWhitespace)))).toOption.getD ByteArray.empty
private def xorBytes (a b : ByteArray) : ByteArray := ByteArray.mk <| (Array.range (min a.size b.size)).map fun i => a.get! i ^^^ b.get! i

/-! ### Live Wire Execution & Per-DSN Connection Pool -/

open Qed.Server.Net (liftE liftP)
private abbrev PgM := ExceptT String IO
private def mapErr {α : Type} (pfx : String) (x : PgM α) : PgM α := ExceptT.mk ((·.mapError fun e => s!"{pfx}: {e}") <$> x.run)

private def readNextFrame (handle : UInt64) (buf : ByteArray) (off : Nat) : Nat → PgM (PgFrame × ByteArray × Nat)
  | 0 => throw "postgres read frame fuel exceeded"
  | fuel + 1 => do
      match decodeFrame buf off with
      | .frame f nextOff => return (f, if nextOff >= buf.size then (ByteArray.empty, 0) else (buf, nextOff))
      | .err msg => throw msg
      | .needMore =>
          let chunk ← liftE (Prim.outboundReadSome handle 16384)
          if chunk.isEmpty then throw "unexpected EOF from PostgreSQL server"
          else readNextFrame handle (if off > 0 then buf.extract off buf.size ++ chunk else buf ++ chunk) 0 fuel

private def parseScramServerFirst (s : String) : Except String (String × ByteArray × Nat) :=
  let (r?, s?, i?) := (s.splitOn ",").foldl (init := (none, none, none)) fun (r?, s?, i?) p =>
    let rest := String.ofList (p.toList.drop 2)
    if p.startsWith "r=" then (some rest, s?, i?) else if p.startsWith "s=" then (r?, some rest, i?)
    else if p.startsWith "i=" then (r?, s?, rest.toNat?) else (r?, s?, i?)
  match r?, s?, i? with | some r, some sb, some it => .ok (r, base64Decode sb, it) | _, _, _ => .error "invalid SCRAM-SHA-256 server-first-message"

private def authLoop (handle : UInt64) (cfg : PgConnParams) (buf : ByteArray) (off : Nat)
    (clientNonce clientFirstBare : String) : Nat → PgM (ByteArray × Nat)
  | 0 => throw "postgres auth loop exceeded limit"
  | fuel + 1 => do
      let (f, b1, o1) ← readNextFrame handle buf off 4096
      let sendNext (wire : ByteArray) (cNonce := clientNonce) (cBare := clientFirstBare) := do
        liftE (Prim.outboundWriteAll handle wire); authLoop handle cfg b1 o1 cNonce cBare fuel
      match f.tag with
      | 0x45 => throw (parseErrorResponse f.payload) | 0x5A => return (b1, o1)
      | 0x52 => match readU32BE f.payload 0 with
          | some 0 | some 12 => authLoop handle cfg b1 o1 clientNonce clientFirstBare fuel
          | some 3 => sendNext (encodeMsg 0x70 (pushCString ByteArray.empty cfg.password))
          | some 10 => let nonce ← Prim.randomHex 12; let bare := s!"n=,r={nonce}"
                       sendNext (encodeSaslInitialResponse "SCRAM-SHA-256" s!"n,,{bare}".toUTF8) nonce bare
          | some 11 =>
              let serverFirst := (String.fromUTF8? (f.payload.extract 4 f.payload.size)).getD ""
              let (srvNonce, salt, iters) ← liftP (parseScramServerFirst serverFirst)
              if !srvNonce.startsWith clientNonce then throw "SCRAM-SHA-256 server nonce mismatch"
              let clientKey ← Prim.hmacSha256 (← Prim.pbkdf2HmacSha256 cfg.password.toUTF8 salt (UInt32.ofNat iters)) "Client Key".toUTF8
              let finalNoProof := s!"c=biws,r={srvNonce}"
              let clientSig ← Prim.hmacSha256 (← Prim.sha256 clientKey) s!"{clientFirstBare},{serverFirst},{finalNoProof}".toUTF8
              sendNext (encodeMsg 0x70 s!"{finalNoProof},p={Qed.Base64.encode (xorBytes clientKey clientSig)}".toUTF8)
          | some code => throw s!"unsupported PostgreSQL auth method {code} (supported: trust, cleartext, SCRAM-SHA-256)"
          | none => throw "truncated PostgreSQL Authentication packet"
      | _ => authLoop handle cfg b1 o1 clientNonce clientFirstBare fuel

private def collectQueryResultLoop (handle : UInt64) (buf : ByteArray) (off : Nat)
    (oids : Array Nat) (rows : Array DbRow) (affected : Nat) (cmdTag : String) (err? : Option String) :
    Nat → PgM (Except String (DbResult × String) × ByteArray × Nat × UInt8)
  | 0 => throw "postgres query response exceeded frame limit"
  | fuel + 1 => do
      let (f, b1, o1) ← readNextFrame handle buf off 4096
      let next (o := oids) (rs := rows) (aff := affected) (tag := cmdTag) (e := err?) := collectQueryResultLoop handle b1 o1 o rs aff tag e fuel
      match f.tag with
      | 0x5A => return (err?.elim (.ok ({ rows, affected }, cmdTag)) .error, b1, o1, f.payload.data.getD 0 0)
      | 0x45 => next (e := some (parseErrorResponse f.payload)) | 0x54 => next (o := parseRowDescription f.payload)
      | 0x44 => match parseDataRow oids f.payload with | .ok row => next (rs := rows.push row) | .error e => next (e := some e)
      | 0x43 => let tag := parseCommandTag f.payload; next (aff := (tag.splitOn " ").reverse.head?.bind String.toNat? |>.getD 0) (tag := tag)
      | _ => next

def PgConnParams.poolKey (cfg : PgConnParams) : String :=
  s!"{cfg.user}:{cfg.password}@{cfg.host.toLower}:{cfg.port}/{cfg.database}?ssl={match cfg.sslMode with | .disable => "disable" | .prefer => "prefer" | .require => "require"}&ssrf={if cfg.ssrfGuard then "1" else "0"}"

structure PgConn where
  poolKey  : String
  handle   : UInt64
  buf      : ByteArray
  off      : Nat
  txStatus : UInt8 := 0x49
  healthy  : Bool := true

private def pgPoolMaxIdlePerDsn : Nat := 8
private def pgPoolIdleTimeoutMs : Nat := 60000
initialize pgPoolBox : IO.Ref (Std.HashMap String (Array (UInt64 × Nat))) ← IO.mkRef {}
private def closePgHandle (handle : UInt64) (sendTerm : Bool := true) : IO Unit := do
  if sendTerm then discard <| Prim.outboundWriteAll handle (encodeMsg 0x58 ByteArray.empty)
  Prim.outboundRelease handle 0
private def partitionPoolEntries (arr : Array (UInt64 × Nat)) (nowMs : Nat) : Array (UInt64 × Nat) × List UInt64 :=
  arr.foldl (init := (#[], [])) fun (l, ex) e => if nowMs - e.2 ≤ pgPoolIdleTimeoutMs then (l.push e, ex) else (l, e.1 :: ex)

private def connectPg (cfg : PgConnParams) : PgM PgConn := do
  let (handleNat, _) ← mapErr "postgres connect failed" <| liftE (Prim.outboundAcquire 0 cfg.host cfg.port (if cfg.ssrfGuard then 1 else 0) (if cfg.ssrfGuard then Net.isBlockedIpBytes else fun _ => false))
  let handle := UInt64.ofNat handleNat
  let writeOr (lbl : String) (bs : ByteArray) := mapErr s!"postgres {lbl} write failed" <| liftE (Prim.outboundWriteAll handle bs)
  try
    if cfg.sslMode != .disable then
      writeOr "SSLRequest" (pushU32BE (pushU32BE ByteArray.empty 8) 80877103)
      let reply ← mapErr "postgres SSLRequest read failed" <| liftE (Prim.outboundReadSome handle 1)
      if reply.size >= 1 && reply[0]! == 0x53 then liftE (Prim.outboundUpgradeTls handle cfg.host)
      else if cfg.sslMode == .require then throw "PostgreSQL server rejected TLS but sslmode=require"
    writeOr "startup" (encodeStartup cfg.user cfg.database)
    let (b, o) ← mapErr "postgres auth failed" <| authLoop handle cfg ByteArray.empty 0 "" "" 64
    return { poolKey := cfg.poolKey, handle, buf := b, off := o, txStatus := 0x49, healthy := true }
  catch e => Prim.outboundRelease handle 0; throw e

private def acquirePooledLoop (cfg : PgConnParams) (key : String) (nowMs : Nat) : Nat → PgM (PgConn × Bool)
  | 0 => (·, false) <$> connectPg cfg
  | fuel + 1 => do
      let (cand?, expired) ← pgPoolBox.modifyGet fun m => match m[key]? with
        | none => ((none, []), m)
        | some arr =>
            let (live, ex) := partitionPoolEntries arr nowMs
            if h : live.size > 0 then
              let rest := live.pop; ((some live[live.size - 1].1, ex), if rest.isEmpty then m.erase key else m.insert key rest)
            else ((none, ex), m.erase key)
      expired.forM (closePgHandle · true)
      match cand? with
      | none => (·, false) <$> connectPg cfg
      | some h =>
          if ← Prim.outboundIsAlive h then return ({ poolKey := key, handle := h, buf := ByteArray.empty, off := 0, txStatus := 0x49, healthy := true }, true)
          else closePgHandle h false; acquirePooledLoop cfg key nowMs fuel

def acquireConn (cfg : PgConnParams) : IO (Except String (PgConn × Bool)) := do
  (acquirePooledLoop cfg cfg.poolKey (← Prim.nowMs).toNat (pgPoolMaxIdlePerDsn + 2)).run
def releaseConn (conn : PgConn) : IO Unit := do
  if !conn.healthy || conn.txStatus != 0x49 || conn.off < conn.buf.size then closePgHandle conn.handle conn.healthy; return
  let nowMs := (← Prim.nowMs).toNat
  let evicted ← pgPoolBox.modifyGet fun m =>
    let (live, expired) := partitionPoolEntries (m[conn.poolKey]?.getD #[]) nowMs
    if live.size < pgPoolMaxIdlePerDsn then (expired, m.insert conn.poolKey (live.push (conn.handle, nowMs)))
    else let (ev, kept) := if h : 0 < live.size then (live[0].1 :: expired, live.extract 1 live.size) else (expired, live)
         (ev, m.insert conn.poolKey (kept.push (conn.handle, nowMs)))
  evicted.forM (closePgHandle · true)

private def runWireOnConn (conn : PgConn) (wire : ByteArray) (errPrefix : String) (fuel : Nat) : IO (Except String (DbResult × String × PgConn) × PgConn) := do
  match ← Prim.outboundWriteAll conn.handle wire with
  | .error e => return (.error s!"{errPrefix}: {e}", { conn with healthy := false })
  | .ok () => match ← (collectQueryResultLoop conn.handle conn.buf conn.off #[] #[] 0 "" none fuel).run with
      | .error transportErr => return (.error transportErr, { conn with healthy := false })
      | .ok (qRes, b', o', status) => let conn' := { conn with buf := b', off := o', txStatus := status, healthy := true }; return (qRes.map fun (r, tag) => (r, tag, conn'), conn')
def execOnConn (conn : PgConn) (sql : String) (params : Array SqlVal) : IO (Except String (DbResult × PgConn) × PgConn) := do
  let (res, conn') ← runWireOnConn conn (encodeParse sql ++ encodeBind params ++ encodeMsg 0x44 (pushCString (ByteArray.empty.push 0x50) "") ++
    encodeMsg 0x45 (pushU32BE (pushCString ByteArray.empty "") 0) ++ encodeMsg 0x53 ByteArray.empty) "postgres query write failed" 65536
  return (res.map fun (r, _, c) => (r, c), conn')
def execSimpleOnConnTag (conn : PgConn) (sql : String) : IO (Except String (String × PgConn) × PgConn) := do
  let (res, conn') ← runWireOnConn conn (encodeMsg 0x51 (pushCString ByteArray.empty sql)) "postgres simple query write failed" 4096
  return (res.map fun (_, tag, c) => (tag, c), conn')
def execSimpleOnConn (conn : PgConn) (sql : String) : IO (Except String PgConn × PgConn) := do
  let (res, conn') ← execSimpleOnConnTag conn sql
  return (res.map Prod.snd, conn')

private def execParameterizedAttempt (cfg : PgConnParams) (sql : String) (params : Array SqlVal) : Nat → PgM DbResult
  | 0 => throw "postgres query failed after retry"
  | attemptsLeft + 1 => do
      let (conn, wasReused) ← liftE (acquireConn cfg); let (res, conn') ← execOnConn conn sql params
      match res with
      | .ok (dbRes, cFinal) => releaseConn cFinal; return dbRes
      | .error e => releaseConn conn'; if !conn'.healthy && wasReused && attemptsLeft > 0 then execParameterizedAttempt cfg sql params attemptsLeft else throw e
def execParameterized (pgUrl : String) (sql : String) (params : Array SqlVal) (ssrfGuard : Bool := false) : IO (Except String DbResult) :=
  ExceptT.run do let cfg ← liftP (parsePgUrl pgUrl); execParameterizedAttempt { cfg with ssrfGuard } sql params 2
def clearPool : IO Unit := do
  (← pgPoolBox.modifyGet fun m => (m.toList.foldl (init := []) (fun acc (_, arr) => arr.foldl (init := acc) fun a e => e.1 :: a), {})).forM (closePgHandle · true)
def execDdl (pgUrl : String) (ddl : String) (ssrfGuard : Bool := false) : IO (Except String Unit) :=
  ExceptT.run do
    if ddl.trimAscii.toString.isEmpty then return ()
    let cfg ← liftP (parsePgUrl pgUrl)
    let (conn, _) ← liftE (acquireConn { cfg with ssrfGuard })
    let (res, conn') ← execSimpleOnConn conn ddl; releaseConn conn'; discard <| liftP res
end Qed.Server.Db.PgWire
