import Tests.Native.Harness
import Tests.DbChecks
import Qed.Server.Db.Core
import Qed.Server.Db.PgWire

open Qed.Server
open Qed.Server.Db

namespace Tests.Native.Database

/-! ## Pure Native Lean HTTP SQL Mock Server (Backed by `Prim.sqliteExec`, Zero Python!) -/

structure HttpSqlMock where
  url        : String
  seenSqlRef : IO.Ref (Array (String × Nat))
  stop       : IO Unit

private def startHttpSqlMock (sqliteFile : String) : IO (Except String HttpSqlMock) := do
  match ← Prim.tcpListen 0 with
  | .error e => return .error e
  | .ok (lid, port) =>
      let seenSqlRef ← IO.mkRef (#[] : Array (String × Nat))
      let runningRef ← IO.mkRef true
      let _ ← IO.asTask (prio := .dedicated) do
        while ← runningRef.get do
          match ← Prim.tcpAccept lid 100 with
          | .error "timeout" => pure ()
          | .error _ => break
          | .ok conn =>
              try
                if let some (_, _, _, body) ← readOneHttpReq conn then
                  let bodyStr := (String.fromUTF8? body).getD ""
                  let (status, respStr) ← match Qed.Json.parse bodyStr 128 with
                    | .error e => pure (400, s!"\{\"error\":\"bad json: {e}\"}")
                    | .ok (.obj fs) =>
                        let sql := match fs.lookup "sql" with | some (.str s) => s | _ => ""
                        let paramsArr := match fs.lookup "params" with | some (.arr ps) => ps | _ => []
                        seenSqlRef.modify (·.push (sql, paramsArr.length))
                        let paramsJson := Qed.Json.render (.arr paramsArr)
                        match ← Prim.sqliteExec sqliteFile sql paramsJson with
                        | .ok rawJson => pure (200, rawJson)
                        | .error e    => pure (400, Qed.Json.render (.obj [("error", .str e)]))
                    | .ok _ => pure (400, "{\"error\":\"expected object\"}")
                  let respWire := Qed.Server.Http.formatHttpResponse status "application/json" respStr.toUTF8 false false true
                  discard <| Prim.outboundWriteAll conn respWire
              catch _ => pure ()
              Prim.outboundRelease conn 0
      return .ok {
        url := s!"http://127.0.0.1:{port}/query"
        seenSqlRef
        stop := do runningRef.set false; Prim.tcpCloseListener lid
      }

/-! ## Pure Native Lean PostgreSQL v3 Wire Protocol Mock Server (with SCRAM-SHA-256 & `Prim.sqliteExec`) -/

private def pushU16BE (ba : ByteArray) (v : Nat) : ByteArray :=
  (ba.push (UInt8.ofNat ((v >>> 8) &&& 0xFF))).push (UInt8.ofNat (v &&& 0xFF))

private def pushU32BE (ba : ByteArray) (v : Nat) : ByteArray :=
  let b0 := UInt8.ofNat ((v >>> 24) &&& 0xFF)
  let b1 := UInt8.ofNat ((v >>> 16) &&& 0xFF)
  let b2 := UInt8.ofNat ((v >>> 8) &&& 0xFF)
  let b3 := UInt8.ofNat (v &&& 0xFF)
  (((ba.push b0).push b1).push b2).push b3

private def readU16BE (ba : ByteArray) (off : Nat) : Nat :=
  if off + 2 ≤ ba.size then ((ba[off]!).toNat <<< 8) ||| (ba[off + 1]!).toNat else 0

private def readU32BE (ba : ByteArray) (off : Nat) : Nat :=
  if off + 4 ≤ ba.size then
    ((ba[off]!).toNat <<< 24) ||| ((ba[off + 1]!).toNat <<< 16) |||
    ((ba[off + 2]!).toNat <<< 8) ||| (ba[off + 3]!).toNat
  else 0

private def readI32BE (ba : ByteArray) (off : Nat) : Int :=
  let u := readU32BE ba off
  if u >= 2147483648 then (u : Int) - 4294967296 else (u : Int)

private def pgFrame (tag : Char) (payload : ByteArray) : ByteArray :=
  pushU32BE (ByteArray.empty.push (UInt8.ofNat tag.toNat)) (4 + payload.size) ++ payload

private def pgAuthMsg (code : Nat) (extra : ByteArray := ByteArray.empty) : ByteArray :=
  pgFrame 'R' (pushU32BE ByteArray.empty code ++ extra)

private def pgReadyForQuery : ByteArray := pgFrame 'Z' "I".toUTF8

private def pgCommandComplete (tag : String) : ByteArray :=
  pgFrame 'C' (tag.toUTF8.push 0)

private def pgErrorResponse (msg : String) : ByteArray :=
  pgFrame 'E' ((("M".toUTF8 ++ msg.toUTF8).push 0).push 0)

private def pgRowDescription (sampleRow : Array SqlVal) : ByteArray := Id.run do
  let mut p := pushU16BE ByteArray.empty sampleRow.size
  for i in [0 : sampleRow.size] do
    let nameBytes := s!"c{i}".toUTF8.push 0
    let oid : Nat := match sampleRow[i]! with
      | .int _   => 20
      | .bool _  => 16
      | .bytes _ => 17
      | _        => 25
    let colMeta := pushU16BE (pushU32BE (pushU16BE (pushU32BE (pushU16BE (pushU32BE ByteArray.empty 0) 0) oid) 0xFFFF) 0xFFFFFFFF) 0
    p := p ++ nameBytes ++ colMeta
  return pgFrame 'T' p

private def pgDataRow (row : Array SqlVal) : ByteArray := Id.run do
  let mut p := pushU16BE ByteArray.empty row.size
  for cell in row do
    match cell with
    | .null =>
        p := pushU32BE p 0xFFFFFFFF
    | .int i =>
        let b := (toString i).toUTF8
        p := pushU32BE p b.size ++ b
    | .text s =>
        let b := s.toUTF8
        p := pushU32BE p b.size ++ b
    | .bool b =>
        let s := if b then "t".toUTF8 else "f".toUTF8
        p := pushU32BE p s.size ++ s
    | .bytes bs =>
        let s := ("\\x" ++ Qed.Proto.encodeHex bs).toUTF8
        p := pushU32BE p s.size ++ s
  return pgFrame 'D' p

/-- Translates PostgreSQL `$1, $2, ...` placeholders into SQLite `?` placeholders, reordering params. -/
private def translatePgSql (sql : String) (params : Array SqlVal) : String × Array SqlVal := Id.run do
  let cs := sql.toList.toArray
  let mut out : Array Char := #[]
  let mut bound : Array SqlVal := #[]
  let mut i : Nat := 0
  let mut inSingleQuote := false
  while i < cs.size do
    let ch := cs[i]!
    if ch == '\'' then
      inSingleQuote := !inSingleQuote
      out := out.push ch
      i := i + 1
    else if !inSingleQuote && ch == '$' && i + 1 < cs.size && cs[i + 1]!.isDigit then
      let mut j := i + 1
      let mut numStr := ""
      while j < cs.size && cs[j]!.isDigit do
        numStr := numStr.push cs[j]!
        j := j + 1
      let idx := numStr.toNat?.getD 1
      bound := bound.push (params.getD (idx - 1) .null)
      out := out.push '?'
      i := j
    else
      out := out.push ch
      i := i + 1
  return (String.ofList out.toList, bound)

private def findZeroByte (ba : ByteArray) (start : Nat) : Nat := Id.run do
  for i in [start : ba.size] do
    if ba[i]! == 0 then return i
  return ba.size

private def xorBytes (a b : ByteArray) : ByteArray := Id.run do
  let n := min a.size b.size
  let mut out := ByteArray.emptyWithCapacity n
  for i in [0 : n] do
    out := out.push (a[i]! ^^^ b[i]!)
  return out

structure PgWireMock where
  url            : String
  parsedSqlRef   : IO.Ref (Array String)
  scramCountRef  : IO.Ref Nat
  startupOkRef   : IO.Ref Bool
  stop           : IO Unit

private partial def handlePgConn (conn : UInt64) (sqliteFile expectedUser expectedPass expectedDb : String)
    (parsedSqlRef : IO.Ref (Array String)) (scramCountRef : IO.Ref Nat) (startupOkRef : IO.Ref Bool) : IO Unit := do
  let mut buf := ByteArray.empty
  let mut stage := "startup"
  let mut clientFirstBare := ""
  let mut serverFirst := ""
  let saltBytes := "qedsalt012345678".toUTF8
  let iters : Nat := 4096
  let mut preparedSql := ""
  let mut boundParams : Array SqlVal := #[]

  let readMore (b : ByteArray) : IO (Option ByteArray) := do
    match ← Prim.outboundReadSome conn 16384 with
    | .error _ => return none
    | .ok chunk => if chunk.size == 0 then return none else return some (b ++ chunk)

  let mut alive := true
  while alive do
    if stage == "startup" then
      while buf.size < 4 do
        match ← readMore buf with
        | none => alive := false; break
        | some b' => buf := b'
      if !alive then break
      let len := readU32BE buf 0
      while buf.size < len do
        match ← readMore buf with
        | none => alive := false; break
        | some b' => buf := b'
      if !alive then break
      let body := buf.extract 4 len
      buf := buf.extract len buf.size
      let code := readU32BE body 0
      if code == 80877103 then
        discard <| Prim.outboundWriteAll conn "N".toUTF8
        continue
      -- Parse StartupMessage null-terminated key/value pairs
      let kvRaw := (String.fromUTF8? (body.extract 4 body.size)).getD ""
      let parts := kvRaw.splitOn "\x00"
      let mut gotUser := ""
      let mut gotDb := ""
      let rec scanKv : List String → String × String
        | k :: v :: rest =>
            let (u, d) := scanKv rest
            (if k == "user" then v else u, if k == "database" then v else d)
        | _ => ("", "")
      let (u, d) := scanKv parts
      gotUser := u; gotDb := d
      if gotUser == expectedUser && gotDb == expectedDb then
        startupOkRef.set true
      discard <| Prim.outboundWriteAll conn (pgAuthMsg 10 ((("SCRAM-SHA-256".toUTF8).push 0).push 0))
      stage := "scram_init"
      continue

    while buf.size < 5 do
      match ← readMore buf with
      | none => alive := false; break
      | some b' => buf := b'
    if !alive then break
    let tag := Char.ofNat (buf[0]!).toNat
    let len := readU32BE buf 1
    while buf.size < 1 + len do
      match ← readMore buf with
      | none => alive := false; break
      | some b' => buf := b'
    if !alive then break
    let payload := buf.extract 5 (1 + len)
    buf := buf.extract (1 + len) buf.size

    if stage == "scram_init" && tag == 'p' then
      let nul := findZeroByte payload 0
      let mech := (String.fromUTF8? (payload.extract 0 nul)).getD ""
      let initLen := readI32BE payload (nul + 1)
      let cf := (String.fromUTF8? (payload.extract (nul + 5) (nul + 5 + initLen.toNat))).getD ""
      if mech != "SCRAM-SHA-256" || !cf.startsWith "n,," then
        discard <| Prim.outboundWriteAll conn (pgErrorResponse "unsupported SASL mechanism")
        break
      clientFirstBare := String.ofList (cf.toList.drop 3)
      let clientNonce := match (clientFirstBare.splitOn "r=").drop 1 with
        | r :: _ => (r.splitOn ",").headD ""
        | [] => ""
      let serverNonce := clientNonce ++ "qedservernonce9876"
      let saltB64 := Qed.Server.Net.base64Encode saltBytes
      serverFirst := s!"r={serverNonce},s={saltB64},i={iters}"
      discard <| Prim.outboundWriteAll conn (pgAuthMsg 11 serverFirst.toUTF8)
      stage := "scram_final"
    else if stage == "scram_final" && tag == 'p' then
      let cf := (String.fromUTF8? payload).getD ""
      match cf.splitOn ",p=" with
      | [clientFinalNoProof, clientProofB64] =>
          let salted ← Prim.pbkdf2HmacSha256 expectedPass.toUTF8 saltBytes iters.toUInt32
          let clientKey ← Prim.hmacSha256 salted "Client Key".toUTF8
          let storedKey ← Prim.sha256 clientKey
          let serverKey ← Prim.hmacSha256 salted "Server Key".toUTF8
          let authMsg := s!"{clientFirstBare},{serverFirst},{clientFinalNoProof}"
          let clientSig ← Prim.hmacSha256 storedKey authMsg.toUTF8
          let expectedProof := Qed.Server.Net.base64Encode (xorBytes clientKey clientSig)
          if clientProofB64 != expectedProof then
            discard <| Prim.outboundWriteAll conn (pgErrorResponse "SCRAM-SHA-256 authentication failed")
            break
          let serverSig ← Prim.hmacSha256 serverKey authMsg.toUTF8
          scramCountRef.modify (· + 1)
          let okBundle :=
            pgAuthMsg 12 (s!"v={Qed.Server.Net.base64Encode serverSig}").toUTF8 ++
            pgAuthMsg 0 ++ pgReadyForQuery
          discard <| Prim.outboundWriteAll conn okBundle
          stage := "ready"
      | _ =>
          discard <| Prim.outboundWriteAll conn (pgErrorResponse "malformed SASLResponse")
          break
    else if stage == "ready" then
      if tag == 'Q' then
        let sql := (String.fromUTF8? (payload.extract 0 (payload.size - 1))).getD ""
        match ← Prim.sqliteDdl sqliteFile sql with
        | .ok () => discard <| Prim.outboundWriteAll conn (pgCommandComplete "CREATE TABLE" ++ pgReadyForQuery)
        | .error e => discard <| Prim.outboundWriteAll conn (pgErrorResponse e ++ pgReadyForQuery)
      else if tag == 'P' then
        let n1 := findZeroByte payload 0
        let n2 := findZeroByte payload (n1 + 1)
        preparedSql := (String.fromUTF8? (payload.extract (n1 + 1) n2)).getD ""
        discard <| Prim.outboundWriteAll conn (pgFrame '1' ByteArray.empty)
      else if tag == 'B' then
        let o1 := findZeroByte payload 0 + 1
        let o2 := findZeroByte payload o1 + 1
        let fmtCnt := readU16BE payload o2
        let mut off := o2 + 2 + fmtCnt * 2
        let paramCnt := readU16BE payload off
        off := off + 2
        let mut ps : Array SqlVal := #[]
        for _ in [0 : paramCnt] do
          let pLen := readI32BE payload off
          off := off + 4
          if pLen < 0 then
            ps := ps.push .null
          else
            let raw := (String.fromUTF8? (payload.extract off (off + pLen.toNat))).getD ""
            off := off + pLen.toNat
            ps := ps.push (.text raw)
        boundParams := ps
        parsedSqlRef.modify (·.push preparedSql)
        discard <| Prim.outboundWriteAll conn (pgFrame '2' ByteArray.empty)
      else if tag == 'D' then
        pure ()
      else if tag == 'E' then
        let (sqliteSql, sqliteParams) := translatePgSql preparedSql boundParams
        let paramsJson := encodeTaggedParamsJson sqliteParams
        match ← Prim.sqliteExec sqliteFile sqliteSql paramsJson with
        | .error e => discard <| Prim.outboundWriteAll conn (pgErrorResponse e)
        | .ok rawJson =>
            match decodeTaggedResultJson rawJson with
            | .error e => discard <| Prim.outboundWriteAll conn (pgErrorResponse e)
            | .ok res =>
                let mut frames := ByteArray.empty
                if h : 0 < res.rows.size then
                  frames := frames ++ pgRowDescription res.rows[0]
                  for row in res.rows do
                    frames := frames ++ pgDataRow row
                else if preparedSql.trimAscii.toString.toUpper.startsWith "SELECT COUNT" then
                  frames := frames ++ pgRowDescription #[.int 0]
                let verb := (preparedSql.trimAscii.toString.splitOn " ").headD "OK" |>.toUpper
                let tagStr :=
                  if verb == "INSERT" then s!"INSERT 0 {res.affected}"
                  else s!"{verb} {if res.rows.size > 0 then res.rows.size else res.affected}"
                frames := frames ++ pgCommandComplete tagStr
                discard <| Prim.outboundWriteAll conn frames
      else if tag == 'S' then
        discard <| Prim.outboundWriteAll conn pgReadyForQuery
      else if tag == 'X' then
        break

private def startPgWireMock (sqliteFile user pass dbName : String) : IO (Except String PgWireMock) := do
  match ← Prim.tcpListen 0 with
  | .error e => return .error e
  | .ok (lid, port) =>
      let parsedSqlRef ← IO.mkRef (#[] : Array String)
      let scramCountRef ← IO.mkRef 0
      let startupOkRef ← IO.mkRef false
      let runningRef ← IO.mkRef true
      let _ ← IO.asTask (prio := .dedicated) do
        while ← runningRef.get do
          match ← Prim.tcpAccept lid 100 with
          | .error "timeout" => pure ()
          | .error _ => break
          | .ok conn =>
              try
                handlePgConn conn sqliteFile user pass dbName parsedSqlRef scramCountRef startupOkRef
              catch _ => pure ()
              Prim.outboundRelease conn 0
      return .ok {
        url := s!"postgres://{user}:{pass}@127.0.0.1:{port}/{dbName}?sslmode=disable"
        parsedSqlRef, scramCountRef, startupOkRef
        stop := do runningRef.set false; Prim.tcpCloseListener lid
      }

/-! ## Shared VaultApp RPC Verification Suite Across All 3 Transports -/

private def callRpc (port : UInt16) (fn : String) (reqBytes : ByteArray := ByteArray.empty)
    (tok? : Option String := none) : IO (Except String HttpResp) :=
  let hdrs := #[("Content-Type", "application/x-protobuf")] ++
    match tok? with | some t => #[("Authorization", s!"Bearer {t}")] | none => #[]
  httpReq port "POST" s!"/_qed/rpc/VaultApi/{fn}" hdrs reqBytes

private def runVaultSuite (c : TestChecker) (label : String) (srv : NativeServerProc)
    (aliceTok bobTok : String) (testRestart : Bool := false) : IO Unit := do
  let sqli := "' OR 1=1; DROP TABLE notes; --"

  -- Auth & `requires` enforcement
  match ← callRpc srv.port "createNote" (Qed.Proto.encode ((1 : Nat), "hi")) none with
  | .ok r => c.checkEq s!"[{label}] unauthenticated createNote rejected (401)" r.status 401
  | .error e => c.check s!"[{label}] unauth createNote" false e

  match ← callRpc srv.port "createNote" (Qed.Proto.encode ((1 : Nat), "")) (some aliceTok) with
  | .ok r => c.checkEq s!"[{label}] empty body rejected by requires (400)" r.status 400
  | .error e => c.check s!"[{label}] empty body createNote" false e

  -- Alice creates normal note + SQLi note (createNote returns `Except (RpcDomainError _) VaultDb.notes`)
  let decodeCreated (bs : ByteArray) : Option DbChecks.VaultDb.notes :=
    match Qed.Proto.decode (α := Except (Qed.RpcDomainError DbChecks.VaultApi.createNote.Error) DbChecks.VaultDb.notes) bs with
    | .ok (.ok n) => some n
    | _ => none

  match ← callRpc srv.port "createNote" (Qed.Proto.encode ((1 : Nat), "hello verified db")) (some aliceTok) with
  | .ok r =>
      c.checkEq s!"[{label}] alice createNote(1) status 200" r.status 200
      let got := decodeCreated r.body
      c.check s!"[{label}] alice createNote(1) payload"
        (got == some { id := 1, ownerId := "alice", body := "hello verified db", version := 0, status := "draft" })
        (reprStr got)
  | .error e => c.check s!"[{label}] alice createNote(1)" false e

  match ← callRpc srv.port "createNote" (Qed.Proto.encode ((2 : Nat), sqli)) (some aliceTok) with
  | .ok r =>
      c.checkEq s!"[{label}] alice createNote(2) SQLi stored safely" r.status 200
      c.checkEq s!"[{label}] alice createNote(2) verbatim body" ((decodeCreated r.body).map (·.body)) (some sqli)
  | .error e => c.check s!"[{label}] alice createNote(2)" false e

  -- Count & list for Alice
  match ← callRpc srv.port "countMyNotes" ByteArray.empty (some aliceTok) with
  | .ok r => c.checkEq s!"[{label}] alice countMyNotes == 2" (Qed.Proto.decode (α := Nat) r.body) (.ok 2)
  | .error e => c.check s!"[{label}] alice countMyNotes" false e

  match ← callRpc srv.port "listMyNotes" ByteArray.empty (some aliceTok) with
  | .ok r =>
      let n := match Qed.Proto.decode (α := Array DbChecks.VaultDb.notes) r.body with | .ok a => a.size | _ => 999
      c.checkEq s!"[{label}] alice listMyNotes returns 2 notes" n 2
  | .error e => c.check s!"[{label}] alice listMyNotes" false e

  -- Row-Level Security (RLS): Bob cannot read, count, edit, or delete Alice's notes!
  match ← callRpc srv.port "listMyNotes" ByteArray.empty (some bobTok) with
  | .ok r =>
      let n := match Qed.Proto.decode (α := Array DbChecks.VaultDb.notes) r.body with | .ok a => a.size | _ => 999
      c.checkEq s!"[{label}] bob listMyNotes == 0 (RLS)" n 0
  | .error e => c.check s!"[{label}] bob listMyNotes" false e

  match ← callRpc srv.port "countMyNotes" ByteArray.empty (some bobTok) with
  | .ok r => c.checkEq s!"[{label}] bob countMyNotes == 0 (RLS)" (Qed.Proto.decode (α := Nat) r.body) (.ok 0)
  | .error e => c.check s!"[{label}] bob countMyNotes" false e

  match ← callRpc srv.port "getNote" (Qed.Proto.encode (1 : Nat)) (some bobTok) with
  | .ok r => c.checkEq s!"[{label}] bob getNote(1) == none (RLS)" (Qed.Proto.decode (α := Option DbChecks.VaultDb.notes) r.body) (.ok none)
  | .error e => c.check s!"[{label}] bob getNote" false e

  match ← callRpc srv.port "editNote" (Qed.Proto.encode ((1 : Nat), "pwned")) (some bobTok) with
  | .ok r => c.checkEq s!"[{label}] bob editNote(1) == none (RLS)" (Qed.Proto.decode (α := Option DbChecks.VaultDb.notes) r.body) (.ok none)
  | .error e => c.check s!"[{label}] bob editNote" false e

  match ← callRpc srv.port "deleteNote" (Qed.Proto.encode (1 : Nat)) (some bobTok) with
  | .ok r => c.checkEq s!"[{label}] bob deleteNote(1) == 0 (RLS)" (Qed.Proto.decode (α := Nat) r.body) (.ok 0)
  | .error e => c.check s!"[{label}] bob deleteNote" false e

  -- Alice edits note 1 (version 0 -> 1) and publishes (draft -> published, version 1 -> 2)
  match ← callRpc srv.port "editNote" (Qed.Proto.encode ((1 : Nat), "updated text")) (some aliceTok) with
  | .ok r =>
      c.checkEq s!"[{label}] alice editNote(1) updated"
        (Qed.Proto.decode (α := Option DbChecks.VaultDb.notes) r.body)
        (.ok (some { id := 1, ownerId := "alice", body := "updated text", version := 1, status := "draft" }))
  | .error e => c.check s!"[{label}] alice editNote(1)" false e

  match ← callRpc srv.port "publishNote" (Qed.Proto.encode (1 : Nat)) (some aliceTok) with
  | .ok r =>
      c.checkEq s!"[{label}] alice publishNote(1) draft -> published"
        (Qed.Proto.decode (α := Option DbChecks.VaultDb.notes) r.body)
        (.ok (some { id := 1, ownerId := "alice", body := "updated text", version := 2, status := "published" }))
  | .error e => c.check s!"[{label}] alice publishNote(1)" false e

  match ← callRpc srv.port "publishNote" (Qed.Proto.encode (1 : Nat)) (some aliceTok) with
  | .ok r =>
      c.checkEq s!"[{label}] alice publishNote(1) twice returns none"
        (Qed.Proto.decode (α := Option DbChecks.VaultDb.notes) r.body) (.ok none)
  | .error e => c.check s!"[{label}] alice publishNote twice" false e

  -- Persistence across full native server restart
  if testRestart then
    let restarted ← srv.restart
    c.check s!"[{label}] server restarted cleanly" restarted
    match ← callRpc srv.port "getNote" (Qed.Proto.encode (1 : Nat)) (some aliceTok) with
    | .ok r =>
        c.checkEq s!"[{label}] note 1 persisted across restart"
          (Qed.Proto.decode (α := Option DbChecks.VaultDb.notes) r.body)
          (.ok (some { id := 1, ownerId := "alice", body := "updated text", version := 2, status := "published" }))
    | .error e => c.check s!"[{label}] getNote(1) after restart" false e
    match ← callRpc srv.port "getNote" (Qed.Proto.encode (2 : Nat)) (some aliceTok) with
    | .ok r =>
        let b := match Qed.Proto.decode (α := Option DbChecks.VaultDb.notes) r.body with | .ok (some n) => some n.body | _ => none
        c.checkEq s!"[{label}] SQLi note 2 persisted verbatim across restart" b (some sqli)
    | .error e => c.check s!"[{label}] getNote(2) after restart" false e

  -- Delete note 2
  match ← callRpc srv.port "deleteNote" (Qed.Proto.encode (2 : Nat)) (some aliceTok) with
  | .ok r => c.checkEq s!"[{label}] alice deleteNote(2) == 1" (Qed.Proto.decode (α := Nat) r.body) (.ok 1)
  | .error e => c.check s!"[{label}] alice deleteNote(2)" false e

  match ← callRpc srv.port "countMyNotes" ByteArray.empty (some aliceTok) with
  | .ok r => c.checkEq s!"[{label}] alice countMyNotes == 1 after delete" (Qed.Proto.decode (α := Nat) r.body) (.ok 1)
  | .error e => c.check s!"[{label}] alice countMyNotes after delete" false e

  -- Guarded atomic `books` update (`stock >= qty`)
  match ← callRpc srv.port "seedBook" (Qed.Proto.encode ("lean4", ("Theorem Proving in Lean 4", (10 : Nat)))) (some aliceTok) with
  | .ok r => c.checkEq s!"[{label}] seedBook status 200" r.status 200
  | .error e => c.check s!"[{label}] seedBook" false e

  match ← callRpc srv.port "listBooks" ByteArray.empty none with
  | .ok r =>
      c.checkEq s!"[{label}] listBooks returns 1 book"
        (Qed.Proto.decode (α := Array DbChecks.VaultDb.books) r.body)
        (.ok #[{ id := "lean4", title := "Theorem Proving in Lean 4", stock := 10 }])
  | .error e => c.check s!"[{label}] listBooks" false e

  match ← callRpc srv.port "orderBook" (Qed.Proto.encode ("lean4", (3 : Nat))) (some aliceTok) with
  | .ok r =>
      let st := match Qed.Proto.decode (α := Option DbChecks.VaultDb.books) r.body with | .ok (some b) => some b.stock | _ => none
      c.checkEq s!"[{label}] orderBook(3) stock 10 -> 7" st (some 7)
  | .error e => c.check s!"[{label}] orderBook(3)" false e

  match ← callRpc srv.port "orderBook" (Qed.Proto.encode ("lean4", (10 : Nat))) (some aliceTok) with
  | .ok r =>
      c.checkEq s!"[{label}] orderBook(10) when stock=7 returns none"
        (Qed.Proto.decode (α := Option DbChecks.VaultDb.books) r.body) (.ok none)
  | .error e => c.check s!"[{label}] orderBook(10)" false e

def run : IO Bool := do
  let c ← mkChecker "database"
  let some dir ← buildDevApp "Tests.DbChecks"
    | c.check "buildDevApp Tests.DbChecks" false; return ← c.finish

  checkLeakGate c "Tests.DbChecks" #[
    "DbChecks.VaultDb.config",
    "DbChecks.VaultDb.secrets",
    "DbChecks.VaultDb.ensureSchema",
    "DbChecks.VaultDb.ddl",
    "DbChecks.VaultDb.rlsDdl",
    "DbChecks.VaultApi.dispatchM",
    "DbChecks.VaultApi.createNote_handler"
  ]

  let authSecret := "db-test-hmac-secret-key"
  let aliceTok ← signSessionToken authSecret "alice"
  let bobTok ← signSessionToken authSecret "bob"
  let tmpDir ← makeTempDir "qed-db-native"
  try
    -- Transport 1: Native Embedded SQLite (with full server restart persistence!)
    let sqliteFile := s!"{tmpDir}/vault.db"
    let (srvSqlite, ok1) ← startNativeServer dir #[
      ("QED_WORKERS", some "2"),
      ("QED_AUTH_SECRET", some authSecret),
      ("QED_TEST_DB_URL", some s!"sqlite://{sqliteFile}")
    ]
    try
      c.check "[sqlite] native server healthy" ok1
      if ok1 then runVaultSuite c "sqlite" srvSqlite aliceTok bobTok (testRestart := true)
    finally
      srvSqlite.stop

    -- Transport 2: HTTP SQL (exact same binary, native Lean HTTP SQL mock backed by Prim.sqliteExec!)
    match ← startHttpSqlMock s!"{tmpDir}/http_mock.db" with
    | .error e => c.check "[http-sql] start mock" false e
    | .ok httpMock =>
        try
          let (srvHttp, ok2) ← startNativeServer dir #[
            ("QED_WORKERS", some "2"),
            ("QED_AUTH_SECRET", some authSecret),
            ("QED_TEST_DB_URL", some httpMock.url)
          ]
          try
            c.check "[http-sql] native server healthy" ok2
            if ok2 then
              runVaultSuite c "http-sql" srvHttp aliceTok bobTok
              let seen ← httpMock.seenSqlRef.get
              c.check "[http-sql] SQLi payload NEVER interpolated into SQL"
                (!(seen.any fun (s, _) => s.contains "DROP TABLE"))
              c.check "[http-sql] parameterized SQL sent with bound params"
                (seen.any fun (s, n) => s.contains "?" && n > 0)
          finally
            srvHttp.stop
        finally
          httpMock.stop

    -- Transport 3: Native PostgreSQL v3 Wire Protocol + SCRAM-SHA-256 (exact same binary!)
    match ← startPgWireMock s!"{tmpDir}/pg_mock.db" "qeduser" "qedpass" "qeddb" with
    | .error e => c.check "[pg-wire] start mock" false e
    | .ok pgMock =>
        try
          let (srvPg, ok3) ← startNativeServer dir #[
            ("QED_WORKERS", some "2"),
            ("QED_AUTH_SECRET", some authSecret),
            ("QED_TEST_DB_URL", some pgMock.url)
          ]
          try
            c.check "[pg-wire] native server healthy" ok3
            if ok3 then
              runVaultSuite c "pg-wire" srvPg aliceTok bobTok
              c.check "[pg-wire] StartupMessage sent expected user & db" (← pgMock.startupOkRef.get)
              c.check "[pg-wire] SCRAM-SHA-256 proof verified" ((← pgMock.scramCountRef.get) > 0)
              let parsed ← pgMock.parsedSqlRef.get
              c.check "[pg-wire] SQLi payload NEVER interpolated into Parse SQL"
                (!(parsed.any fun s => s.contains "DROP TABLE"))
              c.check "[pg-wire] Parse used $1 placeholders with Bind params"
                (parsed.any fun s => s.contains "$1")
          finally
            srvPg.stop
        finally
          pgMock.stop
  finally
    rmRf tmpDir
  c.finish

end Tests.Native.Database
