import Tests.Native.Harness
import Tests.DbChecks
import Qed.Server.Db.Core
import Qed.Server.Db.PgWire
import Qed.Server.Native

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

/-- Translates PostgreSQL `$1, $2, ...` placeholders and `STRPOS(` into SQLite equivalents. -/
private def translatePgSql (sql : String) (params : Array SqlVal) : String × Array SqlVal := Id.run do
  let sql := sql.replace "STRPOS(" "INSTR("
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
  let mut activeTxId? : Option UInt64 := none

  let readyFrame (tx? : Option UInt64) : ByteArray :=
    pgFrame 'Z' (if tx?.isSome then "T" else "I").toUTF8

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
        let sql := ((String.fromUTF8? (payload.extract 0 (payload.size - 1))).getD "").trimAscii.toString
        let upper := sql.toUpper
        if upper == "BEGIN" then
          match ← Prim.sqliteTxBegin sqliteFile with
          | .ok tid =>
              activeTxId? := some tid
              discard <| Prim.outboundWriteAll conn (pgCommandComplete "BEGIN" ++ readyFrame activeTxId?)
          | .error e =>
              discard <| Prim.outboundWriteAll conn (pgErrorResponse e ++ readyFrame activeTxId?)
        else if upper == "COMMIT" then
          match activeTxId? with
          | some tid =>
              activeTxId? := none
              match ← Prim.sqliteTxCommit tid with
              | .ok () => discard <| Prim.outboundWriteAll conn (pgCommandComplete "COMMIT" ++ readyFrame none)
              | .error e => discard <| Prim.outboundWriteAll conn (pgErrorResponse e ++ readyFrame none)
          | none =>
              discard <| Prim.outboundWriteAll conn (pgCommandComplete "COMMIT" ++ readyFrame none)
        else if upper == "ROLLBACK" then
          match activeTxId? with
          | some tid =>
              activeTxId? := none
              Prim.sqliteTxRollback tid
              discard <| Prim.outboundWriteAll conn (pgCommandComplete "ROLLBACK" ++ readyFrame none)
          | none =>
              discard <| Prim.outboundWriteAll conn (pgCommandComplete "ROLLBACK" ++ readyFrame none)
        else
          match ← Prim.sqliteDdl sqliteFile sql with
          | .ok () => discard <| Prim.outboundWriteAll conn (pgCommandComplete "CREATE TABLE" ++ readyFrame activeTxId?)
          | .error e => discard <| Prim.outboundWriteAll conn (pgErrorResponse e ++ readyFrame activeTxId?)
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
        let execRes ← match activeTxId? with
          | some tid => Prim.sqliteTxExec tid sqliteSql paramsJson
          | none     => Prim.sqliteExec sqliteFile sqliteSql paramsJson
        match execRes with
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
                else if preparedSql.trimAscii.toString.toUpper.startsWith "SELECT COUNT" ||
                        preparedSql.trimAscii.toString.toUpper.startsWith "SELECT SUM" ||
                        preparedSql.trimAscii.toString.toUpper.startsWith "SELECT MIN" ||
                        preparedSql.trimAscii.toString.toUpper.startsWith "SELECT MAX" then
                  frames := frames ++ pgRowDescription #[.int 0]
                let verb := (preparedSql.trimAscii.toString.splitOn " ").headD "OK" |>.toUpper
                let tagStr :=
                  if verb == "INSERT" then s!"INSERT 0 {res.affected}"
                  else s!"{verb} {if res.rows.size > 0 then res.rows.size else res.affected}"
                frames := frames ++ pgCommandComplete tagStr
                discard <| Prim.outboundWriteAll conn frames
      else if tag == 'S' then
        discard <| Prim.outboundWriteAll conn (readyFrame activeTxId?)
      else if tag == 'X' then
        if let some tid := activeTxId? then
          Prim.sqliteTxRollback tid
        break
  if let some tid := activeTxId? then
    Prim.sqliteTxRollback tid

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
              let _ ← IO.asTask (prio := .dedicated) do
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

/-! ## Direct Runtime Verification: Transactions, Richer SQL, FK Joins, Reader Pool & Migrations -/

@[implicit_reducible]
private def withRedirectedSqlite (sqlitePath : String) : MonadServer IO :=
  let base : MonadServer IO := Native.mkNativeServerInst none none
  let redir (cfg : DbConfig) : DbConfig :=
    { cfg with endpoint := .sqlitePath sqlitePath, devFallback? := none }
  { base with
    dbExec       := fun cfg q => base.dbExec (redir cfg) q
    dbExecDdl    := fun cfg => base.dbExecDdl (redir cfg)
    dbTxBegin    := fun cfg => base.dbTxBegin (redir cfg)
    dbTxExec     := fun cfg tid q => base.dbTxExec (redir cfg) tid q
    dbTxCommit   := fun cfg tid => base.dbTxCommit (redir cfg) tid
    dbTxRollback := fun cfg tid => base.dbTxRollback (redir cfg) tid
  }

private def withRedirectedPostgres (pgUrl : String) : IO (MonadServer IO) := do
  let txRef ← IO.mkRef ((1 : UInt64), ({} : Std.HashMap UInt64 Db.PgWire.PgConn))
  let base : MonadServer IO := Native.mkNativeServerInst none none
  return { base with
    dbExec := fun _ q => do
      let (sql, params) := q.compile .postgres
      match ← Db.PgWire.execParameterized pgUrl sql params with
      | .ok r    => return .ok r
      | .error e => return .error (ApiError.internal e)
    dbExecDdl := fun cfg => do
      let ddl := Db.renderDatabaseDdl .postgres cfg.tables
      match ← Db.PgWire.execDdl pgUrl ddl with
      | .ok ()   => return .ok ()
      | .error e => return .error (ApiError.internal e)
    dbTxBegin := fun _ => do
      let p ← match Db.PgWire.parsePgUrl pgUrl with
        | .ok p    => pure p
        | .error e => return .error (ApiError.internal e)
      match ← Db.PgWire.acquireConn p with
      | .error e => return .error (ApiError.internal e)
      | .ok (conn, _) =>
          let (res, conn') ← Db.PgWire.execSimpleOnConn conn "BEGIN"
          match res with
          | .error e =>
              Db.PgWire.releaseConn { conn' with healthy := false }
              return .error (ApiError.internal e)
          | .ok cReady =>
              let tid ← txRef.modifyGet fun (nxt, m) => (nxt, (nxt + 1, m.insert nxt cReady))
              return .ok tid
    dbTxExec := fun _ tid q => do
      let popped? ← txRef.modifyGet fun (nxt, m) =>
        match m[tid]? with
        | some c => (some c, (nxt, m.erase tid))
        | none   => (none, (nxt, m))
      let some conn := popped?
        | return .error (ApiError.internal "unknown PG tx")
      let (sql, params) := q.compile .postgres
      let (res, conn') ← Db.PgWire.execOnConn conn sql params
      match res with
      | .ok (dbRes, cNext) =>
          txRef.modify fun (nxt, m) => (nxt, m.insert tid cNext)
          return .ok dbRes
      | .error e =>
          if conn'.healthy then txRef.modify fun (nxt, m) => (nxt, m.insert tid conn')
          else Db.PgWire.releaseConn conn'
          return .error (ApiError.internal e)
    dbTxCommit := fun _ tid => do
      let popped? ← txRef.modifyGet fun (nxt, m) =>
        match m[tid]? with
        | some c => (some c, (nxt, m.erase tid))
        | none   => (none, (nxt, m))
      let some conn := popped? | return .error (ApiError.internal "unknown PG tx")
      let (res, conn') ← Db.PgWire.execSimpleOnConn conn "COMMIT"
      match res with
      | .ok cFinal => Db.PgWire.releaseConn cFinal; return .ok ()
      | .error e => Db.PgWire.releaseConn { conn' with healthy := false }; return .error (ApiError.internal e)
    dbTxRollback := fun _ tid => do
      let popped? ← txRef.modifyGet fun (nxt, m) =>
        match m[tid]? with
        | some c => (some c, (nxt, m.erase tid))
        | none   => (none, (nxt, m))
      if let some conn := popped? then
        let (res, conn') ← Db.PgWire.execSimpleOnConn conn "ROLLBACK"
        match res with
        | .ok cFinal => Db.PgWire.releaseConn cFinal
        | .error _   => Db.PgWire.releaseConn { conn' with healthy := false }
  }

private def runShopDirectSuite (c : TestChecker) (label : String) (srvInst : MonadServer IO)
    (testConcurrentReaders : Bool := false) : IO Unit := do
  let stBox ← Prim.mkStateBox DbChecks.ShopApi.initState
  let atomicInst : MonadAtomic DbChecks.ShopApi.State IO := Native.withStateBox stBox
  let aliceCtx : RequestCtx := { userId := some "alice" }
  let bobCtx   : RequestCtx := { userId := some "bob" }

  -- Initialize schema
  match ← @MonadServer.dbExecDdl IO srvInst DbChecks.ShopDb.config with
  | .ok () => c.check s!"[{label}] ShopDb schema initialized" true
  | .error e => c.check s!"[{label}] ShopDb schema init" false e.message; return

  let callShop (ctx : RequestCtx) (fn : String) (req : ByteArray) : IO (Except ApiError ByteArray) :=
    @DbChecks.ShopApi.dispatchM IO _ srvInst atomicInst ctx fn req

  -- Empty aggregates return 0 / none
  match ← callShop aliceCtx "totalInventoryValue" ByteArray.empty with
  | .ok bs => c.checkEq s!"[{label}] empty sum == 0" (Qed.Proto.decode (α := Nat) bs) (.ok 0)
  | .error e => c.check s!"[{label}] empty sum" false e.message

  match ← callShop aliceCtx "cheapestPrice" ByteArray.empty with
  | .ok bs => c.checkEq s!"[{label}] empty min == none" (Qed.Proto.decode (α := Option Nat) bs) (.ok none)
  | .error e => c.check s!"[{label}] empty min" false e.message

  -- 1. Multi-statement verified DB transaction (`db.transaction:` commit + `atomic:` state update)
  let mkTxReq (aid aname iid title : String) (price : Nat) :=
    Qed.Proto.encode (aid, (aname, (iid, (title, price))))
  match ← callShop aliceCtx "createAuthorAndItem" (mkTxReq "a1" "Ada Lovelace" "i1" "Lean 4 Proofs" 100) with
  | .ok bs =>
      let okItem := match Qed.Proto.decode (α := Except (Qed.RpcDomainError DbChecks.ShopApi.createAuthorAndItem.Error) DbChecks.ShopDb.items) bs with
        | .ok (.ok it) => it.id == "i1" && it.price == 100
        | _ => false
      c.check s!"[{label}] db.transaction: committed author + item" okItem
  | .error e => c.check s!"[{label}] createAuthorAndItem(i1)" false e.message

  match ← callShop aliceCtx "createAuthorAndItem" (mkTxReq "a2" "Alan Turing" "i2" "Lean 4 Compilers" 250) with
  | .ok _ => pure ()
  | .error e => c.check s!"[{label}] createAuthorAndItem(i2)" false e.message

  match ← callShop aliceCtx "createAuthorAndItem" (mkTxReq "a3" "Grace Hopper" "i3" "Rust Systems 100%" 50) with
  | .ok _ => pure ()
  | .error e => c.check s!"[{label}] createAuthorAndItem(i3)" false e.message

  let txOpsAfter ← Prim.atomicRead stBox (·.txOps)
  c.checkEq s!"[{label}] atomic txOps incremented 3 times inside transactions" txOpsAfter 3

  -- 2. Multi-statement DB transaction ROLLBACK on `fail(.aborted)` (`db.transaction:`)
  match ← callShop aliceCtx "createPairDotSyntax" (mkTxReq "a_rolled_back" "Ghost Author" "i_ghost" "Ghost Item" 99999) with
  | .ok bs =>
      let gotAborted := match Qed.Proto.decode (α := Except (Qed.RpcDomainError DbChecks.ShopApi.createPairDotSyntax.Error) DbChecks.ShopDb.items) bs with
        | .ok (.error err) => err.tag == .aborted
        | _ => false
      c.check s!"[{label}] db.transaction: returned fail(.aborted)" gotAborted
  | .error e => c.check s!"[{label}] createPairDotSyntax rollback" false e.message

  -- Verify the author inserted BEFORE `fail(.aborted)` was rolled back!
  let checkGhostAuthorQ := SqlQuery.count ⟨"authors", by decide⟩
    (.binOp .eq (.col ⟨"id", by decide⟩) (.param (.text "a_rolled_back")))
  match ← @MonadServer.dbExec IO srvInst DbChecks.ShopDb.config checkGhostAuthorQ with
  | .ok res =>
      let cnt : Int := match res.rows[0]?.bind (·[0]?) with | some (SqlVal.int n) => n | _ => -1
      c.checkEq s!"[{label}] rolled-back author does NOT exist in DB" cnt (0 : Int)
  | .error e => c.check s!"[{label}] verify rolled-back author" false e.message

  -- 3. Richer SQL: LIKE (`startsWith` + `contains`) + `orderBy` + `limit` + `offset`
  match ← callShop aliceCtx "searchItems" (Qed.Proto.encode ("Lean", ("4", (0 : Nat)))) with
  | .ok bs =>
      let ids := match Qed.Proto.decode (α := Array DbChecks.ShopDb.items) bs with
        | .ok arr => arr.map (·.id)
        | _ => #[]
      c.checkEq s!"[{label}] startsWith+contains+orderBy(-price) returns [i2, i1]" ids #["i2", "i1"]
  | .error e => c.check s!"[{label}] searchItems" false e.message

  -- Offset pagination skips first row
  match ← callShop aliceCtx "searchItems" (Qed.Proto.encode ("Lean", ("4", (1 : Nat)))) with
  | .ok bs =>
      let ids := match Qed.Proto.decode (α := Array DbChecks.ShopDb.items) bs with
        | .ok arr => arr.map (·.id)
        | _ => #[]
      c.checkEq s!"[{label}] offset=1 returns [i1]" ids #["i1"]
  | .error e => c.check s!"[{label}] searchItems offset" false e.message

  -- LIKE metacharacter `%` escaping: searching for "100%" only matches "Rust Systems 100%"
  match ← callShop aliceCtx "searchItems" (Qed.Proto.encode ("Rust", ("100%", (0 : Nat)))) with
  | .ok bs =>
      let ids := match Qed.Proto.decode (α := Array DbChecks.ShopDb.items) bs with
        | .ok arr => arr.map (·.id)
        | _ => #[]
      c.checkEq s!"[{label}] LIKE escapes literal % safely" ids #["i3"]
  | .error e => c.check s!"[{label}] searchItems literal %" false e.message

  -- 4. `IN (...)` list membership (non-empty and empty list!)
  match ← callShop aliceCtx "filterByIds" (Qed.Proto.encode (#["i3", "i1"] : Array String)) with
  | .ok bs =>
      let ids := match Qed.Proto.decode (α := Array DbChecks.ShopDb.items) bs with
        | .ok arr => arr.map (·.id)
        | _ => #[]
      c.checkEq s!"[{label}] IN list returns [i1, i3]" ids #["i1", "i3"]
  | .error e => c.check s!"[{label}] filterByIds" false e.message

  match ← callShop aliceCtx "filterByIds" (Qed.Proto.encode (#[] : Array String)) with
  | .ok bs =>
      let n := match Qed.Proto.decode (α := Array DbChecks.ShopDb.items) bs with | .ok a => a.size | _ => 999
      c.checkEq s!"[{label}] empty IN list returns 0 rows" n 0
  | .error e => c.check s!"[{label}] filterByIds empty" false e.message

  -- 5. Aggregates (`sum`, `min`, `max`) with ReadPolicy enforcement
  match ← callShop aliceCtx "totalInventoryValue" ByteArray.empty with
  | .ok bs => c.checkEq s!"[{label}] alice sum(price) == 400" (Qed.Proto.decode (α := Nat) bs) (.ok 400)
  | .error e => c.check s!"[{label}] alice sum" false e.message

  match ← callShop aliceCtx "cheapestPrice" ByteArray.empty with
  | .ok bs => c.checkEq s!"[{label}] alice min(price) == some 50" (Qed.Proto.decode (α := Option Nat) bs) (.ok (some 50))
  | .error e => c.check s!"[{label}] alice min" false e.message

  match ← callShop aliceCtx "highestPrice" ByteArray.empty with
  | .ok bs => c.checkEq s!"[{label}] alice max(price) == some 250" (Qed.Proto.decode (α := Option Nat) bs) (.ok (some 250))
  | .error e => c.check s!"[{label}] alice max" false e.message

  match ← callShop bobCtx "totalInventoryValue" ByteArray.empty with
  | .ok bs => c.checkEq s!"[{label}] bob sum(price) == 0 (RLS)" (Qed.Proto.decode (α := Nat) bs) (.ok 0)
  | .error e => c.check s!"[{label}] bob sum" false e.message

  -- 6. Typed FK `join` (`items` INNER JOIN `authors` on `authorId = id`, ordered by `-price`)
  match ← callShop aliceCtx "itemsWithAuthors" ByteArray.empty with
  | .ok bs =>
      let pairs := match Qed.Proto.decode (α := Array (DbChecks.ShopDb.items × DbChecks.ShopDb.authors)) bs with
        | .ok arr => arr.map fun (it, au) => (it.id, au.name)
        | _ => #[]
      c.checkEq s!"[{label}] FK join returns [(i2, Alan Turing), (i1, Ada Lovelace), (i3, Grace Hopper)]"
        pairs #[("i2", "Alan Turing"), ("i1", "Ada Lovelace"), ("i3", "Grace Hopper")]
  | .error e => c.check s!"[{label}] itemsWithAuthors" false e.message

  match ← callShop bobCtx "itemsWithAuthors" ByteArray.empty with
  | .ok bs =>
      let n := match Qed.Proto.decode (α := Array (DbChecks.ShopDb.items × DbChecks.ShopDb.authors)) bs with
        | .ok arr => arr.size | _ => 999
      c.checkEq s!"[{label}] bob FK join returns 0 (RLS)" n 0
  | .error e => c.check s!"[{label}] bob itemsWithAuthors" false e.message

  -- 7. SQLite concurrent reader pool stress test (8 parallel read tasks under WAL)
  if testConcurrentReaders then
    let mut readTasks : Array (Task (Except IO.Error Bool)) := #[]
    for _ in [0 : 8] do
      let t ← IO.asTask (prio := .dedicated) do
        match ← callShop aliceCtx "totalInventoryValue" ByteArray.empty with
        | .ok bs => return Qed.Proto.decode (α := Nat) bs == .ok 400
        | .error _ => return false
      readTasks := readTasks.push t
    let mut allOk := true
    for t in readTasks do
      match ← IO.wait t with
      | .ok true => pure ()
      | _ => allOk := false
    c.check s!"[{label}] 8 concurrent SQLite reader-pool queries succeeded" allOk

private def runMigrationSuite (c : TestChecker) (tmpDir : String) : IO Unit := do
  let migDb := s!"{tmpDir}/migrate.db"
  let v1Table : TableSchema := {
    name := ⟨"widgets", by decide⟩
    columns := [
      { name := ⟨"id", by decide⟩, colType := .text, isPrimaryKey := true },
      { name := ⟨"name", by decide⟩, colType := .text }
    ]
    indexes := []
  }
  let v1Cfg : DbConfig := { name := "MigDb", endpoint := .sqlitePath migDb, tables := [v1Table] }
  match ← Native.migrateDatabase v1Cfg with
  | .ok steps => c.checkEq "[migrate] v1 initial creates 1 table" steps.length 1
  | .error e => c.check "[migrate] v1 init" false e.message; return

  -- Insert a v1 row
  let insQ := SqlQuery.insert ⟨"widgets", by decide⟩
    [(⟨"id", by decide⟩, .text "w1"), (⟨"name", by decide⟩, .text "Sprocket")] []
  let (insSql, insParams) := insQ.compile .sqlite
  match ← Prim.sqliteExec migDb insSql (encodeTaggedParamsJson insParams) with
  | .ok _ => pure ()
  | .error e => c.check "[migrate] insert v1 row" false e

  -- Migrate to v2: adds nullable `notes`, non-nullable `views` with `>= 0` default, and an index
  let v2Table : TableSchema := {
    name := ⟨"widgets", by decide⟩
    columns := [
      { name := ⟨"id", by decide⟩, colType := .text, isPrimaryKey := true },
      { name := ⟨"name", by decide⟩, colType := .text },
      { name := ⟨"notes", by decide⟩, colType := .text, nullable := true },
      { name := ⟨"views", by decide⟩, colType := .int, nullable := false, checkSql? := some "\"views\" >= 0" }
    ]
    indexes := [[⟨"views", by decide⟩]]
  }
  let v2Cfg : DbConfig := { name := "MigDb", endpoint := .sqlitePath migDb, tables := [v2Table] }
  match ← Native.migrateDatabase v2Cfg with
  | .ok steps => c.checkEq "[migrate] v1 -> v2 applied 3 additive steps (2 cols + 1 idx)" steps.length 3
  | .error e => c.check "[migrate] v1 -> v2" false e.message

  -- Verify existing row preserved with safe defaults
  match ← Prim.sqliteExec migDb "SELECT \"id\", \"name\", \"notes\", \"views\" FROM \"widgets\" WHERE \"id\" = ?" (encodeTaggedParamsJson #[.text "w1"]) with
  | .ok raw =>
      match decodeTaggedResultJson raw with
      | .ok res =>
          c.check "[migrate] existing row preserved with NULL + default 0"
            (res.rows == #[#[.text "w1", .text "Sprocket", .null, .int 0]])
      | .error e => c.check "[migrate] decode v2 row" false e
  | .error e => c.check "[migrate] select v2 row" false e

  -- Re-running v2 migration is strictly idempotent (0 steps)
  match ← Native.migrateDatabase v2Cfg with
  | .ok steps => c.checkEq "[migrate] v2 re-run is idempotent (0 steps)" steps.length 0
  | .error e => c.check "[migrate] v2 idempotent" false e.message

  -- Unsafe v3 migration (non-nullable column with arbitrary CHECK) is rejected before DDL runs!
  let v3Table : TableSchema := {
    v2Table with
    columns := v2Table.columns ++ [
      { name := ⟨"sku", by decide⟩, colType := .text, nullable := false, checkSql? := some "LENGTH(\"sku\") >= 4" }
    ]
  }
  let v3Cfg : DbConfig := { name := "MigDb", endpoint := .sqlitePath migDb, tables := [v3Table] }
  match ← Native.migrateDatabase v3Cfg with
  | .error e => c.check "[migrate] unsafe v3 migration rejected" (e.message.contains "unsafe additive migration") e.message
  | .ok _ => c.check "[migrate] unsafe v3 migration rejected" false "unexpectedly succeeded"

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
              let scramCnt ← pgMock.scramCountRef.get
              let parsed ← pgMock.parsedSqlRef.get
              c.check "[pg-wire] SCRAM-SHA-256 proof verified" (scramCnt > 0)
              c.check s!"[pg-wire] connection pool reused authenticated sockets (scram={scramCnt}, queries={parsed.size})"
                (scramCnt < parsed.size && scramCnt <= 6)
                s!"scram={scramCnt}, parsed={parsed.size}"
              c.check "[pg-wire] SQLi payload NEVER interpolated into Parse SQL"
                (!(parsed.any fun s => s.contains "DROP TABLE"))
              c.check "[pg-wire] Parse used $1 placeholders with Bind params"
                (parsed.any fun s => s.contains "$1")
          finally
            srvPg.stop
        finally
          pgMock.stop

    -- Extended Direct Suite: Transactions, Richer SQL, FK Joins, Concurrent Reader Pool & Live Migrations
    runShopDirectSuite c "sqlite-direct" (withRedirectedSqlite s!"{tmpDir}/shop_direct.db") (testConcurrentReaders := true)
    runMigrationSuite c tmpDir

    match ← startPgWireMock s!"{tmpDir}/shop_pg_mock.db" "shopuser" "shoppass" "shopdb" with
    | .error e => c.check "[pg-shop] start mock" false e
    | .ok shopPgMock =>
        try
          let pgInst ← withRedirectedPostgres shopPgMock.url
          runShopDirectSuite c "pg-direct" pgInst
          let scramCnt ← shopPgMock.scramCountRef.get
          let parsed ← shopPgMock.parsedSqlRef.get
          c.check s!"[pg-direct] connection pool reused sockets across tx & queries (scram={scramCnt}, queries={parsed.size})"
            (scramCnt > 0 && scramCnt <= 3 && parsed.size >= 10)
            s!"scram={scramCnt}, queries={parsed.size}"
        finally
          Db.PgWire.clearPool
          shopPgMock.stop
  finally
    rmRf tmpDir
  c.finish

end Tests.Native.Database
