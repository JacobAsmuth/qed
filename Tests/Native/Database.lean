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
  let seenSqlRef ← IO.mkRef (#[] : Array (String × Nat))
  let res ← startMockHttpServer fun _ _ _ body => do
    let bodyStr := (String.fromUTF8? body).getD ""
    let (status, respStr) ← match Qed.Json.parse bodyStr 128 with
      | .error e => pure (400, s!"\{\"error\":\"bad json: {e}\"}")
      | .ok (.obj fs) =>
          let sql := match fs.lookup "sql" with | some (.str s) => s | _ => ""
          let paramsArr := match fs.lookup "params" with | some (.arr ps) => ps | _ => []
          seenSqlRef.modify (·.push (sql, paramsArr.length))
          match paramsArr.mapM SqlVal.fromTaggedJson with
          | .error e => pure (400, Qed.Json.render (.obj [("error", .str e)]))
          | .ok ps =>
              match ← Prim.sqliteExec sqliteFile sql ps.toArray with
              | .ok res  => pure (200, encodeTaggedResultJson res)
              | .error e => pure (400, Qed.Json.render (.obj [("error", .str e)]))
      | .ok _ => pure (400, "{\"error\":\"expected object\"}")
    pure (status, "application/json", respStr.toUTF8)
  return res.map fun (port, stop) => { url := s!"http://127.0.0.1:{port}/query", seenSqlRef, stop }

/-! ## Pure Native Lean PostgreSQL v3 Wire Protocol Mock Server (with SCRAM-SHA-256 & `Prim.sqliteExec`) -/

private def pgFrame (tag : Char) (payload : ByteArray) : ByteArray :=
  PgWire.encodeMsg (UInt8.ofNat tag.toNat) payload

private def pgAuthMsg (code : Nat) (extra : ByteArray := ByteArray.empty) : ByteArray :=
  pgFrame 'R' (PgWire.pushU32BE ByteArray.empty code ++ extra)

private def pgReadyForQuery : ByteArray := pgFrame 'Z' "I".toUTF8

private def pgCommandComplete (tag : String) : ByteArray :=
  pgFrame 'C' (tag.toUTF8.push 0)

private def pgErrorResponse (msg : String) : ByteArray :=
  pgFrame 'E' ((("M".toUTF8 ++ msg.toUTF8).push 0).push 0)

private def pgRowDescription (sampleRow : Array SqlVal) : ByteArray := Id.run do
  let mut p := PgWire.pushU16BE ByteArray.empty sampleRow.size
  for i in [0 : sampleRow.size] do
    let nameBytes := s!"c{i}".toUTF8.push 0
    let oid : Nat := match sampleRow[i]! with
      | .int _   => 20
      | .bool _  => 16
      | .bytes _ => 17
      | _        => 25
    let colMeta := PgWire.pushU16BE (PgWire.pushU32BE (PgWire.pushU16BE (PgWire.pushU32BE (PgWire.pushU16BE (PgWire.pushU32BE ByteArray.empty 0) 0) oid) 0xFFFF) 0xFFFFFFFF) 0
    p := p ++ nameBytes ++ colMeta
  return pgFrame 'T' p

private def pgDataRow (row : Array SqlVal) : ByteArray := Id.run do
  let pushVal (p b : ByteArray) : ByteArray := PgWire.pushU32BE p b.size ++ b
  let mut p := PgWire.pushU16BE ByteArray.empty row.size
  for cell in row do
    p := match cell with
      | .null     => PgWire.pushU32BE p 0xFFFFFFFF
      | .int i    => pushVal p (toString i).toUTF8
      | .text s   => pushVal p s.toUTF8
      | .bool b   => pushVal p (if b then "t" else "f").toUTF8
      | .bytes bs => pushVal p ("\\x" ++ Qed.Proto.encodeHex bs).toUTF8
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

private def xorBytes (a b : ByteArray) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := min a.size b.size) fun i => a[i.val]! ^^^ b[i.val]!

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
  let send (bs : ByteArray) : IO Unit := discard <| Prim.outboundWriteAll conn bs

  while true do
    if stage == "startup" then
      let some b1 ← readExact conn buf 4 | break
      let len := (PgWire.readU32BE b1 0).getD 0
      let some b2 ← readExact conn b1 len | break
      let body := b2.extract 4 len
      buf := b2.extract len b2.size
      let code := (PgWire.readU32BE body 0).getD 0
      if code == 80877103 then
        send "N".toUTF8
        continue
      -- Parse StartupMessage null-terminated key/value pairs
      let kvRaw := (String.fromUTF8? (body.extract 4 body.size)).getD ""
      let rec scanKv : List String → String × String
        | k :: v :: rest =>
            let (u, d) := scanKv rest
            (if k == "user" then v else u, if k == "database" then v else d)
        | _ => ("", "")
      let (gotUser, gotDb) := scanKv (kvRaw.splitOn "\x00")
      if gotUser == expectedUser && gotDb == expectedDb then
        startupOkRef.set true
      send (pgAuthMsg 10 ((("SCRAM-SHA-256".toUTF8).push 0).push 0))
      stage := "scram_init"
      continue

    let some b1 ← readExact conn buf 5 | break
    let tag := Char.ofNat (b1[0]!).toNat
    let len := (PgWire.readU32BE b1 1).getD 0
    let some b2 ← readExact conn b1 (1 + len) | break
    let payload := b2.extract 5 (1 + len)
    buf := b2.extract (1 + len) b2.size

    if stage == "scram_init" && tag == 'p' then
      let nul := findZeroByte payload 0
      let mech := (String.fromUTF8? (payload.extract 0 nul)).getD ""
      let initLen := (PgWire.readI32BE payload (nul + 1)).getD 0
      let cf := (String.fromUTF8? (payload.extract (nul + 5) (nul + 5 + initLen.toNat))).getD ""
      if mech != "SCRAM-SHA-256" || !cf.startsWith "n,," then
        send (pgErrorResponse "unsupported SASL mechanism"); break
      clientFirstBare := String.ofList (cf.toList.drop 3)
      let clientNonce := match (clientFirstBare.splitOn "r=").drop 1 with
        | r :: _ => (r.splitOn ",").headD ""
        | [] => ""
      let serverNonce := clientNonce ++ "qedservernonce9876"
      let saltB64 := Qed.Server.Net.base64Encode saltBytes
      serverFirst := s!"r={serverNonce},s={saltB64},i={iters}"
      send (pgAuthMsg 11 serverFirst.toUTF8)
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
            send (pgErrorResponse "SCRAM-SHA-256 authentication failed"); break
          let serverSig ← Prim.hmacSha256 serverKey authMsg.toUTF8
          scramCountRef.modify (· + 1)
          send (pgAuthMsg 12 (s!"v={Qed.Server.Net.base64Encode serverSig}").toUTF8 ++ pgAuthMsg 0 ++ pgReadyForQuery)
          stage := "ready"
      | _ =>
          send (pgErrorResponse "malformed SASLResponse"); break
    else if stage == "ready" then
      if tag == 'Q' then
        let sql := ((String.fromUTF8? (payload.extract 0 (payload.size - 1))).getD "").trimAscii.toString
        let upper := sql.toUpper
        if upper == "BEGIN" then
          match ← Prim.sqliteTxBegin sqliteFile with
          | .ok tid  => activeTxId? := some tid; send (pgCommandComplete "BEGIN" ++ readyFrame activeTxId?)
          | .error e => send (pgErrorResponse e ++ readyFrame activeTxId?)
        else if upper == "COMMIT" || upper == "ROLLBACK" then
          let mut resp := pgCommandComplete upper
          if let some tid := activeTxId? then
            activeTxId? := none
            if upper == "COMMIT" then
              if let .error e ← Prim.sqliteTxCommit tid then resp := pgErrorResponse e
            else Prim.sqliteTxRollback tid
          send (resp ++ readyFrame none)
        else
          match ← Prim.sqliteDdl sqliteFile sql with
          | .ok ()   => send (pgCommandComplete "CREATE TABLE" ++ readyFrame activeTxId?)
          | .error e => send (pgErrorResponse e ++ readyFrame activeTxId?)
      else if tag == 'P' then
        let n1 := findZeroByte payload 0
        let n2 := findZeroByte payload (n1 + 1)
        preparedSql := (String.fromUTF8? (payload.extract (n1 + 1) n2)).getD ""
        send (pgFrame '1' ByteArray.empty)
      else if tag == 'B' then
        let o1 := findZeroByte payload 0 + 1
        let o2 := findZeroByte payload o1 + 1
        let fmtCnt := (PgWire.readU16BE payload o2).getD 0
        let mut off := o2 + 2 + fmtCnt * 2
        let paramCnt := (PgWire.readU16BE payload off).getD 0
        off := off + 2
        let mut ps : Array SqlVal := #[]
        for _ in [0 : paramCnt] do
          let pLen := (PgWire.readI32BE payload off).getD 0
          off := off + 4
          if pLen < 0 then
            ps := ps.push .null
          else
            let raw := (String.fromUTF8? (payload.extract off (off + pLen.toNat))).getD ""
            off := off + pLen.toNat
            ps := ps.push (.text raw)
        boundParams := ps
        parsedSqlRef.modify (·.push preparedSql)
        send (pgFrame '2' ByteArray.empty)
      else if tag == 'D' then
        pure ()
      else if tag == 'E' then
        let (sqliteSql, sqliteParams) := translatePgSql preparedSql boundParams
        let execRes ← match activeTxId? with
          | some tid => Prim.sqliteTxExec tid sqliteSql sqliteParams
          | none     => Prim.sqliteExec sqliteFile sqliteSql sqliteParams
        match execRes with
        | .error e => send (pgErrorResponse e)
        | .ok res =>
            let mut frames := ByteArray.empty
            let upperSql := preparedSql.trimAscii.toString.toUpper
            if h : 0 < res.rows.size then
              frames := frames ++ pgRowDescription res.rows[0]
              for row in res.rows do
                frames := frames ++ pgDataRow row
            else if ["SELECT COUNT", "SELECT SUM", "SELECT MIN", "SELECT MAX"].any (upperSql.startsWith ·) then
              frames := frames ++ pgRowDescription #[.int 0]
            let verb := (upperSql.splitOn " ").headD "OK"
            let tagStr :=
              if verb == "INSERT" then s!"INSERT 0 {res.affected}"
              else s!"{verb} {if res.rows.size > 0 then res.rows.size else res.affected}"
            send (frames ++ pgCommandComplete tagStr)
      else if tag == 'S' then
        send (readyFrame activeTxId?)
      else if tag == 'X' then
        if let some tid := activeTxId? then Prim.sqliteTxRollback tid
        break
  if let some tid := activeTxId? then
    Prim.sqliteTxRollback tid

private def startPgWireMock (sqliteFile user pass dbName : String) : IO (Except String PgWireMock) := do
  let parsedSqlRef ← IO.mkRef (#[] : Array String)
  let scramCountRef ← IO.mkRef 0
  let startupOkRef ← IO.mkRef false
  let res ← startMockTcpServer (concurrent := true) fun conn =>
    handlePgConn conn sqliteFile user pass dbName parsedSqlRef scramCountRef startupOkRef
  return res.map fun (port, stop) => {
    url := s!"postgres://{user}:{pass}@127.0.0.1:{port}/{dbName}?sslmode=disable"
    parsedSqlRef, scramCountRef, startupOkRef, stop
  }

/-! ## Shared VaultApp RPC Verification Suite Across All 3 Transports -/

private def runVaultSuite (c : TestChecker) (label : String) (srv : NativeServerProc)
    (aliceTok bobTok : String) (testRestart : Bool := false) : IO Unit := do
  let sqli := "' OR 1=1; DROP TABLE notes; --"
  let callRpc (fn : String) (reqBytes : ByteArray := ByteArray.empty) (tok? : Option String := none) :=
    httpRpc srv.port "VaultApi" fn reqBytes tok?

  -- Auth & `requires` enforcement
  c.checkStatus s!"[{label}] unauthenticated createNote rejected (401)" (← callRpc "createNote" (Qed.Proto.encode ((1 : Nat), "hi")) none) 401
  c.checkStatus s!"[{label}] empty body rejected by requires (400)" (← callRpc "createNote" (Qed.Proto.encode ((1 : Nat), "")) (some aliceTok)) 400

  -- Alice creates normal note + SQLi note (createNote returns `Except (RpcDomainError _) VaultDb.notes`)
  c.checkHttp s!"[{label}] alice createNote(1)" (← callRpc "createNote" (Qed.Proto.encode ((1 : Nat), "hello verified db")) (some aliceTok)) (extra := fun r =>
    c.checkRpcDomainOk (E := DbChecks.VaultApi.createNote.Error) (α := DbChecks.VaultDb.notes) s!"[{label}] alice createNote(1) payload" (.ok (ε := String) r.body) fun got =>
      c.checkEq s!"[{label}] alice createNote(1) payload" got { id := 1, ownerId := "alice", body := "hello verified db", version := 0, status := "draft" })

  c.checkHttp s!"[{label}] alice createNote(2) SQLi stored safely" (← callRpc "createNote" (Qed.Proto.encode ((2 : Nat), sqli)) (some aliceTok)) (extra := fun r =>
    c.checkRpcDomainOk (E := DbChecks.VaultApi.createNote.Error) (α := DbChecks.VaultDb.notes) s!"[{label}] alice createNote(2) verbatim body" (.ok (ε := String) r.body) fun got =>
      c.checkEq s!"[{label}] alice createNote(2) verbatim body" got.body sqli)

  -- Count & list for Alice
  c.checkRpcProto s!"[{label}] alice countMyNotes == 2" (← callRpc "countMyNotes" ByteArray.empty (some aliceTok)) (2 : Nat)
  c.checkRpcProtoBy (α := Array DbChecks.VaultDb.notes) s!"[{label}] alice listMyNotes returns 2 notes"
    (← callRpc "listMyNotes" ByteArray.empty (some aliceTok)) (·.size) 2

  -- Row-Level Security (RLS): Bob cannot read, count, edit, or delete Alice's notes!
  c.checkRpcProtoBy (α := Array DbChecks.VaultDb.notes) s!"[{label}] bob listMyNotes == 0 (RLS)"
    (← callRpc "listMyNotes" ByteArray.empty (some bobTok)) (·.size) 0
  c.checkRpcProto s!"[{label}] bob countMyNotes == 0 (RLS)" (← callRpc "countMyNotes" ByteArray.empty (some bobTok)) (0 : Nat)
  c.checkRpcProto s!"[{label}] bob getNote(1) == none (RLS)" (← callRpc "getNote" (Qed.Proto.encode (1 : Nat)) (some bobTok)) (none : Option DbChecks.VaultDb.notes)
  c.checkRpcProto s!"[{label}] bob editNote(1) == none (RLS)" (← callRpc "editNote" (Qed.Proto.encode ((1 : Nat), "pwned")) (some bobTok)) (none : Option DbChecks.VaultDb.notes)
  c.checkRpcProto s!"[{label}] bob deleteNote(1) == 0 (RLS)" (← callRpc "deleteNote" (Qed.Proto.encode (1 : Nat)) (some bobTok)) (0 : Nat)

  -- Alice edits note 1 (version 0 -> 1) and publishes (draft -> published, version 1 -> 2)
  c.checkRpcProto s!"[{label}] alice editNote(1) updated"
    (← callRpc "editNote" (Qed.Proto.encode ((1 : Nat), "updated text")) (some aliceTok))
    (some ({ id := 1, ownerId := "alice", body := "updated text", version := 1, status := "draft" } : DbChecks.VaultDb.notes))
  c.checkRpcProto s!"[{label}] alice publishNote(1) draft -> published"
    (← callRpc "publishNote" (Qed.Proto.encode (1 : Nat)) (some aliceTok))
    (some ({ id := 1, ownerId := "alice", body := "updated text", version := 2, status := "published" } : DbChecks.VaultDb.notes))
  c.checkRpcProto s!"[{label}] alice publishNote(1) twice returns none"
    (← callRpc "publishNote" (Qed.Proto.encode (1 : Nat)) (some aliceTok)) (none : Option DbChecks.VaultDb.notes)

  -- Persistence across full native server restart
  if testRestart then
    let restarted ← srv.restart
    c.check s!"[{label}] server restarted cleanly" restarted
    c.checkRpcProto s!"[{label}] note 1 persisted across restart"
      (← callRpc "getNote" (Qed.Proto.encode (1 : Nat)) (some aliceTok))
      (some ({ id := 1, ownerId := "alice", body := "updated text", version := 2, status := "published" } : DbChecks.VaultDb.notes))
    c.checkRpcProtoBy (α := Option DbChecks.VaultDb.notes) s!"[{label}] SQLi note 2 persisted verbatim across restart"
      (← callRpc "getNote" (Qed.Proto.encode (2 : Nat)) (some aliceTok)) (·.map (·.body)) (some sqli)

  -- Delete note 2
  c.checkRpcProto s!"[{label}] alice deleteNote(2) == 1" (← callRpc "deleteNote" (Qed.Proto.encode (2 : Nat)) (some aliceTok)) (1 : Nat)
  c.checkRpcProto s!"[{label}] alice countMyNotes == 1 after delete" (← callRpc "countMyNotes" ByteArray.empty (some aliceTok)) (1 : Nat)

  -- Guarded atomic `books` update (`stock >= qty`)
  c.checkStatus s!"[{label}] seedBook status 200" (← callRpc "seedBook" (Qed.Proto.encode ("lean4", ("Theorem Proving in Lean 4", (10 : Nat)))) (some aliceTok)) 200
  c.checkRpcProto s!"[{label}] listBooks returns 1 book" (← callRpc "listBooks" ByteArray.empty none)
    (#[{ id := "lean4", title := "Theorem Proving in Lean 4", stock := 10 }] : Array DbChecks.VaultDb.books)
  c.checkRpcProtoBy (α := Option DbChecks.VaultDb.books) s!"[{label}] orderBook(3) stock 10 -> 7"
    (← callRpc "orderBook" (Qed.Proto.encode ("lean4", (3 : Nat))) (some aliceTok)) (·.map (·.stock)) (some 7)
  c.checkRpcProto s!"[{label}] orderBook(10) when stock=7 returns none"
    (← callRpc "orderBook" (Qed.Proto.encode ("lean4", (10 : Nat))) (some aliceTok)) (none : Option DbChecks.VaultDb.books)

/-! ## Direct Runtime Verification: Transactions, Richer SQL, FK Joins, Reader Pool & Migrations -/

@[implicit_reducible]
private def withRedirectedDb (ep : DbEndpoint) : MonadServer IO :=
  let base : MonadServer IO := Native.mkNativeServerInst none none
  let redir (cfg : DbConfig) : DbConfig := { cfg with endpoint := ep, devFallback? := none }
  { exec := fun
      | .dbExec cfg q         => base.exec (.dbExec (redir cfg) q)
      | .dbExecDdl cfg        => base.exec (.dbExecDdl (redir cfg))
      | .dbTxBegin cfg        => base.exec (.dbTxBegin (redir cfg))
      | .dbTxExec cfg tid q   => base.exec (.dbTxExec (redir cfg) tid q)
      | .dbTxCommit cfg tid   => base.exec (.dbTxCommit (redir cfg) tid)
      | .dbTxRollback cfg tid => base.exec (.dbTxRollback (redir cfg) tid)
      | eff                   => base.exec eff
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
  c.checkProto s!"[{label}] empty sum == 0" (← callShop aliceCtx "totalInventoryValue" ByteArray.empty) (0 : Nat)
  c.checkProto s!"[{label}] empty min == none" (← callShop aliceCtx "cheapestPrice" ByteArray.empty) (none : Option Nat)

  -- 1. Multi-statement verified DB transaction (`db.transaction:` commit + `atomic:` state update)
  let mkTxReq (aid aname iid title : String) (price : Nat) :=
    Qed.Proto.encode (aid, (aname, (iid, (title, price))))
  c.checkRpcDomainOk (E := DbChecks.ShopApi.createAuthorAndItem.Error) (α := DbChecks.ShopDb.items)
    s!"[{label}] db.transaction: committed author + item"
    (← callShop aliceCtx "createAuthorAndItem" (mkTxReq "a1" "Ada Lovelace" "i1" "Lean 4 Proofs" 100)) fun it =>
      c.check s!"[{label}] db.transaction: committed author + item" (it.id == "i1" && it.price == 100)
  c.expectOk s!"[{label}] createAuthorAndItem(i2)"
    (← callShop aliceCtx "createAuthorAndItem" (mkTxReq "a2" "Alan Turing" "i2" "Lean 4 Compilers" 250)) fun _ => pure ()
  c.expectOk s!"[{label}] createAuthorAndItem(i3)"
    (← callShop aliceCtx "createAuthorAndItem" (mkTxReq "a3" "Grace Hopper" "i3" "Rust Systems 100%" 50)) fun _ => pure ()

  let txOpsAfter ← Prim.atomicRead stBox (·.txOps)
  c.checkEq s!"[{label}] atomic txOps incremented 3 times inside transactions" txOpsAfter 3

  -- 2. Multi-statement DB transaction ROLLBACK on `fail(.aborted)` (`db.transaction:`)
  c.checkRpcDomainErr (E := DbChecks.ShopApi.createPairDotSyntax.Error) (α := DbChecks.ShopDb.items)
    s!"[{label}] db.transaction: returned fail(.aborted)"
    (← callShop aliceCtx "createPairDotSyntax" (mkTxReq "a_rolled_back" "Ghost Author" "i_ghost" "Ghost Item" 99999))
    (·.tag == .aborted)

  -- Verify the author inserted BEFORE `fail(.aborted)` was rolled back!
  let checkGhostAuthorQ := SqlQuery.count ⟨"authors", by decide⟩
    (.binOp .eq (.col ⟨"id", by decide⟩) (.param (.text "a_rolled_back")))
  c.expectOk s!"[{label}] verify rolled-back author" (← @MonadServer.dbExec IO srvInst DbChecks.ShopDb.config checkGhostAuthorQ) fun res =>
    let cnt : Int := match res.rows[0]?.bind (·[0]?) with | some (SqlVal.int n) => n | _ => -1
    c.checkEq s!"[{label}] rolled-back author does NOT exist in DB" cnt (0 : Int)

  -- 3. Richer SQL: LIKE (`startsWith` + `contains`) + `orderBy` + `limit` + `offset`
  c.checkProtoBy (α := Array DbChecks.ShopDb.items) s!"[{label}] startsWith+contains+orderBy(-price) returns [i2, i1]"
    (← callShop aliceCtx "searchItems" (Qed.Proto.encode ("Lean", ("4", (0 : Nat))))) (·.map (·.id)) #["i2", "i1"]
  -- Offset pagination skips first row
  c.checkProtoBy (α := Array DbChecks.ShopDb.items) s!"[{label}] offset=1 returns [i1]"
    (← callShop aliceCtx "searchItems" (Qed.Proto.encode ("Lean", ("4", (1 : Nat))))) (·.map (·.id)) #["i1"]
  -- LIKE metacharacter `%` escaping: searching for "100%" only matches "Rust Systems 100%"
  c.checkProtoBy (α := Array DbChecks.ShopDb.items) s!"[{label}] LIKE escapes literal % safely"
    (← callShop aliceCtx "searchItems" (Qed.Proto.encode ("Rust", ("100%", (0 : Nat))))) (·.map (·.id)) #["i3"]

  -- 4. `IN (...)` list membership (non-empty and empty list!)
  c.checkProtoBy (α := Array DbChecks.ShopDb.items) s!"[{label}] IN list returns [i1, i3]"
    (← callShop aliceCtx "filterByIds" (Qed.Proto.encode (#["i3", "i1"] : Array String))) (·.map (·.id)) #["i1", "i3"]
  c.checkProtoBy (α := Array DbChecks.ShopDb.items) s!"[{label}] empty IN list returns 0 rows"
    (← callShop aliceCtx "filterByIds" (Qed.Proto.encode (#[] : Array String))) (·.size) 0

  -- 5. Aggregates (`sum`, `min`, `max`) with ReadPolicy enforcement
  c.checkProto s!"[{label}] alice sum(price) == 400" (← callShop aliceCtx "totalInventoryValue" ByteArray.empty) (400 : Nat)
  c.checkProto s!"[{label}] alice min(price) == some 50" (← callShop aliceCtx "cheapestPrice" ByteArray.empty) (some (50 : Nat))
  c.checkProto s!"[{label}] alice max(price) == some 250" (← callShop aliceCtx "highestPrice" ByteArray.empty) (some (250 : Nat))
  c.checkProto s!"[{label}] bob sum(price) == 0 (RLS)" (← callShop bobCtx "totalInventoryValue" ByteArray.empty) (0 : Nat)

  -- 6. Typed FK `join` (`items` INNER JOIN `authors` on `authorId = id`, ordered by `-price`)
  c.checkProtoBy (α := Array (DbChecks.ShopDb.items × DbChecks.ShopDb.authors))
    s!"[{label}] FK join returns [(i2, Alan Turing), (i1, Ada Lovelace), (i3, Grace Hopper)]"
    (← callShop aliceCtx "itemsWithAuthors" ByteArray.empty)
    (·.map fun (it, au) => (it.id, au.name))
    #[("i2", "Alan Turing"), ("i1", "Ada Lovelace"), ("i3", "Grace Hopper")]
  c.checkProtoBy (α := Array (DbChecks.ShopDb.items × DbChecks.ShopDb.authors))
    s!"[{label}] bob FK join returns 0 (RLS)" (← callShop bobCtx "itemsWithAuthors" ByteArray.empty) (·.size) 0

  -- 7. SQLite concurrent reader pool stress test (8 parallel read tasks under WAL)
  if testConcurrentReaders then
    let allOk ← runParallelAll 8 do
      match ← callShop aliceCtx "totalInventoryValue" ByteArray.empty with
      | .ok bs   => return Qed.Proto.decode (α := Nat) bs == .ok 400
      | .error _ => return false
    c.check s!"[{label}] 8 concurrent SQLite reader-pool queries succeeded" allOk

private def runMigrationSuite (c : TestChecker) (tmpDir : String) : IO Unit := do
  let migDb := s!"{tmpDir}/migrate.db"
  let (v1Table, v2Table, unsafeCol) := DbChecks.mkMigrationFixture ⟨"widgets", by decide⟩
    [{ name := ⟨"name", by decide⟩, colType := .text }] ⟨"sku", by decide⟩
  let mkCfg (t : TableSchema) : DbConfig := { name := "MigDb", endpoint := .sqlitePath migDb, tables := [t] }
  match ← Native.migrateDatabase (mkCfg v1Table) with
  | .ok steps => c.checkEq "[migrate] v1 initial creates 1 table" steps.length 1
  | .error e => c.check "[migrate] v1 init" false e.message; return

  -- Insert a v1 row
  let (insSql, insParams) := (SqlQuery.insert ⟨"widgets", by decide⟩
    [(⟨"id", by decide⟩, .text "w1"), (⟨"name", by decide⟩, .text "Sprocket")] []).compile .sqlite
  c.expectOk "[migrate] insert v1 row" (← Prim.sqliteExec migDb insSql insParams) fun _ => pure ()

  -- Migrate to v2: adds nullable `notes`, non-nullable `views` with `>= 0` default, and an index
  let v2Cfg := mkCfg v2Table
  c.expectOk "[migrate] v1 -> v2" (← Native.migrateDatabase v2Cfg) fun steps =>
    c.checkEq "[migrate] v1 -> v2 applied 3 additive steps (2 cols + 1 idx)" steps.length 3

  -- Verify existing row preserved with safe defaults
  c.expectOk "[migrate] select v2 row"
    (← Prim.sqliteExec migDb "SELECT \"id\", \"name\", \"notes\", \"views\" FROM \"widgets\" WHERE \"id\" = ?" #[.text "w1"]) fun res =>
      c.check "[migrate] existing row preserved with NULL + default 0"
        (res.rows == #[#[.text "w1", .text "Sprocket", .null, .int 0]])

  -- Re-running v2 migration is strictly idempotent (0 steps)
  c.expectOk "[migrate] v2 idempotent" (← Native.migrateDatabase v2Cfg) fun steps =>
    c.checkEq "[migrate] v2 re-run is idempotent (0 steps)" steps.length 0

  -- Unsafe v3 migration (non-nullable column with arbitrary CHECK) is rejected before DDL runs!
  match ← Native.migrateDatabase (mkCfg { v2Table with columns := v2Table.columns ++ [unsafeCol] }) with
  | .error e => c.check "[migrate] unsafe v3 migration rejected" (e.message.contains "unsafe additive migration") e.message
  | .ok _ => c.check "[migrate] unsafe v3 migration rejected" false "unexpectedly succeeded"

def run : IO Bool := do
  let c ← mkChecker "database"
  let some dir ← buildDevApp "Tests.DbChecks"
    | c.check "buildDevApp Tests.DbChecks" false; return ← c.finish

  checkLeakGate c "Tests.DbChecks" #[
    "DbChecks.VaultDb.config", "DbChecks.VaultDb.secrets", "DbChecks.VaultDb.ensureSchema",
    "DbChecks.VaultDb.ddl", "DbChecks.VaultDb.rlsDdl", "DbChecks.VaultApi.dispatchM",
    "DbChecks.VaultApi.createNote_handler"
  ]

  let authSecret := "db-test-hmac-secret-key"
  let aliceTok ← signSessionToken authSecret "alice"
  let bobTok ← signSessionToken authSecret "bob"
  let dbEnv (url : String) : Array (String × Option String) :=
    #[("QED_WORKERS", some "2"), ("QED_AUTH_SECRET", some authSecret), ("QED_TEST_DB_URL", some url)]
  withTempDir "qed-db-native" fun tmpDir => do
    -- Transport 1: Native Embedded SQLite (with full server restart persistence!)
    withNativeServer c "[sqlite] native server healthy" dir (dbEnv s!"sqlite://{tmpDir}/vault.db") (dev := true) fun srvSqlite =>
      runVaultSuite c "sqlite" srvSqlite aliceTok bobTok (testRestart := true)

    -- Transport 2: HTTP SQL (exact same binary, native Lean HTTP SQL mock backed by Prim.sqliteExec!)
    withMockServer c "[http-sql] start mock" (startHttpSqlMock s!"{tmpDir}/http_mock.db") (·.stop) fun httpMock =>
      withNativeServer c "[http-sql] native server healthy" dir (dbEnv httpMock.url) (dev := true) fun srvHttp => do
        runVaultSuite c "http-sql" srvHttp aliceTok bobTok
        let seen ← httpMock.seenSqlRef.get
        c.check "[http-sql] SQLi payload NEVER interpolated into SQL" (!(seen.any fun (s, _) => s.contains "DROP TABLE"))
        c.check "[http-sql] parameterized SQL sent with bound params" (seen.any fun (s, n) => s.contains "?" && n > 0)

    -- Transport 3: Native PostgreSQL v3 Wire Protocol + SCRAM-SHA-256 (exact same binary!)
    withMockServer c "[pg-wire] start mock" (startPgWireMock s!"{tmpDir}/pg_mock.db" "qeduser" "qedpass" "qeddb") (·.stop) fun pgMock =>
      withNativeServer c "[pg-wire] native server healthy" dir (dbEnv pgMock.url) (dev := true) fun srvPg => do
        runVaultSuite c "pg-wire" srvPg aliceTok bobTok
        c.check "[pg-wire] StartupMessage sent expected user & db" (← pgMock.startupOkRef.get)
        let scramCnt ← pgMock.scramCountRef.get
        let parsed ← pgMock.parsedSqlRef.get
        c.check "[pg-wire] SCRAM-SHA-256 proof verified" (scramCnt > 0)
        c.check s!"[pg-wire] connection pool reused authenticated sockets (scram={scramCnt}, queries={parsed.size})"
          (scramCnt < parsed.size && scramCnt <= 6) s!"scram={scramCnt}, parsed={parsed.size}"
        c.check "[pg-wire] SQLi payload NEVER interpolated into Parse SQL" (!(parsed.any fun s => s.contains "DROP TABLE"))
        c.check "[pg-wire] Parse used $1 placeholders with Bind params" (parsed.any fun s => s.contains "$1")

    -- Extended Direct Suite: Transactions, Richer SQL, FK Joins, Concurrent Reader Pool & Live Migrations
    runShopDirectSuite c "sqlite-direct" (withRedirectedDb (.sqlitePath s!"{tmpDir}/shop_direct.db")) (testConcurrentReaders := true)
    runMigrationSuite c tmpDir

    withMockServer c "[pg-shop] start mock" (startPgWireMock s!"{tmpDir}/shop_pg_mock.db" "shopuser" "shoppass" "shopdb")
      (fun m => do Db.PgWire.clearPool; m.stop) fun shopPgMock => do
        runShopDirectSuite c "pg-direct" (withRedirectedDb (.postgresUrl shopPgMock.url))
        let scramCnt ← shopPgMock.scramCountRef.get
        let parsed ← shopPgMock.parsedSqlRef.get
        c.check s!"[pg-direct] connection pool reused sockets across tx & queries (scram={scramCnt}, queries={parsed.size})"
          (scramCnt > 0 && scramCnt <= 3 && parsed.size >= 10) s!"scram={scramCnt}, queries={parsed.size}"
  c.finish

end Tests.Native.Database
