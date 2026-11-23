import Tests.Native.Harness
import Tests.DbChecks
import Qed.Server.Db.Core
import Qed.Server.Db.PgWire
import Qed.Server.Native

open Qed.Server
open Qed.Server.Db

namespace Tests.Native.Database

/-! ## Pure Native Lean HTTP SQL Mock Server (Backed by `Prim.sqliteExec`) -/

structure HttpSqlMock where
  url        : String
  seenSqlRef : IO.Ref (Array (String × Nat))
  stop       : IO Unit

private def startHttpSqlMock (sqliteFile : String) : IO (Except String HttpSqlMock) := do
  let seenSqlRef ← IO.mkRef (#[] : Array (String × Nat))
  let res ← startMockHttpServer fun _ _ _ body => do
    let errJson (e : String) := (400, Qed.Json.render (.obj [("error", .str e)]))
    let (status, respStr) ← match Qed.Json.parse (utf8Str body) 128 with
      | .error e => pure (errJson s!"bad json: {e}")
      | .ok (.obj fs) =>
          let sql := match fs.lookup "sql" with | some (.str s) => s | _ => ""
          let paramsArr := match fs.lookup "params" with | some (.arr ps) => ps | _ => []
          seenSqlRef.modify (·.push (sql, paramsArr.length))
          match paramsArr.mapM SqlVal.fromTaggedJson with
          | .error e => pure (errJson e)
          | .ok ps => match ← Prim.sqliteExec sqliteFile sql ps.toArray with
              | .ok res  => pure (200, encodeTaggedResultJson res)
              | .error e => pure (errJson e)
      | .ok _ => pure (errJson "expected object")
    pure (status, "application/json", respStr.toUTF8)
  return res.map fun (port, stop) => { url := s!"http://127.0.0.1:{port}/query", seenSqlRef, stop }

/-! ## Pure Native Lean PostgreSQL v3 Wire Protocol Mock Server (SCRAM-SHA-256 + `Prim.sqliteExec`) -/

private def pgFrame (tag : Char) (payload : ByteArray) : ByteArray :=
  PgWire.encodeMsg (UInt8.ofNat tag.toNat) payload
private def pgAuthMsg (code : Nat) (extra : ByteArray := ByteArray.empty) : ByteArray :=
  pgFrame 'R' (PgWire.pushU32BE ByteArray.empty code ++ extra)
private def pgCmdDone (tag : String) : ByteArray := pgFrame 'C' (tag.toUTF8.push 0)
private def pgErr (msg : String) : ByteArray := pgFrame 'E' ((("M".toUTF8 ++ msg.toUTF8).push 0).push 0)
private def pgReady (tx? : Option UInt64 := none) : ByteArray := pgFrame 'Z' (if tx?.isSome then "T" else "I").toUTF8

private def pgRowDescription (sampleRow : Array SqlVal) : ByteArray := Id.run do
  let mut p := PgWire.pushU16BE ByteArray.empty sampleRow.size
  for i in [0 : sampleRow.size] do
    let oid : Nat := match sampleRow[i]! with | .int _ => 20 | .bool _ => 16 | .bytes _ => 17 | _ => 25
    let m := PgWire.pushU32BE ByteArray.empty 0 |> (PgWire.pushU16BE · 0) |> (PgWire.pushU32BE · oid) |>
      (PgWire.pushU16BE · 0xFFFF) |> (PgWire.pushU32BE · 0xFFFFFFFF) |> (PgWire.pushU16BE · 0)
    p := p ++ s!"c{i}".toUTF8.push 0 ++ m
  return pgFrame 'T' p

private def pgDataRow (row : Array SqlVal) : ByteArray :=
  let pushVal (p b : ByteArray) := PgWire.pushU32BE p b.size ++ b
  pgFrame 'D' <| row.foldl (init := PgWire.pushU16BE ByteArray.empty row.size) fun p cell =>
    match cell with
    | .null => PgWire.pushU32BE p 0xFFFFFFFF | .int i => pushVal p (toString i).toUTF8
    | .text s => pushVal p s.toUTF8 | .bool b => pushVal p (if b then "t" else "f").toUTF8
    | .bytes bs => pushVal p ("\\x" ++ Qed.Proto.encodeHex bs).toUTF8

/-- Translates PostgreSQL `$1, $2, ...` placeholders and `STRPOS(` into SQLite equivalents. -/
private def translatePgSql (sql : String) (params : Array SqlVal) : String × Array SqlVal := Id.run do
  let cs := (sql.replace "STRPOS(" "INSTR(").toList.toArray
  let mut out : Array Char := #[]
  let mut bound : Array SqlVal := #[]
  let mut i := 0
  let mut inQ := false
  while i < cs.size do
    let ch := cs[i]!
    if ch == '\'' then inQ := !inQ; out := out.push ch; i := i + 1
    else if !inQ && ch == '$' && i + 1 < cs.size && cs[i + 1]!.isDigit then
      let mut j := i + 1; let mut num := ""
      while j < cs.size && cs[j]!.isDigit do num := num.push cs[j]!; j := j + 1
      bound := bound.push (params.getD (num.toNat?.getD 1 - 1) .null); out := out.push '?'; i := j
    else out := out.push ch; i := i + 1
  return (String.ofList out.toList, bound)

private def findZeroByte (ba : ByteArray) (start : Nat) : Nat := Id.run do
  for i in [start : ba.size] do if ba[i]! == 0 then return i
  return ba.size

private def xorBytes (a b : ByteArray) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := min a.size b.size) fun i => a[i.val]! ^^^ b[i.val]!

structure PgWireMock where
  url           : String
  parsedSqlRef  : IO.Ref (Array String)
  scramCountRef : IO.Ref Nat
  startupOkRef  : IO.Ref Bool
  stop          : IO Unit

private partial def handlePgConn (conn : UInt64) (sqliteFile expectedUser expectedPass expectedDb : String)
    (parsedSqlRef : IO.Ref (Array String)) (scramCountRef : IO.Ref Nat) (startupOkRef : IO.Ref Bool) : IO Unit := do
  let mut buf := ByteArray.empty
  let send (bs : ByteArray) : IO Unit := discard <| Prim.outboundWriteAll conn bs
  let nextTagged (b : ByteArray) : IO (Option (Char × ByteArray × ByteArray)) := do
    let some b1 ← readExact conn b 5 | return none
    let len := (PgWire.readU32BE b1 1).getD 0
    let some b2 ← readExact conn b1 (1 + len) | return none
    return some (Char.ofNat (b1[0]!).toNat, b2.extract 5 (1 + len), b2.extract (1 + len) b2.size)

  -- Phase 1: StartupMessage (handles optional SSLRequest code 80877103)
  while true do
    let some b1 ← readExact conn buf 4 | return
    let len := (PgWire.readU32BE b1 0).getD 0
    let some b2 ← readExact conn b1 len | return
    let body := b2.extract 4 len
    buf := b2.extract len b2.size
    if (PgWire.readU32BE body 0).getD 0 == 80877103 then send "N".toUTF8; continue
    let rec scanKv : List String → String × String
      | k :: v :: rest => let (u, d) := scanKv rest; (if k == "user" then v else u, if k == "database" then v else d)
      | _ => ("", "")
    let (gotUser, gotDb) := scanKv ((utf8Str (body.extract 4 body.size)).splitOn "\x00")
    if gotUser == expectedUser && gotDb == expectedDb then startupOkRef.set true
    send (pgAuthMsg 10 ((("SCRAM-SHA-256".toUTF8).push 0).push 0))
    break

  -- Phase 2: SCRAM-SHA-256 handshake
  let (saltBytes, iters) := ("qedsalt012345678".toUTF8, 4096)
  let some ('p', p1, b1) ← nextTagged buf | return
  buf := b1
  let nul := findZeroByte p1 0
  let mech := utf8Str (p1.extract 0 nul)
  let initLen := (PgWire.readI32BE p1 (nul + 1)).getD 0
  let cf1 := utf8Str (p1.extract (nul + 5) (nul + 5 + initLen.toNat))
  if mech != "SCRAM-SHA-256" || !cf1.startsWith "n,," then send (pgErr "unsupported SASL mechanism"); return
  let clientFirstBare := String.ofList (cf1.toList.drop 3)
  let clientNonce := match (clientFirstBare.splitOn "r=").drop 1 with | r :: _ => (r.splitOn ",").headD "" | [] => ""
  let serverFirst := s!"r={clientNonce}qedservernonce9876,s={Net.base64Encode saltBytes},i={iters}"
  send (pgAuthMsg 11 serverFirst.toUTF8)

  let some ('p', p2, b2) ← nextTagged buf | return
  buf := b2
  let [clientFinalNoProof, clientProofB64] := (utf8Str p2).splitOn ",p=" | send (pgErr "malformed SASLResponse"); return
  let salted ← Prim.pbkdf2HmacSha256 expectedPass.toUTF8 saltBytes iters.toUInt32
  let clientKey ← Prim.hmacSha256 salted "Client Key".toUTF8
  let storedKey ← Prim.sha256 clientKey
  let serverKey ← Prim.hmacSha256 salted "Server Key".toUTF8
  let authMsg := s!"{clientFirstBare},{serverFirst},{clientFinalNoProof}"
  let clientSig ← Prim.hmacSha256 storedKey authMsg.toUTF8
  if clientProofB64 != Net.base64Encode (xorBytes clientKey clientSig) then
    send (pgErr "SCRAM-SHA-256 authentication failed"); return
  let serverSig ← Prim.hmacSha256 serverKey authMsg.toUTF8
  scramCountRef.modify (· + 1)
  send (pgAuthMsg 12 (s!"v={Net.base64Encode serverSig}").toUTF8 ++ pgAuthMsg 0 ++ pgReady)

  -- Phase 3: Ready query & extended-protocol loop
  let mut preparedSql := ""
  let mut boundParams : Array SqlVal := #[]
  let mut activeTxId? : Option UInt64 := none
  while true do
    let some (tag, payload, rest) ← nextTagged buf | break
    buf := rest
    match tag with
    | 'Q' =>
        let sql := (utf8Str (payload.extract 0 (payload.size - 1))).trimAscii.toString
        let upper := sql.toUpper
        if upper == "BEGIN" then
          match ← Prim.sqliteTxBegin sqliteFile with
          | .ok tid  => activeTxId? := some tid; send (pgCmdDone "BEGIN" ++ pgReady activeTxId?)
          | .error e => send (pgErr e ++ pgReady activeTxId?)
        else if upper == "COMMIT" || upper == "ROLLBACK" then
          let mut resp := pgCmdDone upper
          if let some tid := activeTxId? then
            activeTxId? := none
            if upper == "COMMIT" then
              if let .error e ← Prim.sqliteTxCommit tid then resp := pgErr e
            else Prim.sqliteTxRollback tid
          send (resp ++ pgReady)
        else
          match ← Prim.sqliteDdl sqliteFile sql with
          | .ok ()   => send (pgCmdDone "CREATE TABLE" ++ pgReady activeTxId?)
          | .error e => send (pgErr e ++ pgReady activeTxId?)
    | 'P' =>
        let n1 := findZeroByte payload 0
        preparedSql := utf8Str (payload.extract (n1 + 1) (findZeroByte payload (n1 + 1)))
        send (pgFrame '1' ByteArray.empty)
    | 'B' =>
        let o2 := findZeroByte payload (findZeroByte payload 0 + 1) + 1
        let mut off := o2 + 2 + ((PgWire.readU16BE payload o2).getD 0) * 2
        let paramCnt := (PgWire.readU16BE payload off).getD 0; off := off + 2
        let mut ps : Array SqlVal := #[]
        for _ in [0 : paramCnt] do
          let pLen := (PgWire.readI32BE payload off).getD 0; off := off + 4
          if pLen < 0 then ps := ps.push .null
          else ps := ps.push (.text (utf8Str (payload.extract off (off + pLen.toNat)))); off := off + pLen.toNat
        boundParams := ps; parsedSqlRef.modify (·.push preparedSql)
        send (pgFrame '2' ByteArray.empty)
    | 'E' =>
        let (sqliteSql, sqliteParams) := translatePgSql preparedSql boundParams
        let execRes ← match activeTxId? with
          | some tid => Prim.sqliteTxExec tid sqliteSql sqliteParams
          | none     => Prim.sqliteExec sqliteFile sqliteSql sqliteParams
        match execRes with
        | .error e => send (pgErr e)
        | .ok res =>
            let upperSql := preparedSql.trimAscii.toString.toUpper
            let mut frames := ByteArray.empty
            if h : 0 < res.rows.size then
              frames := frames ++ pgRowDescription res.rows[0]
              for row in res.rows do frames := frames ++ pgDataRow row
            else if ["SELECT COUNT", "SELECT SUM", "SELECT MIN", "SELECT MAX"].any (upperSql.startsWith ·) then
              frames := frames ++ pgRowDescription #[.int 0]
            let verb := (upperSql.splitOn " ").headD "OK"
            let tagStr := if verb == "INSERT" then s!"INSERT 0 {res.affected}" else s!"{verb} {if res.rows.size > 0 then res.rows.size else res.affected}"
            send (frames ++ pgCmdDone tagStr)
    | 'S' => send (pgReady activeTxId?)
    | 'X' => break
    | _   => pure ()
  if let some tid := activeTxId? then Prim.sqliteTxRollback tid

private def startPgWireMock (sqliteFile user pass dbName : String) : IO (Except String PgWireMock) := do
  let (parsedSqlRef, scramCountRef, startupOkRef) := (← IO.mkRef #[], ← IO.mkRef 0, ← IO.mkRef false)
  let res ← startMockTcpServer (concurrent := true) fun conn =>
    handlePgConn conn sqliteFile user pass dbName parsedSqlRef scramCountRef startupOkRef
  return res.map fun (port, stop) =>
    { url := s!"postgres://{user}:{pass}@127.0.0.1:{port}/{dbName}?sslmode=disable", parsedSqlRef, scramCountRef, startupOkRef, stop }

/-! ## Shared VaultApp RPC Verification Suite Across All 3 Transports -/

private def runVaultSuite (c : TestChecker) (label : String) (srv : NativeServerProc)
    (aliceTok bobTok : String) (testRestart : Bool := false) : IO Unit := do
  let sqli := "' OR 1=1; DROP TABLE notes; --"
  let lbl (s : String) := s!"[{label}] {s}"
  let call (fn : String) (req := ByteArray.empty) (tok? : Option String := none) := httpRpc srv.port "VaultApi" fn req tok?
  let alice (fn : String) (req := ByteArray.empty) := call fn req (some aliceTok)
  let bob   (fn : String) (req := ByteArray.empty) := call fn req (some bobTok)
  let encNote (id : Nat) (body : String) := Qed.Proto.encode (id, body)
  let publishedNote1 : DbChecks.VaultDb.notes := { id := 1, ownerId := "alice", body := "updated text", version := 2, status := "published" }

  -- Auth & `requires` enforcement
  c.checkStatus (lbl "unauthenticated createNote rejected (401)") (← call "createNote" (encNote 1 "hi")) 401
  c.checkStatus (lbl "empty body rejected by requires (400)") (← alice "createNote" (encNote 1 "")) 400

  -- Alice creates normal note + SQLi note
  c.checkHttp (lbl "alice createNote(1)") (← alice "createNote" (encNote 1 "hello verified db")) (extra := fun r =>
    c.checkRpcDomainOk (E := DbChecks.VaultApi.createNote.Error) (α := DbChecks.VaultDb.notes) (lbl "alice createNote(1) payload") (.ok (ε := String) r.body) fun got =>
      c.checkEq (lbl "alice createNote(1) payload") got { id := 1, ownerId := "alice", body := "hello verified db", version := 0, status := "draft" })
  c.checkHttp (lbl "alice createNote(2) SQLi stored safely") (← alice "createNote" (encNote 2 sqli)) (extra := fun r =>
    c.checkRpcDomainOk (E := DbChecks.VaultApi.createNote.Error) (α := DbChecks.VaultDb.notes) (lbl "alice createNote(2) verbatim body") (.ok (ε := String) r.body) fun got =>
      c.checkEq (lbl "alice createNote(2) verbatim body") got.body sqli)

  -- Count & list for Alice
  c.checkRpcProto (lbl "alice countMyNotes == 2") (← alice "countMyNotes") (2 : Nat)
  c.checkRpcProtoBy (α := Array DbChecks.VaultDb.notes) (lbl "alice listMyNotes returns 2 notes") (← alice "listMyNotes") (·.size) 2

  -- Row-Level Security (RLS): Bob cannot read, count, edit, or delete Alice's notes
  c.checkRpcProtoBy (α := Array DbChecks.VaultDb.notes) (lbl "bob listMyNotes == 0 (RLS)") (← bob "listMyNotes") (·.size) 0
  c.checkRpcProto (lbl "bob countMyNotes == 0 (RLS)") (← bob "countMyNotes") (0 : Nat)
  c.checkRpcProto (lbl "bob getNote(1) == none (RLS)") (← bob "getNote" (Qed.Proto.encode (1 : Nat))) (none : Option DbChecks.VaultDb.notes)
  c.checkRpcProto (lbl "bob editNote(1) == none (RLS)") (← bob "editNote" (encNote 1 "pwned")) (none : Option DbChecks.VaultDb.notes)
  c.checkRpcProto (lbl "bob deleteNote(1) == 0 (RLS)") (← bob "deleteNote" (Qed.Proto.encode (1 : Nat))) (0 : Nat)

  -- Alice edits note 1 (version 0 -> 1) and publishes (draft -> published, version 1 -> 2)
  c.checkRpcProto (lbl "alice editNote(1) updated") (← alice "editNote" (encNote 1 "updated text"))
    (some ({ id := 1, ownerId := "alice", body := "updated text", version := 1, status := "draft" } : DbChecks.VaultDb.notes))
  c.checkRpcProto (lbl "alice publishNote(1) draft -> published") (← alice "publishNote" (Qed.Proto.encode (1 : Nat))) (some publishedNote1)
  c.checkRpcProto (lbl "alice publishNote(1) twice returns none") (← alice "publishNote" (Qed.Proto.encode (1 : Nat))) (none : Option DbChecks.VaultDb.notes)

  -- Persistence across full native server restart
  if testRestart then
    c.check (lbl "server restarted cleanly") (← srv.restart)
    c.checkRpcProto (lbl "note 1 persisted across restart") (← alice "getNote" (Qed.Proto.encode (1 : Nat))) (some publishedNote1)
    c.checkRpcProtoBy (α := Option DbChecks.VaultDb.notes) (lbl "SQLi note 2 persisted verbatim across restart")
      (← alice "getNote" (Qed.Proto.encode (2 : Nat))) (·.map (·.body)) (some sqli)

  -- Delete note 2 & guarded atomic `books` update (`stock >= qty`)
  c.checkRpcProto (lbl "alice deleteNote(2) == 1") (← alice "deleteNote" (Qed.Proto.encode (2 : Nat))) (1 : Nat)
  c.checkRpcProto (lbl "alice countMyNotes == 1 after delete") (← alice "countMyNotes") (1 : Nat)
  c.checkStatus (lbl "seedBook status 200") (← alice "seedBook" (Qed.Proto.encode ("lean4", ("Theorem Proving in Lean 4", (10 : Nat))))) 200
  c.checkRpcProto (lbl "listBooks returns 1 book") (← call "listBooks") (#[{ id := "lean4", title := "Theorem Proving in Lean 4", stock := 10 }] : Array DbChecks.VaultDb.books)
  c.checkRpcProtoBy (α := Option DbChecks.VaultDb.books) (lbl "orderBook(3) stock 10 -> 7") (← alice "orderBook" (Qed.Proto.encode ("lean4", (3 : Nat)))) (·.map (·.stock)) (some 7)
  c.checkRpcProto (lbl "orderBook(10) when stock=7 returns none") (← alice "orderBook" (Qed.Proto.encode ("lean4", (10 : Nat)))) (none : Option DbChecks.VaultDb.books)

/-! ## Direct Runtime Verification: Transactions, Richer SQL, FK Joins, Reader Pool & Migrations -/

@[implicit_reducible]
private def withRedirectedDb (ep : DbEndpoint) : MonadServer IO :=
  let base : MonadServer IO := Native.mkNativeServerInst none none
  let r (cfg : DbConfig) : DbConfig := { cfg with endpoint := ep, devFallback? := none }
  { exec := fun
      | .dbExec c q => base.exec (.dbExec (r c) q) | .dbExecDdl c => base.exec (.dbExecDdl (r c))
      | .dbTxBegin c => base.exec (.dbTxBegin (r c)) | .dbTxExec c t q => base.exec (.dbTxExec (r c) t q)
      | .dbTxCommit c t => base.exec (.dbTxCommit (r c) t) | .dbTxRollback c t => base.exec (.dbTxRollback (r c) t)
      | eff => base.exec eff }

private def runShopDirectSuite (c : TestChecker) (label : String) (srvInst : MonadServer IO)
    (testConcurrentReaders : Bool := false) : IO Unit := do
  let lbl (s : String) := s!"[{label}] {s}"
  let stBox ← Prim.mkStateBox DbChecks.ShopApi.initState
  let atomicInst : MonadAtomic DbChecks.ShopApi.State IO := Native.withStateBox stBox
  match ← @MonadServer.dbExecDdl IO srvInst DbChecks.ShopDb.config with
  | .ok () => c.check (lbl "ShopDb schema initialized") true
  | .error e => c.check (lbl "ShopDb schema init") false e.message; return

  let alice (fn : String) (req := ByteArray.empty) := @DbChecks.ShopApi.dispatchM IO _ srvInst atomicInst { userId := some "alice" } fn req
  let bob   (fn : String) (req := ByteArray.empty) := @DbChecks.ShopApi.dispatchM IO _ srvInst atomicInst { userId := some "bob" } fn req
  let mkTxReq (aid aname iid title : String) (price : Nat) := Qed.Proto.encode (aid, (aname, (iid, (title, price))))

  -- Empty aggregates & multi-statement verified DB transactions (`db.transaction:` commit + rollback)
  c.checkProto (lbl "empty sum == 0") (← alice "totalInventoryValue") (0 : Nat)
  c.checkProto (lbl "empty min == none") (← alice "cheapestPrice") (none : Option Nat)
  c.checkRpcDomainOk (E := DbChecks.ShopApi.createAuthorAndItem.Error) (α := DbChecks.ShopDb.items) (lbl "db.transaction: committed author + item")
    (← alice "createAuthorAndItem" (mkTxReq "a1" "Ada Lovelace" "i1" "Lean 4 Proofs" 100)) fun it =>
      c.check (lbl "db.transaction: committed author + item") (it.id == "i1" && it.price == 100)
  for (aid, aname, iid, title, price) in [("a2", "Alan Turing", "i2", "Lean 4 Compilers", 250), ("a3", "Grace Hopper", "i3", "Rust Systems 100%", 50)] do
    c.expectOk (lbl s!"createAuthorAndItem({iid})") (← alice "createAuthorAndItem" (mkTxReq aid aname iid title price)) fun _ => pure ()
  c.checkEq (lbl "atomic txOps incremented 3 times inside transactions") (← Prim.atomicRead stBox (·.txOps)) 3

  c.checkRpcDomainErr (E := DbChecks.ShopApi.createPairDotSyntax.Error) (α := DbChecks.ShopDb.items) (lbl "db.transaction: returned fail(.aborted)")
    (← alice "createPairDotSyntax" (mkTxReq "a_rolled_back" "Ghost Author" "i_ghost" "Ghost Item" 99999)) (·.tag == .aborted)
  let checkGhostQ := SqlQuery.count ⟨"authors", by decide⟩ (.binOp .eq (.col ⟨"id", by decide⟩) (.param (.text "a_rolled_back")))
  c.expectOk (lbl "verify rolled-back author") (← @MonadServer.dbExec IO srvInst DbChecks.ShopDb.config checkGhostQ) fun res =>
    c.checkEq (lbl "rolled-back author does NOT exist in DB") (match res.rows[0]?.bind (·[0]?) with | some (SqlVal.int n) => n | _ => -1) (0 : Int)

  -- Richer SQL: LIKE (`startsWith`+`contains`+`%` escape) + `orderBy` + `offset` + `IN`
  for (tag, pfx, sub, off, want) in [
      ("startsWith+contains+orderBy(-price) returns [i2, i1]", "Lean", "4", 0, #["i2", "i1"]),
      ("offset=1 returns [i1]", "Lean", "4", 1, #["i1"]),
      ("LIKE escapes literal % safely", "Rust", "100%", 0, #["i3"])] do
    c.checkProtoBy (α := Array DbChecks.ShopDb.items) (lbl tag) (← alice "searchItems" (Qed.Proto.encode (pfx, (sub, off)))) (·.map (·.id)) want
  c.checkProtoBy (α := Array DbChecks.ShopDb.items) (lbl "IN list returns [i1, i3]") (← alice "filterByIds" (Qed.Proto.encode (#["i3", "i1"] : Array String))) (·.map (·.id)) #["i1", "i3"]
  c.checkProtoBy (α := Array DbChecks.ShopDb.items) (lbl "empty IN list returns 0 rows") (← alice "filterByIds" (Qed.Proto.encode (#[] : Array String))) (·.size) 0

  -- Aggregates (`sum`, `min`, `max`) & FK `join` with ReadPolicy enforcement
  c.checkProto (lbl "alice sum(price) == 400") (← alice "totalInventoryValue") (400 : Nat)
  c.checkProto (lbl "alice min(price) == some 50") (← alice "cheapestPrice") (some (50 : Nat))
  c.checkProto (lbl "alice max(price) == some 250") (← alice "highestPrice") (some (250 : Nat))
  c.checkProto (lbl "bob sum(price) == 0 (RLS)") (← bob "totalInventoryValue") (0 : Nat)
  c.checkProtoBy (α := Array (DbChecks.ShopDb.items × DbChecks.ShopDb.authors))
    (lbl "FK join returns [(i2, Alan Turing), (i1, Ada Lovelace), (i3, Grace Hopper)]")
    (← alice "itemsWithAuthors") (·.map fun (it, au) => (it.id, au.name)) #[("i2", "Alan Turing"), ("i1", "Ada Lovelace"), ("i3", "Grace Hopper")]
  c.checkProtoBy (α := Array (DbChecks.ShopDb.items × DbChecks.ShopDb.authors)) (lbl "bob FK join returns 0 (RLS)") (← bob "itemsWithAuthors") (·.size) 0

  if testConcurrentReaders then
    let allOk ← runParallelAll 8 do
      return match ← alice "totalInventoryValue" with | .ok bs => Qed.Proto.decode (α := Nat) bs == .ok 400 | .error _ => false
    c.check (lbl "8 concurrent SQLite reader-pool queries succeeded") allOk

private def runMigrationSuite (c : TestChecker) (tmpDir : String) : IO Unit := do
  let migDb := s!"{tmpDir}/migrate.db"
  let (v1Table, v2Table, unsafeCol) := DbChecks.mkMigrationFixture ⟨"widgets", by decide⟩ [{ name := ⟨"name", by decide⟩, colType := .text }] ⟨"sku", by decide⟩
  let mkCfg (t : TableSchema) : DbConfig := { name := "MigDb", endpoint := .sqlitePath migDb, tables := [t] }
  match ← Native.migrateDatabase (mkCfg v1Table) with
  | .ok steps => c.checkEq "[migrate] v1 initial creates 1 table" steps.length 1
  | .error e => c.check "[migrate] v1 init" false e.message; return
  let (insSql, insParams) := (SqlQuery.insert ⟨"widgets", by decide⟩ [(⟨"id", by decide⟩, .text "w1"), (⟨"name", by decide⟩, .text "Sprocket")] []).compile .sqlite
  c.expectOk "[migrate] insert v1 row" (← Prim.sqliteExec migDb insSql insParams) fun _ => pure ()
  let v2Cfg := mkCfg v2Table
  c.expectOk "[migrate] v1 -> v2" (← Native.migrateDatabase v2Cfg) fun steps => c.checkEq "[migrate] v1 -> v2 applied 3 additive steps (2 cols + 1 idx)" steps.length 3
  c.expectOk "[migrate] select v2 row" (← Prim.sqliteExec migDb "SELECT \"id\", \"name\", \"notes\", \"views\" FROM \"widgets\" WHERE \"id\" = ?" #[.text "w1"]) fun res =>
    c.check "[migrate] existing row preserved with NULL + default 0" (res.rows == #[#[.text "w1", .text "Sprocket", .null, .int 0]])
  c.expectOk "[migrate] v2 idempotent" (← Native.migrateDatabase v2Cfg) fun steps => c.checkEq "[migrate] v2 re-run is idempotent (0 steps)" steps.length 0
  match ← Native.migrateDatabase (mkCfg { v2Table with columns := v2Table.columns ++ [unsafeCol] }) with
  | .error e => c.check "[migrate] unsafe v3 migration rejected" (e.message.contains "unsafe additive migration") e.message
  | .ok _ => c.check "[migrate] unsafe v3 migration rejected" false "unexpectedly succeeded"

def run : IO Bool := do
  let c ← mkChecker "database"
  let some dir ← buildDevApp "Tests.DbChecks" | c.check "buildDevApp Tests.DbChecks" false; return ← c.finish
  checkLeakGate c "Tests.DbChecks" #[
    "DbChecks.VaultDb.config", "DbChecks.VaultDb.secrets", "DbChecks.VaultDb.ensureSchema",
    "DbChecks.VaultDb.ddl", "DbChecks.VaultDb.rlsDdl", "DbChecks.VaultApi.dispatchM", "DbChecks.VaultApi.createNote_handler"
  ]
  let authSecret := "db-test-hmac-secret-key"
  let (aliceTok, bobTok) := (← signSessionToken authSecret "alice", ← signSessionToken authSecret "bob")
  let dbEnv (url : String) := #[("QED_WORKERS", some "2"), ("QED_AUTH_SECRET", some authSecret), ("QED_TEST_DB_URL", some url)]
  withTempDir "qed-db-native" fun tmpDir => do
    withNativeServer c "[sqlite] native server healthy" dir (dbEnv s!"sqlite://{tmpDir}/vault.db") (dev := true) fun srv =>
      runVaultSuite c "sqlite" srv aliceTok bobTok (testRestart := true)

    withMockServer c "[http-sql] start mock" (startHttpSqlMock s!"{tmpDir}/http_mock.db") (·.stop) fun httpMock =>
      withNativeServer c "[http-sql] native server healthy" dir (dbEnv httpMock.url) (dev := true) fun srv => do
        runVaultSuite c "http-sql" srv aliceTok bobTok
        let seen ← httpMock.seenSqlRef.get
        c.check "[http-sql] SQLi payload NEVER interpolated into SQL" (!(seen.any fun (s, _) => s.contains "DROP TABLE"))
        c.check "[http-sql] parameterized SQL sent with bound params" (seen.any fun (s, n) => s.contains "?" && n > 0)

    withMockServer c "[pg-wire] start mock" (startPgWireMock s!"{tmpDir}/pg_mock.db" "qeduser" "qedpass" "qeddb") (·.stop) fun pgMock =>
      withNativeServer c "[pg-wire] native server healthy" dir (dbEnv pgMock.url) (dev := true) fun srv => do
        runVaultSuite c "pg-wire" srv aliceTok bobTok
        c.check "[pg-wire] StartupMessage sent expected user & db" (← pgMock.startupOkRef.get)
        let (scramCnt, parsed) := (← pgMock.scramCountRef.get, ← pgMock.parsedSqlRef.get)
        c.check "[pg-wire] SCRAM-SHA-256 proof verified" (scramCnt > 0)
        c.check s!"[pg-wire] connection pool reused authenticated sockets (scram={scramCnt}, queries={parsed.size})"
          (scramCnt < parsed.size && scramCnt <= 6) s!"scram={scramCnt}, parsed={parsed.size}"
        c.check "[pg-wire] SQLi payload NEVER interpolated into Parse SQL" (!(parsed.any (·.contains "DROP TABLE")))
        c.check "[pg-wire] Parse used $1 placeholders with Bind params" (parsed.any (·.contains "$1"))

    runShopDirectSuite c "sqlite-direct" (withRedirectedDb (.sqlitePath s!"{tmpDir}/shop_direct.db")) (testConcurrentReaders := true)
    runMigrationSuite c tmpDir

    withMockServer c "[pg-shop] start mock" (startPgWireMock s!"{tmpDir}/shop_pg_mock.db" "shopuser" "shoppass" "shopdb")
      (fun m => do Db.PgWire.clearPool; m.stop) fun shopPgMock => do
        runShopDirectSuite c "pg-direct" (withRedirectedDb (.postgresUrl shopPgMock.url))
        let (scramCnt, parsed) := (← shopPgMock.scramCountRef.get, ← shopPgMock.parsedSqlRef.get)
        c.check s!"[pg-direct] connection pool reused sockets across tx & queries (scram={scramCnt}, queries={parsed.size})"
          (scramCnt > 0 && scramCnt <= 3 && parsed.size >= 10) s!"scram={scramCnt}, queries={parsed.size}"
  c.finish

end Tests.Native.Database
