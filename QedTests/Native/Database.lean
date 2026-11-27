import QedTests.Native.Harness
import QedTests.DbChecks
import Qed.Server.Native
open Qed.Server Qed.Server.Db

namespace QedTests.Native.Database

structure HttpSqlMock where
  url        : String
  seenSqlRef : IO.Ref (Array (String × Nat))
  stop       : IO Unit

private def startHttpSqlMock (sqliteFile : String) : IO (Except String HttpSqlMock) := do
  let seenSqlRef ← IO.mkRef (#[] : Array (String × Nat))
  let res ← startMockHttpServer fun _ _ _ body => do
    match Qed.Json.parse (utf8Str body) 128 with
    | .error e => return jsonErrResp 400 s!"bad json: {e}"
    | .ok j =>
        if j.obj?.isNone then return jsonErrResp 400 "expected object"
        let (sql, paramsArr) := (j.strAtD "sql", j.arrAt "params")
        seenSqlRef.modify (·.push (sql, paramsArr.length))
        match paramsArr.mapM SqlVal.fromTaggedJson with
        | .error e => return jsonErrResp 400 e
        | .ok ps => match ← Prim.sqliteExec sqliteFile sql ps.toArray with
            | .ok res => return jsonStrResp 200 (encodeTaggedResultJson res) | .error e => return jsonErrResp 400 e
  return res.map fun (port, stop) => { url := s!"http://127.0.0.1:{port}/query", seenSqlRef, stop }

private def pgFrame (tag : Char) (payload : ByteArray) : ByteArray := PgWire.encodeMsg (UInt8.ofNat tag.toNat) payload
private def pgAuthMsg (code : Nat) (extra : ByteArray := ByteArray.empty) : ByteArray := pgFrame 'R' (PgWire.pushU32BE ByteArray.empty code ++ extra)
private def pgCmdDone (tag : String) : ByteArray := pgFrame 'C' (tag.toUTF8.push 0)
private def pgErr (msg : String) : ByteArray := pgFrame 'E' ((("M".toUTF8 ++ msg.toUTF8).push 0).push 0)
private def pgReady (tx? : Option UInt64 := none) : ByteArray := pgFrame 'Z' (if tx?.isSome then "T" else "I").toUTF8
private def pgRowDescription (sampleRow : Array SqlVal) : ByteArray :=
  pgFrame 'T' <| sampleRow.zipIdx.foldl (init := PgWire.pushU16BE ByteArray.empty sampleRow.size) fun p (cell, i) =>
    let oid : Nat := match cell with | .int _ => 20 | .bool _ => 16 | .bytes _ => 17 | _ => 25
    let m := PgWire.pushU32BE ByteArray.empty 0 |> (PgWire.pushU16BE · 0) |> (PgWire.pushU32BE · oid) |> (PgWire.pushU16BE · 0xFFFF) |> (PgWire.pushU32BE · 0xFFFFFFFF) |> (PgWire.pushU16BE · 0)
    p ++ s!"c{i}".toUTF8.push 0 ++ m
private def pgDataRow (row : Array SqlVal) : ByteArray :=
  let pushVal (p b : ByteArray) := PgWire.pushU32BE p b.size ++ b
  pgFrame 'D' <| row.foldl (init := PgWire.pushU16BE ByteArray.empty row.size) fun p cell => match cell with
    | .null => PgWire.pushU32BE p 0xFFFFFFFF | .int i => pushVal p (toString i).toUTF8 | .text s => pushVal p s.toUTF8
    | .bool b => pushVal p (if b then "t" else "f").toUTF8 | .bytes bs => pushVal p ("\\x" ++ Qed.Proto.encodeHex bs).toUTF8
private def translatePgSql (sql : String) (params : Array SqlVal) : String × Array SqlVal := Id.run do
  let cs := (sql.replace "STRPOS(" "INSTR(").toList.toArray
  let mut out : Array Char := #[]; let mut bound : Array SqlVal := #[]; let mut i := 0; let mut inQ := false
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
private def xorBytes (a b : ByteArray) : ByteArray := ByteArray.mk <| Array.ofFn (n := min a.size b.size) fun i => a[i.val]! ^^^ b[i.val]!

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
  let (r32, r16, ri32) := (fun b o => (PgWire.readU32BE b o).getD 0, fun b o => (PgWire.readU16BE b o).getD 0, fun b o => (PgWire.readI32BE b o).getD 0)
  let nextTagged (b : ByteArray) : IO (Option (Char × ByteArray × ByteArray)) := do
    let some b1 ← readExact conn b 5 | return none
    let len := r32 b1 1
    let some b2 ← readExact conn b1 (1 + len) | return none
    return some (Char.ofNat (b1[0]!).toNat, b2.extract 5 (1 + len), b2.extract (1 + len) b2.size)
  while true do
    let some b1 ← readExact conn buf 4 | return
    let len := r32 b1 0
    let some b2 ← readExact conn b1 len | return
    let body := b2.extract 4 len; buf := b2.extract len b2.size
    if r32 body 0 == 80877103 then send "N".toUTF8; continue
    let rec scanKv : List String → String × String
      | k :: v :: rest => let (u, d) := scanKv rest; (if k == "user" then v else u, if k == "database" then v else d) | _ => ("", "")
    if scanKv ((utf8Str (body.extract 4 body.size)).splitOn "\x00") == (expectedUser, expectedDb) then startupOkRef.set true
    send (pgAuthMsg 10 ((("SCRAM-SHA-256".toUTF8).push 0).push 0)); break
  let (saltBytes, iters) := ("qedsalt012345678".toUTF8, 4096)
  let some ('p', p1, b1) ← nextTagged buf | return
  buf := b1; let nul := findZeroByte p1 0; let cf1 := utf8Str (p1.extract (nul + 5) (nul + 5 + (ri32 p1 (nul + 1)).toNat))
  if utf8Str (p1.extract 0 nul) != "SCRAM-SHA-256" || !cf1.startsWith "n,," then send (pgErr "unsupported SASL mechanism"); return
  let clientFirstBare := dropChars cf1 3
  let clientNonce := match (clientFirstBare.splitOn "r=").drop 1 with | r :: _ => (r.splitOn ",").headD "" | [] => ""
  let serverFirst := s!"r={clientNonce}qedservernonce9876,s={Net.base64Encode saltBytes},i={iters}"
  send (pgAuthMsg 11 serverFirst.toUTF8)
  let some ('p', p2, b2) ← nextTagged buf | return
  buf := b2
  let [clientFinalNoProof, clientProofB64] := (utf8Str p2).splitOn ",p=" | send (pgErr "malformed SASLResponse"); return
  let salted ← Prim.pbkdf2HmacSha256 expectedPass.toUTF8 saltBytes iters.toUInt32
  let clientKey ← Prim.hmacSha256 salted "Client Key".toUTF8
  let (storedKey, serverKey) := (← Prim.sha256 clientKey, ← Prim.hmacSha256 salted "Server Key".toUTF8)
  let authMsg := s!"{clientFirstBare},{serverFirst},{clientFinalNoProof}"
  if clientProofB64 != Net.base64Encode (xorBytes clientKey (← Prim.hmacSha256 storedKey authMsg.toUTF8)) then send (pgErr "SCRAM-SHA-256 authentication failed"); return
  let serverSig ← Prim.hmacSha256 serverKey authMsg.toUTF8
  scramCountRef.modify (· + 1); send (pgAuthMsg 12 (s!"v={Net.base64Encode serverSig}").toUTF8 ++ pgAuthMsg 0 ++ pgReady)
  let mut preparedSql := ""; let mut boundParams : Array SqlVal := #[]; let mut activeTxId? : Option UInt64 := none; let mut txAborted := false
  let readyFrame (tid? : Option UInt64) (aborted : Bool) : ByteArray :=
    pgFrame 'Z' (ByteArray.mk #[if tid?.isNone then 0x49 else if aborted then 0x45 else 0x54])
  let pgErrCode (sqlstate msg : String) : ByteArray :=
    pgFrame 'E' (PgWire.pushCString (ByteArray.empty.push 0x53) "ERROR" ++ PgWire.pushCString (ByteArray.empty.push 0x43) sqlstate ++ PgWire.pushCString (ByteArray.empty.push 0x4D) msg |>.push 0)
  while true do
    let some (tag, payload, rest) ← nextTagged buf | break
    buf := rest
    match tag with
    | 'Q' =>
        let sql := (utf8Str (payload.extract 0 (payload.size - 1))).trimAscii.toString; let upper := sql.toUpper
        if upper == "BEGIN" then
          txAborted := false
          match ← Prim.sqliteTxBegin sqliteFile with | .ok tid => activeTxId? := some tid; send (pgCmdDone "BEGIN" ++ readyFrame activeTxId? false) | .error e => send (pgErr e ++ readyFrame activeTxId? false)
        else if upper == "COMMIT" || upper == "ROLLBACK" then
          let wasAborted := txAborted; txAborted := false
          let mut resp := pgCmdDone (if upper == "COMMIT" && wasAborted then "ROLLBACK" else upper)
          if let some tid := activeTxId? then
            activeTxId? := none
            if upper == "COMMIT" && !wasAborted then
              if let .error e ← Prim.sqliteTxCommit tid then resp := pgErr e
            else Prim.sqliteTxRollback tid
          send (resp ++ readyFrame none false)
        else if txAborted then
          send (pgErrCode "25P02" "current transaction is aborted, commands ignored until end of transaction block" ++ readyFrame activeTxId? true)
        else
          match ← Prim.sqliteDdl sqliteFile sql with | .ok () => send (pgCmdDone "CREATE TABLE" ++ readyFrame activeTxId? false) | .error e => if activeTxId?.isSome then txAborted := true; send (pgErr e ++ readyFrame activeTxId? txAborted)
    | 'P' => let n1 := findZeroByte payload 0; preparedSql := utf8Str (payload.extract (n1 + 1) (findZeroByte payload (n1 + 1))); send (pgFrame '1' ByteArray.empty)
    | 'B' =>
        let o2 := findZeroByte payload (findZeroByte payload 0 + 1) + 1
        let mut off := o2 + 2 + r16 payload o2 * 2; let paramCnt := r16 payload off; off := off + 2; let mut ps : Array SqlVal := #[]
        for _ in [0 : paramCnt] do
          let pLen := ri32 payload off; off := off + 4
          if pLen < 0 then ps := ps.push .null else ps := ps.push (.text (utf8Str (payload.extract off (off + pLen.toNat)))); off := off + pLen.toNat
        boundParams := ps; parsedSqlRef.modify (·.push preparedSql); send (pgFrame '2' ByteArray.empty)
    | 'E' =>
        if txAborted then
          send (pgErrCode "25P02" "current transaction is aborted, commands ignored until end of transaction block")
        else
          let (sqliteSql, sqliteParams) := translatePgSql preparedSql boundParams
          let execRes ← match activeTxId? with | some tid => Prim.sqliteTxExec tid sqliteSql sqliteParams | none => Prim.sqliteExec sqliteFile sqliteSql sqliteParams
          match execRes with
          | .error e =>
              if activeTxId?.isSome then txAborted := true
              send (pgErrCode (if e.contains "UNIQUE" then "23505" else "42000") e)
          | .ok res =>
              let upperSql := preparedSql.trimAscii.toString.toUpper; let mut frames := ByteArray.empty
              if h : 0 < res.rows.size then frames := frames ++ pgRowDescription res.rows[0]; for row in res.rows do frames := frames ++ pgDataRow row
              else if ["SELECT COUNT", "SELECT SUM", "SELECT MIN", "SELECT MAX"].any (upperSql.startsWith ·) then frames := frames ++ pgRowDescription #[.int 0]
              let verb := (upperSql.splitOn " ").headD "OK"
              send (frames ++ pgCmdDone (if verb == "INSERT" then s!"INSERT 0 {res.affected}" else s!"{verb} {if res.rows.size > 0 then res.rows.size else res.affected}"))
    | 'S' => send (readyFrame activeTxId? txAborted) | 'X' => break | _ => pure ()
  if let some tid := activeTxId? then Prim.sqliteTxRollback tid

private def startPgWireMock (sqliteFile user pass dbName : String) : IO (Except String PgWireMock) := do
  let (parsedSqlRef, scramCountRef, startupOkRef) := (← IO.mkRef #[], ← IO.mkRef 0, ← IO.mkRef false)
  let res ← startMockTcpServer (concurrent := true) fun conn => handlePgConn conn sqliteFile user pass dbName parsedSqlRef scramCountRef startupOkRef
  return res.map fun (port, stop) => { url := s!"postgres://{user}:{pass}@127.0.0.1:{port}/{dbName}?sslmode=disable", parsedSqlRef, scramCountRef, startupOkRef, stop }

private def runVaultSuite (c : TestChecker) (label : String) (srv : NativeServerProc) (aliceTok bobTok : String) (testRestart : Bool := false) : IO Unit := do
  let (sqli, lbl) := ("' OR 1=1; DROP TABLE notes; --", fun s => s!"[{label}] {s}")
  let call (fn : String) (req := ByteArray.empty) (tok? : Option String := none) := httpRpc srv.port "VaultApi" fn req tok?
  let alice (fn : String) (req := ByteArray.empty) := call fn req (some aliceTok)
  let bob   (fn : String) (req := ByteArray.empty) := call fn req (some bobTok)
  let encNote (id : Nat) (body : String) := Qed.Proto.encode (id, body)
  let (id1, id2) := (Qed.Proto.encode (1 : Nat), Qed.Proto.encode (2 : Nat))
  let publishedNote1 : DbChecks.VaultDb.notes := { id := 1, ownerId := "alice", body := "updated text", version := 2, status := "published" }
  for (tag, act, want) in [("unauthenticated createNote rejected (401)", call "createNote" (encNote 1 "hi"), 401), ("empty body rejected by requires (400)", alice "createNote" (encNote 1 ""), 400)] do c.checkStatus (lbl tag) (← act) want
  let checkCreate (tag : String) (id : Nat) (body : String) (k : DbChecks.VaultDb.notes → IO Unit) : IO Unit := do
    c.checkHttp (lbl tag) (← alice "createNote" (encNote id body)) (extra := fun r =>
      c.checkRpcDomainOk (E := DbChecks.VaultApi.createNote.Error) (α := DbChecks.VaultDb.notes) (lbl s!"{tag} payload") (.ok (ε := String) r.body) k)
  checkCreate "alice createNote(1)" 1 "hello verified db" (c.checkEq (lbl "alice createNote(1) payload") · { id := 1, ownerId := "alice", body := "hello verified db", version := 0, status := "draft" })
  checkCreate "alice createNote(2) SQLi stored safely" 2 sqli fun got => c.checkEq (lbl "alice createNote(2) verbatim body") got.body sqli
  for (tag, act, want) in [("alice countMyNotes == 2", alice "countMyNotes", 2), ("bob countMyNotes == 0 (RLS)", bob "countMyNotes", 0), ("bob deleteNote(1) == 0 (RLS)", bob "deleteNote" id1, 0)] do c.checkRpcProto (lbl tag) (← act) (want : Nat)
  for (tag, act, want) in [("alice listMyNotes returns 2 notes", alice "listMyNotes", 2), ("bob listMyNotes == 0 (RLS)", bob "listMyNotes", 0)] do c.checkRpcProtoBy (α := Array DbChecks.VaultDb.notes) (lbl tag) (← act) (·.size) want
  for (tag, act, want) in [("bob getNote(1) == none (RLS)", bob "getNote" id1, (none : Option DbChecks.VaultDb.notes)), ("bob editNote(1) == none (RLS)", bob "editNote" (encNote 1 "pwned"), none),
      ("alice editNote(1) updated", alice "editNote" (encNote 1 "updated text"), some { id := 1, ownerId := "alice", body := "updated text", version := 1, status := "draft" }),
      ("alice publishNote(1) draft -> published", alice "publishNote" id1, some publishedNote1), ("alice publishNote(1) twice returns none", alice "publishNote" id1, none)] do
    c.checkRpcProto (lbl tag) (← act) want
  if testRestart then
    c.check (lbl "server restarted cleanly") (← srv.restart)
    c.checkRpcProto (lbl "note 1 persisted across restart") (← alice "getNote" id1) (some publishedNote1)
    c.checkRpcProtoBy (α := Option DbChecks.VaultDb.notes) (lbl "SQLi note 2 persisted verbatim across restart") (← alice "getNote" id2) (·.map (·.body)) (some sqli)
  for (tag, act, want) in [("alice deleteNote(2) == 1", alice "deleteNote" id2, 1), ("alice countMyNotes == 1 after delete", alice "countMyNotes", 1)] do c.checkRpcProto (lbl tag) (← act) (want : Nat)
  c.checkStatus (lbl "seedBook status 200") (← alice "seedBook" (Qed.Proto.encode ("lean4", ("Theorem Proving in Lean 4", (10 : Nat))))) 200
  c.checkRpcProto (lbl "listBooks returns 1 book") (← call "listBooks") (#[{ id := "lean4", title := "Theorem Proving in Lean 4", stock := 10 }] : Array DbChecks.VaultDb.books)
  c.checkRpcProtoBy (α := Option DbChecks.VaultDb.books) (lbl "orderBook(3) stock 10 -> 7") (← alice "orderBook" (Qed.Proto.encode ("lean4", (3 : Nat)))) (·.map (·.stock)) (some 7)
  c.checkRpcProto (lbl "orderBook(10) when stock=7 returns none") (← alice "orderBook" (Qed.Proto.encode ("lean4", (10 : Nat)))) (none : Option DbChecks.VaultDb.books)

@[implicit_reducible]
private def withRedirectedDb (ep : DbEndpoint) : MonadServer IO :=
  let (base, r) := (Native.mkNativeServerInst none none, fun cfg : DbConfig => { cfg with endpoint := ep, devFallback? := none })
  { exec := fun
      | .dbExec c q => base.exec (.dbExec (r c) q) | .dbExecDdl c => base.exec (.dbExecDdl (r c)) | .dbTxBegin c => base.exec (.dbTxBegin (r c))
      | .dbTxExec c t q => base.exec (.dbTxExec (r c) t q) | .dbTxCommit c t => base.exec (.dbTxCommit (r c) t) | .dbTxRollback c t => base.exec (.dbTxRollback (r c) t) | eff => base.exec eff }

@[implicit_reducible]
private def withRedirectedDbAndEnv (ep : DbEndpoint) (envRef : IO.Ref (List (String × String))) (decCountRef : IO.Ref Nat) : MonadServer IO :=
  let base := withRedirectedDb ep
  let lookupKey (kEnv : String) (fb : Option String) : IO (Except ApiError String) := do
    match (← envRef.get).lookup kEnv with
    | some v => if v.isEmpty then return .error (ApiError.internal s!"empty key {kEnv}") else return .ok v
    | none => match fb with
      | some d => if d.isEmpty then return .error (ApiError.internal s!"empty key {kEnv}") else return .ok d
      | none => return .error (ApiError.internal s!"missing required encryption key env var `{kEnv}`")
  { exec := fun
      | .readEnv v => return (← envRef.get).lookup v
      | .aeadEncrypt kEnv fb aad pt => do
          match ← lookupKey kEnv fb with
          | .error e => return .error e
          | .ok k => return (← Prim.aeadEncrypt k.toUTF8 aad pt).mapError ApiError.internal
      | .aeadDecrypt kEnv fb aad ct => do
          decCountRef.modify (· + 1)
          match ← lookupKey kEnv fb with
          | .error e => return .error e
          | .ok k => return (← Prim.aeadDecrypt k.toUTF8 aad ct).mapError ApiError.internal
      | eff => base.exec eff }

private def runShopDirectSuite (c : TestChecker) (label : String) (srvInst : MonadServer IO) (testConcurrentReaders : Bool := false) : IO Unit := do
  let lbl (s : String) := s!"[{label}] {s}"; let stBox ← Prim.mkStateBox DbChecks.ShopApi.initState; let atomicInst : MonadAtomic DbChecks.ShopApi.State IO := Native.withStateBox stBox
  c.expectOk (lbl "ShopDb schema init") (← @MonadServer.dbExecDdl IO srvInst DbChecks.ShopDb.config) fun () => do
    c.check (lbl "ShopDb schema initialized") true
    let alice (fn : String) (req := ByteArray.empty) := @DbChecks.ShopApi.dispatchM IO _ srvInst atomicInst { userId := some "alice" } fn req
    let bob   (fn : String) (req := ByteArray.empty) := @DbChecks.ShopApi.dispatchM IO _ srvInst atomicInst { userId := some "bob" } fn req
    let mkTxReq (aid aname iid title : String) (price : Nat) := Qed.Proto.encode (aid, (aname, (iid, (title, price))))
    c.checkProto (lbl "empty sum == 0") (← alice "totalInventoryValue") (0 : Nat)
    c.checkProto (lbl "empty min == none") (← alice "cheapestPrice") (none : Option Nat)
    c.checkRpcDomainOk (E := DbChecks.ShopApi.createAuthorAndItem.Error) (α := DbChecks.ShopDb.items) (lbl "db.transaction: committed author + item")
      (← alice "createAuthorAndItem" (mkTxReq "a1" "Ada Lovelace" "i1" "Lean 4 Proofs" 100)) fun it => c.check (lbl "db.transaction: committed author + item") (it.id == "i1" && it.price == 100)
    for (aid, aname, iid, title, price) in [("a2", "Alan Turing", "i2", "Lean 4 Compilers", 250), ("a3", "Grace Hopper", "i3", "Rust Systems 100%", 50)] do
      c.expectOk (lbl s!"createAuthorAndItem({iid})") (← alice "createAuthorAndItem" (mkTxReq aid aname iid title price)) fun _ => pure ()
    c.checkEq (lbl "atomic txOps incremented 3 times inside transactions") (← Prim.atomicRead stBox (·.txOps)) 3
    c.checkRpcDomainErr (E := DbChecks.ShopApi.createPairDotSyntax.Error) (α := DbChecks.ShopDb.items) (lbl "db.transaction: returned fail(.aborted)")
      (← alice "createPairDotSyntax" (mkTxReq "a_rolled_back" "Ghost Author" "i_ghost" "Ghost Item" 99999)) (·.tag == .aborted)
    c.checkOkBy (lbl "rolled-back author does NOT exist in DB") (← @MonadServer.dbExec IO srvInst DbChecks.ShopDb.config (SqlQuery.count (sql!"authors") (.binOp .eq (.col (sql!"id")) (.param (.text "a_rolled_back")))))
      (fun res => match res.rows[0]?.bind (·[0]?) with | some (SqlVal.int n) => n | _ => -1) (0 : Int)
    for (tag, pfx, sub, off, want) in [("startsWith+contains+orderBy(-price) returns [i2, i1]", "Lean", "4", 0, #["i2", "i1"]), ("offset=1 returns [i1]", "Lean", "4", 1, #["i1"]), ("LIKE escapes literal % safely", "Rust", "100%", 0, #["i3"])] do
      c.checkProtoBy (α := Array DbChecks.ShopDb.items) (lbl tag) (← alice "searchItems" (Qed.Proto.encode (pfx, (sub, off)))) (·.map (·.id)) want
    c.checkProtoBy (α := Array DbChecks.ShopDb.items) (lbl "IN list returns [i1, i3]") (← alice "filterByIds" (Qed.Proto.encode (#["i3", "i1"] : Array String))) (·.map (·.id)) #["i1", "i3"]
    c.checkProtoBy (α := Array DbChecks.ShopDb.items) (lbl "empty IN list returns 0 rows") (← alice "filterByIds" (Qed.Proto.encode (#[] : Array String))) (·.size) 0
    for (tag, act, want) in [("alice sum(price) == 400", alice "totalInventoryValue", 400), ("bob sum(price) == 0 (RLS)", bob "totalInventoryValue", 0)] do c.checkProto (lbl tag) (← act) (want : Nat)
    for (tag, fn, want) in [("alice min(price) == some 50", "cheapestPrice", some (50 : Nat)), ("alice max(price) == some 250", "highestPrice", some 250)] do c.checkProto (lbl tag) (← alice fn) want
    c.checkProtoBy (α := Array (DbChecks.ShopDb.items × DbChecks.ShopDb.authors)) (lbl "FK join returns [(i2, Alan Turing), (i1, Ada Lovelace), (i3, Grace Hopper)]")
      (← alice "itemsWithAuthors") (·.map fun (it, au) => (it.id, au.name)) #[("i2", "Alan Turing"), ("i1", "Ada Lovelace"), ("i3", "Grace Hopper")]
    c.checkProtoBy (α := Array (DbChecks.ShopDb.items × DbChecks.ShopDb.authors)) (lbl "bob FK join returns 0 (RLS)") (← bob "itemsWithAuthors") (·.size) 0
    if testConcurrentReaders then
      c.check (lbl "8 concurrent SQLite reader-pool queries succeeded") (← runParallelAll 8 do return match ← alice "totalInventoryValue" with | .ok bs => Qed.Proto.decode (α := Nat) bs == .ok 400 | .error _ => false)

private def runMigrationSuite (c : TestChecker) (tmpDir : String) : IO Unit := do
  let migDb := s!"{tmpDir}/migrate.db"
  let (v1Table, v2Table, unsafeCol) := DbChecks.mkMigrationFixture (sql!"widgets") [{ name := sql!"name", colType := .text }] (sql!"sku")
  let mkCfg (t : TableSchema) : DbConfig := { name := "MigDb", endpoint := .sqlitePath migDb, tables := [t] }
  c.expectOk "[migrate] v1 init" (← Native.migrateDatabase (mkCfg v1Table)) fun steps => do
    c.checkEq "[migrate] v1 initial creates 1 table" steps.length 1
    let (insSql, insParams) := (SqlQuery.insert (sql!"widgets") [(sql!"id", .text "w1"), (sql!"name", .text "Sprocket")] []).compile .sqlite
    c.expectOk "[migrate] insert v1 row" (← Prim.sqliteExec migDb insSql insParams) fun _ => pure ()
    let v2Cfg := mkCfg v2Table
    c.checkOkBy "[migrate] v1 -> v2 applied 3 additive steps (2 cols + 1 idx)" (← Native.migrateDatabase v2Cfg) List.length 3
    c.checkOkBy "[migrate] existing row preserved with NULL + default 0" (← Prim.sqliteExec migDb "SELECT \"id\", \"name\", \"notes\", \"views\" FROM \"widgets\" WHERE \"id\" = ?" #[.text "w1"]) (·.rows == #[#[.text "w1", .text "Sprocket", .null, .int 0]]) true
    c.checkOkBy "[migrate] v2 re-run is idempotent (0 steps)" (← Native.migrateDatabase v2Cfg) List.length 0
    c.checkErrContains "[migrate] unsafe v3 migration rejected" (← Native.migrateDatabase (mkCfg { v2Table with columns := v2Table.columns ++ [unsafeCol] })) "unsafe additive migration"

private def runEncryptedColumnSuite (c : TestChecker) (srvInst : MonadServer IO) : IO Unit := do
  let cfg := DbChecks.EncVaultDb.config
  c.expectOk "[enc-db] schema init" (← @MonadServer.dbExecDdl IO srvInst cfg) fun () => do
    let alice (fn : String) (req := ByteArray.empty) := @DbChecks.EncVaultApi.dispatchM IO _ srvInst { userId := some "alice" } fn req
    let some inp1 := DbChecks.SecretNoteInput.parse { body := "top-secret payload 🔐" } | c.check "[enc-db] parse inp1" false; return
    let some inp2 := DbChecks.SecretNoteInput.parse { body := "updated secret 🔑" } | c.check "[enc-db] parse inp2" false; return
    let blob := ByteArray.mk #[1, 2, 3, 255]
    c.checkRpcDomainOk (E := DbChecks.EncVaultApi.save.Error) (α := DbChecks.EncVaultDb.entries) "[enc-db] insert row 1"
      (← alice "save" (Qed.Proto.encode ((1 : Nat), (inp1, (some blob : Option ByteArray))))) fun r1 =>
      c.check "[enc-db] insert returns plaintext" (r1.body == "top-secret payload 🔐" && r1.raw == some blob)
    c.expectOk "[enc-db] insert row 2 (same plaintext)" (← alice "save" (Qed.Proto.encode ((2 : Nat), (inp1, (none : Option ByteArray))))) fun _ => pure ()
    let rawQ := SqlQuery.select (sql!"entries") [sql!"id", sql!"body"] .litTrue (some (sql!"id", .asc)) none none
    c.expectOk "[enc-db] raw SQLite read" (← @MonadServer.dbExec IO srvInst cfg rawQ) fun res => do
      c.check "[enc-db] 2 raw rows stored" (res.rows.size == 2)
      match res.rows[0]?.bind (·[1]?), res.rows[1]?.bind (·[1]?) with
      | some (SqlVal.text ct1), some (SqlVal.text ct2) =>
          c.check "[enc-db] ciphertext hides plaintext" (!ct1.contains "top-secret" && !ct2.contains "top-secret")
          c.check "[enc-db] ciphertext satisfies derived CHECK bounds" (40 <= ct1.length && ct1.length <= 304 && 40 <= ct2.length && ct2.length <= 304)
          c.check "[enc-db] randomized AES-GCM nonces differ" (ct1 != ct2)
      | _, _ => c.check "[enc-db] raw body cells are TEXT" false
    c.checkProtoBy (α := Option DbChecks.EncVaultDb.entries) "[enc-db] findOne decrypts row 1"
      (← alice "get" (Qed.Proto.encode (1 : Nat))) (fun opt => opt.map fun r => (r.body, r.raw)) (some ("top-secret payload 🔐", some blob))
    c.checkProtoBy (α := Array DbChecks.EncVaultDb.entries) "[enc-db] select decrypts all rows"
      (← alice "list") (fun rs => rs.map fun r => (r.id, r.body, r.raw)) #[(1, "top-secret payload 🔐", some blob), (2, "top-secret payload 🔐", none)]
    c.checkProtoBy (α := Option DbChecks.EncVaultDb.entries) "[enc-db] updateOne re-encrypts"
      (← alice "edit" (Qed.Proto.encode ((1 : Nat), inp2))) (fun opt => opt.map (·.body)) (some "updated secret 🔑")
    let tamperQ := SqlQuery.update (sql!"entries") [(sql!"body", .param (.text (String.ofList (List.replicate 44 'A'))))] (.binOp .eq (.col (sql!"id")) (.param (.int 2))) []
    c.expectOk "[enc-db] raw tamper update" (← @MonadServer.dbExec IO srvInst cfg tamperQ) fun _ => do
      c.check "[enc-db] tampered ciphertext rejected on read" (!(← alice "get" (Qed.Proto.encode (2 : Nat))).isOk)
    let badLenQ := SqlQuery.insert (sql!"entries") [(sql!"id", .int 99), (sql!"ownerId", .text "alice"), (sql!"body", .text (String.ofList (List.replicate 308 'A'))), (sql!"note", .text (String.ofList (List.replicate 44 'A'))), (sql!"raw", .null)] []
    c.check "[enc-db] SQLite CHECK rejects oversized ciphertext" (!(← @MonadServer.dbExec IO srvInst cfg badLenQ).isOk)

private def runRoadmapSuite (c : TestChecker) (tmpDir : String) : IO Unit := do
  let dbPath := s!"{tmpDir}/roadmap_worker.db"
  let cfg := { DbChecks.RoadmapDb.config with endpoint := .sqlitePath dbPath, devFallback? := none, envEndpoints? := none }
  let db := DbChecks.RoadmapDb.clientWith cfg
  c.expectOk "[roadmap] migrateDatabase creates tables" (← Native.migrateDatabase cfg) fun _ => do
    c.checkOkBy "[roadmap] org inserted" (← db.orgs.insert { id := "org1", name := "Acme" }) (·.name) "Acme"
    c.checkOkBy "[roadmap] enum roundtrip (.queued)" (← db.projects.insert { id := "p1", orgId := "org1", ownerId := "alice", stage := .queued, note := none }) (·.stage) DbChecks.DeployStage.queued
    -- Re-run migrateDatabase to verify declarative `backfill` populates NULL notes.
    c.expectOk "[roadmap] migrateDatabase runs backfill" (← Native.migrateDatabase cfg) fun _ => do
      c.checkOkBy "[roadmap] backfill updated null note to migrated" (← db.projects.findOne (.eq "id" "p1")) (·.bind (·.note)) (some "migrated")
    -- Standalone client upsert (insert new + update existing + policy-guarded conflict)
    c.checkOkBy "[roadmap] upsert updated stage & note" (← db.projects.upsert { id := "p1", orgId := "org1", ownerId := "alice", stage := .building, note := some "v2" } ["id"] ["stage", "note"] (conflictWhere? := some (.eq "ownerId" "alice")))
      (·.map fun p => (p.stage, p.note)) (some (DbChecks.DeployStage.building, some "v2"))
    c.checkOkBy "[roadmap] conflict where filtered out update" (← db.projects.upsert { id := "p1", orgId := "org1", ownerId := "alice", stage := .live, note := some "hijack" } ["id"] ["stage", "note"] (conflictWhere? := some (.eq "ownerId" "bob"))) Option.isNone true
    c.checkOkBy "[roadmap] updateReturning returned live row" (← db.projects.updateReturning [sqlSet "stage" DbChecks.DeployStage.live] (.eq "id" "p1"))
      (fun rows => (rows.size, rows[0]?.map (·.stage))) (1, some DbChecks.DeployStage.live)
    c.checkOkBy "[roadmap] live count == 1" (← db.projects.count (.eq "stage" DbChecks.DeployStage.live)) id 1
    -- Transaction rollback leaves DB untouched
    let txRes ← db.transaction fun tx => do
      let _ ← db.orgs.insert { id := "org_rb", name := "Rolled Back" } (txId? := some tx)
      return (.error (ApiError.badRequest "abort tx") : Except ApiError Unit)
    c.check "[roadmap] transaction returned error" (!txRes.isOk)
    c.checkOkBy "[roadmap] rollback verified" (← db.orgs.findOne (.eq "id" "org_rb")) Option.isNone true
    c.check "[roadmap] unknown column rejected" (!(← db.projects.select (.eq "nonexistent_col" "x")).isOk)
    -- `insertOrIgnore` + atomic `sqlAdd` / `sqlSub` + `updateOneReturning`
    for (lbl, name, want) in [("[roadmap] insertOrIgnore returned some", "First", some "First"), ("[roadmap] duplicate ignored", "Second", none)] do
      c.checkOkBy lbl (← db.orgs.insertOrIgnore { id := "org_ign", name }) (·.map (·.name)) want
    c.expectOk "[roadmap] insert service for atomic +=" (← db.services.insert { slug := DbChecks.ServiceSlug.make "web", port := DbChecks.ServicePort.make 8080, altPort := none }) fun _ => do
      for (lbl, op, want) in [("[roadmap] port incremented atomically", sqlAdd "port" (5 : Nat), some 8085), ("[roadmap] port decremented atomically", sqlSub "port" (3 : Nat), some 8082)] do
        c.checkOkBy lbl (← db.services.updateOneReturning [op] (.eq "slug" "web")) (·.map (·.port.val)) want
    c.checkOkBy "[roadmap] deleted 1 row" (← db.projects.delete (.eq "id" "p1")) id 1

private def runKeyRotationAndMetaSuite (c : TestChecker) (tmpDir : String) : IO Unit := do
  let dbPath := s!"{tmpDir}/rotating_vault.db"
  let envRef ← IO.mkRef [("VAULT_PRIMARY_KEY", "key-v1-initial-material-32bytes!")]
  let decCountRef ← IO.mkRef 0
  let srvInst := withRedirectedDbAndEnv (.sqlitePath dbPath) envRef decCountRef
  let cfg := DbChecks.RotatingVaultDb.config
  c.expectOk "[enc-rot] schema init" (← @MonadServer.dbExecDdl IO srvInst cfg) fun () => do
    let alice (fn : String) (req := ByteArray.empty) := @DbChecks.RotatingVaultApi.dispatchM IO _ srvInst { userId := some "alice" } fn req
    -- Write 2 rows encrypted with K1
    for (id, label, sec) in [((1 : Nat), "stripe-live", "sk_live_alpha"), (2, "github-pat", "ghp_beta")] do
      c.expectOk s!"[enc-rot] save row {id} under K1" (← alice "save" (Qed.Proto.encode (id, (label, sec)))) fun _ => pure ()
    -- Unset ALL encryption keys: metadata projections MUST succeed with ZERO aeadDecrypt calls!
    envRef.set []
    decCountRef.set 0
    c.checkProtoBy (α := Array DbChecks.RotatingVaultDb.entries.Meta) "[enc-meta] selectMeta succeeds without encryption key"
      (← alice "listMeta") (·.map fun m => (m.id, m.label)) #[(1, "stripe-live"), (2, "github-pat")]
    c.checkProtoBy (α := Option DbChecks.RotatingVaultDb.entries.Meta) "[enc-meta] findOneMeta succeeds without encryption key"
      (← alice "getMeta" (Qed.Proto.encode (2 : Nat))) (·.map (·.label)) (some "github-pat")
    c.checkProto (α := Array (Nat × String)) "[enc-meta] select(columns = [id, label]) succeeds without key"
      (← alice "listLabels") #[(1, "stripe-live"), (2, "github-pat")]
    c.checkProto (α := Option String) "[enc-meta] findOne(columns = [label]) succeeds without key"
      (← alice "getLabel" (Qed.Proto.encode (1 : Nat))) (some "stripe-live")
    let clientCfg := { cfg with endpoint := .sqlitePath dbPath, devFallback? := none, envEndpoints? := none }
    let dbClient := DbChecks.RotatingVaultDb.clientWith clientCfg
    let projRes ← (letI : MonadServer IO := srvInst
      dbClient.entries.selectProjected DbChecks.RotatingVaultDb.entries.metaColNames DbChecks.RotatingVaultDb.entries.decodeMetaRow (.eq "ownerId" "alice") (orderBy? := some ("id", true)))
    c.checkOkBy "[enc-meta] TableHandle.selectProjected rows match" projRes (·.map (·.label)) #["stripe-live", "github-pat"]
    c.checkEq "[enc-meta] ZERO aeadDecrypt calls across all metadata projections" (← decCountRef.get) 0
    -- Primary key missing while prevKey IS set MUST STILL FAIL CLOSED!
    envRef.set [("VAULT_PREV_KEY", "key-v1-initial-material-32bytes!")]
    c.check "[enc-rot] missing primary key fails closed even when prevKey is set" (!(← alice "get" (Qed.Proto.encode (1 : Nat))).isOk)
    -- Rotate: primary = K2, prevKey = K1 -> K1 rows decrypt cleanly!
    envRef.set [("VAULT_PRIMARY_KEY", "key-v2-rotated-material-32bytes!"), ("VAULT_PREV_KEY", "key-v1-initial-material-32bytes!")]
    c.checkProtoBy (α := Option DbChecks.RotatingVaultDb.entries) "[enc-rot] K1 row 1 decrypts via prevKeys fallback"
      (← alice "get" (Qed.Proto.encode (1 : Nat))) (·.map (·.secret)) (some "sk_live_alpha")
    -- Re-encrypt row 1 under primary K2
    c.checkProtoBy (α := Option DbChecks.RotatingVaultDb.entries) "[enc-rot] updateOne re-encrypts row 1 under K2"
      (← alice "rotateValue" (Qed.Proto.encode ((1 : Nat), "sk_live_alpha_v2"))) (·.map (·.secret)) (some "sk_live_alpha_v2")
    -- Drop K1 from prevKeys: row 1 (now K2) STILL reads, row 2 (still K1) fails cleanly
    envRef.set [("VAULT_PRIMARY_KEY", "key-v2-rotated-material-32bytes!")]
    c.checkProtoBy (α := Option DbChecks.RotatingVaultDb.entries) "[enc-rot] rotated row 1 reads with K2 alone"
      (← alice "get" (Qed.Proto.encode (1 : Nat))) (·.map (·.secret)) (some "sk_live_alpha_v2")
    c.check "[enc-rot] unrotated K1 row 2 fails once K1 removed" (!(← alice "get" (Qed.Proto.encode (2 : Nat))).isOk)

private def runMultiTenantCrossTableSuite (c : TestChecker) (tmpDir : String) : IO Unit := do
  let srvInst := withRedirectedDb (.sqlitePath s!"{tmpDir}/multi_tenant.db")
  c.expectOk "[cross-rls] schema init" (← @MonadServer.dbExecDdl IO srvInst DbChecks.MultiTenantDb.config) fun () => do
    let asUser (u : String) (fn : String) (req := ByteArray.empty) :=
      @DbChecks.MultiTenantApi.dispatchM IO _ srvInst { userId := some u } fn req
    for (u, id, name, orgId) in [("alice", "app1", "Alpha", none), ("alice", "app2", "Beta Org", some "org1"), ("bob", "app3", "Bob Private", none)] do
      c.expectOk s!"[cross-rls] {u} creates {id}" (← asUser u "createApp" (Qed.Proto.encode (id, (name, orgId)))) fun _ => pure ()
    for (id, appId, u, role, status) in [("m1", "app1", "charlie", "admin", "accepted"), ("m2", "app1", "dave", "viewer", "accepted"), ("m3", "app1", "eve", "admin", "pending")] do
      c.expectOk s!"[cross-rls] add {u} ({status} {role}) on {appId}" (← asUser "alice" "addMember" (Qed.Proto.encode (id, (appId, (u, (role, status)))))) fun _ => pure ()
    c.expectOk "[cross-rls] add frank in org1" (← asUser "alice" "addOrgMember" (Qed.Proto.encode ("om1", ("org1", "frank")))) fun _ => pure ()
    for (tag, u, want) in [
        ("alice sees own app1, app2", "alice", #["app1", "app2"]),
        ("charlie sees shared app1", "charlie", #["app1"]),
        ("dave sees shared app1", "dave", #["app1"]),
        ("eve (pending) sees nothing", "eve", #[]),
        ("frank (org1) sees org app2", "frank", #["app2"]),
        ("bob sees only own app3", "bob", #["app3"]),
        ("outsider sees nothing", "mallory", #[])] do
      c.checkProtoBy (α := Array DbChecks.MultiTenantDb.apps) s!"[cross-rls] {tag}"
        (← asUser u "listAccessibleApps") (·.map (·.id)) want
    c.checkProtoBy (α := Array DbChecks.MultiTenantDb.apps) "[cross-rls] listSharedApps for charlie returns [app1]"
      (← asUser "charlie" "listSharedApps") (·.map (·.id)) #["app1"]
    for (tag, u, fn, newName, want) in [
        ("dave (viewer) cannot rename app1", "dave", "renameAppAsAdmin", "Hacked", none),
        ("eve (pending admin) cannot rename app1", "eve", "renameAppAsAdmin", "PendingHack", none),
        ("charlie (accepted admin) renames app1 via role in [owner, admin]", "charlie", "renameAppAsAdmin", "Alpha v2", some "Alpha v2"),
        ("charlie renames app1 via role == admin", "charlie", "renameAppAsSpecificAdmin", "Alpha v3", some "Alpha v3")] do
      c.checkProtoBy (α := Option DbChecks.MultiTenantDb.apps) s!"[cross-rls] {tag}"
        (← asUser u fn (Qed.Proto.encode ("app1", newName))) (·.map (·.name)) want

def run : IO Bool := do
  let c ← mkChecker "database"
  withDevApp c "QedTests.DbChecks" fun dir => do
    checkLeakGate c "QedTests.DbChecks" #["DbChecks.VaultDb.config", "DbChecks.VaultDb.secrets", "DbChecks.VaultDb.ensureSchema", "DbChecks.VaultDb.ddl", "DbChecks.VaultDb.rlsDdl", "DbChecks.VaultApi.dispatchM", "DbChecks.VaultApi.createNote_handler"]
    let authSecret := "db-test-hmac-secret-key"; let (aliceTok, bobTok) := (← signSessionToken authSecret "alice", ← signSessionToken authSecret "bob")
    let dbEnv (url : String) := #[("QED_WORKERS", some "2"), ("QED_AUTH_SECRET", some authSecret), ("QED_TEST_DB_URL", some url)]
    withTempDir "qed-db-native" fun tmpDir => do
      withNativeServer c "[sqlite] native server healthy" dir (dbEnv s!"sqlite://{tmpDir}/vault.db") (dev := true) fun srv => runVaultSuite c "sqlite" srv aliceTok bobTok (testRestart := true)
      withMockServer c "[http-sql] start mock" (startHttpSqlMock s!"{tmpDir}/http_mock.db") (·.stop) fun httpMock =>
        withNativeServer c "[http-sql] native server healthy" dir (dbEnv httpMock.url) (dev := true) fun srv => do
          runVaultSuite c "http-sql" srv aliceTok bobTok; let seen ← httpMock.seenSqlRef.get
          c.check "[http-sql] SQLi payload NEVER interpolated into SQL" (!(seen.any fun (s, _) => s.contains "DROP TABLE"))
          c.check "[http-sql] parameterized SQL sent with bound params" (seen.any fun (s, n) => s.contains "?" && n > 0)
      withMockServer c "[pg-wire] start mock" (startPgWireMock s!"{tmpDir}/pg_mock.db" "qeduser" "qedpass" "qeddb") (·.stop) fun pgMock =>
        withNativeServer c "[pg-wire] native server healthy" dir (dbEnv pgMock.url) (dev := true) fun srv => do
          runVaultSuite c "pg-wire" srv aliceTok bobTok
          c.check "[pg-wire] StartupMessage sent expected user & db" (← pgMock.startupOkRef.get)
          let (scramCnt, parsed) := (← pgMock.scramCountRef.get, ← pgMock.parsedSqlRef.get)
          c.check "[pg-wire] SCRAM-SHA-256 proof verified" (scramCnt > 0)
          c.check s!"[pg-wire] connection pool reused authenticated sockets (scram={scramCnt}, queries={parsed.size})" (scramCnt < parsed.size && scramCnt <= 6) s!"scram={scramCnt}, parsed={parsed.size}"
          c.check "[pg-wire] SQLi payload NEVER interpolated into Parse SQL" (!(parsed.any (·.contains "DROP TABLE")))
          c.check "[pg-wire] Parse used $1 placeholders with Bind params" (parsed.any (·.contains "$1"))
      runShopDirectSuite c "sqlite-direct" (withRedirectedDb (.sqlitePath s!"{tmpDir}/shop_direct.db")) (testConcurrentReaders := true)
      runEncryptedColumnSuite c (withRedirectedDb (.sqlitePath s!"{tmpDir}/enc_vault.db"))
      runKeyRotationAndMetaSuite c tmpDir
      runMultiTenantCrossTableSuite c tmpDir
      runMigrationSuite c tmpDir
      runRoadmapSuite c tmpDir
      withMockServer c "[pg-shop] start mock" (startPgWireMock s!"{tmpDir}/shop_pg_mock.db" "shopuser" "shoppass" "shopdb") (fun m => do Db.PgWire.clearPool; m.stop) fun shopPgMock => do
        let ssrfRes ← Db.PgWire.execParameterized shopPgMock.url "SELECT 1" #[] (ssrfGuard := true)
        c.check "[pg-ssrf] dynamic postgresUrl SSRF guard rejects loopback 127.0.0.1" (match ssrfRes with | .error _ => true | .ok _ => false) "expected SSRF rejection"
        runShopDirectSuite c "pg-direct" (withRedirectedDb (.postgresUrl shopPgMock.url (ssrfGuard := false)))
        let (scramCnt, parsed) := (← shopPgMock.scramCountRef.get, ← shopPgMock.parsedSqlRef.get)
        c.check s!"[pg-direct] connection pool reused sockets across tx & queries (scram={scramCnt}, queries={parsed.size})" (scramCnt > 0 && scramCnt <= 3 && parsed.size >= 10) s!"scram={scramCnt}, queries={parsed.size}"
        -- Postgres 25P02 aborted transaction safety: if a query errors inside a tx and caller falls through to COMMIT,
        -- finishPgTx MUST fail closed instead of returning .ok () on Postgres's ROLLBACK command tag.
        let pgCfg : DbConfig := { DbChecks.ShopDb.config with endpoint := .postgresUrl shopPgMock.url (ssrfGuard := false), devFallback? := none, envEndpoints? := none }
        let pgShop := DbChecks.ShopDb.clientWith pgCfg
        let _ ← pgShop.authors.insertOrIgnore { id := "pg_25p02_a", name := "Author" }
        let abortedTxRes ← pgShop.transaction fun tx => do
          let _ ← pgShop.authors.insert { id := "pg_25p02_a", name := "dup-pk-error" } (txId? := some tx)
          return (.ok () : Except ApiError Unit)
        c.check "[pg-25p02] COMMIT on aborted Postgres tx returns error (never silent .ok)" (!abortedTxRes.isOk) "expected finishPgTx error on aborted tx"
        let ignTxRes ← pgShop.transaction fun tx => pgShop.authors.insertOrIgnore { id := "pg_25p02_a", name := "dup-ignored" } (txId? := some tx)
        c.expectOk "[pg-25p02] insertOrIgnore inside Postgres tx commits cleanly" ignTxRes fun opt =>
          c.check "[pg-25p02] duplicate author ignored" opt.isNone
        -- Item 10a: resolveDbConfigCore honors explicit primary env var when QED_DEPLOY_ENV=dev
        let devFallbackCfg : DbConfig := {
          name := "DevOverrideDb", endpoint := .urlEnv "QED_DEV_TEST_DB_URL",
          devFallback? := some (.sqlitePath ".qed/fallback.db"),
          envEndpoints? := some { prod := .urlEnv "QED_DEV_TEST_DB_URL", staging := .urlEnv "QED_DEV_TEST_DB_URL",
                                  preview := .urlEnv "QED_DEV_TEST_DB_URL", dev := .sqlitePath ".qed/fallback.db" } }
        let resFallback ← Native.resolveDbConfigCore (some "dev") false devFallbackCfg
        c.check "[db-resolve] QED_DEPLOY_ENV=dev uses dev sqlite when primary env unset" (match resFallback with | .ok (.sqlite ".qed/fallback.db") => true | _ => false)
        let explicitCfg : DbConfig := { devFallbackCfg with endpoint := .urlEnv "HOME" }
        let resExplicit ← Native.resolveDbConfigCore (some "dev") false explicitCfg
        c.check "[db-resolve] QED_DEPLOY_ENV=dev honors explicitly set primary env var over dev sqlite" (match resExplicit with | .error e => e.message.contains "unrecognized database URL scheme" | _ => false)
  c.finish

end QedTests.Native.Database
