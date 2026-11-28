import QedTests.Native.Harness
import QedTests.DbChecks
import Qed.Server.Native
open Qed.Server Qed.Server.Db

namespace QedTests.Native.Database

structure HttpSqlMock where (url : String) (seenSqlRef : IO.Ref (Array (String × Nat))) (stop : IO Unit)

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
private def pgErrCode (sqlstate msg : String) : ByteArray :=
  pgFrame 'E' (PgWire.pushCString (ByteArray.empty.push 0x53) "ERROR" ++ PgWire.pushCString (ByteArray.empty.push 0x43) sqlstate ++ PgWire.pushCString (ByteArray.empty.push 0x4D) msg |>.push 0)
private def pgReady (tx? : Option UInt64 := none) (aborted : Bool := false) : ByteArray :=
  pgFrame 'Z' (ByteArray.mk #[if tx?.isNone then 0x49 else if aborted then 0x45 else 0x54])
private def pgAbortedErr : ByteArray := pgErrCode "25P02" "current transaction is aborted, commands ignored until end of transaction block"
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

private def readPgDigits (cs : Array Char) (j : Nat) (acc : Nat) : Nat × Nat :=
  if h : j < cs.size then if cs[j].isDigit then readPgDigits cs (j + 1) (acc * 10 + (cs[j].toNat - 48)) else (j, acc) else (j, acc)
private def translatePgSqlLoop (cs : Array Char) (params : Array SqlVal) : Nat → Nat → Bool → Array Char → Array SqlVal → String × Array SqlVal
  | 0, _, _, out, bound => (String.ofList out.toList, bound)
  | fuel + 1, i, inQ, out, bound =>
      if h : i < cs.size then
        let ch := cs[i]
        if ch == '\'' then translatePgSqlLoop cs params fuel (i + 1) (!inQ) (out.push ch) bound
        else if !inQ && ch == '$' && i + 1 < cs.size && cs[i + 1]!.isDigit then
          let (j, num) := readPgDigits cs (i + 1) 0
          translatePgSqlLoop cs params fuel j false (out.push '?') (bound.push (params.getD (num - 1) .null))
        else translatePgSqlLoop cs params fuel (i + 1) inQ (out.push ch) bound
      else (String.ofList out.toList, bound)
private def translatePgSql (sql : String) (params : Array SqlVal) : String × Array SqlVal :=
  let cs := (sql.replace "STRPOS(" "INSTR(").toList.toArray; translatePgSqlLoop cs params (cs.size + 1) 0 false #[] #[]
private def findZeroByte (ba : ByteArray) (i : Nat) : Nat :=
  if h : i < ba.size then if ba[i] == 0 then i else findZeroByte ba (i + 1) else ba.size
termination_by ba.size - i
private def xorBytes (a b : ByteArray) : ByteArray := ByteArray.mk <| Array.ofFn (n := min a.size b.size) fun i => a[i.val]! ^^^ b[i.val]!

structure PgWireMock where
  url : String
  parsedSqlRef : IO.Ref (Array String)
  rlsDdlRef : IO.Ref (Array String)
  sessionVarsRef : IO.Ref (Array (String × String))
  scramCountRef : IO.Ref Nat
  startupOkRef : IO.Ref Bool
  stop : IO Unit

private def pgR32 (b : ByteArray) (o : Nat) : Nat := (PgWire.readU32BE b o).getD 0
private def pgR16 (b : ByteArray) (o : Nat) : Nat := (PgWire.readU16BE b o).getD 0
private def pgRi32 (b : ByteArray) (o : Nat) : Int := (PgWire.readI32BE b o).getD 0
private def pgNextTagged (conn : UInt64) (b : ByteArray) : IO (Option (Char × ByteArray × ByteArray)) := do
  let some b1 ← readExact conn b 5 | return none
  let len := pgR32 b1 1
  let some b2 ← readExact conn b1 (1 + len) | return none
  return some (Char.ofNat (b1[0]!).toNat, b2.extract 5 (1 + len), b2.extract (1 + len) b2.size)
private def pgScanKv : List String → String × String
  | k :: v :: rest => let (u, d) := pgScanKv rest; (if k == "user" then v else u, if k == "database" then v else d) | _ => ("", "")
private def pgStartupLoop (conn : UInt64) (expectedUser expectedDb : String) (startupOkRef : IO.Ref Bool) : Nat → ByteArray → IO (Option ByteArray)
  | 0, _ => return none
  | fuel + 1, buf => do
      let some b1 ← readExact conn buf 4 | return none
      let len := pgR32 b1 0
      let some b2 ← readExact conn b1 len | return none
      let (body, nextBuf) := (b2.extract 4 len, b2.extract len b2.size)
      if pgR32 body 0 == 80877103 then discard <| Prim.outboundWriteAll conn "N".toUTF8; pgStartupLoop conn expectedUser expectedDb startupOkRef fuel nextBuf
      else
        if pgScanKv ((utf8Str (body.extract 4 body.size)).splitOn "\x00") == (expectedUser, expectedDb) then startupOkRef.set true
        discard <| Prim.outboundWriteAll conn (pgAuthMsg 10 ((("SCRAM-SHA-256".toUTF8).push 0).push 0))
        return some nextBuf
private def pgReadBindParams (payload : ByteArray) : Nat → Nat → Array SqlVal → Array SqlVal
  | 0, _, ps => ps
  | n + 1, off, ps =>
      let pLen := pgRi32 payload off; let o1 := off + 4
      if pLen < 0 then pgReadBindParams payload n o1 (ps.push .null)
      else pgReadBindParams payload n (o1 + pLen.toNat) (ps.push (.text (utf8Str (payload.extract o1 (o1 + pLen.toNat)))))
private def pgSessionLoop (conn : UInt64) (sqliteFile : String) (parsedSqlRef rlsDdlRef : IO.Ref (Array String))
    (sessionVarsRef : IO.Ref (Array (String × String))) :
    Nat → ByteArray → String → Array SqlVal → Option UInt64 → Bool → IO (Option UInt64)
  | 0, _, _, _, tx?, _ => return tx?
  | fuel + 1, buf, prepSql, bParams, tx?, aborted => do
      let send (bs : ByteArray) : IO Unit := discard <| Prim.outboundWriteAll conn bs
      let next := pgSessionLoop conn sqliteFile parsedSqlRef rlsDdlRef sessionVarsRef fuel
      let some (tag, payload, rest) ← pgNextTagged conn buf | return tx?
      match tag with
      | 'Q' =>
          let sql := (utf8Str (payload.extract 0 (payload.size - 1))).trimAscii.toString; let upper := sql.toUpper
          if upper == "BEGIN" then
            match ← Prim.sqliteTxBegin sqliteFile with
            | .ok tid => send (pgCmdDone "BEGIN" ++ pgReady (some tid)); next rest prepSql bParams (some tid) false
            | .error e => send (pgErr e ++ pgReady tx?); next rest prepSql bParams tx? false
          else if upper == "COMMIT" || upper == "ROLLBACK" then
            let baseResp := pgCmdDone (if upper == "COMMIT" && aborted then "ROLLBACK" else upper)
            let resp ← match tx? with
              | some tid =>
                  if upper == "COMMIT" && !aborted then
                    match ← Prim.sqliteTxCommit tid with | .error e => pure (pgErr e) | .ok () => pure baseResp
                  else Prim.sqliteTxRollback tid; pure baseResp
              | none => pure baseResp
            send (resp ++ pgReady); next rest prepSql bParams none false
          else if aborted then send (pgAbortedErr ++ pgReady tx? true); next rest prepSql bParams tx? true
          else if upper.contains "ROW LEVEL SECURITY" || upper.contains "CREATE POLICY" || upper.contains "DROP POLICY" || upper.contains "DO $QED_CHK$" then
            rlsDdlRef.modify (·.push sql)
            send (pgCmdDone "ALTER TABLE" ++ pgReady tx?); next rest prepSql bParams tx? false
          else match ← Prim.sqliteDdl sqliteFile sql with
            | .ok () => send (pgCmdDone "CREATE TABLE" ++ pgReady tx?); next rest prepSql bParams tx? false
            | .error e => let ab := tx?.isSome; send (pgErr e ++ pgReady tx? ab); next rest prepSql bParams tx? ab
      | 'P' =>
          let n1 := findZeroByte payload 0; let nextSql := utf8Str (payload.extract (n1 + 1) (findZeroByte payload (n1 + 1)))
          send (pgFrame '1' ByteArray.empty); next rest nextSql bParams tx? aborted
      | 'B' =>
          let o2 := findZeroByte payload (findZeroByte payload 0 + 1) + 1; let o3 := o2 + 2 + pgR16 payload o2 * 2
          let ps := pgReadBindParams payload (pgR16 payload o3) (o3 + 2) #[]
          parsedSqlRef.modify (·.push prepSql); send (pgFrame '2' ByteArray.empty); next rest prepSql ps tx? aborted
      | 'E' =>
          if aborted then send pgAbortedErr; next rest prepSql bParams tx? true
          else if prepSql.startsWith "SELECT set_config('qed.user_id'" then
            let uid := match bParams[0]? with | some (SqlVal.text s) => s | _ => ""
            let ptag := match bParams[1]? with | some (SqlVal.text s) => s | _ => ""
            sessionVarsRef.modify (·.push (uid, ptag))
            let row := #[SqlVal.text uid, SqlVal.text ptag]
            send (pgRowDescription row ++ pgDataRow row ++ pgCmdDone "SELECT 1")
            next rest prepSql bParams tx? false
          else
            let (sqliteSql, sqliteParams) := translatePgSql prepSql bParams
            let execRes ← match tx? with | some tid => Prim.sqliteTxExec tid sqliteSql sqliteParams | none => Prim.sqliteExec sqliteFile sqliteSql sqliteParams
            match execRes with
            | .error e =>
                let ab := tx?.isSome; send (pgErrCode (if e.contains "UNIQUE" then "23505" else "42000") e)
                next rest prepSql bParams tx? ab
            | .ok res =>
                let upperSql := prepSql.trimAscii.toString.toUpper
                let frames := if h : 0 < res.rows.size then res.rows.foldl (init := pgRowDescription res.rows[0]) fun f row => f ++ pgDataRow row
                  else if ["SELECT COUNT", "SELECT SUM", "SELECT MIN", "SELECT MAX"].any (upperSql.startsWith ·) then pgRowDescription #[.int 0] else ByteArray.empty
                let verb := (upperSql.splitOn " ").headD "OK"
                send (frames ++ pgCmdDone (if verb == "INSERT" then s!"INSERT 0 {res.affected}" else s!"{verb} {if res.rows.size > 0 then res.rows.size else res.affected}"))
                next rest prepSql bParams tx? false
      | 'S' => send (pgReady tx? aborted); next rest prepSql bParams tx? aborted
      | 'X' => return tx?
      | _ => next rest prepSql bParams tx? aborted

private def handlePgConn (conn : UInt64) (sqliteFile expectedUser expectedPass expectedDb : String)
    (parsedSqlRef rlsDdlRef : IO.Ref (Array String)) (sessionVarsRef : IO.Ref (Array (String × String)))
    (scramCountRef : IO.Ref Nat) (startupOkRef : IO.Ref Bool) : IO Unit := do
  let send (bs : ByteArray) : IO Unit := discard <| Prim.outboundWriteAll conn bs
  let some buf0 ← pgStartupLoop conn expectedUser expectedDb startupOkRef 16 ByteArray.empty | return
  let (saltBytes, iters) := ("qedsalt012345678".toUTF8, 4096)
  let some ('p', p1, b1) ← pgNextTagged conn buf0 | return
  let nul := findZeroByte p1 0; let cf1 := utf8Str (p1.extract (nul + 5) (nul + 5 + (pgRi32 p1 (nul + 1)).toNat))
  if utf8Str (p1.extract 0 nul) != "SCRAM-SHA-256" || !cf1.startsWith "n,," then send (pgErr "unsupported SASL mechanism"); return
  let clientFirstBare := dropChars cf1 3
  let clientNonce := match (clientFirstBare.splitOn "r=").drop 1 with | r :: _ => (r.splitOn ",").headD "" | [] => ""
  let serverFirst := s!"r={clientNonce}qedservernonce9876,s={Net.base64Encode saltBytes},i={iters}"
  send (pgAuthMsg 11 serverFirst.toUTF8)
  let some ('p', p2, b2) ← pgNextTagged conn b1 | return
  let [clientFinalNoProof, clientProofB64] := (utf8Str p2).splitOn ",p=" | send (pgErr "malformed SASLResponse"); return
  let salted ← Prim.pbkdf2HmacSha256 expectedPass.toUTF8 saltBytes iters.toUInt32
  let clientKey ← Prim.hmacSha256 salted "Client Key".toUTF8
  let (storedKey, serverKey) := (← Prim.sha256 clientKey, ← Prim.hmacSha256 salted "Server Key".toUTF8)
  let authMsg := s!"{clientFirstBare},{serverFirst},{clientFinalNoProof}"
  if clientProofB64 != Net.base64Encode (xorBytes clientKey (← Prim.hmacSha256 storedKey authMsg.toUTF8)) then send (pgErr "SCRAM-SHA-256 authentication failed"); return
  let serverSig ← Prim.hmacSha256 serverKey authMsg.toUTF8
  scramCountRef.modify (· + 1); send (pgAuthMsg 12 (s!"v={Net.base64Encode serverSig}").toUTF8 ++ pgAuthMsg 0 ++ pgReady)
  if let some tid ← pgSessionLoop conn sqliteFile parsedSqlRef rlsDdlRef sessionVarsRef 10000 b2 "" #[] none false then Prim.sqliteTxRollback tid

private def startPgWireMock (sqliteFile user pass dbName : String) : IO (Except String PgWireMock) := do
  let (parsedSqlRef, rlsDdlRef, sessionVarsRef, scramCountRef, startupOkRef) :=
    (← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef #[], ← IO.mkRef 0, ← IO.mkRef false)
  let res ← startMockTcpServer (concurrent := true) fun conn =>
    handlePgConn conn sqliteFile user pass dbName parsedSqlRef rlsDdlRef sessionVarsRef scramCountRef startupOkRef
  return res.map fun (port, stop) =>
    { url := s!"postgres://{user}:{pass}@127.0.0.1:{port}/{dbName}?sslmode=disable", parsedSqlRef, rlsDdlRef, sessionVarsRef, scramCountRef, startupOkRef, stop }

private def runMovedDbChecks (c : TestChecker) : IO Unit := do
  let mk (p1 p2 i1 i2 : String) := SqlQuery.select (sql!"items") [sql!"id"]
    (.binOp .and (.startsWith (.col (sql!"title")) (.param (.text p1))) (.binOp .and (.contains (.col (sql!"title")) (.param (.text p2))) (.inList (.col (sql!"id")) [.text i1, .text i2])))
    (limit := some 10) (offset := some 5)
  let (oldTbl, newTbl, _) := DbChecks.mkMigrationFixture (sql!"items")
  let steps := diffTableSchemas [oldTbl] [newTbl]; let (pgDdl, sqDdl) := (renderMigrationDdl .postgres steps, renderMigrationDdl .sqlite steps)
  c.checkAll [
    ("[ddl] VaultDb postgres/sqlite/rls DDL",
      hasAll (DbChecks.VaultDb.ddl .postgres) ["CREATE TABLE IF NOT EXISTS \"notes\"", "CHECK (1 <= LENGTH(\"body\") AND LENGTH(\"body\") <= 2000)"] &&
      (DbChecks.VaultDb.ddl .sqlite).contains "CREATE INDEX IF NOT EXISTS \"idx_notes_0\" ON \"notes\" (\"ownerId\", \"version\")" &&
      hasAll DbChecks.VaultDb.rlsDdl ["ENABLE ROW LEVEL SECURITY", "FORCE ROW LEVEL SECURITY", "FOR SELECT", "FOR INSERT", "FOR UPDATE", "FOR DELETE", "current_setting('qed.user_id', true)"] &&
      hasAll DbChecks.DefaultDenyDb.rlsDdl ["ENABLE ROW LEVEL SECURITY", "FORCE ROW LEVEL SECURITY", "USING (FALSE)", "WITH CHECK (FALSE)"]),
    ("[ddl] ShopDb migration DDL & SQLi parameterization",
      DbChecks.sameCompiledSql (mk "Rust" "Lean" "a" "b") (mk "'; DROP TABLE items; --" "%' OR 1=1 --" "'; DELETE FROM items;" "x") &&
      hasAll pgDdl ["ADD COLUMN IF NOT EXISTS \"notes\" TEXT", "ADD COLUMN IF NOT EXISTS \"views\" BIGINT NOT NULL DEFAULT 0"] && hasAll sqDdl ["ADD COLUMN \"views\" INTEGER NOT NULL DEFAULT 0", "CREATE INDEX IF NOT EXISTS \"idx_items_0\""]),
    ("[ddl] EncVaultDb derived ciphertext CHECK bounds",
      hasAll (DbChecks.EncVaultDb.ddl .postgres) ["\"body\" TEXT NOT NULL CHECK (40 <= LENGTH(\"body\") AND LENGTH(\"body\") <= 304)", "\"note\" TEXT NOT NULL CHECK (40 <= LENGTH(\"note\") AND LENGTH(\"note\") <= 1104)", "\"raw\" TEXT CHECK (40 <= LENGTH(\"raw\"))"]),
    ("[ddl] RoadmapDb FK/enum/field/scaling CHECK & NOT VALID DDL + backfill",
      hasAll (DbChecks.RoadmapDb.ddl .postgres) ["ON DELETE CASCADE", "ON DELETE SET NULL", "ON DELETE RESTRICT", "CHECK (\"stage\" IN ('queued', 'in-progress', 'live', 'failed'))",
        "\"slug\" TEXT NOT NULL PRIMARY KEY", "\"port\" BIGINT NOT NULL CHECK (\"port\" >= 0)", "\"altPort\" BIGINT", "CONSTRAINT \"qed_chk_scaling_0\" CHECK (\"minInstances\" <= \"maxInstances\")",
        "CONSTRAINT \"qed_chk_scaling_1\" CHECK ((((\"plan\" = 'pro' OR \"plan\" = 'enterprise')) OR ((\"minInstances\" = 0 AND \"maxInstances\" <= 1))))"] &&
      hasAll (DbChecks.RoadmapDb.ddl .sqlite) ["\"port\" INTEGER NOT NULL CHECK (\"port\" >= 0)", "ON DELETE CASCADE"] && hasAll (renderDatabaseCheckDdl DbChecks.RoadmapDb.config.tables) ["ADD CONSTRAINT \"qed_chk_scaling_1\" CHECK", "NOT VALID"] &&
      (DbChecks.RoadmapDb.config.backfills[0]?.map fun q => (q.compile .postgres).1.contains "UPDATE \"projects\" SET \"note\" = $1 WHERE (\"note\" IS NULL)") == some true),
    ("[ddl] MultiTenantDb cross-table EXISTS RLS DDL",
      hasAll DbChecks.MultiTenantDb.rlsDdl ["EXISTS (SELECT 1 FROM \"app_members\" AS \"m\" WHERE", "\"apps\".\"id\"", "EXISTS (SELECT 1 FROM \"org_members\" AS \"om\" WHERE", "\"m\".\"role\" IN ('owner', 'admin')"]),
    ("[ddl] TxLeaseDb RLS DDL", hasAll DbChecks.TxLeaseDb.rlsDdl ["ENABLE ROW LEVEL SECURITY", "current_setting('qed.user_id', true)"]),
    ("[db-pure] SQLi parameterization, migration safety, mappings, Date/Int FromSql, empty select, & Meta codecs",
      let mkN (v : String) := SqlQuery.select (sql!"notes") [sql!"id"] (.binOp .eq (.col (sql!"ownerId")) (.param (.text v)))
      let (_, _, unsafeCol) := DbChecks.mkMigrationFixture (sql!"items")
      let d? := Qed.Date.mk? 2026 11 25
      let (tbl, col) := (sql!"projects", sql!"owner_id")
      let emptySel := (SqlQuery.select tbl [] .litTrue).compile .postgres
      let cents := DbChecks.DollarsToCentsMap.encode ⟨25, by decide⟩
      let m : DbChecks.RotatingVaultDb.entries.Meta := { id := 7, ownerId := "u1", label := "api-key" }
      DbChecks.sameCompiledSql (mkN "alice") (mkN "' OR 1=1; DROP TABLE notes; --") &&
      steps.length == 3 && (verifyMigrationSafe steps).isOk && (diffTableSchemas [newTbl] [newTbl]).isEmpty &&
      !(verifyMigrationSafe [.addColumn (sql!"items") unsafeCol none]).isOk &&
      (match DbChecks.SecretNoteInput.parse { body := "hello" } with | some s => let ct := DbChecks.sealedNoteMap.encode s; 40 <= ct.val.length && ct.val.length <= 304 && (match DbChecks.sealedNoteMap.toSource ct.val with | .ok d => d.body.val == "hello" | .error _ => false) | none => false) &&
      cents.val == 2500 && (match DbChecks.DollarsToCentsMap.decode cents.val with | .ok d => d.val == 25 | .error _ => false) &&
      (match DbChecks.DollarsToCentsMap.decode 2550 with | .error msg => msg == "must be whole dollars" | .ok _ => false) &&
      !(DbChecks.DollarsToCentsMap.decode 1000100).isOk && !DbChecks.EncVaultDb.secrets.contains "QED_TEST_ENC_KEY" &&
      (match d?.map fun d => FromSql.fromSql (α := Qed.Date) (ToSql.toSql d) with | some (.ok d') => some d' == d? | _ => false) &&
      DbChecks.RoadmapDb.config.backfills.length == 1 && FromSql.fromSql (α := Int) (.text "-42") == .ok (-42) && !(FromSql.fromSql (α := Int) (.text "not_int")).isOk &&
      !emptySel.1.contains "*" && emptySel.1.contains "0 = 1" && ((SqlQuery.selectAll tbl .litTrue).compile .postgres).1 == "SELECT * FROM \"projects\" WHERE TRUE" &&
      ((SqlQuery.insertOrIgnore tbl [(col, .text "a")] [] [col]).compile .postgres).1 == "INSERT INTO \"projects\" (\"owner_id\") VALUES ($1) ON CONFLICT DO NOTHING RETURNING \"owner_id\"" &&
      (let g := SqlExpr.existsSubquery (sql!"app_members") (sql!"m") (.binOp .eq (.col (sql!"appId")) (.param (.text "app1")))
       let gBad := SqlExpr.existsSubquery (sql!"app_members") (sql!"m") (.binOp .eq (.col (sql!"appId")) (.param (.text "'; DROP TABLE apps; --")))
       let q1 := SqlQuery.insert (sql!"deployments") [(sql!"id", .text "d1"), (sql!"seq", .int 1), (sql!"active", .bool true), (sql!"blob", .null)] [sql!"id"] (some g) [.text, .int, .bool, .bytes]
       let q2 := SqlQuery.insert (sql!"deployments") [(sql!"id", .text "' OR 1=1"), (sql!"seq", .int 99), (sql!"active", .bool false), (sql!"blob", .bytes ByteArray.empty)] [sql!"id"] (some gBad) [.text, .int, .bool, .bytes]
       let qIgn := SqlQuery.insertOrIgnore (sql!"deployments") [(sql!"id", .text "d1")] [sql!"id"] [sql!"id"] (some g) [.text]
       (q1.compile .postgres).1 == "INSERT INTO \"deployments\" (\"id\", \"seq\", \"active\", \"blob\") SELECT CAST($1 AS TEXT), CAST($2 AS BIGINT), CAST($3 AS BOOLEAN), CAST($4 AS BYTEA) WHERE EXISTS (SELECT 1 FROM \"app_members\" AS \"m\" WHERE (\"appId\" = $5)) RETURNING \"id\"" &&
       (q1.compile .sqlite).1 == "INSERT INTO \"deployments\" (\"id\", \"seq\", \"active\", \"blob\") SELECT ?1, ?2, ?3, ?4 WHERE EXISTS (SELECT 1 FROM \"app_members\" AS \"m\" WHERE (\"appId\" = ?5)) RETURNING \"id\"" &&
       (qIgn.compile .postgres).1 == "INSERT INTO \"deployments\" (\"id\") SELECT CAST($1 AS TEXT) WHERE EXISTS (SELECT 1 FROM \"app_members\" AS \"m\" WHERE (\"appId\" = $2)) ON CONFLICT (\"id\") DO NOTHING RETURNING \"id\"" &&
       DbChecks.sameCompiledSql q1 q2) &&
      DbChecks.RotatingVaultDb.secrets == #["VAULT_PRIMARY_KEY"] && DbChecks.RotatingVaultDb.entries.metaColNames == ["id", "ownerId", "label"] &&
      Qed.fromJson (α := DbChecks.RotatingVaultDb.entries.Meta) (Qed.toJson m) == .ok m &&
      Qed.Proto.decode (α := DbChecks.RotatingVaultDb.entries.Meta) (Qed.Proto.encode m) == .ok m)]

private def runVaultSuite (c : TestChecker) (label : String) (srv : NativeServerProc) (aliceTok bobTok : String) (testRestart : Bool := false) : IO Unit := do
  let (sqli, lbl) := ("' OR 1=1; DROP TABLE notes; --", fun s => s!"[{label}] {s}")
  let call (fn : String) (req := ByteArray.empty) (tok? : Option String := none) := httpRpc srv.port "VaultApi" fn req tok?
  let alice (fn : String) (req := ByteArray.empty) := call fn req (some aliceTok)
  let bob   (fn : String) (req := ByteArray.empty) := call fn req (some bobTok)
  let encNote (id : Nat) (body : String) := Qed.Proto.encode (id, body)
  let (id1, id2) := (Qed.Proto.encode (1 : Nat), Qed.Proto.encode (2 : Nat))
  let publishedNote1 : DbChecks.VaultDb.notes := { id := 1, ownerId := "alice", body := "updated text", version := 2, status := "published" }
  c.checkStatusAll [(lbl "unauthenticated createNote rejected (401)", call "createNote" (encNote 1 "hi"), 401), (lbl "empty body rejected by requires (400)", alice "createNote" (encNote 1 ""), 400)]
  let checkCreate (tag : String) (id : Nat) (body : String) (k : DbChecks.VaultDb.notes → IO Unit) : IO Unit := do
    c.checkHttp (lbl tag) (← alice "createNote" (encNote id body)) (extra := fun r =>
      c.checkRpcDomainOk (E := DbChecks.VaultApi.createNote.Error) (α := DbChecks.VaultDb.notes) (lbl s!"{tag} payload") (.ok (ε := String) r.body) k)
  checkCreate "alice createNote(1)" 1 "hello verified db" (c.checkEq (lbl "alice createNote(1) payload") · { id := 1, ownerId := "alice", body := "hello verified db", version := 0, status := "draft" })
  checkCreate "alice createNote(2) SQLi stored safely" 2 sqli fun got => c.checkEq (lbl "alice createNote(2) verbatim body") got.body sqli
  forList [("alice countMyNotes == 2", alice "countMyNotes", 2), ("bob countMyNotes == 0 (RLS)", bob "countMyNotes", 0), ("bob deleteNote(1) == 0 (RLS)", bob "deleteNote" id1, 0)] fun (tag, act, want) => do c.checkRpcProto (lbl tag) (← act) (want : Nat)
  forList [("alice listMyNotes returns 2 notes", alice "listMyNotes", 2), ("bob listMyNotes == 0 (RLS)", bob "listMyNotes", 0)] fun (tag, act, want) => do c.checkRpcProtoBy (α := Array DbChecks.VaultDb.notes) (lbl tag) (← act) (·.size) want
  forList [("bob getNote(1) == none (RLS)", bob "getNote" id1, (none : Option DbChecks.VaultDb.notes)), ("bob editNote(1) == none (RLS)", bob "editNote" (encNote 1 "pwned"), none),
      ("alice editNote(1) updated", alice "editNote" (encNote 1 "updated text"), some { id := 1, ownerId := "alice", body := "updated text", version := 1, status := "draft" }),
      ("alice publishNote(1) draft -> published", alice "publishNote" id1, some publishedNote1), ("alice publishNote(1) twice returns none", alice "publishNote" id1, none)] fun (tag, act, want) => do
    c.checkRpcProto (lbl tag) (← act) want
  if testRestart then
    c.check (lbl "server restarted cleanly") (← srv.restart)
    c.checkRpcProto (lbl "note 1 persisted across restart") (← alice "getNote" id1) (some publishedNote1)
    c.checkRpcProtoBy (α := Option DbChecks.VaultDb.notes) (lbl "SQLi note 2 persisted verbatim across restart") (← alice "getNote" id2) (·.map (·.body)) (some sqli)
  forList [("alice deleteNote(2) == 1", alice "deleteNote" id2, 1), ("alice countMyNotes == 1 after delete", alice "countMyNotes", 1)] fun (tag, act, want) => do c.checkRpcProto (lbl tag) (← act) (want : Nat)
  c.checkStatus (lbl "seedBook status 200") (← alice "seedBook" (Qed.Proto.encode ("lean4", ("Theorem Proving in Lean 4", (10 : Nat))))) 200
  c.checkRpcProto (lbl "listBooks returns 1 book") (← call "listBooks") (#[{ id := "lean4", title := "Theorem Proving in Lean 4", stock := 10 }] : Array DbChecks.VaultDb.books)
  c.checkRpcProtoBy (α := Option DbChecks.VaultDb.books) (lbl "orderBook(3) stock 10 -> 7") (← alice "orderBook" (Qed.Proto.encode ("lean4", (3 : Nat)))) (·.map (·.stock)) (some 7)
  c.checkRpcProto (lbl "orderBook(10) when stock=7 returns none") (← alice "orderBook" (Qed.Proto.encode ("lean4", (10 : Nat)))) (none : Option DbChecks.VaultDb.books)

set_option warn.classDefReducibility false in
@[noinline, nospecialize]
private def withRedirectedDb (ep : DbEndpoint) : MonadServer IO :=
  let (base, r) := (Native.mkNativeServerInst none none, fun cfg : DbConfig => { cfg with endpoint := ep, devFallback? := none })
  { exec := fun
      | .dbExec c q auth => base.exec (.dbExec (r c) q auth) | .dbExecDdl c => base.exec (.dbExecDdl (r c)) | .dbTxBegin c auth => base.exec (.dbTxBegin (r c) auth)
      | .dbTxExec c t q => base.exec (.dbTxExec (r c) t q) | .dbTxCommit c t => base.exec (.dbTxCommit (r c) t) | .dbTxRollback c t => base.exec (.dbTxRollback (r c) t) | eff => base.exec eff }

@[noinline, nospecialize]
private def runShopDirectSuite (c : TestChecker) (label : String) (srvInst : MonadServer IO) (testConcurrentReaders : Bool := false) : IO Unit := do
  let lbl (s : String) := s!"[{label}] {s}"; let stBox ← Prim.mkStateBox DbChecks.ShopApi.initState; let atomicInst : MonadAtomic DbChecks.ShopApi.State IO := Native.withStateBox stBox
  c.expectOk (lbl "ShopDb schema init") (← @MonadServer.dbExecDdl IO srvInst DbChecks.ShopDb.config) fun () => do
    c.check (lbl "ShopDb schema initialized") true
    let alice (fn : String) (req := ByteArray.empty) := @DbChecks.ShopApi.dispatchM IO _ srvInst atomicInst (RequestCtx.forUser "alice") fn req
    let bob   (fn : String) (req := ByteArray.empty) := @DbChecks.ShopApi.dispatchM IO _ srvInst atomicInst (RequestCtx.forUser "bob") fn req
    let mkTxReq (aid aname iid title : String) (price : Nat) := Qed.Proto.encode (aid, (aname, (iid, (title, price))))
    c.checkProto (lbl "empty sum == 0") (← alice "totalInventoryValue") (0 : Nat)
    c.checkProto (lbl "empty min == none") (← alice "cheapestPrice") (none : Option Nat)
    c.checkRpcDomainOk (E := DbChecks.ShopApi.createAuthorAndItem.Error) (α := DbChecks.ShopDb.items) (lbl "db.transaction: committed author + item")
      (← alice "createAuthorAndItem" (mkTxReq "a1" "Ada Lovelace" "i1" "Lean 4 Proofs" 100)) fun it => c.check (lbl "db.transaction: committed author + item") (it.id == "i1" && it.price == 100)
    forList [("a2", "Alan Turing", "i2", "Lean 4 Compilers", 250), ("a3", "Grace Hopper", "i3", "Rust Systems 100%", 50)] fun (aid, aname, iid, title, price) => do
      c.expectOk (lbl s!"createAuthorAndItem({iid})") (← alice "createAuthorAndItem" (mkTxReq aid aname iid title price)) fun _ => pure ()
    c.checkEq (lbl "atomic txOps incremented 3 times inside transactions") (← Prim.atomicRead stBox (·.txOps)) 3
    c.checkRpcDomainErr (E := DbChecks.ShopApi.createPairDotSyntax.Error) (α := DbChecks.ShopDb.items) (lbl "db.transaction: returned fail(.aborted)")
      (← alice "createPairDotSyntax" (mkTxReq "a_rolled_back" "Ghost Author" "i_ghost" "Ghost Item" 99999)) (·.tag == .aborted)
    c.checkOkBy (lbl "rolled-back author does NOT exist in DB") (← @MonadServer.dbExec IO srvInst DbChecks.ShopDb.config (SqlQuery.count (sql!"authors") (.binOp .eq (.col (sql!"id")) (.param (.text "a_rolled_back")))) AuthToken.anonymous)
      (fun res => match res.rows[0]?.bind (·[0]?) with | some (SqlVal.int n) => n | _ => -1) (0 : Int)
    forList [("startsWith+contains+orderBy(-price) returns [i2, i1]", "Lean", "4", 0, #["i2", "i1"]), ("offset=1 returns [i1]", "Lean", "4", 1, #["i1"]), ("LIKE escapes literal % safely", "Rust", "100%", 0, #["i3"])] fun (tag, pfx, sub, off, want) => do
      c.checkProtoBy (α := Array DbChecks.ShopDb.items) (lbl tag) (← alice "searchItems" (Qed.Proto.encode (pfx, (sub, off)))) (·.map (·.id)) want
    c.checkProtoBy (α := Array DbChecks.ShopDb.items) (lbl "IN list returns [i1, i3]") (← alice "filterByIds" (Qed.Proto.encode (#["i3", "i1"] : Array String))) (·.map (·.id)) #["i1", "i3"]
    c.checkProtoBy (α := Array DbChecks.ShopDb.items) (lbl "empty IN list returns 0 rows") (← alice "filterByIds" (Qed.Proto.encode (#[] : Array String))) (·.size) 0
    forList [("alice sum(price) == 400", alice "totalInventoryValue", 400), ("bob sum(price) == 0 (RLS)", bob "totalInventoryValue", 0)] fun (tag, act, want) => do c.checkProto (lbl tag) (← act) (want : Nat)
    forList [("alice min(price) == some 50", "cheapestPrice", some (50 : Nat)), ("alice max(price) == some 250", "highestPrice", some 250)] fun (tag, fn, want) => do c.checkProto (lbl tag) (← alice fn) want
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

@[noinline, nospecialize]
private def runEncryptedColumnSuite (c : TestChecker) (srvInst : MonadServer IO) : IO Unit := do
  let cfg := DbChecks.EncVaultDb.config
  c.expectOk "[enc-db] schema init" (← @MonadServer.dbExecDdl IO srvInst cfg) fun () => do
    let alice (fn : String) (req := ByteArray.empty) := @DbChecks.EncVaultApi.dispatchM IO _ srvInst (RequestCtx.forUser "alice") fn req
    let some inp1 := DbChecks.SecretNoteInput.parse { body := "top-secret payload 🔐" } | c.check "[enc-db] parse inp1" false; return
    let some inp2 := DbChecks.SecretNoteInput.parse { body := "updated secret 🔑" } | c.check "[enc-db] parse inp2" false; return
    let blob := ByteArray.mk #[1, 2, 3, 255]
    c.checkRpcDomainOk (E := DbChecks.EncVaultApi.save.Error) (α := DbChecks.EncVaultDb.entries) "[enc-db] insert row 1"
      (← alice "save" (Qed.Proto.encode ((1 : Nat), (inp1, (some blob : Option ByteArray))))) fun r1 =>
      c.check "[enc-db] insert returns plaintext" (r1.body == "top-secret payload 🔐" && r1.raw == some blob)
    c.expectOk "[enc-db] insert row 2 (same plaintext)" (← alice "save" (Qed.Proto.encode ((2 : Nat), (inp1, (none : Option ByteArray))))) fun _ => pure ()
    let rawQ := SqlQuery.select (sql!"entries") [sql!"id", sql!"body"] .litTrue (some (sql!"id", .asc)) none none
    c.expectOk "[enc-db] raw SQLite read" (← @MonadServer.dbExec IO srvInst cfg rawQ AuthToken.anonymous) fun res => do
      c.check "[enc-db] 2 raw rows stored" (res.rows.size == 2)
      match res.rows[0]?.bind (·[1]?), res.rows[1]?.bind (·[1]?) with
      | some (SqlVal.text ct1), some (SqlVal.text ct2) =>
          c.checkAll [("[enc-db] ciphertext hides plaintext", !ct1.contains "top-secret" && !ct2.contains "top-secret"),
            ("[enc-db] ciphertext satisfies derived CHECK bounds", 40 <= ct1.length && ct1.length <= 304 && 40 <= ct2.length && ct2.length <= 304),
            ("[enc-db] randomized AES-GCM nonces differ", ct1 != ct2)]
      | _, _ => c.check "[enc-db] raw body cells are TEXT" false
    c.checkProtoBy (α := Option DbChecks.EncVaultDb.entries) "[enc-db] findOne decrypts row 1" (← alice "get" (Qed.Proto.encode (1 : Nat))) (fun opt => opt.map fun r => (r.body, r.raw)) (some ("top-secret payload 🔐", some blob))
    c.checkProtoBy (α := Array DbChecks.EncVaultDb.entries) "[enc-db] select decrypts all rows" (← alice "list") (fun rs => rs.map fun r => (r.id, r.body, r.raw)) #[(1, "top-secret payload 🔐", some blob), (2, "top-secret payload 🔐", none)]
    c.checkProtoBy (α := Option DbChecks.EncVaultDb.entries) "[enc-db] updateOne re-encrypts" (← alice "edit" (Qed.Proto.encode ((1 : Nat), inp2))) (fun opt => opt.map (·.body)) (some "updated secret 🔑")
    let tamperQ := SqlQuery.update (sql!"entries") [(sql!"body", .param (.text (String.ofList (List.replicate 44 'A'))))] (.binOp .eq (.col (sql!"id")) (.param (.int 2))) []
    c.expectOk "[enc-db] raw tamper update" (← @MonadServer.dbExec IO srvInst cfg tamperQ AuthToken.anonymous) fun _ => do
      c.check "[enc-db] tampered ciphertext rejected on read" (!(← alice "get" (Qed.Proto.encode (2 : Nat))).isOk)
    let badLenQ := SqlQuery.insert (sql!"entries") [(sql!"id", .int 99), (sql!"ownerId", .text "alice"), (sql!"body", .text (String.ofList (List.replicate 308 'A'))), (sql!"note", .text (String.ofList (List.replicate 44 'A'))), (sql!"raw", .null)] []
    c.check "[enc-db] SQLite CHECK rejects oversized ciphertext" (!(← @MonadServer.dbExec IO srvInst cfg badLenQ AuthToken.anonymous).isOk)

private def runRoadmapSuite (c : TestChecker) (tmpDir : String) : IO Unit := do
  let dbPath := s!"{tmpDir}/roadmap_worker.db"
  let cfg := { DbChecks.RoadmapDb.config with endpoint := .sqlitePath dbPath, devFallback? := none, envEndpoints? := none }
  let srvInst := withRedirectedDb (.sqlitePath dbPath)
  let asUser (u fn : String) (req := ByteArray.empty) := @DbChecks.RoadmapApi.dispatchM IO _ srvInst (RequestCtx.forUser u) fn req
  c.expectOk "[roadmap] migrateDatabase creates tables" (← Native.migrateDatabase cfg) fun _ => do
    c.checkProtoBy (α := DbChecks.RoadmapDb.orgs) "[roadmap] org inserted" (← asUser "alice" "insertOrg" (Qed.Proto.encode ("org1", "Acme"))) (·.name) "Acme"
    c.checkProtoBy (α := DbChecks.RoadmapDb.projects) "[roadmap] enum roundtrip (.queued)" (← asUser "alice" "insertProject" (Qed.Proto.encode ("p1", "org1"))) (·.stage) DbChecks.DeployStage.queued
    c.expectOk "[roadmap] migrateDatabase runs backfill" (← Native.migrateDatabase cfg) fun _ => do
      c.checkProtoBy (α := Option DbChecks.RoadmapDb.projects) "[roadmap] backfill updated null note to migrated" (← asUser "alice" "getProject" (Qed.Proto.encode "p1")) (·.bind (·.note)) (some "migrated")
    c.checkProtoBy (α := DbChecks.RoadmapDb.projects) "[roadmap] upsert updated stage & note"
      (← asUser "alice" "upsertBuilding" (Qed.Proto.encode ("p1", ("org1", (some "v2" : Option String)))))
      (fun p => (p.stage, p.note)) (DbChecks.DeployStage.building, some "v2")
    c.check "[roadmap] conflict where filtered out bob's hijack upsert" (!(← asUser "bob" "upsertBuilding" (Qed.Proto.encode ("p1", ("org1", (some "hijack" : Option String))))).isOk)
    c.checkProtoBy (α := Option DbChecks.RoadmapDb.projects) "[roadmap] updateOne promoted project to live" (← asUser "alice" "promoteToLive" (Qed.Proto.encode "p1")) (·.map (·.stage)) (some DbChecks.DeployStage.live)
    c.checkProto (α := Nat) "[roadmap] alice live count == 1" (← asUser "alice" "countLive") 1
    c.checkProto (α := Nat) "[roadmap] bob live count == 0 (RLS)" (← asUser "bob" "countLive") 0
    c.checkRpcDomainErr (E := DbChecks.RoadmapApi.abortTxInsertOrg.Error) (α := Bool) "[roadmap] transaction returned fail(.aborted)"
      (← asUser "alice" "abortTxInsertOrg" (Qed.Proto.encode ("org_rb", "Rolled Back"))) (·.tag == .aborted)
    c.checkProtoBy (α := Option DbChecks.RoadmapDb.orgs) "[roadmap] rollback verified" (← asUser "alice" "getOrg" (Qed.Proto.encode "org_rb")) Option.isNone true
    forList [("[roadmap] insertOrIgnore returned some", "First", some "First"), ("[roadmap] duplicate ignored", "Second", none)] fun (lbl, name, want) => do
      c.checkProtoBy (α := Option DbChecks.RoadmapDb.orgs) lbl (← asUser "alice" "idempotentOrg" (Qed.Proto.encode ("org_ign", name))) (·.map (·.name)) want
    c.checkProtoBy (α := DbChecks.RoadmapDb.services) "[roadmap] registerService Field roundtrip" (← asUser "alice" "registerService" (Qed.Proto.encode ("web", (8080 : Nat)))) (·.port.val) 8080
    c.expectOk "[roadmap] insert scaling row for atomic +=" (← asUser "alice" "insertScaling" (Qed.Proto.encode ("s1", ((1 : Nat), (2 : Nat))))) fun _ => do
      c.checkProtoBy (α := Option DbChecks.RoadmapDb.scaling) "[roadmap] maxInstances incremented atomically" (← asUser "alice" "bumpScalingMax" (Qed.Proto.encode ("s1", (5 : Nat)))) (·.map (·.maxInstances)) (some 7)
      c.checkProtoBy (α := Option DbChecks.RoadmapDb.scaling) "[roadmap] maxInstances decremented atomically" (← asUser "alice" "decScalingMax" (Qed.Proto.encode ("s1", (3 : Nat)))) (·.map (·.maxInstances)) (some 4)
    c.checkProto (α := Nat) "[roadmap] deleted 1 row" (← asUser "alice" "deleteProject" (Qed.Proto.encode "p1")) 1

private def runKeyRotationAndMetaSuite (c : TestChecker) (tmpDir : String) : IO Unit := do
  let dbPath := s!"{tmpDir}/rotating_vault.db"
  let (envRef, decCountRef) := (← IO.mkRef [("VAULT_PRIMARY_KEY", "key-v1-initial-material-32bytes!")], ← IO.mkRef 0)
  let srvInst := withMockEnvInst (withRedirectedDb (.sqlitePath dbPath)) (fun v => return (← envRef.get).lookup v) (onDecrypt? := some (decCountRef.modify (· + 1)))
  let cfg := DbChecks.RotatingVaultDb.config
  c.expectOk "[enc-rot] schema init" (← @MonadServer.dbExecDdl IO srvInst cfg) fun () => do
    let alice (fn : String) (req := ByteArray.empty) := @DbChecks.RotatingVaultApi.dispatchM IO _ srvInst (RequestCtx.forUser "alice") fn req
    forList [((1 : Nat), "stripe-live", "sk_live_alpha"), (2, "github-pat", "ghp_beta")] fun (id, label, sec) => do
      c.expectOk s!"[enc-rot] save row {id} under K1" (← alice "save" (Qed.Proto.encode (id, (label, sec)))) fun _ => pure ()
    envRef.set []; decCountRef.set 0
    c.checkProtoBy (α := Array DbChecks.RotatingVaultDb.entries.Meta) "[enc-meta] selectMeta succeeds without encryption key" (← alice "listMeta") (·.map fun m => (m.id, m.label)) #[(1, "stripe-live"), (2, "github-pat")]
    c.checkProtoBy (α := Option DbChecks.RotatingVaultDb.entries.Meta) "[enc-meta] findOneMeta succeeds without encryption key" (← alice "getMeta" (Qed.Proto.encode (2 : Nat))) (·.map (·.label)) (some "github-pat")
    c.checkProto (α := Array (Nat × String)) "[enc-meta] select(columns = [id, label]) succeeds without key" (← alice "listLabels") #[(1, "stripe-live"), (2, "github-pat")]
    c.checkProto (α := Option String) "[enc-meta] findOne(columns = [label]) succeeds without key" (← alice "getLabel" (Qed.Proto.encode (1 : Nat))) (some "stripe-live")
    c.checkEq "[enc-meta] ZERO aeadDecrypt calls across all metadata projections" (← decCountRef.get) 0
    envRef.set [("VAULT_PREV_KEY", "key-v1-initial-material-32bytes!")]
    c.check "[enc-rot] missing primary key fails closed even when prevKey is set" (!(← alice "get" (Qed.Proto.encode (1 : Nat))).isOk)
    envRef.set [("VAULT_PRIMARY_KEY", "key-v2-rotated-material-32bytes!"), ("VAULT_PREV_KEY", "key-v1-initial-material-32bytes!")]
    c.checkProtoBy (α := Option DbChecks.RotatingVaultDb.entries) "[enc-rot] K1 row 1 decrypts via prevKeys fallback" (← alice "get" (Qed.Proto.encode (1 : Nat))) (·.map (·.secret)) (some "sk_live_alpha")
    c.checkProtoBy (α := Option DbChecks.RotatingVaultDb.entries) "[enc-rot] updateOne re-encrypts row 1 under K2" (← alice "rotateValue" (Qed.Proto.encode ((1 : Nat), "sk_live_alpha_v2"))) (·.map (·.secret)) (some "sk_live_alpha_v2")
    envRef.set [("VAULT_PRIMARY_KEY", "key-v2-rotated-material-32bytes!")]
    c.checkProtoBy (α := Option DbChecks.RotatingVaultDb.entries) "[enc-rot] rotated row 1 reads with K2 alone" (← alice "get" (Qed.Proto.encode (1 : Nat))) (·.map (·.secret)) (some "sk_live_alpha_v2")
    c.check "[enc-rot] unrotated K1 row 2 fails once K1 removed" (!(← alice "get" (Qed.Proto.encode (2 : Nat))).isOk)

private def runMultiTenantCrossTableSuite (c : TestChecker) (tmpDir : String) : IO Unit := do
  let srvInst := withRedirectedDb (.sqlitePath s!"{tmpDir}/multi_tenant.db")
  c.expectOk "[cross-rls] schema init" (← @MonadServer.dbExecDdl IO srvInst DbChecks.MultiTenantDb.config) fun () => do
    let asUser (u fn : String) (req := ByteArray.empty) := @DbChecks.MultiTenantApi.dispatchM IO _ srvInst (RequestCtx.forUser u) fn req
    forList [("alice", "app1", "Alpha", none), ("alice", "app2", "Beta Org", some "org1"), ("bob", "app3", "Bob Private", none)] fun (u, id, name, orgId) => do
      c.expectOk s!"[cross-rls] {u} creates {id}" (← asUser u "createApp" (Qed.Proto.encode (id, (name, orgId)))) fun _ => pure ()
    forList [("m1", "app1", "charlie", "admin", "accepted"), ("m2", "app1", "dave", "viewer", "accepted"), ("m3", "app1", "eve", "admin", "pending")] fun (id, appId, u, role, status) => do
      c.expectOk s!"[cross-rls] add {u} ({status} {role}) on {appId}" (← asUser "alice" "addMember" (Qed.Proto.encode (id, (appId, (u, (role, status)))))) fun _ => pure ()
    c.expectOk "[cross-rls] add frank in org1" (← asUser "alice" "addOrgMember" (Qed.Proto.encode ("om1", ("org1", "frank")))) fun _ => pure ()
    forList [("alice sees own app1, app2", "alice", #["app1", "app2"]), ("charlie sees shared app1", "charlie", #["app1"]),
        ("dave sees shared app1", "dave", #["app1"]), ("eve (pending) sees nothing", "eve", #[]),
        ("frank (org1) sees org app2", "frank", #["app2"]), ("bob sees only own app3", "bob", #["app3"]), ("outsider sees nothing", "mallory", #[])] fun (tag, u, want) => do
      c.checkProtoBy (α := Array DbChecks.MultiTenantDb.apps) s!"[cross-rls] {tag}" (← asUser u "listAccessibleApps") (·.map (·.id)) want
    c.checkProtoBy (α := Array DbChecks.MultiTenantDb.apps) "[cross-rls] listSharedApps for charlie returns [app1]" (← asUser "charlie" "listSharedApps") (·.map (·.id)) #["app1"]
    forList [("dave (viewer) cannot rename app1", "dave", "renameAppAsAdmin", "Hacked", none),
        ("eve (pending admin) cannot rename app1", "eve", "renameAppAsAdmin", "PendingHack", none),
        ("charlie (accepted admin) renames app1 via role in [owner, admin]", "charlie", "renameAppAsAdmin", "Alpha v2", some "Alpha v2"),
        ("charlie renames app1 via role == admin", "charlie", "renameAppAsSpecificAdmin", "Alpha v3", some "Alpha v3")] fun (tag, u, fn, newName, want) => do
      c.checkProtoBy (α := Option DbChecks.MultiTenantDb.apps) s!"[cross-rls] {tag}" (← asUser u fn (Qed.Proto.encode ("app1", newName))) (·.map (·.name)) want
    -- Cross-table `policy insert` (unguarded owner, guarded admin/bare/nested/row/insertOrIgnore/encrypted)
    c.expectOk "[cross-rls-ins] alice (owner) deploys without guard" (← asUser "alice" "deployAsOwner" (Qed.Proto.encode ("d_own", ("app1", "owner-v1")))) fun _ => pure ()
    c.expectOk "[cross-rls-ins] charlie (admin) deploys via cross-table where" (← asUser "charlie" "deployAsAdmin" (Qed.Proto.encode ("d_adm", ("app1", ("alice", "admin-v1"))))) fun _ => pure ()
    c.expectOk "[cross-rls-ins] charlie (admin) deploys via bare where" (← asUser "charlie" "deployAsAdminBareWhere" (Qed.Proto.encode ("d_bare", ("app1", ("alice", "bare-v1"))))) fun _ => pure ()
    c.expectOk "[cross-rls-ins] charlie (admin) deploys via row struct" (← asUser "charlie" "deployRowAsAdmin" (Qed.Proto.encode ({ id := "d_row", appId := "app1", ownerId := "alice", label := "row-v1", active := true : DbChecks.MultiTenantDb.deployments }))) fun _ => pure ()
    forList [("dave (viewer) rejected 403 on deployAsAdmin", "dave", "deployAsAdmin", "d_v", "app1"),
        ("eve (pending admin) rejected 403 on deployAsAdmin", "eve", "deployAsAdmin", "d_p", "app1"),
        ("mallory (outsider) rejected 403 on deployAsOrgMember", "mallory", "deployAsOrgMember", "d_m", "app2"),
        ("frank (org1) rejected 403 on non-org app1", "frank", "deployAsOrgMember", "d_f1", "app1")] fun (tag, u, fn, depId, appId) => do
      match ← asUser u fn (Qed.Proto.encode (depId, (appId, ("alice", "denied")))) with
      | .error e => c.check s!"[cross-rls-ins] {tag}" (e.code == 403) s!"expected 403, got {e.code}: {e.message}"
      | .ok _ => c.check s!"[cross-rls-ins] {tag}" false "expected 403 error, got ok"
    c.expectOk "[cross-rls-ins] frank (org1) deploys on app2 via nested any" (← asUser "frank" "deployAsOrgMember" (Qed.Proto.encode ("d_org", ("app2", ("alice", "org-v1"))))) fun _ => pure ()
    c.checkProtoBy (α := Option DbChecks.MultiTenantDb.deployments) "[cross-rls-ins] charlie insertOrIgnore inserts first time" (← asUser "charlie" "deployIdempotentAsAdmin" (Qed.Proto.encode ("d_ign", ("app1", ("alice", "ign-v1"))))) (·.map (·.id)) (some "d_ign")
    c.checkProtoBy (α := Option DbChecks.MultiTenantDb.deployments) "[cross-rls-ins] charlie insertOrIgnore duplicate returns none" (← asUser "charlie" "deployIdempotentAsAdmin" (Qed.Proto.encode ("d_ign", ("app1", ("alice", "ign-v1"))))) (·.map (·.id)) none
    c.checkProtoBy (α := Option DbChecks.MultiTenantDb.deployments) "[cross-rls-ins] dave (viewer) insertOrIgnore returns none without inserting" (← asUser "dave" "deployIdempotentAsAdmin" (Qed.Proto.encode ("d_ign_bad", ("app1", ("alice", "ign-bad"))))) (·.map (·.id)) none
    c.checkProtoBy (α := Array DbChecks.MultiTenantDb.deployments) "[cross-rls-ins] app1 has exactly 5 authorized deployments" (← asUser "alice" "listDeployments" (Qed.Proto.encode "app1")) (·.map (·.id)) #["d_adm", "d_bare", "d_ign", "d_own", "d_row"]
    c.checkProtoBy (α := Array DbChecks.MultiTenantDb.deployments) "[cross-rls-ins] app2 has exactly 1 org deployment" (← asUser "alice" "listDeployments" (Qed.Proto.encode "app2")) (·.map (·.id)) #["d_org"]
    c.expectOk "[cross-rls-ins] charlie (admin) inserts encrypted app_secret" (← asUser "charlie" "createSecretAsAdmin" (Qed.Proto.encode ("s1", ("app1", ("alice", "sk_live_cross_table"))))) fun _ => pure ()
    match ← asUser "dave" "createSecretAsAdmin" (Qed.Proto.encode ("s2", ("app1", ("alice", "sk_denied")))) with
    | .error e => c.check "[cross-rls-ins] dave (viewer) rejected 403 on encrypted app_secret" (e.code == 403) s!"expected 403, got {e.code}"
    | .ok _ => c.check "[cross-rls-ins] dave (viewer) rejected 403 on encrypted app_secret" false "expected 403"
    c.checkProtoBy (α := Array DbChecks.MultiTenantDb.app_secrets) "[cross-rls-ins] encrypted secret roundtrips cleanly" (← asUser "charlie" "listSecrets" (Qed.Proto.encode "app1")) (·.map fun s => (s.id, s.secret)) #[("s1", "sk_live_cross_table")]
    match ← Prim.sqliteExec s!"{tmpDir}/multi_tenant.db" "SELECT \"secret\" FROM \"app_secrets\" WHERE \"id\" = ?1" #[.text "s1"] with
    | .ok r => c.check "[cross-rls-ins] encrypted secret ciphertext on disk != plaintext" (match r.rows[0]?.bind (·[0]?) with | some (SqlVal.text ct) => ct != "sk_live_cross_table" && ct.length >= 40 | _ => false)
    | .error e => c.check "[cross-rls-ins] raw sqlite inspect secret" false e

private def runCloudPolicySuite (c : TestChecker) (tmpDir : String) : IO Unit := do
  let srvInst := withRedirectedDb (.sqlitePath s!"{tmpDir}/cloud_policy.db")
  c.expectOk "[cloud-pol] schema init" (← @MonadServer.dbExecDdl IO srvInst DbChecks.CloudPolicyDb.config) fun () => do
    let asUser (u fn : String) (req := ByteArray.empty) := @DbChecks.CloudPolicyApi.dispatchM IO _ srvInst (RequestCtx.forUser u) fn req
    forList [("alice", "alice@qed.dev", 5000, false), ("bob", "bob@qed.dev", 2000, false),
        ("charlie", "charlie@qed.dev", 0, false), ("dave", "dave@qed.dev", 0, false), ("op1", "op@qed.dev", 0, true)] fun (id, email, cap, isOp) => do
      c.expectOk s!"[cloud-pol] seed account {id}" (← asUser id "seedAccount" (Qed.Proto.encode (id, (email, (cap, isOp))))) fun _ => pure ()
    forList [("a1", "Alpha"), ("a2", "Beta")] fun (id, name) => do
      c.expectOk s!"[cloud-pol] alice creates {id}" (← asUser "alice" "createApp" (Qed.Proto.encode (id, name))) fun _ => pure ()
    forList [("m1", "a1", "charlie", "admin", "accepted"), ("m2", "a1", "dave", "viewer", "accepted")] fun (id, appId, u, role, status) => do
      c.expectOk s!"[cloud-pol] add member {u}" (← asUser "alice" "addMember" (Qed.Proto.encode (id, (appId, (u, (role, status)))))) fun _ => pure ()
    c.expectOk "[cloud-pol] add db1 on a1" (← asUser "charlie" "addAppDb" (Qed.Proto.encode ("db1", ("a1", ("alice", true))))) fun _ => pure ()
    c.expectOk "[cloud-pol] add db2 on a2" (← asUser "alice" "addAppDb" (Qed.Proto.encode ("db2", ("a2", ("alice", true))))) fun _ => pure ()
    c.expectOk "[cloud-pol] add secret on a1" (← asUser "charlie" "addSecret" (Qed.Proto.encode ("s1", ("a1", ("alice", ("STRIPE_KEY", "sk_live_123")))))) fun _ => pure ()
    c.checkProtoBy (α := Option (String × String)) "[cloud-pol] lookupUserIdByEmail resolves bob" (← asUser "dave" "lookupUserIdByEmail" (Qed.Proto.encode "bob@qed.dev")) id (some ("bob", "bob@qed.dev"))
    c.checkProtoBy (α := Option (String × Nat)) "[cloud-pol] collaborator dave reads alice spendCap" (← asUser "dave" "getOwnerSpendCap" (Qed.Proto.encode "alice")) id (some ("alice", 5000))
    c.checkProtoBy (α := Option (String × Nat)) "[cloud-pol] outsider bob gets none for alice spendCap" (← asUser "bob" "getOwnerSpendCap" (Qed.Proto.encode "alice")) id none
    c.checkProtoBy (α := Nat) "[cloud-pol] collaborator dave counts all 2 of alice managed dbs" (← asUser "dave" "countOwnerManagedDbs" (Qed.Proto.encode "alice")) id 2
    c.checkProtoBy (α := Nat) "[cloud-pol] outsider bob counts 0 of alice managed dbs" (← asUser "bob" "countOwnerManagedDbs" (Qed.Proto.encode "alice")) id 0
    c.checkProtoBy (α := Array DbChecks.CloudPolicyDb.app_secrets.Meta) "[cloud-pol] viewer dave reads secret metadata" (← asUser "dave" "listSecretMeta" (Qed.Proto.encode "a1")) (·.map (·.label)) #["STRIPE_KEY"]
    c.checkProtoBy (α := Option DbChecks.CloudPolicyDb.apps) "[cloud-pol] admin charlie renames a1" (← asUser "charlie" "renameApp" (Qed.Proto.encode ("a1", "Alpha Renamed"))) (·.map (·.name)) (some "Alpha Renamed")
    c.checkProtoBy (α := Option DbChecks.CloudPolicyDb.apps) "[cloud-pol] alice transfers a1 to bob" (← asUser "alice" "transferApp" (Qed.Proto.encode ("a1", "bob"))) (·.map (·.ownerId)) (some "bob")
    c.checkProtoBy (α := Option DbChecks.CloudPolicyDb.apps) "[cloud-pol] operator suspends a2" (← asUser "op1" "operatorSuspendApp" (Qed.Proto.encode ("a2", true))) (·.map (·.suspended)) (some true)
    c.checkProtoBy (α := Option DbChecks.CloudPolicyDb.apps) "[cloud-pol] non-operator dave cannot suspend a2" (← asUser "dave" "operatorSuspendApp" (Qed.Proto.encode ("a2", false))) (·.map (·.suspended)) none
    c.checkProtoBy (α := Array DbChecks.CloudPolicyDb.accounts) "[cloud-pol] operator lists all 5 accounts" (← asUser "op1" "listAllAccountsAsOp") (·.size) 5
    c.checkProtoBy (α := Array DbChecks.CloudPolicyDb.accounts) "[cloud-pol] non-operator lists 0 accounts" (← asUser "dave" "listAllAccountsAsOp") (·.size) 0
    c.check "[cloud-pol] rlsDdl expands database fn into SQL EXISTS" (DbChecks.CloudPolicyDb.rlsDdl.contains "EXISTS (SELECT 1 FROM \"app_members\" AS \"m_f")

private def runPrincipalSuite (c : TestChecker) (tmpDir : String) : IO Unit := do
  let dbPath := s!"{tmpDir}/principal.db"
  let envRef ← IO.mkRef ([] : List (String × String))
  let srvInst := withMockEnvInst (withRedirectedDb (.sqlitePath dbPath)) (fun v => return (← envRef.get).lookup v)
  let atomicInst : MonadAtomic Unit IO := Native.withStateBox (← Prim.mkStateBox ())
  let postRoute (path body : String) (hdrs : List (String × String) := []) :=
    @DbChecks.PrincipalApi.httpDispatchM IO _ srvInst { headers := hdrs, body } "POST" path
  let hmacHex (key msg : String) : IO String := return Qed.Proto.encodeHex (← Prim.hmacSha256 key.toUTF8 msg.toUTF8)
  c.expectOk "[principal] schema init" (← @MonadServer.dbExecDdl IO srvInst DbChecks.PrincipalDb.config) fun () => do
    c.checkErrCode "[principal] Stripe webhook 500 when secret unset" (← postRoute "/webhooks/stripe" "{}") 500
    let (stripeSec, ghSec, cronSec, bearerSec) := ("whsec_live_test", "ghsec_live_test", "cron_live_secret", "bearer_live_secret")
    envRef.set [("TEST_STRIPE_WH_SECRET", stripeSec), ("TEST_GITHUB_WH_SECRET", ghSec), ("TEST_CRON_SECRET", cronSec), ("TEST_BEARER_SECRET", bearerSec)]
    let nowS := (← Prim.nowMs).toNat / 1000
    let stripeBody := "{\"type\":\"invoice.paid\"}"
    let goodStripeSig ← hmacHex stripeSec s!"{nowS}.{stripeBody}"
    let oldTs := if nowS > 600 then nowS - 600 else 0
    let expiredStripeSig ← hmacHex stripeSec s!"{oldTs}.{stripeBody}"
    c.checkErrCode "[principal] Stripe webhook 401 on bad sig" (← postRoute "/webhooks/stripe" stripeBody [("stripe-signature", s!"t={nowS},v1=0000")]) 401
    c.checkErrCode "[principal] Stripe webhook 401 on expired timestamp" (← postRoute "/webhooks/stripe" stripeBody [("stripe-signature", s!"t={oldTs},v1={expiredStripeSig}")]) 401
    c.expectOk "[principal] Stripe webhook 200 with real ring HMAC-SHA256" (← postRoute "/webhooks/stripe" stripeBody [("stripe-signature", s!"t={nowS},v1=deadbeef,v1={goodStripeSig},v2=abc==")]) fun resp? =>
      c.check "[principal] Stripe webhook returned 200" (resp?.any (·.status == 200))
    let ghBody := "{\"ref\":\"refs/heads/main\"}"
    let goodGhSig ← hmacHex ghSec ghBody
    c.checkErrCode "[principal] GitHub webhook 401 on wrong sig" (← postRoute "/webhooks/github" ghBody [("x-hub-signature-256", "sha256=" ++ String.ofList (List.replicate 64 '0'))]) 401
    c.expectOk "[principal] GitHub webhook 200 with real ring HMAC-SHA256" (← postRoute "/webhooks/github" ghBody [("x-hub-signature-256", s!"sha256={goodGhSig}")]) fun resp? =>
      c.check "[principal] GitHub webhook returned 200" (resp?.any (·.status == 200))
    let some pollJob := DbChecks.BuildJobSrv.jobs[0]? | c.check "[principal] BuildJobSrv has poll job" false; return
    let ioPoll := pollJob.toIoJob srvInst atomicInst
    c.checkOkBy "[principal] BuildJobSrv.poll claims queued deployment" (← ioPoll.runWorkOnce) id true
    c.checkOkBy "[principal] BuildJobSrv.poll returns false when queue empty" (← ioPoll.runWorkOnce) id false
    c.checkErrCode "[principal] cron/reap 401 on wrong bearer" (← postRoute "/cron/reap" "" [("authorization", "Bearer wrong")]) 401
    c.expectOk "[principal] cron/reap 200 marks building -> stale" (← postRoute "/cron/reap" "" [("authorization", s!"Bearer {bearerSec}")]) fun resp? =>
      c.check "[principal] cron/reap returned reaped:true" (resp?.any fun r => r.status == 200 && ((String.fromUTF8? r.body).getD "").contains "true")
    c.checkErrCode "[principal] cron/cleanup 401 on wrong header secret" (← postRoute "/cron/cleanup" "" [("x-qed-cron-secret", "wrong")]) 401
    c.expectOk "[principal] cron/cleanup 200 deletes stale deployment" (← postRoute "/cron/cleanup" "" [("x-qed-cron-secret", cronSec)]) fun resp? =>
      c.check "[principal] cron/cleanup returned deleted:1" (resp?.any fun r => r.status == 200 && ((String.fromUTF8? r.body).getD "").contains "\"deleted\":1")
    let rls := DbChecks.PrincipalDb.rlsDdl
    let onceRc ← try
        if !(← Native.initDatabases #[DbChecks.PrincipalDb.config]) then pure (1 : UInt32)
        else Native.runServerJobsOnly "BuildJobSrv" (some DbChecks.PrincipalDb.config) () DbChecks.BuildJobSrv.jobs ["--once"]
      finally
        for suf in ["", "-wal", "-shm"] do
          try IO.FS.removeFile s!".qed/principal_checks.db{suf}" catch _ => pure ()
    c.checkAll [
      ("[principal] runServerJobsOnly --once exits 0", onceRc == 0),
      ("[principal] Principal.toSqlTag matches RLS format", Principal.anonymous.toSqlTag == "" && (Principal.system "stripe").toSqlTag == "system:stripe" && (Principal.system "BuildJobSrv.poll").toSqlTag == "system:BuildJobSrv.poll"),
      ("[principal] rlsDdl renders ctx.principal == .system(\"stripe\")", rls.contains "(current_setting('qed.principal', true) = 'system:stripe')"),
      ("[principal] rlsDdl renders ctx.principal in [.system(...), ...]", rls.contains "(current_setting('qed.principal', true) IN ('system:BuildJobSrv.poll', 'system:reap-and-sweep'))")]

private def runRlsGateNegativeSuite (c : TestChecker) (tmpDir : String) : IO Unit := do
  let gateDir := s!"{tmpDir}/rls_gate"
  IO.FS.createDirAll gateDir
  let (qedjs, baseLp) := (← qedjsBinPath, ← getLeanPath)
  let (_, leanOut, _) ← runCmd "lake" #["env", "which", "lean"]
  let leanBin := let s := leanOut.trimAscii.toString; if s.isEmpty then "lean" else s
  let env := #[("LEAN_PATH", some s!"{gateDir}:{baseLp}")]
  let compileMod (modName src : String) : IO (UInt32 × String) := do
    let fPath := s!"{gateDir}/{modName}.lean"
    IO.FS.writeFile fPath src
    let (code, out, err) ← runCmd leanBin #["-R", gateDir, "-o", s!"{gateDir}/{modName}.olean", fPath] (cwd := some gateDir) (env := env)
    return (code, out ++ err)
  let fixtureSrc :=
    "import Qed\nopen Qed Qed.Server Qed.Server.Db\n" ++
    "database GateDb:\n  sqlite \".qed/gate.db\"\n  table notes:\n" ++
    "    id : String primary_key where 1 <= id.length <= 64\n" ++
    "    ownerId : String immutable where 1 <= ownerId.length <= 64\n" ++
    "    body : String where 1 <= body.length <= 200\n" ++
    "    policy read, write requires some(row.ownerId) == ctx.userId\n" ++
    "    policy read(id) by id requires ctx.userId != none\n" ++
    "server stateless GateSrv:\n  use db : GateDb\n  rpc okCount() -> Nat!:\n" ++
    "    requires auth\n    return await db.notes.count(where = r => r.ownerId == uid)?\n"
  let (fc, ferr) ← compileMod "RlsGateFixture" fixtureSrc
  if fc != 0 then c.check "[rls-gate] compile base fixture" false ferr; return
  let (pc, pout, perr) ← runCmd qedjs #["--verify-env", "--skip-qed", "RlsGateFixture"] (env := env)
  c.check "[rls-gate] positive control passes --verify-env" (pc == 0) (pout ++ perr)
  let hdr := "import RlsGateFixture\nopen Qed Qed.Server Qed.Server.Db\n"
  let attacks : List (String × String × String) := [
    ("direct_dbExec",
      hdr ++ "def atk {m} [Monad m] [MonadServer m] : m (Except ApiError DbResult) := MonadServer.dbExec GateDb.config (SqlQuery.count (sql!\"notes\") .litTrue)\n",
      "rls gate: forbidden server/DB/auth primitive"),
    ("direct_prim_sqlite",
      "import Qed.Server.Prim\nopen Qed.Server Qed.Server.Db\ndef atk : IO (Except String DbResult) := Prim.sqliteExec \"a.db\" \"SELECT 1\" #[]\n",
      "rls gate: forbidden server/DB/auth primitive"),
    ("direct_pgwire",
      "import Qed.Server.Db.PgWire\nopen Qed.Server.Db\ndef atk : IO (Except String DbResult) := PgWire.execParameterized \"postgres://u:p@h/d\" \"SELECT 1\" #[]\n",
      "rls gate: forbidden server/DB/auth primitive"),
    ("direct_dbRunChecked",
      hdr ++ "def atk {m} [Monad m] [MonadServer m] (ctx : RequestCtx) : m (Except ApiError DbResult) :=\n  dbRunChecked (Q := fun _ => True) GateDb.config (SqlQuery.count (sql!\"notes\") .litTrue) none .ok (fun _ => trivial) (fun _ => trivial) trivial [] [] ctx.auth\n",
      "rls gate: direct call to `Qed.Server.Db.dbRunChecked`"),
    ("spoofed_dbRunRows_True",
      hdr ++ "def atk {m} [Monad m] [MonadServer m] (ctx : RequestCtx) : m (Except ApiError (Array GateDb.notes)) :=\n  dbRunRows (P := True) GateDb.config (SqlQuery.select (sql!\"notes\") [sql!\"id\", sql!\"ownerId\", sql!\"body\"] .litTrue)\n    GateDb.notes.decodeRow GateDb.notes.RowInv GateDb.notes.rowInvBool GateDb.notes.rowInvBool_sound trivial (fun _ => true) \"err\" none [] [] ctx.auth\n",
      "does not match verified `RowInv"),
    ("vacuous_dbCount_false_pred",
      hdr ++ "def atk {m} [Monad m] [MonadServer m] (ctx : RequestCtx) : m (Except ApiError Nat) :=\n  dbCount (P := ∀ r : GateDb.notes, GateDb.notes.RowInv r → false = true → GateDb.notes.ReadPolicy ctx r)\n    GateDb.config (SqlQuery.count (sql!\"notes\") .litTrue) (fun _ _ h => absurd h (by decide)) none ctx.auth\n",
      "SQL `WHERE` predicate on `notes` does not match"),
    ("mismatched_dbInsert_pairs",
      hdr ++ "def atk {m} [Monad m] [MonadServer m] (ctx : RequestCtx) (uid : String) (hu : ctx.userId = some uid) (hl : 1 ≤ uid.length ∧ uid.length ≤ 64) : m (Except ApiError GateDb.notes) :=\n  let r : GateDb.notes := { id := \"1\", ownerId := uid, body := \"hi\" }\n  dbInsert (P := GateDb.notes.InsertPolicy ctx r) GateDb.config\n    (SqlQuery.insert (sql!\"notes\") [(sql!\"id\", ToSql.toSql r.id), (sql!\"ownerId\", .text \"victim\"), (sql!\"body\", ToSql.toSql r.body)] [])\n    r GateDb.notes.RowInv (by simp [r, GateDb.notes.RowInv, hl]; decide) (by simp [r, GateDb.notes.InsertPolicy, hu]) none [] false ctx.auth\n",
      "SQL insert column pairs on `notes` do not match verified `newRow`"),
    ("guarded_dbInsert_no_returning",
      hdr ++ "def atk {m} [Monad m] [MonadServer m] (ctx : RequestCtx) (uid : String) (hu : ctx.userId = some uid) (hl : 1 ≤ uid.length ∧ uid.length ≤ 64) : m (Except ApiError GateDb.notes) :=\n  let r : GateDb.notes := { id := \"1\", ownerId := uid, body := \"hi\" }\n  dbInsert (P := GateDb.notes.RowInv r → (r.ownerId == uid) = true → GateDb.notes.InsertPolicy ctx r) GateDb.config\n    (SqlQuery.insert (sql!\"notes\") [(sql!\"id\", ToSql.toSql r.id), (sql!\"ownerId\", ToSql.toSql r.ownerId), (sql!\"body\", ToSql.toSql r.body)] [] (some (.binOp .eq (.param (.text uid)) (.param (.text uid)))))\n    r GateDb.notes.RowInv (by simp [r, GateDb.notes.RowInv, hl]; decide) (fun _ _ => by simp [r, GateDb.notes.InsertPolicy, hu]) none [] false ctx.auth\n",
      "must set `requireReturning := true`"),
    ("unauthorized_col_proj",
      hdr ++ "def atk {m} [Monad m] [MonadServer m] (ctx : RequestCtx) (h : ctx.userId ≠ none) : m (Except ApiError (Option String)) :=\n  dbFindOneProj (P := ∀ r : GateDb.notes, GateDb.notes.RowInv r → (r.id == \"1\") = true → GateDb.notes.ColReadPolicy_0 ctx r)\n    GateDb.config (SqlQuery.select (sql!\"notes\") [sql!\"body\"] (.binOp .eq (.col (sql!\"id\")) (.param (.text \"1\"))) none (some 1))\n    (fun _ => .ok \"\") (fun _ _ _ => h) none [] ctx.auth\n",
      "column `body` is not authorized by `GateDb.notes.ColReadPolicy_0`"),
    ("multirow_by_col_proj",
      hdr ++ "def atk {m} [Monad m] [MonadServer m] (ctx : RequestCtx) (h : ctx.userId ≠ none) : m (Except ApiError (Array String)) :=\n  dbSelectProj (P := ∀ r : GateDb.notes, GateDb.notes.RowInv r → (r.id == \"1\") = true → GateDb.notes.ColReadPolicy_0 ctx r)\n    GateDb.config (SqlQuery.select (sql!\"notes\") [sql!\"id\"] (.binOp .eq (.col (sql!\"id\")) (.param (.text \"1\"))))\n    (fun _ => .ok \"\") (fun _ _ _ => h) none [] ctx.auth\n",
      "with `by` columns requires `findOne`"),
    ("anonymous_auth_on_dbCount",
      hdr ++ "def atk {m} [Monad m] [MonadServer m] (ctx : RequestCtx) (uid : String) (hu : ctx.userId = some uid) : m (Except ApiError Nat) :=\n  dbCount (P := ∀ r : GateDb.notes, GateDb.notes.RowInv r → (r.ownerId == uid) = true → GateDb.notes.ReadPolicy ctx r)\n    GateDb.config (SqlQuery.count (sql!\"notes\") (.binOp .eq (.col (sql!\"ownerId\")) (.param (.text uid))))\n    (fun r _ heq => by simp [GateDb.notes.ReadPolicy, hu, beq_iff_eq.mp heq]) none AuthToken.anonymous\n",
      "`auth` must be `ctx.auth`"),
    ("forged_forUser",
      hdr ++ "def atk : RequestCtx := RequestCtx.forUser \"victim\"\n",
      "rls gate: forbidden server/DB/auth primitive"),
    ("forged_ofPrincipal",
      hdr ++ "def atk : AuthToken := AuthToken.ofPrincipal (.system \"stripe\")\n",
      "rls gate: forbidden server/DB/auth primitive"),
    ("forged_verifyRouteAuth",
      hdr ++ "def atk {m} [Monad m] [MonadServer m] (ctx : RequestCtx) : m (Except ApiError { c : RequestCtx // c.principal = .system \"stripe\" }) :=\n  verifyRouteAuth (.system \"stripe\") (.bearerSecret \"hardcoded\") ctx\n",
      "is forbidden outside `<Server>.httpDispatchM`"),
    ("forged_mkSystem_job",
      hdr ++ "def atk : ServerJob Unit := ServerJob.mkSystem \"OtherSrv\" \"poll\" 1000 (by decide) (fun _ _ => pure (.ok ()))\n",
      "is forbidden outside `<Server>.jobs`"),
    ("forged_DbConfig_mk",
      hdr ++ "def atk : DbConfig := { name := \"Fake\", endpoint := .sqlitePath \"x.db\" }\n",
      "`DbConfig.mk` is forbidden outside `<Db>.config`"),
    ("custom_MonadServer_inst",
      hdr ++ "set_option warn.classDefReducibility false in\ndef atk (x : MonadServer Id) : MonadServer Id := x\n",
      "custom `Qed.Server.MonadServer` instance"),
    ("direct_ServerJob_runM",
      hdr ++ "def atk {m} [Monad m] [MonadServer m] [MonadAtomic Unit m] (j : ServerJob Unit) : m (Except ApiError Unit) := j.runM\n",
      "rls gate: forbidden server/DB/auth primitive")
  ]
  runTasks <| attacks.zipIdx.map fun ((tag, src, wantErr), idx) => do
    let modName := s!"RlsGateAtk{idx}"
    let (cc, cerr) ← compileMod modName src
    if cc != 0 then
      c.check s!"[rls-gate] compile attack `{tag}`" false cerr
    else
      let (vc, vout, verr) ← runCmd qedjs #["--verify-env", "--skip-qed", modName] (env := env)
      let combined := vout ++ verr
      c.check s!"[rls-gate] rejects `{tag}`" (vc != 0 && combined.contains wantErr) s!"exit={vc}, out={combined.take 240}"

rollback_env qedServerMain DbChecks.BuildJobSrv
rollback_env qedServerMain DbChecks.PrincipalApi

def run : IO Bool := do
  let c ← mkChecker "database"
  withDevApp c "QedTests.DbChecks" fun dir => do
    let authSecret := "db-test-hmac-secret-key"; let (aliceTok, bobTok) := (← signSessionToken authSecret "alice", ← signSessionToken authSecret "bob")
    let dbEnv (url : String) := #[("QED_WORKERS", some "2"), ("QED_AUTH_SECRET", some authSecret), ("QED_TEST_DB_URL", some url)]
    withTempDir "qed-db-native" fun tmpDir =>
      runTasks [
        checkLeakGate c "QedTests.DbChecks" #["DbChecks.VaultDb.config", "DbChecks.VaultDb.secrets", "DbChecks.VaultDb.ensureSchema", "DbChecks.VaultDb.ddl", "DbChecks.VaultDb.rlsDdl", "DbChecks.VaultApi.dispatchM", "DbChecks.VaultApi.createNote_handler"],
        runMovedDbChecks c,
        withNativeServer c "[sqlite] native server healthy" dir (dbEnv s!"sqlite://{tmpDir}/vault.db") (dev := true) fun srv => runVaultSuite c "sqlite" srv aliceTok bobTok (testRestart := true),
        withMockServer c "[http-sql] start mock" (startHttpSqlMock s!"{tmpDir}/http_mock.db") (·.stop) fun httpMock =>
          withNativeServer c "[http-sql] native server healthy" dir (dbEnv httpMock.url) (dev := true) fun srv => do
            runVaultSuite c "http-sql" srv aliceTok bobTok; let seen ← httpMock.seenSqlRef.get
            c.checkAll [("[http-sql] SQLi payload NEVER interpolated into SQL", !(seen.any fun (s, _) => s.contains "DROP TABLE")),
              ("[http-sql] parameterized SQL sent with bound params", seen.any fun (s, n) => s.contains "?" && n > 0)],
        withMockServer c "[pg-wire] start mock" (startPgWireMock s!"{tmpDir}/pg_mock.db" "qeduser" "qedpass" "qeddb") (·.stop) fun pgMock =>
          withNativeServer c "[pg-wire] native server healthy" dir (dbEnv pgMock.url) (dev := true) fun srv => do
            runVaultSuite c "pg-wire" srv aliceTok bobTok
            let (scramCnt, parsed, rlsDdls, sessVars) := (← pgMock.scramCountRef.get, ← pgMock.parsedSqlRef.get, ← pgMock.rlsDdlRef.get, ← pgMock.sessionVarsRef.get)
            let allRls := String.intercalate "\n" rlsDdls.toList
            c.checkAll [("[pg-wire] StartupMessage sent expected user & db", ← pgMock.startupOkRef.get),
              ("[pg-wire] SCRAM-SHA-256 proof verified", scramCnt > 0),
              (s!"[pg-wire] connection pool reused authenticated sockets (scram={scramCnt}, queries={parsed.size})", scramCnt < parsed.size && scramCnt <= 6),
              ("[pg-wire] SQLi payload NEVER interpolated into Parse SQL", !(parsed.any (·.contains "DROP TABLE"))),
              ("[pg-wire] Parse used $1 placeholders with Bind params", parsed.any (·.contains "$1")),
              ("[pg-wire] migrateDatabase applied ENABLE+FORCE RLS & 4-op policies", hasAll allRls ["ENABLE ROW LEVEL SECURITY", "FORCE ROW LEVEL SECURITY", "FOR SELECT", "FOR INSERT", "FOR UPDATE", "FOR DELETE"]),
              ("[pg-wire] queries set qed.user_id and qed.principal session vars for alice & bob", sessVars.contains ("alice", "user:alice") && sessVars.contains ("bob", "user:bob"))],
        runShopDirectSuite c "sqlite-direct" (withRedirectedDb (.sqlitePath s!"{tmpDir}/shop_direct.db")) (testConcurrentReaders := true),
        runEncryptedColumnSuite c (withRedirectedDb (.sqlitePath s!"{tmpDir}/enc_vault.db")),
        runKeyRotationAndMetaSuite c tmpDir,
        runMultiTenantCrossTableSuite c tmpDir,
        runCloudPolicySuite c tmpDir,
        runPrincipalSuite c tmpDir,
        runMigrationSuite c tmpDir,
        runRoadmapSuite c tmpDir,
        runRlsGateNegativeSuite c tmpDir,
        withMockServer c "[pg-shop] start mock" (startPgWireMock s!"{tmpDir}/shop_pg_mock.db" "shopuser" "shoppass" "shopdb") (fun m => do Db.PgWire.clearPool; m.stop) fun shopPgMock => do
          let ssrfRes ← Db.PgWire.execParameterized shopPgMock.url "SELECT 1" #[] (ssrfGuard := true)
          c.check "[pg-ssrf] dynamic postgresUrl SSRF guard rejects loopback 127.0.0.1" (match ssrfRes with | .error _ => true | .ok _ => false) "expected SSRF rejection"
          let pgShopInst := withRedirectedDb (.postgresUrl shopPgMock.url (ssrfGuard := false))
          runShopDirectSuite c "pg-direct" pgShopInst
          let (scramCnt, parsed, shopRlsDdls, shopSessVars) := (← shopPgMock.scramCountRef.get, ← shopPgMock.parsedSqlRef.get, ← shopPgMock.rlsDdlRef.get, ← shopPgMock.sessionVarsRef.get)
          let allShopRls := String.intercalate "\n" shopRlsDdls.toList
          c.checkAll [
            (s!"[pg-direct] connection pool reused sockets across tx & queries (scram={scramCnt}, queries={parsed.size})", scramCnt > 0 && scramCnt <= 3 && parsed.size >= 10),
            ("[pg-direct] migrateDatabase applied ENABLE+FORCE RLS & 4-op policies", hasAll allShopRls ["ENABLE ROW LEVEL SECURITY", "FORCE ROW LEVEL SECURITY", "FOR SELECT", "FOR INSERT", "FOR UPDATE", "FOR DELETE"]),
            ("[pg-direct] standalone & tx queries set session RLS vars for alice & bob", shopSessVars.contains ("alice", "user:alice") && shopSessVars.contains ("bob", "user:bob"))]
          let shopBox ← Prim.mkStateBox DbChecks.ShopApi.initState
          let shopAtomic : MonadAtomic DbChecks.ShopApi.State IO := Native.withStateBox shopBox
          let shopAlice (fn : String) (req := ByteArray.empty) := @DbChecks.ShopApi.dispatchM IO _ pgShopInst shopAtomic (RequestCtx.forUser "alice") fn req
          let _ ← shopAlice "insertAuthorOrIgnore" (Qed.Proto.encode ("pg_25p02_a", "Author"))
          let abortedTxRes ← shopAlice "abortedDupAuthorTx" (Qed.Proto.encode "pg_25p02_a")
          c.check "[pg-25p02] COMMIT on aborted Postgres tx returns error (never silent .ok)" (!abortedTxRes.isOk) "expected finishPgTx error on aborted tx"
          c.checkProtoBy (α := Option DbChecks.ShopDb.authors) "[pg-25p02] insertOrIgnore inside Postgres tx commits cleanly & ignores dup"
            (← shopAlice "txInsertAuthorOrIgnore" (Qed.Proto.encode ("pg_25p02_a", "dup-ignored"))) Option.isNone true
          withMockServer c "[pg-ext-lock] start external mock" (startPgWireMock s!"{tmpDir}/ext_pg_mock.db" "extuser" "extpass" "extdb") (·.stop) fun extPgMock => do
            discard <| Prim.sqliteDdl s!"{tmpDir}/ext_pg_mock.db" "CREATE TABLE IF NOT EXISTS \"ext_items\" (\"id\" TEXT PRIMARY KEY)"
            let rawInst := Native.mkNativeServerInst none none
            let rSelf ← @PgHandle.queryReadOnly IO _ rawInst (PgHandle.connect shopPgMock.url (ssrfGuard := false)) (SqlQuery.count (sql!"authors") .litTrue) rfl
            let rLocalhost ← @PgHandle.queryReadOnly IO _ rawInst (PgHandle.connect (shopPgMock.url.replace "127.0.0.1" "localhost") (ssrfGuard := false)) (SqlQuery.count (sql!"authors") .litTrue) rfl
            let rExt ← @PgHandle.queryReadOnly IO _ rawInst (PgHandle.connect extPgMock.url (ssrfGuard := false)) (SqlQuery.count (sql!"ext_items") .litTrue) rfl
            c.checkAll [
              ("[pg-app-lock] Db.postgres/PgHandle targeting app DB rejected with 403", match rSelf with | .error e => e.code == 403 && e.message.contains "application-owned database" | .ok _ => false),
              ("[pg-app-lock] Db.postgres/PgHandle localhost alias to app DB rejected with 403", match rLocalhost with | .error e => e.code == 403 && e.message.contains "application-owned database" | .ok _ => false),
              ("[pg-app-lock] Db.postgres/PgHandle targeting separate external DB succeeds", rExt.isOk),
              ("[pg-app-lock] external PgHandle bypasses app RLS set_config", (← extPgMock.sessionVarsRef.get).isEmpty)]
          let devFallbackCfg : DbConfig := {
            name := "DevOverrideDb", endpoint := .urlEnv "QED_DEV_TEST_DB_URL", devFallback? := some (.sqlitePath ".qed/fallback.db"),
            envEndpoints? := some { prod := .urlEnv "QED_DEV_TEST_DB_URL", staging := .urlEnv "QED_DEV_TEST_DB_URL", preview := .urlEnv "QED_DEV_TEST_DB_URL", dev := .sqlitePath ".qed/fallback.db" } }
          let resFallback ← Native.resolveDbConfigCore (some "dev") false devFallbackCfg
          let resExplicit ← Native.resolveDbConfigCore (some "dev") false { devFallbackCfg with endpoint := .urlEnv "HOME" }
          c.checkAll [
            ("[db-resolve] QED_DEPLOY_ENV=dev uses dev sqlite when primary env unset", match resFallback with | .ok (.sqlite ".qed/fallback.db") => true | _ => false),
            ("[db-resolve] QED_DEPLOY_ENV=dev honors explicitly set primary env var over dev sqlite", match resExplicit with | .error e => e.message.contains "unrecognized database URL scheme" | _ => false)]]
  c.finish

end QedTests.Native.Database
