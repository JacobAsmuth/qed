import Qed.Server.Core

namespace Qed.Server.Eval
open Qed Qed.Server Qed.Server.Db

/-! ## Pure Kernel-Reducible `ThreadProg` & In-Memory SQL Evaluator (`Qed.Server.Eval`) -/

private def prngBytesAux (seed : Nat) : Nat → List UInt8 → List UInt8
  | 0, acc => acc.reverse | n + 1, acc => prngBytesAux (seed + 1) n (UInt8.ofNat ((seed * 31 + n * 17 + 7) % 256) :: acc)
def mockRandomBytes (counter : Nat) (bytes : UInt32) : ByteArray := ByteArray.mk (prngBytesAux (counter + 1) bytes.toNat []).toArray
def mockRandomHex (counter : Nat) (bytes : UInt32) : String := Proto.encodeHex (mockRandomBytes counter bytes)

private def mix32List : List UInt8 → List UInt8 → Nat → List UInt8
  | [], acc, _ => acc
  | b :: rest, acc, i =>
      let idx := i % 32
      mix32List rest (acc.zipIdx.map fun (cur, j) =>
        if j == idx then UInt8.ofNat ((cur.toNat * 33 + b.toNat + i + 1) % 256)
        else if j == (idx + 13) % 32 then UInt8.ofNat ((cur.toNat ^^^ b.toNat + j) % 256) else cur) (i + 1)
def mockSha256 (data : ByteArray) : ByteArray :=
  let init := (List.range 32).map fun i => UInt8.ofNat ((i * 19 + 0x5A) % 256)
  ByteArray.mk (mix32List ([UInt8.ofNat (data.size % 256), UInt8.ofNat ((data.size / 256) % 256)] ++ data.data.toList) init 0).toArray
def mockHmacSha256 (key msg : ByteArray) : ByteArray :=
  mockSha256 (ByteArray.mk (key.data.toList ++ [0xFF, UInt8.ofNat (key.size % 256), UInt8.ofNat ((key.size / 256) % 256)] ++ msg.data.toList).toArray)

private def encodeLenPrefix (bs : List UInt8) : List UInt8 := [UInt8.ofNat ((bs.length / 256) % 256), UInt8.ofNat (bs.length % 256)] ++ bs
private def decodeLenPrefix : List UInt8 → Option (List UInt8 × List UInt8)
  | hi :: lo :: rest => let n := hi.toNat * 256 + lo.toNat; if rest.length < n then none else some (rest.take n, rest.drop n)
  | _ => none
private def resolveMockKey (envVars : List (String × String)) (keyEnv : String) (fallback? : Option String) : Except ApiError String :=
  ((envVars.lookup keyEnv).filter (!·.isEmpty) <|> fallback?.filter (!·.isEmpty)).elim (.error (ApiError.internal s!"missing required encryption key `{keyEnv}`")) .ok
def mockAeadEncrypt (envVars : List (String × String)) (keyEnv : String) (fallback? : Option String) (aad pt : ByteArray) : Except ApiError ByteArray := do
  let k ← resolveMockKey envVars keyEnv fallback?
  return ByteArray.mk (encodeLenPrefix k.toUTF8.data.toList ++ encodeLenPrefix aad.data.toList ++ pt.data.toList).toArray
def mockAeadDecrypt (envVars : List (String × String)) (keyEnv : String) (fallback? : Option String) (aad ct : ByteArray) : Except ApiError ByteArray := do
  let k ← resolveMockKey envVars keyEnv fallback?
  let some (kBytes, rest1) := decodeLenPrefix ct.data.toList | .error (ApiError.internal "aead decrypt failed: malformed ciphertext")
  if kBytes != k.toUTF8.data.toList then .error (ApiError.internal "aead decrypt failed: authentication tag mismatch")
  else match decodeLenPrefix rest1 with
    | none => .error (ApiError.internal "aead decrypt failed: malformed aad")
    | some (aadBytes, ptBytes) => if aadBytes != aad.data.toList then .error (ApiError.internal "aead decrypt failed: aad mismatch") else .ok (ByteArray.mk ptBytes.toArray)

/-! ### 2. Pure In-Memory SQL Database & `SqlQuery` Evaluator -/

structure MemTable where (name : String) (columns : List String) (rows : List DbRow := []) deriving Inhabited
abbrev MemDb := List MemTable

namespace MemDb
def findTable (db : MemDb) (name : String) : Option MemTable := db.find? (·.name == name)
def upsertTable : MemDb → MemTable → MemDb | [], tbl => [tbl] | t :: rest, tbl => if t.name == tbl.name then tbl :: rest else t :: upsertTable rest tbl
def ensureTables (db : MemDb) (schemas : List TableSchema) : MemDb :=
  schemas.foldl (init := db) fun acc ts => if (acc.findTable ts.name.raw).isSome then acc else acc ++ [{ name := ts.name.raw, columns := ts.columns.map (·.name.raw) }]
def countRows (db : MemDb) (tblName : String) : Nat := (db.findTable tblName).elim 0 (·.rows.length)
end MemDb

private def buildRowFromPairs (cols : List String) (pairs : List (SqlIdent × SqlVal)) : DbRow :=
  (cols.map fun c => (pairs.find? (·.1.raw == c)).map Prod.snd |>.getD .null).toArray
def MemDb.seedEncoded (db : MemDb) (tblName : String) (cols : List String) (encodedRows : List (List (SqlIdent × SqlVal))) : MemDb :=
  let newRows := encodedRows.map (buildRowFromPairs cols)
  match db.findTable tblName with
  | some existing => db.upsertTable { existing with rows := existing.rows ++ newRows }
  | none => db ++ [{ name := tblName, columns := cols, rows := newRows }]

private def getRowCol (cols : List String) (row : DbRow) (name : String) : SqlVal := (cols.findIdx? (· == name)).bind (row.toList[·]?) |>.getD .null
private def sqlValToBool : SqlVal → Bool | .bool b => b | .int i => i != 0 | .text s => s == "true" || s == "1" | _ => false
private def sqlValToInt? : SqlVal → Option Int | .int i => some i | .bool b => some (if b then 1 else 0) | .text s => Qed.Str.parseInt? s | _ => none
private def sqlValCmp : SqlVal → SqlVal → Option Ordering
  | .int x, .int y => some (compare x y) | .text x, .text y => some (compare x y) | .bool x, .bool y => some (compare x y) | _, _ => none
private def sqlLikeMatch (pat str : List Char) : Nat → Bool
  | 0 => false
  | fuel + 1 => match pat, str with
      | [], [] => true | '!' :: p :: ps, c :: cs => p == c && sqlLikeMatch ps cs fuel | '%' :: ps, [] => sqlLikeMatch ps [] fuel
      | '%' :: ps, _ :: cs => sqlLikeMatch ps str fuel || sqlLikeMatch ('%' :: ps) cs fuel
      | '_' :: ps, _ :: cs => sqlLikeMatch ps cs fuel | p :: ps, c :: cs => p == c && sqlLikeMatch ps cs fuel | _, _ => false
private def lookupEnvCol (env : List (String × List String × DbRow)) (tbl? : Option String) (col : String) : SqlVal :=
  ((tbl?.bind fun t => env.find? (·.1 == t)) <|> env.head?).elim .null fun (_, cols, row) => getRowCol cols row col
private def evalBinOp (op : SqlBinOp) (lv rv : SqlVal) : SqlVal :=
  let cmpOk (ok : Ordering → Bool) := .bool ((sqlValCmp lv rv).map ok |>.getD false)
  let intOp (f : Int → Int → Int) := match sqlValToInt? lv, sqlValToInt? rv with | some a, some b => .int (f a b) | _, _ => .null
  match op with
  | .eq => .bool (lv == rv) | .ne => .bool (lv != rv) | .lt => cmpOk (· == .lt) | .le => cmpOk (· != .gt)
  | .gt => cmpOk (· == .gt) | .ge => cmpOk (· != .lt) | .add => intOp (· + ·) | .sub => intOp (· - ·) | .mul => intOp (· * ·) | .and | .or => .bool false
private def evalSqlExpr (db : MemDb) (env : List (String × List String × DbRow)) : Nat → SqlExpr → SqlVal
  | 0, _ => .bool false
  | fuel + 1, e =>
      let recEv := evalSqlExpr db env fuel
      let strOp (l r : SqlExpr) (f : String → String → Bool) : SqlVal := match recEv l, recEv r with | .text s, .text p => .bool (f s p) | _, _ => .bool false
      match e with
      | .litTrue => .bool true | .litFalse => .bool false | .param v => v
      | .col c => lookupEnvCol env none c.raw | .qualCol tbl c => lookupEnvCol env (some tbl.raw) c.raw
      | .not inner => .bool (!sqlValToBool (recEv inner)) | .isNull inner => .bool (recEv inner == .null) | .isNotNull inner => .bool (recEv inner != .null)
      | .strLen inner => match recEv inner with | .text s => .int (Int.ofNat s.length) | .bytes bs => .int (Int.ofNat bs.size) | _ => .int 0
      | .startsWith l r => strOp l r Qed.Str.startsWith | .contains l r => strOp l r Qed.Str.contains
      | .like l r => strOp l r fun s p => sqlLikeMatch p.toList s.toList (p.length + s.length + 2)
      | .inList l vs => let lv := recEv l; .bool (vs.any (· == lv))
      | .existsSubquery subTbl al pred => (db.findTable subTbl.raw).elim (.bool false) fun st => .bool (st.rows.any fun r => sqlValToBool (evalSqlExpr db ((al.raw, st.columns, r) :: env) fuel pred))
      | .binOp .and l r => .bool (sqlValToBool (recEv l) && sqlValToBool (recEv r))
      | .binOp .or l r => .bool (sqlValToBool (recEv l) || sqlValToBool (recEv r)) | .binOp op l r => evalBinOp op (recEv l) (recEv r)

private def insertSortedBy {α : Type} (le : α → α → Bool) (x : α) : List α → List α | [] => [x] | y :: ys => if le x y then x :: y :: ys else y :: insertSortedBy le x ys
private def sortRowsBy (cols : List String) (ob? : Option (SqlIdent × SqlOrderDir)) (rows : List DbRow) : List DbRow :=
  ob?.elim rows fun (col, dir) =>
    let le (a b : DbRow) : Bool := match sqlValCmp (getRowCol cols a col.raw) (getRowCol cols b col.raw), dir with
      | some .lt, .asc | some .eq, .asc | some .gt, .desc | some .eq, .desc => true | _, _ => false
    rows.foldl (init := []) fun acc r => insertSortedBy le r acc
private def sliceRows (limit? offset? : Option Nat) (rows : List DbRow) : List DbRow := let a := offset?.elim rows rows.drop; limit?.elim a a.take
private def projectRow (cols : List String) (proj : List SqlIdent) (row : DbRow) : DbRow := (proj.map (getRowCol cols row ·.raw)).toArray
private def conflictMatches (cols : List String) (conflictCols : List SqlIdent) (existing candidate : DbRow) : Bool :=
  !conflictCols.isEmpty && conflictCols.all fun cc => getRowCol cols existing cc.raw == getRowCol cols candidate cc.raw
private def transformRows (cols : List String) (ret : List SqlIdent) (step : DbRow → Option (Option DbRow × DbRow)) : List DbRow → List DbRow × List DbRow × Nat
  | [] => ([], [], 0)
  | r :: rs =>
      let (tailRows, tailRet, tailAff) := transformRows cols ret step rs
      match step r with
      | none => (r :: tailRows, tailRet, tailAff)
      | some (kept?, retSrc) => (kept?.elim tailRows (· :: tailRows), if ret.isEmpty then tailRet else projectRow cols ret retSrc :: tailRet, tailAff + 1)

def evalSqlQuery (cfg : DbConfig) (db0 : MemDb) (q : SqlQuery) : MemDb × Except ApiError DbResult :=
  let db := db0.ensureTables cfg.tables
  let withTbl (tn : SqlIdent) (f : MemTable → MemDb × Except ApiError DbResult) :=
    (db.findTable tn.raw).elim (db, .error (ApiError.internal s!"unknown table `{tn.raw}` in in-memory evaluator")) f
  let withSchemaTbl (sc tn : SqlIdent) (f : MemTable → MemDb × Except ApiError DbResult) :=
    ((db.findTable (sc.raw ++ "." ++ tn.raw)).orElse fun _ => db.findTable tn.raw).elim
      (db, .error (ApiError.internal s!"unknown table `{sc.raw}.{tn.raw}` in in-memory evaluator")) f
  let evalWhere (t : MemTable) (tn : SqlIdent) (w : SqlExpr) (r : DbRow) : Bool := sqlValToBool (evalSqlExpr db [(tn.raw, t.columns, r)] 64 w)
  let filterRows (t : MemTable) (tn : SqlIdent) (w : SqlExpr) : List DbRow := t.rows.filter (evalWhere t tn w)
  let uniqueCols (tn : SqlIdent) : List SqlIdent :=
    (cfg.tables.find? (·.name.raw == tn.raw)).elim [] fun ts => (ts.columns.filter fun (c : ColumnSchema) => c.isPrimaryKey || c.isUnique).map (·.name)
  let hasSingleColConflict (t : MemTable) (cols : List SqlIdent) (newRow : DbRow) : Bool :=
    cols.any fun pc => t.rows.any fun r => getRowCol t.columns r pc.raw == getRowCol t.columns newRow pc.raw
  let appendRow (t : MemTable) (newRow : DbRow) (ret : List SqlIdent) : MemDb × Except ApiError DbResult :=
    (db.upsertTable { t with rows := t.rows ++ [newRow] }, .ok { rows := if ret.isEmpty then #[] else #[projectRow t.columns ret newRow], affected := 1 })
  let runSelectOn (t : MemTable) (tn : SqlIdent) (cols? : Option (List SqlIdent)) (w : SqlExpr) (ob : Option (SqlIdent × SqlOrderDir)) (lim off : Option Nat) :=
    let sliced := sliceRows lim off (sortRowsBy t.columns ob (filterRows t tn w))
    let out := cols?.elim sliced fun cols => sliced.map (projectRow t.columns cols); (db, .ok { rows := out.toArray, affected := out.length })
  let runSelect (tn : SqlIdent) (cols? : Option (List SqlIdent)) (w : SqlExpr) (ob : Option (SqlIdent × SqlOrderDir)) (lim off : Option Nat) :=
    withTbl tn fun t => runSelectOn t tn cols? w ob lim off
  let runTransform (t : MemTable) (ret : List SqlIdent) (useRetLen : Bool) (step : DbRow → Option (Option DbRow × DbRow)) :=
    let (outRows, retRows, aff) := transformRows t.columns ret step t.rows
    (db.upsertTable { t with rows := outRows }, .ok { rows := retRows.toArray, affected := if useRetLen then retRows.length else aff })
  match q with
  | .select tn cols w ob lim off => runSelect tn (some cols) w ob lim off
  | .selectAll tn w ob lim off => runSelect tn none w ob lim off
  | .selectSchema sc tn cols w ob lim off => withSchemaTbl sc tn fun t => runSelectOn t tn (if cols.isEmpty then none else some cols) w ob lim off
  | .count tn w => withTbl tn fun t => (db, .ok { rows := #[#[.int (Int.ofNat (filterRows t tn w).length)]], affected := 1 })
  | .countSchema sc tn w => withSchemaTbl sc tn fun t => (db, .ok { rows := #[#[.int (Int.ofNat (filterRows t tn w).length)]], affected := 1 })
  | .aggregate op tn col w => withTbl tn fun t =>
      let vals := (filterRows t tn w).filterMap fun r => sqlValToInt? (getRowCol t.columns r col.raw)
      let aggVal : SqlVal := match op, vals with
        | .sum, vs => .int (vs.foldl (· + ·) 0) | .min, [] | .max, [] => .null | .min, v :: vs => .int (vs.foldl min v) | .max, v :: vs => .int (vs.foldl max v)
      (db, .ok { rows := #[#[aggVal]], affected := 1 })
  | .joinSelect lt rt lCols rCols lJc rJc lW rW ob lim off => withTbl lt fun tL => withTbl rt fun tR =>
      let pairs := tL.rows.flatMap fun rl =>
        if !evalWhere tL lt lW rl then [] else let lv := getRowCol tL.columns rl lJc.raw
          tR.rows.filterMap fun rr => if getRowCol tR.columns rr rJc.raw == lv && sqlValToBool (evalSqlExpr db [(rt.raw, tR.columns, rr), (lt.raw, tL.columns, rl)] 64 rW) then some (rl, rr) else none
      let out := sliceRows lim off (sortRowsBy (lCols.map (·.raw) ++ rCols.map (·.raw)) ob (pairs.map fun (rl, rr) => (lCols.map (getRowCol tL.columns rl ·.raw) ++ rCols.map (getRowCol tR.columns rr ·.raw)).toArray))
      (db, .ok { rows := out.toArray, affected := out.length })
  | .insert tn pairs ret => withTbl tn fun t =>
      let newRow := buildRowFromPairs t.columns pairs
      if hasSingleColConflict t (uniqueCols tn) newRow then (db, .error ⟨409, s!"unique constraint violation on `{tn.raw}`"⟩) else appendRow t newRow ret
  | .insertOrIgnore tn pairs conflictCols ret => withTbl tn fun t =>
      let newRow := buildRowFromPairs t.columns pairs
      let hit := if !conflictCols.isEmpty then t.rows.any (conflictMatches t.columns conflictCols · newRow) else hasSingleColConflict t (uniqueCols tn) newRow
      if hit then (db, .ok { rows := #[], affected := 0 }) else appendRow t newRow ret
  | .upsert tn pairs conflictCols updateCols conflictWhere? ret => withTbl tn fun t =>
      let newRow := buildRowFromPairs t.columns pairs
      if t.rows.any (conflictMatches t.columns conflictCols · newRow) then
        runTransform t ret true fun r =>
          if conflictMatches t.columns conflictCols r newRow && conflictWhere?.elim true (evalWhere t tn · r) then
            let r' := (t.columns.zipIdx.map fun (c, i) => if updateCols.any (·.raw == c) then getRowCol t.columns newRow c else r.toList[i]?.getD .null).toArray
            some (some r', r')
          else none
      else appendRow t newRow ret
  | .update tn sets w ret => withTbl tn fun t => runTransform t ret false fun r =>
      if evalWhere t tn w r then
        let r' := (t.columns.zipIdx.map fun (c, i) => match sets.find? (·.1.raw == c) with | some (_, ex) => evalSqlExpr db [(tn.raw, t.columns, r)] 64 ex | none => r.toList[i]?.getD .null).toArray
        some (some r', r')
      else none
  | .delete tn w ret => withTbl tn fun t => runTransform t ret false fun r => if evalWhere t tn w r then some (none, r) else none

/-! ### 3. Pure `ThreadProg` Evaluator (`EvalEnv`, `EvalState`, `EvalTrace`, `evalProg`) -/

structure HttpStub where (method : String := "") (url : String) (resp : Except ApiError OutboundResp) (once : Bool := false) deriving Inhabited
def HttpStub.ok (method url : String) (status : UInt32 := 200) (body : String := "") (headers : List (String × String) := []) (once : Bool := false) : HttpStub :=
  { method, url, resp := .ok { status, body := body.toUTF8, headers }, once }
def HttpStub.err (method url : String) (code : Nat := 502) (msg : String := "upstream error") (once : Bool := false) : HttpStub :=
  { method, url, resp := .error { code, message := msg }, once }

private def stubMatches (s : HttpStub) (req : OutboundReq) : Bool :=
  (s.method.isEmpty || Qed.Str.toUpper s.method == Qed.Str.toUpper req.method) && (req.url == s.url || req.pathAndQuery == s.url || Qed.Str.startsWith req.url s.url)
private def matchHttpStub (req : OutboundReq) : List HttpStub → Option (Except ApiError OutboundResp × List HttpStub)
  | [] => none
  | s :: rest => if stubMatches s req then some (s.resp, if s.once || rest.any (stubMatches · req) then rest else s :: rest) else (matchHttpStub req rest).map fun (r, rest') => (r, s :: rest')

structure ProcStub where
  (cmd : String) (argsPrefix : List String := []) (resp : Except ApiError ProcOutput) (once : Bool := false)
deriving Inhabited

private def procStubMatches (s : ProcStub) (cmd : String) (args : Array String) : Bool :=
  s.cmd == cmd && (args.toList.take s.argsPrefix.length == s.argsPrefix)
private def matchProcStub (cmd : String) (args : Array String) : List ProcStub → Option (Except ApiError ProcOutput × List ProcStub)
  | [] => none
  | s :: rest =>
      if procStubMatches s cmd args then some (s.resp, if s.once || rest.any (procStubMatches · cmd args) then rest else s :: rest)
      else (matchProcStub cmd args rest).map fun (r, rest') => (r, s :: rest')

structure EvalEnv where (envVars : List (String × String) := []) (nowMs : UInt64 := 1700000000000) deriving Inhabited

structure EvalTrace where
  (httpCalls : List OutboundReq := []) (dbQueries : List SqlQuery := []) (cookies : List SetCookie := [])
  (sseEvents : List SseEvent := []) (wsBroadcasts : List WsEmit := []) (encryptCount decryptCount : Nat := 0)
  (sleptMs : Nat := 0) (procCalls : List (String × Array String × Option String) := [])
deriving Inhabited

structure EvalState (σ : Type) where
  (shared : σ) (db : MemDb := []) (httpStubs : List HttpStub := []) (txSaved : List (UInt64 × MemDb) := [])
  (nextTxId : UInt64 := 1) (rngCounter : Nat := 0) (nowOffsetMs : UInt64 := 0)
  (memFs : List (String × ByteArray) := []) (memDirs : List String := []) (procStubs : List ProcStub := []) (tmpCounter : Nat := 0)
  (trace : EvalTrace := {})
deriving Inhabited

structure EvalResult (σ α : Type) where (value : α) (state : EvalState σ) deriving Inhabited

private def stepEffect {σ : Type} (env : EvalEnv) (st : EvalState σ) (eff : ServerEffect) : EvalState σ × eff.Resp :=
  let withTr {α : Type} (f : EvalTrace → EvalTrace) (r : α) := ({ st with trace := f st.trace }, r)
  match eff with
  | .httpCall req =>
      let tr := { st.trace with httpCalls := st.trace.httpCalls ++ [req] }
      match matchHttpStub req st.httpStubs with
      | some (resp, stubs') => ({ st with httpStubs := stubs', trace := tr }, resp)
      | none => ({ st with trace := tr }, .error (ApiError.internal s!"unmocked HTTP {req.method} {req.url}"))
  | .dbExec cfg q | .dbTxExec cfg _ q => let (db', res) := evalSqlQuery cfg st.db q; ({ st with db := db', trace := { st.trace with dbQueries := st.trace.dbQueries ++ [q] } }, res)
  | .dbExecDdl cfg => ({ st with db := st.db.ensureTables cfg.tables }, .ok ())
  | .dbTxBegin cfg => let db' := st.db.ensureTables cfg.tables; let tid := st.nextTxId; ({ st with db := db', txSaved := (tid, db') :: st.txSaved, nextTxId := tid + 1 }, .ok tid)
  | .dbTxCommit _ tid => ({ st with txSaved := st.txSaved.filter (·.1 != tid) }, .ok ())
  | .dbTxRollback _ tid => (st.txSaved.lookup tid).elim (st, ()) fun saved => ({ st with db := saved, txSaved := st.txSaved.filter (·.1 != tid) }, ())
  | .setCookie c => withTr (fun t => { t with cookies := t.cookies ++ [c] }) ()
  | .sendSse ev => withTr (fun t => { t with sseEvents := t.sseEvents ++ [ev] }) ()
  | .wsBroadcast tp p => withTr (fun t => { t with wsBroadcasts := t.wsBroadcasts ++ [{ topic := tp, payload := p }] }) ()
  | .readEnv v => (st, env.envVars.lookup v) | .nowMs => (st, env.nowMs + st.nowOffsetMs)
  | .sleep ms => ({ st with nowOffsetMs := st.nowOffsetMs + ms.toUInt64, trace := { st.trace with sleptMs := st.trace.sleptMs + ms } }, ())
  | .randomHex n => ({ st with rngCounter := st.rngCounter + 1 }, mockRandomHex st.rngCounter n)
  | .randomBytes n => ({ st with rngCounter := st.rngCounter + 1 }, mockRandomBytes st.rngCounter n)
  | .hmacSha256 k m => (st, mockHmacSha256 k m) | .sha256 d => (st, mockSha256 d) | .constEq a b => (st, a == b)
  | .aeadEncrypt kEnv fb? aad pt => withTr (fun t => { t with encryptCount := t.encryptCount + 1 }) (mockAeadEncrypt env.envVars kEnv fb? aad pt)
  | .aeadDecrypt kEnv fb? aad ct => withTr (fun t => { t with decryptCount := t.decryptCount + 1 }) (mockAeadDecrypt env.envVars kEnv fb? aad ct)
  | .procExec cmd args cwd? _env =>
      let tr := { st.trace with procCalls := st.trace.procCalls ++ [(cmd, args, cwd?)] }
      match matchProcStub cmd args st.procStubs with
      | some (resp, stubs') => ({ st with procStubs := stubs', trace := tr }, resp)
      | none => ({ st with trace := tr }, .error (ApiError.internal s!"unmocked Proc.exec `{cmd}`"))
  | .fsRead path =>
      match st.memFs.lookup path with
      | some bs => (st, .ok bs)
      | none => (st, .error (ApiError.notFound s!"file not found: {path}"))
  | .fsWrite path data => ({ st with memFs := (path, data) :: st.memFs.filter (·.1 != path) }, .ok ())
  | .fsMkdirAll path => ({ st with memDirs := if st.memDirs.contains path then st.memDirs else path :: st.memDirs }, .ok ())
  | .fsRemoveAll path =>
      let pfx := path ++ "/"
      ({ st with memFs := st.memFs.filter fun (k, _) => k != path && !Qed.Str.startsWith k pfx,
                 memDirs := st.memDirs.filter fun d => d != path && !Qed.Str.startsWith d pfx }, .ok ())
  | .fsExists path => (st, st.memFs.any (·.1 == path) || st.memDirs.contains path)
  | .fsMktempDir pfx =>
      let dir := s!"/tmp/{pfx}{st.tmpCounter}"
      ({ st with tmpCounter := st.tmpCounter + 1, memDirs := dir :: st.memDirs }, .ok dir)

def evalProg {σ α : Type} (env : EvalEnv) (st : EvalState σ) : ThreadProg σ α → EvalResult σ α
  | .pure a => ⟨a, st⟩ | .io eff k => let (st', resp) := stepEffect env st eff; evalProg env st' (k resp)
  | .atomic step next => let s0 := st.shared; evalProg env { st with shared := step s0 } (next s0)

def setNow (e : EvalEnv) (ms : UInt64) : EvalEnv := { e with nowMs := ms }
def setEnvVar (e : EvalEnv) (k v : String) : EvalEnv := { e with envVars := (k, v) :: e.envVars }
def setSession (c : RequestCtx) (b : Bool) : RequestCtx := { c with authMethod := if b then .session else .bearer }
def setQuery (c : RequestCtx) (q : String) : RequestCtx := { c with query := q }
def setBody (c : RequestCtx) (b : String) : RequestCtx := { c with body := b }
def setHeader (c : RequestCtx) (k v : String) : RequestCtx := { c with headers := (k, v) :: c.headers }
def setRole (c : RequestCtx) (r : String) : RequestCtx := { c with claims := ("role", r) :: c.claims }
def setUser (c : RequestCtx) : Option String → RequestCtx
  | none => { c with userId := none, authMethod := .none }
  | some u => { c with userId := some u, authMethod := if c.authMethod == .none then .bearer else c.authMethod }
def setShared {σ : Type} (s : EvalState σ) (v : σ) : EvalState σ := { s with shared := v }
def pushHttpStub {σ : Type} (s : EvalState σ) (stub : HttpStub) : EvalState σ := { s with httpStubs := s.httpStubs ++ [stub] }
def pushProcStub {σ : Type} (s : EvalState σ) (stub : ProcStub) : EvalState σ := { s with procStubs := s.procStubs ++ [stub] }
def seedMemFile {σ : Type} (s : EvalState σ) (path content : String) : EvalState σ :=
  { s with memFs := (path, content.toUTF8) :: s.memFs.filter (·.1 != path) }
def seedDbRows {σ Row : Type} (s : EvalState σ) (tbl : String) (sch : TableSchema) (enc : Row → List (SqlIdent × SqlVal)) (rows : List Row) : EvalState σ :=
  { s with db := s.db.seedEncoded tbl (sch.columns.map (·.name.raw)) (rows.map enc) }
def httpStatus : Except ApiError (Option HttpResponse) → Nat | .ok (some r) => r.status | .ok none => 404 | .error e => e.code
def httpBody : Except ApiError (Option HttpResponse) → String | .ok (some r) => (String.fromUTF8? r.body).getD "" | .ok none => "" | .error e => e.message
def isOk {ε α : Type} : Except ε α → Bool | .ok _ => true | .error _ => false
def isOkEq {ε α : Type} [DecidableEq α] (v : α) : Except ε α → Bool | .ok x => decide (x = v) | .error _ => false
def isHttpOk {ε α : Type} : Except ε (Option α) → Bool | .ok (some _) => true | _ => false
def isHttpOkEq {ε α : Type} [DecidableEq α] (v : α) : Except ε (Option α) → Bool | .ok (some x) => decide (x = v) | _ => false
def isErr {ε α : Type} : Except ε α → Bool | .error _ => true | .ok _ => false
def isErrCode {α : Type} (code : Nat) : Except ApiError α → Bool | .error e => e.code == code | .ok _ => false

end Qed.Server.Eval
