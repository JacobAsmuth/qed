import Qed.Server.Core

namespace Qed.Server.Eval

open Qed Qed.Server Qed.Server.Db

/-! ## Pure Kernel-Reducible `ThreadProg` & In-Memory SQL Evaluator (`Qed.Server.Eval`)

Total, deterministic interpreter over `ThreadProg`, `ServerEffect`, and `SqlQuery`.
Uses only structural/fuel recursion and `Qed.Str.*` (zero `partial`, zero `import Lean`,
zero FFI) so `service` and `server` `example` blocks compile into kernel-checked
`decide +kernel` theorems. -/

/-! ### 1. Deterministic Pure Crypto, Random & AEAD Mock Primitives -/

private def hexDigitChar (n : Nat) : Char :=
  let d := n % 16
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

private def repeatHexAux (seed : Nat) : Nat → List Char → List Char
  | 0, acc => acc.reverse
  | n + 1, acc =>
      let b := (seed * 31 + n * 17 + 7) % 256
      repeatHexAux (seed + 1) n (hexDigitChar (b % 16) :: hexDigitChar (b / 16) :: acc)

def mockRandomHex (counter : Nat) (bytes : UInt32) : String :=
  String.ofList (repeatHexAux (counter + 1) bytes.toNat [])

private def repeatBytesAux (seed : Nat) : Nat → List UInt8 → List UInt8
  | 0, acc => acc.reverse
  | n + 1, acc =>
      let b : UInt8 := UInt8.ofNat ((seed * 31 + n * 17 + 7) % 256)
      repeatBytesAux (seed + 1) n (b :: acc)

def mockRandomBytes (counter : Nat) (bytes : UInt32) : ByteArray :=
  ByteArray.mk (repeatBytesAux (counter + 1) bytes.toNat []).toArray

private def mix32List (bs : List UInt8) (acc : List UInt8) (i : Nat) : List UInt8 :=
  match bs with
  | [] => acc
  | b :: rest =>
      let idx := i % 32
      let acc' := acc.zipIdx.map fun (cur, j) =>
        if j == idx then UInt8.ofNat ((cur.toNat * 33 + b.toNat + i + 1) % 256)
        else if j == (idx + 13) % 32 then UInt8.ofNat ((cur.toNat ^^^ b.toNat + j) % 256)
        else cur
      mix32List rest acc' (i + 1)

private def initHashState : List UInt8 :=
  (List.range 32).map fun i => UInt8.ofNat ((i * 19 + 0x5A) % 256)

def mockSha256 (data : ByteArray) : ByteArray :=
  let lenTag : List UInt8 := [UInt8.ofNat (data.size % 256), UInt8.ofNat ((data.size / 256) % 256)]
  ByteArray.mk (mix32List (lenTag ++ data.data.toList) initHashState 0).toArray

def mockHmacSha256 (key msg : ByteArray) : ByteArray :=
  let sep : List UInt8 := [0xFF, UInt8.ofNat (key.size % 256), UInt8.ofNat ((key.size / 256) % 256)]
  mockSha256 (ByteArray.mk (key.data.toList ++ sep ++ msg.data.toList).toArray)

private def encodeLenPrefix (bs : List UInt8) : List UInt8 :=
  let n := bs.length
  [UInt8.ofNat ((n / 256) % 256), UInt8.ofNat (n % 256)] ++ bs

private def decodeLenPrefix (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  match bs with
  | hi :: lo :: rest =>
      let n := hi.toNat * 256 + lo.toNat
      if rest.length < n then none else some (rest.take n, rest.drop n)
  | _ => none

private def resolveMockKey (envVars : List (String × String)) (keyEnv : String) (fallback? : Option String) : Except ApiError String :=
  match (envVars.lookup keyEnv).filter (!·.isEmpty) <|> fallback?.filter (!·.isEmpty) with
  | some k => .ok k
  | none => .error (ApiError.internal s!"missing required encryption key `{keyEnv}`")

def mockAeadEncrypt (envVars : List (String × String)) (keyEnv : String) (fallback? : Option String)
    (aad pt : ByteArray) : Except ApiError ByteArray := do
  let k ← resolveMockKey envVars keyEnv fallback?
  let payload := encodeLenPrefix k.toUTF8.data.toList ++ encodeLenPrefix aad.data.toList ++ pt.data.toList
  return ByteArray.mk payload.toArray

def mockAeadDecrypt (envVars : List (String × String)) (keyEnv : String) (fallback? : Option String)
    (aad ct : ByteArray) : Except ApiError ByteArray := do
  let k ← resolveMockKey envVars keyEnv fallback?
  match decodeLenPrefix ct.data.toList with
  | none => .error (ApiError.internal "aead decrypt failed: malformed ciphertext")
  | some (kBytes, rest1) =>
      if kBytes != k.toUTF8.data.toList then
        .error (ApiError.internal "aead decrypt failed: authentication tag mismatch")
      else match decodeLenPrefix rest1 with
        | none => .error (ApiError.internal "aead decrypt failed: malformed aad")
        | some (aadBytes, ptBytes) =>
            if aadBytes != aad.data.toList then
              .error (ApiError.internal "aead decrypt failed: aad mismatch")
            else .ok (ByteArray.mk ptBytes.toArray)

/-! ### 2. Pure In-Memory SQL Database & `SqlQuery` Evaluator -/

structure MemTable where
  name    : String
  columns : List String
  rows    : List DbRow := []
deriving Inhabited, DecidableEq

abbrev MemDb := List MemTable

namespace MemDb

def findTable (db : MemDb) (name : String) : Option MemTable :=
  db.find? (·.name == name)

def upsertTable (db : MemDb) (tbl : MemTable) : MemDb :=
  match db with
  | [] => [tbl]
  | t :: rest => if t.name == tbl.name then tbl :: rest else t :: upsertTable rest tbl

def ensureTables (db : MemDb) (schemas : List TableSchema) : MemDb :=
  schemas.foldl (init := db) fun acc ts =>
    if (acc.findTable ts.name.raw).isSome then acc
    else acc ++ [{ name := ts.name.raw, columns := ts.columns.map (·.name.raw), rows := [] }]

end MemDb

private def buildRowFromPairs (cols : List String) (pairs : List (SqlIdent × SqlVal)) : DbRow :=
  (cols.map fun c => (pairs.find? fun p => p.1.raw == c).map Prod.snd |>.getD .null).toArray

def MemDb.seedEncoded (db : MemDb) (tblName : String) (cols : List String)
    (encodedRows : List (List (SqlIdent × SqlVal))) : MemDb :=
  let newRows := encodedRows.map (buildRowFromPairs cols)
  match db.findTable tblName with
  | some existing => db.upsertTable { existing with rows := existing.rows ++ newRows }
  | none => db ++ [{ name := tblName, columns := cols, rows := newRows }]

def MemDb.countRows (db : MemDb) (tblName : String) : Nat :=
  match db.findTable tblName with | some t => t.rows.length | none => 0

private def colIndex (cols : List String) (name : String) : Option Nat :=
  let rec go (i : Nat) : List String → Option Nat
    | [] => none
    | c :: cs => if c == name then some i else go (i + 1) cs
  go 0 cols

private def getRowCol (cols : List String) (row : DbRow) (name : String) : SqlVal :=
  match colIndex cols name with
  | some i => row.toList[i]?.getD .null
  | none => .null

private def sqlValToBool : SqlVal → Bool
  | .bool b => b | .int i => i != 0 | .text s => s == "true" || s == "1" | _ => false

private def sqlValToInt? : SqlVal → Option Int
  | .int i => some i | .bool b => some (if b then 1 else 0) | .text s => Qed.Str.parseInt? s | _ => none

private def sqlValCmp (a b : SqlVal) : Option Ordering :=
  match a, b with
  | .int x, .int y => some (compare x y)
  | .text x, .text y => some (compare x y)
  | .bool x, .bool y => some (compare x y)
  | _, _ => none

private def sqlLikeMatch (pat str : List Char) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
      match pat, str with
      | [], [] => true
      | '!' :: p :: ps, c :: cs => p == c && sqlLikeMatch ps cs fuel
      | '%' :: ps, [] => sqlLikeMatch ps [] fuel
      | '%' :: ps, _ :: cs => sqlLikeMatch ps str fuel || sqlLikeMatch ('%' :: ps) cs fuel
      | '_' :: ps, _ :: cs => sqlLikeMatch ps cs fuel
      | p :: ps, c :: cs => p == c && sqlLikeMatch ps cs fuel
      | _, _ => false

private def evalSqlExpr (db : MemDb) (env : List (String × List String × DbRow)) : Nat → SqlExpr → SqlVal
  | 0, _ => .bool false
  | fuel + 1, e =>
      let recEv := evalSqlExpr db env fuel
      match e with
      | .litTrue => .bool true
      | .litFalse => .bool false
      | .param v => v
      | .col c =>
          match env with
          | (_, cols, row) :: _ => getRowCol cols row c.raw
          | [] => .null
      | .qualCol tbl c =>
          match env.find? fun (al, _, _) => al == tbl.raw with
          | some (_, cols, row) => getRowCol cols row c.raw
          | none =>
              match env with
              | (_, cols, row) :: _ => getRowCol cols row c.raw
              | [] => .null
      | .not inner => .bool (!sqlValToBool (recEv inner))
      | .isNull inner => .bool (recEv inner == .null)
      | .isNotNull inner => .bool (recEv inner != .null)
      | .strLen inner =>
          match recEv inner with
          | .text s => .int (Int.ofNat s.length)
          | .bytes bs => .int (Int.ofNat bs.size)
          | _ => .int 0
      | .startsWith l r =>
          match recEv l, recEv r with
          | .text s, .text p => .bool (Qed.Str.startsWith s p)
          | _, _ => .bool false
      | .contains l r =>
          match recEv l, recEv r with
          | .text s, .text n => .bool (Qed.Str.contains s n)
          | _, _ => .bool false
      | .like l r =>
          match recEv l, recEv r with
          | .text s, .text p => .bool (sqlLikeMatch p.toList s.toList (p.length + s.length + 2))
          | _, _ => .bool false
      | .inList l vs =>
          let lv := recEv l
          .bool (vs.any (· == lv))
      | .existsSubquery subTbl al pred =>
          match db.findTable subTbl.raw with
          | none => .bool false
          | some st =>
              .bool (st.rows.any fun r => sqlValToBool (evalSqlExpr db ((al.raw, st.columns, r) :: env) fuel pred))
      | .binOp op l r =>
          match op with
          | .and => .bool (sqlValToBool (recEv l) && sqlValToBool (recEv r))
          | .or  => .bool (sqlValToBool (recEv l) || sqlValToBool (recEv r))
          | .eq  => .bool (recEv l == recEv r)
          | .ne  => .bool (recEv l != recEv r)
          | .lt  => .bool (sqlValCmp (recEv l) (recEv r) == some .lt)
          | .le  => .bool (match sqlValCmp (recEv l) (recEv r) with | some .lt | some .eq => true | _ => false)
          | .gt  => .bool (sqlValCmp (recEv l) (recEv r) == some .gt)
          | .ge  => .bool (match sqlValCmp (recEv l) (recEv r) with | some .gt | some .eq => true | _ => false)
          | .add => match sqlValToInt? (recEv l), sqlValToInt? (recEv r) with | some a, some b => .int (a + b) | _, _ => .null
          | .sub => match sqlValToInt? (recEv l), sqlValToInt? (recEv r) with | some a, some b => .int (a - b) | _, _ => .null
          | .mul => match sqlValToInt? (recEv l), sqlValToInt? (recEv r) with | some a, some b => .int (a * b) | _, _ => .null

private def insertSortedBy {α : Type} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertSortedBy le x ys

private def sortRowsBy (cols : List String) (ob? : Option (SqlIdent × SqlOrderDir)) (rows : List DbRow) : List DbRow :=
  match ob? with
  | none => rows
  | some (col, dir) =>
      let le (a b : DbRow) : Bool :=
        let va := getRowCol cols a col.raw; let vb := getRowCol cols b col.raw
        match sqlValCmp va vb, dir with
        | some .lt, .asc  | some .eq, .asc  => true
        | some .gt, .desc | some .eq, .desc => true
        | _, _ => false
      rows.foldl (init := []) fun acc r => insertSortedBy le r acc

private def sliceRows (limit? offset? : Option Nat) (rows : List DbRow) : List DbRow :=
  let afterOff := match offset? with | some n => rows.drop n | none => rows
  match limit? with | some n => afterOff.take n | none => afterOff

private def projectRow (cols : List String) (proj : List SqlIdent) (row : DbRow) : DbRow :=
  (proj.map fun c => getRowCol cols row c.raw).toArray

private def applySets (db : MemDb) (tblName : String) (cols : List String) (sets : List (SqlIdent × SqlExpr)) (row : DbRow) : DbRow :=
  let env := [(tblName, cols, row)]
  let updated := cols.zipIdx.map fun (c, i) =>
    match sets.find? fun s => s.1.raw == c with
    | some (_, expr) => evalSqlExpr db env 64 expr
    | none => row.toList[i]?.getD .null
  updated.toArray

private def conflictMatches (cols : List String) (conflictCols : List SqlIdent) (existing candidate : DbRow) : Bool :=
  !conflictCols.isEmpty && conflictCols.all fun cc => getRowCol cols existing cc.raw == getRowCol cols candidate cc.raw

private def upsertRowsAux (db : MemDb) (tn : SqlIdent) (cols : List String)
    (conflictCols updateCols : List SqlIdent) (conflictWhere? : Option SqlExpr)
    (ret : List SqlIdent) (newRow : DbRow) : List DbRow → List DbRow × List DbRow
  | [] => ([], [])
  | r :: rs =>
      let (tailRows, tailRet) := upsertRowsAux db tn cols conflictCols updateCols conflictWhere? ret newRow rs
      if conflictMatches cols conflictCols r newRow then
        let allowUpd := match conflictWhere? with
          | none => true
          | some cw => sqlValToBool (evalSqlExpr db [(tn.raw, cols, r)] 64 cw)
        if allowUpd then
          let r' := (cols.zipIdx.map fun (c, i) =>
            if updateCols.any (·.raw == c) then getRowCol cols newRow c else r.toList[i]?.getD .null).toArray
          (r' :: tailRows, if ret.isEmpty then tailRet else projectRow cols ret r' :: tailRet)
        else (r :: tailRows, tailRet)
      else (r :: tailRows, tailRet)

private def updateRowsAux (db : MemDb) (tn : SqlIdent) (cols : List String)
    (sets : List (SqlIdent × SqlExpr)) (w : SqlExpr) (ret : List SqlIdent) :
    List DbRow → List DbRow × List DbRow × Nat
  | [] => ([], [], 0)
  | r :: rs =>
      let (tailRows, tailRet, tailAff) := updateRowsAux db tn cols sets w ret rs
      if sqlValToBool (evalSqlExpr db [(tn.raw, cols, r)] 64 w) then
        let r' := applySets db tn.raw cols sets r
        (r' :: tailRows, (if ret.isEmpty then tailRet else projectRow cols ret r' :: tailRet), tailAff + 1)
      else (r :: tailRows, tailRet, tailAff)

private def deleteRowsAux (db : MemDb) (tn : SqlIdent) (cols : List String)
    (w : SqlExpr) (ret : List SqlIdent) : List DbRow → List DbRow × List DbRow × Nat
  | [] => ([], [], 0)
  | r :: rs =>
      let (kept, tailRet, tailAff) := deleteRowsAux db tn cols w ret rs
      if sqlValToBool (evalSqlExpr db [(tn.raw, cols, r)] 64 w) then
        (kept, (if ret.isEmpty then tailRet else projectRow cols ret r :: tailRet), tailAff + 1)
      else (r :: kept, tailRet, tailAff)

def evalSqlQuery (cfg : DbConfig) (db0 : MemDb) (q : SqlQuery) : MemDb × Except ApiError DbResult :=
  let db := db0.ensureTables cfg.tables
  let getTbl (tn : SqlIdent) : Except ApiError MemTable :=
    match db.findTable tn.raw with
    | some t => .ok t
    | none => .error (ApiError.internal s!"unknown table `{tn.raw}` in in-memory evaluator")
  match q with
  | .select tn cols w ob lim off =>
      match getTbl tn with
      | .error e => (db, .error e)
      | .ok t =>
          let matched := t.rows.filter fun r => sqlValToBool (evalSqlExpr db [(tn.raw, t.columns, r)] 64 w)
          let out := (sliceRows lim off (sortRowsBy t.columns ob matched)).map (projectRow t.columns cols)
          (db, .ok { rows := out.toArray, affected := out.length })
  | .selectAll tn w ob lim off =>
      match getTbl tn with
      | .error e => (db, .error e)
      | .ok t =>
          let matched := t.rows.filter fun r => sqlValToBool (evalSqlExpr db [(tn.raw, t.columns, r)] 64 w)
          let out := sliceRows lim off (sortRowsBy t.columns ob matched)
          (db, .ok { rows := out.toArray, affected := out.length })
  | .count tn w =>
      match getTbl tn with
      | .error e => (db, .error e)
      | .ok t =>
          let n := (t.rows.filter fun r => sqlValToBool (evalSqlExpr db [(tn.raw, t.columns, r)] 64 w)).length
          (db, .ok { rows := #[#[.int (Int.ofNat n)]], affected := 1 })
  | .aggregate op tn col w =>
      match getTbl tn with
      | .error e => (db, .error e)
      | .ok t =>
          let vals := (t.rows.filter fun r => sqlValToBool (evalSqlExpr db [(tn.raw, t.columns, r)] 64 w)).filterMap fun r =>
            sqlValToInt? (getRowCol t.columns r col.raw)
          let aggVal : SqlVal := match op, vals with
            | .sum, vs => .int (vs.foldl (· + ·) 0)
            | .min, [] => .null
            | .min, v :: vs => .int (vs.foldl min v)
            | .max, [] => .null
            | .max, v :: vs => .int (vs.foldl max v)
          (db, .ok { rows := #[#[aggVal]], affected := 1 })
  | .joinSelect lt rt lCols rCols lJc rJc lW rW ob lim off =>
      match getTbl lt, getTbl rt with
      | .ok tL, .ok tR =>
          let pairs := tL.rows.flatMap fun rl =>
            if !sqlValToBool (evalSqlExpr db [(lt.raw, tL.columns, rl)] 64 lW) then []
            else
              let lv := getRowCol tL.columns rl lJc.raw
              tR.rows.filterMap fun rr =>
                if getRowCol tR.columns rr rJc.raw == lv && sqlValToBool (evalSqlExpr db [(rt.raw, tR.columns, rr), (lt.raw, tL.columns, rl)] 64 rW) then
                  some (rl, rr)
                else none
          let combinedCols := lCols.map (·.raw) ++ rCols.map (·.raw)
          let rows := pairs.map fun (rl, rr) =>
            (lCols.map (fun c => getRowCol tL.columns rl c.raw) ++ rCols.map (fun c => getRowCol tR.columns rr c.raw)).toArray
          let out := sliceRows lim off (sortRowsBy combinedCols ob rows)
          (db, .ok { rows := out.toArray, affected := out.length })
      | .error e, _ | _, .error e => (db, .error e)
  | .insert tn pairs ret =>
      match getTbl tn with
      | .error e => (db, .error e)
      | .ok t =>
          let newRow := buildRowFromPairs t.columns pairs
          let pkCols : List SqlIdent := match cfg.tables.find? (·.name.raw == tn.raw) with
            | some ts => (ts.columns.filter fun (c : ColumnSchema) => c.isPrimaryKey || c.isUnique).map (·.name)
            | none => []
          let dup := pkCols.any fun pc => t.rows.any fun r => getRowCol t.columns r pc.raw == getRowCol t.columns newRow pc.raw
          if dup then (db, .error ⟨409, s!"unique constraint violation on `{tn.raw}`"⟩)
          else
            let db' := db.upsertTable { t with rows := t.rows ++ [newRow] }
            let retRows := if ret.isEmpty then #[] else #[projectRow t.columns ret newRow]
            (db', .ok { rows := retRows, affected := 1 })
  | .insertOrIgnore tn pairs conflictCols ret =>
      match getTbl tn with
      | .error e => (db, .error e)
      | .ok t =>
          let newRow := buildRowFromPairs t.columns pairs
          let cCols : List SqlIdent := if !conflictCols.isEmpty then conflictCols
            else match cfg.tables.find? (·.name.raw == tn.raw) with
              | some ts => (ts.columns.filter fun (c : ColumnSchema) => c.isPrimaryKey || c.isUnique).map (·.name)
              | none => []
          let existsMatch :=
            if !conflictCols.isEmpty then t.rows.any (conflictMatches t.columns cCols · newRow)
            else cCols.any fun pc => t.rows.any fun r => getRowCol t.columns r pc.raw == getRowCol t.columns newRow pc.raw
          if existsMatch then (db, .ok { rows := #[], affected := 0 })
          else
            let db' := db.upsertTable { t with rows := t.rows ++ [newRow] }
            let retRows := if ret.isEmpty then #[] else #[projectRow t.columns ret newRow]
            (db', .ok { rows := retRows, affected := 1 })
  | .upsert tn pairs conflictCols updateCols conflictWhere? ret =>
      match getTbl tn with
      | .error e => (db, .error e)
      | .ok t =>
          let newRow := buildRowFromPairs t.columns pairs
          if t.rows.any (conflictMatches t.columns conflictCols · newRow) then
            let (updatedRows, retRows) := upsertRowsAux db tn t.columns conflictCols updateCols conflictWhere? ret newRow t.rows
            let db' := db.upsertTable { t with rows := updatedRows }
            (db', .ok { rows := retRows.toArray, affected := retRows.length })
          else
            let db' := db.upsertTable { t with rows := t.rows ++ [newRow] }
            let retRows := if ret.isEmpty then #[] else #[projectRow t.columns ret newRow]
            (db', .ok { rows := retRows, affected := 1 })
  | .update tn sets w ret =>
      match getTbl tn with
      | .error e => (db, .error e)
      | .ok t =>
          let (outRows, retRows, aff) := updateRowsAux db tn t.columns sets w ret t.rows
          let db' := db.upsertTable { t with rows := outRows }
          (db', .ok { rows := retRows.toArray, affected := aff })
  | .delete tn w ret =>
      match getTbl tn with
      | .error e => (db, .error e)
      | .ok t =>
          let (kept, retRows, aff) := deleteRowsAux db tn t.columns w ret t.rows
          let db' := db.upsertTable { t with rows := kept }
          (db', .ok { rows := retRows.toArray, affected := aff })

/-! ### 3. Pure `ThreadProg` Evaluator (`EvalEnv`, `EvalState`, `EvalTrace`, `evalProg`) -/

structure HttpStub where
  method : String := ""
  url    : String
  resp   : Except ApiError OutboundResp
  once   : Bool := false
deriving Inhabited

def HttpStub.ok (method url : String) (status : UInt32 := 200) (body : String := "") (headers : List (String × String) := []) (once : Bool := false) : HttpStub :=
  { method, url, resp := .ok { status, body := body.toUTF8, headers }, once }

def HttpStub.err (method url : String) (code : Nat := 502) (msg : String := "upstream error") (once : Bool := false) : HttpStub :=
  { method, url, resp := .error { code, message := msg }, once }

private def stubMatches (s : HttpStub) (req : OutboundReq) : Bool :=
  (s.method.isEmpty || Qed.Str.toUpper s.method == Qed.Str.toUpper req.method) &&
  (req.url == s.url || req.pathAndQuery == s.url || Qed.Str.startsWith req.url s.url)

private def matchHttpStub (req : OutboundReq) : List HttpStub → Option (Except ApiError OutboundResp × List HttpStub)
  | [] => none
  | s :: rest =>
      if stubMatches s req then some (s.resp, if s.once || rest.any (stubMatches · req) then rest else s :: rest)
      else match matchHttpStub req rest with
        | none => none
        | some (r, rest') => some (r, s :: rest')

structure EvalEnv where
  envVars   : List (String × String) := []
  nowMs     : UInt64 := 1700000000000
deriving Inhabited, DecidableEq

structure EvalTrace where
  httpCalls    : List OutboundReq := []
  dbQueries    : List SqlQuery := []
  cookies      : List SetCookie := []
  sseEvents    : List SseEvent := []
  wsBroadcasts : List WsEmit := []
  encryptCount : Nat := 0
  decryptCount : Nat := 0
deriving Inhabited, DecidableEq

structure EvalState (σ : Type) where
  shared     : σ
  db         : MemDb := []
  httpStubs  : List HttpStub := []
  txSaved    : List (UInt64 × MemDb) := []
  nextTxId   : UInt64 := 1
  rngCounter : Nat := 0
  trace      : EvalTrace := {}
deriving Inhabited

structure EvalResult (σ α : Type) where
  value : α
  state : EvalState σ
deriving Inhabited

private def stepEffect {σ : Type} (env : EvalEnv) (st : EvalState σ) (eff : ServerEffect) : EvalState σ × eff.Resp :=
  match eff with
  | .httpCall req =>
      let tr := { st.trace with httpCalls := st.trace.httpCalls ++ [req] }
      match matchHttpStub req st.httpStubs with
      | some (resp, stubs') => ({ st with httpStubs := stubs', trace := tr }, resp)
      | none => ({ st with trace := tr }, .error (ApiError.internal s!"unmocked HTTP {req.method} {req.url}"))
  | .dbExec cfg q =>
      let (db', res) := evalSqlQuery cfg st.db q
      ({ st with db := db', trace := { st.trace with dbQueries := st.trace.dbQueries ++ [q] } }, res)
  | .dbExecDdl cfg =>
      ({ st with db := st.db.ensureTables cfg.tables }, .ok ())
  | .dbTxBegin cfg =>
      let db' := st.db.ensureTables cfg.tables
      let tid := st.nextTxId
      ({ st with db := db', txSaved := (tid, db') :: st.txSaved, nextTxId := tid + 1 }, .ok tid)
  | .dbTxExec cfg _ q =>
      let (db', res) := evalSqlQuery cfg st.db q
      ({ st with db := db', trace := { st.trace with dbQueries := st.trace.dbQueries ++ [q] } }, res)
  | .dbTxCommit _ tid =>
      ({ st with txSaved := st.txSaved.filter (·.1 != tid) }, .ok ())
  | .dbTxRollback _ tid =>
      match st.txSaved.lookup tid with
      | some saved => ({ st with db := saved, txSaved := st.txSaved.filter (·.1 != tid) }, ())
      | none => (st, ())
  | .setCookie c =>
      ({ st with trace := { st.trace with cookies := st.trace.cookies ++ [c] } }, ())
  | .sendSse ev =>
      ({ st with trace := { st.trace with sseEvents := st.trace.sseEvents ++ [ev] } }, ())
  | .wsBroadcast t p =>
      ({ st with trace := { st.trace with wsBroadcasts := st.trace.wsBroadcasts ++ [{ topic := t, payload := p }] } }, ())
  | .readEnv v =>
      (st, env.envVars.lookup v)
  | .nowMs =>
      (st, env.nowMs)
  | .randomHex n =>
      ({ st with rngCounter := st.rngCounter + 1 }, mockRandomHex st.rngCounter n)
  | .randomBytes n =>
      ({ st with rngCounter := st.rngCounter + 1 }, mockRandomBytes st.rngCounter n)
  | .hmacSha256 k m =>
      (st, mockHmacSha256 k m)
  | .sha256 d =>
      (st, mockSha256 d)
  | .constEq a b =>
      (st, a == b)
  | .aeadEncrypt kEnv fb? aad pt =>
      ({ st with trace := { st.trace with encryptCount := st.trace.encryptCount + 1 } }, mockAeadEncrypt env.envVars kEnv fb? aad pt)
  | .aeadDecrypt kEnv fb? aad ct =>
      ({ st with trace := { st.trace with decryptCount := st.trace.decryptCount + 1 } }, mockAeadDecrypt env.envVars kEnv fb? aad ct)

def evalProg {σ α : Type} (env : EvalEnv) (st : EvalState σ) : ThreadProg σ α → EvalResult σ α
  | .pure a => ⟨a, st⟩
  | .io eff k =>
      let (st', resp) := stepEffect env st eff
      evalProg env st' (k resp)
  | .atomic step next =>
      let s0 := st.shared
      evalProg env { st with shared := step s0 } (next s0)

end Qed.Server.Eval
