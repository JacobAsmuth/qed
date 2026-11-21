import Qed.Server.Core
import Qed.Server.Db.Core

namespace Qed.Server.Db.HttpSql

/-! ## Pure Verified HTTP SQL Wire Encoders & Decoders
    Supports:
    1. **Cloudflare D1** REST API (`/client/v4/accounts/:acc/d1/database/:db/query`)
    2. **Turso / LibSQL** Hrana HTTP v2 (`/v2/pipeline`)
    3. **Generic Qed HTTP SQL** (`POST /query` with `{sql, params, dialect}`)

    Executes cleanly on top of Qed's verified outbound HTTP/1.1 + `rustls` pool. -/

/-- Encodes a Qed HTTP SQL request body (`{sql, params, dialect}`). -/
def encodeGenericQueryBody (sql : String) (params : Array SqlVal) (dialect : SqlDialect) : ByteArray :=
  let dStr := match dialect with | .postgres => "postgres" | .sqlite => "sqlite"
  let j : Json := .obj [
    ("sql", .str sql),
    ("params", .arr (params.toList.map SqlVal.toTaggedJson)),
    ("dialect", .str dStr)
  ]
  (Json.render j).toUTF8

/-- Encodes a Cloudflare D1 REST API query body (`{sql, params}`). -/
def encodeD1QueryBody (sql : String) (params : Array SqlVal) : ByteArray :=
  let j : Json := .obj [
    ("sql", .str sql),
    ("params", .arr (params.toList.map SqlVal.toPlainJson))
  ]
  (Json.render j).toUTF8

/-- Encodes a Turso / LibSQL Hrana v2 `/v2/pipeline` single-statement execute request. -/
def encodeTursoArg : SqlVal → Json
  | .null     => .obj [("type", .str "null")]
  | .int i    => .obj [("type", .str "integer"), ("value", .str (toString i))]
  | .text s   => .obj [("type", .str "text"), ("value", .str s)]
  | .bool b   => .obj [("type", .str "integer"), ("value", .str (if b then "1" else "0"))]
  | .bytes bs => .obj [("type", .str "blob"), ("base64", .str (Proto.encodeHex bs))]

def encodeTursoPipelineBody (sql : String) (params : Array SqlVal) : ByteArray :=
  let stmt : Json := .obj [
    ("sql", .str sql),
    ("args", .arr (params.toList.map encodeTursoArg))
  ]
  let reqs : Json := .arr [
    .obj [("type", .str "execute"), ("stmt", stmt)],
    .obj [("type", .str "close")]
  ]
  (Json.render (.obj [("requests", reqs)])).toUTF8

/-- Decodes a single Turso Hrana v2 cell (`{type, value}`). -/
def decodeTursoCell : Json → Except String SqlVal
  | .obj fs =>
      match fs.lookup "type" with
      | some (.str "null") => .ok .null
      | some (.str "integer") =>
          match fs.lookup "value" with
          | some (.str s) => match s.toInt? with | some i => .ok (.int i) | none => .error s!"turso bad int: {s}"
          | some (.num n) => .ok (.int n.mantissa)
          | _ => .error "turso missing integer value"
      | some (.str "text") =>
          match fs.lookup "value" with
          | some (.str s) => .ok (.text s)
          | _ => .error "turso missing text value"
      | some (.str "float") =>
          match fs.lookup "value" with
          | some (.str s) => .ok (.text s)
          | some (.num n) => .ok (.int n.mantissa)
          | _ => .error "turso missing float value"
      | some (.str "blob") =>
          match fs.lookup "base64" with
          | some (.str s) => (Proto.decodeHex s).map .bytes
          | _ => .error "turso missing blob payload"
      | _ => .error "turso unknown cell type"
  | j => SqlVal.fromTaggedJson j

/-- Decodes a Turso Hrana v2 `/v2/pipeline` response into `DbResult`. -/
def decodeTursoResponse (raw : String) : Except String DbResult := do
  let j ← Json.parse raw 128
  match j with
  | .obj fs =>
      match fs.lookup "results" with
      | some (.arr (first :: _)) =>
          match first with
          | .obj rfs =>
              match rfs.lookup "type" with
              | some (.str "error") =>
                  let msg := match rfs.lookup "error" with
                    | some (.obj efs) => match efs.lookup "message" with | some (.str m) => m | _ => "turso error"
                    | _ => "turso error"
                  .error msg
              | some (.str "ok") =>
                  match rfs.lookup "response" with
                  | some (.obj respFs) =>
                      match respFs.lookup "result" with
                      | some (.obj resFs) =>
                          let affected : Nat := match resFs.lookup "affected_row_count" with
                            | some (.num n) => if 0 ≤ n.mantissa then n.mantissa.toNat else 0
                            | _ => 0
                          let rowsList ← match resFs.lookup "rows" with
                            | some (.arr rs) =>
                                rs.mapM fun rj =>
                                  match rj with
                                  | .arr cells => (cells.mapM decodeTursoCell).map List.toArray
                                  | _ => .error "turso row is not an array"
                            | none => .ok []
                            | _ => .error "turso rows is not an array"
                          return { rows := rowsList.toArray, affected }
                      | _ => .error "turso missing result"
                  | _ => .error "turso missing response"
              | _ => .error "turso unexpected result type"
          | _ => .error "turso result entry is not an object"
      | _ => .error "turso missing results array"
  | _ => .error "turso response is not an object"

/-- Decodes a Cloudflare D1 REST response (`{success, result: [{results: [...], meta: {changes}}]}`)
    ordering row columns by `expectedCols` when objects are returned. -/
def decodeD1Response (raw : String) (expectedCols : List String) : Except String DbResult := do
  let j ← Json.parse raw 128
  match j with
  | .obj fs =>
      match fs.lookup "success" with
      | some (.bool false) => .error "Cloudflare D1 query returned success=false"
      | _ => pure ()
      match fs.lookup "result" with
      | some (.arr (first :: _)) =>
          match first with
          | .obj rfs =>
              let affected : Nat := match rfs.lookup "meta" with
                | some (.obj mfs) =>
                    match mfs.lookup "changes" with
                    | some (.num n) => if 0 ≤ n.mantissa then n.mantissa.toNat else 0
                    | _ => 0
                | _ => 0
              let rowsList ← match rfs.lookup "results" with
                | some (.arr rs) =>
                    rs.mapM fun rj =>
                      match rj with
                      | .arr vals => (vals.mapM SqlVal.fromTaggedJson).map List.toArray
                      | .obj rowObj =>
                          if expectedCols.isEmpty then
                            (rowObj.mapM fun (kv : String × Json) => SqlVal.fromTaggedJson kv.2).map List.toArray
                          else
                            (expectedCols.mapM fun c =>
                              match rowObj.lookup c with
                              | some v => SqlVal.fromTaggedJson v
                              | none   => .ok .null).map List.toArray
                      | _ => .error "D1 row is not object or array"
                | none => .ok []
                | _ => .error "D1 results is not an array"
              return { rows := rowsList.toArray, affected }
          | _ => .error "D1 result entry is not an object"
      | _ =>
          -- Fallback to generic tagged result format
          decodeTaggedResultJson raw
  | _ => .error "D1 response is not a JSON object"

def queryExpectedCols : SqlQuery → List String
  | .select _ cols _ _ _ _ => cols.map (·.raw)
  | .count _ _             => []
  | .aggregate _ _ _ _     => []
  | .joinSelect _ _ lc rc _ _ _ _ _ _ _ => lc.map (·.raw) ++ rc.map (·.raw)
  | .insert _ _ ret        => ret.map (·.raw)
  | .update _ _ _ ret      => ret.map (·.raw)
  | .delete _ _ ret        => ret.map (·.raw)

end Qed.Server.Db.HttpSql
