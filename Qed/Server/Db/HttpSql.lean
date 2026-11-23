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
  | j@(.obj _) =>
      match jsonStrAt j "type" with
      | some "null"    => .ok .null
      | some "integer" => parseJsonIntCell (j.get? "value") "turso bad int" "turso missing integer value"
      | some "text"    =>
          match jsonStrAt j "value" with
          | some s => .ok (.text s)
          | none   => .error "turso missing text value"
      | some "float"   =>
          match j.get? "value" with
          | some (.str s) => .ok (.text s)
          | some (.num n) => .ok (.int n.mantissa)
          | _ => .error "turso missing float value"
      | some "blob"    =>
          match jsonStrAt j "base64" with
          | some s => (Proto.decodeHex s).map .bytes
          | none   => .error "turso missing blob payload"
      | _ => .error "turso unknown cell type"
  | j => SqlVal.fromTaggedJson j

/-- Decodes a Turso Hrana v2 `/v2/pipeline` response into `DbResult`. -/
def decodeTursoResponse (raw : String) : Except String DbResult := do
  let j@(.obj _) ← Json.parse raw 128 | return ← .error "turso response is not an object"
  let some (.arr (first :: _)) := j.get? "results" | return ← .error "turso missing results array"
  let .obj _ := first | return ← .error "turso result entry is not an object"
  match jsonStrAt first "type" with
  | some "error" =>
      .error ((first.get? "error" |>.bind (jsonStrAt · "message")).getD "turso error")
  | some "ok" =>
      let some resp@(.obj _) := first.get? "response" | return ← .error "turso missing response"
      let some res@(.obj _) := resp.get? "result" | return ← .error "turso missing result"
      let rows ← decodeJsonRows res "rows"
        (decodeJsonArrayRow decodeTursoCell "turso row is not an array") "turso rows is not an array"
      return { rows, affected := jsonNatAt res "affected_row_count" }
  | _ => .error "turso unexpected result type"

/-- Decodes a Cloudflare D1 REST response (`{success, result: [{results: [...], meta: {changes}}]}`)
    ordering row columns by `expectedCols` when objects are returned. -/
def decodeD1Response (raw : String) (expectedCols : List String) : Except String DbResult := do
  let j@(.obj _) ← Json.parse raw 128 | return ← .error "D1 response is not a JSON object"
  if let some (.bool false) := j.get? "success" then
    return ← .error "Cloudflare D1 query returned success=false"
  match j.get? "result" with
  | some (.arr (first :: _)) =>
      let .obj _ := first | return ← .error "D1 result entry is not an object"
      let affected := (first.get? "meta").map (jsonNatAt · "changes") |>.getD 0
      let rows ← decodeJsonRows first "results" (fun
        | .arr vals => (vals.mapM SqlVal.fromTaggedJson).map List.toArray
        | .obj rowObj =>
            (if expectedCols.isEmpty then rowObj.mapM (SqlVal.fromTaggedJson ·.2)
             else expectedCols.mapM fun c =>
               match rowObj.lookup c with | some v => SqlVal.fromTaggedJson v | none => .ok .null)
              |>.map List.toArray
        | _ => .error "D1 row is not object or array") "D1 results is not an array"
      return { rows, affected }
  | _ => decodeTaggedResultJson raw

def queryExpectedCols : SqlQuery → List String
  | .select _ cols _ _ _ _ => cols.map (·.raw)
  | .count _ _             => []
  | .aggregate _ _ _ _     => []
  | .joinSelect _ _ lc rc _ _ _ _ _ _ _ => lc.map (·.raw) ++ rc.map (·.raw)
  | .insert _ _ ret        => ret.map (·.raw)
  | .update _ _ _ ret      => ret.map (·.raw)
  | .delete _ _ ret        => ret.map (·.raw)

end Qed.Server.Db.HttpSql
