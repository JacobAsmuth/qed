import Qed.Server.Db.Core
namespace Qed.Server.Db.HttpSql
/-! ## Pure Verified HTTP SQL Wire Encoders & Decoders (Cloudflare D1, Turso Hrana v2, Generic HTTP SQL) -/

private def jsonObjBytes (fs : List (String × Json)) : ByteArray := (Json.render (.obj fs)).toUTF8
private def typedObj (ty : String) (kv : List (String × Json) := []) : Json := .obj (("type", .str ty) :: kv)
private def firstObjAt (j : Json) (k : String) : Option Json := match j.arrAt k with | o@(.obj _) :: _ => some o | _ => none

def encodeGenericQueryBody (sql : String) (params : Array SqlVal) (dialect : SqlDialect) : ByteArray :=
  jsonObjBytes [("sql", .str sql), ("params", .arr (params.toList.map SqlVal.toTaggedJson)), ("dialect", .str (match dialect with | .postgres => "postgres" | .sqlite => "sqlite"))]
def encodeD1QueryBody (sql : String) (params : Array SqlVal) : ByteArray :=
  jsonObjBytes [("sql", .str sql), ("params", .arr (params.toList.map SqlVal.toPlainJson))]
def encodeTursoArg : SqlVal → Json
  | .null => typedObj "null" | .int i => typedObj "integer" [("value", .str (toString i))]
  | .text s => typedObj "text" [("value", .str s)] | .bool b => typedObj "integer" [("value", .str (if b then "1" else "0"))]
  | .bytes bs => typedObj "blob" [("base64", .str (Proto.encodeHex bs))]
def encodeTursoPipelineBody (sql : String) (params : Array SqlVal) : ByteArray :=
  jsonObjBytes [("requests", .arr [typedObj "execute" [("stmt", .obj [("sql", .str sql), ("args", .arr (params.toList.map encodeTursoArg))])], typedObj "close"])]

def decodeTursoCell : Json → Except String SqlVal
  | j@(.obj _) => match j.strAt? "type", j.get? "value" with
      | some "null", _ => .ok .null
      | some "integer", v => parseJsonIntCell v "turso bad int" "turso missing integer value"
      | some "text", some (.str s) => .ok (.text s) | some "text", _ => .error "turso missing text value"
      | some "float", some (.str s) => .ok (.text s) | some "float", some (.num n) => .ok (.int n.mantissa) | some "float", _ => .error "turso missing float value"
      | some "blob", _ => (j.strAt? "base64").elim (.error "turso missing blob payload") fun s => (Proto.decodeHex s).map .bytes
      | _, _ => .error "turso unknown cell type"
  | j => SqlVal.fromTaggedJson j

def decodeTursoResponse (raw : String) : Except String DbResult := do
  let j@(.obj _) ← Json.parse raw 128 | throw "turso response is not an object"
  let some first := firstObjAt j "results" | throw "turso missing results array"
  match first.strAt? "type" with
  | some "error" => throw ((first.pathStr? "error.message").getD "turso error")
  | some "ok" =>
      let some res@(.obj _) := first.atPath "response.result" | throw "turso missing result"
      return { rows := ← decodeJsonRows res "rows" (decodeJsonArrayRow decodeTursoCell "turso row is not an array") "turso rows is not an array", affected := (res.natAt? "affected_row_count").getD 0 }
  | _ => throw "turso unexpected result type"

def decodeD1Response (raw : String) (expectedCols : List String) : Except String DbResult := do
  let j@(.obj _) ← Json.parse raw 128 | throw "D1 response is not a JSON object"
  if j.boolAt? "success" == some false then throw "Cloudflare D1 query returned success=false"
  let some first := firstObjAt j "result" | decodeTaggedResultJson raw
  let rowDec : Json → Except String DbRow
    | .arr vals => (vals.mapM SqlVal.fromTaggedJson).map List.toArray
    | .obj rowObj => (if expectedCols.isEmpty then rowObj.mapM (SqlVal.fromTaggedJson ·.2)
        else expectedCols.mapM fun c => (rowObj.lookup c).elim (.ok .null) SqlVal.fromTaggedJson).map List.toArray
    | _ => .error "D1 row is not object or array"
  return { rows := ← decodeJsonRows first "results" rowDec "D1 results is not an array", affected := (first.get? "meta" |>.bind (·.natAt? "changes")).getD 0 }

def queryExpectedCols : SqlQuery → List String
  | .select _ cols _ _ _ _ | .insert _ _ cols | .upsert _ _ _ _ _ cols | .update _ _ _ cols | .delete _ _ cols => cols.map (·.raw)
  | .joinSelect _ _ lc rc _ _ _ _ _ _ _ => lc.map (·.raw) ++ rc.map (·.raw) | .count _ _ | .aggregate _ _ _ _ => []
end Qed.Server.Db.HttpSql
