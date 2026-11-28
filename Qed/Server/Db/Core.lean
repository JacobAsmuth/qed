import Qed.Field
import Qed.Json.Lawful
import Qed.Proto.Lawful
import Qed.Date
import Qed.Cloud.Env

namespace Qed.Server.Db

/-! ## Typed SQL Values & Wire Codecs (`SqlVal`, `ToSql`, `FromSql`) -/

inductive SqlVal where
  | null | int (v : Int) | text (v : String) | bool (v : Bool) | bytes (v : ByteArray)
deriving Inhabited, DecidableEq

private def sqlValToProtoFields : SqlVal → List (Nat × Proto.WireVal)
  | .null    => [(1, .varint 0)]
  | .int v   => [(2, ToProto.toProtoVal v)]
  | .text v  => [(3, ToProto.toProtoVal v)]
  | .bool v  => [(4, ToProto.toProtoVal v)]
  | .bytes v => [(5, ToProto.toProtoVal v)]

private def sqlValFromProtoFields (fs : List (Nat × Proto.WireVal)) : Except String SqlVal :=
  match Proto.lookupField 1 fs, Proto.lookupField 2 fs, Proto.lookupField 3 fs, Proto.lookupField 4 fs, Proto.lookupField 5 fs with
  | some _, _, _, _, _ => .ok .null
  | none, some w, _, _, _ => (FromProto.fromProtoVal (α := Int) w).map .int
  | none, none, some w, _, _ => (FromProto.fromProtoVal (α := String) w).map .text
  | none, none, none, some w, _ => (FromProto.fromProtoVal (α := Bool) w).map .bool
  | none, none, none, none, some w => (FromProto.fromProtoVal (α := ByteArray) w).map .bytes
  | none, none, none, none, none => .error "protobuf: missing SqlVal branch"

instance : ToProto SqlVal := .ofFields sqlValToProtoFields
instance : FromProto SqlVal := .ofFields sqlValFromProtoFields
instance : LawfulProto SqlVal := .ofFields sqlValToProtoFields sqlValFromProtoFields
  (by intro v _ h; cases v <;> (rw [List.mem_singleton.1 h]; exact Nat.zero_lt_succ _))
  (by intro v; cases v <;> simp [sqlValToProtoFields, sqlValFromProtoFields, Proto.lookupField, Except.map])

instance : ToJson SqlVal := ⟨fun
  | .null => .null | .int i => toJson i | .text s => .str s | .bool b => .bool b
  | .bytes bs => .obj [("bytes", toJson bs)]⟩
instance : FromJson SqlVal := ⟨fun
  | .null => .ok .null | j@(.num _) => (fromJson (α := Int) j).map .int
  | .str s => .ok (.text s) | .bool b => .ok (.bool b)
  | j@(.obj _) => (j.field "bytes" >>= fromJson).map .bytes
  | _ => .error "expected SQL JSON value"⟩

class ToSql (α : Type) where toSql : α → SqlVal
class FromSql (α : Type) where fromSql : SqlVal → Except String α

private def fromSqlErr {α : Type} (ty : String) : SqlVal → Except String α
  | .null => .error s!"expected {ty}, got NULL"
  | .bytes _ => .error s!"expected {ty}, got BLOB"
  | _ => .error s!"expected {ty}"

instance : ToSql String := ⟨.text⟩
instance : FromSql String := ⟨fun
  | .text s => .ok s | .int i => .ok (toString i) | .bool b => .ok (if b then "true" else "false") | v => fromSqlErr "TEXT" v⟩
instance : ToSql Int := ⟨.int⟩
instance : FromSql Int := ⟨fun
  | .int i => .ok i | .bool b => .ok (if b then 1 else 0)
  | .text s => (Qed.Str.parseInt? s).elim (.error s!"invalid INT: {s}") .ok | v => fromSqlErr "INT" v⟩
instance : ToSql Nat := ⟨fun n => .int (Int.ofNat n)⟩
instance : FromSql Nat := ⟨fun v => do
  let i ← FromSql.fromSql (α := Int) v
  if 0 ≤ i then .ok i.toNat else .error s!"expected non-negative Nat, got {i}"⟩
instance : ToSql Bool := ⟨.bool⟩
instance : FromSql Bool := ⟨fun
  | .bool b => .ok b | .int i => .ok (i != 0)
  | .text s => if s == "true" || s == "t" || s == "1" then .ok true
      else if s == "false" || s == "f" || s == "0" then .ok false else .error s!"invalid BOOL: {s}"
  | v => fromSqlErr "BOOL" v⟩
def decodeSqlHex (s : String) : Except String ByteArray :=
  Proto.decodeHex (if s.startsWith "\\x" then String.ofList (s.toList.drop 2) else s)

instance : ToSql ByteArray := ⟨.bytes⟩
instance : FromSql ByteArray := ⟨fun
  | .bytes bs => .ok bs | .text s => decodeSqlHex s | v => fromSqlErr "BLOB" v⟩
instance [ToSql α] : ToSql (Option α) := ⟨fun | none => .null | some a => ToSql.toSql a⟩
instance [FromSql α] : FromSql (Option α) := ⟨fun | .null => .ok none | v => (FromSql.fromSql (α := α) v).map some⟩
instance {α : Type} [Qed.StringEnum α] : ToSql α := ⟨fun x => .text (Qed.StringEnum.toWire x)⟩
instance {α : Type} [Qed.StringEnum α] : FromSql α := ⟨fun v => (FromSql.fromSql (α := String) v).bind Qed.StringEnum.ofWire⟩
instance : ToSql Qed.Date := ⟨fun d => .text (toString d)⟩
instance : FromSql Qed.Date := ⟨fun v => (FromSql.fromSql (α := String) v).bind fun s => (Qed.Date.parse? s).elim (.error s!"invalid Date '{s}' (expected YYYY-MM-DD)") .ok⟩
instance {α : Type} {p : α → Prop} [ToSql α] : ToSql (Qed.Field p) := ⟨fun f => ToSql.toSql f.val⟩
instance {α : Type} {p : α → Prop} [FromSql α] [DecidablePred p] : FromSql (Qed.Field p) :=
  ⟨fun v => (FromSql.fromSql (α := α) v).bind (Qed.Field.parse p "database column value violated field constraint")⟩
@[inline] def toSqlLike {Row α : Type} [ToSql α] (_proj : Row → α) (v : α) : SqlVal := ToSql.toSql v

class ToSqlList (α : Type) where toSqlList : α → List SqlVal
instance [ToSql α] : ToSqlList (List α) := ⟨List.map ToSql.toSql⟩
instance [ToSql α] : ToSqlList (Array α) := ⟨fun xs => xs.toList.map ToSql.toSql⟩

def escapeLikePattern (s : String) : String :=
  String.ofList (s.toList.flatMap fun c => if c == '!' || c == '%' || c == '_' then ['!', c] else [c])
def endsWithLikeVal (s : String) : SqlVal := .text ("%" ++ escapeLikePattern s)

/-! ## Validated SQL Identifiers (`SqlIdent` & Injection Closure) -/

@[inline] def isSqlIdentHeadChar (c : Char) : Bool := let n := c.toNat; (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || n == 95
@[inline] def isSqlIdentBodyChar (c : Char) : Bool := let n := c.toNat; (48 ≤ n && n ≤ 57) || isSqlIdentHeadChar c
def isSafeSqlIdent (s : String) : Bool :=
  match s.toList with | [] => false | c :: cs => isSqlIdentHeadChar c && cs.all isSqlIdentBodyChar && decide (cs.length < 63)

structure SqlIdent where
  raw   : String
  valid : isSafeSqlIdent raw = true
deriving DecidableEq
instance : Inhabited SqlIdent := ⟨⟨"id", rfl⟩⟩
instance : Repr SqlIdent := ⟨fun id _ => repr id.raw⟩

/-- Safely validate a runtime string into a SQL-injection-proof `SqlIdent`. -/
def SqlIdent.ofString? (s : String) : Option SqlIdent :=
  if h : isSafeSqlIdent s = true then some ⟨s, h⟩ else none

@[simp] theorem SqlIdent.ofString?_isSome (s : String) :
    (SqlIdent.ofString? s).isSome = isSafeSqlIdent s := by
  unfold SqlIdent.ofString?; split <;> simp_all

@[simp] theorem SqlIdent.ofString?_isSome_iff (s : String) :
    (SqlIdent.ofString? s).isSome = true ↔ isSafeSqlIdent s = true := by
  rw [SqlIdent.ofString?_isSome]

theorem SqlIdent.ofString?_raw {s : String} {id : SqlIdent} (h : SqlIdent.ofString? s = some id) :
    id.raw = s := by
  unfold SqlIdent.ofString? at h; split at h
  · cases h; rfl
  · cases h

@[simp] theorem SqlIdent.ofString?_eq_some_iff (s : String) (id : SqlIdent) :
    SqlIdent.ofString? s = some id ↔ id.raw = s := by
  constructor
  · exact SqlIdent.ofString?_raw
  · intro heq; subst heq; unfold SqlIdent.ofString?; simp [id.valid]

@[simp] theorem SqlIdent.ofString?_raw_self (id : SqlIdent) :
    SqlIdent.ofString? id.raw = some id :=
  (SqlIdent.ofString?_eq_some_iff id.raw id).2 rfl

private def parseSqlIdentWire (pfx s : String) : Except String SqlIdent :=
  (SqlIdent.ofString? s).elim (.error s!"{pfx}invalid SQL identifier `{s}`") .ok
private theorem parseSqlIdentWire_raw (pfx : String) (id : SqlIdent) : parseSqlIdentWire pfx id.raw = .ok id := by
  simp [parseSqlIdentWire, SqlIdent.ofString?_raw_self]
instance : ToJson SqlIdent := .ofEquiv SqlIdent.raw
instance : FromJson SqlIdent := .ofRetract (parseSqlIdentWire "")
instance : LawfulJson SqlIdent := .ofRetract SqlIdent.raw (parseSqlIdentWire "") (parseSqlIdentWire_raw "")
instance : NonNullJson SqlIdent := ⟨nofun⟩
instance : ToProto SqlIdent := .ofEquiv SqlIdent.raw
instance : FromProto SqlIdent := .ofRetract (parseSqlIdentWire "protobuf: ")
instance : LawfulProto SqlIdent := .ofRetract SqlIdent.raw (parseSqlIdentWire "protobuf: ") (parseSqlIdentWire_raw "protobuf: ")

/-- Compile-time validated `SqlIdent` literal macro (`sql!"col_name"`).
    Uses `noWs` so `sql` remains unreserved as an ordinary identifier. -/
syntax:max "sql!" noWs str : term
macro_rules | `(sql!$s:str) => `(Qed.Server.Db.SqlIdent.mk $s rfl)

theorem isSafeSqlIdent_all_body {s : String} (h : isSafeSqlIdent s = true) :
    ∀ c ∈ s.toList, isSqlIdentBodyChar c = true := by
  unfold isSafeSqlIdent at h
  rcases hcs : s.toList with _ | ⟨hd, tl⟩
  · rw [hcs] at h; contradiction
  · rw [hcs] at h; simp only [Bool.and_eq_true, List.all_eq_true] at h
    exact fun c hc => (List.mem_cons.1 hc).elim (fun h1 => by subst h1; simp [isSqlIdentBodyChar, h.1.1]) (h.1.2 c)

/-- No validated `SqlIdent` can ever contain quotes, semicolons, dashes, slashes, spaces, or NUL bytes. -/
theorem isSafeSqlIdent_no_inject (id : SqlIdent) :
    ∀ c ∈ id.raw.toList,
      c ≠ '\'' ∧ c ≠ '"' ∧ c ≠ ';' ∧ c ≠ '-' ∧ c ≠ '/' ∧ c ≠ '\\' ∧ c ≠ ' ' ∧ c ≠ '\x00' := by
  intro c hc; have hb := isSafeSqlIdent_all_body id.valid c hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro heq; subst heq; simp [isSqlIdentBodyChar, isSqlIdentHeadChar] at hb)

theorem noAsciiChar_of_bytes (b : UInt8) (hb : b.toNat < 128) (s : String)
    (h : s.toByteArray.data.toList.all (· != b) = true) : ∀ c ∈ s.toList, c ≠ Char.ofNat b.toNat := by
  intro c hc heq; subst heq
  have hba : s.toByteArray = s.toList.utf8Encode := by rw [← String.toByteArray_ofList, String.ofList_toList]
  rw [hba, List.all_eq_true] at h
  have hval : (Char.ofNat b.toNat).val = b.toUInt32 := by
    have hv : Nat.isValidChar b.toNat := Or.inl (by omega)
    simp only [Char.ofNat, hv, ↓reduceDIte, UInt8.toUInt32]; rfl
  have henc : String.utf8EncodeChar (Char.ofNat b.toNat) = [b] := by
    have hsz : (Char.ofNat b.toNat).utf8Size = 1 := by
      simp only [Char.utf8Size, hval]; split
      · rfl
      · rename_i hge; exfalso; apply hge; change b.toNat ≤ 0x7f; omega
    rw [String.utf8EncodeChar_eq_singleton hsz, hval]
    congr 1; exact UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by
      simp only [UInt32.toBitVec_toUInt8, UInt8.toBitVec_toUInt32, BitVec.toNat_setWidth]; omega))
  have hmem : b ∈ s.toList.utf8Encode.data.toList := by
    simp only [List.utf8Encode, List.data_toByteArray, List.toList_toArray, List.mem_flatMap]
    exact ⟨Char.ofNat b.toNat, hc, by rw [henc]; exact List.mem_cons_self ..⟩
  simpa using h b hmem

private abbrev NoSemi (s : String) : Prop := ∀ c ∈ s.toList, c ≠ ';'
private theorem NoSemi.empty : NoSemi "" := fun _ h => nomatch h
private theorem NoSemi.app {a b : String} (ha : NoSemi a) (hb : NoSemi b) : NoSemi (a ++ b) := fun c hc =>
  (List.mem_append.1 (String.toList_append ▸ hc)).elim (ha c) (hb c)
private theorem NoSemi.lit {s : String} (h : s.toByteArray.data.toList.all (· != 59) = true := by decide +kernel) : NoSemi s :=
  noAsciiChar_of_bytes 59 (by decide) s h
private theorem NoSemi.appL {a s : String} (ha : NoSemi a) (h : s.toByteArray.data.toList.all (· != 59) = true := by decide +kernel) : NoSemi (a ++ s) :=
  ha.app (NoSemi.lit h)
private theorem NoSemi.lApp {s b : String} (hb : NoSemi b) (h : s.toByteArray.data.toList.all (· != 59) = true := by decide +kernel) : NoSemi (s ++ b) :=
  (NoSemi.lit h).app hb

def SqlIdent.quoteIdent (id : SqlIdent) : String := "\"" ++ id.raw ++ "\""
theorem SqlIdent.quoteIdent_no_semicolon (id : SqlIdent) : ∀ c ∈ id.quoteIdent.toList, c ≠ ';' :=
  (NoSemi.lApp fun c hc => (isSafeSqlIdent_no_inject id c hc).2.2.1).appL

/-! ## Typed Parameterized SQL AST (`SqlExpr`, `SqlQuery`, `SqlDialect`) -/

inductive SqlDialect  where | postgres | sqlite deriving Inhabited, DecidableEq
inductive SqlBinOp    where | eq | ne | lt | le | gt | ge | and | or | add | sub | mul deriving Inhabited, DecidableEq
inductive SqlOrderDir where | asc | desc deriving Inhabited, DecidableEq
inductive SqlAggOp    where | sum | min | max deriving Inhabited, DecidableEq

@[inline] private def SqlDialect.pick (d : SqlDialect) (pg sq : String) : String := match d with | .postgres => pg | .sqlite => sq
private theorem SqlDialect.pick_no_semi (d : SqlDialect) {pg sq : String} (h1 : NoSemi pg) (h2 : NoSemi sq) : NoSemi (d.pick pg sq) := by
  cases d <;> assumption

def SqlBinOp.render : SqlBinOp → String
  | .eq  => " = "  | .ne  => " <> " | .lt  => " < "  | .le  => " <= "
  | .gt  => " > "  | .ge  => " >= " | .and => " AND " | .or  => " OR "
  | .add => " + "  | .sub => " - "  | .mul => " * "
def SqlAggOp.render : SqlAggOp → String | .sum => "SUM" | .min => "MIN" | .max => "MAX"
theorem SqlBinOp.render_no_semicolon (op : SqlBinOp) : ∀ c ∈ op.render.toList, c ≠ ';' := by cases op <;> exact NoSemi.lit
theorem SqlAggOp.render_no_semicolon (op : SqlAggOp) : ∀ c ∈ op.render.toList, c ≠ ';' := by cases op <;> exact NoSemi.lit

inductive SqlColType where | text | int | bool | bytes deriving Inhabited, DecidableEq
def SqlColType.render (d : SqlDialect) : SqlColType → String
  | .text => "TEXT" | .int => d.pick "BIGINT" "INTEGER" | .bool => d.pick "BOOLEAN" "INTEGER" | .bytes => d.pick "BYTEA" "BLOB"
private theorem SqlColType.render_no_semicolon (d : SqlDialect) (t : SqlColType) : NoSemi (t.render d) := by
  cases t <;> dsimp only [SqlColType.render] <;> first | exact NoSemi.lit | exact d.pick_no_semi NoSemi.lit NoSemi.lit

inductive SqlExpr where
  | litTrue | litFalse | col (name : SqlIdent) | qualCol (tableOrAlias name : SqlIdent) | param (val : SqlVal)
  | binOp (op : SqlBinOp) (lhs rhs : SqlExpr)
  | not (e : SqlExpr) | isNull (e : SqlExpr) | isNotNull (e : SqlExpr) | strLen (e : SqlExpr)
  | like (lhs rhs : SqlExpr) | startsWith (lhs rhs : SqlExpr) | contains (lhs rhs : SqlExpr)
  | inList (lhs : SqlExpr) (vals : List SqlVal)
  | existsSubquery (subTable alias : SqlIdent) (pred : SqlExpr)
deriving Inhabited, DecidableEq

/-- Exact SQL lowering for `some(col) == opt` / `some(col) != opt` against a runtime `Option` parameter. -/
@[inline] def sqlEqSome {α : Type} [ToSql α] (lhs : SqlExpr) (opt : Option α) (neg : Bool := false) : SqlExpr :=
  match opt with
  | none => if neg then .litTrue else .litFalse
  | some v => .binOp (if neg then .ne else .eq) lhs (.param (ToSql.toSql v))

/-- Replaces every runtime `SqlVal` payload with `.null`, preserving the exact AST skeleton. -/
def SqlExpr.eraseVals : SqlExpr → SqlExpr
  | .litTrue => .litTrue | .litFalse => .litFalse | .col name => .col name | .qualCol t c => .qualCol t c | .param _ => .param .null
  | .binOp op l r => .binOp op l.eraseVals r.eraseVals | .not e => .not e.eraseVals
  | .isNull e => .isNull e.eraseVals | .isNotNull e => .isNotNull e.eraseVals | .strLen e => .strLen e.eraseVals
  | .like l r => .like l.eraseVals r.eraseVals | .startsWith l r => .startsWith l.eraseVals r.eraseVals
  | .contains l r => .contains l.eraseVals r.eraseVals | .inList l vs => .inList l.eraseVals (vs.map fun _ => .null)
  | .existsSubquery st al p => .existsSubquery st al p.eraseVals

abbrev SqlExpr.sameShape (e₁ e₂ : SqlExpr) : Prop := e₁.eraseVals = e₂.eraseVals
def placeholder (d : SqlDialect) (idx : Nat) : String := d.pick "$" "?" ++ toString idx

abbrev nat_toString_digits := Qed.Str.nat_toString_digits

private theorem nat_toString_no_semicolon (n : Nat) : NoSemi (toString n) :=
  fun c hc heq => absurd (heq ▸ nat_toString_digits n c hc) (by decide)
theorem placeholder_no_semicolon (d : SqlDialect) (idx : Nat) : ∀ c ∈ (placeholder d idx).toList, c ≠ ';' :=
  (d.pick_no_semi NoSemi.lit NoSemi.lit).app (nat_toString_no_semicolon idx)

/-- Generic comma-separated SQL clause compiler threading bound parameters. -/
private def compileSepList {α : Type} (f : α → Array SqlVal → String × Array SqlVal) :
    List α → Array SqlVal → String × Array SqlVal
  | [], p => ("", p) | [x], p => f x p
  | x :: y :: rest, p => let (sx, p1) := f x p; let (tail, p2) := compileSepList f (y :: rest) p1; (sx ++ ", " ++ tail, p2)

private abbrev SameCompile (r₁ r₂ : String × Array SqlVal) : Prop := r₁.1 = r₂.1 ∧ r₁.2.size = r₂.2.size

private theorem compileSepList_eraseVals {α : Type} (f : α → Array SqlVal → String × Array SqlVal) (g : α → α)
    (hf : ∀ a p₁ p₂, p₁.size = p₂.size → SameCompile (f a p₁) (f (g a) p₂)) :
    ∀ (xs : List α) (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
      SameCompile (compileSepList f xs p₁) (compileSepList f (xs.map g) p₂)
  | [], _, _, h => ⟨rfl, h⟩ | [x], p₁, p₂, h => hf x p₁ p₂ h
  | x :: y :: rest, p₁, p₂, h =>
      let ⟨h1, h2⟩ := hf x p₁ p₂ h; let ⟨h3, h4⟩ := compileSepList_eraseVals f g hf (y :: rest) _ _ h2
      ⟨by simp [compileSepList, h1, h3], h4⟩

private theorem compileSepList_no_semicolon {α : Type} (f : α → Array SqlVal → String × Array SqlVal)
    (hf : ∀ a p, NoSemi (f a p).1) : ∀ (xs : List α) (p : Array SqlVal), NoSemi (compileSepList f xs p).1
  | [], _ => fun _ h => nomatch h | [x], p => hf x p
  | x :: y :: rest, p => (hf x p).appL.app (compileSepList_no_semicolon f hf (y :: rest) (f x p).2)

private def compileInParams (d : SqlDialect) : List SqlVal → Array SqlVal → String × Array SqlVal :=
  compileSepList (α := SqlVal) fun v p => (placeholder d (p.size + 1), p.push v)
private theorem compileInParams_eraseVals (d : SqlDialect) :
    ∀ (vs : List SqlVal) (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
      SameCompile (compileInParams d vs p₁) (compileInParams d (vs.map fun _ => .null) p₂) :=
  compileSepList_eraseVals (α := SqlVal) _ (fun _ => .null) fun _ _ _ h => ⟨by simp [h], by simp [h]⟩
private theorem compileInParams_no_semicolon (d : SqlDialect) :
    ∀ (vs : List SqlVal) (p : Array SqlVal), NoSemi (compileInParams d vs p).1 :=
  compileSepList_no_semicolon (α := SqlVal) _ fun _ p => placeholder_no_semicolon d (p.size + 1)

private def zipValsWithTypes : List SqlVal → List SqlColType → List (SqlVal × Option SqlColType)
  | [], _ => [] | v :: vs, [] => (v, none) :: zipValsWithTypes vs []
  | v :: vs, t :: ts => (v, some t) :: zipValsWithTypes vs ts
private theorem zipValsWithTypes_map_null : ∀ (vs : List SqlVal) (ts : List SqlColType),
    zipValsWithTypes (vs.map fun _ => .null) ts = (zipValsWithTypes vs ts).map fun (_, ty?) => (.null, ty?)
  | [], _ => rfl
  | _ :: vs, [] => congrArg _ (zipValsWithTypes_map_null vs [])
  | _ :: vs, _ :: ts => congrArg _ (zipValsWithTypes_map_null vs ts)
private def compileSelectParams (d : SqlDialect) : List (SqlVal × Option SqlColType) → Array SqlVal → String × Array SqlVal :=
  compileSepList (α := SqlVal × Option SqlColType) fun (v, ty?) p =>
    let ph := placeholder d (p.size + 1)
    (match d, ty? with | .postgres, some ty => "CAST(" ++ ph ++ " AS " ++ ty.render .postgres ++ ")" | _, _ => ph, p.push v)
private theorem compileSelectParams_eraseVals (d : SqlDialect) :
    ∀ (vs : List (SqlVal × Option SqlColType)) (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
      SameCompile (compileSelectParams d vs p₁) (compileSelectParams d (vs.map fun (_, ty?) => (.null, ty?)) p₂) :=
  compileSepList_eraseVals (α := SqlVal × Option SqlColType) _ (fun (_, ty?) => (.null, ty?)) fun (_, ty?) _ _ h =>
    ⟨by cases d <;> cases ty? <;> simp [h], by simp [h]⟩
private theorem compileSelectParams_no_semicolon (d : SqlDialect) :
    ∀ (vs : List (SqlVal × Option SqlColType)) (p : Array SqlVal), NoSemi (compileSelectParams d vs p).1 :=
  compileSepList_no_semicolon (α := SqlVal × Option SqlColType) _ fun (_, ty?) p => by
    cases d <;> cases ty?
    · exact placeholder_no_semicolon .postgres (p.size + 1)
    · exact NoSemi.lApp (placeholder_no_semicolon .postgres (p.size + 1)) |>.appL |>.app (SqlColType.render_no_semicolon .postgres _) |>.appL
    · exact placeholder_no_semicolon .sqlite (p.size + 1)
    · exact placeholder_no_semicolon .sqlite (p.size + 1)

@[inline] private def wrap1 (pre suf : String) (r : String × Array SqlVal) : String × Array SqlVal := (pre ++ r.1 ++ suf, r.2)
@[inline] private def wrap2 (pre mid suf : String) (f g : Array SqlVal → String × Array SqlVal) (p : Array SqlVal) :
    String × Array SqlVal := let (s1, p1) := f p; let (s2, p2) := g p1; (pre ++ s1 ++ mid ++ s2 ++ suf, p2)

private theorem wrap1_eq {pre suf : String} {r₁ r₂ : String × Array SqlVal} (h : SameCompile r₁ r₂) :
    SameCompile (wrap1 pre suf r₁) (wrap1 pre suf r₂) := ⟨by simp [wrap1, h.1], h.2⟩
private theorem wrap2_eq {pre₁ pre₂ mid suf : String} {f₁ f₂ g₁ g₂ : Array SqlVal → String × Array SqlVal}
    {p₁ p₂ : Array SqlVal} (hpre : pre₁ = pre₂) (hf : SameCompile (f₁ p₁) (f₂ p₂))
    (hg : ∀ q₁ q₂, q₁.size = q₂.size → SameCompile (g₁ q₁) (g₂ q₂)) :
    SameCompile (wrap2 pre₁ mid suf f₁ g₁ p₁) (wrap2 pre₂ mid suf f₂ g₂ p₂) :=
  let ⟨h3, h4⟩ := hg _ _ hf.2; ⟨by simp [wrap2, hpre, hf.1, h3], h4⟩
private theorem wrap1_no_semi {pre suf : String} {r : String × Array SqlVal}
    (hp : NoSemi pre) (hr : NoSemi r.1) (hs : NoSemi suf) : NoSemi (wrap1 pre suf r).1 := (hp.app hr).app hs
private theorem wrap2_no_semi {pre mid suf : String} {f g : Array SqlVal → String × Array SqlVal} {p : Array SqlVal}
    (hp : NoSemi pre) (hf : NoSemi (f p).1) (hm : NoSemi mid) (hg : NoSemi (g (f p).2).1) (hs : NoSemi suf) :
    NoSemi (wrap2 pre mid suf f g p).1 := (((hp.app hf).app hm).app hg).app hs

def SqlExpr.compileQual (d : SqlDialect) (pfx : String) (e : SqlExpr) (params : Array SqlVal) : String × Array SqlVal :=
  match e with
  | .litTrue  => (d.pick "TRUE" "1", params)
  | .litFalse => (d.pick "FALSE" "0", params)
  | .col id   => (pfx ++ id.quoteIdent, params)
  | .qualCol t c => (t.quoteIdent ++ "." ++ c.quoteIdent, params)
  | .param v  => (placeholder d (params.size + 1), params.push v)
  | .binOp op l r    => wrap2 "(" op.render ")" (l.compileQual d pfx) (r.compileQual d pfx) params
  | .not inner       => wrap1 "(NOT " ")" (inner.compileQual d pfx params)
  | .isNull inner    => wrap1 "(" " IS NULL)" (inner.compileQual d pfx params)
  | .isNotNull inner => wrap1 "(" " IS NOT NULL)" (inner.compileQual d pfx params)
  | .strLen inner    => wrap1 "LENGTH(" ")" (inner.compileQual d pfx params)
  | .like l r        => wrap2 "(" " LIKE " " ESCAPE '!')" (l.compileQual d pfx) (r.compileQual d pfx) params
  | .startsWith l r  =>
      let (sl, p1) := l.compileQual d pfx params
      wrap2 ("(SUBSTR(" ++ sl ++ ", 1, LENGTH(") ")) = " ")" (r.compileQual d pfx) (r.compileQual d pfx) p1
  | .contains l r    => wrap2 ("(" ++ d.pick "STRPOS(" "INSTR(") ", " ") > 0)" (l.compileQual d pfx) (r.compileQual d pfx) params
  | .inList l vs     => match vs with
      | []     => (d.pick "FALSE" "0", params)
      | _ :: _ => wrap2 "(" " IN (" "))" (l.compileQual d pfx) (compileInParams d vs) params
  | .existsSubquery st al pred =>
      wrap1 ("EXISTS (SELECT 1 FROM " ++ st.quoteIdent ++ " AS " ++ al.quoteIdent ++ " WHERE ") ")" (pred.compileQual d "" params)

def SqlExpr.compile (d : SqlDialect) (e : SqlExpr) (params : Array SqlVal) : String × Array SqlVal := e.compileQual d "" params

private theorem SqlExpr.compileQual_eraseVals (d : SqlDialect) (e : SqlExpr) :
    ∀ (pfx : String) (p₁ p₂ : Array SqlVal), p₁.size = p₂.size → SameCompile (e.compileQual d pfx p₁) (e.eraseVals.compileQual d pfx p₂) := by
  induction e with
  | litTrue | litFalse | col _ | qualCol _ _ => intro _ _ _ hsz; exact ⟨rfl, hsz⟩
  | param _ => intro _ _ _ hsz; exact ⟨by simp [SqlExpr.eraseVals, SqlExpr.compileQual, hsz], by simp [SqlExpr.eraseVals, SqlExpr.compileQual, hsz]⟩
  | not _ ih | isNull _ ih | isNotNull _ ih | strLen _ ih => intro pfx p₁ p₂ hsz; exact wrap1_eq (ih pfx p₁ p₂ hsz)
  | binOp _ _ _ ihl ihr | like _ _ ihl ihr | contains _ _ ihl ihr => intro pfx p₁ p₂ hsz; exact wrap2_eq rfl (ihl pfx p₁ p₂ hsz) (ihr pfx)
  | startsWith _ _ ihl ihr => intro pfx p₁ p₂ hsz; have ⟨h1, h2⟩ := ihl pfx p₁ p₂ hsz; exact wrap2_eq (by rw [h1]) (ihr pfx _ _ h2) (ihr pfx)
  | inList _ vs ihl =>
      intro pfx p₁ p₂ hsz; cases vs with
      | nil => exact ⟨rfl, hsz⟩
      | cons v vs' => exact wrap2_eq rfl (ihl pfx p₁ p₂ hsz) (compileInParams_eraseVals d (v :: vs'))
  | existsSubquery _ _ _ ih => intro _ p₁ p₂ hsz; exact wrap1_eq (ih "" p₁ p₂ hsz)

theorem SqlExpr.compileQual_sameShape (d : SqlDialect) (pfx : String) {e₁ e₂ : SqlExpr} (hsh : e₁.sameShape e₂) :
    ∀ (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
      (e₁.compileQual d pfx p₁).1 = (e₂.compileQual d pfx p₂).1 ∧
      (e₁.compileQual d pfx p₁).2.size = (e₂.compileQual d pfx p₂).2.size := by
  intro p₁ p₂ hsz
  have ⟨h1, h2⟩ := e₁.compileQual_eraseVals d pfx p₁ p₂ hsz
  have ⟨h3, h4⟩ := e₂.compileQual_eraseVals d pfx p₂ p₂ rfl
  rw [hsh] at h1 h2; exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩

/-- Non-interference for `SqlExpr.compile`: changing runtime parameter values leaves the
    compiled SQL string AND parameter count bit-for-bit identical. -/
theorem SqlExpr.compile_sameShape (d : SqlDialect) {e₁ e₂ : SqlExpr} (hsh : e₁.sameShape e₂) :
    ∀ (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
      (e₁.compile d p₁).1 = (e₂.compile d p₂).1 ∧ (e₁.compile d p₁).2.size = (e₂.compile d p₂).2.size :=
  SqlExpr.compileQual_sameShape d "" hsh

private theorem SqlExpr.compileQual_no_semicolon_aux (d : SqlDialect) (e : SqlExpr) :
    ∀ (pfx : String), (∀ c ∈ pfx.toList, c ≠ ';') → ∀ (params : Array SqlVal), ∀ c ∈ (e.compileQual d pfx params).1.toList, c ≠ ';' := by
  induction e with
  | litTrue | litFalse => intro _ _ _; exact d.pick_no_semi NoSemi.lit NoSemi.lit
  | col id => intro _ hpfx _; exact NoSemi.app hpfx id.quoteIdent_no_semicolon
  | qualCol t c => intro _ _ _; exact (NoSemi.appL t.quoteIdent_no_semicolon).app c.quoteIdent_no_semicolon
  | param _ => intro _ _ p; exact placeholder_no_semicolon d (p.size + 1)
  | not _ ih | isNull _ ih | isNotNull _ ih | strLen _ ih =>
      intro pfx hpfx p; exact wrap1_no_semi NoSemi.lit (ih pfx hpfx p) NoSemi.lit
  | binOp op _ _ ihl ihr => intro pfx hpfx p; exact wrap2_no_semi NoSemi.lit (ihl pfx hpfx p) op.render_no_semicolon (ihr pfx hpfx _) NoSemi.lit
  | like _ _ ihl ihr => intro pfx hpfx p; exact wrap2_no_semi NoSemi.lit (ihl pfx hpfx p) NoSemi.lit (ihr pfx hpfx _) NoSemi.lit
  | startsWith _ _ ihl ihr =>
      intro pfx hpfx p; exact wrap2_no_semi (NoSemi.lApp (ihl pfx hpfx p) |>.appL) (ihr pfx hpfx _) NoSemi.lit (ihr pfx hpfx _) NoSemi.lit
  | contains _ _ ihl ihr =>
      intro pfx hpfx p; exact wrap2_no_semi (NoSemi.lApp (d.pick_no_semi NoSemi.lit NoSemi.lit)) (ihl pfx hpfx p) NoSemi.lit (ihr pfx hpfx _) NoSemi.lit
  | inList _ vs ihl =>
      intro pfx hpfx p; cases vs with
      | nil => exact d.pick_no_semi NoSemi.lit NoSemi.lit
      | cons v vs' => exact wrap2_no_semi NoSemi.lit (ihl pfx hpfx p) NoSemi.lit (compileInParams_no_semicolon d (v :: vs') _) NoSemi.lit
  | existsSubquery st al _ ih =>
      intro _ _ p; exact wrap1_no_semi (NoSemi.lApp st.quoteIdent_no_semicolon |>.appL |>.app al.quoteIdent_no_semicolon |>.appL) (ih "" NoSemi.empty p) NoSemi.lit

theorem SqlExpr.compileQual_no_semicolon (d : SqlDialect) (pfx : String) (hpfx : ∀ c ∈ pfx.toList, c ≠ ';') (e : SqlExpr) :
    ∀ (params : Array SqlVal), ∀ c ∈ (e.compileQual d pfx params).1.toList, c ≠ ';' :=
  SqlExpr.compileQual_no_semicolon_aux d e pfx hpfx

theorem SqlExpr.compile_no_semicolon (d : SqlDialect) (e : SqlExpr) :
    ∀ (params : Array SqlVal), ∀ c ∈ (e.compile d params).1.toList, c ≠ ';' :=
  SqlExpr.compileQual_no_semicolon d "" (fun _ h => nomatch h) e

inductive SqlQuery where
  | select (table : SqlIdent) (cols : List SqlIdent) (whereExpr : SqlExpr)
           (orderBy : Option (SqlIdent × SqlOrderDir) := none) (limit offset : Option Nat := none)
  | selectAll (table : SqlIdent) (whereExpr : SqlExpr)
              (orderBy : Option (SqlIdent × SqlOrderDir) := none) (limit offset : Option Nat := none)
  | selectSchema (schema table : SqlIdent) (cols : List SqlIdent) (whereExpr : SqlExpr)
                 (orderBy : Option (SqlIdent × SqlOrderDir) := none) (limit offset : Option Nat := none)
  | count  (table : SqlIdent) (whereExpr : SqlExpr)
  | countSchema (schema table : SqlIdent) (whereExpr : SqlExpr)
  | aggregate (op : SqlAggOp) (table col : SqlIdent) (whereExpr : SqlExpr)
  | joinSelect (leftTable rightTable : SqlIdent) (leftCols rightCols : List SqlIdent)
               (leftJoinCol rightJoinCol : SqlIdent) (leftWhere rightWhere : SqlExpr)
               (orderBy : Option (SqlIdent × SqlOrderDir) := none) (limit offset : Option Nat := none)
  | insert (table : SqlIdent) (cols : List (SqlIdent × SqlVal)) (returning : List SqlIdent)
           (guard? : Option SqlExpr := none) (colTypes : List SqlColType := [])
  | insertOrIgnore (table : SqlIdent) (cols : List (SqlIdent × SqlVal)) (conflictCols : List SqlIdent := [])
                   (returning : List SqlIdent := []) (guard? : Option SqlExpr := none) (colTypes : List SqlColType := [])
  | upsert (table : SqlIdent) (cols : List (SqlIdent × SqlVal)) (conflictCols : List SqlIdent)
           (updateCols : List SqlIdent) (conflictWhere? : Option SqlExpr) (returning : List SqlIdent)
  | update (table : SqlIdent) (sets : List (SqlIdent × SqlExpr)) (whereExpr : SqlExpr) (returning : List SqlIdent)
  | delete (table : SqlIdent) (whereExpr : SqlExpr) (returning : List SqlIdent)
deriving Inhabited, DecidableEq

@[reducible] def SqlQuery.isWrite : SqlQuery → Bool
  | .insert .. | .insertOrIgnore .. | .upsert .. | .update .. | .delete .. => true
  | _ => false

def SqlIdent.joinQuotedPrefixed (pfx : String) : List SqlIdent → String
  | [] => "" | [c] => pfx ++ c.quoteIdent | c :: cs => pfx ++ c.quoteIdent ++ ", " ++ joinQuotedPrefixed pfx cs
abbrev SqlIdent.joinQuoted : List SqlIdent → String := SqlIdent.joinQuotedPrefixed ""

theorem SqlIdent.joinQuotedPrefixed_no_semicolon (pfx : String) (hpfx : ∀ c ∈ pfx.toList, c ≠ ';') :
    ∀ (cs : List SqlIdent), ∀ c ∈ (SqlIdent.joinQuotedPrefixed pfx cs).toList, c ≠ ';'
  | [] => NoSemi.empty
  | [x] => NoSemi.app hpfx x.quoteIdent_no_semicolon
  | x :: y :: rest => NoSemi.app hpfx x.quoteIdent_no_semicolon |>.appL |>.app (SqlIdent.joinQuotedPrefixed_no_semicolon pfx hpfx (y :: rest))

private def compileSets (d : SqlDialect) : List (SqlIdent × SqlExpr) → Array SqlVal → String × Array SqlVal :=
  compileSepList (α := SqlIdent × SqlExpr) fun (col, e) p => let (se, p1) := e.compile d p; (col.quoteIdent ++ " = " ++ se, p1)
private theorem compileSets_eraseVals (d : SqlDialect) :
    ∀ (l : List (SqlIdent × SqlExpr)) (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
      SameCompile (compileSets d l p₁) (compileSets d (l.map fun (c, e) => (c, e.eraseVals)) p₂) :=
  compileSepList_eraseVals (α := SqlIdent × SqlExpr) _ (fun (c, e) => (c, e.eraseVals)) fun (_, e) p₁ p₂ hsz =>
    let ⟨h1, h2⟩ := e.compileQual_eraseVals d "" p₁ p₂ hsz; ⟨by simp [SqlExpr.compile, h1], h2⟩
private theorem compileSets_no_semicolon (d : SqlDialect) :
    ∀ (l : List (SqlIdent × SqlExpr)) (p : Array SqlVal), NoSemi (compileSets d l p).1 :=
  compileSepList_no_semicolon (α := SqlIdent × SqlExpr) _ fun (col, e) p =>
    (NoSemi.appL col.quoteIdent_no_semicolon).app (e.compile_no_semicolon d p)

private def renderUpsertSets : List SqlIdent → String
  | [] => "" | [c] => c.quoteIdent ++ " = EXCLUDED." ++ c.quoteIdent
  | c :: cs => c.quoteIdent ++ " = EXCLUDED." ++ c.quoteIdent ++ ", " ++ renderUpsertSets cs
private theorem renderUpsertSets_no_semicolon : ∀ cs : List SqlIdent, NoSemi (renderUpsertSets cs)
  | [] => NoSemi.empty
  | [c] => (NoSemi.appL c.quoteIdent_no_semicolon).app c.quoteIdent_no_semicolon
  | c :: d :: rest => (NoSemi.appL c.quoteIdent_no_semicolon).app c.quoteIdent_no_semicolon |>.appL |>.app (renderUpsertSets_no_semicolon (d :: rest))

def SqlQuery.eraseVals : SqlQuery → SqlQuery
  | .select t c w o l off => .select t c w.eraseVals o l off
  | .selectAll t w o l off => .selectAll t w.eraseVals o l off
  | .selectSchema sc t c w o l off => .selectSchema sc t c w.eraseVals o l off
  | .count t w => .count t w.eraseVals | .countSchema sc t w => .countSchema sc t w.eraseVals
  | .aggregate op t c w => .aggregate op t c w.eraseVals
  | .joinSelect lt rt lc rc lj rj lw rw o l off => .joinSelect lt rt lc rc lj rj lw.eraseVals rw.eraseVals o l off
  | .insert t cols ret g? tys => .insert t (cols.map fun (c, _) => (c, .null)) ret (g?.map SqlExpr.eraseVals) tys
  | .insertOrIgnore t cols cc ret g? tys => .insertOrIgnore t (cols.map fun (c, _) => (c, .null)) cc ret (g?.map SqlExpr.eraseVals) tys
  | .upsert t cols cc uc cw ret => .upsert t (cols.map fun (c, _) => (c, .null)) cc uc (cw.map SqlExpr.eraseVals) ret
  | .update t s w ret => .update t (s.map fun (c, e) => (c, e.eraseVals)) w.eraseVals ret
  | .delete t w ret => .delete t w.eraseVals ret
abbrev SqlQuery.sameShape (q₁ q₂ : SqlQuery) : Prop := q₁.eraseVals = q₂.eraseVals

def renderReturning (ret : List SqlIdent) : String :=
  if ret.isEmpty then "" else " RETURNING " ++ SqlIdent.joinQuoted ret
private theorem renderReturning_no_semicolon (ret : List SqlIdent) : NoSemi (renderReturning ret) := by
  unfold renderReturning; split
  · exact NoSemi.empty
  · exact NoSemi.lApp (SqlIdent.joinQuotedPrefixed_no_semicolon "" NoSemi.empty ret)

private def renderLimitOffset (d : SqlDialect) (limit? offset? : Option Nat) : String :=
  match limit?, offset? with
  | none, none => "" | some n, none => " LIMIT " ++ toString n
  | some n, some off => " LIMIT " ++ toString n ++ " OFFSET " ++ toString off
  | none, some off => d.pick " OFFSET " " LIMIT -1 OFFSET " ++ toString off
private theorem renderLimitOffset_no_semicolon (d : SqlDialect) (limit? offset? : Option Nat) :
    NoSemi (renderLimitOffset d limit? offset?) := by
  cases limit? <;> cases offset?
  · exact NoSemi.empty
  · exact (d.pick_no_semi NoSemi.lit NoSemi.lit).app (nat_toString_no_semicolon _)
  · exact NoSemi.lApp (nat_toString_no_semicolon _)
  · exact NoSemi.lApp (nat_toString_no_semicolon _) |>.appL |>.app (nat_toString_no_semicolon _)

private def renderOrderBy (pfx : String) : Option (SqlIdent × SqlOrderDir) → String
  | none => "" | some (col, dir) => " ORDER BY " ++ pfx ++ col.quoteIdent ++ (match dir with | .asc => " ASC" | .desc => " DESC")
private theorem renderOrderBy_no_semicolon (pfx : String) (hpfx : NoSemi pfx) (orderBy? : Option (SqlIdent × SqlOrderDir)) :
    NoSemi (renderOrderBy pfx orderBy?) := by
  rcases orderBy? with _ | ⟨col, dir⟩
  · exact NoSemi.empty
  · exact NoSemi.lApp hpfx |>.app col.quoteIdent_no_semicolon |>.app (by cases dir <;> exact NoSemi.lit)

private def renderConflictTarget (conflictCols : List SqlIdent) : String :=
  if conflictCols.isEmpty then " ON CONFLICT " else " ON CONFLICT (" ++ SqlIdent.joinQuoted conflictCols ++ ") "
private theorem renderConflictTarget_no_semicolon (cc : List SqlIdent) : NoSemi (renderConflictTarget cc) := by
  unfold renderConflictTarget; split
  · exact NoSemi.lit
  · exact NoSemi.lApp (SqlIdent.joinQuotedPrefixed_no_semicolon "" NoSemi.empty cc) |>.appL

private def compileInsertHead (d : SqlDialect) (tbl : SqlIdent) (cols : List (SqlIdent × SqlVal))
    (guard? : Option SqlExpr := none) (colTypes : List SqlColType := []) : String × Array SqlVal :=
  let head := "INSERT INTO " ++ tbl.quoteIdent ++ " (" ++ SqlIdent.joinQuoted (cols.map Prod.fst) ++ ") "
  match guard? with
  | none => let (valsSql, params) := compileInParams d (cols.map Prod.snd) #[]; (head ++ "VALUES (" ++ valsSql ++ ")", params)
  | some g =>
      let (valsSql, p1) := compileSelectParams d (zipValsWithTypes (cols.map Prod.snd) colTypes) #[]
      let (gSql, p2) := g.compile d p1
      (head ++ "SELECT " ++ valsSql ++ " WHERE " ++ gSql, p2)

def SqlQuery.compile (d : SqlDialect) : SqlQuery → String × Array SqlVal
  | .select tbl cols whereExpr orderBy? limit? offset? =>
      let (wSql, params) := whereExpr.compile d #[]
      if cols.isEmpty then
        ("SELECT 1 FROM " ++ tbl.quoteIdent ++ " WHERE (0 = 1 AND (" ++ wSql ++ "))", params)
      else
        ("SELECT " ++ SqlIdent.joinQuoted cols ++ " FROM " ++ tbl.quoteIdent ++
         " WHERE " ++ wSql ++ renderOrderBy "" orderBy? ++ renderLimitOffset d limit? offset?, params)
  | .selectAll tbl whereExpr orderBy? limit? offset? =>
      let (wSql, params) := whereExpr.compile d #[]
      ("SELECT * FROM " ++ tbl.quoteIdent ++
       " WHERE " ++ wSql ++ renderOrderBy "" orderBy? ++ renderLimitOffset d limit? offset?, params)
  | .selectSchema sc tbl cols whereExpr orderBy? limit? offset? =>
      let (wSql, params) := whereExpr.compile d #[]
      let sel := if cols.isEmpty then "*" else SqlIdent.joinQuoted cols
      ("SELECT " ++ sel ++ " FROM " ++ sc.quoteIdent ++ "." ++ tbl.quoteIdent ++
       " WHERE " ++ wSql ++ renderOrderBy "" orderBy? ++ renderLimitOffset d limit? offset?, params)
  | .count tbl whereExpr =>
      let (wSql, params) := whereExpr.compile d #[]
      ("SELECT COUNT(*) FROM " ++ tbl.quoteIdent ++ " WHERE " ++ wSql, params)
  | .countSchema sc tbl whereExpr =>
      let (wSql, params) := whereExpr.compile d #[]
      ("SELECT COUNT(*) FROM " ++ sc.quoteIdent ++ "." ++ tbl.quoteIdent ++ " WHERE " ++ wSql, params)
  | .aggregate op tbl col whereExpr =>
      let (wSql, params) := whereExpr.compile d #[]
      ("SELECT " ++ op.render ++ "(" ++ col.quoteIdent ++ ") FROM " ++ tbl.quoteIdent ++ " WHERE " ++ wSql, params)
  | .joinSelect lt rt lCols rCols lJoin rJoin lWhere rWhere orderBy? limit? offset? =>
      let (lwSql, p1) := lWhere.compileQual d "\"_l\"." #[]
      let (rwSql, p2) := rWhere.compileQual d "\"_r\"." p1
      let selCols := SqlIdent.joinQuotedPrefixed "\"_l\"." lCols ++ ", " ++ SqlIdent.joinQuotedPrefixed "\"_r\"." rCols
      ("SELECT " ++ selCols ++ " FROM " ++ lt.quoteIdent ++ " AS \"_l\" INNER JOIN " ++
       rt.quoteIdent ++ " AS \"_r\" ON \"_l\"." ++ lJoin.quoteIdent ++ " = \"_r\"." ++ rJoin.quoteIdent ++
       " WHERE (" ++ lwSql ++ " AND " ++ rwSql ++ ")" ++ renderOrderBy "\"_l\"." orderBy? ++ renderLimitOffset d limit? offset?, p2)
  | .insert tbl cols ret g? tys =>
      let (hd, params) := compileInsertHead d tbl cols g? tys; (hd ++ renderReturning ret, params)
  | .insertOrIgnore tbl cols conflictCols ret g? tys =>
      let (hd, params) := compileInsertHead d tbl cols g? tys
      (hd ++ renderConflictTarget conflictCols ++ "DO NOTHING" ++ renderReturning ret, params)
  | .upsert tbl cols conflictCols updateCols conflictWhere? ret =>
      let (hd, p1) := compileInsertHead d tbl cols
      let conflictClause := renderConflictTarget conflictCols ++
        if updateCols.isEmpty then "DO NOTHING" else "DO UPDATE SET " ++ renderUpsertSets updateCols
      let (whereSql, p2) := match conflictWhere? with
        | none => ("", p1)
        | some cw => let (ws, p2) := cw.compileQual d (tbl.quoteIdent ++ ".") p1; (" WHERE " ++ ws, p2)
      (hd ++ conflictClause ++ whereSql ++ renderReturning ret, p2)
  | .update tbl sets whereExpr ret =>
      let (setSql, p1) := compileSets d sets #[]
      let (wSql, p2) := whereExpr.compile d p1
      ("UPDATE " ++ tbl.quoteIdent ++ " SET " ++ setSql ++ " WHERE " ++ wSql ++ renderReturning ret, p2)
  | .delete tbl whereExpr ret =>
      let (wSql, params) := whereExpr.compile d #[]
      ("DELETE FROM " ++ tbl.quoteIdent ++ " WHERE " ++ wSql ++ renderReturning ret, params)

private theorem compileInsertHead_eraseVals (d : SqlDialect) (tbl : SqlIdent) (cols : List (SqlIdent × SqlVal))
    (guard? : Option SqlExpr := none) (colTypes : List SqlColType := []) :
    SameCompile (compileInsertHead d tbl cols guard? colTypes)
      (compileInsertHead d tbl (cols.map fun (c, _) => (c, .null)) (guard?.map SqlExpr.eraseVals) colTypes) := by
  cases guard? with
  | none =>
      have ⟨h1, h2⟩ := compileInParams_eraseVals d (cols.map Prod.snd) #[] #[] rfl
      refine ⟨?_, ?_⟩ <;> simp only [compileInsertHead, Option.map, List.map_map, Function.comp_def, h1, h2]
  | some g =>
      have ⟨h1, h2⟩ := compileSelectParams_eraseVals d (zipValsWithTypes (cols.map Prod.snd) colTypes) #[] #[] rfl
      have ⟨h3, h4⟩ := g.compileQual_eraseVals d "" _ _ h2
      have hzip : zipValsWithTypes ((cols.map fun (c, _) => (c, SqlVal.null)).map Prod.snd) colTypes =
          (zipValsWithTypes (cols.map Prod.snd) colTypes).map fun (_, ty?) => (.null, ty?) := by
        rw [← zipValsWithTypes_map_null]; simp [List.map_map, Function.comp_def]
      have hfst : (cols.map fun (c, _) => (c, SqlVal.null)).map Prod.fst = cols.map Prod.fst := by
        simp [List.map_map, Function.comp_def]
      refine ⟨?_, ?_⟩
      · dsimp only [compileInsertHead, Option.map, SqlExpr.compile]; rw [hfst, hzip, h1, h3]
      · dsimp only [compileInsertHead, Option.map, SqlExpr.compile]; rw [hzip, h4]

private theorem compileInsertHead_no_semicolon (d : SqlDialect) (tbl : SqlIdent) (cols : List (SqlIdent × SqlVal))
    (guard? : Option SqlExpr := none) (colTypes : List SqlColType := []) :
    NoSemi (compileInsertHead d tbl cols guard? colTypes).1 := by
  have hHead : NoSemi ("INSERT INTO " ++ tbl.quoteIdent ++ " (" ++ SqlIdent.joinQuoted (cols.map Prod.fst) ++ ") ") :=
    NoSemi.lApp tbl.quoteIdent_no_semicolon |>.appL |>.app (SqlIdent.joinQuotedPrefixed_no_semicolon "" NoSemi.empty (cols.map Prod.fst)) |>.appL
  cases guard? with
  | none => exact hHead.appL.app (compileInParams_no_semicolon d _ _) |>.appL
  | some g => exact hHead.appL.app (compileSelectParams_no_semicolon d _ _) |>.appL |>.app (g.compile_no_semicolon d _)

private theorem SqlQuery.compile_eraseVals (d : SqlDialect) (q : SqlQuery) : (q.compile d).1 = (q.eraseVals.compile d).1 := by
  cases q with
  | select _ cols w _ _ _ =>
      dsimp only [SqlQuery.eraseVals, SqlQuery.compile, SqlExpr.compile]
      split <;> (dsimp only; rw [(w.compileQual_eraseVals d "" #[] #[] rfl).1])
  | selectAll _ w _ _ _ | selectSchema _ _ _ w _ _ _ | count _ w | countSchema _ _ w | aggregate _ _ _ w | delete _ w _ =>
      dsimp only [SqlQuery.eraseVals, SqlQuery.compile, SqlExpr.compile]
      rw [(w.compileQual_eraseVals d "" #[] #[] rfl).1]
  | joinSelect _ _ _ _ _ _ lw rw _ _ _ =>
      have ⟨hL, hszL⟩ := lw.compileQual_eraseVals d "\"_l\"." #[] #[] rfl
      have ⟨hR, _⟩ := rw.compileQual_eraseVals d "\"_r\"." _ _ hszL
      dsimp only [SqlQuery.eraseVals, SqlQuery.compile]; rw [hL, hR]
  | insert tbl cols _ g? tys | insertOrIgnore tbl cols _ _ g? tys =>
      dsimp only [SqlQuery.eraseVals, SqlQuery.compile]; rw [(compileInsertHead_eraseVals d tbl cols g? tys).1]
  | upsert tbl cols _ _ cw _ =>
      have ⟨h, hsz⟩ := compileInsertHead_eraseVals d tbl cols none []
      dsimp only [Option.map] at h hsz
      cases cw with
      | none => dsimp only [SqlQuery.eraseVals, SqlQuery.compile, Option.map]; rw [h]
      | some e =>
          have ⟨he, _⟩ := e.compileQual_eraseVals d (tbl.quoteIdent ++ ".") _ _ hsz
          dsimp only [SqlQuery.eraseVals, SqlQuery.compile, Option.map]; rw [h, he]
  | update _ sets w _ =>
      have ⟨hS, hszS⟩ := compileSets_eraseVals d sets #[] #[] rfl
      have ⟨hW, _⟩ := w.compileQual_eraseVals d "" _ _ hszS
      dsimp only [SqlQuery.eraseVals, SqlQuery.compile, SqlExpr.compile]; rw [hS, hW]

/-- **SQL Injection Closure (Non-Interference Theorem):**
    Any two typed `SqlQuery` values with the same AST skeleton (`sameShape`) compile to
    bit-for-bit identical SQL strings regardless of arbitrary runtime parameter payloads. -/
theorem SqlQuery.compile_sameShape (d : SqlDialect) {q₁ q₂ : SqlQuery} (hsh : q₁.sameShape q₂) :
    (q₁.compile d).1 = (q₂.compile d).1 := by rw [q₁.compile_eraseVals d, hsh, ← q₂.compile_eraseVals d]

theorem SqlQuery.compile_no_semicolon (d : SqlDialect) (q : SqlQuery) : ∀ c ∈ (q.compile d).1.toList, c ≠ ';' := by
  let jqp (pfx : String) (hp : NoSemi pfx) (cs : List SqlIdent) := SqlIdent.joinQuotedPrefixed_no_semicolon pfx hp cs
  let jq (cs : List SqlIdent) := jqp "" NoSemi.empty cs
  cases q with
  | select tbl cols w ob lim off =>
      dsimp only [SqlQuery.compile]; split
      · exact NoSemi.lApp tbl.quoteIdent_no_semicolon |>.appL |>.app (w.compile_no_semicolon d #[]) |>.appL
      · exact NoSemi.lApp (jq cols) |>.appL |>.app tbl.quoteIdent_no_semicolon |>.appL |>.app (w.compile_no_semicolon d #[])
          |>.app (renderOrderBy_no_semicolon "" NoSemi.empty ob) |>.app (renderLimitOffset_no_semicolon d lim off)
  | selectAll tbl w ob lim off =>
      exact NoSemi.lApp tbl.quoteIdent_no_semicolon |>.appL |>.app (w.compile_no_semicolon d #[])
        |>.app (renderOrderBy_no_semicolon "" NoSemi.empty ob) |>.app (renderLimitOffset_no_semicolon d lim off)
  | selectSchema sc tbl cols w ob lim off =>
      have hSel : NoSemi (if cols.isEmpty then "*" else SqlIdent.joinQuoted cols) := by
        split
        · exact NoSemi.lit
        · exact jq cols
      exact NoSemi.lApp hSel |>.appL |>.app sc.quoteIdent_no_semicolon |>.appL |>.app tbl.quoteIdent_no_semicolon |>.appL
        |>.app (w.compile_no_semicolon d #[]) |>.app (renderOrderBy_no_semicolon "" NoSemi.empty ob) |>.app (renderLimitOffset_no_semicolon d lim off)
  | count tbl w => exact NoSemi.lApp tbl.quoteIdent_no_semicolon |>.appL |>.app (w.compile_no_semicolon d #[])
  | countSchema sc tbl w =>
      exact NoSemi.lApp sc.quoteIdent_no_semicolon |>.appL |>.app tbl.quoteIdent_no_semicolon |>.appL |>.app (w.compile_no_semicolon d #[])
  | aggregate op tbl col w =>
      exact NoSemi.lApp op.render_no_semicolon |>.appL |>.app col.quoteIdent_no_semicolon |>.appL |>.app tbl.quoteIdent_no_semicolon |>.appL |>.app (w.compile_no_semicolon d #[])
  | joinSelect lt rt lc rc lj rj lw rw ob lim off =>
      have hL : NoSemi "\"_l\"." := NoSemi.lit
      have hR : NoSemi "\"_r\"." := NoSemi.lit
      have hSel := (NoSemi.appL (s := ", ") (jqp "\"_l\"." hL lc)).app (jqp "\"_r\"." hR rc)
      exact NoSemi.lApp hSel |>.appL |>.app lt.quoteIdent_no_semicolon |>.appL |>.app rt.quoteIdent_no_semicolon |>.appL
        |>.app lj.quoteIdent_no_semicolon |>.appL |>.app rj.quoteIdent_no_semicolon |>.appL
        |>.app (lw.compileQual_no_semicolon d "\"_l\"." hL #[]) |>.appL |>.app (rw.compileQual_no_semicolon d "\"_r\"." hR _) |>.appL
        |>.app (renderOrderBy_no_semicolon "\"_l\"." hL ob) |>.app (renderLimitOffset_no_semicolon d lim off)
  | insert tbl cols ret g? tys => exact (compileInsertHead_no_semicolon d tbl cols g? tys).app (renderReturning_no_semicolon ret)
  | insertOrIgnore tbl cols cc ret g? tys =>
      exact (compileInsertHead_no_semicolon d tbl cols g? tys).app (renderConflictTarget_no_semicolon cc) |>.appL |>.app (renderReturning_no_semicolon ret)
  | upsert tbl cols cc uc cw ret =>
      have hConf : NoSemi (renderConflictTarget cc ++ if uc.isEmpty then "DO NOTHING" else "DO UPDATE SET " ++ renderUpsertSets uc) := by
        refine (renderConflictTarget_no_semicolon cc).app ?_
        split
        · exact NoSemi.lit
        · exact NoSemi.lApp (renderUpsertSets_no_semicolon uc)
      have hCw : NoSemi (match cw with | none => ("", (compileInsertHead d tbl cols).2) | some e => let (ws, p2) := e.compileQual d (tbl.quoteIdent ++ ".") (compileInsertHead d tbl cols).2; (" WHERE " ++ ws, p2)).1 := by
        cases cw with
        | none => exact NoSemi.empty
        | some e => exact NoSemi.lApp (e.compileQual_no_semicolon d _ (NoSemi.appL tbl.quoteIdent_no_semicolon) _)
      exact (compileInsertHead_no_semicolon d tbl cols).app hConf |>.app hCw |>.app (renderReturning_no_semicolon ret)
  | update tbl sets w ret =>
      exact NoSemi.lApp tbl.quoteIdent_no_semicolon |>.appL |>.app (compileSets_no_semicolon d sets #[]) |>.appL |>.app (w.compile_no_semicolon d _) |>.app (renderReturning_no_semicolon ret)
  | delete tbl w ret =>
      exact NoSemi.lApp tbl.quoteIdent_no_semicolon |>.appL |>.app (w.compile_no_semicolon d #[]) |>.app (renderReturning_no_semicolon ret)

/-! ## Abstract Relational Policy & Invariant Soundness Model -/

section RelModel
variable {Row : Type}
def evalSelect (tbl : List Row) (wherePred : Row → Bool) : List Row := tbl.filter wherePred
def evalInsert (tbl : List Row) (newRow : Row) : List Row := newRow :: tbl
def evalInsertGuarded (tbl : List Row) (guard : Bool) (newRow : Row) : List Row := if guard then newRow :: tbl else tbl
def evalUpdate (tbl : List Row) (wherePred : Row → Bool) (setFn : Row → Row) : List Row := tbl.map fun r => if wherePred r then setFn r else r
def evalDelete (tbl : List Row) (wherePred : Row → Bool) : List Row := tbl.filter fun r => !wherePred r

theorem evalSelect_satisfies_policy (RowInv ReadPolicy : Row → Prop) (tbl : List Row) (wherePred : Row → Bool)
    (htbl : ∀ r ∈ tbl, RowInv r) (hpol : ∀ r, RowInv r → wherePred r = true → ReadPolicy r) :
    ∀ r ∈ evalSelect tbl wherePred, RowInv r ∧ ReadPolicy r := fun r hr =>
  let ⟨hm, hw⟩ := List.mem_filter.1 hr; ⟨htbl r hm, hpol r (htbl r hm) hw⟩

theorem evalInsert_preserves_inv (RowInv InsertPolicy : Row → Prop) (tbl : List Row) (newRow : Row)
    (htbl : ∀ r ∈ tbl, RowInv r) (hinv : RowInv newRow) (_hpol : InsertPolicy newRow) :
    ∀ r ∈ evalInsert tbl newRow, RowInv r := fun r hr => (List.mem_cons.1 hr).elim (· ▸ hinv) (htbl r)

theorem evalInsertGuarded_preserves_inv_and_policy (RowInv InsertPolicy : Row → Prop) (tbl : List Row)
    (guard : Bool) (newRow : Row) (htbl : ∀ r ∈ tbl, RowInv r) (hinv : RowInv newRow)
    (hpol : guard = true → InsertPolicy newRow) :
    (∀ r ∈ evalInsertGuarded tbl guard newRow, RowInv r) ∧ (guard = true → InsertPolicy newRow) :=
  ⟨fun r hr => by
    cases guard
    · exact htbl r hr
    · exact (List.mem_cons.1 hr).elim (· ▸ hinv) (htbl r), hpol⟩

theorem evalUpdate_preserves_inv_and_trans (RowInv UpdatePolicy : Row → Prop) (TransInv : Row → Row → Prop)
    (tbl : List Row) (wherePred : Row → Bool) (setFn : Row → Row) (htbl : ∀ r ∈ tbl, RowInv r)
    (hpolOld : ∀ r, RowInv r → wherePred r = true → UpdatePolicy r)
    (hpolNew : ∀ r, RowInv r → wherePred r = true → UpdatePolicy (setFn r))
    (hinv : ∀ r, RowInv r → wherePred r = true → RowInv (setFn r))
    (htrans : ∀ r, RowInv r → wherePred r = true → TransInv r (setFn r)) :
    (∀ r ∈ evalUpdate tbl wherePred setFn, RowInv r) ∧
    (∀ r ∈ tbl, wherePred r = true → UpdatePolicy r ∧ UpdatePolicy (setFn r) ∧ TransInv r (setFn r)) :=
  ⟨fun _ hr' => by rcases List.mem_map.1 hr' with ⟨r, hm, rfl⟩; cases hw : wherePred r <;> simp [htbl r hm]; exact hinv r (htbl r hm) hw,
   fun r hm hw => ⟨hpolOld r (htbl r hm) hw, hpolNew r (htbl r hm) hw, htrans r (htbl r hm) hw⟩⟩

theorem evalDelete_preserves_inv_and_policy (RowInv DeletePolicy : Row → Prop) (tbl : List Row) (wherePred : Row → Bool)
    (htbl : ∀ r ∈ tbl, RowInv r) (hpol : ∀ r, RowInv r → wherePred r = true → DeletePolicy r) :
    (∀ r ∈ evalDelete tbl wherePred, RowInv r) ∧ (∀ r ∈ tbl, wherePred r = true → DeletePolicy r) :=
  ⟨fun r hr => htbl r (List.mem_filter.1 hr).1, fun r hm hw => hpol r (htbl r hm) hw⟩
end RelModel

/-! ## Schema Metadata & SQL DDL / Postgres RLS Generator -/

/-- Specification for an `encrypted(...)` column (AES-256-GCM + Base64). -/
structure EncColSpec where
  keyEnv    : String
  fallback? : Option String := none
  aad       : ByteArray
  isBytes   : Bool := false
  prevKeys  : List (String × Option String) := []
deriving Inhabited

abbrev aeadOverhead : Nat := 28
abbrev aeadBase64Len (plainBytes : Nat) : Nat := 4 * ((plainBytes + aeadOverhead + 2) / 3)
theorem aeadBase64Len_mono {a b : Nat} (h : a ≤ b) : aeadBase64Len a ≤ aeadBase64Len b := by
  simp only [aeadBase64Len, aeadOverhead]; omega

inductive OnDeleteAction where | noAction | cascade | setNull | restrict deriving Inhabited, DecidableEq
def OnDeleteAction.render : OnDeleteAction → String
  | .noAction => "" | .cascade => " ON DELETE CASCADE" | .setNull => " ON DELETE SET NULL" | .restrict => " ON DELETE RESTRICT"

structure ColumnSchema where
  name         : SqlIdent
  colType      : SqlColType
  nullable     : Bool := false
  isPrimaryKey : Bool := false
  isUnique     : Bool := false
  isImmutable  : Bool := false
  references?  : Option (SqlIdent × SqlIdent) := none
  onDelete     : OnDeleteAction := .noAction
  checkSql?    : Option String := none
deriving Inhabited

structure TableSchema where
  name      : SqlIdent
  columns   : List ColumnSchema
  indexes   : List (List SqlIdent) := []
  checks    : List String := []
  rlsRead?  : Option String := none
  rlsWrite? : Option String := none
deriving Inhabited

private def optClause (opt : Option α) (f : α → String) : String := opt.map f |>.getD ""
private def joinSqlStmts (stmts : List String) : String := if stmts.isEmpty then "" else String.intercalate ";\n" stmts ++ ";\n"
private def ColumnSchema.renderCore (d : SqlDialect) (c : ColumnSchema) (mid : String) : String :=
  c.name.quoteIdent ++ " " ++ c.colType.render d ++ (if c.nullable then "" else " NOT NULL") ++
    mid ++ optClause c.checkSql? (" CHECK (" ++ · ++ ")")

def ColumnSchema.renderDef (d : SqlDialect) (c : ColumnSchema) : String :=
  c.renderCore d <| (if c.isPrimaryKey then " PRIMARY KEY" else "") ++
    (if c.isUnique && !c.isPrimaryKey then " UNIQUE" else "") ++
    optClause c.references? fun (rt, rc) => " REFERENCES " ++ rt.quoteIdent ++ "(" ++ rc.quoteIdent ++ ")" ++ c.onDelete.render
def TableSchema.chkName (t : TableSchema) (i : Nat) : String := "qed_chk_" ++ t.name.raw ++ "_" ++ toString i
def TableSchema.renderCreateTable (d : SqlDialect) (t : TableSchema) : String :=
  let chkDefs := t.checks.zipIdx.map fun (chk, i) => "CONSTRAINT \"" ++ t.chkName i ++ "\" CHECK (" ++ chk ++ ")"
  let defs := t.columns.map (·.renderDef d) ++ chkDefs
  "CREATE TABLE IF NOT EXISTS " ++ t.name.quoteIdent ++ " (" ++ String.intercalate ", " defs ++ ")"
def TableSchema.idxName (t : TableSchema) (i : Nat) : String := "idx_" ++ t.name.raw ++ "_" ++ toString i
private def renderCreateIndex (tbl : SqlIdent) (idxName : String) (cols : List SqlIdent) : String :=
  "CREATE INDEX IF NOT EXISTS \"" ++ idxName ++ "\" ON " ++ tbl.quoteIdent ++ " (" ++ SqlIdent.joinQuoted cols ++ ")"
def TableSchema.renderIndexes (t : TableSchema) : List String :=
  t.indexes.zipIdx.map fun (cols, i) => renderCreateIndex t.name (t.idxName i) cols
def TableSchema.renderDdlStatements (d : SqlDialect) (t : TableSchema) : List String :=
  t.renderCreateTable d :: t.renderIndexes
def TableSchema.renderPostgresChecks (t : TableSchema) : List String :=
  t.checks.zipIdx.map fun (chk, i) =>
    let cn := t.chkName i
    s!"DO $qed_chk$ BEGIN IF NOT EXISTS (SELECT 1 FROM pg_constraint WHERE conname = '{cn}' AND conrelid = '{t.name.quoteIdent}'::regclass) THEN ALTER TABLE {t.name.quoteIdent} ADD CONSTRAINT \"{cn}\" CHECK ({chk}) NOT VALID; END IF; END $qed_chk$"
def TableSchema.renderPostgresRls (t : TableSchema) : List String :=
  let pols :=
    (t.rlsRead?.map fun e => s!"CREATE POLICY \"qed_read_{t.name.raw}\" ON {t.name.quoteIdent} FOR SELECT USING ({e})").toList ++
    (t.rlsWrite?.map fun e => s!"CREATE POLICY \"qed_write_{t.name.raw}\" ON {t.name.quoteIdent} FOR ALL USING ({e}) WITH CHECK ({e})").toList
  if pols.isEmpty then [] else ("ALTER TABLE " ++ t.name.quoteIdent ++ " ENABLE ROW LEVEL SECURITY") :: pols
def renderDatabaseDdl (d : SqlDialect) (tables : List TableSchema) : String := joinSqlStmts (tables.flatMap (·.renderDdlStatements d))
def renderDatabaseCheckDdl (tables : List TableSchema) : String := joinSqlStmts (tables.flatMap (·.renderPostgresChecks))
def renderDatabaseRlsDdl (tables : List TableSchema) : String := joinSqlStmts (tables.flatMap (·.renderPostgresRls))

/-! ## Pure Verified Schema Diffing & Safe Additive Migrations (`MigrationStep`) -/

inductive MigrationStep where
  | createTable (table : TableSchema)
  | addColumn   (table : SqlIdent) (col : ColumnSchema) (defaultSql? : Option String := none)
  | createIndex (table : SqlIdent) (idxName : String) (cols : List SqlIdent)
deriving Inhabited

private def ColumnSchema.isUnconstrained (c : ColumnSchema) : Bool := !c.isPrimaryKey && !c.isUnique && c.references?.isNone
def ColumnSchema.isAdditiveSafe (c : ColumnSchema) : Bool :=
  c.isUnconstrained && (c.nullable || match c.checkSql? with | none => true | some chk => chk == "\"" ++ c.name.raw ++ "\" >= 0")
def ColumnSchema.safeDefaultSql (d : SqlDialect) (c : ColumnSchema) : Option String :=
  if c.nullable || !c.isAdditiveSafe then none
  else some <| match c.colType with | .text => "''" | .int => "0" | .bool => d.pick "FALSE" "0" | .bytes => d.pick "'\\x'" "X''"
def TableSchema.indexNames (t : TableSchema) : List String := t.indexes.zipIdx.map fun (_, i) => t.idxName i

def diffTableSchema (existingCols existingIdxNames : List String) (desired : TableSchema) (tableExists : Bool) : List MigrationStep :=
  if !tableExists then
    .createTable desired :: desired.indexes.zipIdx.map fun (cols, i) => .createIndex desired.name (desired.idxName i) cols
  else
    desired.columns.filterMap (fun col => if existingCols.contains col.name.raw then none else some (.addColumn desired.name col none)) ++
    desired.indexes.zipIdx.filterMap fun (cols, i) =>
      let idxName := desired.idxName i; if existingIdxNames.contains idxName then none else some (.createIndex desired.name idxName cols)

def diffTableSchemas (oldTables newTables : List TableSchema) : List MigrationStep :=
  newTables.flatMap fun newT => match oldTables.find? (·.name.raw == newT.name.raw) with
    | none => diffTableSchema [] [] newT false
    | some oldT => diffTableSchema (oldT.columns.map (·.name.raw)) oldT.indexNames newT true

def MigrationStep.render (d : SqlDialect) : MigrationStep → String
  | .createTable t => t.renderCreateTable d
  | .addColumn tbl col explicitDef? =>
      "ALTER TABLE " ++ tbl.quoteIdent ++ d.pick " ADD COLUMN IF NOT EXISTS " " ADD COLUMN " ++
        col.renderCore d (optClause (explicitDef?.orElse fun _ => col.safeDefaultSql d) (" DEFAULT " ++ ·))
  | .createIndex tbl idxName cols => renderCreateIndex tbl idxName cols
def renderMigrationDdl (d : SqlDialect) (steps : List MigrationStep) : String := joinSqlStmts (steps.map (·.render d))

def verifyMigrationSafe : List MigrationStep → Except String Unit
  | [] => .ok ()
  | .addColumn tbl col def? :: rest =>
      if col.isAdditiveSafe || (def?.isSome && col.isUnconstrained && col.checkSql?.isNone) then verifyMigrationSafe rest
      else .error s!"unsafe additive migration on `{tbl.raw}.{col.name.raw}`: new non-nullable or constrained column could violate existing row invariants"
  | _ :: rest => verifyMigrationSafe rest

theorem verifyMigrationSafe_nullable_addColumn (tbl : SqlIdent) (col : ColumnSchema)
    (hNull : col.nullable = true) (hNoPk : col.isPrimaryKey = false) (hNoUniq : col.isUnique = false) (hNoFk : col.references? = none) :
    verifyMigrationSafe [.addColumn tbl col none] = .ok () := by
  simp [verifyMigrationSafe, ColumnSchema.isAdditiveSafe, ColumnSchema.isUnconstrained, hNull, hNoPk, hNoUniq, hNoFk]

private theorem filterMap_contains_map_self {α β γ : Type} [BEq β] [LawfulBEq β] (xs : List α) (key : α → β) (g : α → γ) :
    xs.filterMap (fun x => if (xs.map key).contains (key x) then none else some (g x)) = [] :=
  List.filterMap_eq_nil_iff.2 fun x hx => by rw [ite_eq_left (List.contains_iff_mem.2 (List.mem_map.2 ⟨x, hx, rfl⟩))]

theorem diffTableSchema_self_empty (t : TableSchema) :
    diffTableSchema (t.columns.map (·.name.raw)) t.indexNames t true = [] := by
  unfold diffTableSchema TableSchema.indexNames; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [filterMap_contains_map_self t.columns (·.name.raw), filterMap_contains_map_self t.indexes.zipIdx (fun p => t.idxName p.2)]
  rfl

/-! ## Driver-Agnostic Database Endpoint Config & Execution Result -/

inductive DbEndpoint where
  | urlEnv       (envVar : String)
  | postgresEnv  (urlEnvVar : String)
  | postgresUrl  (url : String) (ssrfGuard : Bool := true)
  | sqlitePath   (path : String)
  | sqliteEnv    (envVar : String) (defaultPath? : Option String := none)
  | cloudflareD1 (accountEnv : String) (accountDefault? : Option String)
                 (dbEnv : String) (dbDefault? : Option String) (tokenSecret : String)
  | turso        (urlEnv : String) (tokenSecret : String)
  | httpSql      (urlEnv : String) (tokenSecret? : Option String := none)
  | managedPostgres (dbName : String) (env : Qed.Cloud.DeployEnv)
deriving Inhabited, DecidableEq

structure DbConfig where
  name          : String
  endpoint      : DbEndpoint
  devFallback?  : Option DbEndpoint := none
  envEndpoints? : Option (Qed.Cloud.EnvMap DbEndpoint) := none
  isManaged     : Bool := false
  tables        : List TableSchema := []
  backfills     : List SqlQuery := []
deriving Inhabited

def DbConfig.endpointForEnv (cfg : DbConfig) (env : Qed.Cloud.DeployEnv) : DbEndpoint :=
  match cfg.envEndpoints? with
  | some em => em.get env
  | none    => match env with | .dev => cfg.devFallback?.getD cfg.endpoint | _ => cfg.endpoint

/-- Compile-time table metadata exposed for `database` `invariant` checks. -/
structure TableMetaInfo where
  name            : String
  metaColNames    : List String
  policies        : List String
  hasReadPolicy   : Bool
  hasInsertPolicy : Bool
  hasUpdatePolicy : Bool
  hasDeletePolicy : Bool
  hasWritePolicy  : Bool
deriving Inhabited, DecidableEq, Repr

/-- Construct a `DbConfig` targeting a dynamic runtime PostgreSQL URL (SSRF-guarded by default). -/
@[inline] def DbConfig.forPostgresUrl (url : String) (ssrfGuard : Bool := true) (name : String := "dynamic_pg") : DbConfig :=
  { name, endpoint := .postgresUrl url ssrfGuard }

abbrev DbRow := Array SqlVal
structure DbResult where
  rows     : Array DbRow := #[]
  affected : Nat := 0
deriving Inhabited

/-! ## Compact JSON Wire Encoding for `SqlVal` (Used Across SQLite FFI & HTTP SQL) -/

private def taggedObj (k ty : String) (kv : List (String × Json) := []) : Json := .obj ((k, .str ty) :: kv)
private def parseJsonIntCell (v? : Option Json) (badPfx missingErr : String) : Except String SqlVal :=
  match v? with | some (.str s) => (s.toInt?).elim (.error s!"{badPfx}: {s}") (.ok ∘ .int) | some (.num n) => .ok (.int n.mantissa) | _ => .error missingErr
private def parseJsonHexCell (v? : Option Json) (missingErr : String) : Except String SqlVal :=
  match v? with | some (.str hx) => (Proto.decodeHex hx).map .bytes | _ => .error missingErr
private def decodeJsonArrayRow (cellDec : Json → Except String SqlVal) (notArrErr : String) : Json → Except String DbRow
  | .arr vals => (vals.mapM cellDec).map List.toArray | _ => .error notArrErr
private def decodeJsonRows (j : Json) (key : String) (rowDec : Json → Except String DbRow) (notArrErr : String) : Except String (Array DbRow) :=
  match j.get? key with | some (.arr rs) => (rs.mapM rowDec).map List.toArray | none => .ok #[] | _ => .error notArrErr
private def encodeSqlValTagged (tKey vKey hexKey nT iT sT bT xT : String) (boolAsStr : Bool) : SqlVal → Json
  | .null => taggedObj tKey nT | .int i => taggedObj tKey iT [(vKey, .str (toString i))]
  | .text s => taggedObj tKey sT [(vKey, .str s)]
  | .bool b => taggedObj tKey bT [(vKey, if boolAsStr then .str (if b then "1" else "0") else .bool b)]
  | .bytes bs => taggedObj tKey xT [(hexKey, .str (Proto.encodeHex bs))]

def SqlVal.toTaggedJson : SqlVal → Json := encodeSqlValTagged "t" "v" "v" "n" "i" "s" "b" "x" false
def SqlVal.toPlainJson : SqlVal → Json
  | .null => .null | .int i => .num ⟨i, 0⟩ | .text s => .str s | .bool b => .bool b | .bytes bs => .str (Proto.encodeHex bs)

def SqlVal.fromTaggedJson : Json → Except String SqlVal
  | j@(.obj _) => match j.strAt? "t", j.get? "v" with
      | some "n", _ => .ok .null | some "i", v => parseJsonIntCell v "bad int" "missing int value"
      | some "s", some (.str s) => .ok (.text s) | some "s", _ => .error "missing string value"
      | some "b", some (.bool b) => .ok (.bool b) | some "b", some (.num n) => .ok (.bool (n.mantissa != 0)) | some "b", _ => .error "missing bool value"
      | some "x", v => parseJsonHexCell v "missing bytes hex" | _, _ => .error "unknown SqlVal tag"
  | .null => .ok .null | .str s => .ok (.text s) | .num n => .ok (.int n.mantissa) | .bool b => .ok (.bool b)
  | _ => .error "unexpected JSON value for SqlVal"

def encodeTaggedResultJson (res : DbResult) : String :=
  Json.render (.obj [("rows", .arr (res.rows.toList.map fun r => .arr (r.toList.map SqlVal.toTaggedJson))),
                     ("affected", .num ⟨Int.ofNat res.affected, 0⟩)])

def decodeTaggedResultJson (raw : String) : Except String DbResult := do
  let j@(.obj _) ← Json.parse raw 128 | .error "expected JSON object from database result"
  let rows ← decodeJsonRows j "rows" (decodeJsonArrayRow SqlVal.fromTaggedJson "expected row array") "expected rows array"
  return { rows, affected := (j.natAt? "affected").getD 0 }

namespace HttpSql
/-! ### HTTP SQL Wire Encoders & Decoders (Cloudflare D1, Turso Hrana v2, Generic HTTP SQL) -/

private def jsonObjBytes (fs : List (String × Json)) : ByteArray := (Json.render (.obj fs)).toUTF8
private def firstObjAt (j : Json) (k : String) : Option Json := match j.arrAt k with | o@(.obj _) :: _ => some o | _ => none
private def sqlStmtFields (sql : String) (params : Array SqlVal) (pKey : String) (enc : SqlVal → Json) : List (String × Json) :=
  [("sql", .str sql), (pKey, .arr (params.toList.map enc))]

def encodeGenericQueryBody (sql : String) (params : Array SqlVal) (dialect : SqlDialect) : ByteArray :=
  jsonObjBytes (sqlStmtFields sql params "params" SqlVal.toTaggedJson ++ [("dialect", .str (dialect.pick "postgres" "sqlite"))])
def encodeD1QueryBody (sql : String) (params : Array SqlVal) : ByteArray :=
  jsonObjBytes (sqlStmtFields sql params "params" SqlVal.toPlainJson)
def encodeTursoArg : SqlVal → Json := encodeSqlValTagged "type" "value" "base64" "null" "integer" "text" "integer" "blob" true
def encodeTursoPipelineBody (sql : String) (params : Array SqlVal) : ByteArray :=
  jsonObjBytes [("requests", .arr [taggedObj "type" "execute" [("stmt", .obj (sqlStmtFields sql params "args" encodeTursoArg))], taggedObj "type" "close"])]

def decodeTursoCell : Json → Except String SqlVal
  | j@(.obj _) => match j.strAt? "type", j.get? "value" with
      | some "null", _ => .ok .null | some "integer", v => parseJsonIntCell v "turso bad int" "turso missing integer value"
      | some "text", some (.str s) => .ok (.text s) | some "text", _ => .error "turso missing text value"
      | some "float", some (.str s) => .ok (.text s) | some "float", some (.num n) => .ok (.int n.mantissa) | some "float", _ => .error "turso missing float value"
      | some "blob", _ => parseJsonHexCell (j.get? "base64") "turso missing blob payload" | _, _ => .error "turso unknown cell type"
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
  | .select _ cols _ _ _ _ | .selectSchema _ _ cols _ _ _ _ | .insert _ _ cols _ _ | .insertOrIgnore _ _ _ cols _ _ | .upsert _ _ _ _ _ cols | .update _ _ _ cols | .delete _ _ cols => cols.map (·.raw)
  | .joinSelect _ _ lc rc _ _ _ _ _ _ _ => lc.map (·.raw) ++ rc.map (·.raw) | .selectAll _ _ _ _ _ | .count _ _ | .countSchema _ _ _ | .aggregate _ _ _ _ => []
end HttpSql

/-- Branded transaction handle carrying a live transaction ID for a specific `database`. -/
structure DbTx (dbTag : String) where
  id : UInt64
deriving Inhabited

end Qed.Server.Db
