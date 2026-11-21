import Qed.Json.Lawful
import Qed.Proto

namespace Qed.Server.Db

/-! ## Typed SQL Values & Wire Codecs (`SqlVal`, `ToSql`, `FromSql`) -/

inductive SqlVal where
  | null
  | int   (v : Int)
  | text  (v : String)
  | bool  (v : Bool)
  | bytes (v : ByteArray)
deriving Inhabited, DecidableEq

class ToSql (α : Type) where
  toSql : α → SqlVal

class FromSql (α : Type) where
  fromSql : SqlVal → Except String α

instance : ToSql String where
  toSql := .text

instance : FromSql String where
  fromSql
    | .text s => .ok s
    | .int i  => .ok (toString i)
    | .bool b => .ok (if b then "true" else "false")
    | .null   => .error "expected TEXT, got NULL"
    | .bytes _ => .error "expected TEXT, got BLOB"

instance : ToSql Int where
  toSql := .int

instance : FromSql Int where
  fromSql
    | .int i  => .ok i
    | .text s => match s.toInt? with | some i => .ok i | none => .error s!"invalid INT: {s}"
    | .bool b => .ok (if b then 1 else 0)
    | .null   => .error "expected INT, got NULL"
    | .bytes _ => .error "expected INT, got BLOB"

instance : ToSql Nat where
  toSql n := .int (Int.ofNat n)

instance : FromSql Nat where
  fromSql v := do
    let i ← FromSql.fromSql (α := Int) v
    if 0 ≤ i then .ok i.toNat
    else .error s!"expected non-negative Nat, got {i}"

instance : ToSql Bool where
  toSql := .bool

instance : FromSql Bool where
  fromSql
    | .bool b => .ok b
    | .int i  => .ok (i != 0)
    | .text s =>
        if s == "true" || s == "t" || s == "1" then .ok true
        else if s == "false" || s == "f" || s == "0" then .ok false
        else .error s!"invalid BOOL: {s}"
    | .null   => .error "expected BOOL, got NULL"
    | .bytes _ => .error "expected BOOL, got BLOB"

instance : ToSql ByteArray where
  toSql := .bytes

instance : FromSql ByteArray where
  fromSql
    | .bytes bs => .ok bs
    | .text s   =>
        if s.startsWith "\\x" then Proto.decodeHex (String.ofList (s.toList.drop 2))
        else Proto.decodeHex s
    | .null     => .error "expected BLOB, got NULL"
    | _         => .error "expected BLOB"

instance {α : Type} [ToSql α] : ToSql (Option α) where
  toSql
    | none   => .null
    | some a => ToSql.toSql a

instance {α : Type} [FromSql α] : FromSql (Option α) where
  fromSql
    | .null => .ok none
    | v     => (FromSql.fromSql (α := α) v).map some

/-- Converts a homogeneous list or array of SQL values into parameterized `IN (...)` bindings. -/
class ToSqlList (α : Type) where
  toSqlList : α → List SqlVal

instance {α : Type} [ToSql α] : ToSqlList (List α) where
  toSqlList xs := xs.map ToSql.toSql

instance {α : Type} [ToSql α] : ToSqlList (Array α) where
  toSqlList xs := xs.toList.map ToSql.toSql

/-- Escapes SQL `LIKE` wildcards (`%`, `_`) and escape character (`!`) for safe parameterized `LIKE ... ESCAPE '!'`. -/
def escapeLikePattern (s : String) : String :=
  String.ofList (s.toList.flatMap fun c =>
    if c == '!' || c == '%' || c == '_' then ['!', c] else [c])

def endsWithLikeVal (s : String) : SqlVal := .text ("%" ++ escapeLikePattern s)

/-! ## Validated SQL Identifiers (`SqlIdent` & Injection Closure) -/

@[inline] def isSqlIdentHeadChar (c : Char) : Bool :=
  let n := c.toNat
  (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || n == 95

@[inline] def isSqlIdentBodyChar (c : Char) : Bool :=
  let n := c.toNat
  (48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) || n == 95

def isSafeSqlIdent (s : String) : Bool :=
  match s.toList with
  | []      => false
  | c :: cs => isSqlIdentHeadChar c && cs.all isSqlIdentBodyChar && decide (cs.length < 63)

structure SqlIdent where
  raw   : String
  valid : isSafeSqlIdent raw = true
deriving DecidableEq, Repr

instance : Inhabited SqlIdent := ⟨⟨"id", by decide⟩⟩

theorem isSafeSqlIdent_all_body {s : String} (h : isSafeSqlIdent s = true) :
    ∀ c ∈ s.toList, isSqlIdentBodyChar c = true := by
  unfold isSafeSqlIdent at h
  cases hcs : s.toList with
  | nil => rw [hcs] at h; contradiction
  | cons hd tl =>
      rw [hcs] at h
      simp only [Bool.and_eq_true, List.all_eq_true] at h
      intro c hc
      rcases List.mem_cons.1 hc with rfl | htl
      · have hhd := h.1.1
        unfold isSqlIdentHeadChar at hhd
        unfold isSqlIdentBodyChar
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hhd ⊢
        omega
      · exact h.1.2 c htl

/-- No validated `SqlIdent` can ever contain quotes, semicolons, dashes, slashes, spaces, or NUL bytes. -/
theorem isSafeSqlIdent_no_inject (id : SqlIdent) :
    ∀ c ∈ id.raw.toList,
      c ≠ '\'' ∧ c ≠ '"' ∧ c ≠ ';' ∧ c ≠ '-' ∧ c ≠ '/' ∧ c ≠ '\\' ∧ c ≠ ' ' ∧ c ≠ '\x00' := by
  intro c hc
  have hb := isSafeSqlIdent_all_body id.valid c hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro heq; subst heq; simp [isSqlIdentBodyChar] at hb)

private theorem str_append_no_semi {a b : String}
    (ha : ∀ c ∈ a.toList, c ≠ ';') (hb : ∀ c ∈ b.toList, c ≠ ';') :
    ∀ c ∈ (a ++ b).toList, c ≠ ';' := by
  intro c hc; rw [String.toList_append, List.mem_append] at hc; exact hc.elim (ha c) (hb c)

private theorem lit_no_semi (s : String) (h : s.toList.all (· != ';') = true) :
    ∀ c ∈ s.toList, c ≠ ';' := by
  intro c hc; rw [List.all_eq_true] at h; simpa using h c hc

def SqlIdent.quoteIdent (id : SqlIdent) : String :=
  "\"" ++ id.raw ++ "\""

theorem SqlIdent.quoteIdent_no_semicolon (id : SqlIdent) :
    ∀ c ∈ id.quoteIdent.toList, c ≠ ';' :=
  str_append_no_semi (str_append_no_semi (lit_no_semi "\"" rfl) fun c hc => (isSafeSqlIdent_no_inject id c hc).2.2.1)
    (lit_no_semi "\"" rfl)

/-! ## Typed Parameterized SQL AST (`SqlExpr`, `SqlQuery`, `SqlDialect`) -/

inductive SqlDialect where
  | postgres
  | sqlite
deriving Inhabited, DecidableEq, Repr

inductive SqlBinOp where
  | eq | ne | lt | le | gt | ge | and | or | add | sub | mul
deriving Inhabited, DecidableEq, Repr

def SqlBinOp.render : SqlBinOp → String
  | .eq  => " = "
  | .ne  => " <> "
  | .lt  => " < "
  | .le  => " <= "
  | .gt  => " > "
  | .ge  => " >= "
  | .and => " AND "
  | .or  => " OR "
  | .add => " + "
  | .sub => " - "
  | .mul => " * "

theorem SqlBinOp.render_no_semicolon (op : SqlBinOp) :
    ∀ c ∈ op.render.toList, c ≠ ';' := by
  cases op <;> exact lit_no_semi _ rfl

inductive SqlExpr where
  | litTrue
  | litFalse
  | col        (name : SqlIdent)
  | param      (val : SqlVal)
  | binOp      (op : SqlBinOp) (lhs rhs : SqlExpr)
  | not        (e : SqlExpr)
  | isNull     (e : SqlExpr)
  | isNotNull  (e : SqlExpr)
  | strLen     (e : SqlExpr)
  | like       (lhs rhs : SqlExpr)
  | startsWith (lhs rhs : SqlExpr)
  | contains   (lhs rhs : SqlExpr)
  | inList     (lhs : SqlExpr) (vals : List SqlVal)
deriving Inhabited, DecidableEq

/-- Replaces every runtime `SqlVal` payload with `.null`, preserving the exact AST skeleton. -/
def SqlExpr.eraseVals : SqlExpr → SqlExpr
  | .litTrue        => .litTrue
  | .litFalse       => .litFalse
  | .col name       => .col name
  | .param _        => .param .null
  | .binOp op l r   => .binOp op l.eraseVals r.eraseVals
  | .not e          => .not e.eraseVals
  | .isNull e       => .isNull e.eraseVals
  | .isNotNull e    => .isNotNull e.eraseVals
  | .strLen e       => .strLen e.eraseVals
  | .like l r       => .like l.eraseVals r.eraseVals
  | .startsWith l r => .startsWith l.eraseVals r.eraseVals
  | .contains l r   => .contains l.eraseVals r.eraseVals
  | .inList l vs    => .inList l.eraseVals (List.replicate vs.length .null)

/-- Two `SqlExpr`s have the same AST skeleton when they are identical everywhere except
    possibly the runtime `SqlVal` payloads inside `.param` / `.inList` leaves. -/
abbrev SqlExpr.sameShape (e₁ e₂ : SqlExpr) : Prop :=
  e₁.eraseVals = e₂.eraseVals

def placeholder (d : SqlDialect) (idx : Nat) : String :=
  match d with
  | .postgres => "$" ++ toString idx
  | .sqlite   => "?" ++ toString idx

theorem nat_toString_digits (n : Nat) :
    ∀ c ∈ (toString n).toList, '0' ≤ c ∧ c ≤ '9' := by
  have hdig : ∀ k : Fin 10, '0' ≤ Nat.digitChar k.val ∧ Nat.digitChar k.val ≤ '9' := by decide
  have hmem : ∀ m (b : Nat) (acc : List Char),
      (∀ y ∈ acc, '0' ≤ y ∧ y ≤ '9') →
      ∀ y ∈ Nat.toDigitsCore 10 m b acc, '0' ≤ y ∧ y ≤ '9' := by
    intro m; induction m with
    | zero => intro _ _ hacc y hy; exact hacc y hy
    | succ m ih =>
        intro b acc hacc y hy
        unfold Nat.toDigitsCore at hy; dsimp only at hy
        have hd := hdig ⟨b % 10, Nat.mod_lt b (by decide)⟩
        split at hy
        · exact (List.mem_cons.1 hy).elim (· ▸ hd) (hacc y)
        · exact ih (b / 10) _ (fun z hz => (List.mem_cons.1 hz).elim (· ▸ hd) (hacc z)) y hy
  intro c hc
  have hrepr : (toString n).toList = Nat.toDigits 10 n := by
    change (Nat.repr n).toList = Nat.toDigits 10 n; unfold Nat.repr; exact String.toList_ofList
  rw [hrepr] at hc
  exact hmem (n + 1) n [] (fun _ h => False.elim (List.not_mem_nil h)) c hc

private theorem nat_toString_no_semicolon (n : Nat) :
    ∀ c ∈ (toString n).toList, c ≠ ';' := by
  intro c hc heq; subst heq
  exact absurd (nat_toString_digits n ';' hc) (by decide)

theorem placeholder_no_semicolon (d : SqlDialect) (idx : Nat) :
    ∀ c ∈ (placeholder d idx).toList, c ≠ ';' := by
  cases d <;> exact str_append_no_semi (lit_no_semi _ rfl) (nat_toString_no_semicolon idx)

private def compileInParams (d : SqlDialect) : List SqlVal → Array SqlVal → String × Array SqlVal
  | [], params => ("", params)
  | [v], params => (placeholder d (params.size + 1), params.push v)
  | v :: v2 :: rest, params =>
      let ph := placeholder d (params.size + 1)
      let (tail, p2) := compileInParams d (v2 :: rest) (params.push v)
      (ph ++ ", " ++ tail, p2)

private theorem compileInParams_eraseVals (d : SqlDialect) :
    ∀ (vs : List SqlVal) (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
      (compileInParams d vs p₁).1 = (compileInParams d (List.replicate vs.length .null) p₂).1 ∧
      (compileInParams d vs p₁).2.size = (compileInParams d (List.replicate vs.length .null) p₂).2.size
  | [], _, _, hsz => ⟨rfl, hsz⟩
  | [_], _, _, hsz => by simp [compileInParams, hsz]
  | v :: x :: rest, p₁, p₂, hsz => by
      have hsub := compileInParams_eraseVals d (x :: rest) (p₁.push v) (p₂.push .null) (by simp [hsz])
      simp [compileInParams, List.replicate, hsz, hsub.1, hsub.2]

private theorem compileInParams_no_semicolon (d : SqlDialect) :
    ∀ (vs : List SqlVal) (params : Array SqlVal),
      ∀ c ∈ (compileInParams d vs params).1.toList, c ≠ ';'
  | [], _ => fun _ h => False.elim (List.not_mem_nil h)
  | [_], params => placeholder_no_semicolon d (params.size + 1)
  | v :: x :: rest, params => by
      simp only [compileInParams]
      exact str_append_no_semi
        (str_append_no_semi (placeholder_no_semicolon d (params.size + 1)) (lit_no_semi ", " rfl))
        (compileInParams_no_semicolon d (x :: rest) (params.push v))

local syntax "solve_no_semi" (" with " tactic)? : tactic
local macro_rules
  | `(tactic| solve_no_semi $[with $t]?) => do
    let extra ← match t with | some t => pure t | none => `(tactic| fail)
    `(tactic| ((intro c hc); (try simp only [String.toList_append, List.mem_append] at hc); (revert hc); (try simp only [or_imp]); repeat any_goals constructor) <;>
      (intro hc; first
        | with_reducible exact ‹∀ c ∈ _, c ≠ ';'› c hc
        | with_reducible exact SqlIdent.quoteIdent_no_semicolon _ c hc
        | with_reducible exact SqlBinOp.render_no_semicolon _ c hc
        | with_reducible exact placeholder_no_semicolon _ _ c hc
        | with_reducible exact nat_toString_no_semicolon _ c hc
        | with_reducible exact compileInParams_no_semicolon _ _ _ c hc
        | with_reducible ($extra:tactic)
        | exact lit_no_semi _ rfl c hc))

def SqlExpr.compileQual (d : SqlDialect) (pfx : String) (e : SqlExpr) (params : Array SqlVal) :
    String × Array SqlVal :=
  match e with
  | .litTrue  => (match d with | .postgres => "TRUE" | .sqlite => "1", params)
  | .litFalse => (match d with | .postgres => "FALSE" | .sqlite => "0", params)
  | .col id   => (pfx ++ id.quoteIdent, params)
  | .param v  =>
      let idx := params.size + 1
      (placeholder d idx, params.push v)
  | .binOp op l r =>
      let (sl, p1) := l.compileQual d pfx params
      let (sr, p2) := r.compileQual d pfx p1
      ("(" ++ sl ++ op.render ++ sr ++ ")", p2)
  | .not inner =>
      let (s, p1) := inner.compileQual d pfx params
      ("(NOT " ++ s ++ ")", p1)
  | .isNull inner =>
      let (s, p1) := inner.compileQual d pfx params
      ("(" ++ s ++ " IS NULL)", p1)
  | .isNotNull inner =>
      let (s, p1) := inner.compileQual d pfx params
      ("(" ++ s ++ " IS NOT NULL)", p1)
  | .strLen inner =>
      let (s, p1) := inner.compileQual d pfx params
      ("LENGTH(" ++ s ++ ")", p1)
  | .like l r =>
      let (sl, p1) := l.compileQual d pfx params
      let (sr, p2) := r.compileQual d pfx p1
      ("(" ++ sl ++ " LIKE " ++ sr ++ " ESCAPE '!')", p2)
  | .startsWith l r =>
      let (sl, p1) := l.compileQual d pfx params
      let (sr1, p2) := r.compileQual d pfx p1
      let (sr2, p3) := r.compileQual d pfx p2
      ("(SUBSTR(" ++ sl ++ ", 1, LENGTH(" ++ sr1 ++ ")) = " ++ sr2 ++ ")", p3)
  | .contains l r =>
      let (sl, p1) := l.compileQual d pfx params
      let (sr, p2) := r.compileQual d pfx p1
      let fnName := match d with | .postgres => "STRPOS(" | .sqlite => "INSTR("
      ("(" ++ fnName ++ sl ++ ", " ++ sr ++ ") > 0)", p2)
  | .inList l vs =>
      match vs with
      | [] => (match d with | .postgres => "FALSE" | .sqlite => "0", params)
      | _ :: _ =>
          let (sl, p1) := l.compileQual d pfx params
          let (svs, p2) := compileInParams d vs p1
          ("(" ++ sl ++ " IN (" ++ svs ++ "))", p2)

def SqlExpr.compile (d : SqlDialect) (e : SqlExpr) (params : Array SqlVal) :
    String × Array SqlVal :=
  e.compileQual d "" params

private theorem SqlExpr.compileQual_eraseVals (d : SqlDialect) (pfx : String) (e : SqlExpr) :
    ∀ (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
      (e.compileQual d pfx p₁).1 = (e.eraseVals.compileQual d pfx p₂).1 ∧
      (e.compileQual d pfx p₁).2.size = (e.eraseVals.compileQual d pfx p₂).2.size := by
  induction e with
  | litTrue | litFalse | col _ | param _ =>
      intro _ _ hsz; simp [SqlExpr.eraseVals, SqlExpr.compileQual, hsz]
  | not _ ih | isNull _ ih | isNotNull _ ih | strLen _ ih =>
      intro p₁ p₂ hsz; have ⟨h1, h2⟩ := ih p₁ p₂ hsz; simp [SqlExpr.eraseVals, SqlExpr.compileQual, h1, h2]
  | binOp _ _ _ ihl ihr | like _ _ ihl ihr | contains _ _ ihl ihr =>
      intro p₁ p₂ hsz; have ⟨h1, h2⟩ := ihl p₁ p₂ hsz; have ⟨h3, h4⟩ := ihr _ _ h2
      simp [SqlExpr.eraseVals, SqlExpr.compileQual, h1, h3, h4]
  | startsWith _ _ ihl ihr =>
      intro p₁ p₂ hsz; have ⟨h1, h2⟩ := ihl p₁ p₂ hsz
      have ⟨h3, h4⟩ := ihr _ _ h2; have ⟨h5, h6⟩ := ihr _ _ h4
      simp [SqlExpr.eraseVals, SqlExpr.compileQual, h1, h3, h5, h6]
  | inList _ vs ihl =>
      intro p₁ p₂ hsz
      cases vs with
      | nil => simp [SqlExpr.eraseVals, SqlExpr.compileQual, hsz]
      | cons v vs' =>
          have ⟨h1, h2⟩ := ihl p₁ p₂ hsz
          have ⟨h3, h4⟩ := compileInParams_eraseVals d (v :: vs') _ _ h2
          simp [SqlExpr.eraseVals, SqlExpr.compileQual, List.replicate, h1, h3, h4]

theorem SqlExpr.compileQual_sameShape (d : SqlDialect) (pfx : String) {e₁ e₂ : SqlExpr}
    (hsh : e₁.sameShape e₂) :
    ∀ (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
      (e₁.compileQual d pfx p₁).1 = (e₂.compileQual d pfx p₂).1 ∧
      (e₁.compileQual d pfx p₁).2.size = (e₂.compileQual d pfx p₂).2.size := by
  intro p₁ p₂ hsz
  have ⟨h1, h2⟩ := e₁.compileQual_eraseVals d pfx p₁ p₂ hsz
  have ⟨h3, h4⟩ := e₂.compileQual_eraseVals d pfx p₂ p₂ rfl
  rw [hsh] at h1 h2
  exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩

/-- Non-interference for `SqlExpr.compile`: changing runtime parameter values leaves the
    compiled SQL string AND parameter count bit-for-bit identical. -/
theorem SqlExpr.compile_sameShape (d : SqlDialect) {e₁ e₂ : SqlExpr}
    (hsh : e₁.sameShape e₂) :
    ∀ (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
      (e₁.compile d p₁).1 = (e₂.compile d p₂).1 ∧
      (e₁.compile d p₁).2.size = (e₂.compile d p₂).2.size :=
  SqlExpr.compileQual_sameShape d "" hsh

theorem SqlExpr.compileQual_no_semicolon (d : SqlDialect) (pfx : String)
    (hpfx : ∀ c ∈ pfx.toList, c ≠ ';') (e : SqlExpr) :
    ∀ (params : Array SqlVal), ∀ c ∈ (e.compileQual d pfx params).1.toList, c ≠ ';' := by
  induction e with
  | litTrue | litFalse => intro _; simp only [SqlExpr.compileQual]; cases d <;> exact lit_no_semi _ rfl
  | col _ | param _ => intro _; simp only [SqlExpr.compileQual]; solve_no_semi
  | not _ ih | isNull _ ih | isNotNull _ ih | strLen _ ih =>
      intro params; simp only [SqlExpr.compileQual]
      solve_no_semi with exact ih _ _ ‹_›
  | binOp _ _ _ ihl ihr | like _ _ ihl ihr | startsWith _ _ ihl ihr =>
      intro params; simp only [SqlExpr.compileQual]
      solve_no_semi with (first | exact ihl _ _ ‹_› | exact ihr _ _ ‹_›)
  | contains _ _ ihl ihr =>
      intro params; simp only [SqlExpr.compileQual]
      have hfn : ∀ c ∈ (match d with | .postgres => "STRPOS(" | .sqlite => "INSTR(").toList, c ≠ ';' := by
        cases d <;> exact lit_no_semi _ rfl
      solve_no_semi with (first | exact hfn _ ‹_› | exact ihl _ _ ‹_› | exact ihr _ _ ‹_›)
  | inList _ vs ihl =>
      intro params
      cases vs with
      | nil => simp only [SqlExpr.compileQual]; cases d <;> exact lit_no_semi _ rfl
      | cons _ _ =>
          simp only [SqlExpr.compileQual]
          solve_no_semi with exact ihl _ _ ‹_›

theorem SqlExpr.compile_no_semicolon (d : SqlDialect) (e : SqlExpr) :
    ∀ (params : Array SqlVal), ∀ c ∈ (e.compile d params).1.toList, c ≠ ';' :=
  SqlExpr.compileQual_no_semicolon d "" (fun _ h => False.elim (List.not_mem_nil h)) e

inductive SqlOrderDir where
  | asc | desc
deriving Inhabited, DecidableEq, Repr

inductive SqlAggOp where
  | sum | min | max
deriving Inhabited, DecidableEq, Repr

def SqlAggOp.render : SqlAggOp → String
  | .sum => "SUM"
  | .min => "MIN"
  | .max => "MAX"

theorem SqlAggOp.render_no_semicolon (op : SqlAggOp) :
    ∀ c ∈ op.render.toList, c ≠ ';' := by
  cases op <;> exact lit_no_semi _ rfl

inductive SqlQuery where
  | select (table : SqlIdent) (cols : List SqlIdent) (whereExpr : SqlExpr)
           (orderBy : Option (SqlIdent × SqlOrderDir) := none)
           (limit : Option Nat := none)
           (offset : Option Nat := none)
  | count  (table : SqlIdent) (whereExpr : SqlExpr)
  | aggregate (op : SqlAggOp) (table : SqlIdent) (col : SqlIdent) (whereExpr : SqlExpr)
  | joinSelect (leftTable rightTable : SqlIdent)
               (leftCols rightCols : List SqlIdent)
               (leftJoinCol rightJoinCol : SqlIdent)
               (leftWhere rightWhere : SqlExpr)
               (orderBy : Option (SqlIdent × SqlOrderDir) := none)
               (limit : Option Nat := none)
               (offset : Option Nat := none)
  | insert (table : SqlIdent) (cols : List (SqlIdent × SqlVal)) (returning : List SqlIdent)
  | update (table : SqlIdent) (sets : List (SqlIdent × SqlExpr)) (whereExpr : SqlExpr)
           (returning : List SqlIdent)
  | delete (table : SqlIdent) (whereExpr : SqlExpr) (returning : List SqlIdent)
deriving Inhabited, DecidableEq

def SqlIdent.joinQuotedPrefixed (pfx : String) : List SqlIdent → String
  | []      => pfx ++ "*"
  | [c]     => pfx ++ c.quoteIdent
  | c :: cs => pfx ++ c.quoteIdent ++ ", " ++ joinQuotedPrefixed pfx cs

abbrev SqlIdent.joinQuoted : List SqlIdent → String :=
  SqlIdent.joinQuotedPrefixed ""

theorem SqlIdent.joinQuotedPrefixed_no_semicolon (pfx : String)
    (hpfx : ∀ c ∈ pfx.toList, c ≠ ';') : ∀ (cs : List SqlIdent),
    ∀ c ∈ (SqlIdent.joinQuotedPrefixed pfx cs).toList, c ≠ ';'
  | [] => str_append_no_semi hpfx (lit_no_semi "*" rfl)
  | [x] => str_append_no_semi hpfx x.quoteIdent_no_semicolon
  | x :: y :: rest =>
      str_append_no_semi
        (str_append_no_semi (str_append_no_semi hpfx x.quoteIdent_no_semicolon) (lit_no_semi ", " rfl))
        (SqlIdent.joinQuotedPrefixed_no_semicolon pfx hpfx (y :: rest))

private def compileSets (d : SqlDialect) :
    List (SqlIdent × SqlExpr) → Array SqlVal → String × Array SqlVal
  | [], params => ("", params)
  | [(col, e)], params =>
      let (se, p1) := e.compile d params
      (col.quoteIdent ++ " = " ++ se, p1)
  | (col, e) :: rest, params =>
      let (se, p1) := e.compile d params
      let (tail, p2) := compileSets d rest p1
      (col.quoteIdent ++ " = " ++ se ++ ", " ++ tail, p2)

private theorem compileSets_eraseVals (d : SqlDialect) :
    ∀ (l : List (SqlIdent × SqlExpr)) (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
      (compileSets d l p₁).1 = (compileSets d (l.map fun (c, e) => (c, e.eraseVals)) p₂).1 ∧
      (compileSets d l p₁).2.size = (compileSets d (l.map fun (c, e) => (c, e.eraseVals)) p₂).2.size
  | [], _, _, hsz => ⟨rfl, hsz⟩
  | [(_, e)], p₁, p₂, hsz => by
      have ⟨h1, h2⟩ := e.compileQual_eraseVals d "" p₁ p₂ hsz
      simp [compileSets, SqlExpr.compile, h1, h2]
  | (_, e) :: x :: rest, p₁, p₂, hsz => by
      have ⟨h1, h2⟩ := e.compileQual_eraseVals d "" p₁ p₂ hsz
      have ⟨h3, h4⟩ := compileSets_eraseVals d (x :: rest) _ _ h2
      simp [compileSets, SqlExpr.compile, h1, h3, h4]

private theorem compileSets_no_semicolon (d : SqlDialect) :
    ∀ (l : List (SqlIdent × SqlExpr)) (params : Array SqlVal),
      ∀ c ∈ (compileSets d l params).1.toList, c ≠ ';'
  | [], _ => fun _ h => False.elim (List.not_mem_nil h)
  | [(_, _)], _ => by simp only [compileSets]; solve_no_semi with exact SqlExpr.compile_no_semicolon _ _ _ _ ‹_›
  | (_, e) :: x :: rest, params => by
      simp only [compileSets]
      solve_no_semi with (first
        | exact SqlExpr.compile_no_semicolon _ _ _ _ ‹_›
        | exact compileSets_no_semicolon d (x :: rest) (e.compile d params).2 _ ‹_›)

/-- Replaces every runtime `SqlVal` in a `SqlQuery` with `.null`, preserving the exact SQL skeleton. -/
def SqlQuery.eraseVals : SqlQuery → SqlQuery
  | .select t c w o l off => .select t c w.eraseVals o l off
  | .count t w => .count t w.eraseVals
  | .aggregate op t c w => .aggregate op t c w.eraseVals
  | .joinSelect lt rt lc rc lj rj lw rw o l off =>
      .joinSelect lt rt lc rc lj rj lw.eraseVals rw.eraseVals o l off
  | .insert t cols ret => .insert t (cols.map fun (c, _) => (c, .null)) ret
  | .update t s w ret => .update t (s.map fun (c, e) => (c, e.eraseVals)) w.eraseVals ret
  | .delete t w ret => .delete t w.eraseVals ret

abbrev SqlQuery.sameShape (q₁ q₂ : SqlQuery) : Prop :=
  q₁.eraseVals = q₂.eraseVals

def renderReturning (ret : List SqlIdent) : String :=
  if ret.isEmpty then "" else " RETURNING " ++ SqlIdent.joinQuoted ret

private theorem renderReturning_no_semicolon (ret : List SqlIdent) :
    ∀ c ∈ (renderReturning ret).toList, c ≠ ';' := by
  unfold renderReturning
  split
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · exact str_append_no_semi (lit_no_semi " RETURNING " rfl)
      (SqlIdent.joinQuotedPrefixed_no_semicolon "" (lit_no_semi "" rfl) ret)

private def renderLimitOffset (d : SqlDialect) (limit? offset? : Option Nat) : String :=
  match limit?, offset? with
  | none, none => ""
  | some n, none => " LIMIT " ++ toString n
  | some n, some off => " LIMIT " ++ toString n ++ " OFFSET " ++ toString off
  | none, some off =>
      match d with
      | .postgres => " OFFSET " ++ toString off
      | .sqlite   => " LIMIT -1 OFFSET " ++ toString off

private theorem renderLimitOffset_no_semicolon (d : SqlDialect) (limit? offset? : Option Nat) :
    ∀ c ∈ (renderLimitOffset d limit? offset?).toList, c ≠ ';' := by
  unfold renderLimitOffset
  cases limit? <;> cases offset? <;> try cases d
  all_goals solve_no_semi

private def renderOrderBy (pfx : String) (orderBy? : Option (SqlIdent × SqlOrderDir)) : String :=
  match orderBy? with
  | none => ""
  | some (col, .asc)  => " ORDER BY " ++ pfx ++ col.quoteIdent ++ " ASC"
  | some (col, .desc) => " ORDER BY " ++ pfx ++ col.quoteIdent ++ " DESC"

private theorem renderOrderBy_no_semicolon (pfx : String) (hpfx : ∀ c ∈ pfx.toList, c ≠ ';')
    (orderBy? : Option (SqlIdent × SqlOrderDir)) :
    ∀ c ∈ (renderOrderBy pfx orderBy?).toList, c ≠ ';' := by
  unfold renderOrderBy
  cases orderBy? with
  | none => exact lit_no_semi "" rfl
  | some p => rcases p with ⟨_, dir⟩; cases dir <;> solve_no_semi

def SqlQuery.compile (d : SqlDialect) : SqlQuery → String × Array SqlVal
  | .select tbl cols whereExpr orderBy? limit? offset? =>
      let (wSql, params) := whereExpr.compile d #[]
      let ordSql := renderOrderBy "" orderBy?
      let limSql := renderLimitOffset d limit? offset?
      ("SELECT " ++ SqlIdent.joinQuoted cols ++ " FROM " ++ tbl.quoteIdent ++
       " WHERE " ++ wSql ++ ordSql ++ limSql, params)
  | .count tbl whereExpr =>
      let (wSql, params) := whereExpr.compile d #[]
      ("SELECT COUNT(*) FROM " ++ tbl.quoteIdent ++ " WHERE " ++ wSql, params)
  | .aggregate op tbl col whereExpr =>
      let (wSql, params) := whereExpr.compile d #[]
      ("SELECT " ++ op.render ++ "(" ++ col.quoteIdent ++ ") FROM " ++ tbl.quoteIdent ++ " WHERE " ++ wSql, params)
  | .joinSelect lt rt lCols rCols lJoin rJoin lWhere rWhere orderBy? limit? offset? =>
      let (lwSql, p1) := lWhere.compileQual d "\"_l\"." #[]
      let (rwSql, p2) := rWhere.compileQual d "\"_r\"." p1
      let selCols := SqlIdent.joinQuotedPrefixed "\"_l\"." lCols ++ ", " ++
                     SqlIdent.joinQuotedPrefixed "\"_r\"." rCols
      let ordSql := renderOrderBy "\"_l\"." orderBy?
      let limSql := renderLimitOffset d limit? offset?
      ("SELECT " ++ selCols ++ " FROM " ++ lt.quoteIdent ++ " AS \"_l\" INNER JOIN " ++
       rt.quoteIdent ++ " AS \"_r\" ON \"_l\"." ++ lJoin.quoteIdent ++ " = \"_r\"." ++ rJoin.quoteIdent ++
       " WHERE (" ++ lwSql ++ " AND " ++ rwSql ++ ")" ++ ordSql ++ limSql, p2)
  | .insert tbl cols ret =>
      let colNames := SqlIdent.joinQuoted (cols.map Prod.fst)
      let (valsSql, params) := compileInParams d (cols.map Prod.snd) #[]
      ("INSERT INTO " ++ tbl.quoteIdent ++ " (" ++ colNames ++ ") VALUES (" ++ valsSql ++ ")" ++
       renderReturning ret, params)
  | .update tbl sets whereExpr ret =>
      let (setSql, p1) := compileSets d sets #[]
      let (wSql, p2) := whereExpr.compile d p1
      ("UPDATE " ++ tbl.quoteIdent ++ " SET " ++ setSql ++ " WHERE " ++ wSql ++
       renderReturning ret, p2)
  | .delete tbl whereExpr ret =>
      let (wSql, params) := whereExpr.compile d #[]
      ("DELETE FROM " ++ tbl.quoteIdent ++ " WHERE " ++ wSql ++
       renderReturning ret, params)

private theorem SqlQuery.compile_eraseVals (d : SqlDialect) (q : SqlQuery) :
    (q.compile d).1 = (q.eraseVals.compile d).1 := by
  cases q with
  | select _ _ w _ _ _ | count _ w | aggregate _ _ _ w | delete _ w _ =>
      have ⟨h, _⟩ := w.compileQual_eraseVals d "" #[] #[] rfl
      simp [SqlQuery.eraseVals, SqlQuery.compile, SqlExpr.compile, h]
  | joinSelect _ _ _ _ _ _ lw rw _ _ _ =>
      have ⟨hL, hszL⟩ := lw.compileQual_eraseVals d "\"_l\"." #[] #[] rfl
      have ⟨hR, _⟩ := rw.compileQual_eraseVals d "\"_r\"." _ _ hszL
      simp [SqlQuery.eraseVals, SqlQuery.compile, hL, hR]
  | insert _ cols _ =>
      have hfst : (cols.map fun (c, _) => (c, SqlVal.null)).map Prod.fst = cols.map Prod.fst := by
        simp [List.map_map, Function.comp_def]
      have hsnd : (cols.map fun (c, _) => (c, SqlVal.null)).map Prod.snd = List.replicate (cols.map Prod.snd).length .null := by
        induction cols with
        | nil => rfl
        | cons _ _ ih => simp [List.replicate, ih]
      have ⟨h, _⟩ := compileInParams_eraseVals d (cols.map Prod.snd) #[] #[] rfl
      simp [SqlQuery.eraseVals, SqlQuery.compile, hfst, hsnd, h]
  | update _ sets w _ =>
      have ⟨hS, hszS⟩ := compileSets_eraseVals d sets #[] #[] rfl
      have ⟨hW, _⟩ := w.compileQual_eraseVals d "" _ _ hszS
      simp [SqlQuery.eraseVals, SqlQuery.compile, SqlExpr.compile, hS, hW]

/-- **SQL Injection Closure (Non-Interference Theorem):**
    For any two typed `SqlQuery` values with the same AST skeleton (`sameShape`) and
    *arbitrary* runtime parameter values (including `"' OR 1=1; DROP TABLE users; --"`),
    the compiled SQL query string is **bit-for-bit identical**. User input can never alter
    SQL syntax or structure. -/
theorem SqlQuery.compile_sameShape (d : SqlDialect) {q₁ q₂ : SqlQuery}
    (hsh : q₁.sameShape q₂) :
    (q₁.compile d).1 = (q₂.compile d).1 := by
  rw [q₁.compile_eraseVals d, hsh, ← q₂.compile_eraseVals d]

/-- **Stacked-Query Closure:** No compiled `SqlQuery` can ever contain a `;` statement separator. -/
theorem SqlQuery.compile_no_semicolon (d : SqlDialect) (q : SqlQuery) :
    ∀ c ∈ (q.compile d).1.toList, c ≠ ';' := by
  cases q <;> ((intro c hc); (simp only [SqlQuery.compile, String.toList_append, List.mem_append] at hc); (revert hc); (try simp only [or_imp]); repeat any_goals constructor) <;>
    (intro hc; first
      | with_reducible exact SqlIdent.quoteIdent_no_semicolon _ c hc
      | with_reducible exact SqlIdent.joinQuotedPrefixed_no_semicolon _ (lit_no_semi _ rfl) _ c hc
      | with_reducible exact SqlAggOp.render_no_semicolon _ c hc
      | with_reducible exact SqlExpr.compile_no_semicolon _ _ _ c hc
      | with_reducible exact SqlExpr.compileQual_no_semicolon _ _ (lit_no_semi _ rfl) _ _ c hc
      | with_reducible exact compileInParams_no_semicolon _ _ _ c hc
      | with_reducible exact compileSets_no_semicolon _ _ _ c hc
      | with_reducible exact renderReturning_no_semicolon _ c hc
      | with_reducible exact renderLimitOffset_no_semicolon _ _ _ c hc
      | with_reducible exact renderOrderBy_no_semicolon _ (lit_no_semi _ rfl) _ c hc
      | exact lit_no_semi _ rfl c hc)

/-! ## Abstract Relational Policy & Invariant Soundness Model -/

/-- Pure relational semantics of `SELECT`: returns all rows matching `wherePred`. -/
def evalSelect {Row : Type} (tbl : List Row) (wherePred : Row → Bool) : List Row :=
  tbl.filter wherePred

theorem evalSelect_satisfies_policy {Row : Type}
    (RowInv ReadPolicy : Row → Prop) (tbl : List Row) (wherePred : Row → Bool)
    (htbl : ∀ r ∈ tbl, RowInv r)
    (hpol : ∀ r, RowInv r → wherePred r = true → ReadPolicy r) :
    ∀ r ∈ evalSelect tbl wherePred, RowInv r ∧ ReadPolicy r := by
  intro r hr
  rw [evalSelect, List.mem_filter] at hr
  exact ⟨htbl r hr.1, hpol r (htbl r hr.1) hr.2⟩

/-- Pure relational semantics of `INSERT`: appends a verified row. -/
def evalInsert {Row : Type} (tbl : List Row) (newRow : Row) : List Row :=
  newRow :: tbl

theorem evalInsert_preserves_inv {Row : Type}
    (RowInv InsertPolicy : Row → Prop) (tbl : List Row) (newRow : Row)
    (htbl : ∀ r ∈ tbl, RowInv r)
    (hinv : RowInv newRow)
    (_hpol : InsertPolicy newRow) :
    ∀ r ∈ evalInsert tbl newRow, RowInv r := by
  intro r hr
  rcases List.mem_cons.1 hr with rfl | hmem
  · exact hinv
  · exact htbl r hmem

/-- Pure relational semantics of `UPDATE`: transforms every row matching `wherePred` via `setFn`. -/
def evalUpdate {Row : Type} (tbl : List Row) (wherePred : Row → Bool) (setFn : Row → Row) : List Row :=
  tbl.map fun r => if wherePred r then setFn r else r

theorem evalUpdate_preserves_inv_and_trans {Row : Type}
    (RowInv UpdatePolicy : Row → Prop) (TransInv : Row → Row → Prop)
    (tbl : List Row) (wherePred : Row → Bool) (setFn : Row → Row)
    (htbl : ∀ r ∈ tbl, RowInv r)
    (hpolOld : ∀ r, RowInv r → wherePred r = true → UpdatePolicy r)
    (hpolNew : ∀ r, RowInv r → wherePred r = true → UpdatePolicy (setFn r))
    (hinv : ∀ r, RowInv r → wherePred r = true → RowInv (setFn r))
    (htrans : ∀ r, RowInv r → wherePred r = true → TransInv r (setFn r)) :
    (∀ r ∈ evalUpdate tbl wherePred setFn, RowInv r) ∧
    (∀ r ∈ tbl, wherePred r = true →
      UpdatePolicy r ∧ UpdatePolicy (setFn r) ∧ TransInv r (setFn r)) := by
  constructor
  · intro r' hr'
    rw [evalUpdate, List.mem_map] at hr'
    rcases hr' with ⟨r, hmem, rfl⟩
    have hr := htbl r hmem
    cases hw : wherePred r
    · simpa [hw] using hr
    · simpa [hw] using hinv r hr hw
  · intro r hmem hw
    have hr := htbl r hmem
    exact ⟨hpolOld r hr hw, hpolNew r hr hw, htrans r hr hw⟩

/-- Pure relational semantics of `DELETE`: removes every row matching `wherePred`. -/
def evalDelete {Row : Type} (tbl : List Row) (wherePred : Row → Bool) : List Row :=
  tbl.filter fun r => !wherePred r

theorem evalDelete_preserves_inv_and_policy {Row : Type}
    (RowInv DeletePolicy : Row → Prop) (tbl : List Row) (wherePred : Row → Bool)
    (htbl : ∀ r ∈ tbl, RowInv r)
    (hpol : ∀ r, RowInv r → wherePred r = true → DeletePolicy r) :
    (∀ r ∈ evalDelete tbl wherePred, RowInv r) ∧
    (∀ r ∈ tbl, wherePred r = true → DeletePolicy r) := by
  constructor
  · intro r hr
    rw [evalDelete, List.mem_filter] at hr
    exact htbl r hr.1
  · intro r hmem hw
    exact hpol r (htbl r hmem) hw

/-! ## Schema Metadata & SQL DDL / Postgres RLS Generator -/

inductive SqlColType where
  | text | int | bool | bytes
deriving Inhabited, DecidableEq, Repr

def SqlColType.render (d : SqlDialect) : SqlColType → String
  | .text  => "TEXT"
  | .int   => match d with | .postgres => "BIGINT" | .sqlite => "INTEGER"
  | .bool  => match d with | .postgres => "BOOLEAN" | .sqlite => "INTEGER"
  | .bytes => match d with | .postgres => "BYTEA" | .sqlite => "BLOB"

structure ColumnSchema where
  name         : SqlIdent
  colType      : SqlColType
  nullable     : Bool := false
  isPrimaryKey : Bool := false
  isUnique     : Bool := false
  isImmutable  : Bool := false
  references?  : Option (SqlIdent × SqlIdent) := none
  checkSql?    : Option String := none
deriving Inhabited, Repr

structure TableSchema where
  name      : SqlIdent
  columns   : List ColumnSchema
  indexes   : List (List SqlIdent) := []
  rlsRead?  : Option String := none
  rlsWrite? : Option String := none
deriving Inhabited, Repr

def ColumnSchema.renderDef (d : SqlDialect) (c : ColumnSchema) : String :=
  let base := c.name.quoteIdent ++ " " ++ c.colType.render d
  let nn   := if c.nullable then "" else " NOT NULL"
  let pk   := if c.isPrimaryKey then " PRIMARY KEY" else ""
  let uniq := if c.isUnique && !c.isPrimaryKey then " UNIQUE" else ""
  let fk   := match c.references? with
    | some (rt, rc) => " REFERENCES " ++ rt.quoteIdent ++ "(" ++ rc.quoteIdent ++ ")"
    | none => ""
  let chk  := match c.checkSql? with
    | some sql => " CHECK (" ++ sql ++ ")"
    | none => ""
  base ++ nn ++ pk ++ uniq ++ fk ++ chk

def TableSchema.renderCreateTable (d : SqlDialect) (t : TableSchema) : String :=
  let cols := String.intercalate ", " (t.columns.map (·.renderDef d))
  "CREATE TABLE IF NOT EXISTS " ++ t.name.quoteIdent ++ " (" ++ cols ++ ")"

def TableSchema.renderIndexes (t : TableSchema) : List String :=
  t.indexes.zipIdx.map fun (cols, i) =>
    let idxName := "idx_" ++ t.name.raw ++ "_" ++ toString i
    "CREATE INDEX IF NOT EXISTS \"" ++ idxName ++ "\" ON " ++ t.name.quoteIdent ++
      " (" ++ SqlIdent.joinQuoted cols ++ ")"

def TableSchema.renderDdlStatements (d : SqlDialect) (t : TableSchema) : List String :=
  t.renderCreateTable d :: t.renderIndexes

def TableSchema.renderPostgresRls (t : TableSchema) : List String :=
  if t.rlsRead?.isNone && t.rlsWrite?.isNone then []
  else
    let enable := "ALTER TABLE " ++ t.name.quoteIdent ++ " ENABLE ROW LEVEL SECURITY"
    let readPol := match t.rlsRead? with
      | some expr =>
          ["CREATE POLICY \"qed_read_" ++ t.name.raw ++ "\" ON " ++ t.name.quoteIdent ++
           " FOR SELECT USING (" ++ expr ++ ")"]
      | none => []
    let writePol := match t.rlsWrite? with
      | some expr =>
          ["CREATE POLICY \"qed_write_" ++ t.name.raw ++ "\" ON " ++ t.name.quoteIdent ++
           " FOR ALL USING (" ++ expr ++ ") WITH CHECK (" ++ expr ++ ")"]
      | none => []
    enable :: (readPol ++ writePol)

def renderDatabaseDdl (d : SqlDialect) (tables : List TableSchema) : String :=
  String.intercalate ";\n" (tables.flatMap (·.renderDdlStatements d)) ++
    (if tables.isEmpty then "" else ";\n")

def renderDatabaseRlsDdl (tables : List TableSchema) : String :=
  let stmts := tables.flatMap (·.renderPostgresRls)
  if stmts.isEmpty then "" else String.intercalate ";\n" stmts ++ ";\n"

/-! ## Pure Verified Schema Diffing & Safe Additive Migrations (`MigrationStep`) -/

inductive MigrationStep where
  | createTable (table : TableSchema)
  | addColumn   (table : SqlIdent) (col : ColumnSchema) (defaultSql? : Option String := none)
  | createIndex (table : SqlIdent) (idxName : String) (cols : List SqlIdent)
deriving Inhabited, Repr

/-- Pure invariant-safety check for adding a column to an existing non-empty table:
    - Primary-key, UNIQUE, or foreign-key columns cannot be safely backfilled automatically.
    - Nullable columns are always safe (existing rows receive `NULL`).
    - Non-nullable columns are safe only when they have no `CHECK` constraint (or only the
      standard `Nat` lower bound `"col" >= 0`, satisfied by default `0`). -/
def ColumnSchema.isAdditiveSafe (c : ColumnSchema) : Bool :=
  if c.isPrimaryKey || c.isUnique || c.references?.isSome then false
  else if c.nullable then true
  else
    match c.checkSql? with
    | none => true
    | some chk => chk == ("\"" ++ c.name.raw ++ "\" >= 0")

/-- Default SQL literal used when adding a non-nullable, additive-safe column to an existing table. -/
def ColumnSchema.safeDefaultSql (d : SqlDialect) (c : ColumnSchema) : Option String :=
  if c.nullable then none
  else if !c.isAdditiveSafe then none
  else
    match c.colType with
    | .text  => some "''"
    | .int   => some "0"
    | .bool  => some (match d with | .postgres => "FALSE" | .sqlite => "0")
    | .bytes => some (match d with | .postgres => "'\\x'" | .sqlite => "X''")

def TableSchema.indexNames (t : TableSchema) : List String :=
  t.indexes.zipIdx.map fun (_, i) => "idx_" ++ t.name.raw ++ "_" ++ toString i

/-- Pure schema diff for a single table against the database's live column and index names. -/
def diffTableSchema (existingCols : List String) (existingIdxNames : List String)
    (desired : TableSchema) (tableExists : Bool) : List MigrationStep :=
  if !tableExists then
    let idxSteps := desired.indexes.zipIdx.map fun (cols, i) =>
      .createIndex desired.name ("idx_" ++ desired.name.raw ++ "_" ++ toString i) cols
    .createTable desired :: idxSteps
  else
    let colSteps := desired.columns.filterMap fun col =>
      if existingCols.contains col.name.raw then none
      else some (.addColumn desired.name col none)
    let idxSteps := desired.indexes.zipIdx.filterMap fun (cols, i) =>
      let idxName := "idx_" ++ desired.name.raw ++ "_" ++ toString i
      if existingIdxNames.contains idxName then none
      else some (.createIndex desired.name idxName cols)
    colSteps ++ idxSteps

/-- Pure schema diff comparing an `oldTables` snapshot against a `newTables` target schema. -/
def diffTableSchemas (oldTables newTables : List TableSchema) : List MigrationStep :=
  newTables.flatMap fun newT =>
    match oldTables.find? fun t => t.name.raw == newT.name.raw with
    | none      => diffTableSchema [] [] newT false
    | some oldT =>
        diffTableSchema (oldT.columns.map (·.name.raw)) oldT.indexNames newT true

/-- Renders a single `MigrationStep` into idempotent dialect-specific SQL DDL. -/
def MigrationStep.render (d : SqlDialect) : MigrationStep → String
  | .createTable t => t.renderCreateTable d
  | .addColumn tbl col explicitDef? =>
      let addKw := match d with
        | .postgres => " ADD COLUMN IF NOT EXISTS "
        | .sqlite   => " ADD COLUMN "
      let effDef? := explicitDef?.orElse fun _ => col.safeDefaultSql d
      let nn := if col.nullable then "" else " NOT NULL"
      let defClause := match effDef? with
        | some lit => " DEFAULT " ++ lit
        | none     => ""
      let chk := match col.checkSql? with
        | some sql => " CHECK (" ++ sql ++ ")"
        | none     => ""
      "ALTER TABLE " ++ tbl.quoteIdent ++ addKw ++ col.name.quoteIdent ++ " " ++
        col.colType.render d ++ nn ++ defClause ++ chk
  | .createIndex tbl idxName cols =>
      "CREATE INDEX IF NOT EXISTS \"" ++ idxName ++ "\" ON " ++ tbl.quoteIdent ++
        " (" ++ SqlIdent.joinQuoted cols ++ ")"

def renderMigrationDdl (d : SqlDialect) (steps : List MigrationStep) : String :=
  if steps.isEmpty then ""
  else String.intercalate ";\n" (steps.map (·.render d)) ++ ";\n"

/-- Pure invariant-safety gate for a migration plan: rejects any `addColumn` step whose new column
    is neither additive-safe nor supplied with an explicit default for a nullable/unconstrained column. -/
def verifyMigrationSafe : List MigrationStep → Except String Unit
  | [] => .ok ()
  | .addColumn tbl col def? :: rest =>
      if col.isAdditiveSafe || (def?.isSome && !col.isPrimaryKey && !col.isUnique && col.references?.isNone && col.checkSql?.isNone) then
        verifyMigrationSafe rest
      else
        .error s!"unsafe additive migration on `{tbl.raw}.{col.name.raw}`: new non-nullable or constrained column could violate existing row invariants"
  | _ :: rest => verifyMigrationSafe rest

theorem verifyMigrationSafe_nullable_addColumn (tbl : SqlIdent) (col : ColumnSchema)
    (hNull : col.nullable = true) (hNoPk : col.isPrimaryKey = false)
    (hNoUniq : col.isUnique = false) (hNoFk : col.references? = none) :
    verifyMigrationSafe [.addColumn tbl col none] = .ok () := by
  simp [verifyMigrationSafe, ColumnSchema.isAdditiveSafe, hNull, hNoPk, hNoUniq, hNoFk]

private theorem filterMap_all_none {α β : Type} (f : α → Option β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = none) → xs.filterMap f = []
  | [], _ => rfl
  | x :: xs, hall => by
      simp only [List.filterMap_cons, hall x (by simp)]
      exact filterMap_all_none f xs (fun y hy => hall y (by simp [hy]))

/-- Diffing any table against its own existing column and index lists yields zero migration steps (idempotence). -/
theorem diffTableSchema_self_empty (t : TableSchema) :
    diffTableSchema (t.columns.map (·.name.raw)) t.indexNames t true = [] := by
  unfold diffTableSchema
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hCols : t.columns.filterMap (fun col =>
      if (t.columns.map (·.name.raw)).contains col.name.raw then none
      else some (MigrationStep.addColumn t.name col none)) = [] := by
    apply filterMap_all_none
    intro col hcol
    have hmem : (t.columns.map (·.name.raw)).contains col.name.raw = true :=
      List.contains_iff_mem.2 (List.mem_map.2 ⟨col, hcol, rfl⟩)
    rw [if_pos hmem]
  have hIdxs : t.indexes.zipIdx.filterMap (fun p =>
      let idxName := "idx_" ++ t.name.raw ++ "_" ++ toString p.2
      if t.indexNames.contains idxName then none
      else some (MigrationStep.createIndex t.name idxName p.1)) = [] := by
    apply filterMap_all_none
    intro p hp
    have hmem : t.indexNames.contains ("idx_" ++ t.name.raw ++ "_" ++ toString p.2) = true :=
      List.contains_iff_mem.2 (by unfold TableSchema.indexNames; exact List.mem_map.2 ⟨p, hp, rfl⟩)
    dsimp only
    rw [if_pos hmem]
  rw [hCols, hIdxs]
  rfl

/-! ## Driver-Agnostic Database Endpoint Config & Execution Result -/

inductive DbEndpoint where
  | urlEnv       (envVar : String)
  | postgresEnv  (urlEnvVar : String)
  | postgresUrl  (url : String)
  | sqlitePath   (path : String)
  | sqliteEnv    (envVar : String) (defaultPath? : Option String := none)
  | cloudflareD1 (accountEnv : String) (accountDefault? : Option String)
                 (dbEnv : String) (dbDefault? : Option String)
                 (tokenSecret : String)
  | turso        (urlEnv : String) (tokenSecret : String)
  | httpSql      (urlEnv : String) (tokenSecret? : Option String := none)
deriving Inhabited, DecidableEq, Repr

structure DbConfig where
  name         : String
  endpoint     : DbEndpoint
  devFallback? : Option DbEndpoint := none
  tables       : List TableSchema := []
deriving Inhabited, Repr

abbrev DbRow := Array SqlVal

structure DbResult where
  rows     : Array DbRow := #[]
  affected : Nat := 0
deriving Inhabited, DecidableEq

/-! ## Compact JSON Wire Encoding for `SqlVal` (Used Across SQLite FFI & HTTP SQL) -/

def SqlVal.toTaggedJson : SqlVal → Json
  | .null     => .obj [("t", .str "n")]
  | .int i    => .obj [("t", .str "i"), ("v", .str (toString i))]
  | .text s   => .obj [("t", .str "s"), ("v", .str s)]
  | .bool b   => .obj [("t", .str "b"), ("v", .bool b)]
  | .bytes bs => .obj [("t", .str "x"), ("v", .str (Proto.encodeHex bs))]

def SqlVal.fromTaggedJson : Json → Except String SqlVal
  | .obj fs =>
      match fs.lookup "t" with
      | some (.str "n") => .ok .null
      | some (.str "i") =>
          match fs.lookup "v" with
          | some (.str s) => match s.toInt? with | some i => .ok (.int i) | none => .error s!"bad int: {s}"
          | some (.num n) => .ok (.int n.mantissa)
          | _ => .error "missing int value"
      | some (.str "s") =>
          match fs.lookup "v" with
          | some (.str s) => .ok (.text s)
          | _ => .error "missing string value"
      | some (.str "b") =>
          match fs.lookup "v" with
          | some (.bool b) => .ok (.bool b)
          | some (.num n)  => .ok (.bool (n.mantissa != 0))
          | _ => .error "missing bool value"
      | some (.str "x") =>
          match fs.lookup "v" with
          | some (.str hx) => (Proto.decodeHex hx).map .bytes
          | _ => .error "missing bytes hex"
      | _ => .error "unknown SqlVal tag"
  | .null => .ok .null
  | .str s => .ok (.text s)
  | .num n => .ok (.int n.mantissa)
  | .bool b => .ok (.bool b)
  | _ => .error "unexpected JSON value for SqlVal"

def SqlVal.toPlainJson : SqlVal → Json
  | .null     => .null
  | .int i    => .num ⟨i, 0⟩
  | .text s   => .str s
  | .bool b   => .bool b
  | .bytes bs => .str (Proto.encodeHex bs)

def encodeTaggedParamsJson (params : Array SqlVal) : String :=
  Json.render (.arr (params.toList.map SqlVal.toTaggedJson))

def encodeTaggedResultJson (res : DbResult) : String :=
  Json.render (.obj [
    ("rows", .arr (res.rows.toList.map fun r => .arr (r.toList.map SqlVal.toTaggedJson))),
    ("affected", .num ⟨Int.ofNat res.affected, 0⟩)
  ])

def decodeTaggedResultJson (raw : String) : Except String DbResult := do
  let j ← Json.parse raw 128
  match j with
  | .obj fs =>
      let affected : Nat := match fs.lookup "affected" with
        | some (.num n) => if 0 ≤ n.mantissa then n.mantissa.toNat else 0
        | _ => 0
      let rowsList ← match fs.lookup "rows" with
        | some (.arr rs) =>
            rs.mapM fun rj =>
              match rj with
              | .arr vals => (vals.mapM SqlVal.fromTaggedJson).map List.toArray
              | _ => .error "expected row array"
        | none => .ok []
        | _ => .error "expected rows array"
      return { rows := rowsList.toArray, affected }
  | _ => .error "expected JSON object from database result"

end Qed.Server.Db
