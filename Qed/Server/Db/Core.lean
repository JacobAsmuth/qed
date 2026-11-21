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

def SqlIdent.quoteIdent (id : SqlIdent) : String :=
  "\"" ++ id.raw ++ "\""

theorem SqlIdent.quoteIdent_no_semicolon (id : SqlIdent) :
    ∀ c ∈ id.quoteIdent.toList, c ≠ ';' := by
  intro c hc
  unfold SqlIdent.quoteIdent at hc
  simp only [String.toList_append, List.mem_append] at hc
  rcases hc with (h1 | h2) | h3
  · have : c = '"' := by simpa using h1
    subst this; decide
  · exact (isSafeSqlIdent_no_inject id c h2).2.2.1
  · have : c = '"' := by simpa using h3
    subst this; decide

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
  cases op <;> intro c hc <;> simp [SqlBinOp.render] at hc <;>
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide

inductive SqlExpr where
  | litTrue
  | litFalse
  | col       (name : SqlIdent)
  | param     (val : SqlVal)
  | binOp     (op : SqlBinOp) (lhs rhs : SqlExpr)
  | not       (e : SqlExpr)
  | isNull    (e : SqlExpr)
  | isNotNull (e : SqlExpr)
  | strLen    (e : SqlExpr)
deriving Inhabited, DecidableEq

/-- Two `SqlExpr`s have the same AST skeleton when they are identical everywhere except
    possibly the runtime `SqlVal` payloads inside `.param` leaves. -/
def SqlExpr.sameShape : SqlExpr → SqlExpr → Prop
  | .litTrue, .litTrue => True
  | .litFalse, .litFalse => True
  | .col a, .col b => a = b
  | .param _, .param _ => True
  | .binOp op₁ l₁ r₁, .binOp op₂ l₂ r₂ => op₁ = op₂ ∧ l₁.sameShape l₂ ∧ r₁.sameShape r₂
  | .not e₁, .not e₂ => e₁.sameShape e₂
  | .isNull e₁, .isNull e₂ => e₁.sameShape e₂
  | .isNotNull e₁, .isNotNull e₂ => e₁.sameShape e₂
  | .strLen e₁, .strLen e₂ => e₁.sameShape e₂
  | _, _ => False

def placeholder (d : SqlDialect) (idx : Nat) : String :=
  match d with
  | .postgres => "$" ++ toString idx
  | .sqlite   => "?" ++ toString idx

private theorem nat_toString_no_semicolon (n : Nat) :
    ∀ c ∈ (toString n).toList, c ≠ ';' := by
  intro c hc heq
  subst heq
  have h1 : ∀ cs : List Char, (∀ x ∈ cs, '0' ≤ x ∧ x ≤ '9') → ';' ∉ cs := by
    intro cs hall hmem
    have hlt := hall ';' hmem
    exact absurd hlt (by decide)
  have hdig : ∀ x ∈ (Nat.toDigits 10 n), '0' ≤ x ∧ x ≤ '9' := by
    intro x hx
    have hmem : ∀ m (b : Nat) (acc : List Char),
        (∀ y ∈ acc, '0' ≤ y ∧ y ≤ '9') →
        ∀ y ∈ Nat.toDigitsCore 10 m b acc, '0' ≤ y ∧ y ≤ '9' := by
      intro m
      induction m with
      | zero => intro b acc hacc y hy; exact hacc y hy
      | succ m ih =>
          intro b acc hacc y hy
          unfold Nat.toDigitsCore at hy
          dsimp only at hy
          have hd : '0' ≤ Nat.digitChar (b % 10) ∧ Nat.digitChar (b % 10) ≤ '9' := by
            have hlt : b % 10 < 10 := Nat.mod_lt b (by decide)
            have : b % 10 = 0 ∨ b % 10 = 1 ∨ b % 10 = 2 ∨ b % 10 = 3 ∨ b % 10 = 4 ∨
                   b % 10 = 5 ∨ b % 10 = 6 ∨ b % 10 = 7 ∨ b % 10 = 8 ∨ b % 10 = 9 := by omega
            rcases this with h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide
          split at hy
          · rcases List.mem_cons.1 hy with rfl | hrest
            · exact hd
            · exact hacc y hrest
          · exact ih (b / 10) (Nat.digitChar (b % 10) :: acc)
              (fun z hz => (List.mem_cons.1 hz).elim (fun h => h ▸ hd) (hacc z)) y hy
    exact hmem (n + 1) n [] (fun _ h => False.elim (List.not_mem_nil h)) x hx
  have hrepr : (toString n).toList = Nat.toDigits 10 n := by
    change (Nat.repr n).toList = Nat.toDigits 10 n
    unfold Nat.repr
    exact String.toList_ofList
  rw [hrepr] at hc
  exact h1 _ hdig hc

theorem placeholder_no_semicolon (d : SqlDialect) (idx : Nat) :
    ∀ c ∈ (placeholder d idx).toList, c ≠ ';' := by
  cases d <;> intro c hc <;>
    simp only [placeholder, String.toList_append, List.mem_append] at hc <;>
    rcases hc with h1 | h2
  · have : c = '$' := by simpa using h1
    subst this; decide
  · exact nat_toString_no_semicolon idx c h2
  · have : c = '?' := by simpa using h1
    subst this; decide
  · exact nat_toString_no_semicolon idx c h2

def SqlExpr.compile (d : SqlDialect) (e : SqlExpr) (params : Array SqlVal) :
    String × Array SqlVal :=
  match e with
  | .litTrue  => (match d with | .postgres => "TRUE" | .sqlite => "1", params)
  | .litFalse => (match d with | .postgres => "FALSE" | .sqlite => "0", params)
  | .col id   => (id.quoteIdent, params)
  | .param v  =>
      let idx := params.size + 1
      (placeholder d idx, params.push v)
  | .binOp op l r =>
      let (sl, p1) := l.compile d params
      let (sr, p2) := r.compile d p1
      ("(" ++ sl ++ op.render ++ sr ++ ")", p2)
  | .not inner =>
      let (s, p1) := inner.compile d params
      ("(NOT " ++ s ++ ")", p1)
  | .isNull inner =>
      let (s, p1) := inner.compile d params
      ("(" ++ s ++ " IS NULL)", p1)
  | .isNotNull inner =>
      let (s, p1) := inner.compile d params
      ("(" ++ s ++ " IS NOT NULL)", p1)
  | .strLen inner =>
      let (s, p1) := inner.compile d params
      ("LENGTH(" ++ s ++ ")", p1)

/-- Non-interference for `SqlExpr.compile`: changing runtime parameter values leaves the
    compiled SQL string AND parameter count bit-for-bit identical. -/
theorem SqlExpr.compile_sameShape (d : SqlDialect) {e₁ e₂ : SqlExpr}
    (hsh : e₁.sameShape e₂) :
    ∀ (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
      (e₁.compile d p₁).1 = (e₂.compile d p₂).1 ∧
      (e₁.compile d p₁).2.size = (e₂.compile d p₂).2.size := by
  induction e₁ generalizing e₂ with
  | litTrue =>
      cases e₂ <;> simp_all [SqlExpr.sameShape, SqlExpr.compile]
  | litFalse =>
      cases e₂ <;> simp_all [SqlExpr.sameShape, SqlExpr.compile]
  | col a =>
      cases e₂ <;> simp_all [SqlExpr.sameShape, SqlExpr.compile]
  | param v₁ =>
      cases e₂ <;> simp_all [SqlExpr.sameShape, SqlExpr.compile]
  | binOp op₁ l₁ r₁ ihl ihr =>
      cases e₂ with
      | binOp op₂ l₂ r₂ =>
          rcases hsh with ⟨rfl, hl, hr⟩
          intro p₁ p₂ hsz
          have ⟨hsqlL, hszL⟩ := ihl hl p₁ p₂ hsz
          have ⟨hsqlR, hszR⟩ := ihr hr (l₁.compile d p₁).2 (l₂.compile d p₂).2 hszL
          simp [SqlExpr.compile, hsqlL, hsqlR, hszR]
      | _ => simp [SqlExpr.sameShape] at hsh
  | not e₁ ih =>
      cases e₂ with
      | not e₂ =>
          intro p₁ p₂ hsz
          have ⟨hsql, hsz'⟩ := ih hsh p₁ p₂ hsz
          simp [SqlExpr.compile, hsql, hsz']
      | _ => simp [SqlExpr.sameShape] at hsh
  | isNull e₁ ih =>
      cases e₂ with
      | isNull e₂ =>
          intro p₁ p₂ hsz
          have ⟨hsql, hsz'⟩ := ih hsh p₁ p₂ hsz
          simp [SqlExpr.compile, hsql, hsz']
      | _ => simp [SqlExpr.sameShape] at hsh
  | isNotNull e₁ ih =>
      cases e₂ with
      | isNotNull e₂ =>
          intro p₁ p₂ hsz
          have ⟨hsql, hsz'⟩ := ih hsh p₁ p₂ hsz
          simp [SqlExpr.compile, hsql, hsz']
      | _ => simp [SqlExpr.sameShape] at hsh
  | strLen e₁ ih =>
      cases e₂ with
      | strLen e₂ =>
          intro p₁ p₂ hsz
          have ⟨hsql, hsz'⟩ := ih hsh p₁ p₂ hsz
          simp [SqlExpr.compile, hsql, hsz']
      | _ => simp [SqlExpr.sameShape] at hsh

private theorem str_append_no_semi {a b : String}
    (ha : ∀ c ∈ a.toList, c ≠ ';') (hb : ∀ c ∈ b.toList, c ≠ ';') :
    ∀ c ∈ (a ++ b).toList, c ≠ ';' := by
  intro c hc
  rw [String.toList_append, List.mem_append] at hc
  exact hc.elim (ha c) (hb c)

private theorem lit_no_semi (s : String) (h : s.toList.all (· != ';') = true) :
    ∀ c ∈ s.toList, c ≠ ';' := by
  intro c hc
  rw [List.all_eq_true] at h
  have := h c hc
  simpa using this

theorem SqlExpr.compile_no_semicolon (d : SqlDialect) (e : SqlExpr) :
    ∀ (params : Array SqlVal), ∀ c ∈ (e.compile d params).1.toList, c ≠ ';' := by
  induction e with
  | litTrue =>
      intro _; cases d
      · exact lit_no_semi "TRUE" rfl
      · exact lit_no_semi "1" rfl
  | litFalse =>
      intro _; cases d
      · exact lit_no_semi "FALSE" rfl
      · exact lit_no_semi "0" rfl
  | col id =>
      intro _; exact id.quoteIdent_no_semicolon
  | param _ =>
      intro params; exact placeholder_no_semicolon d (params.size + 1)
  | binOp op l r ihl ihr =>
      intro params
      simp only [SqlExpr.compile]
      apply str_append_no_semi
      · apply str_append_no_semi
        · apply str_append_no_semi
          · apply str_append_no_semi
            · exact lit_no_semi "(" rfl
            · exact ihl params
          · exact op.render_no_semicolon
        · exact ihr (l.compile d params).2
      · exact lit_no_semi ")" rfl
  | not inner ih =>
      intro params
      simp only [SqlExpr.compile]
      exact str_append_no_semi (str_append_no_semi (lit_no_semi "(NOT " rfl) (ih params)) (lit_no_semi ")" rfl)
  | isNull inner ih =>
      intro params
      simp only [SqlExpr.compile]
      exact str_append_no_semi (str_append_no_semi (lit_no_semi "(" rfl) (ih params)) (lit_no_semi " IS NULL)" rfl)
  | isNotNull inner ih =>
      intro params
      simp only [SqlExpr.compile]
      exact str_append_no_semi (str_append_no_semi (lit_no_semi "(" rfl) (ih params)) (lit_no_semi " IS NOT NULL)" rfl)
  | strLen inner ih =>
      intro params
      simp only [SqlExpr.compile]
      exact str_append_no_semi (str_append_no_semi (lit_no_semi "LENGTH(" rfl) (ih params)) (lit_no_semi ")" rfl)

inductive SqlOrderDir where
  | asc | desc
deriving Inhabited, DecidableEq, Repr

inductive SqlQuery where
  | select (table : SqlIdent) (cols : List SqlIdent) (whereExpr : SqlExpr)
           (orderBy : Option (SqlIdent × SqlOrderDir) := none)
           (limit : Option Nat := none)
  | count  (table : SqlIdent) (whereExpr : SqlExpr)
  | insert (table : SqlIdent) (cols : List (SqlIdent × SqlVal)) (returning : List SqlIdent)
  | update (table : SqlIdent) (sets : List (SqlIdent × SqlExpr)) (whereExpr : SqlExpr)
           (returning : List SqlIdent)
  | delete (table : SqlIdent) (whereExpr : SqlExpr) (returning : List SqlIdent)
deriving Inhabited, DecidableEq

def SqlIdent.joinQuoted : List SqlIdent → String
  | []      => "*"
  | [c]     => c.quoteIdent
  | c :: cs => c.quoteIdent ++ ", " ++ joinQuoted cs

theorem SqlIdent.joinQuoted_no_semicolon : ∀ (cs : List SqlIdent),
    ∀ c ∈ (SqlIdent.joinQuoted cs).toList, c ≠ ';'
  | [] => lit_no_semi "*" rfl
  | [x] => x.quoteIdent_no_semicolon
  | x :: y :: rest =>
      str_append_no_semi
        (str_append_no_semi x.quoteIdent_no_semicolon (lit_no_semi ", " rfl))
        (SqlIdent.joinQuoted_no_semicolon (y :: rest))

private def compileInsertVals (d : SqlDialect) :
    List (SqlIdent × SqlVal) → Array SqlVal → String × Array SqlVal
  | [], params => ("", params)
  | [(_, v)], params =>
      (placeholder d (params.size + 1), params.push v)
  | (_, v) :: rest, params =>
      let ph := placeholder d (params.size + 1)
      let (tail, p2) := compileInsertVals d rest (params.push v)
      (ph ++ ", " ++ tail, p2)

private theorem compileInsertVals_sameShape (d : SqlDialect) :
    ∀ (l₁ l₂ : List (SqlIdent × SqlVal)),
      l₁.map Prod.fst = l₂.map Prod.fst →
      ∀ (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
        (compileInsertVals d l₁ p₁).1 = (compileInsertVals d l₂ p₂).1 ∧
        (compileInsertVals d l₁ p₁).2.size = (compileInsertVals d l₂ p₂).2.size
  | [], [], _, p₁, p₂, hsz => ⟨rfl, hsz⟩
  | [(_, _)], [(_, _)], _, p₁, p₂, hsz => by simp [compileInsertVals, hsz]
  | (_, v₁) :: x₁ :: r₁, (_, v₂) :: x₂ :: r₂, hmap, p₁, p₂, hsz => by
      have htail : (x₁ :: r₁).map Prod.fst = (x₂ :: r₂).map Prod.fst := by
        simpa [List.map_cons] using congrArg List.tail hmap
      have hsub := compileInsertVals_sameShape d (x₁ :: r₁) (x₂ :: r₂) htail (p₁.push v₁) (p₂.push v₂) (by simp [hsz])
      simp [compileInsertVals, hsz, hsub.1, hsub.2]
  | [], _ :: _, hmap, _, _, _ => by simp at hmap
  | _ :: _, [], hmap, _, _, _ => by simp at hmap
  | [_], _ :: _ :: _, hmap, _, _, _ => by simp at hmap
  | _ :: _ :: _, [_], hmap, _, _, _ => by simp at hmap

private theorem compileInsertVals_no_semicolon (d : SqlDialect) :
    ∀ (l : List (SqlIdent × SqlVal)) (params : Array SqlVal),
      ∀ c ∈ (compileInsertVals d l params).1.toList, c ≠ ';'
  | [], _ => fun _ h => False.elim (List.not_mem_nil h)
  | [(_, _)], params => placeholder_no_semicolon d (params.size + 1)
  | (_, v) :: x :: rest, params =>
      str_append_no_semi
        (str_append_no_semi (placeholder_no_semicolon d (params.size + 1)) (lit_no_semi ", " rfl))
        (compileInsertVals_no_semicolon d (x :: rest) (params.push v))

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

def setsSameShape : List (SqlIdent × SqlExpr) → List (SqlIdent × SqlExpr) → Prop
  | [], [] => True
  | (c₁, e₁) :: r₁, (c₂, e₂) :: r₂ => c₁ = c₂ ∧ e₁.sameShape e₂ ∧ setsSameShape r₁ r₂
  | _, _ => False

private theorem compileSets_sameShape (d : SqlDialect) :
    ∀ (l₁ l₂ : List (SqlIdent × SqlExpr)),
      setsSameShape l₁ l₂ →
      ∀ (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
        (compileSets d l₁ p₁).1 = (compileSets d l₂ p₂).1 ∧
        (compileSets d l₁ p₁).2.size = (compileSets d l₂ p₂).2.size
  | [], [], _, p₁, p₂, hsz => ⟨rfl, hsz⟩
  | [(c₁, e₁)], [(c₂, e₂)], h, p₁, p₂, hsz => by
      rcases h with ⟨rfl, he, _⟩
      have ⟨hs, hsz'⟩ := SqlExpr.compile_sameShape d he p₁ p₂ hsz
      simp [compileSets, hs, hsz']
  | (c₁, e₁) :: x₁ :: r₁, (c₂, e₂) :: x₂ :: r₂, h, p₁, p₂, hsz => by
      rcases h with ⟨rfl, he, hr⟩
      have ⟨hs, hsz1⟩ := SqlExpr.compile_sameShape d he p₁ p₂ hsz
      have ⟨ht, hsz2⟩ := compileSets_sameShape d (x₁ :: r₁) (x₂ :: r₂) hr (e₁.compile d p₁).2 (e₂.compile d p₂).2 hsz1
      simp [compileSets, hs, ht, hsz2]
  | [], _ :: _, h, _, _, _ => False.elim h
  | _ :: _, [], h, _, _, _ => False.elim h
  | [_], _ :: _ :: _, h, _, _, _ => False.elim h.2.2
  | _ :: _ :: _, [_], h, _, _, _ => False.elim h.2.2

private theorem compileSets_no_semicolon (d : SqlDialect) :
    ∀ (l : List (SqlIdent × SqlExpr)) (params : Array SqlVal),
      ∀ c ∈ (compileSets d l params).1.toList, c ≠ ';'
  | [], _ => fun _ h => False.elim (List.not_mem_nil h)
  | [(col, e)], params =>
      str_append_no_semi
        (str_append_no_semi col.quoteIdent_no_semicolon (lit_no_semi " = " rfl))
        (e.compile_no_semicolon d params)
  | (col, e) :: x :: rest, params =>
      str_append_no_semi
        (str_append_no_semi
          (str_append_no_semi
            (str_append_no_semi col.quoteIdent_no_semicolon (lit_no_semi " = " rfl))
            (e.compile_no_semicolon d params))
          (lit_no_semi ", " rfl))
        (compileSets_no_semicolon d (x :: rest) (e.compile d params).2)

def SqlQuery.sameShape : SqlQuery → SqlQuery → Prop
  | .select t₁ c₁ w₁ o₁ l₁, .select t₂ c₂ w₂ o₂ l₂ =>
      t₁ = t₂ ∧ c₁ = c₂ ∧ w₁.sameShape w₂ ∧ o₁ = o₂ ∧ l₁ = l₂
  | .count t₁ w₁, .count t₂ w₂ =>
      t₁ = t₂ ∧ w₁.sameShape w₂
  | .insert t₁ cols₁ ret₁, .insert t₂ cols₂ ret₂ =>
      t₁ = t₂ ∧ cols₁.map Prod.fst = cols₂.map Prod.fst ∧ ret₁ = ret₂
  | .update t₁ s₁ w₁ ret₁, .update t₂ s₂ w₂ ret₂ =>
      t₁ = t₂ ∧ setsSameShape s₁ s₂ ∧ w₁.sameShape w₂ ∧ ret₁ = ret₂
  | .delete t₁ w₁ ret₁, .delete t₂ w₂ ret₂ =>
      t₁ = t₂ ∧ w₁.sameShape w₂ ∧ ret₁ = ret₂
  | _, _ => False

def renderReturning (ret : List SqlIdent) : String :=
  if ret.isEmpty then "" else " RETURNING " ++ SqlIdent.joinQuoted ret

private theorem renderReturning_no_semicolon (ret : List SqlIdent) :
    ∀ c ∈ (renderReturning ret).toList, c ≠ ';' := by
  unfold renderReturning
  split
  · intro _ h; exact False.elim (List.not_mem_nil h)
  · exact str_append_no_semi (lit_no_semi " RETURNING " rfl) (SqlIdent.joinQuoted_no_semicolon ret)

def SqlQuery.compile (d : SqlDialect) : SqlQuery → String × Array SqlVal
  | .select tbl cols whereExpr orderBy? limit? =>
      let (wSql, params) := whereExpr.compile d #[]
      let ordSql := match orderBy? with
        | none => ""
        | some (col, .asc)  => " ORDER BY " ++ col.quoteIdent ++ " ASC"
        | some (col, .desc) => " ORDER BY " ++ col.quoteIdent ++ " DESC"
      let limSql := match limit? with
        | none   => ""
        | some n => " LIMIT " ++ toString n
      ("SELECT " ++ SqlIdent.joinQuoted cols ++ " FROM " ++ tbl.quoteIdent ++
       " WHERE " ++ wSql ++ ordSql ++ limSql, params)
  | .count tbl whereExpr =>
      let (wSql, params) := whereExpr.compile d #[]
      ("SELECT COUNT(*) FROM " ++ tbl.quoteIdent ++ " WHERE " ++ wSql, params)
  | .insert tbl cols ret =>
      let colNames := SqlIdent.joinQuoted (cols.map Prod.fst)
      let (valsSql, params) := compileInsertVals d cols #[]
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

/-- **SQL Injection Closure (Non-Interference Theorem):**
    For any two typed `SqlQuery` values with the same AST skeleton (`sameShape`) and
    *arbitrary* runtime parameter values (including `"' OR 1=1; DROP TABLE users; --"`),
    the compiled SQL query string is **bit-for-bit identical**. User input can never alter
    SQL syntax or structure. -/
theorem SqlQuery.compile_sameShape (d : SqlDialect) {q₁ q₂ : SqlQuery}
    (hsh : q₁.sameShape q₂) :
    (q₁.compile d).1 = (q₂.compile d).1 := by
  cases q₁ <;> cases q₂ <;> simp only [SqlQuery.sameShape] at hsh
  · rcases hsh with ⟨rfl, rfl, hw, rfl, rfl⟩
    have ⟨hsql, _⟩ := SqlExpr.compile_sameShape d hw #[] #[] rfl
    simp [SqlQuery.compile, hsql]
  · rcases hsh with ⟨rfl, hw⟩
    have ⟨hsql, _⟩ := SqlExpr.compile_sameShape d hw #[] #[] rfl
    simp [SqlQuery.compile, hsql]
  · rcases hsh with ⟨rfl, hcols, rfl⟩
    have ⟨hsql, _⟩ := compileInsertVals_sameShape d _ _ hcols #[] #[] rfl
    simp [SqlQuery.compile, hcols, hsql]
  · rcases hsh with ⟨rfl, hsets, hw, rfl⟩
    have ⟨hsSql, hsSz⟩ := compileSets_sameShape d _ _ hsets #[] #[] rfl
    have ⟨hwSql, _⟩ := SqlExpr.compile_sameShape d hw _ _ hsSz
    simp [SqlQuery.compile, hsSql, hwSql]
  · rcases hsh with ⟨rfl, hw, rfl⟩
    have ⟨hsql, _⟩ := SqlExpr.compile_sameShape d hw #[] #[] rfl
    simp [SqlQuery.compile, hsql]

/-- **Stacked-Query Closure:** No compiled `SqlQuery` can ever contain a `;` statement separator. -/
theorem SqlQuery.compile_no_semicolon (d : SqlDialect) (q : SqlQuery) :
    ∀ c ∈ (q.compile d).1.toList, c ≠ ';' := by
  cases q with
  | select tbl cols w ord lim =>
      simp only [SqlQuery.compile]
      have hOrd : ∀ c ∈ (match ord with
          | none => ""
          | some (col, .asc) => " ORDER BY " ++ col.quoteIdent ++ " ASC"
          | some (col, .desc) => " ORDER BY " ++ col.quoteIdent ++ " DESC").toList, c ≠ ';' := by
        cases ord with
        | none => exact fun _ h => False.elim (List.not_mem_nil h)
        | some p =>
            rcases p with ⟨col, dir⟩
            cases dir
            · exact str_append_no_semi (str_append_no_semi (lit_no_semi " ORDER BY " rfl) col.quoteIdent_no_semicolon) (lit_no_semi " ASC" rfl)
            · exact str_append_no_semi (str_append_no_semi (lit_no_semi " ORDER BY " rfl) col.quoteIdent_no_semicolon) (lit_no_semi " DESC" rfl)
      have hLim : ∀ c ∈ (match lim with | none => "" | some n => " LIMIT " ++ toString n).toList, c ≠ ';' := by
        cases lim with
        | none => exact fun _ h => False.elim (List.not_mem_nil h)
        | some n => exact str_append_no_semi (lit_no_semi " LIMIT " rfl) (nat_toString_no_semicolon n)
      exact str_append_no_semi
        (str_append_no_semi
          (str_append_no_semi
            (str_append_no_semi
              (str_append_no_semi
                (str_append_no_semi
                  (str_append_no_semi (lit_no_semi "SELECT " rfl) (SqlIdent.joinQuoted_no_semicolon cols))
                  (lit_no_semi " FROM " rfl))
                tbl.quoteIdent_no_semicolon)
              (lit_no_semi " WHERE " rfl))
            (w.compile_no_semicolon d #[]))
          hOrd)
        hLim
  | count tbl w =>
      simp only [SqlQuery.compile]
      exact str_append_no_semi
        (str_append_no_semi
          (str_append_no_semi (lit_no_semi "SELECT COUNT(*) FROM " rfl) tbl.quoteIdent_no_semicolon)
          (lit_no_semi " WHERE " rfl))
        (w.compile_no_semicolon d #[])
  | insert tbl cols ret =>
      simp only [SqlQuery.compile]
      exact str_append_no_semi
        (str_append_no_semi
          (str_append_no_semi
            (str_append_no_semi
              (str_append_no_semi
                (str_append_no_semi
                  (str_append_no_semi (lit_no_semi "INSERT INTO " rfl) tbl.quoteIdent_no_semicolon)
                  (lit_no_semi " (" rfl))
                (SqlIdent.joinQuoted_no_semicolon (cols.map Prod.fst)))
              (lit_no_semi ") VALUES (" rfl))
            (compileInsertVals_no_semicolon d cols #[]))
          (lit_no_semi ")" rfl))
        (renderReturning_no_semicolon ret)
  | update tbl sets w ret =>
      simp only [SqlQuery.compile]
      exact str_append_no_semi
        (str_append_no_semi
          (str_append_no_semi
            (str_append_no_semi
              (str_append_no_semi
                (str_append_no_semi (lit_no_semi "UPDATE " rfl) tbl.quoteIdent_no_semicolon)
                (lit_no_semi " SET " rfl))
              (compileSets_no_semicolon d sets #[]))
            (lit_no_semi " WHERE " rfl))
          (w.compile_no_semicolon d (compileSets d sets #[]).2))
        (renderReturning_no_semicolon ret)
  | delete tbl w ret =>
      simp only [SqlQuery.compile]
      exact str_append_no_semi
        (str_append_no_semi
          (str_append_no_semi
            (str_append_no_semi (lit_no_semi "DELETE FROM " rfl) tbl.quoteIdent_no_semicolon)
            (lit_no_semi " WHERE " rfl))
          (w.compile_no_semicolon d #[]))
        (renderReturning_no_semicolon ret)

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

/-! ## Driver-Agnostic Database Endpoint Config & Execution Result -/

inductive DbEndpoint where
  | urlEnv       (envVar : String)
  | postgresEnv  (urlEnvVar : String)
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
