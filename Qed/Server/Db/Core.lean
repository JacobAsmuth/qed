import Qed.Json.Lawful
import Qed.Proto
import Qed.Cloud.Env

namespace Qed.Server.Db

/-! ## Typed SQL Values & Wire Codecs (`SqlVal`, `ToSql`, `FromSql`) -/

inductive SqlVal where
  | null | int (v : Int) | text (v : String) | bool (v : Bool) | bytes (v : ByteArray)
deriving Inhabited, DecidableEq

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
  | .text s => (s.toInt?).elim (.error s!"invalid INT: {s}") .ok | v => fromSqlErr "INT" v⟩
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
instance : ToSql ByteArray := ⟨.bytes⟩
instance : FromSql ByteArray := ⟨fun
  | .bytes bs => .ok bs
  | .text s => Proto.decodeHex (if s.startsWith "\\x" then String.ofList (s.toList.drop 2) else s)
  | .null => .error "expected BLOB, got NULL" | _ => .error "expected BLOB"⟩
instance [ToSql α] : ToSql (Option α) := ⟨fun | none => .null | some a => ToSql.toSql a⟩
instance [FromSql α] : FromSql (Option α) := ⟨fun | .null => .ok none | v => (FromSql.fromSql (α := α) v).map some⟩

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
deriving DecidableEq, Repr
instance : Inhabited SqlIdent := ⟨⟨"id", by decide⟩⟩

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

private abbrev NoSemi (s : String) : Prop := ∀ c ∈ s.toList, c ≠ ';'
private theorem NoSemi.app {a b : String} (ha : NoSemi a) (hb : NoSemi b) : NoSemi (a ++ b) := fun c hc =>
  (List.mem_append.1 (String.toList_append ▸ hc)).elim (ha c) (hb c)
private theorem NoSemi.lit (s : String) (h : s.toList.all (· != ';') = true) : NoSemi s := fun c hc => by
  rw [List.all_eq_true] at h; simpa using h c hc

def SqlIdent.quoteIdent (id : SqlIdent) : String := "\"" ++ id.raw ++ "\""
theorem SqlIdent.quoteIdent_no_semicolon (id : SqlIdent) : ∀ c ∈ id.quoteIdent.toList, c ≠ ';' :=
  ((NoSemi.lit "\"" rfl).app fun c hc => (isSafeSqlIdent_no_inject id c hc).2.2.1).app (NoSemi.lit "\"" rfl)

/-! ## Typed Parameterized SQL AST (`SqlExpr`, `SqlQuery`, `SqlDialect`) -/

inductive SqlDialect  where | postgres | sqlite deriving Inhabited, DecidableEq, Repr
inductive SqlBinOp    where | eq | ne | lt | le | gt | ge | and | or | add | sub | mul deriving Inhabited, DecidableEq, Repr
inductive SqlOrderDir where | asc | desc deriving Inhabited, DecidableEq, Repr
inductive SqlAggOp    where | sum | min | max deriving Inhabited, DecidableEq, Repr

@[inline] private def SqlDialect.pick (d : SqlDialect) (pg sq : String) : String := match d with | .postgres => pg | .sqlite => sq
private theorem SqlDialect.pick_no_semi (d : SqlDialect) {pg sq : String} (h1 : NoSemi pg) (h2 : NoSemi sq) : NoSemi (d.pick pg sq) := by
  cases d <;> assumption

def SqlBinOp.render : SqlBinOp → String
  | .eq  => " = "  | .ne  => " <> " | .lt  => " < "  | .le  => " <= "
  | .gt  => " > "  | .ge  => " >= " | .and => " AND " | .or  => " OR "
  | .add => " + "  | .sub => " - "  | .mul => " * "
def SqlAggOp.render : SqlAggOp → String | .sum => "SUM" | .min => "MIN" | .max => "MAX"
theorem SqlBinOp.render_no_semicolon (op : SqlBinOp) : ∀ c ∈ op.render.toList, c ≠ ';' := by cases op <;> exact NoSemi.lit _ rfl
theorem SqlAggOp.render_no_semicolon (op : SqlAggOp) : ∀ c ∈ op.render.toList, c ≠ ';' := by cases op <;> exact NoSemi.lit _ rfl

inductive SqlExpr where
  | litTrue | litFalse | col (name : SqlIdent) | param (val : SqlVal)
  | binOp (op : SqlBinOp) (lhs rhs : SqlExpr)
  | not (e : SqlExpr) | isNull (e : SqlExpr) | isNotNull (e : SqlExpr) | strLen (e : SqlExpr)
  | like (lhs rhs : SqlExpr) | startsWith (lhs rhs : SqlExpr) | contains (lhs rhs : SqlExpr)
  | inList (lhs : SqlExpr) (vals : List SqlVal)
deriving Inhabited, DecidableEq

/-- Replaces every runtime `SqlVal` payload with `.null`, preserving the exact AST skeleton. -/
def SqlExpr.eraseVals : SqlExpr → SqlExpr
  | .litTrue => .litTrue | .litFalse => .litFalse | .col name => .col name | .param _ => .param .null
  | .binOp op l r => .binOp op l.eraseVals r.eraseVals | .not e => .not e.eraseVals
  | .isNull e => .isNull e.eraseVals | .isNotNull e => .isNotNull e.eraseVals | .strLen e => .strLen e.eraseVals
  | .like l r => .like l.eraseVals r.eraseVals | .startsWith l r => .startsWith l.eraseVals r.eraseVals
  | .contains l r => .contains l.eraseVals r.eraseVals | .inList l vs => .inList l.eraseVals (vs.map fun _ => .null)

abbrev SqlExpr.sameShape (e₁ e₂ : SqlExpr) : Prop := e₁.eraseVals = e₂.eraseVals
def placeholder (d : SqlDialect) (idx : Nat) : String := d.pick "$" "?" ++ toString idx

theorem nat_toString_digits (n : Nat) : ∀ c ∈ (toString n).toList, '0' ≤ c ∧ c ≤ '9' := by
  have hdig : ∀ k : Fin 10, '0' ≤ Nat.digitChar k.val ∧ Nat.digitChar k.val ≤ '9' := by decide
  have hmem : ∀ m (b : Nat) (acc : List Char), (∀ y ∈ acc, '0' ≤ y ∧ y ≤ '9') →
      ∀ y ∈ Nat.toDigitsCore 10 m b acc, '0' ≤ y ∧ y ≤ '9' := by
    intro m; induction m with
    | zero => exact fun _ _ hacc => hacc
    | succ m ih =>
        intro b acc hacc y hy; unfold Nat.toDigitsCore at hy; dsimp only at hy
        have hd := hdig ⟨b % 10, Nat.mod_lt b (by decide)⟩
        split at hy
        · exact (List.mem_cons.1 hy).elim (· ▸ hd) (hacc y)
        · exact ih (b / 10) _ (fun z hz => (List.mem_cons.1 hz).elim (· ▸ hd) (hacc z)) y hy
  intro c hc
  have hrepr : (toString n).toList = Nat.toDigits 10 n := by
    change (Nat.repr n).toList = Nat.toDigits 10 n; unfold Nat.repr; exact String.toList_ofList
  rw [hrepr] at hc; exact hmem (n + 1) n [] (fun _ h => nomatch h) c hc

private theorem nat_toString_no_semicolon (n : Nat) : NoSemi (toString n) :=
  fun c hc heq => absurd (heq ▸ nat_toString_digits n c hc) (by decide)
theorem placeholder_no_semicolon (d : SqlDialect) (idx : Nat) : ∀ c ∈ (placeholder d idx).toList, c ≠ ';' :=
  (d.pick_no_semi (NoSemi.lit _ rfl) (NoSemi.lit _ rfl)).app (nat_toString_no_semicolon idx)

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
  | x :: y :: rest, p => ((hf x p).app (NoSemi.lit ", " rfl)).app (compileSepList_no_semicolon f hf (y :: rest) (f x p).2)

private def compileInParams (d : SqlDialect) : List SqlVal → Array SqlVal → String × Array SqlVal :=
  compileSepList (α := SqlVal) fun v p => (placeholder d (p.size + 1), p.push v)
private theorem compileInParams_eraseVals (d : SqlDialect) :
    ∀ (vs : List SqlVal) (p₁ p₂ : Array SqlVal), p₁.size = p₂.size →
      SameCompile (compileInParams d vs p₁) (compileInParams d (vs.map fun _ => .null) p₂) :=
  compileSepList_eraseVals (α := SqlVal) _ (fun _ => .null) fun _ _ _ h => ⟨by simp [h], by simp [h]⟩
private theorem compileInParams_no_semicolon (d : SqlDialect) :
    ∀ (vs : List SqlVal) (p : Array SqlVal), NoSemi (compileInParams d vs p).1 :=
  compileSepList_no_semicolon (α := SqlVal) _ fun _ p => placeholder_no_semicolon d (p.size + 1)

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

def SqlExpr.compile (d : SqlDialect) (e : SqlExpr) (params : Array SqlVal) : String × Array SqlVal := e.compileQual d "" params

private theorem SqlExpr.compileQual_eraseVals (d : SqlDialect) (pfx : String) (e : SqlExpr) :
    ∀ (p₁ p₂ : Array SqlVal), p₁.size = p₂.size → SameCompile (e.compileQual d pfx p₁) (e.eraseVals.compileQual d pfx p₂) := by
  induction e with
  | litTrue | litFalse | col _ => intro _ _ hsz; exact ⟨rfl, hsz⟩
  | param _ => intro _ _ hsz; exact ⟨by simp [SqlExpr.eraseVals, SqlExpr.compileQual, hsz], by simp [SqlExpr.eraseVals, SqlExpr.compileQual, hsz]⟩
  | not _ ih | isNull _ ih | isNotNull _ ih | strLen _ ih => intro p₁ p₂ hsz; exact wrap1_eq (ih p₁ p₂ hsz)
  | binOp _ _ _ ihl ihr | like _ _ ihl ihr | contains _ _ ihl ihr => intro p₁ p₂ hsz; exact wrap2_eq rfl (ihl p₁ p₂ hsz) ihr
  | startsWith _ _ ihl ihr => intro p₁ p₂ hsz; have ⟨h1, h2⟩ := ihl p₁ p₂ hsz; exact wrap2_eq (by rw [h1]) (ihr _ _ h2) ihr
  | inList _ vs ihl =>
      intro p₁ p₂ hsz; cases vs with
      | nil => exact ⟨rfl, hsz⟩
      | cons v vs' => exact wrap2_eq rfl (ihl p₁ p₂ hsz) (compileInParams_eraseVals d (v :: vs'))

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

theorem SqlExpr.compileQual_no_semicolon (d : SqlDialect) (pfx : String) (hpfx : ∀ c ∈ pfx.toList, c ≠ ';') (e : SqlExpr) :
    ∀ (params : Array SqlVal), ∀ c ∈ (e.compileQual d pfx params).1.toList, c ≠ ';' := by
  induction e with
  | litTrue | litFalse => intro _; exact d.pick_no_semi (NoSemi.lit _ rfl) (NoSemi.lit _ rfl)
  | col id => intro _; exact NoSemi.app hpfx id.quoteIdent_no_semicolon
  | param _ => intro p; exact placeholder_no_semicolon d (p.size + 1)
  | not _ ih | isNull _ ih | isNotNull _ ih | strLen _ ih =>
      intro p; exact wrap1_no_semi (NoSemi.lit _ rfl) (ih p) (NoSemi.lit _ rfl)
  | binOp op _ _ ihl ihr => intro p; exact wrap2_no_semi (NoSemi.lit _ rfl) (ihl p) op.render_no_semicolon (ihr _) (NoSemi.lit _ rfl)
  | like _ _ ihl ihr => intro p; exact wrap2_no_semi (NoSemi.lit _ rfl) (ihl p) (NoSemi.lit _ rfl) (ihr _) (NoSemi.lit _ rfl)
  | startsWith _ _ ihl ihr =>
      intro p; exact wrap2_no_semi (((NoSemi.lit _ rfl).app (ihl p)).app (NoSemi.lit _ rfl)) (ihr _) (NoSemi.lit _ rfl) (ihr _) (NoSemi.lit _ rfl)
  | contains _ _ ihl ihr =>
      intro p; exact wrap2_no_semi ((NoSemi.lit _ rfl).app (d.pick_no_semi (NoSemi.lit _ rfl) (NoSemi.lit _ rfl)))
        (ihl p) (NoSemi.lit _ rfl) (ihr _) (NoSemi.lit _ rfl)
  | inList _ vs ihl =>
      intro p; cases vs with
      | nil => exact d.pick_no_semi (NoSemi.lit _ rfl) (NoSemi.lit _ rfl)
      | cons v vs' => exact wrap2_no_semi (NoSemi.lit _ rfl) (ihl p) (NoSemi.lit _ rfl) (compileInParams_no_semicolon d (v :: vs') _) (NoSemi.lit _ rfl)

theorem SqlExpr.compile_no_semicolon (d : SqlDialect) (e : SqlExpr) :
    ∀ (params : Array SqlVal), ∀ c ∈ (e.compile d params).1.toList, c ≠ ';' :=
  SqlExpr.compileQual_no_semicolon d "" (fun _ h => nomatch h) e

inductive SqlQuery where
  | select (table : SqlIdent) (cols : List SqlIdent) (whereExpr : SqlExpr)
           (orderBy : Option (SqlIdent × SqlOrderDir) := none) (limit offset : Option Nat := none)
  | count  (table : SqlIdent) (whereExpr : SqlExpr)
  | aggregate (op : SqlAggOp) (table col : SqlIdent) (whereExpr : SqlExpr)
  | joinSelect (leftTable rightTable : SqlIdent) (leftCols rightCols : List SqlIdent)
               (leftJoinCol rightJoinCol : SqlIdent) (leftWhere rightWhere : SqlExpr)
               (orderBy : Option (SqlIdent × SqlOrderDir) := none) (limit offset : Option Nat := none)
  | insert (table : SqlIdent) (cols : List (SqlIdent × SqlVal)) (returning : List SqlIdent)
  | update (table : SqlIdent) (sets : List (SqlIdent × SqlExpr)) (whereExpr : SqlExpr) (returning : List SqlIdent)
  | delete (table : SqlIdent) (whereExpr : SqlExpr) (returning : List SqlIdent)
deriving Inhabited, DecidableEq

def SqlIdent.joinQuotedPrefixed (pfx : String) : List SqlIdent → String
  | [] => pfx ++ "*" | [c] => pfx ++ c.quoteIdent | c :: cs => pfx ++ c.quoteIdent ++ ", " ++ joinQuotedPrefixed pfx cs
abbrev SqlIdent.joinQuoted : List SqlIdent → String := SqlIdent.joinQuotedPrefixed ""

theorem SqlIdent.joinQuotedPrefixed_no_semicolon (pfx : String) (hpfx : ∀ c ∈ pfx.toList, c ≠ ';') :
    ∀ (cs : List SqlIdent), ∀ c ∈ (SqlIdent.joinQuotedPrefixed pfx cs).toList, c ≠ ';'
  | [] => NoSemi.app hpfx (NoSemi.lit "*" rfl)
  | [x] => NoSemi.app hpfx x.quoteIdent_no_semicolon
  | x :: y :: rest => ((NoSemi.app hpfx x.quoteIdent_no_semicolon).app (NoSemi.lit ", " rfl)).app (SqlIdent.joinQuotedPrefixed_no_semicolon pfx hpfx (y :: rest))

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
    (NoSemi.app col.quoteIdent_no_semicolon (NoSemi.lit " = " rfl)).app (e.compile_no_semicolon d p)

def SqlQuery.eraseVals : SqlQuery → SqlQuery
  | .select t c w o l off => .select t c w.eraseVals o l off
  | .count t w => .count t w.eraseVals | .aggregate op t c w => .aggregate op t c w.eraseVals
  | .joinSelect lt rt lc rc lj rj lw rw o l off => .joinSelect lt rt lc rc lj rj lw.eraseVals rw.eraseVals o l off
  | .insert t cols ret => .insert t (cols.map fun (c, _) => (c, .null)) ret
  | .update t s w ret => .update t (s.map fun (c, e) => (c, e.eraseVals)) w.eraseVals ret
  | .delete t w ret => .delete t w.eraseVals ret
abbrev SqlQuery.sameShape (q₁ q₂ : SqlQuery) : Prop := q₁.eraseVals = q₂.eraseVals

def renderReturning (ret : List SqlIdent) : String :=
  if ret.isEmpty then "" else " RETURNING " ++ SqlIdent.joinQuoted ret
private theorem renderReturning_no_semicolon (ret : List SqlIdent) : NoSemi (renderReturning ret) := by
  unfold renderReturning; split
  · exact fun _ h => nomatch h
  · exact (NoSemi.lit " RETURNING " rfl).app (SqlIdent.joinQuotedPrefixed_no_semicolon "" (NoSemi.lit "" rfl) ret)

private def renderLimitOffset (d : SqlDialect) (limit? offset? : Option Nat) : String :=
  match limit?, offset? with
  | none, none => "" | some n, none => " LIMIT " ++ toString n
  | some n, some off => " LIMIT " ++ toString n ++ " OFFSET " ++ toString off
  | none, some off => d.pick " OFFSET " " LIMIT -1 OFFSET " ++ toString off
private theorem renderLimitOffset_no_semicolon (d : SqlDialect) (limit? offset? : Option Nat) :
    NoSemi (renderLimitOffset d limit? offset?) := by
  cases limit? <;> cases offset?
  · exact NoSemi.lit "" rfl
  · exact (d.pick_no_semi (NoSemi.lit _ rfl) (NoSemi.lit _ rfl)).app (nat_toString_no_semicolon _)
  · exact (NoSemi.lit _ rfl).app (nat_toString_no_semicolon _)
  · exact (((NoSemi.lit _ rfl).app (nat_toString_no_semicolon _)).app (NoSemi.lit _ rfl)).app (nat_toString_no_semicolon _)

private def renderOrderBy (pfx : String) : Option (SqlIdent × SqlOrderDir) → String
  | none => "" | some (col, dir) => " ORDER BY " ++ pfx ++ col.quoteIdent ++ (match dir with | .asc => " ASC" | .desc => " DESC")
private theorem renderOrderBy_no_semicolon (pfx : String) (hpfx : NoSemi pfx) (orderBy? : Option (SqlIdent × SqlOrderDir)) :
    NoSemi (renderOrderBy pfx orderBy?) := by
  rcases orderBy? with _ | ⟨col, dir⟩
  · exact NoSemi.lit "" rfl
  · exact (((NoSemi.lit _ rfl).app hpfx).app col.quoteIdent_no_semicolon).app (by cases dir <;> exact NoSemi.lit _ rfl)

def SqlQuery.compile (d : SqlDialect) : SqlQuery → String × Array SqlVal
  | .select tbl cols whereExpr orderBy? limit? offset? =>
      let (wSql, params) := whereExpr.compile d #[]
      ("SELECT " ++ SqlIdent.joinQuoted cols ++ " FROM " ++ tbl.quoteIdent ++
       " WHERE " ++ wSql ++ renderOrderBy "" orderBy? ++ renderLimitOffset d limit? offset?, params)
  | .count tbl whereExpr =>
      let (wSql, params) := whereExpr.compile d #[]
      ("SELECT COUNT(*) FROM " ++ tbl.quoteIdent ++ " WHERE " ++ wSql, params)
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
  | .insert tbl cols ret =>
      let (valsSql, params) := compileInParams d (cols.map Prod.snd) #[]
      ("INSERT INTO " ++ tbl.quoteIdent ++ " (" ++ SqlIdent.joinQuoted (cols.map Prod.fst) ++
       ") VALUES (" ++ valsSql ++ ")" ++ renderReturning ret, params)
  | .update tbl sets whereExpr ret =>
      let (setSql, p1) := compileSets d sets #[]
      let (wSql, p2) := whereExpr.compile d p1
      ("UPDATE " ++ tbl.quoteIdent ++ " SET " ++ setSql ++ " WHERE " ++ wSql ++ renderReturning ret, p2)
  | .delete tbl whereExpr ret =>
      let (wSql, params) := whereExpr.compile d #[]
      ("DELETE FROM " ++ tbl.quoteIdent ++ " WHERE " ++ wSql ++ renderReturning ret, params)

private theorem SqlQuery.compile_eraseVals (d : SqlDialect) (q : SqlQuery) : (q.compile d).1 = (q.eraseVals.compile d).1 := by
  cases q with
  | select _ _ w _ _ _ | count _ w | aggregate _ _ _ w | delete _ w _ =>
      have ⟨h, _⟩ := w.compileQual_eraseVals d "" #[] #[] rfl; simp [SqlQuery.eraseVals, SqlQuery.compile, SqlExpr.compile, h]
  | joinSelect _ _ _ _ _ _ lw rw _ _ _ =>
      have ⟨hL, hszL⟩ := lw.compileQual_eraseVals d "\"_l\"." #[] #[] rfl
      have ⟨hR, _⟩ := rw.compileQual_eraseVals d "\"_r\"." _ _ hszL; simp [SqlQuery.eraseVals, SqlQuery.compile, hL, hR]
  | insert _ cols _ =>
      have hfst : (cols.map fun (c, _) => (c, SqlVal.null)).map Prod.fst = cols.map Prod.fst := by simp [List.map_map, Function.comp_def]
      have hsnd : (cols.map fun (c, _) => (c, SqlVal.null)).map Prod.snd = (cols.map Prod.snd).map fun _ => .null := by simp [List.map_map, Function.comp_def]
      have ⟨h, _⟩ := compileInParams_eraseVals d (cols.map Prod.snd) #[] #[] rfl
      simp [SqlQuery.eraseVals, SqlQuery.compile, hfst, hsnd, h]
  | update _ sets w _ =>
      have ⟨hS, hszS⟩ := compileSets_eraseVals d sets #[] #[] rfl
      have ⟨hW, _⟩ := w.compileQual_eraseVals d "" _ _ hszS; simp [SqlQuery.eraseVals, SqlQuery.compile, SqlExpr.compile, hS, hW]

/-- **SQL Injection Closure (Non-Interference Theorem):**
    Any two typed `SqlQuery` values with the same AST skeleton (`sameShape`) compile to
    bit-for-bit identical SQL strings regardless of arbitrary runtime parameter payloads. -/
theorem SqlQuery.compile_sameShape (d : SqlDialect) {q₁ q₂ : SqlQuery} (hsh : q₁.sameShape q₂) :
    (q₁.compile d).1 = (q₂.compile d).1 := by rw [q₁.compile_eraseVals d, hsh, ← q₂.compile_eraseVals d]

theorem SqlQuery.compile_no_semicolon (d : SqlDialect) (q : SqlQuery) : ∀ c ∈ (q.compile d).1.toList, c ≠ ';' := by
  cases q <;> ((intro c hc); (simp only [SqlQuery.compile, String.toList_append, List.mem_append] at hc); (revert hc); (try simp only [or_imp]); repeat any_goals constructor) <;>
    (intro hc; first
      | with_reducible exact SqlIdent.quoteIdent_no_semicolon _ c hc
      | with_reducible exact SqlIdent.joinQuotedPrefixed_no_semicolon _ (NoSemi.lit _ rfl) _ c hc
      | with_reducible exact SqlAggOp.render_no_semicolon _ c hc
      | with_reducible exact SqlExpr.compile_no_semicolon _ _ _ c hc
      | with_reducible exact SqlExpr.compileQual_no_semicolon _ _ (NoSemi.lit _ rfl) _ _ c hc
      | with_reducible exact compileInParams_no_semicolon _ _ _ c hc
      | with_reducible exact compileSets_no_semicolon _ _ _ c hc
      | with_reducible exact renderReturning_no_semicolon _ c hc
      | with_reducible exact renderLimitOffset_no_semicolon _ _ _ c hc
      | with_reducible exact renderOrderBy_no_semicolon _ (NoSemi.lit _ rfl) _ c hc
      | exact NoSemi.lit _ rfl c hc)

/-! ## Abstract Relational Policy & Invariant Soundness Model -/

section RelModel
variable {Row : Type}
def evalSelect (tbl : List Row) (wherePred : Row → Bool) : List Row := tbl.filter wherePred
def evalInsert (tbl : List Row) (newRow : Row) : List Row := newRow :: tbl
def evalUpdate (tbl : List Row) (wherePred : Row → Bool) (setFn : Row → Row) : List Row := tbl.map fun r => if wherePred r then setFn r else r
def evalDelete (tbl : List Row) (wherePred : Row → Bool) : List Row := tbl.filter fun r => !wherePred r

theorem evalSelect_satisfies_policy (RowInv ReadPolicy : Row → Prop) (tbl : List Row) (wherePred : Row → Bool)
    (htbl : ∀ r ∈ tbl, RowInv r) (hpol : ∀ r, RowInv r → wherePred r = true → ReadPolicy r) :
    ∀ r ∈ evalSelect tbl wherePred, RowInv r ∧ ReadPolicy r := fun r hr =>
  let ⟨hm, hw⟩ := List.mem_filter.1 hr; ⟨htbl r hm, hpol r (htbl r hm) hw⟩

theorem evalInsert_preserves_inv (RowInv InsertPolicy : Row → Prop) (tbl : List Row) (newRow : Row)
    (htbl : ∀ r ∈ tbl, RowInv r) (hinv : RowInv newRow) (_hpol : InsertPolicy newRow) :
    ∀ r ∈ evalInsert tbl newRow, RowInv r := fun r hr => (List.mem_cons.1 hr).elim (· ▸ hinv) (htbl r)

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

inductive SqlColType where | text | int | bool | bytes deriving Inhabited, DecidableEq, Repr
def SqlColType.render (d : SqlDialect) : SqlColType → String
  | .text => "TEXT" | .int => d.pick "BIGINT" "INTEGER" | .bool => d.pick "BOOLEAN" "INTEGER" | .bytes => d.pick "BYTEA" "BLOB"

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

private def optClause (opt : Option α) (f : α → String) : String := opt.map f |>.getD ""
private def joinSqlStmts (stmts : List String) : String := if stmts.isEmpty then "" else String.intercalate ";\n" stmts ++ ";\n"
private def ColumnSchema.renderCore (d : SqlDialect) (c : ColumnSchema) (mid : String) : String :=
  c.name.quoteIdent ++ " " ++ c.colType.render d ++ (if c.nullable then "" else " NOT NULL") ++
    mid ++ optClause c.checkSql? (" CHECK (" ++ · ++ ")")

def ColumnSchema.renderDef (d : SqlDialect) (c : ColumnSchema) : String :=
  c.renderCore d <| (if c.isPrimaryKey then " PRIMARY KEY" else "") ++
    (if c.isUnique && !c.isPrimaryKey then " UNIQUE" else "") ++
    optClause c.references? fun (rt, rc) => " REFERENCES " ++ rt.quoteIdent ++ "(" ++ rc.quoteIdent ++ ")"
def TableSchema.renderCreateTable (d : SqlDialect) (t : TableSchema) : String :=
  "CREATE TABLE IF NOT EXISTS " ++ t.name.quoteIdent ++ " (" ++ String.intercalate ", " (t.columns.map (·.renderDef d)) ++ ")"
def TableSchema.idxName (t : TableSchema) (i : Nat) : String := "idx_" ++ t.name.raw ++ "_" ++ toString i
private def renderCreateIndex (tbl : SqlIdent) (idxName : String) (cols : List SqlIdent) : String :=
  "CREATE INDEX IF NOT EXISTS \"" ++ idxName ++ "\" ON " ++ tbl.quoteIdent ++ " (" ++ SqlIdent.joinQuoted cols ++ ")"
def TableSchema.renderIndexes (t : TableSchema) : List String :=
  t.indexes.zipIdx.map fun (cols, i) => renderCreateIndex t.name (t.idxName i) cols
def TableSchema.renderDdlStatements (d : SqlDialect) (t : TableSchema) : List String :=
  t.renderCreateTable d :: t.renderIndexes
def TableSchema.renderPostgresRls (t : TableSchema) : List String :=
  let pols :=
    (t.rlsRead?.map fun e => s!"CREATE POLICY \"qed_read_{t.name.raw}\" ON {t.name.quoteIdent} FOR SELECT USING ({e})").toList ++
    (t.rlsWrite?.map fun e => s!"CREATE POLICY \"qed_write_{t.name.raw}\" ON {t.name.quoteIdent} FOR ALL USING ({e}) WITH CHECK ({e})").toList
  if pols.isEmpty then [] else ("ALTER TABLE " ++ t.name.quoteIdent ++ " ENABLE ROW LEVEL SECURITY") :: pols
def renderDatabaseDdl (d : SqlDialect) (tables : List TableSchema) : String := joinSqlStmts (tables.flatMap (·.renderDdlStatements d))
def renderDatabaseRlsDdl (tables : List TableSchema) : String := joinSqlStmts (tables.flatMap (·.renderPostgresRls))

/-! ## Pure Verified Schema Diffing & Safe Additive Migrations (`MigrationStep`) -/

inductive MigrationStep where
  | createTable (table : TableSchema)
  | addColumn   (table : SqlIdent) (col : ColumnSchema) (defaultSql? : Option String := none)
  | createIndex (table : SqlIdent) (idxName : String) (cols : List SqlIdent)
deriving Inhabited, Repr

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
  | postgresUrl  (url : String)
  | sqlitePath   (path : String)
  | sqliteEnv    (envVar : String) (defaultPath? : Option String := none)
  | cloudflareD1 (accountEnv : String) (accountDefault? : Option String)
                 (dbEnv : String) (dbDefault? : Option String) (tokenSecret : String)
  | turso        (urlEnv : String) (tokenSecret : String)
  | httpSql      (urlEnv : String) (tokenSecret? : Option String := none)
  | managedPostgres (dbName : String) (env : Qed.Cloud.DeployEnv)
deriving Inhabited, DecidableEq, Repr

structure DbConfig where
  name          : String
  endpoint      : DbEndpoint
  devFallback?  : Option DbEndpoint := none
  envEndpoints? : Option (Qed.Cloud.EnvMap DbEndpoint) := none
  isManaged     : Bool := false
  tables        : List TableSchema := []
deriving Inhabited, Repr

def DbConfig.endpointForEnv (cfg : DbConfig) (env : Qed.Cloud.DeployEnv) : DbEndpoint :=
  match cfg.envEndpoints? with
  | some em => em.get env
  | none    => match env with | .dev => cfg.devFallback?.getD cfg.endpoint | _ => cfg.endpoint
theorem DbConfig.endpointForEnv_prod_no_devFallback (cfg : DbConfig) (hnone : cfg.envEndpoints? = none) :
    cfg.endpointForEnv .prod = cfg.endpoint := by simp [DbConfig.endpointForEnv, hnone]
theorem DbConfig.endpointForEnv_envMap (cfg : DbConfig) (em : Qed.Cloud.EnvMap DbEndpoint)
    (h : cfg.envEndpoints? = some em) (env : Qed.Cloud.DeployEnv) :
    cfg.endpointForEnv env = em.get env := by simp [DbConfig.endpointForEnv, h]

abbrev DbRow := Array SqlVal
structure DbResult where
  rows     : Array DbRow := #[]
  affected : Nat := 0
deriving Inhabited, DecidableEq

/-! ## Compact JSON Wire Encoding for `SqlVal` (Used Across SQLite FFI & HTTP SQL) -/

def SqlVal.toTaggedJson : SqlVal → Json
  | .null => .obj [("t", .str "n")] | .int i => .obj [("t", .str "i"), ("v", .str (toString i))]
  | .text s => .obj [("t", .str "s"), ("v", .str s)] | .bool b => .obj [("t", .str "b"), ("v", .bool b)]
  | .bytes bs => .obj [("t", .str "x"), ("v", .str (Proto.encodeHex bs))]

def SqlVal.toPlainJson : SqlVal → Json
  | .null => .null | .int i => .num ⟨i, 0⟩ | .text s => .str s | .bool b => .bool b | .bytes bs => .str (Proto.encodeHex bs)

def jsonNatAt (j : Json) (k : String) : Nat := (j.natAt? k).getD 0
abbrev jsonStrAt := Json.strAt?

def parseJsonIntCell (v? : Option Json) (badPfx missingErr : String) : Except String SqlVal :=
  match v? with
  | some (.str s) => (s.toInt?).elim (.error s!"{badPfx}: {s}") (.ok ∘ .int)
  | some (.num n) => .ok (.int n.mantissa) | _ => .error missingErr

def decodeJsonArrayRow (cellDec : Json → Except String SqlVal) (notArrErr : String) : Json → Except String DbRow
  | .arr vals => (vals.mapM cellDec).map List.toArray | _ => .error notArrErr

def decodeJsonRows (j : Json) (key : String) (rowDec : Json → Except String DbRow) (notArrErr : String) :
    Except String (Array DbRow) :=
  match j.get? key with
  | some (.arr rs) => (rs.mapM rowDec).map List.toArray | none => .ok #[] | _ => .error notArrErr

def SqlVal.fromTaggedJson : Json → Except String SqlVal
  | j@(.obj _) => match j.strAt? "t", j.get? "v" with
      | some "n", _ => .ok .null
      | some "i", v => parseJsonIntCell v "bad int" "missing int value"
      | some "s", some (.str s) => .ok (.text s) | some "s", _ => .error "missing string value"
      | some "b", some (.bool b) => .ok (.bool b) | some "b", some (.num n) => .ok (.bool (n.mantissa != 0)) | some "b", _ => .error "missing bool value"
      | some "x", some (.str hx) => (Proto.decodeHex hx).map .bytes | some "x", _ => .error "missing bytes hex"
      | _, _ => .error "unknown SqlVal tag"
  | .null => .ok .null | .str s => .ok (.text s) | .num n => .ok (.int n.mantissa) | .bool b => .ok (.bool b)
  | _ => .error "unexpected JSON value for SqlVal"

def encodeTaggedResultJson (res : DbResult) : String :=
  Json.render (.obj [("rows", .arr (res.rows.toList.map fun r => .arr (r.toList.map SqlVal.toTaggedJson))),
                     ("affected", .num ⟨Int.ofNat res.affected, 0⟩)])

def decodeTaggedResultJson (raw : String) : Except String DbResult := do
  let j@(.obj _) ← Json.parse raw 128 | .error "expected JSON object from database result"
  let rows ← decodeJsonRows j "rows" (decodeJsonArrayRow SqlVal.fromTaggedJson "expected row array") "expected rows array"
  return { rows, affected := jsonNatAt j "affected" }

end Qed.Server.Db
