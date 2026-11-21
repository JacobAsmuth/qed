import Lean
import Qed.Field
import Qed.Diag
import Qed.Server.Core
import Qed.Server.Registry
import Qed.Server.Db.Core

namespace Qed.Server.Db

instance {α : Type} {p : α → Prop} [ToSql α] : ToSql (Qed.Field p) where
  toSql f := ToSql.toSql f.val

instance {α : Type} {p : α → Prop} [FromSql α] [DecidablePred p] : FromSql (Qed.Field p) where
  fromSql v := do
    let a ← FromSql.fromSql (α := α) v
    if h : p a then .ok ⟨a, h⟩
    else .error "database column value violated table `where` constraint"

/-! ## Generic Zero-Trust Proof-Checked Database Operations (`dbSelect`, `dbFindOne`, `dbCount`,
    `dbInsert`, `dbUpdate`, `dbUpdateOne`, `dbDelete`)

    Every operation:
    1. Requires compile-time kernel proofs for table `policy` rules (`ReadPolicy`, `InsertPolicy`,
       `UpdatePolicy`, `DeletePolicy`), single-row `RowInv`, and two-state `TransInv`.
    2. Re-verifies `rowInvBool` (and `wherePred`/`postPred`) zero-trust on every decoded wire row.
    3. Provides `SafeIO` and `SafeIOEnsures` instances so DB results automatically feed `RowInv`
       and query facts into server `ensures` postconditions and client component invariants. -/

private def decodeRowErr {Row : Type} (decode : DbRow → Except String Row) (r : DbRow) :
    Except ApiError Row :=
  (decode r).mapError fun e => ApiError.internal s!"database row decode failed: {e}"

private def decodeJoinRowErr {RowL RowR : Type} (leftColCount : Nat)
    (decodeL : DbRow → Except String RowL) (decodeR : DbRow → Except String RowR) (r : DbRow) :
    Except ApiError (RowL × RowR) :=
  match decodeL (r.extract 0 leftColCount), decodeR (r.extract leftColCount r.size) with
  | .error e, _ => .error (ApiError.internal s!"database join left-row decode failed: {e}")
  | _, .error e => .error (ApiError.internal s!"database join right-row decode failed: {e}")
  | .ok l, .ok r => .ok (l, r)

private def decodeCheckedList {Row : Type}
    (decode : DbRow → Except ApiError Row) (check : Row → Bool)
    (errMsg : String := "database row violated verified table invariant or query predicate") :
    List DbRow → Except ApiError (List Row)
  | [] => .ok []
  | r :: rs => do
      let row ← decode r
      if check row then return row :: (← decodeCheckedList decode check errMsg rs)
      else .error (ApiError.internal errMsg)

private theorem decodeCheckedList_sound {Row : Type}
    (decode : DbRow → Except ApiError Row) (check : Row → Bool) (errMsg : String) :
    ∀ (raws : List DbRow) (out : List Row),
      decodeCheckedList decode check errMsg raws = .ok out →
      ∀ r ∈ out, check r = true
  | [], _, h => by
      injection h with h; subst h; intro _ hm; exact False.elim (List.not_mem_nil hm)
  | raw :: rest, _, h => by
      unfold decodeCheckedList at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      cases hd : decode raw with
      | error _ => rw [hd] at h; contradiction
      | ok row =>
          rw [hd] at h; dsimp only at h
          cases hc : check row with
          | false => simp [hc] at h
          | true =>
              simp only [hc, ↓reduceIte] at h
              cases hr : decodeCheckedList decode check errMsg rest with
              | error _ => rw [hr] at h; contradiction
              | ok tl =>
                  rw [hr] at h; injection h with h; subst h
                  intro r hm
                  exact (List.mem_cons.1 hm).elim (· ▸ hc) (decodeCheckedList_sound decode check errMsg rest tl hr r)

private def decodeCheckedOne {Row : Type}
    (decode : DbRow → Except String Row) (check : Row → Bool) (errMsg : String) :
    List DbRow → Except ApiError (Option Row)
  | [] => .ok none
  | raw :: _ => do
      let row ← decodeRowErr decode raw
      if check row then .ok (some row) else .error (ApiError.internal errMsg)

private theorem decodeCheckedOne_sound {Row : Type}
    (decode : DbRow → Except String Row) (check : Row → Bool) (errMsg : String)
    (raws : List DbRow) (row : Row)
    (h : decodeCheckedOne decode check errMsg raws = .ok (some row)) :
    check row = true := by
  cases raws with
  | nil => simp [decodeCheckedOne] at h
  | cons raw _ =>
      simp only [decodeCheckedOne, bind, Except.bind] at h
      cases hd : decodeRowErr decode raw with
      | error _ => rw [hd] at h; contradiction
      | ok r =>
          rw [hd] at h; dsimp only at h
          cases hc : check r with
          | false => simp [hc] at h
          | true =>
              simp only [hc, ↓reduceIte, Except.ok.injEq, Option.some.injEq] at h
              exact h ▸ hc

private def decodeFirstCell {α β : Type} [FromSql α]
    (wrap : α → β) (nullAs : Option β) (emptyVal : β) (label : String)
    (dbRes : DbResult) : Except ApiError β :=
  match dbRes.rows[0]?.bind (·[0]?) with
  | none => .ok emptyVal
  | some v =>
      match nullAs, v with
      | some d, .null => .ok d
      | _, _ =>
          ((FromSql.fromSql (α := α) v).map wrap).mapError fun e =>
            ApiError.internal s!"database {label} decode failed: {e}"

@[inline, specialize]
def execDbMaybeTx {m : Type → Type} [MonadServer m] (cfg : DbConfig) (q : SqlQuery)
    (txId? : Option UInt64 := none) : m (Except ApiError DbResult) :=
  match txId? with
  | some tid => MonadServer.dbTxExec cfg tid q
  | none     => MonadServer.dbExec cfg q

private theorem noAtomic_execDbMaybeTx {σ : Type} (cfg : DbConfig) (q : SqlQuery)
    (txId? : Option UInt64) {β : Type} (k : Except ApiError DbResult → ThreadProg σ β)
    (hk : ∀ r, NoAtomic (k r)) :
    NoAtomic (execDbMaybeTx (m := ThreadProg σ) cfg q txId? >>= k) := by
  cases txId? with
  | none     => exact .io (.dbExec cfg q) k hk
  | some tid => exact .io (.dbTxExec cfg tid q) k hk

private theorem progEnsures_execDbMaybeTx {σ : Type} {Inv : σ → Prop} (cfg : DbConfig) (q : SqlQuery)
    (txId? : Option UInt64) {β : Type} {Post : β → Prop}
    (k : Except ApiError DbResult → ThreadProg σ β)
    (hk : ∀ r, ProgEnsures Inv Post (k r)) :
    ProgEnsures Inv Post (execDbMaybeTx (m := ThreadProg σ) cfg q txId? >>= k) := by
  cases txId? with
  | none     => exact .io (.dbExec cfg q) k hk
  | some tid => exact .io (.dbTxExec cfg tid q) k hk

private theorem decodeCheckedList_ensures {σ Row : Type} {Inv : σ → Prop}
    (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64)
    (decode : DbRow → Except ApiError Row) (check : Row → Bool) (errMsg : String)
    {P : Row → Prop} (hP : ∀ r, check r = true → P r) :
    ProgEnsures Inv
      (fun res => match res with | .ok rows => ∀ r ∈ rows.toList, P r | .error _ => True)
      (execDbMaybeTx (m := ThreadProg σ) cfg q txId? >>= fun res =>
        pure (res.bind fun dbRes => (decodeCheckedList decode check errMsg dbRes.rows.toList).map List.toArray)) :=
  progEnsures_execDbMaybeTx cfg q txId? _ fun res => .pure _ (by
    cases res with
    | error _ => trivial
    | ok dbRes =>
        dsimp only [Except.bind, Except.map]
        cases hd : decodeCheckedList decode check errMsg dbRes.rows.toList with
        | error _ => trivial
        | ok out => intro r hr; exact hP r (decodeCheckedList_sound decode check errMsg _ out hd r (by simpa using hr)))

private theorem decodeCheckedOne_ensures {σ Row : Type} {Inv : σ → Prop}
    (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64)
    (decode : DbRow → Except String Row) (check : Row → Bool) (errMsg : String)
    {P : Row → Prop} (hP : ∀ r, check r = true → P r) :
    ProgEnsures Inv
      (fun res => ∀ r, res = .ok (some r) → P r)
      (execDbMaybeTx (m := ThreadProg σ) cfg q txId? >>= fun res =>
        pure (res.bind fun dbRes => decodeCheckedOne decode check errMsg dbRes.rows.toList)) :=
  progEnsures_execDbMaybeTx cfg q txId? _ fun res => .pure _ (by
    intro r hr
    cases res with
    | error _ => simp [Except.bind] at hr
    | ok dbRes => exact hP r (decodeCheckedOne_sound decode check errMsg dbRes.rows.toList r hr))

/-- Verified `SELECT` returning all matching rows with zero-trust `RowInv ∧ wherePred` guarantees. -/
@[specialize]
def dbSelect {Row : Type} {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery)
    (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool)
    (_hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (wherePred : Row → Bool)
    (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (_hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r)
    (txId? : Option UInt64 := none) :
    m (Except ApiError (Array Row)) := do
  let res ← execDbMaybeTx cfg q txId?
  return res.bind fun dbRes =>
    (decodeCheckedList (decodeRowErr decode) (fun r => rowInvBool r && wherePred r)
      "database row violated verified table invariant or query predicate" dbRes.rows.toList).map List.toArray

/-- Verified `SELECT ... LIMIT 1` returning `Option Row` with zero-trust `RowInv ∧ wherePred` guarantees. -/
@[specialize]
def dbFindOne {Row : Type} {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery)
    (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool)
    (_hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (wherePred : Row → Bool)
    (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (_hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r)
    (txId? : Option UInt64 := none) :
    m (Except ApiError (Option Row)) := do
  let res ← execDbMaybeTx cfg q txId?
  return res.bind fun dbRes =>
    decodeCheckedOne decode (fun r => rowInvBool r && wherePred r)
      "database row violated verified table invariant or query predicate" dbRes.rows.toList

/-- Verified `SELECT COUNT(*)` requiring `ReadPolicy` on all counted rows. -/
@[specialize]
def dbCount {Row : Type} {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery)
    (RowInv : Row → Prop)
    (wherePred : Row → Bool)
    (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (_hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r)
    (txId? : Option UInt64 := none) :
    m (Except ApiError Nat) := do
  let res ← execDbMaybeTx cfg q txId?
  return res.bind (decodeFirstCell (α := Nat) id none 0 "COUNT")

/-- Verified `SELECT SUM(col)` for `Nat` columns (returning `0` on empty result sets) requiring `ReadPolicy`. -/
@[specialize]
def dbSumNat {Row : Type} {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery)
    (RowInv : Row → Prop)
    (wherePred : Row → Bool)
    (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (_hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r)
    (txId? : Option UInt64 := none) :
    m (Except ApiError Nat) := do
  let res ← execDbMaybeTx cfg q txId?
  return res.bind (decodeFirstCell (α := Nat) id (some 0) 0 "SUM")

/-- Verified `SELECT SUM(col)` for `Int` columns (returning `0` on empty result sets) requiring `ReadPolicy`. -/
@[specialize]
def dbSumInt {Row : Type} {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery)
    (RowInv : Row → Prop)
    (wherePred : Row → Bool)
    (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (_hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r)
    (txId? : Option UInt64 := none) :
    m (Except ApiError Int) := do
  let res ← execDbMaybeTx cfg q txId?
  return res.bind (decodeFirstCell (α := Int) id (some 0) 0 "SUM")

/-- Verified `SELECT MIN(col)` / `MAX(col)` returning `Option Val` (`none` when 0 rows match),
    inferring `Val` from `_proj` and requiring `ReadPolicy` on all aggregated rows. -/
@[specialize]
def dbAggOpt {Row Val : Type} [FromSql Val] {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery)
    (_proj : Row → Val)
    (RowInv : Row → Prop)
    (wherePred : Row → Bool)
    (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (_hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r)
    (txId? : Option UInt64 := none) :
    m (Except ApiError (Option Val)) := do
  let res ← execDbMaybeTx cfg q txId?
  return res.bind (decodeFirstCell (α := Val) some (some none) none "aggregate")

/-- Verified typed `INNER JOIN` checking BOTH tables' `ReadPolicy` at compile time and
    zero-trust verifying both `RowInv`s, both `wherePred`s, and the join key equality on every row. -/
@[specialize]
def dbJoinSelect {RowL RowR Key : Type} [BEq Key] {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery) (leftColCount : Nat)
    (decodeL : DbRow → Except String RowL) (decodeR : DbRow → Except String RowR)
    (RowInvL : RowL → Prop) (rowInvBoolL : RowL → Bool) (_hInvSoundL : ∀ r, rowInvBoolL r = true → RowInvL r)
    (RowInvR : RowR → Prop) (rowInvBoolR : RowR → Bool) (_hInvSoundR : ∀ r, rowInvBoolR r = true → RowInvR r)
    (wherePredL : RowL → Bool) (wherePredR : RowR → Bool)
    (keyL : RowL → Key) (keyR : RowR → Key)
    (ReadPolicyL : RequestCtx → RowL → Prop) (ReadPolicyR : RequestCtx → RowR → Prop)
    (ctx : RequestCtx)
    (_hPolicyL : ∀ r, RowInvL r → wherePredL r = true → ReadPolicyL ctx r)
    (_hPolicyR : ∀ r, RowInvR r → wherePredR r = true → ReadPolicyR ctx r)
    (txId? : Option UInt64 := none) :
    m (Except ApiError (Array (RowL × RowR))) := do
  let res ← execDbMaybeTx cfg q txId?
  return res.bind fun dbRes =>
    (decodeCheckedList (decodeJoinRowErr leftColCount decodeL decodeR)
      (fun p => rowInvBoolL p.1 && wherePredL p.1 && rowInvBoolR p.2 && wherePredR p.2 && (keyL p.1 == keyR p.2))
      "database joined row violated verified table invariant or query predicate"
      dbRes.rows.toList).map List.toArray

/-- Verified `INSERT` requiring `RowInv newRow` and `InsertPolicy ctx newRow` at compile time. -/
@[specialize]
def dbInsert {Row : Type} {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery) (newRow : Row)
    (RowInv : Row → Prop)
    (InsertPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (_hInv : RowInv newRow)
    (_hPolicy : InsertPolicy ctx newRow)
    (txId? : Option UInt64 := none) :
    m (Except ApiError Row) := do
  let res ← execDbMaybeTx cfg q txId?
  return res.map fun _ => newRow

/-- Verified `UPDATE ... RETURNING *` returning all updated rows, requiring:
    1. `UpdatePolicy ctx oldRow` (caller may update matched rows)
    2. `UpdatePolicy ctx (setFn oldRow)` (no ownership hijacking)
    3. `RowInv (setFn oldRow)` (all column `where` & single-row invariants preserved)
    4. `TransInv oldRow (setFn oldRow)` (all `old(row)` & `transition` invariants preserved) -/
@[specialize]
def dbUpdate {Row : Type} {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery)
    (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool)
    (_hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (TransInv : Row → Row → Prop)
    (wherePred : Row → Bool) (setFn : Row → Row)
    (postPred : Row → Bool)
    (UpdatePolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (_hPolicyOld : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx r)
    (_hPolicyNew : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx (setFn r))
    (_hInvPres   : ∀ r, RowInv r → wherePred r = true → RowInv (setFn r))
    (_hTrans     : ∀ r, RowInv r → wherePred r = true → TransInv r (setFn r))
    (txId? : Option UInt64 := none) :
    m (Except ApiError (Array Row)) := do
  let res ← execDbMaybeTx cfg q txId?
  return res.bind fun dbRes =>
    (decodeCheckedList (decodeRowErr decode) (fun r => rowInvBool r && postPred r)
      "database row violated verified table invariant or query predicate" dbRes.rows.toList).map List.toArray

/-- Verified single-row `UPDATE ... RETURNING *` returning `Option Row` (`none` if 0 rows matched). -/
@[specialize]
def dbUpdateOne {Row : Type} {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery)
    (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool)
    (_hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (TransInv : Row → Row → Prop)
    (wherePred : Row → Bool) (setFn : Row → Row)
    (postPred : Row → Bool)
    (UpdatePolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (_hPolicyOld : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx r)
    (_hPolicyNew : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx (setFn r))
    (_hInvPres   : ∀ r, RowInv r → wherePred r = true → RowInv (setFn r))
    (_hTrans     : ∀ r, RowInv r → wherePred r = true → TransInv r (setFn r))
    (txId? : Option UInt64 := none) :
    m (Except ApiError (Option Row)) := do
  let res ← execDbMaybeTx cfg q txId?
  return res.bind fun dbRes =>
    decodeCheckedOne decode (fun r => rowInvBool r && postPred r)
      "updated database row violated verified table invariant or postcondition" dbRes.rows.toList

/-- Verified `DELETE` requiring `DeletePolicy` on all deleted rows and returning affected count. -/
@[specialize]
def dbDelete {Row : Type} {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery)
    (RowInv : Row → Prop)
    (wherePred : Row → Bool)
    (DeletePolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (_hPolicy : ∀ r, RowInv r → wherePred r = true → DeletePolicy ctx r)
    (txId? : Option UInt64 := none) :
    m (Except ApiError Nat) := do
  let res ← execDbMaybeTx cfg q txId?
  return res.map (·.affected)

/-! ## `SafeIO` & `SafeIOEnsures` Instances (Automatic Zero-Trust Postcondition Propagation) -/

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (wherePred : Row → Bool) (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r) (txId? : Option UInt64) :
    SafeIOEnsures
      (dbSelect (m := ThreadProg σ) cfg q decode RowInv rowInvBool hInvSound wherePred ReadPolicy ctx hPolicy txId?)
      (fun res => match res with | .ok rows => ∀ r ∈ rows.toList, RowInv r ∧ wherePred r = true | .error _ => True) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _
  ensures := decodeCheckedList_ensures cfg q txId? _ _ _ fun r h => by
    simp only [Bool.and_eq_true] at h; exact ⟨hInvSound r h.1, h.2⟩

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (wherePred : Row → Bool) (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r) (txId? : Option UInt64) :
    SafeIOEnsures
      (dbFindOne (m := ThreadProg σ) cfg q decode RowInv rowInvBool hInvSound wherePred ReadPolicy ctx hPolicy txId?)
      (fun res => ∀ r, res = .ok (some r) → RowInv r ∧ wherePred r = true) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _
  ensures := decodeCheckedOne_ensures cfg q txId? _ _ _ fun r h => by
    simp only [Bool.and_eq_true] at h; exact ⟨hInvSound r h.1, h.2⟩

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery)
    (RowInv : Row → Prop) (wherePred : Row → Bool)
    (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r) (txId? : Option UInt64) :
    SafeIO (dbCount (m := ThreadProg σ) cfg q RowInv wherePred ReadPolicy ctx hPolicy txId?) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery)
    (RowInv : Row → Prop) (wherePred : Row → Bool)
    (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r) (txId? : Option UInt64) :
    SafeIO (dbSumNat (m := ThreadProg σ) cfg q RowInv wherePred ReadPolicy ctx hPolicy txId?) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery)
    (RowInv : Row → Prop) (wherePred : Row → Bool)
    (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r) (txId? : Option UInt64) :
    SafeIO (dbSumInt (m := ThreadProg σ) cfg q RowInv wherePred ReadPolicy ctx hPolicy txId?) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _

instance {σ Row Val : Type} [FromSql Val] (cfg : DbConfig) (q : SqlQuery) (proj : Row → Val)
    (RowInv : Row → Prop) (wherePred : Row → Bool)
    (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r) (txId? : Option UInt64) :
    SafeIO (dbAggOpt (m := ThreadProg σ) cfg q proj RowInv wherePred ReadPolicy ctx hPolicy txId?) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _

instance {σ RowL RowR Key : Type} [BEq Key] (cfg : DbConfig) (q : SqlQuery) (leftColCount : Nat)
    (decodeL : DbRow → Except String RowL) (decodeR : DbRow → Except String RowR)
    (RowInvL : RowL → Prop) (rowInvBoolL : RowL → Bool) (hInvSoundL : ∀ r, rowInvBoolL r = true → RowInvL r)
    (RowInvR : RowR → Prop) (rowInvBoolR : RowR → Bool) (hInvSoundR : ∀ r, rowInvBoolR r = true → RowInvR r)
    (wherePredL : RowL → Bool) (wherePredR : RowR → Bool) (keyL : RowL → Key) (keyR : RowR → Key)
    (ReadPolicyL : RequestCtx → RowL → Prop) (ReadPolicyR : RequestCtx → RowR → Prop)
    (ctx : RequestCtx)
    (hPolicyL : ∀ r, RowInvL r → wherePredL r = true → ReadPolicyL ctx r)
    (hPolicyR : ∀ r, RowInvR r → wherePredR r = true → ReadPolicyR ctx r)
    (txId? : Option UInt64) :
    SafeIOEnsures
      (dbJoinSelect (m := ThreadProg σ) cfg q leftColCount decodeL decodeR
        RowInvL rowInvBoolL hInvSoundL RowInvR rowInvBoolR hInvSoundR
        wherePredL wherePredR keyL keyR ReadPolicyL ReadPolicyR ctx hPolicyL hPolicyR txId?)
      (fun res => match res with
        | .ok rows => ∀ p ∈ rows.toList, RowInvL p.1 ∧ wherePredL p.1 = true ∧ RowInvR p.2 ∧ wherePredR p.2 = true
        | .error _ => True) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _
  ensures := by
    intro Inv
    refine progEnsures_imp (decodeCheckedList_ensures cfg q txId? (decodeJoinRowErr leftColCount decodeL decodeR)
      (fun p => rowInvBoolL p.1 && wherePredL p.1 && rowInvBoolR p.2 && wherePredR p.2 && (keyL p.1 == keyR p.2))
      "database joined row violated verified table invariant or query predicate"
      (P := fun p => RowInvL p.1 ∧ wherePredL p.1 = true ∧ RowInvR p.2 ∧ wherePredR p.2 = true)
      fun p h => by simp only [Bool.and_eq_true] at h; exact ⟨hInvSoundL p.1 h.1.1.1.1, h.1.1.1.2, hInvSoundR p.2 h.1.1.2, h.1.2⟩) ?_
    intro res h; cases res <;> exact h

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery) (newRow : Row)
    (RowInv : Row → Prop) (InsertPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hInv : RowInv newRow) (hPolicy : InsertPolicy ctx newRow) (txId? : Option UInt64) :
    SafeIOEnsures
      (dbInsert (m := ThreadProg σ) cfg q newRow RowInv InsertPolicy ctx hInv hPolicy txId?)
      (fun res => match res with | .ok r => r = newRow ∧ RowInv r | .error _ => True) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _
  ensures := progEnsures_execDbMaybeTx cfg q txId? _ fun res =>
    .pure _ (by cases res <;> simp [Except.map, hInv])

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (TransInv : Row → Row → Prop) (wherePred : Row → Bool) (setFn : Row → Row) (postPred : Row → Bool)
    (UpdatePolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPO : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx r)
    (hPN : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx (setFn r))
    (hIP : ∀ r, RowInv r → wherePred r = true → RowInv (setFn r))
    (hTr : ∀ r, RowInv r → wherePred r = true → TransInv r (setFn r)) (txId? : Option UInt64) :
    SafeIOEnsures
      (dbUpdate (m := ThreadProg σ) cfg q decode RowInv rowInvBool hInvSound TransInv
        wherePred setFn postPred UpdatePolicy ctx hPO hPN hIP hTr txId?)
      (fun res => match res with | .ok rows => ∀ r ∈ rows.toList, RowInv r ∧ postPred r = true | .error _ => True) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _
  ensures := decodeCheckedList_ensures cfg q txId? _ _ _ fun r h => by
    simp only [Bool.and_eq_true] at h; exact ⟨hInvSound r h.1, h.2⟩

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (TransInv : Row → Row → Prop) (wherePred : Row → Bool) (setFn : Row → Row) (postPred : Row → Bool)
    (UpdatePolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPO : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx r)
    (hPN : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx (setFn r))
    (hIP : ∀ r, RowInv r → wherePred r = true → RowInv (setFn r))
    (hTr : ∀ r, RowInv r → wherePred r = true → TransInv r (setFn r)) (txId? : Option UInt64) :
    SafeIOEnsures
      (dbUpdateOne (m := ThreadProg σ) cfg q decode RowInv rowInvBool hInvSound TransInv
        wherePred setFn postPred UpdatePolicy ctx hPO hPN hIP hTr txId?)
      (fun res => ∀ r, res = .ok (some r) → RowInv r ∧ postPred r = true) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _
  ensures := decodeCheckedOne_ensures cfg q txId? _ _ _ fun r h => by
    simp only [Bool.and_eq_true] at h; exact ⟨hInvSound r h.1, h.2⟩

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery)
    (RowInv : Row → Prop) (wherePred : Row → Bool)
    (DeletePolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → DeletePolicy ctx r) (txId? : Option UInt64) :
    SafeIO (dbDelete (m := ThreadProg σ) cfg q RowInv wherePred DeletePolicy ctx hPolicy txId?) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _

theorem some_getD_eq_self_iff {α : Type} (o : Option α) (d : α) :
    some (o.getD d) = o ↔ o ≠ none := by
  cases o <;> simp

open Lean Elab Command in
/-- Builds a validated `SqlIdent` syntax term or throws a clear compile-time error. -/
def mkSqlIdentTerm (ref : Syntax) (raw : String) : CommandElabM Term := do
  if !isSafeSqlIdent raw then
    throwErrorAt ref s!"invalid SQL identifier `{raw}` (must start with an ASCII letter or `_` and contain only ASCII letters, digits, and `_`, max 63 chars)"
  let lit := Syntax.mkStrLit raw
  `(Qed.Server.Db.SqlIdent.mk $lit (by decide))

/-! ## Dedicated Database Policy & Invariant Proof Tactic (`qedDbProve`) -/

syntax (name := qedDbProveTac) "qedDbProve" "[" ident,* "]" str str str : tactic

open Lean Meta Elab Tactic in
@[tactic qedDbProveTac]
def elabQedDbProve : Tactic := fun stx => do
  let unfoldIds : Array Ident := (stx.getArg 2).getSepArgs.map fun s => ⟨s⟩
  let kindStr := (⟨(stx.getArg 4)⟩ : TSyntax `str).getString
  let opStr   := (⟨(stx.getArg 5)⟩ : TSyntax `str).getString
  let hintStr := (⟨(stx.getArg 6)⟩ : TSyntax `str).getString
  let runSimplifier : TacticM Unit :=
    evalTactic (← `(tactic|
      (intros;
       try dsimp only [$[$unfoldIds:ident],*] at *;
       try simp (config := { zetaDelta := true }) only [$[$unfoldIds:ident],*, Qed.Server.qedReduceStrLen,
                  Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
                  beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
                  Option.isSome_iff_ne_none, Option.getD_some,
                  Qed.Server.Db.some_getD_eq_self_iff,
                  Qed.QedVal.val_field, Qed.QedVal.val_ensured, Qed.Lang.QedVal.val_id,
                  true_and, and_true, false_or, or_false, true_or, or_true, id_eq, ne_eq] at *;
       try simp_all (config := { zetaDelta := true }) only [Qed.Server.qedReduceStrLen,
                          Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
                          beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
                          Option.isSome_iff_ne_none, Qed.Server.Db.some_getD_eq_self_iff,
                          true_and, and_true, false_or, or_false, true_or, or_true, id_eq, ne_eq])))
  let ok ← do
    let s ← saveState
    try
      runSimplifier
      evalTactic (← `(tactic| all_goals (try first | trivial | rfl | assumption | omega | grind | decide)))
      if (← getUnsolvedGoals).isEmpty then pure true
      else restoreState s; pure false
    catch _ =>
      restoreState s; pure false
  if !ok then
    -- Run simplifier without closing so the remaining obligation is crisp & human-readable!
    try runSimplifier catch _ => pure ()
    let gs ← getUnsolvedGoals
    let g := gs.headD (← getMainGoal)
    let cleanGoal ← g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      Qed.Diag.ppQedExpr tgt ["_row", "_old", "_new", "r"]
    throwErrorAt stx s!"Database {kindStr} failed in `{opStr}`:\n  • must prove: {cleanGoal}\n\nHint: {hintStr}"

end Qed.Server.Db
