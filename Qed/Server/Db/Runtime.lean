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

private def decodeCheckedList {Row : Type}
    (decode : DbRow → Except String Row) (check : Row → Bool) :
    List DbRow → Except ApiError (List Row)
  | [] => .ok []
  | r :: rs => do
      match decode r with
      | .error e => .error (ApiError.internal s!"database row decode failed: {e}")
      | .ok row =>
          if check row then
            let rest ← decodeCheckedList decode check rs
            return row :: rest
          else
            .error (ApiError.internal "database row violated verified table invariant or query predicate")

private theorem decodeCheckedList_sound {Row : Type}
    (decode : DbRow → Except String Row) (check : Row → Bool) :
    ∀ (raws : List DbRow) (out : List Row),
      decodeCheckedList decode check raws = .ok out →
      ∀ r ∈ out, check r = true
  | [], _, h => by
      injection h with h; subst h; intro _ hm; exact False.elim (List.not_mem_nil hm)
  | raw :: rest, _, h => by
      unfold decodeCheckedList at h
      cases hd : decode raw with
      | error _ => rw [hd] at h; contradiction
      | ok row =>
          rw [hd] at h; dsimp only at h
          cases hc : check row with
          | false => simp [hc] at h
          | true =>
              simp only [hc, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
              cases hr : decodeCheckedList decode check rest with
              | error _ => rw [hr] at h; contradiction
              | ok tl =>
                  rw [hr] at h; injection h with h; subst h
                  intro r hm
                  rcases List.mem_cons.1 hm with rfl | htl
                  · exact hc
                  · exact decodeCheckedList_sound decode check rest tl hr r htl

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
    (decodeCheckedList decode (fun r => rowInvBool r && wherePred r) dbRes.rows.toList).map List.toArray

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
    match dbRes.rows.toList with
    | [] => .ok none
    | raw :: _ =>
        match decode raw with
        | .error e => .error (ApiError.internal s!"database row decode failed: {e}")
        | .ok row =>
            if rowInvBool row && wherePred row then .ok (some row)
            else .error (ApiError.internal "database row violated verified table invariant or query predicate")

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
  return res.bind fun dbRes =>
    match dbRes.rows[0]? with
    | some row =>
        match row[0]? with
        | some v =>
            match FromSql.fromSql (α := Nat) v with
            | .ok n    => .ok n
            | .error e => .error (ApiError.internal s!"database COUNT decode failed: {e}")
        | none => .ok 0
    | none => .ok 0

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
  return res.bind fun dbRes =>
    match dbRes.rows[0]? with
    | some row =>
        match row[0]? with
        | some SqlVal.null => .ok 0
        | some v =>
            match FromSql.fromSql (α := Nat) v with
            | .ok n    => .ok n
            | .error e => .error (ApiError.internal s!"database SUM decode failed: {e}")
        | none => .ok 0
    | none => .ok 0

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
  return res.bind fun dbRes =>
    match dbRes.rows[0]? with
    | some row =>
        match row[0]? with
        | some SqlVal.null => .ok 0
        | some v =>
            match FromSql.fromSql (α := Int) v with
            | .ok n    => .ok n
            | .error e => .error (ApiError.internal s!"database SUM decode failed: {e}")
        | none => .ok 0
    | none => .ok 0

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
  return res.bind fun dbRes =>
    match dbRes.rows[0]? with
    | some row =>
        match row[0]? with
        | some SqlVal.null => .ok none
        | some v =>
            match FromSql.fromSql (α := Val) v with
            | .ok val  => .ok (some val)
            | .error e => .error (ApiError.internal s!"database aggregate decode failed: {e}")
        | none => .ok none
    | none => .ok none

private def decodeCheckedJoinList {RowL RowR : Type}
    (leftColCount : Nat)
    (decodeL : DbRow → Except String RowL)
    (decodeR : DbRow → Except String RowR)
    (check : RowL → RowR → Bool) :
    List DbRow → Except ApiError (List (RowL × RowR))
  | [] => .ok []
  | r :: rs => do
      let lRaw := r.extract 0 leftColCount
      let rRaw := r.extract leftColCount r.size
      match decodeL lRaw, decodeR rRaw with
      | .error e, _ => .error (ApiError.internal s!"database join left-row decode failed: {e}")
      | _, .error e => .error (ApiError.internal s!"database join right-row decode failed: {e}")
      | .ok rowL, .ok rowR =>
          if check rowL rowR then
            let rest ← decodeCheckedJoinList leftColCount decodeL decodeR check rs
            return (rowL, rowR) :: rest
          else
            .error (ApiError.internal "database joined row violated verified table invariant or query predicate")

private theorem decodeCheckedJoinList_sound {RowL RowR : Type}
    (leftColCount : Nat)
    (decodeL : DbRow → Except String RowL)
    (decodeR : DbRow → Except String RowR)
    (check : RowL → RowR → Bool) :
    ∀ (raws : List DbRow) (out : List (RowL × RowR)),
      decodeCheckedJoinList leftColCount decodeL decodeR check raws = .ok out →
      ∀ p ∈ out, check p.1 p.2 = true
  | [], _, h => by
      injection h with h; subst h; intro _ hm; exact False.elim (List.not_mem_nil hm)
  | raw :: rest, _, h => by
      unfold decodeCheckedJoinList at h
      dsimp only at h
      cases hdl : decodeL (raw.extract 0 leftColCount) with
      | error _ => rw [hdl] at h; contradiction
      | ok rowL =>
          rw [hdl] at h
          cases hdr : decodeR (raw.extract leftColCount raw.size) with
          | error _ => rw [hdr] at h; contradiction
          | ok rowR =>
              rw [hdr] at h; dsimp only at h
              cases hc : check rowL rowR with
              | false => simp [hc] at h
              | true =>
                  simp only [hc, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
                  cases hr : decodeCheckedJoinList leftColCount decodeL decodeR check rest with
                  | error _ => rw [hr] at h; contradiction
                  | ok tl =>
                      rw [hr] at h; injection h with h; subst h
                      intro p hm
                      rcases List.mem_cons.1 hm with rfl | htl
                      · exact hc
                      · exact decodeCheckedJoinList_sound leftColCount decodeL decodeR check rest tl hr p htl

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
    (decodeCheckedJoinList leftColCount decodeL decodeR
      (fun l r => rowInvBoolL l && wherePredL l && rowInvBoolR r && wherePredR r && (keyL l == keyR r))
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
    (decodeCheckedList decode (fun r => rowInvBool r && postPred r) dbRes.rows.toList).map List.toArray

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
    match dbRes.rows.toList with
    | [] => .ok none
    | raw :: _ =>
        match decode raw with
        | .error e => .error (ApiError.internal s!"database row decode failed: {e}")
        | .ok row =>
            if rowInvBool row && postPred row then .ok (some row)
            else .error (ApiError.internal "updated database row violated verified table invariant or postcondition")

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
    SafeIO (dbSelect (m := ThreadProg σ) cfg q decode RowInv rowInvBool hInvSound wherePred ReadPolicy ctx hPolicy txId?) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (wherePred : Row → Bool) (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r) (txId? : Option UInt64) :
    SafeIOEnsures
      (dbSelect (m := ThreadProg σ) cfg q decode RowInv rowInvBool hInvSound wherePred ReadPolicy ctx hPolicy txId?)
      (fun res => match res with | .ok rows => ∀ r ∈ rows.toList, RowInv r ∧ wherePred r = true | .error _ => True) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _
  ensures := progEnsures_execDbMaybeTx cfg q txId? _ fun res =>
    .pure _ (by
      cases res with
      | error _ => trivial
      | ok dbRes =>
          dsimp only [Except.bind, Except.map]
          cases hd : decodeCheckedList decode (fun r => rowInvBool r && wherePred r) dbRes.rows.toList with
          | error _ => trivial
          | ok out =>
              intro r hr
              have hchk := decodeCheckedList_sound decode (fun r => rowInvBool r && wherePred r)
                dbRes.rows.toList out hd r (by simpa using hr)
              simp only [Bool.and_eq_true] at hchk
              exact ⟨hInvSound r hchk.1, hchk.2⟩)

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (wherePred : Row → Bool) (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r) (txId? : Option UInt64) :
    SafeIO (dbFindOne (m := ThreadProg σ) cfg q decode RowInv rowInvBool hInvSound wherePred ReadPolicy ctx hPolicy txId?) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (wherePred : Row → Bool) (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r) (txId? : Option UInt64) :
    SafeIOEnsures
      (dbFindOne (m := ThreadProg σ) cfg q decode RowInv rowInvBool hInvSound wherePred ReadPolicy ctx hPolicy txId?)
      (fun res => ∀ r, res = .ok (some r) → RowInv r ∧ wherePred r = true) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _
  ensures := progEnsures_execDbMaybeTx cfg q txId? _ fun res =>
    .pure _ (by
      intro r hr
      cases res with
      | error _ => simp [Except.bind] at hr
      | ok dbRes =>
          dsimp only [Except.bind] at hr
          cases hlist : dbRes.rows.toList with
          | nil => rw [hlist] at hr; simp at hr
          | cons raw _ =>
              rw [hlist] at hr; dsimp only at hr
              cases hd : decode raw with
              | error _ => rw [hd] at hr; simp at hr
              | ok row =>
                  rw [hd] at hr; dsimp only at hr
                  cases hchk : (rowInvBool row && wherePred row) with
                  | false => rw [hchk] at hr; simp at hr
                  | true =>
                      rw [hchk] at hr
                      simp only [↓reduceIte, Except.ok.injEq, Option.some.injEq] at hr
                      subst hr
                      simp only [Bool.and_eq_true] at hchk
                      exact ⟨hInvSound row hchk.1, hchk.2⟩)

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
    SafeIO (dbJoinSelect (m := ThreadProg σ) cfg q leftColCount decodeL decodeR
      RowInvL rowInvBoolL hInvSoundL RowInvR rowInvBoolR hInvSoundR
      wherePredL wherePredR keyL keyR ReadPolicyL ReadPolicyR ctx hPolicyL hPolicyR txId?) where
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
  ensures := progEnsures_execDbMaybeTx cfg q txId? _ fun res =>
    .pure _ (by
      cases res with
      | error _ => trivial
      | ok dbRes =>
          dsimp only [Except.bind, Except.map]
          cases hd : decodeCheckedJoinList leftColCount decodeL decodeR
              (fun l r => rowInvBoolL l && wherePredL l && rowInvBoolR r && wherePredR r && (keyL l == keyR r))
              dbRes.rows.toList with
          | error _ => trivial
          | ok out =>
              intro p hp
              have hchk := decodeCheckedJoinList_sound leftColCount decodeL decodeR
                (fun l r => rowInvBoolL l && wherePredL l && rowInvBoolR r && wherePredR r && (keyL l == keyR r))
                dbRes.rows.toList out hd p (by simpa using hp)
              simp only [Bool.and_eq_true] at hchk
              exact ⟨hInvSoundL p.1 hchk.1.1.1.1, hchk.1.1.1.2, hInvSoundR p.2 hchk.1.1.2, hchk.1.2⟩)

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery) (newRow : Row)
    (RowInv : Row → Prop) (InsertPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hInv : RowInv newRow) (hPolicy : InsertPolicy ctx newRow) (txId? : Option UInt64) :
    SafeIO (dbInsert (m := ThreadProg σ) cfg q newRow RowInv InsertPolicy ctx hInv hPolicy txId?) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _

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
    SafeIO (dbUpdate (m := ThreadProg σ) cfg q decode RowInv rowInvBool hInvSound TransInv
      wherePred setFn postPred UpdatePolicy ctx hPO hPN hIP hTr txId?) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _

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
  ensures := progEnsures_execDbMaybeTx cfg q txId? _ fun res =>
    .pure _ (by
      cases res with
      | error _ => trivial
      | ok dbRes =>
          dsimp only [Except.bind, Except.map]
          cases hd : decodeCheckedList decode (fun r => rowInvBool r && postPred r) dbRes.rows.toList with
          | error _ => trivial
          | ok out =>
              intro r hr
              have hchk := decodeCheckedList_sound decode (fun r => rowInvBool r && postPred r)
                dbRes.rows.toList out hd r (by simpa using hr)
              simp only [Bool.and_eq_true] at hchk
              exact ⟨hInvSound r hchk.1, hchk.2⟩)

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (TransInv : Row → Row → Prop) (wherePred : Row → Bool) (setFn : Row → Row) (postPred : Row → Bool)
    (UpdatePolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPO : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx r)
    (hPN : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx (setFn r))
    (hIP : ∀ r, RowInv r → wherePred r = true → RowInv (setFn r))
    (hTr : ∀ r, RowInv r → wherePred r = true → TransInv r (setFn r)) (txId? : Option UInt64) :
    SafeIO (dbUpdateOne (m := ThreadProg σ) cfg q decode RowInv rowInvBool hInvSound TransInv
      wherePred setFn postPred UpdatePolicy ctx hPO hPN hIP hTr txId?) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _

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
  ensures := progEnsures_execDbMaybeTx cfg q txId? _ fun res =>
    .pure _ (by
      intro r hr
      cases res with
      | error _ => simp [Except.bind] at hr
      | ok dbRes =>
          dsimp only [Except.bind] at hr
          cases hlist : dbRes.rows.toList with
          | nil => rw [hlist] at hr; simp at hr
          | cons raw _ =>
              rw [hlist] at hr; dsimp only at hr
              cases hd : decode raw with
              | error _ => rw [hd] at hr; simp at hr
              | ok row =>
                  rw [hd] at hr; dsimp only at hr
                  cases hchk : (rowInvBool row && postPred row) with
                  | false => rw [hchk] at hr; simp at hr
                  | true =>
                      rw [hchk] at hr
                      simp only [↓reduceIte, Except.ok.injEq, Option.some.injEq] at hr
                      subst hr
                      simp only [Bool.and_eq_true] at hchk
                      exact ⟨hInvSound row hchk.1, hchk.2⟩)

instance {σ Row : Type} (cfg : DbConfig) (q : SqlQuery)
    (RowInv : Row → Prop) (wherePred : Row → Bool)
    (DeletePolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → DeletePolicy ctx r) (txId? : Option UInt64) :
    SafeIO (dbDelete (m := ThreadProg σ) cfg q RowInv wherePred DeletePolicy ctx hPolicy txId?) where
  noAtomic := noAtomic_execDbMaybeTx cfg q txId? _ fun _ => .pure _

theorem some_getD_eq_self_iff {α : Type} (o : Option α) (d : α) :
    some (o.getD d) = o ↔ o ≠ none := by
  cases o <;> simp

/-! ## Dedicated Database Policy & Invariant Proof Tactic (`qedDbProve`) -/

open Lean Meta in
private def mkDbCharListExpr (s : String) : Expr :=
  let charTy := mkConst ``Char
  let nilE := mkApp (mkConst ``List.nil [0]) charTy
  let consC := mkApp (mkConst ``List.cons [0]) charTy
  s.toList.foldr (fun c acc => mkApp2 consC (mkApp (mkConst ``Char.ofNat) (mkNatLit c.toNat)) acc) nilE

open Lean Meta in
simproc_decl qedDbReduceStrLen (String.length _) := fun e => do
  let some (Expr.lit (Literal.strVal s)) := e.getAppArgs[0]? | return .continue
  let cs := mkDbCharListExpr s
  let nExpr := mkNatLit s.length
  let prf ← mkEqTrans (mkApp (mkConst ``String.length_ofList) cs) (← mkEqRefl nExpr)
  return .done { expr := nExpr, proof? := some prf }

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
       try simp (config := { zetaDelta := true }) only [$[$unfoldIds:ident],*, Qed.Server.Db.qedDbReduceStrLen,
                  Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
                  beq_iff_eq, bne_iff_ne, decide_eq_true_eq,
                  Option.isSome_iff_ne_none, Option.getD_some,
                  Qed.Server.Db.some_getD_eq_self_iff,
                  Qed.QedVal.val_field, Qed.QedVal.val_ensured, Qed.Lang.QedVal.val_id,
                  true_and, and_true, false_or, or_false, true_or, or_true, id_eq, ne_eq] at *;
       try simp_all (config := { zetaDelta := true }) only [Qed.Server.Db.qedDbReduceStrLen,
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
