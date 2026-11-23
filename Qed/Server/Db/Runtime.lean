import Lean
import Qed.Field
import Qed.Diag
import Qed.Server.Core
import Qed.Server.Registry
import Qed.Server.Db.Core
import Qed.Verify.Core

namespace Qed.Server.Db

instance {α : Type} {p : α → Prop} [ToSql α] : ToSql (Qed.Field p) := ⟨fun f => ToSql.toSql f.val⟩
instance {α : Type} {p : α → Prop} [FromSql α] [DecidablePred p] : FromSql (Qed.Field p) where
  fromSql v := do
    let a ← FromSql.fromSql (α := α) v
    if h : p a then .ok ⟨a, h⟩ else .error "database column value violated table `where` constraint"

/-! ## Generic Zero-Trust Proof-Checked Database Operations -/

private def decodeRowErr {Row : Type} (decode : DbRow → Except String Row) (r : DbRow) : Except ApiError Row :=
  (decode r).mapError fun e => ApiError.internal s!"database row decode failed: {e}"

private def decodeJoinRowErr {RowL RowR : Type} (leftColCount : Nat)
    (decodeL : DbRow → Except String RowL) (decodeR : DbRow → Except String RowR) (r : DbRow) : Except ApiError (RowL × RowR) :=
  match decodeL (r.extract 0 leftColCount), decodeR (r.extract leftColCount r.size) with
  | .error e, _ => .error (ApiError.internal s!"database join left-row decode failed: {e}")
  | _, .error e => .error (ApiError.internal s!"database join right-row decode failed: {e}")
  | .ok l, .ok r => .ok (l, r)

private def decodeCheckedList {Row : Type} (decode : DbRow → Except ApiError Row) (check : Row → Bool) (errMsg : String) :
    List DbRow → Except ApiError (List Row)
  | [] => .ok []
  | r :: rs => do let row ← decode r; if check row then return row :: (← decodeCheckedList decode check errMsg rs) else .error (ApiError.internal errMsg)

private theorem decodeCheckedList_sound {Row : Type} (decode : DbRow → Except ApiError Row) (check : Row → Bool) (errMsg : String) :
    ∀ (raws : List DbRow) (out : List Row), decodeCheckedList decode check errMsg raws = .ok out → ∀ r ∈ out, check r = true
  | [], _, h => by cases h; intro _ hm; nomatch hm
  | raw :: rest, _, h => by
      simp only [decodeCheckedList, bind, Except.bind, pure, Except.pure] at h
      cases hd : decode raw <;> rw [hd] at h <;> try cases h
      rename_i row
      cases hc : check row <;> simp only [hc, ↓reduceIte, Bool.false_eq_true] at h <;> try cases h
      cases hr : decodeCheckedList decode check errMsg rest <;> rw [hr] at h <;> try cases h
      rename_i tl
      exact fun r hm => (List.mem_cons.1 hm).elim (· ▸ hc) (decodeCheckedList_sound decode check errMsg rest tl hr r)

private def decodeFirstCell {α β : Type} [FromSql α] (wrap : α → β) (nullAs : Option β) (emptyVal : β) (label : String) (dbRes : DbResult) : Except ApiError β :=
  match dbRes.rows[0]?.bind (·[0]?) with
  | none => .ok emptyVal
  | some v => match nullAs, v with
      | some d, .null => .ok d
      | _, _ => ((FromSql.fromSql (α := α) v).map wrap).mapError fun e => ApiError.internal s!"database {label} decode failed: {e}"

@[inline, specialize]
def execDbMaybeTx {m : Type → Type} [MonadServer m] (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64 := none) : m (Except ApiError DbResult) :=
  match txId? with | some tid => MonadServer.dbTxExec cfg tid q | none => MonadServer.dbExec cfg q

private theorem progSpec_execDbMaybeTx {σ β : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop} {Post : β → Prop}
    (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64) (k : Except ApiError DbResult → ThreadProg σ β)
    (hk : ∀ r, ProgSpec Inv A Step Post (k r)) : ProgSpec Inv A Step Post (execDbMaybeTx (m := ThreadProg σ) cfg q txId? >>= k) := by
  cases txId? with | none => exact .io (.dbExec cfg q) k hk | some tid => exact .io (.dbTxExec cfg tid q) k hk

private abbrev dbArrPost {Row : Type} (P : Row → Prop) : Except ApiError (Array Row) → Prop
  | .ok rows => ∀ r ∈ rows.toList, P r | .error _ => True

private def decodeCheckedArr {Row : Type} (decode : DbRow → Except ApiError Row) (check : Row → Bool) (errMsg : String) (dbRes : DbResult) : Except ApiError (Array Row) :=
  (decodeCheckedList decode check errMsg dbRes.rows.toList).map List.toArray

private def decodeCheckedOne {Row : Type} (decode : DbRow → Except String Row) (check : Row → Bool) (errMsg : String) (dbRes : DbResult) : Except ApiError (Option Row) :=
  (decodeCheckedList (decodeRowErr decode) check errMsg (dbRes.rows.toList.take 1)).map List.head?

private theorem decodeCheckedArr_post {Row : Type} (decode : DbRow → Except ApiError Row) (check : Row → Bool) (errMsg : String)
    {P : Row → Prop} (hP : ∀ r, check r = true → P r) (dbRes : DbResult) : dbArrPost P (decodeCheckedArr decode check errMsg dbRes) := by
  unfold dbArrPost decodeCheckedArr; dsimp only [Except.map]
  cases hd : decodeCheckedList decode check errMsg dbRes.rows.toList with
  | error _ => trivial
  | ok out => exact fun r hr => hP r (decodeCheckedList_sound decode check errMsg _ out hd r (by simpa using hr))

private theorem decodeCheckedOne_post {Row : Type} (decode : DbRow → Except String Row) (check : Row → Bool) (errMsg : String)
    {P : Row → Prop} (hP : ∀ r, check r = true → P r) (dbRes : DbResult) :
    ∀ r, decodeCheckedOne decode check errMsg dbRes = .ok (some r) → P r := by
  intro r h; unfold decodeCheckedOne at h; dsimp only [Except.map] at h
  cases hd : decodeCheckedList (decodeRowErr decode) check errMsg (dbRes.rows.toList.take 1) with
  | error _ => rw [hd] at h; cases h
  | ok out => rw [hd] at h; injection h with hh; exact hP r (decodeCheckedList_sound _ _ _ _ out hd r (List.mem_of_head? hh))

@[inline, specialize]
def dbRunChecked {α : Type} {P : Prop} {Q : Except ApiError α → Prop} {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64) (post : DbResult → Except ApiError α)
    (_hPost : ∀ r, Q (post r)) (_hErr : ∀ e, Q (.error e)) (_pf : P) : m (Except ApiError α) := do
  return (← execDbMaybeTx cfg q txId?).bind post

abbrev dbRun {α : Type} {P : Prop} {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64) (post : DbResult → Except ApiError α) (pf : P) : m (Except ApiError α) :=
  dbRunChecked (Q := fun _ => True) cfg q txId? post (fun _ => trivial) (fun _ => trivial) pf

instance {σ α : Type} {P : Prop} {Q : Except ApiError α → Prop}
    (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64)
    (post : DbResult → Except ApiError α) (hPost : ∀ r, Q (post r)) (hErr : ∀ e, Q (.error e)) (pf : P) :
    SafeIOEnsures (dbRunChecked (Q := Q) (m := ThreadProg σ) cfg q txId? post hPost hErr pf) Q where
  noAtomic := progSpec_execDbMaybeTx cfg q txId? _ fun _ => .pure _ trivial
  ensures := progSpec_execDbMaybeTx cfg q txId? _ fun res => .pure _ (by cases res with | error e => exact hErr e | ok r => exact hPost r)

private theorem and_inv_pred {Row : Type} {RowInv : Row → Prop} {rowInvBool pred : Row → Bool}
    (hInvSound : ∀ r, rowInvBool r = true → RowInv r) (r : Row) (h : (rowInvBool r && pred r) = true) :
    RowInv r ∧ pred r = true := by simp only [Bool.and_eq_true] at h; exact ⟨hInvSound r h.1, h.2⟩

private abbrev DbRowRunner (Row Res : Type) (m : Type → Type) :=
  ∀ {P : Prop}, DbConfig → SqlQuery → (DbRow → Except String Row) → (RowInv : Row → Prop) → (rowInvBool : Row → Bool) →
    (∀ r, rowInvBool r = true → RowInv r) → (Row → Bool) → String → P → Option UInt64 → m (Except ApiError Res)

section DbOps
variable {Row : Type} {m : Type → Type} [Monad m] [MonadServer m]

private abbrev dbPolicyRun {α : Type} (post : DbResult → Except ApiError α) (cfg : DbConfig) (q : SqlQuery)
    (RowInv : Row → Prop) (wherePred : Row → Bool) (Policy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → Policy ctx r) (txId? : Option UInt64 := none) : m (Except ApiError α) :=
  dbRun cfg q txId? post hPolicy

private abbrev dbRunRows {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (pred : Row → Bool) (errMsg : String) (pf : P) (txId? : Option UInt64) : m (Except ApiError (Array Row)) :=
  dbRunChecked (Q := dbArrPost fun r => RowInv r ∧ pred r = true) cfg q txId?
    (decodeCheckedArr (decodeRowErr decode) (fun r => rowInvBool r && pred r) errMsg)
    (decodeCheckedArr_post _ _ _ (and_inv_pred hInvSound)) (fun _ => trivial) pf

private abbrev dbRunOneRow {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (pred : Row → Bool) (errMsg : String) (pf : P) (txId? : Option UInt64) : m (Except ApiError (Option Row)) :=
  dbRunChecked (Q := fun res => ∀ r, res = .ok (some r) → RowInv r ∧ pred r = true) cfg q txId?
    (decodeCheckedOne decode (fun r => rowInvBool r && pred r) errMsg)
    (decodeCheckedOne_post _ _ _ (and_inv_pred hInvSound)) (fun _ _ h => nomatch h) pf

private abbrev dbSelectRun {Res : Type} (run : DbRowRunner Row Res m) (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (wherePred : Row → Bool) (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r) (txId? : Option UInt64 := none) : m (Except ApiError Res) :=
  run cfg q decode RowInv rowInvBool hInvSound wherePred "database row violated verified table invariant or query predicate" hPolicy txId?

private abbrev dbUpdateRun {Res : Type} (errMsg : String) (run : DbRowRunner Row Res m) (cfg : DbConfig) (q : SqlQuery)
    (decode : DbRow → Except String Row) (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (TransInv : Row → Row → Prop) (wherePred : Row → Bool) (setFn : Row → Row) (postPred : Row → Bool)
    (UpdatePolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicyOld : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx r) (hPolicyNew : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx (setFn r))
    (hInvPres : ∀ r, RowInv r → wherePred r = true → RowInv (setFn r)) (hTrans : ∀ r, RowInv r → wherePred r = true → TransInv r (setFn r))
    (txId? : Option UInt64 := none) : m (Except ApiError Res) :=
  run cfg q decode RowInv rowInvBool hInvSound postPred errMsg (And.intro hPolicyOld (And.intro hPolicyNew (And.intro hInvPres hTrans))) txId?

abbrev dbSelect := @dbSelectRun Row m (Array Row) (fun {_} => @dbRunRows Row m _ _ _)
abbrev dbFindOne := @dbSelectRun Row m (Option Row) (fun {_} => @dbRunOneRow Row m _ _ _)
abbrev dbCount := @dbPolicyRun Row m _ _ Nat (decodeFirstCell (α := Nat) id none 0 "COUNT")
abbrev dbSumNat := @dbPolicyRun Row m _ _ Nat (decodeFirstCell (α := Nat) id (some 0) 0 "SUM")
abbrev dbSumInt := @dbPolicyRun Row m _ _ Int (decodeFirstCell (α := Int) id (some 0) 0 "SUM")
abbrev dbUpdate := @dbUpdateRun Row m (Array Row) "database row violated verified table invariant or query predicate" (fun {_} => @dbRunRows Row m _ _ _)
abbrev dbUpdateOne := @dbUpdateRun Row m (Option Row) "updated database row violated verified table invariant or postcondition" (fun {_} => @dbRunOneRow Row m _ _ _)
abbrev dbDelete := @dbPolicyRun Row m _ _ Nat (fun dbRes => .ok dbRes.affected)

abbrev dbInsert (cfg : DbConfig) (q : SqlQuery) (newRow : Row) (RowInv : Row → Prop) (InsertPolicy : RequestCtx → Row → Prop)
    (ctx : RequestCtx) (hInv : RowInv newRow) (hPolicy : InsertPolicy ctx newRow) (txId? : Option UInt64 := none) : m (Except ApiError Row) :=
  dbRunChecked (Q := fun res => match res with | .ok r => r = newRow ∧ RowInv r | .error _ => True)
    cfg q txId? (fun _ => .ok newRow) (fun _ => ⟨rfl, hInv⟩) (fun _ => trivial) hPolicy

end DbOps

abbrev dbAggOpt {Row Val : Type} [FromSql Val] {m : Type → Type} [Monad m] [MonadServer m] (cfg : DbConfig) (q : SqlQuery) (_proj : Row → Val) :=
  @dbPolicyRun Row m _ _ (Option Val) (decodeFirstCell (α := Val) some (some none) none "aggregate") cfg q

abbrev dbJoinSelect {RowL RowR Key : Type} [BEq Key] {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery) (leftColCount : Nat)
    (decodeL : DbRow → Except String RowL) (decodeR : DbRow → Except String RowR)
    (RowInvL : RowL → Prop) (rowInvBoolL : RowL → Bool) (hInvSoundL : ∀ r, rowInvBoolL r = true → RowInvL r)
    (RowInvR : RowR → Prop) (rowInvBoolR : RowR → Bool) (hInvSoundR : ∀ r, rowInvBoolR r = true → RowInvR r)
    (wherePredL : RowL → Bool) (wherePredR : RowR → Bool) (keyL : RowL → Key) (keyR : RowR → Key)
    (ReadPolicyL : RequestCtx → RowL → Prop) (ReadPolicyR : RequestCtx → RowR → Prop) (ctx : RequestCtx)
    (hPolicyL : ∀ r, RowInvL r → wherePredL r = true → ReadPolicyL ctx r)
    (hPolicyR : ∀ r, RowInvR r → wherePredR r = true → ReadPolicyR ctx r)
    (txId? : Option UInt64 := none) : m (Except ApiError (Array (RowL × RowR))) :=
  dbRunChecked (Q := dbArrPost fun p => RowInvL p.1 ∧ wherePredL p.1 = true ∧ RowInvR p.2 ∧ wherePredR p.2 = true) cfg q txId?
    (decodeCheckedArr (decodeJoinRowErr leftColCount decodeL decodeR)
      (fun p => rowInvBoolL p.1 && wherePredL p.1 && rowInvBoolR p.2 && wherePredR p.2 && (keyL p.1 == keyR p.2))
      "database joined row violated verified table invariant or query predicate")
    (decodeCheckedArr_post _ _ _ fun p h => by
      simp only [Bool.and_eq_true] at h; exact ⟨hInvSoundL p.1 h.1.1.1.1, h.1.1.1.2, hInvSoundR p.2 h.1.1.2, h.1.2⟩)
    (fun _ => trivial) (And.intro hPolicyL hPolicyR)

theorem some_getD_eq_self_iff {α : Type} (o : Option α) (d : α) : some (o.getD d) = o ↔ o ≠ none := by cases o <;> simp

open Lean Elab Command in
def mkSqlIdentTerm (ref : Syntax) (raw : String) : CommandElabM Term := do
  if !isSafeSqlIdent raw then
    throwErrorAt ref s!"invalid SQL identifier `{raw}` (must start with an ASCII letter or `_` and contain only ASCII letters, digits, and `_`, max 63 chars)"
  `(Qed.Server.Db.SqlIdent.mk $(Syntax.mkStrLit raw) (by decide))

syntax (name := qedDbProveTac) "qedDbProve" "[" ident,* "]" str str str : tactic

open Lean Meta Elab Tactic in
@[tactic qedDbProveTac]
def elabQedDbProve : Tactic := fun stx => do
  let unfoldNames ← (stx.getArg 2).getSepArgs.mapM resolveGlobalConstNoOverload
  if !(← Qed.Verify.Core.solveWithUnfolds unfoldNames (Qed.Verify.Core.dbBaseSimpNames.push ``eq_self) #[``Qed.Server.qedReduceStrLen]) then
    Qed.Diag.throwUnsolvedGoals
      m!"Database {(⟨stx.getArg 4⟩ : TSyntax `str).getString} failed in `{(⟨stx.getArg 5⟩ : TSyntax `str).getString}`:"
      m!"\n\nHint: {(⟨stx.getArg 6⟩ : TSyntax `str).getString}"
      (ref? := some stx) (stripPrefixes := ["_row", "_old", "_new", "r"]) (bulletPrefix := "  • must prove: ")
      (goals? := some [(← getUnsolvedGoals).headD (← getMainGoal)])

end Qed.Server.Db
