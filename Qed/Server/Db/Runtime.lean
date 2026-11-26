import Lean
import Qed.Base64
import Qed.Diag
import Qed.Server.Core
import Qed.Server.Registry
import Qed.Server.Db.Core
import Qed.Verify.Core

namespace Qed.Server.Db

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

/-! ## Transparent AES-256-GCM Encryption & Decryption for `encrypted(...)` Columns -/

section DbEnc
variable {m : Type → Type} [Monad m] [MonadServer m]

private def dbEncryptVal (spec : EncColSpec) : SqlVal → m (Except ApiError SqlVal)
  | .null => pure (.ok .null)
  | .text s => (·.map fun ct => .text (Qed.Base64.encode ct)) <$> MonadServer.aeadEncrypt spec.keyEnv spec.fallback? spec.aad s.toUTF8
  | .bytes bs => (·.map fun ct => .text (Qed.Base64.encode ct)) <$> MonadServer.aeadEncrypt spec.keyEnv spec.fallback? spec.aad bs
  | _ => pure (.error (ApiError.internal "encrypted database column expects TEXT, BLOB, or NULL"))

private def dbDecryptTryPrev (aad : ByteArray) (raw : ByteArray) (origErr : ApiError) :
    List (String × Option String) → m (Except ApiError ByteArray)
  | [] => pure (.error origErr)
  | (kEnv, fb?) :: rest =>
      MonadServer.readEnv kEnv >>= fun envOpt =>
        let hasKey := envOpt.any (!·.isEmpty) || fb?.any (!·.isEmpty)
        if !hasKey then dbDecryptTryPrev aad raw origErr rest
        else MonadServer.aeadDecrypt kEnv fb? aad raw >>= fun
          | .ok pt => pure (.ok pt)
          | .error _ => dbDecryptTryPrev aad raw origErr rest

private def finishDecryptVal (isBytes : Bool) (res : Except ApiError ByteArray) : Except ApiError SqlVal :=
  res.bind fun pt =>
    if isBytes then .ok (.bytes pt)
    else match String.fromUTF8? pt with
      | some s => .ok (.text s)
      | none => .error (ApiError.internal "decrypted database column is not valid UTF-8")

private def dbDecryptVal (spec : EncColSpec) : SqlVal → m (Except ApiError SqlVal)
  | .null => pure (.ok .null)
  | .text b64 =>
      match Qed.Base64.decode b64 with
      | .error e => pure (.error (ApiError.internal s!"encrypted column base64 decode failed: {e}"))
      | .ok raw =>
          MonadServer.aeadDecrypt spec.keyEnv spec.fallback? spec.aad raw >>= fun
            | .ok pt => pure (finishDecryptVal spec.isBytes (.ok pt))
            | .error err =>
                if spec.prevKeys.isEmpty || err.message.startsWith "missing required encryption key" then
                  pure (.error err)
                else finishDecryptVal spec.isBytes <$> dbDecryptTryPrev spec.aad raw err spec.prevKeys
  | _ => pure (.error (ApiError.internal "encrypted database column stored value must be TEXT or NULL"))

private def mapExceptList {α β : Type} (f : α → m (Except ApiError β)) : List α → m (Except ApiError (List β))
  | [] => pure (.ok [])
  | x :: xs => f x >>= fun | .error e => pure (.error e) | .ok y => (·.map (y :: ·)) <$> mapExceptList f xs

def dbEncryptQuery (encWrite : List (String × EncColSpec)) (q : SqlQuery) : m (Except ApiError SqlQuery) :=
  let encCols (cols : List (SqlIdent × SqlVal)) := mapExceptList (fun (c, v) =>
    match encWrite.lookup c.raw with | some spec => (·.map (c, ·)) <$> dbEncryptVal spec v | none => pure (.ok (c, v))) cols
  if encWrite.isEmpty then pure (.ok q)
  else match q with
    | .insert tbl cols ret => (·.map fun cs => .insert tbl cs ret) <$> encCols cols
    | .insertOrIgnore tbl cols cc ret => (·.map fun cs => .insertOrIgnore tbl cs cc ret) <$> encCols cols
    | .upsert tbl cols cc uc cw ret => (·.map fun cs => .upsert tbl cs cc uc cw ret) <$> encCols cols
    | .update tbl sets w ret =>
        (·.map fun ss => .update tbl ss w ret) <$> mapExceptList (fun (c, e) =>
          match encWrite.lookup c.raw, e with
          | some spec, .param v => (·.map fun ev => (c, .param ev)) <$> dbEncryptVal spec v
          | some _, _ => pure (.error (ApiError.internal s!"cannot encrypt non-parameter SQL expression for column `{c.raw}`"))
          | none, _ => pure (.ok (c, e))) sets
    | _ => pure (.ok q)

private def dbDecryptRow : List (Nat × EncColSpec) → DbRow → m (Except ApiError DbRow)
  | [], row => pure (.ok row)
  | (idx, spec) :: rest, row =>
      if h : idx < row.size then
        dbDecryptVal spec row[idx] >>= fun | .error e => pure (.error e) | .ok dv => dbDecryptRow rest (row.set idx dv h)
      else pure (.error (ApiError.internal s!"encrypted column index {idx} out of bounds"))

def dbDecryptResult (encRead : List (Nat × EncColSpec)) (res : DbResult) : m (Except ApiError DbResult) :=
  if encRead.isEmpty then pure (.ok res)
  else (·.map fun rs => { res with rows := rs.toArray }) <$> mapExceptList (dbDecryptRow encRead) res.rows.toList

end DbEnc

section DbEncProofs
variable {σ : Type}

private theorem noAtomic_map {α β : Type} (f : α → β) {p : ThreadProg σ α} (hp : NoAtomic p) : NoAtomic (f <$> p) := by
  change NoAtomic (p >>= fun a => .pure (f a)); exact hp.bind fun _ _ => NoAtomic.pure _

private theorem noAtomic_mapExceptList {α β : Type} (f : α → ThreadProg σ (Except ApiError β))
    (hf : ∀ x, NoAtomic (f x)) : ∀ xs, NoAtomic (mapExceptList f xs)
  | [] => NoAtomic.pure _
  | x :: xs => (hf x).bind fun | .error _, _ => NoAtomic.pure _ | .ok _, _ => noAtomic_map _ (noAtomic_mapExceptList f hf xs)

private theorem noAtomic_dbEncryptVal (spec : EncColSpec) (v : SqlVal) : NoAtomic (dbEncryptVal (m := ThreadProg σ) spec v) := by
  cases v <;> first | exact NoAtomic.pure _ | exact noAtomic_map _ (NoAtomic.io _ _ fun _ => NoAtomic.pure _)

private theorem noAtomic_dbDecryptTryPrev (aad raw : ByteArray) (origErr : ApiError) :
    ∀ ks : List (String × Option String), NoAtomic (dbDecryptTryPrev (m := ThreadProg σ) aad raw origErr ks)
  | [] => NoAtomic.pure _
  | (kEnv, fb?) :: rest =>
      (NoAtomic.io (.readEnv kEnv) _ NoAtomic.pure).bind fun _ _ => by
        dsimp only; split
        · exact noAtomic_dbDecryptTryPrev aad raw origErr rest
        · exact (NoAtomic.io (.aeadDecrypt kEnv fb? aad raw) _ NoAtomic.pure).bind fun
            | .ok _, _ => NoAtomic.pure _
            | .error _, _ => noAtomic_dbDecryptTryPrev aad raw origErr rest

private theorem noAtomic_dbDecryptVal (spec : EncColSpec) (v : SqlVal) : NoAtomic (dbDecryptVal (m := ThreadProg σ) spec v) := by
  cases v <;> try exact NoAtomic.pure _
  dsimp only [dbDecryptVal]
  cases Qed.Base64.decode _ with
  | error _ => exact NoAtomic.pure _
  | ok raw =>
      exact (NoAtomic.io (.aeadDecrypt spec.keyEnv spec.fallback? spec.aad raw) _ NoAtomic.pure).bind fun
        | .ok _, _ => NoAtomic.pure _
        | .error err, _ => by
            dsimp only; split
            · exact NoAtomic.pure _
            · exact noAtomic_map _ (noAtomic_dbDecryptTryPrev spec.aad raw err spec.prevKeys)

private theorem noAtomic_dbEncryptQuery (encWrite : List (String × EncColSpec)) (q : SqlQuery) :
    NoAtomic (dbEncryptQuery (m := ThreadProg σ) encWrite q) := by
  unfold dbEncryptQuery; split
  · exact NoAtomic.pure _
  · cases q with
    | insert _ cols _ | insertOrIgnore _ cols _ _ | upsert _ cols _ _ _ _ =>
        exact noAtomic_map _ (noAtomic_mapExceptList _ (fun (c, v) => by
          dsimp only; cases encWrite.lookup c.raw with
          | none => exact NoAtomic.pure _ | some spec => exact noAtomic_map _ (noAtomic_dbEncryptVal spec v)) cols)
    | update _ sets _ _ =>
        exact noAtomic_map _ (noAtomic_mapExceptList _ (fun (c, e) => by
          dsimp only; cases encWrite.lookup c.raw with
          | none => exact NoAtomic.pure _
          | some spec => cases e <;> first | exact NoAtomic.pure _ | exact noAtomic_map _ (noAtomic_dbEncryptVal spec _)) sets)
    | _ => exact NoAtomic.pure _

private theorem noAtomic_dbDecryptRow :
    ∀ (encRead : List (Nat × EncColSpec)) (row : DbRow), NoAtomic (dbDecryptRow (m := ThreadProg σ) encRead row)
  | [], _ => NoAtomic.pure _
  | (_, spec) :: rest, _ => by
      dsimp only [dbDecryptRow]; split
      · exact (noAtomic_dbDecryptVal spec _).bind fun | .error _, _ => NoAtomic.pure _ | .ok _, _ => noAtomic_dbDecryptRow rest _
      · exact NoAtomic.pure _

private theorem noAtomic_dbDecryptResult (encRead : List (Nat × EncColSpec)) (res : DbResult) :
    NoAtomic (dbDecryptResult (m := ThreadProg σ) encRead res) := by
  unfold dbDecryptResult; split
  · exact NoAtomic.pure _
  · exact noAtomic_map _ (noAtomic_mapExceptList _ (noAtomic_dbDecryptRow encRead) _)

end DbEncProofs

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
    (_hPost : ∀ r, Q (post r)) (_hErr : ∀ e, Q (.error e)) (_pf : P)
    (encWrite : List (String × EncColSpec) := []) (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError α) :=
  dbEncryptQuery encWrite q >>= fun
  | .error e => pure (.error e)
  | .ok q' =>
      execDbMaybeTx cfg q' txId? >>= fun
      | .error e => pure (.error e)
      | .ok rawRes =>
          dbDecryptResult encRead rawRes >>= fun
          | .error e => pure (.error e)
          | .ok decRes => pure (post decRes)

abbrev dbRun {α : Type} {P : Prop} {m : Type → Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64) (post : DbResult → Except ApiError α) (pf : P) : m (Except ApiError α) :=
  dbRunChecked (Q := fun _ => True) cfg q txId? post (fun _ => trivial) (fun _ => trivial) pf

private theorem progSpec_dbRunChecked {σ α : Type} {P : Prop} {Q Post : Except ApiError α → Prop}
    {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop}
    (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64)
    (post : DbResult → Except ApiError α) (hQPost : ∀ r, Q (post r)) (hQErr : ∀ e, Q (.error e)) (pf : P)
    (encWrite : List (String × EncColSpec)) (encRead : List (Nat × EncColSpec))
    (hPost : ∀ r, Post (post r)) (hErr : ∀ e, Post (.error e)) :
    ProgSpec Inv A Step Post (dbRunChecked (Q := Q) (m := ThreadProg σ) cfg q txId? post hQPost hQErr pf encWrite encRead) :=
  (ProgSpec.of_noAtomic (noAtomic_dbEncryptQuery encWrite q)).bind fun
    | .error e, _ => .pure _ (hErr e)
    | .ok q', _ => progSpec_execDbMaybeTx cfg q' txId? _ fun
        | .error e => .pure _ (hErr e)
        | .ok raw => (ProgSpec.of_noAtomic (noAtomic_dbDecryptResult encRead raw)).bind fun
            | .error e, _ => .pure _ (hErr e)
            | .ok dec, _ => .pure _ (hPost dec)

instance {σ α : Type} {P : Prop} {Q : Except ApiError α → Prop}
    (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64)
    (post : DbResult → Except ApiError α) (hPost : ∀ r, Q (post r)) (hErr : ∀ e, Q (.error e)) (pf : P)
    (encWrite : List (String × EncColSpec)) (encRead : List (Nat × EncColSpec)) :
    SafeIOEnsures (dbRunChecked (Q := Q) (m := ThreadProg σ) cfg q txId? post hPost hErr pf encWrite encRead) Q where
  noAtomic := progSpec_dbRunChecked cfg q txId? post hPost hErr pf encWrite encRead (fun _ => trivial) (fun _ => trivial)
  ensures := progSpec_dbRunChecked cfg q txId? post hPost hErr pf encWrite encRead hPost hErr

private theorem and_inv_pred {Row : Type} {RowInv : Row → Prop} {rowInvBool pred : Row → Bool}
    (hInvSound : ∀ r, rowInvBool r = true → RowInv r) (r : Row) (h : (rowInvBool r && pred r) = true) :
    RowInv r ∧ pred r = true := by simp only [Bool.and_eq_true] at h; exact ⟨hInvSound r h.1, h.2⟩

private abbrev DbRowRunner (Row Res : Type) (m : Type → Type) :=
  ∀ {P : Prop}, DbConfig → SqlQuery → (DbRow → Except String Row) → (RowInv : Row → Prop) → (rowInvBool : Row → Bool) →
    (∀ r, rowInvBool r = true → RowInv r) → (Row → Bool) → String → P → Option UInt64 →
    List (String × EncColSpec) → List (Nat × EncColSpec) → m (Except ApiError Res)

section DbOps
variable {Row : Type} {m : Type → Type} [Monad m] [MonadServer m]

private abbrev dbPolicyRun {α : Type} (post : DbResult → Except ApiError α) (cfg : DbConfig) (q : SqlQuery)
    (RowInv : Row → Prop) (wherePred : Row → Bool) (Policy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → Policy ctx r) (txId? : Option UInt64 := none) : m (Except ApiError α) :=
  dbRun cfg q txId? post hPolicy

private abbrev dbRunRows {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (pred : Row → Bool) (errMsg : String) (pf : P) (txId? : Option UInt64)
    (encWrite : List (String × EncColSpec)) (encRead : List (Nat × EncColSpec)) : m (Except ApiError (Array Row)) :=
  dbRunChecked (Q := dbArrPost fun r => RowInv r ∧ pred r = true) cfg q txId?
    (decodeCheckedArr (decodeRowErr decode) (fun r => rowInvBool r && pred r) errMsg)
    (decodeCheckedArr_post _ _ _ (and_inv_pred hInvSound)) (fun _ => trivial) pf encWrite encRead

private abbrev dbRunOneRow {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (pred : Row → Bool) (errMsg : String) (pf : P) (txId? : Option UInt64)
    (encWrite : List (String × EncColSpec)) (encRead : List (Nat × EncColSpec)) : m (Except ApiError (Option Row)) :=
  dbRunChecked (Q := fun res => ∀ r, res = .ok (some r) → RowInv r ∧ pred r = true) cfg q txId?
    (decodeCheckedOne decode (fun r => rowInvBool r && pred r) errMsg)
    (decodeCheckedOne_post _ _ _ (and_inv_pred hInvSound)) (fun _ _ h => nomatch h) pf encWrite encRead

private abbrev dbSelectRun {Res : Type} (run : DbRowRunner Row Res m) (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (wherePred : Row → Bool) (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r) (txId? : Option UInt64 := none)
    (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError Res) :=
  run cfg q decode RowInv rowInvBool hInvSound wherePred "database row violated verified table invariant or query predicate" hPolicy txId? [] encRead

private abbrev dbUpdateRun {Res : Type} (errMsg : String) (run : DbRowRunner Row Res m) (cfg : DbConfig) (q : SqlQuery)
    (decode : DbRow → Except String Row) (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (TransInv : Row → Row → Prop) (wherePred : Row → Bool) (setFn : Row → Row) (postPred : Row → Bool)
    (UpdatePolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicyOld : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx r) (hPolicyNew : ∀ r, RowInv r → wherePred r = true → UpdatePolicy ctx (setFn r))
    (hInvPres : ∀ r, RowInv r → wherePred r = true → RowInv (setFn r)) (hTrans : ∀ r, RowInv r → wherePred r = true → TransInv r (setFn r))
    (txId? : Option UInt64 := none) (encWrite : List (String × EncColSpec) := []) (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError Res) :=
  run cfg q decode RowInv rowInvBool hInvSound postPred errMsg (And.intro hPolicyOld (And.intro hPolicyNew (And.intro hInvPres hTrans))) txId? encWrite encRead

abbrev dbSelect := @dbSelectRun Row m (Array Row) (fun {_} => @dbRunRows Row m _ _ _)
abbrev dbFindOne := @dbSelectRun Row m (Option Row) (fun {_} => @dbRunOneRow Row m _ _ _)

/-- Policy-verified cross-table `SELECT` / `FIND ONE` / `UPDATE` / `COUNT` / `DELETE` / `AGG`:
    proves `hPolicy : P` (quantified over a database snapshot `Snap`) at compile time while checking `rowInvBool` on returned rows. -/
abbrev dbSelectP {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (hPolicy : P) (txId? : Option UInt64 := none) (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError (Array Row)) :=
  dbRunRows cfg q decode RowInv rowInvBool hInvSound (fun _ => true) "database row violated verified table invariant" hPolicy txId? [] encRead

abbrev dbFindOneP {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (hPolicy : P) (txId? : Option UInt64 := none) (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError (Option Row)) :=
  dbRunOneRow cfg q decode RowInv rowInvBool hInvSound (fun _ => true) "database row violated verified table invariant" hPolicy txId? [] encRead

abbrev dbUpdateP {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (hPolicy : P) (txId? : Option UInt64 := none) (encWrite : List (String × EncColSpec) := []) (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError (Array Row)) :=
  dbRunRows cfg q decode RowInv rowInvBool hInvSound (fun _ => true) "updated database row violated verified table invariant" hPolicy txId? encWrite encRead

abbrev dbUpdateOneP {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (hPolicy : P) (txId? : Option UInt64 := none) (encWrite : List (String × EncColSpec) := []) (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError (Option Row)) :=
  dbRunOneRow cfg q decode RowInv rowInvBool hInvSound (fun _ => true) "updated database row violated verified table invariant" hPolicy txId? encWrite encRead

abbrev dbSelectProjP {Proj : Type} {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Proj)
    (hPolicy : P) (txId? : Option UInt64 := none) (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError (Array Proj)) :=
  dbRunChecked (Q := fun _ => True) cfg q txId?
    (fun dbRes => (dbRes.rows.toList.mapM (decodeRowErr decode)).map List.toArray)
    (fun _ => trivial) (fun _ => trivial) hPolicy [] encRead

abbrev dbFindOneProjP {Proj : Type} {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Proj)
    (hPolicy : P) (txId? : Option UInt64 := none) (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError (Option Proj)) :=
  dbRunChecked (Q := fun _ => True) cfg q txId?
    (fun dbRes => match dbRes.rows[0]? with | none => .ok none | some r => (decodeRowErr decode r).map some)
    (fun _ => trivial) (fun _ => trivial) hPolicy [] encRead

abbrev dbCountP {P : Prop} (cfg : DbConfig) (q : SqlQuery) (hPolicy : P) (txId? : Option UInt64 := none) : m (Except ApiError Nat) :=
  dbRun cfg q txId? (decodeFirstCell (α := Nat) id none 0 "COUNT") hPolicy

abbrev dbSumNatP {P : Prop} (cfg : DbConfig) (q : SqlQuery) (hPolicy : P) (txId? : Option UInt64 := none) : m (Except ApiError Nat) :=
  dbRun cfg q txId? (decodeFirstCell (α := Nat) id (some 0) 0 "SUM") hPolicy

abbrev dbSumIntP {P : Prop} (cfg : DbConfig) (q : SqlQuery) (hPolicy : P) (txId? : Option UInt64 := none) : m (Except ApiError Int) :=
  dbRun cfg q txId? (decodeFirstCell (α := Int) id (some 0) 0 "SUM") hPolicy

abbrev dbAggOptP {Val : Type} [FromSql Val] {P : Prop} (cfg : DbConfig) (q : SqlQuery) (_proj : Row → Val) (hPolicy : P) (txId? : Option UInt64 := none) : m (Except ApiError (Option Val)) :=
  dbRun cfg q txId? (decodeFirstCell (α := Val) some (some none) none "aggregate") hPolicy

abbrev dbDeleteP {P : Prop} (cfg : DbConfig) (q : SqlQuery) (hPolicy : P) (txId? : Option UInt64 := none) : m (Except ApiError Nat) :=
  dbRun cfg q txId? (fun dbRes => .ok dbRes.affected) hPolicy

@[inline] def fromSqlOfField {R α : Type} [FromSql α] (_ : R → α) (v : SqlVal) : Except String α := FromSql.fromSql v

abbrev dbSelectProj {Proj : Type} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Proj)
    (RowInv : Row → Prop) (wherePred : Row → Bool) (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r) (txId? : Option UInt64 := none)
    (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError (Array Proj)) :=
  dbSelectProjP cfg q decode hPolicy txId? encRead

abbrev dbFindOneProj {Proj : Type} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Proj)
    (RowInv : Row → Prop) (wherePred : Row → Bool) (ReadPolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hPolicy : ∀ r, RowInv r → wherePred r = true → ReadPolicy ctx r) (txId? : Option UInt64 := none)
    (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError (Option Proj)) :=
  dbFindOneProjP cfg q decode hPolicy txId? encRead
abbrev dbCount := @dbPolicyRun Row m _ _ Nat (decodeFirstCell (α := Nat) id none 0 "COUNT")
abbrev dbSumNat := @dbPolicyRun Row m _ _ Nat (decodeFirstCell (α := Nat) id (some 0) 0 "SUM")
abbrev dbSumInt := @dbPolicyRun Row m _ _ Int (decodeFirstCell (α := Int) id (some 0) 0 "SUM")
abbrev dbUpdate := @dbUpdateRun Row m (Array Row) "database row violated verified table invariant or query predicate" (fun {_} => @dbRunRows Row m _ _ _)
abbrev dbUpdateOne := @dbUpdateRun Row m (Option Row) "updated database row violated verified table invariant or postcondition" (fun {_} => @dbRunOneRow Row m _ _ _)
abbrev dbDelete := @dbPolicyRun Row m _ _ Nat (fun dbRes => .ok dbRes.affected)

abbrev dbInsert (cfg : DbConfig) (q : SqlQuery) (newRow : Row) (RowInv : Row → Prop) (InsertPolicy : RequestCtx → Row → Prop)
    (ctx : RequestCtx) (hInv : RowInv newRow) (hPolicy : InsertPolicy ctx newRow) (txId? : Option UInt64 := none)
    (encWrite : List (String × EncColSpec) := []) : m (Except ApiError Row) :=
  dbRunChecked (Q := fun res => match res with | .ok r => r = newRow ∧ RowInv r | .error _ => True)
    cfg q txId? (fun _ => .ok newRow) (fun _ => ⟨rfl, hInv⟩) (fun _ => trivial) hPolicy encWrite []

abbrev dbInsertOrIgnore (cfg : DbConfig) (q : SqlQuery) (newRow : Row) (RowInv : Row → Prop) (InsertPolicy : RequestCtx → Row → Prop)
    (ctx : RequestCtx) (hInv : RowInv newRow) (hPolicy : InsertPolicy ctx newRow) (txId? : Option UInt64 := none)
    (encWrite : List (String × EncColSpec) := []) : m (Except ApiError (Option Row)) :=
  dbRunChecked (Q := fun res => match res with | .ok (some r) => r = newRow ∧ RowInv r | .ok none => True | .error _ => True)
    cfg q txId? (fun dbRes => .ok (if dbRes.rows.isEmpty then none else some newRow))
    (fun dbRes => by cases hE : dbRes.rows.isEmpty <;> simp [hInv]) (fun _ => trivial) hPolicy encWrite []

abbrev dbUpsert (cfg : DbConfig) (q : SqlQuery) (newRow : Row) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (TransInv : Row → Row → Prop) (conflictPred : Row → Bool)
    (InsertPolicy UpdatePolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hInv : RowInv newRow) (hInsPol : InsertPolicy ctx newRow) (hUpdPolNew : UpdatePolicy ctx newRow)
    (hUpdPolOld : ∀ r, RowInv r → conflictPred r = true → UpdatePolicy ctx r)
    (hTrans : ∀ r, RowInv r → conflictPred r = true → TransInv r newRow)
    (txId? : Option UInt64 := none)
    (encWrite : List (String × EncColSpec) := []) (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError Row) :=
  dbRunChecked (Q := fun res => match res with | .ok r => RowInv r | .error _ => True)
    cfg q txId?
    (fun dbRes =>
      match decodeCheckedOne decode rowInvBool "upserted database row violated verified table invariant" dbRes with
      | .error e => .error e
      | .ok (some r) => .ok r
      | .ok none => .error (ApiError.forbidden "upsert conflict rejected by policy"))
    (fun dbRes => by
      cases hd : decodeCheckedOne decode rowInvBool "upserted database row violated verified table invariant" dbRes with
      | error _ => trivial
      | ok opt => cases opt with
        | none => trivial
        | some r => exact decodeCheckedOne_post decode rowInvBool _ hInvSound dbRes r hd)
    (fun _ => trivial) (And.intro hInv (And.intro hInsPol (And.intro hUpdPolNew (And.intro hUpdPolOld hTrans)))) encWrite encRead

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
    (txId? : Option UInt64 := none) (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError (Array (RowL × RowR))) :=
  dbRunChecked (Q := dbArrPost fun p => RowInvL p.1 ∧ wherePredL p.1 = true ∧ RowInvR p.2 ∧ wherePredR p.2 = true) cfg q txId?
    (decodeCheckedArr (decodeJoinRowErr leftColCount decodeL decodeR)
      (fun p => rowInvBoolL p.1 && wherePredL p.1 && rowInvBoolR p.2 && wherePredR p.2 && (keyL p.1 == keyR p.2))
      "database joined row violated verified table invariant or query predicate")
    (decodeCheckedArr_post _ _ _ fun p h => by
      simp only [Bool.and_eq_true] at h; exact ⟨hInvSoundL p.1 h.1.1.1.1, h.1.1.1.2, hInvSoundR p.2 h.1.1.2, h.1.2⟩)
    (fun _ => trivial) (And.intro hPolicyL hPolicyR) [] encRead

theorem some_getD_eq_self_iff {α : Type} (o : Option α) (d : α) : some (o.getD d) = o ↔ o ≠ none := by cases o <;> simp

/-! ## Standalone Typed DB Client (for background workers & scripts outside `server`) -/

inductive DbFilter where
  | litTrue
  | cmp       (op : SqlBinOp) (col : String) (val : SqlVal)
  | isNull    (col : String)
  | isNotNull (col : String)
  | and       (a b : DbFilter)
  | or        (a b : DbFilter)
  | not       (a : DbFilter)

private def resolveDbCol (tblName : String) (cols : List SqlIdent) (col : String) : Except ApiError SqlIdent :=
  match cols.find? (·.raw == col) with
  | some cid => .ok cid
  | none => .error (ApiError.badRequest s!"unknown column `{col}` on table `{tblName}`")

namespace DbFilter
def eq {α : Type} [ToSql α] (col : String) (v : α) : DbFilter := .cmp .eq col (ToSql.toSql v)
def ne {α : Type} [ToSql α] (col : String) (v : α) : DbFilter := .cmp .ne col (ToSql.toSql v)
def lt {α : Type} [ToSql α] (col : String) (v : α) : DbFilter := .cmp .lt col (ToSql.toSql v)
def le {α : Type} [ToSql α] (col : String) (v : α) : DbFilter := .cmp .le col (ToSql.toSql v)
def gt {α : Type} [ToSql α] (col : String) (v : α) : DbFilter := .cmp .gt col (ToSql.toSql v)
def ge {α : Type} [ToSql α] (col : String) (v : α) : DbFilter := .cmp .ge col (ToSql.toSql v)

def toSqlExpr (tblName : String) (cols : List SqlIdent) : DbFilter → Except ApiError SqlExpr
  | .litTrue => .ok .litTrue
  | .cmp op col v => (resolveDbCol tblName cols col).map fun cid => .binOp op (.col cid) (.param v)
  | .isNull col => (resolveDbCol tblName cols col).map fun cid => .isNull (.col cid)
  | .isNotNull col => (resolveDbCol tblName cols col).map fun cid => .isNotNull (.col cid)
  | .and a b => do return .binOp .and (← toSqlExpr tblName cols a) (← toSqlExpr tblName cols b)
  | .or a b => do return .binOp .or (← toSqlExpr tblName cols a) (← toSqlExpr tblName cols b)
  | .not a => do return .not (← toSqlExpr tblName cols a)
end DbFilter

inductive DbSetRhs where
  | val (v : SqlVal)
  | add (delta : SqlVal)
  | sub (delta : SqlVal)
deriving Inhabited, DecidableEq

@[inline] def sqlSet {α : Type} [ToSql α] (col : String) (v : α) : String × DbSetRhs := (col, .val (ToSql.toSql v))
@[inline] def sqlAdd {α : Type} [ToSql α] (col : String) (delta : α) : String × DbSetRhs := (col, .add (ToSql.toSql delta))
@[inline] def sqlSub {α : Type} [ToSql α] (col : String) (delta : α) : String × DbSetRhs := (col, .sub (ToSql.toSql delta))

structure TableHandle (Row : Type) where
  config     : DbConfig
  tableName  : SqlIdent
  columns    : List SqlIdent
  decodeRow  : DbRow → Except String Row
  encodeRow  : Row → List (SqlIdent × SqlVal)
  rowInvBool : Row → Bool
  encWrite   : List (String × EncColSpec) := []
  encRead    : List (Nat × EncColSpec) := []

namespace TableHandle

private def resolveCol {Row : Type} (h : TableHandle Row) (col : String) : Except ApiError SqlIdent :=
  resolveDbCol h.tableName.raw h.columns col

section Ops
variable {Row : Type} {m : Type → Type} [Monad m] [MonadServer m]

private def runDec {α : Type} (h : TableHandle Row) (qRes : Except ApiError SqlQuery) (txId? : Option UInt64)
    (dec : DbResult → Except ApiError α) (doEnc doDec : Bool) : m (Except ApiError α) := do
  match qRes with
  | .error e => return .error e
  | .ok q =>
      let q' ← if doEnc then dbEncryptQuery h.encWrite q else pure (.ok q)
      match q' with
      | .error e => return .error e
      | .ok qEnc =>
          match ← execDbMaybeTx h.config qEnc txId? with
          | .error e => return .error e
          | .ok dbRes =>
              let decRes ← if doDec then dbDecryptResult h.encRead dbRes else pure (.ok dbRes)
              return decRes.bind dec

def select (h : TableHandle Row) (where_ : DbFilter := .litTrue) (orderBy? : Option (String × Bool) := none)
    (limit? : Option Nat := none) (offset? : Option Nat := none) (txId? : Option UInt64 := none) : m (Except ApiError (Array Row)) :=
  runDec h (do
    let wExpr ← where_.toSqlExpr h.tableName.raw h.columns
    let ob ← orderBy?.mapM fun (col, asc) => (·, if asc then SqlOrderDir.asc else SqlOrderDir.desc) <$> h.resolveCol col
    return .select h.tableName h.columns wExpr ob limit? offset?) txId?
    (decodeCheckedArr (decodeRowErr h.decodeRow) h.rowInvBool s!"database row in `{h.tableName.raw}` violated table invariant")
    (doEnc := false) (doDec := true)

def findOne (h : TableHandle Row) (where_ : DbFilter) (orderBy? : Option (String × Bool) := none)
    (txId? : Option UInt64 := none) : m (Except ApiError (Option Row)) :=
  (·.map (·[0]?)) <$> h.select where_ orderBy? (limit? := some 1) (txId? := txId?)

def selectProjected {Proj : Type} (h : TableHandle Row) (cols : List String)
    (decode : DbRow → Except String Proj) (where_ : DbFilter := .litTrue)
    (orderBy? : Option (String × Bool) := none) (limit? : Option Nat := none) (offset? : Option Nat := none)
    (txId? : Option UInt64 := none) : m (Except ApiError (Array Proj)) := do
  let qRes : Except ApiError (SqlQuery × List (Nat × EncColSpec)) := do
    if cols.isEmpty then throw (ApiError.badRequest s!"projected select on `{h.tableName.raw}` requires at least one column")
    let colIds ← cols.mapM h.resolveCol
    let wExpr ← where_.toSqlExpr h.tableName.raw h.columns
    let ob ← orderBy?.mapM fun (col, asc) => (·, if asc then SqlOrderDir.asc else SqlOrderDir.desc) <$> h.resolveCol col
    let projEncRead : List (Nat × EncColSpec) := (colIds.zipIdx).filterMap fun (cid, i) =>
      (h.encWrite.lookup cid.raw).map (i, ·)
    return (.select h.tableName colIds wExpr ob limit? offset?, projEncRead)
  match qRes with
  | .error e => return .error e
  | .ok (q, projEncRead) =>
      match ← execDbMaybeTx h.config q txId? with
      | .error e => return .error e
      | .ok dbRes =>
          let decRes ← if projEncRead.isEmpty then pure (.ok dbRes) else dbDecryptResult projEncRead dbRes
          return decRes.bind fun dr => (dr.rows.toList.mapM (decodeRowErr decode)).map List.toArray

def count (h : TableHandle Row) (where_ : DbFilter := .litTrue) (txId? : Option UInt64 := none) : m (Except ApiError Nat) :=
  runDec h (do return .count h.tableName (← where_.toSqlExpr h.tableName.raw h.columns)) txId?
    (decodeFirstCell (α := Int) Int.toNat none 0 "count") (doEnc := false) (doDec := false)

def insert (h : TableHandle Row) (row : Row) (txId? : Option UInt64 := none) : m (Except ApiError Row) :=
  runDec h (do
    if !h.rowInvBool row then throw (ApiError.badRequest s!"row violated table invariant for `{h.tableName.raw}`")
    return .insert h.tableName (h.encodeRow row) h.columns) txId?
    (fun dbRes => match decodeCheckedOne h.decodeRow h.rowInvBool s!"inserted row in `{h.tableName.raw}` violated table invariant" dbRes with
      | .error e => .error e | .ok (some r) => .ok r
      | .ok none => .error (ApiError.internal s!"insert into `{h.tableName.raw}` returned no row"))
    (doEnc := true) (doDec := true)

def insertOrIgnore (h : TableHandle Row) (row : Row) (conflictCols : List String := [])
    (txId? : Option UInt64 := none) : m (Except ApiError (Option Row)) :=
  runDec h (do
    if !h.rowInvBool row then throw (ApiError.badRequest s!"row violated table invariant for `{h.tableName.raw}`")
    let ccs ← conflictCols.mapM h.resolveCol
    for cc in ccs do
      if (h.encWrite.lookup cc.raw).isSome then
        throw (ApiError.badRequest s!"cannot use encrypted column `{cc.raw}` as conflict target in `{h.tableName.raw}`")
    return .insertOrIgnore h.tableName (h.encodeRow row) ccs (h.columns.take 1)) txId?
    (fun dbRes => .ok (if dbRes.rows.isEmpty then none else some row))
    (doEnc := true) (doDec := false)

def upsert (h : TableHandle Row) (row : Row) (conflictCols : List String) (updateCols : List String)
    (conflictWhere? : Option DbFilter := none) (txId? : Option UInt64 := none) : m (Except ApiError (Option Row)) :=
  runDec h (do
    if !h.rowInvBool row then throw (ApiError.badRequest s!"row violated table invariant for `{h.tableName.raw}`")
    if conflictCols.isEmpty then throw (ApiError.badRequest s!"upsert on `{h.tableName.raw}` requires at least one conflict column")
    let ccs ← conflictCols.mapM h.resolveCol
    let ucs ← updateCols.mapM h.resolveCol
    let cw? ← conflictWhere?.mapM (·.toSqlExpr h.tableName.raw h.columns)
    return .upsert h.tableName (h.encodeRow row) ccs ucs cw? h.columns) txId?
    (decodeCheckedOne h.decodeRow h.rowInvBool s!"upserted row in `{h.tableName.raw}` violated table invariant")
    (doEnc := true) (doDec := true)

private def runUpdate {α : Type} (h : TableHandle Row) (sets : List (String × DbSetRhs)) (where_ : DbFilter)
    (retCols : List SqlIdent) (dec : DbResult → Except ApiError α) (doDec : Bool) (txId? : Option UInt64) : m (Except ApiError α) :=
  runDec h (do
    if sets.isEmpty then throw (ApiError.badRequest s!"update on `{h.tableName.raw}` requires at least one column assignment")
    let sPairs ← sets.mapM fun (c, rhs) => do
      let cid ← h.resolveCol c
      let expr : SqlExpr := match rhs with
        | .val v => .param v
        | .add v => .binOp .add (.col cid) (.param v)
        | .sub v => .binOp .sub (.col cid) (.param v)
      return (cid, expr)
    return .update h.tableName sPairs (← where_.toSqlExpr h.tableName.raw h.columns) retCols) txId? dec (doEnc := true) (doDec := doDec)

def update (h : TableHandle Row) (sets : List (String × DbSetRhs)) (where_ : DbFilter := .litTrue)
    (txId? : Option UInt64 := none) : m (Except ApiError Nat) :=
  runUpdate h sets where_ [] (fun r => .ok r.affected) false txId?

def updateReturning (h : TableHandle Row) (sets : List (String × DbSetRhs)) (where_ : DbFilter := .litTrue)
    (txId? : Option UInt64 := none) : m (Except ApiError (Array Row)) :=
  runUpdate h sets where_ h.columns
    (decodeCheckedArr (decodeRowErr h.decodeRow) h.rowInvBool s!"updated row in `{h.tableName.raw}` violated table invariant")
    true txId?

def updateOneReturning (h : TableHandle Row) (sets : List (String × DbSetRhs)) (where_ : DbFilter := .litTrue)
    (txId? : Option UInt64 := none) : m (Except ApiError (Option Row)) :=
  runUpdate h sets where_ h.columns
    (decodeCheckedOne h.decodeRow h.rowInvBool s!"updated row in `{h.tableName.raw}` violated table invariant")
    true txId?

def delete (h : TableHandle Row) (where_ : DbFilter) (txId? : Option UInt64 := none) : m (Except ApiError Nat) :=
  runDec h (do return .delete h.tableName (← where_.toSqlExpr h.tableName.raw h.columns) []) txId?
    (fun r => .ok r.affected) (doEnc := false) (doDec := false)

end Ops
end TableHandle

def withTransaction {m : Type → Type} {α : Type} [Monad m] [MonadServer m]
    (cfg : DbConfig) (body : UInt64 → m (Except ApiError α)) : m (Except ApiError α) := do
  match ← MonadServer.dbTxBegin cfg with
  | .error e => return .error e
  | .ok tid =>
      match ← body tid with
      | .error e => MonadServer.dbTxRollback cfg tid; return .error e
      | .ok v => (·.map fun () => v) <$> MonadServer.dbTxCommit cfg tid

def sqlCmpOps : Array (String × Lean.Name) := #[
  ("==", `Qed.Server.Db.SqlBinOp.eq), ("!=", `Qed.Server.Db.SqlBinOp.ne), ("<", `Qed.Server.Db.SqlBinOp.lt),
  ("<=", `Qed.Server.Db.SqlBinOp.le), (">", `Qed.Server.Db.SqlBinOp.gt), (">=", `Qed.Server.Db.SqlBinOp.ge)]

open Lean Elab Command in
def mkSqlIdentTerm (ref : Syntax) (raw : String) : CommandElabM Term := do
  if !isSafeSqlIdent raw then
    throwErrorAt ref s!"invalid SQL identifier `{raw}` (must start with an ASCII letter or `_` and contain only ASCII letters, digits, and `_`, max 63 chars)"
  `(Qed.Server.Db.SqlIdent.mk $(Syntax.mkStrLit raw) (by decide))

open Lean in
@[noinline, nospecialize]
def mkTypedSqlParamTerm {M : Type → Type} [Monad M] [MonadQuotation M] (rowTyId fId : Ident) (valT : Term) : M Term :=
  `(Qed.Server.Db.SqlExpr.param (Qed.Server.Db.toSqlLike (fun (_r : $rowTyId) => _r.$fId) $valT))

open Lean Elab Command in
@[noinline]
def mkEncColSpecTerm (tableName colName : String) (ek : DbEncKeyInfo) : CommandElabM Term := do
  let prevTs ← ek.prevKeys.toArray.mapM fun (k, fb?) => `(($(Syntax.mkStrLit k), $(quote fb?)))
  `({ keyEnv := $(Syntax.mkStrLit ek.keyEnv), fallback? := $(quote ek.fallback?), aad := ($(Syntax.mkStrLit s!"{tableName}.{colName}") : String).toUTF8, isBytes := $(quote ek.isBytes), prevKeys := [$[$prevTs:term],*] : Qed.Server.Db.EncColSpec })

syntax (name := qedDbProveTac) "qedDbProve" "[" ident,* "]" str str str : tactic

open Lean Meta Elab Tactic in
@[tactic qedDbProveTac]
def elabQedDbProve : Tactic := fun stx => do
  let unfoldNames ← (stx.getArg 2).getSepArgs.mapM resolveGlobalConstNoOverload
  let simpNames := Qed.Verify.Core.dbBaseSimpNames.push ``eq_self
  let simprocs := #[``Qed.Server.qedReduceStrLen]
  -- Pass 1: Keep user pure `let` bindings opaque (`zetaDelta := false`), only expanding `_insRow`,
  -- so `whnf` never unfolds string/helper internals on symbolic inputs.
  let okOpaque ← Qed.Verify.Core.tryRestoreM false id do
    let g0 ← getMainGoal
    let g1 ← g0.withContext do
      let mut fvs : Array FVarId := #[]
      for ld in (← getLCtx) do
        if ld.isLet && ld.userName.eraseMacroScopes == `_insRow then fvs := fvs.push ld.fvarId
      if fvs.isEmpty then pure g0 else g0.replaceTargetDefEq (← Meta.zetaDeltaFVars (← instantiateMVars (← g0.getType)) fvs)
    replaceMainGoal [g1]
    Qed.Verify.Core.solveWithUnfolds unfoldNames simpNames simprocs
      (simpCfg := { zetaDelta := false }) (harvestFacts := true) (scanLCtxValues := false) (clearErrorsOnFail := true)
  if okOpaque then return
  if !(← Qed.Verify.Core.solveWithUnfolds unfoldNames simpNames simprocs (harvestFacts := true)) then
    Qed.Diag.throwUnsolvedGoals
      m!"Database {(⟨stx.getArg 4⟩ : TSyntax `str).getString} failed in `{(⟨stx.getArg 5⟩ : TSyntax `str).getString}`:"
      m!"\n\nHint: {(⟨stx.getArg 6⟩ : TSyntax `str).getString}"
      (ref? := some stx) (stripPrefixes := ["_row", "_old", "_new", "r"]) (bulletPrefix := "  • must prove: ")
      (goals? := some [(← getUnsolvedGoals).headD (← getMainGoal)])

end Qed.Server.Db
