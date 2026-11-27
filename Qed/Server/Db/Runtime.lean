import Qed.Base64
import Qed.Server.Core
import Qed.Server.Db.Core

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

/-! ## Transparent AES-256-GCM Encryption & Decryption for `encrypted(...)` Columns -/

section DbEnc
variable {m : Type → Type} [Monad m] [MonadServer m]

@[noinline, nospecialize]
private def dbEncryptVal (spec : EncColSpec) : SqlVal → m (Except ApiError SqlVal)
  | .null => pure (.ok .null)
  | .text s => (·.map fun ct => .text (Qed.Base64.encode ct)) <$> MonadServer.aeadEncrypt spec.keyEnv spec.fallback? spec.aad s.toUTF8
  | .bytes bs => (·.map fun ct => .text (Qed.Base64.encode ct)) <$> MonadServer.aeadEncrypt spec.keyEnv spec.fallback? spec.aad bs
  | _ => pure (.error (ApiError.internal "encrypted database column expects TEXT, BLOB, or NULL"))

@[noinline, nospecialize]
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

@[noinline, nospecialize]
private def dbDecryptVal (spec : EncColSpec) : SqlVal → m (Except ApiError SqlVal)
  | .null => pure (.ok .null)
  | .text b64 =>
      match Qed.Base64.decode b64 with
      | .error e => pure (.error (ApiError.internal s!"encrypted column base64 decode failed: {e}"))
      | .ok raw =>
          MonadServer.aeadDecrypt spec.keyEnv spec.fallback? spec.aad raw >>= fun
            | .ok pt => pure (finishDecryptVal spec.isBytes (.ok pt))
            | .error err =>
                if spec.prevKeys.isEmpty || Qed.Str.containsBytes err.message "missing required encryption key" then
                  pure (.error err)
                else finishDecryptVal spec.isBytes <$> dbDecryptTryPrev spec.aad raw err spec.prevKeys
  | _ => pure (.error (ApiError.internal "encrypted database column stored value must be TEXT or NULL"))

@[noinline, nospecialize]
private def mapExceptList {α β : Type} (f : α → m (Except ApiError β)) : List α → m (Except ApiError (List β))
  | [] => pure (.ok [])
  | x :: xs => f x >>= fun | .error e => pure (.error e) | .ok y => (·.map (y :: ·)) <$> mapExceptList f xs

@[noinline, nospecialize]
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

@[noinline, nospecialize]
private def dbDecryptRow : List (Nat × EncColSpec) → DbRow → m (Except ApiError DbRow)
  | [], row => pure (.ok row)
  | (idx, spec) :: rest, row =>
      if h : idx < row.size then
        dbDecryptVal spec row[idx] >>= fun | .error e => pure (.error e) | .ok dv => dbDecryptRow rest (row.set idx dv h)
      else pure (.error (ApiError.internal s!"encrypted column index {idx} out of bounds"))

@[noinline, nospecialize]
def dbDecryptResult (encRead : List (Nat × EncColSpec)) (res : DbResult) : m (Except ApiError DbResult) :=
  if encRead.isEmpty then pure (.ok res)
  else (·.map fun rs => { res with rows := rs.toArray }) <$> mapExceptList (dbDecryptRow encRead) res.rows.toList

end DbEnc

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
    srvEnsPostOpt P (decodeCheckedOne decode check errMsg dbRes) := by
  unfold srvEnsPostOpt decodeCheckedOne; dsimp only [Except.map]
  cases hd : decodeCheckedList (decodeRowErr decode) check errMsg (dbRes.rows.toList.take 1) with
  | error _ => trivial
  | ok out => cases out with
    | nil => trivial
    | cons r _ => exact hP r (decodeCheckedList_sound _ _ _ _ _ hd r (List.mem_cons_self ..))

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

@[reducible] def dbExecEff (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64) : ServerEffect :=
  match txId? with | some tid => .dbTxExec cfg tid q | none => .dbExec cfg q

section ProgEff
variable {σ : Type} {Inv : σ → Prop} {A : Prop} {Step : σ → σ → Prop} {EffOk : ServerEffect → Prop}

private theorem progEffSpec_map {α β : Type} {Q : α → Prop} {Post : β → Prop} {p : ThreadProg σ α}
    (f : α → β) (hp : ProgEffSpec Inv A Step EffOk Q p) (hf : ∀ a, Q a → Post (f a)) : ProgEffSpec Inv A Step EffOk Post (f <$> p) :=
  hp.bind fun a ha => .pure (f a) (hf a ha)
private theorem progEffSpec_map_triv {α β : Type} (f : α → β) {p : ThreadProg σ α} (hp : ProgEffSpec Inv A Step EffOk (fun _ => True) p) :
    ProgEffSpec Inv A Step EffOk (fun _ => True) (f <$> p) := progEffSpec_map f hp fun _ _ => trivial
private theorem progEffSpec_bind_triv {α β : Type} {p : ThreadProg σ α} {k : α → ThreadProg σ β}
    (hp : ProgEffSpec Inv A Step EffOk (fun _ => True) p) (hk : ∀ a, ProgEffSpec Inv A Step EffOk (fun _ => True) (k a)) :
    ProgEffSpec Inv A Step EffOk (fun _ => True) (p >>= k) := hp.bind fun a _ => hk a

private theorem progEffSpec_mapExceptList {α β : Type} (f : α → ThreadProg σ (Except ApiError β))
    (hf : ∀ x, ProgEffSpec Inv A Step EffOk (fun _ => True) (f x)) : ∀ xs : List α, ProgEffSpec Inv A Step EffOk (fun _ => True) (mapExceptList f xs)
  | [] => .pure _ trivial
  | x :: xs => progEffSpec_bind_triv (hf x) fun | .error _ => .pure _ trivial | .ok _ => progEffSpec_map_triv _ (progEffSpec_mapExceptList f hf xs)

private theorem progEffSpec_dbEncryptVal (hEnc : ∀ k f a p, EffOk (.aeadEncrypt k f a p)) (spec : EncColSpec) (v : SqlVal) :
    ProgEffSpec Inv A Step EffOk (fun _ => True) (dbEncryptVal (m := ThreadProg σ) spec v) := by
  cases v with
  | text s => exact progEffSpec_map_triv _ (.io (.aeadEncrypt spec.keyEnv spec.fallback? spec.aad s.toUTF8) _ (hEnc _ _ _ _) fun _ => .pure _ trivial)
  | bytes bs => exact progEffSpec_map_triv _ (.io (.aeadEncrypt spec.keyEnv spec.fallback? spec.aad bs) _ (hEnc _ _ _ _) fun _ => .pure _ trivial)
  | _ => exact .pure _ trivial

private theorem progEffSpec_dbEncryptQuery (encWrite : List (String × EncColSpec)) (q : SqlQuery)
    (hEnc : encWrite = [] ∨ q.isWrite = false ∨ ∀ k f a p, EffOk (.aeadEncrypt k f a p)) :
    ProgEffSpec Inv A Step EffOk (fun r => ∀ q', r = .ok q' → q'.isWrite = q.isWrite) (dbEncryptQuery (m := ThreadProg σ) encWrite q) := by
  unfold dbEncryptQuery; split
  · exact .pure _ fun q' h => by cases h; rfl
  · rename_i hne
    have getE (hw : q.isWrite = true) : ∀ k f a p, EffOk (.aeadEncrypt k f a p) :=
      hEnc.elim (fun he => absurd (he ▸ rfl) hne) fun h => h.elim (fun hf => by rw [hw] at hf; cases hf) id
    cases q with
    | insert _ cols _ | insertOrIgnore _ cols _ _ | upsert _ cols _ _ _ _ =>
        exact progEffSpec_map _ (progEffSpec_mapExceptList _ (fun (c, v) => by
          dsimp only; cases encWrite.lookup c.raw with
          | none => exact .pure _ trivial | some spec => exact progEffSpec_map_triv _ (progEffSpec_dbEncryptVal (getE rfl) spec v)) cols)
          (fun r _ q' hq => by cases r <;> cases hq <;> rfl)
    | update _ sets _ _ =>
        exact progEffSpec_map _ (progEffSpec_mapExceptList _ (fun (c, e) => by
          dsimp only; cases encWrite.lookup c.raw with
          | none => exact .pure _ trivial
          | some spec => cases e <;> first | exact .pure _ trivial | exact progEffSpec_map_triv _ (progEffSpec_dbEncryptVal (getE rfl) spec _)) sets)
          (fun r _ q' hq => by cases r <;> cases hq <;> rfl)
    | _ => exact .pure _ fun q' h => by cases h; rfl

private theorem progEffSpec_dbDecryptTryPrev (hEnv : ∀ v, EffOk (.readEnv v)) (hDec : ∀ k f a c, EffOk (.aeadDecrypt k f a c))
    (aad raw : ByteArray) (origErr : ApiError) :
    ∀ ks : List (String × Option String), ProgEffSpec Inv A Step EffOk (fun _ => True) (dbDecryptTryPrev (m := ThreadProg σ) aad raw origErr ks)
  | [] => .pure _ trivial
  | (kEnv, fb?) :: rest =>
      progEffSpec_bind_triv (ProgEffSpec.exec (.readEnv kEnv) (hEnv kEnv) fun _ => trivial) fun _ => by
        dsimp only; split
        · exact progEffSpec_dbDecryptTryPrev hEnv hDec aad raw origErr rest
        · exact progEffSpec_bind_triv (ProgEffSpec.exec (.aeadDecrypt kEnv fb? aad raw) (hDec kEnv fb? aad raw) fun _ => trivial) fun
            | .ok _ => .pure _ trivial | .error _ => progEffSpec_dbDecryptTryPrev hEnv hDec aad raw origErr rest

private theorem progEffSpec_dbDecryptVal (hEnv : ∀ v, EffOk (.readEnv v)) (hDec : ∀ k f a c, EffOk (.aeadDecrypt k f a c))
    (spec : EncColSpec) (v : SqlVal) : ProgEffSpec Inv A Step EffOk (fun _ => True) (dbDecryptVal (m := ThreadProg σ) spec v) := by
  cases v with
  | text s =>
      dsimp only [dbDecryptVal]; cases Qed.Base64.decode s with
      | error _ => exact .pure _ trivial
      | ok raw =>
          exact progEffSpec_bind_triv (ProgEffSpec.exec (.aeadDecrypt spec.keyEnv spec.fallback? spec.aad raw) (hDec _ _ _ _) fun _ => trivial) fun
            | .ok _ => .pure _ trivial
            | .error err => by
                dsimp only; split
                · exact .pure _ trivial
                · exact progEffSpec_map_triv _ (progEffSpec_dbDecryptTryPrev hEnv hDec spec.aad raw err spec.prevKeys)
  | _ => exact .pure _ trivial

private theorem progEffSpec_dbDecryptRow (hEnv : ∀ v, EffOk (.readEnv v)) (hDec : ∀ k f a c, EffOk (.aeadDecrypt k f a c)) :
    ∀ (encRead : List (Nat × EncColSpec)) (row : DbRow), ProgEffSpec Inv A Step EffOk (fun _ => True) (dbDecryptRow (m := ThreadProg σ) encRead row)
  | [], _ => .pure _ trivial
  | (_, spec) :: rest, _ => by
      dsimp only [dbDecryptRow]; split
      · exact progEffSpec_bind_triv (progEffSpec_dbDecryptVal hEnv hDec spec _) fun | .error _ => .pure _ trivial | .ok _ => progEffSpec_dbDecryptRow hEnv hDec rest _
      · exact .pure _ trivial

private theorem progEffSpec_dbDecryptResult (encRead : List (Nat × EncColSpec)) (res : DbResult)
    (hDec : encRead = [] ∨ ((∀ v, EffOk (.readEnv v)) ∧ (∀ k f a c, EffOk (.aeadDecrypt k f a c)))) :
    ProgEffSpec Inv A Step EffOk (fun _ => True) (dbDecryptResult (m := ThreadProg σ) encRead res) := by
  unfold dbDecryptResult; split
  · exact .pure _ trivial
  · rename_i hne; rcases hDec with rfl | ⟨hEnv, hD⟩
    · exact absurd rfl hne
    · exact progEffSpec_map_triv _ (progEffSpec_mapExceptList _ (progEffSpec_dbDecryptRow hEnv hD encRead) _)

private theorem progEffSpec_execDbMaybeTx {β : Type} {Post : β → Prop} (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64)
    (heff : EffOk (dbExecEff cfg q txId?)) (k : Except ApiError DbResult → ThreadProg σ β) (hk : ∀ r, ProgEffSpec Inv A Step EffOk Post (k r)) :
    ProgEffSpec Inv A Step EffOk Post (execDbMaybeTx (m := ThreadProg σ) cfg q txId? >>= k) := by
  cases txId? with | none => exact .io (.dbExec cfg q) k heff hk | some tid => exact .io (.dbTxExec cfg tid q) k heff hk

theorem progEffSpec_dbRunChecked {α : Type} {P : Prop} {Q Post : Except ApiError α → Prop}
    (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64)
    (post : DbResult → Except ApiError α) (hQPost : ∀ r, Q (post r)) (hQErr : ∀ e, Q (.error e)) (pf : P)
    (encWrite : List (String × EncColSpec)) (encRead : List (Nat × EncColSpec))
    (hEnc : encWrite = [] ∨ q.isWrite = false ∨ ∀ k' f a p, EffOk (.aeadEncrypt k' f a p))
    (hDb : ∀ q', q'.isWrite = q.isWrite → EffOk (dbExecEff cfg q' txId?))
    (hDec : encRead = [] ∨ ((∀ v, EffOk (.readEnv v)) ∧ (∀ k' f a c, EffOk (.aeadDecrypt k' f a c))))
    (hPost : ∀ a, Q a → Post a) :
    ProgEffSpec Inv A Step EffOk Post (dbRunChecked (Q := Q) (m := ThreadProg σ) cfg q txId? post hQPost hQErr pf encWrite encRead) :=
  (progEffSpec_dbEncryptQuery encWrite q hEnc).bind fun
    | .error e, _ => .pure _ (hPost _ (hQErr e))
    | .ok q', hq =>
        progEffSpec_execDbMaybeTx cfg q' txId? (hDb q' (hq q' rfl)) _ fun
          | .error e => .pure _ (hPost _ (hQErr e))
          | .ok raw => (progEffSpec_dbDecryptResult encRead raw hDec).bind fun
              | .error e, _ => .pure _ (hPost _ (hQErr e))
              | .ok dec, _ => .pure _ (hPost _ (hQPost dec))

theorem progEffSpec_dbRunChecked_bind {α β : Type} {P : Prop} {Q : Except ApiError α → Prop} {Post : β → Prop}
    (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64)
    (post : DbResult → Except ApiError α) (hQPost : ∀ r, Q (post r)) (hQErr : ∀ e, Q (.error e)) (pf : P)
    (encWrite : List (String × EncColSpec)) (encRead : List (Nat × EncColSpec))
    {k : Except ApiError α → ThreadProg σ β}
    (hEnc : encWrite = [] ∨ q.isWrite = false ∨ ∀ k' f a p, EffOk (.aeadEncrypt k' f a p))
    (hDb : ∀ q', q'.isWrite = q.isWrite → EffOk (dbExecEff cfg q' txId?))
    (hDec : encRead = [] ∨ ((∀ v, EffOk (.readEnv v)) ∧ (∀ k' f a c, EffOk (.aeadDecrypt k' f a c))))
    (hk : ∀ a, Q a → ProgEffSpec Inv A Step EffOk Post (k a)) :
    ProgEffSpec Inv A Step EffOk Post (dbRunChecked (Q := Q) (m := ThreadProg σ) cfg q txId? post hQPost hQErr pf encWrite encRead >>= k) :=
  (progEffSpec_dbRunChecked cfg q txId? post hQPost hQErr pf encWrite encRead hEnc hDb hDec fun _ h => h).bind hk
end ProgEff

instance {σ α : Type} {P : Prop} {Q : Except ApiError α → Prop}
    (cfg : DbConfig) (q : SqlQuery) (txId? : Option UInt64)
    (post : DbResult → Except ApiError α) (hPost : ∀ r, Q (post r)) (hErr : ∀ e, Q (.error e)) (pf : P)
    (encWrite : List (String × EncColSpec)) (encRead : List (Nat × EncColSpec)) :
    SafeIOEnsures (dbRunChecked (Q := Q) (m := ThreadProg σ) cfg q txId? post hPost hErr pf encWrite encRead) Q where
  noAtomic := progEffSpec_dbRunChecked cfg q txId? post hPost hErr pf encWrite encRead
    (.inr (.inr fun _ _ _ _ => trivial)) (fun _ _ => trivial) (.inr ⟨fun _ => trivial, fun _ _ _ _ => trivial⟩) (fun _ _ => trivial)
  ensures := progEffSpec_dbRunChecked cfg q txId? post hPost hErr pf encWrite encRead
    (.inr (.inr fun _ _ _ _ => trivial)) (fun _ _ => trivial) (.inr ⟨fun _ => trivial, fun _ _ _ _ => trivial⟩) (fun _ h => h)

private theorem and_inv_pred {Row : Type} {RowInv : Row → Prop} {rowInvBool pred : Row → Bool}
    (hInvSound : ∀ r, rowInvBool r = true → RowInv r) (r : Row) (h : (rowInvBool r && pred r) = true) :
    RowInv r ∧ pred r = true := by simp only [Bool.and_eq_true] at h; exact ⟨hInvSound r h.1, h.2⟩

private theorem srvEnsPost_ok_pf {α : Type} {P : α → Prop} {a : α} (h : P a) : srvEnsPost (ε := ApiError) P (.ok a) := h
private theorem srvEnsPost_err_pf {α : Type} {P : α → Prop} (e : ApiError) : srvEnsPost P (.error e) := trivial
private theorem srvEnsPostOpt_err_pf {α : Type} {P : α → Prop} (e : ApiError) : srvEnsPostOpt P (.error e) := trivial

section DbOps
variable {Row : Type} {m : Type → Type} [Monad m] [MonadServer m]

abbrev dbRunRows {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (pf : P) (pred : Row → Bool := fun _ => true)
    (errMsg : String := "database row violated verified table invariant or query predicate")
    (txId? : Option UInt64 := none) (encWrite : List (String × EncColSpec) := []) (encRead : List (Nat × EncColSpec) := []) :
    m (Except ApiError (Array Row)) :=
  dbRunChecked (Q := dbArrPost fun r => RowInv r ∧ pred r = true) cfg q txId?
    (decodeCheckedArr (decodeRowErr decode) (fun r => rowInvBool r && pred r) errMsg)
    (decodeCheckedArr_post _ _ _ (and_inv_pred hInvSound)) (fun _ => trivial) pf encWrite encRead

abbrev dbRunOneRow {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (pf : P) (pred : Row → Bool := fun _ => true)
    (errMsg : String := "database row violated verified table invariant or query predicate")
    (txId? : Option UInt64 := none) (encWrite : List (String × EncColSpec) := []) (encRead : List (Nat × EncColSpec) := []) :
    m (Except ApiError (Option Row)) :=
  dbRunChecked (Q := srvEnsPostOpt fun r => RowInv r ∧ pred r = true) cfg q txId?
    (decodeCheckedOne decode (fun r => rowInvBool r && pred r) errMsg)
    (decodeCheckedOne_post _ _ _ (and_inv_pred hInvSound)) srvEnsPostOpt_err_pf pf encWrite encRead

abbrev dbSelectProj {Proj : Type} {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Proj)
    (pf : P) (txId? : Option UInt64 := none) (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError (Array Proj)) :=
  dbRunChecked (Q := fun _ => True) cfg q txId?
    (fun dbRes => (dbRes.rows.toList.mapM (decodeRowErr decode)).map List.toArray)
    (fun _ => trivial) (fun _ => trivial) pf [] encRead

abbrev dbFindOneProj {Proj : Type} {P : Prop} (cfg : DbConfig) (q : SqlQuery) (decode : DbRow → Except String Proj)
    (pf : P) (txId? : Option UInt64 := none) (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError (Option Proj)) :=
  dbRunChecked (Q := fun _ => True) cfg q txId?
    (fun dbRes => match dbRes.rows[0]? with | none => .ok none | some r => (decodeRowErr decode r).map some)
    (fun _ => trivial) (fun _ => trivial) pf [] encRead

abbrev dbCount {P : Prop} (cfg : DbConfig) (q : SqlQuery) (pf : P) (txId? : Option UInt64 := none) : m (Except ApiError Nat) :=
  dbRun cfg q txId? (decodeFirstCell (α := Nat) id none 0 "COUNT") pf
abbrev dbSumNat {P : Prop} (cfg : DbConfig) (q : SqlQuery) (pf : P) (txId? : Option UInt64 := none) : m (Except ApiError Nat) :=
  dbRun cfg q txId? (decodeFirstCell (α := Nat) id (some 0) 0 "SUM") pf
abbrev dbSumInt {P : Prop} (cfg : DbConfig) (q : SqlQuery) (pf : P) (txId? : Option UInt64 := none) : m (Except ApiError Int) :=
  dbRun cfg q txId? (decodeFirstCell (α := Int) id (some 0) 0 "SUM") pf
abbrev dbAggOpt {Val : Type} [FromSql Val] {P : Prop} (cfg : DbConfig) (q : SqlQuery) (_proj : Row → Val) (pf : P) (txId? : Option UInt64 := none) : m (Except ApiError (Option Val)) :=
  dbRun cfg q txId? (decodeFirstCell (α := Val) some (some none) none "aggregate") pf
abbrev dbDelete {P : Prop} (cfg : DbConfig) (q : SqlQuery) (pf : P) (txId? : Option UInt64 := none) : m (Except ApiError Nat) :=
  dbRun cfg q txId? (fun dbRes => .ok dbRes.affected) pf

@[inline] def fromSqlOfField {R α : Type} [FromSql α] (_ : R → α) (v : SqlVal) : Except String α := FromSql.fromSql v

abbrev dbInsert (cfg : DbConfig) (q : SqlQuery) (newRow : Row) (RowInv : Row → Prop) (InsertPolicy : RequestCtx → Row → Prop)
    (ctx : RequestCtx) (hInv : RowInv newRow) (hPolicy : InsertPolicy ctx newRow) (txId? : Option UInt64 := none)
    (encWrite : List (String × EncColSpec) := []) : m (Except ApiError Row) :=
  dbRunChecked (Q := srvEnsPost fun r => r = newRow ∧ RowInv r)
    cfg q txId? (fun _ => .ok newRow) (fun _ => srvEnsPost_ok_pf (P := fun r => r = newRow ∧ RowInv r) ⟨rfl, hInv⟩) srvEnsPost_err_pf hPolicy encWrite []

abbrev dbInsertOrIgnore (cfg : DbConfig) (q : SqlQuery) (newRow : Row) (RowInv : Row → Prop) (InsertPolicy : RequestCtx → Row → Prop)
    (ctx : RequestCtx) (hInv : RowInv newRow) (hPolicy : InsertPolicy ctx newRow) (txId? : Option UInt64 := none)
    (encWrite : List (String × EncColSpec) := []) : m (Except ApiError (Option Row)) :=
  dbRunChecked (Q := srvEnsPostOpt fun r => r = newRow ∧ RowInv r)
    cfg q txId? (fun dbRes => .ok (if dbRes.rows.isEmpty then none else some newRow))
    (fun dbRes => by cases hE : dbRes.rows.isEmpty <;> simp [srvEnsPostOpt, hInv]) srvEnsPostOpt_err_pf hPolicy encWrite []

abbrev dbUpsert (cfg : DbConfig) (q : SqlQuery) (newRow : Row) (decode : DbRow → Except String Row)
    (RowInv : Row → Prop) (rowInvBool : Row → Bool) (hInvSound : ∀ r, rowInvBool r = true → RowInv r)
    (TransInv : Row → Row → Prop) (conflictPred : Row → Bool)
    (InsertPolicy UpdatePolicy : RequestCtx → Row → Prop) (ctx : RequestCtx)
    (hInv : RowInv newRow) (hInsPol : InsertPolicy ctx newRow) (hUpdPolNew : UpdatePolicy ctx newRow)
    (hUpdPolOld : ∀ r, RowInv r → conflictPred r = true → UpdatePolicy ctx r)
    (hTrans : ∀ r, RowInv r → conflictPred r = true → TransInv r newRow)
    (txId? : Option UInt64 := none)
    (encWrite : List (String × EncColSpec) := []) (encRead : List (Nat × EncColSpec) := []) : m (Except ApiError Row) :=
  dbRunChecked (Q := srvEnsPost RowInv)
    cfg q txId?
    (fun dbRes =>
      match decodeCheckedOne decode rowInvBool "upserted database row violated verified table invariant" dbRes with
      | .error e => .error e
      | .ok (some r) => .ok r
      | .ok none => .error (ApiError.forbidden "upsert conflict rejected by policy"))
    (fun dbRes => by
      have h := decodeCheckedOne_post decode rowInvBool "upserted database row violated verified table invariant" hInvSound dbRes
      cases hd : decodeCheckedOne decode rowInvBool "upserted database row violated verified table invariant" dbRes with
      | error _ => trivial
      | ok opt => cases opt with | none => trivial | some _ => rw [hd] at h; exact h)
    srvEnsPost_err_pf (And.intro hInv (And.intro hInsPol (And.intro hUpdPolNew (And.intro hUpdPolOld hTrans)))) encWrite encRead

end DbOps

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
  | litTrue | cmp (op : SqlBinOp) (col : String) (val : SqlVal) | isNull (col : String) | isNotNull (col : String)
  | and (a b : DbFilter) | or (a b : DbFilter) | not (a : DbFilter)

private def resolveDbCol (tblName : String) (cols : List SqlIdent) (col : String) : Except ApiError SqlIdent :=
  (cols.find? (·.raw == col)).elim (.error (ApiError.badRequest s!"unknown column `{col}` on table `{tblName}`")) .ok

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
  | .and a b => (toSqlExpr tblName cols a).bind fun ea => (toSqlExpr tblName cols b).map (.binOp .and ea)
  | .or a b => (toSqlExpr tblName cols a).bind fun ea => (toSqlExpr tblName cols b).map (.binOp .or ea)
  | .not a => (toSqlExpr tblName cols a).map .not
end DbFilter

inductive DbSetRhs where | val (v : SqlVal) | add (delta : SqlVal) | sub (delta : SqlVal) deriving Inhabited

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
    (dec : DbResult → Except ApiError α) (doEnc doDec : Bool) (encRead? : Option (List (Nat × EncColSpec)) := none) : m (Except ApiError α) :=
  match qRes with
  | .error e => pure (.error e)
  | .ok q => dbRunChecked (Q := fun _ => True) h.config q txId? dec (fun _ => trivial) (fun _ => trivial) trivial
      (if doEnc then h.encWrite else []) (encRead?.getD (if doDec then h.encRead else []))

private def mkSelectQuery (h : TableHandle Row) (cols : List SqlIdent) (where_ : DbFilter)
    (orderBy? : Option (String × Bool)) (limit? offset? : Option Nat) : Except ApiError SqlQuery := do
  let wExpr ← where_.toSqlExpr h.tableName.raw h.columns
  let ob ← orderBy?.mapM fun (col, asc) => (·, if asc then SqlOrderDir.asc else SqlOrderDir.desc) <$> h.resolveCol col
  return .select h.tableName cols wExpr ob limit? offset?

private def checkRowInv (h : TableHandle Row) (row : Row) : Except ApiError Unit :=
  if h.rowInvBool row then .ok () else .error (ApiError.badRequest s!"row violated table invariant for `{h.tableName.raw}`")

private def decCheckedRows (h : TableHandle Row) (lbl : String) : DbResult → Except ApiError (Array Row) :=
  decodeCheckedArr (decodeRowErr h.decodeRow) h.rowInvBool s!"{lbl} row in `{h.tableName.raw}` violated table invariant"

private def decCheckedOne (h : TableHandle Row) (lbl : String) : DbResult → Except ApiError (Option Row) :=
  decodeCheckedOne h.decodeRow h.rowInvBool s!"{lbl} row in `{h.tableName.raw}` violated table invariant"

def select (h : TableHandle Row) (where_ : DbFilter := .litTrue) (orderBy? : Option (String × Bool) := none)
    (limit? : Option Nat := none) (offset? : Option Nat := none) (txId? : Option UInt64 := none) : m (Except ApiError (Array Row)) :=
  runDec h (mkSelectQuery h h.columns where_ orderBy? limit? offset?) txId? (h.decCheckedRows "database") false true

def findOne (h : TableHandle Row) (where_ : DbFilter) (orderBy? : Option (String × Bool) := none)
    (txId? : Option UInt64 := none) : m (Except ApiError (Option Row)) :=
  (·.map (·[0]?)) <$> h.select where_ orderBy? (limit? := some 1) (txId? := txId?)

def selectProjected {Proj : Type} (h : TableHandle Row) (cols : List String)
    (decode : DbRow → Except String Proj) (where_ : DbFilter := .litTrue)
    (orderBy? : Option (String × Bool) := none) (limit? : Option Nat := none) (offset? : Option Nat := none)
    (txId? : Option UInt64 := none) : m (Except ApiError (Array Proj)) :=
  match (if cols.isEmpty then .error (ApiError.badRequest s!"projected select on `{h.tableName.raw}` requires at least one column")
         else cols.mapM h.resolveCol) with
  | .error e => pure (.error e)
  | .ok colIds =>
      let projEncRead := colIds.zipIdx.filterMap fun (cid, i) => (h.encWrite.lookup cid.raw).map (i, ·)
      runDec h (mkSelectQuery h colIds where_ orderBy? limit? offset?) txId?
        (fun dr => (dr.rows.toList.mapM (decodeRowErr decode)).map List.toArray) false false (some projEncRead)

def count (h : TableHandle Row) (where_ : DbFilter := .litTrue) (txId? : Option UInt64 := none) : m (Except ApiError Nat) :=
  runDec h (do return .count h.tableName (← where_.toSqlExpr h.tableName.raw h.columns)) txId?
    (decodeFirstCell (α := Int) Int.toNat none 0 "count") false false

def insert (h : TableHandle Row) (row : Row) (txId? : Option UInt64 := none) : m (Except ApiError Row) :=
  runDec h (do h.checkRowInv row; return .insert h.tableName (h.encodeRow row) h.columns) txId?
    (fun dbRes => match h.decCheckedOne "inserted" dbRes with
      | .error e => .error e | .ok (some r) => .ok r | .ok none => .error (ApiError.internal s!"insert into `{h.tableName.raw}` returned no row")) true true

def insertOrIgnore (h : TableHandle Row) (row : Row) (conflictCols : List String := [])
    (txId? : Option UInt64 := none) : m (Except ApiError (Option Row)) :=
  runDec h (do
    h.checkRowInv row; let ccs ← conflictCols.mapM h.resolveCol
    for cc in ccs do if (h.encWrite.lookup cc.raw).isSome then throw (ApiError.badRequest s!"cannot use encrypted column `{cc.raw}` as conflict target in `{h.tableName.raw}`")
    return .insertOrIgnore h.tableName (h.encodeRow row) ccs (h.columns.take 1)) txId?
    (fun dbRes => .ok (if dbRes.rows.isEmpty then none else some row)) true false

def upsert (h : TableHandle Row) (row : Row) (conflictCols : List String) (updateCols : List String)
    (conflictWhere? : Option DbFilter := none) (txId? : Option UInt64 := none) : m (Except ApiError (Option Row)) :=
  runDec h (do
    h.checkRowInv row
    if conflictCols.isEmpty then throw (ApiError.badRequest s!"upsert on `{h.tableName.raw}` requires at least one conflict column")
    return .upsert h.tableName (h.encodeRow row) (← conflictCols.mapM h.resolveCol) (← updateCols.mapM h.resolveCol)
      (← conflictWhere?.mapM (·.toSqlExpr h.tableName.raw h.columns)) h.columns) txId? (h.decCheckedOne "upserted") true true

private def runUpdate {α : Type} (h : TableHandle Row) (sets : List (String × DbSetRhs)) (where_ : DbFilter)
    (retCols : List SqlIdent) (dec : DbResult → Except ApiError α) (doDec : Bool) (txId? : Option UInt64) : m (Except ApiError α) :=
  runDec h (do
    if sets.isEmpty then throw (ApiError.badRequest s!"update on `{h.tableName.raw}` requires at least one column assignment")
    let sPairs ← sets.mapM fun (c, rhs) => do
      let cid ← h.resolveCol c
      return (cid, match rhs with | .val v => .param v | .add v => .binOp .add (.col cid) (.param v) | .sub v => .binOp .sub (.col cid) (.param v))
    return .update h.tableName sPairs (← where_.toSqlExpr h.tableName.raw h.columns) retCols) txId? dec true doDec

def update (h : TableHandle Row) (sets : List (String × DbSetRhs)) (where_ : DbFilter := .litTrue) (txId? : Option UInt64 := none) : m (Except ApiError Nat) :=
  runUpdate h sets where_ [] (fun r => .ok r.affected) false txId?

def updateReturning (h : TableHandle Row) (sets : List (String × DbSetRhs)) (where_ : DbFilter := .litTrue) (txId? : Option UInt64 := none) : m (Except ApiError (Array Row)) :=
  runUpdate h sets where_ h.columns (h.decCheckedRows "updated") true txId?

def updateOneReturning (h : TableHandle Row) (sets : List (String × DbSetRhs)) (where_ : DbFilter := .litTrue) (txId? : Option UInt64 := none) : m (Except ApiError (Option Row)) :=
  runUpdate h sets where_ h.columns (h.decCheckedOne "updated") true txId?

def delete (h : TableHandle Row) (where_ : DbFilter) (txId? : Option UInt64 := none) : m (Except ApiError Nat) :=
  runDec h (do return .delete h.tableName (← where_.toSqlExpr h.tableName.raw h.columns) []) txId? (fun r => .ok r.affected) false false

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

end Qed.Server.Db
