import Qed.Speculative.Core

namespace Qed

namespace SpecEngine

/-! ## Core Invariant & Coherence Proofs -/

/-- Coherence property: `visible` always equals replaying `log` from `confirmed`. -/
def Coherent {State Msg : Type} (stepOnly : State → Msg → State) (st : SpecState State Msg) : Prop :=
  st.visible = st.log.foldl (replayEntry stepOnly) st.confirmed

/-- Both `confirmed` and `visible` states satisfy the component invariant `Inv`. -/
def SpecInv {State Msg : Type} (Inv : State → Prop) (st : SpecState State Msg) : Prop :=
  Inv st.confirmed ∧ Inv st.visible

/-- Pending transaction IDs currently in the speculative journal, in dispatch order. -/
def pendingIds {Msg : Type} : List (SpecEntry Msg) → List Nat
  | []                  => []
  | .pending id _ :: es => id :: pendingIds es
  | .regular _ :: es    => pendingIds es
  | .resolved _ :: es   => pendingIds es

/-- Well-formed transaction ID invariant: every pending ID in `log` is strictly below `nextTxId`
    and all pending IDs are distinct. -/
def WellFormedIds {State Msg : Type} (st : SpecState State Msg) : Prop :=
  (∀ id ∈ pendingIds st.log, id < st.nextTxId) ∧ (pendingIds st.log).Nodup

@[simp] theorem pendingIds_nil {Msg : Type} : pendingIds ([] : List (SpecEntry Msg)) = [] := rfl
@[simp] theorem pendingIds_cons_regular {Msg : Type} (m : Msg) (es : List (SpecEntry Msg)) :
    pendingIds (.regular m :: es) = pendingIds es := rfl
@[simp] theorem pendingIds_cons_resolved {Msg : Type} (m : Msg) (es : List (SpecEntry Msg)) :
    pendingIds (.resolved m :: es) = pendingIds es := rfl
@[simp] theorem pendingIds_cons_pending {Msg : Type} (id : Nat) (m : Msg) (es : List (SpecEntry Msg)) :
    pendingIds (.pending id m :: es) = id :: pendingIds es := rfl

theorem pendingIds_append {Msg : Type} (a b : List (SpecEntry Msg)) :
    pendingIds (a ++ b) = pendingIds a ++ pendingIds b := by
  induction a with
  | nil => rfl
  | cons e _ ih => cases e <;> simp [pendingIds, ih]

theorem pendingIds_map_resolved {Msg : Type} (ms : List Msg) :
    pendingIds (ms.map SpecEntry.resolved) = [] := by
  induction ms with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem foldl_replayEntry_eq_map {State Msg : Type} (stepOnly : State → Msg → State) :
    ∀ (log : List (SpecEntry Msg)) (s : State),
      log.foldl (replayEntry stepOnly) s = (log.map entryMsg).foldl stepOnly s
  | [], _ => rfl
  | _ :: rest, _ => foldl_replayEntry_eq_map stepOnly rest _

theorem runMsgs_fst_eq_foldl {State Msg : Type} (upd : State → Msg → State × Cmd Msg) :
    ∀ (ms : List Msg) (s : State),
      (runMsgs upd s ms).1 = ms.foldl (fun acc m => (upd acc m).1) s
  | [], _ => rfl
  | m :: ms, s => runMsgs_fst_eq_foldl upd ms (upd s m).1

theorem replayEntry_preserves_inv {State Msg : Type} {Inv : State → Prop}
    {stepOnly : State → Msg → State}
    (hstep : ∀ s m, Inv s → Inv (stepOnly s m))
    {s : State} (hs : Inv s) (e : SpecEntry Msg) :
    Inv (replayEntry stepOnly s e) :=
  hstep s (entryMsg e) hs

theorem replay_preserves_inv {State Msg : Type} {Inv : State → Prop}
    {stepOnly : State → Msg → State}
    (hstep : ∀ s m, Inv s → Inv (stepOnly s m)) :
    ∀ (log : List (SpecEntry Msg)) (s : State), Inv s → Inv (log.foldl (replayEntry stepOnly) s)
  | [], _, hs => hs
  | e :: rest, s, hs =>
      replay_preserves_inv hstep rest (replayEntry stepOnly s e) (replayEntry_preserves_inv hstep hs e)

theorem drainConfirmed_preserves_inv {State Msg : Type} {Inv : State → Prop}
    {stepOnly : State → Msg → State}
    (hstep : ∀ s m, Inv s → Inv (stepOnly s m)) :
    ∀ (log : List (SpecEntry Msg)) (conf : State), Inv conf →
      Inv (drainConfirmed stepOnly conf log).1
  | [], _, hc => hc
  | .regular m :: rest, conf, hc | .resolved m :: rest, conf, hc =>
      drainConfirmed_preserves_inv hstep rest (stepOnly conf m) (hstep conf m hc)
  | .pending _ _ :: _, _, hc => hc

theorem drainConfirmed_foldl_eq {State Msg : Type} (stepOnly : State → Msg → State) :
    ∀ (log : List (SpecEntry Msg)) (conf : State),
      let res := drainConfirmed stepOnly conf log
      res.2.foldl (replayEntry stepOnly) res.1 = log.foldl (replayEntry stepOnly) conf
  | [], _ => rfl
  | .regular m :: rest, conf | .resolved m :: rest, conf =>
      drainConfirmed_foldl_eq stepOnly rest (stepOnly conf m)
  | .pending _ _ :: _, _ => rfl

theorem drainConfirmed_pendingIds {State Msg : Type} (stepOnly : State → Msg → State) :
    ∀ (log : List (SpecEntry Msg)) (conf : State),
      pendingIds (drainConfirmed stepOnly conf log).2 = pendingIds log
  | [], _ => rfl
  | .regular m :: rest, conf | .resolved m :: rest, conf =>
      drainConfirmed_pendingIds stepOnly rest (stepOnly conf m)
  | .pending _ _ :: _, _ => rfl

theorem drainConfirmed_empty_of_no_pending {State Msg : Type} (stepOnly : State → Msg → State) :
    ∀ (log : List (SpecEntry Msg)) (conf : State),
      pendingIds log = [] →
      drainConfirmed stepOnly conf log = (log.foldl (replayEntry stepOnly) conf, [])
  | [], _, _ => rfl
  | .regular m :: rest, conf, h | .resolved m :: rest, conf, h =>
      drainConfirmed_empty_of_no_pending stepOnly rest (stepOnly conf m) h
  | .pending _ _ :: _, _, h => by simp at h

theorem drainConfirmed_append_resolved {State Msg : Type} (stepOnly : State → Msg → State) :
    ∀ (ms : List Msg) (tail : List (SpecEntry Msg)) (conf : State),
      drainConfirmed stepOnly conf (ms.map SpecEntry.resolved ++ tail) =
        drainConfirmed stepOnly (ms.foldl stepOnly conf) tail
  | [], _, _ => rfl
  | m :: ms, tail, conf => drainConfirmed_append_resolved stepOnly ms tail (stepOnly conf m)

theorem runMsgs_preserves_inv {State Msg : Type} {Inv : State → Prop}
    {upd : State → Msg → State × Cmd Msg}
    (hupd : ∀ s m, Inv s → Inv (upd s m).1) :
    ∀ (ms : List Msg) (s : State), Inv s → Inv (runMsgs upd s ms).1
  | [], _, hs => hs
  | m :: ms, s, hs => runMsgs_preserves_inv hupd ms (upd s m).1 (hupd s m hs)

private theorem resolveReplace_preserves_inv {State Msg : Type} {Inv : State → Prop}
    (upd : State → Msg → State × Cmd Msg) (hupd : ∀ s m, Inv s → Inv (upd s m).1)
    (txId : Nat) (replMsgs : List Msg) (st : SpecState State Msg) (h : SpecInv Inv st) :
    SpecInv Inv (resolveReplace upd txId replMsgs st).1 := by
  unfold resolveReplace; dsimp only; split
  · exact h
  · have hc' := drainConfirmed_preserves_inv hupd
      (replacePending upd txId replMsgs st.confirmed st.log).1 st.confirmed h.1
    exact ⟨hc', replay_preserves_inv hupd _ _ hc'⟩

private theorem resolveReplace_preserves_coherent {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg)
    (txId : Nat) (replMsgs : List Msg) (st : SpecState State Msg)
    (hcoh : Coherent (fun s m => (upd s m).1) st) :
    Coherent (fun s m => (upd s m).1) (resolveReplace upd txId replMsgs st).1 := by
  unfold resolveReplace; dsimp only; split
  · exact hcoh
  · rfl

theorem step_preserves_inv {State Msg : Type} {Inv : State → Prop}
    (upd : State → Msg → State × Cmd Msg)
    (classify : State → Msg → SpecAction Msg)
    (hupd : ∀ s m, Inv s → Inv (upd s m).1)
    (st : SpecState State Msg) (msg : Msg)
    (h : SpecInv Inv st) :
    SpecInv Inv (SpecEngine.step upd classify st msg).1 := by
  rcases h with ⟨hconf, hvis⟩
  unfold SpecEngine.step; dsimp only
  cases classify st.visible msg with
  | normal =>
      dsimp only; split
      · exact ⟨hupd _ _ hvis, hupd _ _ hvis⟩
      · exact ⟨hconf, hupd _ _ hvis⟩
  | dispatch preMsg? _ specMsg _ =>
      dsimp only
      cases preMsg? with
      | none => exact ⟨hconf, hupd _ _ hvis⟩
      | some pm =>
          dsimp only; have hv1 := hupd st.visible pm hvis
          split
          · exact ⟨hv1, hupd _ _ hv1⟩
          · exact ⟨hconf, hupd _ _ hv1⟩
  | resolve txId hit replMsgs confirmOnHit =>
      dsimp only
      cases st.log with
      | nil => exact resolveReplace_preserves_inv upd hupd txId replMsgs st ⟨hconf, hvis⟩
      | cons e tail =>
          cases e with
          | pending id0 m0 =>
              dsimp only; split
              · have hc1 := hupd st.confirmed m0 hconf
                split
                · exact ⟨drainConfirmed_preserves_inv hupd tail _ hc1, hvis⟩
                · have hc2 := runMsgs_preserves_inv hupd confirmOnHit _ hc1
                  have hc3 := drainConfirmed_preserves_inv hupd tail _ hc2
                  exact ⟨hc3, replay_preserves_inv hupd _ _ hc3⟩
              · exact resolveReplace_preserves_inv upd hupd txId replMsgs st ⟨hconf, hvis⟩
          | regular _ | resolved _ =>
              exact resolveReplace_preserves_inv upd hupd txId replMsgs st ⟨hconf, hvis⟩

theorem step_preserves_coherent {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg)
    (classify : State → Msg → SpecAction Msg)
    (st : SpecState State Msg) (msg : Msg)
    (hcoh : Coherent (fun s m => (upd s m).1) st) :
    Coherent (fun s m => (upd s m).1) (SpecEngine.step upd classify st msg).1 := by
  unfold SpecEngine.step; dsimp only
  cases classify st.visible msg with
  | normal =>
      dsimp only; split
      · rename_i hemp; simp [Coherent, List.isEmpty_iff.1 hemp]
      · unfold Coherent at hcoh ⊢; simp [List.foldl_append, replayEntry, entryMsg, hcoh]
  | dispatch preMsg? _ specMsg _ =>
      dsimp only
      cases preMsg? with
      | none => unfold Coherent at hcoh ⊢; simp [List.foldl_append, replayEntry, entryMsg, hcoh]
      | some pm =>
          dsimp only; split
          · simp [Coherent, replayEntry, entryMsg]
          · unfold Coherent at hcoh ⊢; simp [List.foldl_append, replayEntry, entryMsg, hcoh]
  | resolve txId hit replMsgs confirmOnHit =>
      dsimp only
      cases hlog : st.log with
      | nil => exact resolveReplace_preserves_coherent upd txId replMsgs st hcoh
      | cons e tail =>
          cases e with
          | pending id0 m0 =>
              dsimp only; split
              · split
                · unfold Coherent at hcoh ⊢; dsimp only
                  rw [drainConfirmed_foldl_eq]
                  simpa [hlog, List.foldl_cons, replayEntry] using hcoh
                · rfl
              · exact resolveReplace_preserves_coherent upd txId replMsgs st hcoh
          | regular _ | resolved _ =>
              exact resolveReplace_preserves_coherent upd txId replMsgs st hcoh

/-! ## Multi-Transaction Linearizability, Hit Soundness, Zero-Leak Drain & Effect-Once Proofs -/

theorem replacePending_not_mem {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg) (txId : Nat) (replMsgs : List Msg) :
    ∀ (log : List (SpecEntry Msg)) (sCur : State),
      txId ∉ pendingIds log →
      replacePending upd txId replMsgs sCur log = (log, [], false)
  | [], _, _ => rfl
  | .regular m :: rest, sCur, h | .resolved m :: rest, sCur, h => by
      simp [replacePending, replayEntry, entryMsg, replacePending_not_mem upd txId replMsgs rest _ h]
  | .pending id m :: rest, sCur, h => by
      have hbeq : (id == txId) = false := beq_false_of_ne (fun heq => h (by simp [heq]))
      have ih := replacePending_not_mem upd txId replMsgs rest (upd sCur m).1 (fun hm => h (by simp [hm]))
      simp [replacePending, hbeq, ih]

/-- Exact characterization of `replacePending` on an arbitrary multi-transaction journal
    `pre ++ [.pending txId specMsg] ++ post` where `txId ∉ pendingIds pre`. -/
theorem replacePending_split {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg) (txId : Nat) (specMsg : Msg) (replMsgs : List Msg) :
    ∀ (pre post : List (SpecEntry Msg)) (sCur : State),
      txId ∉ pendingIds pre →
      replacePending upd txId replMsgs sCur (pre ++ .pending txId specMsg :: post) =
        (pre ++ replMsgs.map SpecEntry.resolved ++ post,
         (runMsgs upd (pre.foldl (replayEntry (fun s m => (upd s m).1)) sCur) replMsgs).2,
         true)
  | [], _, _, _ => by simp [replacePending]
  | .regular m :: pre, post, sCur, h | .resolved m :: pre, post, sCur, h => by
      simp [replacePending, replayEntry, entryMsg,
        replacePending_split upd txId specMsg replMsgs pre post _ h]
  | .pending id m :: pre, post, sCur, h => by
      have hbeq : (id == txId) = false := beq_false_of_ne (fun heq => h (by simp [heq]))
      have ih := replacePending_split upd txId specMsg replMsgs pre post (upd sCur m).1
        (fun hm => h (by simp [hm]))
      simp [replacePending, replayEntry, entryMsg, hbeq, ih]

theorem wellFormedIds_pure {State Msg : Type} (s : State) :
    WellFormedIds (SpecState.pure (Msg := Msg) s) :=
  ⟨fun _ h => by simp at h, List.nodup_nil⟩

private theorem pendingIds_replacePending_sub {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg) (txId : Nat) (replMsgs : List Msg) :
    ∀ (log : List (SpecEntry Msg)) (sCur : State),
      (∀ id ∈ pendingIds (replacePending upd txId replMsgs sCur log).1, id ∈ pendingIds log) ∧
      ((pendingIds log).Nodup → (pendingIds (replacePending upd txId replMsgs sCur log).1).Nodup)
  | [], _ => ⟨fun _ h => h, id⟩
  | .regular m :: rest, sCur | .resolved m :: rest, sCur => by
      simpa [replacePending, replayEntry] using
        pendingIds_replacePending_sub upd txId replMsgs rest (upd sCur m).1
  | .pending id m :: rest, sCur => by
      by_cases heq : id = txId
      · subst heq
        simp only [replacePending, beq_self_eq_true, ↓reduceIte, pendingIds_append,
          pendingIds_map_resolved, List.nil_append, pendingIds_cons_pending]
        exact ⟨fun _ hx => List.mem_cons_of_mem id hx, fun hnd => (List.nodup_cons.1 hnd).2⟩
      · have hbeq : (id == txId) = false := beq_false_of_ne heq
        have ⟨hsub, hnd⟩ := pendingIds_replacePending_sub upd txId replMsgs rest (upd sCur m).1
        simp only [replacePending, hbeq, Bool.false_eq_true, ↓reduceIte, pendingIds_cons_pending]
        refine ⟨fun x hx => ?_, fun hnodup => ?_⟩
        · rcases List.mem_cons.1 hx with rfl | hx'
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem id (hsub x hx')
        · rcases List.nodup_cons.1 hnodup with ⟨hnotmem, hrest⟩
          exact List.nodup_cons.2 ⟨fun hin => hnotmem (hsub id hin), hnd hrest⟩

private theorem nodup_append_singleton {α : Type} {l : List α} {x : α}
    (hnd : l.Nodup) (hnot : x ∉ l) : (l ++ [x]).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rcases List.nodup_cons.1 hnd with ⟨ha, ht⟩
      exact List.nodup_cons.2 ⟨by simp [ha, show a ≠ x from fun h => hnot (by simp [h])],
        ih ht (fun h => hnot (List.mem_cons_of_mem a h))⟩

private theorem resolveReplace_preserves_wellFormedIds {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg) (txId : Nat) (replMsgs : List Msg)
    (st : SpecState State Msg) (hwf : WellFormedIds st) :
    WellFormedIds (resolveReplace upd txId replMsgs st).1 := by
  unfold resolveReplace; dsimp only; split
  · exact hwf
  · have ⟨hsub, hndR⟩ := pendingIds_replacePending_sub upd txId replMsgs st.log st.confirmed
    exact ⟨fun id hid => hwf.1 id (hsub id (by rwa [drainConfirmed_pendingIds] at hid)),
           by rw [drainConfirmed_pendingIds]; exact hndR hwf.2⟩

theorem step_preserves_wellFormedIds {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg)
    (classify : State → Msg → SpecAction Msg)
    (st : SpecState State Msg) (msg : Msg)
    (hwf : WellFormedIds st) :
    WellFormedIds (SpecEngine.step upd classify st msg).1 := by
  rcases hwf with ⟨hlt, hnd⟩
  have hpush : ∀ (l : List (SpecEntry Msg)), (∀ id ∈ pendingIds l, id < st.nextTxId) →
      (pendingIds l).Nodup →
      (∀ id ∈ pendingIds l ++ [st.nextTxId], id < st.nextTxId + 1) ∧
      (pendingIds l ++ [st.nextTxId]).Nodup := by
    intro l hl hn
    refine ⟨fun id hid => ?_, nodup_append_singleton hn (fun hm => Nat.lt_irrefl _ (hl _ hm))⟩
    rcases List.mem_append.1 hid with h1 | h2
    · exact Nat.lt_succ_of_lt (hl id h1)
    · simp only [List.mem_singleton] at h2; subst h2; exact Nat.lt_succ_self _
  unfold SpecEngine.step; dsimp only
  cases classify st.visible msg with
  | normal =>
      dsimp only; split
      · exact ⟨hlt, hnd⟩
      · simpa [WellFormedIds, pendingIds_append] using And.intro hlt hnd
  | dispatch preMsg? _ _ _ =>
      dsimp only
      cases preMsg? with
      | none =>
          simpa [WellFormedIds, pendingIds_append] using hpush st.log hlt hnd
      | some _ =>
          dsimp only; split
          · simp [WellFormedIds, hpush [] (fun _ h => by simp at h) List.nodup_nil]
          · simpa [WellFormedIds, pendingIds_append] using hpush st.log hlt hnd
  | resolve txId hit replMsgs confirmOnHit =>
      dsimp only
      cases hlog : st.log with
      | nil => exact resolveReplace_preserves_wellFormedIds upd txId replMsgs st ⟨hlt, hnd⟩
      | cons e tail =>
          cases e with
          | pending id0 m0 =>
              dsimp only; split
              · have hltT : ∀ id ∈ pendingIds tail, id < st.nextTxId :=
                  fun id hid => hlt id (by simp [hlog, hid])
                have hndT : (pendingIds tail).Nodup :=
                  (List.nodup_cons.1 (by simpa [hlog] using hnd)).2
                split <;>
                  exact ⟨fun id hid => hltT id (by rwa [drainConfirmed_pendingIds] at hid),
                         by rw [drainConfirmed_pendingIds]; exact hndT⟩
              · exact resolveReplace_preserves_wellFormedIds upd txId replMsgs st ⟨hlt, hnd⟩
          | regular _ | resolved _ =>
              exact resolveReplace_preserves_wellFormedIds upd txId replMsgs st ⟨hlt, hnd⟩

/-- Prediction-hit stability: when the head prediction matches (`hit = true`) and there are no
    `on_confirm` state updates (`confirmOnHit = []`), `visible` is provably untouched. -/
theorem resolve_hit_preserves_visible {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg)
    (classify : State → Msg → SpecAction Msg)
    (st : SpecState State Msg) (msg : Msg)
    (txId : Nat) (m0 : Msg) (tail : List (SpecEntry Msg)) (replMsgs : List Msg)
    (hlog : st.log = .pending txId m0 :: tail)
    (hcl : classify st.visible msg = .resolve txId true replMsgs []) :
    (SpecEngine.step upd classify st msg).1.visible = st.visible := by
  simp [SpecEngine.step, hcl, hlog]

/-- Duplicate / stale resolution safety: resolving a `txId` not pending in `st.log` is `(st, .none)`. -/
theorem resolve_unknown_noop {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg)
    (classify : State → Msg → SpecAction Msg)
    (st : SpecState State Msg) (msg : Msg)
    (txId : Nat) (hit : Bool) (replMsgs confirmOnHit : List Msg)
    (hnot : txId ∉ pendingIds st.log)
    (hcl : classify st.visible msg = .resolve txId hit replMsgs confirmOnHit) :
    SpecEngine.step upd classify st msg = (st, .none) := by
  have hrr : resolveReplace upd txId replMsgs st = (st, .none) := by
    simp [resolveReplace, replacePending_not_mem upd txId replMsgs st.log st.confirmed hnot]
  unfold SpecEngine.step; rw [hcl]; dsimp only
  cases hlog : st.log with
  | nil => exact hrr
  | cons e tail =>
      cases e with
      | pending id0 m0 =>
          have hbeq : (id0 == txId) = false := beq_false_of_ne (fun heq => hnot (by simp [hlog, heq]))
          simpa [hbeq] using hrr
      | regular _ | resolved _ => exact hrr

/-- General multi-transaction linearizability & effect-once theorem:
    for ANY journal `pre ++ [.pending txId specMsg] ++ post` with `txId ∉ pendingIds pre`,
    resolving `txId` along the replace/replay path preserves `pre` and `post`, applies `replMsgs`
    in place, removes `txId` from `pendingIds`, and emits ONLY `replMsgs`'s commands at `pre`'s state. -/
theorem resolve_general_linearizable {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg)
    (classify : State → Msg → SpecAction Msg)
    (st : SpecState State Msg) (msg : Msg)
    (txId : Nat) (specMsg : Msg) (hit : Bool)
    (replMsgs confirmOnHit : List Msg)
    (pre post : List (SpecEntry Msg))
    (hlog : st.log = pre ++ .pending txId specMsg :: post)
    (hnotPre : txId ∉ pendingIds pre)
    (hnotHeadHit : !(hit && pre.isEmpty))
    (hcl : classify st.visible msg = .resolve txId hit replMsgs confirmOnHit) :
    let stepOnly := fun s m => (upd s m).1
    let res := SpecEngine.step upd classify st msg
    res.1.visible = (pre.map entryMsg ++ replMsgs ++ post.map entryMsg).foldl stepOnly st.confirmed ∧
    pendingIds res.1.log = pendingIds pre ++ pendingIds post ∧
    res.2 = mkBatchCmd (runMsgs upd (pre.foldl (replayEntry stepOnly) st.confirmed) replMsgs).2 := by
  have hrr :
      let stepOnly := fun s m => (upd s m).1
      let res := resolveReplace upd txId replMsgs st
      res.1.visible = (pre.map entryMsg ++ replMsgs ++ post.map entryMsg).foldl stepOnly st.confirmed ∧
      pendingIds res.1.log = pendingIds pre ++ pendingIds post ∧
      res.2 = mkBatchCmd (runMsgs upd (pre.foldl (replayEntry stepOnly) st.confirmed) replMsgs).2 := by
    unfold resolveReplace; rw [hlog, replacePending_split upd txId specMsg replMsgs pre post st.confirmed hnotPre]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_, trivial⟩
    · dsimp only; rw [drainConfirmed_foldl_eq, foldl_replayEntry_eq_map]
      simp [List.map_append, List.map_map, Function.comp_def, entryMsg]
    · dsimp only; rw [drainConfirmed_pendingIds, pendingIds_append, pendingIds_append,
        pendingIds_map_resolved, List.append_nil]
  have hstepEq : SpecEngine.step upd classify st msg = resolveReplace upd txId replMsgs st := by
    unfold SpecEngine.step; rw [hcl]; dsimp only
    cases pre with
    | nil =>
        simp only [List.isEmpty_nil, Bool.and_true, Bool.not_eq_true'] at hnotHeadHit
        simp [hlog, hnotHeadHit]
    | cons e0 _ =>
        rw [hlog]
        cases e0 with
        | pending id0 _ =>
            have hbeq : (id0 == txId) = false := beq_false_of_ne (fun heq => hnotPre (by simp [heq]))
            simp [hbeq]
        | regular _ | resolved _ => rfl
  simpa [hstepEq] using hrr

/-- Single-transaction rollback completeness: when a sole pending prediction fails or mismatches
    and resolves to `replMsgs`, `log = []` and `visible = confirmed` equals applying `replMsgs`. -/
theorem resolve_rollback_reverts_single {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg)
    (classify : State → Msg → SpecAction Msg)
    (st : SpecState State Msg) (msg : Msg)
    (txId : Nat) (specMsg : Msg) (replMsgs : List Msg)
    (hlog : st.log = [.pending txId specMsg])
    (hcl : classify st.visible msg = .resolve txId false replMsgs []) :
    let st' := (SpecEngine.step upd classify st msg).1
    st'.log = [] ∧
    st'.confirmed = replMsgs.foldl (fun s m => (upd s m).1) st.confirmed ∧
    st'.visible = st'.confirmed := by
  have hdrain := drainConfirmed_append_resolved (fun s m => (upd s m).1) replMsgs [] st.confirmed
  simp [SpecEngine.step, resolveReplace, hcl, hlog, replacePending, List.append_nil] at hdrain ⊢
  simp [hdrain, drainConfirmed]

/-- Lawful hit soundness: when `SpecEq.eq actual pred = true`, `actual = pred` and the O(1)
    head-hit fast path produces the exact same `SpecState` and `Cmd` as replacing and replaying. -/
theorem resolve_hit_sound {State Msg α : Type} [SpecEq α]
    (upd : State → Msg → State × Cmd Msg)
    (classify : State → Msg → SpecAction Msg)
    (cont : α → Msg) (actual pred : α)
    (st : SpecState State Msg) (msg : Msg)
    (txId : Nat) (tail : List (SpecEntry Msg)) (confirmOnHit : List Msg)
    (heq : SpecEq.eq actual pred = true)
    (hcoh : Coherent (fun s m => (upd s m).1) st)
    (hlog : st.log = .pending txId (cont pred) :: tail)
    (hcl : classify st.visible msg = .resolve txId true (cont actual :: confirmOnHit) confirmOnHit) :
    let stepOnly := fun s m => (upd s m).1
    let (confRef, logRef) :=
      drainConfirmed stepOnly st.confirmed ((cont actual :: confirmOnHit).map SpecEntry.resolved ++ tail)
    let visRef := logRef.foldl (replayEntry stepOnly) confRef
    (SpecEngine.step upd classify st msg).1 =
      { visible := visRef, confirmed := confRef, nextTxId := st.nextTxId, log := logRef } ∧
    (SpecEngine.step upd classify st msg).2 =
      if confirmOnHit.isEmpty then .none
      else mkBatchCmd (runMsgs upd (stepOnly st.confirmed (cont actual)) confirmOnHit).2 := by
  cases SpecEq.eq_of_true heq
  unfold SpecEngine.step; rw [hcl, hlog]; dsimp only
  simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
  cases confirmOnHit with
  | nil =>
      simp only [List.isEmpty_nil, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append,
        List.nil_append, drainConfirmed]
      refine ⟨?_, trivial⟩
      cases st with
      | mk vis conf nextTxId log =>
          dsimp only at hcoh hlog ⊢; subst hlog; unfold Coherent at hcoh
          have hvis : vis = (drainConfirmed (fun s m => (upd s m).1) (upd conf (cont actual)).1 tail).2.foldl
              (replayEntry (fun s m => (upd s m).1))
              (drainConfirmed (fun s m => (upd s m).1) (upd conf (cont actual)).1 tail).1 := by
            rw [drainConfirmed_foldl_eq]; simpa [List.foldl_cons, replayEntry] using hcoh
          simp [hvis]
  | cons _ _ =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.map_cons,
        List.cons_append, drainConfirmed]
      rw [runMsgs_fst_eq_foldl, drainConfirmed_append_resolved]
      exact ⟨rfl, trivial⟩

private theorem pendingIds_mem_split {Msg : Type} (txId : Nat) :
    ∀ (l : List (SpecEntry Msg)), txId ∈ pendingIds l → (pendingIds l).Nodup →
      ∃ pre specMsg post, l = pre ++ .pending txId specMsg :: post ∧
        txId ∉ pendingIds pre ∧ txId ∉ pendingIds post
  | [], hm, _ => by simp at hm
  | .regular r :: t, hm, hnd => by
      rcases pendingIds_mem_split txId t hm hnd with ⟨pre, sm, post, rfl, hp, hq⟩
      exact ⟨.regular r :: pre, sm, post, rfl, hp, hq⟩
  | .resolved r :: t, hm, hnd => by
      rcases pendingIds_mem_split txId t hm hnd with ⟨pre, sm, post, rfl, hp, hq⟩
      exact ⟨.resolved r :: pre, sm, post, rfl, hp, hq⟩
  | .pending id0 m0 :: t, hm, hnd => by
      rcases List.nodup_cons.1 hnd with ⟨hnotT, hndT⟩
      rcases List.mem_cons.1 hm with rfl | hmt
      · exact ⟨[], m0, t, rfl, by simp, hnotT⟩
      · rcases pendingIds_mem_split txId t hmt hndT with ⟨pre, sm, post, rfl, hp, hq⟩
        have hne : txId ≠ id0 := fun h => hnotT (h ▸ hmt)
        exact ⟨.pending id0 m0 :: pre, sm, post, rfl, by simp [hne, hp], hq⟩

private theorem step_resolve_empty_pending_drains {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg) (classify : State → Msg → SpecAction Msg)
    (st : SpecState State Msg) (msg : Msg)
    (txId : Nat) (hit : Bool) (replMsgs confirmOnHit : List Msg)
    (hcl : classify st.visible msg = .resolve txId hit replMsgs confirmOnHit)
    (hpe : pendingIds (SpecEngine.step upd classify st msg).1.log = []) :
    (SpecEngine.step upd classify st msg).1.log = [] ∨
    st.log = (SpecEngine.step upd classify st msg).1.log := by
  have hdrain : ∀ (l : List (SpecEntry Msg)) (c : State),
      pendingIds (drainConfirmed (fun s m => (upd s m).1) c l).2 = [] →
      (drainConfirmed (fun s m => (upd s m).1) c l).2 = [] := fun l c hp =>
    congrArg Prod.snd (drainConfirmed_empty_of_no_pending _ l c (by rwa [drainConfirmed_pendingIds] at hp))
  have hrr : pendingIds (resolveReplace upd txId replMsgs st).1.log = [] →
      (resolveReplace upd txId replMsgs st).1.log = [] ∨
      st.log = (resolveReplace upd txId replMsgs st).1.log := by
    unfold resolveReplace; dsimp only; split
    · intro _; exact Or.inr rfl
    · intro hp; exact Or.inl (hdrain _ _ hp)
  unfold SpecEngine.step at hpe ⊢; rw [hcl] at hpe ⊢; dsimp only at hpe ⊢
  cases hlog : st.log with
  | nil => simp only [hlog] at hpe ⊢; simpa [hlog] using hrr hpe
  | cons e tail =>
      simp only [hlog] at hpe ⊢
      cases e with
      | pending id0 m0 =>
          dsimp only at hpe ⊢; split at hpe
          · rename_i h1; simp only [h1, ↓reduceIte]
            split at hpe <;> (rename_i h2; simp only [h2, ↓reduceIte]; exact Or.inl (hdrain _ _ hpe))
          · rename_i h1; simp only [h1, Bool.false_eq_true, ↓reduceIte] at hpe ⊢; simpa [hlog] using hrr hpe
      | regular _ | resolved _ => dsimp only at hpe ⊢; simpa [hlog] using hrr hpe

/-- Zero-leak convergence for the final pending transaction. -/
theorem step_resolve_clears_when_last {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg)
    (classify : State → Msg → SpecAction Msg)
    (st : SpecState State Msg) (msg : Msg)
    (txId : Nat) (hit : Bool) (replMsgs confirmOnHit : List Msg)
    (hcoh : Coherent (fun s m => (upd s m).1) st)
    (hlast : pendingIds st.log = [txId])
    (hcl : classify st.visible msg = .resolve txId hit replMsgs confirmOnHit) :
    let st' := (SpecEngine.step upd classify st msg).1
    st'.log = [] ∧ st'.visible = st'.confirmed := by
  have hcoh' := step_preserves_coherent upd classify st msg hcoh
  have ⟨pre, sm, post, hlog, hnotPre, _⟩ :=
    pendingIds_mem_split txId st.log (by simp [hlast]) (by simp [hlast])
  have hprePost : pendingIds pre ++ pendingIds post = [] := by
    have hEq : pendingIds pre ++ txId :: pendingIds post = [txId] := by
      simpa [hlog, pendingIds_append] using hlast
    cases hp : pendingIds pre with
    | nil => simpa [hp] using hEq
    | cons _ _ => have hlen := congrArg List.length hEq; simp [hp] at hlen
  have hpendEmpty : pendingIds (SpecEngine.step upd classify st msg).1.log = [] := by
    by_cases hhh : hit && pre.isEmpty
    · cases pre with
      | nil =>
          simp only [List.isEmpty_nil, Bool.and_true] at hhh; subst hhh
          simp only [List.nil_append, pendingIds_nil] at hlog hprePost
          unfold SpecEngine.step; rw [hcl, hlog]; dsimp only
          simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
          split <;> simp [drainConfirmed_pendingIds, hprePost]
      | cons _ _ => simp at hhh
    · have hlin := resolve_general_linearizable upd classify st msg txId sm hit replMsgs
        confirmOnHit pre post hlog hnotPre (by simp [hhh]) hcl
      simpa [hprePost] using hlin.2.1
  have hlogEmpty : (SpecEngine.step upd classify st msg).1.log = [] := by
    rcases step_resolve_empty_pending_drains upd classify st msg txId hit replMsgs confirmOnHit hcl hpendEmpty with
      hnil | hsame
    · exact hnil
    · rw [← hsame, hlast] at hpendEmpty; cases hpendEmpty
  refine ⟨hlogEmpty, ?_⟩
  unfold Coherent at hcoh'; simpa [hlogEmpty] using hcoh'

/-- Multi-transaction zero-leak convergence: resolving every pending `txId` in `st.log`
    (in *any* arrival order) drains `log` to `[]` and leaves `visible = confirmed`. -/
theorem resolve_all_drains_log {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg)
    (classify : State → Msg → SpecAction Msg) :
    ∀ (msgs : List Msg) (st : SpecState State Msg),
      Coherent (fun s m => (upd s m).1) st →
      WellFormedIds st →
      (∀ (st0 : SpecState State Msg) (m : Msg), m ∈ msgs →
        ∃ txId hit replMsgs confirmOnHit,
          classify st0.visible m = .resolve txId hit replMsgs confirmOnHit) →
      (∀ id ∈ pendingIds st.log, ∃ m ∈ msgs, ∀ (st0 : SpecState State Msg),
        ∃ hit replMsgs confirmOnHit,
          classify st0.visible m = .resolve id hit replMsgs confirmOnHit) →
      let st' := msgs.foldl (fun acc m => (SpecEngine.step upd classify acc m).1) st
      (pendingIds st'.log = []) ∧
      (st'.log = [] ∨ st.log = st'.log) ∧
      Coherent (fun s m => (upd s m).1) st' := by
  intro msgs
  induction msgs with
  | nil =>
      intro st hcoh _ _ hall
      have hp : pendingIds st.log = [] := by
        cases h : pendingIds st.log with
        | nil => rfl
        | cons id _ => rcases hall id (by simp [h]) with ⟨_, hm, _⟩; exact nomatch hm
      exact ⟨hp, Or.inr rfl, hcoh⟩
  | cons m ms ih =>
      intro st hcoh hwf hres hall
      have hcoh1 := step_preserves_coherent upd classify st m hcoh
      have hwf1 := step_preserves_wellFormedIds upd classify st m hwf
      rcases hres st m List.mem_cons_self with ⟨txId, hit, replMsgs, confirmOnHit, hcl⟩
      have hpend1 : ∀ id ∈ pendingIds (SpecEngine.step upd classify st m).1.log,
          id ∈ pendingIds st.log ∧ id ≠ txId := by
        intro id hid
        by_cases hmem : txId ∈ pendingIds st.log
        · rcases pendingIds_mem_split txId st.log hmem hwf.2 with ⟨pre, sm, post, hlog, hnotPre, hnotPost⟩
          by_cases hhh : hit && pre.isEmpty
          · cases pre with
            | nil =>
                simp only [List.isEmpty_nil, Bool.and_true] at hhh; subst hhh
                simp only [List.nil_append] at hlog
                unfold SpecEngine.step at hid; rw [hcl, hlog] at hid; dsimp only at hid
                simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte] at hid
                have hidPost : id ∈ pendingIds post := by
                  split at hid <;> rwa [drainConfirmed_pendingIds] at hid
                exact ⟨by simp [hlog, hidPost], fun heq => hnotPost (heq ▸ hidPost)⟩
            | cons _ _ => simp at hhh
          · have hlin := resolve_general_linearizable upd classify st m txId sm hit replMsgs
              confirmOnHit pre post hlog hnotPre (by simp [hhh]) hcl
            rw [hlin.2.1] at hid
            rcases List.mem_append.1 hid with h1 | h2
            · exact ⟨by simp [hlog, pendingIds_append, h1], fun heq => hnotPre (heq ▸ h1)⟩
            · exact ⟨by simp [hlog, pendingIds_append, h2], fun heq => hnotPost (heq ▸ h2)⟩
        · rw [resolve_unknown_noop upd classify st m txId hit replMsgs confirmOnHit hmem hcl] at hid
          exact ⟨hid, fun heq => hmem (heq ▸ hid)⟩
      have hall1 : ∀ id ∈ pendingIds (SpecEngine.step upd classify st m).1.log,
          ∃ m' ∈ ms, ∀ (st0 : SpecState State Msg), ∃ hit' repl' conf',
            classify st0.visible m' = .resolve id hit' repl' conf' := by
        intro id hid
        have ⟨hin0, hne⟩ := hpend1 id hid
        rcases hall id hin0 with ⟨m', hm', hcl'⟩
        rcases List.mem_cons.1 hm' with rfl | hm's
        · rcases hcl' st with ⟨_, _, _, hclm⟩
          rw [hcl] at hclm; injection hclm with htx; exact absurd htx.symm hne
        · exact ⟨m', hm's, hcl'⟩
      rcases ih (SpecEngine.step upd classify st m).1 hcoh1 hwf1
          (fun st0 m' hm' => hres st0 m' (List.mem_cons_of_mem m hm')) hall1 with ⟨hpe, hlogOr, hcohEnd⟩
      refine ⟨hpe, ?_, hcohEnd⟩
      cases hlogOr with
      | inl hnil => exact Or.inl hnil
      | inr heq =>
          rcases step_resolve_empty_pending_drains upd classify st m txId hit replMsgs confirmOnHit
              hcl (by rw [heq]; exact hpe) with hnil1 | hsame
          · exact Or.inl (heq.symm.trans hnil1)
          · exact Or.inr (hsame.trans heq)

/-- Pure dispatch guarantee: dispatching a speculative RPC never fires any `Cmd` from `specMsg`. -/
theorem dispatch_never_fires_specMsg_cmd {State Msg : Type}
    (upd : State → Msg → State × Cmd Msg)
    (classify : State → Msg → SpecAction Msg)
    (st : SpecState State Msg) (msg : Msg)
    (preCmd : Cmd Msg) (specMsg : Msg) (rpcCmd : Nat → Cmd Msg)
    (hcl : classify st.visible msg = .dispatch none preCmd specMsg rpcCmd) :
    (SpecEngine.step upd classify st msg).2 = Cmd.batch [preCmd, rpcCmd st.nextTxId] := by
  simp [SpecEngine.step, hcl]

end SpecEngine

namespace Internal


@[simp] theorem App.withSpeculative_init {State Msg : Type}
    (classify : State → Msg → SpecAction Msg) (app : App State Msg) :
    (App.withSpeculative classify app).init = (SpecState.pure app.init.1, app.init.2) := rfl

@[simp] theorem App.withSpeculative_update {State Msg : Type}
    (classify : State → Msg → SpecAction Msg) (app : App State Msg) :
    (App.withSpeculative classify app).update = SpecEngine.step app.update classify := rfl

@[simp] theorem App.withSpeculative_template {State Msg : Type}
    (classify : State → Msg → SpecAction Msg) (app : App State Msg) :
    (App.withSpeculative classify app).template = app.template.mapScope SpecState.visible := rfl

@[simp] theorem App.withSpeculative_view {State Msg : Type}
    (classify : State → Msg → SpecAction Msg) (app : App State Msg) (st : SpecState State Msg) :
    App.view (App.withSpeculative classify app) st = App.view app st.visible := by
  simp [App.view, App.withSpeculative, App.liftModel]

theorem App.withSpeculative_init_inv {State Msg : Type} {Inv : State → Prop}
    (classify : State → Msg → SpecAction Msg) (app : App State Msg) (hinit : Inv app.init.1) :
    SpecEngine.SpecInv Inv (App.withSpeculative classify app).init.1 := ⟨hinit, hinit⟩

theorem App.withSpeculative_step_inv {State Msg : Type} {Inv : State → Prop}
    (classify : State → Msg → SpecAction Msg) (app : App State Msg)
    (hupd : ∀ s m, Inv s → Inv (app.update s m).1)
    (st : SpecState State Msg) (msg : Msg) (h : SpecEngine.SpecInv Inv st) :
    SpecEngine.SpecInv Inv ((App.withSpeculative classify app).update st msg).1 :=
  SpecEngine.step_preserves_inv app.update classify hupd st msg h

theorem App.withSpeculative_init_coherent {State Msg : Type}
    (classify : State → Msg → SpecAction Msg) (app : App State Msg) :
    SpecEngine.Coherent (fun s m => (app.update s m).1) (App.withSpeculative classify app).init.1 := rfl

theorem App.withSpeculative_step_coherent {State Msg : Type}
    (classify : State → Msg → SpecAction Msg) (app : App State Msg)
    (st : SpecState State Msg) (msg : Msg)
    (hcoh : SpecEngine.Coherent (fun s m => (app.update s m).1) st) :
    SpecEngine.Coherent (fun s m => (app.update s m).1)
      ((App.withSpeculative classify app).update st msg).1 :=
  SpecEngine.step_preserves_coherent app.update classify st msg hcoh

theorem App.withSpeculative_init_wellFormedIds {State Msg : Type}
    (classify : State → Msg → SpecAction Msg) (app : App State Msg) :
    SpecEngine.WellFormedIds (App.withSpeculative classify app).init.1 :=
  SpecEngine.wellFormedIds_pure _

theorem App.withSpeculative_step_wellFormedIds {State Msg : Type}
    (classify : State → Msg → SpecAction Msg) (app : App State Msg)
    (st : SpecState State Msg) (msg : Msg) (hwf : SpecEngine.WellFormedIds st) :
    SpecEngine.WellFormedIds ((App.withSpeculative classify app).update st msg).1 :=
  SpecEngine.step_preserves_wellFormedIds app.update classify st msg hwf

theorem App.withSpeculative_rehydrate_sound {State Msg : Type} {Inv : State → Prop}
    (classify : State → Msg → SpecAction Msg) (app : App State Msg)
    (hsound : ∀ raw m', app.rehydrate raw = some m' → Inv m')
    (raw : String) (st' : SpecState State Msg)
    (h : (App.withSpeculative classify app).rehydrate raw = some st') :
    SpecEngine.SpecInv Inv st' := by
  dsimp only [App.withSpeculative, App.liftModel] at h
  simp only [Option.map_eq_some_iff] at h
  rcases h with ⟨m', hm', rfl⟩
  have hm := hsound raw m' hm'
  exact ⟨hm, hm⟩

theorem App.withSpeculative_dehydrate_inv {State Msg : Type} {Inv : State → Prop}
    (classify : State → Msg → SpecAction Msg) (app : App State Msg)
    (hpres : ∀ m m', Inv m → app.rehydrate (app.dehydrate m) = some m' → Inv m')
    (st st' : SpecState State Msg) (hst : SpecEngine.SpecInv Inv st)
    (h : (App.withSpeculative classify app).rehydrate ((App.withSpeculative classify app).dehydrate st) = some st') :
    SpecEngine.SpecInv Inv st' := by
  dsimp only [App.withSpeculative, App.liftModel] at h
  simp only [Option.map_eq_some_iff] at h
  rcases h with ⟨m', hm', rfl⟩
  have hm := hpres st.visible m' hst.2 hm'
  exact ⟨hm, hm⟩

end Internal

end Qed
