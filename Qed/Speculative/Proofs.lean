import Qed.Speculative.Core

namespace Qed
namespace SpecEngine
section
variable {State Msg : Type}

def Coherent (stepOnly : State → Msg → State) (st : SpecState State Msg) : Prop :=
  st.visible = st.log.foldl (replayEntry stepOnly) st.confirmed

def SpecInv (Inv : State → Prop) (st : SpecState State Msg) : Prop := Inv st.confirmed ∧ Inv st.visible

def pendingIds : List (SpecEntry Msg) → List Nat
  | [] => [] | .pending id _ :: es => id :: pendingIds es | .regular _ :: es | .resolved _ :: es => pendingIds es

def WellFormedIds (st : SpecState State Msg) : Prop :=
  (∀ id ∈ pendingIds st.log, id < st.nextTxId) ∧ (pendingIds st.log).Nodup

theorem pendingIds_append : ∀ (a b : List (SpecEntry Msg)), pendingIds (a ++ b) = pendingIds a ++ pendingIds b
  | [], _ => rfl | .pending _ _ :: as, b => congrArg (_ :: ·) (pendingIds_append as b) | .regular _ :: as, b | .resolved _ :: as, b => pendingIds_append as b

private theorem pendingIds_map_resolved : ∀ (ms : List Msg), pendingIds (ms.map SpecEntry.resolved) = []
  | [] => rfl | _ :: ms => pendingIds_map_resolved ms

private theorem foldl_replayEntry_eq_map (stepOnly : State → Msg → State) :
    ∀ (log : List (SpecEntry Msg)) (s : State), log.foldl (replayEntry stepOnly) s = (log.map entryMsg).foldl stepOnly s
  | [], _ => rfl | _ :: rest, _ => foldl_replayEntry_eq_map stepOnly rest _

private theorem runMsgs_fst_eq_foldl (upd : State → Msg → State × Cmd Msg) :
    ∀ (ms : List Msg) (s : State), (runMsgs upd s ms).1 = ms.foldl (fun acc m => (upd acc m).1) s
  | [], _ => rfl | m :: ms, s => runMsgs_fst_eq_foldl upd ms (upd s m).1

theorem replay_preserves_inv {Inv : State → Prop} {stepOnly : State → Msg → State} (hstep : ∀ s m, Inv s → Inv (stepOnly s m)) :
    ∀ (log : List (SpecEntry Msg)) (s : State), Inv s → Inv (log.foldl (replayEntry stepOnly) s)
  | [], _, hs => hs | e :: rest, s, hs => replay_preserves_inv hstep rest _ (hstep s (entryMsg e) hs)

private theorem drainConfirmed_split (stepOnly : State → Msg → State) :
    ∀ (log : List (SpecEntry Msg)) (conf : State),
      ∃ pre suf, log = pre ++ suf ∧ pendingIds pre = [] ∧ (suf = [] ∨ ∃ id m tl, suf = .pending id m :: tl) ∧
        drainConfirmed stepOnly conf log = (pre.foldl (replayEntry stepOnly) conf, suf)
  | [], _ => ⟨[], [], rfl, rfl, .inl rfl, rfl⟩
  | .pending id m :: tl, _ => ⟨[], _, rfl, rfl, .inr ⟨id, m, tl, rfl⟩, rfl⟩
  | .regular m :: rest, conf | .resolved m :: rest, conf =>
      let ⟨pre, suf, hlog, hpre, hsuf, hdr⟩ := drainConfirmed_split stepOnly rest (stepOnly conf m)
      ⟨_ :: pre, suf, congrArg (_ :: ·) hlog, hpre, hsuf, hdr⟩

theorem drainConfirmed_preserves_inv {Inv : State → Prop} {stepOnly : State → Msg → State}
    (hstep : ∀ s m, Inv s → Inv (stepOnly s m)) (log : List (SpecEntry Msg)) (conf : State) (hc : Inv conf) :
    Inv (drainConfirmed stepOnly conf log).1 :=
  let ⟨pre, _, _, _, _, hdr⟩ := drainConfirmed_split stepOnly log conf; hdr ▸ replay_preserves_inv hstep pre conf hc

private theorem drainConfirmed_foldl_eq (stepOnly : State → Msg → State) (log : List (SpecEntry Msg)) (conf : State) :
    let res := drainConfirmed stepOnly conf log; res.2.foldl (replayEntry stepOnly) res.1 = log.foldl (replayEntry stepOnly) conf := by
  rcases drainConfirmed_split stepOnly log conf with ⟨pre, suf, rfl, _, _, hdr⟩; simp only [hdr, List.foldl_append]

private theorem drainConfirmed_pendingIds (stepOnly : State → Msg → State) (log : List (SpecEntry Msg)) (conf : State) :
    pendingIds (drainConfirmed stepOnly conf log).2 = pendingIds log := by
  rcases drainConfirmed_split stepOnly log conf with ⟨pre, suf, rfl, hpre, _, hdr⟩; simp only [hdr, pendingIds_append, hpre, List.nil_append]

private theorem drainConfirmed_nil_of_pending (stepOnly : State → Msg → State) (log : List (SpecEntry Msg)) (conf : State)
    (hp : pendingIds (drainConfirmed stepOnly conf log).2 = []) : (drainConfirmed stepOnly conf log).2 = [] := by
  rcases drainConfirmed_split stepOnly log conf with ⟨pre, suf, rfl, _, rfl | ⟨_, _, _, rfl⟩, hdr⟩
  · rw [hdr]
  · rw [hdr] at hp; cases hp

private theorem drainConfirmed_append_resolved (stepOnly : State → Msg → State) :
    ∀ (ms : List Msg) (tail : List (SpecEntry Msg)) (conf : State),
      drainConfirmed stepOnly conf (ms.map SpecEntry.resolved ++ tail) = drainConfirmed stepOnly (ms.foldl stepOnly conf) tail
  | [], _, _ => rfl | m :: ms, tail, conf => drainConfirmed_append_resolved stepOnly ms tail (stepOnly conf m)

private theorem runMsgs_preserves_inv {Inv : State → Prop} {upd : State → Msg → State × Cmd Msg}
    (hupd : ∀ s m, Inv s → Inv (upd s m).1) : ∀ (ms : List Msg) (s : State), Inv s → Inv (runMsgs upd s ms).1
  | [], _, hs => hs | m :: ms, s, hs => runMsgs_preserves_inv hupd ms _ (hupd s m hs)

private theorem replacePending_not_mem (upd : State → Msg → State × Cmd Msg) (txId : Nat) (replMsgs : List Msg) :
    ∀ (log : List (SpecEntry Msg)) (sCur : State), txId ∉ pendingIds log → replacePending upd txId replMsgs sCur log = (log, [], false)
  | [], _, _ => rfl
  | .regular _ :: rest, _, h | .resolved _ :: rest, _, h => by simp only [replacePending, replacePending_not_mem upd txId replMsgs rest _ h]
  | .pending id m :: rest, sCur, h => by
      simp only [replacePending, beq_false_of_ne (show id ≠ txId from fun e => h (e ▸ .head _)), Bool.false_eq_true, ↓reduceIte,
        replacePending_not_mem upd txId replMsgs rest (upd sCur m).1 (fun hm => h (.tail _ hm))]

theorem replacePending_split (upd : State → Msg → State × Cmd Msg) (txId : Nat) (specMsg : Msg) (replMsgs : List Msg) :
    ∀ (pre post : List (SpecEntry Msg)) (sCur : State), txId ∉ pendingIds pre →
      replacePending upd txId replMsgs sCur (pre ++ .pending txId specMsg :: post) =
        (pre ++ replMsgs.map SpecEntry.resolved ++ post, (runMsgs upd (pre.foldl (replayEntry (fun s m => (upd s m).1)) sCur) replMsgs).2, true)
  | [], _, _, _ => by simp only [List.nil_append, replacePending, beq_self_eq_true, ↓reduceIte, List.foldl_nil]
  | .regular _ :: pre, post, _, h | .resolved _ :: pre, post, _, h => by
      simp only [List.cons_append, replacePending, List.foldl_cons, replayEntry, entryMsg, replacePending_split upd txId specMsg replMsgs pre post _ h]
  | .pending id m :: pre, post, sCur, h => by
      simp only [List.cons_append, replacePending, List.foldl_cons, replayEntry, entryMsg, beq_false_of_ne (show id ≠ txId from fun e => h (e ▸ .head _)),
        Bool.false_eq_true, ↓reduceIte, replacePending_split upd txId specMsg replMsgs pre post (upd sCur m).1 (fun hm => h (.tail _ hm))]

private theorem pendingIds_replacePending_sublist (upd : State → Msg → State × Cmd Msg) (txId : Nat) (replMsgs : List Msg) :
    ∀ (log : List (SpecEntry Msg)) (sCur : State), (pendingIds (replacePending upd txId replMsgs sCur log).1).Sublist (pendingIds log)
  | [], _ => .slnil
  | .regular m :: rest, sCur | .resolved m :: rest, sCur => pendingIds_replacePending_sublist upd txId replMsgs rest (upd sCur m).1
  | .pending id m :: rest, sCur => by
      by_cases heq : id = txId
      · subst heq; simp only [replacePending, beq_self_eq_true, ↓reduceIte, pendingIds_append, pendingIds_map_resolved, List.nil_append, pendingIds]
        exact .cons id (.refl _)
      · simp only [replacePending, beq_false_of_ne heq, Bool.false_eq_true, ↓reduceIte, pendingIds]
        exact .cons_cons id (pendingIds_replacePending_sublist upd txId replMsgs rest (upd sCur m).1)

private theorem pendingIds_mem_split (txId : Nat) :
    ∀ (l : List (SpecEntry Msg)), txId ∈ pendingIds l → (pendingIds l).Nodup →
      ∃ pre specMsg post, l = pre ++ .pending txId specMsg :: post ∧ txId ∉ pendingIds pre ∧ txId ∉ pendingIds post
  | [], hm, _ => nomatch hm
  | .regular _ :: t, hm, hnd | .resolved _ :: t, hm, hnd =>
      let ⟨pre, sm, post, h, hp, hq⟩ := pendingIds_mem_split txId t hm hnd; ⟨_ :: pre, sm, post, congrArg (_ :: ·) h, hp, hq⟩
  | .pending id0 m0 :: t, hm, hnd => by
      rcases List.nodup_cons.1 hnd with ⟨hnotT, hndT⟩
      rcases List.mem_cons.1 hm with rfl | hmt
      · exact ⟨[], m0, t, rfl, (fun h => nomatch h), hnotT⟩
      · rcases pendingIds_mem_split txId t hmt hndT with ⟨pre, sm, post, rfl, hp, hq⟩
        exact ⟨.pending id0 m0 :: pre, sm, post, rfl, fun h => (List.mem_cons.1 h).elim (fun e => hnotT (e ▸ hmt)) hp, hq⟩

section
variable (upd : State → Msg → State × Cmd Msg) (classify : State → Msg → SpecAction Msg)

private theorem step_resolve_cases (st : SpecState State Msg) (msg : Msg) (txId : Nat) (hit : Bool) (replMsgs confirmOnHit : List Msg)
    (hcl : classify st.visible msg = .resolve txId hit replMsgs confirmOnHit) :
    (∃ m0 tail, st.log = .pending txId m0 :: tail ∧ hit = true ∧ SpecEngine.step upd classify st msg = resolveHeadHit upd st m0 tail confirmOnHit) ∨
    SpecEngine.step upd classify st msg = resolveReplace upd txId replMsgs st := by
  unfold SpecEngine.step; rw [hcl]; dsimp only
  match hlog : st.log with
  | .pending id0 m0 :: tail =>
      dsimp only; by_cases hc : (hit && id0 == txId) = true
      · rw [ite_eq_left hc]; rcases Bool.and_eq_true_iff.1 hc with ⟨hh, hi⟩; cases beq_iff_eq.1 hi; exact .inl ⟨m0, tail, rfl, hh, rfl⟩
      · rw [ite_eq_right hc]; exact .inr rfl
  | [] | .regular _ :: _ | .resolved _ :: _ => exact .inr rfl

private theorem step_preserves (P : SpecState State Msg → Prop)
    (hNonPend : ∀ st m e, P st → entryMsg e = m → pendingIds [e] = [] → P (appendNonPending st (upd st.visible m).1 e))
    (hPend : ∀ st m, P st → P (appendPending (fun s m => (upd s m).1) st m))
    (hHit : ∀ st txId m0 tail confirmOnHit, P st → st.log = .pending txId m0 :: tail → P (resolveHeadHit upd st m0 tail confirmOnHit).1)
    (hRepl : ∀ st txId replMsgs, P st →
      let stepOnly := fun s m => (upd s m).1
      let (conf', log') := drainConfirmed stepOnly st.confirmed (replacePending upd txId replMsgs st.confirmed st.log).1
      P { st with visible := log'.foldl (replayEntry stepOnly) conf', confirmed := conf', log := log' })
    (st : SpecState State Msg) (msg : Msg) (h : P st) : P (SpecEngine.step upd classify st msg).1 := by
  cases hcl : classify st.visible msg with
  | normal => unfold SpecEngine.step; rw [hcl]; exact hNonPend st msg (.regular msg) h rfl rfl
  | dispatch preMsg? _ specMsg _ =>
      unfold SpecEngine.step; rw [hcl]; dsimp only
      cases preMsg? with
      | none => exact hPend st specMsg h
      | some pm => exact hPend _ specMsg (hNonPend st pm (.resolved pm) h rfl rfl)
  | resolve txId hit replMsgs confirmOnHit =>
      rcases step_resolve_cases upd classify st msg txId hit replMsgs confirmOnHit hcl with ⟨m0, tail, hlog, _, hstep⟩ | hstep
      · exact hstep ▸ hHit st txId m0 tail confirmOnHit h hlog
      · rw [hstep]; unfold resolveReplace; dsimp only; split; exact h; exact hRepl st txId replMsgs h

theorem step_preserves_inv {Inv : State → Prop} (hupd : ∀ s m, Inv s → Inv (upd s m).1) (st : SpecState State Msg) (msg : Msg)
    (h : SpecInv Inv st) : SpecInv Inv (SpecEngine.step upd classify st msg).1 :=
  step_preserves upd classify (SpecInv Inv)
    (fun _ _ _ h _ _ => by unfold appendNonPending; split <;> exact ⟨by first | exact hupd _ _ h.2 | exact h.1, hupd _ _ h.2⟩)
    (fun _ _ h => ⟨h.1, hupd _ _ h.2⟩)
    (fun _ _ m0 tail conf h _ => by
      unfold resolveHeadHit; dsimp only; have hc1 := hupd _ m0 h.1; split
      · exact ⟨drainConfirmed_preserves_inv hupd tail _ hc1, h.2⟩
      · have hc3 := drainConfirmed_preserves_inv hupd tail _ (runMsgs_preserves_inv hupd conf _ hc1); exact ⟨hc3, replay_preserves_inv hupd _ _ hc3⟩)
    (fun st txId repl h => let hc' := drainConfirmed_preserves_inv hupd (replacePending upd txId repl st.confirmed st.log).1 st.confirmed h.1; ⟨hc', replay_preserves_inv hupd _ _ hc'⟩)
    st msg h

theorem step_preserves_coherent (st : SpecState State Msg) (msg : Msg) (hcoh : Coherent (fun s m => (upd s m).1) st) :
    Coherent (fun s m => (upd s m).1) (SpecEngine.step upd classify st msg).1 :=
  step_preserves upd classify (Coherent fun s m => (upd s m).1)
    (fun _ _ _ h he _ => by unfold appendNonPending; unfold Coherent at h ⊢; split; rfl; simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, replayEntry, he, h])
    (fun _ _ h => by unfold appendPending; unfold Coherent at h ⊢; simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, replayEntry, entryMsg, h])
    (fun _ _ _ _ _ h hlog => by unfold resolveHeadHit; dsimp only; split; (unfold Coherent at h ⊢; dsimp only; rw [drainConfirmed_foldl_eq]; simp only [hlog, List.foldl_cons, replayEntry, entryMsg] at h; exact h); rfl)
    (fun _ _ _ _ => rfl) st msg hcoh

private theorem wellFormedIds_of_sublist {st st' : SpecState State Msg} (h : WellFormedIds st)
    (hnext : st'.nextTxId = st.nextTxId) (hsub : (pendingIds st'.log).Sublist (pendingIds st.log)) : WellFormedIds st' :=
  ⟨fun id hid => hnext ▸ h.1 id (hsub.subset hid), h.2.sublist hsub⟩

theorem step_preserves_wellFormedIds (st : SpecState State Msg) (msg : Msg) (hwf : WellFormedIds st) :
    WellFormedIds (SpecEngine.step upd classify st msg).1 :=
  step_preserves upd classify WellFormedIds
    (fun _ _ _ h _ hp => by unfold appendNonPending; split; exact ⟨(fun _ h => nomatch h), List.nodup_nil⟩; simp only [WellFormedIds, pendingIds_append, hp, List.append_nil]; exact h)
    (fun _ _ h => ⟨fun id hid => by simp only [appendPending, pendingIds_append, pendingIds, List.mem_append, List.mem_singleton] at hid; exact hid.elim (fun h1 => Nat.lt_succ_of_lt (h.1 id h1)) (· ▸ Nat.lt_succ_self _),
      by simp only [appendPending, pendingIds_append, pendingIds, List.nodup_append, h.2, true_and]; exact ⟨List.pairwise_singleton _ _, fun a ha b hb heq => Nat.lt_irrefl _ (List.mem_singleton.1 hb ▸ heq ▸ h.1 a ha)⟩⟩)
    (fun st _ _ tail _ h hlog => by
      have hsub : (pendingIds tail).Sublist (pendingIds st.log) := hlog ▸ .cons _ (.refl _)
      unfold resolveHeadHit; dsimp only; split <;> exact wellFormedIds_of_sublist h rfl (by dsimp only; rwa [drainConfirmed_pendingIds]))
    (fun st txId repl h => wellFormedIds_of_sublist h rfl (by dsimp only; rw [drainConfirmed_pendingIds]; exact pendingIds_replacePending_sublist upd txId repl st.log st.confirmed))
    st msg hwf

theorem resolve_hit_preserves_visible (st : SpecState State Msg) (msg : Msg) (txId : Nat) (m0 : Msg)
    (tail : List (SpecEntry Msg)) (replMsgs : List Msg) (hlog : st.log = .pending txId m0 :: tail)
    (hcl : classify st.visible msg = .resolve txId true replMsgs []) : (SpecEngine.step upd classify st msg).1.visible = st.visible := by
  simp only [SpecEngine.step, resolveHeadHit, hcl, hlog, beq_self_eq_true, Bool.and_self, ↓reduceIte, List.isEmpty_nil]

theorem resolve_unknown_noop (st : SpecState State Msg) (msg : Msg) (txId : Nat) (hit : Bool) (replMsgs confirmOnHit : List Msg)
    (hnot : txId ∉ pendingIds st.log) (hcl : classify st.visible msg = .resolve txId hit replMsgs confirmOnHit) :
    SpecEngine.step upd classify st msg = (st, .none) := by
  rcases step_resolve_cases upd classify st msg txId hit replMsgs confirmOnHit hcl with ⟨_, _, hlog, _, _⟩ | hstep
  · exact absurd (hlog ▸ .head _) hnot
  · simp only [hstep, resolveReplace, replacePending_not_mem upd txId replMsgs st.log st.confirmed hnot, Bool.not_false, ↓reduceIte]

theorem resolve_general_linearizable (st : SpecState State Msg) (msg : Msg) (txId : Nat) (specMsg : Msg)
    (hit : Bool) (replMsgs confirmOnHit : List Msg) (pre post : List (SpecEntry Msg))
    (hlog : st.log = pre ++ .pending txId specMsg :: post) (hnotPre : txId ∉ pendingIds pre) (hnotHeadHit : !(hit && pre.isEmpty))
    (hcl : classify st.visible msg = .resolve txId hit replMsgs confirmOnHit) :
    let stepOnly := fun s m => (upd s m).1; let res := SpecEngine.step upd classify st msg
    res.1.visible = (pre.map entryMsg ++ replMsgs ++ post.map entryMsg).foldl stepOnly st.confirmed ∧
    pendingIds res.1.log = pendingIds pre ++ pendingIds post ∧
    res.2 = mkBatchCmd (runMsgs upd (pre.foldl (replayEntry stepOnly) st.confirmed) replMsgs).2 := by
  have hstepEq : SpecEngine.step upd classify st msg = resolveReplace upd txId replMsgs st := by
    rcases step_resolve_cases upd classify st msg txId hit replMsgs confirmOnHit hcl with ⟨_, _, hlog', hhit, _⟩ | hstep
    · rw [hlog] at hlog'; cases pre with | nil => simp only [hhit, List.isEmpty_nil, Bool.and_self, Bool.not_true] at hnotHeadHit; cases hnotHeadHit | cons _ _ => cases hlog'; exact absurd List.mem_cons_self hnotPre
    · exact hstep
  dsimp only; rw [hstepEq]; unfold resolveReplace; rw [hlog, replacePending_split upd txId specMsg replMsgs pre post st.confirmed hnotPre]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact ⟨by rw [drainConfirmed_foldl_eq, foldl_replayEntry_eq_map]; simp only [List.map_append, List.map_map, Function.comp_def, entryMsg, List.map_id'],
    by rw [drainConfirmed_pendingIds, pendingIds_append, pendingIds_append, pendingIds_map_resolved, List.append_nil], trivial⟩

theorem resolve_rollback_reverts_single (st : SpecState State Msg) (msg : Msg) (txId : Nat) (specMsg : Msg)
    (replMsgs : List Msg) (hlog : st.log = [.pending txId specMsg]) (hcl : classify st.visible msg = .resolve txId false replMsgs []) :
    let st' := (SpecEngine.step upd classify st msg).1
    st'.log = [] ∧ st'.confirmed = replMsgs.foldl (fun s m => (upd s m).1) st.confirmed ∧ st'.visible = st'.confirmed := by
  have hdrain := drainConfirmed_append_resolved (fun s m => (upd s m).1) replMsgs [] st.confirmed
  simp only [List.append_nil] at hdrain
  simp only [SpecEngine.step, resolveReplace, hcl, hlog, Bool.false_and, Bool.false_eq_true, ↓reduceIte, replacePending, beq_self_eq_true, List.append_nil, Bool.not_true, hdrain, drainConfirmed, List.foldl_nil, and_self]

private theorem step_resolve_props (st : SpecState State Msg) (msg : Msg) (txId : Nat) (hit : Bool)
    (replMsgs confirmOnHit : List Msg) (hcl : classify st.visible msg = .resolve txId hit replMsgs confirmOnHit) :
    let st' := (SpecEngine.step upd classify st msg).1
    (pendingIds st'.log = [] → st'.log = [] ∨ st.log = st'.log) ∧
    (∀ pre sm post, st.log = pre ++ .pending txId sm :: post → txId ∉ pendingIds pre → pendingIds st'.log = pendingIds pre ++ pendingIds post) := by
  rcases step_resolve_cases upd classify st msg txId hit replMsgs confirmOnHit hcl with ⟨m0, tail, hlog0, _, hstep⟩ | hstep
  · refine ⟨fun hpe => ?_, fun pre sm post hlog hnotPre => ?_⟩
    · rw [hstep] at hpe ⊢; unfold resolveHeadHit at hpe ⊢; dsimp only at hpe ⊢
      split at hpe <;> (rename_i h2; simp only [h2, ↓reduceIte]; exact .inl (drainConfirmed_nil_of_pending _ _ _ hpe))
    · rw [hlog] at hlog0; cases pre with
      | cons _ _ => cases hlog0; exact absurd (.head _) hnotPre
      | nil => cases hlog0; rw [hstep]; unfold resolveHeadHit; dsimp only; split <;> simp only [drainConfirmed_pendingIds, pendingIds, List.nil_append]
  · refine ⟨fun hpe => ?_, fun pre sm post hlog hnotPre => ?_⟩
    · rw [hstep] at hpe ⊢; unfold resolveReplace at hpe ⊢; dsimp only at hpe ⊢
      split at hpe <;> (rename_i h2; first | (rw [ite_eq_left h2]; exact .inr rfl) | (rw [ite_eq_right h2]; exact .inl (drainConfirmed_nil_of_pending _ _ _ hpe)))
    · rw [hstep]; unfold resolveReplace; rw [hlog, replacePending_split upd txId sm replMsgs pre post st.confirmed hnotPre]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, drainConfirmed_pendingIds, pendingIds_append, pendingIds_map_resolved, List.append_nil]

theorem step_resolve_clears_when_last (st : SpecState State Msg) (msg : Msg) (txId : Nat) (hit : Bool)
    (replMsgs confirmOnHit : List Msg) (hcoh : Coherent (fun s m => (upd s m).1) st)
    (hlast : pendingIds st.log = [txId]) (hcl : classify st.visible msg = .resolve txId hit replMsgs confirmOnHit) :
    let st' := (SpecEngine.step upd classify st msg).1; st'.log = [] ∧ st'.visible = st'.confirmed := by
  have ⟨pre, sm, post, hlog, hnotPre, _⟩ := pendingIds_mem_split txId st.log (hlast ▸ .head _) (hlast ▸ List.pairwise_singleton _ _)
  have hprePost : pendingIds pre ++ pendingIds post = [] := by
    have hEq : pendingIds pre ++ txId :: pendingIds post = [txId] := by rw [hlog, pendingIds_append, pendingIds] at hlast; exact hlast
    cases hp : pendingIds pre with | nil => rw [hp, List.nil_append] at hEq; exact (List.cons.inj hEq).2 | cons _ _ => have := congrArg List.length hEq; simp only [hp, List.length_append, List.length_cons, List.length_nil] at this; omega
  have ⟨hdrain, hsplit⟩ := step_resolve_props upd classify st msg txId hit replMsgs confirmOnHit hcl
  have hpe : pendingIds (SpecEngine.step upd classify st msg).1.log = [] := (hsplit pre sm post hlog hnotPre).trans hprePost
  have hnil : (SpecEngine.step upd classify st msg).1.log = [] := (hdrain hpe).elim id fun hs => by rw [← hs, hlast] at hpe; cases hpe
  exact ⟨hnil, by have hc := step_preserves_coherent upd classify st msg hcoh; unfold Coherent at hc; rw [hnil] at hc; exact hc⟩

theorem resolve_all_drains_log :
    ∀ (msgs : List Msg) (st : SpecState State Msg),
      Coherent (fun s m => (upd s m).1) st → WellFormedIds st →
      (∀ (st0 : SpecState State Msg) (m : Msg), m ∈ msgs → ∃ txId hit replMsgs confirmOnHit, classify st0.visible m = .resolve txId hit replMsgs confirmOnHit) →
      (∀ id ∈ pendingIds st.log, ∃ m ∈ msgs, ∀ (st0 : SpecState State Msg), ∃ hit replMsgs confirmOnHit, classify st0.visible m = .resolve id hit replMsgs confirmOnHit) →
      let st' := msgs.foldl (fun acc m => (SpecEngine.step upd classify acc m).1) st
      (pendingIds st'.log = []) ∧ (st'.log = [] ∨ st.log = st'.log) ∧ Coherent (fun s m => (upd s m).1) st'
  | [], st, hcoh, _, _, hall => ⟨List.eq_nil_iff_forall_not_mem.2 (fun id hid => let ⟨_, hm, _⟩ := hall id hid; nomatch hm), .inr rfl, hcoh⟩
  | m :: ms, st, hcoh, hwf, hres, hall => by
      rcases hres st m List.mem_cons_self with ⟨txId, hit, replMsgs, confirmOnHit, hcl⟩
      have ⟨hdrain, hsplit⟩ := step_resolve_props upd classify st m txId hit replMsgs confirmOnHit hcl
      have hall1 : ∀ id ∈ pendingIds (SpecEngine.step upd classify st m).1.log,
          ∃ m' ∈ ms, ∀ st0 : SpecState State Msg, ∃ hit' repl' conf', classify st0.visible m' = .resolve id hit' repl' conf' := fun id hid => by
        have ⟨hin0, hne⟩ : id ∈ pendingIds st.log ∧ id ≠ txId := by
          by_cases hmem : txId ∈ pendingIds st.log
          · rcases pendingIds_mem_split txId st.log hmem hwf.2 with ⟨pre, sm, post, hlog, hnotPre, hnotPost⟩
            rw [hsplit pre sm post hlog hnotPre] at hid
            exact (List.mem_append.1 hid).elim (fun h1 => ⟨by rw [hlog, pendingIds_append]; exact List.mem_append_left _ h1, fun e => hnotPre (e ▸ h1)⟩)
              (fun h2 => ⟨by rw [hlog, pendingIds_append, pendingIds]; exact List.mem_append_right _ (.tail _ h2), fun e => hnotPost (e ▸ h2)⟩)
          · rw [resolve_unknown_noop upd classify st m txId hit replMsgs confirmOnHit hmem hcl] at hid; exact ⟨hid, fun e => hmem (e ▸ hid)⟩
        rcases hall id hin0 with ⟨m', hm', hcl'⟩
        rcases List.mem_cons.1 hm' with rfl | hm's
        · rcases hcl' st with ⟨_, _, _, hclm⟩; rw [hcl] at hclm; injection hclm with htx; exact absurd htx.symm hne
        · exact ⟨m', hm's, hcl'⟩
      rcases resolve_all_drains_log ms (SpecEngine.step upd classify st m).1
          (step_preserves_coherent upd classify st m hcoh) (step_preserves_wellFormedIds upd classify st m hwf)
          (fun st0 m' hm' => hres st0 m' (.tail m hm')) hall1 with ⟨hpe, hlogOr, hcohEnd⟩
      exact ⟨hpe, hlogOr.elim .inl fun heq => (hdrain (heq ▸ hpe)).elim (fun h1 => .inl (heq.symm.trans h1)) (fun hs => .inr (hs.trans heq)), hcohEnd⟩

theorem dispatch_never_fires_specMsg_cmd (st : SpecState State Msg) (msg : Msg) (preCmd : Cmd Msg) (specMsg : Msg)
    (rpcCmd : Nat → Cmd Msg) (hcl : classify st.visible msg = .dispatch none preCmd specMsg rpcCmd) :
    (SpecEngine.step upd classify st msg).2 = Cmd.batch [preCmd, rpcCmd st.nextTxId] := by simp only [SpecEngine.step, hcl]

end

theorem resolve_hit_sound {α : Type} [SpecEq α] (upd : State → Msg → State × Cmd Msg) (classify : State → Msg → SpecAction Msg)
    (cont : α → Msg) (actual pred : α) (st : SpecState State Msg) (msg : Msg) (txId : Nat) (tail : List (SpecEntry Msg))
    (confirmOnHit : List Msg) (heq : SpecEq.eq actual pred = true) (hcoh : Coherent (fun s m => (upd s m).1) st)
    (hlog : st.log = .pending txId (cont pred) :: tail)
    (hcl : classify st.visible msg = .resolve txId true (cont actual :: confirmOnHit) confirmOnHit) :
    let stepOnly := fun s m => (upd s m).1
    let (confRef, logRef) := drainConfirmed stepOnly st.confirmed ((cont actual :: confirmOnHit).map SpecEntry.resolved ++ tail)
    let visRef := logRef.foldl (replayEntry stepOnly) confRef
    (SpecEngine.step upd classify st msg).1 = { visible := visRef, confirmed := confRef, nextTxId := st.nextTxId, log := logRef } ∧
    (SpecEngine.step upd classify st msg).2 = if confirmOnHit.isEmpty then .none else mkBatchCmd (runMsgs upd (stepOnly st.confirmed (cont actual)) confirmOnHit).2 := by
  cases SpecEq.eq_of_true heq; unfold SpecEngine.step resolveHeadHit; rw [hcl, hlog]; dsimp only
  simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
  cases confirmOnHit with
  | nil =>
      refine ⟨?_, rfl⟩; cases st; dsimp only at hcoh hlog ⊢; subst hlog; unfold Coherent at hcoh
      simp only [List.isEmpty_nil, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append, List.nil_append, drainConfirmed, drainConfirmed_foldl_eq, List.foldl_cons, replayEntry, entryMsg] at hcoh ⊢
      exact congrArg (fun v => SpecState.mk v ..) hcoh
  | cons _ _ =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.cons_append, drainConfirmed, runMsgs_fst_eq_foldl, drainConfirmed_append_resolved]
      exact ⟨rfl, trivial⟩

end
end SpecEngine

namespace Internal

defAppProjSimps App.withSpeculative {State Msg : Type} (classify : State → Msg → SpecAction Msg) (app : App State Msg) =>
    App.withSpeculative classify app with
  [init := (SpecState.pure app.init.1, app.init.2), update := SpecEngine.step app.update classify, template := app.template.mapScope SpecState.visible]

section
variable {State Msg : Type} {Inv : State → Prop} (classify : State → Msg → SpecAction Msg) (app : App State Msg)

@[simp] theorem App.withSpeculative_view (st : SpecState State Msg) :
    App.view (App.withSpeculative classify app) st = App.view app st.visible := by simp only [App.view, App.withSpeculative, App.liftModel, View.render_mapScope]

theorem App.withSpeculative_init_inv (hinit : Inv app.init.1) : SpecEngine.SpecInv Inv (App.withSpeculative classify app).init.1 := ⟨hinit, hinit⟩
theorem App.withSpeculative_step_inv (hupd : ∀ s m, Inv s → Inv (app.update s m).1) (st : SpecState State Msg) (msg : Msg)
    (h : SpecEngine.SpecInv Inv st) : SpecEngine.SpecInv Inv ((App.withSpeculative classify app).update st msg).1 :=
  SpecEngine.step_preserves_inv app.update classify hupd st msg h
theorem App.withSpeculative_init_coherent : SpecEngine.Coherent (fun s m => (app.update s m).1) (App.withSpeculative classify app).init.1 := rfl
theorem App.withSpeculative_step_coherent (st : SpecState State Msg) (msg : Msg) (hcoh : SpecEngine.Coherent (fun s m => (app.update s m).1) st) :
    SpecEngine.Coherent (fun s m => (app.update s m).1) ((App.withSpeculative classify app).update st msg).1 :=
  SpecEngine.step_preserves_coherent app.update classify st msg hcoh
theorem App.withSpeculative_init_wellFormedIds : SpecEngine.WellFormedIds (App.withSpeculative classify app).init.1 := ⟨(fun _ h => nomatch h), List.nodup_nil⟩
theorem App.withSpeculative_step_wellFormedIds (st : SpecState State Msg) (msg : Msg) (hwf : SpecEngine.WellFormedIds st) :
    SpecEngine.WellFormedIds ((App.withSpeculative classify app).update st msg).1 :=
  SpecEngine.step_preserves_wellFormedIds app.update classify st msg hwf

private theorem withSpeculative_rehydrate_inv {raw : String} {st' : SpecState State Msg}
    (h : (App.withSpeculative classify app).rehydrate raw = some st') (hinv : ∀ m', app.rehydrate raw = some m' → Inv m') :
    SpecEngine.SpecInv Inv st' := let ⟨m', hm', e⟩ := Option.map_eq_some_iff.1 h; e ▸ ⟨hinv m' hm', hinv m' hm'⟩

theorem App.withSpeculative_rehydrate_sound (hsound : ∀ raw m', app.rehydrate raw = some m' → Inv m') (raw : String) (st' : SpecState State Msg)
    (h : (App.withSpeculative classify app).rehydrate raw = some st') : SpecEngine.SpecInv Inv st' := withSpeculative_rehydrate_inv classify app h (hsound raw)
theorem App.withSpeculative_dehydrate_inv (hpres : ∀ m m', Inv m → app.rehydrate (app.dehydrate m) = some m' → Inv m')
    (st st' : SpecState State Msg) (hst : SpecEngine.SpecInv Inv st) (h : (App.withSpeculative classify app).rehydrate ((App.withSpeculative classify app).dehydrate st) = some st') :
    SpecEngine.SpecInv Inv st' := withSpeculative_rehydrate_inv classify app h (hpres st.visible · hst.2)

end
end Internal
end Qed
