import Qed.Proofs.ViewPatch.VState

namespace Qed

section
variable {msg : Type}

/-! ## Verified Bare-Array Index & Certifying `O(N log N)` LIS Keyed Reconciler -/

private theorem bind_step {α β : Type} {m : StateM (DomArena msg) α} {k : α → StateM (DomArena msg) β} {a a' : DomArena msg} {r : α} (h : m a = (r, a')) : (m >>= k) a = k r a' := stateM_bind_step h

private theorem down_ind {n : Nat} {P : ∀ i, i ≤ n → Prop} (base : P n (Nat.le_refl n)) (step : ∀ i (hlt : i < n), P (i + 1) hlt → P i (Nat.le_of_lt hlt)) :
    ∀ i (hle : i ≤ n), P i hle := fun i hle => by
  induction h : n - i generalizing i with
  | zero => cases (show i = n by omega); exact base
  | succ _ ih => exact step i (by omega) (ih (i + 1) (by omega) (by omega))

private theorem htmlListNodeCount_append : ∀ (xs ys : List (Html msg)), htmlListNodeCount (xs ++ ys) = htmlListNodeCount xs + htmlListNodeCount ys
  | [], _ => by simp [htmlListNodeCount]
  | _ :: xs, ys => by simp [htmlListNodeCount, htmlListNodeCount_append xs ys, Nat.add_assoc]

private def KeyIdxInv (buckets : Array (List (String × Nat))) (mask : USize) (keys : Array String) (bound : Nat) : Prop :=
  0 < buckets.size ∧ (∀ k oi, keyIndexGet buckets mask k = some oi → oi < bound ∧ keys[oi]? = some k) ∧
  (∀ oi, oi < bound → ∀ k, keys[oi]? = some k → keyIndexGet buckets mask k = some oi)

private theorem buildKeyIndexLoop_spec (keys : Array String) (mask : USize) (hnd : keys.toList.Nodup) (i : Nat) (hle : i ≤ keys.size) :
    ∀ buckets, KeyIdxInv buckets mask keys i → KeyIdxInv (buildKeyIndexLoop keys i buckets mask) mask keys keys.size := by
  induction i, hle using down_ind with
  | base => intro buckets hinv; unfold buildKeyIndexLoop; simp [hinv]
  | step i hlt ih =>
      intro buckets hinv; unfold buildKeyIndexLoop; simp only [hlt, ↓reduceDIte, hinv.1]
      let k := keys[i]; let bi := strBucketIdx k mask buckets.size; have hbi := strBucketIdx_lt k mask buckets.size hinv.1
      let buckets' := buckets.set bi ((k, i) :: buckets[bi]) hbi; have hsz' : buckets'.size = buckets.size := Array.size_set ..; have hpos' : 0 < buckets'.size := hsz'.symm ▸ hinv.1
      have hget' : ∀ s, keyIndexGet buckets' mask s = if s == k then some i else keyIndexGet buckets mask s := fun s => by
        unfold keyIndexGet; simp only [hpos', hinv.1, ↓reduceDIte]
        rw [show buckets'[strBucketIdx s mask buckets'.size]'(strBucketIdx_lt s mask buckets'.size hpos') =
            if bi = strBucketIdx s mask buckets.size then (k, i) :: buckets[bi] else buckets[strBucketIdx s mask buckets.size]'(strBucketIdx_lt s mask buckets.size hinv.1) by simp only [buckets', hsz', Array.getElem_set]]
        by_cases hbiS : bi = strBucketIdx s mask buckets.size
        · simp only [hbiS, ↓reduceIte, kpLookupList]; by_cases hks : k = s; · subst hks; simp
          · simp [beq_eq_false_iff_ne.2 hks, beq_eq_false_iff_ne.2 (Ne.symm hks)]
        · simp only [hbiS, beq_eq_false_iff_ne.2 (show s ≠ k from fun h => hbiS (h ▸ rfl)), Bool.false_eq_true, ↓reduceIte]
      refine ih buckets' ⟨hpos', fun s oi hq => ?_, fun oi hoi s hs => ?_⟩
      · rw [hget'] at hq; by_cases hsk : (s == k) = true
        · simp only [hsk, ↓reduceIte, Option.some.injEq] at hq; subst hq; cases eq_of_beq hsk; exact ⟨Nat.lt_succ_self _, by simp [k, Array.getElem?_eq_getElem hlt]⟩
        · simp only [hsk, Bool.false_eq_true, ↓reduceIte] at hq; have ⟨h1, h2⟩ := hinv.2.1 s oi hq; exact ⟨Nat.lt_trans h1 (Nat.lt_succ_self _), h2⟩
      · rw [hget']; by_cases heqI : oi = i
        · subst heqI; rw [Array.getElem?_eq_getElem hlt, Option.some.injEq] at hs; subst hs; simp [k]
        · have hoiLt : oi < i := by omega
          have hneK : (s == k) = false := beq_eq_false_iff_ne.2 fun hsk => by
            subst hsk; rw [Array.getElem?_eq_getElem (Nat.lt_trans hoiLt hlt), Option.some.injEq] at hs
            exact heqI (nodup_getElem_inj (by simpa using Nat.lt_trans hoiLt hlt) (by simpa using hlt) hnd (by simpa [k] using hs))
          simp only [hneK, Bool.false_eq_true, ↓reduceIte]; exact hinv.2.2 oi hoiLt s hs

theorem buildKeyIndex_spec (keys : Array String) (hnd : keys.toList.Nodup) :
    let (buckets, mask) := buildKeyIndex keys
    (∀ k oi, keyIndexGet buckets mask k = some oi → oi < keys.size ∧ keys[oi]? = some k) ∧
    (∀ oi, oi < keys.size → ∀ k, keys[oi]? = some k → keyIndexGet buckets mask k = some oi) := by
  dsimp only [buildKeyIndex]; have hcap : 0 < nextPow2Ge (keys.size * 2) 16 30 := nextPow2Ge_pos _ 16 30 (by omega)
  exact (buildKeyIndexLoop_spec keys _ hnd 0 (Nat.zero_le _) _ ⟨by simp [hcap], fun _ _ hq => by unfold keyIndexGet at hq; simp [hcap, kpLookupList] at hq, fun _ _ => by omega⟩).2

private abbrev PlanKeyedOut (newKeys : Array String) (oldBuckets : Array (List (String × Nat))) (mask : USize)
    (oldRows : Array (Html msg)) (fresh : Unit → Array (Html msg)) (oldLen : Nat)
    (res : Array (Option Nat) × Array Bool × Array (Html msg) × Array USize × Array (Array (String × String))) : Prop :=
  res.1.size = newKeys.size ∧ res.2.1.size = oldLen ∧ res.2.2.1.size = newKeys.size ∧
  (∀ j (hj : j < newKeys.size), res.1.getD j none = keyIndexGet oldBuckets mask newKeys[j]) ∧
  (∀ oi, oi < oldLen → (res.2.1.getD oi false = true ↔ ∃ j, ∃ _ : j < newKeys.size, res.1.getD j none = some oi)) ∧
  (∀ j (hj : j < newKeys.size), res.2.2.1[j]? = some (match keyIndexGet oldBuckets mask newKeys[j] with | some oi => oldRows.getD oi default | none => (fresh ()).getD j default))

private theorem planKeyedLoop_spec (newKeys : Array String) (oldBuckets : Array (List (String × Nat))) (mask : USize)
    (oldRows : Array (Html msg)) (oldMarks : Array USize) (oldSigs : Array (Array (String × String))) (fresh : Unit → Array (Html msg)) (oldLen : Nat)
    (hidxBound : ∀ k oi, keyIndexGet oldBuckets mask k = some oi → oi < oldLen) (i : Nat) (hle : i ≤ newKeys.size) :
    ∀ freshCache (sources : Array (Option Nat)) (used : Array Bool) (rows : Array (Html msg)) marks sigs,
      (∀ arr, freshCache = some arr → arr = fresh ()) → (hss : sources.size = i) → (hus : used.size = oldLen) → (hrs : rows.size = i) →
      (∀ j (hj : j < i), sources[j]'(by omega) = keyIndexGet oldBuckets mask (newKeys[j]'(by omega))) →
      (∀ oi (ho : oi < oldLen), used[oi]'(by omega) = true ↔ ∃ j, ∃ _ : j < i, sources[j]'(by omega) = some oi) →
      (∀ j (hj : j < i), rows[j]'(by omega) = match keyIndexGet oldBuckets mask (newKeys[j]'(by omega)) with | some oi => oldRows.getD oi default | none => (fresh ()).getD j default) →
      PlanKeyedOut newKeys oldBuckets mask oldRows fresh oldLen (planKeyedLoop newKeys oldBuckets mask oldRows oldMarks oldSigs fresh freshCache i sources used rows marks sigs) := by
  induction i, hle using down_ind with
  | base =>
      intro _ sources used rows _ _ _ hss hus hrs hsrc hused hrows
      unfold planKeyedLoop; simp only [Nat.lt_irrefl, ↓reduceDIte, PlanKeyedOut]
      exact ⟨hss, hus, hrs, fun j hj => by simp only [Array.getD, hss, hj, ↓reduceDIte]; exact hsrc j hj,
        fun oi ho => by
          rw [show used.getD oi false = used[oi]'(by omega) by simp [Array.getD, hus, ho], hused oi ho]
          exact ⟨fun ⟨j, hj, hje⟩ => ⟨j, hj, by simpa [Array.getD, hss, hj] using hje⟩, fun ⟨j, hj, hje⟩ => ⟨j, hj, by simpa [Array.getD, hss, hj] using hje⟩⟩,
        fun j hj => by rw [Array.getElem?_eq_getElem (by omega)]; exact congrArg some (hrows j hj)⟩
  | step i hlt ih =>
      intro freshCache sources used rows marks sigs hfc hss hus hrs hsrc hused hrows
      unfold planKeyedLoop; simp only [hlt, ↓reduceDIte]
      have husedPush : ∀ (v : Option Nat) (oi' : Nat), oi' < oldLen → v ≠ some oi' →
          ((∃ j, ∃ _ : j < i, sources[j]'(by omega) = some oi') ↔ (∃ j, ∃ _ : j < i + 1, (sources.push v)[j]'(by rw [Array.size_push, hss]; omega) = some oi')) := fun v oi' _ hne =>
        ⟨fun ⟨j, hj, hje⟩ => ⟨j, Nat.lt_trans hj (Nat.lt_succ_self _), by simp [Array.getElem_push_lt (by omega : j < sources.size), hje]⟩,
         fun ⟨j, hj, hje⟩ => if hji : j < i then ⟨j, hji, by simpa [Array.getElem_push_lt (by omega : j < sources.size)] using hje⟩
           else by cases (show j = i by omega); rw [show (sources.push v)[i]'(by simp [hss]) = v by simpa [hss] using @Array.getElem_push_eq _ sources v] at hje; exact absurd hje hne⟩
      let rowFn (j : Nat) (hj : j < newKeys.size) := match keyIndexGet oldBuckets mask (newKeys[j]'hj) with | some oi => oldRows.getD oi default | none => (fresh ()).getD j default
      cases hq : keyIndexGet oldBuckets mask newKeys[i] with
      | some oi =>
          have hoi : oi < used.size := hus.symm ▸ hidxBound _ _ hq; simp only [hoi, ↓reduceDIte]
          refine ih freshCache (sources.push (some oi)) (used.set oi true hoi) (rows.push (oldRows.getD oi default)) (marks.push (oldMarks.getD oi 0)) (sigs.push (oldSigs.getD oi #[]))
            hfc (by simp [hss]) (by simp [hus]) (by simp [hrs]) (array_push_step_inv (f := fun j hj => keyIndexGet oldBuckets mask (newKeys[j]'hj)) hlt hss hsrc hq.symm)
            (fun oi' ho' => ?_) (array_push_step_inv (f := rowFn) hlt hrs hrows (by dsimp only [rowFn]; rw [hq]))
          by_cases heqO : oi' = oi
          · subst oi'; simp only [Array.getElem_set_self, true_iff]; exact ⟨i, Nat.lt_succ_self _, by simpa [hss] using @Array.getElem_push_eq _ sources (some oi)⟩
          · simp only [Array.getElem_set_ne (by omega : oi < used.size) (by omega) (Ne.symm heqO), hused oi' ho']; exact husedPush (some oi) oi' ho' fun h => heqO (Option.some.inj h).symm
      | none =>
          have hstep := ih (some (fresh ())) (sources.push none) used (rows.push ((fresh ()).getD i default)) (marks.push 0) (sigs.push #[])
            (fun _ h => (Option.some.inj h).symm) (by simp [hss]) hus (by simp [hrs])
            (array_push_step_inv (f := fun j hj => keyIndexGet oldBuckets mask (newKeys[j]'hj)) hlt hss hsrc hq.symm)
            (fun oi' ho' => (hused oi' ho').trans (husedPush none oi' ho' (by simp))) (array_push_step_inv (f := rowFn) hlt hrs hrows (by dsimp only [rowFn]; rw [hq]))
          cases freshCache with | none => exact hstep | some fArr => rw [hfc fArr rfl]; exact hstep

private theorem isValidLisLoop_sound (sources : Array (Option Nat)) (flags : Array Bool) (i : Nat) (hle : i ≤ sources.size) :
    ∀ last?, isValidLisLoop sources flags i last? = true →
      (∀ j, i ≤ j → j < sources.size → flags.getD j false = true → ∃ oi, sources.getD j none = some oi ∧ (∀ p, last? = some p → p < oi)) ∧
      (∀ j₁ j₂, i ≤ j₁ → j₁ < j₂ → j₂ < sources.size → flags.getD j₁ false = true → flags.getD j₂ false = true →
        ∀ oi₁ oi₂, sources.getD j₁ none = some oi₁ → sources.getD j₂ none = some oi₂ → oi₁ < oi₂) := by
  induction i, hle using down_ind with
  | base => exact fun _ _ => ⟨fun _ _ _ => by omega, fun _ _ _ _ _ => by omega⟩
  | step i hlt ih =>
      intro last? hv; unfold isValidLisLoop at hv; simp only [hlt, ↓reduceDIte] at hv
      cases hfi : flags.getD i false with
      | false =>
          simp only [hfi, Bool.false_eq_true, ↓reduceIte] at hv; have ⟨ih1, ih2⟩ := ih last? hv
          exact ⟨fun j h1 h2 hfj => if h : j = i then by subst h; simp [hfi] at hfj else ih1 j (by omega) h2 hfj,
                 fun j₁ j₂ h1 h2 h3 hf1 hf2 => if h : j₁ = i then by subst h; simp [hfi] at hf1 else ih2 j₁ j₂ (by omega) h2 h3 hf1 hf2⟩
      | true =>
          simp only [hfi, ↓reduceIte] at hv; cases hs : sources[i] with | none => simp [hs] at hv | some oi =>
          simp only [hs] at hv
          have hlast : ∀ p, last? = some p → p < oi := fun p hp => by subst hp; dsimp only at hv; split at hv <;> first | assumption | simp at hv
          have ⟨ih1, ih2⟩ := ih (some oi) (by cases last? with | none => exact hv | some p => simpa [hlast p rfl] using hv)
          exact ⟨fun j h1 h2 hfj => if h : j = i then by subst h; exact ⟨oi, by simpa [Array.getD, hlt] using hs, hlast⟩
                   else let ⟨oj, hsoj, hoiLt⟩ := ih1 j (by omega) h2 hfj; ⟨oj, hsoj, fun p hp => Nat.lt_trans (hlast p hp) (hoiLt oi rfl)⟩,
                 fun j₁ j₂ h1 h2 h3 hf1 hf2 oi₁ oi₂ hs1 hs2 => if h : j₁ = i then by
                   subst h; cases (show oi₁ = oi by simpa [Array.getD, hlt, hs] using hs1.symm)
                   rcases ih1 j₂ (by omega) h3 hf2 with ⟨oj, hsoj, hoiLt⟩; rw [Option.some.inj (hs2.symm.trans hsoj)]; exact hoiLt oi rfl
                 else ih2 j₁ j₂ (by omega) h2 h3 hf1 hf2 oi₁ oi₂ hs1 hs2⟩

theorem verifiedLisFlags_spec (sources : Array (Option Nat)) :
    let inLis := verifiedLisFlags sources
    (∀ j, j < sources.size → inLis.getD j false = true → ∃ oi, sources.getD j none = some oi) ∧
    (∀ j₁ j₂, j₁ < j₂ → j₂ < sources.size → inLis.getD j₁ false = true → inLis.getD j₂ false = true →
      ∀ oi₁ oi₂, sources.getD j₁ none = some oi₁ → sources.getD j₂ none = some oi₂ → oi₁ < oi₂) := by
  dsimp only [verifiedLisFlags]; split
  · rename_i hc; have ⟨h1, h2⟩ := isValidLisLoop_sound sources _ 0 (Nat.zero_le _) none (Bool.and_eq_true_iff.1 hc).2
    exact ⟨fun j hj hf => let ⟨oi, hoi, _⟩ := h1 j (Nat.zero_le _) hj hf; ⟨oi, hoi⟩, fun j₁ j₂ => h2 j₁ j₂ (Nat.zero_le _)⟩
  · exact ⟨fun j hj hf => by simp [Array.getD, hj] at hf, fun _ _ _ _ hf1 => by simp [Array.getD] at hf1⟩

private theorem filter_insertBeforeRef (p : Dom.Node → Bool) (child ref : Dom.Node) (hc : p child = true) (hr : p ref = true) :
    ∀ (xs : List Dom.Node), (insertBeforeRef child ref xs).filter p = insertBeforeRef child ref (xs.filter p)
  | [] => by simp [insertBeforeRef, hc]
  | x :: xs => by simp only [insertBeforeRef, List.filter_cons]; by_cases h : (x == ref) = true; · cases eq_of_beq h; simp [hr, hc, insertBeforeRef]
                  · simp only [h, Bool.false_eq_true, ↓reduceIte]; cases hpx : p x <;> simp [hpx, insertBeforeRef, h, filter_insertBeforeRef p child ref hc hr xs]

private theorem mem_insertBeforeRef_iff {child ref x : Dom.Node} : ∀ (xs : List Dom.Node), x ∈ insertBeforeRef child ref xs ↔ x = child ∨ x ∈ xs
  | [] => by simp [insertBeforeRef]
  | a :: xs => by simp only [insertBeforeRef]; by_cases h : (a == ref) = true; · simp [h, List.mem_cons]
                  · simp only [h, Bool.false_eq_true, ↓reduceIte, List.mem_cons, mem_insertBeforeRef_iff xs]; exact or_left_comm

private theorem nodup_insertBeforeRef {child ref : Dom.Node} : ∀ {xs : List Dom.Node}, xs.Nodup → child ∉ xs → (insertBeforeRef child ref xs).Nodup
  | [], _, _ => by simp [insertBeforeRef]
  | a :: xs, hnd, hnot => by rcases List.nodup_cons.1 hnd with ⟨ha, hxs⟩; simp only [insertBeforeRef]; by_cases h : (a == ref) = true
                             · simp only [h, ↓reduceIte]; exact List.nodup_cons.2 ⟨hnot, List.nodup_cons.2 ⟨ha, hxs⟩⟩
                             · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact List.nodup_cons.2 ⟨fun hm => ((mem_insertBeforeRef_iff xs).1 hm).elim (fun e => hnot (e ▸ .head _)) ha, nodup_insertBeforeRef hxs fun hm => hnot (.tail _ hm)⟩

private theorem erase_filter_of_false {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) (c : α) (hpc : p c = false) : ∀ {xs : List α}, (xs.erase c).filter p = xs.filter p
  | [] => rfl
  | x :: xs => by simp only [List.erase_cons]; by_cases h : (x == c) = true; · cases eq_of_beq h; simp [hpc]
                  · simp only [h, Bool.false_eq_true, ↓reduceIte, List.filter_cons]; cases p x <;> simp [erase_filter_of_false p c hpc]

private theorem removeUnusedM_spec (node : Dom.Node) (ns tag : String) (st : SpecElemState msg) (mg : List String)
    (live : Array Dom.Node) (used : Array Bool) (i : Nat) (hle : i ≤ live.size) :
    ∀ kept (a : DomArena msg), (kept ++ live.toList.drop i).Nodup → a.get node = .element ns tag st mg (kept ++ live.toList.drop i) →
      let aOut := (removeUnusedM (m := StateM (DomArena msg)) node live used i).run a |>.2
      aOut.nextId = a.nextId ∧ (∀ m, m ≠ node → aOut.get m = a.get m) ∧
      aOut.get node = .element ns tag st mg (kept ++ (List.range (live.size - i)).filterMap fun d => if used.getD (i + d) false then some (live.getD (i + d) 0) else none) := by
  induction i, hle using down_ind with
  | base =>
      intro kept a _ hget; unfold removeUnusedM; rw [List.drop_of_length_le (by simp), List.append_nil] at hget
      simp only [Nat.lt_irrefl, ↓reduceDIte, StateT.run, pure, StateT.pure, Nat.sub_self, List.range_zero, List.filterMap_nil, List.append_nil]
      exact ⟨trivial, fun _ _ => trivial, hget⟩
  | step i hlt ih =>
      intro kept a hnd hget
      rw [show live.toList.drop i = live[i] :: live.toList.drop (i + 1) by rw [List.drop_eq_getElem_cons (by simpa using hlt)]; rfl] at hnd hget
      have hshift : ((List.range (live.size - i)).filterMap fun d => if used.getD (i + d) false then some (live.getD (i + d) 0) else none) =
          (if used.getD i false then [live[i]] else []) ++ ((List.range (live.size - (i + 1))).filterMap fun d => if used.getD (i + 1 + d) false then some (live.getD (i + 1 + d) 0) else none) := by
        rw [show live.size - i = (live.size - (i + 1)) + 1 by omega, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map, Nat.add_zero]
        rw [show ((fun d => if used.getD (i + d) false then some (live.getD (i + d) 0) else none) ∘ (· + 1)) = (fun d => if used.getD (i + 1 + d) false then some (live.getD (i + 1 + d) 0) else none) by funext d; simp [Nat.add_comm d 1, Nat.add_assoc]]
        cases used.getD i false <;> simp [Array.getD, hlt]
      unfold removeUnusedM; simp only [hlt, ↓reduceDIte]
      cases hu : used.getD i false with
      | true =>
          simp only [↓reduceIte]; have hrec := ih (kept ++ [live[i]]) a (by simpa [List.append_assoc] using hnd) (by simpa [List.append_assoc] using hget)
          exact ⟨hrec.1, hrec.2.1, by rw [hrec.2.2, hshift, hu]; simp [List.append_assoc]⟩
      | false =>
          have hndP := List.nodup_append.1 hnd; let a1 := a.set node (.element ns tag st mg (kept ++ live.toList.drop (i + 1)))
          have hstep : MonadDom.removeNode (m := StateM (DomArena msg)) node live[i] a = ((), a1) := by
            simp only [MonadDom.removeNode, DomArena.modifyChildren, DomArena.modify, hget,
              erase_append_right_of_not_mem kept (live[i] :: live.toList.drop (i + 1)) fun hm => hndP.2.2 live[i] hm live[i] (.head _) rfl, List.erase_cons_head, a1]
          have hrec := ih kept a1 (List.nodup_append.2 ⟨hndP.1, (List.nodup_cons.1 hndP.2.1).2, fun x hx y hy => hndP.2.2 x hx y (.tail _ hy)⟩) (DomArena.get_set_self ..)
          dsimp only [StateT.run] at hrec; simp only [Bool.false_eq_true, ↓reduceIte, StateT.run, bind]; rw [stateM_bind_step hstep]
          exact ⟨hrec.1, fun m hm => (hrec.2.1 m hm).trans (DomArena.get_set_ne _ _ hm), by rw [hrec.2.2, hshift, hu]; simp⟩

private def filterLisNodes (live : Array Dom.Node) (sources : Array (Option Nat)) (inLis : Array Bool) (want : Bool) (k : Nat) : List Dom.Node :=
  (List.range k).filterMap fun i => if inLis.getD i false == want then (sources.getD i none).map (live.getD · 0) else none

private theorem filterLisNodes_succ (live : Array Dom.Node) (sources : Array (Option Nat)) (inLis : Array Bool) (want : Bool) (k : Nat) :
    filterLisNodes live sources inLis want (k + 1) = filterLisNodes live sources inLis want k ++
      (if inLis.getD k false == want then match sources.getD k none with | some oi => [live.getD oi 0] | none => [] else []) := by
  unfold filterLisNodes; rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases h : (inLis.getD k false == want); · simp
  · simp only [↓reduceIte]; cases sources.getD k none <;> rfl

private theorem mem_filterLisNodes (live : Array Dom.Node) (sources : Array (Option Nat)) (inLis : Array Bool) (want : Bool) (k : Nat) (x : Dom.Node) :
    x ∈ filterLisNodes live sources inLis want k ↔ ∃ i oi, i < k ∧ inLis.getD i false = want ∧ sources.getD i none = some oi ∧ live.getD oi 0 = x := by
  simp only [filterLisNodes, List.mem_filterMap, List.mem_range]
  exact ⟨fun ⟨i, hi, hif⟩ => by simp only [Option.ite_none_right_eq_some, Option.map_eq_some_iff, beq_iff_eq] at hif; rcases hif with ⟨hfl, oi, hs, hx⟩; exact ⟨i, oi, hi, hfl, hs, hx⟩,
         fun ⟨i, oi, hi, hfl, hs, hx⟩ => ⟨i, hi, by rw [← hx]; simp [hfl, hs]⟩⟩

private theorem w3cInsertBeforeRef_reconcile_step {cs mov lis placed : List Dom.Node} {ref? : Option Dom.Node} {x : Dom.Node}
    (hcsNd : cs.Nodup) (hanc : ref? = placed.head?) (hxNotPl : x ∉ placed) (hxNotMov : x ∉ mov)
    (hDisjMP : ∀ y, y ∈ mov → y ∈ placed → False) (hDisjLP : ∀ y, y ∈ lis → y ∈ placed → False)
    (hfiltEr : (cs.erase x).filter (fun y => !mov.contains y) = lis ++ placed) :
    let cs' := w3cInsertBeforeRef cs ref? x
    cs'.Nodup ∧ (∀ y, y ∈ cs' ↔ y = x ∨ y ∈ cs.erase x) ∧ cs'.filter (fun y => !mov.contains y) = lis ++ x :: placed := by
  have hcsErNd := List.Nodup.erase x hcsNd; have hxNotEr : x ∉ cs.erase x := List.Nodup.not_mem_erase hcsNd
  have hnotMovB : ∀ y, y ∉ mov → (!mov.contains y) = true := fun y hy => by cases hc : mov.contains y; rfl; exact absurd (List.contains_iff_mem.1 hc) hy
  subst hanc; dsimp only [w3cInsertBeforeRef]; cases placed with
  | nil => simp only [List.head?_nil]; exact ⟨List.nodup_append.2 ⟨hcsErNd, List.pairwise_singleton _ _, fun y hy z hz => by simp at hz; subst hz; exact fun he => hxNotEr (he ▸ hy)⟩,
      fun _ => by simp only [List.mem_append, List.mem_singleton]; exact ⟨fun h => h.elim .inr .inl, fun h => h.elim .inr .inl⟩, by rw [List.filter_append, hfiltEr, List.append_nil]; simp [hxNotMov]⟩
  | cons r ps =>
      have hrNe : (r == x) = false := beq_eq_false_iff_ne.2 fun h => hxNotPl (h ▸ .head _); simp only [List.head?_cons, hrNe, Bool.false_eq_true, ↓reduceIte]
      exact ⟨nodup_insertBeforeRef hcsErNd hxNotEr, fun _ => mem_insertBeforeRef_iff _, by rw [filter_insertBeforeRef _ x r (hnotMovB x hxNotMov) (hnotMovB r fun hm => hDisjMP r hm (.head _)), hfiltEr]; exact insertBeforeRef_split lis ps fun hm => hDisjLP r hm (.head _)⟩

private theorem pairwise_lt_ext : ∀ (xs ys : List Nat), xs.Pairwise (· < ·) → ys.Pairwise (· < ·) → (∀ a, a ∈ xs ↔ a ∈ ys) → xs = ys
  | [], [], _, _, _ => rfl | [], y :: _, _, _, h => nomatch (h y).2 (.head _) | x :: _, [], _, _, h => nomatch (h x).1 (.head _)
  | x :: xs, y :: ys, hx, hy, hiff => by
      rcases List.pairwise_cons.1 hx with ⟨hxLt, hxs⟩; rcases List.pairwise_cons.1 hy with ⟨hyLt, hys⟩
      have hxy : x = y := (List.mem_cons.1 ((hiff x).1 (.head _))).elim id fun hxt => (List.mem_cons.1 ((hiff y).2 (.head _))).elim Eq.symm fun hyt => by have := hxLt y hyt; have := hyLt x hxt; omega
      subst hxy; congr 1; exact pairwise_lt_ext xs ys hxs hys fun a => ⟨fun ha => (List.mem_cons.1 ((hiff a).1 (.tail _ ha))).resolve_left (Nat.ne_of_gt (hxLt a ha)), fun ha => (List.mem_cons.1 ((hiff a).2 (.tail _ ha))).resolve_left (Nat.ne_of_gt (hyLt a ha))⟩

private theorem pairwise_range_lt {n : Nat} : (List.range n).Pairwise (fun a b => a < n ∧ b < n ∧ a < b) :=
  List.pairwise_lt_range.imp_of_mem fun ha hb hab => ⟨List.mem_range.1 ha, List.mem_range.1 hb, hab⟩

private theorem lis_filter_kept_eq (live : Array Dom.Node) (sources : Array (Option Nat)) (inLis used : Array Bool) (n : Nat)
    (hsrcBound : ∀ i, i < n → ∀ oi, sources.getD i none = some oi → oi < live.size)
    (hsrcInj : ∀ i₁ i₂, i₁ < n → i₂ < n → ∀ oi, sources.getD i₁ none = some oi → sources.getD i₂ none = some oi → i₁ = i₂)
    (husedIff : ∀ oi, oi < live.size → (used.getD oi false = true ↔ ∃ i, ∃ _ : i < n, sources.getD i none = some oi)) (hliveNd : live.toList.Nodup)
    (hlisMono : ∀ i₁ i₂, i₁ < i₂ → i₂ < n → inLis.getD i₁ false = true → inLis.getD i₂ false = true → ∀ oi₁ oi₂, sources.getD i₁ none = some oi₁ → sources.getD i₂ none = some oi₂ → oi₁ < oi₂) :
    let kept := (List.range live.size).filterMap fun oi => if used.getD oi false then some (live.getD oi 0) else none
    kept.Nodup ∧ (∀ x, x ∈ kept ↔ x ∈ filterLisNodes live sources inLis false n ∨ x ∈ filterLisNodes live sources inLis true n) ∧
    (∀ x, x ∈ filterLisNodes live sources inLis false n → x ∈ filterLisNodes live sources inLis true n → False) ∧
    kept.filter (fun x => !(filterLisNodes live sources inLis false n).contains x) = filterLisNodes live sources inLis true n := by
  intro kept
  have hliveInj : ∀ oi₁ oi₂, oi₁ < live.size → oi₂ < live.size → live.getD oi₁ 0 = live.getD oi₂ 0 → oi₁ = oi₂ := fun oi₁ oi₂ h1 h2 heq =>
    nodup_getElem_inj (by simpa using h1) (by simpa using h2) hliveNd (by simpa [Array.getD, h1, h2] using heq)
  have hdisj : ∀ x, x ∈ filterLisNodes live sources inLis false n → x ∈ filterLisNodes live sources inLis true n → False := fun x hm hl => by
    rcases (mem_filterLisNodes ..).1 hm with ⟨i₁, oi₁, hi1, hf1, hs1, hx1⟩; rcases (mem_filterLisNodes ..).1 hl with ⟨i₂, oi₂, hi2, hf2, hs2, hx2⟩
    cases hliveInj oi₁ oi₂ (hsrcBound i₁ hi1 oi₁ hs1) (hsrcBound i₂ hi2 oi₂ hs2) (hx1.trans hx2.symm); cases hsrcInj i₁ i₂ hi1 hi2 oi₁ hs1 hs2; simp [hf1] at hf2
  refine ⟨List.Pairwise.filterMap _ (fun a a' hlt _ hb _ hb' heq => by simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hb hb'; have := hliveInj a a' hlt.1 hlt.2.1 (hb.2.trans (heq.trans hb'.2.symm)); omega) pairwise_range_lt,
    fun x => by simp only [kept, List.mem_filterMap, List.mem_range, Option.ite_none_right_eq_some, Option.some.injEq, mem_filterLisNodes]
                exact ⟨fun ⟨oi, hoi, hu, hx⟩ => let ⟨i, hi, hs⟩ := (husedIff oi hoi).1 hu; match hfl : inLis.getD i false with | false => .inl ⟨i, oi, hi, hfl, hs, hx⟩ | true => .inr ⟨i, oi, hi, hfl, hs, hx⟩,
                       fun h => by rcases h with ⟨i, oi, hi, _, hs, hx⟩ | ⟨i, oi, hi, _, hs, hx⟩ <;> exact ⟨oi, hsrcBound i hi oi hs, (husedIff oi (hsrcBound i hi oi hs)).2 ⟨i, hi, hs⟩, hx⟩⟩,
    hdisj, ?_⟩
  have hkm : ∀ l : List Nat, (l.filterMap fun oi => if used.getD oi false then some (live.getD oi 0) else none) = (l.filter (used.getD · false)).map (live.getD · 0) := fun l => by
    induction l with | nil => rfl | cons a r ih => simp only [List.filterMap_cons, List.filter_cons, ih]; cases used.getD a false <;> rfl
  rw [show kept = _ from hkm _, List.filter_map, List.filter_filter,
      show filterLisNodes live sources inLis true n = ((List.range n).filterMap fun i => if inLis.getD i false then sources.getD i none else none).map (live.getD · 0) by
        unfold filterLisNodes; rw [List.map_filterMap]; congr 1; funext i; cases inLis.getD i false <;> rfl,
      congrArg (List.map _) (List.filter_congr fun _ _ => Bool.and_comm ..)]
  refine congrArg (List.map (live.getD · 0)) (pairwise_lt_ext _ _ (List.Pairwise.filter _ List.pairwise_lt_range)
    (List.Pairwise.filterMap _ (fun i₁ i₂ hlt oi₁ h1 oi₂ h2 => by simp only [Option.ite_none_right_eq_some] at h1 h2; exact hlisMono i₁ i₂ hlt.2.2 hlt.2.1 h1.1 h2.1 oi₁ oi₂ h1.2 h2.2) pairwise_range_lt)
    fun oi => by
      simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, Function.comp_apply, Bool.not_eq_true', List.mem_filterMap, Option.ite_none_right_eq_some]
      exact ⟨fun ⟨hoi, hu, hnotM⟩ => let ⟨i, hi, hs⟩ := (husedIff oi hoi).1 hu; (by cases hfl : inLis.getD i false with | true => exact ⟨i, hi, hfl, hs⟩ | false => rw [List.contains_iff_mem.2 ((mem_filterLisNodes ..).2 ⟨i, oi, hi, hfl, hs, rfl⟩)] at hnotM; cases hnotM),
             fun ⟨i, hi, hfl, hif⟩ => let hoi := hsrcBound i hi oi hif; ⟨hoi, (husedIff oi hoi).2 ⟨i, hi, hif⟩, Bool.eq_false_iff.2 fun hc => hdisj _ (List.contains_iff_mem.1 hc) ((mem_filterLisNodes ..).2 ⟨i, oi, hi, hfl, hif, rfl⟩)⟩⟩)

private theorem htmlDomCleanList_mem : ∀ {l : List (Html msg)}, Html.DomCleanList l = true → ∀ h ∈ l, h.DomClean = true
  | [], _, _, h => nomatch h | _ :: _, hcl, h, hm => by simp only [Html.DomCleanList, Bool.and_eq_true] at hcl; exact (List.mem_cons.1 hm).elim (· ▸ hcl.1) (htmlDomCleanList_mem hcl.2 h)

private theorem htmlDepth_le_listDepth : ∀ {l : List (Html msg)}, ∀ h ∈ l, htmlDepth h ≤ htmlListDepth l
  | [], _, h => nomatch h | _ :: _, h, hm => by simp only [htmlListDepth]; exact (List.mem_cons.1 hm).elim (· ▸ Nat.le_max_left ..) fun ht => Nat.le_trans (htmlDepth_le_listDepth h ht) (Nat.le_max_right ..)

section LisBack
variable {f' : Nat} {node : Dom.Node} {realNs tag childNs : String} {st' : SpecElemState msg} {mg' : List String}
  {live : Array Dom.Node} {sources : Array (Option Nat)} {inLis : Array Bool} {rowsArr : Array (Html msg)}
  {newRowsL oldRowsL : List (Html msg)} {Si : Nat → Nat → Prop} {Sold : Nat → Prop} {baseNext : Nat}

private structure LisBackCtx (f' : Nat) (node : Dom.Node) (live : Array Dom.Node) (sources : Array (Option Nat))
    (rowsArr : Array (Html msg)) (newRowsL oldRowsL : List (Html msg)) (Si : Nat → Nat → Prop) (Sold : Nat → Prop) (baseNext : Nat) : Prop where
  hrows : rowsArr.toList = newRowsL ∧ live.size = oldRowsL.length ∧ live.toList.Nodup ∧ Html.DomCleanList newRowsL = true ∧ htmlListDepth newRowsL ≤ f'
  hsrcBound : ∀ i, i < newRowsL.length → ∀ oi, sources.getD i none = some oi → oi < oldRowsL.length
  hsrcInj : ∀ i₁ i₂, i₁ < newRowsL.length → i₂ < newRowsL.length → ∀ oi, sources.getD i₁ none = some oi → sources.getD i₂ none = some oi → i₁ = i₂
  hsrcRow : ∀ i (hi : i < newRowsL.length) oi (ho : oi < oldRowsL.length), sources.getD i none = some oi → oldRowsL[oi] = newRowsL[i]
  hSi : (∀ oi k, Si oi k → Sold k ∧ k ≠ node.toNat) ∧ (∀ oi₁ oi₂, oi₁ ≠ oi₂ → ∀ k, Si oi₁ k → Si oi₂ k → False) ∧ (∀ k, Sold k → k < baseNext)

private abbrev ReconcileBackOut (f' : Nat) (node : Dom.Node) (realNs tag childNs : String) (st' : SpecElemState msg) (mg' : List String)
    (newRowsL : List (Html msg)) (Sold : Nat → Prop) (baseNext k : Nat) (a aOut : DomArena msg) : Prop :=
  a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount (newRowsL.take k) ∧
  (∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aOut.get m = a.get m) ∧
  ∃ finalCs, aOut.get node = .element realNs tag st' mg' finalCs ∧
    CleanDomChildren f' childNs newRowsL aOut (fun m => (Sold m ∨ (baseNext ≤ m ∧ m < aOut.nextId)) ∧ m ≠ node.toNat) finalCs

private structure LisBackInv (f' : Nat) (node : Dom.Node) (realNs tag childNs : String) (st' : SpecElemState msg) (mg' : List String)
    (live : Array Dom.Node) (sources : Array (Option Nat)) (inLis : Array Bool) (newRowsL oldRowsL : List (Html msg))
    (Si : Nat → Nat → Prop) (Sold : Nat → Prop) (baseNext k : Nat) (hasAnchor : Bool) (anchor : Dom.Node) (cs placed : List Dom.Node) (Splaced : Nat → Prop) (a : DomArena msg) : Prop where
  hbnd : baseNext ≤ a.nextId ∧ 0 < a.nextId ∧ a.nextId + htmlListNodeCount (newRowsL.take k) < UInt32.size ∧ node.toNat < a.nextId
  hget : a.get node = .element realNs tag st' mg' cs ∧ cs.Nodup
  hanc : hasAnchor = !placed.isEmpty ∧ (if hasAnchor then some anchor else none) = placed.head?
  hcsMem : ∀ x, x ∈ cs ↔ x ∈ filterLisNodes live sources inLis false k ∨ x ∈ filterLisNodes live sources inLis true k ∨ x ∈ placed
  hDisj : (∀ x, x ∈ filterLisNodes live sources inLis false k → x ∈ filterLisNodes live sources inLis true k → False) ∧
    (∀ x, x ∈ filterLisNodes live sources inLis false k → x ∈ placed → False) ∧ (∀ x, x ∈ filterLisNodes live sources inLis true k → x ∈ placed → False)
  hfilt : cs.filter (fun x => !(filterLisNodes live sources inLis false k).contains x) = filterLisNodes live sources inLis true k ++ placed
  hOldClean : ∀ oi (ho : oi < oldRowsL.length), CleanDomSubtree f' childNs oldRowsL[oi] a (Si oi) (live.getD oi 0)
  hSp : (∀ m, Splaced m → (Sold m ∨ (baseNext ≤ m ∧ m < a.nextId)) ∧ m ≠ node.toNat) ∧
    (∀ i, i < k → ∀ oi, sources.getD i none = some oi → ∀ m, Si oi m → Splaced m → False)
  hClPl : CleanDomChildren f' childNs (newRowsL.drop k) a Splaced placed

private theorem reconcileLisBackM_spec (ctx : LisBackCtx f' node live sources rowsArr newRowsL oldRowsL Si Sold baseNext) :
    ∀ (k : Nat), k ≤ newRowsL.length → ∀ hasAnchor anchor cs placed Splaced a,
      LisBackInv f' node realNs tag childNs st' mg' live sources inLis newRowsL oldRowsL Si Sold baseNext k hasAnchor anchor cs placed Splaced a →
      ReconcileBackOut f' node realNs tag childNs st' mg' newRowsL Sold baseNext k a
        ((reconcileLisBackM (m := StateM (DomArena msg)) node childNs live sources inLis rowsArr k hasAnchor anchor).run a).2 := by
  have hliveInj : ∀ oi₁ oi₂, oi₁ < live.size → oi₂ < live.size → live.getD oi₁ 0 = live.getD oi₂ 0 → oi₁ = oi₂ := fun oi₁ oi₂ h1 h2 heq =>
    nodup_getElem_inj (Array.length_toList ▸ h1) (Array.length_toList ▸ h2) ctx.hrows.2.2.1 (by simp only [Array.getD, h1, h2, ↓reduceDIte] at heq; exact heq)
  intro k; induction k with
  | zero =>
      intro _ _ _ cs placed Splaced a inv; rcases inv with ⟨_, ⟨hget, _⟩, _, _, _, hfilt, _, ⟨hSpSub, _⟩, hClPl⟩
      dsimp only [ReconcileBackOut]; simp only [reconcileLisBackM, StateT.run, pure, StateT.pure, List.take_zero, htmlListNodeCount, Nat.add_zero, List.drop_zero] at hClPl ⊢
      have hcsEq : cs = placed := (List.filter_eq_self.2 (fun _ _ => rfl)).symm.trans (by simpa [filterLisNodes] using hfilt)
      subst hcsEq; exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ _ => trivial, cs, hget, CleanDomChildren_mono hSpSub hClPl⟩
  | succ k ih =>
      intro hk hasAnchor anchor cs placed Splaced a inv
      have hkLt : k < newRowsL.length := Nat.lt_of_succ_le hk
      have htakeCnt : htmlListNodeCount (newRowsL.take (k + 1)) = htmlListNodeCount (newRowsL.take k) + htmlNodeCount newRowsL[k] := by
        rw [List.take_succ_eq_append_getElem hkLt, htmlListNodeCount_append]; simp only [htmlListNodeCount, Nat.add_zero]
      have hdrop : newRowsL.drop k = newRowsL[k] :: newRowsL.drop (k + 1) := List.drop_eq_getElem_cons hkLt
      have hmono : ∀ w y, y ∈ filterLisNodes live sources inLis w k → y ∈ filterLisNodes live sources inLis w (k + 1) := fun w y hy => by rw [filterLisNodes_succ]; exact List.mem_append_left _ hy
      have hAfter (x : Dom.Node) (cs' : List Dom.Node) (Splaced' : Nat → Prop) (aNext : DomArena msg)
          (haGe : a.nextId ≤ aNext.nextId) (haBd : aNext.nextId ≤ a.nextId + htmlNodeCount newRowsL[k]) (haFr : ∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aNext.get m = a.get m)
          (hget' : aNext.get node = .element realNs tag st' mg' cs') (hcs'Nd : cs'.Nodup) (hxNotF : ∀ w, x ∉ filterLisNodes live sources inLis w k)
          (hcs'Mem : ∀ y, y ∈ cs' ↔ y ∈ filterLisNodes live sources inLis false k ∨ y ∈ filterLisNodes live sources inLis true k ∨ y ∈ x :: placed)
          (hcs'Filt : cs'.filter (fun y => !(filterLisNodes live sources inLis false k).contains y) = filterLisNodes live sources inLis true k ++ x :: placed)
          (hSpSub' : ∀ m, Splaced' m → (Sold m ∨ (baseNext ≤ m ∧ m < aNext.nextId)) ∧ m ≠ node.toNat) (hSpDisj' : ∀ i, i < k → ∀ oi', sources.getD i none = some oi' → ∀ m, Si oi' m → Splaced' m → False)
          (hClPl' : CleanDomChildren f' childNs (newRowsL.drop k) aNext Splaced' (x :: placed)) :
          ReconcileBackOut f' node realNs tag childNs st' mg' newRowsL Sold baseNext (k + 1) a ((reconcileLisBackM (m := StateM (DomArena msg)) node childNs live sources inLis rowsArr k true x).run aNext).2 := by
        have hres := ih (Nat.le_of_lt hkLt) true x cs' (x :: placed) Splaced' aNext
          ⟨⟨Nat.le_trans inv.hbnd.1 haGe, Nat.lt_of_lt_of_le inv.hbnd.2.1 haGe,
            Nat.lt_of_le_of_lt (Nat.add_le_add_right haBd _) (by rw [Nat.add_assoc, Nat.add_comm (htmlNodeCount newRowsL[k]), ← htakeCnt]; exact inv.hbnd.2.2.1),
            Nat.lt_of_lt_of_le inv.hbnd.2.2.2 haGe⟩, ⟨hget', hcs'Nd⟩, ⟨rfl, rfl⟩, hcs'Mem,
           ⟨fun y hm hl => inv.hDisj.1 y (hmono false y hm) (hmono true y hl),
            fun y hm hp => (List.mem_cons.1 hp).elim (fun h => hxNotF false (h ▸ hm)) (inv.hDisj.2.1 y (hmono false y hm)),
            fun y hl hp => (List.mem_cons.1 hp).elim (fun h => hxNotF true (h ▸ hl)) (inv.hDisj.2.2 y (hmono true y hl))⟩,
           hcs'Filt, fun oi ho => CleanDomSubtree_frame (fun m hm => let hsub := ctx.hSi.1 oi m.toNat hm
             haFr m (node_ne_of_toNat_ne hsub.2) (Nat.lt_of_lt_of_le (ctx.hSi.2.2 _ hsub.1) inv.hbnd.1)) (inv.hOldClean oi ho), ⟨hSpSub', hSpDisj'⟩, hClPl'⟩
        exact ⟨Nat.le_trans haGe hres.1, Nat.le_trans hres.2.1 (by rw [htakeCnt, Nat.add_comm (htmlListNodeCount (newRowsL.take k)), ← Nat.add_assoc]; exact Nat.add_le_add_right haBd _),
          fun m hmn hmLt => (hres.2.2.1 m hmn (Nat.lt_of_lt_of_le hmLt haGe)).trans (haFr m hmn hmLt), hres.2.2.2⟩
      have hInsert (x : Dom.Node) (Splaced' : Nat → Prop) (aMid : DomArena msg) (haGe : a.nextId ≤ aMid.nextId) (haBd : aMid.nextId ≤ a.nextId + htmlNodeCount newRowsL[k])
          (haFr : ∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aMid.get m = a.get m) (hgetMid : aMid.get node = .element realNs tag st' mg' cs)
          (hxNotPl : x ∉ placed) (hxNotF : ∀ w, x ∉ filterLisNodes live sources inLis w k)
          (hfiltEr : (cs.erase x).filter (fun y => !(filterLisNodes live sources inLis false k).contains y) = filterLisNodes live sources inLis true k ++ placed)
          (hmemEr : ∀ y, y = x ∨ y ∈ cs.erase x ↔ y ∈ filterLisNodes live sources inLis false k ∨ y ∈ filterLisNodes live sources inLis true k ∨ y ∈ x :: placed)
          (hSpSub' : ∀ m, Splaced' m → (Sold m ∨ (baseNext ≤ m ∧ m < aMid.nextId)) ∧ m ≠ node.toNat) (hSpDisj' : ∀ i, i < k → ∀ oi', sources.getD i none = some oi' → ∀ m, Si oi' m → Splaced' m → False)
          (hClPlMid : CleanDomChildren f' childNs (newRowsL.drop k) aMid Splaced' (x :: placed)) :
          ReconcileBackOut f' node realNs tag childNs st' mg' newRowsL Sold baseNext (k + 1) a
            ((do MonadDom.insertBeforeRef (m := StateM (DomArena msg)) node (if hasAnchor then some anchor else none) x; reconcileLisBackM node childNs live sources inLis rowsArr k true x).run aMid).2 := by
        let cs' := w3cInsertBeforeRef cs (if hasAnchor then some anchor else none) x
        have ⟨hcs'Nd, hmemC', hcs'Filt⟩ := w3cInsertBeforeRef_reconcile_step inv.hget.2 inv.hanc.2 hxNotPl (hxNotF false) (fun y hm => inv.hDisj.2.1 y (hmono false y hm)) (fun y hl => inv.hDisj.2.2 y (hmono true y hl)) hfiltEr
        dsimp only [StateT.run]; rw [bind_step (show MonadDom.insertBeforeRef (m := StateM (DomArena msg)) node (if hasAnchor then some anchor else none) x aMid = ((), aMid.set node (.element realNs tag st' mg' cs')) by simp only [MonadDom.insertBeforeRef, DomArena.modifyChildren, DomArena.modify, hgetMid, cs'])]
        exact hAfter x cs' Splaced' (aMid.set node (.element realNs tag st' mg' cs')) haGe haBd (fun m hmn hmLt => (DomArena.get_set_ne _ _ hmn).trans (haFr m hmn hmLt))
          (DomArena.get_set_self ..) hcs'Nd hxNotF (fun y => (hmemC' y).trans (hmemEr y)) hcs'Filt hSpSub' hSpDisj' (CleanDomChildren_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSpSub' m.toNat hm).2)) hClPlMid)
      have hcsMem := inv.hcsMem; have hfilt := inv.hfilt; dsimp only [reconcileLisBackM, StateT.run, bind, StateT.bind]
      cases hsK : sources.getD k none with
      | some oi =>
          have hoi : oi < oldRowsL.length := ctx.hsrcBound k hkLt oi hsK; let child := live.getD oi 0
          have hClPl' : CleanDomChildren f' childNs (newRowsL.drop k) a (fun m => Si oi m ∨ Splaced m) (child :: placed) := by
            rw [hdrop]; exact ⟨Si oi, Splaced, fun _ => .inl, fun _ => .inr, inv.hSp.2 k (Nat.lt_succ_self k) oi hsK, ctx.hsrcRow k hkLt oi hoi hsK ▸ inv.hOldClean oi hoi, inv.hClPl⟩
          have hSpSub' : ∀ m, (Si oi m ∨ Splaced m) → (Sold m ∨ (baseNext ≤ m ∧ m < a.nextId)) ∧ m ≠ node.toNat := fun m hm => hm.elim (fun h1 => ⟨.inl (ctx.hSi.1 oi m h1).1, (ctx.hSi.1 oi m h1).2⟩) (inv.hSp.1 m)
          have hSpDisj' : ∀ i, i < k → ∀ oi', sources.getD i none = some oi' → ∀ m, Si oi' m → (Si oi m ∨ Splaced m) → False := fun i hi oi' hs' m hm1 hm2 =>
            hm2.elim (ctx.hSi.2.1 oi' oi (fun he => Nat.ne_of_lt hi (ctx.hsrcInj i k (Nat.lt_trans hi hkLt) hkLt oi' hs' (he ▸ hsK))) m hm1) (inv.hSp.2 i (Nat.lt_succ_of_lt hi) oi' hs' m hm1)
          have hchildNotF : ∀ w, child ∉ filterLisNodes live sources inLis w k := fun w hm => by
            rcases (mem_filterLisNodes ..).1 hm with ⟨i, oi', hi, _, hsi, hEq⟩
            exact Nat.ne_of_lt hi (ctx.hsrcInj i k (Nat.lt_trans hi hkLt) hkLt oi' hsi (hliveInj oi' oi (ctx.hrows.2.1 ▸ ctx.hsrcBound i (Nat.lt_trans hi hkLt) oi' hsi) (ctx.hrows.2.1 ▸ hoi) hEq ▸ hsK))
          cases hflK : inLis.getD k false with
          | true =>
              simp only [↓reduceIte]; rw [filterLisNodes_succ, filterLisNodes_succ, hflK, hsK] at hcsMem hfilt
              simp only [beq_false, Bool.not_true, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, List.append_nil] at hcsMem hfilt
              exact hAfter child cs (fun m => Si oi m ∨ Splaced m) a (Nat.le_refl _) (Nat.le_add_right _ _) (fun _ _ _ => rfl) inv.hget.1 inv.hget.2 hchildNotF
                (fun x => by rw [hcsMem x]; simp only [child, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc]) (by simpa [child, List.append_assoc] using hfilt) hSpSub' hSpDisj' hClPl'
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]; rw [filterLisNodes_succ, filterLisNodes_succ, hflK, hsK] at hcsMem hfilt
              simp only [beq_self_eq_true, beq_true, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hcsMem hfilt
              have hchildNotEr : child ∉ cs.erase child := List.Nodup.not_mem_erase inv.hget.2
              exact hInsert child (fun m => Si oi m ∨ Splaced m) a (Nat.le_refl _) (Nat.le_add_right _ _) (fun _ _ _ => rfl) inv.hget.1
                (fun hp => inv.hDisj.2.1 child (by rw [filterLisNodes_succ, hflK, hsK]; simp [child]) hp) hchildNotF
                (by rw [List.filter_congr (q := fun x => !(filterLisNodes live sources inLis false k ++ [child]).contains x) fun x hx => by
                      simp only [List.contains_append, List.contains_cons, List.contains_nil, Bool.or_false, beq_eq_false_iff_ne.2 (show x ≠ child from fun h => hchildNotEr (h ▸ hx))],
                    erase_filter_of_false _ child (by simp only [List.contains_append, List.contains_cons, beq_self_eq_true, Bool.true_or, Bool.or_true, Bool.not_true]), hfilt])
                (fun x => by by_cases hx : x = child; · subst hx; simp
                             · simp only [child, hx, false_or, List.mem_erase_of_ne hx, hcsMem x, List.mem_append, List.mem_cons, List.not_mem_nil, or_false])
                hSpSub' hSpDisj' hClPl'
      | none =>
          have hStepF : ∀ w, filterLisNodes live sources inLis w (k + 1) = filterLisNodes live sources inLis w k := fun w => by rw [filterLisNodes_succ, hsK]; cases (inLis.getD k false == w) <;> simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
          rw [hStepF false, hStepF true] at hcsMem hfilt
          rw [show rowsArr.getD k default = newRowsL[k] by
            have hkArr : k < rowsArr.size := by rw [← Array.length_toList, ctx.hrows.1]; exact hkLt
            simp only [Array.getD, hkArr, ↓reduceDIte]
            exact (Array.getElem_toList (xs := rowsArr) (i := k) (h := hkArr)).symm.trans (Option.some.inj (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, ctx.hrows.1]))]
          have hbm := buildDomM_spec_full childNs newRowsL[k] a f' inv.hbnd.2.1
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left _ _) _) (htakeCnt ▸ inv.hbnd.2.2.1)) (Nat.le_trans (htmlDepth_le_listDepth newRowsL[k] (List.getElem_mem hkLt)) ctx.hrows.2.2.2.2)
          dsimp only [StateT.run] at hbm; cases hbr : buildDomM (m := StateM (DomArena msg)) childNs newRowsL[k] a with
          | mk cn a1 =>
              rw [hbr] at hbm; rcases hbm with ⟨hcnGe, _, ha1Ext, _, _, hbuiltFn⟩
              have ha1Fr : ∀ m : Dom.Node, m.toNat < a.nextId → a1.get m = a.get m := fun m hm => ha1Ext.frame m hm id
              have hfiltInA : ∀ w x, x ∈ filterLisNodes live sources inLis w k → x.toNat < a.nextId := fun _ _ hx => by
                rcases (mem_filterLisNodes ..).1 hx with ⟨i, oi', hi, _, hsi, rfl⟩
                exact Nat.lt_of_lt_of_le (ctx.hSi.2.2 _ (ctx.hSi.1 oi' _ (CleanDomSubtree_root_mem (inv.hOldClean oi' (ctx.hsrcBound i (Nat.lt_trans hi hkLt) oi' hsi)))).1) inv.hbnd.1
              have hcnNotCs : cn ∉ cs := fun hm => Nat.not_lt.2 hcnGe <| match (hcsMem cn).1 hm with
                | .inl h => hfiltInA false cn h | .inr (.inl h) => hfiltInA true cn h
                | .inr (.inr hp) => (inv.hSp.1 cn.toNat (CleanDomChildren_mem inv.hClPl cn hp)).1.elim (fun hs => Nat.lt_of_lt_of_le (ctx.hSi.2.2 _ hs) inv.hbnd.1) (·.2)
              have hcsErEq : cs.erase cn = cs := List.erase_of_not_mem hcnNotCs; dsimp only; rw [stateM_bind_step hbr]
              refine hInsert cn (fun m => (a.nextId ≤ m ∧ m < a1.nextId) ∨ Splaced m) a1 ha1Ext.next_ge ha1Ext.next_le (fun m _ hm => ha1Fr m hm)
                ((ha1Fr node inv.hbnd.2.2.2).trans inv.hget.1) (fun hm => hcnNotCs ((hcsMem cn).2 (.inr (.inr hm))))
                (fun w hm => hcnNotCs ((hcsMem cn).2 (by cases w; exact .inl hm; exact .inr (.inl hm)))) (hcsErEq.symm ▸ hfilt)
                (fun x => by rw [hcsErEq, hcsMem x, List.mem_cons, or_left_comm (a := x = cn), or_left_comm (a := x = cn)])
                (fun m hm => hm.elim (fun ⟨h1, h2⟩ => ⟨.inr ⟨Nat.le_trans inv.hbnd.1 h1, h2⟩, fun e => Nat.not_lt.2 h1 (e ▸ inv.hbnd.2.2.2)⟩)
                  fun h2 => let ⟨h, hne⟩ := inv.hSp.1 m h2; ⟨h.elim .inl fun ⟨hb, hl⟩ => .inr ⟨hb, Nat.lt_of_lt_of_le hl ha1Ext.next_ge⟩, hne⟩)
                (fun i hi oi' hs' m hm1 hm2 => hm2.elim (fun h1 => Nat.not_lt.2 h1.1 (Nat.lt_of_lt_of_le (ctx.hSi.2.2 m (ctx.hSi.1 oi' m hm1).1) inv.hbnd.1)) (inv.hSp.2 i (Nat.lt_succ_of_lt hi) oi' hs' m hm1)) ?_
              rw [hdrop]
              exact ⟨_, Splaced, fun _ => .inl, fun _ => .inr,
                fun m h1 h2 => (inv.hSp.1 m h2).1.elim (fun hs => Nat.not_lt.2 h1.1 (Nat.lt_of_lt_of_le (ctx.hSi.2.2 m hs) inv.hbnd.1)) fun h2 => Nat.not_lt.2 h1.1 h2.2,
                hbuiltFn (htmlDomCleanList_mem ctx.hrows.2.2.2.1 newRowsL[k] (List.getElem_mem hkLt)),
                CleanDomChildren_frame (fun m hm => ha1Fr m ((inv.hSp.1 m.toNat hm).1.elim (fun hs => Nat.lt_of_lt_of_le (ctx.hSi.2.2 _ hs) inv.hbnd.1) (·.2))) inv.hClPl⟩
end LisBack

private theorem appendFragmentRowsM_spec (f' : Nat) (childNs : String) (node : Dom.Node) (realNs tag : String) (st' : SpecElemState msg) (mg' : List String)
    (rows : List (Html msg)) (Sold : Nat → Prop) (a aBase : DomArena msg) (hrowsClean : Html.DomCleanList rows = true)
    (hbound : a.nextId + (1 + htmlListNodeCount rows) < UInt32.size) (hdep : htmlListDepth rows ≤ f') (hpos : 0 < a.nextId) (hnodeLt : node.toNat < a.nextId)
    (haBaseN : aBase.nextId = a.nextId) (haBaseNode : aBase.get node = .element realNs tag st' mg' []) (haBaseOut : ∀ m, m ≠ node → aBase.get m = a.get m) :
    ∃ aOut csNew, (∀ {α} (k : StateM (DomArena msg) α),
        (do let frag ← MonadDom.createFragment; buildDomListM (Dom.childNsOf childNs tag) frag rows; MonadDom.appendChild node frag; k) aBase = k aOut) ∧
      a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + (1 + htmlListNodeCount rows) ∧ (∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      aOut.get node = .element realNs tag st' mg' csNew ∧ CleanDomChildren f' (Dom.childNsOf childNs tag) rows aOut (fun k => (Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ node.toNat) csNew := by
  let frag := UInt32.ofNat aBase.nextId; let aFragBase : DomArena msg := { aBase with nextId := aBase.nextId + 1 }
  have haFragNext : aFragBase.nextId = a.nextId + 1 := by dsimp only [aFragBase]; rw [haBaseN]
  have hfragToNat : frag.toNat = a.nextId := by dsimp only [frag]; rw [haBaseN]; exact uint32_toNat_ofNat_lt a.nextId (by omega)
  have hfragNeNode : frag ≠ node := node_ne_of_toNat_ne (by omega)
  rcases buildDomListM_spec_full (Dom.childNsOf childNs tag) rows aFragBase frag ArenaEntry.fragment (.inr fun _ => rfl) [] f' (by omega) (by omega) (by omega) hdep (fun _ h => nomatch h) with ⟨csNew, aBase', haBuiltEq, haBuiltExt, _, _, hCleanFn⟩
  have hCleanOut := hCleanFn [] (fun _ => False) hrowsClean (fun _ h => h.elim) trivial; simp only [List.nil_append, false_or] at haBuiltEq hCleanOut
  let aBuilt := (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf childNs tag) frag rows (aFragBase.set frag (.fragment []))).2
  have haBuiltGe : a.nextId + 1 ≤ aBuilt.nextId := haFragNext ▸ haBuiltExt.next_ge
  have haBuiltBd : aBuilt.nextId ≤ a.nextId + (1 + htmlListNodeCount rows) := by have := haBuiltExt.next_le; dsimp only [aBuilt, StateT.run] at *; omega
  have haBuiltFr : ∀ m : Dom.Node, m.toNat < a.nextId + 1 → m ≠ frag → aBuilt.get m = aFragBase.get m := fun m hm hne => haBuiltExt.frame m (haFragNext.symm ▸ hm) fun h => hne (uint32_eq_of_toNat_eq h)
  let aOut := (aBuilt.set frag .null).set node (.element realNs tag st' mg' csNew); have haOutN : aOut.nextId = aBuilt.nextId := rfl
  have happendRun : MonadDom.appendChild (m := StateM (DomArena msg)) node frag aBuilt = ((), aOut) := by
    simp only [MonadDom.appendChild, show aBuilt.get frag = .fragment csNew by rw [show aBuilt = aBase'.set frag (.fragment csNew) from haBuiltEq, DomArena.get_set_self],
      DomArena.modifyChildren, DomArena.modify, DomArena.get_set_ne _ _ hfragNeNode.symm, (haBuiltFr node (by omega) hfragNeNode.symm).trans haBaseNode, List.filter_nil, List.nil_append, aOut]
  refine ⟨aOut, csNew, fun k => by rw [bind_step (show MonadDom.createFragment (m := StateM (DomArena msg)) aBase = (frag, aFragBase.set frag (.fragment [])) from rfl),
      bind_step (show buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf childNs tag) frag rows (aFragBase.set frag (.fragment [])) = ((), aBuilt) from rfl), bind_step happendRun],
    by omega, by omega, fun m hmn hmLt => by have hmf : m ≠ frag := node_ne_of_toNat_ne (by omega); dsimp only [aOut]; rw [DomArena.get_set_ne _ _ hmn, DomArena.get_set_ne _ _ hmf, haBuiltFr m (by omega) hmf]; exact haBaseOut m hmn,
    DomArena.get_set_self .., CleanDomChildren_mono (fun k ⟨hk1, hk2⟩ => ⟨.inr ⟨by omega, hk2⟩, by omega⟩)
      (CleanDomChildren_frame (a' := aOut) (fun m ⟨hm1, _⟩ => by simp only [aOut, DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega) : m ≠ node), DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega) : m ≠ frag)]; rfl) hCleanOut)⟩

private theorem bind_seedRowsM {α : Type} (inst : String) (rs : Nat → Array (String × String)) (re : Nat → Array (String × msg))
    (nm om : Array USize) (os : Array (Array (String × String))) (a : DomArena msg) (k : Array (Array (String × String)) → StateM (DomArena msg) α)
    {P : α × DomArena msg → Prop} (h : ∀ r a', a'.SameDom a → P (k r a')) : P ((seedRowsM (m := StateM (DomArena msg)) inst rs re nm om os >>= k) a) := by
  have hs := seedRowsM_sameDom inst rs re nm om os a; dsimp only [StateT.run] at hs
  cases hr : seedRowsM (m := StateM (DomArena msg)) inst rs re nm om os a with | mk r a' => rw [hr] at hs; rw [bind_step hr]; exact h r a' hs

private theorem childNs_elem_step {childNs pns ptag tag : String} {node : Dom.Node} {st' : SpecElemState msg} {mg' : List String} {cs : List Dom.Node} {a : DomArena msg}
    (hc : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") (hg : a.get node = .element (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st' mg' cs) :
    MonadDom.childNamespace (m := StateM (DomArena msg)) node a = (Dom.childNsOf childNs tag, a) := by
  dsimp only [MonadDom.childNamespace]; rw [hg]; exact congrArg (·, a) (childNamespace_eq_childNsOf (ptag := tag) (by rw [hc]; split <;> simp))

section
variable {σ : Type} {f' : Nat} {childNs pns ptag tag inst : String} {parent node : Dom.Node} {pst : SpecElemState msg} {pmg : List String}
  {attrs : List (VAttr σ msg)} {keys : σ → Array String} {marks : σ → Array USize}
  {rowSig : σ → Array String → Nat → Array (String × String)} {rowEv : σ → Array String → Nat → Array (String × msg)}
  {rowsHtml : σ → List (Html msg)} {s₁ s₂ : σ} {pre suf : List Dom.Node} {Sold : Nat → Prop} {a : DomArena msg} {st : SpecElemState msg} {mg : List String} {domCs : List Dom.Node}

private abbrev DynAttrsOk (attrs : List (VAttr σ msg)) (s₂ : σ) (st' : SpecElemState msg) (mg' : List String) : Prop :=
  ElemClean st' mg' ∧ ElemStateEquiv st' (evalSpecAttrs (attrs.map (VAttr.eval s₂))) ∧ (∀ nm ∈ (normalizeAttrs (attrs.map (VAttr.eval s₂))).filterMap managedAttrName, mg'.contains nm = true)

private structure KeyedPatchCtx (f' : Nat) (childNs pns ptag tag : String) (parent node : Dom.Node) (pst : SpecElemState msg) (pmg : List String)
    (attrs : List (VAttr σ msg)) (keys : σ → Array String) (rowsHtml : σ → List (Html msg)) (s₁ s₂ : σ) (pre suf : List Dom.Node)
    (Sold : Nat → Prop) (a : DomArena msg) (st : SpecElemState msg) (mg : List String) (domCs : List Dom.Node) : Prop where
  hclean : (childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") ∧ VAttrListClean attrs ∧ KeyedRowsClean keys rowsHtml
  hbnd : a.nextId + (1 + htmlListNodeCount (rowsHtml s₂)) < UInt32.size ∧ htmlListDepth (rowsHtml s₂) ≤ f' ∧ parent.toNat < a.nextId ∧ 0 < a.nextId
  hpar : a.get parent = .element pns ptag pst pmg (pre ++ node :: suf) ∧ (pre ++ node :: suf).Nodup ∧ ¬Sold parent.toNat ∧ (∀ k, Sold k → k < a.nextId) ∧ (∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId)
  hnode : Sold node.toNat ∧ a.get node = .element (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st mg domCs ∧ DynAttrsOk attrs s₁ st mg ∧ CleanDomChildren f' (Dom.childNsOf childNs tag) (rowsHtml s₁) a (fun k => Sold k ∧ k ≠ node.toNat) domCs

private theorem keyedList_finish_goal {st' : SpecElemState msg} {mg' : List String} {csNew : List Dom.Node} {aOut : DomArena msg}
    {outKeys : Array String} {outSigs : Array (Array (String × String))} {outRows : List (Html msg)} {outMarks : Array USize}
    (ctx : KeyedPatchCtx f' childNs pns ptag tag parent node pst pmg attrs keys rowsHtml s₁ s₂ pre suf Sold a st mg domCs)
    (haOutGe : a.nextId ≤ aOut.nextId) (haOutBd : aOut.nextId ≤ a.nextId + (1 + htmlListNodeCount (rowsHtml s₂))) (haOutFr : ∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aOut.get m = a.get m)
    (haOutNode : aOut.get node = .element (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st' mg' csNew) (hDyn₂ : DynAttrsOk attrs s₂ st' mg')
    (hCleanOut : CleanDomChildren f' (Dom.childNsOf childNs tag) (rowsHtml s₂) aOut (fun k => (Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ node.toNat) csNew) (hkeysEq : outKeys = disambiguateKeys (keys s₂)) (hrowsEq : outRows = rowsHtml s₂) :
    PatchViewPost (f' + 1) childNs parent pns ptag pst pmg (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ pre suf Sold a (.list node outKeys outSigs outRows outMarks inst, aOut) :=
  have hvalOut : VStateValid (f' + 1) childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ aOut (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) (.list node outKeys outSigs outRows outMarks inst) :=
    ⟨⟨.inl ctx.hnode.1, ctx.hclean.2.1.1 s₂, ctx.hclean.2.1.2.1 s₂, st', mg', csNew, haOutNode, hDyn₂.1, hDyn₂.2.1, hDyn₂.2.2, hCleanOut⟩, rfl, hkeysEq, hrowsEq⟩
  ⟨haOutGe, by simp only [View.render, htmlNodeCount]; exact haOutBd, fun m _ hmSold hmLt => haOutFr m (fun h => hmSold (h ▸ ctx.hnode.1)) hmLt,
    by rw [haOutFr parent (fun h => ctx.hpar.2.2.1 (h ▸ ctx.hnode.1)) ctx.hbnd.2.2.1, ctx.hpar.1]; rfl, ctx.hpar.2.1, fun r hr => Nat.lt_of_lt_of_le (ctx.hpar.2.2.2.2 r hr) haOutGe, hvalOut, VStateValid_equiv hvalOut⟩

private theorem keyedList_appendFrag_finish {st' : SpecElemState msg} {mg' : List String} {aBase : DomArena msg} {outSigs : Array (Array (String × String))} {outMarks : Array USize}
    (ctx : KeyedPatchCtx f' childNs pns ptag tag parent node pst pmg attrs keys rowsHtml s₁ s₂ pre suf Sold a st mg domCs)
    (haBaseN : aBase.nextId = a.nextId) (haBaseNode : aBase.get node = .element (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st' mg' []) (haBaseOut : ∀ m, m ≠ node → aBase.get m = a.get m) (hDyn₂ : DynAttrsOk attrs s₂ st' mg') :
    PatchViewPost (f' + 1) childNs parent pns ptag pst pmg (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ pre suf Sold a
      ((do let frag ← MonadDom.createFragment (m := StateM (DomArena msg)); buildDomListM (Dom.childNsOf childNs tag) frag (rowsHtml s₂); MonadDom.appendChild node frag; pure (VState.list node (disambiguateKeys (keys s₂)) outSigs (rowsHtml s₂) outMarks inst)) aBase) := by
  rcases appendFragmentRowsM_spec f' childNs node (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st' mg'
      (rowsHtml s₂) Sold a aBase (ctx.hclean.2.2.2.1 s₂) ctx.hbnd.1 ctx.hbnd.2.1 ctx.hbnd.2.2.2 (ctx.hpar.2.2.2.1 _ ctx.hnode.1) haBaseN haBaseNode haBaseOut with ⟨_, _, hrun, h1, h2, h3, h4, h5⟩
  rw [hrun]; exact keyedList_finish_goal ctx h1 h2 h3 h4 hDyn₂ h5 rfl rfl

private theorem patchViewM_keyedList_lis_spec {oldSigs : Array (Array (String × String))} {oldMarks : Array USize}
    (ctx : KeyedPatchCtx f' childNs pns ptag tag parent node pst pmg attrs keys rowsHtml s₁ s₂ pre suf Sold a st mg domCs)
    (hrawNe : keys s₂ ≠ disambiguateKeys (keys s₁)) (hsameNe : disambiguateKeys (keys s₂) ≠ disambiguateKeys (keys s₁))
    (hnewEmp : (disambiguateKeys (keys s₂)).isEmpty = false) (hemp : (rowsHtml s₁).isEmpty = false) :
    PatchViewPost (f' + 1) childNs parent pns ptag pst pmg (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ pre suf Sold a
      ((patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ (.list node (disambiguateKeys (keys s₁)) oldSigs (rowsHtml s₁) oldMarks inst)).run a) := by
  have hnodeLt : node.toNat < a.nextId := ctx.hpar.2.2.2.1 _ ctx.hnode.1; let realNs := if childNs == "" && tag == "svg" then Dom.svgNs else childNs
  dsimp only [patchViewM, StateT.run]; simp only [beq_eq_false_iff_ne.2 hrawNe, beq_eq_false_iff_ne.2 hsameNe, hnewEmp, hemp, Bool.false_eq_true, ↓reduceIte]
  let oldKeys := disambiguateKeys (keys s₁); let newKeys := disambiguateKeys (keys s₂); have hidxSpec := buildKeyIndex_spec oldKeys (disambiguateKeys_nodup (keys s₁))
  let oldBuckets := (buildKeyIndex oldKeys).1; let mask := (buildKeyIndex oldKeys).2; let freshFn : Unit → Array (Html msg) := fun _ => ((rowsHtml s₂).map (Html.prefixSignals inst)).toArray
  have hsz1 := ctx.hclean.2.2.1 s₁; have hsz2 := ctx.hclean.2.2.1 s₂; let rF := Array.replicate oldKeys.size false
  let plan := planKeyedLoop newKeys oldBuckets mask (rowsHtml s₁).toArray oldMarks oldSigs freshFn none 0 (Array.emptyWithCapacity newKeys.size) rF (Array.emptyWithCapacity newKeys.size) (Array.emptyWithCapacity newKeys.size) (Array.emptyWithCapacity newKeys.size)
  have hplanSpec := planKeyedLoop_spec newKeys oldBuckets mask (rowsHtml s₁).toArray oldMarks oldSigs freshFn oldKeys.size (fun k oi hq => (hidxSpec.1 k oi hq).1) 0 (Nat.zero_le _)
    none (Array.emptyWithCapacity newKeys.size) rF (Array.emptyWithCapacity newKeys.size) (Array.emptyWithCapacity newKeys.size) (Array.emptyWithCapacity newKeys.size) (fun _ h => nomatch h) rfl (Array.size_replicate ..) rfl (fun _ hj => absurd hj (Nat.not_lt_zero _))
    (fun _ _ => ⟨(fun h => by rw [Array.getElem_replicate] at h; cases h), (fun ⟨_, hj, _⟩ => absurd hj (Nat.not_lt_zero _))⟩) (fun _ hj => absurd hj (Nat.not_lt_zero _))
  let sources := plan.1; let used := plan.2.1; let rowsArr := plan.2.2.1; let marksArr := plan.2.2.2.1; let sigsArr := plan.2.2.2.2
  have hsrcSz : sources.size = (rowsHtml s₂).length := hplanSpec.1.trans hsz2.symm; have hsrcGet := hplanSpec.2.2.2.1
  have hsrcBound : ∀ i, i < (rowsHtml s₂).length → ∀ oi, sources.getD i none = some oi → oi < (rowsHtml s₁).length := fun i hi oi hsi => by rw [hsrcGet i (hsz2 ▸ hi)] at hsi; rw [hsz1]; exact (hidxSpec.1 _ oi hsi).1
  have hsrcInj : ∀ i₁ i₂, i₁ < (rowsHtml s₂).length → i₂ < (rowsHtml s₂).length → ∀ oi, sources.getD i₁ none = some oi → sources.getD i₂ none = some oi → i₁ = i₂ := fun i₁ i₂ h1 h2 oi hs1 hs2 => by
    rw [hsrcGet i₁ (hsz2 ▸ h1)] at hs1; rw [hsrcGet i₂ (hsz2 ▸ h2)] at hs2
    exact nodup_getElem_inj (Array.length_toList ▸ hsz2 ▸ h1) (Array.length_toList ▸ hsz2 ▸ h2) (disambiguateKeys_nodup (keys s₂)) (Option.some.inj ((hidxSpec.1 _ oi hs1).2.symm.trans (hidxSpec.1 _ oi hs2).2))
  have hsrcRow : ∀ i (hi : i < (rowsHtml s₂).length) oi (ho : oi < (rowsHtml s₁).length), sources.getD i none = some oi → (rowsHtml s₁)[oi] = (rowsHtml s₂)[i] := fun i hi oi ho hsi => by
    rw [hsrcGet i (hsz2 ▸ hi)] at hsi; have hkeyEq : oldKeys[oi]'(hsz1 ▸ ho) = newKeys[i]'(hsz2 ▸ hi) := by have h := (hidxSpec.1 _ oi hsi).2; rw [Array.getElem?_eq_getElem (hsz1 ▸ ho), Option.some.injEq] at h; exact h
    have hrowEq := ctx.hclean.2.2.2.2.2 s₁ s₂ oi i (hsz1 ▸ ho) (hsz2 ▸ hi) hkeyEq; rw [List.getElem?_eq_getElem ho, List.getElem?_eq_getElem hi, Option.some.injEq] at hrowEq; exact hrowEq
  have hrowsArrEq : rowsArr.toList = rowsHtml s₂ := by
    have hpref := Html.map_prefixSignals_of_DomCleanList inst (ctx.hclean.2.2.2.1 s₂); refine List.ext_getElem? fun i => ?_; rw [Array.getElem?_toList]
    by_cases hi : i < newKeys.size
    · have hri : i < (rowsHtml s₂).length := hsz2 ▸ hi; rw [hplanSpec.2.2.2.2.2 i hi]
      cases hq : keyIndexGet oldBuckets mask newKeys[i] with
      | none => simp only [freshFn, hpref, Array.getD, List.size_toArray, hri, ↓reduceDIte, List.getElem?_eq_getElem hri]; rfl
      | some oi => have hsi := (hsrcGet i hi).trans hq; have hoi1 := hsrcBound i hri oi hsi; simp only [Array.getD, List.size_toArray, hoi1, ↓reduceDIte, List.getElem?_eq_getElem hri]; exact congrArg some (hsrcRow i hri oi hoi1 hsi)
    · rw [Array.getElem?_eq_none (hplanSpec.2.2.1.symm ▸ Nat.not_lt.1 hi), List.getElem?_eq_none (hsz2.symm ▸ Nat.not_lt.1 hi)]
  refine bind_seedRowsM inst (rowSig s₂ newKeys) (rowEv s₂ newKeys) (marks s₂) marksArr sigsArr a _ fun _ aSeed hseed0 => ?_
  have hdyn := applyDynAttrsM_spec aSeed node realNs tag st mg domCs attrs s₁ s₂ ctx.hclean.2.1 ctx.hnode.2.2.1.1 ctx.hnode.2.2.1.2.1 ctx.hnode.2.2.1.2.2
  rw [DomArena.set_get_self aSeed ((hseed0.get_eq node).trans ctx.hnode.2.1)] at hdyn; rcases hdyn with ⟨ha1Next, ha1Ne, st', mg', ha1Get, hDyn₂⟩
  let a1 := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ aSeed).2
  have ha1N : a1.nextId = a.nextId := ha1Next.trans hseed0.1; have ha1Out : ∀ m, m ≠ node → a1.get m = a.get m := fun m hm => (ha1Ne m hm).trans (hseed0.get_eq m)
  rw [bind_step (show applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ aSeed = ((), a1) from rfl), bind_step (childNs_elem_step ctx.hclean.1 ha1Get)]
  split
  · let aClr := a1.set node (.element realNs tag st' mg' [])
    rw [bind_step (show MonadDom.clearChildren (m := StateM (DomArena msg)) node a1 = ((), aClr) by dsimp only [MonadDom.clearChildren, DomArena.modifyChildren, DomArena.modify, aClr]; rw [ha1Get]), hrowsArrEq]
    exact keyedList_appendFrag_finish ctx ha1N (DomArena.get_set_self ..) (fun m hm => (DomArena.get_set_ne _ _ hm).trans (ha1Out m hm)) hDyn₂
  · have ⟨hdomNd, hdomLen⟩ := CleanDomChildren_nodup ctx.hnode.2.2.2
    have hdomLtU32 : domCs.length < UInt32.size := Nat.lt_of_le_of_lt (nodup_nodes_lt_length_le a.nextId domCs hdomNd fun x hx => ctx.hpar.2.2.2.1 _ (CleanDomChildren_mem ctx.hnode.2.2.2 x hx).1) (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) ctx.hbnd.1)
    have hsnap := snapshotChildrenM_spec a1 node realNs tag st' mg' domCs hdomLtU32 0 domCs.length #[] (Nat.zero_add _)
    rw [DomArena.set_get_self a1 ha1Get] at hsnap; dsimp only [StateT.run, List.nil_append, List.drop_zero] at hsnap
    let live : Array Dom.Node := ⟨domCs⟩; have hliveSz : live.size = (rowsHtml s₁).length := hdomLen
    have hremSpec := removeUnusedM_spec node realNs tag st' mg' live used 0 (Nat.zero_le _) [] a1 hdomNd ha1Get
    let aRem := (removeUnusedM (m := StateM (DomArena msg)) node live used 0).run a1 |>.2
    have haRemN : aRem.nextId = a.nextId := hremSpec.1.trans ha1N; have haRemOut : ∀ m, m ≠ node → aRem.get m = a.get m := fun m hm => (hremSpec.2.1 m hm).trans (ha1Out m hm)
    let kept := (List.range live.size).filterMap fun oi => if used.getD oi false then some (live.getD oi 0) else none; let inLis := verifiedLisFlags sources
    have hkeptSpec := lis_filter_kept_eq live sources inLis used (rowsHtml s₂).length (fun i hi oi hsi => hliveSz.symm ▸ hsrcBound i hi oi hsi) hsrcInj
      (fun oi ho => by rw [hsz2]; exact hplanSpec.2.2.2.2.1 oi (hsz1 ▸ hliveSz ▸ ho)) hdomNd (fun i₁ i₂ h1 h2 => (verifiedLisFlags_spec sources).2 i₁ i₂ h1 (hsrcSz.symm ▸ h2))
    rcases CleanDomChildren_indexed ctx.hnode.2.2.2 with ⟨Si, hSiSub, hSiDisj, hSiGet⟩
    have hrec := reconcileLisBackM_spec (realNs := realNs) (tag := tag) (childNs := Dom.childNsOf childNs tag) (st' := st') (mg' := mg') (live := live) (inLis := inLis)
      ⟨⟨hrowsArrEq, hdomLen, hdomNd, ctx.hclean.2.2.2.1 s₂, ctx.hbnd.2.1⟩, hsrcBound, hsrcInj, hsrcRow, ⟨hSiSub, hSiDisj, ctx.hpar.2.2.2.1⟩⟩
      (rowsHtml s₂).length (Nat.le_refl _) false 0 kept [] (fun _ => False) aRem
      ⟨⟨by omega, by have := ctx.hbnd.2.2.2; omega, by rw [haRemN, List.take_length]; have := ctx.hbnd.1; omega, by omega⟩,
       ⟨by simpa only [List.nil_append, Nat.zero_add, Nat.sub_zero] using hremSpec.2.2, hkeptSpec.1⟩, ⟨rfl, rfl⟩,
       fun x => by rw [hkeptSpec.2.1 x]; simp only [List.not_mem_nil, or_false], ⟨hkeptSpec.2.2.1, (fun _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩,
       by rw [List.append_nil]; exact hkeptSpec.2.2.2,
       fun oi ho => by have hoD : oi < domCs.length := hdomLen ▸ ho; rw [show live.getD oi 0 = domCs[oi] by rw [Array.getD, dif_pos (show oi < live.size from hoD)]; rfl]
                       exact CleanDomSubtree_frame (fun m hm => haRemOut m (node_ne_of_toNat_ne (hSiSub oi m.toNat hm).2)) (hSiGet oi ho hoD),
       ⟨(fun _ h => h.elim), (fun _ _ _ _ _ _ h => h.elim)⟩, by rw [List.drop_length]; trivial⟩
    rw [bind_step (show MonadDom.childCount (m := StateM (DomArena msg)) node a1 = (UInt32.ofNat domCs.length, a1) by dsimp only [MonadDom.childCount]; rw [ha1Get]),
        uint32_toNat_ofNat_lt domCs.length hdomLtU32, bind_step hsnap, bind_step (show removeUnusedM (m := StateM (DomArena msg)) node live used 0 a1 = ((), aRem) from rfl)]
    cases hrecRun : reconcileLisBackM (m := StateM (DomArena msg)) node (Dom.childNsOf childNs tag) live sources inLis rowsArr (rowsHtml s₂).length false 0 aRem with
    | mk _ aOut =>
        rw [bind_step ((congrArg (reconcileLisBackM (m := StateM (DomArena msg)) node (Dom.childNsOf childNs tag) live sources inLis rowsArr · false 0 aRem) hsz2.symm).trans hrecRun)]
        dsimp only [StateT.run] at hrec; rw [hrecRun] at hrec; dsimp only at hrec ⊢; rcases hrec with ⟨haOutGe, haOutBd, haOutFr, _, haOutNode, hCleanOut⟩
        rw [haRemN] at haOutGe haOutBd haOutFr; rw [List.take_length] at haOutBd; rw [hrowsArrEq]
        exact keyedList_finish_goal ctx haOutGe (by omega) (fun m hmn hmLt => (haOutFr m hmn hmLt).trans (haRemOut m hmn)) haOutNode hDyn₂ hCleanOut rfl rfl
end

theorem patchViewM_keyedList_spec {σ : Type} (f : Nat) (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (tag : String) (attrs : List (VAttr σ msg)) (keys : σ → Array String) (marks : σ → Array USize)
    (rowSig : σ → Array String → Nat → Array (String × String)) (rowEv : σ → Array String → Nat → Array (String × msg))
    (rowsHtml : σ → List (Html msg)) (tmpl? : Option (RowTmpl σ msg)) (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg)
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") (hclean : View.DomClean (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?))
    (hbound : a.nextId + htmlNodeCount (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂) < UInt32.size)
    (hdep : htmlDepth (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂) ≤ f)
    (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId) (hpar : a.get parent = .element pns ptag pst pmg (pre ++ vst.rootNode :: suf))
    (hnd : (pre ++ vst.rootNode :: suf).Nodup) (hparOut : ¬Sold parent.toNat) (hSoldLt : ∀ k, Sold k → k < a.nextId)
    (hparNodes : ∀ r ∈ pre ++ vst.rootNode :: suf, r.toNat < a.nextId) (hval : VStateValid f childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₁ a Sold vst) :
    PatchViewPost f childNs parent pns ptag pst pmg (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂ pre suf Sold a
      ((patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂ vst).run a) := by
  cases tmpl? with | some _ => exact False.elim hclean | none =>
  cases vst with
  | list node oldKeys oldSigs oldRowsL oldMarks inst =>
    rcases hclean with ⟨haClean, hrowsClean⟩; rcases hval with ⟨hcl, _, rfl, rfl⟩; dsimp only [VState.rootNode] at hpar hnd hparNodes
    cases f with | zero => exact False.elim hcl | succ f' =>
    rcases hcl with ⟨hnodeMem, _, _, st, mg, domCs, hnodeGet, hElClean, hElEq, hmg, hCleanCs⟩; dsimp only [VState.rootNode] at hnodeMem hnodeGet hCleanCs
    simp only [View.render, htmlNodeCount] at hbound; simp only [View.render, htmlDepth] at hdep
    have ctx : KeyedPatchCtx f' childNs pns ptag tag parent node pst pmg attrs keys rowsHtml s₁ s₂ pre suf Sold a st mg domCs :=
      ⟨⟨hchildNs, haClean, hrowsClean⟩, ⟨hbound, by omega, hparLt, hpos⟩, ⟨hpar, hnd, hparOut, hSoldLt, hparNodes⟩, ⟨hnodeMem, hnodeGet, ⟨hElClean, hElEq, hmg⟩, hCleanCs⟩⟩
    let realNs := if childNs == "" && tag == "svg" then Dom.svgNs else childNs
    have hdyn := applyDynAttrsM_spec a node realNs tag st mg domCs attrs s₁ s₂ haClean hElClean hElEq hmg
    rw [DomArena.set_get_self a hnodeGet] at hdyn; rcases hdyn with ⟨ha1Next, ha1Ne, st', mg', ha1Get, hDyn₂⟩
    let a1 := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a).2; have ha1Eq : applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a = ((), a1) := rfl
    by_cases hsameK : disambiguateKeys (keys s₂) = disambiguateKeys (keys s₁)
    · dsimp only [patchViewM, StateT.run]; simp only [beq_iff_eq.2 hsameK, ↓reduceIte, ite_self]; rw [bind_step ha1Eq]
      refine bind_seedRowsM inst (rowSig s₂ (disambiguateKeys (keys s₁))) (rowEv s₂ (disambiguateKeys (keys s₁))) (marks s₂) oldMarks oldSigs a1 _ fun _ aOut hseed => ?_
      have haOutNext : aOut.nextId = a.nextId := hseed.1.trans ha1Next; have haOutOut : ∀ m, m ≠ node → aOut.get m = a.get m := fun m hm => (hseed.get_eq m).trans (ha1Ne m hm)
      have hrowsEq : rowsHtml s₁ = rowsHtml s₂ := keyedRows_eq_of_keys_eq hrowsClean hsameK
      exact keyedList_finish_goal ctx (by omega) (by omega) (fun m hm _ => haOutOut m hm) ((hseed.get_eq node).trans ha1Get) hDyn₂
        (by rw [← hrowsEq]; exact CleanDomChildren_mono (fun k hk => ⟨.inl hk.1, hk.2⟩) (CleanDomChildren_frame (fun m hm => haOutOut m (node_ne_of_toNat_ne hm.2)) hCleanCs)) hsameK.symm hrowsEq
    · have hrawNe : keys s₂ ≠ disambiguateKeys (keys s₁) := fun h => hsameK ((disambiguateKeys_of_nodup (h ▸ disambiguateKeys_nodup (keys s₁))).trans h)
      cases hnewEmp : (disambiguateKeys (keys s₂)).isEmpty
      · cases hemp : (rowsHtml s₁).isEmpty
        · exact patchViewM_keyedList_lis_spec ctx hrawNe hsameK hnewEmp hemp
        · dsimp only [patchViewM, StateT.run]; simp only [beq_eq_false_iff_ne.2 hrawNe, beq_eq_false_iff_ne.2 hsameK, hnewEmp, hemp, Bool.false_eq_true, ↓reduceIte]; rw [bind_step ha1Eq]
          have hnilDom : domCs = [] := by rw [List.isEmpty_iff.1 hemp] at hCleanCs; cases domCs <;> first | rfl | exact False.elim hCleanCs
          refine bind_seedRowsM inst (rowSig s₂ (disambiguateKeys (keys s₂))) (rowEv s₂ (disambiguateKeys (keys s₂))) (marks s₂) #[] #[] a1 _ fun _ aSeed hseed => ?_
          have haSeedNode : aSeed.get node = .element realNs tag st' mg' [] := by rw [hseed.get_eq node, ha1Get, hnilDom]
          rw [bind_step (childNs_elem_step hchildNs haSeedNode), Html.map_prefixSignals_of_DomCleanList inst (hrowsClean.2.1 s₂)]
          exact keyedList_appendFrag_finish ctx (hseed.1.trans ha1Next) haSeedNode (fun m hm => (hseed.get_eq m).trans (ha1Ne m hm)) hDyn₂
      · dsimp only [patchViewM, StateT.run]; simp only [beq_eq_false_iff_ne.2 hrawNe, beq_eq_false_iff_ne.2 hsameK, hnewEmp, Bool.false_eq_true, ↓reduceIte]
        have hnewKeysEq : disambiguateKeys (keys s₂) = #[] := Array.isEmpty_iff.1 hnewEmp; have hnewRows0 : rowsHtml s₂ = [] := List.eq_nil_of_length_eq_zero (by rw [hrowsClean.1 s₂, hnewKeysEq]; rfl)
        let aOut := a1.set node (.element realNs tag st' mg' [])
        rw [bind_step ha1Eq, bind_step (show MonadDom.clearChildren (m := StateM (DomArena msg)) node a1 = ((), aOut) by dsimp only [MonadDom.clearChildren, DomArena.modifyChildren, DomArena.modify, aOut]; rw [ha1Get])]
        exact keyedList_finish_goal ctx (ha1Next ▸ Nat.le_refl _) (by rw [show aOut.nextId = a.nextId from ha1Next]; omega)
          (fun m hm _ => (DomArena.get_set_ne _ _ hm).trans (ha1Ne m hm)) (DomArena.get_set_self ..) hDyn₂ (by rw [hnewRows0]; trivial) hnewKeysEq.symm hnewRows0.symm
  | _ => exact False.elim hval.2

end
end Qed
