import Qed.Proofs.ViewPatch.VState

namespace Qed

/-! ## Verified Bare-Array Index & Certifying `O(N log N)` LIS Keyed Reconciler -/

private theorem htmlListNodeCount_append {msg : Type} :
    ∀ (xs ys : List (Html msg)), htmlListNodeCount (xs ++ ys) = htmlListNodeCount xs + htmlListNodeCount ys
  | [], ys => by simp [htmlListNodeCount]
  | x :: xs, ys => by simp [htmlListNodeCount, htmlListNodeCount_append xs ys, Nat.add_assoc]

private def KeyIdxInv (buckets : Array (List (String × Nat))) (mask : USize)
    (keys : Array String) (bound : Nat) : Prop :=
  0 < buckets.size ∧
  (∀ k oi, keyIndexGet buckets mask k = some oi → oi < bound ∧ keys[oi]? = some k) ∧
  (∀ oi, oi < bound → ∀ k, keys[oi]? = some k → keyIndexGet buckets mask k = some oi)

private theorem buildKeyIndexLoop_spec (keys : Array String) (mask : USize)
    (hnd : keys.toList.Nodup) :
    ∀ (i : Nat) (buckets : Array (List (String × Nat))),
      i ≤ keys.size →
      KeyIdxInv buckets mask keys i →
      KeyIdxInv (buildKeyIndexLoop keys i buckets mask) mask keys keys.size := by
  intro i
  induction hrem : keys.size - i generalizing i with
  | zero =>
      intro buckets hle hinv
      have hi : i = keys.size := by omega
      subst hi; unfold buildKeyIndexLoop; simp [hinv]
  | succ r ih =>
      intro buckets hle hinv
      have hlt : i < keys.size := by omega
      unfold buildKeyIndexLoop
      simp only [hlt, ↓reduceDIte, hinv.1]
      let k := keys[i]
      let bi := strBucketIdx k mask buckets.size
      have hbi : bi < buckets.size := strBucketIdx_lt k mask buckets.size hinv.1
      let buckets' := buckets.set bi ((k, i) :: buckets[bi]) hbi
      have hsz' : buckets'.size = buckets.size := Array.size_set ..
      have hpos' : 0 < buckets'.size := by rw [hsz']; exact hinv.1
      have hget' : ∀ s, keyIndexGet buckets' mask s =
          if s == k then some i else keyIndexGet buckets mask s := by
        intro s; unfold keyIndexGet
        simp only [hpos', hinv.1, ↓reduceDIte]
        have hidxEq : strBucketIdx s mask buckets'.size = strBucketIdx s mask buckets.size := by rw [hsz']
        have hset : buckets'[strBucketIdx s mask buckets'.size]'(strBucketIdx_lt s mask buckets'.size hpos') =
            if bi = strBucketIdx s mask buckets.size then (k, i) :: buckets[bi]
            else buckets[strBucketIdx s mask buckets.size]'(strBucketIdx_lt s mask buckets.size hinv.1) := by
          simp only [buckets', hidxEq, Array.getElem_set]
        rw [hset]
        by_cases hbiS : bi = strBucketIdx s mask buckets.size
        · simp only [hbiS, ↓reduceIte, kpLookupList]
          by_cases hks : k = s
          · subst hks; simp
          · simp [beq_eq_false_iff_ne.2 hks, beq_eq_false_iff_ne.2 (Ne.symm hks)]
        · have hsk : (s == k) = false := beq_eq_false_iff_ne.2 fun h => hbiS (h ▸ rfl)
          simp only [hbiS, hsk, Bool.false_eq_true, ↓reduceIte]
      have hinv' : KeyIdxInv buckets' mask keys (i + 1) := by
        refine ⟨hpos', ?_, ?_⟩
        · intro s oi hq; rw [hget'] at hq
          by_cases hsk : (s == k) = true
          · simp only [hsk, ↓reduceIte, Option.some.injEq] at hq; subst hq
            have heq : s = k := eq_of_beq hsk; subst heq
            exact ⟨Nat.lt_succ_self _, by simp [k, Array.getElem?_eq_getElem hlt]⟩
          · simp only [hsk, Bool.false_eq_true, ↓reduceIte] at hq
            have ⟨hlt0, hget0⟩ := hinv.2.1 s oi hq
            exact ⟨Nat.lt_trans hlt0 (Nat.lt_succ_self _), hget0⟩
        · intro oi hoi s hs; rw [hget']
          by_cases heqI : oi = i
          · subst heqI
            have hsk : s = k := by rw [Array.getElem?_eq_getElem hlt, Option.some.injEq] at hs; exact hs.symm
            subst hsk; simp
          · have hoiLt : oi < i := by omega
            have hneK : (s == k) = false := beq_eq_false_iff_ne.2 fun hsk => by
              subst hsk
              have h1 : keys[oi]'(Nat.lt_trans hoiLt hlt) = k := by
                rw [Array.getElem?_eq_getElem (Nat.lt_trans hoiLt hlt), Option.some.injEq] at hs; exact hs
              exact heqI (nodup_getElem_inj (by simpa using Nat.lt_trans hoiLt hlt) (by simpa using hlt) hnd (by simpa [k] using h1))
            simp only [hneK, Bool.false_eq_true, ↓reduceIte]
            exact hinv.2.2 oi hoiLt s hs
      exact ih (i + 1) (by omega) buckets' (by omega) hinv'

theorem buildKeyIndex_spec (keys : Array String) (hnd : keys.toList.Nodup) :
    let (buckets, mask) := buildKeyIndex keys
    (∀ k oi, keyIndexGet buckets mask k = some oi → oi < keys.size ∧ keys[oi]? = some k) ∧
    (∀ oi, oi < keys.size → ∀ k, keys[oi]? = some k → keyIndexGet buckets mask k = some oi) := by
  dsimp only [buildKeyIndex]
  have hcap : 0 < nextPow2Ge (keys.size * 2) 16 30 := nextPow2Ge_pos _ 16 30 (by omega)
  have hinv0 : KeyIdxInv (Array.replicate (nextPow2Ge (keys.size * 2) 16 30) [])
      (USize.ofNat (nextPow2Ge (keys.size * 2) 16 30 - 1)) keys 0 :=
    ⟨by simp [hcap], fun k oi hq => by unfold keyIndexGet at hq; simp [hcap, kpLookupList] at hq, fun _ hoi => by omega⟩
  exact (buildKeyIndexLoop_spec keys _ hnd 0 _ (Nat.zero_le _) hinv0).2

private abbrev PlanKeyedOut {msg : Type} (newKeys : Array String)
    (oldBuckets : Array (List (String × Nat))) (mask : USize)
    (oldRows : Array (Html msg)) (fresh : Unit → Array (Html msg)) (oldLen : Nat)
    (res : Array (Option Nat) × Array Bool × Array (Html msg) × Array USize × Array (Array (String × String))) : Prop :=
  res.1.size = newKeys.size ∧ res.2.1.size = oldLen ∧ res.2.2.1.size = newKeys.size ∧
  (∀ j (hj : j < newKeys.size), res.1.getD j none = keyIndexGet oldBuckets mask newKeys[j]) ∧
  (∀ oi, oi < oldLen → (res.2.1.getD oi false = true ↔ ∃ j, ∃ _ : j < newKeys.size, res.1.getD j none = some oi)) ∧
  (∀ j (hj : j < newKeys.size), res.2.2.1[j]? = some (
    match keyIndexGet oldBuckets mask newKeys[j] with
    | some oi => oldRows.getD oi default
    | none => (fresh ()).getD j default))

private theorem planKeyedLoop_spec {msg : Type} (newKeys : Array String)
    (oldBuckets : Array (List (String × Nat))) (mask : USize)
    (oldRows : Array (Html msg)) (oldMarks : Array USize) (oldSigs : Array (Array (String × String)))
    (fresh : Unit → Array (Html msg)) (oldLen : Nat)
    (hidxBound : ∀ k oi, keyIndexGet oldBuckets mask k = some oi → oi < oldLen) :
    ∀ (i : Nat) (freshCache : Option (Array (Html msg)))
      (sources : Array (Option Nat)) (used : Array Bool)
      (rows : Array (Html msg)) (marks : Array USize) (sigs : Array (Array (String × String))),
      (hle : i ≤ newKeys.size) →
      (∀ arr, freshCache = some arr → arr = fresh ()) →
      (hss : sources.size = i) → (hus : used.size = oldLen) → (hrs : rows.size = i) →
      (∀ j (hj : j < i), sources[j]'(by omega) = keyIndexGet oldBuckets mask (newKeys[j]'(by omega))) →
      (∀ oi (ho : oi < oldLen), used[oi]'(by omega) = true ↔ ∃ j, ∃ _ : j < i, sources[j]'(by omega) = some oi) →
      (∀ j (hj : j < i), rows[j]'(by omega) =
        match keyIndexGet oldBuckets mask (newKeys[j]'(by omega)) with
        | some oi => oldRows.getD oi default
        | none => (fresh ()).getD j default) →
      PlanKeyedOut newKeys oldBuckets mask oldRows fresh oldLen
        (planKeyedLoop newKeys oldBuckets mask oldRows oldMarks oldSigs fresh freshCache i
          sources used rows marks sigs) := by
  intro i
  induction hrem : newKeys.size - i generalizing i with
  | zero =>
      intro freshCache sources used rows marks sigs hle _ hss hus hrs hsrc hused hrows
      have hi : i = newKeys.size := by omega
      subst hi; unfold planKeyedLoop; simp only [Nat.lt_irrefl, ↓reduceDIte, PlanKeyedOut]
      refine ⟨hss, hus, hrs, fun j hj => by simp only [Array.getD, hss, hj, ↓reduceDIte]; exact hsrc j hj,
        fun oi ho => by
          rw [show used.getD oi false = used[oi]'(by omega) by simp [Array.getD, hus, ho], hused oi ho]
          exact ⟨fun ⟨j, hj, hje⟩ => ⟨j, hj, by simpa [Array.getD, hss, hj] using hje⟩,
                 fun ⟨j, hj, hje⟩ => ⟨j, hj, by simpa [Array.getD, hss, hj] using hje⟩⟩,
        fun j hj => by rw [Array.getElem?_eq_getElem (by omega)]; exact congrArg some (hrows j hj)⟩
  | succ r ih =>
      intro freshCache sources used rows marks sigs hle hfc hss hus hrs hsrc hused hrows
      have hlt : i < newKeys.size := by omega
      unfold planKeyedLoop; simp only [hlt, ↓reduceDIte]
      have husedPush : ∀ (v : Option Nat) (oi' : Nat), oi' < oldLen → v ≠ some oi' →
          ((∃ j, ∃ _ : j < i, sources[j]'(by omega) = some oi') ↔
           (∃ j, ∃ _ : j < i + 1, (sources.push v)[j]'(by rw [Array.size_push, hss]; omega) = some oi')) := by
        intro v oi' _ hne; constructor
        · rintro ⟨j, hj, hje⟩; exact ⟨j, Nat.lt_trans hj (Nat.lt_succ_self _), by simp [Array.getElem_push_lt (by omega : j < sources.size), hje]⟩
        · rintro ⟨j, hj, hje⟩
          by_cases hji : j < i
          · exact ⟨j, hji, by simpa [Array.getElem_push_lt (by omega : j < sources.size)] using hje⟩
          · have heq : j = i := by omega
            subst heq
            have hp : (sources.push v)[j]'(by simp [hss]) = v := by simpa [hss] using @Array.getElem_push_eq _ sources v
            rw [hp] at hje; exact absurd hje hne
      let rowFn (j : Nat) (hj : j < newKeys.size) :=
        match keyIndexGet oldBuckets mask (newKeys[j]'hj) with
        | some oi => oldRows.getD oi default
        | none => (fresh ()).getD j default
      cases hq : keyIndexGet oldBuckets mask newKeys[i] with
      | some oi =>
          have hoi : oi < used.size := by rw [hus]; exact hidxBound _ _ hq
          simp only [hoi, ↓reduceDIte]
          apply ih (i + 1) (by omega) freshCache (sources.push (some oi)) (used.set oi true hoi)
            (rows.push (oldRows.getD oi default)) (marks.push (oldMarks.getD oi 0)) (sigs.push (oldSigs.getD oi #[]))
            (by omega) hfc (by simp [hss]) (by simp [hus]) (by simp [hrs])
          · exact array_push_step_inv (f := fun j hj => keyIndexGet oldBuckets mask (newKeys[j]'hj)) hlt hss hsrc hq.symm
          · intro oi' ho'
            by_cases heqO : oi' = oi
            · subst oi'; simp only [Array.getElem_set_self, true_iff]
              exact ⟨i, Nat.lt_succ_self _, by simpa [hss] using @Array.getElem_push_eq _ sources (some oi)⟩
            · simp only [Array.getElem_set_ne (by omega : oi < used.size) (by omega) (Ne.symm heqO), hused oi' ho']
              exact husedPush (some oi) oi' ho' fun h => heqO (Option.some.inj h).symm
          · exact array_push_step_inv (f := rowFn) hlt hrs hrows (by dsimp only [rowFn]; rw [hq])
      | none =>
          have hStep : ∀ (fArr : Array (Html msg)) (fCache' : Option (Array (Html msg))),
              fArr = fresh () → (∀ arr, fCache' = some arr → arr = fresh ()) →
              PlanKeyedOut newKeys oldBuckets mask oldRows fresh oldLen
                (planKeyedLoop newKeys oldBuckets mask oldRows oldMarks oldSigs fresh fCache' (i + 1)
                  (sources.push none) used (rows.push (fArr.getD i default)) (marks.push 0) (sigs.push #[])) := by
            intro fArr fCache' hfArr hfCache'; subst fArr
            apply ih (i + 1) (by omega) fCache' (sources.push none) used
              (rows.push ((fresh ()).getD i default)) (marks.push 0) (sigs.push #[])
              (by omega) hfCache' (by simp [hss]) hus (by simp [hrs])
            · exact array_push_step_inv (f := fun j hj => keyIndexGet oldBuckets mask (newKeys[j]'hj)) hlt hss hsrc hq.symm
            · intro oi' ho'; rw [hused oi' ho']; exact husedPush none oi' ho' (by simp)
            · exact array_push_step_inv (f := rowFn) hlt hrs hrows (by dsimp only [rowFn]; rw [hq])
          cases freshCache with
          | none => exact hStep (fresh ()) (some (fresh ())) rfl (fun _ h => (Option.some.inj h).symm)
          | some fArr => exact hStep fArr (some fArr) (hfc fArr rfl) (fun _ h => (Option.some.inj h) ▸ hfc fArr rfl)

private theorem isValidLisLoop_sound (sources : Array (Option Nat)) (flags : Array Bool) :
    ∀ (i : Nat) (last? : Option Nat),
      isValidLisLoop sources flags i last? = true →
      (∀ j, i ≤ j → j < sources.size → flags.getD j false = true →
        ∃ oi, sources.getD j none = some oi ∧ (∀ p, last? = some p → p < oi)) ∧
      (∀ j₁ j₂, i ≤ j₁ → j₁ < j₂ → j₂ < sources.size →
        flags.getD j₁ false = true → flags.getD j₂ false = true →
        ∀ oi₁ oi₂, sources.getD j₁ none = some oi₁ → sources.getD j₂ none = some oi₂ → oi₁ < oi₂) := by
  intro i
  induction hrem : sources.size - i generalizing i with
  | zero => intro _ _; exact ⟨fun _ _ _ => by omega, fun _ _ _ _ _ => by omega⟩
  | succ r ih =>
      intro last? hv; have hlt : i < sources.size := by omega
      unfold isValidLisLoop at hv; simp only [hlt, ↓reduceDIte] at hv
      by_cases hfi : flags.getD i false = true
      · simp only [hfi, ↓reduceIte] at hv
        cases hs : sources[i] with
        | none => simp [hs] at hv
        | some oi =>
            simp only [hs] at hv
            have hlast : ∀ p, last? = some p → p < oi := fun p hp => by
              subst hp; dsimp only at hv; split at hv <;> first | assumption | simp at hv
            have hv' : isValidLisLoop sources flags (i + 1) (some oi) = true := by
              cases last? with | none => exact hv | some p => simpa [hlast p rfl] using hv
            have ⟨ih1, ih2⟩ := ih (i + 1) (by omega) (some oi) hv'
            refine ⟨fun j hj1 hj2 hfj => ?_, fun j₁ j₂ h1 h2 h3 hf1 hf2 oi₁ oi₂ hs1 hs2 => ?_⟩
            · by_cases hji : j = i
              · subst hji; exact ⟨oi, by simpa [Array.getD, hlt] using hs, hlast⟩
              · rcases ih1 j (by omega) hj2 hfj with ⟨oj, hsoj, hoiLt⟩
                exact ⟨oj, hsoj, fun p hp => Nat.lt_trans (hlast p hp) (hoiLt oi rfl)⟩
            · by_cases hj1i : j₁ = i
              · subst hj1i
                have hoi1 : oi₁ = oi := by simpa [Array.getD, hlt, hs] using hs1.symm
                subst hoi1
                rcases ih1 j₂ (by omega) h3 hf2 with ⟨oj, hsoj, hoiLt⟩
                rw [Option.some.inj (hs2.symm.trans hsoj)]; exact hoiLt oi₁ rfl
              · exact ih2 j₁ j₂ (by omega) h2 h3 hf1 hf2 oi₁ oi₂ hs1 hs2
      · have hfiF : flags.getD i false = false := Bool.eq_false_iff.2 hfi
        simp only [hfiF, Bool.false_eq_true, ↓reduceIte] at hv
        have ⟨ih1, ih2⟩ := ih (i + 1) (by omega) last? hv
        exact ⟨fun j hj1 hj2 hfj => if hji : j = i then by subst hji; simp [hfiF] at hfj else ih1 j (by omega) hj2 hfj,
               fun j₁ j₂ h1 h2 h3 hf1 hf2 => if hj1i : j₁ = i then by subst hj1i; simp [hfiF] at hf1 else ih2 j₁ j₂ (by omega) h2 h3 hf1 hf2⟩

theorem verifiedLisFlags_spec (sources : Array (Option Nat)) :
    let inLis := verifiedLisFlags sources
    (∀ j, j < sources.size → inLis.getD j false = true → ∃ oi, sources.getD j none = some oi) ∧
    (∀ j₁ j₂, j₁ < j₂ → j₂ < sources.size →
      inLis.getD j₁ false = true → inLis.getD j₂ false = true →
      ∀ oi₁ oi₂, sources.getD j₁ none = some oi₁ → sources.getD j₂ none = some oi₂ → oi₁ < oi₂) := by
  dsimp only [verifiedLisFlags]; split
  · rename_i hc; simp only [Bool.and_eq_true] at hc
    have ⟨h1, h2⟩ := isValidLisLoop_sound sources _ 0 none hc.2
    exact ⟨fun j hj hf => let ⟨oi, hoi, _⟩ := h1 j (Nat.zero_le _) hj hf; ⟨oi, hoi⟩,
           fun j₁ j₂ hlt1 hlt2 => h2 j₁ j₂ (Nat.zero_le _) hlt1 hlt2⟩
  · exact ⟨fun j hj hf => by simp [Array.getD, hj] at hf, fun j₁ _ _ _ hf1 => by simp [Array.getD] at hf1⟩

private theorem filter_insertBeforeRef (p : Dom.Node → Bool) (child ref : Dom.Node)
    (hc : p child = true) (hr : p ref = true) :
    ∀ (xs : List Dom.Node),
      (insertBeforeRef child ref xs).filter p = insertBeforeRef child ref (xs.filter p)
  | [] => by simp [insertBeforeRef, hc]
  | x :: xs => by
      simp only [insertBeforeRef, List.filter_cons]
      by_cases hxr : (x == ref) = true
      · have heq : x = ref := eq_of_beq hxr; subst heq
        simp [hr, hc, insertBeforeRef]
      · simp only [hxr, Bool.false_eq_true, ↓reduceIte]
        cases hpx : p x with
        | true => simp [hpx, insertBeforeRef, hxr, filter_insertBeforeRef p child ref hc hr xs]
        | false => simp [hpx, filter_insertBeforeRef p child ref hc hr xs]

private theorem mem_insertBeforeRef_iff {child ref x : Dom.Node} :
    ∀ (xs : List Dom.Node), x ∈ insertBeforeRef child ref xs ↔ x = child ∨ x ∈ xs
  | [] => by simp [insertBeforeRef]
  | a :: xs => by
      simp only [insertBeforeRef]
      by_cases har : (a == ref) = true
      · simp [har, List.mem_cons]
      · simp only [har, Bool.false_eq_true, ↓reduceIte, List.mem_cons, mem_insertBeforeRef_iff xs]
        exact or_left_comm

private theorem nodup_insertBeforeRef {child ref : Dom.Node} :
    ∀ {xs : List Dom.Node}, xs.Nodup → child ∉ xs → (insertBeforeRef child ref xs).Nodup
  | [], _, _ => by simp [insertBeforeRef]
  | a :: xs, hnd, hnot => by
      rcases List.nodup_cons.1 hnd with ⟨ha, hxs⟩
      simp only [insertBeforeRef]
      by_cases har : (a == ref) = true
      · simp only [har, ↓reduceIte]
        exact List.nodup_cons.2 ⟨hnot, List.nodup_cons.2 ⟨ha, hxs⟩⟩
      · simp only [har, Bool.false_eq_true, ↓reduceIte]
        refine List.nodup_cons.2 ⟨?_, nodup_insertBeforeRef hxs (fun hm => hnot (List.mem_cons_of_mem a hm))⟩
        intro hm; rw [mem_insertBeforeRef_iff] at hm
        rcases hm with rfl | hmem
        · exact hnot (List.mem_cons_self ..)
        · exact ha hmem

private theorem erase_filter_of_false {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) (c : α)
    (hpc : p c = false) :
    ∀ {xs : List α}, (xs.erase c).filter p = xs.filter p
  | [] => rfl
  | x :: xs => by
      simp only [List.erase_cons]
      by_cases hxc : (x == c) = true
      · have heq : x = c := eq_of_beq hxc; subst heq
        simp [hpc]
      · simp only [hxc, Bool.false_eq_true, ↓reduceIte, List.filter_cons]
        cases p x <;> simp [erase_filter_of_false p c hpc]

private theorem removeUnusedM_spec {msg : Type} (node : Dom.Node) (ns tag : String)
    (st : SpecElemState msg) (mg : List String) (live : Array Dom.Node) (used : Array Bool) :
    ∀ (i : Nat) (kept : List Dom.Node) (a : DomArena msg),
      i ≤ live.size →
      (kept ++ live.toList.drop i).Nodup →
      a.get node = .element ns tag st mg (kept ++ live.toList.drop i) →
      let aOut := (removeUnusedM (m := StateM (DomArena msg)) node live used i).run a |>.2
      aOut.nextId = a.nextId ∧
      (∀ m, m ≠ node → aOut.get m = a.get m) ∧
      aOut.get node = .element ns tag st mg
        (kept ++ (List.range (live.size - i)).filterMap fun d =>
          if used.getD (i + d) false then some (live.getD (i + d) 0) else none) := by
  intro i
  induction hrem : live.size - i generalizing i with
  | zero =>
      intro kept a hle _ hget
      have hi : i = live.size := by omega
      subst hi; unfold removeUnusedM
      have hdrop : live.toList.drop live.size = [] := List.drop_of_length_le (by simp)
      simp only [Nat.lt_irrefl, ↓reduceDIte, StateT.run, pure, StateT.pure, List.range_zero,
        List.filterMap_nil, List.append_nil]
      rw [hdrop, List.append_nil] at hget
      exact ⟨trivial, fun _ _ => trivial, hget⟩
  | succ r ih =>
      intro kept a hle hnd hget
      have hlt : i < live.size := by omega
      have hdrop : live.toList.drop i = live[i] :: live.toList.drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using hlt)]; rfl
      rw [hdrop] at hnd hget
      have hshift : ((List.range (r + 1)).filterMap fun d =>
          if used.getD (i + d) false then some (live.getD (i + d) 0) else none) =
        (if used.getD i false then [live[i]] else []) ++
        ((List.range r).filterMap fun d =>
          if used.getD (i + 1 + d) false then some (live.getD (i + 1 + d) 0) else none) := by
        rw [List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map, Nat.add_zero]
        have hfn : ((fun d => if used.getD (i + d) false then some (live.getD (i + d) 0) else none) ∘ (· + 1)) =
            (fun d => if used.getD (i + 1 + d) false then some (live.getD (i + 1 + d) 0) else none) := by
          funext d; dsimp only [Function.comp_def]; simp only [Nat.add_comm d 1, Nat.add_assoc]
        rw [hfn]; cases used.getD i false <;> simp [Array.getD, hlt]
      unfold removeUnusedM
      simp only [hlt, ↓reduceDIte]
      by_cases hu : used.getD i false = true
      · simp only [hu, ↓reduceIte]
        have hrec := ih (i + 1) (by omega) (kept ++ [live[i]]) a (by omega)
          (by simpa [List.append_assoc] using hnd) (by simpa [List.append_assoc] using hget)
        exact ⟨hrec.1, hrec.2.1, by rw [hrec.2.2, hshift, hu]; simp [List.append_assoc]⟩
      · have huF : used.getD i false = false := Bool.eq_false_iff.2 hu
        have hndPair := List.nodup_append.1 hnd
        have hnotKept : live[i] ∉ kept := fun hm => hndPair.2.2 live[i] hm live[i] (List.mem_cons_self ..) rfl
        let a1 := a.set node (.element ns tag st mg (kept ++ live.toList.drop (i + 1)))
        have hstep : MonadDom.removeNode (m := StateM (DomArena msg)) node live[i] a = ((), a1) := by
          simp only [MonadDom.removeNode, DomArena.modifyChildren, DomArena.modify, hget,
            erase_append_right_of_not_mem kept (live[i] :: live.toList.drop (i + 1)) hnotKept,
            List.erase_cons_head, a1]
        have hnd' : (kept ++ live.toList.drop (i + 1)).Nodup :=
          List.nodup_append.2 ⟨hndPair.1, (List.nodup_cons.1 hndPair.2.1).2,
            fun x hx y hy => hndPair.2.2 x hx y (List.mem_cons_of_mem _ hy)⟩
        have hrec := ih (i + 1) (by omega) kept a1 (by omega) hnd' (DomArena.get_set_self ..)
        dsimp only [StateT.run] at hrec
        simp only [huF, Bool.false_eq_true, ↓reduceIte, StateT.run, bind]
        rw [stateM_bind_step hstep]
        exact ⟨hrec.1, fun m hm => (hrec.2.1 m hm).trans (DomArena.get_set_ne _ _ hm),
          by rw [hrec.2.2, hshift, huF]; simp⟩

private def filterLisNodes (live : Array Dom.Node) (sources : Array (Option Nat))
    (inLis : Array Bool) (want : Bool) (k : Nat) : List Dom.Node :=
  (List.range k).filterMap fun i =>
    if inLis.getD i false == want then (sources.getD i none).map (live.getD · 0) else none

private theorem range_filterMap_succ {α : Type} (f : Nat → Option α) (k : Nat) :
    (List.range (k + 1)).filterMap f =
      (List.range k).filterMap f ++ (match f k with | some a => [a] | none => []) := by
  rw [List.range_succ, List.filterMap_append]
  cases hf : f k <;> simp [hf]

private theorem filterLisNodes_succ (live : Array Dom.Node) (sources : Array (Option Nat))
    (inLis : Array Bool) (want : Bool) (k : Nat) :
    filterLisNodes live sources inLis want (k + 1) =
      filterLisNodes live sources inLis want k ++
        (if inLis.getD k false == want then
          match sources.getD k none with | some oi => [live.getD oi 0] | none => []
         else []) := by
  unfold filterLisNodes; rw [range_filterMap_succ]
  cases h : (inLis.getD k false == want) with
  | false => simp
  | true => simp only [↓reduceIte]; cases sources.getD k none <;> rfl

private theorem mem_filterLisNodes (live : Array Dom.Node) (sources : Array (Option Nat))
    (inLis : Array Bool) (want : Bool) (k : Nat) (x : Dom.Node) :
    x ∈ filterLisNodes live sources inLis want k ↔
      ∃ i oi, i < k ∧ inLis.getD i false = want ∧ sources.getD i none = some oi ∧ live.getD oi 0 = x := by
  simp only [filterLisNodes, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, hif⟩; simp only [Option.ite_none_right_eq_some, Option.map_eq_some_iff, beq_iff_eq] at hif
    rcases hif with ⟨hfl, oi, hs, hx⟩; exact ⟨i, oi, hi, hfl, hs, hx⟩
  · rintro ⟨i, oi, hi, hfl, hs, rfl⟩; exact ⟨i, hi, by simp [hfl, hs]⟩

private theorem w3cInsertBeforeRef_reconcile_step {cs mov lis placed : List Dom.Node}
    {ref? : Option Dom.Node} {x : Dom.Node}
    (hcsNd : cs.Nodup) (hanc : ref? = placed.head?)
    (hxNotPl : x ∉ placed) (hxNotMov : x ∉ mov)
    (hDisjMP : ∀ y, y ∈ mov → y ∈ placed → False)
    (hDisjLP : ∀ y, y ∈ lis → y ∈ placed → False)
    (hfiltEr : (cs.erase x).filter (fun y => !mov.contains y) = lis ++ placed) :
    let cs' := w3cInsertBeforeRef cs ref? x
    cs'.Nodup ∧ (∀ y, y ∈ cs' ↔ y = x ∨ y ∈ cs.erase x) ∧
    cs'.filter (fun y => !mov.contains y) = lis ++ x :: placed := by
  intro cs'
  have hcsErNd : (cs.erase x).Nodup := List.Nodup.erase x hcsNd
  have hxNotEr : x ∉ cs.erase x := List.Nodup.not_mem_erase hcsNd
  have hrefMemPl : ∀ r, ref? = some r → r ∈ placed := fun r hrf => by
    have h1 : some r = placed.head? := hrf.symm.trans hanc
    cases placed with | nil => cases h1 | cons _ _ => cases h1; exact List.mem_cons_self ..
  have hnotMovB : ∀ y, y ∉ mov → (!mov.contains y) = true := fun y hy => by
    cases hc : mov.contains y with | false => rfl | true => exact absurd (List.contains_iff_mem.1 hc) hy
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [cs', w3cInsertBeforeRef]
    cases hrf : ref? with
    | none => exact List.nodup_append.2 ⟨hcsErNd, List.pairwise_singleton _ _, fun y hy z hz => by simp at hz; subst hz; exact fun he => hxNotEr (he ▸ hy)⟩
    | some r =>
        have hrNe : (r == x) = false := beq_eq_false_iff_ne.2 fun h => hxNotPl (h ▸ hrefMemPl r hrf)
        simp only [hrNe, Bool.false_eq_true, ↓reduceIte]; exact nodup_insertBeforeRef hcsErNd hxNotEr
  · intro y; dsimp only [cs', w3cInsertBeforeRef]
    cases hrf : ref? with
    | none => simp only [List.mem_append, List.mem_singleton]; exact ⟨fun h => h.elim .inr .inl, fun h => h.elim .inr .inl⟩
    | some r =>
        have hrNe : (r == x) = false := beq_eq_false_iff_ne.2 fun h => hxNotPl (h ▸ hrefMemPl r hrf)
        simp only [hrNe, Bool.false_eq_true, ↓reduceIte, mem_insertBeforeRef_iff]
  · dsimp only [cs', w3cInsertBeforeRef]
    cases hpl : placed with
    | nil =>
        rw [hpl] at hanc; dsimp only [List.head?] at hanc; rw [hanc]
        rw [List.filter_append, hfiltEr, hpl, List.append_nil]; simp [hxNotMov]
    | cons r ps =>
        rw [hpl] at hanc; dsimp only [List.head?] at hanc; rw [hanc]
        have hrMemPl : r ∈ placed := by rw [hpl]; exact List.mem_cons_self ..
        have hrNe : (r == x) = false := beq_eq_false_iff_ne.2 fun h => hxNotPl (h ▸ hrMemPl)
        dsimp only; simp only [hrNe, Bool.false_eq_true, ↓reduceIte]
        rw [filter_insertBeforeRef _ x r (hnotMovB x hxNotMov) (hnotMovB r fun hm => hDisjMP r hm hrMemPl), hfiltEr, hpl]
        exact insertBeforeRef_split lis ps fun hm => hDisjLP r hm hrMemPl

private theorem pairwise_lt_ext : ∀ (xs ys : List Nat),
    xs.Pairwise (· < ·) → ys.Pairwise (· < ·) → (∀ a, a ∈ xs ↔ a ∈ ys) → xs = ys
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, hiff => nomatch (hiff y).2 (List.mem_cons_self ..)
  | x :: _, [], _, _, hiff => nomatch (hiff x).1 (List.mem_cons_self ..)
  | x :: xs, y :: ys, hx, hy, hiff => by
      rcases List.pairwise_cons.1 hx with ⟨hxLt, hxs⟩; rcases List.pairwise_cons.1 hy with ⟨hyLt, hys⟩
      have hxy : x = y :=
        (List.mem_cons.1 ((hiff x).1 (List.mem_cons_self ..))).elim id fun hxt =>
          (List.mem_cons.1 ((hiff y).2 (List.mem_cons_self ..))).elim Eq.symm fun hyt =>
            by have := hxLt y hyt; have := hyLt x hxt; omega
      subst hxy; congr 1
      exact pairwise_lt_ext xs ys hxs hys fun a =>
        ⟨fun ha => (List.mem_cons.1 ((hiff a).1 (List.mem_cons_of_mem x ha))).resolve_left (Nat.ne_of_gt (hxLt a ha)),
         fun ha => (List.mem_cons.1 ((hiff a).2 (List.mem_cons_of_mem x ha))).resolve_left (Nat.ne_of_gt (hyLt a ha))⟩

private theorem lis_filter_kept_eq (live : Array Dom.Node) (sources : Array (Option Nat))
    (inLis : Array Bool) (used : Array Bool) (n : Nat)
    (_hsrcSz : sources.size = n) (_husedSz : used.size = live.size)
    (hsrcBound : ∀ i, i < n → ∀ oi, sources.getD i none = some oi → oi < live.size)
    (hsrcInj : ∀ i₁ i₂, i₁ < n → i₂ < n → ∀ oi, sources.getD i₁ none = some oi → sources.getD i₂ none = some oi → i₁ = i₂)
    (husedIff : ∀ oi, oi < live.size → (used.getD oi false = true ↔ ∃ i, ∃ _ : i < n, sources.getD i none = some oi))
    (hliveNd : live.toList.Nodup)
    (_hlisSome : ∀ i, i < n → inLis.getD i false = true → ∃ oi, sources.getD i none = some oi)
    (hlisMono : ∀ i₁ i₂, i₁ < i₂ → i₂ < n → inLis.getD i₁ false = true → inLis.getD i₂ false = true →
      ∀ oi₁ oi₂, sources.getD i₁ none = some oi₁ → sources.getD i₂ none = some oi₂ → oi₁ < oi₂) :
    let kept := (List.range live.size).filterMap fun oi => if used.getD oi false then some (live.getD oi 0) else none
    kept.Nodup ∧
    (∀ x, x ∈ kept ↔ x ∈ filterLisNodes live sources inLis false n ∨ x ∈ filterLisNodes live sources inLis true n) ∧
    (∀ x, x ∈ filterLisNodes live sources inLis false n → x ∈ filterLisNodes live sources inLis true n → False) ∧
    kept.filter (fun x => !(filterLisNodes live sources inLis false n).contains x) = filterLisNodes live sources inLis true n := by
  intro kept
  have hliveInj : ∀ oi₁ oi₂, oi₁ < live.size → oi₂ < live.size → live.getD oi₁ 0 = live.getD oi₂ 0 → oi₁ = oi₂ := fun oi₁ oi₂ h1 h2 heq =>
    nodup_getElem_inj (by simpa using h1) (by simpa using h2) hliveNd (by simpa [Array.getD, h1, h2] using heq)
  have hkeptMem : ∀ x, x ∈ kept ↔ ∃ oi, oi < live.size ∧ used.getD oi false = true ∧ live.getD oi 0 = x := fun x => by
    simp only [kept, List.mem_filterMap, List.mem_range, Option.ite_none_right_eq_some, Option.some.injEq]
  have hdisj : ∀ x, x ∈ filterLisNodes live sources inLis false n → x ∈ filterLisNodes live sources inLis true n → False := by
    intro x hm hl
    rcases (mem_filterLisNodes ..).1 hm with ⟨i₁, oi₁, hi1, hf1, hs1, hx1⟩
    rcases (mem_filterLisNodes ..).1 hl with ⟨i₂, oi₂, hi2, hf2, hs2, hx2⟩
    have hoiEq := hliveInj oi₁ oi₂ (hsrcBound i₁ hi1 oi₁ hs1) (hsrcBound i₂ hi2 oi₂ hs2) (hx1.trans hx2.symm)
    subst hoiEq; have hiEq := hsrcInj i₁ i₂ hi1 hi2 oi₁ hs1 hs2; subst hiEq; simp [hf1] at hf2
  have hkeptNd : kept.Nodup :=
    List.Pairwise.filterMap _ (fun a a' hlt b hb b' hb' heq => by
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hb hb'
      have := hliveInj a a' hlt.1 hlt.2.1 (hb.2.trans (heq.trans hb'.2.symm)); omega)
      (List.pairwise_lt_range.imp_of_mem (S := fun a b => a < live.size ∧ b < live.size ∧ a < b)
        fun ha hb hab => ⟨List.mem_range.1 ha, List.mem_range.1 hb, hab⟩)
  have hkeptIff : ∀ x, x ∈ kept ↔ x ∈ filterLisNodes live sources inLis false n ∨ x ∈ filterLisNodes live sources inLis true n := by
    intro x; rw [hkeptMem, mem_filterLisNodes, mem_filterLisNodes]; constructor
    · rintro ⟨oi, hoi, hu, rfl⟩
      rcases (husedIff oi hoi).1 hu with ⟨i, hi, hs⟩
      cases hfl : inLis.getD i false with | false => exact .inl ⟨i, oi, hi, hfl, hs, rfl⟩ | true => exact .inr ⟨i, oi, hi, hfl, hs, rfl⟩
    · rintro (⟨i, oi, hi, _, hs, rfl⟩ | ⟨i, oi, hi, _, hs, rfl⟩) <;>
        exact ⟨oi, hsrcBound i hi oi hs, (husedIff oi (hsrcBound i hi oi hs)).2 ⟨i, hi, hs⟩, rfl⟩
  have hfiltEq : kept.filter (fun x => !(filterLisNodes live sources inLis false n).contains x) = filterLisNodes live sources inLis true n := by
    let oiKept := (List.range live.size).filter fun oi => used.getD oi false && !(filterLisNodes live sources inLis false n).contains (live.getD oi 0)
    let oiLis := (List.range n).filterMap fun i => if inLis.getD i false then sources.getD i none else none
    have hkm : ∀ l : List Nat, (l.filterMap fun oi => if used.getD oi false then some (live.getD oi 0) else none) =
        (l.filter (used.getD · false)).map (live.getD · 0) := fun l => by
      induction l with | nil => rfl | cons a r ih => simp only [List.filterMap_cons, List.filter_cons, ih]; cases used.getD a false <;> rfl
    have hlhs : kept.filter (fun x => !(filterLisNodes live sources inLis false n).contains x) = oiKept.map (live.getD · 0) := by
      rw [show kept = _ from hkm _, List.filter_map, List.filter_filter]
      exact congrArg (List.map _) (List.filter_congr fun _ _ => Bool.and_comm ..)
    have hrhs : filterLisNodes live sources inLis true n = oiLis.map (live.getD · 0) := by
      unfold filterLisNodes; rw [List.map_filterMap]; congr 1; funext i; cases inLis.getD i false <;> rfl
    rw [hlhs, hrhs]; apply congrArg (List.map (live.getD · 0)); apply pairwise_lt_ext
    · exact List.Pairwise.filter _ List.pairwise_lt_range
    · exact List.Pairwise.filterMap _ (fun i₁ i₂ hlt oi₁ h1 oi₂ h2 => by
        simp only [Option.ite_none_right_eq_some] at h1 h2
        exact hlisMono i₁ i₂ hlt.2.2 hlt.2.1 h1.1 h2.1 oi₁ oi₂ h1.2 h2.2)
        (List.pairwise_lt_range.imp_of_mem (S := fun a b => a < n ∧ b < n ∧ a < b)
          fun ha hb hab => ⟨List.mem_range.1 ha, List.mem_range.1 hb, hab⟩)
    · intro oi
      simp only [oiKept, oiLis, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
        List.mem_filterMap, Option.ite_none_right_eq_some]
      constructor
      · rintro ⟨hoi, hu, hnotM⟩
        rcases (husedIff oi hoi).1 hu with ⟨i, hi, hs⟩
        cases hfl : inLis.getD i false with
        | true => exact ⟨i, hi, hfl, hs⟩
        | false =>
            have hc := List.contains_iff_mem.2 ((mem_filterLisNodes live sources inLis false n _).2 ⟨i, oi, hi, hfl, hs, rfl⟩)
            rw [hc] at hnotM; cases hnotM
      · rintro ⟨i, hi, hfl, hif⟩
        have hoi := hsrcBound i hi oi hif
        refine ⟨hoi, (husedIff oi hoi).2 ⟨i, hi, hif⟩, Bool.eq_false_iff.2 fun hc =>
          hdisj _ (List.contains_iff_mem.1 hc) ((mem_filterLisNodes ..).2 ⟨i, oi, hi, hfl, hif, rfl⟩)⟩
  exact ⟨hkeptNd, hkeptIff, hdisj, hfiltEq⟩

private theorem htmlDomCleanList_mem {msg : Type} :
    ∀ {l : List (Html msg)}, Html.DomCleanList l = true → ∀ h ∈ l, h.DomClean = true
  | [], _, _, h => nomatch h
  | _ :: _, hcl, h, hm => by
      simp only [Html.DomCleanList, Bool.and_eq_true] at hcl
      exact (List.mem_cons.1 hm).elim (· ▸ hcl.1) (htmlDomCleanList_mem hcl.2 h)

private theorem htmlDepth_le_listDepth {msg : Type} :
    ∀ {l : List (Html msg)}, ∀ h ∈ l, htmlDepth h ≤ htmlListDepth l
  | [], _, h => nomatch h
  | _ :: _, h, hm => by
      simp only [htmlListDepth]
      exact (List.mem_cons.1 hm).elim (· ▸ Nat.le_max_left _ _)
        (fun ht => Nat.le_trans (htmlDepth_le_listDepth h ht) (Nat.le_max_right _ _))

private structure LisBackCtx (msg : Type) where
  f' : Nat
  node : Dom.Node
  realNs : String
  tag : String
  st' : SpecElemState msg
  mg' : List String
  childNs : String
  live : Array Dom.Node
  sources : Array (Option Nat)
  inLis : Array Bool
  rowsArr : Array (Html msg)
  newRowsL : List (Html msg)
  oldRowsL : List (Html msg)
  Si : Nat → Nat → Prop
  Sold : Nat → Prop
  baseNext : Nat
  hrowsArrEq : rowsArr.toList = newRowsL
  hliveLen : live.size = oldRowsL.length
  hliveNd : live.toList.Nodup
  hnewClean : Html.DomCleanList newRowsL = true
  hsrcBound : ∀ i, i < newRowsL.length → ∀ oi, sources.getD i none = some oi → oi < oldRowsL.length
  hsrcInj : ∀ i₁ i₂, i₁ < newRowsL.length → i₂ < newRowsL.length → ∀ oi,
    sources.getD i₁ none = some oi → sources.getD i₂ none = some oi → i₁ = i₂
  hsrcRow : ∀ i (hi : i < newRowsL.length) oi (ho : oi < oldRowsL.length),
    sources.getD i none = some oi → oldRowsL[oi] = newRowsL[i]
  hSiSub : ∀ oi k, Si oi k → Sold k ∧ k ≠ node.toNat
  hSiDisj : ∀ oi₁ oi₂, oi₁ ≠ oi₂ → ∀ k, Si oi₁ k → Si oi₂ k → False
  hSoldLt : ∀ k, Sold k → k < baseNext
  hdep : htmlListDepth newRowsL ≤ f'

private abbrev ReconcileBackOut {msg : Type} (ctx : LisBackCtx msg) (k : Nat) (a aOut : DomArena msg) : Prop :=
  a.nextId ≤ aOut.nextId ∧
  aOut.nextId ≤ a.nextId + htmlListNodeCount (ctx.newRowsL.take k) ∧
  (∀ m : Dom.Node, m ≠ ctx.node → m.toNat < a.nextId → aOut.get m = a.get m) ∧
  ∃ finalCs,
    aOut.get ctx.node = .element ctx.realNs ctx.tag ctx.st' ctx.mg' finalCs ∧
    CleanDomChildren ctx.f' ctx.childNs ctx.newRowsL aOut
      (fun m => (ctx.Sold m ∨ (ctx.baseNext ≤ m ∧ m < aOut.nextId)) ∧ m ≠ ctx.node.toNat) finalCs

private structure LisBackInv {msg : Type} (ctx : LisBackCtx msg) (k : Nat) (hasAnchor : Bool)
    (anchor : Dom.Node) (cs placed : List Dom.Node) (Splaced : Nat → Prop) (a : DomArena msg) : Prop where
  hbase : ctx.baseNext ≤ a.nextId
  hpos : 0 < a.nextId
  hbd : a.nextId + htmlListNodeCount (ctx.newRowsL.take k) < UInt32.size
  hnodeLt : ctx.node.toNat < a.nextId
  hget : a.get ctx.node = .element ctx.realNs ctx.tag ctx.st' ctx.mg' cs
  hcsNd : cs.Nodup
  hha : hasAnchor = !placed.isEmpty
  hanc : (if hasAnchor then some anchor else none) = placed.head?
  hcsMem : ∀ x, x ∈ cs ↔ x ∈ filterLisNodes ctx.live ctx.sources ctx.inLis false k ∨ x ∈ filterLisNodes ctx.live ctx.sources ctx.inLis true k ∨ x ∈ placed
  hDisjML : ∀ x, x ∈ filterLisNodes ctx.live ctx.sources ctx.inLis false k → x ∈ filterLisNodes ctx.live ctx.sources ctx.inLis true k → False
  hDisjMP : ∀ x, x ∈ filterLisNodes ctx.live ctx.sources ctx.inLis false k → x ∈ placed → False
  hDisjLP : ∀ x, x ∈ filterLisNodes ctx.live ctx.sources ctx.inLis true k → x ∈ placed → False
  hfilt : cs.filter (fun x => !(filterLisNodes ctx.live ctx.sources ctx.inLis false k).contains x) =
    filterLisNodes ctx.live ctx.sources ctx.inLis true k ++ placed
  hOldClean : ∀ oi (ho : oi < ctx.oldRowsL.length), CleanDomSubtree ctx.f' ctx.childNs ctx.oldRowsL[oi] a (ctx.Si oi) (ctx.live.getD oi 0)
  hSpSub : ∀ m, Splaced m → (ctx.Sold m ∨ (ctx.baseNext ≤ m ∧ m < a.nextId)) ∧ m ≠ ctx.node.toNat
  hSpDisj : ∀ i, i < k → ∀ oi, ctx.sources.getD i none = some oi → ∀ m, ctx.Si oi m → Splaced m → False
  hClPl : CleanDomChildren ctx.f' ctx.childNs (ctx.newRowsL.drop k) a Splaced placed

private abbrev ReconcileBackGoal {msg : Type} (ctx : LisBackCtx msg) (k : Nat) : Prop :=
  k ≤ ctx.newRowsL.length → ∀ hasAnchor anchor cs placed Splaced a,
    LisBackInv ctx k hasAnchor anchor cs placed Splaced a →
    ReconcileBackOut ctx k a ((reconcileLisBackM (m := StateM (DomArena msg)) ctx.node ctx.childNs ctx.live ctx.sources ctx.inLis ctx.rowsArr k hasAnchor anchor).run a).2

private theorem reconcileLisBackM_after_place {msg : Type} {ctx : LisBackCtx msg} {k : Nat}
    {hasAnchor : Bool} {anchor : Dom.Node} {cs placed : List Dom.Node} {Splaced : Nat → Prop} {a : DomArena msg}
    (inv : LisBackInv ctx (k + 1) hasAnchor anchor cs placed Splaced a)
    (ih : ReconcileBackGoal ctx k) (hkLt : k < ctx.newRowsL.length)
    (htakeCnt : htmlListNodeCount (ctx.newRowsL.take (k + 1)) = htmlListNodeCount (ctx.newRowsL.take k) + htmlNodeCount ctx.newRowsL[k])
    (x : Dom.Node) (cs' : List Dom.Node) (Splaced' : Nat → Prop) (aNext : DomArena msg)
    (haGe : a.nextId ≤ aNext.nextId) (haBd : aNext.nextId ≤ a.nextId + htmlNodeCount ctx.newRowsL[k])
    (haFr : ∀ m : Dom.Node, m ≠ ctx.node → m.toNat < a.nextId → aNext.get m = a.get m)
    (hget' : aNext.get ctx.node = .element ctx.realNs ctx.tag ctx.st' ctx.mg' cs') (hcs'Nd : cs'.Nodup)
    (hcs'Mem : ∀ y, y ∈ cs' ↔ y ∈ filterLisNodes ctx.live ctx.sources ctx.inLis false k ∨ y ∈ filterLisNodes ctx.live ctx.sources ctx.inLis true k ∨ y ∈ x :: placed)
    (hxNotF : ∀ w, x ∉ filterLisNodes ctx.live ctx.sources ctx.inLis w k)
    (hcs'Filt : cs'.filter (fun y => !(filterLisNodes ctx.live ctx.sources ctx.inLis false k).contains y) =
      filterLisNodes ctx.live ctx.sources ctx.inLis true k ++ x :: placed)
    (hSpSub' : ∀ m, Splaced' m → (ctx.Sold m ∨ (ctx.baseNext ≤ m ∧ m < aNext.nextId)) ∧ m ≠ ctx.node.toNat)
    (hSpDisj' : ∀ i, i < k → ∀ oi', ctx.sources.getD i none = some oi' → ∀ m, ctx.Si oi' m → Splaced' m → False)
    (hClPl' : CleanDomChildren ctx.f' ctx.childNs (ctx.newRowsL.drop k) aNext Splaced' (x :: placed)) :
    ReconcileBackOut ctx (k + 1) a
      ((reconcileLisBackM (m := StateM (DomArena msg)) ctx.node ctx.childNs ctx.live ctx.sources ctx.inLis ctx.rowsArr k true x).run aNext).2 := by
  have hmono : ∀ w y, y ∈ filterLisNodes ctx.live ctx.sources ctx.inLis w k → y ∈ filterLisNodes ctx.live ctx.sources ctx.inLis w (k + 1) :=
    fun w y hy => by rw [filterLisNodes_succ]; exact List.mem_append_left _ hy
  have hOldClean' : ∀ oi (ho : oi < ctx.oldRowsL.length), CleanDomSubtree ctx.f' ctx.childNs ctx.oldRowsL[oi] aNext (ctx.Si oi) (ctx.live.getD oi 0) :=
    fun oi ho => CleanDomSubtree_frame (fun m hm =>
      have hsub := ctx.hSiSub oi m.toNat hm
      haFr m (node_ne_of_toNat_ne hsub.2) (Nat.lt_of_lt_of_le (ctx.hSoldLt _ hsub.1) inv.hbase)) (inv.hOldClean oi ho)
  have hbdNext : aNext.nextId + htmlListNodeCount (ctx.newRowsL.take k) < UInt32.size :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_right haBd _)
      (by rw [Nat.add_assoc, Nat.add_comm (htmlNodeCount ctx.newRowsL[k]), ← htakeCnt]; exact inv.hbd)
  have hres := ih (Nat.le_of_lt hkLt) true x cs' (x :: placed) Splaced' aNext
    ⟨Nat.le_trans inv.hbase haGe, Nat.lt_of_lt_of_le inv.hpos haGe, hbdNext,
     Nat.lt_of_lt_of_le inv.hnodeLt haGe, hget', hcs'Nd, rfl, rfl, hcs'Mem,
     fun y hm hl => inv.hDisjML y (hmono false y hm) (hmono true y hl),
     fun y hm hp => (List.mem_cons.1 hp).elim (fun h => hxNotF false (h ▸ hm)) (inv.hDisjMP y (hmono false y hm)),
     fun y hl hp => (List.mem_cons.1 hp).elim (fun h => hxNotF true (h ▸ hl)) (inv.hDisjLP y (hmono true y hl)),
     hcs'Filt, hOldClean', hSpSub', hSpDisj', hClPl'⟩
  refine ⟨Nat.le_trans haGe hres.1,
    Nat.le_trans hres.2.1 (by rw [htakeCnt, Nat.add_comm (htmlListNodeCount (ctx.newRowsL.take k)), ← Nat.add_assoc]; exact Nat.add_le_add_right haBd _),
    fun m hmn hmLt => (hres.2.2.1 m hmn (Nat.lt_of_lt_of_le hmLt haGe)).trans (haFr m hmn hmLt),
    hres.2.2.2⟩

private theorem reconcileLisBackM_spec {msg : Type} (ctx : LisBackCtx msg) :
    ∀ (k : Nat), ReconcileBackGoal ctx k := by
  have hliveInj : ∀ oi₁ oi₂, oi₁ < ctx.live.size → oi₂ < ctx.live.size → ctx.live.getD oi₁ 0 = ctx.live.getD oi₂ 0 → oi₁ = oi₂ := fun oi₁ oi₂ h1 h2 heq =>
    nodup_getElem_inj (Array.length_toList ▸ h1) (Array.length_toList ▸ h2) ctx.hliveNd
      (by simp only [Array.getD, h1, h2, ↓reduceDIte] at heq; exact heq)
  intro k
  induction k with
  | zero =>
      intro _ _ _ cs placed Splaced a inv
      rcases inv with ⟨_, _, _, _, hget, _, _, _, _, _, _, _, hfilt, _, hSpSub, _, hClPl⟩
      dsimp only [ReconcileBackOut]
      simp only [reconcileLisBackM, StateT.run, pure, StateT.pure, List.take_zero, htmlListNodeCount,
        Nat.add_zero, List.drop_zero] at hClPl ⊢
      have h0 : ∀ w, filterLisNodes ctx.live ctx.sources ctx.inLis w 0 = [] := fun _ => rfl
      rw [h0 false, h0 true, List.nil_append] at hfilt
      have hcsEq : cs = placed := (List.filter_eq_self.2 (fun _ _ => rfl)).symm.trans hfilt
      subst hcsEq
      exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ _ => trivial, cs, hget,
        CleanDomChildren_mono (fun m hm => hSpSub m hm) hClPl⟩
  | succ k ih =>
      intro hk hasAnchor anchor cs placed Splaced a inv
      have hkLt : k < ctx.newRowsL.length := Nat.lt_of_succ_le hk
      have htakeCnt : htmlListNodeCount (ctx.newRowsL.take (k + 1)) = htmlListNodeCount (ctx.newRowsL.take k) + htmlNodeCount ctx.newRowsL[k] := by
        rw [List.take_succ_eq_append_getElem hkLt, htmlListNodeCount_append]
        simp only [htmlListNodeCount, Nat.add_zero]
      have hdrop : ctx.newRowsL.drop k = ctx.newRowsL[k] :: ctx.newRowsL.drop (k + 1) := List.drop_eq_getElem_cons hkLt
      have hcsMem := inv.hcsMem; have hDisjMP := inv.hDisjMP; have hDisjLP := inv.hDisjLP; have hfilt := inv.hfilt
      dsimp only [reconcileLisBackM, StateT.run, bind, StateT.bind]
      cases hsK : ctx.sources.getD k none with
      | some oi =>
          have hoi : oi < ctx.oldRowsL.length := ctx.hsrcBound k hkLt oi hsK
          let child := ctx.live.getD oi 0
          have hchildClean : CleanDomSubtree ctx.f' ctx.childNs ctx.newRowsL[k] a (ctx.Si oi) child := by
            rw [← ctx.hsrcRow k hkLt oi hoi hsK]; exact inv.hOldClean oi hoi
          have hClPl' : CleanDomChildren ctx.f' ctx.childNs (ctx.newRowsL.drop k) a (fun m => ctx.Si oi m ∨ Splaced m) (child :: placed) := by
            rw [hdrop]; exact ⟨ctx.Si oi, Splaced, fun _ => .inl, fun _ => .inr, inv.hSpDisj k (Nat.lt_succ_self k) oi hsK, hchildClean, inv.hClPl⟩
          have hSpSub' : ∀ m, (ctx.Si oi m ∨ Splaced m) → (ctx.Sold m ∨ (ctx.baseNext ≤ m ∧ m < a.nextId)) ∧ m ≠ ctx.node.toNat := fun m hm =>
            hm.elim (fun h1 => ⟨.inl (ctx.hSiSub oi m h1).1, (ctx.hSiSub oi m h1).2⟩) (inv.hSpSub m)
          have hSpDisj' : ∀ i, i < k → ∀ oi', ctx.sources.getD i none = some oi' → ∀ m, ctx.Si oi' m → (ctx.Si oi m ∨ Splaced m) → False := by
            intro i hi oi' hs' m hm1 hm2
            rcases hm2 with h2 | h2
            · exact ctx.hSiDisj oi' oi (fun he => Nat.ne_of_lt hi (ctx.hsrcInj i k (Nat.lt_trans hi hkLt) hkLt oi' hs' (he ▸ hsK))) m hm1 h2
            · exact inv.hSpDisj i (Nat.lt_succ_of_lt hi) oi' hs' m hm1 h2
          have hchildNotF : ∀ w, child ∉ filterLisNodes ctx.live ctx.sources ctx.inLis w k := fun w hm => by
            rcases (mem_filterLisNodes ..).1 hm with ⟨i, oi', hi, _, hsi, hEq⟩
            have hoiEq := hliveInj oi' oi (ctx.hliveLen ▸ ctx.hsrcBound i (Nat.lt_trans hi hkLt) oi' hsi) (ctx.hliveLen ▸ hoi) hEq
            exact Nat.ne_of_lt hi (ctx.hsrcInj i k (Nat.lt_trans hi hkLt) hkLt oi' hsi (hoiEq ▸ hsK))
          by_cases hflK : ctx.inLis.getD k false = true
          · simp only [hflK, ↓reduceIte]
            have hmovEq : filterLisNodes ctx.live ctx.sources ctx.inLis false (k + 1) = filterLisNodes ctx.live ctx.sources ctx.inLis false k := by
              rw [filterLisNodes_succ, hflK]; simp only [beq_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_nil]
            have hlisEq : filterLisNodes ctx.live ctx.sources ctx.inLis true (k + 1) = filterLisNodes ctx.live ctx.sources ctx.inLis true k ++ [child] := by
              rw [filterLisNodes_succ, hflK, hsK]; simp only [beq_self_eq_true, ↓reduceIte, child]
            rw [hmovEq, hlisEq] at hcsMem hfilt
            have hfilt' : cs.filter (fun x => !(filterLisNodes ctx.live ctx.sources ctx.inLis false k).contains x) =
                filterLisNodes ctx.live ctx.sources ctx.inLis true k ++ child :: placed := by
              rw [List.append_assoc, List.singleton_append] at hfilt; exact hfilt
            exact reconcileLisBackM_after_place inv ih hkLt htakeCnt child cs (fun m => ctx.Si oi m ∨ Splaced m) a
              (Nat.le_refl _) (Nat.le_add_right _ _) (fun _ _ _ => rfl) inv.hget inv.hcsNd
              (fun x => by
                rw [hcsMem x]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc])
              hchildNotF hfilt' hSpSub' hSpDisj' hClPl'
          · have hflKF : ctx.inLis.getD k false = false := Bool.eq_false_iff.2 hflK
            simp only [hflKF, Bool.false_eq_true, ↓reduceIte]
            have hmovEq : filterLisNodes ctx.live ctx.sources ctx.inLis false (k + 1) = filterLisNodes ctx.live ctx.sources ctx.inLis false k ++ [child] := by
              rw [filterLisNodes_succ, hflKF, hsK]; simp only [beq_self_eq_true, ↓reduceIte, child]
            have hlisEq : filterLisNodes ctx.live ctx.sources ctx.inLis true (k + 1) = filterLisNodes ctx.live ctx.sources ctx.inLis true k := by
              rw [filterLisNodes_succ, hflKF]; simp only [beq_true, Bool.false_eq_true, ↓reduceIte, List.append_nil]
            rw [hmovEq] at hcsMem hDisjMP hfilt; rw [hlisEq] at hcsMem hDisjLP hfilt
            let ref? := if hasAnchor then some anchor else none
            let cs' := w3cInsertBeforeRef cs ref? child
            have hstep : MonadDom.insertBeforeRef (m := StateM (DomArena msg)) ctx.node ref? child a =
                ((), a.set ctx.node (.element ctx.realNs ctx.tag ctx.st' ctx.mg' cs')) := by
              simp only [MonadDom.insertBeforeRef, DomArena.modifyChildren, DomArena.modify, inv.hget, cs']
            rw [stateM_bind_step hstep]
            have hchildNotPl : child ∉ placed := fun hp => hDisjMP child (List.mem_append_right _ (List.mem_singleton_self _)) hp
            have hchildNotEr : child ∉ cs.erase child := List.Nodup.not_mem_erase inv.hcsNd
            have hfiltEr : (cs.erase child).filter (fun x => !(filterLisNodes ctx.live ctx.sources ctx.inLis false k).contains x) =
                filterLisNodes ctx.live ctx.sources ctx.inLis true k ++ placed := by
              have hpEq : ∀ x ∈ cs.erase child,
                  (!(filterLisNodes ctx.live ctx.sources ctx.inLis false k).contains x) =
                  (!(filterLisNodes ctx.live ctx.sources ctx.inLis false k ++ [child]).contains x) := fun x hx => by
                have hne : x ≠ child := fun h => hchildNotEr (h ▸ hx)
                simp only [List.contains_append, List.contains_cons, List.contains_nil, Bool.or_false,
                  beq_eq_false_iff_ne.2 hne]
              have hnotC : (!(filterLisNodes ctx.live ctx.sources ctx.inLis false k ++ [child]).contains child) = false := by
                simp only [List.contains_append, List.contains_cons, beq_self_eq_true, Bool.true_or, Bool.or_true, Bool.not_true]
              rw [List.filter_congr hpEq, erase_filter_of_false _ child hnotC, hfilt]
            have ⟨hcs'Nd, hmemC', hcs'Filt⟩ := w3cInsertBeforeRef_reconcile_step inv.hcsNd inv.hanc hchildNotPl
              (hchildNotF false) (fun y hy => hDisjMP y (List.mem_append_left _ hy)) hDisjLP hfiltEr
            have hcs'Mem : ∀ x, x ∈ cs' ↔
                x ∈ filterLisNodes ctx.live ctx.sources ctx.inLis false k ∨
                x ∈ filterLisNodes ctx.live ctx.sources ctx.inLis true k ∨ x ∈ child :: placed := fun x => by
              rw [hmemC']
              by_cases hx : x = child
              · subst hx; simp
              · simp only [hx, false_or, List.mem_erase_of_ne hx, hcsMem x,
                  List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
            let a1 := a.set ctx.node (.element ctx.realNs ctx.tag ctx.st' ctx.mg' cs')
            have hClPl1 : CleanDomChildren ctx.f' ctx.childNs (ctx.newRowsL.drop k) a1 (fun m => ctx.Si oi m ∨ Splaced m) (child :: placed) :=
              CleanDomChildren_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSpSub' m.toNat hm).2)) hClPl'
            exact reconcileLisBackM_after_place inv ih hkLt htakeCnt child cs' (fun m => ctx.Si oi m ∨ Splaced m) a1
              (Nat.le_refl _) (Nat.le_add_right _ _) (fun m hmn _ => DomArena.get_set_ne _ _ hmn)
              (DomArena.get_set_self ..) hcs'Nd hcs'Mem hchildNotF hcs'Filt hSpSub' hSpDisj' hClPl1
      | none =>
          have hStepF : ∀ w, filterLisNodes ctx.live ctx.sources ctx.inLis w (k + 1) = filterLisNodes ctx.live ctx.sources ctx.inLis w k := fun w => by
            rw [filterLisNodes_succ, hsK]; cases (ctx.inLis.getD k false == w) <;> simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
          rw [hStepF false] at hcsMem hDisjMP hfilt; rw [hStepF true] at hcsMem hDisjLP hfilt
          have hrowAtK : ctx.rowsArr.getD k default = ctx.newRowsL[k] := by
            have hkArr : k < ctx.rowsArr.size := by rw [← Array.length_toList, ctx.hrowsArrEq]; exact hkLt
            simp only [Array.getD, hkArr, ↓reduceDIte]
            have h1 := Array.getElem_toList (xs := ctx.rowsArr) (i := k) (h := hkArr)
            exact h1.symm.trans (Option.some.inj (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, ctx.hrowsArrEq]))
          rw [hrowAtK]
          have hrowClean : ctx.newRowsL[k].DomClean = true := htmlDomCleanList_mem ctx.hnewClean ctx.newRowsL[k] (List.getElem_mem hkLt)
          have hrowDep : htmlDepth ctx.newRowsL[k] ≤ ctx.f' := Nat.le_trans (htmlDepth_le_listDepth ctx.newRowsL[k] (List.getElem_mem hkLt)) ctx.hdep
          have hbdRow : a.nextId + htmlNodeCount ctx.newRowsL[k] < UInt32.size :=
            Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left _ _) _) (htakeCnt ▸ inv.hbd)
          have hbm := buildDomM_spec_full ctx.childNs ctx.newRowsL[k] a ctx.f' inv.hpos hbdRow hrowDep
          dsimp only [StateT.run] at hbm
          cases hbr : buildDomM (m := StateM (DomArena msg)) ctx.childNs ctx.newRowsL[k] a with
          | mk cn a1 =>
              rw [hbr] at hbm; dsimp only at hbm
              rcases hbm with ⟨hcnGe, _, ha1Ext, _, _, hbuiltFn⟩
              have hbuilt := hbuiltFn hrowClean
              have ha1Ge : a.nextId ≤ a1.nextId := ha1Ext.next_ge
              have ha1Bd : a1.nextId ≤ a.nextId + htmlNodeCount ctx.newRowsL[k] := ha1Ext.next_le
              have ha1Fr : ∀ m : Dom.Node, m.toNat < a.nextId → a1.get m = a.get m := fun m hm => ha1Ext.frame m hm id
              have hfiltInA : ∀ w x, x ∈ filterLisNodes ctx.live ctx.sources ctx.inLis w k → x.toNat < a.nextId := fun w x hx => by
                rcases (mem_filterLisNodes ..).1 hx with ⟨i, oi', hi, _, hsi, rfl⟩
                have hoi' := ctx.hsrcBound i (Nat.lt_trans hi hkLt) oi' hsi
                exact Nat.lt_of_lt_of_le (ctx.hSoldLt _ (ctx.hSiSub oi' _ (CleanDomSubtree_root_mem (inv.hOldClean oi' hoi'))).1) inv.hbase
              have hcsInA : ∀ x ∈ cs, x.toNat < a.nextId := fun x hx =>
                match (hcsMem x).1 hx with
                | .inl hm => hfiltInA false x hm
                | .inr (.inl hl) => hfiltInA true x hl
                | .inr (.inr hp) => (inv.hSpSub x.toNat (CleanDomChildren_mem inv.hClPl x hp)).1.elim
                    (fun hs => Nat.lt_of_lt_of_le (ctx.hSoldLt _ hs) inv.hbase) (·.2)
              have hcnNotCs : cn ∉ cs := fun hm => Nat.not_lt.2 hcnGe (hcsInA cn hm)
              have hcnNotF : ∀ w, cn ∉ filterLisNodes ctx.live ctx.sources ctx.inLis w k := fun w hm =>
                hcnNotCs ((hcsMem cn).2 (by cases w; exact .inl hm; exact .inr (.inl hm)))
              have hcnNotPl : cn ∉ placed := fun hm => hcnNotCs ((hcsMem cn).2 (.inr (.inr hm)))
              have ha1Node : a1.get ctx.node = .element ctx.realNs ctx.tag ctx.st' ctx.mg' cs := (ha1Fr ctx.node inv.hnodeLt).trans inv.hget
              let ref? := if hasAnchor then some anchor else none
              let cs' := w3cInsertBeforeRef cs ref? cn
              have hins : MonadDom.insertBeforeRef (m := StateM (DomArena msg)) ctx.node ref? cn a1 =
                  ((), a1.set ctx.node (.element ctx.realNs ctx.tag ctx.st' ctx.mg' cs')) := by
                simp only [MonadDom.insertBeforeRef, DomArena.modifyChildren, DomArena.modify, ha1Node, cs']
              dsimp only; rw [stateM_bind_step hbr, stateM_bind_step hins]
              have hcsErEq : cs.erase cn = cs := List.erase_of_not_mem hcnNotCs
              have ⟨hcs'Nd, hmemC', hcs'Filt⟩ := w3cInsertBeforeRef_reconcile_step inv.hcsNd inv.hanc hcnNotPl
                (hcnNotF false) hDisjMP hDisjLP (by rw [hcsErEq]; exact hfilt)
              have hcs'Mem : ∀ x, x ∈ cs' ↔
                  x ∈ filterLisNodes ctx.live ctx.sources ctx.inLis false k ∨
                  x ∈ filterLisNodes ctx.live ctx.sources ctx.inLis true k ∨ x ∈ cn :: placed := fun x => by
                rw [hmemC', hcsErEq, hcsMem x, List.mem_cons, or_left_comm (a := x = cn), or_left_comm (a := x = cn)]
              let a2 := a1.set ctx.node (.element ctx.realNs ctx.tag ctx.st' ctx.mg' cs')
              let Snew : Nat → Prop := fun m => a.nextId ≤ m ∧ m < a1.nextId
              have hSnewDisjPl : ∀ m, Snew m → Splaced m → False := fun m h1 h2 =>
                (inv.hSpSub m h2).1.elim (fun hs => Nat.not_lt.2 h1.1 (Nat.lt_of_lt_of_le (ctx.hSoldLt m hs) inv.hbase))
                  (fun h2 => Nat.not_lt.2 h1.1 h2.2)
              have hcnClean2 : CleanDomSubtree ctx.f' ctx.childNs ctx.newRowsL[k] a2 Snew cn :=
                CleanDomSubtree_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (fun hEq => Nat.not_lt.2 hm.1 (hEq ▸ inv.hnodeLt)))) hbuilt
              have hClPl2 : CleanDomChildren ctx.f' ctx.childNs (ctx.newRowsL.drop (k + 1)) a2 Splaced placed :=
                CleanDomChildren_frame (fun m hm => by
                  have hsp := inv.hSpSub m.toNat hm
                  rw [DomArena.get_set_ne _ _ (node_ne_of_toNat_ne hsp.2)]
                  exact ha1Fr m (hsp.1.elim (fun hs => Nat.lt_of_lt_of_le (ctx.hSoldLt _ hs) inv.hbase) (·.2))) inv.hClPl
              have hClPl' : CleanDomChildren ctx.f' ctx.childNs (ctx.newRowsL.drop k) a2 (fun m => Snew m ∨ Splaced m) (cn :: placed) := by
                rw [hdrop]; exact ⟨Snew, Splaced, fun _ => .inl, fun _ => .inr, hSnewDisjPl, hcnClean2, hClPl2⟩
              have hSpSub' : ∀ m, (Snew m ∨ Splaced m) → (ctx.Sold m ∨ (ctx.baseNext ≤ m ∧ m < a2.nextId)) ∧ m ≠ ctx.node.toNat := fun m hm =>
                hm.elim (fun ⟨h1, h2⟩ => ⟨.inr ⟨Nat.le_trans inv.hbase h1, h2⟩, fun hEq => Nat.not_lt.2 h1 (hEq ▸ inv.hnodeLt)⟩)
                  (fun h2 => let ⟨h, hne⟩ := inv.hSpSub m h2; ⟨h.elim .inl (fun ⟨hb, hl⟩ => .inr ⟨hb, Nat.lt_of_lt_of_le hl ha1Ge⟩), hne⟩)
              have hSpDisj' : ∀ i, i < k → ∀ oi', ctx.sources.getD i none = some oi' → ∀ m, ctx.Si oi' m → (Snew m ∨ Splaced m) → False :=
                fun i hi oi' hs' m hm1 hm2 => hm2.elim (fun h1 => Nat.not_lt.2 h1.1 (Nat.lt_of_lt_of_le (ctx.hSoldLt m (ctx.hSiSub oi' m hm1).1) inv.hbase))
                  (inv.hSpDisj i (Nat.lt_succ_of_lt hi) oi' hs' m hm1)
              exact reconcileLisBackM_after_place inv ih hkLt htakeCnt cn cs' (fun m => Snew m ∨ Splaced m) a2
                ha1Ge ha1Bd (fun m hmn hmLt => (DomArena.get_set_ne _ _ hmn).trans (ha1Fr m hmLt))
                (DomArena.get_set_self ..) hcs'Nd hcs'Mem hcnNotF hcs'Filt hSpSub' hSpDisj' hClPl'

private theorem appendFragmentRowsM_spec {msg : Type} (f' : Nat) (childNs : String)
    (node : Dom.Node) (realNs tag : String) (st' : SpecElemState msg) (mg' : List String)
    (rows : List (Html msg)) (Sold : Nat → Prop) (a aBase : DomArena msg)
    (hrowsClean : Html.DomCleanList rows = true)
    (hbound : a.nextId + (1 + htmlListNodeCount rows) < UInt32.size)
    (hdep : htmlListDepth rows ≤ f') (hpos : 0 < a.nextId) (hnodeLt : node.toNat < a.nextId)
    (haBaseN : aBase.nextId = a.nextId) (haBaseNode : aBase.get node = .element realNs tag st' mg' [])
    (haBaseOut : ∀ m, m ≠ node → aBase.get m = a.get m) :
    ∃ aOut csNew,
      (∀ {α} (k : StateM (DomArena msg) α),
        (do let frag ← MonadDom.createFragment; buildDomListM (Dom.childNsOf childNs tag) frag rows
            MonadDom.appendChild node frag; k) aBase = k aOut) ∧
      a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + (1 + htmlListNodeCount rows) ∧
      (∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      aOut.get node = .element realNs tag st' mg' csNew ∧
      CleanDomChildren f' (Dom.childNsOf childNs tag) rows aOut
        (fun k => (Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ node.toNat) csNew := by
  let frag := UInt32.ofNat aBase.nextId
  let aFragBase : DomArena msg := { aBase with nextId := aBase.nextId + 1 }
  have haFragNext : aFragBase.nextId = a.nextId + 1 := by dsimp only [aFragBase]; rw [haBaseN]
  have hfragToNat : frag.toNat = a.nextId := by dsimp only [frag]; rw [haBaseN]; exact uint32_toNat_ofNat_lt a.nextId (by omega)
  have hfragNeNode : frag ≠ node := node_ne_of_toNat_ne (by rw [hfragToNat]; omega)
  have hfragRun : MonadDom.createFragment (m := StateM (DomArena msg)) aBase = (frag, aFragBase.set frag (.fragment [])) := rfl
  have hbuilt := buildDomListM_spec_full (Dom.childNsOf childNs tag) rows aFragBase frag
    ArenaEntry.fragment (.inr fun _ => rfl) [] f' (by omega) (by omega) (by omega) hdep (fun _ h => nomatch h)
  rcases hbuilt with ⟨csNew, aBase', haBuiltEq, haBuiltExt, _, _, hCleanFn⟩
  have hCleanOut := hCleanFn [] (fun _ => False) hrowsClean (fun _ h => h.elim) trivial
  simp only [List.nil_append, false_or] at haBuiltEq hCleanOut
  let aBuilt := (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf childNs tag) frag rows (aFragBase.set frag (.fragment []))).2
  have haBuiltGe : a.nextId + 1 ≤ aBuilt.nextId := haFragNext ▸ haBuiltExt.next_ge
  have haBuiltBd : aBuilt.nextId ≤ a.nextId + (1 + htmlListNodeCount rows) := by have := haBuiltExt.next_le; dsimp only [aBuilt, StateT.run] at *; omega
  have haBuiltFr : ∀ m : Dom.Node, m.toNat < a.nextId + 1 → m ≠ frag → aBuilt.get m = aFragBase.get m := fun m hm hne =>
    haBuiltExt.frame m (haFragNext.symm ▸ hm) (fun h => hne (uint32_eq_of_toNat_eq h))
  have haBuiltFrag : aBuilt.get frag = .fragment csNew := by rw [show aBuilt = aBase'.set frag (.fragment csNew) from haBuiltEq, DomArena.get_set_self]
  have haBuiltNode : aBuilt.get node = .element realNs tag st' mg' [] := (haBuiltFr node (by omega) hfragNeNode.symm).trans haBaseNode
  let aOut := (aBuilt.set frag .null).set node (.element realNs tag st' mg' csNew)
  have haOutN : aOut.nextId = aBuilt.nextId := rfl
  have happendRun : MonadDom.appendChild (m := StateM (DomArena msg)) node frag aBuilt = ((), aOut) := by
    simp only [MonadDom.appendChild, haBuiltFrag, DomArena.modifyChildren, DomArena.modify,
      DomArena.get_set_ne _ _ hfragNeNode.symm, haBuiltNode, List.filter_nil, List.nil_append, aOut]
  have hbuiltRun : buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf childNs tag) frag rows (aFragBase.set frag (.fragment [])) = ((), aBuilt) := rfl
  refine ⟨aOut, csNew, fun k => by dsimp only [bind]; rw [stateM_bind_step hfragRun, stateM_bind_step hbuiltRun, stateM_bind_step happendRun],
    by omega, by omega, fun m hmn hmLt => ?_, DomArena.get_set_self _ _ _, ?_⟩
  · have hmf : m ≠ frag := node_ne_of_toNat_ne (by rw [hfragToNat]; omega)
    dsimp only [aOut]; rw [DomArena.get_set_ne _ _ hmn, DomArena.get_set_ne _ _ hmf, haBuiltFr m (by omega) hmf]; exact haBaseOut m hmn
  · refine CleanDomChildren_mono (fun k ⟨hk1, hk2⟩ => ⟨.inr ⟨by omega, hk2⟩, by omega⟩)
      (CleanDomChildren_frame (a' := aOut) (fun m ⟨hm1, _⟩ => by
        have hmn : m ≠ node := node_ne_of_toNat_ne (by omega)
        have hmf : m ≠ frag := node_ne_of_toNat_ne (by rw [hfragToNat]; omega)
        simp only [aOut, DomArena.get_set_ne _ _ hmn, DomArena.get_set_ne _ _ hmf]; rfl) hCleanOut)

section
variable {σ msg : Type} {f' : Nat} {childNs pns ptag tag inst : String}
  {parent node : Dom.Node} {pst : SpecElemState msg} {pmg : List String}
  {attrs : List (VAttr σ msg)} {keys : σ → Array String} {marks : σ → Array USize}
  {rowSig : σ → Array String → Nat → Array (String × String)}
  {rowEv : σ → Array String → Nat → Array (String × msg)} {rowsHtml : σ → List (Html msg)}
  {s₁ s₂ : σ} {pre suf : List Dom.Node} {Sold : Nat → Prop} {a : DomArena msg}
  {st : SpecElemState msg} {mg : List String} {domCs : List Dom.Node}

private theorem keyedList_finish_goal {st' : SpecElemState msg} {mg' : List String}
    {csNew : List Dom.Node} {aOut : DomArena msg}
    {outKeys : Array String} {outSigs : Array (Array (String × String))}
    {outRows : List (Html msg)} {outMarks : Array USize}
    (haClean : VAttrListClean attrs) (hparLt : parent.toNat < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ node :: suf))
    (hnd : (pre ++ node :: suf).Nodup) (hparOut : ¬Sold parent.toNat)
    (hparNodes : ∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId) (hnodeMem : Sold node.toNat)
    (haOutGe : a.nextId ≤ aOut.nextId) (haOutBd : aOut.nextId ≤ a.nextId + (1 + htmlListNodeCount (rowsHtml s₂)))
    (haOutFr : ∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aOut.get m = a.get m)
    (haOutNode : aOut.get node = .element (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st' mg' csNew)
    (hElClean' : ElemClean st' mg') (hElEq' : ElemStateEquiv st' (evalSpecAttrs (attrs.map (VAttr.eval s₂))))
    (hmg' : ∀ nm ∈ (normalizeAttrs (attrs.map (VAttr.eval s₂))).filterMap managedAttrName, mg'.contains nm = true)
    (hCleanOut : CleanDomChildren f' (Dom.childNsOf childNs tag) (rowsHtml s₂) aOut
      (fun k => (Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ node.toNat) csNew)
    (hkeysEq : outKeys = disambiguateKeys (keys s₂)) (hrowsEq : outRows = rowsHtml s₂) :
    PatchViewPost (f' + 1) childNs parent pns ptag pst pmg
      (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ pre suf Sold a
      (.list node outKeys outSigs outRows outMarks inst, aOut) := by
  have hvalOut : VStateValid (f' + 1) childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ aOut
      (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) (.list node outKeys outSigs outRows outMarks inst) :=
    ⟨⟨.inl hnodeMem, haClean.1 s₂, haClean.2.1 s₂, st', mg', csNew, haOutNode, hElClean', hElEq', hmg', hCleanOut⟩,
     rfl, hkeysEq, hrowsEq⟩
  exact ⟨haOutGe, by simp only [View.render, htmlNodeCount]; exact haOutBd,
    fun m _ hmSold hmLt => haOutFr m (fun h => hmSold (h ▸ hnodeMem)) hmLt,
    by rw [haOutFr parent (fun h => hparOut (h ▸ hnodeMem)) hparLt, hpar]; rfl, hnd,
    fun r hr => Nat.lt_of_lt_of_le (hparNodes r hr) haOutGe, hvalOut, VStateValid_equiv hvalOut⟩

private theorem keyedList_appendFrag_finish {st' : SpecElemState msg} {mg' : List String} {aBase : DomArena msg}
    {outSigs : Array (Array (String × String))} {outMarks : Array USize}
    (haClean : VAttrListClean attrs) (hrowsClean : KeyedRowsClean keys rowsHtml)
    (hbound : a.nextId + htmlNodeCount (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂) < UInt32.size)
    (hdep : htmlDepth (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂) ≤ f' + 1)
    (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ node :: suf))
    (hnd : (pre ++ node :: suf).Nodup) (hparOut : ¬Sold parent.toNat)
    (hSoldLt : ∀ k, Sold k → k < a.nextId) (hparNodes : ∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId)
    (hnodeMem : Sold node.toNat)
    (haBaseN : aBase.nextId = a.nextId)
    (haBaseNode : aBase.get node = .element (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st' mg' [])
    (haBaseOut : ∀ m, m ≠ node → aBase.get m = a.get m)
    (hElClean' : ElemClean st' mg') (hElEq' : ElemStateEquiv st' (evalSpecAttrs (attrs.map (VAttr.eval s₂))))
    (hmg' : ∀ nm ∈ (normalizeAttrs (attrs.map (VAttr.eval s₂))).filterMap managedAttrName, mg'.contains nm = true) :
    PatchViewPost (f' + 1) childNs parent pns ptag pst pmg
      (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ pre suf Sold a
      ((do let frag ← MonadDom.createFragment (m := StateM (DomArena msg))
           buildDomListM (Dom.childNsOf childNs tag) frag (rowsHtml s₂)
           MonadDom.appendChild node frag
           pure (VState.list node (disambiguateKeys (keys s₂)) outSigs (rowsHtml s₂) outMarks inst)) aBase) := by
  simp only [View.render, htmlNodeCount] at hbound; simp only [View.render, htmlDepth] at hdep
  rcases appendFragmentRowsM_spec f' childNs node (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st' mg'
    (rowsHtml s₂) Sold a aBase (hrowsClean.2.1 s₂) hbound (by omega) hpos (hSoldLt _ hnodeMem) haBaseN haBaseNode haBaseOut with
    ⟨aOut, _, hrun, haOutGe, haOutBd, haOutFr, haOutNode, hCleanOut'⟩
  rw [hrun]
  exact keyedList_finish_goal haClean hparLt hpar hnd hparOut hparNodes hnodeMem
    haOutGe haOutBd haOutFr haOutNode hElClean' hElEq' hmg' hCleanOut' rfl rfl

private theorem patchViewM_keyedList_lis_spec {oldSigs : Array (Array (String × String))} {oldMarks : Array USize}
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (haClean : VAttrListClean attrs) (hrowsClean : KeyedRowsClean keys rowsHtml)
    (hbound : a.nextId + htmlNodeCount (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂) < UInt32.size)
    (hdep : htmlDepth (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂) ≤ f' + 1)
    (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ node :: suf))
    (hnd : (pre ++ node :: suf).Nodup) (hparOut : ¬Sold parent.toNat)
    (hSoldLt : ∀ k, Sold k → k < a.nextId) (hparNodes : ∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId)
    (hnodeMem : Sold node.toNat)
    (hnodeGet : a.get node = .element (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st mg domCs)
    (hElClean : ElemClean st mg) (hElEq : ElemStateEquiv st (evalSpecAttrs (attrs.map (VAttr.eval s₁))))
    (hmg : ∀ nm ∈ (normalizeAttrs (attrs.map (VAttr.eval s₁))).filterMap managedAttrName, mg.contains nm = true)
    (hCleanCs : CleanDomChildren f' (Dom.childNsOf childNs tag) (rowsHtml s₁) a (fun k => Sold k ∧ k ≠ node.toNat) domCs)
    (hrawNe : keys s₂ ≠ disambiguateKeys (keys s₁))
    (hsameNe : disambiguateKeys (keys s₂) ≠ disambiguateKeys (keys s₁))
    (hnewEmp : (disambiguateKeys (keys s₂)).isEmpty = false)
    (hemp : (rowsHtml s₁).isEmpty = false) :
    PatchViewPost (f' + 1) childNs parent pns ptag pst pmg
      (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ pre suf Sold a
      ((patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
        (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂
        (.list node (disambiguateKeys (keys s₁)) oldSigs (rowsHtml s₁) oldMarks inst)).run a) := by
  have hnodeLt : node.toNat < a.nextId := hSoldLt _ hnodeMem
  let realNs := if childNs == "" && tag == "svg" then Dom.svgNs else childNs
  dsimp only [patchViewM, StateT.run, bind, pure]
  simp only [beq_eq_false_iff_ne.2 hrawNe, beq_eq_false_iff_ne.2 hsameNe, hnewEmp, hemp, Bool.false_eq_true, ↓reduceIte]
  let oldKeys := disambiguateKeys (keys s₁); let newKeys := disambiguateKeys (keys s₂)
  have hidxSpec := buildKeyIndex_spec oldKeys (disambiguateKeys_nodup (keys s₁))
  let oldBuckets := (buildKeyIndex oldKeys).1; let mask := (buildKeyIndex oldKeys).2
  have hidxBnd : ∀ k oi, keyIndexGet oldBuckets mask k = some oi → oi < oldKeys.size := fun k oi hq => (hidxSpec.1 k oi hq).1
  let freshFn : Unit → Array (Html msg) := fun _ => ((rowsHtml s₂).map (Html.prefixSignals inst)).toArray
  let plan := planKeyedLoop newKeys oldBuckets mask (rowsHtml s₁).toArray oldMarks oldSigs freshFn none 0
    (Array.emptyWithCapacity newKeys.size) (Array.replicate oldKeys.size false)
    (Array.emptyWithCapacity newKeys.size) (Array.emptyWithCapacity newKeys.size) (Array.emptyWithCapacity newKeys.size)
  have hplanSpec := planKeyedLoop_spec newKeys oldBuckets mask (rowsHtml s₁).toArray oldMarks oldSigs freshFn oldKeys.size hidxBnd
    0 none (Array.emptyWithCapacity newKeys.size) (Array.replicate oldKeys.size false)
    (Array.emptyWithCapacity newKeys.size) (Array.emptyWithCapacity newKeys.size) (Array.emptyWithCapacity newKeys.size)
    (Nat.zero_le _) (fun _ h => nomatch h) rfl (Array.size_replicate ..) rfl
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
    (fun oi ho => ⟨(fun h => by rw [Array.getElem_replicate] at h; cases h), (fun ⟨_, hj, _⟩ => absurd hj (Nat.not_lt_zero _))⟩)
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
  let sources := plan.1; let used := plan.2.1; let rowsArr := plan.2.2.1; let marksArr := plan.2.2.2.1; let sigsArr := plan.2.2.2.2
  have hsrcSz : sources.size = (rowsHtml s₂).length := by rw [hplanSpec.1, hrowsClean.1 s₂]
  have hsrcGet := hplanSpec.2.2.2.1
  have hsrcBound : ∀ i, i < (rowsHtml s₂).length → ∀ oi, sources.getD i none = some oi → oi < (rowsHtml s₁).length := fun i hi oi hsi => by
    rw [hsrcGet i ((hrowsClean.1 s₂) ▸ hi)] at hsi; rw [hrowsClean.1 s₁]; exact hidxBnd _ oi hsi
  have hsrcInj : ∀ i₁ i₂, i₁ < (rowsHtml s₂).length → i₂ < (rowsHtml s₂).length →
      ∀ oi, sources.getD i₁ none = some oi → sources.getD i₂ none = some oi → i₁ = i₂ := fun i₁ i₂ h1 h2 oi hs1 hs2 => by
    have h1K : i₁ < newKeys.size := (hrowsClean.1 s₂) ▸ h1; have h2K : i₂ < newKeys.size := (hrowsClean.1 s₂) ▸ h2
    rw [hsrcGet i₁ h1K] at hs1; rw [hsrcGet i₂ h2K] at hs2
    exact nodup_getElem_inj (Array.length_toList ▸ h1K) (Array.length_toList ▸ h2K) (disambiguateKeys_nodup (keys s₂))
      (Option.some.inj ((hidxSpec.1 _ oi hs1).2.symm.trans (hidxSpec.1 _ oi hs2).2))
  have hsrcRow : ∀ i (hi : i < (rowsHtml s₂).length) oi (ho : oi < (rowsHtml s₁).length),
      sources.getD i none = some oi → (rowsHtml s₁)[oi] = (rowsHtml s₂)[i] := fun i hi oi ho hsi => by
    have hiK : i < newKeys.size := (hrowsClean.1 s₂) ▸ hi; have hoK : oi < oldKeys.size := (hrowsClean.1 s₁) ▸ ho
    rw [hsrcGet i hiK] at hsi
    have hkeyEq : oldKeys[oi]'hoK = newKeys[i]'hiK := by have h := (hidxSpec.1 _ oi hsi).2; rw [Array.getElem?_eq_getElem hoK, Option.some.injEq] at h; exact h
    have hrowEq := hrowsClean.2.2.2 s₁ s₂ oi i hoK hiK hkeyEq
    rw [List.getElem?_eq_getElem ho, List.getElem?_eq_getElem hi, Option.some.injEq] at hrowEq; exact hrowEq
  have hrowsArrEq : rowsArr.toList = rowsHtml s₂ := by
    have hpref := Html.map_prefixSignals_of_DomCleanList inst (hrowsClean.2.1 s₂)
    refine List.ext_getElem? fun i => ?_; rw [Array.getElem?_toList]
    by_cases hi : i < newKeys.size
    · have hri : i < (rowsHtml s₂).length := (hrowsClean.1 s₂) ▸ hi
      rw [hplanSpec.2.2.2.2.2 i hi]
      cases hq : keyIndexGet oldBuckets mask newKeys[i] with
      | none => simp only [freshFn, hpref, Array.getD, List.size_toArray, hri, ↓reduceDIte, List.getElem?_eq_getElem hri]; rfl
      | some oi =>
          have hsi : sources.getD i none = some oi := (hsrcGet i hi).trans hq
          have hoi1 := hsrcBound i hri oi hsi
          simp only [Array.getD, List.size_toArray, hoi1, ↓reduceDIte, List.getElem?_eq_getElem hri]
          exact congrArg some (hsrcRow i hri oi hoi1 hsi)
    · rw [Array.getElem?_eq_none (hplanSpec.2.2.1.symm ▸ Nat.not_lt.1 hi),
          List.getElem?_eq_none ((hrowsClean.1 s₂).symm ▸ Nat.not_lt.1 hi)]
  have hseed0 := seedRowsM_sameDom inst (rowSig s₂ newKeys) (rowEv s₂ newKeys) (marks s₂) marksArr sigsArr a
  dsimp only [StateT.run] at hseed0
  cases hsRun : seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ newKeys) (rowEv s₂ newKeys) (marks s₂) marksArr sigsArr a with
  | mk newSigs aSeed =>
      rw [hsRun] at hseed0; rw [stateM_bind_step hsRun]; dsimp only at hseed0 ⊢
      have hdyn := applyDynAttrsM_spec aSeed node realNs tag st mg domCs attrs s₁ s₂ haClean hElClean hElEq hmg
      rw [DomArena.set_get_self aSeed ((hseed0.get_eq node).trans hnodeGet)] at hdyn
      rcases hdyn with ⟨ha1Next, ha1Ne, st', mg', ha1Get, hElClean', hElEq', hmg'⟩
      let a1 := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ aSeed).2
      have ha1N : a1.nextId = a.nextId := ha1Next.trans hseed0.1
      have ha1Out : ∀ m, m ≠ node → a1.get m = a.get m := fun m hm => (ha1Ne m hm).trans (hseed0.get_eq m)
      have hccNs := childNamespace_eq_childNsOf (ptag := tag) (show childNs = "" ∨ childNs = Dom.svgNs by rw [hchildNs]; split <;> simp)
      have hcnRun : MonadDom.childNamespace (m := StateM (DomArena msg)) node a1 = (Dom.childNsOf childNs tag, a1) := by
        dsimp only [MonadDom.childNamespace]; rw [ha1Get]; exact congrArg (·, a1) hccNs
      rw [stateM_bind_step (show applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ aSeed = ((), a1) from rfl),
          stateM_bind_step hcnRun]
      split
      · let aClr := a1.set node (.element realNs tag st' mg' [])
        have hclr : MonadDom.clearChildren (m := StateM (DomArena msg)) node a1 = ((), aClr) := by
          dsimp only [MonadDom.clearChildren, DomArena.modifyChildren, DomArena.modify, aClr]; rw [ha1Get]
        rw [stateM_bind_step hclr, hrowsArrEq]
        exact keyedList_appendFrag_finish haClean hrowsClean hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hnodeMem
          ha1N (DomArena.get_set_self ..) (fun m hm => (DomArena.get_set_ne _ _ hm).trans (ha1Out m hm)) hElClean' hElEq' hmg'
      · have ⟨hdomNd, hdomLen⟩ := CleanDomChildren_nodup hCleanCs
        have hdomLtU32 : domCs.length < UInt32.size :=
          Nat.lt_of_le_of_lt (nodup_nodes_lt_length_le a.nextId domCs hdomNd fun x hx =>
            hSoldLt _ (CleanDomChildren_mem hCleanCs x hx).1) (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hbound)
        have hsnap := snapshotChildrenM_spec a1 node realNs tag st' mg' domCs hdomLtU32 0 domCs.length #[] (Nat.zero_add _)
        rw [DomArena.set_get_self a1 ha1Get] at hsnap
        dsimp only [StateT.run, List.nil_append, List.drop_zero] at hsnap
        let live : Array Dom.Node := ⟨domCs⟩
        have hliveSz : live.size = (rowsHtml s₁).length := hdomLen
        have hremSpec := removeUnusedM_spec node realNs tag st' mg' live used 0 [] a1 (Nat.zero_le _) hdomNd ha1Get
        let aRem := (removeUnusedM (m := StateM (DomArena msg)) node live used 0).run a1 |>.2
        have haRemN : aRem.nextId = a.nextId := hremSpec.1.trans ha1N
        have haRemOut : ∀ m, m ≠ node → aRem.get m = a.get m := fun m hm => (hremSpec.2.1 m hm).trans (ha1Out m hm)
        let kept := (List.range live.size).filterMap fun oi => if used.getD oi false then some (live.getD oi 0) else none
        have haRemNode : aRem.get node = .element realNs tag st' mg' kept := by
          simpa only [List.nil_append, Nat.zero_add, Nat.sub_zero] using hremSpec.2.2
        let inLis := verifiedLisFlags sources
        have hlisSpec := verifiedLisFlags_spec sources
        have hkeptSpec := lis_filter_kept_eq live sources inLis used (rowsHtml s₂).length hsrcSz
          (by rw [hplanSpec.2.1, hliveSz, hrowsClean.1 s₁])
          (fun i hi oi hsi => hliveSz.symm ▸ hsrcBound i hi oi hsi) hsrcInj
          (fun oi ho => by rw [hrowsClean.1 s₂]; exact hplanSpec.2.2.2.2.1 oi ((hrowsClean.1 s₁) ▸ hliveSz ▸ ho))
          hdomNd (fun i hi hf => hlisSpec.1 i (hsrcSz.symm ▸ hi) hf)
          (fun i₁ i₂ h1 h2 hf1 hf2 oi₁ oi₂ hs1 hs2 => hlisSpec.2 i₁ i₂ h1 (hsrcSz.symm ▸ h2) hf1 hf2 oi₁ oi₂ hs1 hs2)
        rcases CleanDomChildren_indexed hCleanCs with ⟨Si, hSiSub, hSiDisj, hSiGet⟩
        have hOldCleanRem : ∀ oi (ho : oi < (rowsHtml s₁).length),
            CleanDomSubtree f' (Dom.childNsOf childNs tag) (rowsHtml s₁)[oi] aRem (Si oi) (live.getD oi 0) := fun oi ho => by
          have hoD : oi < domCs.length := hdomLen ▸ ho
          rw [show live.getD oi 0 = domCs[oi] by rw [Array.getD, dif_pos (show oi < live.size from hoD)]; rfl]
          exact CleanDomSubtree_frame (fun m hm => haRemOut m (node_ne_of_toNat_ne (hSiSub oi m.toNat hm).2)) (hSiGet oi ho hoD)
        simp only [View.render, htmlNodeCount] at hbound; simp only [View.render, htmlDepth] at hdep
        have hbdRem : aRem.nextId + htmlListNodeCount ((rowsHtml s₂).take (rowsHtml s₂).length) < UInt32.size := by
          rw [haRemN, List.take_length]; omega
        have hrec := reconcileLisBackM_spec ⟨f', node, realNs, tag, st', mg', Dom.childNsOf childNs tag,
          live, sources, inLis, rowsArr, rowsHtml s₂, rowsHtml s₁, Si, Sold, a.nextId,
          hrowsArrEq, hliveSz, hdomNd, hrowsClean.2.1 s₂, hsrcBound, hsrcInj, hsrcRow,
          hSiSub, hSiDisj, hSoldLt, by omega⟩
          (rowsHtml s₂).length (Nat.le_refl _) false 0 kept [] (fun _ => False) aRem
          ⟨by dsimp only; omega, by omega, hbdRem, by dsimp only; omega, haRemNode, hkeptSpec.1, rfl, rfl,
           fun x => by rw [hkeptSpec.2.1 x]; simp only [List.not_mem_nil, or_false],
           hkeptSpec.2.2.1, (fun _ _ h => nomatch h), (fun _ _ h => nomatch h),
           by rw [List.append_nil]; exact hkeptSpec.2.2.2, hOldCleanRem,
           (fun _ h => h.elim), (fun _ _ _ _ _ _ h => h.elim), by rw [List.drop_length]; trivial⟩
        have hccRun : MonadDom.childCount (m := StateM (DomArena msg)) node a1 = (UInt32.ofNat domCs.length, a1) := by
          dsimp only [MonadDom.childCount]; rw [ha1Get]
        have hremRun : removeUnusedM (m := StateM (DomArena msg)) node live used 0 a1 = ((), aRem) := rfl
        rw [stateM_bind_step hccRun, uint32_toNat_ofNat_lt domCs.length hdomLtU32,
            stateM_bind_step hsnap, stateM_bind_step hremRun]
        cases hrecRun : reconcileLisBackM (m := StateM (DomArena msg)) node (Dom.childNsOf childNs tag)
            live sources inLis rowsArr (rowsHtml s₂).length false 0 aRem with
        | mk _ aOut =>
            rw [stateM_bind_step ((congrArg (reconcileLisBackM (m := StateM (DomArena msg))
              node (Dom.childNsOf childNs tag) live sources inLis rowsArr · false 0 aRem) (hrowsClean.1 s₂).symm).trans hrecRun)]
            dsimp only [StateT.run] at hrec; rw [hrecRun] at hrec; dsimp only at hrec ⊢
            rcases hrec with ⟨haOutGe, haOutBd, haOutFr, _, haOutNode, hCleanOut⟩
            rw [haRemN] at haOutGe haOutBd haOutFr; rw [List.take_length] at haOutBd; rw [hrowsArrEq]
            exact keyedList_finish_goal haClean hparLt hpar hnd hparOut hparNodes hnodeMem haOutGe (by omega)
              (fun m hmn hmLt => (haOutFr m hmn hmLt).trans (haRemOut m hmn))
              haOutNode hElClean' hElEq' hmg' hCleanOut rfl rfl

end

theorem patchViewM_keyedList_spec {σ msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (tag : String) (attrs : List (VAttr σ msg)) (keys : σ → Array String)
    (marks : σ → Array USize) (rowSig : σ → Array String → Nat → Array (String × String))
    (rowEv : σ → Array String → Nat → Array (String × msg)) (rowsHtml : σ → List (Html msg))
    (tmpl? : Option (RowTmpl σ msg))
    (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg)
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (hclean : View.DomClean (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?))
    (hbound : a.nextId + htmlNodeCount (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂) < UInt32.size)
    (hdep : htmlDepth (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂) ≤ f)
    (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ vst.rootNode :: suf))
    (hnd : (pre ++ vst.rootNode :: suf).Nodup) (hparOut : ¬Sold parent.toNat)
    (hSoldLt : ∀ k, Sold k → k < a.nextId) (hparNodes : ∀ r ∈ pre ++ vst.rootNode :: suf, r.toNat < a.nextId)
    (hval : VStateValid f childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₁ a Sold vst) :
    PatchViewPost f childNs parent pns ptag pst pmg
      (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂ pre suf Sold a
      ((patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
        (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂ vst).run a) := by
  cases tmpl? with
  | some _ => exact False.elim hclean
  | none =>
  cases vst with
  | list node oldKeys oldSigs oldRowsL oldMarks inst =>
      rcases hclean with ⟨haClean, hrowsClean⟩
      rcases hval with ⟨hcl, _, rfl, rfl⟩
      dsimp only [VState.rootNode] at hpar hnd hparNodes
      cases f with
      | zero => simp [View.render, CleanDomSubtree] at hcl
      | succ f' =>
          rcases hcl with ⟨hnodeMem, _, _, st, mg, domCs, hnodeGet, hElClean, hElEq, hmg, hCleanCs⟩
          dsimp only [VState.rootNode] at hnodeMem hnodeGet hCleanCs
          let realNs := if childNs == "" && tag == "svg" then Dom.svgNs else childNs
          have hdyn := applyDynAttrsM_spec a node realNs tag st mg domCs attrs s₁ s₂ haClean hElClean hElEq hmg
          rw [DomArena.set_get_self a hnodeGet] at hdyn
          rcases hdyn with ⟨ha1Next, ha1Ne, st', mg', ha1Get, hElClean', hElEq', hmg'⟩
          let a1 := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a).2
          have ha1Eq : applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a = ((), a1) := rfl
          by_cases hsameK : disambiguateKeys (keys s₂) = disambiguateKeys (keys s₁)
          · have hseed := seedRowsM_sameDom inst (rowSig s₂ (disambiguateKeys (keys s₁)))
              (rowEv s₂ (disambiguateKeys (keys s₁))) (marks s₂) oldMarks oldSigs a1
            dsimp only [patchViewM, StateT.run, bind, pure] at hseed ⊢
            simp only [beq_iff_eq.2 hsameK, ↓reduceIte, ite_self]; rw [stateM_bind_step ha1Eq]
            cases hsRun : seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ (disambiguateKeys (keys s₁)))
                (rowEv s₂ (disambiguateKeys (keys s₁))) (marks s₂) oldMarks oldSigs a1 with
            | mk newSigs aOut =>
                rw [hsRun] at hseed; rw [stateM_bind_step hsRun]; dsimp only [StateT.pure] at hseed ⊢
                have haOutNext : aOut.nextId = a.nextId := hseed.1.trans ha1Next
                have haOutOut : ∀ m, m ≠ node → aOut.get m = a.get m := fun m hm => (hseed.get_eq m).trans (ha1Ne m hm)
                have hrowsEq : rowsHtml s₁ = rowsHtml s₂ := keyedRows_eq_of_keys_eq hrowsClean hsameK
                have hClOut := CleanDomChildren_frame (fun m hm => haOutOut m (node_ne_of_toNat_ne hm.2)) hCleanCs
                exact keyedList_finish_goal haClean hparLt hpar hnd hparOut hparNodes hnodeMem (by omega) (by omega)
                  (fun m hm _ => haOutOut m hm) ((hseed.get_eq node).trans ha1Get) hElClean' hElEq' hmg'
                  (by rw [← hrowsEq]; exact CleanDomChildren_mono (fun k hk => ⟨.inl hk.1, hk.2⟩) hClOut)
                  hsameK.symm hrowsEq
          · have hrawNe : keys s₂ ≠ disambiguateKeys (keys s₁) := fun h =>
              hsameK ((disambiguateKeys_of_nodup (h ▸ disambiguateKeys_nodup (keys s₁))).trans h)
            cases hnewEmp : (disambiguateKeys (keys s₂)).isEmpty
            · cases hemp : (rowsHtml s₁).isEmpty
              · exact patchViewM_keyedList_lis_spec hchildNs haClean hrowsClean hbound hdep hparLt hpos hpar hnd
                  hparOut hSoldLt hparNodes hnodeMem hnodeGet hElClean hElEq hmg hCleanCs hrawNe hsameK hnewEmp hemp
              · dsimp only [patchViewM, StateT.run, bind, pure]
                simp only [beq_eq_false_iff_ne.2 hrawNe, beq_eq_false_iff_ne.2 hsameK, hnewEmp, hemp,
                  Bool.false_eq_true, ↓reduceIte]
                have hnilDom : domCs = [] := by
                  rw [List.isEmpty_iff.1 hemp] at hCleanCs
                  cases domCs <;> first | rfl | exact False.elim hCleanCs
                have hseed := seedRowsM_sameDom inst (rowSig s₂ (disambiguateKeys (keys s₂)))
                  (rowEv s₂ (disambiguateKeys (keys s₂))) (marks s₂) #[] #[] a1
                dsimp only [StateT.run] at hseed; rw [stateM_bind_step ha1Eq]
                cases hsRun : seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ (disambiguateKeys (keys s₂)))
                    (rowEv s₂ (disambiguateKeys (keys s₂))) (marks s₂) #[] #[] a1 with
                | mk newSigs aSeed =>
                    rw [hsRun] at hseed; rw [stateM_bind_step hsRun]; dsimp only at hseed ⊢
                    have haSeedNode : aSeed.get node = .element realNs tag st' mg' [] := by
                      rw [hseed.get_eq node, ha1Get, hnilDom]
                    have hccNs := childNamespace_eq_childNsOf (ptag := tag)
                      (show childNs = "" ∨ childNs = Dom.svgNs by rw [hchildNs]; split <;> simp)
                    have hcnRun : MonadDom.childNamespace (m := StateM (DomArena msg)) node aSeed = (Dom.childNsOf childNs tag, aSeed) := by
                      dsimp only [MonadDom.childNamespace]; rw [haSeedNode]; exact congrArg (·, aSeed) hccNs
                    rw [stateM_bind_step hcnRun, Html.map_prefixSignals_of_DomCleanList inst (hrowsClean.2.1 s₂)]
                    exact keyedList_appendFrag_finish haClean hrowsClean hbound hdep hparLt hpos hpar hnd
                      hparOut hSoldLt hparNodes hnodeMem (hseed.1.trans ha1Next) haSeedNode
                      (fun m hm => (hseed.get_eq m).trans (ha1Ne m hm)) hElClean' hElEq' hmg'
            · dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
              simp only [beq_eq_false_iff_ne.2 hrawNe, beq_eq_false_iff_ne.2 hsameK, hnewEmp,
                Bool.false_eq_true, ↓reduceIte]
              have hnewKeysEq : disambiguateKeys (keys s₂) = #[] := Array.isEmpty_iff.1 hnewEmp
              have hnewRows0 : rowsHtml s₂ = [] := List.eq_nil_of_length_eq_zero (by rw [hrowsClean.1 s₂, hnewKeysEq]; rfl)
              let aOut := a1.set node (.element realNs tag st' mg' [])
              have hclr : MonadDom.clearChildren (m := StateM (DomArena msg)) node a1 = ((), aOut) := by
                dsimp only [MonadDom.clearChildren, DomArena.modifyChildren, DomArena.modify, aOut]; rw [ha1Get]
              rw [stateM_bind_step ha1Eq, stateM_bind_step hclr]
              exact keyedList_finish_goal haClean hparLt hpar hnd hparOut hparNodes hnodeMem
                (ha1Next ▸ Nat.le_refl _) (by rw [show aOut.nextId = a.nextId from ha1Next]; omega)
                (fun m hm _ => (DomArena.get_set_ne _ _ hm).trans (ha1Ne m hm))
                (DomArena.get_set_self ..) hElClean' hElEq' hmg'
                (by rw [hnewRows0]; trivial) hnewKeysEq.symm hnewRows0.symm
  | _ => exact False.elim hval.2

end Qed
