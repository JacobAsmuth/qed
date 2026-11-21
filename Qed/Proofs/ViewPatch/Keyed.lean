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
          cases hks : (k == s) with
          | true => have heq : k = s := eq_of_beq hks; subst heq; simp
          | false =>
              have hsk : (s == k) = false := beq_eq_false_iff_ne.2 fun h => by subst h; simp at hks
              simp only [hsk, Bool.false_eq_true, ↓reduceIte]
        · have hsk : (s == k) = false := by
            cases hbeq : (s == k) with
            | false => rfl
            | true => have heq : s = k := eq_of_beq hbeq; subst heq; exact False.elim (hbiS rfl)
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
            have hneK : (s == k) = false := by
              cases hbeq : (s == k) with
              | false => rfl
              | true =>
                  have hsk : s = k := eq_of_beq hbeq; subst hsk
                  have h1 : keys[oi]'(Nat.lt_trans hoiLt hlt) = k := by
                    rw [Array.getElem?_eq_getElem (Nat.lt_trans hoiLt hlt), Option.some.injEq] at hs; exact hs
                  exact False.elim (heqI (nodup_getElem_inj (by simpa using Nat.lt_trans hoiLt hlt) (by simpa using hlt) hnd (by simpa [k] using h1)))
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

private theorem push_step_inv {α : Type} {a : Array α} {i bound : Nat} {x : α} {f : (j : Nat) → j < bound → α}
    (hle : i < bound) (hsz : a.size = i)
    (hprev : ∀ j (hj : j < i), a[j]'(by omega) = f j (Nat.lt_trans hj hle))
    (hcur : x = f i hle) :
    ∀ j (hj : j < i + 1), (a.push x)[j]'(by rw [Array.size_push, hsz]; omega) = f j (by omega) := by
  intro j hj
  by_cases hji : j < i
  · simp only [Array.getElem_push_lt (by omega : j < a.size)]; exact hprev j hji
  · have heq : j = i := by omega
    subst j; simpa [hsz, hcur] using @Array.getElem_push_eq _ a x

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
      let res := planKeyedLoop newKeys oldBuckets mask oldRows oldMarks oldSigs fresh freshCache i
        sources used rows marks sigs
      res.1.size = newKeys.size ∧ res.2.1.size = oldLen ∧ res.2.2.1.size = newKeys.size ∧
      (∀ j (hj : j < newKeys.size), res.1[j]? = some (keyIndexGet oldBuckets mask newKeys[j])) ∧
      (∀ oi, oi < oldLen → (res.2.1.getD oi false = true ↔ ∃ j, ∃ _ : j < newKeys.size, res.1.getD j none = some oi)) ∧
      (∀ j (hj : j < newKeys.size), res.2.2.1[j]? = some (
        match keyIndexGet oldBuckets mask newKeys[j] with
        | some oi => oldRows.getD oi default
        | none => (fresh ()).getD j default)) := by
  intro i
  induction hrem : newKeys.size - i generalizing i with
  | zero =>
      intro freshCache sources used rows marks sigs hle _ hss hus hrs hsrc hused hrows
      have hi : i = newKeys.size := by omega
      subst hi; unfold planKeyedLoop; simp only [Nat.lt_irrefl, ↓reduceDIte]
      refine ⟨hss, hus, hrs, fun j hj => by rw [Array.getElem?_eq_getElem (by omega)]; exact congrArg some (hsrc j hj),
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
      cases hq : keyIndexGet oldBuckets mask newKeys[i] with
      | some oi =>
          have hoi : oi < used.size := by rw [hus]; exact hidxBound _ _ hq
          simp only [hoi, ↓reduceDIte]
          apply ih (i + 1) (by omega) freshCache (sources.push (some oi)) (used.set oi true hoi)
            (rows.push (oldRows.getD oi default)) (marks.push (oldMarks.getD oi 0)) (sigs.push (oldSigs.getD oi #[]))
            (by omega) hfc (by simp [hss]) (by simp [hus]) (by simp [hrs])
          · exact push_step_inv (x := some oi) (f := fun j hj => keyIndexGet oldBuckets mask (newKeys[j]'hj)) hlt hss hsrc hq.symm
          · intro oi' ho'
            by_cases heqO : oi' = oi
            · subst oi'; simp only [Array.getElem_set_self, true_iff]
              exact ⟨i, Nat.lt_succ_self _, by simpa [hss] using @Array.getElem_push_eq _ sources (some oi)⟩
            · simp only [Array.getElem_set_ne (by omega : oi < used.size) (by omega) (Ne.symm heqO), hused oi' ho']
              exact husedPush (some oi) oi' ho' fun h => heqO (Option.some.inj h).symm
          · exact push_step_inv (x := oldRows.getD oi default) (f := fun j hj => match keyIndexGet oldBuckets mask (newKeys[j]'hj) with | some oi => oldRows.getD oi default | none => (fresh ()).getD j default) hlt hrs hrows (by dsimp only; rw [hq])
      | none =>
          have hStep : ∀ (fArr : Array (Html msg)) (fCache' : Option (Array (Html msg))),
              fArr = fresh () → (∀ arr, fCache' = some arr → arr = fresh ()) →
              let res := planKeyedLoop newKeys oldBuckets mask oldRows oldMarks oldSigs fresh fCache' (i + 1)
                (sources.push none) used (rows.push (fArr.getD i default)) (marks.push 0) (sigs.push #[])
              res.1.size = newKeys.size ∧ res.2.1.size = oldLen ∧ res.2.2.1.size = newKeys.size ∧
              (∀ j (hj : j < newKeys.size), res.1[j]? = some (keyIndexGet oldBuckets mask newKeys[j])) ∧
              (∀ oi, oi < oldLen → (res.2.1.getD oi false = true ↔ ∃ j, ∃ _ : j < newKeys.size, res.1.getD j none = some oi)) ∧
              (∀ j (hj : j < newKeys.size), res.2.2.1[j]? = some (
                match keyIndexGet oldBuckets mask newKeys[j] with
                | some oi => oldRows.getD oi default
                | none => (fresh ()).getD j default)) := by
            intro fArr fCache' hfArr hfCache'; subst fArr
            apply ih (i + 1) (by omega) fCache' (sources.push none) used
              (rows.push ((fresh ()).getD i default)) (marks.push 0) (sigs.push #[])
              (by omega) hfCache' (by simp [hss]) hus (by simp [hrs])
            · exact push_step_inv (x := none) (f := fun j hj => keyIndexGet oldBuckets mask (newKeys[j]'hj)) hlt hss hsrc hq.symm
            · intro oi' ho'; rw [hused oi' ho']; exact husedPush none oi' ho' (by simp)
            · exact push_step_inv (x := (fresh ()).getD i default) (f := fun j hj => match keyIndexGet oldBuckets mask (newKeys[j]'hj) with | some oi => oldRows.getD oi default | none => (fresh ()).getD j default) hlt hrs hrows (by dsimp only; rw [hq])
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
        constructor
        · rintro (rfl | rfl | hm)
          · exact .inr (.inl rfl)
          · exact .inl rfl
          · exact .inr (.inr hm)
        · rintro (rfl | rfl | hm)
          · exact .inr (.inl rfl)
          · exact .inl rfl
          · exact .inr (.inr hm)

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
      have hrange : List.range (r + 1) = 0 :: (List.range r).map (· + 1) := by
        rw [List.range_succ_eq_map]
      unfold removeUnusedM
      simp only [hlt, ↓reduceDIte]
      by_cases hu : used.getD i false = true
      · simp only [hu, ↓reduceIte]
        have hnd' : ((kept ++ [live[i]]) ++ live.toList.drop (i + 1)).Nodup := by simpa [List.append_assoc] using hnd
        have hget' : a.get node = .element ns tag st mg ((kept ++ [live[i]]) ++ live.toList.drop (i + 1)) := by
          simpa [List.append_assoc] using hget
        have hrec := ih (i + 1) (by omega) (kept ++ [live[i]]) a (by omega) hnd' hget'
        refine ⟨hrec.1, hrec.2.1, ?_⟩
        rw [hrec.2.2, hrange]
        simp only [List.filterMap_cons, Nat.add_zero, hu, ↓reduceIte, Array.getD, hlt,
          List.filterMap_map, List.append_assoc, List.singleton_append]
        congr 3; apply congrArg (fun f => List.filterMap f (List.range r)); funext d
        simp [Nat.add_comm, Nat.add_left_comm]
      · have huF : used.getD i false = false := Bool.eq_false_iff.2 hu
        simp only [huF, Bool.false_eq_true, ↓reduceIte, StateT.run, bind, StateT.bind]
        have hnotKept : live[i] ∉ kept := by
          intro hm
          have hndPair := List.nodup_append.1 hnd
          exact hndPair.2.2 live[i] hm live[i] (List.mem_cons_self ..) rfl
        let a1 := a.set node (.element ns tag st mg (kept ++ live.toList.drop (i + 1)))
        have hstep : MonadDom.removeNode (m := StateM (DomArena msg)) node live[i] a = ((), a1) := by
          simp only [MonadDom.removeNode, DomArena.modifyChildren, DomArena.modify, hget,
            erase_append_right_of_not_mem kept (live[i] :: live.toList.drop (i + 1)) hnotKept,
            List.erase_cons_head, a1]
        have hnd' : (kept ++ live.toList.drop (i + 1)).Nodup := by
          have := List.nodup_append.1 hnd
          refine List.nodup_append.2 ⟨this.1, (List.nodup_cons.1 this.2.1).2, fun x hx y hy =>
            this.2.2 x hx y (List.mem_cons_of_mem _ hy)⟩
        have hrec := ih (i + 1) (by omega) kept a1 (by omega) hnd' (DomArena.get_set_self ..)
        dsimp only [StateT.run] at hrec
        have hrunEq : (match MonadDom.removeNode (m := StateM (DomArena msg)) node live[i] a with
          | ((), s') => removeUnusedM (m := StateM (DomArena msg)) node live used (i + 1) s') =
            removeUnusedM (m := StateM (DomArena msg)) node live used (i + 1) a1 := by rw [hstep]
        change (match MonadDom.removeNode (m := StateM (DomArena msg)) node live[i] a with
          | ((), s') => removeUnusedM (m := StateM (DomArena msg)) node live used (i + 1) s').2.nextId = a.nextId ∧
          (∀ m, m ≠ node → (match MonadDom.removeNode (m := StateM (DomArena msg)) node live[i] a with
            | ((), s') => removeUnusedM (m := StateM (DomArena msg)) node live used (i + 1) s').2.get m = a.get m) ∧
          (match MonadDom.removeNode (m := StateM (DomArena msg)) node live[i] a with
            | ((), s') => removeUnusedM (m := StateM (DomArena msg)) node live used (i + 1) s').2.get node = _
        rw [hrunEq]
        refine ⟨hrec.1, fun m hm => (hrec.2.1 m hm).trans (DomArena.get_set_ne _ _ hm), ?_⟩
        rw [hrec.2.2, hrange]
        simp only [List.filterMap_cons, Nat.add_zero, huF, Bool.false_eq_true, ↓reduceIte, List.filterMap_map]
        congr 2; apply congrArg (fun f => List.filterMap f (List.range r)); funext d
        simp [Nat.add_comm, Nat.add_left_comm]

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
  have hkeptMem : ∀ x, x ∈ kept ↔ ∃ oi, oi < live.size ∧ used.getD oi false = true ∧ live.getD oi 0 = x := by
    intro x; simp only [kept, List.mem_filterMap, List.mem_range]; constructor
    · rintro ⟨oi, hoi, hif⟩; cases hu : used.getD oi false with | false => simp [hu] at hif | true => simp [hu] at hif; exact ⟨oi, hoi, hu, by simpa [Array.getD, hoi] using hif⟩
    · rintro ⟨oi, hoi, hu, hEq⟩; exact ⟨oi, hoi, by rw [if_pos hu, hEq]⟩
  have hdisj : ∀ x, x ∈ filterLisNodes live sources inLis false n → x ∈ filterLisNodes live sources inLis true n → False := by
    intro x hm hl
    rcases (mem_filterLisNodes ..).1 hm with ⟨i₁, oi₁, hi1, hf1, hs1, hx1⟩
    rcases (mem_filterLisNodes ..).1 hl with ⟨i₂, oi₂, hi2, hf2, hs2, hx2⟩
    have hoiEq := hliveInj oi₁ oi₂ (hsrcBound i₁ hi1 oi₁ hs1) (hsrcBound i₂ hi2 oi₂ hs2) (hx1.trans hx2.symm)
    subst hoiEq; have hiEq := hsrcInj i₁ i₂ hi1 hi2 oi₁ hs1 hs2; subst hiEq; simp [hf1] at hf2
  have hkeptNd : kept.Nodup := by
    have haux : ∀ m, m ≤ live.size → ((List.range m).filterMap fun oi => if used.getD oi false then some (live.getD oi 0) else none).Nodup := by
      intro m; induction m with
      | zero => intro _; simp
      | succ m ih =>
          intro hm; rw [range_filterMap_succ]
          cases hu : used.getD m false with
          | false => simpa using ih (by omega)
          | true =>
              simp only [↓reduceIte]
              refine List.nodup_append.2 ⟨ih (by omega), List.pairwise_singleton _ _, fun x hx y hy heq => ?_⟩
              simp only [List.mem_singleton] at hy; subst hy; simp only [List.mem_filterMap, List.mem_range] at hx
              rcases hx with ⟨oi, hoi, hif⟩; split at hif
              · cases hif; have := hliveInj oi m (by omega) (by omega) heq; omega
              · cases hif
    exact haux live.size (Nat.le_refl _)
  have hkeptIff : ∀ x, x ∈ kept ↔ x ∈ filterLisNodes live sources inLis false n ∨ x ∈ filterLisNodes live sources inLis true n := by
    intro x; rw [hkeptMem, mem_filterLisNodes, mem_filterLisNodes]; constructor
    · rintro ⟨oi, hoi, hu, rfl⟩
      rcases (husedIff oi hoi).1 hu with ⟨i, hi, hs⟩
      cases hfl : inLis.getD i false with | false => exact .inl ⟨i, oi, hi, hfl, hs, rfl⟩ | true => exact .inr ⟨i, oi, hi, hfl, hs, rfl⟩
    · rintro (⟨i, oi, hi, _, hs, rfl⟩ | ⟨i, oi, hi, _, hs, rfl⟩) <;>
        exact ⟨oi, hsrcBound i hi oi hs, (husedIff oi (hsrcBound i hi oi hs)).2 ⟨i, hi, hs⟩, rfl⟩
  have hfiltEq : kept.filter (fun x => !(filterLisNodes live sources inLis false n).contains x) = filterLisNodes live sources inLis true n := by
    have hsortedEq : ∀ (xs ys : List Nat), xs.Pairwise (· < ·) → ys.Pairwise (· < ·) → (∀ a, a ∈ xs ↔ a ∈ ys) → xs = ys := by
      intro xs; induction xs with
      | nil => intro ys _ _ hiff; cases ys with | nil => rfl | cons y _ => exact absurd ((hiff y).2 (List.mem_cons_self ..)) (List.not_mem_nil)
      | cons x xs ih =>
          intro ys hx hy hiff
          cases ys with
          | nil => exact absurd ((hiff x).1 (List.mem_cons_self ..)) (List.not_mem_nil)
          | cons y ys =>
              rcases List.pairwise_cons.1 hx with ⟨hxLt, hxs⟩; rcases List.pairwise_cons.1 hy with ⟨hyLt, hys⟩
              have hxy : x = y := by
                rcases List.mem_cons.1 ((hiff x).1 (List.mem_cons_self ..)) with rfl | hxt
                · rfl
                · rcases List.mem_cons.1 ((hiff y).2 (List.mem_cons_self ..)) with rfl | hyt
                  · rfl
                  · have := hxLt y hyt; have := hyLt x hxt; omega
              subst hxy; congr 1
              refine ih ys hxs hys fun a => ⟨fun ha => ?_, fun ha => ?_⟩
              · rcases List.mem_cons.1 ((hiff a).1 (List.mem_cons_of_mem x ha)) with rfl | hay
                · exact absurd (hxLt a ha) (Nat.lt_irrefl _)
                · exact hay
              · rcases List.mem_cons.1 ((hiff a).2 (List.mem_cons_of_mem x ha)) with rfl | hax
                · exact absurd (hyLt a ha) (Nat.lt_irrefl _)
                · exact hax
    let oiKept := (List.range live.size).filter fun oi => used.getD oi false && !(filterLisNodes live sources inLis false n).contains (live.getD oi 0)
    let oiLis := (List.range n).filterMap fun i => if inLis.getD i false then sources.getD i none else none
    have hlhs : kept.filter (fun x => !(filterLisNodes live sources inLis false n).contains x) = oiKept.map (fun oi => live.getD oi 0) := by
      have hgen : ∀ l : List Nat,
          ((l.filterMap fun oi => if used.getD oi false then some (live.getD oi 0) else none).filter
            (fun x => !(filterLisNodes live sources inLis false n).contains x)) =
          (l.filter fun oi => used.getD oi false && !(filterLisNodes live sources inLis false n).contains (live.getD oi 0)).map (fun oi => live.getD oi 0) := by
        intro l; induction l with
        | nil => rfl
        | cons a rest ih =>
            simp only [List.filterMap_cons, List.filter_cons]
            cases used.getD a false with
            | false => simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, ih]
            | true =>
                simp only [↓reduceIte, Bool.true_and, List.filter_cons]
                cases !(filterLisNodes live sources inLis false n).contains (live.getD a 0) <;> simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, ih]
      exact hgen (List.range live.size)
    have hrhs : filterLisNodes live sources inLis true n = oiLis.map (fun oi => live.getD oi 0) := by
      have hgen : ∀ l : List Nat,
          (l.filterMap fun i => if inLis.getD i false == true then (sources.getD i none).map (live.getD · 0) else none) =
          (l.filterMap fun i => if inLis.getD i false then sources.getD i none else none).map (fun oi => live.getD oi 0) := by
        intro l; induction l with
        | nil => rfl
        | cons a rest ih =>
            simp only [List.filterMap_cons]
            cases inLis.getD a false with
            | false => simp only [Bool.false_eq_true, ↓reduceIte, ih]; rfl
            | true => simp only [beq_self_eq_true, ↓reduceIte]; cases sources.getD a none <;> simp only [Option.map_none, Option.map_some, List.map_cons, ih]
      exact hgen (List.range n)
    rw [hlhs, hrhs]; apply congrArg (List.map fun oi => live.getD oi 0); apply hsortedEq
    · exact List.Pairwise.filter _ List.pairwise_lt_range
    · have haux : ∀ m, m ≤ n → ((List.range m).filterMap fun i => if inLis.getD i false then sources.getD i none else none).Pairwise (· < ·) := by
        intro m; induction m with
        | zero => intro _; simp
        | succ m ih =>
            intro hm; rw [range_filterMap_succ]
            cases hfl : inLis.getD m false with
            | false => simpa using ih (by omega)
            | true =>
                simp only [↓reduceIte]
                cases hs : sources.getD m none with
                | none => simpa using ih (by omega)
                | some om =>
                    refine List.pairwise_append.2 ⟨ih (by omega), List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
                    simp only [List.mem_singleton] at hb; subst b; simp only [List.mem_filterMap, List.mem_range] at ha
                    rcases ha with ⟨i, hi, hif⟩
                    cases hfi : inLis.getD i false with
                    | false => simp [hfi] at hif
                    | true => simp only [hfi, ↓reduceIte] at hif; exact hlisMono i m hi (by omega) hfi hfl a om hif hs
      exact haux n (Nat.le_refl _)
    · intro oi
      simp only [oiKept, oiLis, List.mem_filter, List.mem_range, Bool.and_eq_true, Bool.not_eq_true', List.mem_filterMap]
      constructor
      · rintro ⟨hoi, hu, hnotM⟩
        rcases (husedIff oi hoi).1 hu with ⟨i, hi, hs⟩
        cases hfl : inLis.getD i false with
        | true => exact ⟨i, hi, by simp [hfl, hs]⟩
        | false =>
            have hc := List.contains_iff_mem.2 ((mem_filterLisNodes live sources inLis false n _).2 ⟨i, oi, hi, hfl, hs, rfl⟩)
            rw [hc] at hnotM; cases hnotM
      · rintro ⟨i, hi, hif⟩
        cases hfl : inLis.getD i false with
        | false => simp [hfl] at hif
        | true =>
            simp only [hfl, ↓reduceIte] at hif
            have hoi := hsrcBound i hi oi hif
            refine ⟨hoi, (husedIff oi hoi).2 ⟨i, hi, hif⟩, ?_⟩
            cases hc : (filterLisNodes live sources inLis false n).contains (live.getD oi 0) with
            | false => rfl
            | true => exact False.elim (hdisj _ (List.contains_iff_mem.1 hc) ((mem_filterLisNodes ..).2 ⟨i, oi, hi, hfl, hif, rfl⟩))
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

private abbrev ReconcileBackGoal {msg : Type} (f' : Nat) (node : Dom.Node)
    (realNs tag : String) (st' : SpecElemState msg) (mg' : List String)
    (childNs : String) (live : Array Dom.Node) (sources : Array (Option Nat))
    (inLis : Array Bool) (rowsArr : Array (Html msg)) (newRowsL : List (Html msg))
    (oldRowsL : List (Html msg)) (Si : Nat → Nat → Prop) (Sold : Nat → Prop) (baseNext : Nat)
    (k : Nat) : Prop :=
  k ≤ newRowsL.length → ∀ (hasAnchor : Bool) (anchor : Dom.Node)
    (cs placed : List Dom.Node) (Splaced : Nat → Prop) (a : DomArena msg),
    baseNext ≤ a.nextId →
    0 < a.nextId →
    a.nextId + htmlListNodeCount (newRowsL.take k) < UInt32.size →
    node.toNat < a.nextId →
    a.get node = .element realNs tag st' mg' cs →
    cs.Nodup →
    (hasAnchor = !placed.isEmpty) →
    (if hasAnchor then some anchor else none) = placed.head? →
    (∀ x, x ∈ cs ↔ x ∈ filterLisNodes live sources inLis false k ∨ x ∈ filterLisNodes live sources inLis true k ∨ x ∈ placed) →
    (∀ x, x ∈ filterLisNodes live sources inLis false k → x ∈ filterLisNodes live sources inLis true k → False) →
    (∀ x, x ∈ filterLisNodes live sources inLis false k → x ∈ placed → False) →
    (∀ x, x ∈ filterLisNodes live sources inLis true k → x ∈ placed → False) →
    cs.filter (fun x => !(filterLisNodes live sources inLis false k).contains x) =
      filterLisNodes live sources inLis true k ++ placed →
    (∀ oi (ho : oi < oldRowsL.length), CleanDomSubtree f' childNs oldRowsL[oi] a (Si oi) (live.getD oi 0)) →
    (∀ m, Splaced m → (Sold m ∨ (baseNext ≤ m ∧ m < a.nextId)) ∧ m ≠ node.toNat) →
    (∀ i, i < k → ∀ oi, sources.getD i none = some oi → ∀ m, Si oi m → Splaced m → False) →
    CleanDomChildren f' childNs (newRowsL.drop k) a Splaced placed →
    let aOut := (reconcileLisBackM (m := StateM (DomArena msg)) node childNs live sources inLis rowsArr k hasAnchor anchor).run a |>.2
    a.nextId ≤ aOut.nextId ∧
    aOut.nextId ≤ a.nextId + htmlListNodeCount (newRowsL.take k) ∧
    (∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    ∃ finalCs,
      aOut.get node = .element realNs tag st' mg' finalCs ∧
      CleanDomChildren f' childNs newRowsL aOut
        (fun m => (Sold m ∨ (baseNext ≤ m ∧ m < aOut.nextId)) ∧ m ≠ node.toNat) finalCs

private theorem reconcileLisBackM_move_step {msg : Type} (f' : Nat) (node : Dom.Node)
    (realNs tag : String) (st' : SpecElemState msg) (mg' : List String)
    (childNs : String) (live : Array Dom.Node) (sources : Array (Option Nat))
    (inLis : Array Bool) (rowsArr : Array (Html msg)) (newRowsL oldRowsL : List (Html msg))
    (Si : Nat → Nat → Prop) (Sold : Nat → Prop) (baseNext k oi : Nat)
    (hasAnchor : Bool) (anchor : Dom.Node) (cs placed : List Dom.Node) (Splaced : Nat → Prop) (a : DomArena msg)
    (hSiSub : ∀ oi k, Si oi k → Sold k ∧ k ≠ node.toNat)
    (ih : ReconcileBackGoal f' node realNs tag st' mg' childNs live sources inLis rowsArr newRowsL oldRowsL Si Sold baseNext k)
    (hkLt : k < newRowsL.length) (htakeCnt : htmlListNodeCount (newRowsL.take (k + 1)) = htmlListNodeCount (newRowsL.take k) + htmlNodeCount newRowsL[k])
    (hsK : sources.getD k none = some oi) (hflKF : inLis.getD k false = false)
    (hbase : baseNext ≤ a.nextId) (hpos : 0 < a.nextId) (hbdK : a.nextId + htmlListNodeCount (newRowsL.take k) < UInt32.size)
    (hnodeLt : node.toNat < a.nextId) (hget : a.get node = .element realNs tag st' mg' cs) (hcsNd : cs.Nodup)
    (hanc : (if hasAnchor then some anchor else none) = placed.head?)
    (hcsMem : ∀ x, x ∈ cs ↔ x ∈ filterLisNodes live sources inLis false (k + 1) ∨ x ∈ filterLisNodes live sources inLis true (k + 1) ∨ x ∈ placed)
    (hDisjML : ∀ x, x ∈ filterLisNodes live sources inLis false (k + 1) → x ∈ filterLisNodes live sources inLis true (k + 1) → False)
    (hDisjMP : ∀ x, x ∈ filterLisNodes live sources inLis false (k + 1) → x ∈ placed → False)
    (hDisjLP : ∀ x, x ∈ filterLisNodes live sources inLis true (k + 1) → x ∈ placed → False)
    (hfilt : cs.filter (fun x => !(filterLisNodes live sources inLis false (k + 1)).contains x) =
      filterLisNodes live sources inLis true (k + 1) ++ placed)
    (hOldClean : ∀ oi (ho : oi < oldRowsL.length), CleanDomSubtree f' childNs oldRowsL[oi] a (Si oi) (live.getD oi 0))
    (hClPl' : CleanDomChildren f' childNs (newRowsL.drop k) a (fun m => Si oi m ∨ Splaced m) (live.getD oi 0 :: placed))
    (hSpSub' : ∀ m, (Si oi m ∨ Splaced m) → (Sold m ∨ (baseNext ≤ m ∧ m < a.nextId)) ∧ m ≠ node.toNat)
    (hSpDisj' : ∀ i, i < k → ∀ oi', sources.getD i none = some oi' → ∀ m, Si oi' m → (Si oi m ∨ Splaced m) → False)
    (hchildNotF : ∀ w, live.getD oi 0 ∉ filterLisNodes live sources inLis w k) :
    let child := live.getD oi 0
    let aOut := (StateT.bind (MonadDom.insertBeforeRef (m := StateM (DomArena msg)) node (if hasAnchor then some anchor else none) child) fun _ =>
      reconcileLisBackM node childNs live sources inLis rowsArr k true child) a |>.2
    a.nextId ≤ aOut.nextId ∧
    aOut.nextId ≤ a.nextId + htmlListNodeCount (newRowsL.take (k + 1)) ∧
    (∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    ∃ finalCs,
      aOut.get node = .element realNs tag st' mg' finalCs ∧
      CleanDomChildren f' childNs newRowsL aOut
        (fun m => (Sold m ∨ (baseNext ≤ m ∧ m < aOut.nextId)) ∧ m ≠ node.toNat) finalCs := by
  let child := live.getD oi 0
  change ∀ w, child ∉ filterLisNodes live sources inLis w k at hchildNotF
  have hmovEq : filterLisNodes live sources inLis false (k + 1) = filterLisNodes live sources inLis false k ++ [child] := by
    rw [filterLisNodes_succ, hflKF, hsK]; simp only [beq_self_eq_true, ↓reduceIte, child]
  have hlisEq : filterLisNodes live sources inLis true (k + 1) = filterLisNodes live sources inLis true k := by
    rw [filterLisNodes_succ, hflKF]; simp only [beq_true, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  rw [hmovEq] at hcsMem hDisjML hDisjMP hfilt
  rw [hlisEq] at hcsMem hDisjML hDisjLP hfilt
  let ref? := if hasAnchor then some anchor else none
  let cs' := w3cInsertBeforeRef cs ref? child
  have hstep : MonadDom.insertBeforeRef (m := StateM (DomArena msg)) node ref? child a =
      ((), a.set node (.element realNs tag st' mg' cs')) := by
    simp only [MonadDom.insertBeforeRef, DomArena.modifyChildren, DomArena.modify, hget, cs']
  have hrunStep : (StateT.bind (MonadDom.insertBeforeRef (m := StateM (DomArena msg)) node ref? child) fun _ =>
      reconcileLisBackM node childNs live sources inLis rowsArr k true child) a =
      reconcileLisBackM (m := StateM (DomArena msg)) node childNs live sources inLis rowsArr k true child
        (a.set node (.element realNs tag st' mg' cs')) := by
    dsimp only [StateT.bind]; rw [hstep]; rfl
  dsimp only [child] at hrunStep ⊢
  rw [hrunStep]
  have hchildNotPl : child ∉ placed := fun hp => hDisjMP child (List.mem_append_right _ (List.mem_singleton_self _)) hp
  have hchildNotEr : child ∉ cs.erase child := List.Nodup.not_mem_erase hcsNd
  have hfiltEr : (cs.erase child).filter (fun x => !(filterLisNodes live sources inLis false k).contains x) =
      filterLisNodes live sources inLis true k ++ placed := by
    have hpEq : ∀ x ∈ cs.erase child,
        (!(filterLisNodes live sources inLis false k).contains x) =
        (!(filterLisNodes live sources inLis false k ++ [child]).contains x) :=
      fun x hx => by
        have hne : x ≠ child := fun h => hchildNotEr (h ▸ hx)
        simp only [List.contains_append, List.contains_cons, List.contains_nil, Bool.or_false,
          beq_eq_false_iff_ne.2 hne]
    have hnotC : (!(filterLisNodes live sources inLis false k ++ [child]).contains child) = false := by
      simp only [List.contains_append, List.contains_cons, beq_self_eq_true, Bool.true_or, Bool.or_true, Bool.not_true]
    rw [List.filter_congr hpEq, erase_filter_of_false _ child hnotC, hfilt]
  have ⟨hcs'Nd, hmemC', hcs'Filt⟩ := w3cInsertBeforeRef_reconcile_step hcsNd hanc hchildNotPl
    (hchildNotF false) (fun y hy => hDisjMP y (List.mem_append_left _ hy)) hDisjLP hfiltEr
  have hcs'Mem : ∀ x, x ∈ cs' ↔ x ∈ filterLisNodes live sources inLis false k ∨ x ∈ filterLisNodes live sources inLis true k ∨ x ∈ child :: placed := by
    intro x
    have hmemEr : x ∈ cs.erase child ↔ x ≠ child ∧ x ∈ cs :=
      ⟨fun h => ⟨fun he => hchildNotEr (he ▸ h), List.mem_of_mem_erase h⟩, fun ⟨hne, hm⟩ => (List.mem_erase_of_ne hne).2 hm⟩
    rw [hmemC', hmemEr, hcsMem x]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨fun | .inl rfl => .inr (.inr (.inl rfl)) | .inr ⟨hne, .inl (.inl h)⟩ => .inl h | .inr ⟨hne, .inl (.inr rfl)⟩ => absurd rfl hne
               | .inr ⟨_, .inr (.inl h)⟩ => .inr (.inl h) | .inr ⟨_, .inr (.inr h)⟩ => .inr (.inr (.inr h)),
           fun | .inl h => .inr ⟨fun he => hchildNotF false (he ▸ h), .inl (.inl h)⟩
               | .inr (.inl h) => .inr ⟨fun he => hchildNotF true (he ▸ h), .inr (.inl h)⟩
               | .inr (.inr (.inl rfl)) => .inl rfl
               | .inr (.inr (.inr h)) => .inr ⟨fun he => hchildNotPl (he ▸ h), .inr (.inr h)⟩⟩
  let a1 := a.set node (.element realNs tag st' mg' cs')
  have hOldClean' : ∀ oi (ho : oi < oldRowsL.length), CleanDomSubtree f' childNs oldRowsL[oi] a1 (Si oi) (live.getD oi 0) :=
    fun oi ho => CleanDomSubtree_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSiSub oi m.toNat hm).2)) (hOldClean oi ho)
  have hClPl1 : CleanDomChildren f' childNs (newRowsL.drop k) a1 (fun m => Si oi m ∨ Splaced m) (child :: placed) :=
    CleanDomChildren_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSpSub' m.toNat hm).2)) hClPl'
  have hres := ih (Nat.le_of_lt hkLt) true child cs' (child :: placed) (fun m => Si oi m ∨ Splaced m) a1
    hbase hpos hbdK hnodeLt (DomArena.get_set_self ..) hcs'Nd rfl rfl hcs'Mem
    (fun x hm hl => hDisjML x (List.mem_append_left _ hm) hl)
    (fun x hm hp => (List.mem_cons.1 hp).elim (fun h => hchildNotF false (h ▸ hm)) (hDisjMP x (List.mem_append_left _ hm)))
    (fun x hl hp => (List.mem_cons.1 hp).elim (fun h => hchildNotF true (h ▸ hl)) (hDisjLP x hl))
    hcs'Filt hOldClean' hSpSub' hSpDisj' hClPl1
  dsimp only [StateT.run] at hres
  exact ⟨hres.1, Nat.le_trans hres.2.1 (htakeCnt ▸ Nat.add_le_add_left (Nat.le_add_right _ _) _),
    fun m hmn hmLt => (hres.2.2.1 m hmn hmLt).trans (DomArena.get_set_ne _ _ hmn), hres.2.2.2⟩

private theorem reconcileLisBackM_create_step {msg : Type} (f' : Nat) (node : Dom.Node)
    (realNs tag : String) (st' : SpecElemState msg) (mg' : List String)
    (childNs : String) (live : Array Dom.Node) (sources : Array (Option Nat))
    (inLis : Array Bool) (rowsArr : Array (Html msg)) (newRowsL oldRowsL : List (Html msg))
    (Si : Nat → Nat → Prop) (Sold : Nat → Prop) (baseNext k : Nat)
    (hasAnchor : Bool) (anchor : Dom.Node) (cs placed : List Dom.Node) (Splaced : Nat → Prop) (a : DomArena msg)
    (hrowsArrEq : rowsArr.toList = newRowsL)
    (hnewClean : Html.DomCleanList newRowsL = true)
    (hsrcBound : ∀ i, i < newRowsL.length → ∀ oi, sources.getD i none = some oi → oi < oldRowsL.length)
    (hSiSub : ∀ oi k, Si oi k → Sold k ∧ k ≠ node.toNat)
    (hSoldLt : ∀ k, Sold k → k < baseNext)
    (hdep : htmlListDepth newRowsL ≤ f')
    (ih : ReconcileBackGoal f' node realNs tag st' mg' childNs live sources inLis rowsArr newRowsL oldRowsL Si Sold baseNext k)
    (hkLt : k < newRowsL.length)
    (htakeCnt : htmlListNodeCount (newRowsL.take (k + 1)) = htmlListNodeCount (newRowsL.take k) + htmlNodeCount newRowsL[k])
    (hdrop : newRowsL.drop k = newRowsL[k] :: newRowsL.drop (k + 1))
    (hsK : sources.getD k none = none)
    (hbase : baseNext ≤ a.nextId) (hpos : 0 < a.nextId)
    (hbd : a.nextId + htmlListNodeCount (newRowsL.take (k + 1)) < UInt32.size)
    (hnodeLt : node.toNat < a.nextId) (hget : a.get node = .element realNs tag st' mg' cs) (hcsNd : cs.Nodup)
    (hanc : (if hasAnchor then some anchor else none) = placed.head?)
    (hcsMem : ∀ x, x ∈ cs ↔ x ∈ filterLisNodes live sources inLis false (k + 1) ∨ x ∈ filterLisNodes live sources inLis true (k + 1) ∨ x ∈ placed)
    (hDisjML : ∀ x, x ∈ filterLisNodes live sources inLis false (k + 1) → x ∈ filterLisNodes live sources inLis true (k + 1) → False)
    (hDisjMP : ∀ x, x ∈ filterLisNodes live sources inLis false (k + 1) → x ∈ placed → False)
    (hDisjLP : ∀ x, x ∈ filterLisNodes live sources inLis true (k + 1) → x ∈ placed → False)
    (hfilt : cs.filter (fun x => !(filterLisNodes live sources inLis false (k + 1)).contains x) =
      filterLisNodes live sources inLis true (k + 1) ++ placed)
    (hOldClean : ∀ oi (ho : oi < oldRowsL.length), CleanDomSubtree f' childNs oldRowsL[oi] a (Si oi) (live.getD oi 0))
    (hSpSub : ∀ m, Splaced m → (Sold m ∨ (baseNext ≤ m ∧ m < a.nextId)) ∧ m ≠ node.toNat)
    (hSpDisj : ∀ i, i < k + 1 → ∀ oi, sources.getD i none = some oi → ∀ m, Si oi m → Splaced m → False)
    (hClPl : CleanDomChildren f' childNs (newRowsL.drop (k + 1)) a Splaced placed) :
    let aOut := (StateT.bind (buildDomM (m := StateM (DomArena msg)) childNs (rowsArr.getD k default)) fun cn =>
      StateT.bind (MonadDom.insertBeforeRef node (if hasAnchor then some anchor else none) cn) fun _ =>
        reconcileLisBackM node childNs live sources inLis rowsArr k true cn) a |>.2
    a.nextId ≤ aOut.nextId ∧
    aOut.nextId ≤ a.nextId + htmlListNodeCount (newRowsL.take (k + 1)) ∧
    (∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    ∃ finalCs,
      aOut.get node = .element realNs tag st' mg' finalCs ∧
      CleanDomChildren f' childNs newRowsL aOut
        (fun m => (Sold m ∨ (baseNext ≤ m ∧ m < aOut.nextId)) ∧ m ≠ node.toNat) finalCs := by
  have hkLe : k ≤ newRowsL.length := Nat.le_of_lt hkLt
  have hStepF : ∀ w, filterLisNodes live sources inLis w (k + 1) = filterLisNodes live sources inLis w k := fun w => by
    rw [filterLisNodes_succ, hsK]; cases (inLis.getD k false == w) <;> simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
  rw [hStepF false] at hcsMem hDisjML hDisjMP hfilt
  rw [hStepF true] at hcsMem hDisjML hDisjLP hfilt
  have hrowAtK : rowsArr.getD k default = newRowsL[k] := by
    have hkArr : k < rowsArr.size := by rw [← Array.length_toList, hrowsArrEq]; exact hkLt
    simp only [Array.getD, hkArr, ↓reduceDIte]
    exact (Array.getElem_toList (xs := rowsArr) (i := k) (h := hkArr)).symm.trans (by subst hrowsArrEq; rfl)
  rw [hrowAtK]
  have hrowClean : newRowsL[k].DomClean = true := htmlDomCleanList_mem hnewClean newRowsL[k] (List.getElem_mem hkLt)
  have hrowDep : htmlDepth newRowsL[k] ≤ f' := Nat.le_trans (htmlDepth_le_listDepth newRowsL[k] (List.getElem_mem hkLt)) hdep
  have hbdRow : a.nextId + htmlNodeCount newRowsL[k] < UInt32.size :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left _ _) _) (htakeCnt ▸ hbd)
  have hbmSpec := buildDomM_spec childNs newRowsL[k] a f' hpos hbdRow hrowDep
  have hbuilt := CleanDomSubtree_of_buildDomM childNs newRowsL[k] a f' hrowClean hpos hbdRow hrowDep
  dsimp only [StateT.run] at hbmSpec hbuilt
  cases hbr : buildDomM (m := StateM (DomArena msg)) childNs newRowsL[k] a with
  | mk cn a1 =>
      rw [hbr] at hbmSpec hbuilt; dsimp only at hbmSpec hbuilt ⊢
      rcases hbmSpec with ⟨hcnGe, hcnLt, ha1Bd, ha1Fr, _, _⟩
      have ha1Ge : a.nextId ≤ a1.nextId := Nat.le_trans hcnGe (Nat.le_of_lt hcnLt)
      have hcnRange : a.nextId ≤ cn.toNat ∧ cn.toNat < a1.nextId := CleanDomSubtree_root_mem hbuilt
      have hfiltInA : ∀ w x, x ∈ filterLisNodes live sources inLis w k → x.toNat < a.nextId := fun w x hx => by
        rcases (mem_filterLisNodes ..).1 hx with ⟨i, oi', hi, _, hsi, rfl⟩
        have hoi' := hsrcBound i (Nat.lt_trans hi hkLt) oi' hsi
        exact Nat.lt_of_lt_of_le (hSoldLt _ (hSiSub oi' _ (CleanDomSubtree_root_mem (hOldClean oi' hoi'))).1) hbase
      have hcsInA : ∀ x ∈ cs, x.toNat < a.nextId := fun x hx =>
        match (hcsMem x).1 hx with
        | .inl hm => hfiltInA false x hm
        | .inr (.inl hl) => hfiltInA true x hl
        | .inr (.inr hp) => (hSpSub x.toNat (CleanDomChildren_mem hClPl x hp)).1.elim
            (fun hs => Nat.lt_of_lt_of_le (hSoldLt _ hs) hbase) (·.2)
      have hcnNotCs : cn ∉ cs := fun hm => Nat.not_lt.2 hcnRange.1 (hcsInA cn hm)
      have hcnNotMov : cn ∉ filterLisNodes live sources inLis false k := fun hm => hcnNotCs ((hcsMem cn).2 (.inl hm))
      have hcnNotLis : cn ∉ filterLisNodes live sources inLis true k := fun hm => hcnNotCs ((hcsMem cn).2 (.inr (.inl hm)))
      have hcnNotPl : cn ∉ placed := fun hm => hcnNotCs ((hcsMem cn).2 (.inr (.inr hm)))
      have ha1Node : a1.get node = .element realNs tag st' mg' cs := (ha1Fr node hnodeLt).trans hget
      let ref? := if hasAnchor then some anchor else none
      let cs' := w3cInsertBeforeRef cs ref? cn
      have hrunStep : (StateT.bind (buildDomM (m := StateM (DomArena msg)) childNs newRowsL[k]) fun cn' =>
          StateT.bind (MonadDom.insertBeforeRef node ref? cn') fun _ =>
            reconcileLisBackM node childNs live sources inLis rowsArr k true cn') a =
          reconcileLisBackM (m := StateM (DomArena msg)) node childNs live sources inLis rowsArr k true cn
            (a1.set node (.element realNs tag st' mg' cs')) := by
        change (match buildDomM (m := StateM (DomArena msg)) childNs newRowsL[k] a with
          | (cn', s1) => match MonadDom.insertBeforeRef (m := StateM (DomArena msg)) node ref? cn' s1 with
            | (_, s2) => reconcileLisBackM (m := StateM (DomArena msg)) node childNs live sources inLis rowsArr k true cn' s2) = _
        rw [hbr]; simp only [DomArena.modifyChildren, DomArena.modify, ha1Node, cs']
      rw [hrunStep]
      have hcsErEq : cs.erase cn = cs := List.erase_of_not_mem hcnNotCs
      have ⟨hcs'Nd, hmemC', hcs'Filt⟩ := w3cInsertBeforeRef_reconcile_step hcsNd hanc hcnNotPl
        hcnNotMov hDisjMP hDisjLP (by rw [hcsErEq]; exact hfilt)
      have hcs'Mem : ∀ x, x ∈ cs' ↔ x ∈ filterLisNodes live sources inLis false k ∨ x ∈ filterLisNodes live sources inLis true k ∨ x ∈ cn :: placed := by
        intro x; rw [hmemC', hcsErEq, hcsMem x]; simp only [List.mem_cons]
        exact ⟨fun | .inl rfl => .inr (.inr (.inl rfl)) | .inr (.inl h) => .inl h | .inr (.inr (.inl h)) => .inr (.inl h) | .inr (.inr (.inr h)) => .inr (.inr (.inr h)),
               fun | .inl h => .inr (.inl h) | .inr (.inl h) => .inr (.inr (.inl h)) | .inr (.inr (.inl rfl)) => .inl rfl | .inr (.inr (.inr h)) => .inr (.inr (.inr h))⟩
      let a2 := a1.set node (.element realNs tag st' mg' cs')
      have hOldClean' : ∀ oi (ho : oi < oldRowsL.length), CleanDomSubtree f' childNs oldRowsL[oi] a2 (Si oi) (live.getD oi 0) :=
        fun oi ho => CleanDomSubtree_frame (fun m hm => by
          have hsub := hSiSub oi m.toNat hm
          rw [DomArena.get_set_ne _ _ (node_ne_of_toNat_ne hsub.2)]
          exact ha1Fr m (Nat.lt_of_lt_of_le (hSoldLt _ hsub.1) hbase)) (hOldClean oi ho)
      let Snew : Nat → Prop := fun m => a.nextId ≤ m ∧ m < a1.nextId
      have hSnewDisjPl : ∀ m, Snew m → Splaced m → False := fun m h1 h2 =>
        (hSpSub m h2).1.elim (fun hs => Nat.not_lt.2 h1.1 (Nat.lt_of_lt_of_le (hSoldLt m hs) hbase))
          (fun h2 => Nat.not_lt.2 h1.1 h2.2)
      have hcnClean2 : CleanDomSubtree f' childNs newRowsL[k] a2 Snew cn :=
        CleanDomSubtree_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (fun hEq => Nat.not_lt.2 hm.1 (hEq ▸ hnodeLt)))) hbuilt
      have hClPl2 : CleanDomChildren f' childNs (newRowsL.drop (k + 1)) a2 Splaced placed :=
        CleanDomChildren_frame (fun m hm => by
          have hsp := hSpSub m.toNat hm
          rw [DomArena.get_set_ne _ _ (node_ne_of_toNat_ne hsp.2)]
          exact ha1Fr m (hsp.1.elim (fun hs => Nat.lt_of_lt_of_le (hSoldLt _ hs) hbase) (·.2))) hClPl
      have hClPl' : CleanDomChildren f' childNs (newRowsL.drop k) a2 (fun m => Snew m ∨ Splaced m) (cn :: placed) := by
        rw [hdrop]; exact ⟨Snew, Splaced, fun _ => .inl, fun _ => .inr, hSnewDisjPl, hcnClean2, hClPl2⟩
      have hSpSub' : ∀ m, (Snew m ∨ Splaced m) → (Sold m ∨ (baseNext ≤ m ∧ m < a2.nextId)) ∧ m ≠ node.toNat := fun m hm =>
        hm.elim (fun ⟨h1, h2⟩ => ⟨.inr ⟨Nat.le_trans hbase h1, h2⟩, fun hEq => Nat.not_lt.2 h1 (hEq ▸ hnodeLt)⟩)
          (fun h2 => let ⟨h, hne⟩ := hSpSub m h2; ⟨h.elim .inl (fun ⟨hb, hl⟩ => .inr ⟨hb, Nat.lt_of_lt_of_le hl ha1Ge⟩), hne⟩)
      have hSpDisj' : ∀ i, i < k → ∀ oi', sources.getD i none = some oi' → ∀ m, Si oi' m → (Snew m ∨ Splaced m) → False :=
        fun i hi oi' hs' m hm1 hm2 => hm2.elim (fun h1 => Nat.not_lt.2 h1.1 (Nat.lt_of_lt_of_le (hSoldLt m (hSiSub oi' m hm1).1) hbase))
          (hSpDisj i (Nat.lt_succ_of_lt hi) oi' hs' m hm1)
      have hbdA2 : a2.nextId + htmlListNodeCount (newRowsL.take k) < UInt32.size :=
        Nat.lt_of_le_of_lt (Nat.add_le_add_right ha1Bd _)
          (by rw [Nat.add_assoc, Nat.add_comm (htmlNodeCount newRowsL[k]), ← htakeCnt]; exact hbd)
      have hres := ih hkLe true cn cs' (cn :: placed) (fun m => Snew m ∨ Splaced m) a2
        (Nat.le_trans hbase ha1Ge) (Nat.lt_of_lt_of_le hpos ha1Ge) hbdA2
        (Nat.lt_of_lt_of_le hnodeLt ha1Ge) (DomArena.get_set_self ..) hcs'Nd rfl rfl hcs'Mem hDisjML
        (fun x hm hp => (List.mem_cons.1 hp).elim (fun h => hcnNotMov (h ▸ hm)) (hDisjMP x hm))
        (fun x hl hp => (List.mem_cons.1 hp).elim (fun h => hcnNotLis (h ▸ hl)) (hDisjLP x hl))
        hcs'Filt hOldClean' hSpSub' hSpDisj' hClPl'
      dsimp only [StateT.run] at hres
      refine ⟨Nat.le_trans ha1Ge hres.1,
        Nat.le_trans hres.2.1 (by rw [htakeCnt, Nat.add_comm (htmlListNodeCount (newRowsL.take k)), ← Nat.add_assoc]; exact Nat.add_le_add_right ha1Bd _),
        fun m hmn hmLt => (hres.2.2.1 m hmn (Nat.lt_of_lt_of_le hmLt ha1Ge)).trans ((DomArena.get_set_ne _ _ hmn).trans (ha1Fr m hmLt)),
        hres.2.2.2⟩

private theorem reconcileLisBackM_spec {msg : Type} (f' : Nat) (node : Dom.Node)
    (realNs tag : String) (st' : SpecElemState msg) (mg' : List String)
    (childNs : String) (live : Array Dom.Node) (sources : Array (Option Nat))
    (inLis : Array Bool) (rowsArr : Array (Html msg)) (newRowsL : List (Html msg))
    (oldRowsL : List (Html msg)) (Si : Nat → Nat → Prop) (Sold : Nat → Prop) (baseNext : Nat)
    (_hsrcSz : sources.size = newRowsL.length)
    (hrowsArrEq : rowsArr.toList = newRowsL)
    (hliveLen : live.size = oldRowsL.length)
    (hliveNd : live.toList.Nodup)
    (hnewClean : Html.DomCleanList newRowsL = true)
    (hsrcBound : ∀ i, i < newRowsL.length → ∀ oi, sources.getD i none = some oi → oi < oldRowsL.length)
    (hsrcInj : ∀ i₁ i₂, i₁ < newRowsL.length → i₂ < newRowsL.length → ∀ oi,
      sources.getD i₁ none = some oi → sources.getD i₂ none = some oi → i₁ = i₂)
    (hsrcRow : ∀ i (hi : i < newRowsL.length) oi (ho : oi < oldRowsL.length),
      sources.getD i none = some oi → oldRowsL[oi] = newRowsL[i])
    (hSiSub : ∀ oi k, Si oi k → Sold k ∧ k ≠ node.toNat)
    (hSiDisj : ∀ oi₁ oi₂, oi₁ ≠ oi₂ → ∀ k, Si oi₁ k → Si oi₂ k → False)
    (hSoldLt : ∀ k, Sold k → k < baseNext)
    (hdep : htmlListDepth newRowsL ≤ f') :
    ∀ (k : Nat), ReconcileBackGoal f' node realNs tag st' mg' childNs live sources inLis rowsArr newRowsL oldRowsL Si Sold baseNext k := by
  have hliveInj : ∀ oi₁ oi₂, oi₁ < live.size → oi₂ < live.size → live.getD oi₁ 0 = live.getD oi₂ 0 → oi₁ = oi₂ := fun oi₁ oi₂ h1 h2 heq =>
    nodup_getElem_inj (Array.length_toList ▸ h1) (Array.length_toList ▸ h2) hliveNd
      (by simp only [Array.getD, h1, h2, ↓reduceDIte] at heq; exact heq)
  intro k
  induction k with
  | zero =>
      intro _ _ _ cs placed Splaced a _ _ _ _ hget _ _ _ _ _ _ _ hfilt _ hSpSub _ hClPl
      simp only [reconcileLisBackM, StateT.run, pure, StateT.pure, List.take_zero, htmlListNodeCount,
        Nat.add_zero, List.drop_zero] at hClPl ⊢
      have h0 : ∀ w, filterLisNodes live sources inLis w 0 = [] := fun _ => rfl
      rw [h0 false, h0 true, List.nil_append] at hfilt
      have hcsEq : cs = placed := (List.filter_eq_self.2 (fun _ _ => rfl)).symm.trans hfilt
      subst hcsEq
      exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ _ => trivial, cs, hget,
        CleanDomChildren_mono (fun m hm => hSpSub m hm) hClPl⟩
  | succ k ih =>
      intro hk hasAnchor anchor cs placed Splaced a hbase hpos hbd hnodeLt hget hcsNd hha hanc
        hcsMem hDisjML hDisjMP hDisjLP hfilt hOldClean hSpSub hSpDisj hClPl
      have hkLt : k < newRowsL.length := Nat.lt_of_succ_le hk
      have hkLe : k ≤ newRowsL.length := Nat.le_of_lt hkLt
      have htakeCnt : htmlListNodeCount (newRowsL.take (k + 1)) = htmlListNodeCount (newRowsL.take k) + htmlNodeCount newRowsL[k] := by
        rw [List.take_succ_eq_append_getElem hkLt, htmlListNodeCount_append]
        simp only [htmlListNodeCount, Nat.add_zero]
      have hbdK : a.nextId + htmlListNodeCount (newRowsL.take k) < UInt32.size :=
        Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right _ _) _) (htakeCnt ▸ hbd)
      have hdrop : newRowsL.drop k = newRowsL[k] :: newRowsL.drop (k + 1) := List.drop_eq_getElem_cons hkLt
      dsimp only [reconcileLisBackM, StateT.run, bind, StateT.bind]
      cases hsK : sources.getD k none with
      | some oi =>
          have hoi : oi < oldRowsL.length := hsrcBound k hkLt oi hsK
          let child := live.getD oi 0
          have hchildClean : CleanDomSubtree f' childNs newRowsL[k] a (Si oi) child := by
            rw [← hsrcRow k hkLt oi hoi hsK]; exact hOldClean oi hoi
          have hClPl' : CleanDomChildren f' childNs (newRowsL.drop k) a (fun m => Si oi m ∨ Splaced m) (child :: placed) := by
            rw [hdrop]; exact ⟨Si oi, Splaced, fun _ => .inl, fun _ => .inr, hSpDisj k (Nat.lt_succ_self k) oi hsK, hchildClean, hClPl⟩
          have hSpSub' : ∀ m, (Si oi m ∨ Splaced m) → (Sold m ∨ (baseNext ≤ m ∧ m < a.nextId)) ∧ m ≠ node.toNat := fun m hm =>
            hm.elim (fun h1 => ⟨.inl (hSiSub oi m h1).1, (hSiSub oi m h1).2⟩) (hSpSub m)
          have hSpDisj' : ∀ i, i < k → ∀ oi', sources.getD i none = some oi' → ∀ m, Si oi' m → (Si oi m ∨ Splaced m) → False := by
            intro i hi oi' hs' m hm1 hm2
            rcases hm2 with h2 | h2
            · exact hSiDisj oi' oi (fun he => Nat.ne_of_lt hi (hsrcInj i k (Nat.lt_trans hi hkLt) hkLt oi' hs' (he ▸ hsK))) m hm1 h2
            · exact hSpDisj i (Nat.lt_succ_of_lt hi) oi' hs' m hm1 h2
          have hchildNotF : ∀ w, child ∉ filterLisNodes live sources inLis w k := fun w hm => by
            rcases (mem_filterLisNodes ..).1 hm with ⟨i, oi', hi, _, hsi, hEq⟩
            have hoiEq := hliveInj oi' oi (hliveLen ▸ hsrcBound i (Nat.lt_trans hi hkLt) oi' hsi) (hliveLen ▸ hoi) hEq
            exact Nat.ne_of_lt hi (hsrcInj i k (Nat.lt_trans hi hkLt) hkLt oi' hsi (hoiEq ▸ hsK))
          by_cases hflK : inLis.getD k false = true
          · simp only [hflK, ↓reduceIte]
            have hmovEq : filterLisNodes live sources inLis false (k + 1) = filterLisNodes live sources inLis false k := by
              rw [filterLisNodes_succ, hflK]; simp only [beq_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.append_nil]
            have hlisEq : filterLisNodes live sources inLis true (k + 1) = filterLisNodes live sources inLis true k ++ [child] := by
              rw [filterLisNodes_succ, hflK, hsK]; simp only [beq_self_eq_true, ↓reduceIte, child]
            rw [hmovEq] at hcsMem hDisjML hDisjMP hfilt
            rw [hlisEq] at hcsMem hDisjML hDisjLP hfilt
            have hfilt' : cs.filter (fun x => !(filterLisNodes live sources inLis false k).contains x) =
                filterLisNodes live sources inLis true k ++ child :: placed := by
              rw [List.append_assoc, List.singleton_append] at hfilt; exact hfilt
            have hres := ih hkLe true child cs (child :: placed) (fun m => Si oi m ∨ Splaced m) a
              hbase hpos hbdK hnodeLt hget hcsNd rfl rfl
              (fun x => by
                rw [hcsMem x]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
                exact ⟨fun | .inl h => .inl h | .inr (.inl (.inl h)) => .inr (.inl h) | .inr (.inl (.inr rfl)) => .inr (.inr (.inl rfl)) | .inr (.inr h) => .inr (.inr (.inr h)),
                       fun | .inl h => .inl h | .inr (.inl h) => .inr (.inl (.inl h)) | .inr (.inr (.inl rfl)) => .inr (.inl (.inr rfl)) | .inr (.inr (.inr h)) => .inr (.inr h)⟩)
              (fun x hm hl => hDisjML x hm (List.mem_append_left _ hl))
              (fun x hm hp => (List.mem_cons.1 hp).elim (fun h => hchildNotF false (h ▸ hm)) (hDisjMP x hm))
              (fun x hl hp => (List.mem_cons.1 hp).elim (fun h => hchildNotF true (h ▸ hl)) (hDisjLP x (List.mem_append_left _ hl)))
              hfilt' hOldClean hSpSub' hSpDisj' hClPl'
            dsimp only [StateT.run] at hres
            exact ⟨hres.1, Nat.le_trans hres.2.1 (htakeCnt ▸ Nat.add_le_add_left (Nat.le_add_right _ _) _), hres.2.2.1, hres.2.2.2⟩
          · have hflKF : inLis.getD k false = false := Bool.eq_false_iff.2 hflK
            simp only [hflKF, Bool.false_eq_true, ↓reduceIte]
            exact reconcileLisBackM_move_step f' node realNs tag st' mg' childNs live sources inLis rowsArr newRowsL oldRowsL
              Si Sold baseNext k oi hasAnchor anchor cs placed Splaced a hSiSub ih hkLt htakeCnt hsK hflKF
              hbase hpos hbdK hnodeLt hget hcsNd hanc hcsMem hDisjML hDisjMP hDisjLP hfilt hOldClean hClPl' hSpSub' hSpDisj' hchildNotF
      | none =>
          exact reconcileLisBackM_create_step f' node realNs tag st' mg' childNs live sources inLis rowsArr newRowsL oldRowsL
            Si Sold baseNext k hasAnchor anchor cs placed Splaced a hrowsArrEq hnewClean hsrcBound hSiSub hSoldLt hdep
            ih hkLt htakeCnt hdrop hsK hbase hpos hbd hnodeLt hget hcsNd hanc hcsMem hDisjML hDisjMP hDisjLP hfilt
            hOldClean hSpSub hSpDisj hClPl

private theorem appendFragmentRowsM_spec {msg : Type} (f' : Nat) (childNs : String)
    (node : Dom.Node) (realNs tag : String) (st' : SpecElemState msg) (mg' : List String)
    (rows : List (Html msg)) (Sold : Nat → Prop) (a aBase : DomArena msg)
    (hrowsClean : Html.DomCleanList rows = true)
    (hbound : a.nextId + (1 + htmlListNodeCount rows) < UInt32.size)
    (hdep : htmlListDepth rows ≤ f') (hpos : 0 < a.nextId) (hnodeLt : node.toNat < a.nextId)
    (haBaseN : aBase.nextId = a.nextId) (haBaseNode : aBase.get node = .element realNs tag st' mg' [])
    (haBaseOut : ∀ m, m ≠ node → aBase.get m = a.get m) :
    ∃ aBuilt aOut csNew,
      buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf childNs tag)
        (aBase.alloc (.fragment [])).1 rows (aBase.alloc (.fragment [])).2 = ((), aBuilt) ∧
      MonadDom.appendChild (m := StateM (DomArena msg)) node (aBase.alloc (.fragment [])).1 aBuilt = ((), aOut) ∧
      a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + (1 + htmlListNodeCount rows) ∧
      (∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      aOut.get node = .element realNs tag st' mg' csNew ∧
      CleanDomChildren f' (Dom.childNsOf childNs tag) rows aOut
        (fun k => (Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ node.toNat) csNew := by
  let frag := UInt32.ofNat aBase.nextId
  let aFragBase : DomArena msg := { aBase with nextId := aBase.nextId + 1 }
  have hfragToNat : frag.toNat = a.nextId := by
    dsimp only [frag]; rw [haBaseN]; exact uint32_toNat_ofNat_lt a.nextId (by omega)
  have hfragNeNode : frag ≠ node := node_ne_of_toNat_ne (by rw [hfragToNat]; omega)
  have hfragRun : aBase.alloc (ArenaEntry.fragment []) = (frag, aFragBase.set frag (.fragment [])) := rfl
  have hbuilt := CleanDomChildren_of_buildDomListM (Dom.childNsOf childNs tag) rows [] aFragBase frag
    ArenaEntry.fragment (.inr fun _ => rfl) [] f' (fun _ => False) hrowsClean
    (by change frag.toNat < aBase.nextId + 1; rw [hfragToNat, haBaseN]; omega)
    (by change 0 < aBase.nextId + 1; omega)
    (by change aBase.nextId + 1 + htmlListNodeCount rows < UInt32.size; rw [haBaseN]; omega)
    hdep (fun _ h => h.elim) trivial
  dsimp only [StateT.run] at hbuilt
  rcases hbuilt with ⟨csNew, aBase', haBuiltEq, haBuiltGe, haBuiltBound, haBuiltFr, hCleanOut⟩
  simp only [List.nil_append, false_or] at haBuiltEq hCleanOut
  let aBuilt := (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf childNs tag) frag rows (aFragBase.set frag (.fragment []))).2
  have haBuiltEq' : aBuilt = aBase'.set frag (.fragment csNew) := haBuiltEq
  have haBuiltNext : a.nextId + 1 ≤ aBuilt.nextId := by
    change aFragBase.nextId ≤ aBuilt.nextId at haBuiltGe
    change aBase.nextId + 1 ≤ aBuilt.nextId at haBuiltGe; rw [← haBaseN]; exact haBuiltGe
  have haBuiltBd' : aBuilt.nextId ≤ a.nextId + (1 + htmlListNodeCount rows) := by
    change aBuilt.nextId ≤ aFragBase.nextId + htmlListNodeCount rows at haBuiltBound
    change aBuilt.nextId ≤ aBase.nextId + 1 + htmlListNodeCount rows at haBuiltBound
    rw [← haBaseN]; omega
  have haBuiltFrag : aBuilt.get frag = .fragment csNew := by rw [haBuiltEq', DomArena.get_set_self]
  have haBuiltNode : aBuilt.get node = .element realNs tag st' mg' [] := by
    rw [haBuiltFr node (by change node.toNat < aBase.nextId + 1; rw [haBaseN]; omega) hfragNeNode.symm]
    exact haBaseNode
  let aOut := (aBuilt.set frag .null).set node (.element realNs tag st' mg' csNew)
  have happendRun : MonadDom.appendChild (m := StateM (DomArena msg)) node frag aBuilt = ((), aOut) := by
    simp only [MonadDom.appendChild, haBuiltFrag, DomArena.modifyChildren, DomArena.modify,
      DomArena.get_set_ne _ _ hfragNeNode.symm, haBuiltNode, List.filter_nil, List.nil_append, aOut]
  have hbuildEq : buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf childNs tag)
      (aBase.alloc (.fragment [])).1 rows (aBase.alloc (.fragment [])).2 = ((), aBuilt) := by
    rw [hfragRun]; rfl
  have haOutNext : aOut.nextId = aBuilt.nextId := rfl
  refine ⟨aBuilt, aOut, csNew, hbuildEq, by rw [hfragRun]; exact happendRun, by omega, by omega,
    fun m hmn hmLt => ?_, DomArena.get_set_self _ _ _, ?_⟩
  · have hmf : m ≠ frag := node_ne_of_toNat_ne (by rw [hfragToNat]; omega)
    dsimp only [aOut]
    rw [DomArena.get_set_ne _ _ hmn, DomArena.get_set_ne _ _ hmf,
      haBuiltFr m (by change m.toNat < aBase.nextId + 1; rw [haBaseN]; omega) hmf]
    exact haBaseOut m hmn
  · refine CleanDomChildren_mono (fun k hk => ?_)
      (CleanDomChildren_frame (a' := aOut) (fun m hm => ?_) hCleanOut)
    · rcases hk with ⟨hk1, hk2⟩
      change aBase.nextId + 1 ≤ k at hk1; change k < aBuilt.nextId at hk2; rw [haBaseN] at hk1
      exact ⟨.inr ⟨by omega, by rw [haOutNext]; exact hk2⟩, by omega⟩
    · rcases hm with ⟨hm1, hm2⟩
      change aBase.nextId + 1 ≤ m.toNat at hm1; change m.toNat < aBuilt.nextId at hm2; rw [haBaseN] at hm1
      have hmn : m ≠ node := node_ne_of_toNat_ne (by omega)
      have hmf : m ≠ frag := node_ne_of_toNat_ne (by rw [hfragToNat]; omega)
      simp only [aOut, DomArena.get_set_ne _ _ hmn, DomArena.get_set_ne _ _ hmf]; rfl

private abbrev PatchKeyedGoal {σ msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (v : View σ msg) (s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg)
    (res : VState σ msg × DomArena msg) : Prop :=
  let (vst', a') := res
  a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render v s₂) ∧
  (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
  a'.get parent = .element pns ptag pst pmg (pre ++ vst'.rootNode :: suf) ∧ (pre ++ vst'.rootNode :: suf).Nodup ∧
  (∀ r ∈ pre ++ vst'.rootNode :: suf, r.toNat < a'.nextId) ∧
  VStateValid f childNs v s₂ a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) vst' ∧
  DomTreeAssocEquiv (readDomTree f a' vst'.rootNode) (specDom childNs (View.render v s₂))

private theorem keyedList_finish_goal {σ msg : Type} {f' : Nat} {childNs pns ptag tag inst : String}
    {parent node : Dom.Node} {pst st' : SpecElemState msg} {pmg mg' : List String}
    {attrs : List (VAttr σ msg)} {keys : σ → Array String} {marks : σ → Array USize}
    {rowSig : σ → Array String → Nat → Array (String × String)}
    {rowEv : σ → Array String → Nat → Array (String × msg)} {rowsHtml : σ → List (Html msg)}
    {s₂ : σ} {pre suf csNew : List Dom.Node} {Sold : Nat → Prop} {a aOut : DomArena msg}
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
    PatchKeyedGoal (f' + 1) childNs parent pns ptag pst pmg
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

private theorem patchViewM_keyedList_lis_spec {σ msg : Type} (f' : Nat) (childNs : String) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (tag : String) (attrs : List (VAttr σ msg)) (keys : σ → Array String)
    (marks : σ → Array USize) (rowSig : σ → Array String → Nat → Array (String × String))
    (rowEv : σ → Array String → Nat → Array (String × msg)) (rowsHtml : σ → List (Html msg))
    (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg)
    (node : Dom.Node) (oldSigs : Array (Array (String × String))) (oldMarks : Array USize) (inst : String)
    (st : SpecElemState msg) (mg : List String) (domCs : List Dom.Node)
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
    PatchKeyedGoal (f' + 1) childNs parent pns ptag pst pmg
      (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ pre suf Sold a
      ((patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
        (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂
        (.list node (disambiguateKeys (keys s₁)) oldSigs (rowsHtml s₁) oldMarks inst)).run a) := by
  have hnodeLt : node.toNat < a.nextId := hSoldLt _ hnodeMem
  let realNs := if childNs == "" && tag == "svg" then Dom.svgNs else childNs
  dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
  simp only [beq_eq_false_iff_ne.2 hrawNe, beq_eq_false_iff_ne.2 hsameNe, hnewEmp, hemp, Bool.false_eq_true, ↓reduceIte]
  let oldKeys := disambiguateKeys (keys s₁)
  let newKeys := disambiguateKeys (keys s₂)
  have holdNd : oldKeys.toList.Nodup := disambiguateKeys_nodup (keys s₁)
  have hnewNd : newKeys.toList.Nodup := disambiguateKeys_nodup (keys s₂)
  have hidxSpec := buildKeyIndex_spec oldKeys holdNd
  let oldBuckets := (buildKeyIndex oldKeys).1
  let mask := (buildKeyIndex oldKeys).2
  have hidxBnd : ∀ k oi, keyIndexGet oldBuckets mask k = some oi → oi < oldKeys.size :=
    fun k oi hq => (hidxSpec.1 k oi hq).1
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
  let sources := plan.1
  let used := plan.2.1
  let rowsArr := plan.2.2.1
  let marksArr := plan.2.2.2.1
  let sigsArr := plan.2.2.2.2
  have hrowsArrEq : rowsArr.toList = rowsHtml s₂ := by
    have hpref : (rowsHtml s₂).map (Html.prefixSignals inst) = rowsHtml s₂ :=
      Html.map_prefixSignals_of_DomCleanList inst (hrowsClean.2.1 s₂)
    refine List.ext_getElem? fun i => ?_
    rw [Array.getElem?_toList]
    by_cases hi : i < newKeys.size
    · have hri : i < (rowsHtml s₂).length := by rw [hrowsClean.1 s₂]; exact hi
      rw [hplanSpec.2.2.2.2.2 i hi]
      cases hq : keyIndexGet oldBuckets mask newKeys[i] with
      | none =>
          have hszF : (rowsHtml s₂).toArray.size = (rowsHtml s₂).length := List.size_toArray ..
          simp only [freshFn, hpref, Array.getD, hszF, hri, ↓reduceDIte]
          rw [List.getElem?_eq_getElem hri]; rfl
      | some oi =>
          have ⟨hoiK, hkeyEq?⟩ := hidxSpec.1 _ oi hq
          have hoi1 : oi < (rowsHtml s₁).length := by rw [hrowsClean.1 s₁]; exact hoiK
          have hkeyEq : oldKeys[oi]'hoiK = newKeys[i]'hi := by
            rw [Array.getElem?_eq_getElem hoiK, Option.some.injEq] at hkeyEq?; exact hkeyEq?
          have hrowEq := hrowsClean.2.2.2 s₁ s₂ oi i hoiK hi hkeyEq
          have hget1 : (rowsHtml s₁).toArray.getD oi default = (rowsHtml s₁)[oi] := by
            simp only [Array.getD, List.size_toArray, hoi1, ↓reduceDIte]; rfl
          dsimp only; rw [hget1, ← List.getElem?_eq_getElem hoi1, hrowEq]
    · have h1 : rowsArr.size ≤ i := hplanSpec.2.2.1.symm ▸ Nat.not_lt.1 hi
      have h2 : (rowsHtml s₂).length ≤ i := (hrowsClean.1 s₂).symm ▸ Nat.not_lt.1 hi
      rw [Array.getElem?_eq_none h1, List.getElem?_eq_none h2]
  have hsrcSz : sources.size = (rowsHtml s₂).length := by rw [hplanSpec.1, hrowsClean.1 s₂]
  have hsrcGet : ∀ i (hi : i < newKeys.size), sources.getD i none = keyIndexGet oldBuckets mask newKeys[i] := by
    intro i hi
    have hiS : i < sources.size := hplanSpec.1 ▸ hi
    have h1 := hplanSpec.2.2.2.1 i hi
    rw [Array.getElem?_eq_getElem hiS, Option.some.injEq] at h1
    simp only [Array.getD, hiS, ↓reduceDIte]; exact h1
  have hsrcBound : ∀ i, i < (rowsHtml s₂).length → ∀ oi, sources.getD i none = some oi → oi < (rowsHtml s₁).length := by
    intro i hi oi hsi
    have hiK : i < newKeys.size := (hrowsClean.1 s₂) ▸ hi
    rw [hsrcGet i hiK] at hsi; rw [hrowsClean.1 s₁]; exact hidxBnd _ oi hsi
  have hsrcInj : ∀ i₁ i₂, i₁ < (rowsHtml s₂).length → i₂ < (rowsHtml s₂).length →
      ∀ oi, sources.getD i₁ none = some oi → sources.getD i₂ none = some oi → i₁ = i₂ := by
    intro i₁ i₂ h1 h2 oi hs1 hs2
    have h1K : i₁ < newKeys.size := (hrowsClean.1 s₂) ▸ h1
    have h2K : i₂ < newKeys.size := (hrowsClean.1 s₂) ▸ h2
    rw [hsrcGet i₁ h1K] at hs1; rw [hsrcGet i₂ h2K] at hs2
    have hkeyEq : newKeys[i₁]'h1K = newKeys[i₂]'h2K := Option.some.inj ((hidxSpec.1 _ oi hs1).2.symm.trans (hidxSpec.1 _ oi hs2).2)
    exact nodup_getElem_inj (Array.length_toList ▸ h1K) (Array.length_toList ▸ h2K) hnewNd hkeyEq
  have hsrcRow : ∀ i (hi : i < (rowsHtml s₂).length) oi (ho : oi < (rowsHtml s₁).length),
      sources.getD i none = some oi → (rowsHtml s₁)[oi] = (rowsHtml s₂)[i] := by
    intro i hi oi ho hsi
    have hiK : i < newKeys.size := (hrowsClean.1 s₂) ▸ hi
    have hoK : oi < oldKeys.size := (hrowsClean.1 s₁) ▸ ho
    rw [hsrcGet i hiK] at hsi
    have hkeyEq? := (hidxSpec.1 _ oi hsi).2
    have hkeyEq : oldKeys[oi]'hoK = newKeys[i]'hiK := by
      rw [Array.getElem?_eq_getElem hoK, Option.some.injEq] at hkeyEq?; exact hkeyEq?
    have hrowEq := hrowsClean.2.2.2 s₁ s₂ oi i hoK hiK hkeyEq
    rw [List.getElem?_eq_getElem ho, List.getElem?_eq_getElem hi, Option.some.injEq] at hrowEq
    exact hrowEq
  have hseed0 := seedRowsM_sameDom inst (rowSig s₂ newKeys) (rowEv s₂ newKeys) (marks s₂) marksArr sigsArr a
  dsimp only [StateT.run] at hseed0
  dsimp only [StateT.bind, StateT.pure, bind, pure]
  cases hsRun : seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ newKeys) (rowEv s₂ newKeys) (marks s₂) marksArr sigsArr a with
  | mk newSigs aSeed =>
      rw [hsRun] at hseed0; dsimp only at hseed0 ⊢
      have haSet := DomArena.set_get_self aSeed ((hseed0.get_eq node).trans hnodeGet)
      have hdyn := applyDynAttrsM_spec aSeed node realNs tag st mg domCs attrs s₁ s₂ haClean hElClean hElEq hmg
      rw [haSet] at hdyn
      rcases hdyn with ⟨ha1Next, ha1Ne, st', mg', ha1Get, hElClean', hElEq', hmg'⟩
      let a1 := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ aSeed).2
      have ha1Eq : applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ aSeed = ((), a1) := rfl
      have ha1N : a1.nextId = a.nextId := ha1Next.trans hseed0.1
      have ha1Out : ∀ m, m ≠ node → a1.get m = a.get m := fun m hm => (ha1Ne m hm).trans (hseed0.get_eq m)
      have hcnV : childNs = "" ∨ childNs = Dom.svgNs := by rw [hchildNs]; split; exact .inr rfl; exact .inl rfl
      have hccNs := childNamespace_eq_childNsOf (ptag := tag) hcnV
      rw [ha1Eq]; dsimp only
      rw [ha1Get]; dsimp only [realNs]; rw [hccNs]
      split
      · dsimp only [StateT.bind, StateT.pure, bind, pure]
        change PatchKeyedGoal _ _ _ _ _ _ _ _ _ _ _ _ _
          (match buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf childNs tag)
              ((a1.modifyChildren node fun _ => []).alloc (.fragment [])).1 rowsArr.toList
              ((a1.modifyChildren node fun _ => []).alloc (.fragment [])).2 with
            | (_, s2) => match MonadDom.appendChild (m := StateM (DomArena msg)) node ((a1.modifyChildren node fun _ => []).alloc (.fragment [])).1 s2 with
              | (_, s3) => (VState.list (σ := σ) node newKeys newSigs rowsArr.toList (marks s₂) inst, s3))
        let aClr := a1.set node (.element realNs tag st' mg' [])
        have hclr : a1.modifyChildren node (fun _ => []) = aClr := by
          dsimp only [DomArena.modifyChildren, DomArena.modify, aClr]; rw [ha1Get]
        rw [hclr, hrowsArrEq]
        simp only [View.render, htmlNodeCount] at hbound; simp only [View.render, htmlDepth] at hdep
        have hdepF : htmlListDepth (rowsHtml s₂) ≤ f' := by rw [Nat.add_comm] at hdep; exact Nat.le_of_succ_le_succ hdep
        rcases appendFragmentRowsM_spec f' childNs node realNs tag st' mg' (rowsHtml s₂) Sold a aClr
          (hrowsClean.2.1 s₂) hbound hdepF hpos hnodeLt ha1N (DomArena.get_set_self _ _ _)
          (fun m hm => (DomArena.get_set_ne _ _ hm).trans (ha1Out m hm)) with
          ⟨aBuilt, aOut, csNew, hbuild, happ, haOutGe, haOutBd, haOutFr, haOutNode, hCleanOut'⟩
        rw [hbuild]; dsimp only; rw [happ]
        exact keyedList_finish_goal haClean hparLt hpar hnd hparOut hparNodes hnodeMem
          haOutGe haOutBd haOutFr haOutNode hElClean' hElEq' hmg' hCleanOut' rfl rfl
      · have ⟨hdomNd, hdomLen⟩ := CleanDomChildren_nodup hCleanCs
        have hdomLtU32 : domCs.length < UInt32.size := by
          have hle : domCs.length ≤ a.nextId :=
            nodup_nodes_lt_length_le a.nextId domCs hdomNd fun x hx =>
              hSoldLt _ (CleanDomChildren_mem hCleanCs x hx).1
          exact Nat.lt_of_le_of_lt hle (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hbound)
        have hcountNat : (UInt32.ofNat domCs.length).toNat = domCs.length := uint32_toNat_ofNat_lt domCs.length hdomLtU32
        have hsnap := snapshotChildrenM_spec a1 node realNs tag st' mg' domCs hdomLtU32 0 domCs.length #[] (Nat.zero_add _)
        rw [DomArena.set_get_self a1 ha1Get] at hsnap
        dsimp only [StateT.run, List.nil_append, List.drop_zero] at hsnap
        let live : Array Dom.Node := ⟨domCs⟩
        have hliveSz : live.size = (rowsHtml s₁).length := hdomLen
        have hremSpec := removeUnusedM_spec node realNs tag st' mg' live used 0 [] a1 (Nat.zero_le _) hdomNd ha1Get
        let aRem := (removeUnusedM (m := StateM (DomArena msg)) node live used 0).run a1 |>.2
        have haRemEq : removeUnusedM (m := StateM (DomArena msg)) node live used 0 a1 = ((), aRem) := rfl
        have haRemN : aRem.nextId = a.nextId := hremSpec.1.trans ha1N
        have haRemOut : ∀ m, m ≠ node → aRem.get m = a.get m := fun m hm => (hremSpec.2.1 m hm).trans (ha1Out m hm)
        let kept := (List.range live.size).filterMap fun oi => if used.getD oi false then some (live.getD oi 0) else none
        have haRemNode : aRem.get node = .element realNs tag st' mg' kept := by
          have h := hremSpec.2.2; simp only [List.nil_append, Nat.zero_add, Nat.sub_zero] at h; exact h
        let inLis := verifiedLisFlags sources
        have hlisSpec := verifiedLisFlags_spec sources
        have hkeptSpec := lis_filter_kept_eq live sources inLis used (rowsHtml s₂).length hsrcSz
          (by rw [hplanSpec.2.1, hliveSz, hrowsClean.1 s₁])
          (fun i hi oi hsi => hliveSz.symm ▸ hsrcBound i hi oi hsi)
          hsrcInj
          (fun oi ho => by
            have hoK : oi < oldKeys.size := (hrowsClean.1 s₁) ▸ hliveSz ▸ ho
            have hszEq : newKeys.size = (rowsHtml s₂).length := (hrowsClean.1 s₂).symm
            rw [← hszEq]; exact hplanSpec.2.2.2.2.1 oi hoK)
          hdomNd
          (fun i hi hf => hlisSpec.1 i (hsrcSz.symm ▸ hi) hf)
          (fun i₁ i₂ h1 h2 hf1 hf2 oi₁ oi₂ hs1 hs2 => hlisSpec.2 i₁ i₂ h1 (hsrcSz.symm ▸ h2) hf1 hf2 oi₁ oi₂ hs1 hs2)
        rcases CleanDomChildren_indexed hCleanCs with ⟨Si, hSiSub, hSiDisj, hSiGet⟩
        have hOldCleanRem : ∀ oi (ho : oi < (rowsHtml s₁).length),
            CleanDomSubtree f' (Dom.childNsOf childNs tag) (rowsHtml s₁)[oi] aRem (Si oi) (live.getD oi 0) := by
          intro oi ho
          have hoD : oi < domCs.length := hdomLen ▸ ho
          have hgl : live.getD oi 0 = domCs[oi] := by rw [Array.getD, dif_pos (show oi < live.size from hoD)]; rfl
          rw [hgl]
          exact CleanDomSubtree_frame (fun m hm => haRemOut m (node_ne_of_toNat_ne (hSiSub oi m.toNat hm).2)) (hSiGet oi ho hoD)
        simp only [View.render, htmlNodeCount] at hbound; simp only [View.render, htmlDepth] at hdep
        have hdepF : htmlListDepth (rowsHtml s₂) ≤ f' := by rw [Nat.add_comm] at hdep; exact Nat.le_of_succ_le_succ hdep
        have hbdRem : aRem.nextId + htmlListNodeCount ((rowsHtml s₂).take (rowsHtml s₂).length) < UInt32.size := by
          rw [haRemN, List.take_length]
          exact Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left _ 1) _) hbound
        have hrec := reconcileLisBackM_spec f' node realNs tag st' mg' (Dom.childNsOf childNs tag)
          live sources inLis rowsArr (rowsHtml s₂) (rowsHtml s₁) Si Sold a.nextId
          hsrcSz hrowsArrEq hliveSz hdomNd (hrowsClean.2.1 s₂)
          hsrcBound hsrcInj hsrcRow hSiSub hSiDisj hSoldLt hdepF
          (rowsHtml s₂).length (Nat.le_refl _) false 0 kept [] (fun _ => False) aRem
          (haRemN ▸ Nat.le_refl _) (haRemN ▸ hpos) hbdRem (haRemN ▸ hnodeLt)
          haRemNode hkeptSpec.1 rfl rfl (fun x => by rw [hkeptSpec.2.1 x]; simp only [List.not_mem_nil, or_false])
          hkeptSpec.2.2.1 (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
          (by rw [List.append_nil]; exact hkeptSpec.2.2.2) hOldCleanRem
          (fun _ h => h.elim) (fun _ _ _ _ _ _ h => h.elim) (by rw [List.drop_length]; trivial)
        have hnewKeysSzEq : newKeys.size = (rowsHtml s₂).length := (hrowsClean.1 s₂).symm
        dsimp only [StateT.bind, StateT.pure, bind, pure]
        change PatchKeyedGoal _ _ _ _ _ _ _ _ _ _ _ _ _
          (match MonadDom.childCount (m := StateM (DomArena msg)) node a1 with
            | (oc, s3) => match snapshotChildrenM (m := StateM (DomArena msg)) node 0 #[] oc.toNat s3 with
              | (lv, s4) => match removeUnusedM (m := StateM (DomArena msg)) node lv used 0 s4 with
                | (_, s5) => match reconcileLisBackM (m := StateM (DomArena msg)) node (Dom.childNsOf childNs tag) lv sources inLis rowsArr newKeys.size false 0 s5 with
                  | (_, s6) => (VState.list (σ := σ) node newKeys newSigs rowsArr.toList (marks s₂) inst, s6))
        dsimp only [MonadDom.childCount]; rw [ha1Get]; dsimp only; rw [hcountNat, hsnap]; dsimp only
        rw [haRemEq]; dsimp only; rw [hnewKeysSzEq]
        cases hrecRun : reconcileLisBackM (m := StateM (DomArena msg)) node (Dom.childNsOf childNs tag) live sources inLis rowsArr (rowsHtml s₂).length false 0 aRem with
        | mk _ aOut =>
            dsimp only [StateT.run] at hrec; rw [hrecRun] at hrec; dsimp only at hrec ⊢
            rcases hrec with ⟨haOutGe, haOutBd, haOutFr, finalCs, haOutNode, hCleanOut⟩
            rw [haRemN] at haOutGe haOutBd haOutFr
            rw [List.take_length] at haOutBd
            rw [hrowsArrEq]
            exact keyedList_finish_goal haClean hparLt hpar hnd hparOut hparNodes hnodeMem
              haOutGe (Nat.le_trans haOutBd (Nat.add_le_add_left (Nat.le_add_left _ 1) _))
              (fun m hmn hmLt => (haOutFr m hmn hmLt).trans (haRemOut m hmn))
              haOutNode hElClean' hElEq' hmg' hCleanOut rfl rfl

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
    let (vst', a') := (patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
      (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂ vst).run a
    a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂) ∧
    (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
    a'.get parent = .element pns ptag pst pmg (pre ++ vst'.rootNode :: suf) ∧ (pre ++ vst'.rootNode :: suf).Nodup ∧
    (∀ r ∈ pre ++ vst'.rootNode :: suf, r.toNat < a'.nextId) ∧
    VStateValid f childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂ a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) vst' ∧
    DomTreeAssocEquiv (readDomTree f a' vst'.rootNode) (specDom childNs (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂)) := by
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
          have hnodeLt : node.toNat < a.nextId := hSoldLt _ hnodeMem
          let realNs := if childNs == "" && tag == "svg" then Dom.svgNs else childNs
          have hdyn := applyDynAttrsM_spec a node realNs tag st mg domCs attrs s₁ s₂ haClean hElClean hElEq hmg
          rw [DomArena.set_get_self a hnodeGet] at hdyn
          rcases hdyn with ⟨ha1Next, ha1Ne, st', mg', ha1Get, hElClean', hElEq', hmg'⟩
          let a1 := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a).2
          have ha1Eq : applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a = ((), a1) := rfl
          dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
          have hSameKeysBranch : ∀ (hsameK : disambiguateKeys (keys s₂) = disambiguateKeys (keys s₁)),
              PatchKeyedGoal (f' + 1) childNs parent pns ptag pst pmg
                (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ pre suf Sold a
                ((StateT.bind (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂) fun _ =>
                  StateT.bind (seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ (disambiguateKeys (keys s₁))) (rowEv s₂ (disambiguateKeys (keys s₁))) (marks s₂) oldMarks oldSigs) fun newSigs =>
                    StateT.pure (VState.list node (disambiguateKeys (keys s₁)) newSigs (rowsHtml s₁) (marks s₂) inst)) a) := by
            intro hsameK
            have hseed := seedRowsM_sameDom inst (rowSig s₂ (disambiguateKeys (keys s₁))) (rowEv s₂ (disambiguateKeys (keys s₁))) (marks s₂) oldMarks oldSigs a1
            dsimp only [StateT.run] at hseed
            dsimp only [StateT.bind, StateT.pure, bind, pure]
            rw [ha1Eq]; dsimp only
            cases hsRun : seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ (disambiguateKeys (keys s₁))) (rowEv s₂ (disambiguateKeys (keys s₁))) (marks s₂) oldMarks oldSigs a1 with
            | mk newSigs aOut =>
                rw [hsRun] at hseed; dsimp only at hseed ⊢
                have haOutNext : aOut.nextId = a.nextId := hseed.1.trans ha1Next
                have haOutOutside : ∀ m, m ≠ node → aOut.get m = a.get m := fun m hm =>
                  (hseed.get_eq m).trans (ha1Ne m hm)
                have hrowsEq : rowsHtml s₁ = rowsHtml s₂ := keyedRows_eq_of_keys_eq hrowsClean hsameK
                have hCleanCsOut := CleanDomChildren_frame (fun m hm => haOutOutside m (node_ne_of_toNat_ne hm.2)) hCleanCs
                exact keyedList_finish_goal haClean hparLt hpar hnd hparOut hparNodes hnodeMem
                  (by omega) (by omega) (fun m hm _ => haOutOutside m hm)
                  ((hseed.get_eq node).trans ha1Get) hElClean' hElEq' hmg'
                  (by rw [← hrowsEq]; exact CleanDomChildren_mono (fun k hk => ⟨.inl hk.1, hk.2⟩) hCleanCsOut)
                  hsameK.symm hrowsEq
          by_cases hrawEq : keys s₂ = disambiguateKeys (keys s₁)
          · simp only [beq_iff_eq.2 hrawEq, ↓reduceIte]
            exact hSameKeysBranch ((disambiguateKeys_of_nodup (hrawEq ▸ disambiguateKeys_nodup (keys s₁))).trans hrawEq)
          · have hbRaw : (keys s₂ == disambiguateKeys (keys s₁)) = false := beq_eq_false_iff_ne.2 hrawEq
            simp only [hbRaw, Bool.false_eq_true, ↓reduceIte]
            by_cases hsameK : disambiguateKeys (keys s₂) = disambiguateKeys (keys s₁)
            · simp only [beq_iff_eq.2 hsameK, ↓reduceIte]
              exact hSameKeysBranch hsameK
            · simp only [beq_eq_false_iff_ne.2 hsameK, Bool.false_eq_true, ↓reduceIte]
              cases hnewEmp : (disambiguateKeys (keys s₂)).isEmpty
              · simp only [Bool.false_eq_true, ↓reduceIte]
                cases hemp : (rowsHtml s₁).isEmpty
                · -- Non-empty → Non-empty: verified certifying `O(N log N)` LIS minimal-moves reconciler
                  have hlis := patchViewM_keyedList_lis_spec f' childNs parent pns ptag pst pmg tag attrs keys marks
                    rowSig rowEv rowsHtml s₁ s₂ pre suf Sold a node oldSigs oldMarks inst st mg domCs
                    hchildNs haClean hrowsClean hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes
                    hnodeMem hnodeGet hElClean hElEq hmg hCleanCs hrawEq hsameK hnewEmp hemp
                  dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure] at hlis
                  simp only [hbRaw, beq_eq_false_iff_ne.2 hsameK, hnewEmp, hemp, Bool.false_eq_true, ↓reduceIte] at hlis ⊢
                  exact hlis
                · -- `oldRowsL.isEmpty = true`: fast create via DocumentFragment
                  simp only [↓reduceIte]
                  have hnilRows : rowsHtml s₁ = [] := List.isEmpty_iff.1 hemp
                  have hnilDom : domCs = [] := by
                    rw [hnilRows] at hCleanCs
                    cases domCs with | nil => rfl | cons _ _ => exact False.elim hCleanCs
                  have hseed := seedRowsM_sameDom inst (rowSig s₂ (disambiguateKeys (keys s₂))) (rowEv s₂ (disambiguateKeys (keys s₂))) (marks s₂) #[] #[] a1
                  dsimp only [StateT.run] at hseed
                  dsimp only [StateT.bind, StateT.pure, bind, pure]
                  rw [ha1Eq]; dsimp only
                  cases hsRun : seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ (disambiguateKeys (keys s₂))) (rowEv s₂ (disambiguateKeys (keys s₂))) (marks s₂) #[] #[] a1 with
                  | mk newSigs aSeed =>
                      rw [hsRun] at hseed; dsimp only at hseed ⊢
                      have haSeedN : aSeed.nextId = a.nextId := hseed.1.trans ha1Next
                      have haSeedNode : aSeed.get node = .element realNs tag st' mg' [] := by
                        rw [hseed.get_eq node, ha1Get, hnilDom]
                      have haSeedOut : ∀ m, m ≠ node → aSeed.get m = a.get m := fun m hm => (hseed.get_eq m).trans (ha1Ne m hm)
                      rw [Html.map_prefixSignals_of_DomCleanList inst (hrowsClean.2.1 s₂)]
                      have hcnV : childNs = "" ∨ childNs = Dom.svgNs := by rw [hchildNs]; split <;> simp
                      rw [haSeedNode]; dsimp only [realNs]; rw [childNamespace_eq_childNsOf (ptag := tag) hcnV]
                      simp only [View.render, htmlNodeCount] at hbound; simp only [View.render, htmlDepth] at hdep
                      rcases appendFragmentRowsM_spec f' childNs node realNs tag st' mg' (rowsHtml s₂) Sold a aSeed
                        (hrowsClean.2.1 s₂) hbound (by omega) hpos hnodeLt haSeedN haSeedNode haSeedOut with
                        ⟨aBuilt, aOut, csNew, hbuild, happ, haOutGe, haOutBd, haOutFr, haOutNode, hCleanOut'⟩
                      rw [hbuild]; dsimp only; rw [happ]; dsimp only
                      exact keyedList_finish_goal haClean hparLt hpar hnd hparOut hparNodes hnodeMem
                        haOutGe (by omega) haOutFr haOutNode hElClean' hElEq' hmg' hCleanOut' rfl rfl
              · -- `newKeys.isEmpty = true`: fast `clearChildren`
                simp only [↓reduceIte, StateT.bind, StateT.pure]
                have hnewKeysEq : disambiguateKeys (keys s₂) = #[] := Array.isEmpty_iff.1 hnewEmp
                have hnewRows0 : rowsHtml s₂ = [] := List.eq_nil_of_length_eq_zero (by rw [hrowsClean.1 s₂, hnewKeysEq]; rfl)
                rw [ha1Eq]; dsimp only
                let aOut := a1.set node (.element realNs tag st' mg' [])
                have hclr : MonadDom.clearChildren (m := StateM (DomArena msg)) node a1 = ((), aOut) := by
                  dsimp only [MonadDom.clearChildren, DomArena.modifyChildren, DomArena.modify, aOut]; rw [ha1Get]
                rw [hclr]; dsimp only
                have haOutNext : aOut.nextId = a.nextId := ha1Next
                exact keyedList_finish_goal haClean hparLt hpar hnd hparOut hparNodes hnodeMem
                  (by omega) (by omega) (fun m hm _ => (DomArena.get_set_ne _ _ hm).trans (ha1Ne m hm))
                  (DomArena.get_set_self _ _ _) hElClean' hElEq' hmg'
                  (by rw [hnewRows0]; trivial) hnewKeysEq.symm hnewRows0.symm
  | _ => exact False.elim hval.2

end Qed
