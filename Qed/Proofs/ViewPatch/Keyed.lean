import Qed.Proofs.ViewPatch.VState

namespace Qed

section
variable {msg : Type}

/-! ## Verified Bare-Array Index & Certifying `O(N log N)` LIS Keyed Reconciler -/

private def KeyIdxInv (buckets : Array (List (String × Nat))) (mask : USize) (keys : Array String) (bound : Nat) : Prop :=
  0 < buckets.size ∧ (∀ k oi, keyIndexGet buckets mask k = some oi → oi < bound ∧ keys[oi]? = some k) ∧
  (∀ oi, oi < bound → ∀ k, keys[oi]? = some k → keyIndexGet buckets mask k = some oi)

private abbrev PlanKeyedOut (newKeys : Array String) (oldBuckets : Array (List (String × Nat))) (mask : USize)
    (oldRows : Array (Html msg)) (fresh : Unit → Array (Html msg)) (oldLen : Nat)
    (res : Array (Option Nat) × Array Bool × Array (Html msg) × Array USize × Array (Array (String × String))) : Prop :=
  res.1.size = newKeys.size ∧ res.2.1.size = oldLen ∧ res.2.2.1.size = newKeys.size ∧
  (∀ j (hj : j < newKeys.size), res.1.getD j none = keyIndexGet oldBuckets mask newKeys[j]) ∧
  (∀ oi, oi < oldLen → (res.2.1.getD oi false = true ↔ ∃ j, ∃ _ : j < newKeys.size, res.1.getD j none = some oi)) ∧
  (∀ j (hj : j < newKeys.size), res.2.2.1[j]? = some (match keyIndexGet oldBuckets mask newKeys[j] with | some oi => oldRows.getD oi default | none => (fresh ()).getD j default))

private def filterLisNodes (live : Array Dom.Node) (sources : Array (Option Nat)) (inLis : Array Bool) (want : Bool) (k : Nat) : List Dom.Node :=
  (List.range k).filterMap fun i => if inLis.getD i false == want then (sources.getD i none).map (live.getD · 0) else none

private structure LisBackCtx (f' : Nat) (node : Dom.Node) (live : Array Dom.Node) (sources : Array (Option Nat))
    (rowsArr : Array (Html msg)) (newRowsL oldRowsL : List (Html msg)) (Si : Nat → Nat → Prop) (Sold : Nat → Prop) (baseNext : Nat) : Prop where
  hrows : rowsArr.toList = newRowsL ∧ live.size = oldRowsL.length ∧ live.toList.Nodup ∧ Html.DomCleanList newRowsL = true ∧ htmlListDepth newRowsL ≤ f'
  hsrcBound : ∀ i, i < newRowsL.length → ∀ oi, sources.getD i none = some oi → oi < oldRowsL.length
  hsrcInj : ∀ i₁ i₂, i₁ < newRowsL.length → i₂ < newRowsL.length → ∀ oi, sources.getD i₁ none = some oi → sources.getD i₂ none = some oi → i₁ = i₂
  hsrcRow : ∀ i (hi : i < newRowsL.length) oi (ho : oi < oldRowsL.length), sources.getD i none = some oi → oldRowsL[oi] = newRowsL[i]
  hSi : (∀ oi k, Si oi k → Sold k ∧ k ≠ node.toNat) ∧ (∀ oi₁ oi₂, oi₁ ≠ oi₂ → ∀ k, Si oi₁ k → Si oi₂ k → False) ∧ (∀ k, Sold k → k < baseNext)

private abbrev ReconcileBackOut (en : ElemPar msg) (newRowsL : List (Html msg)) (Sold : Nat → Prop) (baseNext k : Nat) (a aOut : DomArena msg) : Prop :=
  ArenaExt a aOut (· = en.parent.toNat) (htmlListNodeCount (newRowsL.take k)) ∧
  ∃ finalCs, aOut.get en.parent = en.entry finalCs ∧
    CleanDomChildren en.f en.childNs newRowsL aOut (fun m => (Sold m ∨ (baseNext ≤ m ∧ m < aOut.nextId)) ∧ m ≠ en.parent.toNat) finalCs

private structure LisBackInv (en : ElemPar msg) (live : Array Dom.Node) (sources : Array (Option Nat)) (inLis : Array Bool)
    (newRowsL oldRowsL : List (Html msg)) (Si : Nat → Nat → Prop) (Sold : Nat → Prop) (baseNext k : Nat)
    (hasAnchor : Bool) (anchor : Dom.Node) (cs placed : List Dom.Node) (Splaced : Nat → Prop) (a : DomArena msg) : Prop where
  hbnd : baseNext ≤ a.nextId ∧ 0 < a.nextId ∧ a.nextId + htmlListNodeCount (newRowsL.take k) < UInt32.size ∧ en.parent.toNat < a.nextId
  hget : a.get en.parent = en.entry cs ∧ cs.Nodup
  hanc : hasAnchor = !placed.isEmpty ∧ (if hasAnchor then some anchor else none) = placed.head?
  hcsMem : ∀ x, x ∈ cs ↔ x ∈ filterLisNodes live sources inLis false k ∨ x ∈ filterLisNodes live sources inLis true k ∨ x ∈ placed
  hDisj : (∀ x, x ∈ filterLisNodes live sources inLis false k → x ∈ filterLisNodes live sources inLis true k → False) ∧
    (∀ x, x ∈ filterLisNodes live sources inLis false k → x ∈ placed → False) ∧ (∀ x, x ∈ filterLisNodes live sources inLis true k → x ∈ placed → False)
  hfilt : cs.filter (fun x => !(filterLisNodes live sources inLis false k).contains x) = filterLisNodes live sources inLis true k ++ placed
  hOldClean : ∀ oi (ho : oi < oldRowsL.length), CleanDomSubtree en.f en.childNs oldRowsL[oi] a (Si oi) (live.getD oi 0)
  hSp : (∀ m, Splaced m → (Sold m ∨ (baseNext ≤ m ∧ m < a.nextId)) ∧ m ≠ en.parent.toNat) ∧
    (∀ i, i < k → ∀ oi, sources.getD i none = some oi → ∀ m, Si oi m → Splaced m → False)
  hClPl : CleanDomChildren en.f en.childNs (newRowsL.drop k) a Splaced placed

private structure KeyedPatchCtx {σ : Type} (ep : ElemPar msg) (tag : String) (node : Dom.Node)
    (attrs : List (VAttr σ msg)) (keys : σ → Array String) (rowsHtml : σ → List (Html msg)) (s₁ s₂ : σ) (pre suf : List Dom.Node)
    (Sold : Nat → Prop) (a : DomArena msg) (st : SpecElemState msg) (mg : List String) (domCs : List Dom.Node) : Prop where
  hclean : ep.childNsOk ∧ VAttrListClean attrs ∧ KeyedRowsClean keys rowsHtml
  hbnd : a.nextId + (1 + htmlListNodeCount (rowsHtml s₂)) < UInt32.size ∧ htmlListDepth (rowsHtml s₂) ≤ ep.f ∧ ep.parent.toNat < a.nextId ∧ 0 < a.nextId
  hpar : a.get ep.parent = ep.entry (pre ++ node :: suf) ∧ (pre ++ node :: suf).Nodup ∧ ¬Sold ep.parent.toNat ∧ (∀ k, Sold k → k < a.nextId) ∧ (∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId)
  hnode : Sold node.toNat ∧ a.get node = .element (if ep.childNs == "" && tag == "svg" then Dom.svgNs else ep.childNs) tag st mg domCs ∧ DynAttrsOk attrs s₁ st mg ∧ CleanDomChildren ep.f (Dom.childNsOf ep.childNs tag) (rowsHtml s₁) a (fun k => Sold k ∧ k ≠ node.toNat) domCs

private theorem htmlListNodeCount_append : ∀ (xs ys : List (Html msg)), htmlListNodeCount (xs ++ ys) = htmlListNodeCount xs + htmlListNodeCount ys
  | [], _ => (Nat.zero_add _).symm | _ :: xs, ys => by simp only [List.cons_append, htmlListNodeCount, htmlListNodeCount_append xs ys, Nat.add_assoc]
private theorem buildKeyIndexLoop_spec (keys : Array String) (mask : USize) (hnd : keys.toList.Nodup) (i : Nat) (hle : i ≤ keys.size) :
    ∀ buckets, KeyIdxInv buckets mask keys i → KeyIdxInv (buildKeyIndexLoop keys i buckets mask) mask keys keys.size := by
  induction i, hle using down_ind with
  | base => intro buckets hinv; unfold buildKeyIndexLoop; simp [hinv]
  | step i hlt ih =>
      intro buckets hinv; unfold buildKeyIndexLoop; simp only [hlt, ↓reduceDIte, hinv.1]
      let k := keys[i]; let bi := strBucketIdx k mask buckets.size; have hbi := strBucketIdx_lt k mask buckets.size hinv.1
      let buckets' := buckets.set bi ((k, i) :: buckets[bi]) hbi; have hsz' : buckets'.size = buckets.size := Array.size_set ..
      have hget' (s : String) : keyIndexGet buckets' mask s = if s == k then some i else keyIndexGet buckets mask s := by
        unfold keyIndexGet; simp only [hinv.1, ↓reduceDIte, buckets', hsz', Array.getElem_set]
        by_cases hbiS : bi = strBucketIdx s mask buckets.size
        · simp only [hbiS, ↓reduceIte, kpLookupList]; by_cases hks : k = s <;> simp [hks, Ne.symm]
        · simp only [hbiS, beq_eq_false_iff_ne.2 (show s ≠ k from fun h => hbiS (h ▸ rfl)), Bool.false_eq_true, ↓reduceIte]
      refine ih buckets' ⟨hsz'.symm ▸ hinv.1, fun s oi hq => ?_, fun oi hoi s hs => ?_⟩
      · rw [hget'] at hq; by_cases hsk : (s == k) = true
        · simp only [hsk, ↓reduceIte, Option.some.injEq] at hq; subst hq; cases eq_of_beq hsk; exact ⟨Nat.lt_succ_self _, by simp [k, Array.getElem?_eq_getElem hlt]⟩
        · simp only [hsk, Bool.false_eq_true, ↓reduceIte] at hq; have ⟨h1, h2⟩ := hinv.2.1 s oi hq; exact ⟨Nat.lt_trans h1 (Nat.lt_succ_self _), h2⟩
      · rw [hget']; by_cases heqI : oi = i
        · subst heqI; rw [Array.getElem?_eq_getElem hlt, Option.some.injEq] at hs; subst hs; simp [k]
        · have hoiLt : oi < i := by omega
          have hneK : (s == k) = false := beq_eq_false_iff_ne.2 fun hsk => by subst hsk; rw [Array.getElem?_eq_getElem (Nat.lt_trans hoiLt hlt), Option.some.injEq] at hs; exact heqI (nodup_getElem_inj (by simpa using Nat.lt_trans hoiLt hlt) (by simpa using hlt) hnd (by simpa [k] using hs))
          simp only [hneK, Bool.false_eq_true, ↓reduceIte]; exact hinv.2.2 oi hoiLt s hs
theorem buildKeyIndex_spec (keys : Array String) (hnd : keys.toList.Nodup) :
    let (buckets, mask) := buildKeyIndex keys
    (∀ k oi, keyIndexGet buckets mask k = some oi → oi < keys.size ∧ keys[oi]? = some k) ∧
    (∀ oi, oi < keys.size → ∀ k, keys[oi]? = some k → keyIndexGet buckets mask k = some oi) := by
  dsimp only [buildKeyIndex]; have hcap : 0 < nextPow2Ge (keys.size * 2) 16 30 := nextPow2Ge_pos _ 16 30 (by omega)
  exact (buildKeyIndexLoop_spec keys _ hnd 0 (Nat.zero_le _) _ ⟨by simp [hcap], fun _ _ hq => by unfold keyIndexGet at hq; simp [hcap, kpLookupList] at hq, fun _ _ => by omega⟩).2
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
  | base => intro _ sources used rows _ _ _ hss hus hrs hsrc hused hrows; unfold planKeyedLoop; simp only [Nat.lt_irrefl, ↓reduceDIte, PlanKeyedOut]
            exact ⟨hss, hus, hrs, fun j hj => by simpa [Array.getD, hss, hj] using hsrc j hj, fun oi ho => by simpa [Array.getD, hus, ho, hss] using hused oi ho, fun j hj => by rw [Array.getElem?_eq_getElem (by omega)]; exact congrArg some (hrows j hj)⟩
  | step i hlt ih =>
      intro freshCache sources used rows marks sigs hfc hss hus hrs hsrc hused hrows; unfold planKeyedLoop; simp only [hlt, ↓reduceDIte]
      have husedPush (v : Option Nat) (oi' : Nat) (hne : v ≠ some oi') :
          (∃ j, ∃ _ : j < i, sources[j]'(by omega) = some oi') ↔ (∃ j, ∃ _ : j < i + 1, (sources.push v)[j]'(by rw [Array.size_push, hss]; omega) = some oi') :=
        ⟨fun ⟨j, hj, hje⟩ => ⟨j, Nat.lt_trans hj (Nat.lt_succ_self _), by simp [Array.getElem_push_lt (by omega : j < sources.size), hje]⟩,
         fun ⟨j, hj, hje⟩ => if hji : j < i then ⟨j, hji, by simpa [Array.getElem_push_lt (by omega : j < sources.size)] using hje⟩
           else by cases (show j = i by omega); exact absurd ((show (sources.push v)[i]'(by simp [hss]) = v by simpa [hss] using @Array.getElem_push_eq _ sources v).symm.trans hje) hne⟩
      have hsrc' (x) := array_push_step_inv (x := x) (f := fun j hj => keyIndexGet oldBuckets mask (newKeys[j]'hj)) hlt hss hsrc
      have hrows' (x) := array_push_step_inv (x := x) (f := fun j hj => match keyIndexGet oldBuckets mask (newKeys[j]'hj) with | some oi => oldRows.getD oi default | none => (fresh ()).getD j default) hlt hrs hrows
      cases hq : keyIndexGet oldBuckets mask newKeys[i] with
      | some oi =>
          have hoi : oi < used.size := hus.symm ▸ hidxBound _ _ hq; simp only [hoi, ↓reduceDIte]
          refine ih freshCache (sources.push (some oi)) (used.set oi true hoi) (rows.push (oldRows.getD oi default)) (marks.push (oldMarks.getD oi 0)) (sigs.push (oldSigs.getD oi #[]))
            hfc (by simp [hss]) (by simp [hus]) (by simp [hrs]) (hsrc' _ hq.symm) (fun oi' ho' => ?_) (hrows' _ (by simp [hq]))
          by_cases heqO : oi' = oi
          · subst oi'; simp only [Array.getElem_set_self, true_iff]; exact ⟨i, Nat.lt_succ_self _, by simpa [hss] using @Array.getElem_push_eq _ sources (some oi)⟩
          · simp only [Array.getElem_set_ne (by omega : oi < used.size) (by omega) (Ne.symm heqO), hused oi' ho']; exact husedPush (some oi) oi' fun h => heqO (Option.some.inj h).symm
      | none =>
          have hstep := ih (some (fresh ())) (sources.push none) used (rows.push ((fresh ()).getD i default)) (marks.push 0) (sigs.push #[])
            (fun _ h => (Option.some.inj h).symm) (by simp [hss]) hus (by simp [hrs]) (hsrc' _ hq.symm) (fun oi' ho' => (hused oi' ho').trans (husedPush none oi' (by simp))) (hrows' _ (by simp [hq]))
          cases freshCache with | none => exact hstep | some fArr => rw [hfc fArr rfl]; exact hstep
private theorem isValidLisLoop_sound (sources : Array (Option Nat)) (flags : Array Bool) (i : Nat) (hle : i ≤ sources.size) :
    ∀ last?, isValidLisLoop sources flags i last? = true →
      (∀ j, i ≤ j → j < sources.size → flags.getD j false = true → ∃ oi, sources.getD j none = some oi ∧ (∀ p, last? = some p → p < oi)) ∧
      (∀ j₁ j₂, i ≤ j₁ → j₁ < j₂ → j₂ < sources.size → flags.getD j₁ false = true → flags.getD j₂ false = true → ∀ oi₁ oi₂, sources.getD j₁ none = some oi₁ → sources.getD j₂ none = some oi₂ → oi₁ < oi₂) := by
  induction i, hle using down_ind with
  | base => exact fun _ _ => ⟨fun _ _ _ => by omega, fun _ _ _ _ _ => by omega⟩
  | step i hlt ih =>
      intro last? hv; unfold isValidLisLoop at hv; simp only [hlt, ↓reduceDIte] at hv
      cases hfi : flags.getD i false with
      | false => simp only [hfi, Bool.false_eq_true, ↓reduceIte] at hv; have ⟨ih1, ih2⟩ := ih last? hv
                 exact ⟨fun j _ h2 hfj => if h : j = i then by simp [h, hfi] at hfj else ih1 j (by omega) h2 hfj, fun j₁ j₂ _ h2 h3 hf1 hf2 => if h : j₁ = i then by simp [h, hfi] at hf1 else ih2 j₁ j₂ (by omega) h2 h3 hf1 hf2⟩
      | true => simp only [hfi, ↓reduceIte] at hv; cases hs : sources[i] with | none => simp [hs] at hv | some oi =>
                simp only [hs] at hv; have hlast : ∀ p, last? = some p → p < oi := fun p hp => by subst hp; dsimp only at hv; split at hv <;> first | assumption | simp at hv
                have ⟨ih1, ih2⟩ := ih (some oi) (by cases last? with | none => exact hv | some p => simpa [hlast p rfl] using hv)
                exact ⟨fun j _ h2 hfj => if h : j = i then h ▸ ⟨oi, by simpa [Array.getD, hlt] using hs, hlast⟩ else let ⟨oj, hsoj, hoiLt⟩ := ih1 j (by omega) h2 hfj; ⟨oj, hsoj, fun p hp => Nat.lt_trans (hlast p hp) (hoiLt oi rfl)⟩,
                  fun j₁ j₂ _ h2 h3 hf1 hf2 oi₁ oi₂ hs1 hs2 => if h : j₁ = i then by subst h; cases (show oi₁ = oi by simpa [Array.getD, hlt, hs] using hs1.symm); rcases ih1 j₂ (by omega) h3 hf2 with ⟨oj, hsoj, hoiLt⟩; rw [Option.some.inj (hs2.symm.trans hsoj)]; exact hoiLt oi rfl
                    else ih2 j₁ j₂ (by omega) h2 h3 hf1 hf2 oi₁ oi₂ hs1 hs2⟩
theorem verifiedLisFlags_spec (sources : Array (Option Nat)) :
    let inLis := verifiedLisFlags sources
    (∀ j, j < sources.size → inLis.getD j false = true → ∃ oi, sources.getD j none = some oi) ∧
    (∀ j₁ j₂, j₁ < j₂ → j₂ < sources.size → inLis.getD j₁ false = true → inLis.getD j₂ false = true → ∀ oi₁ oi₂, sources.getD j₁ none = some oi₁ → sources.getD j₂ none = some oi₂ → oi₁ < oi₂) := by
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
private theorem removeUnusedM_spec (en : ElemPar msg) (live : Array Dom.Node) (used : Array Bool) (i : Nat) (hle : i ≤ live.size) :
    ∀ kept (a : DomArena msg), (kept ++ live.toList.drop i).Nodup → a.get en.parent = en.entry (kept ++ live.toList.drop i) →
      let aOut := ((removeUnusedM (m := ArenaM msg) en.parent live used i).run a).2
      ArenaExt a aOut (· = en.parent.toNat) 0 ∧ aOut.get en.parent = en.entry (kept ++ (List.range (live.size - i)).filterMap fun d => if used.getD (i + d) false then some (live.getD (i + d) 0) else none) := by
  induction i, hle using down_ind with
  | base => intro kept a _ hget; unfold removeUnusedM; rw [List.drop_of_length_le (by simp), List.append_nil] at hget
            simp only [Nat.lt_irrefl, ↓reduceDIte, StateT.run, pure, StateT.pure, Nat.sub_self, List.range_zero, List.filterMap_nil, List.append_nil]; exact ⟨ArenaExt.refl, hget⟩
  | step i hlt ih =>
      intro kept a hnd hget; rw [show live.toList.drop i = live[i] :: live.toList.drop (i + 1) by rw [List.drop_eq_getElem_cons (by simpa using hlt)]; rfl] at hnd hget
      have hshift : ((List.range (live.size - i)).filterMap fun d => if used.getD (i + d) false then some (live.getD (i + d) 0) else none) =
          (if used.getD i false then [live[i]] else []) ++ ((List.range (live.size - (i + 1))).filterMap fun d => if used.getD (i + 1 + d) false then some (live.getD (i + 1 + d) 0) else none) := by
        rw [show live.size - i = (live.size - (i + 1)) + 1 by omega, List.range_succ_eq_map, List.filterMap_cons, List.filterMap_map, Nat.add_zero,
          show ((fun d => if used.getD (i + d) false then some (live.getD (i + d) 0) else none) ∘ (· + 1)) = (fun d => if used.getD (i + 1 + d) false then some (live.getD (i + 1 + d) 0) else none) from funext fun d => by simp [Nat.add_comm d 1, Nat.add_assoc]]
        cases used.getD i false <;> simp [Array.getD, hlt]
      unfold removeUnusedM; simp only [hlt, ↓reduceDIte]
      cases hu : used.getD i false with
      | true => simp only [↓reduceIte]; have ⟨hext, hpar⟩ := ih (kept ++ [live[i]]) a (by simpa [List.append_assoc] using hnd) (by simpa [List.append_assoc] using hget); exact ⟨hext, by rw [hpar, hshift, hu]; simp [List.append_assoc]⟩
      | false =>
          have hndP := List.nodup_append.1 hnd; let a1 := a.set en.parent (en.entry (kept ++ live.toList.drop (i + 1)))
          have hstep : MonadDom.removeNode (m := ArenaM msg) en.parent live[i] a = ((), a1) := by
            simp only [MonadDom.removeNode, DomArena.modifyChildren, DomArena.modify, hget, ElemPar.entry, erase_append_right_of_not_mem kept (live[i] :: live.toList.drop (i + 1)) fun hm => hndP.2.2 live[i] hm live[i] (.head _) rfl, List.erase_cons_head, a1]
          have ⟨hext, hpar⟩ := ih kept a1 (List.nodup_append.2 ⟨hndP.1, (List.nodup_cons.1 hndP.2.1).2, fun x hx y hy => hndP.2.2 x hx y (.tail _ hy)⟩) (DomArena.get_set_self ..)
          dsimp only [StateT.run] at hext hpar ⊢; simp only [Bool.false_eq_true, ↓reduceIte]; rw [stateM_bind_step hstep]
          exact ⟨(ArenaExt.of_set (W := (· = en.parent.toNat)) rfl).trans hext (fun _ h => h) (fun _ _ h => h) (Nat.le_refl _), by rw [hpar, hshift, hu]; simp⟩
private theorem filterLisNodes_succ (live : Array Dom.Node) (sources : Array (Option Nat)) (inLis : Array Bool) (want : Bool) (k : Nat) :
    filterLisNodes live sources inLis want (k + 1) = filterLisNodes live sources inLis want k ++ (if inLis.getD k false == want then match sources.getD k none with | some oi => [live.getD oi 0] | none => [] else []) := by
  unfold filterLisNodes; rw [List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases (inLis.getD k false == want); · simp
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
  have hdisj : ∀ x, x ∈ filterLisNodes live sources inLis false n → x ∈ filterLisNodes live sources inLis true n → False := fun x hm hl => by
    rcases (mem_filterLisNodes ..).1 hm with ⟨i₁, oi₁, hi1, hf1, hs1, hx1⟩; rcases (mem_filterLisNodes ..).1 hl with ⟨i₂, oi₂, hi2, hf2, hs2, hx2⟩
    cases nodup_array_getD_inj (hsrcBound i₁ hi1 oi₁ hs1) (hsrcBound i₂ hi2 oi₂ hs2) hliveNd (hx1.trans hx2.symm); cases hsrcInj i₁ i₂ hi1 hi2 oi₁ hs1 hs2; simp [hf1] at hf2
  refine ⟨List.Pairwise.filterMap _ (fun a a' hlt _ hb _ hb' heq => by simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hb hb'; have := nodup_array_getD_inj hlt.1 hlt.2.1 hliveNd (hb.2.trans (heq.trans hb'.2.symm)); omega) pairwise_range_lt,
    fun x => by simp only [kept, List.mem_filterMap, List.mem_range, Option.ite_none_right_eq_some, Option.some.injEq, mem_filterLisNodes]
                exact ⟨fun ⟨oi, hoi, hu, hx⟩ => let ⟨i, hi, hs⟩ := (husedIff oi hoi).1 hu; match hfl : inLis.getD i false with | false => .inl ⟨i, oi, hi, hfl, hs, hx⟩ | true => .inr ⟨i, oi, hi, hfl, hs, hx⟩,
                       fun h => by rcases h with ⟨i, oi, hi, _, hs, hx⟩ | ⟨i, oi, hi, _, hs, hx⟩ <;> exact ⟨oi, hsrcBound i hi oi hs, (husedIff oi (hsrcBound i hi oi hs)).2 ⟨i, hi, hs⟩, hx⟩⟩, hdisj, ?_⟩
  let rec hkm : ∀ l : List Nat, (l.filterMap fun oi => if used.getD oi false then some (live.getD oi 0) else none) = (l.filter (used.getD · false)).map (live.getD · 0)
    | [] => rfl | a :: r => by simp only [List.filterMap_cons, List.filter_cons, hkm r]; cases used.getD a false <;> rfl
  rw [show kept = _ from hkm _, List.filter_map, List.filter_filter,
      show filterLisNodes live sources inLis true n = ((List.range n).filterMap fun i => if inLis.getD i false then sources.getD i none else none).map (live.getD · 0) by unfold filterLisNodes; rw [List.map_filterMap]; congr 1; funext i; cases inLis.getD i false <;> rfl,
      congrArg (List.map _) (List.filter_congr fun _ _ => Bool.and_comm ..)]
  refine congrArg (List.map (live.getD · 0)) (pairwise_lt_ext _ _ (List.Pairwise.filter _ List.pairwise_lt_range)
    (List.Pairwise.filterMap _ (fun i₁ i₂ hlt oi₁ h1 oi₂ h2 => by simp only [Option.ite_none_right_eq_some] at h1 h2; exact hlisMono i₁ i₂ hlt.2.2 hlt.2.1 h1.1 h2.1 oi₁ oi₂ h1.2 h2.2) pairwise_range_lt)
    fun oi => by
      simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, Function.comp_apply, Bool.not_eq_true', List.mem_filterMap, Option.ite_none_right_eq_some]
      exact ⟨fun ⟨hoi, hu, hnotM⟩ => let ⟨i, hi, hs⟩ := (husedIff oi hoi).1 hu; (by cases hfl : inLis.getD i false with | true => exact ⟨i, hi, hfl, hs⟩ | false => rw [List.contains_iff_mem.2 ((mem_filterLisNodes ..).2 ⟨i, oi, hi, hfl, hs, rfl⟩)] at hnotM; cases hnotM),
             fun ⟨i, hi, hfl, hif⟩ => let hoi := hsrcBound i hi oi hif; ⟨hoi, (husedIff oi hoi).2 ⟨i, hi, hif⟩, Bool.eq_false_iff.2 fun hc => hdisj _ (List.contains_iff_mem.1 hc) ((mem_filterLisNodes ..).2 ⟨i, oi, hi, hfl, hif, rfl⟩)⟩⟩)
private theorem htmlDepth_le_listDepth : ∀ {l : List (Html msg)}, ∀ h ∈ l, htmlDepth h ≤ htmlListDepth l
  | [], _, h => nomatch h | _ :: _, h, hm => by simp only [htmlListDepth]; exact (List.mem_cons.1 hm).elim (· ▸ Nat.le_max_left ..) fun ht => Nat.le_trans (htmlDepth_le_listDepth h ht) (Nat.le_max_right ..)

section LisBack
variable {en : ElemPar msg}
  {live : Array Dom.Node} {sources : Array (Option Nat)} {inLis : Array Bool} {rowsArr : Array (Html msg)}
  {newRowsL oldRowsL : List (Html msg)} {Si : Nat → Nat → Prop} {Sold : Nat → Prop} {baseNext : Nat}

private theorem reconcileLisBackM_spec (ctx : LisBackCtx en.f en.parent live sources rowsArr newRowsL oldRowsL Si Sold baseNext) :
    ∀ (k : Nat), k ≤ newRowsL.length → ∀ hasAnchor anchor cs placed Splaced a,
      LisBackInv en live sources inLis newRowsL oldRowsL Si Sold baseNext k hasAnchor anchor cs placed Splaced a →
      ReconcileBackOut en newRowsL Sold baseNext k a ((reconcileLisBackM (m := ArenaM msg) en.parent en.childNs live sources inLis rowsArr k hasAnchor anchor).run a).2 := by
  intro k; induction k with
  | zero =>
      intro _ _ _ cs placed Splaced a inv; rcases inv with ⟨_, ⟨hget, _⟩, _, _, _, hfilt, _, ⟨hSpSub, _⟩, hClPl⟩
      dsimp only [ReconcileBackOut]; simp only [reconcileLisBackM, StateT.run, pure, StateT.pure, List.take_zero, htmlListNodeCount, List.drop_zero] at hClPl ⊢
      have hcsEq : cs = placed := (List.filter_eq_self.2 (fun _ _ => rfl)).symm.trans (by simpa only [filterLisNodes, List.range_zero, List.filterMap_nil, List.contains_nil, Bool.not_false, List.nil_append] using hfilt)
      exact ⟨ArenaExt.refl, cs, hget, hcsEq ▸ CleanDomChildren_mono hSpSub hClPl⟩
  | succ k ih =>
      intro hk hasAnchor anchor cs placed Splaced a inv
      have hkLt : k < newRowsL.length := Nat.lt_of_succ_le hk
      have htakeCnt : htmlListNodeCount (newRowsL.take (k + 1)) = htmlListNodeCount (newRowsL.take k) + htmlNodeCount newRowsL[k] := by rw [List.take_succ_eq_append_getElem hkLt, htmlListNodeCount_append]; simp only [htmlListNodeCount, Nat.add_zero]
      have hmono (w : Bool) (y : Dom.Node) (hy : y ∈ filterLisNodes live sources inLis w k) : y ∈ filterLisNodes live sources inLis w (k + 1) := by rw [filterLisNodes_succ]; exact List.mem_append_left _ hy
      have hInvoke (x : Dom.Node) (Sx : Nat → Prop) (cs' : List Dom.Node) (aNext : DomArena msg) (haExt' : ArenaExt a aNext (· = en.parent.toNat) (htmlNodeCount newRowsL[k]))
          (hget' : aNext.get en.parent = en.entry cs') (hnd' : cs'.Nodup) (hxNotF : ∀ w, x ∉ filterLisNodes live sources inLis w k)
          (hm' : ∀ y, y ∈ cs' ↔ y ∈ filterLisNodes live sources inLis false k ∨ y ∈ filterLisNodes live sources inLis true k ∨ y ∈ x :: placed)
          (hf' : cs'.filter (fun y => !(filterLisNodes live sources inLis false k).contains y) = filterLisNodes live sources inLis true k ++ x :: placed)
          (hSxSub : ∀ m, Sx m → (Sold m ∨ (baseNext ≤ m ∧ m < aNext.nextId)) ∧ m ≠ en.parent.toNat)
          (hSxDisj : ∀ i, i < k → ∀ oi', sources.getD i none = some oi' → ∀ m, Si oi' m → ¬Sx m) (hSxPl : ∀ m, Sx m → ¬Splaced m)
          (hxc' : CleanDomSubtree en.f en.childNs newRowsL[k] aNext Sx x) (hpc' : CleanDomChildren en.f en.childNs (newRowsL.drop (k + 1)) aNext Splaced placed) :
          ReconcileBackOut en newRowsL Sold baseNext (k + 1) a ((reconcileLisBackM (m := ArenaM msg) en.parent en.childNs live sources inLis rowsArr k true x).run aNext).2 := by
        have hres := ih (Nat.le_of_lt hkLt) true x cs' (x :: placed) (fun m => Sx m ∨ Splaced m) aNext
          ⟨⟨Nat.le_trans inv.hbnd.1 haExt'.next_ge, haExt'.lt inv.hbnd.2.1, haExt'.bound_sub (by rw [Nat.add_comm (htmlNodeCount newRowsL[k]), ← htakeCnt]; exact inv.hbnd.2.2.1), haExt'.lt inv.hbnd.2.2.2⟩,
           ⟨hget', hnd'⟩, ⟨rfl, rfl⟩, hm', ⟨fun y hm hl => inv.hDisj.1 y (hmono false y hm) (hmono true y hl), fun y hm hp => (List.mem_cons.1 hp).elim (fun h => hxNotF false (h ▸ hm)) (inv.hDisj.2.1 y (hmono false y hm)), fun y hl hp => (List.mem_cons.1 hp).elim (fun h => hxNotF true (h ▸ hl)) (inv.hDisj.2.2 y (hmono true y hl))⟩,
           hf', fun oi ho => CleanDomSubtree_frame (fun m hm => let hsub := ctx.hSi.1 oi m.toNat hm; haExt'.frame m (Nat.lt_of_lt_of_le (ctx.hSi.2.2 _ hsub.1) inv.hbnd.1) hsub.2) (inv.hOldClean oi ho),
           ⟨fun m hm => hm.elim (hSxSub m) fun h => let ⟨hb, hne⟩ := inv.hSp.1 m h; ⟨hb.imp id fun ⟨h1, h2⟩ => ⟨h1, haExt'.lt h2⟩, hne⟩,
            fun i hi oi' hs' m hm1 hm2 => hm2.elim (hSxDisj i hi oi' hs' m hm1) (inv.hSp.2 i (Nat.lt_succ_of_lt hi) oi' hs' m hm1)⟩,
           by rw [List.drop_eq_getElem_cons hkLt]; exact ⟨Sx, Splaced, fun _ => .inl, fun _ => .inr, hSxPl, hxc', hpc'⟩⟩
        exact ⟨haExt'.trans hres.1 (fun _ h => h) (fun _ _ h => h) (by rw [htakeCnt, Nat.add_comm]; exact Nat.le_refl _), hres.2⟩
      have hInsert (x : Dom.Node) (Sx : Nat → Prop) (aMid : DomArena msg) (haExt : ArenaExt a aMid (· = en.parent.toNat) (htmlNodeCount newRowsL[k]))
          (hgetMid : aMid.get en.parent = en.entry cs) (hxNotF : ∀ w, x ∉ filterLisNodes live sources inLis w k) (hxNotPl : x ∉ placed)
          (hfiltEr : (cs.erase x).filter (fun y => !(filterLisNodes live sources inLis false k).contains y) = filterLisNodes live sources inLis true k ++ placed)
          (hmemEr : ∀ y, y = x ∨ y ∈ cs.erase x ↔ y ∈ filterLisNodes live sources inLis false k ∨ y ∈ filterLisNodes live sources inLis true k ∨ y ∈ x :: placed)
          (hSxSub : ∀ m, Sx m → (Sold m ∨ (baseNext ≤ m ∧ m < aMid.nextId)) ∧ m ≠ en.parent.toNat)
          (hSxDisj : ∀ i, i < k → ∀ oi', sources.getD i none = some oi' → ∀ m, Si oi' m → ¬Sx m) (hSxPl : ∀ m, Sx m → ¬Splaced m)
          (hxClean : CleanDomSubtree en.f en.childNs newRowsL[k] aMid Sx x) (hPlClean : CleanDomChildren en.f en.childNs (newRowsL.drop (k + 1)) aMid Splaced placed) :
          ReconcileBackOut en newRowsL Sold baseNext (k + 1) a ((do MonadDom.insertBeforeRef (m := ArenaM msg) en.parent (if hasAnchor then some anchor else none) x; reconcileLisBackM en.parent en.childNs live sources inLis rowsArr k true x).run aMid).2 := by
        have ⟨hnd', hm', hf'⟩ := w3cInsertBeforeRef_reconcile_step inv.hget.2 inv.hanc.2 hxNotPl (hxNotF false) (fun y hm => inv.hDisj.2.1 y (hmono false y hm)) (fun y hl => inv.hDisj.2.2 y (hmono true y hl)) hfiltEr
        dsimp only [StateT.run]; simp only [ArenaM.bind_eq, MonadDom.insertBeforeRef, DomArena.modifyChildren, DomArena.modify, hgetMid, ElemPar.entry]
        exact hInvoke x Sx _ _ (haExt.set_right rfl) (DomArena.get_set_self ..) hnd' hxNotF (fun y => (hm' y).trans (hmemEr y)) hf' hSxSub hSxDisj hSxPl
          (hxClean.frame_set_ne fun h => (hSxSub _ h).2 rfl) (hPlClean.frame_set_ne fun h => (inv.hSp.1 _ h).2 rfl)
      have hcsMem := inv.hcsMem; have hfilt := inv.hfilt; dsimp only [reconcileLisBackM, StateT.run]
      cases hsK : sources.getD k none with
      | some oi =>
          have hoi : oi < oldRowsL.length := ctx.hsrcBound k hkLt oi hsK; let child := live.getD oi 0
          have hchildNotF : ∀ w, child ∉ filterLisNodes live sources inLis w k := fun w hm => by
            rcases (mem_filterLisNodes ..).1 hm with ⟨i, oi', hi, _, hsi, hEq⟩
            exact Nat.ne_of_lt hi (ctx.hsrcInj i k (Nat.lt_trans hi hkLt) hkLt oi' hsi (nodup_array_getD_inj (ctx.hrows.2.1 ▸ ctx.hsrcBound i (Nat.lt_trans hi hkLt) oi' hsi) (ctx.hrows.2.1 ▸ hoi) ctx.hrows.2.2.1 hEq ▸ hsK))
          have hSxSub : ∀ m, Si oi m → (Sold m ∨ (baseNext ≤ m ∧ m < a.nextId)) ∧ m ≠ en.parent.toNat := fun m h => ⟨.inl (ctx.hSi.1 oi m h).1, (ctx.hSi.1 oi m h).2⟩
          have hSxDisj : ∀ i, i < k → ∀ oi', sources.getD i none = some oi' → ∀ m, Si oi' m → ¬Si oi m := fun i hi oi' hs' m hm1 hm2 => ctx.hSi.2.1 oi' oi (fun he => Nat.ne_of_lt hi (ctx.hsrcInj i k (Nat.lt_trans hi hkLt) hkLt oi' hs' (he ▸ hsK))) m hm1 hm2
          have hclC : CleanDomSubtree en.f en.childNs newRowsL[k] a (Si oi) child := ctx.hsrcRow k hkLt oi hoi hsK ▸ inv.hOldClean oi hoi
          cases hflK : inLis.getD k false <;> (rw [filterLisNodes_succ, filterLisNodes_succ, hflK, hsK] at hcsMem hfilt; simp only [beq_false, beq_true, Bool.not_true, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, List.append_nil] at hcsMem hfilt ⊢)
          · have hchildNotEr : child ∉ cs.erase child := List.Nodup.not_mem_erase inv.hget.2
            exact hInsert child (Si oi) a ArenaExt.refl inv.hget.1 hchildNotF
              (fun hp => inv.hDisj.2.1 child (by rw [filterLisNodes_succ, hflK, hsK]; simp only [beq_self_eq_true, ↓reduceIte, List.mem_append, List.mem_singleton, child, or_true]) hp)
              (by rw [List.filter_congr (q := fun x => !(filterLisNodes live sources inLis false k ++ [child]).contains x) fun x hx => by simp only [List.contains_append, List.contains_cons, List.contains_nil, Bool.or_false, beq_eq_false_iff_ne.2 (show x ≠ child from fun h => hchildNotEr (h ▸ hx))],
                      erase_filter_of_false _ child (by simp only [List.contains_append, List.contains_cons, beq_self_eq_true, Bool.true_or, Bool.or_true, Bool.not_true]), hfilt])
              (fun x => by by_cases hx : x = child; · subst hx; simp only [List.mem_cons, true_or, or_true]
                           · simp only [child, hx, false_or, List.mem_erase_of_ne hx, hcsMem x, List.mem_append, List.mem_cons, List.not_mem_nil, or_false])
              hSxSub hSxDisj (inv.hSp.2 k (Nat.lt_succ_self k) oi hsK) hclC inv.hClPl
          · exact hInvoke child (Si oi) cs a ArenaExt.refl inv.hget.1 inv.hget.2 hchildNotF
              (fun x => by rw [hcsMem x]; simp only [child, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc])
              (by simpa only [child, List.append_assoc, List.singleton_append] using hfilt) hSxSub hSxDisj (inv.hSp.2 k (Nat.lt_succ_self k) oi hsK) hclC inv.hClPl
      | none =>
          have hStepF : ∀ w, filterLisNodes live sources inLis w (k + 1) = filterLisNodes live sources inLis w k := fun w => by rw [filterLisNodes_succ, hsK]; cases (inLis.getD k false == w) <;> simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
          rw [hStepF false, hStepF true] at hcsMem hfilt
          rw [show rowsArr.getD k default = newRowsL[k] by have hkArr : k < rowsArr.size := Array.length_toList ▸ ctx.hrows.1.symm ▸ hkLt; simp only [Array.getD, hkArr, ↓reduceDIte]; exact (Array.getElem_toList (xs := rowsArr) (i := k) (h := hkArr)).symm.trans (Option.some.inj (by rw [← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, ctx.hrows.1]))]
          have ⟨hcnGe, _, ha1Ext, _, _, hbuiltFn⟩ := buildDomM_spec_full en.childNs newRowsL[k] a en.f inv.hbnd.2.1
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left _ _) _) (htakeCnt ▸ inv.hbnd.2.2.1)) (Nat.le_trans (htmlDepth_le_listDepth newRowsL[k] (List.getElem_mem hkLt)) ctx.hrows.2.2.2.2)
          let cn := (buildDomM (m := ArenaM msg) en.childNs newRowsL[k] a).1; let a1 := (buildDomM (m := ArenaM msg) en.childNs newRowsL[k] a).2
          have hInA (m : Nat) (h : Sold m ∨ (baseNext ≤ m ∧ m < a.nextId)) : m < a.nextId := h.elim (fun hs => Nat.lt_of_lt_of_le (ctx.hSi.2.2 m hs) inv.hbnd.1) (·.2)
          have hfiltInA : ∀ w x, x ∈ filterLisNodes live sources inLis w k → x.toNat < a.nextId := fun _ _ hx => by
            rcases (mem_filterLisNodes ..).1 hx with ⟨i, oi', hi, _, hsi, rfl⟩
            exact hInA _ (.inl (ctx.hSi.1 oi' _ (CleanDomSubtree_root_mem (inv.hOldClean oi' (ctx.hsrcBound i (Nat.lt_trans hi hkLt) oi' hsi)))).1)
          have hcnNotCs : cn ∉ cs := fun hm => Nat.not_lt.2 hcnGe <| match (hcsMem cn).1 hm with | .inl h => hfiltInA false cn h | .inr (.inl h) => hfiltInA true cn h | .inr (.inr hp) => hInA _ (inv.hSp.1 _ (CleanDomChildren_mem inv.hClPl cn hp)).1
          have hcsErEq : cs.erase cn = cs := List.erase_of_not_mem hcnNotCs
          dsimp only; rw [ArenaM.bind_eq]
          exact hInsert cn (fun m => a.nextId ≤ m ∧ m < a1.nextId) a1 (ha1Ext.mono (fun _ h => h.elim) (Nat.le_refl _)) ((ha1Ext.frame_lt inv.hbnd.2.2.2).trans inv.hget.1)
            (fun w hm => hcnNotCs ((hcsMem cn).2 (by cases w; exact .inl hm; exact .inr (.inl hm)))) (fun hm => hcnNotCs ((hcsMem cn).2 (.inr (.inr hm)))) (hcsErEq.symm ▸ hfilt)
            (fun x => by rw [hcsErEq, hcsMem x, List.mem_cons, or_left_comm (a := x = cn), or_left_comm (a := x = cn)])
            (fun _ ⟨h1, h2⟩ => ⟨.inr ⟨Nat.le_trans inv.hbnd.1 h1, h2⟩, fun e => Nat.not_lt.2 h1 (e ▸ inv.hbnd.2.2.2)⟩)
            (fun i _ oi' _ m hm1 h1 => Nat.not_lt.2 h1.1 (hInA m (.inl (ctx.hSi.1 oi' m hm1).1))) (fun m h1 h2 => Nat.not_lt.2 h1.1 (hInA m (inv.hSp.1 m h2).1))
            (hbuiltFn (List.all_eq_true.1 ctx.hrows.2.2.2.1 newRowsL[k] (List.getElem_mem hkLt))) (CleanDomChildren_frame (fun m hm => ha1Ext.frame_lt (hInA _ (inv.hSp.1 m.toNat hm).1)) inv.hClPl)
end LisBack

private theorem bind_seedRowsM {α : Type} (inst : String) (rs : Nat → Array (String × String)) (re : Nat → Array (String × msg))
    (nm om : Array USize) (os : Array (Array (String × String))) (a : DomArena msg) (k : Array (Array (String × String)) → ArenaM msg α)
    {P : α × DomArena msg → Prop} (h : ∀ r a', a'.SameDom a → P (k r a')) : P ((seedRowsM (m := ArenaM msg) inst rs re nm om os >>= k) a) := by
  rw [ArenaM.bind_eq]; exact h _ _ (seedRowsM_sameDom inst rs re nm om os a)

section
variable {σ : Type} {ep : ElemPar msg} {tag inst : String} {node : Dom.Node}
  {attrs : List (VAttr σ msg)} {keys : σ → Array String} {marks : σ → Array USize}
  {rowSig : σ → Array String → Nat → Array (String × String)} {rowEv : σ → Array String → Nat → Array (String × msg)}
  {rowsHtml : σ → List (Html msg)} {s₁ s₂ : σ} {pre suf : List Dom.Node} {Sold : Nat → Prop} {a : DomArena msg} {st : SpecElemState msg} {mg : List String} {domCs : List Dom.Node}

private theorem keyedList_finish_goal {st' : SpecElemState msg} {mg' : List String} {csNew : List Dom.Node} {aOut : DomArena msg}
    {outKeys : Array String} {outSigs : Array (Array (String × String))} {outRows : List (Html msg)} {outMarks : Array USize}
    (ctx : KeyedPatchCtx ep tag node attrs keys rowsHtml s₁ s₂ pre suf Sold a st mg domCs)
    (haExt : ArenaExt a aOut (· = node.toNat) (1 + htmlListNodeCount (rowsHtml s₂)))
    (haOutNode : aOut.get node = .element (if ep.childNs == "" && tag == "svg" then Dom.svgNs else ep.childNs) tag st' mg' csNew) (hDyn₂ : DynAttrsOk attrs s₂ st' mg')
    (hCleanOut : CleanDomChildren ep.f (Dom.childNsOf ep.childNs tag) (rowsHtml s₂) aOut (fun k => (Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ node.toNat) csNew) (hkeysEq : outKeys = disambiguateKeys (keys s₂)) (hrowsEq : outRows = rowsHtml s₂) :
    PatchViewPost ⟨ep.f + 1, ep.childNs, ep.parent, ep.pns, ep.ptag, ep.pst, ep.pmg⟩ (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ pre suf Sold a (.list node outKeys outSigs outRows outMarks inst, aOut) :=
  have hvalOut : VStateValid (ep.f + 1) ep.childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ aOut (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) (.list node outKeys outSigs outRows outMarks inst) :=
    ⟨⟨.inl ctx.hnode.1, ctx.hclean.2.1.1 s₂, ctx.hclean.2.1.2.1 s₂, st', mg', csNew, haOutNode, hDyn₂.1, hDyn₂.2.1, hDyn₂.2.2, hCleanOut⟩, rfl, hkeysEq, hrowsEq⟩
  ⟨haExt.mono (fun _ h => .inr (h ▸ ctx.hnode.1)) (Nat.le_refl _), (haExt.frame ep.parent ctx.hbnd.2.2.1 fun h => ctx.hpar.2.2.1 (h ▸ ctx.hnode.1)).trans ctx.hpar.1, ctx.hpar.2.1, fun r hr => haExt.lt (ctx.hpar.2.2.2.2 r hr), hvalOut, VStateValid_equiv hvalOut⟩

private theorem keyedList_appendFrag_finish {st' : SpecElemState msg} {mg' : List String} {aBase : DomArena msg} {outSigs : Array (Array (String × String))} {outMarks : Array USize}
    (ctx : KeyedPatchCtx ep tag node attrs keys rowsHtml s₁ s₂ pre suf Sold a st mg domCs)
    (haBaseExt : ArenaExt a aBase (· = node.toNat) 0) (haBaseNode : aBase.get node = .element (if ep.childNs == "" && tag == "svg" then Dom.svgNs else ep.childNs) tag st' mg' []) (hDyn₂ : DynAttrsOk attrs s₂ st' mg') :
    PatchViewPost ⟨ep.f + 1, ep.childNs, ep.parent, ep.pns, ep.ptag, ep.pst, ep.pmg⟩ (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ pre suf Sold a
      ((do let frag ← MonadDom.createFragment (m := ArenaM msg); buildDomListM (Dom.childNsOf ep.childNs tag) frag (rowsHtml s₂); MonadDom.appendChild node frag; pure (VState.list node (disambiguateKeys (keys s₂)) outSigs (rowsHtml s₂) outMarks inst)) aBase) := by
  have haBaseN : aBase.nextId = a.nextId := haBaseExt.nextId_eq; have hnodeLt := ctx.hpar.2.2.2.1 _ ctx.hnode.1
  let frag := UInt32.ofNat aBase.nextId; let aFragBase : DomArena msg := { aBase with nextId := aBase.nextId + 1 }
  have haFragNext : aFragBase.nextId = a.nextId + 1 := haBaseN ▸ rfl
  have hfragToNat : frag.toNat = a.nextId := haBaseN ▸ uint32_toNat_ofNat_lt a.nextId (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) ctx.hbnd.1)
  have hfragNeNode : frag ≠ node := node_ne_of_toNat_ne (Nat.ne_of_gt (hfragToNat.symm ▸ hnodeLt))
  rcases buildDomListM_spec_full (Dom.childNsOf ep.childNs tag) (rowsHtml s₂) aFragBase frag ArenaEntry.fragment (.inr fun _ => rfl) [] ep.f
      (haFragNext.symm ▸ hfragToNat.symm ▸ Nat.lt_succ_self _) (haFragNext.symm ▸ Nat.succ_pos _) (haFragNext.symm ▸ Nat.add_assoc a.nextId 1 _ ▸ ctx.hbnd.1) ctx.hbnd.2.1 (fun _ h => nomatch h) with ⟨csNew, aBase', haBuiltEq, haBuiltExt, _, _, hCleanFn⟩
  have hCleanOut := hCleanFn [] (fun _ => False) (ctx.hclean.2.2.2.1 s₂) (fun _ h => h.elim) trivial; simp only [List.nil_append, false_or] at haBuiltEq hCleanOut
  let aBuilt := (buildDomListM (m := ArenaM msg) (Dom.childNsOf ep.childNs tag) frag (rowsHtml s₂) (aFragBase.set frag (.fragment []))).2
  have haBuiltFr (m : Dom.Node) (hm : m.toNat < a.nextId + 1) (hne : m ≠ frag) : aBuilt.get m = aFragBase.get m := haBuiltExt.frame_of_ne hne (haFragNext.symm ▸ hm)
  let aOut := (aBuilt.set frag .null).set node (.element (if ep.childNs == "" && tag == "svg" then Dom.svgNs else ep.childNs) tag st' mg' csNew)
  have happendRun : MonadDom.appendChild (m := ArenaM msg) node frag aBuilt = ((), aOut) := by
    simp only [MonadDom.appendChild, show aBuilt.get frag = .fragment csNew by rw [show aBuilt = aBase'.set frag (.fragment csNew) from haBuiltEq, DomArena.get_set_self],
      DomArena.modifyChildren, DomArena.modify, DomArena.get_set_ne _ _ hfragNeNode.symm, (haBuiltFr node (Nat.lt_succ_of_lt hnodeLt) hfragNeNode.symm).trans haBaseNode, List.filter_nil, List.nil_append, aOut]
  rw [stateM_bind_step (show MonadDom.createFragment (m := ArenaM msg) aBase = (frag, aFragBase.set frag (.fragment [])) from rfl), ArenaM.bind_eq, stateM_bind_step happendRun, ArenaM.pure_eq]
  exact keyedList_finish_goal ctx
    ⟨Nat.le_trans (Nat.le_add_right a.nextId 1) (haFragNext ▸ haBuiltExt.next_ge), Nat.add_assoc a.nextId 1 _ ▸ haFragNext ▸ haBuiltExt.next_le,
     fun m hmLt hne => have hmf : m ≠ frag := node_ne_of_toNat_ne (Nat.ne_of_lt (hfragToNat.symm ▸ hmLt))
       ((aBuilt.set frag .null).get_set_ne _ (node_ne_of_toNat_ne hne)).trans ((aBuilt.get_set_ne _ hmf).trans ((haBuiltFr m (Nat.lt_succ_of_lt hmLt) hmf).trans (haBaseExt.frame m hmLt hne)))⟩
    (DomArena.get_set_self ..) hDyn₂
    (CleanDomChildren_mono (fun k ⟨hk1, hk2⟩ => have hk1' : a.nextId + 1 ≤ k := haFragNext ▸ hk1; ⟨.inr ⟨Nat.le_trans (Nat.le_succ _) hk1', hk2⟩, Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt hnodeLt) hk1')⟩)
      ((hCleanOut.frame_set_ne fun h => Nat.not_lt.2 (show a.nextId + 1 ≤ frag.toNat from haFragNext ▸ h.1) (hfragToNat.symm ▸ Nat.lt_succ_self _)).frame_set_ne fun h => Nat.not_lt.2 (show a.nextId + 1 ≤ node.toNat from haFragNext ▸ h.1) (Nat.lt_succ_of_lt hnodeLt))) rfl rfl

private theorem patchViewM_keyedList_lis_spec {oldSigs : Array (Array (String × String))} {oldMarks : Array USize}
    (ctx : KeyedPatchCtx ep tag node attrs keys rowsHtml s₁ s₂ pre suf Sold a st mg domCs)
    (hrawNe : keys s₂ ≠ disambiguateKeys (keys s₁)) (hsameNe : disambiguateKeys (keys s₂) ≠ disambiguateKeys (keys s₁))
    (hnewEmp : (disambiguateKeys (keys s₂)).isEmpty = false) (hemp : (rowsHtml s₁).isEmpty = false) :
    PatchViewPost ⟨ep.f + 1, ep.childNs, ep.parent, ep.pns, ep.ptag, ep.pst, ep.pmg⟩ (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ pre suf Sold a
      ((patchViewM (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ (.list node (disambiguateKeys (keys s₁)) oldSigs (rowsHtml s₁) oldMarks inst)).run a) := by
  have hnodeLt : node.toNat < a.nextId := ctx.hpar.2.2.2.1 _ ctx.hnode.1; let realNs := if ep.childNs == "" && tag == "svg" then Dom.svgNs else ep.childNs
  dsimp only [patchViewM, StateT.run]; simp only [beq_eq_false_iff_ne.2 hrawNe, beq_eq_false_iff_ne.2 hsameNe, hnewEmp, hemp, Bool.false_eq_true, ↓reduceIte]
  let oldKeys := disambiguateKeys (keys s₁); let newKeys := disambiguateKeys (keys s₂); have hidxSpec := buildKeyIndex_spec oldKeys (disambiguateKeys_nodup (keys s₁))
  let oldBuckets := (buildKeyIndex oldKeys).1; let mask := (buildKeyIndex oldKeys).2; let freshFn : Unit → Array (Html msg) := fun _ => ((rowsHtml s₂).map (Html.prefixSignals inst)).toArray
  have hsz1 := ctx.hclean.2.2.1 s₁; have hsz2 := ctx.hclean.2.2.1 s₂
  let plan := planKeyedLoop newKeys oldBuckets mask (rowsHtml s₁).toArray oldMarks oldSigs freshFn none 0 (Array.emptyWithCapacity newKeys.size) (Array.replicate oldKeys.size false) (Array.emptyWithCapacity newKeys.size) (Array.emptyWithCapacity newKeys.size) (Array.emptyWithCapacity newKeys.size)
  have hplanSpec := planKeyedLoop_spec newKeys oldBuckets mask (rowsHtml s₁).toArray oldMarks oldSigs freshFn oldKeys.size (fun k oi hq => (hidxSpec.1 k oi hq).1) 0 (Nat.zero_le _)
    none (Array.emptyWithCapacity newKeys.size) (Array.replicate oldKeys.size false) (Array.emptyWithCapacity newKeys.size) (Array.emptyWithCapacity newKeys.size) (Array.emptyWithCapacity newKeys.size)
    (fun _ h => nomatch h) rfl (Array.size_replicate ..) rfl (fun _ hj => absurd hj (Nat.not_lt_zero _)) (fun _ _ => ⟨(fun h => by rw [Array.getElem_replicate] at h; cases h), (fun ⟨_, hj, _⟩ => absurd hj (Nat.not_lt_zero _))⟩) (fun _ hj => absurd hj (Nat.not_lt_zero _))
  let sources := plan.1; let used := plan.2.1; let rowsArr := plan.2.2.1; let marksArr := plan.2.2.2.1; let sigsArr := plan.2.2.2.2
  have hsrcSz : sources.size = (rowsHtml s₂).length := hplanSpec.1.trans hsz2.symm; have hsrcGet := hplanSpec.2.2.2.1
  have hsrcBound (i : Nat) (hi : i < (rowsHtml s₂).length) (oi : Nat) (hsi : sources.getD i none = some oi) : oi < (rowsHtml s₁).length := by rw [hsrcGet i (hsz2 ▸ hi)] at hsi; rw [hsz1]; exact (hidxSpec.1 _ oi hsi).1
  have hsrcInj (i₁ i₂ : Nat) (h1 : i₁ < (rowsHtml s₂).length) (h2 : i₂ < (rowsHtml s₂).length) (oi : Nat) (hs1 : sources.getD i₁ none = some oi) (hs2 : sources.getD i₂ none = some oi) : i₁ = i₂ := by
    rw [hsrcGet i₁ (hsz2 ▸ h1)] at hs1; rw [hsrcGet i₂ (hsz2 ▸ h2)] at hs2
    exact nodup_getElem_inj (Array.length_toList ▸ hsz2 ▸ h1) (Array.length_toList ▸ hsz2 ▸ h2) (disambiguateKeys_nodup (keys s₂)) (Option.some.inj ((hidxSpec.1 _ oi hs1).2.symm.trans (hidxSpec.1 _ oi hs2).2))
  have hsrcRow (i : Nat) (hi : i < (rowsHtml s₂).length) (oi : Nat) (ho : oi < (rowsHtml s₁).length) (hsi : sources.getD i none = some oi) : (rowsHtml s₁)[oi] = (rowsHtml s₂)[i] := by
    rw [hsrcGet i (hsz2 ▸ hi)] at hsi; have h := (hidxSpec.1 _ oi hsi).2; rw [Array.getElem?_eq_getElem (hsz1 ▸ ho), Option.some.injEq] at h
    have hrowEq := ctx.hclean.2.2.2.2.2 s₁ s₂ oi i (hsz1 ▸ ho) (hsz2 ▸ hi) h; rw [List.getElem?_eq_getElem ho, List.getElem?_eq_getElem hi, Option.some.injEq] at hrowEq; exact hrowEq
  have hrowsArrEq : rowsArr.toList = rowsHtml s₂ := by
    have hpref := Html.map_prefixSignals_of_DomCleanList inst (ctx.hclean.2.2.2.1 s₂); refine List.ext_getElem? fun i => ?_; rw [Array.getElem?_toList]
    by_cases hi : i < newKeys.size
    · have hri : i < (rowsHtml s₂).length := hsz2 ▸ hi; rw [hplanSpec.2.2.2.2.2 i hi]
      cases hq : keyIndexGet oldBuckets mask newKeys[i] with
      | none => simp only [freshFn, hpref, Array.getD, List.size_toArray, hri, ↓reduceDIte, List.getElem?_eq_getElem hri]; rfl
      | some oi => have hsi := (hsrcGet i hi).trans hq; have hoi1 := hsrcBound i hri oi hsi; simp only [Array.getD, List.size_toArray, hoi1, ↓reduceDIte, List.getElem?_eq_getElem hri]; exact congrArg some (hsrcRow i hri oi hoi1 hsi)
    · rw [Array.getElem?_eq_none (hplanSpec.2.2.1.symm ▸ Nat.not_lt.1 hi), List.getElem?_eq_none (hsz2.symm ▸ Nat.not_lt.1 hi)]
  refine bind_seedRowsM inst (rowSig s₂ newKeys) (rowEv s₂ newKeys) (marks s₂) marksArr sigsArr a _ fun _ aSeed hseed0 => ?_
  rcases applyDynAttrsM_elem_ext ((hseed0.get_eq node).trans ctx.hnode.2.1) ctx.hclean.2.1 ctx.hnode.2.2.1 with ⟨ha1Ext0, _, _, st', mg', ha1Get, hDyn₂⟩
  let a1 := (applyDynAttrsM (m := ArenaM msg) node attrs s₂ aSeed).2
  have ha1Ext : ArenaExt a a1 (· = node.toNat) 0 := (ArenaExt.refl.sameDom hseed0).trans ha1Ext0 (fun _ h => h) (fun _ _ h => h) (Nat.le_refl _)
  rw [ArenaM.bind_eq, stateM_bind_step ((ArenaM.childNamespace_elem ha1Get).trans (congrArg (·, a1) (ep.childNsOk_child ctx.hclean.1 tag)))]
  split
  · rw [stateM_bind_step (ArenaM.clearChildren_elem ha1Get), hrowsArrEq]; exact keyedList_appendFrag_finish ctx (ha1Ext.set_right rfl) (DomArena.get_set_self ..) hDyn₂
  · have ⟨hdomNd, hdomLen⟩ := CleanDomChildren_nodup ctx.hnode.2.2.2
    have hdomLtU32 : domCs.length < UInt32.size := Nat.lt_of_le_of_lt (nodup_nodes_lt_length_le a.nextId domCs hdomNd fun x hx => ctx.hpar.2.2.2.1 _ (CleanDomChildren_mem ctx.hnode.2.2.2 x hx).1) (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) ctx.hbnd.1)
    have hsnap := snapshotChildrenM_spec a1 node realNs tag st' mg' domCs hdomLtU32 0 domCs.length #[] (Nat.zero_add _)
    rw [DomArena.set_get_self a1 ha1Get] at hsnap; simp only [StateT.run, List.nil_append, List.drop_zero] at hsnap
    let live : Array Dom.Node := ⟨domCs⟩; have hliveSz : live.size = (rowsHtml s₁).length := hdomLen; let en : ElemPar msg := ⟨ep.f, Dom.childNsOf ep.childNs tag, node, realNs, tag, st', mg'⟩
    have ⟨haRemExt0, haRemNode⟩ := removeUnusedM_spec en live used 0 (Nat.zero_le _) [] a1 hdomNd ha1Get
    let aRem := (removeUnusedM (m := ArenaM msg) node live used 0 a1).2
    have haRemExt : ArenaExt a aRem (· = node.toNat) 0 := ha1Ext.trans haRemExt0 (fun _ h => h) (fun _ _ h => h) (Nat.le_refl _)
    have haRemN : aRem.nextId = a.nextId := haRemExt.nextId_eq
    let kept := (List.range live.size).filterMap fun oi => if used.getD oi false then some (live.getD oi 0) else none; let inLis := verifiedLisFlags sources
    have hkeptSpec := lis_filter_kept_eq live sources inLis used (rowsHtml s₂).length (fun i hi oi hsi => hliveSz.symm ▸ hsrcBound i hi oi hsi) hsrcInj
      (fun oi ho => by rw [hsz2]; exact hplanSpec.2.2.2.2.1 oi (hsz1 ▸ hliveSz ▸ ho)) hdomNd (fun i₁ i₂ h1 h2 => (verifiedLisFlags_spec sources).2 i₁ i₂ h1 (hsrcSz.symm ▸ h2))
    rcases CleanDomChildren_indexed ctx.hnode.2.2.2 with ⟨Si, hSiSub, hSiDisj, hSiGet⟩
    have ⟨haOutExt, _, haOutNode, hCleanOut⟩ := reconcileLisBackM_spec (en := en) (live := live) (inLis := inLis)
      ⟨⟨hrowsArrEq, hdomLen, hdomNd, ctx.hclean.2.2.2.1 s₂, ctx.hbnd.2.1⟩, hsrcBound, hsrcInj, hsrcRow, ⟨hSiSub, hSiDisj, ctx.hpar.2.2.2.1⟩⟩
      (rowsHtml s₂).length (Nat.le_refl _) false 0 kept [] (fun _ => False) aRem
      ⟨⟨haRemN ▸ Nat.le_refl _, haRemN.symm ▸ ctx.hbnd.2.2.2, by rw [haRemN, List.take_length]; exact Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left _ 1) _) ctx.hbnd.1, haRemN.symm ▸ hnodeLt⟩,
       ⟨by simpa only [StateT.run, List.nil_append, Nat.zero_add, Nat.sub_zero] using haRemNode, hkeptSpec.1⟩, ⟨rfl, rfl⟩,
       fun x => by rw [hkeptSpec.2.1 x]; simp only [List.not_mem_nil, or_false], ⟨hkeptSpec.2.2.1, (fun _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩,
       by rw [List.append_nil]; exact hkeptSpec.2.2.2,
       fun oi ho => by have hoD : oi < domCs.length := hdomLen ▸ ho; rw [show live.getD oi 0 = domCs[oi] by rw [Array.getD, dite_eq_left (show oi < live.size from hoD)]; rfl]; exact CleanDomSubtree_frame (fun m hm => haRemExt.frame m (ctx.hpar.2.2.2.1 _ (hSiSub oi m.toNat hm).1) (hSiSub oi m.toNat hm).2) (hSiGet oi ho hoD),
       ⟨(fun _ h => h.elim), (fun _ _ _ _ _ _ h => h.elim)⟩, by rw [List.drop_length]; trivial⟩
    rw [stateM_bind_step (ArenaM.childCount_elem ha1Get), uint32_toNat_ofNat_lt domCs.length hdomLtU32, stateM_bind_step hsnap, ArenaM.bind_eq, ArenaM.bind_eq,
        show reconcileLisBackM (m := ArenaM msg) node (Dom.childNsOf ep.childNs tag) live sources inLis rowsArr newKeys.size false 0 aRem = reconcileLisBackM (m := ArenaM msg) node (Dom.childNsOf ep.childNs tag) live sources inLis rowsArr (rowsHtml s₂).length false 0 aRem from congrArg (reconcileLisBackM (m := ArenaM msg) node _ live sources inLis rowsArr · false 0 aRem) hsz2.symm, ArenaM.pure_eq]
    exact keyedList_finish_goal ctx (haRemExt.trans haOutExt (fun _ h => h) (fun _ _ h => h) (by rw [List.take_length]; omega)) haOutNode hDyn₂ hCleanOut rfl hrowsArrEq
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
    PatchViewPost ⟨f, childNs, parent, pns, ptag, pst, pmg⟩ (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂ pre suf Sold a
      ((patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?) s₂ vst).run a) := by
  cases tmpl? with | some _ => exact False.elim hclean | none =>
  cases vst with
  | list node oldKeys oldSigs oldRowsL oldMarks inst =>
    rcases hclean with ⟨haClean, hrowsClean⟩; rcases hval with ⟨hcl, _, rfl, rfl⟩; dsimp only [VState.rootNode] at hpar hnd hparNodes
    cases f with | zero => exact False.elim hcl | succ f' =>
    rcases hcl with ⟨hnodeMem, _, _, st, mg, domCs, hnodeGet, hElClean, hElEq, hmg, hCleanCs⟩; dsimp only [VState.rootNode] at hnodeMem hnodeGet hCleanCs
    simp only [View.render, htmlNodeCount, htmlDepth] at hbound hdep
    let ep : ElemPar msg := ⟨f', childNs, parent, pns, ptag, pst, pmg⟩
    have ctx : KeyedPatchCtx ep tag node attrs keys rowsHtml s₁ s₂ pre suf Sold a st mg domCs :=
      ⟨⟨hchildNs, haClean, hrowsClean⟩, ⟨hbound, Nat.le_of_add_le_add_left (a := 1) (Nat.add_comm f' 1 ▸ hdep), hparLt, hpos⟩, ⟨hpar, hnd, hparOut, hSoldLt, hparNodes⟩, ⟨hnodeMem, hnodeGet, ⟨hElClean, hElEq, hmg⟩, hCleanCs⟩⟩
    rcases applyDynAttrsM_elem_ext hnodeGet haClean ⟨hElClean, hElEq, hmg⟩ with ⟨ha1Ext, _, _, st', mg', ha1Get, hDyn₂⟩
    let a1 := (applyDynAttrsM (m := ArenaM msg) node attrs s₂ a).2
    by_cases hsameK : disambiguateKeys (keys s₂) = disambiguateKeys (keys s₁)
    · dsimp only [patchViewM, StateT.run]; simp only [beq_iff_eq.2 hsameK, ↓reduceIte, ite_self]; rw [ArenaM.bind_eq]
      refine bind_seedRowsM inst (rowSig s₂ (disambiguateKeys (keys s₁))) (rowEv s₂ (disambiguateKeys (keys s₁))) (marks s₂) oldMarks oldSigs a1 _ fun _ aOut hseed => ?_
      have haOutExt := ha1Ext.sameDom hseed; have hrowsEq : rowsHtml s₁ = rowsHtml s₂ := keyedRows_eq_of_keys_eq hrowsClean hsameK
      exact keyedList_finish_goal ctx (haOutExt.mono (fun _ h => h) (Nat.zero_le _)) ((hseed.get_eq node).trans ha1Get) hDyn₂
        (by rw [← hrowsEq]; exact CleanDomChildren_mono (fun k hk => ⟨.inl hk.1, hk.2⟩) (CleanDomChildren_frame (fun m hm => haOutExt.frame m (hSoldLt _ hm.1) hm.2) hCleanCs)) hsameK.symm hrowsEq
    · have hrawNe : keys s₂ ≠ disambiguateKeys (keys s₁) := fun h => hsameK ((disambiguateKeys_of_nodup (h ▸ disambiguateKeys_nodup (keys s₁))).trans h)
      cases hnewEmp : (disambiguateKeys (keys s₂)).isEmpty
      · cases hemp : (rowsHtml s₁).isEmpty
        · exact patchViewM_keyedList_lis_spec ctx hrawNe hsameK hnewEmp hemp
        · dsimp only [patchViewM, StateT.run]; simp only [beq_eq_false_iff_ne.2 hrawNe, beq_eq_false_iff_ne.2 hsameK, hnewEmp, hemp, Bool.false_eq_true, ↓reduceIte]; rw [ArenaM.bind_eq]
          have hnilDom : domCs = [] := by rw [List.isEmpty_iff.1 hemp] at hCleanCs; cases domCs <;> first | rfl | exact False.elim hCleanCs
          refine bind_seedRowsM inst (rowSig s₂ (disambiguateKeys (keys s₂))) (rowEv s₂ (disambiguateKeys (keys s₂))) (marks s₂) #[] #[] a1 _ fun r aSeed hseed => ?_
          have haSeedNode : aSeed.get node = .element (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st' mg' [] := by rw [hseed.get_eq node, ha1Get, hnilDom]
          rw [stateM_bind_step ((ArenaM.childNamespace_elem haSeedNode).trans (congrArg (·, aSeed) (ep.childNsOk_child hchildNs tag))), Html.map_prefixSignals_of_DomCleanList inst (hrowsClean.2.1 s₂)]
          exact keyedList_appendFrag_finish (inst := inst) (marks := marks) (rowSig := rowSig) (rowEv := rowEv) (outSigs := r) (outMarks := marks s₂) ctx (ha1Ext.sameDom hseed) haSeedNode hDyn₂
      · dsimp only [patchViewM, StateT.run]; simp only [beq_eq_false_iff_ne.2 hrawNe, beq_eq_false_iff_ne.2 hsameK, hnewEmp, Bool.false_eq_true, ↓reduceIte]
        have hnewKeysEq : disambiguateKeys (keys s₂) = #[] := Array.isEmpty_iff.1 hnewEmp; have hnewRows0 : rowsHtml s₂ = [] := List.eq_nil_of_length_eq_zero (by rw [hrowsClean.1 s₂, hnewKeysEq]; rfl)
        rw [ArenaM.bind_eq, stateM_bind_step (ArenaM.clearChildren_elem ha1Get)]
        exact keyedList_finish_goal ctx ((ha1Ext.set_right rfl).mono (fun _ h => h) (Nat.zero_le _)) (DomArena.get_set_self ..) hDyn₂ (by rw [hnewRows0]; trivial) hnewKeysEq.symm hnewRows0.symm
  | _ => exact False.elim hval.2

end
end Qed
