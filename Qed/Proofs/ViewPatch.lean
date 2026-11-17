import Qed.Proofs.DomArena

namespace Qed

/-! ## 2. Pure Diff & W3C `insertBefore` Keyed/Positional Reconciler Equivalence -/

/-- For every `old` and `new` `Html` tree, patching `old` with `diff old new` yields a `DomTree`
    identical to building `new` from scratch. -/
theorem specDom_applyPatch_diff (ns : String) (old new : Html msg) :
    specDom ns (applyPatch (diff old new) old) = specDom ns new := by
  rw [diff_apply]


/-! ## 4. Congruence-Sound Memoization (`View.memo`) & Duplicate-Key Safety (`V.forEach`) -/

/-- When `sm.keyOf s₂ = sm.keyOf s₁`, `patchViewM` on `.memo sm` performs **zero** DOM mutations
    (`a' = a`), preserves the exact `node` handle, and by `sm.sound` the existing DOM subtree is
    guaranteed equal to `specDom ns (View.render (.memo sm) s₂)`. -/
theorem patchViewM_memo_hit {σ msg : Type} (sm : SoundMemo σ msg)
    (s₁ s₂ : σ) (parent node : Dom.Node) (idx : UInt32) (a : DomArena msg) (fuel : Nat) (ns : String)
    (hkey : sm.keyOf s₂ = sm.keyOf s₁)
    (hdom : readDomTree fuel a node = specDom ns (View.render (.memo sm) s₁)) :
    let (vst', a') :=
      (patchViewM (m := StateM (DomArena msg)) parent idx (.memo sm) s₂
        (.memo node (sm.keyOf s₁) (sm.eval s₁))).run a
    a' = a ∧
    vst' = .memo node (sm.keyOf s₁) (sm.eval s₁) ∧
    readDomTree fuel a' node = specDom ns (View.render (.memo sm) s₂) := by
  have hbeq : (sm.keyOf s₂ == sm.keyOf s₁) = true := beq_iff_eq.2 hkey
  have heval : sm.eval s₂ = sm.eval s₁ := sm.sound s₂ s₁ hkey
  simp [patchViewM, StateT.run, pure, StateT.pure, hbeq, View.render, heval, hdom]

/-- Imperative `patchViewM` on `.dyn get` updates the DOM text node when changed and always
    leaves `readDomTree` equal to `specDom "" (View.render (.dyn get) s₂)`. -/
theorem patchViewM_dyn_spec {σ msg : Type} (get : σ → String) (s₁ s₂ : σ)
    (parent node : Dom.Node) (idx : UInt32) (a : DomArena msg) (fuel : Nat) (hf : 0 < fuel) :
    let a0 := a.set node (.text (get s₁))
    let (vst', a') :=
      (patchViewM (m := StateM (DomArena msg)) parent idx (.dyn get) s₂ (.dyn node (get s₁))).run a0
    vst' = .dyn node (get s₂) ∧
    readDomTree fuel a' node = specDom "" (View.render (.dyn get) s₂) := by
  cases fuel with
  | zero => omega
  | succ f =>
      dsimp only
      by_cases heq : get s₂ = get s₁
      · simp [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure,
              heq, readDomTree, DomArena.get_set_self, specDom, View.render]
      · simp [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, heq,
              MonadDom.setText, DomArena.modify, DomArena.get_set_self,
              readDomTree, specDom, View.render]

/-- Every keyed list produced by `V.forEach` (or patched/hydrated by `Template.lean`) disambiguates
    keys so that duplicate sibling keys are impossible (`Nodup` holds unconditionally). -/
theorem forEach_disambiguated_keys_nodup {α σ : Type} (items : σ → Array α) (key : α → String) (s : σ) :
    (disambiguateKeys ((items s).map key)).toList.Nodup :=
  disambiguateKeys_nodup ((items s).map key)

/-! ## 5. End-to-End Isomorphic SSR → Rehydrate → Client Equivalence (`App.ssr_rehydrate_equiv`) -/

/-- Crown-jewel isomorphic rendering theorem for every compiled Qed `App`:
    1. Every server-rendered view `app.view m` satisfies HTML5 & XSS validity (`Html.valid`).
    2. Whenever client `app.rehydrate (app.dehydrate m)` succeeds with `m'`, `m'` satisfies
       `Html.valid (app.view m') = true`, renders the **exact** same `Html` and serialized markup
       as the server (`app.view m' = app.view m`), and has the **exact** same `DomTree` (`specDom`).
    3. Every subsequent client message transition `msg : Msg` reconciled via `diff` produces the
       exact `DomTree` of a fresh render of `(app.update m' msg).1`. -/
theorem App.ssr_rehydrate_equiv {Model Msg : Type} (app : App Model Msg)
    (m m' : Model) (hre : app.rehydrate (app.dehydrate m) = some m') :
    Html.valid (app.view m) = true ∧
    Html.valid (app.view m') = true ∧
    app.view m' = app.view m ∧
    Html.render (app.view m') = Html.render (app.view m) ∧
    specDom "" (app.view m') = specDom "" (app.view m) ∧
    (∀ msg : Msg,
      specDom "" (applyPatch (diff (app.view m') (app.view (app.update m' msg).1)) (app.view m')) =
        specDom "" (app.view (app.update m' msg).1)) := by
  have hvalidM  : Html.valid (app.view m) = true := app.valid_view m
  have hvalidM' : Html.valid (app.view m') = true := app.valid_view m'
  have hview    : app.view m' = app.view m := app.dehydrate_view m m' hre
  refine ⟨hvalidM, hvalidM', hview, congrArg Html.render hview, congrArg (specDom "") hview, ?_⟩
  intro msg
  exact specDom_applyPatch_diff "" (app.view m') (app.view (app.update m' msg).1)


/-! ## 6. `applyAttrsM` Retention, `applyToDomM`, `patchViewM` & `diffRowSigs` -/

def lookupAssoc {α : Type} (k : String) : List (String × α) → Option α
  | [] => none
  | (k', v) :: rest => if k' == k then some v else lookupAssoc k rest

theorem lookupAssoc_setAssoc {α : Type} (k k' : String) (v : α) :
    ∀ (xs : List (String × α)),
      lookupAssoc k (setAssoc k' v xs) = if k' == k then some v else lookupAssoc k xs
  | [] => by simp [setAssoc, lookupAssoc]
  | (a, b) :: rest => by
      simp only [setAssoc]
      by_cases ha : a == k'
      · have heq : a = k' := eq_of_beq ha
        subst heq
        simp only [ha, ↓reduceIte, lookupAssoc]
        by_cases hk : a == k <;> simp [hk]
      · simp only [ha, Bool.false_eq_true, ↓reduceIte, lookupAssoc]
        by_cases hk : a == k
        · have heq : a = k := eq_of_beq hk
          subst heq
          have hne : (k' == a) = false := beq_eq_false_iff_ne.2 (fun h => ha (beq_iff_eq.2 h.symm))
          simp [hne]
        · simp only [hk, Bool.false_eq_true, ↓reduceIte]
          exact lookupAssoc_setAssoc k k' v rest

private theorem lookupAssoc_filter_false {α : Type} (p : String → Bool) (k : String)
    (hpF : p k = false) :
    ∀ (xs : List (String × α)),
      lookupAssoc k (xs.filter fun (k', _) => p k') = none
  | [] => rfl
  | (a, b) :: rest => by
      simp only [List.filter_cons]
      by_cases hpa : p a
      · simp only [hpa, ↓reduceIte, lookupAssoc]
        have hne : (a == k) = false := beq_eq_false_iff_ne.2 fun h => by subst h; simp [hpF] at hpa
        simp [hne, lookupAssoc_filter_false p k hpF rest]
      · simp only [hpa, Bool.false_eq_true, ↓reduceIte]
        exact lookupAssoc_filter_false p k hpF rest

theorem lookupAssoc_filter {α : Type} (p : String → Bool) (k : String) :
    ∀ (xs : List (String × α)),
      lookupAssoc k (xs.filter fun (k', _) => p k') =
        if p k then lookupAssoc k xs else none
  | [] => by simp [lookupAssoc]
  | (a, b) :: rest => by
      by_cases hpk : p k
      · simp only [hpk, ↓reduceIte, List.filter_cons]
        by_cases hpa : p a
        · simp only [hpa, ↓reduceIte, lookupAssoc]
          by_cases hak : a == k
          · simp [hak]
          · simp only [hak, Bool.false_eq_true, ↓reduceIte]
            simpa [hpk] using lookupAssoc_filter p k rest
        · simp only [hpa, Bool.false_eq_true, ↓reduceIte]
          have hak : (a == k) = false := beq_eq_false_iff_ne.2 fun h => by subst h; simp [hpk] at hpa
          simp only [lookupAssoc, hak, Bool.false_eq_true, ↓reduceIte]
          simpa [hpk] using lookupAssoc_filter p k rest
      · have hpkF : p k = false := Bool.eq_false_iff.2 hpk
        simp only [hpkF, Bool.false_eq_true, ↓reduceIte]
        exact lookupAssoc_filter_false p k hpkF ((a, b) :: rest)

theorem lookupAssoc_eraseAssoc {α : Type} (k k' : String) :
    ∀ (xs : List (String × α)),
      lookupAssoc k (eraseAssoc k' xs) = if k' == k then none else lookupAssoc k xs
  | [] => by simp [eraseAssoc, lookupAssoc]
  | (a, b) :: rest => by
      simp only [eraseAssoc]
      by_cases ha : a == k'
      · have heq : a = k' := eq_of_beq ha
        subst heq
        simp only [ha, ↓reduceIte]
        rw [lookupAssoc_eraseAssoc k a rest]
        by_cases hk : a == k
        · simp [hk]
        · simp [lookupAssoc, hk]
      · simp only [ha, Bool.false_eq_true, ↓reduceIte, lookupAssoc]
        by_cases hk : a == k
        · have heq : a = k := eq_of_beq hk
          subst heq
          have hne : (k' == a) = false := beq_eq_false_iff_ne.2 fun h => ha (beq_iff_eq.2 h.symm)
          simp [hne]
        · simp only [hk, Bool.false_eq_true, ↓reduceIte]
          exact lookupAssoc_eraseAssoc k k' rest

def ElemManaged (st : SpecElemState msg) (prev : List String) : Prop :=
  (∀ kv ∈ st.attrs, prev.contains kv.1 = true) ∧
  (st.value ≠ "" → prev.contains "value" = true) ∧
  (st.checked = true → prev.contains "checked" = true)

theorem ElemManaged_empty : ElemManaged ({} : SpecElemState msg) [] :=
  ⟨fun _ h => by simp at h, fun h => by simp at h, fun h => by simp at h⟩

private theorem stepSpecAttr_attrs_eq_or_none {msg : Type} (st₁ st₂ : SpecElemState msg)
    (a : Attr msg) (k : String)
    (hcur : lookupAssoc k st₁.attrs = lookupAssoc k st₂.attrs) :
    lookupAssoc k (stepSpecAttr st₁ a).attrs = lookupAssoc k (stepSpecAttr st₂ a).attrs := by
  cases a with
  | cls c => simp [stepSpecAttr, lookupAssoc_setAssoc, hcur]
  | attr k' v =>
      by_cases hv : k' = "value"
      · subst hv; simp [stepSpecAttr, hcur]
      · simp [stepSpecAttr, hv, lookupAssoc_setAssoc, hcur]
  | flag k' p =>
      by_cases hc : k' = "checked"
      · subst hc; simp [stepSpecAttr, hcur]
      · cases p <;> simp [stepSpecAttr, hc, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc, hcur]
  | key _ => simp [stepSpecAttr, hcur]
  | on _ _ => simp [stepSpecAttr, hcur]
  | onValue _ _ => simp [stepSpecAttr, hcur]
  | localCell key comp _ _ _ => simp [stepSpecAttr, lookupAssoc_setAssoc, hcur]
  | signalBind _ => simp [stepSpecAttr, hcur]
  | signalAttr _ _ _ => simp [stepSpecAttr, hcur]

private theorem stepSpecAttr_val_eq {msg : Type} (st₁ st₂ : SpecElemState msg) (a : Attr msg)
    (hval : st₁.value = st₂.value) :
    (stepSpecAttr st₁ a).value = (stepSpecAttr st₂ a).value := by
  cases a with
  | attr k' v =>
      by_cases hv : k' = "value"
      · subst hv; simp [stepSpecAttr]
      · simp [stepSpecAttr, hv, hval]
  | flag k' p =>
      by_cases hc : k' = "checked"
      · subst hc; simp [stepSpecAttr, hval]
      · simp [stepSpecAttr, hc, hval]
  | cls _ => simp [stepSpecAttr, hval]
  | key _ => simp [stepSpecAttr, hval]
  | on _ _ => simp [stepSpecAttr, hval]
  | onValue _ _ => simp [stepSpecAttr, hval]
  | localCell _ _ _ _ _ => simp [stepSpecAttr, hval]
  | signalBind _ => simp [stepSpecAttr, hval]
  | signalAttr _ _ _ => simp [stepSpecAttr, hval]

private theorem stepSpecAttr_chk_eq {msg : Type} (st₁ st₂ : SpecElemState msg) (a : Attr msg)
    (hchk : st₁.checked = st₂.checked) :
    (stepSpecAttr st₁ a).checked = (stepSpecAttr st₂ a).checked := by
  cases a with
  | attr k' v =>
      by_cases hv : k' = "value"
      · subst hv; simp [stepSpecAttr, hchk]
      · simp [stepSpecAttr, hv, hchk]
  | flag k' p =>
      by_cases hc : k' = "checked"
      · subst hc; simp [stepSpecAttr]
      · simp [stepSpecAttr, hc, hchk]
  | cls _ => simp [stepSpecAttr, hchk]
  | key _ => simp [stepSpecAttr, hchk]
  | on _ _ => simp [stepSpecAttr, hchk]
  | onValue _ _ => simp [stepSpecAttr, hchk]
  | localCell _ _ _ _ _ => simp [stepSpecAttr, hchk]
  | signalBind _ => simp [stepSpecAttr, hchk]
  | signalAttr _ _ _ => simp [stepSpecAttr, hchk]

private theorem stepSpecAttr_retains_managed {msg : Type} (st : SpecElemState msg)
    (a : Attr msg) (names : List String)
    (hkeep : match managedAttrName a with | some n => names.contains n = true | none => True)
    (hm : ElemManaged st names) :
    ElemManaged (stepSpecAttr st a) names := by
  rcases hm with ⟨ha, hv, hc⟩
  cases a with
  | cls c =>
      simp only [managedAttrName] at hkeep
      refine ⟨fun kv hkv => ?_, hv, hc⟩
      have hin : ∀ xs, (∀ p ∈ xs, names.contains p.1 = true) →
          ∀ p ∈ setAssoc "class" c xs, names.contains p.1 = true := by
        intro xs hxs p hp
        induction xs with
        | nil => simp [setAssoc] at hp; rcases hp with ⟨rfl, rfl⟩; exact hkeep
        | cons x rest ih =>
            simp only [setAssoc] at hp
            split at hp
            · rcases List.mem_cons.1 hp with rfl | hrest
              · exact hkeep
              · exact hxs p (List.mem_cons_of_mem x hrest)
            · rcases List.mem_cons.1 hp with rfl | hrest
              · exact hxs x (List.mem_cons_self ..)
              · exact ih (fun q hq => hxs q (List.mem_cons_of_mem x hq)) hrest
      exact hin st.attrs ha kv hkv
  | attr k' v =>
      simp only [managedAttrName] at hkeep
      by_cases hv' : k' = "value"
      · subst hv'; refine ⟨ha, fun _ => hkeep, hc⟩
      · refine ⟨fun kv hkv => ?_, fun h => hv (by simpa [stepSpecAttr, hv'] using h),
                fun h => hc (by simpa [stepSpecAttr, hv'] using h)⟩
        have hin : ∀ xs, (∀ p ∈ xs, names.contains p.1 = true) →
            ∀ p ∈ setAssoc k' v xs, names.contains p.1 = true := by
          intro xs hxs p hp
          induction xs with
          | nil => simp [setAssoc] at hp; rcases hp with ⟨rfl, rfl⟩; exact hkeep
          | cons x rest ih =>
              simp only [setAssoc] at hp
              split at hp
              · rcases List.mem_cons.1 hp with rfl | hrest
                · exact hkeep
                · exact hxs p (List.mem_cons_of_mem x hrest)
              · rcases List.mem_cons.1 hp with rfl | hrest
                · exact hxs x (List.mem_cons_self ..)
                · exact ih (fun q hq => hxs q (List.mem_cons_of_mem x hq)) hrest
        simp only [stepSpecAttr, hv'] at hkv
        exact hin st.attrs ha kv hkv
  | flag k' p =>
      simp only [managedAttrName] at hkeep
      by_cases hc' : k' = "checked"
      · subst hc'
        cases p <;> simp [stepSpecAttr]
        · exact ⟨ha, hv, fun h => absurd h Bool.false_ne_true⟩
        · exact ⟨ha, hv, fun _ => hkeep⟩
      · cases p
        · refine ⟨fun kv hkv => ?_, fun h => hv (by simpa [stepSpecAttr, hc'] using h),
                  fun h => hc (by simpa [stepSpecAttr, hc'] using h)⟩
          have her : ∀ (xs : List (String × String)), (∀ q ∈ xs, names.contains q.1 = true) →
              ∀ q ∈ eraseAssoc k' xs, names.contains q.1 = true := by
            intro xs hxs q hq
            induction xs with
            | nil => simp [eraseAssoc] at hq
            | cons x rest ih =>
                simp only [eraseAssoc] at hq
                split at hq
                · exact ih (fun z hz => hxs z (List.mem_cons_of_mem x hz)) hq
                · rcases List.mem_cons.1 hq with rfl | hrest
                  · exact hxs x (List.mem_cons_self ..)
                  · exact ih (fun z hz => hxs z (List.mem_cons_of_mem x hz)) hrest
          simp only [stepSpecAttr, hc', ↓reduceIte] at hkv
          exact her st.attrs ha kv hkv
        · refine ⟨fun kv hkv => ?_, fun h => hv (by simpa [stepSpecAttr, hc'] using h),
                  fun h => hc (by simpa [stepSpecAttr, hc'] using h)⟩
          have hin : ∀ xs, (∀ q ∈ xs, names.contains q.1 = true) →
              ∀ q ∈ setAssoc k' k' xs, names.contains q.1 = true := by
            intro xs hxs q hq
            induction xs with
            | nil => simp [setAssoc] at hq; rcases hq with ⟨rfl, rfl⟩; exact hkeep
            | cons x rest ih =>
                simp only [setAssoc] at hq
                split at hq
                · rcases List.mem_cons.1 hq with rfl | hrest
                  · exact hkeep
                  · exact hxs q (List.mem_cons_of_mem x hrest)
                · rcases List.mem_cons.1 hq with rfl | hrest
                  · exact hxs x (List.mem_cons_self ..)
                  · exact ih (fun z hz => hxs z (List.mem_cons_of_mem x hz)) hrest
          simp only [stepSpecAttr, hc', ↓reduceIte] at hkv
          exact hin st.attrs ha kv hkv
  | localCell key comp _ _ _ =>
      simp only [managedAttrName] at hkeep
      refine ⟨fun kv hkv => ?_, hv, hc⟩
      have hin : ∀ xs, (∀ p ∈ xs, names.contains p.1 = true) →
          ∀ p ∈ setAssoc "data-qed-local" (localKey comp key) xs, names.contains p.1 = true := by
        intro xs hxs p hp
        induction xs with
        | nil => simp [setAssoc] at hp; rcases hp with ⟨rfl, rfl⟩; exact hkeep
        | cons x rest ih =>
            simp only [setAssoc] at hp
            split at hp
            · rcases List.mem_cons.1 hp with rfl | hrest
              · exact hkeep
              · exact hxs p (List.mem_cons_of_mem x hrest)
            · rcases List.mem_cons.1 hp with rfl | hrest
              · exact hxs x (List.mem_cons_self ..)
              · exact ih (fun q hq => hxs q (List.mem_cons_of_mem x hq)) hrest
      exact hin st.attrs ha kv hkv
  | key _ => exact ⟨ha, hv, hc⟩
  | on _ _ => exact ⟨ha, hv, hc⟩
  | onValue _ _ => exact ⟨ha, hv, hc⟩
  | signalBind _ => exact ⟨ha, hv, hc⟩
  | signalAttr _ _ _ => exact ⟨ha, hv, hc⟩

def attrWritesKey (k : String) : Attr msg → Bool
  | .cls _            => k == "class"
  | .attr k' _        => k' != "value" && k' == k
  | .flag k' _        => k' != "checked" && k' == k
  | .localCell ..     => k == "data-qed-local"
  | _                 => false

private theorem stepSpecAttr_writes_indep {msg : Type} (s₁ s₂ : SpecElemState msg)
    (a : Attr msg) (k : String) (hw : attrWritesKey k a = true) :
    lookupAssoc k (stepSpecAttr s₁ a).attrs = lookupAssoc k (stepSpecAttr s₂ a).attrs := by
  cases a with
  | cls c =>
      simp only [attrWritesKey, beq_iff_eq] at hw
      subst hw
      simp [stepSpecAttr, lookupAssoc_setAssoc]
  | attr k' v =>
      simp only [attrWritesKey, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hw
      rcases hw with ⟨hne, rfl⟩
      simp [stepSpecAttr, hne, lookupAssoc_setAssoc]
  | flag k' p =>
      simp only [attrWritesKey, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hw
      rcases hw with ⟨hne, rfl⟩
      cases p <;> simp [stepSpecAttr, hne, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc]
  | localCell _ _ _ _ _ =>
      simp only [attrWritesKey, beq_iff_eq] at hw
      subst hw
      simp [stepSpecAttr, lookupAssoc_setAssoc]
  | key _ => simp [attrWritesKey] at hw
  | on _ _ => simp [attrWritesKey] at hw
  | onValue _ _ => simp [attrWritesKey] at hw
  | signalBind _ => simp [attrWritesKey] at hw
  | signalAttr _ _ _ => simp [attrWritesKey] at hw

private theorem stepSpecAttr_not_writes_preserves {msg : Type} (s : SpecElemState msg)
    (a : Attr msg) (k : String) (hnw : attrWritesKey k a = false) :
    lookupAssoc k (stepSpecAttr s a).attrs = lookupAssoc k s.attrs := by
  cases a with
  | cls c =>
      have hne : ("class" == k) = false := by
        simp only [attrWritesKey, beq_eq_false_iff_ne] at hnw
        exact beq_eq_false_iff_ne.2 hnw.symm
      simp [stepSpecAttr, lookupAssoc_setAssoc, hne]
  | attr k' v =>
      by_cases hv : k' = "value"
      · subst hv; simp [stepSpecAttr]
      · have hne : (k' == k) = false := by
          simp only [attrWritesKey, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hnw
          rcases hnw with heq | hne
          · exact absurd heq hv
          · exact hne
        simp [stepSpecAttr, hv, lookupAssoc_setAssoc, hne]
  | flag k' p =>
      by_cases hc : k' = "checked"
      · subst hc; simp [stepSpecAttr]
      · have hne : (k' == k) = false := by
          simp only [attrWritesKey, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at hnw
          rcases hnw with heq | hne
          · exact absurd heq hc
          · exact hne
        cases p <;> simp [stepSpecAttr, hc, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc, hne]
  | localCell _ _ _ _ _ =>
      have hne : ("data-qed-local" == k) = false := by
        simp only [attrWritesKey, beq_eq_false_iff_ne] at hnw
        exact beq_eq_false_iff_ne.2 hnw.symm
      simp [stepSpecAttr, lookupAssoc_setAssoc, hne]
  | key _ => rfl
  | on _ _ => rfl
  | onValue _ _ => rfl
  | signalBind _ => rfl
  | signalAttr _ _ _ => rfl

private theorem foldl_stepSpecAttr_writes {msg : Type} (k : String) :
    ∀ (xs : List (Attr msg)) (s₁ s₂ : SpecElemState msg),
      (∃ a ∈ xs, attrWritesKey k a = true) →
      lookupAssoc k (xs.foldl stepSpecAttr s₁).attrs =
        lookupAssoc k (xs.foldl stepSpecAttr s₂).attrs
  | [], _, _, ⟨_, h, _⟩ => nomatch h
  | x :: rest, s₁, s₂, ⟨a, ha, hwa⟩ => by
      simp only [List.foldl_cons]
      by_cases hrest : ∃ b ∈ rest, attrWritesKey k b = true
      · exact foldl_stepSpecAttr_writes k rest _ _ hrest
      · have hx : a = x := by
          rcases List.mem_cons.1 ha with rfl | hmem
          · rfl
          · exact False.elim (hrest ⟨a, hmem, hwa⟩)
        subst hx
        have hnw : ∀ b ∈ rest, attrWritesKey k b = false := by
          intro b hb
          cases hbw : attrWritesKey k b with
          | false => rfl
          | true => exact False.elim (hrest ⟨b, hb, hbw⟩)
        have hpres : ∀ (ys : List (Attr msg)) (s : SpecElemState msg),
            (∀ b ∈ ys, attrWritesKey k b = false) →
            lookupAssoc k (ys.foldl stepSpecAttr s).attrs = lookupAssoc k s.attrs := by
          intro ys
          induction ys with
          | nil => intro s _; rfl
          | cons y yr ihy =>
              intro s hy
              simp only [List.foldl_cons]
              rw [ihy _ (fun z hz => hy z (List.mem_cons_of_mem y hz))]
              exact stepSpecAttr_not_writes_preserves s y k (hy y (List.mem_cons_self ..))
        rw [hpres rest _ hnw, hpres rest _ hnw]
        exact stepSpecAttr_writes_indep s₁ s₂ a k hwa

private theorem foldl_stepSpecAttr_not_writes {msg : Type} (k : String) :
    ∀ (xs : List (Attr msg)) (s : SpecElemState msg),
      (∀ a ∈ xs, attrWritesKey k a = false) →
      lookupAssoc k (xs.foldl stepSpecAttr s).attrs = lookupAssoc k s.attrs
  | [], s, _ => rfl
  | x :: rest, s, hnw => by
      simp only [List.foldl_cons]
      rw [foldl_stepSpecAttr_not_writes k rest _ (fun z hz => hnw z (List.mem_cons_of_mem x hz))]
      exact stepSpecAttr_not_writes_preserves s x k (hnw x (List.mem_cons_self ..))

private theorem lookupAssoc_mem {α : Type} {k : String} {v : α} :
    ∀ {xs : List (String × α)}, lookupAssoc k xs = some v → (k, v) ∈ xs
  | [], h => by simp [lookupAssoc] at h
  | (a, b) :: rest, h => by
      simp only [lookupAssoc] at h
      split at h
      · rename_i heq
        have hakeq : a = k := eq_of_beq heq
        subst hakeq; cases h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (lookupAssoc_mem h)

private theorem foldl_stepSpecAttr_val {msg : Type} :
    ∀ (xs : List (Attr msg)) (s₁ s₂ : SpecElemState msg),
      (s₁.value = s₂.value ∨ ∃ v, .attr "value" v ∈ xs) →
      (xs.foldl stepSpecAttr s₁).value = (xs.foldl stepSpecAttr s₂).value
  | [], _, _, .inl h => h
  | [], _, _, .inr ⟨_, h⟩ => nomatch h
  | x :: rest, s₁, s₂, h => by
      simp only [List.foldl_cons]
      apply foldl_stepSpecAttr_val rest
      rcases h with heq | ⟨v, hv⟩
      · left; exact stepSpecAttr_val_eq s₁ s₂ x heq
      · rcases List.mem_cons.1 hv with rfl | hrest
        · left; rfl
        · right; exact ⟨v, hrest⟩

private theorem foldl_stepSpecAttr_chk {msg : Type} :
    ∀ (xs : List (Attr msg)) (s₁ s₂ : SpecElemState msg),
      (s₁.checked = s₂.checked ∨ ∃ p, .flag "checked" p ∈ xs) →
      (xs.foldl stepSpecAttr s₁).checked = (xs.foldl stepSpecAttr s₂).checked
  | [], _, _, .inl h => h
  | [], _, _, .inr ⟨_, h⟩ => nomatch h
  | x :: rest, s₁, s₂, h => by
      simp only [List.foldl_cons]
      apply foldl_stepSpecAttr_chk rest
      rcases h with heq | ⟨p, hp⟩
      · left; exact stepSpecAttr_chk_eq s₁ s₂ x heq
      · rcases List.mem_cons.1 hp with rfl | hrest
        · left; rfl
        · right; exact ⟨p, hrest⟩

/-- Attribute-retention theorem for reused DOM elements: running `applyAttrsM node newAttrs` on any
    element whose state satisfies `ElemManaged st prev` resets dropped `value`/`checked`/attributes,
    updates all new attributes to match `evalSpecAttrs newAttrs`, and preserves `ElemManaged`. -/
theorem applyAttrsM_existing_element (a : DomArena msg) (node : Dom.Node)
    (ns tag : String) (st : SpecElemState msg) (prev : List String) (cs : List Dom.Node)
    (newAttrs : List (Attr msg)) (hm : ElemManaged st prev)
    (hNoShadow :
      (∀ k, ((normalizeAttrs newAttrs).filterMap managedAttrName).contains k = true →
        (∃ x ∈ normalizeAttrs newAttrs, attrWritesKey k x = true) ∨ lookupAssoc k st.attrs = none) ∧
      (((normalizeAttrs newAttrs).filterMap managedAttrName).contains "value" = true →
        (∃ v, .attr "value" v ∈ normalizeAttrs newAttrs) ∨ st.value = "") ∧
      (((normalizeAttrs newAttrs).filterMap managedAttrName).contains "checked" = true →
        (∃ p, .flag "checked" p ∈ normalizeAttrs newAttrs) ∨ st.checked = false)) :
    let norm := normalizeAttrs newAttrs
    let names := norm.filterMap managedAttrName
    let a' := (applyAttrsM (m := StateM (DomArena msg)) node newAttrs
      (a.set node (.element ns tag st prev cs))).2
    ∃ st',
      a'.get node = .element ns tag st' names cs ∧
      (∀ k, lookupAssoc k st'.attrs = lookupAssoc k (evalSpecAttrs newAttrs).attrs) ∧
      st'.value = (evalSpecAttrs newAttrs).value ∧
      st'.checked = (evalSpecAttrs newAttrs).checked ∧
      ElemManaged st' names := by
  dsimp only [applyAttrsM, bind, StateT.bind, MonadDom.retainAttributes, DomArena.modify]
  rw [DomArena.get_set_self, DomArena.set_set]
  let norm := normalizeAttrs newAttrs
  let names := norm.filterMap managedAttrName
  let val' := if prev.contains "value" && !names.contains "value" then "" else st.value
  let chk' := if prev.contains "checked" && !names.contains "checked" then false else st.checked
  let attrs' := st.attrs.filter fun (k, _) => !prev.contains k || names.contains k
  let st0 : SpecElemState msg := { st with attrs := attrs', value := val', checked := chk' }
  rw [applyAttrListM_element norm a node ns tag st0 names cs]
  rw [DomArena.get_set_self]
  refine ⟨norm.foldl stepSpecAttr st0, rfl, ?_, ?_, ?_, ?_⟩
  · intro k
    change lookupAssoc k (norm.foldl stepSpecAttr st0).attrs =
      lookupAssoc k (norm.foldl stepSpecAttr {} ).attrs
    by_cases hw : ∃ x ∈ norm, attrWritesKey k x = true
    · exact foldl_stepSpecAttr_writes k norm st0 {} hw
    · have hnw : ∀ x ∈ norm, attrWritesKey k x = false := by
        intro x hx
        cases hkx : attrWritesKey k x with
        | false => rfl
        | true => exact False.elim (hw ⟨x, hx, hkx⟩)
      rw [foldl_stepSpecAttr_not_writes k norm st0 hnw,
          foldl_stepSpecAttr_not_writes k norm {} hnw]
      change lookupAssoc k attrs' = none
      cases hl : lookupAssoc k attrs' with
      | none => rfl
      | some v =>
          exfalso
          have hmem := lookupAssoc_mem hl
          simp only [attrs', List.mem_filter] at hmem
          have hprev := hm.1 (k, v) hmem.1
          simp only [hprev, Bool.not_true, Bool.false_or] at hmem
          rcases hNoShadow.1 k hmem.2 with hw' | hnoneSt
          · exact hw hw'
          · have hinSt : lookupAssoc k st.attrs ≠ none := by
              have hmem1 : (k, v) ∈ st.attrs := hmem.1
              clear hmem hprev hl hnw hw
              generalize st.attrs = xs at hmem1
              induction xs with
              | nil => nomatch hmem1
              | cons kv rest ih =>
                  rcases List.mem_cons.1 hmem1 with heq | hrest
                  · rw [← heq]; simp [lookupAssoc]
                  · simp only [lookupAssoc]
                    split
                    · intro hno; contradiction
                    · exact ih hrest
            exact hinSt hnoneSt
  · change (norm.foldl stepSpecAttr st0).value = (norm.foldl stepSpecAttr {}).value
    apply foldl_stepSpecAttr_val norm st0 {}
    by_cases hv : ∃ v, .attr "value" v ∈ norm
    · exact .inr hv
    · left
      change val' = ""
      dsimp only [val']
      by_cases hnv : names.contains "value" = true
      · simp only [hnv, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        rcases hNoShadow.2.1 hnv with hv' | hst
        · exact False.elim (hv hv')
        · exact hst
      · have hnvF : names.contains "value" = false := Bool.eq_false_iff.2 hnv
        by_cases hst : st.value = ""
        · simp only [hnvF, Bool.not_false, Bool.and_true]
          cases prev.contains "value" <;> simp [hst]
        · have hpv := hm.2.1 hst
          simp only [hpv, hnvF, Bool.not_false, Bool.and_self, ↓reduceIte]
  · change (norm.foldl stepSpecAttr st0).checked = (norm.foldl stepSpecAttr {}).checked
    apply foldl_stepSpecAttr_chk norm st0 {}
    by_cases hc : ∃ p, .flag "checked" p ∈ norm
    · exact .inr hc
    · left
      change chk' = false
      dsimp only [chk']
      by_cases hnc : names.contains "checked" = true
      · simp only [hnc, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        rcases hNoShadow.2.2 hnc with hc' | hst
        · exact False.elim (hc hc')
        · exact hst
      · have hncF : names.contains "checked" = false := Bool.eq_false_iff.2 hnc
        cases hst : st.checked
        · simp only [hncF, Bool.not_false, Bool.and_true]
          cases prev.contains "checked" <;> simp [hst]
        · have hpc := hm.2.2 hst
          simp only [hpc, hncF, Bool.not_false, Bool.and_self, ↓reduceIte]
  · have hm0 : ElemManaged st0 names := by
      refine ⟨?_, ?_, ?_⟩
      · intro kv hkv
        simp only [st0, attrs', List.mem_filter] at hkv
        have hprev := hm.1 kv hkv.1
        simp only [hprev, Bool.not_true, Bool.false_or] at hkv
        exact hkv.2
      · intro hne
        by_cases hnv : names.contains "value" = true
        · exact hnv
        · have hnvF : names.contains "value" = false := Bool.eq_false_iff.2 hnv
          by_cases hpv : prev.contains "value" = true
          · simp only [st0, val', hpv, hnvF, Bool.not_false, Bool.and_self, ↓reduceIte] at hne
            exact absurd rfl hne
          · have hstEmpty : st.value = "" :=
              if hst : st.value = "" then hst else False.elim (hpv (hm.2.1 hst))
            simp only [st0, val', hstEmpty, Bool.and_not_self] at hne
            cases hpvc : prev.contains "value" <;> simp [hpvc, hnvF] at hne
      · intro hchk
        by_cases hnc : names.contains "checked" = true
        · exact hnc
        · have hncF : names.contains "checked" = false := Bool.eq_false_iff.2 hnc
          by_cases hpc : prev.contains "checked" = true
          · simp only [st0, chk', hpc, hncF, Bool.not_false, Bool.and_self, ↓reduceIte] at hchk
            exact absurd hchk Bool.false_ne_true
          · have hstFalse : st.checked = false := by
              cases hsc : st.checked with
              | false => rfl
              | true => exact False.elim (hpc (hm.2.2 hsc))
            simp only [st0, chk', hstFalse, Bool.and_not_self] at hchk
            cases hpcc : prev.contains "checked" <;> simp [hpcc, hncF] at hchk
    have hpres : ∀ (xs : List (Attr msg)) (s : SpecElemState msg),
        (∀ x ∈ xs, match managedAttrName x with | some n => names.contains n = true | none => True) →
        ElemManaged s names →
        ElemManaged (xs.foldl stepSpecAttr s) names := by
      intro xs
      induction xs with
      | nil => intro s _ h; exact h
      | cons x rest ih =>
          intro s hx hs
          apply ih _ (fun y hy => hx y (List.mem_cons_of_mem x hy))
          exact stepSpecAttr_retains_managed s x names (hx x (List.mem_cons_self ..)) hs
    apply hpres norm st0 _ hm0
    intro x hx
    cases hmName : managedAttrName x with
    | none => trivial
    | some n =>
        apply List.contains_iff_mem.2
        exact List.mem_filterMap.2 ⟨x, hx, hmName⟩

/-! ## 7. `applyToDomM`, `removeTailM`, `buildViewM`, `patchViewM`, `diffRowSigs` & `hydrateDomM` -/

theorem applyToDomM_setText_spec (a : DomArena msg) (parent node : Dom.Node) (idx : UInt32)
    (sOld sNew : String) (fuel : Nat) (hf : 0 < fuel) :
    let a0 := a.set node (.text sOld)
    let a' := ((applyToDomM (m := StateM (DomArena msg)) parent idx node (.setText sNew)).run a0).2
    a'.get node = .text sNew ∧
    readDomTree fuel a' node = specDom "" (applyPatch (.setText sNew) (.text sOld)) := by
  cases fuel with
  | zero => omega
  | succ f =>
      simp [applyToDomM, StateT.run, MonadDom.setText, DomArena.modify, DomArena.get_set_self,
            readDomTree, applyPatch, specDom]

theorem applyToDomM_replace_spec (a : DomArena msg) (parent oldNode : Dom.Node) (idx : UInt32)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (pcs : List Dom.Node)
    (newHtml : Html msg) (fuel : Nat)
    (hpos : 0 < a.nextId)
    (hpar : parent.toNat < a.nextId)
    (hbound : a.nextId + htmlNodeCount newHtml < UInt32.size)
    (hdep : htmlDepth newHtml ≤ fuel) :
    let a0 := a.set parent (.element pns ptag pst pmg pcs)
    let a' := ((applyToDomM (m := StateM (DomArena msg)) parent idx oldNode (.replace newHtml)).run a0).2
    let childNs := if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else ""
    ∃ (newNode : Dom.Node) (cs' : List Dom.Node),
      a'.get parent = .element pns ptag pst pmg cs' ∧
      cs' = listReplaceAt pcs idx.toNat newNode ∧
      readDomTree fuel a' newNode = specDom childNs newHtml := by
  let a0 := a.set parent (.element pns ptag pst pmg pcs)
  have ha0Next : a0.nextId = a.nextId := rfl
  let childNs := if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else ""
  have hchildNs : (MonadDom.childNamespace (m := StateM (DomArena msg)) parent) a0 =
      (childNs, a0) := by
    simp [MonadDom.childNamespace, a0, DomArena.get_set_self, childNs]
  have hbuild := buildDomM_spec childNs newHtml a0 fuel hpos hbound hdep
  rcases hbuild with ⟨hge, hlt, _, hframe, hsub, hread⟩
  let res := buildDomM (m := StateM (DomArena msg)) childNs newHtml a0
  let newNode := res.1
  let aMid := res.2
  have hrun : ((applyToDomM (m := StateM (DomArena msg)) parent idx oldNode (.replace newHtml)).run
      (a.set parent (.element pns ptag pst pmg pcs))).2 =
      aMid.set parent (.element pns ptag pst pmg (listReplaceAt pcs idx.toNat newNode)) := by
    dsimp only [applyToDomM, StateT.run, bind, StateT.bind, MonadDom.childNamespace]
    rw [DomArena.get_set_self]
    dsimp only
    have hres : buildDomM (m := StateM (DomArena msg)) childNs newHtml a0 = (newNode, aMid) := rfl
    change (match buildDomM (m := StateM (DomArena msg)) childNs newHtml a0 with
            | (newNode', aMid') =>
              MonadDom.replaceChild (m := StateM (DomArena msg)) parent idx newNode' aMid').2 = _
    rw [hres]
    dsimp only [MonadDom.replaceChild, DomArena.modifyChildren, DomArena.modify]
    have hparMid : aMid.get parent = .element pns ptag pst pmg pcs := by
      rw [hframe parent (by omega)]
      simp [a0, DomArena.get_set_self]
    rw [hparMid]
  refine ⟨newNode, listReplaceAt pcs idx.toNat newNode, ?_, rfl, ?_⟩
  · rw [hrun, DomArena.get_set_self]
  · rw [hrun]
    have hfr := SubtreeInRange_frame (a := aMid)
      (a' := aMid.set parent (.element pns ptag pst pmg (listReplaceAt pcs idx.toNat newNode)))
      (lo := a0.nextId) (hi := aMid.nextId) (n := newNode)
      (fun m hm _ => by
        have hne : m ≠ parent := by intro heq; subst heq; omega
        exact DomArena.get_set_ne _ _ hne)
      hsub
    exact hfr.2.trans hread

private theorem buildDomM_not_fragment {msg : Type} (ns : String) :
    ∀ (h : Html msg) (a : DomArena msg) (fuel : Nat) (fcs : List Dom.Node),
      0 < a.nextId →
      a.nextId + htmlNodeCount h < UInt32.size →
      htmlDepth h ≤ fuel →
      let (root, a') := (buildDomM (m := StateM (DomArena msg)) ns h).run a
      a'.get root ≠ .fragment fcs
  | .text s, a, _, _, _, _, _ => by
      simp [buildDomM, StateT.run, MonadDom.createText, DomArena.alloc, DomArena.get]
  | .element tag attrs cs, a, fuel, fcs, hpos, hbound, hdep => by
      have hspec := buildDomM_spec ns (.element tag attrs cs) a fuel hpos hbound hdep
      rcases hspec with ⟨_, _, _, _, _, hread⟩
      intro hfrag
      cases fuel with
      | zero => simp [htmlDepth] at hdep
      | succ f =>
          dsimp only [readDomTree, specDom] at hread
          rw [hfrag] at hread
          cases hread

mutual
  /-- Well-formedness for direct `View` building: no `.keyedList` subtrees (whose signal names are
      instance-prefixed) and no non-empty child list inside `ownsChildren` elements (guaranteed for
      every `Html.valid` template). -/
  def View.DirectRenderSafe {σ msg : Type} (s : σ) : View σ msg → Bool
    | .text _ | .dyn _ | .static _ | .dynNode _ | .memo _ => true
    | .element _ attrs kids =>
        (!ownsChildren (attrs.map (VAttr.eval s)) || kids.isEmpty) &&
        View.DirectRenderSafeEach s kids
    | .ifElse cond y n => if cond s then y.DirectRenderSafe s else n.DirectRenderSafe s
    | .keyedList .. => false

  def View.DirectRenderSafeEach {σ msg : Type} (s : σ) : List (View σ msg) → Bool
    | [] => true
    | k :: ks => k.DirectRenderSafe s && View.DirectRenderSafeEach s ks
end

mutual
  /-- Full imperative `buildViewM` simulation on `DomArena`: builds a fresh subtree whose
      `readDomTree` matches `specDom ns (View.render v s)`, leaving all nodes `< a.nextId` untouched. -/
  theorem buildViewM_spec {σ msg : Type} (ns : String) :
      ∀ (v : View σ msg) (s : σ) (a : DomArena msg) (fuel : Nat),
        v.DirectRenderSafe s = true →
        0 < a.nextId →
        a.nextId + htmlNodeCount (View.render v s) < UInt32.size →
        htmlDepth (View.render v s) ≤ fuel →
        let ((root, _), a') := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
        a.nextId ≤ root.toNat ∧
        root.toNat < a'.nextId ∧
        a'.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
        (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
        SubtreeInRange fuel a' a.nextId a'.nextId root ∧
        readDomTree fuel a' root = specDom ns (View.render v s) ∧
        (∀ fcs, a'.get root ≠ .fragment fcs)
    | .text str, s, a, fuel, _, hpos, hbound, hdep =>
        let ⟨h1, h2, h3, h4, h5, h6⟩ := buildDomM_spec ns (.text str) a fuel hpos hbound hdep
        ⟨h1, h2, h3, h4, h5, h6, fun fcs => buildDomM_not_fragment ns (.text str) a fuel fcs hpos hbound hdep⟩
    | .dyn get, s, a, fuel, _, hpos, hbound, hdep =>
        let ⟨h1, h2, h3, h4, h5, h6⟩ := buildDomM_spec ns (.text (get s)) a fuel hpos hbound hdep
        ⟨h1, h2, h3, h4, h5, h6, fun fcs => buildDomM_not_fragment ns (.text (get s)) a fuel fcs hpos hbound hdep⟩
    | .static h, s, a, fuel, _, hpos, hbound, hdep =>
        let ⟨h1, h2, h3, h4, h5, h6⟩ := buildDomM_spec ns h a fuel hpos hbound hdep
        ⟨h1, h2, h3, h4, h5, h6, fun fcs => buildDomM_not_fragment ns h a fuel fcs hpos hbound hdep⟩
    | .dynNode get, s, a, fuel, _, hpos, hbound, hdep =>
        let ⟨h1, h2, h3, h4, h5, h6⟩ := buildDomM_spec ns (get s) a fuel hpos hbound hdep
        ⟨h1, h2, h3, h4, h5, h6, fun fcs => buildDomM_not_fragment ns (get s) a fuel fcs hpos hbound hdep⟩
    | .memo sm, s, a, fuel, _, hpos, hbound, hdep =>
        let ⟨h1, h2, h3, h4, h5, h6⟩ := buildDomM_spec ns (sm.eval s) a fuel hpos hbound hdep
        ⟨h1, h2, h3, h4, h5, h6, fun fcs => buildDomM_not_fragment ns (sm.eval s) a fuel fcs hpos hbound hdep⟩
    | .ifElse cond yes no, s, a, fuel, hsafe, hpos, hbound, hdep => by
        dsimp only [View.DirectRenderSafe] at hsafe
        cases hc : cond s
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hsafe
          have hbound' : a.nextId + htmlNodeCount (View.render no s) < UInt32.size := by
            simpa [View.render, hc] using hbound
          have hdep' : htmlDepth (View.render no s) ≤ fuel := by
            simpa [View.render, hc] using hdep
          have ih := buildViewM_spec ns no s a fuel hsafe hpos hbound' hdep'
          simpa [buildViewM, View.render, hc] using ih
        · simp only [hc, ↓reduceIte] at hsafe
          have hbound' : a.nextId + htmlNodeCount (View.render yes s) < UInt32.size := by
            simpa [View.render, hc] using hbound
          have hdep' : htmlDepth (View.render yes s) ≤ fuel := by
            simpa [View.render, hc] using hdep
          have ih := buildViewM_spec ns yes s a fuel hsafe hpos hbound' hdep'
          simpa [buildViewM, View.render, hc] using ih
    | .element tag attrs kids, s, a, fuel, hsafe, hpos, hbound, hdep => by
        cases fuel with
        | zero => simp [View.render, htmlDepth] at hdep
        | succ f =>
            simp only [View.DirectRenderSafe, Bool.and_eq_true, Bool.or_eq_true,
                       Bool.not_eq_true'] at hsafe
            rcases hsafe with ⟨hownOrEmpty, hkidsSafe⟩
            simp only [View.render, htmlNodeCount] at hbound ⊢
            simp only [View.render, htmlDepth] at hdep
            have hlt0 : a.nextId < UInt32.size := by omega
            let node := UInt32.ofNat a.nextId
            have hnodeNat : node.toNat = a.nextId := UInt32.toNat_ofNat_of_lt hlt0
            let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
            let evAttrs := attrs.map (VAttr.eval s)
            let st := evalSpecAttrs evAttrs
            let mg := (normalizeAttrs evAttrs).filterMap managedAttrName
            let a1 : DomArena msg := { nextId := a.nextId + 1, store := a.store, signals := a.signals }
            have ha1Next : a1.nextId = a.nextId + 1 := rfl
            have ha1Get : ∀ m, a1.get m = a.get m := fun _ => rfl
            have hnodeLt1 : node.toNat < a1.nextId := by omega
            have hbound1 : a1.nextId + htmlListNodeCount (View.renderEach kids s) < UInt32.size := by omega
            have hdep1 : htmlListDepth (View.renderEach kids s) ≤ f := by omega
            have hattrs :
                applyAttrsM (m := StateM (DomArena msg)) node evAttrs (a1.set node (.element realNs tag {} [] [])) =
                  ((), a1.set node (.element realNs tag st mg [])) :=
              applyAttrsM_fresh_element a1 node realNs tag [] evAttrs
            have hkids := buildViewKidsM_spec (Dom.childNsOf ns tag) kids s a1 node realNs tag st mg [] f
              hkidsSafe hnodeLt1 (by omega) hbound1 hdep1 (by intro c hc; nomatch hc)
            dsimp only [StateT.run] at hkids
            rcases hkids with ⟨csNew, aBase', ha'Eq, hnextLe, hnextMono, hframe1, hsubKids, hreadKids⟩
            have hrun :
                (buildViewM (m := StateM (DomArena msg)) ns (.element tag attrs kids) s).run a =
                  ((node, VState.elem node (buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s
                    (a1.set node (.element realNs tag st mg []))).1),
                   (buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s
                    (a1.set node (.element realNs tag st mg []))).2) := by
              dsimp only [buildViewM, MonadDom.createElement, StateT.run, bind, StateT.bind, pure, StateT.pure]
              change (match applyAttrsM (m := StateM (DomArena msg)) node evAttrs
                        (a1.set node (.element realNs tag {} [] [])) with
                      | (_, s') =>
                        match buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s s' with
                        | (ks, s'') => ((node, VState.elem node ks), s'')) = _
              rw [hattrs]
              dsimp only
              cases buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s
                  (a1.set node (.element realNs tag st mg []))
              rfl
            rw [hrun]
            dsimp only
            have haBase'Next : aBase'.nextId =
                (buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s
                  (a1.set node (.element realNs tag st mg []))).2.nextId := by
              rw [ha'Eq]; rfl
            refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
            · intro m hm
              have hm1 : m.toNat < a1.nextId := by omega
              have hne : m ≠ node := by intro heq; subst heq; omega
              rw [ha'Eq, DomArena.get_set_ne _ _ hne]
              have h := hframe1 m hm1 hne
              rwa [DomArena.get_set_ne _ _ hne] at h
            · refine ⟨by omega, by omega, ?_⟩
              rw [ha'Eq, DomArena.get_set_self]
              intro c hc
              have hc' := hsubKids c hc
              rw [ha'Eq] at hc'
              exact SubtreeInRange_mono (by omega) (Nat.le_refl _) hc'
            · rw [ha'Eq] at hreadKids ⊢
              rcases hownOrEmpty with hownF | hemp
              · dsimp only [View.render, readDomTree, specDom]
                rw [DomArena.get_set_self]
                dsimp only
                rw [hownF]
                simpa [realNs, evAttrs, st, specDomList] using hreadKids
              · have hnil : kids = [] := List.isEmpty_iff.1 hemp
                subst hnil
                simp only [buildViewKidsM, pure, StateT.pure, View.renderEach, List.nil_append, List.map_nil] at ha'Eq hreadKids ⊢
                have hcsNil : csNew = [] := by
                  have hnodeEq :
                      (aBase'.set node (.element realNs tag st mg csNew)).get node =
                        (a1.set node (.element realNs tag st mg [])).get node := by
                    rw [← ha'Eq]
                  simp only [DomArena.get_set_self, ArenaEntry.element.injEq] at hnodeEq
                  exact hnodeEq.2.2.2.2
                subst hcsNil
                simp only [readDomTree, DomArena.get_set_self, specDom, List.map_nil]
                cases hown : ownsChildren evAttrs <;> simp [evAttrs, st, realNs, hown]
            · rw [ha'Eq, DomArena.get_set_self]
              intro fcs hfrag; cases hfrag

  theorem buildViewKidsM_spec {σ msg : Type} (childNs : String) :
      ∀ (ks : List (View σ msg)) (s : σ) (aBase : DomArena msg) (parent : Dom.Node)
        (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
        (acc : List Dom.Node) (f : Nat),
        View.DirectRenderSafeEach s ks = true →
        parent.toNat < aBase.nextId →
        0 < aBase.nextId →
        aBase.nextId + htmlListNodeCount (View.renderEach ks s) < UInt32.size →
        htmlListDepth (View.renderEach ks s) ≤ f →
        (∀ c ∈ acc, SubtreeInRange f (aBase.set parent (.element pns ptag pst pmg acc)) (parent.toNat + 1) aBase.nextId c) →
        let aIn := aBase.set parent (.element pns ptag pst pmg acc)
        let aOut := ((buildViewKidsM (m := StateM (DomArena msg)) childNs parent ks s).run aIn).2
        ∃ (csNew : List Dom.Node) (aBase' : DomArena msg),
          aOut = aBase'.set parent (.element pns ptag pst pmg (acc ++ csNew)) ∧
          aOut.nextId ≤ aBase.nextId + htmlListNodeCount (View.renderEach ks s) ∧
          aBase.nextId ≤ aOut.nextId ∧
          (∀ m : Dom.Node, m.toNat < aBase.nextId → m ≠ parent → aBase'.get m = aIn.get m) ∧
          (∀ c ∈ acc ++ csNew, SubtreeInRange f aOut (parent.toNat + 1) aOut.nextId c) ∧
          (acc ++ csNew).map (readDomTree f aOut) =
            acc.map (readDomTree f aIn) ++ specDomList childNs (View.renderEach ks s)
    | [], s, aBase, parent, pns, ptag, pst, pmg, acc, f, _, _, _, _, _, haccSub => by
        refine ⟨[], aBase, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [buildViewKidsM, StateT.run, pure, StateT.pure]
        · simp [buildViewKidsM, StateT.run, pure, StateT.pure, View.renderEach, htmlListNodeCount]
        · simp [buildViewKidsM, StateT.run, pure, StateT.pure]
        · intro m _ hne; simp [DomArena.get_set_ne _ _ hne]
        · simpa [buildViewKidsM, StateT.run, pure, StateT.pure] using haccSub
        · simp [buildViewKidsM, StateT.run, pure, StateT.pure, View.renderEach]
    | k :: rest, s, aBase, parent, pns, ptag, pst, pmg, acc, f, hsafe, hparLt, hpos, hbound, hdep, haccSub => by
        simp only [View.DirectRenderSafeEach, Bool.and_eq_true] at hsafe
        let aIn := aBase.set parent (.element pns ptag pst pmg acc)
        have haInNext : aIn.nextId = aBase.nextId := rfl
        simp only [View.renderEach, htmlListNodeCount] at hbound
        simp only [View.renderEach, htmlListDepth] at hdep
        have hkDep : htmlDepth (View.render k s) ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
        have hrestDep : htmlListDepth (View.renderEach rest s) ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
        have hfPos : 0 < f := by
          cases hkr : View.render k s <;> { simp [hkr, htmlDepth] at hkDep; omega }
        have hkSpec := buildViewM_spec childNs k s aIn f hsafe.1 (by omega) (by omega) hkDep
        dsimp only [StateT.run] at hkSpec
        let res1 := buildViewM (m := StateM (DomArena msg)) childNs k s aIn
        let cn := res1.1.1
        let aMid := res1.2
        rcases hkSpec with ⟨hcnGe, hcnLt, haMidLe, haMidFrame, hcnSub, hcnRead, hcnNotFrag⟩
        have hcnDef : (buildViewM (m := StateM (DomArena msg)) childNs k s aIn).1.1 = cn := rfl
        have haMidDef : (buildViewM (m := StateM (DomArena msg)) childNs k s aIn).2 = aMid := rfl
        rw [hcnDef] at hcnGe hcnLt hcnSub hcnRead hcnNotFrag
        rw [haMidDef] at hcnLt haMidLe haMidFrame hcnSub hcnRead hcnNotFrag
        have hparInMid : aMid.get parent = .element pns ptag pst pmg acc := by
          rw [haMidFrame parent (by omega)]
          simp [aIn, DomArena.get_set_self]
        have hcnNotInAcc : cn ∉ acc := by
          intro hmem
          have hsub := haccSub cn hmem
          cases f with
          | zero => omega
          | succ f' =>
              have hlt := hsub.2.1
              omega
        have heraseAcc : acc.erase cn = acc := List.erase_of_not_mem hcnNotInAcc
        let aAfterAppend := aMid.set parent (.element pns ptag pst pmg (acc ++ [cn]))
        have haAfterNext : aAfterAppend.nextId = aMid.nextId := rfl
        have happendRun :
            (MonadDom.appendChild (m := StateM (DomArena msg)) parent cn).run aMid = ((), aAfterAppend) := by
          cases hgetCn : aMid.get cn with
          | fragment fcs => exact False.elim (hcnNotFrag fcs hgetCn)
          | null | text _ | element _ _ _ _ _ =>
              simp [MonadDom.appendChild, StateT.run, hgetCn, DomArena.modify, hparInMid, heraseAcc, aAfterAppend]
        have haMidNext : aBase.nextId ≤ aMid.nextId := by omega
        have haccMid : ∀ x ∈ acc,
            SubtreeInRange f aAfterAppend (parent.toNat + 1) aMid.nextId x ∧
            readDomTree f aAfterAppend x = readDomTree f aIn x := by
          intro x hx
          have hsub0 := haccSub x hx
          have hfr := SubtreeInRange_frame (a := aIn) (a' := aAfterAppend)
            (lo := parent.toNat + 1) (hi := aBase.nextId) (n := x)
            (fun m hlo hhi => by
              have hne : m ≠ parent := by intro heq; subst heq; omega
              rw [DomArena.get_set_ne _ _ hne]
              exact haMidFrame m (by omega))
            hsub0
          exact ⟨SubtreeInRange_mono (Nat.le_refl _) haMidNext hfr.1, hfr.2⟩
        have hcnAfter :
            SubtreeInRange f aAfterAppend (parent.toNat + 1) aMid.nextId cn ∧
            readDomTree f aAfterAppend cn = specDom childNs (View.render k s) := by
          have hsubW := SubtreeInRange_mono (by omega : parent.toNat + 1 ≤ aIn.nextId) (Nat.le_refl _) hcnSub
          have hfr := SubtreeInRange_frame (a := aMid) (a' := aAfterAppend)
            (lo := parent.toNat + 1) (hi := aMid.nextId) (n := cn)
            (fun m hlo _ => by
              have hne : m ≠ parent := by intro heq; subst heq; omega
              exact DomArena.get_set_ne _ _ hne)
            hsubW
          exact ⟨hfr.1, hfr.2.trans hcnRead⟩
        have hsubComb :
            ∀ x ∈ acc ++ [cn], SubtreeInRange f aAfterAppend (parent.toNat + 1) aMid.nextId x := by
          intro x hx
          rcases List.mem_append.1 hx with hxAcc | hxCn
          · exact (haccMid x hxAcc).1
          · simp only [List.mem_singleton] at hxCn
            subst hxCn
            exact hcnAfter.1
        have hih := buildViewKidsM_spec childNs rest s aMid parent pns ptag pst pmg (acc ++ [cn]) f
          hsafe.2 (by omega) (by omega) (by omega) hrestDep hsubComb
        rcases hih with ⟨csRest, aBase'', haOutEq, hnextLe, hnextMono, hframeRest, hsubFinal, hreadFinal⟩
        have hstepRun :
            ((buildViewKidsM (m := StateM (DomArena msg)) childNs parent (k :: rest) s).run aIn).2 =
              ((buildViewKidsM (m := StateM (DomArena msg)) childNs parent rest s).run aAfterAppend).2 := by
          dsimp only [buildViewKidsM, StateT.run, bind, StateT.bind]
          change (match res1 with
                  | ((cn', _), aMid') =>
                    match (MonadDom.appendChild (m := StateM (DomArena msg)) parent cn').run aMid' with
                    | (_, aAfter') =>
                      (buildViewKidsM (m := StateM (DomArena msg)) childNs parent rest s).run aAfter').2 =
                 ((buildViewKidsM (m := StateM (DomArena msg)) childNs parent rest s).run aAfterAppend).2
          have hres1 : res1 = ((cn, res1.1.2), aMid) := rfl
          rw [hres1]
          dsimp only
          rw [happendRun]
        dsimp only
        simp only [View.renderEach, htmlListNodeCount]
        rw [hstepRun]
        dsimp only [aAfterAppend] at haccMid hcnAfter ⊢
        refine ⟨cn :: csRest, aBase'', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using haOutEq
        · dsimp only [StateT.run] at hnextLe ⊢; omega
        · dsimp only [StateT.run] at hnextMono ⊢; omega
        · intro m hm hne
          rw [hframeRest m (by omega) hne, DomArena.get_set_ne _ _ hne]
          exact haMidFrame m (by omega)
        · simpa [List.append_assoc] using hsubFinal
        · have hmapInit :
              (acc ++ [cn]).map (readDomTree f (aMid.set parent (.element pns ptag pst pmg (acc ++ [cn])))) =
                acc.map (readDomTree f aIn) ++ [specDom childNs (View.render k s)] := by
            rw [List.map_append, List.map_singleton, hcnAfter.2]
            congr 1
            apply List.map_congr_left
            intro x hx
            exact (haccMid x hx).2
          simpa [List.append_assoc, specDomList, hmapInit] using hreadFinal
end

theorem patchViewM_text_static_spec {σ msg : Type} (parent node : Dom.Node) (idx : UInt32)
    (a : DomArena msg) (s : σ) :
    (∀ str, (patchViewM (m := StateM (DomArena msg)) parent idx (.text str) s (.text node)).run a = (.text node, a)) ∧
    (∀ h, (patchViewM (m := StateM (DomArena msg)) parent idx (.static h) s (.stat node)).run a = (.stat node, a)) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem patchViewM_memo_miss_spec {σ msg : Type} (sm : SoundMemo σ msg)
    (s₁ s₂ : σ) (parent node : Dom.Node) (idx : UInt32) (a : DomArena msg)
    (hne : (sm.keyOf s₂ == sm.keyOf s₁) = false) :
    (patchViewM (m := StateM (DomArena msg)) parent idx (.memo sm) s₂
      (.memo node (sm.keyOf s₁) (sm.eval s₁))).run a =
      let (n', a') := (patchHtmlSubtreeM (m := StateM (DomArena msg)) parent idx node (sm.eval s₁) (sm.eval s₂)).run a
      (.memo n' (sm.keyOf s₂) (sm.eval s₂), a') := by
  dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
  rw [if_neg (by simp [hne])]
  dsimp only [StateT.bind]
  cases hsub : (patchHtmlSubtreeM (m := StateM (DomArena msg)) parent idx node (sm.eval s₁) (sm.eval s₂)) a
  rfl

theorem patchViewM_ifElse_flip_spec {σ msg : Type}
    (cond : σ → Bool) (yes no : View σ msg) (s : σ)
    (parent : Dom.Node) (idx : UInt32) (wasYes : Bool) (inner : VState σ msg)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (pcs : List Dom.Node)
    (a : DomArena msg) (fuel : Nat)
    (hflip : (cond s == wasYes) = false)
    (hsafe : (if cond s then yes else no).DirectRenderSafe s = true)
    (hpos : 0 < a.nextId)
    (hpar : parent.toNat < a.nextId)
    (hbound : a.nextId + htmlNodeCount (View.render (.ifElse cond yes no) s) < UInt32.size)
    (hdep : htmlDepth (View.render (.ifElse cond yes no) s) ≤ fuel) :
    let a0 := a.set parent (.element pns ptag pst pmg pcs)
    let childNs := if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else ""
    let (vst', a') := (patchViewM (m := StateM (DomArena msg)) parent idx (.ifElse cond yes no) s (.cond wasYes inner)).run a0
    ∃ (newNode : Dom.Node) (newInner : VState σ msg),
      vst' = .cond (cond s) newInner ∧
      a'.get parent = .element pns ptag pst pmg (listReplaceAt pcs idx.toNat newNode) ∧
      readDomTree fuel a' newNode = specDom childNs (View.render (.ifElse cond yes no) s) := by
  let a0 := a.set parent (.element pns ptag pst pmg pcs)
  have ha0Next : a0.nextId = a.nextId := rfl
  let childNs := if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else ""
  have hchildNs : (MonadDom.childNamespace (m := StateM (DomArena msg)) parent) a0 = (childNs, a0) := by
    simp [MonadDom.childNamespace, a0, DomArena.get_set_self, childNs]
  let targetV := if cond s then yes else no
  have hbuild := buildViewM_spec childNs targetV s a0 fuel hsafe hpos
    (by cases hc : cond s <;> simpa [targetV, View.render, hc] using hbound)
    (by cases hc : cond s <;> simpa [targetV, View.render, hc] using hdep)
  dsimp only [StateT.run] at hbuild
  rcases hbuild with ⟨hge, hlt, _, hframe, hsub, hread, _⟩
  let res := buildViewM (m := StateM (DomArena msg)) childNs targetV s a0
  let newNode := res.1.1
  let newInner := res.1.2
  let aMid := res.2
  have hparMid : aMid.get parent = .element pns ptag pst pmg pcs := by
    rw [hframe parent (by omega)]
    simp [a0, DomArena.get_set_self]
  have hrun : (patchViewM (m := StateM (DomArena msg)) parent idx (.ifElse cond yes no) s (.cond wasYes inner)).run
      (a.set parent (.element pns ptag pst pmg pcs)) =
      (.cond (cond s) newInner,
       aMid.set parent (.element pns ptag pst pmg (listReplaceAt pcs idx.toNat newNode))) := by
    simp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure,
               hflip, Bool.false_eq_true, ↓reduceIte, MonadDom.childNamespace, DomArena.get_set_self]
    cases hc : cond s with
    | true =>
        simp only [↓reduceIte]
        have hres : buildViewM (m := StateM (DomArena msg)) childNs yes s a0 = ((newNode, newInner), aMid) := by
          simp [newNode, newInner, aMid, res, targetV, hc]
          rfl
        dsimp only [childNs, a0] at hres
        dsimp only [StateT.bind]
        rw [hres]
        simp [bind, StateT.pure, MonadDom.replaceChild, DomArena.modifyChildren, DomArena.modify, hparMid]
        rfl
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hres : buildViewM (m := StateM (DomArena msg)) childNs no s a0 = ((newNode, newInner), aMid) := by
          simp [newNode, newInner, aMid, res, targetV, hc]
          rfl
        dsimp only [childNs, a0] at hres
        dsimp only [StateT.bind]
        rw [hres]
        simp [bind, StateT.pure, MonadDom.replaceChild, DomArena.modifyChildren, DomArena.modify, hparMid]
        rfl
  refine ⟨newNode, newInner, congrArg Prod.fst hrun,
    Eq.trans (congrArg (fun ar => ar.get parent) (congrArg Prod.snd hrun)) (DomArena.get_set_self _ _ _), ?_⟩
  refine Eq.trans (congrArg (fun ar => readDomTree fuel ar newNode) (congrArg Prod.snd hrun)) ?_
  dsimp only
  have hfr := SubtreeInRange_frame (a := aMid)
    (a' := aMid.set parent (.element pns ptag pst pmg (listReplaceAt pcs idx.toNat newNode)))
    (lo := a0.nextId) (hi := aMid.nextId) (n := newNode)
    (fun m hm _ => by
      have hne : m ≠ parent := by intro heq; subst heq; omega
      exact DomArena.get_set_ne _ _ hne)
    hsub
  have hviewEq : View.render (.ifElse cond yes no) s = View.render targetV s := by
    cases hc : cond s <;> simp [targetV, View.render, hc]
  rw [hviewEq]
  exact hfr.2.trans hread

/-- Soundness of `diffRowSigs` for `keyedList` fast-path updates:
    whenever every non-zero `refMark` match guarantees identical row signals (`m ≠ 0 → oldMarks[i]? = some m → rowSig i = oldSigs[i]`),
    every resulting row signature `newSigs[i]` equals `rowSig i` unconditionally! -/
theorem diffRowSigs_sound (rowSig : Nat → Array (String × String)) (inst : String)
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String)))
    (hmark : ∀ i, i < newMarks.size → newMarks[i]! ≠ 0 → oldMarks[i]? = some newMarks[i]! →
      rowSig i = oldSigs[i]?.getD #[]) :
    ∀ (i : Nat) (accSigs : Array (Array (String × String))) (accEmit : Array (String × String)),
      i ≤ newMarks.size →
      accSigs.size = i →
      (∀ k, k < i → accSigs[k]! = rowSig k) →
      let (outSigs, _) := diffRowSigs rowSig inst newMarks oldMarks oldSigs i accSigs accEmit
      outSigs.size = newMarks.size ∧
      ∀ k, k < newMarks.size → outSigs[k]! = rowSig k := by
  intro i
  induction hrem : newMarks.size - i generalizing i with
  | zero =>
      intro accSigs accEmit hiLe hsz hprev
      have hge : ¬ i < newMarks.size := by omega
      dsimp only
      rw [diffRowSigs.eq_1]
      simp only [hge, ↓reduceDIte]
      refine ⟨by omega, fun k hk => hprev k (by omega)⟩
  | succ d ih =>
      intro accSigs accEmit hiLe hsz hprev
      have hlt : i < newMarks.size := by omega
      dsimp only
      rw [diffRowSigs.eq_1]
      simp only [hlt, ↓reduceDIte]
      by_cases hskip : (newMarks[i] != 0 && oldMarks[i]? == some newMarks[i]) = true
      · simp only [hskip, ↓reduceIte]
        have hnz : newMarks[i]! ≠ 0 := by
          simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hskip
          simpa [hlt] using hskip.1
        have hold : oldMarks[i]? = some newMarks[i]! := by
          simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hskip
          simpa [hlt] using hskip.2
        have hsigEq : oldSigs[i]?.getD #[] = rowSig i := (hmark i hlt hnz hold).symm
        apply ih (i + 1) (by omega) (accSigs.push (oldSigs[i]?.getD #[])) accEmit (by omega) (by simp [hsz])
        intro k hk
        have hkLtPush : k < (accSigs.push (oldSigs[i]?.getD #[])).size := by simp [hsz]; omega
        by_cases hki : k < i
        · have hkLt : k < accSigs.size := by omega
          simpa [getElem!_pos (accSigs.push (oldSigs[i]?.getD #[])) k hkLtPush,
                 getElem!_pos accSigs k hkLt, Array.getElem_push_lt hkLt] using hprev k hki
        · have heq : k = i := by omega
          subst heq
          simp [getElem!_pos (accSigs.push (oldSigs[k]?.getD #[])) k hkLtPush,
                Array.getElem_push, hsz, hsigEq]
      · simp only [hskip, Bool.false_eq_true, ↓reduceIte]
        apply ih (i + 1) (by omega) (accSigs.push (rowSig i)) _ (by omega) (by simp [hsz])
        intro k hk
        have hkLtPush : k < (accSigs.push (rowSig i)).size := by simp [hsz]; omega
        by_cases hki : k < i
        · have hkLt : k < accSigs.size := by omega
          simpa [getElem!_pos (accSigs.push (rowSig i)) k hkLtPush,
                 getElem!_pos accSigs k hkLt, Array.getElem_push_lt hkLt] using hprev k hki
        · have heq : k = i := by omega
          subst heq
          simp [getElem!_pos (accSigs.push (rowSig i)) k hkLtPush,
                Array.getElem_push, hsz]


end Qed
