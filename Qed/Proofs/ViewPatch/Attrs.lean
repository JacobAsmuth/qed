import Qed.Proofs.DomArena

namespace Qed

section
variable {α σ msg : Type}

/-! ## 2. Pure Diff, Memo, Key Disambiguation & Isomorphic SSR Equivalence -/

theorem specDom_applyPatch_diff (ns : String) (old new : Html msg) :
    specDom ns (applyPatch (diff old new) old) = specDom ns new := by rw [diff_apply]

theorem patchViewM_memo_hit (sm : SoundMemo σ msg) (s₁ s₂ : σ) (parent node : Dom.Node) (idx : UInt32) (a : DomArena msg) (fuel : Nat) (ns : String)
    (hkey : sm.keyOf s₂ = sm.keyOf s₁) (hdom : readDomTree fuel a node = specDom ns (View.render (.memo sm) s₁)) :
    let (vst', a') := (patchViewM (m := StateM (DomArena msg)) parent idx (.memo sm) s₂ (.memo node (sm.keyOf s₁) (sm.eval s₁))).run a
    a' = a ∧ vst' = .memo node (sm.keyOf s₁) (sm.eval s₁) ∧ readDomTree fuel a' node = specDom ns (View.render (.memo sm) s₂) := by
  dsimp only [patchViewM, StateT.run, pure, StateT.pure]; rw [ite_eq_left (beq_iff_eq.2 hkey)]; exact ⟨rfl, rfl, by simpa only [View.render, sm.sound s₂ s₁ hkey] using hdom⟩

theorem patchViewM_dyn_spec (get : σ → String) (s₁ s₂ : σ) (parent node : Dom.Node) (idx : UInt32) (a : DomArena msg) (fuel : Nat) (hf : 0 < fuel) :
    let a0 := a.set node (.text (get s₁))
    let (vst', a') := (patchViewM (m := StateM (DomArena msg)) parent idx (.dyn get) s₂ (.dyn node (get s₁))).run a0
    vst' = .dyn node (get s₂) ∧ readDomTree fuel a' node = specDom "" (View.render (.dyn get) s₂) := by
  cases fuel with | zero => omega | succ _ =>
  dsimp only [patchViewM, StateT.run]; cases h : (get s₂ != get s₁)
  · simp only [Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, DomArena.get_set_self, readDomTree, specDom, View.render, bne_eq_false_iff_eq.1 h, and_self]
  · simp only [↓reduceIte, bind, StateT.bind, pure, StateT.pure, MonadDom.setText, DomArena.modify, DomArena.get_set_self, DomArena.set_set, readDomTree, specDom, View.render, and_self]

theorem forEach_disambiguated_keys_nodup (items : σ → Array α) (key : α → String) (s : σ) :
    (disambiguateKeys ((items s).map key)).toList.Nodup := disambiguateKeys_nodup ((items s).map key)

theorem App.ssr_rehydrate_equiv {Model Msg : Type} (app : App Model Msg) (m m' : Model) (hre : app.rehydrate (app.dehydrate m) = some m') :
    Html.valid (app.view m) = true ∧ Html.valid (app.view m') = true ∧ app.view m' = app.view m ∧
    Html.render (app.view m') = Html.render (app.view m) ∧ specDom "" (app.view m') = specDom "" (app.view m) ∧
    (∀ msg : Msg, specDom "" (applyPatch (diff (app.view m') (app.view (app.update m' msg).1)) (app.view m')) = specDom "" (app.view (app.update m' msg).1)) :=
  let h := app.dehydrate_view m m' hre
  ⟨app.valid_view m, app.valid_view m', h, congrArg Html.render h, congrArg (specDom "") h, fun msg => specDom_applyPatch_diff "" _ (app.view (app.update m' msg).1)⟩

/-! ## 3. Dynamic Attributes (`applyDynAttrsM_spec`) & Unified `VStateValid` -/

def VState.rootNode : VState σ msg → Dom.Node
  | .text n | .dyn n _ | .elem n _ | .list n .. | .tlist n .. | .stat n | .dynNode n _ | .memo n .. => n | .cond _ inner => inner.rootNode

def Attr.NormalKey : Attr msg → Bool | .attr "checked" _ | .flag "value" _ => false | _ => true

def dynValNoLaterStat : List (VAttr σ msg) → Bool
  | [] => true | .dynVal k _ :: rest => rest.all (fun | .stat a => a.key? != some k | _ => true) && dynValNoLaterStat rest | _ :: rest => dynValNoLaterStat rest

def VAttrListClean (attrs : List (VAttr σ msg)) : Prop :=
  (∀ s, ownsChildren (attrs.map (VAttr.eval s)) = false) ∧ (∀ s, (attrs.map (VAttr.eval s)).all Attr.DomClean = true) ∧
  (∀ s, (attrs.map (VAttr.eval s)).all Attr.NormalKey = true) ∧ dynValNoLaterStat attrs = true

def KeyedRowsClean (keys : σ → Array String) (rowsHtml : σ → List (Html msg)) : Prop :=
  (∀ s, (rowsHtml s).length = (disambiguateKeys (keys s)).size) ∧ (∀ s, Html.DomCleanList (rowsHtml s) = true) ∧
  (∀ s r, r ∈ rowsHtml s → r.textOf? = none) ∧
  (∀ s₁ s₂ (i j : Nat) (hi : i < (disambiguateKeys (keys s₁)).size) (hj : j < (disambiguateKeys (keys s₂)).size),
    (disambiguateKeys (keys s₁))[i] = (disambiguateKeys (keys s₂))[j] → (rowsHtml s₁)[i]? = (rowsHtml s₂)[j]?)

mutual
  def View.DomClean : View σ msg → Prop
    | .text _ | .dyn _ => True | .static h => h.DomClean = true | .dynNode get => ∀ s, (get s).DomClean = true
    | .memo sm => ∀ s, (sm.eval s).DomClean = true | .ifElse _ y n => View.DomClean y ∧ View.DomClean n
    | .element _ attrs kids => VAttrListClean attrs ∧ View.DomCleanEach kids
    | .keyedList _ attrs keys _ _ _ rowsHtml none => VAttrListClean attrs ∧ KeyedRowsClean keys rowsHtml
    | .keyedList _ _ _ _ _ _ _ (some _) => False
  def View.DomCleanEach : List (View σ msg) → Prop
    | [] => True | k :: ks => View.DomClean k ∧ View.DomCleanEach ks
end

mutual
  theorem View.DomClean_render : ∀ {v : View σ msg}, View.DomClean v → ∀ s, (View.render v s).DomClean = true
    | .text _, _, _ | .dyn _, _, _ => rfl | .static _, h, _ => h | .dynNode _, h, s | .memo _, h, s => h s
    | .ifElse c _ _, ⟨hy, hn⟩, s => by cases hc : c s <;> simp [View.render, hc, View.DomClean_render hy s, View.DomClean_render hn s]
    | .element _ _ _, ⟨ha, hks⟩, s => by simp [View.render, Html.DomClean, ha.1 s, ha.2.1 s, View.DomCleanEach_renderEach hks s]
    | .keyedList _ _ _ _ _ _ _ none, ⟨ha, hrows⟩, s => by simp [View.render, Html.DomClean, ha.1 s, ha.2.1 s, hrows.2.1 s]
    | .keyedList _ _ _ _ _ _ _ (some _), h, _ => False.elim h
  theorem View.DomCleanEach_renderEach : ∀ {ks : List (View σ msg)}, View.DomCleanEach ks → ∀ s, Html.DomCleanList (View.renderEach ks s) = true
    | [], _, _ => rfl | _ :: _, ⟨hk, hks⟩, s => by simp [View.renderEach, Html.DomCleanList, View.DomClean_render hk s, View.DomCleanEach_renderEach hks s]
end

private theorem map_prefixSignal_of_clean (pfx : String) :
    ∀ (attrs : List (Attr msg)), ownsChildren attrs = false → attrs.all Attr.DomClean = true → attrs.map (Attr.prefixSignal pfx) = attrs
  | [], _, _ => rfl | a :: rest, hown, hcl => by
      simp only [ownsChildren, List.any_cons, Bool.or_eq_false_iff, List.all_cons, Bool.and_eq_true] at hown hcl
      cases a <;> first | (simp [Attr.DomClean] at hown hcl; done) | simp only [List.map_cons, Attr.prefixSignal, map_prefixSignal_of_clean pfx rest hown.2 hcl.2]

mutual
  theorem Html.prefixSignals_of_DomClean (pfx : String) : ∀ {h : Html msg}, h.DomClean = true → h.prefixSignals pfx = h
    | .text _, _ => rfl
    | .element tag attrs cs, hc => by
        simp only [Html.DomClean, Bool.and_eq_true, Bool.not_eq_true'] at hc
        exact (congrArg (Html.element tag · _) (map_prefixSignal_of_clean pfx attrs hc.1.1 hc.1.2)).trans (congrArg (Html.element tag attrs) (Html.prefixSignalsList_of_DomClean pfx hc.2))
  theorem Html.prefixSignalsList_of_DomClean (pfx : String) : ∀ {hs : List (Html msg)}, Html.DomCleanList hs = true → Html.prefixSignalsList pfx hs = hs
    | [], _ => rfl
    | _ :: _, hc => by simp only [Html.DomCleanList, Bool.and_eq_true] at hc; exact (congrArg (· :: _) (Html.prefixSignals_of_DomClean pfx hc.1)).trans (congrArg (_ :: ·) (Html.prefixSignalsList_of_DomClean pfx hc.2))
end

theorem Html.map_prefixSignals_of_DomCleanList (pfx : String) : ∀ {hs : List (Html msg)}, Html.DomCleanList hs = true → hs.map (Html.prefixSignals pfx) = hs
  | [], _ => rfl
  | _ :: _, hc => by simp only [Html.DomCleanList, Bool.and_eq_true] at hc; simp only [List.map_cons, Html.prefixSignals_of_DomClean pfx hc.1, Html.map_prefixSignals_of_DomCleanList pfx hc.2]

theorem Html.DomClean_withKey (k : String) : ∀ (h : Html msg), (withKey k h).DomClean = h.DomClean
  | .text _ => rfl | .element .. => by simp [withKey, Html.DomClean, ownsChildren, Attr.DomClean]

theorem Html.textOf?_withKey (k : String) : ∀ (h : Html msg), (withKey k h).textOf? = h.textOf?
  | .text _ | .element .. => rfl

private theorem managedAttrName_of_key? {a : Attr msg} {k : String} (h : a.key? = some k) : managedAttrName a = some k := by
  cases a <;> simp_all [Attr.key?, managedAttrName]

private theorem mem_managed_dedupAttrs_iff {k : String} :
    ∀ {xs : List (Attr msg)}, k ∈ (dedupAttrs xs).filterMap managedAttrName ↔ ∃ a ∈ xs, managedAttrName a = some k
  | [] => by simp [dedupAttrs]
  | x :: xs => by
      have hcons : k ∈ (x :: dedupAttrs xs).filterMap managedAttrName ↔ ∃ a ∈ x :: xs, managedAttrName a = some k := by
        simp only [List.mem_filterMap, List.mem_cons, exists_eq_or_imp]; exact or_congr_right (by simpa [List.mem_filterMap] using mem_managed_dedupAttrs_iff (k := k) (xs := xs))
      unfold dedupAttrs; split
      · exact hcons
      · rename_i kx hx; split
        · rcases List.any_eq_true.1 ‹_› with ⟨y, hy, hyk⟩; simp only [mem_managed_dedupAttrs_iff, List.mem_cons, exists_eq_or_imp]
          exact ⟨.inr, fun h => h.elim (fun hmk => ⟨y, hy, (managedAttrName_of_key? (beq_iff_eq.1 hyk)).trans ((managedAttrName_of_key? hx).symm.trans hmk)⟩) id⟩
        · exact hcons

private def noBind (xs : List (VAttr σ msg)) : Bool := xs.all (fun | .bind _ | .dynOn _ _ => false | _ => true)
private abbrev nonCls (s : σ) (xs : List (VAttr σ msg)) : List (Attr msg) := (xs.map (VAttr.eval s)).filter (fun | .cls _ => false | _ => true)
private def stepDynAttr (s : σ) (cur : SpecElemState msg) : VAttr σ msg → SpecElemState msg | .dynVal k g => stepSpecAttr cur (.attr k (g s)) | _ => cur

private theorem applyDynAttrListM_fold (a : DomArena msg) (node : Dom.Node) (s : σ) (ns tag : String) (mg : List String) (cs : List Dom.Node) :
    ∀ (xs : List (VAttr σ msg)) (st : SpecElemState msg), noBind xs = true →
      applyDynAttrListM (m := StateM (DomArena msg)) node s xs (a.set node (.element ns tag st mg cs)) =
        ((), a.set node (.element ns tag (xs.foldl (stepDynAttr s) st) mg cs))
  | [], _, _ => rfl | .bind _ :: _, _, h | .dynOn _ _ :: _, _, h => by cases h
  | .stat _ :: rest, st, h => applyDynAttrListM_fold a node s ns tag mg cs rest st h
  | .dynVal _ _ :: rest, _, h => by dsimp only [applyDynAttrListM, bind, StateT.bind, List.foldl_cons, stepDynAttr]; rw [applyAttrM_element]; exact applyDynAttrListM_fold a node s ns tag mg cs rest _ h

private theorem filterMap_cls_eq_of_noBind (s₁ s₂ : σ) :
    ∀ (ys : List (VAttr σ msg)), noBind ys = true →
      (ys.map (VAttr.eval s₁)).filterMap (fun | .cls c => some c | _ => none) = (ys.map (VAttr.eval s₂)).filterMap (fun | .cls c => some c | _ => none)
  | [], _ => rfl | .bind _ :: _, h | .dynOn _ _ :: _, h => by cases h
  | .dynVal _ _ :: rest, h => filterMap_cls_eq_of_noBind s₁ s₂ rest h
  | .stat a :: rest, h => by cases a <;> simp only [List.map_cons, VAttr.eval, List.filterMap_cons, filterMap_cls_eq_of_noBind s₁ s₂ rest h]

private theorem normalKey_slotUpdate_iff {a b : Attr msg} {k : String}
    (ha : a.key? = some k) (hb : b.key? = some k) (haN : a.NormalKey = true) (hbN : b.NormalKey = true)
    (sl : AttrSlot) : (a.slotUpdate? sl).isSome = true → (b.slotUpdate? sl).isSome = true := by
  cases a <;> cases ha <;> cases b <;> cases hb <;> first
    | (cases sl <;> simp only [Attr.slotUpdate?] <;> first | exact id | (split <;> exact id))
    | (have h1 : (k == "checked") = false := beq_eq_false_iff_ne.2 fun h => by subst h; first | exact Bool.noConfusion haN | exact Bool.noConfusion hbN
       have h2 : (k == "value") = false := beq_eq_false_iff_ne.2 fun h => by subst h; first | exact Bool.noConfusion haN | exact Bool.noConfusion hbN
       cases sl <;> simp only [Attr.slotUpdate?, h1, h2, bne, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte] <;> first | exact id | (split <;> exact id))

private theorem dedupAttrs_foldl_equiv :
    ∀ (xs : List (Attr msg)) (cur : SpecElemState msg), xs.all Attr.NormalKey = true →
      ElemStateEquiv ((dedupAttrs xs).foldl stepSpecAttr cur) (xs.foldl stepSpecAttr cur)
  | [], cur, _ => ElemStateEquiv.refl cur
  | x :: xs, cur, hn => by
      simp only [List.all_cons, Bool.and_eq_true] at hn; unfold dedupAttrs; split
      · exact dedupAttrs_foldl_equiv xs (stepSpecAttr cur x) hn.2
      · rename_i k hx; split
        · rcases List.any_eq_true.1 ‹_› with ⟨y, hy, hyk⟩; intro sl
          refine (dedupAttrs_foldl_equiv xs cur hn.2 sl).trans (foldl_stepSpecAttr_read sl xs cur _ ?_)
          cases hxu : x.slotUpdate? sl with
          | some _ => exact .inl ⟨y, hy, normalKey_slotUpdate_iff hx (beq_iff_eq.1 hyk) hn.1 (List.all_eq_true.1 hn.2 y hy) sl (by rw [hxu]; rfl)⟩
          | none => exact .inr (by rw [read_stepSpecAttr, hxu]; rfl)
        · exact dedupAttrs_foldl_equiv xs (stepSpecAttr cur x) hn.2

private theorem foldl_stepDynAttr_congr (sl : AttrSlot) (s : σ) :
    ∀ (xs : List (VAttr σ msg)) {s₁ s₂ : SpecElemState msg}, sl.read s₁ = sl.read s₂ →
      sl.read (xs.foldl (stepDynAttr s) s₁) = sl.read (xs.foldl (stepDynAttr s) s₂)
  | [], _, _, h => h | va :: xs, _, _, h => foldl_stepDynAttr_congr sl s xs (by cases va <;> simp only [stepDynAttr, read_stepSpecAttr, h])

private theorem attr_slotUpdate_key_eq {k v : String} {a : Attr msg} {sl : AttrSlot}
    (hu : (@Attr.attr msg k v).slotUpdate? sl ≠ none) (ha : a.slotUpdate? sl ≠ none)
    (hok : match a with | .cls _ | .localCell .. => False | _ => True) : a.key? = some k := by
  cases sl <;> simp only [Attr.slotUpdate?] at hu <;> try exact absurd rfl hu
  all_goals
    split at hu <;> try exact absurd rfl hu
    rename_i h1; simp only [Bool.and_eq_true, beq_iff_eq] at h1
    cases a <;> simp only [Attr.slotUpdate?] at ha <;>
      first | exact False.elim hok | exact absurd rfl ha
            | (split at ha <;> first | exact absurd rfl ha | (rename_i h2; simp only [Bool.and_eq_true, beq_iff_eq] at h2; exact congrArg some (by first | exact h2.2.trans h1.2.symm | exact h2.trans h1.symm)))

private theorem foldl_dynAttr_eq_nonCls (sl : AttrSlot) (s : σ) :
    ∀ (xs : List (VAttr σ msg)) (u₁ u₂ : SpecElemState msg), noBind xs = true →
      (∀ a, .stat a ∈ xs → (match a with | .cls _ => False | _ => True) → a.slotUpdate? sl = none) →
      sl.read u₁ = sl.read u₂ → sl.read (xs.foldl (stepDynAttr s) u₁) = sl.read ((nonCls s xs).foldl stepSpecAttr u₂)
  | [], _, _, _, _, h => h | .bind _ :: _, _, _, hn, _, _ | .dynOn _ _ :: _, _, _, hn, _, _ => by cases hn
  | .dynVal _ _ :: ws, _, _, hn, hst, h => foldl_dynAttr_eq_nonCls sl s ws _ _ hn (fun a ha => hst a (.tail _ ha)) (by dsimp only [stepDynAttr, VAttr.eval]; rw [read_stepSpecAttr, read_stepSpecAttr, h])
  | .stat a :: ws, _, _, hn, hst, h => by cases a <;> exact foldl_dynAttr_eq_nonCls sl s ws _ _ hn (fun b hb => hst b (.tail _ hb)) (by first | exact h | (dsimp only [stepDynAttr, VAttr.eval]; rw [read_stepSpecAttr, hst _ (.head _) trivial]; exact h))

private theorem stepDynAttr_nonCls_read (sl : AttrSlot) (s₁ s₂ : σ) :
    ∀ (xs : List (VAttr σ msg)) (st₁ st₂ : SpecElemState msg),
      noBind xs = true → dynValNoLaterStat xs = true → ownsChildren (xs.map (VAttr.eval s₂)) = false → sl.read st₁ = sl.read st₂ →
      sl.read (xs.foldl (stepDynAttr s₂) ((nonCls s₁ xs).foldl stepSpecAttr st₁)) = sl.read ((nonCls s₂ xs).foldl stepSpecAttr st₂)
  | [], _, _, _, _, _, heq => heq | .bind _ :: _, _, _, hnb, _, _, _ | .dynOn _ _ :: _, _, _, hnb, _, _, _ => by cases hnb
  | .stat a :: rest, _, _, hnb, hns, hown, heq => by
      simp only [ownsChildren, List.map_cons, VAttr.eval, List.any_cons, Bool.or_eq_false_iff] at hown
      cases a <;> exact stepDynAttr_nonCls_read sl s₁ s₂ rest _ _ hnb hns hown.2 (by first | exact heq | (dsimp only [VAttr.eval]; rw [read_stepSpecAttr, read_stepSpecAttr, heq]))
  | .dynVal k g :: rest, st₁, st₂, hnb, hns, hown, heq => by
      simp only [dynValNoLaterStat, Bool.and_eq_true, List.all_eq_true] at hns
      simp only [nonCls, List.map_cons, VAttr.eval, List.filter_cons, ↓reduceIte, List.foldl_cons, stepDynAttr]
      cases hu : (@Attr.attr msg k (g s₂)).slotUpdate? sl with
      | none =>
          have hu1 : (@Attr.attr msg k (g s₁)).slotUpdate? sl = none := by cases sl <;> simp only [Attr.slotUpdate?] at hu ⊢ <;> split at hu <;> simp_all
          exact (foldl_stepDynAttr_congr sl s₂ rest (by rw [read_stepSpecAttr, hu]; rfl)).trans
            (stepDynAttr_nonCls_read sl s₁ s₂ rest _ _ hnb hns.2 hown (by rw [read_stepSpecAttr, hu1, read_stepSpecAttr, hu]; exact heq))
      | some _ =>
          refine foldl_dynAttr_eq_nonCls sl s₂ rest _ _ hnb (fun a ha hnc => ?_) (by rw [read_stepSpecAttr, read_stepSpecAttr, hu]; rfl)
          cases ha' : a.slotUpdate? sl with | none => rfl | some _ =>
          exact absurd (attr_slotUpdate_key_eq (hu ▸ Option.some_ne_none _) (ha' ▸ Option.some_ne_none _)
            (by have hl := List.any_eq_false.1 hown a (List.mem_map.2 ⟨.stat a, .tail _ ha, rfl⟩); cases a <;> first | trivial | exact hnc | exact hl rfl)) (bne_iff_ne.1 (hns.1 (.stat a) ha))

private theorem stepDynAttr_foldl_clean (s₂ : σ) (mg : List String) :
    ∀ (xs : List (VAttr σ msg)) (cur : SpecElemState msg), (xs.map (VAttr.eval s₂)).all Attr.DomClean = true →
      (∀ k g, .dynVal k g ∈ xs → mg.contains k = true) → ElemClean cur mg → ElemClean (xs.foldl (stepDynAttr s₂) cur) mg
  | [], _, _, _, hc => hc
  | va :: rest, cur, hcl, hmk, hc => by
      simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hcl
      refine stepDynAttr_foldl_clean s₂ mg rest _ hcl.2 (fun k g hm => hmk k g (.tail _ hm)) ?_
      cases va with | dynVal k g => exact ⟨stepSpecAttr_retains_managed cur _ mg (hmk k g (.head _)) hc.1, stepSpecAttr_preserves_clean cur _ hcl.1 hc.2⟩ | _ => exact hc

theorem applyDynAttrsM_spec (a : DomArena msg) (node : Dom.Node) (ns tag : String) (st : SpecElemState msg) (mg : List String) (cs : List Dom.Node)
    (attrs : List (VAttr σ msg)) (s₁ s₂ : σ) (hclean : VAttrListClean attrs) (hElClean : ElemClean st mg)
    (heq : ElemStateEquiv st (evalSpecAttrs (attrs.map (VAttr.eval s₁))))
    (hmg : ∀ nm ∈ (normalizeAttrs (attrs.map (VAttr.eval s₁))).filterMap managedAttrName, mg.contains nm = true) :
    let a' := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ (a.set node (.element ns tag st mg cs))).2
    a'.nextId = a.nextId ∧ (∀ m, m ≠ node → a'.get m = a.get m) ∧
    ∃ st' mg', a'.get node = .element ns tag st' mg' cs ∧ ElemClean st' mg' ∧
      ElemStateEquiv st' (evalSpecAttrs (attrs.map (VAttr.eval s₂))) ∧
      (∀ nm ∈ (normalizeAttrs (attrs.map (VAttr.eval s₂))).filterMap managedAttrName, mg'.contains nm = true) := by
  dsimp only [applyDynAttrsM]; split
  · rcases ElemClean_applyAttrsM a node ns tag st mg cs (attrs.map (VAttr.eval s₂)) hElClean (hclean.2.1 s₂) with ⟨st', hget, heqv', hElClean'⟩
    have ⟨hnx, hne⟩ := applyAttrsM_preserves (a.set node (.element ns tag st mg cs)) node (attrs.map (VAttr.eval s₂))
    exact ⟨hnx, fun m hm => (hne m hm).trans (DomArena.get_set_ne _ _ hm), st', _, hget, hElClean', heqv', fun _ => List.contains_iff_mem.2⟩
  · rename_i hnotBind
    have hnb : noBind attrs = true := List.all_eq_true.2 fun x hx => by cases x <;> first | rfl | exact False.elim (hnotBind (List.any_eq_true.2 ⟨_, hx, rfl⟩))
    rw [congrArg Prod.snd (applyDynAttrListM_fold a node s₂ ns tag mg cs attrs st hnb)]
    let clsPart : List (Attr msg) :=
      let cl := ((attrs.map (VAttr.eval s₁)).filterMap (fun | .cls c => some c | _ => none)).filter (· != "")
      if cl.isEmpty then [] else [Attr.cls (String.intercalate " " cl)]
    have hnorm (s : σ) : normalizeAttrs (attrs.map (VAttr.eval s)) = clsPart ++ dedupAttrs (nonCls s attrs) := by
      unfold normalizeAttrs; dsimp only [clsPart, nonCls]; erw [filterMap_cls_eq_of_noBind s s₁ attrs hnb]; rfl
    have hdd (s : σ) : ElemStateEquiv ((dedupAttrs (nonCls s attrs)).foldl stepSpecAttr (clsPart.foldl stepSpecAttr {})) ((nonCls s attrs).foldl stepSpecAttr (clsPart.foldl stepSpecAttr {})) :=
      dedupAttrs_foldl_equiv _ _ (List.all_eq_true.2 fun a ha => List.all_eq_true.1 (hclean.2.2.1 s) a (List.mem_filter.1 ha).1)
    have hmgOf {a : Attr msg} {nm : String} (ha : a ∈ nonCls s₁ attrs) (hm : managedAttrName a = some nm) : mg.contains nm = true :=
      hmg nm (by rw [hnorm s₁, List.filterMap_append]; exact List.mem_append_right _ (mem_managed_dedupAttrs_iff.2 ⟨a, ha, hm⟩))
    refine ⟨rfl, fun m hm => DomArena.get_set_ne _ _ hm, _, mg, DomArena.get_set_self _ _ _,
      stepDynAttr_foldl_clean s₂ mg attrs st (hclean.2.1 s₂) (fun k g hm => hmgOf (List.mem_filter.2 ⟨List.mem_map.2 ⟨_, hm, rfl⟩, rfl⟩) rfl) hElClean,
      fun sl => by simp only [evalSpecAttrs, hnorm, List.foldl_append] at heq ⊢; rw [foldl_stepDynAttr_congr sl s₂ attrs ((heq sl).trans (hdd s₁ sl)), hdd s₂ sl]; exact stepDynAttr_nonCls_read sl s₁ s₂ attrs _ _ hnb hclean.2.2.2 (hclean.1 s₂) rfl,
      fun nm hnm => by
        rw [hnorm s₂, List.filterMap_append, List.mem_append] at hnm
        rcases hnm with hc | hd; · exact hmg nm (by rw [hnorm s₁, List.filterMap_append]; exact List.mem_append_left _ hc)
        rcases mem_managed_dedupAttrs_iff.1 hd with ⟨_, hx, hmk⟩; rcases List.mem_filter.1 hx with ⟨hxm, hxnc⟩
        rcases List.mem_map.1 hxm with ⟨va, hva, rfl⟩; have hv := List.all_eq_true.1 hnb va hva
        exact hmgOf (List.mem_filter.2 ⟨List.mem_map.2 ⟨va, hva, rfl⟩, by cases va <;> first | exact hxnc | rfl | cases hv⟩) (by cases va <;> first | exact hmk | cases hv)⟩

theorem array_push_step_inv {α : Type} {a : Array α} {i bound : Nat} {x : α} {f : (j : Nat) → j < bound → α}
    (hle : i < bound) (hsz : a.size = i) (hprev : ∀ j (hj : j < i), a[j]'(by omega) = f j (Nat.lt_trans hj hle)) (hcur : x = f i hle) :
    ∀ j (hj : j < i + 1), (a.push x)[j]'(by rw [Array.size_push, hsz]; omega) = f j (by omega) := fun j hj => by
  by_cases h : j < i; · simpa [Array.getElem_push_lt (by omega : j < a.size)] using hprev j h
  · cases (by omega : j = i); simpa [hsz, hcur] using @Array.getElem_push_eq _ a x

end
end Qed
