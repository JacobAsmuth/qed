import Qed.Proofs.DomArena

namespace Qed

/-! ## 2. Pure Diff, Memo, Key Disambiguation & Isomorphic SSR Equivalence -/

theorem specDom_applyPatch_diff (ns : String) (old new : Html msg) :
    specDom ns (applyPatch (diff old new) old) = specDom ns new := by
  rw [diff_apply]

theorem patchViewM_memo_hit {σ msg : Type} (sm : SoundMemo σ msg)
    (s₁ s₂ : σ) (parent node : Dom.Node) (idx : UInt32) (a : DomArena msg) (fuel : Nat) (ns : String)
    (hkey : sm.keyOf s₂ = sm.keyOf s₁)
    (hdom : readDomTree fuel a node = specDom ns (View.render (.memo sm) s₁)) :
    let (vst', a') :=
      (patchViewM (m := StateM (DomArena msg)) parent idx (.memo sm) s₂
        (.memo node (sm.keyOf s₁) (sm.eval s₁))).run a
    a' = a ∧ vst' = .memo node (sm.keyOf s₁) (sm.eval s₁) ∧
    readDomTree fuel a' node = specDom ns (View.render (.memo sm) s₂) := by
  have hbeq : (sm.keyOf s₂ == sm.keyOf s₁) = true := beq_iff_eq.2 hkey
  have heval : sm.eval s₂ = sm.eval s₁ := sm.sound s₂ s₁ hkey
  dsimp only [patchViewM, StateT.run, pure, StateT.pure]
  rw [if_pos hbeq]
  exact ⟨rfl, rfl, by simpa only [View.render, heval] using hdom⟩

theorem patchViewM_dyn_spec {σ msg : Type} (get : σ → String) (s₁ s₂ : σ)
    (parent node : Dom.Node) (idx : UInt32) (a : DomArena msg) (fuel : Nat) (hf : 0 < fuel) :
    let a0 := a.set node (.text (get s₁))
    let (vst', a') :=
      (patchViewM (m := StateM (DomArena msg)) parent idx (.dyn get) s₂ (.dyn node (get s₁))).run a0
    vst' = .dyn node (get s₂) ∧ readDomTree fuel a' node = specDom "" (View.render (.dyn get) s₂) := by
  cases fuel with
  | zero => omega
  | succ _ =>
      dsimp only [patchViewM, StateT.run]
      by_cases heq : get s₂ = get s₁
      · have hne : (get s₂ != get s₁) = false := by rw [heq]; exact bne_self_eq_false _
        rw [if_neg (by rw [hne]; exact Bool.false_ne_true)]
        simp only [heq, bind, StateT.bind, pure, StateT.pure, readDomTree, DomArena.get_set_self, specDom, View.render, and_self]
      · have hne : (get s₂ != get s₁) = true := bne_iff_ne.2 heq
        rw [if_pos hne]
        simp only [bind, StateT.bind, pure, StateT.pure, DomArena.modify,
          DomArena.get_set_self, DomArena.set_set, readDomTree, specDom, View.render, and_self]

theorem forEach_disambiguated_keys_nodup {α σ : Type} (items : σ → Array α) (key : α → String) (s : σ) :
    (disambiguateKeys ((items s).map key)).toList.Nodup :=
  disambiguateKeys_nodup ((items s).map key)

theorem App.ssr_rehydrate_equiv {Model Msg : Type} (app : App Model Msg)
    (m m' : Model) (hre : app.rehydrate (app.dehydrate m) = some m') :
    Html.valid (app.view m) = true ∧ Html.valid (app.view m') = true ∧ app.view m' = app.view m ∧
    Html.render (app.view m') = Html.render (app.view m) ∧ specDom "" (app.view m') = specDom "" (app.view m) ∧
    (∀ msg : Msg,
      specDom "" (applyPatch (diff (app.view m') (app.view (app.update m' msg).1)) (app.view m')) =
        specDom "" (app.view (app.update m' msg).1)) := by
  have hview : app.view m' = app.view m := app.dehydrate_view m m' hre
  exact ⟨app.valid_view m, app.valid_view m', hview, congrArg Html.render hview, congrArg (specDom "") hview,
    fun msg => specDom_applyPatch_diff "" (app.view m') (app.view (app.update m' msg).1)⟩

/-! ## 3. Dynamic Attributes (`applyDynAttrsM_spec`) & Unified `VStateValid` -/

def VState.rootNode {σ msg : Type} : VState σ msg → Dom.Node
  | .text n | .dyn n _ | .elem n _ | .list n .. | .tlist n .. | .stat n | .dynNode n _ | .memo n .. => n
  | .cond _ inner => inner.rootNode

def Attr.NormalKey {msg : Type} : Attr msg → Bool
  | .attr "checked" _ | .flag "value" _ => false
  | _ => true

def dynValNoLaterStat {σ msg : Type} : List (VAttr σ msg) → Bool
  | [] => true
  | .dynVal k _ :: rest => rest.all (fun | .stat a => a.key? != some k | _ => true) && dynValNoLaterStat rest
  | _ :: rest => dynValNoLaterStat rest

def VAttrListClean {σ msg : Type} (attrs : List (VAttr σ msg)) : Prop :=
  (∀ s, ownsChildren (attrs.map (VAttr.eval s)) = false) ∧
  (∀ s, (attrs.map (VAttr.eval s)).all Attr.DomClean = true) ∧
  (∀ s, (attrs.map (VAttr.eval s)).all Attr.NormalKey = true) ∧
  dynValNoLaterStat attrs = true

def KeyedRowsClean {σ msg : Type} (keys : σ → Array String) (rowsHtml : σ → List (Html msg)) : Prop :=
  (∀ s, (rowsHtml s).length = (disambiguateKeys (keys s)).size) ∧
  (∀ s, Html.DomCleanList (rowsHtml s) = true) ∧
  (∀ s r, r ∈ rowsHtml s → r.textOf? = none) ∧
  (∀ s₁ s₂ (i j : Nat) (hi : i < (disambiguateKeys (keys s₁)).size) (hj : j < (disambiguateKeys (keys s₂)).size),
    (disambiguateKeys (keys s₁))[i] = (disambiguateKeys (keys s₂))[j] →
    (rowsHtml s₁)[i]? = (rowsHtml s₂)[j]?)

mutual
  def View.DomClean {σ msg : Type} : View σ msg → Prop
    | .text _ | .dyn _ => True
    | .static h => h.DomClean = true
    | .dynNode get => ∀ s, (get s).DomClean = true
    | .memo sm => ∀ s, (sm.eval s).DomClean = true
    | .ifElse _ y n => View.DomClean y ∧ View.DomClean n
    | .element _ attrs kids => VAttrListClean attrs ∧ View.DomCleanEach kids
    | .keyedList _ attrs keys _ _ _ rowsHtml none => VAttrListClean attrs ∧ KeyedRowsClean keys rowsHtml
    | .keyedList _ _ _ _ _ _ _ (some _) => False

  def View.DomCleanEach {σ msg : Type} : List (View σ msg) → Prop
    | [] => True
    | k :: ks => View.DomClean k ∧ View.DomCleanEach ks
end

theorem View.renderEach_append {σ msg : Type} (s : σ) :
    ∀ (xs ys : List (View σ msg)), View.renderEach (xs ++ ys) s = View.renderEach xs s ++ View.renderEach ys s
  | [], _ => rfl
  | _ :: rest, ys => by simp [View.renderEach, View.renderEach_append s rest ys]

mutual
  theorem View.DomClean_render {σ msg : Type} :
      ∀ {v : View σ msg}, View.DomClean v → ∀ s, (View.render v s).DomClean = true
    | .text _, _, _ | .dyn _, _, _ => rfl
    | .static _, h, _ => h
    | .dynNode _, h, s => h s
    | .memo _, h, s => h s
    | .ifElse c _ _, ⟨hy, hn⟩, s => by
        cases hc : c s <;> simp [View.render, hc, View.DomClean_render hy s, View.DomClean_render hn s]
    | .element _ _ _, ⟨ha, hks⟩, s => by
        simp [View.render, Html.DomClean, ha.1 s, ha.2.1 s, View.DomCleanEach_renderEach hks s]
    | .keyedList _ _ _ _ _ _ _ none, ⟨ha, hrows⟩, s => by
        simp [View.render, Html.DomClean, ha.1 s, ha.2.1 s, hrows.2.1 s]
    | .keyedList _ _ _ _ _ _ _ (some _), h, _ => False.elim h

  theorem View.DomCleanEach_renderEach {σ msg : Type} :
      ∀ {ks : List (View σ msg)}, View.DomCleanEach ks → ∀ s, Html.DomCleanList (View.renderEach ks s) = true
    | [], _, _ => rfl
    | _ :: _, ⟨hk, hks⟩, s => by
        simp [View.renderEach, Html.DomCleanList, View.DomClean_render hk s, View.DomCleanEach_renderEach hks s]
end

private theorem map_prefixSignal_of_clean {msg : Type} (pfx : String) :
    ∀ (attrs : List (Attr msg)), ownsChildren attrs = false → attrs.all Attr.DomClean = true →
      attrs.map (Attr.prefixSignal pfx) = attrs
  | [], _, _ => rfl
  | a :: rest, hown, hcl => by
      simp only [ownsChildren, List.any_cons, Bool.or_eq_false_iff] at hown
      simp only [List.all_cons, Bool.and_eq_true] at hcl
      have hr := map_prefixSignal_of_clean pfx rest hown.2 hcl.2
      cases a with
      | signalBind _ => simp at hown
      | signalAttr _ _ _ | signalOn _ _ _ => simp [Attr.DomClean] at hcl
      | cls _ | attr _ _ | flag _ _ | key _ | on _ _ | onValue _ _ | localCell _ _ _ _ _ =>
          simp [Attr.prefixSignal, hr]

mutual
  theorem Html.prefixSignals_of_DomClean {msg : Type} (pfx : String) :
      ∀ {h : Html msg}, h.DomClean = true → h.prefixSignals pfx = h
    | .text _, _ => rfl
    | .element tag attrs cs, hc => by
        simp only [Html.DomClean, Bool.and_eq_true] at hc
        rcases hc with ⟨⟨hownT, hA⟩, hCs⟩
        have hown : ownsChildren attrs = false := by simpa using hownT
        rw [Html.prefixSignals, map_prefixSignal_of_clean pfx attrs hown hA,
          Html.prefixSignalsList_of_DomClean pfx hCs]

  theorem Html.prefixSignalsList_of_DomClean {msg : Type} (pfx : String) :
      ∀ {hs : List (Html msg)}, Html.DomCleanList hs = true → Html.prefixSignalsList pfx hs = hs
    | [], _ => rfl
    | c :: cs, hc => by
        simp only [Html.DomCleanList, Bool.and_eq_true] at hc
        rw [Html.prefixSignalsList, Html.prefixSignals_of_DomClean pfx hc.1,
          Html.prefixSignalsList_of_DomClean pfx hc.2]
end

theorem Html.map_prefixSignals_of_DomCleanList {msg : Type} (pfx : String) :
    ∀ {hs : List (Html msg)}, Html.DomCleanList hs = true → hs.map (Html.prefixSignals pfx) = hs
  | [], _ => rfl
  | c :: cs, hc => by
      simp only [Html.DomCleanList, Bool.and_eq_true] at hc
      simp [Html.prefixSignals_of_DomClean pfx hc.1, Html.map_prefixSignals_of_DomCleanList pfx hc.2]

theorem Html.DomClean_withKey {msg : Type} (k : String) :
    ∀ (h : Html msg), (withKey k h).DomClean = h.DomClean
  | .text _ => rfl
  | .element t as cs => by simp [withKey, Html.DomClean, ownsChildren, Attr.DomClean]

theorem Html.textOf?_withKey {msg : Type} (k : String) :
    ∀ (h : Html msg), (withKey k h).textOf? = h.textOf?
  | .text _ | .element .. => rfl

private theorem mem_dedupAttrs_of_key? {msg : Type} :
    ∀ {xs : List (Attr msg)} {a : Attr msg} {k : String},
      a ∈ xs → a.key? = some k → ∃ b ∈ dedupAttrs xs, b.key? = some k
  | [], _, _, ha, _ => nomatch ha
  | x :: xs, a, k, ha, hk => by
      by_cases hex : ∃ y ∈ xs, y.key? = some k
      · rcases hex with ⟨y, hy, hyk⟩
        rcases mem_dedupAttrs_of_key? hy hyk with ⟨b, hb, hbk⟩
        cases hxk : x.key? with
        | none => exact ⟨b, by simp [dedupAttrs, hxk, hb], hbk⟩
        | some k' => by_cases hany : xs.any (·.key? == some k') = true <;> exact ⟨b, by simp [dedupAttrs, hxk, hany, hb], hbk⟩
      · have hxNot : ∀ y ∈ xs, y.key? ≠ some k := fun y hy heq => hex ⟨y, hy, heq⟩
        rcases List.mem_cons.1 ha with rfl | hmem
        · have hany : xs.any (·.key? == some k) = false := by rw [List.any_eq_false]; intro y hy; simp [hxNot y hy]
          exact ⟨a, by simp [dedupAttrs, hk, hany], hk⟩
        · exact absurd hk (hxNot a hmem)

theorem mem_managed_of_key? {msg : Type} {xs : List (Attr msg)} {a : Attr msg} {k : String}
    (ha : a ∈ xs) (hk : a.key? = some k) : k ∈ (dedupAttrs xs).filterMap managedAttrName := by
  rcases mem_dedupAttrs_of_key? ha hk with ⟨b, hb, hbk⟩
  refine List.mem_filterMap.2 ⟨b, hb, ?_⟩
  cases b with
  | attr _ _ | flag _ _ => simp only [Attr.key?, Option.some.injEq] at hbk; subst hbk; rfl
  | cls _ | key _ | on _ _ | onValue _ _ | localCell _ _ _ _ _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ => simp [Attr.key?] at hbk

private def noBind {σ msg : Type} (xs : List (VAttr σ msg)) : Bool :=
  xs.all (fun | .bind _ | .dynOn _ _ => false | _ => true)

private def stepDynAttr {σ msg : Type} (s : σ) (cur : SpecElemState msg) : VAttr σ msg → SpecElemState msg
  | .bind f => stepSpecAttr cur (f s)
  | .dynVal k g => stepSpecAttr cur (.attr k (g s))
  | .dynOn ev g => stepSpecAttr cur (.on ev (g s))
  | .stat _ => cur

private theorem applyDynAttrListM_fold {σ msg : Type} (a : DomArena msg) (node : Dom.Node)
    (s : σ) (ns tag : String) (mg : List String) (cs : List Dom.Node) :
    ∀ (xs : List (VAttr σ msg)) (st : SpecElemState msg), noBind xs = true →
      applyDynAttrListM (m := StateM (DomArena msg)) node s xs (a.set node (.element ns tag st mg cs)) =
        ((), a.set node (.element ns tag (xs.foldl (stepDynAttr s) st) mg cs))
  | [], _, _ => rfl
  | va :: rest, st, hnb => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      cases va with
      | bind _ | dynOn _ _ => simp at hnb
      | stat _ => exact applyDynAttrListM_fold a node s ns tag mg cs rest st hnb.2
      | dynVal k g =>
          dsimp only [applyDynAttrListM, bind, StateT.bind, List.foldl_cons, stepDynAttr]
          rw [applyAttrM_element]
          exact applyDynAttrListM_fold a node s ns tag mg cs rest (stepSpecAttr st (.attr k (g s))) hnb.2

private def AttrKeyEq {msg : Type} : List (Attr msg) → List (Attr msg) → Prop
  | [], [] => True
  | x :: xs, y :: ys => x.key? = y.key? ∧ managedAttrName x = managedAttrName y ∧ AttrKeyEq xs ys
  | _, _ => False

private theorem stepSpecAttr_attr_ne {msg : Type} (st : SpecElemState msg) {k : String} (v : String) (h : k ≠ "value") :
    stepSpecAttr st (.attr k v) = { st with attrs := setAssoc k v st.attrs } := by
  simp only [stepSpecAttr, beq_eq_false_iff_ne.2 h, Bool.false_eq_true, ↓reduceIte]

private theorem stepSpecAttr_flag_ne {msg : Type} (st : SpecElemState msg) {k : String} (p : Bool) (h : k ≠ "checked") :
    stepSpecAttr st (.flag k p) = { st with attrs := if p then setAssoc k k st.attrs else eraseAssoc k st.attrs } := by
  simp only [stepSpecAttr, beq_eq_false_iff_ne.2 h, Bool.false_eq_true, ↓reduceIte]

private theorem filterMap_cls_eq_of_noBind {σ msg : Type} (s₁ s₂ : σ) :
    ∀ (ys : List (VAttr σ msg)), noBind ys = true →
      (ys.map (VAttr.eval s₁)).filterMap (fun | .cls c => some c | _ => none) =
      (ys.map (VAttr.eval s₂)).filterMap (fun | .cls c => some c | _ => none)
  | [], _ => rfl
  | va :: rest, hn => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hn
      cases va with
      | bind _ | dynOn _ _ => exact absurd hn.1 Bool.false_ne_true
      | dynVal _ _ =>
          simp only [List.map_cons, VAttr.eval, List.filterMap_cons]
          exact filterMap_cls_eq_of_noBind s₁ s₂ rest hn.2
      | stat a =>
          cases a <;> simp only [List.map_cons, VAttr.eval, List.filterMap_cons,
            filterMap_cls_eq_of_noBind s₁ s₂ rest hn.2]

private theorem managedNames_eq_of_noBind {σ msg : Type} {s₁ s₂ : σ} :
    ∀ {xs : List (VAttr σ msg)}, noBind xs = true →
      (normalizeAttrs (xs.map (VAttr.eval s₂))).filterMap managedAttrName =
      (normalizeAttrs (xs.map (VAttr.eval s₁))).filterMap managedAttrName := by
  have hany : ∀ (k : String) (xs ys : List (Attr msg)), AttrKeyEq xs ys →
      xs.any (·.key? == some k) = ys.any (·.key? == some k) := fun k => by
    intro xs; induction xs with
    | nil => intro ys h; cases ys with | nil => rfl | cons _ _ => exact False.elim h
    | cons x' xs' ih' =>
        intro ys h; cases ys with | nil => exact False.elim h | cons y' ys' =>
          simp only [List.any_cons, h.1, ih' ys' h.2.2]
  have hdd : ∀ (xs ys : List (Attr msg)), AttrKeyEq xs ys → AttrKeyEq (dedupAttrs xs) (dedupAttrs ys) := by
    intro xs; induction xs with
    | nil => intro ys h; cases ys with | nil => trivial | cons _ _ => exact False.elim h
    | cons x xs ih =>
        intro ys h; cases ys with
        | nil => exact False.elim h
        | cons y ys =>
            rcases h with ⟨hk, hm, htl⟩
            have hih := ih ys htl
            cases hx : x.key? with
            | none => have hy : y.key? = none := hk.symm.trans hx; simp only [dedupAttrs, hx, hy]; exact ⟨hk, hm, hih⟩
            | some k =>
                have hy : y.key? = some k := hk.symm.trans hx
                simp only [dedupAttrs, hx, hy, hany k xs ys htl]; split; exact hih; exact ⟨hk, hm, hih⟩
  have hfm : ∀ (xs ys : List (Attr msg)), AttrKeyEq xs ys → ys.filterMap managedAttrName = xs.filterMap managedAttrName := by
    intro xs; induction xs with
    | nil => intro ys h; cases ys with | nil => rfl | cons _ _ => exact False.elim h
    | cons x xs ih =>
        intro ys h; cases ys with | nil => exact False.elim h | cons y ys =>
          simp only [List.filterMap_cons, h.2.1]; cases managedAttrName y <;> simp only [ih ys h.2.2]
  have hnon : ∀ (ys : List (VAttr σ msg)), noBind ys = true →
      AttrKeyEq ((ys.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true))
                ((ys.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true)) := by
    intro ys; induction ys with
    | nil => intro _; trivial
    | cons va rest ih =>
        intro hn; simp only [noBind, List.all_cons, Bool.and_eq_true] at hn
        cases va with
        | bind _ | dynOn _ _ => exact absurd hn.1 Bool.false_ne_true
        | dynVal _ _ => exact ⟨rfl, rfl, ih hn.2⟩
        | stat a => cases a <;> (simp only [List.map_cons, VAttr.eval, List.filter_cons]; first | exact ⟨rfl, rfl, ih hn.2⟩ | exact ih hn.2)
  intro xs hnb
  unfold normalizeAttrs; dsimp only
  erw [← filterMap_cls_eq_of_noBind s₁ s₂ xs hnb]
  rw [List.filterMap_append, List.filterMap_append]; erw [hfm _ _ (hdd _ _ (hnon xs hnb))]; rfl

private theorem stepSpecAttr_equiv {msg : Type} {s₁ s₂ : SpecElemState msg} (a : Attr msg)
    (he : ElemStateEquiv s₁ s₂) : ElemStateEquiv (stepSpecAttr s₁ a) (stepSpecAttr s₂ a) := by
  refine ⟨fun k => ?_, ?_, ?_, fun e => ?_, fun e => ?_⟩
  · cases a with
    | cls _ | localCell _ _ _ _ _ => simp only [stepSpecAttr, lookupAssoc_setAssoc, he.1]
    | attr k' _ =>
        by_cases hv : k' = "value"
        · subst hv; exact he.1 k
        · simp only [stepSpecAttr_attr_ne _ _ hv, lookupAssoc_setAssoc, he.1]
    | flag k' p =>
        by_cases hc : k' = "checked"
        · subst hc; exact he.1 k
        · cases p <;> simp only [stepSpecAttr_flag_ne _ _ hc, Bool.false_eq_true, ↓reduceIte, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc, he.1]
    | key _ | on _ _ | onValue _ _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ => exact he.1 k
  · cases a with
    | attr k' _ => by_cases hv : k' = "value"; subst hv; rfl; simp only [stepSpecAttr_attr_ne _ _ hv, he.2.1]
    | flag k' _ => by_cases hc : k' = "checked"; subst hc; exact he.2.1; simp only [stepSpecAttr_flag_ne _ _ hc, he.2.1]
    | _ => exact he.2.1
  · cases a with
    | attr k' _ => by_cases hv : k' = "value"; subst hv; exact he.2.2.1; simp only [stepSpecAttr_attr_ne _ _ hv, he.2.2.1]
    | flag k' _ => by_cases hc : k' = "checked"; subst hc; rfl; simp only [stepSpecAttr_flag_ne _ _ hc, he.2.2.1]
    | _ => exact he.2.2.1
  · cases a with
    | on _ _ => simp only [stepSpecAttr, lookupAssoc_setAssoc, he.2.2.2.1]
    | attr k' _ => by_cases hv : k' = "value"; subst hv; exact he.2.2.2.1 e; simp only [stepSpecAttr_attr_ne _ _ hv, he.2.2.2.1]
    | flag k' _ => by_cases hc : k' = "checked"; subst hc; exact he.2.2.2.1 e; simp only [stepSpecAttr_flag_ne _ _ hc, he.2.2.2.1]
    | _ => exact he.2.2.2.1 e
  · cases a with
    | onValue _ _ => simp only [stepSpecAttr, lookupAssoc_setAssoc, he.2.2.2.2]
    | attr k' _ => by_cases hv : k' = "value"; subst hv; exact he.2.2.2.2 e; simp only [stepSpecAttr_attr_ne _ _ hv, he.2.2.2.2]
    | flag k' _ => by_cases hc : k' = "checked"; subst hc; exact he.2.2.2.2 e; simp only [stepSpecAttr_flag_ne _ _ hc, he.2.2.2.2]
    | _ => exact he.2.2.2.2 e

private theorem dedupAttrs_foldl_equiv {msg : Type} :
    ∀ (xs : List (Attr msg)) (cur : SpecElemState msg),
      xs.all Attr.NormalKey = true → ElemStateEquiv ((dedupAttrs xs).foldl stepSpecAttr cur) (xs.foldl stepSpecAttr cur)
  | [], cur, _ => ElemStateEquiv.refl cur
  | x :: xs, cur, hn => by
      simp only [List.all_cons, Bool.and_eq_true] at hn
      cases hx : x.key? with
      | none => simp only [dedupAttrs, hx, List.foldl_cons]; exact dedupAttrs_foldl_equiv xs (stepSpecAttr cur x) hn.2
      | some k =>
          by_cases hany : xs.any (·.key? == some k) = true
          · simp only [dedupAttrs, hx, hany, ↓reduceIte, List.foldl_cons]
            rcases List.any_eq_true.1 hany with ⟨y, hy, hyk⟩
            have hyk' : y.key? = some k := beq_iff_eq.1 hyk
            have hyN : Attr.NormalKey y = true := (List.all_eq_true.1 hn.2) y hy
            have ih := dedupAttrs_foldl_equiv xs cur hn.2
            refine ⟨fun k' => (ih.1 k').trans ?_, ih.2.1.trans ?_, ih.2.2.1.trans ?_,
              fun e => (ih.2.2.2.1 e).trans ?_, fun e => (ih.2.2.2.2 e).trans ?_⟩
            · apply foldl_stepSpecAttr_attrs
              by_cases hkEq : k' = k
              · subst hkEq
                by_cases hv : k' = "value"
                · subst hv; right; cases x with | attr kx _ => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; rfl | flag _ _ => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; exact False.elim (by simpa [Attr.NormalKey] using hn.1) | _ => simp only [Attr.key?, reduceCtorEq] at hx
                · by_cases hc : k' = "checked"
                  · subst hc; right; cases x with | flag kx p => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; cases p <;> rfl | attr _ _ => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; exact False.elim (by simpa [Attr.NormalKey] using hn.1) | _ => simp only [Attr.key?, reduceCtorEq] at hx
                  · left; refine ⟨y, hy, ?_⟩; cases y with
                    | attr ky _ => simp only [Attr.key?, Option.some.injEq] at hyk'; subst hyk'; simp [attrWritesKey, hv]
                    | flag ky _ => simp only [Attr.key?, Option.some.injEq] at hyk'; subst hyk'; simp [attrWritesKey, hc]
                    | _ => simp only [Attr.key?, reduceCtorEq] at hyk'
              · right; cases x with
                | attr kx _ =>
                    simp only [Attr.key?, Option.some.injEq] at hx; subst hx
                    by_cases hv : kx = "value"
                    · subst hv; rfl
                    · simp only [stepSpecAttr_attr_ne _ _ hv, lookupAssoc_setAssoc, beq_eq_false_iff_ne.2 (Ne.symm hkEq), Bool.false_eq_true, ↓reduceIte]
                | flag kx p =>
                    simp only [Attr.key?, Option.some.injEq] at hx; subst hx
                    by_cases hc : kx = "checked"
                    · subst hc; rfl
                    · cases p <;> simp only [stepSpecAttr_flag_ne _ _ hc, Bool.false_eq_true, ↓reduceIte, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc, beq_eq_false_iff_ne.2 (Ne.symm hkEq)]
                | _ => simp only [Attr.key?, reduceCtorEq] at hx
            · apply foldl_stepSpecAttr_val
              by_cases hv : k = "value"
              · subst hv; right; cases y with
                | attr ky v => simp only [Attr.key?, Option.some.injEq] at hyk'; subst hyk'; exact ⟨v, hy⟩
                | flag ky _ => simp only [Attr.key?, Option.some.injEq] at hyk'; subst hyk'; simp only [Attr.NormalKey, Bool.false_eq_true] at hyN
                | _ => simp only [Attr.key?, reduceCtorEq] at hyk'
              · left; cases x with
                | attr kx _ => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; simp only [stepSpecAttr_attr_ne _ _ hv]
                | flag kx p => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; by_cases hc : kx = "checked"; subst hc; rfl; simp only [stepSpecAttr_flag_ne _ _ hc]
                | _ => simp only [Attr.key?, reduceCtorEq] at hx
            · apply foldl_stepSpecAttr_chk
              by_cases hc : k = "checked"
              · subst hc; right; cases y with
                | flag ky p => simp only [Attr.key?, Option.some.injEq] at hyk'; subst hyk'; exact ⟨p, hy⟩
                | attr ky _ => simp only [Attr.key?, Option.some.injEq] at hyk'; subst hyk'; simp only [Attr.NormalKey, Bool.false_eq_true] at hyN
                | _ => simp only [Attr.key?, reduceCtorEq] at hyk'
              · left; cases x with
                | attr kx _ => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; by_cases hv : kx = "value"; subst hv; rfl; simp only [stepSpecAttr_attr_ne _ _ hv]
                | flag kx p => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; simp only [stepSpecAttr_flag_ne _ _ hc]
                | _ => simp only [Attr.key?, reduceCtorEq] at hx
            · apply foldl_stepSpecAttr_clicks; right
              cases x with
              | attr kx _ => by_cases hv : kx = "value"; subst hv; rfl; simp only [stepSpecAttr_attr_ne _ _ hv]
              | flag kx p => by_cases hc : kx = "checked"; subst hc; rfl; simp only [stepSpecAttr_flag_ne _ _ hc]
              | _ => simp only [Attr.key?, reduceCtorEq] at hx
            · apply foldl_stepSpecAttr_inputs; right
              cases x with
              | attr kx _ => by_cases hv : kx = "value"; subst hv; rfl; simp only [stepSpecAttr_attr_ne _ _ hv]
              | flag kx p => by_cases hc : kx = "checked"; subst hc; rfl; simp only [stepSpecAttr_flag_ne _ _ hc]
              | _ => simp only [Attr.key?, reduceCtorEq] at hx
          · simp only [dedupAttrs, hx, hany, Bool.false_eq_true, ↓reduceIte, List.foldl_cons]
            exact dedupAttrs_foldl_equiv xs (stepSpecAttr cur x) hn.2

private theorem stepDynAttr_equiv {σ msg : Type} (s : σ) :
    ∀ (xs : List (VAttr σ msg)) {s₁ s₂ : SpecElemState msg}, ElemStateEquiv s₁ s₂ →
      ElemStateEquiv (xs.foldl (stepDynAttr s) s₁) (xs.foldl (stepDynAttr s) s₂)
  | [], _, _, h => h
  | va :: xs, _, _, h => by
      apply stepDynAttr_equiv s xs
      cases va with | stat _ => exact h | bind _ | dynOn _ _ | dynVal _ _ => exact stepSpecAttr_equiv _ h

private def lastDynVal? {σ msg : Type} (k : String) (s : σ) : List (VAttr σ msg) → Option String
  | [] => none
  | .dynVal k' g :: rest => (lastDynVal? k s rest).orElse (fun _ => if k' == k then some (g s) else none)
  | _ :: rest => lastDynVal? k s rest

private theorem stepDynAttr_checked {σ msg : Type} (s : σ) :
    ∀ (xs : List (VAttr σ msg)) (st : SpecElemState msg), noBind xs = true → (xs.foldl (stepDynAttr s) st).checked = st.checked
  | [], _, _ => rfl
  | va :: rest, st, hnb => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      cases va with
      | bind _ | dynOn _ _ => exact absurd hnb.1 Bool.false_ne_true
      | stat _ => exact stepDynAttr_checked s rest st hnb.2
      | dynVal k _ =>
          by_cases hk : k = "value"
          · subst hk; exact stepDynAttr_checked s rest _ hnb.2
          · simp only [List.foldl_cons, stepDynAttr, stepSpecAttr_attr_ne _ _ hk, stepDynAttr_checked s rest _ hnb.2]

private theorem nonCls_checked_eq {σ msg : Type} (s₁ s₂ : σ) :
    ∀ (xs : List (VAttr σ msg)) (st₁ st₂ : SpecElemState msg), noBind xs = true → st₁.checked = st₂.checked →
      (((xs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₁).checked =
      (((xs.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₂).checked
  | [], _, _, _, h => h
  | va :: rest, st₁, st₂, hnb, hc => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      cases va with
      | bind _ | dynOn _ _ => exact absurd hnb.1 Bool.false_ne_true
      | dynVal k _ =>
          simp only [List.map_cons, VAttr.eval, List.filter_cons]
          apply nonCls_checked_eq s₁ s₂ rest _ _ hnb.2
          by_cases hv : k = "value"; subst hv; exact hc; simp only [stepSpecAttr_attr_ne _ _ hv, hc]
      | stat a =>
          cases a with
          | cls _ => exact nonCls_checked_eq s₁ s₂ rest _ _ hnb.2 hc
          | attr k _ =>
              simp only [List.map_cons, VAttr.eval, List.filter_cons]
              apply nonCls_checked_eq s₁ s₂ rest _ _ hnb.2
              by_cases hv : k = "value"; subst hv; exact hc; simp only [stepSpecAttr_attr_ne _ _ hv, hc]
          | flag k p =>
              simp only [List.map_cons, VAttr.eval, List.filter_cons]
              apply nonCls_checked_eq s₁ s₂ rest _ _ hnb.2
              by_cases hck : k = "checked"; subst hck; rfl; simp only [stepSpecAttr_flag_ne _ _ hck, hc]
          | key _ | on _ _ | onValue _ _ | localCell _ _ _ _ _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ =>
              exact nonCls_checked_eq s₁ s₂ rest _ _ hnb.2 hc

private theorem stepDynAttr_clicks_inputs {σ msg : Type} (s : σ) :
    ∀ (xs : List (VAttr σ msg)) (st : SpecElemState msg), noBind xs = true →
      (xs.foldl (stepDynAttr s) st).clicks = st.clicks ∧
      (xs.foldl (stepDynAttr s) st).inputs = st.inputs
  | [], _, _ => ⟨rfl, rfl⟩
  | va :: rest, st, hnb => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      cases va with
      | bind _ | dynOn _ _ => exact absurd hnb.1 Bool.false_ne_true
      | stat _ => exact stepDynAttr_clicks_inputs s rest st hnb.2
      | dynVal k _ =>
          by_cases hk : k = "value"
          · subst hk; exact stepDynAttr_clicks_inputs s rest _ hnb.2
          · simp only [List.foldl_cons, stepDynAttr, stepSpecAttr_attr_ne _ _ hk]
            exact stepDynAttr_clicks_inputs s rest _ hnb.2

private theorem nonCls_handlers_eq {σ msg : Type} (s₁ s₂ : σ) :
    ∀ (xs : List (VAttr σ msg)) (st₁ st₂ : SpecElemState msg), noBind xs = true →
      st₁.clicks = st₂.clicks → st₁.inputs = st₂.inputs →
      (((xs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₁).clicks =
      (((xs.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₂).clicks ∧
      (((xs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₁).inputs =
      (((xs.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₂).inputs
  | [], _, _, _, hcl, hin => ⟨hcl, hin⟩
  | va :: rest, st₁, st₂, hnb, hcl, hin => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      cases va with
      | bind _ | dynOn _ _ => exact absurd hnb.1 Bool.false_ne_true
      | dynVal k _ =>
          simp only [List.map_cons, VAttr.eval, List.filter_cons]
          apply nonCls_handlers_eq s₁ s₂ rest _ _ hnb.2
          · by_cases hv : k = "value"; subst hv; exact hcl; simp only [stepSpecAttr_attr_ne _ _ hv, hcl]
          · by_cases hv : k = "value"; subst hv; exact hin; simp only [stepSpecAttr_attr_ne _ _ hv, hin]
      | stat a =>
          cases a with
          | cls _ => exact nonCls_handlers_eq s₁ s₂ rest _ _ hnb.2 hcl hin
          | attr k _ =>
              simp only [List.map_cons, VAttr.eval, List.filter_cons]
              apply nonCls_handlers_eq s₁ s₂ rest _ _ hnb.2
              · by_cases hv : k = "value"; subst hv; exact hcl; simp only [stepSpecAttr_attr_ne _ _ hv, hcl]
              · by_cases hv : k = "value"; subst hv; exact hin; simp only [stepSpecAttr_attr_ne _ _ hv, hin]
          | flag k p =>
              simp only [List.map_cons, VAttr.eval, List.filter_cons]
              apply nonCls_handlers_eq s₁ s₂ rest _ _ hnb.2
              · by_cases hc : k = "checked"; subst hc; exact hcl; simp only [stepSpecAttr_flag_ne _ _ hc, hcl]
              · by_cases hc : k = "checked"; subst hc; exact hin; simp only [stepSpecAttr_flag_ne _ _ hc, hin]
          | on e m =>
              simp only [List.map_cons, VAttr.eval, List.filter_cons]
              exact nonCls_handlers_eq s₁ s₂ rest _ _ hnb.2 (congrArg (setAssoc e m) hcl) hin
          | onValue e f =>
              simp only [List.map_cons, VAttr.eval, List.filter_cons]
              exact nonCls_handlers_eq s₁ s₂ rest _ _ hnb.2 hcl (congrArg (setAssoc e f) hin)
          | key _ | localCell _ _ _ _ _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ =>
              exact nonCls_handlers_eq s₁ s₂ rest _ _ hnb.2 hcl hin

private theorem stepDynAttr_last_key {σ msg : Type} (s : σ) (k : String) :
    ∀ (xs : List (VAttr σ msg)) (st : SpecElemState msg), noBind xs = true →
      match lastDynVal? k s xs with
      | some v => (k = "value" → (xs.foldl (stepDynAttr s) st).value = v) ∧
                  (k ≠ "value" → lookupAssoc k (xs.foldl (stepDynAttr s) st).attrs = some v)
      | none   => (k = "value" → (xs.foldl (stepDynAttr s) st).value = st.value) ∧
                  (k ≠ "value" → lookupAssoc k (xs.foldl (stepDynAttr s) st).attrs = lookupAssoc k st.attrs)
  | [], _, _ => ⟨fun _ => rfl, fun _ => rfl⟩
  | va :: rest, st, hnb => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      cases va with
      | bind _ | dynOn _ _ => exact absurd hnb.1 Bool.false_ne_true
      | stat _ => exact stepDynAttr_last_key s k rest st hnb.2
      | dynVal k' g =>
          have ih := stepDynAttr_last_key s k rest (stepSpecAttr st (.attr k' (g s))) hnb.2
          cases hr : lastDynVal? k s rest with
          | some v' => rw [hr] at ih; simp only [lastDynVal?, Option.orElse, hr]; exact ih
          | none =>
              rw [hr] at ih; by_cases hk' : k' = k
              · subst hk'; simp only [lastDynVal?, Option.orElse, hr, beq_self_eq_true, ↓reduceIte] at ih ⊢
                exact ⟨fun hkv => (ih.1 hkv).trans (by subst hkv; rfl),
                       fun hnk => (ih.2 hnk).trans (by simp only [stepSpecAttr_attr_ne _ _ hnk, lookupAssoc_setAssoc, beq_self_eq_true, ↓reduceIte])⟩
              · have hb : (k' == k) = false := beq_eq_false_iff_ne.2 hk'
                simp only [lastDynVal?, Option.orElse, hr, hb, Bool.false_eq_true, ↓reduceIte] at ih ⊢
                refine ⟨fun hkv => (ih.1 hkv).trans (by subst hkv; simp only [stepSpecAttr_attr_ne _ _ hk']),
                        fun hnk => (ih.2 hnk).trans ?_⟩
                by_cases hv : k' = "value"
                · subst hv; rfl
                · simp only [stepSpecAttr_attr_ne _ _ hv, lookupAssoc_setAssoc, hb, Bool.false_eq_true, ↓reduceIte]

private theorem ownsChildren_map_tail {σ msg : Type} (s : σ) (va : VAttr σ msg) (rest : List (VAttr σ msg))
    (h : ownsChildren ((va :: rest).map (VAttr.eval s)) = false) :
    ownsChildren (rest.map (VAttr.eval s)) = false := by
  simp only [ownsChildren, List.map_cons, List.any_cons, Bool.or_eq_false_iff] at h; exact h.2

private theorem nonCls_last_key {σ msg : Type} (s : σ) (k : String) :
    ∀ (xs : List (VAttr σ msg)) (st : SpecElemState msg) (v : String),
      noBind xs = true → dynValNoLaterStat xs = true → ownsChildren (xs.map (VAttr.eval s)) = false →
      lastDynVal? k s xs = some v →
      (k = "value" → (((xs.map (VAttr.eval s)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st).value = v) ∧
      (k ≠ "value" → lookupAssoc k (((xs.map (VAttr.eval s)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st).attrs = some v)
  | [], _, _, _, _, _, h => by simp only [lastDynVal?, reduceCtorEq] at h
  | va :: rest, st, v, hnb, hns, hown, hs => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      have hownR := ownsChildren_map_tail s va rest hown
      have hnsR : dynValNoLaterStat rest = true := by
        cases va with | bind _ | dynOn _ _ => exact absurd hnb.1 Bool.false_ne_true | stat _ => exact hns | dynVal _ _ => simp only [dynValNoLaterStat, Bool.and_eq_true] at hns; exact hns.2
      cases va with
      | bind _ | dynOn _ _ => exact absurd hnb.1 Bool.false_ne_true
      | stat a => cases a <;> exact nonCls_last_key s k rest _ v hnb.2 hnsR hownR hs
      | dynVal k' g =>
          cases hr : lastDynVal? k s rest with
          | some v' =>
              have hvv' : v' = v := by simp only [lastDynVal?, Option.orElse, hr, Option.some.injEq] at hs; exact hs
              subst hvv'; exact nonCls_last_key s k rest _ v' hnb.2 hnsR hownR hr
          | none =>
              have hkk' : k' = k ∧ g s = v := by
                by_cases hk : k' = k
                · subst hk; simp only [lastDynVal?, Option.orElse, hr, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hs; exact ⟨rfl, hs⟩
                · simp only [lastDynVal?, Option.orElse, hr, beq_eq_false_iff_ne.2 hk, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hs
              rcases hkk' with ⟨rfl, rfl⟩
              simp only [dynValNoLaterStat, Bool.and_eq_true, List.all_eq_true] at hns
              have hpres : ∀ (ys : List (VAttr σ msg)) (cur : SpecElemState msg),
                  noBind ys = true → ownsChildren (ys.map (VAttr.eval s)) = false → lastDynVal? k' s ys = none →
                  (∀ w ∈ ys, (match w with | .stat a => a.key? != some k' | _ => true) = true) →
                  (k' = "value" → (((ys.map (VAttr.eval s)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr cur).value = cur.value) ∧
                  (k' ≠ "value" → lookupAssoc k' (((ys.map (VAttr.eval s)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr cur).attrs = lookupAssoc k' cur.attrs) := by
                intro ys; induction ys with
                | nil => intro _ _ _ _ _; exact ⟨fun _ => rfl, fun _ => rfl⟩
                | cons w ws ihw =>
                    intro cur hnbw hownw hnw hstw
                    simp only [noBind, List.all_cons, Bool.and_eq_true] at hnbw
                    have hownwR := ownsChildren_map_tail s w ws hownw
                    cases w with
                    | bind _ | dynOn _ _ => exact absurd hnbw.1 Bool.false_ne_true
                    | dynVal kw gw =>
                        cases hrw : lastDynVal? k' s ws with
                        | some _ => simp only [lastDynVal?, Option.orElse, hrw, reduceCtorEq] at hnw
                        | none =>
                            have hne : kw ≠ k' := fun hEq => by subst hEq; simp only [lastDynVal?, Option.orElse, hrw, beq_self_eq_true, ↓reduceIte, reduceCtorEq] at hnw
                            have iht := ihw (stepSpecAttr cur (.attr kw (gw s))) hnbw.2 hownwR hrw (fun u hu => hstw u (.tail _ hu))
                            refine ⟨fun hkv => (iht.1 hkv).trans (by subst hkv; simp only [stepSpecAttr_attr_ne _ _ hne]),
                                    fun hnk => (iht.2 hnk).trans ?_⟩
                            by_cases hv : kw = "value"
                            · subst hv; rfl
                            · simp only [stepSpecAttr_attr_ne _ _ hv, lookupAssoc_setAssoc, beq_eq_false_iff_ne.2 hne, Bool.false_eq_true, ↓reduceIte]
                    | stat b =>
                        have hb : b.key? ≠ some k' := bne_iff_ne.1 (hstw (.stat b) (.head _))
                        cases b with
                        | cls _ => exact ihw cur hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
                        | localCell _ _ _ _ _ => simp only [ownsChildren, List.map_cons, VAttr.eval, List.any_cons, Bool.true_or, Bool.true_eq_false] at hownw
                        | attr kb vb =>
                            have hne : kb ≠ k' := fun hEq => hb (congrArg some hEq)
                            have iht := ihw (stepSpecAttr cur (.attr kb vb)) hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
                            refine ⟨fun hkv => (iht.1 hkv).trans (by subst hkv; simp only [stepSpecAttr_attr_ne _ _ hne]),
                                    fun hnk => (iht.2 hnk).trans ?_⟩
                            by_cases hv : kb = "value"
                            · subst hv; rfl
                            · simp only [stepSpecAttr_attr_ne _ _ hv, lookupAssoc_setAssoc, beq_eq_false_iff_ne.2 hne, Bool.false_eq_true, ↓reduceIte]
                        | flag kb p =>
                            have hne : kb ≠ k' := fun hEq => hb (congrArg some hEq)
                            have iht := ihw (stepSpecAttr cur (.flag kb p)) hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
                            refine ⟨fun hkv => (iht.1 hkv).trans (by by_cases hc : kb = "checked"; subst hc; rfl; simp only [stepSpecAttr_flag_ne _ _ hc]),
                                    fun hnk => (iht.2 hnk).trans ?_⟩
                            by_cases hc : kb = "checked"
                            · subst hc; rfl
                            · cases p <;> simp only [stepSpecAttr_flag_ne _ _ hc, Bool.false_eq_true, ↓reduceIte, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc, beq_eq_false_iff_ne.2 hne]
                        | key _ | on _ _ | onValue _ _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ =>
                            exact ihw _ hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
              have hp := hpres rest (stepSpecAttr st (.attr k' (g s))) hnb.2 hownR hr (fun w hw => hns.1 w hw)
              refine ⟨fun hkv => (hp.1 hkv).trans (by subst hkv; rfl),
                      fun hnk => (hp.2 hnk).trans (by simp only [stepSpecAttr_attr_ne _ _ hnk, lookupAssoc_setAssoc, beq_self_eq_true, ↓reduceIte])⟩

private theorem stepSpecAttr_lookup_congr {msg : Type} (k : String) {s₁ s₂ : SpecElemState msg}
    (ha : lookupAssoc k s₁.attrs = lookupAssoc k s₂.attrs) (a : Attr msg) :
    lookupAssoc k (stepSpecAttr s₁ a).attrs = lookupAssoc k (stepSpecAttr s₂ a).attrs := by
  cases a with
  | cls _ | localCell _ _ _ _ _ => simp only [stepSpecAttr, lookupAssoc_setAssoc, ha]
  | attr k' _ => by_cases hv : k' = "value"; subst hv; exact ha; simp only [stepSpecAttr_attr_ne _ _ hv, lookupAssoc_setAssoc, ha]
  | flag k' p =>
      by_cases hc : k' = "checked"
      · subst hc; exact ha
      · cases p <;> simp only [stepSpecAttr_flag_ne _ _ hc, Bool.false_eq_true, ↓reduceIte, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc, ha]
  | _ => exact ha

private theorem stepSpecAttr_val_congr {msg : Type} (a : Attr msg) {s₁ s₂ : SpecElemState msg} (hv : s₁.value = s₂.value) :
    (stepSpecAttr s₁ a).value = (stepSpecAttr s₂ a).value := by
  cases a with
  | attr k _ => by_cases h : k = "value"; subst h; rfl; simp only [stepSpecAttr_attr_ne _ _ h, hv]
  | flag k p => by_cases h : k = "checked"; subst h; exact hv; simp only [stepSpecAttr_flag_ne _ _ h, hv]
  | _ => exact hv

private theorem nonCls_none_key {σ msg : Type} (s₁ s₂ : σ) (k : String) :
    ∀ (xs : List (VAttr σ msg)) (st₁ st₂ : SpecElemState msg),
      noBind xs = true → lastDynVal? k s₂ xs = none →
      (k = "value" → st₁.value = st₂.value →
        (((xs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₁).value =
        (((xs.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₂).value) ∧
      (k ≠ "value" → lookupAssoc k st₁.attrs = lookupAssoc k st₂.attrs →
        lookupAssoc k (((xs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₁).attrs =
        lookupAssoc k (((xs.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₂).attrs)
  | [], _, _, _, _ => ⟨fun _ h => h, fun _ h => h⟩
  | va :: rest, st₁, st₂, hnb, hn => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      cases va with
      | bind _ | dynOn _ _ => exact absurd hnb.1 Bool.false_ne_true
      | stat a =>
          cases a with
          | cls _ => exact nonCls_none_key s₁ s₂ k rest st₁ st₂ hnb.2 hn
          | attr _ _ | flag _ _ | localCell _ _ _ _ _ | key _ | on _ _ | onValue _ _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ =>
              refine ⟨fun hkv hv => (nonCls_none_key s₁ s₂ k rest _ _ hnb.2 hn).1 hkv (stepSpecAttr_val_congr _ hv),
                      fun hnk ha => (nonCls_none_key s₁ s₂ k rest _ _ hnb.2 hn).2 hnk (stepSpecAttr_lookup_congr k ha _)⟩
      | dynVal k' g =>
          cases hr : lastDynVal? k s₂ rest with
          | some _ => simp only [lastDynVal?, Option.orElse, hr, reduceCtorEq] at hn
          | none =>
              have hne : k' ≠ k := fun hEq => by subst hEq; simp only [lastDynVal?, Option.orElse, hr, beq_self_eq_true, ↓reduceIte, reduceCtorEq] at hn
              have ih := nonCls_none_key s₁ s₂ k rest (stepSpecAttr st₁ (.attr k' (g s₁))) (stepSpecAttr st₂ (.attr k' (g s₂))) hnb.2 hr
              refine ⟨fun hkv hv => ih.1 hkv (by subst hkv; simp only [stepSpecAttr_attr_ne _ _ hne, hv]),
                      fun hnk ha => ih.2 hnk ?_⟩
              by_cases hv : k' = "value"
              · subst hv; exact ha
              · simp only [stepSpecAttr_attr_ne _ _ hv, lookupAssoc_setAssoc, beq_eq_false_iff_ne.2 hne, Bool.false_eq_true, ↓reduceIte, ha]

private theorem anyBind_false_noBind {σ msg : Type} (f : VAttr σ msg → Bool)
    (hf : ∀ x, f x = match x with | .bind _ | .dynOn _ _ => true | _ => false) :
    ∀ (xs : List (VAttr σ msg)), ¬(xs.any f = true) → noBind xs = true
  | [], _ => rfl
  | x :: xs, hn => by
      have hx : f x = false := by cases hfx : f x; rfl; exact False.elim (hn (by simp only [List.any_cons, hfx, Bool.true_or]))
      have hxs : ¬(xs.any f = true) := fun h => hn (by simp only [List.any_cons, h, Bool.or_true])
      cases x with
      | bind _ | dynOn _ _ => simp only [hf, Bool.true_eq_false] at hx
      | stat _ | dynVal _ _ => simp only [noBind, List.all_cons, Bool.and_eq_true]; exact ⟨trivial, anyBind_false_noBind f hf xs hxs⟩

theorem applyDynAttrsM_spec {σ msg : Type} (a : DomArena msg) (node : Dom.Node)
    (ns tag : String) (st : SpecElemState msg) (mg : List String) (cs : List Dom.Node)
    (attrs : List (VAttr σ msg)) (s₁ s₂ : σ)
    (hclean : VAttrListClean attrs) (hElClean : ElemClean st mg)
    (heq : ElemStateEquiv st (evalSpecAttrs (attrs.map (VAttr.eval s₁))))
    (hmg : ∀ nm ∈ (normalizeAttrs (attrs.map (VAttr.eval s₁))).filterMap managedAttrName, mg.contains nm = true) :
    let a' := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ (a.set node (.element ns tag st mg cs))).2
    a'.nextId = a.nextId ∧ (∀ m, m ≠ node → a'.get m = a.get m) ∧
    ∃ st' mg', a'.get node = .element ns tag st' mg' cs ∧ ElemClean st' mg' ∧
      ElemStateEquiv st' (evalSpecAttrs (attrs.map (VAttr.eval s₂))) ∧
      (∀ nm ∈ (normalizeAttrs (attrs.map (VAttr.eval s₂))).filterMap managedAttrName, mg'.contains nm = true) := by
  dsimp only [applyDynAttrsM]
  split
  · have hm := ElemClean_applyAttrsM a node ns tag st mg cs (attrs.map (VAttr.eval s₂)) hElClean (hclean.2.1 s₂)
    rcases hm with ⟨st', hget, heqv', hElClean'⟩
    exact ⟨applyAttrsM_nextId a node _ _, fun m hm => applyAttrsM_get_ne a node _ _ m hm,
      st', (normalizeAttrs (attrs.map (VAttr.eval s₂))).filterMap managedAttrName, hget, hElClean',
      heqv', fun nm hnm => List.contains_iff_mem.2 hnm⟩
  · rename_i hnotBind
    have hnb : noBind attrs = true := anyBind_false_noBind _ (fun x => by cases x <;> rfl) attrs hnotBind
    have hrun : (applyDynAttrListM (m := StateM (DomArena msg)) node s₂ attrs (a.set node (.element ns tag st mg cs))).2 =
        a.set node (.element ns tag (attrs.foldl (stepDynAttr s₂) st) mg cs) :=
      congrArg Prod.snd (applyDynAttrListM_fold a node s₂ ns tag mg cs attrs st hnb)
    rw [hrun]
    let st' := attrs.foldl (stepDynAttr s₂) st
    have hmgEq := managedNames_eq_of_noBind (s₁ := s₁) (s₂ := s₂) hnb
    have hEl' : ElemClean st' mg := by
      have hstep : ∀ (xs : List (VAttr σ msg)) (cur : SpecElemState msg),
          noBind xs = true → (xs.map (VAttr.eval s₂)).all Attr.DomClean = true →
          (∀ k g, .dynVal k g ∈ xs → mg.contains k = true) → ElemClean cur mg →
          ElemClean (xs.foldl (stepDynAttr s₂) cur) mg := by
        intro xs; induction xs with
        | nil => intro _ _ _ _ hc; exact hc
        | cons va rest ih =>
            intro cur hnb' hcl' hmk hc
            simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb'
            simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hcl'
            apply ih _ hnb'.2 hcl'.2 (fun k g hm => hmk k g (.tail _ hm))
            cases va with
            | bind _ | dynOn _ _ => exact absurd hnb'.1 Bool.false_ne_true
            | stat _ => exact hc
            | dynVal k g =>
                exact ⟨stepSpecAttr_retains_managed cur (.attr k (g s₂)) mg (hmk k g (.head _)) hc.1,
                       stepSpecAttr_preserves_clean cur (.attr k (g s₂)) hcl'.1 hc.2⟩
      apply hstep attrs st hnb (hclean.2.1 s₂) (fun k g hm => ?_) hElClean
      have hmemA : .attr k (g s₁) ∈ ((attrs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)) :=
        List.mem_filter.2 ⟨List.mem_map.2 ⟨.dynVal k g, hm, rfl⟩, rfl⟩
      have hmemN := mem_managed_of_key? hmemA (a := .attr k (g s₁)) rfl
      rcases List.mem_filterMap.1 hmemN with ⟨b, hb, hbn⟩
      exact hmg k (List.mem_filterMap.2 ⟨b, by simp only [normalizeAttrs, List.mem_append]; right; exact hb, hbn⟩)
    let base : SpecElemState msg := (let cl := ((attrs.map (VAttr.eval s₁)).filterMap (fun | .cls c => some c | _ => none)).filter (· != "")
      if cl.isEmpty then [] else [Attr.cls (String.intercalate " " cl)]).foldl stepSpecAttr {}
    have hdd1 := dedupAttrs_foldl_equiv ((attrs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)) base
      (List.all_eq_true.2 fun a ha => (List.all_eq_true.1 (hclean.2.2.1 s₁)) a (List.mem_filter.1 ha).1)
    have hdd2 := dedupAttrs_foldl_equiv ((attrs.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true)) base
      (List.all_eq_true.2 fun a ha => (List.all_eq_true.1 (hclean.2.2.1 s₂)) a (List.mem_filter.1 ha).1)
    have hev1 : evalSpecAttrs (attrs.map (VAttr.eval s₁)) =
        (dedupAttrs ((attrs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true))).foldl stepSpecAttr base := by
      simp only [evalSpecAttrs, normalizeAttrs, List.foldl_append]; dsimp only [base]; congr 1
    have hev2 : evalSpecAttrs (attrs.map (VAttr.eval s₂)) =
        (dedupAttrs ((attrs.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true))).foldl stepSpecAttr base := by
      simp only [evalSpecAttrs, normalizeAttrs, List.foldl_append]; dsimp only [base]; congr 1
      refine congrArg (fun (xs : List String) => List.foldl stepSpecAttr {}
        (let cl := xs.filter (· != ""); if cl.isEmpty then [] else [Attr.cls (String.intercalate " " cl)])) ?_
      exact (congrArg (fun f => (attrs.map (VAttr.eval s₂)).filterMap f) (funext fun x => by cases x <;> rfl)).trans
        ((filterMap_cls_eq_of_noBind s₁ s₂ attrs hnb).symm.trans
          (congrArg (fun f => (attrs.map (VAttr.eval s₁)).filterMap f) (funext fun x => by cases x <;> rfl)))
    have heq1 : ElemStateEquiv st (((attrs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr base) :=
      ⟨fun k => (heq.1 k).trans (by rw [hev1]; exact hdd1.1 k),
       heq.2.1.trans (by rw [hev1]; exact hdd1.2.1),
       heq.2.2.1.trans (by rw [hev1]; exact hdd1.2.2.1),
       fun e => (heq.2.2.2.1 e).trans (by rw [hev1]; exact hdd1.2.2.2.1 e),
       fun e => (heq.2.2.2.2 e).trans (by rw [hev1]; exact hdd1.2.2.2.2 e)⟩
    have hstepEq := stepDynAttr_equiv s₂ attrs heq1
    refine ⟨rfl, fun m hm => DomArena.get_set_ne _ _ hm, st', mg, DomArena.get_set_self _ _ _, hEl',
      ⟨?_, ?_, ?_, fun e => ?_, fun e => ?_⟩,
      fun nm hnm => hmg nm (hmgEq ▸ hnm)⟩
    · intro k
      by_cases hkv : k = "value"
      · subst hkv
        exact (hEl'.2 "value" rfl).trans ((ElemClean_evalSpecAttrs (hclean.2.1 s₂)).2 "value" rfl).symm
      · cases hr : lastDynVal? k s₂ attrs with
        | some v =>
            have h1 := stepDynAttr_last_key s₂ k attrs (((attrs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr base) hnb
            rw [hr] at h1
            have h2 := (nonCls_last_key s₂ k attrs base v hnb hclean.2.2.2 (hclean.1 s₂) hr).2 hkv
            refine (hstepEq.1 k).trans ((h1.2 hkv).trans (h2.symm.trans ?_))
            rw [hev2]; exact (hdd2.1 k).symm
        | none =>
            have h1 := stepDynAttr_last_key s₂ k attrs (((attrs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr base) hnb
            rw [hr] at h1
            have h2 := (nonCls_none_key s₁ s₂ k attrs base base hnb hr).2 hkv rfl
            refine (hstepEq.1 k).trans ((h1.2 hkv).trans (h2.trans ?_))
            rw [hev2]; exact (hdd2.1 k).symm
    · cases hr : lastDynVal? "value" s₂ attrs with
      | some v =>
          have h1 := stepDynAttr_last_key s₂ "value" attrs (((attrs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr base) hnb
          rw [hr] at h1
          have h2 := (nonCls_last_key s₂ "value" attrs base v hnb hclean.2.2.2 (hclean.1 s₂) hr).1 rfl
          refine hstepEq.2.1.trans ((h1.1 rfl).trans (h2.symm.trans ?_))
          rw [hev2]; exact hdd2.2.1.symm
      | none =>
          have h1 := stepDynAttr_last_key s₂ "value" attrs (((attrs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr base) hnb
          rw [hr] at h1
          have h2 := (nonCls_none_key s₁ s₂ "value" attrs base base hnb hr).1 rfl rfl
          refine hstepEq.2.1.trans ((h1.1 rfl).trans (h2.trans ?_))
          rw [hev2]; exact hdd2.2.1.symm
    · refine hstepEq.2.2.1.trans ((stepDynAttr_checked s₂ attrs _ hnb).trans ((nonCls_checked_eq s₁ s₂ attrs base base hnb rfl).trans ?_))
      rw [hev2]; exact hdd2.2.2.1.symm
    · rw [hstepEq.2.2.2.1 e, (stepDynAttr_clicks_inputs s₂ attrs _ hnb).1,
        (nonCls_handlers_eq s₁ s₂ attrs base base hnb rfl rfl).1, hev2]
      exact (hdd2.2.2.2.1 e).symm
    · rw [hstepEq.2.2.2.2 e, (stepDynAttr_clicks_inputs s₂ attrs _ hnb).2,
        (nonCls_handlers_eq s₁ s₂ attrs base base hnb rfl rfl).2, hev2]
      exact (hdd2.2.2.2.2 e).symm

end Qed
