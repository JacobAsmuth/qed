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

private theorem normalKey_slotUpdate_iff {msg : Type} {a b : Attr msg} {k : String}
    (ha : a.key? = some k) (hb : b.key? = some k) (haN : a.NormalKey = true) (hbN : b.NormalKey = true)
    (sl : AttrSlot) : (a.slotUpdate? sl).isSome = true → (b.slotUpdate? sl).isSome = true := by
  have hslot : ∀ {x : Attr msg}, x.key? = some k → x.NormalKey = true →
      ((x.slotUpdate? sl).isSome = true ↔
        (k = "value" ∧ sl = .val) ∨ (k = "checked" ∧ sl = .chk) ∨
        (k ≠ "value" ∧ k ≠ "checked" ∧ sl = .attr k)) := fun {x} hxk hxN => by
    cases x with
    | attr kx _ | flag kx _ =>
        simp only [Attr.key?, Option.some.injEq] at hxk; subst hxk
        cases sl with
        | attr k' =>
            dsimp only [Attr.slotUpdate?]; split
            · rename_i h; simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h
              rcases h with ⟨h1, rfl⟩
              first | (have hnc : kx ≠ "checked" := fun h => by subst h; exact Bool.noConfusion hxN
                       simp [h1, hnc])
                    | (have hnv : kx ≠ "value" := fun h => by subst h; exact Bool.noConfusion hxN
                       simp [h1, hnv])
            · rename_i h; simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, not_and] at h
              exact ⟨(fun hc => nomatch hc), fun
                | .inl ⟨_, hc⟩ | .inr (.inl ⟨_, hc⟩) => nomatch hc
                | .inr (.inr ⟨hnv, hnc, hEq⟩) => absurd (AttrSlot.attr.inj hEq).symm (by first | exact h hnv | exact h hnc)⟩
        | val | chk | click _ | input _ =>
            first | (have hnc : kx ≠ "checked" := fun h => by subst h; exact Bool.noConfusion hxN
                     simp [Attr.slotUpdate?, beq_iff_eq, hnc])
                  | (have hnv : kx ≠ "value" := fun h => by subst h; exact Bool.noConfusion hxN
                     simp [Attr.slotUpdate?, beq_iff_eq, hnv])
    | _ => simp [Attr.key?] at hxk
  exact (hslot hb hbN).2 ∘ (hslot ha haN).1

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
            have ih := dedupAttrs_foldl_equiv xs cur hn.2
            intro sl; refine (ih sl).trans (foldl_stepSpecAttr_read sl xs cur (stepSpecAttr cur x) ?_)
            cases hxu : x.slotUpdate? sl with
            | some _ => exact .inl ⟨y, hy, normalKey_slotUpdate_iff hx (beq_iff_eq.1 hyk) hn.1 ((List.all_eq_true.1 hn.2) y hy) sl (by rw [hxu]; rfl)⟩
            | none => exact .inr (by rw [read_stepSpecAttr, hxu]; rfl)
          · simp only [dedupAttrs, hx, hany, Bool.false_eq_true, ↓reduceIte, List.foldl_cons]
            exact dedupAttrs_foldl_equiv xs (stepSpecAttr cur x) hn.2

private theorem stepDynAttr_equiv {σ msg : Type} (s : σ) :
    ∀ (xs : List (VAttr σ msg)) {s₁ s₂ : SpecElemState msg}, ElemStateEquiv s₁ s₂ →
      ElemStateEquiv (xs.foldl (stepDynAttr s) s₁) (xs.foldl (stepDynAttr s) s₂)
  | [], _, _, h => h
  | va :: xs, _, _, h => by
      apply stepDynAttr_equiv s xs
      cases va with | stat _ => exact h | bind _ | dynOn _ _ | dynVal _ _ => exact stepSpecAttr_equiv _ h

private def lastDynSlot? {σ msg : Type} (sl : AttrSlot) (s : σ) : List (VAttr σ msg) → Option (SlotVal msg)
  | [] => none
  | .dynVal k' g :: rest => (lastDynSlot? sl s rest).orElse (fun _ => (Attr.attr k' (g s)).slotUpdate? sl)
  | _ :: rest => lastDynSlot? sl s rest

private theorem stepDynAttr_read {σ msg : Type} (sl : AttrSlot) (s : σ) :
    ∀ (xs : List (VAttr σ msg)) (st : SpecElemState msg), noBind xs = true →
      sl.read (xs.foldl (stepDynAttr s) st) = (lastDynSlot? sl s xs).getD (sl.read st)
  | [], _, _ => rfl
  | va :: rest, st, hnb => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      cases va with
      | bind _ | dynOn _ _ => exact absurd hnb.1 Bool.false_ne_true
      | stat _ => exact stepDynAttr_read sl s rest st hnb.2
      | dynVal k' g =>
          rw [List.foldl_cons, stepDynAttr, stepDynAttr_read sl s rest _ hnb.2, read_stepSpecAttr]
          dsimp only [lastDynSlot?, Option.orElse]
          cases lastDynSlot? sl s rest <;> rfl

private theorem ownsChildren_map_tail {σ msg : Type} (s : σ) (va : VAttr σ msg) (rest : List (VAttr σ msg))
    (h : ownsChildren ((va :: rest).map (VAttr.eval s)) = false) :
    ownsChildren (rest.map (VAttr.eval s)) = false := by
  simp only [ownsChildren, List.map_cons, List.any_cons, Bool.or_eq_false_iff] at h; exact h.2

private theorem nonCls_read_last {σ msg : Type} (sl : AttrSlot) (s : σ) :
    ∀ (xs : List (VAttr σ msg)) (st : SpecElemState msg) (v : SlotVal msg),
      noBind xs = true → dynValNoLaterStat xs = true → ownsChildren (xs.map (VAttr.eval s)) = false →
      lastDynSlot? sl s xs = some v →
      sl.read (((xs.map (VAttr.eval s)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st) = v
  | [], _, _, _, _, _, h => by cases h
  | va :: rest, st, v, hnb, hns, hown, hs => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      have hownR := ownsChildren_map_tail s va rest hown
      have hnsR : dynValNoLaterStat rest = true := by
        cases va with | bind _ | dynOn _ _ => exact absurd hnb.1 Bool.false_ne_true | stat _ => exact hns | dynVal _ _ => simp only [dynValNoLaterStat, Bool.and_eq_true] at hns; exact hns.2
      cases va with
      | bind _ | dynOn _ _ => exact absurd hnb.1 Bool.false_ne_true
      | stat a => cases a <;> exact nonCls_read_last sl s rest _ v hnb.2 hnsR hownR hs
      | dynVal k' g =>
          cases hr : lastDynSlot? sl s rest with
          | some v' =>
              simp only [lastDynSlot?, Option.orElse, hr, Option.some.injEq] at hs; subst hs
              exact nonCls_read_last sl s rest _ v' hnb.2 hnsR hownR hr
          | none =>
              simp only [lastDynSlot?, Option.orElse, hr] at hs
              simp only [dynValNoLaterStat, Bool.and_eq_true, List.all_eq_true] at hns
              have hslKey : (sl = .val ∧ k' = "value") ∨ (∃ k, sl = .attr k ∧ k' = k) := by
                cases sl <;> simp only [Attr.slotUpdate?] at hs <;> first | (split at hs <;> first | (rename_i h; simp only [Bool.and_eq_true, beq_iff_eq] at h; first | exact .inl ⟨rfl, h⟩ | exact .inr ⟨_, rfl, h.2⟩) | cases hs) | cases hs
              have hbn : ∀ (x : Attr msg), x.key? ≠ some k' → (match x with | .cls _ | .localCell .. => False | _ => True) → x.slotUpdate? sl = none := fun x hx hok => by
                rcases hslKey with ⟨rfl, rfl⟩ | ⟨k, rfl, rfl⟩ <;> cases x <;> simp only [Attr.slotUpdate?] <;>
                  first | exact False.elim hok | rfl | (rw [if_neg]; simp only [Bool.and_eq_true, beq_iff_eq]; first | (intro h; exact hx (congrArg some h)) | (intro h; exact hx (congrArg some h.2)))
              have hpres : ∀ (ys : List (VAttr σ msg)) (cur : SpecElemState msg),
                  noBind ys = true → ownsChildren (ys.map (VAttr.eval s)) = false → lastDynSlot? sl s ys = none →
                  (∀ w ∈ ys, (match w with | .stat a => a.key? != some k' | _ => true) = true) →
                  sl.read (((ys.map (VAttr.eval s)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr cur) = sl.read cur := by
                intro ys; induction ys with
                | nil => intro _ _ _ _ _; rfl
                | cons w ws ihw =>
                    intro cur hnbw hownw hnw hstw
                    simp only [noBind, List.all_cons, Bool.and_eq_true] at hnbw
                    have hownwR := ownsChildren_map_tail s w ws hownw
                    cases w with
                    | bind _ | dynOn _ _ => exact absurd hnbw.1 Bool.false_ne_true
                    | dynVal kw gw =>
                        cases hrw : lastDynSlot? sl s ws with
                        | some _ => simp only [lastDynSlot?, Option.orElse, hrw, reduceCtorEq] at hnw
                        | none =>
                            simp only [lastDynSlot?, Option.orElse, hrw] at hnw
                            exact (ihw (stepSpecAttr cur (.attr kw (gw s))) hnbw.2 hownwR hrw (fun u hu => hstw u (.tail _ hu))).trans (by rw [read_stepSpecAttr, hnw]; rfl)
                    | stat b =>
                        have hb : b.key? ≠ some k' := bne_iff_ne.1 (hstw (.stat b) (.head _))
                        cases b with
                        | cls _ => exact ihw cur hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
                        | localCell _ _ _ _ _ => simp only [ownsChildren, List.map_cons, VAttr.eval, List.any_cons, Bool.true_or, Bool.true_eq_false] at hownw
                        | attr _ _ | flag _ _ | key _ | on _ _ | onValue _ _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ =>
                            exact (ihw (stepSpecAttr cur _) hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))).trans (by dsimp only [VAttr.eval]; rw [read_stepSpecAttr, hbn _ hb trivial]; rfl)
              have hp := hpres rest (stepSpecAttr st (.attr k' (g s))) hnb.2 hownR hr (fun w hw => hns.1 w hw)
              exact hp.trans (by rw [read_stepSpecAttr, hs]; rfl)

private theorem nonCls_read_none {σ msg : Type} (sl : AttrSlot) (s₁ s₂ : σ) :
    ∀ (xs : List (VAttr σ msg)) (st₁ st₂ : SpecElemState msg),
      noBind xs = true → lastDynSlot? sl s₂ xs = none → sl.read st₁ = sl.read st₂ →
      sl.read (((xs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₁) =
      sl.read (((xs.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₂)
  | [], _, _, _, _, h => h
  | va :: rest, st₁, st₂, hnb, hn, heq => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      cases va with
      | bind _ | dynOn _ _ => exact absurd hnb.1 Bool.false_ne_true
      | stat a =>
          cases a with
          | cls _ => exact nonCls_read_none sl s₁ s₂ rest st₁ st₂ hnb.2 hn heq
          | attr _ _ | flag _ _ | localCell _ _ _ _ _ | key _ | on _ _ | onValue _ _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ =>
              exact nonCls_read_none sl s₁ s₂ rest _ _ hnb.2 hn (by rw [read_stepSpecAttr, read_stepSpecAttr, heq]; rfl)
      | dynVal k' g =>
          cases hr : lastDynSlot? sl s₂ rest with
          | some _ => simp only [lastDynSlot?, Option.orElse, hr, reduceCtorEq] at hn
          | none =>
              simp only [lastDynSlot?, Option.orElse, hr] at hn
              have hn1 : (@Attr.attr msg k' (g s₁)).slotUpdate? sl = none := by
                cases sl <;> simp only [Attr.slotUpdate?] at hn ⊢ <;> split at hn <;> simp_all
              exact nonCls_read_none sl s₁ s₂ rest _ _ hnb.2 hr (by dsimp only [VAttr.eval]; rw [read_stepSpecAttr, read_stepSpecAttr, hn, hn1]; exact heq)

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
    have ⟨hnx, hne⟩ := applyAttrsM_preserves (a.set node (.element ns tag st mg cs)) node (attrs.map (VAttr.eval s₂))
    rcases hm with ⟨st', hget, heqv', hElClean'⟩
    exact ⟨hnx, fun m hm => (hne m hm).trans (DomArena.get_set_ne _ _ hm),
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
      simp only [evalSpecAttrs, normalizeAttrs, List.foldl_append]; dsimp only [base]
      erw [← filterMap_cls_eq_of_noBind s₁ s₂ attrs hnb]; rfl
    have hstepEq := stepDynAttr_equiv s₂ attrs (heq.trans (hev1 ▸ hdd1))
    refine ⟨rfl, fun m hm => DomArena.get_set_ne _ _ hm, st', mg, DomArena.get_set_self _ _ _, hEl',
      fun sl => ?_, fun nm hnm => hmg nm (hmgEq ▸ hnm)⟩
    rw [hstepEq sl, stepDynAttr_read sl s₂ attrs _ hnb, hev2, hdd2 sl]
    cases hr : lastDynSlot? sl s₂ attrs with
    | some v => exact (nonCls_read_last sl s₂ attrs base v hnb hclean.2.2.2 (hclean.1 s₂) hr).symm
    | none => exact nonCls_read_none sl s₁ s₂ attrs base base hnb hr rfl

end Qed
