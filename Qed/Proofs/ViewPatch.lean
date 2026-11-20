import Qed.Proofs.DomArena
import Qed.Proofs.KeyedReconcile

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
  simp [patchViewM, StateT.run, pure, StateT.pure, hbeq, View.render, heval, hdom]

theorem patchViewM_dyn_spec {σ msg : Type} (get : σ → String) (s₁ s₂ : σ)
    (parent node : Dom.Node) (idx : UInt32) (a : DomArena msg) (fuel : Nat) (hf : 0 < fuel) :
    let a0 := a.set node (.text (get s₁))
    let (vst', a') :=
      (patchViewM (m := StateM (DomArena msg)) parent idx (.dyn get) s₂ (.dyn node (get s₁))).run a0
    vst' = .dyn node (get s₂) ∧ readDomTree fuel a' node = specDom "" (View.render (.dyn get) s₂) := by
  cases fuel with
  | zero => omega
  | succ _ =>
      dsimp only
      by_cases heq : get s₂ = get s₁
      · simp [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, heq, readDomTree, DomArena.get_set_self, specDom, View.render]
      · simp [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, heq, MonadDom.setText, DomArena.modify, DomArena.get_set_self, readDomTree, specDom, View.render]

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

private theorem managedNames_eq_of_noBind {σ msg : Type} {s₁ s₂ : σ} :
    ∀ {xs : List (VAttr σ msg)}, noBind xs = true →
      (normalizeAttrs (xs.map (VAttr.eval s₂))).filterMap managedAttrName =
      (normalizeAttrs (xs.map (VAttr.eval s₁))).filterMap managedAttrName := by
  have hcls : ∀ (ys : List (VAttr σ msg)), noBind ys = true →
      (ys.map (VAttr.eval s₁)).filterMap (fun | .cls c => some c | _ => none) =
      (ys.map (VAttr.eval s₂)).filterMap (fun | .cls c => some c | _ => none) := by
    intro ys; induction ys with
    | nil => intro _; rfl
    | cons va rest ih =>
        intro hn; simp only [noBind, List.all_cons, Bool.and_eq_true] at hn
        cases va with
        | bind _ | dynOn _ _ => simp at hn
        | dynVal _ _ => simpa using ih hn.2
        | stat a => cases a <;> simp [ih hn.2]
  have hany : ∀ (k : String) (xs ys : List (Attr msg)), AttrKeyEq xs ys →
      xs.any (·.key? == some k) = ys.any (·.key? == some k) := fun k => by
    intro xs; induction xs with
    | nil => intro ys h; cases ys with | nil => rfl | cons _ _ => exact False.elim h
    | cons x' xs' ih' => intro ys h; cases ys with | nil => exact False.elim h | cons y' ys' => simp [List.any_cons, h.1, ih' ys' h.2.2]
  have hdd : ∀ (xs ys : List (Attr msg)), AttrKeyEq xs ys → AttrKeyEq (dedupAttrs xs) (dedupAttrs ys) := by
    intro xs; induction xs with
    | nil => intro ys h; cases ys with | nil => simpa [dedupAttrs] using h | cons _ _ => exact False.elim h
    | cons x xs ih =>
        intro ys h; cases ys with
        | nil => exact False.elim h
        | cons y ys =>
            rcases h with ⟨hk, hm, htl⟩
            have hih := ih ys htl
            cases hx : x.key? with
            | none => have hy : y.key? = none := hk.symm.trans hx; simpa [dedupAttrs, hx, hy] using ⟨hk, hm, hih⟩
            | some k =>
                have hy : y.key? = some k := hk.symm.trans hx
                simp only [dedupAttrs, hx, hy, hany k xs ys htl]; split; exact hih; exact ⟨hk, hm, hih⟩
  have hfm : ∀ (xs ys : List (Attr msg)), AttrKeyEq xs ys → ys.filterMap managedAttrName = xs.filterMap managedAttrName := by
    intro xs; induction xs with
    | nil => intro ys h; cases ys with | nil => rfl | cons _ _ => exact False.elim h
    | cons x xs ih => intro ys h; cases ys with | nil => exact False.elim h | cons y ys => simp [List.filterMap, h.2.1, ih ys h.2.2]
  have hnon : ∀ (ys : List (VAttr σ msg)), noBind ys = true →
      AttrKeyEq ((ys.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true))
                ((ys.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true)) := by
    intro ys; induction ys with
    | nil => intro _; trivial
    | cons va rest ih =>
        intro hn; simp only [noBind, List.all_cons, Bool.and_eq_true] at hn
        cases va with | bind _ | dynOn _ _ => simp at hn | dynVal _ _ => exact ⟨rfl, rfl, ih hn.2⟩ | stat a => cases a <;> simp [AttrKeyEq, ih hn.2]
  intro xs hnb
  unfold normalizeAttrs; dsimp only
  erw [← hcls xs hnb]
  rw [List.filterMap_append, List.filterMap_append]; erw [hfm _ _ (hdd _ _ (hnon xs hnb))]; rfl

private theorem stepSpecAttr_equiv {msg : Type} {s₁ s₂ : SpecElemState msg} (a : Attr msg)
    (he : ElemStateEquiv s₁ s₂) : ElemStateEquiv (stepSpecAttr s₁ a) (stepSpecAttr s₂ a) := by
  refine ⟨fun k => ?_, ?_, ?_, fun e => ?_, fun e => ?_⟩
  · cases a with
    | cls _ | localCell _ _ _ _ _ => simp [stepSpecAttr, lookupAssoc_setAssoc, he.1]
    | attr k' _ => by_cases hv : k' = "value" <;> simp [stepSpecAttr, hv, lookupAssoc_setAssoc, he.1]
    | flag k' p => by_cases hc : k' = "checked" <;> cases p <;> simp [stepSpecAttr, hc, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc, he.1] <;> split <;> exact he.1 k
    | key _ | on _ _ | onValue _ _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ => exact he.1 k
  · cases a with
    | attr k' _ => by_cases hv : k' = "value" <;> simp [stepSpecAttr, hv, he.2.1]
    | flag k' _ => by_cases hc : k' = "checked" <;> simp [stepSpecAttr, hc, he.2.1]
    | _ => exact he.2.1
  · cases a with
    | attr k' _ => by_cases hv : k' = "value" <;> simp [stepSpecAttr, hv, he.2.2.1]
    | flag k' _ => by_cases hc : k' = "checked" <;> simp [stepSpecAttr, hc, he.2.2.1]
    | _ => exact he.2.2.1
  · cases a with
    | on _ _ => simp [stepSpecAttr, lookupAssoc_setAssoc, he.2.2.2.1]
    | attr k' _ => by_cases hv : k' = "value" <;> simp [stepSpecAttr, hv, he.2.2.2.1]
    | flag k' _ => by_cases hc : k' = "checked" <;> simp [stepSpecAttr, hc, he.2.2.2.1]
    | _ => exact he.2.2.2.1 e
  · cases a with
    | onValue _ _ => simp [stepSpecAttr, lookupAssoc_setAssoc, he.2.2.2.2]
    | attr k' _ => by_cases hv : k' = "value" <;> simp [stepSpecAttr, hv, he.2.2.2.2]
    | flag k' _ => by_cases hc : k' = "checked" <;> simp [stepSpecAttr, hc, he.2.2.2.2]
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
                · subst hv; right; cases x with | attr kx _ => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; rfl | flag _ _ => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; exact False.elim (by simpa [Attr.NormalKey] using hn.1) | _ => simp [Attr.key?] at hx
                · by_cases hc : k' = "checked"
                  · subst hc; right; cases x with | flag kx p => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; cases p <;> rfl | attr _ _ => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; exact False.elim (by simpa [Attr.NormalKey] using hn.1) | _ => simp [Attr.key?] at hx
                  · left; refine ⟨y, hy, ?_⟩; cases y with
                    | attr ky _ => simp only [Attr.key?, Option.some.injEq] at hyk'; subst hyk'; simp [attrWritesKey, hv]
                    | flag ky _ => simp only [Attr.key?, Option.some.injEq] at hyk'; subst hyk'; simp [attrWritesKey, hc]
                    | _ => simp [Attr.key?] at hyk'
              · right; cases x with
                | attr kx _ => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; by_cases hv : kx = "value" <;> simp [stepSpecAttr, hv, lookupAssoc_setAssoc, beq_eq_false_iff_ne.2 (Ne.symm hkEq)]
                | flag kx p => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; by_cases hc : kx = "checked" <;> cases p <;> simp [stepSpecAttr, hc, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc, beq_eq_false_iff_ne.2 (Ne.symm hkEq)]
                | _ => simp [Attr.key?] at hx
            · apply foldl_stepSpecAttr_val
              by_cases hv : k = "value"
              · subst hv; right; cases y with
                | attr ky v => simp only [Attr.key?, Option.some.injEq] at hyk'; subst hyk'; exact ⟨v, hy⟩
                | flag ky _ => simp only [Attr.key?, Option.some.injEq] at hyk'; subst hyk'; simp [Attr.NormalKey] at hyN
                | _ => simp [Attr.key?] at hyk'
              · left; cases x with
                | attr kx _ => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; simp [stepSpecAttr]
                | flag kx p => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; by_cases hc : kx = "checked" <;> simp [stepSpecAttr, hc]
                | _ => simp [Attr.key?] at hx
            · apply foldl_stepSpecAttr_chk
              by_cases hc : k = "checked"
              · subst hc; right; cases y with
                | flag ky p => simp only [Attr.key?, Option.some.injEq] at hyk'; subst hyk'; exact ⟨p, hy⟩
                | attr ky _ => simp only [Attr.key?, Option.some.injEq] at hyk'; subst hyk'; simp [Attr.NormalKey] at hyN
                | _ => simp [Attr.key?] at hyk'
              · left; cases x with
                | attr kx _ => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; by_cases hv : kx = "value" <;> simp [stepSpecAttr, hv]
                | flag kx _ => simp only [Attr.key?, Option.some.injEq] at hx; subst hx; simp [stepSpecAttr]
                | _ => simp [Attr.key?] at hx
            · apply foldl_stepSpecAttr_clicks; right
              cases x with
              | attr kx _ => by_cases hv : kx = "value" <;> simp [stepSpecAttr, hv]
              | flag kx _ => by_cases hc : kx = "checked" <;> simp [stepSpecAttr, hc]
              | _ => simp [Attr.key?] at hx
            · apply foldl_stepSpecAttr_inputs; right
              cases x with
              | attr kx _ => by_cases hv : kx = "value" <;> simp [stepSpecAttr, hv]
              | flag kx _ => by_cases hc : kx = "checked" <;> simp [stepSpecAttr, hc]
              | _ => simp [Attr.key?] at hx
          · simp only [dedupAttrs, hx, hany, List.foldl_cons]
            exact dedupAttrs_foldl_equiv xs (stepSpecAttr cur x) hn.2

private theorem stepDynAttr_equiv {σ msg : Type} (s : σ) :
    ∀ (xs : List (VAttr σ msg)) {s₁ s₂ : SpecElemState msg}, ElemStateEquiv s₁ s₂ →
      ElemStateEquiv (xs.foldl (stepDynAttr s) s₁) (xs.foldl (stepDynAttr s) s₂)
  | [], _, _, h => h
  | va :: xs, _, _, h => by
      apply stepDynAttr_equiv s xs
      cases va with | stat _ => exact h | bind _ | dynOn _ _ => exact stepSpecAttr_equiv _ h | dynVal _ _ => exact stepSpecAttr_equiv _ h

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
      | bind _ | dynOn _ _ => simp at hnb
      | stat _ => exact stepDynAttr_checked s rest st hnb.2
      | dynVal k _ => by_cases hk : k = "value" <;> simp [List.foldl_cons, stepDynAttr, stepSpecAttr, hk, stepDynAttr_checked s rest _ hnb.2]

private theorem nonCls_checked_eq {σ msg : Type} (s₁ s₂ : σ) :
    ∀ (xs : List (VAttr σ msg)) (st₁ st₂ : SpecElemState msg), noBind xs = true → st₁.checked = st₂.checked →
      (((xs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₁).checked =
      (((xs.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₂).checked
  | [], _, _, _, h => h
  | va :: rest, st₁, st₂, hnb, hc => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      cases va with
      | bind _ | dynOn _ _ => simp at hnb
      | dynVal k _ => apply nonCls_checked_eq s₁ s₂ rest _ _ hnb.2; by_cases hv : k = "value" <;> simp [stepSpecAttr, hv, hc]
      | stat a => cases a <;> (try exact nonCls_checked_eq s₁ s₂ rest _ _ hnb.2 (by simp [stepSpecAttr, hc]; all_goals (try split <;> simp [hc])))

private theorem stepDynAttr_clicks_inputs {σ msg : Type} (s : σ) :
    ∀ (xs : List (VAttr σ msg)) (st : SpecElemState msg), noBind xs = true →
      (xs.foldl (stepDynAttr s) st).clicks = st.clicks ∧
      (xs.foldl (stepDynAttr s) st).inputs = st.inputs
  | [], _, _ => ⟨rfl, rfl⟩
  | va :: rest, st, hnb => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      cases va with
      | bind _ | dynOn _ _ => simp at hnb
      | stat _ => exact stepDynAttr_clicks_inputs s rest st hnb.2
      | dynVal k _ =>
          by_cases hk : k = "value" <;> simp [List.foldl_cons, stepDynAttr, stepSpecAttr, hk, stepDynAttr_clicks_inputs s rest _ hnb.2]

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
      | bind _ | dynOn _ _ => simp at hnb
      | dynVal k _ =>
          apply nonCls_handlers_eq s₁ s₂ rest _ _ hnb.2
          · by_cases hv : k = "value" <;> simp [stepSpecAttr, hv, hcl]
          · by_cases hv : k = "value" <;> simp [stepSpecAttr, hv, hin]
      | stat a =>
          cases a with
          | cls _ => exact nonCls_handlers_eq s₁ s₂ rest _ _ hnb.2 hcl hin
          | attr k _ => by_cases hv : k = "value" <;> exact nonCls_handlers_eq s₁ s₂ rest _ _ hnb.2 (by simp [stepSpecAttr, hv, hcl]) (by simp [stepSpecAttr, hv, hin])
          | flag k p => by_cases hc : k = "checked" <;> cases p <;> exact nonCls_handlers_eq s₁ s₂ rest _ _ hnb.2 (by simp [stepSpecAttr, hc, hcl]) (by simp [stepSpecAttr, hc, hin])
          | on _ _ | onValue _ _ | key _ | localCell _ _ _ _ _ | signalBind _ | signalAttr _ _ _ | signalOn _ _ _ =>
              exact nonCls_handlers_eq s₁ s₂ rest _ _ hnb.2 (by simp [stepSpecAttr, hcl]) (by simp [stepSpecAttr, hin])

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
      | bind _ | dynOn _ _ => simp at hnb
      | stat _ => simpa [lastDynVal?] using stepDynAttr_last_key s k rest st hnb.2
      | dynVal k' g =>
          have ih := stepDynAttr_last_key s k rest (stepSpecAttr st (.attr k' (g s))) hnb.2
          cases hr : lastDynVal? k s rest with
          | some v' => rw [hr] at ih; simpa [lastDynVal?, hr] using ih
          | none =>
              rw [hr] at ih; by_cases hk' : k' = k
              · subst hk'; simp only [lastDynVal?, Option.orElse, hr, beq_self_eq_true, ↓reduceIte] at ih ⊢
                exact ⟨fun hkv => (ih.1 hkv).trans (by subst hkv; rfl),
                       fun hnk => (ih.2 hnk).trans (by simp [stepSpecAttr, lookupAssoc_setAssoc])⟩
              · have hb : (k' == k) = false := beq_eq_false_iff_ne.2 hk'
                simp only [lastDynVal?, Option.orElse, hr, hb, Bool.false_eq_true, ↓reduceIte] at ih ⊢
                refine ⟨fun hkv => (ih.1 hkv).trans (by subst hkv; simp [stepSpecAttr]),
                        fun hnk => (ih.2 hnk).trans ?_⟩
                by_cases hv : k' = "value" <;> simp [stepSpecAttr, hv, lookupAssoc_setAssoc, hb]

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
  | [], _, _, _, _, _, h => by simp [lastDynVal?] at h
  | va :: rest, st, v, hnb, hns, hown, hs => by
      simp only [noBind, List.all_cons, Bool.and_eq_true] at hnb
      have hownR := ownsChildren_map_tail s va rest hown
      have hnsR : dynValNoLaterStat rest = true := by
        cases va with | bind _ | dynOn _ _ => simp at hnb | stat _ => exact hns | dynVal _ _ => simp only [dynValNoLaterStat, Bool.and_eq_true] at hns; exact hns.2
      cases va with
      | bind _ | dynOn _ _ => simp at hnb
      | stat a => cases a <;> exact nonCls_last_key s k rest _ v hnb.2 hnsR hownR (by simpa [lastDynVal?] using hs)
      | dynVal k' g =>
          cases hr : lastDynVal? k s rest with
          | some v' =>
              have hvv' : v' = v := by simpa [lastDynVal?, hr] using hs
              subst hvv'; exact nonCls_last_key s k rest _ v' hnb.2 hnsR hownR hr
          | none =>
              have hkk' : k' = k ∧ g s = v := by
                by_cases hk : k' = k <;> simp [lastDynVal?, Option.orElse, hr, hk] at hs; subst hk; exact ⟨rfl, hs⟩
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
                    | bind _ | dynOn _ _ => simp at hnbw
                    | dynVal kw gw =>
                        cases hrw : lastDynVal? k' s ws with
                        | some _ => simp [lastDynVal?, Option.orElse, hrw] at hnw
                        | none =>
                            have hne : kw ≠ k' := by intro hEq; subst hEq; simp [lastDynVal?, Option.orElse, hrw] at hnw
                            have iht := ihw (stepSpecAttr cur (.attr kw (gw s))) hnbw.2 hownwR hrw (fun u hu => hstw u (.tail _ hu))
                            refine ⟨fun hkv => (iht.1 hkv).trans (by subst hkv; simp [stepSpecAttr]),
                                    fun hnk => (iht.2 hnk).trans ?_⟩
                            by_cases hv : kw = "value" <;> simp [stepSpecAttr, hv, lookupAssoc_setAssoc, beq_eq_false_iff_ne.2 hne]
                    | stat b =>
                        have hb : b.key? ≠ some k' := by simpa using hstw (.stat b) (.head _)
                        cases b with
                        | cls _ => exact ihw cur hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
                        | localCell _ _ _ _ _ => simp [ownsChildren] at hownw
                        | attr kb vb =>
                            have hne : kb ≠ k' := fun hEq => hb (by simp [Attr.key?, hEq])
                            have iht := ihw (stepSpecAttr cur (.attr kb vb)) hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
                            refine ⟨fun hkv => (iht.1 hkv).trans (by subst hkv; simp [stepSpecAttr]),
                                    fun hnk => (iht.2 hnk).trans ?_⟩
                            by_cases hv : kb = "value" <;> simp [stepSpecAttr, hv, lookupAssoc_setAssoc, beq_eq_false_iff_ne.2 hne]
                        | flag kb p =>
                            have hne : kb ≠ k' := fun hEq => hb (by simp [Attr.key?, hEq])
                            have iht := ihw (stepSpecAttr cur (.flag kb p)) hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
                            refine ⟨fun hkv => (iht.1 hkv).trans (by by_cases hc : kb = "checked" <;> cases p <;> simp [stepSpecAttr, hc]),
                                    fun hnk => (iht.2 hnk).trans ?_⟩
                            by_cases hc : kb = "checked" <;> cases p <;> simp [stepSpecAttr, hc, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc, beq_eq_false_iff_ne.2 hne]
                        | key kv =>
                            have iht := ihw (stepSpecAttr cur (.key kv)) hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
                            exact ⟨fun hkv => iht.1 hkv, fun hnk => iht.2 hnk⟩
                        | on ev m =>
                            have iht := ihw (stepSpecAttr cur (.on ev m)) hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
                            exact ⟨fun hkv => iht.1 hkv, fun hnk => iht.2 hnk⟩
                        | onValue ev dec =>
                            have iht := ihw (stepSpecAttr cur (.onValue ev dec)) hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
                            exact ⟨fun hkv => iht.1 hkv, fun hnk => iht.2 hnk⟩
                        | signalBind nm =>
                            have iht := ihw (stepSpecAttr cur (.signalBind nm)) hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
                            exact ⟨fun hkv => iht.1 hkv, fun hnk => iht.2 hnk⟩
                        | signalAttr nm ak av =>
                            have iht := ihw (stepSpecAttr cur (.signalAttr nm ak av)) hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
                            exact ⟨fun hkv => iht.1 hkv, fun hnk => iht.2 hnk⟩
                        | signalOn nm ev m =>
                            have iht := ihw (stepSpecAttr cur (.signalOn nm ev m)) hnbw.2 hownwR hnw (fun u hu => hstw u (.tail _ hu))
                            exact ⟨fun hkv => iht.1 hkv, fun hnk => iht.2 hnk⟩
              have hp := hpres rest (stepSpecAttr st (.attr k' (g s))) hnb.2 hownR hr (fun w hw => hns.1 w hw)
              refine ⟨fun hkv => (hp.1 hkv).trans (by subst hkv; rfl),
                      fun hnk => (hp.2 hnk).trans (by simp [stepSpecAttr, lookupAssoc_setAssoc])⟩

private theorem stepSpecAttr_lookup_congr {msg : Type} (k : String) {s₁ s₂ : SpecElemState msg}
    (ha : lookupAssoc k s₁.attrs = lookupAssoc k s₂.attrs) (a : Attr msg) :
    lookupAssoc k (stepSpecAttr s₁ a).attrs = lookupAssoc k (stepSpecAttr s₂ a).attrs := by
  cases a with
  | cls _ | localCell _ _ _ _ _ => simp only [stepSpecAttr, lookupAssoc_setAssoc]; split <;> simp [ha]
  | attr k' _ => by_cases hv : k' = "value" <;> simp [stepSpecAttr, hv, lookupAssoc_setAssoc, ha]
  | flag k' p => by_cases hc : k' = "checked" <;> cases p <;> simp [stepSpecAttr, hc, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc, ha]
  | _ => exact ha

private theorem stepSpecAttr_val_congr {msg : Type} (a : Attr msg) {s₁ s₂ : SpecElemState msg} (hv : s₁.value = s₂.value) :
    (stepSpecAttr s₁ a).value = (stepSpecAttr s₂ a).value := by
  cases a with | attr k _ => by_cases h : k = "value" <;> simp [stepSpecAttr, h, hv] | flag k _ => by_cases h : k = "checked" <;> simp [stepSpecAttr, h, hv] | _ => simp [stepSpecAttr, hv]

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
      | bind _ | dynOn _ _ => simp at hnb
      | stat a =>
          cases a with
          | cls _ => exact nonCls_none_key s₁ s₂ k rest st₁ st₂ hnb.2 hn
          | attr ak av =>
              have ih := nonCls_none_key s₁ s₂ k rest (stepSpecAttr st₁ (.attr ak av)) (stepSpecAttr st₂ (.attr ak av)) hnb.2 hn
              exact ⟨fun hkv hv => ih.1 hkv (stepSpecAttr_val_congr (.attr ak av) hv), fun hnk ha => ih.2 hnk (stepSpecAttr_lookup_congr k ha (.attr ak av))⟩
          | flag ak p =>
              have ih := nonCls_none_key s₁ s₂ k rest (stepSpecAttr st₁ (.flag ak p)) (stepSpecAttr st₂ (.flag ak p)) hnb.2 hn
              exact ⟨fun hkv hv => ih.1 hkv (stepSpecAttr_val_congr (.flag ak p) hv), fun hnk ha => ih.2 hnk (stepSpecAttr_lookup_congr k ha (.flag ak p))⟩
          | localCell l1 l2 l3 l4 l5 =>
              have ih := nonCls_none_key s₁ s₂ k rest (stepSpecAttr st₁ (.localCell l1 l2 l3 l4 l5)) (stepSpecAttr st₂ (.localCell l1 l2 l3 l4 l5)) hnb.2 hn
              exact ⟨fun hkv hv => ih.1 hkv (stepSpecAttr_val_congr (.localCell l1 l2 l3 l4 l5) hv), fun hnk ha => ih.2 hnk (stepSpecAttr_lookup_congr k ha (.localCell l1 l2 l3 l4 l5))⟩
          | key kv =>
              have ih := nonCls_none_key s₁ s₂ k rest (stepSpecAttr st₁ (.key kv)) (stepSpecAttr st₂ (.key kv)) hnb.2 hn
              exact ⟨fun hkv hv => ih.1 hkv (stepSpecAttr_val_congr (.key kv) hv), fun hnk ha => ih.2 hnk (stepSpecAttr_lookup_congr k ha (.key kv))⟩
          | on ev m =>
              have ih := nonCls_none_key s₁ s₂ k rest (stepSpecAttr st₁ (.on ev m)) (stepSpecAttr st₂ (.on ev m)) hnb.2 hn
              exact ⟨fun hkv hv => ih.1 hkv (stepSpecAttr_val_congr (.on ev m) hv), fun hnk ha => ih.2 hnk (stepSpecAttr_lookup_congr k ha (.on ev m))⟩
          | onValue ev dec =>
              have ih := nonCls_none_key s₁ s₂ k rest (stepSpecAttr st₁ (.onValue ev dec)) (stepSpecAttr st₂ (.onValue ev dec)) hnb.2 hn
              exact ⟨fun hkv hv => ih.1 hkv (stepSpecAttr_val_congr (.onValue ev dec) hv), fun hnk ha => ih.2 hnk (stepSpecAttr_lookup_congr k ha (.onValue ev dec))⟩
          | signalBind nm =>
              have ih := nonCls_none_key s₁ s₂ k rest (stepSpecAttr st₁ (.signalBind nm)) (stepSpecAttr st₂ (.signalBind nm)) hnb.2 hn
              exact ⟨fun hkv hv => ih.1 hkv (stepSpecAttr_val_congr (.signalBind nm) hv), fun hnk ha => ih.2 hnk (stepSpecAttr_lookup_congr k ha (.signalBind nm))⟩
          | signalAttr nm ak av =>
              have ih := nonCls_none_key s₁ s₂ k rest (stepSpecAttr st₁ (.signalAttr nm ak av)) (stepSpecAttr st₂ (.signalAttr nm ak av)) hnb.2 hn
              exact ⟨fun hkv hv => ih.1 hkv (stepSpecAttr_val_congr (.signalAttr nm ak av) hv), fun hnk ha => ih.2 hnk (stepSpecAttr_lookup_congr k ha (.signalAttr nm ak av))⟩
          | signalOn nm ev m =>
              have ih := nonCls_none_key s₁ s₂ k rest (stepSpecAttr st₁ (.signalOn nm ev m)) (stepSpecAttr st₂ (.signalOn nm ev m)) hnb.2 hn
              exact ⟨fun hkv hv => ih.1 hkv (stepSpecAttr_val_congr (.signalOn nm ev m) hv), fun hnk ha => ih.2 hnk (stepSpecAttr_lookup_congr k ha (.signalOn nm ev m))⟩
      | dynVal k' g =>
          cases hr : lastDynVal? k s₂ rest with
          | some _ => simp [lastDynVal?, Option.orElse, hr] at hn
          | none =>
              have hne : k' ≠ k := by intro hEq; subst hEq; simp [lastDynVal?, Option.orElse, hr] at hn
              have ih := nonCls_none_key s₁ s₂ k rest (stepSpecAttr st₁ (.attr k' (g s₁))) (stepSpecAttr st₂ (.attr k' (g s₂))) hnb.2 hr
              refine ⟨fun hkv hv => ih.1 hkv (by subst hkv; simp [stepSpecAttr, hv]),
                      fun hnk ha => ih.2 hnk (by by_cases hv : k' = "value" <;> simp [stepSpecAttr, hv, lookupAssoc_setAssoc, beq_eq_false_iff_ne.2 hne, ha])⟩

private theorem anyBind_false_noBind {σ msg : Type} (f : VAttr σ msg → Bool)
    (hf : ∀ x, f x = match x with | .bind _ | .dynOn _ _ => true | _ => false) :
    ∀ (xs : List (VAttr σ msg)), ¬(xs.any f = true) → noBind xs = true
  | [], _ => rfl
  | x :: xs, hn => by
      have hx : f x = false := by cases hfx : f x; rfl; exact False.elim (hn (by simp [List.any_cons, hfx]))
      have hxs : ¬(xs.any f = true) := fun h => hn (by simp [List.any_cons, h])
      cases x with
      | bind _ | dynOn _ _ => simp [hf] at hx
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
            | bind _ | dynOn _ _ => simp at hnb'
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
    have hclsEq : ∀ (ys : List (VAttr σ msg)), noBind ys = true →
        (ys.map (VAttr.eval s₁)).filterMap (fun | .cls c => some c | _ => none) =
        (ys.map (VAttr.eval s₂)).filterMap (fun | .cls c => some c | _ => none) := by
      intro ys; induction ys with
      | nil => intro _; rfl
      | cons va rest ih =>
          intro hn; simp only [noBind, List.all_cons, Bool.and_eq_true] at hn
          cases va with | bind _ | dynOn _ _ => simp at hn | dynVal _ _ => simpa using ih hn.2 | stat a => cases a <;> simp [ih hn.2]
    have hcls : ((attrs.map (VAttr.eval s₁)).filterMap (fun | .cls c => some c | _ => none)).filter (· != "") =
                ((attrs.map (VAttr.eval s₂)).filterMap (fun | .cls c => some c | _ => none)).filter (· != "") := by
      rw [hclsEq attrs hnb]
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
        ((hclsEq attrs hnb).symm.trans
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
        have hnv : ∀ (xs : List (VAttr σ msg)) (cur : SpecElemState msg), noBind xs = true →
            lookupAssoc "value" (xs.foldl (stepDynAttr s₂) cur).attrs = lookupAssoc "value" cur.attrs := by
          intro xs; induction xs with
          | nil => intro _ _; rfl
          | cons va rest ih =>
              intro cur hn; simp only [noBind, List.all_cons, Bool.and_eq_true] at hn
              cases va with
              | bind _ | dynOn _ _ => simp at hn
              | stat _ => exact ih cur hn.2
              | dynVal k' _ =>
                  refine (ih _ hn.2).trans ?_
                  by_cases hv : k' = "value"
                  · simp [stepDynAttr, stepSpecAttr, hv]
                  · simp [stepDynAttr, stepSpecAttr, hv, lookupAssoc_setAssoc]
        have hev : ∀ (xs : List (VAttr σ msg)) (cur₁ cur₂ : SpecElemState msg), noBind xs = true →
            lookupAssoc "value" cur₁.attrs = lookupAssoc "value" cur₂.attrs →
            lookupAssoc "value" (((xs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr cur₁).attrs =
            lookupAssoc "value" (((xs.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr cur₂).attrs := by
          intro xs; induction xs with
          | nil => intro _ _ _ h; exact h
          | cons va rest ih =>
              intro cur₁ cur₂ hn hlk; simp only [noBind, List.all_cons, Bool.and_eq_true] at hn
              cases va with
              | bind _ | dynOn _ _ => simp at hn
              | dynVal k' _ =>
                  apply ih _ _ hn.2
                  by_cases hv : k' = "value"
                  · simp [stepSpecAttr, hv, hlk]
                  · simp [stepSpecAttr, hv, lookupAssoc_setAssoc, hlk]
              | stat a =>
                  cases a with
                  | cls _ => exact ih _ _ hn.2 hlk
                  | _ => exact ih _ _ hn.2 (stepSpecAttr_lookup_congr "value" hlk _)
        refine (hstepEq.1 "value").trans ((hnv attrs _ hnb).trans ((hev attrs base base hnb rfl).trans ?_))
        rw [hev2]; exact (hdd2.1 "value").symm
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

mutual
  def VStateMatches {σ msg : Type} : View σ msg → σ → DomArena msg → Dom.Node → VState σ msg → Prop
    | .text _, _, _, n, .text n' => n' = n
    | .dyn get, s, _, n, .dyn n' last => n' = n ∧ last = get s
    | .static _, _, _, n, .stat n' => n' = n
    | .dynNode get, s, _, n, .dynNode n' last => n' = n ∧ last = get s
    | .memo sm, s, _, n, .memo n' lk lh => n' = n ∧ lk = sm.keyOf s ∧ lh = sm.eval s
    | .ifElse c y no, s, a, n, .cond wy inner =>
        wy = c s ∧ (if c s then VStateMatches y s a n inner else VStateMatches no s a n inner)
    | .element _ _ kids, s, a, n, .elem n' ks =>
        n' = n ∧ ∃ ns' tag' st mg domCs, a.get n = .element ns' tag' st mg domCs ∧
          VStateKidsMatches kids s a domCs ks
    | .keyedList _ _ keys _ _ _ rowsHtml none, s, _, n, .list n' oldKeys _ oldRowsL _ _ =>
        n' = n ∧ oldKeys = disambiguateKeys (keys s) ∧ oldRowsL = rowsHtml s
    | _, _, _, _, _ => False

  def VStateKidsMatches {σ msg : Type} :
      List (View σ msg) → σ → DomArena msg → List Dom.Node → List (VState σ msg) → Prop
    | [], _, _, [], [] => True
    | k :: ks, s, a, d :: ds, kst :: ksts =>
        d = kst.rootNode ∧ VStateMatches k s a d kst ∧ VStateKidsMatches ks s a ds ksts
    | _, _, _, _, _ => False
end

def VStateValid {σ msg : Type} (f : Nat) (ns : String) (v : View σ msg) (s : σ)
    (a : DomArena msg) (S : Nat → Prop) (vst : VState σ msg) : Prop :=
  CleanDomSubtree f ns (View.render v s) a S vst.rootNode ∧ VStateMatches v s a vst.rootNode vst

theorem VStateValid_root_mem {σ msg : Type} {f : Nat} {ns : String} {v : View σ msg} {s : σ}
    {a : DomArena msg} {S : Nat → Prop} {vst : VState σ msg} (h : VStateValid f ns v s a S vst) :
    S vst.rootNode.toNat := CleanDomSubtree_root_mem h.1

theorem VStateValid_equiv {σ msg : Type} {f : Nat} {ns : String} {v : View σ msg} {s : σ}
    {a : DomArena msg} {S : Nat → Prop} {vst : VState σ msg} (h : VStateValid f ns v s a S vst) :
    DomTreeAssocEquiv (readDomTree f a vst.rootNode) (specDom ns (View.render v s)) := CleanDomSubtree_equiv h.1

mutual
  theorem VStateMatches_frame {σ msg : Type} :
      ∀ {f : Nat} {ns : String} {v : View σ msg} {s : σ} {a a' : DomArena msg} {S : Nat → Prop} {n : Dom.Node} {vst : VState σ msg},
        (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) →
        CleanDomSubtree f ns (View.render v s) a S n → VStateMatches v s a n vst → VStateMatches v s a' n vst
    | _, _, .text _, _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | _, _, .dyn _, _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | _, _, .static _, _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | _, _, .dynNode _, _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | _, _, .memo _, _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | _, _, .keyedList _ _ _ _ _ _ _ none, _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | _, _, .keyedList _ _ _ _ _ _ _ (some _), _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | f, ns, .ifElse c y no, s, a, a', S, n, vst, hfr, hcl, h => by
        cases vst with
        | cond wy inner =>
            rcases h with ⟨hwy, hin⟩
            refine ⟨hwy, ?_⟩
            cases hc : c s <;> simp only [hc, ↓reduceIte, Bool.false_eq_true, View.render] at hcl hin ⊢
            · exact VStateMatches_frame hfr hcl hin
            · exact VStateMatches_frame hfr hcl hin
        | _ => exact False.elim h
    | f, ns, .element tag attrs kids, s, a, a', S, n, vst, hfr, hcl, h => by
        cases vst with
        | elem n' ks =>
            cases f with
            | zero => simp [CleanDomSubtree] at hcl
            | succ _ =>
                rcases h with ⟨hn, ns', tag', st, mg, domCs, hget, hks⟩
                rcases hcl with ⟨hmem, _, _, st', mg', domCs', hget', _, _, _, hcs⟩
                have hfrN := hfr n hmem
                rw [hget'] at hget; cases hget
                exact ⟨hn, _, tag, st, mg, domCs, hfrN.trans hget',
                  VStateKidsMatches_frame (fun m hm => hfr m hm.1) hcs hks⟩
        | _ => exact False.elim h

  theorem VStateKidsMatches_frame {σ msg : Type} :
      ∀ {f : Nat} {ns : String} {ks : List (View σ msg)} {s : σ} {a a' : DomArena msg} {S : Nat → Prop}
        {ds : List Dom.Node} {ksts : List (VState σ msg)},
        (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) →
        CleanDomChildren f ns (View.renderEach ks s) a S ds → VStateKidsMatches ks s a ds ksts → VStateKidsMatches ks s a' ds ksts
    | _, _, [], _, _, _, _, [], [], _, _, h => h
    | _, _, _ :: _, _, _, _, _, _ :: _, _ :: _, hfr, ⟨_, _, hSc, hSr, _, hHd, hTl⟩, ⟨hr, hm, hkt⟩ =>
        ⟨hr, VStateMatches_frame (fun m h => hfr m (hSc _ h)) hHd hm,
          VStateKidsMatches_frame (fun m h => hfr m (hSr _ h)) hTl hkt⟩
    | _, _, [], _, _, _, _, _ :: _, _, _, hc, _ | _, _, _ :: _, _, _, _, _, [], _, _, hc, _ => False.elim hc
    | _, _, [], _, _, _, _, [], _ :: _, _, _, h => False.elim h
    | _, _, _ :: _, _, _, _, _, _ :: _, [], _, _, h => False.elim h
end

theorem VStateValid_mono {σ msg : Type} {f : Nat} {ns : String} {v : View σ msg} {s : σ}
    {a : DomArena msg} {S S' : Nat → Prop} {vst : VState σ msg} (hsub : ∀ k, S k → S' k)
    (h : VStateValid f ns v s a S vst) : VStateValid f ns v s a S' vst := ⟨CleanDomSubtree_mono hsub h.1, h.2⟩

theorem VStateValid_frame {σ msg : Type} {f : Nat} {ns : String} {v : View σ msg} {s : σ}
    {a a' : DomArena msg} {S : Nat → Prop} {vst : VState σ msg}
    (hfr : ∀ m : Dom.Node, S m.toNat → a'.get m = a.get m)
    (h : VStateValid f ns v s a S vst) : VStateValid f ns v s a' S vst :=
  ⟨CleanDomSubtree_frame hfr h.1, VStateMatches_frame hfr h.1 h.2⟩

mutual
  theorem buildViewM_eq_buildDomM {σ msg : Type} (ns : String) :
      ∀ (v : View σ msg) (s : σ) (a : DomArena msg), View.DomClean v →
        let r := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
        let d := (buildDomM (m := StateM (DomArena msg)) ns (View.render v s)).run a
        r.1.1 = d.1 ∧ r.2.SameDom d.2
    | .text _, _, _, _ | .dyn _, _, _, _ | .static _, _, _, _ | .dynNode _, _, _, _ | .memo _, _, _, _ => ⟨rfl, .refl _⟩
    | .ifElse c y n, s, a, ⟨hy, hn⟩ => by
        cases hc : c s <;>
          simp only [buildViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure, hc, Bool.false_eq_true, ↓reduceIte]
        · have ih := buildViewM_eq_buildDomM ns n s a hn
          dsimp only [StateT.run] at ih
          cases hyR : buildViewM (m := StateM (DomArena msg)) ns n s a with
          | mk _ _ => rw [hyR] at ih; exact ih
        · have ih := buildViewM_eq_buildDomM ns y s a hy
          dsimp only [StateT.run] at ih
          cases hyR : buildViewM (m := StateM (DomArena msg)) ns y s a with
          | mk _ _ => rw [hyR] at ih; exact ih
    | .element tag attrs kids, s, a, ⟨ha, hks⟩ => by
        dsimp only [buildViewM, buildDomM, MonadDom.createElement, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
        cases hce : a.alloc (ArenaEntry.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag {} [] []) with
        | mk node a1 =>
            dsimp only
            cases ha1 : applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s)) a1 with
            | mk _ a2 =>
                dsimp only
                simp only [ha.1 s, Bool.not_false, ↓reduceIte, bind, StateT.bind, pure, StateT.pure]
                have hkids := buildViewKidsM_eq_buildDomListM (Dom.childNsOf ns tag) node kids s a2 hks
                dsimp only [StateT.run] at hkids
                cases hbk : buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s a2 with
                | mk _ _ =>
                    cases hbd : buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node (View.renderEach kids s) a2 with
                    | mk _ _ => dsimp only; rw [hbk, hbd] at hkids; exact ⟨rfl, hkids⟩
    | .keyedList _ _ _ _ _ _ _ (some _), _, _, h => False.elim h
    | .keyedList tag attrs keys marks rowSig rowEv rowsHtml none, s, a, ⟨ha, hrows⟩ => by
        dsimp only [buildViewM, buildDomM, MonadDom.createElement, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
        cases hce : a.alloc (ArenaEntry.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag {} [] []) with
        | mk node a1 =>
            dsimp only
            cases ha1 : applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s)) a1 with
            | mk _ a2 =>
                dsimp only
                simp only [ha.1 s, Bool.not_false, ↓reduceIte, bind, StateT.bind, pure, StateT.pure]
                have hseed := seedRowsM_sameDom s!"§{node}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a2
                dsimp only [StateT.run] at hseed
                cases hsRun : seedRowsM (m := StateM (DomArena msg)) s!"§{node}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a2 with
                | mk _ a3 =>
                    rw [hsRun] at hseed; dsimp only at hseed ⊢
                    rw [Html.map_prefixSignals_of_DomCleanList s!"§{node}§" (hrows.2.1 s)]
                    have hb := buildDomListM_sameDom (Dom.childNsOf ns tag) node (rowsHtml s) hseed
                    cases hbl1 : buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node (rowsHtml s) a3 with
                    | mk _ _ =>
                        cases hbl2 : buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node (rowsHtml s) a2 with
                        | mk _ _ => dsimp only; rw [hbl1, hbl2] at hb; exact ⟨rfl, hb⟩

  theorem buildViewKidsM_eq_buildDomListM {σ msg : Type} (ns : String) (parent : Dom.Node) :
      ∀ (ks : List (View σ msg)) (s : σ) (a : DomArena msg), View.DomCleanEach ks →
        ((buildViewKidsM (m := StateM (DomArena msg)) ns parent ks s).run a).2.SameDom
          ((buildDomListM (m := StateM (DomArena msg)) ns parent (View.renderEach ks s)).run a).2
    | [], _, _, _ => .refl _
    | k :: rest, s, a, ⟨hkCl, hrestCl⟩ => by
        have hk := buildViewM_eq_buildDomM ns k s a hkCl
        dsimp only [buildViewKidsM, buildDomListM, View.renderEach, StateT.run, bind, StateT.bind, pure, StateT.pure] at hk ⊢
        cases hbv : buildViewM (m := StateM (DomArena msg)) ns k s a with
        | mk pk a1 =>
            cases hbd : buildDomM (m := StateM (DomArena msg)) ns (View.render k s) a with
            | mk dn ad =>
                rw [hbv, hbd] at hk; dsimp only at hk ⊢
                rw [hk.1]
                have happ : ∀ (x y : DomArena msg), x.SameDom y →
                    (MonadDom.appendChild (m := StateM (DomArena msg)) parent dn x).2.SameDom
                      (MonadDom.appendChild (m := StateM (DomArena msg)) parent dn y).2 := by
                  intro x y ⟨h1, h2⟩
                  cases x; cases y; cases h1; cases h2
                  dsimp only [MonadDom.appendChild, DomArena.get, DomArena.set, DomArena.modifyChildren, DomArena.modify]
                  split <;> exact ⟨rfl, rfl⟩
                have haEq := happ a1 ad hk.2
                cases ha1 : MonadDom.appendChild (m := StateM (DomArena msg)) parent dn a1 with
                | mk _ s1 =>
                    cases ha2 : MonadDom.appendChild (m := StateM (DomArena msg)) parent dn ad with
                    | mk _ s2 =>
                        rw [ha1, ha2] at haEq; dsimp only at haEq
                        have hrest1 := buildViewKidsM_eq_buildDomListM ns parent rest s s1 hrestCl
                        have hrest2 := buildDomListM_sameDom ns parent (View.renderEach rest s) haEq
                        dsimp only [StateT.run] at hrest1
                        exact hrest1.trans hrest2
end

private theorem uint32_toNat_ofNat_lt_vp (n : Nat) (h : n < UInt32.size) :
    (UInt32.ofNat n).toNat = n := by
  simpa [UInt32.toNat_ofNat] using Nat.mod_eq_of_lt h

private theorem node_ne_of_toNat_ne {x y : Dom.Node} (h : x.toNat ≠ y.toNat) : x ≠ y :=
  fun he => h (congrArg UInt32.toNat he)

mutual
  private theorem buildViewM_vstate_clean {σ msg : Type} (ns : String) :
      ∀ (v : View σ msg) (s : σ) (a : DomArena msg) (fuel : Nat),
        View.DomClean v → 0 < a.nextId → a.nextId + htmlNodeCount (View.render v s) < UInt32.size →
        htmlDepth (View.render v s) ≤ fuel →
        let ((root, vst), a') := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
        vst.rootNode = root ∧ a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧
        a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
        (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
        CleanDomSubtree fuel ns (View.render v s) a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root ∧
        VStateMatches v s a' root vst
    | .text str, _, a, fuel, _, hpos, hbound, hdep => by
        cases fuel with | zero => simp [View.render, htmlDepth] at hdep | succ _ =>
          have hs := buildDomM_spec ns (.text str) a _ hpos hbound hdep
          have hc := CleanDomSubtree_of_buildDomM ns (.text str) a _ rfl hpos hbound hdep
          simp only [buildViewM, buildDomM, MonadDom.createText, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at hs hc ⊢
          cases hb : a.alloc (.text str) with
          | mk r a' => rw [hb] at hs hc; dsimp only at hs hc ⊢; exact ⟨rfl, hs.1, hs.2.1, Nat.le_trans hs.1 (Nat.le_of_lt hs.2.1), hs.2.2.1, hs.2.2.2.1, hc, rfl⟩
    | .dyn get, s, a, fuel, _, hpos, hbound, hdep => by
        cases fuel with | zero => simp [View.render, htmlDepth] at hdep | succ _ =>
          have hs := buildDomM_spec ns (.text (get s)) a _ hpos hbound hdep
          have hc := CleanDomSubtree_of_buildDomM ns (.text (get s)) a _ rfl hpos hbound hdep
          simp only [buildViewM, buildDomM, MonadDom.createText, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at hs hc ⊢
          cases hb : a.alloc (.text (get s)) with
          | mk r a' => rw [hb] at hs hc; dsimp only at hs hc ⊢; exact ⟨rfl, hs.1, hs.2.1, Nat.le_trans hs.1 (Nat.le_of_lt hs.2.1), hs.2.2.1, hs.2.2.2.1, hc, rfl, rfl⟩
    | .static html, _, a, fuel, hcl, hpos, hbound, hdep => by
        have hs := buildDomM_spec ns html a fuel hpos hbound hdep
        have hc := CleanDomSubtree_of_buildDomM ns html a fuel hcl hpos hbound hdep
        simp only [buildViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at hs hc ⊢
        cases hb : buildDomM (m := StateM (DomArena msg)) ns html a with
        | mk r a' => rw [hb] at hs hc; dsimp only at hs hc; exact ⟨rfl, hs.1, hs.2.1, Nat.le_trans hs.1 (Nat.le_of_lt hs.2.1), hs.2.2.1, hs.2.2.2.1, hc, rfl⟩
    | .dynNode get, s, a, fuel, hcl, hpos, hbound, hdep => by
        have hs := buildDomM_spec ns (get s) a fuel hpos hbound hdep
        have hc := CleanDomSubtree_of_buildDomM ns (get s) a fuel (hcl s) hpos hbound hdep
        simp only [buildViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at hs hc ⊢
        cases hb : buildDomM (m := StateM (DomArena msg)) ns (get s) a with
        | mk r a' => rw [hb] at hs hc; dsimp only at hs hc; exact ⟨rfl, hs.1, hs.2.1, Nat.le_trans hs.1 (Nat.le_of_lt hs.2.1), hs.2.2.1, hs.2.2.2.1, hc, rfl, rfl⟩
    | .memo sm, s, a, fuel, hcl, hpos, hbound, hdep => by
        have hs := buildDomM_spec ns (sm.eval s) a fuel hpos hbound hdep
        have hc := CleanDomSubtree_of_buildDomM ns (sm.eval s) a fuel (hcl s) hpos hbound hdep
        simp only [buildViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at hs hc ⊢
        cases hb : buildDomM (m := StateM (DomArena msg)) ns (sm.eval s) a with
        | mk r a' => rw [hb] at hs hc; dsimp only at hs hc; exact ⟨rfl, hs.1, hs.2.1, Nat.le_trans hs.1 (Nat.le_of_lt hs.2.1), hs.2.2.1, hs.2.2.2.1, hc, rfl, rfl, rfl⟩
    | .ifElse c y no, s, a, fuel, ⟨hy, hn⟩, hpos, hbound, hdep => by
        cases hc : c s
        · have ih := buildViewM_vstate_clean ns no s a fuel hn hpos (by simpa [View.render, hc] using hbound) (by simpa [View.render, hc] using hdep)
          dsimp only [StateT.run] at ih
          cases hb : buildViewM (m := StateM (DomArena msg)) ns no s a with
          | mk p a' =>
              rcases p with ⟨r, inner⟩; rw [hb] at ih; rcases ih with ⟨hroot, h1, h2, h3, h4, h5, h6, h7⟩
              dsimp only [buildViewM, View.render, StateT.run, bind]
              simp only [hc, Bool.false_eq_true, ↓reduceIte, StateT.bind, pure, StateT.pure]; rw [hb]; dsimp only
              exact ⟨hroot, h1, h2, h3, h4, h5, h6, ⟨hc.symm, by simpa [hc] using h7⟩⟩
        · have ih := buildViewM_vstate_clean ns y s a fuel hy hpos (by simpa [View.render, hc] using hbound) (by simpa [View.render, hc] using hdep)
          dsimp only [StateT.run] at ih
          cases hb : buildViewM (m := StateM (DomArena msg)) ns y s a with
          | mk p a' =>
              rcases p with ⟨r, inner⟩; rw [hb] at ih; rcases ih with ⟨hroot, h1, h2, h3, h4, h5, h6, h7⟩
              dsimp only [buildViewM, View.render, StateT.run, bind]
              simp only [hc, ↓reduceIte, StateT.bind, pure, StateT.pure]; rw [hb]; dsimp only
              exact ⟨hroot, h1, h2, h3, h4, h5, h6, ⟨hc.symm, by simpa [hc] using h7⟩⟩
    | .element tag attrs kids, s, a, fuel, ⟨haClean, hkidsClean⟩, hpos, hbound, hdep => by
        cases fuel with
        | zero => simp [View.render, htmlDepth] at hdep
        | succ f =>
            simp only [View.render, htmlNodeCount] at hbound; simp only [View.render, htmlDepth] at hdep
            let node := UInt32.ofNat a.nextId
            have hnodeNat : node.toNat = a.nextId := uint32_toNat_ofNat_lt_vp a.nextId (by omega)
            let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
            let st := evalSpecAttrs (attrs.map (VAttr.eval s))
            let mg := (normalizeAttrs (attrs.map (VAttr.eval s))).filterMap managedAttrName
            let a1 : DomArena msg := { a with nextId := a.nextId + 1 }
            let aElem := a1.set node (.element realNs tag st mg [])
            have ha1Next : a1.nextId = a.nextId + 1 := rfl
            have hkids := buildViewKidsM_vstate_clean (Dom.childNsOf ns tag) kids [] s a1 node realNs tag st mg [] [] f
              (fun _ => False) hkidsClean (by rw [hnodeNat, ha1Next]; omega) (by rw [ha1Next]; omega)
              (by rw [ha1Next]; omega) (by omega) (fun _ h => h.elim) trivial trivial
            dsimp only [StateT.run] at hkids
            rcases hkids with ⟨csNew, aBase', hOutEq, haBaseGe, haBaseBound, haOutFr, hCleanOut, hVstOut⟩
            simp only [List.nil_append] at hOutEq hCleanOut hVstOut
            rw [hOutEq] at hCleanOut hVstOut
            rw [ha1Next] at haBaseGe haBaseBound hCleanOut
            have hrun : buildViewM (m := StateM (DomArena msg)) ns (.element tag attrs kids) s a =
                ((node, VState.elem node (buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s aElem).1),
                 (buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s aElem).2) := by
              dsimp only [buildViewM, MonadDom.createElement, DomArena.alloc, bind, StateT.bind, pure, StateT.pure]
              change (match applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s)) (a1.set node (.element realNs tag {} [] [])) with
                      | (_, s0) =>
                          match buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s s0 with
                          | (ks, s1) => ((node, VState.elem node ks), s1)) = _
              rw [applyAttrsM_fresh_element a1 node realNs tag [] (attrs.map (VAttr.eval s))]; rfl
            dsimp only [StateT.run]; rw [hrun]; dsimp only; rw [hOutEq]
            have hltBase : node.toNat < (aBase'.set node (.element realNs tag st mg csNew)).nextId := by
              change node.toNat < aBase'.nextId; rw [hnodeNat]; omega
            simp only [View.render, htmlNodeCount]
            refine ⟨rfl, by rw [hnodeNat]; exact Nat.le_refl _, hltBase,
              by change a.nextId ≤ aBase'.nextId; omega, by change aBase'.nextId ≤ _; omega, fun m hm => ?_,
              ⟨⟨by rw [hnodeNat]; exact Nat.le_refl _, hltBase⟩, haClean.1 s, haClean.2.1 s, st, mg, csNew, DomArena.get_set_self _ _ _,
               ElemClean_evalSpecAttrs (haClean.2.1 s), ElemStateEquiv.refl st,
               fun nm hnm => List.contains_iff_mem.2 hnm,
               CleanDomChildren_mono (fun k hk => Or.elim hk (fun h => False.elim h) (fun h => ⟨⟨by omega, h.2⟩, by rw [hnodeNat]; omega⟩)) hCleanOut⟩,
              rfl, realNs, tag, st, mg, csNew, DomArena.get_set_self _ _ _, hVstOut⟩
            · have hne : m ≠ node := node_ne_of_toNat_ne (by rw [hnodeNat]; omega)
              rw [← hOutEq]; rw [haOutFr m (by rw [ha1Next]; omega) hne]; rfl
    | .keyedList _ _ _ _ _ _ _ (some _), _, _, _, h, _, _, _ => False.elim h
    | .keyedList tag attrs keys marks rowSig rowEv rowsHtml none, s, a, fuel, ⟨ha, hrows⟩, hpos, hbound, hdep => by
        have heq := buildViewM_eq_buildDomM ns (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s a ⟨ha, hrows⟩
        have hs := buildDomM_spec ns (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s) a fuel hpos hbound hdep
        have hc := CleanDomSubtree_of_buildDomM ns (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s) a fuel
          (View.DomClean_render (v := .keyedList tag attrs keys marks rowSig rowEv rowsHtml) ⟨ha, hrows⟩ s) hpos hbound hdep
        have hvst : ∃ oldSigs, ((buildViewM (m := StateM (DomArena msg)) ns (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s).run a).1.2 =
            let r := ((buildViewM (m := StateM (DomArena msg)) ns (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s).run a).1.1
            .list r (disambiguateKeys (keys s)) oldSigs (rowsHtml s) (marks s) s!"§{r}§" := by
          dsimp only [buildViewM, MonadDom.createElement, StateT.run, bind, StateT.bind, pure, StateT.pure]
          cases a.alloc (ArenaEntry.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag {} [] []) with
          | mk node a1 =>
              dsimp only
              cases applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s)) a1 with
              | mk _ a2 =>
                  dsimp only
                  cases seedRowsM (m := StateM (DomArena msg)) s!"§{node}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a2 with
                  | mk perRow a3 =>
                      dsimp only
                      cases buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node ((rowsHtml s).map (Html.prefixSignals s!"§{node}§")) a3 with
                      | mk _ _ =>
                          exact ⟨perRow, by simp [Html.map_prefixSignals_of_DomCleanList _ (hrows.2.1 s)]⟩
        rcases hvst with ⟨perRow, hvstEq⟩
        dsimp only [StateT.run] at heq hs hc hvstEq ⊢
        cases hbv : buildViewM (m := StateM (DomArena msg)) ns (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s a with
        | mk p1 aOut =>
            rcases p1 with ⟨root, vst⟩
            cases hbd : buildDomM (m := StateM (DomArena msg)) ns (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s) a with
            | mk droot aDom =>
                rw [hbv] at heq hvstEq; rw [hbd] at heq hs hc; dsimp only at heq hs hc hvstEq ⊢
                subst hvstEq
                rcases heq with ⟨hnEq, hsd⟩
                rw [← hnEq] at hs hc
                rw [hsd.1]
                refine ⟨rfl, hs.1, hs.2.1, Nat.le_trans hs.1 (Nat.le_of_lt hs.2.1), hs.2.2.1,
                  fun m hm => (hsd.get_eq m).trans (hs.2.2.2.1 m hm),
                  CleanDomSubtree_frame (fun m _ => hsd.get_eq m) hc, rfl, rfl, rfl⟩

  private theorem buildViewKidsM_vstate_clean {σ msg : Type} (childNs : String) :
      ∀ (ks hsAcc : List (View σ msg)) (s : σ) (aBase : DomArena msg) (parent : Dom.Node)
        (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
        (acc : List Dom.Node) (kAcc : List (VState σ msg)) (f : Nat) (Sacc : Nat → Prop),
        View.DomCleanEach ks → parent.toNat < aBase.nextId → 0 < aBase.nextId →
        aBase.nextId + htmlListNodeCount (View.renderEach ks s) < UInt32.size →
        htmlListDepth (View.renderEach ks s) ≤ f →
        (∀ k, Sacc k → parent.toNat < k ∧ k < aBase.nextId) →
        CleanDomChildren f childNs (View.renderEach hsAcc s) (aBase.set parent (.element pns ptag pst pmg acc)) Sacc acc →
        VStateKidsMatches hsAcc s (aBase.set parent (.element pns ptag pst pmg acc)) acc kAcc →
        let (ksts, aOut) := (buildViewKidsM (m := StateM (DomArena msg)) childNs parent ks s).run (aBase.set parent (.element pns ptag pst pmg acc))
        ∃ (csNew : List Dom.Node) (aBase' : DomArena msg),
          aOut = aBase'.set parent (.element pns ptag pst pmg (acc ++ csNew)) ∧
          aBase.nextId ≤ aBase'.nextId ∧
          aBase'.nextId ≤ aBase.nextId + htmlListNodeCount (View.renderEach ks s) ∧
          (∀ m, m.toNat < aBase.nextId → m ≠ parent → aOut.get m = aBase.get m) ∧
          CleanDomChildren f childNs (View.renderEach (hsAcc ++ ks) s) aOut (fun k => Sacc k ∨ (aBase.nextId ≤ k ∧ k < aOut.nextId)) (acc ++ csNew) ∧
          VStateKidsMatches (hsAcc ++ ks) s aOut (acc ++ csNew) (kAcc ++ ksts)
    | [], hsAcc, s, aBase, parent, pns, ptag, pst, pmg, acc, kAcc, _, _, _, _, _, _, _, _, hcl, hvk => by
        dsimp only [buildViewKidsM, StateT.run, pure, StateT.pure, htmlListNodeCount]
        refine ⟨[], aBase, ?_, Nat.le_refl _, ?_, fun _ _ h => DomArena.get_set_ne _ _ h, ?_, ?_⟩
        · simp [List.append_nil]
        · simp
        · exact CleanDomChildren_mono (fun _ h => .inl h) (by simpa using hcl)
        · simpa using hvk
    | k :: rest, hsAcc, s, aBase, parent, pns, ptag, pst, pmg, acc, kAcc, f, Sacc,
        ⟨hkCl, hrestCl⟩, hparLt, hpos, hbound, hdep, hSacc, hclAcc, hvkAcc => by
        simp only [View.renderEach, htmlListNodeCount] at hbound; simp only [View.renderEach, htmlListDepth] at hdep
        have hkDep : htmlDepth (View.render k s) ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
        have hrestDep : htmlListDepth (View.renderEach rest s) ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
        let a0 := aBase.set parent (.element pns ptag pst pmg acc)
        have ha0Next : a0.nextId = aBase.nextId := rfl
        have hkSpec := buildViewM_vstate_clean childNs k s a0 f hkCl hpos (by rw [ha0Next]; omega) hkDep
        dsimp only [StateT.run] at hkSpec
        cases hbK : buildViewM (m := StateM (DomArena msg)) childNs k s a0 with
        | mk p1 aMid =>
            rcases p1 with ⟨kn, kst⟩
            rw [hbK] at hkSpec
            rcases hkSpec with ⟨hkRoot, hknGe, hknLt, haMidGe, haMidBound, haMidFr, hkClean, hkMatch⟩
            rw [ha0Next] at hknGe haMidGe haMidBound haMidFr hkClean
            have hparMid : aMid.get parent = .element pns ptag pst pmg acc := by
              rw [haMidFr parent hparLt]; exact DomArena.get_set_self _ _ _
            have hknNotIn : kn ∉ acc := fun hm => by
              have := (hSacc kn.toNat (CleanDomChildren_mem hclAcc kn hm)).2; omega
            let aAfter := aMid.set parent (.element pns ptag pst pmg (acc ++ [kn]))
            have haAfterNext : aAfter.nextId = aMid.nextId := rfl
            have happRun : MonadDom.appendChild (m := StateM (DomArena msg)) parent kn aMid = ((), aAfter) := by
              cases hkG : aMid.get kn with
              | fragment fcs => exact False.elim (CleanDomSubtree_not_fragment hkClean fcs hkG)
              | null | text _ | element _ _ _ _ _ =>
                  simp [MonadDom.appendChild, hkG, DomArena.modifyChildren, DomArena.modify, hparMid, List.erase_of_not_mem hknNotIn, aAfter]
            have hSacc' : ∀ c, (Sacc c ∨ (aBase.nextId ≤ c ∧ c < aAfter.nextId)) → parent.toNat < c ∧ c < aAfter.nextId := fun c hc => by
              rcases hc with h | h; have := hSacc c h; exact ⟨this.1, by omega⟩; exact ⟨by omega, h.2⟩
            have hclAccAfter : CleanDomChildren f childNs (View.renderEach hsAcc s) aAfter Sacc acc :=
              CleanDomChildren_frame (fun m hm => by
                have hb := hSacc _ hm; rw [DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega)), haMidFr m hb.2]) hclAcc
            have hkCleanAfter : CleanDomSubtree f childNs (View.render k s) aAfter (fun c => aBase.nextId ≤ c ∧ c < aAfter.nextId) kn :=
              CleanDomSubtree_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega))) hkClean
            have hclMid : CleanDomChildren f childNs (View.renderEach (hsAcc ++ [k]) s) aAfter
                (fun c => Sacc c ∨ (aBase.nextId ≤ c ∧ c < aAfter.nextId)) (acc ++ [kn]) := by
              have hclOne : CleanDomChildren f childNs [View.render k s] aAfter (fun c => aBase.nextId ≤ c ∧ c < aAfter.nextId) [kn] :=
                ⟨_, fun _ => False, fun _ h => h, fun _ h => h.elim, fun _ _ h => h.elim, hkCleanAfter, trivial⟩
              simpa [View.renderEach_append] using CleanDomChildren_append (fun c h1 h2 => by have := (hSacc c h1).2; omega) hclAccAfter hclOne
            have hvkAccAfter : VStateKidsMatches hsAcc s aAfter acc kAcc :=
              VStateKidsMatches_frame (fun m hm => by
                have hb := hSacc _ hm; rw [DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega)), haMidFr m hb.2]) hclAcc hvkAcc
            have hkMatchAfter : VStateMatches k s aAfter kn kst :=
              VStateMatches_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega))) hkClean hkMatch
            have hvkJoin : ∀ (hs : List (View σ msg)) (ac : List Dom.Node) (kac : List (VState σ msg)),
                VStateKidsMatches hs s aAfter ac kac → VStateKidsMatches (hs ++ [k]) s aAfter (ac ++ [kn]) (kac ++ [kst]) := by
              intro hs; induction hs with
              | nil => intro ac kac hvk; cases ac <;> cases kac <;> simp [VStateKidsMatches] at hvk ⊢; exact ⟨hkRoot.symm, hkMatchAfter⟩
              | cons _ _ ihh =>
                  intro ac kac hvk
                  cases ac with | nil => simp [VStateKidsMatches] at hvk | cons _ _ =>
                    cases kac with | nil => simp [VStateKidsMatches] at hvk | cons _ _ =>
                      exact ⟨hvk.1, hvk.2.1, ihh _ _ hvk.2.2⟩
            have hvkMid := hvkJoin hsAcc acc kAcc hvkAccAfter
            have hih := buildViewKidsM_vstate_clean childNs rest (hsAcc ++ [k]) s aMid parent pns ptag pst pmg
              (acc ++ [kn]) (kAcc ++ [kst]) f (fun c => Sacc c ∨ (aBase.nextId ≤ c ∧ c < aAfter.nextId))
              hrestCl (by omega) (by omega) (by omega) hrestDep hSacc' hclMid hvkMid
            dsimp only [StateT.run] at hih ⊢
            dsimp only [buildViewKidsM, bind, StateT.bind, pure, StateT.pure]
            rw [hbK]; dsimp only; rw [happRun]; dsimp only
            cases hbR : buildViewKidsM (m := StateM (DomArena msg)) childNs parent rest s aAfter with
            | mk restKsts aOut =>
                rw [hbR] at hih; dsimp only at hih
                rcases hih with ⟨csRest, aBase', hOutEq, hGeR, hBdR, hFrR, hClR, hVkR⟩
                have hClR' : CleanDomChildren f childNs (View.renderEach (hsAcc ++ k :: rest) s) aOut
                    (fun c => (Sacc c ∨ (aBase.nextId ≤ c ∧ c < aAfter.nextId)) ∨ (aMid.nextId ≤ c ∧ c < aOut.nextId))
                    (acc ++ kn :: csRest) := by simpa [List.append_assoc] using hClR
                have haOutNext : aOut.nextId = aBase'.nextId := by rw [hOutEq]; rfl
                simp only [View.renderEach, htmlListNodeCount]
                refine ⟨kn :: csRest, aBase', by simpa [List.append_assoc] using hOutEq, by omega, by omega, fun m hmLt hmNe => ?_,
                  CleanDomChildren_mono (fun c hc => hc.elim
                    (fun h => h.elim .inl (fun h2 => .inr ⟨h2.1, by rw [haOutNext]; rw [haAfterNext] at h2; exact Nat.lt_of_lt_of_le h2.2 hGeR⟩))
                    (fun h => .inr ⟨Nat.le_trans haMidGe h.1, h.2⟩)) hClR',
                  by simpa [List.append_assoc] using hVkR⟩
                rw [hFrR m (by omega) hmNe, haMidFr m hmLt]; exact DomArena.get_set_ne _ _ hmNe
end

theorem buildViewM_vstate_spec {σ msg : Type} (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (fuel : Nat)
    (hclean : View.DomClean v) (hpos : 0 < a.nextId)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ fuel) :
    let ((root, vst), a') := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
    vst.rootNode = root ∧ a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
    (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
    VStateValid fuel ns v s a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) vst ∧
    DomTreeAssocEquiv (readDomTree fuel a' vst.rootNode) (specDom ns (View.render v s)) := by
  have h := buildViewM_vstate_clean ns v s a fuel hclean hpos hbound hdep
  dsimp only [StateT.run] at h ⊢
  rcases h with ⟨hroot, _, _, ha1, ha2, hfr, hcl, hmt⟩
  have hval : VStateValid fuel ns v s _ (fun k => a.nextId ≤ k ∧ k < _) _ := ⟨hroot ▸ hcl, hroot ▸ hmt⟩
  exact ⟨hroot, ha1, ha2, hfr, hval, VStateValid_equiv hval⟩

private theorem keyedRows_eq_of_keys_eq {σ msg : Type} {keys : σ → Array String} {rowsHtml : σ → List (Html msg)}
    (hr : KeyedRowsClean keys rowsHtml) {s₁ s₂ : σ} (hk : disambiguateKeys (keys s₂) = disambiguateKeys (keys s₁)) :
    rowsHtml s₁ = rowsHtml s₂ := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < (disambiguateKeys (keys s₁)).size
  · have hj : i < (disambiguateKeys (keys s₂)).size := hk ▸ hi
    exact hr.2.2.2 s₁ s₂ i i hi hj (by simp [hk])
  · have h1 : (rowsHtml s₁).length ≤ i := by rw [hr.1 s₁]; omega
    have h2 : (rowsHtml s₂).length ≤ i := by rw [hr.1 s₂, hk]; omega
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]

/-! ## Verified Bare-Array Index & Certifying `O(N log N)` LIS Keyed Reconciler -/

private theorem nodup_getElem_inj {α : Type} :
    ∀ {l : List α}, l.Nodup → ∀ {i j : Nat} (hi : i < l.length) (hj : j < l.length), l[i] = l[j] → i = j
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | a :: xs, hnd, i, j, hi, hj, heq => by
      rcases List.nodup_cons.1 hnd with ⟨ha, hxs⟩
      cases i <;> cases j
      · rfl
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact False.elim (ha (heq ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj)))
      · simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact False.elim (ha (heq.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi)))
      · exact congrArg Nat.succ (nodup_getElem_inj hxs (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) heq)

private theorem nodup_length_le_bound :
    ∀ (n : Nat) (l : List Dom.Node), l.Nodup → (∀ x ∈ l, x.toNat < n) → l.length ≤ n
  | 0, l, _, hb => by
      cases l with
      | nil => exact Nat.le_refl 0
      | cons x _ => exact absurd (hb x (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | n + 1, l, hnd, hb => by
      let rest := l.filter (fun x => x.toNat != n)
      have hrestNd : rest.Nodup := List.Pairwise.filter _ hnd
      have hrestB : ∀ x ∈ rest, x.toNat < n := by
        intro x hx
        have ⟨hxl, hne⟩ := List.mem_filter.1 hx
        have hlt := hb x hxl
        have hne' : x.toNat ≠ n := by simpa using hne
        omega
      have hih := nodup_length_le_bound n rest hrestNd hrestB
      have hcnt : l.length ≤ rest.length + 1 := by
        have haux : ∀ (xs : List Dom.Node), xs.Nodup →
            (∀ x ∈ xs, ∀ y ∈ xs, x.toNat = n → y.toNat = n → x = y) →
            xs.length ≤ (xs.filter (fun x => x.toNat != n)).length + 1 := by
          intro xs; induction xs with
          | nil => intro _ _; simp
          | cons a as ih =>
              intro hnd' huniq
              rcases List.nodup_cons.1 hnd' with ⟨ha, has⟩
              by_cases han : a.toNat = n
              · have hnotIn : ∀ y ∈ as, (y.toNat != n) = true := by
                  intro y hy
                  by_cases hyn : y.toNat = n
                  · exact False.elim (ha ((huniq a (List.mem_cons_self ..) y (List.mem_cons_of_mem a hy) han hyn) ▸ hy))
                  · simp [hyn]
                have hfiltAs : as.filter (fun x => x.toNat != n) = as := List.filter_eq_self.2 hnotIn
                simp [han, hfiltAs]
              · have hneB : (a.toNat != n) = true := by simp [han]
                have hrec := ih has (fun x hx y hy => huniq x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))
                simp only [List.filter_cons, hneB, ↓reduceIte, List.length_cons]
                omega
        exact haux l hnd fun x _ y _ hx hy => UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (by
          change x.toNat = y.toNat; omega))
      omega

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
                  exact False.elim (heqI (nodup_getElem_inj hnd (by simpa using Nat.lt_trans hoiLt hlt) (by simpa using hlt) (by simpa [k] using h1)))
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
    nodup_getElem_inj hliveNd (by simpa using h1) (by simpa using h2) (by simpa [Array.getD, h1, h2] using heq)
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
    ∀ (k : Nat), k ≤ newRowsL.length → ∀ (hasAnchor : Bool) (anchor : Dom.Node)
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
          (fun m => (Sold m ∨ (baseNext ≤ m ∧ m < aOut.nextId)) ∧ m ≠ node.toNat) finalCs := by
  intro k
  induction k with
  | zero =>
      intro _ _ _ cs placed Splaced a _ _ _ _ hget _ _ _ _ _ _ _ hfilt _ hSpSub _ hClPl
      simp only [reconcileLisBackM, StateT.run, pure, StateT.pure, List.take_zero, htmlListNodeCount,
        Nat.add_zero, List.drop_zero] at hClPl ⊢
      have h0 : ∀ w, filterLisNodes live sources inLis w 0 = [] := fun _ => rfl
      rw [h0 false, h0 true, List.nil_append] at hfilt
      have hcsEq : cs = placed := by
        simpa [List.filter_eq_self.2 (fun _ _ => rfl)] using hfilt
      subst hcsEq
      exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ _ => trivial, cs, hget,
        CleanDomChildren_mono (fun m hm => hSpSub m hm) hClPl⟩
  | succ k ih =>
      intro hk hasAnchor anchor cs placed Splaced a hbase hpos hbd hnodeLt hget hcsNd hha hanc
        hcsMem hDisjML hDisjMP hDisjLP hfilt hOldClean hSpSub hSpDisj hClPl
      have hkLt : k < newRowsL.length := by omega
      have htakeCnt : htmlListNodeCount (newRowsL.take (k + 1)) = htmlListNodeCount (newRowsL.take k) + htmlNodeCount newRowsL[k] := by
        rw [List.take_succ_eq_append_getElem hkLt, htmlListNodeCount_append]; simp [htmlListNodeCount]
      have hdrop : newRowsL.drop k = newRowsL[k] :: newRowsL.drop (k + 1) := List.drop_eq_getElem_cons hkLt
      have hliveInj : ∀ oi₁ oi₂, oi₁ < live.size → oi₂ < live.size → live.getD oi₁ 0 = live.getD oi₂ 0 → oi₁ = oi₂ := fun oi₁ oi₂ h1 h2 heq =>
        nodup_getElem_inj hliveNd (by simpa using h1) (by simpa using h2) (by simpa [Array.getD, h1, h2] using heq)
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
            · exact hSiDisj oi' oi (fun he => by subst he; have := hsrcInj i k (by omega) hkLt oi' hs' hsK; omega) m hm1 h2
            · exact hSpDisj i (by omega) oi' hs' m hm1 h2
          have hchildNotF : ∀ w, child ∉ filterLisNodes live sources inLis w k := fun w hm => by
            rcases (mem_filterLisNodes ..).1 hm with ⟨i, oi', hi, _, hsi, hEq⟩
            have := hliveInj oi' oi (by rw [hliveLen]; exact hsrcBound i (by omega) oi' hsi) (by rw [hliveLen]; exact hoi) hEq
            subst this; have := hsrcInj i k (by omega) hkLt oi' hsi hsK; omega
          by_cases hflK : inLis.getD k false = true
          · simp only [hflK, ↓reduceIte]
            have hmovEq : filterLisNodes live sources inLis false (k + 1) = filterLisNodes live sources inLis false k := by
              rw [filterLisNodes_succ, hflK]; simp
            have hlisEq : filterLisNodes live sources inLis true (k + 1) = filterLisNodes live sources inLis true k ++ [child] := by
              rw [filterLisNodes_succ, hflK, hsK]; simp [child]
            rw [hmovEq] at hcsMem hDisjML hDisjMP hfilt
            rw [hlisEq] at hcsMem hDisjML hDisjLP hfilt
            have hres := ih (by omega) true child cs (child :: placed) (fun m => Si oi m ∨ Splaced m) a
              hbase hpos (by omega) hnodeLt hget hcsNd rfl rfl
              (fun x => by
                rw [hcsMem x]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
                exact ⟨fun | .inl h => .inl h | .inr (.inl (.inl h)) => .inr (.inl h) | .inr (.inl (.inr rfl)) => .inr (.inr (.inl rfl)) | .inr (.inr h) => .inr (.inr (.inr h)),
                       fun | .inl h => .inl h | .inr (.inl h) => .inr (.inl (.inl h)) | .inr (.inr (.inl rfl)) => .inr (.inl (.inr rfl)) | .inr (.inr (.inr h)) => .inr (.inr h)⟩)
              (fun x hm hl => hDisjML x hm (List.mem_append_left _ hl))
              (fun x hm hp => (List.mem_cons.1 hp).elim (fun h => hchildNotF false (h ▸ hm)) (hDisjMP x hm))
              (fun x hl hp => (List.mem_cons.1 hp).elim (fun h => hchildNotF true (h ▸ hl)) (hDisjLP x (List.mem_append_left _ hl)))
              (by simpa [List.append_assoc] using hfilt)
              hOldClean hSpSub' hSpDisj' hClPl'
            dsimp only [StateT.run] at hres
            exact ⟨hres.1, by have h21 := hres.2.1; dsimp only [child] at h21; rw [htakeCnt]; omega, hres.2.2.1, hres.2.2.2⟩
          · have hflKF : inLis.getD k false = false := Bool.eq_false_iff.2 hflK
            simp only [hflKF, Bool.false_eq_true, ↓reduceIte]
            have hmovEq : filterLisNodes live sources inLis false (k + 1) = filterLisNodes live sources inLis false k ++ [child] := by
              rw [filterLisNodes_succ, hflKF, hsK]; simp [child]
            have hlisEq : filterLisNodes live sources inLis true (k + 1) = filterLisNodes live sources inLis true k := by
              rw [filterLisNodes_succ, hflKF]; simp
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
            change (StateT.bind (MonadDom.insertBeforeRef (m := StateM (DomArena msg)) node ref? child) fun _ =>
                reconcileLisBackM node childNs live sources inLis rowsArr k true child) a |> (fun r =>
              a.nextId ≤ r.2.nextId ∧ r.2.nextId ≤ a.nextId + htmlListNodeCount (newRowsL.take (k + 1)) ∧
              (∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → r.2.get m = a.get m) ∧
              ∃ finalCs, r.2.get node = .element realNs tag st' mg' finalCs ∧
                CleanDomChildren f' childNs newRowsL r.2 (fun m => (Sold m ∨ (baseNext ≤ m ∧ m < r.2.nextId)) ∧ m ≠ node.toNat) finalCs)
            rw [hrunStep]; dsimp only
            have hchildNotPl : child ∉ placed := fun hp => hDisjMP child (by simp) hp
            have hchildNotEr : child ∉ cs.erase child := List.Nodup.not_mem_erase hcsNd
            have hfiltEr : (cs.erase child).filter (fun x => !(filterLisNodes live sources inLis false k).contains x) =
                filterLisNodes live sources inLis true k ++ placed := by
              have hpEq : ∀ x ∈ cs.erase child,
                  (!(filterLisNodes live sources inLis false k).contains x) =
                  (!(filterLisNodes live sources inLis false k ++ [child]).contains x) :=
                fun x hx => by simp [show x ≠ child from fun h => hchildNotEr (h ▸ hx)]
              rw [List.filter_congr hpEq, erase_filter_of_false _ child (by simp), hfilt]
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
            have hres := ih (by omega) true child cs' (child :: placed) (fun m => Si oi m ∨ Splaced m) a1
              hbase hpos (by change a.nextId + htmlListNodeCount (newRowsL.take k) < UInt32.size; rw [htakeCnt] at hbd; omega)
              hnodeLt (DomArena.get_set_self ..) hcs'Nd rfl rfl hcs'Mem
              (fun x hm hl => hDisjML x (List.mem_append_left _ hm) hl)
              (fun x hm hp => (List.mem_cons.1 hp).elim (fun h => hchildNotF false (h ▸ hm)) (hDisjMP x (List.mem_append_left _ hm)))
              (fun x hl hp => (List.mem_cons.1 hp).elim (fun h => hchildNotF true (h ▸ hl)) (hDisjLP x hl))
              hcs'Filt hOldClean' hSpSub' hSpDisj' hClPl1
            dsimp only [StateT.run] at hres
            have ha1Next : a1.nextId = a.nextId := rfl
            exact ⟨hres.1, by have h21 := hres.2.1; rw [ha1Next] at h21; dsimp only [a1] at h21; rw [htakeCnt]; omega,
              fun m hmn hmLt => (hres.2.2.1 m hmn hmLt).trans (DomArena.get_set_ne _ _ hmn), hres.2.2.2⟩
      | none =>
          have hStepF : ∀ w, filterLisNodes live sources inLis w (k + 1) = filterLisNodes live sources inLis w k := fun w => by
            rw [filterLisNodes_succ, hsK]; cases (inLis.getD k false == w) <;> simp
          rw [hStepF false] at hcsMem hDisjML hDisjMP hfilt
          rw [hStepF true] at hcsMem hDisjML hDisjLP hfilt
          have hrowAtK : rowsArr.getD k default = newRowsL[k] := by
            have hkArr : k < rowsArr.size := by rw [← Array.length_toList, hrowsArrEq]; exact hkLt
            have h1 : rowsArr.getD k default = rowsArr[k] := by simp [Array.getD, hkArr]
            rw [h1]; exact show rowsArr.toList[k]'(by simpa using hkArr) = newRowsL[k] by simp [hrowsArrEq]
          rw [hrowAtK]
          have hrowClean : newRowsL[k].DomClean = true := by
            have hmemCl : ∀ {l : List (Html msg)}, Html.DomCleanList l = true → ∀ h ∈ l, h.DomClean = true := by
              intro l; induction l with
              | nil => intro _ _ h; nomatch h
              | cons c cs ih => intro hcl h hm; simp only [Html.DomCleanList, Bool.and_eq_true] at hcl; exact (List.mem_cons.1 hm).elim (· ▸ hcl.1) (ih hcl.2 h)
            exact hmemCl hnewClean newRowsL[k] (List.getElem_mem hkLt)
          have hrowDep : htmlDepth newRowsL[k] ≤ f' := by
            have hmemDep : ∀ {l : List (Html msg)}, ∀ h ∈ l, htmlDepth h ≤ htmlListDepth l := by
              intro l; induction l with
              | nil => intro _ h; nomatch h
              | cons c cs ih => intro h hm; simp only [htmlListDepth]; exact (List.mem_cons.1 hm).elim (· ▸ Nat.le_max_left _ _) (fun ht => Nat.le_trans (ih h ht) (Nat.le_max_right _ _))
            exact Nat.le_trans (hmemDep newRowsL[k] (List.getElem_mem hkLt)) hdep
          have hbdRow : a.nextId + htmlNodeCount newRowsL[k] < UInt32.size := by omega
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
                have hoi' := hsrcBound i (by omega) oi' hsi
                exact Nat.lt_of_lt_of_le (hSoldLt _ (hSiSub oi' _ (CleanDomSubtree_root_mem (hOldClean oi' hoi'))).1) hbase
              have hcsInA : ∀ x ∈ cs, x.toNat < a.nextId := fun x hx =>
                match (hcsMem x).1 hx with
                | .inl hm => hfiltInA false x hm
                | .inr (.inl hl) => hfiltInA true x hl
                | .inr (.inr hp) => (hSpSub x.toNat (CleanDomChildren_mem hClPl x hp)).1.elim
                    (fun hs => Nat.lt_of_lt_of_le (hSoldLt _ hs) hbase) (·.2)
              have hcnNotCs : cn ∉ cs := fun hm => by have := hcsInA cn hm; omega
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
              change (StateT.bind (buildDomM (m := StateM (DomArena msg)) childNs newRowsL[k]) fun cn' =>
                  StateT.bind (MonadDom.insertBeforeRef node ref? cn') fun _ =>
                    reconcileLisBackM node childNs live sources inLis rowsArr k true cn') a |> (fun r =>
                a.nextId ≤ r.2.nextId ∧ r.2.nextId ≤ a.nextId + htmlListNodeCount (newRowsL.take (k + 1)) ∧
                (∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → r.2.get m = a.get m) ∧
                ∃ finalCs, r.2.get node = .element realNs tag st' mg' finalCs ∧
                  CleanDomChildren f' childNs newRowsL r.2 (fun m => (Sold m ∨ (baseNext ≤ m ∧ m < r.2.nextId)) ∧ m ≠ node.toNat) finalCs)
              rw [hrunStep]; dsimp only
              have hcsErEq : cs.erase cn = cs := List.erase_of_not_mem hcnNotCs
              have ⟨hcs'Nd, hmemC', hcs'Filt⟩ := w3cInsertBeforeRef_reconcile_step hcsNd hanc hcnNotPl
                hcnNotMov hDisjMP hDisjLP (by rw [hcsErEq]; exact hfilt)
              have hcs'Mem : ∀ x, x ∈ cs' ↔ x ∈ filterLisNodes live sources inLis false k ∨ x ∈ filterLisNodes live sources inLis true k ∨ x ∈ cn :: placed := by
                intro x; rw [hmemC', hcsErEq, hcsMem x]; simp only [List.mem_cons]
                exact ⟨fun | .inl rfl => .inr (.inr (.inl rfl)) | .inr (.inl h) => .inl h | .inr (.inr (.inl h)) => .inr (.inl h) | .inr (.inr (.inr h)) => .inr (.inr (.inr h)),
                       fun | .inl h => .inr (.inl h) | .inr (.inl h) => .inr (.inr (.inl h)) | .inr (.inr (.inl rfl)) => .inl rfl | .inr (.inr (.inr h)) => .inr (.inr (.inr h))⟩
              let a2 := a1.set node (.element realNs tag st' mg' cs')
              have ha2Next : a2.nextId = a1.nextId := rfl
              have hOldClean' : ∀ oi (ho : oi < oldRowsL.length), CleanDomSubtree f' childNs oldRowsL[oi] a2 (Si oi) (live.getD oi 0) :=
                fun oi ho => CleanDomSubtree_frame (fun m hm => by
                  have hsub := hSiSub oi m.toNat hm
                  rw [DomArena.get_set_ne _ _ (node_ne_of_toNat_ne hsub.2)]
                  exact ha1Fr m (Nat.lt_of_lt_of_le (hSoldLt _ hsub.1) hbase)) (hOldClean oi ho)
              let Snew : Nat → Prop := fun m => a.nextId ≤ m ∧ m < a1.nextId
              have hSnewDisjPl : ∀ m, Snew m → Splaced m → False := fun m h1 h2 => by
                rcases (hSpSub m h2).1 with hs | ⟨_, _⟩
                · have := hSoldLt m hs; omega
                · omega
              have hcnClean2 : CleanDomSubtree f' childNs newRowsL[k] a2 Snew cn :=
                CleanDomSubtree_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (by omega))) hbuilt
              have hClPl2 : CleanDomChildren f' childNs (newRowsL.drop (k + 1)) a2 Splaced placed :=
                CleanDomChildren_frame (fun m hm => by
                  have hsp := hSpSub m.toNat hm
                  rw [DomArena.get_set_ne _ _ (node_ne_of_toNat_ne hsp.2)]
                  exact ha1Fr m (hsp.1.elim (fun hs => Nat.lt_of_lt_of_le (hSoldLt _ hs) hbase) (·.2))) hClPl
              have hClPl' : CleanDomChildren f' childNs (newRowsL.drop k) a2 (fun m => Snew m ∨ Splaced m) (cn :: placed) := by
                rw [hdrop]; exact ⟨Snew, Splaced, fun _ => .inl, fun _ => .inr, hSnewDisjPl, hcnClean2, hClPl2⟩
              have hSpSub' : ∀ m, (Snew m ∨ Splaced m) → (Sold m ∨ (baseNext ≤ m ∧ m < a2.nextId)) ∧ m ≠ node.toNat := fun m hm =>
                hm.elim (fun ⟨_, h2⟩ => ⟨.inr ⟨by omega, h2⟩, by omega⟩)
                  (fun h2 => let ⟨h, hne⟩ := hSpSub m h2; ⟨h.elim .inl (fun ⟨hb, hl⟩ => .inr ⟨hb, Nat.lt_of_lt_of_le hl ha1Ge⟩), hne⟩)
              have hSpDisj' : ∀ i, i < k → ∀ oi', sources.getD i none = some oi' → ∀ m, Si oi' m → (Snew m ∨ Splaced m) → False :=
                fun i hi oi' hs' m hm1 hm2 => hm2.elim (fun ⟨_, _⟩ => by have := hSoldLt m (hSiSub oi' m hm1).1; omega) (hSpDisj i (by omega) oi' hs' m hm1)
              have hres := ih (by omega) true cn cs' (cn :: placed) (fun m => Snew m ∨ Splaced m) a2
                (by rw [ha2Next]; omega) (by rw [ha2Next]; omega) (by rw [ha2Next]; rw [htakeCnt] at hbd; omega)
                (by rw [ha2Next]; omega) (DomArena.get_set_self ..) hcs'Nd rfl rfl hcs'Mem hDisjML
                (fun x hm hp => (List.mem_cons.1 hp).elim (fun h => hcnNotMov (h ▸ hm)) (hDisjMP x hm))
                (fun x hl hp => (List.mem_cons.1 hp).elim (fun h => hcnNotLis (h ▸ hl)) (hDisjLP x hl))
                hcs'Filt hOldClean' hSpSub' hSpDisj' hClPl'
              dsimp only [StateT.run] at hres
              refine ⟨by have h1 := hres.1; rw [ha2Next] at h1; exact Nat.le_trans ha1Ge h1,
                by have h2 := hres.2.1; rw [ha2Next] at h2; dsimp only [a2] at h2; rw [htakeCnt]; omega,
                fun m hmn hmLt => (hres.2.2.1 m hmn (by rw [ha2Next]; exact Nat.lt_of_lt_of_le hmLt ha1Ge)).trans ((DomArena.get_set_ne _ _ hmn).trans (ha1Fr m hmLt)),
                hres.2.2.2⟩

mutual
  theorem patchViewM_spec {σ msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node)
      (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
      (v : View σ msg) (s₁ s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (vst : VState σ msg)
      (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
      (hclean : View.DomClean v) (hpreLen : pre.length + 1 + suf.length < UInt32.size)
      (hbound : a.nextId + htmlNodeCount (View.render v s₂) < UInt32.size)
      (hdep : htmlDepth (View.render v s₂) ≤ f) (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId)
      (hpar : a.get parent = .element pns ptag pst pmg (pre ++ vst.rootNode :: suf))
      (hnd : (pre ++ vst.rootNode :: suf).Nodup) (hparOut : ¬Sold parent.toNat)
      (hSoldLt : ∀ k, Sold k → k < a.nextId) (hparNodes : ∀ r ∈ pre ++ vst.rootNode :: suf, r.toNat < a.nextId)
      (hval : VStateValid f childNs v s₁ a Sold vst) :
      let (vst', a') := (patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) v s₂ vst).run a
      a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render v s₂) ∧
      (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
      a'.get parent = .element pns ptag pst pmg (pre ++ vst'.rootNode :: suf) ∧ (pre ++ vst'.rootNode :: suf).Nodup ∧
      (∀ r ∈ pre ++ vst'.rootNode :: suf, r.toNat < a'.nextId) ∧
      VStateValid f childNs v s₂ a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) vst' ∧
      DomTreeAssocEquiv (readDomTree f a' vst'.rootNode) (specDom childNs (View.render v s₂)) := by
    cases v with
    | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
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
                have hne : node ≠ parent := fun h => hparOut (h ▸ hnodeMem)
                have hnodeLt : node.toNat < a.nextId := hSoldLt _ hnodeMem
                let realNs := if childNs == "" && tag == "svg" then Dom.svgNs else childNs
                dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
                have hSameKeysBranch : ∀ (hsameK : disambiguateKeys (keys s₂) = disambiguateKeys (keys s₁)),
                    let res := (StateT.bind (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂) fun _ =>
                      StateT.bind (seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ (disambiguateKeys (keys s₁))) (rowEv s₂ (disambiguateKeys (keys s₁))) (marks s₂) oldMarks oldSigs) fun newSigs =>
                        StateT.pure (VState.list node (disambiguateKeys (keys s₁)) newSigs (rowsHtml s₁) (marks s₂) inst)) a
                    a.nextId ≤ res.2.nextId ∧ res.2.nextId ≤ a.nextId + htmlNodeCount (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂) ∧
                    (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → res.2.get m = a.get m) ∧
                    res.2.get parent = .element pns ptag pst pmg (pre ++ res.1.rootNode :: suf) ∧ (pre ++ res.1.rootNode :: suf).Nodup ∧
                    (∀ r ∈ pre ++ res.1.rootNode :: suf, r.toNat < res.2.nextId) ∧
                    VStateValid (f' + 1) childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ res.2
                      (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < res.2.nextId)) res.1 ∧
                    DomTreeAssocEquiv (readDomTree (f' + 1) res.2 res.1.rootNode)
                      (specDom childNs (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂)) := by
                  intro hsameK
                  have haSet := DomArena.set_get_self a hnodeGet
                  have hdyn := applyDynAttrsM_spec a node realNs tag st mg domCs attrs s₁ s₂ haClean hElClean hElEq hmg
                  rw [haSet] at hdyn
                  rcases hdyn with ⟨ha1Next, ha1Ne, st', mg', ha1Get, hElClean', hElEq', hmg'⟩
                  let a1 := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a).2
                  have ha1Eq : applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a = ((), a1) := rfl
                  have hseed := seedRowsM_sameDom inst (rowSig s₂ (disambiguateKeys (keys s₁))) (rowEv s₂ (disambiguateKeys (keys s₁))) (marks s₂) oldMarks oldSigs a1
                  dsimp only [StateT.run] at hseed
                  have hbind : (StateT.bind (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂) fun _ =>
                      StateT.bind (seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ (disambiguateKeys (keys s₁))) (rowEv s₂ (disambiguateKeys (keys s₁))) (marks s₂) oldMarks oldSigs) fun newSigs =>
                        StateT.pure (VState.list (σ := σ) node (disambiguateKeys (keys s₁)) newSigs (rowsHtml s₁) (marks s₂) inst)) a =
                      match seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ (disambiguateKeys (keys s₁))) (rowEv s₂ (disambiguateKeys (keys s₁))) (marks s₂) oldMarks oldSigs a1 with
                      | (newSigs, aOut) => (VState.list (σ := σ) node (disambiguateKeys (keys s₁)) newSigs (rowsHtml s₁) (marks s₂) inst, aOut) := by
                    simp only [StateT.bind, StateT.pure, bind, pure]
                    rw [ha1Eq]; rfl
                  cases hsRun : seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ (disambiguateKeys (keys s₁))) (rowEv s₂ (disambiguateKeys (keys s₁))) (marks s₂) oldMarks oldSigs a1 with
                  | mk newSigs aOut =>
                      rw [hsRun] at hseed hbind; dsimp only at hseed hbind
                      rw [hbind]; dsimp only
                      have haOutNext : aOut.nextId = a.nextId := hseed.1.trans ha1Next
                      have haOutOutside : ∀ m, m ≠ node → aOut.get m = a.get m := fun m hm =>
                        (hseed.get_eq m).trans (ha1Ne m hm)
                      have hparOut' : aOut.get parent = .element pns ptag pst pmg (pre ++ node :: suf) := by
                        rw [haOutOutside parent hne.symm, hpar]
                      have hrowsEq : rowsHtml s₁ = rowsHtml s₂ := keyedRows_eq_of_keys_eq hrowsClean hsameK
                      have hCleanCsOut := CleanDomChildren_frame (fun m hm => haOutOutside m (node_ne_of_toNat_ne hm.2)) hCleanCs
                      have hvalOut : VStateValid (f' + 1) childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ aOut
                          (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) (.list node (disambiguateKeys (keys s₁)) newSigs (rowsHtml s₁) (marks s₂) inst) :=
                        ⟨⟨.inl hnodeMem, haClean.1 s₂, haClean.2.1 s₂, st', mg', domCs,
                          (hseed.get_eq node).trans ha1Get, hElClean', hElEq', hmg',
                          by rw [← hrowsEq]; exact CleanDomChildren_mono (fun k hk => ⟨.inl hk.1, hk.2⟩) hCleanCsOut⟩,
                         rfl, hsameK.symm, hrowsEq⟩
                      refine ⟨by omega, by simp only [View.render, htmlNodeCount]; omega, fun m hmPar hmOut hmLt => ?_, hparOut', hnd,
                        fun r hr => Nat.lt_of_lt_of_le (hparNodes r hr) (by omega), hvalOut, VStateValid_equiv hvalOut⟩
                      have hmNeNode : m ≠ node := fun h => hmOut (h ▸ hnodeMem)
                      exact haOutOutside m hmNeNode
                by_cases hrawEq : keys s₂ = disambiguateKeys (keys s₁)
                · have hbRaw : (keys s₂ == disambiguateKeys (keys s₁)) = true := beq_iff_eq.2 hrawEq
                  simp only [hbRaw, ↓reduceIte]
                  have hnd2 : (keys s₂).toList.Nodup := hrawEq ▸ disambiguateKeys_nodup (keys s₁)
                  have hsameK : disambiguateKeys (keys s₂) = disambiguateKeys (keys s₁) :=
                    (disambiguateKeys_of_nodup hnd2).trans hrawEq
                  exact hSameKeysBranch hsameK
                · have hbRaw : (keys s₂ == disambiguateKeys (keys s₁)) = false := beq_eq_false_iff_ne.2 hrawEq
                  simp only [hbRaw, Bool.false_eq_true, ↓reduceIte]
                  by_cases hsameK : disambiguateKeys (keys s₂) = disambiguateKeys (keys s₁)
                  · have hbK : (disambiguateKeys (keys s₂) == disambiguateKeys (keys s₁)) = true := beq_iff_eq.2 hsameK
                    simp only [hbK, ↓reduceIte]
                    exact hSameKeysBranch hsameK
                  · have hbK : (disambiguateKeys (keys s₂) == disambiguateKeys (keys s₁)) = false := beq_eq_false_iff_ne.2 hsameK
                    simp only [hbK, Bool.false_eq_true, ↓reduceIte]
                    cases hnewEmp : (disambiguateKeys (keys s₂)).isEmpty
                    · simp only [Bool.false_eq_true, ↓reduceIte]
                      cases hemp : (rowsHtml s₁).isEmpty
                      · simp only [Bool.false_eq_true, ↓reduceIte]
                        -- Non-empty → Non-empty: verified certifying `O(N log N)` LIS minimal-moves reconciler
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
                          (Nat.zero_le _) (fun _ h => by cases h) rfl (by simp) rfl
                          (fun _ hj => by omega) (fun oi ho => by simp) (fun _ hj => by omega)
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
                            have hpR := hplanSpec.2.2.2.2.2 i hi
                            rw [hpR]
                            cases hq : keyIndexGet oldBuckets mask newKeys[i] with
                            | none =>
                                have hszF : (rowsHtml s₂).toArray.size = (rowsHtml s₂).length := List.size_toArray ..
                                simp only [freshFn, hpref, Array.getD, hszF, hri, ↓reduceDIte]
                                rw [List.getElem?_eq_getElem hri]; simp
                            | some oi =>
                                have ⟨hoiK, hkeyEq?⟩ := hidxSpec.1 _ oi hq
                                have hoi1 : oi < (rowsHtml s₁).length := by rw [hrowsClean.1 s₁]; exact hoiK
                                have hkeyEq : oldKeys[oi]'hoiK = newKeys[i]'hi := by
                                  rw [Array.getElem?_eq_getElem hoiK, Option.some.injEq] at hkeyEq?; exact hkeyEq?
                                have hrowEq := hrowsClean.2.2.2 s₁ s₂ oi i hoiK hi hkeyEq
                                have hget1 : (rowsHtml s₁).toArray.getD oi default = (rowsHtml s₁)[oi] := by
                                  simp [Array.getD, hoi1]
                                dsimp only
                                rw [hget1, ← List.getElem?_eq_getElem hoi1, hrowEq]
                          · have h1 : rowsArr.size ≤ i := by
                              change plan.2.2.1.size ≤ i
                              have hszR : plan.2.2.1.size = newKeys.size := hplanSpec.2.2.1; omega
                            have h2 : (rowsHtml s₂).length ≤ i := by rw [hrowsClean.1 s₂]; dsimp only [newKeys] at hi; omega
                            rw [Array.getElem?_eq_none h1, List.getElem?_eq_none h2]
                        have hsrcSz : sources.size = (rowsHtml s₂).length := by rw [hplanSpec.1, hrowsClean.1 s₂]
                        have hsrcGet : ∀ i (hi : i < newKeys.size), sources.getD i none = keyIndexGet oldBuckets mask newKeys[i] := by
                          intro i hi
                          have hiS : i < sources.size := by rw [hplanSpec.1]; exact hi
                          have h1 := hplanSpec.2.2.2.1 i hi
                          rw [Array.getElem?_eq_getElem hiS, Option.some.injEq] at h1
                          simpa [Array.getD, hiS] using h1
                        have hsrcBound : ∀ i, i < (rowsHtml s₂).length → ∀ oi, sources.getD i none = some oi → oi < (rowsHtml s₁).length := by
                          intro i hi oi hsi
                          have hiK : i < newKeys.size := by rw [← hrowsClean.1 s₂]; exact hi
                          rw [hsrcGet i hiK] at hsi
                          rw [hrowsClean.1 s₁]; exact hidxBnd _ oi hsi
                        have hsrcInj : ∀ i₁ i₂, i₁ < (rowsHtml s₂).length → i₂ < (rowsHtml s₂).length →
                            ∀ oi, sources.getD i₁ none = some oi → sources.getD i₂ none = some oi → i₁ = i₂ := by
                          intro i₁ i₂ h1 h2 oi hs1 hs2
                          have h1K : i₁ < newKeys.size := by rw [← hrowsClean.1 s₂]; exact h1
                          have h2K : i₂ < newKeys.size := by rw [← hrowsClean.1 s₂]; exact h2
                          rw [hsrcGet i₁ h1K] at hs1; rw [hsrcGet i₂ h2K] at hs2
                          have heq1 := (hidxSpec.1 _ oi hs1).2
                          have heq2 := (hidxSpec.1 _ oi hs2).2
                          have hkeyEq : newKeys[i₁]'h1K = newKeys[i₂]'h2K := Option.some.inj (heq1.symm.trans heq2)
                          have h1L : i₁ < newKeys.toList.length := by simpa using h1K
                          have h2L : i₂ < newKeys.toList.length := by simpa using h2K
                          exact nodup_getElem_inj hnewNd h1L h2L (by simpa using hkeyEq)
                        have hsrcRow : ∀ i (hi : i < (rowsHtml s₂).length) oi (ho : oi < (rowsHtml s₁).length),
                            sources.getD i none = some oi → (rowsHtml s₁)[oi] = (rowsHtml s₂)[i] := by
                          intro i hi oi ho hsi
                          have hiK : i < newKeys.size := by rw [← hrowsClean.1 s₂]; exact hi
                          have hoK : oi < oldKeys.size := by rw [← hrowsClean.1 s₁]; exact ho
                          rw [hsrcGet i hiK] at hsi
                          have hkeyEq? := (hidxSpec.1 _ oi hsi).2
                          have hkeyEq : oldKeys[oi]'hoK = newKeys[i]'hiK := by
                            rw [Array.getElem?_eq_getElem hoK, Option.some.injEq] at hkeyEq?; exact hkeyEq?
                          have hrowEq := hrowsClean.2.2.2 s₁ s₂ oi i hoK hiK hkeyEq
                          rw [List.getElem?_eq_getElem ho, List.getElem?_eq_getElem hi, Option.some.injEq] at hrowEq
                          exact hrowEq
                        have hseed0 := seedRowsM_sameDom inst (rowSig s₂ newKeys) (rowEv s₂ newKeys) (marks s₂) marksArr sigsArr a
                        dsimp only [StateT.run] at hseed0
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
                            have hcnV : childNs = "" ∨ childNs = Dom.svgNs := by rw [hchildNs]; split <;> simp
                            have hccNs := childNamespace_eq_childNsOf (ptag := tag) hcnV
                            by_cases hnoReuse : (!used.any id) = true
                            · have hmonadEq : (StateT.bind (seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ newKeys) (rowEv s₂ newKeys) (marks s₂) marksArr sigsArr) fun newSigs =>
                                  StateT.bind (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂) fun _ =>
                                  StateT.bind (MonadDom.childNamespace node) fun cn =>
                                  if (!used.any id) = true then
                                    StateT.bind (MonadDom.clearChildren node) fun _ =>
                                    StateT.bind MonadDom.createFragment fun frag =>
                                    StateT.bind (buildDomListM cn frag rowsArr.toList) fun _ =>
                                    StateT.bind (MonadDom.appendChild node frag) fun _ =>
                                    StateT.pure (VState.list (σ := σ) node newKeys newSigs rowsArr.toList (marks s₂) inst)
                                  else
                                    StateT.bind (MonadDom.childCount node) fun oc =>
                                    StateT.bind (snapshotChildrenM node 0 #[] oc.toNat) fun lv =>
                                    StateT.bind (removeUnusedM node lv used 0) fun _ =>
                                    StateT.bind (reconcileLisBackM node cn lv sources (verifiedLisFlags sources) rowsArr newKeys.size false 0) fun _ =>
                                    StateT.pure (VState.list (σ := σ) node newKeys newSigs rowsArr.toList (marks s₂) inst)) a =
                                  (match MonadDom.clearChildren (m := StateM (DomArena msg)) node a1 with
                                  | (_, sClr) =>
                                    match MonadDom.createFragment (m := StateM (DomArena msg)) sClr with
                                    | (frag, sFrag) =>
                                      match buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf childNs tag) frag (rowsHtml s₂) sFrag with
                                      | (_, sB) =>
                                        match MonadDom.appendChild (m := StateM (DomArena msg)) node frag sB with
                                        | (_, sOut) => (VState.list (σ := σ) node newKeys newSigs (rowsHtml s₂) (marks s₂) inst, sOut)) := by
                                simp only [hnoReuse, ↓reduceIte]
                                change (match seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ newKeys) (rowEv s₂ newKeys) (marks s₂) marksArr sigsArr a with
                                  | (newSigs, s0) =>
                                    match applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ s0 with
                                    | (_, s1) =>
                                      match MonadDom.childNamespace (m := StateM (DomArena msg)) node s1 with
                                      | (cn, s2) =>
                                        match MonadDom.clearChildren (m := StateM (DomArena msg)) node s2 with
                                        | (_, s3) =>
                                          match MonadDom.createFragment (m := StateM (DomArena msg)) s3 with
                                          | (frag, s4) =>
                                            match buildDomListM (m := StateM (DomArena msg)) cn frag rowsArr.toList s4 with
                                            | (_, s5) =>
                                              match MonadDom.appendChild (m := StateM (DomArena msg)) node frag s5 with
                                              | (_, s6) => (VState.list (σ := σ) node newKeys newSigs rowsArr.toList (marks s₂) inst, s6)) = _
                                rw [hsRun]; dsimp only
                                rw [ha1Eq]; dsimp only
                                rw [ha1Get]; dsimp only [realNs]
                                rw [hccNs, hrowsArrEq]; rfl
                              change (match (StateT.bind (seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ newKeys) (rowEv s₂ newKeys) (marks s₂) marksArr sigsArr) fun newSigs =>
                                  StateT.bind (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂) fun _ =>
                                  StateT.bind (MonadDom.childNamespace node) fun cn =>
                                  if (!used.any id) = true then
                                    StateT.bind (MonadDom.clearChildren node) fun _ =>
                                    StateT.bind MonadDom.createFragment fun frag =>
                                    StateT.bind (buildDomListM cn frag rowsArr.toList) fun _ =>
                                    StateT.bind (MonadDom.appendChild node frag) fun _ =>
                                    StateT.pure (VState.list (σ := σ) node newKeys newSigs rowsArr.toList (marks s₂) inst)
                                  else
                                    StateT.bind (MonadDom.childCount node) fun oc =>
                                    StateT.bind (snapshotChildrenM node 0 #[] oc.toNat) fun lv =>
                                    StateT.bind (removeUnusedM node lv used 0) fun _ =>
                                    StateT.bind (reconcileLisBackM node cn lv sources (verifiedLisFlags sources) rowsArr newKeys.size false 0) fun _ =>
                                    StateT.pure (VState.list (σ := σ) node newKeys newSigs rowsArr.toList (marks s₂) inst)) a with
                                | (vst', a') =>
                                  a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂) ∧
                                  (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
                                  a'.get parent = .element pns ptag pst pmg (pre ++ vst'.rootNode :: suf) ∧ (pre ++ vst'.rootNode :: suf).Nodup ∧
                                  (∀ r ∈ pre ++ vst'.rootNode :: suf, r.toNat < a'.nextId) ∧
                                  VStateValid (f' + 1) childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ a'
                                    (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) vst' ∧
                                  DomTreeAssocEquiv (readDomTree (f' + 1) a' vst'.rootNode)
                                    (specDom childNs (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂)))
                              rw [hmonadEq]
                              let aClr := a1.set node (.element realNs tag st' mg' [])
                              have hclr : MonadDom.clearChildren (m := StateM (DomArena msg)) node a1 = ((), aClr) := by
                                dsimp only [MonadDom.clearChildren, DomArena.modifyChildren, DomArena.modify, aClr]; rw [ha1Get]
                              rw [hclr]; dsimp only
                              have haClrN : aClr.nextId = a.nextId := ha1N
                              have haClrNode : aClr.get node = .element realNs tag st' mg' [] := DomArena.get_set_self _ _ _
                              have haClrOut : ∀ m, m ≠ node → aClr.get m = a.get m := fun m hm => (DomArena.get_set_ne _ _ hm).trans (ha1Out m hm)
                              let frag := UInt32.ofNat aClr.nextId
                              let aFragBase : DomArena msg := { aClr with nextId := aClr.nextId + 1 }
                              have hfragToNat : frag.toNat = a.nextId := by
                                dsimp only [frag]; rw [haClrN]
                                simp only [View.render, htmlNodeCount] at hbound; exact uint32_toNat_ofNat_lt_vp a.nextId (by omega)
                              have hfragNeNode : frag ≠ node := node_ne_of_toNat_ne (by rw [hfragToNat]; omega)
                              have hfragRun : aClr.alloc (ArenaEntry.fragment []) = (frag, aFragBase.set frag (.fragment [])) := rfl
                              simp only [View.render, htmlNodeCount] at hbound; simp only [View.render, htmlDepth] at hdep
                              have hbuilt := CleanDomChildren_of_buildDomListM (Dom.childNsOf childNs tag) (rowsHtml s₂) [] aFragBase frag
                                ArenaEntry.fragment (.inr fun _ => rfl) [] f' (fun _ => False) (hrowsClean.2.1 s₂)
                                (by change frag.toNat < aClr.nextId + 1; rw [hfragToNat, haClrN]; omega)
                                (by change 0 < aClr.nextId + 1; omega)
                                (by change aClr.nextId + 1 + htmlListNodeCount (rowsHtml s₂) < UInt32.size; rw [haClrN]; omega)
                                (by omega) (fun _ h => h.elim) trivial
                              dsimp only [StateT.run] at hbuilt
                              rcases hbuilt with ⟨csNew, aBase', haBuiltEq, haBuiltGe, haBuiltBound, haBuiltFr, hCleanOut⟩
                              simp only [List.nil_append, false_or] at haBuiltEq hCleanOut
                              let aBuilt := (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf childNs tag) frag (rowsHtml s₂) (aFragBase.set frag (.fragment []))).2
                              have haBuiltEq' : aBuilt = aBase'.set frag (.fragment csNew) := haBuiltEq
                              have haBuiltNext : a.nextId + 1 ≤ aBuilt.nextId := by
                                change aFragBase.nextId ≤ aBuilt.nextId at haBuiltGe; change aClr.nextId + 1 ≤ aBuilt.nextId at haBuiltGe; rw [← haClrN]; exact haBuiltGe
                              have haBuiltBd' : aBuilt.nextId ≤ a.nextId + (1 + htmlListNodeCount (rowsHtml s₂)) := by
                                change aBuilt.nextId ≤ aFragBase.nextId + htmlListNodeCount (rowsHtml s₂) at haBuiltBound
                                change aBuilt.nextId ≤ aClr.nextId + 1 + htmlListNodeCount (rowsHtml s₂) at haBuiltBound
                                rw [← haClrN]; omega
                              have haBuiltFrag : aBuilt.get frag = .fragment csNew := by rw [haBuiltEq', DomArena.get_set_self]
                              have haBuiltNode : aBuilt.get node = .element realNs tag st' mg' [] := by
                                rw [haBuiltFr node (by change node.toNat < aClr.nextId + 1; rw [haClrN]; omega) hfragNeNode.symm]
                                exact haClrNode
                              let aOut := (aBuilt.set frag .null).set node (.element realNs tag st' mg' csNew)
                              have happendRun : MonadDom.appendChild (m := StateM (DomArena msg)) node frag aBuilt = ((), aOut) := by
                                simp [MonadDom.appendChild, haBuiltFrag, DomArena.modifyChildren, DomArena.modify, DomArena.get_set_ne _ _ hfragNeNode.symm, haBuiltNode, aOut]
                              rw [hfragRun]; dsimp only
                              cases hblR : buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf childNs tag) frag (rowsHtml s₂) (aFragBase.set frag (.fragment [])) with
                              | mk _ aB =>
                                  have hEqB : aB = aBuilt := by dsimp only [aBuilt]; rw [hblR]
                                  subst hEqB; dsimp only; rw [happendRun]; dsimp only
                                  have haOutNext : aOut.nextId = aBuilt.nextId := rfl
                                  have haOutFr : ∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aOut.get m = a.get m := fun m hmn hmLt => by
                                    have hmf : m ≠ frag := node_ne_of_toNat_ne (by rw [hfragToNat]; omega)
                                    dsimp only [aOut]
                                    rw [DomArena.get_set_ne _ _ hmn, DomArena.get_set_ne _ _ hmf,
                                      haBuiltFr m (by change m.toNat < aClr.nextId + 1; rw [haClrN]; omega) hmf]
                                    exact haClrOut m hmn
                                  have hparOut' : aOut.get parent = .element pns ptag pst pmg (pre ++ node :: suf) := by
                                    rw [haOutFr parent hne.symm hparLt, hpar]
                                  have hCleanOut' : CleanDomChildren f' (Dom.childNsOf childNs tag) (rowsHtml s₂) aOut
                                      (fun k => (Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ node.toNat) csNew := by
                                    refine CleanDomChildren_mono (fun k hk => ?_)
                                      (CleanDomChildren_frame (a' := aOut) (fun m hm => ?_) hCleanOut)
                                    · rcases hk with ⟨hk1, hk2⟩
                                      change aClr.nextId + 1 ≤ k at hk1; change k < aBuilt.nextId at hk2; rw [haClrN] at hk1
                                      exact ⟨.inr ⟨by omega, by rw [haOutNext]; exact hk2⟩, by omega⟩
                                    · rcases hm with ⟨hm1, hm2⟩
                                      change aClr.nextId + 1 ≤ m.toNat at hm1; change m.toNat < aBuilt.nextId at hm2; rw [haClrN] at hm1
                                      have hmn : m ≠ node := node_ne_of_toNat_ne (by omega)
                                      have hmf : m ≠ frag := node_ne_of_toNat_ne (by rw [hfragToNat]; omega)
                                      simp only [aOut, DomArena.get_set_ne _ _ hmn, DomArena.get_set_ne _ _ hmf]; rfl
                                  have hvalOut : VStateValid (f' + 1) childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ aOut
                                      (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) (.list node newKeys newSigs (rowsHtml s₂) (marks s₂) inst) :=
                                    ⟨⟨.inl hnodeMem, haClean.1 s₂, haClean.2.1 s₂, st', mg', csNew,
                                      DomArena.get_set_self _ _ _, hElClean', hElEq', hmg', hCleanOut'⟩, rfl, rfl, rfl⟩
                                  refine ⟨by omega, by simp only [View.render, htmlNodeCount]; omega, fun m hmPar hmSold hmLt => ?_,
                                    hparOut', hnd, fun r hr => Nat.lt_of_lt_of_le (hparNodes r hr) (by omega), hvalOut, VStateValid_equiv hvalOut⟩
                                  exact haOutFr m (fun h => hmSold (h ▸ hnodeMem)) hmLt
                            have ⟨hdomNd, hdomLen⟩ := CleanDomChildren_nodup hCleanCs
                            have hdomLtU32 : domCs.length < UInt32.size := by
                              have hle : domCs.length ≤ a.nextId :=
                                nodup_length_le_bound a.nextId domCs hdomNd fun x hx =>
                                  hSoldLt _ (CleanDomChildren_mem hCleanCs x hx).1
                              simp only [View.render, htmlNodeCount] at hbound; omega
                            have hcountEq : MonadDom.childCount (m := StateM (DomArena msg)) node a1 = (UInt32.ofNat domCs.length, a1) := by
                              dsimp only [MonadDom.childCount]; rw [ha1Get]
                            have hcountNat : (UInt32.ofNat domCs.length).toNat = domCs.length := uint32_toNat_ofNat_lt_vp domCs.length hdomLtU32
                            have hsnap := snapshotChildrenM_spec a1 node realNs tag st' mg' domCs hdomLtU32 0 domCs.length #[] (by omega)
                            rw [DomArena.set_get_self a1 ha1Get] at hsnap
                            dsimp only [StateT.run, List.nil_append, List.drop_zero] at hsnap
                            let live : Array Dom.Node := ⟨domCs⟩
                            have hliveSz : live.size = (rowsHtml s₁).length := by simpa [live] using hdomLen
                            have hliveToList : live.toList = domCs := rfl
                            have hremSpec := removeUnusedM_spec node realNs tag st' mg' live used 0 [] a1 (Nat.zero_le _) (by simpa [live] using hdomNd) (by simpa [live] using ha1Get)
                            let aRem := (removeUnusedM (m := StateM (DomArena msg)) node live used 0).run a1 |>.2
                            have haRemEq : removeUnusedM (m := StateM (DomArena msg)) node live used 0 a1 = ((), aRem) := rfl
                            have haRemN : aRem.nextId = a.nextId := hremSpec.1.trans ha1N
                            have haRemOut : ∀ m, m ≠ node → aRem.get m = a.get m := fun m hm => (hremSpec.2.1 m hm).trans (ha1Out m hm)
                            let kept := (List.range live.size).filterMap fun oi => if used.getD oi false then some (live.getD oi 0) else none
                            have haRemNode : aRem.get node = .element realNs tag st' mg' kept := by
                              simpa [kept] using hremSpec.2.2
                            let inLis := verifiedLisFlags sources
                            have hlisSpec := verifiedLisFlags_spec sources
                            have hkeptSpec := lis_filter_kept_eq live sources inLis used (rowsHtml s₂).length hsrcSz
                              (by rw [hplanSpec.2.1, hliveSz, hrowsClean.1 s₁])
                              (fun i hi oi hsi => by rw [hliveSz]; exact hsrcBound i hi oi hsi)
                              hsrcInj
                              (fun oi ho => by
                                have hoK : oi < oldKeys.size := by rw [← hrowsClean.1 s₁, ← hliveSz]; exact ho
                                have hiff := hplanSpec.2.2.2.2.1 oi hoK
                                have hszEq : newKeys.size = (rowsHtml s₂).length := (hrowsClean.1 s₂).symm
                                simpa [hszEq] using hiff)
                              hdomNd
                              (fun i hi hf => hlisSpec.1 i (by rw [hsrcSz]; exact hi) hf)
                              (fun i₁ i₂ h1 h2 hf1 hf2 oi₁ oi₂ hs1 hs2 => hlisSpec.2 i₁ i₂ h1 (by rw [hsrcSz]; exact h2) hf1 hf2 oi₁ oi₂ hs1 hs2)
                            rcases CleanDomChildren_indexed hCleanCs with ⟨Si, hSiSub, hSiDisj, hSiGet⟩
                            have hOldCleanRem : ∀ oi (ho : oi < (rowsHtml s₁).length),
                                CleanDomSubtree f' (Dom.childNsOf childNs tag) (rowsHtml s₁)[oi] aRem (Si oi) (live.getD oi 0) := by
                              intro oi ho
                              have hoD : oi < domCs.length := by rw [hdomLen]; exact ho
                              have hgl : live.getD oi 0 = domCs[oi] := by simp [live, Array.getD, hoD]
                              rw [hgl]
                              exact CleanDomSubtree_frame (fun m hm => haRemOut m (node_ne_of_toNat_ne (hSiSub oi m.toNat hm).2)) (hSiGet oi ho hoD)
                            simp only [View.render, htmlNodeCount] at hbound
                            simp only [View.render, htmlDepth] at hdep
                            have hrec := reconcileLisBackM_spec f' node realNs tag st' mg' (Dom.childNsOf childNs tag)
                              live sources inLis rowsArr (rowsHtml s₂) (rowsHtml s₁) Si Sold a.nextId
                              hsrcSz hrowsArrEq hliveSz hdomNd (hrowsClean.2.1 s₂)
                              hsrcBound hsrcInj hsrcRow hSiSub hSiDisj hSoldLt (by omega)
                              (rowsHtml s₂).length (Nat.le_refl _) false 0 kept [] (fun _ => False) aRem
                              (by omega) (by omega)
                              (by rw [haRemN, List.take_length]; omega)
                              (by rw [haRemN]; exact hnodeLt)
                              haRemNode hkeptSpec.1 rfl rfl
                              (fun x => by rw [hkeptSpec.2.1 x]; simp)
                              hkeptSpec.2.2.1
                              (fun _ _ h => nomatch h)
                              (fun _ _ h => nomatch h)
                              (by rw [List.append_nil]; exact hkeptSpec.2.2.2)
                              hOldCleanRem
                              (fun _ h => h.elim)
                              (fun _ _ _ _ _ _ h => h.elim)
                              (by rw [List.drop_length]; trivial)
                            have hnsEq : MonadDom.childNamespace (m := StateM (DomArena msg)) node a1 = (Dom.childNsOf childNs tag, a1) := by
                              dsimp only [MonadDom.childNamespace]; rw [ha1Get]; dsimp only [realNs]; rw [hccNs]
                            have hnewKeysSzEq : newKeys.size = (rowsHtml s₂).length := (hrowsClean.1 s₂).symm
                            cases hrecRun : reconcileLisBackM (m := StateM (DomArena msg)) node (Dom.childNsOf childNs tag) live sources inLis rowsArr (rowsHtml s₂).length false 0 aRem with
                            | mk _ aOut =>
                                dsimp only [StateT.run] at hrec
                                rw [hrecRun] at hrec; dsimp only at hrec ⊢
                                have hmonadEq : (StateT.bind (seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ newKeys) (rowEv s₂ newKeys) (marks s₂) marksArr sigsArr) fun newSigs =>
                                    StateT.bind (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂) fun _ =>
                                    StateT.bind (MonadDom.childNamespace node) fun cn =>
                                    if (!used.any id) = true then
                                      StateT.bind (MonadDom.clearChildren node) fun _ =>
                                      StateT.bind MonadDom.createFragment fun frag =>
                                      StateT.bind (buildDomListM cn frag rowsArr.toList) fun _ =>
                                      StateT.bind (MonadDom.appendChild node frag) fun _ =>
                                      StateT.pure (VState.list (σ := σ) node newKeys newSigs rowsArr.toList (marks s₂) inst)
                                    else
                                      StateT.bind (MonadDom.childCount node) fun oc =>
                                      StateT.bind (snapshotChildrenM node 0 #[] oc.toNat) fun lv =>
                                      StateT.bind (removeUnusedM node lv used 0) fun _ =>
                                      StateT.bind (reconcileLisBackM node cn lv sources inLis rowsArr newKeys.size false 0) fun _ =>
                                      StateT.pure (VState.list (σ := σ) node newKeys newSigs rowsArr.toList (marks s₂) inst)) a =
                                    (VState.list (σ := σ) node newKeys newSigs rowsArr.toList (marks s₂) inst, aOut) := by
                                  simp only [hnoReuse]
                                  change (match seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ newKeys) (rowEv s₂ newKeys) (marks s₂) marksArr sigsArr a with
                                    | (newSigs, s0) =>
                                      match applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ s0 with
                                      | (_, s1) =>
                                        match MonadDom.childNamespace (m := StateM (DomArena msg)) node s1 with
                                        | (cn, s2) =>
                                          match MonadDom.childCount (m := StateM (DomArena msg)) node s2 with
                                          | (oc, s3) =>
                                            match snapshotChildrenM (m := StateM (DomArena msg)) node 0 #[] oc.toNat s3 with
                                            | (lv, s4) =>
                                              match removeUnusedM (m := StateM (DomArena msg)) node lv used 0 s4 with
                                              | (_, s5) =>
                                                match reconcileLisBackM (m := StateM (DomArena msg)) node cn lv sources inLis rowsArr newKeys.size false 0 s5 with
                                                | (_, s6) => (VState.list (σ := σ) node newKeys newSigs rowsArr.toList (marks s₂) inst, s6)) = _
                                  rw [hsRun]; dsimp only
                                  rw [ha1Eq]; dsimp only
                                  rw [ha1Get]; dsimp only [realNs]
                                  rw [hccNs, hcountNat, hsnap]; dsimp only
                                  rw [haRemEq]; dsimp only
                                  rw [hnewKeysSzEq, hrecRun]
                                change (match (StateT.bind (seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ newKeys) (rowEv s₂ newKeys) (marks s₂) marksArr sigsArr) fun newSigs =>
                                    StateT.bind (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂) fun _ =>
                                    StateT.bind (MonadDom.childNamespace node) fun cn =>
                                    if (!used.any id) = true then
                                      StateT.bind (MonadDom.clearChildren node) fun _ =>
                                      StateT.bind MonadDom.createFragment fun frag =>
                                      StateT.bind (buildDomListM cn frag rowsArr.toList) fun _ =>
                                      StateT.bind (MonadDom.appendChild node frag) fun _ =>
                                      StateT.pure (VState.list (σ := σ) node newKeys newSigs rowsArr.toList (marks s₂) inst)
                                    else
                                      StateT.bind (MonadDom.childCount node) fun oc =>
                                      StateT.bind (snapshotChildrenM node 0 #[] oc.toNat) fun lv =>
                                      StateT.bind (removeUnusedM node lv used 0) fun _ =>
                                      StateT.bind (reconcileLisBackM node cn lv sources inLis rowsArr newKeys.size false 0) fun _ =>
                                      StateT.pure (VState.list (σ := σ) node newKeys newSigs rowsArr.toList (marks s₂) inst)) a with
                                  | (vst', a') =>
                                    a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂) ∧
                                    (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
                                    a'.get parent = .element pns ptag pst pmg (pre ++ vst'.rootNode :: suf) ∧ (pre ++ vst'.rootNode :: suf).Nodup ∧
                                    (∀ r ∈ pre ++ vst'.rootNode :: suf, r.toNat < a'.nextId) ∧
                                    VStateValid (f' + 1) childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ a'
                                      (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) vst' ∧
                                    DomTreeAssocEquiv (readDomTree (f' + 1) a' vst'.rootNode)
                                      (specDom childNs (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂)))
                                rw [hmonadEq]; dsimp only
                                rcases hrec with ⟨haOutGe, haOutBd, haOutFr, finalCs, haOutNode, hCleanOut⟩
                                rw [haRemN] at haOutGe haOutBd haOutFr
                                rw [List.take_length] at haOutBd
                                rw [hrowsArrEq]
                                have hfrAll : ∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aOut.get m = a.get m :=
                                  fun m hmn hmLt => (haOutFr m hmn hmLt).trans (haRemOut m hmn)
                                have hparOut' : aOut.get parent = .element pns ptag pst pmg (pre ++ node :: suf) := by
                                  rw [hfrAll parent hne.symm hparLt, hpar]
                                have hvalOut : VStateValid (f' + 1) childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ aOut
                                    (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) (.list node newKeys newSigs (rowsHtml s₂) (marks s₂) inst) :=
                                  ⟨⟨.inl hnodeMem, haClean.1 s₂, haClean.2.1 s₂, st', mg', finalCs,
                                    haOutNode, hElClean', hElEq', hmg', hCleanOut⟩, rfl, rfl, rfl⟩
                                refine ⟨haOutGe, by simp only [View.render, htmlNodeCount]; omega,
                                  fun m _ hmSold hmLt => hfrAll m (fun h => hmSold (h ▸ hnodeMem)) hmLt,
                                  hparOut', hnd, fun r hr => Nat.lt_of_lt_of_le (hparNodes r hr) haOutGe,
                                  hvalOut, VStateValid_equiv hvalOut⟩
                      · -- `oldRowsL.isEmpty = true`: fast create via DocumentFragment
                        simp only [↓reduceIte]
                        have hnilRows : rowsHtml s₁ = [] := List.isEmpty_iff.1 hemp
                        have hnilDom : domCs = [] := by
                          rw [hnilRows] at hCleanCs
                          cases domCs with | nil => rfl | cons _ _ => exact False.elim hCleanCs
                        subst hnilDom
                        have haSet := DomArena.set_get_self a hnodeGet
                        have hdyn := applyDynAttrsM_spec a node realNs tag st mg [] attrs s₁ s₂ haClean hElClean hElEq hmg
                        rw [haSet] at hdyn
                        rcases hdyn with ⟨ha1Next, ha1Ne, st', mg', ha1Get, hElClean', hElEq', hmg'⟩
                        let a1 := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a).2
                        have ha1Eq : applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a = ((), a1) := rfl
                        have hseed := seedRowsM_sameDom inst (rowSig s₂ (disambiguateKeys (keys s₂))) (rowEv s₂ (disambiguateKeys (keys s₂))) (marks s₂) #[] #[] a1
                        dsimp only [StateT.run] at hseed
                        dsimp only [StateT.bind, StateT.pure, bind, pure]
                        rw [ha1Eq]; dsimp only
                        cases hsRun : seedRowsM (m := StateM (DomArena msg)) inst (rowSig s₂ (disambiguateKeys (keys s₂))) (rowEv s₂ (disambiguateKeys (keys s₂))) (marks s₂) #[] #[] a1 with
                        | mk newSigs aSeed =>
                            rw [hsRun] at hseed; dsimp only at hseed ⊢
                            have haSeedN : aSeed.nextId = a.nextId := hseed.1.trans ha1Next
                            have haSeedNode : aSeed.get node = .element realNs tag st' mg' [] := (hseed.get_eq node).trans ha1Get
                            have haSeedOut : ∀ m, m ≠ node → aSeed.get m = a.get m := fun m hm => (hseed.get_eq m).trans (ha1Ne m hm)
                            have hpref : (rowsHtml s₂).map (Html.prefixSignals inst) = rowsHtml s₂ :=
                              Html.map_prefixSignals_of_DomCleanList inst (hrowsClean.2.1 s₂)
                            rw [hpref]
                            have hcnV : childNs = "" ∨ childNs = Dom.svgNs := by rw [hchildNs]; split <;> simp
                            have hccNs := childNamespace_eq_childNsOf (ptag := tag) hcnV
                            let frag := UInt32.ofNat aSeed.nextId
                            let aFragBase : DomArena msg := { aSeed with nextId := aSeed.nextId + 1 }
                            have hfragToNat : frag.toNat = a.nextId := by
                              dsimp only [frag]; rw [haSeedN]
                              simp only [View.render, htmlNodeCount] at hbound; exact uint32_toNat_ofNat_lt_vp a.nextId (by omega)
                            have hfragNeNode : frag ≠ node := node_ne_of_toNat_ne (by rw [hfragToNat]; omega)
                            have hfragRun : aSeed.alloc (ArenaEntry.fragment []) = (frag, aFragBase.set frag (.fragment [])) := rfl
                            simp only [View.render, htmlNodeCount] at hbound; simp only [View.render, htmlDepth] at hdep
                            have hbuilt := CleanDomChildren_of_buildDomListM (Dom.childNsOf childNs tag) (rowsHtml s₂) [] aFragBase frag
                              ArenaEntry.fragment (.inr fun _ => rfl) [] f' (fun _ => False) (hrowsClean.2.1 s₂)
                              (by change frag.toNat < aSeed.nextId + 1; rw [hfragToNat, haSeedN]; omega)
                              (by change 0 < aSeed.nextId + 1; omega)
                              (by change aSeed.nextId + 1 + htmlListNodeCount (rowsHtml s₂) < UInt32.size; rw [haSeedN]; omega)
                              (by omega) (fun _ h => h.elim) trivial
                            dsimp only [StateT.run] at hbuilt
                            rcases hbuilt with ⟨csNew, aBase', haBuiltEq, haBuiltGe, haBuiltBound, haBuiltFr, hCleanOut⟩
                            simp only [List.nil_append, false_or] at haBuiltEq hCleanOut
                            let aBuilt := (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf childNs tag) frag (rowsHtml s₂) (aFragBase.set frag (.fragment []))).2
                            have haBuiltEq' : aBuilt = aBase'.set frag (.fragment csNew) := haBuiltEq
                            have haBuiltNext : a.nextId + 1 ≤ aBuilt.nextId := by
                              change aFragBase.nextId ≤ aBuilt.nextId at haBuiltGe; change aSeed.nextId + 1 ≤ aBuilt.nextId at haBuiltGe; rw [← haSeedN]; exact haBuiltGe
                            have haBuiltBd' : aBuilt.nextId ≤ a.nextId + (1 + htmlListNodeCount (rowsHtml s₂)) := by
                              change aBuilt.nextId ≤ aFragBase.nextId + htmlListNodeCount (rowsHtml s₂) at haBuiltBound
                              change aBuilt.nextId ≤ aSeed.nextId + 1 + htmlListNodeCount (rowsHtml s₂) at haBuiltBound
                              rw [← haSeedN]; omega
                            have haBuiltFrag : aBuilt.get frag = .fragment csNew := by rw [haBuiltEq', DomArena.get_set_self]
                            have haBuiltNode : aBuilt.get node = .element realNs tag st' mg' [] := by
                              rw [haBuiltFr node (by change node.toNat < aSeed.nextId + 1; rw [haSeedN]; omega) hfragNeNode.symm]
                              exact haSeedNode
                            let aOut := (aBuilt.set frag .null).set node (.element realNs tag st' mg' csNew)
                            have happendRun : MonadDom.appendChild (m := StateM (DomArena msg)) node frag aBuilt = ((), aOut) := by
                              simp [MonadDom.appendChild, haBuiltFrag, DomArena.modifyChildren, DomArena.modify, DomArena.get_set_ne _ _ hfragNeNode.symm, haBuiltNode, aOut]
                            rw [haSeedNode]; dsimp only [realNs]; rw [hccNs, hfragRun]; dsimp only
                            cases hblR : buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf childNs tag) frag (rowsHtml s₂) (aFragBase.set frag (.fragment [])) with
                            | mk _ aB =>
                                have hEqB : aB = aBuilt := by dsimp only [aBuilt]; rw [hblR]
                                subst hEqB; dsimp only; rw [happendRun]; dsimp only
                                have haOutNext : aOut.nextId = aBuilt.nextId := rfl
                                have haOutFr : ∀ m : Dom.Node, m ≠ node → m.toNat < a.nextId → aOut.get m = a.get m := fun m hmn hmLt => by
                                  have hmf : m ≠ frag := node_ne_of_toNat_ne (by rw [hfragToNat]; omega)
                                  dsimp only [aOut]
                                  rw [DomArena.get_set_ne _ _ hmn, DomArena.get_set_ne _ _ hmf,
                                    haBuiltFr m (by change m.toNat < aSeed.nextId + 1; rw [haSeedN]; omega) hmf]
                                  exact haSeedOut m hmn
                                have hparOut' : aOut.get parent = .element pns ptag pst pmg (pre ++ node :: suf) := by
                                  rw [haOutFr parent hne.symm hparLt, hpar]
                                have hCleanOut' : CleanDomChildren f' (Dom.childNsOf childNs tag) (rowsHtml s₂) aOut
                                    (fun k => (Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ node.toNat) csNew := by
                                  refine CleanDomChildren_mono (fun k hk => ?_)
                                    (CleanDomChildren_frame (a' := aOut) (fun m hm => ?_) hCleanOut)
                                  · rcases hk with ⟨hk1, hk2⟩
                                    change aSeed.nextId + 1 ≤ k at hk1; change k < aBuilt.nextId at hk2; rw [haSeedN] at hk1
                                    exact ⟨.inr ⟨by omega, by rw [haOutNext]; exact hk2⟩, by omega⟩
                                  · rcases hm with ⟨hm1, hm2⟩
                                    change aSeed.nextId + 1 ≤ m.toNat at hm1; change m.toNat < aBuilt.nextId at hm2; rw [haSeedN] at hm1
                                    have hmn : m ≠ node := node_ne_of_toNat_ne (by omega)
                                    have hmf : m ≠ frag := node_ne_of_toNat_ne (by rw [hfragToNat]; omega)
                                    simp only [aOut, DomArena.get_set_ne _ _ hmn, DomArena.get_set_ne _ _ hmf]; rfl
                                have hvalOut : VStateValid (f' + 1) childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ aOut
                                    (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) (.list node (disambiguateKeys (keys s₂)) newSigs (rowsHtml s₂) (marks s₂) inst) :=
                                  ⟨⟨.inl hnodeMem, haClean.1 s₂, haClean.2.1 s₂, st', mg', csNew,
                                    DomArena.get_set_self _ _ _, hElClean', hElEq', hmg', hCleanOut'⟩, rfl, rfl, rfl⟩
                                refine ⟨by omega, by simp only [View.render, htmlNodeCount]; omega, fun m hmPar hmSold hmLt => ?_,
                                  hparOut', hnd, fun r hr => Nat.lt_of_lt_of_le (hparNodes r hr) (by omega), hvalOut, VStateValid_equiv hvalOut⟩
                                exact haOutFr m (fun h => hmSold (h ▸ hnodeMem)) hmLt
                    · -- `newKeys.isEmpty = true`: fast `clearChildren`
                      simp only [↓reduceIte, StateT.bind, StateT.pure]
                      have hnewSz0 : (disambiguateKeys (keys s₂)).size = 0 := Array.isEmpty_iff.1 hnewEmp |> fun h => by rw [h]; rfl
                      have hnewKeysEq : disambiguateKeys (keys s₂) = #[] := Array.isEmpty_iff.1 hnewEmp
                      have hnewRows0 : rowsHtml s₂ = [] := List.eq_nil_of_length_eq_zero (by rw [hrowsClean.1 s₂, hnewSz0])
                      have haSet := DomArena.set_get_self a hnodeGet
                      have hdyn := applyDynAttrsM_spec a node realNs tag st mg domCs attrs s₁ s₂ haClean hElClean hElEq hmg
                      rw [haSet] at hdyn
                      rcases hdyn with ⟨ha1Next, ha1Ne, st', mg', ha1Get, hElClean', hElEq', hmg'⟩
                      let a1 := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a).2
                      have ha1Eq : applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a = ((), a1) := rfl
                      rw [ha1Eq]; dsimp only
                      let aOut := a1.set node (.element realNs tag st' mg' [])
                      have hclr : MonadDom.clearChildren (m := StateM (DomArena msg)) node a1 = ((), aOut) := by
                        dsimp only [MonadDom.clearChildren, DomArena.modifyChildren, DomArena.modify, aOut]; rw [ha1Get]
                      rw [hclr]; dsimp only
                      have haOutNext : aOut.nextId = a.nextId := ha1Next
                      have haOutOutside : ∀ m, m ≠ node → aOut.get m = a.get m := fun m hm =>
                        (DomArena.get_set_ne _ _ hm).trans (ha1Ne m hm)
                      have hparOut' : aOut.get parent = .element pns ptag pst pmg (pre ++ node :: suf) := by
                        rw [haOutOutside parent hne.symm, hpar]
                      have hvalOut : VStateValid (f' + 1) childNs (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s₂ aOut
                          (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) (.list node #[] #[] [] #[] inst) :=
                        ⟨⟨.inl hnodeMem, haClean.1 s₂, haClean.2.1 s₂, st', mg', [],
                          DomArena.get_set_self _ _ _, hElClean', hElEq', hmg', by rw [hnewRows0]; trivial⟩,
                         rfl, hnewKeysEq.symm, hnewRows0.symm⟩
                      refine ⟨by omega, by simp only [View.render, htmlNodeCount]; omega, fun m hmPar hmOut hmLt => ?_, hparOut', hnd,
                        fun r hr => Nat.lt_of_lt_of_le (hparNodes r hr) (by omega), hvalOut, VStateValid_equiv hvalOut⟩
                      exact haOutOutside m (fun h => hmOut (h ▸ hnodeMem))
        | _ => exact False.elim hval.2
    | text _ =>
        cases vst <;> try exact False.elim hval.2
        dsimp only [patchViewM, StateT.run, pure, StateT.pure]
        exact ⟨Nat.le_refl _, by simp [View.render, htmlNodeCount], fun _ _ _ _ => rfl, hpar, hnd, hparNodes,
          VStateValid_mono (fun _ => .inl) hval, CleanDomSubtree_equiv hval.1⟩
    | static _ =>
        cases vst <;> try exact False.elim hval.2
        dsimp only [patchViewM, StateT.run, pure, StateT.pure]
        exact ⟨Nat.le_refl _, by omega, fun _ _ _ _ => rfl, hpar, hnd, hparNodes,
          VStateValid_mono (fun _ => .inl) hval, CleanDomSubtree_equiv hval.1⟩
    | dyn get =>
        cases vst with
        | dyn node _ =>
            rcases hval with ⟨hcl, _, rfl⟩
            cases f with
            | zero => simp [CleanDomSubtree] at hcl
            | succ f' =>
                rcases hcl with ⟨hmem, hget⟩
                dsimp only [VState.rootNode] at hmem hget
                have hne : node ≠ parent := fun h => hparOut (h ▸ hmem)
                by_cases heq : get s₂ = get s₁
                · dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
                  simp only [show (get s₂ != get s₁) = false by simp [heq], Bool.false_eq_true, ↓reduceIte]
                  have hval' : VStateValid (f' + 1) childNs (.dyn get) s₂ a (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a.nextId)) (.dyn node (get s₂)) :=
                    ⟨⟨.inl hmem, by simpa [View.render, heq] using hget⟩, rfl, rfl⟩
                  exact ⟨Nat.le_refl _, by simp [View.render, htmlNodeCount], fun _ _ _ _ => rfl, hpar, hnd, hparNodes, hval', VStateValid_equiv hval'⟩
                · dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
                  simp only [show (get s₂ != get s₁) = true by simp [heq], ↓reduceIte, StateT.bind, pure, StateT.pure]
                  dsimp only [MonadDom.setText, DomArena.modify]; rw [hget]; dsimp only
                  let a' := a.set node (.text (get s₂))
                  have hval' : VStateValid (f' + 1) childNs (.dyn get) s₂ a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) (.dyn node (get s₂)) :=
                    ⟨⟨.inl hmem, DomArena.get_set_self _ _ _⟩, rfl, rfl⟩
                  refine ⟨Nat.le_refl _, by simp [View.render, htmlNodeCount], fun m _ hmOut _ =>
                    DomArena.get_set_ne _ _ (fun hEq => hmOut (hEq ▸ hmem)),
                    by rw [DomArena.get_set_ne _ _ hne.symm]; simpa [VState.rootNode] using hpar,
                    hnd, hparNodes, hval', VStateValid_equiv hval'⟩
        | _ => exact False.elim hval.2
    | dynNode get =>
        cases vst with
        | dynNode node _ =>
            rcases hval with ⟨hcl, _, rfl⟩
            have hp := patchHtmlSubtreeM_spec f childNs parent pns ptag pst pmg (get s₁) (get s₂) node pre suf Sold a
              hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hcl (hclean s₂)
            dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure] at hp ⊢
            cases hsp : patchHtmlSubtreeM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (get s₁) (get s₂) a with
            | mk n' a' =>
                rw [hsp] at hp; dsimp only at hp; rcases hp with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
                exact ⟨h1, h2, h3, h4, h5, h6, ⟨h7, rfl, rfl⟩, h8⟩
        | _ => exact False.elim hval.2
    | memo sm =>
        cases vst with
        | memo node lastKey lastHtml =>
            rcases hval with ⟨hcl, _, rfl, rfl⟩
            dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
            by_cases hkey : sm.keyOf s₂ = sm.keyOf s₁
            · have hb : (sm.keyOf s₂ == sm.keyOf s₁) = true := beq_iff_eq.2 hkey
              have heval : sm.eval s₂ = sm.eval s₁ := sm.sound s₂ s₁ hkey
              simp only [hb, ↓reduceIte]
              have hval' : VStateValid f childNs (.memo sm) s₂ a (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a.nextId)) (.memo node (sm.keyOf s₁) (sm.eval s₁)) :=
                ⟨by simpa [View.render, heval] using CleanDomSubtree_mono (fun _ => .inl) hcl, rfl, hkey.symm, heval.symm⟩
              exact ⟨Nat.le_refl _, by omega, fun _ _ _ _ => rfl, hpar, hnd, hparNodes, hval', VStateValid_equiv hval'⟩
            · simp only [show (sm.keyOf s₂ == sm.keyOf s₁) = false by exact beq_eq_false_iff_ne.2 hkey, Bool.false_eq_true, ↓reduceIte, StateT.bind, pure, StateT.pure]
              have hp := patchHtmlSubtreeM_spec f childNs parent pns ptag pst pmg (sm.eval s₁) (sm.eval s₂) node pre suf Sold a
                hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hcl (hclean s₂)
              dsimp only [StateT.run] at hp
              cases hsp : patchHtmlSubtreeM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) node (sm.eval s₁) (sm.eval s₂) a with
              | mk n' a' =>
                  rw [hsp] at hp; dsimp only at hp; rcases hp with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
                  exact ⟨h1, h2, h3, h4, h5, h6, ⟨h7, rfl, rfl, rfl⟩, h8⟩
        | _ => exact False.elim hval.2
    | ifElse cond yes no =>
        cases vst with
        | cond wasYes inner =>
            rcases hval with ⟨hcl, ⟨hwy, hin⟩⟩
            dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
            by_cases hsame : cond s₂ = wasYes
            · simp only [beq_iff_eq.2 hsame, ↓reduceIte]
              cases hc₂ : cond s₂
              · simp only [View.render, hc₂, Bool.false_eq_true, ↓reduceIte] at hbound hdep ⊢
                dsimp only [StateT.bind, pure, StateT.pure]
                have hF : cond s₁ = false := by rw [← hwy, ← hsame, hc₂]
                have hvalBranch : VStateValid f childNs no s₁ a Sold inner := ⟨by simpa [View.render, hF] using hcl, by simpa [hF] using hin⟩
                have hih := patchViewM_spec f childNs parent pns ptag pst pmg no s₁ s₂ pre suf Sold a inner
                  hchildNs hclean.2 hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hvalBranch
                dsimp only [StateT.run] at hih
                cases hp : patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) no s₂ inner a with
                | mk inner' a' =>
                    rw [hp] at hih; dsimp only at hih; rcases hih with ⟨h1, h2, h3, h4, h5, h6, ⟨hcl', hm'⟩, heqv'⟩
                    exact ⟨h1, h2, h3, h4, h5, h6, ⟨by simpa [View.render, hc₂] using hcl', hc₂.symm, by simpa [hc₂] using hm'⟩,
                      by simpa [View.render, hc₂] using heqv'⟩
              · simp only [View.render, hc₂, ↓reduceIte] at hbound hdep ⊢
                dsimp only [StateT.bind, pure, StateT.pure]
                have hT : cond s₁ = true := by rw [← hwy, ← hsame, hc₂]
                have hvalBranch : VStateValid f childNs yes s₁ a Sold inner := ⟨by simpa [View.render, hT] using hcl, by simpa [hT] using hin⟩
                have hih := patchViewM_spec f childNs parent pns ptag pst pmg yes s₁ s₂ pre suf Sold a inner
                  hchildNs hclean.1 hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hvalBranch
                dsimp only [StateT.run] at hih
                cases hp : patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) yes s₂ inner a with
                | mk inner' a' =>
                    rw [hp] at hih; dsimp only at hih; rcases hih with ⟨h1, h2, h3, h4, h5, h6, ⟨hcl', hm'⟩, heqv'⟩
                    exact ⟨h1, h2, h3, h4, h5, h6, ⟨by simpa [View.render, hc₂] using hcl', hc₂.symm, by simpa [hc₂] using hm'⟩,
                      by simpa [View.render, hc₂] using heqv'⟩
            · simp only [beq_eq_false_iff_ne.2 hsame, Bool.false_eq_true, ↓reduceIte, StateT.bind]
              have hnsRun : MonadDom.childNamespace (m := StateM (DomArena msg)) parent a = (childNs, a) := by
                simp [MonadDom.childNamespace, hpar, hchildNs]
              have huJ : (UInt32.ofNat pre.length).toNat = pre.length := uint32_toNat_ofNat_lt_vp pre.length (by omega)
              rw [hnsRun]; dsimp only [Bind.bind]
              let targetV := if cond s₂ then yes else no
              have htargetClean : View.DomClean targetV := by cases hc₂ : cond s₂ <;> simp [targetV, hc₂, hclean.1, hclean.2]
              have hbuild := buildViewM_vstate_spec childNs targetV s₂ a f htargetClean hpos
                (by cases hc₂ : cond s₂ <;> simpa [targetV, View.render, hc₂] using hbound)
                (by cases hc₂ : cond s₂ <;> simpa [targetV, View.render, hc₂] using hdep)
              dsimp only [StateT.run] at hbuild
              cases hB : buildViewM (m := StateM (DomArena msg)) childNs (if cond s₂ then yes else no) s₂ a with
              | mk pair aMid =>
                  rcases pair with ⟨n2, newInner⟩
                  rw [hB] at hbuild; dsimp only at hbuild
                  rcases hbuild with ⟨hn2Root, haMidGe, haMidBound, haMidFr, hVstMid, _⟩
                  have hparMid : aMid.get parent = .element pns ptag pst pmg (pre ++ inner.rootNode :: suf) := by
                    rw [haMidFr parent hparLt]; exact hpar
                  let a' := aMid.set parent (.element pns ptag pst pmg (pre ++ n2 :: suf))
                  have hgoalRun : (if cond s₂ = true then
                      StateT.bind (buildViewM (m := StateM (DomArena msg)) childNs yes s₂) fun y =>
                        StateT.bind (MonadDom.replaceChild parent (UInt32.ofNat pre.length) y.fst) fun _ =>
                          StateT.pure (VState.cond (cond s₂) y.snd)
                    else
                      StateT.bind (buildViewM (m := StateM (DomArena msg)) childNs no s₂) fun y =>
                        StateT.bind (MonadDom.replaceChild parent (UInt32.ofNat pre.length) y.fst) fun _ =>
                          StateT.pure (VState.cond (cond s₂) y.snd)) a = (VState.cond (cond s₂) newInner, a') := by
                    cases hc₂ : cond s₂ <;>
                      simp only [hc₂, Bool.false_eq_true, ↓reduceIte, StateT.bind, StateT.pure, Bind.bind] at hB ⊢ <;>
                      rw [hB] <;>
                      simp [DomArena.modifyChildren, DomArena.modify, hparMid, huJ,
                        listReplaceAt_append_middle, pure, a']
                  rw [hgoalRun]; dsimp only
                  have hn2Ge : a.nextId ≤ n2.toNat := by have hrm := VStateValid_root_mem hVstMid; rw [hn2Root] at hrm; exact hrm.1
                  have hn2NotIn : n2 ∉ pre ++ inner.rootNode :: suf := fun hm => by have := hparNodes n2 hm; omega
                  have hVst' : VStateValid f childNs targetV s₂ a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) newInner :=
                    VStateValid_mono (fun _ => .inr) (VStateValid_frame (fun m _ => DomArena.get_set_ne _ _ (fun hEq => by subst hEq; omega)) hVstMid)
                  have hVstIf : VStateValid f childNs (.ifElse cond yes no) s₂ a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) (.cond (cond s₂) newInner) := by
                    refine ⟨?_, rfl, ?_⟩
                    · cases hc₂ : cond s₂ <;> simpa [VState.rootNode, View.render, hc₂, targetV] using hVst'.1
                    · cases hc₂ : cond s₂ <;> simpa [VState.rootNode, hc₂, targetV] using hVst'.2
                  refine ⟨haMidGe, by cases hc₂ : cond s₂ <;> simpa [targetV, View.render, hc₂] using haMidBound,
                    fun m hmPar _ hmLt => by rw [DomArena.get_set_ne _ _ hmPar, haMidFr m hmLt],
                    (by simp only [VState.rootNode, hn2Root]; exact DomArena.get_set_self _ _ _),
                    (by simpa [VState.rootNode, hn2Root] using nodup_append_replace hnd (.inr hn2NotIn)),
                    fun r hr => ?_, hVstIf, VStateValid_equiv hVstIf⟩
                  rcases List.mem_append.1 hr with hp | hc
                  · exact Nat.lt_of_lt_of_le (hparNodes r (List.mem_append_left _ hp)) haMidGe
                  · rcases List.mem_cons.1 hc with rfl | _
                    · exact (VStateValid_root_mem hVstMid).2
                    · exact Nat.lt_of_lt_of_le (hparNodes r (List.mem_append_right _ (.tail _ ‹_›))) haMidGe
        | _ => exact False.elim hval.2
    | element tag attrs kids =>
        cases vst with
        | elem node kstates =>
            dsimp only [VStateValid, VState.rootNode] at hpar hnd hparNodes hval
            rcases hval with ⟨hcl, _, ns', tag', st, mg, domCs, hgetM, hksM⟩
            cases f with
            | zero => simp [CleanDomSubtree] at hcl
            | succ f' =>
                rcases hcl with ⟨hnodeMem, _, _, st0, mg0, domCs0, hnodeGet, hElClean, hElEq, hmg, hCleanCs⟩
                rw [hgetM] at hnodeGet; cases hnodeGet
                have hne : node ≠ parent := fun h => hparOut (h ▸ hnodeMem)
                have hnodeLt : node.toNat < a.nextId := hSoldLt _ hnodeMem
                have haSet := DomArena.set_get_self a hgetM
                have hdyn := applyDynAttrsM_spec a node (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st mg domCs attrs s₁ s₂ hclean.1 hElClean hElEq hmg
                rw [haSet] at hdyn
                rcases hdyn with ⟨ha1Next, ha1Ne, st', mg', ha1Get, hElClean', hElEq', hmg'⟩
                let a1 := (applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a).2
                have ha1N : a1.nextId = a.nextId := ha1Next
                have hCleanCs1 := CleanDomChildren_frame (fun m hm => ha1Ne m (node_ne_of_toNat_ne hm.2)) hCleanCs
                have hksM1 := VStateKidsMatches_frame (fun m hm => ha1Ne m (node_ne_of_toNat_ne hm.2)) hCleanCs hksM
                have hndCs := CleanDomChildren_nodup hCleanCs
                have hChildNodes : ∀ r ∈ domCs, r.toNat < a1.nextId ∧ r ≠ node := fun r hr =>
                  have hb := CleanDomChildren_mem hCleanCs r hr
                  ⟨by rw [ha1N]; exact hSoldLt _ hb.1, node_ne_of_toNat_ne hb.2⟩
                simp only [View.render, htmlNodeCount] at hbound; simp only [View.render, htmlDepth] at hdep
                have hpar1 : a1.get parent = .element pns ptag pst pmg (pre ++ node :: suf) := by
                  rw [ha1Ne parent hne.symm, hpar]
                have hcnV : childNs = "" ∨ childNs = Dom.svgNs := by rw [hchildNs]; split <;> simp
                have hccNs := childNamespace_eq_childNsOf (ptag := tag) hcnV
                have hkids := patchViewKidsM_spec f' (Dom.childNsOf childNs tag) node (if childNs == "" && tag == "svg" then Dom.svgNs else childNs) tag st' mg'
                  kids [] [] domCs kstates s₁ s₂ (fun _ => False) (fun k => Sold k ∧ k ≠ node.toNat) a1
                  hccNs.symm hclean.2 (by omega) (by omega) (by omega) (by omega) ha1Get hndCs.1
                  (fun _ h => h.elim) trivial (fun k hk => ⟨hk.2, by rw [ha1N]; exact hSoldLt k hk.1⟩)
                  (fun _ h => h.elim) hChildNodes hCleanCs1 hksM1
                dsimp only [StateT.run] at hkids
                dsimp only [patchViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
                have ha1Eq : applyDynAttrsM (m := StateM (DomArena msg)) node attrs s₂ a = ((), a1) := rfl
                rw [ha1Eq]; dsimp only
                cases hkRun : patchViewKidsM (m := StateM (DomArena msg)) node 0 kids s₂ kstates a1 with
                | mk ks' aOut =>
                    rw [show (UInt32.ofNat ([] : List Dom.Node).length) = 0 from rfl] at hkids
                    rw [hkRun] at hkids; dsimp only at hkids
                    rcases hkids with ⟨Snew, haOutGe, haOutBound, hnodeOut, _, hfrOut, hSnew, hCleanOut, hVstOut⟩
                    have hparOut' : aOut.get parent = .element pns ptag pst pmg (pre ++ node :: suf) := by
                      rw [hfrOut parent hne.symm (fun h => hparOut h.1) (by omega), hpar1]
                    have hvalOut : VStateValid (f' + 1) childNs (.element tag attrs kids) s₂ aOut
                        (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) (.elem node ks') :=
                      ⟨⟨.inl hnodeMem, hclean.1.1 s₂, hclean.1.2.1 s₂, st', mg', ks'.map VState.rootNode,
                        hnodeOut, hElClean', hElEq', hmg',
                        CleanDomChildren_mono (fun k hk => ⟨(hSnew k hk).1.elim (fun h => h.elim) (fun h => h.elim (fun hs => .inl hs.1) (fun ha => .inr ⟨by omega, ha.2⟩)), (hSnew k hk).2⟩) hCleanOut⟩,
                       rfl, _, tag, st', mg', ks'.map VState.rootNode, hnodeOut, hVstOut⟩
                    refine ⟨by omega, by simp only [View.render, htmlNodeCount]; omega, fun m hmPar hmOut hmLt => ?_, hparOut', hnd,
                      fun r hr => Nat.lt_of_lt_of_le (hparNodes r hr) (by omega), hvalOut, VStateValid_equiv hvalOut⟩
                    have hmNeNode : m ≠ node := fun h => hmOut (h ▸ hnodeMem)
                    rw [hfrOut m hmNeNode (fun h => hmOut h.1) (by omega), ha1Ne m hmNeNode]
        | _ => exact False.elim hval.2

  theorem patchViewKidsM_spec {σ msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node)
      (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) :
      ∀ (kids : List (View σ msg)) (targetsDone : List (Html msg)) (preC sufC : List Dom.Node)
        (kstates : List (VState σ msg)) (s₁ s₂ : σ) (Sdone Srem : Nat → Prop) (a : DomArena msg),
        childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") →
        View.DomCleanEach kids → htmlListDepth (View.renderEach kids s₂) ≤ f →
        a.nextId + htmlListNodeCount (View.renderEach kids s₂) < UInt32.size →
        parent.toNat < a.nextId → 0 < a.nextId →
        a.get parent = .element pns ptag pst pmg (preC ++ sufC) → (preC ++ sufC).Nodup →
        (∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId) →
        CleanDomChildren f childNs targetsDone a Sdone preC →
        (∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) → (∀ k, Sdone k → Srem k → False) →
        (∀ r ∈ sufC, r.toNat < a.nextId ∧ r ≠ parent) →
        CleanDomChildren f childNs (View.renderEach kids s₁) a Srem sufC →
        VStateKidsMatches kids s₁ a sufC kstates →
        let (ks', aOut) := (patchViewKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat preC.length) kids s₂ kstates).run a
        ∃ Snew, let domCs' := ks'.map VState.rootNode
          a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount (View.renderEach kids s₂) ∧
          aOut.get parent = .element pns ptag pst pmg (preC ++ domCs') ∧ (preC ++ domCs').Nodup ∧
          (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
          (∀ k, Snew k → (Sdone k ∨ Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧
          CleanDomChildren f childNs (targetsDone ++ View.renderEach kids s₂) aOut Snew (preC ++ domCs') ∧
          VStateKidsMatches kids s₂ aOut domCs' ks'
    | [], _, _, sufC, kstates, _, _, Sdone, _, a, _, _, _, _, _, _, hpar, hnd, hSdone, hDone, _, _, _, hCl, hVk => by
        cases sufC with | cons _ _ => exact False.elim hCl | nil =>
          cases kstates with | cons _ _ => exact False.elim hVk | nil =>
            dsimp only [patchViewKidsM, StateT.run, pure, StateT.pure, View.renderEach, htmlListNodeCount]
            exact ⟨Sdone, Nat.le_refl _, by omega, by simpa using hpar, by simpa using hnd, fun _ _ _ _ => rfl,
              fun k hk => ⟨.inl hk, (hSdone k hk).1⟩, by simpa using hDone, trivial⟩
    | k :: rest, targetsDone, preC, sufC, kstates, s₁, s₂, Sdone, Srem, a,
        hchildNs, ⟨hkCl, hrestCl⟩, hdep, hbound, hparLt, hpos, hpar, hnd, hSdone, hDone, hSrem, hDisj, hsufB, hCl, hVk => by
        cases sufC with | nil => exact False.elim hCl | cons c sufRest =>
          cases kstates with | nil => exact False.elim hVk | cons kst restSt =>
            rcases hCl with ⟨Sc, Srest, hSc, hSr, hDSr, hcCl, hSufCl⟩
            rcases hVk with ⟨rfl, hkMatch, hRestMatch⟩
            simp only [View.renderEach, htmlListDepth] at hdep; simp only [View.renderEach, htmlListNodeCount] at hbound ⊢
            have hkDep : htmlDepth (View.render k s₂) ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
            have hrestDep : htmlListDepth (View.renderEach rest s₂) ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
            have hparNodes : ∀ r ∈ preC ++ kst.rootNode :: sufRest, r.toNat < a.nextId := fun r hr => by
              rcases List.mem_append.1 hr with hp | hc
              · exact (hSdone _ (CleanDomChildren_mem hDone r hp)).2
              · exact (hsufB r hc).1
            have hnodupLe := nodup_nodes_lt_length_le a.nextId (preC ++ kst.rootNode :: sufRest) hnd hparNodes
            have hpreLen : preC.length + 1 + sufRest.length < UInt32.size := by simp only [List.length_append, List.length_cons] at hnodupLe; omega
            have hpatchK := patchViewM_spec f childNs parent pns ptag pst pmg k s₁ s₂ preC sufRest Sc a kst
              hchildNs hkCl hpreLen (by omega) hkDep hparLt hpos hpar hnd (fun h => (hSrem _ (hSc _ h)).1 rfl)
              (fun k hk => (hSrem k (hSc k hk)).2) hparNodes ⟨hcCl, hkMatch⟩
            dsimp only [StateT.run] at hpatchK
            dsimp only [patchViewKidsM, StateT.run, bind, StateT.bind, pure, StateT.pure]
            cases hpK : patchViewM (m := StateM (DomArena msg)) parent (UInt32.ofNat preC.length) k s₂ kst a with
            | mk kst' aMid =>
                rw [hpK] at hpatchK; dsimp only at hpatchK
                rcases hpatchK with ⟨haMidGe, haMidBound, hfrMid, hparMid, hndMid, hparNodesMid, hValK', _⟩
                let Sc' : Nat → Prop := fun x => Sc x ∨ (a.nextId ≤ x ∧ x < aMid.nextId)
                let Sdone' : Nat → Prop := fun x => Sdone x ∨ Sc' x
                have hSdone' : ∀ x, Sdone' x → x ≠ parent.toNat ∧ x < aMid.nextId := fun x hx => hx.elim
                  (fun h1 => have hb := hSdone x h1; ⟨hb.1, by omega⟩)
                  (fun h2 => h2.elim (fun h => have hb := hSrem x (hSc x h); ⟨hb.1, by omega⟩) (fun h3 => ⟨by omega, h3.2⟩))
                have hDoneMid : CleanDomChildren f childNs targetsDone aMid Sdone preC :=
                  CleanDomChildren_frame (fun m hm =>
                    hfrMid m (node_ne_of_toNat_ne (hSdone _ hm).1) (fun hsc => hDisj _ hm (hSc _ hsc)) (hSdone _ hm).2) hDone
                have hDone' := CleanDomChildren_append (fun x h1 h2 =>
                  h2.elim (fun hsc => hDisj x h1 (hSc x hsc)) (fun hlo => by have := (hSdone x h1).2; omega))
                  hDoneMid (show CleanDomChildren f childNs [View.render k s₂] aMid Sc' [kst'.rootNode] from
                    ⟨Sc', fun _ => False, fun _ h => h, fun _ h => h.elim, fun _ _ h => h.elim, hValK'.1, trivial⟩)
                have hSufMid := CleanDomChildren_frame (fun m hm =>
                  hfrMid m (node_ne_of_toNat_ne (hSrem _ (hSr _ hm)).1) (fun hsc => hDSr _ hsc hm) (hSrem _ (hSr _ hm)).2) hSufCl
                have hRestMatchMid := VStateKidsMatches_frame (fun m hm =>
                  hfrMid m (node_ne_of_toNat_ne (hSrem _ (hSr _ hm)).1) (fun hsc => hDSr _ hsc hm) (hSrem _ (hSr _ hm)).2) hSufCl hRestMatch
                have huNext : UInt32.ofNat preC.length + 1 = UInt32.ofNat (preC ++ [kst'.rootNode]).length := by
                  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
                  exact uint32_ofNat_succ preC.length (by omega)
                rw [huNext]
                have hih := patchViewKidsM_spec f childNs parent pns ptag pst pmg rest (targetsDone ++ [View.render k s₂])
                  (preC ++ [kst'.rootNode]) sufRest restSt s₁ s₂ Sdone' Srest aMid hchildNs hrestCl hrestDep
                  (by omega) (by omega) (by omega) (by simpa [List.append_assoc] using hparMid)
                  (by simpa [List.append_assoc] using hndMid) hSdone' (by simpa [View.renderEach_append] using hDone')
                  (fun x hx => have hb := hSrem x (hSr x hx); ⟨hb.1, by omega⟩)
                  (fun x h1 h2 => h1.elim (fun h => hDisj x h (hSr x h2)) (fun h => h.elim (fun hsc => hDSr x hsc h2)
                    (fun _ => by have := (hSrem x (hSr x h2)).2; omega)))
                  (fun r hr => have hb := hsufB r (.tail _ hr); ⟨by omega, hb.2⟩) hSufMid hRestMatchMid
                dsimp only [StateT.run] at hih ⊢
                cases hpR : patchViewKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (preC ++ [kst'.rootNode]).length) rest s₂ restSt aMid with
                | mk restSt' aOut =>
                    rw [hpR] at hih; dsimp only at hih
                    rcases hih with ⟨Snew, haOutGe, haOutBound, hparR, hndR, hfrR, hSnew, hCleanR, hVstR⟩
                    have hValKOut := VStateMatches_frame (fun m hm => by
                      have hnmR : ¬Srest m.toNat := fun hr => hm.elim (fun hs => hDSr _ hs hr)
                        (fun hlo => absurd (hSrem _ (hSr _ hr)).2 (by omega))
                      exact hfrR m (node_ne_of_toNat_ne (hSdone' m.toNat (.inr hm)).1) hnmR (hSdone' m.toNat (.inr hm)).2)
                      hValK'.1 hValK'.2
                    refine ⟨Snew, by omega, by omega, by simpa [List.append_assoc] using hparR, by simpa [List.append_assoc] using hndR,
                      fun m hmPar hmR hmLt => ?_, fun x hx => ?_, by simpa [List.append_assoc, View.renderEach] using hCleanR, rfl, hValKOut, hVstR⟩
                    · rw [hfrR m hmPar (fun hr => hmR (hSr _ hr)) (by omega), hfrMid m hmPar (fun hsc => hmR (hSc _ hsc)) hmLt]
                    · rcases hSnew x hx with ⟨hS | hSr' | hA, hnp⟩
                      · exact ⟨hS.elim .inl (fun h2 => h2.elim (fun hsc => .inr (.inl (hSc _ hsc))) (fun hhi => .inr (.inr ⟨hhi.1, by omega⟩))), hnp⟩
                      · exact ⟨.inr (.inl (hSr _ hSr')), hnp⟩
                      · exact ⟨.inr (.inr ⟨by omega, hA.2⟩), hnp⟩
end

/-! ## 4. Template Keyed Row Alignment, Signal Store & Diff Soundness -/

private theorem collectChanged_eq_append (inst : String) (old new : Array (String × String)) :
    ∀ (j : Nat) (acc : Array (String × String)),
      (collectChanged inst old new j acc).toList = acc.toList ++ (collectChanged inst old new j #[]).toList := by
  intro j
  induction hrem : new.size - j generalizing j with
  | zero =>
      intro acc; have hge : ¬ j < new.size := by omega
      rw [collectChanged.eq_1]; conv => rhs; rw [collectChanged.eq_1]
      simp [hge]
  | succ _ ih =>
      intro acc; by_cases hlt : j < new.size
      · rw [collectChanged.eq_1]; simp only [hlt, ↓reduceDIte]
        conv => rhs; rw [collectChanged.eq_1]; simp only [hlt, ↓reduceDIte]
        have h1 := ih (j + 1) (by omega) (if (old[j]?.map (·.2) == some new[j].2) = true then acc else acc.push (inst ++ new[j].1, new[j].2))
        have h2 := ih (j + 1) (by omega) (if (old[j]?.map (·.2) == some new[j].2) = true then #[] else #[].push (inst ++ new[j].1, new[j].2))
        split at h1 <;> simp_all [List.append_assoc]
      · rw [collectChanged.eq_1]; conv => rhs; rw [collectChanged.eq_1]
        simp [hlt]

private theorem collectChanged_not_mem_lt (inst : String) (old new : Array (String × String))
    (huniq : ∀ a b, a < new.size → b < new.size → new[a]!.1 = new[b]!.1 → a = b) (targetIdx : Nat) (ht : targetIdx < new.size) :
    ∀ (j : Nat), targetIdx < j →
      ∀ kv ∈ (collectChanged inst old new j #[]).toList, kv.1 ≠ inst ++ new[targetIdx]!.1 := by
  intro j
  induction hrem : new.size - j generalizing j with
  | zero =>
      intro _ kv hkv
      have hge : ¬ j < new.size := by omega
      rw [collectChanged.eq_1] at hkv
      simp [hge] at hkv
  | succ _ ih =>
      intro hltIdx kv hkv
      by_cases hlt : j < new.size
      · rw [collectChanged.eq_1] at hkv; simp only [hlt, ↓reduceDIte] at hkv; rw [collectChanged_eq_append] at hkv
        rcases List.mem_append.1 hkv with ha | htl
        · split at ha
          · simp at ha
          · simp only [Array.toList_push, List.nil_append, List.mem_singleton] at ha
            subst ha; intro hEq
            have hkEq : new[j]!.1 = new[targetIdx]!.1 := by
              have hcancel := string_append_left_cancel hEq
              simpa [getElem!_pos new j hlt, getElem!_pos new targetIdx ht] using hcancel
            have := huniq j targetIdx hlt ht hkEq; omega
        · exact ih (j + 1) (by omega) (by omega) kv htl
      · rw [collectChanged.eq_1] at hkv; simp [hlt] at hkv

private theorem foldl_setAssoc_pres {k : String} :
    ∀ (pairs : List (String × String)) (sigs : List (String × String)),
      (∀ kv ∈ pairs, kv.1 ≠ k) → lookupAssoc k (pairs.foldl (fun acc (nm, v) => setAssoc nm v acc) sigs) = lookupAssoc k sigs
  | [], _, _ => rfl
  | (nm, v) :: rest, sigs, h => by
      have hne : (nm == k) = false := beq_eq_false_iff_ne.2 (h (nm, v) (.head _))
      simpa [List.foldl_cons, lookupAssoc_setAssoc, hne] using
        (foldl_setAssoc_pres rest (setAssoc nm v sigs) (fun kv hkv => h kv (.tail _ hkv))).trans (by rw [lookupAssoc_setAssoc, hne]; simp)

theorem collectChanged_lookup_spec {msg : Type} (inst : String) (old new : Array (String × String))
    (huniq : ∀ a b, a < new.size → b < new.size → new[a]!.1 = new[b]!.1 → a = b) (a : DomArena msg)
    (hunch : ∀ k (hk : k < new.size), old[k]?.map (·.2) = some new[k].2 → lookupAssoc (inst ++ new[k].1) a.signals = some new[k].2) :
    let pairs := (collectChanged inst old new 0 #[]).toList
    let a' := ((emitSignalsM (m := StateM (DomArena msg)) pairs).run a).2
    ∀ k (hk : k < new.size), lookupAssoc (inst ++ new[k].1) a'.signals = some new[k].2 := by
  have heq := emitSignalsM_spec (collectChanged inst old new 0 #[]).toList a
  dsimp only; rw [heq]; dsimp only
  have hgen : ∀ (j : Nat) (sigs : List (String × String)), j ≤ new.size →
      (∀ k (hk : k < new.size), k ≥ j → old[k]?.map (·.2) = some new[k].2 → lookupAssoc (inst ++ new[k].1) sigs = some new[k].2) →
      ∀ k (hk : k < new.size), k ≥ j →
        lookupAssoc (inst ++ new[k].1) ((collectChanged inst old new j #[]).toList.foldl (fun acc (nm, v) => setAssoc nm v acc) sigs) = some new[k].2 := by
    intro j; induction hrem : new.size - j generalizing j with
    | zero => intro _ _ _ k hk hge; omega
    | succ _ ih =>
        intro sigs hj hpre k hk hge
        have hlt : j < new.size := by omega
        rw [collectChanged.eq_1]; simp only [hlt, ↓reduceDIte]; rw [collectChanged_eq_append, List.foldl_append]
        by_cases hkj : k = j
        · subst hkj
          have hnoLater := collectChanged_not_mem_lt inst old new huniq k hk (k + 1) (by omega)
          rw [foldl_setAssoc_pres _ _ (fun kv hkv => by simpa [getElem!_pos new k hk] using hnoLater kv hkv)]
          split
          · rename_i hchg
            simp only [List.foldl_nil]
            exact hpre k hk (Nat.le_refl _) (by simpa using hchg)
          · simp [lookupAssoc_setAssoc]
        · apply ih (j + 1) (by omega) _ (by omega) _ k hk (by omega)
          intro k' hk' hk'ge hold'
          split
          · exact hpre k' hk' (by omega) hold'
          · have hne : (inst ++ new[j].1 == inst ++ new[k'].1) = false := beq_eq_false_iff_ne.2 fun hEq => by
              have hcancel := string_append_left_cancel hEq
              have hjk : new[j]!.1 = new[k']!.1 := by
                simpa [getElem!_pos new j hlt, getElem!_pos new k' hk'] using hcancel
              have := huniq j k' hlt hk' hjk; omega
            simp [List.foldl_cons, lookupAssoc_setAssoc, hne, hpre k' hk' (by omega) hold']
  intro k hk; exact hgen 0 a.signals (Nat.zero_le _) (fun k' hk' _ => hunch k' hk') k hk (Nat.zero_le _)

theorem diffRowSigs_sound {msg : Type} (rowSig : Nat → Array (String × String))
    (rowEv : Nat → Array (String × msg)) (inst : String)
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String)))
    (hmark : ∀ i, i < newMarks.size → newMarks[i]! ≠ 0 → oldMarks[i]? = some newMarks[i]! → rowSig i = oldSigs[i]?.getD #[]) :
    ∀ (i : Nat) (accSigs : Array (Array (String × String))) (accEmit : Array (String × String)) (accEv : Array (String × msg)),
      i ≤ newMarks.size → accSigs.size = i → (∀ k, k < i → accSigs[k]! = rowSig k) →
      let (outSigs, _) := diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs i accSigs accEmit accEv
      outSigs.size = newMarks.size ∧ ∀ k, k < newMarks.size → outSigs[k]! = rowSig k := by
  intro i; induction hrem : newMarks.size - i generalizing i with
  | zero =>
      intro accSigs accEmit accEv hiLe hsz hprev; have hge : ¬ i < newMarks.size := by omega
      dsimp only; rw [diffRowSigs.eq_1]; simp only [hge, ↓reduceDIte]; refine ⟨by omega, fun k hk => hprev k (by omega)⟩
  | succ _ ih =>
      intro accSigs accEmit accEv hiLe hsz hprev; have hlt : i < newMarks.size := by omega
      dsimp only; rw [diffRowSigs.eq_1]; simp only [hlt, ↓reduceDIte]
      by_cases hskip : (newMarks[i] != 0 && oldMarks[i]? == some newMarks[i]) = true
      · simp only [hskip, ↓reduceIte]
        have hnz : newMarks[i]! ≠ 0 := by simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hskip; simpa [hlt] using hskip.1
        have hold : oldMarks[i]? = some newMarks[i]! := by simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hskip; simpa [hlt] using hskip.2
        have hsigEq : oldSigs[i]?.getD #[] = rowSig i := (hmark i hlt hnz hold).symm
        apply ih (i + 1) (by omega) (accSigs.push (oldSigs[i]?.getD #[])) accEmit accEv (by omega) (by simp [hsz])
        intro k hk; have hkLtPush : k < (accSigs.push (oldSigs[i]?.getD #[])).size := by simp [hsz]; omega
        by_cases hki : k < i
        · have hkLt : k < accSigs.size := by omega
          rw [getElem!_pos _ k hkLtPush, Array.getElem_push_lt hkLt, ← getElem!_pos accSigs k hkLt]
          exact hprev k hki
        · have heq : k = i := by omega
          subst heq
          have hPushIdx : (accSigs.push (oldSigs[k]?.getD #[]))[k]'hkLtPush = oldSigs[k]?.getD #[] := by
            subst hsz; exact Array.getElem_push_eq
          rw [getElem!_pos _ k hkLtPush, hPushIdx, hsigEq]
      · simp only [hskip, Bool.false_eq_true, ↓reduceIte]
        apply ih (i + 1) (by omega) (accSigs.push (rowSig i)) _ _ (by omega) (by simp [hsz])
        intro k hk; have hkLtPush : k < (accSigs.push (rowSig i)).size := by simp [hsz]; omega
        by_cases hki : k < i
        · have hkLt : k < accSigs.size := by omega
          rw [getElem!_pos _ k hkLtPush, Array.getElem_push_lt hkLt, ← getElem!_pos accSigs k hkLt]
          exact hprev k hki
        · have heq : k = i := by omega
          subst heq
          have hPushIdx : (accSigs.push (rowSig k))[k]'hkLtPush = rowSig k := by
            subst hsz; exact Array.getElem_push_eq
          rw [getElem!_pos _ k hkLtPush, hPushIdx]

theorem seedRowsM_spec {msg : Type} (inst : String) (rowSig : Nat → Array (String × String))
    (rowEv : Nat → Array (String × msg))
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String))) (a : DomArena msg)
    (hmark : ∀ i, i < newMarks.size → newMarks[i]! ≠ 0 → oldMarks[i]? = some newMarks[i]! → rowSig i = oldSigs[i]?.getD #[]) :
    let res := (seedRowsM (m := StateM (DomArena msg)) inst rowSig rowEv newMarks oldMarks oldSigs).run a
    let d := diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs 0 #[] #[] #[]
    res.1.size = newMarks.size ∧ (∀ k, k < newMarks.size → res.1[k]! = rowSig k) ∧
    res.2.nextId = a.nextId ∧ res.2.store = a.store ∧
    res.2.signals = d.2.1.toList.foldl (fun acc (nm, v) => setAssoc nm v acc) a.signals ∧
    res.2.sigEvents = d.2.2.toList.foldl (fun acc (nm, m) => setAssoc nm m acc) a.sigEvents := by
  have hs := diffRowSigs_sound rowSig rowEv inst newMarks oldMarks oldSigs hmark 0 #[] #[] #[] (Nat.zero_le _) rfl (fun _ h => nomatch h)
  dsimp only [seedRowsM, StateT.run, bind, StateT.bind, pure, StateT.pure]
  cases hd : diffRowSigs rowSig rowEv inst newMarks oldMarks oldSigs 0 #[] #[] #[] with
  | mk newSigs rest =>
      rcases rest with ⟨toEmit, toEv⟩
      rw [hd] at hs; dsimp only at hs ⊢
      have he := emitSignalsM_spec toEmit.toList a
      dsimp only [StateT.run] at he
      rw [he]; dsimp only
      have hev := emitSignalOnsM_spec toEv.toList { a with signals := toEmit.toList.foldl (fun acc (nm, v) => setAssoc nm v acc) a.signals }
      dsimp only [StateT.run] at hev
      rw [hev]; exact ⟨hs.1, hs.2, rfl, rfl, rfl, rfl⟩

theorem renderSig_resolved_spec {σ msg : Type} (ns : String) (get : σ → String)
    (s₁ s₂ : σ) (pre : String) (n : Nat) (a : DomArena msg) (f : Nat) (hbound : a.nextId + 1 < UInt32.size) :
    let (sigHtml, _, _) := View.renderSig (.dyn get : View σ msg) s₁ pre n
    let (root, aMid) := (buildDomM (m := StateM (DomArena msg)) ns sigHtml).run a
    let aOut := (MonadDom.setSignal (m := StateM (DomArena msg)) s!"{pre}#{n}" (get s₂) aMid).2
    readResolvedDomTree (f + 1) aOut root = specDom ns (View.render (.dyn get) s₂) ∧
    aOut.nextId = a.nextId + 1 ∧ ∀ m : Dom.Node, m.toNat < a.nextId → aOut.get m = a.get m := by
  let node := UInt32.ofNat a.nextId
  let sigNm := s!"{pre}#{n}"
  let realNs := if ns == "" && "span" == "svg" then Dom.svgNs else ns
  let a1 : DomArena msg := { a with nextId := a.nextId + 1 }
  have haMid : (buildDomM (m := StateM (DomArena msg)) ns (.element "span" [.signalBind sigNm] [.text (get s₁)])).run a =
      (node, (applyAttrsM (m := StateM (DomArena msg)) node [.signalBind sigNm] (a1.set node (.element realNs "span" {} [] []))).2) := by
    dsimp only [buildDomM, StateT.run, bind, StateT.bind, pure, StateT.pure, MonadDom.createElement, DomArena.alloc]
    have hset : ({ a with nextId := a.nextId + 1, store := fun m => if (m == node) = true then ArenaEntry.element realNs "span" {} [] [] else a.store m } : DomArena msg) =
        a1.set node (.element realNs "span" {} [] []) := rfl
    rw [hset]
    cases applyAttrsM (m := StateM (DomArena msg)) node [.signalBind sigNm] (a1.set node (.element realNs "span" {} [] [])); rfl
  have hev : (evalSpecAttrs ([Attr.signalBind sigNm] : List (Attr msg))).sigBind = some sigNm := rfl
  dsimp only [View.renderSig]
  rw [haMid, applyAttrsM_fresh_element a1 node realNs "span" [] [.signalBind sigNm]]
  simp only [sigNm, MonadDom.setSignal, View.render, specDom, readResolvedDomTree, DomArena.get,
    show (a1.set node (ArenaEntry.element realNs "span" (evalSpecAttrs [Attr.signalBind sigNm])
      (List.filterMap managedAttrName (normalizeAttrs [Attr.signalBind sigNm])) [])).store node =
      ArenaEntry.element realNs "span" (evalSpecAttrs [Attr.signalBind sigNm])
        (List.filterMap managedAttrName (normalizeAttrs [Attr.signalBind sigNm])) [] from DomArena.get_set_self _ _ _,
    hev, lookupAssoc_setAssoc, beq_self_eq_true, ↓reduceIte, Option.getD_some]
  refine ⟨trivial, rfl, fun m hm => ?_⟩
  have hne : m ≠ node := node_ne_of_toNat_ne (by dsimp only [node]; rw [uint32_toNat_ofNat_lt_vp a.nextId (by omega)]; omega)
  exact DomArena.get_set_ne _ _ hne

/-! ## 5. Browser Runtime & Local Island Driver Specifications -/

theorem registerHandlerSpec_sound {α : Type} (arr : Array α) (h : α) :
    let id := arr.size; let arr' := arr.push h
    arr'[id]? = some h ∧ ∀ j, j < arr.size → arr'[j]? = arr[j]? :=
  ⟨by simp, fun j hj => by simp [Array.getElem?_push, Nat.ne_of_lt hj]⟩

structure LocalInstSpec where
  props : String
  rendered : Html LocalMsg

structure LocalRuntimeSpec where
  store     : Std.HashMap String String
  instances : Std.HashMap String LocalInstSpec

def localMountStep (reg : Std.HashMap String LocalDef) (st : LocalRuntimeSpec)
    (key component : String) (init? : Option String) (props : String) : LocalRuntimeSpec :=
  let fk := localKey component key
  match reg[component]? with
  | none => st
  | some ldef =>
      match st.instances[fk]? with
      | some inst =>
          let next : LocalInstSpec := { props := props, rendered := if props != inst.props then ldef.viewForProps props (st.store.getD fk ldef.init) else inst.rendered }
          { st with instances := st.instances.insert fk next }
      | none =>
          let s0 := st.store.getD fk (init?.getD ldef.init)
          { store := st.store.insert fk s0, instances := st.instances.insert fk { props, rendered := ldef.viewForProps props s0 } }

theorem localMountSpec_init_vs_rerender (reg : Std.HashMap String LocalDef) (st : LocalRuntimeSpec)
    (key component : String) (init? : Option String) (props : String) (ldef : LocalDef) (hreg : reg[component]? = some ldef) :
    let fk := localKey component key; let st' := localMountStep reg st key component init? props
    (st.instances[fk]? = none → let s0 := st.store.getD fk (init?.getD ldef.init); st'.store[fk]? = some s0 ∧ st'.instances[fk]? = some ⟨props, ldef.viewForProps props s0⟩) ∧
    (∀ inst, st.instances[fk]? = some inst → st'.store = st.store ∧ st'.instances[fk]? = some ⟨props, if props != inst.props then ldef.viewForProps props (st.store.getD fk ldef.init) else inst.rendered⟩) :=
  ⟨fun h => by simp [localMountStep, hreg, h], fun inst h => by simp [localMountStep, hreg, h]⟩

def gcLocalsSpec (isConn : String → Bool) (st : LocalRuntimeSpec) : LocalRuntimeSpec :=
  let dead := st.instances.toList.filterMap (fun (k, _) => if isConn k then none else some k)
  { store := dead.foldl (·.erase ·) st.store, instances := dead.foldl (·.erase ·) st.instances }

private theorem foldl_erase_mem {α : Type} :
    ∀ (ks : List String) (m : Std.HashMap String α) (k : String), k ∈ ks → (ks.foldl (·.erase ·) m)[k]? = none
  | [], _, _, h => nomatch h
  | x :: xs, m, k, h => by
      rcases List.mem_cons.1 h with rfl | ht
      · by_cases hx : k ∈ xs; exact foldl_erase_mem xs (m.erase k) k hx
        have hf : ∀ (l : List String) (m' : Std.HashMap String α), k ∉ l → (l.foldl (·.erase ·) m')[k]? = m'[k]? := by
          intro l; induction l with
          | nil => intro _ _; rfl
          | cons y ys ihl =>
              intro m' hnl; have hne : y ≠ k := fun hEq => hnl (hEq ▸ .head _)
              simpa [List.foldl_cons, Std.HashMap.getElem?_erase, beq_eq_false_iff_ne.2 hne] using ihl (m'.erase y) (fun hm => hnl (.tail _ hm))
        simpa [List.foldl_cons] using hf xs (m.erase k) hx
      · exact foldl_erase_mem xs (m.erase x) k ht

private theorem foldl_erase_not_mem {α : Type} :
    ∀ (ks : List String) (m : Std.HashMap String α) (k : String), k ∉ ks → (ks.foldl (·.erase ·) m)[k]? = m[k]?
  | [], _, _, _ => rfl
  | x :: xs, m, k, h => by
      have hne : x ≠ k := fun hEq => h (hEq ▸ .head _)
      simpa [List.foldl_cons, Std.HashMap.getElem?_erase, beq_eq_false_iff_ne.2 hne] using foldl_erase_not_mem xs (m.erase x) k (fun hm => h (.tail _ hm))

theorem gcLocalsSpec_frame (isConn : String → Bool) (st : LocalRuntimeSpec) (k : String) :
    let st' := gcLocalsSpec isConn st
    (isConn k = true → st'.store[k]? = st.store[k]? ∧ st'.instances[k]? = st.instances[k]?) ∧
    ((∃ inst, (k, inst) ∈ st.instances.toList) → isConn k = false → st'.store[k]? = none ∧ st'.instances[k]? = none) := by
  let dead := st.instances.toList.filterMap (fun p => if isConn p.1 then none else some p.1)
  have hmem : ∀ x, x ∈ dead ↔ (∃ v, (x, v) ∈ st.instances.toList) ∧ isConn x = false := by
    intro x; simp only [dead, List.mem_filterMap]; constructor
    · rintro ⟨⟨a, v⟩, hm, hp⟩; split at hp <;> simp at hp; subst hp; exact ⟨⟨v, hm⟩, Bool.eq_false_iff.2 ‹_›⟩
    · rintro ⟨⟨v, hm⟩, hc⟩; exact ⟨(x, v), hm, by simp [hc]⟩
  refine ⟨fun hc => ?_, fun ⟨v, hv⟩ hc => ?_⟩
  · have hnd : k ∉ dead := fun hd => by rw [(hmem k).1 hd |>.2] at hc; cases hc
    exact ⟨foldl_erase_not_mem dead st.store k hnd, foldl_erase_not_mem dead st.instances k hnd⟩
  · have hd : k ∈ dead := (hmem k).2 ⟨⟨v, hv⟩, hc⟩
    exact ⟨foldl_erase_mem dead st.store k hd, foldl_erase_mem dead st.instances k hd⟩

def snapshotLocalsJson (entries : List (String × String)) : String :=
  Json.render (Json.obj (entries.map fun (k, v) => (k, .str v)))

def restoreLocalsFromJson (s : String) (base : Std.HashMap String String) : Std.HashMap String String :=
  match Json.parse s with
  | .ok (.obj members) => members.foldl (fun st (k, v) => match v with | .str str => st.insert k str | _ => st) base
  | _ => base

theorem snapshot_restore_locals_roundtrip (entries : List (String × String))
    (hnd : (entries.map Prod.fst).Nodup) (base : Std.HashMap String String) :
    let out := restoreLocalsFromJson (snapshotLocalsJson entries) base
    ∀ kv ∈ entries, out[kv.1]? = some kv.2 := by
  have hdep : (Json.obj (entries.map fun x => (x.1, Json.str x.2))).depth ≤ 64 := by
    have hm : Json.maxObj (entries.map fun x => (x.1, Json.str x.2)) ≤ 0 :=
      Json.maxObj_le_iff.2 fun kv hkv => by rcases List.mem_map.1 hkv with ⟨p, _, rfl⟩; exact Nat.le_refl _
    dsimp only [Json.depth]; omega
  have hpr := parse_render hdep
  have hfold : ∀ (es : List (String × String)) (b : Std.HashMap String String), (es.map Prod.fst).Nodup →
      ∀ kv ∈ es, ((es.map fun (k, v) => (k, Json.str v)).foldl (fun st (k, v) => match v with | .str str => st.insert k str | _ => st) b)[kv.1]? = some kv.2 := by
    intro es; induction es with
    | nil => intro _ _ _ hm; nomatch hm
    | cons kv rest ih =>
        intro b hnde p hp; rcases List.nodup_cons.1 hnde with ⟨hnotin, hndr⟩
        rcases List.mem_cons.1 hp with rfl | ht
        · have hpres : ∀ (rs : List (String × String)) (b' : Std.HashMap String String), p.1 ∉ rs.map Prod.fst →
              ((rs.map fun (k, v) => (k, Json.str v)).foldl (fun st (k, v) => match v with | .str str => st.insert k str | _ => st) b')[p.1]? = b'[p.1]? := by
            intro rs; induction rs with
            | nil => intro _ _; rfl
            | cons q qt ihr =>
                intro b' hnm; have hne : q.1 ≠ p.1 := fun h => hnm (h ▸ .head _)
                simpa [List.foldl_cons, Std.HashMap.getElem?_insert, beq_eq_false_iff_ne.2 hne] using ihr (b'.insert q.1 q.2) (fun hm => hnm (.tail _ hm))
          simpa [List.foldl_cons] using (hpres rest (b.insert p.1 p.2) hnotin).trans (by simp)
        · exact ih (b.insert kv.1 kv.2) hndr p ht
  simpa [restoreLocalsFromJson, snapshotLocalsJson, hpr] using hfold entries base hnd

def drainQueueSpec {σ Msg : Type} (step : σ → Msg → σ × List Msg) :
    Nat → σ → Array Msg → σ × Array Msg
  | 0, st, q => (st, q)
  | fuel + 1, st, q =>
      if q.isEmpty then (st, #[])
      else
        let (st', nextQ) := q.toList.foldl (fun (acc, nxt) m => let (s', sp) := step acc m; (s', nxt ++ sp)) (st, [])
        drainQueueSpec step fuel st' nextQ.toArray

theorem drainPendingQueue_fifo_spec {σ Msg : Type} (step : σ → Msg → σ)
    (st : σ) (q : Array Msg) (fuel : Nat) (hf : 0 < fuel) :
    drainQueueSpec (fun s m => (step s m, [])) fuel st q = (q.toList.foldl step st, #[]) := by
  cases fuel with
  | zero => omega
  | succ f =>
      dsimp only [drainQueueSpec]
      by_cases hemp : q.isEmpty
      · have hnil : q.toList = [] := by cases q; simp_all
        simp [hemp, hnil]
      · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
        have hfold : ∀ (ms : List Msg) (s : σ) (acc : List Msg),
            ms.foldl (fun p m => (step p.1 m, p.2 ++ [])) (s, acc) = (ms.foldl step s, acc) := by
          intro ms; induction ms with | nil => intro _ _; rfl | cons m ms ih => intro s acc; simpa [List.foldl_cons] using ih (step s m) acc
        rw [hfold q.toList st []]; cases f <;> simp [drainQueueSpec]

private theorem renderSigAttrs_of_dynValGets_empty {σ msg : Type} (s : σ) (pre : String) :
    ∀ (attrs : List (VAttr σ msg)) (n en : Nat), dynValGets attrs = [] → dynOnGets attrs = [] →
      (renderSigAttrs s pre attrs n en).1 = attrs.map (VAttr.eval s)
  | [], _, _, _, _ => rfl
  | .stat _ :: rest, n, en, h, he => by simp [renderSigAttrs, VAttr.eval, renderSigAttrs_of_dynValGets_empty s pre rest n en h he]
  | .bind _ :: rest, n, en, h, he => by simp [renderSigAttrs, VAttr.eval, renderSigAttrs_of_dynValGets_empty s pre rest n en h he]
  | .dynVal _ _ :: _, _, _, h, _ => by simp [dynValGets] at h
  | .dynOn _ _ :: _, _, _, _, he => by simp [dynOnGets] at he

mutual
  private theorem renderSig_of_collectDyn_empty {σ msg : Type} :
      ∀ (v : View σ msg), v.collectDyn = [] → v.collectDynOn = [] → ∀ (s : σ) (pre : String) (n en : Nat),
        (v.renderSig s pre n en).1 = v.render s
    | .text _, _, _, _, _, _, _ | .keyedList .., _, _, _, _, _, _ | .static _, _, _, _, _, _, _
    | .dynNode _, _, _, _, _, _, _ | .memo _, _, _, _, _, _, _ => rfl
    | .dyn _, h, _, _, _, _, _ => by simp [View.collectDyn] at h
    | .element _ attrs kids, h, he, s, pre, n, en => by
        simp only [View.collectDyn, List.append_eq_nil_iff] at h
        simp only [View.collectDynOn, List.append_eq_nil_iff] at he
        simp only [View.renderSig, View.render,
          renderSigAttrs_of_dynValGets_empty s pre attrs n en h.1 he.1,
          renderSigList_of_collectDynList_empty kids h.2 he.2 s pre]
    | .ifElse cond y no, h, he, s, pre, n, en => by
        simp only [View.collectDyn, List.append_eq_nil_iff] at h
        simp only [View.collectDynOn, List.append_eq_nil_iff] at he
        by_cases hc : cond s = true <;>
          simp [View.renderSig, View.render, hc,
            renderSig_of_collectDyn_empty y h.1 he.1 s pre n en,
            renderSig_of_collectDyn_empty no h.2 he.2 s pre]

  private theorem renderSigList_of_collectDynList_empty {σ msg : Type} :
      ∀ (ks : List (View σ msg)), View.collectDynList ks = [] → View.collectDynOnList ks = [] →
        ∀ (s : σ) (pre : String) (n en : Nat), (View.renderSigList ks s pre n en).1 = View.renderEach ks s
    | [], _, _, _, _, _, _ => rfl
    | k :: ks, h, he, s, pre, n, en => by
        simp only [View.collectDynList, List.append_eq_nil_iff] at h
        simp only [View.collectDynOnList, List.append_eq_nil_iff] at he
        simp [View.renderSigList, View.renderEach,
          renderSig_of_collectDyn_empty k h.1 he.1 s pre n en,
          renderSigList_of_collectDynList_empty ks h.2 he.2 s pre]
end

private theorem getElem?_map_zipIdx {α β : Type} (g : α × Nat → β) :
    ∀ (xs : List α) (k i : Nat), ((xs.zipIdx k).map g)[i]? = xs[i]?.map (fun a => g (a, k + i))
  | [], _, _ => by simp
  | _ :: _, _, 0 => by simp [List.zipIdx]
  | _ :: rest, k, i + 1 => by simpa [List.zipIdx, Nat.add_assoc, Nat.add_comm 1 i] using getElem?_map_zipIdx g rest (k + 1) i

private theorem Html.DomCleanList_map {α msg : Type} (f : α → Html msg) :
    ∀ (xs : List α), (∀ a ∈ xs, (f a).DomClean = true) → Html.DomCleanList (xs.map f) = true
  | [], _ => rfl
  | x :: rest, h => by simp [Html.DomCleanList, h x (.head _), Html.DomCleanList_map f rest (fun a ha => h a (.tail _ ha))]

theorem View.DomClean_forEach {α σ msg : Type} (tag : String) (items : σ → Array α)
    (key : α → String) (child : View α msg) (attrs : List (VAttr σ msg)) (sigPrefix : String)
    (ha : VAttrListClean attrs)
    (hdyn : (View.collectDyn child).isEmpty = true)
    (hdynOn : (View.collectDynOn child).isEmpty = true)
    (hcl : ∀ a, (child.render a).DomClean = true)
    (htxt : ∀ a, (child.render a).textOf? = none)
    (hnd : ∀ s, (((items s).map key).toList).Nodup)
    (hkey : ∀ a b, key a = key b → child.render a = child.render b) :
    View.DomClean (V.forEach tag items key child attrs sigPrefix) := by
  dsimp only [V.forEach]
  have hnotDirect : V.isDirectTmpl child = false := by
    cases child with
    | element _ _ _ => simp [V.isDirectTmpl, hdyn, hdynOn]
    | _ => rfl
  split
  · intro s
    simp only [Html.DomClean, ha.1 s, ha.2.1 s, Bool.not_false, Bool.true_and, Array.toList_map]
    exact Html.DomCleanList_map _ _ fun a _ => by simp [Html.DomClean_withKey, hcl a]
  · simp only [hnotDirect, Bool.false_eq_true, ↓reduceIte]
    refine ⟨ha, ?_, ?_, ?_, ?_⟩
    · intro s
      dsimp only
      have h1 : disambiguateKeys ((items s).map key) = (items s).map key := disambiguateKeys_of_nodup (by simpa using hnd s)
      rw [h1]
      simp [List.length_map, List.length_zipIdx]
    · intro s
      dsimp only
      have hde : child.collectDyn = [] := List.isEmpty_iff.1 hdyn
      have hdo : child.collectDynOn = [] := List.isEmpty_iff.1 hdynOn
      exact Html.DomCleanList_map _ _ fun p _ => by
        simp [Html.DomClean_withKey, renderSig_of_collectDyn_empty child hde hdo p.1, hcl p.1]
    · intro s r hr
      dsimp only at hr
      rcases List.mem_map.1 hr with ⟨p, _, rfl⟩
      rw [Html.textOf?_withKey, renderSig_of_collectDyn_empty child (List.isEmpty_iff.1 hdyn) (List.isEmpty_iff.1 hdynOn)]
      exact htxt p.1
    · intro s₁ s₂ i j hi hj hkeq
      dsimp only at hi hj hkeq ⊢
      have hde : child.collectDyn = [] := List.isEmpty_iff.1 hdyn
      have hdo : child.collectDynOn = [] := List.isEmpty_iff.1 hdynOn
      have hu1 : disambiguateKeys ((items s₁).map key) = (items s₁).map key := disambiguateKeys_of_nodup (by simpa using hnd s₁)
      have hu2 : disambiguateKeys ((items s₂).map key) = (items s₂).map key := disambiguateKeys_of_nodup (by simpa using hnd s₂)
      have hi' : i < (items s₁).size := by simpa [hu1] using hi
      have hj' : j < (items s₂).size := by simpa [hu2] using hj
      have hkaEq : key (items s₁)[i] = key (items s₂)[j] := by simpa [hu1, hu2] using hkeq
      rw [getElem?_map_zipIdx _ (items s₁).toList 0 i, getElem?_map_zipIdx _ (items s₂).toList 0 j]
      simp only [Nat.zero_add, Array.getElem?_toList, Array.getElem?_eq_getElem hi', Array.getElem?_eq_getElem hj', Option.map_some]
      rw [renderSig_of_collectDyn_empty child hde hdo, renderSig_of_collectDyn_empty child hde hdo]
      have hd1 : (disambiguateKeys ((items s₁).map key)).getD i (key (items s₁)[i]) = key (items s₁)[i] := by simp [hu1, Array.getD, hi']
      have hd2 : (disambiguateKeys ((items s₂).map key)).getD j (key (items s₂)[j]) = key (items s₂)[j] := by simp [hu2, Array.getD, hj']
      rw [hd1, hd2, hkaEq, hkey _ _ hkaEq]

/-! ## 6. Compiled Row-Template & Prefix/Suffix/Swap Fast-Path Soundness -/

private theorem prefixMatchLen_ge (oldMarks newMarks : Array USize) :
    ∀ i, i ≤ prefixMatchLen oldMarks newMarks i := by
  intro i
  induction hrem : oldMarks.size - i generalizing i with
  | zero => unfold prefixMatchLen; split <;> omega
  | succ r ih =>
      unfold prefixMatchLen
      split
      · rename_i h
        dsimp only
        split
        · exact Nat.le_trans (Nat.le_succ i) (ih (i + 1) (by omega))
        · exact Nat.le_refl i
      · exact Nat.le_refl i

theorem prefixMatchLen_bound (oldMarks newMarks : Array USize) :
    ∀ i, i ≤ oldMarks.size → i ≤ newMarks.size →
      prefixMatchLen oldMarks newMarks i ≤ oldMarks.size ∧
      prefixMatchLen oldMarks newMarks i ≤ newMarks.size := by
  intro i
  induction hrem : oldMarks.size - i generalizing i with
  | zero =>
      intro ho hn; unfold prefixMatchLen; split
      · omega
      · exact ⟨ho, hn⟩
  | succ r ih =>
      intro ho hn; unfold prefixMatchLen; split
      · rename_i h
        dsimp only
        split
        · exact ih (i + 1) (by omega) (by omega) (by omega)
        · exact ⟨ho, hn⟩
      · exact ⟨ho, hn⟩

theorem prefixMatchLen_sound (oldMarks newMarks : Array USize) :
    ∀ i k, i ≤ k → k < prefixMatchLen oldMarks newMarks i →
      ∃ (ho : k < oldMarks.size) (hn : k < newMarks.size),
        newMarks[k]'hn ≠ 0 ∧ oldMarks[k]'ho = newMarks[k]'hn := by
  intro i
  induction hrem : oldMarks.size - i generalizing i with
  | zero =>
      intro k hik hklt
      unfold prefixMatchLen at hklt
      split at hklt <;> omega
  | succ r ih =>
      intro k hik hklt
      unfold prefixMatchLen at hklt
      split at hklt
      · rename_i h
        dsimp only at hklt
        split at hklt
        · rename_i hm
          simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hm
          by_cases heq : k = i
          · subst heq; exact ⟨h.1, h.2, hm.1, hm.2⟩
          · exact ih (i + 1) (by omega) k (by omega) hklt
        · omega
      · omega

theorem suffixMatchLen_sound (oldMarks newMarks : Array USize) (p : Nat) :
    ∀ q j, q ≤ j → j < suffixMatchLen oldMarks newMarks p q →
      p + j < oldMarks.size ∧ p + j < newMarks.size ∧
      ∃ (ho : oldMarks.size - 1 - j < oldMarks.size) (hn : newMarks.size - 1 - j < newMarks.size),
        newMarks[newMarks.size - 1 - j]'hn ≠ 0 ∧
        oldMarks[oldMarks.size - 1 - j]'ho = newMarks[newMarks.size - 1 - j]'hn := by
  intro q
  induction hrem : oldMarks.size - (p + q) generalizing q with
  | zero =>
      intro j hqj hjlt
      unfold suffixMatchLen at hjlt
      split at hjlt <;> omega
  | succ r ih =>
      intro j hqj hjlt
      unfold suffixMatchLen at hjlt
      split at hjlt
      · rename_i h
        dsimp only at hjlt
        split at hjlt
        · rename_i hm
          simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hm
          by_cases heq : j = q
          · subst heq; exact ⟨h.1, h.2, by omega, by omega, hm.1, hm.2⟩
          · exact ih (q + 1) (by omega) j (by omega) hjlt
        · omega
      · omega

private theorem mem_collectChangedMarksLoop_of_mem (oldMarks newMarks : Array USize) :
    ∀ i (acc : Array Nat) x, x ∈ acc.toList → x ∈ (collectChangedMarksLoop oldMarks newMarks i acc).toList := by
  intro i
  induction hrem : newMarks.size - i generalizing i with
  | zero =>
      intro acc x hx; unfold collectChangedMarksLoop
      split
      · omega
      · exact hx
  | succ r ih =>
      intro acc x hx; unfold collectChangedMarksLoop
      split
      · rename_i h
        apply ih (i + 1) (by omega)
        split
        · exact hx
        · rw [Array.toList_push]; exact List.mem_append_left _ hx
      · exact hx

theorem collectChangedMarksLoop_sound (oldMarks newMarks : Array USize) :
    ∀ i (acc : Array Nat) k (hk : k < newMarks.size),
      i ≤ k → k ∉ (collectChangedMarksLoop oldMarks newMarks i acc).toList →
      newMarks[k]'hk ≠ 0 ∧ oldMarks[k]? = some (newMarks[k]'hk) := by
  intro i
  induction hrem : newMarks.size - i generalizing i with
  | zero => intro _ k hk hik _; omega
  | succ r ih =>
      intro acc k hk hik hnot
      unfold collectChangedMarksLoop at hnot
      simp only [show i < newMarks.size by omega, ↓reduceDIte] at hnot
      by_cases heq : k = i
      · subst heq
        by_cases hm : (newMarks[k]'hk != 0 && oldMarks[k]? == some (newMarks[k]'hk)) = true
        · simpa [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] using hm
        · have hmf : (newMarks[k]'hk != 0 && oldMarks[k]? == some (newMarks[k]'hk)) = false := Bool.eq_false_iff.2 hm
          simp only [hmf, Bool.false_eq_true, ↓reduceIte] at hnot
          have hmem : k ∈ (collectChangedMarksLoop oldMarks newMarks (k + 1) (acc.push k)).toList :=
            mem_collectChangedMarksLoop_of_mem oldMarks newMarks (k + 1) (acc.push k) k (by rw [Array.toList_push]; simp)
          exact False.elim (hnot hmem)
      · exact ih (i + 1) (by omega) _ k hk (by omega) hnot

theorem patchNodeSlotAt_nextId {msg : Type} (a : DomArena msg) (n : Dom.Node)
    (path : List Nat) (attrName val : String) :
    (patchNodeSlotAt a n path attrName val).nextId = a.nextId := by
  induction path generalizing n with
  | nil =>
      dsimp only [patchNodeSlotAt]
      split
      · rfl
      · split <;> rfl
  | cons idx rest ih =>
      dsimp only [patchNodeSlotAt]
      cases a.get n with
      | element _ _ _ _ cs =>
          dsimp only
          cases cs[idx]? with
          | none => rfl
          | some child => exact ih child
      | _ => rfl

theorem patchNodeSlotAt_text_root {msg : Type} (a : DomArena msg) (n : Dom.Node) (old val : String)
    (hget : a.get n = .text old) :
    (patchNodeSlotAt a n [] "" val).get n = .text val ∧
    ∀ m, m ≠ n → (patchNodeSlotAt a n [] "" val).get m = a.get m := by
  refine ⟨?_, ?_⟩
  · simp [patchNodeSlotAt, DomArena.modify, hget]
  · intro m hm; simp [patchNodeSlotAt, DomArena.modify, hm]

end Qed
