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
  | .text n | .dyn n _ | .elem n _ | .list n .. | .stat n | .dynNode n _ | .memo n .. => n
  | .cond _ inner => inner.rootNode

mutual
  def View.DirectRenderSafe {σ msg : Type} (s : σ) : View σ msg → Bool
    | .text _ | .dyn _ | .static _ | .dynNode _ | .memo _ => true
    | .element _ attrs kids =>
        (!ownsChildren (attrs.map (VAttr.eval s)) || kids.isEmpty) && View.DirectRenderSafeEach s kids
    | .ifElse cond y n => if cond s then y.DirectRenderSafe s else n.DirectRenderSafe s
    | .keyedList .. => false

  def View.DirectRenderSafeEach {σ msg : Type} (s : σ) : List (View σ msg) → Bool
    | [] => true
    | k :: ks => k.DirectRenderSafe s && View.DirectRenderSafeEach s ks
end

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

mutual
  def View.DomClean {σ msg : Type} : View σ msg → Prop
    | .text _ | .dyn _ => True
    | .static h => h.DomClean = true
    | .dynNode get => ∀ s, (get s).DomClean = true
    | .memo sm => ∀ s, (sm.eval s).DomClean = true
    | .ifElse _ y n => View.DomClean y ∧ View.DomClean n
    | .element _ attrs kids => VAttrListClean attrs ∧ View.DomCleanEach kids
    | .keyedList .. => False

  def View.DomCleanEach {σ msg : Type} : List (View σ msg) → Prop
    | [] => True
    | k :: ks => View.DomClean k ∧ View.DomCleanEach ks
end

theorem View.renderEach_append {σ msg : Type} (s : σ) :
    ∀ (xs ys : List (View σ msg)), View.renderEach (xs ++ ys) s = View.renderEach xs s ++ View.renderEach ys s
  | [], _ => rfl
  | _ :: rest, ys => by simp [View.renderEach, View.renderEach_append s rest ys]

mutual
  theorem View.DirectRenderSafe_of_DomClean {σ msg : Type} :
      ∀ {v : View σ msg}, View.DomClean v → ∀ s, v.DirectRenderSafe s = true
    | .text _, _, _ | .dyn _, _, _ | .static _, _, _ | .dynNode _, _, _ | .memo _, _, _ => rfl
    | .ifElse c _ _, ⟨hy, hn⟩, s => by
        cases hc : c s <;> simp [View.DirectRenderSafe, hc, View.DirectRenderSafe_of_DomClean hy, View.DirectRenderSafe_of_DomClean hn]
    | .element _ _ _, ⟨ha, hks⟩, s => by
        simp [View.DirectRenderSafe, ha.1 s, View.DirectRenderSafeEach_of_DomClean hks s]
    | .keyedList .., h, _ => False.elim h

  theorem View.DirectRenderSafeEach_of_DomClean {σ msg : Type} :
      ∀ {ks : List (View σ msg)}, View.DomCleanEach ks → ∀ s, View.DirectRenderSafeEach s ks = true
    | [], _, _ => rfl
    | _ :: _, ⟨hk, hks⟩, s => by
        simp [View.DirectRenderSafeEach, View.DirectRenderSafe_of_DomClean hk s, View.DirectRenderSafeEach_of_DomClean hks s]
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
    | .keyedList .., h, _ => False.elim h

  theorem View.DomCleanEach_renderEach {σ msg : Type} :
      ∀ {ks : List (View σ msg)}, View.DomCleanEach ks → ∀ s, Html.DomCleanList (View.renderEach ks s) = true
    | [], _, _ => rfl
    | _ :: _, ⟨hk, hks⟩, s => by
        simp [View.renderEach, Html.DomCleanList, View.DomClean_render hk s, View.DomCleanEach_renderEach hks s]
end

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
  | cls _ | key _ | on _ _ | onValue _ _ | localCell _ _ _ _ _ | signalBind _ | signalAttr _ _ _ => simp [Attr.key?] at hbk

private def noBind {σ msg : Type} (xs : List (VAttr σ msg)) : Bool :=
  xs.all (fun | .bind _ => false | _ => true)

private def stepDynAttr {σ msg : Type} (s : σ) (cur : SpecElemState msg) : VAttr σ msg → SpecElemState msg
  | .bind f => stepSpecAttr cur (f s)
  | .dynVal k g => stepSpecAttr cur (.attr k (g s))
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
      | bind _ => simp at hnb
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
        | bind _ => simp at hn
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
        cases va with | bind _ => simp at hn | dynVal _ _ => exact ⟨rfl, rfl, ih hn.2⟩ | stat a => cases a <;> simp [AttrKeyEq, ih hn.2]
  intro xs hnb
  unfold normalizeAttrs; dsimp only
  erw [← hcls xs hnb]
  rw [List.filterMap_append, List.filterMap_append]; erw [hfm _ _ (hdd _ _ (hnon xs hnb))]; rfl

private theorem stepSpecAttr_equiv {msg : Type} {s₁ s₂ : SpecElemState msg} (a : Attr msg)
    (he : ElemStateEquiv s₁ s₂) : ElemStateEquiv (stepSpecAttr s₁ a) (stepSpecAttr s₂ a) := by
  refine ⟨fun k => ?_, ?_, ?_⟩
  · cases a with
    | cls _ | localCell _ _ _ _ _ => simp [stepSpecAttr, lookupAssoc_setAssoc, he.1]
    | attr k' _ => by_cases hv : k' = "value" <;> simp [stepSpecAttr, hv, lookupAssoc_setAssoc, he.1]
    | flag k' p => by_cases hc : k' = "checked" <;> cases p <;> simp [stepSpecAttr, hc, lookupAssoc_setAssoc, lookupAssoc_eraseAssoc, he.1] <;> split <;> exact he.1 k
    | key _ | on _ _ | onValue _ _ | signalBind _ | signalAttr _ _ _ => exact he.1 k
  · cases a with
    | attr k' _ => by_cases hv : k' = "value" <;> simp [stepSpecAttr, hv, he.2.1]
    | flag k' _ => by_cases hc : k' = "checked" <;> simp [stepSpecAttr, hc, he.2.1]
    | _ => exact he.2.1
  · cases a with
    | attr k' _ => by_cases hv : k' = "value" <;> simp [stepSpecAttr, hv, he.2.2]
    | flag k' _ => by_cases hc : k' = "checked" <;> simp [stepSpecAttr, hc, he.2.2]
    | _ => exact he.2.2

private theorem dedupAttrs_foldl_equiv {msg : Type} :
    ∀ (xs : List (Attr msg)) (cur : SpecElemState msg),
      xs.all Attr.NormalKey = true → ElemStateEquiv ((dedupAttrs xs).foldl stepSpecAttr cur) (xs.foldl stepSpecAttr cur)
  | [], _, _ => ⟨fun _ => rfl, rfl, rfl⟩
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
            refine ⟨fun k' => (ih.1 k').trans ?_, ih.2.1.trans ?_, ih.2.2.trans ?_⟩
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
          · simp only [dedupAttrs, hx, hany, List.foldl_cons]
            exact dedupAttrs_foldl_equiv xs (stepSpecAttr cur x) hn.2

private theorem stepDynAttr_equiv {σ msg : Type} (s : σ) :
    ∀ (xs : List (VAttr σ msg)) {s₁ s₂ : SpecElemState msg}, ElemStateEquiv s₁ s₂ →
      ElemStateEquiv (xs.foldl (stepDynAttr s) s₁) (xs.foldl (stepDynAttr s) s₂)
  | [], _, _, h => h
  | va :: xs, _, _, h => by
      apply stepDynAttr_equiv s xs
      cases va with | stat _ => exact h | bind _ => exact stepSpecAttr_equiv _ h | dynVal _ _ => exact stepSpecAttr_equiv _ h

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
      | bind _ => simp at hnb
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
      | bind _ => simp at hnb
      | dynVal k _ => apply nonCls_checked_eq s₁ s₂ rest _ _ hnb.2; by_cases hv : k = "value" <;> simp [stepSpecAttr, hv, hc]
      | stat a => cases a <;> (try exact nonCls_checked_eq s₁ s₂ rest _ _ hnb.2 (by simp [stepSpecAttr, hc]; all_goals (try split <;> simp [hc])))

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
      | bind _ => simp at hnb
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
        cases va with | bind _ => simp at hnb | stat _ => exact hns | dynVal _ _ => simp only [dynValNoLaterStat, Bool.and_eq_true] at hns; exact hns.2
      cases va with
      | bind _ => simp at hnb
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
                    | bind _ => simp at hnbw
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
      | bind _ => simp at hnb
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
      | dynVal k' g =>
          cases hr : lastDynVal? k s₂ rest with
          | some _ => simp [lastDynVal?, Option.orElse, hr] at hn
          | none =>
              have hne : k' ≠ k := by intro hEq; subst hEq; simp [lastDynVal?, Option.orElse, hr] at hn
              have ih := nonCls_none_key s₁ s₂ k rest (stepSpecAttr st₁ (.attr k' (g s₁))) (stepSpecAttr st₂ (.attr k' (g s₂))) hnb.2 hr
              refine ⟨fun hkv hv => ih.1 hkv (by subst hkv; simp [stepSpecAttr, hv]),
                      fun hnk ha => ih.2 hnk (by by_cases hv : k' = "value" <;> simp [stepSpecAttr, hv, lookupAssoc_setAssoc, beq_eq_false_iff_ne.2 hne, ha])⟩

private theorem anyBind_false_noBind {σ msg : Type} (f : VAttr σ msg → Bool)
    (hf : ∀ x, f x = match x with | .bind _ => true | _ => false) :
    ∀ (xs : List (VAttr σ msg)), ¬(xs.any f = true) → noBind xs = true
  | [], _ => rfl
  | x :: xs, hn => by
      have hx : f x = false := by cases hfx : f x; rfl; exact False.elim (hn (by simp [List.any_cons, hfx]))
      have hxs : ¬(xs.any f = true) := fun h => hn (by simp [List.any_cons, h])
      cases x with
      | bind _ => simp [hf] at hx
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
    rcases hm with ⟨st', hget, hattrs, hval, hchk, hElClean'⟩
    exact ⟨applyAttrsM_nextId a node _ _, fun m hm => applyAttrsM_get_ne a node _ _ m hm,
      st', (normalizeAttrs (attrs.map (VAttr.eval s₂))).filterMap managedAttrName, hget, hElClean',
      ⟨hattrs, hval, hchk⟩, fun nm hnm => List.contains_iff_mem.2 hnm⟩
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
            | bind _ => simp at hnb'
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
          cases va with | bind _ => simp at hn | dynVal _ _ => simpa using ih hn.2 | stat a => cases a <;> simp [ih hn.2]
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
       heq.2.2.trans (by rw [hev1]; exact hdd1.2.2)⟩
    have hstepEq := stepDynAttr_equiv s₂ attrs heq1
    refine ⟨rfl, fun m hm => DomArena.get_set_ne _ _ hm, st', mg, DomArena.get_set_self _ _ _, hEl', ⟨?_, ?_, ?_⟩,
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
              | bind _ => simp at hn
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
              | bind _ => simp at hn
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
    · refine hstepEq.2.2.trans ((stepDynAttr_checked s₂ attrs _ hnb).trans ((nonCls_checked_eq s₁ s₂ attrs base base hnb rfl).trans ?_))
      rw [hev2]; exact hdd2.2.2.symm

mutual
  def VStateMatches {σ msg : Type} : View σ msg → σ → DomArena msg → Dom.Node → VState σ msg → Prop
    | .text _, _, _, n, .text n' => n' = n
    | .dyn get, s, _, n, .dyn n' last => n' = n ∧ last = get s
    | .static _, _, _, n, .stat n' => n' = n
    | .dynNode get, s, _, n, .dynNode n' last => n' = n ∧ last = get s
    | .memo sm, s, _, n, .memo n' lk lh => n' = n ∧ lk = sm.keyOf s ∧ lh = sm.eval s
    | .ifElse c y no, s, a, n, .cond wy inner =>
        wy = c s ∧ (if c s then VStateMatches y s a n inner else VStateMatches no s a n inner)
    | .element _ attrs kids, s, a, n, .elem n' ks =>
        n' = n ∧ ∃ ns' tag' st mg domCs, a.get n = .element ns' tag' st mg domCs ∧
          (∀ nm ∈ (normalizeAttrs (attrs.map (VAttr.eval s))).filterMap managedAttrName, mg.contains nm = true) ∧
          VStateKidsMatches kids s a domCs ks
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
    | _, _, .keyedList .., _, _, _, _, _, _, _, _, h => False.elim h
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
                rcases h with ⟨hn, ns', tag', st, mg, domCs, hget, hmg, hks⟩
                rcases hcl with ⟨hmem, _, _, st', mg', domCs', hget', _, _, hcs⟩
                have hfrN := hfr n hmem
                rw [hget'] at hget; cases hget
                exact ⟨hn, _, tag, st, mg, domCs, hfrN.trans hget', hmg,
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
      ∀ (v : View σ msg) (s : σ) (a : DomArena msg), v.DirectRenderSafe s = true →
        let r := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
        (r.1.1, r.2) = (buildDomM (m := StateM (DomArena msg)) ns (View.render v s)).run a
    | .text _, _, _, _ | .dyn _, _, _, _ | .static _, _, _, _ | .dynNode _, _, _, _ | .memo _, _, _, _ => rfl
    | .ifElse c y n, s, a, hs => by
        cases hc : c s <;> simp only [View.DirectRenderSafe, hc, Bool.false_eq_true, ↓reduceIte] at hs
        · simpa [buildViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, View.render, hc] using buildViewM_eq_buildDomM ns n s a hs
        · simpa [buildViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, View.render, hc] using buildViewM_eq_buildDomM ns y s a hs
    | .element tag attrs kids, s, a, hs => by
        simp only [View.DirectRenderSafe, Bool.and_eq_true, Bool.or_eq_true] at hs
        dsimp only [buildViewM, buildDomM, MonadDom.createElement, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
        cases hce : a.alloc (ArenaEntry.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag {} [] []) with
        | mk node a1 =>
            cases ha : applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s)) a1 with
            | mk _ a2 =>
                rcases hs.1 with hown | hemp
                · simp only [hown, ↓reduceIte, StateT.bind, pure, StateT.pure]
                  have hks := buildViewKidsM_eq_buildDomListM (Dom.childNsOf ns tag) node kids s a2 hs.2
                  dsimp only [StateT.run] at hks
                  cases hbk : buildViewKidsM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node kids s a2 with
                  | mk ks a3 =>
                      rw [hbk] at hks; dsimp only at hks ⊢; rw [hks]
                      cases buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node (View.renderEach kids s) a2; rfl
                · have hnil : kids = [] := List.isEmpty_iff.1 hemp
                  subst hnil
                  cases hwo : ownsChildren (attrs.map (VAttr.eval s))
                  · simp [buildViewKidsM, buildDomListM, View.renderEach, bind, StateT.bind, pure, StateT.pure]
                  · simp [buildViewKidsM, bind, StateT.bind, pure, StateT.pure]
    | .keyedList .., _, _, h => by simp [View.DirectRenderSafe] at h

  theorem buildViewKidsM_eq_buildDomListM {σ msg : Type} (ns : String) (parent : Dom.Node) :
      ∀ (ks : List (View σ msg)) (s : σ) (a : DomArena msg), View.DirectRenderSafeEach s ks = true →
        ((buildViewKidsM (m := StateM (DomArena msg)) ns parent ks s).run a).2 =
        ((buildDomListM (m := StateM (DomArena msg)) ns parent (View.renderEach ks s)).run a).2
    | [], _, _, _ => rfl
    | k :: rest, s, a, hs => by
        simp only [View.DirectRenderSafeEach, Bool.and_eq_true] at hs
        have hk := buildViewM_eq_buildDomM ns k s a hs.1
        dsimp only [buildViewKidsM, buildDomListM, View.renderEach, StateT.run, bind, StateT.bind, pure, StateT.pure] at hk ⊢
        cases hbv : buildViewM (m := StateM (DomArena msg)) ns k s a with
        | mk pk a1 =>
            rw [hbv] at hk; dsimp only at hk; rw [← hk]
            cases happ : MonadDom.appendChild (m := StateM (DomArena msg)) parent pk.1 a1 with
            | mk _ a2 =>
                dsimp only
                have hrest := buildViewKidsM_eq_buildDomListM ns parent rest s a2 hs.2
                dsimp only [StateT.run] at hrest
                cases hbr : buildViewKidsM (m := StateM (DomArena msg)) ns parent rest s a2 with
                | mk ks a3 =>
                    simp only [happ, hbr] at hrest ⊢; rw [hrest]
end

theorem buildViewM_spec {σ msg : Type} (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (fuel : Nat)
    (hsafe : v.DirectRenderSafe s = true) (hpos : 0 < a.nextId)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ fuel) :
    let ((root, _), a') := (buildViewM (m := StateM (DomArena msg)) ns v s).run a
    a.nextId ≤ root.toNat ∧ root.toNat < a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
    (∀ m : Dom.Node, m.toNat < a.nextId → a'.get m = a.get m) ∧
    SubtreeInRange fuel a' a.nextId a'.nextId root ∧ readDomTree fuel a' root = specDom ns (View.render v s) ∧
    (∀ fcs, a'.get root ≠ .fragment fcs) := by
  have heq := buildViewM_eq_buildDomM ns v s a hsafe
  dsimp only [StateT.run] at heq ⊢
  have h1 := buildDomM_spec ns (View.render v s) a fuel hpos hbound hdep
  have h2 := fun fcs => buildDomM_not_fragment ns (View.render v s) a fuel fcs hpos hbound hdep
  cases hbv : buildViewM (m := StateM (DomArena msg)) ns v s a with
  | mk p a' =>
      rw [hbv] at heq; dsimp only at heq; dsimp only [StateT.run] at h1 h2; rw [← heq] at h1 h2
      exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2, h2⟩

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
            let a1 : DomArena msg := { nextId := a.nextId + 1, store := a.store, signals := a.signals }
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
               ElemClean_evalSpecAttrs (haClean.2.1 s), ⟨fun _ => rfl, rfl, rfl⟩,
               CleanDomChildren_mono (fun k hk => Or.elim hk (fun h => False.elim h) (fun h => ⟨⟨by omega, h.2⟩, by rw [hnodeNat]; omega⟩)) hCleanOut⟩,
              rfl, realNs, tag, st, mg, csNew, DomArena.get_set_self _ _ _,
              fun nm hnm => List.contains_iff_mem.2 hnm, hVstOut⟩
            · have hne : m ≠ node := node_ne_of_toNat_ne (by rw [hnodeNat]; omega)
              rw [← hOutEq]; rw [haOutFr m (by rw [ha1Next]; omega) hne]; rfl
    | .keyedList .., _, _, _, h, _, _, _ => False.elim h

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
              | fragment fcs =>
                  have hnf := (buildViewM_spec childNs k s a0 f (View.DirectRenderSafe_of_DomClean hkCl s) hpos (by rw [ha0Next]; omega) hkDep).2.2.2.2.2.2 fcs
                  rw [hbK] at hnf; exact False.elim (hnf hkG)
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
    | keyedList _ _ _ _ _ _ => exact False.elim hclean
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
            rcases hval with ⟨hcl, _, ns', tag', st, mg, domCs, hgetM, hmg, hksM⟩
            cases f with
            | zero => simp [CleanDomSubtree] at hcl
            | succ f' =>
                rcases hcl with ⟨hnodeMem, _, _, st0, mg0, domCs0, hnodeGet, hElClean, hElEq, hCleanCs⟩
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
                        hnodeOut, hElClean', hElEq',
                        CleanDomChildren_mono (fun k hk => ⟨(hSnew k hk).1.elim (fun h => h.elim) (fun h => h.elim (fun hs => .inl hs.1) (fun ha => .inr ⟨by omega, ha.2⟩)), (hSnew k hk).2⟩) hCleanOut⟩,
                       rfl, _, tag, st', mg', ks'.map VState.rootNode, hnodeOut, hmg', hVstOut⟩
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

private def alignStep {msg : Type} (oldPos : Std.HashMap String Nat) (oldRows : Array (Html msg))
    (oldMarks : Array USize) (oldSigs : Array (Array (String × String))) (fresh : Unit → Array (Html msg))
    (st : AlignedRows msg × Option (Array (Html msg))) (key : String) : AlignedRows msg × Option (Array (Html msg)) :=
  match oldPos[key]? with
  | some i => ({ rows := st.1.rows.push (oldRows.getD i default), marks := st.1.marks.push (oldMarks.getD i 0), sigs := st.1.sigs.push (oldSigs.getD i #[]) }, st.2)
  | none =>
      let rows := match st.2 with | some rs => rs | none => fresh ()
      ({ rows := st.1.rows.push (rows.getD st.1.rows.size default), marks := st.1.marks.push 0, sigs := st.1.sigs.push #[] }, some rows)

private theorem alignStep_sizes {msg : Type} (oldPos : Std.HashMap String Nat) (oldRows : Array (Html msg))
    (oldMarks : Array USize) (oldSigs : Array (Array (String × String))) (fresh : Unit → Array (Html msg)) :
    ∀ (ks : List String) (st : AlignedRows msg × Option (Array (Html msg))),
      st.1.marks.size = st.1.rows.size → st.1.sigs.size = st.1.rows.size →
      let res := (ks.foldl (alignStep oldPos oldRows oldMarks oldSigs fresh) st).1
      res.rows.size = st.1.rows.size + ks.length ∧ res.marks.size = res.rows.size ∧ res.sigs.size = res.rows.size
  | [], _, hm, hs => ⟨by simp, hm, hs⟩
  | k :: rest, st, hm, hs => by
      have h1 : (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.rows.size = st.1.rows.size + 1 ∧
          (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.marks.size = (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.rows.size ∧
          (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.sigs.size = (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.rows.size := by
        unfold alignStep; split <;> simp [hm, hs]
      have ih := alignStep_sizes oldPos oldRows oldMarks oldSigs fresh rest _ h1.2.1 h1.2.2
      exact ⟨by simp [List.foldl_cons, ih.1, h1.1]; omega, ih.2.1, ih.2.2⟩

private theorem alignStep_idx {msg : Type} (oldPos : Std.HashMap String Nat) (oldRows : Array (Html msg))
    (oldMarks : Array USize) (oldSigs : Array (Array (String × String))) (fresh : Unit → Array (Html msg)) :
    ∀ (ks : List String) (st : AlignedRows msg × Option (Array (Html msg))) (i : Nat) (hi : i < ks.length),
      st.1.marks.size = st.1.rows.size → st.1.sigs.size = st.1.rows.size →
      (∀ rs, st.2 = some rs → rs = fresh ()) →
      let out := (ks.foldl (alignStep oldPos oldRows oldMarks oldSigs fresh) st).1
      let idx := st.1.rows.size + i
      match oldPos[ks[i]]? with
      | some oi => out.rows[idx]? = some (oldRows.getD oi default) ∧ out.marks[idx]? = some (oldMarks.getD oi 0) ∧ out.sigs[idx]? = some (oldSigs.getD oi #[])
      | none => out.rows[idx]? = some ((fresh ()).getD idx default) ∧ out.marks[idx]? = some 0 ∧ out.sigs[idx]? = some #[] := by
  have hpres : ∀ (ks' : List String) (st' : AlignedRows msg × Option (Array (Html msg))) (j : Nat),
      st'.1.marks.size = st'.1.rows.size → st'.1.sigs.size = st'.1.rows.size → j < st'.1.rows.size →
      let out := (ks'.foldl (alignStep oldPos oldRows oldMarks oldSigs fresh) st').1
      out.rows[j]? = st'.1.rows[j]? ∧ out.marks[j]? = st'.1.marks[j]? ∧ out.sigs[j]? = st'.1.sigs[j]? := by
    intro ks'; induction ks' with
    | nil => intro _ _ _ _ _; exact ⟨rfl, rfl, rfl⟩
    | cons k' rest' ih' =>
        intro st' j hm hs hj
        have hstep := ih' (alignStep oldPos oldRows oldMarks oldSigs fresh st' k') j
          (by unfold alignStep; split <;> simp [hm]) (by unfold alignStep; split <;> simp [hs])
          (by unfold alignStep; split <;> simp <;> omega)
        refine ⟨hstep.1.trans ?_, hstep.2.1.trans ?_, hstep.2.2.trans ?_⟩
        · unfold alignStep; split <;> simp [Array.getElem?_push, Nat.ne_of_lt hj]
        · unfold alignStep; split <;> simp [Array.getElem?_push, hm, Nat.ne_of_lt hj]
        · unfold alignStep; split <;> simp [Array.getElem?_push, hs, Nat.ne_of_lt hj]
  intro ks; induction ks with
  | nil => intro _ _ hi; nomatch hi
  | cons k rest ih =>
      intro st i hi hm hs hfr
      cases i with
      | zero =>
          simp only [List.getElem_cons_zero, List.foldl_cons, Nat.add_zero]
          have hs' : (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.marks.size = (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.rows.size ∧
              (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.sigs.size = (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.rows.size := by
            unfold alignStep; split <;> simp [hm, hs]
          have hp := hpres rest (alignStep oldPos oldRows oldMarks oldSigs fresh st k) st.1.rows.size hs'.1 hs'.2 (by unfold alignStep; split <;> simp <;> omega)
          cases ho : oldPos[k]? with
          | some oi =>
              dsimp only [Array.getD] at hp ⊢
              simp only [ho, alignStep, Array.getD] at hp ⊢
              rw [hp.1, hp.2.1, hp.2.2]
              simp only [Array.getElem?_push, hm, hs, ↓reduceIte]; exact ⟨trivial, trivial, trivial⟩
          | none =>
              have hrs : (match st.2 with | some rs => rs | none => fresh ()) = fresh () := by
                cases hs2 : st.2 with | none => rfl | some rs => exact hfr rs hs2
              dsimp only [Array.getD] at hp ⊢
              simp only [ho, alignStep, Array.getD] at hp ⊢
              rw [hrs] at hp ⊢
              rw [hp.1, hp.2.1, hp.2.2]
              simp only [Array.getElem?_push, hm, hs, ↓reduceIte]; exact ⟨trivial, trivial, trivial⟩
      | succ i' =>
          have hs' : (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.rows.size = st.1.rows.size + 1 ∧
              (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.marks.size = (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.rows.size ∧
              (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.sigs.size = (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.rows.size ∧
              (∀ rs, (alignStep oldPos oldRows oldMarks oldSigs fresh st k).2 = some rs → rs = fresh ()) := by
            unfold alignStep; split
            · exact ⟨by simp, by simp [hm], by simp [hs], hfr⟩
            · refine ⟨by simp, by simp [hm], by simp [hs], fun rs hrs => ?_⟩
              cases hs2 : st.2 with | none => simp [hs2] at hrs; exact hrs.symm | some r => simp [hs2] at hrs; exact hrs ▸ hfr r hs2
          have hi' : i' < rest.length := Nat.lt_of_succ_lt_succ hi
          have hidx : st.1.rows.size + (i' + 1) = (alignStep oldPos oldRows oldMarks oldSigs fresh st k).1.rows.size + i' := by
            rw [hs'.1]; omega
          change match oldPos[rest[i']'hi']? with
            | some oi => (rest.foldl (alignStep oldPos oldRows oldMarks oldSigs fresh) (alignStep oldPos oldRows oldMarks oldSigs fresh st k)).1.rows[st.1.rows.size + (i' + 1)]? = _ ∧ _ ∧ _
            | none => (rest.foldl (alignStep oldPos oldRows oldMarks oldSigs fresh) (alignStep oldPos oldRows oldMarks oldSigs fresh st k)).1.rows[st.1.rows.size + (i' + 1)]? = _ ∧ _ ∧ _
          rw [hidx]
          exact ih (alignStep oldPos oldRows oldMarks oldSigs fresh st k) i' hi' hs'.2.1 hs'.2.2.1 hs'.2.2.2

private theorem forIn'_list_yield_foldl {α β γ : Type} (step : β × γ → α → β × γ)
    (F : α → MProd β γ → Id (ForInStep (MProd β γ)))
    (hF : ∀ k r, F k r = ForInStep.yield (let p := step (r.fst, r.snd) k; ⟨p.1, p.2⟩)) :
    ∀ (l : List α) (st : MProd β γ), (forIn' (m := Id) l st (fun k _ r => F k r)).fst = (l.foldl step (st.fst, st.snd)).1
  | [], _ => rfl
  | x :: xs, st => by
      rw [List.forIn'_cons, hF]
      exact forIn'_list_yield_foldl step F hF xs ⟨(step (st.fst, st.snd) x).1, (step (st.fst, st.snd) x).2⟩

theorem alignRows_spec {msg : Type} (keys : Array String) (oldPos : Std.HashMap String Nat)
    (oldRows : Array (Html msg)) (oldMarks : Array USize) (oldSigs : Array (Array (String × String)))
    (fresh : Unit → Array (Html msg)) :
    let out := alignRows keys oldPos oldRows oldMarks oldSigs fresh
    out.rows.size = keys.size ∧ out.marks.size = keys.size ∧ out.sigs.size = keys.size ∧
    ∀ (i : Nat) (hi : i < keys.size),
      match oldPos[keys[i]]? with
      | some oi => out.rows[i]? = some (oldRows.getD oi default) ∧ out.marks[i]? = some (oldMarks.getD oi 0) ∧ out.sigs[i]? = some (oldSigs.getD oi #[])
      | none => out.rows[i]? = some ((fresh ()).getD i default) ∧ out.marks[i]? = some 0 ∧ out.sigs[i]? = some #[] := by
  have heq : alignRows keys oldPos oldRows oldMarks oldSigs fresh =
      (keys.toList.foldl (alignStep oldPos oldRows oldMarks oldSigs fresh) ({}, none)).1 := by
    dsimp only [alignRows, Id.run]
    rw [← Array.forIn_toList]
    apply forIn'_list_yield_foldl
    intro key r; cases ho : oldPos[key]? <;> simp only [alignStep, ho, pure, bind] <;> rfl
  rw [heq]
  have hsz := alignStep_sizes oldPos oldRows oldMarks oldSigs fresh keys.toList ({}, none) rfl rfl
  refine ⟨by simpa using hsz.1, by rw [hsz.2.1]; simpa using hsz.1, by rw [hsz.2.2]; simpa using hsz.1, fun i hi => ?_⟩
  simpa using alignStep_idx oldPos oldRows oldMarks oldSigs fresh keys.toList ({}, none) i (by simpa using hi) rfl rfl (fun _ h => by cases h)

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

private theorem string_append_left_cancel {p a b : String} (h : p ++ a = p ++ b) : a = b :=
  String.ext (by have := congrArg String.toList h; simp_all)

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

theorem diffRowSigs_sound (rowSig : Nat → Array (String × String)) (inst : String)
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String)))
    (hmark : ∀ i, i < newMarks.size → newMarks[i]! ≠ 0 → oldMarks[i]? = some newMarks[i]! → rowSig i = oldSigs[i]?.getD #[]) :
    ∀ (i : Nat) (accSigs : Array (Array (String × String))) (accEmit : Array (String × String)),
      i ≤ newMarks.size → accSigs.size = i → (∀ k, k < i → accSigs[k]! = rowSig k) →
      let (outSigs, _) := diffRowSigs rowSig inst newMarks oldMarks oldSigs i accSigs accEmit
      outSigs.size = newMarks.size ∧ ∀ k, k < newMarks.size → outSigs[k]! = rowSig k := by
  intro i; induction hrem : newMarks.size - i generalizing i with
  | zero =>
      intro accSigs accEmit hiLe hsz hprev; have hge : ¬ i < newMarks.size := by omega
      dsimp only; rw [diffRowSigs.eq_1]; simp only [hge, ↓reduceDIte]; refine ⟨by omega, fun k hk => hprev k (by omega)⟩
  | succ _ ih =>
      intro accSigs accEmit hiLe hsz hprev; have hlt : i < newMarks.size := by omega
      dsimp only; rw [diffRowSigs.eq_1]; simp only [hlt, ↓reduceDIte]
      by_cases hskip : (newMarks[i] != 0 && oldMarks[i]? == some newMarks[i]) = true
      · simp only [hskip, ↓reduceIte]
        have hnz : newMarks[i]! ≠ 0 := by simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hskip; simpa [hlt] using hskip.1
        have hold : oldMarks[i]? = some newMarks[i]! := by simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hskip; simpa [hlt] using hskip.2
        have hsigEq : oldSigs[i]?.getD #[] = rowSig i := (hmark i hlt hnz hold).symm
        apply ih (i + 1) (by omega) (accSigs.push (oldSigs[i]?.getD #[])) accEmit (by omega) (by simp [hsz])
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
        apply ih (i + 1) (by omega) (accSigs.push (rowSig i)) _ (by omega) (by simp [hsz])
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
    (newMarks oldMarks : Array USize) (oldSigs : Array (Array (String × String))) (a : DomArena msg)
    (hmark : ∀ i, i < newMarks.size → newMarks[i]! ≠ 0 → oldMarks[i]? = some newMarks[i]! → rowSig i = oldSigs[i]?.getD #[]) :
    let res := (seedRowsM (m := StateM (DomArena msg)) inst rowSig newMarks oldMarks oldSigs).run a
    let d := diffRowSigs rowSig inst newMarks oldMarks oldSigs 0 #[] #[]
    res.1.size = newMarks.size ∧ (∀ k, k < newMarks.size → res.1[k]! = rowSig k) ∧
    res.2.nextId = a.nextId ∧ res.2.store = a.store ∧
    res.2.signals = d.2.toList.foldl (fun acc (nm, v) => setAssoc nm v acc) a.signals := by
  have hs := diffRowSigs_sound rowSig inst newMarks oldMarks oldSigs hmark 0 #[] #[] (Nat.zero_le _) rfl (fun _ h => nomatch h)
  have he := emitSignalsM_spec (diffRowSigs rowSig inst newMarks oldMarks oldSigs 0 #[] #[]).2.toList a
  dsimp only [seedRowsM, StateT.run, bind, StateT.bind, pure, StateT.pure] at he ⊢
  cases hd : diffRowSigs rowSig inst newMarks oldMarks oldSigs 0 #[] #[] with
  | mk newSigs toEmit =>
      rw [hd] at hs he; dsimp only at hs he
      cases hem : emitSignalsM (m := StateM (DomArena msg)) toEmit.toList a with
      | mk _ a' =>
          rw [hem] at he
          rcases Prod.mk.inj he with ⟨_, rfl⟩
          exact ⟨hs.1, hs.2, rfl, rfl, rfl⟩

theorem renderSig_resolved_spec {σ msg : Type} (ns : String) (get : σ → String)
    (s₁ s₂ : σ) (pre : String) (n : Nat) (a : DomArena msg) (f : Nat) (hbound : a.nextId + 1 < UInt32.size) :
    let (sigHtml, _) := View.renderSig (.dyn get : View σ msg) s₁ pre n
    let (root, aMid) := (buildDomM (m := StateM (DomArena msg)) ns sigHtml).run a
    let aOut := (MonadDom.setSignal (m := StateM (DomArena msg)) s!"{pre}#{n}" (get s₂) aMid).2
    readResolvedDomTree (f + 1) aOut root = specDom ns (View.render (.dyn get) s₂) ∧
    aOut.nextId = a.nextId + 1 ∧ ∀ m : Dom.Node, m.toNat < a.nextId → aOut.get m = a.get m := by
  let node := UInt32.ofNat a.nextId
  let sigNm := s!"{pre}#{n}"
  let realNs := if ns == "" && "span" == "svg" then Dom.svgNs else ns
  let a1 : DomArena msg := { nextId := a.nextId + 1, store := a.store, signals := a.signals }
  have haMid : (buildDomM (m := StateM (DomArena msg)) ns (.element "span" [.signalBind sigNm] [.text (get s₁)])).run a =
      (node, (applyAttrsM (m := StateM (DomArena msg)) node [.signalBind sigNm] (a1.set node (.element realNs "span" {} [] []))).2) := by
    dsimp only [buildDomM, StateT.run, bind, StateT.bind, pure, StateT.pure, MonadDom.createElement, DomArena.alloc]
    have hset : ({ nextId := a.nextId + 1, store := fun m => if (m == node) = true then ArenaEntry.element realNs "span" {} [] [] else a.store m, signals := a.signals } : DomArena msg) =
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

end Qed
