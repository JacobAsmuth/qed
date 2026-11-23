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
      · simp only [heq, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          bind, StateT.bind, pure, StateT.pure, readDomTree, DomArena.get_set_self, specDom, View.render, and_self]
      · simp only [bne_iff_ne.2 heq, ↓reduceIte, bind, StateT.bind, pure, StateT.pure,
          DomArena.modify, DomArena.get_set_self, DomArena.set_set, readDomTree, specDom, View.render, and_self]

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
        change Html.element tag (attrs.map (Attr.prefixSignal pfx)) (Html.prefixSignalsList pfx cs) = _
        rw [map_prefixSignal_of_clean pfx attrs hown hA, Html.prefixSignalsList_of_DomClean pfx hCs]

  theorem Html.prefixSignalsList_of_DomClean {msg : Type} (pfx : String) :
      ∀ {hs : List (Html msg)}, Html.DomCleanList hs = true → Html.prefixSignalsList pfx hs = hs
    | [], _ => rfl
    | c :: cs, hc => by
        simp only [Html.DomCleanList, Bool.and_eq_true] at hc
        change Html.prefixSignals pfx c :: Html.prefixSignalsList pfx cs = _
        rw [Html.prefixSignals_of_DomClean pfx hc.1, Html.prefixSignalsList_of_DomClean pfx hc.2]
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

section DynAttrs
variable {σ msg : Type}

private def noBind (xs : List (VAttr σ msg)) : Bool :=
  xs.all (fun | .bind _ | .dynOn _ _ => false | _ => true)

private def stepDynAttr (s : σ) (cur : SpecElemState msg) : VAttr σ msg → SpecElemState msg
  | .bind f => stepSpecAttr cur (f s)
  | .dynVal k g => stepSpecAttr cur (.attr k (g s))
  | .dynOn ev g => stepSpecAttr cur (.on ev (g s))
  | .stat _ => cur

private theorem applyDynAttrListM_fold (a : DomArena msg) (node : Dom.Node)
    (s : σ) (ns tag : String) (mg : List String) (cs : List Dom.Node) :
    ∀ (xs : List (VAttr σ msg)) (st : SpecElemState msg), noBind xs = true →
      applyDynAttrListM (m := StateM (DomArena msg)) node s xs (a.set node (.element ns tag st mg cs)) =
        ((), a.set node (.element ns tag (xs.foldl (stepDynAttr s) st) mg cs))
  | [], _, _ => rfl
  | .bind _ :: _, _, hnb | .dynOn _ _ :: _, _, hnb => by cases hnb
  | .stat _ :: rest, st, hnb => applyDynAttrListM_fold a node s ns tag mg cs rest st hnb
  | .dynVal k g :: rest, st, hnb => by
      dsimp only [applyDynAttrListM, bind, StateT.bind, List.foldl_cons, stepDynAttr]
      rw [applyAttrM_element]
      exact applyDynAttrListM_fold a node s ns tag mg cs rest (stepSpecAttr st (.attr k (g s))) hnb

private def AttrKeyEq : List (Attr msg) → List (Attr msg) → Prop
  | [], [] => True
  | x :: xs, y :: ys => x.key? = y.key? ∧ managedAttrName x = managedAttrName y ∧ AttrKeyEq xs ys
  | _, _ => False

private theorem filterMap_cls_eq_of_noBind (s₁ s₂ : σ) :
    ∀ (ys : List (VAttr σ msg)), noBind ys = true →
      (ys.map (VAttr.eval s₁)).filterMap (fun | .cls c => some c | _ => none) =
      (ys.map (VAttr.eval s₂)).filterMap (fun | .cls c => some c | _ => none)
  | [], _ => rfl
  | .bind _ :: _, hn | .dynOn _ _ :: _, hn => by cases hn
  | .dynVal _ _ :: rest, hn => filterMap_cls_eq_of_noBind s₁ s₂ rest hn
  | .stat a :: rest, hn => by
      cases a <;> simp only [List.map_cons, VAttr.eval, List.filterMap_cons,
        filterMap_cls_eq_of_noBind s₁ s₂ rest hn]

private theorem attrKeyEq_any (k : String) :
    ∀ {xs ys : List (Attr msg)}, AttrKeyEq xs ys → xs.any (·.key? == some k) = ys.any (·.key? == some k)
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨hk, _, htl⟩ => by simp only [List.any_cons, hk, attrKeyEq_any k htl]
  | [], _ :: _, h | _ :: _, [], h => False.elim h

private theorem attrKeyEq_dedup :
    ∀ {xs ys : List (Attr msg)}, AttrKeyEq xs ys → AttrKeyEq (dedupAttrs xs) (dedupAttrs ys)
  | [], [], _ => trivial
  | x :: xs, y :: ys, ⟨hk, hm, htl⟩ => by
      cases hx : x.key? with
      | none => simp only [dedupAttrs, hx, hk.symm.trans hx]; exact ⟨hk, hm, attrKeyEq_dedup htl⟩
      | some k =>
          simp only [dedupAttrs, hx, hk.symm.trans hx, attrKeyEq_any k htl]
          split; exact attrKeyEq_dedup htl; exact ⟨hk, hm, attrKeyEq_dedup htl⟩
  | [], _ :: _, h | _ :: _, [], h => False.elim h

private theorem attrKeyEq_filterMap :
    ∀ {xs ys : List (Attr msg)}, AttrKeyEq xs ys → ys.filterMap managedAttrName = xs.filterMap managedAttrName
  | [], [], _ => rfl
  | _ :: _, y :: _, ⟨_, hm, htl⟩ => by
      simp only [List.filterMap_cons, hm]; cases managedAttrName y <;> simp only [attrKeyEq_filterMap htl]
  | [], _ :: _, h | _ :: _, [], h => False.elim h

private theorem attrKeyEq_nonCls (s₁ s₂ : σ) :
    ∀ (ys : List (VAttr σ msg)), noBind ys = true →
      AttrKeyEq ((ys.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true))
                ((ys.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true))
  | [], _ => trivial
  | .bind _ :: _, hn | .dynOn _ _ :: _, hn => by cases hn
  | .dynVal _ _ :: rest, hn => ⟨rfl, rfl, attrKeyEq_nonCls s₁ s₂ rest hn⟩
  | .stat a :: rest, hn => by
      cases a <;> simp only [List.map_cons, VAttr.eval, List.filter_cons] <;>
        first | exact ⟨rfl, rfl, attrKeyEq_nonCls s₁ s₂ rest hn⟩
              | exact attrKeyEq_nonCls s₁ s₂ rest hn

private theorem managedNames_eq_of_noBind {s₁ s₂ : σ} {xs : List (VAttr σ msg)} (hnb : noBind xs = true) :
    (normalizeAttrs (xs.map (VAttr.eval s₂))).filterMap managedAttrName =
    (normalizeAttrs (xs.map (VAttr.eval s₁))).filterMap managedAttrName := by
  unfold normalizeAttrs; dsimp only; erw [← filterMap_cls_eq_of_noBind s₁ s₂ xs hnb]
  rw [List.filterMap_append, List.filterMap_append]
  erw [attrKeyEq_filterMap (attrKeyEq_dedup (attrKeyEq_nonCls s₁ s₂ xs hnb))]; rfl

private theorem normalKey_slotUpdate_iff {a b : Attr msg} {k : String}
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
                | .inr (.inr ⟨hnv, hnc, hEq⟩) =>
                    absurd (AttrSlot.attr.inj hEq).symm (by first | exact h hnv | exact h hnc)⟩
        | val | chk | click _ | input _ =>
            first | (have hnc : kx ≠ "checked" := fun h => by subst h; exact Bool.noConfusion hxN
                     simp [Attr.slotUpdate?, beq_iff_eq, hnc])
                  | (have hnv : kx ≠ "value" := fun h => by subst h; exact Bool.noConfusion hxN
                     simp [Attr.slotUpdate?, beq_iff_eq, hnv])
    | _ => simp [Attr.key?] at hxk
  exact (hslot hb hbN).2 ∘ (hslot ha haN).1

private theorem dedupAttrs_foldl_equiv :
    ∀ (xs : List (Attr msg)) (cur : SpecElemState msg),
      xs.all Attr.NormalKey = true →
      ElemStateEquiv ((dedupAttrs xs).foldl stepSpecAttr cur) (xs.foldl stepSpecAttr cur)
  | [], cur, _ => ElemStateEquiv.refl cur
  | x :: xs, cur, hn => by
      simp only [List.all_cons, Bool.and_eq_true] at hn
      cases hx : x.key? with
      | none => simp only [dedupAttrs, hx, List.foldl_cons]; exact dedupAttrs_foldl_equiv xs (stepSpecAttr cur x) hn.2
      | some k =>
          by_cases hany : xs.any (·.key? == some k) = true
          · simp only [dedupAttrs, hx, hany, ↓reduceIte, List.foldl_cons]
            rcases List.any_eq_true.1 hany with ⟨y, hy, hyk⟩
            intro sl; refine (dedupAttrs_foldl_equiv xs cur hn.2 sl).trans
              (foldl_stepSpecAttr_read sl xs cur (stepSpecAttr cur x) ?_)
            cases hxu : x.slotUpdate? sl with
            | some _ =>
                exact .inl ⟨y, hy, normalKey_slotUpdate_iff hx (beq_iff_eq.1 hyk) hn.1
                  ((List.all_eq_true.1 hn.2) y hy) sl (by rw [hxu]; rfl)⟩
            | none => exact .inr (by rw [read_stepSpecAttr, hxu]; rfl)
          · simp only [dedupAttrs, hx, hany, Bool.false_eq_true, ↓reduceIte, List.foldl_cons]
            exact dedupAttrs_foldl_equiv xs (stepSpecAttr cur x) hn.2

private theorem stepDynAttr_equiv (s : σ) :
    ∀ (xs : List (VAttr σ msg)) {s₁ s₂ : SpecElemState msg}, ElemStateEquiv s₁ s₂ →
      ElemStateEquiv (xs.foldl (stepDynAttr s) s₁) (xs.foldl (stepDynAttr s) s₂)
  | [], _, _, h => h
  | va :: xs, _, _, h =>
      stepDynAttr_equiv s xs (by cases va with | stat _ => exact h | _ => exact stepSpecAttr_equiv _ h)

private def lastDynSlot? (sl : AttrSlot) (s : σ) : List (VAttr σ msg) → Option (SlotVal msg)
  | [] => none
  | .dynVal k' g :: rest => (lastDynSlot? sl s rest).orElse (fun _ => (Attr.attr k' (g s)).slotUpdate? sl)
  | _ :: rest => lastDynSlot? sl s rest

private theorem stepDynAttr_read (sl : AttrSlot) (s : σ) :
    ∀ (xs : List (VAttr σ msg)) (st : SpecElemState msg), noBind xs = true →
      sl.read (xs.foldl (stepDynAttr s) st) = (lastDynSlot? sl s xs).getD (sl.read st)
  | [], _, _ => rfl
  | .bind _ :: _, _, hnb | .dynOn _ _ :: _, _, hnb => by cases hnb
  | .stat _ :: rest, st, hnb => stepDynAttr_read sl s rest st hnb
  | .dynVal k' g :: rest, st, hnb => by
      rw [List.foldl_cons, stepDynAttr, stepDynAttr_read sl s rest _ hnb, read_stepSpecAttr]
      dsimp only [lastDynSlot?, Option.orElse]; cases lastDynSlot? sl s rest <;> rfl

private theorem nonCls_read_pres (sl : AttrSlot) (s : σ) (k' : String)
    (hbn : ∀ (x : Attr msg), x.key? ≠ some k' →
      (match x with | .cls _ | .localCell .. => False | _ => True) → x.slotUpdate? sl = none) :
    ∀ (ys : List (VAttr σ msg)) (cur : SpecElemState msg),
      noBind ys = true → ownsChildren (ys.map (VAttr.eval s)) = false → lastDynSlot? sl s ys = none →
      (∀ w ∈ ys, (match w with | .stat a => a.key? != some k' | _ => true) = true) →
      sl.read (((ys.map (VAttr.eval s)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr cur) =
        sl.read cur
  | [], _, _, _, _, _ => rfl
  | .bind _ :: _, _, hnbw, _, _, _ | .dynOn _ _ :: _, _, hnbw, _, _, _ => by cases hnbw
  | .dynVal kw gw :: ws, cur, hnbw, hownw, hnw, hstw => by
      cases hrw : lastDynSlot? sl s ws with
      | some _ => simp only [lastDynSlot?, Option.orElse, hrw, reduceCtorEq] at hnw
      | none =>
          simp only [lastDynSlot?, Option.orElse, hrw] at hnw
          refine (nonCls_read_pres sl s k' hbn ws _ hnbw hownw hrw (fun u hu => hstw u (.tail _ hu))).trans ?_
          dsimp only [VAttr.eval]; rw [read_stepSpecAttr, hnw]; rfl
  | .stat b :: ws, cur, hnbw, hownw, hnw, hstw => by
      have hb : b.key? ≠ some k' := bne_iff_ne.1 (hstw (.stat b) (.head _))
      have hstR := fun u hu => hstw u (.tail _ hu)
      cases b <;> first
        | exact nonCls_read_pres sl s k' hbn ws cur hnbw hownw hnw hstR
        | (simp [ownsChildren, VAttr.eval] at hownw; done)
        | (refine (nonCls_read_pres sl s k' hbn ws _ hnbw hownw hnw hstR).trans ?_
           dsimp only [VAttr.eval]; rw [read_stepSpecAttr, hbn _ hb trivial]; rfl)

private theorem nonCls_read_last (sl : AttrSlot) (s : σ) :
    ∀ (xs : List (VAttr σ msg)) (st : SpecElemState msg) (v : SlotVal msg),
      noBind xs = true → dynValNoLaterStat xs = true → ownsChildren (xs.map (VAttr.eval s)) = false →
      lastDynSlot? sl s xs = some v →
      sl.read (((xs.map (VAttr.eval s)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st) = v
  | [], _, _, _, _, _, h => by cases h
  | .bind _ :: _, _, _, hnb, _, _, _ | .dynOn _ _ :: _, _, _, hnb, _, _, _ => by cases hnb
  | .stat a :: rest, _, v, hnb, hns, hown, hs => by
      cases a <;> first
        | (simp [ownsChildren, VAttr.eval] at hown; done)
        | exact nonCls_read_last sl s rest _ v hnb hns hown hs
  | .dynVal k' g :: rest, st, v, hnb, hns, hown, hs => by
      simp only [dynValNoLaterStat, Bool.and_eq_true, List.all_eq_true] at hns
      cases hr : lastDynSlot? sl s rest with
      | some v' =>
          simp only [lastDynSlot?, Option.orElse, hr, Option.some.injEq] at hs; subst hs
          exact nonCls_read_last sl s rest _ v' hnb hns.2 hown hr
      | none =>
          simp only [lastDynSlot?, Option.orElse, hr] at hs
          have hslKey : (sl = .val ∧ k' = "value") ∨ (∃ k, sl = .attr k ∧ k' = k) := by
            cases sl <;> simp only [Attr.slotUpdate?] at hs <;> first
              | (split at hs <;> first
                  | (rename_i h; simp only [Bool.and_eq_true, beq_iff_eq] at h
                     first | exact .inl ⟨rfl, h⟩ | exact .inr ⟨_, rfl, h.2⟩)
                  | cases hs)
              | cases hs
          have hbn : ∀ (x : Attr msg), x.key? ≠ some k' →
              (match x with | .cls _ | .localCell .. => False | _ => True) →
              x.slotUpdate? sl = none := fun x hx hok => by
            rcases hslKey with ⟨rfl, rfl⟩ | ⟨k, rfl, rfl⟩ <;> cases x <;>
              simp only [Attr.slotUpdate?] <;> first
              | exact False.elim hok | rfl
              | (rw [if_neg]; simp only [Bool.and_eq_true, beq_iff_eq]
                 first | (intro h; exact hx (congrArg some h))
                       | (intro h; exact hx (congrArg some h.2)))
          refine (nonCls_read_pres sl s k' hbn rest (stepSpecAttr st (.attr k' (g s)))
            hnb hown hr (fun w hw => hns.1 w hw)).trans ?_
          rw [read_stepSpecAttr, hs]; rfl

private theorem nonCls_read_none (sl : AttrSlot) (s₁ s₂ : σ) :
    ∀ (xs : List (VAttr σ msg)) (st₁ st₂ : SpecElemState msg),
      noBind xs = true → lastDynSlot? sl s₂ xs = none → sl.read st₁ = sl.read st₂ →
      sl.read (((xs.map (VAttr.eval s₁)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₁) =
      sl.read (((xs.map (VAttr.eval s₂)).filter (fun | .cls _ => false | _ => true)).foldl stepSpecAttr st₂)
  | [], _, _, _, _, h => h
  | .bind _ :: _, _, _, hnb, _, _ | .dynOn _ _ :: _, _, _, hnb, _, _ => by cases hnb
  | .stat a :: rest, _, _, hnb, hn, heq => by
      cases a <;> exact nonCls_read_none sl s₁ s₂ rest _ _ hnb hn
        (by first | exact heq | (rw [read_stepSpecAttr, read_stepSpecAttr, heq]; rfl))
  | .dynVal k' g :: rest, _, _, hnb, hn, heq => by
      cases hr : lastDynSlot? sl s₂ rest with
      | some _ => simp only [lastDynSlot?, Option.orElse, hr, reduceCtorEq] at hn
      | none =>
          simp only [lastDynSlot?, Option.orElse, hr] at hn
          have hn1 : (@Attr.attr msg k' (g s₁)).slotUpdate? sl = none := by
            cases sl <;> simp only [Attr.slotUpdate?] at hn ⊢ <;> split at hn <;> simp_all
          refine nonCls_read_none sl s₁ s₂ rest _ _ hnb hr ?_
          dsimp only [VAttr.eval]; rw [read_stepSpecAttr, read_stepSpecAttr, hn, hn1]; exact heq

private theorem anyBind_false_noBind (f : VAttr σ msg → Bool)
    (hf : ∀ x, f x = match x with | .bind _ | .dynOn _ _ => true | _ => false)
    (xs : List (VAttr σ msg)) (hn : ¬(xs.any f = true)) : noBind xs = true :=
  List.all_eq_true.2 fun x hx => by
    cases x with
    | bind _ | dynOn _ _ => exact False.elim (hn (List.any_eq_true.2 ⟨_, hx, hf _⟩))
    | stat _ | dynVal _ _ => rfl

private theorem stepDynAttr_foldl_clean (s₂ : σ) (mg : List String) :
    ∀ (xs : List (VAttr σ msg)) (cur : SpecElemState msg),
      noBind xs = true → (xs.map (VAttr.eval s₂)).all Attr.DomClean = true →
      (∀ k g, .dynVal k g ∈ xs → mg.contains k = true) → ElemClean cur mg →
      ElemClean (xs.foldl (stepDynAttr s₂) cur) mg
  | [], _, _, _, _, hc => hc
  | .bind _ :: _, _, hnb', _, _, _ | .dynOn _ _ :: _, _, hnb', _, _, _ => by cases hnb'
  | .stat _ :: rest, cur, hnb', hcl', hmk, hc =>
      stepDynAttr_foldl_clean s₂ mg rest cur hnb'
        (by simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hcl'; exact hcl'.2)
        (fun k g hm => hmk k g (.tail _ hm)) hc
  | .dynVal k g :: rest, cur, hnb', hcl', hmk, hc => by
      simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hcl'
      exact stepDynAttr_foldl_clean s₂ mg rest _ hnb' hcl'.2 (fun k g hm => hmk k g (.tail _ hm))
        ⟨stepSpecAttr_retains_managed cur (.attr k (g s₂)) mg (hmk k g (.head _)) hc.1,
         stepSpecAttr_preserves_clean cur (.attr k (g s₂)) hcl'.1 hc.2⟩

end DynAttrs

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
  · rcases ElemClean_applyAttrsM a node ns tag st mg cs (attrs.map (VAttr.eval s₂)) hElClean (hclean.2.1 s₂) with
      ⟨st', hget, heqv', hElClean'⟩
    have ⟨hnx, hne⟩ := applyAttrsM_preserves (a.set node (.element ns tag st mg cs)) node (attrs.map (VAttr.eval s₂))
    exact ⟨hnx, fun m hm => (hne m hm).trans (DomArena.get_set_ne _ _ hm),
      st', (normalizeAttrs (attrs.map (VAttr.eval s₂))).filterMap managedAttrName, hget, hElClean',
      heqv', fun _ hnm => List.contains_iff_mem.2 hnm⟩
  · rename_i hnotBind
    have hnb : noBind attrs = true := anyBind_false_noBind _ (fun x => by cases x <;> rfl) attrs hnotBind
    rw [congrArg Prod.snd (applyDynAttrListM_fold a node s₂ ns tag mg cs attrs st hnb)]
    let st' := attrs.foldl (stepDynAttr s₂) st
    have hmgEq := managedNames_eq_of_noBind (s₁ := s₁) (s₂ := s₂) hnb
    let nonCls (s : σ) := (attrs.map (VAttr.eval s)).filter (fun | .cls _ => false | _ => true)
    have hEl' : ElemClean st' mg := stepDynAttr_foldl_clean s₂ mg attrs st hnb (hclean.2.1 s₂) (fun k g hm => by
      have hmemN := mem_managed_of_key? (xs := nonCls s₁)
        (List.mem_filter.2 ⟨List.mem_map.2 ⟨VAttr.dynVal k g, hm, rfl⟩, rfl⟩) (a := .attr k (g s₁)) rfl
      rcases List.mem_filterMap.1 hmemN with ⟨b, hb, hbn⟩
      exact hmg k (List.mem_filterMap.2 ⟨b, List.mem_append_right _ hb, hbn⟩)) hElClean
    let base : SpecElemState msg :=
      (let cl := ((attrs.map (VAttr.eval s₁)).filterMap (fun | .cls c => some c | _ => none)).filter (· != "")
       if cl.isEmpty then [] else [Attr.cls (String.intercalate " " cl)]).foldl stepSpecAttr {}
    have hdd (s : σ) : ElemStateEquiv ((dedupAttrs (nonCls s)).foldl stepSpecAttr base)
        ((nonCls s).foldl stepSpecAttr base) :=
      dedupAttrs_foldl_equiv _ base
        (List.all_eq_true.2 fun a ha => (List.all_eq_true.1 (hclean.2.2.1 s)) a (List.mem_filter.1 ha).1)
    have hev (s : σ) : evalSpecAttrs (attrs.map (VAttr.eval s)) = (dedupAttrs (nonCls s)).foldl stepSpecAttr base := by
      simp only [evalSpecAttrs, normalizeAttrs, List.foldl_append]; dsimp only [base, nonCls]
      erw [filterMap_cls_eq_of_noBind s s₁ attrs hnb]; rfl
    have hstepEq := stepDynAttr_equiv s₂ attrs (heq.trans (hev s₁ ▸ hdd s₁))
    refine ⟨rfl, fun m hm => DomArena.get_set_ne _ _ hm, st', mg, DomArena.get_set_self _ _ _, hEl',
      fun sl => ?_, fun nm hnm => hmg nm (hmgEq ▸ hnm)⟩
    rw [hstepEq sl, stepDynAttr_read sl s₂ attrs _ hnb, hev s₂, hdd s₂ sl]
    cases hr : lastDynSlot? sl s₂ attrs with
    | some v => exact (nonCls_read_last sl s₂ attrs base v hnb hclean.2.2.2 (hclean.1 s₂) hr).symm
    | none => exact nonCls_read_none sl s₁ s₂ attrs base base hnb hr rfl

theorem array_push_step_inv {α : Type} {a : Array α} {i bound : Nat} {x : α} {f : (j : Nat) → j < bound → α}
    (hle : i < bound) (hsz : a.size = i)
    (hprev : ∀ j (hj : j < i), a[j]'(by omega) = f j (Nat.lt_trans hj hle)) (hcur : x = f i hle) :
    ∀ j (hj : j < i + 1), (a.push x)[j]'(by rw [Array.size_push, hsz]; omega) = f j (by omega) := fun j hj => by
  by_cases hji : j < i
  · simp only [Array.getElem_push_lt (by omega : j < a.size)]; exact hprev j hji
  · have : j = i := by omega
    subst j; simpa [hsz, hcur] using @Array.getElem_push_eq _ a x

end Qed
