import Qed.Proofs.Hydration.Dom
import Qed.Proofs.ViewPatch.VState

namespace Qed

/-! ### Fine-Grained `View` Hydration Simulation & End-to-End SSR → Hydrate → Patch -/

theorem View.textOf?_eq_render {σ msg : Type} (s : σ) :
    ∀ (v : View σ msg), v.textOf? s = (View.render v s).textOf?
  | .text _ | .dyn _ | .static _ | .dynNode _ | .memo _ | .element .. | .keyedList .. => rfl
  | .ifElse c y n => by
      cases hc : c s <;> simp [View.textOf?, View.render, hc, View.textOf?_eq_render s y, View.textOf?_eq_render s n]

theorem hasMoreViewText_eq_renderEach {σ msg : Type} (s : σ) :
    ∀ (ks : List (View σ msg)), hasMoreViewText s ks = hasMoreText (View.renderEach ks s)
  | [] => rfl
  | k :: rest => by
      dsimp only [hasMoreViewText, View.renderEach, hasMoreText]
      rw [View.textOf?_eq_render s k]
      cases h : (View.render k s).textOf? with
      | none => rfl
      | some str =>
          by_cases he : str = ""
          · subst he; exact hasMoreViewText_eq_renderEach s rest
          · simp

theorem hydrateViewM_of_textOf? {σ msg : Type} :
    ∀ {v : View σ msg} {s : σ} {str : String},
      v.textOf? s = some str → ∀ (kn : Dom.Node) (a : DomArena msg),
        let (vst, a') := (hydrateViewM (m := StateM (DomArena msg)) v s kn).run a
        a' = a ∧ vst.rootNode = kn ∧ ∀ aAny : DomArena msg, VStateMatches v s aAny kn vst
  | .text _, _, _, _, kn, a => ⟨rfl, rfl, fun _ => rfl⟩
  | .dyn _, _, _, _, kn, a => ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
  | .static (.text _), _, _, _, kn, a => ⟨rfl, rfl, fun _ => rfl⟩
  | .static (.element ..), _, _, h, _, _ => by simp [View.textOf?, Html.textOf?] at h
  | .dynNode get, s, _, h, kn, a => by
      simp only [View.textOf?] at h
      have hg : get s = .text _ := textOf_eq_some_iff.1 h
      simp [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, hg, hydrateDomM, VState.rootNode, VStateMatches]
  | .memo sm, s, _, h, kn, a => by
      simp only [View.textOf?] at h
      have hm : sm.eval s = .text _ := textOf_eq_some_iff.1 h
      simp [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, hm, hydrateDomM, VState.rootNode, VStateMatches]
  | .ifElse c y n, s, str, h, kn, a => by
      simp only [View.textOf?] at h
      cases hc : c s <;> simp only [hc, ↓reduceIte, Bool.false_eq_true] at h
      · have ih := hydrateViewM_of_textOf? h kn a
        dsimp only [StateT.run] at ih
        cases hy : hydrateViewM (m := StateM (DomArena msg)) n s kn a with
        | mk vst' a' =>
            rw [hy] at ih; dsimp only at ih
            simp [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, hc, hy, VState.rootNode, VStateMatches, ih.1, ih.2.1, ih.2.2]
      · have ih := hydrateViewM_of_textOf? h kn a
        dsimp only [StateT.run] at ih
        cases hy : hydrateViewM (m := StateM (DomArena msg)) y s kn a with
        | mk vst' a' =>
            rw [hy] at ih; dsimp only at ih
            simp [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, hc, hy, VState.rootNode, VStateMatches, ih.1, ih.2.1, ih.2.2]
  | .element .., _, _, h, _, _ | .keyedList .., _, _, h, _, _ => by simp [View.textOf?] at h

private theorem DomArena.modify_withSignals {msg : Type} (nxt : Nat)
    (st : Dom.Node → ArenaEntry msg) (s₁ s₂ : List (String × String)) (e₁ e₂ : List (String × msg))
    (t₁ t₂ : Array (ArenaTmpl msg)) (r₁ r₂ : Array (Nat → Nat → Option msg))
    (n : Dom.Node) (f : ArenaEntry msg → ArenaEntry msg) :
    DomArena.modify ⟨nxt, st, s₁, e₁, t₁, r₁⟩ n f = { DomArena.modify ⟨nxt, st, s₂, e₂, t₂, r₂⟩ n f with signals := s₁, sigEvents := e₁, tmpls := t₁, rowEvs := r₁ } := by
  simp only [DomArena.modify, DomArena.get, DomArena.set]

private theorem hydrateTextSlotM_withSignals {msg : Type} (sigs : List (String × String)) (evs : List (String × msg))
    (tmpls : Array (ArenaTmpl msg)) (rowEvs : Array (Nat → Nat → Option msg))
    (parent : Dom.Node) (index : UInt32) (inRun : Bool) (s : String) (more : Unit → Bool) (a : DomArena msg) :
    hydrateTextSlotM (m := StateM (DomArena msg)) parent index inRun s more { a with signals := sigs, sigEvents := evs, tmpls, rowEvs } =
      ((hydrateTextSlotM (m := StateM (DomArena msg)) parent index inRun s more a).1,
       { (hydrateTextSlotM (m := StateM (DomArena msg)) parent index inRun s more a).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs }) := by
  dsimp only [hydrateTextSlotM]
  split
  · simp only [bind, StateT.bind, pure, StateT.pure, DomArena.alloc, DomArena.modifyChildren]
    refine Prod.ext rfl ?_; dsimp only; apply DomArena.modify_withSignals
  · split
    · simp only [bind, StateT.bind, pure, StateT.pure, DomArena.alloc, DomArena.modifyChildren]
      refine Prod.ext rfl ?_; dsimp only; apply DomArena.modify_withSignals
    · simp only [bind, StateT.bind, pure]
      have hg : DomArena.get { a with signals := sigs, sigEvents := evs, tmpls, rowEvs } parent = DomArena.get a parent := rfl
      rw [hg]
      cases more ()
      · rfl
      · simp only [↓reduceIte, bind, StateT.bind, pure, StateT.pure]
        refine Prod.ext rfl ?_; dsimp only; apply DomArena.modify_withSignals

private theorem htmlDepth_mem_le_h {msg : Type} {c : Html msg} {cs : List (Html msg)} (hc : c ∈ cs) :
    htmlDepth c ≤ htmlListDepth cs := by
  induction cs with
  | nil => cases hc
  | cons _ _ ih =>
      simp only [htmlListDepth]
      cases hc with
      | head => exact Nat.le_max_left _ _
      | tail _ h => exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

private theorem hydrateDomKidsM_withSignals_of {msg : Type} (sigs : List (String × String)) (evs : List (String × msg))
    (tmpls : Array (ArenaTmpl msg)) (rowEvs : Array (Nat → Nat → Option msg))
    (node : Dom.Node) (cs : List (Html msg))
    (hSub : ∀ c ∈ cs, ∀ (cn : Dom.Node) (a : DomArena msg),
      (hydrateDomM (m := StateM (DomArena msg)) c cn { a with signals := sigs, sigEvents := evs, tmpls, rowEvs }).2 =
        { (hydrateDomM (m := StateM (DomArena msg)) c cn a).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs }) :
    ∀ (i : UInt32) (inRun : Bool) (a : DomArena msg),
      (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs { a with signals := sigs, sigEvents := evs, tmpls, rowEvs }).2 =
        { (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs a).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs } := by
  induction cs with
  | nil => intro _ _ _; rfl
  | cons c rest ih =>
      intro i inRun a
      dsimp only [hydrateDomKidsM, bind, StateT.bind, pure, StateT.pure]
      cases hc : c.textOf? with
      | none =>
        dsimp only [bind, StateT.bind, pure, StateT.pure]
        have hg : ({ nextId := a.nextId, store := a.store, signals := sigs, sigEvents := evs, tmpls, rowEvs } : DomArena msg).get node = a.get node := rfl
        rw [hg]
        have hchild : ∀ cn : Dom.Node,
            (match hydrateDomM (m := StateM (DomArena msg)) c cn { a with signals := sigs, sigEvents := evs, tmpls, rowEvs } with
            | (_, s) => hydrateDomKidsM (m := StateM (DomArena msg)) node (i + 1) false rest s).snd =
            { (match hydrateDomM (m := StateM (DomArena msg)) c cn a with
              | (_, s) => hydrateDomKidsM (m := StateM (DomArena msg)) node (i + 1) false rest s).snd with signals := sigs, sigEvents := evs, tmpls, rowEvs } := by
          intro cn
          have hd := hSub c (.head _) cn a
          cases hd1 : hydrateDomM (m := StateM (DomArena msg)) c cn { a with signals := sigs, sigEvents := evs, tmpls, rowEvs } with
          | mk _ a1 => cases hd2 : hydrateDomM (m := StateM (DomArena msg)) c cn a with
            | mk _ a2 => rw [hd1, hd2] at hd; dsimp only at hd; rw [hd]; exact ih (fun x hx => hSub x (.tail _ hx)) (i + 1) false a2
        cases a.get node <;> dsimp only <;> exact hchild _
      | some str =>
        dsimp only [bind, StateT.bind, pure, StateT.pure]
        have hs := hydrateTextSlotM_withSignals sigs evs tmpls rowEvs node i inRun str (fun () => hasMoreText rest) a
        cases hs1 : hydrateTextSlotM (m := StateM (DomArena msg)) node i inRun str (fun () => hasMoreText rest) { a with signals := sigs, sigEvents := evs, tmpls, rowEvs } with
        | mk r1 a1 =>
            cases hs2 : hydrateTextSlotM (m := StateM (DomArena msg)) node i inRun str (fun () => hasMoreText rest) a with
            | mk r2 a2 =>
                rw [hs1, hs2] at hs; dsimp only at hs
                rcases Prod.mk.inj hs with ⟨hreq, haeq⟩
                rw [hreq, haeq]
                exact ih (fun x hx => hSub x (.tail _ hx)) (i + 1) r2.2 a2

private theorem hydrateDomM_withSignals_aux {msg : Type} (sigs : List (String × String)) (evs : List (String × msg))
    (tmpls : Array (ArenaTmpl msg)) (rowEvs : Array (Nat → Nat → Option msg)) :
    ∀ (f : Nat) (h : Html msg) (node : Dom.Node) (a : DomArena msg), htmlDepth h ≤ f →
      (hydrateDomM (m := StateM (DomArena msg)) h node { a with signals := sigs, sigEvents := evs, tmpls, rowEvs }).2 =
        { (hydrateDomM (m := StateM (DomArena msg)) h node a).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs }
  | 0, h, _, _, hdep => by cases h <;> { simp only [htmlDepth] at hdep; omega }
  | _ + 1, .text _, _, _, _ => rfl
  | f + 1, .element _ attrs cs, node, a, hdep => by
      simp only [htmlDepth] at hdep
      dsimp only [hydrateDomM, bind, StateT.bind, pure, StateT.pure, DomArena.modifyElemState,
        DomArena.modify, DomArena.get, DomArena.set]
      have hstep : ∀ (nxt : Nat) (st : Dom.Node → ArenaEntry msg),
          (match applyAttrsM (m := StateM (DomArena msg)) node attrs ⟨nxt, st, sigs, evs, tmpls, rowEvs⟩ with
          | (_, s) => (if (!ownsChildren attrs) = true then hydrateDomKidsM (m := StateM (DomArena msg)) node 0 false cs else StateT.pure PUnit.unit) s).snd =
          { (match applyAttrsM (m := StateM (DomArena msg)) node attrs ⟨nxt, st, a.signals, a.sigEvents, a.tmpls, a.rowEvs⟩ with
            | (_, s) => (if (!ownsChildren attrs) = true then hydrateDomKidsM (m := StateM (DomArena msg)) node 0 false cs else StateT.pure PUnit.unit) s).snd with signals := sigs, sigEvents := evs, tmpls, rowEvs } := by
        intro nxt st
        have ha := applyAttrsM_withSignals sigs evs tmpls rowEvs node attrs ⟨nxt, st, a.signals, a.sigEvents, a.tmpls, a.rowEvs⟩
        dsimp only [StateT.run] at ha
        cases ha1 : applyAttrsM (m := StateM (DomArena msg)) node attrs ⟨nxt, st, sigs, evs, tmpls, rowEvs⟩ with
        | mk _ s1 =>
            cases ha2 : applyAttrsM (m := StateM (DomArena msg)) node attrs ⟨nxt, st, a.signals, a.sigEvents, a.tmpls, a.rowEvs⟩ with
            | mk _ s2 =>
                rw [ha1, ha2] at ha; dsimp only at ha; rw [ha]
                cases ownsChildren attrs
                · exact hydrateDomKidsM_withSignals_of sigs evs tmpls rowEvs node cs
                    (fun c hc cn a' => hydrateDomM_withSignals_aux sigs evs tmpls rowEvs f c cn a'
                      (Nat.le_trans (htmlDepth_mem_le_h hc) (by omega))) 0 false s2
                · rfl
      apply hstep

theorem hydrateDomM_withSignals {msg : Type} (sigs : List (String × String)) (evs : List (String × msg))
    (tmpls : Array (ArenaTmpl msg)) (rowEvs : Array (Nat → Nat → Option msg))
    (h : Html msg) (node : Dom.Node) (a : DomArena msg) :
    (hydrateDomM (m := StateM (DomArena msg)) h node { a with signals := sigs, sigEvents := evs, tmpls, rowEvs }).2 =
      { (hydrateDomM (m := StateM (DomArena msg)) h node a).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs } :=
  hydrateDomM_withSignals_aux sigs evs tmpls rowEvs (htmlDepth h) h node a (Nat.le_refl _)

theorem hydrateDomKidsM_withSignals {msg : Type} (sigs : List (String × String)) (evs : List (String × msg))
    (tmpls : Array (ArenaTmpl msg)) (rowEvs : Array (Nat → Nat → Option msg))
    (node : Dom.Node) (i : UInt32) (inRun : Bool) (cs : List (Html msg)) (a : DomArena msg) :
    (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs { a with signals := sigs, sigEvents := evs, tmpls, rowEvs }).2 =
      { (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs a).2 with signals := sigs, sigEvents := evs, tmpls, rowEvs } :=
  hydrateDomKidsM_withSignals_of sigs evs tmpls rowEvs node cs
    (fun c _ cn a' => hydrateDomM_withSignals sigs evs tmpls rowEvs c cn a') i inRun a

theorem hydrateDomKidsM_sameDom {msg : Type} (node : Dom.Node) (i : UInt32) (inRun : Bool)
    (cs : List (Html msg)) {a₁ a₂ : DomArena msg} (hs : a₁.SameDom a₂) :
    (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs a₁).2.SameDom
      (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs a₂).2 := by
  have heq : a₁ = { a₂ with signals := a₁.signals, sigEvents := a₁.sigEvents, tmpls := a₁.tmpls, rowEvs := a₁.rowEvs } :=
    DomArena.ext hs.1 hs.2 rfl rfl rfl rfl
  rw [heq, hydrateDomKidsM_withSignals]; exact ⟨rfl, rfl⟩

theorem hydrateListRowsM_eq_hydrateDomKidsM {msg : Type} (node : Dom.Node) :
    ∀ (i : UInt32) (rs : List (Html msg)), (∀ r ∈ rs, r.textOf? = none) →
      ∀ (a : DomArena msg),
        ((hydrateListRowsM (m := StateM (DomArena msg)) node i rs).run a).2 =
        ((hydrateDomKidsM (m := StateM (DomArena msg)) node i false rs).run a).2
  | _, [], _, _ => rfl
  | i, r :: rs, hr, a => by
      dsimp only [hydrateListRowsM, hydrateDomKidsM, StateT.run]
      rw [hr r (.head _)]
      dsimp only [bind, StateT.bind, pure, StateT.pure]
      cases hydrateDomM (m := StateM (DomArena msg)) r (MonadDom.childAt (m := StateM (DomArena msg)) node i a).1 a with
      | mk _ a2 => exact hydrateListRowsM_eq_hydrateDomKidsM node (i + 1) rs (fun x hx => hr x (.tail _ hx)) a2

private theorem view_sizeOf_pos_h {σ msg : Type} (v : View σ msg) : 0 < sizeOf v := by
  cases v <;> simp only [View.text.sizeOf_spec, View.dyn.sizeOf_spec, View.static.sizeOf_spec,
    View.dynNode.sizeOf_spec, View.memo.sizeOf_spec, View.ifElse.sizeOf_spec,
    View.element.sizeOf_spec, View.keyedList.sizeOf_spec] <;> omega

private theorem hydrateViewKidsM_eq_hydrateDomKidsM_of {σ msg : Type}
    (ks : List (View σ msg)) (node : Dom.Node) (s : σ)
    (hView : ∀ k ∈ ks, View.DomClean k → ∀ (cn : Dom.Node) (a : DomArena msg),
      ((hydrateViewM (m := StateM (DomArena msg)) k s cn).run a).2.SameDom
        ((hydrateDomM (m := StateM (DomArena msg)) (View.render k s) cn).run a).2) :
    View.DomCleanEach ks → ∀ (i : UInt32) (inRun : Bool) (a : DomArena msg),
      ((hydrateViewKidsM (m := StateM (DomArena msg)) node s i inRun ks).run a).2.SameDom
        ((hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun (View.renderEach ks s)).run a).2 := by
  induction ks with
  | nil => intro _ _ _ a; exact DomArena.SameDom.refl a
  | cons k rest ih =>
      intro ⟨hk, hrest⟩ i inRun a
      dsimp only [hydrateViewKidsM, View.renderEach, hydrateDomKidsM, StateT.run]
      rw [← View.textOf?_eq_render s k]
      cases htxt : k.textOf? s with
      | some str =>
          dsimp only [bind, StateT.bind, pure, StateT.pure]
          simp only [hasMoreViewText_eq_renderEach]
          cases hsl : hydrateTextSlotM (m := StateM (DomArena msg)) node i inRun str
              (fun () => hasMoreText (View.renderEach rest s)) a with
          | mk slot a1 =>
              dsimp only
              have hm := hydrateViewM_of_textOf? htxt slot.1 a1
              dsimp only [StateT.run] at hm
              cases hvm : hydrateViewM (m := StateM (DomArena msg)) k s slot.1 a1 with
              | mk kst a2 =>
                  rw [hvm] at hm; dsimp only at hm
                  rw [hm.1]
                  have hkEq := ih (fun x hx => hView x (.tail _ hx)) hrest (i + 1) slot.2 a1
                  dsimp only [StateT.run] at hkEq
                  cases hydrateViewKidsM (m := StateM (DomArena msg)) node s (i + 1) slot.2 rest a1; exact hkEq
      | none =>
          dsimp only [bind, StateT.bind, pure, StateT.pure]
          suffices hCn : ∀ cn : Dom.Node,
              (match hydrateViewM (m := StateM (DomArena msg)) k s cn a with
              | (kst, a2) => match hydrateViewKidsM (m := StateM (DomArena msg)) node s (i + 1) false rest a2 with
                | (r, a3) => (kst :: r, a3)).snd.SameDom
              (match hydrateDomM (m := StateM (DomArena msg)) (k.render s) cn a with
              | (_, ad) => hydrateDomKidsM (m := StateM (DomArena msg)) node (i + 1) false (View.renderEach rest s) ad).snd from
            hCn _
          intro cn
          have heq := hView k (.head _) hk cn a
          dsimp only [StateT.run] at heq
          cases hvm : hydrateViewM (m := StateM (DomArena msg)) k s cn a with
          | mk kst a2 =>
              cases hdm : hydrateDomM (m := StateM (DomArena msg)) (k.render s) cn a with
              | mk _ ad =>
                  rw [hvm, hdm] at heq; dsimp only at heq ⊢
                  have hkEq := ih (fun x hx => hView x (.tail _ hx)) hrest (i + 1) false a2
                  dsimp only [StateT.run] at hkEq
                  cases hkRun : hydrateViewKidsM (m := StateM (DomArena msg)) node s (i + 1) false rest a2 with
                  | mk _ a3 =>
                      rw [hkRun] at hkEq; exact hkEq.trans (hydrateDomKidsM_sameDom node (i + 1) false (View.renderEach rest s) heq)

private theorem hydrateViewM_eq_hydrateDomM_aux {σ msg : Type} :
    ∀ (n : Nat) {v : View σ msg}, sizeOf v ≤ n → View.DomClean v → ∀ (s : σ) (node : Dom.Node) (a : DomArena msg),
      ((hydrateViewM (m := StateM (DomArena msg)) v s node).run a).2.SameDom
        ((hydrateDomM (m := StateM (DomArena msg)) (View.render v s) node).run a).2
  | 0, v, hsz, _, _, _, _ => absurd (Nat.lt_of_lt_of_le (view_sizeOf_pos_h v) hsz) (Nat.lt_irrefl 0)
  | _ + 1, .text _, _, _, _, _, a | _ + 1, .dyn _, _, _, _, _, a => DomArena.SameDom.refl a
  | _ + 1, .static (.text _), _, _, _, _, _ | _ + 1, .static (.element ..), _, _, _, _, _ => by
      dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
      cases hydrateDomM (m := StateM (DomArena msg)) _ _ _; exact DomArena.SameDom.refl _
  | _ + 1, .dynNode get, _, _, s, node, a => by
      dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
      cases hydrateDomM (m := StateM (DomArena msg)) (get s) node a; exact DomArena.SameDom.refl _
  | _ + 1, .memo sm, _, _, s, node, a => by
      dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
      cases hydrateDomM (m := StateM (DomArena msg)) (sm.eval s) node a; exact DomArena.SameDom.refl _
  | n + 1, .ifElse c y no, hsz, ⟨hy, hn⟩, s, node, a => by
      simp only [View.ifElse.sizeOf_spec] at hsz
      cases hcs : c s
      · have h := hydrateViewM_eq_hydrateDomM_aux n (by omega) hn s node a
        dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at h ⊢
        rw [hcs]
        cases hydrateViewM (m := StateM (DomArena msg)) no s node a; exact h
      · have h := hydrateViewM_eq_hydrateDomM_aux n (by omega) hy s node a
        dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at h ⊢
        rw [hcs]
        cases hydrateViewM (m := StateM (DomArena msg)) y s node a; exact h
  | n + 1, .element tag attrs kids, hsz, ⟨ha, hks⟩, s, node, a => by
      dsimp only [hydrateViewM, View.render, hydrateDomM, StateT.run, bind, StateT.bind, pure, StateT.pure]
      rw [ha.1 s, Bool.not_false, if_pos rfl]
      cases applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s))
          (a.modifyElemState node fun st => { st with clicks := [], inputs := [] }) with
      | mk _ a1 =>
          have h := hydrateViewKidsM_eq_hydrateDomKidsM_of kids node s
            (fun k hk hkCl cn a' => hydrateViewM_eq_hydrateDomM_aux n
              (by have := List.sizeOf_lt_of_mem hk; simp only [View.element.sizeOf_spec] at hsz; omega) hkCl s cn a')
            hks 0 false a1
          dsimp only [StateT.run] at h
          cases hydrateViewKidsM (m := StateM (DomArena msg)) node s 0 false kids a1; exact h
  | _ + 1, .keyedList _ _ _ _ _ _ _ (some _), _, h, _, _, _ => False.elim h
  | _ + 1, .keyedList tag attrs keys marks rowSig rowEv rowsHtml none, _, ⟨ha, hrows⟩, s, node, a => by
      dsimp only [hydrateViewM, View.render, hydrateDomM, StateT.run, bind, StateT.bind, pure, StateT.pure]
      rw [ha.1 s, Bool.not_false, if_pos rfl]
      cases applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s))
          (a.modifyElemState node fun st => { st with clicks := [], inputs := [] }) with
      | mk _ a1 =>
          dsimp only
          cases hseed : seedRowsM (m := StateM (DomArena msg)) s!"§{node}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a1 with
          | mk _ a2 =>
              dsimp only
              have hsd : a2.SameDom a1 := by
                have h := seedRowsM_sameDom s!"§{node}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a1
                dsimp only [StateT.run] at h; rw [hseed] at h; exact h
              rw [Html.map_prefixSignals_of_DomCleanList _ (hrows.2.1 s)]
              have hlist := hydrateListRowsM_eq_hydrateDomKidsM node 0 (rowsHtml s) (hrows.2.2.1 s) a2
              dsimp only [StateT.run] at hlist
              cases hl : hydrateListRowsM (m := StateM (DomArena msg)) node 0 (rowsHtml s) a2 with
              | mk _ a3 =>
                  rw [hl] at hlist; dsimp only at hlist ⊢; rw [hlist]
                  exact hydrateDomKidsM_sameDom node 0 false (rowsHtml s) hsd

theorem hydrateViewM_eq_hydrateDomM {σ msg : Type} {v : View σ msg} (hcl : View.DomClean v)
    (s : σ) (node : Dom.Node) (a : DomArena msg) :
    ((hydrateViewM (m := StateM (DomArena msg)) v s node).run a).2.SameDom
      ((hydrateDomM (m := StateM (DomArena msg)) (View.render v s) node).run a).2 :=
  hydrateViewM_eq_hydrateDomM_aux (sizeOf v) (Nat.le_refl _) hcl s node a

theorem hydrateViewKidsM_eq_hydrateDomKidsM {σ msg : Type} {ks : List (View σ msg)} (hcl : View.DomCleanEach ks)
    (node : Dom.Node) (s : σ) (i : UInt32) (inRun : Bool) (a : DomArena msg) :
    ((hydrateViewKidsM (m := StateM (DomArena msg)) node s i inRun ks).run a).2.SameDom
      ((hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun (View.renderEach ks s)).run a).2 :=
  hydrateViewKidsM_eq_hydrateDomKidsM_of ks node s (fun _ _ hkCl cn a' => hydrateViewM_eq_hydrateDomM hkCl s cn a') hcl i inRun a

def ViewHydrateSpecAt {msg : Type} (f : Nat) : Prop :=
  ∀ {σ : Type} (ns : String) (v : View σ msg) (s : σ) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat),
    View.DomClean v →
    a.nextId + htmlNodeCount (View.render v s) < UInt32.size →
    htmlDepth (View.render v s) ≤ f + 1 →
    HydratableDom (f + 1) ns (View.render v s) a lo hi root →
    let (vst, aOut) := (hydrateViewM (m := StateM (DomArena msg)) v s root).run a
    vst.rootNode = root ∧
    a.nextId ≤ aOut.nextId ∧
    aOut.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
    (∀ m : Dom.Node, (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    VStateValid (f + 1) ns v s aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) vst ∧
    DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns (View.render v s))

private theorem htmlDepth_pos {msg : Type} : ∀ h : Html msg, 1 ≤ htmlDepth h
  | .text _ | .element _ _ _ => by simp [htmlDepth]

private theorem View.renderEach_length {σ msg : Type} (s : σ) :
    ∀ ks : List (View σ msg), (View.renderEach ks s).length = ks.length
  | [] => rfl
  | _ :: rest => by simp [View.renderEach, View.renderEach_length s rest]

private theorem viewKidsMatches_step {σ msg : Type} (f : Nat)
    (hViewDom : ∀ f' < f, @ViewHydrateSpecAt msg f') :
    ∀ (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
      (ks : List (View σ msg)) (s : σ) (inTextRun : Bool) (pre domCs : List Dom.Node) (lo hi : Nat) (a : DomArena msg),
      View.DomCleanEach ks →
      pre.length + ks.length < UInt32.size →
      a.nextId + htmlListNodeCount (View.renderEach ks s) < UInt32.size →
      htmlListDepth (View.renderEach ks s) ≤ f →
      parent.toNat < lo →
      (∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet f a Sx x) →
      a.get parent = .element pns ptag pst pmg (pre ++ domCs) →
      HydratableDomList f childNs
        (if inTextRun then dropCurrentTextRun (View.renderEach ks s) else coalesceTextRun (View.renderEach ks s))
        a lo hi domCs →
      let (kstates, aOut) := (hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pre.length) inTextRun ks).run a
      aOut.get parent = .element pns ptag pst pmg (pre ++ kstates.map VState.rootNode) ∧
      VStateKidsMatches ks s aOut (kstates.map VState.rootNode) kstates := by
  intro childNs parent pns ptag pst pmg ks
  induction ks with
  | nil =>
      intro s inTextRun pre domCs _ _ _ _ _ _ _ _ _ hpar hdom
      have hdomNil : domCs = [] := by
        cases inTextRun <;> simp [View.renderEach, coalesceTextRun, dropCurrentTextRun] at hdom <;> cases domCs with
        | nil => rfl
        | cons _ _ => exact False.elim hdom
      subst hdomNil
      dsimp only [hydrateViewKidsM, StateT.run, pure, StateT.pure]
      exact ⟨hpar, trivial⟩
  | cons k rest ih =>
      intro s inTextRun pre domCs lo hi a ⟨hkCl, hrestCl⟩ hlen hbound hdep hparLo hpreSub hpar hdom
      rcases HydratableDomList_bounds f childNs _ a lo hi domCs hdom with ⟨hloHi, hhiNext⟩
      have hposF : 1 ≤ f := Nat.le_trans (htmlListDepth_cons_pos (View.render k s) (View.renderEach rest s)) hdep
      have huIdxNext : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) := by
        simp only [List.length_cons] at hlen
        exact uint32_ofNat_succ pre.length (by omega)
      have hdisjDom : ∀ r ∈ domCs, r ∉ pre := by
        intro r hr hmem
        have hlt := HydratableDomList_nodes_lt f childNs _ a lo hi domCs hdom r hr
        rcases hpreSub r hmem with ⟨Sx, hSx, hsub⟩
        cases f with | zero => omega | succ _ => rcases hSx r.toNat hsub.1 with h1 | h2 <;> omega
      cases htxt : k.textOf? s with
      | some str =>
          have hrenderTxt : (View.render k s).textOf? = some str := (View.textOf?_eq_render s k).symm.trans htxt
          have hkEq : View.render k s = .text str := textOf_eq_some_iff.1 hrenderTxt
          simp only [View.renderEach, hkEq, htmlListNodeCount, htmlNodeCount] at hbound
          have hrestDep : htmlListDepth (View.renderEach rest s) ≤ f := by
            simp only [View.renderEach, htmlListDepth] at hdep
            exact Nat.le_trans (Nat.le_max_right _ _) hdep
          have hallocRun : ∀ (inRun' : Bool) (aMid : DomArena msg),
              aMid.nextId = a.nextId + 1 →
              aMid.get (UInt32.ofNat a.nextId) = .text str →
              aMid.get parent = .element pns ptag pst pmg (pre ++ UInt32.ofNat a.nextId :: domCs) →
              (∀ m : Dom.Node, m ≠ parent → m ≠ UInt32.ofNat a.nextId → aMid.get m = a.get m) →
              HydratableDomList f childNs
                (if inRun' then dropCurrentTextRun (View.renderEach rest s) else coalesceTextRun (View.renderEach rest s))
                a lo hi domCs →
              (hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
                inTextRun str (fun () => hasMoreText (View.renderEach rest s)) a = ((UInt32.ofNat a.nextId, inRun'), aMid)) →
              (let (kstates, aOut) := (hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pre.length) inTextRun (k :: rest)).run a
               aOut.get parent = .element pns ptag pst pmg (pre ++ kstates.map VState.rootNode) ∧
               VStateKidsMatches (k :: rest) s aOut (kstates.map VState.rootNode) kstates) := by
            intro inRun' aMid haMidNext hgetNew hgetParMid hframeMid hdom' hslotEq
            let kn := UInt32.ofNat a.nextId
            have hparNeNew : parent ≠ kn := by
              have huN : kn.toNat = a.nextId := uint32_toNat_ofNat_lt a.nextId (by omega)
              intro heq; rw [heq, huN] at hparLo; omega
            have ⟨hdomMid, hpreMid⟩ := preSub_extend_alloc f childNs parent _ pre domCs lo hi a aMid str
              hposF (by omega) hparLo hhiNext haMidNext hgetNew hframeMid hpreSub hdom'
            have hih := ih s inRun' (pre ++ [kn]) domCs lo hi aMid hrestCl
              (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen; omega)
              (by rw [haMidNext]; omega) hrestDep hparLo hpreMid (by simpa [List.append_assoc] using hgetParMid) hdomMid
            dsimp only [StateT.run] at hih ⊢
            dsimp only [hydrateViewKidsM]; rw [htxt]; simp only [hasMoreViewText_eq_renderEach]
            dsimp only [bind, StateT.bind, pure, StateT.pure]; rw [hslotEq]; dsimp only
            have hvk := hydrateViewM_of_textOf? htxt kn aMid
            dsimp only [StateT.run] at hvk
            cases hvm : hydrateViewM (m := StateM (DomArena msg)) k s kn aMid with
            | mk kst a2 =>
                rw [hvm] at hvk; dsimp only at hvk
                rcases hvk with ⟨ha2Eq, hrootKst, hmatchKst⟩
                rw [ha2Eq]; dsimp only
                rw [show UInt32.ofNat (pre ++ [kn]).length = UInt32.ofNat pre.length + 1 from by
                  rw [List.length_append, List.length_singleton, huIdxNext]] at hih
                cases hrest : hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pre.length + 1) inRun' rest aMid with
                | mk ksR aOut =>
                    rw [hrest] at hih; dsimp only [List.map_cons, VStateKidsMatches] at hih ⊢
                    rw [hrootKst]
                    exact ⟨by simpa [List.append_assoc] using hih.1, rfl, hmatchKst aOut, hih.2⟩
          by_cases hsEmpty : str = ""
          · subst hsEmpty
            have hdom' : HydratableDomList f childNs (if inTextRun then dropCurrentTextRun (View.renderEach rest s) else coalesceTextRun (View.renderEach rest s)) a lo hi domCs := by
              cases inTextRun <;> simpa [View.renderEach, hkEq, coalesceTextRun, dropCurrentTextRun] using hdom
            rcases hydrateDomKidsM_fresh_nextId f childNs parent _ pre domCs lo hi a hposF (by omega) hparLo hpreSub hdom' with
              ⟨hnotIn, hparNePh⟩
            let resSlot := (hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
              inTextRun "" (fun () => hasMoreText (View.renderEach rest s))).run a
            have hslot := hydrateTextSlotM_empty_spec a parent inTextRun (fun () => hasMoreText (View.renderEach rest s))
              pns ptag pst pmg pre domCs (by omega) hnotIn hdisjDom (by simp at hlen; omega) hparNePh hpar
            exact hallocRun inTextRun resSlot.2 hslot.2.2.1 hslot.2.2.2.1 hslot.2.2.2.2.1 hslot.2.2.2.2.2 hdom'
              (Prod.ext (Prod.ext hslot.1 hslot.2.1) rfl)
          · cases inTextRun with
            | true =>
                have hdom' : HydratableDomList f childNs (dropCurrentTextRun (View.renderEach rest s)) a lo hi domCs := by
                  simpa [View.renderEach, hkEq, dropCurrentTextRun, Html.textOf?, hsEmpty] using hdom
                rcases hydrateDomKidsM_fresh_nextId f childNs parent _ pre domCs lo hi a hposF (by omega) hparLo hpreSub hdom' with
                  ⟨hnotIn, hparNeTn⟩
                let resSlot := (hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
                  true str (fun () => hasMoreText (View.renderEach rest s))).run a
                have hslot := hydrateTextSlotM_split_spec a parent str hsEmpty (fun () => hasMoreText (View.renderEach rest s))
                  pns ptag pst pmg pre domCs (by omega) hnotIn hdisjDom (by simp at hlen; omega) hparNeTn hpar
                exact hallocRun true resSlot.2 hslot.2.2.1 hslot.2.2.2.1 hslot.2.2.2.2.1 hslot.2.2.2.2.2 hdom'
                  (Prod.ext (Prod.ext hslot.1 hslot.2.1) rfl)
            | false =>
                have hdomCoal : HydratableDomList f childNs
                    (.text (str ++ restOfTextRun (View.renderEach rest s)) :: dropCurrentTextRun (View.renderEach rest s)) a lo hi domCs := by
                  simpa [View.renderEach, hkEq, coalesceTextRun, Html.textOf?, hsEmpty] using hdom
                cases domCs with
                | nil => exact False.elim hdomCoal
                | cons tn domRest =>
                    rcases HydratableDomList_cons_bounds hdomCoal with ⟨mid, hloMid, hmidHi, hiNext, htnDom, hrestDom⟩
                    cases f with
                    | zero => omega
                    | succ f' =>
                        rcases htnDom with ⟨htnLo, htnMid, _, hgetTn⟩
                        let resSlot := (hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
                          false str (fun () => hasMoreText (View.renderEach rest s))).run a
                        let aMid := resSlot.2
                        have hslot := hydrateTextSlotM_head_spec a parent tn str (restOfTextRun (View.renderEach rest s)) hsEmpty
                          (hasMoreText (View.renderEach rest s)) (hasMoreText_false_restOfTextRun (View.renderEach rest s))
                          pns ptag pst pmg pre domRest (by simp at hlen; omega) hpar hgetTn
                        have haMidNext : aMid.nextId = a.nextId := hslot.2.2.1
                        have hgetTnMid : aMid.get tn = .text str := hslot.2.2.2.1
                        have hframeMid : ∀ m : Dom.Node, m ≠ tn → aMid.get m = a.get m := hslot.2.2.2.2
                        have hparNeTn : parent ≠ tn := by intro heq; rw [heq] at hparLo; omega
                        have hparMid : aMid.get parent = .element pns ptag pst pmg ((pre ++ [tn]) ++ domRest) := by
                          rw [hframeMid parent hparNeTn, hpar]; simp [List.append_assoc]
                        have ⟨hdomMid, hpreMid⟩ := preSub_extend_existing (f' + 1) childNs parent tn
                          (dropCurrentTextRun (View.renderEach rest s)) pre domRest lo mid hi a aMid (fun k' => k' = tn.toNat)
                          hloMid hmidHi hiNext (by rw [haMidNext]; exact Nat.le_refl _)
                          (fun m hm _ => hframeMid m (fun heq => by rw [heq] at hm; rcases hm with h1 | h2 <;> omega))
                          hpreSub hrestDom (fun k' hk' => .inl ⟨by omega, by omega⟩) ⟨rfl, by simp [hgetTnMid]⟩
                        have hih := ih s true (pre ++ [tn]) domRest mid hi aMid hrestCl
                          (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen; omega)
                          (by rw [haMidNext]; omega) hrestDep (by omega) hpreMid hparMid (by simpa using hdomMid)
                        have hslotEq : hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
                            false str (fun () => hasMoreText (View.renderEach rest s)) a = ((tn, true), aMid) :=
                          Prod.ext (Prod.ext hslot.1 hslot.2.1) rfl
                        dsimp only [StateT.run] at hih ⊢
                        dsimp only [hydrateViewKidsM]; rw [htxt]; simp only [hasMoreViewText_eq_renderEach]
                        dsimp only [bind, StateT.bind, pure, StateT.pure]; rw [hslotEq]; dsimp only
                        have hvk := hydrateViewM_of_textOf? htxt tn aMid
                        dsimp only [StateT.run] at hvk
                        cases hvm : hydrateViewM (m := StateM (DomArena msg)) k s tn aMid with
                        | mk kst a2 =>
                            rw [hvm] at hvk; dsimp only at hvk
                            rcases hvk with ⟨ha2Eq, hrootKst, hmatchKst⟩
                            rw [ha2Eq]; dsimp only
                            rw [show UInt32.ofNat (pre ++ [tn]).length = UInt32.ofNat pre.length + 1 from by
                              rw [List.length_append, List.length_singleton, huIdxNext]] at hih
                            cases hrest : hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pre.length + 1) true rest aMid with
                            | mk ksR aOut =>
                                rw [hrest] at hih; dsimp only [List.map_cons, VStateKidsMatches] at hih ⊢
                                rw [hrootKst]
                                exact ⟨by simpa [List.append_assoc] using hih.1, rfl, hmatchKst aOut, hih.2⟩
      | none =>
          have hrenderTxt : (View.render k s).textOf? = none := (View.textOf?_eq_render s k).symm.trans htxt
          rcases textOf_none_is_element hrenderTxt with ⟨tag, attrs, kids, hcEq⟩
          simp only [View.renderEach, htmlListNodeCount, htmlListDepth] at hbound hdep
          have hcDep : htmlDepth (View.render k s) ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
          have hrestDep : htmlListDepth (View.renderEach rest s) ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
          have hlenRest : rest.length = (View.renderEach rest s).length := (View.renderEach_length s rest).symm
          have hdomElem : HydratableDomList f childNs (View.render k s :: coalesceTextRun (View.renderEach rest s)) a lo hi domCs := by
            cases inTextRun
            · simpa [View.renderEach, hcEq, coalesceTextRun_head_element] using hdom
            · simpa [View.renderEach, hcEq, dropCurrentTextRun_head_element] using hdom
          cases domCs with
          | nil => exact False.elim hdomElem
          | cons child domRest =>
              rcases HydratableDomList_cons_bounds hdomElem with ⟨mid, hloMid, hmidHi, hiNext, hchildDom, hrestDom⟩
              cases f with
              | zero => have := htmlDepth_pos (View.render k s); omega
              | succ f' =>
                  have huIdx : (UInt32.ofNat pre.length).toNat = pre.length :=
                    uint32_toNat_ofNat_lt pre.length (by simp at hlen; omega)
                  have hgetD : (pre ++ child :: domRest).getD pre.length 0 = child := getD_append_right child 0 pre domRest
                  have hchildSpec := hViewDom f' (Nat.lt_succ_self f') childNs k s child a lo mid hkCl (by omega) hcDep hchildDom
                  dsimp only [StateT.run] at hchildSpec
                  cases hvm : hydrateViewM (m := StateM (DomArena msg)) k s child a with
                  | mk kst aMid =>
                      rw [hvm] at hchildSpec; dsimp only at hchildSpec
                      rcases hchildSpec with ⟨hrootKst, haMidNext, haMidBound, hframeMid, hvalMid, _⟩
                      have hparMid : aMid.get parent = .element pns ptag pst pmg ((pre ++ [child]) ++ domRest) := by
                        rw [hframeMid parent (.inl hparLo) (by omega), hpar]; simp [List.append_assoc]
                      have hchildSubMid : SubtreeInSet (f' + 1) aMid
                          (fun k' => (lo ≤ k' ∧ k' < mid) ∨ (a.nextId ≤ k' ∧ k' < aMid.nextId)) child := by
                        have hdomS := (hydrateDomM_spec childNs f' (View.render k s) child a lo mid (by omega) hcDep hchildDom).2.2.1
                        have haMidEqDom := hydrateViewM_eq_hydrateDomM hkCl s child a
                        dsimp only [StateT.run] at haMidEqDom hdomS
                        cases hdmMid : hydrateDomM (m := StateM (DomArena msg)) (View.render k s) child a with
                        | mk _ aDomMid =>
                            rw [hvm, hdmMid] at haMidEqDom; dsimp only at haMidEqDom
                            rw [hdmMid] at hdomS; dsimp only at hdomS
                            have hdomS' := (SubtreeInSet_frame (fun m _ => haMidEqDom.get_eq m) hdomS).1
                            rwa [← haMidEqDom.1] at hdomS'
                      have ⟨hdomMid, hpreMid⟩ := preSub_extend_existing (f' + 1) childNs parent child
                        (coalesceTextRun (View.renderEach rest s)) pre domRest lo mid hi a aMid
                        (fun k' => (lo ≤ k' ∧ k' < mid) ∨ (a.nextId ≤ k' ∧ k' < aMid.nextId))
                        hloMid hmidHi hiNext haMidNext hframeMid hpreSub hrestDom
                        (fun k' hk' => hk'.elim (fun h => .inl ⟨by omega, h.2⟩) (fun h => .inr ⟨by omega, h.2⟩))
                        hchildSubMid
                      have hih := ih s false (pre ++ [child]) domRest mid hi aMid hrestCl
                        (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen; omega)
                        (by omega) hrestDep (by omega) hpreMid hparMid (by simpa using hdomMid)
                      have hrestDomSpec := hydrateDomKidsM_spec childNs parent pns ptag pst pmg (f' + 1)
                        (View.renderEach rest s) false (pre ++ [child]) domRest mid hi aMid
                        (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen; omega)
                        (by omega) hrestDep (by omega) hpreMid hparMid (by simpa using hdomMid)
                      rcases hrestDomSpec with ⟨_, _, _, _, _, hfrDomR, _, _⟩
                      dsimp only [StateT.run] at hih ⊢
                      dsimp only [hydrateViewKidsM]; rw [htxt]
                      dsimp only [bind, StateT.bind, pure, StateT.pure, MonadDom.childAt]
                      rw [hpar, huIdx]; dsimp only; rw [hgetD, hvm]; dsimp only
                      rw [show UInt32.ofNat (pre ++ [child]).length = UInt32.ofNat pre.length + 1 from by
                        rw [List.length_append, List.length_singleton, huIdxNext]] at hih hfrDomR
                      have hrestEq := hydrateViewKidsM_eq_hydrateDomKidsM hrestCl parent s (UInt32.ofNat pre.length + 1) false aMid
                      dsimp only [StateT.run] at hrestEq hfrDomR
                      cases hrest : hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pre.length + 1) false rest aMid with
                      | mk ksR aOut =>
                          cases hdrest : hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length + 1) false (View.renderEach rest s) aMid with
                          | mk _ aDomOut =>
                              rw [hrest, hdrest] at hrestEq; dsimp only at hrestEq
                              rw [hdrest] at hfrDomR; dsimp only at hfrDomR
                              rw [hrest] at hih; dsimp only at hih
                              have hmKstOut : VStateMatches k s aOut child kst :=
                                VStateMatches_frame (fun m hm => (hrestEq.get_eq m).trans (hfrDomR m
                                  (by intro heq; rw [heq] at hm; rcases hm with h1 | h2 <;> omega)
                                  (hm.elim (fun h1 => .inl h1.2) (fun h2 => .inr (Nat.le_trans hhiNext h2.1)))
                                  (hm.elim (fun h1 => by omega) (fun h2 => h2.2))))
                                  (hrootKst ▸ hvalMid.1) (hrootKst ▸ hvalMid.2)
                              dsimp only [List.map_cons, VStateKidsMatches]
                              rw [hrootKst]
                              exact ⟨by simpa [List.append_assoc] using hih.1, rfl, hmKstOut, hih.2⟩

private theorem hydrateViewM_spec_view {msg : Type} (f : Nat)
    (ihView : ∀ f' < f, @ViewHydrateSpecAt msg f') {σ : Type} (ns : String) :
    ∀ (v : View σ msg) (s : σ) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat),
      View.DomClean v →
      a.nextId + htmlNodeCount (View.render v s) < UInt32.size →
      htmlDepth (View.render v s) ≤ f + 1 →
      HydratableDom (f + 1) ns (View.render v s) a lo hi root →
      let (vst, aOut) := (hydrateViewM (m := StateM (DomArena msg)) v s root).run a
      vst.rootNode = root ∧
      a.nextId ≤ aOut.nextId ∧
      aOut.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
      (∀ m : Dom.Node, (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      VStateValid (f + 1) ns v s aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) vst ∧
      DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns (View.render v s))
  | .keyedList _ _ _ _ _ _ _ (some _), _, _, _, _, _, h, _, _, _ => False.elim h
  | .keyedList tag attrs keys marks rowSig rowEv rowsHtml none, s, root, a, lo, hi, ⟨haCl, hrowsCl⟩, hbound, hdep, hdom => by
      have hdomSpec := hydrateDomM_spec ns f (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s) root a lo hi hbound hdep hdom
      have hviewEq := hydrateViewM_eq_hydrateDomM (v := .keyedList tag attrs keys marks rowSig rowEv rowsHtml) ⟨haCl, hrowsCl⟩ s root a
      dsimp only [StateT.run] at hdomSpec hviewEq
      dsimp only [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure] at hviewEq ⊢
      cases ha1 : applyAttrsM (m := StateM (DomArena msg)) root (attrs.map (VAttr.eval s))
          (a.modifyElemState root fun st => { st with clicks := [], inputs := [] }) with
      | mk _ a1 =>
          rw [ha1] at hviewEq; dsimp only at hviewEq ⊢
          cases hs1 : seedRowsM (m := StateM (DomArena msg)) s!"§{root}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a1 with
          | mk perRow a2 =>
              rw [hs1] at hviewEq
              rw [Html.map_prefixSignals_of_DomCleanList _ (hrowsCl.2.1 s)] at hviewEq ⊢
              dsimp only at hviewEq ⊢
              cases hl1 : hydrateListRowsM (m := StateM (DomArena msg)) root 0 (rowsHtml s) a2 with
              | mk _ aOut =>
                  rw [hl1] at hviewEq; dsimp only at hviewEq ⊢
                  cases hdomRun : hydrateDomM (m := StateM (DomArena msg))
                      (View.render (.keyedList tag attrs keys marks rowSig rowEv rowsHtml) s) root a with
                  | mk _ aDom =>
                      rw [hdomRun] at hviewEq hdomSpec; dsimp only at hviewEq hdomSpec
                      rcases hdomSpec with ⟨h1, h2, _, h4, h5, h6⟩
                      have hcleanDom := h6 (View.DomClean_render (v := .keyedList tag attrs keys marks rowSig rowEv rowsHtml) ⟨haCl, hrowsCl⟩ s)
                      refine ⟨rfl, by rw [hviewEq.1]; exact h1, by rw [hviewEq.1]; exact h2,
                        fun m hmOut hmLt => (hviewEq.get_eq m).trans (h4 m hmOut hmLt),
                        ⟨CleanDomSubtree_frame (fun m _ => hviewEq.get_eq m) (by rw [hviewEq.1]; exact hcleanDom),
                         rfl, rfl, rfl⟩,
                        by rw [hviewEq.readDomTree_eq (f + 1) root]; exact h5⟩
  | .text str, s, root, a, lo, hi, _, hbound, hdep, hdom => by
      rcases hydrateDomM_spec ns f (View.render (.text str) s) root a lo hi hbound hdep hdom with ⟨h1, h2, _, h4, h5, h6⟩
      exact ⟨rfl, h1, h2, h4, ⟨h6 rfl, rfl⟩, h5⟩
  | .dyn get, s, root, a, lo, hi, _, hbound, hdep, hdom => by
      rcases hydrateDomM_spec ns f (View.render (.dyn get) s) root a lo hi hbound hdep hdom with ⟨h1, h2, _, h4, h5, h6⟩
      exact ⟨rfl, h1, h2, h4, ⟨h6 rfl, rfl, rfl⟩, h5⟩
  | .static h, s, root, a, lo, hi, hc, hbound, hdep, hdom => by
      have hd := hydrateDomM_spec ns f h root a lo hi hbound hdep hdom
      dsimp only [StateT.run] at hd
      dsimp only [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
      cases hhd : hydrateDomM (m := StateM (DomArena msg)) h root a with
      | mk _ aOut =>
          rw [hhd] at hd; dsimp only at hd
          rcases hd with ⟨h1, h2, _, h4, h5, h6⟩
          exact ⟨rfl, h1, h2, h4, ⟨h6 hc, rfl⟩, h5⟩
  | .dynNode get, s, root, a, lo, hi, hc, hbound, hdep, hdom => by
      have hd := hydrateDomM_spec ns f (get s) root a lo hi hbound hdep hdom
      dsimp only [StateT.run] at hd
      dsimp only [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
      cases hhd : hydrateDomM (m := StateM (DomArena msg)) (get s) root a with
      | mk _ aOut =>
          rw [hhd] at hd; dsimp only at hd
          rcases hd with ⟨h1, h2, _, h4, h5, h6⟩
          exact ⟨rfl, h1, h2, h4, ⟨h6 (hc s), rfl, rfl⟩, h5⟩
  | .memo sm, s, root, a, lo, hi, hc, hbound, hdep, hdom => by
      have hd := hydrateDomM_spec ns f (sm.eval s) root a lo hi hbound hdep hdom
      dsimp only [StateT.run] at hd
      dsimp only [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
      cases hhd : hydrateDomM (m := StateM (DomArena msg)) (sm.eval s) root a with
      | mk _ aOut =>
          rw [hhd] at hd; dsimp only at hd
          rcases hd with ⟨h1, h2, _, h4, h5, h6⟩
          exact ⟨rfl, h1, h2, h4, ⟨h6 (hc s), rfl, rfl, rfl⟩, h5⟩
  | .ifElse c y n, s, root, a, lo, hi, ⟨hyCl, hnCl⟩, hbound, hdep, hdom => by
      dsimp only [hydrateViewM, StateT.run]
      cases hcs : c s <;> simp only [hcs, Bool.false_eq_true, ↓reduceIte, View.render, bind, StateT.bind, pure, StateT.pure] at hbound hdep hdom ⊢
      · have hr := hydrateViewM_spec_view f ihView ns n s root a lo hi hnCl hbound hdep hdom
        dsimp only [StateT.run] at hr
        cases hnRun : hydrateViewM (m := StateM (DomArena msg)) n s root a with
        | mk inner aOut =>
            rw [hnRun] at hr; dsimp only at hr ⊢
            rcases hr with ⟨hroot, h1, h2, h4, hval, heqv⟩
            exact ⟨hroot, h1, h2, h4, ⟨by simpa [VState.rootNode, View.render, hcs] using hval.1, hcs.symm, by simpa [VState.rootNode, hcs] using hval.2⟩,
              by simpa [View.render, hcs] using heqv⟩
      · have hr := hydrateViewM_spec_view f ihView ns y s root a lo hi hyCl hbound hdep hdom
        dsimp only [StateT.run] at hr
        cases hyRun : hydrateViewM (m := StateM (DomArena msg)) y s root a with
        | mk inner aOut =>
            rw [hyRun] at hr; dsimp only at hr ⊢
            rcases hr with ⟨hroot, h1, h2, h4, hval, heqv⟩
            exact ⟨hroot, h1, h2, h4, ⟨by simpa [VState.rootNode, View.render, hcs] using hval.1, hcs.symm, by simpa [VState.rootNode, hcs] using hval.2⟩,
              by simpa [View.render, hcs] using heqv⟩
  | .element tag attrs kids, s, root, a, lo, hi, ⟨haCl, hkidsCl⟩, hbound, hdep, hdom => by
      rcases hdom with ⟨hlo, hhi, hnext, st, prev, domCs, hget, hm, hns, hownT, hownF⟩
      have hown : ownsChildren (attrs.map (VAttr.eval s)) = false := haCl.1 s
      rcases hownF hown with ⟨mid, hmidGt, hk⟩
      rcases HydratableDomList_bounds f (Dom.childNsOf ns tag) (coalesceTextRun (View.renderEach kids s)) a mid hi domCs hk with ⟨hmidHi, hhiNext⟩
      have hattrs := applyAttrsM_existing_element a root
        (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
        { st with clicks := [], inputs := [] } prev domCs (attrs.map (VAttr.eval s)) hm hns
      rcases hattrs with ⟨st', ha2Get, ha2Eqv, hm'⟩
      let a2 := (applyAttrsM (m := StateM (DomArena msg)) root (attrs.map (VAttr.eval s))
        (a.set root (.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
          { st with clicks := [], inputs := [] } prev domCs))).2
      have ha2Next : a2.nextId = a.nextId := applyAttrsM_nextId a root (attrs.map (VAttr.eval s)) _
      have ha2Outside : ∀ m : Dom.Node, m ≠ root → a2.get m = a.get m := fun m hne =>
        applyAttrsM_get_ne a root (attrs.map (VAttr.eval s)) _ m hne
      have hkFrame : HydratableDomList f (Dom.childNsOf ns tag) (coalesceTextRun (View.renderEach kids s)) a2 mid hi domCs :=
        HydratableDomList_frame f (Dom.childNsOf ns tag) (coalesceTextRun (View.renderEach kids s)) a a2 mid hi domCs
          (by rw [ha2Next]; exact Nat.le_refl _) (fun m hm1 _ => ha2Outside m (by intro heq; rw [heq] at hm1; omega)) hk
      have hkLen : kids.length = (View.renderEach kids s).length := (View.renderEach_length s kids).symm
      have hcsLenLt : ([] : List Dom.Node).length + kids.length < UInt32.size := by
        simp only [List.length_nil, Nat.zero_add]
        have := list_length_le_htmlListNodeCount (View.renderEach kids s)
        simp only [View.render, htmlNodeCount] at hbound; omega
      have ha2Bound : a2.nextId + htmlListNodeCount (View.renderEach kids s) < UInt32.size := by
        simp only [View.render, htmlNodeCount] at hbound; omega
      have hcsDep : htmlListDepth (View.renderEach kids s) ≤ f := by
        simp only [View.render, htmlDepth] at hdep; omega
      have hvk := viewKidsMatches_step f ihView (Dom.childNsOf ns tag) root
        (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag st'
        ((normalizeAttrs (attrs.map (VAttr.eval s))).filterMap managedAttrName)
        kids s false [] domCs mid hi a2 hkidsCl hcsLenLt ha2Bound hcsDep hmidGt
        (fun _ hm => nomatch hm) ha2Get hkFrame
      have hdomSpec := hydrateDomM_spec ns f (View.render (.element tag attrs kids) s) root a lo hi hbound hdep
        ⟨hlo, hhi, hnext, st, prev, domCs, hget, hm, hns, hownT, hownF⟩
      have hviewEq := hydrateViewM_eq_hydrateDomM (v := .element tag attrs kids) ⟨haCl, hkidsCl⟩ s root a
      dsimp only [StateT.run] at hvk hdomSpec hviewEq ⊢
      have hclearMod : a.modifyElemState root (fun st : SpecElemState msg => { st with clicks := [], inputs := [] }) =
          a.set root (.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
            { st with clicks := [], inputs := [] } prev domCs) := by
        simp [DomArena.modifyElemState, DomArena.modify, hget]
      have ha2Run : applyAttrsM (m := StateM (DomArena msg)) root (attrs.map (VAttr.eval s))
          (a.set root (.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
            { st with clicks := [], inputs := [] } prev domCs)) = ((), a2) := Prod.ext rfl rfl
      dsimp only [hydrateViewM, bind, StateT.bind, pure, StateT.pure]
      rw [hclearMod, ha2Run]; dsimp only
      cases hkidsRun : hydrateViewKidsM (m := StateM (DomArena msg)) root s 0 false kids a2 with
      | mk kstates aOut =>
          rw [show (UInt32.ofNat ([] : List Dom.Node).length) = 0 from rfl, hkidsRun] at hvk
          rw [show hydrateViewM (m := StateM (DomArena msg)) (.element tag attrs kids) s root a = (.elem root kstates, aOut) from by
            simp only [hydrateViewM, bind, StateT.bind, pure, StateT.pure, hclearMod, ha2Run, hkidsRun]] at hviewEq
          cases hdomRun : hydrateDomM (m := StateM (DomArena msg)) (View.render (.element tag attrs kids) s) root a with
          | mk _ aDom =>
              rw [hdomRun] at hviewEq hdomSpec
              dsimp only at hvk hviewEq hdomSpec
              rcases hdomSpec with ⟨h1, h2, _, h4, h5, h6⟩
              have hcleanDom := h6 (View.DomClean_render (v := .element tag attrs kids) ⟨haCl, hkidsCl⟩ s)
              refine ⟨rfl, by rw [hviewEq.1]; exact h1, by rw [hviewEq.1]; exact h2,
                fun m hmOut hmLt => (hviewEq.get_eq m).trans (h4 m hmOut hmLt),
                ⟨CleanDomSubtree_frame (fun m _ => hviewEq.get_eq m) (by rw [hviewEq.1]; exact hcleanDom),
                 rfl, _, tag, st', (normalizeAttrs (attrs.map (VAttr.eval s))).filterMap managedAttrName,
                 kstates.map VState.rootNode, hvk.1, hvk.2⟩,
                by rw [hviewEq.readDomTree_eq (f + 1) root]; exact h5⟩

private theorem hydrateViewM_spec_strong (f : Nat) : @ViewHydrateSpecAt msg f := by
  induction f using Nat.strongRecOn with
  | ind f ihView => intro _ ns v s root a lo hi; exact hydrateViewM_spec_view f ihView ns v s root a lo hi

theorem hydrateViewM_spec {σ msg : Type} (ns : String) (f : Nat) (v : View σ msg) (s : σ)
    (root : Dom.Node) (a : DomArena msg) (lo hi : Nat)
    (hc : View.DomClean v)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size)
    (hdep : htmlDepth (View.render v s) ≤ f + 1)
    (hdom : HydratableDom (f + 1) ns (View.render v s) a lo hi root) :
    let (vst, aOut) := (hydrateViewM (m := StateM (DomArena msg)) v s root).run a
    vst.rootNode = root ∧
    a.nextId ≤ aOut.nextId ∧
    aOut.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
    (∀ m : Dom.Node, (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    VStateValid (f + 1) ns v s aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) vst ∧
    DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns (View.render v s)) :=
  hydrateViewM_spec_strong f ns v s root a lo hi hc hbound hdep hdom

end Qed
