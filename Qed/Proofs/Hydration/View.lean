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
      cases hc : c s <;> (
        simp only [hc, ↓reduceIte, Bool.false_eq_true] at h
        have ih := hydrateViewM_of_textOf? h kn a
        dsimp only [StateT.run] at ih
        cases hy : hydrateViewM (m := StateM (DomArena msg)) _ s kn a with
        | mk vst' a' =>
            rw [hy] at ih; dsimp only at ih
            simp [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, hc, hy, VState.rootNode, VStateMatches, ih.1, ih.2.1, ih.2.2])
  | .element .., _, _, h, _, _ | .keyedList .., _, _, h, _, _ => by simp [View.textOf?] at h

private theorem hydrateTextSlotM_metaIndep {msg : Type} (parent : Dom.Node) (index : UInt32)
    (inRun : Bool) (s : String) (more : Unit → Bool) :
    DomArena.MetaIndep (hydrateTextSlotM (m := StateM (DomArena msg)) parent index inRun s more) :=
  fun _ _ _ _ a => by
    dsimp only [hydrateTextSlotM]
    split
    · rfl
    · split
      · rfl
      · dsimp only [bind, StateT.bind, pure, StateT.pure, MonadDom.childAt, DomArena.get, DomArena.withMeta]
        cases more () <;> rfl

mutual
  theorem hydrateDomM_metaIndep {msg : Type} :
      (h : Html msg) → (node : Dom.Node) → DomArena.MetaIndep (hydrateDomM (m := StateM (DomArena msg)) h node)
    | .text _, _ => .pure ()
    | .element _ attrs cs, node => by
        dsimp only [hydrateDomM]
        refine .bind (fun _ _ _ _ _ => rfl) fun _ => .bind (applyAttrsM_metaIndep node attrs) fun _ => ?_
        cases ownsChildren attrs
        · exact hydrateDomKidsM_metaIndep cs node 0 false
        · exact .pure ()

  theorem hydrateDomKidsM_metaIndep {msg : Type} :
      (cs : List (Html msg)) → (node : Dom.Node) → (i : UInt32) → (inRun : Bool) →
      DomArena.MetaIndep (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs)
    | [], _, _, _ => .pure ()
    | c :: rest, node, i, inRun => by
        dsimp only [hydrateDomKidsM]
        cases c.textOf? with
        | none =>
            exact .bind (fun _ _ _ _ _ => rfl) fun cn =>
              .bind (hydrateDomM_metaIndep c cn) fun _ =>
                hydrateDomKidsM_metaIndep rest node (i + 1) false
        | some str =>
            exact .bind (hydrateTextSlotM_metaIndep node i inRun str (fun () => hasMoreText rest)) fun r =>
              hydrateDomKidsM_metaIndep rest node (i + 1) r.2
end

theorem hydrateDomKidsM_sameDom {msg : Type} (node : Dom.Node) (i : UInt32) (inRun : Bool)
    (cs : List (Html msg)) {a₁ a₂ : DomArena msg} (hs : a₁.SameDom a₂) :
    (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs a₁).2.SameDom
      (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs a₂).2 :=
  (hydrateDomKidsM_metaIndep cs node i inRun).sameDom hs

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

theorem hydrateViewM_eq_hydrateDomM {σ msg : Type} {v : View σ msg} (hcl : View.DomClean v)
    (s : σ) (node : Dom.Node) (a : DomArena msg) :
    ((hydrateViewM (m := StateM (DomArena msg)) v s node).run a).2.SameDom
      ((hydrateDomM (m := StateM (DomArena msg)) (View.render v s) node).run a).2 := by
  induction v using View.ind generalizing node a with
  | text _ | dyn _ => exact DomArena.SameDom.refl a
  | static h =>
      cases h <;> (
        dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
        cases hydrateDomM (m := StateM (DomArena msg)) _ _ _; exact DomArena.SameDom.refl _)
  | dynNode get =>
      dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
      cases hydrateDomM (m := StateM (DomArena msg)) (get s) node a; exact DomArena.SameDom.refl _
  | memo sm =>
      dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
      cases hydrateDomM (m := StateM (DomArena msg)) (sm.eval s) node a; exact DomArena.SameDom.refl _
  | ifElse c y no ihy ihn =>
      rcases hcl with ⟨hy, hn⟩
      cases hcs : c s <;> (
        dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
        rw [hcs]; simp only [Bool.false_eq_true, ↓reduceIte, StateT.bind, StateT.pure]
        cases hrun : hydrateViewM (m := StateM (DomArena msg)) _ s node a
        first
        | (have h := ihn hn node a; dsimp only [StateT.run] at h; rw [hrun] at h; exact h)
        | (have h := ihy hy node a; dsimp only [StateT.run] at h; rw [hrun] at h; exact h))
  | element tag attrs kids ihk =>
      rcases hcl with ⟨ha, hks⟩
      dsimp only [hydrateViewM, View.render, hydrateDomM, StateT.run, bind, StateT.bind, pure, StateT.pure]
      rw [ha.1 s, Bool.not_false, if_pos rfl]
      cases applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s))
          (a.modifyElemState node fun st => { st with clicks := [], inputs := [] }) with
      | mk _ a1 =>
          have h := hydrateViewKidsM_eq_hydrateDomKidsM_of kids node s
            (fun k hk hkCl cn a' => ihk k hk hkCl cn a') hks 0 false a1
          dsimp only [StateT.run] at h
          cases hydrateViewKidsM (m := StateM (DomArena msg)) node s 0 false kids a1; exact h
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      cases tmpl? with
      | some _ => exact False.elim hcl
      | none =>
          rcases hcl with ⟨ha, hrows⟩
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

theorem hydrateViewKidsM_eq_hydrateDomKidsM {σ msg : Type} {ks : List (View σ msg)} (hcl : View.DomCleanEach ks)
    (node : Dom.Node) (s : σ) (i : UInt32) (inRun : Bool) (a : DomArena msg) :
    ((hydrateViewKidsM (m := StateM (DomArena msg)) node s i inRun ks).run a).2.SameDom
      ((hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun (View.renderEach ks s)).run a).2 :=
  hydrateViewKidsM_eq_hydrateDomKidsM_of ks node s (fun _ _ hkCl cn a' => hydrateViewM_eq_hydrateDomM hkCl s cn a') hcl i inRun a

private theorem View.renderEach_eq_map {σ msg : Type} (s : σ) :
    ∀ ks : List (View σ msg), View.renderEach ks s = ks.map (fun v => View.render v s)
  | [] => rfl
  | _ :: rest => congrArg (List.cons _) (View.renderEach_eq_map s rest)

private theorem View.DomCleanEach_iff {σ msg : Type} :
    ∀ {ks : List (View σ msg)}, View.DomCleanEach ks ↔ ∀ k ∈ ks, View.DomClean k
  | [] => ⟨(fun _ _ h => nomatch h), fun _ => trivial⟩
  | _ :: _ => ⟨fun ⟨h1, h2⟩ _ hm => (List.mem_cons.1 hm).elim (· ▸ h1) (View.DomCleanEach_iff.1 h2 _),
      fun h => ⟨h _ (.head _), View.DomCleanEach_iff.2 fun x hx => h x (.tail _ hx)⟩⟩

private theorem hydrateViewM_spec_of_matches {σ msg : Type} (ns : String) (f : Nat)
    (v : View σ msg) (s : σ) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat)
    (hc : View.DomClean v)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size)
    (hdep : htmlDepth (View.render v s) ≤ f + 1)
    (hdom : HydratableDom (f + 1) ns (View.render v s) a lo hi root)
    (hmt : let (vst, aOut) := (hydrateViewM (m := StateM (DomArena msg)) v s root).run a
           vst.rootNode = root ∧ VStateMatches v s aOut root vst) :
    let (vst, aOut) := (hydrateViewM (m := StateM (DomArena msg)) v s root).run a
    vst.rootNode = root ∧ a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
    (∀ m : Dom.Node, (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    VStateValid (f + 1) ns v s aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) vst ∧
    DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns (View.render v s)) := by
  have hdomSpec := hydrateDomM_spec ns f (View.render v s) root a lo hi hbound hdep hdom
  have hviewEq := hydrateViewM_eq_hydrateDomM hc s root a
  dsimp only [StateT.run] at hdomSpec hviewEq hmt ⊢
  cases hvm : hydrateViewM (m := StateM (DomArena msg)) v s root a with
  | mk vst aOut =>
      cases hdm : hydrateDomM (m := StateM (DomArena msg)) (View.render v s) root a with
      | mk _ aDom =>
          rw [hvm] at hviewEq hmt; rw [hdm] at hviewEq hdomSpec; dsimp only at hviewEq hdomSpec hmt ⊢
          rcases hdomSpec with ⟨h1, h2, _, h4, h5, h6⟩
          have hcl : CleanDomSubtree (f + 1) ns (View.render v s) aOut
              (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) root :=
            CleanDomSubtree_frame (fun m _ => hviewEq.get_eq m) (hviewEq.1 ▸ h6 (View.DomClean_render hc s))
          exact ⟨hmt.1, hviewEq.1 ▸ h1, hviewEq.1 ▸ h2,
            fun m hmOut hmLt => (hviewEq.get_eq m).trans (h4 m hmOut hmLt),
            ⟨hmt.1.symm ▸ hcl, hmt.1.symm ▸ hmt.2⟩,
            hviewEq.readDomTree_eq (f + 1) root ▸ h5⟩

private theorem viewKidsMatches_step {σ msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (ks : List (View σ msg)) (s : σ) (inTextRun : Bool) (pre domCs : List Dom.Node) (lo hi : Nat) (a : DomArena msg)
    (hView : ∀ k ∈ ks, ∀ (f' : Nat) (root : Dom.Node) (a0 : DomArena msg) (lo0 hi0 : Nat),
      View.DomClean k → a0.nextId + htmlNodeCount (View.render k s) < UInt32.size →
      htmlDepth (View.render k s) ≤ f' + 1 → HydratableDom (f' + 1) childNs (View.render k s) a0 lo0 hi0 root →
      let (vst, aOut) := (hydrateViewM (m := StateM (DomArena msg)) k s root).run a0
      vst.rootNode = root ∧ VStateMatches k s aOut root vst)
    (hcl : View.DomCleanEach ks) (hlen : pre.length + ks.length < UInt32.size)
    (hbound : a.nextId + htmlListNodeCount (View.renderEach ks s) < UInt32.size)
    (hdep : htmlListDepth (View.renderEach ks s) ≤ f) (hparLo : parent.toNat < lo)
    (hpreSub : ∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet f a Sx x)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ domCs))
    (hdom : HydratableDomList f childNs
      (if inTextRun then dropCurrentTextRun (View.renderEach ks s) else coalesceTextRun (View.renderEach ks s))
      a lo hi domCs) :
    let (kstates, aOut) := (hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pre.length) inTextRun ks).run a
    aOut.get parent = .element pns ptag pst pmg (pre ++ kstates.map VState.rootNode) ∧
    VStateKidsMatches ks s aOut (kstates.map VState.rootNode) kstates := by
  have htextFinish : ∀ (k : View σ msg) (rest : List (View σ msg)) (inRun inRun' : Bool)
      (pr : List Dom.Node) (kn : Dom.Node) (a0 aMid : DomArena msg) (str : String),
      k.textOf? s = some str → UInt32.ofNat pr.length + 1 = UInt32.ofNat (pr.length + 1) →
      hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pr.length) inRun str
        (fun () => hasMoreText (rest.map (fun v => View.render v s))) a0 = ((kn, inRun'), aMid) →
      (let (ksR, aOut) := (hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat (pr ++ [kn]).length) inRun' rest).run aMid
       aOut.get parent = .element pns ptag pst pmg ((pr ++ [kn]) ++ ksR.map VState.rootNode) ∧
       VStateKidsMatches rest s aOut (ksR.map VState.rootNode) ksR) →
      (let (kstates, aOut) := (hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pr.length) inRun (k :: rest)).run a0
       aOut.get parent = .element pns ptag pst pmg (pr ++ kstates.map VState.rootNode) ∧
       VStateKidsMatches (k :: rest) s aOut (kstates.map VState.rootNode) kstates) := by
    intro k rest inRun inRun' pr kn a0 aMid str htxt huNext hslotEq hih
    dsimp only [StateT.run] at hih ⊢
    dsimp only [hydrateViewKidsM]; rw [htxt]; simp only [hasMoreViewText_eq_renderEach, View.renderEach_eq_map]
    dsimp only [bind, StateT.bind, pure, StateT.pure]; rw [hslotEq]; dsimp only
    have hvk := hydrateViewM_of_textOf? htxt kn aMid; dsimp only [StateT.run] at hvk
    cases hvm : hydrateViewM (m := StateM (DomArena msg)) k s kn aMid with
    | mk kst a2 =>
        rw [hvm] at hvk; dsimp only at hvk; rcases hvk with ⟨ha2Eq, hrootKst, hmatchKst⟩; rw [ha2Eq]; dsimp only
        rw [show UInt32.ofNat (pr ++ [kn]).length = UInt32.ofNat pr.length + 1 from by rw [List.length_append, List.length_singleton, huNext]] at hih
        cases hrest : hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pr.length + 1) inRun' rest aMid with
        | mk ksR aOut =>
            rw [hrest] at hih; dsimp only [List.map_cons, VStateKidsMatches] at hih ⊢; rw [hrootKst]
            exact ⟨by simpa [List.append_assoc] using hih.1, rfl, hmatchKst aOut, hih.2⟩
  refine hydrateKids_ind (toHtml := fun v => View.render v s) (ItemOk := fun k => View.DomClean k ∧ k ∈ ks)
    (Post := fun tgt inRun pr _ _ a0 =>
      let (kstates, aOut) := (hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pr.length) inRun tgt).run a0
      aOut.get parent = .element pns ptag pst pmg (pr ++ kstates.map VState.rootNode) ∧
      VStateKidsMatches tgt s aOut (kstates.map VState.rootNode) kstates)
    f childNs parent pns ptag pst pmg ?_ ?_ ?_ ?_ ks inTextRun pre domCs lo hi a
    (fun k hk => ⟨View.DomCleanEach_iff.1 hcl k hk, hk⟩) hlen
    (by simpa [View.renderEach_eq_map] using hbound) (by simpa [View.renderEach_eq_map] using hdep)
    hparLo hpreSub hpar (by simpa [View.renderEach_eq_map] using hdom)
  · intro _ _ _ _ _ hpar0; exact ⟨by simpa [hydrateViewKidsM, StateT.run, pure, StateT.pure] using hpar0, trivial⟩
  · intro c rest inRun pr _ _ a0 str aMid hcEq _ _ _ _ _ _ _ _ huNext hslotEq _ _ _ hih
    dsimp only at hcEq
    exact htextFinish c rest inRun inRun pr _ a0 aMid str ((View.textOf?_eq_render s c).trans (by rw [hcEq]; rfl)) huNext hslotEq hih
  · intro c rest pr tn _ _ _ a0 str aMid _ _ hcEq _ _ _ _ _ _ _ _ _ huNext hslotEq _ _ _ hih
    dsimp only at hcEq
    exact htextFinish c rest false true pr tn a0 aMid str ((View.textOf?_eq_render s c).trans (by rw [hcEq]; rfl)) huNext hslotEq hih
  · intro c rest inRun pr child domRest lo' mid hi' a0 f' hfEq htxt ⟨hcCl, hcMem⟩ hrestOk hlen' huIdx huNext hbd' hcDep hrestDep hparLo' hloMid hmidHi hiNext hpar0 hchildDom _ hcont
    subst hfEq
    have hcTxt : c.textOf? s = none := (View.textOf?_eq_render s c).trans htxt
    have hbdC : a0.nextId + htmlNodeCount (View.render c s) < UInt32.size := by simp only [List.map_cons, htmlListNodeCount] at hbd'; omega
    have hchildSpec := hydrateViewM_spec_of_matches childNs f' c s child a0 lo' mid hcCl hbdC hcDep hchildDom
      (hView c hcMem f' child a0 lo' mid hcCl hbdC hcDep hchildDom)
    have hdomS := (hydrateDomM_spec childNs f' (View.render c s) child a0 lo' mid hbdC hcDep hchildDom).2.2.1
    have haMidEqDom := hydrateViewM_eq_hydrateDomM hcCl s child a0
    dsimp only [StateT.run] at hchildSpec hdomS haMidEqDom
    cases hvm : hydrateViewM (m := StateM (DomArena msg)) c s child a0 with
    | mk kst aMid =>
        rw [hvm] at hchildSpec haMidEqDom; dsimp only at hchildSpec haMidEqDom
        rcases hchildSpec with ⟨hrootKst, haMidNext, haMidBound, hframeMid, hvalMid, _⟩
        have hchildSubMid : SubtreeInSet (f' + 1) aMid (fun k' => (lo' ≤ k' ∧ k' < mid) ∨ (a0.nextId ≤ k' ∧ k' < aMid.nextId)) child := by
          cases hdmMid : hydrateDomM (m := StateM (DomArena msg)) (View.render c s) child a0 with
          | mk _ aDomMid =>
              rw [hdmMid] at haMidEqDom hdomS; dsimp only at haMidEqDom hdomS
              exact haMidEqDom.1 ▸ (SubtreeInSet_frame (fun m _ => haMidEqDom.get_eq m) hdomS).1
        rcases hcont aMid haMidNext haMidBound hchildSubMid hframeMid with ⟨hih, hpreMid, hparMid, hdomMid⟩
        have hrestCl : View.DomCleanEach rest := View.DomCleanEach_iff.2 fun r hr => (hrestOk r hr).1
        have hrestDomSpec := hydrateDomKidsM_spec childNs parent pns ptag pst pmg (f' + 1)
          (View.renderEach rest s) false (pr ++ [child]) domRest mid hi' aMid
          (by rw [View.renderEach_eq_map, List.length_map]; simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen'; omega)
          (by rw [View.renderEach_eq_map]; simp only [List.map_cons, htmlListNodeCount] at hbd'; omega)
          (by rw [View.renderEach_eq_map]; exact hrestDep) (by omega) hpreMid hparMid (by rw [View.renderEach_eq_map]; exact hdomMid)
        rcases hrestDomSpec with ⟨_, _, _, _, _, hfrDomR, _, _⟩
        dsimp only [StateT.run] at hih ⊢
        dsimp only [hydrateViewKidsM]; rw [hcTxt]
        dsimp only [bind, StateT.bind, pure, StateT.pure, MonadDom.childAt]
        rw [hpar0, huIdx]; dsimp only; rw [getD_append_right child 0 pr domRest, hvm]; dsimp only
        rw [show UInt32.ofNat (pr ++ [child]).length = UInt32.ofNat pr.length + 1 from by rw [List.length_append, List.length_singleton, huNext]] at hih hfrDomR
        have hrestEq := hydrateViewKidsM_eq_hydrateDomKidsM hrestCl parent s (UInt32.ofNat pr.length + 1) false aMid
        dsimp only [StateT.run] at hrestEq hfrDomR
        cases hrest : hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pr.length + 1) false rest aMid with
        | mk ksR aOut =>
            cases hdrest : hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pr.length + 1) false (View.renderEach rest s) aMid with
            | mk _ aDomOut =>
                rw [hrest, hdrest] at hrestEq; rw [hdrest] at hfrDomR; rw [hrest] at hih; dsimp only at hrestEq hfrDomR hih
                have hmKstOut : VStateMatches c s aOut child kst :=
                  VStateMatches_frame (fun m hm => (hrestEq.get_eq m).trans (hfrDomR m
                    (fun heq => by rw [heq] at hm; rcases hm with h1 | h2 <;> omega)
                    (hm.elim (fun h1 => .inl h1.2) (fun h2 => .inr (Nat.le_trans hiNext h2.1)))
                    (hm.elim (fun h1 => by omega) (fun h2 => h2.2))))
                    (hrootKst ▸ hvalMid.1) (hrootKst ▸ hvalMid.2)
                dsimp only [List.map_cons, VStateKidsMatches]; rw [hrootKst]
                exact ⟨by simpa [List.append_assoc] using hih.1, rfl, hmKstOut, hih.2⟩

private theorem hydrateViewM_matches {σ msg : Type} (ns : String) (f : Nat) (v : View σ msg) (s : σ)
    (root : Dom.Node) (a : DomArena msg) (lo hi : Nat) (hc : View.DomClean v)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size)
    (hdep : htmlDepth (View.render v s) ≤ f + 1)
    (hdom : HydratableDom (f + 1) ns (View.render v s) a lo hi root) :
    let (vst, aOut) := (hydrateViewM (m := StateM (DomArena msg)) v s root).run a
    vst.rootNode = root ∧ VStateMatches v s aOut root vst := by
  induction v using View.ind generalizing ns f root a lo hi with
  | text _ | static _ => exact ⟨rfl, rfl⟩
  | dyn _ | dynNode _ => exact ⟨rfl, rfl, rfl⟩
  | memo _ => exact ⟨rfl, rfl, rfl, rfl⟩
  | ifElse c y n ihy ihn =>
      rcases hc with ⟨hyCl, hnCl⟩
      dsimp only [hydrateViewM, StateT.run]
      cases hcs : c s <;>
        (simp only [hcs, Bool.false_eq_true, ↓reduceIte, View.render, bind, StateT.bind, pure, StateT.pure] at hbound hdep hdom ⊢
         have hr := by first | exact ihn ns f root a lo hi hnCl hbound hdep hdom | exact ihy ns f root a lo hi hyCl hbound hdep hdom
         dsimp only [StateT.run] at hr
         cases hRun : hydrateViewM (m := StateM (DomArena msg)) _ s root a with
         | mk inner aOut =>
             rw [hRun] at hr; dsimp only at hr ⊢
             exact ⟨hr.1, hcs.symm, by simpa [hcs] using hr.2⟩)
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      cases tmpl? with
      | some _ => exact False.elim hc
      | none =>
          rcases hc with ⟨_, hrowsCl⟩
          dsimp only [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
          cases applyAttrsM (m := StateM (DomArena msg)) root (attrs.map (VAttr.eval s))
              (a.modifyElemState root fun st => { st with clicks := [], inputs := [] }) with
          | mk _ a1 =>
              dsimp only
              cases seedRowsM (m := StateM (DomArena msg)) s!"§{root}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a1 with
              | mk _ a2 =>
                  dsimp only; rw [Html.map_prefixSignals_of_DomCleanList _ (hrowsCl.2.1 s)]
                  cases hydrateListRowsM (m := StateM (DomArena msg)) root 0 (rowsHtml s) a2 with
                  | mk _ _ => exact ⟨rfl, rfl, rfl, rfl⟩
  | element tag attrs kids ihk =>
      rcases hc with ⟨haCl, hkidsCl⟩
      rcases hdom with ⟨_, _, _, st, prev, domCs, hget, hm, hns, _, hownF⟩
      rcases hownF (haCl.1 s) with ⟨mid, hmidGt, hk⟩
      have hattrs := applyAttrsM_existing_element a root
        (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
        { st with clicks := [], inputs := [] } prev domCs (attrs.map (VAttr.eval s)) hm hns
      rcases hattrs with ⟨st', ha2Get, _, _⟩
      let a2 := (applyAttrsM (m := StateM (DomArena msg)) root (attrs.map (VAttr.eval s))
        (a.set root (.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
          { st with clicks := [], inputs := [] } prev domCs))).2
      have ha2Next : a2.nextId = a.nextId := applyAttrsM_nextId a root (attrs.map (VAttr.eval s)) _
      have hkFrame : HydratableDomList f (Dom.childNsOf ns tag) (coalesceTextRun (View.renderEach kids s)) a2 mid hi domCs :=
        HydratableDomList_frame f (Dom.childNsOf ns tag) (coalesceTextRun (View.renderEach kids s)) a a2 mid hi domCs
          (by rw [ha2Next]; exact Nat.le_refl _)
          (fun m hm1 _ => applyAttrsM_get_ne a root (attrs.map (VAttr.eval s)) _ m (fun heq => by rw [heq] at hm1; omega)) hk
      have hvk := viewKidsMatches_step f (Dom.childNsOf ns tag) root
        (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag st'
        ((normalizeAttrs (attrs.map (VAttr.eval s))).filterMap managedAttrName)
        kids s false [] domCs mid hi a2 (fun k hkMem f' r a0 lo0 hi0 => ihk k hkMem (Dom.childNsOf ns tag) f' r a0 lo0 hi0)
        hkidsCl
        (by have hcnt := list_length_le_htmlListNodeCount (View.renderEach kids s); have hlen : (View.renderEach kids s).length = kids.length := (by rw [View.renderEach_eq_map, List.length_map]); simp only [View.render, htmlNodeCount] at hbound; simp only [List.length_nil]; omega)
        (by simp only [View.render, htmlNodeCount] at hbound; omega)
        (by simp only [View.render, htmlDepth] at hdep; omega)
        hmidGt (fun _ hm => nomatch hm) ha2Get hkFrame
      have hclearMod : a.modifyElemState root (fun st : SpecElemState msg => { st with clicks := [], inputs := [] }) =
          a.set root (.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
            { st with clicks := [], inputs := [] } prev domCs) := by simp [DomArena.modifyElemState, DomArena.modify, hget]
      have ha2Run : applyAttrsM (m := StateM (DomArena msg)) root (attrs.map (VAttr.eval s))
          (a.set root (.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
            { st with clicks := [], inputs := [] } prev domCs)) = ((), a2) := Prod.ext rfl rfl
      dsimp only [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure] at hvk ⊢
      rw [hclearMod, ha2Run]; dsimp only
      cases hkidsRun : hydrateViewKidsM (m := StateM (DomArena msg)) root s 0 false kids a2 with
      | mk kstates aOut =>
          rw [show (UInt32.ofNat ([] : List Dom.Node).length) = 0 from rfl, hkidsRun] at hvk
          exact ⟨rfl, rfl, _, tag, st', (normalizeAttrs (attrs.map (VAttr.eval s))).filterMap managedAttrName,
            kstates.map VState.rootNode, hvk.1, hvk.2⟩

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
  hydrateViewM_spec_of_matches ns f v s root a lo hi hc hbound hdep hdom
    (hydrateViewM_matches ns f v s root a lo hi hc hbound hdep hdom)

end Qed
