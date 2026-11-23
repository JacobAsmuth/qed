import Qed.Proofs.Hydration.Dom
import Qed.Proofs.ViewPatch.VState

namespace Qed

section
variable {σ msg : Type}

private theorem View.textOf?_eq_render (s : σ) : ∀ (v : View σ msg), v.textOf? s = (View.render v s).textOf?
  | .text _ | .dyn _ | .static _ | .dynNode _ | .memo _ | .element .. | .keyedList .. => rfl
  | .ifElse c y n => by cases hc : c s <;> simp [View.textOf?, View.render, hc, View.textOf?_eq_render s y, View.textOf?_eq_render s n]

private theorem hasMoreViewText_eq_renderEach (s : σ) : ∀ (ks : List (View σ msg)), hasMoreViewText s ks = hasMoreText (View.renderEach ks s)
  | [] => rfl
  | k :: rest => by dsimp only [hasMoreViewText, View.renderEach, hasMoreText]; rw [View.textOf?_eq_render s k]; cases (View.render k s).textOf? with | none => rfl | some str => by_cases he : str = "" <;> simp [he, hasMoreViewText_eq_renderEach s rest]

private theorem hydrateViewM_of_textOf? :
    ∀ {v : View σ msg} {s : σ} {str : String}, v.textOf? s = some str → ∀ (kn : Dom.Node) (a : DomArena msg),
      let (vst, a') := (hydrateViewM (m := StateM (DomArena msg)) v s kn).run a
      a' = a ∧ vst.rootNode = kn ∧ ∀ aAny : DomArena msg, VStateMatches v s aAny kn vst
  | .text _, _, _, _, _, _ | .static (.text _), _, _, _, _, _ => ⟨rfl, rfl, fun _ => rfl⟩
  | .dyn _, _, _, _, _, _ => ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
  | .static (.element ..), _, _, h, _, _ | .element .., _, _, h, _, _ | .keyedList .., _, _, h, _, _ => by simp [View.textOf?, Html.textOf?] at h
  | .dynNode _, _, _, h, _, _ | .memo _, _, _, h, _, _ => by simp [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, textOf_eq_some_iff.1 h, hydrateDomM, VState.rootNode, VStateMatches]
  | .ifElse c y n, s, _, h, kn, a => by
      simp only [View.textOf?] at h; cases hc : c s <;> (
        simp only [hc, ↓reduceIte, Bool.false_eq_true] at h; have ih := hydrateViewM_of_textOf? h kn a; dsimp only [StateT.run] at ih
        rcases hy : hydrateViewM (m := StateM (DomArena msg)) _ s kn a with ⟨_, _⟩; rw [hy] at ih
        simp [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, hc, hy, VState.rootNode, VStateMatches, ih.1, ih.2.1, ih.2.2])

private theorem hydrateTextSlotM_metaIndep (parent : Dom.Node) (index : UInt32) (inRun : Bool) (s : String) (more : Unit → Bool) :
    DomArena.MetaIndep (hydrateTextSlotM (m := StateM (DomArena msg)) parent index inRun s more) := fun _ _ _ _ _ => by
  dsimp only [hydrateTextSlotM]; split <;> first | rfl | (split <;> first | rfl | (dsimp only [bind, StateT.bind, pure, StateT.pure, MonadDom.childAt, DomArena.get, DomArena.withMeta]; cases more () <;> rfl))

mutual
  private theorem hydrateDomM_metaIndep : (h : Html msg) → (node : Dom.Node) → DomArena.MetaIndep (hydrateDomM (m := StateM (DomArena msg)) h node)
    | .text _, _ => .pure ()
    | .element _ attrs cs, node => by dsimp only [hydrateDomM]; refine .bind (fun _ _ _ _ _ => rfl) fun _ => .bind (applyAttrsM_metaIndep node attrs) fun _ => ?_; cases ownsChildren attrs; exact hydrateDomKidsM_metaIndep cs node 0 false; exact .pure ()

  private theorem hydrateDomKidsM_metaIndep : (cs : List (Html msg)) → (node : Dom.Node) → (i : UInt32) → (inRun : Bool) → DomArena.MetaIndep (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs)
    | [], _, _, _ => .pure ()
    | c :: rest, node, i, inRun => by
        dsimp only [hydrateDomKidsM]; cases c.textOf? with
        | none => exact .bind (fun _ _ _ _ _ => rfl) fun cn => .bind (hydrateDomM_metaIndep c cn) fun _ => hydrateDomKidsM_metaIndep rest node (i + 1) false
        | some str => exact .bind (hydrateTextSlotM_metaIndep node i inRun str (fun () => hasMoreText rest)) fun r => hydrateDomKidsM_metaIndep rest node (i + 1) r.2
end

private theorem hydrateListRowsM_eq_hydrateDomKidsM (node : Dom.Node) :
    ∀ (i : UInt32) (rs : List (Html msg)), (∀ r ∈ rs, r.textOf? = none) → ∀ (a : DomArena msg),
      ((hydrateListRowsM (m := StateM (DomArena msg)) node i rs).run a).2 = ((hydrateDomKidsM (m := StateM (DomArena msg)) node i false rs).run a).2
  | _, [], _, _ => rfl
  | i, r :: rs, hr, a => by
      dsimp only [hydrateListRowsM, hydrateDomKidsM, StateT.run]; rw [hr r (.head _)]; dsimp only [bind, StateT.bind, pure, StateT.pure]
      rcases hydrateDomM (m := StateM (DomArena msg)) r (MonadDom.childAt (m := StateM (DomArena msg)) node i a).1 a with ⟨_, a2⟩
      exact hydrateListRowsM_eq_hydrateDomKidsM node (i + 1) rs (fun x hx => hr x (.tail _ hx)) a2

private theorem hydrateViewKidsM_eq_hydrateDomKidsM_of (ks : List (View σ msg)) (node : Dom.Node) (s : σ)
    (hView : ∀ k ∈ ks, View.DomClean k → ∀ (cn : Dom.Node) (a : DomArena msg),
      ((hydrateViewM (m := StateM (DomArena msg)) k s cn).run a).2.SameDom ((hydrateDomM (m := StateM (DomArena msg)) (View.render k s) cn).run a).2) :
    View.DomCleanEach ks → ∀ (i : UInt32) (inRun : Bool) (a : DomArena msg),
      ((hydrateViewKidsM (m := StateM (DomArena msg)) node s i inRun ks).run a).2.SameDom ((hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun (View.renderEach ks s)).run a).2 := by
  induction ks with
  | nil => exact fun _ _ _ a => DomArena.SameDom.refl a
  | cons k rest ih =>
      intro ⟨hk, hrest⟩ i inRun a; dsimp only [hydrateViewKidsM, View.renderEach, hydrateDomKidsM, StateT.run]; rw [← View.textOf?_eq_render s k]
      cases htxt : k.textOf? s with
      | some str =>
          dsimp only [bind, StateT.bind, pure, StateT.pure]; simp only [hasMoreViewText_eq_renderEach]
          rcases hydrateTextSlotM (m := StateM (DomArena msg)) node i inRun str (fun () => hasMoreText (View.renderEach rest s)) a with ⟨slot, a1⟩
          have hm := hydrateViewM_of_textOf? htxt slot.1 a1; dsimp only [StateT.run] at hm ⊢
          rcases hvm : hydrateViewM (m := StateM (DomArena msg)) k s slot.1 a1 with ⟨_, _⟩; rw [hvm] at hm; dsimp only at hm ⊢; rw [hm.1]
          have hkEq := ih (fun x hx => hView x (.tail _ hx)) hrest (i + 1) slot.2 a1; dsimp only [StateT.run] at hkEq
          rcases hkr : hydrateViewKidsM (m := StateM (DomArena msg)) node s (i + 1) slot.2 rest a1 with ⟨_, _⟩; rw [hkr] at hkEq; exact hkEq
      | none =>
          dsimp only [bind, StateT.bind, pure, StateT.pure]; have heq := hView k (.head _) hk (MonadDom.childAt (m := StateM (DomArena msg)) node i a).1 a; dsimp only [StateT.run, MonadDom.childAt] at heq
          rcases hvm : hydrateViewM (m := StateM (DomArena msg)) k s _ a with ⟨_, a2⟩; rcases hdm : hydrateDomM (m := StateM (DomArena msg)) (k.render s) _ a with ⟨_, _⟩
          rw [hvm, hdm] at heq; dsimp only at heq ⊢; have hkEq := ih (fun x hx => hView x (.tail _ hx)) hrest (i + 1) false a2; dsimp only [StateT.run] at hkEq
          rcases hkRun : hydrateViewKidsM (m := StateM (DomArena msg)) node s (i + 1) false rest a2 with ⟨_, _⟩
          rw [hkRun] at hkEq; exact hkEq.trans ((hydrateDomKidsM_metaIndep (View.renderEach rest s) node (i + 1) false).sameDom heq)

theorem hydrateViewM_eq_hydrateDomM {v : View σ msg} (hcl : View.DomClean v) (s : σ) (node : Dom.Node) (a : DomArena msg) :
    ((hydrateViewM (m := StateM (DomArena msg)) v s node).run a).2.SameDom ((hydrateDomM (m := StateM (DomArena msg)) (View.render v s) node).run a).2 := by
  induction v using View.ind generalizing node a with
  | text _ | dyn _ => exact DomArena.SameDom.refl a
  | static h => cases h <;> (dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]; cases hydrateDomM (m := StateM (DomArena msg)) _ _ _; exact DomArena.SameDom.refl _)
  | dynNode _ | memo _ => dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]; cases hydrateDomM (m := StateM (DomArena msg)) _ node a; exact DomArena.SameDom.refl _
  | ifElse c y no ihy ihn =>
      rcases hcl with ⟨hy, hn⟩; cases hcs : c s <;> (
        dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]; rw [hcs]; simp only [Bool.false_eq_true, ↓reduceIte]
        rcases hrun : hydrateViewM (m := StateM (DomArena msg)) _ s node a with ⟨_, _⟩
        first | (have h := ihn hn node a; dsimp only [StateT.run] at h; rw [hrun] at h; exact h) | (have h := ihy hy node a; dsimp only [StateT.run] at h; rw [hrun] at h; exact h))
  | element tag attrs kids ihk =>
      rcases hcl with ⟨ha, hks⟩; dsimp only [hydrateViewM, View.render, hydrateDomM, StateT.run, bind, StateT.bind, pure, StateT.pure]; rw [ha.1 s, Bool.not_false, if_pos rfl]
      rcases applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s)) (a.modifyElemState node fun st => { st with clicks := [], inputs := [] }) with ⟨_, a1⟩
      have h := hydrateViewKidsM_eq_hydrateDomKidsM_of kids node s (fun k hk hkCl cn a' => ihk k hk hkCl cn a') hks 0 false a1; dsimp only [StateT.run] at h
      cases hydrateViewKidsM (m := StateM (DomArena msg)) node s 0 false kids a1; exact h
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      cases tmpl? with | some _ => exact False.elim hcl | none =>
      rcases hcl with ⟨ha, hrows⟩; dsimp only [hydrateViewM, View.render, hydrateDomM, StateT.run, bind, StateT.bind, pure, StateT.pure]; rw [ha.1 s, Bool.not_false, if_pos rfl]
      rcases applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s)) (a.modifyElemState node fun st => { st with clicks := [], inputs := [] }) with ⟨_, a1⟩
      dsimp only; rcases hseed : seedRowsM (m := StateM (DomArena msg)) s!"§{node}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a1 with ⟨_, a2⟩
      have hsd := seedRowsM_sameDom s!"§{node}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a1; dsimp only [StateT.run] at hsd; rw [hseed] at hsd
      dsimp only; rw [Html.map_prefixSignals_of_DomCleanList _ (hrows.2.1 s)]
      have hlist := hydrateListRowsM_eq_hydrateDomKidsM node 0 (rowsHtml s) (hrows.2.2.1 s) a2; dsimp only [StateT.run] at hlist
      rcases hl : hydrateListRowsM (m := StateM (DomArena msg)) node 0 (rowsHtml s) a2 with ⟨_, _⟩; rw [hl] at hlist; dsimp only at hlist ⊢; rw [hlist]
      exact (hydrateDomKidsM_metaIndep (rowsHtml s) node 0 false).sameDom hsd

private theorem View.renderEach_eq_map (s : σ) : ∀ ks : List (View σ msg), View.renderEach ks s = ks.map (fun v => View.render v s)
  | [] => rfl | _ :: rest => congrArg (List.cons _) (View.renderEach_eq_map s rest)

private theorem View.DomCleanEach_iff : ∀ {ks : List (View σ msg)}, View.DomCleanEach ks ↔ ∀ k ∈ ks, View.DomClean k
  | [] => ⟨(fun _ _ h => nomatch h), fun _ => trivial⟩
  | _ :: _ => ⟨fun ⟨h1, h2⟩ _ hm => (List.mem_cons.1 hm).elim (· ▸ h1) (View.DomCleanEach_iff.1 h2 _), fun h => ⟨h _ (.head _), View.DomCleanEach_iff.2 fun x hx => h x (.tail _ hx)⟩⟩

private theorem hydrateViewM_spec_of_matches (ns : String) (f : Nat) (v : View σ msg) (s : σ) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat) (hc : View.DomClean v)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ f + 1) (hdom : HydratableDom (f + 1) ns (View.render v s) a lo hi root)
    (hmt : let (vst, aOut) := (hydrateViewM (m := StateM (DomArena msg)) v s root).run a; vst.rootNode = root ∧ VStateMatches v s aOut root vst) :
    let (vst, aOut) := (hydrateViewM (m := StateM (DomArena msg)) v s root).run a
    vst.rootNode = root ∧ a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
    (∀ m : Dom.Node, (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    VStateValid (f + 1) ns v s aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) vst ∧
    DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns (View.render v s)) ∧ SubtreeInSet (f + 1) aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) root := by
  have hdomSpec := hydrateDomM_spec ns f (View.render v s) root a lo hi hbound hdep hdom
  have hviewEq := hydrateViewM_eq_hydrateDomM hc s root a; dsimp only [StateT.run] at hdomSpec hviewEq hmt ⊢
  rcases hvm : hydrateViewM (m := StateM (DomArena msg)) v s root a with ⟨vst, aOut⟩; rcases hdm : hydrateDomM (m := StateM (DomArena msg)) (View.render v s) root a with ⟨_, aDom⟩
  rw [hvm] at hviewEq hmt; rw [hdm] at hviewEq hdomSpec; dsimp only at hviewEq hdomSpec hmt ⊢; rcases hdomSpec with ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨hmt.1, hviewEq.1 ▸ h1, hviewEq.1 ▸ h2, fun m hmOut hmLt => (hviewEq.get_eq m).trans (h4 m hmOut hmLt),
    ⟨hmt.1.symm ▸ CleanDomSubtree_frame (fun m _ => hviewEq.get_eq m) (hviewEq.1 ▸ h6 (View.DomClean_render hc s)), hmt.1.symm ▸ hmt.2⟩,
    hviewEq.readDomTree_eq (f + 1) root ▸ h5, hviewEq.1 ▸ (SubtreeInSet_frame (fun m _ => hviewEq.get_eq m) h3).1⟩

private theorem viewKidsMatches_step (f : Nat) (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (ks : List (View σ msg)) (s : σ) (inTextRun : Bool) (pre domCs : List Dom.Node) (lo hi : Nat) (a : DomArena msg)
    (hView : ∀ k ∈ ks, ∀ (f' : Nat) (root : Dom.Node) (a0 : DomArena msg) (lo0 hi0 : Nat), View.DomClean k →
      a0.nextId + htmlNodeCount (View.render k s) < UInt32.size → htmlDepth (View.render k s) ≤ f' + 1 → HydratableDom (f' + 1) childNs (View.render k s) a0 lo0 hi0 root →
      let (vst, aOut) := (hydrateViewM (m := StateM (DomArena msg)) k s root).run a0; vst.rootNode = root ∧ VStateMatches k s aOut root vst)
    (hcl : View.DomCleanEach ks) (hlen : pre.length + ks.length < UInt32.size) (hbound : a.nextId + htmlListNodeCount (View.renderEach ks s) < UInt32.size)
    (hdep : htmlListDepth (View.renderEach ks s) ≤ f) (hparLo : parent.toNat < lo)
    (hpreSub : ∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet f a Sx x)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ domCs)) (hdom : HydratableDomList f childNs (if inTextRun then dropCurrentTextRun (View.renderEach ks s) else coalesceTextRun (View.renderEach ks s)) a lo hi domCs) :
    let (kstates, aOut) := (hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pre.length) inTextRun ks).run a
    aOut.get parent = .element pns ptag pst pmg (pre ++ kstates.map VState.rootNode) ∧ VStateKidsMatches ks s aOut (kstates.map VState.rootNode) kstates := by
  refine hydrateKids_ind (toHtml := fun v => View.render v s) (ItemOk := fun k => View.DomClean k ∧ k ∈ ks)
    (Post := fun tgt inRun pr _ _ a0 => let (kstates, aOut) := (hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pr.length) inRun tgt).run a0
      aOut.get parent = .element pns ptag pst pmg (pr ++ kstates.map VState.rootNode) ∧ VStateKidsMatches tgt s aOut (kstates.map VState.rootNode) kstates)
    f childNs parent pns ptag pst pmg ?_ ?_ ?_ ks inTextRun pre domCs lo hi a (fun k hk => ⟨View.DomCleanEach_iff.1 hcl k hk, hk⟩) hlen
    (by simpa [View.renderEach_eq_map] using hbound) (by simpa [View.renderEach_eq_map] using hdep) hparLo hpreSub hpar (by simpa [View.renderEach_eq_map] using hdom)
  · intro _ _ _ _ _ hpar0; exact ⟨by simpa [hydrateViewKidsM, StateT.run, pure, StateT.pure] using hpar0, trivial⟩
  · intro c rest inRun inRun' pr kn _ _ _ a0 str aMid _ hcEq _ _ _ _ _ _ huNext hslotEq _ _ _ _ _ hih
    have htxt : c.textOf? s = some str := (View.textOf?_eq_render s c).trans (by dsimp only at hcEq; rw [hcEq]; rfl)
    dsimp only [hydrateViewKidsM, StateT.run] at hih ⊢; rw [htxt]; simp only [hasMoreViewText_eq_renderEach, View.renderEach_eq_map]; dsimp only [bind, StateT.bind, pure, StateT.pure]; rw [hslotEq]; dsimp only
    have hvk := hydrateViewM_of_textOf? htxt kn aMid; dsimp only [StateT.run] at hvk
    rcases hvm : hydrateViewM (m := StateM (DomArena msg)) c s kn aMid with ⟨_, _⟩; rw [hvm] at hvk; dsimp only at hvk; rcases hvk with ⟨ha2Eq, hrootKst, hmatchKst⟩; rw [ha2Eq]; dsimp only
    rw [show UInt32.ofNat (pr ++ [kn]).length = UInt32.ofNat pr.length + 1 from by rw [List.length_append, List.length_singleton, huNext]] at hih
    rcases hrest : hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pr.length + 1) inRun' rest aMid with ⟨_, aOut⟩
    rw [hrest] at hih; dsimp only [List.map_cons, VStateKidsMatches] at hih ⊢; rw [hrootKst]; exact ⟨by simpa [List.append_assoc] using hih.1, rfl, hmatchKst aOut, hih.2⟩
  · intro c rest inRun pr child domRest lo' mid hi' a0 f' hfEq htxt ⟨hcCl, hcMem⟩ hrestOk hlen' huIdx huNext hbd' hcDep hrestDep hparLo' hloMid hmidHi hiNext hpar0 hchildDom _ hcont
    subst hfEq; have hcTxt : c.textOf? s = none := (View.textOf?_eq_render s c).trans htxt
    have hbdC : a0.nextId + htmlNodeCount (View.render c s) < UInt32.size := by simp only [List.map_cons, htmlListNodeCount] at hbd'; omega
    have hchildSpec := hydrateViewM_spec_of_matches childNs f' c s child a0 lo' mid hcCl hbdC hcDep hchildDom (hView c hcMem f' child a0 lo' mid hcCl hbdC hcDep hchildDom)
    dsimp only [StateT.run] at hchildSpec; rcases hvm : hydrateViewM (m := StateM (DomArena msg)) c s child a0 with ⟨kst, aMid⟩
    rw [hvm] at hchildSpec; rcases hchildSpec with ⟨hrootKst, haMidNext, haMidBound, hframeMid, hvalMid, _, hchildSubMid⟩
    rcases hcont aMid haMidNext haMidBound hchildSubMid hframeMid with ⟨hih, hpreMid, hparMid, hdomMid⟩
    rcases hydrateDomKidsM_spec childNs parent pns ptag pst pmg (f' + 1) (View.renderEach rest s) false (pr ++ [child]) domRest mid hi' aMid
      (by rw [View.renderEach_eq_map, List.length_map]; simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen'; omega)
      (by rw [View.renderEach_eq_map]; simp only [List.map_cons, htmlListNodeCount] at hbd'; omega) (by rw [View.renderEach_eq_map]; exact hrestDep) (by omega) hpreMid hparMid (by rw [View.renderEach_eq_map]; exact hdomMid) with ⟨_, _, _, _, _, hfrDomR, _, _⟩
    dsimp only [hydrateViewKidsM, StateT.run] at hih ⊢; rw [hcTxt]; dsimp only [bind, StateT.bind, pure, StateT.pure, MonadDom.childAt]; rw [hpar0, huIdx]; dsimp only; rw [getD_append_right child 0 pr domRest, hvm]; dsimp only
    rw [show UInt32.ofNat (pr ++ [child]).length = UInt32.ofNat pr.length + 1 from by rw [List.length_append, List.length_singleton, huNext]] at hih hfrDomR
    have hrestEq := hydrateViewKidsM_eq_hydrateDomKidsM_of rest parent s (fun _ _ h => hydrateViewM_eq_hydrateDomM h s) (View.DomCleanEach_iff.2 fun r hr => (hrestOk r hr).1) (UInt32.ofNat pr.length + 1) false aMid
    dsimp only [StateT.run] at hrestEq hfrDomR; rcases hrest : hydrateViewKidsM (m := StateM (DomArena msg)) parent s (UInt32.ofNat pr.length + 1) false rest aMid with ⟨_, aOut⟩
    rcases hdrest : hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pr.length + 1) false (View.renderEach rest s) aMid with ⟨_, _⟩
    rw [hrest, hdrest] at hrestEq; rw [hdrest] at hfrDomR; rw [hrest] at hih; dsimp only [List.map_cons, VStateKidsMatches] at hrestEq hfrDomR hih ⊢; rw [hrootKst]
    exact ⟨by simpa [List.append_assoc] using hih.1, rfl,
      VStateMatches_frame (fun m hm => (hrestEq.get_eq m).trans (hfrDomR m (fun e => by rw [e] at hm; rcases hm with h1 | h2 <;> omega) (hm.elim (fun h1 => .inl h1.2) fun h2 => .inr (Nat.le_trans hiNext h2.1)) (hm.elim (fun _ => by omega) (·.2)))) (hrootKst ▸ hvalMid.1) (hrootKst ▸ hvalMid.2), hih.2⟩

private theorem hydrateViewM_matches (ns : String) (f : Nat) (v : View σ msg) (s : σ) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat) (hc : View.DomClean v)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ f + 1) (hdom : HydratableDom (f + 1) ns (View.render v s) a lo hi root) :
    let (vst, aOut) := (hydrateViewM (m := StateM (DomArena msg)) v s root).run a
    vst.rootNode = root ∧ VStateMatches v s aOut root vst := by
  induction v using View.ind generalizing ns f root a lo hi with
  | text _ | static _ => exact ⟨rfl, rfl⟩
  | dyn _ | dynNode _ => exact ⟨rfl, rfl, rfl⟩
  | memo _ => exact ⟨rfl, rfl, rfl, rfl⟩
  | ifElse c y n ihy ihn =>
      rcases hc with ⟨hyCl, hnCl⟩; dsimp only [hydrateViewM, StateT.run]; cases hcs : c s <;> (
        simp only [hcs, Bool.false_eq_true, ↓reduceIte, View.render, bind, StateT.bind, pure, StateT.pure] at hbound hdep hdom ⊢
        have hr := by first | exact ihn ns f root a lo hi hnCl hbound hdep hdom | exact ihy ns f root a lo hi hyCl hbound hdep hdom
        dsimp only [StateT.run] at hr; rcases hRun : hydrateViewM (m := StateM (DomArena msg)) _ s root a with ⟨_, _⟩; rw [hRun] at hr; exact ⟨hr.1, hcs.symm, by simpa [hcs] using hr.2⟩)
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      cases tmpl? with | some _ => exact False.elim hc | none =>
      rcases hc with ⟨_, hrowsCl⟩; dsimp only [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure]
      rcases applyAttrsM (m := StateM (DomArena msg)) root (attrs.map (VAttr.eval s)) (a.modifyElemState root fun st => { st with clicks := [], inputs := [] }) with ⟨_, a1⟩
      dsimp only; rcases seedRowsM (m := StateM (DomArena msg)) s!"§{root}§" (rowSig s (disambiguateKeys (keys s))) (rowEv s (disambiguateKeys (keys s))) (marks s) #[] #[] a1 with ⟨_, a2⟩
      dsimp only; rw [Html.map_prefixSignals_of_DomCleanList _ (hrowsCl.2.1 s)]; cases hydrateListRowsM (m := StateM (DomArena msg)) root 0 (rowsHtml s) a2; exact ⟨rfl, rfl, rfl, rfl⟩
  | element tag attrs kids ihk =>
      rcases hc with ⟨haCl, hkidsCl⟩; rcases hdom with ⟨_, _, _, st, prev, domCs, hget, hm, hns, _, hownF⟩; rcases hownF (haCl.1 s) with ⟨mid, hmidGt, hk⟩
      let a2 := (applyAttrsM (m := StateM (DomArena msg)) root (attrs.map (VAttr.eval s)) (a.modifyElemState root fun st => { st with clicks := [], inputs := [] })).2
      rcases hydrateElemAttrs_step a root ns tag st prev domCs (attrs.map (VAttr.eval s)) hget hm hns with ⟨st', ha2Get, _, _, ha2Next, ha2Outside⟩; have ha2Next' : a2.nextId = a.nextId := ha2Next
      have hvk := viewKidsMatches_step f (Dom.childNsOf ns tag) root (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag st'
        ((normalizeAttrs (attrs.map (VAttr.eval s))).filterMap managedAttrName) kids s false [] domCs mid hi a2 (fun k hkMem => ihk k hkMem (Dom.childNsOf ns tag)) hkidsCl
        (by have := list_length_le_htmlListNodeCount (View.renderEach kids s); have : (View.renderEach kids s).length = kids.length := (by rw [View.renderEach_eq_map, List.length_map]); simp only [View.render, htmlNodeCount] at hbound; simp; omega)
        (by simp only [View.render, htmlNodeCount] at hbound; omega) (by simp only [View.render, htmlDepth] at hdep; omega) hmidGt (fun _ hm => nomatch hm) ha2Get
        (HydratableDomList_frame f (Dom.childNsOf ns tag) (coalesceTextRun (View.renderEach kids s)) a a2 mid hi domCs (by omega) (fun m hm1 _ => ha2Outside m fun e => by rw [e] at hm1; omega) hk)
      dsimp only [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, MonadDom.clearHandlers] at hvk ⊢
      rw [show applyAttrsM (m := StateM (DomArena msg)) root (attrs.map (VAttr.eval s)) (a.modifyElemState root fun st => { st with clicks := [], inputs := [] }) = ((), a2) from rfl]; dsimp only
      rcases hkidsRun : hydrateViewKidsM (m := StateM (DomArena msg)) root s 0 false kids a2 with ⟨kstates, _⟩
      rw [show (UInt32.ofNat ([] : List Dom.Node).length) = 0 from rfl, hkidsRun] at hvk; exact ⟨rfl, rfl, _, tag, st', _, kstates.map VState.rootNode, hvk.1, hvk.2⟩

theorem hydrateViewM_spec (ns : String) (f : Nat) (v : View σ msg) (s : σ) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat) (hc : View.DomClean v)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ f + 1) (hdom : HydratableDom (f + 1) ns (View.render v s) a lo hi root) :
    let (vst, aOut) := (hydrateViewM (m := StateM (DomArena msg)) v s root).run a
    vst.rootNode = root ∧ a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
    (∀ m : Dom.Node, (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    VStateValid (f + 1) ns v s aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) vst ∧
    DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns (View.render v s)) :=
  let h := hydrateViewM_spec_of_matches ns f v s root a lo hi hc hbound hdep hdom (hydrateViewM_matches ns f v s root a lo hi hc hbound hdep hdom)
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

end
end Qed
