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
      let (vst, a') := (hydrateViewM (m := ArenaM msg) v s kn).run a; a' = a ∧ vst.rootNode = kn ∧ ∀ aAny : DomArena msg, VStateMatches v s aAny kn vst
  | .text _, _, _, _, _, _ | .static (.text _), _, _, _, _, _ => ⟨rfl, rfl, fun _ => rfl⟩
  | .dyn _, _, _, _, _, _ => ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
  | .static (.element ..), _, _, h, _, _ | .element .., _, _, h, _, _ | .keyedList .., _, _, h, _, _ => by simp [View.textOf?, Html.textOf?] at h
  | .dynNode _, _, _, h, _, _ | .memo _, _, _, h, _, _ => by simp [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure, textOf_eq_some_iff.1 h, hydrateDomM, VState.rootNode, VStateMatches]
  | .ifElse c y n, s, _, h, kn, a => by
      simp only [View.textOf?] at h; cases hc : c s <;> (simp only [hc, ↓reduceIte, Bool.false_eq_true] at h; have ⟨h1, h2, h3⟩ := hydrateViewM_of_textOf? h kn a; simp [hydrateViewM, StateT.run, Functor.map, StateT.map, hc, VState.rootNode, VStateMatches, h1, h2, h3])
private theorem hydrateTextSlotM_metaIndep (parent : Dom.Node) (index : UInt32) (inRun : Bool) (s : String) (more : Unit → Bool) :
    DomArena.MetaIndep (hydrateTextSlotM (m := ArenaM msg) parent index inRun s more) := fun _ _ _ _ _ => by
  dsimp only [hydrateTextSlotM]; split <;> first | rfl | (split <;> first | rfl | (dsimp only [bind, StateT.bind, pure, StateT.pure, MonadDom.childAt, DomArena.get, DomArena.withMeta]; cases more () <;> rfl))
mutual
  private theorem hydrateDomM_metaIndep : (h : Html msg) → (node : Dom.Node) → DomArena.MetaIndep (hydrateDomM (m := ArenaM msg) h node)
    | .text _, _ => .pure ()
    | .element _ attrs cs, node => by dsimp only [hydrateDomM]; refine .bind (fun _ _ _ _ _ => rfl) fun _ => .bind (applyAttrsM_metaIndep node attrs) fun _ => ?_; cases ownsChildren attrs; exact hydrateDomKidsM_metaIndep cs node 0 false; exact .pure ()
  private theorem hydrateDomKidsM_metaIndep : (cs : List (Html msg)) → (node : Dom.Node) → (i : UInt32) → (inRun : Bool) → DomArena.MetaIndep (hydrateDomKidsM (m := ArenaM msg) node i inRun cs)
    | [], _, _, _ => .pure ()
    | c :: rest, node, i, inRun => by
        dsimp only [hydrateDomKidsM]; cases c.textOf? with
        | none => exact .bind (fun _ _ _ _ _ => rfl) fun cn => .bind (hydrateDomM_metaIndep c cn) fun _ => hydrateDomKidsM_metaIndep rest node (i + 1) false
        | some str => exact .bind (hydrateTextSlotM_metaIndep node i inRun str (fun () => hasMoreText rest)) fun r => hydrateDomKidsM_metaIndep rest node (i + 1) r.2
end
private theorem hydrateListRowsM_eq_hydrateDomKidsM (node : Dom.Node) :
    ∀ (i : UInt32) (rs : List (Html msg)), (∀ r ∈ rs, r.textOf? = none) → ∀ (a : DomArena msg), (hydrateListRowsM (m := ArenaM msg) node i rs a).2 = (hydrateDomKidsM (m := ArenaM msg) node i false rs a).2
  | _, [], _, _ => rfl
  | i, r :: rs, hr, a => by dsimp only [hydrateListRowsM, hydrateDomKidsM]; rw [hr r (.head _)]; simp only [ArenaM.bind_eq]; exact hydrateListRowsM_eq_hydrateDomKidsM node (i + 1) rs (fun x hx => hr x (.tail _ hx)) _
private theorem hydrateViewKidsM_eq_hydrateDomKidsM_of (ks : List (View σ msg)) (node : Dom.Node) (s : σ)
    (hView : ∀ k ∈ ks, View.DomClean k → ∀ (cn : Dom.Node) (a : DomArena msg), ((hydrateViewM (m := ArenaM msg) k s cn).run a).2.SameDom ((hydrateDomM (m := ArenaM msg) (View.render k s) cn).run a).2) :
    View.DomCleanEach ks → ∀ (i : UInt32) (inRun : Bool) (a : DomArena msg), ((hydrateViewKidsM (m := ArenaM msg) node s i inRun ks).run a).2.SameDom ((hydrateDomKidsM (m := ArenaM msg) node i inRun (View.renderEach ks s)).run a).2 := by
  induction ks with
  | nil => exact fun _ _ _ a => DomArena.SameDom.refl a
  | cons k rest ih =>
      intro ⟨hk, hrest⟩ i inRun a; dsimp only [hydrateViewKidsM, View.renderEach, hydrateDomKidsM, StateT.run]; rw [← View.textOf?_eq_render s k]
      cases htxt : k.textOf? s with
      | some str => simp only [hasMoreViewText_eq_renderEach, ArenaM.bind_eq, ArenaM.pure_eq]; rw [(hydrateViewM_of_textOf? htxt _ _).1]; exact ih (fun x hx => hView x (.tail _ hx)) hrest (i + 1) _ _
      | none => simp only [ArenaM.bind_eq, ArenaM.pure_eq]; exact (ih (fun x hx => hView x (.tail _ hx)) hrest (i + 1) false _).trans ((hydrateDomKidsM_metaIndep (View.renderEach rest s) node (i + 1) false).sameDom (hView k (.head _) hk _ a))

theorem hydrateViewM_eq_hydrateDomM {v : View σ msg} (hcl : View.DomClean v) (s : σ) (node : Dom.Node) (a : DomArena msg) :
    ((hydrateViewM (m := StateM (DomArena msg)) v s node).run a).2.SameDom ((hydrateDomM (m := StateM (DomArena msg)) (View.render v s) node).run a).2 := by
  induction v using View.ind generalizing node a with
  | text _ | dyn _ => exact DomArena.SameDom.refl a
  | static h => cases h <;> (dsimp only [hydrateViewM, View.render, StateT.run]; simp only [ArenaM.bind_eq, ArenaM.pure_eq]; exact DomArena.SameDom.refl _)
  | dynNode _ | memo _ => dsimp only [hydrateViewM, View.render, StateT.run]; simp only [ArenaM.bind_eq, ArenaM.pure_eq]; exact DomArena.SameDom.refl _
  | ifElse c y no ihy ihn => rcases hcl with ⟨hy, hn⟩; cases hcs : c s <;> (dsimp only [hydrateViewM, View.render, StateT.run]; simp only [hcs, Bool.false_eq_true, ↓reduceIte, ArenaM.bind_eq, ArenaM.pure_eq]; first | exact ihn hn node a | exact ihy hy node a)
  | element tag attrs kids ihk =>
      rcases hcl with ⟨ha, hks⟩; dsimp only [hydrateViewM, View.render, hydrateDomM, StateT.run, MonadDom.clearHandlers]
      rw [ha.1 s, Bool.not_false, ite_eq_left rfl]; simp only [ArenaM.bind_eq, ArenaM.pure_eq]; exact hydrateViewKidsM_eq_hydrateDomKidsM_of kids node s (fun k hk hkCl cn a' => ihk k hk hkCl cn a') hks 0 false _
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      cases tmpl? with | some _ => exact False.elim hcl | none =>
      rcases hcl with ⟨ha, hrows⟩; dsimp only [hydrateViewM, View.render, hydrateDomM, StateT.run, MonadDom.clearHandlers]
      rw [ha.1 s, Bool.not_false, ite_eq_left rfl]; simp only [ArenaM.bind_eq, ArenaM.pure_eq, Html.map_prefixSignals_of_DomCleanList _ (hrows.2.1 s)]
      rw [hydrateListRowsM_eq_hydrateDomKidsM node 0 (rowsHtml s) (hrows.2.2.1 s)]; exact (hydrateDomKidsM_metaIndep (rowsHtml s) node 0 false).sameDom (seedRowsM_sameDom ..)

private theorem View.renderEach_eq_map (s : σ) : ∀ ks : List (View σ msg), View.renderEach ks s = ks.map (fun v => View.render v s)
  | [] => rfl | _ :: rest => congrArg (List.cons _) (View.renderEach_eq_map s rest)
private theorem View.DomCleanEach_iff : ∀ {ks : List (View σ msg)}, View.DomCleanEach ks ↔ ∀ k ∈ ks, View.DomClean k
  | [] => ⟨(fun _ _ h => nomatch h), fun _ => trivial⟩
  | _ :: _ => ⟨fun ⟨h1, h2⟩ _ hm => (List.mem_cons.1 hm).elim (· ▸ h1) (View.DomCleanEach_iff.1 h2 _), fun h => ⟨h _ (.head _), View.DomCleanEach_iff.2 fun x hx => h x (.tail _ hx)⟩⟩
private theorem hydrateViewM_spec_of_matches (ns : String) (f : Nat) (v : View σ msg) (s : σ) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat) (hc : View.DomClean v)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ f + 1) (hdom : HydratableDom (f + 1) ns (View.render v s) a lo hi root)
    (hmt : let (vst, aOut) := (hydrateViewM (m := ArenaM msg) v s root).run a; vst.rootNode = root ∧ VStateMatches v s aOut root vst) :
    let (vst, aOut) := (hydrateViewM (m := ArenaM msg) v s root).run a
    vst.rootNode = root ∧ ArenaExt a aOut (HydRange lo hi) (htmlNodeCount (View.render v s)) ∧ VStateValid (f + 1) ns v s aOut (HydSet lo hi a.nextId aOut.nextId) vst ∧
    DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns (View.render v s)) ∧ SubtreeInSet (f + 1) aOut (HydSet lo hi a.nextId aOut.nextId) root := by
  have ⟨hext, hsub, heqv, hcl⟩ := hydrateDomM_spec ns f (View.render v s) root a lo hi hbound hdep hdom; have hsd := hydrateViewM_eq_hydrateDomM hc s root a
  exact ⟨hmt.1, hext.sameDom hsd, VStateValid.of_sameDom hsd (hsd.1 ▸ hcl (View.DomClean_render hc s)) hmt.1 hmt.2, hsd.readDomTree_eq (f + 1) root ▸ heqv, hsd.1 ▸ (SubtreeInSet_frame (fun m _ => hsd.get_eq m) hsub).1⟩

private theorem viewKidsMatches_step (ep : ElemPar msg) (ks : List (View σ msg)) (s : σ) (inTextRun : Bool) (pre domCs : List Dom.Node) (lo hi : Nat) (a : DomArena msg)
    (hView : ∀ k ∈ ks, ∀ (f' : Nat) (root : Dom.Node) (a0 : DomArena msg) (lo0 hi0 : Nat), View.DomClean k →
      a0.nextId + htmlNodeCount (View.render k s) < UInt32.size → htmlDepth (View.render k s) ≤ f' + 1 → HydratableDom (f' + 1) ep.childNs (View.render k s) a0 lo0 hi0 root →
      let (vst, aOut) := (hydrateViewM (m := ArenaM msg) k s root).run a0; vst.rootNode = root ∧ VStateMatches k s aOut root vst)
    (hcl : View.DomCleanEach ks) (hlen : pre.length + ks.length < UInt32.size) (hbound : a.nextId + htmlListNodeCount (View.renderEach ks s) < UInt32.size)
    (hdep : htmlListDepth (View.renderEach ks s) ≤ ep.f) (hparLo : ep.parent.toNat < lo) (hpreSub : PreSub ep lo hi a pre)
    (hpar : a.get ep.parent = ep.entry (pre ++ domCs)) (hdom : HydratableDomList ep.f ep.childNs (if inTextRun then dropCurrentTextRun (View.renderEach ks s) else coalesceTextRun (View.renderEach ks s)) a lo hi domCs) :
    let (kstates, aOut) := (hydrateViewKidsM (m := ArenaM msg) ep.parent s (UInt32.ofNat pre.length) inTextRun ks).run a
    aOut.get ep.parent = ep.entry (pre ++ kstates.map VState.rootNode) ∧ VStateKidsMatches ks s aOut (kstates.map VState.rootNode) kstates := by
  refine hydrateKids_ind ep (toHtml := fun v => View.render v s) (ItemOk := fun k => View.DomClean k ∧ k ∈ ks)
    (Post := fun tgt inRun pr _ _ a0 => let (kstates, aOut) := (hydrateViewKidsM (m := ArenaM msg) ep.parent s (UInt32.ofNat pr.length) inRun tgt).run a0
      aOut.get ep.parent = ep.entry (pr ++ kstates.map VState.rootNode) ∧ VStateKidsMatches tgt s aOut (kstates.map VState.rootNode) kstates)
    ?_ ?_ ?_ ks inTextRun pre domCs lo hi a (fun k hk => ⟨View.DomCleanEach_iff.1 hcl k hk, hk⟩) hlen
    (by simpa only [View.renderEach_eq_map] using hbound) (by simpa only [View.renderEach_eq_map] using hdep) hparLo hpreSub hpar (by simpa only [View.renderEach_eq_map] using hdom)
  · intro _ _ _ _ _ hpar0; exact ⟨by simpa only [hydrateViewKidsM, StateT.run, pure, StateT.pure, List.map_nil, List.append_nil] using hpar0, trivial⟩
  · intro c rest inRun inRun' pr kn _ _ _ a0 str aMid _ hcEq _ _ _ _ huNext hslotEq _ _ _ _ _ hih
    have htxt : c.textOf? s = some str := (View.textOf?_eq_render s c).trans (by rw [hcEq]; rfl)
    have ⟨ha2Eq, hrootKst, hmatchKst⟩ := hydrateViewM_of_textOf? htxt kn aMid
    rw [show UInt32.ofNat (pr ++ [kn]).length = UInt32.ofNat pr.length + 1 by rw [List.length_append, List.length_singleton, huNext]] at hih
    dsimp only [hydrateViewKidsM, StateT.run] at hih ⊢; rw [htxt]
    simp only [hasMoreViewText_eq_renderEach, View.renderEach_eq_map, stateM_bind_step hslotEq, ArenaM.bind_eq, ArenaM.pure_eq, ha2Eq, List.map, VStateKidsMatches]
    exact ⟨by rw [hrootKst]; simpa only [List.append_assoc, List.singleton_append] using hih.1, trivial, hrootKst.symm ▸ hmatchKst _, hih.2⟩
  · intro c rest inRun pr child domRest lo' mid hi' a0 f' _ htxt ⟨hcCl, hcMem⟩ hrestOk hlen' huIdx huNext hbd' hcDep hrestDep hb hloMid hmidHi hpar0 hchildDom _ hcont
    have hcTxt : c.textOf? s = none := (View.textOf?_eq_render s c).trans htxt
    have hbdC : a0.nextId + htmlNodeCount (View.render c s) < UInt32.size := Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right _ _) _) hbd'
    have ⟨hrootKst, hextMid, hvalMid, _, hchildSubMid⟩ := hydrateViewM_spec_of_matches ep.childNs f' c s child a0 lo' mid hcCl hbdC hcDep hchildDom (hView c hcMem f' child a0 lo' mid hcCl hbdC hcDep hchildDom)
    let aMid := (hydrateViewM (m := ArenaM msg) c s child a0).2; rcases hcont aMid hextMid hchildSubMid with ⟨hih, hpreMid, hparMid, hdomMid⟩
    have ⟨_, hextR, _, _, _, _⟩ := hydrateDomKidsM_spec { ep with f := f' + 1 } (View.renderEach rest s) false (pr ++ [child]) domRest mid hi' aMid
      (by rw [View.renderEach_eq_map, List.length_map]; simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen'; omega)
      (by rw [View.renderEach_eq_map]; exact hextMid.bound_sub hbd') (by rw [View.renderEach_eq_map]; exact hrestDep) (Nat.lt_of_lt_of_le hb.1 hloMid) hpreMid hparMid (by rw [View.renderEach_eq_map]; exact hdomMid)
    rw [show UInt32.ofNat (pr ++ [child]).length = UInt32.ofNat pr.length + 1 by rw [List.length_append, List.length_singleton, huNext]] at hih hextR
    have hrestEq := hydrateViewKidsM_eq_hydrateDomKidsM_of rest ep.parent s (fun _ _ h => hydrateViewM_eq_hydrateDomM h s) (View.DomCleanEach_iff.2 fun r hr => (hrestOk r hr).1) (UInt32.ofNat pr.length + 1) false aMid
    dsimp only [hydrateViewKidsM, StateT.run] at hih hextR hrestEq ⊢; rw [hcTxt]; simp only [ArenaM.bind_eq, ArenaM.pure_eq, MonadDom.childAt, hpar0, huIdx, getD_append_right, List.map, VStateKidsMatches]
    exact ⟨by rw [hrootKst]; simpa only [List.append_assoc, List.singleton_append] using hih.1, trivial, VStateMatches_frame (fun m hm => (hrestEq.get_eq m).trans (hydChild_frame_of_rest hb hmidHi hextMid.next_ge hextR m hm)) hvalMid.1 hvalMid.2, hih.2⟩

private theorem hydrateViewM_matches (ns : String) (f : Nat) (v : View σ msg) (s : σ) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat) (hc : View.DomClean v)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ f + 1) (hdom : HydratableDom (f + 1) ns (View.render v s) a lo hi root) :
    let (vst, aOut) := (hydrateViewM (m := ArenaM msg) v s root).run a; vst.rootNode = root ∧ VStateMatches v s aOut root vst := by
  induction v using View.ind generalizing ns f root a lo hi with
  | text _ | static _ => exact ⟨rfl, rfl⟩ | dyn _ | dynNode _ => exact ⟨rfl, rfl, rfl⟩ | memo _ => exact ⟨rfl, rfl, rfl, rfl⟩
  | ifElse c y n ihy ihn =>
      rcases hc with ⟨hyCl, hnCl⟩; dsimp only [hydrateViewM, StateT.run]; cases hcs : c s <;> (
        simp only [hcs, Bool.false_eq_true, ↓reduceIte, View.render] at hbound hdep hdom ⊢
        have hr := by first | exact ihn ns f root a lo hi hnCl hbound hdep hdom | exact ihy ns f root a lo hi hyCl hbound hdep hdom
        exact ⟨hr.1, hcs.symm, by simpa only [hcs, Bool.false_eq_true, ↓reduceIte] using hr.2⟩)
  | keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl? =>
      cases tmpl? with | some _ => exact False.elim hc | none =>
      rcases hc with ⟨_, hrowsCl⟩; dsimp only [hydrateViewM, StateT.run, MonadDom.clearHandlers]; simp only [ArenaM.bind_eq, ArenaM.pure_eq, Html.map_prefixSignals_of_DomCleanList _ (hrowsCl.2.1 s)]; exact ⟨rfl, rfl, rfl, rfl⟩
  | element tag attrs kids ihk =>
      rcases hc with ⟨haCl, hkidsCl⟩; rcases hdom with ⟨_, _, _, st, prev, domCs, hget, hm, hns, _, hownF⟩; rcases hownF (haCl.1 s) with ⟨mid, hmidGt, hk⟩
      rcases hydrateElemAttrs_step a root ns tag st prev domCs (attrs.map (VAttr.eval s)) hget hm hns with ⟨st', ha2Get, _, _, ha2Next, ha2Out⟩
      have ⟨hlenK, hbdK, hdepK, hk2⟩ := hydrateKids_bounds_of_elem hbound hdep ha2Next ha2Out hmidGt hk
      have hvk := viewKidsMatches_step ⟨f, Dom.childNsOf ns tag, root, if ns == "" && tag == "svg" then Dom.svgNs else ns, tag, st',
        ((normalizeAttrs (attrs.map (VAttr.eval s))).filterMap managedAttrName)⟩ kids s false [] domCs mid hi _ (fun k hkMem => ihk k hkMem (Dom.childNsOf ns tag)) hkidsCl
        (by rw [← List.length_map (fun v => View.render v s), ← View.renderEach_eq_map]; exact hlenK) hbdK hdepK hmidGt (fun _ hm => nomatch hm) ha2Get hk2
      dsimp only [hydrateViewM, StateT.run, MonadDom.clearHandlers] at hvk ⊢; simp only [ArenaM.bind_eq, ArenaM.pure_eq]; exact ⟨rfl, rfl, _, tag, st', _, _, hvk.1, hvk.2⟩

theorem hydrateViewM_spec (ns : String) (f : Nat) (v : View σ msg) (s : σ) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat) (hc : View.DomClean v)
    (hbound : a.nextId + htmlNodeCount (View.render v s) < UInt32.size) (hdep : htmlDepth (View.render v s) ≤ f + 1) (hdom : HydratableDom (f + 1) ns (View.render v s) a lo hi root) :
    let (vst, aOut) := (hydrateViewM (m := StateM (DomArena msg)) v s root).run a
    vst.rootNode = root ∧ a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlNodeCount (View.render v s) ∧
    (∀ m : Dom.Node, (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    VStateValid (f + 1) ns v s aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) vst ∧
    DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns (View.render v s)) :=
  let ⟨h1, hext, hval, heqv, _⟩ := hydrateViewM_spec_of_matches ns f v s root a lo hi hc hbound hdep hdom (hydrateViewM_matches ns f v s root a lo hi hc hbound hdep hdom)
  ⟨h1, hext.next_ge, hext.next_le, fun m hmOut hmLt => hext.frame m hmLt fun hr => hmOut.elim (Nat.not_lt.2 hr.1) (Nat.not_lt.2 · hr.2), hval, heqv⟩

end
end Qed
