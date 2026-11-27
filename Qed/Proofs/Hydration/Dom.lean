import Qed.Proofs.DomSubtree

namespace Qed
variable {msg : Type}

/-! ## 3. HTML5 Text Coalescing & `hydrateTextSlotM` / `hydrateDomM` Equivalence -/

theorem hasMoreText_false_restOfTextRun : ∀ (cs : List (Html msg)), hasMoreText cs = false → restOfTextRun cs = ""
  | [], _ => rfl
  | c :: cs, h => by cases hc : c.textOf? with | none => simp [restOfTextRun, hc] | some s =>
      by_cases hse : s = ""; · subst hse; simp only [hasMoreText, hc] at h; simp [restOfTextRun, hc, hasMoreText_false_restOfTextRun cs h]
      · simp [hasMoreText, hc] at h
def hydrateDomTextModel (inTextRun : Bool) : List (Html msg) → List (Html msg) → List (Html msg)
  | [], _ => []
  | c :: rest, dom => match c.textOf? with
      | some s => if s == "" then .text "" :: hydrateDomTextModel inTextRun rest dom else if inTextRun then .text s :: hydrateDomTextModel true rest dom
          else match dom with | .text raw :: domRest => .text (if hasMoreText rest then s else raw) :: hydrateDomTextModel true rest domRest | _ :: domRest => .text s :: hydrateDomTextModel true rest domRest | [] => []
      | none => match dom with | _ :: domRest => c :: hydrateDomTextModel false rest domRest | [] => []
theorem textOf_eq_some_iff {h : Html msg} {s : String} : h.textOf? = some s ↔ h = .text s := by cases h <;> simp [Html.textOf?]
theorem hydrateDomTextModel_roundtrip : ∀ (cs : List (Html msg)), hydrateDomTextModel false cs (coalesceTextRun cs) = cs ∧ hydrateDomTextModel true cs (dropCurrentTextRun cs) = cs
  | [] => ⟨rfl, rfl⟩
  | c :: rest => by
      rcases hydrateDomTextModel_roundtrip rest with ⟨ihF, ihT⟩
      cases hc : c.textOf? with
      | none => exact ⟨by simpa [hydrateDomTextModel, coalesceTextRun, hc] using ihF, by simpa [hydrateDomTextModel, dropCurrentTextRun, hc] using ihF⟩
      | some s =>
          cases textOf_eq_some_iff.1 hc; by_cases hse : s = ""
          · subst hse; exact ⟨by simpa [hydrateDomTextModel, coalesceTextRun, Html.textOf?] using ihF, by simpa [hydrateDomTextModel, dropCurrentTextRun, Html.textOf?] using ihT⟩
          · refine ⟨?_, by simpa [hydrateDomTextModel, dropCurrentTextRun, Html.textOf?, hse] using ihT⟩
            simp only [coalesceTextRun, Html.textOf?, beq_eq_false_iff_ne.2 hse, Bool.false_eq_true, ↓reduceIte, hydrateDomTextModel, ihT]
            cases hm : hasMoreText rest with | true => simp | false => simp [hasMoreText_false_restOfTextRun rest hm]
theorem hydrateTextRun_equiv (cs : List (Html msg)) : hydrateDomTextModel false cs (coalesceTextRun cs) = cs := (hydrateDomTextModel_roundtrip cs).1
theorem hydrateDomM_ownsChildren_element (a : DomArena msg) (node : Dom.Node) (ns tag : String) (cs : List Dom.Node) (attrs : List (Attr msg)) (children : List (Html msg)) (hown : ownsChildren attrs = true) :
    ((hydrateDomM (m := ArenaM msg) (.element tag attrs children) node).run (a.set node (.element ns tag {} [] cs))).2 = a.set node (.element ns tag (evalSpecAttrs attrs) ((normalizeAttrs attrs).filterMap managedAttrName) cs) := by
  dsimp only [hydrateDomM, StateT.run, bind, StateT.bind, pure, StateT.pure, MonadDom.clearHandlers, DomArena.modifyElemState, DomArena.modify]
  rw [ite_eq_right (by simp [hown]), DomArena.get_set_self, DomArena.set_set, show applyAttrsM (m := ArenaM msg) node attrs (a.set node (.element ns tag {} [] cs)) = _ from applyAttrsM_fresh_element a node ns tag cs attrs]; rfl

def HydratableDomListAux (nodePred : String → Html msg → DomArena msg → Nat → Nat → Dom.Node → Prop) (ns : String) : List (Html msg) → DomArena msg → Nat → Nat → List Dom.Node → Prop
  | [], a, lo, hi, [] => lo ≤ hi ∧ hi ≤ a.nextId
  | d :: drest, a, lo, hi, n :: nrest => ∃ mid, nodePred ns d a lo mid n ∧ HydratableDomListAux nodePred ns drest a mid hi nrest
  | _, _, _, _, _ => False
def HydratableDom : Nat → String → Html msg → DomArena msg → Nat → Nat → Dom.Node → Prop
  | 0, _, _, _, _, _, _ => False
  | _ + 1, _, .text s, a, lo, hi, n => lo ≤ n.toNat ∧ n.toNat < hi ∧ hi ≤ a.nextId ∧ a.get n = .text s
  | f + 1, ns, .element tag attrs cs, a, lo, hi, n =>
      lo ≤ n.toNat ∧ n.toNat < hi ∧ hi ≤ a.nextId ∧ ∃ st prev domCs,
        a.get n = .element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag st prev domCs ∧
        ElemManaged ({ st with clicks := [], inputs := [] } : SpecElemState msg) prev ∧ AttrsNoShadow attrs ({ st with clicks := [], inputs := [] } : SpecElemState msg) ∧
        (ownsChildren attrs = true → domCs = []) ∧ (ownsChildren attrs = false → ∃ mid, n.toNat + 1 ≤ mid ∧ HydratableDomListAux (HydratableDom f) (Dom.childNsOf ns tag) (coalesceTextRun cs) a mid hi domCs)
abbrev HydratableDomList (f : Nat) : String → List (Html msg) → DomArena msg → Nat → Nat → List Dom.Node → Prop := HydratableDomListAux (@HydratableDom msg f)

theorem HydratableDom_bounds : ∀ (f : Nat) (ns : String) (d : Html msg) (a : DomArena msg) (lo hi : Nat) (n : Dom.Node), HydratableDom f ns d a lo hi n → lo ≤ n.toNat ∧ hi ≤ a.nextId ∧ lo ≤ hi
  | 0, _, _, _, _, _, _, h => h.elim | _ + 1, _, .text _, _, _, _, _, h | _ + 1, _, .element .., _, _, _, _, h => ⟨h.1, h.2.2.1, Nat.le_trans h.1 (Nat.le_of_lt h.2.1)⟩
theorem HydratableDomList_bounds : ∀ (f : Nat) (ns : String) (ds : List (Html msg)) (a : DomArena msg) (lo hi : Nat) (ns' : List Dom.Node), HydratableDomList f ns ds a lo hi ns' → lo ≤ hi ∧ hi ≤ a.nextId
  | _, _, [], _, _, _, [], h => h | _, _, [], _, _, _, _ :: _, h | _, _, _ :: _, _, _, _, [], h => h.elim
  | f, ns, d :: drest, a, lo, hi, n :: nrest, ⟨mid, hd, hrest⟩ => ⟨Nat.le_trans (HydratableDom_bounds f ns d a lo mid n hd).2.2 (HydratableDomList_bounds f ns drest a mid hi nrest hrest).1, (HydratableDomList_bounds f ns drest a mid hi nrest hrest).2⟩
theorem HydratableDomList_nodes_lt : ∀ (f : Nat) (ns : String) (ds : List (Html msg)) (a : DomArena msg) (lo hi : Nat) (ns' : List Dom.Node), HydratableDomList f ns ds a lo hi ns' → ∀ n ∈ ns', lo ≤ n.toNat ∧ n.toNat < hi
  | _, _, [], _, _, _, [], _ => fun _ h => nomatch h | _, _, [], _, _, _, _ :: _, h | _, _, _ :: _, _, _, _, [], h => h.elim
  | f, ns, d :: drest, a, lo, hi, n :: nrest, ⟨mid, hd, hrest⟩ => fun x hx =>
      let hb1 := HydratableDom_bounds f ns d a lo mid n hd; let hb2 := HydratableDomList_bounds f ns drest a mid hi nrest hrest
      (List.mem_cons.1 hx).elim (fun e => e ▸ match f, d, hd with | 0, _, h => h.elim | _ + 1, .text _, h | _ + 1, .element .., h => ⟨h.1, Nat.lt_of_lt_of_le h.2.1 hb2.1⟩)
        (fun htail => let hr := HydratableDomList_nodes_lt f ns drest a mid hi nrest hrest x htail; ⟨Nat.le_trans hb1.2.2 hr.1, hr.2⟩)

private theorem HydratableDomListAux.imp {f : Nat} {ns : String} {a a' : DomArena msg} (hle : a.nextId ≤ a'.nextId)
    (ih : ∀ d lo hi n, (∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m) → HydratableDom f ns d a lo hi n → HydratableDom f ns d a' lo hi n) :
    ∀ {ds : List (Html msg)} {lo hi : Nat} {ns' : List Dom.Node}, (∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m) → HydratableDomList f ns ds a lo hi ns' → HydratableDomList f ns ds a' lo hi ns'
  | [], _, _, [], _, ⟨h1, h2⟩ => ⟨h1, Nat.le_trans h2 hle⟩ | [], _, _, _ :: _, _, h | _ :: _, _, _, [], _, h => h.elim
  | d :: drest, lo, hi, n :: nrest, hfr, ⟨mid, hd, hrest⟩ =>
      ⟨mid, ih d lo mid n (fun m h1 h2 => hfr m h1 (Nat.lt_of_lt_of_le h2 (HydratableDomList_bounds f ns drest a mid hi nrest hrest).1)) hd,
       HydratableDomListAux.imp hle ih (fun m h1 h2 => hfr m (Nat.le_trans (HydratableDom_bounds f ns d a lo mid n hd).2.2 h1) h2) hrest⟩
private theorem HydratableDom_frame {a a' : DomArena msg} (hle : a.nextId ≤ a'.nextId) :
    ∀ {f : Nat} {ns : String} {d : Html msg} {lo hi : Nat} {n : Dom.Node}, (∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m) → HydratableDom f ns d a lo hi n → HydratableDom f ns d a' lo hi n
  | 0, _, _, _, _, _, _, h => h.elim | _ + 1, _, .text _, _, _, n, hfr, h => ⟨h.1, h.2.1, Nat.le_trans h.2.2.1 hle, (hfr n h.1 h.2.1).trans h.2.2.2⟩
  | _ + 1, _, .element .., _, _, n, hfr, ⟨hlo, hhi, hnext, st, prev, domCs, hget, hm, hns, hownT, hownF⟩ =>
      ⟨hlo, hhi, Nat.le_trans hnext hle, st, prev, domCs, (hfr n hlo hhi).trans hget, hm, hns, hownT,
        fun hown => let ⟨mid, hmid, hk⟩ := hownF hown; ⟨mid, hmid, HydratableDomListAux.imp hle (fun _ _ _ _ => HydratableDom_frame hle) (fun m hm1 hm2 => hfr m (by omega) hm2) hk⟩⟩
theorem HydratableDomList_frame (f : Nat) (ns : String) (ds : List (Html msg)) (a a' : DomArena msg) (lo hi : Nat) (ns' : List Dom.Node)
    (hle : a.nextId ≤ a'.nextId) (hfr : ∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m) (h : HydratableDomList f ns ds a lo hi ns') : HydratableDomList f ns ds a' lo hi ns' :=
  HydratableDomListAux.imp hle (fun _ _ _ _ => HydratableDom_frame hle) hfr h

private abbrev TextSlotAllocOut (a : DomArena msg) (parent : Dom.Node) (inTextRun : Bool) (s : String) (moreInRun : Unit → Bool) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (pre suf : List Dom.Node) : Prop :=
  let tn := UInt32.ofNat a.nextId; let ((outNode, outRun), a') := (hydrateTextSlotM (m := ArenaM msg) parent (UInt32.ofNat pre.length) inTextRun s moreInRun).run a
  outNode = tn ∧ outRun = inTextRun ∧ a'.nextId = a.nextId + 1 ∧ a'.get tn = .text s ∧ a'.get parent = .element pns ptag pst pmg (pre ++ tn :: suf) ∧ (∀ m : Dom.Node, m ≠ parent → m ≠ tn → a'.get m = a.get m)
theorem hydrateTextSlotM_alloc_spec (a : DomArena msg) (parent : Dom.Node) (inTextRun : Bool) (s : String) (hcond : s = "" ∨ inTextRun = true)
    (moreInRun : Unit → Bool) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (pre suf : List Dom.Node)
    (hnot : UInt32.ofNat a.nextId ∉ pre ++ suf) (hdisj : ∀ r ∈ suf, r ∉ pre) (hpreLen : pre.length < UInt32.size) (hparNe : parent ≠ UInt32.ofNat a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ suf)) : TextSlotAllocOut a parent inTextRun s moreInRun pns ptag pst pmg pre suf := by
  have hins : w3cInsertBefore (pre ++ suf) (UInt32.ofNat pre.length).toNat (UInt32.ofNat a.nextId) = pre ++ UInt32.ofNat a.nextId :: suf := by rw [uint32_toNat_ofNat_lt pre.length hpreLen]; exact w3cInsertBefore_fresh_append pre suf _ hnot hdisj
  have hallocPar : (DomArena.mk (a.nextId + 1) (fun m => if m == UInt32.ofNat a.nextId then .text s else a.store m) a.signals a.sigEvents a.tmpls a.rowEvs).get parent = .element pns ptag pst pmg (pre ++ suf) := by simp [DomArena.get, hparNe]; exact hpar
  dsimp only [TextSlotAllocOut, hydrateTextSlotM]
  by_cases hs : (s == "") = true <;> (
    first | (cases beq_iff_eq.1 hs; rw [ite_eq_left hs]) | (cases hcond.resolve_left (fun h => hs (by rw [h]; rfl)); rw [ite_eq_right hs, ite_eq_left rfl])
    dsimp only [StateT.run, bind, StateT.bind, pure, MonadDom.createText, DomArena.alloc, MonadDom.insertBeforeNode, DomArena.modifyChildren, DomArena.modify]
    rw [hallocPar]; dsimp only; exact ⟨rfl, rfl, rfl, by simp [DomArena.get, DomArena.set, hparNe.symm], by rw [DomArena.get_set_self, hins], fun m hm1 hm2 => by simp [DomArena.get, DomArena.set, hm1, hm2]⟩)
theorem hydrateTextSlotM_empty_spec (a : DomArena msg) (parent : Dom.Node) (inTextRun : Bool) (moreInRun : Unit → Bool) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (pre suf : List Dom.Node) (_hlt : a.nextId < UInt32.size) (hnot : UInt32.ofNat a.nextId ∉ pre ++ suf) (hdisj : ∀ r ∈ suf, r ∉ pre) (hpreLen : pre.length < UInt32.size)
    (hparNe : parent ≠ UInt32.ofNat a.nextId) (hpar : a.get parent = .element pns ptag pst pmg (pre ++ suf)) : TextSlotAllocOut a parent inTextRun "" moreInRun pns ptag pst pmg pre suf :=
  hydrateTextSlotM_alloc_spec a parent inTextRun "" (.inl rfl) moreInRun pns ptag pst pmg pre suf hnot hdisj hpreLen hparNe hpar
theorem hydrateTextSlotM_split_spec (a : DomArena msg) (parent : Dom.Node) (s : String) (_hs : s ≠ "") (moreInRun : Unit → Bool) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (pre suf : List Dom.Node) (_hlt : a.nextId < UInt32.size) (hnot : UInt32.ofNat a.nextId ∉ pre ++ suf) (hdisj : ∀ r ∈ suf, r ∉ pre) (hpreLen : pre.length < UInt32.size)
    (hparNe : parent ≠ UInt32.ofNat a.nextId) (hpar : a.get parent = .element pns ptag pst pmg (pre ++ suf)) : TextSlotAllocOut a parent true s moreInRun pns ptag pst pmg pre suf :=
  hydrateTextSlotM_alloc_spec a parent true s (.inr rfl) moreInRun pns ptag pst pmg pre suf hnot hdisj hpreLen hparNe hpar
theorem hydrateTextSlotM_head_spec (a : DomArena msg) (parent tn : Dom.Node) (s rawTail : String) (hs : s ≠ "") (more : Bool) (hmore : more = false → rawTail = "")
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (pre domRest : List Dom.Node) (hpreLen : pre.length < UInt32.size)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ tn :: domRest)) (htn : a.get tn = .text (s ++ rawTail)) :
    let ((outNode, outRun), a') := (hydrateTextSlotM (m := ArenaM msg) parent (UInt32.ofNat pre.length) false s (fun () => more)).run a
    outNode = tn ∧ outRun = true ∧ a'.nextId = a.nextId ∧ a'.get tn = .text s ∧ (∀ m : Dom.Node, m ≠ tn → a'.get m = a.get m) := by
  unfold hydrateTextSlotM; rw [beq_eq_false_iff_ne.2 hs]; cases more
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run, bind, StateT.bind, pure, StateT.pure, MonadDom.childAt, hpar, uint32_toNat_ofNat_lt pre.length hpreLen, getD_append_right, true_and]
    exact ⟨by simpa [hmore rfl] using htn, fun _ _ => trivial⟩
  · simp only [Bool.false_eq_true, ↓reduceIte, StateT.run, bind, StateT.bind, pure, StateT.pure, MonadDom.childAt, MonadDom.setText, DomArena.modify, hpar, uint32_toNat_ofNat_lt pre.length hpreLen, getD_append_right, true_and]
    rw [htn]; exact ⟨rfl, DomArena.get_set_self .., fun m hm => DomArena.get_set_ne _ _ hm⟩

private theorem HydratableDom.text_inv : ∀ {f : Nat} {ns s : String} {a : DomArena msg} {lo hi : Nat} {n : Dom.Node}, HydratableDom f ns (.text s) a lo hi n → lo ≤ n.toNat ∧ n.toNat < hi ∧ hi ≤ a.nextId ∧ a.get n = .text s
  | 0, _, _, _, _, _, _, h => h.elim | _ + 1, _, _, _, _, _, _, h => h
private theorem SubtreeInSet.text {f : Nat} (hf : 1 ≤ f) {a : DomArena msg} {S : Nat → Prop} {tn : Dom.Node} {s : String} (hm : S tn.toNat) (hg : a.get tn = .text s) : SubtreeInSet f a S tn := by cases f with | zero => cases hf | succ _ => exact ⟨hm, by rw [hg]; trivial⟩
private theorem HydratableDomList_cons_bounds {f : Nat} {ns : String} {d : Html msg} {drest : List (Html msg)} {a : DomArena msg} {lo hi : Nat} {n : Dom.Node} {nrest : List Dom.Node} (h : HydratableDomList f ns (d :: drest) a lo hi (n :: nrest)) :
    ∃ mid, lo ≤ mid ∧ mid ≤ hi ∧ hi ≤ a.nextId ∧ HydratableDom f ns d a lo mid n ∧ HydratableDomList f ns drest a mid hi nrest :=
  let ⟨mid, hd, hrest⟩ := h; let b1 := HydratableDom_bounds f ns d a lo mid n hd; let b2 := HydratableDomList_bounds f ns drest a mid hi nrest hrest; ⟨mid, b1.2.2, b2.1, b2.2, hd, hrest⟩
private theorem textOf_none_is_element : ∀ {c : Html msg}, c.textOf? = none → ∃ tag attrs kids, c = .element tag attrs kids
  | .text _, h => by simp [Html.textOf?] at h | .element tag attrs kids, _ => ⟨tag, attrs, kids, rfl⟩
abbrev HydRange (lo hi : Nat) (k : Nat) : Prop := lo ≤ k ∧ k < hi
abbrev HydSet (lo hi next0 next1 : Nat) (k : Nat) : Prop := HydRange lo hi k ∨ (next0 ≤ k ∧ k < next1)
abbrev PreSub (ep : ElemPar msg) (lo hi : Nat) (a : DomArena msg) (pre : List Dom.Node) : Prop :=
  ∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (ep.parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet ep.f a Sx x
abbrev HydBounds (ep : ElemPar msg) (lo hi : Nat) (a : DomArena msg) : Prop := ep.parent.toNat < lo ∧ lo ≤ hi ∧ hi ≤ a.nextId
private theorem hydSet_split (lo : Nat) {mid hi n0 n1 : Nat} (hmidHi : mid ≤ hi) (hhiNext : hi ≤ n0) (hnGe : n0 ≤ n1) :
    (∀ k, HydSet lo mid n0 n1 k → HydSet lo hi n0 n1 k) ∧ (∀ k, HydSet lo mid n0 n1 k → (k < mid ∨ hi ≤ k) ∧ k < n1) :=
  ⟨fun _ hk => hk.imp (fun h => ⟨h.1, Nat.lt_of_lt_of_le h.2 hmidHi⟩) id,
   fun _ hk => hk.elim (fun h => ⟨.inl h.2, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h.2 hmidHi) hhiNext) hnGe⟩) (fun h => ⟨.inr (Nat.le_trans hhiNext h.1), h.2⟩)⟩
theorem hydChild_frame_of_rest {ep : ElemPar msg} {lo mid hi : Nat} {a0 aMid aOut : DomArena msg} {b : Nat}
    (hb : HydBounds ep lo hi a0) (hmidHi : mid ≤ hi) (haMidGe : a0.nextId ≤ aMid.nextId) (hextR : ArenaExt aMid aOut (fun k => k = ep.parent.toNat ∨ HydRange mid hi k) b) :
    ∀ m : Dom.Node, HydSet lo mid a0.nextId aMid.nextId m.toNat → aOut.get m = aMid.get m := fun m hm =>
  hextR.frame m ((hydSet_split lo hmidHi hb.2.2 haMidGe).2 _ hm).2
    fun h => h.elim (fun e => hm.elim (fun h1 => Nat.not_lt.2 h1.1 (e ▸ hb.1)) (fun h2 => Nat.not_lt.2 h2.1 (e ▸ Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hb.1 hb.2.1) hb.2.2)))
      fun hr => hm.elim (fun h1 => Nat.not_lt.2 hr.1 h1.2) (fun h2 => Nat.not_lt.2 (Nat.le_trans hb.2.2 h2.1) hr.2)
abbrev DomHydrateOut (f : Nat) (ns : String) (h : Html msg) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat) (aOut : DomArena msg) : Prop :=
  ArenaExt a aOut (HydRange lo hi) (htmlNodeCount h) ∧ SubtreeInSet (f + 1) aOut (HydSet lo hi a.nextId aOut.nextId) root ∧
  DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns h) ∧ (h.DomClean = true → CleanDomSubtree (f + 1) ns h aOut (HydSet lo hi a.nextId aOut.nextId) root)
abbrev KidsHydrateOut (ep : ElemPar msg) (target : List (Html msg)) (pre : List Dom.Node) (lo hi : Nat) (a aOut : DomArena msg) : Prop :=
  ∃ hydratedCs : List Dom.Node, ArenaExt a aOut (fun k => k = ep.parent.toNat ∨ HydRange lo hi k) (htmlListNodeCount target) ∧
    aOut.get ep.parent = ep.entry (pre ++ hydratedCs) ∧ (∀ c ∈ hydratedCs, SubtreeInSet ep.f aOut (HydSet lo hi a.nextId aOut.nextId) c) ∧
    DomTreeListAssocEquiv (hydratedCs.map (readDomTree ep.f aOut)) (specDomList ep.childNs target) ∧
    (Html.DomCleanList target = true → CleanDomChildren ep.f ep.childNs target aOut (HydSet lo hi a.nextId aOut.nextId) hydratedCs)

private theorem preSub_extend_ext {ep : ElemPar msg} {child : Dom.Node} {targetRest : List (Html msg)} {pre domRest : List Dom.Node}
    {lo mid hi b : Nat} {a aMid : DomArena msg} {W Snew : Nat → Prop} (hb : HydBounds ep lo hi a) (hloMid : lo ≤ mid)
    (hext : ArenaExt a aMid W b) (hW : ∀ k, W k → k = ep.parent.toNat ∨ Snew k)
    (hSnewSub : ∀ k, Snew k → HydSet lo hi a.nextId aMid.nextId k) (hSnewOut : ∀ k, Snew k → (k < mid ∨ hi ≤ k) ∧ k < aMid.nextId)
    (hpreSub : PreSub ep lo hi a pre) (hrestDom : HydratableDomList ep.f ep.childNs targetRest a mid hi domRest) (hSubNew : SubtreeInSet ep.f aMid Snew child) :
    HydratableDomList ep.f ep.childNs targetRest aMid mid hi domRest ∧ PreSub ep mid hi aMid (pre ++ [child]) :=
  ⟨HydratableDomList_frame ep.f ep.childNs targetRest a aMid mid hi domRest hext.next_ge
    (fun m h1 h2 => hext.frame m (Nat.lt_of_lt_of_le h2 hb.2.2) fun hw => (hW _ hw).elim (fun e => Nat.not_le.2 (Nat.lt_of_lt_of_le hb.1 hloMid) (e ▸ h1)) fun hs => (hSnewOut _ hs).1.elim (Nat.not_lt.2 h1) (Nat.not_lt.2 · h2)) hrestDom,
   fun x hx => (List.mem_append.1 hx).elim (fun hOld => let ⟨Sx, hSx, hsub⟩ := hpreSub x hOld
     ⟨Sx, fun k hk => (hSx k hk).elim (fun h1 => .inl ⟨h1.1, Nat.lt_of_lt_of_le h1.2 hloMid⟩) (fun h2 => .inr ⟨h2.1, Nat.lt_of_lt_of_le h2.2 hext.next_ge⟩),
      (SubtreeInSet_frame (fun m hm => hext.frame m ((hSx _ hm).elim (fun h1 => Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h1.2 hb.2.1) hb.2.2) (·.2)) fun hw => (hW _ hw).elim
        (fun e => (hSx _ hm).elim (fun h1 => Nat.lt_irrefl _ (e ▸ h1.1)) fun h2 => Nat.not_le.2 (Nat.lt_of_lt_of_le hb.1 hb.2.1) (e ▸ h2.1))
        fun hs => (hSx _ hm).elim (fun h1 => (hSnewSub _ hs).elim (fun h3 => Nat.not_lt.2 h3.1 h1.2) fun h4 => Nat.not_lt.2 h4.1 (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h1.2 hb.2.1) hb.2.2))
          fun h2 => (hSnewSub _ hs).elim (fun h3 => Nat.not_lt.2 h2.1 h3.2) fun h4 => Nat.not_lt.2 h4.1 h2.2) hsub).1⟩)
     fun hNew => List.mem_singleton.1 hNew ▸ ⟨Snew, fun k hk => (hSnewSub k hk).elim (fun h1 => .inl ⟨Nat.lt_of_lt_of_le hb.1 h1.1, (hSnewOut k hk).1.resolve_right (Nat.not_le_of_lt h1.2)⟩) (fun h2 => .inr ⟨Nat.le_trans hb.2.2 h2.1, h2.2⟩), hSubNew⟩⟩

theorem hydrateKids_ind {α msg : Type} (ep : ElemPar msg) (toHtml : α → Html msg) (ItemOk : α → Prop) (Post : List α → Bool → List Dom.Node → Nat → Nat → DomArena msg → Prop)
    (hNil : ∀ inTextRun pre lo hi a, a.get ep.parent = ep.entry pre → Post [] inTextRun pre lo hi a)
    (hText : ∀ c rest inTextRun inRun' pre tn lo loRest hi a (s : String) (aMid : DomArena msg) (S_tn : Nat → Prop),
      toHtml c = .text s → ItemOk c → 1 ≤ ep.f → lo ≤ loRest → ep.parent ≠ tn → UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) →
      hydrateTextSlotM (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) inTextRun s (fun () => hasMoreText (rest.map toHtml)) a = ((tn, inRun'), aMid) →
      aMid.get tn = .text s → S_tn tn.toNat → (∀ k, S_tn k → HydSet lo hi a.nextId aMid.nextId k) → (∀ k, S_tn k → (k < loRest ∨ hi ≤ k) ∧ k < aMid.nextId) →
      ArenaExt a aMid (fun k => k = ep.parent.toNat ∨ HydRange lo hi k) 1 → Post rest inRun' (pre ++ [tn]) loRest hi aMid → Post (c :: rest) inTextRun pre lo hi a)
    (hElem : ∀ c rest inTextRun pre child domRest lo mid hi a (f' : Nat),
      ep.f = f' + 1 → (toHtml c).textOf? = none → ItemOk c → (∀ r ∈ rest, ItemOk r) → pre.length + (c :: rest).length < UInt32.size → (UInt32.ofNat pre.length).toNat = pre.length →
      UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) → a.nextId + htmlListNodeCount ((c :: rest).map toHtml) < UInt32.size → htmlDepth (toHtml c) ≤ f' + 1 → htmlListDepth (rest.map toHtml) ≤ f' + 1 →
      HydBounds ep lo hi a → lo ≤ mid → mid ≤ hi → a.get ep.parent = ep.entry (pre ++ child :: domRest) → HydratableDom (f' + 1) ep.childNs (toHtml c) a lo mid child → HydratableDomList (f' + 1) ep.childNs (coalesceTextRun (rest.map toHtml)) a mid hi domRest →
      (∀ (aMid : DomArena msg), ArenaExt a aMid (HydRange lo mid) (htmlNodeCount (toHtml c)) → SubtreeInSet (f' + 1) aMid (HydSet lo mid a.nextId aMid.nextId) child →
        Post rest false (pre ++ [child]) mid hi aMid ∧ PreSub { ep with f := f' + 1 } mid hi aMid (pre ++ [child]) ∧ aMid.get ep.parent = ep.entry ((pre ++ [child]) ++ domRest) ∧ HydratableDomList (f' + 1) ep.childNs (coalesceTextRun (rest.map toHtml)) aMid mid hi domRest) →
      Post (c :: rest) inTextRun pre lo hi a) :
    ∀ (target : List α) (inTextRun : Bool) (pre domCs : List Dom.Node) (lo hi : Nat) (a : DomArena msg),
      (∀ x ∈ target, ItemOk x) → pre.length + target.length < UInt32.size → a.nextId + htmlListNodeCount (target.map toHtml) < UInt32.size → htmlListDepth (target.map toHtml) ≤ ep.f →
      ep.parent.toNat < lo → PreSub ep lo hi a pre → a.get ep.parent = ep.entry (pre ++ domCs) →
      HydratableDomList ep.f ep.childNs (if inTextRun then dropCurrentTextRun (target.map toHtml) else coalesceTextRun (target.map toHtml)) a lo hi domCs → Post target inTextRun pre lo hi a := by
  intro target; induction target with
  | nil => intro inTextRun pre domCs lo hi a _ _ _ _ _ _ hpar hdom
           have : domCs = [] := by cases inTextRun <;> simp [coalesceTextRun, dropCurrentTextRun] at hdom <;> cases domCs with | nil => rfl | cons _ _ => exact hdom.elim
           subst this; exact hNil inTextRun pre lo hi a (by simpa only [List.append_nil] using hpar)
  | cons c rest ih =>
      intro inTextRun pre domCs lo hi a hok hlen hbound hdep hparLo hpreSub hpar hdom
      have hrestOk : ∀ r ∈ rest, ItemOk r := fun r hr => hok r (.tail _ hr)
      rcases HydratableDomList_bounds ep.f ep.childNs _ a lo hi domCs hdom with ⟨hloHi, hhiNext⟩
      have hb : HydBounds ep lo hi a := ⟨hparLo, hloHi, hhiNext⟩; have hparLt := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hparLo hloHi) hhiNext
      have hposF : 1 ≤ ep.f := Nat.le_trans (Nat.le_trans (by cases toHtml c <;> simp only [htmlDepth, Nat.le_refl, Nat.le_add_right]) (Nat.le_max_left ..)) hdep
      have huIdxNext : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) := uint32_ofNat_succ pre.length (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _)) _) hlen)
      have hrestDep : htmlListDepth (rest.map toHtml) ≤ ep.f := by simp only [List.map_cons, htmlListDepth] at hdep; exact Nat.le_trans (Nat.le_max_right _ _) hdep
      cases htxt : (toHtml c).textOf? with
      | some s =>
          have hcEq : toHtml c = .text s := textOf_eq_some_iff.1 htxt; simp only [List.map_cons, hcEq, htmlListNodeCount, htmlNodeCount] at hbound
          have hTextStep (tn : Dom.Node) (inRun' : Bool) (loRest : Nat) (domRest : List Dom.Node) (aMid : DomArena msg) (S_tn : Nat → Prop) (hloRest : lo ≤ loRest) (hparNe : ep.parent ≠ tn)
              (hslotEq : hydrateTextSlotM (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) inTextRun s (fun () => hasMoreText (rest.map toHtml)) a = ((tn, inRun'), aMid))
              (hgetTn : aMid.get tn = .text s) (hparMid : aMid.get ep.parent = ep.entry ((pre ++ [tn]) ++ domRest)) (hext : ArenaExt a aMid (fun k => k = ep.parent.toNat ∨ S_tn k) 1) (hStn : S_tn tn.toNat)
              (hStnSub : ∀ k, S_tn k → HydSet lo hi a.nextId aMid.nextId k) (hStnOut : ∀ k, S_tn k → (k < loRest ∨ hi ≤ k) ∧ k < aMid.nextId)
              (hdomRest : HydratableDomList ep.f ep.childNs (if inRun' then dropCurrentTextRun (rest.map toHtml) else coalesceTextRun (rest.map toHtml)) a loRest hi domRest) : Post (c :: rest) inTextRun pre lo hi a :=
            have ⟨hdomMid, hpreMid⟩ := preSub_extend_ext hb hloRest hext (fun _ h => h) hStnSub hStnOut hpreSub hdomRest (SubtreeInSet.text hposF hStn hgetTn)
            hText c rest inTextRun inRun' pre tn lo loRest hi a s aMid S_tn hcEq (hok c (.head _)) hposF hloRest hparNe huIdxNext hslotEq hgetTn hStn hStnSub hStnOut
              ⟨hext.next_ge, hext.next_le, fun m hm hne => hext.frame m hm fun hw => hne (hw.imp id fun hs => (hStnSub _ hs).resolve_right fun h => Nat.not_lt.2 h.1 hm)⟩
              (ih inRun' (pre ++ [tn]) domRest loRest hi aMid hrestOk (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen; omega) (hext.bound_sub hbound) hrestDep (Nat.lt_of_lt_of_le hparLo hloRest) hpreMid hparMid hdomMid)
          by_cases halloc : s = "" ∨ inTextRun = true
          · have hdisjDom : ∀ r ∈ domCs, r ∉ pre := fun r hr hmem => let hlt := HydratableDomList_nodes_lt ep.f ep.childNs _ a lo hi domCs hdom r hr; let ⟨_, hSx, hsub⟩ := hpreSub r hmem
              (hSx _ (SubtreeInSet_root_mem hposF hsub)).elim (fun h1 => Nat.not_lt.2 hlt.1 h1.2) (fun h2 => Nat.not_lt.2 h2.1 hlt.2)
            have hdom' : HydratableDomList ep.f ep.childNs (if inTextRun then dropCurrentTextRun (rest.map toHtml) else coalesceTextRun (rest.map toHtml)) a lo hi domCs := by
              rcases halloc with rfl | rfl; · cases inTextRun <;> simpa only [List.map_cons, hcEq, coalesceTextRun, dropCurrentTextRun, Html.textOf?, beq_self_eq_true, ↓reduceIte] using hdom
              · by_cases hs : s = "" <;> simpa only [List.map_cons, hcEq, dropCurrentTextRun, Html.textOf?, beq_iff_eq.2, beq_eq_false_iff_ne.2, hs, Bool.false_eq_true, ↓reduceIte] using hdom
            let tn := UInt32.ofNat a.nextId; have htnNat : tn.toNat = a.nextId := uint32_toNat_ofNat_lt a.nextId (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hbound)
            have hparNeTn : ep.parent ≠ tn := node_ne_of_toNat_ne (Nat.ne_of_lt (htnNat.symm ▸ hparLt))
            have hnotIn : tn ∉ pre ++ domCs := fun hm => (List.mem_append.1 hm).elim
              (fun hp => let ⟨_, hSx, hsub⟩ := hpreSub _ hp; (hSx _ (SubtreeInSet_root_mem hposF hsub)).elim (fun h1 => Nat.not_lt.2 (Nat.le_trans hloHi hhiNext) (htnNat ▸ h1.2)) (fun h2 => Nat.lt_irrefl _ (htnNat ▸ h2.2)))
              (fun hd => Nat.not_lt.2 hhiNext (htnNat ▸ (HydratableDomList_nodes_lt ep.f ep.childNs _ a lo hi domCs hdom _ hd).2))
            have ⟨hOut1, hOut2, haMidNext, hgetTn, hparM, hfrM⟩ := hydrateTextSlotM_alloc_spec a ep.parent inTextRun s halloc (fun () => hasMoreText (rest.map toHtml)) ep.pns ep.ptag ep.pst ep.pmg pre domCs hnotIn hdisjDom (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlen) hparNeTn hpar
            exact hTextStep tn inTextRun lo domCs _ (· = a.nextId) (Nat.le_refl _) hparNeTn (Prod.ext (Prod.ext hOut1 hOut2) rfl) hgetTn (List.append_assoc .. ▸ hparM)
              ⟨haMidNext ▸ Nat.le_succ _, haMidNext ▸ Nat.le_refl _, fun m hm hne => hfrM m (node_ne_of_toNat_ne fun e => hne (.inl e)) (node_ne_of_toNat_ne fun e => Nat.ne_of_lt hm (htnNat ▸ e))⟩
              htnNat (fun _ hk => .inr ⟨hk ▸ Nat.le_refl _, hk ▸ haMidNext ▸ Nat.lt_succ_self _⟩) (fun _ hk => ⟨.inr (hk ▸ hhiNext), hk ▸ haMidNext ▸ Nat.lt_succ_self _⟩) hdom'
          · have ⟨hsEmpty, hirF⟩ : s ≠ "" ∧ inTextRun = false := ⟨fun h => halloc (.inl h), Bool.eq_false_iff.2 fun h => halloc (.inr h)⟩; subst hirF
            have hdomCoal : HydratableDomList ep.f ep.childNs (.text (s ++ restOfTextRun (rest.map toHtml)) :: dropCurrentTextRun (rest.map toHtml)) a lo hi domCs := by simpa only [List.map_cons, hcEq, coalesceTextRun, Html.textOf?, beq_eq_false_iff_ne.2 hsEmpty, Bool.false_eq_true, ↓reduceIte] using hdom
            cases domCs with | nil => exact hdomCoal.elim | cons tn domRest =>
            rcases HydratableDomList_cons_bounds hdomCoal with ⟨mid, hloMid, hmidHi, hiNext, htnDom, hrestDom⟩; rcases HydratableDom.text_inv htnDom with ⟨htnLo, htnMid, _, hgetTn⟩
            have ⟨hOut1, hOut2, haMidNext, hgetTn', hfrM⟩ := hydrateTextSlotM_head_spec a ep.parent tn s (restOfTextRun (rest.map toHtml)) hsEmpty (hasMoreText (rest.map toHtml)) (hasMoreText_false_restOfTextRun (rest.map toHtml)) ep.pns ep.ptag ep.pst ep.pmg pre domRest (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlen) hpar hgetTn
            have hparNeTn : ep.parent ≠ tn := node_ne_of_toNat_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le hparLo htnLo))
            exact hTextStep tn true mid domRest _ (HydRange lo mid) hloMid hparNeTn (Prod.ext (Prod.ext hOut1 hOut2) rfl) hgetTn' ((hfrM ep.parent hparNeTn).trans (by rw [hpar, List.append_assoc, List.singleton_append]))
              ⟨haMidNext ▸ Nat.le_refl _, haMidNext ▸ Nat.le_succ _, fun m _ hne => hfrM m fun e => hne (.inr (e ▸ ⟨htnLo, htnMid⟩))⟩
              ⟨htnLo, htnMid⟩ (fun _ hk => .inl ⟨hk.1, Nat.lt_of_lt_of_le hk.2 hmidHi⟩) (fun _ hk => ⟨.inl hk.2, haMidNext ▸ Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hk.2 hmidHi) hiNext⟩) (by simpa only [↓reduceIte] using hrestDom)
      | none =>
          rcases textOf_none_is_element htxt with ⟨tag, attrs, kids, hcEq⟩
          have hcDep : htmlDepth (toHtml c) ≤ ep.f := by simp only [List.map_cons, htmlListDepth] at hdep; exact Nat.le_trans (Nat.le_max_left _ _) hdep
          have hdomElem : HydratableDomList ep.f ep.childNs (toHtml c :: coalesceTextRun (rest.map toHtml)) a lo hi domCs := by cases inTextRun <;> simpa only [List.map_cons, hcEq, coalesceTextRun, dropCurrentTextRun, Html.textOf?, ↓reduceIte, Bool.false_eq_true] using hdom
          cases domCs with | nil => exact hdomElem.elim | cons child domRest =>
          rcases HydratableDomList_cons_bounds hdomElem with ⟨mid, hloMid, hmidHi, hiNext, hchildDom, hrestDom⟩
          cases hf : ep.f with | zero => rw [hf] at hposF; cases hposF | succ f' =>
          rw [hf] at hcDep hrestDep hchildDom hrestDom
          refine hElem c rest inTextRun pre child domRest lo mid hi a f' hf htxt (hok c (.head _)) hrestOk hlen (uint32_toNat_ofNat_lt pre.length (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hlen)) huIdxNext hbound hcDep hrestDep hb hloMid hmidHi hpar hchildDom hrestDom fun aMid hextMid hchildSubMid => ?_
          have hparMid : aMid.get ep.parent = ep.entry ((pre ++ [child]) ++ domRest) := (hextMid.frame ep.parent hparLt (fun h => Nat.not_lt.2 h.1 hparLo)).trans (List.append_assoc .. ▸ hpar)
          have hsp := hydSet_split lo hmidHi hiNext hextMid.next_ge
          have ⟨hdomMid, hpreMid⟩ := preSub_extend_ext (ep := { ep with f := f' + 1 }) ⟨hparLo, hloHi, hhiNext⟩ hloMid hextMid (fun _ => .inr ∘ .inl) hsp.1 hsp.2 (hf ▸ hpreSub : PreSub { ep with f := f' + 1 } lo hi a pre) hrestDom hchildSubMid
          exact ⟨ih false (pre ++ [child]) domRest mid hi aMid hrestOk (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen; omega)
            (hextMid.bound_sub hbound) (hf ▸ hrestDep) (Nat.lt_of_lt_of_le hparLo hloMid) (by dsimp only [PreSub] at hpreMid ⊢; rw [hf]; exact hpreMid) hparMid (hf ▸ by simpa only [Bool.false_eq_true, ↓reduceIte] using hdomMid), hpreMid, hparMid, hdomMid⟩

private theorem kidsHydrate_cons {ep : ElemPar msg} {child : Dom.Node} {c : Html msg} {rest : List (Html msg)} {pr : List Dom.Node} {lo loRest hi : Nat} {a0 aMid aOut : DomArena msg} {Sc : Nat → Prop}
    (hloLe : lo ≤ loRest) (hextMid : ArenaExt a0 aMid (fun k => k = ep.parent.toNat ∨ HydRange lo hi k) (htmlNodeCount c))
    (hScSub : ∀ k, Sc k → HydSet lo hi a0.nextId aMid.nextId k) (hScDisj : ∀ k, Sc k → (k < loRest ∨ hi ≤ k) ∧ k < aMid.nextId)
    (hSubC : SubtreeInSet ep.f aOut Sc child) (hEqC : DomTreeAssocEquiv (readDomTree ep.f aOut child) (specDom ep.childNs c))
    (hClC : c.DomClean = true → CleanDomSubtree ep.f ep.childNs c aOut Sc child) (hRest : KidsHydrateOut ep rest (pr ++ [child]) loRest hi aMid aOut) :
    KidsHydrateOut ep (c :: rest) pr lo hi a0 aOut := by
  rcases hRest with ⟨hydRest, hextR, hparR, hsubR, heqR, hclR⟩
  have hSubL : ∀ k, Sc k → HydSet lo hi a0.nextId aOut.nextId k := fun k hk => (hScSub k hk).imp id fun h => ⟨h.1, hextR.lt h.2⟩
  have hSubR : ∀ k, HydSet loRest hi aMid.nextId aOut.nextId k → HydSet lo hi a0.nextId aOut.nextId k := fun _ hk => hk.elim (fun h => .inl ⟨Nat.le_trans hloLe h.1, h.2⟩) (fun h => .inr ⟨Nat.le_trans hextMid.next_ge h.1, h.2⟩)
  exact ⟨child :: hydRest, hextMid.trans hextR (fun _ h => h) (fun _ _ h => h.imp id fun hr => ⟨Nat.le_trans hloLe hr.1, hr.2⟩) (Nat.le_refl _),
    by simpa only [List.append_assoc, List.singleton_append] using hparR,
    fun z hz => (List.mem_cons.1 hz).elim (fun h => h ▸ SubtreeInSet_mono hSubL hSubC) (fun ht => SubtreeInSet_mono hSubR (hsubR z ht)),
    .cons hEqC heqR, fun hc => by simp only [Html.DomCleanList, List.all_cons, Bool.and_eq_true] at hc
                                  exact ⟨Sc, _, hSubL, hSubR, fun k hk1 hk2 => let ⟨ho, hl⟩ := hScDisj k hk1; hk2.elim (fun h => ho.elim (Nat.not_lt.2 h.1) (Nat.not_lt.2 · h.2)) (fun h => Nat.not_lt.2 h.1 hl), hClC hc.1, hclR hc.2⟩⟩

private theorem hydrateDomKidsM_spec_step (ep : ElemPar msg)
    (hDom : ∀ f', ep.f = f' + 1 → ∀ (ns : String) (h : Html msg) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat),
      a.nextId + htmlNodeCount h < UInt32.size → htmlDepth h ≤ f' + 1 → HydratableDom (f' + 1) ns h a lo hi root → DomHydrateOut f' ns h root a lo hi ((hydrateDomM (m := ArenaM msg) h root).run a).2)
    (target : List (Html msg)) (inTextRun : Bool) (pre domCs : List Dom.Node) (lo hi : Nat) (a : DomArena msg)
    (hlen : pre.length + target.length < UInt32.size) (hbound : a.nextId + htmlListNodeCount target < UInt32.size) (hdep : htmlListDepth target ≤ ep.f) (hparLo : ep.parent.toNat < lo)
    (hpreSub : PreSub ep lo hi a pre) (hpar : a.get ep.parent = ep.entry (pre ++ domCs)) (hdom : HydratableDomList ep.f ep.childNs (if inTextRun then dropCurrentTextRun target else coalesceTextRun target) a lo hi domCs) :
    KidsHydrateOut ep target pre lo hi a ((hydrateDomKidsM (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) inTextRun target).run a).2 := by
  refine hydrateKids_ind ep (toHtml := id) (ItemOk := fun _ => True) (Post := fun tgt inRun pr lo' hi' a0 => KidsHydrateOut ep tgt pr lo' hi' a0 ((hydrateDomKidsM (m := ArenaM msg) ep.parent (UInt32.ofNat pr.length) inRun tgt).run a0).2)
    ?_ ?_ ?_ target inTextRun pre domCs lo hi a (fun _ _ => trivial) hlen (by simpa only [List.map_id] using hbound) (by simpa only [List.map_id] using hdep) hparLo hpreSub hpar (by simpa only [List.map_id] using hdom)
  · intro _ pr _ _ a0 hpar0; exact ⟨[], ArenaExt.refl, by simpa only [hydrateDomKidsM, StateT.run, pure, StateT.pure, List.append_nil] using hpar0, (fun _ hm => nomatch hm), .nil, fun _ => trivial⟩
  · intro c rest inRun inRun' pr tn lo' loRest hi' a0 s aMid S_tn hcEq _ hfPos hloLe hparNe huNext hslotEq hgetNew htnIn hStnSub hStnOut hextMid hih
    cases hcEq; simp only [List.map_id] at hslotEq; rw [show UInt32.ofNat (pr ++ [tn]).length = UInt32.ofNat pr.length + 1 by rw [List.length_append, List.length_singleton, huNext]] at hih
    dsimp only [StateT.run, hydrateDomKidsM, Html.textOf?] at hih ⊢; rw [stateM_bind_step hslotEq]
    have haOutTn : (hydrateDomKidsM (m := ArenaM msg) ep.parent (UInt32.ofNat pr.length + 1) inRun' rest aMid).2.get tn = .text s :=
      let ⟨_, hextR, _, _, _, _⟩ := hih; (hextR.frame tn (hStnOut tn.toNat htnIn).2 fun h => h.elim (fun e => hparNe (uint32_eq_of_toNat_eq e.symm)) fun hr => (hStnOut tn.toNat htnIn).1.elim (Nat.not_lt.2 hr.1) (Nat.not_lt.2 · hr.2)).trans hgetNew
    cases hfp : ep.f with | zero => rw [hfp] at hfPos; cases hfPos | succ _ =>
    exact kidsHydrate_cons (ep := ep) hloLe hextMid hStnSub hStnOut (by rw [hfp]; exact ⟨htnIn, by rw [haOutTn]; trivial⟩) (by rw [hfp]; dsimp only [readDomTree, specDom]; rw [haOutTn]; exact .text s) (fun _ => by rw [hfp]; exact ⟨htnIn, haOutTn⟩) hih
  · intro c rest inRun pr child domRest lo' mid hi' a0 f' hfEq htxt _ _ _ huIdx huNext hbd' hcDep _ hb hloMid hmidHi hpar0 hchildDom _ hcont
    simp only [List.map_id] at hbd'; rcases textOf_none_is_element htxt with ⟨tag, attrs, kids, hcEq⟩; subst hcEq
    let aMid := (hydrateDomM (m := ArenaM msg) (.element tag attrs kids) child a0).2
    rcases hDom f' hfEq ep.childNs (.element tag attrs kids) child a0 lo' mid (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_right _ _) _) hbd') hcDep hchildDom with ⟨hextMid, hchildSubMid, hequivChild, hchildClMid⟩
    have hrest := (hcont aMid hextMid hchildSubMid).1; rw [show UInt32.ofNat (pr ++ [child]).length = UInt32.ofNat pr.length + 1 by rw [List.length_append, List.length_singleton, huNext]] at hrest
    dsimp only [StateT.run, hydrateDomKidsM, Html.textOf?] at hrest ⊢; rw [ArenaM.bind_eq]; simp only [MonadDom.childAt, hpar0, huIdx, getD_append_right]; rw [ArenaM.bind_eq]
    have hfrChild : ∀ m : Dom.Node, HydSet lo' mid a0.nextId aMid.nextId m.toNat → (hydrateDomKidsM (m := ArenaM msg) ep.parent (UInt32.ofNat pr.length + 1) false rest aMid).2.get m = aMid.get m := let ⟨_, hextR, _, _, _, _⟩ := hrest; hydChild_frame_of_rest hb hmidHi hextMid.next_ge hextR
    have haOutChild := SubtreeInSet_frame (n := child) hfrChild hchildSubMid; have hsp := hydSet_split lo' hmidHi hb.2.2 hextMid.next_ge
    exact kidsHydrate_cons (ep := ep) hloMid (hextMid.mono (fun _ hr => .inr ⟨hr.1, Nat.lt_of_lt_of_le hr.2 hmidHi⟩) (Nat.le_refl _)) hsp.1 hsp.2 (hfEq ▸ haOutChild.1) (hfEq ▸ (haOutChild.2.symm ▸ hequivChild)) (fun hc => hfEq ▸ CleanDomSubtree_frame hfrChild (hchildClMid hc)) hrest

theorem hydrateElemAttrs_step (a : DomArena msg) (root : Dom.Node) (ns tag : String) (st : SpecElemState msg) (prev : List String)
    (domCs : List Dom.Node) (attrs : List (Attr msg)) (hget : a.get root = .element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag st prev domCs)
    (hm : ElemManaged ({ st with clicks := [], inputs := [] } : SpecElemState msg) prev) (hns : AttrsNoShadow attrs ({ st with clicks := [], inputs := [] } : SpecElemState msg)) :
    let aClear := a.modifyElemState root (fun st : SpecElemState msg => { st with clicks := [], inputs := [] }); let a2 := (applyAttrsM (m := ArenaM msg) root attrs aClear).2
    ∃ st', a2.get root = .element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag st' ((normalizeAttrs attrs).filterMap managedAttrName) domCs ∧
      ElemStateEquiv st' (evalSpecAttrs attrs) ∧ ElemManaged st' ((normalizeAttrs attrs).filterMap managedAttrName) ∧ a2.nextId = a.nextId ∧ (∀ m : Dom.Node, m ≠ root → a2.get m = a.get m) := by
  let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns; let st0 : SpecElemState msg := { st with clicks := [], inputs := [] }
  have hclear : a.modifyElemState root (fun st : SpecElemState msg => { st with clicks := [], inputs := [] }) = a.set root (.element realNs tag st0 prev domCs) := by simp only [DomArena.modifyElemState, DomArena.modify, hget, realNs, st0]
  rcases applyAttrsM_existing_element a root realNs tag st0 prev domCs attrs hm hns with ⟨st', ha2Get, ha2Eqv, hm'⟩
  have ⟨ha2Next, ha2Out⟩ := applyAttrsM_preserves (a.set root (.element realNs tag st0 prev domCs)) root attrs
  dsimp only; rw [hclear]; exact ⟨st', ha2Get, ha2Eqv, hm', ha2Next, fun m hne => (ha2Out m hne).trans (DomArena.get_set_ne _ _ hne)⟩

theorem hydrateKids_bounds_of_elem {ns tag : String} {f hi mid : Nat} {root : Dom.Node} {attrs : List (Attr msg)} {cs : List (Html msg)} {domCs : List Dom.Node} {a a2 : DomArena msg}
    (hbound : a.nextId + htmlNodeCount (.element tag attrs cs) < UInt32.size) (hdep : htmlDepth (.element tag attrs cs) ≤ f + 1)
    (ha2Next : a2.nextId = a.nextId) (ha2Out : ∀ m, m ≠ root → a2.get m = a.get m) (hmidGt : root.toNat + 1 ≤ mid) (hk : HydratableDomList f (Dom.childNsOf ns tag) (coalesceTextRun cs) a mid hi domCs) :
    ([] : List Dom.Node).length + cs.length < UInt32.size ∧ a2.nextId + htmlListNodeCount cs < UInt32.size ∧ htmlListDepth cs ≤ f ∧ HydratableDomList f (Dom.childNsOf ns tag) (coalesceTextRun cs) a2 mid hi domCs :=
  ⟨by rw [List.length_nil, Nat.zero_add]; exact Nat.lt_of_le_of_lt (Nat.le_trans (list_length_le_htmlListNodeCount cs) (Nat.le_add_left _ _)) (Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left _ 1) _) hbound),
   ha2Next.symm ▸ Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_add_left _ 1) _) hbound, Nat.le_of_add_le_add_left (a := 1) (Nat.add_comm f 1 ▸ hdep),
   HydratableDomList_frame f (Dom.childNsOf ns tag) (coalesceTextRun cs) a a2 mid hi domCs (ha2Next ▸ Nat.le_refl _) (fun m hm1 _ => ha2Out m fun e => Nat.not_lt.2 hm1 (e ▸ hmidGt)) hk⟩

theorem hydrateDomM_spec (ns : String) (f : Nat) (h : Html msg) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat)
    (hbound : a.nextId + htmlNodeCount h < UInt32.size) (hdep : htmlDepth h ≤ f + 1) (hdom : HydratableDom (f + 1) ns h a lo hi root) :
    DomHydrateOut f ns h root a lo hi ((hydrateDomM (m := ArenaM msg) h root).run a).2 := by
  induction f using Nat.strongRecOn generalizing ns h root a lo hi with
  | ind f ih =>
      cases h with
      | text s => rcases hdom with ⟨hlo, hhi, _, hget⟩
                  exact ⟨ArenaExt.refl.mono (fun _ h => h) (Nat.zero_le _), ⟨.inl ⟨hlo, hhi⟩, by dsimp only [hydrateDomM, StateT.run, pure, StateT.pure]; rw [hget]; trivial⟩,
                    by dsimp only [hydrateDomM, StateT.run, pure, StateT.pure, readDomTree, specDom]; rw [hget]; exact .text s, fun _ => ⟨.inl ⟨hlo, hhi⟩, hget⟩⟩
      | element tag attrs cs =>
          rcases hdom with ⟨hlo, hhi, _, st, prev, domCs, hget, hm, hns, hownT, hownF⟩
          let a2 := (applyAttrsM (m := ArenaM msg) root attrs (a.modifyElemState root fun st => { st with clicks := [], inputs := [] })).2
          rcases hydrateElemAttrs_step a root ns tag st prev domCs attrs hget hm hns with ⟨st', ha2Get, ha2Eqv, hm', ha2Next, ha2Out⟩
          have ha2Next' : a2.nextId = a.nextId := ha2Next; have ha2Ext : ArenaExt a a2 (· = root.toNat) 0 := ArenaExt.of_next_eq ha2Next' fun m _ hne => ha2Out m (node_ne_of_toNat_ne hne)
          dsimp only [DomHydrateOut, hydrateDomM, StateT.run, MonadDom.clearHandlers]; simp only [ArenaM.bind_eq]
          cases hown : ownsChildren attrs with
          | true => cases hownT hown; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ArenaM.pure_eq]
                    exact ⟨ha2Ext.mono (fun _ e => e ▸ ⟨hlo, hhi⟩) (Nat.zero_le _), ⟨.inl ⟨hlo, hhi⟩, by rw [ha2Get]; intro _ hc; nomatch hc⟩,
                      by dsimp only [readDomTree, specDom]; rw [ha2Get, hown]; exact .element ha2Eqv .nil, fun hc => by simp only [Html.DomClean_element, hown, Bool.not_true, Bool.false_and] at hc; cases hc⟩
          | false =>
              simp only [Bool.not_false, ↓reduceIte]; rcases hownF hown with ⟨mid, hmidGt, hk⟩
              have ⟨hlenK, hbdK, hdepK, hk2⟩ := hydrateKids_bounds_of_elem hbound hdep ha2Next' ha2Out hmidGt hk
              have ⟨hydratedCs, hextKids, hgetOut, hsubSet, hequivKids, hcleanKids⟩ := hydrateDomKidsM_spec_step
                ⟨f, Dom.childNsOf ns tag, root, if ns == "" && tag == "svg" then Dom.svgNs else ns, tag, st', (normalizeAttrs attrs).filterMap managedAttrName⟩
                (fun f' hEq ns' h' r' a' lo' hi' => ih f' (by rw [show f = f' + 1 from hEq]; exact Nat.lt_succ_self _) ns' h' r' a' lo' hi') cs false [] domCs mid hi a2 hlenK hbdK hdepK hmidGt (fun _ hm => nomatch hm) ha2Get hk2
              simp only [StateT.run, List.length_nil, show (UInt32.ofNat 0 : UInt32) = 0 from rfl] at hextKids hgetOut hsubSet hequivKids hcleanKids
              have hkb := HydratableDomList_bounds _ _ _ _ _ _ _ hk
              have hSubMap : ∀ k, HydSet mid hi a2.nextId (hydrateDomKidsM (m := ArenaM msg) root 0 false cs a2).2.nextId k →
                  HydSet lo hi a.nextId (hydrateDomKidsM (m := ArenaM msg) root 0 false cs a2).2.nextId k ∧ k ≠ root.toNat := fun _ hkS =>
                hkS.elim (fun h => ⟨.inl ⟨Nat.le_trans hlo (Nat.le_of_lt (Nat.lt_of_lt_of_le hmidGt h.1)), h.2⟩, Nat.ne_of_gt (Nat.lt_of_lt_of_le hmidGt h.1)⟩)
                  fun h => ⟨.inr ⟨ha2Next' ▸ h.1, h.2⟩, Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hmidGt hkb.1) hkb.2) (ha2Next' ▸ h.1))⟩
              exact ⟨ha2Ext.trans hextKids (fun _ e => e ▸ ⟨hlo, hhi⟩) (fun _ _ h => h.elim (· ▸ ⟨hlo, hhi⟩) fun hr => ⟨Nat.le_trans hlo (Nat.le_of_lt (Nat.lt_of_lt_of_le hmidGt hr.1)), hr.2⟩) (Nat.zero_add _ ▸ Nat.le_add_left _ 1),
                ⟨.inl ⟨hlo, hhi⟩, by rw [hgetOut]; exact fun c hc => SubtreeInSet_mono (fun k hkS => (hSubMap k hkS).1) (hsubSet c hc)⟩,
                by dsimp only [readDomTree, specDom]; rw [hgetOut, hown]; exact .element ha2Eqv hequivKids,
                fun hc => by simp only [Html.DomClean_element, hown, Bool.not_false, Bool.true_and, Bool.and_eq_true] at hc
                             exact ⟨.inl ⟨hlo, hhi⟩, hown, hc.1, st', _, hydratedCs, hgetOut, ⟨hm', fun k hk' => (SlotVal.optStr.inj (ha2Eqv (.attr k))).trans ((ElemClean_evalSpecAttrs hc.1).2 k hk')⟩,
                               ha2Eqv, fun _ => List.contains_iff_mem.2, CleanDomChildren_mono hSubMap (hcleanKids hc.2)⟩⟩

theorem hydrateDomKidsM_spec (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (f : Nat) (target : List (Html msg)) (inTextRun : Bool) (pre domCs : List Dom.Node) (lo hi : Nat) (a : DomArena msg)
    (hlen : pre.length + target.length < UInt32.size) (hbound : a.nextId + htmlListNodeCount target < UInt32.size) (hdep : htmlListDepth target ≤ f) (hparLo : parent.toNat < lo)
    (hpreSub : PreSub ⟨f, childNs, parent, pns, ptag, pst, pmg⟩ lo hi a pre)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ domCs)) (hdom : HydratableDomList f childNs (if inTextRun then dropCurrentTextRun target else coalesceTextRun target) a lo hi domCs) :
    KidsHydrateOut ⟨f, childNs, parent, pns, ptag, pst, pmg⟩ target pre lo hi a ((hydrateDomKidsM (m := ArenaM msg) parent (UInt32.ofNat pre.length) inTextRun target).run a).2 :=
  hydrateDomKidsM_spec_step ⟨f, childNs, parent, pns, ptag, pst, pmg⟩ (fun f' _ => hydrateDomM_spec (f := f')) target inTextRun pre domCs lo hi a hlen hbound hdep hparLo hpreSub hpar hdom

end Qed
