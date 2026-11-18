import Qed.Proofs.ViewPatch

namespace Qed

/-! ## 3. HTML5 Text Coalescing & `hydrateTextSlotM` / `hydrateDomM` Equivalence -/

theorem hasMoreText_false_restOfTextRun :
    ∀ (cs : List (Html msg)), hasMoreText cs = false → restOfTextRun cs = ""
  | [], _ => rfl
  | c :: cs, h => by
      cases hc : c.textOf? with
      | none => simp [restOfTextRun, hc]
      | some s =>
          by_cases hse : s = ""
          · subst hse
            simp only [hasMoreText, hc] at h
            simp [restOfTextRun, hc, hasMoreText_false_restOfTextRun cs h]
          · simp [hasMoreText, hc] at h

/-- Pure DOM-child specification of `hydrateTextSlotM` + `hydrateDomKidsM`: given the coalesced
    child texts emitted by an HTML5 parser (`coalesceTextRun cs`), `hydrateTextSlotM` splits merged
    text runs and inserts `""` placeholder nodes so the hydrated child list matches `cs` 1-for-1. -/
def hydrateDomTextModel (inTextRun : Bool) : List (Html msg) → List (Html msg) → List (Html msg)
  | [], _ => []
  | c :: rest, dom =>
      match c.textOf? with
      | some s =>
          if s == "" then
            .text "" :: hydrateDomTextModel inTextRun rest dom
          else if inTextRun then
            .text s :: hydrateDomTextModel true rest dom
          else
            match dom with
            | .text raw :: domRest =>
                let fixed := if hasMoreText rest then s else raw
                .text fixed :: hydrateDomTextModel true rest domRest
            | _ :: domRest =>
                .text s :: hydrateDomTextModel true rest domRest
            | [] => []
      | none =>
          match dom with
          | _ :: domRest => c :: hydrateDomTextModel false rest domRest
          | [] => []

private theorem textOf_eq_some_iff {h : Html msg} {s : String} :
    h.textOf? = some s ↔ h = .text s := by
  cases h <;> simp [Html.textOf?]

theorem hydrateDomTextModel_roundtrip (cs : List (Html msg)) :
    hydrateDomTextModel false cs (coalesceTextRun cs) = cs ∧
    hydrateDomTextModel true cs (dropCurrentTextRun cs) = cs := by
  induction cs with
  | nil => exact ⟨rfl, rfl⟩
  | cons c rest ih =>
      rcases ih with ⟨ihFalse, ihTrue⟩
      cases hc : c.textOf? with
      | none =>
          refine ⟨?_, ?_⟩ <;>
            simpa [hydrateDomTextModel, coalesceTextRun, dropCurrentTextRun, hc] using ihFalse
      | some s =>
          have hce : c = .text s := textOf_eq_some_iff.1 hc
          subst hce
          cases hs : (s == "") with
          | true =>
              have hse : s = "" := eq_of_beq hs
              subst hse
              refine ⟨?_, ?_⟩
              · simpa [hydrateDomTextModel, coalesceTextRun, Html.textOf?] using ihFalse
              · simpa [hydrateDomTextModel, dropCurrentTextRun, Html.textOf?] using ihTrue
          | false =>
              have hne : s ≠ "" := fun h => by simp [h] at hs
              refine ⟨?_, ?_⟩
              · simp only [coalesceTextRun, Html.textOf?, hs, Bool.false_eq_true, ↓reduceIte,
                           hydrateDomTextModel, ihTrue]
                cases hm : hasMoreText rest with
                | true => simp
                | false =>
                    simp [hasMoreText_false_restOfTextRun rest hm]
              · simpa [hydrateDomTextModel, dropCurrentTextRun, Html.textOf?, hne] using ihTrue

/-- Hydrating an HTML5-coalesced child list restores the exact uncoalesced `Html` child list,
    including preserving existing text nodes untouched when `hasMoreText rest = false`. -/
theorem hydrateTextRun_equiv (cs : List (Html msg)) :
    hydrateDomTextModel false cs (coalesceTextRun cs) = cs :=
  (hydrateDomTextModel_roundtrip cs).1

/-- Imperative `hydrateDomM` on an element node clears stale handler attributes, applies normalized
    attributes (`evalSpecAttrs attrs`), and hydrates children when `!ownsChildren attrs`. -/
theorem hydrateDomM_ownsChildren_element (a : DomArena msg) (node : Dom.Node)
    (ns tag : String) (cs : List Dom.Node) (attrs : List (Attr msg)) (children : List (Html msg))
    (hown : ownsChildren attrs = true) :
    ((hydrateDomM (m := StateM (DomArena msg)) (.element tag attrs children) node).run
      (a.set node (.element ns tag {} [] cs))).2 =
      a.set node (.element ns tag (evalSpecAttrs attrs) ((normalizeAttrs attrs).filterMap managedAttrName) cs) := by
  dsimp only [hydrateDomM, StateT.run, bind, StateT.bind, pure, StateT.pure,
              MonadDom.clearHandlers, DomArena.modifyElemState, DomArena.modify]
  rw [if_neg (by simp [hown]), DomArena.get_set_self, DomArena.set_set]
  dsimp only
  rw [applyAttrsM_fresh_element a node ns tag cs attrs]
  rfl


/-! ### HTML5 Hydration Simulation on `DomArena` -/

def HydratableDomListAux {msg : Type}
    (nodePred : String → Html msg → DomArena msg → Nat → Nat → Dom.Node → Prop)
    (ns : String) : List (Html msg) → DomArena msg → Nat → Nat → List Dom.Node → Prop
  | [], a, lo, hi, [] => lo ≤ hi ∧ hi ≤ a.nextId
  | d :: drest, a, lo, hi, n :: nrest =>
      ∃ mid, nodePred ns d a lo mid n ∧ HydratableDomListAux nodePred ns drest a mid hi nrest
  | _, _, _, _, _ => False

/-- Well-formed SSR-parsed DOM tree corresponding to a coalesced HTML5 tree `domH` in interval `[lo, hi)`. -/
def HydratableDom {msg : Type} :
    Nat → String → Html msg → DomArena msg → Nat → Nat → Dom.Node → Prop
  | 0, _, _, _, _, _, _ => False
  | _ + 1, _, .text s, a, lo, hi, n =>
      lo ≤ n.toNat ∧ n.toNat < hi ∧ hi ≤ a.nextId ∧ a.get n = .text s
  | f + 1, ns, .element tag attrs cs, a, lo, hi, n =>
      lo ≤ n.toNat ∧ n.toNat < hi ∧ hi ≤ a.nextId ∧
      ∃ st prev domCs,
        a.get n = .element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag st prev domCs ∧
        ElemManaged ({ st with clicks := [], inputs := [] } : SpecElemState msg) prev ∧
        AttrsNoShadow attrs ({ st with clicks := [], inputs := [] } : SpecElemState msg) ∧
        (ownsChildren attrs = true → domCs = []) ∧
        (ownsChildren attrs = false →
          ∃ mid, n.toNat + 1 ≤ mid ∧
            HydratableDomListAux (HydratableDom f) (Dom.childNsOf ns tag) (coalesceTextRun cs) a mid hi domCs)

abbrev HydratableDomList {msg : Type} (f : Nat) :
    String → List (Html msg) → DomArena msg → Nat → Nat → List Dom.Node → Prop :=
  HydratableDomListAux (@HydratableDom msg f)

private theorem HydratableDom_bounds {msg : Type} :
    ∀ (f : Nat) (ns : String) (d : Html msg) (a : DomArena msg) (lo hi : Nat) (n : Dom.Node),
      HydratableDom f ns d a lo hi n → lo ≤ n.toNat ∧ hi ≤ a.nextId ∧ lo ≤ hi
  | 0, _, _, _, _, _, _, h => False.elim h
  | _ + 1, _, .text _, _, _, _, _, h => by
      have h1 := h.1; have h2 := h.2.1; exact ⟨h1, h.2.2.1, by omega⟩
  | _ + 1, _, .element _ _ _, _, _, _, _, h => by
      have h1 := h.1; have h2 := h.2.1; exact ⟨h1, h.2.2.1, by omega⟩

private theorem HydratableDomList_bounds {msg : Type} :
    ∀ (f : Nat) (ns : String) (ds : List (Html msg)) (a : DomArena msg) (lo hi : Nat) (ns' : List Dom.Node),
      HydratableDomList f ns ds a lo hi ns' → lo ≤ hi ∧ hi ≤ a.nextId
  | _, _, [], _, _, _, [], h => h
  | f, ns, d :: drest, a, lo, hi, n :: nrest, h => by
      rcases h with ⟨mid, hd, hrest⟩
      have b1 := HydratableDom_bounds f ns d a lo mid n hd
      have b2 := HydratableDomList_bounds f ns drest a mid hi nrest hrest
      exact ⟨by omega, b2.2⟩
  | _, _, [], _, _, _, _ :: _, h => False.elim h
  | _, _, _ :: _, _, _, _, [], h => False.elim h

private theorem HydratableDomList_nodes_lt {msg : Type} :
    ∀ (f : Nat) (ns : String) (ds : List (Html msg)) (a : DomArena msg) (lo hi : Nat) (ns' : List Dom.Node),
      HydratableDomList f ns ds a lo hi ns' → ∀ n ∈ ns', lo ≤ n.toNat ∧ n.toNat < hi
  | _, _, [], _, _, _, [], _ => fun _ h => nomatch h
  | f, ns, d :: drest, a, lo, hi, n :: nrest, h => by
      rcases h with ⟨mid, hd, hrest⟩
      intro x hx
      have hb1 := HydratableDom_bounds f ns d a lo mid n hd
      have hb2 := HydratableDomList_bounds f ns drest a mid hi nrest hrest
      rcases List.mem_cons.1 hx with rfl | htail
      · cases f with
        | zero => exact False.elim hd
        | succ f' =>
            cases d <;> exact ⟨hd.1, Nat.lt_of_lt_of_le hd.2.1 hb2.1⟩
      · have hr := HydratableDomList_nodes_lt f ns drest a mid hi nrest hrest x htail
        exact ⟨Nat.le_trans hb1.2.2 hr.1, hr.2⟩
  | _, _, [], _, _, _, _ :: _, h => False.elim h
  | _, _, _ :: _, _, _, _, [], h => False.elim h

private theorem HydratableDomListAux_bounds_le {msg : Type}
    (P : String → Html msg → DomArena msg → Nat → Nat → Dom.Node → Prop)
    (hP : ∀ ns d a lo hi n, P ns d a lo hi n → lo ≤ hi)
    (ns : String) :
    ∀ (ds : List (Html msg)) (a : DomArena msg) (lo hi : Nat) (ns' : List Dom.Node),
      HydratableDomListAux P ns ds a lo hi ns' → lo ≤ hi
  | [], _, _, _, [], h => h.1
  | d :: dr, a, _, _, n :: nr, ⟨mid, hd, hrest⟩ =>
      Nat.le_trans (hP ns d a _ mid n hd) (HydratableDomListAux_bounds_le P hP ns dr a mid _ nr hrest)
  | [], _, _, _, _ :: _, h => False.elim h
  | _ :: _, _, _, _, [], h => False.elim h

private theorem HydratableDomListAux_frame {msg : Type}
    (P : String → Html msg → DomArena msg → Nat → Nat → Dom.Node → Prop)
    (hP_bounds : ∀ ns d a lo hi n, P ns d a lo hi n → lo ≤ hi ∧ hi ≤ a.nextId)
    (hP_frame : ∀ ns d a a' lo hi n, a.nextId ≤ a'.nextId →
      (∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m) →
      P ns d a lo hi n → P ns d a' lo hi n)
    (ns : String) :
    ∀ (ds : List (Html msg)) (a a' : DomArena msg) (lo hi : Nat) (ns' : List Dom.Node),
      a.nextId ≤ a'.nextId →
      (∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m) →
      HydratableDomListAux P ns ds a lo hi ns' →
      HydratableDomListAux P ns ds a' lo hi ns'
  | [], _, _, _, _, [], hle, _, ⟨h1, h2⟩ => ⟨h1, Nat.le_trans h2 hle⟩
  | d :: drest, a, a', lo, hi, n :: nrest, hle, hfr, ⟨mid, hd, hrest⟩ =>
      let b1 := hP_bounds ns d a lo mid n hd
      let hmidLeHi := HydratableDomListAux_bounds_le P (fun _ _ _ _ _ _ h => (hP_bounds _ _ _ _ _ _ h).1)
        ns drest a mid hi nrest hrest
      ⟨mid,
       hP_frame ns d a a' lo mid n hle (fun m hm1 hm2 => hfr m hm1 (Nat.lt_of_lt_of_le hm2 hmidLeHi)) hd,
       HydratableDomListAux_frame P hP_bounds hP_frame ns drest a a' mid hi nrest hle
         (fun m hm1 hm2 => hfr m (Nat.le_trans b1.1 hm1) hm2) hrest⟩
  | [], _, _, _, _, _ :: _, _, _, h => False.elim h
  | _ :: _, _, _, _, _, [], _, _, h => False.elim h

private theorem HydratableDom_frame {msg : Type} :
    ∀ (f : Nat) (ns : String) (d : Html msg) (a a' : DomArena msg) (lo hi : Nat) (n : Dom.Node),
      a.nextId ≤ a'.nextId →
      (∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m) →
      HydratableDom f ns d a lo hi n →
      HydratableDom f ns d a' lo hi n
  | 0, _, _, _, _, _, _, _, _, _, h => False.elim h
  | _ + 1, ns, .text s, a, a', lo, hi, n, hle, hfr, h =>
      ⟨h.1, h.2.1, Nat.le_trans h.2.2.1 hle, by rw [hfr n h.1 h.2.1, h.2.2.2]⟩
  | f + 1, ns, .element tag attrs cs, a, a', lo, hi, n, hle, hfr, h => by
      rcases h with ⟨hlo, hhi, hnext, st, prev, domCs, hget, hm, hns, hownT, hownF⟩
      refine ⟨hlo, hhi, Nat.le_trans hnext hle, st, prev, domCs, ?_, hm, hns, hownT, ?_⟩
      · rw [hfr n hlo hhi, hget]
      · intro hown
        rcases hownF hown with ⟨mid, hmid, hk⟩
        refine ⟨mid, hmid, HydratableDomListAux_frame (HydratableDom f)
          (fun ns' d' a0 lo' hi' n' hd' =>
            let b := HydratableDom_bounds f ns' d' a0 lo' hi' n' hd'; ⟨b.2.2, b.2.1⟩)
          (fun ns' d' a0 a0' lo' hi' n' hle' hfr' hd' =>
            HydratableDom_frame f ns' d' a0 a0' lo' hi' n' hle' hfr' hd')
          (Dom.childNsOf ns tag) (coalesceTextRun cs) a a' mid hi domCs hle
          (fun m hm1 hm2 => hfr m (by omega) hm2) hk⟩

private theorem HydratableDomList_frame {msg : Type} (f : Nat) (ns : String) (ds : List (Html msg))
    (a a' : DomArena msg) (lo hi : Nat) (ns' : List Dom.Node)
    (hle : a.nextId ≤ a'.nextId)
    (hfr : ∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m)
    (h : HydratableDomList f ns ds a lo hi ns') :
    HydratableDomList f ns ds a' lo hi ns' :=
  HydratableDomListAux_frame (HydratableDom f)
    (fun ns0 d0 a0 lo0 hi0 n0 hd0 =>
      let b := HydratableDom_bounds f ns0 d0 a0 lo0 hi0 n0 hd0; ⟨b.2.2, b.2.1⟩)
    (HydratableDom_frame f)
    ns ds a a' lo hi ns' hle hfr h

/-- Imperative `hydrateTextSlotM` equivalence over `DomArena`:
    handles all three HTML5 hydration cases (`s == ""` placeholder insertion, `inTextRun` split
    insertion, and reused first text node trimming via `setText` when `hasMoreText rest`), returning
    exact `.text s` at `pre.length`. -/
theorem hydrateTextSlotM_empty_spec (a : DomArena msg) (parent : Dom.Node) (inTextRun : Bool)
    (moreInRun : Unit → Bool) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (pre suf : List Dom.Node) (_hlt : a.nextId < UInt32.size) (hnot : UInt32.ofNat a.nextId ∉ pre ++ suf)
    (hdisj : ∀ r ∈ suf, r ∉ pre)
    (hpreLen : pre.length < UInt32.size)
    (hparNe : parent ≠ UInt32.ofNat a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ suf)) :
    let ph := UInt32.ofNat a.nextId
    let ((outNode, outRun), a') :=
      (hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) inTextRun "" moreInRun).run a
    outNode = ph ∧ outRun = inTextRun ∧
    a'.nextId = a.nextId + 1 ∧
    a'.get ph = .text "" ∧
    a'.get parent = .element pns ptag pst pmg (pre ++ ph :: suf) ∧
    (∀ m : Dom.Node, m ≠ parent → m ≠ ph → a'.get m = a.get m) := by
  have huIdx : (UInt32.ofNat pre.length).toNat = pre.length := uint32_toNat_ofNat_lt pre.length hpreLen
  have hins : w3cInsertBefore (pre ++ suf) (UInt32.ofNat pre.length).toNat (UInt32.ofNat a.nextId) =
      pre ++ UInt32.ofNat a.nextId :: suf := by
    rw [huIdx]
    exact w3cInsertBefore_fresh_append pre suf (UInt32.ofNat a.nextId) hnot hdisj
  have hallocPar : (DomArena.mk (a.nextId + 1)
      (fun m => if m == UInt32.ofNat a.nextId then .text "" else a.store m)
      a.signals).get parent = .element pns ptag pst pmg (pre ++ suf) := by
    simp [DomArena.get, hparNe]; exact hpar
  dsimp only [hydrateTextSlotM]
  rw [if_pos (beq_self_eq_true "")]
  dsimp only [StateT.run, bind, StateT.bind, pure,
              MonadDom.createText, DomArena.alloc, MonadDom.insertBeforeNode, DomArena.modifyChildren, DomArena.modify]
  rw [hallocPar]
  dsimp only
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [DomArena.get, DomArena.set, hparNe.symm]
  · rw [DomArena.get_set_self, hins]
  · intro m hm1 hm2
    simp [DomArena.get, DomArena.set, hm1, hm2]

theorem hydrateTextSlotM_split_spec (a : DomArena msg) (parent : Dom.Node) (s : String)
    (hs : s ≠ "") (moreInRun : Unit → Bool)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (pre suf : List Dom.Node) (_hlt : a.nextId < UInt32.size) (hnot : UInt32.ofNat a.nextId ∉ pre ++ suf)
    (hdisj : ∀ r ∈ suf, r ∉ pre)
    (hpreLen : pre.length < UInt32.size)
    (hparNe : parent ≠ UInt32.ofNat a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ suf)) :
    let tn := UInt32.ofNat a.nextId
    let ((outNode, outRun), a') :=
      (hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) true s moreInRun).run a
    outNode = tn ∧ outRun = true ∧
    a'.nextId = a.nextId + 1 ∧
    a'.get tn = .text s ∧
    a'.get parent = .element pns ptag pst pmg (pre ++ tn :: suf) ∧
    (∀ m : Dom.Node, m ≠ parent → m ≠ tn → a'.get m = a.get m) := by
  have huIdx : (UInt32.ofNat pre.length).toNat = pre.length := uint32_toNat_ofNat_lt pre.length hpreLen
  have hne : (s == "") = false := beq_eq_false_iff_ne.2 hs
  have hins : w3cInsertBefore (pre ++ suf) (UInt32.ofNat pre.length).toNat (UInt32.ofNat a.nextId) =
      pre ++ UInt32.ofNat a.nextId :: suf := by
    rw [huIdx]
    exact w3cInsertBefore_fresh_append pre suf (UInt32.ofNat a.nextId) hnot hdisj
  have hallocPar : (DomArena.mk (a.nextId + 1)
      (fun m => if m == UInt32.ofNat a.nextId then .text s else a.store m)
      a.signals).get parent = .element pns ptag pst pmg (pre ++ suf) := by
    simp [DomArena.get, hparNe]; exact hpar
  dsimp only [hydrateTextSlotM]
  rw [if_neg (by simp [hne]), if_pos rfl]
  dsimp only [StateT.run, bind, StateT.bind, pure,
              MonadDom.createText, DomArena.alloc, MonadDom.insertBeforeNode, DomArena.modifyChildren, DomArena.modify]
  rw [hallocPar]
  dsimp only
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [DomArena.get, DomArena.set, hparNe.symm]
  · rw [DomArena.get_set_self, hins]
  · intro m hm1 hm2
    simp [DomArena.get, DomArena.set, hm1, hm2]

theorem hydrateTextSlotM_head_spec (a : DomArena msg) (parent tn : Dom.Node) (s rawTail : String)
    (hs : s ≠ "") (more : Bool) (hmore : more = false → rawTail = "")
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (pre domRest : List Dom.Node)
    (hpreLen : pre.length < UInt32.size)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ tn :: domRest))
    (htn : a.get tn = .text (s ++ rawTail)) :
    let ((outNode, outRun), a') :=
      (hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) false s (fun () => more)).run a
    outNode = tn ∧ outRun = true ∧
    a'.nextId = a.nextId ∧
    a'.get tn = .text s ∧
    (∀ m : Dom.Node, m ≠ tn → a'.get m = a.get m) := by
  have huIdx : (UInt32.ofNat pre.length).toNat = pre.length := uint32_toNat_ofNat_lt pre.length hpreLen
  have hne : (s == "") = false := beq_eq_false_iff_ne.2 hs
  have hgetD : (pre ++ tn :: domRest).getD pre.length 0 = tn := getD_append_right tn 0 pre domRest
  cases more
  · have hrt := hmore rfl
    subst hrt
    simp only [hydrateTextSlotM, hne, Bool.false_eq_true, ↓reduceIte, StateT.run, bind, StateT.bind,
               pure, hpar, huIdx]
    rw [hgetD]
    exact ⟨rfl, rfl, rfl, by simpa using htn, fun _ _ => rfl⟩
  · simp only [hydrateTextSlotM, hne, Bool.false_eq_true, ↓reduceIte, StateT.run, bind, StateT.bind,
               pure, MonadDom.setText, DomArena.modify, hpar, huIdx]
    rw [hgetD, htn]
    exact ⟨rfl, rfl, rfl, DomArena.get_set_self _ _ _, fun m hm => DomArena.get_set_ne _ _ hm⟩

private theorem HydratableDomList_cons_bounds {msg : Type} {f : Nat} {ns : String}
    {d : Html msg} {drest : List (Html msg)} {a : DomArena msg} {lo hi : Nat} {n : Dom.Node} {nrest : List Dom.Node}
    (h : HydratableDomList f ns (d :: drest) a lo hi (n :: nrest)) :
    ∃ mid, lo ≤ mid ∧ mid ≤ hi ∧ hi ≤ a.nextId ∧
      HydratableDom f ns d a lo mid n ∧ HydratableDomList f ns drest a mid hi nrest := by
  rcases h with ⟨mid, hd, hrest⟩
  have b1 := HydratableDom_bounds f ns d a lo mid n hd
  have b2 := HydratableDomList_bounds f ns drest a mid hi nrest hrest
  exact ⟨mid, b1.2.2, b2.1, b2.2, hd, hrest⟩

private theorem htmlListDepth_cons_pos {msg : Type} (c : Html msg) (rest : List (Html msg)) :
    1 ≤ htmlListDepth (c :: rest) := by
  have hc : 1 ≤ htmlDepth c := by
    cases c with
    | text _ => simp [htmlDepth]
    | element _ _ _ => simp [htmlDepth]
  exact Nat.le_trans hc (by simp [htmlListDepth, Nat.le_max_left])

private theorem dropCurrentTextRun_head_element {msg : Type} (tag : String) (attrs : List (Attr msg))
    (kids rest : List (Html msg)) :
    dropCurrentTextRun (.element tag attrs kids :: rest) =
      .element tag attrs kids :: coalesceTextRun rest := by
  simp [dropCurrentTextRun, Html.textOf?]

private theorem coalesceTextRun_head_element {msg : Type} (tag : String) (attrs : List (Attr msg))
    (kids rest : List (Html msg)) :
    coalesceTextRun (.element tag attrs kids :: rest) =
      .element tag attrs kids :: coalesceTextRun rest := by
  simp [coalesceTextRun, Html.textOf?]

private theorem textOf_none_is_element {msg : Type} :
    ∀ {c : Html msg}, c.textOf? = none → ∃ tag attrs kids, c = .element tag attrs kids
  | .text _, h => by simp [Html.textOf?] at h
  | .element tag attrs kids, _ => ⟨tag, attrs, kids, rfl⟩

def DomHydrateSpecAt {msg : Type} (f : Nat) : Prop :=
  ∀ (ns : String) (h : Html msg) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat),
    a.nextId + htmlNodeCount h < UInt32.size →
    htmlDepth h ≤ f + 1 →
    HydratableDom (f + 1) ns h a lo hi root →
    let aOut := ((hydrateDomM (m := StateM (DomArena msg)) h root).run a).2
    a.nextId ≤ aOut.nextId ∧
    aOut.nextId ≤ a.nextId + htmlNodeCount h ∧
    SubtreeInSet (f + 1) aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) root ∧
    (∀ m : Dom.Node, (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns h) ∧
    (h.DomClean = true →
      CleanDomSubtree (f + 1) ns h aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) root)

def KidsHydrateSpecAt {msg : Type} (f : Nat) : Prop :=
  ∀ (childNs : String) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (target : List (Html msg)) (inTextRun : Bool)
    (pre domCs : List Dom.Node) (lo hi : Nat) (a : DomArena msg),
    pre.length + target.length < UInt32.size →
    a.nextId + htmlListNodeCount target < UInt32.size →
    htmlListDepth target ≤ f →
    parent.toNat < lo →
    (∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet f a Sx x) →
    a.get parent = .element pns ptag pst pmg (pre ++ domCs) →
    HydratableDomList f childNs (if inTextRun then dropCurrentTextRun target else coalesceTextRun target) a lo hi domCs →
    let aOut := ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) inTextRun target).run a).2
    ∃ (hydratedCs : List Dom.Node),
      a.nextId ≤ aOut.nextId ∧
      aOut.nextId ≤ a.nextId + htmlListNodeCount target ∧
      aOut.get parent = .element pns ptag pst pmg (pre ++ hydratedCs) ∧
      (∀ c ∈ hydratedCs, SubtreeInSet f aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) c) ∧
      (∀ m : Dom.Node, m ≠ parent → (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      DomTreeListAssocEquiv (hydratedCs.map (readDomTree f aOut)) (specDomList childNs target) ∧
      (Html.DomCleanList target = true →
        CleanDomChildren f childNs target aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) hydratedCs)

private theorem hydrateDomKidsM_fresh_nextId {msg : Type} (f : Nat) (childNs : String)
    (parent : Dom.Node) (hs : List (Html msg)) (pre domCs : List Dom.Node) (lo hi : Nat)
    (a : DomArena msg) (hfPos : 1 ≤ f) (hbound : a.nextId < UInt32.size) (hparLo : parent.toNat < lo)
    (hpreSub : ∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet f a Sx x)
    (hdom : HydratableDomList f childNs hs a lo hi domCs) :
    UInt32.ofNat a.nextId ∉ pre ++ domCs ∧ parent ≠ UInt32.ofNat a.nextId := by
  rcases HydratableDomList_bounds f childNs hs a lo hi domCs hdom with ⟨hloHi, hhiNext⟩
  have huNext : (UInt32.ofNat a.nextId).toNat = a.nextId := uint32_toNat_ofNat_lt a.nextId hbound
  refine ⟨fun hm => ?_, fun heq => by rw [heq, huNext] at hparLo; omega⟩
  rcases List.mem_append.1 hm with hp | hd
  · rcases hpreSub _ hp with ⟨Sx, hSx, hsub⟩
    cases f with
    | zero => omega
    | succ f' => rcases hSx _ hsub.1 with h1 | h2 <;> omega
  · have hlt := HydratableDomList_nodes_lt f childNs hs a lo hi domCs hdom _ hd
    omega

private theorem hydrateDomKidsM_allocText_step {msg : Type} (f : Nat) (childNs : String)
    (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (s : String) (rest : List (Html msg)) (inTextRun inRun' : Bool)
    (targetRest : List (Html msg)) (pre domCs : List Dom.Node) (lo hi : Nat)
    (a aMid : DomArena msg) (hfPos : 1 ≤ f)
    (hparLo : parent.toNat < lo) (hloHi : lo ≤ hi) (hhiNext : hi ≤ a.nextId)
    (hbound : a.nextId + (1 + htmlListNodeCount rest) < UInt32.size)
    (hpreSub : ∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet f a Sx x)
    (hparNeNew : parent ≠ UInt32.ofNat a.nextId)
    (haMidNext : aMid.nextId = a.nextId + 1)
    (hgetNew : aMid.get (UInt32.ofNat a.nextId) = .text s)
    (hframeMid : ∀ m : Dom.Node, m ≠ parent → m ≠ UInt32.ofNat a.nextId → aMid.get m = a.get m)
    (hdom' : HydratableDomList f childNs targetRest a lo hi domCs)
    (hihFn :
      (∀ x ∈ pre ++ [UInt32.ofNat a.nextId], ∃ Sx,
        (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < aMid.nextId)) ∧ SubtreeInSet f aMid Sx x) →
      HydratableDomList f childNs targetRest aMid lo hi domCs →
      let aOut := ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
        (UInt32.ofNat (pre ++ [UInt32.ofNat a.nextId]).length) inRun' rest).run aMid).2
      ∃ hydratedCs, aMid.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ aMid.nextId + htmlListNodeCount rest ∧
        aOut.get parent = .element pns ptag pst pmg ((pre ++ [UInt32.ofNat a.nextId]) ++ hydratedCs) ∧
        (∀ c ∈ hydratedCs, SubtreeInSet f aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (aMid.nextId ≤ k ∧ k < aOut.nextId)) c) ∧
        (∀ m : Dom.Node, m ≠ parent → (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < aMid.nextId → aOut.get m = aMid.get m) ∧
        DomTreeListAssocEquiv (hydratedCs.map (readDomTree f aOut)) (specDomList childNs rest) ∧
        (Html.DomCleanList rest = true →
          CleanDomChildren f childNs rest aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (aMid.nextId ≤ k ∧ k < aOut.nextId)) hydratedCs))
    (hstep :
      ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) inTextRun
        (.text s :: rest)).run a).2 =
      ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
        (UInt32.ofNat (pre ++ [UInt32.ofNat a.nextId]).length) inRun' rest).run aMid).2) :
    let aOut := ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) inTextRun
      (.text s :: rest)).run a).2
    ∃ hydratedCs, a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount (.text s :: rest) ∧
      aOut.get parent = .element pns ptag pst pmg (pre ++ hydratedCs) ∧
      (∀ c ∈ hydratedCs, SubtreeInSet f aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) c) ∧
      (∀ m : Dom.Node, m ≠ parent → (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      DomTreeListAssocEquiv (hydratedCs.map (readDomTree f aOut)) (specDomList childNs (.text s :: rest)) ∧
      (Html.DomCleanList (.text s :: rest) = true →
        CleanDomChildren f childNs (.text s :: rest) aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) hydratedCs) := by
  let tn := UInt32.ofNat a.nextId
  have hdomMid : HydratableDomList f childNs targetRest aMid lo hi domCs :=
    HydratableDomList_frame f childNs targetRest a aMid lo hi domCs (by rw [haMidNext]; omega)
      (fun m hm1 hm2 => hframeMid m (by intro heq; rw [heq] at hm1; omega)
        (by intro heq
            have hmNat : m.toNat = a.nextId := by
              rw [heq]; exact uint32_toNat_ofNat_lt a.nextId (by omega)
            omega))
      hdom'
  have hpreMid : ∀ x ∈ pre ++ [tn], ∃ Sx,
      (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < aMid.nextId)) ∧ SubtreeInSet f aMid Sx x := by
    intro x hx
    rcases List.mem_append.1 hx with hOld | hNew
    · rcases hpreSub x hOld with ⟨Sx, hSx, hsub⟩
      refine ⟨Sx, fun k hk => ?_, ?_⟩
      · rcases hSx k hk with h1 | h2
        · exact .inl h1
        · exact .inr ⟨h2.1, Nat.lt_of_lt_of_le h2.2 (by rw [haMidNext]; omega)⟩
      · exact (SubtreeInSet_frame (fun m hm => hframeMid m
          (by intro heq; rw [heq] at hm; rcases hSx parent.toNat hm with h1 | h2 <;> omega)
          (by intro heq
              have hmNat : m.toNat = a.nextId := by
                rw [heq]; exact uint32_toNat_ofNat_lt a.nextId (by omega)
              rcases hSx m.toNat hm with h1 | h2 <;> omega)) hsub).1
    · simp only [List.mem_singleton] at hNew; subst hNew
      refine ⟨fun k => k = a.nextId, fun k hk => .inr ⟨by omega, by rw [haMidNext]; omega⟩, ?_⟩
      cases f with
      | zero => omega
      | succ f' =>
          have htnNat : tn.toNat = a.nextId := uint32_toNat_ofNat_lt a.nextId (by omega)
          exact ⟨htnNat, by simp [tn, hgetNew]⟩
  rcases hihFn hpreMid hdomMid with ⟨hydRest, hnextR, hboundR, hparR, hsubR, hfrR, heqR, hclR⟩
  rw [hstep]
  refine ⟨tn :: hydRest, by rw [haMidNext] at hnextR; omega,
    by rw [haMidNext] at hboundR; simp only [htmlListNodeCount, htmlNodeCount]; omega,
    by simpa [List.append_assoc] using hparR, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases List.mem_cons.1 hz with hzEq | htail
    · rw [hzEq]
      cases f with
      | zero => omega
      | succ f' =>
          have htnNat : tn.toNat = a.nextId := uint32_toNat_ofNat_lt a.nextId (by omega)
          have haOutTn := hfrR tn hparNeNew.symm (.inr (by rw [htnNat]; omega)) (by rw [haMidNext, htnNat]; omega)
          have hnextTn : a.nextId < ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
              (UInt32.ofNat (pre ++ [UInt32.ofNat a.nextId]).length) inRun' rest).run aMid).2.nextId := by
            rw [haMidNext] at hnextR; omega
          exact ⟨.inr ⟨by rw [htnNat]; exact Nat.le_refl _, by rw [htnNat]; exact hnextTn⟩, by
            rw [haOutTn, hgetNew]; trivial⟩
    · exact SubtreeInSet_mono (fun k hkS => by
        rcases hkS with h1 | h2
        · exact .inl h1
        · exact .inr ⟨by rw [haMidNext] at h2; omega, h2.2⟩) (hsubR z htail)
  · intro m hmPar hmOut hmLt
    rw [hfrR m hmPar hmOut (by rw [haMidNext]; omega),
        hframeMid m hmPar (by intro heq
                              have hmNat : m.toNat = a.nextId := by
                                rw [heq]; exact uint32_toNat_ofNat_lt a.nextId (by omega)
                              omega)]
  · have hreadTn : readDomTree f ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
        (UInt32.ofNat (pre ++ [tn]).length) inRun' rest).run aMid).2 tn = .text s := by
      cases f with
      | zero => omega
      | succ f' =>
          have htnNat : tn.toNat = a.nextId := uint32_toNat_ofNat_lt a.nextId (by omega)
          have haOutTn := hfrR tn hparNeNew.symm (.inr (by rw [htnNat]; omega)) (by rw [haMidNext, htnNat]; omega)
          dsimp only [readDomTree]; rw [haOutTn, hgetNew]
    simp only [List.map_cons, specDomList, specDom, DomTreeListAssocEquiv]
    rw [hreadTn]
    exact ⟨rfl, heqR⟩
  · intro hc
    simp only [Html.DomCleanList, Html.DomClean, Bool.true_and] at hc
    have hcleanTn : CleanDomSubtree f childNs (.text s)
        ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (pre ++ [tn]).length) inRun' rest).run aMid).2
        (fun k => k = a.nextId) tn := by
      cases f with
      | zero => omega
      | succ f' =>
          have htnNat : tn.toNat = a.nextId := uint32_toNat_ofNat_lt a.nextId (by omega)
          have haOutTn := hfrR tn hparNeNew.symm (.inr (by rw [htnNat]; omega)) (by rw [haMidNext, htnNat]; omega)
          exact ⟨htnNat, by rw [haOutTn, hgetNew]⟩
    refine ⟨fun k => k = a.nextId,
      fun k => (lo ≤ k ∧ k < hi) ∨ (aMid.nextId ≤ k ∧ k < ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
        (UInt32.ofNat (pre ++ [tn]).length) inRun' rest).run aMid).2.nextId),
      fun _ hk => .inr ⟨hk ▸ Nat.le_refl _, by rw [haMidNext] at hnextR; omega⟩,
      fun _ hk => hk.elim .inl (fun h => .inr ⟨by rw [haMidNext] at h; omega, h.2⟩),
      fun _ hk1 hk2 => by rcases hk2 with h | h <;> omega,
      hcleanTn, hclR hc⟩

private theorem hydrateDomKidsM_spec_step {msg : Type} (f : Nat)
    (hDom : ∀ f' < f, @DomHydrateSpecAt msg f') :
    @KidsHydrateSpecAt msg f := by
  intro childNs parent pns ptag pst pmg target
  induction target with
  | nil =>
      intro inTextRun pre domCs lo hi a _ _ _ _ _ hpar hdom
      have hdomNil : domCs = [] := by
        cases inTextRun <;> simp [coalesceTextRun, dropCurrentTextRun] at hdom <;> cases domCs with
        | nil => rfl
        | cons _ _ => exact False.elim hdom
      subst hdomNil
      refine ⟨[], ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hydrateDomKidsM, StateT.run, pure, StateT.pure]
      · simp [hydrateDomKidsM, StateT.run, pure, StateT.pure, htmlListNodeCount]
      · simpa [hydrateDomKidsM, StateT.run, pure, StateT.pure] using hpar
      · intro _ hm; nomatch hm
      · intro _ _ _ _; rfl
      · simp [specDomList, DomTreeListAssocEquiv]
      · intro _; trivial
  | cons c rest ih =>
      intro inTextRun pre domCs lo hi a hlen hbound hdep hparLo hpreSub hpar hdom
      rcases HydratableDomList_bounds f childNs _ a lo hi domCs hdom with ⟨hloHi, hhiNext⟩
      have hposF : 1 ≤ f := Nat.le_trans (htmlListDepth_cons_pos c rest) hdep
      have huIdxNext : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) := by
        simp only [List.length_cons] at hlen
        exact uint32_ofNat_succ pre.length (by omega)
      have hdisjDom : ∀ r ∈ domCs, r ∉ pre := by
        intro r hr hmem
        have hlt := HydratableDomList_nodes_lt f childNs _ a lo hi domCs hdom r hr
        rcases hpreSub r hmem with ⟨Sx, hSx, hsub⟩
        cases f with
        | zero => omega
        | succ f' => rcases hSx r.toNat hsub.1 with h1 | h2 <;> omega
      cases htxt : c.textOf? with
      | some s =>
          have hcEq : c = .text s := textOf_eq_some_iff.1 htxt
          subst hcEq
          simp only [htmlListNodeCount, htmlNodeCount] at hbound
          simp only [htmlListDepth] at hdep
          have hrestDep : htmlListDepth rest ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
          by_cases hsEmpty : s = ""
          · subst hsEmpty
            have hdom' : HydratableDomList f childNs (if inTextRun then dropCurrentTextRun rest else coalesceTextRun rest) a lo hi domCs := by
              cases inTextRun <;> simpa [coalesceTextRun, dropCurrentTextRun] using hdom
            rcases hydrateDomKidsM_fresh_nextId f childNs parent _ pre domCs lo hi a hposF (by omega) hparLo hpreSub hdom' with
              ⟨hnotIn, hparNePh⟩
            let ph := UInt32.ofNat a.nextId
            let resSlot := (hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
              inTextRun "" (fun () => hasMoreText rest)).run a
            let aMid := resSlot.2
            have hslot := hydrateTextSlotM_empty_spec a parent inTextRun (fun () => hasMoreText rest)
              pns ptag pst pmg pre domCs (by omega) hnotIn hdisjDom (by simp at hlen; omega) hparNePh hpar
            have haMidNext : aMid.nextId = a.nextId + 1 := hslot.2.2.1
            have hgetParMid : aMid.get parent = .element pns ptag pst pmg (pre ++ ph :: domCs) := hslot.2.2.2.2.1
            exact hydrateDomKidsM_allocText_step f childNs parent pns ptag pst pmg "" rest inTextRun inTextRun
              _ pre domCs lo hi a aMid hposF hparLo hloHi hhiNext hbound hpreSub hparNePh
              haMidNext hslot.2.2.2.1 hslot.2.2.2.2.2 hdom'
              (fun hpreMid hdomMid => ih inTextRun (pre ++ [ph]) domCs lo hi aMid
                (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen; omega)
                (by rw [haMidNext]; omega) hrestDep hparLo hpreMid (by simpa using hgetParMid) hdomMid)
              (by
                dsimp only [StateT.run, hydrateDomKidsM, Html.textOf?, bind, StateT.bind]
                have hSlotEq : hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
                    inTextRun "" (fun () => hasMoreText rest) a = ((ph, inTextRun), aMid) :=
                  Prod.ext (Prod.ext hslot.1 hslot.2.1) rfl
                rw [hSlotEq]
                dsimp only
                simp only [List.length_append, List.length_singleton]
                rw [← huIdxNext])
          · cases inTextRun with
            | true =>
                have hdom' : HydratableDomList f childNs (dropCurrentTextRun rest) a lo hi domCs := by
                  simpa [dropCurrentTextRun, Html.textOf?, hsEmpty] using hdom
                rcases hydrateDomKidsM_fresh_nextId f childNs parent _ pre domCs lo hi a hposF (by omega) hparLo hpreSub hdom' with
                  ⟨hnotIn, hparNeTn⟩
                let tn := UInt32.ofNat a.nextId
                let resSlot := (hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
                  true s (fun () => hasMoreText rest)).run a
                let aMid := resSlot.2
                have hslot := hydrateTextSlotM_split_spec a parent s hsEmpty (fun () => hasMoreText rest)
                  pns ptag pst pmg pre domCs (by omega) hnotIn hdisjDom (by simp at hlen; omega) hparNeTn hpar
                have haMidNext : aMid.nextId = a.nextId + 1 := hslot.2.2.1
                have hgetParMid : aMid.get parent = .element pns ptag pst pmg (pre ++ tn :: domCs) := hslot.2.2.2.2.1
                exact hydrateDomKidsM_allocText_step f childNs parent pns ptag pst pmg s rest true true
                  _ pre domCs lo hi a aMid hposF hparLo hloHi hhiNext hbound hpreSub hparNeTn
                  haMidNext hslot.2.2.2.1 hslot.2.2.2.2.2 hdom'
                  (fun hpreMid hdomMid => ih true (pre ++ [tn]) domCs lo hi aMid
                    (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen; omega)
                    (by rw [haMidNext]; omega) hrestDep hparLo hpreMid (by simpa using hgetParMid)
                    (by simpa using hdomMid))
                  (by
                    dsimp only [StateT.run, hydrateDomKidsM, Html.textOf?, bind, StateT.bind]
                    have hSlotEq : hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
                        true s (fun () => hasMoreText rest) a = ((tn, true), aMid) :=
                      Prod.ext (Prod.ext hslot.1 hslot.2.1) rfl
                    rw [hSlotEq]
                    dsimp only
                    simp only [List.length_append, List.length_singleton]
                    rw [← huIdxNext])
            | false =>
                have hdomCoal : HydratableDomList f childNs (.text (s ++ restOfTextRun rest) :: dropCurrentTextRun rest) a lo hi domCs := by
                  simpa [coalesceTextRun, Html.textOf?, hsEmpty] using hdom
                cases domCs with
                | nil => exact False.elim hdomCoal
                | cons tn domRest =>
                    rcases HydratableDomList_cons_bounds hdomCoal with ⟨mid, hloMid, hmidHi, hiNext, htnDom, hrestDom⟩
                    cases f with
                    | zero => omega
                    | succ f' =>
                        rcases htnDom with ⟨htnLo, htnMid, _, hgetTn⟩
                        let resSlot := (hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
                          false s (fun () => hasMoreText rest)).run a
                        let aMid := resSlot.2
                        have hslot := hydrateTextSlotM_head_spec a parent tn s (restOfTextRun rest) hsEmpty
                          (hasMoreText rest) (hasMoreText_false_restOfTextRun rest) pns ptag pst pmg
                          pre domRest (by simp at hlen; omega) hpar hgetTn
                        have hresNode : resSlot.1.1 = tn := hslot.1
                        have hresRun : resSlot.1.2 = true := hslot.2.1
                        have haMidNext : aMid.nextId = a.nextId := hslot.2.2.1
                        have hgetTnMid : aMid.get tn = .text s := hslot.2.2.2.1
                        have hframeMid : ∀ m : Dom.Node, m ≠ tn → aMid.get m = a.get m := hslot.2.2.2.2
                        have hparNeTn : parent ≠ tn := by intro heq; rw [heq] at hparLo; omega
                        have hparMid : aMid.get parent = .element pns ptag pst pmg ((pre ++ [tn]) ++ domRest) := by
                          rw [hframeMid parent hparNeTn, hpar]; simp [List.append_assoc]
                        have hdomMid : HydratableDomList (f' + 1) childNs (dropCurrentTextRun rest) aMid mid hi domRest :=
                          HydratableDomList_frame (f' + 1) childNs (dropCurrentTextRun rest) a aMid mid hi domRest
                            (by rw [haMidNext]; exact Nat.le_refl _)
                            (fun m hm1 _ => hframeMid m (by intro heq; rw [heq] at hm1; omega))
                            hrestDom
                        have hpreMid : ∀ x ∈ pre ++ [tn], ∃ Sx,
                            (∀ k, Sx k → (parent.toNat < k ∧ k < mid) ∨ (hi ≤ k ∧ k < aMid.nextId)) ∧
                            SubtreeInSet (f' + 1) aMid Sx x := by
                          intro x hx
                          rcases List.mem_append.1 hx with hOld | hNew
                          · rcases hpreSub x hOld with ⟨Sx, hSx, hsub⟩
                            refine ⟨Sx, fun k hk => ?_, ?_⟩
                            · rcases hSx k hk with h1 | h2
                              · exact .inl ⟨h1.1, Nat.lt_of_lt_of_le h1.2 hloMid⟩
                              · exact .inr ⟨h2.1, by rw [haMidNext]; exact h2.2⟩
                            · exact (SubtreeInSet_frame (fun m hm => hframeMid m (by
                                intro heq; rw [heq] at hm
                                rcases hSx tn.toNat hm with h1 | h2 <;> omega)) hsub).1
                          · simp only [List.mem_singleton] at hNew
                            rw [hNew]
                            refine ⟨fun k => k = tn.toNat, fun k hk => .inl ⟨by rw [hk]; omega, by rw [hk]; exact htnMid⟩, ?_⟩
                            exact ⟨rfl, by simp [hgetTnMid]⟩
                        have hih := ih true (pre ++ [tn]) domRest mid hi aMid
                          (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen; omega)
                          (by rw [haMidNext]; omega)
                          hrestDep (by omega) hpreMid hparMid (by simpa using hdomMid)
                        have hstep :
                            ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) false
                              (.text s :: rest)).run a).2 =
                            ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (pre ++ [tn]).length) true
                              rest).run aMid).2 := by
                          dsimp only [StateT.run, hydrateDomKidsM, Html.textOf?, bind, StateT.bind]
                          have hSlotEq : hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
                              false s (fun () => hasMoreText rest) a = ((tn, true), aMid) :=
                            Prod.ext (Prod.ext hresNode hresRun) rfl
                          rw [hSlotEq]
                          dsimp only
                          simp only [List.length_append, List.length_singleton]
                          rw [← huIdxNext]
                        rcases hih with ⟨hydRest, hnextR, hboundR, hparR, hsubR, hfrR, heqR, hclR⟩
                        rw [hstep]
                        have haOutTn : ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
                            (UInt32.ofNat (pre ++ [tn]).length) true rest).run aMid).2.get tn = .text s := by
                          rw [hfrR tn hparNeTn.symm (.inl htnMid) (by rw [haMidNext]; omega), hgetTnMid]
                        refine ⟨tn :: hydRest, ?_⟩
                        refine ⟨by rw [haMidNext] at hnextR; omega,
                          by rw [haMidNext] at hboundR; simp only [htmlListNodeCount, htmlNodeCount]; omega,
                          by simpa [List.append_assoc] using hparR, ?_, ?_, ?_, ?_⟩
                        · intro z hz
                          rcases List.mem_cons.1 hz with hzEq | htail
                          · rw [hzEq]
                            exact ⟨.inl ⟨htnLo, Nat.lt_of_lt_of_le htnMid hmidHi⟩, by rw [haOutTn]; trivial⟩
                          · exact SubtreeInSet_mono (fun k hkS => by
                              rcases hkS with ⟨h1, h2⟩ | ⟨h1, h2⟩
                              · exact .inl ⟨Nat.le_trans hloMid h1, h2⟩
                              · exact .inr ⟨by rw [haMidNext] at h1; omega, h2⟩) (hsubR z htail)
                        · intro m hmPar hmOut hmLt
                          rw [hfrR m hmPar (hmOut.elim (fun h1 => .inl (by omega)) .inr) (by rw [haMidNext]; omega),
                              hframeMid m (by intro heq; rw [heq] at hmOut; rcases hmOut with h1 | h2 <;> omega)]
                        · have hreadTn : readDomTree (f' + 1) ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
                              (UInt32.ofNat (pre ++ [tn]).length) true rest).run aMid).2 tn = .text s := by
                            dsimp only [readDomTree]; rw [haOutTn]
                          simp only [List.map_cons, specDomList, specDom, DomTreeListAssocEquiv]
                          rw [hreadTn]
                          exact ⟨rfl, heqR⟩
                        · intro hc
                          simp only [Html.DomCleanList, Html.DomClean, Bool.true_and] at hc
                          refine ⟨fun k => lo ≤ k ∧ k < mid,
                            fun k => (mid ≤ k ∧ k < hi) ∨ (aMid.nextId ≤ k ∧ k < ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
                              (UInt32.ofNat (pre ++ [tn]).length) true rest).run aMid).2.nextId),
                            fun _ hk => .inl ⟨hk.1, Nat.lt_of_lt_of_le hk.2 hmidHi⟩,
                            fun _ hk => hk.elim (fun h => .inl ⟨Nat.le_trans hloMid h.1, h.2⟩) (fun h => .inr ⟨by rw [haMidNext] at h; exact h.1, h.2⟩),
                            fun _ hk1 hk2 => by rcases hk2 with h | h <;> omega,
                            ⟨⟨htnLo, htnMid⟩, haOutTn⟩, hclR hc⟩
      | none =>
          rcases textOf_none_is_element htxt with ⟨tag, attrs, kids, hcEq⟩
          subst hcEq
          simp only [htmlListNodeCount] at hbound
          simp only [htmlListDepth] at hdep
          have hcDep : htmlDepth (.element tag attrs kids) ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
          have hrestDep : htmlListDepth rest ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
          have hdomElem : HydratableDomList f childNs (.element tag attrs kids :: coalesceTextRun rest) a lo hi domCs := by
            cases inTextRun
            · simpa [coalesceTextRun_head_element] using hdom
            · simpa [dropCurrentTextRun_head_element] using hdom
          cases domCs with
          | nil => exact False.elim hdomElem
          | cons child domRest =>
              rcases HydratableDomList_cons_bounds hdomElem with ⟨mid, hloMid, hmidHi, hiNext, hchildDom, hrestDom⟩
              cases f with
              | zero => simp [htmlDepth] at hcDep
              | succ f' =>
                  have huIdx : (UInt32.ofNat pre.length).toNat = pre.length :=
                    uint32_toNat_ofNat_lt pre.length (by simp at hlen; omega)
                  have hgetD : (pre ++ child :: domRest).getD pre.length 0 = child := getD_append_right child 0 pre domRest
                  have hchildAt : (MonadDom.childAt (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)).run a =
                      (child, a) := by
                    simp only [MonadDom.childAt, StateT.run, hpar, huIdx]
                    rw [hgetD]
                  let aMid := ((hydrateDomM (m := StateM (DomArena msg)) (.element tag attrs kids) child).run a).2
                  have hchildSpec := hDom f' (Nat.lt_succ_self f') childNs (.element tag attrs kids) child a lo mid
                    (by omega) hcDep hchildDom
                  dsimp only [StateT.run] at hchildSpec
                  have haMidEq : (hydrateDomM (m := StateM (DomArena msg)) (.element tag attrs kids) child a).2 = aMid := rfl
                  rw [haMidEq] at hchildSpec
                  rcases hchildSpec with ⟨haMidNext, haMidBound, hchildSubMid, hframeMid, hequivChild, hchildClMid⟩
                  have hparMid : aMid.get parent = .element pns ptag pst pmg ((pre ++ [child]) ++ domRest) := by
                    rw [hframeMid parent (.inl hparLo) (by omega), hpar]; simp [List.append_assoc]
                  have hdomMid : HydratableDomList (f' + 1) childNs (coalesceTextRun rest) aMid mid hi domRest :=
                    HydratableDomList_frame (f' + 1) childNs (coalesceTextRun rest) a aMid mid hi domRest
                      haMidNext (fun m hm1 _ => hframeMid m (.inr hm1) (by omega)) hrestDom
                  have hpreMid : ∀ x ∈ pre ++ [child], ∃ Sx,
                      (∀ k, Sx k → (parent.toNat < k ∧ k < mid) ∨ (hi ≤ k ∧ k < aMid.nextId)) ∧
                      SubtreeInSet (f' + 1) aMid Sx x := by
                    intro x hx
                    rcases List.mem_append.1 hx with hOld | hNew
                    · rcases hpreSub x hOld with ⟨Sx, hSx, hsub⟩
                      refine ⟨Sx, fun k hk => ?_, ?_⟩
                      · rcases hSx k hk with h1 | h2
                        · exact .inl ⟨h1.1, Nat.lt_of_lt_of_le h1.2 hloMid⟩
                        · exact .inr ⟨h2.1, Nat.lt_of_lt_of_le h2.2 haMidNext⟩
                      · exact (SubtreeInSet_frame (fun m hm => hframeMid m
                          (by rcases hSx m.toNat hm with h1 | h2
                              · exact .inl h1.2
                              · exact .inr (Nat.le_trans hmidHi h2.1))
                          (by rcases hSx m.toNat hm with h1 | h2
                              · omega
                              · exact h2.2)) hsub).1
                    · simp only [List.mem_singleton] at hNew; subst hNew
                      refine ⟨fun k => (lo ≤ k ∧ k < mid) ∨ (a.nextId ≤ k ∧ k < aMid.nextId), fun k hk => ?_, hchildSubMid⟩
                      · rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
                        · exact .inl ⟨by omega, h2⟩
                        · exact .inr ⟨by omega, h2⟩
                  have hih := ih false (pre ++ [child]) domRest mid hi aMid
                    (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen; omega)
                    (by omega) hrestDep (by omega) hpreMid hparMid (by simpa using hdomMid)
                  have hstep :
                      ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) inTextRun
                        (.element tag attrs kids :: rest)).run a).2 =
                      ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (pre ++ [child]).length) false
                        rest).run aMid).2 := by
                    dsimp only [StateT.run, hydrateDomKidsM, Html.textOf?, bind, StateT.bind, MonadDom.childAt]
                    rw [hpar, huIdx]
                    dsimp only
                    rw [hgetD]
                    change (hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length + 1) false rest aMid).2 = _
                    simp only [List.length_append, List.length_singleton]
                    rw [← huIdxNext]
                  rcases hih with ⟨hydRest, hnextR, hboundR, hparR, hsubR, hfrR, heqR, hclR⟩
                  have hfrChild : ∀ m : Dom.Node,
                      ((lo ≤ m.toNat ∧ m.toNat < mid) ∨ (a.nextId ≤ m.toNat ∧ m.toNat < aMid.nextId)) →
                      ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
                        (UInt32.ofNat (pre ++ [child]).length) false rest).run aMid).2.get m = aMid.get m :=
                    fun m hm => hfrR m (by intro heq; rw [heq] at hm; rcases hm with h1 | h2 <;> omega)
                      (hm.elim (fun h1 => .inl h1.2) (fun h2 => .inr (Nat.le_trans hhiNext h2.1)))
                      (hm.elim (fun h1 => by omega) (fun h2 => h2.2))
                  have haOutChild := SubtreeInSet_frame (a := aMid)
                      (a' := ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
                        (UInt32.ofNat (pre ++ [child]).length) false rest).run aMid).2)
                      (S := fun k => (lo ≤ k ∧ k < mid) ∨ (a.nextId ≤ k ∧ k < aMid.nextId))
                      (n := child) hfrChild hchildSubMid
                  rw [hstep]
                  refine ⟨child :: hydRest, Nat.le_trans haMidNext hnextR,
                    by simp only [htmlListNodeCount]; omega,
                    by simpa [List.append_assoc] using hparR, ?_, ?_, ?_, ?_⟩
                  · intro z hz
                    rcases List.mem_cons.1 hz with hzEq | htail
                    · rw [hzEq]
                      exact SubtreeInSet_mono (fun k hkS => by
                        rcases hkS with ⟨h1, h2⟩ | ⟨h1, h2⟩
                        · exact .inl ⟨h1, Nat.le_trans h2 hmidHi⟩
                        · exact .inr ⟨h1, Nat.le_trans h2 hnextR⟩) haOutChild.1
                    · exact SubtreeInSet_mono (fun k hkS => by
                        rcases hkS with ⟨h1, h2⟩ | ⟨h1, h2⟩
                        · exact .inl ⟨Nat.le_trans hloMid h1, h2⟩
                        · exact .inr ⟨Nat.le_trans haMidNext h1, h2⟩) (hsubR z htail)
                  · intro m hmPar hmOut hmLt
                    rw [hfrR m hmPar (hmOut.elim (fun h1 => .inl (by omega)) .inr) (by omega),
                        hframeMid m (hmOut.elim .inl (fun h2 => .inr (Nat.le_trans hmidHi h2))) hmLt]
                  · simp only [List.map_cons, specDomList, DomTreeListAssocEquiv]
                    rw [haOutChild.2]
                    exact ⟨hequivChild, heqR⟩
                  · intro hc
                    simp only [Html.DomCleanList, Bool.and_eq_true] at hc
                    refine ⟨fun k => (lo ≤ k ∧ k < mid) ∨ (a.nextId ≤ k ∧ k < aMid.nextId),
                      fun k => (mid ≤ k ∧ k < hi) ∨ (aMid.nextId ≤ k ∧ k < ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
                        (UInt32.ofNat (pre ++ [child]).length) false rest).run aMid).2.nextId),
                      fun _ hk => hk.elim (fun h => .inl ⟨h.1, Nat.le_trans h.2 hmidHi⟩) (fun h => .inr ⟨h.1, Nat.le_trans h.2 hnextR⟩),
                      fun _ hk => hk.elim (fun h => .inl ⟨Nat.le_trans hloMid h.1, h.2⟩) (fun h => .inr ⟨Nat.le_trans haMidNext h.1, h.2⟩),
                      fun _ hk1 hk2 => by rcases hk1 with h1 | h1 <;> rcases hk2 with h2 | h2 <;> omega,
                      CleanDomSubtree_frame hfrChild (hchildClMid hc.1), hclR hc.2⟩

private theorem hydrateDomM_spec_strong (f : Nat) : @DomHydrateSpecAt msg f := by
  induction f using Nat.strongRecOn with
  | ind f ihDom =>
      intro ns h root a lo hi hbound hdep hdom
      cases h with
      | text s =>
          rcases hdom with ⟨hlo, hhi, hnext, hget⟩
          simp only [hydrateDomM, StateT.run, pure, StateT.pure]
          refine ⟨Nat.le_refl _, by simp [htmlNodeCount], ?_, ?_, ?_, ?_⟩
          · exact ⟨.inl ⟨hlo, hhi⟩, by simp [hget]⟩
          · intro _ _ _; exact trivial
          · simp [readDomTree, hget, specDom, DomTreeAssocEquiv]
          · intro _; exact ⟨.inl ⟨hlo, hhi⟩, hget⟩
      | element tag attrs cs =>
          rcases hdom with ⟨hlo, hhi, hnext, st, prev, domCs, hget, hm, hns, hownT, hownF⟩
          have hattrs := applyAttrsM_existing_element a root
            (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
            { st with clicks := [], inputs := [] } prev domCs attrs hm hns
          rcases hattrs with ⟨st', ha2Get, ha2Eqv, hm'⟩
          let a2 := (applyAttrsM (m := StateM (DomArena msg)) root attrs
            (a.set root (.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
              { st with clicks := [], inputs := [] } prev domCs))).2
          have ha2Next : a2.nextId = a.nextId := applyAttrsM_nextId a root attrs
            (.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
              { st with clicks := [], inputs := [] } prev domCs)
          have ha2Outside : ∀ m : Dom.Node, m ≠ root → a2.get m = a.get m := by
            intro m hne
            exact applyAttrsM_get_ne a root attrs _ m hne
          have hpreBind :
              ((hydrateDomM (m := StateM (DomArena msg)) (.element tag attrs cs) root).run a).2 =
              if !ownsChildren attrs then
                ((hydrateDomKidsM (m := StateM (DomArena msg)) root 0 false cs).run a2).2
              else a2 := by
            dsimp only [hydrateDomM, StateT.run, bind, StateT.bind, pure, StateT.pure]
            have hclearMod : a.modifyElemState root (fun st : SpecElemState msg => { st with clicks := [], inputs := [] }) =
                a.set root (.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
                  { st with clicks := [], inputs := [] } prev domCs) := by
              simp [DomArena.modifyElemState, DomArena.modify, hget]
            rw [hclearMod]
            cases hresA : applyAttrsM (m := StateM (DomArena msg)) root attrs
                (a.set root (.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
                  { st with clicks := [], inputs := [] } prev domCs)) with
            | mk u s' =>
                have hsEq : s' = a2 := by dsimp [a2]; rw [hresA]
                subst hsEq
                cases ownsChildren attrs <;> rfl
          cases hown : ownsChildren attrs with
          | true =>
              have hrunOut : ((hydrateDomM (m := StateM (DomArena msg)) (.element tag attrs cs) root).run a).2 = a2 := by
                rw [hpreBind, hown]; rfl
              rw [hrunOut]
              have hdomNil : domCs = [] := hownT hown
              subst hdomNil
              refine ⟨by rw [ha2Next]; exact Nat.le_refl _, by rw [ha2Next]; simp [htmlNodeCount], ?_, ?_, ?_, ?_⟩
              · dsimp only [SubtreeInSet]
                refine ⟨.inl ⟨hlo, hhi⟩, ?_⟩
                rw [ha2Get]
                intro c hc; nomatch hc
              · intro m hmOut hmLt
                have hne : m ≠ root := by intro heq; rw [heq] at hmOut; omega
                exact ha2Outside m hne
              · dsimp only [readDomTree, specDom]
                rw [ha2Get, hown]
                exact ⟨rfl, rfl, ha2Eqv, trivial⟩
              · intro hc; simp [Html.DomClean, hown] at hc
          | false =>
              have hrunOut : ((hydrateDomM (m := StateM (DomArena msg)) (.element tag attrs cs) root).run a).2 =
                  ((hydrateDomKidsM (m := StateM (DomArena msg)) root 0 false cs).run a2).2 := by
                rw [hpreBind, hown]; rfl
              rcases hownF hown with ⟨mid, hmidGt, hk⟩
              rcases HydratableDomList_bounds f (Dom.childNsOf ns tag) (coalesceTextRun cs) a mid hi domCs hk with ⟨hmidHi, hhiNext⟩
              have hkFrame : HydratableDomList f (Dom.childNsOf ns tag) (coalesceTextRun cs) a2 mid hi domCs :=
                HydratableDomList_frame f (Dom.childNsOf ns tag) (coalesceTextRun cs) a a2 mid hi domCs
                  (by rw [ha2Next]; exact Nat.le_refl _) (fun m hm1 _ => ha2Outside m (by intro heq; rw [heq] at hm1; omega)) hk
              have hcsLenLt : ([] : List Dom.Node).length + cs.length < UInt32.size := by
                simp only [List.length_nil, Nat.zero_add]
                have := list_length_le_htmlListNodeCount cs
                simp only [htmlNodeCount] at hbound
                omega
              have ha2Bound : a2.nextId + htmlListNodeCount cs < UInt32.size := by
                simp only [htmlNodeCount] at hbound; omega
              have hcsDep : htmlListDepth cs ≤ f := by
                simp only [htmlDepth] at hdep; omega
              have hkidsRun := hydrateDomKidsM_spec_step f ihDom (Dom.childNsOf ns tag) root
                (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag st'
                ((normalizeAttrs attrs).filterMap managedAttrName)
                cs false [] domCs mid hi a2 hcsLenLt ha2Bound hcsDep hmidGt
                (fun _ hm => nomatch hm) ha2Get hkFrame
              simp only [List.length_nil] at hkidsRun
              change ∃ hydratedCs, _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hkidsRun
              have hzeroEq : (UInt32.ofNat 0 : UInt32) = 0 := rfl
              rw [hzeroEq] at hkidsRun
              rcases hkidsRun with ⟨hydratedCs, hnextLe, hnextBound, hgetOut, hsubSet, hframeKids, hequivKids, hcleanKids⟩
              rw [hrunOut]
              refine ⟨by omega, by simp only [htmlNodeCount]; omega, ?_, ?_, ?_, ?_⟩
              · dsimp only [SubtreeInSet]
                refine ⟨.inl ⟨hlo, hhi⟩, ?_⟩
                rw [hgetOut]
                intro c hc
                exact SubtreeInSet_mono (fun k hkS => by
                  rcases hkS with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · exact .inl ⟨by omega, h2⟩
                  · exact .inr ⟨by omega, h2⟩) (hsubSet c hc)
              · intro m hmOut hmLt
                have hne : m ≠ root := by intro heq; rw [heq] at hmOut; omega
                rw [hframeKids m hne (hmOut.elim (fun h1 => .inl (by omega)) .inr) (by omega),
                    ha2Outside m hne]
              · dsimp only [readDomTree, specDom]
                rw [hgetOut, hown]
                exact ⟨rfl, rfl, ha2Eqv, hequivKids⟩
              · intro hc
                simp only [Html.DomClean, hown, Bool.not_false, Bool.true_and, Bool.and_eq_true] at hc
                refine ⟨.inl ⟨hlo, hhi⟩, hown, hc.1, st', (normalizeAttrs attrs).filterMap managedAttrName, hydratedCs,
                  hgetOut, ⟨hm', fun k hk => (ha2Eqv.1 k).trans ((ElemClean_evalSpecAttrs hc.1).2 k hk)⟩,
                  ha2Eqv, fun nm hnm => List.contains_iff_mem.2 hnm,
                  CleanDomChildren_mono (fun k hkS => ?_) (hcleanKids hc.2)⟩
                rcases hkS with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact ⟨.inl ⟨by omega, h2⟩, by omega⟩
                · exact ⟨.inr ⟨by rw [ha2Next] at h1; exact h1, h2⟩, by rw [ha2Next] at h1; omega⟩

/-- Imperative HTML5 hydration simulation for `hydrateDomM`:
    given an SSR-parsed `HydratableDom` tree whose text children were coalesced by the HTML5 parser
    (`coalesceTextRun`), `hydrateDomM` preserves outside nodes and makes `readDomTree (f + 1) aOut root`
    match `specDom ns h` via `DomTreeAssocEquiv`, producing `CleanDomSubtree` whenever `h.DomClean`. -/
theorem hydrateDomM_spec {msg : Type} (ns : String)
    (f : Nat) (h : Html msg) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat)
    (hbound : a.nextId + htmlNodeCount h < UInt32.size)
    (hdep : htmlDepth h ≤ f + 1)
    (hdom : HydratableDom (f + 1) ns h a lo hi root) :
    let aOut := ((hydrateDomM (m := StateM (DomArena msg)) h root).run a).2
    a.nextId ≤ aOut.nextId ∧
    aOut.nextId ≤ a.nextId + htmlNodeCount h ∧
    SubtreeInSet (f + 1) aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) root ∧
    (∀ m : Dom.Node, (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns h) ∧
    (h.DomClean = true →
      CleanDomSubtree (f + 1) ns h aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) root) :=
  hydrateDomM_spec_strong f ns h root a lo hi hbound hdep hdom

/-- Imperative child-list HTML5 hydration simulation for `hydrateDomKidsM`:
    interpolates `hydrateTextSlotM` and recursive `hydrateDomM` calls across `target`, keeping child
    subtrees disjoint and producing `DomTreeListAssocEquiv` against `specDomList` and `CleanDomChildren`. -/
theorem hydrateDomKidsM_spec {msg : Type} (childNs : String) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (f : Nat) (target : List (Html msg)) (inTextRun : Bool)
    (pre domCs : List Dom.Node) (lo hi : Nat) (a : DomArena msg)
    (hlen : pre.length + target.length < UInt32.size)
    (hbound : a.nextId + htmlListNodeCount target < UInt32.size)
    (hdep : htmlListDepth target ≤ f)
    (hparLo : parent.toNat < lo)
    (hpreSub : ∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet f a Sx x)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ domCs))
    (hdom : HydratableDomList f childNs (if inTextRun then dropCurrentTextRun target else coalesceTextRun target) a lo hi domCs) :
    let aOut := ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) inTextRun target).run a).2
    ∃ (hydratedCs : List Dom.Node),
      a.nextId ≤ aOut.nextId ∧
      aOut.nextId ≤ a.nextId + htmlListNodeCount target ∧
      aOut.get parent = .element pns ptag pst pmg (pre ++ hydratedCs) ∧
      (∀ c ∈ hydratedCs, SubtreeInSet f aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) c) ∧
      (∀ m : Dom.Node, m ≠ parent → (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
      DomTreeListAssocEquiv (hydratedCs.map (readDomTree f aOut)) (specDomList childNs target) ∧
      (Html.DomCleanList target = true →
        CleanDomChildren f childNs target aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) hydratedCs) :=
  hydrateDomKidsM_spec_step f (fun f' _ => hydrateDomM_spec_strong f') childNs parent pns ptag pst pmg
    target inTextRun pre domCs lo hi a hlen hbound hdep hparLo hpreSub hpar hdom

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
    (st : Dom.Node → ArenaEntry msg) (s₁ s₂ : List (String × String))
    (n : Dom.Node) (f : ArenaEntry msg → ArenaEntry msg) :
    DomArena.modify ⟨nxt, st, s₁⟩ n f = { DomArena.modify ⟨nxt, st, s₂⟩ n f with signals := s₁ } := by
  simp only [DomArena.modify, DomArena.get, DomArena.set]

private theorem hydrateTextSlotM_withSignals {msg : Type} (sigs : List (String × String))
    (parent : Dom.Node) (index : UInt32) (inRun : Bool) (s : String) (more : Unit → Bool) (a : DomArena msg) :
    hydrateTextSlotM (m := StateM (DomArena msg)) parent index inRun s more { a with signals := sigs } =
      ((hydrateTextSlotM (m := StateM (DomArena msg)) parent index inRun s more a).1,
       { (hydrateTextSlotM (m := StateM (DomArena msg)) parent index inRun s more a).2 with signals := sigs }) := by
  dsimp only [hydrateTextSlotM]
  split
  · simp only [bind, StateT.bind, pure, StateT.pure, DomArena.alloc, DomArena.modifyChildren]
    refine Prod.ext rfl ?_; dsimp only; apply DomArena.modify_withSignals
  · split
    · simp only [bind, StateT.bind, pure, StateT.pure, DomArena.alloc, DomArena.modifyChildren]
      refine Prod.ext rfl ?_; dsimp only; apply DomArena.modify_withSignals
    · simp only [bind, StateT.bind, pure]
      have hg : DomArena.get { a with signals := sigs } parent = DomArena.get a parent := rfl
      rw [hg]
      cases more ()
      · rfl
      · simp only [↓reduceIte, bind, StateT.bind, pure, StateT.pure]
        refine Prod.ext rfl ?_; dsimp only; apply DomArena.modify_withSignals

mutual
  theorem hydrateDomM_withSignals {msg : Type} (sigs : List (String × String)) :
      ∀ (h : Html msg) (node : Dom.Node) (a : DomArena msg),
        (hydrateDomM (m := StateM (DomArena msg)) h node { a with signals := sigs }).2 =
          { (hydrateDomM (m := StateM (DomArena msg)) h node a).2 with signals := sigs }
    | .text _, _, _ => rfl
    | .element _ attrs cs, node, a => by
        dsimp only [hydrateDomM, bind, StateT.bind, pure, StateT.pure, DomArena.modifyElemState,
          DomArena.modify, DomArena.get, DomArena.set]
        have hstep : ∀ (nxt : Nat) (st : Dom.Node → ArenaEntry msg),
            (match applyAttrsM (m := StateM (DomArena msg)) node attrs ⟨nxt, st, sigs⟩ with
            | (_, s) => (if (!ownsChildren attrs) = true then hydrateDomKidsM (m := StateM (DomArena msg)) node 0 false cs else StateT.pure PUnit.unit) s).snd =
            { (match applyAttrsM (m := StateM (DomArena msg)) node attrs ⟨nxt, st, a.signals⟩ with
              | (_, s) => (if (!ownsChildren attrs) = true then hydrateDomKidsM (m := StateM (DomArena msg)) node 0 false cs else StateT.pure PUnit.unit) s).snd with signals := sigs } := by
          intro nxt st
          have ha := applyAttrsM_withSignals sigs node attrs ⟨nxt, st, a.signals⟩
          dsimp only [StateT.run] at ha
          cases ha1 : applyAttrsM (m := StateM (DomArena msg)) node attrs ⟨nxt, st, sigs⟩ with
          | mk _ s1 =>
              cases ha2 : applyAttrsM (m := StateM (DomArena msg)) node attrs ⟨nxt, st, a.signals⟩ with
              | mk _ s2 =>
                  rw [ha1, ha2] at ha; dsimp only at ha; rw [ha]
                  cases ownsChildren attrs
                  · exact hydrateDomKidsM_withSignals sigs node 0 false cs s2
                  · rfl
        apply hstep

  theorem hydrateDomKidsM_withSignals {msg : Type} (sigs : List (String × String))
      (node : Dom.Node) : ∀ (i : UInt32) (inRun : Bool) (cs : List (Html msg)) (a : DomArena msg),
        (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs { a with signals := sigs }).2 =
          { (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs a).2 with signals := sigs }
    | _, _, [], _ => rfl
    | i, inRun, c :: rest, a => by
        dsimp only [hydrateDomKidsM, bind, StateT.bind, pure, StateT.pure]
        cases hc : c.textOf? with
        | none =>
          dsimp only [bind, StateT.bind, pure, StateT.pure]
          have hg : ({ nextId := a.nextId, store := a.store, signals := sigs } : DomArena msg).get node = a.get node := rfl
          rw [hg]
          have hchild : ∀ cn : Dom.Node,
              (match hydrateDomM (m := StateM (DomArena msg)) c cn { a with signals := sigs } with
              | (_, s) => hydrateDomKidsM (m := StateM (DomArena msg)) node (i + 1) false rest s).snd =
              { (match hydrateDomM (m := StateM (DomArena msg)) c cn a with
                | (_, s) => hydrateDomKidsM (m := StateM (DomArena msg)) node (i + 1) false rest s).snd with signals := sigs } := by
            intro cn
            have hd := hydrateDomM_withSignals sigs c cn a
            cases hd1 : hydrateDomM (m := StateM (DomArena msg)) c cn { a with signals := sigs } with
            | mk _ a1 => cases hd2 : hydrateDomM (m := StateM (DomArena msg)) c cn a with
              | mk _ a2 => rw [hd1, hd2] at hd; dsimp only at hd; rw [hd]; exact hydrateDomKidsM_withSignals sigs node (i + 1) false rest a2
          cases a.get node <;> dsimp only <;> exact hchild _
        | some str =>
          dsimp only [bind, StateT.bind, pure, StateT.pure]
          have hs := hydrateTextSlotM_withSignals sigs node i inRun str (fun () => hasMoreText rest) a
          cases hs1 : hydrateTextSlotM (m := StateM (DomArena msg)) node i inRun str (fun () => hasMoreText rest) { a with signals := sigs } with
          | mk r1 a1 =>
              cases hs2 : hydrateTextSlotM (m := StateM (DomArena msg)) node i inRun str (fun () => hasMoreText rest) a with
              | mk r2 a2 =>
                  rw [hs1, hs2] at hs; dsimp only at hs
                  rcases Prod.mk.inj hs with ⟨hreq, haeq⟩
                  rw [hreq, haeq]
                  exact hydrateDomKidsM_withSignals sigs node (i + 1) r2.2 rest a2
end

theorem hydrateDomM_sameDom {msg : Type} (h : Html msg) (node : Dom.Node) {a₁ a₂ : DomArena msg}
    (hs : a₁.SameDom a₂) :
    (hydrateDomM (m := StateM (DomArena msg)) h node a₁).2.SameDom
      (hydrateDomM (m := StateM (DomArena msg)) h node a₂).2 := by
  have heq : a₁ = { a₂ with signals := a₁.signals } := DomArena.ext hs.1 hs.2 rfl
  rw [heq, hydrateDomM_withSignals]; exact ⟨rfl, rfl⟩

theorem hydrateDomKidsM_sameDom {msg : Type} (node : Dom.Node) (i : UInt32) (inRun : Bool)
    (cs : List (Html msg)) {a₁ a₂ : DomArena msg} (hs : a₁.SameDom a₂) :
    (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs a₁).2.SameDom
      (hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun cs a₂).2 := by
  have heq : a₁ = { a₂ with signals := a₁.signals } := DomArena.ext hs.1 hs.2 rfl
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

mutual
  theorem hydrateViewM_eq_hydrateDomM {σ msg : Type} :
      ∀ {v : View σ msg}, View.DomClean v → ∀ (s : σ) (node : Dom.Node) (a : DomArena msg),
        ((hydrateViewM (m := StateM (DomArena msg)) v s node).run a).2.SameDom
          ((hydrateDomM (m := StateM (DomArena msg)) (View.render v s) node).run a).2
    | .text _, _, _, _, a | .dyn _, _, _, _, a => DomArena.SameDom.refl a
    | .static (.text _), _, _, _, _ | .static (.element ..), _, _, _, _ => by
        dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
        cases hydrateDomM (m := StateM (DomArena msg)) _ _ _; exact DomArena.SameDom.refl _
    | .dynNode get, _, s, node, a => by
        dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
        cases hydrateDomM (m := StateM (DomArena msg)) (get s) node a; exact DomArena.SameDom.refl _
    | .memo sm, _, s, node, a => by
        dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure]
        cases hydrateDomM (m := StateM (DomArena msg)) (sm.eval s) node a; exact DomArena.SameDom.refl _
    | .ifElse c y n, ⟨hy, hn⟩, s, node, a => by
        cases hcs : c s
        · have h := hydrateViewM_eq_hydrateDomM hn s node a
          dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at h ⊢
          rw [hcs]
          cases hydrateViewM (m := StateM (DomArena msg)) n s node a; exact h
        · have h := hydrateViewM_eq_hydrateDomM hy s node a
          dsimp only [hydrateViewM, View.render, StateT.run, bind, StateT.bind, pure, StateT.pure] at h ⊢
          rw [hcs]
          cases hydrateViewM (m := StateM (DomArena msg)) y s node a; exact h
    | .element tag attrs kids, ⟨ha, hks⟩, s, node, a => by
        dsimp only [hydrateViewM, View.render, hydrateDomM, StateT.run, bind, StateT.bind, pure, StateT.pure]
        rw [ha.1 s, Bool.not_false, if_pos rfl]
        cases applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s))
            (a.modifyElemState node fun st => { st with clicks := [], inputs := [] }) with
        | mk _ a1 =>
            have h := hydrateViewKidsM_eq_hydrateDomKidsM hks node s 0 false a1
            dsimp only [StateT.run] at h
            cases hydrateViewKidsM (m := StateM (DomArena msg)) node s 0 false kids a1; exact h
    | .keyedList tag attrs keys marks rowSig rowsHtml, ⟨ha, hrows⟩, s, node, a => by
        dsimp only [hydrateViewM, View.render, hydrateDomM, StateT.run, bind, StateT.bind, pure, StateT.pure]
        rw [ha.1 s, Bool.not_false, if_pos rfl]
        cases applyAttrsM (m := StateM (DomArena msg)) node (attrs.map (VAttr.eval s))
            (a.modifyElemState node fun st => { st with clicks := [], inputs := [] }) with
        | mk _ a1 =>
            dsimp only
            cases hseed : seedRowsM (m := StateM (DomArena msg)) s!"§{node}§" (rowSig s) (marks s) #[] #[] a1 with
            | mk _ a2 =>
                dsimp only
                have hsd : a2.SameDom a1 := by
                  have h := seedRowsM_sameDom s!"§{node}§" (rowSig s) (marks s) #[] #[] a1
                  dsimp only [StateT.run] at h; rw [hseed] at h; exact h
                rw [Html.map_prefixSignals_of_DomCleanList _ (hrows.2.1 s)]
                have hlist := hydrateListRowsM_eq_hydrateDomKidsM node 0 (rowsHtml s) (hrows.2.2.1 s) a2
                dsimp only [StateT.run] at hlist
                cases hl : hydrateListRowsM (m := StateM (DomArena msg)) node 0 (rowsHtml s) a2 with
                | mk _ a3 =>
                    rw [hl] at hlist; dsimp only at hlist ⊢; rw [hlist]
                    exact hydrateDomKidsM_sameDom node 0 false (rowsHtml s) hsd

  theorem hydrateViewKidsM_eq_hydrateDomKidsM {σ msg : Type} :
      ∀ {ks : List (View σ msg)}, View.DomCleanEach ks → ∀ (node : Dom.Node) (s : σ) (i : UInt32) (inRun : Bool)
        (a : DomArena msg),
        ((hydrateViewKidsM (m := StateM (DomArena msg)) node s i inRun ks).run a).2.SameDom
          ((hydrateDomKidsM (m := StateM (DomArena msg)) node i inRun (View.renderEach ks s)).run a).2
    | [], _, _, _, _, _, a => DomArena.SameDom.refl a
    | k :: rest, ⟨hk, hrest⟩, node, s, i, inRun, a => by
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
                    have hkEq := hydrateViewKidsM_eq_hydrateDomKidsM hrest node s (i + 1) slot.2 a1
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
            have heq := hydrateViewM_eq_hydrateDomM hk s cn a
            dsimp only [StateT.run] at heq
            cases hvm : hydrateViewM (m := StateM (DomArena msg)) k s cn a with
            | mk kst a2 =>
                cases hdm : hydrateDomM (m := StateM (DomArena msg)) (k.render s) cn a with
                | mk _ ad =>
                    rw [hvm, hdm] at heq; dsimp only at heq ⊢
                    have hkEq := hydrateViewKidsM_eq_hydrateDomKidsM hrest node s (i + 1) false a2
                    dsimp only [StateT.run] at hkEq
                    cases hkRun : hydrateViewKidsM (m := StateM (DomArena msg)) node s (i + 1) false rest a2 with
                    | mk _ a3 =>
                        rw [hkRun] at hkEq; exact hkEq.trans (hydrateDomKidsM_sameDom node (i + 1) false (View.renderEach rest s) heq)
end

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
            have hdomMid : HydratableDomList f childNs
                (if inRun' then dropCurrentTextRun (View.renderEach rest s) else coalesceTextRun (View.renderEach rest s))
                aMid lo hi domCs :=
              HydratableDomList_frame f childNs _ a aMid lo hi domCs (by rw [haMidNext]; omega)
                (fun m hm1 _ => hframeMid m (by intro heq; rw [heq] at hm1; omega)
                  (by intro heq; have : m.toNat = a.nextId := heq ▸ uint32_toNat_ofNat_lt a.nextId (by omega); omega))
                hdom'
            have hpreMid : ∀ x ∈ pre ++ [kn], ∃ Sx,
                (∀ k', Sx k' → (parent.toNat < k' ∧ k' < lo) ∨ (hi ≤ k' ∧ k' < aMid.nextId)) ∧ SubtreeInSet f aMid Sx x := by
              intro x hx
              rcases List.mem_append.1 hx with hOld | hNew
              · rcases hpreSub x hOld with ⟨Sx, hSx, hsub⟩
                refine ⟨Sx, fun k' hk' => (hSx k' hk').elim .inl (fun h2 => .inr ⟨h2.1, Nat.lt_of_lt_of_le h2.2 (by rw [haMidNext]; omega)⟩), ?_⟩
                exact (SubtreeInSet_frame (fun m hm => hframeMid m
                  (by intro heq; rw [heq] at hm; rcases hSx parent.toNat hm with h1 | h2 <;> omega)
                  (by intro heq; have : m.toNat = a.nextId := heq ▸ uint32_toNat_ofNat_lt a.nextId (by omega)
                      rcases hSx m.toNat hm with h1 | h2 <;> omega)) hsub).1
              · simp only [List.mem_singleton] at hNew; rw [hNew]
                refine ⟨fun k' => k' = a.nextId, fun k' hk' => .inr ⟨by omega, by rw [haMidNext]; omega⟩, ?_⟩
                cases f with | zero => omega | succ _ => exact ⟨uint32_toNat_ofNat_lt a.nextId (by omega), by simp [kn, hgetNew]⟩
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
                        have hdomMid : HydratableDomList (f' + 1) childNs (dropCurrentTextRun (View.renderEach rest s)) aMid mid hi domRest :=
                          HydratableDomList_frame (f' + 1) childNs (dropCurrentTextRun (View.renderEach rest s)) a aMid mid hi domRest
                            (by rw [haMidNext]; exact Nat.le_refl _)
                            (fun m hm1 _ => hframeMid m (by intro heq; rw [heq] at hm1; omega)) hrestDom
                        have hpreMid : ∀ x ∈ pre ++ [tn], ∃ Sx,
                            (∀ k', Sx k' → (parent.toNat < k' ∧ k' < mid) ∨ (hi ≤ k' ∧ k' < aMid.nextId)) ∧
                            SubtreeInSet (f' + 1) aMid Sx x := by
                          intro x hx
                          rcases List.mem_append.1 hx with hOld | hNew
                          · rcases hpreSub x hOld with ⟨Sx, hSx, hsub⟩
                            refine ⟨Sx, fun k' hk' => (hSx k' hk').elim
                              (fun h1 => .inl ⟨h1.1, Nat.lt_of_lt_of_le h1.2 hloMid⟩)
                              (fun h2 => .inr ⟨h2.1, by rw [haMidNext]; exact h2.2⟩), ?_⟩
                            exact (SubtreeInSet_frame (fun m hm => hframeMid m (by
                              intro heq; rw [heq] at hm; rcases hSx tn.toNat hm with h1 | h2 <;> omega)) hsub).1
                          · simp only [List.mem_singleton] at hNew; rw [hNew]
                            exact ⟨fun k' => k' = tn.toNat, fun k' hk' => .inl ⟨by omega, by omega⟩, rfl, by simp [hgetTnMid]⟩
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
                      have hdomMid : HydratableDomList (f' + 1) childNs (coalesceTextRun (View.renderEach rest s)) aMid mid hi domRest :=
                        HydratableDomList_frame (f' + 1) childNs (coalesceTextRun (View.renderEach rest s)) a aMid mid hi domRest
                          haMidNext (fun m hm1 _ => hframeMid m (.inr hm1) (by omega)) hrestDom
                      have hpreMid : ∀ x ∈ pre ++ [child], ∃ Sx,
                          (∀ k', Sx k' → (parent.toNat < k' ∧ k' < mid) ∨ (hi ≤ k' ∧ k' < aMid.nextId)) ∧
                          SubtreeInSet (f' + 1) aMid Sx x := by
                        intro x hx
                        rcases List.mem_append.1 hx with hOld | hNew
                        · rcases hpreSub x hOld with ⟨Sx, hSx, hsub⟩
                          refine ⟨Sx, fun k' hk' => (hSx k' hk').elim
                            (fun h1 => .inl ⟨h1.1, Nat.lt_of_lt_of_le h1.2 hloMid⟩)
                            (fun h2 => .inr ⟨h2.1, Nat.lt_of_lt_of_le h2.2 haMidNext⟩), ?_⟩
                          exact (SubtreeInSet_frame (fun m hm => hframeMid m
                            (by rcases hSx m.toNat hm with h1 | h2
                                · exact .inl h1.2
                                · exact .inr (Nat.le_trans hmidHi h2.1))
                            (by rcases hSx m.toNat hm with h1 | h2
                                · omega
                                · exact h2.2)) hsub).1
                        · simp only [List.mem_singleton] at hNew; rw [hNew]
                          have hdomS := (hydrateDomM_spec childNs f' (View.render k s) child a lo mid (by omega) hcDep hchildDom).2.2.1
                          have haMidEqDom := hydrateViewM_eq_hydrateDomM hkCl s child a
                          dsimp only [StateT.run] at haMidEqDom hdomS
                          cases hdmMid : hydrateDomM (m := StateM (DomArena msg)) (View.render k s) child a with
                          | mk _ aDomMid =>
                              rw [hvm, hdmMid] at haMidEqDom; dsimp only at haMidEqDom
                              rw [hdmMid] at hdomS; dsimp only at hdomS
                              have hdomS' := (SubtreeInSet_frame (fun m _ => haMidEqDom.get_eq m) hdomS).1
                              rw [← haMidEqDom.1] at hdomS'
                              refine ⟨fun k' => (lo ≤ k' ∧ k' < mid) ∨ (a.nextId ≤ k' ∧ k' < aMid.nextId), fun k' hk' => ?_, hdomS'⟩
                              rcases hk' with ⟨h1, h2⟩ | ⟨h1, h2⟩
                              · exact .inl ⟨by omega, h2⟩
                              · exact .inr ⟨by omega, h2⟩
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
  | .keyedList tag attrs keys marks rowSig rowsHtml, s, root, a, lo, hi, ⟨haCl, hrowsCl⟩, hbound, hdep, hdom => by
      have hdomSpec := hydrateDomM_spec ns f (View.render (.keyedList tag attrs keys marks rowSig rowsHtml) s) root a lo hi hbound hdep hdom
      have hviewEq := hydrateViewM_eq_hydrateDomM (v := .keyedList tag attrs keys marks rowSig rowsHtml) ⟨haCl, hrowsCl⟩ s root a
      dsimp only [StateT.run] at hdomSpec hviewEq
      dsimp only [hydrateViewM, StateT.run, bind, StateT.bind, pure, StateT.pure] at hviewEq ⊢
      cases ha1 : applyAttrsM (m := StateM (DomArena msg)) root (attrs.map (VAttr.eval s))
          (a.modifyElemState root fun st => { st with clicks := [], inputs := [] }) with
      | mk _ a1 =>
          rw [ha1] at hviewEq; dsimp only at hviewEq ⊢
          cases hs1 : seedRowsM (m := StateM (DomArena msg)) s!"§{root}§" (rowSig s) (marks s) #[] #[] a1 with
          | mk perRow a2 =>
              rw [hs1] at hviewEq
              rw [Html.map_prefixSignals_of_DomCleanList _ (hrowsCl.2.1 s)] at hviewEq ⊢
              dsimp only at hviewEq ⊢
              cases hl1 : hydrateListRowsM (m := StateM (DomArena msg)) root 0 (rowsHtml s) a2 with
              | mk _ aOut =>
                  rw [hl1] at hviewEq; dsimp only at hviewEq ⊢
                  cases hdomRun : hydrateDomM (m := StateM (DomArena msg))
                      (View.render (.keyedList tag attrs keys marks rowSig rowsHtml) s) root a with
                  | mk _ aDom =>
                      rw [hdomRun] at hviewEq hdomSpec; dsimp only at hviewEq hdomSpec
                      rcases hdomSpec with ⟨h1, h2, _, h4, h5, h6⟩
                      have hcleanDom := h6 (View.DomClean_render (v := .keyedList tag attrs keys marks rowSig rowsHtml) ⟨haCl, hrowsCl⟩ s)
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

theorem App.ssr_hydrate_patch_equiv {Model Msg : Type} (app : App Model Msg)
    (m m' : Model) (msg : Msg)
    (hre : app.rehydrate (app.dehydrate m) = some m')
    (hclean : View.DomClean app.template)
    (f : Nat) (parent root : Dom.Node) (ptag : String) (pst : SpecElemState Msg) (pmg : List String)
    (lo hi : Nat) (a : DomArena Msg)
    (hpar : a.get parent = .element "" ptag pst pmg [root])
    (hparLo : parent.toNat < lo)
    (hdom : HydratableDom (f + 1) "" (app.view m) a lo hi root)
    (hbound : a.nextId + htmlNodeCount (app.view m') < UInt32.size)
    (hdep : htmlDepth (app.view m') ≤ f + 1)
    (hboundNext : a.nextId + htmlNodeCount (app.view m') + htmlNodeCount (app.view (app.update m' msg).1) < UInt32.size)
    (hdepNext : htmlDepth (app.view (app.update m' msg).1) ≤ f + 1) :
    let (vst, aHyd) := (hydrateViewM (m := StateM (DomArena Msg)) app.template m' root).run a
    let mNext := (app.update m' msg).1
    let (vst', aPatch) := (patchViewM (m := StateM (DomArena Msg)) parent 0 app.template mNext vst).run aHyd
    DomTreeAssocEquiv (readDomTree (f + 1) aHyd vst.rootNode) (specDom "" (app.view m)) ∧
    VStateValid (f + 1) "" app.template mNext aPatch
      (fun k => ((lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aHyd.nextId)) ∨ (aHyd.nextId ≤ k ∧ k < aPatch.nextId)) vst' ∧
    DomTreeAssocEquiv (readDomTree (f + 1) aPatch vst'.rootNode) (specDom "" (app.view mNext)) := by
  have hview : app.view m' = app.view m := app.dehydrate_view m m' hre
  have hb := HydratableDom_bounds (f + 1) "" (app.view m) a lo hi root hdom
  have hdom' : HydratableDom (f + 1) "" (View.render app.template m') a lo hi root := by
    change HydratableDom (f + 1) "" (app.view m') a lo hi root; rw [hview]; exact hdom
  have hhyd := hydrateViewM_spec "" f app.template m' root a lo hi hclean hbound hdep hdom'
  dsimp only [StateT.run] at hhyd ⊢
  cases hH : hydrateViewM (m := StateM (DomArena Msg)) app.template m' root a with
  | mk vst aHyd =>
      rw [hH] at hhyd; dsimp only at hhyd ⊢
      rcases hhyd with ⟨hroot, haHydGe, haHydBound, haHydFr, hVstHyd, hEquivHyd⟩
      let S_hyd : Nat → Prop := fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aHyd.nextId)
      have hparHyd : aHyd.get parent = .element "" ptag pst pmg ([] ++ vst.rootNode :: []) := by
        rw [haHydFr parent (.inl hparLo) (by omega), hpar, hroot]; rfl
      have hbNext : aHyd.nextId + htmlNodeCount (View.render app.template (app.update m' msg).1) < UInt32.size := by
        dsimp only [App.view] at hbound hboundNext; omega
      have hrootLt : vst.rootNode.toNat < aHyd.nextId := by
        rcases VStateValid_root_mem hVstHyd with h1 | h2 <;> omega
      have hpatch := patchViewM_spec (f + 1) "" parent "" ptag pst pmg app.template m' (app.update m' msg).1
        [] [] S_hyd aHyd vst rfl hclean (by simp only [List.length_nil]; decide) hbNext
        (by simpa [App.view] using hdepNext) (by omega) (by omega) hparHyd (by simp)
        (fun h => h.elim (fun h1 => by omega) (fun h2 => by omega))
        (fun k hk => hk.elim (fun h1 => by omega) (fun h2 => h2.2))
        (fun r hr => by simp only [List.nil_append, List.mem_singleton] at hr; exact hr ▸ hrootLt)
        hVstHyd
      dsimp only [StateT.run] at hpatch
      have h0 : (UInt32.ofNat ([] : List Dom.Node).length) = 0 := rfl
      rw [h0] at hpatch
      cases hP : patchViewM (m := StateM (DomArena Msg)) parent 0 app.template (app.update m' msg).1 vst aHyd with
      | mk vst' aPatch =>
          rw [hP] at hpatch; dsimp only [App.view] at hpatch ⊢
          rcases hpatch with ⟨_, _, _, _, _, _, hVstP, hEquivP⟩
          dsimp only [App.view] at hview
          exact ⟨by rw [← hview]; simpa [hroot] using hEquivHyd, by simpa [S_hyd] using hVstP, hEquivP⟩

end Qed

