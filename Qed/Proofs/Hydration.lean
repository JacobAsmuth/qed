import Qed.Proofs.DomArena
import Qed.Proofs.ViewPatch
import Qed.Proofs.KeyedReconcile

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

/-- No shadowing attribute invariant matching `applyAttrsM_existing_element`'s requirement. -/
def AttrsNoShadow {msg : Type} (newAttrs : List (Attr msg)) (st : SpecElemState msg) : Prop :=
  (∀ k, ((normalizeAttrs newAttrs).filterMap managedAttrName).contains k = true →
    (∃ x ∈ normalizeAttrs newAttrs, attrWritesKey k x = true) ∨ lookupAssoc k st.attrs = none) ∧
  (((normalizeAttrs newAttrs).filterMap managedAttrName).contains "value" = true →
    (∃ v, .attr "value" v ∈ normalizeAttrs newAttrs) ∨ st.value = "") ∧
  (((normalizeAttrs newAttrs).filterMap managedAttrName).contains "checked" = true →
    (∃ p, .flag "checked" p ∈ normalizeAttrs newAttrs) ∨ st.checked = false)

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
        ElemManaged st prev ∧
        AttrsNoShadow attrs st ∧
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

mutual
  /-- Observational equivalence of `DomTree` modulo `SpecElemState` attribute association list
      lookup order, `value`, and `checked`. Holds unconditionally for all hydrated SSR DOMs. -/
  def DomTreeAssocEquiv {msg : Type} : DomTree msg → DomTree msg → Prop
    | .text s₁, .text s₂ => s₁ = s₂
    | .element ns₁ tag₁ st₁ cs₁, .element ns₂ tag₂ st₂ cs₂ =>
        ns₁ = ns₂ ∧ tag₁ = tag₂ ∧
        (∀ k, lookupAssoc k st₁.attrs = lookupAssoc k st₂.attrs) ∧
        st₁.value = st₂.value ∧ st₁.checked = st₂.checked ∧
        DomTreeListAssocEquiv cs₁ cs₂
    | _, _ => False

  def DomTreeListAssocEquiv {msg : Type} : List (DomTree msg) → List (DomTree msg) → Prop
    | [], [] => True
    | x :: xs, y :: ys => DomTreeAssocEquiv x y ∧ DomTreeListAssocEquiv xs ys
    | _, _ => False
end

private theorem list_length_le_htmlListNodeCount {msg : Type} :
    ∀ (cs : List (Html msg)), cs.length ≤ htmlListNodeCount cs
  | [] => Nat.le_refl 0
  | .text _ :: rest => by
      simp only [List.length_cons, htmlListNodeCount, htmlNodeCount]
      have := list_length_le_htmlListNodeCount rest
      omega
  | .element _ _ _ :: rest => by
      simp only [List.length_cons, htmlListNodeCount, htmlNodeCount]
      have := list_length_le_htmlListNodeCount rest
      omega

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

private theorem applyAttrM_preserves_meta {msg : Type} (a : DomArena msg) (node : Dom.Node) (attr : Attr msg) :
    (applyAttrM (m := StateM (DomArena msg)) node attr a).2.nextId = a.nextId ∧
    ∀ m : Dom.Node, m ≠ node → (applyAttrM (m := StateM (DomArena msg)) node attr a).2.get m = a.get m := by
  cases attr with
  | cls _ | key _ | on _ _ | onValue _ _ | localCell _ _ _ _ _ | signalBind _ | signalAttr _ _ _ =>
      exact ⟨by simp [applyAttrM, pure, StateT.pure, MonadDom.setAttribute, MonadDom.onEvent, MonadDom.onValueEvent,
          MonadDom.mountLocalCell, MonadDom.bindSignal, MonadDom.bindSignalAttr, DomArena.modifyElemState, DomArena.modify],
        fun m hm => by simp [applyAttrM, pure, StateT.pure, MonadDom.setAttribute, MonadDom.onEvent, MonadDom.onValueEvent,
          MonadDom.mountLocalCell, MonadDom.bindSignal, MonadDom.bindSignalAttr, DomArena.modifyElemState, DomArena.modify,
          DomArena.get_set_ne _ _ hm]⟩
  | attr k _ =>
      by_cases hv : k = "value"
      · subst hv
        exact ⟨by simp [applyAttrM, MonadDom.setValue, DomArena.modifyElemState, DomArena.modify],
          fun m hm => by simp [applyAttrM, MonadDom.setValue, DomArena.modifyElemState, DomArena.modify, DomArena.get_set_ne _ _ hm]⟩
      · exact ⟨by simp [applyAttrM, MonadDom.setAttribute, DomArena.modifyElemState, DomArena.modify],
          fun m hm => by simp [applyAttrM, MonadDom.setAttribute, DomArena.modifyElemState, DomArena.modify, DomArena.get_set_ne _ _ hm]⟩
  | flag k p =>
      by_cases hc : k = "checked"
      · subst hc
        exact ⟨by simp [applyAttrM, MonadDom.setChecked, DomArena.modifyElemState, DomArena.modify],
          fun m hm => by simp [applyAttrM, MonadDom.setChecked, DomArena.modifyElemState, DomArena.modify, DomArena.get_set_ne _ _ hm]⟩
      · cases p <;>
        exact ⟨by simp [applyAttrM, MonadDom.removeAttribute, MonadDom.setAttribute, DomArena.modifyElemState, DomArena.modify],
          fun m hm => by simp [applyAttrM, MonadDom.removeAttribute, MonadDom.setAttribute, DomArena.modifyElemState, DomArena.modify, DomArena.get_set_ne _ _ hm]⟩

private theorem applyAttrListM_preserves_meta {msg : Type} (node : Dom.Node) :
    ∀ (xs : List (Attr msg)) (a : DomArena msg),
      (applyAttrListM (m := StateM (DomArena msg)) node xs a).2.nextId = a.nextId ∧
      ∀ m : Dom.Node, m ≠ node → (applyAttrListM (m := StateM (DomArena msg)) node xs a).2.get m = a.get m
  | [], a => ⟨rfl, fun _ _ => rfl⟩
  | x :: rest, a => by
      dsimp only [applyAttrListM, bind, StateT.bind]
      cases hres : applyAttrM (m := StateM (DomArena msg)) node x a with
      | mk u a1 =>
          have h1 := applyAttrM_preserves_meta a node x
          rw [hres] at h1
          have ih := applyAttrListM_preserves_meta node rest a1
          exact ⟨ih.1.trans h1.1, fun m hm => (ih.2 m hm).trans (h1.2 m hm)⟩

private theorem applyAttrsM_nextId {msg : Type} (a : DomArena msg) (node : Dom.Node)
    (attrs : List (Attr msg)) (e : ArenaEntry msg) :
    (applyAttrsM (m := StateM (DomArena msg)) node attrs (a.set node e)).2.nextId = a.nextId := by
  dsimp only [applyAttrsM, bind, StateT.bind, MonadDom.retainAttributes]
  exact (applyAttrListM_preserves_meta node (normalizeAttrs attrs) _).1

private theorem applyAttrsM_get_ne {msg : Type} (a : DomArena msg) (node : Dom.Node)
    (attrs : List (Attr msg)) (e : ArenaEntry msg) (m : Dom.Node) (hne : m ≠ node) :
    (applyAttrsM (m := StateM (DomArena msg)) node attrs (a.set node e)).2.get m = a.get m := by
  dsimp only [applyAttrsM, bind, StateT.bind, MonadDom.retainAttributes]
  exact ((applyAttrListM_preserves_meta node (normalizeAttrs attrs) _).2 m hne).trans
    (by simp [DomArena.modify, DomArena.get_set_ne _ _ hne])

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
    DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns h)

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
      DomTreeListAssocEquiv (hydratedCs.map (readDomTree f aOut)) (specDomList childNs target)

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
        DomTreeListAssocEquiv (hydratedCs.map (readDomTree f aOut)) (specDomList childNs rest))
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
      DomTreeListAssocEquiv (hydratedCs.map (readDomTree f aOut)) (specDomList childNs (.text s :: rest)) := by
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
  rcases hihFn hpreMid hdomMid with ⟨hydRest, hnextR, hboundR, hparR, hsubR, hfrR, heqR⟩
  rw [hstep]
  refine ⟨tn :: hydRest, by rw [haMidNext] at hnextR; omega,
    by rw [haMidNext] at hboundR; simp only [htmlListNodeCount, htmlNodeCount]; omega,
    by simpa [List.append_assoc] using hparR, ?_, ?_, ?_⟩
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
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hydrateDomKidsM, StateT.run, pure, StateT.pure]
      · simp [hydrateDomKidsM, StateT.run, pure, StateT.pure, htmlListNodeCount]
      · simpa [hydrateDomKidsM, StateT.run, pure, StateT.pure] using hpar
      · intro _ hm; nomatch hm
      · intro _ _ _ _; rfl
      · simp [specDomList, DomTreeListAssocEquiv]
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
                        rcases hih with ⟨hydRest, hnextR, hboundR, hparR, hsubR, hfrR, heqR⟩
                        rw [hstep]
                        refine ⟨tn :: hydRest, ?_⟩
                        refine ⟨by rw [haMidNext] at hnextR; omega,
                          by rw [haMidNext] at hboundR; simp only [htmlListNodeCount, htmlNodeCount]; omega,
                          by simpa [List.append_assoc] using hparR, ?_, ?_, ?_⟩
                        · intro z hz
                          rcases List.mem_cons.1 hz with hzEq | htail
                          · rw [hzEq]
                            have haOutTn : ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
                                (UInt32.ofNat (pre ++ [tn]).length) true rest).run aMid).2.get tn = .text s := by
                              rw [hfrR tn hparNeTn.symm (.inl htnMid) (by rw [haMidNext]; omega), hgetTnMid]
                            exact ⟨.inl ⟨htnLo, Nat.lt_of_lt_of_le htnMid hmidHi⟩, by
                              rw [haOutTn]; trivial⟩
                          · exact SubtreeInSet_mono (fun k hkS => by
                              rcases hkS with ⟨h1, h2⟩ | ⟨h1, h2⟩
                              · exact .inl ⟨Nat.le_trans hloMid h1, h2⟩
                              · exact .inr ⟨by rw [haMidNext] at h1; omega, h2⟩) (hsubR z htail)
                        · intro m hmPar hmOut hmLt
                          rw [hfrR m hmPar (hmOut.elim (fun h1 => .inl (by omega)) .inr) (by rw [haMidNext]; omega),
                              hframeMid m (by intro heq; rw [heq] at hmOut; rcases hmOut with h1 | h2 <;> omega)]
                        · have hreadTn : readDomTree (f' + 1) ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
                              (UInt32.ofNat (pre ++ [tn]).length) true rest).run aMid).2 tn = .text s := by
                            have haOutTn : ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
                                (UInt32.ofNat (pre ++ [tn]).length) true rest).run aMid).2.get tn = .text s := by
                              rw [hfrR tn hparNeTn.symm (.inl htnMid) (by rw [haMidNext]; omega), hgetTnMid]
                            dsimp only [readDomTree]; rw [haOutTn]
                          simp only [List.map_cons, specDomList, specDom, DomTreeListAssocEquiv]
                          rw [hreadTn]
                          exact ⟨rfl, heqR⟩
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
                  rcases hchildSpec with ⟨haMidNext, haMidBound, hchildSubMid, hframeMid, hequivChild⟩
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
                  rcases hih with ⟨hydRest, hnextR, hboundR, hparR, hsubR, hfrR, heqR⟩
                  have haOutChild := SubtreeInSet_frame (a := aMid)
                      (a' := ((hydrateDomKidsM (m := StateM (DomArena msg)) parent
                        (UInt32.ofNat (pre ++ [child]).length) false rest).run aMid).2)
                      (S := fun k => (lo ≤ k ∧ k < mid) ∨ (a.nextId ≤ k ∧ k < aMid.nextId))
                      (n := child)
                      (fun m hm => hfrR m
                        (by intro heq; rw [heq] at hm; rcases hm with h1 | h2 <;> omega)
                        (hm.elim (fun h1 => .inl h1.2) (fun h2 => .inr (Nat.le_trans hhiNext h2.1)))
                        (hm.elim (fun h1 => by omega) (fun h2 => h2.2)))
                      hchildSubMid
                  rw [hstep]
                  refine ⟨child :: hydRest, Nat.le_trans haMidNext hnextR,
                    by simp only [htmlListNodeCount]; omega,
                    by simpa [List.append_assoc] using hparR, ?_, ?_, ?_⟩
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

private theorem hydrateDomM_spec_strong (f : Nat) : @DomHydrateSpecAt msg f := by
  induction f using Nat.strongRecOn with
  | ind f ihDom =>
      intro ns h root a lo hi hbound hdep hdom
      cases h with
      | text s =>
          rcases hdom with ⟨hlo, hhi, hnext, hget⟩
          simp only [hydrateDomM, StateT.run, pure, StateT.pure]
          refine ⟨Nat.le_refl _, by simp [htmlNodeCount], ?_, ?_, ?_⟩
          · exact ⟨.inl ⟨hlo, hhi⟩, by simp [hget]⟩
          · intro _ _ _; exact trivial
          · simp [readDomTree, hget, specDom, DomTreeAssocEquiv]
      | element tag attrs cs =>
          rcases hdom with ⟨hlo, hhi, hnext, st, prev, domCs, hget, hm, hns, hownT, hownF⟩
          have hattrs := applyAttrsM_existing_element a root
            (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
            { st with clicks := [], inputs := [] } prev domCs attrs hm hns
          rcases hattrs with ⟨st', ha2Get, ha2Attrs, ha2Val, ha2Chk, hm'⟩
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
              refine ⟨by rw [ha2Next]; exact Nat.le_refl _, by rw [ha2Next]; simp [htmlNodeCount], ?_, ?_, ?_⟩
              · dsimp only [SubtreeInSet]
                refine ⟨.inl ⟨hlo, hhi⟩, ?_⟩
                rw [ha2Get]
                intro c hc; nomatch hc
              · intro m hmOut hmLt
                have hne : m ≠ root := by intro heq; rw [heq] at hmOut; omega
                exact ha2Outside m hne
              · dsimp only [readDomTree, specDom]
                rw [ha2Get, hown]
                exact ⟨rfl, rfl, ha2Attrs, ha2Val, ha2Chk, trivial⟩
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
              change ∃ hydratedCs, _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hkidsRun
              have hzeroEq : (UInt32.ofNat 0 : UInt32) = 0 := rfl
              rw [hzeroEq] at hkidsRun
              rcases hkidsRun with ⟨hydratedCs, hnextLe, hnextBound, hgetOut, hsubSet, hframeKids, hequivKids⟩
              rw [hrunOut]
              refine ⟨by omega, by simp only [htmlNodeCount]; omega, ?_, ?_, ?_⟩
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
                exact ⟨rfl, rfl, ha2Attrs, ha2Val, ha2Chk, hequivKids⟩

/-- Imperative HTML5 hydration simulation for `hydrateDomM`:
    given an SSR-parsed `HydratableDom` tree whose text children were coalesced by the HTML5 parser
    (`coalesceTextRun`), `hydrateDomM` preserves outside nodes and makes `readDomTree (f + 1) aOut root`
    match `specDom ns h` via `DomTreeAssocEquiv`. -/
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
    DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns h) :=
  hydrateDomM_spec_strong f ns h root a lo hi hbound hdep hdom

/-- Imperative child-list HTML5 hydration simulation for `hydrateDomKidsM`:
    interpolates `hydrateTextSlotM` and recursive `hydrateDomM` calls across `target`, keeping child
    subtrees disjoint and producing `DomTreeListAssocEquiv` against `specDomList`. -/
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
      DomTreeListAssocEquiv (hydratedCs.map (readDomTree f aOut)) (specDomList childNs target) :=
  hydrateDomKidsM_spec_step f (fun f' _ => hydrateDomM_spec_strong f') childNs parent pns ptag pst pmg
    target inTextRun pre domCs lo hi a hlen hbound hdep hparLo hpreSub hpar hdom

end Qed

