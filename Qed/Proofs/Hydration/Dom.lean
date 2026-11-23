import Qed.Proofs.DomSubtree

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

theorem textOf_eq_some_iff {h : Html msg} {s : String} :
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
      | none => exact ⟨by simpa [hydrateDomTextModel, coalesceTextRun, hc] using ihFalse,
          by simpa [hydrateDomTextModel, dropCurrentTextRun, hc] using ihFalse⟩
      | some s =>
          have hce : c = .text s := textOf_eq_some_iff.1 hc; subst hce
          by_cases hse : s = ""
          · subst hse
            exact ⟨by simpa [hydrateDomTextModel, coalesceTextRun, Html.textOf?] using ihFalse,
              by simpa [hydrateDomTextModel, dropCurrentTextRun, Html.textOf?] using ihTrue⟩
          · refine ⟨?_, by simpa [hydrateDomTextModel, dropCurrentTextRun, Html.textOf?, hse] using ihTrue⟩
            simp only [coalesceTextRun, Html.textOf?, beq_eq_false_iff_ne.2 hse, Bool.false_eq_true, ↓reduceIte, hydrateDomTextModel, ihTrue]
            cases hm : hasMoreText rest with
            | true => simp
            | false => simp [hasMoreText_false_restOfTextRun rest hm]

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
  rw [if_neg (by simp [hown]), DomArena.get_set_self, DomArena.set_set,
      show applyAttrsM (m := StateM (DomArena msg)) node attrs (a.set node (.element ns tag {} [] cs)) = _ from
        applyAttrsM_fresh_element a node ns tag cs attrs]; rfl


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

theorem HydratableDom_bounds {msg : Type} :
    ∀ (f : Nat) (ns : String) (d : Html msg) (a : DomArena msg) (lo hi : Nat) (n : Dom.Node),
      HydratableDom f ns d a lo hi n → lo ≤ n.toNat ∧ hi ≤ a.nextId ∧ lo ≤ hi
  | 0, _, _, _, _, _, _, h => False.elim h
  | _ + 1, _, .text _, _, _, _, _, h | _ + 1, _, .element _ _ _, _, _, _, _, h =>
      ⟨h.1, h.2.2.1, Nat.le_trans h.1 (Nat.le_of_lt h.2.1)⟩

theorem HydratableDomList_bounds {msg : Type} :
    ∀ (f : Nat) (ns : String) (ds : List (Html msg)) (a : DomArena msg) (lo hi : Nat) (ns' : List Dom.Node),
      HydratableDomList f ns ds a lo hi ns' → lo ≤ hi ∧ hi ≤ a.nextId
  | _, _, [], _, _, _, [], h => h
  | f, ns, d :: drest, a, lo, hi, n :: nrest, h => by
      rcases h with ⟨mid, hd, hrest⟩
      have b1 := HydratableDom_bounds f ns d a lo mid n hd
      have b2 := HydratableDomList_bounds f ns drest a mid hi nrest hrest
      exact ⟨by omega, b2.2⟩
  | _, _, [], _, _, _, _ :: _, h | _, _, _ :: _, _, _, _, [], h => False.elim h

theorem HydratableDomList_nodes_lt {msg : Type} :
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
  | _, _, [], _, _, _, _ :: _, h | _, _, _ :: _, _, _, _, [], h => False.elim h

private theorem HydratableDomList_frame_of {msg : Type} (f : Nat)
    (ih : ∀ (ns : String) (d : Html msg) (a a' : DomArena msg) (lo hi : Nat) (n : Dom.Node), a.nextId ≤ a'.nextId →
      (∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m) →
      HydratableDom f ns d a lo hi n → HydratableDom f ns d a' lo hi n) (ns : String) :
    ∀ (ds : List (Html msg)) (a a' : DomArena msg) (lo hi : Nat) (ns' : List Dom.Node),
      a.nextId ≤ a'.nextId → (∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m) →
      HydratableDomList f ns ds a lo hi ns' → HydratableDomList f ns ds a' lo hi ns'
  | [], _, _, _, _, [], hle, _, ⟨h1, h2⟩ => ⟨h1, Nat.le_trans h2 hle⟩
  | d :: drest, a, a', lo, hi, n :: nrest, hle, hfr, ⟨mid, hd, hrest⟩ =>
      let h1 := (HydratableDom_bounds f ns d a lo mid n hd).2.2
      let h2 := (HydratableDomList_bounds f ns drest a mid hi nrest hrest).1
      ⟨mid, ih ns d a a' lo mid n hle (fun m hm1 hm2 => hfr m hm1 (Nat.lt_of_lt_of_le hm2 h2)) hd,
       HydratableDomList_frame_of f ih ns drest a a' mid hi nrest hle (fun m hm1 hm2 => hfr m (Nat.le_trans h1 hm1) hm2) hrest⟩
  | [], _, _, _, _, _ :: _, _, _, h | _ :: _, _, _, _, _, [], _, _, h => False.elim h

private theorem HydratableDom_frame {msg : Type} :
    ∀ (f : Nat) (ns : String) (d : Html msg) (a a' : DomArena msg) (lo hi : Nat) (n : Dom.Node),
      a.nextId ≤ a'.nextId → (∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m) →
      HydratableDom f ns d a lo hi n → HydratableDom f ns d a' lo hi n
  | 0, _, _, _, _, _, _, _, _, _, h => False.elim h
  | _ + 1, _, .text _, _, _, _, _, n, hle, hfr, h =>
      ⟨h.1, h.2.1, Nat.le_trans h.2.2.1 hle, by rw [hfr n h.1 h.2.1, h.2.2.2]⟩
  | f + 1, ns, .element tag attrs cs, a, a', lo, hi, n, hle, hfr, h => by
      rcases h with ⟨hlo, hhi, hnext, st, prev, domCs, hget, hm, hns, hownT, hownF⟩
      exact ⟨hlo, hhi, Nat.le_trans hnext hle, st, prev, domCs, by rw [hfr n hlo hhi, hget], hm, hns, hownT,
        fun hown => let ⟨mid, hmid, hk⟩ := hownF hown
          ⟨mid, hmid, HydratableDomList_frame_of f (HydratableDom_frame f) (Dom.childNsOf ns tag)
            (coalesceTextRun cs) a a' mid hi domCs hle (fun m hm1 hm2 => hfr m (by omega) hm2) hk⟩⟩

theorem HydratableDomList_frame {msg : Type} (f : Nat) (ns : String) (ds : List (Html msg))
    (a a' : DomArena msg) (lo hi : Nat) (ns' : List Dom.Node) (hle : a.nextId ≤ a'.nextId)
    (hfr : ∀ m : Dom.Node, lo ≤ m.toNat → m.toNat < hi → a'.get m = a.get m)
    (h : HydratableDomList f ns ds a lo hi ns') : HydratableDomList f ns ds a' lo hi ns' :=
  HydratableDomList_frame_of f (HydratableDom_frame f) ns ds a a' lo hi ns' hle hfr h

theorem hydrateTextSlotM_alloc_spec (a : DomArena msg) (parent : Dom.Node) (inTextRun : Bool)
    (s : String) (hcond : s = "" ∨ inTextRun = true) (moreInRun : Unit → Bool)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (pre suf : List Dom.Node) (hnot : UInt32.ofNat a.nextId ∉ pre ++ suf)
    (hdisj : ∀ r ∈ suf, r ∉ pre) (hpreLen : pre.length < UInt32.size)
    (hparNe : parent ≠ UInt32.ofNat a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ suf)) :
    let tn := UInt32.ofNat a.nextId
    let ((outNode, outRun), a') :=
      (hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) inTextRun s moreInRun).run a
    outNode = tn ∧ outRun = inTextRun ∧ a'.nextId = a.nextId + 1 ∧
    a'.get tn = .text s ∧ a'.get parent = .element pns ptag pst pmg (pre ++ tn :: suf) ∧
    (∀ m : Dom.Node, m ≠ parent → m ≠ tn → a'.get m = a.get m) := by
  have hins : w3cInsertBefore (pre ++ suf) (UInt32.ofNat pre.length).toNat (UInt32.ofNat a.nextId) =
      pre ++ UInt32.ofNat a.nextId :: suf := by
    rw [uint32_toNat_ofNat_lt pre.length hpreLen]; exact w3cInsertBefore_fresh_append pre suf _ hnot hdisj
  have hallocPar : (DomArena.mk (a.nextId + 1)
      (fun m => if m == UInt32.ofNat a.nextId then .text s else a.store m)
      a.signals a.sigEvents a.tmpls a.rowEvs).get parent = .element pns ptag pst pmg (pre ++ suf) := by
    simp [DomArena.get, hparNe]; exact hpar
  dsimp only [hydrateTextSlotM]
  by_cases hs : (s == "") = true <;> (
    first
    | (have hse : s = "" := beq_iff_eq.1 hs; subst hse; rw [if_pos hs])
    | (have hir : inTextRun = true := hcond.resolve_left (fun h => hs (by rw [h]; rfl)); subst hir; rw [if_neg hs, if_pos rfl])
    dsimp only [StateT.run, bind, StateT.bind, pure,
      MonadDom.createText, DomArena.alloc, MonadDom.insertBeforeNode, DomArena.modifyChildren, DomArena.modify]
    rw [hallocPar]; dsimp only
    exact ⟨rfl, rfl, rfl, by simp [DomArena.get, DomArena.set, hparNe.symm], by rw [DomArena.get_set_self, hins],
      fun m hm1 hm2 => by simp [DomArena.get, DomArena.set, hm1, hm2]⟩)

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
    (∀ m : Dom.Node, m ≠ parent → m ≠ ph → a'.get m = a.get m) :=
  hydrateTextSlotM_alloc_spec a parent inTextRun "" (.inl rfl) moreInRun pns ptag pst pmg pre suf hnot hdisj hpreLen hparNe hpar

theorem hydrateTextSlotM_split_spec (a : DomArena msg) (parent : Dom.Node) (s : String)
    (_hs : s ≠ "") (moreInRun : Unit → Bool)
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
    (∀ m : Dom.Node, m ≠ parent → m ≠ tn → a'.get m = a.get m) :=
  hydrateTextSlotM_alloc_spec a parent true s (.inr rfl) moreInRun pns ptag pst pmg pre suf hnot hdisj hpreLen hparNe hpar

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
  simp only [hydrateTextSlotM, beq_eq_false_iff_ne.2 hs, Bool.false_eq_true, ↓reduceIte, StateT.run, bind, StateT.bind,
             pure, MonadDom.setText, DomArena.modify, hpar, uint32_toNat_ofNat_lt pre.length hpreLen, getD_append_right]
  cases more
  · exact ⟨rfl, rfl, rfl, by simpa [hmore rfl] using htn, fun _ _ => rfl⟩
  · simp only [↓reduceIte, StateT.bind, StateT.pure, true_and]; rw [htn]
    exact ⟨rfl, DomArena.get_set_self .., fun m hm => DomArena.get_set_ne _ _ hm⟩

theorem HydratableDomList_cons_bounds {msg : Type} {f : Nat} {ns : String}
    {d : Html msg} {drest : List (Html msg)} {a : DomArena msg} {lo hi : Nat} {n : Dom.Node} {nrest : List Dom.Node}
    (h : HydratableDomList f ns (d :: drest) a lo hi (n :: nrest)) :
    ∃ mid, lo ≤ mid ∧ mid ≤ hi ∧ hi ≤ a.nextId ∧
      HydratableDom f ns d a lo mid n ∧ HydratableDomList f ns drest a mid hi nrest := by
  rcases h with ⟨mid, hd, hrest⟩
  have b1 := HydratableDom_bounds f ns d a lo mid n hd
  have b2 := HydratableDomList_bounds f ns drest a mid hi nrest hrest
  exact ⟨mid, b1.2.2, b2.1, b2.2, hd, hrest⟩

theorem htmlListDepth_cons_pos {msg : Type} (c : Html msg) (rest : List (Html msg)) :
    1 ≤ htmlListDepth (c :: rest) :=
  Nat.le_trans (by cases c <;> simp [htmlDepth]) (Nat.le_max_left ..)

theorem textOf_none_is_element {msg : Type} :
    ∀ {c : Html msg}, c.textOf? = none → ∃ tag attrs kids, c = .element tag attrs kids
  | .text _, h => by simp [Html.textOf?] at h
  | .element tag attrs kids, _ => ⟨tag, attrs, kids, rfl⟩

abbrev DomHydrateOut {msg : Type} (f : Nat) (ns : String) (h : Html msg) (root : Dom.Node)
    (a : DomArena msg) (lo hi : Nat) (aOut : DomArena msg) : Prop :=
  a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlNodeCount h ∧
  SubtreeInSet (f + 1) aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) root ∧
  (∀ m : Dom.Node, (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
  DomTreeAssocEquiv (readDomTree (f + 1) aOut root) (specDom ns h) ∧
  (h.DomClean = true →
    CleanDomSubtree (f + 1) ns h aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) root)

abbrev KidsHydrateOut {msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (target : List (Html msg)) (pre : List Dom.Node) (lo hi : Nat) (a aOut : DomArena msg) : Prop :=
  ∃ hydratedCs : List Dom.Node,
    a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount target ∧
    aOut.get parent = .element pns ptag pst pmg (pre ++ hydratedCs) ∧
    (∀ c ∈ hydratedCs, SubtreeInSet f aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) c) ∧
    (∀ m : Dom.Node, m ≠ parent → (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    DomTreeListAssocEquiv (hydratedCs.map (readDomTree f aOut)) (specDomList childNs target) ∧
    (Html.DomCleanList target = true →
      CleanDomChildren f childNs target aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) hydratedCs)

private abbrev DomHydrateSpecAt {msg : Type} (f : Nat) : Prop :=
  ∀ (ns : String) (h : Html msg) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat),
    a.nextId + htmlNodeCount h < UInt32.size → htmlDepth h ≤ f + 1 → HydratableDom (f + 1) ns h a lo hi root →
    DomHydrateOut f ns h root a lo hi ((hydrateDomM (m := StateM (DomArena msg)) h root).run a).2

private abbrev KidsHydrateSpecAt {msg : Type} (f : Nat) : Prop :=
  ∀ (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (target : List (Html msg)) (inTextRun : Bool) (pre domCs : List Dom.Node) (lo hi : Nat) (a : DomArena msg),
    pre.length + target.length < UInt32.size → a.nextId + htmlListNodeCount target < UInt32.size →
    htmlListDepth target ≤ f → parent.toNat < lo →
    (∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet f a Sx x) →
    a.get parent = .element pns ptag pst pmg (pre ++ domCs) →
    HydratableDomList f childNs (if inTextRun then dropCurrentTextRun target else coalesceTextRun target) a lo hi domCs →
    KidsHydrateOut f childNs parent pns ptag pst pmg target pre lo hi a
      ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) inTextRun target).run a).2

theorem hydrateDomKidsM_fresh_nextId {msg : Type} (f : Nat) (childNs : String)
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

private theorem preSub_extend_core {msg : Type} {f : Nat} {childNs : String} {parent child : Dom.Node}
    {targetRest : List (Html msg)} {pre domRest : List Dom.Node} {lo mid hi : Nat} {a aMid : DomArena msg}
    {Snew : Nat → Prop} (hloMid : lo ≤ mid) (haMidNext : a.nextId ≤ aMid.nextId)
    (hframeDom : ∀ m : Dom.Node, mid ≤ m.toNat → m.toNat < hi → aMid.get m = a.get m)
    (hframePre : ∀ m : Dom.Node, ((parent.toNat < m.toNat ∧ m.toNat < lo) ∨ (hi ≤ m.toNat ∧ m.toNat < a.nextId)) → aMid.get m = a.get m)
    (hpreSub : ∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet f a Sx x)
    (hrestDom : HydratableDomList f childNs targetRest a mid hi domRest)
    (hSnew : ∀ k, Snew k → (parent.toNat < k ∧ k < mid) ∨ (hi ≤ k ∧ k < aMid.nextId))
    (hSubNew : SubtreeInSet f aMid Snew child) :
    HydratableDomList f childNs targetRest aMid mid hi domRest ∧
    (∀ x ∈ pre ++ [child], ∃ Sx,
      (∀ k, Sx k → (parent.toNat < k ∧ k < mid) ∨ (hi ≤ k ∧ k < aMid.nextId)) ∧ SubtreeInSet f aMid Sx x) := by
  refine ⟨HydratableDomList_frame f childNs targetRest a aMid mid hi domRest haMidNext hframeDom hrestDom, fun x hx => ?_⟩
  rcases List.mem_append.1 hx with hOld | hNew
  · rcases hpreSub x hOld with ⟨Sx, hSx, hsub⟩
    exact ⟨Sx, fun k hk => (hSx k hk).elim (fun h1 => .inl ⟨h1.1, Nat.lt_of_lt_of_le h1.2 hloMid⟩)
        (fun h2 => .inr ⟨h2.1, Nat.lt_of_lt_of_le h2.2 haMidNext⟩),
      (SubtreeInSet_frame (fun m hm => hframePre m (hSx m.toNat hm)) hsub).1⟩
  · simp only [List.mem_singleton] at hNew; subst hNew; exact ⟨Snew, hSnew, hSubNew⟩

theorem preSub_extend_alloc {msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node)
    (targetRest : List (Html msg)) (pre domCs : List Dom.Node) (lo hi : Nat) (a aMid : DomArena msg) (s : String)
    (hfPos : 1 ≤ f) (hbound : a.nextId < UInt32.size) (hparLo : parent.toNat < lo) (hhiNext : hi ≤ a.nextId)
    (haMidNext : aMid.nextId = a.nextId + 1) (hgetNew : aMid.get (UInt32.ofNat a.nextId) = .text s)
    (hframeMid : ∀ m : Dom.Node, m ≠ parent → m ≠ UInt32.ofNat a.nextId → aMid.get m = a.get m)
    (hpreSub : ∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet f a Sx x)
    (hdom' : HydratableDomList f childNs targetRest a lo hi domCs) :
    HydratableDomList f childNs targetRest aMid lo hi domCs ∧
    (∀ x ∈ pre ++ [UInt32.ofNat a.nextId], ∃ Sx,
      (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < aMid.nextId)) ∧ SubtreeInSet f aMid Sx x) := by
  have ⟨hloHi, _⟩ := HydratableDomList_bounds f childNs targetRest a lo hi domCs hdom'
  have huNext : (UInt32.ofNat a.nextId).toNat = a.nextId := uint32_toNat_ofNat_lt a.nextId hbound
  exact preSub_extend_core (Snew := fun k => k = a.nextId) (Nat.le_refl _) (by omega)
    (fun m hm1 hm2 => hframeMid m (fun heq => by rw [heq] at hm1; omega) (fun heq => by have : m.toNat = a.nextId := heq ▸ huNext; omega))
    (fun m hm => hframeMid m (fun heq => by rw [heq] at hm; rcases hm with h1 | h2 <;> omega)
      (fun heq => by have : m.toNat = a.nextId := heq ▸ huNext; rcases hm with h1 | h2 <;> omega))
    hpreSub hdom' (fun _ hk => .inr ⟨by omega, by omega⟩)
    (by cases f with | zero => omega | succ _ => exact ⟨huNext, by simp [hgetNew]⟩)

theorem preSub_extend_existing {msg : Type} (f : Nat) (childNs : String) (parent child : Dom.Node)
    (targetRest : List (Html msg)) (pre domRest : List Dom.Node) (lo mid hi : Nat) (a aMid : DomArena msg)
    (Snew : Nat → Prop)
    (hloMid : lo ≤ mid) (hmidHi : mid ≤ hi) (hhiNext : hi ≤ a.nextId) (haMidNext : a.nextId ≤ aMid.nextId)
    (hframe : ∀ m : Dom.Node, (m.toNat < lo ∨ mid ≤ m.toNat) → m.toNat < a.nextId → aMid.get m = a.get m)
    (hpreSub : ∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet f a Sx x)
    (hrestDom : HydratableDomList f childNs targetRest a mid hi domRest)
    (hSnew : ∀ k, Snew k → (parent.toNat < k ∧ k < mid) ∨ (hi ≤ k ∧ k < aMid.nextId))
    (hSubNew : SubtreeInSet f aMid Snew child) :
    HydratableDomList f childNs targetRest aMid mid hi domRest ∧
    (∀ x ∈ pre ++ [child], ∃ Sx,
      (∀ k, Sx k → (parent.toNat < k ∧ k < mid) ∨ (hi ≤ k ∧ k < aMid.nextId)) ∧ SubtreeInSet f aMid Sx x) :=
  preSub_extend_core hloMid haMidNext (fun m hm1 _ => hframe m (.inr hm1) (by omega))
    (fun m hm => hframe m (hm.elim (fun h1 => .inl h1.2) (fun h2 => .inr (Nat.le_trans hmidHi h2.1)))
      (hm.elim (fun h1 => by omega) (fun h2 => h2.2)))
    hpreSub hrestDom hSnew hSubNew

theorem hydrateKids_ind {α msg : Type} (f : Nat) (childNs : String) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (toHtml : α → Html msg) (ItemOk : α → Prop)
    (Post : List α → Bool → List Dom.Node → Nat → Nat → DomArena msg → Prop)
    (hNil : ∀ inTextRun pre lo hi a,
      a.get parent = .element pns ptag pst pmg pre →
      Post [] inTextRun pre lo hi a)
    (hText : ∀ c rest inTextRun inRun' pre tn lo loRest hi a (s : String) (aMid : DomArena msg) (S_tn : Nat → Prop),
      toHtml c = .text s → ItemOk c →
      1 ≤ f → lo ≤ loRest → a.nextId ≤ aMid.nextId → aMid.nextId ≤ a.nextId + 1 →
      parent ≠ tn → UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) →
      hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) inTextRun s
        (fun () => hasMoreText (rest.map toHtml)) a = ((tn, inRun'), aMid) →
      aMid.get tn = .text s → S_tn tn.toNat →
      (∀ k, S_tn k → (lo ≤ k ∧ k < hi) ∨ (a.nextId ≤ k ∧ k < aMid.nextId)) →
      (∀ k, S_tn k → (k < loRest ∨ hi ≤ k) ∧ k < aMid.nextId) →
      (∀ m : Dom.Node, m ≠ parent → (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < a.nextId → aMid.get m = a.get m) →
      Post rest inRun' (pre ++ [tn]) loRest hi aMid →
      Post (c :: rest) inTextRun pre lo hi a)
    (hElem : ∀ c rest inTextRun pre child domRest lo mid hi a (f' : Nat),
      f = f' + 1 → (toHtml c).textOf? = none → ItemOk c → (∀ r ∈ rest, ItemOk r) →
      pre.length + (c :: rest).length < UInt32.size →
      (UInt32.ofNat pre.length).toNat = pre.length →
      UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) →
      a.nextId + htmlListNodeCount ((c :: rest).map toHtml) < UInt32.size →
      htmlDepth (toHtml c) ≤ f' + 1 → htmlListDepth (rest.map toHtml) ≤ f' + 1 →
      parent.toNat < lo → lo ≤ mid → mid ≤ hi → hi ≤ a.nextId →
      a.get parent = .element pns ptag pst pmg (pre ++ child :: domRest) →
      HydratableDom (f' + 1) childNs (toHtml c) a lo mid child →
      HydratableDomList (f' + 1) childNs (coalesceTextRun (rest.map toHtml)) a mid hi domRest →
      (∀ (aMid : DomArena msg),
        a.nextId ≤ aMid.nextId → aMid.nextId ≤ a.nextId + htmlNodeCount (toHtml c) →
        SubtreeInSet (f' + 1) aMid (fun k => (lo ≤ k ∧ k < mid) ∨ (a.nextId ≤ k ∧ k < aMid.nextId)) child →
        (∀ m : Dom.Node, (m.toNat < lo ∨ mid ≤ m.toNat) → m.toNat < a.nextId → aMid.get m = a.get m) →
        Post rest false (pre ++ [child]) mid hi aMid ∧
        (∀ x ∈ pre ++ [child], ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < mid) ∨ (hi ≤ k ∧ k < aMid.nextId)) ∧ SubtreeInSet (f' + 1) aMid Sx x) ∧
        aMid.get parent = .element pns ptag pst pmg ((pre ++ [child]) ++ domRest) ∧
        HydratableDomList (f' + 1) childNs (coalesceTextRun (rest.map toHtml)) aMid mid hi domRest) →
      Post (c :: rest) inTextRun pre lo hi a) :
    ∀ (target : List α) (inTextRun : Bool) (pre domCs : List Dom.Node) (lo hi : Nat) (a : DomArena msg),
      (∀ x ∈ target, ItemOk x) →
      pre.length + target.length < UInt32.size →
      a.nextId + htmlListNodeCount (target.map toHtml) < UInt32.size →
      htmlListDepth (target.map toHtml) ≤ f →
      parent.toNat < lo →
      (∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet f a Sx x) →
      a.get parent = .element pns ptag pst pmg (pre ++ domCs) →
      HydratableDomList f childNs
        (if inTextRun then dropCurrentTextRun (target.map toHtml) else coalesceTextRun (target.map toHtml))
        a lo hi domCs →
      Post target inTextRun pre lo hi a
  | [], inTextRun, pre, domCs, lo, hi, a, _, _, _, _, _, _, hpar, hdom => by
      have hdomNil : domCs = [] := by
        cases inTextRun <;> simp [coalesceTextRun, dropCurrentTextRun] at hdom <;> cases domCs with
        | nil => rfl | cons _ _ => exact False.elim hdom
      subst hdomNil; exact hNil inTextRun pre lo hi a (by simpa using hpar)
  | c :: rest, inTextRun, pre, domCs, lo, hi, a, hok, hlen, hbound, hdep, hparLo, hpreSub, hpar, hdom => by
      have hrestOk : ∀ r ∈ rest, ItemOk r := fun r hr => hok r (.tail _ hr)
      rcases HydratableDomList_bounds f childNs _ a lo hi domCs hdom with ⟨hloHi, hhiNext⟩
      have hposF : 1 ≤ f := Nat.le_trans (htmlListDepth_cons_pos (toHtml c) (rest.map toHtml)) hdep
      have huIdxNext : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) := by
        simp only [List.length_cons] at hlen; exact uint32_ofNat_succ pre.length (by omega)
      have hdisjDom : ∀ r ∈ domCs, r ∉ pre := fun r hr hmem => by
        have hlt := HydratableDomList_nodes_lt f childNs _ a lo hi domCs hdom r hr
        rcases hpreSub r hmem with ⟨Sx, hSx, hsub⟩
        cases f with | zero => omega | succ _ => rcases hSx r.toNat hsub.1 with h1 | h2 <;> omega
      cases htxt : (toHtml c).textOf? with
      | some s =>
          have hcEq : toHtml c = .text s := textOf_eq_some_iff.1 htxt
          simp only [List.map_cons, hcEq, htmlListNodeCount, htmlNodeCount] at hbound
          have hrestDep : htmlListDepth (rest.map toHtml) ≤ f := by
            simp only [List.map_cons, htmlListDepth] at hdep; exact Nat.le_trans (Nat.le_max_right _ _) hdep
          by_cases halloc : s = "" ∨ inTextRun = true
          · have hdom' : HydratableDomList f childNs (if inTextRun then dropCurrentTextRun (rest.map toHtml) else coalesceTextRun (rest.map toHtml)) a lo hi domCs := by
              rcases halloc with rfl | rfl
              · cases inTextRun <;> simpa [List.map_cons, hcEq, coalesceTextRun, dropCurrentTextRun] using hdom
              · by_cases hs : s = "" <;> simpa [List.map_cons, hcEq, dropCurrentTextRun, Html.textOf?, hs] using hdom
            rcases hydrateDomKidsM_fresh_nextId f childNs parent _ pre domCs lo hi a hposF (by omega) hparLo hpreSub hdom' with
              ⟨hnotIn, hparNeTn⟩
            let tn := UInt32.ofNat a.nextId
            have htnNat : tn.toNat = a.nextId := uint32_toNat_ofNat_lt a.nextId (by omega)
            let resSlot := (hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
              inTextRun s (fun () => hasMoreText (rest.map toHtml))).run a
            have hslot := hydrateTextSlotM_alloc_spec a parent inTextRun s halloc (fun () => hasMoreText (rest.map toHtml))
              pns ptag pst pmg pre domCs hnotIn hdisjDom (by simp at hlen; omega) hparNeTn hpar
            have haMidNext : resSlot.2.nextId = a.nextId + 1 := hslot.2.2.1
            have ⟨hdomMid, hpreMid⟩ := preSub_extend_alloc f childNs parent _ pre domCs lo hi a resSlot.2 s
              hposF (by omega) hparLo hhiNext haMidNext hslot.2.2.2.1 hslot.2.2.2.2.2 hpreSub hdom'
            exact hText c rest inTextRun inTextRun pre tn lo lo hi a s resSlot.2 (fun k => k = a.nextId)
              hcEq (hok c (.head _)) hposF (Nat.le_refl _) (by rw [haMidNext]; omega) (by rw [haMidNext]; exact Nat.le_refl _)
              hparNeTn huIdxNext (Prod.ext (Prod.ext hslot.1 hslot.2.1) rfl) hslot.2.2.2.1 htnNat
              (fun _ hk => .inr ⟨hk ▸ Nat.le_refl _, by rw [haMidNext]; omega⟩)
              (fun _ hk => ⟨.inr (by omega), by rw [haMidNext]; omega⟩)
              (fun m hmPar _ hmLt => hslot.2.2.2.2.2 m hmPar (fun heq => by have : m.toNat = a.nextId := heq ▸ htnNat; omega))
              (hydrateKids_ind f childNs parent pns ptag pst pmg toHtml ItemOk Post hNil hText hElem rest inTextRun (pre ++ [tn]) domCs lo hi resSlot.2 hrestOk
                (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen; omega)
                (by rw [haMidNext]; omega) hrestDep hparLo hpreMid (by simpa [List.append_assoc] using hslot.2.2.2.2.1) hdomMid)
          · have ⟨hsEmpty, hirF⟩ : s ≠ "" ∧ inTextRun = false :=
              ⟨fun h => halloc (.inl h), Bool.eq_false_iff.2 fun h => halloc (.inr h)⟩
            subst hirF
            have hdomCoal : HydratableDomList f childNs (.text (s ++ restOfTextRun (rest.map toHtml)) :: dropCurrentTextRun (rest.map toHtml)) a lo hi domCs := by
              simpa [List.map_cons, hcEq, coalesceTextRun, Html.textOf?, hsEmpty] using hdom
            cases domCs with
            | nil => exact False.elim hdomCoal
            | cons tn domRest =>
                rcases HydratableDomList_cons_bounds hdomCoal with ⟨mid, hloMid, hmidHi, hiNext, htnDom, hrestDom⟩
                cases f with
                | zero => omega
                | succ f' =>
                    rcases htnDom with ⟨htnLo, htnMid, _, hgetTn⟩
                    let resSlot := (hydrateTextSlotM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)
                      false s (fun () => hasMoreText (rest.map toHtml))).run a
                    have hslot := hydrateTextSlotM_head_spec a parent tn s (restOfTextRun (rest.map toHtml)) hsEmpty
                      (hasMoreText (rest.map toHtml)) (hasMoreText_false_restOfTextRun (rest.map toHtml))
                      pns ptag pst pmg pre domRest (by simp at hlen; omega) hpar hgetTn
                    have haMidNext : resSlot.2.nextId = a.nextId := hslot.2.2.1
                    have hparNeTn : parent ≠ tn := fun heq => by rw [heq] at hparLo; omega
                    have hparMid : resSlot.2.get parent = .element pns ptag pst pmg ((pre ++ [tn]) ++ domRest) :=
                      (hslot.2.2.2.2 parent hparNeTn).trans (by rw [hpar]; simp [List.append_assoc])
                    have ⟨hdomMid, hpreMid⟩ := preSub_extend_existing (f' + 1) childNs parent tn
                      (dropCurrentTextRun (rest.map toHtml)) pre domRest lo mid hi a resSlot.2 (fun k => k = tn.toNat)
                      hloMid hmidHi hiNext (by rw [haMidNext]; exact Nat.le_refl _)
                      (fun m hm _ => hslot.2.2.2.2 m fun heq => by rw [heq] at hm; rcases hm with h1 | h2 <;> omega)
                      hpreSub hrestDom (fun _ hk => .inl ⟨by omega, by omega⟩)
                      ⟨rfl, by rw [show resSlot.2.get tn = .text s from hslot.2.2.2.1]; trivial⟩
                    exact hText c rest false true pre tn lo mid hi a s resSlot.2 (fun k => lo ≤ k ∧ k < mid)
                      hcEq (hok c (.head _)) (Nat.succ_pos _) hloMid (by rw [haMidNext]; exact Nat.le_refl _) (by rw [haMidNext]; omega)
                      hparNeTn huIdxNext (Prod.ext (Prod.ext hslot.1 hslot.2.1) rfl) hslot.2.2.2.1 ⟨htnLo, htnMid⟩
                      (fun _ hk => .inl ⟨hk.1, Nat.lt_of_lt_of_le hk.2 hmidHi⟩)
                      (fun _ hk => ⟨.inl hk.2, by rw [haMidNext]; omega⟩)
                      (fun m _ hmOut _ => hslot.2.2.2.2 m (fun heq => by rw [heq] at hmOut; rcases hmOut with h1 | h2 <;> omega))
                      (hydrateKids_ind (f' + 1) childNs parent pns ptag pst pmg toHtml ItemOk Post hNil hText hElem rest true (pre ++ [tn]) domRest mid hi resSlot.2 hrestOk
                        (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen; omega)
                        (by rw [haMidNext]; omega) hrestDep (by omega) hpreMid hparMid (by simpa using hdomMid))
      | none =>
          rcases textOf_none_is_element htxt with ⟨tag, attrs, kids, hcEq⟩
          have hcDep : htmlDepth (toHtml c) ≤ f := by simp only [List.map_cons, htmlListDepth] at hdep; exact Nat.le_trans (Nat.le_max_left _ _) hdep
          have hrestDep : htmlListDepth (rest.map toHtml) ≤ f := by simp only [List.map_cons, htmlListDepth] at hdep; exact Nat.le_trans (Nat.le_max_right _ _) hdep
          have hdomElem : HydratableDomList f childNs (toHtml c :: coalesceTextRun (rest.map toHtml)) a lo hi domCs := by
            cases inTextRun <;> simpa [List.map_cons, hcEq, coalesceTextRun, dropCurrentTextRun, Html.textOf?] using hdom
          cases domCs with
          | nil => exact False.elim hdomElem
          | cons child domRest =>
              rcases HydratableDomList_cons_bounds hdomElem with ⟨mid, hloMid, hmidHi, hiNext, hchildDom, hrestDom⟩
              cases f with
              | zero => rw [hcEq] at hcDep; simp [htmlDepth] at hcDep
              | succ f' =>
                  refine hElem c rest inTextRun pre child domRest lo mid hi a f' rfl htxt (hok c (.head _)) hrestOk
                    hlen (uint32_toNat_ofNat_lt pre.length (by simp at hlen; omega)) huIdxNext hbound hcDep hrestDep hparLo hloMid hmidHi hiNext hpar hchildDom hrestDom
                    fun aMid haMidNext haMidBound hchildSubMid hframeMid => ?_
                  have hparMid : aMid.get parent = .element pns ptag pst pmg ((pre ++ [child]) ++ domRest) := by
                    rw [hframeMid parent (.inl hparLo) (by omega), hpar]; simp [List.append_assoc]
                  have ⟨hdomMid, hpreMid⟩ := preSub_extend_existing (f' + 1) childNs parent child
                    (coalesceTextRun (rest.map toHtml)) pre domRest lo mid hi a aMid
                    (fun k => (lo ≤ k ∧ k < mid) ∨ (a.nextId ≤ k ∧ k < aMid.nextId))
                    hloMid hmidHi hiNext haMidNext hframeMid hpreSub hrestDom
                    (fun _ hk => hk.elim (fun h => .inl ⟨by omega, h.2⟩) (fun h => .inr ⟨by omega, h.2⟩))
                    hchildSubMid
                  exact ⟨hydrateKids_ind (f' + 1) childNs parent pns ptag pst pmg toHtml ItemOk Post hNil hText hElem rest false (pre ++ [child]) domRest mid hi aMid hrestOk
                    (by simp only [List.length_append, List.length_singleton]; simp only [List.length_cons] at hlen; omega)
                    (by simp only [List.map_cons, htmlListNodeCount] at hbound; omega)
                    hrestDep (by omega) hpreMid hparMid (by simpa using hdomMid),
                    hpreMid, hparMid, hdomMid⟩

private theorem hydrateDomKidsM_spec_step {msg : Type} (f : Nat)
    (hDom : ∀ f' < f, @DomHydrateSpecAt msg f') :
    @KidsHydrateSpecAt msg f := by
  intro childNs parent pns ptag pst pmg target inTextRun pre domCs lo hi a hlen hbound hdep hparLo hpreSub hpar hdom
  refine hydrateKids_ind (toHtml := id) (ItemOk := fun _ => True)
    (Post := fun tgt inRun pr lo' hi' a0 =>
      KidsHydrateOut f childNs parent pns ptag pst pmg tgt pr lo' hi' a0
        ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pr.length) inRun tgt).run a0).2)
    f childNs parent pns ptag pst pmg ?_ ?_ ?_ target inTextRun pre domCs lo hi a
    (fun _ _ => trivial) hlen (by simpa using hbound) (by simpa using hdep) hparLo hpreSub hpar (by simpa using hdom)
  · intro _ pr _ _ a0 hpar0
    exact ⟨[], Nat.le_refl _, by simp [hydrateDomKidsM, StateT.run, pure, StateT.pure, htmlListNodeCount],
      by simpa [hydrateDomKidsM, StateT.run, pure, StateT.pure] using hpar0,
      (fun _ hm => nomatch hm), fun _ _ _ _ => rfl, trivial, fun _ => trivial⟩
  · intro c rest inRun inRun' pr tn lo' loRest hi' a0 s aMid S_tn hcEq _ hfPos hloLe haMidLe haMidLe1 hparNe huNext hslotEq hgetNew htnIn hStnSub hStnOut hfrMid hih
    dsimp only [id] at hcEq; subst hcEq; simp only [List.map_id] at hslotEq
    rcases hih with ⟨hydRest, hnextR, hboundR, hparR, hsubR, hfrR, heqR, hclR⟩
    have hstep : ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pr.length) inRun (.text s :: rest)).run a0).2 =
        ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (pr ++ [tn]).length) inRun' rest).run aMid).2 := by
      dsimp only [StateT.run, hydrateDomKidsM, Html.textOf?, bind, StateT.bind]
      rw [hslotEq]; dsimp only; simp only [List.length_append, List.length_singleton]; rw [← huNext]
    have haOutTn : ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (pr ++ [tn]).length) inRun' rest).run aMid).2.get tn = .text s := by
      rw [hfrR tn hparNe.symm (hStnOut tn.toNat htnIn).1 (hStnOut tn.toNat htnIn).2, hgetNew]
    dsimp only [KidsHydrateOut]; rw [hstep]
    cases f with
    | zero => omega
    | succ f' =>
        let aOut := ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (pr ++ [tn]).length) inRun' rest).run aMid).2
        have hSubL : ∀ k, S_tn k → (lo' ≤ k ∧ k < hi') ∨ (a0.nextId ≤ k ∧ k < aOut.nextId) :=
          fun k hk => (hStnSub k hk).imp id fun h => ⟨h.1, Nat.lt_of_lt_of_le h.2 hnextR⟩
        have hSubR : ∀ k, ((loRest ≤ k ∧ k < hi') ∨ (aMid.nextId ≤ k ∧ k < aOut.nextId)) →
            (lo' ≤ k ∧ k < hi') ∨ (a0.nextId ≤ k ∧ k < aOut.nextId) :=
          fun _ hk => hk.elim (fun h => .inl ⟨Nat.le_trans hloLe h.1, h.2⟩) (fun h => .inr ⟨Nat.le_trans haMidLe h.1, h.2⟩)
        refine ⟨tn :: hydRest, Nat.le_trans haMidLe hnextR, by simp only [htmlListNodeCount, htmlNodeCount]; omega,
          by simpa [List.append_assoc] using hparR,
          fun z hz => (List.mem_cons.1 hz).elim (fun h => by subst h; exact ⟨hSubL _ htnIn, by rw [haOutTn]; trivial⟩)
            (fun htail => SubtreeInSet_mono hSubR (hsubR z htail)),
          fun m hmPar hmOut hmLt => by
            rw [hfrR m hmPar (hmOut.elim (fun h1 => .inl (by omega)) .inr) (Nat.lt_of_lt_of_le hmLt haMidLe), hfrMid m hmPar hmOut hmLt],
          by simp only [List.map_cons, specDomList, specDom, DomTreeListAssocEquiv, readDomTree, haOutTn]; exact ⟨rfl, heqR⟩,
          fun hc => by
            simp only [Html.DomCleanList, Html.DomClean, Bool.true_and] at hc
            exact ⟨S_tn, _, hSubL, hSubR,
              fun k hk1 hk2 => by have ⟨ho, hl⟩ := hStnOut k hk1; rcases hk2 with h | h <;> rcases ho with h' | h' <;> omega,
              ⟨htnIn, haOutTn⟩, hclR hc⟩⟩
  · intro c rest inRun pr child domRest lo' mid hi' a0 f' hfEq htxt _ _ _ huIdx huNext hbd' hcDep _ hparLo' hloMid hmidHi hiNext hpar0 hchildDom _ hcont
    subst hfEq; simp only [List.map_id] at hbd'
    rcases textOf_none_is_element htxt with ⟨tag, attrs, kids, hcEq⟩; subst hcEq
    let aMid := (hydrateDomM (m := StateM (DomArena msg)) (.element tag attrs kids) child a0).2
    rcases hDom f' (Nat.lt_succ_self f') childNs (.element tag attrs kids) child a0 lo' mid
        (by simp only [htmlListNodeCount] at hbd'; omega) hcDep hchildDom with
      ⟨haMidNext, haMidBound, hchildSubMid, hframeMid, hequivChild, hchildClMid⟩
    have haMidGe : a0.nextId ≤ aMid.nextId := haMidNext
    have haMidLe : aMid.nextId ≤ a0.nextId + htmlNodeCount (.element tag attrs kids) := haMidBound
    rcases (hcont aMid haMidNext haMidBound hchildSubMid hframeMid).1 with
      ⟨hydRest, hnextR, hboundR, hparR, hsubR, hfrR, heqR, hclR⟩
    have hstep : ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pr.length) inRun (.element tag attrs kids :: rest)).run a0).2 =
        ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (pr ++ [child]).length) false rest).run aMid).2 := by
      dsimp only [StateT.run, hydrateDomKidsM, Html.textOf?, bind, StateT.bind, MonadDom.childAt]
      rw [hpar0, huIdx]; dsimp only; rw [getD_append_right child 0 pr domRest]
      change (hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pr.length + 1) false rest aMid).2 = _
      simp only [List.length_append, List.length_singleton]; rw [← huNext]
    have hfrChild : ∀ m : Dom.Node, ((lo' ≤ m.toNat ∧ m.toNat < mid) ∨ (a0.nextId ≤ m.toNat ∧ m.toNat < aMid.nextId)) →
        ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (pr ++ [child]).length) false rest).run aMid).2.get m = aMid.get m :=
      fun m hm => hfrR m (fun heq => by rw [heq] at hm; rcases hm with h1 | h2 <;> omega)
        (hm.elim (fun h1 => .inl h1.2) (fun h2 => .inr (Nat.le_trans hiNext h2.1)))
        (hm.elim (fun h1 => by omega) (fun h2 => h2.2))
    have haOutChild := SubtreeInSet_frame (n := child) hfrChild hchildSubMid
    let aOut := ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat (pr ++ [child]).length) false rest).run aMid).2
    have hSubL : ∀ k, ((lo' ≤ k ∧ k < mid) ∨ (a0.nextId ≤ k ∧ k < aMid.nextId)) →
        (lo' ≤ k ∧ k < hi') ∨ (a0.nextId ≤ k ∧ k < aOut.nextId) :=
      fun _ hk => hk.elim (fun h => .inl ⟨h.1, Nat.le_trans h.2 hmidHi⟩) (fun h => .inr ⟨h.1, Nat.lt_of_lt_of_le h.2 hnextR⟩)
    have hSubR : ∀ k, ((mid ≤ k ∧ k < hi') ∨ (aMid.nextId ≤ k ∧ k < aOut.nextId)) →
        (lo' ≤ k ∧ k < hi') ∨ (a0.nextId ≤ k ∧ k < aOut.nextId) :=
      fun _ hk => hk.elim (fun h => .inl ⟨Nat.le_trans hloMid h.1, h.2⟩) (fun h => .inr ⟨Nat.le_trans haMidGe h.1, h.2⟩)
    dsimp only [KidsHydrateOut]; rw [hstep]
    refine ⟨child :: hydRest, Nat.le_trans haMidGe hnextR, by simp only [htmlListNodeCount]; omega,
      by simpa [List.append_assoc] using hparR,
      fun z hz => (List.mem_cons.1 hz).elim (fun h => by subst h; exact SubtreeInSet_mono hSubL haOutChild.1)
        (fun htail => SubtreeInSet_mono hSubR (hsubR z htail)),
      fun m hmPar hmOut hmLt =>
        (hfrR m hmPar (hmOut.elim (fun h1 => .inl (by omega)) .inr) (by omega)).trans
          (hframeMid m (hmOut.elim .inl (fun h2 => .inr (Nat.le_trans hmidHi h2))) hmLt),
      by simp only [List.map_cons, specDomList, DomTreeListAssocEquiv, haOutChild.2]; exact ⟨hequivChild, heqR⟩,
      fun hc => by
        simp only [Html.DomCleanList, Bool.and_eq_true] at hc
        exact ⟨_, _, hSubL, hSubR, fun _ hk1 hk2 => by rcases hk1 with h1 | h1 <;> rcases hk2 with h2 | h2 <;> omega,
          CleanDomSubtree_frame hfrChild (hchildClMid hc.1), hclR hc.2⟩⟩

theorem hydrateElemAttrs_step {msg : Type} (a : DomArena msg) (root : Dom.Node)
    (ns tag : String) (st : SpecElemState msg) (prev : List String) (domCs : List Dom.Node)
    (attrs : List (Attr msg))
    (hget : a.get root = .element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag st prev domCs)
    (hm : ElemManaged ({ st with clicks := [], inputs := [] } : SpecElemState msg) prev)
    (hns : AttrsNoShadow attrs ({ st with clicks := [], inputs := [] } : SpecElemState msg)) :
    let aClear := a.modifyElemState root (fun st : SpecElemState msg => { st with clicks := [], inputs := [] })
    let a2 := (applyAttrsM (m := StateM (DomArena msg)) root attrs aClear).2
    ∃ st', a2.get root = .element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag st'
        ((normalizeAttrs attrs).filterMap managedAttrName) domCs ∧
      ElemStateEquiv st' (evalSpecAttrs attrs) ∧
      ElemManaged st' ((normalizeAttrs attrs).filterMap managedAttrName) ∧
      a2.nextId = a.nextId ∧ (∀ m : Dom.Node, m ≠ root → a2.get m = a.get m) := by
  have hclear : a.modifyElemState root (fun st : SpecElemState msg => { st with clicks := [], inputs := [] }) =
      a.set root (.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
        { st with clicks := [], inputs := [] } prev domCs) := by simp [DomArena.modifyElemState, DomArena.modify, hget]
  rcases applyAttrsM_existing_element a root (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
      { st with clicks := [], inputs := [] } prev domCs attrs hm hns with ⟨st', ha2Get, ha2Eqv, hm'⟩
  have ⟨ha2Next, ha2Out⟩ := applyAttrsM_preserves
    (a.set root (.element (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag
      { st with clicks := [], inputs := [] } prev domCs)) root attrs
  dsimp only; rw [hclear]
  exact ⟨st', ha2Get, ha2Eqv, hm', ha2Next, fun m hne => (ha2Out m hne).trans (DomArena.get_set_ne _ _ hne)⟩

private theorem hydrateDomM_spec_strong (f : Nat) : @DomHydrateSpecAt msg f := by
  induction f using Nat.strongRecOn with
  | ind f ihDom =>
      intro ns h root a lo hi hbound hdep hdom
      cases h with
      | text s =>
          rcases hdom with ⟨hlo, hhi, hnext, hget⟩
          simp only [DomHydrateOut, hydrateDomM, StateT.run, pure, StateT.pure]
          refine ⟨Nat.le_refl _, by simp [htmlNodeCount], ⟨.inl ⟨hlo, hhi⟩, by simp [hget]⟩,
            fun _ _ _ => trivial, by simp [readDomTree, hget, specDom, DomTreeAssocEquiv],
            fun _ => ⟨.inl ⟨hlo, hhi⟩, hget⟩⟩
      | element tag attrs cs =>
          rcases hdom with ⟨hlo, hhi, hnext, st, prev, domCs, hget, hm, hns, hownT, hownF⟩
          let a2 := (applyAttrsM (m := StateM (DomArena msg)) root attrs
            (a.modifyElemState root fun st => { st with clicks := [], inputs := [] })).2
          rcases hydrateElemAttrs_step a root ns tag st prev domCs attrs hget hm hns with
            ⟨st', ha2Get, ha2Eqv, hm', ha2Next, ha2Outside⟩
          have ha2Next' : a2.nextId = a.nextId := ha2Next
          have hpreBind : ((hydrateDomM (m := StateM (DomArena msg)) (.element tag attrs cs) root).run a).2 =
              if !ownsChildren attrs then ((hydrateDomKidsM (m := StateM (DomArena msg)) root 0 false cs).run a2).2 else a2 := by
            dsimp only [hydrateDomM, StateT.run, bind, StateT.bind, pure, StateT.pure, MonadDom.clearHandlers]
            cases ownsChildren attrs <;> rfl
          dsimp only [DomHydrateOut]; rw [hpreBind]
          cases hown : ownsChildren attrs with
          | true =>
              simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              have hdomNil : domCs = [] := hownT hown; subst hdomNil
              refine ⟨by omega, by simp only [htmlNodeCount]; omega,
                ⟨.inl ⟨hlo, hhi⟩, by rw [ha2Get]; intro _ hc; nomatch hc⟩,
                fun m hmOut _ => ha2Outside m (fun heq => by rw [heq] at hmOut; omega),
                by dsimp only [readDomTree, specDom]; rw [ha2Get, hown]; exact ⟨rfl, rfl, ha2Eqv, trivial⟩,
                fun hc => by simp [Html.DomClean, hown] at hc⟩
          | false =>
              simp only [Bool.not_false, ↓reduceIte]
              rcases hownF hown with ⟨mid, hmidGt, hk⟩
              have hkFrame := HydratableDomList_frame f (Dom.childNsOf ns tag) (coalesceTextRun cs) a a2 mid hi domCs
                (by omega) (fun m hm1 _ => ha2Outside m (fun heq => by rw [heq] at hm1; omega)) hk
              have hkidsRun := hydrateDomKidsM_spec_step f ihDom (Dom.childNsOf ns tag) root
                (if ns == "" && tag == "svg" then Dom.svgNs else ns) tag st'
                ((normalizeAttrs attrs).filterMap managedAttrName) cs false [] domCs mid hi a2
                (by have := list_length_le_htmlListNodeCount cs; simp only [htmlNodeCount] at hbound; simp; omega)
                (by simp only [htmlNodeCount] at hbound; omega) (by simp only [htmlDepth] at hdep; omega)
                hmidGt (fun _ hm => nomatch hm) ha2Get hkFrame
              simp only [List.length_nil, show (UInt32.ofNat 0 : UInt32) = 0 from rfl] at hkidsRun
              rcases hkidsRun with ⟨hydratedCs, hnextLe, hnextBound, hgetOut, hsubSet, hframeKids, hequivKids, hcleanKids⟩
              refine ⟨by omega, by simp only [htmlNodeCount]; omega, ?_, ?_, ?_, ?_⟩
              · refine ⟨.inl ⟨hlo, hhi⟩, ?_⟩; rw [hgetOut]
                exact fun c hc => SubtreeInSet_mono (fun _ hkS => hkS.elim (fun h => .inl ⟨by omega, h.2⟩) (fun h => .inr ⟨by omega, h.2⟩)) (hsubSet c hc)
              · intro m hmOut hmLt
                have hne : m ≠ root := fun heq => by rw [heq] at hmOut; omega
                rw [hframeKids m hne (hmOut.elim (fun h1 => .inl (by omega)) .inr) (by omega), ha2Outside m hne]
              · dsimp only [readDomTree, specDom]; rw [hgetOut, hown]; exact ⟨rfl, rfl, ha2Eqv, hequivKids⟩
              · intro hc
                simp only [Html.DomClean, hown, Bool.not_false, Bool.true_and, Bool.and_eq_true] at hc
                exact ⟨.inl ⟨hlo, hhi⟩, hown, hc.1, st', (normalizeAttrs attrs).filterMap managedAttrName, hydratedCs,
                  hgetOut, ⟨hm', fun k hk => (SlotVal.optStr.inj (ha2Eqv (.attr k))).trans ((ElemClean_evalSpecAttrs hc.1).2 k hk)⟩,
                  ha2Eqv, fun nm hnm => List.contains_iff_mem.2 hnm,
                  CleanDomChildren_mono (fun _ hkS => hkS.elim (fun h => ⟨.inl ⟨by omega, h.2⟩, by omega⟩) (fun h => ⟨.inr ⟨by omega, h.2⟩, by omega⟩)) (hcleanKids hc.2)⟩

/-- Imperative HTML5 hydration simulation for `hydrateDomM`:
    given an SSR-parsed `HydratableDom` tree whose text children were coalesced by the HTML5 parser
    (`coalesceTextRun`), `hydrateDomM` preserves outside nodes and makes `readDomTree (f + 1) aOut root`
    match `specDom ns h` via `DomTreeAssocEquiv`, producing `CleanDomSubtree` whenever `h.DomClean`. -/
theorem hydrateDomM_spec {msg : Type} (ns : String)
    (f : Nat) (h : Html msg) (root : Dom.Node) (a : DomArena msg) (lo hi : Nat)
    (hbound : a.nextId + htmlNodeCount h < UInt32.size) (hdep : htmlDepth h ≤ f + 1)
    (hdom : HydratableDom (f + 1) ns h a lo hi root) :
    DomHydrateOut f ns h root a lo hi ((hydrateDomM (m := StateM (DomArena msg)) h root).run a).2 :=
  hydrateDomM_spec_strong f ns h root a lo hi hbound hdep hdom

/-- Imperative child-list HTML5 hydration simulation for `hydrateDomKidsM`:
    interpolates `hydrateTextSlotM` and recursive `hydrateDomM` calls across `target`, keeping child
    subtrees disjoint and producing `DomTreeListAssocEquiv` against `specDomList` and `CleanDomChildren`. -/
theorem hydrateDomKidsM_spec {msg : Type} (childNs : String) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (f : Nat) (target : List (Html msg)) (inTextRun : Bool)
    (pre domCs : List Dom.Node) (lo hi : Nat) (a : DomArena msg)
    (hlen : pre.length + target.length < UInt32.size) (hbound : a.nextId + htmlListNodeCount target < UInt32.size)
    (hdep : htmlListDepth target ≤ f) (hparLo : parent.toNat < lo)
    (hpreSub : ∀ x ∈ pre, ∃ Sx, (∀ k, Sx k → (parent.toNat < k ∧ k < lo) ∨ (hi ≤ k ∧ k < a.nextId)) ∧ SubtreeInSet f a Sx x)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ domCs))
    (hdom : HydratableDomList f childNs (if inTextRun then dropCurrentTextRun target else coalesceTextRun target) a lo hi domCs) :
    KidsHydrateOut f childNs parent pns ptag pst pmg target pre lo hi a
      ((hydrateDomKidsM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) inTextRun target).run a).2 :=
  hydrateDomKidsM_spec_step f (fun f' _ => hydrateDomM_spec_strong f') childNs parent pns ptag pst pmg
    target inTextRun pre domCs lo hi a hlen hbound hdep hparLo hpreSub hpar hdom

end Qed
