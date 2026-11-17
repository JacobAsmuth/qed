import Qed.Proofs.DomArena

namespace Qed

/-! ## Pure Diff & W3C `insertBefore` Keyed/Positional Reconciler Equivalence -/

theorem insertBeforeRef_split {child ref : Dom.Node} :
    ∀ (pre suf : List Dom.Node),
      ref ∉ pre →
      insertBeforeRef child ref (pre ++ ref :: suf) = pre ++ child :: ref :: suf
  | [], suf, _ => by simp [insertBeforeRef]
  | x :: xs, suf, href => by
      have hne : (x == ref) = false := beq_eq_false_iff_ne.2 (fun h => href (by simp [h]))
      simp [insertBeforeRef, hne, insertBeforeRef_split xs suf (fun h => href (List.mem_cons_of_mem x h))]

theorem erase_append_right_of_not_mem {α : Type} [BEq α] [LawfulBEq α]
    (pre suf : List α) {x : α} (hnot : x ∉ pre) :
    (pre ++ suf).erase x = pre ++ suf.erase x := by
  induction pre with
  | nil => rfl
  | cons a rest ih =>
      have hne : (a == x) = false := beq_eq_false_iff_ne.2 (fun h => hnot (by simp [h]))
      simp [hne, ih (fun h => hnot (List.mem_cons_of_mem a h))]

private theorem not_mem_left_of_nodup_append {α : Type} {xs ys : List α} {y : α}
    (hnd : (xs ++ ys).Nodup) (hy : y ∈ ys) : y ∉ xs := by
  induction xs with
  | nil => intro h; nomatch h
  | cons x rest ih =>
      rcases List.nodup_cons.1 hnd with ⟨hx, hrest⟩
      intro hm
      rcases List.mem_cons.1 hm with rfl | htail
      · exact hx (List.mem_append_right rest hy)
      · exact ih hrest htail

private theorem nodup_erase {α : Type} [BEq α] [LawfulBEq α] {xs : List α} (x : α)
    (hnd : xs.Nodup) : (xs.erase x).Nodup := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
      rcases List.nodup_cons.1 hnd with ⟨ha, hrest⟩
      by_cases hax : a == x
      · simpa [List.erase_cons, hax] using hrest
      · simp only [List.erase_cons, hax, Bool.false_eq_true, ↓reduceIte]
        refine List.nodup_cons.2 ⟨fun hm => ha (List.mem_of_mem_erase hm), ih hrest⟩

private theorem nodup_reinsert {α : Type} [BEq α] [LawfulBEq α] {pre suf : List α} {c : α}
    (hnd : (pre ++ suf).Nodup) (hc : c ∉ pre) :
    (pre ++ c :: suf.erase c).Nodup := by
  induction pre with
  | nil =>
      simp only [List.nil_append] at hnd ⊢
      refine List.nodup_cons.2 ⟨?_, nodup_erase c hnd⟩
      -- Since `suf.Nodup`, erasing `c` removes the only possible occurrence of `c` in `suf`.
      clear hc
      induction suf with
      | nil => simp
      | cons s srest ihS =>
          rcases List.nodup_cons.1 hnd with ⟨hs, hsrest⟩
          by_cases hsc : s == c
          · have heq : s = c := eq_of_beq hsc
            subst heq
            simpa [List.erase_cons] using hs
          · simp only [List.erase_cons, hsc, Bool.false_eq_true, ↓reduceIte, List.mem_cons, not_or]
            refine ⟨fun h => hsc (beq_iff_eq.2 h.symm), ihS hsrest⟩
  | cons p prest ih =>
      simp only [List.cons_append] at hnd ⊢
      rcases List.nodup_cons.1 hnd with ⟨hp, hprest⟩
      have hcp : c ≠ p := fun h => hc (by simp [h])
      refine List.nodup_cons.2 ⟨?_, ih hprest (fun h => hc (List.mem_cons_of_mem p h))⟩
      intro hm
      rcases List.mem_append.1 hm with h1 | h2
      · exact hp (List.mem_append_left _ h1)
      · rcases List.mem_cons.1 h2 with hpeq | her
        · exact hcp hpeq.symm
        · exact hp (List.mem_append_right _ (List.mem_of_mem_erase her))

/-- Unified W3C `insertBefore` step theorem: whether `child` is freshly created (`child ∉ suf`)
    or reused from `suf` (`child ∈ suf`), as long as `(pre ++ suf).Nodup` and `child ∉ pre`,
    `w3cInsertBefore (pre ++ suf) pre.length child = pre ++ child :: suf.erase child`. -/
theorem w3cInsertBefore_step (pre suf : List Dom.Node) (child : Dom.Node)
    (hnd : (pre ++ suf).Nodup) (hnotPre : child ∉ pre) :
    w3cInsertBefore (pre ++ suf) pre.length child = pre ++ child :: suf.erase child := by
  unfold w3cInsertBefore
  rw [List.drop_left]
  cases suf with
  | nil =>
      simp [List.erase_of_not_mem hnotPre]
  | cons ref rest =>
      by_cases hrc : ref == child
      · have heq : ref = child := eq_of_beq hrc
        subst heq
        simp
      · simp only [hrc, Bool.false_eq_true, ↓reduceIte]
        rw [erase_append_right_of_not_mem pre (ref :: rest) hnotPre]
        have hrc' : (ref == child) = false := Bool.eq_false_iff.2 hrc
        simp only [List.erase_cons, hrc', Bool.false_eq_true, ↓reduceIte]
        have hrefNotPre : ref ∉ pre := not_mem_left_of_nodup_append hnd (List.mem_cons_self ..)
        exact insertBeforeRef_split pre (rest.erase child) hrefNotPre

def w3cPlaceSeq : List Dom.Node → Nat → List Dom.Node → List Dom.Node
  | cs, _, [] => cs
  | cs, j, target :: rest => w3cPlaceSeq (w3cInsertBefore cs j target) (j + 1) rest

theorem w3cPlaceSeq_invariant (targets : List Dom.Node) :
    ∀ (pre suf : List Dom.Node),
      (pre ++ suf).Nodup →
      targets.Nodup →
      (∀ t ∈ targets, t ∉ pre) →
      ∃ rem,
        w3cPlaceSeq (pre ++ suf) pre.length targets = pre ++ targets ++ rem := by
  induction targets with
  | nil =>
      intro pre suf _ _ _
      exact ⟨suf, by simp [w3cPlaceSeq]⟩
  | cons t rest ih =>
      intro pre suf hnd htnd hdisj
      rcases List.nodup_cons.1 htnd with ⟨htRest, hrestNd⟩
      have htNotPre : t ∉ pre := hdisj t (List.mem_cons_self ..)
      have hstep := w3cInsertBefore_step pre suf t hnd htNotPre
      have hnd' : ((pre ++ [t]) ++ suf.erase t).Nodup := by
        simpa [List.append_assoc] using nodup_reinsert hnd htNotPre
      have hdisj' : ∀ r ∈ rest, r ∉ pre ++ [t] := by
        intro r hr hm
        rcases List.mem_append.1 hm with h1 | h2
        · exact hdisj r (List.mem_cons_of_mem t hr) h1
        · simp only [List.mem_singleton] at h2
          subst h2
          exact htRest hr
      have hlen' : (pre ++ [t]).length = pre.length + 1 := by simp
      rcases ih (pre ++ [t]) (suf.erase t) hnd' hrestNd hdisj' with ⟨rem, heq⟩
      refine ⟨rem, ?_⟩
      simp only [w3cPlaceSeq, hstep]
      have hassoc : pre ++ t :: suf.erase t = (pre ++ [t]) ++ suf.erase t := by simp
      rw [hassoc, ← hlen', heq]
      simp [List.append_assoc]

/-- Complete keyed child-order reconciliation theorem: placing any duplicate-free `targets` sequence
    via W3C `insertBefore` over an existing duplicate-free `live` child list and removing the
    trailing unused suffix yields `targets` in exact order. -/
theorem w3cReconcileKeyed_eq (live targets : List Dom.Node)
    (hlive : live.Nodup) (htargets : targets.Nodup) :
    let placed := w3cPlaceSeq live 0 targets
    removeTailSpec targets.length (placed.length - targets.length) placed = targets := by
  rcases w3cPlaceSeq_invariant targets [] live (by simpa using hlive) htargets
    (fun _ _ h => nomatch h) with ⟨rem, hplaced⟩
  dsimp only
  simp only [List.nil_append, List.length_nil] at hplaced
  rw [hplaced]
  have hsub : (targets ++ rem).length - targets.length = rem.length := by simp
  rw [hsub]
  exact removeTailSpec_append targets rem


/-! ## 8. Keyed/Positional Child Reconciliation & Hydration Simulation on `DomArena` -/

private theorem getElem?_getD_of_lt {α : Type} (xs : List α) (i : Nat) (d : α) (h : i < xs.length) :
    xs[i]?.getD d = xs[i] := by
  simp [List.getElem?_eq_getElem h]

private theorem drop_getElem_cons {α : Type} :
    ∀ (xs : List α) (i : Nat) (h : i < xs.length), xs.drop i = xs[i] :: xs.drop (i + 1)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: rest, i + 1, h => drop_getElem_cons rest i (Nat.lt_of_succ_lt_succ h)



theorem snapshotChildrenM_spec (a : DomArena msg) (node : Dom.Node) (pns ptag : String)
    (pst : SpecElemState msg) (pmg : List String) (cs : List Dom.Node)
    (hsize : cs.length < UInt32.size) :
    ∀ (i rem : Nat) (acc : Array Dom.Node),
      i + rem = cs.length →
      (snapshotChildrenM (m := StateM (DomArena msg)) node i acc rem).run
        (a.set node (.element pns ptag pst pmg cs)) =
        (⟨acc.toList ++ cs.drop i⟩, a.set node (.element pns ptag pst pmg cs)) := by
  intro i rem
  induction rem generalizing i with
  | zero =>
      intro acc hsum
      have hi : i = cs.length := by omega
      subst hi
      cases acc with
      | mk data => simp [snapshotChildrenM, StateT.run, pure, StateT.pure]
  | succ r ih =>
      intro acc hsum
      have hlt : i < cs.length := by omega
      have hu : (UInt32.ofNat i).toNat = i := uint32_toNat_ofNat_lt i (by omega)
      have hchildAt :
          (MonadDom.childAt (m := StateM (DomArena msg)) node (UInt32.ofNat i)).run
            (a.set node (.element pns ptag pst pmg cs)) =
            (cs[i], a.set node (.element pns ptag pst pmg cs)) := by
        simp [MonadDom.childAt, StateT.run, DomArena.get_set_self, hu, getElem?_getD_of_lt cs i 0 hlt]
      have hdrop : cs.drop i = cs[i] :: cs.drop (i + 1) := drop_getElem_cons cs i hlt
      dsimp only [snapshotChildrenM, StateT.run, bind, StateT.bind]
      change (match (MonadDom.childAt (m := StateM (DomArena msg)) node (UInt32.ofNat i)).run
                (a.set node (.element pns ptag pst pmg cs)) with
              | (child, s') =>
                (snapshotChildrenM (m := StateM (DomArena msg)) node (i + 1) (acc.push child) r).run s') = _
      rw [hchildAt]
      dsimp only
      rw [ih (i + 1) (acc.push cs[i]) (by omega)]
      simp only [Array.toList_push, List.append_assoc, List.singleton_append, hdrop]


/-- Abstract specification for a single in-place child patch step in `applyPositionalStepsM` /
    `applyKeyedStepsM`: running `applyToDomM parent j child p` leaves `parent` and all
    existing nodes `< aIn.nextId` outside `[lo, hi)` untouched, keeps `aIn.nextId ≤ aOut.nextId ≤ aIn.nextId + htmlNodeCount target`,
    and updates `child` (inside `[lo, hi) ∪ [aIn.nextId, aOut.nextId)`) so `readDomTree fuel aOut child = specDom childNs target`. -/
def InPlaceChildPatchSpec (fuel : Nat) (childNs : String) (parent : Dom.Node) (j : UInt32)
    (child : Dom.Node) (p : Patch msg) (target : Html msg)
    (lo hi : Nat) (aIn aOut : DomArena msg) : Prop :=
  ((applyToDomM (m := StateM (DomArena msg)) parent j child p).run aIn).2 = aOut ∧
  aIn.nextId ≤ aOut.nextId ∧
  aOut.nextId ≤ aIn.nextId + htmlNodeCount target ∧
  (∀ m : Dom.Node, (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < aIn.nextId → aOut.get m = aIn.get m) ∧
  SubtreeInSet fuel aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (aIn.nextId ≤ k ∧ k < aOut.nextId)) child ∧
  readDomTree fuel aOut child = specDom childNs target

theorem InPlaceChildPatchSpec_setText (a : DomArena msg) (parent child : Dom.Node) (idx : UInt32)
    (sOld sNew : String) (childNs : String) (fuel : Nat) (hf : 0 < fuel)
    (hlo : child.toNat < a.nextId) :
    InPlaceChildPatchSpec fuel childNs parent idx child (.setText sNew) (.text sNew)
      child.toNat (child.toNat + 1) (a.set child (.text sOld))
      ((applyToDomM (m := StateM (DomArena msg)) parent idx child (.setText sNew)).run
        (a.set child (.text sOld))).2 := by
  have hget : ((applyToDomM (m := StateM (DomArena msg)) parent idx child (.setText sNew)).run
      (a.set child (.text sOld))).2 = a.set child (.text sNew) := by
    simp [applyToDomM, StateT.run, MonadDom.setText, DomArena.modify, DomArena.get_set_self, DomArena.set_set]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hget]
  · simp [hget, htmlNodeCount]
  · intro m hm _; simp only [hget]
    have hne : m ≠ child := by intro heq; subst heq; omega
    simp [DomArena.get_set_ne _ _ hne]
  · simp only [hget]
    cases fuel with
    | zero => omega
    | succ f =>
        refine ⟨.inl ⟨Nat.le_refl _, by omega⟩, ?_⟩
        simp [DomArena.get_set_self]
  · simp only [hget]
    cases fuel with
    | zero => omega
    | succ f => simp [readDomTree, DomArena.get_set_self, specDom]

theorem w3cInsertBefore_fresh_append (pre suf : List Dom.Node) (cn : Dom.Node)
    (hnot : cn ∉ pre ++ suf) (hdisj : ∀ r ∈ suf, r ∉ pre) :
    w3cInsertBefore (pre ++ suf) pre.length cn = pre ++ cn :: suf := by
  unfold w3cInsertBefore
  rw [List.drop_left, List.erase_of_not_mem hnot]
  cases suf with
  | nil => simp
  | cons ref rest =>
      have hne : ref ≠ cn := fun h => hnot (by simp [h])
      have hrc : (ref == cn) = false := beq_eq_false_iff_ne.2 hne
      simp only [hrc, Bool.false_eq_true, ↓reduceIte]
      exact insertBeforeRef_split pre rest (hdisj ref (List.mem_cons_self ..))

theorem keyed_step_insertBefore_create (pre suf : List Dom.Node) (cn : Dom.Node)
    (hnd : (pre ++ suf).Nodup) (hnot : cn ∉ pre ++ suf) :
    w3cInsertBefore (pre ++ suf) pre.length cn = pre ++ cn :: suf := by
  have hnotPre : cn ∉ pre := fun h => hnot (List.mem_append_left _ h)
  have hnotSuf : cn ∉ suf := fun h => hnot (List.mem_append_right _ h)
  rw [w3cInsertBefore_step pre suf cn hnd hnotPre, List.erase_of_not_mem hnotSuf]

theorem positional_step_reuse_tail {msg : Type} (parent : Dom.Node) (pns ptag : String)
    (pst : SpecElemState msg) (pmg : List String)
    (pre : List Dom.Node) (hd : Dom.Node) (tl : List Dom.Node) (a : DomArena msg) :
    pre.length < UInt32.size →
    (MonadDom.childAt (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length)).run
      (a.set parent (.element pns ptag pst pmg (pre ++ hd :: tl))) =
      (hd, a.set parent (.element pns ptag pst pmg (pre ++ hd :: tl))) := by
  intro hlt
  have hu : (UInt32.ofNat pre.length).toNat = pre.length := uint32_toNat_ofNat_lt pre.length hlt
  simp [MonadDom.childAt, StateT.run, DomArena.get_set_self, hu]

theorem positional_removeTail_spec {msg : Type} (a : DomArena msg) (parent : Dom.Node)
    (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (targets rem : List Dom.Node) (hlen : targets.length + rem.length < UInt32.size) :
    ((MonadDom.childCount (m := StateM (DomArena msg)) parent >>= fun count =>
      removeTailM (m := StateM (DomArena msg)) parent (UInt32.ofNat targets.length)
        (count.toNat - targets.length)).run
      (a.set parent (.element pns ptag pst pmg (targets ++ rem)))).2 =
      a.set parent (.element pns ptag pst pmg targets) := by
  have hc : (targets ++ rem).length < UInt32.size := by simp; omega
  have huCount : (UInt32.ofNat (targets ++ rem).length).toNat = targets.length + rem.length := by
    rw [uint32_toNat_ofNat_lt _ hc]; simp
  have huAt : (UInt32.ofNat targets.length).toNat = targets.length :=
    uint32_toNat_ofNat_lt targets.length (by omega)
  dsimp only [bind, StateT.bind, StateT.run, MonadDom.childCount]
  rw [DomArena.get_set_self]
  dsimp only
  rw [huCount, Nat.add_sub_cancel_left]
  have hr := removeTailM_spec a parent targets.length rem.length pns ptag pst pmg (targets ++ rem)
  dsimp only [StateT.run] at hr
  rw [hr, huAt, removeTailSpec_append]

/-- Tracked DOM child state for `applyPositionalStepsM` / `applyKeyedStepsM`: pairs each placed
    child node with its disjoint node predicate `S : Nat → Prop` inside `[parent+1, a.nextId)`. -/
def DisjointDomSetChild {msg : Type} (fuel : Nat) (parent : Dom.Node) (a : DomArena msg)
    (n : Dom.Node) (S : Nat → Prop) : Prop :=
  (∀ k, S k → parent.toNat < k ∧ k < a.nextId) ∧ SubtreeInSet fuel a S n

/-- Inductive well-formedness plan for `applyKeyedStepsM`: pairs every step with its target `Html`
    and disjoint base-arena intervals `used` strictly inside `[parent+1, baseLimit)`. -/
def KeyedStepPlanOk {msg : Type} (fuel : Nat) (childNs : String) (parent : Dom.Node)
    (live : Array Dom.Node) (baseLimit : Nat) :
    Nat → List (KeyedStep msg) → List (Html msg) → List Dom.Node →
      List (Nat × Nat) → Prop
  | _, [], [], _, _ => True
  | j, .create newH :: sRest, t :: tRest, suf, used =>
      newH = t ∧
      KeyedStepPlanOk fuel childNs parent live baseLimit (j + 1) sRest tRest suf used
  | j, .reuse oldIdx p :: sRest, t :: tRest, suf, used =>
      oldIdx < live.size ∧
      let c := live[oldIdx]!
      c ∈ suf ∧
      (∃ lo hi, parent.toNat < lo ∧ lo ≤ c.toNat ∧ c.toNat < hi ∧ hi ≤ baseLimit ∧
        (∀ iv ∈ used, iv.2 ≤ lo ∨ hi ≤ iv.1) ∧
        (∀ aCur : DomArena msg, hi ≤ aCur.nextId →
          InPlaceChildPatchSpec fuel childNs parent (UInt32.ofNat j) c p t lo hi aCur
            ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat j) c p).run aCur).2) ∧
        KeyedStepPlanOk fuel childNs parent live baseLimit (j + 1) sRest tRest (suf.erase c)
          (used ++ [(lo, hi)]))
  | _, _, _, _, _ => False

private theorem keyed_placed_old_frame {msg : Type} {fuel : Nat} {parent : Dom.Node}
    {a a' : DomArena msg} {d : Dom.Node × (Nat → Prop)}
    (hbound : a.nextId ≤ a'.nextId)
    (hdisj : DisjointDomSetChild fuel parent a d.1 d.2)
    (hfr : ∀ m : Dom.Node, d.2 m.toNat → m ≠ parent → a'.get m = a.get m) :
    DisjointDomSetChild fuel parent a' d.1 d.2 ∧
    readDomTree fuel a' d.1 = readDomTree fuel a d.1 := by
  rcases hdisj with ⟨hdB, hdSub⟩
  have hres := SubtreeInSet_frame (a := a) (a' := a') (S := d.2) (n := d.1)
    (fun m hm => hfr m hm (by intro heq; subst heq; have := (hdB m.toNat hm).1; omega)) hdSub
  exact ⟨⟨fun k hk => ⟨(hdB k hk).1, Nat.lt_of_lt_of_le (hdB k hk).2 hbound⟩, hres.1⟩, hres.2⟩

/-- Inductive `applyKeyedStepsM` simulation theorem on `DomArena`:
    executes W3C `insertBefore` placement (`w3cInsertBefore`) + `InPlaceChildPatchSpec` /
    `buildDomM` over `steps`, placing exact child prefix `targetsOut ++ sufRem` on `parent` whose
    `targetsOut.map (readDomTree fuel aOut)` equals `specDomList childNs targets`. -/
theorem applyKeyedStepsM_reconcile_spec {msg : Type} (parent : Dom.Node) (pns ptag : String)
    (pst : SpecElemState msg) (pmg : List String) (live : Array Dom.Node)
    (fuel : Nat) (childNs : String) (baseLimit : Nat)
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") :
    ∀ (steps : List (KeyedStep msg)) (targets : List (Html msg))
      (pre suf : List Dom.Node) (used : List (Nat × Nat))
      (placed : List (Dom.Node × (Nat → Prop))) (a : DomArena msg),
      steps.length = targets.length →
      placed.map Prod.fst = pre →
      pre.length + suf.length + steps.length < UInt32.size →
      baseLimit ≤ a.nextId →
      a.nextId + htmlListNodeCount targets < UInt32.size →
      htmlListDepth targets ≤ fuel →
      parent.toNat < a.nextId →
      0 < a.nextId →
      a.get parent = .element pns ptag pst pmg (pre ++ suf) →
      (pre ++ suf).Nodup →
      (∀ d ∈ placed, DisjointDomSetChild fuel parent a d.1 d.2) →
      (∀ d ∈ placed, ∀ k, d.2 k → k < baseLimit → ∃ iv ∈ used, iv.1 ≤ k ∧ k < iv.2) →
      (∀ r ∈ suf, r.toNat < a.nextId ∧ r ≠ parent) →
      KeyedStepPlanOk fuel childNs parent live baseLimit pre.length steps targets suf used →
      let (finalJ, aOut) := (applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat pre.length) steps).run a
      ∃ (targetsOut sufRem : List Dom.Node) (placedOut : List (Dom.Node × (Nat → Prop))),
        finalJ.toNat = pre.length + steps.length ∧
        targetsOut.length = steps.length ∧
        sufRem.length ≤ suf.length ∧
        aOut.nextId ≤ a.nextId + htmlListNodeCount targets ∧
        aOut.get parent = .element pns ptag pst pmg ((pre ++ targetsOut) ++ sufRem) ∧
        placedOut.map Prod.fst = pre ++ targetsOut ∧
        (∀ d ∈ placedOut, DisjointDomSetChild fuel parent aOut d.1 d.2) ∧
        (pre ++ targetsOut).map (readDomTree fuel aOut) =
          pre.map (readDomTree fuel a) ++ specDomList childNs targets := by
  intro steps
  induction steps with
  | nil =>
      intro targets pre suf used placed a hlen hpm hsz hbase hbound hdep hparLt hpos hget hnd hplaced hmatch hsuf hplan
      cases targets with
      | cons _ _ => simp at hlen
      | nil =>
          refine ⟨[], suf, placed, ?_, rfl, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_⟩
          · simp [uint32_toNat_ofNat_lt pre.length (by simp at hsz; omega)]
          · simp [htmlListNodeCount]
          · simpa [applyKeyedStepsM, StateT.run, pure] using hget
          · simp [hpm]
          · simpa [applyKeyedStepsM, StateT.run, pure] using hplaced
          · simp [specDomList]
  | cons step sRest ih =>
      intro targets pre suf used placed a hlen hpm hsz hbase hbound hdep hparLt hpos hget hnd hplaced hmatch hsuf hplan
      simp only [List.length_cons] at hsz hlen
      cases targets with
      | nil => simp at hlen
      | cons t tRest =>
          simp only [List.length_cons] at hlen
          have hlen' : sRest.length = tRest.length := Nat.succ.inj hlen
          cases step with
          | create newH =>
              simp only [KeyedStepPlanOk] at hplan
              rcases hplan with ⟨hnewEq, hrestPlan⟩
              subst hnewEq
              simp only [htmlListNodeCount] at hbound
              simp only [htmlListDepth] at hdep
              have htDep : htmlDepth newH ≤ fuel := Nat.le_trans (Nat.le_max_left _ _) hdep
              have hrestDep : htmlListDepth tRest ≤ fuel := Nat.le_trans (Nat.le_max_right _ _) hdep
              have hchildNsRun : (MonadDom.childNamespace (m := StateM (DomArena msg)) parent).run a =
                  (childNs, a) := by
                simp [MonadDom.childNamespace, StateT.run, hget, hchildNs]
              have hbuild := buildDomM_spec childNs newH a fuel hpos (by omega) htDep
              dsimp only [StateT.run] at hbuild
              rcases hbuild with ⟨hcnGe, hcnLt, haMidLe, haMidFrame, hcnSub, hcnRead⟩
              let resB := buildDomM (m := StateM (DomArena msg)) childNs newH a
              let cn := resB.1
              let aMid := resB.2
              have hcnDef : (buildDomM (m := StateM (DomArena msg)) childNs newH a).1 = cn := rfl
              have haMidDef : (buildDomM (m := StateM (DomArena msg)) childNs newH a).2 = aMid := rfl
              rw [hcnDef] at hcnGe hcnLt hcnSub hcnRead
              rw [haMidDef] at hcnLt haMidLe haMidFrame hcnSub hcnRead
              have hparMid : aMid.get parent = .element pns ptag pst pmg (pre ++ suf) := by
                rw [haMidFrame parent hparLt, hget]
              have hcnNotIn : cn ∉ pre ++ suf := by
                intro hmem
                have hfuelPos : 1 ≤ fuel := by
                  have : 1 ≤ htmlDepth newH := by cases newH <;> simp [htmlDepth]
                  omega
                rcases List.mem_append.1 hmem with hpre | hs
                · rcases List.mem_map.1 (by rw [hpm]; exact hpre) with ⟨d, hd, hfst⟩
                  rcases hplaced d hd with ⟨hdB, hdSub⟩
                  cases fuel with
                  | zero => omega
                  | succ f' =>
                      have hdLt := (hdB d.1.toNat hdSub.1).2
                      rw [hfst] at hdLt
                      omega
                · have hsB := (hsuf cn hs).1
                  omega
              have huJ : (UInt32.ofNat pre.length).toNat = pre.length :=
                uint32_toNat_ofNat_lt pre.length (by omega)
              let aIns := aMid.set parent (.element pns ptag pst pmg ((pre ++ [cn]) ++ suf))
              have haInsNext : aIns.nextId = aMid.nextId := DomArena.nextId_set _ _ _
              let sCn : Nat → Prop := fun k => a.nextId ≤ k ∧ k < aMid.nextId
              have holdFrame : ∀ d ∈ placed,
                  DisjointDomSetChild fuel parent aIns d.1 d.2 ∧
                  readDomTree fuel aIns d.1 = readDomTree fuel a d.1 := by
                intro d hd
                exact keyed_placed_old_frame (by rw [haInsNext]; omega) (hplaced d hd)
                  (fun m hm hne => by
                    rw [DomArena.get_set_ne _ _ hne, haMidFrame m ((hplaced d hd).1 m.toNat hm).2])
              have hplaced' : ∀ d ∈ placed ++ [(cn, sCn)],
                  DisjointDomSetChild fuel parent aIns d.1 d.2 := by
                intro d hd
                rcases List.mem_append.1 hd with hdOld | hdNew
                · exact (holdFrame d hdOld).1
                · simp only [List.mem_singleton] at hdNew
                  subst hdNew
                  refine ⟨fun k hk => ⟨by omega, by rw [haInsNext]; exact hk.2⟩, ?_⟩
                  have hcnSet := SubtreeInRange_to_SubtreeInSet hcnSub
                  have hfr := SubtreeInSet_frame (a := aMid) (a' := aIns) (S := sCn) (n := cn)
                    (fun m hm => by
                      have hne : m ≠ parent := by intro heq; subst heq; omega
                      exact DomArena.get_set_ne _ _ hne)
                    hcnSet
                  exact hfr.1
              have hmatch' : ∀ d ∈ placed ++ [(cn, sCn)], ∀ k, d.2 k → k < baseLimit →
                  ∃ iv ∈ used, iv.1 ≤ k ∧ k < iv.2 := by
                intro d hd k hk hlt
                rcases List.mem_append.1 hd with hdOld | hdNew
                · exact hmatch d hdOld k hk hlt
                · simp only [List.mem_singleton] at hdNew
                  subst hdNew
                  dsimp [sCn] at hk
                  omega
              have hcnReadIns : readDomTree fuel aIns cn = specDom childNs newH := by
                have hfr := SubtreeInRange_frame (a := aMid) (a' := aIns) (lo := a.nextId) (hi := aMid.nextId) (n := cn)
                  (fun m hm1 _ => by
                    have hne : m ≠ parent := by intro heq; subst heq; omega
                    exact DomArena.get_set_ne _ _ hne)
                  hcnSub
                exact hfr.2.trans hcnRead
              have hpreReadIns : ∀ x ∈ pre, readDomTree fuel aIns x = readDomTree fuel a x := by
                intro x hx
                rcases List.mem_map.1 (by rw [hpm]; exact hx) with ⟨d, hd, hfst⟩
                rw [← hfst]
                exact (holdFrame d hd).2
              have hnd' : ((pre ++ [cn]) ++ suf).Nodup := by
                have hcns : cn ∉ pre ∧ cn ∉ suf := by
                  simpa [List.mem_append, not_or] using hcnNotIn
                have hndSplit := List.nodup_append.1 hnd
                rw [List.append_assoc]
                refine List.nodup_append.2 ⟨hndSplit.1, List.nodup_cons.2 ⟨hcns.2, hndSplit.2.1⟩, ?_⟩
                intro x hx y hy hxy
                rcases List.mem_cons.1 hy with hyEq | hysuf
                · subst hxy; rw [hyEq] at hx; exact hcns.1 hx
                · exact hndSplit.2.2 x hx y hysuf hxy
              have hsuf' : ∀ r ∈ suf, r.toNat < aIns.nextId ∧ r ≠ parent := by
                intro r hr
                have hr0 := hsuf r hr
                exact ⟨Nat.lt_of_lt_of_le hr0.1 (by rw [haInsNext]; omega), hr0.2⟩
              have hinsRun : (MonadDom.insertBeforeNode (m := StateM (DomArena msg)) parent
                  (UInt32.ofNat pre.length) cn).run aMid = ((), aIns) := by
                dsimp only [MonadDom.insertBeforeNode, StateT.run, DomArena.modifyChildren, DomArena.modify]
                rw [hparMid]
                have hwb := keyed_step_insertBefore_create pre suf cn hnd hcnNotIn
                simp [huJ, hwb, aIns]
              have hih := ih tRest (pre ++ [cn]) suf used (placed ++ [(cn, sCn)]) aIns
                hlen'
                (by simp [hpm])
                (by simp only [List.length_append, List.length_singleton]; omega)
                (by rw [haInsNext]; omega)
                (by rw [haInsNext]; omega)
                hrestDep
                (by rw [haInsNext]; omega)
                (by rw [haInsNext]; omega)
                (by simp [aIns, DomArena.get_set_self])
                hnd'
                hplaced'
                hmatch'
                hsuf'
                (by simpa [List.length_append] using hrestPlan)
              have huNext : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre ++ [cn]).length := by
                simp only [List.length_append, List.length_singleton]
                exact uint32_ofNat_succ pre.length (by omega)
              have hstepRun :
                  (applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat pre.length)
                    (.create newH :: sRest)).run a =
                  (applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat (pre ++ [cn]).length)
                    sRest).run aIns := by
                dsimp only [applyKeyedStepsM, StateT.run, bind, StateT.bind,
                            MonadDom.insertBeforeNode, DomArena.modifyChildren, DomArena.modify]
                rw [hget]
                dsimp only
                rw [show (if (pns == Dom.svgNs && ptag != "foreignObject") = true then Dom.svgNs else "") = childNs from hchildNs.symm]
                have hresB : buildDomM (m := StateM (DomArena msg)) childNs newH a = (cn, aMid) := rfl
                rw [hresB]
                dsimp only
                rw [hparMid, huJ]
                dsimp only
                rw [keyed_step_insertBefore_create pre suf cn hnd hcnNotIn, huNext]
                simp only [aIns, List.append_assoc, List.singleton_append]
              cases hresOut : (applyKeyedStepsM (m := StateM (DomArena msg)) parent live
                  (UInt32.ofNat (pre ++ [cn]).length) sRest).run aIns with
              | mk fj aFin =>
                  rw [hstepRun, hresOut]
                  rw [hresOut] at hih
                  rcases hih with ⟨targetsOut, sufRem, placedOut, hfj, hlenOut, hsufLe, hnextOut, hgetOut, hpmOut, hplOut, hreadOut⟩
                  refine ⟨cn :: targetsOut, sufRem, placedOut, ?_, ?_, hsufLe, ?_, ?_, ?_, hplOut, ?_⟩
                  · simp [hfj, List.length_append]; omega
                  · simp [hlenOut]
                  · rw [haInsNext] at hnextOut; simp only [htmlListNodeCount]; omega
                  · simpa [List.append_assoc] using hgetOut
                  · simpa [List.append_assoc] using hpmOut
                  · rw [List.append_assoc] at hreadOut
                    have hpreMap : (pre ++ [cn]).map (readDomTree fuel aIns) =
                        pre.map (readDomTree fuel a) ++ [specDom childNs newH] := by
                      rw [List.map_append, List.map_singleton, hcnReadIns]
                      congr 1
                      exact List.map_congr_left hpreReadIns
                    simpa [List.append_assoc, specDomList, hpreMap] using hreadOut
          | reuse oldIdx p =>
              simp only [KeyedStepPlanOk] at hplan
              rcases hplan with ⟨holdLt, hcsuf, lo, hi, hparLo, hcLo, hcHi, hiBase, hdisj, hpSpec, hrestPlan⟩
              let c := live[oldIdx]!
              have hcDef : live.getD oldIdx 0 = c := by simp [c, Array.getD, holdLt]
              have hcInSuf : c ∈ suf := hcsuf
              have huJ : (UInt32.ofNat pre.length).toNat = pre.length :=
                uint32_toNat_ofNat_lt pre.length (by omega)
              let aIns := a.set parent (.element pns ptag pst pmg ((pre ++ [c]) ++ suf.erase c))
              have haInsNext : aIns.nextId = a.nextId := DomArena.nextId_set _ _ _
              have hcNotPre : c ∉ pre := not_mem_left_of_nodup_append hnd hcInSuf
              have hinsRun : (MonadDom.insertBeforeNode (m := StateM (DomArena msg)) parent
                  (UInt32.ofNat pre.length) c).run a = ((), aIns) := by
                dsimp only [MonadDom.insertBeforeNode, StateT.run, DomArena.modifyChildren, DomArena.modify]
                rw [hget, huJ]
                dsimp only
                rw [w3cInsertBefore_step pre suf c hnd hcNotPre]
                simp only [aIns, List.append_assoc, List.singleton_append]
              let aMid := ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) c p).run aIns).2
              have hpatchSpec := hpSpec aIns (by rw [haInsNext]; omega)
              have haMidOutEq : ((applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) live[oldIdx]! p).run aIns).2 = aMid := rfl
              rw [haMidOutEq] at hpatchSpec
              rcases hpatchSpec with ⟨haMidEq, haMidNext, haMidNextLe, haMidFrame, hcSubMid, hcReadMid⟩
              simp only [htmlListNodeCount] at hbound
              simp only [htmlListDepth] at hdep
              have hrestDep : htmlListDepth tRest ≤ fuel := Nat.le_trans (Nat.le_max_right _ _) hdep
              have hparMid : aMid.get parent = .element pns ptag pst pmg ((pre ++ [c]) ++ suf.erase c) := by
                rw [haMidFrame parent (.inl hparLo) (by rw [haInsNext]; omega)]
                simp [aIns, DomArena.get_set_self]
              let sC : Nat → Prop := fun k => (lo ≤ k ∧ k < hi) ∨ (aIns.nextId ≤ k ∧ k < aMid.nextId)
              have holdFrame : ∀ d ∈ placed,
                  DisjointDomSetChild fuel parent aMid d.1 d.2 ∧
                  readDomTree fuel aMid d.1 = readDomTree fuel a d.1 := by
                intro d hd
                have hdisjD := hplaced d hd
                exact keyed_placed_old_frame (by rw [← haInsNext]; exact haMidNext) hdisjD
                  (fun m hm hne => by
                    have hmDisj : m.toNat < lo ∨ hi ≤ m.toNat := by
                      rcases Nat.lt_or_ge m.toNat baseLimit with hmLt | hmGe
                      · rcases hmatch d hd m.toNat hm hmLt with ⟨iv, hiv, h1, h2⟩
                        rcases hdisj iv hiv with hle | hge
                        · left; omega
                        · right; omega
                      · right; omega
                    rw [haMidFrame m hmDisj (by rw [haInsNext]; exact (hdisjD.1 m.toNat hm).2),
                        DomArena.get_set_ne _ _ hne])
              have hplaced' : ∀ d ∈ placed ++ [(c, sC)],
                  DisjointDomSetChild fuel parent aMid d.1 d.2 := by
                intro d hd
                rcases List.mem_append.1 hd with hdOld | hdNew
                · exact (holdFrame d hdOld).1
                · simp only [List.mem_singleton] at hdNew
                  subst hdNew
                  refine ⟨fun k hk => ?_, hcSubMid⟩
                  rcases hk with ⟨hk1, hk2⟩ | ⟨hk1, hk2⟩
                  · exact ⟨by omega, by omega⟩
                  · exact ⟨by rw [haInsNext] at hk1; omega, hk2⟩
              have hmatch' : ∀ d ∈ placed ++ [(c, sC)], ∀ k, d.2 k → k < baseLimit →
                  ∃ iv ∈ used ++ [(lo, hi)], iv.1 ≤ k ∧ k < iv.2 := by
                intro d hd k hk hlt
                rcases List.mem_append.1 hd with hdOld | hdNew
                · rcases hmatch d hdOld k hk hlt with ⟨iv, hiv, h1, h2⟩
                  exact ⟨iv, List.mem_append_left _ hiv, h1, h2⟩
                · simp only [List.mem_singleton] at hdNew
                  subst hdNew
                  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · exact ⟨(lo, hi), by simp, h1, h2⟩
                  · rw [haInsNext] at h1; omega
              have hpreReadMid : ∀ x ∈ pre, readDomTree fuel aMid x = readDomTree fuel a x := by
                intro x hx
                rcases List.mem_map.1 (by rw [hpm]; exact hx) with ⟨d, hd, hfst⟩
                rw [← hfst]
                exact (holdFrame d hd).2
              have hnd' : ((pre ++ [c]) ++ suf.erase c).Nodup := by
                simpa [List.append_assoc] using nodup_reinsert hnd hcNotPre
              have hsufLen : (suf.erase c).length ≤ suf.length :=
                List.length_erase_le
              have hsuf' : ∀ r ∈ suf.erase c, r.toNat < aMid.nextId ∧ r ≠ parent := by
                intro r hr
                have hr0 := hsuf r (List.mem_of_mem_erase hr)
                exact ⟨Nat.lt_of_lt_of_le hr0.1 (by rw [haInsNext] at haMidNext; exact haMidNext), hr0.2⟩
              have hih := ih tRest (pre ++ [c]) (suf.erase c) (used ++ [(lo, hi)]) (placed ++ [(c, sC)]) aMid
                hlen'
                (by simp [hpm])
                (by simp only [List.length_append, List.length_singleton]; omega)
                (by rw [haInsNext] at haMidNext; omega)
                (by rw [haInsNext] at haMidNextLe; omega)
                hrestDep
                (by rw [haInsNext] at haMidNext; omega)
                (by rw [haInsNext] at haMidNext; omega)
                hparMid
                hnd'
                hplaced'
                hmatch'
                hsuf'
                (by simpa [c, List.length_append] using hrestPlan)
              have huNext : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre ++ [c]).length := by
                simp only [List.length_append, List.length_singleton]
                exact uint32_ofNat_succ pre.length (by omega)
              have hstepRun :
                  (applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat pre.length)
                    (.reuse oldIdx p :: sRest)).run a =
                  (applyKeyedStepsM (m := StateM (DomArena msg)) parent live (UInt32.ofNat (pre ++ [c]).length)
                    sRest).run aMid := by
                dsimp only [applyKeyedStepsM, StateT.run, bind, StateT.bind,
                            MonadDom.insertBeforeNode, DomArena.modifyChildren, DomArena.modify]
                rw [hcDef, hget, huJ]
                dsimp only
                rw [w3cInsertBefore_step pre suf c hnd hcNotPre]
                have hInsEq : a.set parent (.element pns ptag pst pmg (pre ++ c :: suf.erase c)) = aIns := by
                  simp only [aIns, List.append_assoc, List.singleton_append]
                rw [hInsEq]
                cases hresPatch : applyToDomM (m := StateM (DomArena msg)) parent (UInt32.ofNat pre.length) c p aIns with
                | mk u s' =>
                    have hsEq : s' = aMid := by
                      dsimp only [aMid, StateT.run]
                      rw [hresPatch]
                    subst hsEq
                    rw [huNext]
              cases hresOut : (applyKeyedStepsM (m := StateM (DomArena msg)) parent live
                  (UInt32.ofNat (pre ++ [c]).length) sRest).run aMid with
              | mk fj aFin =>
                  rw [hstepRun, hresOut]
                  rw [hresOut] at hih
                  rcases hih with ⟨targetsOut, sufRem, placedOut, hfj, hlenOut, hsufLe', hnextOut, hgetOut, hpmOut, hplOut, hreadOut⟩
                  refine ⟨c :: targetsOut, sufRem, placedOut, ?_, ?_, Nat.le_trans hsufLe' hsufLen, ?_, ?_, ?_, hplOut, ?_⟩
                  · simp [hfj, List.length_append]; omega
                  · simp [hlenOut]
                  · rw [haInsNext] at haMidNextLe; simp only [htmlListNodeCount]; omega
                  · simpa [List.append_assoc] using hgetOut
                  · simpa [List.append_assoc] using hpmOut
                  · rw [List.append_assoc] at hreadOut
                    have hpreMap : (pre ++ [c]).map (readDomTree fuel aMid) =
                        pre.map (readDomTree fuel a) ++ [specDom childNs t] := by
                      rw [List.map_append, List.map_singleton, hcReadMid]
                      congr 1
                      exact List.map_congr_left hpreReadMid
                    simpa [List.append_assoc, specDomList, hpreMap] using hreadOut

/-- Full end-to-end keyed reconciliation (`snapshotChildrenM` + `applyKeyedStepsM` + `removeTailM`)
    connecting directly to `removeTailSpec` / `w3cReconcileKeyed_eq` and `specDomList`. -/
theorem applyKeyedStepsM_with_removeTail_spec {msg : Type} (parent : Dom.Node) (pns ptag : String)
    (pst : SpecElemState msg) (pmg : List String) (liveCs : List Dom.Node)
    (steps : List (KeyedStep msg)) (targets : List (Html msg))
    (fuel : Nat) (childNs : String) (a : DomArena msg)
    (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (hlen : steps.length = targets.length)
    (hsize : liveCs.length + steps.length < UInt32.size)
    (hbound : a.nextId + htmlListNodeCount targets < UInt32.size)
    (hdep : htmlListDepth targets ≤ fuel)
    (hparLt : parent.toNat < a.nextId)
    (hpos : 0 < a.nextId)
    (hget : a.get parent = .element pns ptag pst pmg liveCs)
    (hliveNd : liveCs.Nodup)
    (hliveDom : ∀ r ∈ liveCs, r.toNat < a.nextId ∧ r ≠ parent)
    (hplan : KeyedStepPlanOk fuel childNs parent ⟨liveCs⟩ a.nextId 0 steps targets liveCs []) :
    let ((_, finalJ), aMid) := (do
      let live ← snapshotChildrenM (m := StateM (DomArena msg)) parent 0 #[] (UInt32.ofNat liveCs.length).toNat
      let fj ← applyKeyedStepsM (m := StateM (DomArena msg)) parent live 0 steps
      pure (live, fj)).run a
    let aOut := ((MonadDom.childCount (m := StateM (DomArena msg)) parent >>= fun count =>
      removeTailM (m := StateM (DomArena msg)) parent finalJ (count.toNat - finalJ.toNat)).run aMid).2
    ∃ (targetsOut : List Dom.Node),
      targetsOut.length = steps.length ∧
      aOut.get parent = .element pns ptag pst pmg targetsOut ∧
      targetsOut.map (readDomTree fuel aOut) = specDomList childNs targets := by
  have hsnap := snapshotChildrenM_spec a parent pns ptag pst pmg liveCs (by omega) 0 liveCs.length #[] (by omega)
  have ha0 : a.set parent (.element pns ptag pst pmg liveCs) = a := by
    cases a; simp only [DomArena.set, DomArena.mk.injEq, true_and, and_true]
    funext m; by_cases hm : m == parent
    · have heq : m = parent := eq_of_beq hm; subst heq; simpa [DomArena.get] using hget.symm
    · simp [hm]
  rw [ha0] at hsnap
  simp only [List.drop_zero, List.nil_append] at hsnap
  dsimp only [StateT.run] at hsnap
  have hrec := applyKeyedStepsM_reconcile_spec parent pns ptag pst pmg ⟨liveCs⟩ fuel childNs a.nextId hchildNs
    steps targets [] liveCs [] [] a hlen rfl (by simp; omega) (Nat.le_refl _) hbound hdep hparLt hpos
    (by simpa using hget) (by simpa using hliveNd) (fun _ h => nomatch h) (fun _ h => nomatch h)
    hliveDom hplan
  dsimp only [StateT.run] at hrec
  have huLive : (UInt32.ofNat liveCs.length).toNat = liveCs.length := uint32_toNat_ofNat_lt liveCs.length (by omega)
  dsimp only [StateT.run, bind, StateT.bind, pure, StateT.pure]
  rw [huLive, hsnap]
  dsimp only
  cases hrunK : applyKeyedStepsM (m := StateM (DomArena msg)) parent ⟨liveCs⟩ 0 steps a with
  | mk fj aMid =>
      have hrunK' : applyKeyedStepsM (m := StateM (DomArena msg)) parent
          ({ toList := liveCs } : Array Dom.Node) (UInt32.ofNat ([] : List Dom.Node).length) steps a =
          (fj, aMid) := hrunK
      rw [hrunK'] at hrec
      rcases hrec with ⟨targetsOut, sufRem, placedOut, hfj, hlenOut, hsufLe, hnextOut, hgetOut, hpmOut, hplOut, hreadOut⟩
      have hfjEq : fj = UInt32.ofNat targetsOut.length := by
        apply uint32_eq_of_toNat_eq
        rw [hfj, List.length_nil, Nat.zero_add, uint32_toNat_ofNat_lt _ (by omega), hlenOut]
      have haMidEq : aMid.set parent (.element pns ptag pst pmg (targetsOut ++ sufRem)) = aMid := by
        cases aMid; simp only [DomArena.set, DomArena.mk.injEq, true_and, and_true]
        funext m; by_cases hm : m == parent
        · have heq : m = parent := eq_of_beq hm; subst heq; simpa [DomArena.get] using hgetOut.symm
        · simp [hm]
      have hrem : ((MonadDom.childCount (m := StateM (DomArena msg)) parent >>= fun count =>
          removeTailM (m := StateM (DomArena msg)) parent fj (count.toNat - fj.toNat)).run aMid).2 =
          aMid.set parent (.element pns ptag pst pmg targetsOut) := by
        have huTarg : (UInt32.ofNat targetsOut.length).toNat = targetsOut.length :=
          uint32_toNat_ofNat_lt targetsOut.length (by omega)
        rw [hfjEq, huTarg]
        calc ((MonadDom.childCount (m := StateM (DomArena msg)) parent >>= fun count =>
                removeTailM (m := StateM (DomArena msg)) parent (UInt32.ofNat targetsOut.length)
                  (count.toNat - targetsOut.length)).run aMid).2
            = ((MonadDom.childCount (m := StateM (DomArena msg)) parent >>= fun count =>
                removeTailM (m := StateM (DomArena msg)) parent (UInt32.ofNat targetsOut.length)
                  (count.toNat - targetsOut.length)).run
                (aMid.set parent (.element pns ptag pst pmg (targetsOut ++ sufRem)))).2 := by
                  rw [haMidEq]
          _ = aMid.set parent (.element pns ptag pst pmg targetsOut) :=
                positional_removeTail_spec aMid parent pns ptag pst pmg targetsOut sufRem (by omega)
      dsimp only [StateT.run, bind, StateT.bind, MonadDom.childCount, pure, StateT.pure] at hrem
      refine ⟨targetsOut, hlenOut, ?_, ?_⟩
      · rw [hrem, DomArena.get_set_self]
      · rw [hrem]
        have hreadTargets : targetsOut.map (readDomTree fuel aMid) = specDomList childNs targets := by
          simpa using hreadOut
        rw [← hreadTargets]
        apply List.map_congr_left
        intro t ht
        have ht' : t ∈ ([] : List Dom.Node) ++ targetsOut := ht
        rw [← hpmOut] at ht'
        rcases List.mem_map.1 ht' with ⟨d, hd, hfst⟩
        rw [← hfst]
        rcases hplOut d hd with ⟨hdB, hdSub⟩
        have hfr := SubtreeInSet_frame (a := aMid) (a' := aMid.set parent (.element pns ptag pst pmg targetsOut))
          (S := d.2) (n := d.1)
          (fun m hm => by
            have hne : m ≠ parent := by intro heq; subst heq; have := (hdB m.toNat hm).1; omega
            exact DomArena.get_set_ne _ _ hne)
          hdSub
        exact hfr.2


end Qed
