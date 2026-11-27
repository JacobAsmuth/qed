import Qed.Proofs.DomSubtree

namespace Qed
variable {msg : Type}
private abbrev ArenaM (msg : Type) := StateM (DomArena msg)

private structure RecStepCtx (ep : ElemPar msg) (nSteps : Nat) (targets targetsDone : List (Html msg))
    (pre suf : List Dom.Node) (Sdone : Nat → Prop) (a : DomArena msg) : Prop where
  hchildNs : ep.childNsOk
  hlen   : nSteps = targets.length
  hclean : Html.DomCleanList targets = true
  hdep   : htmlListDepth targets ≤ ep.f
  hsz    : pre.length + suf.length + nSteps < UInt32.size
  hbound : a.nextId + htmlListNodeCount targets < UInt32.size
  hparLt : ep.parent.toNat < a.nextId
  hposId : 0 < a.nextId
  hpar   : a.get ep.parent = ep.entry (pre ++ suf)
  hnd    : (pre ++ suf).Nodup
  hSdone : ∀ k, Sdone k → k ≠ ep.parent.toNat ∧ k < a.nextId
  hDoneC : CleanDomChildren ep.f ep.childNs targetsDone a Sdone pre
  hsufB  : ∀ r ∈ suf, r.toNat < a.nextId ∧ r ≠ ep.parent

def InPlaceChildPatchSpec (fuel : Nat) (childNs : String) (parent : Dom.Node) (j : UInt32) (child : Dom.Node) (p : Patch msg) (target : Html msg) (lo hi : Nat) (aIn aOut : DomArena msg) : Prop :=
  ((applyToDomM (m := ArenaM msg) parent j child p).run aIn).2 = aOut ∧ aIn.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ aIn.nextId + htmlNodeCount target ∧
  (∀ m : Dom.Node, (m.toNat < lo ∨ hi ≤ m.toNat) → m.toNat < aIn.nextId → aOut.get m = aIn.get m) ∧
  SubtreeInSet fuel aOut (fun k => (lo ≤ k ∧ k < hi) ∨ (aIn.nextId ≤ k ∧ k < aOut.nextId)) child ∧ readDomTree fuel aOut child = specDom childNs target
theorem InPlaceChildPatchSpec_setText (a : DomArena msg) (parent child : Dom.Node) (idx : UInt32) (sOld sNew : String) (childNs : String) (fuel : Nat) (hf : 0 < fuel) (hlo : child.toNat < a.nextId) :
    InPlaceChildPatchSpec fuel childNs parent idx child (.setText sNew) (.text sNew) child.toNat (child.toNat + 1) (a.set child (.text sOld))
      ((applyToDomM (m := ArenaM msg) parent idx child (.setText sNew)).run (a.set child (.text sOld))).2 := by
  have hget : ((applyToDomM (m := ArenaM msg) parent idx child (.setText sNew)).run (a.set child (.text sOld))).2 = a.set child (.text sNew) := by
    simp [applyToDomM, StateT.run, MonadDom.setText, DomArena.modify, DomArena.get_set_self, DomArena.set_set]
  cases fuel with | zero => omega | succ _ =>
  exact ⟨rfl, by simp [hget], by simp [hget, htmlNodeCount], fun m hm _ => by simp [hget, DomArena.get_set_ne _ _ (show m ≠ child from fun e => by subst e; omega)],
    by simp only [hget]; exact ⟨.inl ⟨Nat.le_refl _, by omega⟩, by simp [DomArena.get_set_self]⟩, by simp [hget, readDomTree, DomArena.get_set_self, specDom]⟩
theorem keyed_step_insertBefore_create (pre suf : List Dom.Node) (cn : Dom.Node) (hnd : (pre ++ suf).Nodup) (hnot : cn ∉ pre ++ suf) :
    w3cInsertBefore (pre ++ suf) pre.length cn = pre ++ cn :: suf := by
  rw [w3cInsertBefore_step pre suf cn hnd (fun h => hnot (List.mem_append_left _ h)), List.erase_of_not_mem (fun h => hnot (List.mem_append_right _ h))]
theorem positional_step_reuse_tail (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (pre : List Dom.Node) (hd : Dom.Node) (tl : List Dom.Node) (a : DomArena msg) : pre.length < UInt32.size →
    (MonadDom.childAt (m := ArenaM msg) parent (UInt32.ofNat pre.length)).run (a.set parent (.element pns ptag pst pmg (pre ++ hd :: tl))) =
      (hd, a.set parent (.element pns ptag pst pmg (pre ++ hd :: tl))) := fun hlt => by
  simp [MonadDom.childAt, StateT.run, DomArena.get_set_self, uint32_toNat_ofNat_lt pre.length hlt]
theorem positional_removeTail_spec (a : DomArena msg) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (targets rem : List Dom.Node) (hlen : targets.length + rem.length < UInt32.size) :
    ((MonadDom.childCount (m := ArenaM msg) parent >>= fun count => removeTailM (m := ArenaM msg) parent (UInt32.ofNat targets.length) (count.toNat - targets.length)).run
      (a.set parent (.element pns ptag pst pmg (targets ++ rem)))).2 = a.set parent (.element pns ptag pst pmg targets) := by
  dsimp only [bind, StateT.bind, StateT.run, MonadDom.childCount]; rw [DomArena.get_set_self]; dsimp only
  rw [uint32_toNat_ofNat_lt _ (by simp; omega), List.length_append, Nat.add_sub_cancel_left]
  have hr := removeTailM_spec a parent targets.length rem.length pns ptag pst pmg (targets ++ rem)
  dsimp only [StateT.run] at hr; rw [hr, uint32_toNat_ofNat_lt targets.length (by omega), removeTailSpec_append]

/-! ## Keyed Index Injectivity, `CleanDomSubtree`, & Complete `applyToDomM` / `patchHtmlSubtreeM` -/
theorem validatedKeyIndex_inj {cs : List (Html msg)} {idx : Std.HashMap String Nat} (hv : validatedKeyIndex cs = some idx)
    {i₁ i₂ : Nat} {k : String} (h₁ : i₁ < cs.length) (h₂ : i₂ < cs.length) (hk₁ : cs[i₁].keyOf = some k) (hk₂ : cs[i₂].keyOf = some k) : i₁ = i₂ := by
  have ⟨_, hspec⟩ := validatedKeyIndex_spec hv
  rcases hspec i₁ h₁ with ⟨_, heq₁, hidx₁⟩; rcases hspec i₂ h₂ with ⟨_, heq₂, hidx₂⟩
  rw [hk₁] at heq₁; cases heq₁; rw [hk₂] at heq₂; cases heq₂; exact Option.some.inj (hidx₁.symm.trans hidx₂)
def DiffStepsValid (c₁ c₂ : List (Html msg)) (steps : List (KeyedStep msg)) : Prop :=
  steps.length = c₂.length ∧
  (∀ (i : Nat) (hi : i < c₂.length), (∀ newH, steps[i]? = some (.create newH) → newH = c₂[i]) ∧ (∀ j p, steps[i]? = some (.reuse j p) → ∃ _ : j < c₁.length, p = diff c₁[j] c₂[i])) ∧
  ∀ i₁ i₂ j₁ j₂ p₁ p₂, i₁ < steps.length → i₂ < steps.length → steps[i₁]? = some (.reuse j₁ p₁) → steps[i₂]? = some (.reuse j₂ p₂) → j₁ = j₂ → i₁ = i₂
private theorem diff_steps_valid_of {c₁ c₂ : List (Html msg)} {steps : List (KeyedStep msg)}
    (P : (i : Nat) → i < c₂.length → (j : Nat) → j < c₁.length → Prop) (hlen : steps.length = c₂.length)
    (hAt : ∀ (i : Nat) (hi : i < c₂.length), steps[i]'(hlen ▸ hi) = .create c₂[i] ∨ ∃ j, ∃ hj : j < c₁.length, P i hi j hj ∧ steps[i]'(hlen ▸ hi) = .reuse j (diff c₁[j] c₂[i]))
    (hInj : ∀ i₁ i₂ (hi₁ : i₁ < c₂.length) (hi₂ : i₂ < c₂.length) j (hj : j < c₁.length), P i₁ hi₁ j hj → P i₂ hi₂ j hj → i₁ = i₂) : DiffStepsValid c₁ c₂ steps := by
  have hreuse : ∀ (i : Nat) (hi : i < c₂.length) j p, steps[i]? = some (.reuse j p) → ∃ hj : j < c₁.length, P i hi j hj ∧ p = diff c₁[j] c₂[i] := fun i hi j p h => by
    rw [List.getElem?_eq_getElem (hlen ▸ hi)] at h; rcases hAt i hi with hc | ⟨_, hj', hp, hr⟩ <;> (first | rw [hc] at h | rw [hr] at h) <;> cases h; exact ⟨hj', hp, rfl⟩
  refine ⟨hlen, fun i hi => ⟨fun newH h => ?_, fun j p h => let ⟨hj, _, hp⟩ := hreuse i hi j p h; ⟨hj, hp⟩⟩,
    fun i₁ i₂ j₁ _ p₁ p₂ hi₁ hi₂ h1 h2 hj => by subst hj; rcases hreuse i₁ (hlen ▸ hi₁) j₁ p₁ h1 with ⟨hj₁, hp1, _⟩; rcases hreuse i₂ (hlen ▸ hi₂) j₁ p₂ h2 with ⟨_, hp2, _⟩; exact hInj i₁ i₂ (hlen ▸ hi₁) (hlen ▸ hi₂) j₁ hj₁ hp1 hp2⟩
  rw [List.getElem?_eq_getElem (hlen ▸ hi)] at h; rcases hAt i hi with hc | ⟨_, _, _, hr⟩ <;> (first | rw [hc] at h | rw [hr] at h) <;> cases h; rfl
private theorem diff_steps_valid_pos {t : String} {a₁ a₂ : List (Attr msg)} {c₁ c₂ : List (Html msg)} {steps : List (KeyedStep msg)}
    (hun : validatedKeyIndex c₁ = none ∨ validatedKeyIndex c₂ = none) (hdiff : diff (.element t a₁ c₁) (.element t a₂ c₂) = .patchElement a₂ steps) : DiffStepsValid c₁ c₂ steps := by
  rcases diff_positional_reuses (t := t) (a₁ := a₁) (a₂ := a₂) hun with ⟨_, hEq, hlen, hAt⟩; rw [hEq] at hdiff; cases hdiff
  exact diff_steps_valid_of (fun i _ j _ => i = j) hlen (fun i hi => if hc : i < c₁.length then .inr ⟨i, hc, rfl, (hAt i hi).1 hc⟩ else .inl ((hAt i hi).2 (Nat.le_of_not_lt hc))) (fun _ _ _ _ _ _ h1 h2 => h1.trans h2.symm)
theorem diff_steps_valid {t : String} {a₁ a₂ : List (Attr msg)} {c₁ c₂ : List (Html msg)} {steps : List (KeyedStep msg)}
    (hdiff : diff (.element t a₁ c₁) (.element t a₂ c₂) = .patchElement a₂ steps) : DiffStepsValid c₁ c₂ steps := by
  cases h₁ : validatedKeyIndex c₁ with
  | none => exact diff_steps_valid_pos (.inl h₁) hdiff
  | some _ => cases h₂ : validatedKeyIndex c₂ with
    | none => exact diff_steps_valid_pos (.inr h₂) hdiff
    | some _ =>
        rcases diff_keyed_reuses (t := t) (a₁ := a₁) (a₂ := a₂) h₁ h₂ with ⟨_, hEq, hlen, hAt⟩; rw [hEq] at hdiff; cases hdiff
        exact diff_steps_valid_of (fun i hi j hj => ∃ k, c₂[i].keyOf = some k ∧ c₁[j].keyOf = some k) hlen
          (fun i hi => by rcases (validatedKeyIndex_spec h₂).2 i hi with ⟨k, hkc₂, _⟩
                          by_cases hex : ∃ j, ∃ hj : j < c₁.length, c₁[j].keyOf = some k
                          · rcases hex with ⟨j, hj, hkj⟩; exact .inr ⟨j, hj, ⟨k, hkc₂, hkj⟩, (hAt i hi).1 j hj k hkc₂ hkj⟩
                          · exact .inl ((hAt i hi).2 k hkc₂ fun j hj hk => hex ⟨j, hj, hk⟩))
          (fun i₁ i₂ hi₁ hi₂ _ _ ⟨_, h1, ho1⟩ ⟨_, h2, ho2⟩ => by rw [ho1] at ho2; cases ho2; exact validatedKeyIndex_inj h₂ hi₁ hi₂ h1 h2)
abbrev PatchSpecOut (f : Nat) (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (oldH newH : Html msg) (node : Dom.Node) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a a' : DomArena msg) : Prop :=
  a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount newH ∧ (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
  ∃ newNode, (diff oldH newH = .replace newH ∨ newNode = node) ∧ a'.get parent = .element pns ptag pst pmg (pre ++ newNode :: suf) ∧ (pre ++ newNode :: suf).Nodup ∧
    (∀ r ∈ pre ++ newNode :: suf, r.toNat < a'.nextId) ∧ CleanDomSubtree f childNs newH a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) newNode
def PatchSpecAt (f : Nat) : Prop :=
  ∀ (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (oldH newH : Html msg) (node : Dom.Node) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg),
    childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "") → pre.length + 1 + suf.length < UInt32.size → a.nextId + htmlNodeCount newH < UInt32.size → htmlDepth newH ≤ f →
    parent.toNat < a.nextId → 0 < a.nextId → a.get parent = .element pns ptag pst pmg (pre ++ node :: suf) → (pre ++ node :: suf).Nodup → ¬Sold parent.toNat → (∀ k, Sold k → k < a.nextId) →
    (∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId) → CleanDomSubtree f childNs oldH a Sold node → newH.DomClean = true →
    PatchSpecOut f childNs parent pns ptag pst pmg oldH newH node pre suf Sold a ((applyToDomM (m := ArenaM msg) parent (UInt32.ofNat pre.length) node (diff oldH newH)).run a).2
abbrev ReconcileStepOut (f : Nat) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (childNs : String)
    (nSteps sufLen : Nat) (targets targetsDone : List (Html msg)) (pre : List Dom.Node) (Sdone Srem : Nat → Prop) (a aOut : DomArena msg) : Prop :=
  ∃ targetsOut sufRem Snew, targetsOut.length = nSteps ∧ (targetsOut ++ sufRem).length ≤ sufLen + nSteps ∧
    a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount targets ∧ aOut.get parent = .element pns ptag pst pmg ((pre ++ targetsOut) ++ sufRem) ∧
    (∀ m : Dom.Node, m ≠ parent → ¬Sdone m.toNat → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    (∀ k, Snew k → (Sdone k ∨ Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧ CleanDomChildren f childNs (targetsDone ++ targets) aOut Snew (pre ++ targetsOut)
abbrev ReconcileStepAt0Out (f : Nat) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (childNs : String)
    (nSteps domLen : Nat) (c₂ : List (Html msg)) (Srem : Nat → Prop) (a aOut : DomArena msg) : Prop :=
  ∃ targetsOut sufRem Snew, targetsOut.length = nSteps ∧ (targetsOut ++ sufRem).length ≤ domLen + nSteps ∧
    a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount c₂ ∧ aOut.get parent = .element pns ptag pst pmg (targetsOut ++ sufRem) ∧
    (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    (∀ k, Snew k → (Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧ CleanDomChildren f childNs c₂ aOut Snew targetsOut
abbrev ReconcileTailOut (f : Nat) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String) (childNs : String)
    (c₂ : List (Html msg)) (Srem : Nat → Prop) (a aOut : DomArena msg) : Prop :=
  ∃ targetsOut Snew, a.nextId ≤ aOut.nextId ∧ aOut.nextId ≤ a.nextId + htmlListNodeCount c₂ ∧ aOut.get parent = .element pns ptag pst pmg targetsOut ∧
    (∀ m : Dom.Node, m ≠ parent → ¬Srem m.toNat → m.toNat < a.nextId → aOut.get m = a.get m) ∧
    (∀ k, Snew k → (Srem k ∨ (a.nextId ≤ k ∧ k < aOut.nextId)) ∧ k ≠ parent.toNat) ∧ CleanDomChildren f childNs c₂ aOut Snew targetsOut

private abbrev ElemPar.stepOut (ep : ElemPar msg) := ReconcileStepOut ep.f ep.parent ep.pns ep.ptag ep.pst ep.pmg ep.childNs
private abbrev ElemPar.at0Out (ep : ElemPar msg) := ReconcileStepAt0Out ep.f ep.parent ep.pns ep.ptag ep.pst ep.pmg ep.childNs
private abbrev ElemPar.tailOut (ep : ElemPar msg) := ReconcileTailOut ep.f ep.parent ep.pns ep.ptag ep.pst ep.pmg ep.childNs
private theorem cleanChildren_dom_bounds {ep : ElemPar msg} {c₁ c₂ : List (Html msg)} {domCs : List Dom.Node} {Srem : Nat → Prop} {a : DomArena msg} {n : Nat}
    (hn : n = c₂.length) (hbound : a.nextId + htmlListNodeCount c₂ < UInt32.size) (hSrem : ∀ k, Srem k → k ≠ ep.parent.toNat ∧ k < a.nextId) (hCleanCs : CleanDomChildren ep.f ep.childNs c₁ a Srem domCs) :
    (domCs.Nodup ∧ domCs.length = c₁.length) ∧ (∀ r ∈ domCs, r.toNat < a.nextId ∧ r ≠ ep.parent) ∧ domCs.length ≤ a.nextId ∧ ([] : List Dom.Node).length + domCs.length + n < UInt32.size := by
  have hnd := CleanDomChildren_nodup hCleanCs
  have hsufB : ∀ r ∈ domCs, r.toNat < a.nextId ∧ r ≠ ep.parent := fun r hr => have hb := hSrem r.toNat (CleanDomChildren_mem hCleanCs r hr); ⟨hb.2, node_ne_of_toNat_ne hb.1⟩
  have h1 := nodup_nodes_lt_length_le a.nextId domCs hnd.1 fun r hr => (hsufB r hr).1
  have h2 := list_length_le_htmlListNodeCount c₂; exact ⟨hnd, hsufB, h1, by rw [List.length_nil, Nat.zero_add, hn]; exact Nat.lt_of_le_of_lt (Nat.add_le_add h1 h2) hbound⟩
private theorem clean_build_child (ep : ElemPar msg) (hchildNs : ep.childNsOk) {newH : Html msg} {cs : List Dom.Node} {a : DomArena msg}
    (hclean : newH.DomClean = true) (hdep : htmlDepth newH ≤ ep.f) (hbound : a.nextId + htmlNodeCount newH < UInt32.size)
    (hparLt : ep.parent.toNat < a.nextId) (hpos : 0 < a.nextId) (hpar : a.get ep.parent = ep.entry cs) :
    ∃ cn aMid, MonadDom.childNamespace (m := ArenaM msg) ep.parent a = (ep.childNs, a) ∧ buildDomM (m := ArenaM msg) ep.childNs newH a = (cn, aMid) ∧
      a.nextId ≤ cn.toNat ∧ cn.toNat < aMid.nextId ∧ a.nextId ≤ aMid.nextId ∧ aMid.nextId ≤ a.nextId + htmlNodeCount newH ∧
      aMid.get ep.parent = ep.entry cs ∧ (∀ m : Dom.Node, m.toNat < a.nextId → aMid.get m = a.get m) ∧
      ∀ e, CleanDomSubtree ep.f ep.childNs newH (aMid.set ep.parent e) (fun k => a.nextId ≤ k ∧ k < aMid.nextId) cn := by
  have hbuild := buildDomM_spec_full ep.childNs newH a ep.f hpos hbound hdep; dsimp only [StateT.run] at hbuild
  cases hB : buildDomM (m := ArenaM msg) ep.childNs newH a with
  | mk cn aMid =>
      rw [hB] at hbuild; rcases hbuild with ⟨hge, hlt, hext, _, _, hcl⟩
      have hfr : ∀ m : Dom.Node, m.toNat < a.nextId → aMid.get m = a.get m := fun m hm => hext.frame m hm id
      exact ⟨cn, aMid, by dsimp only [MonadDom.childNamespace]; rw [hpar]; dsimp only [ElemPar.entry]; rw [← hchildNs], rfl, hge, hlt, hext.next_ge, hext.next_le,
        by rw [hfr ep.parent hparLt, hpar], hfr, fun _ => CleanDomSubtree_frame (fun m hm => DomArena.get_set_ne _ _ fun e => Nat.not_lt.2 hm.1 (e ▸ hparLt)) (hcl hclean)⟩
private theorem clean_step_reconcile_combine {ep : ElemPar msg} {nRest sufRestLen sufLen : Nat} {t : Html msg} {tRest targetsDone : List (Html msg)}
    {pre : List Dom.Node} {newChild : Dom.Node} {Sdone Sdone' Srem Srest : Nat → Prop} {a aMid aOut : DomArena msg}
    (hsufLe : sufRestLen ≤ sufLen) (haMidLe : a.nextId ≤ aMid.nextId) (haMidBound : aMid.nextId ≤ a.nextId + htmlNodeCount t)
    (hSr : ∀ k, Srest k → Srem k) (hSdone'Sub : ∀ k, Sdone' k → Sdone k ∨ Srem k ∨ (a.nextId ≤ k ∧ k < aMid.nextId))
    (hNotSdone' : ∀ k, ¬Sdone k → ¬Srem k → k < a.nextId → ¬Sdone' k) (hframeMid : ∀ m : Dom.Node, m ≠ ep.parent → ¬Srem m.toNat → m.toNat < a.nextId → aMid.get m = a.get m)
    (hih : ep.stepOut nRest sufRestLen tRest (targetsDone ++ [t]) (pre ++ [newChild]) Sdone' Srest aMid aOut) :
    ep.stepOut (nRest + 1) sufLen (t :: tRest) targetsDone pre Sdone Srem a aOut := by
  rcases hih with ⟨targetsRest, sufRem, Snew, hlenR, htotLenR, hmonoR, hboundR, hparR, hfrR, hSnew, hDoneR⟩
  simp only [List.append_assoc, List.singleton_append] at hparR hDoneR
  exact ⟨newChild :: targetsRest, sufRem, Snew, congrArg Nat.succ hlenR, by simp only [List.cons_append, List.length_cons] at htotLenR ⊢; omega,
    Nat.le_trans haMidLe hmonoR, by simp only [htmlListNodeCount]; exact Nat.le_trans hboundR (Nat.add_assoc _ _ _ ▸ Nat.add_le_add_right haMidBound _),
    by simp only [List.append_assoc]; exact hparR,
    fun m hmPar hmD hmR hmLt => (hfrR m hmPar (hNotSdone' _ hmD hmR hmLt) (fun hr => hmR (hSr _ hr)) (Nat.lt_of_lt_of_le hmLt haMidLe)).trans (hframeMid m hmPar hmR hmLt),
    fun k hk => by rcases hSnew k hk with ⟨h1 | h2 | ⟨hlo, hhi⟩, hnp⟩
                   · exact ⟨(hSdone'Sub k h1).imp id fun h => h.imp id fun ⟨h1, h2⟩ => ⟨h1, Nat.lt_of_lt_of_le h2 hmonoR⟩, hnp⟩
                   · exact ⟨.inr (.inl (hSr k h2)), hnp⟩
                   · exact ⟨.inr (.inr ⟨Nat.le_trans haMidLe hlo, hhi⟩), hnp⟩, hDoneR⟩

private theorem reconcile_steps_spec {Aux : Type} (ep : ElemPar msg) (hPatch : @PatchSpecAt msg ep.f) (run : UInt32 → List (KeyedStep msg) → DomArena msg → DomArena msg)
    (Inv : Aux → List (KeyedStep msg) → List (Html msg) → List Dom.Node → List Dom.Node → (Nat → Prop) → (Nat → Prop) → DomArena msg → Prop)
    (hNil : ∀ j a, run j [] a = a)
    (hCreateRun : ∀ newH sRest j a aIns, (∀ {α} (k : ArenaM msg α), (do let ns ← MonadDom.childNamespace ep.parent; let cn' ← buildDomM ns newH; MonadDom.insertBeforeNode ep.parent j cn'; k) a = k aIns) → run j (.create newH :: sRest) a = run (j + 1) sRest aIns)
    (hCreateInv : ∀ aux newH sRest t tRest pre suf Sdone Srem a, Inv aux (.create newH :: sRest) (t :: tRest) pre suf Sdone Srem a →
      newH = t ∧ ∀ cn aIns, a.nextId ≤ aIns.nextId → (∀ m : Dom.Node, m ≠ ep.parent → m.toNat < a.nextId → aIns.get m = a.get m) →
        ∃ aux', Inv aux' sRest tRest (pre ++ [cn]) suf (fun k => Sdone k ∨ (a.nextId ≤ k ∧ k < aIns.nextId)) Srem aIns)
    (hReuse : ∀ aux oldIdx p sRest t tRest pre suf Sdone Srem a, sRest.length = tRest.length → pre.length + suf.length + (sRest.length + 1) < UInt32.size →
      a.get ep.parent = ep.entry (pre ++ suf) → (pre ++ suf).Nodup → Inv aux (.reuse oldIdx p :: sRest) (t :: tRest) pre suf Sdone Srem a →
      ∃ cOld child sufRest Sc Srest a1, p = diff cOld t ∧ a1.nextId = a.nextId ∧ (∀ m : Dom.Node, m ≠ ep.parent → a1.get m = a.get m) ∧
        sufRest.length ≤ suf.length ∧ (∀ r ∈ child :: sufRest, r ∈ suf) ∧ a1.get ep.parent = ep.entry (pre ++ child :: sufRest) ∧ (pre ++ child :: sufRest).Nodup ∧
        (∀ k, Sc k → k ≠ ep.parent.toNat ∧ k < a.nextId) ∧ (∀ k, Sc k → Srem k) ∧ (∀ k, Srest k → Srem k) ∧ (∀ k, Sdone k → ¬Sc k) ∧ CleanDomSubtree ep.f ep.childNs cOld a1 Sc child ∧
        run (UInt32.ofNat pre.length) (.reuse oldIdx (diff cOld t) :: sRest) a = run (UInt32.ofNat pre.length + 1) sRest (applyToDomM (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) child (diff cOld t) a1).2 ∧
        ∀ newChild, let aMid := (applyToDomM (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) child (diff cOld t) a1).2
          a.nextId ≤ aMid.nextId → (∀ m : Dom.Node, m ≠ ep.parent → ¬Sc m.toNat → m.toNat < a.nextId → aMid.get m = a.get m) →
          ∃ aux', Inv aux' sRest tRest (pre ++ [newChild]) sufRest (fun k => Sdone k ∨ (Sc k ∨ (a.nextId ≤ k ∧ k < aMid.nextId))) Srest aMid) :
    ∀ (steps : List (KeyedStep msg)) (aux : Aux) (targets targetsDone : List (Html msg)) (pre suf : List Dom.Node) (Sdone Srem : Nat → Prop) (a : DomArena msg),
      RecStepCtx ep steps.length targets targetsDone pre suf Sdone a → Inv aux steps targets pre suf Sdone Srem a →
      ep.stepOut steps.length suf.length targets targetsDone pre Sdone Srem a (run (UInt32.ofNat pre.length) steps a) := by
  intro steps; induction steps with
  | nil => intro _ targets _ _ suf Sdone _ a ctx _
           cases targets with | cons _ _ => cases ctx.hlen | nil =>
           rw [hNil]; exact ⟨[], suf, Sdone, rfl, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, by rw [List.append_nil]; exact ctx.hpar, fun _ _ _ _ _ => rfl, fun k hk => ⟨.inl hk, (ctx.hSdone k hk).1⟩, by rw [List.append_nil, List.append_nil]; exact ctx.hDoneC⟩
  | cons step sRest ih =>
      intro aux targets targetsDone pre suf Sdone Srem a ctx hinv
      cases targets with | nil => cases ctx.hlen | cons t tRest =>
      have ⟨hchildNs, hlen, hclean, hdep, hsz, hbound, hparLt, hposId, hpar, hnd, hSdone, hDoneC, hsufB⟩ := ctx
      simp only [List.length_cons] at hlen hsz; simp only [Html.DomCleanList, List.all_cons, Bool.and_eq_true] at hclean
      simp only [htmlListDepth] at hdep; simp only [htmlListNodeCount] at hbound
      have huJNext : UInt32.ofNat pre.length + 1 = UInt32.ofNat (pre.length + 1) := uint32_ofNat_succ pre.length (by omega)
      cases step with
      | create newH =>
          rcases hCreateInv aux newH sRest t tRest pre suf Sdone Srem a hinv with ⟨htEq, hNext⟩; subst htEq
          rcases clean_build_child ep hchildNs hclean.1 (Nat.le_trans (Nat.le_max_left _ _) hdep) (by omega) hparLt hposId hpar with ⟨cn, aMid, hns, hB, hge, _, haGe, haLe, hparMid, hfr, hcl⟩
          have hcnNotIn : cn ∉ pre ++ suf := fun hm => (List.mem_append.1 hm).elim (fun hp => Nat.not_lt.2 hge (hSdone _ (CleanDomChildren_mem hDoneC cn hp)).2) (fun hs => Nat.not_lt.2 hge (hsufB cn hs).1)
          let aIns := aMid.set ep.parent (ep.entry ((pre ++ [cn]) ++ suf)); have haInsNext : aIns.nextId = aMid.nextId := rfl
          have hinsRun : MonadDom.insertBeforeNode (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) cn aMid = ((), aIns) := by
            simp only [MonadDom.insertBeforeNode, DomArena.modifyChildren, DomArena.modify, hparMid, ElemPar.entry, uint32_toNat_ofNat_lt pre.length (by omega), keyed_step_insertBefore_create pre suf cn hnd hcnNotIn, aIns, List.append_assoc, List.singleton_append]
          have hfrIns : ∀ m : Dom.Node, m ≠ ep.parent → m.toNat < a.nextId → aIns.get m = a.get m := fun m h1 h2 => (DomArena.get_set_ne _ _ h1).trans (hfr m h2)
          rcases hNext cn aIns haGe hfrIns with ⟨aux', hinv'⟩
          rw [hCreateRun newH sRest (UInt32.ofNat pre.length) a aIns (fun k => by rw [stateM_bind_step hns, stateM_bind_step hB, stateM_bind_step hinsRun]), huJNext, show pre.length + 1 = (pre ++ [cn]).length by simp only [List.length_append, List.length_singleton]]
          exact clean_step_reconcile_combine (aMid := aIns) (Sdone' := fun k => Sdone k ∨ (a.nextId ≤ k ∧ k < aIns.nextId)) (Nat.le_refl _) haGe haLe (fun _ h => h) (fun _ hk => hk.imp id .inr) (fun _ hD _ hLt h => h.elim hD fun hlo => Nat.not_lt.2 hlo.1 hLt) (fun m h1 _ h2 => hfrIns m h1 h2)
            (ih aux' tRest (targetsDone ++ [newH]) (pre ++ [cn]) suf _ Srem aIns
              ⟨hchildNs, Nat.succ.inj hlen, hclean.2, Nat.le_trans (Nat.le_max_right _ _) hdep, by simp only [List.length_append, List.length_singleton]; omega, by omega, Nat.lt_of_lt_of_le hparLt haGe, Nat.lt_of_lt_of_le hposId haGe,
               DomArena.get_set_self .., nodup_snoc_append hnd hcnNotIn, clean_done_alloc_bounds haGe hparLt hSdone,
               CleanDomChildren_append (fun k hk1 hk2 => Nat.not_lt.2 hk2.1 (hSdone k hk1).2) (CleanDomChildren_frame (fun m hm => hfrIns m (node_ne_of_toNat_ne (hSdone _ hm).1) (hSdone _ hm).2) hDoneC) (DisjointDomList.singleton (hcl _)),
               fun r hr => have hb := hsufB r hr; ⟨Nat.lt_of_lt_of_le hb.1 haGe, hb.2⟩⟩ hinv')
      | reuse oldIdx p =>
          rcases hReuse aux oldIdx p sRest t tRest pre suf Sdone Srem a (Nat.succ.inj hlen) hsz hpar hnd hinv with
            ⟨cOld, child, sufRest, Sc, Srest, a1, rfl, ha1Next, hfr1, hsufLe, hsufSub, hpar1, hnd1, hScB, hSc, hSr, hDisj, hcClean1, hRunStep, hNext⟩
          let aMid := (applyToDomM (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) child (diff cOld t) a1).2
          have hPatchC := hPatch ep.childNs ep.parent ep.pns ep.ptag ep.pst ep.pmg cOld t child pre sufRest Sc a1 hchildNs (by omega)
            (ha1Next ▸ (by omega)) (Nat.le_trans (Nat.le_max_left _ _) hdep) (ha1Next ▸ hparLt) (ha1Next ▸ hposId) hpar1 hnd1
            (fun h => (hScB ep.parent.toNat h).1 rfl) (fun k hk => ha1Next ▸ (hScB k hk).2)
            (fun r hr => ha1Next.symm ▸ (List.mem_append.1 hr).elim (fun hp => (hSdone _ (CleanDomChildren_mem hDoneC r hp)).2) fun hs => (hsufB r (hsufSub r hs)).1) hcClean1 hclean.1
          dsimp only [PatchSpecOut, StateT.run] at hPatchC; rcases hPatchC with ⟨haMidLe, haMidBound, hframeMid, newChild, _, hparMid, hndMid, _, hcNew⟩
          rw [ha1Next] at haMidLe haMidBound hframeMid hcNew
          have hframe : ∀ m : Dom.Node, m ≠ ep.parent → ¬Sc m.toNat → m.toNat < a.nextId → aMid.get m = a.get m := fun m h1 h2 h3 => (hframeMid m h1 h2 h3).trans (hfr1 m h1)
          have ⟨hSdone', hDone'⟩ := clean_done_extend haMidLe hparLt hSdone hScB hDisj (fun m hm => hframe m (node_ne_of_toNat_ne (hSdone _ hm).1) (hDisj _ hm) (hSdone _ hm).2) hDoneC hcNew
          rcases hNext newChild haMidLe hframe with ⟨aux', hinv'⟩
          rw [hRunStep, huJNext, show pre.length + 1 = (pre ++ [newChild]).length by simp only [List.length_append, List.length_singleton]]
          exact clean_step_reconcile_combine hsufLe haMidLe haMidBound hSr (fun k hk => hk.imp id fun h => h.imp (hSc k) id)
            (fun k hD hR hLt => not_Sdone_extend hD (fun hsc => hR (hSc k hsc)) hLt) (fun m h1 hR h2 => hframe m h1 (fun hsc => hR (hSc _ hsc)) h2)
            (ih aux' tRest (targetsDone ++ [t]) (pre ++ [newChild]) sufRest _ Srest aMid
              ⟨hchildNs, Nat.succ.inj hlen, hclean.2, Nat.le_trans (Nat.le_max_right _ _) hdep, by simp only [List.length_append, List.length_singleton]; omega, by dsimp only [aMid]; omega,
               Nat.lt_of_lt_of_le hparLt haMidLe, Nat.lt_of_lt_of_le hposId haMidLe, by simpa only [List.append_assoc, List.singleton_append] using hparMid,
               by simpa only [List.append_assoc, List.singleton_append] using hndMid, hSdone', hDone', fun r hr => have hb := hsufB r (hsufSub r (.tail _ hr)); ⟨Nat.lt_of_lt_of_le hb.1 haMidLe, hb.2⟩⟩ hinv')
private theorem no_reuse_of_allCreates_top : ∀ (xs : List (KeyedStep msg)) (k idx : Nat) (p : Patch msg), allCreates xs = true → xs[k]? = some (.reuse idx p) → False
  | [], _, _, _, _, h | .create _ :: _, 0, _, _, _, h => by simp at h
  | .reuse _ _ :: _, _, _, _, hc, _ => by simp [allCreates] at hc
  | .create _ :: sr, k + 1, idx, p, hc, h => no_reuse_of_allCreates_top sr k idx p hc (by simpa using h)
private theorem positional_reuse_idx : ∀ (base : Nat) (steps : List (KeyedStep msg)) (k idx : Nat) (p : Patch msg), positional base steps = true → steps[k]? = some (.reuse idx p) → idx = base + k
  | _, [], _, _, _, _, h | _, .create _ :: _, 0, _, _, _, h => by simp at h
  | _, .create _ :: rest, k + 1, idx, p, hpos, h => False.elim (no_reuse_of_allCreates_top rest k idx p hpos (by simpa using h))
  | _, .reuse _ _ :: _, 0, _, _, hpos, h => by simp only [List.getElem?_cons_zero, Option.some.injEq, KeyedStep.reuse.injEq] at h; simp only [positional, Bool.and_eq_true, beq_iff_eq] at hpos; omega
  | base, .reuse _ _ :: rest, k + 1, idx, p, hpos, h => by simp only [positional, Bool.and_eq_true] at hpos; have := positional_reuse_idx (base + 1) rest k idx p hpos.2 (by simpa using h); omega
private def PosStepsMatch (base : Nat) (steps : List (KeyedStep msg)) (targets oldRem : List (Html msg)) : Prop :=
  ∀ (k : Nat) (hk : k < targets.length), (∀ newH, steps[k]? = some (.create newH) → newH = targets[k]) ∧ (∀ idx p, steps[k]? = some (.reuse idx p) → idx = base + k ∧ ∃ c, oldRem[k]? = some c ∧ p = diff c targets[k])
private def PosSufClean (f : Nat) (ns : String) : List (KeyedStep msg) → List (Html msg) → DomArena msg → (Nat → Prop) → List Dom.Node → Prop
  | .reuse _ _ :: _, oldRem, a, Srem, suf => CleanDomChildren f ns oldRem a Srem suf | _, _, _, _, _ => True
private theorem applyPositionalStepsM_clean_at0 (ep : ElemPar msg) (hchildNs : ep.childNsOk) (hPatch : @PatchSpecAt msg ep.f) (steps : List (KeyedStep msg)) (c₁ c₂ : List (Html msg)) (domCs : List Dom.Node) (Srem : Nat → Prop) (a : DomArena msg)
    (hsteps : steps.length = c₂.length) (hpos : positional 0 steps = true) (hvalid : DiffStepsValid c₁ c₂ steps) (hclean : Html.DomCleanList c₂ = true) (hdep : htmlListDepth c₂ ≤ ep.f)
    (hbound : a.nextId + htmlListNodeCount c₂ < UInt32.size) (hparLt : ep.parent.toNat < a.nextId) (hposId : 0 < a.nextId) (hpar : a.get ep.parent = ep.entry domCs)
    (hSrem : ∀ k, Srem k → k ≠ ep.parent.toNat ∧ k < a.nextId) (hCleanCs : CleanDomChildren ep.f ep.childNs c₁ a Srem domCs) :
    ep.at0Out steps.length domCs.length c₂ Srem a ((applyPositionalStepsM (m := ArenaM msg) ep.parent 0 steps).run a).2 := by
  rcases cleanChildren_dom_bounds (ep := ep) hsteps hbound hSrem hCleanCs with ⟨hnd, hsufB, _, hsz⟩
  let Inv (oldRem : List (Html msg)) (stps : List (KeyedStep msg)) (tgts : List (Html msg)) (pre suf : List Dom.Node) (Sdone Sr : Nat → Prop) (s : DomArena msg) : Prop :=
    positional pre.length stps = true ∧ PosStepsMatch pre.length stps tgts oldRem ∧ (∀ k, Sr k → k ≠ ep.parent.toNat ∧ k < s.nextId) ∧ (∀ k, Sdone k → Sr k → False) ∧ PosSufClean ep.f ep.childNs stps oldRem s Sr suf
  have hmain := reconcile_steps_spec ep hPatch (fun j stps s => (applyPositionalStepsM (m := ArenaM msg) ep.parent j stps s).2) Inv (fun _ _ => rfl)
    (fun _ _ _ _ _ h => by dsimp only [applyPositionalStepsM]; exact congrArg Prod.snd (h _))
    (fun oldRem newH sRest t tRest pre suf Sdone Sr s ⟨hp, hm, hSr, hD, _⟩ => by
      simp only [positional] at hp; have h0 := hm 0 (Nat.zero_lt_succ _); simp only [List.getElem_cons_zero] at h0
      exact ⟨h0.1 newH rfl, fun _ _ haGe _ => ⟨[], by cases sRest with | nil => rfl | cons s0 _ => cases s0 with | reuse _ _ => cases hp | create _ => exact hp,
        fun k hk => by have hm' := hm (k + 1) (Nat.succ_lt_succ hk); simp only [List.getElem?_cons_succ, List.getElem_cons_succ] at hm'; exact ⟨hm'.1, fun idx' p' hs => False.elim (no_reuse_of_allCreates_top sRest k idx' p' hp hs)⟩,
        fun k hk => have hb := hSr k hk; ⟨hb.1, Nat.lt_of_lt_of_le hb.2 haGe⟩, fun k hk1 hk2 => hk1.elim (fun h => hD k h hk2) fun hhi => Nat.not_lt.2 hhi.1 (hSr k hk2).2,
        by cases sRest with | nil => trivial | cons s0 _ => cases s0 with | create _ => trivial | reuse _ _ => cases hp⟩⟩)
    (fun oldRem oldIdx p sRest t tRest pre suf Sdone Sr s _ hsz' hpar' hnd' ⟨hp, hm, hSr, hD, hsufC⟩ => by
      simp only [PosSufClean] at hsufC; simp only [positional, Bool.and_eq_true, beq_iff_eq] at hp
      have h0 := hm 0 (Nat.zero_lt_succ _); simp only [List.getElem_cons_zero] at h0; rcases h0.2 oldIdx p rfl with ⟨_, cOld, hcOld0, rfl⟩
      cases oldRem with | nil => cases hcOld0 | cons cO oldRest =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hcOld0; subst hcOld0
      cases suf with | nil => exact False.elim hsufC | cons child sufRest =>
      rcases hsufC with ⟨Sc, Srest, hSc, hSr', hDSr, hcClean, hSufClean⟩
      have hchildAt := positional_step_reuse_tail ep.parent ep.pns ep.ptag ep.pst ep.pmg pre child sufRest s (by simp only [List.length_cons] at hsz'; omega)
      dsimp only [StateT.run] at hchildAt; rw [DomArena.set_get_self s hpar'] at hchildAt
      exact ⟨cO, child, sufRest, Sc, Srest, s, rfl, rfl, fun _ _ => rfl, Nat.le_succ _, fun _ h => h, hpar', hnd', fun k h => hSr k (hSc k h), hSc, hSr', fun k h1 h2 => hD k h1 (hSc k h2), hcClean,
        by dsimp only [applyPositionalStepsM]; rw [stateM_bind_step hchildAt, stateM_bind_step (show applyToDomM (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) child (diff cO t) s = ((), _) from rfl)],
        fun newChild haGe hfrMid => ⟨oldRest, by rw [List.length_append, List.length_singleton]; exact hp.2,
          fun k hk => by have hm' := hm (k + 1) (Nat.succ_lt_succ hk); simp only [List.getElem?_cons_succ, List.getElem_cons_succ, List.length_append, List.length_singleton] at hm' ⊢; exact ⟨hm'.1, fun idx' p' hs => let hr := hm'.2 idx' p' hs; ⟨by omega, hr.2⟩⟩,
          fun k hk => have hb := hSr k (hSr' k hk); ⟨hb.1, Nat.lt_of_lt_of_le hb.2 haGe⟩, fun k hk1 hk2 => not_Sdone_extend (fun h1 => hD k h1 (hSr' k hk2)) (fun h => hDSr k h hk2) (hSr k (hSr' k hk2)).2 hk1,
          by cases sRest with | nil => trivial | cons stp _ => cases stp with | create _ => trivial | reuse _ _ => exact CleanDomChildren_frame (fun m hm => hfrMid m (node_ne_of_toNat_ne (hSr _ (hSr' _ hm)).1) (fun hsc => hDSr _ hsc hm) (hSr _ (hSr' _ hm)).2) hSufClean⟩⟩)
    steps c₁ c₂ [] [] domCs (fun _ => False) Srem a ⟨hchildNs, hsteps, hclean, hdep, hsz, hbound, hparLt, hposId, hpar, by simpa using hnd.1, fun _ h => h.elim, trivial, hsufB⟩
    ⟨hpos, fun k hk => ⟨(hvalid.2.1 k hk).1, fun j p hsk => by have hjEq := positional_reuse_idx 0 steps k j p hpos hsk; rcases (hvalid.2.1 k hk).2 j p hsk with ⟨hj, hp⟩; simp only [Nat.zero_add] at hjEq; subst hjEq; exact ⟨(Nat.zero_add j).symm, c₁[j], List.getElem?_eq_getElem hj, hp⟩⟩,
     hSrem, fun _ h => h.elim, by cases steps with | nil => trivial | cons stp _ => cases stp with | create _ => trivial | reuse _ _ => exact hCleanCs⟩
  simpa [ElemPar.stepOut, ElemPar.at0Out, ReconcileStepOut, ReconcileStepAt0Out, StateT.run] using hmain
private theorem replace_child_clean (ep : ElemPar msg) (hchildNs : ep.childNsOk) {newH : Html msg} {node : Dom.Node} {pre suf : List Dom.Node} {Sold : Nat → Prop} {a : DomArena msg}
    (hpreLen : pre.length + 1 + suf.length < UInt32.size) (hbound : a.nextId + htmlNodeCount newH < UInt32.size) (hdep : htmlDepth newH ≤ ep.f) (hparLt : ep.parent.toNat < a.nextId)
    (hpos : 0 < a.nextId) (hpar : a.get ep.parent = ep.entry (pre ++ node :: suf)) (hnd : (pre ++ node :: suf).Nodup) (hparNodesLt : ∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId) (hcleanNew : newH.DomClean = true) :
    let a' := ((applyToDomM (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) node (.replace newH)).run a).2
    a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount newH ∧ (∀ m : Dom.Node, m ≠ ep.parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
    ∃ newNode, (MonadDom.childNamespace (m := ArenaM msg) ep.parent >>= fun ns' => buildDomM (m := ArenaM msg) ns' newH >>= fun n2' => MonadDom.replaceChild (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) n2' >>= fun _ => pure n2') a = (newNode, a') ∧
      a'.get ep.parent = ep.entry (pre ++ newNode :: suf) ∧ (pre ++ newNode :: suf).Nodup ∧ (∀ r ∈ pre ++ newNode :: suf, r.toNat < a'.nextId) ∧ CleanDomSubtree ep.f ep.childNs newH a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) newNode := by
  rcases clean_build_child ep hchildNs hcleanNew hdep hbound hparLt hpos hpar with ⟨n2, aMid, hns, hB, hn2Ge, hn2Lt, haGe, haLe, hparMid, hfr, hcl⟩
  let a' := aMid.set ep.parent (ep.entry (pre ++ n2 :: suf))
  have hrep : MonadDom.replaceChild (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) n2 aMid = ((), a') := by simp [MonadDom.replaceChild, DomArena.modifyChildren, DomArena.modify, hparMid, uint32_toNat_ofNat_lt pre.length (by omega), listReplaceAt_append_middle, a']
  have hrun : applyToDomM (m := ArenaM msg) ep.parent (UInt32.ofNat pre.length) node (.replace newH) a = ((), a') := by dsimp only [applyToDomM]; rw [stateM_bind_step hns, stateM_bind_step hB, hrep]
  dsimp only [StateT.run]; rw [hrun]
  exact ⟨haGe, haLe, fun m hmPar _ hmLt => (DomArena.get_set_ne _ _ hmPar).trans (hfr m hmLt), n2, by rw [stateM_bind_step hns, stateM_bind_step hB, stateM_bind_step hrep]; rfl,
    DomArena.get_set_self .., nodup_append_replace hnd (.inr fun hm => by have := hparNodesLt n2 hm; omega),
    fun r hr => (List.mem_append.1 hr).elim (fun hp => Nat.lt_of_lt_of_le (hparNodesLt r (List.mem_append_left _ hp)) haGe) (fun hc => (List.mem_cons.1 hc).elim (· ▸ hn2Lt) fun hs => Nat.lt_of_lt_of_le (hparNodesLt r (List.mem_append_right _ (.tail _ hs))) haGe), CleanDomSubtree_mono (fun _ => .inr) (hcl _)⟩
private theorem finish_reconcile_removeTail {ep : ElemPar msg} {nSteps domLen : Nat} {c₂ : List (Html msg)} {Srem : Nat → Prop} {a aMid : DomArena msg}
    (hsize : domLen + nSteps < UInt32.size) (hstep : ep.at0Out nSteps domLen c₂ Srem a aMid) :
    ep.tailOut c₂ Srem a ((do let count ← MonadDom.childCount ep.parent; removeTailM (m := ArenaM msg) ep.parent (UInt32.ofNat nSteps) (count.toNat - nSteps)).run aMid).2 := by
  rcases hstep with ⟨targetsOut, sufRem, Snew, hlenT, htotLen, haMidLe, haMidBound, hnodeMid, hfrMid, hSnew, hCleanOut⟩
  simp only [List.length_append] at htotLen
  have hremTail := positional_removeTail_spec aMid ep.parent ep.pns ep.ptag ep.pst ep.pmg targetsOut sufRem (by omega)
  rw [DomArena.set_get_self aMid hnodeMid] at hremTail; dsimp only [ReconcileTailOut, StateT.run] at hremTail ⊢; rw [← hlenT, hremTail]
  exact ⟨targetsOut, Snew, haMidLe, haMidBound, DomArena.get_set_self .., fun m hmPar hmS hmLt => (DomArena.get_set_ne _ _ hmPar).trans (hfrMid m hmPar hmS hmLt),
    hSnew, CleanDomChildren_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSnew m.toNat hm).2)) hCleanOut⟩
def KeyedCleanMatch (c₁ : List (Html msg)) (usedIdxs : List Nat) (steps : List (KeyedStep msg)) (targets : List (Html msg)) : Prop :=
  (∀ (i : Nat) (hi : i < targets.length), (∀ newH, steps[i]? = some (.create newH) → newH = targets[i]) ∧ (∀ j p, steps[i]? = some (.reuse j p) → j ∉ usedIdxs ∧ ∃ _ : j < c₁.length, p = diff c₁[j] targets[i])) ∧
  ∀ i₁ i₂ j₁ j₂ p₁ p₂, i₁ < steps.length → i₂ < steps.length → steps[i₁]? = some (.reuse j₁ p₁) → steps[i₂]? = some (.reuse j₂ p₂) → j₁ = j₂ → i₁ = i₂
private theorem applyKeyedStepsM_fst (parent : Dom.Node) (live : Array Dom.Node) :
    ∀ (steps : List (KeyedStep msg)) (j : Nat) (a : DomArena msg), j + steps.length < UInt32.size → (applyKeyedStepsM (m := ArenaM msg) parent live (UInt32.ofNat j) steps a).1.toNat = j + steps.length
  | [], j, _, h => by simpa [applyKeyedStepsM, pure, StateT.pure] using uint32_toNat_ofNat_lt j h
  | .reuse _ _ :: rest, j, _, h | .create _ :: rest, j, _, h => by
      dsimp only [applyKeyedStepsM, bind, StateT.bind]; rw [uint32_ofNat_succ j (by simp at h; omega)]; repeat' split
      rw [applyKeyedStepsM_fst parent live rest (j + 1) _ (by simp at h; omega)]; simp; omega

theorem applyKeyedStepsM_reconcile_spec (f : Nat) (hPatch : @PatchSpecAt msg f) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (childNs : String) (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (c₁ : List (Html msg)) (live : Array Dom.Node) (Si : Nat → Nat → Prop) (baseLimit : Nat) (_hliveLen : live.size = c₁.length)
    (hSiB : ∀ i k, Si i k → k ≠ parent.toNat ∧ k < baseLimit) (hSiDisj : ∀ i₁ i₂, i₁ ≠ i₂ → ∀ k, Si i₁ k → Si i₂ k → False)
    (hliveInj : ∀ i₁ i₂, i₁ < c₁.length → i₂ < c₁.length → live.getD i₁ 0 = live.getD i₂ 0 → i₁ = i₂)
    (steps : List (KeyedStep msg)) (targets targetsDone : List (Html msg)) (usedIdxs : List Nat) (pre suf : List Dom.Node) (Sdone : Nat → Prop) (a : DomArena msg)
    (hlen : steps.length = targets.length) (hkm : KeyedCleanMatch c₁ usedIdxs steps targets) (hclean : Html.DomCleanList targets = true)
    (hdep : htmlListDepth targets ≤ f) (hsz : pre.length + suf.length + steps.length < UInt32.size) (hbase : baseLimit ≤ a.nextId)
    (hbound : a.nextId + htmlListNodeCount targets < UInt32.size) (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg (pre ++ suf)) (hnd : (pre ++ suf).Nodup) (hSdone : ∀ k, Sdone k → k ≠ parent.toNat ∧ k < a.nextId)
    (hDoneC : CleanDomChildren f childNs targetsDone a Sdone pre)
    (hLive : ∀ (i : Nat) (hi : i < c₁.length), i ∉ usedIdxs → live.getD i 0 ∈ suf ∧ CleanDomSubtree f childNs c₁[i] a (Si i) (live.getD i 0))
    (hDisj : ∀ i, i ∉ usedIdxs → ∀ k, Si i k → Sdone k → False) (hsufB : ∀ r ∈ suf, r.toNat < a.nextId ∧ r ≠ parent) :
    let (finalJ, aOut) := (applyKeyedStepsM (m := ArenaM msg) parent live (UInt32.ofNat pre.length) steps).run a
    finalJ.toNat = pre.length + steps.length ∧ ReconcileStepOut f parent pns ptag pst pmg childNs steps.length suf.length targets targetsDone pre Sdone (fun k => ∃ i, Si i k) a aOut := by
  let ep : ElemPar msg := ⟨f, childNs, parent, pns, ptag, pst, pmg⟩
  let Inv (u : List Nat) (stps : List (KeyedStep msg)) (tgts : List (Html msg)) (_ suf' : List Dom.Node) (Sd Sr : Nat → Prop) (s : DomArena msg) : Prop :=
    Sr = (fun k => ∃ i, Si i k) ∧ KeyedCleanMatch c₁ u stps tgts ∧ baseLimit ≤ s.nextId ∧
    (∀ i (hi : i < c₁.length), i ∉ u → live.getD i 0 ∈ suf' ∧ CleanDomSubtree f childNs c₁[i] s (Si i) (live.getD i 0)) ∧ (∀ i, i ∉ u → ∀ k, Si i k → Sd k → False)
  refine ⟨applyKeyedStepsM_fst parent live steps pre.length a (by omega),
    reconcile_steps_spec ep hPatch (fun j stps s => (applyKeyedStepsM (m := ArenaM msg) parent live j stps s).2) Inv (fun _ _ => rfl)
      (fun _ _ _ _ _ h => by dsimp only [applyKeyedStepsM]; exact congrArg Prod.snd (h _))
      (fun u newH sRest t tRest pre' suf' Sd Sr s ⟨hSrEq, hkm', hb', hL', hD'⟩ => by
        subst hSrEq; have h0 := hkm'.1 0 (Nat.zero_lt_succ _); simp only [List.getElem_cons_zero] at h0
        exact ⟨h0.1 newH rfl, fun _ aIns haGe hfrIns => ⟨u, rfl, ⟨fun i hi => hkm'.1 (i + 1) (Nat.succ_lt_succ hi), fun i₁ i₂ j₁ j₂ p₁ p₂ hi₁ hi₂ h1 h2 hj => Nat.succ.inj (hkm'.2 (i₁ + 1) (i₂ + 1) j₁ j₂ p₁ p₂ (Nat.succ_lt_succ hi₁) (Nat.succ_lt_succ hi₂) h1 h2 hj)⟩,
          Nat.le_trans hb' haGe, fun i hi hnu => let ⟨hs, hcl⟩ := hL' i hi hnu; ⟨hs, CleanDomSubtree_frame (fun m hm => hfrIns m (node_ne_of_toNat_ne (hSiB i m.toNat hm).1) (Nat.lt_of_lt_of_le (hSiB i m.toNat hm).2 hb')) hcl⟩,
          fun i hnu k hsi hk => hk.elim (hD' i hnu k hsi) fun hhi => Nat.not_lt.2 hhi.1 (Nat.lt_of_lt_of_le (hSiB i k hsi).2 hb')⟩⟩)
      (fun u oldIdx p sRest t tRest pre' suf' Sd Sr s hlen' hsz' hpar' hnd' ⟨hSrEq, hkm', hb', hL', hD'⟩ => by
        subst hSrEq; have h0 := hkm'.1 0 (Nat.zero_lt_succ _); simp only [List.getElem_cons_zero] at h0
        rcases h0.2 oldIdx p rfl with ⟨hOldNotUsed, hOldLt, rfl⟩; rcases hL' oldIdx hOldLt hOldNotUsed with ⟨hChildSuf, hChildClean⟩
        let child := live.getD oldIdx 0; let a1 := s.set parent (ep.entry (pre' ++ child :: suf'.erase child))
        have hparIns : MonadDom.insertBeforeNode (m := ArenaM msg) parent (UInt32.ofNat pre'.length) child s = ((), a1) := by
          simp only [MonadDom.insertBeforeNode, DomArena.modifyChildren, DomArena.modify, show s.get parent = .element pns ptag pst pmg (pre' ++ suf') from hpar',
            uint32_toNat_ofNat_lt pre'.length (by omega), w3cInsertBefore_step pre' suf' child hnd' fun hp => (List.nodup_append.1 hnd').2.2 child hp child hChildSuf rfl, a1, ep, ElemPar.entry]
        exact ⟨c₁[oldIdx], child, suf'.erase child, Si oldIdx, fun k => ∃ i, Si i k, a1, rfl, rfl, fun _ => DomArena.get_set_ne _ _, List.length_erase_le,
          fun r hr => (List.mem_cons.1 hr).elim (· ▸ hChildSuf) List.mem_of_mem_erase, DomArena.get_set_self ..,
          by have h := nodup_move_to_pre hnd' hChildSuf (.inl rfl); rw [List.append_assoc, List.singleton_append] at h; exact h,
          fun k h => let hb := hSiB _ k h; ⟨hb.1, Nat.lt_of_lt_of_le hb.2 hb'⟩, fun _ h => ⟨oldIdx, h⟩, fun _ h => h, fun k h1 h2 => hD' oldIdx hOldNotUsed k h2 h1,
          CleanDomSubtree_frame (fun m hm => DomArena.get_set_ne _ _ (node_ne_of_toNat_ne (hSiB oldIdx m.toNat hm).1)) hChildClean,
          by dsimp only [applyKeyedStepsM]; rw [stateM_bind_step hparIns, stateM_bind_step (show applyToDomM (m := ArenaM msg) parent (UInt32.ofNat pre'.length) child (diff c₁[oldIdx] t) a1 = ((), _) from rfl)],
          fun newChild haGe hfrMid => ⟨oldIdx :: u, rfl,
            ⟨fun i hi => ⟨(hkm'.1 (i + 1) (Nat.succ_lt_succ hi)).1, fun j' p' hs => have hm := (hkm'.1 (i + 1) (Nat.succ_lt_succ hi)).2 j' p' hs
              ⟨fun hu => (List.mem_cons.1 hu).elim (fun h0 => Nat.zero_ne_add_one i (hkm'.2 0 (i + 1) oldIdx j' (diff c₁[oldIdx] t) p' (Nat.zero_lt_succ _) (Nat.succ_lt_succ (hlen' ▸ hi)) rfl hs h0.symm)) hm.1, hm.2⟩⟩,
             fun i₁ i₂ j₁ j₂ p₁ p₂ hi₁ hi₂ h1 h2 hj => Nat.succ.inj (hkm'.2 (i₁ + 1) (i₂ + 1) j₁ j₂ p₁ p₂ (Nat.succ_lt_succ hi₁) (Nat.succ_lt_succ hi₂) h1 h2 hj)⟩,
            Nat.le_trans hb' haGe,
            fun i hi hnu => have hneIdx : i ≠ oldIdx := fun h => hnu (h ▸ .head _); have ⟨hInSuf, hCleanI⟩ := hL' i hi fun h => hnu (.tail _ h)
              ⟨(List.mem_erase_of_ne fun hEq => hneIdx (hliveInj i oldIdx hi hOldLt hEq)).2 hInSuf, CleanDomSubtree_frame (fun m hm => let hSi := hSiB i m.toNat hm; hfrMid m (node_ne_of_toNat_ne hSi.1) (hSiDisj i oldIdx hneIdx m.toNat hm) (Nat.lt_of_lt_of_le hSi.2 hb')) hCleanI⟩,
            fun i hi k hsi hk => not_Sdone_extend (hD' i (fun h => hi (.tail _ h)) k hsi) (hSiDisj i oldIdx (fun h => hi (h ▸ .head _)) k hsi) (Nat.lt_of_lt_of_le (hSiB i k hsi).2 hb') hk⟩⟩)
      steps usedIdxs targets targetsDone pre suf Sdone (fun k => ∃ i, Si i k) a ⟨hchildNs, hlen, hclean, hdep, hsz, hbound, hparLt, hposId, hpar, hnd, hSdone, hDoneC, hsufB⟩ ⟨rfl, hkm, hbase, hLive, hDisj⟩⟩
theorem applyKeyedStepsM_with_removeTail_spec (f : Nat) (hPatch : @PatchSpecAt msg f) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (childNs : String) (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (steps : List (KeyedStep msg)) (c₁ c₂ : List (Html msg)) (domCs : List Dom.Node) (Srem : Nat → Prop) (a : DomArena msg)
    (hvalid : DiffStepsValid c₁ c₂ steps) (hclean : Html.DomCleanList c₂ = true) (hdep : htmlListDepth c₂ ≤ f) (hbound : a.nextId + htmlListNodeCount c₂ < UInt32.size)
    (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId) (hpar : a.get parent = .element pns ptag pst pmg domCs)
    (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) (hCleanCs : CleanDomChildren f childNs c₁ a Srem domCs) :
    ReconcileTailOut f parent pns ptag pst pmg childNs c₂ Srem a
      ((do let live ← snapshotChildrenM parent 0 #[] domCs.length; let finalJ ← applyKeyedStepsM parent live 0 steps; let count ← MonadDom.childCount parent; removeTailM (m := ArenaM msg) parent finalJ (count.toNat - finalJ.toNat)).run a).2 := by
  let ep : ElemPar msg := ⟨f, childNs, parent, pns, ptag, pst, pmg⟩
  rcases cleanChildren_dom_bounds (ep := ep) hvalid.1 hbound hSrem hCleanCs with ⟨hnd, hsufB, hdomLe, hsz⟩
  rcases CleanDomChildren_indexed hCleanCs with ⟨Si, hSiSub, hSiDisj, hSiGet⟩
  let live : Array Dom.Node := { toList := domCs }
  have hsnap : snapshotChildrenM (m := ArenaM msg) parent 0 #[] domCs.length a = (live, a) := by
    have hs := snapshotChildrenM_spec a parent pns ptag pst pmg domCs (by omega) 0 domCs.length #[] (by simp); rw [DomArena.set_get_self a hpar] at hs; simpa [live, StateT.run] using hs
  have hres := applyKeyedStepsM_reconcile_spec f hPatch parent pns ptag pst pmg childNs hchildNs c₁ live Si a.nextId (by simp [live, hnd.2])
    (fun i k hk => hSrem k (hSiSub i k hk)) hSiDisj (fun i₁ i₂ hi₁ hi₂ hEq => by simp [live, Array.getD, hnd.2, hi₁, hi₂] at hEq; exact nodup_getElem_inj (hnd.2 ▸ hi₁) (hnd.2 ▸ hi₂) hnd.1 hEq)
    steps c₂ [] [] [] domCs (fun _ => False) a hvalid.1 ⟨fun i hi => ⟨(hvalid.2.1 i hi).1, fun j p hs => ⟨(fun hm => nomatch hm), (hvalid.2.1 i hi).2 j p hs⟩⟩, hvalid.2.2⟩
    hclean hdep hsz (Nat.le_refl _) hbound hparLt hposId hpar (by simpa using hnd.1) (fun _ h => h.elim) trivial
    (fun i hi _ => ⟨by simp [live, Array.getD, hnd.2, hi], by rw [show live.getD i 0 = domCs[i]'(hnd.2 ▸ hi) by simp [live, Array.getD, hnd.2, hi]]; exact hSiGet i hi (hnd.2 ▸ hi)⟩) (fun _ _ _ _ h => h.elim) hsufB
  simp only [List.length_nil, show (UInt32.ofNat 0 : Dom.Node) = 0 from rfl, ReconcileStepOut, StateT.run, Nat.zero_add] at hres
  cases hK : applyKeyedStepsM (m := ArenaM msg) parent live 0 steps a with
  | mk finalJ aMid =>
      rw [hK] at hres; rcases hres with ⟨hfjNat, targetsOut, sufRem, Snew, hlenT, htotLen, haMidLe, haMidBound, hnodeMid, hfrMid, hSnew, hCleanOut⟩
      simp only [List.nil_append] at hnodeMid hCleanOut
      have hfin := finish_reconcile_removeTail (ep := ep) (nSteps := steps.length) (domLen := domCs.length) (c₂ := c₂) (Srem := Srem) (a := a) (by simp at hsz; omega)
        ⟨targetsOut, sufRem, Snew, hlenT, htotLen, haMidLe, haMidBound, hnodeMid, fun m hmPar hmS hmLt => hfrMid m hmPar (fun h => h.elim) (fun ⟨i, hsi⟩ => hmS (hSiSub i m.toNat hsi)) hmLt,
          fun k hk => by rcases hSnew k hk with ⟨hF | ⟨i, hSi⟩ | hA, hnp⟩; exact hF.elim; exact ⟨.inl (hSiSub i k hSi), hnp⟩; exact ⟨.inr hA, hnp⟩, hCleanOut⟩
      have hfjEq : finalJ = UInt32.ofNat steps.length := uint32_eq_of_toNat_eq (by rw [hfjNat, uint32_toNat_ofNat_lt _ (by simp at hsz; omega)])
      dsimp only [StateT.run, bind, StateT.bind] at hfin ⊢; rw [hsnap]; dsimp only; rw [hK, hfjEq]; dsimp only; rwa [uint32_toNat_ofNat_lt steps.length (by simp at hsz; omega)]

theorem applyToDomM_spec (fuel : Nat) : @PatchSpecAt msg fuel := by
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ newH _ _ _ _ _ _ _ _ hdep; cases newH <;> simp [htmlDepth] at hdep
  | succ f ih =>
      intro childNs parent pns ptag pst pmg oldH newH node pre suf Sold a hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hcleanOld hcleanNew
      have hReplace : diff oldH newH = .replace newH →
          PatchSpecOut (f + 1) childNs parent pns ptag pst pmg oldH newH node pre suf Sold a ((applyToDomM (m := ArenaM msg) parent (UInt32.ofNat pre.length) node (diff oldH newH)).run a).2 := fun hd => by
        rcases replace_child_clean ⟨f + 1, childNs, parent, pns, ptag, pst, pmg⟩ hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparNodes hcleanNew with ⟨hle, hbd, hfr, n2, _, hpar', hnd', hnodes', hcl'⟩
        dsimp only [PatchSpecOut]; rw [hd]; exact ⟨hle, hbd, hfr, n2, .inl rfl, hpar', hnd', hnodes', hcl'⟩
      cases oldH with
      | text sOld => cases newH with
        | element _ _ _ => exact hReplace rfl
        | text sNew =>
            rcases hcleanOld with ⟨hnodeIn, hnodeGet⟩; dsimp only [PatchSpecOut, diff, applyToDomM, StateT.run, MonadDom.setText, DomArena.modify]; rw [hnodeGet]; dsimp only
            exact ⟨Nat.le_refl _, by simp only [htmlNodeCount, DomArena.nextId_set]; exact Nat.le_add_right .., fun m _ hmOut _ => DomArena.get_set_ne _ _ fun e => hmOut (congrArg UInt32.toNat e ▸ hnodeIn),
              node, .inr rfl, by rw [DomArena.get_set_ne _ _ (show parent ≠ node from fun h => hparOut (h ▸ hnodeIn)), hpar], hnd, hparNodes, .inl hnodeIn, DomArena.get_set_self ..⟩
      | element t₁ a₁ c₁ => cases newH with
        | text _ => exact hReplace rfl
        | element t₂ a₂ c₂ =>
            by_cases ht : t₁ = t₂
            · subst ht; rcases hcleanOld with ⟨hnodeIn, _, _, st, mg, domCs, hnodeGet, hElClean, _, _, hCleanCs⟩
              simp only [Html.DomClean_element, Bool.and_eq_true] at hcleanNew; rcases hcleanNew with ⟨⟨hownNewT, ha₂Clean⟩, hc₂Clean⟩
              have hownNewF : ownsChildren a₂ = false := Bool.not_eq_true' _ ▸ hownNewT
              simp only [htmlNodeCount] at hbound; simp only [htmlDepth] at hdep
              have hne : node ≠ parent := fun h => hparOut (h ▸ hnodeIn); have hnodeLt : node.toNat < a.nextId := hSoldLt _ hnodeIn
              let realNs := if childNs == "" && t₁ == "svg" then Dom.svgNs else childNs
              have hccNs := childNamespace_eq_childNsOf (ptag := t₁) (show childNs = "" ∨ childNs = Dom.svgNs by rw [hchildNs]; split <;> simp)
              have hattrs := ElemClean_applyAttrsM a node realNs t₁ st mg domCs a₂ hElClean ha₂Clean
              rw [DomArena.set_get_self a hnodeGet] at hattrs; rcases hattrs with ⟨st', ha1Get, ha1Equiv, hElClean'⟩
              let mg' := (normalizeAttrs a₂).filterMap managedAttrName; let a1 := (applyAttrsM (m := ArenaM msg) node a₂ a).2
              have ha1Next : a1.nextId = a.nextId := (applyAttrsM_preserves a node a₂).1; have ha1Ne : ∀ m, m ≠ node → a1.get m = a.get m := (applyAttrsM_preserves a node a₂).2
              have hCleanCs1 := CleanDomChildren_frame (fun m hm => ha1Ne m (node_ne_of_toNat_ne hm.2)) hCleanCs
              have hdomLe : domCs.length ≤ a1.nextId := nodup_nodes_lt_length_le a1.nextId domCs (CleanDomChildren_nodup hCleanCs).1 fun r hr => ha1Next.symm ▸ hSoldLt _ (CleanDomChildren_mem hCleanCs r hr).1
              have ⟨steps, hdiffEq⟩ : ∃ steps, diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂) = .patchElement a₂ steps := by
                cases h : diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂) with
                | replace _ | setText _ => simp [diff] at h
                | patchElement a₂' s => obtain ⟨rfl, _⟩ : a₂ = a₂' ∧ True := ⟨by simp [diff] at h; exact h.1, trivial⟩; exact ⟨s, rfl⟩
              have hvalid := diff_steps_valid hdiffEq; have hSrem : ∀ k, (Sold k ∧ k ≠ node.toNat) → k ≠ node.toNat ∧ k < a1.nextId := fun k hk => ⟨hk.2, ha1Next.symm ▸ hSoldLt k hk.1⟩
              let epC : ElemPar msg := ⟨f, Dom.childNsOf childNs t₁, node, realNs, t₁, st', mg'⟩
              have hRec : epC.tailOut c₂ (fun k => Sold k ∧ k ≠ node.toNat) a1 ((applyToDomM (m := ArenaM msg) parent (UInt32.ofNat pre.length) node (diff (.element t₁ a₁ c₁) (.element t₁ a₂ c₂))).run a).2 := by
                dsimp only [StateT.run]; rw [hdiffEq]; dsimp only [applyToDomM, bind, StateT.bind, pure, StateT.pure]
                rw [show applyAttrsM (m := ArenaM msg) node a₂ a = ((), a1) from rfl]; dsimp only; simp only [hownNewF, Bool.false_eq_true, ↓reduceIte, StateT.bind, bind, MonadDom.childCount]; rw [ha1Get]; dsimp only
                by_cases hposSt : positional 0 steps = true
                · simp only [hposSt, ↓reduceIte]; rcases cleanChildren_dom_bounds (ep := epC) hvalid.1 (by omega) hSrem hCleanCs1 with ⟨_, _, _, hsz⟩
                  have hfin := finish_reconcile_removeTail (ep := epC) (by simp at hsz; omega)
                    (applyPositionalStepsM_clean_at0 epC hccNs.symm ih steps c₁ c₂ domCs _ a1 hvalid.1 hposSt hvalid hc₂Clean (by dsimp only [epC]; omega) (by omega) (by dsimp only [epC]; omega) (by omega) ha1Get hSrem hCleanCs1)
                  dsimp only [StateT.run, bind, StateT.bind] at hfin ⊢; cases hP : applyPositionalStepsM (m := ArenaM msg) node 0 steps a1; rw [hP] at hfin; exact hfin
                · simp only [Bool.eq_false_iff.2 hposSt, Bool.false_eq_true, ↓reduceIte, show (UInt32.ofNat domCs.length).toNat = domCs.length from uint32_toNat_ofNat_lt _ (by omega)]
                  exact applyKeyedStepsM_with_removeTail_spec f ih node realNs t₁ st' mg' (Dom.childNsOf childNs t₁) hccNs.symm steps c₁ c₂ domCs _ a1 hvalid hc₂Clean (by omega) (by omega) (by omega) (by omega) ha1Get hSrem hCleanCs1
              rcases hRec with ⟨targetsOut, Snew, haOutGe, haOutBound, hnodeOut, hfrOut, hSnew, hCleanOut⟩
              exact ⟨by omega, by simp only [htmlNodeCount]; omega,
                fun m _ hmOut hmLt => let hmNe : m ≠ node := fun h => hmOut (h ▸ hnodeIn); (hfrOut m hmNe (fun h => hmOut h.1) (by omega)).trans (ha1Ne m hmNe),
                node, .inr rfl, by rw [hfrOut parent hne.symm (fun h => hparOut h.1) (by omega), ha1Ne parent hne.symm, hpar], hnd,
                fun r hr => Nat.lt_of_lt_of_le (hparNodes r hr) (by omega), .inl hnodeIn, hownNewF, ha₂Clean, st', mg', targetsOut, hnodeOut, hElClean',
                ha1Equiv, fun _ => List.contains_iff_mem.2, CleanDomChildren_mono (fun k hk => ⟨(hSnew k hk).1.elim (fun h => .inl h.1) (fun h => .inr ⟨by omega, h.2⟩), (hSnew k hk).2⟩) hCleanOut⟩
            · exact hReplace (by simp [diff, ht])
theorem applyPositionalStepsM_spec (f : Nat) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (childNs : String) (hchildNs : childNs = if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else "")
    (steps : List (KeyedStep msg)) (c₁ c₂ : List (Html msg)) (domCs : List Dom.Node) (Srem : Nat → Prop) (a : DomArena msg)
    (hsteps : steps.length = c₂.length) (hpos : positional 0 steps = true) (hvalid : DiffStepsValid c₁ c₂ steps) (hclean : Html.DomCleanList c₂ = true)
    (hdep : htmlListDepth c₂ ≤ f) (hbound : a.nextId + htmlListNodeCount c₂ < UInt32.size) (hparLt : parent.toNat < a.nextId) (hposId : 0 < a.nextId)
    (hpar : a.get parent = .element pns ptag pst pmg domCs) (hSrem : ∀ k, Srem k → k ≠ parent.toNat ∧ k < a.nextId) (hCleanCs : CleanDomChildren f childNs c₁ a Srem domCs) :
    ReconcileStepAt0Out f parent pns ptag pst pmg childNs steps.length domCs.length c₂ Srem a ((applyPositionalStepsM (m := ArenaM msg) parent 0 steps).run a).2 :=
  applyPositionalStepsM_clean_at0 ⟨f, childNs, parent, pns, ptag, pst, pmg⟩ hchildNs (applyToDomM_spec f) steps c₁ c₂ domCs Srem a hsteps hpos hvalid hclean hdep hbound hparLt hposId hpar hSrem hCleanCs

theorem patchHtmlSubtreeM_spec (f : Nat) (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (oldH newH : Html msg) (node : Dom.Node) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg)
    (hchildNs : childNs = (if pns == Dom.svgNs && ptag != "foreignObject" then Dom.svgNs else ""))
    (hpreLen : pre.length + 1 + suf.length < UInt32.size) (hbound : a.nextId + htmlNodeCount newH < UInt32.size) (hdep : htmlDepth newH ≤ f)
    (hparLt : parent.toNat < a.nextId) (hpos : 0 < a.nextId) (hpar : a.get parent = .element pns ptag pst pmg (pre ++ node :: suf)) (hnd : (pre ++ node :: suf).Nodup)
    (hparOut : ¬Sold parent.toNat) (hSoldLt : ∀ k, Sold k → k < a.nextId) (hparNodes : ∀ r ∈ pre ++ node :: suf, r.toNat < a.nextId)
    (hcleanOld : CleanDomSubtree f childNs oldH a Sold node) (hcleanNew : newH.DomClean = true) :
    let (newNode, a') := (patchHtmlSubtreeM (m := ArenaM msg) parent (UInt32.ofNat pre.length) node oldH newH).run a
    a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount newH ∧ (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
    a'.get parent = .element pns ptag pst pmg (pre ++ newNode :: suf) ∧ (pre ++ newNode :: suf).Nodup ∧ (∀ r ∈ pre ++ newNode :: suf, r.toNat < a'.nextId) ∧
    CleanDomSubtree f childNs newH a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) newNode ∧ DomTreeAssocEquiv (readDomTree f a' newNode) (specDom childNs newH) := by
  have hSpec := applyToDomM_spec f childNs parent pns ptag pst pmg oldH newH node pre suf Sold a hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparOut hSoldLt hparNodes hcleanOld hcleanNew
  dsimp only [PatchSpecOut, StateT.run] at hSpec
  cases hd : diff oldH newH with
  | replace h2 =>
      have h2Eq : h2 = newH := by
        cases oldH <;> cases newH <;> simp [diff] at hd <;> try (subst hd; rfl)
        split at hd <;> simp at hd; subst hd; rfl
      subst h2Eq; rcases replace_child_clean ⟨f, childNs, parent, pns, ptag, pst, pmg⟩ hchildNs hpreLen hbound hdep hparLt hpos hpar hnd hparNodes hcleanNew with ⟨hle, hbd, hfr, n2, hEqRun, hpar', hnd', hnodes', hcl'⟩
      dsimp only [patchHtmlSubtreeM, StateT.run]; rw [hd]; dsimp only; rw [hEqRun]
      exact ⟨hle, hbd, hfr, hpar', hnd', hnodes', hcl', CleanDomSubtree_equiv hcl'⟩
  | setText _ | patchElement _ _ =>
      rw [hd] at hSpec; rcases hSpec with ⟨hle, hbd, hfr, newNode, hEq, hpar', hnd', hnodes', hcl'⟩; rcases hEq with hc | rfl; cases hc
      dsimp only [patchHtmlSubtreeM, StateT.run, bind, StateT.bind, pure, StateT.pure]; rw [hd]; dsimp only
      exact ⟨hle, hbd, hfr, hpar', hnd', hnodes', hcl', CleanDomSubtree_equiv hcl'⟩

end Qed
