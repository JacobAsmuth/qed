import Qed.Proofs.DomSubtree
import Qed.Proofs.ViewPatch.Attrs

namespace Qed

section
variable {σ msg : Type}

mutual
  def VStateMatches : View σ msg → σ → DomArena msg → Dom.Node → VState σ msg → Prop
    | .text _, _, _, n, .text n' | .static _, _, _, n, .stat n' => n' = n
    | .dyn get, s, _, n, .dyn n' last => n' = n ∧ last = get s
    | .dynNode get, s, _, n, .dynNode n' last => n' = n ∧ last = get s
    | .memo sm, s, _, n, .memo n' lk lh => n' = n ∧ lk = sm.keyOf s ∧ lh = sm.eval s
    | .ifElse c y no, s, a, n, .cond wy inner => wy = c s ∧ (if c s then VStateMatches y s a n inner else VStateMatches no s a n inner)
    | .element _ _ kids, s, a, n, .elem n' ks => n' = n ∧ ∃ ns' tag' st mg domCs, a.get n = .element ns' tag' st mg domCs ∧ VStateKidsMatches kids s a domCs ks
    | .keyedList _ _ keys _ _ _ rowsHtml none, s, _, n, .list n' oldKeys _ oldRowsL _ _ => n' = n ∧ oldKeys = disambiguateKeys (keys s) ∧ oldRowsL = rowsHtml s
    | _, _, _, _, _ => False

  def VStateKidsMatches : List (View σ msg) → σ → DomArena msg → List Dom.Node → List (VState σ msg) → Prop
    | [], _, _, [], [] => True
    | k :: ks, s, a, d :: ds, kst :: ksts => d = kst.rootNode ∧ VStateMatches k s a d kst ∧ VStateKidsMatches ks s a ds ksts
    | _, _, _, _, _ => False
end

def VStateValid (f : Nat) (ns : String) (v : View σ msg) (s : σ) (a : DomArena msg) (S : Nat → Prop) (vst : VState σ msg) : Prop :=
  CleanDomSubtree f ns (View.render v s) a S vst.rootNode ∧ VStateMatches v s a vst.rootNode vst

mutual
  theorem VStateMatches_frame :
      ∀ {f : Nat} {ns : String} {v : View σ msg} {s : σ} {a a' : DomArena msg} {S : Nat → Prop} {n : Dom.Node} {vst : VState σ msg},
        (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) → CleanDomSubtree f ns (View.render v s) a S n → VStateMatches v s a n vst → VStateMatches v s a' n vst
    | _, _, .ifElse c _ _, _, _, _, _, _, vst, hfr, hcl, h => by
        cases vst with | cond _ _ => rcases h with ⟨hwy, hin⟩; exact ⟨hwy, by cases hc : c _ <;> simp only [hc, ↓reduceIte, Bool.false_eq_true, View.render] at hcl hin ⊢ <;> exact VStateMatches_frame hfr hcl hin⟩ | _ => exact False.elim h
    | f, _, .element _ _ _, _, _, _, _, n, vst, hfr, hcl, h => by
        cases vst with
        | elem _ _ => cases f with | zero => exact False.elim hcl | succ _ =>
            rcases h with ⟨hn, _, _, _, _, _, hget, hks⟩; rcases hcl with ⟨hmem, _, _, _, _, _, hget', _, _, _, hcs⟩
            rw [hget'] at hget; cases hget; exact ⟨hn, _, _, _, _, _, (hfr n hmem).trans hget', VStateKidsMatches_frame (fun m hm => hfr m hm.1) hcs hks⟩
        | _ => exact False.elim h
    | _, _, .text _, _, _, _, _, _, vst, _, _, h | _, _, .dyn _, _, _, _, _, _, vst, _, _, h | _, _, .static _, _, _, _, _, _, vst, _, _, h
    | _, _, .dynNode _, _, _, _, _, _, vst, _, _, h | _, _, .memo _, _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | _, _, .keyedList _ _ _ _ _ _ _ t, _, _, _, _, _, vst, _, _, h => by cases t <;> cases vst <;> exact h
  theorem VStateKidsMatches_frame :
      ∀ {f : Nat} {ns : String} {ks : List (View σ msg)} {s : σ} {a a' : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node} {ksts : List (VState σ msg)},
        (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) → CleanDomChildren f ns (View.renderEach ks s) a S ds → VStateKidsMatches ks s a ds ksts → VStateKidsMatches ks s a' ds ksts
    | _, _, [], _, _, _, _, [], [], _, _, h => h
    | _, _, _ :: _, _, _, _, _, _ :: _, _ :: _, hfr, ⟨_, _, hSc, hSr, _, hHd, hTl⟩, ⟨hr, hm, hkt⟩ =>
        ⟨hr, VStateMatches_frame (fun m h => hfr m (hSc _ h)) hHd hm, VStateKidsMatches_frame (fun m h => hfr m (hSr _ h)) hTl hkt⟩
    | _, _, [], _, _, _, _, _ :: _, _, _, hc, _ | _, _, _ :: _, _, _, _, _, [], _, _, hc, _ => False.elim hc
    | _, _, [], _, _, _, _, [], _ :: _, _, _, h | _, _, _ :: _, _, _, _, _, _ :: _, [], _, _, h => False.elim h
end

section
variable {f : Nat} {ns : String} {v : View σ msg} {s : σ} {a : DomArena msg} {S : Nat → Prop} {vst : VState σ msg}
theorem VStateValid_root_mem (h : VStateValid f ns v s a S vst) : S vst.rootNode.toNat := CleanDomSubtree_root_mem h.1
theorem VStateValid_equiv (h : VStateValid f ns v s a S vst) : DomTreeAssocEquiv (readDomTree f a vst.rootNode) (specDom ns (View.render v s)) := CleanDomSubtree_equiv h.1
theorem VStateValid_mono {S' : Nat → Prop} (hsub : ∀ k, S k → S' k) (h : VStateValid f ns v s a S vst) : VStateValid f ns v s a S' vst := ⟨CleanDomSubtree_mono hsub h.1, h.2⟩
theorem VStateValid_frame {a' : DomArena msg} (hfr : ∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) (h : VStateValid f ns v s a S vst) : VStateValid f ns v s a' S vst := ⟨CleanDomSubtree_frame hfr h.1, VStateMatches_frame hfr h.1 h.2⟩
end

theorem View.ind {P : View σ msg → Prop}
    (text : ∀ str, P (.text str)) (dyn : ∀ get, P (.dyn get)) (static : ∀ h, P (.static h))
    (dynNode : ∀ get, P (.dynNode get)) (memo : ∀ sm, P (.memo sm)) (ifElse : ∀ c y n, P y → P n → P (.ifElse c y n))
    (element : ∀ tag attrs kids, (∀ k ∈ kids, P k) → P (.element tag attrs kids))
    (keyedList : ∀ tag attrs keys marks rowSig rowEv rowsHtml tmpl?, P (.keyedList tag attrs keys marks rowSig rowEv rowsHtml tmpl?)) : ∀ v, P v
  | .text s => text s | .dyn g => dyn g | .static h => static h | .dynNode g => dynNode g | .memo sm => memo sm | .keyedList .. => keyedList ..
  | .ifElse c y n => ifElse c y n (View.ind text dyn static dynNode memo ifElse element keyedList y) (View.ind text dyn static dynNode memo ifElse element keyedList n)
  | .element tag attrs kids => element tag attrs kids fun k hk =>
      have : sizeOf k < sizeOf (View.element tag attrs kids) := by have := List.sizeOf_lt_of_mem hk; simp only [View.element.sizeOf_spec]; omega
      View.ind text dyn static dynNode memo ifElse element keyedList k
termination_by v => sizeOf v

theorem keyedRows_eq_of_keys_eq {keys : σ → Array String} {rowsHtml : σ → List (Html msg)} (hr : KeyedRowsClean keys rowsHtml)
    {s₁ s₂ : σ} (hk : disambiguateKeys (keys s₂) = disambiguateKeys (keys s₁)) : rowsHtml s₁ = rowsHtml s₂ :=
  List.ext_getElem? fun i => if hi : i < (disambiguateKeys (keys s₁)).size then hr.2.2.2 s₁ s₂ i i hi (hk ▸ hi) (by simp [hk])
    else by rw [List.getElem?_eq_none (by rw [hr.1 s₁]; omega), List.getElem?_eq_none (by rw [hr.1 s₂, hk]; omega)]

theorem down_ind {n : Nat} {P : ∀ i, i ≤ n → Prop} (base : P n (Nat.le_refl n)) (step : ∀ i (hlt : i < n), P (i + 1) hlt → P i (Nat.le_of_lt hlt)) :
    ∀ i (hle : i ≤ n), P i hle := fun i hle => by
  induction h : n - i generalizing i with
  | zero => cases Nat.le_antisymm hle (Nat.sub_eq_zero_iff_le.1 h); exact base
  | succ k ih =>
      have hlt : i < n := Nat.lt_of_sub_pos (h.symm ▸ Nat.succ_pos k)
      exact step i hlt (ih (i + 1) hlt ((Nat.sub_add_eq n i 1).trans (by rw [h]; exact Nat.add_sub_cancel k 1)))

abbrev PatchViewPost (f : Nat) (childNs : String) (parent : Dom.Node) (pns ptag : String) (pst : SpecElemState msg) (pmg : List String)
    (v : View σ msg) (s₂ : σ) (pre suf : List Dom.Node) (Sold : Nat → Prop) (a : DomArena msg) (res : VState σ msg × DomArena msg) : Prop :=
  let (vst', a') := res
  a.nextId ≤ a'.nextId ∧ a'.nextId ≤ a.nextId + htmlNodeCount (View.render v s₂) ∧
  (∀ m : Dom.Node, m ≠ parent → ¬Sold m.toNat → m.toNat < a.nextId → a'.get m = a.get m) ∧
  a'.get parent = .element pns ptag pst pmg (pre ++ vst'.rootNode :: suf) ∧ (pre ++ vst'.rootNode :: suf).Nodup ∧
  (∀ r ∈ pre ++ vst'.rootNode :: suf, r.toNat < a'.nextId) ∧
  VStateValid f childNs v s₂ a' (fun k => Sold k ∨ (a.nextId ≤ k ∧ k < a'.nextId)) vst' ∧
  DomTreeAssocEquiv (readDomTree f a' vst'.rootNode) (specDom childNs (View.render v s₂))

abbrev ElemPar.patchViewPost (ep : ElemPar msg) (v : View σ msg) :=
  PatchViewPost ep.f ep.childNs ep.parent ep.pns ep.ptag ep.pst ep.pmg v

end
end Qed
