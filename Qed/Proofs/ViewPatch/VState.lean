import Qed.Proofs.DomSubtree
import Qed.Proofs.ViewPatch.Attrs

namespace Qed

mutual
  def VStateMatches {σ msg : Type} : View σ msg → σ → DomArena msg → Dom.Node → VState σ msg → Prop
    | .text _, _, _, n, .text n' => n' = n
    | .dyn get, s, _, n, .dyn n' last => n' = n ∧ last = get s
    | .static _, _, _, n, .stat n' => n' = n
    | .dynNode get, s, _, n, .dynNode n' last => n' = n ∧ last = get s
    | .memo sm, s, _, n, .memo n' lk lh => n' = n ∧ lk = sm.keyOf s ∧ lh = sm.eval s
    | .ifElse c y no, s, a, n, .cond wy inner =>
        wy = c s ∧ (if c s then VStateMatches y s a n inner else VStateMatches no s a n inner)
    | .element _ _ kids, s, a, n, .elem n' ks =>
        n' = n ∧ ∃ ns' tag' st mg domCs, a.get n = .element ns' tag' st mg domCs ∧
          VStateKidsMatches kids s a domCs ks
    | .keyedList _ _ keys _ _ _ rowsHtml none, s, _, n, .list n' oldKeys _ oldRowsL _ _ =>
        n' = n ∧ oldKeys = disambiguateKeys (keys s) ∧ oldRowsL = rowsHtml s
    | _, _, _, _, _ => False

  def VStateKidsMatches {σ msg : Type} :
      List (View σ msg) → σ → DomArena msg → List Dom.Node → List (VState σ msg) → Prop
    | [], _, _, [], [] => True
    | k :: ks, s, a, d :: ds, kst :: ksts =>
        d = kst.rootNode ∧ VStateMatches k s a d kst ∧ VStateKidsMatches ks s a ds ksts
    | _, _, _, _, _ => False
end

def VStateValid {σ msg : Type} (f : Nat) (ns : String) (v : View σ msg) (s : σ)
    (a : DomArena msg) (S : Nat → Prop) (vst : VState σ msg) : Prop :=
  CleanDomSubtree f ns (View.render v s) a S vst.rootNode ∧ VStateMatches v s a vst.rootNode vst

theorem VStateValid_root_mem {σ msg : Type} {f : Nat} {ns : String} {v : View σ msg} {s : σ}
    {a : DomArena msg} {S : Nat → Prop} {vst : VState σ msg} (h : VStateValid f ns v s a S vst) :
    S vst.rootNode.toNat := CleanDomSubtree_root_mem h.1

theorem VStateValid_equiv {σ msg : Type} {f : Nat} {ns : String} {v : View σ msg} {s : σ}
    {a : DomArena msg} {S : Nat → Prop} {vst : VState σ msg} (h : VStateValid f ns v s a S vst) :
    DomTreeAssocEquiv (readDomTree f a vst.rootNode) (specDom ns (View.render v s)) := CleanDomSubtree_equiv h.1

mutual
  theorem VStateMatches_frame {σ msg : Type} :
      ∀ {f : Nat} {ns : String} {v : View σ msg} {s : σ} {a a' : DomArena msg} {S : Nat → Prop} {n : Dom.Node} {vst : VState σ msg},
        (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) →
        CleanDomSubtree f ns (View.render v s) a S n → VStateMatches v s a n vst → VStateMatches v s a' n vst
    | _, _, .text _, _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | _, _, .dyn _, _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | _, _, .static _, _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | _, _, .dynNode _, _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | _, _, .memo _, _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | _, _, .keyedList _ _ _ _ _ _ _ none, _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | _, _, .keyedList _ _ _ _ _ _ _ (some _), _, _, _, _, _, vst, _, _, h => by cases vst <;> exact h
    | f, ns, .ifElse c y no, s, a, a', S, n, vst, hfr, hcl, h => by
        cases vst with
        | cond wy inner =>
            rcases h with ⟨hwy, hin⟩
            refine ⟨hwy, ?_⟩
            cases hc : c s <;> simp only [hc, ↓reduceIte, Bool.false_eq_true, View.render] at hcl hin ⊢
            · exact VStateMatches_frame hfr hcl hin
            · exact VStateMatches_frame hfr hcl hin
        | _ => exact False.elim h
    | f, ns, .element tag attrs kids, s, a, a', S, n, vst, hfr, hcl, h => by
        cases vst with
        | elem n' ks =>
            cases f with
            | zero => simp [CleanDomSubtree] at hcl
            | succ _ =>
                rcases h with ⟨hn, ns', tag', st, mg, domCs, hget, hks⟩
                rcases hcl with ⟨hmem, _, _, st', mg', domCs', hget', _, _, _, hcs⟩
                have hfrN := hfr n hmem
                rw [hget'] at hget; cases hget
                exact ⟨hn, _, tag, st, mg, domCs, hfrN.trans hget',
                  VStateKidsMatches_frame (fun m hm => hfr m hm.1) hcs hks⟩
        | _ => exact False.elim h

  theorem VStateKidsMatches_frame {σ msg : Type} :
      ∀ {f : Nat} {ns : String} {ks : List (View σ msg)} {s : σ} {a a' : DomArena msg} {S : Nat → Prop}
        {ds : List Dom.Node} {ksts : List (VState σ msg)},
        (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) →
        CleanDomChildren f ns (View.renderEach ks s) a S ds → VStateKidsMatches ks s a ds ksts → VStateKidsMatches ks s a' ds ksts
    | _, _, [], _, _, _, _, [], [], _, _, h => h
    | _, _, _ :: _, _, _, _, _, _ :: _, _ :: _, hfr, ⟨_, _, hSc, hSr, _, hHd, hTl⟩, ⟨hr, hm, hkt⟩ =>
        ⟨hr, VStateMatches_frame (fun m h => hfr m (hSc _ h)) hHd hm,
          VStateKidsMatches_frame (fun m h => hfr m (hSr _ h)) hTl hkt⟩
    | _, _, [], _, _, _, _, _ :: _, _, _, hc, _ | _, _, _ :: _, _, _, _, _, [], _, _, hc, _ => False.elim hc
    | _, _, [], _, _, _, _, [], _ :: _, _, _, h => False.elim h
    | _, _, _ :: _, _, _, _, _, _ :: _, [], _, _, h => False.elim h
end

theorem VStateValid_mono {σ msg : Type} {f : Nat} {ns : String} {v : View σ msg} {s : σ}
    {a : DomArena msg} {S S' : Nat → Prop} {vst : VState σ msg} (hsub : ∀ k, S k → S' k)
    (h : VStateValid f ns v s a S vst) : VStateValid f ns v s a S' vst := ⟨CleanDomSubtree_mono hsub h.1, h.2⟩

theorem VStateValid_frame {σ msg : Type} {f : Nat} {ns : String} {v : View σ msg} {s : σ}
    {a a' : DomArena msg} {S : Nat → Prop} {vst : VState σ msg}
    (hfr : ∀ m : Dom.Node, S m.toNat → a'.get m = a.get m)
    (h : VStateValid f ns v s a S vst) : VStateValid f ns v s a' S vst :=
  ⟨CleanDomSubtree_frame hfr h.1, VStateMatches_frame hfr h.1 h.2⟩


theorem keyedRows_eq_of_keys_eq {σ msg : Type} {keys : σ → Array String} {rowsHtml : σ → List (Html msg)}
    (hr : KeyedRowsClean keys rowsHtml) {s₁ s₂ : σ} (hk : disambiguateKeys (keys s₂) = disambiguateKeys (keys s₁)) :
    rowsHtml s₁ = rowsHtml s₂ := by
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < (disambiguateKeys (keys s₁)).size
  · have hj : i < (disambiguateKeys (keys s₂)).size := hk ▸ hi
    exact hr.2.2.2 s₁ s₂ i i hi hj (by simp [hk])
  · have h1 : (rowsHtml s₁).length ≤ i := by rw [hr.1 s₁]; omega
    have h2 : (rowsHtml s₂).length ≤ i := by rw [hr.1 s₂, hk]; omega
    rw [List.getElem?_eq_none h1, List.getElem?_eq_none h2]

end Qed
