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

private theorem nodup_reinsert {α : Type} [BEq α] [LawfulBEq α] {pre suf : List α} {c : α}
    (hnd : (pre ++ suf).Nodup) (hc : c ∉ pre) :
    (pre ++ c :: suf.erase c).Nodup := by
  induction pre with
  | nil =>
      simp only [List.nil_append] at hnd ⊢
      refine List.nodup_cons.2 ⟨?_, hnd.erase c⟩
      clear hc
      induction suf with
      | nil => simp
      | cons s srest ihS =>
          rcases List.nodup_cons.1 hnd with ⟨hs, hsrest⟩
          by_cases hsc : s == c
          · have heq : s = c := eq_of_beq hsc
            subst heq; simpa [List.erase_cons] using hs
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
  | nil => simp [List.erase_of_not_mem hnotPre]
  | cons ref rest =>
      by_cases hrc : ref == child
      · have heq : ref = child := eq_of_beq hrc
        subst heq; simp
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
      (pre ++ suf).Nodup → targets.Nodup → (∀ t ∈ targets, t ∉ pre) →
      ∃ rem, w3cPlaceSeq (pre ++ suf) pre.length targets = pre ++ targets ++ rem := by
  induction targets with
  | nil => intro pre suf _ _ _; exact ⟨suf, by simp [w3cPlaceSeq]⟩
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
        · simp only [List.mem_singleton] at h2; subst h2; exact htRest hr
      have hlen' : (pre ++ [t]).length = pre.length + 1 := by simp
      rcases ih (pre ++ [t]) (suf.erase t) hnd' hrestNd hdisj' with ⟨rem, heq⟩
      refine ⟨rem, ?_⟩
      simp only [w3cPlaceSeq, hstep]
      have hassoc : pre ++ t :: suf.erase t = (pre ++ [t]) ++ suf.erase t := by simp
      rw [hassoc, ← hlen', heq]; simp [List.append_assoc]

/-- Complete keyed child-order reconciliation theorem: placing any duplicate-free `targets` sequence
    via W3C `insertBefore` over an existing duplicate-free `live` child list and removing the
    trailing unused suffix yields `targets` in exact order. -/
theorem w3cReconcileKeyed_eq (live targets : List Dom.Node)
    (hlive : live.Nodup) (htargets : targets.Nodup) :
    let placed := w3cPlaceSeq live 0 targets
    removeTailSpec targets.length (placed.length - targets.length) placed = targets := by
  rcases w3cPlaceSeq_invariant targets [] live (by simpa using hlive) htargets
    (fun _ _ h => nomatch h) with ⟨rem, hplaced⟩
  dsimp only; simp only [List.nil_append, List.length_nil] at hplaced
  rw [hplaced]
  have hsub : (targets ++ rem).length - targets.length = rem.length := by simp
  rw [hsub]; exact removeTailSpec_append targets rem

/-! ## Child Reconciliation & Full Subtree Patching on `DomArena` -/

private theorem getElem?_getD_of_lt {α : Type} (xs : List α) (i : Nat) (d : α) (h : i < xs.length) :
    xs[i]?.getD d = xs[i] := by simp [List.getElem?_eq_getElem h]

theorem snapshotChildrenM_spec (a : DomArena msg) (node : Dom.Node) (pns ptag : String)
    (pst : SpecElemState msg) (pmg : List String) (cs : List Dom.Node)
    (hsize : cs.length < UInt32.size) :
    ∀ (i rem : Nat) (acc : Array Dom.Node),
      i + rem = cs.length →
      (snapshotChildrenM (m := StateM (DomArena msg)) node i acc rem).run
        (a.set node (.element pns ptag pst pmg cs)) =
        (⟨acc.toList ++ cs.drop i⟩, a.set node (.element pns ptag pst pmg cs)) := by
  intro i rem; induction rem generalizing i with
  | zero =>
      intro acc hsum
      have hi : i = cs.length := by omega
      subst hi; cases acc with | mk _ => simp [snapshotChildrenM, StateT.run, pure, StateT.pure]
  | succ r ih =>
      intro acc hsum
      have hlt : i < cs.length := by omega
      have hu : (UInt32.ofNat i).toNat = i := uint32_toNat_ofNat_lt i (by omega)
      have hchildAt :
          (MonadDom.childAt (m := StateM (DomArena msg)) node (UInt32.ofNat i)).run
            (a.set node (.element pns ptag pst pmg cs)) =
            (cs[i], a.set node (.element pns ptag pst pmg cs)) := by
        simp [MonadDom.childAt, StateT.run, DomArena.get_set_self, hu, getElem?_getD_of_lt cs i 0 hlt]
      have hdrop : cs.drop i = cs[i] :: cs.drop (i + 1) := List.drop_eq_getElem_cons hlt
      dsimp only [snapshotChildrenM, StateT.run, bind, StateT.bind]
      change (match (MonadDom.childAt (m := StateM (DomArena msg)) node (UInt32.ofNat i)).run
                (a.set node (.element pns ptag pst pmg cs)) with
              | (child, s') =>
                (snapshotChildrenM (m := StateM (DomArena msg)) node (i + 1) (acc.push child) r).run s') = _
      rw [hchildAt]; dsimp only; rw [ih (i + 1) (acc.push cs[i]) (by omega)]
      simp only [Array.toList_push, List.append_assoc, List.singleton_append, hdrop]


mutual
  def CleanDomSubtree {msg : Type} : Nat → String → Html msg → DomArena msg → (Nat → Prop) → Dom.Node → Prop
    | 0, _, _, _, _, _ => False
    | _ + 1, _, .text s, a, S, n => S n.toNat ∧ a.get n = .text s
    | f + 1, ns, .element tag attrs cs, a, S, n =>
        let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
        S n.toNat ∧ ownsChildren attrs = false ∧ attrs.all Attr.DomClean = true ∧
        ∃ st mg domCs, a.get n = .element realNs tag st mg domCs ∧
          ElemClean st mg ∧ ElemStateEquiv st (evalSpecAttrs attrs) ∧
          (∀ nm ∈ (normalizeAttrs attrs).filterMap managedAttrName, mg.contains nm = true) ∧
          CleanDomChildren f (Dom.childNsOf ns tag) cs a (fun k => S k ∧ k ≠ n.toNat) domCs

  def CleanDomChildren {msg : Type} : Nat → String → List (Html msg) → DomArena msg → (Nat → Prop) → List Dom.Node → Prop
    | _, _, [], _, _, [] => True
    | f, ns, c :: cs, a, S, d :: ds =>
        ∃ Sc Srest, (∀ k, Sc k → S k) ∧ (∀ k, Srest k → S k) ∧ (∀ k, Sc k → Srest k → False) ∧
          CleanDomSubtree f ns c a Sc d ∧ CleanDomChildren f ns cs a Srest ds
    | _, _, _, _, _, _ => False
end

theorem CleanDomSubtree_root_mem {msg : Type} :
    ∀ {f : Nat} {ns : String} {h : Html msg} {a : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
      CleanDomSubtree f ns h a S n → S n.toNat
  | 0, _, _, _, _, _, h => by simp [CleanDomSubtree] at h
  | _ + 1, _, .text _, _, _, _, h => h.1
  | _ + 1, _, .element _ _ _, _, _, _, h => h.1

theorem CleanDomChildren_mem {msg : Type} :
    ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node},
      CleanDomChildren f ns cs a S ds → ∀ d ∈ ds, S d.toNat
  | _, _, [], _, _, [], _ => fun _ hm => nomatch hm
  | _, _, _ :: _, _, _, _ :: _, ⟨_, _, hSc, hSr, _, hHd, hTl⟩ => fun d hd => by
      rcases List.mem_cons.1 hd with rfl | hr
      · exact hSc _ (CleanDomSubtree_root_mem hHd)
      · exact hSr _ (CleanDomChildren_mem hTl d hr)
  | _, _, [], _, _, _ :: _, h => False.elim h
  | _, _, _ :: _, _, _, [], h => False.elim h

theorem CleanDomChildren_nodup {msg : Type} :
    ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node},
      CleanDomChildren f ns cs a S ds → ds.Nodup ∧ ds.length = cs.length
  | _, _, [], _, _, [], _ => ⟨List.nodup_nil, rfl⟩
  | _, _, _ :: _, _, _, _ :: _, ⟨_, _, _, _, hDisj, hHd, hTl⟩ => by
      have ⟨hnd, hlen⟩ := CleanDomChildren_nodup hTl
      exact ⟨List.nodup_cons.2 ⟨fun hm => hDisj _ (CleanDomSubtree_root_mem hHd) (CleanDomChildren_mem hTl _ hm), hnd⟩, by simp [hlen]⟩
  | _, _, [], _, _, _ :: _, h => False.elim h
  | _, _, _ :: _, _, _, [], h => False.elim h

theorem CleanDomChildren_mono {msg : Type} :
    ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S S' : Nat → Prop} {ds : List Dom.Node},
      (∀ k, S k → S' k) → CleanDomChildren f ns cs a S ds → CleanDomChildren f ns cs a S' ds
  | _, _, [], _, _, _, [], _, _ => trivial
  | _, _, _ :: _, _, _, _, _ :: _, hsub, ⟨Sc, Srest, hSc, hSr, hDisj, hHd, hTl⟩ =>
      ⟨Sc, Srest, fun k hk => hsub k (hSc k hk), fun k hk => hsub k (hSr k hk), hDisj, hHd, hTl⟩
  | _, _, [], _, _, _, _ :: _, _, hc => False.elim hc
  | _, _, _ :: _, _, _, _, [], _, hc => False.elim hc

theorem CleanDomSubtree_mono {msg : Type} :
    ∀ {f : Nat} {ns : String} {h : Html msg} {a : DomArena msg} {S S' : Nat → Prop} {n : Dom.Node},
      (∀ k, S k → S' k) → CleanDomSubtree f ns h a S n → CleanDomSubtree f ns h a S' n
  | 0, _, _, _, _, _, _, _, hc => by simp only [CleanDomSubtree] at hc
  | _ + 1, _, .text _, _, _, _, _, hsub, ⟨hn, hg⟩ => ⟨hsub _ hn, hg⟩
  | _ + 1, _, .element _ _ _, _, _, _, _, hsub, ⟨hn, ho, ha, st, mg, domCs, hg, hcl, heq, hmg, hcs⟩ =>
      ⟨hsub _ hn, ho, ha, st, mg, domCs, hg, hcl, heq, hmg, CleanDomChildren_mono (fun _ hk => ⟨hsub _ hk.1, hk.2⟩) hcs⟩

private theorem cleanDomChildren_frame_of {msg : Type} {f : Nat} {a a' : DomArena msg}
    (hSub : ∀ {ns : String} {h : Html msg} {S : Nat → Prop} {n : Dom.Node},
      (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) → CleanDomSubtree f ns h a S n → CleanDomSubtree f ns h a' S n) :
    ∀ {ns : String} {cs : List (Html msg)} {S : Nat → Prop} {ds : List Dom.Node},
      (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) → CleanDomChildren f ns cs a S ds → CleanDomChildren f ns cs a' S ds
  | _, [], _, [], _, _ => trivial
  | _, _ :: _, _, _ :: _, hfr, ⟨Sc, Srest, hSc, hSr, hDisj, hHd, hTl⟩ =>
      ⟨Sc, Srest, hSc, hSr, hDisj,
       hSub (fun m hm => hfr m (hSc _ hm)) hHd,
       cleanDomChildren_frame_of hSub (fun m hm => hfr m (hSr _ hm)) hTl⟩
  | _, [], _, _ :: _, _, hc => False.elim hc
  | _, _ :: _, _, [], _, hc => False.elim hc

theorem CleanDomSubtree_frame {msg : Type} :
    ∀ {f : Nat} {ns : String} {h : Html msg} {a a' : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
      (∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) → CleanDomSubtree f ns h a S n → CleanDomSubtree f ns h a' S n
  | 0, _, _, _, _, _, _, _, hc => by simp only [CleanDomSubtree] at hc
  | _ + 1, _, .text _, _, _, _, n, hfr, ⟨hn, hg⟩ => ⟨hn, (hfr n hn).trans hg⟩
  | _ + 1, _, .element _ _ _, _, _, _, n, hfr, ⟨hn, ho, ha, st, mg, domCs, hg, hcl, heq, hmg, hcs⟩ =>
      ⟨hn, ho, ha, st, mg, domCs, (hfr n hn).trans hg, hcl, heq, hmg,
       cleanDomChildren_frame_of (fun hfr' h => CleanDomSubtree_frame hfr' h) (fun m hm => hfr m hm.1) hcs⟩

theorem CleanDomChildren_frame {msg : Type} {f : Nat} {ns : String} {cs : List (Html msg)} {a a' : DomArena msg}
    {S : Nat → Prop} {ds : List Dom.Node}
    (hfr : ∀ m : Dom.Node, S m.toNat → a'.get m = a.get m) (h : CleanDomChildren f ns cs a S ds) :
    CleanDomChildren f ns cs a' S ds :=
  cleanDomChildren_frame_of (fun hfr' h' => CleanDomSubtree_frame hfr' h') hfr h

private theorem cleanDomChildren_equiv_of {msg : Type} {f : Nat} {a : DomArena msg}
    (hSub : ∀ {ns : String} {h : Html msg} {S : Nat → Prop} {n : Dom.Node},
      CleanDomSubtree f ns h a S n → DomTreeAssocEquiv (readDomTree f a n) (specDom ns h)) :
    ∀ {ns : String} {cs : List (Html msg)} {S : Nat → Prop} {ds : List Dom.Node},
      CleanDomChildren f ns cs a S ds → DomTreeListAssocEquiv (ds.map (readDomTree f a)) (specDomList ns cs)
  | _, [], _, [], _ => trivial
  | _, _ :: _, _, _ :: _, ⟨_, _, _, _, _, hHd, hTl⟩ => ⟨hSub hHd, cleanDomChildren_equiv_of hSub hTl⟩
  | _, [], _, _ :: _, hc => False.elim hc
  | _, _ :: _, _, [], hc => False.elim hc

theorem CleanDomSubtree_equiv {msg : Type} :
    ∀ {f : Nat} {ns : String} {h : Html msg} {a : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
      CleanDomSubtree f ns h a S n → DomTreeAssocEquiv (readDomTree f a n) (specDom ns h)
  | 0, _, _, _, _, _, hc => by simp only [CleanDomSubtree] at hc
  | _ + 1, _, .text _, _, _, _, ⟨_, hg⟩ => by
      dsimp only [readDomTree, specDom, DomTreeAssocEquiv]; rw [hg]; rfl
  | _ + 1, _, .element _ _ _, _, _, _, ⟨_, ho, _, _, _, _, hg, _, heq, _, hcs⟩ => by
      dsimp only [readDomTree, specDom]; rw [hg, ho]
      exact ⟨rfl, rfl, heq, cleanDomChildren_equiv_of (fun h' => CleanDomSubtree_equiv h') hcs⟩

theorem CleanDomChildren_equiv {msg : Type} {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg}
    {S : Nat → Prop} {ds : List Dom.Node} (h : CleanDomChildren f ns cs a S ds) :
    DomTreeListAssocEquiv (ds.map (readDomTree f a)) (specDomList ns cs) :=
  cleanDomChildren_equiv_of (fun h' => CleanDomSubtree_equiv h') h

theorem CleanDomChildren_append {msg : Type} :
    ∀ {f : Nat} {ns : String} {xs₁ xs₂ : List (Html msg)} {a : DomArena msg}
      {S₁ S₂ : Nat → Prop} {ds₁ ds₂ : List Dom.Node},
      (∀ k, S₁ k → S₂ k → False) →
      CleanDomChildren f ns xs₁ a S₁ ds₁ → CleanDomChildren f ns xs₂ a S₂ ds₂ →
      CleanDomChildren f ns (xs₁ ++ xs₂) a (fun k => S₁ k ∨ S₂ k) (ds₁ ++ ds₂)
  | _, _, [], _, _, _, _, [], _, _, _, h2 => CleanDomChildren_mono (fun _ hk => .inr hk) h2
  | _, _, _ :: _, _, _, _, S₂, _ :: _, _, hDisj, ⟨Sc, Srest, hSc, hSr, hD, hHd, hTl⟩, h2 =>
      ⟨Sc, fun k => Srest k ∨ S₂ k, fun k hk => .inl (hSc k hk), fun k hk => hk.elim (fun h => .inl (hSr k h)) .inr,
       fun k hk1 hk2 => hk2.elim (hD k hk1) (hDisj k (hSc k hk1)), hHd, CleanDomChildren_append (fun k h1 h2' => hDisj k (hSr k h1) h2') hTl h2⟩
  | _, _, [], _, _, _, _, _ :: _, _, _, hc, _ => False.elim hc
  | _, _, _ :: _, _, _, _, _, [], _, _, hc, _ => False.elim hc

theorem CleanDomChildren_indexed {msg : Type} :
    ∀ {f : Nat} {ns : String} {cs : List (Html msg)} {a : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node},
      CleanDomChildren f ns cs a S ds →
      ∃ (Si : Nat → Nat → Prop), (∀ i k, Si i k → S k) ∧
        (∀ i₁ i₂, i₁ ≠ i₂ → ∀ k, Si i₁ k → Si i₂ k → False) ∧
        (∀ (i : Nat) (h1 : i < cs.length) (h2 : i < ds.length), CleanDomSubtree f ns cs[i] a (Si i) ds[i])
  | _, _, [], _, _, [], _ => ⟨fun _ _ => False, fun _ _ h => h.elim, fun _ _ _ _ h => h.elim, fun _ h => nomatch h⟩
  | _, _, _ :: _, _, _, _ :: _, ⟨Sc, Srest, hSc, hSr, hDisj, hHd, hTl⟩ => by
      rcases CleanDomChildren_indexed hTl with ⟨SiTail, hSub, hPair, hGet⟩
      refine ⟨fun | 0 => Sc | i + 1 => SiTail i, ?_, ?_, ?_⟩
      · intro i k hk; cases i with | zero => exact hSc k hk | succ i => exact hSr k (hSub i k hk)
      · intro i₁ i₂ hne k h1 h2
        cases i₁ <;> cases i₂
        · exact absurd rfl hne
        · exact hDisj k h1 (hSub _ k h2)
        · exact hDisj k h2 (hSub _ k h1)
        · exact hPair _ _ (by omega) k h1 h2
      · intro i h1 h2; cases i with | zero => exact hHd | succ i => exact hGet i (by simpa using h1) (by simpa using h2)
  | _, _, [], _, _, _ :: _, hc => False.elim hc
  | _, _, _ :: _, _, _, [], hc => False.elim hc

private theorem cleanDomChildren_DomCleanList_of {msg : Type} {f : Nat} {a : DomArena msg}
    (hSub : ∀ {ns : String} {h : Html msg} {S : Nat → Prop} {n : Dom.Node},
      CleanDomSubtree f ns h a S n → h.DomClean = true) :
    ∀ {ns : String} {cs : List (Html msg)} {S : Nat → Prop} {ds : List Dom.Node},
      CleanDomChildren f ns cs a S ds → Html.DomCleanList cs = true
  | _, [], _, [], _ => rfl
  | _, _ :: _, _, _ :: _, ⟨_, _, _, _, _, hHd, hTl⟩ => by
      simp only [Html.DomCleanList, hSub hHd, cleanDomChildren_DomCleanList_of hSub hTl, Bool.and_self]
  | _, [], _, _ :: _, hc => False.elim hc
  | _, _ :: _, _, [], hc => False.elim hc

theorem CleanDomSubtree_DomClean {msg : Type} :
    ∀ {f : Nat} {ns : String} {h : Html msg} {a : DomArena msg} {S : Nat → Prop} {n : Dom.Node},
      CleanDomSubtree f ns h a S n → h.DomClean = true
  | 0, _, _, _, _, _, hc => by simp only [CleanDomSubtree] at hc
  | _ + 1, _, .text _, _, _, _, _ => rfl
  | _ + 1, _, .element _ _ _, _, _, _, ⟨_, ho, ha, _, _, _, _, _, _, _, hcs⟩ => by
      simp only [Html.DomClean, ho, ha, cleanDomChildren_DomCleanList_of (fun h' => CleanDomSubtree_DomClean h') hcs,
        Bool.not_false, Bool.and_self]

theorem CleanDomChildren_DomCleanList {msg : Type} {f : Nat} {ns : String} {cs : List (Html msg)}
    {a : DomArena msg} {S : Nat → Prop} {ds : List Dom.Node} (h : CleanDomChildren f ns cs a S ds) :
    Html.DomCleanList cs = true :=
  cleanDomChildren_DomCleanList_of (fun h' => CleanDomSubtree_DomClean h') h

theorem CleanDomSubtree_not_fragment {msg : Type} {f : Nat} {ns : String} {h : Html msg}
    {a : DomArena msg} {S : Nat → Prop} {n : Dom.Node} (hcl : CleanDomSubtree f ns h a S n) :
    ∀ fcs, a.get n ≠ .fragment fcs := by
  cases f with
  | zero => simp only [CleanDomSubtree] at hcl
  | succ _ => cases h with
    | text _ => intro fcs hf; dsimp only [CleanDomSubtree] at hcl; rw [hcl.2] at hf; cases hf
    | element _ _ _ => intro fcs hf; rcases hcl with ⟨_, _, _, _, _, _, hg, _⟩; rw [hg] at hf; cases hf

private theorem appendChild_nextId {msg : Type} (p c : Dom.Node) (a : DomArena msg) :
    ((MonadDom.appendChild (m := StateM (DomArena msg)) p c).run a).2.nextId = a.nextId := by
  dsimp only [MonadDom.appendChild, StateT.run]; split <;> rfl

private theorem htmlDepth_mem_le' {msg : Type} {c : Html msg} {cs : List (Html msg)} (hc : c ∈ cs) :
    htmlDepth c ≤ htmlListDepth cs := by
  induction cs with
  | nil => cases hc
  | cons _ _ ih =>
      simp only [htmlListDepth]
      cases hc with
      | head => exact Nat.le_max_left _ _
      | tail _ h => exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

private theorem buildDomListM_nextId_mono_of {msg : Type} (ns : String) (parent : Dom.Node) (cs : List (Html msg))
    (hBuild : ∀ c ∈ cs, ∀ (a : DomArena msg), a.nextId ≤ ((buildDomM (m := StateM (DomArena msg)) ns c).run a).2.nextId) :
    ∀ (a : DomArena msg), a.nextId ≤ ((buildDomListM (m := StateM (DomArena msg)) ns parent cs).run a).2.nextId := by
  induction cs with
  | nil => intro _; exact Nat.le_refl _
  | cons c rest ih =>
      intro a
      have h1 := hBuild c (.head _) a
      dsimp only [buildDomListM, StateT.run, bind, StateT.bind] at h1 ⊢
      cases hres : buildDomM (m := StateM (DomArena msg)) ns c a with
      | mk cn aMid =>
          rw [hres] at h1; dsimp only at h1
          have h2 := appendChild_nextId parent cn aMid
          dsimp only [StateT.run] at h2
          cases hApp : MonadDom.appendChild (m := StateM (DomArena msg)) parent cn aMid with
          | mk _ a2 =>
              dsimp only; rw [hApp] at h2 ⊢; dsimp only at h2 ⊢
              have h3 := ih (fun x hx => hBuild x (.tail _ hx)) a2
              dsimp only [StateT.run] at h3 ⊢
              exact Nat.le_trans h1 (h2 ▸ h3)

private theorem buildDomM_nextId_mono_aux {msg : Type} :
    ∀ (f : Nat) (ns : String) (h : Html msg) (a : DomArena msg),
      htmlDepth h ≤ f → a.nextId ≤ ((buildDomM (m := StateM (DomArena msg)) ns h).run a).2.nextId
  | 0, _, h, _, hdep => by cases h <;> { simp only [htmlDepth] at hdep; omega }
  | _ + 1, _, .text _, _, _ => Nat.le_succ _
  | f + 1, ns, .element tag attrs cs, a, hdep => by
      simp only [htmlDepth] at hdep
      let node := UInt32.ofNat a.nextId
      let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
      let a1 : DomArena msg := { a with nextId := a.nextId + 1 }
      have hnx := applyAttrsM_nextId a1 node attrs (.element realNs tag {} [] [])
      dsimp only [StateT.run] at hnx
      dsimp only [buildDomM, MonadDom.createElement, DomArena.alloc, StateT.run, bind, StateT.bind, pure, StateT.pure]
      change a.nextId ≤ (match applyAttrsM (m := StateM (DomArena msg)) node attrs (a1.set node (.element realNs tag {} [] [])) with
        | (_, s) => (if (!ownsChildren attrs) = true then
            StateT.bind (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node cs) fun _ => StateT.pure node
          else (StateT.pure PUnit.unit).bind fun _ => StateT.pure node) s).2.nextId
      cases hres : applyAttrsM (m := StateM (DomArena msg)) node attrs (a1.set node (.element realNs tag {} [] [])) with
      | mk _ s1 =>
          rw [hres] at hnx
          have hs1 : a.nextId ≤ s1.nextId := hnx ▸ Nat.le_succ _
          cases ownsChildren attrs with
          | true => exact hs1
          | false =>
              have hm := buildDomListM_nextId_mono_of (Dom.childNsOf ns tag) node cs
                (fun c hc a' => buildDomM_nextId_mono_aux f (Dom.childNsOf ns tag) c a'
                  (Nat.le_trans (htmlDepth_mem_le' hc) (by omega))) s1
              dsimp only [StateT.run] at hm; exact Nat.le_trans hs1 hm

theorem buildDomM_nextId_mono {msg : Type} (ns : String) (h : Html msg) (a : DomArena msg) :
    a.nextId ≤ ((buildDomM (m := StateM (DomArena msg)) ns h).run a).2.nextId :=
  buildDomM_nextId_mono_aux (htmlDepth h) ns h a (Nat.le_refl _)

theorem buildDomListM_nextId_mono {msg : Type} (ns : String) (parent : Dom.Node) (cs : List (Html msg)) (a : DomArena msg) :
    a.nextId ≤ ((buildDomListM (m := StateM (DomArena msg)) ns parent cs).run a).2.nextId :=
  buildDomListM_nextId_mono_of ns parent cs (fun c _ a' => buildDomM_nextId_mono ns c a') a

private theorem cleanDomChildren_of_buildDomListM_of {msg : Type} (f : Nat)
    (hSub : ∀ (ns : String) (h : Html msg) (a : DomArena msg),
      h.DomClean = true → 0 < a.nextId → a.nextId + htmlNodeCount h < UInt32.size → htmlDepth h ≤ f →
      let (root, a') := (buildDomM (m := StateM (DomArena msg)) ns h).run a
      CleanDomSubtree f ns h a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root)
    (childNs : String) (cs : List (Html msg)) :
    ∀ (hsAcc : List (Html msg)) (aBase : DomArena msg) (parent : Dom.Node)
      (mkPar : List Dom.Node → ArenaEntry msg),
      ((∃ pns ptag pst pmg, ∀ ds, mkPar ds = .element pns ptag pst pmg ds) ∨ (∀ ds, mkPar ds = .fragment ds)) →
      ∀ (acc : List Dom.Node) (Sacc : Nat → Prop),
      Html.DomCleanList cs = true → parent.toNat < aBase.nextId → 0 < aBase.nextId → aBase.nextId + htmlListNodeCount cs < UInt32.size →
      htmlListDepth cs ≤ f → (∀ k, Sacc k → parent.toNat < k ∧ k < aBase.nextId) →
      CleanDomChildren f childNs hsAcc (aBase.set parent (mkPar acc)) Sacc acc →
      let aIn := aBase.set parent (mkPar acc)
      let aOut := ((buildDomListM (m := StateM (DomArena msg)) childNs parent cs).run aIn).2
      ∃ (csNew : List Dom.Node) (aBase' : DomArena msg),
        aOut = aBase'.set parent (mkPar (acc ++ csNew)) ∧
        aBase.nextId ≤ aOut.nextId ∧
        aOut.nextId ≤ aBase.nextId + htmlListNodeCount cs ∧
        (∀ m : Dom.Node, m.toNat < aBase.nextId → m ≠ parent → aOut.get m = aBase.get m) ∧
        CleanDomChildren f childNs (hsAcc ++ cs) aOut (fun k => Sacc k ∨ (aBase.nextId ≤ k ∧ k < aOut.nextId)) (acc ++ csNew) := by
  induction cs with
  | nil =>
      intro hsAcc aBase parent mkPar _ acc Sacc _ _ _ _ _ _ haccClean
      refine ⟨[], aBase, ?_, Nat.le_refl _, ?_, fun m _ hne => ?_, ?_⟩
      · simp only [buildDomListM, StateT.run, pure, StateT.pure, List.append_nil]
      · simp only [buildDomListM, StateT.run, pure, StateT.pure, htmlListNodeCount, Nat.add_zero, DomArena.set]
        exact Nat.le_refl _
      · dsimp only [buildDomListM, StateT.run, pure, StateT.pure]; exact DomArena.get_set_ne _ _ hne
      · simp only [buildDomListM, StateT.run, pure, StateT.pure, List.append_nil]
        exact CleanDomChildren_mono (fun _ hk => .inl hk) haccClean
  | cons c rest ih =>
      intro hsAcc aBase parent mkPar hmk acc Sacc hclean hparLt hpos hbound hdep hSacc haccClean
      simp only [Html.DomCleanList, Bool.and_eq_true] at hclean
      simp only [htmlListNodeCount] at hbound; simp only [htmlListDepth] at hdep
      have hcDep : htmlDepth c ≤ f := Nat.le_trans (Nat.le_max_left _ _) hdep
      have hrestDep : htmlListDepth rest ≤ f := Nat.le_trans (Nat.le_max_right _ _) hdep
      let aIn := aBase.set parent (mkPar acc)
      have haInNext : aIn.nextId = aBase.nextId := rfl
      have hcSpec := buildDomM_spec childNs c aIn f hpos (by omega) hcDep
      have hcClean := hSub childNs c aIn hclean.1 hpos (by omega) hcDep
      have haMidLe := buildDomM_nextId_mono childNs c aIn
      dsimp only [StateT.run] at hcSpec hcClean haMidLe
      cases hR : buildDomM (m := StateM (DomArena msg)) childNs c aIn with
      | mk cn aMid =>
          rw [hR] at hcSpec hcClean haMidLe; dsimp only at hcSpec hcClean haMidLe
          rcases hcSpec with ⟨hcnGe, hcnLt, haMidBound, haMidFrame, _, _⟩
          rw [haInNext] at hcnGe haMidLe haMidBound
          have hparInMid : aMid.get parent = mkPar acc := by
            rw [haMidFrame parent hparLt]; exact DomArena.get_set_self ..
          have hcnNotFrag : ∀ fcs, aMid.get cn ≠ .fragment fcs := fun fcs => by
            have hb := buildDomM_not_fragment childNs c aIn f fcs hpos (by omega) hcDep
            dsimp only [StateT.run] at hb; rw [hR] at hb; exact hb
          have hcnNotInAcc : cn ∉ acc := fun hmem => by have := hSacc _ (CleanDomChildren_mem haccClean cn hmem); omega
          let aAfter := aMid.set parent (mkPar (acc ++ [cn]))
          have haAfterNext : aAfter.nextId = aMid.nextId := rfl
          let Sc : Nat → Prop := fun k => aBase.nextId ≤ k ∧ k < aMid.nextId
          have haccMid : CleanDomChildren f childNs hsAcc aAfter Sacc acc :=
            CleanDomChildren_frame (fun m hm => by
              have hb := hSacc _ hm; rw [DomArena.get_set_ne _ _ (fun h => by subst h; omega)]; exact haMidFrame m hb.2) haccClean
          have hcAfter : CleanDomSubtree f childNs c aAfter Sc cn :=
            CleanDomSubtree_frame (fun m _ => DomArena.get_set_ne _ _ fun heq => by subst heq; omega) hcClean
          have hcombClean : CleanDomChildren f childNs (hsAcc ++ [c]) aAfter (fun k => Sacc k ∨ Sc k) (acc ++ [cn]) :=
            CleanDomChildren_append (fun k hk1 hk2 => by have := hSacc k hk1; omega) haccMid
              (show CleanDomChildren f childNs [c] aAfter Sc [cn] from
                ⟨Sc, fun _ => False, fun _ h => h, fun _ h => h.elim, fun _ _ h => h.elim, hcAfter, trivial⟩)
          rcases ih (hsAcc ++ [c]) aMid parent mkPar hmk (acc ++ [cn])
            (fun k => Sacc k ∨ Sc k) hclean.2 (by omega) (by omega) (by omega) hrestDep
            (fun k hk => hk.elim (fun h => let b := hSacc k h; ⟨b.1, by omega⟩) (fun h => ⟨by omega, h.2⟩))
            hcombClean with ⟨csRest, aBase'', haOutEq, haOutGe, haOutBound, haOutFrame, hcleanFinal⟩
          have hstepRun := buildDomListM_step childNs parent c rest aIn aMid cn mkPar hmk acc hR hparInMid hcnNotFrag hcnNotInAcc
          have haRestMono := buildDomListM_nextId_mono childNs parent rest aAfter
          dsimp only [StateT.run] at hstepRun hcleanFinal haOutEq haRestMono haOutGe haOutBound haOutFrame ⊢
          rw [haAfterNext] at haRestMono
          simp only [List.append_assoc, List.singleton_append] at haOutEq hcleanFinal
          refine ⟨cn :: csRest, aBase'', by rw [hstepRun]; exact haOutEq,
            by rw [hstepRun]; exact Nat.le_trans haMidLe haOutGe,
            by rw [hstepRun]; simp only [htmlListNodeCount]; omega, fun m hm hne => ?_, ?_⟩
          · rw [hstepRun, haOutFrame m (Nat.lt_of_lt_of_le hm haMidLe) hne, haMidFrame m hm]
            exact DomArena.get_set_ne _ _ hne
          · rw [hstepRun]
            refine CleanDomChildren_mono (fun k hk => ?_) hcleanFinal
            rcases hk with (hS | hSc) | hRest
            · exact .inl hS
            · exact .inr ⟨hSc.1, Nat.lt_of_lt_of_le hSc.2 haOutGe⟩
            · exact .inr ⟨Nat.le_trans haMidLe hRest.1, hRest.2⟩

theorem CleanDomSubtree_of_buildDomM {msg : Type} (ns : String) (h : Html msg) (a : DomArena msg) (fuel : Nat) :
    h.DomClean = true → 0 < a.nextId → a.nextId + htmlNodeCount h < UInt32.size → htmlDepth h ≤ fuel →
    let (root, a') := (buildDomM (m := StateM (DomArena msg)) ns h).run a
    CleanDomSubtree fuel ns h a' (fun k => a.nextId ≤ k ∧ k < a'.nextId) root := by
  induction fuel generalizing ns h a with
  | zero => intro _ _ _ hdep; cases h <;> { simp only [htmlDepth] at hdep; omega }
  | succ f ih =>
      intro hclean hpos hbound hdep
      cases h with
      | text s =>
          simp only [htmlNodeCount] at hbound
          have htoNat : (UInt32.ofNat a.nextId).toNat = a.nextId := uint32_toNat_ofNat_lt _ (by omega)
          dsimp only [buildDomM, MonadDom.createText, DomArena.alloc, StateT.run, CleanDomSubtree, DomArena.get]
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          rw [beq_self_eq_true, if_pos rfl]
      | element tag attrs children =>
          simp only [Html.DomClean, Bool.and_eq_true] at hclean
          rcases hclean with ⟨⟨hownT, hAclean⟩, hKclean⟩
          have hownF : ownsChildren attrs = false := by rw [← Bool.not_eq_true']; exact hownT
          simp only [htmlNodeCount] at hbound; simp only [htmlDepth] at hdep
          let node := UInt32.ofNat a.nextId
          have hnodeNat : node.toNat = a.nextId := uint32_toNat_ofNat_lt _ (by omega)
          let realNs := if ns == "" && tag == "svg" then Dom.svgNs else ns
          let st := evalSpecAttrs attrs; let mg := (normalizeAttrs attrs).filterMap managedAttrName
          let a1 : DomArena msg := { a with nextId := a.nextId + 1 }
          have ha1Next : a1.nextId = a.nextId + 1 := rfl
          let aElem := a1.set node (.element realNs tag st mg [])
          have haElemNext : aElem.nextId = a.nextId + 1 := rfl
          have hrun : buildDomM (m := StateM (DomArena msg)) ns (.element tag attrs children) a =
              (node, (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node children aElem).2) := by
            dsimp only [buildDomM, MonadDom.createElement, DomArena.alloc, StateT.run, bind, StateT.bind, pure, StateT.pure]
            change (match applyAttrsM (m := StateM (DomArena msg)) node attrs (a1.set node (.element realNs tag {} [] [])) with
                    | (_, s) => (if (!ownsChildren attrs) = true then
                       StateT.bind (buildDomListM (m := StateM (DomArena msg)) (Dom.childNsOf ns tag) node children) (fun _ => StateT.pure node)
                       else StateT.bind (StateT.pure PUnit.unit) (fun _ => StateT.pure node)) s) = _
            rw [applyAttrsM_fresh_element a1 node realNs tag [] attrs, hownF]; rfl
          rcases cleanDomChildren_of_buildDomListM_of f (fun ns' h' a' => ih ns' h' a')
            (Dom.childNsOf ns tag) children [] a1 node (ArenaEntry.element realNs tag st mg)
            (.inl ⟨realNs, tag, st, mg, fun _ => rfl⟩) [] (fun _ => False) hKclean
            (by omega) (by omega) (by omega) (by omega) (fun _ h => h.elim) trivial with
            ⟨csNew, aBase', ha'Eq, _, _, _, hcleanOut⟩
          have hmono := buildDomListM_nextId_mono (Dom.childNsOf ns tag) node children aElem
          dsimp only [StateT.run] at hmono ha'Eq hcleanOut ⊢
          rw [hrun]; dsimp only
          rw [List.nil_append, List.nil_append] at hcleanOut
          refine ⟨by omega, hownF, hAclean, st, mg, csNew, ?_,
            ElemClean_evalSpecAttrs hAclean, ElemStateEquiv.refl st,
            fun nm hnm => List.contains_iff_mem.2 hnm, ?_⟩
          · rw [ha'Eq, DomArena.get_set_self, List.nil_append]
          · refine CleanDomChildren_mono (fun k hk => ?_) hcleanOut
            rcases hk with hF | ⟨h1, h2⟩
            · exact hF.elim
            · exact ⟨⟨Nat.le_trans (Nat.le_succ _) h1, h2⟩, fun heq => by dsimp only [a1] at h1; omega⟩

theorem CleanDomChildren_of_buildDomListM {msg : Type} (childNs : String)
    (cs hsAcc : List (Html msg)) (aBase : DomArena msg) (parent : Dom.Node)
    (mkPar : List Dom.Node → ArenaEntry msg)
    (hmk : (∃ pns ptag pst pmg, ∀ ds, mkPar ds = .element pns ptag pst pmg ds) ∨ (∀ ds, mkPar ds = .fragment ds))
    (acc : List Dom.Node) (f : Nat) (Sacc : Nat → Prop) :
    Html.DomCleanList cs = true → parent.toNat < aBase.nextId → 0 < aBase.nextId → aBase.nextId + htmlListNodeCount cs < UInt32.size →
    htmlListDepth cs ≤ f → (∀ k, Sacc k → parent.toNat < k ∧ k < aBase.nextId) →
    CleanDomChildren f childNs hsAcc (aBase.set parent (mkPar acc)) Sacc acc →
    let aIn := aBase.set parent (mkPar acc)
    let aOut := ((buildDomListM (m := StateM (DomArena msg)) childNs parent cs).run aIn).2
    ∃ (csNew : List Dom.Node) (aBase' : DomArena msg),
      aOut = aBase'.set parent (mkPar (acc ++ csNew)) ∧
      aBase.nextId ≤ aOut.nextId ∧
      aOut.nextId ≤ aBase.nextId + htmlListNodeCount cs ∧
      (∀ m : Dom.Node, m.toNat < aBase.nextId → m ≠ parent → aOut.get m = aBase.get m) ∧
      CleanDomChildren f childNs (hsAcc ++ cs) aOut (fun k => Sacc k ∨ (aBase.nextId ≤ k ∧ k < aOut.nextId)) (acc ++ csNew) :=
  cleanDomChildren_of_buildDomListM_of f (fun ns' h' a' => CleanDomSubtree_of_buildDomM ns' h' a' f)
    childNs cs hsAcc aBase parent mkPar hmk acc Sacc

theorem listReplaceAt_append_middle {α : Type} :
    ∀ (pre : List α) (x y : α) (suf : List α), listReplaceAt (pre ++ x :: suf) pre.length y = pre ++ y :: suf
  | [], _, _, _ => rfl
  | _ :: pre, x, y, suf => by simp [listReplaceAt, listReplaceAt_append_middle pre x y suf]

theorem list_length_le_htmlListNodeCount {msg : Type} :
    ∀ (cs : List (Html msg)), cs.length ≤ htmlListNodeCount cs
  | [] => Nat.le_refl 0
  | c :: cs => by
      have hc : 1 ≤ htmlNodeCount c := by cases c <;> (simp [htmlNodeCount]; try omega)
      have hcs := list_length_le_htmlListNodeCount cs; simp only [List.length_cons, htmlListNodeCount]; omega

theorem nodup_snoc_append {α : Type} {pre suf : List α} {cn : α}
    (hnd : (pre ++ suf).Nodup) (hnot : cn ∉ pre ++ suf) : ((pre ++ [cn]) ++ suf).Nodup := by
  rcases List.nodup_append.1 hnd with ⟨hp, hs, hd⟩
  have hcns : cn ∉ pre ∧ cn ∉ suf := by simpa [List.mem_append, not_or] using hnot
  refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨hp, List.pairwise_singleton _ _, fun x hx y hy hEq => by
    simp only [List.mem_singleton] at hy; subst hy; subst hEq; exact hcns.1 hx⟩, hs, fun x hx y hy hEq => ?_⟩
  rcases List.mem_append.1 hx with hxp | hxc
  · exact hd x hxp y hy hEq
  · simp only [List.mem_singleton] at hxc; subst hxc; subst hEq; exact hcns.2 hy

private theorem not_mem_erase_of_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs : List α} {x : α}, xs.Nodup → x ∉ xs.erase x
  | [], _, _ => fun h => nomatch h
  | y :: ys, x, hnd => by
      rcases List.nodup_cons.1 hnd with ⟨hy, hys⟩
      by_cases hyx : y = x
      · subst hyx; simpa [List.erase_cons_head] using hy
      · have hbeq : (y == x) = false := beq_eq_false_iff_ne.2 hyx
        simp only [List.erase_cons, hbeq, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        intro h; rcases h with rfl | ht; exact hyx rfl; exact not_mem_erase_of_nodup hys ht

private theorem erase_nat_step (n : Nat) :
    ∀ (xs : List Nat), xs.Nodup → (∀ x ∈ xs, x < n + 1) →
      (xs.erase n).Nodup ∧ (∀ y ∈ xs.erase n, y < n) ∧ xs.length ≤ (xs.erase n).length + 1
  | [], _, _ => ⟨by simp, fun _ h => by simp at h, by simp⟩
  | x :: xs, hnd, hlt => by
      rcases List.nodup_cons.1 hnd with ⟨hxNot, hxsNd⟩
      have hxLt := hlt x (.head _); have hxsLt : ∀ y ∈ xs, y < n + 1 := fun y hy => hlt y (.tail _ hy)
      by_cases hxn : x = n
      · subst hxn; simp only [List.erase_cons_head]
        exact ⟨hxsNd, fun y hy => by have := hxsLt y hy; have hne : y ≠ x := fun h => hxNot (h ▸ hy); omega, Nat.le_refl _⟩
      · have hbeq : (x == n) = false := beq_eq_false_iff_ne.2 hxn
        simp only [List.erase_cons, hbeq, Bool.false_eq_true, ↓reduceIte]
        rcases erase_nat_step n xs hxsNd hxsLt with ⟨heNd, heLt, heLen⟩
        exact ⟨List.nodup_cons.2 ⟨fun h => hxNot (List.mem_of_mem_erase h), heNd⟩,
               fun y hy => by rcases List.mem_cons.1 hy with rfl | ht; omega; exact heLt y ht, by simp; omega⟩

theorem nodup_lt_length_le :
    ∀ (n : Nat) (xs : List Nat), xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, hlt => absurd (hlt x (.head _)) (Nat.not_lt_zero _)
  | n + 1, xs, hnd, hlt => by
      rcases erase_nat_step n xs hnd hlt with ⟨heNd, heLt, heLen⟩
      have := nodup_lt_length_le n (xs.erase n) heNd heLt; omega

theorem nodup_nodes_lt_length_le (n : Nat) (xs : List Dom.Node)
    (hnd : xs.Nodup) (hlt : ∀ x ∈ xs, x.toNat < n) : xs.length ≤ n := by
  have hmapNd : (xs.map UInt32.toNat).Nodup := by
    clear hlt; induction xs with
    | nil => exact List.nodup_nil
    | cons x xs ih =>
        rcases List.nodup_cons.1 hnd with ⟨hxNot, hxsNd⟩
        refine List.nodup_cons.2 ⟨fun hm => ?_, ih hxsNd⟩
        rcases List.mem_map.1 hm with ⟨y, hy, hyEq⟩; exact hxNot ((uint32_eq_of_toNat_eq hyEq) ▸ hy)
  have hmapLt : ∀ k ∈ xs.map UInt32.toNat, k < n := fun k hk => by rcases List.mem_map.1 hk with ⟨y, hy, rfl⟩; exact hlt y hy
  simpa using nodup_lt_length_le n (xs.map UInt32.toNat) hmapNd hmapLt

theorem nodup_append_replace {α : Type} {pre suf : List α} {x y : α}
    (hnd : (pre ++ x :: suf).Nodup) (hy : y = x ∨ y ∉ pre ++ x :: suf) : (pre ++ y :: suf).Nodup := by
  rcases hy with rfl | hnot
  · exact hnd
  · rcases List.nodup_append.1 hnd with ⟨hpre, hcons, hdisj⟩
    rcases List.nodup_cons.1 hcons with ⟨_, hsuf⟩
    refine List.nodup_append.2 ⟨hpre, List.nodup_cons.2 ⟨fun h => hnot (by simp [h]), hsuf⟩, fun a ha b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hbs
    · intro hEq; subst hEq; exact hnot (by simp [ha])
    · exact hdisj a ha b (.tail _ hbs)

theorem nodup_move_to_pre {α : Type} [BEq α] [LawfulBEq α] {pre suf : List α} {x y : α}
    (hnd : (pre ++ suf).Nodup) (hx : x ∈ suf) (hy : y = x ∨ y ∉ pre ++ suf) : ((pre ++ [y]) ++ suf.erase x).Nodup := by
  rcases List.nodup_append.1 hnd with ⟨hpre, hsuf, hdisj⟩
  have hyNotPre : y ∉ pre := fun hp => hy.elim (fun h => hdisj _ (h ▸ hp) _ hx rfl) (fun hn => hn (by simp [hp]))
  have hyNotSufE : y ∉ suf.erase x := fun hs => hy.elim (fun h => not_mem_erase_of_nodup hsuf (h ▸ hs)) (fun hn => hn (by simp [List.mem_of_mem_erase hs]))
  refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨hpre, List.pairwise_singleton _ _, fun a ha b hb => by
    simp only [List.mem_singleton] at hb; subst hb; intro hEq; subst hEq; exact hyNotPre ha⟩,
    hsuf.erase x, fun a ha b hb => ?_⟩
  rcases List.mem_append.1 ha with hap | ha1
  · exact hdisj a hap b (List.mem_of_mem_erase hb)
  · simp only [List.mem_singleton] at ha1; subst ha1; intro hEq; subst hEq; exact hyNotSufE hb


theorem childNamespace_eq_childNsOf {ns ptag : String} (hns : ns = "" ∨ ns = Dom.svgNs) :
    (if (if ns == "" && ptag == "svg" then Dom.svgNs else ns) == Dom.svgNs && ptag != "foreignObject"
      then Dom.svgNs else "") = Dom.childNsOf ns ptag := by
  rcases hns with rfl | rfl <;> by_cases hfo : ptag = "foreignObject"
  · subst hfo; simp [Dom.childNsOf]
  · by_cases hsvg : ptag = "svg" <;> simp [Dom.childNsOf, Dom.svgNs, hfo, hsvg]
  · subst hfo; simp [Dom.childNsOf, Dom.svgNs]
  · simp [Dom.childNsOf, Dom.svgNs, hfo]


theorem nodup_getElem_inj {α : Type} :
    ∀ {xs : List α} {i₁ i₂ : Nat} (h₁ : i₁ < xs.length) (h₂ : i₂ < xs.length), xs.Nodup → xs[i₁] = xs[i₂] → i₁ = i₂
  | [], _, _, h₁, _, _, _ => nomatch h₁
  | x :: xs, 0, 0, _, _, _, _ => rfl
  | x :: xs, 0, i₂ + 1, _, h₂, hnd, hEq => by
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hEq
      exact absurd (hEq.symm ▸ List.getElem_mem (by simpa using h₂)) (List.nodup_cons.1 hnd).1
  | x :: xs, i₁ + 1, 0, h₁, _, hnd, hEq => by
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hEq
      exact absurd (hEq ▸ List.getElem_mem (by simpa using h₁)) (List.nodup_cons.1 hnd).1
  | x :: xs, i₁ + 1, i₂ + 1, h₁, h₂, hnd, hEq =>
      congrArg Nat.succ (nodup_getElem_inj (by simpa using h₁) (by simpa using h₂) (List.nodup_cons.1 hnd).2 hEq)

theorem w3cInsertBefore_fresh_append (pre suf : List Dom.Node) (cn : Dom.Node)
    (hnot : cn ∉ pre ++ suf) (hdisj : ∀ r ∈ suf, r ∉ pre) :
    w3cInsertBefore (pre ++ suf) pre.length cn = pre ++ cn :: suf := by
  unfold w3cInsertBefore; rw [List.drop_left, List.erase_of_not_mem hnot]
  cases suf with
  | nil => simp
  | cons ref rest =>
      have hrc : (ref == cn) = false := beq_eq_false_iff_ne.2 (fun h => hnot (by simp [h]))
      simp only [hrc, Bool.false_eq_true, ↓reduceIte]
      exact insertBeforeRef_split pre rest (hdisj ref (List.mem_cons_self ..))

end Qed
