import Qed.Style.Core

namespace Qed

/-! ## CSS Injection & `<style>` Breakout Safety Proofs -/

theorem hasCommentOpenLoop_stripCommentOpenLoop (cs : List Char) :
    ∀ (b : Bool), hasCommentOpenLoop b (stripCommentOpenLoop b cs) = false := by
  induction cs with
  | nil => intro _; rfl
  | cons c rest ih =>
      intro b
      simp only [stripCommentOpenLoop]
      cases h : (b && c == '*')
      · simpa [hasCommentOpenLoop, h] using ih (c == '/')
      · cases b <;> simp at h
        simpa [hasCommentOpenLoop] using ih true

private theorem stripCommentOpenLoop_mem :
    ∀ (cs : List Char) (b : Bool) {c : Char}, c ∈ stripCommentOpenLoop b cs → c ∈ cs
  | [], _, _, h => nomatch h
  | x :: xs, b, c, hc => by
      dsimp only [stripCommentOpenLoop] at hc
      split at hc
      · exact List.mem_cons_of_mem x (stripCommentOpenLoop_mem xs true hc)
      · rcases List.mem_cons.1 hc with rfl | ht
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem x (stripCommentOpenLoop_mem xs (x == '/') ht)

private theorem sanitizeWith_safe (p : Char → Bool) (s : String) :
    ∀ c ∈ (sanitizeWith p s).toList, p c = true := by
  unfold sanitizeWith
  dsimp only
  by_cases h : s.toList.all p = true
  · simp only [h, ↓reduceIte]
    rw [List.all_eq_true] at h
    exact h
  · simp only [h, Bool.false_eq_true, ↓reduceIte, String.toList_ofList]
    intro c hc
    exact (List.mem_filter.1 hc).2

private theorem sanitizeCssWith_safe (p : Char → Bool) (s : String) :
    ∀ c ∈ (sanitizeCssWith p s).toList, p c = true := by
  unfold sanitizeCssWith
  dsimp only
  split
  · simp only [String.toList_ofList]
    intro c hc
    exact sanitizeWith_safe p s c (stripCommentOpenLoop_mem _ false hc)
  · exact sanitizeWith_safe p s

private theorem sanitizeCssWith_no_comment (p : Char → Bool) (s : String) :
    hasCommentOpen (sanitizeCssWith p s).toList = false := by
  unfold sanitizeCssWith
  dsimp only
  split
  · simpa [hasCommentOpen, stripCommentOpen] using hasCommentOpenLoop_stripCommentOpenLoop _ false
  · exact Bool.eq_false_iff.2 ‹_›

theorem sanitizeCssAtom_safe (s : String) :
    ∀ c ∈ (sanitizeCssAtom s).toList, isSafeCssAtomChar c = true :=
  sanitizeCssWith_safe isSafeCssAtomChar s

theorem sanitizeCssSelector_safe (s : String) :
    ∀ c ∈ (sanitizeCssSelector s).toList, isSafeCssSelectorChar c = true :=
  sanitizeCssWith_safe isSafeCssSelectorChar s

theorem sanitizeInlineCssAtom_safe (s : String) :
    ∀ c ∈ (sanitizeInlineCssAtom s).toList, isSafeInlineCssChar c = true :=
  sanitizeCssWith_safe isSafeInlineCssChar s

theorem sanitizeCssIdent_safe (s : String) :
    ∀ c ∈ (sanitizeCssIdent s).toList, isSafeCssIdentChar c = true :=
  sanitizeWith_safe isSafeCssIdentChar s

theorem sanitizeCssAtom_no_comment (s : String) :
    hasCommentOpen (sanitizeCssAtom s).toList = false :=
  sanitizeCssWith_no_comment isSafeCssAtomChar s

theorem sanitizeCssSelector_no_comment (s : String) :
    hasCommentOpen (sanitizeCssSelector s).toList = false :=
  sanitizeCssWith_no_comment isSafeCssSelectorChar s

theorem sanitizeInlineCssAtom_no_comment (s : String) :
    hasCommentOpen (sanitizeInlineCssAtom s).toList = false :=
  sanitizeCssWith_no_comment isSafeInlineCssChar s

private theorem no_lt_implies_no_closeSeq :
    ∀ (cs : List Char), (∀ c ∈ cs, c ≠ '<') → containsCloseSeqLoop false cs = false
  | [], _ => rfl
  | c :: rest, hno => by
      have hc : c ≠ '<' := hno c (List.mem_cons_self ..)
      have hcb : (c == '<') = false := beq_eq_false_iff_ne.2 hc
      simpa [containsCloseSeqLoop, hcb] using
        no_lt_implies_no_closeSeq rest (fun x hx => hno x (List.mem_cons_of_mem c hx))

theorem containsCloseSeq_of_no_lt {s : String} (hno : ∀ c ∈ s.toList, c ≠ '<') :
    containsCloseSeq s.toList = false :=
  no_lt_implies_no_closeSeq s.toList hno

private theorem lit_prop {P : Char → Prop} {p : Char → Bool}
    (hp : ∀ c, p c = true → P c) (s : String) (h : s.toList.all p = true) :
    ∀ c ∈ s.toList, P c := by
  rw [List.all_eq_true] at h
  exact fun c hc => hp c (h c hc)

private theorem lit_no_lt (s : String) (h : s.toList.all (· != '<') = true) :
    ∀ c ∈ s.toList, c ≠ '<' :=
  lit_prop (fun _ h => bne_iff_ne.1 h) s h

private theorem lit_safe_inline (s : String)
    (h : s.toList.all (fun c => c != '<' && c != '>' && c != '"' && c != '\'') = true) :
    ∀ c ∈ s.toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'' :=
  lit_prop (fun _ h => by simp only [Bool.and_eq_true, bne_iff_ne] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩) s h

private theorem sanitizeCssAtom_no_lt (s : String) : ∀ c ∈ (sanitizeCssAtom s).toList, c ≠ '<' := fun c hc => by
  have hs := sanitizeCssAtom_safe s c hc; simp only [isSafeCssAtomChar, Bool.and_eq_true, bne_iff_ne] at hs; exact hs.1.1.2

private theorem sanitizeCssSelector_no_lt (s : String) : ∀ c ∈ (sanitizeCssSelector s).toList, c ≠ '<' := fun c hc => by
  have hs := sanitizeCssSelector_safe s c hc; simp only [isSafeCssSelectorChar, Bool.and_eq_true, bne_iff_ne] at hs; exact hs.1.2

private theorem sanitizeCssIdent_no_lt (s : String) : ∀ c ∈ (sanitizeCssIdent s).toList, c ≠ '<' := fun c hc heq => by
  have hs := sanitizeCssIdent_safe s c hc; subst heq
  simp [isSafeCssIdentChar, Char.isAlphanum, Char.isAlpha, Char.isDigit] at hs

private theorem sanitizeInlineCssAtom_no_lt_or_quote (s : String) :
    ∀ c ∈ (sanitizeInlineCssAtom s).toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'' := fun c hc => by
  have hs := sanitizeInlineCssAtom_safe s c hc
  simp only [isSafeInlineCssChar, isSafeCssAtomChar, Bool.and_eq_true, bne_iff_ne] at hs
  exact ⟨hs.1.1.1.1.2, hs.1.1.1.2, hs.1.2, hs.2⟩

local macro "solve_str_prop" : tactic =>
  `(tactic| (
    intro c
    try simp only [String.toList_append, List.mem_append, or_imp]
    repeat refine And.intro ?_ ?_
    all_goals (
      revert c
      first
        | with_reducible assumption
        | with_reducible exact sanitizeCssAtom_no_lt _
        | with_reducible exact sanitizeCssSelector_no_lt _
        | with_reducible exact sanitizeCssIdent_no_lt _
        | with_reducible exact sanitizeInlineCssAtom_no_lt_or_quote _
        | with_reducible exact fun c hc => bne_iff_ne.1 (sanitizeWith_safe (· != '<') _ c hc)
        | (apply lit_no_lt; decide)
        | (apply lit_safe_inline; decide))))

mutual
  theorem Item.render_no_lt : ∀ (i : Item), ∀ c ∈ (Item.render i).toList, c ≠ '<'
    | .decl p v => by simp only [Item.render]; solve_str_prop
    | .nest sel b => by have := Item.renderList_no_lt b; simp only [Item.render]; solve_str_prop

  theorem Item.renderList_no_lt : ∀ (is : List Item), ∀ c ∈ (Item.renderList is).toList, c ≠ '<'
    | [] => lit_no_lt "" (by decide)
    | [i] => Item.render_no_lt i
    | i :: j :: rest => by
        have := Item.render_no_lt i; have := Item.renderList_no_lt (j :: rest)
        simp only [Item.renderList]; solve_str_prop
end

theorem Item.render_no_closeSeq (i : Item) :
    containsCloseSeq (Item.render i).toList = false :=
  containsCloseSeq_of_no_lt (Item.render_no_lt i)

theorem Item.renderList_no_closeSeq (is : List Item) :
    containsCloseSeq (Item.renderList is).toList = false :=
  containsCloseSeq_of_no_lt (Item.renderList_no_lt is)

private theorem cssJoinLines_no_lt :
    ∀ (xs : List String), (∀ s ∈ xs, ∀ c ∈ s.toList, c ≠ '<') →
      ∀ c ∈ (cssJoinLines xs).toList, c ≠ '<'
  | [], _ => lit_no_lt "" (by decide)
  | [s], hs => hs s (List.mem_cons_self ..)
  | s₁ :: s₂ :: rest, hs => by
      have := hs s₁ (List.mem_cons_self ..)
      have := cssJoinLines_no_lt (s₂ :: rest) (fun x hx => hs x (List.mem_cons_of_mem _ hx))
      simp only [cssJoinLines]; solve_str_prop

private theorem renderThemeRule_no_lt (item : Item) :
    ∀ c ∈ (renderThemeRule item).toList, c ≠ '<' := by
  cases item with
  | decl p v => exact Item.render_no_lt (.decl p v)
  | nest sel b =>
      have := Item.renderList_no_lt b
      simp only [renderThemeRule]; split <;> solve_str_prop

theorem Theme.render_no_lt (th : Theme) :
    ∀ c ∈ (Theme.render th).toList, c ≠ '<' := by
  apply cssJoinLines_no_lt; intro s hs
  simp only [List.mem_append, List.mem_map] at hs
  rcases hs with (hlight | hdark) | ⟨item, _, rfl⟩
  · split at hlight
    · nomatch hlight
    · simp only [List.mem_singleton] at hlight; subst hlight
      have := Item.renderList_no_lt th.lightDecls; solve_str_prop
  · split at hdark
    · nomatch hdark
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hdark
      rcases hdark with rfl | rfl <;> (have := Item.renderList_no_lt th.darkDecls; solve_str_prop)
  · exact renderThemeRule_no_lt item

theorem Theme.render_no_closeSeq (th : Theme) :
    containsCloseSeq (Theme.render th).toList = false :=
  containsCloseSeq_of_no_lt (Theme.render_no_lt th)

theorem Keyframes.renderSteps_no_lt (steps : List (String × List Item)) :
    ∀ c ∈ (Keyframes.renderSteps steps).toList, c ≠ '<' :=
  Item.renderList_no_lt _

theorem Keyframes.rule_no_lt (kf : Keyframes) :
    ∀ c ∈ kf.rule.toList, c ≠ '<' := by
  have := Keyframes.renderSteps_no_lt kf.steps
  simp only [Keyframes.rule]; solve_str_prop

theorem Keyframes.rule_no_closeSeq (kf : Keyframes) :
    containsCloseSeq kf.rule.toList = false :=
  containsCloseSeq_of_no_lt (Keyframes.rule_no_lt kf)

theorem Style.rule_no_lt (s : Style) :
    ∀ c ∈ (Style.rule s).toList, c ≠ '<' := by
  unfold Style.rule; split <;> solve_str_prop

theorem renderStyleSheet_no_lt (styles : List Style) :
    ∀ c ∈ (renderStyleSheet styles).toList, c ≠ '<' := by
  apply cssJoinLines_no_lt; intro r hr
  simp only [List.mem_append, List.mem_map] at hr
  rcases hr with (⟨s, _, rfl⟩ | ⟨e, _, rfl⟩) | ⟨s, _, rfl⟩
  · exact Style.rule_no_lt s
  · exact fun c hc => bne_iff_ne.1 (sanitizeWith_safe (· != '<') e c hc)
  · exact Style.rule_no_lt s

theorem renderStyleSheet_no_closeSeq (styles : List Style) :
    containsCloseSeq (renderStyleSheet styles).toList = false :=
  containsCloseSeq_of_no_lt (renderStyleSheet_no_lt styles)

/-! ## Safe Dynamic Inline Style Proofs -/

theorem inlineStyleItem_safe (i : Item) :
    ∀ c ∈ (inlineStyleItem i).toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'' := by
  cases i <;> (simp only [inlineStyleItem]; solve_str_prop)

theorem inlineStyleStr_safe :
    ∀ (items : List Item), ∀ c ∈ (inlineStyleStr items).toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\''
  | [] => lit_safe_inline "" (by decide)
  | [i] => inlineStyleItem_safe i
  | i :: j :: rest => by
      have := inlineStyleItem_safe i; have := inlineStyleStr_safe (j :: rest)
      simp only [inlineStyleStr]
      split
      · assumption
      · split
        · assumption
        · solve_str_prop

theorem inlineStyleStr_no_lt (items : List Item) :
    ∀ c ∈ (inlineStyleStr items).toList, c ≠ '<' :=
  fun c hc => (inlineStyleStr_safe items c hc).1

theorem inlineStyleStr_no_quote (items : List Item) :
    ∀ c ∈ (inlineStyleStr items).toList, c ≠ '"' ∧ c ≠ '\'' :=
  fun c hc => ⟨(inlineStyleStr_safe items c hc).2.2.1, (inlineStyleStr_safe items c hc).2.2.2⟩

theorem inlineStyleStr_no_closeSeq (items : List Item) :
    containsCloseSeq (inlineStyleStr items).toList = false :=
  containsCloseSeq_of_no_lt (inlineStyleStr_no_lt items)

@[simp] theorem Attr.valid_inlineStyle {msg : Type} (items : List Item) :
    (inlineStyle items : Attr msg).valid = true := rfl

@[simp] theorem Attr.valid_styleVars {msg : Type} (vars : List Item) :
    (styleVars vars : Attr msg).valid = true := rfl

@[simp] theorem Attr.isLocalCell_inlineStyle {msg : Type} (items : List Item) :
    (inlineStyle items : Attr msg).isLocalCell = false := rfl

@[simp] theorem Attr.isLocalCell_styleVars {msg : Type} (vars : List Item) :
    (styleVars vars : Attr msg).isLocalCell = false := rfl

/-! ## Theme Coverage Lemmas -/

@[simp] theorem Theme.coversAll_nil (th : Theme) : th.coversAll [] = true := rfl

@[simp] theorem Theme.coversAll_cons (th : Theme) (s : Style) (ss : List Style) :
    th.coversAll (s :: ss) = (th.coversStyle s && th.coversAll ss) := rfl

end Qed
