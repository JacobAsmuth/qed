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

private theorem str_append_prop {P : Char → Prop} {a b : String}
    (ha : ∀ c ∈ a.toList, P c) (hb : ∀ c ∈ b.toList, P c) :
    ∀ c ∈ (a ++ b).toList, P c := by
  intro c hc
  rw [String.toList_append, List.mem_append] at hc
  exact hc.elim (ha c) (hb c)

private theorem str_append_no_lt {a b : String}
    (ha : ∀ c ∈ a.toList, c ≠ '<') (hb : ∀ c ∈ b.toList, c ≠ '<') :
    ∀ c ∈ (a ++ b).toList, c ≠ '<' :=
  str_append_prop ha hb

private theorem lit_no_lt {s : String} (cs : List Char)
    (heq : String.ofList cs = s) (h : cs.all (· != '<') = true) :
    ∀ c ∈ s.toList, c ≠ '<' := by
  subst heq
  rw [String.toList_ofList]
  rw [List.all_eq_true] at h
  intro c hc
  exact bne_iff_ne.1 (h c hc)

private theorem lit_empty_no_lt : ∀ c ∈ ("").toList, c ≠ '<' :=
  lit_no_lt [] rfl rfl

private theorem lit_space_no_lt : ∀ c ∈ (" ").toList, c ≠ '<' :=
  lit_no_lt [' '] rfl rfl

private theorem lit_nl_no_lt : ∀ c ∈ ("\n").toList, c ≠ '<' :=
  lit_no_lt ['\n'] rfl rfl

private theorem lit_open_brace_no_lt : ∀ c ∈ (" { ").toList, c ≠ '<' :=
  lit_no_lt [' ', '{', ' '] rfl rfl

private theorem lit_close_brace_no_lt : ∀ c ∈ (" }").toList, c ≠ '<' :=
  lit_no_lt [' ', '}'] rfl rfl

private theorem sanitizeCssAtom_no_lt (s : String) :
    ∀ c ∈ (sanitizeCssAtom s).toList, c ≠ '<' := by
  intro c hc
  have hs := sanitizeCssAtom_safe s c hc
  simp only [isSafeCssAtomChar, Bool.and_eq_true, bne_iff_ne] at hs
  exact hs.1.1.2

private theorem sanitizeCssSelector_no_lt (s : String) :
    ∀ c ∈ (sanitizeCssSelector s).toList, c ≠ '<' := by
  intro c hc
  have hs := sanitizeCssSelector_safe s c hc
  simp only [isSafeCssSelectorChar, Bool.and_eq_true, bne_iff_ne] at hs
  exact hs.1.2

private theorem sanitizeCssIdent_no_lt (s : String) :
    ∀ c ∈ (sanitizeCssIdent s).toList, c ≠ '<' := by
  intro c hc
  have hs := sanitizeCssIdent_safe s c hc
  intro heq
  subst heq
  simp [isSafeCssIdentChar, Char.isAlphanum, Char.isAlpha, Char.isDigit] at hs

private theorem sanitizeInlineCssAtom_no_lt_or_quote (s : String) :
    ∀ c ∈ (sanitizeInlineCssAtom s).toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'' := by
  intro c hc
  have hs := sanitizeInlineCssAtom_safe s c hc
  simp only [isSafeInlineCssChar, isSafeCssAtomChar, Bool.and_eq_true, bne_iff_ne] at hs
  exact ⟨hs.1.1.1.1.2, hs.1.1.1.2, hs.1.2, hs.2⟩

mutual
  theorem Item.render_no_lt : ∀ (i : Item), ∀ c ∈ (Item.render i).toList, c ≠ '<'
    | .decl p v => by
        simp only [Item.render]
        exact str_append_no_lt
          (str_append_no_lt
            (str_append_no_lt (sanitizeCssAtom_no_lt p) (lit_no_lt [':', ' '] rfl rfl))
            (sanitizeCssAtom_no_lt v))
          (lit_no_lt [';'] rfl rfl)
    | .nest sel b => by
        simp only [Item.render]
        exact str_append_no_lt
          (str_append_no_lt
            (str_append_no_lt (sanitizeCssSelector_no_lt sel) lit_open_brace_no_lt)
            (Item.renderList_no_lt b))
          lit_close_brace_no_lt

  theorem Item.renderList_no_lt : ∀ (is : List Item), ∀ c ∈ (Item.renderList is).toList, c ≠ '<'
    | [] => lit_empty_no_lt
    | [i] => Item.render_no_lt i
    | i :: j :: rest => by
        simp only [Item.renderList]
        exact str_append_no_lt
          (str_append_no_lt (Item.render_no_lt i) lit_space_no_lt)
          (Item.renderList_no_lt (j :: rest))
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
  | [], _ => lit_empty_no_lt
  | [s], hs => hs s (List.mem_cons_self ..)
  | s₁ :: s₂ :: rest, hs => by
      have h1 := hs s₁ (List.mem_cons_self ..)
      have h2 := cssJoinLines_no_lt (s₂ :: rest) (fun x hx => hs x (List.mem_cons_of_mem _ hx))
      simp only [cssJoinLines]
      exact str_append_no_lt (str_append_no_lt h1 lit_nl_no_lt) h2

private theorem renderThemeRule_no_lt (item : Item) :
    ∀ c ∈ (renderThemeRule item).toList, c ≠ '<' := by
  cases item with
  | decl p v => exact Item.render_no_lt (.decl p v)
  | nest sel b =>
      simp only [renderThemeRule]
      split
      · exact str_append_no_lt
          (str_append_no_lt
            (str_append_no_lt (sanitizeCssSelector_no_lt sel) lit_open_brace_no_lt)
            (Item.renderList_no_lt b))
          lit_close_brace_no_lt
      · exact str_append_no_lt
          (str_append_no_lt
            (str_append_no_lt
              (str_append_no_lt (lit_no_lt [':', 'w', 'h', 'e', 'r', 'e', '('] rfl rfl) (sanitizeCssSelector_no_lt sel))
              (lit_no_lt [')', ' ', '{', ' '] rfl rfl))
            (Item.renderList_no_lt b))
          lit_close_brace_no_lt

theorem Theme.render_no_lt (th : Theme) :
    ∀ c ∈ (Theme.render th).toList, c ≠ '<' := by
  unfold Theme.render
  dsimp only
  apply cssJoinLines_no_lt
  intro s hs
  rw [List.mem_append] at hs
  rcases hs with h1 | hreset
  · rw [List.mem_append] at h1
    rcases h1 with hlight | hdark
    · split at hlight
      · nomatch hlight
      · simp only [List.mem_singleton] at hlight
        subst hlight
        exact str_append_no_lt
          (str_append_no_lt (lit_no_lt [':', 'r', 'o', 'o', 't', ' ', '{', ' '] rfl rfl) (Item.renderList_no_lt _))
          lit_close_brace_no_lt
    · split at hdark
      · nomatch hdark
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hdark
        rcases hdark with rfl | rfl
        · exact str_append_no_lt
            (str_append_no_lt
              (lit_no_lt ['@', 'm', 'e', 'd', 'i', 'a', ' ', '(', 'p', 'r', 'e', 'f', 'e', 'r', 's', '-',
                'c', 'o', 'l', 'o', 'r', '-', 's', 'c', 'h', 'e', 'm', 'e', ':', ' ', 'd', 'a', 'r', 'k', ')',
                ' ', '{', ' ', ':', 'r', 'o', 'o', 't', ' ', '{', ' '] rfl rfl)
              (Item.renderList_no_lt _))
            (lit_no_lt [' ', '}', ' ', '}'] rfl rfl)
        · exact str_append_no_lt
            (str_append_no_lt
              (lit_no_lt ['[', 'd', 'a', 't', 'a', '-', 't', 'h', 'e', 'm', 'e', '=', '"', 'd', 'a', 'r', 'k', '"',
                ']', ' ', '{', ' '] rfl rfl)
              (Item.renderList_no_lt _))
            lit_close_brace_no_lt
  · rcases List.mem_map.1 hreset with ⟨item, _, rfl⟩
    exact renderThemeRule_no_lt item

theorem Theme.render_no_closeSeq (th : Theme) :
    containsCloseSeq (Theme.render th).toList = false :=
  containsCloseSeq_of_no_lt (Theme.render_no_lt th)

theorem Keyframes.renderSteps_no_lt :
    ∀ (steps : List (String × List Item)), ∀ c ∈ (Keyframes.renderSteps steps).toList, c ≠ '<'
  | [] => lit_empty_no_lt
  | [(sel, body)] =>
      str_append_no_lt
        (str_append_no_lt
          (str_append_no_lt (sanitizeCssSelector_no_lt sel) lit_open_brace_no_lt)
          (Item.renderList_no_lt body))
        lit_close_brace_no_lt
  | (sel, body) :: s2 :: rest =>
      str_append_no_lt
        (str_append_no_lt
          (str_append_no_lt
            (str_append_no_lt (sanitizeCssSelector_no_lt sel) lit_open_brace_no_lt)
            (Item.renderList_no_lt body))
          (lit_no_lt [' ', '}', ' '] rfl rfl))
        (Keyframes.renderSteps_no_lt (s2 :: rest))

theorem Keyframes.rule_no_lt (kf : Keyframes) :
    ∀ c ∈ kf.rule.toList, c ≠ '<' := by
  simp only [Keyframes.rule]
  exact str_append_no_lt
    (str_append_no_lt
      (str_append_no_lt
        (str_append_no_lt
          (lit_no_lt ['@', 'k', 'e', 'y', 'f', 'r', 'a', 'm', 'e', 's', ' '] rfl rfl)
          (sanitizeCssIdent_no_lt kf.name))
        lit_open_brace_no_lt)
      (Keyframes.renderSteps_no_lt kf.steps))
    lit_close_brace_no_lt

theorem Keyframes.rule_no_closeSeq (kf : Keyframes) :
    containsCloseSeq kf.rule.toList = false :=
  containsCloseSeq_of_no_lt (Keyframes.rule_no_lt kf)

theorem Style.rule_no_lt (s : Style) :
    ∀ c ∈ (Style.rule s).toList, c ≠ '<' := by
  unfold Style.rule
  split
  · intro c hc
    exact bne_iff_ne.1 (sanitizeWith_safe (· != '<') s.raw c hc)
  · exact str_append_no_lt
      (str_append_no_lt
        (str_append_no_lt
          (str_append_no_lt (lit_no_lt ['.'] rfl rfl)
            (fun c hc => bne_iff_ne.1 (sanitizeWith_safe (· != '<') s.className c hc)))
          lit_open_brace_no_lt)
        (fun c hc => bne_iff_ne.1 (sanitizeWith_safe (· != '<') s.raw c hc)))
      lit_close_brace_no_lt

theorem renderStyleSheet_no_lt (styles : List Style) :
    ∀ c ∈ (renderStyleSheet styles).toList, c ≠ '<' := by
  unfold renderStyleSheet
  dsimp only
  apply cssJoinLines_no_lt
  intro r hr
  rw [List.mem_append] at hr
  rcases hr with h1 | hscoped
  · rw [List.mem_append] at h1
    rcases h1 with hglob | hextra
    · rcases List.mem_map.1 hglob with ⟨s, _, rfl⟩
      exact Style.rule_no_lt s
    · rcases List.mem_map.1 hextra with ⟨e, _, rfl⟩
      intro c hc
      exact bne_iff_ne.1 (sanitizeWith_safe (· != '<') e c hc)
  · rcases List.mem_map.1 hscoped with ⟨s, _, rfl⟩
    exact Style.rule_no_lt s

theorem renderStyleSheet_no_closeSeq (styles : List Style) :
    containsCloseSeq (renderStyleSheet styles).toList = false :=
  containsCloseSeq_of_no_lt (renderStyleSheet_no_lt styles)

/-! ## Safe Dynamic Inline Style Proofs -/

private theorem lit_safe_inline {s : String} (cs : List Char)
    (heq : String.ofList cs = s)
    (h : cs.all (fun c => c != '<' && c != '>' && c != '"' && c != '\'') = true) :
    ∀ c ∈ s.toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'' := by
  subst heq
  rw [String.toList_ofList]
  rw [List.all_eq_true] at h
  intro c hc
  have h1 := h c hc
  simp only [Bool.and_eq_true, bne_iff_ne] at h1
  exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩

theorem inlineStyleItem_safe (i : Item) :
    ∀ c ∈ (inlineStyleItem i).toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'' := by
  cases i with
  | decl p v =>
      simp only [inlineStyleItem]
      exact str_append_prop
        (str_append_prop
          (str_append_prop (sanitizeInlineCssAtom_no_lt_or_quote p) (lit_safe_inline [':', ' '] rfl rfl))
          (sanitizeInlineCssAtom_no_lt_or_quote v))
        (lit_safe_inline [';'] rfl rfl)
  | nest _ _ =>
      exact lit_safe_inline [] rfl rfl

theorem inlineStyleStr_safe :
    ∀ (items : List Item), ∀ c ∈ (inlineStyleStr items).toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\''
  | [] => lit_safe_inline [] rfl rfl
  | [i] => inlineStyleItem_safe i
  | i :: j :: rest => by
      simp only [inlineStyleStr]
      split
      · exact inlineStyleStr_safe (j :: rest)
      · split
        · exact inlineStyleItem_safe i
        · exact str_append_prop
            (str_append_prop (inlineStyleItem_safe i) (lit_safe_inline [' '] rfl rfl))
            (inlineStyleStr_safe (j :: rest))

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
