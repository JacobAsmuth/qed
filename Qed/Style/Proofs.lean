import Qed.Style.Core

namespace Qed

theorem hasCommentOpenLoop_stripCommentOpenLoop : ∀ (cs : List Char) (b : Bool), hasCommentOpenLoop b (stripCommentOpenLoop b cs) = false
  | [], _ => rfl
  | c :: rest, b => by
      simp only [stripCommentOpenLoop]; cases h : (b && c == '*')
      · simpa [hasCommentOpenLoop, h] using hasCommentOpenLoop_stripCommentOpenLoop rest (c == '/')
      · cases b <;> simp at h; simpa [hasCommentOpenLoop] using hasCommentOpenLoop_stripCommentOpenLoop rest true

private theorem stripCommentOpenLoop_mem : ∀ (cs : List Char) (b : Bool) {c : Char}, c ∈ stripCommentOpenLoop b cs → c ∈ cs
  | [], _, _, h => nomatch h
  | x :: xs, b, _, hc => by
      dsimp only [stripCommentOpenLoop] at hc
      split at hc
      · exact List.mem_cons_of_mem x (stripCommentOpenLoop_mem xs true hc)
      · exact (List.mem_cons.1 hc).elim (· ▸ List.mem_cons_self ..) (List.mem_cons_of_mem x <| stripCommentOpenLoop_mem xs (x == '/') ·)

private theorem sanitizeWith_safe (p : Char → Bool) (s : String) : ∀ c ∈ (sanitizeWith p s).toList, p c = true := by
  unfold sanitizeWith; dsimp only; split
  · exact List.all_eq_true.1 ‹_›
  · exact fun _ hc => (List.mem_filter.1 (String.toList_ofList ▸ hc)).2

private theorem sanitizeCssWith_safe (p : Char → Bool) (s : String) : ∀ c ∈ (sanitizeCssWith p s).toList, p c = true := by
  unfold sanitizeCssWith; dsimp only; split
  · exact fun c hc => sanitizeWith_safe p s c (stripCommentOpenLoop_mem _ false (by simpa [stripCommentOpen] using hc))
  · exact sanitizeWith_safe p s

private theorem sanitizeCssWith_no_comment (p : Char → Bool) (s : String) : hasCommentOpen (sanitizeCssWith p s).toList = false := by
  unfold sanitizeCssWith; dsimp only; split
  · simpa [hasCommentOpen, stripCommentOpen] using hasCommentOpenLoop_stripCommentOpenLoop _ false
  · exact Bool.eq_false_iff.2 ‹_›

theorem sanitizeCssAtom_safe (s : String) : ∀ c ∈ (sanitizeCssAtom s).toList, isSafeCssAtomChar c = true := sanitizeCssWith_safe _ s
theorem sanitizeCssSelector_safe (s : String) : ∀ c ∈ (sanitizeCssSelector s).toList, isSafeCssSelectorChar c = true := sanitizeCssWith_safe _ s
theorem sanitizeInlineCssAtom_safe (s : String) : ∀ c ∈ (sanitizeInlineCssAtom s).toList, isSafeInlineCssChar c = true := sanitizeCssWith_safe _ s
theorem sanitizeCssIdent_safe (s : String) : ∀ c ∈ (sanitizeCssIdent s).toList, isSafeCssIdentChar c = true := sanitizeWith_safe _ s
theorem sanitizeCssAtom_no_comment (s : String) : hasCommentOpen (sanitizeCssAtom s).toList = false := sanitizeCssWith_no_comment _ s
theorem sanitizeCssSelector_no_comment (s : String) : hasCommentOpen (sanitizeCssSelector s).toList = false := sanitizeCssWith_no_comment _ s
theorem sanitizeInlineCssAtom_no_comment (s : String) : hasCommentOpen (sanitizeInlineCssAtom s).toList = false := sanitizeCssWith_no_comment _ s

private theorem no_lt_implies_no_closeSeq : ∀ (cs : List Char), (∀ c ∈ cs, c ≠ '<') → containsCloseSeqLoop false cs = false
  | [], _ => rfl
  | c :: rest, hno => by
      have hcb : (c == '<') = false := beq_eq_false_iff_ne.2 (hno c (List.mem_cons_self ..))
      simpa [containsCloseSeqLoop, hcb] using no_lt_implies_no_closeSeq rest fun x hx => hno x (List.mem_cons_of_mem c hx)
theorem containsCloseSeq_of_no_lt {s : String} (hno : ∀ c ∈ s.toList, c ≠ '<') : containsCloseSeq s.toList = false := no_lt_implies_no_closeSeq s.toList hno

private theorem noLtBytes_ne_60 : ∀ {bs : List UInt8}, noLtBytes bs = true → ∀ b ∈ bs, b ≠ 60
  | [], _, _, h => nomatch h
  | x :: xs, h, _, hb => by
      unfold noLtBytes at h; split at h
      · cases h
      · rename_i hne; exact (List.mem_cons.1 hb).elim (fun e heq => hne (by subst e heq; rfl)) (noLtBytes_ne_60 h _)

private theorem sanitizeNoLt_no_lt (s : String) : ∀ c ∈ (sanitizeNoLt s).toList, c ≠ '<' := by
  unfold sanitizeNoLt; split
  · intro c hc hlt; subst hlt
    have hflat : s.toByteArray.data.toList = s.toList.flatMap String.utf8EncodeChar := by
      rw [show s.toByteArray = s.toList.utf8Encode by rw [← String.toByteArray_ofList, String.ofList_toList], List.utf8Encode, List.data_toByteArray, List.toList_toArray]
    exact noLtBytes_ne_60 ‹_› 60 (hflat ▸ List.mem_flatMap.2 ⟨'<', hc, by decide⟩) rfl
  · exact fun c hc => bne_iff_ne.1 (sanitizeWith_safe (· != '<') s c hc)

private theorem lit_prop {P : Char → Prop} {p : Char → Bool} (hp : ∀ c, p c = true → P c) (s : String) (h : s.toList.all p = true) : ∀ c ∈ s.toList, P c := fun c hc => hp c (List.all_eq_true.1 h c hc)
private theorem lit_no_lt (s : String) (h : s.toList.all (· != '<') = true := by decide) : ∀ c ∈ s.toList, c ≠ '<' := lit_prop (fun _ => bne_iff_ne.1) s h
private theorem lit_safe_inline (s : String) (h : s.toList.all (fun c => c != '<' && c != '>' && c != '"' && c != '\'') = true := by decide) : ∀ c ∈ s.toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'' :=
  lit_prop (fun _ h => by simp only [Bool.and_eq_true, bne_iff_ne] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩) s h
private theorem app2 {P : Char → Prop} {a b : String} (ha : ∀ c ∈ a.toList, P c) (hb : ∀ c ∈ b.toList, P c) : ∀ c ∈ (a ++ b).toList, P c := fun c hc => (List.mem_append.1 (String.toList_append ▸ hc)).elim (ha c) (hb c)
private theorem app3 {P : Char → Prop} {a b d : String} (ha : ∀ c ∈ a.toList, P c) (hb : ∀ c ∈ b.toList, P c) (hd : ∀ c ∈ d.toList, P c) : ∀ c ∈ (a ++ b ++ d).toList, P c := app2 (app2 ha hb) hd
private theorem app4 {P : Char → Prop} {a b d e : String} (ha : ∀ c ∈ a.toList, P c) (hb : ∀ c ∈ b.toList, P c) (hd : ∀ c ∈ d.toList, P c) (he : ∀ c ∈ e.toList, P c) : ∀ c ∈ (a ++ b ++ d ++ e).toList, P c := app2 (app3 ha hb hd) he
private theorem app5 {P : Char → Prop} {a b d e f : String} (ha : ∀ c ∈ a.toList, P c) (hb : ∀ c ∈ b.toList, P c) (hd : ∀ c ∈ d.toList, P c) (he : ∀ c ∈ e.toList, P c) (hf : ∀ c ∈ f.toList, P c) : ∀ c ∈ (a ++ b ++ d ++ e ++ f).toList, P c := app2 (app4 ha hb hd he) hf

private theorem sanitizeCssAtom_no_lt (s : String) : ∀ c ∈ (sanitizeCssAtom s).toList, c ≠ '<' := fun c hc => by
  have hs := sanitizeCssAtom_safe s c hc; simp only [isSafeCssAtomChar, Bool.and_eq_true, bne_iff_ne] at hs; exact hs.1.1.2
private theorem sanitizeCssIdent_no_lt (s : String) : ∀ c ∈ (sanitizeCssIdent s).toList, c ≠ '<' := fun c hc heq => by
  have hs := sanitizeCssIdent_safe s c hc; subst heq; simp [isSafeCssIdentChar, Char.isAlphanum, Char.isAlpha, Char.isDigit] at hs
private theorem sanitizeInlineCssAtom_no_lt_or_quote (s : String) : ∀ c ∈ (sanitizeInlineCssAtom s).toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\'' := fun c hc => by
  have hs := sanitizeInlineCssAtom_safe s c hc; simp only [isSafeInlineCssChar, isSafeCssAtomChar, Bool.and_eq_true, bne_iff_ne] at hs; exact ⟨hs.1.1.1.1.2, hs.1.1.1.2, hs.1.2, hs.2⟩

mutual
  theorem Item.render_no_lt : ∀ (i : Item), ∀ c ∈ (Item.render i).toList, c ≠ '<'
    | .decl p v => app4 (sanitizeCssAtom_no_lt p) (lit_no_lt ": ") (sanitizeCssAtom_no_lt v) (lit_no_lt ";")
    | .nest s b => app4 (sanitizeCssAtom_no_lt s) (lit_no_lt " { ") (Item.renderList_no_lt b) (lit_no_lt " }")
  theorem Item.renderList_no_lt : ∀ (is : List Item), ∀ c ∈ (Item.renderList is).toList, c ≠ '<'
    | [] => lit_no_lt "" | [i] => Item.render_no_lt i | i :: j :: rest => app3 (Item.render_no_lt i) (lit_no_lt " ") (Item.renderList_no_lt (j :: rest))
end
theorem Item.render_no_closeSeq (i : Item) : containsCloseSeq (Item.render i).toList = false := containsCloseSeq_of_no_lt (Item.render_no_lt i)
theorem Item.renderList_no_closeSeq (is : List Item) : containsCloseSeq (Item.renderList is).toList = false := containsCloseSeq_of_no_lt (Item.renderList_no_lt is)

private theorem cssJoinLines_no_lt : ∀ (xs : List String), (∀ s ∈ xs, ∀ c ∈ s.toList, c ≠ '<') → ∀ c ∈ (cssJoinLines xs).toList, c ≠ '<'
  | [], _ => lit_no_lt "" | [s], hs => hs s (List.mem_cons_self ..)
  | s₁ :: s₂ :: rest, hs => app3 (hs s₁ (List.mem_cons_self ..)) (lit_no_lt "\n") (cssJoinLines_no_lt (s₂ :: rest) fun x hx => hs x (List.mem_cons_of_mem _ hx))

private theorem renderThemeRule_no_lt : ∀ (item : Item), ∀ c ∈ (renderThemeRule item).toList, c ≠ '<'
  | .decl p v => Item.render_no_lt (.decl p v)
  | .nest s b => by simp only [renderThemeRule]; split; exact app4 (sanitizeCssAtom_no_lt s) (lit_no_lt " { ") (Item.renderList_no_lt b) (lit_no_lt " }"); exact app5 (lit_no_lt ":where(") (sanitizeCssAtom_no_lt s) (lit_no_lt ") { ") (Item.renderList_no_lt b) (lit_no_lt " }")

theorem Theme.render_no_lt (th : Theme) : ∀ c ∈ (Theme.render th).toList, c ≠ '<' := by
  apply cssJoinLines_no_lt; intro s hs; simp only [List.mem_append, List.mem_map] at hs
  rcases hs with (hlight | hdark) | ⟨item, _, rfl⟩
  · split at hlight; · nomatch hlight
    · cases List.mem_singleton.1 hlight; exact app3 (lit_no_lt ":root { ") (Item.renderList_no_lt th.lightDecls) (lit_no_lt " }")
  · split at hdark; · nomatch hdark
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hdark
      rcases hdark with rfl | rfl <;> exact app3 (lit_no_lt _) (Item.renderList_no_lt th.darkDecls) (lit_no_lt _)
  · exact renderThemeRule_no_lt item

theorem Theme.render_no_closeSeq (th : Theme) : containsCloseSeq (Theme.render th).toList = false := containsCloseSeq_of_no_lt (Theme.render_no_lt th)
theorem Keyframes.renderSteps_no_lt (steps : List (String × List Item)) : ∀ c ∈ (Keyframes.renderSteps steps).toList, c ≠ '<' := Item.renderList_no_lt _
theorem Keyframes.rule_no_lt (kf : Keyframes) : ∀ c ∈ kf.rule.toList, c ≠ '<' := app5 (lit_no_lt "@keyframes ") (sanitizeCssIdent_no_lt kf.name) (lit_no_lt " { ") (Keyframes.renderSteps_no_lt kf.steps) (lit_no_lt " }")
theorem Keyframes.rule_no_closeSeq (kf : Keyframes) : containsCloseSeq kf.rule.toList = false := containsCloseSeq_of_no_lt (Keyframes.rule_no_lt kf)
theorem Style.rule_no_lt (s : Style) : ∀ c ∈ (Style.rule s).toList, c ≠ '<' := by
  unfold Style.rule; split; exact sanitizeNoLt_no_lt s.raw; exact app5 (lit_no_lt ".") (sanitizeNoLt_no_lt s.className) (lit_no_lt " { ") (sanitizeNoLt_no_lt s.raw) (lit_no_lt " }")
theorem renderStyleSheet_no_lt (styles : List Style) : ∀ c ∈ (renderStyleSheet styles).toList, c ≠ '<' := by
  apply cssJoinLines_no_lt; intro r hr; simp only [List.mem_append, List.mem_map] at hr
  rcases hr with (⟨s, _, rfl⟩ | ⟨e, _, rfl⟩) | ⟨s, _, rfl⟩ <;> first | exact Style.rule_no_lt _ | exact sanitizeNoLt_no_lt _
theorem renderStyleSheet_no_closeSeq (styles : List Style) : containsCloseSeq (renderStyleSheet styles).toList = false := containsCloseSeq_of_no_lt (renderStyleSheet_no_lt styles)

theorem inlineStyleItem_safe : ∀ (i : Item), ∀ c ∈ (inlineStyleItem i).toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\''
  | .decl p v => app4 (sanitizeInlineCssAtom_no_lt_or_quote p) (lit_safe_inline ": ") (sanitizeInlineCssAtom_no_lt_or_quote v) (lit_safe_inline ";")
  | .nest _ _ => lit_safe_inline ""
theorem inlineStyleStr_safe : ∀ (items : List Item), ∀ c ∈ (inlineStyleStr items).toList, c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '"' ∧ c ≠ '\''
  | [] => lit_safe_inline "" | [i] => inlineStyleItem_safe i
  | i :: j :: rest => by simp only [inlineStyleStr]; split; exact inlineStyleStr_safe (j :: rest); split; exact inlineStyleItem_safe i; exact app3 (inlineStyleItem_safe i) (lit_safe_inline " ") (inlineStyleStr_safe (j :: rest))
theorem inlineStyleStr_no_lt (items : List Item) : ∀ c ∈ (inlineStyleStr items).toList, c ≠ '<' := fun c hc => (inlineStyleStr_safe items c hc).1
theorem inlineStyleStr_no_quote (items : List Item) : ∀ c ∈ (inlineStyleStr items).toList, c ≠ '"' ∧ c ≠ '\'' := fun c hc => ⟨(inlineStyleStr_safe items c hc).2.2.1, (inlineStyleStr_safe items c hc).2.2.2⟩
theorem inlineStyleStr_no_closeSeq (items : List Item) : containsCloseSeq (inlineStyleStr items).toList = false := containsCloseSeq_of_no_lt (inlineStyleStr_no_lt items)

@[simp] theorem Attr.valid_inlineStyle {msg : Type} (items : List Item) : (inlineStyle items : Attr msg).valid = true := rfl
@[simp] theorem Attr.valid_styleVars {msg : Type} (vars : List Item) : (styleVars vars : Attr msg).valid = true := rfl
@[simp] theorem Attr.isLocalCell_inlineStyle {msg : Type} (items : List Item) : (inlineStyle items : Attr msg).isLocalCell = false := rfl
@[simp] theorem Attr.isLocalCell_styleVars {msg : Type} (vars : List Item) : (styleVars vars : Attr msg).isLocalCell = false := rfl
@[simp] theorem Theme.coversAll_nil (th : Theme) : th.coversAll [] = true := rfl
@[simp] theorem Theme.coversAll_cons (th : Theme) (s : Style) (ss : List Style) : th.coversAll (s :: ss) = (th.coversStyle s && th.coversAll ss) := rfl
end Qed
