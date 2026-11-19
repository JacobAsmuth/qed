import Js.Backend

namespace Js.Proofs

open Lean IR

/-!
# Core Hygiene, Runtime Representation & Static RC Analyses for `Js.Backend`

1. **String/Nat Injectivity, Identifier Hygiene, `jsStr` Safety & Reachability Closure**
2. **Runtime Values, Closures (`rtApp`), `CowHeap` & `MemoCell`**
3. **Static Analyses (`collectNonArr`, `collectProjSrc`, `hasDecOf`, `hasJpSelfTail`)**
-/

/-! ## 1. Digit/String Injectivity, Identifier Hygiene, `jsStr` Safety & `reach` Closure -/

@[simp] theorem toString_str_eq (s : String) : toString s = s := rfl
private def digitVal (c : Char) : Nat := c.toNat - '0'.toNat
private def fromDigits (ds : List Char) : Nat := ds.foldl (fun acc c => acc * 10 + digitVal c) 0
private theorem digitVal_digitChar (d : Nat) (hd : d < 10) : digitVal (Nat.digitChar d) = d := by match d, hd with | 0,_|1,_|2,_|3,_|4,_|5,_|6,_|7,_|8,_|9,_ => rfl
private theorem digitChar_isDigit (d : Nat) (hd : d < 10) : (Nat.digitChar d).isDigit = true := by match d, hd with | 0,_|1,_|2,_|3,_|4,_|5,_|6,_|7,_|8,_|9,_ => rfl

private theorem toDigitsCore_all_digits (n fuel : Nat) (ds : List Char) (hds : ∀ c ∈ ds, c.isDigit = true) : ∀ c ∈ Nat.toDigitsCore 10 fuel n ds, c.isDigit = true := by
  induction fuel generalizing n ds with
  | zero => exact hds
  | succ _ ih => simp only [Nat.toDigitsCore]; split <;> first
    | exact fun c hc => (List.mem_cons.1 hc).elim (· ▸ digitChar_isDigit _ (Nat.mod_lt _ (by omega))) (hds c)
    | exact ih (n / 10) _ fun c hc => (List.mem_cons.1 hc).elim (· ▸ digitChar_isDigit _ (Nat.mod_lt _ (by omega))) (hds c)

private theorem foldl_fromDigits (ds : List Char) (acc : Nat) : ds.foldl (fun a c => a * 10 + digitVal c) acc = acc * 10 ^ ds.length + fromDigits ds := by
  induction ds generalizing acc with | nil => simp [fromDigits] | cons d rest ih =>
    have hhd : fromDigits (d :: rest) = digitVal d * 10 ^ rest.length + fromDigits rest := by rw [fromDigits, List.foldl_cons, Nat.zero_mul, Nat.zero_add, ih]
    rw [List.foldl_cons, ih, hhd, List.length_cons, Nat.pow_succ']; simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
private theorem fromDigits_append (xs ys : List Char) : fromDigits (xs ++ ys) = fromDigits xs * 10 ^ ys.length + fromDigits ys := by unfold fromDigits; rw [List.foldl_append, foldl_fromDigits]; rfl
private theorem toDigitsCore_append : ∀ (fuel n : Nat) (ds : List Char), Nat.toDigitsCore 10 fuel n ds = Nat.toDigitsCore 10 fuel n [] ++ ds
  | 0, _, _ => rfl | f + 1, n, ds => by simp only [Nat.toDigitsCore]; split; rfl; rw [toDigitsCore_append f (n / 10) (Nat.digitChar (n % 10) :: ds), toDigitsCore_append f (n / 10) [Nat.digitChar (n % 10)], List.append_assoc]; rfl
private theorem fromDigits_toDigitsCore : ∀ (fuel n : Nat), n < fuel → fromDigits (Nat.toDigitsCore 10 fuel n []) = n
  | 0, _, h => by omega
  | f + 1, n, h => by
      simp only [Nat.toDigitsCore]; split
      · have hlt : n < 10 := by omega
        simp only [fromDigits, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hlt, digitVal_digitChar n hlt]
      · rw [toDigitsCore_append, fromDigits_append, fromDigits_toDigitsCore f (n / 10) (by omega)]; simp only [fromDigits, List.foldl_cons, List.foldl_nil, List.length_singleton, Nat.pow_one, Nat.zero_mul, Nat.zero_add, digitVal_digitChar (n % 10) (Nat.mod_lt _ (by omega))]; omega

theorem nat_toString_digits (n : Nat) : ∀ c ∈ (toString n).toList, c.isDigit = true := by simpa [Nat.toString_eq_repr, Nat.repr, Nat.toDigits] using toDigitsCore_all_digits n (n + 1) [] (fun _ h => nomatch h)
theorem fromDigits_toString (n : Nat) : fromDigits (toString n).toList = n := by simpa [Nat.toString_eq_repr, Nat.repr, Nat.toDigits] using fromDigits_toDigitsCore (n + 1) n (Nat.lt_succ_self n)
theorem nat_toString_inj {a b : Nat} (h : toString a = toString b) : a = b := by rw [← fromDigits_toString a, ← fromDigits_toString b, h]
theorem nat_repr_inj {a b : Nat} (h : Nat.repr a = Nat.repr b) : a = b := nat_toString_inj (by simpa [Nat.toString_eq_repr] using h)
private theorem pref_nat_inj (pfx : String) {a b : Nat} (h : pfx ++ toString a = pfx ++ toString b) : a = b :=
  nat_toString_inj (String.ext (by have := congrArg String.toList h; simpa [String.toList_append] using this))

private theorem digits_sep_inj {sep : Char} (hsep : sep.isDigit = false) :
    ∀ {d₁ d₂ r₁ r₂ : List Char}, (∀ c ∈ d₁, c.isDigit = true) → (∀ c ∈ d₂, c.isDigit = true) → d₁ ++ sep :: r₁ = d₂ ++ sep :: r₂ → d₁ = d₂ ∧ r₁ = r₂
  | [], [], _, _, _, _, h => by simpa using h
  | [], _ :: _, _, _, _, hd₂, h => by simp only [List.nil_append, List.cons_append, List.cons.injEq] at h; have := hd₂ _ (.head _); rw [← h.1, hsep] at this; contradiction
  | _ :: _, [], _, _, hd₁, _, h => by simp only [List.cons_append, List.nil_append, List.cons.injEq] at h; have := hd₁ _ (.head _); rw [h.1, hsep] at this; contradiction
  | c₁ :: _, c₂ :: _, _, _, hd₁, hd₂, h => by simp only [List.cons_append, List.cons.injEq] at h; obtain ⟨rfl, h2⟩ := h; obtain ⟨hds, hr⟩ := digits_sep_inj hsep (fun c hc => hd₁ c (.tail _ hc)) (fun c hc => hd₂ c (.tail _ hc)) h2; exact ⟨congrArg (c₁ :: ·) hds, hr⟩

def genGlobalName (counter : Nat) : String := s!"_g{counter}"
def inlineJpSlot (j : JoinPointId) (i : Nat) : String := s!"_{jp j}_{i}"
theorem v_inj {x y : VarId} (h : v x = v y) : x.idx = y.idx := pref_nat_inj "x" h
theorem jp_inj {i k : JoinPointId} (h : jp i = jp k) : i.idx = k.idx := pref_nat_inj "j" h
theorem genGlobalName_inj {a b : Nat} (h : genGlobalName a = genGlobalName b) : a = b := pref_nat_inj "_g" h
theorem v_ne_jp (x : VarId) (j : JoinPointId) : v x ≠ jp j := fun h => by have := congrArg String.toList h; simp [v, jp, String.toList_append] at this
theorem list_take_ne_x_append_digits (m j i : Nat) : s!"x{m}" ≠ s!"_{jp ⟨j⟩}_{i}" := fun h => by have := congrArg String.toList h; simp [jp, String.toList_append] at this
private theorem nat_repr_digits (n : Nat) : ∀ c ∈ n.repr.toList, c.isDigit = true := by simpa [← Nat.toString_eq_repr] using nat_toString_digits n
private theorem inline_var_ne_inline_var {j₁ j₂ i₁ i₂ : Nat} (hne : j₁ ≠ j₂) : s!"_{jp ⟨j₁⟩}_{i₁}" ≠ s!"_{jp ⟨j₂⟩}_{i₂}" := fun h => by
  have h_ : "_".toList = ['_'] := rfl; have hj : "j".toList = ['j'] := rfl; have hl := congrArg String.toList h
  simp only [jp, toString_str_eq, Nat.toString_eq_repr, String.toList_append, h_, hj, List.cons_append, List.nil_append, List.cons.injEq, true_and, List.append_assoc] at hl
  exact hne (nat_repr_inj (String.ext (digits_sep_inj (sep := '_') rfl (nat_repr_digits j₁) (nat_repr_digits j₂) hl).1))
private theorem inline_var_inj_idx {j i₁ i₂ : Nat} (h : s!"_{jp ⟨j⟩}_{i₁}" = s!"_{jp ⟨j⟩}_{i₂}") : i₁ = i₂ := by
  have h_ : "_".toList = ['_'] := rfl; have hj : "j".toList = ['j'] := rfl; have hl := congrArg String.toList h
  simp only [jp, toString_str_eq, Nat.toString_eq_repr, String.toList_append, h_, hj, List.cons_append, List.nil_append, List.cons.injEq, true_and, List.append_assoc, List.append_cancel_left_eq] at hl; exact nat_repr_inj (String.ext hl)
theorem inlineJpSlot_inj {j₁ j₂ : JoinPointId} {i₁ i₂ : Nat} (h : inlineJpSlot j₁ i₁ = inlineJpSlot j₂ i₂) : j₁.idx = j₂.idx ∧ i₁ = i₂ := by
  by_cases hj : j₁.idx = j₂.idx; obtain ⟨_⟩ := j₁; obtain ⟨_⟩ := j₂; simp at hj; subst hj; exact ⟨rfl, inline_var_inj_idx h⟩; exact False.elim (inline_var_ne_inline_var hj (by simpa [inlineJpSlot] using h))
theorem genGlobalName_disjoint_all (counter : Nat) (x : VarId) (j : JoinPointId) (i : Nat) (ext : String) :
    genGlobalName counter ≠ v x ∧ genGlobalName counter ≠ jp j ∧ genGlobalName counter ≠ inlineJpSlot j i ∧
    genGlobalName counter ≠ "$." ++ ext ∧ genGlobalName counter ≠ "__step" ∧ genGlobalName counter ≠ "__r" ∧ genGlobalName counter ≠ "__externs" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> · intro h; have hl := congrArg String.toList h; simp [genGlobalName, v, jp, inlineJpSlot, String.toList_append] at hl
theorem ctxJs_fallback_startsWith_dollar (c : Ctx) (n : Name) (hmiss : c.names.get? n = none) : (c.js n).startsWith "$." = true := by
  have hget : c.names[n]? = none := hmiss; simp [Ctx.js, hget, String.startsWith]

/-- All ECMAScript reserved words, strict-mode keywords, and internal runtime names. -/
def jsReservedWords : List String :=
  ["break", "case", "catch", "class", "const", "continue", "debugger", "default", "delete", "do", "else", "enum",
   "export", "extends", "false", "finally", "for", "function", "if", "import", "in", "instanceof", "let", "new",
   "null", "return", "super", "switch", "this", "throw", "true", "try", "typeof", "var", "void", "while", "with",
   "yield", "await", "implements", "interface", "package", "private", "protected", "public", "static",
   "__step", "__r", "__externs", "Error", "Object", "Array"]
private def hasInternalIdentShape (s : String) : Bool :=
  match s.toList with | '$' :: '.' :: _ | '_' :: 'j' :: _ => true | 'x' :: ds | 'j' :: ds | '_' :: 'g' :: ds => !ds.isEmpty && ds.all Char.isDigit | _ => false
private theorem digits_nonempty_isDigit (n : Nat) : !(toString n).toList.isEmpty && (toString n).toList.all Char.isDigit = true := by
  have hne : (toString n).toList ≠ [] := by cases n with | zero => decide | succ k => intro h; have hf := fromDigits_toString (k + 1); rw [h] at hf; simp [fromDigits] at hf
  cases hcs : (toString n).toList with | nil => exact absurd hcs hne | cons _ _ =>
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, List.all_eq_true, decide_eq_true_eq]; exact fun ch hch => nat_toString_digits n ch (by rw [hcs]; exact hch)

/-- Every compiler-generated JS identifier (`v`, `jp`, `genGlobalName`, `inlineJpSlot`, `"$." ++ ext`) is disjoint from all ECMAScript reserved words. -/
theorem ident_ne_jsKeyword (x : VarId) (j : JoinPointId) (k i : Nat) (ext : String) :
    v x ∉ jsReservedWords ∧ jp j ∉ jsReservedWords ∧ genGlobalName k ∉ jsReservedWords ∧ inlineJpSlot j i ∉ jsReservedWords ∧ ("$." ++ ext) ∉ jsReservedWords := by
  have hres : ∀ w ∈ jsReservedWords, hasInternalIdentShape w = false := by decide
  have noRes {s : String} (hs : hasInternalIdentShape s = true) : s ∉ jsReservedWords := fun hm => by have := hres s hm; rw [hs] at this; contradiction
  refine ⟨noRes ?_, noRes ?_, noRes ?_, noRes ?_, noRes ?_⟩
  · simpa [hasInternalIdentShape, v, String.toList_append] using digits_nonempty_isDigit x.idx
  · simpa [hasInternalIdentShape, jp, String.toList_append] using digits_nonempty_isDigit j.idx
  · simpa [hasInternalIdentShape, genGlobalName, String.toList_append] using digits_nonempty_isDigit k
  · simp [hasInternalIdentShape, inlineJpSlot, jp, String.toList_append]
  · simp [hasInternalIdentShape]

private def mangleStep (s : String) (c : Char) : String :=
  if c.isAlphanum then s.push c else if c == '.' || c == '_' then s.push '_' else s ++ s!"x{c.toNat}"
private theorem mangleStep_preserves (s : String) (c : Char) (hs : ∀ ch ∈ s.toList, ch.isAlphanum = true ∨ ch = '_') : ∀ ch ∈ (mangleStep s c).toList, ch.isAlphanum = true ∨ ch = '_' := by
  unfold mangleStep; split
  · rename_i hal; intro ch hch; rcases (by simpa [String.toList_push] using hch : ch ∈ s.toList ∨ ch = c) with h | rfl; exact hs ch h; exact Or.inl hal
  · split
    · intro ch hch; rcases (by simpa [String.toList_push] using hch : ch ∈ s.toList ∨ ch = '_') with h | rfl; exact hs ch h; exact Or.inr rfl
    · intro ch hch; rcases List.mem_append.1 (String.toList_append ▸ hch) with h | h2; exact hs ch h
      have hx : (s!"x{c.toNat}").toList = 'x' :: (toString c.toNat).toList := by simp [String.toList_append]
      rw [hx, List.mem_cons] at h2; rcases h2 with rfl | hd; exact Or.inl (by decide)
      have := nat_toString_digits c.toNat ch hd; exact Or.inl (by cases ch using Char.casesOn <;> simp_all [Char.isAlphanum, Char.isDigit])

/-- Identifier hygiene for `Js.mangle`: every character in `mangle n` is strictly alphanumeric or `'_'`. -/
theorem mangle_chars_safe (n : Name) : ∀ ch ∈ (mangle n).toList, ch.isAlphanum = true ∨ ch = '_' := by
  have hloop : ∀ (cs : List Char) (s : String), (∀ ch ∈ s.toList, ch.isAlphanum = true ∨ ch = '_') →
      ∀ ch ∈ (Id.run (forIn cs s fun c r => if c.isAlphanum = true then pure (.yield (r.push c)) else if c = '.' ∨ c = '_' then pure (.yield (r.push '_')) else pure (.yield (r ++ (toString "x" ++ c.toNat.repr))))).toList,
        ch.isAlphanum = true ∨ ch = '_' := fun cs => by
    induction cs with | nil => exact fun s hs => by simpa using hs | cons c _ ih =>
      intro s hs; simp only [List.forIn_cons, Id.run, bind, pure]; by_cases hal : c.isAlphanum = true
      · simp only [hal, ↓reduceIte]; exact ih _ (by simpa [mangleStep, hal] using mangleStep_preserves s c hs)
      · by_cases hdu : c = '.' ∨ c = '_'
        · simp only [hal, Bool.false_eq_true, ↓reduceIte, hdu]; exact ih _ (by simpa [show mangleStep s c = s.push '_' by rcases hdu with rfl | rfl <;> simp [mangleStep, hal]] using mangleStep_preserves s c hs)
        · simp only [hal, Bool.false_eq_true, ↓reduceIte, hdu]; exact ih _ (by simpa [show mangleStep s c = s ++ (toString "x" ++ c.toNat.repr) by simp only [mangleStep, hal, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, beq_iff_eq]; split; exact absurd ‹_› hdu; rfl] using mangleStep_preserves s c hs)
  unfold mangle; simpa using hloop n.toString.toList "" (fun _ h => by simp at h)

/-- Valid JS string literal interiors: no raw control characters (`< 32`), no unescaped `'"'`, and every `'\\'` starts an escape pair. -/
inductive ValidJsStrBody : List Char → Prop where
  | nil : ValidJsStrBody []
  | plain {c : Char} {cs : List Char} : 32 ≤ c.toNat → c ≠ '"' → c ≠ '\\' → ValidJsStrBody cs → ValidJsStrBody (c :: cs)
  | esc {c : Char} {cs : List Char} : 32 ≤ c.toNat → ValidJsStrBody cs → ValidJsStrBody ('\\' :: c :: cs)
private theorem ValidJsStrBody.append {xs ys : List Char} (hx : ValidJsStrBody xs) (hy : ValidJsStrBody ys) : ValidJsStrBody (xs ++ ys) := by
  induction hx with | nil => exact hy | plain h1 h2 h3 _ ih => exact .plain h1 h2 h3 ih | esc h1 _ ih => exact .esc h1 ih
private theorem hexDigits_valid (cs : List Char) (h : ∀ c ∈ cs, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']) : ValidJsStrBody cs := by
  have hall : ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'].all (fun c => decide (32 ≤ c.toNat) && (c != '"') && (c != '\\')) = true := by decide
  rw [List.all_eq_true] at hall; induction cs with | nil => exact .nil | cons c _ ih => have hp := hall c (h c (.head _)); simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at hp; exact .plain hp.1.1 hp.1.2 hp.2 (ih fun x hx => h x (.tail _ hx))
private theorem hex_toDigitsCore_chars (n fuel : Nat) (ds : List Char) (hds : ∀ c ∈ ds, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']) :
    ∀ c ∈ Nat.toDigitsCore 16 fuel n ds, c ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'] := by
  have hd16 : ∀ d, d < 16 → Nat.digitChar d ∈ ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'] := fun d hd => by match d with | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15 => decide | _ + 16 => omega
  induction fuel generalizing n ds with | zero => exact hds | succ _ ih =>
    simp only [Nat.toDigitsCore]; split <;> first
      | exact fun c hc => (List.mem_cons.1 hc).elim (· ▸ hd16 _ (Nat.mod_lt _ (by omega))) (hds c)
      | exact ih (n / 16) _ fun c hc => (List.mem_cons.1 hc).elim (· ▸ hd16 _ (Nat.mod_lt _ (by omega))) (hds c)

/-- Every string produced by `Js.jsStr s` has the form `"\"" ++ body ++ "\""` where `body` satisfies `ValidJsStrBody`. -/
theorem jsStr_safe (s : String) : ∃ body : String, jsStr s = "\"" ++ body ++ "\"" ∧ ValidJsStrBody body.toList := by
  let step : String → Char → String := fun acc c => acc ++ (match c with
    | '\\' => "\\\\" | '"' => "\\\"" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
    | c => if c.toNat < 32 then let h := Nat.toDigits 16 c.toNat; "\\x" ++ String.ofList (if h.length == 1 then '0' :: h else h) else String.singleton c)
  have hstep : ∀ acc c, ValidJsStrBody acc.toList → ValidJsStrBody (step acc c).toList := fun acc c hacc => by
    dsimp only [step]; rw [String.toList_append]; apply ValidJsStrBody.append hacc
    by_cases h1 : c = '\\'; subst h1; exact .esc (by decide) .nil; by_cases h2 : c = '"'; subst h2; exact .esc (by decide) .nil
    by_cases h3 : c = '\n'; subst h3; exact .esc (by decide) .nil; by_cases h4 : c = '\r'; subst h4; exact .esc (by decide) .nil
    by_cases h5 : c = '\t'; subst h5; exact .esc (by decide) .nil; split <;> try contradiction
    split
    · have hd := hex_toDigitsCore_chars c.toNat (c.toNat + 1) [] (fun _ h => nomatch h)
      simpa [String.toList_append] using ValidJsStrBody.esc (c := 'x') (by decide) (by split; exact .plain (by decide) (by decide) (by decide) (hexDigits_valid _ hd); exact hexDigits_valid _ hd)
    · rw [String.toList_singleton]; exact .plain (by omega) h2 h1 .nil
  have hfold : ∀ (cs : List Char) (acc : String), ValidJsStrBody acc.toList → ValidJsStrBody (cs.foldl step acc).toList := fun cs => by
    induction cs with | nil => exact fun _ ha => ha | cons c _ ih => exact fun acc ha => ih _ (hstep acc c ha)
  exact ⟨s.foldl step "", rfl, by simpa [jsStr, String.foldl] using hfold s.toList "" .nil⟩

def assignProgramNamesStep (st : Std.HashMap Name String × Nat) (name : Name) (entryMap : Std.HashMap Name String) (isFdecl : Bool) : Std.HashMap Name String × Nat :=
  if isFdecl then match entryMap.get? name with | some s => (st.1.insert name s, st.2) | none => (st.1.insert name (genGlobalName st.2), st.2 + 1) else st
theorem assignProgramNames_invariant (steps : List (Name × Bool)) (entryMap : Std.HashMap Name String)
    (hentries : ∀ n s, entryMap.get? n = some s → ∀ i, s ≠ genGlobalName i) (nm₀ : Std.HashMap Name String) (cnt₀ : Nat)
    (hbound : ∀ k nm, nm₀.get? k = some nm → ∀ i ≥ cnt₀, nm ≠ genGlobalName i) :
    let (nm₁, cnt₁) := steps.foldl (fun st p => assignProgramNamesStep st p.1 entryMap p.2) (nm₀, cnt₀)
    cnt₀ ≤ cnt₁ ∧ (∀ k nm, nm₁.get? k = some nm → ∀ i ≥ cnt₁, nm ≠ genGlobalName i) := by
  induction steps generalizing nm₀ cnt₀ with
  | nil => exact ⟨Nat.le_refl _, hbound⟩
  | cons p _ ih =>
      simp only [List.foldl_cons, assignProgramNamesStep]; cases p.2 with | false => exact ih nm₀ cnt₀ hbound | true =>
      cases he : entryMap.get? p.1 with
      | some s => refine ih (nm₀.insert p.1 s) cnt₀ fun k nm hget i hi => ?_; rw [Std.HashMap.get?_insert] at hget; split at hget; (cases hget; exact hentries p.1 s he i); exact hbound k nm hget i hi
      | none =>
          have ih' := ih (nm₀.insert p.1 (genGlobalName cnt₀)) (cnt₀ + 1) fun k nm hget i hi => by rw [Std.HashMap.get?_insert] at hget; split at hget; (cases hget; intro hc; have := genGlobalName_inj hc; omega); exact hbound k nm hget i (by omega)
          exact ⟨Nat.le_trans (Nat.le_succ cnt₀) ih'.1, ih'.2⟩

/-! ### Reachability Closure & Server-Leak Isolation (`reach_closed`) -/

def reachEdges (env : Environment) (n : Name) : List Name :=
  match findEnvDecl env n with | some (.fdecl (body := b) ..) => (callees b #[]).toList ++ (getInitFnNameFor? env n).toList | _ => []

theorem reachAux_mono (env : Environment) :
    ∀ (fuel : Nat) (rest : List Name) (seen : Array Name) (visited : Std.HashSet Name) (out : Array Name),
      reachAux env fuel rest seen visited = .ok out → ∀ x ∈ seen.toList, x ∈ out.toList
  | _, [], _, _, _, hok, _, hx => by simp only [reachAux] at hok; cases hok; exact hx
  | 0, _ :: _, _, _, _, hok, _, _ => by simp only [reachAux] at hok; nomatch hok
  | f + 1, _ :: rest, seen, visited, out, hok, x, hx => by
      dsimp only [reachAux] at hok; split at hok
      · exact reachAux_mono env f rest seen visited out hok x hx
      · split at hok <;> exact reachAux_mono env f _ _ _ out hok x (by simp [Array.toList_push, hx])

private theorem reachAux_closed_aux (env : Environment) :
    ∀ (fuel : Nat) (rest : List Name) (seen : Array Name) (visited : Std.HashSet Name) (out : Array Name),
      (∀ x, x ∈ visited ↔ x ∈ seen.toList) → (∀ x ∈ seen.toList, ∀ y ∈ reachEdges env x, y ∈ seen.toList ∨ y ∈ rest) →
      reachAux env fuel rest seen visited = .ok out → (∀ r ∈ rest, r ∈ out.toList) ∧ (∀ x ∈ out.toList, ∀ y ∈ reachEdges env x, y ∈ out.toList)
  | _, [], _, _, _, _, hclosed, hok => by simp only [reachAux] at hok; cases hok; exact ⟨(fun _ hr => nomatch hr), fun x hx y hy => (hclosed x hx y hy).elim id (fun h => nomatch h)⟩
  | 0, _ :: _, _, _, _, _, _, hok => by simp only [reachAux] at hok; nomatch hok
  | f + 1, n :: rest, seen, visited, out, hiff, hclosed, hok => by
      dsimp only [reachAux] at hok; by_cases hcon : visited.contains n = true
      · simp only [hcon, ↓reduceIte] at hok; have hnSeen := (hiff n).1 (Std.HashSet.contains_iff_mem.1 hcon)
        obtain ⟨ihR, ihC⟩ := reachAux_closed_aux env f rest seen visited out hiff (fun x hx y hy => (hclosed x hx y hy).elim .inl fun hr => (List.mem_cons.1 hr).elim (· ▸ .inl hnSeen) .inr) hok
        exact ⟨fun r hr => (List.mem_cons.1 hr).elim (· ▸ reachAux_mono env f rest seen visited out hok _ hnSeen) (ihR r), ihC⟩
      · have hconF : visited.contains n = false := Bool.eq_false_iff.2 hcon; simp only [hconF, Bool.false_eq_true, ↓reduceIte] at hok
        have hiff' : ∀ x, x ∈ visited.insert n ↔ x ∈ (seen.push n).toList := fun x => by rw [Std.HashSet.mem_insert, beq_iff_eq, Array.toList_push, List.mem_append, List.mem_singleton, hiff x]; exact ⟨fun h => h.elim (fun he => .inr he.symm) .inl, fun h => h.elim .inr (fun he => .inl he.symm)⟩
        have hclosed' : ∀ x ∈ (seen.push n).toList, ∀ y ∈ reachEdges env x, y ∈ (seen.push n).toList ∨ y ∈ rest ++ reachEdges env n := fun x hx y hy => by
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx ⊢
          rcases hx with hxSeen | rfl; exact (hclosed x hxSeen y hy).elim (fun ys => .inl (.inl ys)) fun yr => (List.mem_cons.1 yr).elim (· ▸ .inl (.inr rfl)) (fun yr' => .inr (List.mem_append_left _ yr')); exact .inr (List.mem_append_right _ hy)
        have hEmpty : reachEdges env n = [] → reachAux env f rest (seen.push n) (visited.insert n) = .ok out →
            (∀ r ∈ n :: rest, r ∈ out.toList) ∧ (∀ x ∈ out.toList, ∀ y ∈ reachEdges env x, y ∈ out.toList) := fun hed hok' => by
          simp only [hed, List.append_nil] at hclosed'; obtain ⟨ihR, ihC⟩ := reachAux_closed_aux env f rest (seen.push n) (visited.insert n) out hiff' hclosed' hok'
          exact ⟨fun r hr => (List.mem_cons.1 hr).elim (fun e => by subst e; exact reachAux_mono env f rest (seen.push r) (visited.insert r) out hok' r (by simp [Array.toList_push])) (ihR r), ihC⟩
        cases hfd : findEnvDecl env n with
        | none => rw [hfd] at hok; exact hEmpty (by simp [reachEdges, hfd]) hok
        | some d => cases d with
          | extern _ _ _ _ => rw [hfd] at hok; exact hEmpty (by simp [reachEdges, hfd]) hok
          | fdecl _ _ _ b _ =>
              rw [hfd] at hok
              have hed : reachEdges env n = (callees b #[]).toList ++ (getInitFnNameFor? env n).toList := by simp [reachEdges, hfd]
              rw [hed] at hclosed'; obtain ⟨ihR, ihC⟩ := reachAux_closed_aux env f (rest ++ ((callees b #[]).toList ++ (getInitFnNameFor? env n).toList)) (seen.push n) (visited.insert n) out hiff' hclosed' hok
              exact ⟨fun r hr => (List.mem_cons.1 hr).elim (fun e => by subst e; exact reachAux_mono env f _ (seen.push r) (visited.insert r) out hok r (by simp [Array.toList_push])) (fun hr' => ihR r (List.mem_append_left _ hr')), ihC⟩

theorem reach_closed (env : Environment) (roots : List Name) (out : Array Name)
    (hreach : reach env roots #[] = .ok out) :
    (∀ r ∈ roots, r ∈ out.toList) ∧ (∀ x ∈ out.toList, ∀ y ∈ reachEdges env x, y ∈ out.toList) :=
  reachAux_closed_aux env 1000000 roots #[] ∅ out (fun _ => by simp) (fun _ h => by simp at h) hreach

def isClientSafeDecl (env : Environment) (n : Name) : Bool :=
  (clientLeakReason? env n).isNone

inductive ReachPath (env : Environment) : Name → List Name → Prop where
  | nil (a : Name) : ReachPath env a [] | cons {a b : Name} {rest : List Name} : b ∈ reachEdges env a → ReachPath env b rest → ReachPath env a (b :: rest)

private theorem forIn_list_unit_all {α ε : Type} (step : α → PUnit → Except ε (ForInStep PUnit)) (P : α → Prop)
    (hstep : ∀ a, step a PUnit.unit = .ok (.yield PUnit.unit) → P a) (hnoDone : ∀ a u, step a PUnit.unit ≠ .ok (.done u)) :
    ∀ ls : List α, forIn ls PUnit.unit step = .ok PUnit.unit → ∀ a ∈ ls, P a
  | [], _, _, h => nomatch h
  | x :: rest, h, a, ha => by rw [List.forIn_cons] at h; cases hs : step x PUnit.unit with
    | error _ => rw [hs] at h; simp [bind, Except.bind] at h
    | ok res => cases res with | done u => exact absurd hs (hnoDone x u) | yield _ => rw [hs] at h; dsimp only [bind, Except.bind] at h; exact (List.mem_cons.1 ha).elim (· ▸ hstep _ hs) (forIn_list_unit_all step P hstep hnoDone rest h a)

private theorem forIn_verifyNoServerLeak_implies (env : Environment) (xs : Array Name) (h : verifyNoServerLeakInClient env xs = .ok ()) : ∀ x ∈ xs.toList, isClientSafeDecl env x = true := by
  unfold verifyNoServerLeakInClient at h; rw [← Array.forIn_toList] at h
  have hret : ∀ (ls : List Name) (step : Name → PUnit → Except String (ForInStep PUnit)), (do forIn ls PUnit.unit step; pure PUnit.unit) = Except.ok PUnit.unit → forIn ls PUnit.unit step = Except.ok PUnit.unit :=
    fun ls step hd => by cases hf : forIn ls PUnit.unit step with | error _ => rw [hf] at hd; simp [bind, Except.bind] at hd | ok _ => rfl
  refine forIn_list_unit_all _ (fun x => isClientSafeDecl env x = true) (fun n hn => ?_) (fun n u hn => ?_) xs.toList (hret _ _ h)
  · dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, isClientSafeDecl] at hn ⊢
    cases hc : clientLeakReason? env n with
    | none => rfl
    | some err => simp [hc] at hn
  · dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hn
    cases hc : clientLeakReason? env n <;> simp [hc] at hn

/-- End-to-end client-leak isolation: whenever `reach` succeeds (fails closed on fuel exhaustion) and
    `verifyNoServerLeakInClient` passes, every declaration along any `ReachPath` from `roots` is client-safe. -/
theorem reach_verifyNoServerLeak_sound (env : Environment) (roots : List Name) (out : Array Name)
    (hreach : reach env roots #[] = .ok out)
    (hgate : verifyNoServerLeakInClient env out = .ok ()) : ∀ (path : List Name) (r : Name), r ∈ roots → ReachPath env r path → ∀ x ∈ r :: path, isClientSafeDecl env x = true := by
  obtain ⟨hroots, hclosed⟩ := reach_closed env roots out hreach; have hsafeOut := forIn_verifyNoServerLeak_implies env out hgate
  have gen : ∀ (p : List Name) (cur : Name), cur ∈ out.toList → ReachPath env cur p → ∀ x ∈ cur :: p, isClientSafeDecl env x = true := fun p => by
    induction p with | nil => exact fun cur hc _ x hx => (List.mem_singleton.1 hx) ▸ hsafeOut _ hc | cons nxt _ ih =>
      intro cur hc hch x hx; cases hch with | cons hadj hrest => exact (List.mem_cons.1 hx).elim (· ▸ hsafeOut _ hc) (ih nxt (hclosed cur hc nxt hadj) hrest x)
  exact fun path r hr hchain => gen path r (hroots r hr) hchain

/-! ## 2. Runtime Values, Closures (`rtApp`), `CowHeap` & `MemoCell` -/

inductive JsVal where
  | num (n : Nat) | bigInt (n : Nat) | str (s : String) | arr (id : Nat)
  | ctorObj (tag : Nat) (fields : List JsVal) (hasS : Bool) (hasU : Bool) (uFields : List (Nat × JsVal)) (sFields : List ((Nat × Nat) × JsVal))
  | pap (fn : String) (arity : Nat) (args : List JsVal) | tc (args : List JsVal)

def jsTag : JsVal → Nat | .num n | .ctorObj n _ _ _ _ _ => n | _ => 0
def assocGet [BEq κ] (k : κ) : List (κ × JsVal) → JsVal | [] => .num 0 | (k', v) :: rest => if k' == k then v else assocGet k rest
def assocSet [BEq κ] (k : κ) (v : JsVal) : List (κ × JsVal) → List (κ × JsVal) | [] => [(k, v)] | (k', v') :: rest => if k' == k then (k, v) :: rest else (k', v') :: assocSet k v rest

mutual
def evalJsExpr (env : String → JsVal) : JsExpr → JsVal
  | .var name => env name | .numLit n => .num n | .bigIntLit n => .bigInt n | .strLit s => .str s | .arrLit _ => .arr 0
  | .ctorObj cidx fs hasS hasU => .ctorObj cidx (evalJsExprList env fs) hasS hasU [] []
  | .fieldProj obj idx => match evalJsExpr env obj with | .ctorObj _ fs _ _ _ _ => fs.getD idx (.num 0) | _ => .num 0
  | .uProj obj idx => match evalJsExpr env obj with | .ctorObj _ _ _ _ u _ => assocGet idx u | _ => .num 0
  | .sProj obj n off => match evalJsExpr env obj with | .ctorObj _ _ _ _ _ s => assocGet (n, off) s | _ => .num 0
  | .pap fn ar args => .pap fn ar (evalJsExprList env args)
  | .tc args => .tc (evalJsExprList env args)
  | .call "$.tag" [e] => .num (jsTag (evalJsExpr env e))
  | _ => .num 0
def evalJsExprList (env : String → JsVal) : List JsExpr → List JsVal | [] => [] | e :: es => evalJsExpr env e :: evalJsExprList env es
end

@[simp] theorem evalJsExprList_map (env : String → JsVal) : ∀ (xs : List α) (f : α → JsExpr), evalJsExprList env (xs.map f) = xs.map (fun x => evalJsExpr env (f x))
  | [], _ => rfl | x :: xs, f => by simp [evalJsExprList, evalJsExprList_map env xs f]
theorem jsTag_lowerCtor (env : String → JsVal) (info : CtorInfo) (ys : Array Arg) : jsTag (evalJsExpr env (lowerCtor info ys)) = info.cidx := by unfold lowerCtor; split <;> simp [evalJsExpr, jsTag]
theorem eval_case_scrut_lowerCtor (env : String → JsVal) (x : VarId) (info : CtorInfo) (ys : Array Arg) (hx : env (v x) = evalJsExpr env (lowerCtor info ys)) :
    evalJsExpr env (.call "$.tag" [.var (v x)]) = .num info.cidx := by simp [evalJsExpr, hx, jsTag_lowerCtor]
theorem fieldProj_lowerCtor (c : Ctx) (ty : IRType) (env : String → JsVal) (x : VarId) (info : CtorInfo) (ys : Array Arg) (idx : Nat)
    (hboxed : ¬(info.size == 0 && info.usize == 0 && info.ssize == 0) = true) (hidx : idx < ys.toList.length) (hx : env (v x) = evalJsExpr env (lowerCtor info ys)) :
    evalJsExpr env (lowerExpr c ty (.proj idx x)) = evalJsExpr env (lowerArg (ys.toList.getD idx .erased)) := by
  simp only [lowerExpr, evalJsExpr, hx, lowerCtor, Bool.eq_false_iff.2 hboxed, Bool.false_eq_true, ↓reduceIte, evalJsExprList_map]
  generalize ys.toList = args at hidx ⊢; induction args generalizing idx with | nil => simp at hidx | cons _ _ ih => cases idx with | zero => rfl | succ k => exact ih k (by simp at hidx; exact hidx)

/-- Semantic domain of `qed_rt.mjs` values supporting curried higher-order closures (`pap`/`app`). -/
inductive RtFnVal (α : Type) where | ground (v : α) | pap (fn : List α → RtFnVal α) (arity : Nat) (acc : List α)
def rtPap (fn : List α → RtFnVal α) (arity : Nat) (args : List α) : RtFnVal α := .pap fn arity args
def rtApp : Nat → RtFnVal α → List α → Option (RtFnVal α)
  | 0, _, _ => none | _, .ground v, _ => some (.ground v)
  | fuel + 1, .pap fn arity acc, xs => let rem := arity - acc.length
      if xs.length < rem then some (.pap fn arity (acc ++ xs)) else if xs.length == rem then some (fn (acc ++ xs)) else rtApp fuel (fn (acc ++ xs.take rem)) (xs.drop rem)

theorem rtApp_under_compose {α : Type} (fn : List α → RtFnVal α) (arity : Nat) (acc xs₁ xs₂ : List α) (fuel : Nat) (hunder : acc.length + xs₁.length < arity) :
    (rtApp (fuel + 1) (.pap fn arity acc) xs₁).bind (fun f' => rtApp (fuel + 1) f' xs₂) = rtApp (fuel + 1) (.pap fn arity acc) (xs₁ ++ xs₂) := by
  dsimp only [rtApp]; rw [if_pos (by omega)]; dsimp only [Option.bind, rtApp]
  by_cases hlt2 : xs₂.length < arity - (acc ++ xs₁).length
  · rw [if_pos hlt2, if_pos (by simp at hlt2 ⊢; omega), List.append_assoc]
  · have hrhs : ¬(xs₁ ++ xs₂).length < arity - acc.length := by simp at hlt2 ⊢; omega
    rw [if_neg hlt2, if_neg hrhs]; by_cases heq2 : (xs₂.length == arity - (acc ++ xs₁).length) = true
    · have := eq_of_beq heq2; rw [if_pos heq2, if_pos (beq_iff_eq.2 (by simp at this ⊢; omega)), List.append_assoc]
    · have hne2 : xs₂.length ≠ arity - (acc ++ xs₁).length := fun h => heq2 (beq_iff_eq.2 h)
      have hrhsNe : ¬((xs₁ ++ xs₂).length == arity - acc.length) = true := fun h => by have heqS := eq_of_beq h; simp only [List.length_append] at hunder hlt2 hne2 heqS; omega
      rw [if_neg heq2, if_neg hrhsNe, show arity - (acc ++ xs₁).length = arity - acc.length - xs₁.length by simp only [List.length_append]; omega,
        show (xs₁ ++ xs₂).take (arity - acc.length) = xs₁ ++ xs₂.take (arity - acc.length - xs₁.length) by rw [List.take_append, List.take_of_length_le (by omega)],
        show (xs₁ ++ xs₂).drop (arity - acc.length) = xs₂.drop (arity - acc.length - xs₁.length) by rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append], List.append_assoc]

theorem rtApp_exact_equiv {α : Type} (fn : List α → RtFnVal α) (arity : Nat) (acc xs : List α) (fuel : Nat) (hacc : acc.length ≤ arity) (hsat : acc.length + xs.length = arity) :
    rtApp (fuel + 1) (rtPap fn arity acc) xs = some (fn (acc ++ xs)) := by simp [rtPap, rtApp, show ¬xs.length < arity - acc.length by omega, show (xs.length == arity - acc.length) = true from beq_iff_eq.2 (by omega)]
theorem rtApp_over_equiv {α : Type} (fn : List α → RtFnVal α) (arity : Nat) (acc xs₁ xs₂ : List α) (fuel : Nat) (hacc : acc.length ≤ arity) (hsat : acc.length + xs₁.length = arity) (hmore : 0 < xs₂.length) :
    rtApp (fuel + 2) (rtPap fn arity acc) (xs₁ ++ xs₂) = rtApp (fuel + 1) (fn (acc ++ xs₁)) xs₂ := by
  dsimp only [rtPap, rtApp]; rw [if_neg (by simp; omega), if_neg (fun h => by have := eq_of_beq h; simp at this; omega), show arity - acc.length = xs₁.length by omega, List.take_left, List.drop_left]

def recEval {α β : Type} (step : α → Sum α β) : Nat → α → Option β | 0, _ => none | fuel + 1, a => match step a with | .inl n => recEval step fuel n | .inr r => some r
def directLoopEval {α β : Type} (step : α → Sum α β) : Nat → α → Option β | 0, _ => none | fuel + 1, a => match step a with | .inl n => directLoopEval step fuel n | .inr r => some r
theorem directLoop_equiv {α β : Type} (step : α → Sum α β) (fuel : Nat) (init : α) : directLoopEval step fuel init = recEval step fuel init := by
  induction fuel generalizing init with | zero => rfl | succ f ih => simp only [directLoopEval, recEval]; cases step init with | inl n => exact ih n | inr _ => rfl
def encodeTrampolineStep (step : List JsVal → Sum (List JsVal) JsVal) (args : List JsVal) : JsVal := match step args with | .inl n => .tc n | .inr r => r
def trampolineLoop (stepFn : List JsVal → JsVal) : Nat → List JsVal → Option JsVal
  | 0, _ => none | fuel + 1, args => match stepFn args with | .tc n => trampolineLoop stepFn fuel n | r => some r
theorem trampoline_equiv (step : List JsVal → Sum (List JsVal) JsVal) (hnoSentinel : ∀ args v, step args = .inr v → ∀ xs, v ≠ .tc xs) :
    ∀ (fuel : Nat) (args : List JsVal), trampolineLoop (encodeTrampolineStep step) fuel args = recEval step fuel args
  | 0, _ => rfl | fuel + 1, args => by simp only [trampolineLoop, encodeTrampolineStep, recEval]; cases hs : step args with | inl n => exact trampoline_equiv step hnoSentinel fuel n | inr v => cases v with | tc xs => exact False.elim (hnoSentinel args (.tc xs) hs xs rfl) | _ => rfl

/-! ### COW `.r` Refcounted Arrays, `$.refMark` Invalidation & `$.memo` Purity -/
structure CowEntry (α : Type) where
  elems : List α := []
  refcount : Nat := 1
  mark : Option Nat := none
structure CowHeap (α : Type) where
  nextId : Nat := 1
  nextStamp : Nat := 1
  cells : Nat → CowEntry α := fun _ => {}
inductive RcVal where | arr (id : Nat) | nonArr (val : JsVal)
def JsVal.toRcVal : JsVal → RcVal | .arr id => .arr id | v => .nonArr v

namespace CowHeap
def get (h : CowHeap α) (id : Nat) : CowEntry α := h.cells id
def set (h : CowHeap α) (id : Nat) (e : CowEntry α) : CowHeap α := { h with cells := fun m => if m == id then e else h.cells m }
@[simp] theorem get_set_self (h : CowHeap α) (id : Nat) (e : CowEntry α) : (h.set id e).get id = e := by simp [get, set]
@[simp] theorem get_set_ne (h : CowHeap α) {id other : Nat} (e : CowEntry α) (hne : other ≠ id) : (h.set id e).get other = h.get other := by simp [get, set, hne]
def readArray (h : CowHeap α) (id : Nat) : List α := (h.get id).elems
def cowUpdate (h : CowHeap α) (id : Nat) (f : List α → List α) : Nat × CowHeap α :=
  let e := h.get id; let updated := f e.elems
  if e.refcount ≤ 1 then (id, h.set id { elems := updated, refcount := 1, mark := none })
  else let hDec := h.set id { e with refcount := e.refcount - 1 }
    (h.nextId, { nextId := h.nextId + 1, nextStamp := h.nextStamp, cells := fun m => if m == h.nextId then { elems := updated, refcount := 1, mark := none } else hDec.cells m })
def cowUset (h : CowHeap α) (id idx : Nat) (val : α) : Nat × CowHeap α := h.cowUpdate id (·.set idx val)
def cowPush (h : CowHeap α) (id : Nat) (val : α) : Nat × CowHeap α := h.cowUpdate id (· ++ [val])

theorem cowUpdate_obs_equiv (h : CowHeap α) (id : Nat) (f : List α → List α) (hid : id < h.nextId) :
    let (outId, h') := h.cowUpdate id f
    h'.readArray outId = f (h.readArray id) ∧ (∀ alias : Nat, alias < h.nextId → ((h.get id).refcount ≤ 1 → alias ≠ id) → h'.readArray alias = h.readArray alias) := by
  dsimp only [cowUpdate]; by_cases huniq : (h.get id).refcount ≤ 1
  · simp only [huniq, ↓reduceIte]; exact ⟨by simp [readArray], fun alias _ hne => by simp [readArray, hne trivial]⟩
  · simp only [huniq, ↓reduceIte]; refine ⟨by simp [readArray, get], fun alias halias _ => ?_⟩
    by_cases ha : alias = id; subst ha; simp [readArray, get, set, beq_false_of_ne (Nat.ne_of_lt hid)]; simp [readArray, get, set, beq_false_of_ne (by omega : alias ≠ h.nextId), ha]
theorem cowUset_obs_equiv (h : CowHeap α) (id idx : Nat) (val : α) (hid : id < h.nextId) :
    let (outId, h') := h.cowUset id idx val; h'.readArray outId = (h.readArray id).set idx val ∧ (∀ alias : Nat, alias < h.nextId → ((h.get id).refcount ≤ 1 → alias ≠ id) → h'.readArray alias = h.readArray alias) := cowUpdate_obs_equiv h id (·.set idx val) hid
theorem cowPush_obs_equiv (h : CowHeap α) (id : Nat) (val : α) (hid : id < h.nextId) :
    let (outId, h') := h.cowPush id val; h'.readArray outId = h.readArray id ++ [val] ∧ (∀ alias : Nat, alias < h.nextId → ((h.get id).refcount ≤ 1 → alias ≠ id) → h'.readArray alias = h.readArray alias) := cowUpdate_obs_equiv h id (· ++ [val]) hid

def refMark (h : CowHeap α) (id : Nat) : Nat × CowHeap α :=
  let e := h.get id; match e.mark with | some s => (s, h) | none => (h.nextStamp, { (h.set id { e with mark := some h.nextStamp }) with nextStamp := h.nextStamp + 1 })
def HeapStampInv (h : CowHeap α) : Prop := (∀ m s, (h.get m).mark = some s → s < h.nextStamp) ∧ (∀ m₁ m₂ s, (h.get m₁).mark = some s → (h.get m₂).mark = some s → m₁ = m₂)
def SnapshotValid (snapStamp : Nat) (snapElems : List α) (h : CowHeap α) : Prop := snapStamp < h.nextStamp ∧ ∀ m : Nat, (h.get m).mark = some snapStamp → (h.get m).elems = snapElems

theorem refMark_creates_snapshot (h : CowHeap α) (id : Nat) (hinv : HeapStampInv h) : let (stamp, h') := h.refMark id; HeapStampInv h' ∧ SnapshotValid stamp (h.readArray id) h' := by
  rcases hinv with ⟨hbnd, huniq⟩; dsimp only [refMark]; cases hm : (h.get id).mark with
  | some s => exact ⟨⟨hbnd, huniq⟩, ⟨hbnd id s hm, fun m hm' => by rw [huniq m id s hm' hm]; rfl⟩⟩
  | none =>
      refine ⟨⟨fun m s hm' => ?_, fun m₁ m₂ s hm₁ hm₂ => ?_⟩, ⟨Nat.lt_succ_self _, fun m hm' => ?_⟩⟩
      · dsimp only at hm' ⊢; by_cases hmid : m = id; subst hmid; simp only [get, set, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hm'; subst hm'; exact Nat.lt_succ_self _
        simp only [get, set, beq_false_of_ne hmid, Bool.false_eq_true, ↓reduceIte] at hm'; exact Nat.lt_trans (hbnd m s hm') (Nat.lt_succ_self _)
      · dsimp only at hm₁ hm₂; by_cases h1 : m₁ = id <;> by_cases h2 : m₂ = id
        · exact h1.trans h2.symm
        · subst h1; simp only [get, set, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hm₁; simp only [get, set, beq_false_of_ne h2, Bool.false_eq_true, ↓reduceIte] at hm₂; subst hm₁; exact absurd (hbnd m₂ _ hm₂) (by omega)
        · subst h2; simp only [get, set, beq_false_of_ne h1, Bool.false_eq_true, ↓reduceIte] at hm₁; simp only [get, set, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hm₂; subst hm₂; exact absurd (hbnd m₁ _ hm₁) (by omega)
        · simp only [get, set, beq_false_of_ne h1, beq_false_of_ne h2, Bool.false_eq_true, ↓reduceIte] at hm₁ hm₂; exact huniq m₁ m₂ s hm₁ hm₂
      · dsimp only at hm'; by_cases hmid : m = id; subst hmid; simp [get, set, readArray]; simp only [get, set, beq_false_of_ne hmid, Bool.false_eq_true, ↓reduceIte] at hm'; exact absurd (hbnd m _ hm') (by omega)

theorem SnapshotValid_cowUpdate (h : CowHeap α) (id : Nat) (f : List α → List α) (snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) :
    SnapshotValid snapStamp snapElems (h.cowUpdate id f).2 := by
  rcases hsnap with ⟨hlt, heq⟩; dsimp only [cowUpdate]; by_cases huniq : (h.get id).refcount ≤ 1
  · simp only [huniq, ↓reduceIte]; exact ⟨hlt, fun m hm => by by_cases hmid : m = id; subst hmid; simp at hm; rw [get_set_ne _ _ hmid] at hm ⊢; exact heq m hm⟩
  · simp only [huniq, ↓reduceIte]; exact ⟨hlt, fun m hm => by by_cases hmf : m = h.nextId; subst hmf; simp [get] at hm; by_cases hmid : m = id <;> simp_all [get, set] <;> exact heq m hm⟩
theorem SnapshotValid_cowUset (h : CowHeap α) (id idx : Nat) (val : α) (snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) :
    SnapshotValid snapStamp snapElems (h.cowUset id idx val).2 := SnapshotValid_cowUpdate h id (·.set idx val) snapStamp snapElems hsnap
theorem SnapshotValid_cowPush (h : CowHeap α) (id : Nat) (val : α) (snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) :
    SnapshotValid snapStamp snapElems (h.cowPush id val).2 := SnapshotValid_cowUpdate h id (· ++ [val]) snapStamp snapElems hsnap
theorem SnapshotValid_refMark (h : CowHeap α) (id : Nat) (snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) :
    SnapshotValid snapStamp snapElems (h.refMark id).2 := by
  rcases hsnap with ⟨hlt, heq⟩; dsimp only [refMark]; cases hm : (h.get id).mark with | some _ => exact ⟨hlt, heq⟩ | none =>
    refine ⟨Nat.lt_trans hlt (Nat.lt_succ_self _), fun m hm' => ?_⟩; by_cases hmid : m = id; subst hmid; simp only [get, set, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hm'; omega; simp only [get, set, beq_false_of_ne hmid, Bool.false_eq_true, ↓reduceIte] at hm' ⊢; exact heq m hm'
theorem refMark_snapshot_sound (h : CowHeap α) (id snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) (heqStamp : (h.refMark id).1 = snapStamp) :
    h.readArray id = snapElems := by
  rcases hsnap with ⟨_, heq⟩; dsimp only [refMark] at heqStamp; cases hm : (h.get id).mark with
  | some _ => rw [hm] at heqStamp; dsimp only at heqStamp; subst heqStamp; exact heq id hm | none => rw [hm] at heqStamp; dsimp only at heqStamp; omega

def rcInc (h : CowHeap α) (v : RcVal) (n : Nat) : CowHeap α := match v with | .arr id => h.set id { h.get id with refcount := (h.get id).refcount + n } | .nonArr _ => h
def rcDec (h : CowHeap α) (v : RcVal) (n : Nat) : CowHeap α := match v with | .arr id => h.set id { h.get id with refcount := (h.get id).refcount - n } | .nonArr _ => h
@[simp] theorem rcInc_nonArr_noop (h : CowHeap α) (v : JsVal) (n : Nat) : h.rcInc (.nonArr v) n = h := rfl
@[simp] theorem rcDec_nonArr_noop (h : CowHeap α) (v : JsVal) (n : Nat) : h.rcDec (.nonArr v) n = h := rfl
@[simp] theorem rcInc_zero (h : CowHeap α) (v : RcVal) : h.rcInc v 0 = h := by cases v with | nonArr _ => rfl | arr id => cases h; simp only [rcInc, set, get, CowHeap.mk.injEq, true_and]; funext m; by_cases hm : m == id <;> simp_all
end CowHeap

structure MemoCell (α : Type) where
  ok : Bool := false
  val : Option α := none
def MemoCell.Valid (thunk : Unit → α) (c : MemoCell α) : Prop := c.ok = true → c.val = some (thunk ())
def memoForce (thunk : Unit → α) (defaultVal : α) (c : MemoCell α) : α × MemoCell α := if c.ok then (c.val.getD defaultVal, c) else let v := thunk (); (v, { ok := true, val := some v })
theorem memo_thunk_obs_equiv {α : Type} (thunk : Unit → α) (defaultVal : α) (c : MemoCell α) (hvalid : MemoCell.Valid thunk c) :
    let (res, c') := memoForce thunk defaultVal c; res = thunk () ∧ MemoCell.Valid thunk c' := by dsimp only [memoForce]; cases hok : c.ok with | false => simp [MemoCell.Valid] | true => have hv := hvalid hok; simp [hok, hv, MemoCell.Valid]

/-! ## 3. Static RC & Tail-Call Analyses (`collectNonArr`, `collectProjSrc`, `hasDecOf`, `hasJpSelfTail`) -/

def altBody : Alt → FnBody | .ctor _ b | .default b => b
theorem sizeOf_alts_toList_lt (tid : Name) (x : VarId) (ty : IRType) (alts : Array Alt) : sizeOf alts.toList < sizeOf (FnBody.case tid x ty alts) := by cases alts; simp; omega
def fnBodyStep (P : FnBody → Prop) : FnBody → Prop
  | .vdecl _ _ _ cont | .set _ _ _ cont | .setTag _ _ cont | .uset _ _ _ cont | .sset _ _ _ _ _ cont | .inc _ _ _ _ cont | .dec _ _ _ _ cont | .del _ cont => P cont
  | .jdecl _ _ val cont => P val ∧ P cont | .case _ _ _ alts => ∀ arm ∈ alts.toList, P (altBody arm) | .ret _ | .jmp _ _ | .unreachable => True
theorem fnBody_ind (P : FnBody → Prop) (h : ∀ b, fnBodyStep P b → P b) : ∀ b, P b := by
  have haux : ∀ (sz : Nat) (b : FnBody), sizeOf b ≤ sz → P b := fun sz => by
    induction sz using Nat.strongRecOn with | ind sz ih => intro b hsz; apply h; cases b with
      | vdecl _ _ _ cont | set _ _ _ cont | setTag _ _ cont | uset _ _ _ cont | sset _ _ _ _ _ cont | inc _ _ _ _ cont | dec _ _ _ _ cont | del _ cont => exact ih (sizeOf cont) (by simp at hsz; omega) cont (Nat.le_refl _)
      | jdecl _ _ val cont => exact ⟨ih (sizeOf val) (by simp at hsz; omega) val (Nat.le_refl _), ih (sizeOf cont) (by simp at hsz; omega) cont (Nat.le_refl _)⟩
      | case tid x ty alts =>
          intro arm harm; have halt : sizeOf (altBody arm) < sizeOf alts.toList := by clear hsz ih; generalize alts.toList = ls at harm ⊢; induction ls with | nil => nomatch harm | cons _ _ ihr => rcases List.mem_cons.1 harm with rfl | hm; cases arm <;> simp [altBody] <;> omega; have := ihr hm; simp; omega
          have := sizeOf_alts_toList_lt tid x ty alts; exact ih (sizeOf (altBody arm)) (by omega) (altBody arm) (Nat.le_refl _)
      | ret _ | jmp _ _ | unreachable => trivial
  exact fun b => haux (sizeOf b) b (Nat.le_refl _)

theorem collectNonArr_insert_mono {α : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (s : Std.HashSet α) (x y : α) (h : x ∈ s) : x ∈ s.insert y := Std.HashSet.mem_insert.mpr (.inr h)
private theorem collectAlts_fold_mem {β : Type} (step : β → FnBody → β) (altsFn : β → List Alt → β) (hal : ∀ b0 ls, altsFn b0 ls = ls.foldl (fun a arm => step a (altBody arm)) b0) (I : β → Prop) :
    ∀ ls a, (∀ arm ∈ ls, ∀ b, I b → I (step b (altBody arm))) → I a → I (altsFn a ls) := fun ls a hstep ha => by rw [hal]; induction ls generalizing a with | nil => exact ha | cons arm _ ih => exact ih _ (fun x hx => hstep x (.tail _ hx)) (hstep arm (.head _) a ha)
private theorem collectNonArrAlts_eq_foldl (acc : Std.HashSet Nat) (ls : List Alt) : collectNonArrAlts acc ls = ls.foldl (fun a arm => collectNonArr a (altBody arm)) acc := by
  induction ls generalizing acc with | nil => rfl | cons arm _ ih => cases arm <;> simp [collectNonArrAlts, altBody, ih]
private theorem collectProjSrcAlts_eq_foldl (calls : Std.HashSet Nat) (acc : Std.HashMap Nat Nat) (ls : List Alt) : collectProjSrcAlts calls acc ls = ls.foldl (fun a arm => collectProjSrc calls a (altBody arm)) acc := by
  induction ls generalizing acc with | nil => rfl | cons arm _ ih => cases arm <;> simp [collectProjSrcAlts, altBody, ih]

theorem collectNonArr_mono (b : FnBody) (acc : Std.HashSet Nat) (k : Nat) (hk : k ∈ acc) : k ∈ collectNonArr acc b := by
  revert acc; refine fnBody_ind (fun b => ∀ acc, k ∈ acc → k ∈ collectNonArr acc b) (fun b hb acc hk => ?_) b; cases b with
  | vdecl _ _ e _ => apply hb; cases e <;> first | exact hk | exact collectNonArr_insert_mono acc k _ hk
  | jdecl _ _ _ _ => exact hb.2 _ (hb.1 acc hk)
  | case _ x _ alts => exact collectAlts_fold_mem collectNonArr collectNonArrAlts collectNonArrAlts_eq_foldl (k ∈ ·) alts.toList (acc.insert x.idx) hb (collectNonArr_insert_mono acc k x.idx hk)
  | set _ _ _ _ | setTag _ _ _ | uset _ _ _ _ | sset _ _ _ _ _ _ | inc _ _ _ _ _ | dec _ _ _ _ _ | del _ _ => exact hb acc hk
  | ret _ | jmp _ _ | unreachable => exact hk
theorem collectNonArrAlts_mono (alts : List Alt) (acc : Std.HashSet Nat) (k : Nat) (hk : k ∈ acc) : k ∈ collectNonArrAlts acc alts :=
  collectAlts_fold_mem collectNonArr collectNonArrAlts collectNonArrAlts_eq_foldl (k ∈ ·) alts acc (fun arm _ b hb => collectNonArr_mono (altBody arm) b k hb) hk

def NonArrExpr : IR.Expr → Bool | .ctor .. | .reuse .. | .pap .. | .lit .. | .box .. | .unbox .. | .isShared .. => true | _ => false
def ProjSrcVar : IR.Expr → Option Nat | .proj _ p | .uproj _ p | .sproj _ _ p => some p.idx | _ => none
def NonArrSetSound (acc : Std.HashSet Nat) (ρ : Nat → RcVal) : Prop := ∀ k, k ∈ acc → ∃ v, ρ k = .nonArr v
theorem NonArrSetSound_insert {acc : Std.HashSet Nat} {ρ : Nat → RcVal} {k : Nat} {v : JsVal} (hs : NonArrSetSound acc ρ) (hk : ρ k = .nonArr v) : NonArrSetSound (acc.insert k) ρ :=
  fun m hm => (Std.HashSet.mem_insert.1 hm).elim (fun hkm => ⟨v, by have : k = m := beq_iff_eq.mp hkm; subst this; exact hk⟩) (hs m)

mutual
def NonArrConsistent (ρ : Nat → RcVal) : FnBody → Prop
  | .vdecl x _ e b => (NonArrExpr e = true → ∃ v, ρ x.idx = .nonArr v) ∧ (∀ p, ProjSrcVar e = some p → ∃ v, ρ p = .nonArr v) ∧ NonArrConsistent ρ b
  | .jdecl _ _ v b => NonArrConsistent ρ v ∧ NonArrConsistent ρ b | .case _ x _ alts => (∃ v, ρ x.idx = .nonArr v) ∧ NonArrConsistentAlts ρ alts.toList
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => NonArrConsistent ρ b
  | .ret _ | .jmp _ _ | .unreachable => True
def NonArrConsistentAlts (ρ : Nat → RcVal) : List Alt → Prop | [] => True | .ctor _ b :: rest | .default b :: rest => NonArrConsistent ρ b ∧ NonArrConsistentAlts ρ rest
end
private theorem nonArrConsistentAlts_mem {ρ : Nat → RcVal} : ∀ {ls : List Alt}, NonArrConsistentAlts ρ ls → ∀ arm ∈ ls, NonArrConsistent ρ (altBody arm)
  | [], _, _, h => nomatch h | arm :: _, hc, a, ha => have ⟨h1, h2⟩ : NonArrConsistent ρ (altBody arm) ∧ NonArrConsistentAlts ρ _ := by cases arm <;> exact hc
      (List.mem_cons.1 ha).elim (fun e => e ▸ h1) (nonArrConsistentAlts_mem h2 a)

theorem collectNonArr_sound (body : FnBody) (ρ : Nat → RcVal) (hcon : NonArrConsistent ρ body) :
    ∀ x : VarId, (collectNonArr {} body).contains x.idx = true → ∀ (h : CowHeap α) (n : Nat), h.rcInc (ρ x.idx) n = h ∧ h.rcDec (ρ x.idx) n = h := by
  have hgen : ∀ acc, NonArrSetSound acc ρ → NonArrConsistent ρ body → NonArrSetSound (collectNonArr acc body) ρ := by
    refine fnBody_ind (fun b => ∀ acc, NonArrSetSound acc ρ → NonArrConsistent ρ b → NonArrSetSound (collectNonArr acc b) ρ) (fun b hb acc ha hc => ?_) body; cases b with
    | vdecl x _ e _ => rcases hc with ⟨hx, hp, hcont⟩; apply hb _ _ hcont; cases e with
      | ctor _ _ | reuse _ _ _ _ | pap _ _ | lit _ | box _ _ | unbox _ | isShared _ => exact NonArrSetSound_insert ha (hx rfl).choose_spec
      | proj _ p | uproj _ p | sproj _ _ p => exact NonArrSetSound_insert ha (hp p.idx rfl).choose_spec
      | _ => exact ha
    | jdecl _ _ _ _ => exact hb.2 _ (hb.1 acc ha hc.1) hc.2
    | case _ x _ alts => exact collectAlts_fold_mem collectNonArr collectNonArrAlts collectNonArrAlts_eq_foldl (NonArrSetSound · ρ) alts.toList (acc.insert x.idx) (fun arm harm a ha' => hb arm harm a ha' (nonArrConsistentAlts_mem hc.2 arm harm)) (NonArrSetSound_insert ha hc.1.choose_spec)
    | set _ _ _ _ | setTag _ _ _ | uset _ _ _ _ | sset _ _ _ _ _ _ | inc _ _ _ _ _ | dec _ _ _ _ _ | del _ _ => exact hb acc ha (by simpa [NonArrConsistent] using hc)
    | ret _ | jmp _ _ | unreachable => exact ha
  intro x hx h n; rcases hgen {} (fun _ hk => False.elim (Std.HashSet.not_mem_empty hk)) hcon x.idx (by simpa using hx) with ⟨v, hv⟩; simp [hv]

theorem collectProjSrc_subset_collectNonArr (body : FnBody) (x p : Nat) (hsrc : (collectProjSrc {} {} body).get? x = some p) : (collectNonArr {} body).contains p = true := by
  have hgen : ∀ calls acc na, (∀ k q, acc.get? k = some q → q ∈ na) → ∀ k q, (collectProjSrc calls acc body).get? k = some q → q ∈ collectNonArr na body := by
    refine fnBody_ind (fun b => ∀ calls acc na, (∀ k q, acc.get? k = some q → q ∈ na) → ∀ k q, (collectProjSrc calls acc b).get? k = some q → q ∈ collectNonArr na b) (fun b hb calls acc na hinv k q hres => ?_) body; cases b with
    | vdecl xv _ e _ => cases e with
      | fap _ _ | ap _ _ | reset _ _ => exact hb _ acc na hinv k q hres
      | proj _ src =>
          apply hb calls _ (na.insert src.idx) _ k q hres; intro k' q' hkq; split at hkq
          · rw [Std.HashMap.get?_insert] at hkq; split at hkq; (cases hkq; exact Std.HashSet.mem_insert.mpr (.inl (beq_self_eq_true _))); exact collectNonArr_insert_mono na q' src.idx (hinv k' q' hkq)
          · exact collectNonArr_insert_mono na q' src.idx (hinv k' q' hkq)
      | uproj _ src | sproj _ _ src => exact hb calls acc (na.insert src.idx) (fun k' q' hkq => collectNonArr_insert_mono na q' src.idx (hinv k' q' hkq)) k q hres
      | ctor _ _ | reuse _ _ _ _ | pap _ _ | lit _ | box _ _ | unbox _ | isShared _ => exact hb calls acc (na.insert xv.idx) (fun k' q' hkq => collectNonArr_insert_mono na q' xv.idx (hinv k' q' hkq)) k q hres
    | jdecl _ _ _ _ => exact hb.2 calls _ _ (hb.1 calls acc na hinv) k q hres
    | case _ scr _ alts =>
        simp only [collectProjSrc, collectNonArr] at hres ⊢; rw [collectProjSrcAlts_eq_foldl] at hres; rw [collectNonArrAlts_eq_foldl]
        have hstep : ∀ (ls : List Alt) (a : Std.HashMap Nat Nat) (n : Std.HashSet Nat), (∀ arm ∈ ls, ∀ c a' n', (∀ k q, a'.get? k = some q → q ∈ n') → ∀ k q, (collectProjSrc c a' (altBody arm)).get? k = some q → q ∈ collectNonArr n' (altBody arm)) →
            (∀ k q, a.get? k = some q → q ∈ n) → ∀ k q, (ls.foldl (fun a arm => collectProjSrc calls a (altBody arm)) a).get? k = some q → q ∈ ls.foldl (fun n arm => collectNonArr n (altBody arm)) n := fun ls => by
          induction ls with | nil => exact fun _ _ _ ha k q h => ha k q h | cons arm _ ih => exact fun _ _ hst ha => ih _ _ (fun y hy => hst y (.tail _ hy)) (hst arm (.head _) calls _ _ ha)
        exact hstep alts.toList acc (na.insert scr.idx) hb (fun k' q' h => collectNonArr_insert_mono na q' scr.idx (hinv k' q' h)) k q hres
    | set _ _ _ _ | setTag _ _ _ | uset _ _ _ _ | sset _ _ _ _ _ _ | inc _ _ _ _ _ | dec _ _ _ _ _ | del _ _ => exact hb calls acc na hinv k q hres
    | ret _ | jmp _ _ | unreachable => exact hinv k q hres
  exact Std.HashSet.contains_iff_mem.2 (hgen {} {} {} (fun _ _ hk => by simp at hk) x p hsrc)

inductive DropsVar (p : Nat) : FnBody → Prop where
  | dec (y : VarId) (n : Nat) (c b : Bool) (cont : FnBody) (hy : y.idx = p) : DropsVar p (.dec y n c b cont)
  | del (y : VarId) (cont : FnBody) (hy : y.idx = p) : DropsVar p (.del y cont)
  | dec_skip (y : VarId) (n : Nat) (c b : Bool) (cont : FnBody) (h : DropsVar p cont) : DropsVar p (.dec y n c b cont)
  | del_skip (y : VarId) (cont : FnBody) (h : DropsVar p cont) : DropsVar p (.del y cont)
  | inc_skip (y : VarId) (n : Nat) (c b : Bool) (cont : FnBody) (h : DropsVar p cont) : DropsVar p (.inc y n c b cont)
  | proj_skip (x : VarId) (ty : IRType) (i : Nat) (src : VarId) (cont : FnBody) (h : DropsVar p cont) : DropsVar p (.vdecl x ty (.proj i src) cont)
  | uproj_skip (x : VarId) (ty : IRType) (i : Nat) (src : VarId) (cont : FnBody) (h : DropsVar p cont) : DropsVar p (.vdecl x ty (.uproj i src) cont)
  | sproj_skip (x : VarId) (ty : IRType) (n off : Nat) (src : VarId) (cont : FnBody) (h : DropsVar p cont) : DropsVar p (.vdecl x ty (.sproj n off src) cont)

theorem hasDecOf_sound (p : Nat) : ∀ b : FnBody, hasDecOf p b = true → DropsVar p b
  | .dec y n c bf cont, h => by simp only [hasDecOf, Bool.or_eq_true, beq_iff_eq] at h; exact h.elim (DropsVar.dec y n c bf cont ·.symm) (DropsVar.dec_skip y n c bf cont <| hasDecOf_sound p cont ·)
  | .del y cont, h => by simp only [hasDecOf, Bool.or_eq_true, beq_iff_eq] at h; exact h.elim (DropsVar.del y cont ·.symm) (DropsVar.del_skip y cont <| hasDecOf_sound p cont ·)
  | .inc y n c bf cont, h => DropsVar.inc_skip y n c bf cont (hasDecOf_sound p cont (by simpa [hasDecOf] using h))
  | .vdecl x ty e cont, h => by cases e with
    | proj _ _ => exact DropsVar.proj_skip x ty _ _ cont (hasDecOf_sound p cont (by simpa [hasDecOf] using h))
    | uproj _ _ => exact DropsVar.uproj_skip x ty _ _ cont (hasDecOf_sound p cont (by simpa [hasDecOf] using h))
    | sproj _ _ _ => exact DropsVar.sproj_skip x ty _ _ _ cont (hasDecOf_sound p cont (by simpa [hasDecOf] using h))
    | _ => simp [hasDecOf] at h
  | .jdecl _ _ _ _, h | .case _ _ _ _, h | .set _ _ _ _, h | .setTag _ _ _, h | .uset _ _ _ _, h | .sset _ _ _ _ _ _, h | .ret _, h | .jmp _ _, h | .unreachable, h => by simp [hasDecOf] at h

def CowHeap.jsTransferInc (h : CowHeap α) (id n : Nat) : CowHeap α := let n' := n - 1; if n' == 0 then h else h.rcInc (.arr id) n'
theorem projRefTransfer_cowHeap_equiv (h : CowHeap α) (id n : Nat) (hn : n ≥ 1) : ∀ k : Nat, (h.jsTransferInc id n).get k = ((h.rcInc (.arr id) n).rcDec (.arr id) 1).get k := fun k => by
  dsimp only [CowHeap.jsTransferInc, CowHeap.rcInc, CowHeap.rcDec]; by_cases hn1 : (n - 1 == 0) = true
  · have : n = 1 := by have := beq_iff_eq.mp hn1; omega
    subst this; by_cases hkid : k = id <;> simp_all [CowHeap.get, CowHeap.set]
  · simp only [hn1, Bool.false_eq_true, ↓reduceIte]; by_cases hkid : k = id; subst hkid; simp only [CowHeap.get_set_self]; rcases h.get k with ⟨el, rc, mk⟩; simp [show rc + (n - 1) = rc + n - 1 by omega]; simp only [CowHeap.get_set_ne _ _ hkid]

mutual
def stmtsTailSafe (allowSelf : Bool) : List JsStmt → Prop | [] => True | s :: ss => stmtTailSafe allowSelf s ∧ stmtsTailSafe allowSelf ss
def stmtTailSafe (allowSelf : Bool) : JsStmt → Prop | .tailContinue .. => allowSelf = true | .labeledBlock _ body => stmtsTailSafe allowSelf body | .constArrow _ _ body => stmtsTailSafe false body | .switchStmt _ arms => armsTailSafe allowSelf arms | _ => True
def armsTailSafe (allowSelf : Bool) : List JsSwitchArm → Prop | [] => True | .caseArm _ b :: rest | .defaultArm b :: rest => stmtsTailSafe allowSelf b ∧ armsTailSafe allowSelf rest
end
@[simp] private theorem stmtsTailSafe_nil {a : Bool} : stmtsTailSafe a [] := trivial
@[simp] private theorem stmtsTailSafe_cons_iff {a : Bool} {s : JsStmt} {ss : List JsStmt} : stmtsTailSafe a (s :: ss) ↔ stmtTailSafe a s ∧ stmtsTailSafe a ss := Iff.rfl
@[simp] private theorem stmtsTailSafe_append_iff {a : Bool} {s₁ s₂ : List JsStmt} : stmtsTailSafe a (s₁ ++ s₂) ↔ stmtsTailSafe a s₁ ∧ stmtsTailSafe a s₂ := by induction s₁ with | nil => simp [stmtsTailSafe] | cons _ _ ih => simp [stmtsTailSafe, ih, and_assoc]
mutual
private theorem stmtsTailSafe_mono : ∀ {s : List JsStmt}, stmtsTailSafe false s → stmtsTailSafe true s | [], _ => trivial | _ :: _, h => ⟨stmtTailSafe_mono h.1, stmtsTailSafe_mono h.2⟩
private theorem stmtTailSafe_mono : ∀ {st : JsStmt}, stmtTailSafe false st → stmtTailSafe true st | s, h => by cases s with | tailContinue => simp [stmtTailSafe] at h | labeledBlock => exact stmtsTailSafe_mono h | constArrow => exact h | switchStmt => exact armsTailSafe_mono h | _ => simp [stmtTailSafe]
private theorem armsTailSafe_mono : ∀ {arms : List JsSwitchArm}, armsTailSafe false arms → armsTailSafe true arms | [], _ => trivial | .caseArm _ _ :: _, h | .defaultArm _ :: _, h => ⟨stmtsTailSafe_mono h.1, armsTailSafe_mono h.2⟩
end
private theorem hasSelfTailAltsAux_mem {f : Name} {onlyRec active : Bool} : ∀ {ls : List Alt}, hasSelfTailAltsAux f onlyRec active ls = false → ∀ arm ∈ ls, hasSelfTailAux f onlyRec active (altBody arm) = false
  | [], _, _, h => nomatch h | arm :: _, h, a, ha => have h' : hasSelfTailAux f onlyRec active (altBody arm) = false ∧ hasSelfTailAltsAux f onlyRec active _ = false := by cases arm <;> simpa [hasSelfTailAltsAux, Bool.or_eq_false_iff, altBody] using h
      (List.mem_cons.1 ha).elim (fun e => e ▸ h'.1) (hasSelfTailAltsAux_mem h'.2 a)

/-- Soundness of `hasJpSelfTail`: whenever `hasJpSelfTail f b = false`, no `.constArrow` closure generated by `lowerBody c b` ever contains an illegal `.tailContinue`. -/
theorem noTailCont_of_hasJpSelfTail_false (f : Name) (b : FnBody) (c : Ctx) (hself : c.selfFn = none ∨ c.selfFn = some f) :
    (hasSelfTailAux f true true b = false → stmtsTailSafe false (lowerBody c b)) ∧ (hasSelfTailAux f true false b = false → stmtsTailSafe true (lowerBody c b)) := by
  revert c; refine fnBody_ind (fun b => ∀ c, c.selfFn = none ∨ c.selfFn = some f → (hasSelfTailAux f true true b = false → stmtsTailSafe false (lowerBody c b)) ∧ (hasSelfTailAux f true false b = false → stmtsTailSafe true (lowerBody c b))) (fun b hb c hself => ?_) b; cases b with
  | vdecl x ty e cont =>
      refine ⟨fun h => ?_, fun h => ?_⟩
      · cases e with
        | fap g ys =>
            simp only [hasSelfTailAux, Bool.true_and, Bool.or_eq_false_iff] at h
            have hnotSelf : ¬(c.selfFn == some g && retsVar x cont) = true := fun hc => by simp only [Bool.and_eq_true, beq_iff_eq] at hc; rcases hself with hsn | hsf; rw [hsn] at hc; cases hc.1; rw [hsf] at hc; cases hc.1; rw [hc.2] at h; simp at h
            rw [show lowerBody c (.vdecl x ty (.fap g ys) cont) = .letVar (v x) (lowerExpr c ty (.fap g ys)) :: lowerBody c cont by simp [lowerBody, hnotSelf]]; exact ⟨trivial, (hb c hself).1 h.2⟩
        | _ => exact ⟨trivial, (hb c hself).1 (by simpa [hasSelfTailAux] using h)⟩
      · cases e with
        | fap _ _ => simp only [lowerBody]; split; (split <;> simp [stmtTailSafe]); exact ⟨trivial, (hb c hself).2 (by simp only [hasSelfTailAux, Bool.false_and, Bool.false_or] at h; exact h)⟩
        | _ => exact ⟨trivial, (hb c hself).2 (by simpa [hasSelfTailAux] using h)⟩
  | jdecl j xs val _ =>
      have hself' : ({ c with inlineJps := c.inlineJps.insert j.idx xs } : Ctx).selfFn = none ∨ ({ c with inlineJps := c.inlineJps.insert j.idx xs } : Ctx).selfFn = some f := hself
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp only [hasSelfTailAux, Bool.or_eq_false_iff] at h; by_cases hj : hasJmpTo j val = true <;> simp only [lowerBody, hj, Bool.not_true, Bool.not_false, ↓reduceIte]
        · exact ⟨(hb.1 c hself).1 h.1, (hb.2 c hself).1 h.2⟩
        · have hv := (hb.1 c hself).1 h.1; have hc := (hb.2 _ hself').1 h.2; by_cases hemp : xs.isEmpty = true <;> simp [hemp, stmtTailSafe, hv, hc]
      · simp only [hasSelfTailAux, Bool.or_eq_false_iff] at h; by_cases hj : hasJmpTo j val = true
        · simp only [hj, Bool.false_or, ite_true] at h; simp only [lowerBody, hj, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact ⟨(hb.1 c hself).1 h.1, (hb.2 c hself).2 h.2⟩
        · have hjF := Bool.eq_false_iff.2 hj; simp only [hjF, Bool.false_or, ite_true] at h; simp only [lowerBody, hjF, Bool.not_false, ↓reduceIte]
          have hv := (hb.1 c hself).2 h.1; have hc := (hb.2 _ hself').2 h.2; by_cases hemp : xs.isEmpty = true <;> simp [hemp, stmtTailSafe, hv, hc]
  | case _ _ _ alts =>
      have mkArms : ∀ a (ls : List Alt), (∀ arm ∈ ls, stmtsTailSafe a (lowerBody c (altBody arm))) → armsTailSafe a (lowerAlts c ls) := fun a ls hls => by induction ls with | nil => trivial | cons arm _ ih => cases arm <;> exact ⟨hls _ (.head _), ih fun x hx => hls x (.tail _ hx)⟩
      exact ⟨fun h => by simp only [lowerBody, stmtsTailSafe, stmtTailSafe, and_true]; exact mkArms false alts.toList fun arm harm => (hb arm harm c hself).1 (hasSelfTailAltsAux_mem h arm harm),
             fun h => by simp only [lowerBody, stmtsTailSafe, stmtTailSafe, and_true]; exact mkArms true alts.toList fun arm harm => (hb arm harm c hself).2 (hasSelfTailAltsAux_mem h arm harm)⟩
  | inc x _ _ _ _ =>
      have hite : ∀ {a} {m : Nat} {ss : List JsStmt}, stmtsTailSafe a ss → stmtsTailSafe a (if (m == 0 || c.nonArr.contains x.idx) = true then ss else .incRef (v x) m :: ss) := fun hs => by split <;> simp [stmtTailSafe, hs]
      exact ⟨fun h => hite ((hb c hself).1 h), fun h => hite ((hb c hself).2 h)⟩
  | dec _ _ _ _ _ | del _ _ => refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp only [lowerBody] <;> split <;> first | exact (hb c hself).1 h | exact ⟨trivial, (hb c hself).1 h⟩ | exact (hb c hself).2 h | exact ⟨trivial, (hb c hself).2 h⟩
  | set _ _ _ _ | setTag _ _ _ | uset _ _ _ _ | sset _ _ _ _ _ _ => exact ⟨fun h => ⟨trivial, (hb c hself).1 h⟩, fun h => ⟨trivial, (hb c hself).2 h⟩⟩
  | ret _ | jmp _ _ | unreachable => constructor <;> intro _ <;> (try simp [lowerBody]; try split) <;> simp [stmtTailSafe]

end Js.Proofs
