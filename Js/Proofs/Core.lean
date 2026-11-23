import Js.Backend

namespace Js.Proofs

open Lean IR

/-! ## 1. Digit/String Injectivity, Identifier Hygiene, `jsStr` Safety & `reach` Closure -/

@[simp] theorem toString_str_eq (s : String) : toString s = s := rfl
theorem nat_toString_digits (n : Nat) : ∀ c ∈ (toString n).toList, c.isDigit = true := by
  simpa [Nat.toString_eq_repr, Nat.toList_repr] using fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
theorem nat_toString_inj {a b : Nat} (h : toString a = toString b) : a = b := by
  rw [← Nat.ofDigitChars_ten_toDigits (n := a), ← Nat.ofDigitChars_ten_toDigits (n := b), ← Nat.toList_repr, ← Nat.toList_repr, ← Nat.toString_eq_repr, ← Nat.toString_eq_repr, h]
private theorem pref_nat_inj (pfx : String) {a b : Nat} (h : pfx ++ toString a = pfx ++ toString b) : a = b :=
  nat_toString_inj (String.ext (by have := congrArg String.toList h; simpa [String.toList_append] using this))
private theorem digits_sep_inj {sep : Char} (hsep : sep.isDigit = false) :
    ∀ {d₁ d₂ r₁ r₂ : List Char}, (∀ c ∈ d₁, c.isDigit = true) → (∀ c ∈ d₂, c.isDigit = true) → d₁ ++ sep :: r₁ = d₂ ++ sep :: r₂ → d₁ = d₂ ∧ r₁ = r₂
  | [], [], _, _, _, _, h => by simpa using h
  | [], _ :: _, _, _, _, hd, h => by simp only [List.nil_append, List.cons_append, List.cons.injEq] at h; exact absurd (h.1 ▸ hd _ (.head _)) (by rw [hsep]; decide)
  | _ :: _, [], _, _, hd, _, h => by simp only [List.cons_append, List.nil_append, List.cons.injEq] at h; exact absurd (h.1 ▸ hd _ (.head _)) (by rw [hsep]; decide)
  | c₁ :: _, c₂ :: _, _, _, hd₁, hd₂, h => by simp only [List.cons_append, List.cons.injEq] at h; obtain ⟨rfl, h2⟩ := h; obtain ⟨h1, hr⟩ := digits_sep_inj hsep (fun c hc => hd₁ c (.tail _ hc)) (fun c hc => hd₂ c (.tail _ hc)) h2; exact ⟨congrArg (c₁ :: ·) h1, hr⟩

def genGlobalName (counter : Nat) : String := s!"_g{counter}"
def inlineJpSlot (j : JoinPointId) (i : Nat) : String := s!"_{jp j}_{i}"
theorem v_inj {x y : VarId} (h : v x = v y) : x.idx = y.idx := pref_nat_inj "x" h
theorem jp_inj {i k : JoinPointId} (h : jp i = jp k) : i.idx = k.idx := pref_nat_inj "j" h
theorem genGlobalName_inj {a b : Nat} (h : genGlobalName a = genGlobalName b) : a = b := pref_nat_inj "_g" h
theorem v_ne_jp (x : VarId) (j : JoinPointId) : v x ≠ jp j := fun h => by have := congrArg String.toList h; simp [v, jp, String.toList_append] at this
theorem list_take_ne_x_append_digits (m j i : Nat) : s!"x{m}" ≠ s!"_{jp ⟨j⟩}_{i}" := fun h => by have := congrArg String.toList h; simp [jp, String.toList_append] at this
theorem inlineJpSlot_inj {j₁ j₂ : JoinPointId} {i₁ i₂ : Nat} (h : inlineJpSlot j₁ i₁ = inlineJpSlot j₂ i₂) : j₁.idx = j₂.idx ∧ i₁ = i₂ := by
  have hl := congrArg String.toList h; have hd (n : Nat) : ∀ c ∈ n.repr.toList, c.isDigit = true := by simpa [← Nat.toString_eq_repr] using nat_toString_digits n
  simp only [inlineJpSlot, jp, toString_str_eq, Nat.toString_eq_repr, String.toList_append, show "_".toList = ['_'] from rfl, show "j".toList = ['j'] from rfl, List.cons_append, List.nil_append, List.cons.injEq, true_and, List.append_assoc] at hl
  have ⟨h1, h2⟩ := digits_sep_inj (sep := '_') rfl (hd j₁.idx) (hd j₂.idx) hl; exact ⟨nat_toString_inj (by simpa [Nat.toString_eq_repr] using String.ext h1), nat_toString_inj (by simpa [Nat.toString_eq_repr] using String.ext h2)⟩
theorem genGlobalName_disjoint_all (counter : Nat) (x : VarId) (j : JoinPointId) (i : Nat) (ext : String) :
    genGlobalName counter ≠ v x ∧ genGlobalName counter ≠ jp j ∧ genGlobalName counter ≠ inlineJpSlot j i ∧
    genGlobalName counter ≠ "$." ++ ext ∧ genGlobalName counter ≠ "__step" ∧ genGlobalName counter ≠ "__r" ∧ genGlobalName counter ≠ "__externs" := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> · intro h; have hl := congrArg String.toList h; simp [genGlobalName, v, jp, inlineJpSlot, String.toList_append] at hl
theorem ctxJs_fallback_startsWith_dollar (c : Ctx) (n : Name) (hmiss : c.names.get? n = none) : (c.js n).startsWith "$." = true := by
  have hget : c.names[n]? = none := hmiss; simp [Ctx.js, hget]

def jsReservedWords : List String :=
  ["break", "case", "catch", "class", "const", "continue", "debugger", "default", "delete", "do", "else", "enum", "export", "extends", "false",
   "finally", "for", "function", "if", "import", "in", "instanceof", "let", "new", "null", "return", "super", "switch", "this", "throw", "true",
   "try", "typeof", "var", "void", "while", "with", "yield", "await", "implements", "interface", "package", "private", "protected", "public",
   "static", "__step", "__r", "__externs", "Error", "Object", "Array"]
private def isInternalTag : List UInt8 → Bool | 120 :: _ | 106 :: _ | 36 :: _ | 95 :: 103 :: _ | 95 :: 106 :: _ => true | _ => false
private theorem not_res_of_pfx {p t : String} (hp : ∀ r, isInternalTag (p.toByteArray.data.toList ++ r) = true) : p ++ t ∉ jsReservedWords := fun hm => by
  have h1 : isInternalTag (p ++ t).toByteArray.data.toList = true := by rw [String.toByteArray_append, ByteArray.data_append, Array.toList_append]; exact hp _
  have h2 := List.all_eq_true.1 (show jsReservedWords.all (!isInternalTag ·.toByteArray.data.toList) = true from rfl) _ hm; rw [h1] at h2; exact nomatch h2
theorem ident_ne_jsKeyword (x : VarId) (j : JoinPointId) (k i : Nat) (ext : String) :
    v x ∉ jsReservedWords ∧ jp j ∉ jsReservedWords ∧ genGlobalName k ∉ jsReservedWords ∧ inlineJpSlot j i ∉ jsReservedWords ∧ ("$." ++ ext) ∉ jsReservedWords :=
  ⟨not_res_of_pfx (p := "x") fun _ => rfl, not_res_of_pfx (p := "j") fun _ => rfl, not_res_of_pfx (p := "_g") fun _ => rfl,
   by have heq : inlineJpSlot j i = "_j" ++ (toString j.idx ++ "_" ++ toString i) := by
        simp only [inlineJpSlot, jp, toString_str_eq, String.append_assoc]; rw [← String.append_assoc (s₁ := "_") (s₂ := "j"), show "_" ++ "j" = "_j" from rfl]
      rw [heq]; exact not_res_of_pfx (p := "_j") fun _ => rfl, not_res_of_pfx (p := "$.") fun _ => rfl⟩

private def mangleStep (s : String) (c : Char) : String := if c.isAlphanum then s.push c else if c == '.' || c == '_' then s.push '_' else s ++ s!"x{c.toNat}"
theorem mangle_chars_safe (n : Name) : ∀ ch ∈ (mangle n).toList, ch.isAlphanum = true ∨ ch = '_' := by
  have hfold (cs : List Char) : ∀ s, (∀ ch ∈ s.toList, ch.isAlphanum = true ∨ ch = '_') → ∀ ch ∈ (cs.foldl mangleStep s).toList, ch.isAlphanum = true ∨ ch = '_' := by
    induction cs with | nil => exact fun _ hs => hs | cons c _ ih =>
      intro s hs; refine ih _ fun ch hch => ?_; unfold mangleStep at hch; split at hch
      · exact (by simpa [String.toList_push] using hch : ch ∈ s.toList ∨ ch = c).elim (hs ch) (· ▸ .inl ‹_›)
      · split at hch; exact (by simpa [String.toList_push] using hch : ch ∈ s.toList ∨ ch = '_').elim (hs ch) .inr
        exact (List.mem_append.1 (String.toList_append ▸ hch)).elim (hs ch) fun h2 => (by simpa [String.toList_append] using h2 : ch = 'x' ∨ ch ∈ (toString c.toNat).toList).elim (· ▸ .inl (by decide)) fun hd => .inl (by simp [Char.isAlphanum, nat_toString_digits c.toNat ch hd])
  rw [show mangle n = n.toString.foldl mangleStep "" from rfl]; simpa [String.foldl] using hfold n.toString.toList "" (fun _ h => by simp at h)

inductive ValidJsStrBody : List Char → Prop where
  | nil : ValidJsStrBody []
  | plain {c : Char} {cs : List Char} : 32 ≤ c.toNat → c ≠ '"' → c ≠ '\\' → ValidJsStrBody cs → ValidJsStrBody (c :: cs)
  | esc {c : Char} {cs : List Char} : 32 ≤ c.toNat → ValidJsStrBody cs → ValidJsStrBody ('\\' :: c :: cs)
private theorem digitChar16_valid : ∀ (d : Nat), d < 16 → 32 ≤ (Nat.digitChar d).toNat ∧ Nat.digitChar d ≠ '"' ∧ Nat.digitChar d ≠ '\\'
  | 0,_|1,_|2,_|3,_|4,_|5,_|6,_|7,_|8,_|9,_|10,_|11,_|12,_|13,_|14,_|15,_ => ⟨by decide, by decide, by decide⟩ | _ + 16, h => by omega
private theorem hex_toDigitsCore_valid : ∀ (fuel n : Nat) (ds : List Char), ValidJsStrBody ds → ValidJsStrBody (Nat.toDigitsCore 16 fuel n ds)
  | 0, _, _, hds => hds
  | fuel + 1, n, ds, hds => by have ⟨h1, h2, h3⟩ := digitChar16_valid (n % 16) (Nat.mod_lt _ (by omega)); dsimp only [Nat.toDigitsCore]; split; exact .plain h1 h2 h3 hds; exact hex_toDigitsCore_valid fuel (n / 16) _ (.plain h1 h2 h3 hds)
theorem jsStr_safe (s : String) : ∃ body : String, jsStr s = "\"" ++ body ++ "\"" ∧ ValidJsStrBody body.toList := by
  have happ : ∀ {xs ys : List Char}, ValidJsStrBody xs → ValidJsStrBody ys → ValidJsStrBody (xs ++ ys) := fun hx hy => by
    induction hx with | nil => exact hy | plain h1 h2 h3 _ ih => exact .plain h1 h2 h3 ih | esc h1 _ ih => exact .esc h1 ih
  have hchar (c : Char) : ValidJsStrBody (jsStrChar c).toList := by
    unfold jsStrChar; split <;> try exact .esc (by decide) .nil
    rename_i h1 h2 _ _ _; split
    · rw [String.toList_append]; have hd : ValidJsStrBody (Nat.toDigits 16 c.toNat) := hex_toDigitsCore_valid (c.toNat + 1) c.toNat [] .nil
      have hb : ValidJsStrBody (if (Nat.toDigits 16 c.toNat).length == 1 then '0' :: Nat.toDigits 16 c.toNat else Nat.toDigits 16 c.toNat) := by split; exact .plain (c := '0') (by decide) (by decide) (by decide) hd; exact hd
      simpa only [String.toList_ofList, show "\\x".toList = ['\\', 'x'] from rfl, List.cons_append, List.nil_append] using ValidJsStrBody.esc (c := 'x') (by decide) hb
    · rw [String.toList_singleton]; exact .plain (by omega) h2 h1 .nil
  have hfold (cs : List Char) : ∀ acc : String, ValidJsStrBody acc.toList → ValidJsStrBody (cs.foldl (fun a c => a ++ jsStrChar c) acc).toList := by
    induction cs with | nil => exact fun _ ha => ha | cons c _ ih => exact fun acc ha => ih _ (by rw [String.toList_append]; exact happ ha (hchar c))
  exact ⟨s.foldl (fun a c => a ++ jsStrChar c) "", rfl, by simpa [jsStr, String.foldl] using hfold s.toList "" .nil⟩

def assignProgramNamesStep (st : Std.HashMap Name String × Nat) (name : Name) (entryMap : Std.HashMap Name String) (isFdecl : Bool) : Std.HashMap Name String × Nat :=
  if isFdecl then match entryMap.get? name with | some s => (st.1.insert name s, st.2) | none => (st.1.insert name (genGlobalName st.2), st.2 + 1) else st
theorem assignProgramNames_invariant (steps : List (Name × Bool)) (entryMap : Std.HashMap Name String)
    (hentries : ∀ n s, entryMap.get? n = some s → ∀ i, s ≠ genGlobalName i) (nm₀ : Std.HashMap Name String) (cnt₀ : Nat)
    (hbound : ∀ k nm, nm₀.get? k = some nm → ∀ i ≥ cnt₀, nm ≠ genGlobalName i) :
    let (nm₁, cnt₁) := steps.foldl (fun st p => assignProgramNamesStep st p.1 entryMap p.2) (nm₀, cnt₀)
    cnt₀ ≤ cnt₁ ∧ (∀ k nm, nm₁.get? k = some nm → ∀ i ≥ cnt₁, nm ≠ genGlobalName i) := by
  induction steps generalizing nm₀ cnt₀ with | nil => exact ⟨Nat.le_refl _, hbound⟩ | cons p _ ih =>
    simp only [List.foldl_cons, assignProgramNamesStep]; cases p.2 with | false => exact ih nm₀ cnt₀ hbound | true =>
    cases he : entryMap.get? p.1 with
    | some s => exact ih (nm₀.insert p.1 s) cnt₀ fun k nm hg i hi => by rw [Std.HashMap.get?_insert] at hg; split at hg; (cases hg; exact hentries p.1 s he i); exact hbound k nm hg i hi
    | none => have ih' := ih (nm₀.insert p.1 (genGlobalName cnt₀)) (cnt₀ + 1) fun k nm hg i hi => by rw [Std.HashMap.get?_insert] at hg; split at hg; (cases hg; intro hc; have := genGlobalName_inj hc; omega); exact hbound k nm hg i (by omega)
              exact ⟨Nat.le_trans (Nat.le_succ _) ih'.1, ih'.2⟩

/-! ### Reachability Closure & Server-Leak Isolation (`reach_closed`) -/

def reachEdges (env : Environment) (n : Name) : List Name :=
  match findEnvDecl env n with | some (.fdecl (body := b) ..) => (callees b #[]).toList ++ (getInitFnNameFor? env n).toList | _ => []
private theorem reachAux_closed_aux (env : Environment) :
    ∀ (fuel : Nat) (rest : List Name) (seen : Array Name) (visited : Std.HashSet Name) (out : Array Name),
      (∀ x, x ∈ visited ↔ x ∈ seen.toList) → (∀ x ∈ seen.toList, ∀ y ∈ reachEdges env x, y ∈ seen.toList ∨ y ∈ rest) →
      reachAux env fuel rest seen visited = .ok out → (∀ x ∈ seen.toList, x ∈ out.toList) ∧ (∀ r ∈ rest, r ∈ out.toList) ∧ (∀ x ∈ out.toList, ∀ y ∈ reachEdges env x, y ∈ out.toList)
  | _, [], _, _, _, _, hclosed, hok => by simp only [reachAux] at hok; cases hok; exact ⟨(fun _ hx => hx), (fun _ hr => nomatch hr), fun x hx y hy => (hclosed x hx y hy).elim id fun h => nomatch h⟩
  | 0, _ :: _, _, _, _, _, _, hok => by simp only [reachAux] at hok; nomatch hok
  | f + 1, n :: rest, seen, visited, out, hiff, hclosed, hok => by
      dsimp only [reachAux] at hok; by_cases hcon : visited.contains n = true
      · simp only [hcon, ↓reduceIte] at hok; have hn := (hiff n).1 (Std.HashSet.contains_iff_mem.1 hcon)
        obtain ⟨ihS, ihR, ihC⟩ := reachAux_closed_aux env f rest seen visited out hiff (fun x hx y hy => (hclosed x hx y hy).elim .inl fun hr => (List.mem_cons.1 hr).elim (· ▸ .inl hn) .inr) hok
        exact ⟨ihS, fun r hr => (List.mem_cons.1 hr).elim (· ▸ ihS n hn) (ihR r), ihC⟩
      · simp only [Bool.eq_false_iff.2 hcon, Bool.false_eq_true, ↓reduceIte] at hok
        have hstep : reachAux env f (rest ++ reachEdges env n) (seen.push n) (visited.insert n) = .ok out := by unfold reachEdges; cases hfd : findEnvDecl env n with | none => simp only [hfd, List.append_nil] at hok ⊢; exact hok | some d => cases d <;> (simp only [hfd, List.append_nil] at hok ⊢; exact hok)
        obtain ⟨ihS, ihR, ihC⟩ := reachAux_closed_aux env f (rest ++ reachEdges env n) (seen.push n) (visited.insert n) out
          (fun x => by rw [Std.HashSet.mem_insert, beq_iff_eq, Array.toList_push, List.mem_append, List.mem_singleton, hiff x]; exact ⟨fun h => h.elim (fun e => .inr e.symm) .inl, fun h => h.elim .inr fun e => .inl e.symm⟩)
          (fun x hx y hy => by rcases (by simpa [Array.toList_push] using hx : x ∈ seen.toList ∨ x = n) with hxS | rfl; exact (hclosed x hxS y hy).elim (fun ys => .inl (by simp [Array.toList_push, ys])) fun yr => (List.mem_cons.1 yr).elim (· ▸ .inl (by simp [Array.toList_push])) fun yr' => .inr (List.mem_append_left _ yr'); exact .inr (List.mem_append_right _ hy)) hstep
        exact ⟨fun x hx => ihS x (by simp [Array.toList_push, hx]), fun r hr => (List.mem_cons.1 hr).elim (· ▸ ihS n (by simp [Array.toList_push])) (fun hr' => ihR r (List.mem_append_left _ hr')), ihC⟩
theorem reach_closed (env : Environment) (roots : List Name) (out : Array Name) (hreach : reach env roots #[] = .ok out) :
    (∀ r ∈ roots, r ∈ out.toList) ∧ (∀ x ∈ out.toList, ∀ y ∈ reachEdges env x, y ∈ out.toList) :=
  (reachAux_closed_aux env 1000000 roots #[] ∅ out (fun _ => by simp) (fun _ h => by simp at h) hreach).2
def isClientSafeDecl (env : Environment) (n : Name) : Bool := (clientLeakReason? env n).isNone
inductive ReachPath (env : Environment) : Name → List Name → Prop where
  | nil (a : Name) : ReachPath env a [] | cons {a b : Name} {rest : List Name} : b ∈ reachEdges env a → ReachPath env b rest → ReachPath env a (b :: rest)
theorem reach_verifyNoServerLeak_sound (env : Environment) (roots : List Name) (out : Array Name)
    (hreach : reach env roots #[] = .ok out) (hgate : verifyNoServerLeakInClient env out = .ok ()) :
    ∀ (path : List Name) (r : Name), r ∈ roots → ReachPath env r path → ∀ x ∈ r :: path, isClientSafeDecl env x = true := by
  obtain ⟨hroots, hclosed⟩ := reach_closed env roots out hreach
  have hsafeOut : ∀ x ∈ out.toList, isClientSafeDecl env x = true := by
    unfold verifyNoServerLeakInClient at hgate; rw [← Array.forIn_toList] at hgate
    have hfi : ∀ {step : Name → PUnit → Except String (ForInStep PUnit)} (ls : List Name),
        (do forIn ls () step; pure ()) = .ok () → (∀ n, step n () = .ok (.yield ()) → isClientSafeDecl env n = true) → (∀ n u, step n () ≠ .ok (.done u)) → ∀ x ∈ ls, isClientSafeDecl env x = true := fun {step} ls => by
      induction ls with | nil => exact fun _ _ _ _ h => nomatch h | cons n _ ih =>
        intro hf hst hnd x hx; rw [List.forIn_cons] at hf; cases hs : step n () with | error _ => rw [hs] at hf; simp [bind, Except.bind] at hf | ok r => cases r with | done u => exact absurd hs (hnd n u) | yield _ => rw [hs] at hf; exact (List.mem_cons.1 hx).elim (· ▸ hst n hs) (ih hf hst hnd x)
    refine hfi out.toList hgate (fun n hn => by dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, isClientSafeDecl] at hn ⊢; cases hc : clientLeakReason? env n with | none => rfl | some _ => simp [hc] at hn)
      (fun n u hn => by dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hn; cases hc : clientLeakReason? env n <;> simp [hc] at hn)
  have gen (p : List Name) : ∀ cur, cur ∈ out.toList → ReachPath env cur p → ∀ x ∈ cur :: p, isClientSafeDecl env x = true := by
    induction p with | nil => exact fun cur hc _ x hx => (List.mem_singleton.1 hx) ▸ hsafeOut _ hc | cons nxt _ ih => intro cur hc hch x hx; cases hch with | cons hadj hrest => exact (List.mem_cons.1 hx).elim (· ▸ hsafeOut _ hc) (ih nxt (hclosed cur hc nxt hadj) hrest x)
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
  | .pap fn ar args => .pap fn ar (evalJsExprList env args) | .tc args => .tc (evalJsExprList env args)
  | .call fn args => if fn == "$.tag" then match args with | [e] => .num (jsTag (evalJsExpr env e)) | _ => .num 0 else .num 0 | .app _ _ => .num 0
def evalJsExprList (env : String → JsVal) : List JsExpr → List JsVal | [] => [] | e :: es => evalJsExpr env e :: evalJsExprList env es
end
@[simp] theorem evalJsExprList_map (env : String → JsVal) : ∀ (xs : List α) (f : α → JsExpr), evalJsExprList env (xs.map f) = xs.map (fun x => evalJsExpr env (f x))
  | [], _ => rfl | _ :: xs, f => by dsimp only [List.map, evalJsExprList]; rw [evalJsExprList_map env xs f]
theorem jsTag_lowerCtor (env : String → JsVal) (info : CtorInfo) (ys : Array Arg) : jsTag (evalJsExpr env (lowerCtor info ys)) = info.cidx := by unfold lowerCtor; split <;> rfl
theorem fieldProj_lowerCtor (c : Ctx) (ty : IRType) (env : String → JsVal) (x : VarId) (info : CtorInfo) (ys : Array Arg) (idx : Nat)
    (hboxed : ¬(info.size == 0 && info.usize == 0 && info.ssize == 0) = true) (hidx : idx < ys.toList.length) (hx : env (v x) = evalJsExpr env (lowerCtor info ys)) :
    evalJsExpr env (lowerExpr c ty (.proj idx x)) = evalJsExpr env (lowerArg (ys.toList.getD idx .erased)) := by
  dsimp only [lowerExpr, evalJsExpr]; rw [hx]; dsimp only [lowerCtor]; rw [ite_eq_right hboxed]; dsimp only [evalJsExpr]; rw [evalJsExprList_map]
  generalize ys.toList = args at hidx ⊢; induction args generalizing idx with | nil => nomatch hidx | cons _ _ ih => cases idx with | zero => rfl | succ k => exact ih k (Nat.lt_of_succ_lt_succ hidx)

inductive RtFnVal (α : Type) where | ground (v : α) | pap (fn : List α → RtFnVal α) (arity : Nat) (acc : List α)
def rtPap (fn : List α → RtFnVal α) (arity : Nat) (args : List α) : RtFnVal α := .pap fn arity args
def rtApp : Nat → RtFnVal α → List α → Option (RtFnVal α)
  | 0, _, _ => none | _, .ground v, _ => some (.ground v)
  | fuel + 1, .pap fn arity acc, xs => let rem := arity - acc.length
      if xs.length < rem then some (.pap fn arity (acc ++ xs)) else if xs.length == rem then some (fn (acc ++ xs)) else rtApp fuel (fn (acc ++ xs.take rem)) (xs.drop rem)
theorem rtApp_under_compose {α : Type} (fn : List α → RtFnVal α) (arity : Nat) (acc xs₁ xs₂ : List α) (fuel : Nat) (hunder : acc.length + xs₁.length < arity) :
    (rtApp (fuel + 1) (.pap fn arity acc) xs₁).bind (fun f' => rtApp (fuel + 1) f' xs₂) = rtApp (fuel + 1) (.pap fn arity acc) (xs₁ ++ xs₂) := by
  dsimp only [rtApp]; rw [ite_eq_left (by omega)]; simp only [Option.bind, rtApp, List.length_append, List.append_assoc]
  by_cases hlt2 : xs₂.length < arity - (acc.length + xs₁.length); · rw [ite_eq_left hlt2, ite_eq_left (by omega)]
  have hrhs : ¬xs₁.length + xs₂.length < arity - acc.length := by omega
  rw [ite_eq_right hlt2, ite_eq_right hrhs]; by_cases heq2 : xs₂.length = arity - (acc.length + xs₁.length); · rw [ite_eq_left (beq_iff_eq.2 heq2), ite_eq_left (beq_iff_eq.2 (by omega))]
  rw [ite_eq_right (fun h => heq2 (eq_of_beq h)), ite_eq_right (fun h => heq2 (by have := eq_of_beq h; omega)), show arity - (acc.length + xs₁.length) = arity - acc.length - xs₁.length by omega,
    show (xs₁ ++ xs₂).take (arity - acc.length) = xs₁ ++ xs₂.take (arity - acc.length - xs₁.length) by rw [List.take_append, List.take_of_length_le (by omega)],
    show (xs₁ ++ xs₂).drop (arity - acc.length) = xs₂.drop (arity - acc.length - xs₁.length) by rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]]
theorem rtApp_exact_equiv {α : Type} (fn : List α → RtFnVal α) (arity : Nat) (acc xs : List α) (fuel : Nat) (hacc : acc.length ≤ arity) (hsat : acc.length + xs.length = arity) :
    rtApp (fuel + 1) (rtPap fn arity acc) xs = some (fn (acc ++ xs)) := by simp [rtPap, rtApp, show ¬xs.length < arity - acc.length by omega, show (xs.length == arity - acc.length) = true from beq_iff_eq.2 (by omega)]
theorem rtApp_over_equiv {α : Type} (fn : List α → RtFnVal α) (arity : Nat) (acc xs₁ xs₂ : List α) (fuel : Nat) (hacc : acc.length ≤ arity) (hsat : acc.length + xs₁.length = arity) (hmore : 0 < xs₂.length) :
    rtApp (fuel + 2) (rtPap fn arity acc) (xs₁ ++ xs₂) = rtApp (fuel + 1) (fn (acc ++ xs₁)) xs₂ := by
  dsimp only [rtPap, rtApp]; rw [ite_eq_right (by simp; omega), ite_eq_right (fun h => by have := eq_of_beq h; simp at this; omega), show arity - acc.length = xs₁.length by omega, List.take_left, List.drop_left]
def recEval {α β : Type} (step : α → Sum α β) : Nat → α → Option β | 0, _ => none | fuel + 1, a => match step a with | .inl n => recEval step fuel n | .inr r => some r
def directLoopEval {α β : Type} (step : α → Sum α β) : Nat → α → Option β | 0, _ => none | fuel + 1, a => match step a with | .inl n => directLoopEval step fuel n | .inr r => some r
theorem directLoop_equiv {α β : Type} (step : α → Sum α β) : ∀ (fuel : Nat) (init : α), directLoopEval step fuel init = recEval step fuel init
  | 0, _ => rfl | f + 1, a => by simp only [directLoopEval, recEval]; cases step a with | inl n => exact directLoop_equiv step f n | inr _ => rfl
def encodeTrampolineStep (step : List JsVal → Sum (List JsVal) JsVal) (args : List JsVal) : JsVal := match step args with | .inl n => .tc n | .inr r => r
def trampolineLoop (stepFn : List JsVal → JsVal) : Nat → List JsVal → Option JsVal | 0, _ => none | fuel + 1, args => match stepFn args with | .tc n => trampolineLoop stepFn fuel n | r => some r
theorem trampoline_equiv (step : List JsVal → Sum (List JsVal) JsVal) (hnoSentinel : ∀ args v, step args = .inr v → ∀ xs, v ≠ .tc xs) :
    ∀ (fuel : Nat) (args : List JsVal), trampolineLoop (encodeTrampolineStep step) fuel args = recEval step fuel args
  | 0, _ => rfl | f + 1, args => by simp only [trampolineLoop, encodeTrampolineStep, recEval]; cases hs : step args with | inl n => exact trampoline_equiv step hnoSentinel f n | inr v => cases v with | tc xs => exact absurd rfl (hnoSentinel args (.tc xs) hs xs) | _ => rfl

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
variable {α : Type}
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
  dsimp only [cowUpdate]; split; exact ⟨by simp [readArray], fun alias _ hne => by simp [readArray, hne ‹_›]⟩
  exact ⟨by simp [readArray, get], fun alias halias _ => by by_cases ha : alias = id <;> simp [readArray, get, set, Nat.ne_of_lt hid, Nat.ne_of_lt halias, ha]⟩
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
  | none => exact ⟨⟨fun m s hm' => by simp only [get, set] at hm' ⊢; split at hm'; (cases hm'; exact Nat.lt_succ_self _); exact Nat.lt_trans (hbnd m s hm') (Nat.lt_succ_self _),
      fun m₁ m₂ s hm₁ hm₂ => by simp only [get, set, beq_iff_eq] at hm₁ hm₂; split at hm₁ <;> split at hm₂ <;> first | exact ‹m₁ = id›.trans ‹m₂ = id›.symm | (cases hm₁; exact absurd (hbnd m₂ _ hm₂) (by omega)) | (cases hm₂; exact absurd (hbnd m₁ _ hm₁) (by omega)) | exact huniq m₁ m₂ s hm₁ hm₂⟩,
      ⟨Nat.lt_succ_self _, fun m hm' => by simp only [get, set, beq_iff_eq] at hm' ⊢; split at hm'; (subst ‹m = id›; simp [readArray, get]); exact absurd (hbnd m _ hm') (by omega)⟩⟩
theorem SnapshotValid_cowUpdate (h : CowHeap α) (id : Nat) (f : List α → List α) (snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) :
    SnapshotValid snapStamp snapElems (h.cowUpdate id f).2 := by
  rcases hsnap with ⟨hlt, heq⟩; dsimp only [cowUpdate]; split
  · exact ⟨hlt, fun m hm => by by_cases hmid : m = id; (subst hmid; simp at hm); rw [get_set_ne _ _ hmid] at hm ⊢; exact heq m hm⟩
  · exact ⟨hlt, fun m hm => by by_cases hmf : m = h.nextId; (subst hmf; simp [get] at hm); by_cases hmid : m = id; (subst hmid; simp only [get, set, beq_iff_eq, hmf, ↓reduceIte] at hm ⊢; exact heq _ hm); simp only [get, set, beq_iff_eq, hmf, hmid, ↓reduceIte] at hm ⊢; exact heq m hm⟩
theorem SnapshotValid_cowUset (h : CowHeap α) (id idx : Nat) (val : α) (snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) :
    SnapshotValid snapStamp snapElems (h.cowUset id idx val).2 := SnapshotValid_cowUpdate h id (·.set idx val) snapStamp snapElems hsnap
theorem SnapshotValid_cowPush (h : CowHeap α) (id : Nat) (val : α) (snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) :
    SnapshotValid snapStamp snapElems (h.cowPush id val).2 := SnapshotValid_cowUpdate h id (· ++ [val]) snapStamp snapElems hsnap
theorem SnapshotValid_refMark (h : CowHeap α) (id : Nat) (snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) :
    SnapshotValid snapStamp snapElems (h.refMark id).2 := by
  rcases hsnap with ⟨hlt, heq⟩; dsimp only [refMark]; cases hm : (h.get id).mark with | some _ => exact ⟨hlt, heq⟩ | none =>
    exact ⟨Nat.lt_trans hlt (Nat.lt_succ_self _), fun m hm' => by by_cases hmid : m = id <;> simp only [get, set, beq_iff_eq, hmid, ↓reduceIte] at hm' ⊢; (cases hm'; omega); exact heq m hm'⟩
theorem refMark_snapshot_sound (h : CowHeap α) (id snapStamp : Nat) (snapElems : List α) (hsnap : SnapshotValid snapStamp snapElems h) (heqStamp : (h.refMark id).1 = snapStamp) :
    h.readArray id = snapElems := by
  rcases hsnap with ⟨_, heq⟩; dsimp only [refMark] at heqStamp; cases hm : (h.get id).mark <;> simp [hm] at heqStamp; omega; exact heq id (heqStamp ▸ hm)
def rcInc (h : CowHeap α) (v : RcVal) (n : Nat) : CowHeap α := match v with | .arr id => h.set id { h.get id with refcount := (h.get id).refcount + n } | .nonArr _ => h
def rcDec (h : CowHeap α) (v : RcVal) (n : Nat) : CowHeap α := match v with | .arr id => h.set id { h.get id with refcount := (h.get id).refcount - n } | .nonArr _ => h
@[simp] theorem rcInc_zero (h : CowHeap α) (v : RcVal) : h.rcInc v 0 = h := by cases v with | nonArr _ => rfl | arr id => cases h; simp only [rcInc, set, get, CowHeap.mk.injEq, true_and]; funext m; by_cases hm : m == id <;> simp_all
def jsTransferInc (h : CowHeap α) (id n : Nat) : CowHeap α := let n' := n - 1; if n' == 0 then h else h.rcInc (.arr id) n'
end CowHeap
structure MemoCell (α : Type) where
  ok : Bool := false
  val : Option α := none
def MemoCell.Valid (thunk : Unit → α) (c : MemoCell α) : Prop := c.ok = true → c.val = some (thunk ())
def memoForce (thunk : Unit → α) (defaultVal : α) (c : MemoCell α) : α × MemoCell α := if c.ok then (c.val.getD defaultVal, c) else let v := thunk (); (v, { ok := true, val := some v })
theorem memo_thunk_obs_equiv {α : Type} (thunk : Unit → α) (defaultVal : α) (c : MemoCell α) (hvalid : MemoCell.Valid thunk c) :
    let (res, c') := memoForce thunk defaultVal c; res = thunk () ∧ MemoCell.Valid thunk c' := by dsimp only [memoForce]; cases hok : c.ok with | false => simp [MemoCell.Valid] | true => simp [hok, hvalid hok, MemoCell.Valid]

/-! ## 3. Static RC & Tail-Call Analyses (`collectNonArr`, `collectProjSrc`, `hasDecOf`, `hasJpSelfTail`) -/

def altBody : Alt → FnBody | .ctor _ b | .default b => b
def fnBodyStep (P : FnBody → Prop) : FnBody → Prop
  | .vdecl _ _ _ cont | .set _ _ _ cont | .setTag _ _ cont | .uset _ _ _ cont | .sset _ _ _ _ _ cont | .inc _ _ _ _ cont | .dec _ _ _ _ cont | .del _ cont => P cont
  | .jdecl _ _ val cont => P val ∧ P cont | .case _ _ _ alts => ∀ arm ∈ alts.toList, P (altBody arm) | .ret _ | .jmp _ _ | .unreachable => True
theorem fnBody_ind (P : FnBody → Prop) (h : ∀ b, fnBodyStep P b → P b) : ∀ b, P b :=
  let go : ∀ (sz : Nat) (b : FnBody), sizeOf b ≤ sz → P b := fun sz => by
    induction sz using Nat.strongRecOn with | ind sz ih => intro b hsz; apply h; cases b with
      | vdecl _ _ _ c | set _ _ _ c | setTag _ _ c | uset _ _ _ c | sset _ _ _ _ _ c | inc _ _ _ _ c | dec _ _ _ _ c | del _ c => exact ih (sizeOf c) (by simp at hsz; omega) c (Nat.le_refl _)
      | jdecl _ _ v c => exact ⟨ih (sizeOf v) (by simp at hsz; omega) v (Nat.le_refl _), ih (sizeOf c) (by simp at hsz; omega) c (Nat.le_refl _)⟩
      | case tid x ty alts => intro arm harm; have h1 : sizeOf alts.toList < sizeOf (FnBody.case tid x ty alts) := by cases alts; simp; omega
                              have h2 : sizeOf (altBody arm) < sizeOf alts.toList := by clear hsz ih h1; generalize alts.toList = ls at harm ⊢; induction ls with | nil => nomatch harm | cons _ _ ihr => rcases List.mem_cons.1 harm with rfl | hm; (cases arm <;> simp [altBody] <;> omega); have := ihr hm; simp; omega
                              exact ih (sizeOf (altBody arm)) (by omega) (altBody arm) (Nat.le_refl _)
      | ret _ | jmp _ _ | unreachable => trivial
  fun b => go (sizeOf b) b (Nat.le_refl _)
private theorem collectNonArrAlts_inv (I : Std.HashSet Nat → Prop) : ∀ ls a, (∀ arm ∈ ls, ∀ b, I b → I (collectNonArr b (altBody arm))) → I a → I (collectNonArrAlts a ls)
  | [], _, _, ha => ha | arm :: rest, a, hst, ha => by cases arm <;> exact collectNonArrAlts_inv I rest _ (fun x hx => hst x (.tail _ hx)) (hst _ (.head _) a ha)
theorem collectNonArr_mono (b : FnBody) (acc : Std.HashSet Nat) (k : Nat) (hk : k ∈ acc) : k ∈ collectNonArr acc b :=
  fnBody_ind (fun b => ∀ acc, k ∈ acc → k ∈ collectNonArr acc b) (fun b hb acc hk => by cases b with
    | vdecl _ _ e _ => refine hb _ ?_; cases e <;> first | exact hk | exact Std.HashSet.mem_insert.mpr (.inr hk)
    | jdecl _ _ _ _ => exact hb.2 _ (hb.1 acc hk) | case _ _ _ alts => exact collectNonArrAlts_inv (k ∈ ·) alts.toList _ hb (Std.HashSet.mem_insert.mpr (.inr hk))
    | ret _ | jmp _ _ | unreachable => exact hk | _ => exact hb acc hk) b acc hk
theorem collectNonArrAlts_mono (alts : List Alt) (acc : Std.HashSet Nat) (k : Nat) (hk : k ∈ acc) : k ∈ collectNonArrAlts acc alts :=
  collectNonArrAlts_inv (k ∈ ·) alts acc (fun arm _ b hb => collectNonArr_mono (altBody arm) b k hb) hk

def NonArrExpr : IR.Expr → Bool | .ctor .. | .reuse .. | .pap .. | .lit .. | .box .. | .unbox .. | .isShared .. => true | _ => false
def ProjSrcVar : IR.Expr → Option Nat | .proj _ p | .uproj _ p | .sproj _ _ p => some p.idx | _ => none
mutual
def NonArrConsistent (ρ : Nat → RcVal) : FnBody → Prop
  | .vdecl x _ e b => (NonArrExpr e = true → ∃ v, ρ x.idx = .nonArr v) ∧ (∀ p, ProjSrcVar e = some p → ∃ v, ρ p = .nonArr v) ∧ NonArrConsistent ρ b
  | .jdecl _ _ v b => NonArrConsistent ρ v ∧ NonArrConsistent ρ b | .case _ x _ alts => (∃ v, ρ x.idx = .nonArr v) ∧ NonArrConsistentAlts ρ alts.toList
  | .set _ _ _ b | .setTag _ _ b | .uset _ _ _ b | .sset _ _ _ _ _ b | .inc _ _ _ _ b | .dec _ _ _ _ b | .del _ b => NonArrConsistent ρ b
  | .ret _ | .jmp _ _ | .unreachable => True
def NonArrConsistentAlts (ρ : Nat → RcVal) : List Alt → Prop | [] => True | .ctor _ b :: rest | .default b :: rest => NonArrConsistent ρ b ∧ NonArrConsistentAlts ρ rest
end
theorem collectNonArr_sound (body : FnBody) (ρ : Nat → RcVal) (hcon : NonArrConsistent ρ body) :
    ∀ x : VarId, (collectNonArr {} body).contains x.idx = true → ∀ (h : CowHeap α) (n : Nat), h.rcInc (ρ x.idx) n = h ∧ h.rcDec (ρ x.idx) n = h := by
  have hins {a : Std.HashSet Nat} {k : Nat} (ha : ∀ m ∈ a, ∃ v, ρ m = .nonArr v) (hk : ∃ v, ρ k = .nonArr v) : ∀ m ∈ a.insert k, ∃ v, ρ m = .nonArr v := fun m hm => (Std.HashSet.mem_insert.1 hm).elim (fun h => (beq_iff_eq.mp h) ▸ hk) (ha m)
  have hmem : ∀ {ls : List Alt}, NonArrConsistentAlts ρ ls → ∀ arm ∈ ls, NonArrConsistent ρ (altBody arm) := fun {ls} => by
    induction ls with | nil => exact fun _ _ h => nomatch h | cons a t ih => intro hc x hx; have ⟨h1, h2⟩ : NonArrConsistent ρ (altBody a) ∧ NonArrConsistentAlts ρ t := (by cases a <;> exact hc); exact (List.mem_cons.1 hx).elim (· ▸ h1) (ih h2 x)
  have hgen : ∀ acc, (∀ k ∈ acc, ∃ v, ρ k = .nonArr v) → NonArrConsistent ρ body → ∀ k ∈ collectNonArr acc body, ∃ v, ρ k = .nonArr v :=
    fnBody_ind (fun b => ∀ acc, (∀ k ∈ acc, ∃ v, ρ k = .nonArr v) → NonArrConsistent ρ b → ∀ k ∈ collectNonArr acc b, ∃ v, ρ k = .nonArr v) (fun b hb acc ha hc => by cases b with
      | vdecl _ _ e _ => refine hb _ ?_ hc.2.2; cases e <;> first | exact ha | exact hins ha (hc.2.1 _ rfl) | exact hins ha (hc.1 rfl)
      | jdecl _ _ _ _ => exact hb.2 _ (hb.1 acc ha hc.1) hc.2
      | case _ _ _ alts => exact collectNonArrAlts_inv (fun s => ∀ k ∈ s, ∃ v, ρ k = .nonArr v) alts.toList _ (fun a hm s hs => hb a hm s hs (hmem hc.2 a hm)) (hins ha hc.1)
      | ret _ | jmp _ _ | unreachable => exact ha | _ => exact hb acc ha hc) body
  intro x hx h n; rcases hgen {} (fun _ hk => False.elim (Std.HashSet.not_mem_empty hk)) hcon x.idx (Std.HashSet.contains_iff_mem.1 hx) with ⟨v, hv⟩; rw [hv]; exact ⟨rfl, rfl⟩
theorem collectProjSrc_subset_collectNonArr (body : FnBody) (x p : Nat) (hsrc : (collectProjSrc {} {} body).get? x = some p) : (collectNonArr {} body).contains p = true := by
  have hgen : ∀ calls acc na, (∀ k q, acc.get? k = some q → q ∈ na) → ∀ k q, (collectProjSrc calls acc body).get? k = some q → q ∈ collectNonArr na body :=
    fnBody_ind (fun b => ∀ calls acc na, (∀ k q, acc.get? k = some q → q ∈ na) → ∀ k q, (collectProjSrc calls acc b).get? k = some q → q ∈ collectNonArr na b) (fun b hb calls acc na hinv k q hres => by cases b with
      | vdecl xv _ e _ =>
          have hins (m : Nat) : ∀ k' q', acc.get? k' = some q' → q' ∈ na.insert m := fun k' q' h => Std.HashSet.mem_insert.mpr (.inr (hinv k' q' h))
          cases e with
          | fap _ _ | ap _ _ => exact hb (calls.insert xv.idx) acc na hinv k q hres | reset _ _ => exact hb calls acc na hinv k q hres
          | proj _ src => refine hb calls _ (na.insert src.idx) (fun k' q' h => ?_) k q hres; split at h; (rw [Std.HashMap.get?_insert] at h; split at h; (cases h; exact Std.HashSet.mem_insert.mpr (.inl (beq_self_eq_true _))); exact hins src.idx k' q' h); exact hins src.idx k' q' h
          | uproj _ src | sproj _ _ src => exact hb calls acc (na.insert src.idx) (hins src.idx) k q hres | _ => exact hb calls acc (na.insert xv.idx) (hins xv.idx) k q hres
      | jdecl _ _ _ _ => exact hb.2 calls _ _ (hb.1 calls acc na hinv) k q hres
      | case _ scr _ alts =>
          have hstep : ∀ (ls : List Alt) a n, (∀ arm ∈ ls, ∀ c a' n', (∀ k q, a'.get? k = some q → q ∈ n') → ∀ k q, (collectProjSrc c a' (altBody arm)).get? k = some q → q ∈ collectNonArr n' (altBody arm)) → (∀ k q, a.get? k = some q → q ∈ n) → ∀ k q, (collectProjSrcAlts calls a ls).get? k = some q → q ∈ collectNonArrAlts n ls := fun ls => by
            induction ls with | nil => exact fun _ _ _ ha k q h => ha k q h | cons arm _ ih => intro a n hst ha; cases arm <;> exact ih _ _ (fun y hy => hst y (.tail _ hy)) (hst _ (.head _) calls a n ha)
          exact hstep alts.toList acc (na.insert scr.idx) hb (fun k' q' h => Std.HashSet.mem_insert.mpr (.inr (hinv k' q' h))) k q hres
      | ret _ | jmp _ _ | unreachable => exact hinv k q hres | _ => exact hb calls acc na hinv k q hres) body
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
  | .dec y n c bf cont, h => (Bool.or_eq_true_iff.1 h).elim (fun h1 => .dec y n c bf cont (eq_of_beq h1).symm) (.dec_skip y n c bf cont <| hasDecOf_sound p cont ·)
  | .del y cont, h => (Bool.or_eq_true_iff.1 h).elim (fun h1 => .del y cont (eq_of_beq h1).symm) (.del_skip y cont <| hasDecOf_sound p cont ·)
  | .inc y n c bf cont, h => .inc_skip y n c bf cont (hasDecOf_sound p cont h)
  | .vdecl x ty (.proj _ _) cont, h => .proj_skip x ty _ _ cont (hasDecOf_sound p cont h)
  | .vdecl x ty (.uproj _ _) cont, h => .uproj_skip x ty _ _ cont (hasDecOf_sound p cont h)
  | .vdecl x ty (.sproj _ _ _) cont, h => .sproj_skip x ty _ _ _ cont (hasDecOf_sound p cont h)
  | .vdecl _ _ (.ctor ..) _, h | .vdecl _ _ (.reset ..) _, h | .vdecl _ _ (.reuse ..) _, h | .vdecl _ _ (.fap ..) _, h | .vdecl _ _ (.pap ..) _, h | .vdecl _ _ (.ap ..) _, h | .vdecl _ _ (.box ..) _, h | .vdecl _ _ (.unbox ..) _, h | .vdecl _ _ (.lit ..) _, h | .vdecl _ _ (.isShared ..) _, h | .jdecl .., h | .case .., h | .set .., h | .setTag .., h | .uset .., h | .sset .., h | .ret _, h | .jmp .., h | .unreachable, h => nomatch h
theorem projRefTransfer_cowHeap_equiv (h : CowHeap α) (id n : Nat) (hn : n ≥ 1) : ∀ k : Nat, (h.jsTransferInc id n).get k = ((h.rcInc (.arr id) n).rcDec (.arr id) 1).get k := fun k => by
  dsimp only [CowHeap.jsTransferInc, CowHeap.rcInc, CowHeap.rcDec]; split
  · obtain rfl : n = 1 := by have := beq_iff_eq.mp ‹_›; omega
    by_cases hkid : k = id <;> simp [CowHeap.get, CowHeap.set, hkid]
  · by_cases hkid : k = id; (subst hkid; simp only [CowHeap.get_set_self]; rcases h.get k with ⟨el, rc, mk⟩; simp [show rc + (n - 1) = rc + n - 1 by omega]); simp only [CowHeap.get_set_ne _ _ hkid]

mutual
def stmtsTailSafe (allowSelf : Bool) : List JsStmt → Prop | [] => True | s :: ss => stmtTailSafe allowSelf s ∧ stmtsTailSafe allowSelf ss
def stmtTailSafe (allowSelf : Bool) : JsStmt → Prop | .tailContinue .. => allowSelf = true | .labeledBlock _ body => stmtsTailSafe allowSelf body | .constArrow _ _ body => stmtsTailSafe false body | .switchStmt _ arms => armsTailSafe allowSelf arms | _ => True
def armsTailSafe (allowSelf : Bool) : List JsSwitchArm → Prop | [] => True | .caseArm _ b :: rest | .defaultArm b :: rest => stmtsTailSafe allowSelf b ∧ armsTailSafe allowSelf rest
end
private theorem stmtsTailSafe_append {a : Bool} : ∀ {s₁ s₂ : List JsStmt}, stmtsTailSafe a s₁ → stmtsTailSafe a s₂ → stmtsTailSafe a (s₁ ++ s₂)
  | [], _, _, h2 => h2 | _ :: _, _, ⟨h1, hr⟩, h2 => ⟨h1, stmtsTailSafe_append hr h2⟩
private theorem noTailCont_aux (f : Name) (b : FnBody) :
    ∀ (c : Ctx) (active : Bool), (c.selfFn = none ∨ c.selfFn = some f) → hasSelfTailAux f true active b = false → stmtsTailSafe (!active) (lowerBody c b) :=
  fnBody_ind (fun b => ∀ c active, (c.selfFn = none ∨ c.selfFn = some f) → hasSelfTailAux f true active b = false → stmtsTailSafe (!active) (lowerBody c b)) (fun b hb c active hself h => by
    cases b with
    | vdecl x _ e cont => cases e with
        | fap g _ => cases active with
            | false => simp only [hasSelfTailAux, Bool.false_and, Bool.false_or] at h; dsimp only [lowerBody]; split; (split <;> exact ⟨by first | rfl | trivial, trivial⟩); exact ⟨trivial, hb c false hself h⟩
            | true => have ⟨h1, h2⟩ := Bool.or_eq_false_iff.1 h
                      have hns : (c.selfFn == some g && retsVar x cont) = false := by cases hfg : c.selfFn == some g; rfl; cases hr : retsVar x cont; rfl; rcases hself with h0 | h0; (rw [h0] at hfg; cases hfg); rw [h0] at hfg; cases Option.some.inj (eq_of_beq hfg); simp [hr] at h1
                      dsimp only [lowerBody]; rw [hns]; exact ⟨trivial, hb c true hself h2⟩
        | _ => exact ⟨trivial, hb c active hself h⟩
    | jdecl j xs val _ =>
        have ⟨h1, h2⟩ := Bool.or_eq_false_iff.1 h; dsimp only [lowerBody]; cases hj : hasJmpTo j val
        · rw [hj, Bool.or_false] at h1; have hs1 := hb.2 { c with inlineJps := c.inlineJps.insert j.idx xs } active hself h2; have hs2 := hb.1 c active hself h1
          cases xs.isEmpty <;> exact stmtsTailSafe_append (stmtsTailSafe_append (stmtsTailSafe_append (by first | trivial | exact ⟨trivial, trivial⟩) ⟨hs1, trivial⟩) (by first | trivial | exact ⟨trivial, trivial⟩)) hs2
        · rw [hj, Bool.or_true] at h1; exact ⟨hb.1 c true hself h1, hb.2 c active hself h2⟩
    | case _ _ _ alts =>
        have go : ∀ ls : List Alt, hasSelfTailAltsAux f true active ls = false → (∀ arm ∈ ls, hasSelfTailAux f true active (altBody arm) = false → stmtsTailSafe (!active) (lowerBody c (altBody arm))) → armsTailSafe (!active) (lowerAlts c ls) := fun ls => by
          induction ls with | nil => exact fun _ _ => trivial | cons arm _ ih => intro ha hls; cases arm <;> (have ⟨h1, h2⟩ := Bool.or_eq_false_iff.1 ha; exact ⟨hls _ (.head _) h1, ih h2 fun x hx => hls x (.tail _ hx)⟩)
        exact ⟨go alts.toList h fun arm harm => hb arm harm c active hself, trivial⟩
    | inc _ _ _ _ _ | dec _ _ _ _ _ | del _ _ => dsimp only [lowerBody]; repeat (split <;> first | exact hb c active hself h | exact ⟨trivial, hb c active hself h⟩ | skip)
    | set _ _ _ _ | setTag _ _ _ | uset _ _ _ _ | sset _ _ _ _ _ _ => exact ⟨trivial, hb c active hself h⟩ | ret _ | unreachable => exact ⟨trivial, trivial⟩ | jmp j _ => dsimp only [lowerBody]; cases c.inlineJps.get? j.idx <;> exact ⟨trivial, trivial⟩) b
theorem noTailCont_of_hasJpSelfTail_false (f : Name) (b : FnBody) (c : Ctx) (hself : c.selfFn = none ∨ c.selfFn = some f) :
    (hasSelfTailAux f true true b = false → stmtsTailSafe false (lowerBody c b)) ∧ (hasSelfTailAux f true false b = false → stmtsTailSafe true (lowerBody c b)) :=
  ⟨noTailCont_aux f b c true hself, noTailCont_aux f b c false hself⟩

end Js.Proofs
