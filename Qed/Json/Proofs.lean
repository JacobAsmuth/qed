import Qed.Json.Basic

namespace Qed

mutual
  theorem parseVal_depth_le :
      ∀ (fuel budget : Nat) (cs : List Char) (j : Json) (r : List Char),
        parseVal fuel budget cs = .ok (j, r) → j.depth ≤ budget
    | 0,        _,      _,  _, _, h => by simp [parseVal] at h
    | fuel + 1, budget, cs, j, r, h => by
        simp only [parseVal] at h
        repeat' split at h
        all_goals first
          | contradiction
          | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
             obtain ⟨rfl, rfl⟩ := h
             first
               | (simp only [Json.depth, Json.maxArr, Json.maxObj]; omega)
               | (simp only [Json.depth]
                  have hb := Json.maxArr_le_iff.mpr
                    (fun e he => parseElems_depth_le _ _ _ _ _ (by assumption) e he)
                  omega)
               | (simp only [Json.depth]
                  have hb := Json.maxObj_le_iff.mpr
                    (fun kv hkv => parseMembers_depth_le _ _ _ _ _ (by assumption) kv hkv)
                  omega))
  theorem parseElems_depth_le :
      ∀ (fuel budget : Nat) (cs : List Char) (es : List Json) (r : List Char),
        parseElems fuel budget cs = .ok (es, r) → ∀ e ∈ es, e.depth ≤ budget
    | 0,        _,      _,  _,  _, h => by simp [parseElems] at h
    | fuel + 1, budget, cs, es, r, h => by
        simp only [parseElems] at h
        repeat' split at h
        all_goals first
          | contradiction
          | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
             obtain ⟨rfl, rfl⟩ := h
             intro e he
             first
               | exact absurd he (List.not_mem_nil)
               | (cases he with
                  | head => exact parseVal_depth_le _ _ _ _ _ (by assumption)
                  | tail _ he' => first
                      | exact parseElems_depth_le _ _ _ _ _ (by assumption) _ he'
                      | exact absurd he' (List.not_mem_nil)))
  theorem parseMembers_depth_le :
      ∀ (fuel budget : Nat) (cs : List Char) (ms : List (String × Json)) (r : List Char),
        parseMembers fuel budget cs = .ok (ms, r) → ∀ kv ∈ ms, kv.2.depth ≤ budget
    | 0,        _,      _,  _,  _, h => by simp [parseMembers] at h
    | fuel + 1, budget, cs, ms, r, h => by
        simp only [parseMembers] at h
        repeat' split at h
        all_goals first
          | contradiction
          | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
             obtain ⟨rfl, rfl⟩ := h
             intro kv hkv
             first
               | exact absurd hkv (List.not_mem_nil)
               | (cases hkv with
                  | head => exact parseVal_depth_le _ _ _ _ _ (by assumption)
                  | tail _ hkv' => first
                      | exact parseMembers_depth_le _ _ _ _ _ (by assumption) _ hkv'
                      | exact absurd hkv' (List.not_mem_nil)))
end

theorem parse_depth_le (s : String) (maxDepth : Nat) (j : Json) :
    parse s maxDepth = .ok j → j.depth ≤ maxDepth := by
  intro h
  simp only [parse] at h
  split at h
  · simp at h
  · rename_i j0 r heq
    split at h
    · cases h; exact parseVal_depth_le _ maxDepth _ _ _ heq
    · contradiction

theorem digit_spec (k : Nat) (h : k < 10) :
    (Char.ofNat ('0'.toNat + k)).toNat - '0'.toNat = k
    ∧ isDigit (Char.ofNat ('0'.toNat + k)) = true :=
  match k, h with
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | _ + 10, h => absurd h (by omega)

theorem natDigitsAux_append (n : Nat) : ∀ acc : List Char,
    natDigitsAux n acc = natDigitsAux n [] ++ acc := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro acc
    rw [natDigitsAux.eq_def (acc := acc), natDigitsAux.eq_def (acc := [])]
    by_cases h : n < 10
    · simp [h]
    · simp only [if_neg h]
      rw [ih (n / 10) (by omega), ih (n / 10) (by omega) [_]]
      simp

theorem natDigits_unfold (n : Nat) :
    natDigitsAux n [] = (if n < 10 then [] else natDigitsAux (n / 10) [])
                        ++ [Char.ofNat ('0'.toNat + n % 10)] := by
  rw [natDigitsAux.eq_def]
  by_cases h : n < 10
  · simp [h]
  · simp only [if_neg h]
    exact natDigitsAux_append (n / 10) [_]

theorem natDigits_ne_nil (n : Nat) : natDigitsAux n [] ≠ [] := by
  rw [natDigits_unfold]; simp

theorem natDigits_digit (n : Nat) : ∀ c ∈ natDigitsAux n [], isDigit c = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits_unfold]
    intro c hc
    rw [List.mem_append] at hc
    cases hc with
    | inr h =>
        rw [List.mem_singleton] at h; subst h
        exact (digit_spec _ (Nat.mod_lt _ (by omega))).2
    | inl h =>
        by_cases h10 : n < 10
        · simp [h10] at h
        · exact ih (n / 10) (by omega) c (by simpa [h10] using h)

theorem foldl_natDigits (n : Nat) :
    (natDigitsAux n []).foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [natDigits_unfold, List.foldl_append]
    by_cases h : n < 10
    · simp only [if_pos h, List.foldl_nil, List.foldl_cons]
      rw [(digit_spec _ (Nat.mod_lt _ (by omega))).1]
      omega
    · simp only [if_neg h, List.foldl_cons, List.foldl_nil]
      rw [ih (n / 10) (by omega), (digit_spec _ (Nat.mod_lt _ (by omega))).1]
      omega

theorem digitsToInt_natDigits (n : Nat) : digitsToInt (natDigitsAux n []) = (n : Int) := by
  rw [digitsToInt, foldl_natDigits]

def numDelim : List Char → Bool
  | []     => true
  | c :: _ => !(isDigit c || c == '.' || c == 'e' || c == 'E')

theorem takeDigits_cons_not {c : Char} {t : List Char} (h : isDigit c = false) :
    takeDigits (c :: t) = ([], c :: t) := by
  simp [takeDigits, h]

theorem takeDigits_stop {cs : List Char} (h : numDelim cs = true) :
    takeDigits cs = ([], cs) := by
  match cs with
  | [] => rfl
  | c :: t =>
      simp only [numDelim, Bool.not_eq_true', Bool.or_eq_false_iff] at h
      exact takeDigits_cons_not h.1.1.1

theorem takeDigits_append (ds : List Char) (hds : ∀ c ∈ ds, isDigit c = true)
    (rest : List Char) (hrest : takeDigits rest = ([], rest)) :
    takeDigits (ds ++ rest) = (ds, rest) := by
  induction ds with
  | nil => simpa using hrest
  | cons c t ih =>
      have hc : isDigit c = true := hds c (by simp)
      have ht := ih (fun x hx => hds x (by simp [hx]))
      simp [takeDigits, hc, ht]

theorem natDigits_cons (m : Nat) :
    ∃ c t, natDigitsAux m [] = c :: t ∧ isDigit c = true := by
  match h : natDigitsAux m [] with
  | [] => exact absurd h (natDigits_ne_nil m)
  | c :: t => exact ⟨c, t, rfl, natDigits_digit m c (h ▸ List.mem_cons_self ..)⟩

theorem digit_not_sign {c : Char} (h : isDigit c = true) : c ≠ '-' ∧ c ≠ '+' :=
  ⟨fun e => by subst e; exact absurd h (by decide),
   fun e => by subst e; exact absurd h (by decide)⟩

theorem numDelim_head {c : Char} {t : List Char} (h : numDelim (c :: t) = true) :
    isDigit c = false ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' := by
  simp only [numDelim, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem parseNum_render (n : JsonNumber) (rest : List Char) (hr : numDelim rest = true) :
    parseNum (Json.renderNumL n ++ rest) = .ok (n, rest) := by
  obtain ⟨m, ex⟩ := n
  by_cases hm : m < 0 <;> by_cases hex : ex = 0
  · have harg : Json.renderNumL ⟨m, ex⟩ ++ rest = '-' :: (natDigitsAux m.natAbs [] ++ rest) := by
      simp [Json.renderNumL, intCharsL, hm, hex]
    rw [harg]
    simp only [parseNum]
    rw [takeDigits_append _ (natDigits_digit _) _ (takeDigits_stop hr)]
    rw [if_neg (by simp [natDigits_ne_nil])]
    cases rest with
    | nil => simp [digitsToInt_natDigits, hex]; omega
    | cons c t =>
        obtain ⟨hd, hdot, he, hE⟩ := numDelim_head hr
        simp [hdot, he, hE, digitsToInt_natDigits, hex]
        omega
  · by_cases hexn : ex < 0
    · have harg : Json.renderNumL ⟨m, ex⟩ ++ rest
          = '-' :: (natDigitsAux m.natAbs []
              ++ ('e' :: ('-' :: (natDigitsAux ex.natAbs [] ++ rest)))) := by
        simp [Json.renderNumL, intCharsL, hm, hex, hexn]
      rw [harg]
      simp only [parseNum]
      rw [takeDigits_append _ (natDigits_digit _) _ (takeDigits_cons_not (by decide))]
      rw [if_neg (by simp [natDigits_ne_nil])]
      have hte : takeDigits (natDigitsAux ex.natAbs [] ++ rest)
          = (natDigitsAux ex.natAbs [], rest) :=
        takeDigits_append _ (natDigits_digit _) _ (takeDigits_stop hr)
      simp [hte, digitsToInt_natDigits]
      omega
    · obtain ⟨c1, t1, hex0, hc1⟩ := natDigits_cons ex.natAbs
      obtain ⟨hns, hps⟩ := digit_not_sign hc1
      have harg : Json.renderNumL ⟨m, ex⟩ ++ rest
          = '-' :: (natDigitsAux m.natAbs []
              ++ ('e' :: (natDigitsAux ex.natAbs [] ++ rest))) := by
        simp [Json.renderNumL, intCharsL, hm, hex, hexn]
      rw [harg]
      simp only [parseNum]
      rw [takeDigits_append _ (natDigits_digit _) _ (takeDigits_cons_not (by decide))]
      rw [if_neg (by simp [natDigits_ne_nil])]
      rw [hex0]
      simp only [List.cons_append]
      have htd : takeDigits (c1 :: (t1 ++ rest)) = (c1 :: t1, rest) := by
        have := takeDigits_append _ (natDigits_digit ex.natAbs) _ (takeDigits_stop hr)
        rwa [hex0, List.cons_append] at this
      have hdi : digitsToInt (c1 :: t1) = (ex.natAbs : Int) := by
        have := digitsToInt_natDigits ex.natAbs
        rwa [hex0] at this
      simp [hns, hps, htd, hdi, digitsToInt_natDigits]
      omega
  · obtain ⟨c0, t0, hm0, hc0⟩ := natDigits_cons m.natAbs
    obtain ⟨hns, hps⟩ := digit_not_sign hc0
    have harg : Json.renderNumL ⟨m, ex⟩ ++ rest = c0 :: (t0 ++ rest) := by
      simp [Json.renderNumL, intCharsL, hm, hex, hm0]
    rw [harg]
    simp only [parseNum]
    have htd : takeDigits (c0 :: (t0 ++ rest)) = (c0 :: t0, rest) := by
      have := takeDigits_append _ (natDigits_digit m.natAbs) _ (takeDigits_stop hr)
      rwa [hm0, List.cons_append] at this
    have hdi : digitsToInt (c0 :: t0) = (m.natAbs : Int) := by
      have := digitsToInt_natDigits m.natAbs
      rwa [hm0] at this
    cases rest with
    | nil =>
        rw [List.append_nil] at htd
        simp [hns, htd, hdi, hex]
        omega
    | cons c t =>
        obtain ⟨hd, hdot, he, hE⟩ := numDelim_head hr
        simp [hns, htd, hdi, hdot, he, hE, hex]
        omega
  · obtain ⟨c0, t0, hm0, hc0⟩ := natDigits_cons m.natAbs
    obtain ⟨hns0, hps0⟩ := digit_not_sign hc0
    by_cases hexn : ex < 0
    · have harg : Json.renderNumL ⟨m, ex⟩ ++ rest
          = c0 :: (t0 ++ ('e' :: ('-' :: (natDigitsAux ex.natAbs [] ++ rest)))) := by
        simp [Json.renderNumL, intCharsL, hm, hex, hexn, hm0]
      rw [harg]
      simp only [parseNum]
      have htd : takeDigits (c0 :: (t0 ++ ('e' :: ('-' :: (natDigitsAux ex.natAbs [] ++ rest)))))
          = (c0 :: t0, 'e' :: ('-' :: (natDigitsAux ex.natAbs [] ++ rest))) := by
        have := takeDigits_append _ (natDigits_digit m.natAbs)
          ('e' :: ('-' :: (natDigitsAux ex.natAbs [] ++ rest))) (takeDigits_cons_not (by decide))
        rwa [hm0, List.cons_append] at this
      have hdi : digitsToInt (c0 :: t0) = (m.natAbs : Int) := by
        have := digitsToInt_natDigits m.natAbs
        rwa [hm0] at this
      have hte : takeDigits (natDigitsAux ex.natAbs [] ++ rest)
          = (natDigitsAux ex.natAbs [], rest) :=
        takeDigits_append _ (natDigits_digit _) _ (takeDigits_stop hr)
      simp [hns0, htd, hdi, hte, digitsToInt_natDigits]
      omega
    · obtain ⟨c1, t1, hex0, hc1⟩ := natDigits_cons ex.natAbs
      obtain ⟨hns1, hps1⟩ := digit_not_sign hc1
      have harg : Json.renderNumL ⟨m, ex⟩ ++ rest
          = c0 :: (t0 ++ ('e' :: (c1 :: (t1 ++ rest)))) := by
        simp [Json.renderNumL, intCharsL, hm, hex, hexn, hm0, hex0]
      rw [harg]
      simp only [parseNum]
      have htd : takeDigits (c0 :: (t0 ++ ('e' :: (c1 :: (t1 ++ rest)))))
          = (c0 :: t0, 'e' :: (c1 :: (t1 ++ rest))) := by
        have := takeDigits_append _ (natDigits_digit m.natAbs)
          ('e' :: (c1 :: (t1 ++ rest))) (takeDigits_cons_not (by decide))
        rwa [hm0, List.cons_append] at this
      have htd1 : takeDigits (c1 :: (t1 ++ rest)) = (c1 :: t1, rest) := by
        have := takeDigits_append _ (natDigits_digit ex.natAbs) _ (takeDigits_stop hr)
        rwa [hex0, List.cons_append] at this
      have hdi : digitsToInt (c0 :: t0) = (m.natAbs : Int) := by
        have := digitsToInt_natDigits m.natAbs
        rwa [hm0] at this
      have hdi1 : digitsToInt (c1 :: t1) = (ex.natAbs : Int) := by
        have := digitsToInt_natDigits ex.natAbs
        rwa [hex0] at this
      simp [hns0, hns1, hps1, htd, htd1, hdi, hdi1]
      omega

theorem hexVal_toHexDigit (d : Nat) (h : d < 16) : hexVal (toHexDigit d) = some d :=
  match d, h with
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | 10, _ => by decide
  | 11, _ => by decide
  | 12, _ => by decide
  | 13, _ => by decide
  | 14, _ => by decide
  | 15, _ => by decide
  | _ + 16, h => absurd h (by omega)

theorem parseStrAux_escape (c : Char) (acc rest : List Char) :
    parseStrAux acc (escapeCharL c ++ rest) = parseStrAux (c :: acc) rest := by
  simp only [escapeCharL]
  split
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rename_i cv h1 h2 h3 h4 h5
    by_cases hlt : c.toNat < 0x20
    · simp only [if_pos hlt, List.cons_append]
      have h16 : ∀ k : Nat, k % 16 < 16 := fun k => Nat.mod_lt _ (by omega)
      have harith : ((c.toNat / 4096 % 16 * 16 + c.toNat / 256 % 16) * 16 + c.toNat / 16 % 16) * 16
              + c.toNat % 16 = c.toNat := by omega
      simp [parseStrAux, hex4, hexVal_toHexDigit _ (h16 _), harith, Char.ofNat_toNat]
    · simp only [if_neg hlt, List.cons_append, List.nil_append]
      rw [parseStrAux.eq_def]
      have h2' : c ≠ '\\' := h2
      simp [h2']

theorem parseStrAux_flatMap (cs : List Char) : ∀ (acc rest : List Char),
    parseStrAux acc (cs.flatMap escapeCharL ++ '"' :: rest)
      = .ok (String.ofList (acc.reverse ++ cs), rest) := by
  induction cs with
  | nil => intro acc rest; simp [parseStrAux]
  | cons c cs ih =>
      intro acc rest
      rw [List.flatMap_cons, List.append_assoc, parseStrAux_escape, ih]
      simp

theorem parseStr_render (s : String) (rest : List Char) :
    parseStr (s.toList.flatMap escapeCharL ++ '"' :: rest) = .ok (s, rest) := by
  rw [parseStr, parseStrAux_flatMap]
  simp [String.ofList_toList]

theorem numDelim_cons {c : Char} {t : List Char}
    (h : (isDigit c || c == '.' || c == 'e' || c == 'E') = false) :
    numDelim (c :: t) = true := by
  simp [numDelim, h]

theorem digit_not_special {c : Char} (h : isDigit c = true) :
    isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> (intro rfl; exact absurd h (by decide))
  · intro rfl; exact absurd h (by decide)
  · intro rfl; exact absurd h (by decide)

theorem digit_not_starts {c : Char} (h : isDigit c = true) :
    c ≠ 'n' ∧ c ≠ 't' ∧ c ≠ 'f' ∧ c ≠ '"' ∧ c ≠ '[' ∧ c ≠ '{' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro rfl; exact absurd h (by decide))

theorem renderL_head (j : Json) :
    ∃ c t, Json.renderL j = c :: t ∧ isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases j with
  | null => exact ⟨'n', _, rfl, by decide, by decide, by decide⟩
  | bool b => cases b with
      | true => exact ⟨'t', _, rfl, by decide, by decide, by decide⟩
      | false => exact ⟨'f', _, rfl, by decide, by decide, by decide⟩
  | str s => exact ⟨'"', _, rfl, by decide, by decide, by decide⟩
  | arr es => exact ⟨'[', _, rfl, by decide, by decide, by decide⟩
  | obj ms => exact ⟨'{', _, rfl, by decide, by decide, by decide⟩
  | num n =>
      by_cases hm : n.mantissa < 0
      · refine ⟨'-', natDigitsAux n.mantissa.natAbs []
            ++ (if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent),
            ?_, by decide, by decide, by decide⟩
        simp [Json.renderL, Json.renderNumL, intCharsL, hm]
      · obtain ⟨c0, t0, h0, hc0⟩ := natDigits_cons n.mantissa.natAbs
        obtain ⟨hws, hbr, hbc⟩ := digit_not_special hc0
        refine ⟨c0, t0 ++ (if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent),
                ?_, hws, hbr, hbc⟩
        simp [Json.renderL, Json.renderNumL, intCharsL, hm, h0]

theorem skipWs_renderL (j : Json) (x : List Char) :
    skipWs (Json.renderL j ++ x) = Json.renderL j ++ x := by
  obtain ⟨c, t, hren, hcws, _, _⟩ := renderL_head j
  rw [hren, List.cons_append]
  simp [skipWs, hcws]

theorem skipWs_renderElemsL (e : Json) (es : List Json) (x : List Char) :
    skipWs (Json.renderElemsL (e :: es) ++ x) = Json.renderElemsL (e :: es) ++ x := by
  simp only [Json.renderElemsL, List.append_assoc]
  exact skipWs_renderL e _

theorem parseVal_to_parseNum (f b : Nat) (c0 : Char) (t : List Char)
    (hws : isWs c0 = false)
    (hn : c0 ≠ 'n') (ht : c0 ≠ 't') (hf : c0 ≠ 'f') (hq : c0 ≠ '"')
    (hbk : c0 ≠ '[') (hbc : c0 ≠ '{') (hg : (c0 == '-' || isDigit c0) = true) :
    parseVal (f + 1) b (c0 :: t)
      = (match parseNum (c0 :: t) with
         | .ok (n, r') => .ok (.num n, r')
         | .error e => .error e) := by
  simp only [parseVal]
  rw [show skipWs (c0 :: t) = c0 :: t from by simp [skipWs, hws]]
  simp [hn, ht, hf, hg]
  rcases parseNum (c0 :: t) with _ | ⟨n, r'⟩ <;> rfl

theorem parseVal_num (n : JsonNumber) (f b : Nat) (rest : List Char)
    (hr : numDelim rest = true) :
    parseVal (f + 1) b (Json.renderNumL n ++ rest) = .ok (.num n, rest) := by
  by_cases hm : n.mantissa < 0
  · have harg : Json.renderNumL n ++ rest
        = '-' :: (natDigitsAux n.mantissa.natAbs []
            ++ ((if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent) ++ rest)) := by
      simp [Json.renderNumL, intCharsL, hm]
    rw [harg, parseVal_to_parseNum f b '-' _ (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), ← harg, parseNum_render n rest hr]
  · obtain ⟨c0, t0, h0, hc0⟩ := natDigits_cons n.mantissa.natAbs
    obtain ⟨hn, ht, hf', hq, hbk, hbc⟩ := digit_not_starts hc0
    obtain ⟨hws, _, _⟩ := digit_not_special hc0
    obtain ⟨hminus, _⟩ := digit_not_sign hc0
    have harg : Json.renderNumL n ++ rest
        = c0 :: (t0 ++ ((if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent) ++ rest)) := by
      simp [Json.renderNumL, intCharsL, hm, h0]
    rw [harg, parseVal_to_parseNum f b c0 _ hws hn ht hf' hq hbk hbc (by simp [hc0]),
        ← harg, parseNum_render n rest hr]

theorem renderMembersL_cons (k : String) (v : Json) (ms : List (String × Json)) :
    Json.renderMembersL ((k, v) :: ms)
      = Json.renderStrL k ++ ':' :: (Json.renderL v ++ Json.renderMemberSep ms) := rfl

theorem renderMemberSep_cons (k : String) (v : Json) (ms : List (String × Json)) :
    Json.renderMemberSep ((k, v) :: ms) = ',' :: Json.renderMembersL ((k, v) :: ms) := rfl

theorem skipWs_renderMembersL (k : String) (v : Json) (ms : List (String × Json)) (x : List Char) :
    skipWs (Json.renderMembersL ((k, v) :: ms) ++ x)
      = Json.renderMembersL ((k, v) :: ms) ++ x := by
  simp only [renderMembersL_cons, Json.renderStrL, List.cons_append, List.append_assoc]
  simp [skipWs, isWs]

theorem parseVal_arr (e : Json) (es : List Json) (f b : Nat) (rest : List Char) :
    parseVal (f + 1) (b + 1) ('[' :: (Json.renderElemsL (e :: es) ++ ']' :: rest))
      = (match parseElems f b (Json.renderElemsL (e :: es) ++ ']' :: rest) with
         | .ok (vs, r') => .ok (Json.arr vs, r')
         | .error msg   => .error msg) := by
  obtain ⟨c, t, hren, hcws, hcbr, _⟩ := renderL_head e
  have hcons : Json.renderElemsL (e :: es) ++ ']' :: rest
             = c :: (t ++ Json.renderElemSep es ++ ']' :: rest) := by
    simp only [Json.renderElemsL, hren, List.cons_append, List.append_assoc]
  have step : parseVal (f + 1) (b + 1) ('[' :: (Json.renderElemsL (e :: es) ++ ']' :: rest))
            = (match skipWs (Json.renderElemsL (e :: es) ++ ']' :: rest) with
               | []      => .error "unexpected end of input"
               | c :: r' => if c = ']' then .ok (Json.arr [], r')
                            else (match parseElems f b (c :: r') with
                                  | .ok (es', r'') => .ok (Json.arr es', r'')
                                  | .error e       => .error e)) := rfl
  rw [step, skipWs_renderElemsL e es (']' :: rest), hcons]
  simp only [if_neg hcbr]

theorem parseVal_obj (k : String) (v : Json) (ms : List (String × Json))
    (f b : Nat) (rest : List Char) :
    parseVal (f + 1) (b + 1) ('{' :: (Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest))
      = (match parseMembers f b (Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest) with
         | .ok (ms', r') => .ok (Json.obj ms', r')
         | .error msg   => .error msg) := by
  have hcons : Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest
      = '"' :: (k.toList.flatMap escapeCharL
          ++ ('"' :: (':' :: (Json.renderL v ++ (Json.renderMemberSep ms ++ '}' :: rest))))) := by
    simp [renderMembersL_cons, Json.renderStrL]
  have step : parseVal (f + 1) (b + 1) ('{' :: (Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest))
      = (match skipWs (Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest) with
         | []      => .error "unexpected end of input"
         | c :: r' => if c = '}' then .ok (Json.obj [], r')
                      else (match parseMembers f b (c :: r') with
                            | .ok (ms', r'') => .ok (Json.obj ms', r'')
                            | .error e       => .error e)) := rfl
  rw [step, skipWs_renderMembersL, hcons]
  simp only [if_neg (by decide : ¬('"' = '}'))]

theorem parseMembers_step (f budget : Nat) (cs : List Char) :
    parseMembers (f + 1) budget cs
      = (match skipWs cs with
         | '"' :: r =>
             match parseStr r with
             | .error e => .error e
             | .ok (key, r1) =>
                 match skipWs r1 with
                 | ':' :: r2 =>
                     match parseVal f budget (skipWs r2) with
                     | .error e => .error e
                     | .ok (v, r3) =>
                         match skipWs r3 with
                         | ',' :: r4 =>
                             match parseMembers f budget (skipWs r4) with
                             | .ok (ms, r5) => .ok ((key, v) :: ms, r5)
                             | .error e     => .error e
                         | '}' :: r4 => .ok ([(key, v)], r4)
                         | _         => .error "expected ',' or '}'"
                 | _ => .error "expected ':'"
         | _ => .error "expected string key") := rfl

theorem parseElems_step (f budget : Nat) (cs : List Char) :
    parseElems (f + 1) budget cs
      = (match parseVal f budget cs with
         | .error msg => .error msg
         | .ok (v, r) =>
             match skipWs r with
             | ',' :: r' =>
                 (match parseElems f budget (skipWs r') with
                  | .ok (vs, r'') => .ok (v :: vs, r'')
                  | .error e      => .error e)
             | ']' :: r' => .ok ([v], r')
             | _         => .error "expected ',' or ']'") := rfl

mutual
  theorem rt_val : ∀ (j : Json) (budget fuel : Nat) (rest : List Char),
      j.depth ≤ budget → (Json.renderL j).length < fuel → numDelim rest = true →
      parseVal fuel budget (Json.renderL j ++ rest) = .ok (j, rest)
    | .null, budget, fuel, rest, _, hf, _ => by
        cases fuel with
        | zero => simp [Json.renderL] at hf
        | succ f => simp [Json.renderL, parseVal, skipWs, isWs]
    | .bool b, budget, fuel, rest, _, hf, _ => by
        cases fuel with
        | zero => cases b <;> simp [Json.renderL] at hf
        | succ f => cases b <;> simp [Json.renderL, parseVal, skipWs, isWs]
    | .num n, budget, fuel, rest, _, hf, hr => by
        cases fuel with
        | zero => exact absurd hf (Nat.not_lt_zero _)
        | succ f => exact parseVal_num n f budget rest hr
    | .str s, budget, fuel, rest, _, hf, _ => by
        cases fuel with
        | zero => exact absurd hf (Nat.not_lt_zero _)
        | succ f =>
            have harg : Json.renderL (.str s) ++ rest
                = '"' :: (s.toList.flatMap escapeCharL ++ ('"' :: rest)) := by
              simp [Json.renderL, Json.renderStrL]
            rw [harg]
            simp [parseVal, skipWs, isWs, parseStr_render]
    | .arr [], budget, fuel, rest, hd, hf, _ => by
        cases fuel with
        | zero => simp [Json.renderL, Json.renderElemsL] at hf
        | succ f => cases budget with
          | zero => simp [Json.depth, Json.maxArr] at hd
          | succ b => simp [Json.renderL, Json.renderElemsL, parseVal, skipWs, isWs]
    | .arr (e :: es), budget, fuel, rest, hd, hf, _ => by
        cases budget with
        | zero => simp [Json.depth] at hd
        | succ b =>
            simp only [Json.depth] at hd
            have hdall : ∀ x ∈ (e :: es), Json.depth x ≤ b :=
              Json.maxArr_le_iff.mp (by omega)
            cases fuel with
            | zero => simp [Json.renderL, Json.renderElemsL] at hf
            | succ f =>
                have hfe : (Json.renderElemsL (e :: es)).length + 1 < f := by
                  simp only [Json.renderL, List.length_cons, List.length_append] at hf; omega
                have key := rt_elems e es b f rest hdall hfe
                have harr : Json.renderL (Json.arr (e :: es)) ++ rest
                          = '[' :: (Json.renderElemsL (e :: es) ++ ']' :: rest) := by
                  simp [Json.renderL]
                rw [harr, parseVal_arr e es f b rest, key]
    | .obj [], budget, fuel, rest, hd, hf, _ => by
        cases fuel with
        | zero => simp [Json.renderL, Json.renderMembersL] at hf
        | succ f => cases budget with
          | zero => simp [Json.depth, Json.maxObj] at hd
          | succ b => simp [Json.renderL, Json.renderMembersL, parseVal, skipWs, isWs]
    | .obj ((k, v) :: ms), budget, fuel, rest, hd, hf, _ => by
        cases budget with
        | zero => simp [Json.depth] at hd
        | succ b =>
            simp only [Json.depth] at hd
            have hdall : ∀ x ∈ ((k, v) :: ms), Json.depth x.2 ≤ b :=
              Json.maxObj_le_iff.mp (by omega)
            cases fuel with
            | zero => simp [Json.renderL, Json.renderMembersL] at hf
            | succ f =>
                have hfm : (Json.renderMembersL ((k, v) :: ms)).length + 1 < f := by
                  simp only [Json.renderL, List.length_cons, List.length_append] at hf; omega
                have key := rt_members (k, v) ms b f rest hdall hfm
                have hobj : Json.renderL (Json.obj ((k, v) :: ms)) ++ rest
                          = '{' :: (Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest) := by
                  simp [Json.renderL]
                rw [hobj, parseVal_obj k v ms f b rest, key]
  termination_by j _ _ _ _ _ _ => sizeOf j
  theorem rt_elems : ∀ (e : Json) (es : List Json),
      ∀ (budget fuel : Nat) (rest : List Char),
      (∀ x ∈ e :: es, Json.depth x ≤ budget) →
      (Json.renderElemsL (e :: es)).length + 1 < fuel →
      parseElems fuel budget (Json.renderElemsL (e :: es) ++ ']' :: rest) = .ok (e :: es, rest)
    | e, [], budget, fuel, rest, hd, hf => by
        cases fuel with
        | zero => omega
        | succ f =>
            have hfe : (Json.renderL e).length < f := by
              simp only [Json.renderElemsL, Json.renderElemSep, List.append_nil] at hf; omega
            have hv := rt_val e budget f (']' :: rest) (hd e (by simp)) hfe
              (numDelim_cons (by decide))
            have harg : Json.renderElemsL (e :: []) ++ ']' :: rest = Json.renderL e ++ ']' :: rest := by
              simp [Json.renderElemsL, Json.renderElemSep]
            rw [harg, parseElems_step, hv]
            simp [skipWs, isWs]
    | e, x :: xs, budget, fuel, rest, hd, hf => by
        cases fuel with
        | zero => omega
        | succ f =>
            have hdtail : ∀ y ∈ x :: xs, Json.depth y ≤ budget := fun y hy => hd y (by simp [hy])
            simp only [Json.renderElemsL, Json.renderElemSep, List.length_append,
                       List.length_cons] at hf
            have hfe : (Json.renderL e).length < f := by omega
            have hfx : (Json.renderElemsL (x :: xs)).length + 1 < f := by
              simp only [Json.renderElemsL, List.length_append]; omega
            have hv := rt_val e budget f
              (',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest)) (hd e (by simp)) hfe
              (numDelim_cons (by decide))
            have key := rt_elems x xs budget f rest hdtail hfx
            have harg : Json.renderElemsL (e :: x :: xs) ++ ']' :: rest
                      = Json.renderL e ++ ',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest) := by
              simp only [Json.renderElemsL, Json.renderElemSep, List.cons_append, List.append_assoc]
            have hcomma : skipWs (',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest))
                        = ',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest) := by simp [skipWs, isWs]
            have h2 := skipWs_renderElemsL x xs (']' :: rest)
            rw [harg, parseElems_step, hv]
            simp only [hcomma, h2, key]
  termination_by e es _ _ _ _ _ => sizeOf e + sizeOf es
  theorem rt_members : ∀ (kv : String × Json) (ms : List (String × Json)),
      ∀ (budget fuel : Nat) (rest : List Char),
      (∀ x ∈ kv :: ms, Json.depth x.2 ≤ budget) →
      (Json.renderMembersL (kv :: ms)).length + 1 < fuel →
      parseMembers fuel budget (Json.renderMembersL (kv :: ms) ++ '}' :: rest)
        = .ok (kv :: ms, rest)
    | (k, v), [], budget, fuel, rest, hd, hf => by
        cases fuel with
        | zero => omega
        | succ f =>
            have hfe : (Json.renderL v).length < f := by
              simp only [renderMembersL_cons, Json.renderMemberSep, Json.renderStrL,
                         List.append_nil, List.length_append, List.length_cons] at hf
              omega
            have hv := rt_val v budget f ('}' :: rest) (hd (k, v) (by simp)) hfe
              (numDelim_cons (by decide))
            have harg : Json.renderMembersL ((k, v) :: []) ++ '}' :: rest
                = '"' :: (k.toList.flatMap escapeCharL
                    ++ ('"' :: (':' :: (Json.renderL v ++ '}' :: rest)))) := by
              simp [renderMembersL_cons, Json.renderMemberSep, Json.renderStrL]
            rw [harg, parseMembers_step]
            simp [skipWs, isWs, parseStr_render, skipWs_renderL, hv]
    | (k, v), (k', v') :: ms, budget, fuel, rest, hd, hf => by
        cases fuel with
        | zero => omega
        | succ f =>
            have hdtail : ∀ y ∈ (k', v') :: ms, Json.depth y.2 ≤ budget :=
              fun y hy => hd y (by simp [hy])
            simp only [renderMembersL_cons (ms := (k', v') :: ms), renderMemberSep_cons,
                       List.length_append, List.length_cons] at hf
            have hfe : (Json.renderL v).length < f := by
              simp only [Json.renderStrL, List.length_cons, List.length_append] at hf; omega
            have hfx : (Json.renderMembersL ((k', v') :: ms)).length + 1 < f := by
              simp only [Json.renderStrL, List.length_cons, List.length_append] at hf; omega
            have hv := rt_val v budget f
              (',' :: (Json.renderMembersL ((k', v') :: ms) ++ '}' :: rest)) (hd (k, v) (by simp))
              hfe (numDelim_cons (by decide))
            have key := rt_members (k', v') ms budget f rest hdtail hfx
            have harg : Json.renderMembersL ((k, v) :: (k', v') :: ms) ++ '}' :: rest
                = '"' :: (k.toList.flatMap escapeCharL
                    ++ ('"' :: (':' :: (Json.renderL v
                        ++ (',' :: (Json.renderMembersL ((k', v') :: ms) ++ '}' :: rest)))))) := by
              simp [renderMembersL_cons (ms := (k', v') :: ms), renderMemberSep_cons,
                    Json.renderStrL]
            rw [harg, parseMembers_step]
            simp [skipWs, isWs, parseStr_render, skipWs_renderL, hv,
                  skipWs_renderMembersL, key]
  termination_by kv ms _ _ _ _ _ => sizeOf kv + sizeOf ms
end

theorem parse_render {j : Json} {maxDepth : Nat}
    (h : j.depth ≤ maxDepth) : parse (Json.render j) maxDepth = .ok j := by
  have hv := rt_val j maxDepth ((Json.renderL j).length + 1) [] h (by omega) rfl
  simp only [List.append_nil] at hv
  simp only [parse, Json.render, String.toList_ofList, hv, skipWs, List.isEmpty_nil, if_true]

end Qed
