import Qed.Json.Basic

namespace Qed

set_option hygiene false in
local macro "peel_ok" : tactic =>
  `(tactic| repeat (any_goals first
    | (cases h; exact Nat.zero_le _)
    | (cases h; exact Nat.succ_le_succ (Nat.zero_le _))
    | (cases h; done)
    | split at h))

private theorem parseDepth_le_all (fuel : Nat) :
    (∀ budget cs j r, parseVal fuel budget cs = .ok (j, r) → j.depth ≤ budget) ∧
    (∀ budget cs es r, parseElems fuel budget cs = .ok (es, r) → ∀ e ∈ es, e.depth ≤ budget) ∧
    (∀ budget cs ms r, parseMembers fuel budget cs = .ok (ms, r) → ∀ kv ∈ ms, kv.2.depth ≤ budget) := by
  induction fuel with
  | zero => exact ⟨(fun _ _ _ _ h => nomatch h), (fun _ _ _ _ h => nomatch h), (fun _ _ _ _ h => nomatch h)⟩
  | succ f ih =>
      obtain ⟨ihV, ihE, ihM⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro budget cs j r h
        dsimp only [parseVal] at h; peel_ok
        · cases h; have := Json.maxArr_le_iff.mpr (ihE _ _ _ _ ‹_›); simp only [Json.depth]; omega
        · cases h; have := Json.maxObj_le_iff.mpr (ihM _ _ _ _ ‹_›); simp only [Json.depth]; omega
      · intro budget cs es r h
        dsimp only [parseElems] at h; peel_ok
        · cases h; intro _ hm; rcases List.mem_cons.mp hm with rfl | hm
          · exact ihV _ _ _ _ ‹_›
          · exact ihE _ _ _ _ ‹_› _ hm
        · cases h; intro _ hm; rcases List.mem_cons.mp hm with rfl | hm
          · exact ihV _ _ _ _ ‹_›
          · nomatch hm
      · intro budget cs ms r h
        dsimp only [parseMembers] at h; peel_ok
        · cases h; intro _ hm; rcases List.mem_cons.mp hm with rfl | hm
          · exact ihV _ _ _ _ ‹_›
          · exact ihM _ _ _ _ ‹_› _ hm
        · cases h; intro _ hm; rcases List.mem_cons.mp hm with rfl | hm
          · exact ihV _ _ _ _ ‹_›
          · nomatch hm

theorem parseVal_depth_le (fuel budget : Nat) (cs : List Char) (j : Json) (r : List Char)
    (h : parseVal fuel budget cs = .ok (j, r)) : j.depth ≤ budget :=
  (parseDepth_le_all fuel).1 budget cs j r h

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

private theorem digit_spec_fin : ∀ k : Fin 10,
    (Char.ofNat ('0'.toNat + k.val)).toNat - '0'.toNat = k.val
    ∧ isDigit (Char.ofNat ('0'.toNat + k.val)) = true := by decide

theorem digit_spec (k : Nat) (h : k < 10) :
    (Char.ofNat ('0'.toNat + k)).toNat - '0'.toNat = k
    ∧ isDigit (Char.ofNat ('0'.toNat + k)) = true :=
  digit_spec_fin ⟨k, h⟩

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

private theorem isDigit_ne {c t : Char} (hc : isDigit c = true) (ht : isDigit t = false) : c ≠ t :=
  fun e => by subst e; simp [hc] at ht

private theorem isDigit_not_ws {c : Char} (h : isDigit c = true) : isWs c = false := by
  simp only [isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  exact ⟨⟨⟨isDigit_ne h (by decide), isDigit_ne h (by decide)⟩, isDigit_ne h (by decide)⟩, isDigit_ne h (by decide)⟩

theorem numDelim_head {c : Char} {t : List Char} (h : numDelim (c :: t) = true) :
    isDigit c = false ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' := by
  simp only [numDelim, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

private theorem intCharsL_cases (i : Int) (tail : List Char) :
    (i < 0 ∧ intCharsL i ++ tail = '-' :: (natDigitsAux i.natAbs [] ++ tail)) ∨
    (¬ i < 0 ∧ ∃ c t, intCharsL i ++ tail = c :: (t ++ tail) ∧
      natDigitsAux i.natAbs [] = c :: t ∧ isDigit c = true) := by
  by_cases hi : i < 0
  · exact .inl ⟨hi, by simp [intCharsL, hi]⟩
  · obtain ⟨c, t, h0, hc⟩ := natDigits_cons i.natAbs
    exact .inr ⟨hi, c, t, by simp [intCharsL, hi, h0], h0, hc⟩

theorem parseNum_render (n : JsonNumber) (rest : List Char) (hr : numDelim rest = true) :
    parseNum (Json.renderNumL n ++ rest) = .ok (n, rest) := by
  obtain ⟨m, ex⟩ := n
  let tail := (if ex == 0 then [] else 'e' :: intCharsL ex) ++ rest
  have htailStop : takeDigits tail = ([], tail) := by
    by_cases hex : ex = 0
    · simp only [tail, hex, beq_self_eq_true, ↓reduceIte, List.nil_append]; exact takeDigits_stop hr
    · simp only [tail, beq_eq_false_iff_ne.2 hex, Bool.false_eq_true, ↓reduceIte, List.cons_append]
      exact takeDigits_cons_not (by decide)
  have htd := takeDigits_append _ (natDigits_digit m.natAbs) _ htailStop
  have hne : (natDigitsAux m.natAbs []).isEmpty = false := List.isEmpty_eq_false_iff.mpr (natDigits_ne_nil _)
  rw [show Json.renderNumL ⟨m, ex⟩ ++ rest = intCharsL m ++ tail by simp only [Json.renderNumL, tail, List.append_assoc]]
  unfold parseNum
  rcases intCharsL_cases m tail with ⟨hm, hcs⟩ | ⟨hm, c0, t0, hcs, hm0, hc0⟩ <;>
    (rw [hcs]; try (simp [isDigit_ne hc0 (by decide : isDigit '-' = false)]; rw [← List.cons_append, ← hm0])) <;>
    (simp only [htd, hne, natDigits_ne_nil, Bool.false_eq_true, ↓reduceIte];
     by_cases hex : ex = 0
     · subst hex
       rw [show tail = rest by simp only [tail, beq_self_eq_true, ↓reduceIte, List.nil_append]]
       cases rest with
       | nil => simp [digitsToInt_natDigits]; omega
       | cons c t => obtain ⟨_, hdot, he, hE⟩ := numDelim_head hr; simp [hdot, he, hE, digitsToInt_natDigits]; omega
     · rw [show tail = 'e' :: (intCharsL ex ++ rest) by
           simp only [tail, beq_eq_false_iff_ne.2 hex, Bool.false_eq_true, ↓reduceIte, List.cons_append]]
       have htdE := takeDigits_append _ (natDigits_digit ex.natAbs) _ (takeDigits_stop hr)
       rcases intCharsL_cases ex rest with ⟨hexn, hint⟩ | ⟨hexn, c1, t1, hint, hex0, hc1⟩ <;>
         (rw [hint]; try (simp [isDigit_ne hc1 (by decide : isDigit '-' = false), isDigit_ne hc1 (by decide : isDigit '+' = false)]; rw [← List.cons_append, ← hex0])) <;>
         (simp [htdE, digitsToInt_natDigits]; omega))

private theorem hexVal_toHexDigit_fin :
    ∀ d : Fin 16, hexVal (toHexDigit d.val) = some d.val := by decide

theorem hexVal_toHexDigit (d : Nat) (h : d < 16) : hexVal (toHexDigit d) = some d :=
  hexVal_toHexDigit_fin ⟨d, h⟩

theorem parseStrAux_escape (c : Char) (acc rest : List Char) :
    parseStrAux acc (escapeCharL c ++ rest) = parseStrAux (c :: acc) rest := by
  dsimp only [escapeCharL]
  split <;> try rfl
  rename_i _ h1 h2 _ _ _
  by_cases hlt : c.toNat < 0x20
  · simp only [if_pos hlt, List.cons_append, List.nil_append, parseStrAux, hex4]
    have h16 : ∀ k : Nat, k % 16 < 16 := fun k => Nat.mod_lt _ (by omega)
    rw [hexVal_toHexDigit _ (h16 _), hexVal_toHexDigit _ (h16 _),
        hexVal_toHexDigit _ (h16 _), hexVal_toHexDigit _ (h16 _)]
    simp only [bind, Option.bind, pure]
    rw [show ((c.toNat / 4096 % 16 * 16 + c.toNat / 256 % 16) * 16 + c.toNat / 16 % 16) * 16
          + c.toNat % 16 = c.toNat by omega, Char.ofNat_toNat]
  · simp only [if_neg hlt, List.cons_append, List.nil_append]
    rw [parseStrAux.eq_def]
    split <;> (rename_i heq; cases heq <;> first | contradiction | rfl)

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

theorem renderL_head (j : Json) :
    ∃ c t, Json.renderL j = c :: t ∧ isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases j with
  | null => exact ⟨'n', _, rfl, by decide⟩
  | bool b => cases b <;> first | exact ⟨'t', _, rfl, by decide⟩ | exact ⟨'f', _, rfl, by decide⟩
  | str _ => exact ⟨'"', _, rfl, by decide⟩
  | arr _ => exact ⟨'[', _, rfl, by decide⟩
  | obj _ => exact ⟨'{', _, rfl, by decide⟩
  | num n =>
      rcases intCharsL_cases n.mantissa (if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent) with
        ⟨_, hcs⟩ | ⟨_, c0, _, hcs, _, hc0⟩
      · exact ⟨'-', _, hcs, by decide⟩
      · exact ⟨c0, _, hcs, isDigit_not_ws hc0, isDigit_ne hc0 (by decide), isDigit_ne hc0 (by decide)⟩

private theorem skipWs_cons {c : Char} {r : List Char} (h : isWs c = false) :
    skipWs (c :: r) = c :: r := by
  simp only [skipWs, h, Bool.false_eq_true, ↓reduceIte]

theorem skipWs_renderL (j : Json) (x : List Char) :
    skipWs (Json.renderL j ++ x) = Json.renderL j ++ x := by
  obtain ⟨c, t, hren, hcws, _, _⟩ := renderL_head j
  rw [hren, List.cons_append, skipWs_cons hcws]

theorem skipWs_renderElemsL (e : Json) (es : List Json) (x : List Char) :
    skipWs (Json.renderElemsL (e :: es) ++ x) = Json.renderElemsL (e :: es) ++ x := by
  cases es <;> simp only [Json.renderElemsL, List.append_assoc] <;> exact skipWs_renderL e _

theorem skipWs_renderMembersL (k : String) (v : Json) (ms : List (String × Json)) (x : List Char) :
    skipWs (Json.renderMembersL ((k, v) :: ms) ++ x) = Json.renderMembersL ((k, v) :: ms) ++ x := by
  cases ms <;> simp [Json.renderMembersL, Json.renderStrL, skipWs, isWs]

theorem parseVal_to_parseNum (f b : Nat) (c0 : Char) (t : List Char)
    (h0 : c0 = '-' ∨ isDigit c0 = true) :
    parseVal (f + 1) b (c0 :: t)
      = (match parseNum (c0 :: t) with
         | .ok (n, r') => .ok (.num n, r')
         | .error e => .error e) := by
  have hws : isWs c0 = false := h0.elim (fun h => h ▸ rfl) isDigit_not_ws
  have hg : (c0 == '-' || isDigit c0) = true := by rcases h0 with rfl | h <;> simp [*]
  dsimp only [parseVal]; rw [skipWs_cons hws]
  split <;> (rename_i heq; cases heq <;> first
    | (rcases h0 with h | hd <;> first | exact absurd h (by decide) | exact absurd hd (by decide))
    | (simp only [hg, ↓reduceIte]; rcases parseNum (c0 :: t) with _ | ⟨_, _⟩ <;> rfl))

theorem parseVal_num (n : JsonNumber) (f b : Nat) (rest : List Char)
    (hr : numDelim rest = true) :
    parseVal (f + 1) b (Json.renderNumL n ++ rest) = .ok (.num n, rest) := by
  have hsplit : Json.renderNumL n ++ rest =
      intCharsL n.mantissa ++ ((if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent) ++ rest) := by
    simp only [Json.renderNumL, List.append_assoc]
  rcases intCharsL_cases n.mantissa ((if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent) ++ rest) with
    ⟨_, hcs⟩ | ⟨_, c0, _, hcs, _, hc0⟩ <;>
    (have harg := hsplit.trans hcs
     rw [harg, parseVal_to_parseNum f b _ _ (by first | exact .inl rfl | exact .inr hc0),
       ← harg, parseNum_render n rest hr])

theorem parseVal_arr (e : Json) (es : List Json) (f b : Nat) (rest : List Char) :
    parseVal (f + 1) (b + 1) ('[' :: (Json.renderElemsL (e :: es) ++ ']' :: rest))
      = (match parseElems f b (Json.renderElemsL (e :: es) ++ ']' :: rest) with
         | .ok (vs, r') => .ok (Json.arr vs, r')
         | .error msg   => .error msg) := by
  obtain ⟨c, t, hren, _, hcbr, _⟩ := renderL_head e
  unfold parseVal; simp only [skipWs_cons (by decide : isWs '[' = false)]
  rw [skipWs_renderElemsL]
  cases es <;> (simp only [Json.renderElemsL, hren, List.cons_append, List.append_assoc, if_neg hcbr]; rfl)

theorem parseVal_obj (k : String) (v : Json) (ms : List (String × Json))
    (f b : Nat) (rest : List Char) :
    parseVal (f + 1) (b + 1) ('{' :: (Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest))
      = (match parseMembers f b (Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest) with
         | .ok (ms', r') => .ok (Json.obj ms', r')
         | .error msg   => .error msg) := by
  unfold parseVal; simp only [skipWs_cons (by decide : isWs '{' = false)]
  rw [skipWs_renderMembersL]
  cases ms <;> (simp only [Json.renderMembersL, Json.renderStrL, List.cons_append, List.append_assoc,
    if_neg (by decide : ¬('"' = '}'))]; rfl)

private theorem rt_all (fuel : Nat) :
    (∀ (j : Json) (budget : Nat) (rest : List Char),
      j.depth ≤ budget → (Json.renderL j).length < fuel → numDelim rest = true →
      parseVal fuel budget (Json.renderL j ++ rest) = .ok (j, rest)) ∧
    (∀ (e : Json) (es : List Json) (budget : Nat) (rest : List Char),
      (∀ x ∈ e :: es, Json.depth x ≤ budget) →
      (Json.renderElemsL (e :: es)).length + 1 < fuel →
      parseElems fuel budget (Json.renderElemsL (e :: es) ++ ']' :: rest) = .ok (e :: es, rest)) ∧
    (∀ (kv : String × Json) (ms : List (String × Json)) (budget : Nat) (rest : List Char),
      (∀ x ∈ kv :: ms, Json.depth x.2 ≤ budget) →
      (Json.renderMembersL (kv :: ms)).length + 1 < fuel →
      parseMembers fuel budget (Json.renderMembersL (kv :: ms) ++ '}' :: rest) = .ok (kv :: ms, rest)) := by
  induction fuel with
  | zero =>
      exact ⟨fun _ _ _ _ hf _ => absurd hf (Nat.not_lt_zero _),
             fun _ _ _ _ _ hf => absurd hf (Nat.not_lt_zero _),
             fun _ _ _ _ _ hf => absurd hf (Nat.not_lt_zero _)⟩
  | succ f ih =>
      obtain ⟨ihV, ihE, ihM⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro j budget rest hd hf hr
        cases j with
        | null => rfl
        | bool b => cases b <;> rfl
        | num n => exact parseVal_num n f budget rest hr
        | str s =>
            simp only [Json.renderL, Json.renderStrL, List.cons_append, List.nil_append, List.append_assoc,
              parseVal, skipWs_cons (by decide : isWs '"' = false), parseStr_render]
        | arr es =>
            cases budget with
            | zero => simp only [Json.depth] at hd; omega
            | succ b =>
              cases es with
              | nil => rfl
              | cons e es =>
                  simp only [Json.depth, Json.renderL, List.length_cons, List.length_append] at hd hf
                  have key := ihE e es b rest (Json.maxArr_le_iff.mp (by omega)) (by omega)
                  simp only [Json.renderL, List.cons_append, List.nil_append, List.append_assoc,
                    parseVal_arr, key]
        | obj ms =>
            cases budget with
            | zero => simp only [Json.depth] at hd; omega
            | succ b =>
              cases ms with
              | nil => rfl
              | cons kv ms =>
                  rcases kv with ⟨k, v⟩
                  simp only [Json.depth, Json.renderL, List.length_cons, List.length_append] at hd hf
                  have key := ihM (k, v) ms b rest (Json.maxObj_le_iff.mp (by omega)) (by omega)
                  simp only [Json.renderL, List.cons_append, List.nil_append, List.append_assoc,
                    parseVal_obj, key]
      · intro e es budget rest hd hf
        cases es with
        | nil =>
            simp only [Json.renderElemsL] at hf ⊢
            have hv := ihV e budget (']' :: rest) (hd e (List.mem_cons_self ..)) (by omega) (numDelim_cons (by decide))
            simp only [parseElems, hv, skipWs_cons (by decide : isWs ']' = false)]
        | cons x xs =>
            rw [Json.renderElemsL.eq_def] at hf; dsimp only at hf
            simp only [List.length_append, List.length_cons] at hf
            have hv := ihV e budget (',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest))
              (hd e (List.mem_cons_self ..)) (by omega) (numDelim_cons (by decide))
            have key := ihE x xs budget rest (fun y hy => hd y (List.mem_cons_of_mem _ hy)) (by omega)
            rw [Json.renderElemsL.eq_def]; dsimp only
            rw [List.append_assoc, List.cons_append]
            simp only [parseElems, hv, skipWs_cons (by decide : isWs ',' = false), skipWs_renderElemsL, key]
      · intro kv ms budget rest hd hf
        rcases kv with ⟨k, v⟩
        cases ms with
        | nil =>
            simp only [Json.renderMembersL, Json.renderStrL, List.length_append, List.length_cons] at hf
            have hv := ihV v budget ('}' :: rest) (hd (k, v) (List.mem_cons_self ..)) (by omega) (numDelim_cons (by decide))
            simp only [Json.renderMembersL, Json.renderStrL, List.cons_append, List.nil_append, List.append_assoc,
              parseMembers, skipWs_cons (by decide : isWs '"' = false), parseStr_render,
              skipWs_cons (by decide : isWs ':' = false), skipWs_renderL, hv,
              skipWs_cons (by decide : isWs '}' = false)]
        | cons kv' ms =>
            rcases kv' with ⟨k', v'⟩
            rw [Json.renderMembersL.eq_def] at hf; dsimp only at hf
            simp only [Json.renderStrL, List.length_append, List.length_cons] at hf
            have hv := ihV v budget (',' :: (Json.renderMembersL ((k', v') :: ms) ++ '}' :: rest))
              (hd (k, v) (List.mem_cons_self ..)) (by omega) (numDelim_cons (by decide))
            have key := ihM (k', v') ms budget rest (fun y hy => hd y (List.mem_cons_of_mem _ hy)) (by omega)
            rw [Json.renderMembersL.eq_def]; dsimp only
            simp only [Json.renderStrL, List.cons_append, List.nil_append, List.append_assoc,
              parseMembers, skipWs_cons (by decide : isWs '"' = false), parseStr_render,
              skipWs_cons (by decide : isWs ':' = false), skipWs_renderL, hv,
              skipWs_cons (by decide : isWs ',' = false), skipWs_renderMembersL, key]

theorem rt_val (j : Json) (budget fuel : Nat) (rest : List Char)
    (hd : j.depth ≤ budget) (hf : (Json.renderL j).length < fuel) (hr : numDelim rest = true) :
    parseVal fuel budget (Json.renderL j ++ rest) = .ok (j, rest) :=
  (rt_all fuel).1 j budget rest hd hf hr

theorem parse_render {j : Json} {maxDepth : Nat}
    (h : j.depth ≤ maxDepth) : parse (Json.render j) maxDepth = .ok j := by
  have hv := rt_val j maxDepth ((Json.renderL j).length + 1) [] h (by omega) rfl
  simp only [List.append_nil] at hv
  simp only [parse, Json.render, String.toList_ofList, hv, skipWs, List.isEmpty_nil, if_true]

end Qed
