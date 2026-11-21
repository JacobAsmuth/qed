import Qed.Json.Basic

namespace Qed

private theorem parseDepth_le_all (fuel : Nat) :
    (∀ budget cs j r, parseVal fuel budget cs = .ok (j, r) → j.depth ≤ budget) ∧
    (∀ budget cs es r, parseElems fuel budget cs = .ok (es, r) → ∀ e ∈ es, e.depth ≤ budget) ∧
    (∀ budget cs ms r, parseMembers fuel budget cs = .ok (ms, r) → ∀ kv ∈ ms, kv.2.depth ≤ budget) := by
  induction fuel with
  | zero =>
      exact ⟨(fun _ _ _ _ h => nomatch h), (fun _ _ _ _ h => nomatch h), (fun _ _ _ _ h => nomatch h)⟩
  | succ f ih =>
      obtain ⟨ihV, ihE, ihM⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · intro budget cs j r h
        dsimp only [parseVal] at h
        split at h <;> try (cases h; exact Nat.zero_le _)
        · split at h <;> cases h; exact Nat.zero_le _
        · cases budget with
          | zero => cases h
          | succ b =>
              dsimp only at h
              split at h
              · cases h
              · split at h
                · cases h; exact Nat.succ_le_succ (Nat.zero_le _)
                · split at h
                  · rename_i he; cases h
                    have hle := Json.maxArr_le_iff.mpr (ihE b _ _ _ he)
                    simp only [Json.depth]; omega
                  · cases h
        · cases budget with
          | zero => cases h
          | succ b =>
              dsimp only at h
              split at h
              · cases h
              · split at h
                · cases h; exact Nat.succ_le_succ (Nat.zero_le _)
                · split at h
                  · rename_i hm; cases h
                    have hle := Json.maxObj_le_iff.mpr (ihM b _ _ _ hm)
                    simp only [Json.depth]; omega
                  · cases h
        · split at h
          · split at h <;> cases h; exact Nat.zero_le _
          · cases h
        · cases h
      · intro budget cs es r h
        dsimp only [parseElems] at h
        split at h
        · cases h
        · rename_i v r1 hv
          split at h
          · split at h
            · rename_i vs r'' he; cases h
              intro e hmem
              cases hmem with
              | head => exact ihV budget cs v r1 hv
              | tail _ hmem' => exact ihE budget _ _ _ he e hmem'
            · cases h
          · cases h
            intro e hmem
            cases hmem with
            | head => exact ihV budget cs v r1 hv
            | tail _ hmem' => nomatch hmem'
          · cases h
      · intro budget cs ms r h
        dsimp only [parseMembers] at h
        split at h
        · split at h
          · cases h
          · split at h
            · split at h
              · cases h
              · rename_i v r3 hv
                split at h
                · split at h
                  · rename_i ms' r5 hm; cases h
                    intro kv hmem
                    cases hmem with
                    | head => exact ihV budget _ v r3 hv
                    | tail _ hmem' => exact ihM budget _ _ _ hm kv hmem'
                  · cases h
                · cases h
                  intro kv hmem
                  cases hmem with
                  | head => exact ihV budget _ v r3 hv
                  | tail _ hmem' => nomatch hmem'
                · cases h
            · cases h
        · cases h

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
  let tail := (if ex == 0 then [] else 'e' :: intCharsL ex) ++ rest
  have harg : Json.renderNumL ⟨m, ex⟩ ++ rest = intCharsL m ++ tail := by
    simp only [Json.renderNumL, tail, List.append_assoc]
  have htailStop : takeDigits tail = ([], tail) := by
    by_cases hex : ex = 0
    · simp only [tail, hex, beq_self_eq_true, ↓reduceIte, List.nil_append]; exact takeDigits_stop hr
    · simp only [tail, beq_eq_false_iff_ne.2 hex, Bool.false_eq_true, ↓reduceIte, List.cons_append]
      exact takeDigits_cons_not (by decide)
  have hne : (natDigitsAux m.natAbs []).isEmpty = false := by
    cases h : natDigitsAux m.natAbs [] with
    | nil => exact absurd h (natDigits_ne_nil m.natAbs)
    | cons _ _ => rfl
  have htd := takeDigits_append _ (natDigits_digit m.natAbs) _ htailStop
  have finish : ∀ (neg : Bool), (if neg then (-1 : Int) else 1) * (m.natAbs : Int) = m →
      (let (fracDs, cs3) := match tail with | '.' :: r => takeDigits r | _ => ([], tail)
       let (expVal, cs4) : Int × List Char := match cs3 with
         | 'e' :: r | 'E' :: r =>
             let (sgn, r1) : Int × List Char := match r with
               | '+' :: r' => (1, r') | '-' :: r' => (-1, r') | _ => (1, r)
             let (eds, r2) := takeDigits r1
             (sgn * digitsToInt eds, r2)
         | _ => (0, cs3)
       let mant : Int := (if neg then -1 else 1) * digitsToInt (natDigitsAux m.natAbs [] ++ fracDs)
       Except.ok (JsonNumber.mk mant (expVal - (fracDs.length : Int)), cs4)) =
      (Except.ok (JsonNumber.mk m ex, rest) : Except String _) := by
    intro neg hneg
    by_cases hex : ex = 0
    · subst hex
      have ht : tail = rest := by simp only [tail, beq_self_eq_true, ↓reduceIte, List.nil_append]
      rw [ht]; clear ht harg htailStop htd
      cases rest with
      | nil => simp [digitsToInt_natDigits, hneg]
      | cons c t =>
          obtain ⟨_, hdot, he, hE⟩ := numDelim_head hr
          simp [hdot, he, hE, digitsToInt_natDigits, hneg]
    · have ht : tail = 'e' :: (intCharsL ex ++ rest) := by
        simp only [tail, beq_eq_false_iff_ne.2 hex, Bool.false_eq_true, ↓reduceIte, List.cons_append]
      rw [ht]; clear ht harg htailStop htd
      by_cases hexn : ex < 0
      · have hint : intCharsL ex ++ rest = '-' :: (natDigitsAux ex.natAbs [] ++ rest) := by
          simp [intCharsL, hexn]
        rw [hint]
        simp [takeDigits_append _ (natDigits_digit ex.natAbs) _ (takeDigits_stop hr),
          digitsToInt_natDigits, hneg]
        omega
      · obtain ⟨c1, t1, hex0, hc1⟩ := natDigits_cons ex.natAbs
        obtain ⟨hns, hps⟩ := digit_not_sign hc1
        have hint : intCharsL ex ++ rest = c1 :: (t1 ++ rest) := by
          simp only [intCharsL, hexn, ↓reduceIte, hex0, List.cons_append, List.nil_append]
        have htdE : takeDigits (c1 :: (t1 ++ rest)) = (c1 :: t1, rest) := by
          have := takeDigits_append _ (natDigits_digit ex.natAbs) _ (takeDigits_stop hr)
          rwa [hex0, List.cons_append] at this
        have hdiE : digitsToInt (c1 :: t1) = (ex.natAbs : Int) := by
          have := digitsToInt_natDigits ex.natAbs; rwa [hex0] at this
        rw [hint]
        simp [hps, hns, htdE, hdiE, digitsToInt_natDigits, hneg]
        omega
  rw [harg]; unfold parseNum
  by_cases hm : m < 0
  · have hcs : intCharsL m ++ tail = '-' :: (natDigitsAux m.natAbs [] ++ tail) := by simp [intCharsL, hm]
    rw [hcs]; simp only [htd, hne, Bool.false_eq_true, ↓reduceIte]
    exact finish true (by simp; omega)
  · obtain ⟨c0, t0, hm0, hc0⟩ := natDigits_cons m.natAbs
    obtain ⟨hns, _⟩ := digit_not_sign hc0
    have hcs : intCharsL m ++ tail = c0 :: (t0 ++ tail) := by
      simp only [intCharsL, hm, ↓reduceIte, hm0, List.cons_append, List.nil_append]
    rw [hcs]; simp [hns]
    rw [← List.cons_append, ← hm0, htd]
    simpa [natDigits_ne_nil] using finish false (by simp; omega)

private theorem hexVal_toHexDigit_fin :
    ∀ d : Fin 16, hexVal (toHexDigit d.val) = some d.val := by decide

theorem hexVal_toHexDigit (d : Nat) (h : d < 16) : hexVal (toHexDigit d) = some d :=
  hexVal_toHexDigit_fin ⟨d, h⟩

theorem parseStrAux_escape (c : Char) (acc rest : List Char) :
    parseStrAux acc (escapeCharL c ++ rest) = parseStrAux (c :: acc) rest := by
  dsimp only [escapeCharL]
  split
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rename_i cv h1 h2 h3 h4 h5
    by_cases hlt : c.toNat < 0x20
    · rw [if_pos hlt]
      simp only [List.cons_append, List.nil_append, parseStrAux, hex4]
      have h16 : ∀ k : Nat, k % 16 < 16 := fun k => Nat.mod_lt _ (by omega)
      rw [hexVal_toHexDigit _ (h16 _), hexVal_toHexDigit _ (h16 _),
          hexVal_toHexDigit _ (h16 _), hexVal_toHexDigit _ (h16 _)]
      simp only [bind, Option.bind, pure]
      have harith : ((c.toNat / 4096 % 16 * 16 + c.toNat / 256 % 16) * 16 + c.toNat / 16 % 16) * 16
              + c.toNat % 16 = c.toNat := by omega
      rw [harith, Char.ofNat_toNat]
    · simp only [if_neg hlt, List.cons_append, List.nil_append]
      rw [parseStrAux.eq_def]
      split
      · rename_i heq; injection heq with hc; exact absurd hc h1
      · rename_i heq; injection heq with hc; exact absurd hc h2
      · rename_i heq; injection heq with hc; exact absurd hc h2
      · rename_i heq; injection heq with hc hr; subst hc; subst hr; rfl
      · rename_i heq; cases heq

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
        simp only [Json.renderL, Json.renderNumL, intCharsL, hm, ↓reduceIte, List.cons_append, List.nil_append]
      · obtain ⟨c0, t0, h0, hc0⟩ := natDigits_cons n.mantissa.natAbs
        obtain ⟨hws, hbr, hbc⟩ := digit_not_special hc0
        refine ⟨c0, t0 ++ (if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent),
                ?_, hws, hbr, hbc⟩
        simp only [Json.renderL, Json.renderNumL, intCharsL, hm, ↓reduceIte, h0, List.cons_append, List.nil_append]

theorem skipWs_renderL (j : Json) (x : List Char) :
    skipWs (Json.renderL j ++ x) = Json.renderL j ++ x := by
  obtain ⟨c, t, hren, hcws, _, _⟩ := renderL_head j
  rw [hren, List.cons_append]
  simp only [skipWs, hcws, Bool.false_eq_true, ↓reduceIte]

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
  dsimp only [parseVal]
  rw [show skipWs (c0 :: t) = c0 :: t from by simp only [skipWs, hws, Bool.false_eq_true, ↓reduceIte]]
  split
  · rename_i heq; injection heq with hc; exact absurd hc hn
  · rename_i heq; injection heq with hc; exact absurd hc ht
  · rename_i heq; injection heq with hc; exact absurd hc hf
  · rename_i heq; injection heq with hc; exact absurd hc hq
  · rename_i heq; injection heq with hc; exact absurd hc hbk
  · rename_i heq; injection heq with hc; exact absurd hc hbc
  · rename_i heq; injection heq with hc hr; subst hc; subst hr
    simp only [hg, ↓reduceIte]
    rcases parseNum (c0 :: t) with _ | ⟨n, r'⟩ <;> rfl
  · rename_i heq; cases heq

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

private theorem skipWs_cons {c : Char} {r : List Char} (h : isWs c = false) :
    skipWs (c :: r) = c :: r := by
  simp only [skipWs, h, Bool.false_eq_true, ↓reduceIte]

theorem parseVal_arr (e : Json) (es : List Json) (f b : Nat) (rest : List Char) :
    parseVal (f + 1) (b + 1) ('[' :: (Json.renderElemsL (e :: es) ++ ']' :: rest))
      = (match parseElems f b (Json.renderElemsL (e :: es) ++ ']' :: rest) with
         | .ok (vs, r') => .ok (Json.arr vs, r')
         | .error msg   => .error msg) := by
  obtain ⟨c, t, hren, _, hcbr, _⟩ := renderL_head e
  have hcons : Json.renderElemsL (e :: es) ++ ']' :: rest
             = c :: (t ++ Json.renderElemSep es ++ ']' :: rest) := by
    simp only [Json.renderElemsL, hren, List.cons_append, List.append_assoc]
  unfold parseVal; simp only [skipWs_cons (by decide : isWs '[' = false)]
  rw [skipWs_renderElemsL, hcons]; simp only [if_neg hcbr]; rfl

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
  unfold parseVal; simp only [skipWs_cons (by decide : isWs '{' = false)]
  rw [skipWs_renderMembersL, hcons]; simp only [if_neg (by decide : ¬('"' = '}'))]; rfl

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
            have harg : Json.renderL (.str s) ++ rest
                = '"' :: (s.toList.flatMap escapeCharL ++ ('"' :: rest)) := by
              simp only [Json.renderL, Json.renderStrL, List.cons_append, List.nil_append, List.append_assoc]
            rw [harg]
            change (match parseStr (s.toList.flatMap escapeCharL ++ '"' :: rest) with
              | Except.ok (s', r') => Except.ok (Json.str s', r')
              | Except.error e => Except.error e) = Except.ok (Json.str s, rest)
            rw [parseStr_render]
        | arr es =>
            cases es with
            | nil =>
                cases budget with
                | zero => simp only [Json.depth, Json.maxArr] at hd; omega
                | succ b => rfl
            | cons e es =>
                cases budget with
                | zero => simp only [Json.depth] at hd; omega
                | succ b =>
                    simp only [Json.depth] at hd
                    have hdall : ∀ x ∈ (e :: es), Json.depth x ≤ b :=
                      Json.maxArr_le_iff.mp (by omega)
                    have hfe : (Json.renderElemsL (e :: es)).length + 1 < f := by
                      simp only [Json.renderL, List.length_cons, List.length_append] at hf; omega
                    have key := ihE e es b rest hdall hfe
                    have harr : Json.renderL (Json.arr (e :: es)) ++ rest
                              = '[' :: (Json.renderElemsL (e :: es) ++ ']' :: rest) := by
                      simp only [Json.renderL, List.cons_append, List.nil_append, List.append_assoc]
                    rw [harr, parseVal_arr e es f b rest, key]
        | obj ms =>
            cases ms with
            | nil =>
                cases budget with
                | zero => simp only [Json.depth, Json.maxObj] at hd; omega
                | succ b => rfl
            | cons kv ms =>
                rcases kv with ⟨k, v⟩
                cases budget with
                | zero => simp only [Json.depth] at hd; omega
                | succ b =>
                    simp only [Json.depth] at hd
                    have hdall : ∀ x ∈ ((k, v) :: ms), Json.depth x.2 ≤ b :=
                      Json.maxObj_le_iff.mp (by omega)
                    have hfm : (Json.renderMembersL ((k, v) :: ms)).length + 1 < f := by
                      simp only [Json.renderL, List.length_cons, List.length_append] at hf; omega
                    have key := ihM (k, v) ms b rest hdall hfm
                    have hobj : Json.renderL (Json.obj ((k, v) :: ms)) ++ rest
                              = '{' :: (Json.renderMembersL ((k, v) :: ms) ++ '}' :: rest) := by
                      simp only [Json.renderL, List.cons_append, List.nil_append, List.append_assoc]
                    rw [hobj, parseVal_obj k v ms f b rest, key]
      · intro e es budget rest hd hf
        cases es with
        | nil =>
            have hfe : (Json.renderL e).length < f := by
              simp only [Json.renderElemsL, Json.renderElemSep, List.append_nil] at hf; omega
            have hv := ihV e budget (']' :: rest) (hd e (List.mem_cons_self ..)) hfe
              (numDelim_cons (by decide))
            have harg : Json.renderElemsL (e :: []) ++ ']' :: rest = Json.renderL e ++ ']' :: rest := by
              simp only [Json.renderElemsL, Json.renderElemSep, List.append_nil]
            rw [harg]; dsimp only [parseElems]
            simp only [hv, skipWs_cons (by decide : isWs ']' = false)]
        | cons x xs =>
            have hdtail : ∀ y ∈ x :: xs, Json.depth y ≤ budget := fun y hy => hd y (List.mem_cons_of_mem _ hy)
            simp only [Json.renderElemsL, Json.renderElemSep, List.length_append, List.length_cons] at hf
            have hfe : (Json.renderL e).length < f := by omega
            have hfx : (Json.renderElemsL (x :: xs)).length + 1 < f := by
              simp only [Json.renderElemsL, List.length_append]; omega
            have hv := ihV e budget
              (',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest)) (hd e (List.mem_cons_self ..)) hfe
              (numDelim_cons (by decide))
            have key := ihE x xs budget rest hdtail hfx
            have harg : Json.renderElemsL (e :: x :: xs) ++ ']' :: rest
                      = Json.renderL e ++ ',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest) := by
              simp only [Json.renderElemsL, Json.renderElemSep, List.cons_append, List.append_assoc]
            rw [harg]; dsimp only [parseElems]
            simp only [hv, skipWs_cons (by decide : isWs ',' = false), skipWs_renderElemsL, key]
      · intro kv ms budget rest hd hf
        rcases kv with ⟨k, v⟩
        cases ms with
        | nil =>
            have hfe : (Json.renderL v).length < f := by
              simp only [renderMembersL_cons, Json.renderMemberSep, Json.renderStrL,
                         List.append_nil, List.length_append, List.length_cons] at hf
              omega
            have hv := ihV v budget ('}' :: rest) (hd (k, v) (List.mem_cons_self ..)) hfe
              (numDelim_cons (by decide))
            have harg : Json.renderMembersL ((k, v) :: []) ++ '}' :: rest
                = '"' :: (k.toList.flatMap escapeCharL
                    ++ ('"' :: (':' :: (Json.renderL v ++ '}' :: rest)))) := by
              simp only [renderMembersL_cons, Json.renderMemberSep, Json.renderStrL,
                         List.append_nil, List.nil_append, List.cons_append, List.append_assoc]
            rw [harg]; dsimp only [parseMembers]
            simp only [skipWs_cons (by decide : isWs '"' = false), parseStr_render,
              skipWs_cons (by decide : isWs ':' = false), skipWs_renderL, hv,
              skipWs_cons (by decide : isWs '}' = false)]
        | cons kv' ms =>
            rcases kv' with ⟨k', v'⟩
            have hdtail : ∀ y ∈ (k', v') :: ms, Json.depth y.2 ≤ budget :=
              fun y hy => hd y (List.mem_cons_of_mem _ hy)
            simp only [renderMembersL_cons (ms := (k', v') :: ms), renderMemberSep_cons,
                       List.length_append, List.length_cons] at hf
            have hfe : (Json.renderL v).length < f := by
              simp only [Json.renderStrL, List.length_cons, List.length_append] at hf; omega
            have hfx : (Json.renderMembersL ((k', v') :: ms)).length + 1 < f := by
              simp only [Json.renderStrL, List.length_cons, List.length_append] at hf; omega
            have hv := ihV v budget
              (',' :: (Json.renderMembersL ((k', v') :: ms) ++ '}' :: rest)) (hd (k, v) (List.mem_cons_self ..))
              hfe (numDelim_cons (by decide))
            have key := ihM (k', v') ms budget rest hdtail hfx
            have harg : Json.renderMembersL ((k, v) :: (k', v') :: ms) ++ '}' :: rest
                = '"' :: (k.toList.flatMap escapeCharL
                    ++ ('"' :: (':' :: (Json.renderL v
                        ++ (',' :: (Json.renderMembersL ((k', v') :: ms) ++ '}' :: rest)))))) := by
              simp only [renderMembersL_cons (ms := (k', v') :: ms), renderMemberSep_cons,
                         Json.renderStrL, List.nil_append, List.cons_append, List.append_assoc]
            rw [harg]; dsimp only [parseMembers]
            simp only [skipWs_cons (by decide : isWs '"' = false), parseStr_render,
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
