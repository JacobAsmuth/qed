import Qed.Json.Basic

namespace Qed

private def numDelim : List Char → Bool | [] => true | c :: _ => !(isDigit c || c == '.' || c == 'e' || c == 'E')
private theorem map_ok {x : Except String α} {f : α → β} {y : β} (h : x.map f = .ok y) : ∃ a, x = .ok a ∧ f a = y := by cases x with | error _ => cases h | ok a => exact ⟨a, rfl, Except.ok.inj h⟩
private theorem bind_ok {x : Except String α} {f : α → Except String β} {y : β} (h : x.bind f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by cases x with | error _ => cases h | ok a => exact ⟨a, rfl, h⟩

private theorem parseContainer_depth {α : Type} {close : Char} {empty : Json} {wrap : α → Json} {pItems : Nat → List Char → Except String (α × List Char)} {budget : Nat} {cs : List Char} {j : Json} {r : List Char}
    (he : empty.depth ≤ 1) (hw : ∀ b xs r', pItems b r' = .ok (xs, r) → (wrap xs).depth ≤ b + 1) (h : parseContainer close empty wrap pItems budget cs = .ok (j, r)) : j.depth ≤ budget := by
  cases budget with | zero => cases h | succ b =>
    dsimp only [parseContainer] at h; cases hws : skipWs cs with | nil => rw [hws] at h; cases h | cons c r' =>
      rw [hws] at h; dsimp only at h; split at h; · cases h; omega
      obtain ⟨⟨xs, _⟩, hx, heq⟩ := map_ok h; cases heq; exact hw b xs _ hx

private theorem parseSep_depth {α : Type} {P : α → Prop} {close : Char} {err : String} {step : List Char → Except String (α × List Char)} {rec : List Char → Except String (List α × List Char)} {cs : List Char} {xs : List α} {r : List Char}
    (hs : ∀ cs v r', step cs = .ok (v, r') → P v) (hr : ∀ cs ys r', rec cs = .ok (ys, r') → ∀ y ∈ ys, P y) (h : parseSep close err step rec cs = .ok (xs, r)) : ∀ x ∈ xs, P x := by
  obtain ⟨⟨v, r1⟩, hv, h⟩ := bind_ok h; dsimp only at h
  cases hws : skipWs r1 with | nil => rw [hws] at h; cases h | cons c r' =>
    rw [hws] at h; dsimp only at h; split at h
    · obtain ⟨⟨vs, _⟩, hvs, heq⟩ := map_ok h; cases heq; exact fun x hm => (List.mem_cons.1 hm).elim (· ▸ hs _ _ _ hv) (hr _ _ _ hvs x)
    · split at h <;> cases h; exact fun x hm => List.mem_singleton.1 hm ▸ hs _ _ _ hv

private theorem parseDepth_le_all (fuel : Nat) :
    (∀ budget cs j r, parseVal fuel budget cs = .ok (j, r) → j.depth ≤ budget) ∧
    (∀ budget cs es r, parseElems fuel budget cs = .ok (es, r) → ∀ e ∈ es, e.depth ≤ budget) ∧
    (∀ budget cs ms r, parseMembers fuel budget cs = .ok (ms, r) → ∀ kv ∈ ms, kv.2.depth ≤ budget) := by
  induction fuel with
  | zero => exact ⟨(fun _ _ _ _ h => nomatch h), (fun _ _ _ _ h => nomatch h), (fun _ _ _ _ h => nomatch h)⟩
  | succ f ih =>
      obtain ⟨ihV, ihE, ihM⟩ := ih; refine ⟨?_, fun b _ _ _ h => parseSep_depth (P := fun e => e.depth ≤ b) (ihV b) (ihE b) h, ?_⟩
      · intro budget cs j r h; dsimp only [parseVal] at h; cases hws : skipWs cs with | nil => rw [hws] at h; cases h | cons c r' =>
          rw [hws] at h; dsimp only at h
          split at h; · obtain ⟨⟨_, _⟩, _, heq⟩ := map_ok h; cases heq; exact Nat.zero_le _
          split at h; · exact parseContainer_depth (by decide) (fun _ _ _ hx => by have := Json.maxArr_le_iff.2 (ihE _ _ _ _ hx); simp only [Json.depth]; omega) h
          split at h; · exact parseContainer_depth (by decide) (fun _ _ _ hx => by have := Json.maxObj_le_iff.2 (ihM _ _ _ _ hx); simp only [Json.depth]; omega) h
          split at h; · obtain ⟨⟨_, _⟩, _, heq⟩ := map_ok h; cases heq; exact Nat.zero_le _
          unfold parseLit at h; split at h <;> cases h <;> exact Nat.zero_le _
      · refine fun budget cs ms r h => parseSep_depth (P := fun kv : String × Json => kv.2.depth ≤ budget) (fun cs kv r' hs => ?_) (ihM budget) h
        dsimp only [parseMember] at hs; split at hs <;> try cases hs
        obtain ⟨⟨_, r1⟩, _, hs⟩ := bind_ok hs; dsimp only at hs; split at hs <;> try cases hs
        obtain ⟨⟨v, _⟩, hv, heq⟩ := map_ok hs; cases heq; exact ihV budget _ _ _ hv

theorem parse_depth_le (s : String) (maxDepth : Nat) (j : Json) (h : parse s maxDepth = .ok j) : j.depth ≤ maxDepth := by
  obtain ⟨⟨j0, r⟩, hval, h⟩ := bind_ok h; dsimp only at h; split at h <;> cases h; exact (parseDepth_le_all _).1 maxDepth _ _ _ hval

private theorem digit_spec_fin : ∀ k : Fin 10, (Char.ofNat ('0'.toNat + k.val)).toNat - '0'.toNat = k.val ∧ isDigit (Char.ofNat ('0'.toNat + k.val)) = true := by decide

private theorem natDigitsAux_append (n : Nat) : ∀ acc : List Char, natDigitsAux n acc = natDigitsAux n [] ++ acc := by
  induction n using Nat.strongRecOn with | _ n ih =>
    intro acc; rw [natDigitsAux.eq_def (acc := acc), natDigitsAux.eq_def (acc := [])]
    by_cases h : n < 10; · simp only [ite_eq_left h, List.singleton_append]
    simp only [ite_eq_right h]; rw [ih (n / 10) (by omega), ih (n / 10) (by omega) [_], List.append_assoc, List.singleton_append]

private theorem natDigits_spec (n : Nat) :
    natDigitsAux n [] ≠ [] ∧ (∀ c ∈ natDigitsAux n [], isDigit c = true) ∧ (natDigitsAux n []).foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0 = n := by
  induction n using Nat.strongRecOn with | _ n ih =>
    have hunf : natDigitsAux n [] = (if n < 10 then [] else natDigitsAux (n / 10) []) ++ [Char.ofNat ('0'.toNat + n % 10)] := by
      rw [natDigitsAux.eq_def]; by_cases h : n < 10; (simp only [ite_eq_left h, List.nil_append]); simp only [ite_eq_right h]; exact natDigitsAux_append (n / 10) [_]
    rw [hunf]; have hd := digit_spec_fin ⟨n % 10, Nat.mod_lt _ (by decide)⟩
    refine ⟨List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _),
      fun c hc => (List.mem_append.1 hc).elim (fun h => if h10 : n < 10 then by rw [ite_eq_left h10] at h; cases h else (ih (n / 10) (by omega)).2.1 c (by rw [ite_eq_right h10] at h; exact h)) (fun h => List.mem_singleton.1 h ▸ hd.2), ?_⟩
    rw [List.foldl_append]; by_cases h : n < 10
    · simp only [ite_eq_left h, List.foldl_nil, List.foldl_cons, hd.1]; omega
    · simp only [ite_eq_right h, List.foldl_cons, List.foldl_nil, (ih (n / 10) (by omega)).2.2, hd.1]; omega

private theorem takeDigits_stop {cs : List Char} (h : numDelim cs = true) : takeDigits cs = ([], cs) := by
  cases cs with | nil => rfl | cons c t => simp only [numDelim, Bool.not_eq_true', Bool.or_eq_false_iff] at h; simp only [takeDigits, h.1.1.1, Bool.false_eq_true, ↓reduceIte]
private theorem takeDigits_append : ∀ (ds : List Char), (∀ c ∈ ds, isDigit c = true) → ∀ rest, takeDigits rest = ([], rest) → takeDigits (ds ++ rest) = (ds, rest)
  | [], _, _, hr => hr | c :: t, hd, r, hr => by simp only [List.cons_append, takeDigits, hd c (.head _), ↓reduceIte, takeDigits_append t (fun x hx => hd x (.tail _ hx)) r hr]
private theorem isDigit_ne {c t : Char} (hc : isDigit c = true) (ht : isDigit t = false) : c ≠ t := fun e => by subst e; rw [hc] at ht; cases ht
private theorem isDigit_not_ws {c : Char} (h : isDigit c = true) : isWs c = false := by
  simp only [isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne]; exact ⟨⟨⟨isDigit_ne h rfl, isDigit_ne h rfl⟩, isDigit_ne h rfl⟩, isDigit_ne h rfl⟩

private theorem intCharsL_cases (i : Int) (tail : List Char) :
    (i < 0 ∧ intCharsL i ++ tail = '-' :: (natDigitsAux i.natAbs [] ++ tail)) ∨
    (¬ i < 0 ∧ ∃ c t, intCharsL i ++ tail = c :: (t ++ tail) ∧ natDigitsAux i.natAbs [] = c :: t ∧ isDigit c = true) := by
  by_cases hi : i < 0
  · exact .inl ⟨hi, by simp only [intCharsL, ite_eq_left hi, List.nil_append, List.cons_append]⟩
  · match h0 : natDigitsAux i.natAbs [] with
    | [] => exact absurd h0 (natDigits_spec _).1
    | c :: t => exact .inr ⟨hi, c, t, by simp only [intCharsL, ite_eq_right hi, h0, List.nil_append, List.cons_append], rfl, (natDigits_spec _).2.1 c (h0 ▸ List.mem_cons_self ..)⟩

private theorem parseSigned_intCharsL (allowPlus : Bool) (i : Int) (tail : List Char) (hstop : takeDigits tail = ([], tail)) :
    parseSigned allowPlus (intCharsL i ++ tail) = (if i < 0 then -1 else 1, natDigitsAux i.natAbs [], tail) := by
  have htd := takeDigits_append _ (natDigits_spec i.natAbs).2.1 _ hstop; unfold parseSigned
  rcases intCharsL_cases i tail with ⟨hi, h⟩ | ⟨hi, c, t, h, h0, hc⟩
  · rw [h]; simp only [hi, beq_self_eq_true, ↓reduceIte, htd]
  · rw [h]; dsimp only; simp only [hi, beq_eq_false_iff_ne.2 (isDigit_ne hc rfl : c ≠ '-'), beq_eq_false_iff_ne.2 (isDigit_ne hc rfl : c ≠ '+'), Bool.and_false, Bool.false_eq_true, ↓reduceIte]; rw [← List.cons_append, ← h0, htd]

private theorem parseNum_render (n : JsonNumber) (rest : List Char) (hr : numDelim rest = true) : parseNum (Json.renderNumL n ++ rest) = .ok (n, rest) := by
  obtain ⟨m, ex⟩ := n; let tail := (if ex == 0 then [] else 'e' :: intCharsL ex) ++ rest
  have hd (i : Int) : digitsToInt (natDigitsAux i.natAbs []) = (i.natAbs : Int) := congrArg Nat.cast (natDigits_spec i.natAbs).2.2
  have htail : takeDigits tail = ([], tail) ∧ parseFrac tail = ([], tail) ∧ parseExp tail = (ex, rest) := by
    by_cases hex : ex = 0
    · subst hex; have ht : tail = rest := by simp only [tail, beq_self_eq_true, ↓reduceIte, List.nil_append]
      rw [ht]; refine ⟨takeDigits_stop hr, ?_, ?_⟩ <;> (cases rest with | nil => rfl | cons c t => simp only [numDelim, Bool.not_eq_true', Bool.or_eq_false_iff] at hr; simp only [parseFrac, parseExp, hr.1.1.2, hr.1.2, hr.2, Bool.or_false, Bool.false_eq_true, ↓reduceIte])
    · have ht : tail = 'e' :: (intCharsL ex ++ rest) := by simp only [tail, beq_eq_false_iff_ne.2 hex, Bool.false_eq_true, ↓reduceIte, List.cons_append]
      rw [ht]; refine ⟨rfl, rfl, ?_⟩; simp only [parseExp, beq_self_eq_true, Bool.true_or, ↓reduceIte, parseSigned_intCharsL true ex rest (takeDigits_stop hr), hd]; congr 1; split <;> omega
  have hne : (natDigitsAux m.natAbs []).isEmpty = false := List.isEmpty_eq_false_iff.2 (natDigits_spec _).1
  rw [show Json.renderNumL ⟨m, ex⟩ ++ rest = intCharsL m ++ tail by simp only [Json.renderNumL, tail, List.append_assoc]]
  unfold parseNum; rw [parseSigned_intCharsL false m tail htail.1]; dsimp only
  rw [hne, ite_eq_right Bool.false_ne_true, htail.2.1]; dsimp only; rw [htail.2.2]
  simp only [List.append_nil, hd, List.length_nil, Except.ok.injEq, Prod.mk.injEq, JsonNumber.mk.injEq, and_true]; split <;> omega

private theorem parseStrAux_escape (c : Char) (acc : String) (rest : List Char) : parseStrAux acc (escapeCharL c ++ rest) = parseStrAux (acc.push c) rest := by
  dsimp only [escapeCharL]; split <;> try rfl
  rename_i _ h1 h2 _ _ _; by_cases hlt : c.toNat < 0x20
  · simp only [ite_eq_left hlt, hexEscapeL, List.cons_append, List.nil_append]; rw [parseStrAux.eq_def]
    simp only [show ('\\' == '"') = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, hex4, hexVal, unhexNat?_hexDigitLower (Nat.mod_lt _ (by decide)), bind, Option.bind, pure, Option.elim]
    rw [show ((c.toNat / 4096 % 16 * 16 + c.toNat / 256 % 16) * 16 + c.toNat / 16 % 16) * 16 + c.toNat % 16 = c.toNat by omega, Char.ofNat_toNat]
  · simp only [ite_eq_right hlt, List.cons_append, List.nil_append]; rw [parseStrAux.eq_def]; simp only [beq_eq_false_iff_ne.2 h1, beq_eq_false_iff_ne.2 h2, Bool.false_eq_true, ↓reduceIte]

private theorem parseStrAux_flatMap : ∀ (cs : List Char) (acc : String) (rest : List Char),
    parseStrAux acc (cs.flatMap escapeCharL ++ '"' :: rest) = .ok (acc ++ String.ofList cs, rest)
  | [], _, _ => by rw [List.flatMap_nil, List.nil_append, parseStrAux.eq_def]; simp only [beq_self_eq_true, ↓reduceIte, String.ofList_nil, String.append_empty]
  | c :: cs, _, _ => by rw [List.flatMap_cons, List.append_assoc, parseStrAux_escape, parseStrAux_flatMap cs]; congr 2; exact String.toList_injective (by simp only [String.toList_append, String.toList_push, String.toList_ofList, List.append_assoc, List.singleton_append])

private theorem parseStr_render (s : String) (rest : List Char) : parseStr (s.toList.flatMap escapeCharL ++ '"' :: rest) = .ok (s, rest) := by
  rw [parseStr, parseStrAux_flatMap, String.empty_append, String.ofList_toList]

private theorem renderL_head (j : Json) : ∃ c t, Json.renderL j = c :: t ∧ isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' := by
  cases j with
  | null => exact ⟨'n', _, rfl, by decide⟩ | bool b => cases b <;> first | exact ⟨'t', _, rfl, by decide⟩ | exact ⟨'f', _, rfl, by decide⟩
  | str _ => exact ⟨'"', _, rfl, by decide⟩ | arr _ => exact ⟨'[', _, rfl, by decide⟩ | obj _ => exact ⟨'{', _, rfl, by decide⟩
  | num n => rcases intCharsL_cases n.mantissa (if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent) with ⟨_, hcs⟩ | ⟨_, c0, _, hcs, _, hc0⟩
             · exact ⟨'-', _, hcs, by decide⟩
             · exact ⟨c0, _, hcs, isDigit_not_ws hc0, isDigit_ne hc0 rfl, isDigit_ne hc0 rfl⟩

private theorem skipWs_cons {c : Char} {r : List Char} (h : isWs c = false) : skipWs (c :: r) = c :: r := by simp only [skipWs, h, Bool.false_eq_true, ↓reduceIte]
private theorem skipWs_renderL (j : Json) (x : List Char) : skipWs (Json.renderL j ++ x) = Json.renderL j ++ x := by
  obtain ⟨c, _, hren, hcws, _, _⟩ := renderL_head j; rw [hren, List.cons_append, skipWs_cons hcws]

private theorem parseVal_num (n : JsonNumber) (f b : Nat) (rest : List Char) (hr : numDelim rest = true) :
    parseVal (f + 1) b (Json.renderNumL n ++ rest) = .ok (.num n, rest) := by
  have toNum (c0 : Char) (t : List Char) (h0 : c0 = '-' ∨ isDigit c0 = true) : parseVal (f + 1) b (c0 :: t) = (parseNum (c0 :: t)).map fun (n, r') => (.num n, r') := by
    have hne (k : Char) (hk : k ≠ '-' ∧ isDigit k = false) : (c0 == k) = false := beq_eq_false_iff_ne.2 (h0.elim (fun h => h ▸ hk.1.symm) (fun hd => isDigit_ne hd hk.2))
    have hg : (c0 == '-' || isDigit c0) = true := h0.elim (fun h => by rw [h]; rfl) (fun h => by rw [h, Bool.or_true])
    simp only [parseVal, skipWs_cons (h0.elim (fun h => h ▸ rfl) isDigit_not_ws), hne '"' ⟨by decide, rfl⟩, hne '[' ⟨by decide, rfl⟩, hne '{' ⟨by decide, rfl⟩, hg, Bool.false_eq_true, ↓reduceIte]
  have hsplit : Json.renderNumL n ++ rest = intCharsL n.mantissa ++ ((if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent) ++ rest) := by simp only [Json.renderNumL, List.append_assoc]
  rcases intCharsL_cases n.mantissa ((if n.exponent == 0 then [] else 'e' :: intCharsL n.exponent) ++ rest) with ⟨_, hcs⟩ | ⟨_, c0, _, hcs, _, hc0⟩ <;>
    (have harg := hsplit.trans hcs; rw [harg, toNum _ _ (by first | exact .inl rfl | exact .inr hc0), ← harg, parseNum_render n rest hr]; rfl)

private theorem parseSep_single {α : Type} {close : Char} {err : String} {step : List Char → Except String (α × List Char)} {rec : List Char → Except String (List α × List Char)} {cs rest : List Char} {v : α}
    (hws : isWs close = false) (hne : close ≠ ',') (hs : step cs = .ok (v, close :: rest)) : parseSep close err step rec cs = .ok ([v], rest) := by
  simp only [parseSep, hs, Except.bind, skipWs_cons hws, beq_eq_false_iff_ne.2 hne, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
private theorem parseSep_cons {α : Type} {close : Char} {err : String} {step : List Char → Except String (α × List Char)} {rec : List Char → Except String (List α × List Char)} {cs tail rest : List Char} {v : α} {vs : List α}
    (hs : step cs = .ok (v, ',' :: tail)) (hws : skipWs tail = tail) (hr : rec tail = .ok (vs, rest)) : parseSep close err step rec cs = .ok (v :: vs, rest) := by
  simp only [parseSep, hs, Except.bind, skipWs_cons (rfl : isWs ',' = false), beq_self_eq_true, ↓reduceIte, hws, hr, Except.map]
private theorem parseContainer_rt {α : Type} {close c : Char} {empty : Json} {wrap : α → Json} {pItems : Nat → List Char → Except String (α × List Char)} {b : Nat} {t rest : List Char} {xs : α}
    (hcws : isWs c = false) (hne : c ≠ close) (hp : pItems b (c :: t) = .ok (xs, rest)) : parseContainer close empty wrap pItems (b + 1) (c :: t) = .ok (wrap xs, rest) := by
  simp only [parseContainer, skipWs_cons hcws, beq_eq_false_iff_ne.2 hne, Bool.false_eq_true, ↓reduceIte, hp, Except.map]

private theorem rt_all (fuel : Nat) :
    (∀ j budget rest, j.depth ≤ budget → (Json.renderL j).length < fuel → numDelim rest = true → parseVal fuel budget (Json.renderL j ++ rest) = .ok (j, rest)) ∧
    (∀ e es budget rest, (∀ x ∈ e :: es, Json.depth x ≤ budget) → (Json.renderElemsL (e :: es)).length + 1 < fuel → parseElems fuel budget (Json.renderElemsL (e :: es) ++ ']' :: rest) = .ok (e :: es, rest)) ∧
    (∀ kv ms budget rest, (∀ x ∈ kv :: ms, Json.depth x.2 ≤ budget) → (Json.renderMembersL (kv :: ms)).length + 1 < fuel → parseMembers fuel budget (Json.renderMembersL (kv :: ms) ++ '}' :: rest) = .ok (kv :: ms, rest)) := by
  induction fuel with
  | zero => exact ⟨(fun _ _ _ _ hf _ => nomatch hf), (fun _ _ _ _ _ hf => nomatch hf), (fun _ _ _ _ _ hf => nomatch hf)⟩
  | succ f ih =>
      obtain ⟨ihV, ihE, ihM⟩ := ih; refine ⟨?_, ?_, ?_⟩
      · intro j budget rest hd hf hr; cases j with
        | null => rfl | bool b => cases b <;> rfl | num n => exact parseVal_num n f budget rest hr
        | str s => simp only [Json.renderL, Json.renderStrL, List.cons_append, List.nil_append, List.append_assoc, parseVal, skipWs_cons (rfl : isWs '"' = false), beq_self_eq_true, ↓reduceIte, parseStr_render, Except.map]
        | arr es =>
            cases budget with | zero => simp only [Json.depth] at hd; omega | succ b =>
              cases es with | nil => rfl | cons e es =>
                simp only [Json.depth, Json.renderL, List.length_cons, List.length_append] at hd hf
                have key := ihE e es b rest (Json.maxArr_le_iff.1 (by omega)) (by omega); obtain ⟨c, _, hren, hcws, hcbr, _⟩ := renderL_head e
                simp only [Json.renderL, List.cons_append, List.nil_append, List.append_assoc, parseVal, skipWs_cons (rfl : isWs '[' = false), show ('[' == '"') = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
                cases es <;> (simp only [Json.renderElemsL, hren, List.cons_append, List.append_assoc] at key ⊢; exact parseContainer_rt hcws hcbr key)
        | obj ms =>
            cases budget with | zero => simp only [Json.depth] at hd; omega | succ b =>
              cases ms with | nil => rfl | cons kv ms =>
                rcases kv with ⟨k, v⟩; simp only [Json.depth, Json.renderL, List.length_cons, List.length_append] at hd hf
                have key := ihM (k, v) ms b rest (Json.maxObj_le_iff.1 (by omega)) (by omega)
                simp only [Json.renderL, List.cons_append, List.nil_append, List.append_assoc, parseVal, skipWs_cons (rfl : isWs '{' = false), show ('{' == '"') = false from rfl, show ('{' == '[') = false from rfl, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]
                cases ms <;> (simp only [Json.renderMembersL, Json.renderStrL, List.cons_append, List.append_assoc] at key ⊢; exact parseContainer_rt (rfl : isWs '"' = false) (by decide) key)
      · intro e es budget rest hd hf; cases es with
        | nil => exact parseSep_single (rfl : isWs ']' = false) (by decide) (ihV e budget (']' :: rest) (hd e (.head _)) (by simp only [Json.renderElemsL] at hf; omega) rfl)
        | cons x xs =>
            simp only [Json.renderElemsL, List.length_append, List.length_cons] at hf
            exact parseSep_cons (by rw [Json.renderElemsL, List.append_assoc]; exact ihV e budget (',' :: (Json.renderElemsL (x :: xs) ++ ']' :: rest)) (hd e (.head _)) (by omega) rfl)
              (by cases xs <;> simp only [Json.renderElemsL, List.append_assoc] <;> exact skipWs_renderL x _) (ihE x xs budget rest (fun y hy => hd y (.tail _ hy)) (by omega))
      · intro ⟨k, v⟩ ms budget rest hd hf
        have hstep (tail : List Char) (hv : parseVal f budget (Json.renderL v ++ tail) = .ok (v, tail)) : parseMember (parseVal f budget) (Json.renderStrL k ++ ':' :: (Json.renderL v ++ tail)) = .ok ((k, v), tail) := by
          simp only [parseMember, Json.renderStrL, List.cons_append, List.nil_append, List.append_assoc, skipWs_cons (rfl : isWs '"' = false), parseStr_render, Except.bind, skipWs_cons (rfl : isWs ':' = false), skipWs_renderL, hv, Except.map]
        cases ms with
        | nil => simp only [Json.renderMembersL, Json.renderStrL, List.length_append, List.length_cons] at hf; exact parseSep_single (rfl : isWs '}' = false) (by decide) (by rw [Json.renderMembersL, List.append_assoc]; exact hstep _ (ihV v budget ('}' :: rest) (hd (k, v) (.head _)) (by omega) rfl))
        | cons kv' ms =>
            rcases kv' with ⟨k', v'⟩; simp only [Json.renderMembersL, Json.renderStrL, List.length_append, List.length_cons] at hf
            exact parseSep_cons (by rw [Json.renderMembersL, List.append_assoc, List.cons_append, List.append_assoc]; exact hstep _ (ihV v budget (',' :: (Json.renderMembersL ((k', v') :: ms) ++ '}' :: rest)) (hd (k, v) (.head _)) (by omega) rfl))
              (by cases ms <;> rfl) (ihM (k', v') ms budget rest (fun y hy => hd y (.tail _ hy)) (by omega))

theorem parse_render {j : Json} {maxDepth : Nat} (h : j.depth ≤ maxDepth) : parse (Json.render j) maxDepth = .ok j := by
  have hv := (rt_all ((Json.renderL j).length + 1)).1 j maxDepth [] h (by omega) rfl
  simp only [List.append_nil] at hv; simp only [parse, Json.render, String.toList_ofList, hv, Except.bind, skipWs, List.isEmpty_nil, ↓reduceIte]

end Qed
