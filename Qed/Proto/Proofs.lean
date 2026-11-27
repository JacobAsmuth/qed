import Qed.Proto.Basic

namespace Qed.Proto

private def sliceList (buf : ByteArray) (pos limit : Nat) : List UInt8 := ((bytesToList buf).take limit).drop pos

/-! ## 1. Varint, Fixed32/64 & Prefix-Free Round-Trip Proofs -/

private theorem encodeVarintList_cons (n : Nat) : ∃ b bs, encodeVarintList n = b :: bs := by unfold encodeVarintList; split <;> exact ⟨_, _, rfl⟩

private theorem decodeVarintList_append (n : Nat) (rest : List UInt8) : decodeVarintList (encodeVarintList n ++ rest) = .ok (n, rest) := by
  induction n using Nat.strongRecOn generalizing rest with
  | ind n ih =>
      unfold encodeVarintList; by_cases hlt : n < 128
      · rw [ite_eq_left hlt, List.singleton_append, decodeVarintList, show (UInt8.ofNat n).toNat = n by simp; omega, ite_eq_left hlt]
      · rw [ite_eq_right hlt, List.cons_append, decodeVarintList, show (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 by simp; omega,
          ite_eq_right (by omega), ih (n / 128) (Nat.div_lt_self (by omega) (by decide)) rest]
        exact congrArg (fun k => Except.ok (k, rest)) (by omega)

private theorem decodeLEList_encodeLEList : ∀ (k n : Nat) (rest : List UInt8), decodeLEList k (encodeLEList k n ++ rest) = some (n % 256 ^ k, rest)
  | 0, _, _ => by simp [encodeLEList, decodeLEList, Nat.mod_one]
  | k + 1, n, rest => by
      simp only [encodeLEList, List.cons_append, decodeLEList, decodeLEList_encodeLEList k (n / 256) rest, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      have h2 := Nat.mod_add_div (n % (256 * 256 ^ k)) 256
      rw [Nat.mod_mod_of_dvd n (Nat.dvd_mul_right 256 (256 ^ k)), Nat.mod_mul_right_div_self] at h2
      rw [show (UInt8.ofNat (n % 256)).toNat = n % 256 by simp, Nat.pow_succ']; exact h2

private theorem splitExact_append : ∀ (xs rest : List UInt8), splitExact xs.length (xs ++ rest) = some (xs, rest)
  | [], _ => rfl | _ :: xs, rest => by simp [splitExact, splitExact_append xs rest]

private theorem decodeFieldList_append {fieldNum : Nat} (hf : 0 < fieldNum) (w : WireVal) (rest : List UInt8) :
    decodeFieldList (encodeFieldList fieldNum w ++ rest) = .ok ((fieldNum, w), rest) := by
  unfold encodeFieldList decodeFieldList; rw [List.append_assoc, decodeVarintList_append]
  have hwt : w.wireType < 8 := by cases w <;> dsimp only [WireVal.wireType] <;> decide
  have hpay : decodePayloadList w.wireType (encodePayloadList w ++ rest) = .ok (w, rest) := by
    cases w with
    | varint _ => simp only [WireVal.wireType, encodePayloadList, decodePayloadList, decodeVarintList_append, Except.map]
    | fixed64 v => simp only [WireVal.wireType, encodePayloadList, decodePayloadList, decodeLEExcept, decodeLEList_encodeLEList, Option.elim_some, Except.map]; rw [Nat.mod_eq_of_lt (show v.toNat < 256 ^ 8 from v.toBitVec.isLt), UInt64.ofNat_toNat]
    | fixed32 v => simp only [WireVal.wireType, encodePayloadList, decodePayloadList, decodeLEExcept, decodeLEList_encodeLEList, Option.elim_some, Except.map]; rw [Nat.mod_eq_of_lt (show v.toNat < 256 ^ 4 from v.toBitVec.isLt), UInt32.ofNat_toNat]
    | bytes b => simp only [WireVal.wireType, encodePayloadList, List.append_assoc, decodePayloadList, decodeVarintList_append, Except.bind,
        show b.size = (bytesToList b).length from rfl, splitExact_append, Option.elim_some, bytesOfList_bytesToList]
  simp only [Except.bind, Except.map, show (fieldNum * 8 + w.wireType) / 8 = fieldNum by omega,
    show (fieldNum * 8 + w.wireType) % 8 = w.wireType by omega, beq_eq_false_iff_ne.2 (Nat.ne_of_gt hf), Bool.false_eq_true, ↓reduceIte, hpay]

private theorem decodeFieldsAux_encodeFieldsList :
    ∀ (fields : List (Nat × WireVal)) (fuel : Nat) (acc : List (Nat × WireVal)),
      (∀ kw ∈ fields, 0 < kw.1) → (encodeFieldsList fields).length ≤ fuel → decodeFieldsAux fuel (encodeFieldsList fields) acc = .ok (acc.reverse ++ fields)
  | [], fuel, _, _, _ => by cases fuel <;> simp only [encodeFieldsList, decodeFieldsAux, List.append_nil]
  | (k, w) :: _, 0, _, _, hfuel => by obtain ⟨_, _, he⟩ := encodeVarintList_cons (k * 8 + w.wireType); simp only [encodeFieldsList, encodeFieldList, he, List.cons_append, List.length_cons] at hfuel; exact nomatch hfuel
  | (k, w) :: rest, f' + 1, acc, hpos, hfuel => by
      obtain ⟨b, bs, he⟩ := encodeVarintList_cons (k * 8 + w.wireType)
      simp only [encodeFieldsList, encodeFieldList, he, List.cons_append, List.length_cons, List.length_append] at hfuel ⊢
      simp only [decodeFieldsAux, Except.bind]
      rw [show b :: (bs ++ encodePayloadList w ++ encodeFieldsList rest) = encodeFieldList k w ++ encodeFieldsList rest by simp only [encodeFieldList, he, List.cons_append, List.append_assoc],
          decodeFieldList_append (hpos (k, w) (.head _))]
      dsimp only
      rw [decodeFieldsAux_encodeFieldsList rest f' ((k, w) :: acc) (fun kw hm => hpos kw (.tail _ hm)) (by omega)]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem decodeFieldsSpec_encodeFieldsSpec (fields : List (Nat × WireVal)) (hpos : ∀ kw ∈ fields, 0 < kw.1) :
    decodeFieldsSpec (encodeFieldsSpec fields) = .ok fields := by
  simpa [decodeFieldsSpec, encodeFieldsSpec, ByteArray.size] using decodeFieldsAux_encodeFieldsList fields (encodeFieldsList fields).length [] hpos (Nat.le_refl _)

/-! ## 2. Framing Non-Smuggling, Cursor DoS Bound & Forward Compatibility -/

theorem decodeFrameList_append (payload rest : List UInt8) : decodeFrameList (encodeFrameList payload ++ rest) = .ok (payload, rest) := by
  simp [encodeFrameList, decodeFrameList, List.append_assoc, decodeVarintList_append, Except.bind, splitExact_append]

private theorem bind_eq_ok {x : Except String α} {f : α → Except String β} {b : β} (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with | error _ => cases h | ok a => exact ⟨a, rfl, h⟩
private theorem map_eq_ok {x : Except String α} {f : α → β} {b : β} (h : x.map f = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with | error _ => cases h | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

private theorem readVarintAt_advances (buf : ByteArray) (pos limit : Nat) {n pos' : Nat} (h : readVarintAt buf pos limit = .ok (n, pos')) : pos < pos' ∧ pos' ≤ limit := by
  induction hfuel : limit - pos generalizing pos n with
  | zero => unfold readVarintAt at h; rw [dite_eq_right (by omega)] at h; cases h
  | succ _ ih =>
      unfold readVarintAt at h; split at h <;> try cases h
      dsimp only at h; split at h
      · cases h; omega
      · obtain ⟨⟨_, _⟩, hr, heq⟩ := map_eq_ok h; cases heq; have := ih (pos + 1) hr (by omega); omega

theorem cursor_strictly_advances (buf : ByteArray) (pos limit : Nat) {fw : Nat × WireVal} {pos' : Nat} (h : readFieldAt buf pos limit = .ok (fw, pos')) : pos < pos' ∧ pos' ≤ limit := by
  obtain ⟨⟨tag, afterTag⟩, htag, h1⟩ := bind_eq_ok h
  have := readVarintAt_advances buf pos limit htag; dsimp only at h1; split at h1 <;> try cases h1
  obtain ⟨⟨_, _⟩, hpay, heq⟩ := map_eq_ok h1; cases heq
  generalize tag % 8 = wt at hpay
  match wt with
  | 0 => obtain ⟨⟨_, _⟩, hr, heq⟩ := map_eq_ok hpay; cases heq; have := readVarintAt_advances buf afterTag limit hr; omega
  | 1 | 5 =>
      obtain ⟨⟨_, _⟩, hr, heq⟩ := map_eq_ok hpay; cases heq; unfold readFixedAt at hr; split at hr
      · have := (Prod.mk.inj (Except.ok.inj hr)).2; dsimp only; omega
      · cases hr
  | 2 => obtain ⟨⟨_, _⟩, hr, heq⟩ := bind_eq_ok hpay; have := readVarintAt_advances buf afterTag limit hr; dsimp only at heq; split at heq <;> cases heq; omega
  | 3 | 4 | _ + 6 => cases hpay

theorem skipUnknown_preserves_lookup_prefix (k : Nat) : ∀ (unknown known : List (Nat × WireVal)), (∀ u ∈ unknown, u.1 ≠ k) → lookupField k (unknown ++ known) = lookupField k known
  | [], _, _ => rfl | (uk, uw) :: rest, known, hne => by simp only [List.cons_append, lookupField, beq_eq_false_iff_ne.2 (hne (uk, uw) (List.mem_cons_self ..)), Bool.false_eq_true, ↓reduceIte, skipUnknown_preserves_lookup_prefix k rest known fun u hu => hne u (List.mem_cons_of_mem _ hu)]
theorem skipUnknown_preserves_lookup_suffix (k : Nat) : ∀ (known unknown : List (Nat × WireVal)), (∀ u ∈ unknown, u.1 ≠ k) → lookupField k (known ++ unknown) = lookupField k known
  | [], unknown, hne => by simpa using skipUnknown_preserves_lookup_prefix k unknown [] hne
  | (kk, _) :: rest, unknown, hne => by cases h : (kk == k) <;> simp only [List.cons_append, lookupField, h, Bool.false_eq_true, ↓reduceIte, skipUnknown_preserves_lookup_suffix k rest unknown hne]
private theorem lookupRepeated_eq_nil_of_ne (k : Nat) : ∀ (unknown : List (Nat × WireVal)), (∀ u ∈ unknown, u.1 ≠ k) → lookupRepeated k unknown = []
  | [], _ => rfl
  | (uk, uw) :: rest, hne => by
      simp only [lookupRepeated, beq_eq_false_iff_ne.2 (hne (uk, uw) (.head _)), Bool.false_eq_true, ↓reduceIte]
      exact lookupRepeated_eq_nil_of_ne k rest fun u hu => hne u (.tail _ hu)

theorem skipUnknown_preserves_repeated_suffix (k : Nat) : ∀ (known unknown : List (Nat × WireVal)), (∀ u ∈ unknown, u.1 ≠ k) → lookupRepeated k (known ++ unknown) = lookupRepeated k known
  | [], unknown, hne => lookupRepeated_eq_nil_of_ne k unknown hne
  | (kk, _) :: rest, unknown, hne => by cases h : (kk == k) <;> simp only [List.cons_append, lookupRepeated, h, Bool.false_eq_true, ↓reduceIte, skipUnknown_preserves_repeated_suffix k rest unknown hne]

/-! ## 3. `@[csimp]` Fast Writer & Borrowed-Cursor Equivalence -/

private theorem bytesToList_push (b : ByteArray) (x : UInt8) : bytesToList (b.push x) = bytesToList b ++ [x] := by cases b; simp [bytesToList, ByteArray.push]
private theorem bytesToList_inj {a b : ByteArray} (h : bytesToList a = bytesToList b) : a = b := by rw [← bytesOfList_bytesToList a, ← bytesOfList_bytesToList b, h]

private theorem writeVarint_toList (n : Nat) (buf : ByteArray) : bytesToList (writeVarint buf n) = bytesToList buf ++ encodeVarintList n := by
  induction n using Nat.strongRecOn generalizing buf with
  | ind n ih =>
      unfold writeVarint encodeVarintList; by_cases hlt : n < 128
      · rw [ite_eq_left hlt, ite_eq_left hlt, bytesToList_push]
      · rw [ite_eq_right hlt, ite_eq_right hlt, ih (n / 128) (Nat.div_lt_self (by omega) (by decide)), bytesToList_push, List.append_assoc]; rfl

private theorem writeFieldsLoop_toList : ∀ (fields : List (Nat × WireVal)) (buf : ByteArray), bytesToList (writeFieldsLoop buf fields) = bytesToList buf ++ encodeFieldsList fields
  | [], _ => by simp [writeFieldsLoop, encodeFieldsList]
  | (_, w) :: rest, buf => by
      have hpay (b : ByteArray) : bytesToList (writePayload b w) = bytesToList b ++ encodePayloadList w := by
        cases w with
        | varint n => exact writeVarint_toList n b
        | fixed32 _ | fixed64 _ => simp [writePayload, encodePayloadList, encodeLEList, bytesToList_push, List.append_assoc, Nat.div_div_eq_div_mul]
        | bytes bs => have hw := writeVarint_toList bs.size b; simp only [writePayload, encodePayloadList] at hw ⊢; simp [hw, List.append_assoc]
      simp [writeFieldsLoop, encodeFieldsList, encodeFieldList, writeFieldsLoop_toList rest, hpay, writeVarint_toList, List.append_assoc]

@[csimp] theorem encodeFieldsSpec_eq_fast : @encodeFieldsSpec = @encodeFieldsFast := by
  funext fields; apply bytesToList_inj; simp [encodeFieldsSpec, encodeFieldsFast, writeFieldsLoop_toList, show bytesToList (ByteArray.emptyWithCapacity 64) = [] from rfl]

private theorem sliceList_eq_nil {buf : ByteArray} {pos limit : Nat} (h : limit ≤ pos) : sliceList buf pos limit = [] := List.drop_eq_nil_of_le (Nat.le_trans (List.length_take_le limit _) h)
private theorem sliceList_full (buf : ByteArray) : sliceList buf 0 buf.size = bytesToList buf := by unfold sliceList; rw [show buf.size = (bytesToList buf).length from rfl, List.take_length, List.drop_zero]
private theorem sliceList_cons {buf : ByteArray} {pos limit : Nat} (h : pos < limit ∧ limit ≤ buf.size) : sliceList buf pos limit = (buf[pos]'(by omega)) :: sliceList buf (pos + 1) limit := by
  cases buf with | mk arr => have hlt : pos < (arr.toList.take limit).length := by rw [List.length_take_of_le h.2]; exact h.1
                             unfold sliceList; rw [← List.getElem_cons_drop hlt, List.getElem_take]; rfl

private theorem readVarintAt_eq_spec (buf : ByteArray) (pos limit : Nat) (hlim : limit ≤ buf.size) :
    (readVarintAt buf pos limit).map (fun (n, p') => (n, sliceList buf p' limit)) = decodeVarintList (sliceList buf pos limit) := by
  induction hfuel : limit - pos generalizing pos with
  | zero => unfold readVarintAt; rw [dite_eq_right (by omega), sliceList_eq_nil (by omega)]; rfl
  | succ _ ih =>
      have hcond : pos < limit ∧ limit ≤ buf.size := ⟨by omega, hlim⟩
      rw [sliceList_cons hcond]; unfold readVarintAt; rw [dite_eq_left hcond]
      by_cases hb : (buf[pos]'(by omega)).toNat < 128
      · simp [decodeVarintList, hb, Except.map]
      · simp only [ite_eq_right hb, decodeVarintList, ← ih (pos + 1) (by omega)]; cases readVarintAt buf (pos + 1) limit <;> rfl

private theorem splitExact_sliceList (buf : ByteArray) :
    ∀ (len pos limit : Nat), pos ≤ limit → limit ≤ buf.size →
      splitExact len (sliceList buf pos limit) = if pos + len ≤ limit then some (sliceList buf pos (pos + len), sliceList buf (pos + len) limit) else none
  | 0, pos, _, hp, _ => by simp [splitExact, hp, sliceList_eq_nil (Nat.le_refl pos)]
  | len + 1, pos, limit, _, hlim => by
      by_cases hlt : pos < limit
      · rw [sliceList_cons ⟨hlt, hlim⟩, splitExact, splitExact_sliceList buf len (pos + 1) limit (by omega) hlim]
        by_cases hfit : pos + 1 + len ≤ limit
        · rw [ite_eq_left hfit, ite_eq_left (by omega), show pos + (len + 1) = pos + 1 + len by omega, sliceList_cons (pos := pos) (limit := pos + 1 + len) ⟨by omega, by omega⟩]; rfl
        · rw [ite_eq_right hfit, ite_eq_right (by omega)]; rfl
      · rw [sliceList_eq_nil (by omega), splitExact, ite_eq_right (by omega)]

private theorem decodeLEList_none_of_lt : ∀ {k : Nat} {xs : List UInt8}, xs.length < k → decodeLEList k xs = none
  | 0, _, h => nomatch h | _ + 1, [], _ => rfl | k + 1, _ :: _, h => by simp [decodeLEList, decodeLEList_none_of_lt (k := k) (by simpa using h)]

private theorem readFixedAt_eq_spec {α : Type} (k : Nat) (hk : 0 < k) (mk : Nat → α) (err : String) {buf : ByteArray} {pos limit : Nat} (hlim : limit ≤ buf.size) (val : pos + k ≤ buf.size → Nat)
    (hval : ∀ h : pos + k ≤ limit ∧ limit ≤ buf.size, decodeLEList k (sliceList buf pos limit) = some (val (by omega), sliceList buf (pos + k) limit)) :
    (readFixedAt k mk err buf pos limit val).map (fun (v, p') => (v, sliceList buf p' limit)) = decodeLEExcept k mk err (sliceList buf pos limit) := by
  unfold readFixedAt; by_cases h : pos + k ≤ limit ∧ limit ≤ buf.size
  · rw [dite_eq_left h, decodeLEExcept, hval h]; rfl
  · have : (sliceList buf pos limit).length ≤ limit - pos := by have := List.length_take_le limit (bytesToList buf); simp [sliceList]; omega
    rw [dite_eq_right h, decodeLEExcept, decodeLEList_none_of_lt (by omega)]; rfl

private theorem map_wire_eq {α : Type} (ctor : α → WireVal) {r : Except String (α × Nat)} {s : Except String (α × List UInt8)} {buf : ByteArray} {limit : Nat}
    (h : r.map (fun (v, p') => (v, sliceList buf p' limit)) = s) : (r.map fun (v, p') => (ctor v, p')).map (fun (w, p') => (w, sliceList buf p' limit)) = s.map fun (v, rem) => (ctor v, rem) := by
  rw [← h]; cases r <;> rfl

private theorem decodeLEList_4_slice {buf : ByteArray} {pos limit : Nat} (h : pos + 4 ≤ limit ∧ limit ≤ buf.size) :
    decodeLEList 4 (sliceList buf pos limit) = some (readLE4At buf pos (Nat.le_trans h.1 h.2), sliceList buf (pos + 4) limit) := by
  rw [sliceList_cons ⟨by omega, h.2⟩, sliceList_cons ⟨by omega, h.2⟩, sliceList_cons ⟨by omega, h.2⟩, sliceList_cons ⟨by omega, h.2⟩]
  simp only [readLE4At, decodeLEList, Option.map_some, Option.some.injEq, Prod.mk.injEq, Nat.add_assoc, Nat.reduceAdd, and_true]; omega

private theorem readPayloadAt_eq_spec (wt : Nat) (buf : ByteArray) (pos limit : Nat) (hlim : limit ≤ buf.size) :
    (readPayloadAt wt buf pos limit).map (fun (w, p') => (w, sliceList buf p' limit)) = decodePayloadList wt (sliceList buf pos limit) := by
  match wt with
  | 0 => exact map_wire_eq .varint (readVarintAt_eq_spec buf pos limit hlim)
  | 1 => exact map_wire_eq .fixed64 (readFixedAt_eq_spec 8 (by decide) UInt64.ofNat "protobuf: truncated fixed64" hlim _ fun h => by
      have h4b := decodeLEList_4_slice (buf := buf) (pos := pos + 4) (limit := limit) ⟨by omega, h.2⟩
      rw [sliceList_cons ⟨by omega, h.2⟩, sliceList_cons ⟨by omega, h.2⟩, sliceList_cons ⟨by omega, h.2⟩, sliceList_cons ⟨by omega, h.2⟩]
      simp only [decodeLEList, Nat.add_assoc, Nat.reduceAdd, h4b, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true, readLE4At]; omega)
  | 5 => exact map_wire_eq .fixed32 (readFixedAt_eq_spec 4 (by decide) UInt32.ofNat "protobuf: truncated fixed32" hlim _ decodeLEList_4_slice)
  | 2 =>
      simp only [readPayloadAt, decodePayloadList]; rw [← readVarintAt_eq_spec buf pos limit hlim]
      cases hr : readVarintAt buf pos limit with | error _ => rfl | ok lp =>
        rcases lp with ⟨len, afterLen⟩; have hAdv := readVarintAt_advances buf pos limit hr
        dsimp only [Except.map, Except.bind]; rw [splitExact_sliceList buf len afterLen limit hAdv.2 hlim]
        by_cases hfit : afterLen + len ≤ limit
        · rw [ite_eq_left hfit, ite_eq_left ⟨hfit, hlim⟩, show buf.extract afterLen (afterLen + len) = bytesOfList (sliceList buf afterLen (afterLen + len)) from bytesToList_inj (by simp only [bytesToList, sliceList, ByteArray.data_extract, Array.toList_extract, List.drop_take])]; rfl
        · rw [ite_eq_right hfit, ite_eq_right (fun h => hfit h.1)]; rfl
  | 3 | 4 | _ + 6 => rfl

private theorem readFieldAt_eq_spec (buf : ByteArray) (pos limit : Nat) (hlim : limit ≤ buf.size) :
    (readFieldAt buf pos limit).map (fun (fw, p') => (fw, sliceList buf p' limit)) = decodeFieldList (sliceList buf pos limit) := by
  unfold readFieldAt decodeFieldList; rw [← readVarintAt_eq_spec buf pos limit hlim]
  cases readVarintAt buf pos limit with | error _ => rfl | ok tp =>
    rcases tp with ⟨tag, afterTag⟩; dsimp only [Except.map, Except.bind]
    by_cases hf0 : (tag / 8 == 0) = true
    · rw [ite_eq_left hf0, ite_eq_left hf0]
    · rw [ite_eq_right hf0, ite_eq_right hf0, ← readPayloadAt_eq_spec (tag % 8) buf afterTag limit hlim]
      cases readPayloadAt (tag % 8) buf afterTag limit <;> rfl

private theorem readVarintAt_fast_byte {buf : ByteArray} {pos limit : Nat} (h : pos < limit ∧ limit ≤ buf.size)
    (hb : (buf[pos]'(Nat.lt_of_lt_of_le h.1 h.2)).toNat < 128) :
    readVarintAt buf pos limit = .ok ((buf[pos]'(Nat.lt_of_lt_of_le h.1 h.2)).toNat, pos + 1) := by
  unfold readVarintAt; rw [dite_eq_left h, ite_eq_left hb]

private theorem readFieldAt_fast_twoByte {buf : ByteArray} {pos limit : Nat} (h2 : pos + 1 < limit ∧ limit ≤ buf.size)
    {h0 : pos < buf.size} {h1 : pos + 1 < buf.size} (hb0 : buf[pos].toNat < 128) (hb1 : buf[pos + 1].toNat < 128) (hfn : (buf[pos].toNat / 8 != 0) = true) :
    ((buf[pos].toNat % 8 == 0) = true → readFieldAt buf pos limit = .ok ((buf[pos].toNat / 8, .varint buf[pos + 1].toNat), pos + 2)) ∧
    ((buf[pos].toNat % 8 == 2) = true → readFieldAt buf pos limit =
      if pos + 2 + buf[pos + 1].toNat ≤ limit then .ok ((buf[pos].toNat / 8, .bytes (buf.extract (pos + 2) (pos + 2 + buf[pos + 1].toNat))), pos + 2 + buf[pos + 1].toNat)
      else .error "protobuf: truncated length-delimited field") := by
  have hv1 := readVarintAt_fast_byte ⟨Nat.lt_trans (Nat.lt_succ_self pos) h2.1, h2.2⟩ hb0
  have hv2 := readVarintAt_fast_byte h2 hb1
  have hfn0 : (buf[pos].toNat / 8 == 0) = false := beq_eq_false_iff_ne.2 (bne_iff_ne.1 hfn)
  refine ⟨fun hwt => by simp only [readFieldAt, hv1, Except.bind, hfn0, Bool.false_eq_true, ↓reduceIte, beq_iff_eq.1 hwt, readPayloadAt, hv2, Except.map], fun hwt => ?_⟩
  by_cases hle : pos + 2 + buf[pos + 1].toNat ≤ limit
  · rw [ite_eq_left hle]; simp only [readFieldAt, hv1, Except.bind, hfn0, Bool.false_eq_true, ↓reduceIte, beq_iff_eq.1 hwt, readPayloadAt, hv2, hle, h2.2, and_self, Except.map]
  · rw [ite_eq_right hle]; simp only [readFieldAt, hv1, Except.bind, hfn0, Bool.false_eq_true, ↓reduceIte, beq_iff_eq.1 hwt, readPayloadAt, hv2, hle, false_and, Except.map]

private theorem readFieldsLoop_eq_spec (buf : ByteArray) (fuel pos limit : Nat) (acc : List (Nat × WireVal)) (hp : pos ≤ limit) (hlim : limit ≤ buf.size) :
    readFieldsLoop fuel buf pos limit acc = decodeFieldsAux fuel (sliceList buf pos limit) acc := by
  induction fuel generalizing pos acc with
  | zero | succ f' ih =>
      by_cases heq : (pos == limit) = true
      · cases beq_iff_eq.1 heq; unfold readFieldsLoop; rw [ite_eq_left heq, sliceList_eq_nil (Nat.le_refl _)]; rfl
      · have hlt : pos < limit := Nat.lt_of_le_of_ne hp (beq_eq_false_iff_ne.1 (Bool.eq_false_iff.2 heq))
        first
        | (unfold readFieldsLoop; rw [ite_eq_right heq, sliceList_cons ⟨hlt, hlim⟩]; rfl)
        | (have hstep := readFieldAt_eq_spec buf pos limit hlim
           have hfb : (match readFieldAt buf pos limit with | .error e => .error e | .ok (fw, p') => readFieldsLoop f' buf p' limit (fw :: acc)) = decodeFieldsAux (f' + 1) (sliceList buf pos limit) acc := by
             rw [sliceList_cons ⟨hlt, hlim⟩] at hstep ⊢; unfold decodeFieldsAux; dsimp only [Except.bind]; rw [← hstep]
             cases hrf : readFieldAt buf pos limit with | error _ => rfl | ok fwp => exact ih fwp.2 (fwp.1 :: acc) (cursor_strictly_advances buf pos limit hrf).2
           unfold readFieldsLoop; rw [ite_eq_right heq]; dsimp only
           by_cases h2 : pos + 1 < limit ∧ limit ≤ buf.size
           · rw [dite_eq_left h2]
             have h1 : pos + 1 < buf.size := Nat.lt_of_lt_of_le h2.1 h2.2; have h0 : pos < buf.size := Nat.lt_trans (Nat.lt_succ_self pos) h1
             by_cases hlt128 : (decide (buf[pos].toNat < 128) && decide (buf[pos + 1].toNat < 128)) = true
             · rw [ite_eq_left hlt128]; rcases Bool.and_eq_true_iff.1 hlt128 with ⟨hb0, hb1⟩
               by_cases hfn : (buf[pos].toNat / 8 != 0) = true
               · rw [ite_eq_left hfn]; have ⟨hvar, hbyt⟩ := readFieldAt_fast_twoByte h2 (of_decide_eq_true hb0) (of_decide_eq_true hb1) hfn
                 by_cases hwt0 : (buf[pos].toNat % 8 == 0) = true
                 · rw [ite_eq_left hwt0, ← hfb, hvar hwt0]
                 · rw [ite_eq_right hwt0]
                   by_cases hwt2 : (buf[pos].toNat % 8 == 2) = true
                   · rw [ite_eq_left hwt2, ← hfb, hbyt hwt2]; split <;> rfl
                   · rw [ite_eq_right hwt2]; exact hfb
               · rw [ite_eq_right hfn]; exact hfb
             · rw [ite_eq_right hlt128]; exact hfb
           · rw [dite_eq_right h2]; exact hfb)

@[csimp] theorem decodeFieldsSpec_eq_fast : @decodeFieldsSpec = @decodeFieldsFast := by
  funext buf; unfold decodeFieldsSpec decodeFieldsFast; rw [readFieldsLoop_eq_spec buf buf.size 0 buf.size [] (Nat.zero_le _) (Nat.le_refl _), sliceList_full]

/-! ## 4. Hex `ByteArray` Round-Trip Theorem -/

private theorem decodeHexList_encodeHexList : ∀ (xs : List UInt8), decodeHexList (encodeHexList xs) = some xs
  | [] => rfl
  | b :: bs => by
      have hb : b.toNat < 256 := b.toBitVec.isLt
      have hrec : UInt8.ofNat (b.toNat / 16 * 16 + b.toNat % 16) = b := by rw [show b.toNat / 16 * 16 + b.toNat % 16 = b.toNat by omega]; exact UInt8.ofNat_toNat
      simp only [encodeHexList, decodeHexList, unhexByte, unhexNat?_hexDigitLower (show b.toNat / 16 < 16 by omega),
        unhexNat?_hexDigitLower (show b.toNat % 16 < 16 by omega), Option.bind_some, Option.map_some, hrec, decodeHexList_encodeHexList bs]

theorem decodeHex_encodeHex (b : ByteArray) : decodeHex (encodeHex b) = .ok b := by simp [encodeHex, decodeHex, String.toList_ofList, decodeHexList_encodeHexList]

theorem encodeHex_encode_injective {α : Type} {p : String} (enc : α → ByteArray) (dec : ByteArray → Except String α) (hinv : ∀ x, dec (enc x) = .ok x)
    {a b : α} (h : p ++ encodeHex (enc a) = p ++ encodeHex (enc b)) : a = b := by
  have heq : encodeHex (enc a) = encodeHex (enc b) := String.toList_injective (List.append_cancel_left (as := p.toList) (by simpa [String.toList_append] using congrArg String.toList h))
  have hba : enc a = enc b := by simpa [decodeHex_encodeHex] using congrArg decodeHex heq
  simpa [hinv] using congrArg dec hba

private theorem encodeHexLoop_eq_spec (b : ByteArray) (i : Nat) (acc : List Char) : encodeHexLoop b i acc = acc.reverse ++ encodeHexList (sliceList b i b.size) := by
  induction hfuel : b.size - i generalizing i acc with
  | zero => unfold encodeHexLoop; rw [dite_eq_right (by omega), sliceList_eq_nil (by omega)]; simp [encodeHexList]
  | succ _ ih => unfold encodeHexLoop; rw [dite_eq_left (by omega), ih (i + 1) _ (by omega), sliceList_cons (pos := i) ⟨by omega, Nat.le_refl _⟩]; simp [encodeHexList, List.append_assoc]
@[csimp] theorem encodeHex_eq_fast : @encodeHex = @encodeHexFast := by funext b; simp [encodeHex, encodeHexFast, encodeHexLoop_eq_spec, sliceList_full]

private theorem decodeHexBuf_eq_spec : ∀ (cs : List Char) (out : ByteArray), (decodeHexBuf cs out).map bytesToList = (decodeHexList cs).map (bytesToList out ++ ·)
  | [], _ => by simp [decodeHexBuf, decodeHexList] | [_], _ => rfl
  | hi :: lo :: rest, out => by
      unfold decodeHexBuf decodeHexList; cases unhexByte hi lo with | none => rfl | some b =>
        dsimp only [Option.bind]; rw [decodeHexBuf_eq_spec rest (out.push b), bytesToList_push]; cases decodeHexList rest <;> simp [List.append_assoc]
@[csimp] theorem decodeHex_eq_fast : @decodeHex = @decodeHexFast := by
  funext s; unfold decodeHex decodeHexFast; have h := decodeHexBuf_eq_spec s.toList (ByteArray.emptyWithCapacity (s.utf8ByteSize / 2))
  cases hbuf : decodeHexBuf s.toList _ <;> cases hlst : decodeHexList s.toList <;> rw [hbuf, hlst] at h <;> cases h <;> first | rfl | exact congrArg Except.ok (bytesOfList_bytesToList _)

end Qed.Proto
