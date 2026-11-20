import Qed.Proto.Basic

namespace Qed.Proto

/-! ## 1. Varint, Fixed32, Fixed64 & Split Prefix-Free Round-Trip Proofs -/

theorem encodeVarintList_pos (n : Nat) : 0 < (encodeVarintList n).length := by
  unfold encodeVarintList
  split <;> simp

theorem decodeVarintList_append (n : Nat) (rest : List UInt8) :
    decodeVarintList (encodeVarintList n ++ rest) = .ok (n, rest) := by
  induction n using Nat.strongRecOn generalizing rest with
  | ind n ih =>
      unfold encodeVarintList
      by_cases hlt : n < 128
      · rw [if_pos hlt, List.singleton_append]
        unfold decodeVarintList
        have hbn : (UInt8.ofNat n).toNat = n := by simp; omega
        rw [hbn, if_pos hlt]
      · rw [if_neg hlt, List.cons_append]
        unfold decodeVarintList
        have hbn : (UInt8.ofNat (n % 128 + 128)).toNat = n % 128 + 128 := by simp; omega
        have hge : ¬ (n % 128 + 128 < 128) := by omega
        have hdiv : n / 128 < n := Nat.div_lt_self (by omega) (by decide)
        rw [hbn, if_neg hge]
        simp only [ih (n / 128) hdiv rest, bind, Except.bind, pure, Except.pure]
        have hrec : n % 128 + 128 - 128 + 128 * (n / 128) = n := by omega
        rw [hrec]

theorem uint8_ext {a b : UInt8} (h : a.toNat = b.toNat) : a = b :=
  UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

private theorem uint32_ext {a b : UInt32} (h : a.toNat = b.toNat) : a = b :=
  UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

private theorem uint64_ext {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem decodeFixed32List_append (v : UInt32) (rest : List UInt8) :
    decodeFixed32List (encodeFixed32List v ++ rest) = .ok (v, rest) := by
  have hn' : v.toNat < 4294967296 := v.toBitVec.isLt
  unfold encodeFixed32List decodeFixed32List
  simp only [List.cons_append, List.nil_append]
  congr 1
  apply Prod.ext
  · apply uint32_ext
    change (v.toNat % 256 % 256
      + 256 * (v.toNat / 256 % 256 % 256)
      + 65536 * (v.toNat / 65536 % 256 % 256)
      + 16777216 * (v.toNat / 16777216 % 256 % 256)) % 4294967296 = v.toNat
    omega
  · rfl

theorem decodeFixed64List_append (v : UInt64) (rest : List UInt8) :
    decodeFixed64List (encodeFixed64List v ++ rest) = .ok (v, rest) := by
  have hn' : v.toNat < 18446744073709551616 := v.toBitVec.isLt
  unfold encodeFixed64List decodeFixed64List
  simp only [List.cons_append, List.nil_append]
  congr 1
  apply Prod.ext
  · apply uint64_ext
    change (v.toNat % 256 % 256
      + 256 * (v.toNat / 256 % 256 % 256)
      + 65536 * (v.toNat / 65536 % 256 % 256)
      + 16777216 * (v.toNat / 16777216 % 256 % 256)
      + 4294967296 * (v.toNat / 4294967296 % 256 % 256)
      + 1099511627776 * (v.toNat / 1099511627776 % 256 % 256)
      + 281474976710656 * (v.toNat / 281474976710656 % 256 % 256)
      + 72057594037927936 * (v.toNat / 72057594037927936 % 256 % 256)) % 18446744073709551616 = v.toNat
    omega
  · rfl

theorem splitExact_append :
    ∀ (xs rest : List UInt8), splitExact xs.length (xs ++ rest) = some (xs, rest)
  | [], rest => rfl
  | _ :: xs, rest => by
      simp [splitExact, splitExact_append xs rest]

theorem bytesToList_length (b : ByteArray) : (bytesToList b).length = b.size := by
  cases b; rfl

theorem decodePayloadList_append (w : WireVal) (rest : List UInt8) :
    decodePayloadList w.wireType (encodePayloadList w ++ rest) = .ok (w, rest) := by
  cases w with
  | varint n =>
      simp [WireVal.wireType, encodePayloadList, decodePayloadList,
            decodeVarintList_append, bind, Except.bind, pure, Except.pure]
  | fixed64 v =>
      simp [WireVal.wireType, encodePayloadList, decodePayloadList,
            decodeFixed64List_append, bind, Except.bind, pure, Except.pure]
  | bytes b =>
      simp only [WireVal.wireType, encodePayloadList, List.append_assoc, decodePayloadList,
                 decodeVarintList_append, bind, Except.bind]
      rw [← bytesToList_length b, splitExact_append]
      simp [bytesOfList_bytesToList]
  | fixed32 v =>
      simp [WireVal.wireType, encodePayloadList, decodePayloadList,
            decodeFixed32List_append, bind, Except.bind, pure, Except.pure]

theorem wireType_lt_eight (w : WireVal) : w.wireType < 8 := by
  cases w <;> simp [WireVal.wireType]

theorem encodeFieldList_pos (fieldNum : Nat) (w : WireVal) :
    0 < (encodeFieldList fieldNum w).length := by
  unfold encodeFieldList
  rw [List.length_append]
  have := encodeVarintList_pos (fieldNum * 8 + w.wireType)
  omega

theorem decodeFieldList_append {fieldNum : Nat} (hf : 0 < fieldNum) (w : WireVal) (rest : List UInt8) :
    decodeFieldList (encodeFieldList fieldNum w ++ rest) = .ok ((fieldNum, w), rest) := by
  unfold encodeFieldList decodeFieldList
  rw [List.append_assoc, decodeVarintList_append]
  have hwt := wireType_lt_eight w
  have hdiv : (fieldNum * 8 + w.wireType) / 8 = fieldNum := by omega
  have hmod : (fieldNum * 8 + w.wireType) % 8 = w.wireType := by omega
  have hne : (fieldNum == 0) = false := beq_eq_false_iff_ne.2 (by omega)
  simp [bind, Except.bind, pure, Except.pure, hdiv, hmod, hne, decodePayloadList_append]

private theorem decodeFieldsAux_encodeFieldsList :
    ∀ (fields : List (Nat × WireVal)) (fuel : Nat) (acc : List (Nat × WireVal)),
      (∀ kw ∈ fields, 0 < kw.1) →
      (encodeFieldsList fields).length ≤ fuel →
      decodeFieldsAux fuel (encodeFieldsList fields) acc = .ok (acc.reverse ++ fields)
  | [], fuel, acc, _, _ => by
      cases fuel <;> simp [encodeFieldsList, decodeFieldsAux]
  | (k, w) :: rest, fuel, acc, hpos, hfuel => by
      have hk : 0 < k := hpos (k, w) (by simp)
      have hrest : ∀ kw ∈ rest, 0 < kw.1 := fun kw hm => hpos kw (by simp [hm])
      have hlen : 0 < (encodeFieldList k w).length := encodeFieldList_pos k w
      have htot : (encodeFieldsList ((k, w) :: rest)).length =
          (encodeFieldList k w).length + (encodeFieldsList rest).length := by
        simp [encodeFieldsList, List.length_append]
      cases fuel with
      | zero => omega
      | succ f' =>
          have hf' : (encodeFieldsList rest).length ≤ f' := by omega
          unfold encodeFieldsList
          cases henc : encodeFieldList k w ++ encodeFieldsList rest with
          | nil =>
              have : (encodeFieldList k w ++ encodeFieldsList rest).length = 0 := by rw [henc]; rfl
              rw [List.length_append] at this
              omega
          | cons b bs =>
              unfold decodeFieldsAux
              dsimp only [bind, Except.bind]
              rw [← henc, decodeFieldList_append hk w (encodeFieldsList rest)]
              dsimp only
              rw [decodeFieldsAux_encodeFieldsList rest f' ((k, w) :: acc) hrest hf']
              simp [List.append_assoc]

theorem decodeFieldsSpec_encodeFieldsSpec (fields : List (Nat × WireVal))
    (hpos : ∀ kw ∈ fields, 0 < kw.1) :
    decodeFieldsSpec (encodeFieldsSpec fields) = .ok fields := by
  unfold decodeFieldsSpec encodeFieldsSpec
  dsimp only
  rw [bytesToList_bytesOfList]
  simpa using decodeFieldsAux_encodeFieldsList fields (encodeFieldsList fields).length [] hpos (Nat.le_refl _)

/-! ## 2. Framing Non-Smuggling, Cursor DoS Bound & Forward Compatibility -/

/-- Self-delimiting frame non-smuggling: decoding a framed Protobuf message concatenated with
    arbitrary trailing bytes recovers the exact frame and leaves `rest` unconsumed. -/
theorem decodeFrameList_append (payload rest : List UInt8) :
    decodeFrameList (encodeFrameList payload ++ rest) = .ok (payload, rest) := by
  unfold encodeFrameList decodeFrameList
  rw [List.append_assoc, decodeVarintList_append]
  dsimp only [bind, Except.bind]
  rw [splitExact_append]

theorem readVarintAt_advances (buf : ByteArray) (pos limit : Nat) {n pos' : Nat}
    (h : readVarintAt buf pos limit = .ok (n, pos')) :
    pos < pos' ∧ pos' ≤ limit := by
  induction hfuel : limit - pos generalizing pos n with
  | zero =>
      unfold readVarintAt at h
      have hnot : ¬ (pos < limit ∧ limit ≤ buf.size) := by omega
      rw [dif_neg hnot] at h
      cases h
  | succ d ih =>
      unfold readVarintAt at h
      by_cases hcond : pos < limit ∧ limit ≤ buf.size
      · rw [dif_pos hcond] at h
        by_cases hb : (buf[pos]'(Nat.lt_of_lt_of_le hcond.1 hcond.2)).toNat < 128
        · rw [if_pos hb] at h
          injection h with hpair
          injection hpair with _ hp'
          omega
        · rw [if_neg hb] at h
          dsimp only [bind, Except.bind, pure, Except.pure] at h
          cases hr : readVarintAt buf (pos + 1) limit with
          | error _ => rw [hr] at h; cases h
          | ok hp =>
              rcases hp with ⟨hi, pos''⟩
              rw [hr] at h
              injection h with hpair
              injection hpair with _ hp'
              subst hp'
              have hstep := ih (pos + 1) hr (by omega)
              omega
      · rw [dif_neg hcond] at h
        cases h

theorem readPayloadAt_bounds (wt : Nat) (buf : ByteArray) (pos limit : Nat) {w : WireVal} {pos' : Nat}
    (h : readPayloadAt wt buf pos limit = .ok (w, pos')) :
    pos ≤ pos' ∧ pos' ≤ limit := by
  unfold readPayloadAt at h
  match wt with
  | 0 =>
      dsimp only [bind, Except.bind, pure, Except.pure] at h
      cases hr : readVarintAt buf pos limit with
      | error _ => rw [hr] at h; cases h
      | ok vp =>
          rw [hr] at h
          injection h with hpair
          injection hpair with _ hp'
          have hadv := readVarintAt_advances buf pos limit hr
          omega
  | 1 =>
      unfold readFixed64At at h
      dsimp only [bind, Except.bind, pure, Except.pure] at h
      by_cases hc : pos + 8 ≤ limit ∧ limit ≤ buf.size
      · rw [dif_pos hc] at h
        injection h with hpair
        injection hpair with _ hp'
        omega
      · rw [dif_neg hc] at h; cases h
  | 2 =>
      dsimp only [bind, Except.bind] at h
      cases hr : readVarintAt buf pos limit with
      | error _ => rw [hr] at h; cases h
      | ok vp =>
          rw [hr] at h
          dsimp only at h
          have hadv := readVarintAt_advances buf pos limit hr
          by_cases hc : vp.2 + vp.1 ≤ limit ∧ limit ≤ buf.size
          · rw [if_pos hc] at h
            injection h with hpair
            injection hpair with _ hp'
            omega
          · rw [if_neg hc] at h; cases h
  | 5 =>
      unfold readFixed32At at h
      dsimp only [bind, Except.bind, pure, Except.pure] at h
      by_cases hc : pos + 4 ≤ limit ∧ limit ≤ buf.size
      · rw [dif_pos hc] at h
        injection h with hpair
        injection hpair with _ hp'
        omega
      · rw [dif_neg hc] at h; cases h
  | 3 | 4 | n + 6 => cases h

/-- Linear DoS termination bound: every decoded Protobuf field strictly advances the byte cursor
    (`pos < pos' ≤ limit`), bounding loop iterations by `buf.size`. -/
theorem cursor_strictly_advances (buf : ByteArray) (pos limit : Nat)
    {fw : Nat × WireVal} {pos' : Nat}
    (h : readFieldAt buf pos limit = .ok (fw, pos')) :
    pos < pos' ∧ pos' ≤ limit := by
  unfold readFieldAt at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  cases htag : readVarintAt buf pos limit with
  | error _ => rw [htag] at h; cases h
  | ok tp =>
      rw [htag] at h
      dsimp only at h
      have htagAdv := readVarintAt_advances buf pos limit htag
      by_cases hf0 : (tp.1 / 8 == 0) = true
      · rw [if_pos hf0] at h; cases h
      · rw [if_neg hf0] at h
        cases hpay : readPayloadAt (tp.1 % 8) buf tp.2 limit with
        | error _ => rw [hpay] at h; cases h
        | ok wp =>
            rw [hpay] at h
            injection h with hpair
            injection hpair with _ hp'
            have hpayBnd := readPayloadAt_bounds (tp.1 % 8) buf tp.2 limit hpay
            omega

/-- Rolling-deploy forward compatibility: unknown field tags placed before or after known schema
    fields never alter lookup of known fields. -/
theorem skipUnknown_preserves_lookup_prefix (k : Nat) :
    ∀ (unknown known : List (Nat × WireVal)),
      (∀ u ∈ unknown, u.1 ≠ k) →
      lookupField k (unknown ++ known) = lookupField k known
  | [], _, _ => rfl
  | (uk, uw) :: rest, known, hne => by
      have huk : (uk == k) = false := beq_eq_false_iff_ne.2 (hne (uk, uw) (by simp))
      simp [lookupField, huk, skipUnknown_preserves_lookup_prefix k rest known (fun u hu => hne u (by simp [hu]))]

theorem skipUnknown_preserves_lookup_suffix (k : Nat) :
    ∀ (known unknown : List (Nat × WireVal)),
      (∀ u ∈ unknown, u.1 ≠ k) →
      lookupField k (known ++ unknown) = lookupField k known
  | [], unknown, hne => by
      simpa using skipUnknown_preserves_lookup_prefix k unknown [] hne
  | (kk, kw) :: rest, unknown, hne => by
      by_cases h : (kk == k) = true
      · simp [lookupField, h]
      · have hf : (kk == k) = false := Bool.eq_false_iff.2 h
        simp [lookupField, hf, skipUnknown_preserves_lookup_suffix k rest unknown hne]

private theorem lookupRepeated_none_of_ne (k : Nat) :
    ∀ (unknown : List (Nat × WireVal)),
      (∀ u ∈ unknown, u.1 ≠ k) →
      lookupRepeated k unknown = []
  | [], _ => rfl
  | (uk, uw) :: rest, hne => by
      have huk : (uk == k) = false := beq_eq_false_iff_ne.2 (hne (uk, uw) (by simp))
      simp [lookupRepeated, huk, lookupRepeated_none_of_ne k rest (fun u hu => hne u (by simp [hu]))]

theorem skipUnknown_preserves_repeated_suffix (k : Nat) :
    ∀ (known unknown : List (Nat × WireVal)),
      (∀ u ∈ unknown, u.1 ≠ k) →
      lookupRepeated k (known ++ unknown) = lookupRepeated k known
  | [], unknown, hne => by simpa using lookupRepeated_none_of_ne k unknown hne
  | (kk, kw) :: rest, unknown, hne => by
      by_cases h : (kk == k) = true
      · simp [lookupRepeated, h, skipUnknown_preserves_repeated_suffix k rest unknown hne]
      · have hf : (kk == k) = false := Bool.eq_false_iff.2 h
        simp [lookupRepeated, hf, skipUnknown_preserves_repeated_suffix k rest unknown hne]

/-! ## 3. `@[csimp]` Fast Writer & Borrowed-Cursor Equivalence -/

private theorem bytesToList_push (b : ByteArray) (x : UInt8) :
    bytesToList (b.push x) = bytesToList b ++ [x] := by
  cases b with | mk d =>
  simp [bytesToList, ByteArray.push, Array.toList_push]

private theorem writeVarint_toList (n : Nat) (buf : ByteArray) :
    bytesToList (writeVarint buf n) = bytesToList buf ++ encodeVarintList n := by
  induction n using Nat.strongRecOn generalizing buf with
  | ind n ih =>
      unfold writeVarint encodeVarintList
      by_cases hlt : n < 128
      · rw [if_pos hlt, if_pos hlt, bytesToList_push]
      · have hdiv : n / 128 < n := Nat.div_lt_self (by omega) (by decide)
        rw [if_neg hlt, if_neg hlt, ih (n / 128) hdiv (buf.push (UInt8.ofNat (n % 128 + 128))),
            bytesToList_push, List.append_assoc]
        rfl

private theorem writeFixed32_toList (buf : ByteArray) (v : UInt32) :
    bytesToList (writeFixed32 buf v) = bytesToList buf ++ encodeFixed32List v := by
  simp [writeFixed32, encodeFixed32List, bytesToList_push, List.append_assoc]

private theorem writeFixed64_toList (buf : ByteArray) (v : UInt64) :
    bytesToList (writeFixed64 buf v) = bytesToList buf ++ encodeFixed64List v := by
  simp [writeFixed64, encodeFixed64List, bytesToList_push, List.append_assoc]

private theorem writePayload_toList (buf : ByteArray) (w : WireVal) :
    bytesToList (writePayload buf w) = bytesToList buf ++ encodePayloadList w := by
  cases w with
  | varint n => exact writeVarint_toList n buf
  | fixed64 v => exact writeFixed64_toList buf v
  | bytes b =>
      have hw := writeVarint_toList b.size buf
      simp only [writePayload, encodePayloadList, bytesToList] at hw ⊢
      simp [hw, List.append_assoc]
  | fixed32 v => exact writeFixed32_toList buf v

private theorem writeField_toList (buf : ByteArray) (k : Nat) (w : WireVal) :
    bytesToList (writeField buf k w) = bytesToList buf ++ encodeFieldList k w := by
  simp [writeField, encodeFieldList, writePayload_toList, writeVarint_toList, List.append_assoc]

private theorem writeFieldsLoop_toList :
    ∀ (fields : List (Nat × WireVal)) (buf : ByteArray),
      bytesToList (writeFieldsLoop buf fields) = bytesToList buf ++ encodeFieldsList fields
  | [], buf => by simp [writeFieldsLoop, encodeFieldsList]
  | (k, w) :: rest, buf => by
      simp [writeFieldsLoop, encodeFieldsList, writeFieldsLoop_toList rest,
            writeField_toList, List.append_assoc]

private theorem bytesToList_inj {a b : ByteArray} (h : bytesToList a = bytesToList b) : a = b := by
  rw [← bytesOfList_bytesToList a, ← bytesOfList_bytesToList b, h]

@[csimp] theorem encodeFieldsSpec_eq_fast : @encodeFieldsSpec = @encodeFieldsFast := by
  funext fields
  apply bytesToList_inj
  have hempty : bytesToList (ByteArray.emptyWithCapacity 64) = [] := rfl
  simp [encodeFieldsSpec, encodeFieldsFast, writeFieldsLoop_toList, hempty]

private def sliceList (buf : ByteArray) (pos limit : Nat) : List UInt8 :=
  ((bytesToList buf).take limit).drop pos

private theorem sliceList_eq_nil {buf : ByteArray} {pos limit : Nat} (h : limit ≤ pos) :
    sliceList buf pos limit = [] := by
  unfold sliceList
  have hlen : ((bytesToList buf).take limit).length ≤ pos :=
    Nat.le_trans (List.length_take_le limit _) h
  exact List.drop_eq_nil_of_le hlen

private theorem sliceList_cons {buf : ByteArray} {pos limit : Nat}
    (h : pos < limit ∧ limit ≤ buf.size) :
    sliceList buf pos limit = (buf[pos]'(by omega)) :: sliceList buf (pos + 1) limit := by
  unfold sliceList
  cases buf with | mk arr =>
  dsimp only [bytesToList]
  have hlen : limit ≤ arr.toList.length := h.2
  have hltTake : pos < (arr.toList.take limit).length := by
    rw [List.length_take_of_le hlen]; exact h.1
  have hgetTake : (arr.toList.take limit)[pos]'hltTake = ({ data := arr } : ByteArray)[pos]'(by omega) := by
    rw [List.getElem_take]
    rfl
  rw [← List.getElem_cons_drop hltTake, hgetTake]

private theorem readVarintAt_eq_spec (buf : ByteArray) (pos limit : Nat)
    (hlim : limit ≤ buf.size) :
    (readVarintAt buf pos limit).map (fun (n, p') => (n, sliceList buf p' limit)) =
      decodeVarintList (sliceList buf pos limit) := by
  induction hfuel : limit - pos generalizing pos with
  | zero =>
      have hge : limit ≤ pos := by omega
      unfold readVarintAt
      have hnot : ¬ (pos < limit ∧ limit ≤ buf.size) := by omega
      rw [dif_neg hnot, sliceList_eq_nil hge]
      rfl
  | succ d ih =>
      have hlt : pos < limit := by omega
      have hcond : pos < limit ∧ limit ≤ buf.size := ⟨hlt, hlim⟩
      rw [sliceList_cons hcond]
      unfold readVarintAt
      rw [dif_pos hcond]
      by_cases hb : (buf[pos]'(by omega)).toNat < 128
      · rw [if_pos hb]
        simp [decodeVarintList, hb, Except.map]
      · rw [if_neg hb]
        unfold decodeVarintList
        rw [if_neg hb]
        dsimp only [bind, Except.bind]
        rw [← ih (pos + 1) (by omega)]
        cases readVarintAt buf (pos + 1) limit <;> simp [Except.map, pure, Except.pure]

private theorem splitExact_sliceList (buf : ByteArray) :
    ∀ (len pos limit : Nat),
      pos ≤ limit →
      limit ≤ buf.size →
      splitExact len (sliceList buf pos limit) =
        if pos + len ≤ limit then
          some (sliceList buf pos (pos + len), sliceList buf (pos + len) limit)
        else
          none
  | 0, pos, limit, hp, _ => by
      simp [splitExact, hp, sliceList_eq_nil (Nat.le_refl pos)]
  | len + 1, pos, limit, hp, hlim => by
      by_cases hlt : pos < limit
      · rw [sliceList_cons ⟨hlt, hlim⟩]
        unfold splitExact
        rw [splitExact_sliceList buf len (pos + 1) limit (by omega) hlim]
        by_cases hfit : pos + 1 + len ≤ limit
        · have hfit' : pos + (len + 1) ≤ limit := by omega
          have heq2 : pos + (len + 1) = pos + 1 + len := by omega
          have hsc : sliceList buf pos (pos + 1 + len) =
              (buf[pos]'(by omega)) :: sliceList buf (pos + 1) (pos + 1 + len) :=
            sliceList_cons ⟨by omega, by omega⟩
          rw [if_pos hfit, if_pos hfit', heq2, hsc]
        · have hfit' : ¬ (pos + (len + 1) ≤ limit) := by omega
          rw [if_neg hfit, if_neg hfit']
      · have heq : limit ≤ pos := by omega
        have hnot : ¬ (pos + (len + 1) ≤ limit) := by omega
        simp [sliceList_eq_nil heq, splitExact, hnot]

private theorem sliceList_len_le (buf : ByteArray) (pos limit : Nat) :
    (sliceList buf pos limit).length ≤ limit - pos := by
  unfold sliceList
  have := List.length_take_le limit (bytesToList buf)
  rw [List.length_drop]; omega

private theorem readFixed32At_eq_spec (buf : ByteArray) (pos limit : Nat)
    (hlim : limit ≤ buf.size) :
    (readFixed32At buf pos limit).map (fun (v, p') => (v, sliceList buf p' limit)) =
      decodeFixed32List (sliceList buf pos limit) := by
  unfold readFixed32At
  by_cases h : pos + 4 ≤ limit ∧ limit ≤ buf.size
  · rw [dif_pos h, sliceList_cons ⟨by omega, hlim⟩, sliceList_cons ⟨by omega, hlim⟩,
        sliceList_cons ⟨by omega, hlim⟩, sliceList_cons ⟨by omega, hlim⟩]
    rfl
  · rw [dif_neg h]
    have hlen := sliceList_len_le buf pos limit
    match hsl : sliceList buf pos limit with
    | _ :: _ :: _ :: _ :: _ => exfalso; simp [hsl] at hlen; omega
    | [] | [_] | [_, _] | [_, _, _] => rfl

private theorem readFixed64At_eq_spec (buf : ByteArray) (pos limit : Nat)
    (hlim : limit ≤ buf.size) :
    (readFixed64At buf pos limit).map (fun (v, p') => (v, sliceList buf p' limit)) =
      decodeFixed64List (sliceList buf pos limit) := by
  unfold readFixed64At
  by_cases h : pos + 8 ≤ limit ∧ limit ≤ buf.size
  · rw [dif_pos h, sliceList_cons ⟨by omega, hlim⟩, sliceList_cons ⟨by omega, hlim⟩,
        sliceList_cons ⟨by omega, hlim⟩, sliceList_cons ⟨by omega, hlim⟩,
        sliceList_cons ⟨by omega, hlim⟩, sliceList_cons ⟨by omega, hlim⟩,
        sliceList_cons ⟨by omega, hlim⟩, sliceList_cons ⟨by omega, hlim⟩]
    rfl
  · rw [dif_neg h]
    have hlen := sliceList_len_le buf pos limit
    match hsl : sliceList buf pos limit with
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => exfalso; simp [hsl] at hlen; omega
    | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _]
    | [_, _, _, _, _, _] | [_, _, _, _, _, _, _] => rfl

private theorem readPayloadAt_eq_spec (wt : Nat) (buf : ByteArray) (pos limit : Nat)
    (hlim : limit ≤ buf.size) :
    (readPayloadAt wt buf pos limit).map (fun (w, p') => (w, sliceList buf p' limit)) =
      decodePayloadList wt (sliceList buf pos limit) := by
  unfold readPayloadAt decodePayloadList
  match wt with
  | 0 =>
      rw [← readVarintAt_eq_spec buf pos limit hlim]
      cases readVarintAt buf pos limit <;> simp [Except.map, bind, Except.bind, pure, Except.pure]
  | 1 =>
      rw [← readFixed64At_eq_spec buf pos limit hlim]
      cases readFixed64At buf pos limit <;> simp [Except.map, bind, Except.bind, pure, Except.pure]
  | 2 =>
      rw [← readVarintAt_eq_spec buf pos limit hlim]
      cases hr : readVarintAt buf pos limit with
      | error _ => rfl
      | ok lp =>
          rcases lp with ⟨len, afterLen⟩
          have hadv := readVarintAt_advances buf pos limit hr
          dsimp only [Except.map, bind, Except.bind]
          rw [splitExact_sliceList buf len afterLen limit (by omega) hlim]
          by_cases hfit : afterLen + len ≤ limit
          · have hcond : afterLen + len ≤ limit ∧ limit ≤ buf.size := ⟨hfit, hlim⟩
            have hchunk : buf.extract afterLen (afterLen + len) =
                bytesOfList (sliceList buf afterLen (afterLen + len)) := by
              apply bytesToList_inj
              simp [bytesToList, bytesOfList, sliceList, List.drop_take]
            rw [if_pos hfit, if_pos hcond, hchunk]
          · have hnot : ¬ (afterLen + len ≤ limit ∧ limit ≤ buf.size) := by omega
            rw [if_neg hfit, if_neg hnot]
  | 5 =>
      rw [← readFixed32At_eq_spec buf pos limit hlim]
      cases readFixed32At buf pos limit <;> simp [Except.map, bind, Except.bind, pure, Except.pure]
  | 3 | 4 | n + 6 => rfl

private theorem readFieldAt_eq_spec (buf : ByteArray) (pos limit : Nat)
    (hlim : limit ≤ buf.size) :
    (readFieldAt buf pos limit).map (fun (fw, p') => (fw, sliceList buf p' limit)) =
      decodeFieldList (sliceList buf pos limit) := by
  unfold readFieldAt decodeFieldList
  rw [← readVarintAt_eq_spec buf pos limit hlim]
  cases htag : readVarintAt buf pos limit with
  | error _ => rfl
  | ok tp =>
      rcases tp with ⟨tag, afterTag⟩
      dsimp only [Except.map, bind, Except.bind]
      by_cases hf0 : (tag / 8 == 0) = true
      · rw [if_pos hf0, if_pos hf0]
      · rw [if_neg hf0, if_neg hf0, ← readPayloadAt_eq_spec (tag % 8) buf afterTag limit hlim]
        cases readPayloadAt (tag % 8) buf afterTag limit <;>
          simp [Except.map, pure, Except.pure]

private theorem readFieldAt_fast_step (buf : ByteArray) (pos limit : Nat)
    (h2 : pos + 1 < limit ∧ limit ≤ buf.size)
    (htag : (buf[pos]'(by omega)).toNat < 128) (hb1 : (buf[pos + 1]'(by omega)).toNat < 128)
    (hfn : ((buf[pos]'(by omega)).toNat / 8 != 0) = true) :
    ((buf[pos]'(by omega)).toNat % 8 = 0 →
      readFieldAt buf pos limit = .ok (((buf[pos]'(by omega)).toNat / 8, .varint (buf[pos + 1]'(by omega)).toNat), pos + 2)) ∧
    ((buf[pos]'(by omega)).toNat % 8 = 2 →
      readFieldAt buf pos limit =
        if pos + 2 + (buf[pos + 1]'(by omega)).toNat ≤ limit then
          .ok (((buf[pos]'(by omega)).toNat / 8, .bytes (buf.extract (pos + 2) (pos + 2 + (buf[pos + 1]'(by omega)).toNat))),
            pos + 2 + (buf[pos + 1]'(by omega)).toNat)
        else .error "protobuf: truncated length-delimited field") := by
  have hv1 : readVarintAt buf pos limit = .ok ((buf[pos]'(by omega)).toNat, pos + 1) := by
    unfold readVarintAt; rw [dif_pos ⟨by omega, h2.2⟩, if_pos htag]
  have hv2 : readVarintAt buf (pos + 1) limit = .ok ((buf[pos + 1]'(by omega)).toNat, pos + 2) := by
    unfold readVarintAt; rw [dif_pos h2, if_pos hb1]
  have hfn0 : ((buf[pos]'(by omega)).toNat / 8 == 0) = false :=
    beq_eq_false_iff_ne.2 (by simpa [bne_iff_ne] using hfn)
  constructor <;> intro hwt
  · simp [readFieldAt, hv1, hfn0, hwt, readPayloadAt, hv2, bind, Except.bind, pure, Except.pure]
  · split <;> simp [readFieldAt, readPayloadAt, h2.2, *, bind, Except.bind, pure, Except.pure]

private theorem readFieldsLoop_eq_spec (buf : ByteArray) :
    ∀ (fuel pos limit : Nat) (acc : List (Nat × WireVal)),
      pos ≤ limit →
      limit ≤ buf.size →
      readFieldsLoop fuel buf pos limit acc = decodeFieldsAux fuel (sliceList buf pos limit) acc
  | fuel, pos, limit, acc, hp, hlim => by
      by_cases heq : (pos == limit) = true
      · have hp' : pos = limit := beq_iff_eq.1 heq
        subst hp'
        unfold readFieldsLoop
        rw [if_pos heq, sliceList_eq_nil (Nat.le_refl pos)]
        cases fuel <;> rfl
      · have hlt : pos < limit := by
          have hne : pos ≠ limit := beq_eq_false_iff_ne.1 (Bool.eq_false_iff.2 heq)
          omega
        cases fuel with
        | zero =>
            unfold readFieldsLoop
            rw [if_neg heq, sliceList_cons ⟨hlt, hlim⟩]
            rfl
        | succ f' =>
            have hstep := readFieldAt_eq_spec buf pos limit hlim
            rw [sliceList_cons ⟨hlt, hlim⟩] at hstep
            have hfallback :
                (match readFieldAt buf pos limit with
                  | .error e => .error e
                  | .ok (fw, pos') => readFieldsLoop f' buf pos' limit (fw :: acc)) =
                decodeFieldsAux (f' + 1) (sliceList buf pos limit) acc := by
              rw [sliceList_cons ⟨hlt, hlim⟩]
              unfold decodeFieldsAux
              dsimp only [bind, Except.bind]
              rw [← hstep]
              cases hrf : readFieldAt buf pos limit with
              | error _ => rfl
              | ok fwp =>
                  have hadv := cursor_strictly_advances buf pos limit hrf
                  exact readFieldsLoop_eq_spec buf f' fwp.2 limit (fwp.1 :: acc) (by omega) hlim
            unfold readFieldsLoop
            rw [if_neg heq]; dsimp only
            split
            · rename_i h2
              split
              · rename_i hlt128
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt128
                split
                · rename_i hfw0
                  simp only [Bool.and_eq_true] at hfw0
                  rw [← hfallback, (readFieldAt_fast_step buf pos limit h2 hlt128.1 hlt128.2 hfw0.1).1 (beq_iff_eq.1 hfw0.2)]
                · split
                  · rename_i _ hfw2
                    simp only [Bool.and_eq_true] at hfw2
                    have hrf := (readFieldAt_fast_step buf pos limit h2 hlt128.1 hlt128.2 hfw2.1).2 (beq_iff_eq.1 hfw2.2)
                    split <;> (rw [← hfallback, hrf]; simp [*])
                  · exact hfallback
              · exact hfallback
            · exact hfallback

@[csimp] theorem decodeFieldsSpec_eq_fast : @decodeFieldsSpec = @decodeFieldsFast := by
  funext buf
  unfold decodeFieldsSpec decodeFieldsFast
  dsimp only
  rw [readFieldsLoop_eq_spec buf buf.size 0 buf.size [] (Nat.zero_le _) (Nat.le_refl _)]
  have hsl : sliceList buf 0 buf.size = bytesToList buf := by
    unfold sliceList
    rw [← bytesToList_length buf, List.take_length, List.drop_zero]
  rw [hsl, bytesToList_length]

/-! ## 4. Hex `ByteArray` Round-Trip Theorem -/

private theorem unhexChar_hexByte {d : Nat} (hd : d < 16) : unhexChar (hexByte d) = some d := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => decide
  | _ + 16 => omega

private theorem decodeHexList_encodeHexList :
    ∀ (xs : List UInt8), decodeHexList (encodeHexList xs) = some xs
  | [] => rfl
  | b :: bs => by
      have hb : b.toNat < 256 := b.toBitVec.isLt
      have hhi : b.toNat / 16 < 16 := by omega
      have hlo : b.toNat % 16 < 16 := by omega
      have hrec : UInt8.ofNat (b.toNat / 16 * 16 + b.toNat % 16) = b := by
        apply uint8_ext
        change (b.toNat / 16 * 16 + b.toNat % 16) % 256 = b.toNat
        omega
      unfold encodeHexList decodeHexList
      rw [unhexChar_hexByte hhi, unhexChar_hexByte hlo, decodeHexList_encodeHexList bs]
      dsimp only [bind, Option.bind]
      rw [hrec]
      rfl

theorem decodeHex_encodeHex (b : ByteArray) : decodeHex (encodeHex b) = .ok b := by
  simp [encodeHex, decodeHex, String.toList_ofList, decodeHexList_encodeHexList, bytesOfList_bytesToList]

private theorem encodeHexLoop_eq_spec (b : ByteArray) :
    ∀ (i : Nat) (acc : List Char),
      i ≤ b.size →
      encodeHexLoop b i acc = acc.reverse ++ encodeHexList ((bytesToList b).drop i) := by
  intro i
  induction hfuel : b.size - i generalizing i with
  | zero =>
      intro acc hi
      have heq : i = b.size := by omega
      subst heq
      unfold encodeHexLoop
      have hnot : ¬ (b.size < b.size) := Nat.lt_irrefl _
      rw [dif_neg hnot]
      have hdrop : (bytesToList b).drop b.size = [] := by
        rw [← bytesToList_length b]; exact List.drop_length
      simp [hdrop, encodeHexList]
  | succ d ih =>
      intro acc hi
      have hlt : i < b.size := by omega
      unfold encodeHexLoop
      rw [dif_pos hlt, ih (i + 1) (by omega) _ (by omega)]
      cases b with | mk arr =>
      have hltArr : i < arr.toList.length := by simpa [ByteArray.size] using hlt
      have hget : ({ data := arr } : ByteArray)[i]'hlt = arr.toList[i]'hltArr := rfl
      have hdrop : (bytesToList { data := arr }).drop i =
          (arr.toList[i]'hltArr) :: arr.toList.drop (i + 1) := by
        dsimp only [bytesToList]
        exact (List.getElem_cons_drop hltArr).symm
      rw [hget, hdrop]
      simp [encodeHexList, bytesToList, List.append_assoc]

@[csimp] theorem encodeHex_eq_fast : @encodeHex = @encodeHexFast := by
  funext b
  unfold encodeHex encodeHexFast
  rw [encodeHexLoop_eq_spec b 0 [] (Nat.zero_le _)]
  simp

private theorem decodeHexBuf_eq_spec :
    ∀ (cs : List Char) (out : ByteArray),
      (decodeHexBuf cs out).map bytesToList =
        (decodeHexList cs).map (fun xs => bytesToList out ++ xs)
  | [], out => by simp [decodeHexBuf, decodeHexList]
  | [_], _ => rfl
  | hi :: lo :: rest, out => by
      unfold decodeHexBuf decodeHexList
      cases unhexChar hi with
      | none => rfl
      | some h =>
          dsimp only [bind, Option.bind]
          cases unhexChar lo with
          | none => rfl
          | some l =>
              dsimp only [bind, Option.bind]
              rw [decodeHexBuf_eq_spec rest (out.push (UInt8.ofNat (h * 16 + l))),
                  bytesToList_push]
              cases decodeHexList rest <;> simp [Option.map, List.append_assoc]

@[csimp] theorem decodeHex_eq_fast : @decodeHex = @decodeHexFast := by
  funext s
  unfold decodeHex decodeHexFast
  have h := decodeHexBuf_eq_spec s.toList (ByteArray.emptyWithCapacity (s.utf8ByteSize / 2))
  have hempty : bytesToList (ByteArray.emptyWithCapacity (s.utf8ByteSize / 2)) = [] := rfl
  cases hbuf : decodeHexBuf s.toList (ByteArray.emptyWithCapacity (s.utf8ByteSize / 2)) <;>
    cases hlst : decodeHexList s.toList
  · rfl
  · rw [hbuf, hlst] at h; cases h
  · rw [hbuf, hlst] at h; cases h
  · rw [hbuf, hlst] at h
    simp only [Option.map, hempty, List.nil_append, Option.some.injEq] at h
    dsimp only
    rw [← h, bytesOfList_bytesToList]

end Qed.Proto
