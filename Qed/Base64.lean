namespace Qed.Base64

/-! ## Total, Verified RFC 4648 Standard Base64 Codec -/

def encodeChar (n : Nat) : Char :=
  if n < 26 then Char.ofNat (65 + n)
  else if n < 52 then Char.ofNat (71 + n)
  else if n < 62 then Char.ofNat (n - 4)
  else if n == 62 then '+'
  else '/'

def decodeChar (c : Char) : Option Nat :=
  let n := c.toNat
  if 65 ≤ n && n ≤ 90 then some (n - 65)
  else if 97 ≤ n && n ≤ 122 then some (n - 71)
  else if 48 ≤ n && n ≤ 57 then some (n + 4)
  else if n == 43 then some 62
  else if n == 47 then some 63
  else none

private theorem toNat_ofNat_lt_128 {k : Nat} (h : k < 128) :
    (Char.ofNat k).toNat = k := by
  have hv : k.isValidChar := Or.inl (by omega)
  have h1 : Char.ofNat k = Char.ofNatAux k hv := by simp [Char.ofNat, hv]
  rw [h1]
  simp [Char.toNat, Char.ofNatAux]

theorem decodeChar_encodeChar (n : Nat) (h : n < 64) :
    decodeChar (encodeChar n) = some n := by
  unfold encodeChar decodeChar
  by_cases h1 : n < 26
  · rw [if_pos h1, toNat_ofNat_lt_128 (by omega)]
    have hc : (decide (65 ≤ 65 + n) && decide (65 + n ≤ 90)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    rw [if_pos hc]; congr 1; omega
  · rw [if_neg h1]
    by_cases h2 : n < 52
    · rw [if_pos h2, toNat_ofNat_lt_128 (by omega)]
      have hc1 : (decide (65 ≤ 71 + n) && decide (71 + n ≤ 90)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      have hc2 : (decide (97 ≤ 71 + n) && decide (71 + n ≤ 122)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
      rw [if_neg (by simp [hc1]), if_pos hc2]; congr 1; omega
    · rw [if_neg h2]
      by_cases h3 : n < 62
      · rw [if_pos h3, toNat_ofNat_lt_128 (by omega)]
        have hc1 : (decide (65 ≤ n - 4) && decide (n - 4 ≤ 90)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
        have hc2 : (decide (97 ≤ n - 4) && decide (n - 4 ≤ 122)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
        have hc3 : (decide (48 ≤ n - 4) && decide (n - 4 ≤ 57)) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
        rw [if_neg (by rw [hc1]; decide), if_neg (by rw [hc2]; decide), if_pos hc3]; congr 1; omega
      · rw [if_neg h3]
        by_cases h4 : n = 62
        · subst h4; rfl
        · have h5 : n = 63 := by omega
          subst h5; rfl

theorem encodeChar_ne_pad (n : Nat) (h : n < 64) : encodeChar n ≠ '=' := by
  intro heq
  have h1 := decodeChar_encodeChar n h
  rw [heq] at h1
  contradiction

def encodeList : List UInt8 → List Char
  | [] => []
  | [b0] =>
      let n0 := b0.toNat
      [encodeChar (n0 / 4), encodeChar ((n0 % 4) * 16), '=', '=']
  | [b0, b1] =>
      let n0 := b0.toNat; let n1 := b1.toNat
      [encodeChar (n0 / 4), encodeChar ((n0 % 4) * 16 + n1 / 16),
       encodeChar ((n1 % 16) * 4), '=']
  | b0 :: b1 :: b2 :: rest =>
      let n0 := b0.toNat; let n1 := b1.toNat; let n2 := b2.toNat
      encodeChar (n0 / 4) ::
      encodeChar ((n0 % 4) * 16 + n1 / 16) ::
      encodeChar ((n1 % 16) * 4 + n2 / 64) ::
      encodeChar (n2 % 64) ::
      encodeList rest

def decodeQuad (c0 c1 c2 c3 : Char) (isLast : Bool) : Except String (List UInt8) :=
  if isLast && c2 == '=' && c3 == '=' then
    match decodeChar c0, decodeChar c1 with
    | some v0, some v1 => .ok [UInt8.ofNat (v0 * 4 + v1 / 16)]
    | _, _             => .error "base64: invalid character"
  else if isLast && c3 == '=' then
    match decodeChar c0, decodeChar c1, decodeChar c2 with
    | some v0, some v1, some v2 =>
        .ok [UInt8.ofNat (v0 * 4 + v1 / 16), UInt8.ofNat ((v1 % 16) * 16 + v2 / 4)]
    | _, _, _ => .error "base64: invalid character"
  else
    match decodeChar c0, decodeChar c1, decodeChar c2, decodeChar c3 with
    | some v0, some v1, some v2, some v3 =>
        .ok [UInt8.ofNat (v0 * 4 + v1 / 16),
             UInt8.ofNat ((v1 % 16) * 16 + v2 / 4),
             UInt8.ofNat ((v2 % 4) * 64 + v3)]
    | _, _, _, _ => .error "base64: invalid character"

def decodeList : List Char → Except String (List UInt8)
  | [] => .ok []
  | c0 :: c1 :: c2 :: c3 :: rest => do
      let chunk ← decodeQuad c0 c1 c2 c3 rest.isEmpty
      let tl ← decodeList rest
      .ok (chunk ++ tl)
  | _ => .error "base64: invalid length"

private theorem uint8_ofNat_toNat_eq (b : UInt8) {k : Nat} (h : k = b.toNat) :
    UInt8.ofNat k = b := by
  subst h; exact UInt8.ofNat_toNat

theorem decodeList_encodeList : ∀ (bs : List UInt8), decodeList (encodeList bs) = .ok bs
  | [] => rfl
  | [b0] => by
      have hb0 : b0.toNat < 256 := b0.toNat_lt
      have h0 := decodeChar_encodeChar (b0.toNat / 4) (by omega)
      have h1 := decodeChar_encodeChar ((b0.toNat % 4) * 16) (by omega)
      simp only [encodeList, decodeList, decodeQuad, List.isEmpty_nil, beq_self_eq_true,
        Bool.and_self, ↓reduceIte, h0, h1, bind, Except.bind, List.append_nil]
      congr 1; congr 1
      exact uint8_ofNat_toNat_eq b0 (by omega)
  | [b0, b1] => by
      have hb0 : b0.toNat < 256 := b0.toNat_lt
      have hb1 : b1.toNat < 256 := b1.toNat_lt
      have h0 := decodeChar_encodeChar (b0.toNat / 4) (by omega)
      have h1 := decodeChar_encodeChar ((b0.toNat % 4) * 16 + b1.toNat / 16) (by omega)
      have h2 := decodeChar_encodeChar ((b1.toNat % 16) * 4) (by omega)
      have hne2 : (encodeChar ((b1.toNat % 16) * 4) == '=') = false :=
        beq_false_of_ne (encodeChar_ne_pad _ (by omega))
      simp only [encodeList, decodeList, decodeQuad, List.isEmpty_nil, hne2, beq_self_eq_true,
        Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte, h0, h1, h2,
        bind, Except.bind, List.append_nil]
      congr 1
      have e0 : UInt8.ofNat (b0.toNat / 4 * 4 + ((b0.toNat % 4) * 16 + b1.toNat / 16) / 16) = b0 :=
        uint8_ofNat_toNat_eq b0 (by omega)
      have e1 : UInt8.ofNat ((((b0.toNat % 4) * 16 + b1.toNat / 16) % 16) * 16 + ((b1.toNat % 16) * 4) / 4) = b1 :=
        uint8_ofNat_toNat_eq b1 (by omega)
      rw [e0, e1]
  | b0 :: b1 :: b2 :: rest => by
      have hb0 : b0.toNat < 256 := b0.toNat_lt
      have hb1 : b1.toNat < 256 := b1.toNat_lt
      have hb2 : b2.toNat < 256 := b2.toNat_lt
      have h0 := decodeChar_encodeChar (b0.toNat / 4) (by omega)
      have h1 := decodeChar_encodeChar ((b0.toNat % 4) * 16 + b1.toNat / 16) (by omega)
      have h2 := decodeChar_encodeChar ((b1.toNat % 16) * 4 + b2.toNat / 64) (by omega)
      have h3 := decodeChar_encodeChar (b2.toNat % 64) (by omega)
      have hne3 : (encodeChar (b2.toNat % 64) == '=') = false :=
        beq_false_of_ne (encodeChar_ne_pad _ (by omega))
      have ih := decodeList_encodeList rest
      simp only [encodeList, decodeList, decodeQuad, hne3, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte, h0, h1, h2, h3, ih, bind, Except.bind, List.cons_append, List.nil_append]
      congr 1
      have e0 : UInt8.ofNat (b0.toNat / 4 * 4 + ((b0.toNat % 4) * 16 + b1.toNat / 16) / 16) = b0 :=
        uint8_ofNat_toNat_eq b0 (by omega)
      have e1 : UInt8.ofNat ((((b0.toNat % 4) * 16 + b1.toNat / 16) % 16) * 16 +
          ((b1.toNat % 16) * 4 + b2.toNat / 64) / 4) = b1 :=
        uint8_ofNat_toNat_eq b1 (by omega)
      have e2 : UInt8.ofNat ((((b1.toNat % 16) * 4 + b2.toNat / 64) % 4) * 64 + b2.toNat % 64) = b2 :=
        uint8_ofNat_toNat_eq b2 (by omega)
      rw [e0, e1, e2]

def encode (bs : ByteArray) : String :=
  String.ofList (encodeList bs.data.toList)

def decode (s : String) : Except String ByteArray :=
  (decodeList s.toList).map fun xs => ByteArray.mk xs.toArray

theorem decode_encode (bs : ByteArray) : decode (encode bs) = .ok bs := by
  unfold decode encode
  rw [String.toList_ofList, decodeList_encodeList]
  cases bs; rfl

/-! ## Tail-Recursive O(1)-Stack Fast Implementations (`@[csimp]`) -/

private def encodeListRevAcc : List UInt8 → List Char → List Char
  | [], acc => acc.reverse
  | [b0], acc =>
      let n0 := b0.toNat
      ('=' :: '=' :: encodeChar ((n0 % 4) * 16) :: encodeChar (n0 / 4) :: acc).reverse
  | [b0, b1], acc =>
      let n0 := b0.toNat; let n1 := b1.toNat
      ('=' :: encodeChar ((n1 % 16) * 4) :: encodeChar ((n0 % 4) * 16 + n1 / 16) ::
       encodeChar (n0 / 4) :: acc).reverse
  | b0 :: b1 :: b2 :: rest, acc =>
      let n0 := b0.toNat; let n1 := b1.toNat; let n2 := b2.toNat
      encodeListRevAcc rest
        (encodeChar (n2 % 64) ::
         encodeChar ((n1 % 16) * 4 + n2 / 64) ::
         encodeChar ((n0 % 4) * 16 + n1 / 16) ::
         encodeChar (n0 / 4) :: acc)

private theorem encodeListRevAcc_eq :
    ∀ (bs : List UInt8) (acc : List Char),
      encodeListRevAcc bs acc = acc.reverse ++ encodeList bs
  | [], acc => by simp [encodeListRevAcc, encodeList]
  | [b0], acc => by simp [encodeListRevAcc, encodeList]
  | [b0, b1], acc => by simp [encodeListRevAcc, encodeList]
  | b0 :: b1 :: b2 :: rest, acc => by
      simp only [encodeListRevAcc, encodeList]
      rw [encodeListRevAcc_eq rest]
      simp [List.append_assoc]

def encodeFast (bs : ByteArray) : String :=
  String.ofList (encodeListRevAcc bs.data.toList [])

@[csimp] theorem encode_eq_fast : @encode = @encodeFast := by
  funext bs
  unfold encode encodeFast
  rw [encodeListRevAcc_eq]
  simp

private def decodeBufAcc : List Char → List UInt8 → Except String (List UInt8)
  | [], acc => .ok acc.reverse
  | c0 :: c1 :: c2 :: c3 :: rest, acc =>
      match decodeQuad c0 c1 c2 c3 rest.isEmpty with
      | .error e    => .error e
      | .ok chunk   => decodeBufAcc rest (chunk.reverse ++ acc)
  | _, _ => .error "base64: invalid length"

private theorem decodeBufAcc_eq :
    ∀ (cs : List Char) (acc : List UInt8),
      decodeBufAcc cs acc = (decodeList cs).map (acc.reverse ++ ·)
  | [], acc => by simp [decodeBufAcc, decodeList, Except.map]
  | [_], acc => by simp [decodeBufAcc, decodeList, Except.map]
  | [_, _], acc => by simp [decodeBufAcc, decodeList, Except.map]
  | [_, _, _], acc => by simp [decodeBufAcc, decodeList, Except.map]
  | c0 :: c1 :: c2 :: c3 :: rest, acc => by
      unfold decodeBufAcc decodeList
      dsimp only [bind, Except.bind]
      cases decodeQuad c0 c1 c2 c3 rest.isEmpty with
      | error e => rfl
      | ok chunk =>
          dsimp only
          rw [decodeBufAcc_eq rest]
          cases decodeList rest with
          | error e => rfl
          | ok tl => simp [Except.map, List.append_assoc]

def decodeFast (s : String) : Except String ByteArray :=
  (decodeBufAcc s.toList []).map fun xs => ByteArray.mk xs.toArray

@[csimp] theorem decode_eq_fast : @decode = @decodeFast := by
  funext s
  unfold decode decodeFast
  rw [decodeBufAcc_eq]
  cases decodeList s.toList <;> simp [Except.map]

end Qed.Base64
