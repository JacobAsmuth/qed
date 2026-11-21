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

def isUrlChar (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '-' || c == '_'

def toUrlChar : Char → Char
  | '+' => '-'
  | '/' => '_'
  | c   => c

def fromUrlChar : Char → Char
  | '-' => '+'
  | '_' => '/'
  | c   => c

private theorem decodeChar_encodeChar_fin :
    ∀ n : Fin 64, decodeChar (encodeChar n.val) = some n.val := by
  decide

theorem decodeChar_encodeChar (n : Nat) (h : n < 64) :
    decodeChar (encodeChar n) = some n :=
  decodeChar_encodeChar_fin ⟨n, h⟩

theorem encodeChar_ne_pad (n : Nat) (h : n < 64) : encodeChar n ≠ '=' := by
  intro heq
  have h1 := decodeChar_encodeChar n h
  rw [heq] at h1
  contradiction

def encodeListWith (f : Nat → Char) (pad : Bool) : List UInt8 → List Char
  | [] => []
  | [b0] =>
      let n0 := b0.toNat
      let c0 := f (n0 / 4); let c1 := f ((n0 % 4) * 16)
      if pad then [c0, c1, '=', '='] else [c0, c1]
  | [b0, b1] =>
      let n0 := b0.toNat; let n1 := b1.toNat
      let c0 := f (n0 / 4); let c1 := f ((n0 % 4) * 16 + n1 / 16); let c2 := f ((n1 % 16) * 4)
      if pad then [c0, c1, c2, '='] else [c0, c1, c2]
  | b0 :: b1 :: b2 :: rest =>
      let n0 := b0.toNat; let n1 := b1.toNat; let n2 := b2.toNat
      f (n0 / 4) :: f ((n0 % 4) * 16 + n1 / 16) ::
      f ((n1 % 16) * 4 + n2 / 64) :: f (n2 % 64) ::
      encodeListWith f pad rest

def encodeList (bs : List UInt8) : List Char :=
  encodeListWith encodeChar true bs

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
      simp only [encodeList, encodeListWith, decodeList, decodeQuad, List.isEmpty_nil, beq_self_eq_true,
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
      simp only [encodeList, encodeListWith, decodeList, decodeQuad, List.isEmpty_nil, hne2, beq_self_eq_true,
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
      have ih : decodeList (encodeListWith encodeChar true rest) = .ok rest :=
        decodeList_encodeList rest
      simp only [encodeList, encodeListWith, decodeList, decodeQuad, hne3, Bool.and_false, Bool.false_eq_true,
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

/-! ## Verified RFC 4648 §5 Base64URL Codec (Unpadded Encode, Padded/Unpadded Decode) -/

/-- RFC 4648 §5 unpadded Base64URL encoding (`-` / `_`, no `=` padding). -/
def encodeUrl (bs : ByteArray) : String :=
  String.ofList (encodeListWith (fun n => toUrlChar (encodeChar n)) false bs.data.toList)

/-- RFC 4648 §5 Base64URL decoding (accepts padded or unpadded input; rejects `+`/`/` and interior `=`). -/
def decodeUrl (s : String) : Except String ByteArray :=
  let cs := s.toList
  let stripped := if cs.isEmpty then [] else (cs.reverse.dropWhile (· == '=')).reverse
  if stripped.length % 4 == 1 then
    .error "base64url: invalid length"
  else if stripped.any (fun c => c == '+' || c == '/' || c == '=') then
    .error "base64url: invalid character"
  else
    let mapped := stripped.map fromUrlChar
    let padded := match mapped.length % 4 with
      | 2 => mapped ++ ['=', '=']
      | 3 => mapped ++ ['=']
      | _ => mapped
    decode (String.ofList padded)

private theorem toUrlChar_encodeChar_safe_fin :
    ∀ n : Fin 64, isUrlChar (toUrlChar (encodeChar n.val)) = true := by
  decide

private theorem encodeListWith_all (f : Nat → Char) (p : Char → Bool)
    (hf : ∀ n < 64, p (f n) = true) :
    ∀ bs : List UInt8, (encodeListWith f false bs).all p = true
  | [] => rfl
  | [b0] => by
      have := b0.toNat_lt
      simp only [encodeListWith, Bool.false_eq_true, ↓reduceIte, List.all_cons, List.all_nil, Bool.and_true]
      rw [hf _ (by omega), hf _ (by omega)]; rfl
  | [b0, b1] => by
      have := b0.toNat_lt; have := b1.toNat_lt
      simp only [encodeListWith, Bool.false_eq_true, ↓reduceIte, List.all_cons, List.all_nil, Bool.and_true]
      rw [hf _ (by omega), hf _ (by omega), hf _ (by omega)]; rfl
  | b0 :: b1 :: b2 :: rest => by
      have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt
      simp only [encodeListWith, List.all_cons, encodeListWith_all f p hf rest, Bool.and_true]
      rw [hf _ (by omega), hf _ (by omega), hf _ (by omega), hf _ (by omega)]; rfl

theorem encodeUrl_safe (bs : ByteArray) :
    (encodeUrl bs).toList.all isUrlChar = true := by
  unfold encodeUrl
  rw [String.toList_ofList]
  exact encodeListWith_all (fun n => toUrlChar (encodeChar n)) isUrlChar
    (fun n h => toUrlChar_encodeChar_safe_fin ⟨n, h⟩) bs.data.toList

/-! ## Tail-Recursive O(1)-Stack Fast Implementations (`@[csimp]`) -/

private def encodeListRevAccWith (f : Nat → Char) (pad : Bool) : List UInt8 → List Char → List Char
  | [], acc => acc.reverse
  | [b0], acc =>
      let n0 := b0.toNat
      let acc' := f ((n0 % 4) * 16) :: f (n0 / 4) :: acc
      (if pad then '=' :: '=' :: acc' else acc').reverse
  | [b0, b1], acc =>
      let n0 := b0.toNat; let n1 := b1.toNat
      let acc' := f ((n1 % 16) * 4) :: f ((n0 % 4) * 16 + n1 / 16) :: f (n0 / 4) :: acc
      (if pad then '=' :: acc' else acc').reverse
  | b0 :: b1 :: b2 :: rest, acc =>
      let n0 := b0.toNat; let n1 := b1.toNat; let n2 := b2.toNat
      encodeListRevAccWith f pad rest
        (f (n2 % 64) :: f ((n1 % 16) * 4 + n2 / 64) ::
         f ((n0 % 4) * 16 + n1 / 16) :: f (n0 / 4) :: acc)

private theorem encodeListRevAccWith_eq (f : Nat → Char) (pad : Bool) :
    ∀ (bs : List UInt8) (acc : List Char),
      encodeListRevAccWith f pad bs acc = acc.reverse ++ encodeListWith f pad bs
  | [], acc => by simp [encodeListRevAccWith, encodeListWith]
  | [b0], acc => by cases pad <;> simp [encodeListRevAccWith, encodeListWith]
  | [b0, b1], acc => by cases pad <;> simp [encodeListRevAccWith, encodeListWith]
  | b0 :: b1 :: b2 :: rest, acc => by
      simp only [encodeListRevAccWith, encodeListWith]
      rw [encodeListRevAccWith_eq f pad rest]
      simp [List.append_assoc]

def encodeFast (bs : ByteArray) : String :=
  String.ofList (encodeListRevAccWith encodeChar true bs.data.toList [])

@[csimp] theorem encode_eq_fast : @encode = @encodeFast := by
  funext bs
  unfold encode encodeFast encodeList
  rw [encodeListRevAccWith_eq]
  simp

def encodeUrlFast (bs : ByteArray) : String :=
  String.ofList (encodeListRevAccWith (fun n => toUrlChar (encodeChar n)) false bs.data.toList [])

@[csimp] theorem encodeUrl_eq_fast : @encodeUrl = @encodeUrlFast := by
  funext bs
  unfold encodeUrl encodeUrlFast
  rw [encodeListRevAccWith_eq]
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
