namespace Qed.Base64

def encodeChar (n : Nat) : Char :=
  if n < 26 then Char.ofNat (65 + n) else if n < 52 then Char.ofNat (71 + n)
  else if n < 62 then Char.ofNat (n - 4) else if n == 62 then '+' else '/'
def decodeChar (c : Char) : Option Nat :=
  let n := c.toNat
  if 65 ≤ n && n ≤ 90 then some (n - 65) else if 97 ≤ n && n ≤ 122 then some (n - 71)
  else if 48 ≤ n && n ≤ 57 then some (n + 4) else if n == 43 then some 62 else if n == 47 then some 63 else none
def isUrlChar (c : Char) : Bool := ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '-' || c == '_'
def toUrlChar : Char → Char | '+' => '-' | '/' => '_' | c => c
def fromUrlChar : Char → Char | '-' => '+' | '_' => '/' | c => c

private def decChar (c : Char) : Except String Nat := (decodeChar c).elim (.error "base64: invalid character") .ok
private theorem char_spec : ∀ n : Fin 64, decodeChar (encodeChar n.val) = some n.val ∧ isUrlChar (toUrlChar (encodeChar n.val)) = true := by decide
private theorem dec_enc (n : Nat) (h : n < 64) : decChar (encodeChar n) = .ok n := by simp [decChar, (char_spec ⟨n, h⟩).1]
private theorem enc_ne_pad (n : Nat) (h : n < 64) : (encodeChar n == '=') = false := beq_false_of_ne fun heq => by have h1 := (char_spec ⟨n, h⟩).1; rw [heq] at h1; cases h1

def encodeListWith (f : Nat → Char) (pad : Bool) : List UInt8 → List Char
  | [] => []
  | [b0] => let n0 := b0.toNat; let cs := [f (n0 / 4), f ((n0 % 4) * 16)]; if pad then cs ++ ['=', '='] else cs
  | [b0, b1] => let n0 := b0.toNat; let n1 := b1.toNat; let cs := [f (n0 / 4), f ((n0 % 4) * 16 + n1 / 16), f ((n1 % 16) * 4)]; if pad then cs ++ ['='] else cs
  | b0 :: b1 :: b2 :: rest =>
      let n0 := b0.toNat; let n1 := b1.toNat; let n2 := b2.toNat
      f (n0 / 4) :: f ((n0 % 4) * 16 + n1 / 16) :: f ((n1 % 16) * 4 + n2 / 64) :: f (n2 % 64) :: encodeListWith f pad rest

def decodeQuad (c0 c1 c2 c3 : Char) (isLast : Bool) : Except String (List UInt8) :=
  (decChar c0).bind fun v0 => (decChar c1).bind fun v1 =>
    let b0 := UInt8.ofNat (v0 * 4 + v1 / 16)
    if isLast && c2 == '=' && c3 == '=' then .ok [b0]
    else (decChar c2).bind fun v2 =>
      let b1 := UInt8.ofNat ((v1 % 16) * 16 + v2 / 4)
      if isLast && c3 == '=' then .ok [b0, b1]
      else (decChar c3).map fun v3 => [b0, b1, UInt8.ofNat ((v2 % 4) * 64 + v3)]

def decodeList : List Char → Except String (List UInt8)
  | [] => .ok []
  | c0 :: c1 :: c2 :: c3 :: rest => (decodeQuad c0 c1 c2 c3 rest.isEmpty).bind fun chunk => (decodeList rest).map (chunk ++ ·)
  | _ => .error "base64: invalid length"

private theorem u8_eq (b : UInt8) {k : Nat} (h : k = b.toNat) : UInt8.ofNat k = b := h ▸ UInt8.ofNat_toNat

theorem decodeList_encodeList : ∀ bs : List UInt8, decodeList (encodeListWith encodeChar true bs) = .ok bs
  | [] => rfl
  | [b0] => by
      have := b0.toNat_lt
      simp only [encodeListWith, decodeList, decodeQuad, List.isEmpty_nil, beq_self_eq_true, Bool.and_self, ↓reduceIte, List.cons_append, List.nil_append]
      repeat rw [dec_enc _ (by omega)]
      simp only [Except.bind, Except.map, List.append_nil, Except.ok.injEq, List.cons.injEq, and_true]; exact u8_eq b0 (by omega)
  | [b0, b1] => by
      have := b0.toNat_lt; have := b1.toNat_lt
      simp only [encodeListWith, ↓reduceIte, List.cons_append, List.nil_append, decodeList, decodeQuad, List.isEmpty_nil]
      repeat rw [dec_enc _ (by omega)]
      simp only [Except.bind, enc_ne_pad ((b1.toNat % 16) * 4) (by omega), beq_self_eq_true, Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Except.map, List.append_nil, Except.ok.injEq, List.cons.injEq, and_true]
      exact ⟨u8_eq b0 (by omega), u8_eq b1 (by omega)⟩
  | b0 :: b1 :: b2 :: rest => by
      have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt
      simp only [encodeListWith, decodeList, decodeQuad]
      repeat rw [dec_enc _ (by omega)]
      simp only [Except.bind, Except.map, enc_ne_pad (b2.toNat % 64) (by omega), Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        decodeList_encodeList rest, List.cons_append, List.nil_append, Except.ok.injEq, List.cons.injEq, and_true]
      exact ⟨u8_eq b0 (by omega), u8_eq b1 (by omega), u8_eq b2 (by omega)⟩

def encode (bs : ByteArray) : String := String.ofList (encodeListWith encodeChar true bs.data.toList)
def decode (s : String) : Except String ByteArray := (decodeList s.toList).map fun xs => ByteArray.mk xs.toArray
theorem decode_encode (bs : ByteArray) : decode (encode bs) = .ok bs := by unfold decode encode; rw [String.toList_ofList, decodeList_encodeList]; cases bs; rfl

def encodeUrl (bs : ByteArray) : String := String.ofList (encodeListWith (fun n => toUrlChar (encodeChar n)) false bs.data.toList)
def decodeUrl (s : String) : Except String ByteArray :=
  let cs := s.toList; let stripped := if cs.isEmpty then [] else (cs.reverse.dropWhile (· == '=')).reverse
  if stripped.length % 4 == 1 then .error "base64url: invalid length"
  else if stripped.any (fun c => c == '+' || c == '/' || c == '=') then .error "base64url: invalid character"
  else let m := stripped.map fromUrlChar; decode (String.ofList (m ++ match m.length % 4 with | 2 => ['=', '='] | 3 => ['='] | _ => []))

private theorem encodeListWith_all (f : Nat → Char) (p : Char → Bool) (hf : ∀ {n}, n < 64 → p (f n) = true) :
    ∀ bs : List UInt8, (encodeListWith f false bs).all p = true
  | [] => rfl
  | [b0] => by have := b0.toNat_lt; simp only [encodeListWith, Bool.false_eq_true, ↓reduceIte, List.all_cons, List.all_nil, Bool.and_true]; rw [hf (by omega), hf (by omega)]; rfl
  | [b0, b1] => by have := b0.toNat_lt; have := b1.toNat_lt; simp only [encodeListWith, Bool.false_eq_true, ↓reduceIte, List.all_cons, List.all_nil, Bool.and_true]; rw [hf (by omega), hf (by omega), hf (by omega)]; rfl
  | b0 :: b1 :: b2 :: rest => by
      have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt
      simp only [encodeListWith, List.all_cons, encodeListWith_all f p hf rest, Bool.and_true]; rw [hf (by omega), hf (by omega), hf (by omega), hf (by omega)]; rfl

theorem encodeUrl_safe (bs : ByteArray) : (encodeUrl bs).toList.all isUrlChar = true := by
  unfold encodeUrl; rw [String.toList_ofList]; exact encodeListWith_all (fun n => toUrlChar (encodeChar n)) isUrlChar (fun h => (char_spec ⟨_, h⟩).2) bs.data.toList

/-! ## Tail-Recursive O(1)-Stack Fast Implementations (`@[csimp]`) -/

private def encodeListRevAccWith (f : Nat → Char) (pad : Bool) : List UInt8 → List Char → List Char
  | [], acc => acc.reverse
  | [b0], acc => let n0 := b0.toNat; let a := f ((n0 % 4) * 16) :: f (n0 / 4) :: acc; (if pad then '=' :: '=' :: a else a).reverse
  | [b0, b1], acc => let n0 := b0.toNat; let n1 := b1.toNat; let a := f ((n1 % 16) * 4) :: f ((n0 % 4) * 16 + n1 / 16) :: f (n0 / 4) :: acc; (if pad then '=' :: a else a).reverse
  | b0 :: b1 :: b2 :: rest, acc => let n0 := b0.toNat; let n1 := b1.toNat; let n2 := b2.toNat; encodeListRevAccWith f pad rest (f (n2 % 64) :: f ((n1 % 16) * 4 + n2 / 64) :: f ((n0 % 4) * 16 + n1 / 16) :: f (n0 / 4) :: acc)

private theorem encodeListRevAccWith_eq (f : Nat → Char) (pad : Bool) : ∀ (bs : List UInt8) (acc : List Char), encodeListRevAccWith f pad bs acc = acc.reverse ++ encodeListWith f pad bs
  | [], _ => by simp [encodeListRevAccWith, encodeListWith]
  | [_], _ | [_, _], _ => by cases pad <;> simp [encodeListRevAccWith, encodeListWith]
  | _ :: _ :: _ :: rest, _ => by simp only [encodeListRevAccWith, encodeListWith]; rw [encodeListRevAccWith_eq f pad rest]; simp [List.append_assoc]

def encodeFast (bs : ByteArray) : String := String.ofList (encodeListRevAccWith encodeChar true bs.data.toList [])
@[csimp] theorem encode_eq_fast : @encode = @encodeFast := by funext bs; unfold encode encodeFast; rw [encodeListRevAccWith_eq]; simp
def encodeUrlFast (bs : ByteArray) : String := String.ofList (encodeListRevAccWith (fun n => toUrlChar (encodeChar n)) false bs.data.toList [])
@[csimp] theorem encodeUrl_eq_fast : @encodeUrl = @encodeUrlFast := by funext bs; unfold encodeUrl encodeUrlFast; rw [encodeListRevAccWith_eq]; simp

private def decodeBufAcc : List Char → List UInt8 → Except String (List UInt8)
  | [], acc => .ok acc.reverse
  | c0 :: c1 :: c2 :: c3 :: rest, acc => (decodeQuad c0 c1 c2 c3 rest.isEmpty).bind fun chunk => decodeBufAcc rest (chunk.reverse ++ acc)
  | _, _ => .error "base64: invalid length"

private theorem decodeBufAcc_eq : ∀ (cs : List Char) (acc : List UInt8), decodeBufAcc cs acc = (decodeList cs).map (acc.reverse ++ ·)
  | [], _ | [_], _ | [_, _], _ | [_, _, _], _ => by simp [decodeBufAcc, decodeList, Except.map]
  | c0 :: c1 :: c2 :: c3 :: rest, acc => by
      unfold decodeBufAcc decodeList; cases decodeQuad c0 c1 c2 c3 rest.isEmpty with
      | error _ => rfl | ok chunk => dsimp only [Except.bind]; rw [decodeBufAcc_eq rest]; cases decodeList rest <;> simp [Except.map, List.append_assoc]

def decodeFast (s : String) : Except String ByteArray := (decodeBufAcc s.toList []).map fun xs => ByteArray.mk xs.toArray
@[csimp] theorem decode_eq_fast : @decode = @decodeFast := by funext s; unfold decode decodeFast; rw [decodeBufAcc_eq]; cases decodeList s.toList <;> simp [Except.map]

end Qed.Base64
