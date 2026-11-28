import Qed.Html

namespace Qed

namespace Proto

inductive WireVal where
  | varint (n : Nat) | fixed64 (v : UInt64) | bytes (b : ByteArray) | fixed32 (v : UInt32)
deriving Inhabited, BEq

def WireVal.wireType : WireVal → Nat | .varint _ => 0 | .fixed64 _ => 1 | .bytes _ => 2 | .fixed32 _ => 5

def zigzagEncode : Int → Nat | .ofNat n => 2 * n | .negSucc n => 2 * n + 1
def zigzagDecode (n : Nat) : Int := if n % 2 == 0 then .ofNat (n / 2) else .negSucc (n / 2)
theorem zigzagDecode_zigzagEncode (i : Int) : zigzagDecode (zigzagEncode i) = i := by cases i <;> simp [zigzagEncode, zigzagDecode] <;> omega

def encodeVarintList (n : Nat) : List UInt8 :=
  if n < 128 then [UInt8.ofNat n] else UInt8.ofNat (n % 128 + 128) :: encodeVarintList (n / 128)
termination_by n

def decodeVarintList : List UInt8 → Except String (Nat × List UInt8)
  | [] => .error "protobuf: truncated varint"
  | b :: rest => if b.toNat < 128 then .ok (b.toNat, rest) else (decodeVarintList rest).map fun (hi, rem) => ((b.toNat - 128) + 128 * hi, rem)

def encodeLEList : Nat → Nat → List UInt8 | 0, _ => [] | k + 1, n => UInt8.ofNat (n % 256) :: encodeLEList k (n / 256)
def decodeLEList : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, bs => some (0, bs) | k + 1, b :: bs => (decodeLEList k bs).map fun (hi, rem) => (b.toNat + 256 * hi, rem) | _ + 1, [] => none
@[inline] def decodeLEExcept {α : Type} (k : Nat) (mk : Nat → α) (err : String) (bs : List UInt8) : Except String (α × List UInt8) :=
  (decodeLEList k bs).elim (.error err) fun (n, rest) => .ok (mk n, rest)

abbrev bytesToList (b : ByteArray) : List UInt8 := b.data.toList
abbrev bytesOfList (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩
@[simp] theorem bytesOfList_bytesToList (b : ByteArray) : bytesOfList (bytesToList b) = b := by cases b; rfl

def encodePayloadList : WireVal → List UInt8
  | .varint n => encodeVarintList n | .fixed64 v => encodeLEList 8 v.toNat
  | .bytes b => encodeVarintList b.size ++ bytesToList b | .fixed32 v => encodeLEList 4 v.toNat
def encodeFieldList (fieldNum : Nat) (w : WireVal) : List UInt8 := encodeVarintList (fieldNum * 8 + w.wireType) ++ encodePayloadList w
def encodeFieldsList : List (Nat × WireVal) → List UInt8 | [] => [] | (k, w) :: rest => encodeFieldList k w ++ encodeFieldsList rest

def splitExact : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, xs => some ([], xs) | n + 1, x :: xs => (splitExact n xs).map fun (pre, post) => (x :: pre, post) | _ + 1, [] => none

def decodePayloadList : Nat → List UInt8 → Except String (WireVal × List UInt8)
  | 0, bs => (decodeVarintList bs).map fun (n, rem) => (.varint n, rem)
  | 1, bs => (decodeLEExcept 8 UInt64.ofNat "protobuf: truncated fixed64" bs).map fun (v, rem) => (.fixed64 v, rem)
  | 2, bs => (decodeVarintList bs).bind fun (len, afterLen) =>
      (splitExact len afterLen).elim (.error "protobuf: truncated length-delimited field") fun (chunk, rem) => .ok (.bytes (bytesOfList chunk), rem)
  | 5, bs => (decodeLEExcept 4 UInt32.ofNat "protobuf: truncated fixed32" bs).map fun (v, rem) => (.fixed32 v, rem)
  | wt, _ => .error s!"protobuf: unsupported wire type {wt}"

def decodeFieldList (bs : List UInt8) : Except String ((Nat × WireVal) × List UInt8) :=
  (decodeVarintList bs).bind fun (tag, afterTag) =>
    let fieldNum := tag / 8
    if fieldNum == 0 then .error "protobuf: invalid field number 0"
    else (decodePayloadList (tag % 8) afterTag).map fun (w, rem) => ((fieldNum, w), rem)

def decodeFieldsAux : Nat → List UInt8 → List (Nat × WireVal) → Except String (List (Nat × WireVal))
  | _, [], acc => .ok acc.reverse | 0, _ :: _, _ => .error "protobuf: field budget exhausted"
  | fuel + 1, bs, acc => (decodeFieldList bs).bind fun (fw, rem) => decodeFieldsAux fuel rem (fw :: acc)

def encodeFieldsSpec (fields : List (Nat × WireVal)) : ByteArray := bytesOfList (encodeFieldsList fields)
def decodeFieldsSpec (buf : ByteArray) : Except String (List (Nat × WireVal)) := decodeFieldsAux buf.size (bytesToList buf) []

/-! ## High-Throughput Direct `ByteArray` Writer & Borrowed Cursor Decoder (`@[csimp]`) -/

def writeVarint (buf : ByteArray) (n : Nat) : ByteArray :=
  if n < 128 then buf.push (UInt8.ofNat n) else writeVarint (buf.push (UInt8.ofNat (n % 128 + 128))) (n / 128)
termination_by n

@[reducible, inline] def writeLE4 (buf : ByteArray) (n : Nat) : ByteArray :=
  (((buf.push (UInt8.ofNat (n % 256))).push (UInt8.ofNat ((n / 256) % 256))).push
    (UInt8.ofNat ((n / 65536) % 256))).push (UInt8.ofNat ((n / 16777216) % 256))

def writePayload (buf : ByteArray) : WireVal → ByteArray
  | .varint n => writeVarint buf n | .fixed64 v => writeLE4 (writeLE4 buf v.toNat) (v.toNat / 4294967296)
  | .bytes b => (writeVarint buf b.size) ++ b | .fixed32 v => writeLE4 buf v.toNat

def writeFieldsLoop (buf : ByteArray) : List (Nat × WireVal) → ByteArray
  | [] => buf | (k, w) :: rest => writeFieldsLoop (writePayload (writeVarint buf (k * 8 + w.wireType)) w) rest
def encodeFieldsFast (fields : List (Nat × WireVal)) : ByteArray := writeFieldsLoop (ByteArray.emptyWithCapacity 64) fields

def readVarintAt (buf : @& ByteArray) (pos limit : Nat) : Except String (Nat × Nat) :=
  if h : pos < limit ∧ limit ≤ buf.size then
    let b := buf[pos]'(Nat.lt_of_lt_of_le h.1 h.2)
    if b.toNat < 128 then .ok (b.toNat, pos + 1)
    else (readVarintAt buf (pos + 1) limit).map fun (hi, pos') => ((b.toNat - 128) + 128 * hi, pos')
  else .error "protobuf: truncated varint"
termination_by limit - pos

@[reducible, inline] def readLE4At (buf : @& ByteArray) (pos : Nat) (h : pos + 4 ≤ buf.size) : Nat :=
  (buf[pos]'(by omega)).toNat + 256 * ((buf[pos + 1]'(by omega)).toNat + 256 * ((buf[pos + 2]'(by omega)).toNat + 256 * (buf[pos + 3]'(by omega)).toNat))

@[inline] def readFixedAt {α : Type} (k : Nat) (mk : Nat → α) (err : String) (buf : @& ByteArray) (pos limit : Nat)
    (val : pos + k ≤ buf.size → Nat) : Except String (α × Nat) :=
  if h : pos + k ≤ limit ∧ limit ≤ buf.size then .ok (mk (val (by omega)), pos + k) else .error err

def readPayloadAt (wireType : Nat) (buf : @& ByteArray) (pos limit : Nat) : Except String (WireVal × Nat) :=
  match wireType with
  | 0 => (readVarintAt buf pos limit).map fun (n, p) => (.varint n, p)
  | 1 => (readFixedAt 8 UInt64.ofNat "protobuf: truncated fixed64" buf pos limit fun h =>
      readLE4At buf pos (by omega) + 4294967296 * readLE4At buf (pos + 4) (by omega)).map fun (v, p) => (.fixed64 v, p)
  | 2 => (readVarintAt buf pos limit).bind fun (len, afterLen) =>
      if afterLen + len ≤ limit ∧ limit ≤ buf.size then .ok (.bytes (buf.extract afterLen (afterLen + len)), afterLen + len)
      else .error "protobuf: truncated length-delimited field"
  | 5 => (readFixedAt 4 UInt32.ofNat "protobuf: truncated fixed32" buf pos limit (readLE4At buf pos)).map fun (v, p) => (.fixed32 v, p)
  | wt => .error s!"protobuf: unsupported wire type {wt}"

def readFieldAt (buf : @& ByteArray) (pos limit : Nat) : Except String ((Nat × WireVal) × Nat) :=
  (readVarintAt buf pos limit).bind fun (tag, afterTag) =>
    let fieldNum := tag / 8
    if fieldNum == 0 then .error "protobuf: invalid field number 0"
    else (readPayloadAt (tag % 8) buf afterTag limit).map fun (w, pos') => ((fieldNum, w), pos')

def readFieldsLoop (fuel : Nat) (buf : @& ByteArray) (pos limit : Nat) (acc : List (Nat × WireVal)) : Except String (List (Nat × WireVal)) :=
  if pos == limit then .ok acc.reverse
  else match fuel with
    | 0 => .error "protobuf: field budget exhausted"
    | fuel' + 1 =>
        let fallback := fun () => match readFieldAt buf pos limit with | .error e => .error e | .ok (fw, pos') => readFieldsLoop fuel' buf pos' limit (fw :: acc)
        if h2 : pos + 1 < limit ∧ limit ≤ buf.size then
          let tagB := buf[pos]'(by omega); let b1 := buf[pos + 1]'(by omega)
          if tagB.toNat < 128 && b1.toNat < 128 then
            let fn := tagB.toNat / 8; let wt := tagB.toNat % 8
            if fn != 0 then
              if wt == 0 then readFieldsLoop fuel' buf (pos + 2) limit ((fn, .varint b1.toNat) :: acc)
              else if wt == 2 then
                let endPos := pos + 2 + b1.toNat
                if endPos ≤ limit then readFieldsLoop fuel' buf endPos limit ((fn, .bytes (buf.extract (pos + 2) endPos)) :: acc)
                else .error "protobuf: truncated length-delimited field"
              else fallback ()
            else fallback ()
          else fallback ()
        else fallback ()

def decodeFieldsFast (buf : ByteArray) : Except String (List (Nat × WireVal)) := readFieldsLoop buf.size buf 0 buf.size []

/-! ## Field Lookup, Framing & Hex Codec -/

def lookupField (fieldNum : Nat) : List (Nat × WireVal) → Option WireVal
  | [] => none | (k, w) :: rest => if k == fieldNum then some w else lookupField fieldNum rest
def lookupRepeated (fieldNum : Nat) : List (Nat × WireVal) → List WireVal
  | [] => [] | (k, w) :: rest => if k == fieldNum then w :: lookupRepeated fieldNum rest else lookupRepeated fieldNum rest

def encodeFrameList (payload : List UInt8) : List UInt8 := encodeVarintList payload.length ++ payload
def decodeFrameList (bs : List UInt8) : Except String (List UInt8 × List UInt8) :=
  (decodeVarintList bs).bind fun (len, afterLen) => (splitExact len afterLen).elim (.error "protobuf: truncated frame") .ok

@[inline] def unhexByte (hi lo : Char) : Option UInt8 := (unhexNat? hi).bind fun h => (unhexNat? lo).map fun l => UInt8.ofNat (h * 16 + l)
def encodeHexList : List UInt8 → List Char | [] => [] | b :: bs => hexDigitLower (b.toNat / 16) :: hexDigitLower (b.toNat % 16) :: encodeHexList bs
def decodeHexList : List Char → Option (List UInt8)
  | [] => some [] | hi :: lo :: rest => (unhexByte hi lo).bind fun b => (decodeHexList rest).map (b :: ·) | [_] => none
def encodeHex (b : ByteArray) : String := String.ofList (encodeHexList (bytesToList b))
def decodeHex (s : String) : Except String ByteArray := (decodeHexList s.toList).elim (.error "invalid hex byte string") (.ok ∘ bytesOfList)

def encodeHexLoop (b : @& ByteArray) (i : Nat) (acc : List Char) : List Char :=
  if h : i < b.size then let v := b[i].toNat; encodeHexLoop b (i + 1) (hexDigitLower (v % 16) :: hexDigitLower (v / 16) :: acc)
  else acc.reverse
termination_by b.size - i
def decodeHexBuf : List Char → ByteArray → Option ByteArray
  | [], out => some out | hi :: lo :: rest, out => (unhexByte hi lo).bind fun b => decodeHexBuf rest (out.push b) | [_], _ => none
def encodeHexFast (b : ByteArray) : String := String.ofList (encodeHexLoop b 0 [])
def decodeHexFast (s : String) : Except String ByteArray :=
  (decodeHexBuf s.toList (ByteArray.emptyWithCapacity (s.utf8ByteSize / 2))).elim (.error "invalid hex byte string") .ok

end Proto
end Qed
