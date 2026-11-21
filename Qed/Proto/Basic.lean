namespace Qed

/-- Alias for binary byte payloads (`ByteArray` natively, `Uint8Array` in JavaScript). -/
abbrev Bytes := ByteArray

namespace Proto

/-- Standard Protocol Buffers wire value tags:
    - `0`: Varint (`varint`, LEB128 unsigned / ZigZag signed / bool)
    - `1`: 64-bit little-endian (`fixed64` / IEEE-754 `Float`)
    - `2`: Length-delimited (`bytes`, UTF-8 `String`, embedded messages, packed arrays)
    - `5`: 32-bit little-endian (`fixed32`) -/
inductive WireVal where
  | varint  (n : Nat)
  | fixed64 (v : UInt64)
  | bytes   (b : ByteArray)
  | fixed32 (v : UInt32)
deriving Inhabited, BEq

def WireVal.wireType : WireVal → Nat
  | .varint _  => 0
  | .fixed64 _ => 1
  | .bytes _   => 2
  | .fixed32 _ => 5

/-! ## ZigZag Signed Integer Bijection (`sint32` / `sint64` / arbitrary `Int`) -/

def zigzagEncode (i : Int) : Nat :=
  match i with
  | .ofNat n   => 2 * n
  | .negSucc n => 2 * n + 1

def zigzagDecode (n : Nat) : Int :=
  if n % 2 == 0 then .ofNat (n / 2)
  else .negSucc (n / 2)

theorem zigzagDecode_zigzagEncode (i : Int) : zigzagDecode (zigzagEncode i) = i := by
  cases i with
  | ofNat n =>
      unfold zigzagEncode zigzagDecode
      have hmod : (2 * n) % 2 = 0 := by omega
      have hdiv : (2 * n) / 2 = n := by omega
      simp [hmod, hdiv]
  | negSucc n =>
      unfold zigzagEncode zigzagDecode
      have hmod : (2 * n + 1) % 2 = 1 := by omega
      have hdiv : (2 * n + 1) / 2 = n := by omega
      simp [hmod, hdiv]

/-! ## Pure Specification over `List UInt8` -/

def encodeVarintList (n : Nat) : List UInt8 :=
  if n < 128 then
    [UInt8.ofNat n]
  else
    UInt8.ofNat (n % 128 + 128) :: encodeVarintList (n / 128)
termination_by n

def decodeVarintList : List UInt8 → Except String (Nat × List UInt8)
  | [] => .error "protobuf: truncated varint"
  | b :: rest =>
      if b.toNat < 128 then
        .ok (b.toNat, rest)
      else do
        let (hi, rem) ← decodeVarintList rest
        return ((b.toNat - 128) + 128 * hi, rem)

def encodeLEList : Nat → Nat → List UInt8
  | 0, _     => []
  | k + 1, n => UInt8.ofNat (n % 256) :: encodeLEList k (n / 256)

def decodeLEList : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, bs          => some (0, bs)
  | k + 1, b :: bs => (decodeLEList k bs).map fun (hi, rem) => (b.toNat + 256 * hi, rem)
  | _ + 1, []      => none

def encodeFixed32List (v : UInt32) : List UInt8 := encodeLEList 4 v.toNat

def decodeFixed32List (bs : List UInt8) : Except String (UInt32 × List UInt8) :=
  match decodeLEList 4 bs with
  | some (n, rest) => .ok (UInt32.ofNat n, rest)
  | none           => .error "protobuf: truncated fixed32"

def encodeFixed64List (v : UInt64) : List UInt8 := encodeLEList 8 v.toNat

def decodeFixed64List (bs : List UInt8) : Except String (UInt64 × List UInt8) :=
  match decodeLEList 8 bs with
  | some (n, rest) => .ok (UInt64.ofNat n, rest)
  | none           => .error "protobuf: truncated fixed64"

def bytesToList (b : ByteArray) : List UInt8 := b.data.toList
def bytesOfList (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray

@[simp] theorem bytesToList_bytesOfList (xs : List UInt8) :
    bytesToList (bytesOfList xs) = xs := rfl

@[simp] theorem bytesOfList_bytesToList (b : ByteArray) :
    bytesOfList (bytesToList b) = b := by
  cases b; rfl

def encodePayloadList : WireVal → List UInt8
  | .varint n  => encodeVarintList n
  | .fixed64 v => encodeFixed64List v
  | .bytes b   => encodeVarintList b.size ++ bytesToList b
  | .fixed32 v => encodeFixed32List v

def encodeFieldList (fieldNum : Nat) (w : WireVal) : List UInt8 :=
  encodeVarintList (fieldNum * 8 + w.wireType) ++ encodePayloadList w

def encodeFieldsList : List (Nat × WireVal) → List UInt8
  | [] => []
  | (k, w) :: rest => encodeFieldList k w ++ encodeFieldsList rest

def splitExact : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  | 0, xs => some ([], xs)
  | n + 1, x :: xs =>
      match splitExact n xs with
      | some (pre, post) => some (x :: pre, post)
      | none => none
  | _ + 1, [] => none

def decodePayloadList (wireType : Nat) (bs : List UInt8) : Except String (WireVal × List UInt8) :=
  match wireType with
  | 0 => do
      let (n, rem) ← decodeVarintList bs
      return (.varint n, rem)
  | 1 => do
      let (v, rem) ← decodeFixed64List bs
      return (.fixed64 v, rem)
  | 2 => do
      let (len, afterLen) ← decodeVarintList bs
      match splitExact len afterLen with
      | some (chunk, rem) => .ok (.bytes (bytesOfList chunk), rem)
      | none => .error "protobuf: truncated length-delimited field"
  | 5 => do
      let (v, rem) ← decodeFixed32List bs
      return (.fixed32 v, rem)
  | wt => .error s!"protobuf: unsupported wire type {wt}"

def decodeFieldList (bs : List UInt8) : Except String ((Nat × WireVal) × List UInt8) := do
  let (tag, afterTag) ← decodeVarintList bs
  let fieldNum := tag / 8
  let wireType := tag % 8
  if fieldNum == 0 then
    .error "protobuf: invalid field number 0"
  else do
    let (w, rem) ← decodePayloadList wireType afterTag
    return ((fieldNum, w), rem)

def decodeFieldsAux : Nat → List UInt8 → List (Nat × WireVal) → Except String (List (Nat × WireVal))
  | _, [], acc => .ok acc.reverse
  | 0, _ :: _, _ => .error "protobuf: field budget exhausted"
  | fuel + 1, bs, acc => do
      let (fw, rem) ← decodeFieldList bs
      decodeFieldsAux fuel rem (fw :: acc)

def encodeFieldsSpec (fields : List (Nat × WireVal)) : ByteArray :=
  bytesOfList (encodeFieldsList fields)

def decodeFieldsSpec (buf : ByteArray) : Except String (List (Nat × WireVal)) :=
  let bs := bytesToList buf
  decodeFieldsAux bs.length bs []

/-! ## High-Throughput Direct `ByteArray` Writer & Borrowed Cursor Decoder (`@[csimp]`) -/

def writeVarint (buf : ByteArray) (n : Nat) : ByteArray :=
  if n < 128 then
    buf.push (UInt8.ofNat n)
  else
    writeVarint (buf.push (UInt8.ofNat (n % 128 + 128))) (n / 128)
termination_by n

def writeFixed32 (buf : ByteArray) (v : UInt32) : ByteArray :=
  let n := v.toNat
  (((buf.push (UInt8.ofNat (n % 256))).push
      (UInt8.ofNat ((n / 256) % 256))).push
      (UInt8.ofNat ((n / 65536) % 256))).push
      (UInt8.ofNat ((n / 16777216) % 256))

def writeFixed64 (buf : ByteArray) (v : UInt64) : ByteArray :=
  let n := v.toNat
  (((((((buf.push (UInt8.ofNat (n % 256))).push
      (UInt8.ofNat ((n / 256) % 256))).push
      (UInt8.ofNat ((n / 65536) % 256))).push
      (UInt8.ofNat ((n / 16777216) % 256))).push
      (UInt8.ofNat ((n / 4294967296) % 256))).push
      (UInt8.ofNat ((n / 1099511627776) % 256))).push
      (UInt8.ofNat ((n / 281474976710656) % 256))).push
      (UInt8.ofNat ((n / 72057594037927936) % 256))

def writePayload (buf : ByteArray) : WireVal → ByteArray
  | .varint n  => writeVarint buf n
  | .fixed64 v => writeFixed64 buf v
  | .bytes b   => (writeVarint buf b.size) ++ b
  | .fixed32 v => writeFixed32 buf v

def writeField (buf : ByteArray) (fieldNum : Nat) (w : WireVal) : ByteArray :=
  writePayload (writeVarint buf (fieldNum * 8 + w.wireType)) w

def writeFieldsLoop (buf : ByteArray) : List (Nat × WireVal) → ByteArray
  | [] => buf
  | (k, w) :: rest => writeFieldsLoop (writeField buf k w) rest

def encodeFieldsFast (fields : List (Nat × WireVal)) : ByteArray :=
  writeFieldsLoop (ByteArray.emptyWithCapacity 64) fields

/-- Borrowed-buffer cursor varint decoder: zero sub-array or list allocations. -/
def readVarintAt (buf : @& ByteArray) (pos limit : Nat) : Except String (Nat × Nat) :=
  if h : pos < limit ∧ limit ≤ buf.size then
    let b := buf[pos]'(Nat.lt_of_lt_of_le h.1 h.2)
    if b.toNat < 128 then
      .ok (b.toNat, pos + 1)
    else do
      let (hi, pos') ← readVarintAt buf (pos + 1) limit
      return ((b.toNat - 128) + 128 * hi, pos')
  else
    .error "protobuf: truncated varint"
termination_by limit - pos

def readFixed32At (buf : @& ByteArray) (pos limit : Nat) : Except String (UInt32 × Nat) :=
  if h : pos + 4 ≤ limit ∧ limit ≤ buf.size then
    let b0 := buf[pos]'(by omega); let b1 := buf[pos + 1]'(by omega)
    let b2 := buf[pos + 2]'(by omega); let b3 := buf[pos + 3]'(by omega)
    let n := b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))
    .ok (UInt32.ofNat n, pos + 4)
  else
    .error "protobuf: truncated fixed32"

def readFixed64At (buf : @& ByteArray) (pos limit : Nat) : Except String (UInt64 × Nat) :=
  if h : pos + 8 ≤ limit ∧ limit ≤ buf.size then
    let b0 := buf[pos]'(by omega); let b1 := buf[pos + 1]'(by omega)
    let b2 := buf[pos + 2]'(by omega); let b3 := buf[pos + 3]'(by omega)
    let b4 := buf[pos + 4]'(by omega); let b5 := buf[pos + 5]'(by omega)
    let b6 := buf[pos + 6]'(by omega); let b7 := buf[pos + 7]'(by omega)
    let n := b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat +
      256 * (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat))))))
    .ok (UInt64.ofNat n, pos + 8)
  else
    .error "protobuf: truncated fixed64"

def readPayloadAt (wireType : Nat) (buf : @& ByteArray) (pos limit : Nat) :
    Except String (WireVal × Nat) :=
  match wireType with
  | 0 => do
      let (n, pos') ← readVarintAt buf pos limit
      return (.varint n, pos')
  | 1 => do
      let (v, pos') ← readFixed64At buf pos limit
      return (.fixed64 v, pos')
  | 2 => do
      let (len, afterLen) ← readVarintAt buf pos limit
      if afterLen + len ≤ limit ∧ limit ≤ buf.size then
        let chunk := buf.extract afterLen (afterLen + len)
        .ok (.bytes chunk, afterLen + len)
      else
        .error "protobuf: truncated length-delimited field"
  | 5 => do
      let (v, pos') ← readFixed32At buf pos limit
      return (.fixed32 v, pos')
  | wt => .error s!"protobuf: unsupported wire type {wt}"

def readFieldAt (buf : @& ByteArray) (pos limit : Nat) : Except String ((Nat × WireVal) × Nat) := do
  let (tag, afterTag) ← readVarintAt buf pos limit
  let fieldNum := tag / 8
  let wireType := tag % 8
  if fieldNum == 0 then
    .error "protobuf: invalid field number 0"
  else do
    let (w, pos') ← readPayloadAt wireType buf afterTag limit
    return ((fieldNum, w), pos')

def readFieldsLoop (fuel : Nat) (buf : @& ByteArray) (pos limit : Nat)
    (acc : List (Nat × WireVal)) : Except String (List (Nat × WireVal)) :=
  if pos == limit then
    .ok acc.reverse
  else match fuel with
    | 0 => .error "protobuf: field budget exhausted"
    | fuel' + 1 =>
        let fallback := fun () => match readFieldAt buf pos limit with
          | .error e => .error e
          | .ok (fw, pos') => readFieldsLoop fuel' buf pos' limit (fw :: acc)
        if h2 : pos + 1 < limit ∧ limit ≤ buf.size then
          let tagB := buf[pos]'(by omega)
          let b1 := buf[pos + 1]'(by omega)
          if tagB.toNat < 128 && b1.toNat < 128 then
            let fn := tagB.toNat / 8
            let wt := tagB.toNat % 8
            if fn != 0 && wt == 0 then
              readFieldsLoop fuel' buf (pos + 2) limit ((fn, .varint b1.toNat) :: acc)
            else if fn != 0 && wt == 2 then
              let endPos := pos + 2 + b1.toNat
              if endPos ≤ limit then
                readFieldsLoop fuel' buf endPos limit ((fn, .bytes (buf.extract (pos + 2) endPos)) :: acc)
              else .error "protobuf: truncated length-delimited field"
            else fallback ()
          else fallback ()
        else fallback ()

def decodeFieldsFast (buf : ByteArray) : Except String (List (Nat × WireVal)) :=
  readFieldsLoop buf.size buf 0 buf.size []

/-! ## Field Lookup & Framed Envelopes -/

/-- Scalar field lookup: returns the first entry matching `fieldNum` while ignoring unknown
    field tags (`k' ≠ fieldNum`). For canonical schema encodings with distinct field numbers,
    first and last match coincide, making `skipUnknown_preserves_decode` immediate. -/
def lookupField (fieldNum : Nat) : List (Nat × WireVal) → Option WireVal
  | [] => none
  | (k, w) :: rest => if k == fieldNum then some w else lookupField fieldNum rest

def lookupRepeated (fieldNum : Nat) : List (Nat × WireVal) → List WireVal
  | [] => []
  | (k, w) :: rest =>
      if k == fieldNum then w :: lookupRepeated fieldNum rest
      else lookupRepeated fieldNum rest

/-- Length-prefixed Protobuf message frame (used for multi-message / streaming frames). -/
def encodeFrameList (payload : List UInt8) : List UInt8 :=
  encodeVarintList payload.length ++ payload

def decodeFrameList (bs : List UInt8) : Except String (List UInt8 × List UInt8) := do
  let (len, afterLen) ← decodeVarintList bs
  match splitExact len afterLen with
  | some (chunk, rem) => .ok (chunk, rem)
  | none => .error "protobuf: truncated frame"

/-! ## Hex Codec for `Bytes` JSON / SSR Interop -/

def hexByte (n : Nat) : Char :=
  let d := n % 16
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

def unhexChar (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else if 65 ≤ n && n ≤ 70 then some (n - 55)
  else none

def encodeHexList : List UInt8 → List Char
  | [] => []
  | b :: bs => hexByte (b.toNat / 16) :: hexByte (b.toNat % 16) :: encodeHexList bs

def decodeHexList : List Char → Option (List UInt8)
  | [] => some []
  | hi :: lo :: rest => do
      let h ← unhexChar hi
      let l ← unhexChar lo
      let tail ← decodeHexList rest
      return UInt8.ofNat (h * 16 + l) :: tail
  | [_] => none

def encodeHex (b : ByteArray) : String :=
  String.ofList (encodeHexList (bytesToList b))

def decodeHex (s : String) : Except String ByteArray :=
  match decodeHexList s.toList with
  | some xs => .ok (bytesOfList xs)
  | none    => .error "invalid hex byte string"

def encodeHexLoop (b : @& ByteArray) (i : Nat) (acc : List Char) : List Char :=
  if h : i < b.size then
    let v := b[i].toNat
    encodeHexLoop b (i + 1) (hexByte (v % 16) :: hexByte (v / 16) :: acc)
  else
    acc.reverse
termination_by b.size - i

def encodeHexFast (b : ByteArray) : String :=
  String.ofList (encodeHexLoop b 0 [])

def decodeHexBuf : List Char → ByteArray → Option ByteArray
  | [], out => some out
  | hi :: lo :: rest, out => do
      let h ← unhexChar hi
      let l ← unhexChar lo
      decodeHexBuf rest (out.push (UInt8.ofNat (h * 16 + l)))
  | [_], _ => none

def decodeHexFast (s : String) : Except String ByteArray :=
  match decodeHexBuf s.toList (ByteArray.emptyWithCapacity (s.utf8ByteSize / 2)) with
  | some out => .ok out
  | none     => .error "invalid hex byte string"

end Proto
end Qed
