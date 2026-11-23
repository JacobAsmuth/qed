import Qed.Proto.Basic
import Qed.Proto.Proofs
import Qed.Json.Lawful
import Qed.Date

namespace Qed

open Qed.Proto

/-! ## JSON Codec for `Bytes` (`ByteArray`) via Verified Hex Bijection -/

instance : ToJson ByteArray where
  toJson b := .str (encodeHex b)

instance : FromJson ByteArray where
  fromJson
    | .str s => decodeHex s
    | _      => .error "expected hex-encoded byte string"

instance : LawfulJson ByteArray where
  fromJson_toJson b := decodeHex_encodeHex b

instance : NonNullJson ByteArray := ⟨nofun⟩

/-! ## Binary Protocol Buffers Typeclasses (`ToProto`, `FromProto`, `LawfulProto`) -/

class ToProto (α : Type) where
  toProtoVal : α → WireVal
  toProtoMsg : α → List (Nat × WireVal) := fun a => [(1, toProtoVal a)]

class FromProto (α : Type) where
  fromProtoVal : WireVal → Except String α
  fromProtoMsg : List (Nat × WireVal) → Except String α := fun fs =>
    match lookupField 1 fs with
    | some w => fromProtoVal w
    | none   => .error "protobuf: missing value field 1"

class LawfulProto (α : Type) extends ToProto α, FromProto α where
  msg_tags_pos : ∀ (a : α) (kw : Nat × WireVal), kw ∈ toProtoMsg a → 0 < kw.1
  fromProtoVal_toProtoVal : ∀ a : α, fromProtoVal (toProtoVal a) = .ok a
  fromProtoMsg_toProtoMsg : ∀ a : α, fromProtoMsg (toProtoMsg a) = .ok a

@[simp] theorem fromProtoVal_toProtoVal_simp {α : Type} [LawfulProto α] (a : α) :
    FromProto.fromProtoVal (ToProto.toProtoVal a) = .ok a :=
  LawfulProto.fromProtoVal_toProtoVal a

@[simp] theorem fromProtoMsg_toProtoMsg_simp {α : Type} [LawfulProto α] (a : α) :
    FromProto.fromProtoMsg (ToProto.toProtoMsg a) = .ok a :=
  LawfulProto.fromProtoMsg_toProtoMsg a

@[reducible] def LawfulProto.ofScalar {α : Type} [t : ToProto α] [f : FromProto α]
    (hval : ∀ a : α, f.fromProtoVal (t.toProtoVal a) = .ok a)
    (hmsg : ∀ a : α, t.toProtoMsg a = [(1, t.toProtoVal a)] := by intro _; rfl)
    (hfmsg : ∀ fs, f.fromProtoMsg fs =
      (match lookupField 1 fs with
       | some w => f.fromProtoVal w
       | none   => .error "protobuf: missing value field 1") := by intro _; rfl) : LawfulProto α where
  msg_tags_pos a kw h := by
    rw [hmsg] at h
    simp only [List.mem_singleton] at h
    rw [h]
    simp
  fromProtoVal_toProtoVal := hval
  fromProtoMsg_toProtoMsg a := by
    rw [hmsg, hfmsg]
    simp [lookupField, hval]

namespace Proto

/-- Top-level binary Protocol Buffers encoder. Structs and `Unit` encode directly without outer
    wrapping; standalone scalars and arrays encode using standard field-1 wrapper messages. -/
def encode {α : Type} [ToProto α] (a : α) : ByteArray :=
  encodeFieldsSpec (ToProto.toProtoMsg a)

/-- Top-level binary Protocol Buffers decoder. -/
def decode {α : Type} [FromProto α] (buf : ByteArray) : Except String α :=
  (decodeFieldsSpec buf).bind FromProto.fromProtoMsg

@[simp] theorem decode_encode {α : Type} [LawfulProto α] (a : α) :
    Proto.decode (Proto.encode a) = .ok a := by
  unfold Proto.decode Proto.encode
  rw [decodeFieldsSpec_encodeFieldsSpec _ (LawfulProto.msg_tags_pos a)]
  exact LawfulProto.fromProtoMsg_toProtoMsg a

/-- Direct `[FromProto α]` field lookup (avoids `FromProtoField` priority coercion on `Option α`). -/
def decodeFieldVal {α : Type} [FromProto α] (k : Nat) (fs : List (Nat × WireVal))
    (err : String := s!"protobuf: missing field {k}") : Except String α :=
  match lookupField k fs with | some w => FromProto.fromProtoVal w | none => .error err

end Proto

/-! ## Primitive & Scalar `LawfulProto` Instances -/

instance : ToProto Unit where
  toProtoVal _ := .bytes ByteArray.empty
  toProtoMsg _ := []

instance : FromProto Unit where
  fromProtoVal
    | .bytes _ => .ok ()
    | _        => .error "protobuf: expected unit bytes"
  fromProtoMsg _ := .ok ()

instance : LawfulProto Unit where
  msg_tags_pos _ _ h := by cases h
  fromProtoVal_toProtoVal _ := rfl
  fromProtoMsg_toProtoMsg _ := rfl

instance : ToProto Bool where
  toProtoVal
    | false => .varint 0
    | true  => .varint 1

instance : FromProto Bool where
  fromProtoVal
    | .varint 0 => .ok false
    | .varint 1 => .ok true
    | .varint n => .error s!"protobuf: invalid bool varint {n}"
    | _         => .error "protobuf: expected varint for Bool"

instance : LawfulProto Bool :=
  .ofScalar (by intro b; cases b <;> rfl)

local macro "defDirectProto " ty:ident ctor:ident err:str : command => do
  return ⟨Lean.mkNullNode #[
    ← `(command| instance : ToProto $ty where toProtoVal x := $ctor x),
    ← `(command| instance : FromProto $ty where fromProtoVal | $ctor x => .ok x | _ => .error $err),
    ← `(command| instance : LawfulProto $ty := .ofScalar fun _ => rfl)
  ]⟩

defDirectProto Nat WireVal.varint "protobuf: expected varint for Nat"

instance : ToProto Int where
  toProtoVal i := .varint (zigzagEncode i)

instance : FromProto Int where
  fromProtoVal
    | .varint n => .ok (zigzagDecode n)
    | _         => .error "protobuf: expected ZigZag varint for Int"

instance : LawfulProto Int :=
  .ofScalar (fun i => by simp [FromProto.fromProtoVal, zigzagDecode_zigzagEncode])

instance : ToProto UInt8 where
  toProtoVal b := .varint b.toNat

instance : FromProto UInt8 where
  fromProtoVal
    | .varint n =>
        if n < 256 then .ok (UInt8.ofNat n)
        else .error s!"protobuf: UInt8 out of range ({n})"
    | _ => .error "protobuf: expected varint for UInt8"

instance : LawfulProto UInt8 :=
  .ofScalar fun b => by
    have hb : b.toNat < 256 := b.toBitVec.isLt
    have heq : UInt8.ofNat b.toNat = b := uint8_ext (by change b.toNat % 256 = b.toNat; omega)
    simp [FromProto.fromProtoVal, hb, heq]

defDirectProto UInt32 WireVal.fixed32 "protobuf: expected fixed32 for UInt32"
defDirectProto UInt64 WireVal.fixed64 "protobuf: expected fixed64 for UInt64"

instance : ToProto Float where
  toProtoVal f := .fixed64 f.toBits

instance : FromProto Float where
  fromProtoVal
    | .fixed64 bits => .ok (Float.ofBits bits)
    | _             => .error "protobuf: expected fixed64 for Float"

defDirectProto ByteArray WireVal.bytes "protobuf: expected length-delimited bytes"

instance : ToProto String where
  toProtoVal s := .bytes s.toUTF8

instance : FromProto String where
  fromProtoVal
    | .bytes b =>
        match String.fromUTF8? b with
        | some s => .ok s
        | none   => .error "protobuf: invalid UTF-8 string"
    | _ => .error "protobuf: expected length-delimited UTF-8 string"

instance : LawfulProto String :=
  .ofScalar fun s => by
    cases s with | ofByteArray ba h =>
    simp [FromProto.fromProtoVal, String.fromUTF8?, String.toUTF8, h, String.fromUTF8]

/-! ## Structured Message Field Helpers (`ToProtoField`, `FromProtoField`, `LawfulProtoField`) -/

class ToProtoField (α : Type) where
  encodeProtoField : Nat → α → List (Nat × WireVal)

class FromProtoField (α : Type) where
  decodeProtoField : Nat → List (Nat × WireVal) → Except String α

class LawfulProtoField (α : Type) extends ToProtoField α, FromProtoField α where
  encodeProtoField_tag : ∀ (k : Nat) (a : α) (kw : Nat × WireVal),
    kw ∈ encodeProtoField k a → kw.1 = k
  decodeProtoField_skip_prefix : ∀ (k : Nat) (pre rest : List (Nat × WireVal)),
    (∀ kw ∈ pre, kw.1 ≠ k) →
    decodeProtoField k (pre ++ rest) = decodeProtoField k rest
  decodeProtoField_hit_raw : ∀ (k : Nat) (a : α) (rest : List (Nat × WireVal)),
    (∀ kw ∈ rest, kw.1 ≠ k) →
    decodeProtoField k (encodeProtoField k a ++ rest) = .ok a

instance (priority := low) {α : Type} [ToProto α] : ToProtoField α where
  encodeProtoField k a := [(k, ToProto.toProtoVal a)]

instance (priority := low) {α : Type} [FromProto α] : FromProtoField α where
  decodeProtoField k fs :=
    match lookupField k fs with
    | some w => FromProto.fromProtoVal w
    | none   => .error s!"protobuf: missing field {k}"

instance (priority := low) {α : Type} [LawfulProto α] : LawfulProtoField α where
  encodeProtoField_tag k _ kw h := by
    simp only [ToProtoField.encodeProtoField, List.mem_singleton] at h
    subst h
    rfl
  decodeProtoField_skip_prefix k pre rest hne := by
    simp [FromProtoField.decodeProtoField, skipUnknown_preserves_lookup_prefix k pre rest hne]
  decodeProtoField_hit_raw k a rest _ := by
    simp [ToProtoField.encodeProtoField, FromProtoField.decodeProtoField, lookupField]

/-- Optional message fields omit `none` (0 wire bytes) and decode missing tags as `none` for
    seamless rolling-deploy schema evolution. -/
instance {α : Type} [ToProto α] : ToProtoField (Option α) where
  encodeProtoField k
    | none   => []
    | some a => [(k, ToProto.toProtoVal a)]

instance {α : Type} [FromProto α] : FromProtoField (Option α) where
  decodeProtoField k fs :=
    match lookupField k fs with
    | none   => .ok none
    | some w => (FromProto.fromProtoVal w).map some

instance {α : Type} [LawfulProto α] : LawfulProtoField (Option α) where
  encodeProtoField_tag k opt kw h := by
    cases opt with
    | none => cases h
    | some a =>
        simp only [ToProtoField.encodeProtoField, List.mem_singleton] at h
        subst h
        rfl
  decodeProtoField_skip_prefix k pre rest hne := by
    simp [FromProtoField.decodeProtoField, skipUnknown_preserves_lookup_prefix k pre rest hne]
  decodeProtoField_hit_raw k opt rest hne := by
    cases opt with
    | none =>
        have hnone : lookupField k rest = lookupField k [] := by
          simpa using skipUnknown_preserves_lookup_prefix k rest [] hne
        simp [ToProtoField.encodeProtoField, FromProtoField.decodeProtoField, hnone, lookupField]
    | some a =>
        simp [ToProtoField.encodeProtoField, FromProtoField.decodeProtoField, lookupField, Except.map]

namespace Proto

/-- Predicate stating that every field number in `fs` is strictly greater than `k`. -/
def AllTagsGt (k : Nat) : List (Nat × WireVal) → Prop
  | [] => True
  | (j, _) :: rest => k < j ∧ AllTagsGt k rest

@[simp] theorem allTagsGt_nil (k : Nat) : AllTagsGt k [] := trivial

theorem allTagsGt_ne {k : Nat} :
    ∀ {fs : List (Nat × WireVal)}, AllTagsGt k fs → ∀ kw ∈ fs, kw.1 ≠ k
  | [], _, _, h => by cases h
  | (j, w) :: rest, ⟨hj, hrest⟩, kw, hm => by
      simp only [List.mem_cons] at hm
      rcases hm with rfl | hm'
      · omega
      · exact allTagsGt_ne hrest kw hm'

private theorem allTagsGt_append_aux {k j : Nat} (hj : k < j) {rest : List (Nat × WireVal)}
    (hr : AllTagsGt k rest) :
    ∀ (xs : List (Nat × WireVal)), (∀ kw ∈ xs, kw.1 = j) → AllTagsGt k (xs ++ rest)
  | [], _ => hr
  | (t, w) :: tail, htag => by
      have ht : t = j := htag (t, w) (by simp)
      subst ht
      exact ⟨hj, allTagsGt_append_aux hj hr tail fun kw hm => htag kw (by simp [hm])⟩

theorem allTagsGt_encodeAppend {α : Type} [LawfulProtoField α] {k j : Nat}
    (hj : k < j) (a : α) {rest : List (Nat × WireVal)} (hr : AllTagsGt k rest) :
    AllTagsGt k (ToProtoField.encodeProtoField j a ++ rest) :=
  allTagsGt_append_aux hj hr _ (LawfulProtoField.encodeProtoField_tag j a)

theorem msg_tags_pos_encodeAppend {α : Type} [LawfulProtoField α] {k : Nat}
    (hk : 0 < k) (a : α) {rest : List (Nat × WireVal)}
    (hr : ∀ kw ∈ rest, 0 < kw.1) :
    ∀ kw ∈ ToProtoField.encodeProtoField k a ++ rest, 0 < kw.1 := by
  intro kw hm
  rcases List.mem_append.1 hm with h1 | h2
  · have := LawfulProtoField.encodeProtoField_tag k a kw h1
    omega
  · exact hr kw h2

theorem decodeProtoField_skip {α β : Type} [LawfulProtoField α] [LawfulProtoField β]
    {k j : Nat} (hne : j ≠ k) (b : β) (rest : List (Nat × WireVal)) :
    FromProtoField.decodeProtoField (α := α) k (ToProtoField.encodeProtoField j b ++ rest) =
      FromProtoField.decodeProtoField (α := α) k rest := by
  apply LawfulProtoField.decodeProtoField_skip_prefix
  intro kw hm
  have := LawfulProtoField.encodeProtoField_tag j b kw hm
  omega

theorem decodeProtoField_hit {α : Type} [LawfulProtoField α] (k : Nat) (a : α)
    (rest : List (Nat × WireVal)) (hgt : AllTagsGt k rest) :
    FromProtoField.decodeProtoField k (ToProtoField.encodeProtoField k a ++ rest) = .ok a :=
  LawfulProtoField.decodeProtoField_hit_raw k a rest (allTagsGt_ne hgt)

/-- Helper constructor for message-shaped `ToProto`/`FromProto` instances from field encoders. -/
def encodeEmbedded (fields : List (Nat × WireVal)) : WireVal :=
  .bytes (encodeFieldsSpec fields)

def decodeEmbedded (w : WireVal) (k : List (Nat × WireVal) → Except String α) : Except String α :=
  match w with
  | .bytes b => (decodeFieldsSpec b).bind k
  | _        => .error "protobuf: expected embedded message bytes"

theorem decodeEmbedded_encodeEmbedded {α : Type} (fields : List (Nat × WireVal))
    (k : List (Nat × WireVal) → Except String α) (a : α)
    (hpos : ∀ kw ∈ fields, 0 < kw.1)
    (hk : k fields = .ok a) :
    decodeEmbedded (encodeEmbedded fields) k = .ok a := by
  unfold decodeEmbedded encodeEmbedded
  dsimp only
  rw [decodeFieldsSpec_encodeFieldsSpec fields hpos]
  exact hk

end Proto

@[reducible] def ToProto.ofFields {α : Type} (enc : α → List (Nat × WireVal)) : ToProto α where
  toProtoMsg := enc
  toProtoVal a := Proto.encodeEmbedded (enc a)

@[reducible] def FromProto.ofFields {α : Type} (dec : List (Nat × WireVal) → Except String α) : FromProto α where
  fromProtoMsg := dec
  fromProtoVal w := Proto.decodeEmbedded w dec

@[reducible] def LawfulProto.ofFields {α : Type}
    (enc : α → List (Nat × WireVal))
    (dec : List (Nat × WireVal) → Except String α)
    (htags : ∀ (a : α) (kw : Nat × WireVal), kw ∈ enc a → 0 < kw.1)
    (hrt : ∀ a : α, dec (enc a) = .ok a) : LawfulProto α where
  toToProto := ToProto.ofFields enc
  toFromProto := FromProto.ofFields dec
  msg_tags_pos := htags
  fromProtoMsg_toProtoMsg := hrt
  fromProtoVal_toProtoVal a := Proto.decodeEmbedded_encodeEmbedded _ _ a (htags a) (hrt a)

@[reducible] def ToProto.ofEquiv {α β : Type} [ToProto β] (toB : α → β) : ToProto α where
  toProtoMsg a := ToProto.toProtoMsg (toB a)
  toProtoVal a := ToProto.toProtoVal (toB a)

@[reducible] def FromProto.ofEquiv {α β : Type} [FromProto β] (ofB : β → α) : FromProto α where
  fromProtoMsg fs := (FromProto.fromProtoMsg (α := β) fs).map ofB
  fromProtoVal w  := (FromProto.fromProtoVal (α := β) w).map ofB

@[reducible] def LawfulProto.ofEquiv {α β : Type} [LawfulProto β]
    (toB : α → β) (ofB : β → α) (hinv : ∀ a : α, ofB (toB a) = a) : LawfulProto α where
  toToProto := ToProto.ofEquiv toB
  toFromProto := FromProto.ofEquiv ofB
  msg_tags_pos a := LawfulProto.msg_tags_pos (toB a)
  fromProtoMsg_toProtoMsg a := by
    change (FromProto.fromProtoMsg (ToProto.toProtoMsg (toB a)) : Except String β).map ofB = .ok a
    rw [LawfulProto.fromProtoMsg_toProtoMsg (toB a)]; exact congrArg Except.ok (hinv a)
  fromProtoVal_toProtoVal a := by
    change (FromProto.fromProtoVal (ToProto.toProtoVal (toB a)) : Except String β).map ofB = .ok a
    rw [LawfulProto.fromProtoVal_toProtoVal (toB a)]; exact congrArg Except.ok (hinv a)

@[reducible] def FromProto.ofRetract {α β : Type} [FromProto β] (ofB : β → Except String α) : FromProto α where
  fromProtoMsg fs := (FromProto.fromProtoMsg (α := β) fs).bind ofB
  fromProtoVal w  := (FromProto.fromProtoVal (α := β) w).bind ofB

@[reducible] def LawfulProto.ofRetract {α β : Type} [LawfulProto β]
    (toB : α → β) (ofB : β → Except String α) (hinv : ∀ a : α, ofB (toB a) = .ok a) : LawfulProto α where
  toToProto := ToProto.ofEquiv toB
  toFromProto := FromProto.ofRetract ofB
  msg_tags_pos a := LawfulProto.msg_tags_pos (toB a)
  fromProtoMsg_toProtoMsg a := by
    change (FromProto.fromProtoMsg (ToProto.toProtoMsg (toB a)) : Except String β).bind ofB = .ok a
    rw [LawfulProto.fromProtoMsg_toProtoMsg (toB a)]; exact hinv a
  fromProtoVal_toProtoVal a := by
    change (FromProto.fromProtoVal (ToProto.toProtoVal (toB a)) : Except String β).bind ofB = .ok a
    rw [LawfulProto.fromProtoVal_toProtoVal (toB a)]; exact hinv a

/-! ## Composite & Container `LawfulProto` Instances (`Date`, `Option`, `Except`, `Prod`, `List`, `Array`) -/

def Date.toProtoFields (d : Date) : List (Nat × WireVal) :=
  [(1, ToProto.toProtoVal d.year), (2, ToProto.toProtoVal d.month), (3, ToProto.toProtoVal d.day)]

def Date.fromProtoFields (fs : List (Nat × WireVal)) : Except String Date := do
  let year  ← FromProtoField.decodeProtoField 1 fs
  let month ← FromProtoField.decodeProtoField 2 fs
  let day   ← FromProtoField.decodeProtoField 3 fs
  match Date.mk? year month day with
  | some d => .ok d
  | none   => .error "protobuf: invalid calendar Date"

macro "qed_proto_fields% " "[" vs:ident,* "]"
    "(" ty:term "," enc:term "," dec:term "," htags:term "," hinv:term ")" : command => do
  let ids := vs.getElems
  `(instance $[{$ids:ident : Type}]* $[[ToProto $ids]]* : ToProto $ty := .ofFields $enc
    instance $[{$ids:ident : Type}]* $[[FromProto $ids]]* : FromProto $ty := .ofFields $dec
    instance $[{$ids:ident : Type}]* $[[LawfulProto $ids]]* : LawfulProto $ty := .ofFields $enc $dec $htags $hinv)

macro "qed_equiv_codec% " kind:ident "[" vs:ident,* "]"
    "(" ty:term "," toB:term "," ofB:term "," hinv:term ")" : command => do
  let ids := vs.getElems
  if kind.getId == `json then
    `(instance $[{$ids:ident : Type}]* $[[ToJson $ids]]* : ToJson $ty := .ofEquiv $toB
      instance $[{$ids:ident : Type}]* $[[FromJson $ids]]* : FromJson $ty := .ofEquiv $ofB
      instance $[{$ids:ident : Type}]* $[[LawfulJson $ids]]* : LawfulJson $ty := .ofEquiv $toB $ofB $hinv
      instance $[{$ids:ident : Type}]* $[[ToJson $ids]]* : NonNullJson $ty := ⟨nofun⟩)
  else if kind.getId == `jsonLow then
    `(instance (priority := low) $[{$ids:ident : Type}]* $[[ToJson $ids]]* : ToJson $ty := .ofEquiv $toB
      instance (priority := low) $[{$ids:ident : Type}]* $[[FromJson $ids]]* : FromJson $ty := .ofEquiv $ofB
      instance (priority := low) $[{$ids:ident : Type}]* $[[LawfulJson $ids]]* :
          LawfulJson $ty := .ofEquiv $toB $ofB $hinv
      instance (priority := low) $[{$ids:ident : Type}]* $[[ToJson $ids]]* : NonNullJson $ty := ⟨nofun⟩)
  else
    `(instance $[{$ids:ident : Type}]* $[[ToProto $ids]]* : ToProto $ty := .ofEquiv $toB
      instance $[{$ids:ident : Type}]* $[[FromProto $ids]]* : FromProto $ty := .ofEquiv $ofB
      instance $[{$ids:ident : Type}]* $[[LawfulProto $ids]]* : LawfulProto $ty := .ofEquiv $toB $ofB $hinv)

qed_proto_fields% [] (Date, Date.toProtoFields, Date.fromProtoFields,
  by intro d kw h; simp only [Date.toProtoFields, List.mem_cons, List.not_mem_nil, or_false] at h
     rcases h with rfl | rfl | rfl <;> simp,
  by rintro ⟨y, m, day, hok⟩; unfold Date.fromProtoFields Date.toProtoFields
     simp [FromProtoField.decodeProtoField, lookupField, Date.mk?, hok, bind, Except.bind])

qed_proto_fields% [α] (Option α, ToProtoField.encodeProtoField 1, FromProtoField.decodeProtoField 1,
  fun opt kw h => by rw [LawfulProtoField.encodeProtoField_tag 1 opt kw h]; simp,
  fun opt => by simpa using LawfulProtoField.decodeProtoField_hit_raw 1 opt [] (by simp))

private def encodeExceptFields {ε α : Type} [ToProto ε] [ToProto α] : Except ε α → List (Nat × WireVal)
  | .ok a    => [(1, ToProto.toProtoVal a)]
  | .error e => [(2, ToProto.toProtoVal e)]

private def decodeExceptFields {ε α : Type} [FromProto ε] [FromProto α]
    (fs : List (Nat × WireVal)) : Except String (Except ε α) :=
  match lookupField 1 fs with
  | some w => (FromProto.fromProtoVal (α := α) w).map Except.ok
  | none   =>
      match lookupField 2 fs with
      | some w => (FromProto.fromProtoVal (α := ε) w).map Except.error
      | none   => .error "protobuf: missing Except branch"

qed_proto_fields% [ε, α] (Except ε α, encodeExceptFields, decodeExceptFields,
  by intro r kw h; cases r <;> (simp only [encodeExceptFields, List.mem_singleton] at h; rw [h]; simp),
  by intro r; cases r <;> simp [encodeExceptFields, decodeExceptFields, lookupField, Except.map])

private def encodeProdFields {α β : Type} [ToProto α] [ToProto β] (p : α × β) : List (Nat × WireVal) :=
  [(1, ToProto.toProtoVal p.1), (2, ToProto.toProtoVal p.2)]

private def decodeProdFields {α β : Type} [FromProto α] [FromProto β]
    (fs : List (Nat × WireVal)) : Except String (α × β) := do
  return (← decodeFieldVal 1 fs "protobuf: missing tuple field 1",
          ← decodeFieldVal 2 fs "protobuf: missing tuple field 2")

qed_proto_fields% [α, β] (α × β, encodeProdFields, decodeProdFields,
  by intro p kw h; simp only [encodeProdFields, List.mem_cons, List.not_mem_nil, or_false] at h
     rcases h with rfl | rfl <;> simp,
  by rintro ⟨a, b⟩
     simp [encodeProdFields, decodeProdFields, decodeFieldVal, lookupField, bind, Except.bind, pure, Except.pure])

private def encodeRepeatedField1 {α : Type} [ToProto α] (xs : List α) : List (Nat × WireVal) :=
  xs.map fun x => (1, ToProto.toProtoVal x)

private def decodeRepeatedField1 {α : Type} [FromProto α]
    (fs : List (Nat × WireVal)) : Except String (List α) :=
  (lookupRepeated 1 fs).mapM FromProto.fromProtoVal

private theorem lookupRepeated_map_one {α : Type} [ToProto α] :
    ∀ (xs : List α), lookupRepeated 1 (encodeRepeatedField1 xs) = xs.map ToProto.toProtoVal
  | [] => rfl
  | x :: rest => congrArg (ToProto.toProtoVal x :: ·) (lookupRepeated_map_one rest)

qed_proto_fields% [α] (List α, encodeRepeatedField1, decodeRepeatedField1,
  by intro xs kw h; rcases List.mem_map.1 h with ⟨_, _, rfl⟩; simp,
  by intro xs; unfold decodeRepeatedField1
     rw [lookupRepeated_map_one,
       list_mapM_map_ok ToProto.toProtoVal FromProto.fromProtoVal LawfulProto.fromProtoVal_toProtoVal])

qed_equiv_codec% proto [α] (Array α, Array.toList, List.toArray, fun xs => by cases xs; rfl)

end Qed
