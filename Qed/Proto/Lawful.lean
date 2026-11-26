import Qed.Proto.Basic
import Qed.Proto.Proofs
import Qed.Json.Lawful
import Qed.Date

namespace Qed
open Qed.Proto

/-! ## JSON Codec for `Bytes` (`ByteArray`) via Verified Hex Bijection -/

instance : ToJson ByteArray where toJson b := .str (encodeHex b)
instance : FromJson ByteArray where fromJson | .str s => decodeHex s | _ => .error "expected hex-encoded byte string"
instance : LawfulJson ByteArray where fromJson_toJson := decodeHex_encodeHex
instance : NonNullJson ByteArray := ⟨nofun⟩

/-! ## Binary Protocol Buffers Typeclasses (`ToProto`, `FromProto`, `LawfulProto`) -/

class ToProto (α : Type) where
  toProtoVal : α → WireVal
  toProtoMsg : α → List (Nat × WireVal) := fun a => [(1, toProtoVal a)]

class FromProto (α : Type) where
  fromProtoVal : WireVal → Except String α
  fromProtoMsg : List (Nat × WireVal) → Except String α := fun fs =>
    match lookupField 1 fs with | some w => fromProtoVal w | none => .error "protobuf: missing value field 1"

class LawfulProto (α : Type) extends ToProto α, FromProto α where
  msg_tags_pos : ∀ (a : α) (kw : Nat × WireVal), kw ∈ toProtoMsg a → 0 < kw.1
  fromProtoVal_toProtoVal : ∀ a : α, fromProtoVal (toProtoVal a) = .ok a
  fromProtoMsg_toProtoMsg : ∀ a : α, fromProtoMsg (toProtoMsg a) = .ok a

@[simp] theorem fromProtoVal_toProtoVal_simp {α : Type} [LawfulProto α] (a : α) :
    FromProto.fromProtoVal (ToProto.toProtoVal a) = .ok a := LawfulProto.fromProtoVal_toProtoVal a
@[simp] theorem fromProtoMsg_toProtoMsg_simp {α : Type} [LawfulProto α] (a : α) :
    FromProto.fromProtoMsg (ToProto.toProtoMsg a) = .ok a := LawfulProto.fromProtoMsg_toProtoMsg a

@[reducible] def LawfulProto.ofScalar {α : Type} [t : ToProto α] [f : FromProto α]
    (hval : ∀ a : α, f.fromProtoVal (t.toProtoVal a) = .ok a)
    (hmsg : ∀ a : α, t.toProtoMsg a = [(1, t.toProtoVal a)] := by intro _; rfl)
    (hfmsg : ∀ fs, f.fromProtoMsg fs = (match lookupField 1 fs with | some w => f.fromProtoVal w | none => .error "protobuf: missing value field 1") := by intro _; rfl) : LawfulProto α where
  msg_tags_pos a kw h := by rw [hmsg] at h; rw [List.mem_singleton.1 h]; simp
  fromProtoVal_toProtoVal := hval
  fromProtoMsg_toProtoMsg a := by rw [hmsg, hfmsg]; simp [lookupField, hval]

namespace Proto
def encode {α : Type} [ToProto α] (a : α) : ByteArray := encodeFieldsSpec (ToProto.toProtoMsg a)
def decode {α : Type} [FromProto α] (buf : ByteArray) : Except String α := (decodeFieldsSpec buf).bind FromProto.fromProtoMsg
@[simp] theorem decode_encode {α : Type} [LawfulProto α] (a : α) : Proto.decode (Proto.encode a) = .ok a := by
  unfold Proto.decode Proto.encode; rw [decodeFieldsSpec_encodeFieldsSpec _ (LawfulProto.msg_tags_pos a)]; exact LawfulProto.fromProtoMsg_toProtoMsg a
def decodeFieldVal {α : Type} [FromProto α] (k : Nat) (fs : List (Nat × WireVal)) (err : String := s!"protobuf: missing field {k}") : Except String α :=
  (lookupField k fs).elim (.error err) FromProto.fromProtoVal
end Proto

/-! ## Primitive & Scalar `LawfulProto` Instances -/

instance : ToProto Unit where toProtoVal _ := .bytes ByteArray.empty; toProtoMsg _ := []
instance : FromProto Unit where fromProtoVal | .bytes _ => .ok () | _ => .error "protobuf: expected unit bytes"; fromProtoMsg _ := .ok ()
instance : LawfulProto Unit where msg_tags_pos _ _ h := nomatch h; fromProtoVal_toProtoVal _ := rfl; fromProtoMsg_toProtoMsg _ := rfl

local macro "defScalarProto " ty:ident ctor:ident enc:term "," dec:term "," err:str "," pf:term : command =>
  `(instance : ToProto $ty where toProtoVal x := $ctor ($enc x)
    instance : FromProto $ty where fromProtoVal | $ctor v => $dec v | _ => .error $err
    instance : LawfulProto $ty := .ofScalar $pf)

defScalarProto Nat WireVal.varint id, Except.ok, "protobuf: expected varint for Nat", (fun _ => rfl)
defScalarProto UInt32 WireVal.fixed32 id, Except.ok, "protobuf: expected fixed32 for UInt32", (fun _ => rfl)
defScalarProto UInt64 WireVal.fixed64 id, Except.ok, "protobuf: expected fixed64 for UInt64", (fun _ => rfl)
defScalarProto ByteArray WireVal.bytes id, Except.ok, "protobuf: expected length-delimited bytes", (fun _ => rfl)
defScalarProto Bool WireVal.varint (fun b => if b then 1 else 0),
  (fun | 0 => .ok false | 1 => .ok true | n => .error s!"protobuf: invalid bool varint {n}"),
  "protobuf: expected varint for Bool", (by intro b; cases b <;> rfl)
defScalarProto Int WireVal.varint zigzagEncode, (fun n => .ok (zigzagDecode n)),
  "protobuf: expected ZigZag varint for Int", (fun i => by simp [ToProto.toProtoVal, FromProto.fromProtoVal, zigzagDecode_zigzagEncode])
defScalarProto UInt8 WireVal.varint UInt8.toNat,
  (fun n => if n < 256 then .ok (UInt8.ofNat n) else .error s!"protobuf: UInt8 out of range ({n})"),
  "protobuf: expected varint for UInt8", (fun b => by simp [ToProto.toProtoVal, FromProto.fromProtoVal, b.toNat_lt, UInt8.ofNat_toNat])
defScalarProto String WireVal.bytes String.toUTF8,
  (fun b => (String.fromUTF8? b).elim (.error "protobuf: invalid UTF-8 string") .ok),
  "protobuf: expected length-delimited UTF-8 string", (fun ⟨_, h⟩ => by simp [ToProto.toProtoVal, FromProto.fromProtoVal, String.fromUTF8?, String.toUTF8, h, String.fromUTF8])

instance : ToProto Float where toProtoVal f := .fixed64 f.toBits
instance : FromProto Float where fromProtoVal | .fixed64 bits => .ok (Float.ofBits bits) | _ => .error "protobuf: expected fixed64 for Float"

/-! ## Structured Message Field Helpers (`ToProtoField`, `FromProtoField`, `LawfulProtoField`) -/

class ToProtoField (α : Type) where encodeProtoField : Nat → α → List (Nat × WireVal)
class FromProtoField (α : Type) where decodeProtoField : Nat → List (Nat × WireVal) → Except String α
class LawfulProtoField (α : Type) extends ToProtoField α, FromProtoField α where
  encodeProtoField_tag : ∀ (k : Nat) (a : α) (kw : Nat × WireVal), kw ∈ encodeProtoField k a → kw.1 = k
  decodeProtoField_skip_prefix : ∀ (k : Nat) (pre rest : List (Nat × WireVal)), (∀ kw ∈ pre, kw.1 ≠ k) → decodeProtoField k (pre ++ rest) = decodeProtoField k rest
  decodeProtoField_hit_raw : ∀ (k : Nat) (a : α) (rest : List (Nat × WireVal)), (∀ kw ∈ rest, kw.1 ≠ k) → decodeProtoField k (encodeProtoField k a ++ rest) = .ok a

instance (priority := low) {α : Type} [ToProto α] : ToProtoField α where encodeProtoField k a := [(k, ToProto.toProtoVal a)]
instance (priority := low) {α : Type} [FromProto α] : FromProtoField α where
  decodeProtoField k fs := (lookupField k fs).elim (.error s!"protobuf: missing field {k}") FromProto.fromProtoVal
instance (priority := low) {α : Type} [LawfulProto α] : LawfulProtoField α where
  encodeProtoField_tag _ _ _ h := by rw [List.mem_singleton.1 h]
  decodeProtoField_skip_prefix k pre rest hne := by simp [FromProtoField.decodeProtoField, skipUnknown_preserves_lookup_prefix k pre rest hne]
  decodeProtoField_hit_raw _ _ _ _ := by simp [ToProtoField.encodeProtoField, FromProtoField.decodeProtoField, lookupField]

instance {α : Type} [ToProto α] : ToProtoField (Option α) where encodeProtoField k | none => [] | some a => [(k, ToProto.toProtoVal a)]
instance {α : Type} [FromProto α] : FromProtoField (Option α) where
  decodeProtoField k fs := (lookupField k fs).elim (.ok none) fun w => (FromProto.fromProtoVal w).map some
instance {α : Type} [LawfulProto α] : LawfulProtoField (Option α) where
  encodeProtoField_tag _ opt _ h := by cases opt with | none => cases h | some _ => rw [List.mem_singleton.1 h]
  decodeProtoField_skip_prefix k pre rest hne := by simp [FromProtoField.decodeProtoField, skipUnknown_preserves_lookup_prefix k pre rest hne]
  decodeProtoField_hit_raw k opt rest hne := by
    cases opt with
    | none => simp [ToProtoField.encodeProtoField, FromProtoField.decodeProtoField, show lookupField k rest = none by simpa [lookupField] using skipUnknown_preserves_lookup_prefix k rest [] hne]
    | some _ => simp [ToProtoField.encodeProtoField, FromProtoField.decodeProtoField, lookupField, Except.map]

namespace Proto
def AllTagsGt (k : Nat) (fs : List (Nat × WireVal)) : Prop := ∀ kw ∈ fs, k < kw.1
@[simp] theorem allTagsGt_nil (k : Nat) : AllTagsGt k [] := fun _ h => nomatch h
theorem allTagsGt_encodeAppend {α : Type} [LawfulProtoField α] {k j : Nat} (hj : k < j) (a : α) {rest : List (Nat × WireVal)} (hr : AllTagsGt k rest) :
    AllTagsGt k (ToProtoField.encodeProtoField j a ++ rest) := fun kw hm =>
  (List.mem_append.1 hm).elim (fun h1 => by rw [LawfulProtoField.encodeProtoField_tag j a kw h1]; exact hj) (hr kw)
theorem msg_tags_pos_encodeAppend {α : Type} [LawfulProtoField α] {k : Nat} (hk : 0 < k) (a : α) {rest : List (Nat × WireVal)} (hr : ∀ kw ∈ rest, 0 < kw.1) :
    ∀ kw ∈ ToProtoField.encodeProtoField k a ++ rest, 0 < kw.1 := fun kw hm =>
  (List.mem_append.1 hm).elim (fun h1 => by rw [LawfulProtoField.encodeProtoField_tag k a kw h1]; exact hk) (hr kw)
theorem decodeProtoField_skip {α β : Type} [LawfulProtoField α] [LawfulProtoField β] {k j : Nat} (hne : j ≠ k) (b : β) (rest : List (Nat × WireVal)) :
    FromProtoField.decodeProtoField (α := α) k (ToProtoField.encodeProtoField j b ++ rest) = FromProtoField.decodeProtoField (α := α) k rest :=
  LawfulProtoField.decodeProtoField_skip_prefix k _ rest fun kw hm => by rw [LawfulProtoField.encodeProtoField_tag j b kw hm]; exact hne
theorem decodeProtoField_hit {α : Type} [LawfulProtoField α] (k : Nat) (a : α) (rest : List (Nat × WireVal)) (hgt : AllTagsGt k rest) :
    FromProtoField.decodeProtoField k (ToProtoField.encodeProtoField k a ++ rest) = .ok a :=
  LawfulProtoField.decodeProtoField_hit_raw k a rest fun kw hm => Nat.ne_of_gt (hgt kw hm)
end Proto

@[reducible] def ToProto.ofFields {α : Type} (enc : α → List (Nat × WireVal)) : ToProto α :=
  ⟨fun a => .bytes (encodeFieldsSpec (enc a)), enc⟩
@[reducible] def FromProto.ofFields {α : Type} (dec : List (Nat × WireVal) → Except String α) : FromProto α :=
  ⟨fun | .bytes b => (decodeFieldsSpec b).bind dec | _ => .error "protobuf: expected embedded message bytes", dec⟩
@[reducible] def LawfulProto.ofFields {α : Type} (enc : α → List (Nat × WireVal)) (dec : List (Nat × WireVal) → Except String α)
    (htags : ∀ (a : α) (kw : Nat × WireVal), kw ∈ enc a → 0 < kw.1) (hrt : ∀ a : α, dec (enc a) = .ok a) : LawfulProto α where
  toToProto := .ofFields enc; toFromProto := .ofFields dec; msg_tags_pos := htags; fromProtoMsg_toProtoMsg := hrt
  fromProtoVal_toProtoVal a := by
    change (decodeFieldsSpec (encodeFieldsSpec (enc a))).bind dec = .ok a
    rw [decodeFieldsSpec_encodeFieldsSpec _ (htags a)]; exact hrt a

@[reducible] def ToProto.ofEquiv {α β : Type} [ToProto β] (toB : α → β) : ToProto α :=
  ⟨fun a => ToProto.toProtoVal (toB a), fun a => ToProto.toProtoMsg (toB a)⟩
@[reducible] def FromProto.ofEquiv {α β : Type} [FromProto β] (ofB : β → α) : FromProto α :=
  ⟨fun w => (FromProto.fromProtoVal (α := β) w).map ofB, fun fs => (FromProto.fromProtoMsg (α := β) fs).map ofB⟩
@[reducible] def FromProto.ofRetract {α β : Type} [FromProto β] (ofB : β → Except String α) : FromProto α :=
  ⟨fun w => (FromProto.fromProtoVal (α := β) w).bind ofB, fun fs => (FromProto.fromProtoMsg (α := β) fs).bind ofB⟩

@[reducible] def LawfulProto.ofEquiv {α β : Type} [LawfulProto β] (toB : α → β) (ofB : β → α) (hinv : ∀ a : α, ofB (toB a) = a) : LawfulProto α where
  toToProto := .ofEquiv toB; toFromProto := .ofEquiv ofB; msg_tags_pos a := LawfulProto.msg_tags_pos (toB a)
  fromProtoMsg_toProtoMsg a := (congrArg (Except.map ofB) (LawfulProto.fromProtoMsg_toProtoMsg (toB a))).trans (congrArg Except.ok (hinv a))
  fromProtoVal_toProtoVal a := (congrArg (Except.map ofB) (LawfulProto.fromProtoVal_toProtoVal (toB a))).trans (congrArg Except.ok (hinv a))

@[reducible] def LawfulProto.ofRetract {α β : Type} [LawfulProto β] (toB : α → β) (ofB : β → Except String α) (hinv : ∀ a : α, ofB (toB a) = .ok a) : LawfulProto α where
  toToProto := .ofEquiv toB; toFromProto := .ofRetract ofB; msg_tags_pos a := LawfulProto.msg_tags_pos (toB a)
  fromProtoMsg_toProtoMsg a := (congrArg (·.bind ofB) (LawfulProto.fromProtoMsg_toProtoMsg (toB a))).trans (hinv a)
  fromProtoVal_toProtoVal a := (congrArg (·.bind ofB) (LawfulProto.fromProtoVal_toProtoVal (toB a))).trans (hinv a)

/-! ## Composite & Container `LawfulProto` Instances (`Date`, `Option`, `Except`, `Prod`, `List`, `Array`) -/

macro "qed_proto_fields% " "[" vs:ident,* "]" "(" ty:term "," enc:term "," dec:term "," htags:term "," hinv:term ")" : command => do
  let ids := vs.getElems
  `(instance $[{$ids:ident : Type}]* $[[ToProto $ids]]* : ToProto $ty := .ofFields $enc
    instance $[{$ids:ident : Type}]* $[[FromProto $ids]]* : FromProto $ty := .ofFields $dec
    instance $[{$ids:ident : Type}]* $[[LawfulProto $ids]]* : LawfulProto $ty := .ofFields $enc $dec $htags $hinv)

macro "qed_equiv_codec% " kind:ident "[" vs:ident,* "]" "(" ty:term "," toB:term "," ofB:term "," hinv:term ")" : command => do
  let ids := vs.getElems
  if kind.getId == `json || kind.getId == `jsonLow then
    let p ← if kind.getId == `jsonLow then `(prio| low) else `(prio| default)
    `(instance (priority := $p) $[{$ids:ident : Type}]* $[[ToJson $ids]]* : ToJson $ty := .ofEquiv $toB
      instance (priority := $p) $[{$ids:ident : Type}]* $[[FromJson $ids]]* : FromJson $ty := .ofEquiv $ofB
      instance (priority := $p) $[{$ids:ident : Type}]* $[[LawfulJson $ids]]* : LawfulJson $ty := .ofEquiv $toB $ofB $hinv
      instance (priority := $p) $[{$ids:ident : Type}]* $[[ToJson $ids]]* : NonNullJson $ty := ⟨nofun⟩)
  else
    `(instance $[{$ids:ident : Type}]* $[[ToProto $ids]]* : ToProto $ty := .ofEquiv $toB
      instance $[{$ids:ident : Type}]* $[[FromProto $ids]]* : FromProto $ty := .ofEquiv $ofB
      instance $[{$ids:ident : Type}]* $[[LawfulProto $ids]]* : LawfulProto $ty := .ofEquiv $toB $ofB $hinv)

def Date.toProtoFields (d : Date) : List (Nat × WireVal) := [(1, ToProto.toProtoVal d.year), (2, ToProto.toProtoVal d.month), (3, ToProto.toProtoVal d.day)]
def Date.fromProtoFields (fs : List (Nat × WireVal)) : Except String Date := do
  (Date.mk? (← FromProtoField.decodeProtoField 1 fs) (← FromProtoField.decodeProtoField 2 fs) (← FromProtoField.decodeProtoField 3 fs)).elim (.error "protobuf: invalid calendar Date") .ok
qed_proto_fields% [] (Date, Date.toProtoFields, Date.fromProtoFields,
  by intro _ _ h; simp only [Date.toProtoFields, List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> exact Nat.zero_lt_succ _,
  by rintro ⟨_, _, _, hok⟩; simp [Date.fromProtoFields, Date.toProtoFields, FromProtoField.decodeProtoField, lookupField, Date.mk?, hok, bind, Except.bind])

qed_proto_fields% [α] (Option α, ToProtoField.encodeProtoField 1, FromProtoField.decodeProtoField 1,
  fun opt kw h => by rw [LawfulProtoField.encodeProtoField_tag 1 opt kw h]; exact Nat.zero_lt_succ _,
  fun opt => by simpa using LawfulProtoField.decodeProtoField_hit_raw 1 opt [] (by simp))

private def encodeExceptFields [ToProto ε] [ToProto α] : Except ε α → List (Nat × WireVal)
  | .ok a => [(1, ToProto.toProtoVal a)] | .error e => [(2, ToProto.toProtoVal e)]
private def decodeExceptFields [FromProto ε] [FromProto α] (fs : List (Nat × WireVal)) : Except String (Except ε α) :=
  match lookupField 1 fs, lookupField 2 fs with
  | some w, _ => (FromProto.fromProtoVal (α := α) w).map .ok | none, some w => (FromProto.fromProtoVal (α := ε) w).map .error | none, none => .error "protobuf: missing Except branch"
qed_proto_fields% [ε, α] (Except ε α, encodeExceptFields, decodeExceptFields,
  by intro r _ h; cases r <;> (rw [List.mem_singleton.1 h]; exact Nat.zero_lt_succ _),
  by intro r; cases r <;> simp [encodeExceptFields, decodeExceptFields, lookupField, Except.map])

private def encodeProdFields [ToProto α] [ToProto β] (p : α × β) : List (Nat × WireVal) := [(1, ToProto.toProtoVal p.1), (2, ToProto.toProtoVal p.2)]
private def decodeProdFields [FromProto α] [FromProto β] (fs : List (Nat × WireVal)) : Except String (α × β) :=
  (decodeFieldVal 1 fs "protobuf: missing tuple field 1").bind fun a => (decodeFieldVal 2 fs "protobuf: missing tuple field 2").map (a, ·)
qed_proto_fields% [α, β] (α × β, encodeProdFields, decodeProdFields,
  by intro _ _ h; simp only [encodeProdFields, List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> exact Nat.zero_lt_succ _,
  by rintro ⟨_, _⟩; simp [encodeProdFields, decodeProdFields, decodeFieldVal, lookupField, Except.bind, Except.map])

private def encodeRepeatedField1 [ToProto α] (xs : List α) : List (Nat × WireVal) := xs.map fun x => (1, ToProto.toProtoVal x)
private def decodeRepeatedField1 [FromProto α] (fs : List (Nat × WireVal)) : Except String (List α) := (lookupRepeated 1 fs).mapM FromProto.fromProtoVal
private theorem lookupRepeated_map_one [ToProto α] : ∀ xs : List α, lookupRepeated 1 (encodeRepeatedField1 xs) = xs.map ToProto.toProtoVal
  | [] => rfl | x :: rest => congrArg (ToProto.toProtoVal x :: ·) (lookupRepeated_map_one rest)
qed_proto_fields% [α] (List α, encodeRepeatedField1, decodeRepeatedField1,
  by intro _ _ h; rcases List.mem_map.1 h with ⟨_, _, rfl⟩; exact Nat.zero_lt_succ _,
  fun xs => by rw [decodeRepeatedField1, lookupRepeated_map_one]; exact list_mapM_map_ok _ _ LawfulProto.fromProtoVal_toProtoVal xs)

qed_equiv_codec% proto [α] (Array α, Array.toList, List.toArray, fun ⟨_⟩ => rfl)

/-! ## Verified JSON & Protobuf Codecs for `Qed.Url` (Re-verifies `isSafeUrl` on Untrusted Wire Bytes) -/

instance : ToJson Url where toJson u := .str u.raw
instance : FromJson Url where
  fromJson
    | .str s => (Url.parse? s).elim (.error s!"unsafe URL `{s}`") .ok
    | _ => .error "expected URL string"
instance : LawfulJson Url where
  fromJson_toJson u := by simp [ToJson.toJson, FromJson.fromJson, Url.parse?, u.safe]
instance : NonNullJson Url := ⟨nofun⟩

instance : ToProto Url where toProtoVal u := ToProto.toProtoVal u.raw
instance : FromProto Url where
  fromProtoVal w := (FromProto.fromProtoVal (α := String) w).bind fun s =>
    (Url.parse? s).elim (.error s!"protobuf: unsafe URL `{s}`") .ok
instance : LawfulProto Url := .ofScalar fun ⟨⟨_, hs⟩, hsafe⟩ => by
  simp [ToProto.toProtoVal, FromProto.fromProtoVal, String.fromUTF8?, String.toUTF8, hs, String.fromUTF8, Except.bind, Url.parse?, hsafe]

end Qed
