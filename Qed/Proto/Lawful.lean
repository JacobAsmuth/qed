import Qed.Proto.Basic
import Qed.Proto.Proofs
import Qed.Json.Lawful
import Qed.Date

namespace Qed
open Qed.Proto

/-! ## JSON Codec for `Bytes` (`ByteArray`) & Binary Protobuf Typeclasses -/

instance : ToJson ByteArray := .ofEquiv encodeHex
instance : FromJson ByteArray := .ofRetract decodeHex
instance : LawfulJson ByteArray := .ofRetract encodeHex decodeHex decodeHex_encodeHex
instance : NonNullJson ByteArray := ⟨nofun⟩

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

@[simp] theorem fromProtoVal_toProtoVal_simp {α : Type} [LawfulProto α] (a : α) : FromProto.fromProtoVal (ToProto.toProtoVal a) = .ok a := LawfulProto.fromProtoVal_toProtoVal a
@[simp] theorem fromProtoMsg_toProtoMsg_simp {α : Type} [LawfulProto α] (a : α) : FromProto.fromProtoMsg (ToProto.toProtoMsg a) = .ok a := LawfulProto.fromProtoMsg_toProtoMsg a

@[reducible] def LawfulProto.ofScalar {α : Type} [t : ToProto α] [f : FromProto α] (hval : ∀ a : α, f.fromProtoVal (t.toProtoVal a) = .ok a)
    (hmsg : ∀ a : α, t.toProtoMsg a = [(1, t.toProtoVal a)] := by intro _; rfl)
    (hfmsg : ∀ fs, f.fromProtoMsg fs = (match lookupField 1 fs with | some w => f.fromProtoVal w | none => .error "protobuf: missing value field 1") := by intro _; rfl) : LawfulProto α where
  msg_tags_pos a kw h := by rw [hmsg] at h; rw [List.mem_singleton.1 h]; simp
  fromProtoVal_toProtoVal := hval
  fromProtoMsg_toProtoMsg a := by rw [hmsg, hfmsg]; simp [lookupField, hval]

namespace Proto
@[noinline, nospecialize] def encode {α : Type} [ToProto α] (a : α) : ByteArray := encodeFieldsSpec (ToProto.toProtoMsg a)
@[noinline, nospecialize] def decode {α : Type} [FromProto α] (buf : ByteArray) : Except String α := (decodeFieldsSpec buf).bind FromProto.fromProtoMsg
@[simp] theorem decode_encode {α : Type} [LawfulProto α] (a : α) : Proto.decode (Proto.encode a) = .ok a := by
  unfold Proto.decode Proto.encode; rw [decodeFieldsSpec_encodeFieldsSpec _ (LawfulProto.msg_tags_pos a)]; exact LawfulProto.fromProtoMsg_toProtoMsg a
@[noinline, nospecialize] def decodeFieldVal {α : Type} [FromProto α] (k : Nat) (fs : List (Nat × WireVal)) (err : String := s!"protobuf: missing field {k}") : Except String α :=
  (lookupField k fs).elim (.error err) FromProto.fromProtoVal
end Proto

/-! ## Primitive & Scalar `LawfulProto` Instances -/

instance : ToProto Unit where toProtoVal _ := .bytes ByteArray.empty; toProtoMsg _ := []
instance : FromProto Unit where fromProtoVal | .bytes _ => .ok () | _ => .error "protobuf: expected unit bytes"; fromProtoMsg _ := .ok ()
instance : LawfulProto Unit where msg_tags_pos _ _ h := nomatch h; fromProtoVal_toProtoVal _ := rfl; fromProtoMsg_toProtoMsg _ := rfl

instance : ToProto Nat where toProtoVal := .varint
instance : FromProto Nat where fromProtoVal | .varint v => .ok v | _ => .error "protobuf: expected varint for Nat"
instance : LawfulProto Nat := .ofScalar fun _ => rfl
instance : ToProto UInt32 where toProtoVal := .fixed32
instance : FromProto UInt32 where fromProtoVal | .fixed32 v => .ok v | _ => .error "protobuf: expected fixed32 for UInt32"
instance : LawfulProto UInt32 := .ofScalar fun _ => rfl
instance : ToProto UInt64 where toProtoVal := .fixed64
instance : FromProto UInt64 where fromProtoVal | .fixed64 v => .ok v | _ => .error "protobuf: expected fixed64 for UInt64"
instance : LawfulProto UInt64 := .ofScalar fun _ => rfl
instance : ToProto ByteArray where toProtoVal := .bytes
instance : FromProto ByteArray where fromProtoVal | .bytes v => .ok v | _ => .error "protobuf: expected length-delimited bytes"
instance : LawfulProto ByteArray := .ofScalar fun _ => rfl
instance : ToProto Bool where toProtoVal b := .varint (if b then 1 else 0)
instance : FromProto Bool where fromProtoVal | .varint 0 => .ok false | .varint 1 => .ok true | .varint n => .error s!"protobuf: invalid bool varint {n}" | _ => .error "protobuf: expected varint for Bool"
instance : LawfulProto Bool := .ofScalar fun | false | true => rfl
instance : ToProto Int where toProtoVal i := .varint (zigzagEncode i)
instance : FromProto Int where fromProtoVal | .varint n => .ok (zigzagDecode n) | _ => .error "protobuf: expected ZigZag varint for Int"
instance : LawfulProto Int := .ofScalar fun i => by simp [ToProto.toProtoVal, FromProto.fromProtoVal, zigzagDecode_zigzagEncode]
instance : ToProto UInt8 where toProtoVal b := .varint b.toNat
instance : FromProto UInt8 where fromProtoVal | .varint n => if n < 256 then .ok (UInt8.ofNat n) else .error s!"protobuf: UInt8 out of range ({n})" | _ => .error "protobuf: expected varint for UInt8"
instance : LawfulProto UInt8 := .ofScalar fun b => by simp [ToProto.toProtoVal, FromProto.fromProtoVal, b.toNat_lt, UInt8.ofNat_toNat]
instance : ToProto String where toProtoVal s := .bytes s.toUTF8
instance : FromProto String where fromProtoVal | .bytes b => (String.fromUTF8? b).elim (.error "protobuf: invalid UTF-8 string") .ok | _ => .error "protobuf: expected length-delimited UTF-8 string"
instance : LawfulProto String := .ofScalar fun ⟨_, h⟩ => by simp [ToProto.toProtoVal, FromProto.fromProtoVal, String.fromUTF8?, String.toUTF8, h, String.fromUTF8]

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
instance (priority := low) {α : Type} [FromProto α] : FromProtoField α where decodeProtoField k fs := (lookupField k fs).elim (.error s!"protobuf: missing field {k}") FromProto.fromProtoVal
instance (priority := low) {α : Type} [LawfulProto α] : LawfulProtoField α where
  encodeProtoField_tag _ _ _ h := by rw [List.mem_singleton.1 h]
  decodeProtoField_skip_prefix k pre rest hne := by simp [FromProtoField.decodeProtoField, skipUnknown_preserves_lookup_prefix k pre rest hne]
  decodeProtoField_hit_raw _ _ _ _ := by simp [ToProtoField.encodeProtoField, FromProtoField.decodeProtoField, lookupField]

instance {α : Type} [ToProto α] : ToProtoField (Option α) where encodeProtoField k | none => [] | some a => [(k, ToProto.toProtoVal a)]
instance {α : Type} [FromProto α] : FromProtoField (Option α) where decodeProtoField k fs := (lookupField k fs).elim (.ok none) fun w => (FromProto.fromProtoVal w).map some
instance {α : Type} [LawfulProto α] : LawfulProtoField (Option α) where
  encodeProtoField_tag _ opt _ h := by cases opt with | none => cases h | some _ => rw [List.mem_singleton.1 h]
  decodeProtoField_skip_prefix k pre rest hne := by simp [FromProtoField.decodeProtoField, skipUnknown_preserves_lookup_prefix k pre rest hne]
  decodeProtoField_hit_raw k opt rest hne := by
    cases opt with
    | none => simp [ToProtoField.encodeProtoField, FromProtoField.decodeProtoField, show lookupField k rest = none by simpa [lookupField] using skipUnknown_preserves_lookup_prefix k rest [] hne]
    | some _ => simp [ToProtoField.encodeProtoField, FromProtoField.decodeProtoField, lookupField, Except.map]

namespace Proto
def AllTagsGt (k : Nat) (fs : List (Nat × WireVal)) : Prop := ∀ kw ∈ fs, k < kw.1
def AllTagsLe (k : Nat) (fs : List (Nat × WireVal)) : Prop := ∀ kw ∈ fs, kw.1 ≤ k
@[simp] theorem allTagsGt_nil (k : Nat) : AllTagsGt k [] := fun _ h => nomatch h
theorem allTagsGt_step {α : Type} [LawfulProtoField α] {k : Nat} (a : α) {rest : List (Nat × WireVal)} (hr : AllTagsGt (k + 1) rest) :
    AllTagsGt k (ToProtoField.encodeProtoField (k + 1) a ++ rest) := fun kw hm => (List.mem_append.1 hm).elim (fun h1 => by rw [LawfulProtoField.encodeProtoField_tag (k + 1) a kw h1]; exact Nat.lt_succ_self k) (fun h2 => Nat.lt_trans (Nat.lt_succ_self k) (hr kw h2))
theorem allTagsLe_single {α : Type} [LawfulProtoField α] (k : Nat) (a : α) : AllTagsLe k (ToProtoField.encodeProtoField k a) := fun kw hm => by rw [LawfulProtoField.encodeProtoField_tag k a kw hm]; exact Nat.le_refl k
theorem allTagsLe_append_step {α : Type} [LawfulProtoField α] {k : Nat} {pre : List (Nat × WireVal)} (hp : AllTagsLe k pre) (a : α) :
    AllTagsLe (k + 1) (pre ++ ToProtoField.encodeProtoField (k + 1) a) := fun kw hm => (List.mem_append.1 hm).elim (fun h1 => Nat.le_succ_of_le (hp kw h1)) (fun h2 => by rw [LawfulProtoField.encodeProtoField_tag (k + 1) a kw h2]; exact Nat.le_refl _)
theorem split_step {α : Type} [ToProtoField α] {all pre tail : List (Nat × WireVal)} (k : Nat) (a : α)
    (h : all = pre ++ (ToProtoField.encodeProtoField k a ++ tail)) : all = (pre ++ ToProtoField.encodeProtoField k a) ++ tail := h.trans (List.append_assoc pre _ tail).symm
theorem msg_tags_pos_encodeAppend {α : Type} [LawfulProtoField α] {k : Nat} (hk : 0 < k) (a : α) {rest : List (Nat × WireVal)} (hr : ∀ kw ∈ rest, 0 < kw.1) :
    ∀ kw ∈ ToProtoField.encodeProtoField k a ++ rest, 0 < kw.1 := fun kw hm => (List.mem_append.1 hm).elim (fun h1 => by rw [LawfulProtoField.encodeProtoField_tag k a kw h1]; exact hk) (hr kw)
theorem decodeProtoField_hit {α : Type} [LawfulProtoField α] (k : Nat) (a : α) (rest : List (Nat × WireVal)) (hgt : AllTagsGt k rest) :
    FromProtoField.decodeProtoField k (ToProtoField.encodeProtoField k a ++ rest) = .ok a := LawfulProtoField.decodeProtoField_hit_raw k a rest fun kw hm => Nat.ne_of_gt (hgt kw hm)
theorem decodeProtoField_mid {α : Type} [LawfulProtoField α] {k : Nat} {all pre rest : List (Nat × WireVal)} (a : α)
    (hsplit : all = pre ++ (ToProtoField.encodeProtoField (k + 1) a ++ rest)) (hle : AllTagsLe k pre) (hgt : AllTagsGt (k + 1) rest) : FromProtoField.decodeProtoField (k + 1) all = .ok a := by
  rw [hsplit, LawfulProtoField.decodeProtoField_skip_prefix (k + 1) pre _ fun kw hm => Nat.ne_of_lt (Nat.lt_succ_of_le (hle kw hm))]; exact decodeProtoField_hit (k + 1) a rest hgt
end Proto

@[reducible, noinline, nospecialize] def ToProto.ofFields {α : Type} (enc : α → List (Nat × WireVal)) : ToProto α := ⟨fun a => .bytes (encodeFieldsSpec (enc a)), enc⟩
@[reducible, noinline, nospecialize] def FromProto.ofFields {α : Type} (dec : List (Nat × WireVal) → Except String α) : FromProto α :=
  ⟨fun | .bytes b => (decodeFieldsSpec b).bind dec | _ => .error "protobuf: expected embedded message bytes", dec⟩
@[reducible, noinline, nospecialize] def LawfulProto.ofFields {α : Type} (enc : α → List (Nat × WireVal)) (dec : List (Nat × WireVal) → Except String α)
    (htags : ∀ (a : α) (kw : Nat × WireVal), kw ∈ enc a → 0 < kw.1) (hrt : ∀ a : α, dec (enc a) = .ok a) : LawfulProto α where
  toToProto := .ofFields enc; toFromProto := .ofFields dec; msg_tags_pos := htags; fromProtoMsg_toProtoMsg := hrt
  fromProtoVal_toProtoVal a := by change (decodeFieldsSpec (encodeFieldsSpec (enc a))).bind dec = .ok a; rw [decodeFieldsSpec_encodeFieldsSpec _ (htags a)]; exact hrt a

@[reducible, noinline, nospecialize] def ToProto.ofEquiv {α β : Type} [ToProto β] (toB : α → β) : ToProto α := ⟨fun a => ToProto.toProtoVal (toB a), fun a => ToProto.toProtoMsg (toB a)⟩
@[reducible, noinline, nospecialize] def FromProto.ofEquiv {α β : Type} [FromProto β] (ofB : β → α) : FromProto α := ⟨fun w => (FromProto.fromProtoVal (α := β) w).map ofB, fun fs => (FromProto.fromProtoMsg (α := β) fs).map ofB⟩
@[reducible, noinline, nospecialize] def FromProto.ofRetract {α β : Type} [FromProto β] (ofB : β → Except String α) : FromProto α := ⟨fun w => (FromProto.fromProtoVal (α := β) w).bind ofB, fun fs => (FromProto.fromProtoMsg (α := β) fs).bind ofB⟩
@[reducible, noinline, nospecialize] def LawfulProto.ofEquiv {α β : Type} [LawfulProto β] (toB : α → β) (ofB : β → α) (hinv : ∀ a : α, ofB (toB a) = a) : LawfulProto α where
  toToProto := .ofEquiv toB; toFromProto := .ofEquiv ofB; msg_tags_pos a := LawfulProto.msg_tags_pos (toB a)
  fromProtoMsg_toProtoMsg a := (congrArg (Except.map ofB) (LawfulProto.fromProtoMsg_toProtoMsg (toB a))).trans (congrArg Except.ok (hinv a))
  fromProtoVal_toProtoVal a := (congrArg (Except.map ofB) (LawfulProto.fromProtoVal_toProtoVal (toB a))).trans (congrArg Except.ok (hinv a))
@[reducible, noinline, nospecialize] def LawfulProto.ofRetract {α β : Type} [LawfulProto β] (toB : α → β) (ofB : β → Except String α) (hinv : ∀ a : α, ofB (toB a) = .ok a) : LawfulProto α where
  toToProto := .ofEquiv toB; toFromProto := .ofRetract ofB; msg_tags_pos a := LawfulProto.msg_tags_pos (toB a)
  fromProtoMsg_toProtoMsg a := (congrArg (·.bind ofB) (LawfulProto.fromProtoMsg_toProtoMsg (toB a))).trans (hinv a)
  fromProtoVal_toProtoVal a := (congrArg (·.bind ofB) (LawfulProto.fromProtoVal_toProtoVal (toB a))).trans (hinv a)

/-! ## Composite & Container `LawfulProto` Instances (`Date`, `Option`, `Except`, `Prod`, `List`, `Array`, `Url`) -/

macro "qed_equiv_codec% " kind:ident "[" vs:ident,* "]" "(" ty:term "," toB:term "," ofB:term "," hinv:term ")" : command => do
  let ids := vs.getElems
  let mkInst (p : Lean.TSyntax `prio) (reqCls outCls : Lean.Name) (body : Lean.TSyntax `term) := do
    let reqId := Lean.mkIdent reqCls; let outId := Lean.mkIdent outCls
    let reqs ← ids.mapM fun id => `($reqId $id)
    `(command| instance (priority := $p) $[{$ids:ident : Type}]* $[[$reqs:term]]* : $outId $ty := $body)
  let k := kind.getId; let p ← if k == `jsonLow then `(prio| low) else `(prio| default)
  if k == `json || k == `jsonLow then
    return ⟨Lean.mkNullNode #[
      ← mkInst p `Qed.ToJson `Qed.ToJson (← `(.ofEquiv $toB)),
      ← mkInst p `Qed.FromJson `Qed.FromJson (← `(.ofEquiv $ofB)),
      ← mkInst p `Qed.LawfulJson `Qed.LawfulJson (← `(.ofEquiv $toB $ofB $hinv)),
      ← mkInst p `Qed.ToJson `Qed.NonNullJson (← `(⟨nofun⟩))]⟩
  else
    return ⟨Lean.mkNullNode #[
      ← mkInst p `Qed.ToProto `Qed.ToProto (← `(.ofEquiv $toB)),
      ← mkInst p `Qed.FromProto `Qed.FromProto (← `(.ofEquiv $ofB)),
      ← mkInst p `Qed.LawfulProto `Qed.LawfulProto (← `(.ofEquiv $toB $ofB $hinv))]⟩

def Date.toProtoFields (d : Date) : List (Nat × WireVal) := [(1, ToProto.toProtoVal d.year), (2, ToProto.toProtoVal d.month), (3, ToProto.toProtoVal d.day)]
def Date.fromProtoFields (fs : List (Nat × WireVal)) : Except String Date := do
  (Date.mk? (← FromProtoField.decodeProtoField 1 fs) (← FromProtoField.decodeProtoField 2 fs) (← FromProtoField.decodeProtoField 3 fs)).elim (.error "protobuf: invalid calendar Date") .ok
instance : ToProto Date := .ofFields Date.toProtoFields
instance : FromProto Date := .ofFields Date.fromProtoFields
instance : LawfulProto Date := .ofFields Date.toProtoFields Date.fromProtoFields
  (by intro _ _ h; simp only [Date.toProtoFields, List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> exact Nat.zero_lt_succ _)
  (by rintro ⟨_, _, _, hok⟩; simp [Date.fromProtoFields, Date.toProtoFields, FromProtoField.decodeProtoField, lookupField, Date.mk?, hok, bind, Except.bind])

section
variable {ε α β : Type}
instance [ToProto α] : ToProto (Option α) := .ofFields (ToProtoField.encodeProtoField 1)
instance [FromProto α] : FromProto (Option α) := .ofFields (FromProtoField.decodeProtoField 1)
instance [LawfulProto α] : LawfulProto (Option α) := .ofFields (ToProtoField.encodeProtoField 1) (FromProtoField.decodeProtoField 1)
  (fun opt kw h => by rw [LawfulProtoField.encodeProtoField_tag 1 opt kw h]; exact Nat.zero_lt_succ _)
  (fun opt => by simpa using LawfulProtoField.decodeProtoField_hit_raw 1 opt [] (by simp))

@[noinline, nospecialize] private def encodeExceptFields [ToProto ε] [ToProto α] : Except ε α → List (Nat × WireVal) | .ok a => [(1, ToProto.toProtoVal a)] | .error e => [(2, ToProto.toProtoVal e)]
@[noinline, nospecialize] private def decodeExceptFields [FromProto ε] [FromProto α] (fs : List (Nat × WireVal)) : Except String (Except ε α) :=
  match lookupField 1 fs, lookupField 2 fs with | some w, _ => (FromProto.fromProtoVal (α := α) w).map .ok | none, some w => (FromProto.fromProtoVal (α := ε) w).map .error | none, none => .error "protobuf: missing Except branch"
instance [ToProto ε] [ToProto α] : ToProto (Except ε α) := .ofFields encodeExceptFields
instance [FromProto ε] [FromProto α] : FromProto (Except ε α) := .ofFields decodeExceptFields
instance [LawfulProto ε] [LawfulProto α] : LawfulProto (Except ε α) := .ofFields encodeExceptFields decodeExceptFields
  (by intro r _ h; cases r <;> (rw [List.mem_singleton.1 h]; exact Nat.zero_lt_succ _))
  (by intro r; cases r <;> simp [encodeExceptFields, decodeExceptFields, lookupField, Except.map])

@[noinline, nospecialize] private def encodeProdFields [ToProto α] [ToProto β] (p : α × β) : List (Nat × WireVal) := [(1, ToProto.toProtoVal p.1), (2, ToProto.toProtoVal p.2)]
@[noinline, nospecialize] private def decodeProdFields [FromProto α] [FromProto β] (fs : List (Nat × WireVal)) : Except String (α × β) :=
  (decodeFieldVal 1 fs "protobuf: missing tuple field 1").bind fun a => (decodeFieldVal 2 fs "protobuf: missing tuple field 2").map (a, ·)
instance [ToProto α] [ToProto β] : ToProto (α × β) := .ofFields encodeProdFields
instance [FromProto α] [FromProto β] : FromProto (α × β) := .ofFields decodeProdFields
instance [LawfulProto α] [LawfulProto β] : LawfulProto (α × β) := .ofFields encodeProdFields decodeProdFields
  (by intro _ _ h; simp only [encodeProdFields, List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> exact Nat.zero_lt_succ _)
  (by rintro ⟨_, _⟩; simp [encodeProdFields, decodeProdFields, decodeFieldVal, lookupField, Except.bind, Except.map])

@[noinline, nospecialize] private def encodeRepeatedField1 [ToProto α] (xs : List α) : List (Nat × WireVal) := xs.map fun x => (1, ToProto.toProtoVal x)
@[noinline, nospecialize] private def decodeRepeatedField1 [FromProto α] (fs : List (Nat × WireVal)) : Except String (List α) := (lookupRepeated 1 fs).mapM FromProto.fromProtoVal
private theorem lookupRepeated_map_one [ToProto α] : ∀ xs : List α, lookupRepeated 1 (encodeRepeatedField1 xs) = xs.map ToProto.toProtoVal
  | [] => rfl | x :: rest => congrArg (ToProto.toProtoVal x :: ·) (lookupRepeated_map_one rest)
instance [ToProto α] : ToProto (List α) := .ofFields encodeRepeatedField1
instance [FromProto α] : FromProto (List α) := .ofFields decodeRepeatedField1
instance [LawfulProto α] : LawfulProto (List α) := .ofFields encodeRepeatedField1 decodeRepeatedField1
  (by intro _ _ h; rcases List.mem_map.1 h with ⟨_, _, rfl⟩; exact Nat.zero_lt_succ _)
  (fun xs => by rw [decodeRepeatedField1, lookupRepeated_map_one]; exact list_mapM_map_ok _ _ LawfulProto.fromProtoVal_toProtoVal xs)

instance [ToProto α] : ToProto (Array α) := .ofEquiv Array.toList
instance [FromProto α] : FromProto (Array α) := .ofEquiv List.toArray
instance [LawfulProto α] : LawfulProto (Array α) := .ofEquiv Array.toList List.toArray fun ⟨_⟩ => rfl
end

private def parseUrlWire (pfx s : String) : Except String Url := (Url.parse? s).elim (.error s!"{pfx}unsafe URL `{s}`") .ok
private theorem parseUrlWire_raw (pfx : String) (u : Url) : parseUrlWire pfx u.raw = .ok u := by simp [parseUrlWire, Url.parse?, u.safe]
instance : ToJson Url := .ofEquiv Url.raw
instance : FromJson Url := .ofRetract (parseUrlWire "")
instance : LawfulJson Url := .ofRetract Url.raw (parseUrlWire "") (parseUrlWire_raw "")
instance : NonNullJson Url := ⟨nofun⟩
instance : ToProto Url := .ofEquiv Url.raw
instance : FromProto Url := .ofRetract (parseUrlWire "protobuf: ")
instance : LawfulProto Url := .ofRetract Url.raw (parseUrlWire "protobuf: ") (parseUrlWire_raw "protobuf: ")

/-- Typed application-level RPC failure transmitted cleanly inside binary Protobuf responses. -/
structure RpcDomainError (ε : Type) where
  tag     : ε
  message : String
deriving Inhabited, DecidableEq, Repr

qed_equiv_codec% json [ε] (RpcDomainError ε,
  fun e => (e.tag, e.message), fun p : ε × String => ⟨p.1, p.2⟩, fun ⟨_, _⟩ => rfl)
qed_equiv_codec% proto [ε] (RpcDomainError ε,
  fun e => (e.tag, e.message), fun p : ε × String => RpcDomainError.mk p.1 p.2, fun ⟨_, _⟩ => rfl)

end Qed
