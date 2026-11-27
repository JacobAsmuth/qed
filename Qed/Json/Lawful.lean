import Qed.Json.Basic

namespace Qed

class LawfulJson (α : Type) extends ToJson α, FromJson α where
  depthBound      : Nat := 0
  depth_toJson    : ∀ a : α, (toJson a).depth ≤ depthBound := by intro _; exact Nat.le_refl _
  fromJson_toJson : ∀ a : α, fromJson (toJson a) = .ok a

attribute [simp] LawfulJson.fromJson_toJson

instance : LawfulJson Unit       where depthBound := 1; depth_toJson _ := Nat.le_refl 1; fromJson_toJson | () => rfl
instance : LawfulJson JsonNumber where fromJson_toJson _ := rfl
instance : LawfulJson Bool       where fromJson_toJson _ := rfl
instance : LawfulJson String     where fromJson_toJson _ := rfl
instance : LawfulJson Int        where fromJson_toJson _ := by simp [toJson, fromJson, JsonNumber.toInt?]
instance : LawfulJson Nat        where fromJson_toJson _ := by simp [toJson, fromJson, JsonNumber.toInt?]

theorem list_mapM_map_ok {α β ε : Type} (f : α → β) (g : β → Except ε α) (h : ∀ a, g (f a) = .ok a) :
    ∀ xs : List α, (xs.map f).mapM (m := Except ε) g = .ok xs
  | [] => rfl | x :: xs => by simp only [List.map_cons, List.mapM_cons, h x, list_mapM_map_ok f g h xs]; rfl

@[reducible, noinline, nospecialize] def ToJson.ofEquiv {α β : Type} [ToJson β] (toB : α → β) : ToJson α := ⟨fun a => toJson (toB a)⟩
@[reducible, noinline, nospecialize] def FromJson.ofEquiv {α β : Type} [FromJson β] (ofB : β → α) : FromJson α := ⟨fun j => (fromJson j : Except String β).map ofB⟩
@[reducible, noinline, nospecialize] def FromJson.ofRetract {α β : Type} [FromJson β] (ofB : β → Except String α) : FromJson α := ⟨fun j => (fromJson j : Except String β).bind ofB⟩

@[reducible, noinline, nospecialize] def LawfulJson.iso {α β : Type} (inst : LawfulJson β) (toB : α → β) (fromB : β → α) (left_inv : ∀ a, fromB (toB a) = a) : LawfulJson α where
  toJson a := @ToJson.toJson β inst.toToJson (toB a); fromJson j := (@FromJson.fromJson β inst.toFromJson j).map fromB
  depthBound := @LawfulJson.depthBound β inst; depth_toJson a := @LawfulJson.depth_toJson β inst (toB a)
  fromJson_toJson a := (congrArg (Except.map fromB) (@LawfulJson.fromJson_toJson β inst (toB a))).trans (congrArg Except.ok (left_inv a))

@[reducible, noinline, nospecialize] def LawfulJson.ofEquiv {α β : Type} [LawfulJson β] (toB : α → β) (ofB : β → α) (hinv : ∀ a, ofB (toB a) = a) : LawfulJson α :=
  LawfulJson.iso inferInstance toB ofB hinv

@[reducible, noinline, nospecialize] def LawfulJson.ofRetract {α β : Type} [LawfulJson β] (toB : α → β) (ofB : β → Except String α) (hinv : ∀ a, ofB (toB a) = .ok a) : LawfulJson α where
  toToJson := .ofEquiv toB; toFromJson := .ofRetract ofB; depthBound := LawfulJson.depthBound β; depth_toJson a := LawfulJson.depth_toJson (toB a)
  fromJson_toJson a := (congrArg (·.bind ofB) (LawfulJson.fromJson_toJson (toB a))).trans (hinv a)

instance [LawfulJson α] : LawfulJson (List α) where
  depthBound := 1 + LawfulJson.depthBound α
  depth_toJson xs := Nat.add_le_add_left (Json.maxArr_le_iff.2 fun _ he => by rcases List.mem_map.1 he with ⟨a, _, rfl⟩; exact LawfulJson.depth_toJson a) 1
  fromJson_toJson := list_mapM_map_ok toJson fromJson LawfulJson.fromJson_toJson

instance [LawfulJson α] : LawfulJson (Array α) := .ofEquiv Array.toList List.toArray fun ⟨_⟩ => rfl

instance [LawfulJson α] [LawfulJson β] : LawfulJson (α × β) where
  depthBound := 1 + max (LawfulJson.depthBound α) (LawfulJson.depthBound β)
  depth_toJson | (a, b) => Nat.add_le_add_left (by simpa [Json.maxArr, Nat.max_le] using ⟨Nat.le_trans (LawfulJson.depth_toJson a) (Nat.le_max_left _ _), Nat.le_trans (LawfulJson.depth_toJson b) (Nat.le_max_right _ _)⟩) 1
  fromJson_toJson := fun (a, b) => by
    change ((fromJson (toJson a) : Except String α).bind fun x => (fromJson (toJson b) : Except String β).map (x, ·)) = .ok (a, b)
    rw [LawfulJson.fromJson_toJson a, LawfulJson.fromJson_toJson b]; rfl

instance [LawfulJson α] [LawfulJson β] : LawfulJson (Sum α β) where
  depthBound := 1 + max (LawfulJson.depthBound α) (LawfulJson.depthBound β)
  depth_toJson
    | .inl a => Nat.add_le_add_left (by simpa [Json.maxArr, Json.depth] using Nat.le_trans (LawfulJson.depth_toJson a) (Nat.le_max_left _ _)) 1
    | .inr b => Nat.add_le_add_left (by simpa [Json.maxArr, Json.depth] using Nat.le_trans (LawfulJson.depth_toJson b) (Nat.le_max_right _ _)) 1
  fromJson_toJson
    | .inl a => congrArg (Except.map Sum.inl) (LawfulJson.fromJson_toJson a)
    | .inr b => congrArg (Except.map Sum.inr) (LawfulJson.fromJson_toJson b)

class NonNullJson (α : Type) [ToJson α] : Prop where toJson_ne_null : ∀ a : α, toJson a ≠ .null

instance : NonNullJson Unit := ⟨nofun⟩
instance : NonNullJson JsonNumber := ⟨nofun⟩
instance : NonNullJson Bool := ⟨nofun⟩
instance : NonNullJson String := ⟨nofun⟩
instance : NonNullJson Int := ⟨nofun⟩
instance : NonNullJson Nat := ⟨nofun⟩
instance [ToJson α] : NonNullJson (List α) := ⟨nofun⟩
instance [ToJson α] : NonNullJson (Array α) := ⟨nofun⟩
instance [ToJson α] [ToJson β] : NonNullJson (α × β) := ⟨fun (_, _) => nofun⟩
instance [ToJson α] [ToJson β] : NonNullJson (Sum α β) := ⟨fun | .inl _ | .inr _ => nofun⟩

instance [LawfulJson α] [NonNullJson α] : LawfulJson (Option α) where
  depthBound := LawfulJson.depthBound α
  depth_toJson | none => Nat.zero_le _ | some a => LawfulJson.depth_toJson a
  fromJson_toJson
    | none => rfl
    | some a => by
        have hfa := LawfulJson.fromJson_toJson a; change (fromJson (toJson a) : Except String (Option α)) = .ok (some a)
        unfold fromJson; cases hj : toJson a
        · exact absurd hj (NonNullJson.toJson_ne_null a)
        all_goals rw [hj] at hfa; exact congrArg (Except.map some) hfa

theorem NonNullJson.iso {α β : Type} (inst : LawfulJson β) (hnn : @NonNullJson β inst.toToJson)
    (toB : α → β) (fromB : β → α) (left_inv : ∀ a, fromB (toB a) = a) : @NonNullJson α (LawfulJson.iso inst toB fromB left_inv).toToJson :=
  @NonNullJson.mk α (LawfulJson.iso inst toB fromB left_inv).toToJson fun a => @NonNullJson.toJson_ne_null β inst.toToJson hnn (toB a)

class LawfulFromJsonField (α : Type) [ToJson α] [FromJsonField α] : Prop where
  fromField_of_field : ∀ (j : Json) (k : String) (a : α),
    j.field k = .ok (toJson a) → (FromJsonField.fromField j k : Except String α) = .ok a

instance (priority := low) {α : Type} [LawfulJson α] : LawfulFromJsonField α where
  fromField_of_field j k a h := by
    simp [FromJsonField.fromField, fromFieldVal, Except.bind, h]

instance {α : Type} [LawfulJson α] [NonNullJson α] : LawfulFromJsonField (Option α) where
  fromField_of_field j k opt h := by
    have hget : j.get? k = some (toJson opt) := by rw [Json.get?, h]; rfl
    cases opt with
    | none => simp [FromJsonField.fromField, hget, toJson, Option.elim]
    | some a =>
        have hnn := NonNullJson.toJson_ne_null a
        simp only [FromJsonField.fromField, hget, toJson, Option.elim]
        cases hj : toJson a with
        | null => exact absurd hj hnn
        | bool _ | num _ | str _ | arr _ | obj _ =>
            have hfa := LawfulJson.fromJson_toJson a
            rw [hj] at hfa
            simp [fromFieldVal, hfa, Except.map]

@[simp] theorem LawfulJson.fromField_of_field {α : Type} [ToJson α] [FromJsonField α] [LawfulFromJsonField α]
    (j : Json) (k : String) (a : α) (h : j.field k = .ok (toJson a)) :
    (FromJsonField.fromField j k : Except String α) = .ok a :=
  LawfulFromJsonField.fromField_of_field j k a h

/-- Typeclass implemented by every nullary `enum` declaration, providing a lossless wire string codec. -/
class StringEnum (α : Type) where
  toWire : α → String
  ofWire : String → Except String α

end Qed
