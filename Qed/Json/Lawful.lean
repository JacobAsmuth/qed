import Qed.Json.Basic

namespace Qed

class LawfulJson (α : Type) extends ToJson α, FromJson α where
  depthBound      : Nat := 0
  depth_toJson    : ∀ a : α, (toJson a).depth ≤ depthBound := by intro _; exact Nat.le_refl _
  fromJson_toJson : ∀ a : α, fromJson (toJson a) = .ok a

attribute [simp] LawfulJson.fromJson_toJson

instance : LawfulJson Unit where
  depthBound := 1
  depth_toJson | () => Nat.le_refl 1
  fromJson_toJson | () => rfl
instance : LawfulJson JsonNumber where fromJson_toJson _ := rfl
instance : LawfulJson Bool       where fromJson_toJson _ := rfl
instance : LawfulJson String     where fromJson_toJson _ := rfl
instance : LawfulJson Int        where fromJson_toJson i := by simp [fromJson, JsonNumber.toInt?]
instance : LawfulJson Nat        where fromJson_toJson n := by simp [fromJson, JsonNumber.toInt?]

private theorem mapM_fromJson_toJson {α : Type} [LawfulJson α] :
    ∀ xs : List α, (xs.map toJson).mapM (m := Except String) fromJson = .ok xs
  | []      => rfl
  | x :: xs => by
      simp only [List.map_cons, List.mapM_cons, LawfulJson.fromJson_toJson x, mapM_fromJson_toJson xs]
      rfl

instance [LawfulJson α] : LawfulJson (List α) where
  depthBound := 1 + LawfulJson.depthBound α
  depth_toJson xs := Nat.add_le_add_left
    (Json.maxArr_le_iff.2 (by intro e he; rcases List.mem_map.1 he with ⟨a, _, rfl⟩; exact LawfulJson.depth_toJson a)) 1
  fromJson_toJson := mapM_fromJson_toJson

instance [LawfulJson α] : LawfulJson (Array α) where
  depthBound := 1 + LawfulJson.depthBound α
  depth_toJson xs := LawfulJson.depth_toJson xs.toList
  fromJson_toJson xs := by
    change (fromJson (toJson xs.toList) : Except String (List α)).map List.toArray = .ok xs
    rw [LawfulJson.fromJson_toJson xs.toList]; rfl

instance [LawfulJson α] [LawfulJson β] : LawfulJson (α × β) where
  depthBound := 1 + max (LawfulJson.depthBound α) (LawfulJson.depthBound β)
  depth_toJson p := Nat.add_le_add_left (Json.maxArr_le_iff.2 (by
    intro e he; simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Nat.le_trans (LawfulJson.depth_toJson p.1) (Nat.le_max_left _ _)
    · exact Nat.le_trans (LawfulJson.depth_toJson p.2) (Nat.le_max_right _ _))) 1
  fromJson_toJson p := by
    rcases p with ⟨a, b⟩
    change (do return (← fromJson (toJson a), ← fromJson (toJson b))) = .ok (a, b)
    rw [LawfulJson.fromJson_toJson a, LawfulJson.fromJson_toJson b]; rfl

instance [LawfulJson α] [LawfulJson β] : LawfulJson (Sum α β) where
  depthBound := 1 + max (LawfulJson.depthBound α) (LawfulJson.depthBound β)
  depth_toJson s := by
    cases s <;> refine Nat.add_le_add_left (Json.maxArr_le_iff.2 fun e he => ?_) 1 <;>
      (simp only [List.mem_cons, List.not_mem_nil, or_false] at he; rcases he with rfl | rfl)
    · exact Nat.zero_le _
    · exact Nat.le_trans (LawfulJson.depth_toJson _) (Nat.le_max_left _ _)
    · exact Nat.zero_le _
    · exact Nat.le_trans (LawfulJson.depth_toJson _) (Nat.le_max_right _ _)
  fromJson_toJson
    | .inl a => by change (fromJson (toJson a) : Except String α).map Sum.inl = _; rw [LawfulJson.fromJson_toJson a]; rfl
    | .inr b => by change (fromJson (toJson b) : Except String β).map Sum.inr = _; rw [LawfulJson.fromJson_toJson b]; rfl

class NonNullJson (α : Type) [ToJson α] : Prop where
  toJson_ne_null : ∀ a : α, toJson a ≠ .null

instance                        : NonNullJson Unit       := ⟨fun () => nofun⟩
instance                        : NonNullJson JsonNumber := ⟨nofun⟩
instance                        : NonNullJson Bool       := ⟨nofun⟩
instance                        : NonNullJson String     := ⟨nofun⟩
instance                        : NonNullJson Int        := ⟨nofun⟩
instance                        : NonNullJson Nat        := ⟨nofun⟩
instance [ToJson α]             : NonNullJson (List α)   := ⟨nofun⟩
instance [ToJson α]             : NonNullJson (Array α)  := ⟨nofun⟩
instance [ToJson α] [ToJson β]  : NonNullJson (α × β)    := ⟨fun (_, _) => nofun⟩
instance [ToJson α] [ToJson β]  : NonNullJson (Sum α β)  := ⟨fun | .inl _ | .inr _ => nofun⟩

instance [LawfulJson α] [NonNullJson α] : LawfulJson (Option α) where
  depthBound := LawfulJson.depthBound α
  depth_toJson | none => Nat.zero_le _ | some a => LawfulJson.depth_toJson a
  fromJson_toJson
    | none   => rfl
    | some a => by
        have hne := NonNullJson.toJson_ne_null a
        have hfa := LawfulJson.fromJson_toJson a
        change (fromJson (toJson a) : Except String (Option α)) = .ok (some a)
        unfold fromJson
        cases hj : toJson a
        · exact absurd hj hne
        all_goals rw [hj] at hfa; exact congrArg (Except.map some) hfa

@[reducible] def LawfulJson.iso {α β : Type} (inst : LawfulJson β)
    (toB : α → β) (fromB : β → α) (left_inv : ∀ a, fromB (toB a) = a) : LawfulJson α where
  toJson a := @ToJson.toJson β inst.toToJson (toB a)
  fromJson j := (@FromJson.fromJson β inst.toFromJson j).map fromB
  depthBound := @LawfulJson.depthBound β inst
  depth_toJson a := @LawfulJson.depth_toJson β inst (toB a)
  fromJson_toJson a := by
    change (@FromJson.fromJson β inst.toFromJson (@ToJson.toJson β inst.toToJson (toB a))).map fromB = .ok a
    rw [@LawfulJson.fromJson_toJson β inst (toB a)]
    exact congrArg Except.ok (left_inv a)

theorem NonNullJson.iso {α β : Type} (inst : LawfulJson β)
    (hnn : @NonNullJson β inst.toToJson)
    (toB : α → β) (fromB : β → α) (left_inv : ∀ a, fromB (toB a) = a) :
    @NonNullJson α (LawfulJson.iso inst toB fromB left_inv).toToJson :=
  @NonNullJson.mk α (LawfulJson.iso inst toB fromB left_inv).toToJson
    (fun a => @NonNullJson.toJson_ne_null β inst.toToJson hnn (toB a))

@[simp] theorem LawfulJson.fromField_of_field {α : Type} [LawfulJson α] (j : Json) (k : String) (a : α)
    (h : j.field k = .ok (toJson a)) :
    (FromJsonField.fromField j k : Except String α) = .ok a := by
  simp [FromJsonField.fromField, h]

end Qed
