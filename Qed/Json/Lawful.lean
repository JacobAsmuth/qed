import Qed.Json.Basic
import Qed.Json.Proofs

namespace Qed

class LawfulJson (α : Type) extends ToJson α, FromJson α where
  depthBound      : Nat := 0
  depth_toJson    : ∀ a : α, (toJson a).depth ≤ depthBound := by intro _; exact Nat.le_refl _
  fromJson_toJson : ∀ a : α, fromJson (toJson a) = .ok a

attribute [simp] LawfulJson.fromJson_toJson

theorem LawfulJson.parse_render_toJson {α : Type} [LawfulJson α] (a : α)
    {maxDepth : Nat} (h : LawfulJson.depthBound α ≤ maxDepth := by omega) :
    (Json.parse (Json.render (toJson a)) maxDepth).bind fromJson = .ok a := by
  unfold Json.parse
  rw [Qed.parse_render (Nat.le_trans (LawfulJson.depth_toJson a) h)]
  exact LawfulJson.fromJson_toJson a

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

@[simp] theorem LawfulJson.fromField_of_field {α : Type} [LawfulJson α] (j : Json) (k : String) (a : α)
    (h : j.field k = .ok (toJson a)) :
    (FromJsonField.fromField j k : Except String α) = .ok a := by
  simp [FromJsonField.fromField, h]

end Qed
