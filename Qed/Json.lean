import Qed.Json.Basic
import Qed.Json.Proofs
import Qed.Json.Lawful

namespace Qed

theorem LawfulJson.parse_render_toJson {α : Type} [LawfulJson α] (a : α)
    {maxDepth : Nat} (h : LawfulJson.depthBound α ≤ maxDepth := by omega) :
    (Json.parse (Json.render (toJson a)) maxDepth).bind fromJson = .ok a := by
  unfold Json.parse
  rw [Qed.parse_render (Nat.le_trans (LawfulJson.depth_toJson a) h)]
  exact LawfulJson.fromJson_toJson a

end Qed
