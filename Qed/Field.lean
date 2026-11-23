import Qed.Html
import Qed.Json.Lawful
import Qed.Proto.Lawful

namespace Qed

structure Field {α : Type} (p : α → Prop) where
  val : α
  ok  : p val

section FieldInstances
variable {α : Type} {p : α → Prop}
@[reducible] instance : CoeOut (Field p) α := ⟨Field.val⟩
@[reducible] instance {msg : Type} [Coe α (Html msg)] : CoeHTCT (Field p) (Html msg) := ⟨fun f => (f.val : Html msg)⟩
@[reducible] instance : CoeHTCT (Option (Field p)) (Option α) := ⟨Option.map Field.val⟩
instance [ToString α] : ToString (Field p) := ⟨fun f => toString f.val⟩
instance [BEq α] : BEq (Field p) := ⟨fun a b => a.val == b.val⟩
instance [Repr α] : Repr (Field p) := ⟨fun f n => reprPrec f.val n⟩
instance [BEq α] [LawfulBEq α] : LawfulBEq (Field p) where
  eq_of_beq {a b} h := by cases a; cases b; cases eq_of_beq (α := α) h; rfl
  rfl {a} := beq_self_eq_true a.val
instance [DecidableEq α] : DecidableEq (Field p) := fun ⟨a, _⟩ ⟨b, _⟩ =>
  if h : a = b then isTrue (by cases h; rfl) else isFalse fun heq => h (congrArg Field.val heq)
private def mkField [DecidablePred p] (err : String) (a : α) : Except String (Field p) := if h : p a then .ok ⟨a, h⟩ else .error err
instance [ToJson α] : ToJson (Field p) := .ofEquiv Field.val
instance [DecidablePred p] [FromJson α] : FromJson (Field p) := .ofRetract (mkField "failed field refinement")
instance [DecidablePred p] [LawfulJson α] : LawfulJson (Field p) := .ofRetract Field.val (mkField "failed field refinement") fun ⟨_, hok⟩ => dif_pos hok
instance [ToJson α] [NonNullJson α] : NonNullJson (Field p) := ⟨fun f => NonNullJson.toJson_ne_null f.val⟩
instance [ToProto α] : ToProto (Field p) := .ofEquiv Field.val
instance [DecidablePred p] [FromProto α] : FromProto (Field p) := .ofRetract (mkField "protobuf: failed field refinement")
instance [DecidablePred p] [LawfulProto α] : LawfulProto (Field p) := .ofRetract Field.val (mkField "protobuf: failed field refinement") fun ⟨_, hok⟩ => dif_pos hok
@[simp] theorem Proto.encode_field [ToProto α] (f : Field p) : Proto.encode f = Proto.encode f.val := rfl
end FieldInstances

end Qed
