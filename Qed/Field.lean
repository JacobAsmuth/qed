import Qed.Html
import Qed.Lang
import Qed.Json
import Qed.Proto
import Qed.Date

namespace Qed

structure Field {α : Type} (p : α → Prop) where
  val : α
  ok  : p val

@[reducible, inline] instance {α : Type} {p : α → Prop} : Qed.Lang.QedVal (Field p) α := ⟨Field.val⟩
@[simp] theorem QedVal.val_field {α : Type} {p : α → Prop} (f : Field p) :
    Qed.Lang.QedVal.val f = f.val := rfl

@[reducible] instance {α : Type} {p : α → Prop} : CoeOut (Field p) α := ⟨Field.val⟩
@[reducible] instance {α msg : Type} {p : α → Prop} [Coe α (Html msg)] : CoeHTCT (Field p) (Html msg) := ⟨fun f => (f.val : Html msg)⟩
@[reducible] instance {α : Type} {p : α → Prop} : CoeHTCT (Option (Field p)) (Option α) := ⟨Option.map Field.val⟩
instance {α : Type} {p : α → Prop} [ToString α] : ToString (Field p) := ⟨fun f => toString f.val⟩
instance {α : Type} {p : α → Prop} [BEq α] : BEq (Field p) := ⟨fun a b => a.val == b.val⟩
instance {α : Type} {p : α → Prop} [BEq α] [LawfulBEq α] : LawfulBEq (Field p) where
  eq_of_beq {a b} h := by
    cases a; cases b
    have hv := eq_of_beq (α := α) h
    subst hv; rfl
  rfl {a} := beq_self_eq_true a.val
instance {α : Type} {p : α → Prop} [DecidableEq α] : DecidableEq (Field p) :=
  fun ⟨a, _⟩ ⟨b, _⟩ => if h : a = b then isTrue (by cases h; rfl) else isFalse (by intro heq; injection heq; exact h ‹_›)

instance {α : Type} {p : α → Prop} [ToJson α] : ToJson (Field p) := ⟨fun f => toJson f.val⟩
instance {α : Type} {p : α → Prop} [DecidablePred p] [FromJson α] : FromJson (Field p) :=
  ⟨fun j => do let a ← (fromJson j : Except String α); if h : p a then .ok ⟨a, h⟩ else .error "failed field refinement"⟩
instance {α : Type} {p : α → Prop} [DecidablePred p] [LawfulJson α] : LawfulJson (Field p) where
  depthBound := LawfulJson.depthBound α
  depth_toJson f := LawfulJson.depth_toJson f.val
  fromJson_toJson f := by
    rcases f with ⟨val, hok⟩
    change (fromJson (toJson val) : Except String α).bind
      (fun a => if h : p a then Except.ok (Field.mk a h) else Except.error _) = Except.ok (Field.mk val hok)
    rw [LawfulJson.fromJson_toJson val]; dsimp only [bind, Except.bind]; rw [dif_pos hok]
instance {α : Type} {p : α → Prop} [ToJson α] [NonNullJson α] : NonNullJson (Field p) :=
  ⟨fun f => NonNullJson.toJson_ne_null f.val⟩

instance {α : Type} {p : α → Prop} [ToProto α] : ToProto (Field p) where
  toProtoVal f := ToProto.toProtoVal f.val

instance {α : Type} {p : α → Prop} [DecidablePred p] [FromProto α] : FromProto (Field p) where
  fromProtoVal w := do
    let a ← FromProto.fromProtoVal (α := α) w
    if h : p a then .ok ⟨a, h⟩ else .error "protobuf: failed field refinement"

instance {α : Type} {p : α → Prop} [DecidablePred p] [LawfulProto α] : LawfulProto (Field p) :=
  .ofScalar fun ⟨val, hok⟩ => by
    dsimp only [ToProto.toProtoVal, FromProto.fromProtoVal, bind, Except.bind]
    rw [LawfulProto.fromProtoVal_toProtoVal val]
    dsimp only
    rw [dif_pos hok]

end Qed
