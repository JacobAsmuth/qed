import Qed.Html
import Qed.Json.Lawful
import Qed.Proto.Lawful

namespace Qed

/-- Value paired with an erased proof of a server `ensures` postcondition `p val`.
    Encodes identically on the Protobuf wire to `α` (`Proto.encode e = Proto.encode e.val`),
    while `FromProto` re-verifies `p` on untrusted bytes so `LawfulProto` holds zero-trust. -/
structure Ensured (α : Type) (p : α → Prop) where
  val : α
  ok  : p val

@[reducible] instance {α : Type} {p : α → Prop} : CoeOut (Ensured α p) α := ⟨Ensured.val⟩
@[reducible] instance {α msg : Type} {p : α → Prop} [Coe α (Html msg)] : CoeHTCT (Ensured α p) (Html msg) :=
  ⟨fun e => (e.val : Html msg)⟩
@[reducible] instance {α : Type} {p : α → Prop} : CoeHTCT (Option (Ensured α p)) (Option α) :=
  ⟨Option.map Ensured.val⟩
instance {α : Type} {p : α → Prop} [ToString α] : ToString (Ensured α p) := ⟨fun e => toString e.val⟩
instance {α : Type} {p : α → Prop} [BEq α] : BEq (Ensured α p) := ⟨fun a b => a.val == b.val⟩
instance {α : Type} {p : α → Prop} [Repr α] : Repr (Ensured α p) := ⟨fun e n => reprPrec e.val n⟩
instance {α : Type} {p : α → Prop} [DecidableEq α] : DecidableEq (Ensured α p) :=
  fun ⟨a, _⟩ ⟨b, _⟩ => if h : a = b then isTrue (by cases h; rfl) else isFalse (by intro heq; injection heq; exact h ‹_›)

instance {α : Type} {p : α → Prop} [ToJson α] : ToJson (Ensured α p) := ⟨fun e => toJson e.val⟩
instance {α : Type} {p : α → Prop} [DecidablePred p] [FromJson α] : FromJson (Ensured α p) :=
  ⟨fun j => do let a ← (fromJson j : Except String α); if h : p a then .ok ⟨a, h⟩ else .error "failed RPC ensures postcondition"⟩
instance {α : Type} {p : α → Prop} [DecidablePred p] [LawfulJson α] : LawfulJson (Ensured α p) where
  depthBound := LawfulJson.depthBound α
  depth_toJson e := LawfulJson.depth_toJson e.val
  fromJson_toJson e := by
    rcases e with ⟨val, hok⟩
    change (fromJson (toJson val) : Except String α).bind
      (fun a => if h : p a then Except.ok (Ensured.mk a h) else Except.error _) = Except.ok (Ensured.mk val hok)
    rw [LawfulJson.fromJson_toJson val]; dsimp only [bind, Except.bind]; rw [dif_pos hok]
instance {α : Type} {p : α → Prop} [ToJson α] [NonNullJson α] : NonNullJson (Ensured α p) :=
  ⟨fun e => NonNullJson.toJson_ne_null e.val⟩

instance {α : Type} {p : α → Prop} [ToProto α] : ToProto (Ensured α p) where
  toProtoVal e := ToProto.toProtoVal e.val
  toProtoMsg e := ToProto.toProtoMsg e.val

instance {α : Type} {p : α → Prop} [DecidablePred p] [FromProto α] : FromProto (Ensured α p) where
  fromProtoVal w := do
    let a ← FromProto.fromProtoVal (α := α) w
    if h : p a then .ok ⟨a, h⟩ else .error "protobuf: failed RPC ensures postcondition"
  fromProtoMsg fs := do
    let a ← FromProto.fromProtoMsg (α := α) fs
    if h : p a then .ok ⟨a, h⟩ else .error "protobuf: failed RPC ensures postcondition"

instance {α : Type} {p : α → Prop} [DecidablePred p] [LawfulProto α] : LawfulProto (Ensured α p) where
  msg_tags_pos e := LawfulProto.msg_tags_pos e.val
  fromProtoVal_toProtoVal := fun ⟨val, hok⟩ => by
    dsimp only [ToProto.toProtoVal, FromProto.fromProtoVal, bind, Except.bind]
    rw [LawfulProto.fromProtoVal_toProtoVal val]
    dsimp only
    rw [dif_pos hok]
  fromProtoMsg_toProtoMsg := fun ⟨val, hok⟩ => by
    dsimp only [ToProto.toProtoMsg, FromProto.fromProtoMsg, bind, Except.bind]
    rw [LawfulProto.fromProtoMsg_toProtoMsg val]
    dsimp only
    rw [dif_pos hok]

@[simp] theorem Proto.encode_ensured {α : Type} {p : α → Prop} [ToProto α] (e : Ensured α p) :
    Proto.encode e = Proto.encode e.val := rfl

end Qed
