import Qed.Field

namespace Qed

/-- Value paired with an erased proof of a server `ensures` postcondition `p val`.
    Encodes identically on the Protobuf wire to `α` (`Proto.encode e = Proto.encode e.val`),
    while `FromProto` re-verifies `p` on untrusted bytes so `LawfulProto` holds zero-trust. -/
abbrev Ensured (α : Type) (p : α → Prop) := Field (α := α) p

@[match_pattern] abbrev Ensured.mk {α : Type} {p : α → Prop} (val : α) (ok : p val) : Ensured α p :=
  Field.mk val ok

abbrev Ensured.val {α : Type} {p : α → Prop} (e : Ensured α p) : α := Field.val e
abbrev Ensured.ok {α : Type} {p : α → Prop} (e : Ensured α p) : p (Field.val e) := Field.ok e

@[simp] theorem Proto.encode_ensured {α : Type} {p : α → Prop} [ToProto α] (e : Ensured α p) :
    Proto.encode e = Proto.encode e.val := rfl

end Qed
