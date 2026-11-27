import Qed.Collection
import Qed.Html
import Qed.Router.Basic
import Qed.Json.Lawful
import Qed.Proto.Lawful

namespace Qed

@[inline] def decidableEqOfLawfulBEq {α : Type} [BEq α] [LawfulBEq α] : DecidableEq α :=
  fun a b => if h : a == b then isTrue (eq_of_beq h) else isFalse fun heq => h (heq ▸ beq_self_eq_true a)

structure Field {α : Type} (p : α → Prop) where
  val : α
  ok  : p val

section FieldInstances
variable {α : Type} {p : α → Prop}
@[reducible] instance : CoeOut (Field p) α := ⟨Field.val⟩
@[reducible, inline] instance : Qed.Lang.QedVal (Field p) α := ⟨Field.val⟩
@[simp] theorem QedVal.val_field (f : Field p) : Qed.Lang.QedVal.val f = f.val := rfl
@[reducible] instance {msg : Type} [Coe α (Html msg)] : CoeHTCT (Field p) (Html msg) := ⟨fun f => (f.val : Html msg)⟩
@[reducible] instance : CoeHTCT (Option (Field p)) (Option α) := ⟨Option.map Field.val⟩
instance [ToString α] : ToString (Field p) := ⟨fun f => toString f.val⟩
@[simp] theorem toString_field [ToString α] (f : Field p) : toString f = toString f.val := rfl
instance [BEq α] : BEq (Field p) := ⟨fun a b => a.val == b.val⟩
instance [Repr α] : Repr (Field p) := ⟨fun f n => reprPrec f.val n⟩
instance [BEq α] [LawfulBEq α] : LawfulBEq (Field p) where
  eq_of_beq {a b} h := by cases a; cases b; cases eq_of_beq (α := α) h; rfl
  rfl {a} := beq_self_eq_true a.val
instance [DecidableEq α] : DecidableEq (Field p) := fun ⟨a, _⟩ ⟨b, _⟩ =>
  if h : a = b then isTrue (by cases h; rfl) else isFalse fun heq => h (congrArg Field.val heq)
@[inline] def Field.parse? {α : Type} (p : α → Prop) [DecidablePred p] (a : α) : Option (Field p) :=
  if h : p a then some ⟨a, h⟩ else none
@[inline] def Field.parse {α : Type} (p : α → Prop) [DecidablePred p] (err : String) (a : α) : Except String (Field p) :=
  if h : p a then .ok ⟨a, h⟩ else .error err
@[simp] theorem Field.parse?_val {α : Type} {p : α → Prop} [DecidablePred p] (x : Field p) : Field.parse? p x.val = some x :=
  dite_eq_left x.ok
@[simp] theorem Field.parse_val {α : Type} {p : α → Prop} [DecidablePred p] (err : String) (x : Field p) : Field.parse p err x.val = .ok x :=
  dite_eq_left x.ok
instance [ToJson α] : ToJson (Field p) := .ofEquiv Field.val
instance [DecidablePred p] [FromJson α] : FromJson (Field p) := .ofRetract (Field.parse p "failed field refinement")
instance [DecidablePred p] [LawfulJson α] : LawfulJson (Field p) := .ofRetract Field.val (Field.parse p "failed field refinement") (Field.parse_val _)
instance [ToJson α] [NonNullJson α] : NonNullJson (Field p) := ⟨fun f => NonNullJson.toJson_ne_null f.val⟩
instance [ToProto α] : ToProto (Field p) := .ofEquiv Field.val
instance [DecidablePred p] [FromProto α] : FromProto (Field p) := .ofRetract (Field.parse p "protobuf: failed field refinement")
instance [DecidablePred p] [LawfulProto α] : LawfulProto (Field p) := .ofRetract Field.val (Field.parse p "protobuf: failed field refinement") (Field.parse_val _)
@[simp] theorem Proto.encode_field [ToProto α] (f : Field p) : Proto.encode f = Proto.encode f.val := rfl
instance [ToHref α] : ToHref (Field p) := ⟨fun f => ToHref.toUrl f.val⟩
instance [LawfulKey α] : LawfulKey (Field p) where
  toKey f := LawfulKey.toKey f.val
  injective a b h := by cases a; cases b; cases LawfulKey.injective _ _ h; rfl
instance [RouteParam α] [DecidablePred p] : RouteParam (Field p) where
  toSeg f := RouteParam.toSeg f.val
  fromSeg s := (RouteParam.fromSeg s).bind (Field.parse? p)
  round_trip f := by simp [RouteParam.round_trip]
end FieldInstances

def Field.map {α β : Type} {p : α → Prop} {q : β → Prop} (f : α → β)
    (hf : ∀ a, p a → q (f a)) (x : Field p) : Field q :=
  ⟨f x.val, hf x.val x.ok⟩

abbrev Field.length {p : String → Prop} (f : Field p) : Nat := f.val.length
abbrev Field.utf8ByteSize {p : String → Prop} (f : Field p) : Nat := f.val.utf8ByteSize
abbrev Field.toUTF8 {p : String → Prop} (f : Field p) : ByteArray := f.val.toUTF8
abbrev Field.size {p : ByteArray → Prop} (f : Field p) : Nat := f.val.size

@[simp] theorem toUTF8_size (s : String) : s.toUTF8.size = s.utf8ByteSize := Nat.add_zero _
@[simp] theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp [String.fromUTF8?, String.toUTF8, s.isValidUTF8]

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

/-- Unwraps fallible (`Except String α`) or optional (`Option α`) results inside `mapping` `decode` blocks. -/
class MappingUnwrap (α : Type) (β : outParam Type) where
  unwrap : α → Except String β

instance {α : Type} : MappingUnwrap (Except String α) α := ⟨id⟩
instance {α : Type} : MappingUnwrap (Option α) α := ⟨fun | some a => .ok a | none => .error "mapping decode failed"⟩

@[simp] theorem MappingUnwrap.unwrap_ok {α : Type} (a : α) : MappingUnwrap.unwrap (Except.ok a : Except String α) = .ok a := rfl
@[simp] theorem MappingUnwrap.unwrap_error {α : Type} (e : String) : MappingUnwrap.unwrap (Except.error e : Except String α) = .error e := rfl
@[simp] theorem MappingUnwrap.unwrap_some {α : Type} (a : α) : MappingUnwrap.unwrap (some a : Option α) = .ok a := rfl
@[simp] theorem MappingUnwrap.unwrap_none {α : Type} : MappingUnwrap.unwrap (none : Option α) = .error "mapping decode failed" := rfl

/-- Verified bidirectional mapping between a source representation `A` (invariant `pA`)
    and a target representation `B` (invariant `pB`), e.g. plaintext <-> ciphertext,
    bytes <-> Base64, or domain units <-> wire formats. -/
structure Mapping {A B : Type} (pA : A → Prop) (pB : B → Prop) where
  toTarget  : A → B
  toSource  : B → Except String A
  encode_ok : ∀ a, pA a → pB (toTarget a)
  decode_ok : ∀ b a, toSource b = .ok a → pA a
  roundtrip : ∀ a, pA a → toSource (toTarget a) = .ok a

namespace Mapping
variable {A B : Type} {pA : A → Prop} {pB : B → Prop}

def encode (m : Mapping pA pB) (a : A) (ha : pA a := by trivial) : Field pB :=
  ⟨m.toTarget a, m.encode_ok a ha⟩

def encodeField (m : Mapping pA pB) (a : Field pA) : Field pB :=
  Field.map m.toTarget m.encode_ok a

def decode (m : Mapping pA pB) (b : B) : Except String (Field pA) :=
  match h : m.toSource b with
  | .ok a    => .ok ⟨a, m.decode_ok b a h⟩
  | .error e => .error e

theorem decode_encode (m : Mapping pA pB) (a : A) (ha : pA a) :
    m.decode (m.encode a ha).val = .ok ⟨a, ha⟩ := by
  unfold decode encode; split
  · rename_i _ h; cases Except.ok.inj ((m.roundtrip a ha).symm.trans h); rfl
  · rename_i _ h; cases (m.roundtrip a ha).symm.trans h

def comp {A B C : Type} {pA : A → Prop} {pB pB' : B → Prop} {pC : C → Prop}
    (m2 : Mapping pB' pC) (m1 : Mapping pA pB)
    (hCompat : ∀ b, pB b → pB' b := by intro _ h; exact h) : Mapping pA pC where
  toTarget a := m2.toTarget (m1.toTarget a)
  toSource c := (m2.toSource c).bind m1.toSource
  encode_ok a ha := m2.encode_ok _ (hCompat _ (m1.encode_ok a ha))
  decode_ok c a h := by
    cases h2 : m2.toSource c with
    | error _ => simp [h2, Except.bind] at h
    | ok b => simp only [h2, Except.bind] at h; exact m1.decode_ok b a h
  roundtrip a ha := by
    have h2 := m2.roundtrip (m1.toTarget a) (hCompat _ (m1.encode_ok a ha))
    simp only [h2, Except.bind, m1.roundtrip a ha]

theorem decode_ok_of_guard {A : Type} {pA : A → Prop} {dec : ∀ x, Decidable (pA x)} {e : Except String A} {err : String} {a : A}
    (h : (e.bind fun x => @dite _ (pA x) (dec x) (fun _ => Except.ok x) (fun _ => Except.error err)) = Except.ok a) : pA a := by
  cases e with
  | error _ => nomatch h
  | ok a0 =>
      dsimp only [Except.bind] at h
      split at h
      · exact Except.ok.inj h ▸ ‹_›
      · nomatch h

end Mapping

end Qed
