import Qed.Json.Lawful
import Qed.Proto

namespace Qed

namespace Internal
inductive TaggedCase (α : Type) where
  | unit (jTag : String) (pTag : Nat) | payload (a : α) | failed (e : String)

structure TaggedCodec (T α : Type) where mk ::
  (typeName payloadTag payloadField : String) (payloadPTag failedPTag : Nat)
  (split : T → TaggedCase α) (ofUnitJson : String → Option T) (ofUnitProto : Nat → Option T)
  (mkPayload : α → T) (mkFailed : String → T)
  (sound : ∀ t, match split t with
    | .unit j p => ofUnitJson j = some t ∧ ofUnitProto p = some t ∧ j ≠ payloadTag ∧ j ≠ "failed" ∧ p ≠ payloadPTag ∧ p ≠ failedPTag
    | .payload a => mkPayload a = t | .failed e => mkFailed e = t)
  (tagsDistinct : payloadTag ≠ "failed" ∧ payloadField ≠ "t" ∧ payloadPTag ≠ failedPTag)

namespace TaggedCodec
variable {T α : Type} (c : TaggedCodec T α)
@[instance_reducible] def toJsonInst [ToJson α] : ToJson T := ⟨fun t => match c.split t with
  | .unit j _ => .obj [("t", .str j)] | .payload a => .obj [("t", .str c.payloadTag), (c.payloadField, toJson a)] | .failed e => .obj [("t", .str "failed"), ("e", .str e)]⟩
@[instance_reducible] def fromJsonInst [FromJson α] : FromJson T := ⟨fun j => match j.strAt? "t" with
  | some s => if s == c.payloadTag then ((j.field c.payloadField).bind fromJson).map c.mkPayload
              else if s == "failed" then .ok (c.mkFailed (j.strAtD "e")) else (c.ofUnitJson s).elim (.error s!"expected a {c.typeName}") .ok
  | none => .error s!"expected a {c.typeName}"⟩
theorem nonNullInst [ToJson α] : @NonNullJson T c.toJsonInst := @NonNullJson.mk T c.toJsonInst fun t => by
  change (match c.split t with | .unit j _ => Json.obj [("t", .str j)] | .payload a => .obj [("t", .str c.payloadTag), (c.payloadField, toJson a)] | .failed e => .obj [("t", .str "failed"), ("e", .str e)]) ≠ Json.null
  cases c.split t <;> nofun
@[instance_reducible] def lawfulJsonInst [LawfulJson α] : LawfulJson T where
  toToJson := c.toJsonInst; toFromJson := c.fromJsonInst; depthBound := 1 + LawfulJson.depthBound α
  depth_toJson t := by
    change Json.depth (match c.split t with | .unit .. => _ | .payload .. => _ | .failed .. => _) ≤ _
    cases c.split t with | unit _ _ | failed _ => exact Nat.le_add_right 1 _ | payload a => exact Nat.add_le_add_left (by simpa [Json.maxObj, Json.depth] using LawfulJson.depth_toJson a) 1
  fromJson_toJson t := by
    have hs := c.sound t; change c.fromJsonInst.fromJson (c.toJsonInst.toJson t) = .ok t
    unfold toJsonInst fromJsonInst; dsimp only; cases h : c.split t <;> (rw [h] at hs; dsimp only at hs)
    · simp [Json.strAt?, Json.get?, Json.field, Except.toOption, Json.str?, hs.2.2.1, hs.2.2.2.1, hs.1]
    · simp only [Json.strAt?, Json.get?, Json.field, Except.toOption, Json.str?, List.foldl, beq_self_eq_true, ↓reduceIte, beq_eq_false_iff_ne.2 c.tagsDistinct.2.1, Bool.false_eq_true, Option.bind_some, Option.elim]
      change (fromJson (toJson _) : Except String α).map c.mkPayload = _; rw [LawfulJson.fromJson_toJson]; exact congrArg Except.ok hs
    · simp [Json.strAt?, Json.strAtD, Json.get?, Json.field, Except.toOption, Json.str?, c.tagsDistinct.1.symm, hs]
def encodeFields [ToProto α] (t : T) : List (Nat × Proto.WireVal) := match c.split t with
  | .unit _ p => [(1, .varint p)] | .payload a => [(1, .varint c.payloadPTag), (2, ToProto.toProtoVal a)] | .failed e => [(1, .varint c.failedPTag), (2, ToProto.toProtoVal e)]
def decodeFields [FromProto α] (fs : List (Nat × Proto.WireVal)) : Except String T := match Proto.lookupField 1 fs with
  | some (.varint n) => if n == c.payloadPTag then (Proto.decodeFieldVal 2 fs s!"{c.typeName}: missing field 2").map c.mkPayload
                        else if n == c.failedPTag then (Proto.decodeFieldVal 2 fs s!"{c.typeName}.failed: missing field 2").map c.mkFailed
                        else (c.ofUnitProto n).elim (.error s!"protobuf: invalid {c.typeName} tag") .ok
  | _ => .error s!"protobuf: invalid {c.typeName} tag"
@[instance_reducible] def toProtoInst [ToProto α] : ToProto T := .ofFields c.encodeFields
@[instance_reducible] def fromProtoInst [FromProto α] : FromProto T := .ofFields c.decodeFields
@[instance_reducible] def lawfulProtoInst [LawfulProto α] : LawfulProto T := .ofFields c.encodeFields c.decodeFields
  (by intro t kw h; unfold encodeFields at h; cases h' : c.split t <;> rw [h'] at h <;> (simp only [List.mem_cons, List.not_mem_nil, or_false] at h; try rcases h with rfl | rfl; all_goals ((try subst h); exact Nat.zero_lt_succ _)))
  (by intro t; have hs := c.sound t; dsimp only [encodeFields, decodeFields]; cases h : c.split t <;> (rw [h] at hs; dsimp only at hs)
      · simp [Proto.lookupField, beq_eq_false_iff_ne.2 hs.2.2.2.2.1, beq_eq_false_iff_ne.2 hs.2.2.2.2.2, hs.2.1]
      · simp [Proto.decodeFieldVal, Proto.lookupField, Except.map, hs]
      · simp [Proto.decodeFieldVal, Proto.lookupField, beq_eq_false_iff_ne.2 c.tagsDistinct.2.2.symm, Except.map, hs])
end TaggedCodec
end Internal

inductive SocketStatus where
  | disconnected | connecting | connected | reconnecting (attempt : Nat) | failed (err : String)
deriving Inhabited, DecidableEq, Repr

namespace SocketStatus
@[inline] def isConnected : SocketStatus → Bool | .connected => true | _ => false
instance : ToString SocketStatus := ⟨fun
  | .disconnected => "disconnected" | .connecting => "connecting" | .connected => "connected"
  | .reconnecting n => s!"reconnecting ({n})" | .failed e => s!"failed: {e}"⟩
private def codec : Internal.TaggedCodec SocketStatus Nat where
  typeName := "SocketStatus"; payloadTag := "reconnecting"; payloadField := "a"; payloadPTag := 3; failedPTag := 4
  split | .disconnected => .unit "disconnected" 0 | .connecting => .unit "connecting" 1 | .connected => .unit "connected" 2 | .reconnecting n => .payload n | .failed e => .failed e
  ofUnitJson | "disconnected" => some .disconnected | "connecting" => some .connecting | "connected" => some .connected | _ => none
  ofUnitProto | 0 => some .disconnected | 1 => some .connecting | 2 => some .connected | _ => none
  mkPayload := .reconnecting; mkFailed := .failed
  sound | .disconnected | .connecting | .connected => by decide | .reconnecting _ | .failed _ => rfl
  tagsDistinct := by decide
instance : ToJson SocketStatus := codec.toJsonInst
instance : FromJson SocketStatus := codec.fromJsonInst
instance : LawfulJson SocketStatus := codec.lawfulJsonInst
instance : NonNullJson SocketStatus := codec.nonNullInst
instance : ToProto SocketStatus := codec.toProtoInst
instance : FromProto SocketStatus := codec.fromProtoInst
instance : LawfulProto SocketStatus := codec.lawfulProtoInst
end SocketStatus

inductive Reconnect where
  | off
  | fixed (delayMs : Nat) (maxRetries : Option Nat := none)
  | backoff (initialMs : Nat := 250) (maxMs : Nat := 30000) (maxRetries : Option Nat := none)
deriving DecidableEq, Repr

namespace Reconnect
def defaultPolicy : Reconnect := .backoff 250 30000 none
instance : Inhabited Reconnect := ⟨defaultPolicy⟩
def nextDelayMs : Reconnect → Nat → Option Nat
  | .off, _ => none
  | .fixed delayMs maxRetries, attempt => if maxRetries.all (attempt < ·) then some delayMs else none
  | .backoff initialMs maxMs maxRetries, attempt =>
      if maxRetries.all (attempt < ·) then some (min maxMs (initialMs * (2 ^ min attempt 20))) else none
theorem nextDelayMs_off (attempt : Nat) : Reconnect.off.nextDelayMs attempt = none := rfl
theorem nextDelayMs_exhausted_fixed (delayMs limit attempt : Nat) (h : limit ≤ attempt) :
    (Reconnect.fixed delayMs (some limit)).nextDelayMs attempt = none := by simp [nextDelayMs, Nat.not_lt.2 h]
theorem nextDelayMs_exhausted_backoff (initialMs maxMs limit attempt : Nat) (h : limit ≤ attempt) :
    (Reconnect.backoff initialMs maxMs (some limit)).nextDelayMs attempt = none := by simp [nextDelayMs, Nat.not_lt.2 h]
theorem nextDelayMs_backoff_le_max (initialMs maxMs : Nat) (maxRetries : Option Nat) (attempt d : Nat)
    (h : (Reconnect.backoff initialMs maxMs maxRetries).nextDelayMs attempt = some d) : d ≤ maxMs := by
  simp only [nextDelayMs] at h; split at h <;> cases h; exact Nat.min_le_left _ _
end Reconnect

/-- Canonical binary frames exchanged over `/_qed/ws/<Server>`. -/
inductive WsMuxFrame where
  | sub    (subId : UInt32) (channel : String) (params : ByteArray)
  | unsub  (subId : UInt32)
  | send   (subId : UInt32) (payload : ByteArray)
  | joinOk (subId : UInt32) (snapshot : ByteArray)
  | event  (subId : UInt32) (payload : ByteArray)
  | err    (subId : UInt32) (message : String)
  | closed (subId : UInt32) (reason : String)
deriving DecidableEq

namespace WsMuxFrame
private def mkMuxHdr (op : UInt8) (sid : UInt32) : ByteArray :=
  ByteArray.mk #[op, (sid >>> 24).toUInt8, (sid >>> 16).toUInt8, (sid >>> 8).toUInt8, sid.toUInt8]
def encode : WsMuxFrame → ByteArray
  | .sub sid ch params => let b := ch.toUTF8; let n := UInt16.ofNat b.size
      mkMuxHdr 0x01 sid ++ ByteArray.mk #[(n >>> 8).toUInt8, n.toUInt8] ++ b ++ params
  | .unsub sid => mkMuxHdr 0x02 sid | .send sid payload => mkMuxHdr 0x03 sid ++ payload
  | .joinOk sid snap => mkMuxHdr 0x11 sid ++ snap | .event sid payload => mkMuxHdr 0x12 sid ++ payload
  | .err sid msg => mkMuxHdr 0x13 sid ++ msg.toUTF8 | .closed sid reason => mkMuxHdr 0x14 sid ++ reason.toUTF8
@[inline] private def decodeBody (op : UInt8) (sid : UInt32) (rest : ByteArray) : Except String WsMuxFrame :=
  match op with
  | 0x01 => if h : 2 ≤ rest.size then
      let n := (rest[0]'(by omega)).toNat * 256 + (rest[1]'(by omega)).toNat
      if 2 + n ≤ rest.size then
        (String.fromUTF8? (rest.extract 2 (2 + n))).elim (.error "invalid UTF-8 in ws channel name")
          fun ch => .ok (.sub sid ch (rest.extract (2 + n) rest.size))
      else .error "truncated ws sub channel name"
    else .error "truncated ws sub channel length"
  | 0x02 => if rest.size == 0 then .ok (.unsub sid) else .error "unexpected trailing bytes in ws unsub frame"
  | 0x03 => .ok (.send sid rest) | 0x11 => .ok (.joinOk sid rest) | 0x12 => .ok (.event sid rest)
  | 0x13 => (String.fromUTF8? rest).elim (.error "invalid UTF-8 in ws error frame") (.ok ∘ .err sid)
  | 0x14 => (String.fromUTF8? rest).elim (.error "invalid UTF-8 in ws close frame") (.ok ∘ .closed sid)
  | _    => .error s!"unknown ws mux opcode {op}"
def decode (ba : ByteArray) : Except String WsMuxFrame :=
  if h0 : 5 ≤ ba.size then
    let sid : UInt32 := (ba[1]'(by omega)).toUInt32 * (16777216 : UInt32) + (ba[2]'(by omega)).toUInt32 * (65536 : UInt32) +
                        (ba[3]'(by omega)).toUInt32 * (256 : UInt32) + (ba[4]'(by omega)).toUInt32
    decodeBody (ba[0]'(by omega)) sid (ba.extract 5 ba.size)
  else .error "ws mux frame shorter than 5-byte header"
private theorem u32_be_roundtrip (v : UInt32) :
    (v >>> 24).toUInt8.toUInt32 * (16777216 : UInt32) + (v >>> 16).toUInt8.toUInt32 * (65536 : UInt32) +
    (v >>> 8).toUInt8.toUInt32 * (256 : UInt32) + v.toUInt8.toUInt32 = v := by
  apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq; have hv : v.toNat < 4294967296 := v.toBitVec.isLt
  change (_ : UInt32).toNat = v.toNat
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32, UInt32.toNat_toUInt8,
    UInt32.toNat_shiftRight, UInt32.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod, Nat.reducePow]; omega
private theorem byteArray_extract_append_right (a b : ByteArray) : (a ++ b).extract a.size (a ++ b).size = b :=
  ByteArray.ext <| Array.ext (by simp [ByteArray.size_append]) fun i h1 h2 => by
    change ((a ++ b).extract a.size (a ++ b).size)[i]'h1 = b[i]'h2
    rw [ByteArray.getElem_extract, ByteArray.getElem_append_right (by omega)]; simp only [Nat.add_sub_cancel_left]
private theorem decode_mkMuxHdr (op : UInt8) (sid : UInt32) (rest : ByteArray) :
    decode (mkMuxHdr op sid ++ rest) = decodeBody op sid rest := by
  have hsz : (mkMuxHdr op sid).size = 5 := rfl
  unfold decode; rw [dite_eq_left (by rw [ByteArray.size_append, hsz]; omega)]
  repeat rw [ByteArray.getElem_append_left (by rw [hsz]; omega)]
  have hrest := byteArray_extract_append_right (mkMuxHdr op sid) rest
  rw [hsz] at hrest; rw [hrest, show (mkMuxHdr op sid)[0] = op from rfl]; exact congrArg (decodeBody op · rest) (u32_be_roundtrip sid)
theorem decode_encode_unsub (sid : UInt32) : decode (encode (.unsub sid)) = .ok (.unsub sid) := by
  simpa [encode, ByteArray.append_empty, decodeBody] using decode_mkMuxHdr 0x02 sid ByteArray.empty
theorem decode_encode_send (sid : UInt32) (payload : ByteArray) : decode (encode (.send sid payload)) = .ok (.send sid payload) := decode_mkMuxHdr 0x03 sid payload
theorem decode_encode_joinOk (sid : UInt32) (snap : ByteArray) : decode (encode (.joinOk sid snap)) = .ok (.joinOk sid snap) := decode_mkMuxHdr 0x11 sid snap
theorem decode_encode_event (sid : UInt32) (payload : ByteArray) : decode (encode (.event sid payload)) = .ok (.event sid payload) := decode_mkMuxHdr 0x12 sid payload
end WsMuxFrame

def wsTopicKey {Params : Type} [ToProto Params] (channel : String) (params : Params) : String :=
  channel ++ ":" ++ Proto.encodeHex (Proto.encode params)
theorem wsTopicKey_injective {Params : Type} [LawfulProto Params] (channel : String) (a b : Params)
    (h : wsTopicKey channel a = wsTopicKey channel b) : a = b :=
  Proto.encodeHex_encode_injective Proto.encode Proto.decode Proto.decode_encode h
end Qed
