import Qed.Json.Lawful
import Qed.Proto

namespace Qed

inductive SocketStatus where
  | disconnected | connecting | connected
  | reconnecting (attempt : Nat) | failed (err : String)
deriving Inhabited, DecidableEq, Repr

namespace SocketStatus
@[inline] def isConnected : SocketStatus → Bool | .connected => true | _ => false
instance : ToString SocketStatus := ⟨fun
  | .disconnected => "disconnected" | .connecting => "connecting" | .connected => "connected"
  | .reconnecting n => s!"reconnecting ({n})" | .failed e => s!"failed: {e}"⟩
instance : ToJson SocketStatus := ⟨fun
  | .disconnected => .obj [("t", .str "disconnected")] | .connecting => .obj [("t", .str "connecting")]
  | .connected => .obj [("t", .str "connected")] | .reconnecting n => .obj [("t", .str "reconnecting"), ("a", toJson n)]
  | .failed e => .obj [("t", .str "failed"), ("e", .str e)]⟩
instance : FromJson SocketStatus := ⟨fun j => match j.strAt? "t" with
  | some "disconnected" => .ok .disconnected | some "connecting" => .ok .connecting | some "connected" => .ok .connected
  | some "reconnecting" => ((j.field "a").bind fromJson).map .reconnecting | some "failed" => .ok (.failed (j.strAtD "e"))
  | _ => .error "expected a SocketStatus"⟩
instance : LawfulJson SocketStatus where
  depthBound := 1 + LawfulJson.depthBound Nat
  depth_toJson
    | .disconnected | .connecting | .connected | .failed _ => Nat.le_add_right 1 _
    | .reconnecting n => Nat.add_le_add_left (by simpa [Json.maxObj] using LawfulJson.depth_toJson n) 1
  fromJson_toJson
    | .disconnected | .connecting | .connected | .failed _ => rfl
    | .reconnecting n => by change (FromJson.fromJson (toJson n) : Except String Nat).map SocketStatus.reconnecting = _; rw [LawfulJson.fromJson_toJson n]; rfl
instance : NonNullJson SocketStatus := ⟨fun | .disconnected | .connecting | .connected | .reconnecting _ | .failed _ => nofun⟩
private def encodeFields : SocketStatus → List (Nat × Proto.WireVal)
  | .disconnected => [(1, .varint 0)] | .connecting => [(1, .varint 1)] | .connected => [(1, .varint 2)]
  | .reconnecting n => [(1, .varint 3), (2, ToProto.toProtoVal n)] | .failed e => [(1, .varint 4), (2, ToProto.toProtoVal e)]
private def decodeFields (fs : List (Nat × Proto.WireVal)) : Except String SocketStatus :=
  match Proto.lookupField 1 fs with
  | some (.varint 0) => .ok .disconnected | some (.varint 1) => .ok .connecting | some (.varint 2) => .ok .connected
  | some (.varint 3) => (Proto.decodeFieldVal 2 fs "SocketStatus.reconnecting: missing field 2").map .reconnecting
  | some (.varint 4) => (Proto.decodeFieldVal 2 fs "SocketStatus.failed: missing field 2").map .failed
  | _ => .error "protobuf: invalid SocketStatus tag"
qed_proto_fields% [] (SocketStatus, encodeFields, decodeFields,
  by intro s kw h; cases s <;> (simp only [encodeFields, List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> simp),
  by intro s; cases s <;> simp [encodeFields, decodeFields, Proto.decodeFieldVal, Proto.lookupField, Except.map])
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
    rw [ByteArray.getElem_extract, ByteArray.getElem_append_right (by omega)]; simp only [Nat.add_sub_cancel_left]; rfl
private theorem decode_mkMuxHdr (op : UInt8) (sid : UInt32) (rest : ByteArray) :
    decode (mkMuxHdr op sid ++ rest) = decodeBody op sid rest := by
  have hsz : (mkMuxHdr op sid).size = 5 := rfl
  unfold decode; rw [dif_pos (by rw [ByteArray.size_append, hsz]; omega)]
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
