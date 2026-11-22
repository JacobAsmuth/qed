import Qed.Json.Lawful
import Qed.Proto

namespace Qed

/-! ## Connection Lifecycle Status (`SocketStatus`) -/

inductive SocketStatus where
  | disconnected
  | connecting
  | connected
  | reconnecting (attempt : Nat)
  | failed (err : String)
deriving Inhabited, DecidableEq, Repr

namespace SocketStatus

@[inline] def isConnected : SocketStatus → Bool
  | .connected => true
  | _          => false

instance : ToString SocketStatus where
  toString
    | .disconnected   => "disconnected"
    | .connecting     => "connecting"
    | .connected      => "connected"
    | .reconnecting n => s!"reconnecting ({n})"
    | .failed e       => s!"failed: {e}"

instance : ToJson SocketStatus := ⟨fun
  | .disconnected   => .obj [("t", .str "disconnected")]
  | .connecting     => .obj [("t", .str "connecting")]
  | .connected      => .obj [("t", .str "connected")]
  | .reconnecting n => .obj [("t", .str "reconnecting"), ("a", toJson n)]
  | .failed e       => .obj [("t", .str "failed"), ("e", .str e)]⟩

instance : FromJson SocketStatus := ⟨fun j =>
  match (j.get? "t").bind (·.str?) with
  | some "disconnected" => .ok .disconnected
  | some "connecting"   => .ok .connecting
  | some "connected"    => .ok .connected
  | some "reconnecting" => ((j.field "a").bind fromJson).map .reconnecting
  | some "failed"       => .ok (.failed (((j.get? "e").bind (·.str?)).getD ""))
  | _ => .error "expected a SocketStatus"⟩

instance : LawfulJson SocketStatus where
  depthBound := 1 + LawfulJson.depthBound Nat
  depth_toJson
    | .disconnected | .connecting | .connected | .failed _ => Nat.le_add_right 1 _
    | .reconnecting n => Nat.add_le_add_left (by simpa [Json.maxObj] using LawfulJson.depth_toJson n) 1
  fromJson_toJson
    | .disconnected | .connecting | .connected | .failed _ => rfl
    | .reconnecting n => by
        change (FromJson.fromJson (toJson n) : Except String Nat).map SocketStatus.reconnecting = _
        rw [LawfulJson.fromJson_toJson n]; rfl

instance : NonNullJson SocketStatus :=
  ⟨fun | .disconnected | .connecting | .connected | .reconnecting _ | .failed _ => nofun⟩

private def encodeFields : SocketStatus → List (Nat × Proto.WireVal)
  | .disconnected   => [(1, .varint 0)]
  | .connecting     => [(1, .varint 1)]
  | .connected      => [(1, .varint 2)]
  | .reconnecting n => [(1, .varint 3), (2, ToProto.toProtoVal n)]
  | .failed e       => [(1, .varint 4), (2, ToProto.toProtoVal e)]

private def decodeFields (fs : List (Nat × Proto.WireVal)) : Except String SocketStatus :=
  match Proto.lookupField 1 fs with
  | some (.varint 0) => .ok .disconnected
  | some (.varint 1) => .ok .connecting
  | some (.varint 2) => .ok .connected
  | some (.varint 3) => (Proto.decodeFieldVal 2 fs "SocketStatus.reconnecting: missing field 2").map .reconnecting
  | some (.varint 4) => (Proto.decodeFieldVal 2 fs "SocketStatus.failed: missing field 2").map .failed
  | _ => .error "protobuf: invalid SocketStatus tag"

instance : ToProto SocketStatus   := .ofFields encodeFields
instance : FromProto SocketStatus := .ofFields decodeFields
instance : LawfulProto SocketStatus :=
  .ofFields encodeFields decodeFields
    (by intro s kw h; cases s <;>
          (simp only [encodeFields, List.mem_cons, List.not_mem_nil, or_false] at h
           rcases h with rfl | rfl <;> simp))
    (by intro s; cases s <;> simp [encodeFields, decodeFields, Proto.decodeFieldVal, Proto.lookupField, Except.map])

end SocketStatus

/-! ## Configurable Reconnect Policy (`Reconnect`) & Bounds Proofs -/

inductive Reconnect where
  | off
  | fixed (delayMs : Nat) (maxRetries : Option Nat := none)
  | backoff (initialMs : Nat := 250) (maxMs : Nat := 30000) (maxRetries : Option Nat := none)
deriving DecidableEq, Repr

namespace Reconnect

/-- Sensible default: exponential backoff starting at 250ms, capped at 30s, unlimited retries. -/
def defaultPolicy : Reconnect := .backoff 250 30000 none

instance : Inhabited Reconnect := ⟨defaultPolicy⟩

/-- Computes the deterministic base reconnect delay in milliseconds for 0-based `attempt`,
    returning `none` when reconnect is disabled or `maxRetries` is exhausted. -/
def nextDelayMs (p : Reconnect) (attempt : Nat) : Option Nat :=
  match p with
  | .off => none
  | .fixed delayMs maxRetries =>
      if maxRetries.all (attempt < ·) then some delayMs else none
  | .backoff initialMs maxMs maxRetries =>
      if maxRetries.all (attempt < ·) then some (min maxMs (initialMs * (2 ^ min attempt 20))) else none

theorem nextDelayMs_off (attempt : Nat) :
    Reconnect.off.nextDelayMs attempt = none := rfl

theorem nextDelayMs_exhausted_fixed (delayMs limit attempt : Nat) (h : limit ≤ attempt) :
    (Reconnect.fixed delayMs (some limit)).nextDelayMs attempt = none := by
  simp [nextDelayMs, Nat.not_lt.2 h]

theorem nextDelayMs_exhausted_backoff (initialMs maxMs limit attempt : Nat) (h : limit ≤ attempt) :
    (Reconnect.backoff initialMs maxMs (some limit)).nextDelayMs attempt = none := by
  simp [nextDelayMs, Nat.not_lt.2 h]

theorem nextDelayMs_backoff_le_max (initialMs maxMs : Nat) (maxRetries : Option Nat)
    (attempt d : Nat)
    (h : (Reconnect.backoff initialMs maxMs maxRetries).nextDelayMs attempt = some d) :
    d ≤ maxMs := by
  simp only [nextDelayMs] at h; split at h <;> cases h; exact Nat.min_le_left _ _

end Reconnect

/-! ## Multiplexed Binary Wire Frame Codec (`WsMuxFrame`) & Round-Trip Proof -/

/-- Canonical binary frames exchanged over `/_qed/ws/<Server>`.
    Client → Server: `sub` (0x01), `unsub` (0x02), `send` (0x03).
    Server → Client: `joinOk` (0x11), `event` (0x12), `err` (0x13), `closed` (0x14). -/
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
  ByteArray.mk #[
    op,
    (sid >>> 24).toUInt8,
    (sid >>> 16).toUInt8,
    (sid >>> 8).toUInt8,
    sid.toUInt8
  ]

private def mkU16BE (v : UInt16) : ByteArray :=
  ByteArray.mk #[
    (v >>> 8).toUInt8,
    v.toUInt8
  ]

private def readU32BE (ba : ByteArray) (off : Nat) : Option UInt32 :=
  if h : off + 3 < ba.size then
    let b0 : UInt32 := (ba[off]'(by omega)).toUInt32
    let b1 : UInt32 := (ba[off + 1]'(by omega)).toUInt32
    let b2 : UInt32 := (ba[off + 2]'(by omega)).toUInt32
    let b3 : UInt32 := (ba[off + 3]'(by omega)).toUInt32
    some (b0 * 16777216 + b1 * 65536 + b2 * 256 + b3)
  else none

private def readU16BE (ba : ByteArray) (off : Nat) : Option UInt16 :=
  if h : off + 1 < ba.size then
    let b0 : UInt16 := (ba[off]'(by omega)).toUInt16
    let b1 : UInt16 := (ba[off + 1]'(by omega)).toUInt16
    some (b0 * 256 + b1)
  else none

def encode : WsMuxFrame → ByteArray
  | .sub sid ch params =>
      let chBytes := ch.toUTF8
      mkMuxHdr 0x01 sid ++ mkU16BE (UInt16.ofNat chBytes.size) ++ chBytes ++ params
  | .unsub sid =>
      mkMuxHdr 0x02 sid
  | .send sid payload =>
      mkMuxHdr 0x03 sid ++ payload
  | .joinOk sid snap =>
      mkMuxHdr 0x11 sid ++ snap
  | .event sid payload =>
      mkMuxHdr 0x12 sid ++ payload
  | .err sid msg =>
      mkMuxHdr 0x13 sid ++ msg.toUTF8
  | .closed sid reason =>
      mkMuxHdr 0x14 sid ++ reason.toUTF8

@[inline] private def decodeBody (op : UInt8) (sid : UInt32) (rest : ByteArray) :
    Except String WsMuxFrame :=
  match op with
  | 0x01 => do
      let some chLen := readU16BE rest 0 | throw "truncated ws sub channel length"
      let n := chLen.toNat
      if 2 + n ≤ rest.size then
        match String.fromUTF8? (rest.extract 2 (2 + n)) with
        | some ch => return .sub sid ch (rest.extract (2 + n) rest.size)
        | none    => throw "invalid UTF-8 in ws channel name"
      else throw "truncated ws sub channel name"
  | 0x02 =>
      if rest.size == 0 then return .unsub sid
      else throw "unexpected trailing bytes in ws unsub frame"
  | 0x03 => return .send sid rest
  | 0x11 => return .joinOk sid rest
  | 0x12 => return .event sid rest
  | 0x13 => (String.fromUTF8? rest).elim (throw "invalid UTF-8 in ws error frame") (return .err sid ·)
  | 0x14 => (String.fromUTF8? rest).elim (throw "invalid UTF-8 in ws close frame") (return .closed sid ·)
  | _ => throw s!"unknown ws mux opcode {op}"

def decode (ba : ByteArray) : Except String WsMuxFrame := do
  if h0 : 5 ≤ ba.size then
    let op := ba[0]'(by omega)
    let some sid := readU32BE ba 1 | throw "truncated ws mux sub_id"
    decodeBody op sid (ba.extract 5 ba.size)
  else
    throw "ws mux frame shorter than 5-byte header"

private theorem u32_be_roundtrip (v : UInt32) :
    (v >>> 24).toUInt8.toUInt32 * (16777216 : UInt32) +
    (v >>> 16).toUInt8.toUInt32 * (65536 : UInt32) +
    (v >>> 8).toUInt8.toUInt32 * (256 : UInt32) +
    v.toUInt8.toUInt32 = v := by
  apply UInt32.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
  have hv : v.toNat < 4294967296 := v.toBitVec.isLt
  change (_ : UInt32).toNat = v.toNat
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt8.toNat_toUInt32,
    UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.reduceToNat, Nat.shiftRight_eq_div_pow,
    Nat.reduceMod, Nat.reducePow]
  omega

private theorem byteArray_extract_append_right (a b : ByteArray) :
    (a ++ b).extract a.size (a ++ b).size = b := by
  apply ByteArray.ext
  apply Array.ext
  · simp [ByteArray.size_append]
  · intro i h1 h2
    have h1' : i < ((a ++ b).extract a.size (a ++ b).size).size := h1
    change ((a ++ b).extract a.size (a ++ b).size)[i]'h1' = b[i]'h2
    rw [ByteArray.getElem_extract, ByteArray.getElem_append_right (by omega)]
    have hsub : a.size + i - a.size = i := by omega
    simp only [hsub]
    rfl

private theorem mkMuxHdr_size (op : UInt8) (sid : UInt32) :
    (mkMuxHdr op sid).size = 5 := rfl

private theorem readU32BE_mkMuxHdr (op : UInt8) (sid : UInt32) (rest : ByteArray) :
    readU32BE (mkMuxHdr op sid ++ rest) 1 = some sid := by
  unfold readU32BE
  have hlen : 1 + 3 < (mkMuxHdr op sid ++ rest).size := by
    rw [ByteArray.size_append, mkMuxHdr_size]; omega
  rw [dif_pos hlen]; dsimp only; congr 1
  repeat rw [ByteArray.getElem_append_left (by rw [mkMuxHdr_size]; omega)]
  exact u32_be_roundtrip sid

private theorem decode_mkMuxHdr (op : UInt8) (sid : UInt32) (rest : ByteArray) :
    decode (mkMuxHdr op sid ++ rest) = decodeBody op sid rest := by
  unfold decode
  have h5 : 5 ≤ (mkMuxHdr op sid ++ rest).size := by rw [ByteArray.size_append, mkMuxHdr_size]; omega
  rw [dif_pos h5, readU32BE_mkMuxHdr]; dsimp only
  rw [ByteArray.getElem_append_left (by simp [mkMuxHdr_size])]
  have hrest := byteArray_extract_append_right (mkMuxHdr op sid) rest
  rw [mkMuxHdr_size] at hrest; rw [hrest]; rfl

theorem decode_encode_unsub (sid : UInt32) :
    decode (encode (.unsub sid)) = .ok (.unsub sid) := by
  simpa [encode, ByteArray.append_empty, decodeBody] using decode_mkMuxHdr 0x02 sid ByteArray.empty

theorem decode_encode_send (sid : UInt32) (payload : ByteArray) :
    decode (encode (.send sid payload)) = .ok (.send sid payload) :=
  decode_mkMuxHdr 0x03 sid payload

theorem decode_encode_joinOk (sid : UInt32) (snap : ByteArray) :
    decode (encode (.joinOk sid snap)) = .ok (.joinOk sid snap) :=
  decode_mkMuxHdr 0x11 sid snap

theorem decode_encode_event (sid : UInt32) (payload : ByteArray) :
    decode (encode (.event sid payload)) = .ok (.event sid payload) :=
  decode_mkMuxHdr 0x12 sid payload

end WsMuxFrame

/-! ## Collision-Free Channel Topic Key (`wsTopicKey`) & Injectivity Proof -/

/-- Canonical, collision-free topic key for a typed WebSocket channel subscription (`LawfulProto`). -/
def wsTopicKey {Params : Type} [ToProto Params] (channel : String) (params : Params) : String :=
  channel ++ ":" ++ Proto.encodeHex (Proto.encode params)

theorem wsTopicKey_injective {Params : Type} [LawfulProto Params]
    (channel : String) (a b : Params)
    (h : wsTopicKey channel a = wsTopicKey channel b) : a = b :=
  Proto.encodeHex_encode_injective Proto.encode Proto.decode Proto.decode_encode h

end Qed
