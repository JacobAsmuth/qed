import Tests.Native.Harness
import Examples.LiveRoom
import Qed.Server.Http
import Qed.Socket.Basic

open Qed
open Qed.Server
open Qed.Server.Http

namespace Tests.Native.WebSocket

/-! ## Pure Native Lean RFC 6455 + Qed Mux WebSocket Test Client -/

private def encodeClientWsFrame (opcode : UInt8) (payload : ByteArray) : ByteArray := Id.run do
  let len := payload.size
  let mask : Array UInt8 := #[0x37, 0xFA, 0x21, 0x3D]
  let mut out := ByteArray.empty
  out := out.push (0x80 ||| (opcode &&& 0x0F))
  if len < 126 then
    out := out.push (0x80 ||| UInt8.ofNat len)
  else if len < 65536 then
    out := out.push (0x80 ||| 126)
    out := out.push (UInt8.ofNat ((len >>> 8) &&& 0xFF))
    out := out.push (UInt8.ofNat (len &&& 0xFF))
  else
    out := out.push (0x80 ||| 127)
    for shift in [56, 48, 40, 32, 24, 16, 8, 0] do
      out := out.push (UInt8.ofNat ((len >>> shift) &&& 0xFF))
  for m in mask do out := out.push m
  for i in [0 : len] do
    out := out.push (payload[i]! ^^^ mask[i % 4]!)
  return out

private def decodeServerWsFrame (buf : ByteArray) : Option (UInt8 × ByteArray × ByteArray) := Id.run do
  if buf.size < 2 then return none
  let opcode := buf[0]! &&& 0x0F
  let mut len := (buf[1]! &&& 0x7F).toNat
  let mut off := 2
  if len == 126 then
    if buf.size < 4 then return none
    len := ((buf[2]!).toNat <<< 8) ||| (buf[3]!).toNat
    off := 4
  else if len == 127 then
    if buf.size < 10 then return none
    let mut n := 0
    for i in [2 : 10] do n := (n <<< 8) ||| (buf[i]!).toNat
    len := n
    off := 10
  if buf.size < off + len then return none
  return some (opcode, buf.extract off (off + len), buf.extract (off + len) buf.size)

structure WsClient where
  handle : UInt64
  bufRef : IO.Ref ByteArray

private def WsClient.sendBin (ws : WsClient) (payload : ByteArray) : IO Unit := do
  discard <| Prim.outboundWriteAll ws.handle (encodeClientWsFrame 0x02 payload)

private partial def WsClient.recvMux (ws : WsClient) (maxReads : Nat := 12) : IO (Option WsMuxFrame) := do
  let rec loop : Nat → IO (Option WsMuxFrame)
    | 0 => return none
    | fuel + 1 => do
        let buf ← ws.bufRef.get
        if let some (op, payload, rest) := decodeServerWsFrame buf then
          ws.bufRef.set rest
          if op == 0x09 then
            discard <| Prim.outboundWriteAll ws.handle (encodeClientWsFrame 0x0A payload)
            return ← loop fuel
          else if op == 0x02 then
            match WsMuxFrame.decode payload with
            | .ok mf => return some mf
            | .error _ => return none
          else
            return ← loop fuel
        match ← Prim.outboundReadSome ws.handle 16384 with
        | .error _ => return none
        | .ok chunk =>
            if chunk.size == 0 then return none
            ws.bufRef.set (buf ++ chunk)
            loop fuel
  loop maxReads

private def WsClient.close (ws : WsClient) : IO Unit := do
  try discard <| Prim.outboundWriteAll ws.handle (encodeClientWsFrame 0x08 ByteArray.empty) catch _ => pure ()
  Prim.outboundRelease ws.handle 0

private def connectWs (port : UInt16) (wsPath : String) (origin? : Option String)
    (extraHdrs : Array (String × String) := #[]) : IO (Except String (Nat × String × Option WsClient)) := do
  let keyB64 := "dGhlIHNhbXBsZSBub25jZQ=="
  match ← Prim.outboundAcquire 0 "127.0.0.1" port 0 (fun _ => false) with
  | .error e => return .error e
  | .ok (hNat, _) =>
      let handle := hNat.toUInt64
      let mut req := s!"GET {wsPath} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: {keyB64}\r\nSec-WebSocket-Version: 13\r\n"
      if let some o := origin? then req := req ++ s!"Origin: {o}\r\n"
      for (k, v) in extraHdrs do req := req ++ s!"{k}: {v}\r\n"
      req := req ++ "\r\n"
      match ← Prim.outboundWriteAll handle req.toUTF8 with
      | .error e => Prim.outboundRelease handle 0; return .error e
      | .ok () =>
          match (← readHeadUntilCrlfCrlf handle 16).bind fun (buf, _) => (parseHttpResp buf).toOption with
          | none => Prim.outboundRelease handle 0; return .error "truncated WS handshake response"
          | some resp =>
              let accept := (resp.header? "sec-websocket-accept").getD ""
              if resp.status != 101 then
                Prim.outboundRelease handle 0
                return .ok (resp.status, accept, none)
              let bufRef ← IO.mkRef resp.body
              return .ok (resp.status, accept, some { handle, bufRef })

private def withWsConn (c : TestChecker) (who : String) (port : UInt16) (origin : String)
    (extraHdrs : Array (String × String) := #[]) (k : String → WsClient → IO Unit) : IO Unit := do
  c.expectOk s!"{who} WS connect" (← connectWs port "/_qed/ws/Hub" (some origin) extraHdrs) fun
    | (st, _, none)      => c.checkEq s!"{who} WS upgrade returns 101" st 101
    | (st, acc, some ws) =>
        try c.checkEq s!"{who} WS upgrade returns 101" st 101; k acc ws
        finally ws.close

def run : IO Bool := do
  let c ← mkChecker "websockets"
  let some dir ← buildDevApp "Examples.LiveRoom"
    | c.check "buildDevApp Examples.LiveRoom" false; return ← c.finish

  checkLeakGate c "Examples.LiveRoom" #[
    "LiveRoom.Hub.initState",
    "LiveRoom.Hub.dispatchM",
    "LiveRoom.Hub.wsDispatchM"
  ]

  let authSecret := "ws-test-secret-key"
  let aliceTok ← signSessionToken authSecret "alice"
  let bobTok ← signSessionToken authSecret "bob"
  withNativeServer c "LiveRoom native server healthy" dir #[
    ("QED_WORKERS", some "2"),
    ("QED_AUTH_SECRET", some authSecret)
  ] (dev := true) fun srv => do
    let sameOrigin := s!"http://127.0.0.1:{srv.port}"

    -- 1. CSWSH cross-origin & missing-origin rejection
    c.expectOk "CSWSH cross-origin check"
      (← connectWs srv.port "/_qed/ws/Hub" (some "https://evil.example.com") #[("Authorization", s!"Bearer {aliceTok}")]) fun (st, _, _) =>
        c.checkEq "CSWSH cross-origin WS upgrade rejected 403" st 403

    c.expectOk "cross-site Sec-Fetch-Site check"
      (← connectWs srv.port "/_qed/ws/Hub" none #[("Sec-Fetch-Site", "cross-site"), ("Authorization", s!"Bearer {aliceTok}")]) fun (st, _, _) =>
        c.checkEq "cross-site Sec-Fetch-Site WS upgrade rejected 403" st 403

    -- 2. Valid RFC 6455 handshake + Sec-WebSocket-Accept verification
    let wantAccept := (wsComputeAccept "dGhlIHNhbXBsZSBub25jZQ==").getD ""
    let hubRpc (fn : String) (body : ByteArray := ByteArray.empty) (tok? : Option String := none) :=
      httpRpc srv.port "Hub" fn body tok?
    withWsConn c "alice" srv.port sameOrigin #[("Authorization", s!"Bearer {aliceTok}")] fun accA wsA => do
      c.checkEq "RFC 6455 Sec-WebSocket-Accept matches" accA wantAccept

      -- Subscribe alice to room 1
      wsA.sendBin (WsMuxFrame.encode (.sub 1 "room" (Qed.Proto.encode (1 : Nat))))
      match ← wsA.recvMux with
      | some (.joinOk sid _) => c.checkEq "alice joinOk subId=1" sid 1
      | other => c.check "alice received joinOk" false (toString (other.isSome))

      -- Connect bob and subscribe to room 1
      withWsConn c "bob" srv.port sameOrigin #[("Authorization", s!"Bearer {bobTok}")] fun _ wsB => do
        wsB.sendBin (WsMuxFrame.encode (.sub 2 "room" (Qed.Proto.encode (1 : Nat))))
        match ← wsB.recvMux with
        | some (.joinOk sid _) => c.checkEq "bob joinOk subId=2" sid 2
        | _ => c.check "bob received joinOk" false

        -- Verify online count == 2
        c.checkRpcProto "onlineCount == 2" (← hubRpc "onlineCount") (2 : Nat)

        -- Announce in room 1 via RPC -> both alice and bob receive the ChatMsg broadcast!
        c.checkStatus "announce RPC status 200"
          (← hubRpc "announce" (Qed.Proto.encode ((1 : Nat), "hello live room")) (some aliceTok)) 200

        let checkBroadcast (who : String) (ws : WsClient) (wantSid : UInt32) : IO Unit := do
          match ← ws.recvMux with
          | some (.event sid payload) =>
              c.checkEq s!"{who} received event on subId={wantSid}" sid wantSid
              c.expectOk s!"{who} decode ChatMsg" (Qed.Proto.decode (α := LiveRoom.ChatMsg) payload) fun msg =>
                c.checkEq s!"{who} event body" msg.body.val "hello live room"
          | _ => c.check s!"{who} received broadcast event" false
        checkBroadcast "alice" wsA 1
        checkBroadcast "bob" wsB 2

        -- Transactional `emit` rollback: announce "ROLLBACK" fails with domain error & emits nothing!
        c.checkRpcDomainErr (E := LiveRoom.Hub.announce.Error) (α := LiveRoom.ChatMsg) "ROLLBACK returned domain error"
          ((← hubRpc "announce" (Qed.Proto.encode ((1 : Nat), "ROLLBACK")) (some aliceTok)).map (·.body))

        -- Send a real follow-up message and verify alice's NEXT frame is "after rollback" (not "ROLLBACK"!)
        discard <| hubRpc "announce" (Qed.Proto.encode ((1 : Nat), "after rollback")) (some aliceTok)
        match ← wsA.recvMux with
        | some (.event _ payload) =>
            c.expectOk "decode after-rollback event" (Qed.Proto.decode (α := LiveRoom.ChatMsg) payload) fun msg =>
              c.checkEq "ROLLBACK emit was rolled back; next event is 'after rollback'" msg.body.val "after rollback"
        | _ => c.check "received after-rollback event" false

        -- Unsub bob -> onlineCount drops to 1
        wsB.sendBin (WsMuxFrame.encode (.unsub 2))
        IO.sleep 60
        c.checkRpcProto "onlineCount == 1 after bob unsub" (← hubRpc "onlineCount") (1 : Nat)

    -- 3. Unauthenticated WS client rejected when subscribing to auth-gated `room` channel
    withWsConn c "anon" srv.port sameOrigin #[] fun _ wsAnon => do
      wsAnon.sendBin (WsMuxFrame.encode (.sub 9 "room" (Qed.Proto.encode (1 : Nat))))
      match ← wsAnon.recvMux with
      | some (.err sid _) => c.checkEq "unauth room subscribe rejected with mux err" sid 9
      | _ => c.check "unauth room subscribe rejected" false
  c.finish

end Tests.Native.WebSocket
