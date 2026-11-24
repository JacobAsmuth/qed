import Tests.Native.Harness
import Examples.LiveRoom
import Qed.Server.Http
import Qed.Socket.Basic
open Qed Qed.Server Qed.Server.Http

namespace Tests.Native.WebSocket

private def encodeClientWsFrame (opcode : UInt8) (payload : ByteArray) : ByteArray := Id.run do
  let (len, mask) := (payload.size, (#[0x37, 0xFA, 0x21, 0x3D] : Array UInt8))
  let mut out := ByteArray.empty.push (0x80 ||| (opcode &&& 0x0F))
  if len < 126 then out := out.push (0x80 ||| UInt8.ofNat len)
  else if len < 65536 then out := Net.pushU16BE (out.push (0x80 ||| 126)) len
  else out := Net.pushU32BE (Net.pushU32BE (out.push (0x80 ||| 127)) (len >>> 32)) len
  for m in mask do out := out.push m
  for i in [0 : len] do out := out.push (payload[i]! ^^^ mask[i % 4]!)
  return out
private def decodeServerWsFrame (buf : ByteArray) : Option (UInt8 × ByteArray × ByteArray) := do
  if buf.size < 2 then failure
  let (opcode, b1) := (buf[0]! &&& 0x0F, (buf[1]! &&& 0x7F).toNat)
  let (len, off) ← if b1 < 126 then some (b1, 2) else if b1 == 126 then (Net.readU16BE buf 2).map (·, 4)
    else (Net.readU32BE buf 2).bind fun hi => (Net.readU32BE buf 6).map fun lo => ((hi <<< 32) ||| lo, 10)
  if buf.size < off + len then failure
  return (opcode, buf.extract off (off + len), buf.extract (off + len) buf.size)

structure WsClient where
  handle : UInt64
  bufRef : IO.Ref ByteArray
private def WsClient.sendBin (ws : WsClient) (payload : ByteArray) : IO Unit := discard <| Prim.outboundWriteAll ws.handle (encodeClientWsFrame 0x02 payload)
private def WsClient.close (ws : WsClient) : IO Unit := do
  try discard <| Prim.outboundWriteAll ws.handle (encodeClientWsFrame 0x08 ByteArray.empty) catch _ => pure (); Prim.outboundRelease ws.handle 0
private def WsClient.recvMux (ws : WsClient) (maxReads : Nat := 12) : IO (Option WsMuxFrame) := do
  for _ in [0 : maxReads] do
    let buf ← ws.bufRef.get
    if let some (op, payload, rest) := decodeServerWsFrame buf then
      ws.bufRef.set rest
      if op == 0x09 then discard <| Prim.outboundWriteAll ws.handle (encodeClientWsFrame 0x0A payload)
      else if op == 0x02 then return (WsMuxFrame.decode payload).toOption
    else match ← Prim.outboundReadSome ws.handle 16384 with | .ok c => if c.size == 0 then return none else ws.bufRef.set (buf ++ c) | .error _ => return none
  return none

private def connectWs (port : UInt16) (wsPath : String) (origin? : Option String) (extraHdrs : Array (String × String) := #[]) : IO (Except String (Nat × String × Option WsClient)) := do
  match ← Prim.outboundAcquire 0 "127.0.0.1" port 0 (fun _ => false) with
  | .error e => return .error e
  | .ok (hNat, _) =>
      let handle := hNat.toUInt64
      let origLine := origin?.map (fun o => s!"Origin: {o}\r\n") |>.getD ""
      let hdrLines := extraHdrs.foldl (init := "") fun acc (k, v) => acc ++ s!"{k}: {v}\r\n"
      let req := s!"GET {wsPath} HTTP/1.1\r\nHost: 127.0.0.1:{port}\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\n{origLine}{hdrLines}\r\n"
      match ← Prim.outboundWriteAll handle req.toUTF8 with
      | .error e => Prim.outboundRelease handle 0; return .error e
      | .ok () =>
          match (← readHeadUntilCrlfCrlf handle 16).bind fun (buf, _) => (parseHttpResp buf).toOption with
          | none => Prim.outboundRelease handle 0; return .error "truncated WS handshake response"
          | some resp =>
              let acc := (resp.header? "sec-websocket-accept").getD ""
              if resp.status != 101 then Prim.outboundRelease handle 0; return .ok (resp.status, acc, none)
              return .ok (resp.status, acc, some { handle, bufRef := ← IO.mkRef resp.body })

private def withWsConn (c : TestChecker) (who : String) (port : UInt16) (origin : String) (extraHdrs : Array (String × String) := #[]) (k : String → WsClient → IO Unit) : IO Unit := do
  c.expectOk s!"{who} WS connect" (← connectWs port "/_qed/ws/Hub" (some origin) extraHdrs) fun
    | (st, _, none) => c.checkEq s!"{who} WS upgrade returns 101" st 101 | (st, acc, some ws) => try c.checkEq s!"{who} WS upgrade returns 101" st 101; k acc ws finally ws.close

def run : IO Bool := do
  let c ← mkChecker "websockets"
  withDevApp c "Examples.LiveRoom" fun dir => do
    checkLeakGate c "Examples.LiveRoom" #["LiveRoom.Hub.initState", "LiveRoom.Hub.dispatchM", "LiveRoom.Hub.wsDispatchM", "LiveRoom.Hub.wsProject"]
    let authSecret := "ws-test-secret-key"; let (aliceTok, bobTok) := (← signSessionToken authSecret "alice", ← signSessionToken authSecret "bob")
    withNativeServer c "LiveRoom native server healthy" dir #[("QED_WORKERS", some "2"), ("QED_AUTH_SECRET", some authSecret)] (dev := true) fun srv => do
      let sameOrigin := s!"http://127.0.0.1:{srv.port}"
      let hubRpc (fn : String) (body := ByteArray.empty) (tok? : Option String := none) := httpRpc srv.port "Hub" fn body tok?
      let subJoin (who : String) (ws : WsClient) (sid : UInt32) : IO Unit := do
        ws.sendBin (WsMuxFrame.encode (.sub sid "room" (Qed.Proto.encode (1 : Nat))))
        match ← ws.recvMux with | some (.joinOk got _) => c.checkEq s!"{who} joinOk subId={sid}" got sid | other => c.check s!"{who} received joinOk" false (toString other.isSome)
      let expectEvent (label : String) (ws : WsClient) (wantSid? : Option UInt32) (wantBody : String) : IO Unit := do
        match ← ws.recvMux with
        | some (.event sid payload) =>
            if let some wantSid := wantSid? then c.checkEq s!"{label} subId={wantSid}" sid wantSid
            c.expectOk s!"{label} decode ChatMsg" (Qed.Proto.decode (α := LiveRoom.ChatMsg) payload) fun msg => c.checkEq s!"{label} body" msg.body.val wantBody
        | _ => c.check s!"{label} received event" false
      for (lbl, orig?, hdrs) in [("CSWSH cross-origin WS upgrade rejected 403", some "https://evil.example.com", #[("Authorization", s!"Bearer {aliceTok}")]),
          ("cross-site Sec-Fetch-Site WS upgrade rejected 403", none, #[("Sec-Fetch-Site", "cross-site"), ("Authorization", s!"Bearer {aliceTok}")])] do
        c.expectOk lbl (← connectWs srv.port "/_qed/ws/Hub" orig? hdrs) fun (st, _, _) => c.checkEq lbl st 403
      withWsConn c "alice" srv.port sameOrigin #[("Authorization", s!"Bearer {aliceTok}")] fun accA wsA => do
        c.checkEq "RFC 6455 Sec-WebSocket-Accept matches" accA ((wsComputeAccept "dGhlIHNhbXBsZSBub25jZQ==").getD ""); subJoin "alice" wsA 1
        withWsConn c "bob" srv.port sameOrigin #[("Authorization", s!"Bearer {bobTok}")] fun _ wsB => do
          subJoin "bob" wsB 2; c.checkRpcProto "onlineCount == 2" (← hubRpc "onlineCount") (2 : Nat)
          c.checkStatus "announce RPC status 200" (← hubRpc "announce" (Qed.Proto.encode ((1 : Nat), "hello live room")) (some aliceTok)) 200
          expectEvent "alice broadcast" wsA (some 1) "hello live room"; expectEvent "bob broadcast" wsB (some 2) "hello live room"
          c.checkRpcDomainErr (E := LiveRoom.Hub.announce.Error) (α := LiveRoom.ChatMsg) "ROLLBACK returned domain error" ((← hubRpc "announce" (Qed.Proto.encode ((1 : Nat), "ROLLBACK")) (some aliceTok)).map (·.body))
          discard <| hubRpc "announce" (Qed.Proto.encode ((1 : Nat), "after rollback")) (some aliceTok)
          expectEvent "after-rollback" wsA none "after rollback"
          expectEvent "after-rollback bob" wsB none "after rollback"
          -- Per-viewer projected channel: alice sees the secret, bob receives redacted `none`!
          wsA.sendBin (WsMuxFrame.encode (.sub 3 "secretFeed" (Qed.Proto.encode (1 : Nat))))
          match ← wsA.recvMux with | some (.joinOk got _) => c.checkEq "alice secretFeed joinOk" got 3 | _ => c.check "alice secretFeed joinOk" false
          wsB.sendBin (WsMuxFrame.encode (.sub 4 "secretFeed" (Qed.Proto.encode (1 : Nat))))
          match ← wsB.recvMux with | some (.joinOk got _) => c.checkEq "bob secretFeed joinOk" got 4 | _ => c.check "bob secretFeed joinOk" false
          c.checkStatus "broadcastSecret RPC status 200" (← hubRpc "broadcastSecret" (Qed.Proto.encode ((1 : Nat), ("Casino", "bob"))) (some aliceTok)) 200
          match ← wsA.recvMux with
          | some (.event sid payload) =>
              c.checkEq "alice projected subId=3" sid 3
              c.expectOk "alice decode SecretView" (Qed.Proto.decode (α := LiveRoom.SecretView) payload) fun v =>
                c.checkEq "alice sees unredacted secret" v.secret (some "Casino")
          | _ => c.check "alice received projected SecretView" false
          match ← wsB.recvMux with
          | some (.event sid payload) =>
              c.checkEq "bob projected subId=4" sid 4
              c.expectOk "bob decode SecretView" (Qed.Proto.decode (α := LiveRoom.SecretView) payload) fun v =>
                c.checkEq "bob receives redacted secret (none)" v.secret none
          | _ => c.check "bob received projected SecretView" false
          wsB.sendBin (WsMuxFrame.encode (.unsub 2)); IO.sleep 60
          c.checkRpcProto "onlineCount == 1 after bob unsub" (← hubRpc "onlineCount") (1 : Nat)
      withWsConn c "anon" srv.port sameOrigin #[] fun _ wsAnon => do
        wsAnon.sendBin (WsMuxFrame.encode (.sub 9 "room" (Qed.Proto.encode (1 : Nat))))
        match ← wsAnon.recvMux with | some (.err sid _) => c.checkEq "unauth room subscribe rejected with mux err" sid 9 | _ => c.check "unauth room subscribe rejected" false
  c.finish

end Tests.Native.WebSocket
