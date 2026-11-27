import Qed.Server.Db.Core

namespace Qed.Server.Prim

/-! ## Trusted Native Server FFI Boundary (`Qed.Server.Prim`)
    Sole server module permitted by `Js.VerifyEnv` to declare `@[extern]` native bindings
    (implemented in `rust/qed_server`) and guaranteed unreachable from client JS bundles. -/

opaque StateBoxPointed : NonemptyType.{0}
def StateBox (_ : Type) : Type := StateBoxPointed.type
instance {σ : Type} : Nonempty (StateBox σ) := StateBoxPointed.property

@[extern "qed_server_state_new"]    opaque mkStateBox   {σ : Type} (init : σ) : IO (StateBox σ)
@[extern "qed_server_state_read"]   opaque atomicRead   {σ α : Type} (box : @& StateBox σ) (f : σ → α) : IO α
@[extern "qed_server_state_modify"] opaque atomicModify {σ α : Type} (box : @& StateBox σ) (f : σ → σ × α) : IO α

opaque StaticDirPointed : NonemptyType.{0}
def StaticDir : Type := StaticDirPointed.type
instance : Nonempty StaticDir := StaticDirPointed.property

@[extern "qed_server_open_static_dir"]  opaque openStaticDir  (path : @& String) : IO StaticDir
@[extern "qed_server_read_static_file"] opaque readStaticFile (dir : @& StaticDir) (relPath : @& String) (headOnly : UInt8) : IO (Option (Nat × Nat × ByteArray))

-- Environment, clock, CSPRNG, crypto (`ring`) & DEFLATE gzip
@[extern "qed_server_get_env"]            opaque getEnv           (name : @& String) : IO (Option String)
@[extern "qed_server_now_ms"]             opaque nowMs            : IO UInt64
def nowSec : IO Nat := return (← nowMs).toNat / 1000
@[extern "qed_server_random_hex"]         opaque randomHex        (numBytes : UInt32) : IO String
@[extern "qed_server_random_bytes"]       opaque randomBytes      (numBytes : UInt32) : IO ByteArray
@[extern "qed_server_const_eq"]           opaque constEq          (a b : @& ByteArray) : IO Bool
@[extern "qed_server_hmac_sha256"]        opaque hmacSha256       (key msg : @& ByteArray) : IO ByteArray
@[extern "qed_server_hmac_sha256_verify"] opaque hmacSha256Verify (key msg sig : @& ByteArray) : IO Bool
@[extern "qed_server_rsa_sha256_sign"]    opaque rsaSha256Sign    (pemPrivateKey : @& String) (msg : @& ByteArray) : IO (Except String ByteArray)
@[extern "qed_server_rsa_sha256_verify"]  opaque rsaSha256Verify  (pemPrivateKey : @& String) (msg sig : @& ByteArray) : IO Bool
@[extern "qed_server_rsa_jwk_verify"]     opaque rsaJwkVerify     (nBytes eBytes msg sig : @& ByteArray) : IO Bool
@[extern "qed_server_ec_p256_jwk_verify"] opaque ecP256JwkVerify  (xBytes yBytes msg sig : @& ByteArray) : IO Bool
@[extern "qed_server_ec_p256_keygen"]     opaque ecP256Keygen     : IO (Except String (ByteArray × ByteArray × ByteArray))
@[extern "qed_server_ec_p256_sign"]       opaque ecP256Sign       (pkcs8Der msg : @& ByteArray) : IO (Except String ByteArray)
@[extern "qed_server_sha256"]             opaque sha256           (data : @& ByteArray) : IO ByteArray
@[extern "qed_server_pbkdf2_sha256"]      opaque pbkdf2HmacSha256 (password salt : @& ByteArray) (iterations : UInt32) : IO ByteArray
@[extern "qed_server_aead_encrypt"]       opaque aeadEncrypt      (key aad pt : @& ByteArray) : IO (Except String ByteArray)
@[extern "qed_server_aead_decrypt"]       opaque aeadDecrypt      (key aad ct : @& ByteArray) : IO (Except String ByteArray)
@[extern "qed_server_gzip_compress"]      opaque gzipCompress     (data : @& ByteArray) : IO ByteArray

-- Pooled SQLite WAL queries & pinned transactions
@[extern "qed_server_sqlite_exec"]        opaque sqliteExec       (path sql : @& String) (params : @& Array Qed.Server.Db.SqlVal) : IO (Except String Qed.Server.Db.DbResult)
@[extern "qed_server_sqlite_ddl"]         opaque sqliteDdl        (path ddl : @& String) : IO (Except String Unit)
@[extern "qed_server_sqlite_tx_begin"]    opaque sqliteTxBegin    (path : @& String) : IO (Except String UInt64)
@[extern "qed_server_sqlite_tx_exec"]     opaque sqliteTxExec     (txId : UInt64) (sql : @& String) (params : @& Array Qed.Server.Db.SqlVal) : IO (Except String Qed.Server.Db.DbResult)
@[extern "qed_server_sqlite_tx_commit"]   opaque sqliteTxCommit   (txId : UInt64) : IO (Except String Unit)
@[extern "qed_server_sqlite_tx_rollback"] opaque sqliteTxRollback (txId : UInt64) : IO Unit

-- Outbound TCP/TLS (`rustls`) pool & test TCP listener
@[extern "qed_server_outbound_acquire"]     opaque outboundAcquire    (isTls : UInt8) (host : @& String) (port : UInt16) (ssrfGuard : UInt8) (isBlockedIp : @& (ByteArray → Bool)) : IO (Except String (Nat × Nat))
@[extern "qed_server_outbound_write_all"]   opaque outboundWriteAll   (handle : UInt64) (data : @& ByteArray) : IO (Except String Unit)
@[extern "qed_server_outbound_read_some"]   opaque outboundReadSome   (handle : UInt64) (maxBytes : UInt32) : IO (Except String ByteArray)
@[extern "qed_server_outbound_upgrade_tls"] opaque outboundUpgradeTls (handle : UInt64) (host : @& String) : IO (Except String Unit)
@[extern "qed_server_outbound_is_alive"]    opaque outboundIsAlive    (handle : UInt64) : IO Bool
@[extern "qed_server_outbound_release"]     opaque outboundRelease    (handle : UInt64) (keepAlive : UInt8) : IO Unit
@[extern "qed_server_free_port"]            opaque freePort           : IO UInt16
@[extern "qed_server_tcp_listen"]           opaque tcpListen          (port : UInt16) : IO (Except String (UInt64 × UInt16))
@[extern "qed_server_tcp_accept"]           opaque tcpAccept          (listenerId : UInt64) (timeoutMs : UInt32) : IO (Except String UInt64)
@[extern "qed_server_tcp_close_listener"]   opaque tcpCloseListener   (listenerId : UInt64) : IO Unit
@[extern "qed_server_ws_broadcast"]         opaque wsBroadcast        (topicKey : @& String) (payload : @& ByteArray) : IO Unit

/-- Decision returned by Lean's verified HTTP/1.1 head handler to the Rust socket loop (all fields object-typed). -/
inductive HttpHeadAction (Req Ctx : Type) where
  | doneClose      (respWire : ByteArray)
  | doneKeepAlive  (respWire : ByteArray)
  | needBodyClose  (contentLen : Nat) (req : Req)
  | needBodyKeep   (contentLen : Nat) (req : Req)
  | wsUpgrade      (respWire : ByteArray) (wsCtx : Ctx)
  | deferBodyClose (contentLen : Nat) (req : Req)
  | deferBodyKeep  (contentLen : Nat) (req : Req)
  | deferHead

inductive WsSubOp where
  | addSub    (subId : Nat) (topic channel : String) (params : ByteArray)
  | removeSub (subId : Nat)

structure WsStepOut (Frag : Type) where
  consumed  : Nat
  outWire   : ByteArray
  closeFlag : Nat
  fragState : Frag
  subOps    : Array WsSubOp

@[extern "qed_server_run"]
opaque serveNative {Req Ctx Frag : Type}
    (host : @& String) (port : UInt16) (numWorkers : UInt32) (initFrag : Frag)
    (onHead : ByteArray → String → Nat → IO (HttpHeadAction Req Ctx))
    (onBody : Req → ByteArray → String → IO ByteArray)
    (onWsBytes : Ctx → ByteArray → Frag → Array (Nat × String × ByteArray) → IO (WsStepOut Frag))
    (onWsLeave : Ctx → String → ByteArray → IO Unit)
    (onWsProject : Option (Ctx → String → ByteArray → ByteArray → Option (Option ByteArray))) : IO UInt32

end Qed.Server.Prim
