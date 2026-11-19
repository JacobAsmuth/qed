namespace Qed.Server.Prim

/-! ## Trusted Native Server FFI Boundary (`Qed.Server.Prim`)
    Mirrors `Qed.Dom` on the client: this is the **sole** server module permitted by
    `Js.VerifyEnv` to declare `@[extern]` native bindings (implemented in `rust/qed_server`),
    and `Js.VerifyEnv.verifyNoServerLeakInClient` guarantees none of these symbols can
    ever be linked into a client JavaScript bundle. -/

opaque StateBoxPointed : NonemptyType.{0}

/-- Thread-safe `RwLock` shared state container (`lean_mark_mt`-marked) for
    serialized atomic updates under write-lock and concurrent multi-core reads. -/
def StateBox (_ : Type) : Type := StateBoxPointed.type

instance {σ : Type} : Nonempty (StateBox σ) := StateBoxPointed.property

@[extern "qed_server_state_new"]
opaque mkStateBox {σ : Type} (init : σ) : IO (StateBox σ)

@[extern "qed_server_state_read"]
opaque atomicRead {σ α : Type} (box : @& StateBox σ) (f : σ → α) : IO α

@[extern "qed_server_state_modify"]
opaque atomicModify {σ α : Type} (box : @& StateBox σ) (f : σ → σ × α) : IO α

opaque StaticDirPointed : NonemptyType.{0}

/-- Directory descriptor (`dirfd`) anchored at startup for symlink-free `openat2`/`openat` static reads. -/
def StaticDir : Type := StaticDirPointed.type

instance : Nonempty StaticDir := StaticDirPointed.property

@[extern "qed_server_open_static_dir"]
opaque openStaticDir (path : @& String) : IO StaticDir

/-- Reads a regular file beneath `dir` using `openat2(RESOLVE_BENEATH | RESOLVE_NO_SYMLINKS)`
    on Linux (or `openat` + `O_NOFOLLOW` segment walk on macOS). Returns `some (fileSize, mtimeMs, bytes)`,
    where `bytes` is empty when `headOnly != 0`. -/
@[extern "qed_server_read_static_file"]
opaque readStaticFile (dir : @& StaticDir) (relPath : @& String) (headOnly : UInt8) :
    IO (Option (Nat × Nat × ByteArray))

/-- Reads an OS environment variable (`none` if unset). -/
@[extern "qed_server_get_env"]
opaque getEnv (name : @& String) : IO (Option String)

/-- Current Unix epoch timestamp in milliseconds. -/
@[extern "qed_server_now_ms"]
opaque nowMs : IO UInt64

/-- Generates `2 * numBytes` lowercase hex characters from OS CSPRNG (`getrandom`). -/
@[extern "qed_server_random_hex"]
opaque randomHex (numBytes : UInt32) : IO String

/-- Computes a 32-byte HMAC-SHA256 digest. -/
@[extern "qed_server_hmac_sha256"]
opaque hmacSha256 (key : @& ByteArray) (msg : @& ByteArray) : IO ByteArray

/-- Verifies an HMAC-SHA256 digest in compiler-barriered constant time (`hmac::Mac::verify_slice` / `subtle`). -/
@[extern "qed_server_hmac_sha256_verify"]
opaque hmacSha256Verify (key : @& ByteArray) (msg : @& ByteArray) (sig : @& ByteArray) : IO Bool

/-- Signs `msg` using RSASSA-PKCS1-v1_5 SHA-256 (`RS256`) with a PEM-encoded RSA private key. -/
@[extern "qed_server_rsa_sha256_sign"]
opaque rsaSha256Sign (pemPrivateKey : @& String) (msg : @& ByteArray) : IO (Except String ByteArray)

/-- Acquires a pooled or fresh TCP/TLS (`rustls`) outbound stream. When `ssrfGuard != 0`,
    validates every DNS-resolved IP against Lean's verified `isBlockedIp` before `connect`.
    Returns `(handleId, wasReusedFlag)`. -/
@[extern "qed_server_outbound_acquire"]
opaque outboundAcquire
    (isTls : UInt8)
    (host : @& String)
    (port : UInt16)
    (ssrfGuard : UInt8)
    (isBlockedIp : @& (ByteArray → Bool)) :
    IO (Except String (Nat × Nat))

@[extern "qed_server_outbound_write_all"]
opaque outboundWriteAll (handle : UInt64) (data : @& ByteArray) : IO (Except String Unit)

@[extern "qed_server_outbound_read_some"]
opaque outboundReadSome (handle : UInt64) (maxBytes : UInt32) : IO (Except String ByteArray)

@[extern "qed_server_outbound_release"]
opaque outboundRelease (handle : UInt64) (keepAlive : UInt8) : IO Unit

/-- Broadcasts a pre-encoded Protobuf event payload across all multi-core worker threads to
    every WebSocket subscription matching `topicKey` (`<channel>:<hex(params)>`). -/
@[extern "qed_server_ws_broadcast"]
opaque wsBroadcast (topicKey : @& String) (payload : @& ByteArray) : IO Unit

/-- Decision returned by Lean's verified HTTP/1.1 head handler to the Rust socket loop.
    All constructor fields are object-typed so the FFI never relies on scalar field layout. -/
inductive HttpHeadAction (Req Ctx : Type) where
  | doneClose     (respWire : ByteArray)
  | doneKeepAlive (respWire : ByteArray)
  | needBodyClose (contentLen : Nat) (req : Req)
  | needBodyKeep  (contentLen : Nat) (req : Req)
  | wsUpgrade     (respWire : ByteArray) (wsCtx : Ctx)

/-- Subscription table mutation emitted by Lean's verified WebSocket frame/mux handler. -/
inductive WsSubOp where
  | addSub    (subId : Nat) (topic channel : String) (params : ByteArray)
  | removeSub (subId : Nat)

/-- Result of processing buffered WebSocket bytes in Lean. All fields are object-typed. -/
structure WsStepOut (Frag : Type) where
  consumed  : Nat
  outWire   : ByteArray
  closeFlag : Nat
  fragState : Frag
  subOps    : Array WsSubOp

/-- Starts the multi-core `epoll`/`kqueue` socket loop + blocking handler pool in Rust.
    All HTTP/1.1 parsing/formatting, static path/MIME policy, CSRF/CSWSH checks, RFC 6455
    WebSocket framing/SHA-1/reassembly, and mux routing execute in Lean via the 4 callbacks. -/
@[extern "qed_server_run"]
opaque serveNative {Req Ctx Frag : Type}
    (host : @& String)
    (port : UInt16)
    (numWorkers : UInt32)
    (initFrag : Frag)
    (onHead : ByteArray → String → IO (HttpHeadAction Req Ctx))
    (onBody : Req → ByteArray → String → IO ByteArray)
    (onWsBytes : Ctx → ByteArray → Frag → Array (Nat × String × ByteArray) → IO (WsStepOut Frag))
    (onWsLeave : Ctx → String → ByteArray → IO Unit) :
    IO UInt32

end Qed.Server.Prim
