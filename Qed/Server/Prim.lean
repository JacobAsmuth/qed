namespace Qed.Server.Prim

/-! ## Trusted Native Server FFI Boundary (`Qed.Server.Prim`)
    Mirrors `Qed.Dom` on the client: this is the **sole** server module permitted by
    `Js.VerifyEnv` to declare `@[extern]` C bindings (implemented in `c/qed_server.c`),
    and `Js.VerifyEnv.verifyNoServerLeakInClient` guarantees none of these symbols can
    ever be linked into a client JavaScript bundle. -/

opaque StateBoxPointed : NonemptyType.{0}

/-- Thread-safe `pthread_rwlock_t` shared state container (`lean_mark_mt`-marked) for
    serialized atomic updates under `wrlock` and concurrent multi-core reads under `rdlock`. -/
def StateBox (_ : Type) : Type := StateBoxPointed.type

instance {σ : Type} : Nonempty (StateBox σ) := StateBoxPointed.property

@[extern "qed_server_state_new"]
opaque mkStateBox {σ : Type} (init : σ) : IO (StateBox σ)

@[extern "qed_server_state_read"]
opaque atomicRead {σ α : Type} (box : @& StateBox σ) (f : σ → α) : IO α

@[extern "qed_server_state_modify"]
opaque atomicModify {σ α : Type} (box : @& StateBox σ) (f : σ → σ × α) : IO α

/-- Executes an outbound HTTP/1.1 or HTTPS (OpenSSL TLS) request using the worker's
    keep-alive connection pool. When `ssrfGuard == 1`, resolves DNS and blocks loopback,
    RFC1918 private, link-local, and cloud-metadata IPv4/IPv6 addresses prior to `connect`. -/
@[extern "qed_server_http_call"]
opaque httpCall
    (method : @& String)
    (url : @& String)
    (headers : @& Array (String × String))
    (body : @& ByteArray)
    (ssrfGuard : UInt8) :
    IO (Except String (Nat × ByteArray × Array (String × String)))

/-- Mints an RS256-signed JWT from a GCP Service Account JSON credential and exchanges
    (and caches until 60s before expiry) an OAuth2 Bearer access token for `scope`. -/
@[extern "qed_server_gcp_bearer_token"]
opaque gcpBearerToken (saJson : @& String) (scope : @& String) : IO (Except String String)

/-- Reads an OS environment variable (`none` if unset). -/
@[extern "qed_server_get_env"]
opaque getEnv (name : @& String) : IO (Option String)

/-- Current Unix epoch timestamp in milliseconds. -/
@[extern "qed_server_now_ms"]
opaque nowMs : IO UInt64

/-- Generates `2 * numBytes` lowercase hex characters from OpenSSL `RAND_bytes` CSPRNG. -/
@[extern "qed_server_random_hex"]
opaque randomHex (numBytes : UInt32) : IO String

/-- Computes a 32-byte HMAC-SHA256 digest via OpenSSL `HMAC(EVP_sha256(), ...)`. -/
@[extern "qed_server_hmac_sha256"]
opaque hmacSha256 (key : @& ByteArray) (msg : @& ByteArray) : IO ByteArray

/-- Starts the multi-core `SO_REUSEPORT` + `epoll`/`kqueue` HTTP/1.1 server loop.
    Serves static assets from `staticDir` directly in C and dispatches RPC & SSR requests
    to `handler (method, pathAndQuery, headers, body, clientIp) → (status, contentType, respBody)`. -/
@[extern "qed_server_run"]
opaque serveNative
    (port : UInt16)
    (numWorkers : UInt32)
    (staticDir : @& String)
    (devMode : UInt8)
    (handler : String → String → Array (String × String) → ByteArray → String → IO (Nat × String × ByteArray)) :
    IO UInt32

end Qed.Server.Prim
