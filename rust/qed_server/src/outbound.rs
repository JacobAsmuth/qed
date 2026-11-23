use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{self, Read, Write};
use std::net::{IpAddr, SocketAddr, TcpListener, TcpStream, ToSocketAddrs};
use std::os::fd::AsRawFd;
use std::sync::{Arc, Mutex, OnceLock};
use std::time::{Duration, Instant};

use rustls::client::danger::{HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier};
use rustls::pki_types::{CertificateDer, ServerName, UnixTime};
use rustls::{ClientConfig, ClientConnection, DigitallySignedStruct, RootCertStore, SignatureScheme, StreamOwned};

use crate::lean_ffi::*;
use crate::{HandleTable, is_wouldblock, last_errno, lock_unpoison};

const POOL_MAX_PER_HOST: usize = 16;
const POOL_MAX_TOTAL: usize = 128;
const POOL_TTL: Duration = Duration::from_secs(30);
const CONNECT_TIMEOUT: Duration = Duration::from_secs(10);
const MULTI_ADDR_CONNECT_TIMEOUT: Duration = Duration::from_secs(3);
const IO_TIMEOUT: Duration = Duration::from_secs(30);
const READ_BUF_CAP: usize = 65536;

#[derive(Debug)]
struct NoVerify;

impl ServerCertVerifier for NoVerify {
    fn verify_server_cert(&self, _: &CertificateDer<'_>, _: &[CertificateDer<'_>], _: &ServerName<'_>, _: &[u8], _: UnixTime) -> Result<ServerCertVerified, rustls::Error> {
        Ok(ServerCertVerified::assertion())
    }
    fn verify_tls12_signature(&self, _: &[u8], _: &CertificateDer<'_>, _: &DigitallySignedStruct) -> Result<HandshakeSignatureValid, rustls::Error> {
        Ok(HandshakeSignatureValid::assertion())
    }
    fn verify_tls13_signature(&self, _: &[u8], _: &CertificateDer<'_>, _: &DigitallySignedStruct) -> Result<HandshakeSignatureValid, rustls::Error> {
        Ok(HandshakeSignatureValid::assertion())
    }
    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        rustls::crypto::ring::default_provider().signature_verification_algorithms.supported_schemes()
    }
}

static TLS_CONFIG: OnceLock<Arc<ClientConfig>> = OnceLock::new();

fn load_extra_ca_certs(roots: &mut RootCertStore) {
    let path = std::env::var("QED_CA_CERT_FILE")
        .ok()
        .filter(|s| !s.trim().is_empty())
        .or_else(|| std::env::var("SSL_CERT_FILE").ok().filter(|s| !s.trim().is_empty()));
    let Some(path) = path else { return };
    match std::fs::read_to_string(&path) {
        Ok(pem) => {
            let certs: Vec<CertificateDer<'static>> = crate::parse_pem_blocks(&pem, "CERTIFICATE")
                .into_iter()
                .map(CertificateDer::from)
                .collect();
            let (added, ignored) = roots.add_parsable_certificates(certs);
            if added == 0 {
                eprintln!("warning: no valid CA certificates loaded from `{path}` (ignored: {ignored})");
            }
        }
        Err(e) => eprintln!("warning: failed to read CA bundle `{path}`: {e}"),
    }
}

fn tls_config() -> Arc<ClientConfig> {
    TLS_CONFIG.get_or_init(|| {
        let builder = ClientConfig::builder_with_provider(Arc::new(rustls::crypto::ring::default_provider()))
            .with_safe_default_protocol_versions()
            .expect("TLS versions");
        let cfg = if std::env::var("QED_INSECURE_SKIP_TLS_VERIFY").as_deref() == Ok("1") {
            builder.dangerous().with_custom_certificate_verifier(Arc::new(NoVerify)).with_no_client_auth()
        } else {
            let mut roots = RootCertStore::empty();
            roots.extend(webpki_roots::TLS_SERVER_ROOTS.iter().cloned());
            load_extra_ca_certs(&mut roots);
            builder.with_root_certificates(roots).with_no_client_auth()
        };
        Arc::new(cfg)
    }).clone()
}

enum OutStream {
    Plain(TcpStream),
    Tls(Box<StreamOwned<ClientConnection, TcpStream>>),
}

impl OutStream {
    fn raw_fd(&self) -> libc::c_int {
        match self { OutStream::Plain(s) => s.as_raw_fd(), OutStream::Tls(s) => s.sock.as_raw_fd() }
    }
    fn write_all_bytes(&mut self, buf: &[u8]) -> io::Result<()> {
        match self { OutStream::Plain(s) => s.write_all(buf), OutStream::Tls(s) => { s.write_all(buf)?; s.flush() } }
    }
    fn read_some_bytes(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            OutStream::Plain(s) => s.read(buf),
            OutStream::Tls(s) => match s.read(buf) {
                Ok(n) => Ok(n),
                Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => Ok(0),
                Err(e) => Err(e),
            },
        }
    }
}

type PoolKey = (bool, String, u16, bool);

struct OutConn {
    is_tls: bool,
    host: String,
    port: u16,
    ssrf_guarded: bool,
    peer_addr: SocketAddr,
    stream: OutStream,
}

struct PoolEntry {
    conn: OutConn,
    last_used: Instant,
}

struct OutboundPool {
    buckets: HashMap<PoolKey, Vec<PoolEntry>>,
    total: usize,
    max_per_host: usize,
    max_total: usize,
}

impl OutboundPool {
    fn new(max_per_host: usize, max_total: usize) -> Self {
        Self { buckets: HashMap::new(), total: 0, max_per_host, max_total }
    }

    fn pop_entry(&mut self, key: &PoolKey, now: Instant) -> Option<OutConn> {
        let vec = self.buckets.get_mut(key)?;
        while let Some(entry) = vec.pop() {
            self.total -= 1;
            if now.duration_since(entry.last_used) <= POOL_TTL {
                if vec.is_empty() {
                    self.buckets.remove(key);
                }
                return Some(entry.conn);
            }
        }
        self.buckets.remove(key);
        None
    }

    fn sweep_expired(&mut self, now: Instant) {
        let mut removed = 0usize;
        self.buckets.retain(|_, vec| {
            let before = vec.len();
            vec.retain(|e| now.duration_since(e.last_used) <= POOL_TTL);
            removed += before - vec.len();
            !vec.is_empty()
        });
        self.total -= removed;
    }

    fn push(&mut self, conn: OutConn, now: Instant) {
        let key: PoolKey = (conn.is_tls, conn.host.clone(), conn.port, conn.ssrf_guarded);
        if let Some(vec) = self.buckets.get_mut(&key) {
            let before = vec.len();
            vec.retain(|e| now.duration_since(e.last_used) <= POOL_TTL);
            self.total -= before - vec.len();
            while vec.len() >= self.max_per_host {
                vec.remove(0);
                self.total -= 1;
            }
        }
        if self.total >= self.max_total {
            self.sweep_expired(now);
            if self.total >= self.max_total {
                if let Some(oldest_key) = self.buckets.iter()
                    .filter_map(|(k, v)| v.first().map(|e| (k, e.last_used)))
                    .min_by_key(|(_, ts)| *ts)
                    .map(|(k, _)| k.clone())
                {
                    if let Some(vec) = self.buckets.get_mut(&oldest_key) {
                        if !vec.is_empty() {
                            vec.remove(0);
                            self.total -= 1;
                        }
                        if vec.is_empty() {
                            self.buckets.remove(&oldest_key);
                        }
                    }
                }
            }
        }
        self.buckets.entry(key).or_default().push(PoolEntry { conn, last_used: now });
        self.total += 1;
    }
}

static ACTIVE_CONNS: HandleTable<Arc<Mutex<OutConn>>> = HandleTable::new();
static OUTBOUND_POOL: OnceLock<Mutex<OutboundPool>> = OnceLock::new();

thread_local! {
    static READ_SCRATCH: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) };
}

fn global_pool() -> &'static Mutex<OutboundPool> {
    OUTBOUND_POOL.get_or_init(|| Mutex::new(OutboundPool::new(POOL_MAX_PER_HOST, POOL_MAX_TOTAL)))
}

fn socket_is_alive(fd: libc::c_int) -> bool {
    let mut b: u8 = 0;
    let r = unsafe { libc::recv(fd, &mut b as *mut u8 as *mut libc::c_void, 1, libc::MSG_PEEK | libc::MSG_DONTWAIT) };
    // An idle HTTP/1.1 keep-alive or PostgreSQL idle connection must have zero pending bytes (`EAGAIN`/`EWOULDBLOCK`);
    // `r == 0` is peer EOF and `r > 0` indicates an unread TLS `close_notify` alert or stray data.
    r < 0 && is_wouldblock(last_errno())
}

fn pop_pooled(is_tls: bool, host: &str, port: u16, ssrf_guarded: bool) -> Option<OutConn> {
    let key: PoolKey = (is_tls, host.to_owned(), port, ssrf_guarded);
    let pool = global_pool();
    loop {
        let candidate = lock_unpoison(pool).pop_entry(&key, Instant::now());
        let conn = candidate?;
        if socket_is_alive(conn.stream.raw_fd()) {
            return Some(conn);
        }
    }
}

fn insert_active(conn: OutConn) -> u64 {
    ACTIVE_CONNS.insert(Arc::new(Mutex::new(conn)))
}

fn remove_active(handle: u64) -> Option<OutConn> {
    let arc = ACTIVE_CONNS.remove(handle)?;
    Arc::try_unwrap(arc).ok().map(|m| m.into_inner().unwrap_or_else(|e| e.into_inner()))
}

fn wrap_tls(mut sock: TcpStream, host: &str, label: &str) -> Result<OutStream, String> {
    let sni = ServerName::try_from(host.to_owned()).map_err(|_| format!("invalid TLS server name: {host}"))?;
    let mut conn = ClientConnection::new(tls_config(), sni).map_err(|_| "TLS client init failed".to_owned())?;
    conn.complete_io(&mut sock).map_err(|e| format!("{label} handshake failed for {host}: {e}"))?;
    Ok(OutStream::Tls(Box::new(StreamOwned::new(conn, sock))))
}

unsafe fn check_ssrf_lean(addrs: &[SocketAddr], is_blocked_fn: *mut LeanObj) -> Result<(), &'static str> {
    if addrs.is_empty() { return Err("SSRF blocked: empty DNS resolution"); }
    for addr in addrs {
        let ba = match addr.ip() {
            IpAddr::V4(v4) => mk_ba(&v4.octets()),
            IpAddr::V6(v6) => mk_ba(&v6.octets()),
        };
        qed_lean_inc(is_blocked_fn);
        let res = qed_lean_apply_1(is_blocked_fn, ba);
        let blocked = qed_lean_unbox(res) != 0;
        qed_lean_dec(res);
        if blocked { return Err("SSRF blocked: private/internal IP address"); }
    }
    Ok(())
}

fn configure_sock(sock: &TcpStream) {
    let _ = sock.set_nodelay(true);
    let _ = sock.set_read_timeout(Some(IO_TIMEOUT));
    let _ = sock.set_write_timeout(Some(IO_TIMEOUT));
}

fn with_active_conn<T>(handle: u64, f: impl FnOnce(&mut OutStream) -> Result<T, String>) -> Result<T, String> {
    let arc = ACTIVE_CONNS.get(handle).ok_or_else(|| "invalid outbound connection handle".to_owned())?;
    let mut guard = lock_unpoison(&arc);
    f(&mut guard.stream)
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_outbound_acquire(
    is_tls: u8,
    host_obj: *mut LeanObj,
    port: u16,
    ssrf_guard: u8,
    is_blocked_fn: *mut LeanObj,
) -> *mut LeanObj {
    let (want_tls, want_ssrf, host) = (is_tls != 0, ssrf_guard != 0, str_slice(host_obj));
    let res: Result<(u64, usize), String> = (|| {
        if let Some(conn) = pop_pooled(want_tls, host, port, want_ssrf) {
            if want_ssrf {
                check_ssrf_lean(&[conn.peer_addr], is_blocked_fn).map_err(str::to_owned)?;
            }
            return Ok((insert_active(conn), 1));
        }
        let addrs: Vec<SocketAddr> = (host, port).to_socket_addrs()
            .map_err(|e| format!("DNS resolution failed for {host}: {e}"))?.collect();
        if want_ssrf {
            check_ssrf_lean(&addrs, is_blocked_fn).map_err(str::to_owned)?;
        }
        let deadline = Instant::now() + CONNECT_TIMEOUT;
        let multi = addrs.len() > 1;
        let mut last_err = None;
        let (sock, peer_addr) = addrs.iter().find_map(|&addr| {
            let rem = deadline.saturating_duration_since(Instant::now());
            if rem.is_zero() { return None; }
            let timeout = if multi { rem.min(MULTI_ADDR_CONNECT_TIMEOUT) } else { rem };
            match TcpStream::connect_timeout(&addr, timeout) {
                Ok(s) => Some((s, addr)),
                Err(e) => { last_err = Some(e); None }
            }
        }).ok_or_else(|| match last_err {
            Some(e) => format!("TCP connect failed for {host}:{port}: {e}"),
            None => format!("TCP connect failed for {host}:{port}"),
        })?;
        configure_sock(&sock);
        let stream = if want_tls { wrap_tls(sock, host, "TLS")? } else { OutStream::Plain(sock) };
        let conn = OutConn {
            is_tls: want_tls,
            host: host.to_owned(),
            port,
            ssrf_guarded: want_ssrf,
            peer_addr,
            stream,
        };
        Ok((insert_active(conn), 0))
    })();
    mk_io_except(res, |(id, reused)| qed_lean_mk_prod(qed_lean_usize_to_nat(id as usize), qed_lean_usize_to_nat(reused)))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_outbound_write_all(handle: u64, data_obj: *mut LeanObj) -> *mut LeanObj {
    let data = ba_slice(data_obj);
    let res = with_active_conn(handle, |s| s.write_all_bytes(data).map_err(|e| format!("write failed: {e}")));
    mk_io_except(res, |()| qed_lean_box(0))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_outbound_read_some(handle: u64, max_bytes: u32) -> *mut LeanObj {
    let want = (max_bytes as usize).clamp(1, READ_BUF_CAP);
    READ_SCRATCH.with(|cell| {
        let mut buf = cell.borrow_mut();
        if buf.len() < want {
            buf.resize(READ_BUF_CAP, 0);
        }
        let res = with_active_conn(handle, |s| {
            s.read_some_bytes(&mut buf[..want]).map_err(|e| format!("read failed: {e}"))
        });
        mk_io_except(res, |n| mk_ba(&buf[..n]))
    })
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_outbound_upgrade_tls(handle: u64, host_obj: *mut LeanObj) -> *mut LeanObj {
    let host = str_slice(host_obj);
    let res = match remove_active(handle) {
        None => Err("invalid outbound connection handle".to_owned()),
        Some(conn) => match conn.stream {
            OutStream::Tls(_) => {
                ACTIVE_CONNS.insert_at(handle, Arc::new(Mutex::new(conn)));
                Ok(())
            }
            OutStream::Plain(sock) => wrap_tls(sock, host, "STARTTLS").map(|stream| {
                let upgraded = OutConn {
                    is_tls: true,
                    host: conn.host,
                    port: conn.port,
                    ssrf_guarded: conn.ssrf_guarded,
                    peer_addr: conn.peer_addr,
                    stream,
                };
                ACTIVE_CONNS.insert_at(handle, Arc::new(Mutex::new(upgraded)));
            }),
        },
    };
    mk_io_except(res, |()| qed_lean_box(0))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_outbound_is_alive(handle: u64) -> *mut LeanObj {
    mk_io_bool(ACTIVE_CONNS.get(handle).is_some_and(|arc| socket_is_alive(lock_unpoison(&arc).stream.raw_fd())))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_outbound_release(handle: u64, keep_alive: u8) -> *mut LeanObj {
    if let Some(conn) = remove_active(handle) {
        if keep_alive != 0 {
            lock_unpoison(global_pool()).push(conn, Instant::now());
        }
    }
    mk_io_unit()
}

// ---- Loopback TCP Listener Helpers (Native Server & Test Harnesses) ----

static LISTENERS: HandleTable<Arc<TcpListener>> = HandleTable::new();

#[no_mangle]
pub unsafe extern "C" fn qed_server_free_port() -> *mut LeanObj {
    let port = TcpListener::bind(("127.0.0.1", 0))
        .and_then(|l| l.local_addr())
        .map(|a| a.port())
        .unwrap_or(0);
    qed_lean_io_mk_ok(qed_lean_box(port as usize))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_tcp_listen(port: u16) -> *mut LeanObj {
    let res: Result<(u64, u16), String> = (|| {
        let listener = TcpListener::bind(("127.0.0.1", port))
            .map_err(|_| format!("failed to bind 127.0.0.1:{port}"))?;
        let actual_port = listener.local_addr()
            .map_err(|_| "failed to query local TCP address".to_owned())?.port();
        let _ = listener.set_nonblocking(true);
        Ok((LISTENERS.insert(Arc::new(listener)), actual_port))
    })();
    mk_io_except(res, |(id, p)| qed_lean_mk_prod(qed_lean_box_u64(id), qed_lean_box(p as usize)))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_tcp_accept(listener_id: u64, timeout_ms: u32) -> *mut LeanObj {
    let deadline = Instant::now() + Duration::from_millis(timeout_ms as u64);
    loop {
        let Some(listener) = LISTENERS.get(listener_id) else {
            return mk_io_except_err("closed");
        };
        match listener.accept() {
            Ok((sock, peer)) => {
                let _ = sock.set_nonblocking(false);
                configure_sock(&sock);
                let conn = OutConn {
                    is_tls: false,
                    host: peer.ip().to_string(),
                    port: peer.port(),
                    ssrf_guarded: false,
                    peer_addr: peer,
                    stream: OutStream::Plain(sock),
                };
                return mk_io_except_ok(qed_lean_box_u64(insert_active(conn)));
            }
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                let now = Instant::now();
                if now >= deadline {
                    return mk_io_except_err("timeout");
                }
                let rem_ms = (deadline - now).as_millis().clamp(1, i32::MAX as u128) as i32;
                let rc = crate::poll_in(listener.as_raw_fd(), rem_ms);
                if rc < 0 && last_errno() != libc::EINTR {
                    return mk_io_except_err(&format!("tcp accept failed: {}", io::Error::last_os_error()));
                }
            }
            Err(e) => return mk_io_except_err(&format!("tcp accept failed: {e}")),
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_tcp_close_listener(listener_id: u64) -> *mut LeanObj {
    LISTENERS.remove(listener_id);
    mk_io_unit()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn outbound_pool_lifo_caps_ttl_and_ssrf_isolation() {
        let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let addr = listener.local_addr().unwrap();
        let mut accepted = Vec::new();
        let mut mk = |host: &str, port: u16, ssrf: bool| -> (OutConn, u16) {
            let cli = TcpStream::connect(addr).unwrap();
            let (srv, _) = listener.accept().unwrap();
            accepted.push(srv);
            let local_port = cli.local_addr().unwrap().port();
            (
                OutConn {
                    is_tls: false,
                    host: host.to_owned(),
                    port,
                    ssrf_guarded: ssrf,
                    peer_addr: addr,
                    stream: OutStream::Plain(cli),
                },
                local_port,
            )
        };
        let local_port = |c: &OutConn| match &c.stream {
            OutStream::Plain(s) => s.local_addr().unwrap().port(),
            OutStream::Tls(s) => s.sock.local_addr().unwrap().port(),
        };

        let t0 = Instant::now();
        let mut pool = OutboundPool::new(2, 3);

        // Per-host cap (2) evicts oldest and pops LIFO
        let (c1, _) = mk("a.test", 80, false);
        let (c2, p2) = mk("a.test", 80, false);
        let (c3, p3) = mk("a.test", 80, false);
        pool.push(c1, t0);
        pool.push(c2, t0 + Duration::from_secs(1));
        pool.push(c3, t0 + Duration::from_secs(2));
        assert_eq!(pool.total, 2);

        // SSRF partition isolation: ssrf_guarded=true must NEVER pop ssrf_guarded=false sockets
        let k_a_unguarded = (false, "a.test".to_owned(), 80, false);
        let k_a_guarded = (false, "a.test".to_owned(), 80, true);
        assert!(pool.pop_entry(&k_a_guarded, t0 + Duration::from_secs(2)).is_none());

        let popped1 = pool.pop_entry(&k_a_unguarded, t0 + Duration::from_secs(2)).unwrap();
        assert_eq!(local_port(&popped1), p3);
        let popped2 = pool.pop_entry(&k_a_unguarded, t0 + Duration::from_secs(2)).unwrap();
        assert_eq!(local_port(&popped2), p2);
        assert!(pool.pop_entry(&k_a_unguarded, t0 + Duration::from_secs(2)).is_none());
        assert_eq!(pool.total, 0);

        // Global cap (3) evicts globally oldest across hosts & keeps SSRF partitions separate
        let (g1, _) = mk("a.test", 80, true);
        let (g2, gp2) = mk("a.test", 80, true);
        let (b1, _) = mk("b.test", 80, false);
        let (b2, bp2) = mk("b.test", 80, false);
        pool.push(g1, t0);
        pool.push(g2, t0 + Duration::from_secs(1));
        pool.push(b1, t0 + Duration::from_secs(2));
        pool.push(b2, t0 + Duration::from_secs(3));
        assert_eq!(pool.total, 3);
        assert!(pool.pop_entry(&k_a_unguarded, t0 + Duration::from_secs(3)).is_none());
        assert_eq!(local_port(&pool.pop_entry(&k_a_guarded, t0 + Duration::from_secs(3)).unwrap()), gp2);
        assert!(pool.pop_entry(&k_a_guarded, t0 + Duration::from_secs(3)).is_none());

        // TTL expiry evicts stale entries deterministically
        let k_b = (false, "b.test".to_owned(), 80, false);
        assert_eq!(local_port(&pool.pop_entry(&k_b, t0 + Duration::from_secs(3)).unwrap()), bp2);
        assert!(pool.pop_entry(&k_b, t0 + POOL_TTL + Duration::from_secs(10)).is_none());
        assert_eq!(pool.total, 0);
    }
}
