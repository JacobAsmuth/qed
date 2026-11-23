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
use crate::{HandleTable, bind_loopback_nonblock, is_wouldblock, last_errno, lock_unpoison, rem_timeout_ms};

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
    fn verify_server_cert(
        &self, _: &CertificateDer<'_>, _: &[CertificateDer<'_>], _: &ServerName<'_>, _: &[u8], _: UnixTime,
    ) -> Result<ServerCertVerified, rustls::Error> { Ok(ServerCertVerified::assertion()) }
    fn verify_tls12_signature(
        &self, _: &[u8], _: &CertificateDer<'_>, _: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> { Ok(HandshakeSignatureValid::assertion()) }
    fn verify_tls13_signature(
        &self, _: &[u8], _: &CertificateDer<'_>, _: &DigitallySignedStruct,
    ) -> Result<HandshakeSignatureValid, rustls::Error> { Ok(HandshakeSignatureValid::assertion()) }
    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> {
        rustls::crypto::ring::default_provider().signature_verification_algorithms.supported_schemes()
    }
}

static TLS_CONFIG: OnceLock<Arc<ClientConfig>> = OnceLock::new();

fn load_extra_ca_certs(roots: &mut RootCertStore) {
    let Some(path) = ["QED_CA_CERT_FILE", "SSL_CERT_FILE"].into_iter()
        .find_map(|k| std::env::var(k).ok().filter(|s| !s.trim().is_empty())) else { return };
    match std::fs::read_to_string(&path) {
        Ok(pem) => {
            let (added, ignored) = roots.add_parsable_certificates(
                crate::parse_pem_blocks(&pem, "CERTIFICATE").into_iter().map(CertificateDer::from),
            );
            if added == 0 { eprintln!("warning: no valid CA certificates loaded from `{path}` (ignored: {ignored})"); }
        }
        Err(e) => eprintln!("warning: failed to read CA bundle `{path}`: {e}"),
    }
}

fn tls_config() -> Arc<ClientConfig> {
    TLS_CONFIG.get_or_init(|| {
        let builder = ClientConfig::builder_with_provider(Arc::new(rustls::crypto::ring::default_provider()))
            .with_safe_default_protocol_versions().expect("TLS versions");
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
                Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => Ok(0),
                r => r,
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

struct PoolEntry { conn: OutConn, last_used: Instant }

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
                if vec.is_empty() { self.buckets.remove(key); }
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
            while vec.len() >= self.max_per_host { vec.remove(0); self.total -= 1; }
        }
        if self.total >= self.max_total {
            self.sweep_expired(now);
            if self.total >= self.max_total {
                if let Some(oldest_key) = self.buckets.iter()
                    .filter_map(|(k, v)| v.first().map(|e| (k, e.last_used)))
                    .min_by_key(|(_, ts)| *ts).map(|(k, _)| k.clone())
                {
                    if let Some(vec) = self.buckets.get_mut(&oldest_key) {
                        vec.remove(0);
                        self.total -= 1;
                        if vec.is_empty() { self.buckets.remove(&oldest_key); }
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
        let conn = lock_unpoison(pool).pop_entry(&key, Instant::now())?;
        if socket_is_alive(conn.stream.raw_fd()) { return Some(conn); }
    }
}

fn insert_active(conn: OutConn) -> u64 { ACTIVE_CONNS.insert(Arc::new(Mutex::new(conn))) }

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

unsafe fn check_ssrf_lean(addrs: &[SocketAddr], is_blocked_fn: *mut LeanObj) -> Result<(), String> {
    if addrs.is_empty() { return Err("SSRF blocked: empty DNS resolution".to_owned()); }
    for addr in addrs {
        let ba = match addr.ip() { IpAddr::V4(v4) => mk_ba(&v4.octets()), IpAddr::V6(v6) => mk_ba(&v6.octets()) };
        qed_lean_inc(is_blocked_fn);
        let res = lean_apply_1(is_blocked_fn, ba);
        let blocked = qed_lean_unbox(res) != 0;
        qed_lean_dec(res);
        if blocked { return Err("SSRF blocked: private/internal IP address".to_owned()); }
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
            if want_ssrf { check_ssrf_lean(&[conn.peer_addr], is_blocked_fn)?; }
            return Ok((insert_active(conn), 1));
        }
        let addrs: Vec<SocketAddr> = (host, port).to_socket_addrs()
            .map_err(|e| format!("DNS resolution failed for {host}: {e}"))?.collect();
        if want_ssrf { check_ssrf_lean(&addrs, is_blocked_fn)?; }
        let deadline = Instant::now() + CONNECT_TIMEOUT;
        let multi = addrs.len() > 1;
        let mut last_err = None;
        let (sock, peer_addr) = addrs.iter().find_map(|&addr| {
            let rem = deadline.checked_duration_since(Instant::now()).filter(|d| !d.is_zero())?;
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
        let conn = OutConn { is_tls: want_tls, host: host.to_owned(), port, ssrf_guarded: want_ssrf, peer_addr, stream };
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
        if buf.len() < want { buf.resize(READ_BUF_CAP, 0); }
        let res = with_active_conn(handle, |s| s.read_some_bytes(&mut buf[..want]).map_err(|e| format!("read failed: {e}")));
        mk_io_except(res, |n| mk_ba(&buf[..n]))
    })
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_outbound_upgrade_tls(handle: u64, host_obj: *mut LeanObj) -> *mut LeanObj {
    let host = str_slice(host_obj);
    let res = match remove_active(handle) {
        None => Err("invalid outbound connection handle".to_owned()),
        Some(conn) => match conn.stream {
            OutStream::Tls(_) => { ACTIVE_CONNS.insert_at(handle, Arc::new(Mutex::new(conn))); Ok(()) }
            OutStream::Plain(sock) => wrap_tls(sock, host, "STARTTLS").map(|stream| {
                ACTIVE_CONNS.insert_at(handle, Arc::new(Mutex::new(OutConn { is_tls: true, stream, ..conn })));
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
        if keep_alive != 0 { lock_unpoison(global_pool()).push(conn, Instant::now()); }
    }
    mk_io_unit()
}

// ---- Loopback TCP Listener Helpers (Native Server & Test Harnesses) ----

static LISTENERS: HandleTable<Arc<TcpListener>> = HandleTable::new();

#[no_mangle]
pub unsafe extern "C" fn qed_server_free_port() -> *mut LeanObj {
    let port = TcpListener::bind(("127.0.0.1", 0)).and_then(|l| l.local_addr()).map_or(0, |a| a.port());
    qed_lean_io_mk_ok(qed_lean_box(port as usize))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_tcp_listen(port: u16) -> *mut LeanObj {
    let res = bind_loopback_nonblock(port).map(|(l, p)| (LISTENERS.insert(Arc::new(l)), p));
    mk_io_except(res, |(id, p)| qed_lean_mk_prod(qed_lean_box_u64(id), qed_lean_box(p as usize)))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_tcp_accept(listener_id: u64, timeout_ms: u32) -> *mut LeanObj {
    let deadline = Instant::now() + Duration::from_millis(timeout_ms as u64);
    let res: Result<u64, String> = loop {
        let Some(listener) = LISTENERS.get(listener_id) else { break Err("closed".to_owned()); };
        match listener.accept() {
            Ok((sock, peer)) => {
                let _ = sock.set_nonblocking(false);
                configure_sock(&sock);
                let conn = OutConn {
                    is_tls: false, host: peer.ip().to_string(), port: peer.port(),
                    ssrf_guarded: false, peer_addr: peer, stream: OutStream::Plain(sock),
                };
                break Ok(insert_active(conn));
            }
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                let Some(rem_ms) = rem_timeout_ms(deadline, 1) else { break Err("timeout".to_owned()); };
                if crate::poll_in(listener.as_raw_fd(), rem_ms) < 0 && last_errno() != libc::EINTR {
                    break Err(format!("tcp accept failed: {}", io::Error::last_os_error()));
                }
            }
            Err(e) => break Err(format!("tcp accept failed: {e}")),
        }
    };
    mk_io_except(res, |id| qed_lean_box_u64(id))
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
            accepted.push(listener.accept().unwrap().0);
            let lp = cli.local_addr().unwrap().port();
            (OutConn { is_tls: false, host: host.to_owned(), port, ssrf_guarded: ssrf, peer_addr: addr, stream: OutStream::Plain(cli) }, lp)
        };
        let t0 = Instant::now();
        let at = |s| t0 + Duration::from_secs(s);
        let pop_port = |pool: &mut OutboundPool, k: &PoolKey, t: Instant| {
            pool.pop_entry(k, t).map(|c| match &c.stream {
                OutStream::Plain(s) => s.local_addr().unwrap().port(),
                OutStream::Tls(s) => s.sock.local_addr().unwrap().port(),
            })
        };

        let mut pool = OutboundPool::new(2, 3);
        let (k_a_u, k_a_g, k_b) = (
            (false, "a.test".to_owned(), 80, false),
            (false, "a.test".to_owned(), 80, true),
            (false, "b.test".to_owned(), 80, false),
        );

        // Per-host cap (2) evicts oldest and pops LIFO; SSRF partition stays isolated
        let (c1, _) = mk("a.test", 80, false);
        let (c2, p2) = mk("a.test", 80, false);
        let (c3, p3) = mk("a.test", 80, false);
        for (c, s) in [(c1, 0), (c2, 1), (c3, 2)] { pool.push(c, at(s)); }
        assert_eq!(pool.total, 2);
        assert_eq!(pop_port(&mut pool, &k_a_g, at(2)), None);
        assert_eq!(pop_port(&mut pool, &k_a_u, at(2)), Some(p3));
        assert_eq!(pop_port(&mut pool, &k_a_u, at(2)), Some(p2));
        assert_eq!(pop_port(&mut pool, &k_a_u, at(2)), None);
        assert_eq!(pool.total, 0);

        // Global cap (3) evicts globally oldest across hosts & preserves SSRF partition isolation
        let (g1, _) = mk("a.test", 80, true);
        let (g2, gp2) = mk("a.test", 80, true);
        let (b1, _) = mk("b.test", 80, false);
        let (b2, bp2) = mk("b.test", 80, false);
        for (c, s) in [(g1, 0), (g2, 1), (b1, 2), (b2, 3)] { pool.push(c, at(s)); }
        assert_eq!(pool.total, 3);
        assert_eq!(pop_port(&mut pool, &k_a_u, at(3)), None);
        assert_eq!(pop_port(&mut pool, &k_a_g, at(3)), Some(gp2));
        assert_eq!(pop_port(&mut pool, &k_a_g, at(3)), None);

        // TTL expiry evicts stale entries deterministically
        assert_eq!(pop_port(&mut pool, &k_b, at(3)), Some(bp2));
        assert_eq!(pop_port(&mut pool, &k_b, t0 + POOL_TTL + Duration::from_secs(10)), None);
        assert_eq!(pool.total, 0);
    }
}
