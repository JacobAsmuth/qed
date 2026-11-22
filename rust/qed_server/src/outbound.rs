use std::cell::RefCell;
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

const POOL_SIZE: usize = 8;
const POOL_TTL: Duration = Duration::from_secs(30);
const CONNECT_TIMEOUT: Duration = Duration::from_secs(10);
const IO_TIMEOUT: Duration = Duration::from_secs(30);

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

struct OutConn { is_tls: bool, host: String, port: u16, stream: OutStream }
struct PoolEntry { conn: OutConn, last_used: Instant }

static ACTIVE_CONNS: HandleTable<Arc<Mutex<OutConn>>> = HandleTable::new();

thread_local! {
    static OUTBOUND_POOL: RefCell<Vec<PoolEntry>> = const { RefCell::new(Vec::new()) };
}

fn socket_is_alive(fd: libc::c_int) -> bool {
    let mut b: u8 = 0;
    let r = unsafe { libc::recv(fd, &mut b as *mut u8 as *mut libc::c_void, 1, libc::MSG_PEEK | libc::MSG_DONTWAIT) };
    // An idle HTTP/1.1 keep-alive or PostgreSQL idle connection must have zero pending bytes (`EAGAIN`/`EWOULDBLOCK`);
    // `r == 0` is peer EOF and `r > 0` indicates an unread TLS `close_notify` alert or stray data.
    r < 0 && is_wouldblock(last_errno())
}

fn pop_pooled(is_tls: bool, host: &str, port: u16) -> Option<OutConn> {
    OUTBOUND_POOL.with(|cell| {
        let mut pool = cell.borrow_mut();
        let now = Instant::now();
        let mut i = 0;
        while i < pool.len() {
            if now.duration_since(pool[i].last_used) > POOL_TTL {
                pool.swap_remove(i);
            } else if pool[i].conn.is_tls == is_tls && pool[i].conn.port == port && pool[i].conn.host == host {
                let entry = pool.swap_remove(i);
                if socket_is_alive(entry.conn.stream.raw_fd()) { return Some(entry.conn); }
            } else {
                i += 1;
            }
        }
        None
    })
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
    let res = f(&mut lock_unpoison(&arc).stream);
    res
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_outbound_acquire(
    is_tls: u8,
    host_obj: *mut LeanObj,
    port: u16,
    ssrf_guard: u8,
    is_blocked_fn: *mut LeanObj,
) -> *mut LeanObj {
    let (want_tls, host) = (is_tls != 0, str_slice(host_obj));
    let res: Result<(u64, usize), String> = (|| {
        if ssrf_guard == 0 {
            if let Some(conn) = pop_pooled(want_tls, host, port) {
                return Ok((insert_active(conn), 1));
            }
        }
        let addrs: Vec<SocketAddr> = (host, port).to_socket_addrs()
            .map_err(|e| format!("DNS resolution failed for {host}: {e}"))?.collect();
        if ssrf_guard != 0 {
            check_ssrf_lean(&addrs, is_blocked_fn).map_err(str::to_owned)?;
        }
        let mut last_err = None;
        let sock = addrs.iter().find_map(|addr| match TcpStream::connect_timeout(addr, CONNECT_TIMEOUT) {
            Ok(s) => Some(s),
            Err(e) => { last_err = Some(e); None }
        }).ok_or_else(|| match last_err {
            Some(e) => format!("TCP connect failed for {host}:{port}: {e}"),
            None => format!("TCP connect failed for {host}:{port}"),
        })?;
        configure_sock(&sock);
        let stream = if want_tls { wrap_tls(sock, host, "TLS")? } else { OutStream::Plain(sock) };
        Ok((insert_active(OutConn { is_tls: want_tls, host: host.to_owned(), port, stream }), 0))
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
    let mut buf = vec![0u8; (max_bytes as usize).clamp(1, 65536)];
    let res = with_active_conn(handle, |s| s.read_some_bytes(&mut buf).map_err(|e| format!("read failed: {e}")));
    mk_io_except(res, |n| mk_ba(&buf[..n]))
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
                let upgraded = OutConn { is_tls: true, host: conn.host, port: conn.port, stream };
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
            OUTBOUND_POOL.with(|cell| {
                let mut pool = cell.borrow_mut();
                if pool.len() >= POOL_SIZE {
                    if let Some((idx, _)) = pool.iter().enumerate().min_by_key(|(_, e)| e.last_used) {
                        pool.swap_remove(idx);
                    }
                }
                pool.push(PoolEntry { conn, last_used: Instant::now() });
            });
        }
    }
    mk_io_unit()
}

// ---- Loopback TCP Listener Helpers (Native Server & Test Harnesses) ----

static LISTENERS: HandleTable<TcpListener> = HandleTable::new();

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
        Ok((LISTENERS.insert(listener), actual_port))
    })();
    mk_io_except(res, |(id, p)| qed_lean_mk_prod(qed_lean_box_u64(id), qed_lean_box(p as usize)))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_tcp_accept(listener_id: u64, timeout_ms: u32) -> *mut LeanObj {
    let deadline = Instant::now() + Duration::from_millis(timeout_ms as u64);
    loop {
        let Some(step) = LISTENERS.with(listener_id, |l| l.accept()) else {
            return mk_io_except_err("closed");
        };
        match step {
            Ok((sock, peer)) => {
                let _ = sock.set_nonblocking(false);
                configure_sock(&sock);
                let conn = OutConn {
                    is_tls: false,
                    host: peer.ip().to_string(),
                    port: peer.port(),
                    stream: OutStream::Plain(sock),
                };
                return mk_io_except_ok(qed_lean_box_u64(insert_active(conn)));
            }
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                if Instant::now() >= deadline {
                    return mk_io_except_err("timeout");
                }
                std::thread::sleep(Duration::from_millis(3));
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
