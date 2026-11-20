use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{self, Read, Write};
use std::net::{IpAddr, SocketAddr, TcpStream, ToSocketAddrs};
use std::os::fd::AsRawFd;
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

use rustls::client::danger::{HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier};
use rustls::pki_types::{CertificateDer, ServerName, UnixTime};
use rustls::{ClientConfig, ClientConnection, DigitallySignedStruct, RootCertStore, SignatureScheme, StreamOwned};

use crate::lean_ffi::*;
use crate::{is_wouldblock, last_errno};

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

#[derive(Default)]
struct OutboundState { next_id: u64, active: HashMap<u64, OutConn>, pool: Vec<PoolEntry> }

thread_local! {
    static OUTBOUND: RefCell<OutboundState> = RefCell::new(OutboundState::default());
}

fn socket_is_alive(fd: libc::c_int) -> bool {
    let mut b: u8 = 0;
    let r = unsafe { libc::recv(fd, &mut b as *mut u8 as *mut libc::c_void, 1, libc::MSG_PEEK | libc::MSG_DONTWAIT) };
    // An idle HTTP/1.1 keep-alive connection must have zero pending bytes (`EAGAIN`/`EWOULDBLOCK`);
    // `r == 0` is peer EOF and `r > 0` indicates an unread TLS `close_notify` alert or stray data.
    r < 0 && is_wouldblock(last_errno())
}

fn pop_pooled(is_tls: bool, host: &str, port: u16) -> Option<OutConn> {
    OUTBOUND.with(|cell| {
        let mut st = cell.borrow_mut();
        let now = Instant::now();
        let mut i = 0;
        while i < st.pool.len() {
            if now.duration_since(st.pool[i].last_used) > POOL_TTL {
                st.pool.swap_remove(i);
            } else if st.pool[i].conn.is_tls == is_tls && st.pool[i].conn.port == port && st.pool[i].conn.host == host {
                let entry = st.pool.swap_remove(i);
                if socket_is_alive(entry.conn.stream.raw_fd()) { return Some(entry.conn); }
            } else {
                i += 1;
            }
        }
        None
    })
}

fn insert_active(conn: OutConn) -> usize {
    OUTBOUND.with(|cell| {
        let mut st = cell.borrow_mut();
        st.next_id = st.next_id.wrapping_add(1).max(1);
        let id = st.next_id;
        st.active.insert(id, conn);
        id as usize
    })
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

#[no_mangle]
pub unsafe extern "C" fn qed_server_outbound_acquire(
    is_tls: u8,
    host_obj: *mut LeanObj,
    port: u16,
    ssrf_guard: u8,
    is_blocked_fn: *mut LeanObj,
) -> *mut LeanObj {
    let want_tls = is_tls != 0;
    let host = str_slice(host_obj);
    if ssrf_guard == 0 {
        if let Some(conn) = pop_pooled(want_tls, host, port) {
            return mk_io_except_ok(qed_lean_mk_prod(qed_lean_usize_to_nat(insert_active(conn)), qed_lean_usize_to_nat(1)));
        }
    }
    let addrs: Vec<SocketAddr> = match (host, port).to_socket_addrs() {
        Ok(it) => it.collect(),
        Err(e) => return mk_io_except_err(&format!("DNS resolution failed for {host}: {e}")),
    };
    if ssrf_guard != 0 {
        if let Err(msg) = check_ssrf_lean(&addrs, is_blocked_fn) { return mk_io_except_err(msg); }
    }
    let mut last_err = None;
    let mut sock = None;
    for addr in &addrs {
        match TcpStream::connect_timeout(addr, CONNECT_TIMEOUT) {
            Ok(s) => { sock = Some(s); break; }
            Err(e) => last_err = Some(e),
        }
    }
    let Some(mut sock) = sock else {
        let msg = last_err.map_or_else(|| format!("TCP connect failed for {host}:{port}"), |e| format!("TCP connect failed for {host}:{port}: {e}"));
        return mk_io_except_err(&msg);
    };
    let _ = sock.set_read_timeout(Some(IO_TIMEOUT));
    let _ = sock.set_write_timeout(Some(IO_TIMEOUT));
    let _ = sock.set_nodelay(true);
    let stream = if want_tls {
        let Ok(sni) = ServerName::try_from(host.to_owned()) else { return mk_io_except_err(&format!("invalid TLS server name: {host}")); };
        let Ok(mut conn) = ClientConnection::new(tls_config(), sni) else { return mk_io_except_err("TLS client init failed"); };
        if let Err(e) = conn.complete_io(&mut sock) { return mk_io_except_err(&format!("TLS handshake failed for {host}: {e}")); }
        OutStream::Tls(Box::new(StreamOwned::new(conn, sock)))
    } else {
        OutStream::Plain(sock)
    };
    let id = insert_active(OutConn { is_tls: want_tls, host: host.to_owned(), port, stream });
    mk_io_except_ok(qed_lean_mk_prod(qed_lean_usize_to_nat(id), qed_lean_usize_to_nat(0)))
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_outbound_write_all(handle: u64, data_obj: *mut LeanObj) -> *mut LeanObj {
    let data = ba_slice(data_obj);
    let res = OUTBOUND.with(|cell| match cell.borrow_mut().active.get_mut(&handle) {
        Some(c) => c.stream.write_all_bytes(data).map_err(|e| format!("write failed: {e}")),
        None => Err("invalid outbound connection handle".to_owned()),
    });
    match res { Ok(()) => mk_io_except_ok(qed_lean_box(0)), Err(e) => mk_io_except_err(&e) }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_outbound_read_some(handle: u64, max_bytes: u32) -> *mut LeanObj {
    let mut buf = vec![0u8; (max_bytes as usize).clamp(1, 65536)];
    let res = OUTBOUND.with(|cell| match cell.borrow_mut().active.get_mut(&handle) {
        Some(c) => c.stream.read_some_bytes(&mut buf).map_err(|e| format!("read failed: {e}")),
        None => Err("invalid outbound connection handle".to_owned()),
    });
    match res { Ok(n) => mk_io_except_ok(mk_ba(&buf[..n])), Err(e) => mk_io_except_err(&e) }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_outbound_release(handle: u64, keep_alive: u8) -> *mut LeanObj {
    OUTBOUND.with(|cell| {
        let mut st = cell.borrow_mut();
        if let Some(conn) = st.active.remove(&handle) {
            if keep_alive != 0 {
                if st.pool.len() >= POOL_SIZE {
                    if let Some((idx, _)) = st.pool.iter().enumerate().min_by_key(|(_, e)| e.last_used) {
                        st.pool.swap_remove(idx);
                    }
                }
                st.pool.push(PoolEntry { conn, last_used: Instant::now() });
            }
        }
    });
    qed_lean_io_mk_ok(qed_lean_box(0))
}
