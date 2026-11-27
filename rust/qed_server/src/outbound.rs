use std::{cell::RefCell, collections::HashMap, io::{self, Read, Write}, net::{IpAddr, SocketAddr, TcpListener, TcpStream, ToSocketAddrs}, os::fd::AsRawFd, sync::{Arc, Mutex, OnceLock}, time::{Duration, Instant}};
use rustls::{client::danger::{HandshakeSignatureValid, ServerCertVerified, ServerCertVerifier}, pki_types::{CertificateDer, ServerName, UnixTime}, ClientConfig, ClientConnection, DigitallySignedStruct, RootCertStore, SignatureScheme, StreamOwned};

use crate::lean_ffi::*;
use crate::{HandleTable, bind_loopback_nonblock, is_wouldblock, last_errno, lock_unpoison, rem_timeout_ms};

const POOL_TTL: Duration = Duration::from_secs(30);
const READ_BUF_CAP: usize = 65536;
const BAD_HANDLE: &str = "invalid outbound connection handle";

#[derive(Debug)]
struct NoVerify;
impl ServerCertVerifier for NoVerify {
    fn verify_server_cert(&self, _: &CertificateDer<'_>, _: &[CertificateDer<'_>], _: &ServerName<'_>, _: &[u8], _: UnixTime) -> Result<ServerCertVerified, rustls::Error> { Ok(ServerCertVerified::assertion()) }
    fn verify_tls12_signature(&self, _: &[u8], _: &CertificateDer<'_>, _: &DigitallySignedStruct) -> Result<HandshakeSignatureValid, rustls::Error> { Ok(HandshakeSignatureValid::assertion()) }
    fn verify_tls13_signature(&self, _: &[u8], _: &CertificateDer<'_>, _: &DigitallySignedStruct) -> Result<HandshakeSignatureValid, rustls::Error> { Ok(HandshakeSignatureValid::assertion()) }
    fn supported_verify_schemes(&self) -> Vec<SignatureScheme> { rustls::crypto::ring::default_provider().signature_verification_algorithms.supported_schemes() }
}

fn tls_config() -> Arc<ClientConfig> {
    static TLS_CONFIG: OnceLock<Arc<ClientConfig>> = OnceLock::new();
    TLS_CONFIG.get_or_init(|| {
        let b = ClientConfig::builder_with_provider(Arc::new(rustls::crypto::ring::default_provider()))
            .with_safe_default_protocol_versions().expect("TLS versions");
        Arc::new(if std::env::var("QED_INSECURE_SKIP_TLS_VERIFY").as_deref() == Ok("1") {
            b.dangerous().with_custom_certificate_verifier(Arc::new(NoVerify)).with_no_client_auth()
        } else {
            let mut roots = RootCertStore::empty();
            roots.extend(webpki_roots::TLS_SERVER_ROOTS.iter().cloned());
            if let Some(p) = ["QED_CA_CERT_FILE", "SSL_CERT_FILE"].into_iter().find_map(|k| std::env::var(k).ok().filter(|s| !s.trim().is_empty())) {
                match std::fs::read_to_string(&p) {
                    Ok(pem) => if let (0, ign) = roots.add_parsable_certificates(crate::parse_pem_blocks(&pem, "CERTIFICATE").into_iter().map(CertificateDer::from)) {
                        eprintln!("warning: no valid CA certificates loaded from `{p}` (ignored: {ign})");
                    },
                    Err(e) => eprintln!("warning: failed to read CA bundle `{p}`: {e}"),
                }
            }
            b.with_root_certificates(roots).with_no_client_auth()
        })
    }).clone()
}

enum OutStream { Plain(TcpStream), Tls(Box<StreamOwned<ClientConnection, TcpStream>>) }
impl OutStream {
    fn raw_fd(&self) -> libc::c_int { match self { Self::Plain(s) => s.as_raw_fd(), Self::Tls(s) => s.sock.as_raw_fd() } }
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        match self { Self::Plain(s) => s.write_all(buf), Self::Tls(s) => { s.write_all(buf)?; s.flush() } }
    }
    fn read_some(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self { Self::Plain(s) => s.read(buf), Self::Tls(s) => match s.read(buf) { Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => Ok(0), r => r } }
    }
}

type PoolKey = (bool, String, u16, bool);
struct OutConn { key: PoolKey, peer_addr: SocketAddr, stream: OutStream }
struct PoolEntry { conn: OutConn, last_used: Instant }
struct OutboundPool { buckets: HashMap<PoolKey, Vec<PoolEntry>>, total: usize, max_per_host: usize, max_total: usize }

impl OutboundPool {
    fn new(max_per_host: usize, max_total: usize) -> Self { Self { buckets: HashMap::new(), total: 0, max_per_host, max_total } }
    fn prune_bucket(v: &mut Vec<PoolEntry>, now: Instant, total: &mut usize) -> bool {
        let before = v.len(); v.retain(|e| now.duration_since(e.last_used) <= POOL_TTL); *total -= before - v.len(); !v.is_empty()
    }
    fn pop_entry(&mut self, key: &PoolKey, now: Instant) -> Option<OutConn> {
        let v = self.buckets.get_mut(key)?;
        while let Some(e) = v.pop() {
            self.total -= 1;
            if now.duration_since(e.last_used) <= POOL_TTL { if v.is_empty() { self.buckets.remove(key); } return Some(e.conn); }
        }
        self.buckets.remove(key); None
    }
    fn push(&mut self, conn: OutConn, now: Instant) {
        let key = conn.key.clone();
        if let Some(v) = self.buckets.get_mut(&key) {
            Self::prune_bucket(v, now, &mut self.total);
            while v.len() >= self.max_per_host { v.remove(0); self.total -= 1; }
        }
        if self.total >= self.max_total {
            self.buckets.retain(|_, v| Self::prune_bucket(v, now, &mut self.total));
            if self.total >= self.max_total {
                if let Some(k) = self.buckets.iter().filter_map(|(k, v)| v.first().map(|e| (k, e.last_used))).min_by_key(|(_, t)| *t).map(|(k, _)| k.clone()) {
                    let v = self.buckets.get_mut(&k).unwrap();
                    v.remove(0); self.total -= 1;
                    if v.is_empty() { self.buckets.remove(&k); }
                }
            }
        }
        self.buckets.entry(key).or_default().push(PoolEntry { conn, last_used: now });
        self.total += 1;
    }
}

static ACTIVE_CONNS: HandleTable<Arc<Mutex<OutConn>>> = HandleTable::new();
static LISTENERS: HandleTable<Arc<TcpListener>> = HandleTable::new();
thread_local! { static READ_SCRATCH: RefCell<Vec<u8>> = const { RefCell::new(Vec::new()) }; }

fn global_pool() -> &'static Mutex<OutboundPool> {
    static POOL: OnceLock<Mutex<OutboundPool>> = OnceLock::new();
    POOL.get_or_init(|| Mutex::new(OutboundPool::new(16, 128)))
}
fn socket_is_alive(fd: libc::c_int) -> bool {
    let mut b = 0u8;
    unsafe { libc::recv(fd, &mut b as *mut u8 as *mut _, 1, libc::MSG_PEEK | libc::MSG_DONTWAIT) < 0 && is_wouldblock(last_errno()) }
}
fn insert_active(conn: OutConn) -> u64 { ACTIVE_CONNS.insert(Arc::new(Mutex::new(conn))) }
fn remove_active(handle: u64) -> Option<OutConn> {
    Arc::try_unwrap(ACTIVE_CONNS.remove(handle)?).ok().map(|m| m.into_inner().unwrap_or_else(|e| e.into_inner()))
}
fn configure_sock(s: &TcpStream) {
    let t = Some(Duration::from_secs(30));
    let _ = (s.set_nodelay(true), s.set_read_timeout(t), s.set_write_timeout(t));
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
fn with_active<T>(handle: u64, f: impl FnOnce(&mut OutStream) -> Result<T, String>) -> Result<T, String> {
    ACTIVE_CONNS.get(handle).ok_or_else(|| BAD_HANDLE.to_owned()).and_then(|arc| f(&mut lock_unpoison(&arc).stream))
}

ffi_export! {
    qed_server_outbound_acquire(is_tls: u8, host_obj: *mut LeanObj, port: u16, ssrf_guard: u8, is_blocked_fn: *mut LeanObj) => {
        let (want_tls, want_ssrf, host) = (is_tls != 0, ssrf_guard != 0, str_slice(host_obj));
        let res: Result<(u64, usize), String> = (|| {
            let key: PoolKey = (want_tls, host.to_owned(), port, want_ssrf);
            while let Some(conn) = lock_unpoison(global_pool()).pop_entry(&key, Instant::now()) {
                if socket_is_alive(conn.stream.raw_fd()) {
                    if want_ssrf { check_ssrf_lean(&[conn.peer_addr], is_blocked_fn)?; }
                    return Ok((insert_active(conn), 1));
                }
            }
            let addrs: Vec<SocketAddr> = (host, port).to_socket_addrs().map_err(|e| format!("DNS resolution failed for {host}: {e}"))?.collect();
            if want_ssrf { check_ssrf_lean(&addrs, is_blocked_fn)?; }
            let (deadline, multi, mut last_err) = (Instant::now() + Duration::from_secs(10), addrs.len() > 1, None);
            let (sock, peer_addr) = addrs.iter().find_map(|&addr| {
                let rem = deadline.checked_duration_since(Instant::now()).filter(|d| !d.is_zero())?;
                match TcpStream::connect_timeout(&addr, if multi { rem.min(Duration::from_secs(3)) } else { rem }) {
                    Ok(s) => Some((s, addr)), Err(e) => { last_err = Some(e); None }
                }
            }).ok_or_else(|| last_err.map_or_else(|| format!("TCP connect failed for {host}:{port}"), |e| format!("TCP connect failed for {host}:{port}: {e}")))?;
            configure_sock(&sock);
            let stream = if want_tls { wrap_tls(sock, host, "TLS")? } else { OutStream::Plain(sock) };
            Ok((insert_active(OutConn { key, peer_addr, stream }), 0))
        })();
        mk_io_except(res, |(id, reused)| qed_lean_mk_prod(qed_lean_usize_to_nat(id as usize), qed_lean_usize_to_nat(reused)))
    };
    qed_server_outbound_write_all(handle: u64, data_obj: *mut LeanObj) =>
        mk_io_except_unit(with_active(handle, |s| s.write_all(ba_slice(data_obj)).map_err(|e| format!("write failed: {e}"))));
    qed_server_outbound_read_some(handle: u64, max_bytes: u32) => {
        let want = (max_bytes as usize).clamp(1, READ_BUF_CAP);
        READ_SCRATCH.with(|cell| {
            let mut buf = cell.borrow_mut();
            if buf.len() < want { buf.resize(READ_BUF_CAP, 0); }
            mk_io_except(with_active(handle, |s| s.read_some(&mut buf[..want]).map_err(|e| format!("read failed: {e}"))), |n| mk_ba(&buf[..n]))
        })
    };
    qed_server_outbound_upgrade_tls(handle: u64, host_obj: *mut LeanObj) => mk_io_except_unit((|| -> Result<(), String> {
        let OutConn { mut key, peer_addr, stream } = remove_active(handle).ok_or_else(|| BAD_HANDLE.to_owned())?;
        let stream = match stream { OutStream::Plain(sock) => { key.0 = true; wrap_tls(sock, str_slice(host_obj), "STARTTLS")? } tls => tls };
        ACTIVE_CONNS.insert_at(handle, Arc::new(Mutex::new(OutConn { key, peer_addr, stream }))); Ok(())
    })());
    qed_server_outbound_is_alive(handle: u64) =>
        mk_io_bool(ACTIVE_CONNS.get(handle).is_some_and(|arc| socket_is_alive(lock_unpoison(&arc).stream.raw_fd())));
    qed_server_outbound_release(handle: u64, keep_alive: u8) => {
        if let Some(conn) = remove_active(handle) { if keep_alive != 0 { lock_unpoison(global_pool()).push(conn, Instant::now()); } } mk_io_unit()
    };
    qed_server_free_port() => qed_lean_io_mk_ok(qed_lean_box(bind_loopback_nonblock(0).map_or(0, |(_, p)| p) as usize));
    qed_server_tcp_listen(port: u16) =>
        mk_io_except(bind_loopback_nonblock(port).map(|(l, p)| (LISTENERS.insert(Arc::new(l)), p)), |(id, p)| qed_lean_mk_prod(qed_lean_box_u64(id), qed_lean_box(p as usize)));
    qed_server_tcp_accept(listener_id: u64, timeout_ms: u32) => {
        let deadline = Instant::now() + Duration::from_millis(timeout_ms as u64);
        mk_io_except(loop {
            let Some(l) = LISTENERS.get(listener_id) else { break Err("closed".to_owned()) };
            match l.accept() {
                Ok((sock, peer)) => {
                    let _ = sock.set_nonblocking(false); configure_sock(&sock);
                    break Ok(insert_active(OutConn { key: (false, peer.ip().to_string(), peer.port(), false), peer_addr: peer, stream: OutStream::Plain(sock) }));
                }
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    let Some(rem) = rem_timeout_ms(deadline, 1) else { break Err("timeout".to_owned()) };
                    if crate::poll_in(l.as_raw_fd(), rem) < 0 && last_errno() != libc::EINTR { break Err(format!("tcp accept failed: {}", io::Error::last_os_error())); }
                }
                Err(e) => break Err(format!("tcp accept failed: {e}")),
            }
        }, |id| qed_lean_box_u64(id))
    };
    qed_server_tcp_close_listener(listener_id: u64) => { LISTENERS.remove(listener_id); mk_io_unit() };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn outbound_pool_lifo_caps_ttl_and_ssrf_isolation() {
        let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let (addr, mut accepted, t0, mut pool) = (listener.local_addr().unwrap(), Vec::new(), Instant::now(), OutboundPool::new(2, 3));
        let mut mk = |k: &PoolKey| {
            let cli = TcpStream::connect(addr).unwrap(); accepted.push(listener.accept().unwrap().0);
            let lp = cli.local_addr().unwrap().port();
            (OutConn { key: k.clone(), peer_addr: addr, stream: OutStream::Plain(cli) }, lp)
        };
        let (at, pop) = (|s| t0 + Duration::from_secs(s), |p: &mut OutboundPool, k: &PoolKey, t| p.pop_entry(k, t).map(|c| match &c.stream { OutStream::Plain(s) => s.local_addr().unwrap().port(), OutStream::Tls(s) => s.sock.local_addr().unwrap().port() }));
        let (k_u, k_g, k_b) = ((false, "a.test".into(), 80, false), (false, "a.test".into(), 80, true), (false, "b.test".into(), 80, false));
        let ((c1, _), (c2, p2), (c3, p3)) = (mk(&k_u), mk(&k_u), mk(&k_u));
        for (c, s) in [(c1, 0), (c2, 1), (c3, 2)] { pool.push(c, at(s)); }
        assert_eq!((pool.total, pop(&mut pool, &k_g, at(2)), pop(&mut pool, &k_u, at(2)), pop(&mut pool, &k_u, at(2)), pop(&mut pool, &k_u, at(2)), pool.total), (2, None, Some(p3), Some(p2), None, 0));
        let ((g1, _), (g2, gp2), (b1, _), (b2, bp2)) = (mk(&k_g), mk(&k_g), mk(&k_b), mk(&k_b));
        for (c, s) in [(g1, 0), (g2, 1), (b1, 2), (b2, 3)] { pool.push(c, at(s)); }
        assert_eq!((pool.total, pop(&mut pool, &k_u, at(3)), pop(&mut pool, &k_g, at(3)), pop(&mut pool, &k_g, at(3))), (3, None, Some(gp2), None));
        assert_eq!((pop(&mut pool, &k_b, at(3)), pop(&mut pool, &k_b, t0 + POOL_TTL + Duration::from_secs(10)), pool.total), (Some(bp2), None, 0));
    }
}
