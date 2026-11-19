use std::collections::HashMap;
use std::io::{self, Write};
use std::net::{Ipv4Addr, SocketAddrV4};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use crate::lean_ffi::*;
use crate::{is_wouldblock, last_errno, lock_unpoison};

const MAX_REQ_HDR_BYTES: usize = 65536;
const MAX_WORKER_CONNS: usize = 4096;
const HTTP_IDLE_TIMEOUT: Duration = Duration::from_secs(30);
const WS_PING_INTERVAL: Duration = Duration::from_secs(25);
const WS_DEAD_TIMEOUT: Duration = Duration::from_secs(75);
const TOKEN_LISTEN: u64 = 1;
const TOKEN_WAKE: u64 = 2;

static STOP: AtomicBool = AtomicBool::new(false);
static INBOXES: Mutex<Vec<Arc<WorkerInbox>>> = Mutex::new(Vec::new());

extern "C" fn handle_stop_signal(_sig: libc::c_int) { STOP.store(true, Ordering::SeqCst); }

// ---- Cross-Worker WebSocket Broadcast Inbox ----

struct BcastMsg { topic: String, payload: Vec<u8> }
struct WorkerInbox { queue: Mutex<Vec<Arc<BcastMsg>>>, wake_rfd: libc::c_int, wake_wfd: libc::c_int }

impl WorkerInbox {
    fn new() -> Self {
        #[cfg(target_os = "linux")]
        let (rfd, wfd) = { let fd = unsafe { libc::eventfd(0, libc::EFD_NONBLOCK | libc::EFD_CLOEXEC) }; (fd, fd) };
        #[cfg(not(target_os = "linux"))]
        let (rfd, wfd) = {
            let mut fds = [-1 as libc::c_int; 2];
            if unsafe { libc::pipe(fds.as_mut_ptr()) } == 0 {
                set_nonblocking(fds[0]); set_nonblocking(fds[1]); (fds[0], fds[1])
            } else { (-1, -1) }
        };
        Self { queue: Mutex::new(Vec::new()), wake_rfd: rfd, wake_wfd: wfd }
    }
    fn wake(&self) {
        if self.wake_wfd >= 0 {
            let v: u64 = 1;
            let _ = unsafe { libc::write(self.wake_wfd, &v as *const u64 as *const libc::c_void, 8) };
        }
    }
    fn drain_wake(&self) {
        if self.wake_rfd >= 0 {
            let mut buf = [0u8; 64];
            while unsafe { libc::read(self.wake_rfd, buf.as_mut_ptr() as *mut libc::c_void, buf.len()) } > 0 {}
        }
    }
}

impl Drop for WorkerInbox {
    fn drop(&mut self) {
        if self.wake_rfd >= 0 { unsafe { libc::close(self.wake_rfd) }; }
        if self.wake_wfd >= 0 && self.wake_wfd != self.wake_rfd { unsafe { libc::close(self.wake_wfd) }; }
    }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_ws_broadcast(topic_obj: *mut LeanObj, payload_obj: *mut LeanObj) -> *mut LeanObj {
    let msg = Arc::new(BcastMsg { topic: str_slice(topic_obj).to_owned(), payload: ba_slice(payload_obj).to_vec() });
    for inbox in lock_unpoison(&INBOXES).clone() {
        lock_unpoison(&inbox.queue).push(msg.clone());
        inbox.wake();
    }
    qed_lean_io_mk_ok(qed_lean_box(0))
}

// ---- Platform Event Loop (Linux epoll / macOS kqueue) ----

struct PollEvent { token: u64, readable: bool, writable: bool, hangup: bool }
struct Poller(libc::c_int);

impl Poller {
    fn new() -> io::Result<Self> {
        #[cfg(target_os = "linux")]
        let fd = unsafe { libc::epoll_create1(libc::EPOLL_CLOEXEC) };
        #[cfg(target_os = "macos")]
        let fd = unsafe { libc::kqueue() };
        if fd < 0 { Err(io::Error::last_os_error()) } else { Ok(Self(fd)) }
    }

    fn add_read(&self, sock: libc::c_int, token: u64) -> bool {
        #[cfg(target_os = "linux")]
        unsafe {
            let mut ev = libc::epoll_event { events: (libc::EPOLLIN | libc::EPOLLRDHUP) as u32, u64: token };
            libc::epoll_ctl(self.0, libc::EPOLL_CTL_ADD, sock, &mut ev) == 0
        }
        #[cfg(target_os = "macos")]
        unsafe {
            let kev = libc::kevent {
                ident: sock as usize, filter: libc::EVFILT_READ, flags: libc::EV_ADD | libc::EV_ENABLE,
                fflags: 0, data: 0, udata: token as *mut libc::c_void,
            };
            libc::kevent(self.0, &kev, 1, std::ptr::null_mut(), 0, std::ptr::null()) == 0
        }
    }

    fn set_write(&self, sock: libc::c_int, token: u64, want_write: bool) {
        #[cfg(target_os = "linux")]
        unsafe {
            let mut ev = libc::epoll_event {
                events: (libc::EPOLLIN | libc::EPOLLRDHUP | if want_write { libc::EPOLLOUT } else { 0 }) as u32,
                u64: token,
            };
            let _ = libc::epoll_ctl(self.0, libc::EPOLL_CTL_MOD, sock, &mut ev);
        }
        #[cfg(target_os = "macos")]
        unsafe {
            let kev = libc::kevent {
                ident: sock as usize, filter: libc::EVFILT_WRITE,
                flags: if want_write { libc::EV_ADD | libc::EV_ENABLE } else { libc::EV_DELETE },
                fflags: 0, data: 0, udata: token as *mut libc::c_void,
            };
            let _ = libc::kevent(self.0, &kev, 1, std::ptr::null_mut(), 0, std::ptr::null());
        }
    }

    fn remove(&self, sock: libc::c_int) {
        #[cfg(target_os = "linux")]
        unsafe { let _ = libc::epoll_ctl(self.0, libc::EPOLL_CTL_DEL, sock, std::ptr::null_mut()); }
        #[cfg(target_os = "macos")]
        let _ = sock;
    }

    fn wait(&self, out: &mut Vec<PollEvent>, timeout_ms: i32) {
        out.clear();
        #[cfg(target_os = "linux")]
        unsafe {
            let mut evs: [libc::epoll_event; 128] = std::mem::zeroed();
            let n = libc::epoll_wait(self.0, evs.as_mut_ptr(), evs.len() as i32, timeout_ms);
            for ev in evs.iter().take(n.max(0) as usize) {
                let f = ev.events as i32;
                out.push(PollEvent {
                    token: ev.u64,
                    readable: (f & libc::EPOLLIN) != 0,
                    writable: (f & libc::EPOLLOUT) != 0,
                    hangup: (f & (libc::EPOLLERR | libc::EPOLLHUP | libc::EPOLLRDHUP)) != 0,
                });
            }
        }
        #[cfg(target_os = "macos")]
        unsafe {
            let mut evs: [libc::kevent; 128] = std::mem::zeroed();
            let ts = libc::timespec { tv_sec: (timeout_ms / 1000) as libc::time_t, tv_nsec: ((timeout_ms % 1000) * 1_000_000) as libc::c_long };
            let n = libc::kevent(self.0, std::ptr::null(), 0, evs.as_mut_ptr(), evs.len() as i32, &ts);
            for ev in evs.iter().take(n.max(0) as usize) {
                out.push(PollEvent {
                    token: ev.udata as u64,
                    readable: ev.filter == libc::EVFILT_READ,
                    writable: ev.filter == libc::EVFILT_WRITE,
                    hangup: (ev.flags & (libc::EV_EOF | libc::EV_ERROR)) != 0,
                });
            }
        }
    }
}

impl Drop for Poller { fn drop(&mut self) { unsafe { libc::close(self.0) }; } }

// ---- Low-Level Socket Helpers ----

fn set_nonblocking(fd: libc::c_int) {
    unsafe {
        let f = libc::fcntl(fd, libc::F_GETFL, 0);
        if f >= 0 { let _ = libc::fcntl(fd, libc::F_SETFL, f | libc::O_NONBLOCK); }
    }
}

fn create_listener(port: u16, allow_reuseport: bool) -> io::Result<libc::c_int> {
    unsafe {
        let fd = libc::socket(libc::AF_INET, libc::SOCK_STREAM, 0);
        if fd < 0 { return Err(io::Error::last_os_error()); }
        let one: libc::c_int = 1;
        let _ = libc::setsockopt(fd, libc::SOL_SOCKET, libc::SO_REUSEADDR, &one as *const _ as *const _, 4);
        if allow_reuseport {
            let _ = libc::setsockopt(fd, libc::SOL_SOCKET, libc::SO_REUSEPORT, &one as *const _ as *const _, 4);
        }
        let _ = libc::setsockopt(fd, libc::IPPROTO_TCP, libc::TCP_NODELAY, &one as *const _ as *const _, 4);
        let mut addr: libc::sockaddr_in = std::mem::zeroed();
        addr.sin_family = libc::AF_INET as libc::sa_family_t;
        addr.sin_port = port.to_be();
        if libc::bind(fd, &addr as *const _ as *const libc::sockaddr, std::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t) != 0
            || libc::listen(fd, 1024) != 0
        {
            let err = io::Error::last_os_error();
            libc::close(fd);
            return Err(err);
        }
        set_nonblocking(fd);
        Ok(fd)
    }
}

fn bound_port(fd: libc::c_int) -> u16 {
    unsafe {
        let mut addr: libc::sockaddr_in = std::mem::zeroed();
        let mut len = std::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t;
        if libc::getsockname(fd, &mut addr as *mut _ as *mut libc::sockaddr, &mut len) == 0 { u16::from_be(addr.sin_port) } else { 0 }
    }
}

fn send_nonblock(fd: libc::c_int, data: &[u8]) -> isize {
    #[cfg(target_os = "linux")]
    let flags = libc::MSG_NOSIGNAL;
    #[cfg(not(target_os = "linux"))]
    let flags = 0;
    unsafe { libc::send(fd, data.as_ptr() as *const libc::c_void, data.len(), flags) }
}

// ---- Per-Connection & Per-Worker State ----

struct Callbacks { init_frag: LeanRef, on_head: LeanRef, on_body: LeanRef, on_ws_bytes: LeanRef, on_ws_leave: LeanRef }
struct WsSub { sub_id: u32, topic: String, channel: String, params: Vec<u8> }
struct PendingBody { content_len: usize, keep_alive: bool, req: LeanRef }
enum SubOp { Add(u32, String, String, Vec<u8>), Remove(u32) }

struct Conn {
    token: u64,
    fd: libc::c_int,
    ip: String,
    rx: Vec<u8>,
    tx: Vec<u8>,
    tx_armed: bool,
    peer_eof: bool,
    close_after_tx: bool,
    pending_body: Option<PendingBody>,
    is_ws: bool,
    ws_ctx: Option<LeanRef>,
    frag: Option<LeanRef>,
    subs: Vec<WsSub>,
    last_active: Instant,
    last_ping: Instant,
}

impl Conn {
    fn queue_bytes(&mut self, poller: &Poller, data: &[u8]) -> bool {
        if data.is_empty() { return true; }
        let mut rem = data;
        if self.tx.is_empty() {
            let n = send_nonblock(self.fd, rem);
            if n > 0 {
                rem = &rem[n as usize..];
                if rem.is_empty() { return true; }
            } else if n < 0 {
                let e = last_errno();
                if !is_wouldblock(e) && e != libc::EINTR { return false; }
            }
        }
        self.tx.extend_from_slice(rem);
        if !self.tx_armed {
            poller.set_write(self.fd, self.token, true);
            self.tx_armed = true;
        }
        true
    }

    fn flush_tx(&mut self, poller: &Poller) -> bool {
        while !self.tx.is_empty() {
            let n = send_nonblock(self.fd, &self.tx);
            if n > 0 {
                self.tx.drain(..n as usize);
            } else if n < 0 {
                let e = last_errno();
                if e == libc::EINTR { continue; }
                if is_wouldblock(e) { break; }
                return false;
            } else {
                return false;
            }
        }
        if self.tx.is_empty() && self.tx_armed {
            poller.set_write(self.fd, self.token, false);
            self.tx_armed = false;
        }
        true
    }

    fn queue_ws_event(&mut self, poller: &Poller, sub_id: u32, payload: &[u8]) -> bool {
        let total = 5 + payload.len();
        let mut hdr = [0u8; 15];
        hdr[0] = 0x82;
        let hlen = if total < 126 {
            hdr[1] = total as u8;
            2
        } else if total <= 65535 {
            hdr[1] = 126;
            hdr[2..4].copy_from_slice(&(total as u16).to_be_bytes());
            4
        } else {
            hdr[1] = 127;
            hdr[2..10].copy_from_slice(&(total as u64).to_be_bytes());
            10
        };
        hdr[hlen] = 0x12;
        hdr[hlen + 1..hlen + 5].copy_from_slice(&sub_id.to_be_bytes());
        self.queue_bytes(poller, &hdr[..hlen + 5]) && self.queue_bytes(poller, payload)
    }
}

struct Worker {
    poller: Poller,
    listen_fd: libc::c_int,
    inbox: Arc<WorkerInbox>,
    cbs: Arc<Callbacks>,
    next_token: u64,
    conns: HashMap<u64, Conn>,
    topics: HashMap<String, Vec<(u64, u32)>>,
}

impl Worker {
    fn topic_remove(&mut self, topic: &str, token: u64, sub_id: u32) {
        if let Some(v) = self.topics.get_mut(topic) {
            v.retain(|&(t, s)| !(t == token && s == sub_id));
            if v.is_empty() { self.topics.remove(topic); }
        }
    }

    fn accept_all(&mut self) {
        loop {
            let mut addr: libc::sockaddr_in = unsafe { std::mem::zeroed() };
            let mut len = std::mem::size_of::<libc::sockaddr_in>() as libc::socklen_t;
            let fd = unsafe { libc::accept(self.listen_fd, &mut addr as *mut _ as *mut libc::sockaddr, &mut len) };
            if fd < 0 { break; }
            if self.conns.len() >= MAX_WORKER_CONNS { unsafe { libc::close(fd) }; continue; }
            set_nonblocking(fd);
            let one: libc::c_int = 1;
            unsafe { libc::setsockopt(fd, libc::IPPROTO_TCP, libc::TCP_NODELAY, &one as *const _ as *const _, 4) };
            let token = self.next_token;
            self.next_token += 1;
            if !self.poller.add_read(fd, token) { unsafe { libc::close(fd) }; continue; }
            let ip = SocketAddrV4::new(Ipv4Addr::from(u32::from_be(addr.sin_addr.s_addr)), 0).ip().to_string();
            let now = Instant::now();
            self.conns.insert(token, Conn {
                token, fd, ip, rx: Vec::with_capacity(4096), tx: Vec::new(), tx_armed: false,
                peer_eof: false, close_after_tx: false, pending_body: None, is_ws: false,
                ws_ctx: None, frag: None, subs: Vec::new(), last_active: now, last_ping: now,
            });
        }
    }

    fn close_conn(&mut self, token: u64) {
        let Some(conn) = self.conns.remove(&token) else { return };
        self.poller.remove(conn.fd);
        unsafe { libc::close(conn.fd) };
        if let Some(ws_ctx) = &conn.ws_ctx {
            for sub in &conn.subs {
                self.topic_remove(&sub.topic, token, sub.sub_id);
                unsafe {
                    qed_lean_dec_ref(qed_lean_apply_4(
                        self.cbs.on_ws_leave.clone_ptr(), ws_ctx.clone_ptr(),
                        mk_str(&sub.channel), mk_ba(&sub.params), qed_lean_box(0),
                    ));
                }
            }
        }
    }

    fn drain_inbox(&mut self) {
        self.inbox.drain_wake();
        let msgs = std::mem::take(&mut *lock_unpoison(&self.inbox.queue));
        for msg in msgs {
            let Some(targets) = self.topics.get(&msg.topic).cloned() else { continue };
            for (token, sub_id) in targets {
                if let Some(c) = self.conns.get_mut(&token) {
                    if c.is_ws && !c.close_after_tx { let _ = c.queue_ws_event(&self.poller, sub_id, &msg.payload); }
                }
            }
        }
    }

    fn sweep_idle(&mut self, now: Instant) {
        let mut to_close = Vec::new();
        for (&token, c) in &mut self.conns {
            if c.is_ws {
                if now.duration_since(c.last_active) > WS_DEAD_TIMEOUT {
                    to_close.push(token);
                } else if !c.close_after_tx && now.duration_since(c.last_ping) >= WS_PING_INTERVAL {
                    c.last_ping = now;
                    if !c.queue_bytes(&self.poller, &[0x89, 0x00]) { to_close.push(token); }
                }
            } else if now.duration_since(c.last_active) > HTTP_IDLE_TIMEOUT {
                to_close.push(token);
            }
        }
        for t in to_close { self.close_conn(t); }
    }

    fn process_rx(&mut self, token: u64) -> bool {
        loop {
            let Some(conn) = self.conns.get_mut(&token) else { return false };
            if conn.close_after_tx { return false; }
            if conn.is_ws { return self.process_ws_rx(token); }

            if let Some(pb) = &conn.pending_body {
                if conn.rx.len() < pb.content_len { return true; }
                let pb = conn.pending_body.take().unwrap();
                let ok = unsafe {
                    let res = qed_lean_apply_4(
                        self.cbs.on_body.clone_ptr(), pb.req.clone_ptr(),
                        mk_ba(&conn.rx[..pb.content_len]), mk_str(&conn.ip), qed_lean_box(0),
                    );
                    let sent = qed_lean_io_is_ok(res) != 0 && conn.queue_bytes(&self.poller, ba_slice(qed_lean_io_val(res)));
                    qed_lean_dec_ref(res);
                    sent
                };
                conn.rx.drain(..pb.content_len);
                if !ok || !pb.keep_alive { conn.close_after_tx = true; return false; }
                continue;
            }

            let (head_end, consume_len) = match conn.rx.windows(4).position(|w| w == b"\r\n\r\n") {
                Some(pos) => (pos, pos + 4),
                None if conn.rx.len() > MAX_REQ_HDR_BYTES => (MAX_REQ_HDR_BYTES + 1, conn.rx.len()),
                None => return true,
            };
            let res = unsafe {
                qed_lean_apply_3(self.cbs.on_head.clone_ptr(), mk_ba(&conn.rx[..head_end]), mk_str(&conn.ip), qed_lean_box(0))
            };
            conn.rx.drain(..consume_len);
            if unsafe { qed_lean_io_is_ok(res) } == 0 {
                unsafe { qed_lean_dec_ref(res) };
                conn.close_after_tx = true;
                return false;
            }
            let keep_going = unsafe {
                let act = qed_lean_io_val(res);
                match qed_lean_obj_tag(act) {
                    t @ (0 | 1) => {
                        let sent = conn.queue_bytes(&self.poller, ba_slice(qed_lean_ctor_get(act, 0)));
                        if !sent || t == 0 { conn.close_after_tx = true; false } else { true }
                    }
                    t @ (2 | 3) => {
                        let cl = qed_lean_usize_of_nat(qed_lean_ctor_get(act, 0));
                        let req_ptr = qed_lean_ctor_get(act, 1);
                        qed_lean_inc(req_ptr);
                        conn.pending_body = Some(PendingBody { content_len: cl, keep_alive: t == 3, req: LeanRef(req_ptr) });
                        true
                    }
                    4 => {
                        let sent = conn.queue_bytes(&self.poller, ba_slice(qed_lean_ctor_get(act, 0)));
                        if !sent {
                            conn.close_after_tx = true;
                            false
                        } else {
                            let ctx_ptr = qed_lean_ctor_get(act, 1);
                            qed_lean_inc(ctx_ptr);
                            let now = Instant::now();
                            conn.is_ws = true;
                            conn.ws_ctx = Some(LeanRef(ctx_ptr));
                            conn.frag = Some(self.cbs.init_frag.clone());
                            conn.last_active = now;
                            conn.last_ping = now;
                            true
                        }
                    }
                    _ => { conn.close_after_tx = true; false }
                }
            };
            unsafe { qed_lean_dec_ref(res) };
            if !keep_going { return false; }
        }
    }

    fn process_ws_rx(&mut self, token: u64) -> bool {
        let mut ops_out = Vec::new();
        let stay_open = {
            let conn = self.conns.get_mut(&token).unwrap();
            if conn.rx.is_empty() { return true; }
            let (Some(ws_ctx), Some(frag)) = (&conn.ws_ctx, &conn.frag) else { return false };
            unsafe {
                let mut subs_arr = qed_lean_array_empty();
                for s in &conn.subs {
                    let entry = qed_lean_mk_prod(qed_lean_usize_to_nat(s.sub_id as usize), qed_lean_mk_prod(mk_str(&s.channel), mk_ba(&s.params)));
                    subs_arr = qed_lean_array_push(subs_arr, entry);
                }
                let res = qed_lean_apply_5(
                    self.cbs.on_ws_bytes.clone_ptr(), ws_ctx.clone_ptr(),
                    mk_ba(&conn.rx), frag.clone_ptr(), subs_arr, qed_lean_box(0),
                );
                if qed_lean_io_is_ok(res) == 0 {
                    qed_lean_dec_ref(res);
                    conn.close_after_tx = true;
                    return false;
                }
                let out = qed_lean_io_val(res);
                let consumed = qed_lean_usize_of_nat(qed_lean_ctor_get(out, 0)).min(conn.rx.len());
                let close_flag = qed_lean_usize_of_nat(qed_lean_ctor_get(out, 2));
                let new_frag = qed_lean_ctor_get(out, 3);
                qed_lean_inc(new_frag);
                let ops_arr = qed_lean_ctor_get(out, 4);
                for i in 0..qed_lean_array_size(ops_arr) {
                    let op = qed_lean_array_uget(ops_arr, i);
                    let sid = qed_lean_usize_of_nat(qed_lean_ctor_get(op, 0)) as u32;
                    match qed_lean_obj_tag(op) {
                        0 => ops_out.push(SubOp::Add(
                            sid, str_slice(qed_lean_ctor_get(op, 1)).to_owned(),
                            str_slice(qed_lean_ctor_get(op, 2)).to_owned(),
                            ba_slice(qed_lean_ctor_get(op, 3)).to_vec(),
                        )),
                        1 => ops_out.push(SubOp::Remove(sid)),
                        _ => {}
                    }
                }
                let sent = conn.queue_bytes(&self.poller, ba_slice(qed_lean_ctor_get(out, 1)));
                qed_lean_dec_ref(res);
                if consumed > 0 { conn.rx.drain(..consumed); conn.last_active = Instant::now(); }
                conn.frag = Some(LeanRef(new_frag));
                if !sent || close_flag != 0 { conn.close_after_tx = true; false } else { true }
            }
        };
        for op in ops_out {
            let sid = match &op { SubOp::Add(s, ..) | SubOp::Remove(s) => *s };
            let old = self.conns.get_mut(&token).and_then(|c| c.subs.iter().position(|s| s.sub_id == sid).map(|i| c.subs.swap_remove(i).topic));
            if let Some(ot) = old { self.topic_remove(&ot, token, sid); }
            if let SubOp::Add(sid, topic, channel, params) = op {
                if let Some(c) = self.conns.get_mut(&token) {
                    c.subs.push(WsSub { sub_id: sid, topic: topic.clone(), channel, params });
                }
                self.topics.entry(topic).or_default().push((token, sid));
            }
        }
        stay_open
    }

    fn handle_readable(&mut self, token: u64, hangup: bool) {
        let mut buf = [0u8; 8192];
        let (mut closed, mut got_bytes) = (false, false);
        if let Some(c) = self.conns.get_mut(&token) {
            loop {
                let n = unsafe { libc::read(c.fd, buf.as_mut_ptr() as *mut libc::c_void, buf.len()) };
                if n > 0 {
                    c.rx.extend_from_slice(&buf[..n as usize]);
                    c.last_active = Instant::now();
                    got_bytes = true;
                    if c.rx.len() >= 34 * 1024 * 1024 { closed = true; break; }
                } else if n == 0 {
                    c.peer_eof = true;
                    break;
                } else {
                    let e = last_errno();
                    if e == libc::EINTR { continue; }
                    if is_wouldblock(e) { break; }
                    closed = true;
                    break;
                }
            }
        } else { return; }
        if closed { self.close_conn(token); return; }
        if got_bytes && !self.process_rx(token) && self.conns.get(&token).is_none_or(|c| c.tx.is_empty()) {
            self.close_conn(token);
            return;
        }
        if self.conns.get(&token).is_some_and(|c| c.tx.is_empty() && (c.close_after_tx || ((c.peer_eof || hangup) && (c.rx.is_empty() || c.is_ws)))) {
            self.close_conn(token);
        }
    }

    fn handle_writable(&mut self, token: u64) {
        let close = self.conns.get_mut(&token).is_some_and(|c| {
            !c.flush_tx(&self.poller) || (c.tx.is_empty() && (c.close_after_tx || (c.peer_eof && c.rx.is_empty())))
        });
        if close { self.close_conn(token); }
    }

    fn run(mut self) {
        let mut events = Vec::with_capacity(128);
        let mut last_sweep = Instant::now();
        while !STOP.load(Ordering::Relaxed) {
            self.poller.wait(&mut events, 250);
            for ev in events.drain(..) {
                match ev.token {
                    TOKEN_LISTEN => self.accept_all(),
                    TOKEN_WAKE => self.drain_inbox(),
                    t => {
                        if ev.readable || ev.hangup { self.handle_readable(t, ev.hangup); }
                        if ev.writable && self.conns.contains_key(&t) { self.handle_writable(t); }
                    }
                }
            }
            let now = Instant::now();
            if now.duration_since(last_sweep) >= Duration::from_secs(5) {
                last_sweep = now;
                self.sweep_idle(now);
            }
        }
        for t in self.conns.keys().copied().collect::<Vec<_>>() { self.close_conn(t); }
        unsafe { libc::close(self.listen_fd) };
    }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_run(
    port_in: u16,
    num_workers_in: u32,
    init_frag: *mut LeanObj,
    on_head: *mut LeanObj,
    on_body: *mut LeanObj,
    on_ws_bytes: *mut LeanObj,
    on_ws_leave: *mut LeanObj,
) -> *mut LeanObj {
    libc::signal(libc::SIGPIPE, libc::SIG_IGN);
    let mut sa: libc::sigaction = std::mem::zeroed();
    sa.sa_sigaction = handle_stop_signal as *const () as usize;
    libc::sigaction(libc::SIGINT, &sa, std::ptr::null_mut());
    libc::sigaction(libc::SIGTERM, &sa, std::ptr::null_mut());
    STOP.store(false, Ordering::SeqCst);

    let cbs = Arc::new(Callbacks {
        init_frag: LeanRef::new_mt(init_frag),
        on_head: LeanRef::new_mt(on_head),
        on_body: LeanRef::new_mt(on_body),
        on_ws_bytes: LeanRef::new_mt(on_ws_bytes),
        on_ws_leave: LeanRef::new_mt(on_ws_leave),
    });
    let num_workers = if num_workers_in == 0 {
        thread::available_parallelism().map_or(2, |n| n.get()).clamp(1, 16) as u32
    } else { num_workers_in };

    let first_fd = match create_listener(port_in, num_workers > 1) {
        Ok(fd) => fd,
        Err(e) => { eprintln!("✗ failed to bind port {port_in}: {e}"); return qed_lean_io_mk_ok(qed_lean_box_u32(1)); }
    };
    let port = if port_in == 0 { bound_port(first_fd) } else { port_in };
    let inboxes: Vec<Arc<WorkerInbox>> = (0..num_workers).map(|_| Arc::new(WorkerInbox::new())).collect();
    *lock_unpoison(&INBOXES) = inboxes.clone();

    println!("▸ qed native server listening on http://127.0.0.1:{port} ({num_workers} worker{})", if num_workers == 1 { "" } else { "s" });
    let _ = io::stdout().flush();

    let run_worker = |lfd: libc::c_int, inbox: Arc<WorkerInbox>, cbs: Arc<Callbacks>| {
        let Ok(poller) = Poller::new() else { unsafe { libc::close(lfd) }; return; };
        poller.add_read(lfd, TOKEN_LISTEN);
        if inbox.wake_rfd >= 0 { poller.add_read(inbox.wake_rfd, TOKEN_WAKE); }
        Worker { poller, listen_fd: lfd, inbox, cbs, next_token: 16, conns: HashMap::new(), topics: HashMap::new() }.run();
    };

    let handles: Vec<_> = (1..num_workers).map(|i| {
        let (inbox, cbs_c) = (inboxes[i as usize].clone(), cbs.clone());
        thread::spawn(move || {
            unsafe { lean_initialize_thread() };
            if let Ok(lfd) = create_listener(port, true) { run_worker(lfd, inbox, cbs_c); }
            unsafe { lean_finalize_thread() };
        })
    }).collect();
    run_worker(first_fd, inboxes[0].clone(), cbs.clone());
    for h in handles { let _ = h.join(); }
    lock_unpoison(&INBOXES).clear();
    qed_lean_io_mk_ok(qed_lean_box_u32(0))
}
