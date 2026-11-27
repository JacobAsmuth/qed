use std::{collections::{HashMap, HashSet, VecDeque}, io::{self, Write}, net::{IpAddr, Ipv4Addr, Ipv6Addr}, str::FromStr, thread, time::{Duration, Instant}};
use std::sync::{atomic::{AtomicBool, AtomicUsize, Ordering}, Arc, Condvar, Mutex, OnceLock, RwLock};

use crate::lean_ffi::*;
use crate::{WakeFd, close_fd, is_wouldblock, last_errno, lock_unpoison, read_unpoison, set_sockopt, wait_unpoison, write_unpoison};

const MAX_REQ_HDR_BYTES: usize = 65536;
const MAX_RX_BUF_BYTES: usize = 34 * 1024 * 1024;
const MAX_TX_BUF_BYTES: usize = 8 * 1024 * 1024;
const MAX_TX_SEND_ITERS: usize = 16;
const COMPACT_THRESHOLD: usize = 65536;
const TOKEN_LISTEN: u64 = 1;
const TOKEN_WAKE: u64 = 2;
const RL_SHARDS: usize = 16;
const RL_MAX_ENTRIES_PER_SHARD: usize = 4096;

fn env_parse<T: FromStr>(k: &str) -> Option<T> { std::env::var(k).ok().and_then(|s| s.trim().parse().ok()) }

// ---- Sharded Per-IP Token-Bucket Rate Limiter ----

struct IpBucket { tokens_milli: u64, last_ms: u64 }
struct RateLimiter { rps: u64, burst_milli: u64, epoch: Instant, shards: [Mutex<HashMap<IpAddr, IpBucket>>; RL_SHARDS] }
impl RateLimiter {
    fn new(rps: u64, burst: u64) -> Self {
        Self { rps, burst_milli: burst.saturating_mul(1000), epoch: Instant::now(), shards: std::array::from_fn(|_| Mutex::new(HashMap::new())) }
    }
    fn from_env() -> Option<Arc<Self>> {
        let rps = env_parse::<u64>("QED_RATE_LIMIT_RPS").filter(|&r| r > 0)?;
        Some(Arc::new(Self::new(rps, env_parse::<u64>("QED_RATE_LIMIT_BURST").filter(|&b| b > 0).unwrap_or_else(|| rps.saturating_mul(2).max(1)))))
    }
    #[inline] fn shard_idx(ip: IpAddr) -> usize {
        let fnv = |bs: &[u8]| bs.iter().fold(0xcbf29ce484222325u64, |h, &b| (h ^ b as u64).wrapping_mul(0x100000001b3));
        (match ip { IpAddr::V4(v4) => fnv(&v4.octets()), IpAddr::V6(v6) => fnv(&v6.octets()) } as usize) & (RL_SHARDS - 1)
    }
    fn check(&self, ip: IpAddr) -> Result<(), u64> { self.check_at(ip, self.epoch.elapsed().as_millis() as u64) }
    fn check_at(&self, ip: IpAddr, now_ms: u64) -> Result<(), u64> {
        let mut map = lock_unpoison(&self.shards[Self::shard_idx(ip)]);
        if !map.contains_key(&ip) && map.len() >= RL_MAX_ENTRIES_PER_SHARD {
            let cutoff = now_ms.saturating_sub(60_000);
            map.retain(|_, b| b.last_ms >= cutoff);
            if map.len() >= RL_MAX_ENTRIES_PER_SHARD {
                if let Some(k) = map.iter().min_by_key(|(_, b)| b.last_ms).map(|(&k, _)| k) { map.remove(&k); }
            }
        }
        let b = map.entry(ip).or_insert(IpBucket { tokens_milli: self.burst_milli, last_ms: now_ms });
        let elapsed = now_ms.saturating_sub(b.last_ms);
        if elapsed > 0 { b.tokens_milli = b.tokens_milli.saturating_add(elapsed.saturating_mul(self.rps)).min(self.burst_milli); b.last_ms = now_ms; }
        if b.tokens_milli >= 1000 { b.tokens_milli -= 1000; Ok(()) }
        else { Err((1000 - b.tokens_milli).div_ceil(self.rps.saturating_mul(1000).max(1)).max(1)) }
    }
}

static STOP: AtomicBool = AtomicBool::new(false);
static INBOXES: RwLock<Vec<Arc<WorkerInbox>>> = RwLock::new(Vec::new());
static TOPIC_WORKERS: OnceLock<RwLock<HashMap<String, u64>>> = OnceLock::new();
fn topic_workers() -> &'static RwLock<HashMap<String, u64>> { TOPIC_WORKERS.get_or_init(|| RwLock::new(HashMap::new())) }
extern "C" fn handle_stop_signal(_: libc::c_int) { STOP.store(true, Ordering::SeqCst); }

// ---- Cursor-Based RX Byte Queue & Incremental Header Scanner ----

#[derive(Default)]
struct ByteQueue { buf: Vec<u8>, pos: usize }
impl ByteQueue {
    #[inline] fn as_slice(&self) -> &[u8] { &self.buf[self.pos..] }
    #[inline] fn len(&self) -> usize { self.buf.len() - self.pos }
    #[inline] fn is_empty(&self) -> bool { self.pos >= self.buf.len() }
    fn write_spare(&mut self, want: usize, max_len: usize, f: impl FnOnce(*mut u8, usize) -> isize) -> (isize, usize) {
        if self.pos >= self.buf.len() { self.buf.clear(); self.pos = 0; }
        let cap = want.min(max_len.saturating_sub(self.len()));
        if cap == 0 { return (0, 0); }
        self.buf.reserve(cap);
        let spare = self.buf.spare_capacity_mut();
        let wlen = spare.len().min(cap);
        let n = f(spare.as_mut_ptr() as *mut u8, wlen);
        if n > 0 { unsafe { self.buf.set_len(self.buf.len() + (n as usize).min(wlen)); } }
        (n, wlen)
    }
    fn consume(&mut self, n: usize) {
        self.pos += n.min(self.len());
        if self.pos >= self.buf.len() {
            self.buf.clear(); self.pos = 0;
            if self.buf.capacity() > COMPACT_THRESHOLD { self.buf.shrink_to(4096); }
        } else if self.pos >= COMPACT_THRESHOLD && self.pos * 2 >= self.buf.len() {
            let rem = self.buf.len() - self.pos;
            self.buf.copy_within(self.pos.., 0); self.buf.truncate(rem); self.pos = 0;
        }
    }
}

/// Incremental Boyer-Moore-style scan for `\r\n\r\n`, resuming across fragmented reads in O(N).
fn find_header_end(slice: &[u8], scanned: &mut usize) -> Option<usize> {
    let mut i = (*scanned).saturating_sub(3);
    while i + 3 < slice.len() {
        match slice[i + 3] {
            b'\n' if &slice[i..i + 3] == b"\r\n\r" => { *scanned = 0; return Some(i); }
            b'\n' => i += 2, b'\r' => i += 1, _ => i += 4,
        }
    }
    *scanned = slice.len(); None
}

// ---- Generational Connection Slab (O(1) Indexed Lookup, ABA-Safe, Token >= 65536 > 16) ----

struct ConnSlot<T> { gen: u64, val: Option<T> }
struct ConnSlab<T = Conn> { slots: Vec<ConnSlot<T>>, free: Vec<u32>, len: usize }
impl<T> ConnSlab<T> {
    fn new() -> Self { Self { slots: Vec::new(), free: Vec::new(), len: 0 } }
    #[inline] fn len(&self) -> usize { self.len }
    #[inline] fn encode(i: usize, g: u64) -> u64 { (g << 16) | (i as u64) }
    #[inline] fn decode(t: u64) -> Option<(usize, u64)> { let g = t >> 16; (g != 0).then_some(((t & 0xFFFF) as usize, g)) }
    #[inline] fn next_gen(g: u64) -> u64 { (g.wrapping_add(1) & 0x0000_FFFF_FFFF_FFFF).max(1) }
    fn alloc_slot(&mut self) -> (u32, u64) {
        if let Some(i) = self.free.pop() { (i, Self::encode(i as usize, self.slots[i as usize].gen)) } else {
            let i = self.slots.len() as u32; debug_assert!(i <= 0xFFFF);
            self.slots.push(ConnSlot { gen: 1, val: None }); (i, Self::encode(i as usize, 1))
        }
    }
    fn insert_at(&mut self, idx: u32, val: T) { self.slots[idx as usize].val = Some(val); self.len += 1; }
    fn cancel_slot(&mut self, idx: u32) { let s = &mut self.slots[idx as usize]; s.gen = Self::next_gen(s.gen); self.free.push(idx); }
    #[inline] fn get(&self, t: u64) -> Option<&T> { let (i, g) = Self::decode(t)?; self.slots.get(i).filter(|s| s.gen == g).and_then(|s| s.val.as_ref()) }
    #[inline] fn get_mut(&mut self, t: u64) -> Option<&mut T> { let (i, g) = Self::decode(t)?; self.slots.get_mut(i).filter(|s| s.gen == g).and_then(|s| s.val.as_mut()) }
    fn remove(&mut self, t: u64) -> Option<T> {
        let (i, g) = Self::decode(t)?;
        let s = self.slots.get_mut(i).filter(|s| s.gen == g)?;
        let val = s.val.take()?;
        s.gen = Self::next_gen(s.gen); self.free.push(i as u32); self.len -= 1; Some(val)
    }
    fn iter_mut(&mut self) -> impl Iterator<Item = (u64, &mut T)> {
        self.slots.iter_mut().enumerate().filter_map(|(i, s)| s.val.as_mut().map(|v| (Self::encode(i, s.gen), v)))
    }
}

// ---- Cross-Worker WebSocket Broadcast & Blocking Handler Pool ----

struct BcastMsg { topic: String, payload: Vec<u8> }
enum SubOp { Add(u32, String, String, Vec<u8>), Remove(u32) }
enum DoneEvent {
    Http { token: u64, resp: Option<LeanRef>, keep_alive: bool },
    WsUpgrade { token: u64, resp: LeanRef, ws_ctx: LeanRef },
    WsStep { token: u64, ws_ctx: LeanRef, consumed: usize, out_wire: Option<LeanRef>, close: bool, new_frag: Option<LeanRef>, ops: Vec<SubOp> },
}

struct WorkerInbox { done: Mutex<VecDeque<DoneEvent>>, bcast: Mutex<VecDeque<Arc<BcastMsg>>>, wake_fd: WakeFd, wake_pending: AtomicBool, ws_subs: AtomicUsize }
impl WorkerInbox {
    fn new() -> Self { Self { done: Mutex::new(VecDeque::new()), bcast: Mutex::new(VecDeque::new()), wake_fd: WakeFd::new(), wake_pending: AtomicBool::new(false), ws_subs: AtomicUsize::new(0) } }
    fn push_done(&self, ev: DoneEvent) { lock_unpoison(&self.done).push_back(ev); self.wake(); }
    fn push_bcast(&self, msg: Arc<BcastMsg>) {
        let mut q = lock_unpoison(&self.bcast); if q.len() >= 16384 { q.pop_front(); } q.push_back(msg); drop(q); self.wake();
    }
    fn wake(&self) { if !self.wake_pending.swap(true, Ordering::SeqCst) { self.wake_fd.wake(); } }
    fn drain_wake(&self) { self.wake_fd.drain(); self.wake_pending.store(false, Ordering::SeqCst); }
}

struct Callbacks { init_frag: LeanRef, on_head: LeanRef, on_body: LeanRef, on_ws_bytes: LeanRef, on_ws_leave: LeanRef, on_ws_project: Option<LeanRef> }
enum PoolJob {
    Head { token: u64, head_ba: LeanRef, ip: LeanRef, inbox: Arc<WorkerInbox> },
    Body { token: u64, req: LeanRef, body: LeanRef, ip: LeanRef, keep_alive: bool, inbox: Arc<WorkerInbox> },
    WsStep { token: u64, ws_ctx: LeanRef, rx_ba: LeanRef, rx_len: usize, frag: LeanRef, subs_arr: LeanRef, inbox: Arc<WorkerInbox> },
    WsLeave { ws_ctx: LeanRef, channel: String, params: Vec<u8> },
}

struct BlockingPool { queue: Mutex<(VecDeque<PoolJob>, usize, bool)>, cv: Condvar, idle_hint: AtomicUsize, handles: Mutex<Vec<thread::JoinHandle<()>>> }
impl BlockingPool {
    fn new(num_threads: usize, cbs: Arc<Callbacks>) -> Arc<Self> {
        let pool = Arc::new(Self { queue: Mutex::new((VecDeque::new(), 0, false)), cv: Condvar::new(), idle_hint: AtomicUsize::new(0), handles: Mutex::new(Vec::new()) });
        *lock_unpoison(&pool.handles) = (0..num_threads).map(|_| {
            let (p, c) = (pool.clone(), cbs.clone());
            thread::spawn(move || {
                unsafe { lean_initialize_thread() };
                loop {
                    let mut q = lock_unpoison(&p.queue);
                    while q.0.is_empty() && !q.2 {
                        q.1 += 1; p.idle_hint.store(q.1, Ordering::Relaxed);
                        q = wait_unpoison(&p.cv, q);
                        q.1 -= 1; p.idle_hint.store(q.1, Ordering::Relaxed);
                    }
                    let Some(job) = q.0.pop_front() else { break };
                    drop(q); exec_pool_job(&c, job);
                }
                unsafe { lean_finalize_thread() };
            })
        }).collect();
        pool
    }
    fn try_push(&self, job: PoolJob, bounded: bool, idle_only: bool) -> Result<(), PoolJob> {
        let mut q = lock_unpoison(&self.queue);
        if q.2 || if idle_only { q.1 == 0 || !q.0.is_empty() } else { bounded && q.0.len() >= 8192 } { return Err(job); }
        let notify = q.1 > 0; q.0.push_back(job); drop(q);
        if notify { self.cv.notify_one(); } Ok(())
    }
    fn shutdown(&self) {
        { lock_unpoison(&self.queue).2 = true; self.cv.notify_all(); }
        for h in std::mem::take(&mut *lock_unpoison(&self.handles)) { let _ = h.join(); }
    }
}

fn submit_pool_job(pools: &[Arc<BlockingPool>], idx: usize, mut job: PoolJob, bounded: bool) -> bool {
    if pools[idx].idle_hint.load(Ordering::Relaxed) == 0 {
        for off in 1..pools.len() {
            let peer = &pools[(idx + off) % pools.len()];
            if peer.idle_hint.load(Ordering::Relaxed) > 0 { match peer.try_push(job, false, true) { Ok(()) => return true, Err(j) => job = j } }
        }
    }
    pools[idx].try_push(job, bounded, false).is_ok()
}

#[inline] unsafe fn mk_ba_mt(data: &[u8]) -> LeanRef { let ba = mk_ba(data); if !data.is_empty() { lean_mark_mt(ba); } LeanRef(ba) }
unsafe fn mk_ip_lean(ip: IpAddr) -> LeanRef {
    let mut buf = [0u8; 64];
    let n = { let mut c = io::Cursor::new(&mut buf[..]); let _ = write!(c, "{ip}"); c.position() as usize };
    let obj = mk_str(std::str::from_utf8_unchecked(&buf[..n])); lean_mark_mt(obj); LeanRef(obj)
}
unsafe fn build_subs_arr(subs: &[WsSub]) -> LeanRef {
    let mut arr = qed_lean_array_with_cap(subs.len());
    for s in subs { arr = lean_array_push(arr, qed_lean_mk_prod(qed_lean_usize_to_nat(s.sub_id as usize), qed_lean_mk_prod(mk_str(&s.channel), mk_ba(&s.params)))); }
    lean_mark_mt(arr); LeanRef(arr)
}
#[inline] unsafe fn call_on_head<R>(cbs: &Callbacks, head: *mut LeanObj, ip: *mut LeanObj, defer: bool, f: impl FnOnce(*mut LeanObj) -> R) -> Option<R> {
    with_io_ok(lean_apply_4(cbs.on_head.clone_ptr(), head, ip, qed_lean_box(defer as usize), qed_lean_box(0)), f)
}
#[inline] unsafe fn call_on_body<R>(cbs: &Callbacks, req: *mut LeanObj, body: *mut LeanObj, ip: *mut LeanObj, f: impl FnOnce(*mut LeanObj) -> R) -> Option<R> {
    with_io_ok(lean_apply_4(cbs.on_body.clone_ptr(), req, body, ip, qed_lean_box(0)), f)
}

fn exec_pool_job(cbs: &Callbacks, job: PoolJob) {
    match job {
        PoolJob::Head { token, head_ba, ip, inbox } => inbox.push_done(unsafe {
            call_on_head(cbs, head_ba.into_raw(), ip.into_raw(), false, |act| match qed_lean_obj_tag(act) {
                t @ (0 | 1) => DoneEvent::Http { token, resp: Some(LeanRef::clone_mt(qed_lean_ctor_get(act, 0))), keep_alive: t == 1 },
                4 => DoneEvent::WsUpgrade { token, resp: LeanRef::clone_mt(qed_lean_ctor_get(act, 0)), ws_ctx: LeanRef::clone_mt(qed_lean_ctor_get(act, 1)) },
                _ => DoneEvent::Http { token, resp: None, keep_alive: false },
            }).unwrap_or(DoneEvent::Http { token, resp: None, keep_alive: false })
        }),
        PoolJob::Body { token, req, body, ip, keep_alive, inbox } => inbox.push_done(DoneEvent::Http {
            token, resp: unsafe { call_on_body(cbs, req.into_raw(), body.into_raw(), ip.into_raw(), |v| LeanRef::clone_mt(v)) }, keep_alive,
        }),
        PoolJob::WsStep { token, ws_ctx, rx_ba, rx_len, frag, subs_arr, inbox } => {
            let (consumed, out_wire, close, new_frag, ops) = unsafe {
                let res = lean_apply_5(cbs.on_ws_bytes.clone_ptr(), ws_ctx.clone_ptr(), rx_ba.into_raw(), frag.into_raw(), subs_arr.into_raw(), qed_lean_box(0));
                with_io_ok(res, |out| {
                    let (consumed, wire_ba) = (qed_lean_usize_of_nat(qed_lean_ctor_get(out, 0)).min(rx_len), qed_lean_ctor_get(out, 1));
                    let out_wire = (!ba_slice(wire_ba).is_empty()).then(|| LeanRef::clone_mt(wire_ba));
                    let (close, new_frag, ops_arr) = (qed_lean_usize_of_nat(qed_lean_ctor_get(out, 2)) != 0, Some(LeanRef::clone_mt(qed_lean_ctor_get(out, 3))), qed_lean_ctor_get(out, 4));
                    let ops = (0..qed_lean_array_size(ops_arr)).filter_map(|i| {
                        let op = qed_lean_array_get_core(ops_arr, i);
                        let sid = qed_lean_usize_of_nat(qed_lean_ctor_get(op, 0)) as u32;
                        match qed_lean_obj_tag(op) {
                            0 => Some(SubOp::Add(sid, str_slice(qed_lean_ctor_get(op, 1)).to_owned(), str_slice(qed_lean_ctor_get(op, 2)).to_owned(), ba_slice(qed_lean_ctor_get(op, 3)).to_vec())),
                            1 => Some(SubOp::Remove(sid)), _ => None,
                        }
                    }).collect();
                    (consumed, out_wire, close, new_frag, ops)
                }).unwrap_or((rx_len, None, true, None, Vec::new()))
            };
            inbox.push_done(DoneEvent::WsStep { token, ws_ctx, consumed, out_wire, close, new_frag, ops });
        }
        PoolJob::WsLeave { ws_ctx, channel, params } => unsafe { qed_lean_dec(lean_apply_4(cbs.on_ws_leave.clone_ptr(), ws_ctx.into_raw(), mk_str(&channel), mk_ba(&params), qed_lean_box(0))); },
    }
}

// ---- Platform Event Loop (Linux epoll / macOS kqueue) ----

struct PollEvent { token: u64, readable: bool, writable: bool, hangup: bool }
struct Poller(libc::c_int);
impl Drop for Poller { fn drop(&mut self) { close_fd(self.0); } }

#[cfg(target_os = "linux")]
impl Poller {
    fn new() -> io::Result<Self> { let fd = unsafe { libc::epoll_create1(libc::EPOLL_CLOEXEC) }; if fd < 0 { Err(io::Error::last_os_error()) } else { Ok(Self(fd)) } }
    fn ctl(&self, op: libc::c_int, sock: libc::c_int, ev: libc::c_int, token: u64) -> bool {
        let mut e = libc::epoll_event { events: ev as u32, u64: token }; unsafe { libc::epoll_ctl(self.0, op, sock, &mut e) == 0 }
    }
    fn add_read(&self, sock: libc::c_int, token: u64) -> bool { self.ctl(libc::EPOLL_CTL_ADD, sock, libc::EPOLLIN | libc::EPOLLRDHUP, token) }
    fn set_write(&self, sock: libc::c_int, token: u64, w: bool) { let _ = self.ctl(libc::EPOLL_CTL_MOD, sock, libc::EPOLLIN | libc::EPOLLRDHUP | if w { libc::EPOLLOUT } else { 0 }, token); }
    fn remove(&self, sock: libc::c_int) { unsafe { let _ = libc::epoll_ctl(self.0, libc::EPOLL_CTL_DEL, sock, std::ptr::null_mut()); } }
    fn wait(&self, out: &mut Vec<PollEvent>, ms: i32) {
        out.clear();
        unsafe {
            let mut evs: [libc::epoll_event; 128] = std::mem::zeroed();
            let n = libc::epoll_wait(self.0, evs.as_mut_ptr(), 128, ms);
            for ev in &evs[..n.max(0) as usize] {
                let f = ev.events as i32;
                out.push(PollEvent { token: ev.u64, readable: (f & libc::EPOLLIN) != 0, writable: (f & libc::EPOLLOUT) != 0, hangup: (f & (libc::EPOLLERR | libc::EPOLLHUP | libc::EPOLLRDHUP)) != 0 });
            }
        }
    }
}
#[cfg(target_os = "macos")]
impl Poller {
    fn new() -> io::Result<Self> { let fd = unsafe { libc::kqueue() }; if fd < 0 { Err(io::Error::last_os_error()) } else { Ok(Self(fd)) } }
    fn kev(&self, sock: libc::c_int, filter: i16, flags: u16, token: u64) -> bool {
        let k = libc::kevent { ident: sock as usize, filter, flags, fflags: 0, data: 0, udata: token as *mut libc::c_void };
        unsafe { libc::kevent(self.0, &k, 1, std::ptr::null_mut(), 0, std::ptr::null()) == 0 }
    }
    fn add_read(&self, sock: libc::c_int, token: u64) -> bool { self.kev(sock, libc::EVFILT_READ, libc::EV_ADD | libc::EV_ENABLE, token) }
    fn set_write(&self, sock: libc::c_int, token: u64, w: bool) { let _ = self.kev(sock, libc::EVFILT_WRITE, if w { libc::EV_ADD | libc::EV_ENABLE } else { libc::EV_DELETE }, token); }
    fn remove(&self, _: libc::c_int) {}
    fn wait(&self, out: &mut Vec<PollEvent>, ms: i32) {
        out.clear();
        unsafe {
            let (mut evs, ts): ([libc::kevent; 128], _) = (std::mem::zeroed(), libc::timespec { tv_sec: (ms / 1000) as libc::time_t, tv_nsec: ((ms % 1000) * 1_000_000) as libc::c_long });
            let n = libc::kevent(self.0, std::ptr::null(), 0, evs.as_mut_ptr(), 128, &ts);
            for ev in &evs[..n.max(0) as usize] {
                out.push(PollEvent { token: ev.udata as u64, readable: ev.filter == libc::EVFILT_READ, writable: ev.filter == libc::EVFILT_WRITE, hangup: (ev.flags & (libc::EV_EOF | libc::EV_ERROR)) != 0 });
            }
        }
    }
}

// ---- Low-Level Socket Helpers (IPv4 & IPv6) ----

fn parse_bind_ip(host: &str) -> io::Result<IpAddr> {
    let t = host.trim();
    if t.is_empty() { return Ok(IpAddr::V4(Ipv4Addr::UNSPECIFIED)); }
    IpAddr::from_str(t.strip_prefix('[').and_then(|s| s.strip_suffix(']')).unwrap_or(t)).map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, format!("invalid bind IP `{host}`")))
}
fn create_listener(bind_ip: IpAddr, port: u16, allow_reuseport: bool) -> io::Result<libc::c_int> {
    unsafe {
        #[cfg(target_os = "linux")] let ty = libc::SOCK_STREAM | libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC;
        #[cfg(not(target_os = "linux"))] let ty = libc::SOCK_STREAM;
        let fd = libc::socket(if bind_ip.is_ipv4() { libc::AF_INET } else { libc::AF_INET6 }, ty, 0);
        if fd < 0 { return Err(io::Error::last_os_error()); }
        set_sockopt(fd, libc::SOL_SOCKET, libc::SO_REUSEADDR, 1);
        if allow_reuseport { set_sockopt(fd, libc::SOL_SOCKET, libc::SO_REUSEPORT, 1); }
        set_sockopt(fd, libc::IPPROTO_TCP, libc::TCP_NODELAY, 1);
        let rc = match bind_ip {
            IpAddr::V4(v4) => { let mut a: libc::sockaddr_in = std::mem::zeroed(); (a.sin_family, a.sin_port, a.sin_addr) = (libc::AF_INET as _, port.to_be(), libc::in_addr { s_addr: u32::from_ne_bytes(v4.octets()) }); libc::bind(fd, &a as *const _ as *const _, std::mem::size_of_val(&a) as _) }
            IpAddr::V6(v6) => { if v6.is_unspecified() { set_sockopt(fd, libc::IPPROTO_IPV6, libc::IPV6_V6ONLY, 0); } let mut a: libc::sockaddr_in6 = std::mem::zeroed(); (a.sin6_family, a.sin6_port, a.sin6_addr) = (libc::AF_INET6 as _, port.to_be(), libc::in6_addr { s6_addr: v6.octets() }); libc::bind(fd, &a as *const _ as *const _, std::mem::size_of_val(&a) as _) }
        };
        if rc != 0 || libc::listen(fd, 4096) != 0 { let err = io::Error::last_os_error(); close_fd(fd); return Err(err); }
        #[cfg(not(target_os = "linux"))] crate::set_nonblocking(fd);
        Ok(fd)
    }
}
fn bound_port(fd: libc::c_int) -> u16 { std::mem::ManuallyDrop::new(unsafe { <std::net::TcpListener as std::os::fd::FromRawFd>::from_raw_fd(fd) }).local_addr().map_or(0, |a| a.port()) }
fn peer_ip_addr(st: &libc::sockaddr_storage) -> IpAddr {
    unsafe { match st.ss_family as libc::c_int {
        libc::AF_INET => IpAddr::V4(Ipv4Addr::from((&*(st as *const _ as *const libc::sockaddr_in)).sin_addr.s_addr.to_ne_bytes())),
        libc::AF_INET6 => { let v6 = Ipv6Addr::from((&*(st as *const _ as *const libc::sockaddr_in6)).sin6_addr.s6_addr); v6.to_ipv4_mapped().map_or(IpAddr::V6(v6), IpAddr::V4) }
        _ => IpAddr::V4(Ipv4Addr::UNSPECIFIED),
    }}
}

#[cfg(target_os = "linux")] const SEND_FLAGS: libc::c_int = libc::MSG_NOSIGNAL;
#[cfg(not(target_os = "linux"))] const SEND_FLAGS: libc::c_int = 0;

enum SendRes { Done(usize), WouldBlock, Err }
#[inline] fn iov(s: &[u8]) -> libc::iovec { libc::iovec { iov_base: s.as_ptr() as *mut _, iov_len: s.len() } }
fn send_iovs(fd: libc::c_int, iovs: &[libc::iovec]) -> SendRes {
    let mut msg: libc::msghdr = unsafe { std::mem::zeroed() };
    (msg.msg_iov, msg.msg_iovlen) = (iovs.as_ptr() as *mut _, iovs.len() as _);
    loop {
        match unsafe { libc::sendmsg(fd, &msg, SEND_FLAGS) } {
            n if n > 0 => return SendRes::Done(n as usize), 0 => return SendRes::Err,
            _ => match last_errno() { libc::EINTR => continue, e if is_wouldblock(e) => return SendRes::WouldBlock, _ => return SendRes::Err },
        }
    }
}

// ---- Vectored Zero-Copy TX Chunks & Per-Connection State ----

enum TxBuf { Wire(LeanRef), Owned(Vec<u8>) }
struct TxChunk { buf: TxBuf, off: usize }
impl TxChunk {
    #[inline] fn as_slice(&self) -> &[u8] { let s = match &self.buf { TxBuf::Wire(w) => w.as_bytes(), TxBuf::Owned(v) => v }; &s[self.off..] }
    #[inline] fn len(&self) -> usize { self.as_slice().len() }
}
struct WsSub { sub_id: u32, topic: String, channel: String, params: Vec<u8> }
struct PendingBody { content_len: usize, keep_alive: bool, req: LeanRef, inline: bool }
#[derive(Copy, Clone, Eq, PartialEq)] enum ConnStep { Continue, Done, Close }

struct Conn {
    token: u64, fd: libc::c_int, ip_addr: IpAddr, ip_lean: LeanRef,
    rx: ByteQueue, rx_hdr_scanned: usize, tx: VecDeque<TxChunk>, tx_bytes: usize, tx_armed: bool,
    peer_eof: bool, close_after_tx: bool, in_flight: bool, pending_body: Option<PendingBody>,
    is_ws: bool, ws_ctx: Option<LeanRef>, frag: Option<LeanRef>, subs: Vec<WsSub>, subs_arr: Option<LeanRef>,
    last_active: Instant, last_ping: Instant,
}
impl Conn {
    #[inline] fn consume_rx(&mut self, n: usize) { self.rx.consume(n); self.rx_hdr_scanned = 0; }
    #[inline] fn send_parts(&mut self, poller: &Poller, a: &[u8], b: &[u8], make: impl FnOnce(usize) -> TxChunk) -> bool {
        let total = a.len() + b.len();
        if total == 0 { return true; }
        let off = if self.tx.is_empty() {
            let mut off = 0;
            for _ in 0..MAX_TX_SEND_ITERS {
                let (s1, s2) = if off < a.len() { (&a[off..], b) } else { (&b[off - a.len()..], &[][..]) };
                match send_iovs(self.fd, &[iov(s1), iov(s2)][..1 + usize::from(!s2.is_empty())]) {
                    SendRes::Done(n) => { off += n; if off >= total { return true; } }
                    SendRes::WouldBlock => break, SendRes::Err => return false,
                }
            }
            off
        } else if self.tx_bytes.saturating_add(total) > MAX_TX_BUF_BYTES { return false; } else { 0 };
        let chunk = make(off); self.tx_bytes += chunk.len(); self.tx.push_back(chunk);
        if !self.tx_armed { poller.set_write(self.fd, self.token, true); self.tx_armed = true; }
        true
    }
    fn send_wire(&mut self, poller: &Poller, wire: LeanRef) -> bool { self.send_parts(poller, unsafe { ba_slice(wire.0) }, &[], |off| TxChunk { buf: TxBuf::Wire(wire), off }) }
    /// Inline ST fast path: sends from borrowed Lean ByteArray without `mark_mt` unless queueing in `self.tx`.
    unsafe fn send_borrowed_ba(&mut self, poller: &Poller, ba: *mut LeanObj) -> bool { self.send_parts(poller, ba_slice(ba), &[], |off| TxChunk { buf: TxBuf::Wire(LeanRef::clone_mt(ba)), off }) }
    fn send_slice(&mut self, poller: &Poller, data: &[u8]) -> bool { self.send_parts(poller, data, &[], |off| TxChunk { buf: TxBuf::Owned(data[off..].to_vec()), off: 0 }) }
    fn send_ws_event(&mut self, poller: &Poller, sub_id: u32, payload: &[u8]) -> bool {
        let (total, mut hdr) = (5 + payload.len(), [0x82u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        let hlen = match total {
            0..=125 => { hdr[1] = total as u8; 2 }
            126..=65535 => { hdr[1] = 126; hdr[2..4].copy_from_slice(&(total as u16).to_be_bytes()); 4 }
            _ => { hdr[1] = 127; hdr[2..10].copy_from_slice(&(total as u64).to_be_bytes()); 10 }
        };
        hdr[hlen] = 0x12; hdr[hlen + 1..hlen + 5].copy_from_slice(&sub_id.to_be_bytes());
        let h = &hdr[..hlen + 5];
        self.send_parts(poller, h, payload, |off| {
            let (rh, rp) = if off < h.len() { (&h[off..], payload) } else { (&[][..], &payload[off - h.len()..]) };
            TxChunk { buf: TxBuf::Owned([rh, rp].concat()), off: 0 }
        })
    }
    fn flush_tx(&mut self, poller: &Poller) -> bool {
        for _ in 0..MAX_TX_SEND_ITERS {
            let (mut iovs, mut count): ([libc::iovec; 16], usize) = (unsafe { std::mem::zeroed() }, 0);
            for s in self.tx.iter().take(16).map(TxChunk::as_slice).filter(|s| !s.is_empty()) { iovs[count] = iov(s); count += 1; }
            if count == 0 { self.tx.clear(); self.tx_bytes = 0; break; }
            match send_iovs(self.fd, &iovs[..count]) {
                SendRes::Done(mut sent) => {
                    self.tx_bytes = self.tx_bytes.saturating_sub(sent);
                    while sent > 0 { let fl = self.tx[0].len(); if sent >= fl { sent -= fl; self.tx.pop_front(); } else { self.tx[0].off += sent; sent = 0; } }
                }
                SendRes::WouldBlock => break, SendRes::Err => return false,
            }
        }
        if self.tx.is_empty() && self.tx_armed { poller.set_write(self.fd, self.token, false); self.tx_armed = false; }
        true
    }

    fn ready_to_close(&self, hangup: bool) -> bool {
        !self.in_flight && self.tx.is_empty() && (self.close_after_tx || ((self.peer_eof || hangup) && (self.rx.is_empty() || self.is_ws)))
    }
    fn close_step(&mut self, sent: bool) -> ConnStep { self.close_after_tx = true; if !sent || self.tx.is_empty() { ConnStep::Close } else { ConnStep::Done } }
    fn send_error_close(&mut self, poller: &Poller, status: &str, retry: Option<u64>, body: &str) -> ConnStep {
        let mut buf = [0u8; 256];
        let mut c = io::Cursor::new(&mut buf[..]);
        let _ = write!(c, "HTTP/1.1 {status}\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: {}\r\n", body.len());
        if let Some(ra) = retry { let _ = write!(c, "Retry-After: {ra}\r\n"); }
        let _ = write!(c, "X-Content-Type-Options: nosniff\r\nConnection: close\r\n\r\n{body}");
        let n = c.position() as usize;
        let s = self.send_slice(poller, &buf[..n]); self.close_step(s)
    }
    fn finish_write(&mut self, sent: bool, keep_open: bool, can_cont: bool) -> ConnStep {
        if !sent || !keep_open { self.close_step(sent) } else if self.ready_to_close(false) { ConnStep::Close }
        else if can_cont && !self.rx.is_empty() { ConnStep::Continue } else { ConnStep::Done }
    }
    fn finish_ws_upgrade(&mut self, sent: bool, ws_ctx: LeanRef, init_frag: &LeanRef, now: Instant) -> ConnStep {
        if !sent { return self.close_step(false); }
        (self.is_ws, self.ws_ctx, self.frag, self.subs_arr, self.last_active, self.last_ping) = (true, Some(ws_ctx), Some(init_frag.clone()), None, now, now);
        if self.rx.is_empty() { ConnStep::Done } else { ConnStep::Continue }
    }
    /// Returns `None` iff `on_head` returned tag 7 (`DeferHead` for OIDC WS upgrades).
    fn eval_head_inline(&mut self, poller: &Poller, cbs: &Callbacks, head_end: usize, consume: usize, now: Instant) -> Option<ConnStep> {
        unsafe {
            call_on_head(cbs, mk_ba(&self.rx.as_slice()[..head_end]), self.ip_lean.clone_ptr(), true, |act| {
                let tag = qed_lean_obj_tag(act);
                if tag == 7 { return None; }
                self.consume_rx(consume);
                Some(match tag {
                    t @ (0 | 1) => { let s = self.send_borrowed_ba(poller, qed_lean_ctor_get(act, 0)); self.finish_write(s, t == 1, true) }
                    t @ (2 | 3 | 5 | 6) => {
                        let (cl, req, inline) = (qed_lean_usize_of_nat(qed_lean_ctor_get(act, 0)), qed_lean_ctor_get(act, 1), t <= 3);
                        qed_lean_inc(req); if !inline { lean_mark_mt(req); }
                        self.pending_body = Some(PendingBody { content_len: cl, keep_alive: t == 3 || t == 6, req: LeanRef(req), inline });
                        ConnStep::Continue
                    }
                    4 => { let (ctx, s) = (LeanRef::clone_mt(qed_lean_ctor_get(act, 1)), self.send_borrowed_ba(poller, qed_lean_ctor_get(act, 0))); self.finish_ws_upgrade(s, ctx, &cbs.init_frag, now) }
                    _ => self.close_step(true),
                })
            }).unwrap_or_else(|| { self.consume_rx(consume); Some(self.close_step(true)) })
        }
    }
}

// ---- Per-Worker Event Loop ----

struct Worker {
    poller: Poller, listen_fd: libc::c_int, inbox: Arc<WorkerInbox>, idx: usize, pools: Arc<Vec<Arc<BlockingPool>>>,
    cbs: Arc<Callbacks>, rate_limiter: Option<Arc<RateLimiter>>,
    conns: ConnSlab, topics: HashMap<String, HashSet<(u64, u32)>>,
    done_buf: VecDeque<DoneEvent>, bcast_buf: VecDeque<Arc<BcastMsg>>, now: Instant,
}

fn swap_queue<T>(local: &mut VecDeque<T>, shared: &Mutex<VecDeque<T>>) -> VecDeque<T> {
    let mut b = std::mem::take(local); std::mem::swap(&mut b, &mut *lock_unpoison(shared)); b
}
fn restore_queue<T>(local: &mut VecDeque<T>, mut b: VecDeque<T>) { if b.capacity() > 1024 { b.shrink_to(1024); } *local = b; }

fn topic_remove_from(topics: &mut HashMap<String, HashSet<(u64, u32)>>, inbox: &WorkerInbox, widx: usize, use_bm: bool, topic: &str, token: u64, sid: u32) {
    let Some(subs) = topics.get_mut(topic) else { return };
    if subs.remove(&(token, sid)) { inbox.ws_subs.fetch_sub(1, Ordering::Release); }
    if subs.is_empty() {
        topics.remove(topic);
        if use_bm {
            let mut tw = write_unpoison(topic_workers());
            if let Some(m) = tw.get_mut(topic) { *m &= !(1u64 << widx); if *m == 0 { tw.remove(topic); } }
        }
    }
}

fn apply_ws_sub_ops(topics: &mut HashMap<String, HashSet<(u64, u32)>>, inbox: &WorkerInbox, widx: usize, use_bm: bool, token: u64, conn: &mut Conn, ops: Vec<SubOp>) {
    if ops.is_empty() { return; }
    for op in ops {
        let sid = match &op { SubOp::Add(s, ..) | SubOp::Remove(s) => *s };
        if let Some(i) = conn.subs.iter().position(|s| s.sub_id == sid) {
            let ot = conn.subs.swap_remove(i).topic; topic_remove_from(topics, inbox, widx, use_bm, &ot, token, sid);
        }
        if let SubOp::Add(sid, topic, channel, params) = op {
            conn.subs.push(WsSub { sub_id: sid, topic: topic.clone(), channel, params });
            let set = topics.entry(topic.clone()).or_default(); let first = set.is_empty();
            if set.insert((token, sid)) { inbox.ws_subs.fetch_add(1, Ordering::Release); }
            if first && use_bm { *write_unpoison(topic_workers()).entry(topic).or_insert(0) |= 1u64 << widx; }
        }
    }
    conn.subs_arr = None;
}

impl Worker {
    fn spawn_and_run(listen_fd: libc::c_int, inbox: Arc<WorkerInbox>, idx: usize, pools: Arc<Vec<Arc<BlockingPool>>>, cbs: Arc<Callbacks>, rate_limiter: Option<Arc<RateLimiter>>) {
        let Ok(poller) = Poller::new() else { eprintln!("✗ failed to initialize poller"); close_fd(listen_fd); return; };
        poller.add_read(listen_fd, TOKEN_LISTEN);
        if inbox.wake_fd.read_fd() >= 0 { poller.add_read(inbox.wake_fd.read_fd(), TOKEN_WAKE); }
        Self { poller, listen_fd, inbox, idx, pools, cbs, rate_limiter, conns: ConnSlab::new(), topics: HashMap::new(), done_buf: VecDeque::new(), bcast_buf: VecDeque::new(), now: Instant::now() }.run();
    }
    fn accept_all(&mut self) {
        loop {
            let (mut st, mut len): (libc::sockaddr_storage, _) = (unsafe { std::mem::zeroed() }, std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t);
            let sptr = &mut st as *mut _ as *mut libc::sockaddr;
            #[cfg(target_os = "linux")] let fd = unsafe { libc::accept4(self.listen_fd, sptr, &mut len, libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC) };
            #[cfg(not(target_os = "linux"))] let fd = unsafe { libc::accept(self.listen_fd, sptr, &mut len) };
            if fd < 0 { break; }
            if self.conns.len() >= 4096 { close_fd(fd); continue; }
            #[cfg(not(target_os = "linux"))] crate::set_nonblocking(fd);
            unsafe { set_sockopt(fd, libc::IPPROTO_TCP, libc::TCP_NODELAY, 1) };
            let (slot_idx, token) = self.conns.alloc_slot();
            if !self.poller.add_read(fd, token) { self.conns.cancel_slot(slot_idx); close_fd(fd); continue; }
            let (ip_addr, now) = (peer_ip_addr(&st), self.now);
            self.conns.insert_at(slot_idx, Conn {
                token, fd, ip_addr, ip_lean: unsafe { mk_ip_lean(ip_addr) }, rx: ByteQueue::default(), rx_hdr_scanned: 0,
                tx: VecDeque::new(), tx_bytes: 0, tx_armed: false, peer_eof: false, close_after_tx: false, in_flight: false,
                pending_body: None, is_ws: false, ws_ctx: None, frag: None, subs: Vec::new(), subs_arr: None, last_active: now, last_ping: now,
            });
        }
    }
    fn close_conn(&mut self, token: u64) {
        let Some(conn) = self.conns.remove(token) else { return };
        self.poller.remove(conn.fd); close_fd(conn.fd);
        if let Some(ws_ctx) = conn.ws_ctx {
            let use_bm = self.pools.len() <= 64;
            for sub in conn.subs {
                topic_remove_from(&mut self.topics, &self.inbox, self.idx, use_bm, &sub.topic, token, sub.sub_id);
                let _ = submit_pool_job(&self.pools, self.idx, PoolJob::WsLeave { ws_ctx: ws_ctx.clone(), channel: sub.channel, params: sub.params }, false);
            }
        }
    }
    fn drain_inbox(&mut self) {
        self.inbox.drain_wake();
        let mut done = swap_queue(&mut self.done_buf, &self.inbox.done);
        for ev in done.drain(..) { self.handle_done_event(ev); }
        restore_queue(&mut self.done_buf, done);
        let (mut bcast, mut to_close) = (swap_queue(&mut self.bcast_buf, &self.inbox.bcast), Vec::new());
        for msg in bcast.drain(..) {
            for &(token, sid) in self.topics.get(&msg.topic).into_iter().flatten() {
                let Some(c) = self.conns.get_mut(token).filter(|c| c.is_ws && !c.close_after_tx) else { continue };
                let sent = match &self.cbs.on_ws_project {
                    Some(proj_fn) => {
                        let (Some(ws_ctx), Some(sub)) = (c.ws_ctx.as_ref(), c.subs.iter().find(|s| s.sub_id == sid)) else { continue };
                        unsafe {
                            let out = lean_apply_4(proj_fn.clone_ptr(), ws_ctx.clone_ptr(), mk_str(&sub.channel), mk_ba(&sub.params), mk_ba(&msg.payload));
                            let ok = match qed_lean_obj_tag(out) {
                                0 => c.send_ws_event(&self.poller, sid, &msg.payload),
                                _ => { let inner = qed_lean_ctor_get(out, 0); qed_lean_obj_tag(inner) != 1 || c.send_ws_event(&self.poller, sid, ba_slice(qed_lean_ctor_get(inner, 0))) }
                            };
                            qed_lean_dec(out); ok
                        }
                    }
                    None => c.send_ws_event(&self.poller, sid, &msg.payload),
                };
                if !sent { c.close_after_tx = true; to_close.push(token); }
            }
        }
        restore_queue(&mut self.bcast_buf, bcast);
        for t in to_close { self.close_conn(t); }
    }
    fn handle_done_event(&mut self, ev: DoneEvent) {
        let (token, step) = match ev {
            DoneEvent::Http { token, resp, keep_alive } => (token, self.conns.get_mut(token).map_or(ConnStep::Done, |c| {
                c.in_flight = false; c.last_active = self.now;
                match resp { Some(w) => { let s = c.send_wire(&self.poller, w); c.finish_write(s, keep_alive, true) } None => c.close_step(true) }
            })),
            DoneEvent::WsUpgrade { token, resp, ws_ctx } => (token, self.conns.get_mut(token).map_or(ConnStep::Done, |c| {
                c.in_flight = false; let s = c.send_wire(&self.poller, resp); c.finish_ws_upgrade(s, ws_ctx, &self.cbs.init_frag, self.now)
            })),
            DoneEvent::WsStep { token, ws_ctx, consumed, out_wire, close, new_frag, ops } => {
                let Worker { conns, topics, inbox, poller, idx, pools, now, .. } = self;
                let step = if let Some(c) = conns.get_mut(token) {
                    apply_ws_sub_ops(topics, inbox, *idx, pools.len() <= 64, token, c, ops);
                    c.in_flight = false;
                    if consumed > 0 { c.consume_rx(consumed); c.last_active = *now; }
                    if let Some(f) = new_frag { c.frag = Some(f); }
                    let sent = out_wire.is_none_or(|w| c.send_wire(poller, w));
                    c.finish_write(sent, !close, consumed > 0)
                } else {
                    for op in ops { if let SubOp::Add(_, _, channel, params) = op { let _ = pools[*idx].try_push(PoolJob::WsLeave { ws_ctx: ws_ctx.clone(), channel, params }, false, false); } }
                    ConnStep::Done
                };
                (token, step)
            }
        };
        self.drive_step(token, step);
    }
    fn sweep_idle(&mut self, now: Instant) {
        let mut to_close = Vec::new();
        for (token, c) in self.conns.iter_mut().filter(|(_, c)| !c.in_flight) {
            if now.duration_since(c.last_active) > Duration::from_secs(if c.is_ws { 75 } else { 30 })
                || (c.is_ws && !c.close_after_tx && now.duration_since(c.last_ping) >= Duration::from_secs(25)
                    && { c.last_ping = now; !c.send_slice(&self.poller, &[0x89, 0x00]) })
            { to_close.push(token); }
        }
        for t in to_close { self.close_conn(t); }
    }
    fn step_rx(&mut self, token: u64) -> ConnStep {
        let Worker { poller, inbox, idx, pools, cbs, rate_limiter, conns, now, .. } = self;
        let Some(conn) = conns.get_mut(token).filter(|c| !c.close_after_tx && !c.in_flight) else { return ConnStep::Done };
        let dispatch = |c: &mut Conn, job: PoolJob, send_503: bool| {
            c.in_flight = true;
            if submit_pool_job(pools, *idx, job, true) { ConnStep::Done } else {
                c.in_flight = false;
                if send_503 { c.send_error_close(poller, "503 Service Unavailable", None, "server overloaded\r\n") } else { ConnStep::Close }
            }
        };
        if conn.is_ws {
            if conn.rx.is_empty() { return ConnStep::Done; }
            let (Some(ws_ctx), Some(frag)) = (conn.ws_ctx.clone(), conn.frag.clone()) else { return ConnStep::Close };
            let (rx_len, rx_ba) = (conn.rx.len(), unsafe { mk_ba_mt(conn.rx.as_slice()) });
            let subs_arr = conn.subs_arr.get_or_insert_with(|| unsafe { build_subs_arr(&conn.subs) }).clone();
            return dispatch(conn, PoolJob::WsStep { token, ws_ctx, rx_ba, rx_len, frag, subs_arr, inbox: inbox.clone() }, false);
        }
        if let Some(pb) = &conn.pending_body {
            if conn.rx.len() < pb.content_len { return if conn.peer_eof { ConnStep::Close } else { ConnStep::Done }; }
            let pb = conn.pending_body.take().unwrap();
            let body = unsafe { if pb.inline { LeanRef(mk_ba(&conn.rx.as_slice()[..pb.content_len])) } else { mk_ba_mt(&conn.rx.as_slice()[..pb.content_len]) } };
            if pb.content_len > 0 { conn.consume_rx(pb.content_len); }
            return if pb.inline {
                let sent = unsafe { call_on_body(cbs, pb.req.into_raw(), body.into_raw(), conn.ip_lean.clone_ptr(), |v| conn.send_borrowed_ba(poller, v)).unwrap_or(false) };
                conn.finish_write(sent, pb.keep_alive, true)
            } else { dispatch(conn, PoolJob::Body { token, req: pb.req, body, ip: conn.ip_lean.clone(), keep_alive: pb.keep_alive, inbox: inbox.clone() }, true) };
        }
        let (head_end, consume_len) = match find_header_end(conn.rx.as_slice(), &mut conn.rx_hdr_scanned) {
            Some(p) => (p, p + 4),
            None if conn.rx.len() > MAX_REQ_HDR_BYTES => (MAX_REQ_HDR_BYTES + 1, conn.rx.len()),
            None => return if conn.peer_eof { ConnStep::Close } else { ConnStep::Done },
        };
        if let Some(rl) = rate_limiter.as_ref().filter(|_| !conn.rx.as_slice()[..head_end].starts_with(b"GET /_qed/health ")) {
            if let Err(ra) = rl.check(conn.ip_addr) { return conn.send_error_close(poller, "429 Too Many Requests", Some(ra), "too many requests\r\n"); }
        }
        if let Some(step) = conn.eval_head_inline(poller, cbs, head_end, consume_len, *now) { return step; }
        let (head_ba, ip) = (unsafe { mk_ba_mt(&conn.rx.as_slice()[..head_end]) }, conn.ip_lean.clone());
        conn.consume_rx(consume_len);
        dispatch(conn, PoolJob::Head { token, head_ba, ip, inbox: inbox.clone() }, true)
    }
    fn drive_step(&mut self, token: u64, mut step: ConnStep) {
        loop { match step { ConnStep::Continue => step = self.step_rx(token), ConnStep::Close => { self.close_conn(token); return; } ConnStep::Done => return } }
    }
    fn handle_readable(&mut self, token: u64, hangup: bool) {
        let (mut closed, mut got_bytes, mut want, now) = (false, false, 4096usize, self.now);
        let Some(c) = self.conns.get_mut(token) else { return };
        loop {
            if c.rx.len() >= MAX_RX_BUF_BYTES { closed = true; break; }
            let (n, cap) = c.rx.write_spare(want, MAX_RX_BUF_BYTES, |ptr, cap| unsafe { libc::read(c.fd, ptr as *mut _, cap) });
            if n > 0 { got_bytes = true; if (n as usize) < cap { break; } want = (want * 2).min(65536); }
            else if n == 0 { c.peer_eof = true; break; }
            else { let e = last_errno(); if e == libc::EINTR { continue; } if !is_wouldblock(e) { closed = true; } break; }
        }
        if got_bytes { c.last_active = now; }
        if closed { self.close_conn(token); return; }
        if got_bytes { self.drive_step(token, ConnStep::Continue); }
        if self.conns.get(token).is_some_and(|c| c.ready_to_close(hangup)) { self.close_conn(token); }
    }
    fn run(mut self) {
        let (mut events, mut last_sweep) = (Vec::with_capacity(128), self.now);
        while !STOP.load(Ordering::Relaxed) {
            self.poller.wait(&mut events, 250); self.now = Instant::now();
            for ev in events.drain(..) {
                match ev.token {
                    TOKEN_LISTEN => self.accept_all(), TOKEN_WAKE => self.drain_inbox(),
                    t => {
                        if ev.readable || ev.hangup { self.handle_readable(t, ev.hangup); }
                        if ev.writable && self.conns.get_mut(t).is_some_and(|c| !c.flush_tx(&self.poller) || c.ready_to_close(false)) { self.close_conn(t); }
                    }
                }
            }
            if self.now.duration_since(last_sweep) >= Duration::from_secs(5) { last_sweep = self.now; self.sweep_idle(self.now); }
        }
        for t in self.conns.iter_mut().map(|(t, _)| t).collect::<Vec<_>>() { self.close_conn(t); }
        close_fd(self.listen_fd);
    }
}

ffi_export! {
    qed_server_ws_broadcast(topic_obj: *mut LeanObj, payload_obj: *mut LeanObj) => {
        let (inboxes, topic) = (read_unpoison(&INBOXES), str_slice(topic_obj));
        let mk_msg = || Arc::new(BcastMsg { topic: topic.to_owned(), payload: ba_slice(payload_obj).to_vec() });
        if inboxes.len() <= 64 {
            let mut mask = read_unpoison(topic_workers()).get(topic).copied().unwrap_or(0);
            if mask == 0 { return mk_io_unit(); }
            let msg = mk_msg();
            while mask != 0 { let i = mask.trailing_zeros() as usize; mask &= mask - 1; if let Some(inb) = inboxes.get(i) { inb.push_bcast(msg.clone()); } }
        } else {
            let mut msg = None;
            for inb in inboxes.iter().filter(|i| i.ws_subs.load(Ordering::Acquire) > 0) { inb.push_bcast(msg.get_or_insert_with(mk_msg).clone()); }
        }
        mk_io_unit()
    };
    qed_server_run(
        host_obj: *mut LeanObj, port_in: u16, num_workers_in: u32,
        init_frag: *mut LeanObj, on_head: *mut LeanObj, on_body: *mut LeanObj, on_ws_bytes: *mut LeanObj, on_ws_leave: *mut LeanObj, on_ws_project_opt: *mut LeanObj,
    ) => {
        libc::signal(libc::SIGPIPE, libc::SIG_IGN);
        let mut sa: libc::sigaction = std::mem::zeroed(); sa.sa_sigaction = handle_stop_signal as *const () as usize;
        for sig in [libc::SIGINT, libc::SIGTERM] { libc::sigaction(sig, &sa, std::ptr::null_mut()); }
        STOP.store(false, Ordering::SeqCst);
        let num_workers = if num_workers_in == 0 { thread::available_parallelism().map_or(2, |n| n.get()).clamp(1, 16) as u32 } else { num_workers_in };
        let (bind_ip, first_fd) = match parse_bind_ip(str_slice(host_obj)).map_err(|e| e.to_string()).and_then(|ip| {
            create_listener(ip, port_in, cfg!(target_os = "linux") && num_workers > 1).map(|fd| (ip, fd)).map_err(|e| format!("failed to bind {ip}:{port_in}: {e}"))
        }) {
            Ok(v) => v,
            Err(e) => {
                eprintln!("✗ {e}");
                for obj in [init_frag, on_head, on_body, on_ws_bytes, on_ws_leave, on_ws_project_opt] { qed_lean_dec(obj); }
                return qed_lean_io_mk_ok(qed_lean_box_u32(1));
            }
        };
        let per_w = env_parse::<usize>("QED_BLOCKING_THREADS").map(|n| n.clamp(1, 256).div_ceil(num_workers as usize).max(1))
            .unwrap_or_else(|| (64usize / (num_workers as usize).max(1)).clamp(2, 4));
        let on_ws_project = (qed_lean_obj_tag(on_ws_project_opt) == 1).then(|| { let f = qed_lean_ctor_get(on_ws_project_opt, 0); qed_lean_inc(f); LeanRef::new_persistent(f) });
        qed_lean_dec(on_ws_project_opt);
        let [init_frag, on_head, on_body, on_ws_bytes, on_ws_leave] = [init_frag, on_head, on_body, on_ws_bytes, on_ws_leave].map(|p| LeanRef::new_persistent(p));
        let (cbs, port) = (Arc::new(Callbacks { init_frag, on_head, on_body, on_ws_bytes, on_ws_leave, on_ws_project }), if port_in == 0 { bound_port(first_fd) } else { port_in });
        let inboxes: Vec<_> = (0..num_workers).map(|_| Arc::new(WorkerInbox::new())).collect();
        *write_unpoison(&INBOXES) = inboxes.clone();
        let pools = Arc::new((0..num_workers).map(|_| BlockingPool::new(per_w, cbs.clone())).collect::<Vec<_>>());
        println!("▸ qed native server listening on http://{}:{port} ({num_workers} I/O worker{}, {} handler threads)",
            match bind_ip { IpAddr::V4(v4) => v4.to_string(), IpAddr::V6(v6) => format!("[{v6}]") }, if num_workers == 1 { "" } else { "s" }, per_w * (num_workers as usize));
        let _ = io::stdout().flush();
        let rl = RateLimiter::from_env();
        let handles: Vec<_> = (1..num_workers as usize).map(|idx| {
            let (inbox, ps, cbs_c, rl_c) = (inboxes[idx].clone(), pools.clone(), cbs.clone(), rl.clone());
            #[cfg(not(target_os = "linux"))] let dup_fd = libc::dup(first_fd);
            thread::spawn(move || {
                unsafe { lean_initialize_thread() };
                #[cfg(target_os = "linux")] let fd = create_listener(bind_ip, port, true).map_err(|e| format!("bind {bind_ip}:{port}: {e}"));
                #[cfg(not(target_os = "linux"))] let fd = if dup_fd >= 0 { Ok(dup_fd) } else { Err("dup listener socket".into()) };
                match fd { Ok(lfd) => Worker::spawn_and_run(lfd, inbox, idx, ps, cbs_c, rl_c), Err(e) => eprintln!("✗ worker {idx} failed to {e}") }
                unsafe { lean_finalize_thread() };
            })
        }).collect();
        Worker::spawn_and_run(first_fd, inboxes[0].clone(), 0, pools.clone(), cbs.clone(), rl);
        STOP.store(true, Ordering::SeqCst);
        for inb in &inboxes { inb.wake_fd.wake(); }
        for h in handles { let _ = h.join(); }
        for p in pools.iter() { p.shutdown(); }
        write_unpoison(&INBOXES).clear(); write_unpoison(topic_workers()).clear();
        qed_lean_io_mk_ok(qed_lean_box_u32(0))
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    fn push_via_spare(bq: &mut ByteQueue, data: &[u8], max_len: usize) -> isize {
        bq.write_spare(data.len(), max_len, |ptr, cap| { let n = data.len().min(cap); unsafe { std::ptr::copy_nonoverlapping(data.as_ptr(), ptr, n); } n as isize }).0
    }
    #[test]
    fn byte_queue_direct_append_compact_and_shrink() {
        let (mut q, big) = (ByteQueue::default(), vec![0xABu8; COMPACT_THRESHOLD + 4096]);
        assert_eq!((push_via_spare(&mut q, &big, MAX_RX_BUF_BYTES) as usize, q.len()), (big.len(), big.len()));
        q.consume(COMPACT_THRESHOLD);
        assert_eq!((q.pos, q.as_slice()), (0, &[0xABu8; 4096][..]));
        assert_eq!((push_via_spare(&mut q, &[1, 2, 3, 4], 4098), q.len()), (2, 4098));
        q.consume(4098); assert!(q.is_empty() && q.buf.capacity() <= 4096);
    }
    #[test]
    fn conn_slab_insert_aba_and_token_range() {
        let mut slab: ConnSlab<u32> = ConnSlab::new();
        let ins = |s: &mut ConnSlab<u32>, v| { let (i, t) = s.alloc_slot(); s.insert_at(i, v); (i, t) };
        let ((i1, t1), (_, t2)) = (ins(&mut slab, 100), ins(&mut slab, 200));
        assert!(t1 >= 16 && t2 >= 16 && t2 != t1 && slab.len() == 2 && slab.get(t1) == Some(&100));
        assert_eq!((slab.remove(t1), slab.get(t1)), (Some(100), None));
        let (i3, t3) = ins(&mut slab, 300);
        assert!(i3 == i1 && t3 != t1 && (slab.get(t1).copied(), slab.remove(t1), slab.get(t3).copied()) == (None, None, Some(300)));
        let (ic, tc) = slab.alloc_slot(); slab.cancel_slot(ic);
        assert_eq!((slab.get(tc), slab.len()), (None, 2));
    }
    #[test]
    fn rate_limiter_burst_429_refill_and_eviction() {
        let rl = RateLimiter::new(10, 2);
        for ip in [IpAddr::V4(Ipv4Addr::new(192, 0, 2, 1)), IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1))] {
            assert_eq!((rl.check_at(ip, 0), rl.check_at(ip, 0), rl.check_at(ip, 0).is_err(), rl.check_at(ip, 100), rl.check_at(ip, 100).is_err()), (Ok(()), Ok(()), true, Ok(()), true));
        }
        let rl_ev = RateLimiter::new(100, 1);
        for (hit, ip) in (1u32..).map(|n| IpAddr::V4(Ipv4Addr::from(0x0A00_0000 | n))).filter(|&ip| RateLimiter::shard_idx(ip) == 0).take(RL_MAX_ENTRIES_PER_SHARD + 9).enumerate() {
            assert_eq!(rl_ev.check_at(ip, hit as u64), Ok(()));
        }
        assert!(lock_unpoison(&rl_ev.shards[0]).len() <= RL_MAX_ENTRIES_PER_SHARD);
    }
    #[test]
    fn find_header_end_incremental_and_pipelined() {
        let reqs = b"GET /a HTTP/1.1\r\nHost: x\r\n\r\nGET /b HTTP/1.1\r\nHost: y\r\r\n\r\n";
        let (mut buf, mut scanned, mut found1) = (Vec::new(), 0usize, None);
        for &b in &reqs[..28] { buf.push(b); found1 = find_header_end(&buf, &mut scanned); }
        let mut q = ByteQueue::default(); push_via_spare(&mut q, reqs, MAX_RX_BUF_BYTES);
        let p1 = find_header_end(q.as_slice(), &mut scanned).unwrap(); q.consume(p1 + 4);
        let p2 = find_header_end(q.as_slice(), &mut scanned).unwrap();
        assert_eq!((found1, p1, p2, &q.as_slice()[..p2]), (Some(24), 24, 25, &b"GET /b HTTP/1.1\r\nHost: y\r"[..]));
    }
}
