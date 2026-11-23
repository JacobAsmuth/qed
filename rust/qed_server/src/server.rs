use std::collections::{HashMap, HashSet, VecDeque};
use std::io::{self, Write};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use std::str::FromStr;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock, RwLock};
use std::thread;
use std::time::{Duration, Instant};

use crate::lean_ffi::*;
use crate::{WakeFd, is_wouldblock, last_errno, lock_unpoison, read_unpoison, set_sockopt, wait_unpoison, write_unpoison};

const MAX_REQ_HDR_BYTES: usize = 65536;
const MAX_RX_BUF_BYTES: usize = 34 * 1024 * 1024;
const MAX_TX_BUF_BYTES: usize = 8 * 1024 * 1024;
const MAX_TX_SEND_ITERS: usize = 16;
const MAX_INBOX_BCAST: usize = 16384;
const MAX_POOL_QUEUE: usize = 8192;
const MAX_WORKER_CONNS: usize = 4096;
const COMPACT_THRESHOLD: usize = 65536;
const HTTP_IDLE_TIMEOUT: Duration = Duration::from_secs(30);
const WS_PING_INTERVAL: Duration = Duration::from_secs(25);
const WS_DEAD_TIMEOUT: Duration = Duration::from_secs(75);
const TOKEN_LISTEN: u64 = 1;
const TOKEN_WAKE: u64 = 2;

const RESP_503_WIRE: &[u8] =
    b"HTTP/1.1 503 Service Unavailable\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 19\r\nX-Content-Type-Options: nosniff\r\nConnection: close\r\n\r\nserver overloaded\r\n";

fn env_parse<T: FromStr>(k: &str) -> Option<T> {
    std::env::var(k).ok().and_then(|s| s.trim().parse().ok())
}

// ---- Sharded Per-IP Token-Bucket Rate Limiter (Configurable via QED_RATE_LIMIT_RPS / BURST) ----

const RL_SHARDS: usize = 16;
const RL_MAX_ENTRIES_PER_SHARD: usize = 4096;

struct IpBucket { tokens_milli: u64, last_ms: u64 }

struct RateLimiter {
    rps: u64,
    burst_milli: u64,
    epoch: Instant,
    shards: [Mutex<HashMap<IpAddr, IpBucket>>; RL_SHARDS],
}

impl RateLimiter {
    fn new(rps: u64, burst: u64) -> Self {
        Self {
            rps,
            burst_milli: burst.saturating_mul(1000),
            epoch: Instant::now(),
            shards: std::array::from_fn(|_| Mutex::new(HashMap::new())),
        }
    }

    fn from_env() -> Option<Arc<Self>> {
        let rps = env_parse::<u64>("QED_RATE_LIMIT_RPS").unwrap_or(0);
        if rps == 0 { return None; }
        let burst = env_parse::<u64>("QED_RATE_LIMIT_BURST").filter(|&b| b > 0).unwrap_or_else(|| rps.saturating_mul(2).max(1));
        Some(Arc::new(Self::new(rps, burst)))
    }

    #[inline]
    fn shard_idx(ip: IpAddr) -> usize {
        let fnv = |bs: &[u8]| bs.iter().fold(0xcbf29ce484222325u64, |h, &b| (h ^ b as u64).wrapping_mul(0x100000001b3));
        let h = match ip { IpAddr::V4(v4) => fnv(&v4.octets()), IpAddr::V6(v6) => fnv(&v6.octets()) };
        (h as usize) & (RL_SHARDS - 1)
    }

    fn check(&self, ip: IpAddr) -> Result<(), u64> { self.check_at(ip, self.epoch.elapsed().as_millis() as u64) }

    fn check_at(&self, ip: IpAddr, now_ms: u64) -> Result<(), u64> {
        let mut map = lock_unpoison(&self.shards[Self::shard_idx(ip)]);
        let bucket = if let Some(b) = map.get_mut(&ip) {
            b
        } else {
            if map.len() >= RL_MAX_ENTRIES_PER_SHARD {
                let cutoff = now_ms.saturating_sub(60_000);
                map.retain(|_, b| b.last_ms >= cutoff);
                if map.len() >= RL_MAX_ENTRIES_PER_SHARD {
                    if let Some(k) = map.iter().min_by_key(|(_, b)| b.last_ms).map(|(&k, _)| k) { map.remove(&k); }
                }
            }
            map.entry(ip).or_insert(IpBucket { tokens_milli: self.burst_milli, last_ms: now_ms })
        };
        let elapsed_ms = now_ms.saturating_sub(bucket.last_ms);
        if elapsed_ms > 0 {
            bucket.tokens_milli = bucket.tokens_milli.saturating_add(elapsed_ms.saturating_mul(self.rps)).min(self.burst_milli);
            bucket.last_ms = now_ms;
        }
        if bucket.tokens_milli >= 1000 {
            bucket.tokens_milli -= 1000;
            Ok(())
        } else {
            Err((1000 - bucket.tokens_milli).div_ceil(self.rps.saturating_mul(1000).max(1)).max(1))
        }
    }
}

fn format_429_wire(retry_after: u64, out: &mut [u8; 256]) -> &[u8] {
    let mut cur = io::Cursor::new(&mut out[..]);
    let _ = write!(
        cur,
        "HTTP/1.1 429 Too Many Requests\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: 19\r\nRetry-After: {retry_after}\r\nX-Content-Type-Options: nosniff\r\nConnection: close\r\n\r\ntoo many requests\r\n"
    );
    let n = cur.position() as usize;
    &out[..n]
}

static STOP: AtomicBool = AtomicBool::new(false);
static INBOXES: RwLock<Vec<Arc<WorkerInbox>>> = RwLock::new(Vec::new());
static TOPIC_WORKERS: OnceLock<RwLock<HashMap<String, u64>>> = OnceLock::new();

fn topic_workers() -> &'static RwLock<HashMap<String, u64>> {
    TOPIC_WORKERS.get_or_init(|| RwLock::new(HashMap::new()))
}

extern "C" fn handle_stop_signal(_sig: libc::c_int) { STOP.store(true, Ordering::SeqCst); }

// ---- Cursor-Based RX Byte Queue (Direct Kernel Append, O(1) Consume, Bounded Idle Cap) ----

struct ByteQueue { buf: Vec<u8>, pos: usize }

impl ByteQueue {
    fn new() -> Self { Self { buf: Vec::new(), pos: 0 } }
    #[inline] fn as_slice(&self) -> &[u8] { &self.buf[self.pos..] }
    #[inline] fn len(&self) -> usize { self.buf.len() - self.pos }
    #[inline] fn is_empty(&self) -> bool { self.pos >= self.buf.len() }

    fn write_spare(&mut self, want: usize, max_len: usize, f: impl FnOnce(*mut u8, usize) -> isize) -> (isize, usize) {
        if self.pos >= self.buf.len() { self.buf.clear(); self.pos = 0; }
        let room = max_len.saturating_sub(self.len());
        if room == 0 { return (0, 0); }
        let cap = want.min(room);
        self.buf.reserve(cap);
        let spare = self.buf.spare_capacity_mut();
        let write_len = spare.len().min(cap);
        let n = f(spare.as_mut_ptr() as *mut u8, write_len);
        if n > 0 {
            let written = (n as usize).min(write_len);
            unsafe { self.buf.set_len(self.buf.len() + written); }
        }
        (n, write_len)
    }

    fn consume(&mut self, n: usize) {
        self.pos += n.min(self.len());
        if self.pos >= self.buf.len() {
            self.buf.clear();
            self.pos = 0;
            if self.buf.capacity() > COMPACT_THRESHOLD { self.buf.shrink_to(4096); }
        } else if self.pos >= COMPACT_THRESHOLD && self.pos * 2 >= self.buf.len() {
            let rem = self.buf.len() - self.pos;
            self.buf.copy_within(self.pos.., 0);
            self.buf.truncate(rem);
            self.pos = 0;
        }
    }
}

/// Incremental Boyer-Moore-style scan for `\r\n\r\n`, resuming across fragmented reads in O(N).
fn find_header_end(slice: &[u8], scanned: &mut usize) -> Option<usize> {
    let mut i = (*scanned).saturating_sub(3);
    while i + 3 < slice.len() {
        match slice[i + 3] {
            b'\n' if &slice[i..i + 3] == b"\r\n\r" => { *scanned = 0; return Some(i); }
            b'\n' => i += 2,
            b'\r' => i += 1,
            _ => i += 4,
        }
    }
    *scanned = slice.len();
    None
}

// ---- Generational Connection Slab (O(1) Indexed Lookup, ABA-Safe, Token >= 65536 > 16) ----

struct ConnSlot<T> { gen: u64, val: Option<T> }
struct ConnSlab<T = Conn> { slots: Vec<ConnSlot<T>>, free: Vec<u32>, len: usize }

impl<T> ConnSlab<T> {
    fn new() -> Self { Self { slots: Vec::new(), free: Vec::new(), len: 0 } }
    #[inline] fn len(&self) -> usize { self.len }
    #[inline] fn encode(idx: usize, gen: u64) -> u64 { (gen << 16) | (idx as u64) }
    #[inline] fn decode(token: u64) -> Option<(usize, u64)> {
        let gen = token >> 16;
        (gen != 0).then_some(((token & 0xFFFF) as usize, gen))
    }
    #[inline] fn next_gen(gen: u64) -> u64 { (gen.wrapping_add(1) & 0x0000_FFFF_FFFF_FFFF).max(1) }

    fn alloc_slot(&mut self) -> (u32, u64) {
        if let Some(idx) = self.free.pop() {
            (idx, Self::encode(idx as usize, self.slots[idx as usize].gen))
        } else {
            let idx = self.slots.len() as u32;
            debug_assert!(idx <= 0xFFFF);
            self.slots.push(ConnSlot { gen: 1, val: None });
            (idx, Self::encode(idx as usize, 1))
        }
    }
    fn insert_at(&mut self, idx: u32, val: T) { self.slots[idx as usize].val = Some(val); self.len += 1; }
    fn cancel_slot(&mut self, idx: u32) {
        let s = &mut self.slots[idx as usize];
        s.gen = Self::next_gen(s.gen);
        self.free.push(idx);
    }
    #[inline] fn get(&self, token: u64) -> Option<&T> {
        let (idx, gen) = Self::decode(token)?;
        self.slots.get(idx).filter(|s| s.gen == gen).and_then(|s| s.val.as_ref())
    }
    #[inline] fn get_mut(&mut self, token: u64) -> Option<&mut T> {
        let (idx, gen) = Self::decode(token)?;
        self.slots.get_mut(idx).filter(|s| s.gen == gen).and_then(|s| s.val.as_mut())
    }
    fn remove(&mut self, token: u64) -> Option<T> {
        let (idx, gen) = Self::decode(token)?;
        let s = self.slots.get_mut(idx).filter(|s| s.gen == gen)?;
        let val = s.val.take()?;
        s.gen = Self::next_gen(s.gen);
        self.free.push(idx as u32);
        self.len -= 1;
        Some(val)
    }
    fn iter_mut(&mut self) -> impl Iterator<Item = (u64, &mut T)> {
        self.slots.iter_mut().enumerate().filter_map(|(i, s)| s.val.as_mut().map(|v| (Self::encode(i, s.gen), v)))
    }
}

// ---- Cross-Worker WebSocket Broadcast & Blocking-Pool Completion Inbox ----

struct BcastMsg { topic: String, payload: Vec<u8> }
enum SubOp { Add(u32, String, String, Vec<u8>), Remove(u32) }

enum DoneEvent {
    Http { token: u64, resp: Option<WireBytes>, keep_alive: bool },
    WsUpgrade { token: u64, resp: WireBytes, ws_ctx: LeanRef },
    WsStep {
        token: u64,
        ws_ctx: LeanRef,
        consumed: usize,
        out_wire: Option<WireBytes>,
        close: bool,
        new_frag: Option<LeanRef>,
        ops: Vec<SubOp>,
    },
}

struct WorkerInbox {
    done_queue: Mutex<Vec<DoneEvent>>,
    bcast_queue: Mutex<VecDeque<Arc<BcastMsg>>>,
    wake_fd: WakeFd,
    wake_pending: AtomicBool,
    ws_subs: AtomicUsize,
}

impl WorkerInbox {
    fn new() -> Self {
        Self {
            done_queue: Mutex::new(Vec::new()), bcast_queue: Mutex::new(VecDeque::new()),
            wake_fd: WakeFd::new(), wake_pending: AtomicBool::new(false), ws_subs: AtomicUsize::new(0),
        }
    }
    fn push_done(&self, ev: DoneEvent) { lock_unpoison(&self.done_queue).push(ev); self.wake(); }
    fn push_bcast(&self, msg: Arc<BcastMsg>) {
        let mut q = lock_unpoison(&self.bcast_queue);
        if q.len() >= MAX_INBOX_BCAST { q.pop_front(); }
        q.push_back(msg);
        drop(q);
        self.wake();
    }
    fn wake(&self) { if !self.wake_pending.swap(true, Ordering::SeqCst) { self.wake_fd.wake(); } }
    fn drain_wake(&self) { self.wake_fd.drain(); self.wake_pending.store(false, Ordering::SeqCst); }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_ws_broadcast(topic_obj: *mut LeanObj, payload_obj: *mut LeanObj) -> *mut LeanObj {
    let inboxes = read_unpoison(&INBOXES);
    let topic = str_slice(topic_obj);
    let mk_msg = || Arc::new(BcastMsg { topic: topic.to_owned(), payload: ba_slice(payload_obj).to_vec() });
    if inboxes.len() <= 64 {
        let mut mask = read_unpoison(topic_workers()).get(topic).copied().unwrap_or(0);
        if mask == 0 { return mk_io_unit(); }
        let msg = mk_msg();
        while mask != 0 {
            let idx = mask.trailing_zeros() as usize;
            mask &= mask - 1;
            if let Some(inbox) = inboxes.get(idx) { inbox.push_bcast(msg.clone()); }
        }
    } else {
        let mut msg: Option<Arc<BcastMsg>> = None;
        for inbox in inboxes.iter() {
            if inbox.ws_subs.load(Ordering::Acquire) == 0 { continue; }
            inbox.push_bcast(msg.get_or_insert_with(mk_msg).clone());
        }
    }
    mk_io_unit()
}

// ---- Dedicated Blocking Handler Pool (Keeps epoll/kqueue Non-Blocking) ----

struct Callbacks {
    init_frag: LeanRef,
    on_head: LeanRef,
    on_body: LeanRef,
    on_ws_bytes: LeanRef,
    on_ws_leave: LeanRef,
}

enum PoolJob {
    /// Used exclusively for WS upgrade requests carrying OIDC auth headers.
    Head { token: u64, head_ba: LeanRef, ip: LeanRef, inbox: Arc<WorkerInbox> },
    Body { token: u64, req: LeanRef, body: LeanRef, ip: LeanRef, keep_alive: bool, inbox: Arc<WorkerInbox> },
    WsStep {
        token: u64,
        ws_ctx: LeanRef,
        rx_ba: LeanRef,
        rx_len: usize,
        frag: LeanRef,
        subs_arr: LeanRef,
        inbox: Arc<WorkerInbox>,
    },
    WsLeave { ws_ctx: LeanRef, channel: String, params: Vec<u8> },
}

struct PoolQueue { jobs: VecDeque<PoolJob>, idle_threads: usize, closed: bool }

struct BlockingPool {
    state: Arc<(Mutex<PoolQueue>, Condvar)>,
    idle_hint: Arc<AtomicUsize>,
    handles: Mutex<Vec<thread::JoinHandle<()>>>,
}

impl BlockingPool {
    fn new(num_threads: usize, cbs: Arc<Callbacks>) -> Arc<Self> {
        let state = Arc::new((Mutex::new(PoolQueue { jobs: VecDeque::new(), idle_threads: 0, closed: false }), Condvar::new()));
        let idle_hint = Arc::new(AtomicUsize::new(0));
        let handles = (0..num_threads).map(|_| {
            let (st, idle_c, cbs_c) = (state.clone(), idle_hint.clone(), cbs.clone());
            thread::spawn(move || {
                unsafe { lean_initialize_thread() };
                loop {
                    let job = {
                        let (lock, cv) = &*st;
                        let mut q = lock_unpoison(lock);
                        while q.jobs.is_empty() && !q.closed {
                            q.idle_threads += 1;
                            idle_c.store(q.idle_threads, Ordering::Relaxed);
                            q = wait_unpoison(cv, q);
                            q.idle_threads -= 1;
                            idle_c.store(q.idle_threads, Ordering::Relaxed);
                        }
                        match q.jobs.pop_front() { Some(j) => j, None => break }
                    };
                    exec_pool_job(&cbs_c, job);
                }
                unsafe { lean_finalize_thread() };
            })
        }).collect();
        Arc::new(Self { state, idle_hint, handles: Mutex::new(handles) })
    }

    fn submit(&self, job: PoolJob, bounded: bool) -> bool {
        let (lock, cv) = &*self.state;
        let notify = {
            let mut q = lock_unpoison(lock);
            if q.closed || (bounded && q.jobs.len() >= MAX_POOL_QUEUE) { return false; }
            q.jobs.push_back(job);
            q.idle_threads > 0
        };
        if notify { cv.notify_one(); }
        true
    }

    fn try_submit_if_idle(&self, job: PoolJob) -> Result<(), PoolJob> {
        let (lock, cv) = &*self.state;
        {
            let mut q = lock_unpoison(lock);
            if q.closed || q.idle_threads == 0 || !q.jobs.is_empty() { return Err(job); }
            q.jobs.push_back(job);
        }
        cv.notify_one();
        Ok(())
    }

    fn shutdown(&self) {
        let (lock, cv) = &*self.state;
        {
            let mut q = lock_unpoison(lock);
            q.closed = true;
            cv.notify_all();
        }
        let handles = std::mem::take(&mut *lock_unpoison(&self.handles));
        for h in handles { let _ = h.join(); }
    }
}

#[inline]
unsafe fn mk_ba_mt(data: &[u8]) -> LeanRef {
    let ba = mk_ba(data);
    if !data.is_empty() { lean_mark_mt(ba); }
    LeanRef(ba)
}

unsafe fn mk_ip_lean(ip: IpAddr) -> LeanRef {
    let mut buf = [0u8; 64];
    let mut cur = io::Cursor::new(&mut buf[..]);
    let _ = write!(cur, "{ip}");
    let n = cur.position() as usize;
    let obj = mk_str(std::str::from_utf8_unchecked(&buf[..n]));
    lean_mark_mt(obj);
    LeanRef(obj)
}

unsafe fn build_subs_arr(subs: &[WsSub]) -> LeanRef {
    let mut arr = qed_lean_array_with_cap(subs.len());
    for s in subs {
        let entry = qed_lean_mk_prod(
            qed_lean_usize_to_nat(s.sub_id as usize),
            qed_lean_mk_prod(mk_str(&s.channel), mk_ba(&s.params)),
        );
        arr = lean_array_push(arr, entry);
    }
    lean_mark_mt(arr);
    LeanRef(arr)
}

fn exec_pool_job(cbs: &Callbacks, job: PoolJob) {
    match job {
        PoolJob::Head { token, head_ba, ip, inbox } => {
            let ev = unsafe {
                let res = lean_apply_4(
                    cbs.on_head.clone_ptr(), head_ba.into_raw(), ip.into_raw(), qed_lean_box(0), qed_lean_box(0),
                );
                with_io_ok(res, |act| match qed_lean_obj_tag(act) {
                    t @ (0 | 1) => DoneEvent::Http {
                        token, resp: Some(WireBytes::from_borrowed(qed_lean_ctor_get(act, 0))), keep_alive: t == 1,
                    },
                    4 => DoneEvent::WsUpgrade {
                        token,
                        resp: WireBytes::from_borrowed(qed_lean_ctor_get(act, 0)),
                        ws_ctx: LeanRef::clone_mt(qed_lean_ctor_get(act, 1)),
                    },
                    _ => DoneEvent::Http { token, resp: None, keep_alive: false },
                }).unwrap_or(DoneEvent::Http { token, resp: None, keep_alive: false })
            };
            inbox.push_done(ev);
        }
        PoolJob::Body { token, req, body, ip, keep_alive, inbox } => {
            let resp = unsafe {
                let res = lean_apply_4(cbs.on_body.clone_ptr(), req.into_raw(), body.into_raw(), ip.into_raw(), qed_lean_box(0));
                with_io_ok(res, |v| WireBytes::from_borrowed(v))
            };
            inbox.push_done(DoneEvent::Http { token, resp, keep_alive });
        }
        PoolJob::WsStep { token, ws_ctx, rx_ba, rx_len, frag, subs_arr, inbox } => {
            let (consumed, out_wire, close, new_frag, ops) = unsafe {
                let res = lean_apply_5(
                    cbs.on_ws_bytes.clone_ptr(), ws_ctx.clone_ptr(),
                    rx_ba.into_raw(), frag.into_raw(), subs_arr.into_raw(), qed_lean_box(0),
                );
                with_io_ok(res, |out| {
                    let consumed = qed_lean_usize_of_nat(qed_lean_ctor_get(out, 0)).min(rx_len);
                    let wire_ba = qed_lean_ctor_get(out, 1);
                    let out_wire = (qed_lean_ba_len(wire_ba) > 0).then(|| WireBytes::from_borrowed(wire_ba));
                    let close = qed_lean_usize_of_nat(qed_lean_ctor_get(out, 2)) != 0;
                    let new_frag = Some(LeanRef::clone_mt(qed_lean_ctor_get(out, 3)));
                    let ops_arr = qed_lean_ctor_get(out, 4);
                    let mut ops = Vec::new();
                    for i in 0..qed_lean_array_size(ops_arr) {
                        let op = qed_lean_array_get_core(ops_arr, i);
                        let sid = qed_lean_usize_of_nat(qed_lean_ctor_get(op, 0)) as u32;
                        match qed_lean_obj_tag(op) {
                            0 => ops.push(SubOp::Add(
                                sid,
                                str_slice(qed_lean_ctor_get(op, 1)).to_owned(),
                                str_slice(qed_lean_ctor_get(op, 2)).to_owned(),
                                ba_slice(qed_lean_ctor_get(op, 3)).to_vec(),
                            )),
                            1 => ops.push(SubOp::Remove(sid)),
                            _ => {}
                        }
                    }
                    (consumed, out_wire, close, new_frag, ops)
                }).unwrap_or((rx_len, None, true, None, Vec::new()))
            };
            inbox.push_done(DoneEvent::WsStep { token, ws_ctx, consumed, out_wire, close, new_frag, ops });
        }
        PoolJob::WsLeave { ws_ctx, channel, params } => unsafe {
            let res = lean_apply_4(
                cbs.on_ws_leave.clone_ptr(), ws_ctx.into_raw(), mk_str(&channel), mk_ba(&params), qed_lean_box(0),
            );
            qed_lean_dec_ref(res);
        },
    }
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

    #[cfg(target_os = "linux")]
    fn ctl(&self, op: libc::c_int, sock: libc::c_int, events: libc::c_int, token: u64) -> bool {
        let mut ev = libc::epoll_event { events: events as u32, u64: token };
        unsafe { libc::epoll_ctl(self.0, op, sock, &mut ev) == 0 }
    }

    #[cfg(target_os = "macos")]
    fn kevent_one(&self, sock: libc::c_int, filter: i16, flags: u16, token: u64) -> bool {
        let kev = libc::kevent { ident: sock as usize, filter, flags, fflags: 0, data: 0, udata: token as *mut libc::c_void };
        unsafe { libc::kevent(self.0, &kev, 1, std::ptr::null_mut(), 0, std::ptr::null()) == 0 }
    }

    fn add_read(&self, sock: libc::c_int, token: u64) -> bool {
        #[cfg(target_os = "linux")]
        { self.ctl(libc::EPOLL_CTL_ADD, sock, libc::EPOLLIN | libc::EPOLLRDHUP, token) }
        #[cfg(target_os = "macos")]
        { self.kevent_one(sock, libc::EVFILT_READ, libc::EV_ADD | libc::EV_ENABLE, token) }
    }

    fn set_write(&self, sock: libc::c_int, token: u64, want_write: bool) {
        #[cfg(target_os = "linux")]
        {
            let ev = libc::EPOLLIN | libc::EPOLLRDHUP | if want_write { libc::EPOLLOUT } else { 0 };
            let _ = self.ctl(libc::EPOLL_CTL_MOD, sock, ev, token);
        }
        #[cfg(target_os = "macos")]
        {
            let fl = if want_write { libc::EV_ADD | libc::EV_ENABLE } else { libc::EV_DELETE };
            let _ = self.kevent_one(sock, libc::EVFILT_WRITE, fl, token);
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
                    token: ev.u64, readable: (f & libc::EPOLLIN) != 0, writable: (f & libc::EPOLLOUT) != 0,
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
                    token: ev.udata as u64, readable: ev.filter == libc::EVFILT_READ, writable: ev.filter == libc::EVFILT_WRITE,
                    hangup: (ev.flags & (libc::EV_EOF | libc::EV_ERROR)) != 0,
                });
            }
        }
    }
}

impl Drop for Poller { fn drop(&mut self) { unsafe { libc::close(self.0) }; } }

// ---- Low-Level Socket Helpers (IPv4 & IPv6) ----

fn parse_bind_ip(host: &str) -> io::Result<IpAddr> {
    let trimmed = host.trim();
    if trimmed.is_empty() { return Ok(IpAddr::V4(Ipv4Addr::UNSPECIFIED)); }
    let clean = trimmed.strip_prefix('[').and_then(|s| s.strip_suffix(']')).unwrap_or(trimmed);
    IpAddr::from_str(clean).map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, format!("invalid bind IP `{host}`")))
}

fn create_listener(bind_ip: IpAddr, port: u16, allow_reuseport: bool) -> io::Result<libc::c_int> {
    unsafe {
        let domain = match bind_ip { IpAddr::V4(_) => libc::AF_INET, IpAddr::V6(_) => libc::AF_INET6 };
        #[cfg(target_os = "linux")]
        let sock_type = libc::SOCK_STREAM | libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC;
        #[cfg(not(target_os = "linux"))]
        let sock_type = libc::SOCK_STREAM;
        let fd = libc::socket(domain, sock_type, 0);
        if fd < 0 { return Err(io::Error::last_os_error()); }
        set_sockopt(fd, libc::SOL_SOCKET, libc::SO_REUSEADDR, 1);
        if allow_reuseport { set_sockopt(fd, libc::SOL_SOCKET, libc::SO_REUSEPORT, 1); }
        set_sockopt(fd, libc::IPPROTO_TCP, libc::TCP_NODELAY, 1);
        let bind_rc = match bind_ip {
            IpAddr::V4(v4) => {
                let mut a: libc::sockaddr_in = std::mem::zeroed();
                a.sin_family = libc::AF_INET as libc::sa_family_t;
                a.sin_port = port.to_be();
                a.sin_addr = libc::in_addr { s_addr: u32::from_ne_bytes(v4.octets()) };
                libc::bind(fd, &a as *const _ as *const libc::sockaddr, std::mem::size_of::<libc::sockaddr_in>() as _)
            }
            IpAddr::V6(v6) => {
                if v6.is_unspecified() { set_sockopt(fd, libc::IPPROTO_IPV6, libc::IPV6_V6ONLY, 0); }
                let mut a: libc::sockaddr_in6 = std::mem::zeroed();
                a.sin6_family = libc::AF_INET6 as libc::sa_family_t;
                a.sin6_port = port.to_be();
                a.sin6_addr = libc::in6_addr { s6_addr: v6.octets() };
                libc::bind(fd, &a as *const _ as *const libc::sockaddr, std::mem::size_of::<libc::sockaddr_in6>() as _)
            }
        };
        if bind_rc != 0 || libc::listen(fd, 4096) != 0 {
            let err = io::Error::last_os_error();
            libc::close(fd);
            return Err(err);
        }
        #[cfg(not(target_os = "linux"))]
        crate::set_nonblocking(fd);
        Ok(fd)
    }
}

fn bound_port(fd: libc::c_int) -> u16 {
    use std::os::fd::FromRawFd;
    std::mem::ManuallyDrop::new(unsafe { std::net::TcpListener::from_raw_fd(fd) })
        .local_addr().map_or(0, |a| a.port())
}

fn peer_ip_addr(storage: &libc::sockaddr_storage) -> IpAddr {
    unsafe {
        match storage.ss_family as libc::c_int {
            libc::AF_INET => {
                let addr = &*(storage as *const _ as *const libc::sockaddr_in);
                IpAddr::V4(Ipv4Addr::from(addr.sin_addr.s_addr.to_ne_bytes()))
            }
            libc::AF_INET6 => {
                let v6 = Ipv6Addr::from((&*(storage as *const _ as *const libc::sockaddr_in6)).sin6_addr.s6_addr);
                v6.to_ipv4_mapped().map_or(IpAddr::V6(v6), IpAddr::V4)
            }
            _ => IpAddr::V4(Ipv4Addr::UNSPECIFIED),
        }
    }
}

#[cfg(target_os = "linux")]
const SEND_FLAGS: libc::c_int = libc::MSG_NOSIGNAL;
#[cfg(not(target_os = "linux"))]
const SEND_FLAGS: libc::c_int = 0;

enum SendRes { Done(usize), WouldBlock, Err }

#[inline]
fn iov(s: &[u8]) -> libc::iovec { libc::iovec { iov_base: s.as_ptr() as *mut libc::c_void, iov_len: s.len() } }

fn send_iovs(fd: libc::c_int, iovs: &[libc::iovec]) -> SendRes {
    let mut msg: libc::msghdr = unsafe { std::mem::zeroed() };
    msg.msg_iov = iovs.as_ptr() as *mut libc::iovec;
    msg.msg_iovlen = iovs.len() as _;
    loop {
        let n = unsafe { libc::sendmsg(fd, &msg, SEND_FLAGS) };
        if n > 0 { return SendRes::Done(n as usize); }
        if n == 0 { return SendRes::Err; }
        let e = last_errno();
        if e == libc::EINTR { continue; }
        return if is_wouldblock(e) { SendRes::WouldBlock } else { SendRes::Err };
    }
}

// ---- Vectored Zero-Copy TX Chunks & Per-Connection State ----

enum TxBuf { Wire(WireBytes), Owned(Vec<u8>) }
struct TxChunk { buf: TxBuf, off: usize }

impl TxChunk {
    #[inline]
    fn as_slice(&self) -> &[u8] {
        let s = match &self.buf { TxBuf::Wire(w) => w.as_slice(), TxBuf::Owned(v) => v };
        &s[self.off..]
    }
    #[inline] fn len(&self) -> usize { self.as_slice().len() }
    #[inline] fn advance(&mut self, n: usize) { self.off += n; }
}

struct WsSub { sub_id: u32, topic: String, channel: String, params: Vec<u8> }
struct PendingBody { content_len: usize, keep_alive: bool, req: LeanRef, inline: bool }

#[derive(Copy, Clone, Eq, PartialEq)]
enum ConnStep { Continue, Done, Close }

struct Conn {
    token: u64,
    fd: libc::c_int,
    ip_addr: IpAddr,
    ip_lean: LeanRef,
    rx: ByteQueue,
    rx_hdr_scanned: usize,
    tx: VecDeque<TxChunk>,
    tx_bytes: usize,
    tx_armed: bool,
    peer_eof: bool,
    close_after_tx: bool,
    in_flight: bool,
    pending_body: Option<PendingBody>,
    is_ws: bool,
    ws_ctx: Option<LeanRef>,
    frag: Option<LeanRef>,
    subs: Vec<WsSub>,
    subs_arr: Option<LeanRef>,
    last_active: Instant,
    last_ping: Instant,
}

impl Conn {
    #[inline]
    fn consume_rx(&mut self, n: usize) { self.rx.consume(n); self.rx_hdr_scanned = 0; }

    fn enqueue_chunk(&mut self, poller: &Poller, chunk: TxChunk) -> bool {
        let clen = chunk.len();
        if clen == 0 { return true; }
        // Allow an empty TX queue to hold one response > MAX_TX_BUF_BYTES (e.g. large static asset),
        // while bounding multi-message / WS broadcast backlog at MAX_TX_BUF_BYTES.
        if !self.tx.is_empty() && self.tx_bytes.saturating_add(clen) > MAX_TX_BUF_BYTES { return false; }
        self.tx_bytes += clen;
        self.tx.push_back(chunk);
        if !self.tx_armed {
            poller.set_write(self.fd, self.token, true);
            self.tx_armed = true;
        }
        true
    }

    fn send_one(&mut self, poller: &Poller, slice: &[u8], make_chunk: impl FnOnce(usize) -> TxChunk) -> bool {
        if slice.is_empty() { return true; }
        if self.tx.is_empty() {
            let mut off = 0usize;
            for _ in 0..MAX_TX_SEND_ITERS {
                match send_iovs(self.fd, &[iov(&slice[off..])]) {
                    SendRes::Done(sent) => {
                        off += sent;
                        if off >= slice.len() { return true; }
                    }
                    SendRes::WouldBlock => break,
                    SendRes::Err => return false,
                }
            }
            return self.enqueue_chunk(poller, make_chunk(off));
        }
        if self.tx_bytes.saturating_add(slice.len()) > MAX_TX_BUF_BYTES { return false; }
        self.enqueue_chunk(poller, make_chunk(0))
    }

    fn send_wire(&mut self, poller: &Poller, wire: WireBytes) -> bool {
        let ba = wire.0 .0;
        self.send_one(poller, unsafe { ba_slice(ba) }, |off| TxChunk { buf: TxBuf::Wire(wire), off })
    }

    /// Inline ST fast path: send straight from borrowed Lean ByteArray without `mark_mt` or `WireBytes`
    /// unless a partial write / `WouldBlock` requires queueing in `self.tx`.
    unsafe fn send_borrowed_ba(&mut self, poller: &Poller, ba: *mut LeanObj) -> bool {
        self.send_one(poller, ba_slice(ba), |off| TxChunk { buf: TxBuf::Wire(WireBytes::from_borrowed(ba)), off })
    }

    fn send_slice(&mut self, poller: &Poller, data: &[u8]) -> bool {
        self.send_one(poller, data, |off| TxChunk { buf: TxBuf::Owned(data[off..].to_vec()), off: 0 })
    }

    fn send_ws_event(&mut self, poller: &Poller, sub_id: u32, payload: &[u8]) -> bool {
        let total = 5 + payload.len();
        let mut hdr = [0u8; 15];
        hdr[0] = 0x82;
        let hlen = match total {
            0..=125 => {
                hdr[1] = total as u8;
                2
            }
            126..=65535 => {
                hdr[1] = 126;
                hdr[2..4].copy_from_slice(&(total as u16).to_be_bytes());
                4
            }
            _ => {
                hdr[1] = 127;
                hdr[2..10].copy_from_slice(&(total as u64).to_be_bytes());
                10
            }
        };
        hdr[hlen] = 0x12;
        hdr[hlen + 1..hlen + 5].copy_from_slice(&sub_id.to_be_bytes());
        let mut rem_h = &hdr[..hlen + 5];
        let mut rem_p = payload;
        if self.tx.is_empty() {
            let iovs = [iov(rem_h), iov(rem_p)];
            match send_iovs(self.fd, if rem_p.is_empty() { &iovs[..1] } else { &iovs }) {
                SendRes::Done(sent) if sent >= rem_h.len() + rem_p.len() => return true,
                SendRes::Done(sent) if sent >= rem_h.len() => {
                    rem_p = &rem_p[sent - rem_h.len()..];
                    rem_h = &[];
                }
                SendRes::Done(sent) => rem_h = &rem_h[sent..],
                SendRes::WouldBlock => {}
                SendRes::Err => return false,
            }
        }
        let rem_len = rem_h.len() + rem_p.len();
        if !self.tx.is_empty() && self.tx_bytes.saturating_add(rem_len) > MAX_TX_BUF_BYTES { return false; }
        let mut buf = Vec::with_capacity(rem_len);
        buf.extend_from_slice(rem_h);
        buf.extend_from_slice(rem_p);
        self.enqueue_chunk(poller, TxChunk { buf: TxBuf::Owned(buf), off: 0 })
    }

    fn flush_tx(&mut self, poller: &Poller) -> bool {
        for _ in 0..MAX_TX_SEND_ITERS {
            if self.tx.is_empty() { break; }
            let mut iovs: [libc::iovec; 16] = unsafe { std::mem::zeroed() };
            let mut count = 0usize;
            for chunk in self.tx.iter().take(16) {
                let s = chunk.as_slice();
                if !s.is_empty() { iovs[count] = iov(s); count += 1; }
            }
            if count == 0 {
                self.tx.clear();
                self.tx_bytes = 0;
                break;
            }
            match send_iovs(self.fd, &iovs[..count]) {
                SendRes::Done(mut sent) => {
                    self.tx_bytes = self.tx_bytes.saturating_sub(sent);
                    while sent > 0 {
                        let front_len = self.tx[0].len();
                        if sent >= front_len {
                            sent -= front_len;
                            self.tx.pop_front();
                        } else {
                            self.tx[0].advance(sent);
                            sent = 0;
                        }
                    }
                }
                SendRes::WouldBlock => break,
                SendRes::Err => return false,
            }
        }
        if self.tx.is_empty() && self.tx_armed {
            poller.set_write(self.fd, self.token, false);
            self.tx_armed = false;
        }
        true
    }

    fn ready_to_close(&self, hangup: bool) -> bool {
        !self.in_flight && self.tx.is_empty() && (self.close_after_tx || ((self.peer_eof || hangup) && (self.rx.is_empty() || self.is_ws)))
    }

    fn close_step(&mut self, sent: bool) -> ConnStep {
        self.close_after_tx = true;
        if !sent || self.tx.is_empty() { ConnStep::Close } else { ConnStep::Done }
    }

    fn send_and_close(&mut self, poller: &Poller, data: &[u8]) -> ConnStep {
        let sent = self.send_slice(poller, data);
        self.close_step(sent)
    }

    fn finish_write(&mut self, sent: bool, keep_open: bool, can_continue: bool) -> ConnStep {
        if !sent || !keep_open { self.close_step(sent) }
        else if self.ready_to_close(false) { ConnStep::Close }
        else if can_continue && !self.rx.is_empty() { ConnStep::Continue }
        else { ConnStep::Done }
    }

    fn finish_ws_upgrade(&mut self, sent: bool, ws_ctx: LeanRef, init_frag: &LeanRef, now: Instant) -> ConnStep {
        if !sent { return self.close_step(false); }
        self.is_ws = true;
        self.ws_ctx = Some(ws_ctx);
        self.frag = Some(init_frag.clone());
        self.subs_arr = None;
        self.last_active = now;
        self.last_ping = now;
        if self.rx.is_empty() { ConnStep::Done } else { ConnStep::Continue }
    }

    unsafe fn eval_body_inline(&mut self, poller: &Poller, cbs: &Callbacks, req_ptr: *mut LeanObj, cl: usize) -> bool {
        let res = lean_apply_4(
            cbs.on_body.clone_ptr(), req_ptr, mk_ba(&self.rx.as_slice()[..cl]), self.ip_lean.clone_ptr(), qed_lean_box(0),
        );
        self.consume_rx(cl);
        with_io_ok(res, |v| self.send_borrowed_ba(poller, v)).unwrap_or(false)
    }

    /// Returns `None` iff `on_head` returned tag 7 (`DeferHead` for OIDC WS upgrades).
    fn eval_head_inline(
        &mut self, poller: &Poller, cbs: &Callbacks, head_end: usize, consume_len: usize, now: Instant,
    ) -> Option<ConnStep> {
        unsafe {
            let res = lean_apply_4(
                cbs.on_head.clone_ptr(), mk_ba(&self.rx.as_slice()[..head_end]),
                self.ip_lean.clone_ptr(), qed_lean_box(1), qed_lean_box(0),
            );
            with_io_ok(res, |act| match qed_lean_obj_tag(act) {
                t @ (0 | 1) => {
                    let sent = self.send_borrowed_ba(poller, qed_lean_ctor_get(act, 0));
                    self.consume_rx(consume_len);
                    Some(self.finish_write(sent, t == 1, true))
                }
                t @ (2 | 3 | 5 | 6) => {
                    let cl = qed_lean_usize_of_nat(qed_lean_ctor_get(act, 0));
                    let req_ptr = qed_lean_ctor_get(act, 1);
                    let inline = t <= 3;
                    qed_lean_inc(req_ptr);
                    if !inline { lean_mark_mt(req_ptr); }
                    self.consume_rx(consume_len);
                    self.pending_body = Some(PendingBody {
                        content_len: cl, keep_alive: t == 3 || t == 6, req: LeanRef(req_ptr), inline,
                    });
                    Some(ConnStep::Continue)
                }
                4 => {
                    let ws_ctx = LeanRef::clone_mt(qed_lean_ctor_get(act, 1));
                    let sent = self.send_borrowed_ba(poller, qed_lean_ctor_get(act, 0));
                    self.consume_rx(consume_len);
                    Some(self.finish_ws_upgrade(sent, ws_ctx, &cbs.init_frag, now))
                }
                7 => None,
                _ => { self.consume_rx(consume_len); Some(self.close_step(true)) }
            }).unwrap_or_else(|| { self.consume_rx(consume_len); Some(self.close_step(true)) })
        }
    }
}

// ---- Per-Worker Event Loop ----

struct Worker {
    worker_idx: usize,
    poller: Poller,
    listen_fd: libc::c_int,
    inbox: Arc<WorkerInbox>,
    pool: Arc<BlockingPool>,
    all_pools: Arc<Vec<Arc<BlockingPool>>>,
    cbs: Arc<Callbacks>,
    rate_limiter: Option<Arc<RateLimiter>>,
    conns: ConnSlab,
    topics: HashMap<String, HashSet<(u64, u32)>>,
    done_buf: Vec<DoneEvent>,
    bcast_buf: VecDeque<Arc<BcastMsg>>,
    now: Instant,
}

fn topic_remove_from(
    topics: &mut HashMap<String, HashSet<(u64, u32)>>,
    inbox: &WorkerInbox,
    worker_idx: usize,
    use_bitmask: bool,
    topic: &str,
    token: u64,
    sub_id: u32,
) {
    let Some(subs) = topics.get_mut(topic) else { return };
    if subs.remove(&(token, sub_id)) { inbox.ws_subs.fetch_sub(1, Ordering::Release); }
    if subs.is_empty() {
        topics.remove(topic);
        if use_bitmask {
            let mut tw = write_unpoison(topic_workers());
            if let Some(mask) = tw.get_mut(topic) {
                *mask &= !(1u64 << worker_idx);
                if *mask == 0 { tw.remove(topic); }
            }
        }
    }
}

impl Worker {
    fn spawn_and_run(
        worker_idx: usize,
        listen_fd: libc::c_int,
        inbox: Arc<WorkerInbox>,
        pool: Arc<BlockingPool>,
        all_pools: Arc<Vec<Arc<BlockingPool>>>,
        cbs: Arc<Callbacks>,
        rate_limiter: Option<Arc<RateLimiter>>,
    ) {
        let Ok(poller) = Poller::new() else {
            eprintln!("✗ failed to initialize poller");
            unsafe { libc::close(listen_fd) };
            return;
        };
        poller.add_read(listen_fd, TOKEN_LISTEN);
        if inbox.wake_fd.read_fd() >= 0 { poller.add_read(inbox.wake_fd.read_fd(), TOKEN_WAKE); }
        Self {
            worker_idx, poller, listen_fd, inbox, pool, all_pools, cbs, rate_limiter,
            conns: ConnSlab::new(), topics: HashMap::new(),
            done_buf: Vec::new(), bcast_buf: VecDeque::new(), now: Instant::now(),
        }.run();
    }

    fn submit_job(&self, mut job: PoolJob, bounded: bool) -> bool {
        if self.pool.idle_hint.load(Ordering::Relaxed) == 0 && self.all_pools.len() > 1 {
            let n = self.all_pools.len();
            for off in 1..n {
                let peer = &self.all_pools[(self.worker_idx + off) % n];
                if peer.idle_hint.load(Ordering::Relaxed) > 0 {
                    match peer.try_submit_if_idle(job) {
                        Ok(()) => return true,
                        Err(j) => job = j,
                    }
                }
            }
        }
        self.pool.submit(job, bounded)
    }

    fn accept_all(&mut self) {
        loop {
            let mut storage: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
            let mut len = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
            let sptr = &mut storage as *mut _ as *mut libc::sockaddr;
            #[cfg(target_os = "linux")]
            let fd = unsafe { libc::accept4(self.listen_fd, sptr, &mut len, libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC) };
            #[cfg(not(target_os = "linux"))]
            let fd = unsafe { libc::accept(self.listen_fd, sptr, &mut len) };
            if fd < 0 { break; }
            if self.conns.len() >= MAX_WORKER_CONNS { unsafe { libc::close(fd) }; continue; }
            #[cfg(not(target_os = "linux"))]
            crate::set_nonblocking(fd);
            unsafe { set_sockopt(fd, libc::IPPROTO_TCP, libc::TCP_NODELAY, 1) };
            let (slot_idx, token) = self.conns.alloc_slot();
            if !self.poller.add_read(fd, token) {
                self.conns.cancel_slot(slot_idx);
                unsafe { libc::close(fd) };
                continue;
            }
            let ip_addr = peer_ip_addr(&storage);
            let now = self.now;
            self.conns.insert_at(slot_idx, Conn {
                token, fd, ip_addr, ip_lean: unsafe { mk_ip_lean(ip_addr) },
                rx: ByteQueue::new(), rx_hdr_scanned: 0,
                tx: VecDeque::new(), tx_bytes: 0, tx_armed: false,
                peer_eof: false, close_after_tx: false, in_flight: false, pending_body: None,
                is_ws: false, ws_ctx: None, frag: None, subs: Vec::new(), subs_arr: None,
                last_active: now, last_ping: now,
            });
        }
    }

    fn close_conn(&mut self, token: u64) {
        let Some(conn) = self.conns.remove(token) else { return };
        self.poller.remove(conn.fd);
        unsafe { libc::close(conn.fd) };
        if let Some(ws_ctx) = conn.ws_ctx {
            let use_bitmask = self.all_pools.len() <= 64;
            for sub in conn.subs {
                topic_remove_from(&mut self.topics, &self.inbox, self.worker_idx, use_bitmask, &sub.topic, token, sub.sub_id);
                let _ = self.submit_job(PoolJob::WsLeave { ws_ctx: ws_ctx.clone(), channel: sub.channel, params: sub.params }, false);
            }
        }
    }

    fn drain_inbox(&mut self) {
        self.inbox.drain_wake();

        let mut done_events = std::mem::take(&mut self.done_buf);
        std::mem::swap(&mut done_events, &mut *lock_unpoison(&self.inbox.done_queue));
        for ev in done_events.drain(..) { self.handle_done_event(ev); }
        if done_events.capacity() > 1024 { done_events.shrink_to(1024); }
        self.done_buf = done_events;

        let mut bcast_msgs = std::mem::take(&mut self.bcast_buf);
        std::mem::swap(&mut bcast_msgs, &mut *lock_unpoison(&self.inbox.bcast_queue));
        let mut to_close = Vec::new();
        {
            let Worker { conns, topics, poller, .. } = self;
            for msg in bcast_msgs.drain(..) {
                let Some(targets) = topics.get(&msg.topic) else { continue };
                for &(token, sub_id) in targets {
                    if let Some(c) = conns.get_mut(token) {
                        if c.is_ws && !c.close_after_tx && !c.send_ws_event(poller, sub_id, &msg.payload) {
                            c.close_after_tx = true;
                            to_close.push(token);
                        }
                    }
                }
            }
        }
        if bcast_msgs.capacity() > 1024 { bcast_msgs.shrink_to(1024); }
        self.bcast_buf = bcast_msgs;
        for t in to_close { self.close_conn(t); }
    }

    fn finish_step(&mut self, token: u64, step: ConnStep) {
        match step {
            ConnStep::Close => self.close_conn(token),
            ConnStep::Continue => self.process_rx(token),
            ConnStep::Done => {}
        }
    }

    fn handle_done_event(&mut self, ev: DoneEvent) {
        match ev {
            DoneEvent::Http { token, resp, keep_alive } => {
                let step = self.conns.get_mut(token).map_or(ConnStep::Done, |c| {
                    c.in_flight = false;
                    c.last_active = self.now;
                    match resp {
                        Some(w) => {
                            let sent = c.send_wire(&self.poller, w);
                            c.finish_write(sent, keep_alive, true)
                        }
                        None => c.close_step(true),
                    }
                });
                self.finish_step(token, step);
            }
            DoneEvent::WsUpgrade { token, resp, ws_ctx } => {
                let step = self.conns.get_mut(token).map_or(ConnStep::Done, |c| {
                    c.in_flight = false;
                    let sent = c.send_wire(&self.poller, resp);
                    c.finish_ws_upgrade(sent, ws_ctx, &self.cbs.init_frag, self.now)
                });
                self.finish_step(token, step);
            }
            DoneEvent::WsStep { token, ws_ctx, consumed, out_wire, close, new_frag, ops } => {
                let step = {
                    let Worker { worker_idx, conns, topics, inbox, poller, pool, all_pools, now, .. } = self;
                    let use_bitmask = all_pools.len() <= 64;
                    let Some(conn) = conns.get_mut(token) else {
                        // Connection closed while step was in flight: clean up any newly joined channels.
                        for op in ops {
                            if let SubOp::Add(_, _, channel, params) = op {
                                let _ = pool.submit(PoolJob::WsLeave { ws_ctx: ws_ctx.clone(), channel, params }, false);
                            }
                        }
                        return;
                    };
                    if !ops.is_empty() {
                        for op in ops {
                            let sid = match &op { SubOp::Add(s, ..) | SubOp::Remove(s) => *s };
                            if let Some(i) = conn.subs.iter().position(|s| s.sub_id == sid) {
                                let ot = conn.subs.swap_remove(i).topic;
                                topic_remove_from(topics, inbox, *worker_idx, use_bitmask, &ot, token, sid);
                            }
                            if let SubOp::Add(sid, topic, channel, params) = op {
                                conn.subs.push(WsSub { sub_id: sid, topic: topic.clone(), channel, params });
                                let set = topics.entry(topic.clone()).or_default();
                                let first_for_worker = set.is_empty();
                                if set.insert((token, sid)) { inbox.ws_subs.fetch_add(1, Ordering::Release); }
                                if first_for_worker && use_bitmask {
                                    *write_unpoison(topic_workers()).entry(topic).or_insert(0) |= 1u64 << *worker_idx;
                                }
                            }
                        }
                        conn.subs_arr = None;
                    }
                    conn.in_flight = false;
                    if consumed > 0 { conn.consume_rx(consumed); conn.last_active = *now; }
                    if let Some(f) = new_frag { conn.frag = Some(f); }
                    let sent = out_wire.is_none_or(|w| conn.send_wire(poller, w));
                    conn.finish_write(sent, !close, consumed > 0)
                };
                self.finish_step(token, step);
            }
        }
    }

    fn sweep_idle(&mut self, now: Instant) {
        let mut to_close = Vec::new();
        for (token, c) in self.conns.iter_mut() {
            if c.in_flight { continue; }
            if c.is_ws {
                if now.duration_since(c.last_active) > WS_DEAD_TIMEOUT {
                    to_close.push(token);
                } else if !c.close_after_tx && now.duration_since(c.last_ping) >= WS_PING_INTERVAL {
                    c.last_ping = now;
                    if !c.send_slice(&self.poller, &[0x89, 0x00]) { to_close.push(token); }
                }
            } else if now.duration_since(c.last_active) > HTTP_IDLE_TIMEOUT {
                to_close.push(token);
            }
        }
        for t in to_close { self.close_conn(t); }
    }

    fn reject_overloaded(&mut self, token: u64) {
        let close = self.conns.get_mut(token).is_some_and(|conn| {
            conn.in_flight = false;
            conn.send_and_close(&self.poller, RESP_503_WIRE) == ConnStep::Close
        });
        if close { self.close_conn(token); }
    }

    fn submit_deferred_body(&mut self, token: u64, req: LeanRef, cl: usize, keep_alive: bool) {
        let Some(conn) = self.conns.get_mut(token) else { return };
        let body = unsafe { mk_ba_mt(&conn.rx.as_slice()[..cl]) };
        if cl > 0 { conn.consume_rx(cl); }
        let ip = conn.ip_lean.clone();
        conn.in_flight = true;
        if !self.submit_job(PoolJob::Body { token, req, body, ip, keep_alive, inbox: self.inbox.clone() }, true) {
            self.reject_overloaded(token);
        }
    }

    fn process_rx(&mut self, token: u64) {
        loop {
            let Some(conn) = self.conns.get_mut(token) else { return };
            if conn.close_after_tx || conn.in_flight { return; }

            if conn.is_ws {
                if conn.rx.is_empty() { return; }
                let (Some(ws_ctx), Some(frag)) = (conn.ws_ctx.clone(), conn.frag.clone()) else {
                    self.close_conn(token);
                    return;
                };
                let rx_slice = conn.rx.as_slice();
                let (rx_len, rx_ba) = (rx_slice.len(), unsafe { mk_ba_mt(rx_slice) });
                let subs_arr = conn.subs_arr.get_or_insert_with(|| unsafe { build_subs_arr(&conn.subs) }).clone();
                conn.in_flight = true;
                if !self.submit_job(PoolJob::WsStep { token, ws_ctx, rx_ba, rx_len, frag, subs_arr, inbox: self.inbox.clone() }, true) {
                    if let Some(c) = self.conns.get_mut(token) { c.in_flight = false; }
                    self.close_conn(token);
                }
                return;
            }

            if let Some(pb) = &conn.pending_body {
                if conn.rx.len() < pb.content_len {
                    if conn.peer_eof { self.close_conn(token); }
                    return;
                }
                let pb = conn.pending_body.take().unwrap();
                if pb.inline {
                    let sent = unsafe { conn.eval_body_inline(&self.poller, &self.cbs, pb.req.into_raw(), pb.content_len) };
                    match conn.finish_write(sent, pb.keep_alive, true) {
                        ConnStep::Continue => continue,
                        ConnStep::Done => return,
                        ConnStep::Close => { self.close_conn(token); return; }
                    }
                }
                self.submit_deferred_body(token, pb.req, pb.content_len, pb.keep_alive);
                return;
            }

            let (head_end, consume_len) = match find_header_end(conn.rx.as_slice(), &mut conn.rx_hdr_scanned) {
                Some(pos) => (pos, pos + 4),
                None if conn.rx.len() > MAX_REQ_HDR_BYTES => (MAX_REQ_HDR_BYTES + 1, conn.rx.len()),
                None => {
                    if conn.peer_eof { self.close_conn(token); }
                    return;
                }
            };
            if let Some(rl) = &self.rate_limiter {
                if !conn.rx.as_slice()[..head_end].starts_with(b"GET /_qed/health ") {
                    if let Err(retry_after) = rl.check(conn.ip_addr) {
                        let mut buf = [0u8; 256];
                        if conn.send_and_close(&self.poller, format_429_wire(retry_after, &mut buf)) == ConnStep::Close {
                            self.close_conn(token);
                        }
                        return;
                    }
                }
            }
            // Fast inline execution on the I/O worker for non-blocking endpoints; body requests
            // loop back into `pending_body` above (inline or pooled) without re-parsing headers.
            match conn.eval_head_inline(&self.poller, &self.cbs, head_end, consume_len, self.now) {
                Some(ConnStep::Continue) => continue,
                Some(ConnStep::Done) => return,
                Some(ConnStep::Close) => { self.close_conn(token); return; }
                None => {
                    let head_ba = unsafe { mk_ba_mt(&conn.rx.as_slice()[..head_end]) };
                    conn.consume_rx(consume_len);
                    let ip = conn.ip_lean.clone();
                    conn.in_flight = true;
                    if !self.submit_job(PoolJob::Head { token, head_ba, ip, inbox: self.inbox.clone() }, true) {
                        self.reject_overloaded(token);
                    }
                    return;
                }
            }
        }
    }

    fn handle_readable(&mut self, token: u64, hangup: bool) {
        let (mut closed, mut got_bytes) = (false, false);
        let now = self.now;
        if let Some(c) = self.conns.get_mut(token) {
            let mut want: usize = 4096;
            loop {
                if c.rx.len() >= MAX_RX_BUF_BYTES { closed = true; break; }
                let (n, read_cap) = c.rx.write_spare(want, MAX_RX_BUF_BYTES, |ptr, cap| {
                    unsafe { libc::read(c.fd, ptr as *mut libc::c_void, cap) }
                });
                if n > 0 {
                    got_bytes = true;
                    if (n as usize) < read_cap { break; }
                    want = (want * 2).min(65536);
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
            if got_bytes { c.last_active = now; }
        } else { return; }
        if closed { self.close_conn(token); return; }
        if got_bytes { self.process_rx(token); }
        if self.conns.get(token).is_some_and(|c| c.ready_to_close(hangup)) { self.close_conn(token); }
    }

    fn handle_writable(&mut self, token: u64) {
        if self.conns.get_mut(token).is_some_and(|c| !c.flush_tx(&self.poller) || c.ready_to_close(false)) {
            self.close_conn(token);
        }
    }

    fn run(mut self) {
        let mut events = Vec::with_capacity(128);
        let mut last_sweep = self.now;
        while !STOP.load(Ordering::Relaxed) {
            self.poller.wait(&mut events, 250);
            self.now = Instant::now();
            for ev in events.drain(..) {
                match ev.token {
                    TOKEN_LISTEN => self.accept_all(),
                    TOKEN_WAKE => self.drain_inbox(),
                    t => {
                        if ev.readable || ev.hangup { self.handle_readable(t, ev.hangup); }
                        if ev.writable { self.handle_writable(t); }
                    }
                }
            }
            if self.now.duration_since(last_sweep) >= Duration::from_secs(5) {
                last_sweep = self.now;
                self.sweep_idle(self.now);
            }
        }
        let tokens: Vec<u64> = self.conns.iter_mut().map(|(t, _)| t).collect();
        for t in tokens { self.close_conn(t); }
        unsafe { libc::close(self.listen_fd) };
    }
}

#[no_mangle]
pub unsafe extern "C" fn qed_server_run(
    host_obj: *mut LeanObj,
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

    let num_workers = if num_workers_in == 0 {
        thread::available_parallelism().map_or(2, |n| n.get()).clamp(1, 16) as u32
    } else { num_workers_in };
    let setup = || -> Result<(IpAddr, libc::c_int), String> {
        let bind_ip = parse_bind_ip(str_slice(host_obj)).map_err(|e| e.to_string())?;
        let use_reuseport = cfg!(target_os = "linux") && num_workers > 1;
        let fd = create_listener(bind_ip, port_in, use_reuseport)
            .map_err(|e| format!("failed to bind {bind_ip}:{port_in}: {e}"))?;
        Ok((bind_ip, fd))
    };
    let (bind_ip, first_fd) = match setup() {
        Ok(v) => v,
        Err(e) => {
            eprintln!("✗ {e}");
            for obj in [init_frag, on_head, on_body, on_ws_bytes, on_ws_leave] { qed_lean_dec(obj); }
            return qed_lean_io_mk_ok(qed_lean_box_u32(1));
        }
    };

    let per_worker_threads = env_parse::<usize>("QED_BLOCKING_THREADS")
        .map(|n| n.clamp(1, 256).div_ceil(num_workers as usize).max(1))
        .unwrap_or_else(|| (64usize / (num_workers as usize).max(1)).clamp(2, 4));

    // Mark long-lived server closures persistent (`m_rc = 0`) only after bind succeeds so
    // multi-core handler threads avoid atomic MT refcount cache-line bouncing on every request.
    let cbs = Arc::new(Callbacks {
        init_frag: LeanRef::new_persistent(init_frag),
        on_head: LeanRef::new_persistent(on_head),
        on_body: LeanRef::new_persistent(on_body),
        on_ws_bytes: LeanRef::new_persistent(on_ws_bytes),
        on_ws_leave: LeanRef::new_persistent(on_ws_leave),
    });

    let port = if port_in == 0 { bound_port(first_fd) } else { port_in };
    let inboxes: Vec<Arc<WorkerInbox>> = (0..num_workers).map(|_| Arc::new(WorkerInbox::new())).collect();
    *write_unpoison(&INBOXES) = inboxes.clone();
    // Dedicated handler pool per I/O worker eliminates cross-worker `PoolQueue` mutex contention,
    // with lock-free idle-peer overflow when a single worker saturates its local threads.
    let pools = Arc::new((0..num_workers).map(|_| BlockingPool::new(per_worker_threads, cbs.clone())).collect::<Vec<_>>());

    let display_host = match bind_ip { IpAddr::V4(v4) => v4.to_string(), IpAddr::V6(v6) => format!("[{v6}]") };
    println!(
        "▸ qed native server listening on http://{display_host}:{port} ({num_workers} I/O worker{}, {} handler threads)",
        if num_workers == 1 { "" } else { "s" },
        per_worker_threads * (num_workers as usize),
    );
    let _ = io::stdout().flush();

    let rate_limiter = RateLimiter::from_env();
    let handles: Vec<_> = (1..num_workers as usize).map(|idx| {
        let (inbox, pool_c, all_pools_c, cbs_c, rl_c) =
            (inboxes[idx].clone(), pools[idx].clone(), pools.clone(), cbs.clone(), rate_limiter.clone());
        #[cfg(not(target_os = "linux"))]
        let shared_fd = libc::dup(first_fd);
        thread::spawn(move || {
            unsafe { lean_initialize_thread() };
            #[cfg(target_os = "linux")]
            match create_listener(bind_ip, port, true) {
                Ok(lfd) => Worker::spawn_and_run(idx, lfd, inbox, pool_c, all_pools_c, cbs_c, rl_c),
                Err(e) => eprintln!("✗ worker {idx} failed to bind {bind_ip}:{port}: {e}"),
            }
            #[cfg(not(target_os = "linux"))]
            if shared_fd >= 0 { Worker::spawn_and_run(idx, shared_fd, inbox, pool_c, all_pools_c, cbs_c, rl_c); }
            else { eprintln!("✗ worker {idx} failed to dup listener socket"); }
            unsafe { lean_finalize_thread() };
        })
    }).collect();

    Worker::spawn_and_run(0, first_fd, inboxes[0].clone(), pools[0].clone(), pools.clone(), cbs.clone(), rate_limiter);
    STOP.store(true, Ordering::SeqCst);
    for inbox in &inboxes { inbox.wake_fd.wake(); }
    for h in handles { let _ = h.join(); }
    for p in pools.iter() { p.shutdown(); }
    write_unpoison(&INBOXES).clear();
    write_unpoison(topic_workers()).clear();
    qed_lean_io_mk_ok(qed_lean_box_u32(0))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn push_via_spare(bq: &mut ByteQueue, data: &[u8], max_len: usize) -> isize {
        bq.write_spare(data.len(), max_len, |ptr, cap| {
            let n = data.len().min(cap);
            unsafe { std::ptr::copy_nonoverlapping(data.as_ptr(), ptr, n); }
            n as isize
        }).0
    }

    #[test]
    fn byte_queue_direct_append_compact_and_shrink() {
        let mut q = ByteQueue::new();
        let big = vec![0xABu8; COMPACT_THRESHOLD + 4096];
        assert_eq!(push_via_spare(&mut q, &big, MAX_RX_BUF_BYTES) as usize, big.len());
        assert_eq!(q.len(), big.len());
        // Consuming >= COMPACT_THRESHOLD and >= half compacts `pos` back to 0 while retaining tail.
        q.consume(COMPACT_THRESHOLD);
        assert_eq!(q.pos, 0);
        assert_eq!(q.as_slice(), &[0xABu8; 4096]);
        // Max-len cap prevents unbounded direct writes.
        assert_eq!(push_via_spare(&mut q, &[1, 2, 3, 4], 4098), 2);
        assert_eq!(q.len(), 4098);
        // Draining completely shrinks oversized buffer back to <= 4096.
        q.consume(4098);
        assert!(q.is_empty());
        assert!(q.buf.capacity() <= 4096);
    }

    #[test]
    fn conn_slab_insert_aba_and_token_range() {
        let mut slab: ConnSlab<u32> = ConnSlab::new();
        let ins = |s: &mut ConnSlab<u32>, v| { let (i, t) = s.alloc_slot(); s.insert_at(i, v); (i, t) };
        let (i1, t1) = ins(&mut slab, 100);
        let (_, t2) = ins(&mut slab, 200);
        assert!(t1 >= 16 && t2 >= 16 && t2 != t1);
        assert_eq!(slab.len(), 2);
        assert_eq!(slab.get(t1), Some(&100));
        assert_eq!(slab.remove(t1), Some(100));
        assert_eq!(slab.get(t1), None);
        // Reusing slot `i1` bumps generation so stale `t1` is ABA-rejected.
        let (i3, t3) = ins(&mut slab, 300);
        assert_eq!(i3, i1);
        assert_ne!(t3, t1);
        assert_eq!(slab.get(t1), None);
        assert_eq!(slab.remove(t1), None);
        assert_eq!(slab.get(t3), Some(&300));
        // Canceled slot also bumps generation and stays absent.
        let (ic, tc) = slab.alloc_slot();
        slab.cancel_slot(ic);
        assert_eq!(slab.get(tc), None);
        assert_eq!(slab.len(), 2);
    }

    #[test]
    fn rate_limiter_burst_429_refill_and_eviction() {
        let rl = RateLimiter::new(10, 2);
        for ip in [IpAddr::V4(Ipv4Addr::new(192, 0, 2, 1)), IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1))] {
            assert_eq!(rl.check_at(ip, 0), Ok(()));
            assert_eq!(rl.check_at(ip, 0), Ok(()));
            assert!(rl.check_at(ip, 0).is_err());
            // At 10 rps (100ms/token), +100ms refills exactly 1 token.
            assert_eq!(rl.check_at(ip, 100), Ok(()));
            assert!(rl.check_at(ip, 100).is_err());
        }
        // Fill a single shard past RL_MAX_ENTRIES_PER_SHARD and verify bounded eviction.
        let rl_ev = RateLimiter::new(100, 1);
        for (hit, ip) in (1u32..).map(|n| IpAddr::V4(Ipv4Addr::from(0x0A00_0000 | n)))
            .filter(|&ip| RateLimiter::shard_idx(ip) == 0)
            .take(RL_MAX_ENTRIES_PER_SHARD + 9).enumerate()
        {
            assert_eq!(rl_ev.check_at(ip, hit as u64), Ok(()));
        }
        assert!(lock_unpoison(&rl_ev.shards[0]).len() <= RL_MAX_ENTRIES_PER_SHARD);
    }

    #[test]
    fn find_header_end_incremental_and_pipelined() {
        let reqs = b"GET /a HTTP/1.1\r\nHost: x\r\n\r\nGET /b HTTP/1.1\r\nHost: y\r\r\n\r\n";
        let mut buf = Vec::new();
        let mut scanned = 0usize;
        let mut found1 = None;
        for &b in &reqs[..28] {
            buf.push(b);
            found1 = find_header_end(&buf, &mut scanned);
        }
        assert_eq!(found1, Some(24));
        assert_eq!(scanned, 0);
        // Pipelined 2nd request after consuming 1st (with tricky `\r\r\n\r\n` ending).
        let mut q = ByteQueue::new();
        push_via_spare(&mut q, reqs, MAX_RX_BUF_BYTES);
        let p1 = find_header_end(q.as_slice(), &mut scanned).unwrap();
        assert_eq!(p1, 24);
        q.consume(p1 + 4);
        let p2 = find_header_end(q.as_slice(), &mut scanned).unwrap();
        assert_eq!(p2, 25);
        assert_eq!(&q.as_slice()[..p2], b"GET /b HTTP/1.1\r\nHost: y\r");
    }
}
